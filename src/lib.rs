pub mod block;
pub mod compact;
mod util;

use std::cell::{RefCell, UnsafeCell};
use std::fmt;
use std::marker::PhantomData;
use std::ops::Deref;
use std::rc::Rc;

#[derive(Debug)]
pub enum ShaleError {
    LinearMemStoreError,
    DecodeError,
}

enum MemRollback {
    Rollback(Box<[u8]>),
    NoRollback,
}

pub type SpaceID = u8;
pub const INVALID_SPACE_ID: SpaceID = 0xff;

pub struct DiskWrite {
    pub space_id: SpaceID,
    pub space_off: u64,
    pub data: Box<[u8]>,
}

impl std::fmt::Debug for DiskWrite {
    fn fmt(
        &self, f: &mut std::fmt::Formatter<'_>,
    ) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "[Disk space=0x{:02x} offset=0x{:04x} data=0x{}",
            self.space_id,
            self.space_off,
            hex::encode(&self.data)
        )
    }
}

/// A typed, readable handle for the stored item in [ShaleStore]. The object does not contain any
/// addressing information (and is thus read-only) and just represents the decoded/mapped data.
/// This should be implemented as part of [ShaleRefConverter::into_shale_ref].
pub trait ShaleRef<T: ?Sized>: Deref<Target = T> {
    /// Access it as a [MemView] object.
    fn as_linear_ref(&self) -> &dyn MemView;
    /// Defines how the current in-memory object of `T` should be represented in the linear storage space.
    fn to_mem_image(&self) -> Option<Box<[u8]>>;
    /// Write to the typed content.
    fn write(&mut self) -> &mut T;
    /// Returns if the typed content is memory-mapped (i.e., all changes through `write` are auto
    /// reflected in the underlying [MemStore]).
    fn is_mem_mapped(&self) -> bool;
}

/// A handle that pins a portion of the linear memory image.
pub trait MemView: Deref<Target = [u8]> {
    /// Returns the underlying linear in-memory store.
    fn mem_image(&self) -> Box<dyn MemStore>;
}

/// In-memory store that offers access for intervals from a linear byte space, which is usually
/// backed by a cached/memory-mapped pool of the accessed intervals from its underlying linear
/// persistent store. Reads could trigger disk reads, but writes will *only* be visible in memory
/// (it does not write back to the disk).
pub trait MemStore {
    /// Returns a handle that pins the `length` of bytes starting from `offset` and makes them
    /// directly accessible.
    fn get_ref(&self, offset: u64, length: u64) -> Option<Box<dyn MemView>>;
    /// Write the `change` to the portion of the linear space starting at `offset`. The change
    /// should be immediately visible to all `MemView` associated to this linear space.
    fn write(&self, offset: u64, change: &[u8]);
    /// Returns the identifier of this storage space.
    fn id(&self) -> SpaceID;
    ///// Grows the space by a specified number of bytes and returns the original size. Use 0 to get
    ///// the current size.
    //fn grow(&self, extra: u64) -> u64;
}

/// Records a context of changes made to the [ShaleStore].
pub struct WriteContext {
    writes: RefCell<Vec<(DiskWrite, MemRollback, Box<dyn MemStore>)>>,
}

impl WriteContext {
    pub fn new() -> Self {
        Self {
            writes: RefCell::new(Vec::new()),
        }
    }

    fn add(&self, dw: DiskWrite, mw: MemRollback, mem: Box<dyn MemStore>) {
        self.writes.borrow_mut().push((dw, mw, mem))
    }

    /// Returns an atomic group of writes that should be done by a persistent store to make
    /// in-memory change persistent. Each write is made to one logic linear space specified
    /// by `space_id`. The `data` should be written from `space_off` in that linear space.
    pub fn commit(self) -> Vec<DiskWrite> {
        self.writes
            .into_inner()
            .into_iter()
            .map(|(dw, _, _)| dw)
            .collect()
    }

    /// Abort all changes.
    pub fn abort(self) {
        for (dw, mw, mem) in self.writes.into_inner() {
            if let MemRollback::Rollback(r) = mw {
                mem.write(dw.space_off, &r);
            }
        }
    }
}

/// Opaque typed pointer in the 64-bit virtual addressable space.
#[repr(C)]
pub struct ObjPtr<T: ?Sized> {
    pub(crate) addr: u64,
    phantom: PhantomData<T>,
}

impl<T> std::cmp::PartialEq for ObjPtr<T> {
    fn eq(&self, other: &ObjPtr<T>) -> bool {
        self.addr == other.addr
    }
}

impl<T> Eq for ObjPtr<T> {}
impl<T> Copy for ObjPtr<T> {}
impl<T> Clone for ObjPtr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> fmt::Display for ObjPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[ObjPtr addr={:08x}]", self.addr)
    }
}

impl<T: ?Sized> ObjPtr<T> {
    pub fn null() -> Self {
        Self::new(0)
    }
    pub fn is_null(&self) -> bool {
        self.addr == 0
    }
    pub fn addr(&self) -> u64 {
        self.addr
    }

    #[inline(always)]
    pub(crate) fn new(addr: u64) -> Self {
        ObjPtr {
            addr,
            phantom: PhantomData,
        }
    }

    #[inline(always)]
    pub unsafe fn new_from_addr(addr: u64) -> Self {
        Self::new(addr)
    }
}

impl<T> std::hash::Hash for ObjPtr<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.addr.hash(state)
    }
}

/// Handle offers read & write access to the stored [ShaleStore] item.
pub struct ObjRef<'a, T: ?Sized> {
    addr_: u64,
    space_id: SpaceID,
    inner: Box<dyn ShaleRef<T> + 'a>,
}

impl<'a, T: ?Sized> ObjRef<'a, T> {
    #[inline(always)]
    pub fn as_ptr(&self) -> ObjPtr<T> {
        ObjPtr::<T>::new(self.addr_)
    }

    pub unsafe fn to_longlive(self) -> ObjRef<'static, T> {
        let inner = Box::into_raw(self.inner);
        ObjRef {
            addr_: self.addr_,
            space_id: self.space_id,
            inner: Box::from_raw(std::mem::transmute::<
                *mut (dyn ShaleRef<T> + 'a),
                *mut (dyn ShaleRef<T> + 'static),
            >(inner)),
        }
    }
}

impl<'a, T: ?Sized> ObjRef<'a, T> {
    /// Write to the underlying object. Returns `Some(())` on success.
    pub fn write(
        &mut self, modify: impl FnOnce(&mut T) -> (), mem_rollback: bool,
        wctx: &WriteContext,
    ) -> Option<()> {
        let mw = if mem_rollback {
            MemRollback::Rollback(self.inner.to_mem_image()?)
        } else {
            MemRollback::NoRollback
        };
        modify(self.inner.write());
        let lspace = self.inner.as_linear_ref().mem_image();
        let new_value = self.inner.to_mem_image()?;
        if !self.inner.is_mem_mapped() {
            lspace.write(self.addr_, &new_value);
        }
        if new_value.len() == 0 {
            return Some(())
        }
        let dw = DiskWrite {
            space_off: self.addr_,
            space_id: self.space_id,
            data: new_value,
        };
        wctx.add(dw, mw, lspace);
        Some(())
    }

    pub fn get_space_id(&self) -> SpaceID {
        self.space_id
    }

    pub unsafe fn from_shale(
        addr_: u64, space_id: SpaceID, r: Box<dyn ShaleRef<T> + 'a>,
    ) -> Self {
        ObjRef {
            addr_,
            space_id,
            inner: r,
        }
    }
}

impl<'a, T> Deref for ObjRef<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        &*self.inner
    }
}

/// A persistent item storage backed by linear logical space. New items can be created and old
/// items could be dropped or retrieved.
pub trait ShaleStore {
    /// Derference the [ObjPtr] to a handle that gives direct access to the item in memory.
    fn get_item<'a, T: MummyItem + 'a>(
        &'a self, ptr: ObjPtr<T>,
    ) -> Result<ObjRef<'a, T>, ShaleError>;
    /// Allocate a new item.
    fn put_item<'a, T: MummyItem + 'a>(
        &'a self, item: T, extra: u64, wctx: &WriteContext,
    ) -> Result<ObjRef<'a, T>, ShaleError>;
    /// Free a item and recycle its space when applicable.
    fn free_item<T: MummyItem>(
        &mut self, item: ObjPtr<T>, wctx: &WriteContext,
    ) -> Result<(), ShaleError>;
}

/// A stored item type that could be decoded from or encoded to on-disk raw bytes. An efficient
/// implementation could be directly transmuting to/from a POD struct. But sometimes necessary
/// compression/decompression is needed to reduce disk I/O and facilitate faster in-memory access.
pub trait MummyItem {
    fn dehydrate(&self) -> Vec<u8>;
    fn hydrate(
        addr: u64, mem: &dyn MemStore,
    ) -> Result<(u64, Self), ShaleError>
    where
        Self: Sized;
    fn is_mem_mapped(&self) -> bool {
        false
    }
}

/// Helper implementation of [ShaleRef]. It takes any type that implements [MummyItem] and should
/// be used in most of the circumstances.
pub struct MummyRef<T> {
    decoded: T,
    raw: Box<dyn MemView>,
    len_limit: u64,
}

impl<T> Deref for MummyRef<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.decoded
    }
}

impl<T: MummyItem> ShaleRef<T> for MummyRef<T> {
    fn as_linear_ref(&self) -> &dyn MemView {
        &*self.raw
    }
    fn to_mem_image(&self) -> Option<Box<[u8]>> {
        let mem: Box<[u8]> = self.decoded.dehydrate().into();
        if mem.len() as u64 > self.len_limit {
            None
        } else {
            Some(mem)
        }
    }
    fn write(&mut self) -> &mut T {
        &mut self.decoded
    }
    fn is_mem_mapped(&self) -> bool {
        self.decoded.is_mem_mapped()
    }
}

impl<T: MummyItem> MummyRef<T> {
    fn new(addr: u64, len_limit: u64, space: &dyn MemStore) -> Result<Self, ShaleError> {
        let (length, decoded) = T::hydrate(addr, space)?;
        Ok(Self {
            decoded,
            raw: space
                .get_ref(addr, length)
                .ok_or(ShaleError::LinearMemStoreError)?,
            len_limit,
        })
    }
    fn from_hydrated(
        addr: u64, length: u64, len_limit: u64, decoded: T,
        space: &dyn MemStore,
    ) -> Result<Self, ShaleError> {
        Ok(Self {
            decoded,
            raw: space
                .get_ref(addr, length)
                .ok_or(ShaleError::LinearMemStoreError)?,
            len_limit,
        })
    }
}

impl<T> MummyRef<T> {
    unsafe fn new_from_slice(
        addr: u64, length: u64, len_limit: u64, decoded: T,
        space: &dyn MemStore,
    ) -> Result<Self, ShaleError> {
        Ok(Self {
            decoded,
            raw: space
                .get_ref(addr, length)
                .ok_or(ShaleError::LinearMemStoreError)?,
            len_limit,
        })
    }

    pub unsafe fn slice<'b, U: MummyItem + 'b>(
        s: &ObjRef<'b, T>, offset: u64, length: u64, decoded: U,
    ) -> Result<ObjRef<'b, U>, ShaleError> {
        let addr_ = s.addr_ + offset;
        let r = Box::new(MummyRef::new_from_slice(
            addr_,
            length,
            length,
            decoded,
            s.inner.as_linear_ref().mem_image().as_ref(),
        )?);
        Ok(ObjRef {
            addr_,
            space_id: s.space_id,
            inner: r,
        })
    }
}

impl<T> MummyItem for ObjPtr<T> {
    fn dehydrate(&self) -> Vec<u8> {
        self.addr().to_le_bytes().into()
    }

    fn hydrate(
        addr: u64, mem: &dyn MemStore,
    ) -> Result<(u64, Self), ShaleError> {
        const SIZE: u64 = 8;
        let raw = mem
            .get_ref(addr, SIZE)
            .ok_or(ShaleError::LinearMemStoreError)?;
        unsafe {
            Ok((
                SIZE,
                Self::new_from_addr(u64::from_le_bytes(
                    (**raw).try_into().unwrap(),
                )),
            ))
        }
    }
}

#[derive(Clone)]
pub struct PlainMem {
    space: Rc<UnsafeCell<Vec<u8>>>,
    id: SpaceID,
}

impl PlainMem {
    pub fn new(size: u64, id: SpaceID) -> Self {
        let mut space = Vec::new();
        space.resize(size as usize, 0);
        let space = Rc::new(UnsafeCell::new(space));
        Self { space, id }
    }
    fn get_space_mut(&self) -> &mut Vec<u8> {
        unsafe { &mut *self.space.get() }
    }
}

impl MemStore for PlainMem {
    fn get_ref(&self, offset: u64, length: u64) -> Option<Box<dyn MemView>> {
        let offset = offset as usize;
        let length = length as usize;
        if offset + length > self.get_space_mut().len() {
            None
        } else {
            Some(Box::new(PlainMemRef {
                offset,
                length,
                mem: self.clone(),
            }))
        }
    }

    fn write(&self, offset: u64, change: &[u8]) {
        let offset = offset as usize;
        let length = change.len();
        self.get_space_mut()[offset..offset + length].copy_from_slice(change)
    }

    fn id(&self) -> SpaceID {
        self.id
    }
}

struct PlainMemRef {
    offset: usize,
    length: usize,
    mem: PlainMem,
}

impl Deref for PlainMemRef {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.mem.get_space_mut()[self.offset..self.offset + self.length]
    }
}

impl MemView for PlainMemRef {
    fn mem_image(&self) -> Box<dyn MemStore> {
        Box::new(self.mem.clone())
    }
}

pub unsafe fn get_obj_ref<'a, T: 'a + MummyItem>(
    store: &'a dyn MemStore, ptr: ObjPtr<T>, len_limit: u64,
) -> Result<ObjRef<'a, T>, ShaleError> {
    let addr = ptr.addr();
    Ok(ObjRef::from_shale(
        addr,
        store.id(),
        Box::new(MummyRef::new(addr, len_limit, store)?),
    ))
}

pub unsafe fn obj_ref_from_item<'a, T: 'a + MummyItem>(
    store: &'a dyn MemStore, addr: u64, length: u64, len_limit: u64,
    decoded: T,
) -> Result<ObjRef<'a, T>, ShaleError> {
    Ok(ObjRef::from_shale(
        addr,
        store.id(),
        Box::new(MummyRef::from_hydrated(
            addr,
            length,
            len_limit,
            decoded,
            store,
        )?),
    ))
}
