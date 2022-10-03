pub mod block;
pub mod compact;
pub mod util;

use std::cell::UnsafeCell;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Deref;
use std::rc::Rc;

#[derive(Debug)]
pub enum ShaleError {
    LinearMemStoreError,
    DecodeError,
    ObjRefError,
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

/// A handle that pins a portion of the linear memory image.
pub trait MemView: Deref<Target = [u8]> {
    /// Returns the underlying linear in-memory store.
    fn mem_image(&self) -> &dyn MemStore;
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

impl<T> std::hash::Hash for ObjPtr<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.addr.hash(state)
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

/// A typed, readable handle for the stored item in [ShaleStore]. The object does not contain any
/// addressing information (and is thus read-only) and just represents the decoded/mapped data.
/// This should be implemented by [Obj::from_typed_view] or see [MummyObj::ptr_to_obj].
pub trait TypedView<T: ?Sized>: Deref<Target = T> {
    /// Access it as a [MemView] object.
    fn as_mem_view(&self) -> &dyn MemView;
    /// Defines how the current in-memory object of `T` should be represented in the linear storage space.
    fn to_mem_image(&self) -> Option<Box<[u8]>>;
    /// Write to the typed content.
    fn write(&mut self) -> &mut T;
    /// Returns if the typed content is memory-mapped (i.e., all changes through `write` are auto
    /// reflected in the underlying [MemStore]).
    fn is_mem_mapped(&self) -> bool;
}

pub struct Obj<T: ?Sized> {
    addr_: u64,
    space_id: SpaceID,
    inner: Box<dyn TypedView<T>>,
}

impl<T: ?Sized> Obj<T> {
    #[inline(always)]
    pub fn as_ptr(&self) -> ObjPtr<T> {
        ObjPtr::<T>::new(self.addr_)
    }
}

impl<T: ?Sized> Obj<T> {
    /// Write to the underlying object. Returns `Some(())` on success.
    pub fn write(&mut self, modify: impl FnOnce(&mut T) -> ()) -> Option<()> {
        modify(self.inner.write());
        let lspace = self.inner.as_mem_view().mem_image();
        let new_value = self.inner.to_mem_image()?;
        if !self.inner.is_mem_mapped() {
            lspace.write(self.addr_, &new_value);
        }
        if new_value.len() == 0 {
            return Some(())
        }
        Some(())
    }

    pub fn get_space_id(&self) -> SpaceID {
        self.space_id
    }

    pub unsafe fn from_typed_view(
        addr_: u64, space_id: SpaceID, r: Box<dyn TypedView<T>>,
    ) -> Self {
        Obj {
            addr_,
            space_id,
            inner: r,
        }
    }
}

impl<T> Deref for Obj<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &*self.inner
    }
}

/// Handle offers read & write access to the stored [ShaleStore] item.
pub struct ObjRef<'a, T> {
    inner: Option<Obj<T>>,
    cache: Rc<ObjCacheInner<T>>,
    _life: PhantomData<&'a mut ()>,
}

impl<'a, T> ObjRef<'a, T> {
    pub unsafe fn to_longlive(mut self) -> ObjRef<'static, T> {
        ObjRef {
            inner: self.inner.take(),
            cache: self.cache.clone(),
            _life: PhantomData,
        }
    }
}

impl<'a, T> Deref for ObjRef<'a, T> {
    type Target = Obj<T>;
    fn deref(&self) -> &Obj<T> {
        self.inner.as_ref().unwrap()
    }
}

impl<'a, T> std::ops::DerefMut for ObjRef<'a, T> {
    fn deref_mut(&mut self) -> &mut Obj<T> {
        self.inner.as_mut().unwrap()
    }
}

impl<'a, T> Drop for ObjRef<'a, T> {
    fn drop(&mut self) {
        let inner = self.inner.take().unwrap();
        let ptr = inner.as_ptr();
        self.cache.0.borrow_mut().put(ptr, Some(inner));
    }
}

/// A persistent item storage backed by linear logical space. New items can be created and old
/// items could be dropped or retrieved.
pub trait ShaleStore<T> {
    /// Derference the [ObjPtr] to a handle that gives direct access to the item in memory.
    fn get_item<'a>(
        &'a self, ptr: ObjPtr<T>,
    ) -> Result<ObjRef<'a, T>, ShaleError>;
    /// Allocate a new item.
    fn put_item<'a>(
        &'a self, item: T, extra: u64,
    ) -> Result<ObjRef<'a, T>, ShaleError>;
    /// Free a item and recycle its space when applicable.
    fn free_item(&mut self, item: ObjPtr<T>) -> Result<(), ShaleError>;
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

/// Reference implementation of [TypedView]. It takes any type that implements [MummyItem] and should
/// be used in most of the circumstances.
pub struct MummyObj<T> {
    decoded: T,
    raw: Box<dyn MemView>,
    len_limit: u64,
}

impl<T> Deref for MummyObj<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.decoded
    }
}

impl<T: MummyItem> TypedView<T> for MummyObj<T> {
    fn as_mem_view(&self) -> &dyn MemView {
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

impl<T: MummyItem + 'static> MummyObj<T> {
    fn new(
        addr: u64, len_limit: u64, space: &dyn MemStore,
    ) -> Result<Self, ShaleError> {
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

    pub unsafe fn ptr_to_obj(
        store: &dyn MemStore, ptr: ObjPtr<T>, len_limit: u64,
    ) -> Result<Obj<T>, ShaleError> {
        let addr = ptr.addr();
        Ok(Obj::from_typed_view(
            addr,
            store.id(),
            Box::new(MummyObj::new(addr, len_limit, store)?),
        ))
    }

    pub unsafe fn item_to_obj(
        store: &dyn MemStore, addr: u64, length: u64, len_limit: u64,
        decoded: T,
    ) -> Result<Obj<T>, ShaleError> {
        Ok(Obj::from_typed_view(
            addr,
            store.id(),
            Box::new(MummyObj::from_hydrated(
                addr, length, len_limit, decoded, store,
            )?),
        ))
    }
}

impl<T> MummyObj<T> {
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

    pub unsafe fn slice<U: MummyItem + 'static>(
        s: &Obj<T>, offset: u64, length: u64, decoded: U,
    ) -> Result<Obj<U>, ShaleError> {
        let addr_ = s.addr_ + offset;
        let r = Box::new(MummyObj::new_from_slice(
            addr_,
            length,
            length,
            decoded,
            s.inner.as_mem_view().mem_image(),
        )?);
        Ok(Obj {
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
    fn mem_image(&self) -> &dyn MemStore {
        &self.mem
    }
}

use std::cell::RefCell;
use std::num::NonZeroUsize;

struct ObjCacheInner<T: ?Sized>(
    RefCell<lru::LruCache<ObjPtr<T>, Option<Obj<T>>>>,
);

pub struct ObjCache<T: ?Sized>(Rc<ObjCacheInner<T>>);

impl<T> ObjCache<T> {
    pub fn new(capacity: usize) -> Self {
        Self(Rc::new(ObjCacheInner(RefCell::new(lru::LruCache::new(
            NonZeroUsize::new(capacity).expect("non-zero cache size"),
        )))))
    }

    pub fn get<'a>(
        &'a self, ptr: ObjPtr<T>,
    ) -> Result<Option<ObjRef<'a, T>>, ShaleError> {
        let mut pinned = self.0 .0.borrow_mut();
        if let Some(r) = pinned.get_mut(&ptr) {
            return match r.take() {
                Some(r) => Ok(Some(ObjRef {
                    inner: Some(r),
                    cache: self.0.clone(),
                    _life: PhantomData,
                })),
                None => Err(ShaleError::ObjRefError),
            }
        }
        Ok(None)
    }

    pub fn put<'a>(&'a self, inner: Obj<T>) -> ObjRef<'a, T> {
        let ptr = inner.as_ptr();
        self.0 .0.borrow_mut().put(ptr, None);
        ObjRef {
            inner: Some(inner),
            cache: self.0.clone(),
            _life: PhantomData,
        }
    }

    pub fn pop(&self, ptr: ObjPtr<T>) {
        self.0 .0.borrow_mut().pop(&ptr);
    }
}
