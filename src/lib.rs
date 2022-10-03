use std::cell::UnsafeCell;
use std::fmt;
use std::marker::PhantomData;
use std::num::NonZeroUsize;
use std::ops::Deref;
use std::rc::Rc;

pub mod block;
pub mod compact;
pub mod util;

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

/// A handle that pins and provides a readable access to a portion of the linear memory image.
pub trait MemView: Deref<Target = [u8]> {
    /// Returns the underlying linear in-memory store.
    fn mem_image(&self) -> &dyn MemStore;
    /// Get the interval (offset, length).
    fn get_interval(&self) -> (u64, u64);
}

/// In-memory store that offers access to intervals from a linear byte space, which is usually
/// backed by a cached/memory-mapped pool of the accessed intervals from the underlying linear
/// persistent store. Reads could trigger disk reads to bring data into memory, but writes will
/// *only* be visible in memory (it does not write back to the disk).
pub trait MemStore {
    /// Returns a handle that pins the `length` of bytes starting from `offset` and makes them
    /// directly accessible.
    fn get_view(&self, offset: u64, length: u64) -> Option<Box<dyn MemView>>;
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

/// A addressed, typed, and read-writable handle for the stored item in [ShaleStore]. The object
/// represents the decoded/mapped data. The implementation of [ShaleStore] could use [ObjCache] to
/// turn a `TypedView` into an [ObjRef].
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

/// A wrapper of `TypedView` to enable writes. The direct construction (by [Obj::from_typed_view]
/// or [MummyObj::ptr_to_obj]) could be useful for some unsafe access to a low-level item (e.g.
/// headers/metadata at bootstrap or part of [ShaleStore] implementation) stored at a given [ObjPtr]
/// . Users of [ShaleStore] implementation, however, will only use [ObjRef] for safeguarded access.
pub struct Obj<T: ?Sized>(Box<dyn TypedView<T>>);

impl<T: ?Sized> Obj<T> {
    #[inline(always)]
    pub fn as_ptr(&self) -> ObjPtr<T> {
        ObjPtr::<T>::new(self.0.as_mem_view().get_interval().0)
    }
}

impl<T: ?Sized> Obj<T> {
    /// Write to the underlying object. Returns `Some(())` on success.
    #[inline]
    pub fn write(&mut self, modify: impl FnOnce(&mut T) -> ()) -> Option<()> {
        modify(self.0.write());
        let lspace = self.0.as_mem_view().mem_image();
        let new_value = self.0.to_mem_image()?;
        if !self.0.is_mem_mapped() {
            lspace.write(self.0.as_mem_view().get_interval().0, &new_value);
        }
        Some(())
    }

    #[inline(always)]
    pub fn get_space_id(&self) -> SpaceID {
        self.0.as_mem_view().mem_image().id()
    }

    #[inline(always)]
    pub fn from_typed_view(v: Box<dyn TypedView<T>>) -> Self {
        Obj(v)
    }
}

impl<T> Deref for Obj<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &*self.0
    }
}

/// User handle that offers read & write access to the stored [ShaleStore] item.
pub struct ObjRef<'a, T> {
    inner: Option<Obj<T>>,
    cache: ObjCache<T>,
    _life: PhantomData<&'a mut ()>,
}

impl<'a, T> ObjRef<'a, T> {
    pub unsafe fn to_longlive(mut self) -> ObjRef<'static, T> {
        ObjRef {
            inner: self.inner.take(),
            cache: ObjCache(self.cache.0.clone()),
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
        self.cache.get_inner_mut().put(ptr, Some(inner));
    }
}

/// A persistent item storage backed by linear logical space. New items can be created and old
/// items could be retrieved or dropped.
pub trait ShaleStore<T> {
    /// Dereference [ObjPtr] to a unique handle that allows direct access to the item in memory.
    fn get_item<'a>(
        &'a self, ptr: ObjPtr<T>,
    ) -> Result<ObjRef<'a, T>, ShaleError>;
    /// Allocate a new item.
    fn put_item<'a>(
        &'a self, item: T, extra: u64,
    ) -> Result<ObjRef<'a, T>, ShaleError>;
    /// Free an item and recycle its space when applicable.
    fn free_item(&mut self, item: ObjPtr<T>) -> Result<(), ShaleError>;
}

/// A stored item type that can be decoded from or encoded to on-disk raw bytes. An efficient
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

/// Reference implementation of [TypedView]. It takes any type that implements [MummyItem] and
/// should be useful for most applications.
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
    #[inline(always)]
    fn new(
        addr: u64, len_limit: u64, space: &dyn MemStore,
    ) -> Result<Self, ShaleError> {
        let (length, decoded) = T::hydrate(addr, space)?;
        Ok(Self {
            decoded,
            raw: space
                .get_view(addr, length)
                .ok_or(ShaleError::LinearMemStoreError)?,
            len_limit,
        })
    }

    #[inline(always)]
    fn from_hydrated(
        addr: u64, length: u64, len_limit: u64, decoded: T,
        space: &dyn MemStore,
    ) -> Result<Self, ShaleError> {
        Ok(Self {
            decoded,
            raw: space
                .get_view(addr, length)
                .ok_or(ShaleError::LinearMemStoreError)?,
            len_limit,
        })
    }

    #[inline(always)]
    pub unsafe fn ptr_to_obj(
        store: &dyn MemStore, ptr: ObjPtr<T>, len_limit: u64,
    ) -> Result<Obj<T>, ShaleError> {
        let addr = ptr.addr();
        Ok(Obj::from_typed_view(Box::new(Self::new(
            addr, len_limit, store,
        )?)))
    }

    #[inline(always)]
    pub unsafe fn item_to_obj(
        store: &dyn MemStore, addr: u64, length: u64, len_limit: u64,
        decoded: T,
    ) -> Result<Obj<T>, ShaleError> {
        Ok(Obj::from_typed_view(Box::new(Self::from_hydrated(
            addr, length, len_limit, decoded, store,
        )?)))
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
                .get_view(addr, length)
                .ok_or(ShaleError::LinearMemStoreError)?,
            len_limit,
        })
    }

    pub unsafe fn slice<U: MummyItem + 'static>(
        s: &Obj<T>, offset: u64, length: u64, decoded: U,
    ) -> Result<Obj<U>, ShaleError> {
        let addr_ = s.0.as_mem_view().get_interval().0 + offset;
        let r = Box::new(MummyObj::new_from_slice(
            addr_,
            length,
            length,
            decoded,
            s.0.as_mem_view().mem_image(),
        )?);
        Ok(Obj(r))
    }
}

impl<T> MummyItem for ObjPtr<T> {
    fn dehydrate(&self) -> Vec<u8> {
        self.addr().to_le_bytes().into()
    }

    fn hydrate(
        addr: u64, mem: &dyn MemStore,
    ) -> Result<(u64, Self), ShaleError> {
        const MSIZE: u64 = 8;
        let raw = mem
            .get_view(addr, MSIZE)
            .ok_or(ShaleError::LinearMemStoreError)?;
        unsafe {
            Ok((
                MSIZE,
                Self::new_from_addr(u64::from_le_bytes(
                    (**raw).try_into().unwrap(),
                )),
            ))
        }
    }
}

/// Purely volatile, vector-based implementation for [MemStore]. This is good for testing or trying
/// out stuff (persistent data structures) built on [ShaleStore] in memory, without having to write
/// your own [MemStore] implementation.
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
    fn get_view(&self, offset: u64, length: u64) -> Option<Box<dyn MemView>> {
        let offset = offset as usize;
        let length = length as usize;
        if offset + length > self.get_space_mut().len() {
            None
        } else {
            Some(Box::new(PlainMemRef {
                offset,
                length,
                mem: Self {
                    space: self.space.clone(),
                    id: self.id,
                },
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
    fn get_interval(&self) -> (u64, u64) {
        (self.offset as u64, self.length as u64)
    }
}

/// [ObjRef] pool that is used by [ShaleStore] implementation to construct [ObjRef]s.
pub struct ObjCache<T: ?Sized>(
    Rc<UnsafeCell<lru::LruCache<ObjPtr<T>, Option<Obj<T>>>>>,
);

impl<T> ObjCache<T> {
    pub fn new(capacity: usize) -> Self {
        Self(Rc::new(UnsafeCell::new(lru::LruCache::new(
            NonZeroUsize::new(capacity).expect("non-zero cache size"),
        ))))
    }

    #[inline(always)]
    fn get_inner_mut(&self) -> &mut lru::LruCache<ObjPtr<T>, Option<Obj<T>>> {
        unsafe { &mut *self.0.get() }
    }

    #[inline(always)]
    pub fn get<'a>(
        &'a self, ptr: ObjPtr<T>,
    ) -> Result<Option<ObjRef<'a, T>>, ShaleError> {
        let pinned = self.get_inner_mut();
        if let Some(r) = pinned.get_mut(&ptr) {
            return match r.take() {
                Some(r) => Ok(Some(ObjRef {
                    inner: Some(r),
                    cache: Self(self.0.clone()),
                    _life: PhantomData,
                })),
                None => Err(ShaleError::ObjRefError),
            }
        }
        Ok(None)
    }

    #[inline(always)]
    pub fn put<'a>(&'a self, inner: Obj<T>) -> ObjRef<'a, T> {
        let ptr = inner.as_ptr();
        self.get_inner_mut().put(ptr, None);
        ObjRef {
            inner: Some(inner),
            cache: Self(self.0.clone()),
            _life: PhantomData,
        }
    }

    #[inline(always)]
    pub fn pop(&self, ptr: ObjPtr<T>) {
        self.get_inner_mut().pop(&ptr);
    }
}
