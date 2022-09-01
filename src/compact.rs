use super::{
    MemStore, MummyItem, MummyRef, ObjPtr, ObjRef, ShaleError, ShaleStore,
    WriteContext,
};
use std::cell::UnsafeCell;

pub struct CompactHeader {
    payload_size: u64,
    is_freed: bool,
    desc_addr: ObjPtr<CompactDescriptor>,
}

impl CompactHeader {
    #![allow(dead_code)]

    pub const MSIZE: u64 = 17;
    pub fn is_freed(&self) -> bool {
        self.is_freed
    }

    pub fn payload_size(&self) -> u64 {
        self.payload_size
    }
}

impl MummyItem for CompactHeader {
    fn hydrate(
        addr: u64, mem: &dyn MemStore,
    ) -> Result<(u64, Self), ShaleError> {
        let raw = mem
            .get_ref(addr, Self::MSIZE)
            .ok_or(ShaleError::LinearMemStoreError)?;
        let payload_size = u64::from_le_bytes(raw[..8].try_into().unwrap());
        let is_freed = if raw[8] == 0 { false } else { true };
        let desc_addr = u64::from_le_bytes(raw[9..17].try_into().unwrap());
        Ok((
            Self::MSIZE,
            Self {
                payload_size,
                is_freed,
                desc_addr: ObjPtr::new(desc_addr),
            },
        ))
    }

    fn dehydrate(&self) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend(self.payload_size.to_le_bytes());
        m.push(if self.is_freed { 1 } else { 0 });
        m.extend(self.desc_addr.addr().to_le_bytes());
        assert_eq!(m.len() as u64, Self::MSIZE);
        m
    }
}

struct CompactFooter {
    payload_size: u64,
}

impl CompactFooter {
    const MSIZE: u64 = 8;
}

impl MummyItem for CompactFooter {
    fn hydrate(
        addr: u64, mem: &dyn MemStore,
    ) -> Result<(u64, Self), ShaleError> {
        let raw = mem
            .get_ref(addr, Self::MSIZE)
            .ok_or(ShaleError::LinearMemStoreError)?;
        let payload_size = u64::from_le_bytes(raw.deref().try_into().unwrap());
        Ok((Self::MSIZE, Self { payload_size }))
    }

    fn dehydrate(&self) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend(self.payload_size.to_le_bytes());
        assert_eq!(m.len() as u64, Self::MSIZE);
        m
    }
}

#[derive(Clone, Copy)]
struct CompactDescriptor {
    payload_size: u64,
    haddr: u64, // pointer to the payload of freed space
}

impl CompactDescriptor {
    const MSIZE: u64 = 16;
}

impl MummyItem for CompactDescriptor {
    fn hydrate(
        addr: u64, mem: &dyn MemStore,
    ) -> Result<(u64, Self), ShaleError> {
        let raw = mem
            .get_ref(addr, Self::MSIZE)
            .ok_or(ShaleError::LinearMemStoreError)?;
        let payload_size = u64::from_le_bytes(raw[..8].try_into().unwrap());
        let haddr = u64::from_le_bytes(raw[8..].try_into().unwrap());
        Ok((
            Self::MSIZE,
            Self {
                payload_size,
                haddr,
            },
        ))
    }

    fn dehydrate(&self) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend(self.payload_size.to_le_bytes());
        m.extend(self.haddr.to_le_bytes());
        assert_eq!(m.len() as u64, Self::MSIZE);
        m
    }
}

pub struct CompactSpaceHeader {
    meta_space_tail: u64,
    compact_space_tail: u64,
    base_addr: ObjPtr<CompactDescriptor>,
    alloc_addr: ObjPtr<CompactDescriptor>,
}

struct CompactSpaceHeaderSliced<'a> {
    meta_space_tail: ObjRef<'a, U64Field>,
    compact_space_tail: ObjRef<'a, U64Field>,
    base_addr: ObjRef<'a, ObjPtr<CompactDescriptor>>,
    alloc_addr: ObjRef<'a, ObjPtr<CompactDescriptor>>,
}

impl CompactSpaceHeader {
    pub const MSIZE: u64 = 32;

    pub fn new(meta_base: u64, compact_base: u64) -> Self {
        unsafe {
            Self {
                meta_space_tail: meta_base,
                compact_space_tail: compact_base,
                base_addr: ObjPtr::new_from_addr(meta_base),
                alloc_addr: ObjPtr::new_from_addr(meta_base),
            }
        }
    }

    fn into_fields<'a>(
        r: ObjRef<'a, Self>,
    ) -> Result<CompactSpaceHeaderSliced<'a>, ShaleError> {
        unsafe {
            Ok(CompactSpaceHeaderSliced {
                meta_space_tail: MummyRef::slice(
                    &r,
                    0,
                    8,
                    U64Field(r.meta_space_tail),
                )?,
                compact_space_tail: MummyRef::slice(
                    &r,
                    8,
                    8,
                    U64Field(r.compact_space_tail),
                )?,
                base_addr: MummyRef::slice(&r, 16, 8, r.base_addr)?,
                alloc_addr: MummyRef::slice(&r, 24, 8, r.alloc_addr)?,
            })
        }
    }
}

impl MummyItem for CompactSpaceHeader {
    fn hydrate(
        addr: u64, mem: &dyn MemStore,
    ) -> Result<(u64, Self), ShaleError> {
        let raw = mem
            .get_ref(addr, Self::MSIZE)
            .ok_or(ShaleError::LinearMemStoreError)?;
        let meta_space_tail = u64::from_le_bytes(raw[..8].try_into().unwrap());
        let compact_space_tail =
            u64::from_le_bytes(raw[8..16].try_into().unwrap());
        let base_addr = u64::from_le_bytes(raw[16..24].try_into().unwrap());
        let alloc_addr = u64::from_le_bytes(raw[24..].try_into().unwrap());
        unsafe {
            Ok((
                Self::MSIZE,
                Self {
                    meta_space_tail,
                    compact_space_tail,
                    base_addr: ObjPtr::new_from_addr(base_addr),
                    alloc_addr: ObjPtr::new_from_addr(alloc_addr),
                },
            ))
        }
    }

    fn dehydrate(&self) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend(self.meta_space_tail.to_le_bytes());
        m.extend(self.compact_space_tail.to_le_bytes());
        m.extend(self.base_addr.addr().to_le_bytes());
        m.extend(self.alloc_addr.addr().to_le_bytes());
        assert_eq!(m.len() as u64, Self::MSIZE);
        m
    }
}

struct ObjPtrField<T>(ObjPtr<T>);

impl<T> MummyItem for ObjPtrField<T> {
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
                Self(ObjPtr::new_from_addr(u64::from_le_bytes(
                    raw.deref().try_into().unwrap(),
                ))),
            ))
        }
    }
    fn dehydrate(&self) -> Vec<u8> {
        self.0.addr().to_le_bytes().into()
    }
}

impl<T> std::ops::Deref for ObjPtrField<T> {
    type Target = ObjPtr<T>;
    fn deref(&self) -> &ObjPtr<T> {
        &self.0
    }
}

impl<T> std::ops::DerefMut for ObjPtrField<T> {
    fn deref_mut(&mut self) -> &mut ObjPtr<T> {
        &mut self.0
    }
}

struct U64Field(u64);

impl MummyItem for U64Field {
    fn hydrate(
        addr: u64, mem: &dyn MemStore,
    ) -> Result<(u64, Self), ShaleError> {
        const SIZE: u64 = 8;
        let raw = mem
            .get_ref(addr, SIZE)
            .ok_or(ShaleError::LinearMemStoreError)?;
        Ok((
            SIZE,
            Self(u64::from_le_bytes(raw.deref().try_into().unwrap())),
        ))
    }
    fn dehydrate(&self) -> Vec<u8> {
        self.0.to_le_bytes().into()
    }
}

impl std::ops::Deref for U64Field {
    type Target = u64;
    fn deref(&self) -> &u64 {
        &self.0
    }
}

impl std::ops::DerefMut for U64Field {
    fn deref_mut(&mut self) -> &mut u64 {
        &mut self.0
    }
}

struct CompactSpaceInner {
    meta_space: Box<dyn MemStore>,
    compact_space: Box<dyn MemStore>,
    header: CompactSpaceHeaderSliced<'static>,
    alloc_max_walk: u64,
    regn_nbit: u64,
}

impl CompactSpaceInner {
    fn get_descriptor<'a>(
        &'a self, ptr: ObjPtr<CompactDescriptor>,
    ) -> Result<ObjRef<'a, CompactDescriptor>, ShaleError> {
        unsafe {
            super::get_obj_ref(&self.meta_space, ptr, CompactDescriptor::MSIZE)
        }
    }

    fn get_data_ref<'a, T: MummyItem + 'a>(
        &'a self, ptr: ObjPtr<T>, len_limit: u64,
    ) -> Result<ObjRef<'a, T>, ShaleError> {
        unsafe { super::get_obj_ref(&self.compact_space, ptr, len_limit) }
    }

    fn del_desc(
        &mut self, desc_addr: ObjPtr<CompactDescriptor>, wctx: &WriteContext,
    ) -> Result<(), ShaleError> {
        let desc_size = CompactDescriptor::MSIZE;
        debug_assert!(
            (desc_addr.addr - self.header.base_addr.addr) % desc_size == 0
        );
        self.header
            .meta_space_tail
            .write(|r| **r -= desc_size, true, wctx);
        if desc_addr.addr != **self.header.meta_space_tail {
            let desc_last = self.get_descriptor(unsafe {
                ObjPtr::new_from_addr(**self.header.meta_space_tail)
            })?;
            let mut desc = self.get_descriptor(unsafe {
                ObjPtr::new_from_addr(desc_addr.addr)
            })?;
            desc.write(|r| *r = *desc_last, true, wctx);
            let mut header = self.get_data_ref::<CompactHeader>(
                ObjPtr::new(desc.haddr),
                CompactHeader::MSIZE,
            )?;
            header.write(|h| h.desc_addr = desc_addr, true, wctx);
        }
        Ok(())
    }

    fn new_desc(
        &mut self, wctx: &WriteContext,
    ) -> Result<ObjPtr<CompactDescriptor>, ShaleError> {
        let addr = **self.header.meta_space_tail;
        self.header.meta_space_tail.write(
            |r| **r += CompactDescriptor::MSIZE,
            true,
            wctx,
        );
        Ok(unsafe { ObjPtr::new_from_addr(addr) })
    }

    fn free(
        &mut self, addr: u64, wctx: &WriteContext,
    ) -> Result<(), ShaleError> {
        let hsize = CompactHeader::MSIZE;
        let fsize = CompactFooter::MSIZE;
        let regn_size = 1 << self.regn_nbit;

        let mut offset = addr - hsize;
        let header_payload_size;
        {
            let header = self.get_data_ref::<CompactHeader>(
                ObjPtr::new(offset),
                CompactHeader::MSIZE,
            )?;
            header_payload_size = header.payload_size;
            assert!(!header.is_freed);
        }
        let mut h = offset;
        let mut payload_size = header_payload_size;

        if offset & (regn_size - 1) > 0 {
            // merge with lower data segment
            offset -= fsize;
            let pheader_is_freed;
            let pheader_payload_size;
            let pheader_desc_addr;
            {
                let pfooter = self.get_data_ref::<CompactFooter>(
                    ObjPtr::new(offset),
                    CompactFooter::MSIZE,
                )?;
                offset -= pfooter.payload_size + hsize;
                let pheader = self.get_data_ref::<CompactHeader>(
                    ObjPtr::new(offset),
                    CompactHeader::MSIZE,
                )?;
                pheader_is_freed = pheader.is_freed;
                pheader_payload_size = pheader.payload_size;
                pheader_desc_addr = pheader.desc_addr;
            }
            if pheader_is_freed {
                h = offset;
                payload_size += hsize + fsize + pheader_payload_size;
                self.del_desc(pheader_desc_addr, wctx)?;
            }
        }

        offset = addr + header_payload_size;
        let mut f = offset;

        if offset + fsize < **self.header.compact_space_tail &&
            (regn_size - (offset & (regn_size - 1))) >= fsize + hsize
        {
            // merge with higher data segment
            offset += fsize;
            let nheader_is_freed;
            let nheader_payload_size;
            let nheader_desc_addr;
            {
                let nheader = self.get_data_ref::<CompactHeader>(
                    ObjPtr::new(offset),
                    CompactHeader::MSIZE,
                )?;
                nheader_is_freed = nheader.is_freed;
                nheader_payload_size = nheader.payload_size;
                nheader_desc_addr = nheader.desc_addr;
            }
            if nheader_is_freed {
                offset += hsize + nheader_payload_size;
                f = offset;
                {
                    let nfooter = self.get_data_ref::<CompactFooter>(
                        ObjPtr::new(offset),
                        CompactFooter::MSIZE,
                    )?;
                    assert!(nheader_payload_size == nfooter.payload_size);
                }
                payload_size += hsize + fsize + nheader_payload_size;
                self.del_desc(nheader_desc_addr, wctx)?;
            }
        }

        let desc_addr = self.new_desc(wctx)?;
        {
            let mut desc = self.get_descriptor(desc_addr)?;
            desc.write(
                |d| {
                    d.payload_size = payload_size;
                    d.haddr = h;
                },
                true,
                wctx,
            );
        }
        let mut h = self.get_data_ref::<CompactHeader>(
            ObjPtr::new(h),
            CompactHeader::MSIZE,
        )?;
        let mut f = self.get_data_ref::<CompactFooter>(
            ObjPtr::new(f),
            CompactFooter::MSIZE,
        )?;
        h.write(
            |h| {
                h.payload_size = payload_size;
                h.is_freed = true;
                h.desc_addr = desc_addr;
            },
            true,
            wctx,
        );
        f.write(|f| f.payload_size = payload_size, true, wctx);
        Ok(())
    }

    fn alloc_from_freed(
        &mut self, length: u64, wctx: &WriteContext,
    ) -> Result<Option<u64>, ShaleError> {
        let tail = **self.header.meta_space_tail;
        if tail == self.header.base_addr.addr {
            return Ok(None)
        }

        let hsize = CompactHeader::MSIZE;
        let fsize = CompactFooter::MSIZE;
        let dsize = CompactDescriptor::MSIZE;

        let mut old_alloc_addr = *self.header.alloc_addr;

        if old_alloc_addr.addr >= tail {
            old_alloc_addr = *self.header.base_addr;
        }

        let mut ptr = old_alloc_addr;
        let mut res: Option<u64> = None;
        for _ in 0..self.alloc_max_walk {
            assert!(ptr.addr < tail);
            let desc_payload_size;
            let desc_haddr;
            {
                let desc = self.get_descriptor(ptr)?;
                desc_payload_size = desc.payload_size;
                desc_haddr = desc.haddr;
            }
            let exit = if desc_payload_size == length {
                // perfect match
                {
                    let mut header = self.get_data_ref::<CompactHeader>(
                        ObjPtr::new(desc_haddr),
                        CompactHeader::MSIZE,
                    )?;
                    assert_eq!(header.payload_size, desc_payload_size);
                    assert!(header.is_freed);
                    header.write(|h| h.is_freed = false, true, wctx);
                }
                self.del_desc(ptr, wctx)?;
                true
            } else if desc_payload_size > length + hsize + fsize {
                // able to split
                {
                    let mut lheader = self.get_data_ref::<CompactHeader>(
                        ObjPtr::new(desc_haddr),
                        CompactHeader::MSIZE,
                    )?;
                    assert_eq!(lheader.payload_size, desc_payload_size);
                    assert!(lheader.is_freed);
                    lheader.write(
                        |h| {
                            h.is_freed = false;
                            h.payload_size = length;
                        },
                        true,
                        wctx,
                    );
                }
                {
                    let mut lfooter = self.get_data_ref::<CompactFooter>(
                        ObjPtr::new(desc_haddr + hsize + length),
                        CompactFooter::MSIZE,
                    )?;
                    //assert!(lfooter.payload_size == desc_payload_size);
                    lfooter.write(|f| f.payload_size = length, true, wctx);
                }

                let offset = desc_haddr + hsize + length + fsize;
                let rpayload_size = desc_payload_size - length - fsize - hsize;
                let rdesc_addr = self.new_desc(wctx)?;
                {
                    let mut rdesc = self.get_descriptor(rdesc_addr)?;
                    rdesc.write(
                        |rd| {
                            rd.payload_size = rpayload_size;
                            rd.haddr = offset;
                        },
                        true,
                        wctx,
                    );
                }
                {
                    let mut rheader = self.get_data_ref::<CompactHeader>(
                        ObjPtr::new(offset),
                        CompactHeader::MSIZE,
                    )?;
                    rheader.write(
                        |rh| {
                            rh.is_freed = true;
                            rh.payload_size = rpayload_size;
                            rh.desc_addr = rdesc_addr;
                        },
                        true,
                        wctx,
                    );
                }
                {
                    let mut rfooter = self.get_data_ref::<CompactFooter>(
                        ObjPtr::new(offset + hsize + rpayload_size),
                        CompactFooter::MSIZE,
                    )?;
                    rfooter.write(
                        |f| f.payload_size = rpayload_size,
                        true,
                        wctx,
                    );
                }
                self.del_desc(ptr, wctx)?;
                true
            } else {
                false
            };
            if exit {
                self.header.alloc_addr.write(|r| *r = ptr, true, wctx);
                res = Some(desc_haddr + hsize);
                break
            }
            ptr.addr += dsize;
            if ptr.addr >= tail {
                ptr = *self.header.base_addr;
            }
            if ptr == old_alloc_addr {
                break
            }
        }
        Ok(res)
    }

    fn alloc_new(
        &mut self, length: u64, wctx: &WriteContext,
    ) -> Result<u64, ShaleError> {
        let offset = **self.header.compact_space_tail;
        let regn_size = 1 << self.regn_nbit;
        let mut total_length =
            CompactHeader::MSIZE + length + CompactFooter::MSIZE;
        self.header.compact_space_tail.write(
            |r| {
                // an item is always fully in one region
                let rem = regn_size - (offset & (regn_size - 1));
                if rem < total_length {
                    total_length += rem
                }
                **r += total_length
            },
            true,
            wctx,
        );
        let mut h = self.get_data_ref::<CompactHeader>(
            ObjPtr::new(offset),
            CompactHeader::MSIZE,
        )?;
        let mut f = self.get_data_ref::<CompactFooter>(
            ObjPtr::new(offset + CompactHeader::MSIZE + length),
            CompactFooter::MSIZE,
        )?;
        h.write(
            |h| {
                h.payload_size = length;
                h.is_freed = false;
                h.desc_addr = ObjPtr::new(0);
            },
            true,
            wctx,
        );
        f.write(|f| f.payload_size = length, true, wctx);
        Ok(offset + CompactHeader::MSIZE)
    }
}

pub struct CompactSpace {
    inner: UnsafeCell<CompactSpaceInner>,
}

impl CompactSpace {
    pub fn new(
        meta_space: Box<dyn MemStore>, compact_space: Box<dyn MemStore>,
        header: ObjRef<'static, CompactSpaceHeader>, alloc_max_walk: u64,
        regn_nbit: u64,
    ) -> Result<Self, ShaleError> {
        let cs = CompactSpace {
            inner: UnsafeCell::new(CompactSpaceInner {
                meta_space,
                compact_space,
                header: CompactSpaceHeader::into_fields(header)?,
                alloc_max_walk,
                regn_nbit,
            }),
        };
        Ok(cs)
    }
}

impl ShaleStore for CompactSpace {
    fn put_item<'a, T: MummyItem + 'a>(
        &'a self, item: T, extra: u64, wctx: &WriteContext,
    ) -> Result<ObjRef<'a, T>, ShaleError> {
        let bytes = item.dehydrate();
        let size = bytes.len() as u64 + extra;
        let inner = unsafe { &mut *self.inner.get() };
        let ptr: ObjPtr<T> = unsafe {
            ObjPtr::new_from_addr(
                if let Some(addr) = inner.alloc_from_freed(size, wctx)? {
                    addr
                } else {
                    inner.alloc_new(size, wctx)?
                },
            )
        };
        let mut u: ObjRef<T> = unsafe {
            super::obj_ref_from_item(
                &inner.compact_space,
                ptr.addr(),
                size,
                size,
                item,
            )?
        };
        u.write(|_| {}, true, wctx);
        Ok(u)
    }

    fn free_item<T: MummyItem>(
        &mut self, item: ObjPtr<T>, wctx: &WriteContext,
    ) -> Result<(), ShaleError> {
        self.inner.get_mut().free(item.addr(), wctx)
    }

    fn get_item<'a, T: MummyItem + 'a>(
        &'a self, ptr: ObjPtr<T>,
    ) -> Result<ObjRef<'a, T>, ShaleError> {
        let inner = unsafe { &*self.inner.get() };
        let h = inner.get_data_ref::<CompactHeader>(
            ObjPtr::new(ptr.addr() - CompactHeader::MSIZE),
            CompactHeader::MSIZE,
        )?;
        inner.get_data_ref(ptr, h.payload_size)
    }
}
