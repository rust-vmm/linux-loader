// Rust translation of xen/include/public/arch-x86/hvm/start_info.h

#![allow(non_camel_case_types)]

pub const XEN_HVM_START_MAGIC_VALUE: u32 = 0x336ec578;

pub const XEN_HVM_MEMMAP_TYPE_RAM: u32 = 1;
pub const XEN_HVM_MEMMAP_TYPE_RESERVED: u32 = 2;
pub const XEN_HVM_MEMMAP_TYPE_ACPI: u32 = 3;
pub const XEN_HVM_MEMMAP_TYPE_NVS: u32 = 4;
pub const XEN_HVM_MEMMAP_TYPE_UNUSABLE: u32 = 5;
pub const XEN_HVM_MEMMAP_TYPE_DISABLED: u32 = 6;
pub const XEN_HVM_MEMMAP_TYPE_PMEM: u32 = 7;

/// Start of day structure passed to PVH guests and to HVM guests in %ebx.
///
/// A 0 value in any address field means not present.
/// Version 0 ends after `rsdp_paddr`; fields from `memmap_paddr` onward
/// are only present in version 1+.
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct hvm_start_info {
    pub magic: u32,
    pub version: u32,
    pub flags: u32,
    pub nr_modules: u32,
    pub modlist_paddr: u64,
    pub cmdline_paddr: u64,
    pub rsdp_paddr: u64,
    pub memmap_paddr: u64,
    pub memmap_entries: u32,
    pub reserved: u32,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct hvm_modlist_entry {
    pub paddr: u64,
    pub size: u64,
    pub cmdline_paddr: u64,
    pub reserved: u64,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct hvm_memmap_table_entry {
    pub addr: u64,
    pub size: u64,
    pub type_: u32,
    pub reserved: u32,
}

// Compile-time layout assertions (sizes from the spec comments)
const _: () = assert!(core::mem::size_of::<hvm_start_info>() == 56);
const _: () = assert!(core::mem::size_of::<hvm_modlist_entry>() == 32);
const _: () = assert!(core::mem::size_of::<hvm_memmap_table_entry>() == 24);
