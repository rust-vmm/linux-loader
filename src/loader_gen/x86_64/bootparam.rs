// Rust translation of arch/x86/include/uapi/asm/bootparam.h and its dependencies.
// All structs use #[repr(C, packed)] to match the kernel's binary layout exactly.

#![allow(non_camel_case_types, non_snake_case)]

// --- setup_data.h constants ---

pub const SETUP_NONE: u32 = 0;
pub const SETUP_E820_EXT: u32 = 1;
pub const SETUP_DTB: u32 = 2;
pub const SETUP_PCI: u32 = 3;
pub const SETUP_EFI: u32 = 4;
pub const SETUP_APPLE_PROPERTIES: u32 = 5;
pub const SETUP_JAILHOUSE: u32 = 6;
pub const SETUP_CC_BLOB: u32 = 7;
pub const SETUP_IMA: u32 = 8;
pub const SETUP_RNG_SEED: u32 = 9;
pub const SETUP_KEXEC_KHO: u32 = 10;
pub const SETUP_ENUM_MAX: u32 = SETUP_KEXEC_KHO;
pub const SETUP_INDIRECT: u32 = 1 << 31;
pub const SETUP_TYPE_MAX: u32 = SETUP_ENUM_MAX | SETUP_INDIRECT;

// --- bootparam.h constants ---

pub const RAMDISK_IMAGE_START_MASK: u16 = 0x07FF;
pub const RAMDISK_PROMPT_FLAG: u16 = 0x8000;
pub const RAMDISK_LOAD_FLAG: u16 = 0x4000;

pub const LOADED_HIGH: u8 = 1 << 0;
pub const KASLR_FLAG: u8 = 1 << 1;
pub const QUIET_FLAG: u8 = 1 << 5;
pub const KEEP_SEGMENTS: u8 = 1 << 6;
pub const CAN_USE_HEAP: u8 = 1 << 7;

pub const XLF_KERNEL_64: u16 = 1 << 0;
pub const XLF_CAN_BE_LOADED_ABOVE_4G: u16 = 1 << 1;
pub const XLF_EFI_HANDOVER_32: u16 = 1 << 2;
pub const XLF_EFI_HANDOVER_64: u16 = 1 << 3;
pub const XLF_EFI_KEXEC: u16 = 1 << 4;
pub const XLF_5LEVEL: u16 = 1 << 5;
pub const XLF_5LEVEL_ENABLED: u16 = 1 << 6;
pub const XLF_MEM_ENCRYPTION: u16 = 1 << 7;

pub const E820_MAX_ENTRIES_ZEROPAGE: usize = 128;
pub const JAILHOUSE_SETUP_REQUIRED_VERSION: u32 = 1;

// --- edd.h constants ---

pub const EDDNR: u16 = 0x1e9;
pub const EDDBUF: u16 = 0xd00;
pub const EDDMAXNR: usize = 6;
pub const EDDEXTSIZE: usize = 8;
pub const EDDPARMSIZE: usize = 74;
pub const CHECKEXTENSIONSPRESENT: u8 = 0x41;
pub const GETDEVICEPARAMETERS: u8 = 0x48;
pub const LEGACYGETDEVICEPARAMETERS: u8 = 0x08;
pub const EDDMAGIC1: u16 = 0x55AA;
pub const EDDMAGIC2: u16 = 0xAA55;

pub const READ_SECTORS: u8 = 0x02;
pub const EDD_MBR_SIG_OFFSET: u16 = 0x1B8;
pub const EDD_MBR_SIG_BUF: u16 = 0x290;
pub const EDD_MBR_SIG_MAX: usize = 16;
pub const EDD_MBR_SIG_NR_BUF: u16 = 0x1ea;

pub const EDD_EXT_FIXED_DISK_ACCESS: u16 = 1 << 0;
pub const EDD_EXT_DEVICE_LOCKING_AND_EJECTING: u16 = 1 << 1;
pub const EDD_EXT_ENHANCED_DISK_DRIVE_SUPPORT: u16 = 1 << 2;
pub const EDD_EXT_64BIT_EXTENSIONS: u16 = 1 << 3;

pub const EDD_INFO_DMA_BOUNDARY_ERROR_TRANSPARENT: u16 = 1 << 0;
pub const EDD_INFO_GEOMETRY_VALID: u16 = 1 << 1;
pub const EDD_INFO_REMOVABLE: u16 = 1 << 2;
pub const EDD_INFO_WRITE_VERIFY: u16 = 1 << 3;
pub const EDD_INFO_MEDIA_CHANGE_NOTIFICATION: u16 = 1 << 4;
pub const EDD_INFO_LOCKABLE: u16 = 1 << 5;
pub const EDD_INFO_NO_MEDIA_PRESENT: u16 = 1 << 6;
pub const EDD_INFO_USE_INT13_FN50: u16 = 1 << 7;

// --- screen_info.h constants ---

pub const VIDEO_TYPE_MDA: u8 = 0x10;
pub const VIDEO_TYPE_CGA: u8 = 0x11;
pub const VIDEO_TYPE_EGAM: u8 = 0x20;
pub const VIDEO_TYPE_EGAC: u8 = 0x21;
pub const VIDEO_TYPE_VGAC: u8 = 0x22;
pub const VIDEO_TYPE_VLFB: u8 = 0x23;
pub const VIDEO_TYPE_PICA_S3: u8 = 0x30;
pub const VIDEO_TYPE_MIPS_G364: u8 = 0x31;
pub const VIDEO_TYPE_SGI: u8 = 0x33;
pub const VIDEO_TYPE_TGAC: u8 = 0x40;
pub const VIDEO_TYPE_SUN: u8 = 0x50;
pub const VIDEO_TYPE_SUNPCI: u8 = 0x51;
pub const VIDEO_TYPE_PMAC: u8 = 0x60;
pub const VIDEO_TYPE_EFI: u8 = 0x70;

pub const VIDEO_FLAGS_NOCURSOR: u8 = 1 << 0;
pub const VIDEO_CAPABILITY_SKIP_QUIRKS: u32 = 1 << 0;
pub const VIDEO_CAPABILITY_64BIT_BASE: u32 = 1 << 1;

// ============================================================================
// Struct definitions
// ============================================================================

/// From include/uapi/linux/screen_info.h
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct screen_info {
    pub orig_x: u8,
    pub orig_y: u8,
    pub ext_mem_k: u16,
    pub orig_video_page: u16,
    pub orig_video_mode: u8,
    pub orig_video_cols: u8,
    pub flags: u8,
    pub unused2: u8,
    pub orig_video_ega_bx: u16,
    pub unused3: u16,
    pub orig_video_lines: u8,
    pub orig_video_isVGA: u8,
    pub orig_video_points: u16,
    pub lfb_width: u16,
    pub lfb_height: u16,
    pub lfb_depth: u16,
    pub lfb_base: u32,
    pub lfb_size: u32,
    pub cl_magic: u16,
    pub cl_offset: u16,
    pub lfb_linelength: u16,
    pub red_size: u8,
    pub red_pos: u8,
    pub green_size: u8,
    pub green_pos: u8,
    pub blue_size: u8,
    pub blue_pos: u8,
    pub rsvd_size: u8,
    pub rsvd_pos: u8,
    pub vesapm_seg: u16,
    pub vesapm_off: u16,
    pub pages: u16,
    pub vesa_attributes: u16,
    pub capabilities: u32,
    pub ext_lfb_base: u32,
    pub _reserved: [u8; 2],
}

/// From include/uapi/linux/apm_bios.h
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct apm_bios_info {
    pub version: u16,
    pub cseg: u16,
    pub offset: u32,
    pub cseg_16: u16,
    pub dseg: u16,
    pub flags: u16,
    pub cseg_len: u16,
    pub cseg_16_len: u16,
    pub dseg_len: u16,
}

/// From arch/x86/include/uapi/asm/ist.h
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct ist_info {
    pub signature: u32,
    pub command: u32,
    pub event: u32,
    pub perf_level: u32,
}

/// From include/uapi/video/edid.h
#[repr(C, packed)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct edid_info {
    pub dummy: [u8; 128],
}

impl Default for edid_info {
    fn default() -> Self {
        unsafe { core::mem::zeroed() }
    }
}

/// From arch/x86/include/uapi/asm/setup_data.h
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct boot_e820_entry {
    pub addr: u64,
    pub size: u64,
    pub r#type: u32,
}

/// From include/uapi/linux/edd.h
///
/// The `interface_path` and `device_path` fields are unions in C. They are
/// represented here as fixed-size byte arrays (8 and 16 bytes respectively)
/// for simplicity. Transmute or use `ptr::read_unaligned` to access a
/// specific variant.
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct edd_device_params {
    pub length: u16,
    pub info_flags: u16,
    pub num_default_cylinders: u32,
    pub num_default_heads: u32,
    pub sectors_per_track: u32,
    pub number_of_sectors: u64,
    pub bytes_per_sector: u16,
    pub dpte_ptr: u32,
    pub key: u16,
    pub device_path_info_length: u8,
    pub reserved2: u8,
    pub reserved3: u16,
    pub host_bus_type: [u8; 4],
    pub interface_type: [u8; 8],
    pub interface_path: [u8; 8],
    pub device_path: [u8; 16],
    pub reserved4: u8,
    pub checksum: u8,
}

/// From include/uapi/linux/edd.h
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct edd_info {
    pub device: u8,
    pub version: u8,
    pub interface_support: u16,
    pub legacy_max_cylinder: u16,
    pub legacy_max_head: u8,
    pub legacy_sectors_per_track: u8,
    pub params: edd_device_params,
}

/// From arch/x86/include/uapi/asm/bootparam.h
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct setup_header {
    pub setup_sects: u8,
    pub root_flags: u16,
    pub syssize: u32,
    pub ram_size: u16,
    pub vid_mode: u16,
    pub root_dev: u16,
    pub boot_flag: u16,
    pub jump: u16,
    pub header: u32,
    pub version: u16,
    pub realmode_swtch: u32,
    pub start_sys_seg: u16,
    pub kernel_version: u16,
    pub type_of_loader: u8,
    pub loadflags: u8,
    pub setup_move_size: u16,
    pub code32_start: u32,
    pub ramdisk_image: u32,
    pub ramdisk_size: u32,
    pub bootsect_kludge: u32,
    pub heap_end_ptr: u16,
    pub ext_loader_ver: u8,
    pub ext_loader_type: u8,
    pub cmd_line_ptr: u32,
    pub initrd_addr_max: u32,
    pub kernel_alignment: u32,
    pub relocatable_kernel: u8,
    pub min_alignment: u8,
    pub xloadflags: u16,
    pub cmdline_size: u32,
    pub hardware_subarch: u32,
    pub hardware_subarch_data: u64,
    pub payload_offset: u32,
    pub payload_length: u32,
    pub setup_data: u64,
    pub pref_address: u64,
    pub init_size: u32,
    pub handover_offset: u32,
    pub kernel_info_offset: u32,
}

#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct sys_desc_table {
    pub length: u16,
    pub table: [u8; 14],
}

#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct olpc_ofw_header {
    pub ofw_magic: u32,
    pub ofw_version: u32,
    pub cif_handler: u32,
    pub irq_desc_table: u32,
}

#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct efi_info {
    pub efi_loader_signature: u32,
    pub efi_systab: u32,
    pub efi_memdesc_size: u32,
    pub efi_memdesc_version: u32,
    pub efi_memmap: u32,
    pub efi_memmap_size: u32,
    pub efi_systab_hi: u32,
    pub efi_memmap_hi: u32,
}

/// The x86 "zeropage" — exactly 4096 bytes.
///
/// `_pad7` size is `0x290 - 0x1f1 - sizeof(setup_header)` = 36 bytes.
#[repr(C, packed)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct boot_params {
    pub screen_info: screen_info,                                 // 0x000
    pub apm_bios_info: apm_bios_info,                             // 0x040
    pub _pad2: [u8; 4],                                           // 0x054
    pub tboot_addr: u64,                                          // 0x058
    pub ist_info: ist_info,                                       // 0x060
    pub acpi_rsdp_addr: u64,                                      // 0x070
    pub _pad3: [u8; 8],                                           // 0x078
    pub hd0_info: [u8; 16],                                       // 0x080
    pub hd1_info: [u8; 16],                                       // 0x090
    pub sys_desc_table: sys_desc_table,                           // 0x0a0
    pub olpc_ofw_header: olpc_ofw_header,                         // 0x0b0
    pub ext_ramdisk_image: u32,                                   // 0x0c0
    pub ext_ramdisk_size: u32,                                    // 0x0c4
    pub ext_cmd_line_ptr: u32,                                    // 0x0c8
    pub _pad4: [u8; 112],                                         // 0x0cc
    pub cc_blob_address: u32,                                     // 0x13c
    pub edid_info: edid_info,                                     // 0x140
    pub efi_info: efi_info,                                       // 0x1c0
    pub alt_mem_k: u32,                                           // 0x1e0
    pub scratch: u32,                                             // 0x1e4
    pub e820_entries: u8,                                         // 0x1e8
    pub eddbuf_entries: u8,                                       // 0x1e9
    pub edd_mbr_sig_buf_entries: u8,                              // 0x1ea
    pub kbd_status: u8,                                           // 0x1eb
    pub secure_boot: u8,                                          // 0x1ec
    pub _pad5: [u8; 2],                                           // 0x1ed
    pub sentinel: u8,                                             // 0x1ef
    pub _pad6: [u8; 1],                                           // 0x1f0
    pub hdr: setup_header,                                        // 0x1f1
    pub _pad7: [u8; 36],                                          // 0x26c
    pub edd_mbr_sig_buffer: [u32; EDD_MBR_SIG_MAX],               // 0x290
    pub e820_table: [boot_e820_entry; E820_MAX_ENTRIES_ZEROPAGE], // 0x2d0
    pub _pad8: [u8; 48],                                          // 0xcd0
    pub eddbuf: [edd_info; EDDMAXNR],                             // 0xd00
    pub _pad9: [u8; 276],                                         // 0xeec
}

#[repr(u32)]
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
pub enum x86_hardware_subarch {
    #[default]
    X86_SUBARCH_PC = 0,
    X86_SUBARCH_LGUEST = 1,
    X86_SUBARCH_XEN = 2,
    X86_SUBARCH_INTEL_MID = 3,
    X86_SUBARCH_CE4100 = 4,
}

pub const X86_NR_SUBARCHS: u32 = 5;

impl Default for boot_params {
    fn default() -> Self {
        unsafe { core::mem::zeroed() }
    }
}

// ============================================================================
// Compile-time layout assertions
// ============================================================================

const _: () = assert!(core::mem::size_of::<screen_info>() == 0x40);
const _: () = assert!(core::mem::size_of::<apm_bios_info>() == 0x14);
const _: () = assert!(core::mem::size_of::<ist_info>() == 0x10);
const _: () = assert!(core::mem::size_of::<edid_info>() == 0x80);
const _: () = assert!(core::mem::size_of::<boot_e820_entry>() == 20);
const _: () = assert!(core::mem::size_of::<edd_device_params>() == EDDPARMSIZE);
const _: () = assert!(core::mem::size_of::<edd_info>() == EDDEXTSIZE + EDDPARMSIZE);
const _: () = assert!(core::mem::size_of::<sys_desc_table>() == 0x10);
const _: () = assert!(core::mem::size_of::<olpc_ofw_header>() == 0x10);
const _: () = assert!(core::mem::size_of::<efi_info>() == 0x20);
const _: () = assert!(core::mem::size_of::<setup_header>() == 123);
const _: () = assert!(core::mem::size_of::<boot_params>() == 4096);
