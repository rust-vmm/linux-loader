// Rust translation of include/uapi/linux/elf.h and include/uapi/linux/elf-em.h.
// All structs use #[repr(C)] to match the standard ELF ABI layout.

#![allow(non_camel_case_types, non_snake_case, non_upper_case_globals)]

// ============================================================================
// ELF base type aliases
// ============================================================================

pub type Elf32_Addr = u32;
pub type Elf32_Half = u16;
pub type Elf32_Off = u32;
pub type Elf32_Sword = i32;
pub type Elf32_Word = u32;
pub type Elf32_Versym = u16;

pub type Elf64_Addr = u64;
pub type Elf64_Half = u16;
pub type Elf64_SHalf = i16;
pub type Elf64_Off = u64;
pub type Elf64_Sword = i32;
pub type Elf64_Word = u32;
pub type Elf64_Xword = u64;
pub type Elf64_Sxword = i64;
pub type Elf64_Versym = u16;

// ============================================================================
// ELF machine types (elf-em.h)
// ============================================================================

pub const EM_NONE: u16 = 0;
pub const EM_M32: u16 = 1;
pub const EM_SPARC: u16 = 2;
pub const EM_386: u16 = 3;
pub const EM_68K: u16 = 4;
pub const EM_88K: u16 = 5;
pub const EM_486: u16 = 6;
pub const EM_860: u16 = 7;
pub const EM_MIPS: u16 = 8;
pub const EM_MIPS_RS3_LE: u16 = 10;
pub const EM_MIPS_RS4_BE: u16 = 10;
pub const EM_PARISC: u16 = 15;
pub const EM_SPARC32PLUS: u16 = 18;
pub const EM_PPC: u16 = 20;
pub const EM_PPC64: u16 = 21;
pub const EM_SPU: u16 = 23;
pub const EM_ARM: u16 = 40;
pub const EM_SH: u16 = 42;
pub const EM_SPARCV9: u16 = 43;
pub const EM_H8_300: u16 = 46;
pub const EM_IA_64: u16 = 50;
pub const EM_X86_64: u16 = 62;
pub const EM_S390: u16 = 22;
pub const EM_CRIS: u16 = 76;
pub const EM_M32R: u16 = 88;
pub const EM_MN10300: u16 = 89;
pub const EM_OPENRISC: u16 = 92;
pub const EM_ARCOMPACT: u16 = 93;
pub const EM_XTENSA: u16 = 94;
pub const EM_BLACKFIN: u16 = 106;
pub const EM_UNICORE: u16 = 110;
pub const EM_ALTERA_NIOS2: u16 = 113;
pub const EM_TI_C6000: u16 = 140;
pub const EM_HEXAGON: u16 = 164;
pub const EM_NDS32: u16 = 167;
pub const EM_AARCH64: u16 = 183;
pub const EM_TILEPRO: u16 = 188;
pub const EM_MICROBLAZE: u16 = 189;
pub const EM_TILEGX: u16 = 191;
pub const EM_ARCV2: u16 = 195;
pub const EM_RISCV: u16 = 243;
pub const EM_BPF: u16 = 247;
pub const EM_CSKY: u16 = 252;
pub const EM_LOONGARCH: u16 = 258;
pub const EM_FRV: u16 = 0x5441;
pub const EM_ALPHA: u16 = 0x9026;
pub const EM_CYGNUS_M32R: u16 = 0x9041;
pub const EM_S390_OLD: u16 = 0xA390;
pub const EM_CYGNUS_MN10300: u16 = 0xbeef;

// ============================================================================
// Segment types (p_type)
// ============================================================================

pub const PT_NULL: u32 = 0;
pub const PT_LOAD: u32 = 1;
pub const PT_DYNAMIC: u32 = 2;
pub const PT_INTERP: u32 = 3;
pub const PT_NOTE: u32 = 4;
pub const PT_SHLIB: u32 = 5;
pub const PT_PHDR: u32 = 6;
pub const PT_TLS: u32 = 7;
pub const PT_LOOS: u32 = 0x60000000;
pub const PT_HIOS: u32 = 0x6fffffff;
pub const PT_LOPROC: u32 = 0x70000000;
pub const PT_HIPROC: u32 = 0x7fffffff;
pub const PT_GNU_EH_FRAME: u32 = PT_LOOS + 0x474e550;
pub const PT_GNU_STACK: u32 = PT_LOOS + 0x474e551;
pub const PT_GNU_RELRO: u32 = PT_LOOS + 0x474e552;
pub const PT_GNU_PROPERTY: u32 = PT_LOOS + 0x474e553;

pub const PT_AARCH64_MEMTAG_MTE: u32 = PT_LOPROC + 0x2;

pub const PN_XNUM: u16 = 0xffff;

// ============================================================================
// ELF file types (e_type)
// ============================================================================

pub const ET_NONE: u16 = 0;
pub const ET_REL: u16 = 1;
pub const ET_EXEC: u16 = 2;
pub const ET_DYN: u16 = 3;
pub const ET_CORE: u16 = 4;
pub const ET_LOPROC: u16 = 0xff00;
pub const ET_HIPROC: u16 = 0xffff;

// ============================================================================
// Dynamic section tags (d_tag)
// ============================================================================

pub const DT_NULL: i64 = 0;
pub const DT_NEEDED: i64 = 1;
pub const DT_PLTRELSZ: i64 = 2;
pub const DT_PLTGOT: i64 = 3;
pub const DT_HASH: i64 = 4;
pub const DT_STRTAB: i64 = 5;
pub const DT_SYMTAB: i64 = 6;
pub const DT_RELA: i64 = 7;
pub const DT_RELASZ: i64 = 8;
pub const DT_RELAENT: i64 = 9;
pub const DT_STRSZ: i64 = 10;
pub const DT_SYMENT: i64 = 11;
pub const DT_INIT: i64 = 12;
pub const DT_FINI: i64 = 13;
pub const DT_SONAME: i64 = 14;
pub const DT_RPATH: i64 = 15;
pub const DT_SYMBOLIC: i64 = 16;
pub const DT_REL: i64 = 17;
pub const DT_RELSZ: i64 = 18;
pub const DT_RELENT: i64 = 19;
pub const DT_PLTREL: i64 = 20;
pub const DT_DEBUG: i64 = 21;
pub const DT_TEXTREL: i64 = 22;
pub const DT_JMPREL: i64 = 23;
pub const DT_ENCODING: i64 = 32;
pub const OLD_DT_LOOS: i64 = 0x60000000;
pub const DT_LOOS: i64 = 0x6000000d;
pub const DT_HIOS: i64 = 0x6ffff000;
pub const DT_VALRNGLO: i64 = 0x6ffffd00;
pub const DT_VALRNGHI: i64 = 0x6ffffdff;
pub const DT_ADDRRNGLO: i64 = 0x6ffffe00;
pub const DT_GNU_HASH: i64 = 0x6ffffef5;
pub const DT_ADDRRNGHI: i64 = 0x6ffffeff;
pub const DT_VERSYM: i64 = 0x6ffffff0;
pub const DT_RELACOUNT: i64 = 0x6ffffff9;
pub const DT_RELCOUNT: i64 = 0x6ffffffa;
pub const DT_FLAGS_1: i64 = 0x6ffffffb;
pub const DT_VERDEF: i64 = 0x6ffffffc;
pub const DT_VERDEFNUM: i64 = 0x6ffffffd;
pub const DT_VERNEED: i64 = 0x6ffffffe;
pub const DT_VERNEEDNUM: i64 = 0x6fffffff;
pub const OLD_DT_HIOS: i64 = 0x6fffffff;
pub const DT_LOPROC: i64 = 0x70000000;
pub const DT_HIPROC: i64 = 0x7fffffff;

// ============================================================================
// Symbol binding and type
// ============================================================================

pub const STB_LOCAL: u8 = 0;
pub const STB_GLOBAL: u8 = 1;
pub const STB_WEAK: u8 = 2;

pub const STN_UNDEF: u32 = 0;

pub const STT_NOTYPE: u8 = 0;
pub const STT_OBJECT: u8 = 1;
pub const STT_FUNC: u8 = 2;
pub const STT_SECTION: u8 = 3;
pub const STT_FILE: u8 = 4;
pub const STT_COMMON: u8 = 5;
pub const STT_TLS: u8 = 6;

pub const VER_FLG_BASE: u16 = 0x1;
pub const VER_FLG_WEAK: u16 = 0x2;

#[inline]
pub const fn ELF_ST_BIND(info: u8) -> u8 {
    info >> 4
}

#[inline]
pub const fn ELF_ST_TYPE(info: u8) -> u8 {
    info & 0xf
}

#[inline]
pub const fn ELF32_ST_BIND(info: u8) -> u8 {
    ELF_ST_BIND(info)
}

#[inline]
pub const fn ELF32_ST_TYPE(info: u8) -> u8 {
    ELF_ST_TYPE(info)
}

#[inline]
pub const fn ELF64_ST_BIND(info: u8) -> u8 {
    ELF_ST_BIND(info)
}

#[inline]
pub const fn ELF64_ST_TYPE(info: u8) -> u8 {
    ELF_ST_TYPE(info)
}

// ============================================================================
// Relocation helpers
// ============================================================================

#[inline]
pub const fn ELF32_R_SYM(info: u32) -> u32 {
    info >> 8
}

#[inline]
pub const fn ELF32_R_TYPE(info: u32) -> u8 {
    (info & 0xff) as u8
}

#[inline]
pub const fn ELF64_R_SYM(info: u64) -> u32 {
    (info >> 32) as u32
}

#[inline]
pub const fn ELF64_R_TYPE(info: u64) -> u32 {
    (info & 0xffffffff) as u32
}

// ============================================================================
// Segment permission flags (p_flags)
// ============================================================================

pub const PF_R: u32 = 0x4;
pub const PF_W: u32 = 0x2;
pub const PF_X: u32 = 0x1;

// ============================================================================
// Section header types (sh_type)
// ============================================================================

pub const SHT_NULL: u32 = 0;
pub const SHT_PROGBITS: u32 = 1;
pub const SHT_SYMTAB: u32 = 2;
pub const SHT_STRTAB: u32 = 3;
pub const SHT_RELA: u32 = 4;
pub const SHT_HASH: u32 = 5;
pub const SHT_DYNAMIC: u32 = 6;
pub const SHT_NOTE: u32 = 7;
pub const SHT_NOBITS: u32 = 8;
pub const SHT_REL: u32 = 9;
pub const SHT_SHLIB: u32 = 10;
pub const SHT_DYNSYM: u32 = 11;
pub const SHT_NUM: u32 = 12;
pub const SHT_LOPROC: u32 = 0x70000000;
pub const SHT_HIPROC: u32 = 0x7fffffff;
pub const SHT_LOUSER: u32 = 0x80000000;
pub const SHT_HIUSER: u32 = 0xffffffff;

// ============================================================================
// Section header flags (sh_flags)
// ============================================================================

pub const SHF_WRITE: u64 = 0x1;
pub const SHF_ALLOC: u64 = 0x2;
pub const SHF_EXECINSTR: u64 = 0x4;
pub const SHF_MERGE: u64 = 0x10;
pub const SHF_STRINGS: u64 = 0x20;
pub const SHF_INFO_LINK: u64 = 0x40;
pub const SHF_LINK_ORDER: u64 = 0x80;
pub const SHF_OS_NONCONFORMING: u64 = 0x100;
pub const SHF_GROUP: u64 = 0x200;
pub const SHF_TLS: u64 = 0x400;
pub const SHF_RELA_LIVEPATCH: u64 = 0x00100000;
pub const SHF_RO_AFTER_INIT: u64 = 0x00200000;
pub const SHF_ORDERED: u64 = 0x04000000;
pub const SHF_EXCLUDE: u64 = 0x08000000;
pub const SHF_MASKOS: u64 = 0x0ff00000;
pub const SHF_MASKPROC: u64 = 0xf0000000;

// ============================================================================
// Special section indexes
// ============================================================================

pub const SHN_UNDEF: u16 = 0;
pub const SHN_LORESERVE: u16 = 0xff00;
pub const SHN_LOPROC: u16 = 0xff00;
pub const SHN_HIPROC: u16 = 0xff1f;
pub const SHN_LIVEPATCH: u16 = 0xff20;
pub const SHN_ABS: u16 = 0xfff1;
pub const SHN_COMMON: u16 = 0xfff2;
pub const SHN_HIRESERVE: u16 = 0xffff;

// ============================================================================
// e_ident[] indexes and values
// ============================================================================

pub const EI_MAG0: usize = 0;
pub const EI_MAG1: usize = 1;
pub const EI_MAG2: usize = 2;
pub const EI_MAG3: usize = 3;
pub const EI_CLASS: usize = 4;
pub const EI_DATA: usize = 5;
pub const EI_VERSION: usize = 6;
pub const EI_OSABI: usize = 7;
pub const EI_PAD: usize = 8;
pub const EI_NIDENT: usize = 16;

pub const ELFMAG0: u8 = 0x7f;
pub const ELFMAG1: u8 = b'E';
pub const ELFMAG2: u8 = b'L';
pub const ELFMAG3: u8 = b'F';
pub const ELFMAG: &[u8; 4] = b"\x7fELF";
pub const SELFMAG: usize = 4;

pub const ELFCLASSNONE: u8 = 0;
pub const ELFCLASS32: u8 = 1;
pub const ELFCLASS64: u8 = 2;
pub const ELFCLASSNUM: u8 = 3;

pub const ELFDATANONE: u8 = 0;
pub const ELFDATA2LSB: u8 = 1;
pub const ELFDATA2MSB: u8 = 2;

pub const EV_NONE: u8 = 0;
pub const EV_CURRENT: u8 = 1;
pub const EV_NUM: u8 = 2;

pub const ELFOSABI_NONE: u8 = 0;
pub const ELFOSABI_LINUX: u8 = 3;

// ============================================================================
// GNU property types
// ============================================================================

pub const GNU_PROPERTY_AARCH64_FEATURE_1_AND: u32 = 0xc0000000;
pub const GNU_PROPERTY_AARCH64_FEATURE_1_BTI: u32 = 1 << 0;

// ============================================================================
// Note types (NT_*) and note names (NN_*)
// ============================================================================

pub const NN_GNU_PROPERTY_TYPE_0: &str = "GNU";
pub const NT_GNU_PROPERTY_TYPE_0: u32 = 5;

pub const NN_PRSTATUS: &str = "CORE";
pub const NT_PRSTATUS: u32 = 1;
pub const NN_PRFPREG: &str = "CORE";
pub const NT_PRFPREG: u32 = 2;
pub const NN_PRPSINFO: &str = "CORE";
pub const NT_PRPSINFO: u32 = 3;
pub const NN_TASKSTRUCT: &str = "CORE";
pub const NT_TASKSTRUCT: u32 = 4;
pub const NN_AUXV: &str = "CORE";
pub const NT_AUXV: u32 = 6;
pub const NN_SIGINFO: &str = "CORE";
pub const NT_SIGINFO: u32 = 0x53494749;
pub const NN_FILE: &str = "CORE";
pub const NT_FILE: u32 = 0x46494c45;
pub const NN_PRXFPREG: &str = "LINUX";
pub const NT_PRXFPREG: u32 = 0x46e62b7f;
pub const NN_PPC_VMX: &str = "LINUX";
pub const NT_PPC_VMX: u32 = 0x100;
pub const NN_PPC_SPE: &str = "LINUX";
pub const NT_PPC_SPE: u32 = 0x101;
pub const NN_PPC_VSX: &str = "LINUX";
pub const NT_PPC_VSX: u32 = 0x102;
pub const NN_PPC_TAR: &str = "LINUX";
pub const NT_PPC_TAR: u32 = 0x103;
pub const NN_PPC_PPR: &str = "LINUX";
pub const NT_PPC_PPR: u32 = 0x104;
pub const NN_PPC_DSCR: &str = "LINUX";
pub const NT_PPC_DSCR: u32 = 0x105;
pub const NN_PPC_EBB: &str = "LINUX";
pub const NT_PPC_EBB: u32 = 0x106;
pub const NN_PPC_PMU: &str = "LINUX";
pub const NT_PPC_PMU: u32 = 0x107;
pub const NN_PPC_TM_CGPR: &str = "LINUX";
pub const NT_PPC_TM_CGPR: u32 = 0x108;
pub const NN_PPC_TM_CFPR: &str = "LINUX";
pub const NT_PPC_TM_CFPR: u32 = 0x109;
pub const NN_PPC_TM_CVMX: &str = "LINUX";
pub const NT_PPC_TM_CVMX: u32 = 0x10a;
pub const NN_PPC_TM_CVSX: &str = "LINUX";
pub const NT_PPC_TM_CVSX: u32 = 0x10b;
pub const NN_PPC_TM_SPR: &str = "LINUX";
pub const NT_PPC_TM_SPR: u32 = 0x10c;
pub const NN_PPC_TM_CTAR: &str = "LINUX";
pub const NT_PPC_TM_CTAR: u32 = 0x10d;
pub const NN_PPC_TM_CPPR: &str = "LINUX";
pub const NT_PPC_TM_CPPR: u32 = 0x10e;
pub const NN_PPC_TM_CDSCR: &str = "LINUX";
pub const NT_PPC_TM_CDSCR: u32 = 0x10f;
pub const NN_PPC_PKEY: &str = "LINUX";
pub const NT_PPC_PKEY: u32 = 0x110;
pub const NN_PPC_DEXCR: &str = "LINUX";
pub const NT_PPC_DEXCR: u32 = 0x111;
pub const NN_PPC_HASHKEYR: &str = "LINUX";
pub const NT_PPC_HASHKEYR: u32 = 0x112;
pub const NN_386_TLS: &str = "LINUX";
pub const NT_386_TLS: u32 = 0x200;
pub const NN_386_IOPERM: &str = "LINUX";
pub const NT_386_IOPERM: u32 = 0x201;
pub const NN_X86_XSTATE: &str = "LINUX";
pub const NT_X86_XSTATE: u32 = 0x202;
pub const NN_X86_SHSTK: &str = "LINUX";
pub const NT_X86_SHSTK: u32 = 0x204;
pub const NN_X86_XSAVE_LAYOUT: &str = "LINUX";
pub const NT_X86_XSAVE_LAYOUT: u32 = 0x205;
pub const NN_S390_HIGH_GPRS: &str = "LINUX";
pub const NT_S390_HIGH_GPRS: u32 = 0x300;
pub const NN_S390_TIMER: &str = "LINUX";
pub const NT_S390_TIMER: u32 = 0x301;
pub const NN_S390_TODCMP: &str = "LINUX";
pub const NT_S390_TODCMP: u32 = 0x302;
pub const NN_S390_TODPREG: &str = "LINUX";
pub const NT_S390_TODPREG: u32 = 0x303;
pub const NN_S390_CTRS: &str = "LINUX";
pub const NT_S390_CTRS: u32 = 0x304;
pub const NN_S390_PREFIX: &str = "LINUX";
pub const NT_S390_PREFIX: u32 = 0x305;
pub const NN_S390_LAST_BREAK: &str = "LINUX";
pub const NT_S390_LAST_BREAK: u32 = 0x306;
pub const NN_S390_SYSTEM_CALL: &str = "LINUX";
pub const NT_S390_SYSTEM_CALL: u32 = 0x307;
pub const NN_S390_TDB: &str = "LINUX";
pub const NT_S390_TDB: u32 = 0x308;
pub const NN_S390_VXRS_LOW: &str = "LINUX";
pub const NT_S390_VXRS_LOW: u32 = 0x309;
pub const NN_S390_VXRS_HIGH: &str = "LINUX";
pub const NT_S390_VXRS_HIGH: u32 = 0x30a;
pub const NN_S390_GS_CB: &str = "LINUX";
pub const NT_S390_GS_CB: u32 = 0x30b;
pub const NN_S390_GS_BC: &str = "LINUX";
pub const NT_S390_GS_BC: u32 = 0x30c;
pub const NN_S390_RI_CB: &str = "LINUX";
pub const NT_S390_RI_CB: u32 = 0x30d;
pub const NN_S390_PV_CPU_DATA: &str = "LINUX";
pub const NT_S390_PV_CPU_DATA: u32 = 0x30e;
pub const NN_ARM_VFP: &str = "LINUX";
pub const NT_ARM_VFP: u32 = 0x400;
pub const NN_ARM_TLS: &str = "LINUX";
pub const NT_ARM_TLS: u32 = 0x401;
pub const NN_ARM_HW_BREAK: &str = "LINUX";
pub const NT_ARM_HW_BREAK: u32 = 0x402;
pub const NN_ARM_HW_WATCH: &str = "LINUX";
pub const NT_ARM_HW_WATCH: u32 = 0x403;
pub const NN_ARM_SYSTEM_CALL: &str = "LINUX";
pub const NT_ARM_SYSTEM_CALL: u32 = 0x404;
pub const NN_ARM_SVE: &str = "LINUX";
pub const NT_ARM_SVE: u32 = 0x405;
pub const NN_ARM_PAC_MASK: &str = "LINUX";
pub const NT_ARM_PAC_MASK: u32 = 0x406;
pub const NN_ARM_PACA_KEYS: &str = "LINUX";
pub const NT_ARM_PACA_KEYS: u32 = 0x407;
pub const NN_ARM_PACG_KEYS: &str = "LINUX";
pub const NT_ARM_PACG_KEYS: u32 = 0x408;
pub const NN_ARM_TAGGED_ADDR_CTRL: &str = "LINUX";
pub const NT_ARM_TAGGED_ADDR_CTRL: u32 = 0x409;
pub const NN_ARM_PAC_ENABLED_KEYS: &str = "LINUX";
pub const NT_ARM_PAC_ENABLED_KEYS: u32 = 0x40a;
pub const NN_ARM_SSVE: &str = "LINUX";
pub const NT_ARM_SSVE: u32 = 0x40b;
pub const NN_ARM_ZA: &str = "LINUX";
pub const NT_ARM_ZA: u32 = 0x40c;
pub const NN_ARM_ZT: &str = "LINUX";
pub const NT_ARM_ZT: u32 = 0x40d;
pub const NN_ARM_FPMR: &str = "LINUX";
pub const NT_ARM_FPMR: u32 = 0x40e;
pub const NN_ARM_POE: &str = "LINUX";
pub const NT_ARM_POE: u32 = 0x40f;
pub const NN_ARM_GCS: &str = "LINUX";
pub const NT_ARM_GCS: u32 = 0x410;
pub const NN_ARC_V2: &str = "LINUX";
pub const NT_ARC_V2: u32 = 0x600;
pub const NN_VMCOREDD: &str = "LINUX";
pub const NT_VMCOREDD: u32 = 0x700;
pub const NN_MIPS_DSP: &str = "LINUX";
pub const NT_MIPS_DSP: u32 = 0x800;
pub const NN_MIPS_FP_MODE: &str = "LINUX";
pub const NT_MIPS_FP_MODE: u32 = 0x801;
pub const NN_MIPS_MSA: &str = "LINUX";
pub const NT_MIPS_MSA: u32 = 0x802;
pub const NN_RISCV_CSR: &str = "LINUX";
pub const NT_RISCV_CSR: u32 = 0x900;
pub const NN_RISCV_VECTOR: &str = "LINUX";
pub const NT_RISCV_VECTOR: u32 = 0x901;
pub const NN_RISCV_TAGGED_ADDR_CTRL: &str = "LINUX";
pub const NT_RISCV_TAGGED_ADDR_CTRL: u32 = 0x902;
pub const NN_RISCV_USER_CFI: &str = "LINUX";
pub const NT_RISCV_USER_CFI: u32 = 0x903;
pub const NN_LOONGARCH_CPUCFG: &str = "LINUX";
pub const NT_LOONGARCH_CPUCFG: u32 = 0xa00;
pub const NN_LOONGARCH_CSR: &str = "LINUX";
pub const NT_LOONGARCH_CSR: u32 = 0xa01;
pub const NN_LOONGARCH_LSX: &str = "LINUX";
pub const NT_LOONGARCH_LSX: u32 = 0xa02;
pub const NN_LOONGARCH_LASX: &str = "LINUX";
pub const NT_LOONGARCH_LASX: u32 = 0xa03;
pub const NN_LOONGARCH_LBT: &str = "LINUX";
pub const NT_LOONGARCH_LBT: u32 = 0xa04;
pub const NN_LOONGARCH_HW_BREAK: &str = "LINUX";
pub const NT_LOONGARCH_HW_BREAK: u32 = 0xa05;
pub const NN_LOONGARCH_HW_WATCH: &str = "LINUX";
pub const NT_LOONGARCH_HW_WATCH: u32 = 0xa06;

// ============================================================================
// Struct definitions — 32-bit ELF
// ============================================================================

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf32_Ehdr {
    pub e_ident: [u8; EI_NIDENT],
    pub e_type: Elf32_Half,
    pub e_machine: Elf32_Half,
    pub e_version: Elf32_Word,
    pub e_entry: Elf32_Addr,
    pub e_phoff: Elf32_Off,
    pub e_shoff: Elf32_Off,
    pub e_flags: Elf32_Word,
    pub e_ehsize: Elf32_Half,
    pub e_phentsize: Elf32_Half,
    pub e_phnum: Elf32_Half,
    pub e_shentsize: Elf32_Half,
    pub e_shnum: Elf32_Half,
    pub e_shstrndx: Elf32_Half,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf32_Phdr {
    pub p_type: Elf32_Word,
    pub p_offset: Elf32_Off,
    pub p_vaddr: Elf32_Addr,
    pub p_paddr: Elf32_Addr,
    pub p_filesz: Elf32_Word,
    pub p_memsz: Elf32_Word,
    pub p_flags: Elf32_Word,
    pub p_align: Elf32_Word,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf32_Shdr {
    pub sh_name: Elf32_Word,
    pub sh_type: Elf32_Word,
    pub sh_flags: Elf32_Word,
    pub sh_addr: Elf32_Addr,
    pub sh_offset: Elf32_Off,
    pub sh_size: Elf32_Word,
    pub sh_link: Elf32_Word,
    pub sh_info: Elf32_Word,
    pub sh_addralign: Elf32_Word,
    pub sh_entsize: Elf32_Word,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf32_Sym {
    pub st_name: Elf32_Word,
    pub st_value: Elf32_Addr,
    pub st_size: Elf32_Word,
    pub st_info: u8,
    pub st_other: u8,
    pub st_shndx: Elf32_Half,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf32_Rel {
    pub r_offset: Elf32_Addr,
    pub r_info: Elf32_Word,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf32_Rela {
    pub r_offset: Elf32_Addr,
    pub r_info: Elf32_Word,
    pub r_addend: Elf32_Sword,
}

/// Anonymous union in C; named here because Rust requires it.
/// Cannot derive Debug, Default, or PartialEq on unions.
#[repr(C)]
#[derive(Copy, Clone)]
pub union Elf32_Dyn_d_un {
    pub d_val: Elf32_Sword,
    pub d_ptr: Elf32_Addr,
}

/// Contains a union field (d_un), so Debug, Default, and PartialEq
/// cannot be derived.
#[repr(C)]
#[derive(Copy, Clone)]
pub struct Elf32_Dyn {
    pub d_tag: Elf32_Sword,
    pub d_un: Elf32_Dyn_d_un,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf32_Nhdr {
    pub n_namesz: Elf32_Word,
    pub n_descsz: Elf32_Word,
    pub n_type: Elf32_Word,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf32_Verdef {
    pub vd_version: Elf32_Half,
    pub vd_flags: Elf32_Half,
    pub vd_ndx: Elf32_Half,
    pub vd_cnt: Elf32_Half,
    pub vd_hash: Elf32_Word,
    pub vd_aux: Elf32_Word,
    pub vd_next: Elf32_Word,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf32_Verdaux {
    pub vda_name: Elf32_Word,
    pub vda_next: Elf32_Word,
}

// ============================================================================
// Struct definitions — 64-bit ELF
// ============================================================================

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf64_Ehdr {
    pub e_ident: [u8; EI_NIDENT],
    pub e_type: Elf64_Half,
    pub e_machine: Elf64_Half,
    pub e_version: Elf64_Word,
    pub e_entry: Elf64_Addr,
    pub e_phoff: Elf64_Off,
    pub e_shoff: Elf64_Off,
    pub e_flags: Elf64_Word,
    pub e_ehsize: Elf64_Half,
    pub e_phentsize: Elf64_Half,
    pub e_phnum: Elf64_Half,
    pub e_shentsize: Elf64_Half,
    pub e_shnum: Elf64_Half,
    pub e_shstrndx: Elf64_Half,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf64_Phdr {
    pub p_type: Elf64_Word,
    pub p_flags: Elf64_Word,
    pub p_offset: Elf64_Off,
    pub p_vaddr: Elf64_Addr,
    pub p_paddr: Elf64_Addr,
    pub p_filesz: Elf64_Xword,
    pub p_memsz: Elf64_Xword,
    pub p_align: Elf64_Xword,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf64_Shdr {
    pub sh_name: Elf64_Word,
    pub sh_type: Elf64_Word,
    pub sh_flags: Elf64_Xword,
    pub sh_addr: Elf64_Addr,
    pub sh_offset: Elf64_Off,
    pub sh_size: Elf64_Xword,
    pub sh_link: Elf64_Word,
    pub sh_info: Elf64_Word,
    pub sh_addralign: Elf64_Xword,
    pub sh_entsize: Elf64_Xword,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf64_Sym {
    pub st_name: Elf64_Word,
    pub st_info: u8,
    pub st_other: u8,
    pub st_shndx: Elf64_Half,
    pub st_value: Elf64_Addr,
    pub st_size: Elf64_Xword,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf64_Rel {
    pub r_offset: Elf64_Addr,
    pub r_info: Elf64_Xword,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf64_Rela {
    pub r_offset: Elf64_Addr,
    pub r_info: Elf64_Xword,
    pub r_addend: Elf64_Sxword,
}

/// Anonymous union in C; named here because Rust requires it.
/// Cannot derive Debug, Default, or PartialEq on unions.
#[repr(C)]
#[derive(Copy, Clone)]
pub union Elf64_Dyn_d_un {
    pub d_val: Elf64_Xword,
    pub d_ptr: Elf64_Addr,
}

/// Contains a union field (d_un), so Debug, Default, and PartialEq
/// cannot be derived.
#[repr(C)]
#[derive(Copy, Clone)]
pub struct Elf64_Dyn {
    pub d_tag: Elf64_Sxword,
    pub d_un: Elf64_Dyn_d_un,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf64_Nhdr {
    pub n_namesz: Elf64_Word,
    pub n_descsz: Elf64_Word,
    pub n_type: Elf64_Word,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf64_Verdef {
    pub vd_version: Elf64_Half,
    pub vd_flags: Elf64_Half,
    pub vd_ndx: Elf64_Half,
    pub vd_cnt: Elf64_Half,
    pub vd_hash: Elf64_Word,
    pub vd_aux: Elf64_Word,
    pub vd_next: Elf64_Word,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct Elf64_Verdaux {
    pub vda_name: Elf64_Word,
    pub vda_next: Elf64_Word,
}

// ============================================================================
// Compile-time layout assertions
// ============================================================================

const _: () = assert!(core::mem::size_of::<Elf32_Ehdr>() == 52);
const _: () = assert!(core::mem::size_of::<Elf64_Ehdr>() == 64);
const _: () = assert!(core::mem::size_of::<Elf32_Phdr>() == 32);
const _: () = assert!(core::mem::size_of::<Elf64_Phdr>() == 56);
const _: () = assert!(core::mem::size_of::<Elf32_Shdr>() == 40);
const _: () = assert!(core::mem::size_of::<Elf64_Shdr>() == 64);
const _: () = assert!(core::mem::size_of::<Elf32_Sym>() == 16);
const _: () = assert!(core::mem::size_of::<Elf64_Sym>() == 24);
const _: () = assert!(core::mem::size_of::<Elf32_Rel>() == 8);
const _: () = assert!(core::mem::size_of::<Elf64_Rel>() == 16);
const _: () = assert!(core::mem::size_of::<Elf32_Rela>() == 12);
const _: () = assert!(core::mem::size_of::<Elf64_Rela>() == 24);
const _: () = assert!(core::mem::size_of::<Elf32_Dyn>() == 8);
const _: () = assert!(core::mem::size_of::<Elf64_Dyn>() == 16);
const _: () = assert!(core::mem::size_of::<Elf32_Nhdr>() == 12);
const _: () = assert!(core::mem::size_of::<Elf64_Nhdr>() == 12);
const _: () = assert!(core::mem::size_of::<Elf32_Verdef>() == 20);
const _: () = assert!(core::mem::size_of::<Elf64_Verdef>() == 20);
const _: () = assert!(core::mem::size_of::<Elf32_Verdaux>() == 8);
const _: () = assert!(core::mem::size_of::<Elf64_Verdaux>() == 8);
