# Linux-loader

## Short-description

* Parsing and loading vmlinux (raw ELF image) and bzImage images
* Linux command line parsing and generation
* Definitions and helpers for the Linux boot protocol

## How to build

```
cd linux-loader
cargo build
```

## How to run test

```
cd linux-loader
cargo test
cargo test -- --nocapture
```

## Platform Support
- Arch: x86
- OS: Linux/Unix

