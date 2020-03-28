# Linux-loader

## Short-description

* Parsing and loading vmlinux (raw ELF image), bzImage and PE images
* Linux command line parsing and generation
* Loading device tree blobs
* Definitions and helpers for the Linux boot protocol

## How to build

```
cd linux-loader
cargo build
```

## Tests

Our Continuous Integration (CI) pipeline is implemented on top of
[Buildkite](https://buildkite.com/).
For the complete list of tests, check our
[CI pipeline](https://buildkite.com/rust-vmm/rust-vmm-ci).

Each individual test runs in a container. To reproduce a test locally, you can
use the dev-container on both x86 and arm64.

```bash
container_version=5
docker run -it \
           --security-opt seccomp=unconfined \
           --volume $(pwd):/linux-loader \
           rustvmm/dev:v${container_version}
cd linux-loader/
cargo test
```

### bzImage test

As we don't want to distribute an entire kernel bzImage, the `load_bzImage`
test is ignored by default. In order to test the bzImage support, one needs to
locally build a bzImage, copy it to the `src/loader` directory and run
`cargo test`:

```bash
# Assuming your linux-loader and linux-stable are both under ${LINUX_LOADER}:
git clone git://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git ${LINUX_LOADER}/linux-stable
cd linux-stable
make bzImage
cp linux-stable/arch/x86/boot/bzImage ${LINUX_LOADER}/linux-loader/src/loader/
cd ${LINUX_LOADER}/linux-loader
container_version=5
docker run -it \
           --security-opt seccomp=unconfined \
           --volume $(pwd):/linux-loader \
           rustvmm/dev:v${container_version}
cd linux-loader/
cargo test
```
