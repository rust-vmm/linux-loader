# Testing `linux-loader`

## Tests

Our Continuous Integration (CI) pipeline is implemented on top of
[Buildkite](https://buildkite.com/).
For the complete list of tests, check our
[CI pipeline](https://buildkite.com/rust-vmm/rust-vmm-ci).

Each individual test runs in a container. To reproduce a test locally, you can
use the dev-container on both x86 and arm64. Please note some features are not
enabled (and thus not tested) by default. To run tests with all features
enabled, use `cargo test --all-features`.

```bash
container_version=5
docker run -it \
           --security-opt seccomp=unconfined \
           --volume $(pwd):/linux-loader \
           rustvmm/dev:v${container_version}
cd linux-loader/
cargo test --all-features
```

### bzImage test

As we don't want to distribute an entire kernel bzImage, the `load_bzImage`
test is ignored by default. In order to test the bzImage support, one needs to
locally build a bzImage and copy it to the current working directory for
`cargo test --features bzimage`:

```bash
# Assuming your linux-loader and linux-stable are both under ${LINUX_LOADER}:
git clone git://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git ${LINUX_LOADER}/linux-stable
cd linux-stable
make bzImage
cp linux-stable/arch/x86/boot/bzImage ${LINUX_LOADER}/linux-loader
cd ${LINUX_LOADER}/linux-loader
container_version=5
docker run -it \
           --security-opt seccomp=unconfined \
           --volume $(pwd):/linux-loader \
           rustvmm/dev:v${container_version}
cd linux-loader/
cargo test --features bzimage
```
