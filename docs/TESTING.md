# Testing `linux-loader`

## Tests

Our Continuous Integration (CI) pipeline is implemented on top of
[Buildkite](https://buildkite.com/).
For the complete list of tests, check our
[CI pipeline](https://buildkite.com/rust-vmm/rust-vmm-ci).

Each individual test runs in a container. To reproduce a test locally, you can
use the dev-container on both x86 and arm64.

```bash
container_version=11
docker run -it \
           --security-opt seccomp=unconfined \
           --volume $(pwd):/linux-loader \
           rustvmm/dev:v${container_version}
cd linux-loader/
cargo test
```

