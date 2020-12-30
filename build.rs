use std::process::Command;

fn main() {
    let command = "./.buildkite/download_resources.sh";
    let status = Command::new(command).status().unwrap();
    if !status.success() {
        panic!("Cannot run build script");
    }

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=.buildkite/download_resources.sh");
    println!("cargo:rerun-if-changed=src/loader/x86_64/bzimage/bzimage");
}
