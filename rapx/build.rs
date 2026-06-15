use std::process::Command;

fn main() {
    println!("cargo::rustc-check-cfg=cfg(rustc_spanned_at_root)");

    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let output = Command::new(&rustc)
        .arg("--version")
        .output()
        .unwrap_or_else(|_| {
            panic!("failed to run `{} --version`", rustc);
        });
    let version = String::from_utf8_lossy(&output.stdout);

    let parts: Vec<&str> = version
        .split(|c: char| !c.is_ascii_digit())
        .filter(|s| !s.is_empty())
        .collect();

    let minor: u32 = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);

    if minor >= 97 {
        println!("cargo:rustc-cfg=rustc_spanned_at_root");
    }
}
