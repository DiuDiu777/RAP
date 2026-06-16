use std::process::Command;

fn main() {
    let (_major, minor, _patch) = detect_rustc_version();

    // Register all cfg flags with Cargo for expected warnings suppression.
    emit_check_cfg("rustc_spanned_at_root");

    // ─── Version-gated compatibility flags ───────────────────────────────
    //
    // Add new entries here when compiler APIs change.  Each entry records
    // the minimum rustc minor version that requires the new code path.
    //
    // Flag name                     | since | Description
    // ------------------------------|-------|-------------------------------
    // rustc_spanned_at_root         | 1.97  | Spanned moved from
    //                               |       | source_map to rustc_span root
    emit_cfg("rustc_spanned_at_root", minor >= 97);
}

fn emit_check_cfg(name: &str) {
    println!("cargo::rustc-check-cfg=cfg({name})");
}

fn emit_cfg(name: &str, condition: bool) {
    if condition {
        println!("cargo::rustc-cfg={name}");
    }
}

fn detect_rustc_version() -> (u32, u32, u32) {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let output = Command::new(&rustc)
        .arg("--version")
        .output()
        .unwrap_or_else(|_| panic!("failed to run `{} --version`", rustc));

    let version = String::from_utf8_lossy(&output.stdout);
    let parts: Vec<&str> = version
        .split(|c: char| !c.is_ascii_digit())
        .filter(|s| !s.is_empty())
        .collect();

    let major = parts.first().and_then(|s| s.parse().ok()).unwrap_or(0);
    let minor = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
    let patch = parts.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
    (major, minor, patch)
}
