// src/main.rs
use anyhow::{Context, Result};
use serde_json::from_reader;
use std::fs::File;
use vrl_validator::{FSStateSnap, RepairAction, validate_action, check_block_range, check_bitmap_soundness, check_unique_ownership};

fn print_checks(s: &FSStateSnap) {
    println!("block_range: {}", check_block_range(s));
    println!("bitmap_soundness: {}", check_bitmap_soundness(s));
    println!("unique_ownership: {}", check_unique_ownership(s));
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: vrl_validator <snapshot.json>");
        std::process::exit(2);
    }
    let f = File::open(&args[1]).with_context(|| format!("open {}", &args[1]))?;
    let s: FSStateSnap = from_reader(f).context("parse snapshot")?;

    println!("Before:");
    print_checks(&s);

    if !(check_block_range(&s) && check_bitmap_soundness(&s) && check_unique_ownership(&s)) {
        println!("Discrepancy detected -> proposing FixBitmap");
        let ok = validate_action(&s, &RepairAction::FixBitmap)?;
        println!("After applying FixBitmap, invariants hold? {}", ok);
    } else {
        println!("No discrepancy detected.");
    }
    Ok(())
}
