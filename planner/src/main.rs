/* Full planner/src/main.rs — Diagnose-enabled */
use anyhow::Result;
use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "vrl", author, version, about = "Verified Repair Layer CLI (planner + diagnostic)")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Dump filesystem snapshot to JSON (stub - writes a sample snapshot)
    Inspect {
        /// Input image file (unused in stub)
        #[arg(short, long)]
        image: PathBuf,
        /// Output snapshot JSON path
        #[arg(short, long)]
        out: PathBuf,
    },

    /// Compute a repair plan from diagnostics (stub)
    Plan {
        /// Input diagnostic JSON
        #[arg(short, long)]
        diagnostic: PathBuf,
        /// Output plan JSON
        #[arg(short, long)]
        out: PathBuf,
    },

    /// Apply a plan to an image (stub)
    Apply {
        /// Image to apply to
        #[arg(short, long)]
        image: PathBuf,
        /// Plan JSON file
        #[arg(short, long)]
        plan: PathBuf,
        /// Undo log path
        #[arg(long)]
        undo: Option<PathBuf>,
    },

    /// Diagnose a snapshot.json and write diagnostic.json (real implementation)
    Diagnose {
        /// Input snapshot JSON (from inspect)
        #[arg(short, long)]
        snapshot: PathBuf,
        /// Output diagnostic JSON path
        #[arg(short, long)]
        out: PathBuf,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match &cli.command {
        Commands::Inspect { image, out } => {
            println!("INSPECT stub. image={:?} out={:?}", image, out);
            create_sample_snapshot(out)?;
            println!("Sample snapshot created at {:?}", out);
        }
        Commands::Plan { diagnostic, out } => {
            println!("PLAN stub. diagnostic={:?} out={:?}", diagnostic, out);
            // TODO: planner logic here
        }
        Commands::Apply { image, plan, undo } => {
            println!("APPLY stub. image={:?} plan={:?} undo={:?}", image, plan, undo);
            // TODO: applier logic here
        }
        Commands::Diagnose { snapshot, out } => {
            println!("DIAGNOSE running: snapshot={:?} -> out={:?}", snapshot, out);
            run_diagnose(snapshot, out)?;
            println!("Diagnostic written to {:?}", out);
        }
    }

    Ok(())
}

/* ---------------------
   Snapshot & Diagnostic types
   --------------------- */

#[derive(Serialize, Deserialize, Debug)]
struct Snapshot {
    superblock: Superblock,
    block_groups: Vec<BlockGroup>,
    inodes: Vec<Inode>,
}

#[derive(Serialize, Deserialize, Debug)]
struct Superblock {
    block_size: u64,
    blocks_count: u64,
    inodes_count: u64,
    blocks_per_group: u64,
    inodes_per_group: u64,
}

#[derive(Serialize, Deserialize, Debug)]
struct BlockGroup {
    group_index: u64,
    block_start: u64,
    // bitmap as an array of bools; true = allocated
    block_bitmap: Vec<bool>,
}

#[derive(Serialize, Deserialize, Debug)]
struct Inode {
    inode: u64,
    link_count: u64,
    // list of global block numbers referenced by this inode
    blocks: Vec<u64>,
}

#[derive(Serialize, Deserialize, Debug)]
struct Diagnostic {
    referenced_but_free: Vec<u64>,
    allocated_but_unreferenced: Vec<u64>,
    duplicate_block_owners: Vec<DuplicateOwner>,
    referenced_count: usize,
    allocated_count: usize,
}

#[derive(Serialize, Deserialize, Debug)]
struct DuplicateOwner {
    block: u64,
    owners: Vec<u64>, // inode numbers that reference this block
}

/* ---------------------
   Helpers
   --------------------- */

fn create_sample_snapshot(out: &std::path::Path) -> Result<()> {
    // Small sample snapshot; later real dumper will produce a similar structure
    let snap = Snapshot {
        superblock: Superblock {
            block_size: 4096,
            blocks_count: 1024,
            inodes_count: 128,
            blocks_per_group: 1024,
            inodes_per_group: 128,
        },
        block_groups: vec![
            BlockGroup {
                group_index: 0,
                block_start: 0,
                block_bitmap: vec![false, true, true, false, false, true, false, false],
            },
            // second group sample
            BlockGroup {
                group_index: 1,
                block_start: 8,
                block_bitmap: vec![false, false, true, false, false],
            },
        ],
        inodes: vec![
            Inode { inode: 2, link_count: 1, blocks: vec![1, 2] }, // uses blocks 1 and 2
            Inode { inode: 3, link_count: 1, blocks: vec![6] },    // uses block 6
            Inode { inode: 4, link_count: 1, blocks: vec![10] },   // uses block 10 (group 1, index 2)
            // create a duplicate reference to block 2 to test duplicate detection
            Inode { inode: 5, link_count: 1, blocks: vec![2] },
        ],
    };

    let f = File::create(out)?;
    serde_json::to_writer_pretty(f, &snap)?;
    Ok(())
}

fn run_diagnose(snapshot_path: &std::path::Path, out_path: &std::path::Path) -> Result<()> {
    // 1) Read snapshot.json
    let f = File::open(snapshot_path)?;
    let snap: Snapshot = serde_json::from_reader(f)?;

    // 2) Compute referenced blocks & duplicate owners
    let mut block_to_owners: HashMap<u64, Vec<u64>> = HashMap::new();
    for inode in &snap.inodes {
        for &blk in &inode.blocks {
            block_to_owners.entry(blk).or_default().push(inode.inode);
        }
    }
    let referenced_set: HashSet<u64> = block_to_owners.keys().cloned().collect();

    // 3) Compute allocated blocks from block groups
    let mut allocated_set: HashSet<u64> = HashSet::new();
    for bg in &snap.block_groups {
        for (i, bit) in bg.block_bitmap.iter().enumerate() {
            if *bit {
                let block_num = bg.block_start + (i as u64);
                allocated_set.insert(block_num);
            }
        }
    }

    // 4) Differences
    let referenced_but_free: Vec<u64> = referenced_set
        .difference(&allocated_set)
        .cloned()
        .collect();

    let allocated_but_unreferenced: Vec<u64> = allocated_set
        .difference(&referenced_set)
        .cloned()
        .collect();

    // 5) Duplicate owners
    let mut duplicates = Vec::new();
    for (&blk, owners) in &block_to_owners {
        if owners.len() > 1 {
            duplicates.push(DuplicateOwner {
                block: blk,
                owners: owners.clone(),
            });
        }
    }

    // 6) Diagnostic struct + write
    let diag = Diagnostic {
        referenced_but_free: {
            let mut v = referenced_but_free;
            v.sort_unstable();
            v
        },
        allocated_but_unreferenced: {
            let mut v = allocated_but_unreferenced;
            v.sort_unstable();
            v
        },
        duplicate_block_owners: duplicates,
        referenced_count: referenced_set.len(),
        allocated_count: allocated_set.len(),
    };

    let outf = File::create(out_path)?;
    serde_json::to_writer_pretty(outf, &diag)?;
    Ok(())
}
