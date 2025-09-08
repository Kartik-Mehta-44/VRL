use anyhow::Result;
use clap::{Parser, Subcommand};
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    name = "vrl",
    author,
    version,
    about = "Verified Repair Layer CLI (planner stub)"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Dump filesystem snapshot to JSON (stub)
    Inspect {
        /// Input image file
        #[arg(short, long)]
        image: PathBuf,
        /// Output snapshot JSON path
        #[arg(short, long)]
        out: PathBuf,
    },

    /// Create plan from diagnostic (stub)
    Plan {
        /// Input diagnostic JSON
        #[arg(short, long)]
        diagnostic: PathBuf,
        /// Output plan JSON
        #[arg(short, long)]
        out: PathBuf,
    },

    /// Apply plan to image (stub)
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
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match &cli.command {
        Commands::Inspect { image, out } => {
            println!("INSPECT stub. image={:?} out={:?}", image, out);
            // TODO: call real dumper; for now, write a tiny skeleton JSON file to show flow
            create_sample_snapshot(out)?;
        }
        Commands::Plan { diagnostic, out } => {
            println!("PLAN stub. diagnostic={:?} out={:?}", diagnostic, out);
            // TODO: planner logic here
        }
        Commands::Apply { image, plan, undo } => {
            println!(
                "APPLY stub. image={:?} plan={:?} undo={:?}",
                image, plan, undo
            );
            // TODO: applier logic here
        }
    }

    Ok(())
}

// small helper to write a minimal snapshot so downstream tools can be tested
fn create_sample_snapshot(out: &std::path::Path) -> Result<()> {
    use serde::Serialize;
    use std::fs::File;
    #[derive(Serialize)]
    struct Snapshot {
        superblock: Superblock,
        block_groups: Vec<BlockGroup>,
        inodes: Vec<Inode>,
    }
    #[derive(Serialize)]
    struct Superblock {
        block_size: u64,
        blocks_count: u64,
        inodes_count: u64,
    }
    #[derive(Serialize)]
    struct BlockGroup {
        group_index: u64,
        block_bitmap: Vec<bool>, // simple
    }
    #[derive(Serialize)]
    struct Inode {
        inode: u64,
        link_count: u64,
        blocks: Vec<u64>,
    }

    let snap = Snapshot {
        superblock: Superblock {
            block_size: 4096,
            blocks_count: 1024,
            inodes_count: 128,
        },
        block_groups: vec![BlockGroup {
            group_index: 0,
            block_bitmap: vec![false, true, true, false, false],
        }],
        inodes: vec![
            Inode {
                inode: 2,
                link_count: 1,
                blocks: vec![1, 2],
            },
            Inode {
                inode: 3,
                link_count: 1,
                blocks: vec![4],
            },
        ],
    };

    let f = File::create(out)?;
    serde_json::to_writer_pretty(f, &snap)?;
    println!("Wrote sample snapshot to {:?}", out);
    Ok(())
}
