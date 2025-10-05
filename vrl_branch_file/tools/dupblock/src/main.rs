use clap::Parser;
use std::fs::OpenOptions;
use std::io::{Read, Seek, SeekFrom, Write};
use serde::Serialize;

#[derive(Parser)]
struct Opts {
    #[arg(long)]
    input: String,
    #[arg(long)]
    output: String,
    #[arg(long, default_value_t = 1)]
    pairs: usize,
    #[arg(long, default_value_t = 4096)]
    block_size: usize,
    #[arg(long)]
    seed: Option<u64>,
}

#[derive(Serialize)]
struct Pair {
    src: usize,
    dst: usize,
}

fn main() -> std::io::Result<()> {
    let opts = Opts::parse();
    if opts.input != opts.output {
        std::fs::copy(&opts.input, &opts.output)?;
    }
    let mut file = OpenOptions::new().read(true).write(true).open(&opts.output)?;
    let sz = file.metadata()?.len() as usize;
    let nblocks = sz / opts.block_size;
    let mut rng = match opts.seed {
        Some(s) => rand::rngs::StdRng::seed_from_u64(s),
        None => rand::rngs::StdRng::from_entropy(),
    };
    use rand::Rng;
    let mut pairs = Vec::new();
    for _ in 0..opts.pairs {
        let src = rng.gen_range(0..nblocks);
        let mut dst = rng.gen_range(0..nblocks);
        while dst == src {
            dst = rng.gen_range(0..nblocks);
        }
        pairs.push(Pair { src, dst });
    }
    for p in &pairs {
        let mut buf = vec![0u8; opts.block_size];
        file.seek(SeekFrom::Start((p.src * opts.block_size) as u64))?;
        file.read_exact(&mut buf)?;
        file.seek(SeekFrom::Start((p.dst * opts.block_size) as u64))?;
        file.write_all(&buf)?;
    }
    println!("{}", serde_json::to_string_pretty(&pairs).unwrap());
    Ok(())
}
