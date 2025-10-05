#!/usr/bin/env python3
# experiments/scripts/seed_duplicate_blocks.py
import argparse, os, random, subprocess, json, sys

def get_block_size(img_path):
    # try dumpe2fs (comes with e2fsprogs)
    try:
        out = subprocess.check_output(['dumpe2fs', '-h', img_path], stderr=subprocess.DEVNULL, text=True)
        for line in out.splitlines():
            if 'Block size:' in line:
                return int(line.split(':',1)[1].strip())
    except Exception:
        pass
    # fallback
    return 4096

def duplicate_blocks(img_in, img_out, pairs, block_size=None):
    # copy the original image to output path first
    if img_in != img_out:
        import shutil
        shutil.copy2(img_in, img_out)
    if block_size is None:
        block_size = get_block_size(img_out)
    img_size = os.path.getsize(img_out)
    nblocks = img_size // block_size
    # validate pairs
    with open(img_out, 'r+b') as f:
        for src, dst in pairs:
            if src < 0 or dst < 0 or src >= nblocks or dst >= nblocks:
                raise ValueError(f'block index out of range: {src}->{dst}, nblocks={nblocks}')
            # read source block
            f.seek(src * block_size)
            data = f.read(block_size)
            # write into dst block
            f.seek(dst * block_size)
            f.write(data)
    return {'image': img_out, 'block_size': block_size, 'nblocks': nblocks, 'pairs': pairs}

def make_random_pairs(img_path, num_pairs, seed=None, block_size=None):
    if seed is not None:
        random.seed(seed)
    if block_size is None:
        block_size = get_block_size(img_path)
    nblocks = os.path.getsize(img_path) // block_size
    pairs = []
    for _ in range(num_pairs):
        src = random.randrange(0, nblocks)
        dst = random.randrange(0, nblocks)
        # avoid trivial src==dst
        while dst == src:
            dst = random.randrange(0, nblocks)
        pairs.append((src, dst))
    return pairs

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--input', required=True)
    p.add_argument('--output', required=True)
    p.add_argument('--pairs', type=int, default=1, help='number of random duplicate-block pairs to create')
    p.add_argument('--seed', type=int, default=None)
    p.add_argument('--block-size', type=int, default=None)
    p.add_argument('--pairs-json', default=None, help='if given, write the pairs JSON to this path')
    args = p.parse_args()
    pairs = make_random_pairs(args.input, args.pairs, seed=args.seed, block_size=args.block_size)
    result = duplicate_blocks(args.input, args.output, pairs, block_size=args.block_size)
    if args.pairs_json:
        with open(args.pairs_json, 'w') as f:
            json.dump(result, f, indent=2)
    print('WROTE', args.output)
    print('Pairs:', pairs)

if __name__ == '__main__':
    main()
