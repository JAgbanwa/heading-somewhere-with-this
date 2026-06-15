#!/usr/bin/env python3
"""Parallel m-range sweep driver."""

from __future__ import annotations

import argparse
import json
import multiprocessing as mp
import os
import time

from divisor_sweep import KNOWN_SET, search_m


def _worker(args: tuple[int, int, int, str]) -> tuple[int, int, list[dict]]:
    m_start, m_end, worker_id, out_dir = args
    hits: list[dict] = []
    t0 = time.time()
    for m in range(m_start, m_end + 1):
        for mm in (m, -m):
            for n, m_val, y_abs in search_m(mm):
                triple = (n, m_val, y_abs)
                if triple not in KNOWN_SET:
                    hits.append({"n": n, "m": m_val, "abs_y": y_abs})
        if m % 100000 == 0:
            elapsed = time.time() - t0
            print(
                f"[worker {worker_id}] m={m}/{m_end} hits={len(hits)} elapsed={elapsed:.1f}s",
                flush=True,
            )
    out_path = os.path.join(out_dir, f"hits_{worker_id}_{m_start}_{m_end}.json")
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(hits, fh, indent=2)
        fh.write("\n")
    return worker_id, len(hits), hits


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m-start", type=int, required=True)
    parser.add_argument("--m-end", type=int, required=True)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--out-dir", type=str, default="/tmp/eq171_sweep")
    args = parser.parse_args()

    os.makedirs(args.out_dir, exist_ok=True)
    total = args.m_end - args.m_start + 1
    chunk = (total + args.workers - 1) // args.workers
    tasks = []
    for i in range(args.workers):
        start = args.m_start + i * chunk
        end = min(args.m_start + (i + 1) * chunk - 1, args.m_end)
        if start > args.m_end:
            break
        tasks.append((start, end, i, args.out_dir))

    print(f"Launching {len(tasks)} workers for m in [{args.m_start}, {args.m_end}]")
    with mp.Pool(len(tasks)) as pool:
        results = pool.map(_worker, tasks)

    all_hits: list[dict] = []
    for _, _, hits in results:
        all_hits.extend(hits)

    merged_path = os.path.join(args.out_dir, "merged_hits.json")
    with open(merged_path, "w", encoding="utf-8") as fh:
        json.dump(all_hits, fh, indent=2)
        fh.write("\n")
    print(f"Done. new_hits={len(all_hits)} written to {merged_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
