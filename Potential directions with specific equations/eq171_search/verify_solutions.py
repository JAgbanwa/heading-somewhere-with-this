#!/usr/bin/env python3
"""Exact verification of eq 1.71 solution triples."""

from __future__ import annotations

import argparse
import json
import sys

from known_solutions import KNOWN_SOLUTIONS
from divisor_sweep import verify_solution


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--file", type=str, default="")
    args = parser.parse_args()

    triples = KNOWN_SOLUTIONS
    if args.file:
        with open(args.file, encoding="utf-8") as fh:
            data = json.load(fh)
        triples = [(row["n"], row["m"], row["abs_y"]) for row in data]

    bad = []
    for n, m, y_abs in triples:
        if not verify_solution(n, m, y_abs):
            bad.append((n, m, y_abs))

    if bad:
        print("FAILED:", bad, file=sys.stderr)
        return 1

    print(f"verified {len(triples)} triples")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
