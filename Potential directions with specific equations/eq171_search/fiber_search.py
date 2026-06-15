#!/usr/bin/env python3
"""Search integral points on fiber E_n via multiples of known points."""

from __future__ import annotations

import argparse
import json
import math

from known_solutions import KNOWN_SET, KNOWN_SOLUTIONS
from divisor_sweep import verify_solution


def fiber_points(n: int) -> list[tuple[int, int]]:
    return [(m, y) for nn, m, y in KNOWN_SOLUTIONS if nn == n]


class FiberCurve:
    def __init__(self, n: int) -> None:
        self.n = n
        c = 36 * n**3 - 19
        self.a2 = 36 * n**2
        self.a1 = 12 * n * c
        self.a0 = c * c

    def rhs(self, x: int) -> int:
        return x**3 + self.a2 * x**2 + self.a1 * x + self.a0

    def is_point(self, x: int, y: int) -> bool:
        return y * y == self.rhs(x)

    def negate(self, p: tuple[int, int]) -> tuple[int, int]:
        x, y = p
        return (x, -y)

    def add(self, p: tuple[int, int], q: tuple[int, int]) -> tuple[int, int] | None:
        if p is None:  # type: ignore[comparison-overlap]
            return q
        if q is None:  # type: ignore[comparison-overlap]
            return p
        x1, y1 = p
        x2, y2 = q
        if x1 == x2:
            if (y1 + y2) % 2 == 0 and y1 + y2 != 0:
                return self.negate(p)
            if y1 == y2:
                num = 3 * x1 * x1 + 2 * self.a2 * x1 + self.a1
                den = 2 * y1
                if num % den != 0:
                    return None
                lam = num // den
            else:
                return None
        else:
            num = y2 - y1
            den = x2 - x1
            if num % den != 0:
                return None
            lam = num // den
        x3 = lam * lam - self.a2 - x1 - x2
        y3 = lam * (x1 - x3) - y1
        return (x3, y3)

    def mul(self, p: tuple[int, int], k: int) -> tuple[int, int] | None:
        if k == 0 or p is None:
            return None
        if k < 0:
            out = self.mul(self.negate(p), -k)
            return None if out is None else self.negate(out)
        r: tuple[int, int] | None = None
        q = p
        while k:
            if k & 1:
                r = self.add(r, q) if r is not None else q
            q = self.add(q, q)
            if q is None:
                return None
            k >>= 1
        return r


def point_to_solution(n: int, x: int, y: int) -> tuple[int, int, int] | None:
    if x % 2 != 0:
        return None
    m = -x // 2
    if m == 0:
        return None
    y_abs = abs(y)
    if verify_solution(n, m, y_abs):
        return (n, m, y_abs)
    return None


def search_fiber(n: int, max_multiple: int = 5000, x_abs_max: int = 0) -> list[tuple[int, int, int]]:
    curve = FiberCurve(n)
    hits: dict[tuple[int, int, int], None] = {}
    base_points: list[tuple[int, int]] = []
    for m, y_abs in fiber_points(n):
        x = -2 * m
        for y in (y_abs, -y_abs):
            if curve.is_point(x, y):
                base_points.append((x, y))

    # Include torsion section T=(0,c) when integral.
    c = 36 * n**3 - 19
    if curve.is_point(0, c):
        base_points.append((0, c))
    if curve.is_point(0, -c):
        base_points.append((0, -c))

    seen_pts: set[tuple[int, int]] = set()
    for p in base_points:
        for k in range(1, max_multiple + 1):
            q = curve.mul(p, k)
            if q is None:
                break
            if q in seen_pts:
                continue
            seen_pts.add(q)
            sol = point_to_solution(n, q[0], q[1])
            if sol and sol not in KNOWN_SET:
                hits[sol] = None

    # Small Z-linear combinations of distinct base points.
    uniq = []
    for p in base_points:
        if p not in uniq:
            uniq.append(p)
    for i, p in enumerate(uniq):
        for j, q in enumerate(uniq):
            for a in range(-8, 9):
                for b in range(-8, 9):
                    if a == 0 and b == 0:
                        continue
                    if j < i and a < 0:
                        continue
                    pt: tuple[int, int] | None = None
                    pa = curve.mul(p, abs(a)) if a else None
                    qb = curve.mul(q, abs(b)) if b else None
                    if a < 0 and pa is not None:
                        pa = curve.negate(pa)
                    if b < 0 and qb is not None:
                        qb = curve.negate(qb)
                    if pa is not None:
                        pt = pa
                    if qb is not None:
                        pt = qb if pt is None else curve.add(pt, qb)
                    if pt is None or pt in seen_pts:
                        continue
                    seen_pts.add(pt)
                    sol = point_to_solution(n, pt[0], pt[1])
                    if sol and sol not in KNOWN_SET:
                        hits[sol] = None

    if x_abs_max > 0:
        for x in range(-x_abs_max, x_abs_max + 1, 2):
            rhs = curve.rhs(x)
            if rhs < 0:
                continue
            y = math.isqrt(rhs)
            if y * y != rhs:
                continue
            for yy in ({y, -y} if y else {0}):
                sol = point_to_solution(n, x, yy)
                if sol and sol not in KNOWN_SET:
                    hits[sol] = None

    return list(hits.keys())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-values", type=str, default="")
    parser.add_argument("--max-multiple", type=int, default=5000)
    parser.add_argument("--x-abs-max", type=int, default=0)
    parser.add_argument("--out", type=str, default="")
    args = parser.parse_args()

    rank2 = [-29, -4, 46, -54, -57, 75, 93, -4741, -6561, 16531, 17309, 27949]
    n_values = rank2 if not args.n_values else [int(x) for x in args.n_values.split(",")]

    all_hits: list[dict] = []
    for n in n_values:
        hits = search_fiber(n, args.max_multiple, args.x_abs_max)
        print(f"n={n} new_hits={len(hits)}")
        for hit in hits:
            all_hits.append({"n": hit[0], "m": hit[1], "abs_y": hit[2]})
            print(hit)

    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            json.dump(all_hits, fh, indent=2)
            fh.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
