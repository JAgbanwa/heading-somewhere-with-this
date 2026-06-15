#!/usr/bin/env python3
"""Divisor-pair search for y^2 = (36n^3 - 19 - 12mn)^2 - (2m)^3."""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
from typing import Iterable

from known_solutions import KNOWN_SET


def factorize(n: int) -> dict[int, int]:
    n = abs(int(n))
    if n <= 1:
        return {}
    factors: dict[int, int] = {}
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            factors[d] = e
        d = 3 if d == 2 else d + 2
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def divisors_from_factors(factors: dict[int, int]) -> list[int]:
    divs = [1]
    for p in sorted(factors):
        a = factors[p]
        divs = [d * pow(p, k) for d in divs for k in range(a + 1)]
    return divs


def factorization_2m3(m: int) -> dict[int, int]:
    f = factorize(m)
    out = {p: 3 * a for p, a in f.items()}
    out[2] = out.get(2, 0) + 1
    return out


def verify_solution(n: int, m: int, y_abs: int) -> bool:
    if m == 0:
        return False
    a = 36 * n**3 - 19 - 12 * m * n
    return a * a - y_abs * y_abs == 8 * m**3


def cubic_integer_roots(m: int, a_val: int) -> list[int]:
    """Return integer roots n of 36n^3 - 12mn - (A+19) = 0."""
    if (a_val + 19) % 12 != 0:
        return []
    rhs = a_val + 19
    b = rhs // 12  # 3n^3 - m*n - B = 0

    roots: list[int] = []
    # Cardano on n^3 - (m/3)n - B/3 = 0 via high-precision float, then confirm.
    p = -m / 3.0
    q = -b / 3.0
    disc = (q / 2.0) ** 2 + (p / 3.0) ** 3
    candidates: set[int] = set()

    def add_candidate(val: float) -> None:
        if not math.isfinite(val):
            return
        for cand in (int(round(val)), int(math.floor(val)), int(math.ceil(val))):
            candidates.add(cand)

    if disc >= 0:
        s = math.sqrt(disc)
        u = (-q / 2.0 + s) ** (1.0 / 3.0) if (-q / 2.0 + s) >= 0 else -((-(-q / 2.0 + s)) ** (1.0 / 3.0))
        v = (-q / 2.0 - s) ** (1.0 / 3.0) if (-q / 2.0 - s) >= 0 else -((-(-q / 2.0 - s)) ** (1.0 / 3.0))
        add_candidate(u + v)
    else:
        r = math.sqrt(-(p / 3.0) ** 3)
        theta = math.acos((-q / 2.0) / r)
        for k in range(3):
            t = 2.0 * math.sqrt(-p / 3.0) * math.cos((theta + 2 * math.pi * k) / 3.0)
            add_candidate(t)

    # Small rational-root scan when B is modest.
    if abs(b) <= 10**7:
        lim = int(round((abs(b) * 6) ** (1.0 / 3.0))) + 4
        for n in range(-lim, lim + 1):
            candidates.add(n)

    for n in candidates:
        if 36 * n**3 - 12 * m * n == rhs:
            roots.append(n)
    return sorted(set(roots))


def process_divisor_pair(m: int, d: int, e: int) -> list[tuple[int, int, int]]:
    a_val = d + e
    if a_val % 12 != 5:
        return []
    y_abs = abs(e - d)
    hits: list[tuple[int, int, int]] = []
    for n in cubic_integer_roots(m, a_val):
        if verify_solution(n, m, y_abs):
            hits.append((n, m, y_abs))
    return hits


def search_m(m: int) -> list[tuple[int, int, int]]:
    if m == 0:
        return []
    val = 2 * m**3
    factors = factorization_2m3(m)
    pos_divs = divisors_from_factors(factors)
    hits: list[tuple[int, int, int]] = []
    seen: set[tuple[int, int, int]] = set()
    for d_pos in pos_divs:
        for d in (d_pos, -d_pos):
            if d == 0:
                continue
            if val % d != 0:
                continue
            e = val // d
            for pair in ((d, e), (e, d)):
                for hit in process_divisor_pair(m, pair[0], pair[1]):
                    if hit not in seen:
                        seen.add(hit)
                        hits.append(hit)
    return hits


def search_range(m_start: int, m_end: int, *, positive_only: bool = False) -> list[tuple[int, int, int]]:
    hits: list[tuple[int, int, int]] = []
    seen: set[tuple[int, int, int]] = set()
    for m in range(m_start, m_end + 1):
        if positive_only and m <= 0:
            continue
        for hit in search_m(m):
            if hit not in seen and hit not in KNOWN_SET:
                seen.add(hit)
                hits.append(hit)
        for hit in search_m(-m):
            if hit not in seen and hit not in KNOWN_SET:
                seen.add(hit)
                hits.append(hit)
    return hits


def q_progression(d: int) -> int:
    """Smallest q such that d | 2m^3 iff m in qZ (for d fixed)."""
    f = factorize(d)
    q = 1
    for p, a in f.items():
        need = (a + (1 if p == 2 else 0) + 2) // 3
        q *= pow(p, need)
    return q


def small_cofactor_search(
    m_abs_max: int,
    d_max: int = 64,
    *,
    d_values: Iterable[int] | None = None,
) -> list[tuple[int, int, int]]:
    """Enumerate solutions whose divisor pair has a factor of abs value <= d_max."""
    hits: list[tuple[int, int, int]] = []
    seen: set[tuple[int, int, int]] = set()
    ds = list(d_values) if d_values is not None else list(range(1, d_max + 1))

    for d in ds:
        if d == 0:
            continue
        q = q_progression(d)
        # e = 2m^3/d, m = k*q => e = 2*q^3*k^3/d, need integer k and |m|<=max
        k_max = int((m_abs_max / q) ** (1.0 / 3.0)) + 2
        for k in range(1, k_max + 1):
            for sign in (1, -1):
                m = sign * q * k
                if abs(m) > m_abs_max or m == 0:
                    continue
                m3x2 = 2 * m**3
                if m3x2 % d != 0:
                    continue
                e = m3x2 // d
                for pair in ((d, e), (-d, e), (d, -e), (-d, -e)):
                    dd, ee = pair
                    if dd == 0 or ee == 0:
                        continue
                    if dd * ee != m3x2:
                        continue
                    for hit in process_divisor_pair(m, dd, ee):
                        if hit not in seen and hit not in KNOWN_SET:
                            seen.add(hit)
                            hits.append(hit)
    return hits


def torsion_translate(n: int, m: int, y_abs: int) -> tuple[int, int, int] | None:
    """Apply order-3 torsion translate; return (n, m', |y'|) if integral."""
    c = 36 * n**3 - 19
    # Try both signs for y in the map.
    for eps in (y_abs, -y_abs):
        denom = 2 * m
        if denom == 0:
            continue
        num = ((eps - c) // 2) ** 2 - 36 * n**2 + 2 * m
        if ((eps - c) % 2) != 0:
            continue
        if num % denom != 0:
            continue
        mp = -num // denom
        if mp == 0:
            continue
        a_new = 36 * n**3 - 19 - 12 * n * mp
        disc = a_new * a_new - 8 * mp**3
        if disc < 0:
            continue
        root = math.isqrt(disc)
        if root * root != disc:
            continue
        y_new = root
        if verify_solution(n, mp, y_new):
            return (n, mp, y_new)
    return None


def torsion_closure() -> list[tuple[int, int, int]]:
    from known_solutions import KNOWN_SOLUTIONS

    hits: list[tuple[int, int, int]] = []
    seen = set(KNOWN_SET)
    for n, m, y_abs in KNOWN_SOLUTIONS:
        for _ in range(3):
            out = torsion_translate(n, m, y_abs)
            if out is None:
                break
            if out not in seen:
                hits.append(out)
                seen.add(out)
                n, m, y_abs = out
            else:
                n, m, y_abs = out
    return [h for h in hits if h not in KNOWN_SET]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["range", "small-cofactor", "torsion"], required=True)
    parser.add_argument("--m-start", type=int, default=1)
    parser.add_argument("--m-end", type=int, default=1000)
    parser.add_argument("--m-abs-max", type=int, default=10**10)
    parser.add_argument("--d-max", type=int, default=64)
    parser.add_argument("--out", type=str, default="")
    args = parser.parse_args()

    if args.mode == "range":
        hits = search_range(args.m_start, args.m_end)
    elif args.mode == "small-cofactor":
        hits = small_cofactor_search(args.m_abs_max, args.d_max)
    else:
        hits = torsion_closure()

    payload = [{"n": n, "m": m, "abs_y": y} for n, m, y in hits]
    text = json.dumps(payload, indent=2)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(text + "\n")
    else:
        print(text)
    print(f"# new_hits={len(hits)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
