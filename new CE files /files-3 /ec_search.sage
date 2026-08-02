# ec_search.sage — COMPLETE solution of  y^2 = (6n+x)^2 + (36 n^3 - 19)/x  per fixed x or u.
#
# For fixed x:  x*y^2 = 36n^3 + 36x n^2 + 12x^2 n + x^3 - 19.
#   With U = 36x*n, V = 36x^2*y this is the elliptic curve
#     E_x:  V^2 = U^3 + 36x^2 U^2 + 432x^4 U + 1296x^6 - 24624x^3
#   Siegel => finitely many integral points => for each x this finds ALL integer n
#   (of ANY size, including 10^20..10^40) with x | 36n^3-19 and y integral.
#   This is strictly stronger than any brute-force n-scan for that x.
#
# For fixed u = y - x - 6n:  u*s^2 = 288n^3 + 144u n^2 + 24u^2 n + u^3 - 152,
#   s = 4x + u + 12n.  With U = 288u*n, V = 288u^2*s:
#     F_u:  V^2 = U^3 + 144u^2 U^2 + 6912u^4 U + 82944u^6 - 12607488u^3
#   Recover x = (s - u - 12n)/4 (must be a positive integer).
#
# Caveats: integral_points() needs provable Mordell-Weil generators; for some curves
# rank/descent may fail or be slow (conductor grows fast with x). Failures are logged;
# retry those with proof=False, mwrank with higher descent bounds, or Magma.
# Run: sage ec_search.sage

import sys
K = 19
XMAX = 300          # push as far as your patience allows; cost grows with x
UMAX = 300
WINDOWS = [(10^20, 10^30), (10^30, 10^40)]

def report(x, n, y, tag):
    N = 36*n^3 - K
    assert n and N % x == 0 and y^2 == (6*n+x)^2 + N//x, "verification failed"
    loc = next((f"IN WINDOW {a}..{b}" for a, b in WINDOWS if a <= n < b),
               "outside target windows")
    print(f"SOLUTION [{tag}]  x={x}  n={n}  y={y}   ({loc})", flush=True)

for x in range(1, XMAX+1):
    if gcd(x, 6) != 1:          # 36n^3-19 is odd and == 2 (mod 3)
        continue
    E = EllipticCurve([0, 36*x^2, 0, 432*x^4, 1296*x^6 - 1296*K*x^3])
    try:
        pts = E.integral_points(both_signs=True)
    except Exception as e:
        print(f"x={x}: integral_points FAILED ({e}) — retry manually", flush=True)
        continue
    for P in pts:
        U, V = P[0], P[1]
        if U % (36*x) == 0 and V % (36*x^2) == 0:
            n = U // (36*x)
            y = abs(V // (36*x^2))
            if n != 0 and (36*n^3 - K) % x == 0:
                report(x, n, y, "x-fiber")
    print(f"# x={x} done, rank={E.rank()}", flush=True)

for u in range(1, UMAX+1):
    if gcd(u, 6) != 1:
        continue
    F = EllipticCurve([0, 144*u^2, 0, 6912*u^4, 82944*u^6 - 663552*K*u^3])
    try:
        pts = F.integral_points(both_signs=True)
    except Exception as e:
        print(f"u={u}: integral_points FAILED ({e}) — retry manually", flush=True)
        continue
    for P in pts:
        U, V = P[0], P[1]
        if U % (288*u) or V % (288*u^2):
            continue
        n = U // (288*u)
        s = abs(V // (288*u^2))
        w = s - u - 12*n
        if n != 0 and w > 0 and w % 4 == 0:
            x = w // 4
            y = x + 6*n + u
            if (36*n^3 - K) % x == 0 and y^2 == (6*n+x)^2 + (36*n^3-K)//x:
                report(x, n, y, f"u-fiber u={u}")
    print(f"# u={u} done, rank={F.rank()}", flush=True)
