#!/usr/bin/env python3
"""
Exact verification of all 50 known (n, m, |y|) triples for
y^2 = (36n^3 - 19 - 12mn)^2 - (2m)^3,
and of any new hits piped in as lines 'n m y'.

Usage:
  python3 verify_solutions.py              # just verify the table
  python3 verify_solutions.py < hits.txt  # also check new hits
"""
import sys

ROWS = [
(-29317,-335124555576,561438594393311033),
(-29317,-1373577672,1397778450840953),
(-14362,454411005,7213473617543),
(-9925,185596059,10965628195127),
(-6561,83882471,2823976115241),
(-4741,45340050,913195026575),
(-2271,-196197225,9679512465865),
(-1641,-620850,171316003825),
(-970,-739259850,57503797038269),
(-921,1452425,11010153735),
(-675,-613606,16099399767),
(-570,-1931787,21281482855),
(-367,289374,247553783),
(-234,-1074880501,99720478180593),
(-147,-166915,452011593),
(-57,-2926,8679903),
(-54,-10743,13016935),
(-54,4749,2420407),
(-29,-16716,9066007),
(-4,-1818,236845),
(-4,-1032,107155),
(1,-51,1207),
(1,-3,55),
(15,-1207,358905),
(19,-252195,362844665),
(19,-1197,532855),
(46,-21522,17788355),
(75,11523,3310775),
(93,-175921,307097193),
(114,27575,8719215),
(131,-401940,1013677687),
(309,56375,852251625),
(790,1096893,6593716025),
(798,-5378466956142,35280376688536712227),
(798,-5586,18347596867),
(909,-11607484,190054724721),
(909,1826300,1390662225),
(1626,-213292581,9811228042657),
(1759,6612585,29364964345),
(5118,-526254004,50456015630061),
(11409,-1918935865,395599034387145),
(11527,-67430670,64484348509601),
(11750,-1737888261,366153513664753),
(14709,-2616641560,689629545026145),
(14709,473559320,10489917226785),
(15519,-2004788485,567823975362135),
(16531,220439859,118539695046007),
(17309,225396696,139544322245119),
(18344,-1152587709,488636781747209),
(27949,7804038,783344205524825),
]

def check(n, m, y):
    A = 36*n**3 - 19 - 12*m*n
    return y*y == A*A - (2*m)**3

def translate(n, m, y, c):
    """Apply torsion-translate T=(0,c) to solution (n,m,y); return new m' if integral."""
    results = []
    for eps in (1, -1):
        num = eps*y - c
        if num % (2*m) != 0:
            continue
        q = num // (2*m)
        mp = -(q*q - 36*n*n + 2*m) // 2
        if (q*q - 36*n*n + 2*m) % 2 != 0:
            continue
        if mp != 0 and mp != m:
            A2 = 36*n**3 - 19 - 12*mp*n
            y2sq = A2*A2 - (2*mp)**3
            if y2sq > 0:
                import math
                y2 = int(math.isqrt(y2sq))
                if y2*y2 == y2sq:
                    results.append((mp, y2))
    return results

# --- verify the table ---
bad = [(n,m) for n,m,y in ROWS if not check(n,m,y)]
print(f"table: {len(ROWS)-len(bad)}/{len(ROWS)} rows valid", "" if not bad else f"BAD: {bad}")

known = {(n,m) for n,m,_ in ROWS}

# --- process any piped input ---
if not sys.stdin.isatty():
    for line in sys.stdin:
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        parts = line.split()
        if len(parts) < 3:
            continue
        try:
            n, m, y = int(parts[0]), int(parts[1]), int(parts[2])
        except ValueError:
            continue
        tag = "known" if (n,m) in known else "NEW  "
        valid = check(n, m, y)
        c = 36*n**3 - 19
        tr = translate(n, m, y, c) if valid else []
        tr_str = ""
        if tr:
            for mp, yp in tr:
                ttag = "known" if (n,mp) in known else "NEW-TRANSLATE"
                tr_str += f"  -> {ttag} n={n} m={mp} |y|={yp}"
        print(f"{tag}  n={n:>8}  m={m:>20}  valid={valid}{tr_str}")
