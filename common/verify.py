#!/usr/bin/env python3
"""
Standalone independent verifier for all packing results in this repository.

It reads ONLY the data/packings.json files (coordinates + container geometry) and
checks, with pure arithmetic, that every claimed packing is valid:

    * every pair of unit-circle centers is at least 2.0 apart   (circles don't overlap)
    * every center is at least 1.0 from every container wall     (circles stay inside)

A packing is valid iff min_pair_dist >= 2 and min_wall_clearance >= 1 (within TOL).
No optimizer code is used or trusted here; this is an independent audit of the
coordinates.

Usage:  python3 common/verify.py            (verifies everything)
        python3 common/verify.py cirinl     (one category)
"""
import json, math, os, sys

TOL = 1e-7
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def _pair_min(P):
    m = float('inf')
    for i in range(len(P)):
        xi, yi = P[i]
        for j in range(i+1, len(P)):
            d = math.hypot(xi-P[j][0], yi-P[j][1])
            if d < m: m = d
    return m

# ----- container wall-clearance functions (min distance center->boundary) -----
def wall_clear_L(P, s):
    """L-tromino = [0,s]x[0,s] minus [s/2,s]x[s/2,s]. Reentrant notch at (s/2,s/2)."""
    h = s/2.0
    m = float('inf')
    for x, y in P:
        c = min(x, y, s-x, s-y)                      # four outer walls
        if x > h and y > h:                          # inside removed square => invalid
            c = min(c, -min(x-h, y-h))
        else:                                        # clearance to reentrant corner box
            c = min(c, math.hypot(max(h-x, 0.0), max(h-y, 0.0)))
        if c < m: m = c
    return m

def wall_clear_triangle(P, verts):
    """Min signed distance from each center to the 3 triangle edges (interior +)."""
    A, B, C = (tuple(v) for v in verts)
    cen = ((A[0]+B[0]+C[0])/3.0, (A[1]+B[1]+C[1])/3.0)
    def edge(p, U, V):
        dx, dy = V[0]-U[0], V[1]-U[1]
        L = math.hypot(dx, dy)
        nx, ny = -dy/L, dx/L
        val  = nx*(p[0]-U[0]) + ny*(p[1]-U[1])
        valc = nx*(cen[0]-U[0]) + ny*(cen[1]-U[1])
        return val if valc >= 0 else -val
    m = float('inf')
    for p in P:
        for U, V in ((A,B),(B,C),(C,A)):
            c = edge(p, U, V)
            if c < m: m = c
    return m

def verify_cirinl(path):
    packs = json.load(open(path))
    print(f"\n=== cirinl (circles in L-tromino) — {len(packs)} packings ===")
    print(f"{'n':>3} {'side s':>11} {'min_pair':>11} {'min_wall':>11}  status")
    allok = True
    for n in sorted(packs, key=int):
        d = packs[n]; P = d['centers']; s = d['side_s']
        assert len(P) == int(n), f"n={n}: {len(P)} centers!"
        mp = _pair_min(P); mw = wall_clear_L(P, s)
        ok = mp >= 2-TOL and mw >= 1-TOL
        allok &= ok
        print(f"{int(n):>3} {s:>11.6f} {mp:>11.7f} {mw:>11.7f}  {'OK' if ok else 'FAIL'}")
    return allok

def verify_cirinttt(path):
    packs = json.load(open(path))
    print(f"\n=== cirinttt (circles in arbitrary triangles) — {len(packs)} packings ===")
    print(f"{'n':>3} {'area':>11} {'min_pair':>11} {'min_wall':>11}  status")
    allok = True
    for n in sorted(packs, key=int):
        d = packs[n]; P = d['centers']; V = d['triangle_vertices']
        assert len(P) == int(n), f"n={n}: {len(P)} centers!"
        mp = _pair_min(P); mw = wall_clear_triangle(P, V)
        area = 0.5*abs((V[1][0]-V[0][0])*(V[2][1]-V[0][1]) - (V[2][0]-V[0][0])*(V[1][1]-V[0][1]))
        ok = mp >= 2-TOL and mw >= 1-TOL
        allok &= ok
        print(f"{int(n):>3} {area:>11.5f} {mp:>11.7f} {mw:>11.7f}  {'OK' if ok else 'FAIL'}")
    return allok

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    ok = True
    if which in ('all', 'cirinl'):
        p = os.path.join(ROOT, 'cirinl_circles_in_L', 'data', 'packings.json')
        if os.path.exists(p): ok &= verify_cirinl(p)
    if which in ('all', 'cirinttt'):
        p = os.path.join(ROOT, 'cirinttt_circles_in_triangles', 'data', 'packings.json')
        if os.path.exists(p): ok &= verify_cirinttt(p)
    print("\n" + ("ALL PACKINGS VERIFIED VALID" if ok else "*** SOME PACKINGS FAILED ***"))
    sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main()
