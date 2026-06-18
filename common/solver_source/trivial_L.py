"""Trivial baselines for circles in L-tromino, to compare against optimized records.
Square-grid and hex-grid packings; for each n find smallest s that fits n via that
construction. Also returns the configuration for seeding the optimizer."""
import numpy as np, math

def count_in_L(P, s, tol=1e-9):
    """count points satisfying all L constraints with margin 1."""
    h=s/2.0
    ok=[]
    for (x,y) in P:
        if x<1-tol or y<1-tol or x>s-1+tol or y>s-1+tol:
            continue
        dx=max(h-x,0.0); dy=max(h-y,0.0)
        if dx*dx+dy*dy < 1-tol:
            continue
        ok.append((x,y))
    return ok

def square_grid_points(s, dx0=1.0, dy0=1.0, spacing=2.0):
    h=s/2.0
    xs=np.arange(dx0, s-1+1e-9, spacing)
    ys=np.arange(dy0, s-1+1e-9, spacing)
    P=[(x,y) for x in xs for y in ys]
    return count_in_L(P,s)

def hex_grid_points(s, spacing=2.0):
    """hex (offset rows) packing."""
    h=s/2.0
    dy=spacing*math.sqrt(3)/2.0
    P=[]
    j=0
    y=1.0
    while y<=s-1+1e-9:
        xoff = 1.0 + (spacing/2.0 if j%2 else 0.0)
        x=xoff
        while x<=s-1+1e-9:
            P.append((x,y)); x+=spacing
        y+=dy; j+=1
    return count_in_L(P,s)

def best_trivial_s(n, smax=20.0, step=0.0005):
    """smallest s such that square-grid OR hex-grid fits >= n circles."""
    best=None; bestkind=None; bestP=None
    s=2.0
    # square grid: try a few origin offsets
    while s<=smax:
        for kind,fn in (('sq',square_grid_points),('hex',hex_grid_points)):
            P=fn(s)
            if len(P)>=n:
                if best is None or s<best:
                    best=s; bestkind=kind; bestP=P[:n]
        if best is not None:
            break
        s+=step
    # refine downward a touch
    if best is not None:
        lo=best-step; hi=best
        for _ in range(20):
            mid=0.5*(lo+hi)
            ok=False
            for fn in (square_grid_points,hex_grid_points):
                if len(fn(mid))>=n: ok=True;break
            if ok: hi=mid
            else: lo=mid
        best=hi
    return best,bestkind,bestP

if __name__=='__main__':
    import math
    REC={4:5.304,5:5.780,6:6.416,7:6.787,8:7.116,9:4+12/math.sqrt(13),
         10:7.628,11:4+math.sqrt(2)+math.sqrt(6),12:8.0,13:8.812,
         14:9.085,15:9.412,16:9.635}
    print(f"{'n':>3} {'record':>9} {'trivial_s':>10} {'kind':>5}  note")
    for n in range(1,31):
        ts,kind,P=best_trivial_s(n)
        rec=REC.get(n)
        recs=f"{rec:.3f}" if rec else "  --  "
        note=''
        if rec and ts is not None:
            if ts < rec-1e-3: note='*** TRIVIAL BEATS RECORD ***'
            elif abs(ts-rec)<1e-3: note='record==trivial'
            else: note=f'record better by {ts-rec:.3f}'
        print(f"{n:>3} {recs:>9} {ts:>10.4f} {kind:>5}  {note}")
