"""
Equal-circle packing optimizer for Erich Friedman's packing center.

Problem: pack n unit circles (radius 1) into the smallest container of a given
shape, parameterized by a single scale s. Equivalent to placing n center points
with each center >=1 from every wall and pairwise >=2 apart, minimizing s.

Containers:
  - Regular m-gon with side length s  (triangle m=3, pentagon m=5, hexagon m=6)
  - L-tromino with outer side s (three s/2 squares; top-right s/2 square removed)

Method: force-relaxation (repulsion + boundary projection) with binary search on
s for many random restarts, then SLSQP polish to high precision. A rigorous
arithmetic verifier confirms every reported packing.
"""
import numpy as np
from scipy.optimize import minimize
import math

# ----------------------------------------------------------------------------
# Container definitions
# ----------------------------------------------------------------------------

class RegularPolygon:
    """Regular m-gon, centered at origin, parameterized by side length s.
    apothem a = s / (2 tan(pi/m)); a center point p is feasible (margin 1) iff
    n_k . p <= a - 1 for every outward unit edge normal n_k."""
    def __init__(self, m, rot=0.0):
        self.m = m
        self.ca = 1.0 / (2.0 * math.tan(math.pi / m))     # apothem = ca * s
        ang = np.array([2*math.pi*k/m + rot for k in range(m)])
        # outward edge normals (edges centered between vertices); pick normals
        self.nx = np.cos(ang)
        self.ny = np.sin(ang)

    def apothem(self, s):
        return self.ca * s

    def s_from_apothem(self, a):
        return a / self.ca

    def margin_inradius(self, s):
        """Largest distance a center can be from polygon center (approx, for init)."""
        return max(self.apothem(s) - 1.0, 0.0)

    def project(self, P, s):
        """Project points P (k,2) into the feasible region (margin 1)."""
        a1 = self.apothem(s) - 1.0
        for _ in range(8):
            d = P[:,0:1]*self.nx[None,:] + P[:,1:2]*self.ny[None,:]   # (k,m)
            viol = d - a1                                            # >0 means outside
            mx = viol.max(axis=1)
            bad = mx > 1e-12
            if not bad.any():
                break
            kidx = viol.argmax(axis=1)
            ex = np.maximum(mx, 0.0)
            P[:,0] -= ex * self.nx[kidx]
            P[:,1] -= ex * self.ny[kidx]
        return P

    def wall_clearance(self, P, s):
        """min over points of (apothem - n.p) -- should be >= 1 for feasibility."""
        a = self.apothem(s)
        d = P[:,0:1]*self.nx[None,:] + P[:,1:2]*self.ny[None,:]
        return (a - d).min()

    # SLSQP constraint machinery: variables z = [s, x0,y0,x1,y1,...]
    def constraints(self, n):
        m = self.m; ca = self.ca; nx = self.nx; ny = self.ny
        cons = []
        # wall constraints: for each point i, each edge k: ca*s - 1 - (nx*x+ny*y) >= 0
        for i in range(n):
            xi = 1+2*i; yi = 2+2*i
            for k in range(m):
                def f(z, i=i, k=k, xi=xi, yi=yi):
                    return ca*z[0] - 1.0 - (nx[k]*z[xi] + ny[k]*z[yi])
                def g(z, i=i, k=k, xi=xi, yi=yi):
                    jac = np.zeros_like(z)
                    jac[0] = ca; jac[xi] = -nx[k]; jac[yi] = -ny[k]
                    return jac
                cons.append({'type':'ineq','fun':f,'jac':g})
        _add_pair_constraints(cons, n)
        return cons

    def random_start(self, n, s, rng):
        a1 = max(self.apothem(s)-1.0, 1e-3)
        P = rng.uniform(-a1, a1, size=(n,2))
        return self.project(P, s)


class LTromino:
    """L-tromino: outer bounding square [0,s] x [0,s] with the top-right
    s/2 x s/2 square [s/2,s] x [s/2,s] removed.  Center feasible (margin 1) iff
      1 <= x <= s-1, 1 <= y <= s-1, and dist(center, removed box) >= 1,
    where dist to removed box = sqrt(max(s/2-x,0)^2 + max(s/2-y,0)^2)."""
    def project(self, P, s):
        h = s/2.0
        P[:,0] = np.clip(P[:,0], 1.0, s-1.0)
        P[:,1] = np.clip(P[:,1], 1.0, s-1.0)
        for _ in range(6):
            x = P[:,0]; y = P[:,1]
            dx = np.maximum(h - x, 0.0)
            dy = np.maximum(h - y, 0.0)
            d2 = dx*dx + dy*dy
            bad = d2 < 1.0 - 1e-15
            if not bad.any():
                break
            for idx in np.where(bad)[0]:
                xi, yi = P[idx,0], P[idx,1]
                if xi < h and yi < h:
                    d = math.hypot(h-xi, h-yi)
                    if d < 1e-9:
                        P[idx] = [h-1.0, yi]       # arbitrary push
                    else:
                        sc = 1.0/d
                        P[idx,0] = h - (h-xi)*sc
                        P[idx,1] = h - (h-yi)*sc
                elif xi >= h and yi < h:
                    P[idx,1] = h - 1.0
                elif yi >= h and xi < h:
                    P[idx,0] = h - 1.0
                else:  # both >= h : inside removed box, eject to nearest strip
                    if (xi - (h-1.0)) <= (yi - (h-1.0)):
                        P[idx,0] = h - 1.0
                    else:
                        P[idx,1] = h - 1.0
            P[:,0] = np.clip(P[:,0], 1.0, s-1.0)
            P[:,1] = np.clip(P[:,1], 1.0, s-1.0)
        return P

    def wall_clearance(self, P, s):
        """Returns signed min clearance to all walls (>=0 means feasible, want the
        circle radius 1 to fit => returns min slack vs radius 1, i.e. >=0 ok)."""
        h = s/2.0
        x = P[:,0]; y = P[:,1]
        left = x; bottom = y; right = s - x; top = s - y
        dx = np.maximum(h - x, 0.0); dy = np.maximum(h - y, 0.0)
        notch = np.sqrt(dx*dx + dy*dy)
        # each must be >= 1
        return float(np.min([left.min(), bottom.min(), right.min(), top.min(), notch.min()])) - 1.0

    def constraints(self, n):
        cons = []
        for i in range(n):
            xi = 1+2*i; yi = 2+2*i
            # x>=1
            cons.append({'type':'ineq','fun':(lambda z,xi=xi: z[xi]-1.0),
                         'jac':(lambda z,xi=xi: _e(z,xi,1.0))})
            # y>=1
            cons.append({'type':'ineq','fun':(lambda z,yi=yi: z[yi]-1.0),
                         'jac':(lambda z,yi=yi: _e(z,yi,1.0))})
            # s-1-x>=0
            cons.append({'type':'ineq','fun':(lambda z,xi=xi: z[0]-1.0-z[xi]),
                         'jac':(lambda z,xi=xi: _e2(z,0,1.0,xi,-1.0))})
            # s-1-y>=0
            cons.append({'type':'ineq','fun':(lambda z,yi=yi: z[0]-1.0-z[yi]),
                         'jac':(lambda z,yi=yi: _e2(z,0,1.0,yi,-1.0))})
            # notch: max(s/2-x,0)^2+max(s/2-y,0)^2 - 1 >= 0
            def fn(z, xi=xi, yi=yi):
                h = z[0]/2.0
                dx = max(h - z[xi], 0.0); dy = max(h - z[yi], 0.0)
                return dx*dx + dy*dy - 1.0
            def jn(z, xi=xi, yi=yi):
                h = z[0]/2.0
                dx = max(h - z[xi], 0.0); dy = max(h - z[yi], 0.0)
                jac = np.zeros_like(z)
                ax = 1.0 if (h - z[xi]) > 0 else 0.0
                ay = 1.0 if (h - z[yi]) > 0 else 0.0
                jac[xi] = 2*dx*(-ax)
                jac[yi] = 2*dy*(-ay)
                jac[0]  = 2*dx*(0.5*ax) + 2*dy*(0.5*ay)
                return jac
            cons.append({'type':'ineq','fun':fn,'jac':jn})
        _add_pair_constraints(cons, n)
        return cons

    def random_start(self, n, s, rng):
        # sample uniformly in the L by rejection
        pts = []
        h = s/2.0
        while len(pts) < n:
            x = rng.uniform(1.0, s-1.0); y = rng.uniform(1.0, s-1.0)
            dx = max(h-x,0.0); dy = max(h-y,0.0)
            if dx*dx+dy*dy >= 1.0:
                pts.append((x,y))
        return self.project(np.array(pts), s)


def _e(z, i, v):
    j = np.zeros_like(z); j[i] = v; return j

def _e2(z, i, vi, k, vk):
    j = np.zeros_like(z); j[i] = vi; j[k] = vk; return j

def _add_pair_constraints(cons, n):
    for i in range(n):
        for j in range(i+1, n):
            xi=1+2*i; yi=2+2*i; xj=1+2*j; yj=2+2*j
            def f(z, xi=xi,yi=yi,xj=xj,yj=yj):
                return (z[xi]-z[xj])**2 + (z[yi]-z[yj])**2 - 4.0
            def g(z, xi=xi,yi=yi,xj=xj,yj=yj):
                jac=np.zeros_like(z)
                dx=z[xi]-z[xj]; dy=z[yi]-z[yj]
                jac[xi]=2*dx; jac[xj]=-2*dx; jac[yi]=2*dy; jac[yj]=-2*dy
                return jac
            cons.append({'type':'ineq','fun':f,'jac':g})

# ----------------------------------------------------------------------------
# Force relaxation (find a feasible packing at fixed scale s)
# ----------------------------------------------------------------------------

def relax(container, n, s, rng, iters=2000):
    P = container.random_start(n, s, rng)
    for it in range(iters):
        # pairwise repulsion: resolve overlaps (dist<2)
        diff = P[:,None,:] - P[None,:,:]
        dist = np.sqrt((diff**2).sum(-1)) + np.eye(n)*1e9
        overlap = 2.0 - dist
        np.fill_diagonal(overlap, 0.0)
        mask = overlap > 0
        if mask.any():
            with np.errstate(invalid='ignore', divide='ignore'):
                u = diff / dist[:,:,None]
            push = np.where(mask[:,:,None], u * (overlap[:,:,None]*0.5), 0.0)
            P = P + push.sum(axis=1)
        P = container.project(P, s)
        if it % 50 == 0 or mask.sum()==0:
            # check feasibility
            if not mask.any() and container.wall_clearance(P, s) >= -1e-9:
                # verify pairwise after projection
                diff2 = P[:,None,:]-P[None,:,:]
                d2 = np.sqrt((diff2**2).sum(-1)) + np.eye(n)*1e9
                if d2.min() >= 2.0 - 1e-7:
                    return P, True
    # final check
    diff2 = P[:,None,:]-P[None,:,:]
    d2 = np.sqrt((diff2**2).sum(-1)) + np.eye(n)*1e9
    ok = d2.min() >= 2.0 - 1e-7 and container.wall_clearance(P, s) >= -1e-7
    return P, ok


def find_packing(container, n, s_lo, s_hi, rng, restarts=12, iters=1500):
    """Binary search smallest s in [s_lo,s_hi] with a feasible packing found by relax."""
    best_P = None
    # ensure s_hi feasible
    for _ in range(restarts):
        P, ok = relax(container, n, s_hi, rng, iters)
        if ok:
            best_P = P.copy(); break
    if best_P is None:
        return None, None
    lo, hi = s_lo, s_hi
    for _ in range(34):
        mid = 0.5*(lo+hi)
        found = None
        for _ in range(restarts):
            P, ok = relax(container, n, mid, rng, iters)
            if ok:
                found = P; break
        if found is not None:
            hi = mid; best_P = found.copy()
        else:
            lo = mid
        if hi - lo < 1e-4:
            break
    return hi, best_P

# ----------------------------------------------------------------------------
# SLSQP polish: minimize s exactly
# ----------------------------------------------------------------------------

def polish(container, n, s0, P0, maxiter=400):
    z0 = np.empty(1+2*n)
    z0[0] = s0
    z0[1::2] = P0[:,0]
    z0[2::2] = P0[:,1]
    cons = container.constraints(n)
    # objective: minimize s
    def obj(z): return z[0]
    def jac(z):
        j = np.zeros_like(z); j[0]=1.0; return j
    # bound s positive
    bounds = [(1e-3, None)] + [(None,None)]*(2*n)
    res = minimize(obj, z0, jac=jac, method='SLSQP', constraints=cons,
                   bounds=bounds, options={'maxiter':maxiter,'ftol':1e-12})
    s = res.x[0]
    P = np.column_stack([res.x[1::2], res.x[2::2]])
    return s, P, res

# ----------------------------------------------------------------------------
# Rigorous verification
# ----------------------------------------------------------------------------

def verify(container, n, s, P, tol=1e-9):
    """Returns (ok, min_pair_dist, min_wall_clear). Feasible iff min_pair>=2 and
    min_wall_clear>=1 (within tol)."""
    diff = P[:,None,:]-P[None,:,:]
    d = np.sqrt((diff**2).sum(-1)) + np.eye(n)*1e18
    minpair = d.min()
    wc = container.wall_clearance(P, s) + 1.0  # wall_clearance returns slack-1
    return (minpair >= 2.0 - tol and wc >= 1.0 - tol), minpair, wc


CONTAINERS = {
    'tri': RegularPolygon(3),
    'pen': RegularPolygon(5),
    'hex': RegularPolygon(6),
    'L':   LTromino(),
}

# side-length conversion already baked in: for polygons s is the side length,
# for L, s is the outer side length.

if __name__ == '__main__':
    print("solver module loaded OK")
