"""Efficient multistart optimizer: SLSQP minimizes s directly, seeded by a short
relaxation. Much faster than binary-search-over-relaxation."""
import numpy as np, math
from solver import CONTAINERS, polish, verify

def quick_relax(container, n, s, P, steps=300):
    for it in range(steps):
        diff = P[:,None,:]-P[None,:,:]
        dist = np.sqrt((diff**2).sum(-1)) + np.eye(n)*1e9
        overlap = 2.0 - dist
        np.fill_diagonal(overlap,0.0)
        mask = overlap>0
        if mask.any():
            with np.errstate(invalid='ignore',divide='ignore'):
                u = diff/dist[:,:,None]
            push = np.where(mask[:,:,None], u*(overlap[:,:,None]*0.5),0.0)
            P = P + push.sum(axis=1)
        P = container.project(P,s)
    return P

def one_start(container, n, s_init, rng):
    P = container.random_start(n, s_init, rng)
    P = quick_relax(container, n, s_init, P, steps=250)
    s2,P2,res = polish(container, n, s_init, P)
    ok,mp,wc = verify(container, n, s2, P2)
    if ok:
        return s2, P2
    return None, None

def optimize(container, n, s_guess, rng, starts=40, spread=0.5):
    """s_guess: a roomy upper bound on s. Returns best (s,P) verified feasible."""
    best_s=None; best_P=None
    for k in range(starts):
        # vary init scale a bit above guess for room
        s_init = s_guess*(1.0+spread*rng.random())
        s,P = one_start(container, n, s_init, rng)
        if s is not None and (best_s is None or s<best_s):
            best_s=s; best_P=P
    # extra polishing passes from best, with small perturbations
    if best_P is not None:
        for k in range(15):
            Pp = best_P + rng.normal(0, 0.05, best_P.shape)
            Pp = container.project(Pp, best_s*1.02)
            s,P,res = polish(container,n,best_s*1.02,Pp)
            ok,mp,wc = verify(container,n,s,P)
            if ok and s<best_s:
                best_s=s; best_P=P
    return best_s, best_P

if __name__=='__main__':
    print("optimize module OK")
