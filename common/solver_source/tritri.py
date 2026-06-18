"""Circles in arbitrary triangles: minimize triangle AREA containing n unit circles.
Gauge: v1=(0,0), v2=(b,0), v3=(cx,cy), b>0, cy>0 (CCW).
vars z = [b, cx, cy, p0x,p0y, p1x,p1y, ...] length 3+2n.
Constraints:
  bottom edge:   py_i >= 1
  edge v2->v3:   dx*py_i - cy*px_i + cy*b - L >= 0,  dx=cx-b, L=sqrt(dx^2+cy^2)
  edge v3->v1:   cy*px_i - cx*py_i - M >= 0,         M=sqrt(cx^2+cy^2)
  pairwise:      |pi-pj|^2 >= 4
Objective: area = 0.5*b*cy.
"""
import numpy as np, math
from scipy.optimize import minimize

def area_of(z): return 0.5*z[0]*z[2]

def make_cons(n):
    cons=[]
    def gA(i):
        yi=4+2*i
        def f(z,yi=yi): return z[yi]-1.0
        def j(z,yi=yi):
            v=np.zeros_like(z); v[yi]=1.0; return v
        return {'type':'ineq','fun':f,'jac':j}
    def gB(i):
        xi=3+2*i; yi=4+2*i
        def f(z,xi=xi,yi=yi):
            b,cx,cy=z[0],z[1],z[2]; dx=cx-b; L=math.hypot(dx,cy)
            return dx*z[yi]-cy*z[xi]+cy*b-L
        def j(z,xi=xi,yi=yi):
            b,cx,cy=z[0],z[1],z[2]; dx=cx-b; L=math.hypot(dx,cy)
            v=np.zeros_like(z)
            v[0]  = -z[yi]+cy+dx/L          # d/db
            v[1]  =  z[yi]-dx/L             # d/dcx
            v[2]  = -z[xi]+b-cy/L           # d/dcy
            v[xi] = -cy
            v[yi] = dx
            return v
        return {'type':'ineq','fun':f,'jac':j}
    def gC(i):
        xi=3+2*i; yi=4+2*i
        def f(z,xi=xi,yi=yi):
            cx,cy=z[1],z[2]; M=math.hypot(cx,cy)
            return cy*z[xi]-cx*z[yi]-M
        def j(z,xi=xi,yi=yi):
            cx,cy=z[1],z[2]; M=math.hypot(cx,cy)
            v=np.zeros_like(z)
            v[1]= -z[yi]-cx/M     # d/dcx
            v[2]=  z[xi]-cy/M     # d/dcy
            v[xi]= cy
            v[yi]= -cx
            return v
        return {'type':'ineq','fun':f,'jac':j}
    for i in range(n):
        cons.append(gA(i)); cons.append(gB(i)); cons.append(gC(i))
    for i in range(n):
        for k in range(i+1,n):
            xi=3+2*i;yi=4+2*i;xk=3+2*k;yk=4+2*k
            def f(z,xi=xi,yi=yi,xk=xk,yk=yk):
                return (z[xi]-z[xk])**2+(z[yi]-z[yk])**2-4.0
            def j(z,xi=xi,yi=yi,xk=xk,yk=yk):
                v=np.zeros_like(z); dx=z[xi]-z[xk]; dy=z[yi]-z[yk]
                v[xi]=2*dx;v[xk]=-2*dx;v[yi]=2*dy;v[yk]=-2*dy; return v
            cons.append({'type':'ineq','fun':f,'jac':j})
    return cons

def tri_edges_inside(z, P, n):
    """min slack of P wrt the 3 offset edges (>=0 feasible)."""
    b,cx,cy=z[0],z[1],z[2]; dx=cx-b; L=math.hypot(dx,cy); M=math.hypot(cx,cy)
    sl=[]
    for i in range(n):
        px,py=P[i]
        sl.append(py-1.0)
        sl.append(dx*py-cy*px+cy*b-L)
        sl.append(cy*px-cx*py-M)
    return min(sl)

def project_tri(z, P, n, iters=10):
    """Push centers inside offset triangle defined by z."""
    b,cx,cy=z[0],z[1],z[2]; dx=cx-b; L=math.hypot(dx,cy); M=math.hypot(cx,cy)
    # edge normals (inward) and offsets for constraint nrm.p <= off-... we use signed forms
    for _ in range(iters):
        for i in range(n):
            px,py=P[i]
            # bottom: py>=1
            if py<1.0: py=1.0
            # edge B: dx*py - cy*px + cy*b - L >=0; normal grad (−cy, dx)/?; move along
            gB=dx*py-cy*px+cy*b-L
            if gB<0:
                nrm=math.hypot(cy,dx)
                px += (-cy)*(gB)/(nrm*nrm)*(-1)   # move to increase gB
                py += (dx)*(gB)/(nrm*nrm)*(-1)
            # edge C: cy*px - cx*py - M >=0; grad (cy,-cx)
            gC=cy*px-cx*py-M
            if gC<0:
                nrm=math.hypot(cy,cx)
                px += (cy)*(gC)/(nrm*nrm)*(-1)
                py += (-cx)*(gC)/(nrm*nrm)*(-1)
            if py<1.0: py=1.0
            P[i]=[px,py]
    return P

def relax_tri(z, P, n, steps=200):
    for _ in range(steps):
        diff=P[:,None,:]-P[None,:,:]
        dist=np.sqrt((diff**2).sum(-1))+np.eye(n)*1e9
        ov=2.0-dist; np.fill_diagonal(ov,0.0); mask=ov>0
        if mask.any():
            with np.errstate(invalid='ignore',divide='ignore'):
                u=diff/dist[:,:,None]
            P=P+np.where(mask[:,:,None],u*(ov[:,:,None]*0.5),0.0).sum(1)
        P=project_tri(z,P,n,iters=4)
    return P

def verify_tri(z, n, tol=1e-7):
    P=np.column_stack([z[3::2],z[4::2]])
    # pairwise
    diff=P[:,None,:]-P[None,:,:]
    d=np.sqrt((diff**2).sum(-1))+np.eye(n)*1e18
    mp=d.min()
    sl=tri_edges_inside(z,P,n)
    ok = mp>=2.0-tol and sl>=-tol
    return ok, mp, sl, area_of(z)

def solve_tri(n, area_guess, rng, starts=60):
    cons=make_cons(n)
    best=None
    # rough triangle scale from area guess (assume near-equilateral)
    s_eq=math.sqrt(area_guess*4/math.sqrt(3))
    for k in range(starts):
        # random-ish triangle near equilateral, perturbed
        b=s_eq*(0.7+0.6*rng.random())
        ang=math.radians(40+40*rng.random())  # apex-ish
        cx=b*rng.uniform(0.2,0.8)
        cy=b*(0.5+0.7*rng.random())
        z=np.zeros(3+2*n); z[0]=b; z[1]=cx; z[2]=cy
        # seed centers by rejection in bounding box then project+relax
        P=np.column_stack([rng.uniform(1,max(b,cx)-0.5,n), rng.uniform(1,cy-0.5,n)])
        P=project_tri(z,P,n,iters=12); P=relax_tri(z,P,n,steps=150)
        z[3::2]=P[:,0]; z[4::2]=P[:,1]
        bnds=[(1e-3,None),(None,None),(1e-3,None)]+[(None,None)]*(2*n)
        try:
            r=minimize(area_of,z,jac=lambda z:_garea(z),method='SLSQP',
                       constraints=cons,bounds=bnds,options={'maxiter':500,'ftol':1e-12})
        except Exception:
            continue
        ok,mp,sl,A=verify_tri(r.x,n)
        if ok and (best is None or A<best[0]):
            best=(A,r.x.copy())
    # polish best with perturbations
    if best is not None:
        A0,z0=best
        for _ in range(20):
            z=z0.copy()
            z[3:]+=rng.normal(0,0.03,2*n)
            z[0]*=(1+rng.normal(0,0.01)); z[2]*=(1+rng.normal(0,0.01))
            try:
                r=minimize(area_of,z,jac=lambda z:_garea(z),method='SLSQP',
                           constraints=cons,bounds=[(1e-3,None),(None,None),(1e-3,None)]+[(None,None)]*(2*n),
                           options={'maxiter':500,'ftol':1e-12})
            except Exception: continue
            ok,mp,sl,A=verify_tri(r.x,n)
            if ok and A<best[0]: best=(A,r.x.copy())
    return best

def _garea(z):
    v=np.zeros_like(z); v[0]=0.5*z[2]; v[2]=0.5*z[0]; return v

if __name__=='__main__':
    print("tritri module OK")
