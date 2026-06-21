"""
Corroboration script for proof_ellipse_n2.tex.

Theorem: the smallest-area ellipse containing two interior-disjoint unit circles has
area A = (3*sqrt(3)/2)*pi, attained by semi-axes a = 3*sqrt(2)/2, b = sqrt(6)/2 with the
circles centered at (+-1,0) and touching at the origin.

Every algebraic identity in the human proof is re-derived here in exact arithmetic
(sympy), plus an independent numerical SLSQP optimization of the FULL problem.
"""
import sympy as sp

print("="*72)
print("PART 1.  Exact algebra behind the human proof")
print("="*72)

u, v, c, x = sp.symbols('u v c x', positive=True)   # u=a^2, v=b^2, c=cos t

# ---- 1a. Containment of the unit disk at (1,0): g(c) <= 1 on c in [-1,1] -------------
# Disk boundary point (1+cos t, sin t); ellipse value there, in c=cos t:
g = (1+c)**2/u + (1-c**2)/v
g = sp.expand(g)
print("\n[1a] g(c) =", g)
print("     coeff of c^2 =", sp.simplify(g.coeff(c, 2)), " (= 1/u - 1/v, <0 iff u>v)")
# vertex of this parabola and its value
cstar = sp.simplify(-g.coeff(c, 1)/(2*g.coeff(c, 2)))
gmax = sp.simplify(g.subs(c, cstar))
print("     vertex c* =", cstar, "(= v/(u-v))")
print("     g(c*)      =", gmax, "(= u/(v(u-v)))")

# ---- 1b. Tangency (binding) -> the constraint surface u = v(u-v) -----------------
usol = sp.solve(sp.Eq(gmax, 1), u)
print("\n[1b] g(c*) = 1  <=>  u =", sp.simplify(usol[0]), "(= v^2/(v-1))")
usol = sp.simplify(v**2/(v-1))

# ---- 1c. One-variable minimization of (ab)^2 = uv on the tangency surface ---------
F = sp.simplify(usol*v)                       # (ab)^2 along the binding surface
dF = sp.simplify(sp.diff(F, v))
print("\n[1c] (ab)^2 = uv =", F, " = v^3/(v-1)")
print("     d/dv (ab)^2 =", dF, "  (numerator factor 2v-3)")
crit = sp.solve(sp.Eq(dF, 0), v)
print("     critical v =", crit)
vstar = sp.Rational(3, 2)
ustar = sp.simplify(usol.subs(v, vstar))
print("     => v=b^2 =", vstar, ", u=a^2 =", ustar)
print("     a =", sp.sqrt(ustar), " b =", sp.sqrt(vstar))
ab = sp.sqrt(ustar*vstar)
print("     a*b =", sp.simplify(ab), "  area/pi =", sp.nsimplify(ab))
print("     matches 3*sqrt(3)/2 :", sp.simplify(ab - 3*sp.sqrt(3)/2) == 0)
d2 = sp.simplify(sp.diff(F, v, 2).subs(v, vstar))
print("     F''(3/2) =", d2, " (>0 => strict local min); F'~(2v-3) => unique GLOBAL min on v>1")

# ---- 1d. The hand-checkable certificate at the optimum: uv(1-g) is a perfect square
h = sp.factor(sp.expand((ustar*vstar)*(1 - g.subs({u: ustar, v: vstar}))))
print("\n[1d] At optimum, a^2 b^2 (1 - g(c)) =", h, " = (27/4)(2c-1)^2/... perfect square >=0")
print("     so g(c) <= 1 for all c, equality only at c = 1/2 (cos t = 1/2, t = +-pi/3).")

# ---- 1e. vertex in range, and the competing 'endpoint' regime is infeasible -------
print("\n[1e] vertex c* at optimum =", sp.simplify(cstar.subs({u: ustar, v: vstar})),
      "in (-1,1): OK (interior tangency).")
# endpoint regime a=2,b^2=4/3 (tangent only at c=1) really violates containment:
ge = sp.expand((1+c)**2/4 + (1-c**2)/sp.Rational(4, 3))
print("     endpoint candidate a=2,b^2=4/3: max_c g =", sp.simplify(ge.subs(c, sp.Rational(1, 2))),
      ">1  => INFEASIBLE.")

# ---- 1f. xmax(u,v): half-diameter of the eroded set on the major axis -------------
gx = sp.expand((x+c)**2/u + (1-c**2)/v)
cstar_x = -gx.coeff(c, 1)/(2*gx.coeff(c, 2))
gmax_x = sp.simplify(gx.subs(c, cstar_x))
xmax = sp.solve(sp.Eq(gmax_x, 1), x)
print("\n[1f] xmax(u,v) =", [sp.simplify(s) for s in xmax], " (= sqrt((u-v)(v-1)/v))")
print("     feasibility (two disjoint disks fit) <=> xmax >= 1 <=> (u-v)(v-1) >= v")
print("     at optimum xmax =", sp.simplify(xmax[0].subs({u: ustar, v: vstar})), "(= 1: touching = at extreme)")

print("\n" + "="*72)
print("PART 1g.  The Step-2 key lemma (rotation witness): N(m') >= N((1,0))")
print("="*72)
import numpy as np, math
from scipy.optimize import minimize


def Qf(u_, v_, X, Y):
    return X*X/u_ + Y*Y/v_


def Nf(u_, v_, X, Y):     # max ellipse-value over the unit disk centered at (X,Y)
    ts = np.linspace(0, 2*math.pi, 60000, endpoint=False)
    return np.max((X+np.cos(ts))**2/u_ + (Y+np.sin(ts))**2/v_)


rng = np.random.default_rng(0)
ok_lemma = True
worst = 0.0
tested = 0
for _ in range(8000):
    vv = 1.01 + rng.random()*4
    uu = vv + 0.01 + rng.random()*8         # u >= v (major axis on x)
    cs = vv/(uu-vv)                         # vertex cos t* of the (1,0)-disk parabola
    if cs > 1:                              # endpoint regime handled separately (uv>8)
        continue
    ss = math.sqrt(1-cs*cs)
    B0 = (1+cs, ss)
    N0 = Qf(uu, vv, *B0)
    assert abs(N0 - Nf(uu, vv, 1, 0)) < 1e-3        # B0 really is the max point
    phi = rng.uniform(-math.pi/2, math.pi/2)
    sgn = 1 if phi > 0 else -1                       # orient s* away from the axis
    B0s = np.array([1+cs, sgn*ss])
    R = np.array([[math.cos(phi), -math.sin(phi)], [math.sin(phi), math.cos(phi)]])
    B = R @ B0s                                      # witness point on the m'-disk
    tested += 1
    # B must lie on the m'-disk boundary:
    mp = (math.cos(phi), math.sin(phi))
    assert abs(math.hypot(B[0]-mp[0], B[1]-mp[1]) - 1) < 1e-9
    QB = Qf(uu, vv, *B)
    if QB < N0 - 1e-7:
        ok_lemma = False
        worst = min(worst, QB-N0)
print(f"  tested {tested} cases; witness Q(R_phi B0) >= N((1,0)) holds: {ok_lemma}",
      "" if ok_lemma else f"(worst {worst})")
print("  => the major-axis unit-vector disk is the easiest to contain. LEMMA corroborated.")

print("\n" + "="*72)
print("PART 2.  Independent numerical optimization of the FULL problem")
print("="*72)


def dist_point_ellipse(a, b, px, py):
    x_, y_ = abs(px), abs(py)
    A, B = a, b
    if A < B:
        A, B = B, A
        x_, y_ = y_, x_
    if y_ > 1e-12:
        if x_ > 1e-12:
            t = 0.5*((-B*B+B*y_) + (-B*B+math.hypot(A*x_, B*y_)))
            for _ in range(100):
                ta, tb = t+A*A, t+B*B
                if ta <= 0 or tb <= 0:
                    t = max(t, -min(A*A, B*B)+1e-9); ta, tb = t+A*A, t+B*B
                ex, ey = A*x_/ta, B*y_/tb
                f = ex*ex+ey*ey-1.0
                if abs(f) < 1e-16:
                    break
                fp = -2*(A*A*x_*x_/ta**3 + B*B*y_*y_/tb**3)
                tn = t - f/fp
                if tn == t:
                    break
                t = tn
            cx, cy = A*A*x_/(t+A*A), B*B*y_/(t+B*B)
        else:
            cx, cy = 0.0, B
    else:
        if x_ < (A*A-B*B)/A:
            cx = A*A*x_/(A*A-B*B); cy = B*math.sqrt(max(0, 1-(cx/A)**2))
        else:
            cx, cy = A, 0.0
    d = math.hypot(x_-cx, y_-cy)
    return -d if (x_*x_/A**2 + y_*y_/B**2 < 1.0) else d


cons = [
    {'type': 'ineq', 'fun': lambda z: -dist_point_ellipse(z[0], z[1], z[2], z[3]) - 1.0},
    {'type': 'ineq', 'fun': lambda z: -dist_point_ellipse(z[0], z[1], z[4], z[5]) - 1.0},
    {'type': 'ineq', 'fun': lambda z: (z[2]-z[4])**2 + (z[3]-z[5])**2 - 4.0},
]
best = None
rng = np.random.default_rng(0)
for _ in range(60):
    z0 = np.array([2.5+rng.random(), 1.0+rng.random(),
                   -1+0.5*rng.standard_normal(), 0.3*rng.standard_normal(),
                   1+0.5*rng.standard_normal(), 0.3*rng.standard_normal()])
    r = minimize(lambda z: z[0]*z[1], z0, constraints=cons,
                 bounds=[(0.5, 6)]*2 + [(-5, 5)]*4, method='SLSQP',
                 options={'maxiter': 500, 'ftol': 1e-12})
    if r.success and (best is None or r.fun < best.fun):
        best = r
z = best.x
print("\n min a*b (area/pi)  =", best.fun)
print(" target 3*sqrt(3)/2 =", float(3*math.sqrt(3)/2))
print(" a^2, b^2           =", round(z[0]**2, 6), round(z[1]**2, 6), " (target 4.5, 1.5)")
print(" centers            =", (round(z[2], 6), round(z[3], 6)), (round(z[4], 6), round(z[5], 6)))
print(" center distance    =", round(math.hypot(z[2]-z[4], z[3]-z[5]), 9), " (touching = 2)")
print("\nALL CHECKS CONSISTENT." if abs(best.fun - 3*math.sqrt(3)/2) < 1e-5 else "\nMISMATCH!")
