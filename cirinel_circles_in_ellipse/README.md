# 2 unit circles in the smallest ellipse (`cirinel`, n = 2)

A complete **proof** — not a numerical record — that the smallest-area ellipse containing two
interior-disjoint unit circles has area exactly

$$A \;=\; \frac{3\sqrt3}{2}\,\pi \;\approx\; 8.1621,$$

attained by $\frac{x^2}{9/2}+\frac{y^2}{3/2}\le 1$ with the two circles centered at $(\pm1,0)$,
touching at the origin (each circle internally tangent to the ellipse at two points
$(\pm\tfrac32,\pm\tfrac{\sqrt3}{2})$).

This value was found numerically by James Buddenhagen (2004) and listed on
[Erich Friedman's Packing Center](https://erich-friedman.github.io/packing/cirinel/), page
[`cirinel`](https://erich-friedman.github.io/packing/cirinel/), but does not appear to have been
proved before. The result here is proved two ways: a self-contained hand proof, and a
**formally verified Lean 4 development** (kernel-checked, zero `sorry`, only the three standard
mathlib axioms).

## Files

| File | What it is |
|------|------------|
| [`proof_ellipse_n2.pdf`](proof_ellipse_n2.pdf) | The hand proof (start here). Four steps: normalize → reduce two disks to the single disk at $(1,0)$ → one-point + AM–GM lower bound → perfect-square construction. |
| [`companion.pdf`](companion.pdf) | The same proof, plus a closing section mapping each step to the corresponding Lean lemma. |
| [`statement_explained.pdf`](statement_explained.pdf) | Short note: the headline Lean statement, why it needed proving, and what a reader must take on trust. |
| [`AUDIT_THIS.md`](AUDIT_THIS.md) | Step-by-step checklist for convincing yourself the *statement* is the right theorem. |
| [`verify.py`](verify.py) | Independent exact-arithmetic (sympy) certificate of every algebraic identity, plus a numerical re-optimization of the full free problem. |
| [`lean/`](lean/) | The Lean 4 + mathlib development. |
| `*.tex` | LaTeX sources for the three PDFs. |

## The proof in four steps

1. **Normalization.** A rigid motion makes the ellipse axis-aligned and origin-centered,
   $x^2/u+y^2/v\le1$ with $u=a^2\ge v=b^2$; area $=\pi\sqrt{uv}$.
2. **Reduction (the one geometric step).** For a fixed such ellipse, two interior-disjoint unit
   disks fit **iff** the single unit disk centered at $(1,0)$ fits. (Convexity and double symmetry
   of the admissible-center set force a unit-vector center to fit; and among unit vectors the
   major-axis one $(1,0)$ is the easiest to contain, because the ellipse is widest there.)
3. **Lower bound.** The disk at $(1,0)$ contains the point $(\tfrac32,\tfrac{\sqrt3}{2})$, giving
   $9/u+3/v\le4$; with $X=9/u,\,Y=3/v$, AM–GM gives $XY\le4$, i.e. $uv\ge27/4$, so
   $A=\pi\sqrt{uv}\ge\tfrac{3\sqrt3}{2}\pi$, with equality only at $u=9/2,\,v=3/2$.
4. **Construction.** That ellipse does hold two disjoint unit disks: a one-line perfect square
   $\tfrac{27}{4}(1-g)=3(c-\tfrac12)^2\ge0$.

## Verifying

**The arithmetic certificate** (independent of the proof and the Lean):

```bash
python3 verify.py        # needs sympy, numpy, scipy
```

It re-derives every identity in exact arithmetic (the AM–GM/lower-bound algebra, the tangency
perfect square, the Step-2 lemma corroborated over thousands of cases) and runs an independent
multistart optimization of the full free problem, which returns the stated optimum. Output ends
with `ALL CHECKS CONSISTENT.`

**The formal proof.** Pinned to Lean 4.31.0 (`lean/lean-toolchain`) with the matching mathlib
(`lean/lake-manifest.json`). The multi-GB compiled mathlib cache is intentionally not committed; to
build:

```bash
cd lean
lake exe cache get      # fetch mathlib at the pinned revision
lake build
```

To inspect what was proved without a full build, the decisive check is on the two capstone theorems:

```lean
#print axioms Ellipse.area_toReal_ge_of_feasibleGen   -- the lower bound, fully general ellipse
#print axioms Ellipse.isLeast_minArea                  -- "this IS the minimum", in mathlib's vocabulary
-- both report exactly [propext, Classical.choice, Quot.sound], and no sorryAx
```

`Ellipse.feasible_optimal` proves the optimum is attained (so the bound is not vacuous). The
development covers an **arbitrary positive-definite ellipse** (any tilt, any center) via a
kernel-checked rigid-motion reduction, with the genuine Lebesgue area (`MeasureTheory.volume`) and
literal interior-disjointness. See `AUDIT_THIS.md` for the full trust surface.

## Notes

- The hand proof and the Lean reach the same theorem by slightly different routes on two internal
  steps (a cone-restricted rotation identity in Step 2, and a sum-of-squares in place of AM–GM in
  Step 3); both are noted in `companion.pdf`. Neither affects the stated result.
