# Sources — Equal unit circles in the smallest equilateral triangle

This file documents every source actually consulted for the best-known
maximum–minimum center distance `d(n)` (equivalently, smallest equilateral
triangle side `s` holding `n` unit circles), with exact URLs, the range of
`n` each source covers, the conversion formula, and the proven-vs-best-known
distinction. **The packings are NOT original to this compilation** — they are
due to Graham & Lubachevsky, Melissen, Oler/Groemer, Erdős, Milano, and
Melissen & Schuur, as credited below.

## Conversion formula and conventions

Two equivalent quantities are used in the literature:

- **`d(n)`** (Graham–Lubachevsky convention): the minimum center-to-center
  distance among `n` points, measured in units of the side of the **smallest
  equilateral triangle that contains all the disk centers** (the "inner"
  triangle through the outermost centers). GL note `d(n)·L(n) = 1`, where
  `L(n)` is that inner-triangle side measured in disk-**diameter** units.
  This is identical to "the max–min center distance in a unit-side (inner)
  triangle." (GL paper, p. ~5: *"This number is the disk diameter d(n) which
  is measured in units equal to the side of the smallest equilateral triangle
  that contains the centers of all disks."*)

- **`s`** (Friedman convention): the side of the smallest equilateral
  triangle (the **container**) that holds `n` circles of **unit radius**.

The exact relationship (verified, see below) is:

```
s = 2 / d(n) + 2*sqrt(3)        area = (sqrt(3)/4) * s^2
```

Equivalently `d(n) = 2 / (s - 2*sqrt(3))`. This matches the repo's stated
formula. The `2*sqrt(3)` term is the outward offset from the inner
center-triangle to the container (one inradius-spacing per side for radius-1
circles); the `2/d` term converts the inner side from disk-diameter units
(diameter 2) to radius-1 units.

**Validation performed** (`validate.py`, light only — no optimizer):
Converting GL's published 15-digit `d(n)` for n = 4, 8, 11, 12, 13 via the
formula reproduces Friedman's exact closed-form side lengths
(e.g. n=8: `2+2√3+(2/3)√33`) to **machine precision (|Δs| ≈ 1e-15)**. The
triangular-number proven values `d(Δ(k)) = 1/(k-1)` and the explicit class
formulas `d(4Δ(k)) = 1/(2k-2+√3)`, `d(2Δ(k+1)+2Δ(k)-1) = 1/(2k-1+√3)`
reproduce the corresponding tabulated GL values (n=24,40,60 and n=17,31,49)
exactly. The two conventions are therefore fully reconciled.

---

## Source 1 — Graham & Lubachevsky 1995  (PRIMARY, most complete numeric source)

- **Citation:** R. L. Graham and B. D. Lubachevsky, *"Dense packings of equal
  disks in an equilateral triangle: from 22 to 34 and beyond,"* The Electronic
  Journal of Combinatorics **2** (1995), #A1. AT&T Bell Laboratories.
  Submitted Aug 11 1994; accepted Dec 7 1994. DOI: 10.37236/1223.
- **URLs actually fetched:**
  - Abstract / article landing:
    `https://www.combinatorics.org/ojs/index.php/eljc/article/view/v2i1a1`
  - **PDF (open access, the file used):**
    `https://www.combinatorics.org/ojs/index.php/eljc/article/download/v2i1a1/pdf/`
    (saved locally as `gl1995.pdf`; text extracted to `gl1995.txt` via
    `pdftotext -layout`.)
- **Coverage / what was extracted:**
  - Best ("a") packings for **n = 22–34** (the paper's focus), given as 15-digit
    `d(n)` next to each figure. Extracted: 22,23,24,25,26,29,30,31,32,33,34.
    (GL ran only a few runs for 27,28,35,36 — see below.)
  - Explicit closed-form infinite classes:
    - Triangular `Δ(k)=k(k+1)/2`: `L(Δ(k)) = k-1`, so `d(Δ(k)) = 1/(k-1)`
      (these are **proven** optimal; also conjectured `d(Δ(k)-1)=d(Δ(k))`).
    - `4Δ(k)`: `d = 1/(2k-2+√3)`  (n = 4, 24, 40, 60, 84, 112, …).
    - `2Δ(k+1)+2Δ(k)-1`: `d = 1/(2k-1+√3)` (n = 7, 17, 31, 49, 71, …).
    - Plus four further conjectured classes (`Δ(2k)+1`, `Δ(2k+1)+1`,
      `Δ(k+2)-2`, `Δ(2k+3)-3`, `Δ(3k+1)+2`).
  - Selected larger best packings with 15-digit `d(n)`: n = 16, 37, 40, 46,
    49, 56, 60, 67, 79 (d=0.0871159038791759), 106 (0.0742982999063026),
    121 (0.0691630188894699), 254 (0.0467170396481042).
- **Proven vs best-known per GL:** GL state (their §"on rigor") that they
  believe properties (I) configuration validity and (II) rigidity, and *hope*
  (III) optimal ranking holds for the **a-packings**, i.e. the a-packings are
  **conjectured optimal, not proven**, except where they coincide with the
  proven triangular-number class. GL explicitly say a better packing turning
  up would not astound them for lower-ranked packings.
- **Caveat:** The PDF is figure-heavy; `pdftotext` scrambles multi-column
  layout. Values were taken from the value-line that immediately follows each
  identified figure label line (e.g. "t22a" → next line `0.179396908611866`),
  and cross-checked against the closed-form class formulas where applicable
  (all matched). The n=18 ("t18a", attributed to Melissen [M1]) and n=27
  values were **not** cleanly recoverable from the OCR text and are therefore
  **omitted** rather than guessed.

## Source 2 — Erich Friedman, Packing Center: "Circles in Triangles"

- **URL fetched:** `https://erich-friedman.github.io/packing/cirintri/`
  (page dated 7/19/02). Reached from index `https://erich-friedman.github.io/packing/`.
- **Coverage:** **n = 1–15 only.** Tabulates the container side `s` directly
  for unit circles (same convention as `s` above) and gives a closed form for
  triangular cases. Per-`n` attribution shown on the page:
  - n1,2: Trivial. n4,5: Milano 1987. n6,10,15: Oler/Groemer 1961 (triangular).
    n7,8,9,11,13: Melissen 1993. n12: Melissen 1994. n13: "found by" Melissen.
    n14: "found by" Erdős/Oler 1961. n15: Erdős/Groemer 1961.
- **Use here:** Friedman's exact closed-form `s` values supply the **proven**
  small-`n` entries (n=1–15) and served as the cross-check for the conversion
  formula. This is the page the user wants to expand.

## Source 3 — Wikipedia, "Circle packing in an equilateral triangle"

- **URL fetched:** `https://en.wikipedia.org/wiki/Circle_packing_in_an_equilateral_triangle`
- **Coverage:** Same n=1–15 table as Friedman (identical closed-form sides),
  with explicit proven-status statement and references.
- **Key statements used:**
  - **Proven optimal "for n ≤ 15, and for any triangular number of circles."**
  - Conjectured (not proven) solutions known up to n=34 plus conjectured
    families (37,40,42,43,46,49,…).
  - Attribution: Melissen 1993 (*Amer. Math. Monthly*) for the small-n table;
    Melissen & Schuur 1995 for n=16,17,18; Graham & Lubachevsky 1995 for
    "22 to 34 and beyond"; Erdős–Oler / Oler 1961 conjecture, "true for n ≤ 15"
    (Payan 1997). Related covering problem: Nurmela 2000.

## Source 4 (checked, NEGATIVE result) — Packomania (Eckard Specht)

- **URLs fetched:** `http://www.packomania.com/` and `https://www.packomania.com/`.
  (The Magdeburg mirror `http://hydra.nat.uni-magdeburg.de/packing/` timed out.)
- **Finding:** Packomania does **NOT** maintain an equilateral-triangle table.
  Its container types are: square, circle, **isosceles right triangle**
  (`crt/crt.html`), semicircle, circular quadrant, rectangles (1×0.1–1×0.8 and
  variable aspect), regular **polygons pentagon through heptadecagon**
  (`cpt`…`ced`), plus sphere/hypersphere problems. There is no equilateral
  triangle container (the only triangle is the *right* isosceles one).
- **Consequence:** The task premise that Packomania is the most complete modern
  source for *this* shape is **incorrect**. For equal circles in an equilateral
  triangle, **Graham–Lubachevsky 1995 is the most complete single source**, and
  Friedman/Wikipedia/Melissen supply the proven small-n closed forms.

---

## Original-discoverer credits referenced (full citations)

- **R. L. Graham, B. D. Lubachevsky (1995)** — EJC 2 #A1 (see Source 1).
- **H. Melissen (1993)** — "Densest packings of congruent circles in an
  equilateral triangle," *American Mathematical Monthly* 100, 916–925.
- **H. Melissen, P. C. Schuur (1995)** — packing 16, 17, 18 circles in an
  equilateral triangle (cited by GL as [MS] and by Wikipedia).
- **N. Oler (1961)** / **H. Groemer (1960)** — triangular-number optimality and
  the Erdős–Oler conjecture `d(Δ(k)-1)=d(Δ(k))` (Oler, *Canad. Math. Bull.* 4).
- **Milano (1987)** — n=4,5 optimality (per Friedman).
- **Erdős–Oler** — n=14 configuration; conjecture proven for n≤15 (**Payan 1997**).
- **K. J. Nurmela (2000)** — related minimal-radius *covering* problem (not packing).

## Honest caveats before publishing

1. **Proven vs best-known.** Only **n ≤ 15** and **all triangular numbers
   Δ(k)=k(k+1)/2** (n = 3,6,10,15,21,28,36,45,55,…) are *proven* optimal.
   Everything for n=16,17 and n≥22 in this dataset is **best-known /
   conjectured optimal** (chiefly from GL), NOT proven.
2. **Do not claim authorship.** These packings are due to the cited authors.
   GL 1995 is the source for the bulk of n≥22; the small-n closed forms are
   Melissen/Oler/Groemer/Milano/Erdős.
3. **Gaps left intentionally:** n=18, 27 (and n=19,20,27,35,… generally) are
   omitted because no clean sourced numeric value was recoverable here. Better
   a small honest table than fabricated values. n=18's value exists in GL
   (attributed to Melissen [M1]) but was not cleanly OCR-extractable.
4. **`d(n)` numeric precision** is GL's 15-significant-digit figures; for
   triangular n and the two explicit classes the values are exact closed forms.
