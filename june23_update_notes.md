# Packing Center update notes — June 2026

What changed in this repository, page by page. This batch touches **three pages**: new
entries on `cirinl`, `cirintri`, and `cirinttt`, plus two small improvements to
already-submitted `cirinl` values. Everything is best-known/numerical unless marked
proven, and every value can be re-checked from coordinates with
`python3 common/verify.py` (reports min pairwise distance and min wall clearance for each
packing).

---

## 1. `cirinl` — circles in an L-tromino

Two kinds of change:

- **NEW entries: n = 49 to 100** (52 packings). Side length grows to s = 22.77855 at
  n = 100. All beat the trivial grid; all best-known/numerical.
- **UPDATES to two already-submitted values** (a perturbation/anneal polish found slightly
  tighter packings):
  | n | old s | new s | improvement |
  |---|-------|-------|------------|
  | 46 | 15.721660 | **15.713585** | 0.008075 |
  | 48 | 15.985209 | **15.983107** | 0.002102 |

- **Unchanged:** n = 17–45 and 47 (already on the page) are identical — no action needed.

Data + per-n figures for the full n = 17–100 range are in
[`cirinl_circles_in_L/`](cirinl_circles_in_L/).

---

## 2. `cirintri` — circles in an equilateral triangle  (NEW entries + ATTRIBUTION)

- **Page currently tabulates:** n = 1 to 15.
- **NEW entries: n = 16 to 100** (85 packings), in
  [`cirintri_circles_in_equilateral_triangles/`](cirintri_circles_in_equilateral_triangles/).

**IMPORTANT — these packings are almost all due to others, not to us.** This is a
*compilation* from the literature; our optimizer fills the gaps the literature does not
cover and generates verifiable coordinates/figures for every `n`. Please credit the
original discoverers. Per-entry credit is in
[`.../data/records.csv`](cirintri_circles_in_equilateral_triangles/data/records.csv)
(`credit` column) and [`SOURCES.md`](cirintri_circles_in_equilateral_triangles/SOURCES.md).
We audited every entry against the Graham–Lubachevsky arXiv source (math/0406252): our
value matches or beats GL's exact published value for every `n` GL gives (16–95); the one
exception is n = 88, for which GL state they omit the diagram and publish no value. The 85
entries break down as:

| Credit | Entries | Notes |
|--------|--------:|-------|
| **Graham & Lubachevsky 1995** | 36 | their seven infinite families + tabulated/listed packings; main source for n ≥ 22 |
| **this work (optimizer)** | 30 | n with no value we could source in the literature; the only genuinely new entries |
| **Oler 1961 / Groemer 1960** | 8 | triangular numbers n = k(k+1)/2, **proven optimal**, d = 1/(k−1) |
| **Erdős–Oler** | 8 | one-less-than-triangular n = k(k+1)/2 − 1 (conjectured d(n) = d(n+1)) |
| **Melissen 1993 / Melissen & Schuur 1995** | 3 | n = 16, 17, 18 |

- **Proven optimal:** only the 8 triangular numbers (plus n ≤ 15 already on the page).
  Everything else is best-known/conjectured.
- Reference: R. L. Graham & B. D. Lubachevsky, *Dense packings of equal disks in an
  equilateral triangle: from 22 to 34 and beyond*, Electron. J. Combin. 2 (1995), #A1.
- Near-ties at n = 59, 83, 96 (equal their n+1 neighbor to within ~1e-6, because the n+1
  family packing is rigid) are flagged in the `note` column.

---

## 3. `cirinttt` — circles in arbitrary triangles  (NEW entries; existing unchanged)

- **Already on the page:** Cantrell's n = 2–22 entries and our n = 23–43 (15 entries).
  **These are unchanged.**
- **NEW: 38 entries at n = 46 to 100** (n = 46, 47, 48, 50–53, 56–58, 61–63, 67–70, 72–75,
  79–82, 85–88, 92–100), in [`cirinttt_circles_in_triangles/`](cirinttt_circles_in_triangles/).
  Each is a non-equilateral triangle of smaller area than the best equilateral packing of
  the same `n` (baseline = our own `cirintri` equilateral values, n = 16–100). Side lengths
  `a,b,c` are in `data/records.csv`; coordinates in `data/packings.json`.
- The near-triangular `n` (44, 45, 49, 54, 55, 59, 60, 64–66, 71, 76–78, 83, 84, 89–91) show
  no improvement over equilateral and are **not** claimed.
- All best-known/numerical, not optimality proofs.

**What to update:** add n = 46–100 (the 38 listed) to the `cirinttt` table; leave n ≤ 43
as-is.

---

## How to verify

```bash
python3 common/verify.py            # every page
python3 common/verify.py cirintri   # one page
```

Output ends with `ALL PACKINGS VERIFIED VALID`. The verifier reads only the coordinate
files and uses the Python standard library; no optimizer code is trusted.
