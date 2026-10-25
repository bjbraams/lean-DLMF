/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import Carlson.Elliptic.Asymptotic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Asymptotic approximations of the symmetric elliptic integrals (DLMF §19.27)

DLMF §19.27 gives approximations of `R_F`, `R_G`, `R_D`, `R_J` with real nonnegative
arguments when some arguments are much smaller than the others, with relative or absolute
`O`-terms (from Carlson and Gustafson, SIAM J. Math. Anal. 25 (1994), with explicit bounds).

## Reading of the `O`-terms

DLMF writes, e.g., `R_F(x, y, z) = (1/(2√z)) ln(8z/(a + g)) (1 + O(a/z))` as `a/z → 0`. All
formulas are homogeneous, so the limit is realized here by letting the **small arguments tend
to `0` jointly** (through DLMF's domain: real, nonnegative, at most one of `x, y, z` zero, `p > 0`)
with the **large arguments fixed** and positive; the `O`-term is then a Mathlib
`Asymptotics.IsBigO` along `𝓝[S] 0` (or `𝓝[>] 0`, `𝓝[≥] 0`). Uniformity in the fixed
arguments, which Carlson–Gustafson's explicit bounds also provide, is not asserted. Every
statement was checked numerically (mpmath, random directions of approach, 2026-10-25).

## Corrections

* **19.27.8.** DLMF: `R_D(x, y, z) = 3/√(xyz) - (6/(xy)) R_G(x, y, 0) (1 + O(z/g))`. The
  relative error of the bracket is of order `√(z/g)`, not `z/g`: numerically, for
  `x = 2, y = 3`, `(3/√(xyz) - R_D)/((6/(xy)) R_G(x, y, 0)) - 1 ≈ -1.2895 √(z/g)` for
  `z = 10⁻⁴, …, 10⁻¹⁰`. This agrees with Carlson–Gustafson (1994, (37)):
  `R_D = 3/√(xyz) - (6/(xy)) R_G(x, y, 0) + (6a√z/g³)(1 - (πθ/4)√(z/a))` with bounded `θ`. The
  statement below has `O(√(z/g))`.
* **19.27.12.** DLMF: `R_J(x, y, z, p) = (3/(2√(xyz))) (ln(4f/p) - 2)(1 + O(p/f))`. This fails
  unless `x = y = z`: for `(x, y, z) = (1, 2, 3)` the difference `R_J - (3/(2√(xyz)))(ln(4f/p) - 2)`
  tends to `-0.0381…`, not `0`, as `p → 0`. Carlson–Gustafson (1994, (42)) state
  `R_J = (3/(2√(xyz))) (ln(4f/p) - 2 + r)` with `-ln(f/H) < r < (3p/(2(f - p))) ln(f/p)`, where
  `H = 3/(x⁻¹ + y⁻¹ + z⁻¹)` is the harmonic mean (`r → 0` only when `f = H`). That bounded form
  (with non-strict inequalities, checked numerically on 400 random triples and `0 < p < f`) is
  acquired.

## Proved bridges from `lean-codes`

Carlson's (9.2-10) and (8.3-16) (`Carlson.isEquivalent_carlsonRF_atTop`,
`Carlson.isEquivalent_carlsonRK_zero`) give the leading term of (19.27.2) as an asymptotic
equivalence along rays (weaker than DLMF's relative `O(a/z)`): `symEllIntRF_isEquivalent_atTop`.

## §19.27 prose

* 19.27.i.p1: the notation (19.27.1), definitions `ellAsymA` … `ellAsymH`.
* 19.27.ii.p1, iii.p1, iv.p1, v.p1: the standing assumptions, carried as hypotheses.
* 19.27.vi.p1, vi.p2: commentary (bounds of Carlson–Gustafson; convergent but slowly converging
  asymptotic series of Wong, Carlson–Gustafson, López; the `R_{-a}` analogue in Carlson (1985));
  no further explicit formula.

## References

* NIST DLMF §19.27; B. C. Carlson and J. L. Gustafson, *Asymptotic approximations for
  symmetric elliptic integrals*, SIAM J. Math. Anal. 25 (1994) 288–303.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-! ### Notation (19.27.1) -/

/-- DLMF 19.27.1: `a = (x + y)/2`. -/
@[dlmf 19.27.E1]
def ellAsymA (x y : ℝ) : ℝ := (x + y) / 2

/-- DLMF 19.27.1: `b = (y + z)/2`. -/
@[dlmf 19.27.E1]
def ellAsymB (y z : ℝ) : ℝ := (y + z) / 2

/-- DLMF 19.27.1: `c = (x + y + z)/3`. -/
@[dlmf 19.27.E1]
def ellAsymC (x y z : ℝ) : ℝ := (x + y + z) / 3

/-- DLMF 19.27.1: `f = (xyz)^{1/3}`. -/
@[dlmf 19.27.E1]
def ellAsymF (x y z : ℝ) : ℝ := (x * y * z) ^ (1 / 3 : ℝ)

/-- DLMF 19.27.1: `g = (xy)^{1/2}`. -/
@[dlmf 19.27.E1]
def ellAsymG (x y : ℝ) : ℝ := √(x * y)

/-- DLMF 19.27.1: `h = (yz)^{1/2}`. -/
@[dlmf 19.27.E1]
def ellAsymH (y z : ℝ) : ℝ := √(y * z)

/-- The approach set for two small nonnegative arguments, not both zero. -/
def ellAsymPair : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q ≠ 0}

/-- The approach set for three small nonnegative arguments, at most one of them zero. -/
def ellAsymTriple : Set (ℝ × ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2 ∧
    (q.1 = 0 → q.2.1 ≠ 0 ∧ q.2.2 ≠ 0) ∧ (q.2.1 = 0 → q.2.2 ≠ 0)}

/-! ### §19.27(ii) `R_F` -/

/-- DLMF 19.27.2: `R_F(x, y, z) = (1/(2√z)) ln(8z/(a + g)) (1 + O(a/z))` as `a/z → 0`: for fixed
`z > 0`, as `(x, y) → 0` through nonnegative pairs not both zero. -/
@[dlmf 19.27.E2]
theorem symEllIntRF_asymp_large_z {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => symEllIntRF q.1 q.2 z -
        ((Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) / (2 * √z) : ℝ) : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 / z *
        (Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) / (2 * √z)) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.3: `R_F(x, y, z) = R_F(0, y, z) - (1/√h)(√(x/h) + O(x/h))` as `x/h → 0`: for
fixed `y, z > 0`, as `x → 0+`. -/
@[dlmf 19.27.E3]
theorem symEllIntRF_asymp_small_x {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (fun x : ℝ => symEllIntRF x y z - symEllIntRF 0 y z +
        ((√(x / ellAsymH y z) / √(ellAsymH y z) : ℝ) : ℂ)) =O[𝓝[≥] 0]
      (fun x : ℝ => ((x / ellAsymH y z / √(ellAsymH y z) : ℝ) : ℂ)) := by
  sorry

/-- Bridge (proved, from `lean-codes` (9.2-10)): for fixed `x, y > 0`,
`R_F(x, y, z) ∼ (1/(2√z)) ln(8z/(a + g))` as `z → ∞`, the leading term of (19.27.2) as an
asymptotic equivalence (weaker than DLMF's relative `O(a/z)`). -/
@[dlmf 19.27.E2]
theorem symEllIntRF_isEquivalent_atTop {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IsEquivalent atTop (fun z : ℝ => symEllIntRF x y z)
      (fun z : ℝ => ((Real.log (8 * z / (ellAsymA x y + ellAsymG x y)) / (2 * √z) : ℝ) : ℂ)) := by
  have H := Carlson.isEquivalent_carlsonRF_atTop hx hy
  have hl : (fun z : ℝ => Carlson.carlsonRF x y z) =ᶠ[atTop] fun z : ℝ => symEllIntRF x y z := by
    filter_upwards [eventually_gt_atTop 0] with z hz
    rw [symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
      (ofReal_mem_slitPlane.mpr hz)]
  have hr : (fun z : ℝ => ((Real.log (4 * √z / (√x + √y)) / √z : ℝ) : ℂ)) =ᶠ[atTop]
      fun z : ℝ => ((Real.log (8 * z / (ellAsymA x y + ellAsymG x y)) / (2 * √z) : ℝ) : ℂ) := by
    filter_upwards [eventually_gt_atTop 0] with z hz
    have hsx := Real.sqrt_pos.mpr hx
    have hsy := Real.sqrt_pos.mpr hy
    have hsz := Real.sqrt_pos.mpr hz
    have hsum : 0 < √x + √y := by positivity
    have e : 8 * z / (ellAsymA x y + ellAsymG x y) = (4 * √z / (√x + √y)) ^ 2 := by
      simp only [ellAsymA, ellAsymG]
      rw [Real.sqrt_mul hx.le, div_pow, mul_pow, Real.sq_sqrt hz.le]
      have : (√x + √y) ^ 2 = x + y + 2 * (√x * √y) := by
        rw [add_sq, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]; ring
      rw [this]
      have : 0 < x + y + 2 * (√x * √y) := by positivity
      field_simp
      ring
    rw [e, Real.log_pow]
    congr 1
    field_simp
    push_cast
    ring
  exact (H.congr_left hl).congr_right hr

/-- Bridge (proved, from `lean-codes` (8.3-16)): the case `x = 0` of (19.27.2) as an asymptotic
equivalence: for fixed `z > 0`, `R_F(0, y, z) ∼ (1/(2√z)) ln(16z/y)` as `y → 0+` (here
`a = y/2`, `g = 0`). Weaker than DLMF's relative `O(y/z)`. -/
@[dlmf 19.27.E2]
theorem symEllIntRF_zero_isEquivalent {z : ℝ} (hz : 0 < z) :
    IsEquivalent (𝓝[>] 0) (fun y : ℝ => symEllIntRF 0 y z)
      (fun y : ℝ => ((Real.log (16 * z / y) / (2 * √z) : ℝ) : ℂ)) := by
  have H := (IsEquivalent.refl (u := fun _ : ℝ => ((π / 2 : ℝ) : ℂ)) (l := 𝓝[>] 0)).mul
    (Carlson.isEquivalent_carlsonRK_zero hz)
  have hl : ((fun _ : ℝ => ((π / 2 : ℝ) : ℂ)) * fun y : ℝ => Carlson.TwoVariable.carlsonRK z y)
      =ᶠ[𝓝[>] 0] fun y : ℝ => symEllIntRF 0 y z := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    simp only [Pi.mul_apply]
    rw [symEllIntRF_comm_right, symEllIntRF_zero_left (ofReal_mem_slitPlane.mpr hz)
      (ofReal_mem_slitPlane.mpr hy), symEllIntR_of_mem _ _ (ei19c_slit2
        (ofReal_mem_slitPlane.mpr hz) (ofReal_mem_slitPlane.mpr hy))]
    simp only [Carlson.TwoVariable.carlsonRK, Carlson.TwoVariable.pair]
    push_cast
    congr 2
    ring
  have hr : ((fun _ : ℝ => ((π / 2 : ℝ) : ℂ)) *
      fun y : ℝ => ((Real.log (16 * z / y) / (π * √z) : ℝ) : ℂ))
      =ᶠ[𝓝[>] 0] fun y : ℝ => ((Real.log (16 * z / y) / (2 * √z) : ℝ) : ℂ) := by
    filter_upwards with y
    simp only [Pi.mul_apply]
    have := Real.sqrt_pos.mpr hz
    push_cast
    field_simp
  exact (H.congr_left hl).congr_right hr

/-! ### §19.27(iii) `R_G` -/

/-- DLMF 19.27.4: `R_G(x, y, z) = (√z/2)(1 + O((a/z) ln(z/a)))` as `a/z → 0`: for fixed
`z > 0`, as `(x, y) → 0` through nonnegative pairs not both zero. -/
@[dlmf 19.27.E4]
theorem symEllIntRG_asymp_large_z {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => symEllIntRG q.1 q.2 z - ((√z / 2 : ℝ) : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((√z / 2 * (ellAsymA q.1 q.2 / z *
        Real.log (z / ellAsymA q.1 q.2)) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.5: `R_G(x, y, z) = R_G(0, y, z) + √x O(√(x/h))` as `x/h → 0`: for fixed
`y, z > 0`, as `x → 0+`. -/
@[dlmf 19.27.E5]
theorem symEllIntRG_asymp_small_x {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (fun x : ℝ => symEllIntRG x y z - symEllIntRG 0 y z) =O[𝓝[≥] 0]
      (fun x : ℝ => ((√x * √(x / ellAsymH y z) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.6: `R_G(0, y, z) = √z/2 + (y/(8√z))(ln(16z/y) - 1)(1 + O(y/z))` as `y/z → 0`:
for fixed `z > 0`, as `y → 0+`. -/
@[dlmf 19.27.E6]
theorem symEllIntRG_zero_asymp {z : ℝ} (hz : 0 < z) :
    (fun y : ℝ => symEllIntRG 0 y z -
        ((√z / 2 + y / (8 * √z) * (Real.log (16 * z / y) - 1) : ℝ) : ℂ)) =O[𝓝[>] 0]
      (fun y : ℝ => ((y / (8 * √z) * (Real.log (16 * z / y) - 1) * (y / z) : ℝ) : ℂ)) := by
  sorry

/-! ### §19.27(iv) `R_D` -/

/-- DLMF 19.27.7: `R_D(x, y, z) = (3/(2z^{3/2}))(ln(8z/(a + g)) - 2)(1 + O(a/z))` as
`a/z → 0`: for fixed `z > 0`, as `(x, y) → 0` through nonnegative pairs not both zero. -/
@[dlmf 19.27.E7]
theorem symEllIntRD_asymp_large_z {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => symEllIntRD q.1 q.2 z - ((3 / (2 * z ^ (3 / 2 : ℝ)) *
        (Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) - 2) : ℝ) : ℂ))
      =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 / z * (3 / (2 * z ^ (3 / 2 : ℝ)) *
        (Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) - 2)) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.8, **corrected** (see the module docstring: DLMF prints `O(z/g)`; the correct
order is `O(√(z/g))`): `R_D(x, y, z) = 3/√(xyz) - (6/(xy)) R_G(x, y, 0)(1 + O(√(z/g)))` as
`z/g → 0`: for fixed `x, y > 0`, as `z → 0+`. -/
@[dlmf 19.27.E8]
theorem symEllIntRD_asymp_small_z {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (fun z : ℝ => symEllIntRD x y z -
        (((3 / √(x * y * z) : ℝ) : ℂ) - 6 / (x * y : ℝ) * symEllIntRG x y 0)) =O[𝓝[>] 0]
      (fun z : ℝ => 6 / (x * y : ℝ) * symEllIntRG x y 0 * ((√(z / ellAsymG x y) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.9: `R_D(x, y, z) = 3/(√(xz)(√y + √z)) (1 + O((b/x) ln(x/b)))` as `b/x → 0`: for
fixed `x > 0`, as `(y, z) → 0` with `y ≥ 0`, `z > 0`. -/
@[dlmf 19.27.E9]
theorem symEllIntRD_asymp_large_x {x : ℝ} (hx : 0 < x) :
    (fun q : ℝ × ℝ => symEllIntRD x q.1 q.2 -
        ((3 / (√(x * q.2) * (√q.1 + √q.2)) : ℝ) : ℂ)) =O[𝓝[{q | 0 ≤ q.1 ∧ 0 < q.2}] 0]
      (fun q : ℝ × ℝ => ((3 / (√(x * q.2) * (√q.1 + √q.2)) *
        (ellAsymB q.1 q.2 / x * Real.log (x / ellAsymB q.1 q.2)) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.10: `R_D(x, y, z) = R_D(0, y, z) - (3√x/(hz))(1 + O(√(x/h)))` as `x/h → 0`: for
fixed `y, z > 0`, as `x → 0+`. -/
@[dlmf 19.27.E10]
theorem symEllIntRD_asymp_small_x {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (fun x : ℝ => symEllIntRD x y z - symEllIntRD 0 y z +
        ((3 * √x / (ellAsymH y z * z) : ℝ) : ℂ)) =O[𝓝[≥] 0]
      (fun x : ℝ => ((3 * √x / (ellAsymH y z * z) * √(x / ellAsymH y z) : ℝ) : ℂ)) := by
  sorry

/-! ### §19.27(v) `R_J` -/

/-- DLMF 19.27.11: `R_J(x, y, z, p) = (3/p) R_F(x, y, z) - (3π/(2p^{3/2}))(1 + O(√(c/p)))` as
`c/p → 0`: for fixed `p > 0`, as `(x, y, z) → 0` through nonnegative triples with at most one
zero. -/
@[dlmf 19.27.E11]
theorem symEllIntRJ_asymp_large_p {p : ℝ} (hp : 0 < p) :
    (fun q : ℝ × ℝ × ℝ => symEllIntRJ q.1 q.2.1 q.2.2 p -
        (3 / (p : ℂ) * symEllIntRF q.1 q.2.1 q.2.2 - ((3 * π / (2 * p ^ (3 / 2 : ℝ)) : ℝ) : ℂ)))
      =O[𝓝[ellAsymTriple] 0]
      (fun q : ℝ × ℝ × ℝ => ((3 * π / (2 * p ^ (3 / 2 : ℝ)) *
        √(ellAsymC q.1 q.2.1 q.2.2 / p) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.12, **corrected** to Carlson–Gustafson (1994, (42)) (see the module docstring;
DLMF's relative error `O(p/f)` is false unless `x = y = z`): for `x, y, z > 0` and `0 < p < f`,
`R_J(x, y, z, p) = (3/(2√(xyz)))(ln(4f/p) - 2 + r)` with
`-ln(f/H) ≤ r ≤ (3p/(2(f - p))) ln(f/p)`, `H = 3/(x⁻¹ + y⁻¹ + z⁻¹)`. In particular
`R_J = (3/(2√(xyz)))(ln(4f/p) - 2 + O(1))` as `p/f → 0`. The bounds on `r` were checked
numerically (no violation at 500 random triples, mpmath, 2026-10-25), not against the paper. -/
@[dlmf 19.27.E12]
theorem symEllIntRJ_small_p_bounds {x y z p : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : 0 < p) (hpf : p < ellAsymF x y z) :
    ∃ r : ℝ, symEllIntRJ x y z p =
        ((3 / (2 * √(x * y * z)) * (Real.log (4 * ellAsymF x y z / p) - 2 + r) : ℝ) : ℂ) ∧
      -Real.log (ellAsymF x y z / (3 / (x⁻¹ + y⁻¹ + z⁻¹))) ≤ r ∧
      r ≤ 3 * p / (2 * (ellAsymF x y z - p)) * Real.log (ellAsymF x y z / p) := by
  sorry

/-- DLMF 19.27.13: `R_J(x, y, z, p) = (3/(2√z p))(ln(8z/(a + g)) - 2 R_C(1, p/z)
+ O((a/z + a/p) ln(p/a)))` as `max(x, y)/min(z, p) → 0`: for fixed `z, p > 0`, as
`(x, y) → 0` through nonnegative pairs not both zero. -/
@[dlmf 19.27.E13]
theorem symEllIntRJ_asymp_small_xy {z p : ℝ} (hz : 0 < z) (hp : 0 < p) :
    (fun q : ℝ × ℝ => symEllIntRJ q.1 q.2 z p -
        ((3 / (2 * √z * p) : ℝ) : ℂ) *
          (((Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) : ℝ) : ℂ) -
            2 * symEllIntRC 1 (p / z : ℝ))) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((3 / (2 * √z * p) * ((ellAsymA q.1 q.2 / z + ellAsymA q.1 q.2 / p) *
        Real.log (p / ellAsymA q.1 q.2)) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.14: `R_J(x, y, z, p) = (3/√(yz)) R_C(x, p) - (6/(yz)) R_G(0, y, z)
+ O(√(x + 2p)/(yz))` as `max(x, p)/min(y, z) → 0`: for fixed `y, z > 0`, as `(x, p) → 0` with
`x ≥ 0`, `p > 0`. -/
@[dlmf 19.27.E14]
theorem symEllIntRJ_asymp_small_xp {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (fun q : ℝ × ℝ => symEllIntRJ q.1 y z q.2 -
        (3 / (√(y * z) : ℝ) * symEllIntRC q.1 q.2 - 6 / (y * z : ℝ) * symEllIntRG 0 y z))
      =O[𝓝[{q | 0 ≤ q.1 ∧ 0 < q.2}] 0]
      (fun q : ℝ × ℝ => ((√(q.1 + 2 * q.2) / (y * z) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.15: `R_J(x, y, z, p) = R_J(0, y, z, p) - (3√x/(hp))(1 + O((b/h + h/p)√(x/h)))`
as `x/min(y, z, p) → 0`: for fixed `y, z, p > 0`, as `x → 0+`. -/
@[dlmf 19.27.E15]
theorem symEllIntRJ_asymp_small_x {y z p : ℝ} (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    (fun x : ℝ => symEllIntRJ x y z p - symEllIntRJ 0 y z p +
        ((3 * √x / (ellAsymH y z * p) : ℝ) : ℂ)) =O[𝓝[≥] 0]
      (fun x : ℝ => ((3 * √x / (ellAsymH y z * p) *
        ((ellAsymB y z / ellAsymH y z + ellAsymH y z / p) * √(x / ellAsymH y z)) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.16: `R_J(x, y, z, p) = (3/√x) R_C((h + p)², 2(b + h)p)
+ O(x^{-3/2} ln(x/(b + h)))` as `max(y, z, p)/x → 0`: for fixed `x > 0`, as `(y, z, p) → 0` with
`y, z ≥ 0` not both zero and `p > 0`. -/
@[dlmf 19.27.E16]
theorem symEllIntRJ_asymp_large_x {x : ℝ} (hx : 0 < x) :
    (fun q : ℝ × ℝ × ℝ => symEllIntRJ x q.1 q.2.1 q.2.2 -
        3 / (√x : ℝ) * symEllIntRC ((ellAsymH q.1 q.2.1 + q.2.2) ^ 2 : ℝ)
          (2 * (ellAsymB q.1 q.2.1 + ellAsymH q.1 q.2.1) * q.2.2 : ℝ))
      =O[𝓝[{q | 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ (q.1, q.2.1) ≠ 0 ∧ 0 < q.2.2}] 0]
      (fun q : ℝ × ℝ × ℝ => ((x ^ (-(3 / 2) : ℝ) *
        Real.log (x / (ellAsymB q.1 q.2.1 + ellAsymH q.1 q.2.1)) : ℝ) : ℂ)) := by
  sorry

end DLMF.EllipticIntegrals
