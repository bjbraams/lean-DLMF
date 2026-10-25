/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.EllipticIntegrals.Inequalities
public import Carlson.Elliptic.CapacityBound
public import Carlson.Mean.Bounds
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Inequalities for the symmetric elliptic integrals (DLMF §19.24)

Inequalities for the complete integrals (§19.24(i)) and the incomplete integrals (§19.24(ii)).
All variables are real and positive (or nonnegative where DLMF says so); on such arguments the
symmetric integrals of `DLMF.EllipticIntegrals` are real, and the inequalities are stated for
their real parts (`symEllIntRF_ofReal_im` etc. record that the imaginary parts vanish).

* (19.24.1)–(19.24.4): bounds for `R_F(0, y, z)`, `R_G(0, y, z)`, `R_G(0, y², z²)` and
  `R_J(0, y, z, p)`; the condition `y ≤ z` in (19.24.1)–(19.24.2) only identifies the smaller
  variable (19.24.i.p1). `R_D(0, y, z)` is the case `p = z` of (19.24.4) (19.24.i.p2).
* (19.24.5)–(19.24.6): the AGM bounds `1/aₙ ≤ (2/π) R_F(0, a₀², g₀²) ≤ 1/gₙ`.
* (19.24.7): the perimeter of an ellipse `L(a, b) = 8 R_G(0, a², b²)` (`ellipsePerimeter` of
  §19.9(i)); the approximations of §19.9(i) then apply (19.24.i.p4).
* (19.24.8)–(19.24.9): strict product and sum bounds for `R_F(x, y, 0)`, `R_G(x, y, 0)` and
  Neuman's bounds for `R_G/R_F` through the first AGM step.
* (19.24.10)–(19.24.12): bounds for `R_F`, `R_J`, `R_G` by elementary means (special cases of
  Carlson (1966), Theorems 2 and 3; "all variables are positive", 19.24.ii.p1); the cases
  `R_C`, `R_D` are included (19.24.Px1.p1).
* (19.24.13)–(19.24.15): Neuman's bounds `R_a R_{-a} > 1`, `R_a + R_{-a} > 2`, their special
  case `R_F R_G > 1`, `R_F + R_G > 2`, and `R_C(x, (y+z)/2) ≤ R_F(x, y, z) ≤ R_C(x, √(yz))`.

The lower bound in (19.24.10) is proved from `lean-codes`' capacity bound
`Carlson.inv_dupMean_le_carlsonRF_sq` (Carlson 1966, Theorem 3).

## References

* NIST DLMF §19.24.
* B. C. Carlson, *Some inequalities for hypergeometric functions*, Proc. AMS 17 (1966);
  formalized in `lean-codes` (`Carlson.Mean.*`, `Carlson.Elliptic.CapacityBound`).
* E. Neuman, *Bounds for symmetric elliptic integrals*, J. Approx. Theory 122 (2003).
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory
open scoped Real

namespace DLMF.EllipticIntegrals

/-! ### Reality on nonnegative arguments -/

theorem ei19d_ofReal_add_cpow_half {t r : ℝ} (h : 0 ≤ t + r) :
    ((t : ℂ) + (r : ℂ)) ^ (1 / 2 : ℂ) = ((√(t + r) : ℝ) : ℂ) := by
  rw [← ofReal_add, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow h, Real.sqrt_eq_rpow]

theorem ei19d_symEllIntS_ofReal {x y z t : ℝ} (hx : 0 ≤ t + x) (hy : 0 ≤ t + y)
    (hz : 0 ≤ t + z) :
    symEllIntS (x : ℂ) (y : ℂ) (z : ℂ) t = ((√(t + x) * √(t + y) * √(t + z) : ℝ) : ℂ) := by
  rw [symEllIntS, ei19d_ofReal_add_cpow_half hx, ei19d_ofReal_add_cpow_half hy,
    ei19d_ofReal_add_cpow_half hz]
  push_cast; ring

/-- `R_F(x, y, z)` is real for nonnegative real `x, y, z`. -/
theorem symEllIntRF_ofReal_im {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (symEllIntRF x y z).im = 0 := by
  have h : (∫ t in Ioi (0 : ℝ), (symEllIntS (x : ℂ) (y : ℂ) (z : ℂ) t)⁻¹) =
      ∫ t in Ioi (0 : ℝ), (((√(t + x) * √(t + y) * √(t + z))⁻¹ : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [ei19d_symEllIntS_ofReal (by linarith) (by linarith) (by linarith), ofReal_inv]
  rw [symEllIntRF, h, integral_complex_ofReal]
  simp

/-! ### §19.24(i) Complete integrals -/

/-- DLMF 19.24.1: `ln 4 ≤ √z R_F(0, y, z) + ln √(y/z) ≤ π/2` for `0 < y ≤ z` (the condition
`y ≤ z` only identifies the smaller variable, 19.24.i.p1). -/
@[dlmf 19.24.E1]
theorem symEllIntRF_zero_log_bounds {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    Real.log 4 ≤ √z * (symEllIntRF 0 y z).re + Real.log √(y / z) ∧
      √z * (symEllIntRF 0 y z).re + Real.log √(y / z) ≤ π / 2 := by
  sorry

/-- DLMF 19.24.2: `1/2 ≤ z^{-1/2} R_G(0, y, z) ≤ π/4` for `0 ≤ y ≤ z`, `z > 0`. -/
@[dlmf 19.24.E2]
theorem symEllIntRG_zero_bounds {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (hz : 0 < z) :
    1 / 2 ≤ (√z)⁻¹ * (symEllIntRG 0 y z).re ∧ (√z)⁻¹ * (symEllIntRG 0 y z).re ≤ π / 4 := by
  sorry

/-- DLMF 19.24.3: `((y^{3/2} + z^{3/2})/2)^{2/3} ≤ (4/π) R_G(0, y², z²) ≤ ((y² + z²)/2)^{1/2}`
for `y, z > 0`. -/
@[dlmf 19.24.E3]
theorem symEllIntRG_zero_sq_bounds {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    ((y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ)) / 2) ^ (2 / 3 : ℝ) ≤
        4 / π * (symEllIntRG 0 ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ)).re ∧
      4 / π * (symEllIntRG 0 ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ)).re ≤ √((y ^ 2 + z ^ 2) / 2) := by
  sorry

/-- DLMF 19.24.4: `(2/√p) (2yz + yp + zp)^{-1/2} ≤ (4/(3π)) R_J(0, y, z, p) ≤ (y z p²)^{-3/8}`
for `y, z, p > 0`; the case `p = z` gives bounds for `R_D(0, y, z)` (19.24.i.p2). -/
@[dlmf 19.24.E4]
theorem symEllIntRJ_zero_bounds {y z p : ℝ} (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    2 / √p * (2 * y * z + y * p + z * p) ^ (-1 / 2 : ℝ) ≤
        4 / (3 * π) * (symEllIntRJ 0 y z p).re ∧
      4 / (3 * π) * (symEllIntRJ 0 y z p).re ≤ (y * z * p ^ 2) ^ (-3 / 8 : ℝ) := by
  sorry

/-- DLMF 19.24.5 with 19.24.6: for `a₀ ≥ g₀ > 0` and the AGM sequences
`a_{n+1} = (aₙ + gₙ)/2`, `g_{n+1} = √(aₙ gₙ)` (19.24.6, §19.8(i)),
`1/aₙ ≤ (2/π) R_F(0, a₀², g₀²) ≤ 1/gₙ` for every `n`. -/
@[dlmf 19.24.E5, dlmf 19.24.E6]
theorem symEllIntRF_zero_agm_bounds {a g : ℕ → ℝ} (hg0 : 0 < g 0) (hag : g 0 ≤ a 0)
    (ha : ∀ n, a (n + 1) = (a n + g n) / 2) (hg : ∀ n, g (n + 1) = √(a n * g n)) (n : ℕ) :
    1 / a n ≤ 2 / π * (symEllIntRF 0 ((a 0 ^ 2 : ℝ) : ℂ) ((g 0 ^ 2 : ℝ) : ℂ)).re ∧
      2 / π * (symEllIntRF 0 ((a 0 ^ 2 : ℝ) : ℂ) ((g 0 ^ 2 : ℝ) : ℂ)).re ≤ 1 / g n := by
  sorry

/-- DLMF 19.24.7: the perimeter of an ellipse with semiaxes `a, b`,
`L(a, b) = 8 R_G(0, a², b²)`, with `L` the arc-length integral `ellipsePerimeter` of §19.9(i)
(`DLMF.EllipticIntegrals.ellipsePerimeter`). Valid for all real `a, b` (both sides depend on
`a², b²` only). -/
@[dlmf 19.24.E7]
theorem ellipsePerimeter_eq_symEllIntRG (a b : ℝ) :
    (ellipsePerimeter a b : ℂ) = 8 * symEllIntRG 0 ((a ^ 2 : ℝ) : ℂ) ((b ^ 2 : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.24.8: for `x, y > 0`, `x ≠ y`,
`R_F(x, y, 0) R_G(x, y, 0) > π²/8` and `R_F(x, y, 0) + 2 R_G(x, y, 0) > π`. -/
@[dlmf 19.24.E8]
theorem symEllIntRF_symEllIntRG_complete_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) :
    π ^ 2 / 8 < (symEllIntRF x y 0).re * (symEllIntRG x y 0).re ∧
      π < (symEllIntRF x y 0).re + 2 * (symEllIntRG x y 0).re := by
  sorry

/-- DLMF 19.24.9 (Neuman): with `a₁ = (a₀ + g₀)/2`, `g₁ = √(a₀ g₀)` (19.24.6) and `a₀ ≥ g₀ > 0`,
`g₁²/2 ≤ R_G(a₀², g₀², 0)/R_F(a₀², g₀², 0) ≤ a₁²/2`, with equality (in either inequality) iff
`a₀ = g₀`. -/
@[dlmf 19.24.E9]
theorem symEllIntRG_div_symEllIntRF_agm_bounds {a₀ g₀ : ℝ} (hg : 0 < g₀) (hag : g₀ ≤ a₀) :
    let a₁ := (a₀ + g₀) / 2
    let g₁ := √(a₀ * g₀)
    let r := (symEllIntRG ((a₀ ^ 2 : ℝ) : ℂ) ((g₀ ^ 2 : ℝ) : ℂ) 0).re /
      (symEllIntRF ((a₀ ^ 2 : ℝ) : ℂ) ((g₀ ^ 2 : ℝ) : ℂ) 0).re
    g₁ ^ 2 / 2 ≤ r ∧ r ≤ a₁ ^ 2 / 2 ∧ (g₁ ^ 2 / 2 = r ↔ a₀ = g₀) ∧ (r = a₁ ^ 2 / 2 ↔ a₀ = g₀) := by
  sorry

/-! ### §19.24(ii) Incomplete integrals -/

/-- DLMF 19.24.10 (lower bound): `3/(√x + √y + √z) ≤ R_F(x, y, z)` for positive `x, y, z`.
From `lean-codes`' `Carlson.inv_dupMean_le_carlsonRF_sq` (Carlson 1966, Theorem 3). -/
@[dlmf 19.24.E10]
theorem symEllIntRF_ge {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 / (√x + √y + √z) ≤ (symEllIntRF x y z).re := by
  have h := Carlson.inv_dupMean_le_carlsonRF_sq (Real.sqrt_pos.mpr hx) (Real.sqrt_pos.mpr hy)
    (Real.sqrt_pos.mpr hz)
  simp only [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le, Real.sq_sqrt hz.le, Carlson.dupMean,
    inv_div] at h
  rw [symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
    (ofReal_mem_slitPlane.mpr hz)]
  exact h

/-- DLMF 19.24.10 (upper bound): `R_F(x, y, z) ≤ (xyz)^{-1/6}` for positive `x, y, z`. -/
@[dlmf 19.24.E10]
theorem symEllIntRF_le {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (symEllIntRF x y z).re ≤ (x * y * z) ^ (-1 / 6 : ℝ) := by
  sorry

/-- DLMF 19.24.11: `(5/(√x + √y + √z + 2√p))³ ≤ R_J(x, y, z, p) ≤ (x y z p²)^{-3/10}` for
positive `x, y, z, p`. -/
@[dlmf 19.24.E11]
theorem symEllIntRJ_bounds {x y z p : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    (5 / (√x + √y + √z + 2 * √p)) ^ 3 ≤ (symEllIntRJ x y z p).re ∧
      (symEllIntRJ x y z p).re ≤ (x * y * z * p ^ 2) ^ (-3 / 10 : ℝ) := by
  sorry

/-- DLMF 19.24.12: `(√x + √y + √z)/3 ≤ R_G(x, y, z) ≤
min(√((x + y + z)/3), (x² + y² + z²)/(3√(xyz)))` for positive `x, y, z`. -/
@[dlmf 19.24.E12]
theorem symEllIntRG_bounds {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (√x + √y + √z) / 3 ≤ (symEllIntRG x y z).re ∧
      (symEllIntRG x y z).re ≤ min (√((x + y + z) / 3)) ((x ^ 2 + y ^ 2 + z ^ 2) / (3 * √(x * y *
        z))) := by
  sorry

/-- DLMF 19.24.13 (Neuman): if `a ≠ 0` is real, all components of `𝐛` and `𝐳` are positive and
the components of `𝐳` are not all equal, then `R_a(𝐛; 𝐳) R_{-a}(𝐛; 𝐳) > 1` and
`R_a(𝐛; 𝐳) + R_{-a}(𝐛; 𝐳) > 2`. In `symEllIntR a 𝐛 𝐳 = R_{-a}(𝐛; 𝐳)` notation,
`R_a(𝐛; 𝐳) = symEllIntR (-a) 𝐛 𝐳`. -/
@[dlmf 19.24.E13]
theorem symEllIntR_mul_neg_gt {ι : Type*} [Fintype ι] {a : ℝ} (ha : a ≠ 0) {b z : ι → ℝ}
    (hb : ∀ i, 0 < b i) (hz : ∀ i, 0 < z i) (hne : ∃ i j, z i ≠ z j) :
    1 < (symEllIntR (-a : ℂ) (fun i => (b i : ℂ)) (fun i => (z i : ℂ))).re *
        (symEllIntR (a : ℂ) (fun i => (b i : ℂ)) (fun i => (z i : ℂ))).re ∧
      2 < (symEllIntR (-a : ℂ) (fun i => (b i : ℂ)) (fun i => (z i : ℂ))).re +
        (symEllIntR (a : ℂ) (fun i => (b i : ℂ)) (fun i => (z i : ℂ))).re := by
  sorry

/-- DLMF 19.24.14: for positive `x, y, z`, not all equal, `R_F(x, y, z) R_G(x, y, z) > 1` and
`R_F(x, y, z) + R_G(x, y, z) > 2` (the case `a = 1/2` of (19.24.13)). -/
@[dlmf 19.24.E14]
theorem symEllIntRF_symEllIntRG_gt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hne : ¬ (x = y ∧ y = z)) :
    1 < (symEllIntRF x y z).re * (symEllIntRG x y z).re ∧
      2 < (symEllIntRF x y z).re + (symEllIntRG x y z).re := by
  sorry

/-- DLMF 19.24.15: `R_C(x, (y + z)/2) ≤ R_F(x, y, z) ≤ R_C(x, √(yz))` for `x ≥ 0` and `y, z > 0`,
with equality (in either inequality) iff `y = z`. -/
@[dlmf 19.24.E15]
theorem symEllIntRF_symEllIntRC_bounds {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    (symEllIntRC x (((y + z) / 2 : ℝ) : ℂ)).re ≤ (symEllIntRF x y z).re ∧
      (symEllIntRF x y z).re ≤ (symEllIntRC x ((√(y * z) : ℝ) : ℂ)).re ∧
      ((symEllIntRC x (((y + z) / 2 : ℝ) : ℂ)).re = (symEllIntRF x y z).re ↔ y = z) ∧
      ((symEllIntRF x y z).re = (symEllIntRC x ((√(y * z) : ℝ) : ℂ)).re ↔ y = z) := by
  sorry

end DLMF.EllipticIntegrals
