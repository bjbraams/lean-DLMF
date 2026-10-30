/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Legendre
public import DLMF.Elementary.Trigonometric
public import Carlson.Elliptic.Standard
public import Carlson.Elliptic.CapacityBound
public import Carlson.Mean.Bounds

/-!
# Inequalities for Legendre's elliptic integrals (DLMF §19.9)

DLMF §19.9 states inequalities for real modulus `0 < k < 1`, `k' = √(1 - k²)`, and, in
§19.9(ii), real amplitude `0 ≤ φ ≤ π/2` with `Δ = √(1 - k² sin²φ) > 0`. The Legendre integrals
are the complex DLMF integrals of `DLMF.EllipticIntegrals` (`incEllIntFk`, `incEllIntEk`,
`incEllIntPik`, `compEllIntEk`, `compEllIntPik`, and `DLMF.JacobiElliptic.compEllIntKk`,
`cCompEllIntKk`), evaluated at real arguments; there they are real
(`incEllIntFk_eq_ofReal` etc.), and the inequalities are stated for their real parts.

The strict bounds (19.9.14) use the normalized first-kind integral from
`Carlson.Elliptic.Standard`, the strict capacity lower bound from
`Carlson.Elliptic.CapacityBound`, and the geometric upper bound from `Carlson.Mean.Bounds`
(all in lean-codes).

Domain qualifications (Lean totalization; DLMF's own statements are kept otherwise):

* (19.9.1), third line, and (19.9.13): the characteristic `α²` is real with `α² < 1`, as DLMF
  states for (19.9.1); for (19.9.13) DLMF leaves the range of `α²` implicit, and `α² < 1` is the
  range where the defining integral is an ordinary positive integral.
* (19.9.11): the bound by `gd⁻¹(φ)` is stated for `φ < π/2` (at `φ = π/2`, `gd⁻¹ = ∞`, and the
  minimum is `φ/Δ`). Likewise in (19.9.13) the bound by `Π(φ, α², 1)` needs `φ < π/2`.
* (19.9.14)–(19.9.16) need `sin φ > 0`; (19.9.14) and (19.9.17) also need `cos φ > 0`
  (otherwise a side is infinite), so they are stated for `0 < φ < π/2`; (19.9.15), (19.9.16)
  for `0 < φ ≤ π/2`.
* The perimeter `L(a, b)` of (19.9.9) is the arc length of `t ↦ (a cos t, b sin t)`,
  `ellipsePerimeter`.

The approximations of §19.9(i) ((19.9.10) and the cited accuracy figures) are numerical and not
acquired, except the analytical statement that Ramanujan's approximation is from below
(Barnard et al. 2000), `pi_mul_ramanujan_le_ellipsePerimeter`.

## References

* NIST DLMF §19.9.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### Real-variable helpers -/

/-- `x^{-1/2} = (√x)⁻¹` for `x ≥ 0`. -/
theorem ei19b_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 / 2) : ℝ) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

/-- `x^{1/2} = √x`. -/
theorem ei19b_rpow_half (x : ℝ) : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm

/-- On `[0, π/2]` the sine is monotone: `sin² θ ≤ sin² φ` for `0 ≤ θ ≤ φ ≤ π/2`. -/
lemma ei19b_sin_sq_le {θ φ : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≤ φ) (hφ : φ ≤ π / 2) :
    Real.sin θ ^ 2 ≤ Real.sin φ ^ 2 := by
  have hs : Real.sin θ ≤ Real.sin φ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hφ hθ
  have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  exact pow_le_pow_left₀ h1 hs 2

/-- `1 - m sin²θ ≥ cos²θ` for `m ≤ 1`. -/
lemma ei19b_cos_sq_le {m : ℝ} (hm : m ≤ 1) (θ : ℝ) :
    Real.cos θ ^ 2 ≤ 1 - m * Real.sin θ ^ 2 := by
  have := Real.sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (Real.sin θ)]

/-- `1 - m sin²θ ≥ 1 - m sin²φ` for `0 ≤ m` and `0 ≤ θ ≤ φ ≤ π/2`. -/
lemma ei19b_delta_sq_le {m θ φ : ℝ} (hm : 0 ≤ m) (h0 : 0 ≤ θ) (hθ : θ ≤ φ) (hφ : φ ≤ π / 2) :
    1 - m * Real.sin φ ^ 2 ≤ 1 - m * Real.sin θ ^ 2 := by
  nlinarith [ei19b_sin_sq_le h0 hθ hφ]

/-- `1 - m sin²θ ≤ 1` for `m ≥ 0`. -/
lemma ei19b_base_le_one {m : ℝ} (hm : 0 ≤ m) (θ : ℝ) : 1 - m * Real.sin θ ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg (Real.sin θ)]

/-- The third-kind factor `(1 - n sin²θ)⁻¹` is positive for `n < 1`. -/
lemma ei19b_pi_factor_pos {n : ℝ} (hn : n < 1) (θ : ℝ) : 0 < (1 - n * Real.sin θ ^ 2)⁻¹ :=
  inv_pos.mpr (DLMF.Elliptic.one_sub_mul_sin_sq_pos hn θ)

/-! ### Real forms of the integrals -/

/-- `Re F(φ, k) = F(φ | k²)` for real `φ` and `k² ≤ 1`. -/
lemma ei19b_re_incEllIntFk {φ k : ℝ} (hk : k ^ 2 ≤ 1) :
    (incEllIntFk φ k).re = DLMF.Elliptic.Real.incEllIntFm φ (k ^ 2) := by
  rw [incEllIntFk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk φ, ofReal_re]

/-- `Re E(φ, k) = E(φ | k²)` for real `φ` and `k² ≤ 1`. -/
lemma ei19b_re_incEllIntEk {φ k : ℝ} (hk : k ^ 2 ≤ 1) :
    (incEllIntEk φ k).re = DLMF.Elliptic.Real.incEllIntEm φ (k ^ 2) := by
  rw [incEllIntEk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk φ, ofReal_re]

/-- `Re Π(φ, α², k) = Π(φ, α² | k²)` for real `φ`, `α² < 1` and `k² ≤ 1`. -/
lemma ei19b_re_incEllIntPik {φ α2 k : ℝ} (hα : α2 < 1) (hk : k ^ 2 ≤ 1) :
    (incEllIntPik φ α2 k).re = DLMF.Elliptic.Real.incEllIntPim φ α2 (k ^ 2) := by
  rw [incEllIntPik_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk hα φ, ofReal_re]

/-- `E(k) = E(π/2, k)` with a real amplitude cast. -/
lemma ei19b_compEllIntEk_eq (k : ℂ) : compEllIntEk k = incEllIntEk ((π / 2 : ℝ) : ℂ) k := by
  rw [compEllIntEk]; push_cast; rfl

/-- `Π(α², k) = Π(π/2, α², k)` with a real amplitude cast. -/
lemma ei19b_compEllIntPik_eq (α2 k : ℂ) :
    compEllIntPik α2 k = incEllIntPik ((π / 2 : ℝ) : ℂ) α2 k := by
  rw [compEllIntPik]; push_cast; rfl

/-! ### §19.9(i) Complete integrals -/

/-- DLMF 19.9.1, first line: `ln 4 ≤ K(k) + ln k' ≤ π/2` for `0 < k < 1`. -/
@[dlmf 19.9.E1]
theorem log_four_le_compEllIntKk_add_log {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    Real.log 4 ≤ (compEllIntKk k).re + Real.log (Real.sqrt (1 - k ^ 2)) ∧
      (compEllIntKk k).re + Real.log (Real.sqrt (1 - k ^ 2)) ≤ π / 2 := by
  sorry

/-- DLMF 19.9.2: `1 + k'²/8 < K(k)/ln(4/k') < 1 + k'²/4` for `0 < k < 1`. -/
@[dlmf 19.9.E2]
theorem compEllIntKk_div_log_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    1 + (1 - k ^ 2) / 8 < (compEllIntKk k).re / Real.log (4 / Real.sqrt (1 - k ^ 2)) ∧
      (compEllIntKk k).re / Real.log (4 / Real.sqrt (1 - k ^ 2)) < 1 + (1 - k ^ 2) / 4 := by
  sorry

/-- DLMF 19.9.3: `9 + k²k'²/8 < (8 + k²) K(k)/ln(4/k') < 9.096` for `0 < k < 1`. -/
@[dlmf 19.9.E3]
theorem eight_add_sq_mul_compEllIntKk_div_log_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    9 + k ^ 2 * (1 - k ^ 2) / 8 <
        (8 + k ^ 2) * (compEllIntKk k).re / Real.log (4 / Real.sqrt (1 - k ^ 2)) ∧
      (8 + k ^ 2) * (compEllIntKk k).re / Real.log (4 / Real.sqrt (1 - k ^ 2)) < 9.096 := by
  sorry

/-- DLMF 19.9.4: `((1 + k'^{3/2})/2)^{2/3} ≤ (2/π) E(k) ≤ ((1 + k'²)/2)^{1/2}` for
`0 ≤ k ≤ 1`. -/
@[dlmf 19.9.E4]
theorem compEllIntEk_bounds {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    ((1 + Real.sqrt (1 - k ^ 2) ^ (3 / 2 : ℝ)) / 2) ^ (2 / 3 : ℝ) ≤ 2 / π * (compEllIntEk k).re ∧
      2 / π * (compEllIntEk k).re ≤ Real.sqrt ((1 + (1 - k ^ 2)) / 2) := by
  sorry

/-- DLMF 19.9.5: `ln((1 + √k')²/k) < π K'(k)/(2K(k)) < ln(2(1 + k')/k)` for `0 < k < 1`, with
DLMF's complementary integral `K'(k)` (`cCompEllIntKk`, equal to `K(k')` here). -/
@[dlmf 19.9.E5]
theorem pi_mul_cCompEllIntKk_div_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    Real.log ((1 + Real.sqrt (Real.sqrt (1 - k ^ 2))) ^ 2 / k) <
        π * (cCompEllIntKk k).re / (2 * (compEllIntKk k).re) ∧
      π * (cCompEllIntKk k).re / (2 * (compEllIntKk k).re) <
        Real.log (2 * (1 + Real.sqrt (1 - k ^ 2)) / k) := by
  sorry

/-- DLMF 19.9.6: `(1 - ¾k²)^{-1/2} < (4/(πk²))(K(k) - E(k)) < k'^{-3/4}` for `0 < k < 1`. -/
@[dlmf 19.9.E6]
theorem compEllIntKk_sub_compEllIntEk_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    (1 - 3 / 4 * k ^ 2) ^ (-(1 / 2) : ℝ) <
        4 / (π * k ^ 2) * ((compEllIntKk k).re - (compEllIntEk k).re) ∧
      4 / (π * k ^ 2) * ((compEllIntKk k).re - (compEllIntEk k).re) <
        Real.sqrt (1 - k ^ 2) ^ (-(3 / 4) : ℝ) := by
  sorry

/-- DLMF 19.9.7: `(1 - ¼k²)^{-1/2} < (4/(πk²))(E(k) - k'² K(k)) < min(k'^{-1/4}, 4/π)` for
`0 < k < 1`. -/
@[dlmf 19.9.E7]
theorem compEllIntEk_sub_mul_compEllIntKk_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    (1 - 1 / 4 * k ^ 2) ^ (-(1 / 2) : ℝ) <
        4 / (π * k ^ 2) * ((compEllIntEk k).re - (1 - k ^ 2) * (compEllIntKk k).re) ∧
      4 / (π * k ^ 2) * ((compEllIntEk k).re - (1 - k ^ 2) * (compEllIntKk k).re) <
        min (Real.sqrt (1 - k ^ 2) ^ (-(1 / 4) : ℝ)) (4 / π) := by
  sorry

/-- DLMF 19.9.8: `k' < E(k)/K(k) < ((1 + k')/2)²` for `0 < k < 1`. -/
@[dlmf 19.9.E8]
theorem compEllIntEk_div_compEllIntKk_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    Real.sqrt (1 - k ^ 2) < (compEllIntEk k).re / (compEllIntKk k).re ∧
      (compEllIntEk k).re / (compEllIntKk k).re < ((1 + Real.sqrt (1 - k ^ 2)) / 2) ^ 2 := by
  sorry

/-- The perimeter `L(a, b)` of an ellipse with semiaxes `a, b` (DLMF §19.9(i)): the arc length
`∫₀^{2π} √(a² sin²t + b² cos²t) dt` of `t ↦ (a cos t, b sin t)`. -/
@[dlmf 19.9.i]
def ellipsePerimeter (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * π), Real.sqrt (a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2)

/-- DLMF 19.9.9: `L(a, b) = 4a E(k)`, `k² = 1 - b²/a²`, `a > b` (here `b ≥ 0`). -/
@[dlmf 19.9.E9]
theorem ellipsePerimeter_eq {a b : ℝ} (hb : 0 ≤ b) (hab : b < a) :
    (ellipsePerimeter a b : ℂ) = 4 * a * compEllIntEk (Real.sqrt (1 - b ^ 2 / a ^ 2)) := by
  have ha : 0 < a := lt_of_le_of_lt hb hab
  set m := 1 - b ^ 2 / a ^ 2 with hmdef
  have hba : b ^ 2 / a ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hm0 : 0 ≤ m := by rw [hmdef]; linarith
  have hm1 : m ≤ 1 := by
    rw [hmdef]; have : 0 ≤ b ^ 2 / a ^ 2 := by positivity
    linarith
  set f : ℝ → ℝ := fun θ => Real.sqrt (1 - m * Real.sin θ ^ 2) with hf
  have hfc : Continuous f := by fun_prop
  have hfper : Function.Periodic f π := fun θ => by simp [hf, Real.sin_add_pi]
  have hfsym : ∀ θ, f (π - θ) = f θ := fun θ => by simp [hf, Real.sin_pi_sub]
  -- (i) factor out `a`
  have h1 : ellipsePerimeter a b = a * ∫ t in (0 : ℝ)..(2 * π), f (t + π / 2) := by
    rw [ellipsePerimeter, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hf, Real.sin_add_pi_div_two]
    have hst := Real.sin_sq_add_cos_sq t
    have hX : 0 ≤ 1 - m * Real.cos t ^ 2 := by
      nlinarith [Real.cos_sq_le_one t, sq_nonneg (Real.cos t)]
    rw [show a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2 = a ^ 2 * (1 - m * Real.cos t ^ 2) by
      rw [hmdef]; field_simp; linear_combination a ^ 2 * hst,
      Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le]
  -- (ii) shift and periodicity
  have hper2 : Function.Periodic f (2 * π) := by
    intro θ; rw [show θ + 2 * π = θ + π + π by ring, hfper, hfper]
  have h2 : ∫ t in (0 : ℝ)..(2 * π), f (t + π / 2) = ∫ t in (0 : ℝ)..(2 * π), f t := by
    rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (2 * π),
      hper2.intervalIntegral_add_eq (π / 2) 0, zero_add]
  -- (iii) reduce to a quarter period
  have h3 : ∫ t in (0 : ℝ)..(2 * π), f t = 4 * ∫ t in (0 : ℝ)..(π / 2), f t := by
    have hq : ∫ t in (π / 2)..π, f t = ∫ t in (0 : ℝ)..(π / 2), f t := by
      have := intervalIntegral.integral_comp_sub_left f (a := 0) (b := π / 2) π
      simp only [hfsym, sub_zero, show π - π / 2 = π / 2 by ring] at this
      exact this.symm
    have hh : ∫ t in π..(2 * π), f t = ∫ t in (0 : ℝ)..π, f t := by
      have := intervalIntegral.integral_comp_add_right f (a := 0) (b := π) π
      simp only [zero_add, show π + π = 2 * π by ring] at this
      rw [← this]
      exact intervalIntegral.integral_congr fun t _ => hfper t
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := π)
      (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _), hh,
      ← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
      (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _), hq]
    ring
  -- (iv) identify `E(m)`
  have hk : ((Real.sqrt (1 - b ^ 2 / a ^ 2) : ℝ) : ℂ) ^ 2 = ((m : ℝ) : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt hm0]
  have h4 : compEllIntEk ((Real.sqrt (1 - b ^ 2 / a ^ 2) : ℝ) : ℂ) =
      ((∫ t in (0 : ℝ)..(π / 2), f t : ℝ) : ℂ) := by
    rw [compEllIntEk_eq_ofReal hk hm1, DLMF.Elliptic.Real.compEllIntEm]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hf, ei19b_rpow_half]
  rw [h1, h2, h3, h4]
  push_cast
  ring

/-- DLMF §19.9(i) (Barnard et al. 2000): Ramanujan's approximation is from below,
`π(a + b)(1 + 3λ²/(10 + √(4 - 3λ²))) ≤ L(a, b)`, `λ = (a - b)/(a + b)`, `a > b ≥ 0`. -/
@[dlmf 19.9.i]
theorem pi_mul_ramanujan_le_ellipsePerimeter {a b : ℝ} (hb : 0 ≤ b) (hab : b < a) :
    π * (a + b) * (1 + 3 * ((a - b) / (a + b)) ^ 2 /
        (10 + Real.sqrt (4 - 3 * ((a - b) / (a + b)) ^ 2))) ≤ ellipsePerimeter a b := by
  sorry

/-! ### §19.9(ii) Incomplete integrals -/

/-- DLMF 19.9.11: `φ ≤ F(φ, k) ≤ min(φ/Δ, gd⁻¹(φ))` for `0 < k < 1`, `0 ≤ φ ≤ π/2`,
`Δ = √(1 - k² sin²φ)`; the bound `gd⁻¹(φ)` (DLMF 4.23.41,
`DLMF.Elementary.inverseGudermannian`) is stated for `φ < π/2`. -/
@[dlmf 19.9.E11]
theorem incEllIntFk_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) :
    φ ≤ (incEllIntFk φ k).re ∧
      (incEllIntFk φ k).re ≤ φ / Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) ∧
      (φ < π / 2 → (incEllIntFk φ k).re ≤ DLMF.Elementary.inverseGudermannian φ) := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hm0 : 0 ≤ k ^ 2 := sq_nonneg k
  rw [ei19b_re_incEllIntFk hk2.le, DLMF.Elliptic.Real.incEllIntFm]
  have hc := DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hk2 (-(1 / 2))
  have hΔ : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 φ
  refine ⟨?_, ?_, ?_⟩
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (continuous_const.intervalIntegrable 0 φ)
      (hc.intervalIntegrable 0 φ) (f := fun _ => (1 : ℝ)) (fun θ hθ => by
        rw [ei19b_rpow_neg_half (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
        have h1 := ei19b_base_le_one hm0 θ
        have h2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ
        rw [one_le_inv₀ (Real.sqrt_pos.mpr h2)]
        exact Real.sqrt_le_one.mpr h1)
    simpa using h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (hc.intervalIntegrable 0 φ)
      (continuous_const.intervalIntegrable 0 φ)
      (g := fun _ => (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2))⁻¹)
      (fun θ hθ => by
        rw [ei19b_rpow_neg_half (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
        exact inv_anti₀ (Real.sqrt_pos.mpr hΔ)
          (Real.sqrt_le_sqrt (ei19b_delta_sq_le hm0 hθ.1 hθ.2 hφ1)))
    simpa [div_eq_mul_inv] using h
  · intro hφ2
    unfold DLMF.Elementary.inverseGudermannian
    have hcos : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < Real.cos θ := fun θ hθ =>
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    refine intervalIntegral.integral_mono_on hφ0 (hc.intervalIntegrable 0 φ) ?_ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hφ0]
      exact (Real.continuous_cos.continuousOn).inv₀ fun θ hθ => (hcos θ hθ).ne'
    · intro θ hθ
      rw [ei19b_rpow_neg_half (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
      refine inv_anti₀ (hcos θ hθ) ?_
      rw [← Real.sqrt_sq (hcos θ hθ).le]
      exact Real.sqrt_le_sqrt (ei19b_cos_sq_le hk2.le θ)

/-- DLMF 19.9.12: `max(sin φ, φΔ) ≤ E(φ, k) ≤ φ` for `0 < k < 1`, `0 ≤ φ ≤ π/2`. -/
@[dlmf 19.9.E12]
theorem incEllIntEk_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) :
    max (Real.sin φ) (φ * Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2)) ≤ (incEllIntEk φ k).re ∧
      (incEllIntEk φ k).re ≤ φ := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hm0 : 0 ≤ k ^ 2 := sq_nonneg k
  rw [ei19b_re_incEllIntEk hk2.le, DLMF.Elliptic.Real.incEllIntEm]
  have hc := DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hk2 (1 / 2)
  refine ⟨max_le ?_ ?_, ?_⟩
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (Real.continuous_cos.intervalIntegrable 0 φ)
      (hc.intervalIntegrable 0 φ) (fun θ hθ => by
        rw [ei19b_rpow_half]
        have hcos : 0 ≤ Real.cos θ :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
        rw [← Real.sqrt_sq hcos]
        exact Real.sqrt_le_sqrt (ei19b_cos_sq_le hk2.le θ))
    simpa using h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (continuous_const.intervalIntegrable 0 φ)
      (hc.intervalIntegrable 0 φ) (f := fun _ => Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2))
      (fun θ hθ => by
        rw [ei19b_rpow_half]
        exact Real.sqrt_le_sqrt (ei19b_delta_sq_le hm0 hθ.1 hθ.2 hφ1))
    simpa using h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (hc.intervalIntegrable 0 φ)
      (continuous_const.intervalIntegrable 0 φ) (g := fun _ => (1 : ℝ)) (fun θ _ => by
        rw [ei19b_rpow_half]
        exact Real.sqrt_le_one.mpr (ei19b_base_le_one hm0 θ))
    simpa using h

/-- Pointwise comparison of the third-kind integrands in the modulus. -/
lemma ei19b_piIntegrand_mono {n m m' θ : ℝ} (hn : n < 1) (hm : m ≤ m')
    (hm' : m' * Real.sin θ ^ 2 < 1)
    (hm0 : m * Real.sin θ ^ 2 < 1) :
    DLMF.Elliptic.piIntegrand n m θ ≤ DLMF.Elliptic.piIntegrand n m' θ := by
  unfold DLMF.Elliptic.piIntegrand
  refine mul_le_mul_of_nonneg_left ?_ (ei19b_pi_factor_pos hn θ).le
  rw [ei19b_rpow_neg_half (by linarith), ei19b_rpow_neg_half (by linarith)]
  refine inv_anti₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt ?_)
  nlinarith [sq_nonneg (Real.sin θ)]

/-- DLMF 19.9.13: `Π(φ, α², 0) ≤ Π(φ, α², k) ≤ min(Π(φ, α², 0)/Δ, Π(φ, α², 1))` for
`0 < k < 1`, `0 ≤ φ ≤ π/2` and real `α² < 1`; the bound by `Π(φ, α², 1)` is stated for
`φ < π/2` (it is infinite at `φ = π/2`). -/
@[dlmf 19.9.E13]
theorem incEllIntPik_bounds {φ α2 k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) (hα : α2 < 1) :
    (incEllIntPik φ α2 0).re ≤ (incEllIntPik φ α2 k).re ∧
      (incEllIntPik φ α2 k).re ≤
        (incEllIntPik φ α2 0).re / Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) ∧
      (φ < π / 2 → (incEllIntPik φ α2 k).re ≤ (incEllIntPik φ α2 1).re) := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hm0 : 0 ≤ k ^ 2 := sq_nonneg k
  have e0 : incEllIntPik φ α2 0 = incEllIntPik φ α2 ((0 : ℝ) : ℂ) := by simp
  have e1 : incEllIntPik φ α2 1 = incEllIntPik φ α2 ((1 : ℝ) : ℂ) := by simp
  rw [e0, e1, ei19b_re_incEllIntPik hα hk2.le, ei19b_re_incEllIntPik (k := 0) hα (by norm_num),
    ei19b_re_incEllIntPik (k := 1) hα (by norm_num)]
  simp only [DLMF.Elliptic.Real.incEllIntPim]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, one_pow]
  have hcont : ∀ m : ℝ, m < 1 → Continuous (DLMF.Elliptic.piIntegrand α2 m) :=
    fun m hm => DLMF.Elliptic.continuous_piIntegrand hα hm
  have hΔ : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 φ
  refine ⟨?_, ?_, ?_⟩
  · refine intervalIntegral.integral_mono_on hφ0 ((hcont 0 (by norm_num)).intervalIntegrable _ _)
      ((hcont _ hk2).intervalIntegrable _ _) fun θ _ => ?_
    have h := ei19b_piIntegrand_mono (θ := θ) hα hm0 (by nlinarith [Real.sin_sq_le_one θ])
      (by simp)
    simpa using h
  · rw [div_eq_mul_inv, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_mono_on hφ0 ((hcont _ hk2).intervalIntegrable _ _)
      (((hcont 0 (by norm_num)).mul continuous_const).intervalIntegrable _ _) fun θ hθ => ?_
    unfold DLMF.Elliptic.piIntegrand
    simp only [zero_mul, sub_zero, Real.one_rpow, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ (ei19b_pi_factor_pos hα θ).le
    rw [ei19b_rpow_neg_half (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
    exact inv_anti₀ (Real.sqrt_pos.mpr hΔ)
      (Real.sqrt_le_sqrt (ei19b_delta_sq_le hm0 hθ.1 hθ.2 hφ1))
  · intro hφ2
    have hcos : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < Real.cos θ := fun θ hθ =>
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    have hbase : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < 1 - 1 * Real.sin θ ^ 2 := fun θ hθ => by
      have := Real.sin_sq_add_cos_sq θ
      have := hcos θ hθ
      nlinarith
    refine intervalIntegral.integral_mono_on hφ0 ((hcont _ hk2).intervalIntegrable _ _) ?_
      fun θ hθ => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hφ0]
      unfold DLMF.Elliptic.piIntegrand
      refine ContinuousOn.mul ((Continuous.inv₀ (by fun_prop)
        fun θ => (DLMF.Elliptic.one_sub_mul_sin_sq_pos hα θ).ne').continuousOn) ?_
      · exact ContinuousOn.rpow_const (by fun_prop) fun θ hθ => Or.inl (hbase θ hθ).ne'
    · have hb := hbase θ hθ
      exact ei19b_piIntegrand_mono hα hk2.le (by linarith)
        (by nlinarith [Real.sin_sq_le_one θ])

/-- DLMF 19.9.1, second line: `1 ≤ E(k) ≤ π/2` for `0 < k < 1`. -/
@[dlmf 19.9.E1]
theorem one_le_compEllIntEk_le {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    1 ≤ (compEllIntEk k).re ∧ (compEllIntEk k).re ≤ π / 2 := by
  rw [ei19b_compEllIntEk_eq]
  have h := incEllIntEk_bounds (φ := π / 2) hk0 hk1 (by positivity) le_rfl
  rw [Real.sin_pi_div_two] at h
  exact ⟨le_trans (le_max_left _ _) h.1, h.2⟩

/-- DLMF 19.9.1, third line: `1 ≤ (2/π)√(1 - α²) Π(α², k) ≤ 1/k'` for `0 < k < 1` and real
`α² < 1`. -/
@[dlmf 19.9.E1]
theorem one_le_compEllIntPik_le {α2 k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hα : α2 < 1) :
    1 ≤ 2 / π * Real.sqrt (1 - α2) * (compEllIntPik α2 k).re ∧
      2 / π * Real.sqrt (1 - α2) * (compEllIntPik α2 k).re ≤ 1 / Real.sqrt (1 - k ^ 2) := by
  rw [ei19b_compEllIntPik_eq]
  have h := incEllIntPik_bounds (φ := π / 2) hk0 hk1 (by positivity) le_rfl hα
  rw [Real.sin_pi_div_two, one_pow, mul_one] at h
  have e0 : incEllIntPik ((π / 2 : ℝ) : ℂ) α2 0 = incEllIntPik ((π / 2 : ℝ) : ℂ) α2 ((0 : ℝ) : ℂ) :=
    by simp
  rw [e0, ei19b_re_incEllIntPik (k := 0) hα (by norm_num)] at h
  have hz : DLMF.Elliptic.Real.incEllIntPim (π / 2) α2 (0 ^ 2) = π / (2 * Real.sqrt (1 - α2)) := by
    rw [zero_pow two_ne_zero]
    exact DLMF.Elliptic.Real.compEllIntPim_param_zero hα
  rw [hz] at h
  have hs : 0 < Real.sqrt (1 - α2) := Real.sqrt_pos.mpr (by linarith)
  have hk' : 0 < Real.sqrt (1 - k ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hc : 0 < 2 / π * Real.sqrt (1 - α2) := by positivity
  obtain ⟨h1, h2, -⟩ := h
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hc.le
    calc (1 : ℝ) = 2 / π * Real.sqrt (1 - α2) * (π / (2 * Real.sqrt (1 - α2))) := by
          field_simp
      _ ≤ _ := this
  · have := mul_le_mul_of_nonneg_left h2 hc.le
    calc _ ≤ 2 / π * Real.sqrt (1 - α2) * (π / (2 * Real.sqrt (1 - α2)) / Real.sqrt (1 - k ^ 2)) :=
          this
      _ = 1 / Real.sqrt (1 - k ^ 2) := by field_simp

/-- DLMF 19.9.14: `3/(1 + Δ + cos φ) < F(φ, k)/sin φ < (Δ cos φ)^{-1/3}` for `0 < k < 1`,
`0 < φ < π/2`. -/
@[dlmf 19.9.E14]
theorem incEllIntFk_div_sin_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) :
    3 / (1 + Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ) <
        (incEllIntFk φ k).re / Real.sin φ ∧
      (incEllIntFk φ k).re / Real.sin φ <
        (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) * Real.cos φ) ^ (-(1 / 3) : ℝ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ1⟩
  have hx : 0 < Real.cos φ ^ 2 := sq_pos_of_pos hc
  have hy : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk φ
  have hxy : ¬(Real.cos φ ^ 2 = 1 - k ^ 2 * Real.sin φ ^ 2 ∧ 1 - k ^ 2 * Real.sin φ ^ 2 = 1) := by
    intro he
    nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_pos hs]
  have hF : (incEllIntFk φ k).re / Real.sin φ =
      (Carlson.carlsonRF ((Real.cos φ ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1).re := by
    have h := congrArg Complex.re (Carlson.Real.incEllIntFk_eq hφ0 hφ1 hk)
    have he := incEllIntFk_eq_ofReal (m:=k ^ 2) (k:=(k : ℂ)) (by push_cast; rfl) hk.le φ
    rw [he, ofReal_re]
    change DLMF.Elliptic.Real.incEllIntFm φ (k ^ 2) / Real.sin φ = _
    simp only [ofReal_re] at h
    have hreal : Carlson.Real.incEllIntFk φ k = DLMF.Elliptic.Real.incEllIntFm φ (k ^ 2) := by
      simp only [Carlson.Real.incEllIntFk, DLMF.Elliptic.Real.incEllIntFm, neg_div]
    rw [hreal] at h
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at h
    rw [h]
    field_simp
  rw [hF]
  constructor
  · have h := Carlson.carlsonRF_capacity_lower_bound hx hy (by norm_num : (0 : ℝ) < 1) hxy
    simpa only [Real.sqrt_sq hc.le, Real.sqrt_one, ofReal_one, add_comm, add_left_comm] using h
  · let b : Fin 3 → ℝ := fun _ => 1 / 2
    let v : Fin 3 → ℝ := ![Real.cos φ ^ 2, 1 - k ^ 2 * Real.sin φ ^ 2, 1]
    have hb : b ∈ ProbabilityTheory.mvRealBetaDomain := by intro i; norm_num [b]
    have hv : ∀ i, 0 < v i := by intro i; fin_cases i <;> first | exact hx | exact hy | norm_num [v]
    have hn : ∃ i j, v i ≠ v j := by
      refine ⟨0, 2, ?_⟩
      dsimp [v]
      nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_pos hs]
    have hh := (Carlson.carlsonRReal_bounds_between_neg_sum_zero hb hv hn
      (by norm_num : (-1 / 2 : ℝ) < 0) (by norm_num [b, Fin.sum_univ_succ])).2
    have he := Carlson.ofReal_carlsonRReal (-1 / 2) hb hv
    have he' : (Carlson.carlsonRF ((Real.cos φ ^ 2 : ℝ) : ℂ) ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1).re =
        Carlson.carlsonRReal (-1 / 2) b v := by
      unfold Carlson.carlsonRF
      have ev : (fun i => (v i : ℂ)) = ![((Real.cos φ ^ 2 : ℝ) : ℂ), ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ), 1] := by
        ext i; fin_cases i <;> simp [v]
      norm_num only [b, ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat, ev] at he
      rw [neg_div, ←he, ofReal_re]
      simp only [neg_div, b]
    rw [he']
    refine hh.trans_eq ?_
    rw [←Real.exp_mul, Real.rpow_def_of_pos (mul_pos (Real.sqrt_pos.mpr hy) hc)]
    congr 1
    simp only [b, v, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Real.log_one, mul_zero, Real.log_mul (Real.sqrt_pos.mpr hy).ne' hc.ne',
      Real.log_sqrt hy.le, Real.log_pow]
    ring

/-- DLMF 19.9.15: `1 < F(φ, k)/((sin φ) ln(4/(Δ + cos φ))) < 4/(2 + (1 + k²) sin²φ)` for
`0 < k < 1`, `0 < φ ≤ π/2`. -/
@[dlmf 19.9.E15]
theorem incEllIntFk_div_sin_mul_log_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ ≤ π / 2) :
    1 < (incEllIntFk φ k).re /
        (Real.sin φ * Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ))) ∧
      (incEllIntFk φ k).re /
          (Real.sin φ * Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ))) <
        4 / (2 + (1 + k ^ 2) * Real.sin φ ^ 2) := by
  sorry

/-- DLMF 19.9.16: `F(φ, k) = (2/π) K(k') ln(4/(Δ + cos φ)) - θΔ²` with
`(sin φ)/8 < θ < (ln 2)/(k² sin φ)`, for `0 < k < 1`, `0 < φ ≤ π/2`; here `θ` is defined by the
equation. -/
@[dlmf 19.9.E16]
theorem incEllIntFk_eq_log_sub_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ ≤ π / 2) :
    Real.sin φ / 8 <
        (2 / π * (compEllIntKk (Real.sqrt (1 - k ^ 2))).re *
            Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ)) -
          (incEllIntFk φ k).re) / (1 - k ^ 2 * Real.sin φ ^ 2) ∧
      (2 / π * (compEllIntKk (Real.sqrt (1 - k ^ 2))).re *
            Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ)) -
          (incEllIntFk φ k).re) / (1 - k ^ 2 * Real.sin φ ^ 2) <
        Real.log 2 / (k ^ 2 * Real.sin φ) := by
  sorry

/-! ### Helpers for 19.9.17–19.9.18 -/

/-- At `x`, the function `Real.artanh` has derivative `(1 / (1 - x ^ 2))`. -/
lemma p19lR1_hasDerivAt_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  have heq : (fun y => 1 / 2 * (Real.log (1 + y) - Real.log (1 - y))) =ᶠ[𝓝 x] Real.artanh := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    have h1' : 0 < 1 + y := by linarith [hy.1]
    have h2' : 0 < 1 - y := by linarith [hy.2]
    rw [Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩, Real.log_div h1'.ne' h2'.ne']
  have hd := (((hasDerivAt_id x).const_add 1).log h1.ne').sub
    (((hasDerivAt_id x).const_sub 1).log h2.ne') |>.const_mul (1 / 2 : ℝ)
  refine (hd.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  have h3 : (1 - x ^ 2) ≠ 0 := by nlinarith
  simp only [id]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ θ in (0 : ℝ)..φ, Real.cos θ /
(1 - q ^ 2 * Real.sin θ ^ 2) = q⁻¹ * Real.artanh (q * Real.sin φ)`. -/
lemma p19lR1_integral_cos_div {q φ : ℝ} (hq : 0 < q) (hφ0 : 0 ≤ φ) (hφ1 : φ < π / 2)
    (hqs : q * Real.sin φ < 1) :
    ∫ θ in (0 : ℝ)..φ, Real.cos θ / (1 - q ^ 2 * Real.sin θ ^ 2) =
      q⁻¹ * Real.artanh (q * Real.sin φ) := by
  have hmem : ∀ θ ∈ uIcc 0 φ, q * Real.sin θ ∈ Ioo (-1 : ℝ) 1 := by
    intro θ hθ
    rw [uIcc_of_le hφ0] at hθ
    have h0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2])
    have h1 : Real.sin θ ≤ Real.sin φ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hθ.1, Real.pi_pos]) hφ1.le hθ.2
    exact ⟨by nlinarith, by nlinarith⟩
  have hden : ∀ θ ∈ uIcc 0 φ, 0 < 1 - q ^ 2 * Real.sin θ ^ 2 := by
    intro θ hθ
    have := hmem θ hθ
    nlinarith [this.1, this.2]
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ => q⁻¹ * Real.artanh (q * Real.sin θ))
    (f' := fun θ => Real.cos θ / (1 - q ^ 2 * Real.sin θ ^ 2)) (a := 0) (b := φ)
    (fun θ hθ => by
      have h := ((p19lR1_hasDerivAt_artanh (hmem θ hθ)).comp θ
        ((Real.hasDerivAt_sin θ).const_mul q)).const_mul q⁻¹
      refine h.congr_deriv ?_
      have := (hden θ hθ).ne'
      rw [mul_pow]
      field_simp)
    (ContinuousOn.intervalIntegrable (by
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun θ hθ => (hden θ hθ).ne'))
  rw [this]
  simp

/-- Cauchy–Schwarz for interval integrals of continuous nonnegative functions. -/
lemma p19lR1_cauchy_schwarz {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : Continuous f)
    (hg : Continuous g) (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x) :
    (∫ x in a..b, Real.sqrt (f x) * Real.sqrt (g x)) ^ 2 ≤
      (∫ x in a..b, f x) * ∫ x in a..b, g x := by
  set A := ∫ x in a..b, f x
  set B := ∫ x in a..b, g x
  set C := ∫ x in a..b, Real.sqrt (f x) * Real.sqrt (g x)
  have hsf : Continuous fun x => Real.sqrt (f x) := hf.sqrt
  have hsg : Continuous fun x => Real.sqrt (g x) := hg.sqrt
  have hq : ∀ t : ℝ, 0 ≤ A * (t * t) + (-2 * C) * t + B := by
    intro t
    have h0 : 0 ≤ ∫ x in a..b, (t * Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have hexp : ∫ x in a..b, (t * Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 =
        ∫ x in a..b, (t ^ 2 * f x - 2 * t * (Real.sqrt (f x) * Real.sqrt (g x)) + g x) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hab] at hx
      have h1 := Real.sq_sqrt (hf0 x hx)
      have h2 := Real.sq_sqrt (hg0 x hx)
      linear_combination t ^ 2 * h1 + h2
    rw [hexp, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
    · linarith
    all_goals first
      | exact (hf.intervalIntegrable _ _).const_mul _
      | exact ((hsf.mul hsg).intervalIntegrable _ _).const_mul _
      | exact hg.intervalIntegrable _ _
      | exact (((hf.intervalIntegrable _ _).const_mul _).sub
          (((hsf.mul hsg).intervalIntegrable _ _).const_mul _))
  have := discrim_le_zero hq
  rw [discrim] at this
  nlinarith

/-- Estimate under the stated parameter and domain assumptions: `c / ((a + b) / 2) ≤ c * (a⁻¹ +
b⁻¹) / 2`. -/
lemma p19lR1_hm_am {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) :
    c / ((a + b) / 2) ≤ c * (a⁻¹ + b⁻¹) / 2 := by
  rw [div_le_iff₀ (by positivity)]
  have : c * (a⁻¹ + b⁻¹) / 2 * ((a + b) / 2) = c * ((a + b) ^ 2 / (4 * a * b)) := by
    field_simp; ring
  rw [this]
  have h1 : 1 ≤ (a + b) ^ 2 / (4 * a * b) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (a - b)]
  nlinarith

/-- Estimate under the stated parameter and domain assumptions: `c / ((c ^ 2 + b) / 2) ≤
(Real.sqrt b)⁻¹`. -/
lemma p19lR1_gm_am {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    c / ((c ^ 2 + b) / 2) ≤ (Real.sqrt b)⁻¹ := by
  have hsb := Real.sq_sqrt hb.le
  have hsb0 := Real.sqrt_pos.2 hb
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hsb0]
  nlinarith [sq_nonneg (c - Real.sqrt b)]

/-- Identity under the stated parameter and domain assumptions: `Real.sqrt (c * ((c ^ 2)⁻¹ + b⁻¹)
/ 2) * Real.sqrt (c / ((c ^ 2 + b) / 2)) = (Real.sqrt b)⁻¹`. -/
lemma p19lR1_sqrt_AG {b c : ℝ} (hc : 0 < c) (hb : 0 < b) :
    Real.sqrt (c * ((c ^ 2)⁻¹ + b⁻¹) / 2) * Real.sqrt (c / ((c ^ 2 + b) / 2)) =
      (Real.sqrt b)⁻¹ := by
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_inv]
  congr 1
  field_simp
  ring

/-- DLMF 19.9.17–19.9.18 (Carlson 1961b): `L ≤ F(φ, k) ≤ √(UL) ≤ (U + L)/2 ≤ U` with
`L = σ⁻¹ arctanh(σ sin φ)`, `σ = √((1 + k²)/2)`, and
`U = ½ arctanh(sin φ) + ½ k⁻¹ arctanh(k sin φ)`, for `0 < k < 1`, `0 ≤ φ < π/2`. In the variable
`θ` the three integrands are `cos θ/√(ab)`, `cos θ (1/a + 1/b)/2` and `2 cos θ/(a + b)` with
`a = cos²θ`, `b = 1 - k² sin²θ`; the bounds follow from AM–GM and Cauchy–Schwarz. -/
@[dlmf 19.9.E17, dlmf 19.9.E18]
theorem incEllIntFk_arctanh_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ < π / 2) :
    let σ := Real.sqrt ((1 + k ^ 2) / 2)
    let L := σ⁻¹ * Real.artanh (σ * Real.sin φ)
    let U := Real.artanh (Real.sin φ) / 2 + k⁻¹ * Real.artanh (k * Real.sin φ) / 2
    L ≤ (incEllIntFk φ k).re ∧ (incEllIntFk φ k).re ≤ Real.sqrt (U * L) ∧
      Real.sqrt (U * L) ≤ (U + L) / 2 ∧ (U + L) / 2 ≤ U := by
  intro σ L U
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hσ2 : σ ^ 2 = (1 + k ^ 2) / 2 := Real.sq_sqrt (by positivity)
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by positivity)
  have hσ1 : σ < 1 := by nlinarith
  have hs0 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos])
  have hs1 : Real.sin φ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl hφ1
  -- pointwise data on `[0, φ]`
  have hc : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hb : ∀ θ : ℝ, 0 < 1 - k ^ 2 * Real.sin θ ^ 2 := fun θ =>
    DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ
  have hsq : ∀ θ : ℝ, 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := fun θ => by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  set A : ℝ → ℝ := fun θ => Real.cos θ * ((1 - Real.sin θ ^ 2)⁻¹ +
    (1 - k ^ 2 * Real.sin θ ^ 2)⁻¹) / 2 with hA
  set G : ℝ → ℝ := fun θ => Real.cos θ / (1 - σ ^ 2 * Real.sin θ ^ 2) with hG
  set Φ : ℝ → ℝ := fun θ => (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹ with hΦ
  have hF : (incEllIntFk φ k).re = ∫ θ in (0 : ℝ)..φ, Φ θ := by
    rw [ei19b_re_incEllIntFk hk2.le, DLMF.Elliptic.Real.incEllIntFm]
    exact intervalIntegral.integral_congr fun θ _ => ei19b_rpow_neg_half (hb θ).le
  have hU : U = ∫ θ in (0 : ℝ)..φ, A θ := by
    have h1 := p19lR1_integral_cos_div one_pos hφ0 hφ1 (by linarith)
    have h2 := p19lR1_integral_cos_div hk0 hφ0 hφ1 (by nlinarith)
    simp only [one_pow, one_mul, inv_one] at h1
    have hi1 : IntervalIntegrable (fun θ => Real.cos θ / (1 - Real.sin θ ^ 2)) volume 0 φ := by
      refine ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
      intro θ hθ; rw [uIcc_of_le hφ0] at hθ; rw [hsq]; exact pow_ne_zero _ (hc θ hθ).ne'
    have hi2 : IntervalIntegrable (fun θ => Real.cos θ / (1 - k ^ 2 * Real.sin θ ^ 2)) volume 0 φ :=
      (Continuous.div (by fun_prop) (by fun_prop) fun θ => (hb θ).ne').intervalIntegrable _ _
    have : (∫ θ in (0 : ℝ)..φ, A θ) = ((∫ θ in (0 : ℝ)..φ, Real.cos θ / (1 - Real.sin θ ^ 2)) +
        ∫ θ in (0 : ℝ)..φ, Real.cos θ / (1 - k ^ 2 * Real.sin θ ^ 2)) / 2 := by
      rw [← intervalIntegral.integral_add hi1 hi2, ← intervalIntegral.integral_div]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [hA]; ring
    rw [this, h1, h2]
    show Real.artanh (Real.sin φ) / 2 + k⁻¹ * Real.artanh (k * Real.sin φ) / 2 = _
    ring
  have hL : L = ∫ θ in (0 : ℝ)..φ, G θ :=
    (p19lR1_integral_cos_div hσ0 hφ0 hφ1 (by nlinarith)).symm
  have hab : ∀ θ ∈ Icc (0 : ℝ) φ, 1 - σ ^ 2 * Real.sin θ ^ 2 =
      ((1 - Real.sin θ ^ 2) + (1 - k ^ 2 * Real.sin θ ^ 2)) / 2 := fun θ _ => by
    rw [hσ2]; ring
  -- pointwise inequalities
  have hGΦ : ∀ θ ∈ Icc (0 : ℝ) φ, G θ ≤ Φ θ := by
    intro θ hθ
    simp only [hG, hΦ]
    rw [hab θ hθ, hsq]
    exact p19lR1_gm_am (hb θ) (hc θ hθ)
  have hGA : ∀ θ ∈ Icc (0 : ℝ) φ, G θ ≤ A θ := by
    intro θ hθ
    simp only [hG, hA]
    rw [hab θ hθ, hsq]
    exact p19lR1_hm_am (pow_pos (hc θ hθ) 2) (hb θ) (hc θ hθ).le
  have hAG : ∀ θ ∈ Icc (0 : ℝ) φ, Real.sqrt (A θ) * Real.sqrt (G θ) = Φ θ := by
    intro θ hθ
    simp only [hG, hA, hΦ]
    rw [hab θ hθ, hsq]
    exact p19lR1_sqrt_AG (hc θ hθ) (hb θ)
  have hG0 : ∀ θ ∈ Icc (0 : ℝ) φ, 0 ≤ G θ := fun θ hθ => by
    simp only [hG]; rw [hab θ hθ]
    exact div_nonneg (hc θ hθ).le (by linarith [hb θ, sq_nonneg (Real.sin θ), Real.sin_sq_le_one θ])
  have hA0 : ∀ θ ∈ Icc (0 : ℝ) φ, 0 ≤ A θ := fun θ hθ => (hG0 θ hθ).trans (hGA θ hθ)
  -- continuity
  have hdenσ : ∀ θ : ℝ, 0 < 1 - σ ^ 2 * Real.sin θ ^ 2 := fun θ => by
    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ)]
  have hGc : Continuous G := Continuous.div (by fun_prop) (by fun_prop) fun θ => (hdenσ θ).ne'
  have hΦc : Continuous Φ :=
    (Continuous.sqrt (by fun_prop)).inv₀ fun θ => (Real.sqrt_pos.2 (hb θ)).ne'
  -- `A` is continuous on `[0, φ]`; use a continuous extension for Cauchy–Schwarz
  have hAc : ContinuousOn A (Icc 0 φ) := by
    refine ContinuousOn.div_const (ContinuousOn.mul (by fun_prop) (ContinuousOn.add ?_ ?_)) _
    · refine ContinuousOn.inv₀ (by fun_prop) fun θ hθ => ?_
      rw [hsq]; exact pow_ne_zero _ (hc θ hθ).ne'
    · exact (Continuous.inv₀ (by fun_prop) fun θ => (hb θ).ne').continuousOn
  obtain ⟨A', hA'c, hA'eq⟩ : ∃ A' : ℝ → ℝ, Continuous A' ∧ EqOn A' A (Icc 0 φ) := by
    refine ⟨IccExtend hφ0 (domRestrict (Icc 0 φ) A), ?_, fun θ hθ => ?_⟩
    · exact continuous_IccExtend_iff.2 (hAc.domRestrict)
    · rw [IccExtend_of_mem hφ0 _ hθ]; rfl
  have hint_eq : ∀ {f g : ℝ → ℝ}, EqOn f g (Icc 0 φ) → ∫ θ in (0 : ℝ)..φ, f θ = ∫ θ in (0 : ℝ)..φ, g θ :=
    fun h => intervalIntegral.integral_congr (by rw [uIcc_of_le hφ0]; exact h)
  have hUA' : U = ∫ θ in (0 : ℝ)..φ, A' θ := by rw [hU]; exact (hint_eq hA'eq).symm
  have hcs := p19lR1_cauchy_schwarz hφ0 hA'c hGc (fun θ hθ => (hA'eq hθ).symm ▸ hA0 θ hθ) hG0
  have hFeq : (∫ θ in (0 : ℝ)..φ, Real.sqrt (A' θ) * Real.sqrt (G θ)) = (incEllIntFk φ k).re := by
    rw [hF]; exact hint_eq fun θ hθ => by rw [hA'eq hθ]; exact hAG θ hθ
  rw [hFeq, ← hUA', ← hL] at hcs
  have hLF : L ≤ (incEllIntFk φ k).re := by
    rw [hL, hF]
    exact intervalIntegral.integral_mono_on hφ0 (hGc.intervalIntegrable _ _)
      (hΦc.intervalIntegrable _ _) hGΦ
  have hLU : L ≤ U := by
    rw [hL, hUA']
    exact intervalIntegral.integral_mono_on hφ0 (hGc.intervalIntegrable _ _)
      (hA'c.intervalIntegrable _ _) fun θ hθ => (hA'eq hθ).symm ▸ hGA θ hθ
  have hL0 : 0 ≤ L := by rw [hL]; exact intervalIntegral.integral_nonneg hφ0 hG0
  have hF0 : 0 ≤ (incEllIntFk φ k).re := hL0.trans hLF
  have hU0 : 0 ≤ U := hL0.trans hLU
  refine ⟨hLF, ?_, ?_, by linarith⟩
  · rw [← Real.sqrt_sq hF0]; exact Real.sqrt_le_sqrt hcs
  · rw [← Real.sqrt_sq (by linarith : 0 ≤ (U + L) / 2)]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (U - L)])

end DLMF.EllipticIntegrals
