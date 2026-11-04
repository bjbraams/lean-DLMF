/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Integrals.FerrersDiagonal
public import DLMF.OrthogonalPolynomials.Legendre
public import DLMF.OrthogonalPolynomials.Topics
public import DLMF.Legendre.IntegerTheory
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The Legendre series of the Ferrers function `𝖯_ν`

For `ν` not an integer, the Ferrers function `𝖯_ν` on `(-1,1)` is the sum of its Legendre series
`∑ (-1)ⁿ (sin νπ/π) (2n+1)/((ν-n)(ν+n+1)) Pₙ(x)`, which converges absolutely by Temme's bound
`|Pₙ(cos θ)| ≤ √(π/(2n))/sin θ`. The sum is identified with `𝖯_ν` by computing its Legendre
moments (DLMF 14.17.10) and by the completeness of the Legendre polynomials, which follows from
the Weierstrass approximation theorem. This gives DLMF 14.18.8 in `DLMF.Legendre.Sums`.

## Main results

* `ZonalSeries.eqOn_zero_of_integral_mul_legendrePolynomialP_eq_zero`: a function continuous on
  `(-1,1)`, integrable on `[-1,1]`, with vanishing Legendre moments vanishes on `(-1,1)`.
* `ZonalSeries.hasSum_legendreCoeff_mul`: the Legendre series of `𝖯_ν`, `ν ∉ ℤ`.
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Real Topology

noncomputable section

namespace DLMF.Legendre

open DLMF.OrthogonalPolynomials

namespace ZonalSeries


/-- Vanishing Legendre moments give vanishing moments of `xᵏ Pₘ`, by the recurrence. -/
private theorem integral_mul_pow_mul_eq_zero {h : ℝ → ℂ}
    (hi : IntervalIntegrable h volume (-1) 1)
    (hz : ∀ m, ∫ x in (-1:ℝ)..1, h x * legendrePolynomialP m x = 0) (k m : ℕ) :
    ∫ x in (-1:ℝ)..1, h x * ((x:ℂ) ^ k * legendrePolynomialP m x) = 0 := by
  induction k generalizing m with
  | zero => simpa using hz m
  | succ k ih =>
    have hint : ∀ j, IntervalIntegrable
        (fun x : ℝ => h x * ((x:ℂ) ^ k * legendrePolynomialP j x)) volume (-1) 1 := fun j =>
      hi.mul_continuousOn ((continuous_ofReal.pow k).mul
        (continuous_legendrePolynomialP_ofReal j)).continuousOn
    rcases m with _ | n
    · have e : ∀ x : ℝ, h x * ((x:ℂ) ^ (k+1) * legendrePolynomialP 0 x) =
          h x * ((x:ℂ) ^ k * legendrePolynomialP 1 x) := by
        intro x; rw [legendrePolynomialP_zero, legendrePolynomialP_one]; ring
      simp_rw [e]; exact ih 1
    · have h3 : (2 * (n:ℂ) + 3) ≠ 0 := by norm_cast
      have e : ∀ x : ℝ, h x * ((x:ℂ) ^ (k+1) * legendrePolynomialP (n+1) x) =
          ((n+2)/(2*n+3) : ℂ) * (h x * ((x:ℂ) ^ k * legendrePolynomialP (n+2) x)) +
          ((n+1)/(2*n+3) : ℂ) * (h x * ((x:ℂ) ^ k * legendrePolynomialP n x)) := by
        intro x
        have hr := legendrePolynomialP_recurrence n x
        have hx : (x:ℂ) * legendrePolynomialP (n+1) x =
            ((n+2) * legendrePolynomialP (n+2) x + (n+1) * legendrePolynomialP n x) / (2*n+3) := by
          rw [eq_div_iff h3]; linear_combination -hr
        rw [pow_succ, mul_assoc ((x:ℂ) ^ k), hx]
        ring
      simp_rw [e]
      rw [intervalIntegral.integral_add ((hint _).const_mul _) ((hint _).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ih, ih]
      simp

/-- Vanishing Legendre moments give vanishing polynomial moments. -/
private theorem integral_mul_polynomial_eq_zero {h : ℝ → ℂ}
    (hi : IntervalIntegrable h volume (-1) 1)
    (hz : ∀ m, ∫ x in (-1:ℝ)..1, h x * legendrePolynomialP m x = 0) (q : Polynomial ℝ) :
    ∫ x in (-1:ℝ)..1, h x * ((q.eval x : ℝ) : ℂ) = 0 := by
  have e : ∀ x : ℝ, h x * ((q.eval x : ℝ) : ℂ) = ∑ i ∈ Finset.range (q.natDegree + 1),
      (q.coeff i : ℂ) * (h x * ((x:ℂ) ^ i * legendrePolynomialP 0 x)) := by
    intro x
    rw [Polynomial.eval_eq_sum_range]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [legendrePolynomialP_zero]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_mul_pow_mul_eq_zero hi hz, mul_zero]
  · intro i _
    exact (hi.mul_continuousOn ((continuous_ofReal.pow i).mul
        (continuous_legendrePolynomialP_ofReal 0)).continuousOn).const_mul _

/-- Vanishing Legendre moments give vanishing moments against continuous functions, by the
Weierstrass approximation theorem. -/
private theorem integral_mul_continuous_eq_zero {h : ℝ → ℂ}
    (hi : IntervalIntegrable h volume (-1) 1)
    (hz : ∀ m, ∫ x in (-1:ℝ)..1, h x * legendrePolynomialP m x = 0) {g : ℝ → ℝ}
    (hg : Continuous g) :
    ∫ x in (-1:ℝ)..1, h x * (g x : ℂ) = 0 := by
  set I := ∫ x in (-1:ℝ)..1, h x * (g x : ℂ)
  set C := ∫ x in (-1:ℝ)..1, ‖h x‖
  have hC : 0 ≤ C := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => norm_nonneg _
  have key : ∀ ε > 0, ‖I‖ ≤ ε * C := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 g hg.continuousOn ε hε
    have hgi : IntervalIntegrable (fun x : ℝ => h x * (g x : ℂ)) volume (-1) 1 :=
      hi.mul_continuousOn (continuous_ofReal.comp hg).continuousOn
    have hpi : IntervalIntegrable (fun x : ℝ => h x * ((p.eval x : ℝ) : ℂ)) volume (-1) 1 :=
      hi.mul_continuousOn (continuous_ofReal.comp p.continuous).continuousOn
    have hI : I = ∫ x in (-1:ℝ)..1, h x * (((g x - p.eval x : ℝ)) : ℂ) := by
      have := intervalIntegral.integral_sub hgi hpi
      rw [integral_mul_polynomial_eq_zero hi hz p, sub_zero] at this
      calc I = _ := this.symm
        _ = _ := by congr 1; funext x; push_cast; ring
    rw [hI, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_ (hi.norm.const_mul ε)
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, mul_comm ε]
    exact mul_le_mul_of_nonneg_left (hp x ⟨hx.1.le, hx.2⟩).le (norm_nonneg _)
  by_contra hne
  have hpos : 0 < ‖I‖ := norm_pos_iff.mpr hne
  have := key (‖I‖ / (2 * (C + 1))) (by positivity)
  have h2 : ‖I‖ / (2 * (C + 1)) * C < ‖I‖ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- A function continuous on `(-1,1)` and integrable on `[-1,1]` all of whose Legendre moments
vanish is zero on `(-1,1)`. -/
theorem eqOn_zero_of_integral_mul_legendrePolynomialP_eq_zero {h : ℝ → ℂ}
    (hc : ContinuousOn h (Ioo (-1) 1)) (hi : IntervalIntegrable h volume (-1) 1)
    (hz : ∀ m, ∫ x in (-1:ℝ)..1, h x * legendrePolynomialP m x = 0) :
    EqOn h 0 (Ioo (-1) 1) := by
  set F := (Ioo (-1:ℝ) 1).indicator h with hFdef
  have hiF : IntegrableOn h (Ioo (-1:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1:ℝ) ≤ 1)).mp hi
  have hF : Integrable F := (integrable_indicator_iff measurableSet_Ioo).mpr hiF
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hF.locallyIntegrable (fun g hg _ => by
    have e : (fun x => g x • F x) = (Ioo (-1:ℝ) 1).indicator (fun x => h x * (g x : ℂ)) := by
      funext x
      by_cases hx : x ∈ Ioo (-1:ℝ) 1
      · simp [F, hx, Complex.real_smul, mul_comm]
      · simp [F, hx]
    rw [e, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num)]
    exact integral_mul_continuous_eq_zero hi hz hg.continuous)
  have hae' : h =ᵐ[volume.restrict (Ioo (-1:ℝ) 1)] 0 := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae] with x hx hxI
    simpa [F, hxI] using hx
  exact Measure.eqOn_of_ae_eq hae' hc continuousOn_const
    (by rw [isOpen_Ioo.interior_eq]; exact subset_closure)

/-- Temme's bound in the variable `x`: `|Pₙ(x)| ≤ cₙ/√(1-x²)`, `c₀ = 1`, `cₙ = √(π/(2n))`. -/
private theorem norm_legendrePolynomialP_le_div_sqrt (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ‖legendrePolynomialP n x‖ ≤
      (if n = 0 then 1 else Real.sqrt (π / (2 * n))) / Real.sqrt (1 - x ^ 2) := by
  have h0 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr h0
  have hs1 : Real.sqrt (1 - x ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [legendrePolynomialP_zero, norm_one, ite_true]
    rw [le_div_iff₀ hs, one_mul]; exact hs1
  · have h := norm_legendrePolynomialP_cos_le n hn (θ := Real.arccos x) (Real.arccos_pos.mpr hx.2)
      (Real.arccos_lt_pi.mpr hx.1)
    rw [Real.cos_arccos hx.1.le hx.2.le, Real.sin_arccos] at h
    simpa [hn.ne'] using h

/-- The Legendre coefficients `(-1)ⁿ (sin νπ/π)(2n+1)/((ν-n)(ν+n+1))` of `𝖯_ν`. -/
def legendreCoeff (ν : ℂ) (n : ℕ) : ℂ :=
  sin (ν * π) / π * (-1) ^ n * (2 * n + 1) / ((ν - n) * (ν + n + 1))

/-- The constant of Temme's bound. -/
private def temmeMajorant (n : ℕ) : ℝ := if n = 0 then 1 else Real.sqrt (π / (2 * n))

/-- The Legendre coefficients times Temme's constants are summable, being `O(n^{-3/2})`. -/
private theorem summable_norm_legendreCoeff_mul (ν : ℂ) :
    Summable fun n => ‖legendreCoeff ν n‖ * temmeMajorant n := by
  set K := ‖sin (ν * π)‖ / π * 12 * Real.sqrt π
  refine Summable.of_norm_bounded_eventually_nat
    ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ) < 3 / 2)).mul_left K) ?_
  filter_upwards [eventually_gt_atTop ⌈2 * ‖ν‖⌉₊] with n hn
  have hn' : 2 * ‖ν‖ < n := Nat.lt_of_ceil_lt hn
  have hnr : (0:ℝ) < n := by linarith [norm_nonneg ν]
  have hn0 : n ≠ 0 := by exact_mod_cast hnr.ne'
  have h1 : (n:ℝ) / 2 ≤ ‖ν - n‖ := by
    have := norm_sub_norm_le (n:ℂ) ν
    rw [Complex.norm_natCast, norm_sub_rev] at this; linarith
  have h2 : (n:ℝ) / 2 ≤ ‖ν + n + 1‖ := by
    have := norm_sub_norm_le ((n:ℂ) + 1) (-ν)
    rw [sub_neg_eq_add, show (n:ℂ) + 1 + ν = ν + n + 1 by ring, norm_neg,
      show ((n:ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast] at this
    push_cast at this; linarith
  have hc : ‖legendreCoeff ν n‖ ≤ ‖sin (ν * π)‖ / π * (12 / n) := by
    rw [legendreCoeff, norm_div, norm_mul, norm_mul, norm_div, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, mul_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      show (2 * (n:ℂ) + 1) = ((2 * n + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : (n:ℝ) / 2 * (n / 2) ≤ ‖ν - n‖ * ‖ν + n + 1‖ :=
      mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) this) hnr]
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    nlinarith
  have ht : temmeMajorant n ≤ Real.sqrt π / Real.sqrt n := by
    simp only [temmeMajorant, hn0, ↓reduceIte]
    rw [Real.sqrt_div' _ (by positivity)]
    gcongr; nlinarith
  have hpow : ((n:ℝ) ^ (3 / 2 : ℝ))⁻¹ = 1 / (n * Real.sqrt n) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hnr, Real.rpow_one,
      ← Real.sqrt_eq_rpow, one_div]
  rw [Real.norm_of_nonneg (by unfold temmeMajorant; split_ifs <;> positivity), hpow]
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnr
  calc ‖legendreCoeff ν n‖ * temmeMajorant n
      ≤ (‖sin (ν * π)‖ / π * (12 / n)) * (Real.sqrt π / Real.sqrt n) :=
        mul_le_mul hc ht (by unfold temmeMajorant; split_ifs <;> positivity) (by positivity)
    _ = K * (1 / (n * Real.sqrt n)) := by simp only [K]; field_simp

/-- Temme's constants are nonnegative. -/
private theorem temmeMajorant_nonneg (n : ℕ) : 0 ≤ temmeMajorant n := by
  unfold temmeMajorant; split_ifs <;> positivity

/-- `(1-x²)^{-1/2} = 1/√(1-x²)`. -/
private theorem rpow_neg_half_eq {x : ℝ} (hx : 0 ≤ 1 - x ^ 2) :
    (1 - x ^ 2) ^ (-1 / 2 : ℝ) = 1 / Real.sqrt (1 - x ^ 2) := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hx, Real.sqrt_eq_rpow]
  exact (one_div _).symm

/-- `cos(mπ) = (-1)ᵐ` in `ℂ`. -/
private theorem complex_cos_nat_mul_pi (m : ℕ) : cos ((m : ℂ) * π) = (-1) ^ m := by
  rw [show (m : ℂ) * π = ((m * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
    Real.cos_nat_mul_pi]
  push_cast; rfl

/-- The Legendre moments of `𝖯_ν`, from DLMF 14.17.10. -/
private theorem integral_ferrersP_mul_legendrePolynomialP {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (m : ℕ) :
    ∫ x in (-1:ℝ)..1, ferrersP ν 0 x * legendrePolynomialP m x =
      legendreCoeff ν m * (2 / (2 * m + 1)) := by
  have hc : ∫ x in (-1:ℝ)..1, ferrersP ν 0 x * legendrePolynomialP m x =
      ∫ x in (-1:ℝ)..1, ferrersP ν 0 x * ferrersP m 0 x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hx1 hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    rw [ferrersP_nat_polynomial m ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩]
  have hνm : (m:ℂ) ≠ ν := fun h => hν m (by rw [← h]; simp)
  have h1 : (m:ℂ) ≠ -ν - 1 := fun h => hν (-(m + 1 : ℤ)) (by push_cast; linear_combination h)
  have hrν : LegendreQRegular ν 0 := fun n h => hν (-(n + 1 : ℤ)) (by push_cast; simpa using h)
  have hrm : LegendreQRegular (m:ℂ) 0 := fun n h => by
    have := congrArg re h; simp at this; linarith
  rw [hc, ferrers_product_integral_10 ν m hνm h1 hrν hrm, Complex.sin_nat_mul_pi,
    show ((m:ℂ) - ν) * π = m * π - ν * π by ring, Complex.sin_sub, Complex.sin_nat_mul_pi,
    complex_cos_nat_mul_pi, legendreCoeff]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have d1 : (m:ℂ) - ν ≠ 0 := sub_ne_zero.mpr hνm
  have d2 : (m:ℂ) + ν + 1 ≠ 0 := fun h => h1 (by linear_combination h)
  have d3 : ν - m ≠ 0 := sub_ne_zero.mpr hνm.symm
  have d4 : ν + m + 1 ≠ 0 := fun h => d2 (by linear_combination h)
  have d5 : (2 * (m:ℂ) + 1) ≠ 0 := by norm_cast
  field_simp
  ring

/-- For `ν ∉ ℤ` the Legendre series of `𝖯_ν` converges absolutely to `𝖯_ν` on `(-1,1)`. -/
theorem hasSum_legendreCoeff_mul {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {y : ℝ} (hy : y ∈ Ioo (-1:ℝ) 1) :
    HasSum (fun n : ℕ => legendreCoeff ν n * legendrePolynomialP n y) (ferrersP ν 0 y) := by
  set u : ℕ → ℝ := fun n => ‖legendreCoeff ν n‖ * temmeMajorant n with hudef
  have hu : Summable u := summable_norm_legendreCoeff_mul ν
  have hu0 : ∀ n, 0 ≤ u n := fun n => mul_nonneg (norm_nonneg _) (temmeMajorant_nonneg n)
  set w : ℝ → ℝ := fun x => (1 - x ^ 2) ^ (-1 / 2 : ℝ) with hwdef
  have hbd : ∀ n, ∀ x ∈ Ioo (-1:ℝ) 1, ‖legendreCoeff ν n * legendrePolynomialP n x‖ ≤
      u n * w x := by
    intro n x hx
    have h0 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    rw [norm_mul, hwdef, hudef]
    simp only
    rw [rpow_neg_half_eq h0, mul_assoc, mul_one_div]
    exact mul_le_mul_of_nonneg_left (norm_legendrePolynomialP_le_div_sqrt n hx) (norm_nonneg _)
  have hS : ∀ x ∈ Ioo (-1:ℝ) 1, HasSum (fun n => legendreCoeff ν n * legendrePolynomialP n x)
      (∑' n, legendreCoeff ν n * legendrePolynomialP n x) :=
    fun x hx => (Summable.of_norm_bounded (hu.mul_right (w x)) fun n => hbd n x hx).hasSum
  set S : ℝ → ℂ := fun x => ∑' n, legendreCoeff ν n * legendrePolynomialP n x with hSdef
  have hSc : ContinuousOn S (Ioo (-1) 1) := by
    intro x0 hx0
    have ha : |x0| < 1 := abs_lt.mpr ⟨hx0.1, hx0.2⟩
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (|x0| + 1) / 2 := ⟨_, rfl⟩
    have hr1 : r < 1 := by linarith
    have hr0 : |x0| < r := by linarith
    have hr00 : 0 < 1 - r ^ 2 := by nlinarith [abs_nonneg x0]
    have hsub : Ioo (-r) r ⊆ Ioo (-1) 1 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hcont : ContinuousOn S (Ioo (-r) r) := by
      refine continuousOn_tsum (u := fun n => u n * w r)
        (fun n => (continuous_const.mul (continuous_legendrePolynomialP_ofReal n)).continuousOn)
        (hu.mul_right _) ?_
      intro n x hx
      refine (hbd n x (hsub hx)).trans (mul_le_mul_of_nonneg_left ?_ (hu0 n))
      have hx2 : x ^ 2 ≤ r ^ 2 := by nlinarith [hx.1, hx.2]
      exact Real.rpow_le_rpow_of_nonpos hr00 (by linarith) (by norm_num)
    exact (hcont.continuousAt (Ioo_mem_nhds (by linarith [neg_abs_le x0])
      (by linarith [le_abs_self x0]))).continuousWithinAt
  have hw : IntervalIntegrable w volume (-1) 1 :=
    OrthogonalityIntegrals.intervalIntegrable_rpow (Or.inl rfl)
  have hm : ∀ m : ℕ, HasSum (fun n => ∫ x in (-1:ℝ)..1,
      legendreCoeff ν n * legendrePolynomialP n x * legendrePolynomialP m x)
      (∫ x in (-1:ℝ)..1, S x * legendrePolynomialP m x) := by
    intro m
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n x => u n * w x)
      (fun n => ((continuous_const.mul (continuous_legendrePolynomialP_ofReal n)).mul
        (continuous_legendrePolynomialP_ofReal m)).aestronglyMeasurable) ?_ ?_ ?_ ?_
    · intro n
      filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hx1 hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
      rw [norm_mul]
      calc _ ≤ (u n * w x) * 1 := mul_le_mul (hbd n x hx')
            (norm_legendrePolynomialP_le_one m (abs_le.mpr ⟨hx'.1.le, hx'.2.le⟩)) (norm_nonneg _)
            (le_trans (norm_nonneg _) (hbd n x hx'))
        _ = _ := mul_one _
    · exact Filter.Eventually.of_forall fun x _ => hu.mul_right _
    · simp_rw [tsum_mul_right]; exact hw.const_mul _
    · filter_upwards [Measure.ae_ne volume (1:ℝ)] with x hx1 hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      exact (hS x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩).mul_right _
  have hSm : ∀ m : ℕ, ∫ x in (-1:ℝ)..1, S x * legendrePolynomialP m x =
      legendreCoeff ν m * (2 / (2 * m + 1)) := by
    intro m
    refine (hm m).unique ?_
    have e : ∀ n, ∫ x in (-1:ℝ)..1, legendreCoeff ν n * legendrePolynomialP n x *
        legendrePolynomialP m x =
        if n = m then legendreCoeff ν m * (2 / (2 * m + 1)) else 0 := by
      intro n
      simp_rw [mul_assoc]
      rw [intervalIntegral.integral_const_mul, legendre_orthogonality]
      split_ifs with h
      · subst h; rfl
      · simp
    simp_rw [e]
    exact hasSum_ite_eq m _
  have hP : IntervalIntegrable (ferrersP ν 0) volume (-1) 1 := by
    refine (FerrersGreen.intervalIntegrable_PP ν 0).congr_uIoo fun x hx => ?_
    rw [Set.uIoo_of_le (by norm_num)] at hx
    have := ferrersP_nat_polynomial 0 hx
    simp only [Nat.cast_zero, legendrePolynomialP_zero] at this
    simp [this]
  have hSi : IntervalIntegrable S volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    refine ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
      (hw.const_mul (∑' n, u n))).mono' (hSc.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact tsum_of_norm_bounded (hu.hasSum.mul_right (w x)) fun n => hbd n x hx
  have hz : ∀ m : ℕ, ∫ x in (-1:ℝ)..1, (S x - ferrersP ν 0 x) * legendrePolynomialP m x = 0 := by
    intro m
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub
      (hSi.mul_continuousOn (continuous_legendrePolynomialP_ofReal m).continuousOn)
      (hP.mul_continuousOn (continuous_legendrePolynomialP_ofReal m).continuousOn),
      hSm, integral_ferrersP_mul_legendrePolynomialP hν, sub_self]
  have := eqOn_zero_of_integral_mul_legendrePolynomialP_eq_zero
    (hSc.sub (FerrersGreen.continuousOn_ferrersP ν))
    (hSi.sub hP) hz hy
  have h2 : S y = ferrersP ν 0 y := sub_eq_zero.mp (by simpa using this)
  rw [← h2]
  exact hS y hy

/-- Parity of the Legendre polynomials. -/
theorem legendrePolynomialP_neg (n : ℕ) (z : ℂ) :
    legendrePolynomialP n (-z) = (-1) ^ n * legendrePolynomialP n z := by
  simpa [legendrePolynomialP] using jacobi_reflection (α := 0) (β := 0) (by simp) (by simp) n z

end ZonalSeries

end DLMF.Legendre
