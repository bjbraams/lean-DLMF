/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.SecondKind
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma

/-!
# The noncentral chi-squared distribution and Marcum's Q-function (Temme §11.4)

Temme writes the noncentral chi-squared distribution with `2μ` degrees of freedom and
noncentrality `2x` as Poisson mixtures of incomplete Gamma ratios,

`P_μ(x,y) = ∑ₙ e^{-x} xⁿ/n! · P(μ+n, y)`,  `Q_μ(x,y) = ∑ₙ e^{-x} xⁿ/n! · Q(μ+n, y)`,

for `μ > 0` and `x, y ≥ 0`, where `P = TauCeti.regularizedGamma` and `Q = 1 - P`. `Q_μ` is the
generalized Marcum Q-function `Q_μ(√(2x), √(2y))`.

## Main results

* `hasSum_poissonWeight`: the Poisson weights `e^{-x} xⁿ/n!` sum to `1`.
* `marcumP_add_marcumQ`: `P_μ(x,y) + Q_μ(x,y) = 1`.
* `marcumP_nonneg`, `marcumP_le_one`: `0 ≤ P_μ(x,y) ≤ 1`.
* `marcumP_zero_left`: `P_μ(0,y) = P(μ,y)`.
* `marcumQ_add_one`: `Q_{μ+1}(x,y) = Q_μ(x,y) + (y/x)^{μ/2} e^{-x-y} I_μ(2√(xy))` (Temme (11.64)).
* `marcumQ_recurrence`: `x Q_{μ+2} = (x-μ) Q_{μ+1} + (y+μ) Q_μ - y Q_{μ-1}` (Temme (11.65)).
* `marcumQ_eq_integral`: `Q_μ(x,y) = ∫_y^∞ (t/x)^{(μ-1)/2} e^{-t-x} I_{μ-1}(2√(xt)) dt`
  (Temme (11.63)).
-/

@[expose] public section

open Complex Filter Set
open scoped Real Nat Topology
open DLMF.Bessel

noncomputable section

namespace DLMF.Statistical

/-- The Poisson weight `e^{-x} xⁿ/n!`. -/
def poissonWeight (x : ℝ) (n : ℕ) : ℝ := Real.exp (-x) * x ^ n / n !

/-- The Poisson weights sum to `1`. -/
theorem hasSum_poissonWeight (x : ℝ) : HasSum (poissonWeight x) 1 := by
  have h : HasSum (fun n : ℕ => x ^ n / n !) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have h' := h.mul_left (Real.exp (-x))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h'
  refine h'.congr_fun fun n => ?_
  simp only [poissonWeight]
  ring

/-- For `x ≥ 0` the Poisson weight `e^{-x} xⁿ/n!` is nonnegative. -/
theorem poissonWeight_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ poissonWeight x n := by
  unfold poissonWeight; positivity

/-- The noncentral chi-squared distribution function `P_μ(x,y)` (Temme (11.62)). -/
def marcumP (μ x y : ℝ) : ℝ :=
  ∑' n : ℕ, poissonWeight x n * TauCeti.regularizedGamma (μ + n) y

/-- The complementary function `Q_μ(x,y)`, the generalized Marcum Q-function (Temme (11.61)). -/
def marcumQ (μ x y : ℝ) : ℝ :=
  ∑' n : ℕ, poissonWeight x n * (1 - TauCeti.regularizedGamma (μ + n) y)

/-- For `x ≥ 0`, the series `∑ₙ e^{-x} xⁿ/n! · P(μ+n, y)` defining `marcumP μ x y` converges. -/
theorem summable_marcumP_term (μ : ℝ) {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    Summable fun n : ℕ => poissonWeight x n * TauCeti.regularizedGamma (μ + n) y :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg hx n) (TauCeti.regularizedGamma_nonneg _ _))
    (fun n => mul_le_of_le_one_right (poissonWeight_nonneg hx n)
      (TauCeti.regularizedGamma_le_one _ _))
    (hasSum_poissonWeight x).summable

/-- For `x ≥ 0`, the series `∑ₙ e^{-x} xⁿ/n! · (1 - P(μ+n, y))` defining `marcumQ μ x y`
converges. -/
theorem summable_marcumQ_term (μ : ℝ) {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    Summable fun n : ℕ => poissonWeight x n * (1 - TauCeti.regularizedGamma (μ + n) y) := by
  simp_rw [mul_sub, mul_one]
  exact (hasSum_poissonWeight x).summable.sub (summable_marcumP_term μ hx y)

/-- `P_μ(x,y) + Q_μ(x,y) = 1`. -/
theorem marcumP_add_marcumQ (μ : ℝ) {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    marcumP μ x y + marcumQ μ x y = 1 := by
  rw [marcumP, marcumQ, ← (summable_marcumP_term μ hx y).tsum_add (summable_marcumQ_term μ hx y)]
  simp_rw [← mul_add, add_sub_cancel, mul_one]
  exact (hasSum_poissonWeight x).tsum_eq

/-- `0 ≤ P_μ(x,y)`. -/
theorem marcumP_nonneg (μ : ℝ) {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ marcumP μ x y :=
  tsum_nonneg fun n =>
    mul_nonneg (poissonWeight_nonneg hx n) (TauCeti.regularizedGamma_nonneg _ _)

/-- `P_μ(x,y) ≤ 1`. -/
theorem marcumP_le_one (μ : ℝ) {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : marcumP μ x y ≤ 1 := by
  rw [← (hasSum_poissonWeight x).tsum_eq]
  exact (summable_marcumP_term μ hx y).tsum_le_tsum
    (fun n => mul_le_of_le_one_right (poissonWeight_nonneg hx n)
      (TauCeti.regularizedGamma_le_one _ _)) (hasSum_poissonWeight x).summable

/-- With zero noncentrality, `P_μ(0,y) = P(μ,y)`, the central chi-squared distribution. -/
theorem marcumP_zero_left (μ y : ℝ) : marcumP μ 0 y = TauCeti.regularizedGamma μ y := by
  rw [marcumP, tsum_eq_single 0 fun n hn => by simp [poissonWeight, zero_pow hn]]
  simp [poissonWeight]

/-- The Bessel series `(xy)^{-μ/2} I_μ(2√(xy)) = ∑ (xy)ⁿ / (n! Γ(μ+1+n))` for `x, y ≥ 0`. -/
theorem besselI_two_sqrt_mul (μ : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    besselI μ ((2 * Real.sqrt (x * y) : ℝ) : ℂ) =
      ((Real.sqrt (x * y) ^ μ * ∑' n : ℕ, (x * y) ^ n / n ! / Real.Gamma (μ + 1 + n) : ℝ) : ℂ) := by
  have hs : 0 ≤ Real.sqrt (x * y) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (x * y) ^ 2 = x * y := Real.sq_sqrt (mul_nonneg hx hy)
  rw [besselI, regularized0F1_eq_tsum]
  conv_rhs => rw [ofReal_mul, ofReal_tsum, ofReal_cpow hs]
  congr 1
  · congr 1; push_cast; ring
  · refine tsum_congr fun n => ?_
    rw [show ((2 * Real.sqrt (x * y) : ℝ) : ℂ) ^ 2 / 4 = ((x * y : ℝ) : ℂ) by
      have : ((Real.sqrt (x * y) : ℝ) : ℂ) ^ 2 = (x : ℂ) * y := by
        rw [← ofReal_pow, hsq]; push_cast; ring
      push_cast; linear_combination this]
    rw [show (μ : ℂ) + 1 + n = ((μ + 1 + n : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal]
    push_cast
    ring

/-- `(y/x)^{μ/2} (√(xy))^μ = y^μ` for `x, y > 0`. -/
theorem div_rpow_mul_sqrt_rpow (μ : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y / x) ^ (μ / 2) * Real.sqrt (x * y) ^ μ = y ^ μ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), show 1 / 2 * μ = μ / 2 by ring,
    ← Real.mul_rpow (by positivity)
    (by positivity), show y / x * (x * y) = y ^ (2 : ℝ) by field_simp; ring_nf; norm_num,
    ← Real.rpow_mul hy.le]
  ring_nf

/-- **Recurrence in `μ`** (Temme (11.64)): for `μ, x, y > 0`,
`Q_{μ+1}(x,y) = Q_μ(x,y) + (y/x)^{μ/2} e^{-x-y} I_μ(2√(xy))`. -/
theorem marcumQ_add_one {μ x y : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hy : 0 < y) :
    (marcumQ (μ + 1) x y : ℂ) = marcumQ μ x y +
      (((y / x) ^ (μ / 2) * Real.exp (-x - y) : ℝ) : ℂ) *
        besselI μ ((2 * Real.sqrt (x * y) : ℝ) : ℂ) := by
  have hdiff : marcumQ (μ + 1) x y - marcumQ μ x y =
      Real.exp (-x - y) * y ^ μ * ∑' n : ℕ, (x * y) ^ n / n ! / Real.Gamma (μ + 1 + n) := by
    rw [marcumQ, marcumQ, ← (summable_marcumQ_term (μ + 1) hx.le y).tsum_sub
      (summable_marcumQ_term μ hx.le y), ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have hn : (0 : ℝ) < μ + n := by positivity
    rw [show μ + 1 + (n : ℝ) = μ + n + 1 by ring,
      TauCeti.regularizedGamma_add_one hn hy.le, Real.rpow_add hy, Real.rpow_natCast,
      poissonWeight, show -x - y = -x + -y by ring, Real.exp_add, mul_pow]
    ring
  rw [besselI_two_sqrt_mul μ hx.le hy.le, ← ofReal_mul, ← ofReal_add]
  congr 1
  rw [← mul_assoc, show (y / x) ^ (μ / 2) * Real.exp (-x - y) * Real.sqrt (x * y) ^ μ =
    Real.exp (-x - y) * ((y / x) ^ (μ / 2) * Real.sqrt (x * y) ^ μ) by ring,
    div_rpow_mul_sqrt_rpow μ hx hy]
  linarith

/-- The coefficient `(y/x)^{ν/2} e^{-x-y}` of the Marcum recurrence. -/
def marcumCoeff (ν x y : ℝ) : ℝ := (y / x) ^ (ν / 2) * Real.exp (-x - y)

/-- For `x, y > 0`, `x · marcumCoeff (μ+1) x y = √(xy) · marcumCoeff μ x y`. -/
theorem x_mul_marcumCoeff_add_one (μ : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * marcumCoeff (μ + 1) x y = marcumCoeff μ x y * Real.sqrt (x * y) := by
  have hq : 0 < y / x := div_pos hy hx
  have hs : x * Real.sqrt (y / x) = Real.sqrt (x * y) := by
    rw [← Real.sqrt_sq hx.le, ← Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx.le]
    congr 1; field_simp
  rw [marcumCoeff, marcumCoeff, show (μ + 1) / 2 = μ / 2 + 1 / 2 by ring, Real.rpow_add hq,
    ← Real.sqrt_eq_rpow, ← hs]
  ring

/-- For `x, y > 0`, `y · marcumCoeff (μ-1) x y = √(xy) · marcumCoeff μ x y`. -/
theorem y_mul_marcumCoeff_sub_one (μ : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    y * marcumCoeff (μ - 1) x y = marcumCoeff μ x y * Real.sqrt (x * y) := by
  have hq : 0 < y / x := div_pos hy hx
  have hs : y = Real.sqrt (y / x) * Real.sqrt (x * y) := by
    rw [← Real.sqrt_mul hq.le, show y / x * (x * y) = y ^ 2 by field_simp, Real.sqrt_sq hy.le]
  have hr : (y / x) ^ (μ / 2) = (y / x) ^ ((μ - 1) / 2) * Real.sqrt (y / x) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hq]; ring_nf
  rw [marcumCoeff, marcumCoeff, hr]
  nth_rewrite 1 [hs]
  ring

/-- **The three-term recurrence** (Temme (11.65)): for `μ > 1` and `x, y > 0`,
`x Q_{μ+2} = (x - μ) Q_{μ+1} + (y + μ) Q_μ - y Q_{μ-1}`. -/
theorem marcumQ_recurrence {μ x y : ℝ} (hμ : 1 < μ) (hx : 0 < x) (hy : 0 < y) :
    x * marcumQ (μ + 2) x y =
      (x - μ) * marcumQ (μ + 1) x y + (y + μ) * marcumQ μ x y - y * marcumQ (μ - 1) x y := by
  have hA := marcumQ_add_one (μ := μ - 1) (by linarith) hx hy
  have hB := marcumQ_add_one (μ := μ) (by linarith) hx hy
  have hC := marcumQ_add_one (μ := μ + 1) (by linarith) hx hy
  rw [sub_add_cancel] at hA
  rw [show μ + 1 + 1 = μ + 2 by ring] at hC
  have hz : ((2 * Real.sqrt (x * y) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (by have := Real.sqrt_pos.mpr (mul_pos hx hy); positivity)
  have hR := besselI_sub_add (ν := (μ : ℂ)) hz
  have h1 := x_mul_marcumCoeff_add_one μ hx hy
  have h2 := y_mul_marcumCoeff_sub_one μ hx hy
  rw [show (y / x) ^ ((μ - 1) / 2) * Real.exp (-x - y) = marcumCoeff (μ - 1) x y from rfl] at hA
  rw [show (y / x) ^ (μ / 2) * Real.exp (-x - y) = marcumCoeff μ x y from rfl] at hB
  rw [show (y / x) ^ ((μ + 1) / 2) * Real.exp (-x - y) = marcumCoeff (μ + 1) x y from rfl] at hC
  rw [show ((μ - 1 : ℝ) : ℂ) = (μ : ℂ) - 1 by push_cast; ring] at hA
  rw [show ((μ + 1 : ℝ) : ℂ) = (μ : ℂ) + 1 by push_cast; ring] at hC
  have h1' : (x : ℂ) * (marcumCoeff (μ + 1) x y : ℂ) =
      (marcumCoeff μ x y : ℂ) * (Real.sqrt (x * y) : ℂ) := by exact_mod_cast h1
  have h2' : (y : ℂ) * (marcumCoeff (μ - 1) x y : ℂ) =
      (marcumCoeff μ x y : ℂ) * (Real.sqrt (x * y) : ℂ) := by exact_mod_cast h2
  apply ofReal_injective
  push_cast
  generalize besselI (μ : ℂ) ((2 * Real.sqrt (x * y) : ℝ) : ℂ) = I0 at *
  generalize besselI ((μ : ℂ) - 1) ((2 * Real.sqrt (x * y) : ℝ) : ℂ) = Im at *
  generalize besselI ((μ : ℂ) + 1) ((2 * Real.sqrt (x * y) : ℝ) : ℂ) = Ip at *
  push_cast at hR hz
  have hs0 : (Real.sqrt (x * y) : ℂ) ≠ 0 := by
    intro h; apply hz; rw [h, mul_zero]
  field_simp at hR
  linear_combination (x : ℂ) * hC + (μ : ℂ) * hB - (y : ℂ) * hA + Ip * h1' - Im * h2' +
    (marcumCoeff μ x y : ℂ) * hR

open MeasureTheory in
/-- The upper incomplete Gamma integral `∫_y^∞ t^{s-1} e^{-t} dt = Γ(s) (1 - P(s,y))`. -/
theorem integral_Ioi_rpow_mul_exp {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) :
    ∫ t in Ioi y, Real.exp (-t) * t ^ (s - 1) =
      Real.Gamma s * (1 - TauCeti.regularizedGamma s y) := by
  have hint := Real.GammaIntegral_convergent hs
  have hG := Real.Gamma_eq_integral hs
  rw [← Ioc_union_Ioi_eq_Ioi hy, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hy))] at hG
  have hlow := TauCeti.lowerIncompleteGamma_eq_integral hs hy
  rw [intervalIntegral.integral_of_le hy] at hlow
  have hGpos := Real.Gamma_pos_of_pos hs
  rw [TauCeti.regularizedGamma_eq_div, hlow, mul_sub, mul_one, mul_div_cancel₀ _ hGpos.ne']
  have : ∫ t in Ioc 0 y, t ^ (s - 1) * Real.exp (-t) =
      ∫ t in Ioc 0 y, Real.exp (-t) * t ^ (s - 1) :=
    setIntegral_congr_fun measurableSet_Ioc fun t _ => mul_comm _ _
  rw [this]
  linarith

open MeasureTheory in
/-- The real form of the Bessel integral for `Q_μ`. -/
theorem marcumQ_eq_integral_series {μ x y : ℝ} (hμ : 0 < μ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    marcumQ μ x y = ∫ t in Ioi y, Real.exp (-x - t) * t ^ (μ - 1) *
      ∑' n : ℕ, (x * t) ^ n / n ! / Real.Gamma (μ - 1 + 1 + n) := by
  set F : ℕ → ℝ → ℝ := fun n t =>
    poissonWeight x n * (Real.exp (-t) * t ^ (μ + n - 1) / Real.Gamma (μ + n)) with hF
  have hint (n : ℕ) : Integrable (F n) (volume.restrict (Ioi y)) := by
    have hs : (0 : ℝ) < μ + n := by positivity
    exact (((Real.GammaIntegral_convergent hs).mono_set (Ioi_subset_Ioi hy)).div_const
      _).const_mul _
  have hval (n : ℕ) : ∫ t in Ioi y, F n t =
      poissonWeight x n * (1 - TauCeti.regularizedGamma (μ + n) y) := by
    have hs : (0 : ℝ) < μ + n := by positivity
    rw [hF, integral_const_mul, integral_div, integral_Ioi_rpow_mul_exp hs hy,
      mul_div_cancel_left₀ _ (Real.Gamma_pos_of_pos hs).ne']
  have hnorm (n : ℕ) : ∫ t in Ioi y, ‖F n t‖ = ∫ t in Ioi y, F n t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_of_le_of_lt hy ht
    have hs : (0 : ℝ) < μ + n := by positivity
    refine Real.norm_of_nonneg (mul_nonneg (poissonWeight_nonneg hx n) ?_)
    have := Real.Gamma_pos_of_pos hs
    positivity
  have hsum : Summable fun n => ∫ t in Ioi y, ‖F n t‖ := by
    simp_rw [hnorm, hval]
    exact summable_marcumQ_term μ hx y
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hval] at key
  rw [marcumQ, key]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := lt_of_le_of_lt hy ht
  simp only [hF, poissonWeight]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [show μ + n - 1 = μ - 1 + n by ring, Real.rpow_add ht0, Real.rpow_natCast,
    show μ - 1 + 1 + (n : ℝ) = μ + n by ring, show -x - t = -x + -t by ring, Real.exp_add,
    mul_pow]
  ring

/-- **The Bessel integral for `Q_μ`** (Temme (11.63)): for `μ, x > 0` and `y ≥ 0`,
`Q_μ(x,y) = ∫_y^∞ (t/x)^{(μ-1)/2} e^{-t-x} I_{μ-1}(2√(xt)) dt`. -/
theorem marcumQ_eq_integral {μ x y : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hy : 0 ≤ y) :
    (marcumQ μ x y : ℂ) = ∫ t in Ioi y, (((t / x) ^ ((μ - 1) / 2) * Real.exp (-t - x) : ℝ) : ℂ) *
      besselI ((μ - 1 : ℝ) : ℂ) ((2 * Real.sqrt (x * t) : ℝ) : ℂ) := by
  rw [marcumQ_eq_integral_series hμ hx.le hy, ← integral_complex_ofReal]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := lt_of_le_of_lt hy ht
  rw [besselI_two_sqrt_mul (μ - 1) hx.le ht0.le, ← ofReal_mul]
  congr 1
  have h := div_rpow_mul_sqrt_rpow (μ - 1) hx ht0
  rw [show -t - x = -x - t by ring]
  calc Real.exp (-x - t) * t ^ (μ - 1) *
        ∑' n : ℕ, (x * t) ^ n / n ! / Real.Gamma (μ - 1 + 1 + n)
      = Real.exp (-x - t) * ((t / x) ^ ((μ - 1) / 2) * Real.sqrt (x * t) ^ (μ - 1)) *
        ∑' n : ℕ, (x * t) ^ n / n ! / Real.Gamma (μ - 1 + 1 + n) := by rw [h]
    _ = _ := by ring

end DLMF.Statistical
