/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.Hermite
public import DLMF.Zeta.HurwitzIntegrals
public import DLMF.IncompleteGamma.ContinuedProperties
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# The holomorphic remainder in Lerch's logarithmic expansion

For `Re a > 0`, the Hermite correction is holomorphic in the strip `|Im w| < 2π`.
Subtracting an entire Kummer endpoint term gives a holomorphic function whose derivative
lowers the order and whose value at zero is the Hurwitz zeta function. Its Taylor series
provides the regular part of DLMF 25.14.3_1.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory DLMF.Confluent DLMF.Hypergeometric
open scoped Real Topology Nat

namespace DLMF.Zeta.LerchLogarithmic

/-- The entire endpoint term for the regularized ray integral, with principal powers. -/
def endpoint (s a w : ℂ) : ℂ :=
  a ^ (1 - s) * Gamma (1 - s) * regularizedHGFun {1 - s} {2 - s} (a * w)

/-- The regular part of the exponentially weighted Hermite representation. -/
def regularized (s a w : ℂ) : ℂ :=
  exp (a * w) * (a ^ (-s) / 2 + 2 * ∫ x in Ioi (0 : ℝ), LerchHermite.kernel s a w x) -
    endpoint s a w

/-- Differentiating the entire endpoint term lowers its order. -/
theorem hasDerivAt_endpoint {a s : ℂ} (ha : a ≠ 0) (hs : s ≠ 1) (w : ℂ) :
    HasDerivAt (endpoint s a) (endpoint (s - 1) a w) w := by
  have hG : Gamma (2 - s) = (1 - s) * Gamma (1 - s) := by
    simpa only [show (1 - s) + 1 = 2 - s by ring] using
      Gamma_add_one (1 - s) (sub_ne_zero.mpr hs.symm)
  have h := ((differentiableAt_regularizedConfluent (1 - s) (2 - s) (a * w)).hasDerivAt.comp w
    ((hasDerivAt_id w).const_mul a)).const_mul (a ^ (1 - s) * Gamma (1 - s))
  rw [deriv_regularizedConfluent] at h
  convert h using 1
  · rfl
  · simp only [endpoint, show 1 - (s - 1) = 2 - s by ring,
      show 2 - (s - 1) = 3 - s by ring,
      show 1 - s + 1 = 2 - s by ring, show 2 - s + 1 = 3 - s by ring]
    rw [hG, show 2 - s = (1 - s) + 1 by ring, cpow_add _ _ ha, cpow_one]
    ring

/-- The regularized Kummer function at zero gives the endpoint's elementary value. -/
theorem endpoint_zero {a s : ℂ} (hs : ∀ n : ℕ, s ≠ (n : ℂ) + 1) :
    endpoint s a 0 = a ^ (1 - s) / (1 - s) := by
  have hn : ∀ n : ℕ, 2 - s ≠ -(n : ℂ) := by
    intro n h
    apply hs (n + 1)
    push_cast
    linear_combination -h
  have hs1 : 1 - s ≠ 0 := sub_ne_zero.mpr (by simpa using (hs 0).symm)
  have hG : Gamma (2 - s) = (1 - s) * Gamma (1 - s) := by
    simpa only [show (1 - s) + 1 = 2 - s by ring] using Gamma_add_one (1 - s) hs1
  rw [endpoint, mul_zero, regularizedHGFun_zero, regularizedHGFunCoeff_singleton]
  simp only [pochhammer_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, one_mul,
    one_div, add_zero]
  have hΓ : Gamma (2 - s) ≠ 0 := Gamma_ne_zero hn
  field_simp [hΓ, hs1]
  rw [hG]
  ring

/-- The derivative in the logarithmic variable is a difference of adjacent-order kernels. -/
theorem hasDerivAt_kernel {a : ℂ} (ha : 0 < a.re) (s w : ℂ) (x : ℝ) :
    HasDerivAt (fun v => LerchHermite.kernel s a v x)
      (LerchHermite.kernel (s - 1) a w x - a * LerchHermite.kernel s a w x) w := by
  have hm : a - x * I ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have hp : a + x * I ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have h := ((((hasDerivAt_id w).const_mul (-(I * x))).cexp.mul_const
    ((a - x * I) ^ (-s))).sub
      (((hasDerivAt_id w).const_mul (I * x)).cexp.mul_const
        ((a + x * I) ^ (-s)))).div_const (2 * I) |>.div_const
          (Real.exp (2 * π * x) - 1 : ℝ)
  have heq : (fun v => LerchHermite.kernel s a v x) =
      fun v => (exp (-(I * x) * v) * (a - x * I) ^ (-s) -
        exp (I * x * v) * (a + x * I) ^ (-s)) /
        (2 * I) / (Real.exp (2 * π * x) - 1 : ℝ) := by
    funext v
    rw [LerchHermite.kernel_eq_cpow ha]
    congr 3
    congr 2
    ring
  rw [heq]
  convert h using 1
  · funext v; rfl
  rw [LerchHermite.kernel_eq_cpow ha, LerchHermite.kernel_eq_cpow ha]
  have hem : (a - x * I) ^ (-(s - 1)) = (a - x * I) ^ (-s) * (a - x * I) := by
    rw [show -(s - 1) = -s + 1 by ring, cpow_add _ _ hm, cpow_one]
  have hep : (a + x * I) ^ (-(s - 1)) = (a + x * I) ^ (-s) * (a + x * I) := by
    rw [show -(s - 1) = -s + 1 by ring, cpow_add _ _ hp, cpow_one]
  rw [hem, hep]
  simp only [neg_mul, id_eq]
  ring

/-- Absolute convergence permits differentiating the correction integral. -/
theorem hasDerivAt_integral_kernel {a w : ℂ} (ha : 0 < a.re)
    (hw : |w.im| < 2 * π) (s : ℂ) :
    HasDerivAt (fun v => ∫ x in Ioi (0 : ℝ), LerchHermite.kernel s a v x)
      ((∫ x in Ioi (0 : ℝ), LerchHermite.kernel (s - 1) a w x) -
        a * ∫ x in Ioi (0 : ℝ), LerchHermite.kernel s a w x) w := by
  have hd := hasDerivAt_integral_of_locally_dominated
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (Φ := fun v x => LerchHermite.kernel s a v x)
    (U := {v : ℂ | |v.im| < 2 * π})
    (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)
    (fun v _ => (LerchHermite.continuousOn_kernel ha s v).aestronglyMeasurable
      measurableSet_Ioi)
    (Eventually.of_forall fun x =>
      (LerchHermite.differentiable_kernel_argument ha s x).differentiableOn) ?_ hw
  · convert hd using 1
    rw [← integral_const_mul,
      ← integral_sub (LerchHermite.integrableOn_kernel ha hw (s - 1))
        ((LerchHermite.integrableOn_kernel ha hw s).const_mul a)]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => (hasDerivAt_kernel ha s w x).deriv.symm
  · intro v hv
    change |v.im| < 2 * π at hv
    let θ : ℝ := (2 * π + |v.im|) / 2
    have hθ0 : |v.im| < θ := by dsimp [θ]; linarith
    have hθ : θ < 2 * π := by dsimp [θ]; linarith
    obtain ⟨g, hg, hb⟩ := LerchHermite.exists_integrable_bound_kernel ha (norm_nonneg s)
      (L := ‖v‖ + 1) (by positivity) hθ
    refine ⟨Metric.ball v 1 ∩ {t : ℂ | |t.im| < θ},
      Filter.inter_mem (Metric.ball_mem_nhds v one_pos)
        ((isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds hθ0),
      g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t ht
    have ht' : ‖t‖ ≤ ‖v‖ + 1 := by
      have hdist : ‖t - v‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using ht.1
      have htri := norm_add_le (t - v) v
      rw [sub_add_cancel] at htri
      linarith
    exact hb s t le_rfl ht' ht.2.le x hx

/-- The holomorphic remainder satisfies the adjacent-order derivative recurrence. -/
theorem hasDerivAt_regularized {a s w : ℂ} (ha : 0 < a.re) (hs : s ≠ 1)
    (hw : |w.im| < 2 * π) :
    HasDerivAt (regularized s a) (regularized (s - 1) a w) w := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have h := ((((hasDerivAt_id w).const_mul a).cexp).mul
    (((hasDerivAt_integral_kernel ha hw s).const_mul 2).const_add (a ^ (-s) / 2))).sub
      (hasDerivAt_endpoint ha0 hs w)
  convert h using 1
  · rfl
  · rw [regularized, show -(s - 1) = -s + 1 by ring, cpow_add _ _ ha0, cpow_one]
    simp only [id_eq]
    ring

/-- Evaluating the regular part at zero recovers Hermite's Hurwitz-zeta formula. -/
theorem regularized_zero {a s : ℂ} (ha : 0 < a.re)
    (hs : ∀ n : ℕ, s ≠ (n : ℂ) + 1) :
    regularized s a 0 = hurwitzZetaComplex s a := by
  rw [regularized, mul_zero, exp_zero, one_mul, endpoint_zero hs,
    hurwitzZetaComplex_hermite (by simpa using hs 0) ha]
  have heq : (∫ x in Ioi (0 : ℝ), LerchHermite.kernel s a 0 x) =
      ∫ x in Ioi (0 : ℝ), sin (s * arctan (x / a)) /
        ((a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) * (Real.exp (2 * π * x) - 1 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [LerchHermite.kernel, mul_zero, sub_zero, div_div]
  rw [heq]
  rw [show s - 1 = -(1 - s) by ring, div_neg]
  ring

/-- Subtracting a natural number preserves exclusion of positive integer orders. -/
theorem ne_natCast_add_one_sub_natCast {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ (n : ℂ) + 1) (m : ℕ) :
    ∀ n : ℕ, s - m ≠ (n : ℂ) + 1 := by
  intro n h
  apply hs (m + n)
  push_cast
  linear_combination h

/-- Every logarithmic derivative lowers the order of the holomorphic remainder. -/
theorem iteratedDeriv_regularized {a : ℂ} (ha : 0 < a.re) (n : ℕ) {s w : ℂ}
    (hs : ∀ k : ℕ, s ≠ (k : ℂ) + 1) (hw : |w.im| < 2 * π) :
    iteratedDeriv n (regularized s a) w = regularized (s - n) a w := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have heq : deriv (regularized s a) =ᶠ[𝓝 w] regularized (s - 1) a := by
      filter_upwards [(isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds
        hw] with v hv
      exact (hasDerivAt_regularized ha (by simpa using hs 0) hv).deriv
    rw [heq.iteratedDeriv_eq n, ih (by simpa using ne_natCast_add_one_sub_natCast hs 1)]
    congr 1
    push_cast
    ring

/-- The Taylor coefficients of the regularized Hermite formula are the Hurwitz zeta values. -/
theorem hasSum_regularized {a s w : ℂ} (ha : 0 < a.re)
    (hs : ∀ n : ℕ, s ≠ (n : ℂ) + 1) (hw : ‖w‖ < 2 * π) :
    HasSum (fun n : ℕ => hurwitzZetaComplex (s - n) a * w ^ n / n !)
      (regularized s a w) := by
  have hf : DifferentiableOn ℂ (regularized s a) (Metric.ball 0 (2 * π)) := by
    intro v hv
    have hv' : ‖v‖ < 2 * π := by simpa [Metric.mem_ball, dist_zero_right] using hv
    exact (hasDerivAt_regularized ha (by simpa using hs 0)
      ((abs_im_le_norm v).trans_lt hv')).differentiableAt.differentiableWithinAt
  have h := Complex.hasSum_taylorSeries_on_ball hf
    (z := w) (by simpa [Metric.mem_ball, dist_zero_right] using hw)
  convert h using 1
  funext n
  rw [iteratedDeriv_regularized ha n hs (by simp; positivity),
    regularized_zero ha (ne_natCast_add_one_sub_natCast hs n)]
  simp only [sub_zero, smul_eq_mul]
  ring

end DLMF.Zeta.LerchLogarithmic
