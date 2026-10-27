/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.IntegralRepresentations

/-!
# Growth of the regularized Kummer function on a ray

Euler's integral bounds the exponential factor by the positive part of the real
part of the ray direction. Parameter recurrences extend this bound to arbitrary
parameters, including poles of the unregularized denominator parameter.
The integral estimates use Mathlib's interval integral inequalities and FTC.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral
open scoped Real Topology

noncomputable section

namespace DLMF.Confluent

/-- Lowering the denominator parameter of the entire regularized Kummer function.
The reciprocal Gamma recurrence keeps this identity valid at Gamma poles. -/
theorem regularizedConfluent_lower_denominator (a c z : ℂ) :
    regularizedHGFun {a} {c} z = c * regularizedHGFun {a} {c + 1} z +
      a * z * regularizedHGFun {a + 1} {c + 2} z := by
  have hcoeff (n : ℕ) : regularizedHGFunCoeff {a} {c} n =
      (c + n) * regularizedHGFunCoeff {a} {c + 1} n := by
    rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_singleton,
      show c + 1 + n = c + n + 1 by ring]
    have h := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + n)
    simp only [div_eq_mul_inv, mul_inv_rev]
    rw [h]
    ring
  have hsucc (n : ℕ) : regularizedHGFunCoeff {a} {c} (n + 1) * z ^ (n + 1) =
      c * (regularizedHGFunCoeff {a} {c + 1} (n + 1) * z ^ (n + 1)) +
        (a * z) * (regularizedHGFunCoeff {a + 1} {c + 2} n * z ^ n) := by
    have h := regularizedHGFunCoeff_singleton_succ a (c + 1) n
    rw [show c + 1 + 1 = c + 2 by ring] at h
    rw [hcoeff, pow_succ]
    push_cast
    linear_combination z ^ n * z * h
  have hs (a c : ℂ) := (hasFPowerSeriesOnBall_regularizedConfluent a c).hasSum_mul_pow
    (z := z) (by simp)
  have ht (a c : ℂ) : HasSum
      (fun n => regularizedHGFunCoeff {a} {c} (n + 1) * z ^ (n + 1))
      (regularizedHGFun {a} {c} z - regularizedHGFunCoeff {a} {c} 0) := by
    simpa using (hasSum_nat_add_iff' 1).mpr (hs a c)
  have hsum := ((ht a (c + 1)).mul_left c).add ((hs (a + 1) (c + 2)).mul_left (a * z))
  have he := (ht a c).unique (hsum.congr_fun fun n => hsucc n)
  have hzero := hcoeff 0
  simp only [Nat.cast_zero, add_zero] at hzero
  linear_combination he + hzero

/-- Euler's integral gives an exponential bound in the positive-parameter region. -/
theorem regularizedConfluent_euler_growth {a c k : ℂ}
    (ha : 0 < a.re) (hca : 0 < (c - a).re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖regularizedHGFun {a} {c} (k * t)‖ ≤ C * Real.exp (max 0 k.re * t) := by
  let w (s : ℝ) : ℂ := (s : ℂ) ^ (a - 1) * (1 - (s : ℂ)) ^ (c - a - 1)
  have hw : IntervalIntegrable w volume 0 1 := betaIntegral_convergent ha hca
  let C : ℝ := ‖1 / (Gamma a * Gamma (c - a))‖ * |∫ s : ℝ in 0..1, ‖w s‖|
  refine ⟨C, by dsimp [C]; positivity, fun t ht => ?_⟩
  let E := Real.exp (max 0 k.re * t)
  have he (s : ℝ) (hs : s ∈ Set.uIoc (0 : ℝ) 1) : ‖exp (k * t * s)‖ ≤ E := by
    rw [Set.uIoc_of_le (by norm_num)] at hs
    simp only [Complex.norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    apply Real.exp_le_exp.mpr
    have hkt : k.re * t ≤ max 0 k.re * t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht
    have hσ : 0 ≤ max 0 k.re * t := mul_nonneg (le_max_left _ _) ht
    by_cases hk : 0 ≤ k.re * t
    · exact (mul_le_of_le_one_right hk hs.2).trans hkt
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hk) hs.1.le).trans hσ
  have hi : ‖∫ s : ℝ in 0..1, exp (k * t * s) * w s‖ ≤
      E * |∫ s : ℝ in 0..1, ‖w s‖| := by
    have h := intervalIntegral.norm_integral_le_abs_of_norm_le
      (f := fun s : ℝ => exp (k * t * s) * w s) (g := fun s => E * ‖w s‖)
      (by
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (he s hs) (norm_nonneg _))
      (hw.norm.const_mul E)
    simpa only [intervalIntegral.integral_const_mul, abs_mul,
      abs_of_pos (show 0 < E from Real.exp_pos _)] using h
  rw [regularized_euler_integral ha hca, norm_mul]
  have heq : (∫ s : ℝ in 0..1, exp (k * t * s) * (s : ℂ) ^ (a - 1) *
      (1 - (s : ℂ)) ^ (c - a - 1)) = ∫ s : ℝ in 0..1, exp (k * t * s) * w s := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp [w]
    ring
  rw [heq]
  calc
    _ ≤ ‖1 / (Gamma a * Gamma (c - a))‖ *
        (E * |∫ s : ℝ in 0..1, ‖w s‖|) := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    _ = _ := by dsimp [C, E]; ring

/-- A polynomial times the expected exponential bounds the Kummer function on a ray. -/
private def KummerRayBound (a c k : ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ t : ℝ, 0 ≤ t →
    ‖regularizedHGFun {a} {c} (k * t)‖ ≤ C * (1 + t) ^ N * Real.exp (max 0 k.re * t)

/-- The denominator-lowering recurrence preserves a polynomial exponential bound. -/
private lemma kummerRayBound_lower_denominator {a c k : ℂ}
    (h₁ : KummerRayBound a (c + 1) k) (h₂ : KummerRayBound (a + 1) (c + 2) k) :
    KummerRayBound a c k := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := h₁
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := h₂
  refine ⟨‖c‖ * C₁ + ‖a * k‖ * C₂, by positivity, N₁ + N₂ + 1, fun t ht => ?_⟩
  have hbase : 1 ≤ 1 + t := by linarith
  have hp₁ : (1 + t) ^ N₁ ≤ (1 + t) ^ (N₁ + N₂ + 1) :=
    pow_le_pow_right₀ hbase (by omega)
  have hp₂ : t * (1 + t) ^ N₂ ≤ (1 + t) ^ (N₁ + N₂ + 1) := by
    calc
      _ ≤ (1 + t) * (1 + t) ^ N₂ := by gcongr; linarith
      _ = (1 + t) ^ (N₂ + 1) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_right₀ hbase (by omega)
  rw [regularizedConfluent_lower_denominator]
  calc
    _ ≤ ‖c * regularizedHGFun {a} {c + 1} (k * t)‖ +
        ‖a * (k * t) * regularizedHGFun {a + 1} {c + 2} (k * t)‖ := norm_add_le _ _
    _ = ‖c‖ * ‖regularizedHGFun {a} {c + 1} (k * t)‖ +
        ‖a * k‖ * t * ‖regularizedHGFun {a + 1} {c + 2} (k * t)‖ := by
      rw [show a * (k * t) = (a * k) * t by ring]
      simp [Complex.norm_real, abs_of_nonneg ht]
    _ ≤ ‖c‖ * (C₁ * (1 + t) ^ N₁ * Real.exp (max 0 k.re * t)) +
        ‖a * k‖ * t * (C₂ * (1 + t) ^ N₂ * Real.exp (max 0 k.re * t)) := by
      gcongr
      · exact h₁ t ht
      · exact h₂ t ht
    _ = ‖c‖ * C₁ * (1 + t) ^ N₁ * Real.exp (max 0 k.re * t) +
        ‖a * k‖ * C₂ * (t * (1 + t) ^ N₂) * Real.exp (max 0 k.re * t) := by ring
    _ ≤ ‖c‖ * C₁ * (1 + t) ^ (N₁ + N₂ + 1) * Real.exp (max 0 k.re * t) +
        ‖a * k‖ * C₂ * (1 + t) ^ (N₁ + N₂ + 1) * Real.exp (max 0 k.re * t) := by
      gcongr
    _ = _ := by ring

/-- Positive first parameters admit a ray bound for every denominator parameter. -/
private lemma kummerRayBound_of_re_pos {a c k : ℂ} (ha : 0 < a.re) :
    KummerRayBound a c k := by
  have hshift : ∀ M : ℕ, ∀ a c : ℂ, 0 < a.re → 0 < (c - a).re + M →
      KummerRayBound a c k := by
    intro M
    induction M with
    | zero =>
      intro a c ha hca
      obtain ⟨C, hC, h⟩ := regularizedConfluent_euler_growth (k := k) ha (by simpa using hca)
      exact ⟨C, hC, 0, by simpa using h⟩
    | succ M ih =>
      intro a c ha hca
      apply kummerRayBound_lower_denominator
      · apply ih a (c + 1) ha
        simp only [sub_re, add_re, one_re, Nat.cast_add, Nat.cast_one] at hca ⊢
        linarith
      · apply ih (a + 1) (c + 2)
        · simp only [add_re, one_re]; linarith
        · simp only [sub_re, add_re, one_re, Nat.cast_add, Nat.cast_one] at hca ⊢
          norm_num at hca ⊢
          linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (-(c - a).re)
  exact hshift M a c ha (by linarith)

/-- Integrating the derivative lowers the first and second parameters together. -/
private lemma kummerRayBound_lower_both {a c k : ℂ}
    (h : KummerRayBound (a + 1) (c + 1) k) : KummerRayBound a c k := by
  obtain ⟨C, hC, N, h⟩ := h
  refine ⟨‖regularizedHGFun {a} {c} 0‖ + ‖a * k‖ * C, by positivity,
    N + 1, fun t ht => ?_⟩
  have hderiv (s : ℝ) : HasDerivAt (fun s : ℝ => regularizedHGFun {a} {c} (k * s))
      (a * k * regularizedHGFun {a + 1} {c + 1} (k * s)) s := by
    have hd := (differentiableAt_regularizedConfluent a c (k * s)).hasDerivAt
    rw [deriv_regularizedConfluent] at hd
    convert (hd.comp (s : ℂ) ((hasDerivAt_id (s : ℂ)).const_mul k)).comp_ofReal using 1
    · rfl
    · ring
  have hi : IntervalIntegrable (fun s : ℝ => a * k *
      regularizedHGFun {a + 1} {c + 1} (k * s)) volume 0 t := by
    apply Continuous.intervalIntegrable
    apply Continuous.const_mul
    exact continuous_regularizedConfluent.comp
      (show Continuous (fun s : ℝ => (a + 1, c + 1, k * (s : ℂ))) by fun_prop)
  have he : (∫ s : ℝ in 0..t, a * k * regularizedHGFun {a + 1} {c + 1} (k * s)) =
      regularizedHGFun {a} {c} (k * t) - regularizedHGFun {a} {c} 0 := by
    simpa only [Complex.ofReal_zero, mul_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hi
  have hbound : ‖∫ s : ℝ in 0..t, a * k * regularizedHGFun {a + 1} {c + 1} (k * s)‖ ≤
      ‖a * k‖ * C * (1 + t) ^ N * Real.exp (max 0 k.re * t) * t := by
    have hb (s : ℝ) (hs : s ∈ Set.uIoc 0 t) :
        ‖a * k * regularizedHGFun {a + 1} {c + 1} (k * s)‖ ≤
          ‖a * k‖ * C * (1 + t) ^ N * Real.exp (max 0 k.re * t) := by
      rw [Set.uIoc_of_le ht] at hs
      rw [norm_mul]
      calc
        _ ≤ ‖a * k‖ * (C * (1 + s) ^ N * Real.exp (max 0 k.re * s)) := by
          gcongr; exact h s hs.1.le
        _ = ‖a * k‖ * C * (1 + s) ^ N * Real.exp (max 0 k.re * s) := by ring
        _ ≤ _ := by
          gcongr <;> linarith [hs.1, hs.2]
    simpa only [sub_zero, abs_of_nonneg ht] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hp : (1 + t) ^ N * t ≤ (1 + t) ^ (N + 1) := by
    rw [pow_succ]
    gcongr
    linarith
  have hunit : 1 ≤ (1 + t) ^ (N + 1) * Real.exp (max 0 k.re * t) := by
    have hp : (1 : ℝ) ≤ (1 + t) ^ (N + 1) := one_le_pow₀ (by linarith)
    have he := Real.one_le_exp (mul_nonneg (le_max_left 0 k.re) ht)
    nlinarith
  calc
    _ = ‖regularizedHGFun {a} {c} 0 +
        ∫ s : ℝ in 0..t, a * k * regularizedHGFun {a + 1} {c + 1} (k * s)‖ := by
      congr 1
      rw [he]
      abel
    _ ≤ ‖regularizedHGFun {a} {c} 0‖ +
        ‖∫ s : ℝ in 0..t, a * k * regularizedHGFun {a + 1} {c + 1} (k * s)‖ := norm_add_le _ _
    _ ≤ ‖regularizedHGFun {a} {c} 0‖ +
        ‖a * k‖ * C * (1 + t) ^ N * Real.exp (max 0 k.re * t) * t := by gcongr
    _ ≤ ‖regularizedHGFun {a} {c} 0‖ * ((1 + t) ^ (N + 1) * Real.exp (max 0 k.re * t)) +
        ‖a * k‖ * C * ((1 + t) ^ (N + 1) * Real.exp (max 0 k.re * t)) := by
      apply add_le_add
      · exact le_mul_of_one_le_right (norm_nonneg _) hunit
      · calc
          _ = ‖a * k‖ * C * ((1 + t) ^ N * t) * Real.exp (max 0 k.re * t) := by ring
          _ ≤ _ := by
            calc
              _ ≤ ‖a * k‖ * C * (1 + t) ^ (N + 1) * Real.exp (max 0 k.re * t) := by
                gcongr
              _ = _ := by ring
    _ = _ := by ring

/-- The regularized Kummer function has polynomial exponential growth on every
positive ray, for arbitrary complex parameters. -/
theorem regularizedConfluent_ray_growth (a c k : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ t : ℝ, 0 ≤ t →
      ‖regularizedHGFun {a} {c} (k * t)‖ ≤ C * (1 + t) ^ N * Real.exp (max 0 k.re * t) := by
  have hshift : ∀ M : ℕ, ∀ a c : ℂ, 0 < a.re + M → KummerRayBound a c k := by
    intro M
    induction M with
    | zero => intro a c ha; exact kummerRayBound_of_re_pos (by simpa using ha)
    | succ M ih =>
      intro a c ha
      apply kummerRayBound_lower_both
      apply ih (a + 1) (c + 1)
      simp only [add_re, one_re, Nat.cast_add, Nat.cast_one] at ha ⊢
      linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (-a.re)
  exact hshift M a c (by linarith)

/-- Every polynomial Gamma majorant is integrable on the positive half-line. -/
theorem integrableOn_rpow_mul_one_add_pow_mul_exp {s δ : ℝ}
    (hs : -1 < s) (hδ : 0 < δ) (N : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ s * (1 + t) ^ N * Real.exp (-δ * t)) (Set.Ioi 0) := by
  let G (j : ℕ) (t : ℝ) := (N.choose j : ℝ) * (t ^ (s + j) * Real.exp (-δ * t))
  have hG (j : ℕ) : IntegrableOn (G j) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s + j) (b := δ)
      (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith) one_pos hδ
    simp only [Real.rpow_one] at h
    exact h.const_mul _
  have hsum := integrable_finsetSum (Finset.range (N + 1)) (fun j _ => hG j)
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  rw [add_comm (1 : ℝ) t, add_pow, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [G]
  rw [Real.rpow_add ht, Real.rpow_natCast, one_pow]
  ring

/-- The growth bound dominates a Kummer Laplace kernel by a polynomial Gamma kernel. -/
private lemma norm_kummerLaplaceKernel_le {a b c k z : ℂ} {C δ : ℝ} {N : ℕ}
    (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 ≤ t → ‖regularizedHGFun {a} {c} (k * t)‖ ≤
      C * (1 + t) ^ N * Real.exp (max 0 k.re * t))
    (hz : δ ≤ z.re - max 0 k.re) {t : ℝ} (ht : 0 < t) :
    ‖exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t)‖ ≤
      C * (t ^ (b.re - 1) * (1 + t) ^ N * Real.exp (-δ * t)) := by
  rw [norm_mul, norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re, one_re]
  calc
    _ ≤ Real.exp (-z.re * t) * t ^ (b.re - 1) *
        (C * (1 + t) ^ N * Real.exp (max 0 k.re * t)) := by
      gcongr
      exact h t ht.le
    _ = C * (t ^ (b.re - 1) * (1 + t) ^ N *
        Real.exp (-(z.re - max 0 k.re) * t)) := by
      rw [show -(z.re - max 0 k.re) * t = -z.re * t + max 0 k.re * t by ring,
        Real.exp_add]
      ring
    _ ≤ _ := by gcongr

/-- Absolute convergence of the regularized Kummer Laplace transform in its full
half-plane, including all exceptional denominator parameters. -/
theorem laplace_regularizedHGFun_integrable {a b c k z : ℂ}
    (hb : 0 < b.re) (hz : max 0 k.re < z.re) :
    IntegrableOn (fun t : ℝ => exp (-z * t) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun {a} {c} (k * t)) (Set.Ioi 0) := by
  obtain ⟨C, hC, N, h⟩ := regularizedConfluent_ray_growth a c k
  have hR : Continuous (fun t : ℝ => regularizedHGFun {a} {c} (k * t)) :=
    continuous_regularizedConfluent.comp
      (show Continuous (fun t : ℝ => (a, c, k * (t : ℂ))) by fun_prop)
  have hRm := hR.measurable
  refine Integrable.mono'
    ((integrableOn_rpow_mul_one_add_pow_mul_exp (s := b.re - 1)
      (by linarith) (sub_pos.mpr hz) N).const_mul C)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_kummerLaplaceKernel_le hC h le_rfl ht

/-- Holomorphic dependence on the Laplace variable in the full convergence half-plane.
Mathlib's dominated differentiation theorem applies to a polynomial Gamma majorant. -/
theorem differentiableOn_laplace_regularizedHGFun (a b c k : ℂ) (hb : 0 < b.re) :
    DifferentiableOn ℂ (fun z => ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t))
      {z : ℂ | max 0 k.re < z.re} := by
  obtain ⟨C, hC, N, hRbound⟩ := regularizedConfluent_ray_growth a c k
  have hR : Continuous (fun t : ℝ => regularizedHGFun {a} {c} (k * t)) :=
    continuous_regularizedConfluent.comp
      (show Continuous (fun t : ℝ => (a, c, k * (t : ℂ))) by fun_prop)
  have hRm := hR.measurable
  intro z₀ hz₀
  change max 0 k.re < z₀.re at hz₀
  let δ : ℝ := (z₀.re - max 0 k.re) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hre (z : ℂ) (hz : z ∈ Metric.ball z₀ δ) : δ ≤ z.re - max 0 k.re := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hh := (abs_lt.mp ((abs_re_le_norm (z - z₀)).trans_lt hz)).1
    simp only [sub_re] at hh
    dsimp [δ] at *
    linarith
  have hmeas (z : ℂ) : AEStronglyMeasurable (fun t : ℝ => exp (-z * t) *
      (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t)) (volume.restrict (Set.Ioi 0)) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0))
    (F := fun z (t : ℝ) => exp (-z * t) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun {a} {c} (k * t))
    (F' := fun z (t : ℝ) => -(t : ℂ) * (exp (-z * t) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun {a} {c} (k * t)))
    (bound := fun t : ℝ => C * (t ^ b.re * (1 + t) ^ N * Real.exp (-δ * t)))
    (Metric.ball_mem_nhds _ hδ) (Eventually.of_forall hmeas)
    (laplace_regularizedHGFun_integrable hb hz₀)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    ((integrableOn_rpow_mul_one_add_pow_mul_exp (s := b.re) (by linarith) hδ N).const_mul C) ?_
  · exact hd.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    change 0 < t at ht
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht.le]
    have hn := norm_kummerLaplaceKernel_le (b := b) hC hRbound (hre z hz) ht
    calc
      _ ≤ t * (C * (t ^ (b.re - 1) * (1 + t) ^ N * Real.exp (-δ * t))) := by gcongr
      _ = _ := by
        have hp := Real.rpow_add_one ht.ne' (b.re - 1)
        rw [show b.re - 1 + 1 = b.re by ring] at hp
        rw [hp]
        ring
  · filter_upwards with t z _
    have hh := (((hasDerivAt_id z).neg.mul_const (t : ℂ)).cexp.mul_const
      ((t : ℂ) ^ (b - 1))).mul_const (regularizedHGFun {a} {c} (k * t))
    simp only [Pi.neg_apply, id_eq] at hh
    convert hh using 1
    ring

end DLMF.Confluent
