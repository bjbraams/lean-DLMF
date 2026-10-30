/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Lommel
public import DLMF.Bessel.Schlafli
public import DLMF.ErrorFunctions.AnalyticProperties
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import DLMF.Struve.Poisson

/-!
# Anger and Weber integral and series identities

Integral definitions, derivative formulas and regularized series identities for Anger and Weber
functions.

Source references and common attribution are retained in
`DLMF.Struve.AngerWeber`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel DLMF.Confluent

/-- Anger function defined by the finite cosine integral `π⁻¹ ∫₀π cos (νθ-z sin θ) dθ`. -/
@[dlmf 11.10.E1]
def angerJ (ν z : ℂ) : ℂ :=
  1/π*∫ θ : ℝ in 0..π, cos (ν*θ-z*Real.sin θ)

/-- Differentiation under the integral sign over a compact interval for a jointly continuous
integrand with jointly continuous complex derivative. -/
theorem hasDerivAt_intervalIntegral_of_continuous {F F' : ℂ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ z t, HasDerivAt (fun w => F w t) (F' z t) z) (a b : ℝ) (z₀ : ℂ) :
    HasDerivAt (fun z => ∫ t in a..b, F z t) (∫ t in a..b, F' z₀ t) z₀ := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z₀ 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn
    hF'.continuousOn
  have hFc : ∀ z, Continuous (F z) := fun z => hF.comp (Continuous.prodMk_right z)
  have hF'c : ∀ z, Continuous (F' z) := fun z => hF'.comp (Continuous.prodMk_right z)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds z₀ one_pos) (Eventually.of_forall fun z => (hFc z).aestronglyMeasurable)
    ((hFc z₀).intervalIntegrable _ _) (hF'c z₀).aestronglyMeasurable ?_ intervalIntegrable_const
    (Eventually.of_forall fun t _ z _ => hd z t)).2
  refine Eventually.of_forall fun t ht z hz => hC (z, t) ⟨Metric.ball_subset_closedBall hz, ?_⟩
  exact uIoc_subset_uIcc ht

/-- Derivative of the Anger function in its argument, as an integral. -/
theorem angerJ_hasDerivAt_arg (ν z : ℂ) :
    HasDerivAt (angerJ ν)
      (1/π*∫ θ : ℝ in 0..π, sin (ν*θ-z*Real.sin θ)*Real.sin θ) z := by
  refine (hasDerivAt_intervalIntegral_of_continuous
    (F := fun z (θ : ℝ) => cos (ν*θ-z*Real.sin θ))
    (F' := fun z (θ : ℝ) => sin (ν*θ-z*Real.sin θ)*Real.sin θ) (by fun_prop) (by fun_prop)
    (fun w t => ?_) 0 π z).const_mul _
  have := ((hasDerivAt_id' w).mul_const ((Real.sin t : ℂ))).const_sub (ν*t) |>.ccos
  convert this using 1
  ring

/-- Derivative of the Anger function in its order, as an integral. -/
theorem angerJ_hasDerivAt_order (ν z : ℂ) :
    HasDerivAt (fun ν => angerJ ν z)
      (1/π*∫ θ : ℝ in 0..π, -(sin (ν*θ-z*Real.sin θ)*θ)) ν := by
  refine (hasDerivAt_intervalIntegral_of_continuous
    (F := fun ν (θ : ℝ) => cos (ν*θ-z*Real.sin θ))
    (F' := fun ν (θ : ℝ) => -(sin (ν*θ-z*Real.sin θ)*θ)) (by fun_prop) (by fun_prop)
    (fun w t => ?_) 0 π ν).const_mul _
  have := ((hasDerivAt_id' w).mul_const ((t : ℂ))).sub_const (z*Real.sin t) |>.ccos
  convert this using 1
  ring

/-- Entire dependence on the argument. -/
theorem angerJ_entire (ν : ℂ) :
    Differentiable ℂ (angerJ ν) := by
  exact fun z => (angerJ_hasDerivAt_arg ν z).differentiableAt

/-- Entire dependence on the order. -/
theorem angerJ_entire_order (z : ℂ) :
    Differentiable ℂ (fun ν => angerJ ν z) := by
  exact fun ν => (angerJ_hasDerivAt_order ν z).differentiableAt

/-- Weber function defined by the finite sine integral `π⁻¹ ∫₀π sin (νθ-z sin θ) dθ`. -/
@[dlmf 11.10.E2]
def weberE (ν z : ℂ) : ℂ :=
  1/π*∫ θ : ℝ in 0..π, sin (ν*θ-z*Real.sin θ)

/-- Derivative of the Weber function in its argument, as an integral. -/
theorem weberE_hasDerivAt_arg (ν z : ℂ) :
    HasDerivAt (weberE ν)
      (1/π*∫ θ : ℝ in 0..π, -(cos (ν*θ-z*Real.sin θ)*Real.sin θ)) z := by
  refine (hasDerivAt_intervalIntegral_of_continuous
    (F := fun z (θ : ℝ) => sin (ν*θ-z*Real.sin θ))
    (F' := fun z (θ : ℝ) => -(cos (ν*θ-z*Real.sin θ)*Real.sin θ)) (by fun_prop) (by fun_prop)
    (fun w t => ?_) 0 π z).const_mul _
  have := ((hasDerivAt_id' w).mul_const ((Real.sin t : ℂ))).const_sub (ν*t) |>.csin
  convert this using 1
  ring

/-- Derivative of the Weber function in its order, as an integral. -/
theorem weberE_hasDerivAt_order (ν z : ℂ) :
    HasDerivAt (fun ν => weberE ν z)
      (1/π*∫ θ : ℝ in 0..π, cos (ν*θ-z*Real.sin θ)*θ) ν := by
  refine (hasDerivAt_intervalIntegral_of_continuous
    (F := fun ν (θ : ℝ) => sin (ν*θ-z*Real.sin θ))
    (F' := fun ν (θ : ℝ) => cos (ν*θ-z*Real.sin θ)*θ) (by fun_prop) (by fun_prop)
    (fun w t => ?_) 0 π ν).const_mul _
  have := ((hasDerivAt_id' w).mul_const ((t : ℂ))).sub_const (z*Real.sin t) |>.csin
  convert this using 1
  ring

/-- Entire dependence on the argument. -/
theorem weberE_entire (ν : ℂ) :
    Differentiable ℂ (weberE ν) := by
  exact fun z => (weberE_hasDerivAt_arg ν z).differentiableAt

/-- Entire dependence on the order. -/
theorem weberE_entire_order (z : ℂ) :
    Differentiable ℂ (fun ν => weberE ν z) := by
  exact fun ν => (weberE_hasDerivAt_order ν z).differentiableAt

/-- Continuous functions are interval integrable on `[0, π]`. -/
theorem intervalIntegrable_zero_pi (f : ℝ → ℂ) (hf : Continuous f) : IntervalIntegrable f volume 0 π :=
  hf.intervalIntegrable _ _

/-- The complex number `π` is nonzero. -/
theorem pi_complex_ne_zero : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero

/-- Derivative of the Anger function via the shifted orders (DLMF 11.10.34). -/
theorem hasDerivAt_angerJ_shift (ν z : ℂ) :
    HasDerivAt (angerJ ν) ((angerJ (ν-1) z-angerJ (ν+1) z)/2) z := by
  convert angerJ_hasDerivAt_arg ν z using 1
  unfold angerJ
  rw [← mul_sub, mul_div_assoc, ← intervalIntegral.integral_sub (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop)),
    ← intervalIntegral.integral_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [show (ν-1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-θ by ring,
    show (ν+1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)+θ by ring, cos_sub, cos_add,
    ← ofReal_sin]
  ring

/-- Derivative of the Weber function via the shifted orders (DLMF 11.10.35). -/
theorem hasDerivAt_weberE_shift (ν z : ℂ) :
    HasDerivAt (weberE ν) ((weberE (ν-1) z-weberE (ν+1) z)/2) z := by
  convert weberE_hasDerivAt_arg ν z using 1
  unfold weberE
  rw [← mul_sub, mul_div_assoc, ← intervalIntegral.integral_sub (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop)),
    ← intervalIntegral.integral_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [show (ν-1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-θ by ring,
    show (ν+1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)+θ by ring, sin_sub, sin_add,
    ← ofReal_sin]
  ring

/-- Derivative of the phase `νθ - z sin θ` in `θ`. -/
theorem hasDerivAt_phase (ν z : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ν*(t:ℂ)-z*Real.sin t) (ν-z*Real.cos t) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => ((Real.sin t : ℝ):ℂ)) (Real.cos t) t :=
    (Real.hasDerivAt_sin t).ofReal_comp
  convert (h1.const_mul ν).sub (h2.const_mul z) using 1
  ring

/-- The Anger recurrence (DLMF 11.10.32), proved by integration of `d/dθ sin(νθ - z sin θ)`. -/
lemma angerJ_recurrence_aux (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    angerJ (ν-1) z+angerJ (ν+1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν)) := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => sin (ν*(t:ℂ)-z*Real.sin t))
    (f' := fun t : ℝ => cos (ν*(t:ℂ)-z*Real.sin t)*(ν-z*Real.cos t))
    (a := 0) (b := π) (fun t _ => (Complex.hasDerivAt_sin _).comp t (hasDerivAt_phase ν z t)) (intervalIntegrable_zero_pi _ (by fun_prop))
  have e1 : (∫ t in (0:ℝ)..π, cos (ν*(t:ℂ)-z*Real.sin t)*(ν-z*Real.cos t)) =
      ν*(∫ t in (0:ℝ)..π, cos (ν*(t:ℂ)-z*Real.sin t)) -
        z*∫ t in (0:ℝ)..π, cos (ν*(t:ℂ)-z*Real.sin t)*Real.cos t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    congr 1; funext t; ring
  have e2 : angerJ (ν-1) z+angerJ (ν+1) z =
      1/π*(2*∫ t in (0:ℝ)..π, cos (ν*(t:ℂ)-z*Real.sin t)*Real.cos t) := by
    unfold angerJ
    rw [← mul_add, ← intervalIntegral.integral_add (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    rw [show (ν-1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-θ by ring,
      show (ν+1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)+θ by ring, cos_sub, cos_add,
      ← ofReal_cos]
    ring
  simp only [Real.sin_pi, Real.sin_zero, ofReal_zero, mul_zero, sub_zero, sin_zero] at hftc
  rw [e1] at hftc
  rw [e2]
  unfold angerJ
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  rw [mul_comm (π:ℂ) ν]
  linear_combination (-1:ℂ)*hftc

/-- The Weber recurrence (DLMF 11.10.33), proved by integration of `d/dθ cos(νθ - z sin θ)`. -/
lemma weberE_recurrence_aux (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    weberE (ν-1) z+weberE (ν+1) z = 2*ν/z*weberE ν z-2/(π*z)*(1-cos (π*ν)) := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -cos (ν*(t:ℂ)-z*Real.sin t))
    (f' := fun t : ℝ => sin (ν*(t:ℂ)-z*Real.sin t)*(ν-z*Real.cos t))
    (a := 0) (b := π) (fun t _ => by
      convert ((Complex.hasDerivAt_cos _).comp t (hasDerivAt_phase ν z t)).neg using 1 <;> first | rfl | ring) (intervalIntegrable_zero_pi _ (by fun_prop))
  have e1 : (∫ t in (0:ℝ)..π, sin (ν*(t:ℂ)-z*Real.sin t)*(ν-z*Real.cos t)) =
      ν*(∫ t in (0:ℝ)..π, sin (ν*(t:ℂ)-z*Real.sin t)) -
        z*∫ t in (0:ℝ)..π, sin (ν*(t:ℂ)-z*Real.sin t)*Real.cos t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    congr 1; funext t; ring
  have e2 : weberE (ν-1) z+weberE (ν+1) z =
      1/π*(2*∫ t in (0:ℝ)..π, sin (ν*(t:ℂ)-z*Real.sin t)*Real.cos t) := by
    unfold weberE
    rw [← mul_add, ← intervalIntegral.integral_add (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    rw [show (ν-1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-θ by ring,
      show (ν+1)*(θ:ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)+θ by ring, sin_sub, sin_add,
      ← ofReal_cos]
    ring
  simp only [Real.sin_pi, Real.sin_zero, ofReal_zero, mul_zero, sub_zero, cos_zero] at hftc
  rw [e1] at hftc
  rw [e2]
  unfold weberE
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  rw [mul_comm (π:ℂ) ν]
  linear_combination (-1:ℂ)*hftc

/-- At integer order the Anger function is Bessel's `J_n` (DLMF 11.10.29). -/
lemma angerJ_int_aux (n : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ n z = besselJ n z := by
  have _ := slitPlane_ne_zero hz
  rw [besselJ_int_eq_integral_cos, angerJ]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [← cos_neg, ofReal_sin]
  ring_nf

/-- In a punctured neighbourhood of any complex number there are no integers. -/
theorem eventually_nhdsNE_not_int (ν : ℂ) : ∀ᶠ μ : ℂ in 𝓝[≠] ν, ∀ k : ℤ, μ ≠ k := by
  by_cases h : ∃ k : ℤ, ν = k
  · obtain ⟨n, rfl⟩ := h
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (n:ℂ) (by norm_num : (0:ℝ) < 1/2)),
      self_mem_nhdsWithin] with μ h1 h2
    exact DLMF.Bessel.not_int_of_mem_ball h1 h2
  · have ho : IsOpen (Set.range ((↑) : ℤ → ℂ))ᶜ :=
      Complex.isClosedEmbedding_intCast.isClosed_range.isOpen_compl
    filter_upwards [nhdsWithin_le_nhds (ho.mem_nhds (by rintro ⟨k, hk⟩; exact h ⟨k, hk.symm⟩))]
      with μ hμ k hk
    exact hμ ⟨k, hk.symm⟩

/-- `sin(πν) ≠ 0` at nonintegral `ν`. -/
theorem sin_pi_mul_ne_zero_of_not_int {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : sin (π*ν) ≠ 0 :=
  DLMF.Confluent.sin_pi_mul_ne_zero_of_mem (DLMF.Confluent.mem_integerComplement_of_forall hν)

/-- Associated Anger–Weber function at nonintegral order. -/
def angerARegular (ν z : ℂ) : ℂ :=
  (angerJ ν z-besselJ ν z)/sin (π*ν)

/-- Continuation in order supplies removable values at integral orders. -/
@[dlmf 11.10.E4]
def angerA (ν z : ℂ) : ℂ :=
  limUnder (𝓝[≠] ν) (fun n => angerARegular n z)

/-- The regular quotient defining `angerA` is continuous in the order at nonintegral orders. -/
theorem continuousAt_angerARegular {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {z : ℂ} (hz : z ∈ slitPlane) :
    ContinuousAt (fun μ => angerARegular μ z) ν := by
  unfold angerARegular
  exact (((angerJ_entire_order z) ν).continuousAt.sub
    ((DLMF.Bessel.differentiable_besselJ_order (slitPlane_ne_zero hz)) ν).continuousAt).div
    (by fun_prop) (sin_pi_mul_ne_zero_of_not_int hν)

/-- Identity under the stated parameter and domain assumptions: `angerA ν z = angerARegular ν z`. -/
theorem angerA_regular {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {z : ℂ} (hz : z ∈ slitPlane) :
    angerA ν z = angerARegular ν z := by
  exact ((continuousAt_angerARegular hν hz).tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

/-- The map `(fun n => angerARegular n z)` tends to `(𝓝 (angerA ν z))` along `(𝓝[≠] ν)`. -/
theorem angerA_order_limit (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun n => angerARegular n z) (𝓝[≠] ν) (𝓝 (angerA ν z)) := by
  suffices h : ∃ L, Tendsto (fun n => angerARegular n z) (𝓝[≠] ν) (𝓝 L) by
    obtain ⟨L, hL⟩ := h
    rwa [angerA, hL.limUnder_eq]
  by_cases h : ∃ k : ℤ, ν = k
  · obtain ⟨n, rfl⟩ := h
    set g : ℂ → ℂ := fun μ => angerJ μ z - besselJ μ z
    have hg : DifferentiableAt ℂ g n :=
      (angerJ_entire_order z n).sub
        (DLMF.Bessel.differentiable_besselJ_order (slitPlane_ne_zero hz) n)
    have hs : HasDerivAt (fun μ : ℂ => sin (π*μ)) (cos (π*n)*π) n := by
      simpa using ((hasDerivAt_id (n:ℂ)).const_mul (π:ℂ)).csin
    have hsn : sin (π*(n:ℂ)) = 0 := by rw [mul_comm]; exact sin_int_mul_pi n
    have hgn : g n = 0 := by simp only [g, angerJ_int_aux n hz, sub_self]
    have hcn : cos (π*(n:ℂ))*π ≠ 0 := by
      refine mul_ne_zero (fun h0 => ?_) pi_complex_ne_zero
      have := sin_sq_add_cos_sq (π*(n:ℂ))
      rw [hsn, h0] at this; norm_num at this
    refine ⟨deriv g n/(cos (π*n)*π), ?_⟩
    have h1 := hasDerivAt_iff_tendsto_slope.1 hg.hasDerivAt
    have h2 := hasDerivAt_iff_tendsto_slope.1 hs
    refine (h1.div h2 hcn).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with μ hμ
    have hμ' : μ - n ≠ 0 := sub_ne_zero.2 hμ
    rw [Pi.div_apply, slope_def_field, slope_def_field, hgn, hsn, sub_zero, sub_zero,
      div_div_div_cancel_right₀ hμ']
    rfl
  · push Not at h
    exact ⟨_, (continuousAt_angerARegular (fun n => h n) hz).tendsto.mono_left nhdsWithin_le_nhds⟩

/-- The associated Anger–Weber function is continuous in the order. -/
theorem continuousAt_angerA_order (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    ContinuousAt (fun μ => angerA μ z) ν := by
  rw [← continuousWithinAt_compl_self]
  refine (angerA_order_limit ν hz).congr' ?_
  filter_upwards [eventually_nhdsNE_not_int ν] with μ hμ
  exact (angerA_regular hμ hz).symm

/-- The Anger function is the angular part of Schläfli's integral. -/
theorem angerJ_eq_angular (ν z : ℂ) :
    angerJ ν z = 1 / π * ∫ θ in (0:ℝ)..π, cos (z * Real.sin θ - ν * θ) := by
  rw [angerJ]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [← cos_neg]
  ring_nf

/-- Anger–Weber consequence of Schläfli's integral (DLMF 10.9.6 with 11.10.1):
`𝐉_ν(z) - J_ν(z) = (sin νπ/π) ∫₀^∞ e^{-νt - z sinh t} dt` for `ℜ z > 0`. -/
theorem angerJ_sub_besselJ_eq_integral (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    angerJ ν z - besselJ ν z =
      sin (ν * π) / π * ∫ t in Ioi (0:ℝ), exp (-ν * t - z * Real.sinh t) := by
  rw [angerJ_eq_angular, angular_sub_besselJ_eq_schlafli ν hz]
  congr 2
  funext t
  ring_nf

/-- At nonintegral order and `ℜ w > 0`, the regular quotient is the Schläfli radial integral. -/
theorem angerARegular_eq_integral {μ : ℂ} (hμ : ∀ n : ℤ, μ ≠ n) {w : ℂ} (hw : 0 < w.re) :
    angerARegular μ w = (∫ t in Ioi (0:ℝ), exp (-(w * Real.sinh t) - μ * t)) / π := by
  have hs := sin_pi_mul_ne_zero_of_not_int hμ
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [angerARegular, angerJ_eq_angular, angular_sub_besselJ_eq_schlafli μ hw, mul_comm μ]
  field_simp

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => exp (-ν*t-z*Real.sinh
t)/π) 0 (angerA ν z)`. -/
@[dlmf 11.10.E4]
theorem angerA_integral (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-ν*t-z*Real.sinh t)/π) 0 (angerA ν z) := by
  have hzs : z ∈ slitPlane := Or.inl hz
  set R : ℂ → ℂ := fun μ => ∫ t in Ioi (0:ℝ), exp (-(z * Real.sinh t) - μ * t) with hR
  have hRc : Continuous R := (differentiable_schlafli_order hz).continuous
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hreg {μ : ℂ} (hμ : ∀ n : ℤ, μ ≠ n) : angerARegular μ z = R μ / π :=
    angerARegular_eq_integral hμ hz
  have hA : angerA ν z = R ν / π := by
    refine tendsto_nhds_unique (angerA_order_limit ν hzs) ?_
    have h := ((hRc.tendsto ν).div_const (π : ℂ)).mono_left (nhdsWithin_le_nhds (s := {ν}ᶜ))
    refine h.congr' ?_
    filter_upwards [eventually_nhdsNE_not_int ν] with μ hμ
    exact (hreg hμ).symm
  have ht := (tendsto_intervalIntegral_schlafli ν hz).div_const (π : ℂ)
  unfold HasIntegralAtTop
  rw [hA]
  refine ht.congr fun b => ?_
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring_nf

/-- Boundary extension of the defining integral. -/
theorem angerA_boundary_integral {ν z : ℂ} (hν : 0 < ν.re) (hz : z.re = 0) (hz0 : z ≠ 0) :
    HasIntegralAtTop (fun t : ℝ => exp (-ν*t-z*Real.sinh t)/π) 0 (angerA ν z) := by
  have hzim : z.im ≠ 0 := fun h => hz0 (Complex.ext hz h)
  have hzs : z ∈ slitPlane := Or.inr hzim
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hzre : 0 ≤ z.re := hz.ge
  have hcl : z ∈ closure {w : ℂ | 0 < w.re} := by rw [closure_setOfPred_lt_re]; exact hzre
  have : (𝓝[{w : ℂ | 0 < w.re}] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hkey {μ : ℂ} (hμ : ∀ n : ℤ, μ ≠ n) (hμr : 0 < μ.re) :
      angerARegular μ z = schlafliBoundary μ z / π := by
    have hf : ContinuousAt (fun w => angerARegular μ w) z := by
      unfold angerARegular
      exact (((angerJ_entire μ) z).continuousAt.sub
        (analyticAt_besselJ μ hzs).continuousAt).div_const _
    have hg := (continuousWithinAt_schlafliBoundary_right hμr hz0).div_const (π : ℂ)
    refine tendsto_nhds_unique (l := 𝓝[{w : ℂ | 0 < w.re}] z) (hf.tendsto.mono_left nhdsWithin_le_nhds) ?_
    refine ((hg.mono (s := {w : ℂ | 0 < w.re}) (fun w (hw : 0 < w.re) => show 0 ≤ w.re from le_of_lt hw)).tendsto).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [angerARegular_eq_integral hμ hw, integral_schlafli_eq_schlafliBoundary hμr hw]
  have hA : angerA ν z = schlafliBoundary ν z / π := by
    refine tendsto_nhds_unique (angerA_order_limit ν hzs) ?_
    have h := ((continuousAt_schlafliBoundary_order hν hzre).div_const (π : ℂ)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {ν}ᶜ))
    refine h.congr' ?_
    have hopen : {μ : ℂ | 0 < μ.re} ∈ 𝓝[≠] ν :=
      nhdsWithin_le_nhds ((isOpen_lt continuous_const continuous_re).mem_nhds hν)
    filter_upwards [eventually_nhdsNE_not_int ν, hopen] with μ hμ hμr
    exact (hkey hμ hμr).symm
  have ht := (tendsto_intervalIntegral_schlafliBoundary hν hzre hz0).div_const (π : ℂ)
  unfold HasIntegralAtTop
  rw [hA]
  refine ht.congr fun b => ?_
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring_nf

/-- Identity under the stated parameter and domain assumptions: `(1/π*∫ θ : ℝ in 0..2*π, cos
(ν*θ-z*Real.sin θ)) = (1+cos (2*π*ν))*angerJ ν z+sin (2*π*ν)*weberE ν z`. -/
@[dlmf 11.10.E3]
theorem angerJ_double_integral (ν z : ℂ) :
    (1/π*∫ θ : ℝ in 0..2*π, cos (ν*θ-z*Real.sin θ)) = (1+cos (2*π*ν))*angerJ ν z+sin (2*π*ν)*weberE ν z := by
  have hc : Continuous (fun θ : ℝ => cos (ν*θ-z*Real.sin θ)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => cos (ν*θ-z*Real.sin θ)) (a := 0) (b := π) (2*π)
  rw [show 2*π-π = π by ring, sub_zero] at this
  rw [← this]
  have e : (∫ x in (0:ℝ)..π, cos (ν*((2*π-x:ℝ):ℂ)-z*Real.sin (2*π-x))) =
      cos (2*π*ν)*(∫ x in (0:ℝ)..π, cos (ν*x-z*Real.sin x)) +
        sin (2*π*ν)*∫ x in (0:ℝ)..π, sin (ν*x-z*Real.sin x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [Real.sin_two_pi_sub]
    rw [show ν*((2*π-θ:ℝ):ℂ)-z*((-Real.sin θ:ℝ):ℂ) = 2*π*ν-(ν*θ-z*Real.sin θ) by push_cast; ring,
      cos_sub]
  rw [e]; unfold angerJ weberE; ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv 2 (angerJ ν)
z+deriv (angerJ ν) z/z+(1-ν^2/z^2)*angerJ ν z = (z-ν)/(π*z^2)*sin (π*ν)`. -/
@[dlmf 11.10.E5, dlmf 11.10.E6]
theorem angerJ_ode (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    iteratedDeriv 2 (angerJ ν) z+deriv (angerJ ν) z/z+(1-ν^2/z^2)*angerJ ν z = (z-ν)/(π*z^2)*sin (π*ν) := by
  have hD : deriv (angerJ ν) = fun w => (angerJ (ν-1) w-angerJ (ν+1) w)/2 :=
    funext fun w => (hasDerivAt_angerJ_shift ν w).deriv
  have h2 : iteratedDeriv 2 (angerJ ν) z =
      ((angerJ (ν-1-1) z - angerJ ν z)/2 - (angerJ ν z - angerJ (ν+1+1) z)/2)/2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hD]
    have := ((hasDerivAt_angerJ_shift (ν-1) z).sub (hasDerivAt_angerJ_shift (ν+1) z)).div_const 2
    rw [sub_add_cancel, add_sub_cancel_right] at this
    exact this.deriv
  have r1 := angerJ_recurrence_aux (ν-1) hz
  have r2 := angerJ_recurrence_aux (ν+1) hz
  have r3 := angerJ_recurrence_aux ν hz
  rw [sub_add_cancel, show π*(ν-1) = π*ν-π by ring, sin_sub_pi] at r1
  rw [add_sub_cancel_right, show π*(ν+1) = π*ν+π by ring, sin_add_pi] at r2
  rw [h2, (hasDerivAt_angerJ_shift ν z).deriv]
  linear_combination (norm := skip) (1/4:ℂ)*r1 + (1/4:ℂ)*r2 + ν/(2*z)*r3
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv 2 (weberE ν)
z+deriv (weberE ν) z/z+(1-ν^2/z^2)*weberE ν z = -(z+ν+(z-ν)*cos (π*ν))/(π*z^2)`. -/
@[dlmf 11.10.E5, dlmf 11.10.E7]
theorem weberE_ode (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    iteratedDeriv 2 (weberE ν) z+deriv (weberE ν) z/z+(1-ν^2/z^2)*weberE ν z = -(z+ν+(z-ν)*cos (π*ν))/(π*z^2) := by
  have hD : deriv (weberE ν) = fun w => (weberE (ν-1) w-weberE (ν+1) w)/2 :=
    funext fun w => (hasDerivAt_weberE_shift ν w).deriv
  have h2 : iteratedDeriv 2 (weberE ν) z =
      ((weberE (ν-1-1) z - weberE ν z)/2 - (weberE ν z - weberE (ν+1+1) z)/2)/2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hD]
    have := ((hasDerivAt_weberE_shift (ν-1) z).sub (hasDerivAt_weberE_shift (ν+1) z)).div_const 2
    rw [sub_add_cancel, add_sub_cancel_right] at this
    exact this.deriv
  have r1 := weberE_recurrence_aux (ν-1) hz
  have r2 := weberE_recurrence_aux (ν+1) hz
  have r3 := weberE_recurrence_aux ν hz
  rw [sub_add_cancel, show π*(ν-1) = π*ν-π by ring, cos_sub_pi] at r1
  rw [add_sub_cancel_right, show π*(ν+1) = π*ν+π by ring, cos_add_pi] at r2
  rw [h2, (hasDerivAt_weberE_shift ν z).deriv]
  linear_combination (norm := skip) (1/4:ℂ)*r1 + (1/4:ℂ)*r2 + ν/(2*z)*r3
  field_simp
  ring

/-- The coefficients of the regularized `₁F₂(1; a, b; ·)` series. -/
lemma regularized1F2_one_coeff (a b : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {1} {a,b} n = 1/(Gamma (n+a)*Gamma (n+b)) := by
  simp only [regularizedHGFunCoeff, Multiset.map_singleton, Multiset.prod_singleton,
    Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons]
  rw [show (ascPochhammer ℂ n).eval 1=(n.factorial:ℂ) by simp,
    div_mul_eq_div_div, div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
  rw [add_comm a, add_comm b]

/-- The series `∑ (-1)^k (z/2)^{2k} / (Γ(k+a) Γ(k+b))` sums to the regularized
`₁F₂(1; a, b; -z²/4)`. -/
theorem hasSum_regularized1F2_one (a b z : ℂ) :
    HasSum (fun k : ℕ => (-1)^k*(z/2)^(2*k)/(Gamma (k+a)*Gamma (k+b)))
      (regularizedHGFun {1} {a,b} (-z^2/4)) := by
  have hr : (regularizedHGFunSeries {1} {a,b}).radius=⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hp : HasFPowerSeriesOnBall (regularizedHGFun {1} {a,b})
      (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff {1} {a,b})) 0 ⊤ := by
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {1} {a,b}).sum
      (regularizedHGFunSeries {1} {a,b}) 0 ⊤
    rw [← hr]
    exact (regularizedHGFunSeries {1} {a,b}).hasFPowerSeriesOnBall (by rw [hr]; simp)
  have hs := hp.hasSum_mul_pow (by simp : (-z^2/4) ∈ Metric.eball (0:ℂ) ⊤)
  refine hs.congr_fun fun n => ?_
  rw [regularized1F2_one_coeff, show (-z^2/4)=-((z/2)^2) by ring]
  rw [neg_pow ((z/2)^2), ← pow_mul]
  ring

/-- The even entire Anger series with reciprocal-Gamma factors `Γ(k+ν/2+1)⁻¹ Γ(k-ν/2+1)⁻¹`. -/
@[dlmf 11.10.E10]
def angerS1 (ν z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1)^k*(z/2)^(2*k)/(Gamma (k+ν/2+1)*Gamma (k-ν/2+1))

/-- The series with terms `(fun k : ℕ => (-1)^k*(z/2)^(2*k)/(Gamma (k+ν/2+1)*Gamma (k-ν/2+1)))`
converges to `(angerS1 ν z)`. -/
@[dlmf 11.10.E10]
theorem hasSum_angerS1 (ν z : ℂ) :
    HasSum (fun k : ℕ => (-1)^k*(z/2)^(2*k)/(Gamma (k+ν/2+1)*Gamma (k-ν/2+1))) (angerS1 ν z) := by
  have h := hasSum_regularized1F2_one (ν/2+1) (-ν/2+1) z
  simp only [← add_assoc, ← sub_eq_add_neg, neg_div] at h
  exact h.summable.hasSum

/-- The odd entire Anger series with reciprocal-Gamma factors `Γ(k+ν/2+3/2)⁻¹ Γ(k-ν/2+3/2)⁻¹`. -/
@[dlmf 11.10.E11]
def angerS2 (ν z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1)^k*(z/2)^(2*k+1)/(Gamma (k+ν/2+3/2)*Gamma (k-ν/2+3/2))

/-- The series with terms `(fun k : ℕ => (-1)^k*(z/2)^(2*k+1)/(Gamma (k+ν/2+3/2)*Gamma
(k-ν/2+3/2)))` converges to `(angerS2 ν z)`. -/
@[dlmf 11.10.E11]
theorem hasSum_angerS2 (ν z : ℂ) :
    HasSum (fun k : ℕ => (-1)^k*(z/2)^(2*k+1)/(Gamma (k+ν/2+3/2)*Gamma (k-ν/2+3/2))) (angerS2 ν z) := by
  have h := (hasSum_regularized1F2_one (ν/2+3/2) (-ν/2+3/2) z).mul_left (z/2)
  simp only [← add_assoc, ← sub_eq_add_neg, neg_div] at h
  refine (h.congr_fun fun k => ?_).summable.hasSum
  simp only [pow_succ]
  ring

/-- Two integrations by parts for the sine-power moments `∫₀^π sinⁿθ g(θ) dθ` of a solution of
`g'' = -ν² g`. -/
theorem sinPow_moment_recurrence (ν : ℂ) {g g1 : ℝ → ℂ} (hg : ∀ θ, HasDerivAt g (g1 θ) θ)
    (hg1 : ∀ θ, HasDerivAt g1 (-ν^2 * g θ) θ) (m : ℕ) :
    (((m:ℂ)+2)^2 - ν^2) * (∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^(m+2) * g θ) =
      ((m:ℂ)+2)*((m:ℂ)+1) * ∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^m * g θ := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun θ => (hg θ).continuousAt
  set Φ : ℝ → ℂ := fun θ => (Real.sin θ:ℂ)^(m+2) * g1 θ -
    ((m:ℂ)+2) * (Real.sin θ:ℂ)^(m+1) * (Real.cos θ:ℂ) * g θ
  set Φ' : ℝ → ℂ := fun θ => (((m:ℂ)+2)^2 - ν^2) * ((Real.sin θ:ℂ)^(m+2) * g θ) -
    ((m:ℂ)+2)*((m:ℂ)+1) * ((Real.sin θ:ℂ)^m * g θ)
  have hd : ∀ θ, HasDerivAt Φ (Φ' θ) θ := by
    intro θ
    have hs := (Real.hasDerivAt_sin θ).ofReal_comp
    have hc := (Real.hasDerivAt_cos θ).ofReal_comp
    have h := ((hs.pow (m+2)).mul (hg1 θ)).sub
      ((((hs.pow (m+1)).const_mul ((m:ℂ)+2)).mul hc).mul (hg θ))
    convert h using 1
    have hpy : (Real.sin θ:ℂ)^2 + (Real.cos θ:ℂ)^2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    simp only [Φ', Pi.mul_apply, Pi.pow_apply, ofReal_neg, Nat.cast_add,
      Nat.cast_ofNat, Nat.cast_one, show m+2-1 = m+1 by omega, show m+1-1 = m by omega]
    linear_combination (((m:ℂ)+2)*((m:ℂ)+1)) * (Real.sin θ:ℂ)^m * g θ * hpy
  have hΦ' : Continuous Φ' := by
    have := hgc; simp only [Φ']; fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (hΦ'.intervalIntegrable 0 π)
  have hΦπ : Φ π = 0 := by simp [Φ]
  have hΦ0 : Φ 0 = 0 := by simp [Φ]
  rw [hΦπ, hΦ0, sub_zero] at hint
  simp only [Φ'] at hint
  have i1 : IntervalIntegrable (fun θ : ℝ => (((m:ℂ)+2)^2 - ν^2) *
      ((Real.sin θ:ℂ)^(m+2) * g θ)) volume 0 π := by
    apply Continuous.intervalIntegrable; fun_prop
  have i2 : IntervalIntegrable (fun θ : ℝ => ((m:ℂ)+2)*((m:ℂ)+1) *
      ((Real.sin θ:ℂ)^m * g θ)) volume 0 π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  linear_combination hint

/-- The first sine moment `(1-ν²) ∫₀^π sin θ g(θ) dθ = g(π) + g(0)` for `g'' = -ν² g`. -/
theorem sinPow_moment_one (ν : ℂ) {g g1 : ℝ → ℂ} (hg : ∀ θ, HasDerivAt g (g1 θ) θ)
    (hg1 : ∀ θ, HasDerivAt g1 (-ν^2 * g θ) θ) :
    (1 - ν^2) * (∫ θ : ℝ in 0..π, (Real.sin θ:ℂ) * g θ) = g π + g 0 := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun θ => (hg θ).continuousAt
  set Φ : ℝ → ℂ := fun θ => (Real.sin θ:ℂ) * g1 θ - (Real.cos θ:ℂ) * g θ
  have hd : ∀ θ, HasDerivAt Φ ((1 - ν^2) * ((Real.sin θ:ℂ) * g θ)) θ := by
    intro θ
    have hs := (Real.hasDerivAt_sin θ).ofReal_comp
    have hc := (Real.hasDerivAt_cos θ).ofReal_comp
    have h := (hs.mul (hg1 θ)).sub (hc.mul (hg θ))
    convert h using 1
    simp only [ofReal_neg]; ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    ((by fun_prop : Continuous fun θ : ℝ => (1 - ν^2) * ((Real.sin θ:ℂ) * g θ)).intervalIntegrable 0 π)
  rw [intervalIntegral.integral_const_mul] at hint
  rw [hint]
  simp [Φ]

/-- `a / Γ(a+1) = 1/Γ(a)` for every complex `a` (both sides vanish at the poles). -/
theorem div_Gamma_add_one (a : ℂ) : a / Gamma (a+1) = (Gamma a)⁻¹ := by
  by_cases h : a = 0
  · subst h; simp [Complex.Gamma_zero]
  · rw [Complex.Gamma_add_one a h, div_mul_cancel_left₀ h]

/-- The closed form of the sine-power moments, without the trigonometric factor. -/
noncomputable def sinPowR (ν : ℂ) (n : ℕ) : ℂ :=
  π * n ! / 2^n * ((Gamma (1+((n:ℂ)+ν)/2))⁻¹ * (Gamma (1+((n:ℂ)-ν)/2))⁻¹)

/-- Identity under the stated parameter and domain assumptions: `(((m:ℂ)+2)^2 - ν^2) * sinPowR ν
(m+2) = ((m:ℂ)+2)*((m:ℂ)+1) * sinPowR ν m`. -/
theorem sinPowR_recurrence (ν : ℂ) (m : ℕ) :
    (((m:ℂ)+2)^2 - ν^2) * sinPowR ν (m+2) = ((m:ℂ)+2)*((m:ℂ)+1) * sinPowR ν m := by
  simp only [sinPowR]
  set A : ℂ := 1+((m:ℂ)+ν)/2
  set B : ℂ := 1+((m:ℂ)-ν)/2
  have hA : (1+(((m+2:ℕ):ℂ)+ν)/2) = A+1 := by simp only [A]; push_cast; ring
  have hB : (1+(((m+2:ℕ):ℂ)-ν)/2) = B+1 := by simp only [B]; push_cast; ring
  have hAB : ((m:ℂ)+2)^2 - ν^2 = 4*A*B := by simp only [A, B]; ring
  rw [hA, hB, hAB]
  have e1 := div_Gamma_add_one A
  have e2 := div_Gamma_add_one B
  rw [show 4*A*B*(π*((m+2)! : ℕ)/2^(m+2)*((Gamma (A+1))⁻¹*(Gamma (B+1))⁻¹)) =
    4*(π*((m+2)! : ℕ)/2^(m+2))*(A/Gamma (A+1))*(B/Gamma (B+1)) by ring, e1, e2]
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

/-- Nonvanishing under the stated hypotheses: `((m:ℂ))^2 - ν^2 ≠ 0`. -/
theorem sq_sub_ne_zero_of_not_int {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (m : ℕ) :
    ((m:ℂ))^2 - ν^2 ≠ 0 := by
  intro h
  have : ((m:ℂ) - ν) * ((m:ℂ)+ν) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hν m (by push_cast; linear_combination -h1)
  · exact hν (-m) (by push_cast; linear_combination h1)

/-- Sine-power moments from the two base cases, for nonintegral `ν`. -/
theorem sinPow_moment_eq_of_base {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {g g1 : ℝ → ℂ}
    (hg : ∀ θ, HasDerivAt g (g1 θ) θ) (hg1 : ∀ θ, HasDerivAt g1 (-ν^2 * g θ) θ) (T : ℂ)
    (h0 : (∫ θ : ℝ in 0..π, g θ) = T * sinPowR ν 0)
    (h1 : (∫ θ : ℝ in 0..π, (Real.sin θ:ℂ) * g θ) = T * sinPowR ν 1) (n : ℕ) :
    (∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^n * g θ) = T * sinPowR ν n := by
  suffices H : ∀ n, (∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^n * g θ) = T * sinPowR ν n ∧
      (∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^(n+1) * g θ) = T * sinPowR ν (n+1) from (H n).1
  intro n
  induction n with
  | zero => exact ⟨by simpa using h0, by simpa using h1⟩
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have hne := sq_sub_ne_zero_of_not_int hν (m+2)
    have hr := sinPow_moment_recurrence ν hg hg1 m
    have hR := sinPowR_recurrence ν m
    push_cast at hne
    apply mul_left_cancel₀ hne
    rw [show m+1+1 = m+2 by ring, hr, ih.1]
    linear_combination -T * hR

/-- The zeroth moment `-ν² ∫₀^π g = g'(π) - g'(0)` for `g'' = -ν² g`. -/
theorem sinPow_moment_zero (ν : ℂ) {g g1 : ℝ → ℂ} (hg : ∀ θ, HasDerivAt g (g1 θ) θ)
    (hg1 : ∀ θ, HasDerivAt g1 (-ν^2 * g θ) θ) :
    -ν^2 * (∫ θ : ℝ in 0..π, g θ) = g1 π - g1 0 := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun θ => (hg θ).continuousAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hg1 θ)
    ((by fun_prop : Continuous fun θ : ℝ => -ν^2 * g θ).intervalIntegrable 0 π)
  rw [intervalIntegral.integral_const_mul] at hint
  exact hint

/-- Nonvanishing under the stated hypotheses: `∀ n : ℤ, ν/2 ≠ n`. -/
theorem not_int_half {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : ∀ n : ℤ, ν/2 ≠ n := by
  intro n h
  exact hν (2*n) (by push_cast; linear_combination 2*h)

/-- Nonvanishing under the stated hypotheses: `∀ n : ℤ, (1+ν)/2 ≠ n`. -/
theorem not_int_half_add {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : ∀ n : ℤ, (1+ν)/2 ≠ n := by
  intro n h
  exact hν (2*n-1) (by push_cast; linear_combination 2*h)

/-- `1/(Γ(1+x)Γ(1-x)) = sin(πx)/(πx)` off the integers. -/
theorem recip_Gamma_one_add_mul_recip_Gamma_one_sub {x : ℂ} (hx : ∀ n : ℤ, x ≠ n) :
    (Gamma (1+x))⁻¹ * (Gamma (1-x))⁻¹ = sin (π*x)/(π*x) := by
  have hx0 : x ≠ 0 := by simpa using hx 0
  have hs := sin_pi_mul_ne_zero_of_not_int hx
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [add_comm, Complex.Gamma_add_one x hx0, mul_inv, mul_assoc, ← mul_inv,
    Complex.Gamma_mul_Gamma_one_sub]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `sinPowR ν 0 = 2*sin (π*ν/2)/ν`. -/
theorem sinPowR_zero {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : sinPowR ν 0 = 2*sin (π*ν/2)/ν := by
  have h := recip_Gamma_one_add_mul_recip_Gamma_one_sub (not_int_half hν)
  have hν0 : ν ≠ 0 := by simpa using hν 0
  simp only [sinPowR, Nat.cast_zero, zero_add, zero_sub, Nat.factorial_zero, pow_zero,
    Nat.cast_one, div_one, mul_one]
  rw [show 1 + -ν/2 = 1 - ν/2 by ring, h, show π*(ν/2) = π*ν/2 by ring]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

/-- Identity under the stated parameter and domain assumptions: `sinPowR ν 1 = 2*cos
(π*ν/2)/(1-ν^2)`. -/
theorem sinPowR_one {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) :
    sinPowR ν 1 = 2*cos (π*ν/2)/(1-ν^2) := by
  have hy := not_int_half_add hν
  set y := (1+ν)/2 with hydef
  have hy0 : y ≠ 0 := fun h => hy 0 (by rw [h]; simp)
  have hy1 : 1 - y ≠ 0 := by
    intro h; exact hy 1 (by push_cast; linear_combination -h)
  have hs := sin_pi_mul_ne_zero_of_not_int hy
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hne := sq_sub_ne_zero_of_not_int hν 1
  simp only [Nat.cast_one, one_pow] at hne
  have hsy : sin (π*y) = cos (π*ν/2) := by
    rw [show π*y = π*ν/2 + π/2 by simp only [y]; ring, Complex.sin_add_pi_div_two]
  simp only [sinPowR, Nat.cast_one, Nat.factorial_one, pow_one]
  rw [show 1+(1+ν)/2 = y+1 by simp only [y]; ring, show 1+(1-ν)/2 = (1-y)+1 by simp only [y]; ring,
    Complex.Gamma_add_one y hy0, Complex.Gamma_add_one (1-y) hy1]
  have hG := Complex.Gamma_mul_Gamma_one_sub y
  rw [← hsy]
  have hΓ : Gamma y * Gamma (1-y) ≠ 0 := by rw [hG]; exact div_ne_zero hπ hs
  have hΓ1 : Gamma y ≠ 0 := left_ne_zero_of_mul hΓ
  have hΓ2 : Gamma (1-y) ≠ 0 := right_ne_zero_of_mul hΓ
  have hyy : 1 - ν^2 = 4*y*(1-y) := by simp only [y]; ring
  rw [hyy]
  have : (Gamma y)⁻¹ * (Gamma (1-y))⁻¹ = sin (π*y)/π := by
    rw [← mul_inv, hG]; field_simp
  rw [mul_inv, mul_inv, show (π:ℂ)*1/2*((y)⁻¹*(Gamma y)⁻¹*((1-y)⁻¹*(Gamma (1-y))⁻¹)) =
    π/2*(y⁻¹*(1-y)⁻¹)*((Gamma y)⁻¹*(Gamma (1-y))⁻¹) by ring, this]
  field_simp
  norm_num

/-- Continuous functions of the order agreeing off the integers agree everywhere. -/
theorem eq_of_continuous_of_not_int {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ ν : ℂ, (∀ n : ℤ, ν ≠ n) → f ν = g ν) (ν : ℂ) : f ν = g ν := by
  have hd : Dense (Set.range (fun n : ℤ => (n:ℂ)))ᶜ :=
    (Set.countable_range _).dense_compl ℂ
  refine congrFun (hf.ext_on hd hg fun μ hμ => h μ fun n hn => hμ ⟨n, hn.symm⟩) ν

/-- Continuity of the indicated function: `Continuous fun ν => sinPowR ν n`. -/
theorem continuous_sinPowR (n : ℕ) : Continuous fun ν => sinPowR ν n := by
  have hG := Complex.differentiable_one_div_Gamma.continuous
  simp only [sinPowR]
  exact continuous_const.mul ((hG.comp (by fun_prop : Continuous fun ν:ℂ => 1+((n:ℂ)+ν)/2)).mul
    (hG.comp (by fun_prop : Continuous fun ν:ℂ => 1+((n:ℂ)-ν)/2)))

/-- At `θ`, the function `(fun t : ℝ => cos (ν*t))` has derivative `(-ν * sin (ν*θ))`. -/
theorem hasDerivAt_cos_mul_ofReal (ν : ℂ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => cos (ν*t)) (-ν * sin (ν*θ)) θ := by
  have := ((Complex.hasDerivAt_cos (ν*θ)).comp (θ:ℂ) ((hasDerivAt_id (θ:ℂ)).const_mul ν)).comp_ofReal
  convert this using 1; simp; ring

/-- At `θ`, the function `(fun t : ℝ => sin (ν*t))` has derivative `(ν * cos (ν*θ))`. -/
theorem hasDerivAt_sin_mul_ofReal (ν : ℂ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => sin (ν*t)) (ν * cos (ν*θ)) θ := by
  have := ((Complex.hasDerivAt_sin (ν*θ)).comp (θ:ℂ) ((hasDerivAt_id (θ:ℂ)).const_mul ν)).comp_ofReal
  convert this using 1; simp; ring

/-- **Sine-power cosine moments**: `∫₀^π sinⁿθ cos νθ dθ = π cos(πν/2) n! / (2ⁿ Γ(1+(n+ν)/2) Γ(1+(n-ν)/2))`
for every complex `ν`. -/
theorem integral_sinPow_mul_cos (ν : ℂ) (n : ℕ) :
    (∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^n * cos (ν*θ)) = cos (π*ν/2) * sinPowR ν n := by
  refine eq_of_continuous_of_not_int (f := fun ν => ∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^n * cos (ν*θ))
    (g := fun ν => cos (π*ν/2) * sinPowR ν n)
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _)
    ((by fun_prop : Continuous fun ν:ℂ => cos (π*ν/2)).mul (continuous_sinPowR n)) (fun ν hν => ?_) ν
  have hg := hasDerivAt_cos_mul_ofReal ν
  have hg1 : ∀ θ:ℝ, HasDerivAt (fun t:ℝ => -ν * sin (ν*t)) (-ν^2 * cos (ν*θ)) θ := fun θ => by
    convert (hasDerivAt_sin_mul_ofReal ν θ).const_mul (-ν) using 1; ring
  have hν0 : ν ≠ 0 := by simpa using hν 0
  have hne := sq_sub_ne_zero_of_not_int hν 1
  simp only [Nat.cast_one, one_pow] at hne
  refine sinPow_moment_eq_of_base hν hg hg1 _ ?_ ?_ n
  · have h0 := sinPow_moment_zero ν hg hg1
    rw [sinPowR_zero hν]
    simp only [ofReal_zero, mul_zero, sin_zero, sub_zero] at h0
    have : sin (ν*π) = 2*sin (π*ν/2)*cos (π*ν/2) := by
      rw [show ν*(π:ℂ) = 2*(π*ν/2) by ring, Complex.sin_two_mul]
    apply mul_left_cancel₀ (neg_ne_zero.2 (pow_ne_zero 2 hν0))
    rw [h0, this]; field_simp
  · have h1 := sinPow_moment_one ν hg hg1
    rw [sinPowR_one hν]
    simp only [ofReal_zero, mul_zero, cos_zero] at h1
    have : cos (ν*π) = 2*cos (π*ν/2)^2 - 1 := by
      rw [show ν*(π:ℂ) = 2*(π*ν/2) by ring, Complex.cos_two_mul]
    apply mul_left_cancel₀ hne
    rw [h1, this]; field_simp; ring

/-- **Sine-power sine moments**: `∫₀^π sinⁿθ sin νθ dθ = π sin(πν/2) n! / (2ⁿ Γ(1+(n+ν)/2) Γ(1+(n-ν)/2))`
for every complex `ν`. -/
theorem integral_sinPow_mul_sin (ν : ℂ) (n : ℕ) :
    (∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^n * sin (ν*θ)) = sin (π*ν/2) * sinPowR ν n := by
  refine eq_of_continuous_of_not_int (f := fun ν => ∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^n * sin (ν*θ))
    (g := fun ν => sin (π*ν/2) * sinPowR ν n)
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _)
    ((by fun_prop : Continuous fun ν:ℂ => sin (π*ν/2)).mul (continuous_sinPowR n)) (fun ν hν => ?_) ν
  have hg := hasDerivAt_sin_mul_ofReal ν
  have hg1 : ∀ θ:ℝ, HasDerivAt (fun t:ℝ => ν * cos (ν*t)) (-ν^2 * sin (ν*θ)) θ := fun θ => by
    convert (hasDerivAt_cos_mul_ofReal ν θ).const_mul ν using 1; ring
  have hν0 : ν ≠ 0 := by simpa using hν 0
  have hne := sq_sub_ne_zero_of_not_int hν 1
  simp only [Nat.cast_one, one_pow] at hne
  refine sinPow_moment_eq_of_base hν hg hg1 _ ?_ ?_ n
  · have h0 := sinPow_moment_zero ν hg hg1
    rw [sinPowR_zero hν]
    simp only [ofReal_zero, mul_zero, cos_zero, mul_one] at h0
    have : cos (ν*π) = 1 - 2*sin (π*ν/2)^2 := by
      rw [show ν*(π:ℂ) = 2*(π*ν/2) by ring, Complex.cos_two_mul, ← Complex.sin_sq_add_cos_sq (π*ν/2)]
      ring
    apply mul_left_cancel₀ (neg_ne_zero.2 (pow_ne_zero 2 hν0))
    rw [h0, this]; field_simp; ring
  · have h1 := sinPow_moment_one ν hg hg1
    rw [sinPowR_one hν]
    simp only [ofReal_zero, mul_zero, sin_zero, add_zero] at h1
    have : sin (ν*π) = 2*sin (π*ν/2)*cos (π*ν/2) := by
      rw [show ν*(π:ℂ) = 2*(π*ν/2) by ring, Complex.sin_two_mul]
    apply mul_left_cancel₀ hne
    rw [h1, this]; field_simp

/-- Termwise integration on `[0,π]` of a series in powers of `sin θ` against a continuous
function. -/
theorem hasSum_integral_sinPow {g : ℝ → ℂ} (hg : Continuous g) (c : ℕ → ℂ)
    (hc : Summable fun k => ‖c k‖) (p : ℕ → ℕ) (f : ℝ → ℂ)
    (hf : ∀ θ : ℝ, HasSum (fun k => c k * (Real.sin θ:ℂ)^(p k)) (f θ)) :
    HasSum (fun k => c k * ∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^(p k) * g θ)
      (∫ θ : ℝ in 0..π, g θ * f θ) := by
  obtain ⟨C, hC⟩ := (isCompact_uIcc (a := (0:ℝ)) (b := π)).exists_bound_of_continuousOn
    hg.continuousOn
  simp_rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k _ => ‖c k‖ * C) (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
  · exact (by fun_prop : Continuous fun θ : ℝ => c k * ((Real.sin θ:ℂ)^(p k) * g θ)
      ).aestronglyMeasurable
  · refine Eventually.of_forall fun θ hθ => ?_
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real]
    have h1 : ‖Real.sin θ‖^(p k) ≤ 1 := pow_le_one₀ (norm_nonneg _)
      (by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one θ)
    have h2 : ‖g θ‖ ≤ C := hC θ (uIoc_subset_uIcc hθ)
    have h3 := norm_nonneg (c k)
    have h4 : ‖Real.sin θ‖^(p k) * ‖g θ‖ ≤ C := by
      calc ‖Real.sin θ‖^(p k) * ‖g θ‖ ≤ 1 * C :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    exact mul_le_mul_of_nonneg_left h4 h3
  · exact Eventually.of_forall fun θ _ => hc.mul_right _
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun θ _ => ?_
    refine ((hf θ).mul_left (g θ)).congr_fun fun k => ?_
    ring

/-- Summability of even exponential coefficients. -/
theorem summable_norm_even_div_factorial (z : ℂ) :
    Summable fun k : ℕ => ‖z‖^(2*k) / ((2*k)! : ℝ) := by
  have h := Real.summable_pow_div_factorial ‖z‖
  exact h.comp_injective (i := fun k : ℕ => 2*k) (fun a b h => by simp only at h; omega)

/-- `∫₀^π g(θ) cos(z sin θ) dθ` from sine-power moments of the form `T · sinPowR ν n`. -/
theorem integral_mul_cos_mul_sin {ν T : ℂ} {g : ℝ → ℂ} (hg : Continuous g)
    (hmom : ∀ n : ℕ, (∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^n * g θ) = T * sinPowR ν n) (z : ℂ) :
    (∫ θ : ℝ in 0..π, g θ * cos (z*Real.sin θ)) = π * T * angerS1 ν z := by
  set c : ℕ → ℂ := fun k => (-1)^k * z^(2*k) / ((2*k)! : ℂ)
  have hc : Summable fun k => ‖c k‖ := by
    refine (summable_norm_even_div_factorial z).congr fun k => ?_
    simp [c, norm_pow]
  have hS := hasSum_integral_sinPow hg c hc (fun k => 2*k) (fun θ => cos (z*Real.sin θ))
    (fun θ => by
      refine (Complex.hasSum_cos (z*Real.sin θ)).congr_fun fun k => ?_
      simp only [c]; ring)
  simp_rw [hmom] at hS
  refine hS.unique ?_
  refine ((hasSum_angerS1 ν z).mul_left (π*T)).congr_fun fun k => ?_
  have hf : (((2*k)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  simp only [c, sinPowR]
  rw [show 1+(((2*k:ℕ):ℂ)+ν)/2 = (k:ℂ)+ν/2+1 by push_cast; ring,
    show 1+(((2*k:ℕ):ℂ)-ν)/2 = (k:ℂ)-ν/2+1 by push_cast; ring, div_pow]
  field_simp

/-- `∫₀^π g(θ) sin(z sin θ) dθ` from sine-power moments of the form `T · sinPowR ν n`. -/
theorem integral_mul_sin_mul_sin {ν T : ℂ} {g : ℝ → ℂ} (hg : Continuous g)
    (hmom : ∀ n : ℕ, (∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^n * g θ) = T * sinPowR ν n) (z : ℂ) :
    (∫ θ : ℝ in 0..π, g θ * sin (z*Real.sin θ)) = π * T * angerS2 ν z := by
  set c : ℕ → ℂ := fun k => (-1)^k * z^(2*k+1) / ((2*k+1)! : ℂ)
  have hc : Summable fun k => ‖c k‖ := by
    refine (summable_norm_odd_div_factorial z).congr fun k => ?_
    simp [c, norm_pow]
  have hS := hasSum_integral_sinPow hg c hc (fun k => 2*k+1) (fun θ => sin (z*Real.sin θ))
    (fun θ => by
      refine (Complex.hasSum_sin (z*Real.sin θ)).congr_fun fun k => ?_
      simp only [c]; ring)
  simp_rw [hmom] at hS
  refine hS.unique ?_
  refine ((hasSum_angerS2 ν z).mul_left (π*T)).congr_fun fun k => ?_
  have hf : (((2*k+1)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  simp only [c, sinPowR]
  rw [show 1+(((2*k+1:ℕ):ℂ)+ν)/2 = (k:ℂ)+ν/2+3/2 by push_cast; ring,
    show 1+(((2*k+1:ℕ):ℂ)-ν)/2 = (k:ℂ)-ν/2+3/2 by push_cast; ring, div_pow]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `angerJ ν z = cos (π*ν/2)*angerS1
ν z+sin (π*ν/2)*angerS2 ν z`. -/
@[dlmf 11.10.E8]
theorem angerJ_series (ν z : ℂ) :
    angerJ ν z = cos (π*ν/2)*angerS1 ν z+sin (π*ν/2)*angerS2 ν z := by
  have h1 := integral_mul_cos_mul_sin (by fun_prop) (integral_sinPow_mul_cos ν) z
  have h2 := integral_mul_sin_mul_sin (by fun_prop) (integral_sinPow_mul_sin ν) z
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsplit : (∫ θ : ℝ in 0..π, cos (ν*θ-z*Real.sin θ)) =
      (∫ θ : ℝ in 0..π, cos (ν*θ) * cos (z*Real.sin θ)) +
        ∫ θ : ℝ in 0..π, sin (ν*θ) * sin (z*Real.sin θ) := by
    rw [← intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    exact intervalIntegral.integral_congr fun θ _ => by simp only [Complex.cos_sub]
  rw [angerJ, hsplit, h1, h2]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `weberE ν z = sin (π*ν/2)*angerS1
ν z-cos (π*ν/2)*angerS2 ν z`. -/
@[dlmf 11.10.E9]
theorem weberE_series (ν z : ℂ) :
    weberE ν z = sin (π*ν/2)*angerS1 ν z-cos (π*ν/2)*angerS2 ν z := by
  have h1 := integral_mul_cos_mul_sin (by fun_prop) (integral_sinPow_mul_sin ν) z
  have h2 := integral_mul_sin_mul_sin (by fun_prop) (integral_sinPow_mul_cos ν) z
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsplit : (∫ θ : ℝ in 0..π, sin (ν*θ-z*Real.sin θ)) =
      (∫ θ : ℝ in 0..π, sin (ν*θ) * cos (z*Real.sin θ)) -
        ∫ θ : ℝ in 0..π, cos (ν*θ) * sin (z*Real.sin θ) := by
    rw [← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    exact intervalIntegral.integral_congr fun θ _ => by simp only [Complex.sin_sub]
  rw [weberE, hsplit, h1, h2]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `angerJ ν (-z) = angerJ (-ν) z`. -/
@[dlmf 11.10.E12]
theorem angerJ_neg (ν z : ℂ) :
    angerJ ν (-z) = angerJ (-ν) z := by
  unfold angerJ
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [show (-ν)*(θ:ℂ)-z*Real.sin θ=-(ν*θ-(-z)*Real.sin θ) by ring, cos_neg]

/-- Identity under the stated parameter and domain assumptions: `weberE ν (-z) = -weberE (-ν) z`. -/
@[dlmf 11.10.E12]
theorem weberE_neg (ν z : ℂ) :
    weberE ν (-z) = -weberE (-ν) z := by
  unfold weberE
  rw [← mul_neg, ← intervalIntegral.integral_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [show (-ν)*(θ:ℂ)-z*Real.sin θ=-(ν*θ-(-z)*Real.sin θ) by ring, sin_neg, neg_neg]

/-- Identity under the stated parameter and domain assumptions: `sin (π*ν)*angerJ ν z = cos
(π*ν)*weberE ν z-weberE (-ν) z`. -/
@[dlmf 11.10.E13]
theorem anger_weber (ν z : ℂ) :
    sin (π*ν)*angerJ ν z = cos (π*ν)*weberE ν z-weberE (-ν) z := by
  have h : weberE (-ν) z = cos (π*ν)*weberE ν z - sin (π*ν)*angerJ ν z := by
    unfold weberE angerJ
    have := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => sin ((-ν)*θ-z*Real.sin θ)) (a := 0) (b := π) π
    simp only [sub_self, sub_zero] at this
    have key : (∫ θ : ℝ in 0..π, sin ((-ν)*θ-z*Real.sin θ)) =
        cos (π*ν)*(∫ θ : ℝ in 0..π, sin (ν*θ-z*Real.sin θ)) - sin (π*ν)*∫ θ : ℝ in 0..π, cos (ν*θ-z*Real.sin θ) := by
      rw [← this, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [Real.sin_pi_sub]
      rw [show (-ν)*((π-θ:ℝ):ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-π*ν by push_cast; ring, sin_sub]
      ring
    rw [key]; ring
  rw [h]; ring

/-- Identity under the stated parameter and domain assumptions: `sin (π*ν)*weberE ν z = angerJ
(-ν) z-cos (π*ν)*angerJ ν z`. -/
@[dlmf 11.10.E14]
theorem weber_anger (ν z : ℂ) :
    sin (π*ν)*weberE ν z = angerJ (-ν) z-cos (π*ν)*angerJ ν z := by
  have h : angerJ (-ν) z = cos (π*ν)*angerJ ν z + sin (π*ν)*weberE ν z := by
    unfold weberE angerJ
    have := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => cos ((-ν)*θ-z*Real.sin θ)) (a := 0) (b := π) π
    simp only [sub_self, sub_zero] at this
    have key : (∫ θ : ℝ in 0..π, cos ((-ν)*θ-z*Real.sin θ)) =
        cos (π*ν)*(∫ θ : ℝ in 0..π, cos (ν*θ-z*Real.sin θ)) + sin (π*ν)*∫ θ : ℝ in 0..π, sin (ν*θ-z*Real.sin θ) := by
      rw [← this, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [Real.sin_pi_sub]
      rw [show (-ν)*((π-θ:ℝ):ℂ)-z*Real.sin θ = (ν*θ-z*Real.sin θ)-π*ν by push_cast; ring, cos_sub]
      ring
    rw [key]; ring
  rw [h]; ring

/-- Identity under the stated parameter and domain assumptions: `angerJ ν z = besselJ ν z+sin
(π*ν)*angerA ν z`. -/
@[dlmf 11.10.E15]
theorem anger_bessel (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ ν z = besselJ ν z+sin (π*ν)*angerA ν z := by
  by_cases h : ∃ k : ℤ, ν = k
  · obtain ⟨n, rfl⟩ := h
    rw [mul_comm (π:ℂ), sin_int_mul_pi, zero_mul, add_zero, angerJ_int_aux n hz]
  · push Not at h
    rw [angerA_regular (fun n => h n) hz, angerARegular]
    field_simp [sin_pi_mul_ne_zero_of_not_int (fun n => h n)]
    ring

/-- Identity under the stated parameter and domain assumptions: `weberE ν z = -besselY ν z-cos
(π*ν)*angerA ν z-angerA (-ν) z`. -/
@[dlmf 11.10.E16]
theorem weber_bessel (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE ν z = -besselY ν z-cos (π*ν)*angerA ν z-angerA (-ν) z := by
  refine DLMF.Confluent.eq_of_continuousAt_of_integerComplement
    (f := fun μ => weberE μ z)
    (g := fun μ => -besselY μ z-cos (π*μ)*angerA μ z-angerA (-μ) z)
    ((weberE_entire_order z) ν).continuousAt ?_ ?_
  · refine ((DLMF.Bessel.continuousAt_besselY_order id continuous_id ν hz).neg.sub
      ((by fun_prop : Continuous fun μ : ℂ => cos (π*μ)).continuousAt.mul
        (continuousAt_angerA_order ν hz))).sub ?_
    exact (continuousAt_angerA_order (-ν) hz).comp (f := fun μ : ℂ => -μ) continuousAt_id.neg
  · intro c hc
    have hc' := DLMF.Confluent.forall_of_mem_integerComplement hc
    have hcn : ∀ k : ℤ, -c ≠ k := fun k hk => hc' (-k) (by rw [Int.cast_neg, ← hk, neg_neg])
    have hs := sin_pi_mul_ne_zero_of_not_int hc'
    have hw := weber_anger c z
    rw [angerA_regular hc' hz, angerA_regular hcn hz, DLMF.Bessel.besselY_eq_of_not_int hc',
      DLMF.Bessel.besselD, angerARegular, angerARegular, mul_neg, sin_neg, mul_comm c (π:ℂ)]
    field_simp
    linear_combination hw

/-- `angerS1` as a regularized `₁F₂`. -/
lemma angerS1_eq_regularized (ν z : ℂ) :
    angerS1 ν z = regularizedHGFun {1} {ν/2+1, -ν/2+1} (-z^2/4) :=
  (hasSum_angerS1 ν z).unique (by
    convert hasSum_regularized1F2_one (ν/2+1) (-ν/2+1) z using 3; ring_nf)

/-- `angerS2` as a regularized `₁F₂`. -/
lemma angerS2_eq_regularized (ν z : ℂ) :
    angerS2 ν z = z/2 * regularizedHGFun {1} {ν/2+3/2, -ν/2+3/2} (-z^2/4) :=
  (hasSum_angerS2 ν z).unique (by
    convert (hasSum_regularized1F2_one (ν/2+3/2) (-ν/2+3/2) z).mul_left (z/2) using 1
    funext k; ring_nf)

end DLMF.Struve
end
