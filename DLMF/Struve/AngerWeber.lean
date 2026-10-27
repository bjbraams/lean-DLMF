/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Lommel
public import DLMF.Bessel.Schlafli
public import DLMF.ErrorFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import DLMF.Struve.Poisson

/-!
# Anger and Weber functions: entire definitions and identities

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Struve

open DLMF.Bessel DLMF.Confluent

/-- angerJ. -/
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

/-- weberE. -/
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

/-- angerA regular. -/
theorem angerA_regular {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {z : ℂ} (hz : z ∈ slitPlane) :
    angerA ν z = angerARegular ν z := by
  exact ((continuousAt_angerARegular hν hz).tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

/-- angerA order limit. -/
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

/-- angerA integral. -/
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

/-- angerJ double integral. -/
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

/-- angerJ ode. -/
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

/-- weberE ode. -/
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

/-- angerS1. -/
@[dlmf 11.10.E10]
def angerS1 (ν z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1)^k*(z/2)^(2*k)/(Gamma (k+ν/2+1)*Gamma (k-ν/2+1))

/-- hasSum angerS1. -/
@[dlmf 11.10.E10]
theorem hasSum_angerS1 (ν z : ℂ) :
    HasSum (fun k : ℕ => (-1)^k*(z/2)^(2*k)/(Gamma (k+ν/2+1)*Gamma (k-ν/2+1))) (angerS1 ν z) := by
  have h := hasSum_regularized1F2_one (ν/2+1) (-ν/2+1) z
  simp only [← add_assoc, ← sub_eq_add_neg, neg_div] at h
  exact h.summable.hasSum

/-- angerS2. -/
@[dlmf 11.10.E11]
def angerS2 (ν z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1)^k*(z/2)^(2*k+1)/(Gamma (k+ν/2+3/2)*Gamma (k-ν/2+3/2))

/-- hasSum angerS2. -/
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

theorem not_int_half {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : ∀ n : ℤ, ν/2 ≠ n := by
  intro n h
  exact hν (2*n) (by push_cast; linear_combination 2*h)

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

theorem sinPowR_zero {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : sinPowR ν 0 = 2*sin (π*ν/2)/ν := by
  have h := recip_Gamma_one_add_mul_recip_Gamma_one_sub (not_int_half hν)
  have hν0 : ν ≠ 0 := by simpa using hν 0
  simp only [sinPowR, Nat.cast_zero, zero_add, zero_sub, Nat.factorial_zero, pow_zero,
    Nat.cast_one, div_one, mul_one]
  rw [show 1 + -ν/2 = 1 - ν/2 by ring, h, show π*(ν/2) = π*ν/2 by ring]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

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

theorem continuous_sinPowR (n : ℕ) : Continuous fun ν => sinPowR ν n := by
  have hG := Complex.differentiable_one_div_Gamma.continuous
  simp only [sinPowR]
  exact continuous_const.mul ((hG.comp (by fun_prop : Continuous fun ν:ℂ => 1+((n:ℂ)+ν)/2)).mul
    (hG.comp (by fun_prop : Continuous fun ν:ℂ => 1+((n:ℂ)-ν)/2)))

theorem hasDerivAt_cos_mul_ofReal (ν : ℂ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => cos (ν*t)) (-ν * sin (ν*θ)) θ := by
  have := ((Complex.hasDerivAt_cos (ν*θ)).comp (θ:ℂ) ((hasDerivAt_id (θ:ℂ)).const_mul ν)).comp_ofReal
  convert this using 1; simp; ring

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

/-- angerJ series. -/
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

/-- weberE series. -/
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

/-- angerJ neg. -/
@[dlmf 11.10.E12]
theorem angerJ_neg (ν z : ℂ) :
    angerJ ν (-z) = angerJ (-ν) z := by
  unfold angerJ
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [show (-ν)*(θ:ℂ)-z*Real.sin θ=-(ν*θ-(-z)*Real.sin θ) by ring, cos_neg]

/-- weberE neg. -/
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

/-- anger weber. -/
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

/-- weber anger. -/
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

/-- anger bessel. -/
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

/-- weber bessel. -/
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

/-- `(0, ν)` is a regular Lommel pair off the integers. -/
theorem lommelRegular_zero_of_not_int {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : LommelRegular 0 ν :=
  fun n => ⟨fun h => hν (2*n+1) (by push_cast; linear_combination -h),
    fun h => hν (-(2*n+1)) (by push_cast; linear_combination h)⟩

/-- `(-1, ν)` is a regular Lommel pair off the integers. -/
theorem lommelRegular_neg_one_of_not_int {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : LommelRegular (-1) ν :=
  fun n => ⟨fun h => hν (2*n) (by push_cast; linear_combination -h),
    fun h => hν (-(2*n)) (by push_cast; linear_combination h)⟩

/-- The Gamma factors of `s_{0,ν}` and `s_{-1,ν}` off the integers. -/
theorem lommel_Gamma_factors {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) :
    Gamma ((0-ν+1)/2)*Gamma ((0+ν+1)/2) = π/cos (π*ν/2) ∧
    Gamma ((-1-ν+1)/2)*Gamma ((-1+ν+1)/2) = -2*π/(ν*sin (π*ν/2)) := by
  constructor
  · have h := Complex.Gamma_mul_Gamma_one_sub ((1+ν)/2)
    rw [show π*((1+ν)/2) = π*ν/2 + π/2 by ring, Complex.sin_add_pi_div_two,
      show 1-(1+ν)/2 = (0-ν+1)/2 by ring, show (1+ν)/2 = (0+ν+1)/2 by ring] at h
    rw [mul_comm, h]
  · have hν0 : ν ≠ 0 := by simpa using hν 0
    have h2 : -ν/2 ≠ 0 := by
      intro h; apply hν0; linear_combination -2*h
    have h := Complex.Gamma_mul_Gamma_one_sub (ν/2)
    have ha := Complex.Gamma_add_one (-ν/2) h2
    have hs := sin_pi_mul_ne_zero_of_not_int (not_int_half hν)
    rw [show -ν/2+1 = 1-ν/2 by ring] at ha
    rw [show (-1-ν+1)/2 = -ν/2 by ring, show (-1+ν+1)/2 = ν/2 by ring]
    rw [ha] at h
    have h' := (eq_div_iff hs).1 h
    rw [show π*ν/2 = π*(ν/2) by ring, eq_div_iff (mul_ne_zero hν0 hs)]
    linear_combination (-2:ℂ)*h'


/-- `s_{0,ν}` and `s_{-1,ν}` as regularized `₁F₂` functions off the integers. -/
theorem lommel_zero_neg_one_regularized {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (z : ℂ) :
    lommelS 0 ν z = z/2*(π/(2*cos (π*ν/2)))*
      regularizedHGFun {1} {ν/2+3/2, -ν/2+3/2} (-z^2/4) ∧
    lommelS (-1) ν z = -π/(2*ν*sin (π*ν/2))*
      regularizedHGFun {1} {ν/2+1, -ν/2+1} (-z^2/4) := by
  obtain ⟨hG0, hG1⟩ := lommel_Gamma_factors hν
  constructor
  · rw [lommelS_eq_regularized (lommelRegular_zero_of_not_int hν), hG0, zero_add, cpow_one,
      show (0-ν+3)/2 = -ν/2+3/2 by ring, show (0+ν+3)/2 = ν/2+3/2 by ring,
      Multiset.pair_comm]
    ring
  · rw [lommelS_eq_regularized (lommelRegular_neg_one_of_not_int hν), hG1, neg_add_cancel,
      cpow_zero, show (-1-ν+3)/2 = -ν/2+1 by ring, show (-1+ν+3)/2 = ν/2+1 by ring,
      Multiset.pair_comm]
    ring

/-- angerJ lommel. -/
@[dlmf 11.10.E17]
theorem angerJ_lommel {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ ν z = sin (π*ν)/π*(lommelS 0 ν z-ν*lommelS (-1) ν z) := by
  obtain ⟨h0, h1⟩ := lommel_zero_neg_one_regularized hν z
  have hν0 : ν ≠ 0 := by simpa using hν 0
  have hs := sin_pi_mul_ne_zero_of_not_int (not_int_half hν)
  have hc : cos (π*ν/2) ≠ 0 := by
    have := sin_pi_mul_ne_zero_of_not_int (not_int_half_add hν)
    rwa [show π*((1+ν)/2) = π*ν/2 + π/2 by ring, Complex.sin_add_pi_div_two] at this
  rw [show π*(ν/2) = π*ν/2 by ring] at hs
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [angerJ_series, angerS1_eq_regularized, angerS2_eq_regularized, h0, h1,
    show π*ν = 2*(π*ν/2) by ring, Complex.sin_two_mul]
  field_simp
  ring

/-- weberE lommel. -/
@[dlmf 11.10.E18]
theorem weberE_lommel {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE ν z = -(1+cos (π*ν))/π*lommelS 0 ν z-ν/π*(1-cos (π*ν))*lommelS (-1) ν z := by
  obtain ⟨h0, h1⟩ := lommel_zero_neg_one_regularized hν z
  have hν0 : ν ≠ 0 := by simpa using hν 0
  have hs := sin_pi_mul_ne_zero_of_not_int (not_int_half hν)
  have hc : cos (π*ν/2) ≠ 0 := by
    have := sin_pi_mul_ne_zero_of_not_int (not_int_half_add hν)
    rwa [show π*((1+ν)/2) = π*ν/2 + π/2 by ring, Complex.sin_add_pi_div_two] at this
  rw [show π*(ν/2) = π*ν/2 by ring] at hs
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsc := Complex.sin_sq_add_cos_sq (π*ν/2)
  rw [weberE_series, angerS1_eq_regularized, angerS2_eq_regularized, h0, h1,
    show π*ν = 2*(π*ν/2) by ring, Complex.cos_two_mul]
  field_simp
  linear_combination (4 * cos (π*ν/2) *
    regularizedHGFun {1} {(ν + 2) / 2, (-ν + 2) / 2} (-(z ^ 2 / 4))) * hsc

/-- angerFresnelPlus. -/
@[dlmf 11.10.E21]
def angerFresnelPlus (z : ℂ) : ℂ :=
  fresnelCosInt z+fresnelSinInt z

/-- angerFresnelMinus. -/
@[dlmf 11.10.E21]
def angerFresnelMinus (z : ℂ) : ℂ :=
  fresnelCosInt z-fresnelSinInt z

/-- Weighted derivative identity `z 𝐉_ν' + ν 𝐉_ν = z 𝐉_{ν-1} + sin(πν)/π` away from the origin. -/
theorem angerHalf_weighted_add (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    z*deriv (angerJ ν) z+(1:ℂ)*ν*angerJ ν z = (1:ℂ)*z*angerJ (ν-1) z+(1:ℂ)*(sin (π*ν))/π := by
  rw [(hasDerivAt_angerJ_shift ν z).deriv]
  have := angerJ_recurrence_aux ν hz
  rw [show angerJ (ν+1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν))-angerJ (ν-1) z by
    linear_combination this]
  field_simp
  ring

/-- Weighted derivative identity `z 𝐉_ν' - ν 𝐉_ν = -z 𝐉_{ν+1} - sin(πν)/π` away from the
origin. -/
theorem angerHalf_weighted_sub (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    z*deriv (angerJ ν) z+(-1:ℂ)*ν*angerJ ν z =
      (-1:ℂ)*z*angerJ (ν-(-1)) z+(-1:ℂ)*(sin (π*ν))/π := by
  rw [(hasDerivAt_angerJ_shift ν z).deriv, sub_neg_eq_add]
  have := angerJ_recurrence_aux ν hz
  rw [show angerJ (ν-1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν))-angerJ (ν+1) z by
    linear_combination this]
  field_simp
  ring

/-- Defect of DLMF 11.10.20, scaled by `√(πx/2)`, on the real line. -/
noncomputable def angerHalfDefectF (x : ℝ) : ℂ :=
  (Real.sqrt (π * x / 2) : ℂ) * angerJ (1/2) x -
    (angerFresnelPlus (Real.sqrt (2 * x / π)) * sin x +
      angerFresnelMinus (Real.sqrt (2 * x / π)) * cos x)

/-- Defect of DLMF 11.10.19, scaled by `√(πx/2)`, on the real line. -/
noncomputable def angerHalfDefectG (x : ℝ) : ℂ :=
  (Real.sqrt (π * x / 2) : ℂ) * angerJ (-1/2) x -
    (angerFresnelPlus (Real.sqrt (2 * x / π)) * cos x -
      angerFresnelMinus (Real.sqrt (2 * x / π)) * sin x)

/-- `d/dx √(cx) = √(cx)/(2x)` for `c, x > 0`, as a complex-valued function. -/
theorem hasDerivAt_sqrt_mul (c : ℝ) (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (Real.sqrt (c * x) : ℂ))
      ((Real.sqrt (c * x) : ℂ) / (2 * x)) x := by
  have h := ((Real.hasDerivAt_sqrt (by positivity : c * x ≠ 0)).comp x
    ((hasDerivAt_id x).const_mul c)).ofReal_comp
  refine h.congr_deriv ?_
  have hs : Real.sqrt (c * x) ^ 2 = c * x := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (c * x) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have h0 : ((Real.sqrt (c * x)) : ℂ) ≠ 0 := ofReal_ne_zero.2 hs0
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have : ((Real.sqrt (c * x)) : ℂ) ^ 2 = c * x := by exact_mod_cast hs
  push_cast
  field_simp
  linear_combination -this

/-- Derivatives of `C(√(2x/π))` and `S(√(2x/π))`. -/
theorem hasDerivAt_fresnel_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => fresnelCosInt (Real.sqrt (2 * x / π)))
        (cos x * ((Real.sqrt (2 * x / π) : ℂ) / (2 * x))) x ∧
      HasDerivAt (fun x : ℝ => fresnelSinInt (Real.sqrt (2 * x / π)))
        (sin x * ((Real.sqrt (2 * x / π) : ℂ) / (2 * x))) x := by
  have hw := hasDerivAt_sqrt_mul (2 / π) (by positivity) hx
  simp only [show ∀ y : ℝ, 2 / π * y = 2 * y / π from fun y => by ring] at hw
  have hw2 : π * ((Real.sqrt (2 * x / π) : ℝ) : ℂ) ^ 2 / 2 = x := by
    have : Real.sqrt (2 * x / π) ^ 2 = 2 * x / π := Real.sq_sqrt (by positivity)
    have h' : ((Real.sqrt (2 * x / π) : ℝ) : ℂ) ^ 2 = 2 * x / π := by exact_mod_cast this
    rw [h']
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    field_simp
  constructor
  · have := (hasDerivAt_fresnelCosInt_complex _).comp x hw
    rwa [hw2] at this
  · have := (hasDerivAt_fresnelSinInt_complex _).comp x hw
    rwa [hw2] at this

/-- `sin(π/2) = 1` in complex form. -/
theorem sin_pi_mul_half_complex : sin (π * (1/2 : ℂ)) = 1 := by
  rw [show π * (1/2 : ℂ) = (π/2 : ℝ) by push_cast; ring, ← ofReal_sin, Real.sin_pi_div_two]
  simp

/-- `2√(πx/2) = π√(2x/π)`. -/
theorem two_mul_sqrt_eq_pi_mul_sqrt (x : ℝ) :
    2 * (Real.sqrt (π * x / 2) : ℂ) = π * Real.sqrt (2 * x / π) := by
  have h : 2 * Real.sqrt (π * x / 2) = π * Real.sqrt (2 * x / π) := by
    rw [← Real.sqrt_sq (zero_le_two : (0:ℝ) ≤ 2), ← Real.sqrt_mul (sq_nonneg _),
      ← Real.sqrt_sq Real.pi_pos.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq zero_le_two,
      Real.sqrt_sq Real.pi_pos.le]
    congr 1
    have := Real.pi_pos
    field_simp
  exact_mod_cast h

/-- The scaled defects satisfy `F' = G`. -/
theorem hasDerivAt_angerHalfDefectF {x : ℝ} (hx : 0 < x) :
    HasDerivAt angerHalfDefectF (angerHalfDefectG x) x := by
  have hs := hasDerivAt_sqrt_mul (π / 2) (by positivity) hx
  simp only [show ∀ y : ℝ, π / 2 * y = π * y / 2 from fun y => by ring] at hs
  have ha := (angerJ_entire (1/2) (x : ℂ)).hasDerivAt.comp_ofReal
  obtain ⟨hC, hS⟩ := hasDerivAt_fresnel_sqrt hx
  have hsin := (Complex.hasDerivAt_sin (x : ℂ)).comp_ofReal
  have hcos := (Complex.hasDerivAt_cos (x : ℂ)).comp_ofReal
  have h := (hs.mul ha).sub (((hC.add hS).mul hsin).add ((hC.sub hS).mul hcos))
  unfold angerHalfDefectF
  refine h.congr_deriv ?_
  have hw := angerHalf_weighted_add (1/2) (ofReal_ne_zero.2 hx.ne')
  rw [show (1/2 : ℂ) - 1 = -1/2 by norm_num, sin_pi_mul_half_complex] at hw
  have hsw := two_mul_sqrt_eq_pi_mul_sqrt x
  have htrig := sin_sq_add_cos_sq (x : ℂ)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  unfold angerHalfDefectG angerFresnelPlus angerFresnelMinus
  simp only [Pi.add_apply, Pi.sub_apply]
  set s : ℂ := (Real.sqrt (π * x / 2) : ℂ)
  set w : ℂ := (Real.sqrt (2 * x / π) : ℂ)
  set D := deriv (angerJ (1/2)) (x : ℂ)
  have hD : D = (x * angerJ (-1/2) x + 1 / π - angerJ (1/2) x / 2) / x := by
    rw [eq_div_iff hx0]; linear_combination hw
  rw [hD]
  field_simp
  linear_combination hsw - π * w * htrig

/-- The scaled defects satisfy `G' = -F`. -/
theorem hasDerivAt_angerHalfDefectG {x : ℝ} (hx : 0 < x) :
    HasDerivAt angerHalfDefectG (-angerHalfDefectF x) x := by
  have hs := hasDerivAt_sqrt_mul (π / 2) (by positivity) hx
  simp only [show ∀ y : ℝ, π / 2 * y = π * y / 2 from fun y => by ring] at hs
  have ha := (angerJ_entire (-1/2) (x : ℂ)).hasDerivAt.comp_ofReal
  obtain ⟨hC, hS⟩ := hasDerivAt_fresnel_sqrt hx
  have hsin := (Complex.hasDerivAt_sin (x : ℂ)).comp_ofReal
  have hcos := (Complex.hasDerivAt_cos (x : ℂ)).comp_ofReal
  have h := (hs.mul ha).sub (((hC.add hS).mul hcos).sub ((hC.sub hS).mul hsin))
  unfold angerHalfDefectG
  refine h.congr_deriv ?_
  have hw := angerHalf_weighted_sub (-1/2) (ofReal_ne_zero.2 hx.ne')
  have hsn : sin (π * (-1/2 : ℂ)) = -1 := by
    rw [show π * (-1/2 : ℂ) = -(π * (1/2 : ℂ)) by ring, sin_neg, sin_pi_mul_half_complex]
  rw [show (-1/2 : ℂ) - (-1) = 1/2 by norm_num, hsn] at hw
  have hsw := two_mul_sqrt_eq_pi_mul_sqrt x
  have htrig := sin_sq_add_cos_sq (x : ℂ)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  unfold angerHalfDefectF angerFresnelPlus angerFresnelMinus
  simp only [Pi.add_apply, Pi.sub_apply]
  set s : ℂ := (Real.sqrt (π * x / 2) : ℂ)
  set w : ℂ := (Real.sqrt (2 * x / π) : ℂ)
  set D := deriv (angerJ (-1/2)) (x : ℂ)
  have hD : D = (-(x * angerJ (1/2) x) + 1 / π - angerJ (-1/2) x / 2) / x := by
    rw [eq_div_iff hx0]; linear_combination hw
  rw [hD]
  field_simp
  linear_combination hsw - π * w * htrig

/-- Continuity of the defect `F`. -/
theorem continuous_angerHalfDefectF : Continuous angerHalfDefectF := by
  have h1 : Continuous fun x : ℝ => angerJ (1/2) x := (angerJ_entire _).continuous.comp continuous_ofReal
  have hw : Continuous fun x : ℝ => ((Real.sqrt (2 * x / π) : ℝ) : ℂ) :=
    continuous_ofReal.comp (by fun_prop)
  have hC := fresnelCosInt_entire.continuous.comp hw
  have hS := fresnelSinInt_entire.continuous.comp hw
  unfold angerHalfDefectF angerFresnelPlus angerFresnelMinus
  exact ((continuous_ofReal.comp (by fun_prop)).mul h1).sub
    (((hC.add hS).mul (by fun_prop)).add ((hC.sub hS).mul (by fun_prop)))

/-- Continuity of the defect `G`. -/
theorem continuous_angerHalfDefectG : Continuous angerHalfDefectG := by
  have h1 : Continuous fun x : ℝ => angerJ (-1/2) x :=
    (angerJ_entire _).continuous.comp continuous_ofReal
  have hw : Continuous fun x : ℝ => ((Real.sqrt (2 * x / π) : ℝ) : ℂ) :=
    continuous_ofReal.comp (by fun_prop)
  have hC := fresnelCosInt_entire.continuous.comp hw
  have hS := fresnelSinInt_entire.continuous.comp hw
  unfold angerHalfDefectG angerFresnelPlus angerFresnelMinus
  exact ((continuous_ofReal.comp (by fun_prop)).mul h1).sub
    (((hC.add hS).mul (by fun_prop)).sub ((hC.sub hS).mul (by fun_prop)))

/-- Both defects vanish at the origin. -/
theorem angerHalfDefect_zero : angerHalfDefectF 0 = 0 ∧ angerHalfDefectG 0 = 0 := by
  simp [angerHalfDefectF, angerHalfDefectG, angerFresnelPlus, angerFresnelMinus,
    fresnelCosInt, fresnelSinInt]

/-- A function on `[0, ∞)` with zero derivative on `(0, ∞)` and continuous at `0` is constant. -/
theorem angerHalf_eq_of_hasDerivAt_zero {u : ℝ → ℂ} (hu : Continuous u)
    (hd : ∀ x, 0 < x → HasDerivAt u 0 x) {x : ℝ} (hx : 0 < x) : u x = u 0 := by
  have hconst : ∀ y, 0 < y → u y = u x := fun y hy =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hd z hz).deriv) hy hx
  have ht : Tendsto u (𝓝[>] 0) (𝓝 (u 0)) := (hu.tendsto 0).mono_left nhdsWithin_le_nhds
  have ht' : Tendsto u (𝓝[>] 0) (𝓝 (u x)) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => (hconst y hy).symm)
  exact tendsto_nhds_unique ht' ht

/-- Both defects vanish on `(0, ∞)`: `F cos - G sin` and `F sin + G cos` are constant. -/
theorem angerHalfDefect_eq_zero {x : ℝ} (hx : 0 < x) :
    angerHalfDefectF x = 0 ∧ angerHalfDefectG x = 0 := by
  set u : ℝ → ℂ := fun y => angerHalfDefectF y * cos y - angerHalfDefectG y * sin y
  set v' : ℝ → ℂ := fun y => angerHalfDefectF y * sin y + angerHalfDefectG y * cos y
  have hsin (y : ℝ) := (Complex.hasDerivAt_sin (y : ℂ)).comp_ofReal
  have hcos (y : ℝ) := (Complex.hasDerivAt_cos (y : ℂ)).comp_ofReal
  have hu : ∀ y, 0 < y → HasDerivAt u 0 y := fun y hy => by
    have := ((hasDerivAt_angerHalfDefectF hy).mul (hcos y)).sub
      ((hasDerivAt_angerHalfDefectG hy).mul (hsin y))
    refine this.congr_deriv ?_
    ring
  have hv : ∀ y, 0 < y → HasDerivAt v' 0 y := fun y hy => by
    have := ((hasDerivAt_angerHalfDefectF hy).mul (hsin y)).add
      ((hasDerivAt_angerHalfDefectG hy).mul (hcos y))
    refine this.congr_deriv ?_
    ring
  have hcu : Continuous u := by
    exact (continuous_angerHalfDefectF.mul (by fun_prop)).sub
      (continuous_angerHalfDefectG.mul (by fun_prop))
  have hcv : Continuous v' := by
    exact (continuous_angerHalfDefectF.mul (by fun_prop)).add
      (continuous_angerHalfDefectG.mul (by fun_prop))
  have hu0 := angerHalf_eq_of_hasDerivAt_zero hcu hu hx
  have hv0 := angerHalf_eq_of_hasDerivAt_zero hcv hv hx
  obtain ⟨hF0, hG0⟩ := angerHalfDefect_zero
  simp only [u, v', hF0, hG0, zero_mul, sub_zero, add_zero] at hu0 hv0
  have htrig := sin_sq_add_cos_sq (x : ℂ)
  constructor
  · linear_combination cos (x : ℂ) * hu0 + sin (x : ℂ) * hv0 +
      -angerHalfDefectF x * htrig
  · linear_combination -sin (x : ℂ) * hu0 + cos (x : ℂ) * hv0 +
      -angerHalfDefectG x * htrig

/-- `r^{1/2} = √r` for `r ≥ 0`. -/
theorem ofReal_cpow_half {r : ℝ} (hr : 0 ≤ r) : (r : ℂ) ^ (1/2 : ℂ) = (Real.sqrt r : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow hr]; push_cast; ring_nf

/-- `r^{-1/2} = (√r)⁻¹` for `r ≥ 0`. -/
theorem ofReal_cpow_neg_half {r : ℝ} (hr : 0 ≤ r) :
    (r : ℂ) ^ (-1/2 : ℂ) = ((Real.sqrt r : ℂ))⁻¹ := by
  rw [show (-1/2 : ℂ) = -(1/2) by ring, cpow_neg, ofReal_cpow_half hr]

/-- The slit plane is invariant under positive real scaling. -/
theorem mul_mem_slitPlane_of_pos {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ slitPlane) :
    (r : ℂ) * z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mul_im, add_zero]
  rcases hz with h | h
  · exact Or.inl (mul_pos hr h)
  · exact Or.inr (mul_ne_zero hr.ne' h)

/-- Positive reals accumulate at `1` in the punctured complex neighbourhood. -/
theorem frequently_ofReal_pos {P : ℂ → Prop} (hP : ∀ x : ℝ, 0 < x → P x) :
    ∃ᶠ z in 𝓝[≠] (1 : ℂ), P z := by
  have hu : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
      rw [add_zero] at this
      have h2 := (continuous_ofReal.tendsto _).comp this
      simpa [Function.comp_def] using h2
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have h' : (1 + 1 / ((n:ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
  exact hu.frequently (Frequently.of_forall fun n => hP _ (by positivity))

/-- The Fresnel right-hand sides of DLMF 11.10.19–20 are holomorphic on the slit plane. -/
theorem differentiableOn_angerHalf_rhs (A B : ℂ → ℂ) (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) :
    DifferentiableOn ℂ (fun z : ℂ => (π*z/2)^(-1/2:ℂ) *
      (angerFresnelPlus ((2*z/π)^(1/2:ℂ)) * A z - angerFresnelMinus ((2*z/π)^(1/2:ℂ)) * B z))
      slitPlane := by
  intro z hz
  have h1 : π * z / 2 ∈ slitPlane := by
    have := mul_mem_slitPlane_of_pos (by positivity : (0:ℝ) < π / 2) hz
    convert this using 1; push_cast; ring
  have h2 : 2 * z / π ∈ slitPlane := by
    have := mul_mem_slitPlane_of_pos (by positivity : (0:ℝ) < 2 / π) hz
    convert this using 1; push_cast; ring
  have hc1 : DifferentiableAt ℂ (fun z : ℂ => (π*z/2)^(-1/2:ℂ)) z :=
    DifferentiableAt.cpow (by fun_prop) (differentiableAt_const _) h1
  have hc2 : DifferentiableAt ℂ (fun z : ℂ => (2*z/π)^(1/2:ℂ)) z :=
    DifferentiableAt.cpow (by fun_prop) (differentiableAt_const _) h2
  have hP : DifferentiableAt ℂ (fun z : ℂ => angerFresnelPlus ((2*z/π)^(1/2:ℂ))) z := by
    unfold angerFresnelPlus
    exact ((fresnelCosInt_entire _).comp z hc2).add ((fresnelSinInt_entire _).comp z hc2)
  have hM : DifferentiableAt ℂ (fun z : ℂ => angerFresnelMinus ((2*z/π)^(1/2:ℂ))) z := by
    unfold angerFresnelMinus
    exact ((fresnelCosInt_entire _).comp z hc2).sub ((fresnelSinInt_entire _).comp z hc2)
  exact (hc1.mul ((hP.mul (hA z)).sub (hM.mul (hB z)))).differentiableWithinAt

/-- The slit plane is preconnected. -/
theorem isPreconnected_slitPlane' : IsPreconnected slitPlane :=
  (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected

/-- angerJ half 19. -/
@[dlmf 11.10.E19]
theorem angerJ_half_19 {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ (-1/2) z = (π*z/2)^(-1/2:ℂ)*(angerFresnelPlus ((2*z/π)^(1/2:ℂ))*cos z-angerFresnelMinus ((2*z/π)^(1/2:ℂ))*sin z) := by
  have hf : AnalyticOnNhd ℂ (angerJ (-1/2)) slitPlane :=
    (analyticOnNhd_univ_iff_differentiable.2 (angerJ_entire _)).mono (subset_univ _)
  have hg := (differentiableOn_angerHalf_rhs cos sin differentiable_cos differentiable_sin).analyticOnNhd
    isOpen_slitPlane
  refine hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_slitPlane' one_mem_slitPlane
    (frequently_ofReal_pos fun x hx => ?_) hz
  have h := (angerHalfDefect_eq_zero hx).2
  unfold angerHalfDefectG at h
  have hs0 : (Real.sqrt (π * x / 2) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne'
  rw [show π * (x : ℂ) / 2 = ((π * x / 2 : ℝ) : ℂ) by push_cast; ring,
    show 2 * (x : ℂ) / π = ((2 * x / π : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow_neg_half (by positivity), ofReal_cpow_half (by positivity),
    eq_inv_mul_iff_mul_eq₀ hs0]
  linear_combination h

/-- angerJ half 20. -/
@[dlmf 11.10.E20]
theorem angerJ_half_20 {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ (1/2) z = (π*z/2)^(-1/2:ℂ)*(angerFresnelPlus ((2*z/π)^(1/2:ℂ))*sin z+angerFresnelMinus ((2*z/π)^(1/2:ℂ))*cos z) := by
  have hf : AnalyticOnNhd ℂ (angerJ (1/2)) slitPlane :=
    (analyticOnNhd_univ_iff_differentiable.2 (angerJ_entire _)).mono (subset_univ _)
  have hg := (differentiableOn_angerHalf_rhs sin (fun z => -cos z) differentiable_sin
    differentiable_cos.neg).analyticOnNhd isOpen_slitPlane
  have key := hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_slitPlane'
    one_mem_slitPlane (frequently_ofReal_pos fun x hx => ?_) hz
  · rw [key]; ring
  have h := (angerHalfDefect_eq_zero hx).1
  unfold angerHalfDefectF at h
  have hs0 : (Real.sqrt (π * x / 2) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne'
  rw [show π * (x : ℂ) / 2 = ((π * x / 2 : ℝ) : ℂ) by push_cast; ring,
    show 2 * (x : ℂ) / π = ((2 * x / π : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow_neg_half (by positivity), ofReal_cpow_half (by positivity),
    eq_inv_mul_iff_mul_eq₀ hs0]
  linear_combination h

/-- anger weber half. -/
@[dlmf 11.10.E19, dlmf 11.10.E20]
theorem anger_weber_half (z : ℂ) :
    angerJ (-1/2) z = weberE (1/2) z ∧ angerJ (1/2) z = -weberE (-1/2) z := by
  have hc : cos (π*(1/2:ℂ)) = 0 := by
    rw [show π*(1/2:ℂ) = (π/2:ℝ) by push_cast; ring, ← ofReal_cos, Real.cos_pi_div_two]; simp
  have hs : sin (π*(1/2:ℂ)) = 1 := by
    rw [show π*(1/2:ℂ) = (π/2:ℝ) by push_cast; ring, ← ofReal_sin, Real.sin_pi_div_two]; simp
  have h1 := weber_anger (1/2) z
  have h2 := anger_weber (1/2) z
  rw [hc, hs] at h1 h2
  rw [show (-1/2:ℂ) = -(1/2) by ring]
  constructor
  · linear_combination -h1
  · linear_combination h2

/-- Number of terms floor((n-1)/2)+1, with empty case n=0. This is `(n+1)/2` in
natural-number division (corrected 2026-10-20 from `n/2`, which gave no term at `n = 1`). -/
@[dlmf 11.10.E24]
def weberM1 (n : ℕ) : ℕ :=
  (n+1)/2

/-- Number of terms ceil((n-3)/2)+1 for n positive. -/
@[dlmf 11.10.E24]
def weberM2 (n : ℕ) : ℕ :=
  n/2

/-- `cos(nπ) = (-1)ⁿ` in `ℂ`. -/
theorem cos_nat_mul_pi_complex (n : ℕ) : cos ((n:ℂ)*π) = (-1)^n := by
  rw [show (n:ℂ)*π = ((n*π:ℝ):ℂ) by push_cast; ring, ← ofReal_cos, Real.cos_nat_mul_pi]
  push_cast; ring

/-- `Γ(1/2 + j) Γ(1/2 - j) = (-1)^j π`. -/
theorem Gamma_half_add_mul_Gamma_half_sub (j : ℕ) :
    Gamma (1/2+j) * Gamma (1/2-j) = (-1)^j * π := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1/2+j)
  rw [show 1-(1/2+(j:ℂ)) = 1/2-j by ring, show (π:ℂ)*(1/2+j) = j*π + π/2 by ring,
    Complex.sin_add_pi_div_two, cos_nat_mul_pi_complex] at h
  rw [h]
  rcases neg_one_pow_eq_or ℂ j with h1 | h1 <;> rw [h1] <;> ring

/-- DLMF 11.10.22 for even order `2m`. -/
theorem weberE_nat_even (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE ((2*m:ℕ):ℂ) z = -struveH ((2*m:ℕ):ℂ) z+1/π*∑ k ∈ Finset.range m,
      Gamma (k+1/2)/Gamma (((2*m:ℕ):ℂ)+1/2-k)*(z/2)^(((2*m:ℕ):ℤ)-2*k-1) := by
  have hz2 : z/2 ≠ 0 := div_ne_zero (slitPlane_ne_zero hz) two_ne_zero
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [weberE_series]
  have hs : sin (π*((2*m:ℕ):ℂ)/2) = 0 := by
    rw [show π*((2*m:ℕ):ℂ)/2 = (m:ℂ)*π by push_cast; ring, Complex.sin_nat_mul_pi]
  have hc : cos (π*((2*m:ℕ):ℂ)/2) = (-1)^m := by
    rw [show π*((2*m:ℕ):ℂ)/2 = (m:ℂ)*π by push_cast; ring, cos_nat_mul_pi_complex]
  rw [hs, hc, zero_mul, zero_sub]
  set f : ℕ → ℂ := fun k => (-1)^k*(z/2)^(2*k+1)/(Gamma (k+((2*m:ℕ):ℂ)/2+3/2)*
    Gamma (k-((2*m:ℕ):ℂ)/2+3/2))
  have h := hasSum_angerS2 ((2*m:ℕ):ℂ) z
  rw [← hasSum_nat_add_iff' m] at h
  have hH : HasSum (fun k => f (k+m)) ((-1)^m*struveH ((2*m:ℕ):ℂ) z) := by
    rw [struveH, show ((2*m:ℕ):ℂ)+1 = ((2*m+1:ℕ):ℂ) by push_cast; ring, cpow_natCast,
      ← mul_assoc]
    refine ((hasSum_struveHCore _ z).mul_left ((-1)^m*(z/2)^(2*m+1))).congr_fun fun k => ?_
    simp only [f, struveCoeff]
    rw [show ((k+m:ℕ):ℂ)+((2*m:ℕ):ℂ)/2+3/2 = (k:ℂ)+((2*m:ℕ):ℂ)+3/2 by push_cast; ring,
      show ((k+m:ℕ):ℂ)-((2*m:ℕ):ℂ)/2+3/2 = (k:ℂ)+3/2 by push_cast; ring]
    rw [show 2*(k+m)+1 = (2*m+1)+2*k by ring, pow_add, pow_add, pow_mul]
    ring
  have hu := h.unique hH
  have hsum : (-1)^m * ∑ i ∈ Finset.range m, f i = -(1/π*∑ k ∈ Finset.range m,
      Gamma (k+1/2)/Gamma (((2*m:ℕ):ℂ)+1/2-k)*(z/2)^(((2*m:ℕ):ℤ)-2*k-1)) := by
    rw [← Finset.sum_range_reflect, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨k, rfl⟩ : ∃ k, m = k+j+1 := ⟨m-j-1, by simp at hj; omega⟩
    rw [show k+j+1-1-j = k by omega]
    simp only [f]
    have hG := Gamma_half_add_mul_Gamma_half_sub j
    rw [show (k:ℂ)+((2*(k+j+1):ℕ):ℂ)/2+3/2 = ((2*(k+j+1):ℕ):ℂ)+1/2-j by push_cast; ring,
      show (k:ℂ)-((2*(k+j+1):ℕ):ℂ)/2+3/2 = 1/2-j by push_cast; ring,
      show ((2*(k+j+1):ℕ):ℤ)-2*(j:ℤ)-1 = ((2*k+1:ℕ):ℤ) by push_cast; ring, zpow_natCast]
    have hG2 : Gamma (1/2-(j:ℂ)) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hG
      exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hπ) hG.symm
    rw [show (j:ℂ)+1/2 = 1/2+j by ring]
    have hGi : (Gamma (1/2-(j:ℂ)))⁻¹ = Gamma (1/2+j) * ((-1:ℂ)^j * (π:ℂ))⁻¹ := by
      have hG1 : Gamma (1/2+(j:ℂ)) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hG
        exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hπ) hG.symm
      rw [← hG, mul_inv, ← mul_assoc, mul_inv_cancel₀ hG1, one_mul]
    rw [div_eq_mul_inv _ (_ * Gamma (1/2-(j:ℂ))), mul_inv, hGi]
    rw [pow_add, pow_add, pow_one]
    have e : ((-1:ℂ))^k * (-1)^k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have e2 : ((-1:ℂ))^j ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    rw [sq, e, one_mul]
  have e : ((-1:ℂ))^m * (-1)^m - 1 = 0 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination -(-1:ℂ)^m*hu - hsum - struveH ((2*m:ℕ):ℂ) z*e


/-- DLMF 11.10.22 for odd order `2m+1`. -/
theorem weberE_nat_odd (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE ((2*m+1:ℕ):ℂ) z = -struveH ((2*m+1:ℕ):ℂ) z+1/π*∑ k ∈ Finset.range (m+1),
      Gamma (k+1/2)/Gamma (((2*m+1:ℕ):ℂ)+1/2-k)*(z/2)^(((2*m+1:ℕ):ℤ)-2*k-1) := by
  have hz2 : z/2 ≠ 0 := div_ne_zero (slitPlane_ne_zero hz) two_ne_zero
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [weberE_series]
  have hs : sin (π*((2*m+1:ℕ):ℂ)/2) = (-1)^m := by
    rw [show π*((2*m+1:ℕ):ℂ)/2 = (m:ℂ)*π + π/2 by push_cast; ring, Complex.sin_add_pi_div_two,
      cos_nat_mul_pi_complex]
  have hc : cos (π*((2*m+1:ℕ):ℂ)/2) = 0 := by
    rw [show π*((2*m+1:ℕ):ℂ)/2 = (m:ℂ)*π + π/2 by push_cast; ring, Complex.cos_add_pi_div_two,
      Complex.sin_nat_mul_pi, neg_zero]
  rw [hs, hc, zero_mul, sub_zero]
  set f : ℕ → ℂ := fun k => (-1)^k*(z/2)^(2*k)/(Gamma (k+((2*m+1:ℕ):ℂ)/2+1)*
    Gamma (k-((2*m+1:ℕ):ℂ)/2+1))
  have h := hasSum_angerS1 ((2*m+1:ℕ):ℂ) z
  rw [← hasSum_nat_add_iff' (m+1)] at h
  have hH : HasSum (fun k => f (k+(m+1))) (-(-1)^m*struveH ((2*m+1:ℕ):ℂ) z) := by
    rw [struveH, show ((2*m+1:ℕ):ℂ)+1 = ((2*m+2:ℕ):ℂ) by push_cast; ring, cpow_natCast,
      ← mul_assoc]
    refine ((hasSum_struveHCore _ z).mul_left (-(-1)^m*(z/2)^(2*m+2))).congr_fun fun k => ?_
    simp only [f, struveCoeff]
    rw [show ((k+(m+1):ℕ):ℂ)+((2*m+1:ℕ):ℂ)/2+1 = (k:ℂ)+((2*m+1:ℕ):ℂ)+3/2 by push_cast; ring,
      show ((k+(m+1):ℕ):ℂ)-((2*m+1:ℕ):ℂ)/2+1 = (k:ℂ)+3/2 by push_cast; ring]
    rw [show 2*(k+(m+1)) = (2*m+2)+2*k by ring, pow_add]
    ring
  have hu := h.unique hH
  have hsum : (-1)^m * ∑ i ∈ Finset.range (m+1), f i = 1/π*∑ k ∈ Finset.range (m+1),
      Gamma (k+1/2)/Gamma (((2*m+1:ℕ):ℂ)+1/2-k)*(z/2)^(((2*m+1:ℕ):ℤ)-2*k-1) := by
    rw [← Finset.sum_range_reflect, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨k, rfl⟩ : ∃ k, m = k+j := ⟨m-j, by simp at hj; omega⟩
    rw [show k+j+1-1-j = k by omega]
    simp only [f]
    have hG := Gamma_half_add_mul_Gamma_half_sub j
    rw [show (k:ℂ)+((2*(k+j)+1:ℕ):ℂ)/2+1 = ((2*(k+j)+1:ℕ):ℂ)+1/2-j by push_cast; ring,
      show (k:ℂ)-((2*(k+j)+1:ℕ):ℂ)/2+1 = 1/2-j by push_cast; ring,
      show ((2*(k+j)+1:ℕ):ℤ)-2*(j:ℤ)-1 = ((2*k:ℕ):ℤ) by push_cast; ring, zpow_natCast]
    rw [show (j:ℂ)+1/2 = 1/2+j by ring]
    have hGi : (Gamma (1/2-(j:ℂ)))⁻¹ = Gamma (1/2+j) * ((-1:ℂ)^j * (π:ℂ))⁻¹ := by
      have hG1 : Gamma (1/2+(j:ℂ)) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hG
        exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hπ) hG.symm
      rw [← hG, mul_inv, ← mul_assoc, mul_inv_cancel₀ hG1, one_mul]
    rw [div_eq_mul_inv _ (_ * Gamma (1/2-(j:ℂ))), mul_inv, hGi]
    rw [pow_add]
    have e : ((-1:ℂ))^k * (-1)^k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have e2 : ((-1:ℂ))^j ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    rw [sq, e, one_mul]
  have e : ((-1:ℂ))^m * (-1)^m - 1 = 0 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (-1:ℂ)^m*hu + hsum - struveH ((2*m+1:ℕ):ℂ) z*e


/-- DLMF 11.10.23 for even order `-2m`. -/
theorem weberE_neg_nat_even (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE (-((2*m:ℕ):ℂ)) z = -struveH (-((2*m:ℕ):ℂ)) z+(-1)^(2*m+1)/π*∑ k ∈ Finset.range m,
      Gamma (((2*m:ℕ):ℂ)-k-1/2)/Gamma (k+3/2)*(z/2)^(-((2*m:ℕ):ℤ)+2*k+1) := by
  have hz2 : z/2 ≠ 0 := div_ne_zero (slitPlane_ne_zero hz) two_ne_zero
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [weberE_series]
  have hs : sin (π*(-((2*m:ℕ):ℂ))/2) = 0 := by
    rw [show π*(-((2*m:ℕ):ℂ))/2 = -((m:ℂ)*π) by push_cast; ring, Complex.sin_neg,
      Complex.sin_nat_mul_pi, neg_zero]
  have hc : cos (π*(-((2*m:ℕ):ℂ))/2) = (-1)^m := by
    rw [show π*(-((2*m:ℕ):ℂ))/2 = -((m:ℂ)*π) by push_cast; ring, Complex.cos_neg, cos_nat_mul_pi_complex]
  rw [hs, hc, zero_mul, zero_sub]
  set h : ℕ → ℂ := fun j => (-1)^j*(z/2)^(2*(j:ℤ)+1-2*m)/(Gamma (j+3/2)*Gamma (j-((2*m:ℕ):ℂ)+3/2))
  have hH : HasSum h (struveH (-((2*m:ℕ):ℂ)) z) := by
    rw [struveH, show -((2*m:ℕ):ℂ)+1 = (((1-2*m:ℤ)):ℂ) by push_cast; ring, cpow_intCast]
    refine ((hasSum_struveHCore _ z).mul_left _).congr_fun fun j => ?_
    simp only [h, struveCoeff]
    rw [show (2*(j:ℤ)+1-2*m) = (1-2*m) + ((2*j:ℕ):ℤ) by push_cast; ring, zpow_add₀ hz2,
      zpow_natCast, show (j:ℂ)+-((2*m:ℕ):ℂ)+3/2 = (j:ℂ)-((2*m:ℕ):ℂ)+3/2 by ring]
    ring
  rw [← hasSum_nat_add_iff' m] at hH
  have hS := (hasSum_angerS2 (-((2*m:ℕ):ℂ)) z).mul_left ((-1:ℂ)^m)
  have hT := hH.unique (hS.congr_fun fun k => ?_)
  rotate_left
  · simp only [h]
    rw [show (2*((k+m:ℕ):ℤ)+1-2*m) = ((2*k+1:ℕ):ℤ) by push_cast; ring, zpow_natCast,
      show ((k+m:ℕ):ℂ)+3/2 = (k:ℂ)-(-((2*m:ℕ):ℂ))/2+3/2 by push_cast; ring,
      show ((k+m:ℕ):ℂ)-((2*m:ℕ):ℂ)+3/2 = (k:ℂ)+(-((2*m:ℕ):ℂ))/2+3/2 by push_cast; ring,
      pow_add]
    ring
  have hsum : ∑ j ∈ Finset.range m, h j = (-1)^(2*m+1)/π*∑ k ∈ Finset.range m,
      Gamma (((2*m:ℕ):ℂ)-k-1/2)/Gamma (k+3/2)*(z/2)^(-((2*m:ℕ):ℤ)+2*k+1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < m := by simpa using hj
    obtain ⟨i, hi⟩ : ∃ i, 2*m = i+j+1 := ⟨2*m-j-1, by omega⟩
    simp only [h]
    have hG := Gamma_half_add_mul_Gamma_half_sub i
    have e1 : (j:ℂ)-((2*m:ℕ):ℂ)+3/2 = 1/2-i := by
      rw [hi]; push_cast; ring
    have e2 : ((2*m:ℕ):ℂ)-j-1/2 = 1/2+i := by
      rw [hi]; push_cast; ring
    rw [e1, e2, show (2*(j:ℤ)+1-2*m) = -((2*m:ℕ):ℤ)+2*j+1 by push_cast; ring]
    have hG1 : Gamma (1/2+(i:ℂ)) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hG
      exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hπ) hG.symm
    have hGi : (Gamma (1/2-(i:ℂ)))⁻¹ = Gamma (1/2+i) * ((-1:ℂ)^i * (π:ℂ))⁻¹ := by
      rw [← hG, mul_inv, ← mul_assoc, mul_inv_cancel₀ hG1, one_mul]
    rw [div_eq_mul_inv _ (_ * Gamma (1/2-(i:ℂ))), mul_inv, hGi]
    have hp : ((-1:ℂ))^(2*m+1) = (-1)^i * (-1)^j := by
      rw [show 2*m+1 = i+j+2 by omega, pow_add, pow_add]; norm_num
    rw [hp]
    have e2 : ((-1:ℂ))^i ≠ 0 := pow_ne_zero _ (by norm_num)
    have ei : (((-1:ℂ))^i)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    field_simp
    rw [ei, mul_one]
  linear_combination hT + hsum


/-- DLMF 11.10.23 for odd order `-(2m+1)`. -/
theorem weberE_neg_nat_odd (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE (-((2*m+1:ℕ):ℂ)) z = -struveH (-((2*m+1:ℕ):ℂ)) z+(-1)^(2*m+1+1)/π*
      ∑ k ∈ Finset.range m,
      Gamma (((2*m+1:ℕ):ℂ)-k-1/2)/Gamma (k+3/2)*(z/2)^(-((2*m+1:ℕ):ℤ)+2*k+1) := by
  have hz2 : z/2 ≠ 0 := div_ne_zero (slitPlane_ne_zero hz) two_ne_zero
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [weberE_series]
  have hs : sin (π*(-((2*m+1:ℕ):ℂ))/2) = -(-1)^m := by
    rw [show π*(-((2*m+1:ℕ):ℂ))/2 = -((m:ℂ)*π + π/2) by push_cast; ring, Complex.sin_neg,
      Complex.sin_add_pi_div_two, cos_nat_mul_pi_complex]
  have hc : cos (π*(-((2*m+1:ℕ):ℂ))/2) = 0 := by
    rw [show π*(-((2*m+1:ℕ):ℂ))/2 = -((m:ℂ)*π + π/2) by push_cast; ring, Complex.cos_neg,
      Complex.cos_add_pi_div_two, Complex.sin_nat_mul_pi, neg_zero]
  rw [hs, hc, zero_mul, sub_zero]
  set h : ℕ → ℂ := fun j => (-1)^j*(z/2)^(2*(j:ℤ)-2*m)/(Gamma (j+3/2)*
    Gamma (j-((2*m+1:ℕ):ℂ)+3/2))
  have hH : HasSum h (struveH (-((2*m+1:ℕ):ℂ)) z) := by
    rw [struveH, show -((2*m+1:ℕ):ℂ)+1 = (((-2*m:ℤ)):ℂ) by push_cast; ring, cpow_intCast]
    refine ((hasSum_struveHCore _ z).mul_left _).congr_fun fun j => ?_
    simp only [h, struveCoeff]
    rw [show (2*(j:ℤ)-2*m) = (-2*m) + ((2*j:ℕ):ℤ) by push_cast; ring, zpow_add₀ hz2,
      zpow_natCast, show (j:ℂ)+-((2*m+1:ℕ):ℂ)+3/2 = (j:ℂ)-((2*m+1:ℕ):ℂ)+3/2 by ring]
    ring
  rw [← hasSum_nat_add_iff' m] at hH
  have hS := (hasSum_angerS1 (-((2*m+1:ℕ):ℂ)) z).mul_left ((-1:ℂ)^m)
  have hT := hH.unique (hS.congr_fun fun k => ?_)
  rotate_left
  · simp only [h]
    rw [show (2*((k+m:ℕ):ℤ)-2*m) = ((2*k:ℕ):ℤ) by push_cast; ring, zpow_natCast,
      show ((k+m:ℕ):ℂ)+3/2 = (k:ℂ)-(-((2*m+1:ℕ):ℂ))/2+1 by push_cast; ring,
      show ((k+m:ℕ):ℂ)-((2*m+1:ℕ):ℂ)+3/2 = (k:ℂ)+(-((2*m+1:ℕ):ℂ))/2+1 by push_cast; ring,
      pow_add]
    ring
  have hsum : ∑ j ∈ Finset.range m, h j = (-1)^(2*m+1+1)/π*∑ k ∈ Finset.range m,
      Gamma (((2*m+1:ℕ):ℂ)-k-1/2)/Gamma (k+3/2)*(z/2)^(-((2*m+1:ℕ):ℤ)+2*k+1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < m := by simpa using hj
    obtain ⟨i, hi⟩ : ∃ i, 2*m+1 = i+j+1 := ⟨2*m-j, by omega⟩
    simp only [h]
    have hG := Gamma_half_add_mul_Gamma_half_sub i
    have e1 : (j:ℂ)-((2*m+1:ℕ):ℂ)+3/2 = 1/2-i := by
      rw [hi]; push_cast; ring
    have e2 : ((2*m+1:ℕ):ℂ)-j-1/2 = 1/2+i := by
      rw [hi]; push_cast; ring
    rw [e1, e2, show (2*(j:ℤ)-2*m) = -((2*m+1:ℕ):ℤ)+2*j+1 by push_cast; ring]
    have hG1 : Gamma (1/2+(i:ℂ)) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hG
      exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hπ) hG.symm
    have hGi : (Gamma (1/2-(i:ℂ)))⁻¹ = Gamma (1/2+i) * ((-1:ℂ)^i * (π:ℂ))⁻¹ := by
      rw [← hG, mul_inv, ← mul_assoc, mul_inv_cancel₀ hG1, one_mul]
    rw [div_eq_mul_inv _ (_ * Gamma (1/2-(i:ℂ))), mul_inv, hGi]
    have hp : ((-1:ℂ))^(2*m+1+1) = (-1)^i * (-1)^j := by
      rw [show 2*m+1+1 = i+j+2 by omega, pow_add, pow_add]; norm_num
    rw [hp]
    have e2 : ((-1:ℂ))^i ≠ 0 := pow_ne_zero _ (by norm_num)
    have ei : (((-1:ℂ))^i)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    field_simp
    rw [ei, mul_one]
  linear_combination hT + hsum

/-- weberE nat. -/
@[dlmf 11.10.E22]
theorem weberE_nat (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE n z = -struveH n z+1/π*∑ k ∈ Finset.range (weberM1 n), Gamma (k+1/2)/Gamma (n+1/2-k)*(z/2)^((n:ℤ)-2*k-1) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show weberM1 (2*m) = m by simp only [weberM1]; omega]
    exact weberE_nat_even m hz
  · rw [show weberM1 (2*m+1) = m+1 by simp only [weberM1]; omega]
    exact weberE_nat_odd m hz

/-- weberE neg nat. -/
@[dlmf 11.10.E23]
theorem weberE_neg_nat (n : ℕ) (hn : 0 < n) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE (-n) z = -struveH (-n) z+(-1)^(n+1)/π*∑ k ∈ Finset.range (weberM2 n), Gamma (n-k-1/2)/Gamma (k+3/2)*(z/2)^(-(n:ℤ)+2*k+1) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show weberM2 (2*m) = m by simp only [weberM2]; omega]
    exact weberE_neg_nat_even m hz
  · rw [show weberM2 (2*m+1) = m by simp only [weberM2]; omega]
    exact weberE_neg_nat_odd m hz

/-- Special value with the removable order-zero value retained. -/
@[dlmf 11.10.E25]
theorem angerJ_zero (ν : ℂ) :
    angerJ ν 0 = if ν=0 then 1 else sin (π*ν)/(π*ν) := by
  by_cases hν : ν=0
  · subst ν
    simp [angerJ]
  · rw [if_neg hν]
    unfold angerJ
    simp only [zero_mul, sub_zero]
    rw [integral_cos_mul_complex hν]
    try simp only [Complex.ofReal_zero, mul_zero, sin_zero, zero_div, sub_zero]
    rw [mul_comm ν (π:ℂ)]
    ring

/-- Special value with the removable order-zero value retained. -/
@[dlmf 11.10.E25]
theorem weberE_zero (ν : ℂ) :
    weberE ν 0 = if ν=0 then 0 else (1-cos (π*ν))/(π*ν) := by
  by_cases hν : ν=0
  · subst ν
    simp [weberE]
  · rw [if_neg hν]
    have hd (t : ℝ) : HasDerivAt (fun t : ℝ => -cos (ν*t)/ν) (sin (ν*t)) t := by
      have hh := (((Complex.hasDerivAt_cos (ν*t)).comp (t:ℂ)
        ((hasDerivAt_id (t:ℂ)).const_mul ν)).neg.div_const ν).comp_ofReal
      convert hh using 1
      · funext x; simp only [Function.comp_apply, Pi.neg_apply]
      · field_simp
    have hi:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((by fun_prop : Continuous (fun t : ℝ => sin (ν*t))).intervalIntegrable 0 π)
    unfold weberE
    simp only [zero_mul,sub_zero]
    rw [hi]
    simp only [Complex.ofReal_zero, mul_zero, cos_zero]
    rw [mul_comm ν (π:ℂ)]
    ring

/-- weberE zero order. -/
@[dlmf 11.10.E26]
theorem weberE_zero_order (z : ℂ) :
    weberE 0 z = -struveH 0 z := by
  rw [weberE_series]
  simp only [mul_zero, zero_div, sin_zero, cos_zero, zero_mul, one_mul, zero_sub, neg_inj]
  refine (hasSum_angerS2 0 z).unique ?_
  rw [struveH, zero_add, cpow_one]
  refine ((hasSum_struveHCore 0 z).mul_left (z/2)).congr_fun fun k => ?_
  simp only [struveCoeff, zero_div, add_zero, sub_zero]
  ring

/-- `Γ(3/2) Γ(1/2) = π/2`. -/
theorem Gamma_three_halves_mul_Gamma_one_half :
    Gamma (3/2) * Gamma (1/2) = π/2 := by
  rw [show (3/2:ℂ) = 1/2+1 by norm_num, Complex.Gamma_add_one _ (by norm_num),
    Complex.Gamma_one_half_eq]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [mul_assoc, ← cpow_add _ _ hπ]
  norm_num
  ring

/-- weberE one order. -/
@[dlmf 11.10.E26]
theorem weberE_one_order (z : ℂ) :
    weberE 1 z = 2/π-struveH 1 z := by
  rw [weberE_series]
  have hs : sin (π*(1:ℂ)/2) = 1 := by
    rw [show π*(1:ℂ)/2 = ((π/2:ℝ):ℂ) by push_cast; ring, ← ofReal_sin, Real.sin_pi_div_two]; simp
  have hc : cos (π*(1:ℂ)/2) = 0 := by
    rw [show π*(1:ℂ)/2 = ((π/2:ℝ):ℂ) by push_cast; ring, ← ofReal_cos, Real.cos_pi_div_two]; simp
  rw [hs, hc, one_mul, zero_mul, sub_zero]
  have h := hasSum_angerS1 1 z
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, mul_zero,
    pow_zero, one_mul] at h
  have h0 : (1:ℂ) / (Gamma (1/2+1) * Gamma (0-1/2+1)) = 2/π := by
    rw [show (1/2:ℂ)+1 = 3/2 by norm_num, show (0:ℂ)-1/2+1 = 1/2 by norm_num,
      Gamma_three_halves_mul_Gamma_one_half]
    field_simp
  rw [show (1:ℂ)/2 = 1/2 from rfl] at h
  have hH : HasSum (fun k : ℕ => (-1)^(k+1)*(z/2)^(2*(k+1))/(Gamma (((k+1:ℕ):ℂ)+1/2+1)*
      Gamma (((k+1:ℕ):ℂ)-1/2+1))) (-struveH 1 z) := by
    rw [struveH, show (1:ℂ)+1 = ((2:ℕ):ℂ) by norm_num, cpow_natCast, ← neg_mul]
    refine ((hasSum_struveHCore 1 z).mul_left (-(z/2)^2)).congr_fun fun k => ?_
    simp only [struveCoeff]
    rw [show ((k+1:ℕ):ℂ)+1/2+1 = (k:ℂ)+1+3/2 by push_cast; ring,
      show ((k+1:ℕ):ℂ)-1/2+1 = (k:ℂ)+3/2 by push_cast; ring]
    ring
  have := h.unique hH
  rw [h0] at this
  linear_combination this

/-- angerJ order deriv zero. -/
@[dlmf 11.10.E27]
theorem angerJ_order_deriv_zero (z : ℂ) :
    HasDerivAt (fun ν => angerJ ν z) (π/2*struveH 0 z) 0 := by
  convert angerJ_hasDerivAt_order 0 z using 1
  have hE := weberE_zero_order z
  simp only [weberE, zero_mul, zero_sub, sin_neg] at hE
  rw [intervalIntegral.integral_neg] at hE
  have := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => -(sin (0*(θ:ℂ)-z*Real.sin θ)*θ)) (a := 0) (b := π) π
  simp only [sub_self, sub_zero, Real.sin_pi_sub] at this
  have hsplit : (∫ x in (0:ℝ)..π, -(sin (0*((π-x:ℝ):ℂ)-z*Real.sin x)*((π-x:ℝ):ℂ))) =
      π*(∫ x in (0:ℝ)..π, sin (z*Real.sin x)) -
        ∫ x in (0:ℝ)..π, -(sin (0*(x:ℂ)-z*Real.sin x)*x) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (intervalIntegrable_zero_pi _ (by fun_prop))
        (intervalIntegrable_zero_pi _ (by fun_prop))]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [zero_mul, zero_sub, sin_neg]
    push_cast; ring
  rw [hsplit] at this
  have hI : (∫ x in (0:ℝ)..π, -(sin (0*(x:ℂ)-z*Real.sin x)*x)) =
      π*(∫ x in (0:ℝ)..π, sin (z*Real.sin x))/2 := by linear_combination -this/2
  rw [hI]
  have hπ := pi_complex_ne_zero
  have hH : struveH 0 z = 1/π*∫ x in (0:ℝ)..π, sin (z*Real.sin x) := by
    linear_combination hE
  rw [hH]
  field_simp

/-- weberE order deriv zero. -/
@[dlmf 11.10.E28]
theorem weberE_order_deriv_zero (z : ℂ) :
    HasDerivAt (fun ν => weberE ν z) (π/2*besselJ 0 z) 0 := by
  convert weberE_hasDerivAt_order 0 z using 1
  have hJ := besselJ_int_eq_integral_cos 0 z
  simp only [Int.cast_zero, zero_mul, sub_zero] at hJ
  have := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => cos (0*(θ:ℂ)-z*Real.sin θ)*θ) (a := 0) (b := π) π
  simp only [sub_self, sub_zero, Real.sin_pi_sub] at this
  have hsplit : (∫ x in (0:ℝ)..π, cos (0*((π-x:ℝ):ℂ)-z*Real.sin x)*((π-x:ℝ):ℂ)) =
      π*(∫ x in (0:ℝ)..π, cos (z*sin x)) - ∫ x in (0:ℝ)..π, cos (0*(x:ℂ)-z*Real.sin x)*x := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    simp only [zero_mul, zero_sub, cos_neg, ofReal_sin]
    push_cast; ring
  rw [hsplit] at this
  have hI : (∫ x in (0:ℝ)..π, cos (0*(x:ℂ)-z*Real.sin x)*x) =
      π*(∫ x in (0:ℝ)..π, cos (z*sin x))/2 := by linear_combination -this/2
  rw [hJ, hI]
  have hπ := pi_complex_ne_zero
  field_simp

/-- angerJ int. -/
@[dlmf 11.10.E29]
theorem angerJ_int (n : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ n z = besselJ n z := by
  exact angerJ_int_aux n hz

/-- Folding `[0, π]` about `π/2`: `∫₀^π f = ∫₀^{π/2} (f(π/2+ψ) + f(π/2-ψ)) dψ`. -/
theorem integral_zero_pi_fold {f : ℝ → ℂ} (hf : Continuous f) :
    ∫ θ in (0:ℝ)..π, f θ = ∫ ψ in (0:ℝ)..(π / 2), (f (π / 2 + ψ) + f (π / 2 - ψ)) := by
  have h1 : IntervalIntegrable (fun ψ => f (π / 2 + ψ)) volume 0 (π / 2) :=
    (hf.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun ψ => f (π / 2 - ψ)) volume 0 (π / 2) :=
    (hf.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _),
    intervalIntegral.integral_add h1 h2, add_comm]
  congr 1
  · rw [intervalIntegral.integral_comp_add_left (fun x => f x) (π / 2)]
    norm_num [add_halves]
  · rw [intervalIntegral.integral_comp_sub_left (fun x => f x) (π / 2)]
    norm_num

/-- The folded Anger integrand: `cos(ν(π/2±ψ) - z cos ψ)` summed over both signs. -/
theorem angerFold_cos (ν z : ℂ) (ψ : ℝ) :
    cos (ν * ((π / 2 + ψ : ℝ) : ℂ) - z * Real.sin (π / 2 + ψ)) +
      cos (ν * ((π / 2 - ψ : ℝ) : ℂ) - z * Real.sin (π / 2 - ψ)) =
    2 * (((2 * sin (ν * π / 2)) / 2 * sin (z * Real.cos ψ) +
      (2 * cos (ν * π / 2)) / 2 * cos (z * Real.cos ψ)) * cos (ν * ψ)) := by
  rw [add_comm (π / 2) ψ, Real.sin_add_pi_div_two, Real.sin_pi_div_two_sub, add_comm ψ]
  push_cast
  have e1 : ν * (π / 2 + ψ) - z * cos (ψ : ℂ) = (ν * π / 2 - z * cos (ψ : ℂ)) + ν * ψ := by ring
  have e2 : ν * (π / 2 - ψ) - z * cos (ψ : ℂ) = (ν * π / 2 - z * cos (ψ : ℂ)) - ν * ψ := by ring
  rw [e1, e2]
  simp only [cos_add, cos_sub, sin_sub]
  ring

/-- The folded Weber integrand: `sin(ν(π/2±ψ) - z cos ψ)` summed over both signs. -/
theorem angerFold_sin (ν z : ℂ) (ψ : ℝ) :
    sin (ν * ((π / 2 + ψ : ℝ) : ℂ) - z * Real.sin (π / 2 + ψ)) +
      sin (ν * ((π / 2 - ψ : ℝ) : ℂ) - z * Real.sin (π / 2 - ψ)) =
    2 * (((-2 * cos (ν * π / 2)) / 2 * sin (z * Real.cos ψ) +
      (2 * sin (ν * π / 2)) / 2 * cos (z * Real.cos ψ)) * cos (ν * ψ)) := by
  rw [add_comm (π / 2) ψ, Real.sin_add_pi_div_two, Real.sin_pi_div_two_sub, add_comm ψ]
  push_cast
  have e1 : ν * (π / 2 + ψ) - z * cos (ψ : ℂ) = (ν * π / 2 - z * cos (ψ : ℂ)) + ν * ψ := by ring
  have e2 : ν * (π / 2 - ψ) - z * cos (ψ : ℂ) = (ν * π / 2 - z * cos (ψ : ℂ)) - ν * ψ := by ring
  rw [e1, e2]
  simp only [sin_add, sin_sub, cos_sub]
  ring

/-- angerJ bessel products. -/
@[dlmf 11.10.E30]
theorem angerJ_bessel_products (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 2*sin (ν*π/2)*(-1)^k*besselJ (k-ν/2+1/2) (z/2)*besselJ (k+ν/2+1/2) (z/2)+2*cos (ν*π/2)*(if k=0 then 1/2 else 1)*(-1)^k*besselJ (k-ν/2) (z/2)*besselJ (k+ν/2) (z/2)) (angerJ ν z) := by
  convert hasSum_besselJ_products_integral (2 * sin (ν * π / 2)) (2 * cos (ν * π / 2)) ν hz
    using 1
  rw [angerJ, integral_zero_pi_fold (by fun_prop)]
  simp_rw [angerFold_cos]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- weberE bessel products. -/
@[dlmf 11.10.E31]
theorem weberE_bessel_products (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => -2*cos (ν*π/2)*(-1)^k*besselJ (k-ν/2+1/2) (z/2)*besselJ (k+ν/2+1/2) (z/2)+2*sin (ν*π/2)*(if k=0 then 1/2 else 1)*(-1)^k*besselJ (k-ν/2) (z/2)*besselJ (k+ν/2) (z/2)) (weberE ν z) := by
  convert hasSum_besselJ_products_integral (-2 * cos (ν * π / 2)) (2 * sin (ν * π / 2)) ν hz
    using 1
  rw [weberE, integral_zero_pi_fold (by fun_prop)]
  simp_rw [angerFold_sin]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- angerJ recurrence. -/
@[dlmf 11.10.E32]
theorem angerJ_recurrence (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    angerJ (ν-1) z+angerJ (ν+1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν)) := by
  exact angerJ_recurrence_aux ν hz

/-- angerJ deriv. -/
@[dlmf 11.10.E34]
theorem angerJ_deriv (ν z : ℂ) :
    HasDerivAt (angerJ ν) ((angerJ (ν-1) z-angerJ (ν+1) z)/2) z := by
  exact hasDerivAt_angerJ_shift ν z

/-- angerJ weighted deriv add. -/
@[dlmf 11.10.E36]
theorem angerJ_weighted_deriv_add (ν z : ℂ) :
    z*deriv (angerJ ν) z+(1:ℂ)*ν*angerJ ν z = (1:ℂ)*z*angerJ (ν-1) z+(1:ℂ)*(sin (π*ν))/π := by
  rw [(hasDerivAt_angerJ_shift ν z).deriv]
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [zero_mul, zero_add, mul_zero]
    rw [angerJ_zero ν]
    split_ifs with h
    · subst h; simp
    · field_simp
  · have := angerJ_recurrence_aux ν hz
    rw [show angerJ (ν+1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν))-angerJ (ν-1) z by linear_combination this]
    field_simp
    ring

/-- angerJ weighted deriv sub. -/
@[dlmf 11.10.E36]
theorem angerJ_weighted_deriv_sub (ν z : ℂ) :
    z*deriv (angerJ ν) z+(-1:ℂ)*ν*angerJ ν z = (-1:ℂ)*z*angerJ (ν-(-1)) z+(-1:ℂ)*(sin (π*ν))/π := by
  rw [(hasDerivAt_angerJ_shift ν z).deriv, sub_neg_eq_add]
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [zero_mul, zero_add, mul_zero]
    rw [angerJ_zero ν]
    split_ifs with h
    · subst h; simp
    · field_simp
  · have := angerJ_recurrence_aux ν hz
    rw [show angerJ (ν-1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν))-angerJ (ν+1) z by linear_combination this]
    field_simp
    ring

/-- weberE recurrence. -/
@[dlmf 11.10.E33]
theorem weberE_recurrence (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    weberE (ν-1) z+weberE (ν+1) z = 2*ν/z*weberE ν z-2/(π*z)*(1-cos (π*ν)) := by
  exact weberE_recurrence_aux ν hz

/-- weberE deriv. -/
@[dlmf 11.10.E35]
theorem weberE_deriv (ν z : ℂ) :
    HasDerivAt (weberE ν) ((weberE (ν-1) z-weberE (ν+1) z)/2) z := by
  exact hasDerivAt_weberE_shift ν z

/-- weberE weighted deriv add. -/
@[dlmf 11.10.E37]
theorem weberE_weighted_deriv_add (ν z : ℂ) :
    z*deriv (weberE ν) z+(1:ℂ)*ν*weberE ν z = (1:ℂ)*z*weberE (ν-1) z+(1:ℂ)*(1-cos (π*ν))/π := by
  rw [(hasDerivAt_weberE_shift ν z).deriv]
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [zero_mul, zero_add, mul_zero]
    rw [weberE_zero ν]
    split_ifs with h
    · subst h; simp
    · field_simp
  · have := weberE_recurrence_aux ν hz
    rw [show weberE (ν+1) z = 2*ν/z*weberE ν z-2/(π*z)*(1-cos (π*ν))-weberE (ν-1) z by linear_combination this]
    field_simp
    ring

/-- weberE weighted deriv sub. -/
@[dlmf 11.10.E37]
theorem weberE_weighted_deriv_sub (ν z : ℂ) :
    z*deriv (weberE ν) z+(-1:ℂ)*ν*weberE ν z = (-1:ℂ)*z*weberE (ν-(-1)) z+(-1:ℂ)*(1-cos (π*ν))/π := by
  rw [(hasDerivAt_weberE_shift ν z).deriv, sub_neg_eq_add]
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [zero_mul, zero_add, mul_zero]
    rw [weberE_zero ν]
    split_ifs with h
    · subst h; simp
    · field_simp
  · have := weberE_recurrence_aux ν hz
    rw [show weberE (ν-1) z = 2*ν/z*weberE ν z-2/(π*z)*(1-cos (π*ν))-weberE (ν+1) z by linear_combination this]
    field_simp
    ring

end DLMF.Struve
