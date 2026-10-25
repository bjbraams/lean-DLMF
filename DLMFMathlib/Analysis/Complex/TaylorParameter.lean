/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import Mathlib.Analysis.Complex.Liouville

/-!
# Parameter derivatives and bounds of Taylor coefficients

Cauchy's circle integral gives holomorphy in a complex parameter of Taylor
coefficients, commutation with a specified parameter derivative, and locally
uniform geometric coefficient bounds. The holomorphy proof is extracted from
`DLMF/Hypergeometric/Asymptotics.lean`; all inputs here are Mathlib-only.
-/

@[expose] public noncomputable section
open Complex Filter MeasureTheory Set Metric
open scoped Nat Real Topology
namespace Complex

/-- Holomorphy in a parameter of Taylor coefficients, through Cauchy's integral formula on the
circle of radius `r`. -/
lemma differentiable_iteratedDeriv_param {G : ℂ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hcont : ∀ a : ℂ, ∀ t : ℂ, ‖t‖ = r → ContinuousAt (fun p : ℂ × ℂ => G p.1 p.2) (a, t))
    (hdt : ∀ a : ℂ, DifferentiableOn ℂ (G a) (Metric.closedBall 0 r))
    (hda : ∀ t : ℂ, ‖t‖ = r → Differentiable ℂ (fun a => G a t)) (N : ℕ) :
    Differentiable ℂ (fun a => iteratedDeriv N (G a) 0) := by
  set c : ℝ → ℂ := circleMap 0 r with hc
  have hcn : ∀ θ, ‖c θ‖ = r := fun θ => by simp [hc, abs_of_pos hr]
  have hc0 : ∀ θ, c θ ≠ 0 := fun θ h => by
    have := hcn θ; rw [h, norm_zero] at this; linarith
  set Φ : ℂ → ℝ → ℂ := fun a θ => (c θ * I) • ((1 / (c θ - 0) ^ (N + 1)) • G a (c θ)) with hΦ
  have hcc : Continuous c := continuous_circleMap 0 r
  have hcont' : Continuous fun p : ℂ × ℝ => Φ p.1 p.2 := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hG : ContinuousAt (fun p : ℂ × ℝ => G p.1 (c p.2)) p := by
      have h1 := hcont p.1 (c p.2) (hcn p.2)
      exact h1.comp (f := fun p : ℂ × ℝ => (p.1, c p.2))
        (continuous_fst.prodMk (hcc.comp continuous_snd)).continuousAt
    simp only [hΦ, smul_eq_mul]
    refine ContinuousAt.mul ((hcc.comp continuous_snd).continuousAt.mul continuousAt_const)
      (ContinuousAt.mul ?_ hG)
    exact (continuousAt_const.div ((hcc.comp continuous_snd).continuousAt.sub
      continuousAt_const |>.pow _) (pow_ne_zero _ (by simpa using hc0 p.2)))
  have hint : Differentiable ℂ (fun a => ∫ θ in (0 : ℝ)..2 * π, Φ a θ) := by
    have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) (2 * π))) :=
      isFiniteMeasure_restrict.mpr (by rw [uIoc_of_le (by positivity)]; exact measure_Ioc_lt_top.ne)
    have hD := Complex.differentiableOn_intervalIntegral_of_locally_dominated (Φ := Φ) (U := univ)
      isOpen_univ (ν := volume) 0 (2 * π)
      (fun a _ => (hcont'.comp (Continuous.prodMk_right a)).aestronglyMeasurable)
      (Eventually.of_forall fun θ => fun a _ => by
        simp only [hΦ, smul_eq_mul]
        exact ((differentiableAt_const _).mul ((differentiableAt_const _).mul
          (hda (c θ) (hcn θ) a))).differentiableWithinAt)
      (fun x _ => by
        have hK : IsCompact (Metric.closedBall x 1 ×ˢ Icc (0 : ℝ) (2 * π)) :=
          (isCompact_closedBall x 1).prod isCompact_Icc
        obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont'.continuousOn
        refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds _ one_pos, fun _ => M,
          integrable_const _, ?_⟩
        refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun θ hθ y hy => ?_)
        have hθ' : θ ∈ Icc (0 : ℝ) (2 * π) := by
          rw [uIoc_of_le (by positivity)] at hθ; exact ⟨hθ.1.le, hθ.2⟩
        exact hM (y, θ) ⟨hy, hθ'⟩)
    exact fun a0 => (hD a0 (mem_univ _)).differentiableAt Filter.univ_mem
  have heq : (fun a => iteratedDeriv N (G a) 0) =
      fun a => ((N ! : ℂ) / (2 * π * I)) * ∫ θ in (0 : ℝ)..2 * π, Φ a θ := by
    funext a
    have h := (hdt a).circleIntegral_one_div_sub_center_pow_smul hr N
    rw [circleIntegral] at h
    have h' : (∫ θ in (0 : ℝ)..2 * π, Φ a θ) = (2 * π * I / N !) * iteratedDeriv N (G a) 0 := by
      rw [smul_eq_mul] at h
      rw [← h]
      simp only [deriv_circleMap, hΦ, hc]
    rw [h']
    have : (N ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
    field_simp
  rw [heq]
  exact (differentiable_const _).mul hint


/-- Parameter differentiation commutes with Taylor derivatives, by differentiating
Cauchy's circle integral under a locally uniform bound on the parameter derivative. -/
theorem hasDerivAt_iteratedDeriv_param {G Gz : ℂ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hcont : ∀ a : ℂ, ∀ t : ℂ, ‖t‖ = r →
      ContinuousAt (fun p : ℂ × ℂ => G p.1 p.2) (a,t))
    (hcontz : ∀ a : ℂ, ∀ t : ℂ, ‖t‖ = r →
      ContinuousAt (fun p : ℂ × ℂ => Gz p.1 p.2) (a,t))
    (hdt : ∀ a : ℂ, DifferentiableOn ℂ (G a) (closedBall 0 r))
    (hdtz : ∀ a : ℂ, DifferentiableOn ℂ (Gz a) (closedBall 0 r))
    (hda : ∀ a t : ℂ, ‖t‖ = r → HasDerivAt (fun a => G a t) (Gz a t) a)
    (N : ℕ) (a₀ : ℂ) :
    HasDerivAt (fun a => iteratedDeriv N (G a) 0)
      (iteratedDeriv N (Gz a₀) 0) a₀ := by
  let c : ℝ → ℂ := circleMap 0 r
  have hcn : ∀ θ, ‖c θ‖ = r := fun θ => by simp [c,abs_of_pos hr]
  have hc0 : ∀ θ, c θ ≠ 0 := fun θ h => by
    have := hcn θ; rw [h,norm_zero] at this; linarith
  let P : (ℂ → ℂ → ℂ) → ℂ → ℝ → ℂ := fun H a θ =>
    (c θ*I) • ((1/(c θ-0)^(N+1)) • H a (c θ))
  have hcc : Continuous c := continuous_circleMap 0 r
  have hPc (H : ℂ → ℂ → ℂ)
      (hH : ∀ a t : ℂ, ‖t‖ = r → ContinuousAt (fun p : ℂ × ℂ => H p.1 p.2) (a,t)) :
      Continuous (fun p : ℂ × ℝ => P H p.1 p.2) := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hH' : ContinuousAt (fun p : ℂ × ℝ => H p.1 (c p.2)) p :=
      (hH p.1 (c p.2) (hcn p.2)).comp
        (f := fun p : ℂ × ℝ => (p.1,c p.2))
        (continuous_fst.prodMk (hcc.comp continuous_snd)).continuousAt
    dsimp only [P]
    simp only [smul_eq_mul]
    refine ContinuousAt.mul ((hcc.comp continuous_snd).continuousAt.mul continuousAt_const)
      (ContinuousAt.mul ?_ hH')
    exact continuousAt_const.div
      (((hcc.comp continuous_snd).continuousAt.sub continuousAt_const).pow _)
      (pow_ne_zero _ (by simpa using hc0 p.2))
  have heq (H : ℂ → ℂ → ℂ)
      (hH : ∀ a : ℂ, DifferentiableOn ℂ (H a) (closedBall 0 r)) (a : ℂ) :
      iteratedDeriv N (H a) 0 = ((N ! : ℂ)/(2*π*I))*∫ θ in (0:ℝ)..2*π, P H a θ := by
    have h := (hH a).circleIntegral_one_div_sub_center_pow_smul hr N
    rw [circleIntegral] at h
    have h' : (∫ θ in (0:ℝ)..2*π, P H a θ) =
        (2*π*I/N !)*iteratedDeriv N (H a) 0 := by
      rw [smul_eq_mul] at h
      rw [← h]
      simp only [deriv_circleMap,P,c]
    rw [h']
    have : (N ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have : (2*π*I : ℂ) ≠ 0 := two_pi_I_ne_zero
    field_simp
  have hP := hPc G hcont
  have hPz := hPc Gz hcontz
  have hK : IsCompact (closedBall a₀ 1 ×ˢ Icc (0:ℝ) (2*π)) :=
    (isCompact_closedBall a₀ 1).prod isCompact_Icc
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hPz.continuousOn
  have hd (a : ℂ) (θ : ℝ) : HasDerivAt (fun a => P G a θ) (P Gz a θ) a := by
    have h := (hda a (c θ) (hcn θ)).const_mul
      ((c θ*I)*(1/(c θ-0)^(N+1)))
    convert h using 1 <;> first | (funext y; simp only [P,smul_eq_mul]; ring) |
      (simp only [P,smul_eq_mul]; ring)
  have hI := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := P G) (F' := P Gz) (bound := fun _ => M)
    (μ := volume) (a := 0) (b := 2*π) (x₀ := a₀)
    (ball_mem_nhds a₀ one_pos)
    (Eventually.of_forall fun a => (hP.comp (Continuous.prodMk_right a)).aestronglyMeasurable)
    ((hP.comp (Continuous.prodMk_right a₀)).intervalIntegrable _ _)
    ((hPz.comp (Continuous.prodMk_right a₀)).aestronglyMeasurable)
    (Eventually.of_forall fun θ hθ a ha => by
      have hθ' : θ ∈ Icc (0:ℝ) (2*π) := by
        rw [uIoc_of_le (by positivity)] at hθ; exact ⟨hθ.1.le,hθ.2⟩
      exact hM (a,θ) ⟨ball_subset_closedBall ha,hθ'⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ a _ => hd a θ)
  have heqG : (fun a => iteratedDeriv N (G a) 0) =
      fun a => ((N ! : ℂ)/(2*π*I))*∫ θ in (0:ℝ)..2*π, P G a θ := funext (heq G hdt)
  rw [heqG,heq Gz hdtz a₀]
  exact hI.2.const_mul _

/-- Uniform Cauchy bounds for Taylor coefficients on a compact parameter ball. -/
theorem exists_uniform_norm_taylorCoeff_le {G : ℂ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hcont : ∀ a : ℂ, ∀ t : ℂ, ‖t‖ = r →
      ContinuousAt (fun p : ℂ × ℂ => G p.1 p.2) (a,t))
    (hdt : ∀ a : ℂ, DifferentiableOn ℂ (G a) (closedBall 0 r))
    (a₀ : ℂ) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ closedBall a₀ R, ∀ n : ℕ,
      ‖iteratedDeriv n (G a) 0 / (n ! : ℂ)‖ ≤ M / r^n := by
  have hK : IsCompact (closedBall a₀ R ×ˢ sphere (0:ℂ) r) :=
    (isCompact_closedBall a₀ R).prod (isCompact_sphere (0:ℂ) r)
  have hc : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2)
      (closedBall a₀ R ×ˢ sphere (0:ℂ) r) := by
    rintro ⟨a,t⟩ ⟨ha,ht⟩
    exact (hcont a t (by simpa using ht)).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max M 0,le_max_right _ _,fun a ha n => ?_⟩
  have hb : ∀ t ∈ sphere (0:ℂ) r, ‖G a t‖ ≤ max M 0 :=
    fun t ht => (hM (a,t) ⟨ha,ht⟩).trans (le_max_left _ _)
  have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    ((hdt a).mono closure_ball_subset_closedBall).diffContOnCl hb
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity)]
  calc ‖iteratedDeriv n (G a) 0‖ ≤ n.factorial * max M 0 / r^n := h
    _ = max M 0 / r^n * n.factorial := by ring

end Complex
