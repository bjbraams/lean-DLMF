/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Framework
public import DLMF.Airy.IntegralRepresentations

/-!
# Incomplete Airy functions, DLMF §9.14

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology
namespace DLMF.Airy

/-- The incomplete contour integral, replacing the upper endpoint of 9.5.4 by a.
The lower endpoint remains infinity on the ray of angle -π/3. -/
def incompleteAiryAi (a z : ℂ) : ℂ :=
  (-rayIntegral (fun t => exp (t ^ 3 / 3 - z * t)) (-π / 3) 1 +
    segmentIntegral (fun t => exp (t ^ 3 / 3 - z * t)) (exp (-π * I / 3)) a) / (2 * π * I)

/-- A segment integral of a derivative is the difference of the primitive at the endpoints. -/
theorem lineIntegral_eq_sub {f g : ℂ → ℂ} (hf : Continuous f) (hg : ∀ z, HasDerivAt g (f z) z)
    (a b : ℂ) : segmentIntegral f a b = g b - g a := by
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => g (a + u * (b - a))) ((b - a) * f (a + t * (b - a))) t := by
    have h := ((hg (a + t * (b - a))).comp (t : ℂ)
      (((hasDerivAt_id (t : ℂ)).mul_const (b - a)).const_add a)).comp_ofReal
    simpa [mul_comm] using h
  have hi : IntervalIntegrable (fun t : ℝ => (b - a) * f (a + t * (b - a))) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => (b - a) * f (a + t * (b - a)))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at h
  simpa [segmentIntegral] using h

/-- For an entire integrand, the segment integral differentiates in its upper endpoint. -/
theorem hasDerivAt_lineIntegral_right {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a b : ℂ) :
    HasDerivAt (fun w => segmentIntegral f a w) (f b) b := by
  obtain ⟨g, hg⟩ := hf.isExactOn_univ
  have hg' (w : ℂ) : HasDerivAt g (f w) w := hg w (mem_univ w)
  have he : (fun w => segmentIntegral f a w) = fun w => g w - g a :=
    funext fun w => lineIntegral_eq_sub hf.continuous hg' a w
  rw [he]
  exact (hg' b).sub_const _

/-- For an entire integrand, the segment integral differentiates in its lower endpoint. -/
theorem hasDerivAt_lineIntegral_left {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a b : ℂ) :
    HasDerivAt (fun w => segmentIntegral f w b) (-f a) a := by
  obtain ⟨g, hg⟩ := hf.isExactOn_univ
  have hg' (w : ℂ) : HasDerivAt g (f w) w := hg w (mem_univ w)
  have he : (fun w => segmentIntegral f w b) = fun w => g b - g w :=
    funext fun w => lineIntegral_eq_sub hf.continuous hg' w b
  rw [he]
  exact (hg' a).const_sub _

/-- The Airy contour integrand is entire. -/
theorem differentiable_airyIntegrand (z : ℂ) :
    Differentiable ℂ fun t : ℂ => exp (t ^ 3 / 3 - z * t) := by fun_prop

/-- Differentiation with respect to the finite endpoint in DLMF §9.14. -/
theorem incompleteAiryAi_endpoint_derivative (a z : ℂ) :
    HasDerivAt (fun b => incompleteAiryAi b z) (exp (a ^ 3 / 3 - z * a) / (2 * π * I)) a := by
  unfold incompleteAiryAi
  exact (((hasDerivAt_lineIntegral_right (differentiable_airyIntegrand z) _ a).const_add
    _).div_const _)

/-- An arc integral of a derivative is the difference of the primitive at the endpoints. -/
theorem arcIntegral_eq_sub {f g : ℂ → ℂ} (hf : Continuous f) (hg : ∀ z, HasDerivAt g (f z) z)
    (α β : ℝ) : arcIntegral f α β = g (exp (β * I)) - g (exp (α * I)) := by
  have hd : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => g (exp (θ * I))) (I * exp (θ * I) * f (exp (θ * I))) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => exp ((θ : ℂ) * I)) (exp (θ * I) * (1 * I)) θ :=
      (((hasDerivAt_id θ).ofReal_comp).mul_const I).cexp
    exact ((hg _).comp θ h1).congr_deriv (by ring)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    ((by fun_prop : Continuous fun θ : ℝ => I * exp (θ * I) * f (exp (θ * I))).intervalIntegrable _ _)

/-- Integrability of the Airy contour integrand on a ray where it decays. -/
theorem integrableOn_airy_ray (z : ℂ) {θ : ℝ} (hc : exp (3 * (((θ + π : ℝ) : ℂ) * I)) = 1) :
    IntegrableOn (fun t : ℝ => exp (θ * I) * exp ((t * exp (θ * I)) ^ 3 / 3 - z * (t * exp (θ * I))))
      (Ioi 1) := by
  have h := (integrableOn_reidRay hc z 0 zero_le_one (Or.inl le_rfl)).neg
  refine h.congr_fun (fun t (ht : 1 < t) => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := by linarith
  simp only [Pi.neg_apply]
  rw [reidKernel_zero_eq_airyIntegrand z _ (u := t * exp (θ * I)), exp_add_pi_mul_I]
  · ring
  · rw [exp_add, exp_log (ofReal_ne_zero.mpr ht0.ne'), exp_add_pi_mul_I]; ring

/-- The primitive along a decaying ray tends to its value at `e^{θi}` plus the ray integral. -/
theorem tendsto_primitive_airy_ray (z : ℂ) {θ : ℝ} (hc : exp (3 * (((θ + π : ℝ) : ℂ) * I)) = 1)
    {g : ℂ → ℂ} (hg : ∀ u, HasDerivAt g (exp (u ^ 3 / 3 - z * u)) u) :
    Tendsto (fun R : ℝ => g (R * exp (θ * I))) atTop
      (𝓝 (g (exp (θ * I)) + rayIntegral (fun t => exp (t ^ 3 / 3 - z * t)) θ 1)) := by
  have hint := integrableOn_airy_ray z hc
  have hlim := intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id
  have hFTC : ∀ R : ℝ, ∫ t in (1 : ℝ)..R, exp (θ * I) *
      exp ((t * exp (θ * I)) ^ 3 / 3 - z * (t * exp (θ * I))) =
        g (R * exp (θ * I)) - g (exp (θ * I)) := by
    intro R
    have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => g (t * exp (θ * I)))
        (exp (θ * I) * exp ((t * exp (θ * I)) ^ 3 / 3 - z * (t * exp (θ * I)))) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * exp (θ * I)) (1 * exp (θ * I)) t :=
        ((hasDerivAt_id t).ofReal_comp).mul_const _
      exact ((hg _).comp t h1).congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((by fun_prop : Continuous fun t : ℝ => exp (θ * I) *
        exp ((t * exp (θ * I)) ^ 3 / 3 - z * (t * exp (θ * I)))).intervalIntegrable _ _)]
    simp
  simp only [hFTC] at hlim
  have := hlim.const_add (g (exp (θ * I)))
  simp only [add_sub_cancel] at this
  exact this

/-- Recovery of the complete Airy contour in DLMF §9.14. -/
theorem incompleteAiryAi_complete_limit (z : ℂ) :
    Tendsto (fun R : ℝ => incompleteAiryAi ((R : ℂ) * exp (π * I / 3)) z) atTop (𝓝 (airyAi z)) := by
  obtain ⟨g, hg⟩ := (differentiable_airyIntegrand z).isExactOn_univ
  have hg' : ∀ u, HasDerivAt g (exp (u ^ 3 / 3 - z * u)) u := fun u => hg u (mem_univ u)
  have hline := lineIntegral_eq_sub (differentiable_airyIntegrand z).continuous hg'
  have harc := arcIntegral_eq_sub (differentiable_airyIntegrand z).continuous hg' (-π / 3) (π / 3)
  have e1 : exp (((π / 3 : ℝ) : ℂ) * I) = exp (π * I / 3) := by push_cast; ring_nf
  have e2 : exp (((-π / 3 : ℝ) : ℂ) * I) = exp (-π * I / 3) := by push_cast; ring_nf
  have ht := tendsto_primitive_airy_ray z (θ := π / 3) (exp_three_mul_of_eq 2 (by ring)) hg'
  rw [e1] at ht
  rw [airyAi_contour_integral, contourIntegral, harc, e1, e2]
  simp only [incompleteAiryAi, hline]
  have := ((ht.sub_const (g (exp (-π * I / 3)))).const_add
    (-rayIntegral (fun t => exp (t ^ 3 / 3 - z * t)) (-π / 3) 1)).div_const (2 * π * I)
  convert this using 2
  ring

/-- The incomplete integral with variable lower endpoint and the upper endpoint at infinity. -/
def incompleteAiryAiLower (a z : ℂ) : ℂ :=
  (segmentIntegral (fun t => exp (t ^ 3 / 3 - z * t)) a (exp (π * I / 3)) +
    rayIntegral (fun t => exp (t ^ 3 / 3 - z * t)) (π / 3) 1) / (2 * π * I)

/-- The lower-endpoint version of the incomplete Airy integral, DLMF §9.14. -/
theorem incompleteAiryAiLower_endpoint_derivative (a z : ℂ) :
    HasDerivAt (fun b => incompleteAiryAiLower b z) (-exp (a ^ 3 / 3 - z * a) / (2 * π * I)) a := by
  unfold incompleteAiryAiLower
  exact (((hasDerivAt_lineIntegral_left (differentiable_airyIntegrand z) a _).add_const
    _).div_const _)

/-- Splitting the complete contour at any finite endpoint, DLMF §9.14. -/
theorem incompleteAiryAi_split (a z : ℂ) :
    incompleteAiryAi a z + incompleteAiryAiLower a z = airyAi z := by
  obtain ⟨g, hg⟩ := (differentiable_airyIntegrand z).isExactOn_univ
  have hg' : ∀ u, HasDerivAt g (exp (u ^ 3 / 3 - z * u)) u := fun u => hg u (mem_univ u)
  have hline := lineIntegral_eq_sub (differentiable_airyIntegrand z).continuous hg'
  have harc := arcIntegral_eq_sub (differentiable_airyIntegrand z).continuous hg' (-π / 3) (π / 3)
  have e1 : exp (((π / 3 : ℝ) : ℂ) * I) = exp (π * I / 3) := by push_cast; ring_nf
  have e2 : exp (((-π / 3 : ℝ) : ℂ) * I) = exp (-π * I / 3) := by push_cast; ring_nf
  rw [airyAi_contour_integral, contourIntegral, harc, e1, e2, incompleteAiryAi,
    incompleteAiryAiLower, hline, hline]
  ring

/-- Recovery with the lower endpoint tending to its original infinite limit, DLMF §9.14. -/
theorem incompleteAiryAiLower_complete_limit (z : ℂ) :
    Tendsto (fun R : ℝ => incompleteAiryAiLower ((R : ℂ) * exp (-π * I / 3)) z) atTop (𝓝 (airyAi z)) := by
  obtain ⟨g, hg⟩ := (differentiable_airyIntegrand z).isExactOn_univ
  have hg' : ∀ u, HasDerivAt g (exp (u ^ 3 / 3 - z * u)) u := fun u => hg u (mem_univ u)
  have hline := lineIntegral_eq_sub (differentiable_airyIntegrand z).continuous hg'
  have harc := arcIntegral_eq_sub (differentiable_airyIntegrand z).continuous hg' (-π / 3) (π / 3)
  have e1 : exp (((π / 3 : ℝ) : ℂ) * I) = exp (π * I / 3) := by push_cast; ring_nf
  have e2 : exp (((-π / 3 : ℝ) : ℂ) * I) = exp (-π * I / 3) := by push_cast; ring_nf
  have ht := tendsto_primitive_airy_ray z (θ := -π / 3) (exp_three_mul_of_eq 1 (by ring)) hg'
  rw [e2] at ht
  rw [airyAi_contour_integral, contourIntegral, harc, e1, e2]
  simp only [incompleteAiryAiLower, hline]
  have := ((ht.const_sub (g (exp (π * I / 3)))).add_const
    (rayIntegral (fun t => exp (t ^ 3 / 3 - z * t)) (π / 3) 1)).div_const (2 * π * I)
  convert this using 2
  ring

end DLMF.Airy
