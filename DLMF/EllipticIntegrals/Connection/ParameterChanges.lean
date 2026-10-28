/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Connection.ModulusChanges

/-!
# Hyperbolic substitutions and elliptic parameter changes

Hyperbolic amplitude substitutions and transformations of the third-kind parameter.

Source references and common attribution are retained in
`DLMF.EllipticIntegrals.Connection`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory

open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### Helpers for 19.7.7 (substitution `θ = arctan (sinh u)`) -/

/-- Identity under the stated parameter and domain assumptions: `((r : ℂ) * z) ^ w = (r : ℂ) ^ w *
z ^ w`. -/
lemma p19lR1_mul_ofReal_cpow {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rcases eq_or_ne z 0 with rfl | hz
  · rcases eq_or_ne w 0 with rfl | hw
    · simp
    · simp [zero_cpow hw]
  · rw [cpow_def_of_ne_zero (mul_ne_zero hr' hz), cpow_def_of_ne_zero hr', cpow_def_of_ne_zero hz,
      show (r : ℂ) * z = z * r by ring, log_mul_ofReal r hr z hz, ← exp_add, ofReal_log hr.le]
    ring_nf

/-- A segment integral along `[0, iφ]`. -/
lemma p19lR1_segmentIntegral_I (f : ℂ → ℂ) (φ : ℝ) :
    ei19a_segmentIntegral f (I * φ) = I * ∫ u in (0 : ℝ)..φ, f (I * u) := by
  have h := ei19a_segmentIntegral_ofReal (fun z => I * f (I * z)) φ
  rw [intervalIntegral.integral_const_mul] at h
  rw [← h, ei19a_segmentIntegral, ei19a_segmentIntegral]
  congr 1; funext t; ring_nf

/-- Identity under the stated parameter and domain assumptions: `Complex.sin (I * u) ^ 2 =
-((Real.sinh u : ℝ) : ℂ) ^ 2`. -/
lemma p19lR1_sin_I_sq (u : ℝ) : Complex.sin (I * u) ^ 2 = -((Real.sinh u : ℝ) : ℂ) ^ 2 := by
  rw [mul_comm, Complex.sin_mul_I, ofReal_sinh, mul_pow, I_sq]; ring

/-- Substitution `θ = arctan (sinh u)`, `dθ = du / cosh u`. -/
lemma p19lR1_subst_arctan_sinh {G : ℝ → ℂ} (hG : ContinuousOn G (Ioo (-(π / 2)) (π / 2)))
    (φ : ℝ) :
    ∫ u in (0 : ℝ)..φ, ((Real.cosh u)⁻¹ : ℝ) • G (Real.arctan (Real.sinh u)) =
      ∫ θ in (0 : ℝ)..(Real.arctan (Real.sinh φ)), G θ := by
  have h := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := φ)
    (f := fun u => Real.arctan (Real.sinh u)) (f' := fun u => (Real.cosh u)⁻¹) (g := G)
    (fun u _ => by
      have := (Real.hasDerivAt_arctan (Real.sinh u)).comp u (Real.hasDerivAt_sinh u)
      refine this.congr_deriv ?_
      have hc := Real.cosh_pos u
      rw [← Real.cosh_sq']; field_simp)
    (by
      refine Continuous.continuousOn ?_
      exact continuous_iff_continuousAt.2 fun u =>
        (Real.continuous_cosh.continuousAt).inv₀ (Real.cosh_pos u).ne')
    (hG.mono (by
      rintro _ ⟨u, -, rfl⟩
      exact ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩))
  simpa [Real.sinh_zero, Real.arctan_zero] using h

/-- Identity under the stated parameter and domain assumptions: `Real.sin (Real.arctan (Real.sinh
u)) = Real.sinh u / Real.cosh u ∧ Real.cos (Real.arctan (Real.sinh u)) = (Real.cosh u)⁻¹`. -/
lemma p19lR1_sin_cos_arctan_sinh (u : ℝ) :
    Real.sin (Real.arctan (Real.sinh u)) = Real.sinh u / Real.cosh u ∧
      Real.cos (Real.arctan (Real.sinh u)) = (Real.cosh u)⁻¹ := by
  have hs : Real.sqrt (1 + Real.sinh u ^ 2) = Real.cosh u := by
    rw [← Real.cosh_sq', Real.sqrt_sq (Real.cosh_pos u).le]
  rw [Real.sin_arctan, Real.cos_arctan, hs, one_div]
  exact ⟨rfl, rfl⟩

/-- Along the substitution, `1 - (1 - b) sin²θ = (1 + b sinh²u)/cosh²u`. -/
lemma p19lR1_one_sub_arctan_sinh (b : ℂ) (u : ℝ) :
    1 - (1 - b) * (Real.sin (Real.arctan (Real.sinh u)) : ℂ) ^ 2 =
      ((((Real.cosh u) ^ 2)⁻¹ : ℝ) : ℂ) * (1 + b * ((Real.sinh u : ℝ) : ℂ) ^ 2) := by
  rw [(p19lR1_sin_cos_arctan_sinh u).1]
  have hc : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
  have h2 : (Real.cosh u : ℂ) ^ 2 = 1 + (Real.sinh u : ℂ) ^ 2 := by
    have := Real.cosh_sq' u; exact_mod_cast (by linarith : Real.cosh u ^ 2 = 1 + Real.sinh u ^ 2)
  rw [ofReal_div, div_pow, ofReal_inv, ofReal_pow]
  field_simp
  linear_combination h2

/-- Formula under the stated hypotheses: `1 - (1 - b) * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane`. -/
lemma p19lR1_conv_mem {b : ℂ} (hb : b ∈ slitPlane) (θ : ℝ) :
    1 - (1 - b) * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane := by
  have := ei19a_one_sub_mul_mem_slitPlane (z := 1 - b) (by rw [sub_sub_cancel]; exact hb)
    (sq_nonneg (Real.sin θ)) (Real.sin_sq_le_one θ)
  convert this using 2; push_cast; ring

/-- Identity under the stated parameter and domain assumptions: `(1 - (1 - b) * (Real.sin
(Real.arctan (Real.sinh u)) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = (Real.cosh u : ℂ) * (1 + b *
((Real.sinh u : ℝ) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) ∧ (1 - (1 - b) * (Real.sin (Real.arctan
(Real.sinh u)) : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (Real.cosh u : ℂ)⁻¹ * (1 + b * ((Real.sinh u : ℝ) :
ℂ) ^ 2) ^ (1 / 2 : ℂ)`. -/
lemma p19lR1_cpow_arctan_sinh (b : ℂ) (u : ℝ) :
    (1 - (1 - b) * (Real.sin (Real.arctan (Real.sinh u)) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      (Real.cosh u : ℂ) * (1 + b * ((Real.sinh u : ℝ) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) ∧
    (1 - (1 - b) * (Real.sin (Real.arctan (Real.sinh u)) : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
      (Real.cosh u : ℂ)⁻¹ * (1 + b * ((Real.sinh u : ℝ) : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
  have hc := Real.cosh_pos u
  rw [p19lR1_one_sub_arctan_sinh, p19lR1_mul_ofReal_cpow (by positivity),
    p19lR1_mul_ofReal_cpow (by positivity), (p19lR1_inv_sq_cpow hc).1, (p19lR1_inv_sq_cpow hc).2]
  exact ⟨rfl, rfl⟩

/-- Identity under the stated parameter and domain assumptions: `incEllIntFk (I * φ) k = I *
incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k)`. -/
lemma p19lR1_imag_arg_F (φ : ℝ) {k : ℂ} (hk : k ^ 2 ∈ slitPlane) :
    incEllIntFk (I * φ) k = I * incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) := by
  rw [incEllIntFk, p19lR1_segmentIntegral_I, incEllIntFk_ofReal_eq_integral,
    ei19a_jacobiComodulusk_sq]
  congr 1
  rw [← p19lR1_subst_arctan_sinh]
  · refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [p19lR1_sin_I_sq, (p19lR1_cpow_arctan_sinh _ u).1, real_smul]
    have hc : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
    rw [ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    ring_nf
  · exact (continuous_iff_continuousAt.2 fun θ =>
      (continuousAt_cpow_const (p19lR1_conv_mem hk θ)).comp
        (f := fun θ : ℝ => 1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) (by fun_prop)).continuousOn

/-- Nonvanishing under the stated hypotheses: `Real.cos θ ≠ 0`. -/
lemma p19lR1_cos_ne_zero_of_mem {θ : ℝ} (h : θ ∈ Ioo (-(π / 2)) (π / 2)) : Real.cos θ ≠ 0 :=
  (Real.cos_pos_of_mem_Ioo h).ne'

/-- The stated relation follows from the given hypotheses: `uIcc 0 ψ ⊆ Ioo (-(π / 2)) (π / 2)`. -/
lemma p19lR1_uIcc_sub_Ioo {ψ : ℝ} (h : ψ ∈ Ioo (-(π / 2)) (π / 2)) :
    uIcc 0 ψ ⊆ Ioo (-(π / 2)) (π / 2) := by
  intro x hx
  rcases le_total 0 ψ with h0 | h0
  · rw [uIcc_of_le h0] at hx; exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, h.2]⟩
  · rw [uIcc_of_ge h0] at hx; exact ⟨by linarith [hx.1, h.1], by linarith [hx.2, Real.pi_pos]⟩

/-- Identity under the stated parameter and domain assumptions: `incEllIntEk (I * φ) k = I *
(incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) - incEllIntEk (Real.arctan
(Real.sinh φ)) (jacobiComodulusk k) + Real.tan (Real.arctan (Real.sinh φ)) * (1 - (1 - k ^ 2)
* (Real.sin (Real.arctan (Real.sinh φ)) : ℂ) ^ 2) ^ (1 / 2 : ℂ))`. -/
lemma p19lR1_imag_arg_E (φ : ℝ) {k : ℂ} (hk : k ^ 2 ∈ slitPlane) :
    incEllIntEk (I * φ) k = I * (incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) -
        incEllIntEk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) +
          Real.tan (Real.arctan (Real.sinh φ)) *
            (1 - (1 - k ^ 2) * (Real.sin (Real.arctan (Real.sinh φ)) : ℂ) ^ 2) ^ (1 / 2 : ℂ)) := by
  set ψ := Real.arctan (Real.sinh φ) with hψ
  set k' := jacobiComodulusk k with hk'
  have hk'2 : k' ^ 2 = 1 - k ^ 2 := ei19a_jacobiComodulusk_sq k
  have hk's : 1 - k' ^ 2 ∈ slitPlane := by rw [hk'2, sub_sub_cancel]; exact hk
  have hψI : ψ ∈ Ioo (-(π / 2)) (π / 2) :=
    ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hsub := p19lR1_uIcc_sub_Ioo hψI
  set G : ℝ → ℂ := fun θ => p19lR1_Δ k' θ / (Real.cos θ : ℂ) ^ 2 with hG
  have hΔc := p19lR1_continuous_Δ hk's
  have hGc : ContinuousOn G (Ioo (-(π / 2)) (π / 2)) := by
    refine hΔc.continuousOn.div (by fun_prop) fun θ hθ => ?_
    exact pow_ne_zero _ (by exact_mod_cast p19lR1_cos_ne_zero_of_mem hθ)
  -- the substitution
  have h1 : incEllIntEk (I * φ) k = I * ∫ θ in (0 : ℝ)..ψ, G θ := by
    rw [incEllIntEk, p19lR1_segmentIntegral_I, ← p19lR1_subst_arctan_sinh hGc]
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hG, p19lR1_Δ, hk'2, (p19lR1_cpow_arctan_sinh _ u).2, p19lR1_sin_I_sq, real_smul,
      (p19lR1_sin_cos_arctan_sinh u).2]
    have hc0 : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
    have e : (1 - k ^ 2 * -((Real.sinh u : ℝ) : ℂ) ^ 2) = 1 + k ^ 2 * ((Real.sinh u : ℝ) : ℂ) ^ 2 := by
      ring
    rw [e, ofReal_inv]
    field_simp
  -- the integration by parts identity
  set D : ℝ → ℂ := fun θ => G θ - (p19lR1_Δ k' θ)⁻¹ + p19lR1_Δ k' θ with hD
  have hDc : ContinuousOn D (uIcc 0 ψ) := by
    refine ((hGc.mono hsub).sub ?_).add hΔc.continuousOn
    exact (continuous_iff_continuousAt.2 fun θ =>
      (hΔc.continuousAt).inv₀ (p19lR1_Δ_ne_zero hk's θ)).continuousOn
  have hFTC : ∫ θ in (0 : ℝ)..ψ, D θ = Real.tan ψ * p19lR1_Δ k' ψ := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ : ℝ => (Real.tan θ : ℂ) * p19lR1_Δ k' θ) (f' := D) (a := 0) (b := ψ)
      (fun θ hθ => by
        have hcos := p19lR1_cos_ne_zero_of_mem (hsub hθ)
        have h := ((Real.hasDerivAt_tan hcos).ofReal_comp).mul (p19lR1_hasDerivAt_Δ hk's θ)
        refine h.congr_deriv ?_
        have hΔ := p19lR1_Δ_ne_zero hk's θ
        have hΔ2 := p19lR1_Δ_sq k' θ
        have hc : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hcos
        simp only [hD, hG, Real.tan_eq_sin_div_cos, ofReal_div, ofReal_one, ofReal_pow]
        field_simp
        linear_combination (-(Real.cos θ : ℂ) ^ 2) * hΔ2)
      (hDc.intervalIntegrable)
    rw [this]; simp [Real.tan_zero]
  have hGint : IntervalIntegrable G volume 0 ψ := (hGc.mono hsub).intervalIntegrable
  have hΔint : IntervalIntegrable (p19lR1_Δ k') volume 0 ψ := hΔc.intervalIntegrable _ _
  have hΔiint : IntervalIntegrable (fun θ => (p19lR1_Δ k' θ)⁻¹) volume 0 ψ :=
    (continuous_iff_continuousAt.2 fun θ =>
      (hΔc.continuousAt).inv₀ (p19lR1_Δ_ne_zero hk's θ)).intervalIntegrable _ _
  have hsplit : ∫ θ in (0 : ℝ)..ψ, G θ = (∫ θ in (0 : ℝ)..ψ, D θ) +
      (∫ θ in (0 : ℝ)..ψ, (p19lR1_Δ k' θ)⁻¹) - ∫ θ in (0 : ℝ)..ψ, p19lR1_Δ k' θ := by
    rw [← intervalIntegral.integral_add ((hGint.sub hΔiint).add hΔint) hΔiint,
      ← intervalIntegral.integral_sub (((hGint.sub hΔiint).add hΔint).add hΔiint) hΔint]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring
  rw [h1, hsplit, hFTC, incEllIntFk_ofReal_eq_integral, incEllIntEk_ofReal_eq_integral]
  simp only [p19lR1_Δ, ← cpow_neg, hk'2]
  ring

/-- Formula under the stated hypotheses: `1 + b * x ∈ slitPlane`. -/
lemma p19lR1_one_add_mem {b : ℂ} (hb : b ∈ slitPlane) {x : ℝ} (hx : 0 ≤ x) :
    1 + b * x ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hb ⊢
  simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, add_im, one_im,
    mul_im, zero_add]
  rcases hx.lt_or_eq with hx | rfl
  · rcases eq_or_ne b.im 0 with h | h
    · left; have := hb.resolve_right (not_not.2 h); nlinarith
    · right; exact mul_ne_zero h hx.ne'
  · left; simp

/-- Estimate under the stated parameter and domain assumptions: `∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤
‖g (t * w)‖`. -/
lemma p19lR1_path_bound {g : ℂ → ℂ} (hg : Continuous g) (w : ℂ)
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, g (t * w) ≠ 0) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖g (t * w)‖ := by
  obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    (nonempty_Icc.2 zero_le_one) (by fun_prop : Continuous fun t : ℝ => ‖g (t * w)‖).continuousOn
  exact ⟨‖g (t0 * w)‖, norm_pos_iff.2 (hne t0 ht0), fun t ht => hmin ht⟩

/-- Identity under the stated parameter and domain assumptions: `incEllIntPik ψ β k = ∫ θ in (0 :
ℝ)..ψ, ((1 - β * (Real.sin θ : ℂ) ^ 2)⁻¹ * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 :
ℂ)))`. -/
lemma p19lR1_incEllIntPik_ofReal_slit (ψ : ℝ) {β : ℂ} (hβ : 1 - β ∈ slitPlane) (k : ℂ) :
    incEllIntPik ψ β k = ∫ θ in (0 : ℝ)..ψ, ((1 - β * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
  obtain ⟨δ, hδ, hb⟩ := p19lR1_exists_norm_lower_gen hβ
  rw [incEllIntPik_eq_segmentIntegral (δ := δ) hδ, ei19a_segmentIntegral_ofReal]
  · simp only [← Complex.ofReal_sin]
  · intro t _
    have := hb (t * ψ)
    push_cast at this; exact this

/-- Identity under the stated parameter and domain assumptions: `incEllIntPik (I * φ) α2 k = I *
(incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) - α2 * incEllIntPik (Real.arctan
(Real.sinh φ)) (1 - α2) (jacobiComodulusk k)) / (1 - α2)`. -/
lemma p19lR1_imag_arg_Pi (φ : ℝ) {k α2 : ℂ} (hk : k ^ 2 ∈ slitPlane) (hα : α2 ∈ slitPlane)
    (hα1 : α2 ≠ 1) :
    incEllIntPik (I * φ) α2 k = I * (incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) -
        α2 * incEllIntPik (Real.arctan (Real.sinh φ)) (1 - α2) (jacobiComodulusk k)) / (1 - α2) := by
  set ψ := Real.arctan (Real.sinh φ) with hψ
  set k' := jacobiComodulusk k with hk'
  have hk'2 : k' ^ 2 = 1 - k ^ 2 := ei19a_jacobiComodulusk_sq k
  have hα1' : (1 : ℂ) - α2 ≠ 0 := sub_ne_zero.2 (Ne.symm hα1)
  have hpath : ∀ u : ℝ, 1 - α2 * Complex.sin (I * u) ^ 2 =
      1 + α2 * (((Real.sinh u) ^ 2 : ℝ) : ℂ) := by
    intro u; rw [p19lR1_sin_I_sq]; push_cast; ring
  -- remove the principal value on the left
  obtain ⟨δ, hδ, hb⟩ := p19lR1_path_bound (g := fun z => 1 - α2 * Complex.sin z ^ 2)
    (by fun_prop) (I * φ) (fun t _ => by
      have : ((t : ℂ) * (I * φ)) = I * ((t * φ : ℝ) : ℂ) := by push_cast; ring
      simp only [this, hpath]
      exact slitPlane_ne_zero (p19lR1_one_add_mem hα (sq_nonneg _)))
  rw [incEllIntPik_eq_segmentIntegral hδ hb, p19lR1_segmentIntegral_I,
    p19lR1_incEllIntPik_ofReal_slit ψ (by rw [sub_sub_cancel]; exact hα),
    incEllIntFk_ofReal_eq_integral]
  set P : ℝ → ℂ := fun θ => 1 - (1 - α2) * (Real.sin θ : ℂ) ^ 2 with hP
  have hPne : ∀ θ, P θ ≠ 0 := fun θ => slitPlane_ne_zero (p19lR1_conv_mem hα θ)
  set H : ℝ → ℂ := fun θ => (Real.cos θ : ℂ) ^ 2 * (P θ)⁻¹ *
    (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) with hH
  have hQc : Continuous fun θ : ℝ => (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) :=
    continuous_iff_continuousAt.2 fun θ =>
      (continuousAt_cpow_const (p19lR1_conv_mem hk θ)).comp
        (f := fun θ : ℝ => 1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) (by fun_prop)
  have hPic : Continuous fun θ => (P θ)⁻¹ :=
    continuous_iff_continuousAt.2 fun θ => ((by fun_prop : Continuous P).continuousAt).inv₀ (hPne θ)
  have hHc : Continuous H := by
    rw [hH]; exact ((by fun_prop : Continuous fun θ : ℝ => (Real.cos θ : ℂ) ^ 2).mul hPic).mul hQc
  have h1 : (∫ u in (0 : ℝ)..φ, (1 - α2 * Complex.sin (I * u) ^ 2)⁻¹ *
      (1 - k ^ 2 * Complex.sin (I * u) ^ 2) ^ (-(1 / 2 : ℂ))) = ∫ θ in (0 : ℝ)..ψ, H θ := by
    rw [← p19lR1_subst_arctan_sinh hHc.continuousOn]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have hPu : P (Real.arctan (Real.sinh u)) =
        ((((Real.cosh u) ^ 2)⁻¹ : ℝ) : ℂ) * (1 + α2 * ((Real.sinh u : ℝ) : ℂ) ^ 2) :=
      p19lR1_one_sub_arctan_sinh α2 u
    simp only [hH, hPu, (p19lR1_cpow_arctan_sinh _ u).1, (p19lR1_sin_cos_arctan_sinh u).2,
      real_smul, p19lR1_sin_I_sq]
    have hc0 : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
    have hA : (1 + α2 * ((Real.sinh u : ℝ) : ℂ) ^ 2) ≠ 0 :=
      slitPlane_ne_zero (by
        have := p19lR1_one_add_mem hα (sq_nonneg (Real.sinh u)); push_cast at this ⊢; exact this)
    have e : (1 - k ^ 2 * -((Real.sinh u : ℝ) : ℂ) ^ 2) = 1 + k ^ 2 * ((Real.sinh u : ℝ) : ℂ) ^ 2 := by
      ring
    have e2 : (1 - α2 * -((Real.sinh u : ℝ) : ℂ) ^ 2) =
        1 + α2 * ((Real.sinh u : ℝ) : ℂ) ^ 2 := by ring
    rw [e, e2, ofReal_inv, ofReal_inv, ofReal_pow]
    field_simp
  rw [h1]
  have hint1 : IntervalIntegrable (fun θ : ℝ =>
      (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) volume 0 ψ :=
    hQc.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ : ℝ => (P θ)⁻¹ *
      (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) volume 0 ψ :=
    (hPic.mul hQc).intervalIntegrable _ _
  have h2 : ∫ θ in (0 : ℝ)..ψ, H θ = ((∫ θ in (0 : ℝ)..ψ,
      (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) - α2 * ∫ θ in (0 : ℝ)..ψ,
        (P θ)⁻¹ * (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) / (1 - α2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hint1
      (hint2.const_mul _), ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hP' := hPne θ
    simp only [hH]
    have hcs : (Real.cos θ : ℂ) ^ 2 = 1 - (Real.sin θ : ℂ) ^ 2 := by
      have := Real.cos_sq' θ; exact_mod_cast this
    rw [hcs]
    field_simp
    simp only [hP]
    ring
  rw [h2, hk'2]
  ring
/-- DLMF 19.7.7 (imaginary-argument transformation): for real `φ`, `tan ψ = sinh φ`
(`ψ = arctan(sinh φ)`), `k² ∉ (-∞, 0]` and `α² ∉ (-∞, 0]`, `α² ≠ 1`:
`F(iφ, k) = iF(ψ, k')`,
`E(iφ, k) = i(F(ψ, k') - E(ψ, k') + tan ψ √(1 - k'² sin²ψ))`,
`Π(iφ, α², k) = i(F(ψ, k') - α²Π(ψ, 1 - α², k'))/(1 - α²)`. -/
@[dlmf 19.7.E7]
theorem incEllInt_imaginary_argument (φ : ℝ) {k α2 : ℂ} (hk : k ^ 2 ∈ slitPlane)
    (hα : α2 ∈ slitPlane) (hα1 : α2 ≠ 1) :
    let ψ := Real.arctan (Real.sinh φ)
    incEllIntFk (I * φ) k = I * incEllIntFk ψ (jacobiComodulusk k) ∧
      incEllIntEk (I * φ) k = I * (incEllIntFk ψ (jacobiComodulusk k) -
        incEllIntEk ψ (jacobiComodulusk k) +
          Real.tan ψ * (1 - (1 - k ^ 2) * (Real.sin ψ : ℂ) ^ 2) ^ (1 / 2 : ℂ)) ∧
      incEllIntPik (I * φ) α2 k = I * (incEllIntFk ψ (jacobiComodulusk k) -
        α2 * incEllIntPik ψ (1 - α2) (jacobiComodulusk k)) / (1 - α2) :=
  ⟨p19lR1_imag_arg_F φ hk, p19lR1_imag_arg_E φ hk, p19lR1_imag_arg_Pi φ hk hα hα1⟩

/-! ### §19.7(iii) Change of parameter of `Π(φ, α², k)` -/

/-- **Admitted.** DLMF 19.7.8: for real `0 < φ < π/2`, `c = csc²φ`, real `0 < k < 1` and real
`α², ω²` with `α²ω² = k²`, `α² ≠ c`, `ω² ≠ c` (Cauchy principal values when `α²` or `ω²`
exceeds `c`):
`Π(φ, α², k) + Π(φ, ω², k) = F(φ, k) + √c R_C((c-1)(c-k²), (c-α²)(c-ω²))`. -/
@[dlmf 19.7.E8]
theorem incEllIntPik_add_first {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : α2 * ω2 = k ^ 2) (hα : α2 ≠ 1 / Real.sin φ ^ 2)
    (hω : ω2 ≠ 1 / Real.sin φ ^ 2) :
    let c := 1 / Real.sin φ ^ 2
    incEllIntPik φ α2 k + incEllIntPik φ ω2 k = incEllIntFk φ k +
      Real.sqrt c * symEllIntRC ((c - 1) * (c - k ^ 2) : ℝ) ((c - α2) * (c - ω2) : ℝ) := by
  sorry

/-- **Admitted.** DLMF 19.7.9: for real `0 < φ < π/2`, `c = csc²φ`, real `0 < k < 1` and real
`α², ω²` with `(1 - α²)(1 - ω²) = 1 - k²`, `α² ≠ c`, `ω² ≠ c`:
`(k² - α²)Π(φ, α², k) + (k² - ω²)Π(φ, ω², k)
= k²F(φ, k) - α²ω² √(c - 1) R_C(c(c - k²), (c - α²)(c - ω²))`. -/
@[dlmf 19.7.E9]
theorem incEllIntPik_add_second {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : (1 - α2) * (1 - ω2) = 1 - k ^ 2) (hα : α2 ≠ 1 / Real.sin φ ^ 2)
    (hω : ω2 ≠ 1 / Real.sin φ ^ 2) :
    let c := 1 / Real.sin φ ^ 2
    ((k ^ 2 - α2 : ℝ) : ℂ) * incEllIntPik φ α2 k + ((k ^ 2 - ω2 : ℝ) : ℂ) * incEllIntPik φ ω2 k =
      (k ^ 2 : ℝ) * incEllIntFk φ k - (α2 * ω2 * Real.sqrt (c - 1) : ℝ) *
        symEllIntRC (c * (c - k ^ 2) : ℝ) ((c - α2) * (c - ω2) : ℝ) := by
  sorry

/-- **Admitted.** DLMF 19.7.10: for real `0 < φ < π/2`, `c = csc²φ`, real `0 < k < 1` and real
`α², ω²` with `(k² - α²)(k² - ω²) = k²(k² - 1)`, `α² ≠ c`, `ω² ≠ c`:
`(1 - α²)Π(φ, α², k) + (1 - ω²)Π(φ, ω², k)
= F(φ, k) + (1 - α² - ω²) √(c - k²) R_C(c(c - 1), (c - α²)(c - ω²))`. -/
@[dlmf 19.7.E10]
theorem incEllIntPik_add_third {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : (k ^ 2 - α2) * (k ^ 2 - ω2) = k ^ 2 * (k ^ 2 - 1))
    (hα : α2 ≠ 1 / Real.sin φ ^ 2) (hω : ω2 ≠ 1 / Real.sin φ ^ 2) :
    let c := 1 / Real.sin φ ^ 2
    ((1 - α2 : ℝ) : ℂ) * incEllIntPik φ α2 k + ((1 - ω2 : ℝ) : ℂ) * incEllIntPik φ ω2 k =
      incEllIntFk φ k + ((1 - α2 - ω2) * Real.sqrt (c - k ^ 2) : ℝ) *
        symEllIntRC (c * (c - 1) : ℝ) ((c - α2) * (c - ω2) : ℝ) := by
  sorry

/-- DLMF §19.7(iii) (prose): under the relation `α²ω² = k²` of 19.7.8, since `k² ≤ c`, `α² > c`
implies `ω² < 1 ≤ c` (for real `0 < k < 1` and `0 < φ < π/2`). -/
@[dlmf 19.7.iii]
theorem first_relation_omega_lt {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : α2 * ω2 = k ^ 2) (hα : 1 / Real.sin φ ^ 2 < α2) :
    ω2 < 1 ∧ 1 ≤ 1 / Real.sin φ ^ 2 := by
  have hs0 : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hs1 : Real.sin φ ^ 2 ≤ 1 := Real.sin_sq_le_one φ
  have hc : 1 ≤ 1 / Real.sin φ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  refine ⟨?_, hc⟩
  have hα0 : 1 < α2 := lt_of_le_of_lt hc hα
  by_contra h
  push Not at h
  nlinarith

end DLMF.EllipticIntegrals

end
