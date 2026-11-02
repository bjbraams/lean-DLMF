/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Connection.ModulusChanges

/-!
# Imaginary argument and changes of parameter (DLMF §19.7(ii)–(iii))

The imaginary-argument (hyperbolic amplitude) transformation of Legendre's incomplete
integrals and the three transformations of the third-kind parameter, stated for real data
with Cauchy principal values. Here `c = csc²φ` and `R_C = symEllIntRC`.

## Main results

* `incEllInt_imaginary_argument`: the imaginary-argument transformation with
  `tan ψ = sinh φ`, for complex `k` (DLMF 19.7.7).
* `incEllIntPik_add_first`, `incEllIntPik_add_second`, `incEllIntPik_add_third`: the
  parameter changes of `Π(φ, α², k)` (DLMF 19.7.8, 19.7.9, 19.7.10).
* `first_relation_omega_lt`: under `α²ω² = k²`, `α² > c` implies `ω² < c`
  (DLMF §19.7(iii), prose).

## References

* NIST DLMF §19.7.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory

open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### Helpers for 19.7.7 (substitution `θ = arctan (sinh u)`) -/

/-- Identity under the stated parameter and domain assumptions: `((r : ℂ) * z) ^ w = (r : ℂ) ^ w *
z ^ w`. -/
private lemma ofReal_mul_cpow_eq_of_pos {r : ℝ} (hr : 0 < r) (z w : ℂ) :
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
private lemma segmentIntegral_I_mul (f : ℂ → ℂ) (φ : ℝ) :
    segmentIntegral f (I * φ) = I * ∫ u in (0 : ℝ)..φ, f (I * u) := by
  have h := segmentIntegral_ofReal (fun z => I * f (I * z)) φ
  rw [intervalIntegral.integral_const_mul] at h
  rw [← h, segmentIntegral, segmentIntegral]
  congr 1; funext t; ring_nf

/-- Identity under the stated parameter and domain assumptions: `Complex.sin (I * u) ^ 2 =
-((Real.sinh u : ℝ) : ℂ) ^ 2`. -/
private lemma sin_I_mul_sq (u : ℝ) : Complex.sin (I * u) ^ 2 = -((Real.sinh u : ℝ) : ℂ) ^ 2 := by
  rw [mul_comm, Complex.sin_mul_I, ofReal_sinh, mul_pow, I_sq]; ring

/-- Substitution `θ = arctan (sinh u)`, `dθ = du / cosh u`. -/
private lemma integral_arctan_sinh_subst {G : ℝ → ℂ} (hG : ContinuousOn G (Ioo (-(π / 2)) (π / 2)))
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
private lemma sin_cos_arctan_sinh (u : ℝ) :
    Real.sin (Real.arctan (Real.sinh u)) = Real.sinh u / Real.cosh u ∧
      Real.cos (Real.arctan (Real.sinh u)) = (Real.cosh u)⁻¹ := by
  have hs : Real.sqrt (1 + Real.sinh u ^ 2) = Real.cosh u := by
    rw [← Real.cosh_sq', Real.sqrt_sq (Real.cosh_pos u).le]
  rw [Real.sin_arctan, Real.cos_arctan, hs, one_div]
  exact ⟨rfl, rfl⟩

/-- Along the substitution, `1 - (1 - b) sin²θ = (1 + b sinh²u)/cosh²u`. -/
private lemma one_sub_mul_sin_arctan_sinh_sq (b : ℂ) (u : ℝ) :
    1 - (1 - b) * (Real.sin (Real.arctan (Real.sinh u)) : ℂ) ^ 2 =
      ((((Real.cosh u) ^ 2)⁻¹ : ℝ) : ℂ) * (1 + b * ((Real.sinh u : ℝ) : ℂ) ^ 2) := by
  rw [(sin_cos_arctan_sinh u).1]
  have hc : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
  have h2 : (Real.cosh u : ℂ) ^ 2 = 1 + (Real.sinh u : ℂ) ^ 2 := by
    have := Real.cosh_sq' u; exact_mod_cast (by linarith : Real.cosh u ^ 2 = 1 + Real.sinh u ^ 2)
  rw [ofReal_div, div_pow, ofReal_inv, ofReal_pow]
  field_simp
  linear_combination h2

/-- Formula under the stated hypotheses: `1 - (1 - b) * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane`. -/
private lemma one_sub_one_sub_mul_sin_sq_mem_slitPlane {b : ℂ} (hb : b ∈ slitPlane) (θ : ℝ) :
    1 - (1 - b) * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane := by
  have := one_sub_mul_ofReal_mem_slitPlane (z := 1 - b) (by rw [sub_sub_cancel]; exact hb)
    (sq_nonneg (Real.sin θ)) (Real.sin_sq_le_one θ)
  convert this using 2; push_cast; ring

/-- Identity under the stated parameter and domain assumptions: `(1 - (1 - b) * (Real.sin
(Real.arctan (Real.sinh u)) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = (Real.cosh u : ℂ) * (1 + b *
((Real.sinh u : ℝ) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) ∧ (1 - (1 - b) * (Real.sin (Real.arctan
(Real.sinh u)) : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (Real.cosh u : ℂ)⁻¹ * (1 + b * ((Real.sinh u : ℝ) :
ℂ) ^ 2) ^ (1 / 2 : ℂ)`. -/
private lemma cpow_one_sub_mul_sin_arctan_sinh_sq (b : ℂ) (u : ℝ) :
    (1 - (1 - b) * (Real.sin (Real.arctan (Real.sinh u)) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      (Real.cosh u : ℂ) * (1 + b * ((Real.sinh u : ℝ) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) ∧
    (1 - (1 - b) * (Real.sin (Real.arctan (Real.sinh u)) : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
      (Real.cosh u : ℂ)⁻¹ * (1 + b * ((Real.sinh u : ℝ) : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
  have hc := Real.cosh_pos u
  rw [one_sub_mul_sin_arctan_sinh_sq, ofReal_mul_cpow_eq_of_pos (by positivity),
    ofReal_mul_cpow_eq_of_pos (by positivity), (ofReal_inv_sq_cpow_half hc).1,
        (ofReal_inv_sq_cpow_half hc).2]
  exact ⟨rfl, rfl⟩

/-- Identity under the stated parameter and domain assumptions: `incEllIntFk (I * φ) k = I *
incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k)`. -/
private lemma incEllIntFk_I_mul (φ : ℝ) {k : ℂ} (hk : k ^ 2 ∈ slitPlane) :
    incEllIntFk (I * φ) k = I * incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) := by
  rw [incEllIntFk, segmentIntegral_I_mul, incEllIntFk_ofReal_eq_integral,
    jacobiComodulusk_sq_eq_one_sub_sq]
  congr 1
  rw [← integral_arctan_sinh_subst]
  · refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [sin_I_mul_sq, (cpow_one_sub_mul_sin_arctan_sinh_sq _ u).1, real_smul]
    have hc : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
    rw [ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    ring_nf
  · exact (continuous_iff_continuousAt.2 fun θ =>
      (continuousAt_cpow_const (one_sub_one_sub_mul_sin_sq_mem_slitPlane hk θ)).comp
        (f := fun θ : ℝ => 1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) (by fun_prop)).continuousOn

/-- Nonvanishing under the stated hypotheses: `Real.cos θ ≠ 0`. -/
private lemma cos_ne_zero_of_mem_Ioo {θ : ℝ} (h : θ ∈ Ioo (-(π / 2)) (π / 2)) : Real.cos θ ≠ 0 :=
  (Real.cos_pos_of_mem_Ioo h).ne'

/-- The stated relation follows from the given hypotheses: `uIcc 0 ψ ⊆ Ioo (-(π / 2)) (π / 2)`. -/
private lemma uIcc_zero_subset_Ioo {ψ : ℝ} (h : ψ ∈ Ioo (-(π / 2)) (π / 2)) :
    uIcc 0 ψ ⊆ Ioo (-(π / 2)) (π / 2) := by
  intro x hx
  rcases le_total 0 ψ with h0 | h0
  · rw [uIcc_of_le h0] at hx; exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, h.2]⟩
  · rw [uIcc_of_ge h0] at hx; exact ⟨by linarith [hx.1, h.1], by linarith [hx.2, Real.pi_pos]⟩

/-- Identity under the stated parameter and domain assumptions: `incEllIntEk (I * φ) k = I *
(incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) - incEllIntEk (Real.arctan
(Real.sinh φ)) (jacobiComodulusk k) + Real.tan (Real.arctan (Real.sinh φ)) * (1 - (1 - k ^ 2)
* (Real.sin (Real.arctan (Real.sinh φ)) : ℂ) ^ 2) ^ (1 / 2 : ℂ))`. -/
private lemma incEllIntEk_I_mul (φ : ℝ) {k : ℂ} (hk : k ^ 2 ∈ slitPlane) :
    incEllIntEk (I * φ) k = I * (incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) -
        incEllIntEk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) +
          Real.tan (Real.arctan (Real.sinh φ)) *
            (1 - (1 - k ^ 2) * (Real.sin (Real.arctan (Real.sinh φ)) : ℂ) ^ 2) ^ (1 / 2 : ℂ)) := by
  set ψ := Real.arctan (Real.sinh φ) with hψ
  set k' := jacobiComodulusk k with hk'
  have hk'2 : k' ^ 2 = 1 - k ^ 2 := jacobiComodulusk_sq_eq_one_sub_sq k
  have hk's : 1 - k' ^ 2 ∈ slitPlane := by rw [hk'2, sub_sub_cancel]; exact hk
  have hψI : ψ ∈ Ioo (-(π / 2)) (π / 2) :=
    ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hsub := uIcc_zero_subset_Ioo hψI
  set G : ℝ → ℂ := fun θ => ellDelta k' θ / (Real.cos θ : ℂ) ^ 2 with hG
  have hΔc := continuous_ellDelta hk's
  have hGc : ContinuousOn G (Ioo (-(π / 2)) (π / 2)) := by
    refine hΔc.continuousOn.div (by fun_prop) fun θ hθ => ?_
    exact pow_ne_zero _ (by exact_mod_cast cos_ne_zero_of_mem_Ioo hθ)
  -- the substitution
  have h1 : incEllIntEk (I * φ) k = I * ∫ θ in (0 : ℝ)..ψ, G θ := by
    rw [incEllIntEk, segmentIntegral_I_mul, ← integral_arctan_sinh_subst hGc]
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hG, ellDelta, hk'2, (cpow_one_sub_mul_sin_arctan_sinh_sq _ u).2,
        sin_I_mul_sq, real_smul,
      (sin_cos_arctan_sinh u).2]
    have hc0 : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
    have e : (1 - k ^ 2 * -((Real.sinh u : ℝ) : ℂ) ^ 2) = 1 + k ^ 2 *
        ((Real.sinh u : ℝ) : ℂ) ^ 2 := by
      ring
    rw [e, ofReal_inv]
    field_simp
  -- the integration by parts identity
  set D : ℝ → ℂ := fun θ => G θ - (ellDelta k' θ)⁻¹ + ellDelta k' θ with hD
  have hDc : ContinuousOn D (uIcc 0 ψ) := by
    refine ((hGc.mono hsub).sub ?_).add hΔc.continuousOn
    exact (continuous_iff_continuousAt.2 fun θ =>
      (hΔc.continuousAt).inv₀ (ellDelta_ne_zero hk's θ)).continuousOn
  have hFTC : ∫ θ in (0 : ℝ)..ψ, D θ = Real.tan ψ * ellDelta k' ψ := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ : ℝ => (Real.tan θ : ℂ) * ellDelta k' θ) (f' := D) (a := 0) (b := ψ)
      (fun θ hθ => by
        have hcos := cos_ne_zero_of_mem_Ioo (hsub hθ)
        have h := ((Real.hasDerivAt_tan hcos).ofReal_comp).mul (hasDerivAt_ellDelta hk's θ)
        refine h.congr_deriv ?_
        have hΔ := ellDelta_ne_zero hk's θ
        have hΔ2 := ellDelta_sq k' θ
        have hc : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hcos
        simp only [hD, hG, Real.tan_eq_sin_div_cos, ofReal_div, ofReal_one, ofReal_pow]
        field_simp
        linear_combination (-(Real.cos θ : ℂ) ^ 2) * hΔ2)
      (hDc.intervalIntegrable)
    rw [this]; simp [Real.tan_zero]
  have hGint : IntervalIntegrable G volume 0 ψ := (hGc.mono hsub).intervalIntegrable
  have hΔint : IntervalIntegrable (ellDelta k') volume 0 ψ := hΔc.intervalIntegrable _ _
  have hΔiint : IntervalIntegrable (fun θ => (ellDelta k' θ)⁻¹) volume 0 ψ :=
    (continuous_iff_continuousAt.2 fun θ =>
      (hΔc.continuousAt).inv₀ (ellDelta_ne_zero hk's θ)).intervalIntegrable _ _
  have hsplit : ∫ θ in (0 : ℝ)..ψ, G θ = (∫ θ in (0 : ℝ)..ψ, D θ) +
      (∫ θ in (0 : ℝ)..ψ, (ellDelta k' θ)⁻¹) - ∫ θ in (0 : ℝ)..ψ, ellDelta k' θ := by
    rw [← intervalIntegral.integral_add ((hGint.sub hΔiint).add hΔint) hΔiint,
      ← intervalIntegral.integral_sub (((hGint.sub hΔiint).add hΔint).add hΔiint) hΔint]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring
  rw [h1, hsplit, hFTC, incEllIntFk_ofReal_eq_integral, incEllIntEk_ofReal_eq_integral]
  simp only [ellDelta, ← cpow_neg, hk'2]
  ring

/-- Formula under the stated hypotheses: `1 + b * x ∈ slitPlane`. -/
private lemma one_add_mul_ofReal_mem_slitPlane {b : ℂ} (hb : b ∈ slitPlane) {x : ℝ} (hx : 0 ≤ x) :
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
private lemma exists_norm_lower_on_segment {g : ℂ → ℂ} (hg : Continuous g) (w : ℂ)
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, g (t * w) ≠ 0) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖g (t * w)‖ := by
  obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    (nonempty_Icc.2 zero_le_one) (by fun_prop : Continuous fun t : ℝ => ‖g (t * w)‖).continuousOn
  exact ⟨‖g (t0 * w)‖, norm_pos_iff.2 (hne t0 ht0), fun t ht => hmin ht⟩

/-- Identity under the stated parameter and domain assumptions: `incEllIntPik ψ β k = ∫ θ in (0 :
ℝ)..ψ, ((1 - β * (Real.sin θ : ℂ) ^ 2)⁻¹ * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 :
ℂ)))`. -/
private lemma incEllIntPik_ofReal_eq_integral_of_slit (ψ : ℝ) {β : ℂ}
    (hβ : 1 - β ∈ slitPlane) (k : ℂ) :
    incEllIntPik ψ β k = ∫ θ in (0 : ℝ)..ψ, ((1 - β * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
  obtain ⟨δ, hδ, hb⟩ := exists_le_norm_one_sub_mul_sin_sq hβ
  rw [incEllIntPik_eq_segmentIntegral (δ := δ) hδ, segmentIntegral_ofReal]
  · simp only [← Complex.ofReal_sin]
  · intro t _
    have := hb (t * ψ)
    push_cast at this; exact this

/-- Identity under the stated parameter and domain assumptions: `incEllIntPik (I * φ) α2 k = I *
(incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) - α2 * incEllIntPik (Real.arctan
(Real.sinh φ)) (1 - α2) (jacobiComodulusk k)) / (1 - α2)`. -/
private lemma incEllIntPik_I_mul (φ : ℝ) {k α2 : ℂ} (hk : k ^ 2 ∈ slitPlane) (hα : α2 ∈ slitPlane)
    (hα1 : α2 ≠ 1) :
    incEllIntPik (I * φ) α2 k = I * (incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) -
        α2 * incEllIntPik (Real.arctan (Real.sinh φ)) (1 - α2) (jacobiComodulusk k))
            / (1 - α2) := by
  set ψ := Real.arctan (Real.sinh φ) with hψ
  set k' := jacobiComodulusk k with hk'
  have hk'2 : k' ^ 2 = 1 - k ^ 2 := jacobiComodulusk_sq_eq_one_sub_sq k
  have hα1' : (1 : ℂ) - α2 ≠ 0 := sub_ne_zero.2 (Ne.symm hα1)
  have hpath : ∀ u : ℝ, 1 - α2 * Complex.sin (I * u) ^ 2 =
      1 + α2 * (((Real.sinh u) ^ 2 : ℝ) : ℂ) := by
    intro u; rw [sin_I_mul_sq]; push_cast; ring
  -- remove the principal value on the left
  obtain ⟨δ, hδ, hb⟩ := exists_norm_lower_on_segment (g := fun z => 1 - α2 * Complex.sin z ^ 2)
    (by fun_prop) (I * φ) (fun t _ => by
      have : ((t : ℂ) * (I * φ)) = I * ((t * φ : ℝ) : ℂ) := by push_cast; ring
      simp only [this, hpath]
      exact slitPlane_ne_zero (one_add_mul_ofReal_mem_slitPlane hα (sq_nonneg _)))
  rw [incEllIntPik_eq_segmentIntegral hδ hb, segmentIntegral_I_mul,
    incEllIntPik_ofReal_eq_integral_of_slit ψ (by rw [sub_sub_cancel]; exact hα),
    incEllIntFk_ofReal_eq_integral]
  set P : ℝ → ℂ := fun θ => 1 - (1 - α2) * (Real.sin θ : ℂ) ^ 2 with hP
  have hPne : ∀ θ, P θ ≠ 0 := fun θ =>
      slitPlane_ne_zero (one_sub_one_sub_mul_sin_sq_mem_slitPlane hα θ)
  set H : ℝ → ℂ := fun θ => (Real.cos θ : ℂ) ^ 2 * (P θ)⁻¹ *
    (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) with hH
  have hQc : Continuous fun θ : ℝ => (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) :=
    continuous_iff_continuousAt.2 fun θ =>
      (continuousAt_cpow_const (one_sub_one_sub_mul_sin_sq_mem_slitPlane hk θ)).comp
        (f := fun θ : ℝ => 1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) (by fun_prop)
  have hPic : Continuous fun θ => (P θ)⁻¹ :=
    continuous_iff_continuousAt.2 fun θ => ((by fun_prop : Continuous P).continuousAt).inv₀ (hPne θ)
  have hHc : Continuous H := by
    rw [hH]; exact ((by fun_prop : Continuous fun θ : ℝ => (Real.cos θ : ℂ) ^ 2).mul hPic).mul hQc
  have h1 : (∫ u in (0 : ℝ)..φ, (1 - α2 * Complex.sin (I * u) ^ 2)⁻¹ *
      (1 - k ^ 2 * Complex.sin (I * u) ^ 2) ^ (-(1 / 2 : ℂ))) = ∫ θ in (0 : ℝ)..ψ, H θ := by
    rw [← integral_arctan_sinh_subst hHc.continuousOn]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have hPu : P (Real.arctan (Real.sinh u)) =
        ((((Real.cosh u) ^ 2)⁻¹ : ℝ) : ℂ) * (1 + α2 * ((Real.sinh u : ℝ) : ℂ) ^ 2) :=
      one_sub_mul_sin_arctan_sinh_sq α2 u
    simp only [hH, hPu, (cpow_one_sub_mul_sin_arctan_sinh_sq _ u).1, (sin_cos_arctan_sinh u).2,
      real_smul, sin_I_mul_sq]
    have hc0 : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
    have hA : (1 + α2 * ((Real.sinh u : ℝ) : ℂ) ^ 2) ≠ 0 :=
      slitPlane_ne_zero (by
        have := one_add_mul_ofReal_mem_slitPlane hα (sq_nonneg (Real.sinh u));
            push_cast at this ⊢; exact this)
    have e : (1 - k ^ 2 * -((Real.sinh u : ℝ) : ℂ) ^ 2) = 1 + k ^ 2 *
        ((Real.sinh u : ℝ) : ℂ) ^ 2 := by
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
  ⟨incEllIntFk_I_mul φ hk, incEllIntEk_I_mul φ hk, incEllIntPik_I_mul φ hk hα hα1⟩

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
