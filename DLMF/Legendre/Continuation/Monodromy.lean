/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Continuation.LogarithmicBranches

/-!
# Monodromy of associated Legendre solutions

Explicit transport of the first- and second-kind associated Legendre functions around the
singular points.

Source references and common attribution are retained in
`DLMF.Legendre.Continuation`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat ComplexConjugate

namespace DLMF.Legendre

/-! ### Helpers for DLMF 14.24.2: the explicit transport of `𝑸^μ_ν` along the ellipse -/

/-- The Joukowski map `J(w) = (w + w⁻¹)/2` sends `{|w| < 1} ∖ (-∞, 0]` into `ℂ ∖ (-∞, 1]`. -/
theorem legInt_joukowski_mem {w : ℂ} (hw1 : ‖w‖ < 1) (hw : w ∈ slitPlane) :
    (w + w⁻¹)/2 - 1 ∈ slitPlane := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hn : 0 < normSq w := normSq_pos.mpr hw0
  have hn1 : normSq w < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  rw [mem_slitPlane_iff]
  by_cases hb : w.im = 0
  · left
    have ha : 0 < w.re := by
      rcases mem_slitPlane_iff.mp hw with h | h
      · exact h
      · exact absurd hb h
    have hnq : normSq w = w.re^2 := by rw [normSq_apply, hb]; ring
    simp only [sub_re, div_re, add_re, inv_re, one_re, hnq]
    norm_num
    have : w.re < 1 := by nlinarith
    have e : (w.re + w.re / w.re ^ 2) * 2 / 4 - 1 = (w.re - 1)^2/(2*w.re) := by field_simp; ring
    have := div_pos (pow_pos (show (0:ℝ) < 1 - w.re by linarith) 2) (by linarith : (0:ℝ) < 2*w.re)
    rw [show (1 - w.re)^2 = (w.re - 1)^2 by ring] at this
    linarith
  · right
    simp only [sub_im, div_im, add_im, inv_im, one_im]
    norm_num
    intro h
    have : w.im * (1 - 1/normSq w) = 0 := by
      field_simp; field_simp at h; linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hb h1
    · have : 1/normSq w = 1 := by linarith
      rw [div_eq_one_iff_eq hn.ne'] at this; linarith

/-- `ζ(J(w)) = w` for `|w| < 1`, `w ∉ (-∞, 0]`. -/
theorem legInt_zeta_joukowski {w : ℂ} (hw1 : ‖w‖ < 1) (hw : w ∈ slitPlane) :
    legInt_zeta ((w + w⁻¹)/2) = w := by
  have hm := legInt_joukowski_mem hw1 hw
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have h := legInt_zeta_mul hm
  set y := legInt_zeta ((w + w⁻¹)/2)
  have hy : (y - w) * (y - w⁻¹) = 0 := by
    have : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
    linear_combination -h + this
  rcases mul_eq_zero.mp hy with h1 | h1
  · linear_combination h1
  · exfalso
    have hy1 : ‖y‖ < 1 := legInt_norm_zeta_lt_one hm
    rw [show y = w⁻¹ by linear_combination h1, norm_inv] at hy1
    have := (one_lt_inv₀ (norm_pos_iff.mpr hw0)).mpr hw1
    linarith

/-- The moving point `w(t) = ζ e^{-sπit}` of DLMF 14.24.2. -/
noncomputable def legInt_ew (ζ : ℂ) (s : ℤ) (t : ℝ) : ℂ := ζ * exp (-(s:ℂ)*π*I*t)

/-- The ellipse path is `J(w(t))`. -/
theorem legInt_path_eq {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) (t : ℝ) :
    legendreEllipsePath z s t = (legInt_ew (legInt_zeta z) s t + (legInt_ew (legInt_zeta z) s t)⁻¹)/2 := by
  have h0 := legInt_zeta_ne_zero hz
  have hq : z + exp ((log (z-1) + log (z+1))/2) = (legInt_zeta z)⁻¹ := by
    have := legInt_zeta_mul hz
    have h2 : z + exp ((log (z-1) + log (z+1))/2) = 2*z - legInt_zeta z := by
      simp only [legInt_zeta, legInt_root]; ring
    rw [h2]; exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact this)
  simp only [legendreEllipsePath, legInt_ew]
  rw [hq, mul_inv, inv_inv, ← exp_neg, show -(-(s:ℂ)*π*I*t) = (s:ℂ)*π*I*t by ring,
    show -(s:ℂ)*π*I*t = -(s:ℂ)*π*I*t from rfl]
  ring

/-- `|w(t)| = |ζ|`. -/
theorem legInt_norm_ew (ζ : ℂ) (s : ℤ) (t : ℝ) : ‖legInt_ew ζ s t‖ = ‖ζ‖ := by
  rw [legInt_ew, norm_mul, norm_exp]
  simp

/-- The derivative of `w(t)`. -/
theorem legInt_hasDerivAt_ew (ζ : ℂ) (s : ℤ) (t : ℝ) :
    HasDerivAt (legInt_ew ζ s) (-(s:ℂ)*π*I * legInt_ew ζ s t) t := by
  have h := ((hasDerivAt_id (t:ℂ)).const_mul (-(s:ℂ)*π*I)).cexp.const_mul ζ
  have h2 := h.comp_ofReal
  simp only [legInt_ew]
  convert h2 using 1
  · ext t; simp only [legInt_ew, id]
  · simp only [id]; ring_nf

/-- The explicit transport of `𝑸^μ_ν` along the ellipse path:
`u(t) = √π (1-w²)^μ ζ^{ν+1} e^{-(ν+1)sπit} 𝐅(μ+1/2, ν+μ+1; ν+3/2; w²)`, `w = ζ e^{-sπit}`. -/
noncomputable def legInt_eu (ν μ ζ : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  Real.sqrt π * (1 - legInt_ew ζ s t ^ 2)^μ * (ζ^(ν+1) * exp (-(ν+1)*((s:ℂ)*π*I*t))) *
    regularizedGaussHG (μ+1/2) (ν+μ+1) (ν+3/2) (legInt_ew ζ s t ^ 2)

/-- Locally along the path, the transport is a constant multiple of `𝑸^μ_ν(σ z)`, `σ = ±1`. -/
theorem legInt_eu_local (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) {σ : ℂ}
    (hσ : σ = 1 ∨ σ = -1) {t₀ : ℝ} (ht₀ : σ * legInt_ew (legInt_zeta z) s t₀ ∈ slitPlane) :
    ∀ᶠ t in 𝓝 t₀, (σ * legInt_ew (legInt_zeta z) s t ∈ slitPlane) ∧
      legInt_eu ν μ (legInt_zeta z) s t =
      exp ((ν+1)*(log (legInt_zeta z) - (log (σ * legInt_ew (legInt_zeta z) s t₀) + (s:ℂ)*π*I*t₀))) *
        olverQ ν μ (σ * ((legInt_ew (legInt_zeta z) s t + (legInt_ew (legInt_zeta z) s t)⁻¹)/2)) := by
  set ζ := legInt_zeta z with hζ
  have hζ0 : ζ ≠ 0 := legInt_zeta_ne_zero hz
  have hζ1 : ‖ζ‖ < 1 := legInt_norm_zeta_lt_one hz
  set w := legInt_ew ζ s with hw
  have hσ2 : σ^2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ2
  have hwc : Continuous w := by
    rw [hw]; unfold legInt_ew; fun_prop
  have hU : ∀ᶠ t in 𝓝 t₀, σ * w t ∈ slitPlane :=
    ((continuous_const.mul hwc).continuousAt (x := t₀)).preimage_mem_nhds (isOpen_slitPlane.mem_nhds ht₀)
  obtain ⟨l, r, hlr, hsub⟩ := hU.exists_Ioo_subset
  set h : ℝ → ℂ := fun t => log (σ * w t) + (s:ℂ)*π*I*t with hh
  have hdh : ∀ t ∈ Ioo l r, HasDerivAt h 0 t := by
    intro t ht
    have hm : σ * w t ∈ slitPlane := hsub ht
    have h1 := ((legInt_hasDerivAt_ew ζ s t).const_mul σ).clog_real hm
    have h2 : HasDerivAt (fun t : ℝ => (s:ℂ)*π*I*t) ((s:ℂ)*π*I) t := by
      have := ((hasDerivAt_id (t:ℂ)).const_mul ((s:ℂ)*π*I)).comp_ofReal
      simpa using this
    convert h1.add h2 using 1
    have hw0 : w t ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hm; exact slitPlane_ne_zero hm rfl
    have hinv : legInt_ew ζ s t * (legInt_ew ζ s t)⁻¹ = 1 := mul_inv_cancel₀ hw0
    field_simp
    linear_combination ((s:ℂ)*π*I) * hinv
  have hconst : ∀ t ∈ Ioo l r, h t = h t₀ := fun t ht =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun x hx => (hdh x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hdh x hx).deriv) ht hlr
  filter_upwards [isOpen_Ioo.mem_nhds hlr] with t ht
  have hm : σ * w t ∈ slitPlane := hsub ht
  refine ⟨hm, ?_⟩
  have hn : ‖σ * w t‖ < 1 := by
    rw [norm_mul, show ‖σ‖ = 1 by rcases hσ with h | h <;> rw [h] <;> simp, one_mul, hw,
      legInt_norm_ew]; exact hζ1
  have hJ := legInt_joukowski_mem hn hm
  have hσJ : σ * ((w t + (w t)⁻¹)/2) = (σ * w t + (σ * w t)⁻¹)/2 := by
    rcases hσ with h | h
    · rw [h]; simp
    · rw [h]; simp; ring
  rw [hσJ, legFS_olverQ_eq_G ν μ hJ, legInt_zeta_joukowski hn hm, legFS_G, legInt_eu]
  have hw0 : σ * w t ≠ 0 := slitPlane_ne_zero hm
  have hsq : (σ * w t)^2 = w t ^ 2 := by rw [mul_pow, hσ2, one_mul]
  have hht := hconst t ht
  simp only [hh] at hht
  have hp : (σ * w t)^(ν+1) = exp ((ν+1)*(log (σ * w t₀) + (s:ℂ)*π*I*t₀ - (s:ℂ)*π*I*t)) := by
    rw [cpow_def_of_ne_zero hw0, ← hht]; congr 1; ring
  have hz' : ζ^(ν+1) = exp ((ν+1) * log ζ) := by rw [cpow_def_of_ne_zero hζ0]; ring_nf
  rw [hsq, hp, hz']
  have e : exp ((ν+1) * log ζ) * exp (-(ν+1)*((s:ℂ)*π*I*t)) =
      exp ((ν+1)*(log ζ - (log (σ * w t₀) + (s:ℂ)*π*I*t₀))) *
        exp ((ν+1)*(log (σ * w t₀) + (s:ℂ)*π*I*t₀ - (s:ℂ)*π*I*t)) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  rw [e]; ring

/-- The derivative of the ellipse path, `γ'(t) = -sπi (w - w⁻¹)/2`. -/
noncomputable def legInt_gd (ζ : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  -(s:ℂ)*π*I * (legInt_ew ζ s t - (legInt_ew ζ s t)⁻¹)/2

/-- `w(t) ≠ 0`. -/
theorem legInt_ew_ne_zero {ζ : ℂ} (hζ : ζ ≠ 0) (s : ℤ) (t : ℝ) : legInt_ew ζ s t ≠ 0 :=
  mul_ne_zero hζ (exp_ne_zero _)

/-- The ellipse path has derivative `legInt_gd`. -/
theorem legInt_hasDerivAt_path {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) (t : ℝ) :
    HasDerivAt (legendreEllipsePath z s) (legInt_gd (legInt_zeta z) s t) t := by
  have h0 := legInt_ew_ne_zero (legInt_zeta_ne_zero hz) s t
  have hw := legInt_hasDerivAt_ew (legInt_zeta z) s t
  have h := (hw.add (hw.inv h0)).div_const 2
  have he : legendreEllipsePath z s = fun t =>
      (legInt_ew (legInt_zeta z) s t + (legInt_ew (legInt_zeta z) s t)⁻¹)/2 :=
    funext fun t => legInt_path_eq hz s t
  rw [he]
  convert h using 1
  simp only [legInt_gd]
  field_simp
  ring

/-- `γ'(t) ≠ 0` for `s ≠ 0`. -/
theorem legInt_gd_ne_zero {z : ℂ} (hz : z-1 ∈ slitPlane) {s : ℤ} (hs : s ≠ 0) (t : ℝ) :
    legInt_gd (legInt_zeta z) s t ≠ 0 := by
  have h0 := legInt_ew_ne_zero (legInt_zeta_ne_zero hz) s t
  have hn : ‖legInt_ew (legInt_zeta z) s t‖ < 1 := by
    rw [legInt_norm_ew]; exact legInt_norm_zeta_lt_one hz
  simp only [legInt_gd]
  refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hs))
    (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero) ?_) two_ne_zero
  intro h
  have h1 : legInt_ew (legInt_zeta z) s t ^ 2 = 1 := by
    field_simp at h; linear_combination h
  have := congrArg norm h1
  rw [norm_pow, norm_one] at this
  nlinarith [norm_nonneg (legInt_ew (legInt_zeta z) s t)]

/-- A nonzero point outside `ℂ ∖ (-∞, 0]` has its negative inside. -/
theorem legInt_neg_mem_slitPlane {w : ℂ} (hw0 : w ≠ 0) (hw : w ∉ slitPlane) : -w ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  push Not at hw
  left
  have : w.re ≠ 0 := fun h => hw0 (Complex.ext (by simp [h]) (by simp [hw.2]))
  simp only [neg_re]
  exact neg_pos.mpr (lt_of_le_of_ne hw.1 this)

/-- Local data at each point of the path: `u = c 𝑸(σ γ)` near `t₀`. -/
theorem legInt_eu_local' (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) (t₀ : ℝ) :
    ∃ c σ : ℂ, σ^2 = 1 ∧ ∀ᶠ t in 𝓝 t₀, σ * legendreEllipsePath z s t - 1 ∈ slitPlane ∧
      legInt_eu ν μ (legInt_zeta z) s t = c * olverQ ν μ (σ * legendreEllipsePath z s t) := by
  have h0 := legInt_ew_ne_zero (legInt_zeta_ne_zero hz) s t₀
  have key : ∀ σ : ℂ, (σ = 1 ∨ σ = -1) → σ * legInt_ew (legInt_zeta z) s t₀ ∈ slitPlane →
      ∃ c σ : ℂ, σ^2 = 1 ∧ ∀ᶠ t in 𝓝 t₀, σ * legendreEllipsePath z s t - 1 ∈ slitPlane ∧
      legInt_eu ν μ (legInt_zeta z) s t = c * olverQ ν μ (σ * legendreEllipsePath z s t) := by
    intro σ hσ hm
    refine ⟨exp ((ν+1)*(log (legInt_zeta z) - (log (σ * legInt_ew (legInt_zeta z) s t₀) +
      (s:ℂ)*π*I*t₀))), σ, by rcases hσ with h | h <;> rw [h] <;> norm_num, ?_⟩
    filter_upwards [legInt_eu_local ν μ hz s hσ hm] with t ⟨hmt, he⟩
    have hn : ‖σ * legInt_ew (legInt_zeta z) s t‖ < 1 := by
      rw [norm_mul, show ‖σ‖ = 1 by rcases hσ with h | h <;> rw [h] <;> simp, one_mul,
        legInt_norm_ew]; exact legInt_norm_zeta_lt_one hz
    have hσJ : σ * ((legInt_ew (legInt_zeta z) s t + (legInt_ew (legInt_zeta z) s t)⁻¹)/2) =
        (σ * legInt_ew (legInt_zeta z) s t + (σ * legInt_ew (legInt_zeta z) s t)⁻¹)/2 := by
      rcases hσ with h | h
      · rw [h]; simp
      · rw [h]; simp; ring
    rw [legInt_path_eq hz s t]
    refine ⟨?_, he⟩
    rw [hσJ]; exact legInt_joukowski_mem hn hmt
  by_cases hm : legInt_ew (legInt_zeta z) s t₀ ∈ slitPlane
  · exact key 1 (Or.inl rfl) (by rwa [one_mul])
  · exact key (-1) (Or.inr rfl) (by rw [neg_one_mul]; exact legInt_neg_mem_slitPlane h0 hm)

/-- The transport `u` satisfies the first-order Legendre system along the ellipse path, with
`v = u'/γ'`. -/
theorem legInt_eu_deriv (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) {s : ℤ} (hs : s ≠ 0) (t₀ : ℝ) :
    HasDerivAt (legInt_eu ν μ (legInt_zeta z) s)
      (deriv (legendreEllipsePath z s) t₀ * (deriv (legInt_eu ν μ (legInt_zeta z) s) t₀ /
        legInt_gd (legInt_zeta z) s t₀)) t₀ ∧
    HasDerivAt (fun t => deriv (legInt_eu ν μ (legInt_zeta z) s) t / legInt_gd (legInt_zeta z) s t)
      (deriv (legendreEllipsePath z s) t₀ * (2 * legendreEllipsePath z s t₀ *
        (deriv (legInt_eu ν μ (legInt_zeta z) s) t₀ / legInt_gd (legInt_zeta z) s t₀) -
        (ν*(ν+1) - μ^2/(1 - (legendreEllipsePath z s t₀)^2)) * legInt_eu ν μ (legInt_zeta z) s t₀) /
        (1 - (legendreEllipsePath z s t₀)^2)) t₀ := by
  obtain ⟨c, σ, hσ2, hev⟩ := legInt_eu_local' ν μ hz s t₀
  set γ := legendreEllipsePath z s with hγdef
  set u := legInt_eu ν μ (legInt_zeta z) s with hudef
  set gd := legInt_gd (legInt_zeta z) s with hgd
  set Q := olverQ ν μ with hQdef
  have hγ : ∀ t, HasDerivAt γ (gd t) t := legInt_hasDerivAt_path hz s
  have hdγ : ∀ t, deriv γ t = gd t := fun t => (hγ t).deriv
  have hgd0 : ∀ t, gd t ≠ 0 := legInt_gd_ne_zero hz hs
  have hf : ∀ t, σ * γ t - 1 ∈ slitPlane →
      HasDerivAt (fun t => c * Q (σ * γ t)) (c * (deriv Q (σ * γ t) * (σ * gd t))) t := by
    intro t ht
    have hQ : HasDerivAt Q (deriv Q (σ * γ t)) (σ * γ t) :=
      (olverQ_analytic ν μ _ ht).differentiableAt.hasDerivAt
    exact (hQ.comp t ((hγ t).const_mul σ)).const_mul c
  have hloc : ∀ᶠ t in 𝓝 t₀, σ * γ t - 1 ∈ slitPlane ∧ HasDerivAt u (c * (deriv Q (σ * γ t) * (σ * gd t))) t := by
    filter_upwards [hev.eventually_nhds] with t ht
    have hm := ht.self_of_nhds.1
    refine ⟨hm, (hf t hm).congr_of_eventuallyEq ?_⟩
    filter_upwards [ht] with y hy using hy.2
  have hV : ∀ᶠ t in 𝓝 t₀, deriv u t / gd t = c * σ * deriv Q (σ * γ t) := by
    filter_upwards [hloc] with t ⟨_, ht⟩
    rw [ht.deriv]; field_simp [hgd0 t]
  obtain ⟨hm0, hu0⟩ := hloc.self_of_nhds
  have hV0 := hV.self_of_nhds
  rw [hdγ, hV0]
  have hQ2 : HasDerivAt (deriv Q) (iteratedDeriv 2 Q (σ * γ t₀)) (σ * γ t₀) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (olverQ_analytic ν μ _ hm0).deriv.differentiableAt.hasDerivAt
  have hg := ((hQ2.comp t₀ ((hγ t₀).const_mul σ)).const_mul (c*σ))
  have hode := olverQ_ode ν μ hm0
  have hγ2 : (σ * γ t₀)^2 = γ t₀ ^ 2 := by rw [mul_pow, hσ2, one_mul]
  rw [hγ2] at hode
  have hev0 := hev.self_of_nhds
  refine ⟨?_, ?_⟩
  · convert hu0 using 1; ring
  · refine (hg.congr_of_eventuallyEq hV).congr_deriv ?_
    rw [hev0.2]
    have h1 : 1 - γ t₀ ^ 2 ≠ 0 := by
      rw [← hγ2]
      have ha : σ * γ t₀ - 1 ≠ 0 := slitPlane_ne_zero hm0
      have hb : σ * γ t₀ + 1 ≠ 0 := by
        intro h; rw [show σ * γ t₀ - 1 = -2 by linear_combination h] at hm0
        rw [mem_slitPlane_iff] at hm0; norm_num at hm0
      have : 1 - (σ * γ t₀)^2 = -((σ * γ t₀ - 1) * (σ * γ t₀ + 1)) := by ring
      rw [this]; exact neg_ne_zero.mpr (mul_ne_zero ha hb)
    rw [← hQdef] at hode
    generalize Q (σ * γ t₀) = A at hode ⊢
    generalize deriv Q (σ * γ t₀) = B at hode ⊢
    generalize iteratedDeriv 2 Q (σ * γ t₀) = C at hode ⊢
    have hode' : (1 - γ t₀ ^ 2)^2 * C - 2 * (σ * γ t₀) * B * (1 - γ t₀ ^ 2) +
        (ν * (ν + 1) * (1 - γ t₀ ^ 2) - μ ^ 2) * A = 0 := by
      field_simp at hode; linear_combination hode
    field_simp
    linear_combination (c * gd t₀ * (1 - γ t₀ ^ 2)^2 * C) * hσ2 +
      (c * gd t₀) * hode'

/-- The ellipse path avoids `±1`. -/
theorem legInt_path_ne {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) (t : ℝ) :
    legendreEllipsePath z s t ≠ 1 ∧ legendreEllipsePath z s t ≠ -1 := by
  have h0 := legInt_ew_ne_zero (legInt_zeta_ne_zero hz) s t
  have hn : ‖legInt_ew (legInt_zeta z) s t‖ < 1 := by
    rw [legInt_norm_ew]; exact legInt_norm_zeta_lt_one hz
  rw [legInt_path_eq hz s t]
  set w := legInt_ew (legInt_zeta z) s t
  have key : ∀ σ : ℂ, σ^2 = 1 → (w + w⁻¹)/2 ≠ σ := by
    intro σ hσ h
    have h1 : (w - σ)^2 = 0 := by
      field_simp at h; linear_combination h + hσ
    have h2 : w = σ := by linear_combination pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h1
    have h3 : ‖σ‖ = 1 := by
      have := congrArg norm hσ; rw [norm_pow, norm_one] at this
      nlinarith [norm_nonneg σ]
    rw [h2, h3] at hn; exact lt_irrefl _ hn
  exact ⟨key 1 (by norm_num), key (-1) (by norm_num)⟩

/-- The initial data of the transport: `u(0) = 𝑸^μ_ν(z)`, `u'(0) = γ'(0) 𝑸'(z)`. -/
theorem legInt_eu_zero (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    legInt_eu ν μ (legInt_zeta z) s 0 = olverQ ν μ z ∧
    HasDerivAt (legInt_eu ν μ (legInt_zeta z) s)
      (deriv (olverQ ν μ) z * legInt_gd (legInt_zeta z) s 0) 0 := by
  have hw0 : legInt_ew (legInt_zeta z) s 0 = legInt_zeta z := by simp [legInt_ew]
  have hm : (1:ℂ) * legInt_ew (legInt_zeta z) s 0 ∈ slitPlane := by
    rw [one_mul, hw0]; exact legInt_zeta_mem_slitPlane hz
  have hev := legInt_eu_local ν μ hz s (Or.inl rfl) hm
  rw [one_mul, hw0] at hev
  simp only [ofReal_zero, mul_zero, add_zero, sub_self, exp_zero, one_mul] at hev
  have hγ0 : legendreEllipsePath z s 0 = z := by
    rw [legInt_path_eq hz s 0, hw0, legInt_two_mul_eq hz |>.symm]; ring
  have hev' : legInt_eu ν μ (legInt_zeta z) s =ᶠ[𝓝 0] fun t => olverQ ν μ (legendreEllipsePath z s t) := by
    filter_upwards [hev] with t ht
    rw [ht.2, legInt_path_eq hz s t]
  refine ⟨by rw [hev'.self_of_nhds]; show olverQ ν μ (legendreEllipsePath z s 0) = _; rw [hγ0], ?_⟩
  have hQ : HasDerivAt (olverQ ν μ) (deriv (olverQ ν μ) z) (legendreEllipsePath z s 0) := by
    rw [hγ0]; exact (olverQ_analytic ν μ z hz).differentiableAt.hasDerivAt
  exact (hQ.comp 0 (legInt_hasDerivAt_path hz s 0)).congr_of_eventuallyEq hev'

-- DLMF 14.24.1 `associatedP_ellipse_continuation` is stated below, after 14.24.2 and 14.24.3, which its proof uses.

/-- olverQ ellipse continuation. Along the ellipse `γ(t) = J(w(t))`, `w(t) = ζ e^{-sπit}`, the
transport is `√π (1-w²)^μ ζ^{ν+1} e^{-(ν+1)sπit} 𝐅(μ+1/2, ν+μ+1; ν+3/2; w²)` (`legInt_eu`),
locally a multiple of `𝑸^μ_ν(±γ)` by the `ζ`-form `legFS_olverQ_eq_G`. -/
@[dlmf 14.24.E2]
theorem olverQ_ellipse_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    legendreEllipseContinued (olverQ ν μ) ν μ z s=(-1:ℂ)^s*exp (-s*ν*π*I)*olverQ ν μ z := by
  have hreg : ∀ t ∈ Icc (0:ℝ) 1, legendreEllipsePath z s t ≠ 1 ∧ legendreEllipsePath z s t ≠ -1 :=
    fun t _ => legInt_path_ne hz s t
  have hγc : ContDiff ℝ 1 (legendreEllipsePath z s) := by
    have he : legendreEllipsePath z s = fun t : ℝ =>
        ((z + exp ((log (z-1) + log (z+1))/2)) * exp ((s:ℂ)*π*I * ofRealCLM t) +
          (z + exp ((log (z-1) + log (z+1))/2))⁻¹ * exp ((-(s:ℂ))*π*I * ofRealCLM t))/2 := by
      funext t; simp only [legendreEllipsePath, ofRealCLM_apply]
    rw [he]
    have h1 : ContDiff ℝ 1 (fun t : ℝ => ofRealCLM t) := ofRealCLM.contDiff
    fun_prop
  obtain ⟨hu0, hd0⟩ := legInt_eu_zero ν μ hz s
  by_cases hs : s = 0
  · subst hs
    have hγ : legendreEllipsePath z 0 = fun _ => z := funext fun t => by
      have hw : legInt_ew (legInt_zeta z) 0 t = legInt_zeta z := by simp [legInt_ew]
      rw [legInt_path_eq hz 0 t, hw, ← legInt_two_mul_eq hz]; ring
    have hd : ∀ t, deriv (legendreEllipsePath z 0) t = 0 := fun t => by rw [hγ]; simp
    have huv : IsLegendreTransport ν μ (legendreEllipsePath z 0) (olverQ ν μ z) (deriv (olverQ ν μ) z)
        (fun _ => olverQ ν μ z) (fun _ => deriv (olverQ ν μ) z) := by
      refine ⟨rfl, rfl, continuousOn_const, continuousOn_const, fun t _ => ⟨?_, ?_⟩⟩
      · rw [hd, zero_mul]; exact hasDerivWithinAt_const _ _ _
      · rw [hd, zero_mul, zero_div]; exact hasDerivWithinAt_const _ _ _
    rw [legendreEllipseContinued, legendreTransport_unique _ _ _ _ _ hγc hreg huv]
    simp
  · set u := legInt_eu ν μ (legInt_zeta z) s with hudef
    set gd := legInt_gd (legInt_zeta z) s with hgd
    have hD := legInt_eu_deriv ν μ hz hs
    have huv : IsLegendreTransport ν μ (legendreEllipsePath z s) (olverQ ν μ z) (deriv (olverQ ν μ) z)
        u (fun t => deriv u t / gd t) := by
      refine ⟨hu0, ?_, fun t _ => (hD t).1.continuousAt.continuousWithinAt,
        fun t _ => (hD t).2.continuousAt.continuousWithinAt,
        fun t _ => ⟨(hD t).1.hasDerivWithinAt, (hD t).2.hasDerivWithinAt⟩⟩
      show deriv u 0 / gd 0 = _
      rw [hd0.deriv, mul_div_assoc, div_self (legInt_gd_ne_zero hz hs 0), mul_one]
    rw [legendreEllipseContinued, legendreTransport_unique _ _ _ _ _ hγc hreg huv, hudef, legInt_eu,
      legFS_olverQ_eq_G ν μ hz, legFS_G]
    have hw1 : legInt_ew (legInt_zeta z) s 1 ^ 2 = legInt_zeta z ^ 2 := by
      rw [legInt_ew, mul_pow, ← exp_nat_mul]
      have : exp (((2:ℕ):ℂ) * (-(s:ℂ)*π*I*((1:ℝ):ℂ))) = 1 := by
        rw [show ((2:ℕ):ℂ) * (-(s:ℂ)*π*I*((1:ℝ):ℂ)) = ((-s:ℤ):ℂ) * (2*π*I) by push_cast; ring]
        exact exp_int_mul_two_pi_mul_I _
      rw [this, mul_one]
    have hexp : exp (-(ν+1)*((s:ℂ)*π*I*((1:ℝ):ℂ))) = (-1:ℂ)^s * exp (-s*ν*π*I) := by
      rw [show -(ν+1)*((s:ℂ)*π*I*((1:ℝ):ℂ)) = (s:ℂ) * (-(π*I)) + -s*ν*π*I by push_cast; ring,
        exp_add, exp_int_mul, exp_neg, exp_pi_mul_I]
      norm_num
    rw [hw1, hexp]; ring

/-- Smooth joining parameter with zero derivatives at both endpoints. -/
def legendreSmoothStep (t : ℝ) : ℝ :=
  3*t^2-2*t^3

/-- A joined path from z to 3/2, s circuits about one of radius 1/2, and back; minus one is not enclosed. -/
def legendreOneLoop (z : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  if t ≤ 1/3 then z+legendreSmoothStep (3*t)*(3/2-z) else if t ≤ 2/3 then 1+1/2*exp (2*π*I*s*legendreSmoothStep (3*t-1)) else 3/2+legendreSmoothStep (3*t-2)*(z-3/2)

/-- The value obtained by continuing the solution `F` of the associated Legendre equation (with its
derivative at `z`) along a loop from `z` that makes `s` circuits around the branch point `1` but not
around `-1` (used for DLMF 14.24.3–4). -/
def legendreOneContinued (F : ℂ → ℂ) (ν μ z : ℂ) (s : ℤ) : ℂ :=
  legendreTransport ν μ (legendreOneLoop z s) (F z) (deriv F z)

/-! ### Helpers for DLMF 14.24.3: transport of `P^{-μ}_ν` around `1` (prefix `legTr_`) -/

/-- A pair `(u, v)` is a Legendre transport along `γ` if near each `t₀` it is `(f ∘ γ, f' ∘ γ)`
for a local solution `f` of the Legendre equation at `γ(t₀)`. -/
theorem legTr_isTransport_of_local (ν μ : ℂ) {γ : ℝ → ℂ} (hγ : Differentiable ℝ γ) {u v : ℝ → ℂ}
    (hloc : ∀ t₀ ∈ Icc (0:ℝ) 1, ∃ f f1 : ℂ → ℂ, ∃ f2 : ℂ, HasDerivAt f (f1 (γ t₀)) (γ t₀) ∧
      HasDerivAt f1 f2 (γ t₀) ∧ 1 - γ t₀ ^ 2 ≠ 0 ∧
      (1 - γ t₀ ^ 2) * f2 - 2 * γ t₀ * f1 (γ t₀) + (ν*(ν+1) - μ^2/(1 - γ t₀ ^ 2)) * f (γ t₀) = 0 ∧
      ∀ᶠ t in 𝓝[Icc 0 1] t₀, u t = f (γ t) ∧ v t = f1 (γ t)) :
    IsLegendreTransport ν μ γ (u 0) (v 0) u v := by
  have hd : ∀ t₀ ∈ Icc (0:ℝ) 1, HasDerivWithinAt u (deriv γ t₀ * v t₀) (Icc 0 1) t₀ ∧
      HasDerivWithinAt v (deriv γ t₀ * (2 * γ t₀ * v t₀ - (ν*(ν+1) - μ^2/(1 - γ t₀ ^ 2)) * u t₀) /
        (1 - γ t₀ ^ 2)) (Icc 0 1) t₀ := by
    intro t₀ ht₀
    obtain ⟨f, f1, f2, hf, hf1, hne, hode, hev⟩ := hloc t₀ ht₀
    have hg := (hγ t₀).hasDerivAt
    have hu0 : u t₀ = f (γ t₀) := (hev.self_of_nhdsWithin ht₀).1
    have hv0 : v t₀ = f1 (γ t₀) := (hev.self_of_nhdsWithin ht₀).2
    have hA := (hf.comp t₀ hg).hasDerivWithinAt (s := Icc 0 1)
    have hB := (hf1.comp t₀ hg).hasDerivWithinAt (s := Icc 0 1)
    refine ⟨(hA.congr_of_eventuallyEq (hev.mono fun t h => h.1) hu0).congr_deriv ?_,
      (hB.congr_of_eventuallyEq (hev.mono fun t h => h.2) hv0).congr_deriv ?_⟩
    · rw [hv0]; ring
    · rw [hv0, hu0, eq_div_iff hne]
      linear_combination (deriv γ t₀) * hode
  refine ⟨rfl, rfl, fun t ht => (hd t ht).1.continuousWithinAt,
    fun t ht => (hd t ht).2.continuousWithinAt, hd⟩

/-- A function continuous within `s` at `t₀` with locally constant exponential is locally
constant. -/
theorem legTr_eventually_eq_of_exp {d : ℝ → ℂ} {s : Set ℝ} {t₀ : ℝ}
    (hd : ContinuousWithinAt d s t₀) (he : ∀ᶠ t in 𝓝[s] t₀, exp (d t) = exp (d t₀)) :
    ∀ᶠ t in 𝓝[s] t₀, d t = d t₀ := by
  have hn : ∀ᶠ t in 𝓝[s] t₀, ‖d t - d t₀‖ < 2*π := by
    have := (hd.tendsto.sub_const (d t₀)).norm
    rw [sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hn, he] with t h1 h2
  have h3 : exp (d t - d t₀) = 1 := by rw [exp_sub, h2, div_self (exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h3
  rw [hn] at h1
  have : ‖(n:ℂ) * (2*π*I)‖ = |(n:ℝ)| * (2*π) := by
    rw [norm_mul, norm_intCast]; simp [abs_of_pos Real.pi_pos]
  rw [this] at h1
  have hn0 : n = 0 := by
    have : |(n:ℝ)| < 1 := by nlinarith [Real.pi_pos]
    have : |n| < 1 := by exact_mod_cast this
    have := abs_lt.mp this
    omega
  rw [hn0] at hn; simp at hn; linear_combination hn

/-- The regular factor `(w+1)^{-μ/2} 𝐅(ν+1, -ν; 1+μ; (1-w)/2)` of `P^{-μ}_ν`. -/
noncomputable def legTr_K (ν μ w : ℂ) : ℂ :=
  exp (-μ/2*log (w+1)) * regularizedGaussHG (ν+1) (-ν) (1+μ) ((1-w)/2)

/-- `P^{-μ}_ν(w) = e^{μ log(w-1)/2} K(w)`. -/
theorem legTr_associatedP_eq (ν μ w : ℂ) :
    associatedP ν (-μ) w = exp (μ/2*log (w-1)) * legTr_K ν μ w := by
  rw [associatedP, legTr_K, show (1:ℂ) - -μ = 1+μ by ring, ← mul_assoc, ← exp_add]
  congr 2; ring

/-- `𝖯^{-μ}_ν(w) = e^{μ log(1-w)/2} K(w)` (continued into the disk). -/
theorem legTr_ferrersPCont_eq (ν μ w : ℂ) :
    ferrersPCont ν (-μ) w = exp (μ/2*log (1-w)) * legTr_K ν μ w := by
  rw [ferrersPCont, legTr_K, show (1:ℂ) - -μ = 1+μ by ring, ← mul_assoc, ← exp_add, add_comm 1 w]
  congr 2; ring

/-- `K` is analytic where `w + 1 ∉ (-∞, 0]` and `(1-w)/2 ∉ [1, ∞)`. -/
theorem legTr_K_analyticAt (ν μ : ℂ) {w : ℂ} (hp : w+1 ∈ slitPlane) (hc : (1-w)/2 ∈ cutPlane) :
    AnalyticAt ℂ (legTr_K ν μ) w := by
  have hG : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG (ν+1) (-ν) (1+μ) ((1-w)/2)) w :=
    (analyticAt_regularizedGaussHG _ _ _ hc).comp_of_eq (by fun_prop) rfl
  have hE : AnalyticAt ℂ (fun w : ℂ => exp (-μ/2*log (w+1))) w := by
    fun_prop (disch := assumption)
  exact hE.mul hG

/-- Derivative of `e^{μL/2} K` for a branch `L` of `log(w-1)` (up to constants). -/
theorem legTr_hasDerivAt_branch (ν μ : ℂ) {L : ℂ → ℂ} {w : ℂ} (hL : HasDerivAt L (1/(w-1)) w)
    (hK : DifferentiableAt ℂ (legTr_K ν μ) w) :
    HasDerivAt (fun w => exp (μ/2*L w) * legTr_K ν μ w)
      (exp (μ/2*L w) * (μ/2*legTr_K ν μ w/(w-1) + deriv (legTr_K ν μ) w)) w := by
  have h := ((hL.const_mul (μ/2)).cexp).mul hK.hasDerivAt
  convert h using 1; ring

/-- `(log(w-1))' = 1/(w-1)`. -/
theorem legTr_hasDerivAt_log_sub_one {w : ℂ} (hw : w-1 ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => log (w-1)) (1/(w-1)) w := by
  simpa using ((hasDerivAt_id w).sub_const 1).clog hw

/-- `(log(1-w))' = 1/(w-1)`. -/
theorem legTr_hasDerivAt_log_one_sub {w : ℂ} (hw : 1-w ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => log (1-w)) (1/(w-1)) w := by
  have h := ((hasDerivAt_id' w).const_sub 1).clog hw
  have hne : 1 - w ≠ 0 := slitPlane_ne_zero hw
  have hne' : w - 1 ≠ 0 := fun h => hne (by linear_combination -h)
  convert h using 1
  field_simp
  ring

/-- The Legendre equation for `𝖯^μ_ν` continued into the unit disk. -/
theorem legTr_ferrersPCont_ode (ν μ : ℂ) {w : ℂ} (hw : w ∈ Metric.ball (0:ℂ) 1) :
    (1-w^2)*iteratedDeriv 2 (ferrersPCont ν μ) w-2*w*deriv (ferrersPCont ν μ) w+
      (ν*(ν+1)-μ^2/(1-w^2))*ferrersPCont ν μ w=0 := by
  set F := ferrersPCont ν μ
  set B := Metric.ball (0:ℂ) 1
  have hF := ferrersPCont_analytic ν μ
  have hne : ∀ w ∈ B, 1 - w^2 ≠ 0 := fun w hw => slitPlane_ne_zero (legendre_disk_facts hw).2.2.2.1
  have hE : AnalyticOnNhd ℂ (fun w => (1-w^2)*iteratedDeriv 2 F w-2*w*deriv F w+
      (ν*(ν+1)-μ^2/(1-w^2))*F w) B := by
    intro w hw
    have h2 : AnalyticAt ℂ (iteratedDeriv 2 F) w := by
      rw [iteratedDeriv_eq_iterate]; exact hF.iterated_deriv 2 w hw
    have h1 := hF.deriv w hw
    have h0 := hF w hw
    have hd : AnalyticAt ℂ (fun w : ℂ => μ^2/(1-w^2)) w :=
      analyticAt_const.div (by fun_prop) (hne w hw)
    have h1' : AnalyticAt ℂ (deriv F) w := h1
    have h0' : AnalyticAt ℂ F w := h0
    exact (((analyticAt_const.sub (analyticAt_id.pow 2)).fun_mul h2).fun_sub
      ((analyticAt_const.fun_mul analyticAt_id).fun_mul h1')).fun_add ((analyticAt_const.fun_sub hd).fun_mul h0')
  have hI : (I/2 : ℂ) ∈ B := by
    simp only [B, Metric.mem_ball, dist_zero_right, norm_div, norm_I]; norm_num
  have hev : (fun w => (1-w^2)*iteratedDeriv 2 F w-2*w*deriv F w+
      (ν*(ν+1)-μ^2/(1-w^2))*F w) =ᶠ[𝓝 (I/2)] 0 := by
    have hV : IsOpen (B ∩ {w : ℂ | 0 < w.im}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
    have hI' : (I/2:ℂ) ∈ B ∩ {w : ℂ | 0 < w.im} := ⟨hI, by simp⟩
    filter_upwards [hV.mem_nhds hI'] with w ⟨hwB, hwi⟩
    have hloc : F =ᶠ[𝓝 w] fun w => exp (μ*π*I/2) * associatedP ν μ w := by
      filter_upwards [hV.mem_nhds ⟨hwB, hwi⟩] with y ⟨_, hyi⟩
      have := associatedP_eq_ferrersPCont (s := 1) (Or.inl rfl) ν μ (z := y) (by simpa using hyi)
      have e : exp (μ*π*I/2) * exp (-((1:ℝ):ℂ)*μ*π*I/2) = 1 := by
        rw [← exp_add]; push_cast; ring_nf; exact exp_zero
      rw [this, ← mul_assoc, e, one_mul]
    have hw1 : w - 1 ∈ slitPlane := Or.inr (by simp; exact hwi.ne')
    have hd1 := hloc.deriv_eq
    have hd2 := (hloc.iteratedDeriv 2).self_of_nhds
    rw [iteratedDeriv_const_mul_field] at hd2
    rw [show deriv (fun w => exp (μ*π*I/2) * associatedP ν μ w) w =
      exp (μ*π*I/2) * deriv (associatedP ν μ) w from deriv_const_mul _
        (associatedP_analytic ν μ w hw1).differentiableAt] at hd1
    have hode := associatedP_ode ν μ hw1
    simp only [Pi.zero_apply]
    rw [hd2, hd1, hloc.self_of_nhds]
    linear_combination exp (μ*π*I/2) * hode
  exact hE.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hI hev hw

/-- The transported value `e^{μℓ(t)/2} K(γ(t))`, with `ℓ` a continuous logarithm of `γ - 1`. -/
noncomputable def legTr_u (ν μ : ℂ) (γ ℓ : ℝ → ℂ) (t : ℝ) : ℂ :=
  exp (μ/2*ℓ t) * legTr_K ν μ (γ t)

/-- The transported derivative `e^{μℓ(t)/2} (μ K/(2(γ-1)) + K')(γ(t))`. -/
noncomputable def legTr_v (ν μ : ℂ) (γ ℓ : ℝ → ℂ) (t : ℝ) : ℂ :=
  exp (μ/2*ℓ t) * (μ/2*legTr_K ν μ (γ t)/(γ t - 1) + deriv (legTr_K ν μ) (γ t))

/-- Local data for `legTr_isTransport_of_local` from a local branch `L` of `log(w-1)` (up to a
constant) and a solution `F = e^{μL/2} K` of the Legendre equation near `γ(t₀)`. -/
theorem legTr_local_branch (ν μ : ℂ) {γ : ℝ → ℂ} (hγ : Differentiable ℝ γ) {ℓ : ℝ → ℂ}
    (hℓ : ContinuousOn ℓ (Icc 0 1)) (hexp : ∀ t ∈ Icc (0:ℝ) 1, exp (ℓ t) = γ t - 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0:ℝ) 1) {L F : ℂ → ℂ} {U : Set ℂ} {κ : ℂ} (hU : IsOpen U)
    (hw₀ : γ t₀ ∈ U) (hLd : ∀ w ∈ U, HasDerivAt L (1/(w-1)) w)
    (hLexp : ∀ w ∈ U, exp (L w) = κ * (w - 1)) (hκ : κ ≠ 0)
    (hFeq : ∀ w, F w = exp (μ/2*L w) * legTr_K ν μ w)
    (hKd : ∀ w ∈ U, DifferentiableAt ℂ (legTr_K ν μ) w) (hFa : AnalyticOnNhd ℂ F U)
    (hode : ∀ w ∈ U, (1-w^2)*iteratedDeriv 2 F w-2*w*deriv F w+(ν*(ν+1)-μ^2/(1-w^2))*F w=0)
    (hne : ∀ w ∈ U, 1 - w^2 ≠ 0) :
    ∃ f f1 : ℂ → ℂ, ∃ f2 : ℂ, HasDerivAt f (f1 (γ t₀)) (γ t₀) ∧
      HasDerivAt f1 f2 (γ t₀) ∧ 1 - γ t₀ ^ 2 ≠ 0 ∧
      (1 - γ t₀ ^ 2) * f2 - 2 * γ t₀ * f1 (γ t₀) + (ν*(ν+1) - μ^2/(1 - γ t₀ ^ 2)) * f (γ t₀) = 0 ∧
      ∀ᶠ t in 𝓝[Icc 0 1] t₀, legTr_u ν μ γ ℓ t = f (γ t) ∧ legTr_v ν μ γ ℓ t = f1 (γ t) := by
  set w₀ := γ t₀
  have hne1 : ∀ w ∈ U, w - 1 ≠ 0 := fun w hw h => hne w hw (by
    rw [show w = 1 by linear_combination h]; ring)
  have hγU : ∀ᶠ t in 𝓝 t₀, γ t ∈ U := (hγ t₀).continuousAt.preimage_mem_nhds (hU.mem_nhds hw₀)
  set d : ℝ → ℂ := fun t => ℓ t - L (γ t)
  have hdc : ContinuousWithinAt d (Icc 0 1) t₀ :=
    (hℓ t₀ ht₀).sub (((hLd w₀ hw₀).differentiableAt.continuousAt.comp
      (hγ t₀).continuousAt).continuousWithinAt)
  have hdexp : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ U → exp (d t) = κ⁻¹ := by
    intro t ht hU'
    simp only [d]
    rw [exp_sub, hexp t ht, hLexp _ hU']
    field_simp [hne1 _ hU']
  have hd := legTr_eventually_eq_of_exp hdc (by
    filter_upwards [nhdsWithin_le_nhds hγU, self_mem_nhdsWithin] with t h1 h2
    rw [hdexp t h2 h1, hdexp t₀ ht₀ hw₀])
  set c := exp (μ/2*d t₀)
  have hF' : ∀ w ∈ U, deriv F w = exp (μ/2*L w) * (μ/2*legTr_K ν μ w/(w-1) + deriv (legTr_K ν μ) w) := by
    intro w hw
    have he : F = fun w => exp (μ/2*L w) * legTr_K ν μ w := funext hFeq
    rw [he]; exact (legTr_hasDerivAt_branch ν μ (hLd w hw) (hKd w hw)).deriv
  refine ⟨fun w => c * F w, fun w => c * deriv F w, c * iteratedDeriv 2 F w₀,
    ((hFa w₀ hw₀).differentiableAt.hasDerivAt).const_mul c, ?_, hne w₀ hw₀, ?_, ?_⟩
  · have h := ((hFa.deriv w₀ hw₀).differentiableAt.hasDerivAt).const_mul c
    rwa [iteratedDeriv_succ, iteratedDeriv_one]
  · linear_combination c * hode w₀ hw₀
  · filter_upwards [hd, nhdsWithin_le_nhds hγU] with t hdt hUt
    have hl : ℓ t = L (γ t) + d t₀ := by rw [← hdt]; simp only [d]; ring
    have hE : exp (μ/2*ℓ t) = c * exp (μ/2*L (γ t)) := by
      rw [hl, ← exp_add]; congr 1; ring
    refine ⟨?_, ?_⟩
    · simp only [legTr_u]; rw [hE, hFeq]; ring
    · simp only [legTr_v]; rw [hE, hF' _ hUt]; ring

/-- Transport of `P^{-μ}_ν` along a path that stays in `ℂ ∖ (-∞, 1]` or in the unit disk:
`u = e^{μℓ/2} K(γ)`, `ℓ` a continuous logarithm of `γ - 1`. -/
theorem legTr_isTransport_branch (ν μ : ℂ) {γ : ℝ → ℂ} (hγ : Differentiable ℝ γ) {ℓ : ℝ → ℂ}
    (hℓ : ContinuousOn ℓ (Icc 0 1)) (hexp : ∀ t ∈ Icc (0:ℝ) 1, exp (ℓ t) = γ t - 1)
    (hdom : ∀ t ∈ Icc (0:ℝ) 1, γ t - 1 ∈ slitPlane ∨ γ t ∈ Metric.ball (0:ℂ) 1) :
    IsLegendreTransport ν μ γ (legTr_u ν μ γ ℓ 0) (legTr_v ν μ γ ℓ 0) (legTr_u ν μ γ ℓ)
      (legTr_v ν μ γ ℓ) := by
  refine legTr_isTransport_of_local ν μ hγ fun t₀ ht₀ => ?_
  rcases hdom t₀ ht₀ with hs | hb
  · have hp : ∀ w : ℂ, w - 1 ∈ slitPlane → w + 1 ∈ slitPlane := fun w hw => by
      simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hw
    refine legTr_local_branch ν μ hγ hℓ hexp ht₀ (L := fun w => log (w-1)) (F := associatedP ν (-μ))
      (U := {w | w-1 ∈ slitPlane}) (κ := 1) isOpen_sub_one_mem_slitPlane hs
      (fun w hw => legTr_hasDerivAt_log_sub_one hw)
      (fun w hw => by simp [exp_log (slitPlane_ne_zero hw)]) one_ne_zero (legTr_associatedP_eq ν μ)
      (fun w hw => (legTr_K_analyticAt ν μ (hp w hw)
        (mem_cutPlane_of_one_add (by simpa [add_comm] using hp w hw))).differentiableAt)
      (associatedP_analytic ν (-μ)) (fun w hw => by
        have := associatedP_ode ν (-μ) hw; rwa [neg_sq] at this) (fun w hw => ?_)
    have h1 := slitPlane_ne_zero (show w - 1 ∈ slitPlane from hw)
    have h2 := slitPlane_ne_zero (hp w hw)
    intro h; apply mul_ne_zero h1 h2; linear_combination -h
  · refine legTr_local_branch ν μ hγ hℓ hexp ht₀ (L := fun w => log (1-w)) (F := ferrersPCont ν (-μ))
      (U := Metric.ball (0:ℂ) 1) (κ := -1) Metric.isOpen_ball hb
      (fun w hw => legTr_hasDerivAt_log_one_sub (legendre_disk_facts hw).2.1)
      (fun w hw => by rw [exp_log (slitPlane_ne_zero (legendre_disk_facts hw).2.1)]; ring)
      (by norm_num) (legTr_ferrersPCont_eq ν μ)
      (fun w hw => (legTr_K_analyticAt ν μ (by simpa [add_comm] using (legendre_disk_facts hw).1)
        (legendre_disk_facts hw).2.2.1).differentiableAt)
      (ferrersPCont_analytic ν (-μ)) (fun w hw => by
        have := legTr_ferrersPCont_ode ν (-μ) hw; rwa [neg_sq] at this)
      (fun w hw => slitPlane_ne_zero (legendre_disk_facts hw).2.2.2.1)

/-- Gluing two everywhere-differentiable functions that agree to first order at `a`. -/
theorem legTr_hasDerivAt_piecewise {f g f' g' : ℝ → ℂ} {a : ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hg : ∀ t, HasDerivAt g (g' t) t) (ha : f a = g a) (ha' : f' a = g' a) (t : ℝ) :
    HasDerivAt (fun t => if t ≤ a then f t else g t) (if t ≤ a then f' t else g' t) t := by
  rcases lt_trichotomy t a with h | h | h
  · simp only [h.le, ↓reduceIte]
    refine (hf t).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with x hx
    simp [le_of_lt (show x < a from hx)]
  · rw [h]
    simp only [le_refl, ↓reduceIte]
    have h1 : HasDerivWithinAt (fun x => if x ≤ a then f x else g x) (f' a) (Iic a) a :=
      (hf a).hasDerivWithinAt.congr (fun x hx => by simp [show x ≤ a from hx]) (by simp)
    have h2 : HasDerivWithinAt (fun x => if x ≤ a then f x else g x) (f' a) (Ici a) a := by
      rw [ha']
      refine (hg a).hasDerivWithinAt.congr (fun x hx => ?_) (by simp [ha])
      rcases eq_or_lt_of_le (show a ≤ x from hx) with h | h
      · rw [← h]; simp [ha]
      · simp [not_le.mpr h]
    have := h1.union h2
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · simp only [not_le.mpr h, ↓reduceIte]
    refine (hg t).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with x hx
    simp [not_le.mpr (show a < x from hx)]

/-- Gluing two functions continuous on adjacent closed intervals. -/
theorem legTr_continuousOn_piecewise {f g : ℝ → ℂ} {p a q : ℝ} (hf : ContinuousOn f (Icc p a))
    (hg : ContinuousOn g (Icc a q)) (ha : f a = g a) :
    ContinuousOn (fun t => if t ≤ a then f t else g t) (Icc p q) := by
  have h1 : ContinuousOn (fun t => if t ≤ a then f t else g t) (Icc p a) :=
    hf.congr fun x hx => by simp [hx.2]
  have h2 : ContinuousOn (fun t => if t ≤ a then f t else g t) (Icc a q) := hg.congr fun x hx => by
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; simp [ha]
    · simp [not_le.mpr h]
  refine (h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc).mono fun x hx => ?_
  rcases le_total x a with h | h
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr ⟨h, hx.2⟩

/-- `ℂ ∖ (-∞, 0]` is star-shaped about `1/2`. -/
theorem legTr_star_mem {w : ℂ} (hw : w ∈ slitPlane) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - r) * w + r * (1/2) ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  rcases eq_or_lt_of_le hr1 with h | h
  · left; rw [h]; norm_num
  · by_cases hi : w.im = 0
    · left
      have : 0 < w.re := hw.resolve_right (not_not.mpr hi)
      simp; nlinarith
    · right; simp [hi]; exact fun h' => by linarith

/-- The smooth step maps `[0, 1]` into `[0, 1]`. -/
theorem legTr_S_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ legendreSmoothStep x ∧ legendreSmoothStep x ≤ 1 := by
  unfold legendreSmoothStep
  constructor
  · nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.mpr h1)]
  · nlinarith [mul_nonneg (sq_nonneg (1-x)) (by linarith : (0:ℝ) ≤ 1+2*x)]

/-- Derivative of `t ↦ S(3t-c)`. -/
theorem legTr_hasDerivAt_S (c : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ((legendreSmoothStep (3*t-c) : ℝ) : ℂ))
      (((6*(3*t-c)-6*(3*t-c)^2)*3 : ℝ) : ℂ) t := by
  have h : HasDerivAt (fun t : ℝ => legendreSmoothStep (3*t-c)) ((6*(3*t-c)-6*(3*t-c)^2)*3) t := by
    unfold legendreSmoothStep
    have h1 : HasDerivAt (fun t : ℝ => 3*t-c) 3 t := by
      simpa using ((hasDerivAt_id t).const_mul 3).sub_const c
    have := ((h1.pow 2).const_mul 3).sub ((h1.pow 3).const_mul 2)
    convert this using 1; push_cast; ring
  exact h.ofReal_comp

/-- The derivative `(6x-6x²)·3` of `t ↦ S(3t-c)`. -/
noncomputable def legTr_Sd (c t : ℝ) : ℂ := (((6*(3*t-c)-6*(3*t-c)^2)*3 : ℝ) : ℂ)

/-- The derivative of `legendreOneLoop`. -/
noncomputable def legTr_loopDeriv (z : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  if t ≤ 1/3 then legTr_Sd 0 t*(3/2-z) else if t ≤ 2/3 then
    1/2*exp (2*π*I*s*legendreSmoothStep (3*t-1))*(2*π*I*s*legTr_Sd 1 t) else legTr_Sd 2 t*(z-3/2)

/-- `e^{2πis S(1)} = 1`. -/
theorem legTr_exp_two_pi_s (s : ℤ) : exp (2*π*I*s*((legendreSmoothStep (3*(2/3:ℝ)-1) : ℝ) : ℂ)) = 1 := by
  rw [show legendreSmoothStep (3*(2/3:ℝ)-1) = 1 by unfold legendreSmoothStep; norm_num]
  rw [show 2*π*I*(s:ℂ)*((1:ℝ):ℂ) = (s:ℂ)*(2*π*I) by push_cast; ring]
  exact exp_int_mul_two_pi_mul_I s

/-- `legendreOneLoop` is differentiable, with derivative `legTr_loopDeriv`. -/
theorem legTr_hasDerivAt_loop (z : ℂ) (s : ℤ) (t : ℝ) :
    HasDerivAt (legendreOneLoop z s) (legTr_loopDeriv z s t) t := by
  have hA : ∀ t, HasDerivAt (fun t : ℝ => z+legendreSmoothStep (3*t)*(3/2-z)) (legTr_Sd 0 t*(3/2-z)) t := by
    intro t
    have := ((legTr_hasDerivAt_S 0 t).mul_const (3/2-z)).const_add z
    simpa [legTr_Sd] using this
  have hB : ∀ t, HasDerivAt (fun t : ℝ => 1+1/2*exp (2*π*I*s*legendreSmoothStep (3*t-1)))
      (1/2*exp (2*π*I*s*legendreSmoothStep (3*t-1))*(2*π*I*s*legTr_Sd 1 t)) t := by
    intro t
    have := ((((legTr_hasDerivAt_S 1 t).const_mul (2*π*I*s)).cexp).const_mul (1/2)).const_add 1
    convert this using 1
    simp only [legTr_Sd]; ring
  have hC : ∀ t, HasDerivAt (fun t : ℝ => 3/2+legendreSmoothStep (3*t-2)*(z-3/2)) (legTr_Sd 2 t*(z-3/2)) t := by
    intro t
    have := ((legTr_hasDerivAt_S 2 t).mul_const (z-3/2)).const_add (3/2)
    simpa [legTr_Sd] using this
  have hBC := legTr_hasDerivAt_piecewise (a := 2/3) hB hC (by
      rw [legTr_exp_two_pi_s]; unfold legendreSmoothStep; norm_num)
    (by unfold legTr_Sd; norm_num)
  have h := legTr_hasDerivAt_piecewise (a := 1/3) hA hBC (by
      unfold legendreSmoothStep; norm_num) (by unfold legTr_Sd; norm_num) t
  exact h

/-- The derivative of `legendreOneLoop` is continuous. -/
theorem legTr_continuous_loopDeriv (z : ℂ) (s : ℤ) : Continuous (legTr_loopDeriv z s) := by
  have hS : ∀ c, Continuous (legTr_Sd c) := fun c => by unfold legTr_Sd; fun_prop
  have hS' : Continuous fun t : ℝ => ((legendreSmoothStep (3*t-1) : ℝ) : ℂ) := by
    unfold legendreSmoothStep; fun_prop
  unfold legTr_loopDeriv
  refine Continuous.if_le ((hS 0).mul continuous_const)
    (Continuous.if_le (by fun_prop) ((hS 2).mul continuous_const) continuous_id continuous_const ?_)
    continuous_id continuous_const ?_
  · intro x hx; rw [hx]; unfold legTr_Sd; norm_num
  · intro x hx; rw [hx]; unfold legTr_Sd; norm_num

/-- `legendreOneLoop` is `C¹`. -/
theorem legTr_contDiff_loop (z : ℂ) (s : ℤ) : ContDiff ℝ 1 (legendreOneLoop z s) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (legTr_hasDerivAt_loop z s t).differentiableAt, ?_⟩
  have : deriv (legendreOneLoop z s) = legTr_loopDeriv z s :=
    funext fun t => (legTr_hasDerivAt_loop z s t).deriv
  rw [this]; exact legTr_continuous_loopDeriv z s

/-- A continuous logarithm of `γ - 1` along `legendreOneLoop`. -/
noncomputable def legTr_ell (z : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  if t ≤ 1/3 then log (z+legendreSmoothStep (3*t)*(3/2-z)-1) else if t ≤ 2/3 then
    log (1/2)+2*π*I*s*legendreSmoothStep (3*t-1) else log (3/2+legendreSmoothStep (3*t-2)*(z-3/2)-1)+2*π*I*s

/-- The first leg of `legendreOneLoop` stays in `ℂ ∖ (-∞, 1]`. -/
theorem legTr_mem_first {z : ℂ} (hz : z-1 ∈ slitPlane) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (1/3)) :
    z+legendreSmoothStep (3*t)*(3/2-z)-1 ∈ slitPlane := by
  obtain ⟨h0, h1⟩ := legTr_S_mem (x := 3*t) (by linarith [ht.1]) (by linarith [ht.2])
  have := legTr_star_mem hz h0 h1
  convert this using 1; ring

/-- The last leg of `legendreOneLoop` stays in `ℂ ∖ (-∞, 1]`. -/
theorem legTr_mem_last {z : ℂ} (hz : z-1 ∈ slitPlane) {t : ℝ} (ht : t ∈ Icc (2/3:ℝ) 1) :
    3/2+legendreSmoothStep (3*t-2)*(z-3/2)-1 ∈ slitPlane := by
  obtain ⟨h0, h1⟩ := legTr_S_mem (x := 3*t-2) (by linarith [ht.1]) (by linarith [ht.2])
  have := legTr_star_mem hz (r := 1 - legendreSmoothStep (3*t-2)) (by linarith) (by linarith)
  convert this using 1; push_cast; ring

/-- `e^{ℓ(t)} = γ(t) - 1` along `legendreOneLoop`. -/
theorem legTr_exp_ell {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    exp (legTr_ell z s t) = legendreOneLoop z s t - 1 := by
  unfold legTr_ell legendreOneLoop
  split_ifs with h1 h2
  · exact exp_log (slitPlane_ne_zero (legTr_mem_first hz ⟨ht.1, h1⟩))
  · rw [exp_add, exp_log (by norm_num)]; ring
  · rw [exp_add, exp_log (slitPlane_ne_zero (legTr_mem_last hz ⟨by linarith, ht.2⟩)),
      show 2*π*I*(s:ℂ) = (s:ℂ)*(2*π*I) by ring, exp_int_mul_two_pi_mul_I, mul_one]

/-- `legTr_ell` is continuous on `[0, 1]`. -/
theorem legTr_continuousOn_ell {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    ContinuousOn (legTr_ell z s) (Icc 0 1) := by
  have hS : ∀ c : ℝ, Continuous fun t : ℝ => ((legendreSmoothStep (3*t-c) : ℝ) : ℂ) := fun c => by
    unfold legendreSmoothStep; fun_prop
  have hS0 : Continuous fun t : ℝ => ((legendreSmoothStep (3*t) : ℝ) : ℂ) := by
    unfold legendreSmoothStep; fun_prop
  unfold legTr_ell
  refine legTr_continuousOn_piecewise (p := 0) (a := 1/3) (q := 1) ?_ ?_ ?_
  · intro t ht
    have hc : Continuous (fun t : ℝ => z+(legendreSmoothStep (3*t):ℂ)*(3/2-z)-1) :=
      (continuous_const.add (hS0.mul continuous_const)).sub continuous_const
    exact (hc.continuousAt.clog (legTr_mem_first hz ht)).continuousWithinAt
  · refine legTr_continuousOn_piecewise (p := 1/3) (a := 2/3) (q := 1)
      (continuous_const.add (continuous_const.mul (hS 1))).continuousOn ?_ ?_
    · intro t ht
      have hc : Continuous (fun t : ℝ => 3/2+(legendreSmoothStep (3*t-2):ℂ)*(z-3/2)-1) :=
        (continuous_const.add ((hS 2).mul continuous_const)).sub continuous_const
      exact ((hc.continuousAt.clog (legTr_mem_last hz ht)).add
        continuousAt_const).continuousWithinAt
    · unfold legendreSmoothStep; norm_num
  · simp only [show (1/3:ℝ) ≤ 2/3 by norm_num, ↓reduceIte]
    unfold legendreSmoothStep; norm_num

/-- Each point of `legendreOneLoop` lies in `ℂ ∖ (-∞, 1]` or in the unit disk. -/
theorem legTr_loop_dom {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    legendreOneLoop z s t - 1 ∈ slitPlane ∨ legendreOneLoop z s t ∈ Metric.ball (0:ℂ) 1 := by
  unfold legendreOneLoop
  split_ifs with h1 h2
  · exact Or.inl (legTr_mem_first hz ⟨ht.1, h1⟩)
  · set w : ℂ := 1/2*exp (2*π*I*s*legendreSmoothStep (3*t-1))
    have hw : 1 + w - 1 = w := by ring
    rw [hw]
    by_cases hm : w ∈ slitPlane
    · exact Or.inl hm
    · right
      have hn : ‖w‖ = 1/2 := by
        simp only [w, norm_mul, norm_exp]
        simp
      rw [mem_slitPlane_iff] at hm
      push Not at hm
      have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hm.2])
      have habs : |w.re| = 1/2 := by rw [← hn, hw', norm_real, Real.norm_eq_abs]; simp
      have hre : w.re = -1/2 := by
        rcases abs_eq (by norm_num : (0:ℝ) ≤ 1/2) |>.mp habs with h | h
        · linarith [hm.1]
        · linarith
      rw [hw', hre]
      simp only [Metric.mem_ball, dist_zero_right]
      rw [show (1:ℂ) + (((-1/2:ℝ)):ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, norm_real]
      norm_num
  · exact Or.inl (legTr_mem_last hz ⟨by linarith, ht.2⟩)

/-- associatedP one continuation. The transport is `e^{μℓ(t)/2} K(γ(t))`, `ℓ` a continuous
logarithm of `γ - 1` along the loop (`legTr_isTransport_branch`), so `ℓ(1) = log(z-1) + 2πis`. -/
@[dlmf 14.24.E3]
theorem associatedP_one_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    legendreOneContinued (associatedP ν (-μ)) ν μ z s=exp (s*μ*π*I)*associatedP ν (-μ) z := by
  have hγd : Differentiable ℝ (legendreOneLoop z s) := fun t => (legTr_hasDerivAt_loop z s t).differentiableAt
  have huv := legTr_isTransport_branch ν μ hγd (legTr_continuousOn_ell hz s)
    (fun t ht => legTr_exp_ell hz s ht) (fun t ht => legTr_loop_dom hz s ht)
  have hreg : ∀ t ∈ Icc (0:ℝ) 1, legendreOneLoop z s t ≠ 1 ∧ legendreOneLoop z s t ≠ -1 := by
    intro t ht
    rcases legTr_loop_dom hz s ht with h | h
    · refine ⟨fun h1 => slitPlane_ne_zero h (by rw [h1]; ring), fun h1 => ?_⟩
      rw [h1] at h; norm_num [mem_slitPlane_iff] at h
    · have hn : ‖legendreOneLoop z s t‖ < 1 := by simpa using h
      refine ⟨fun h1 => by rw [h1] at hn; simp at hn, fun h1 => by rw [h1] at hn; simp at hn⟩
  have key := legendreTransport_unique ν μ _ _ (legendreOneLoop z s) (legTr_contDiff_loop z s) hreg huv
  have hγ0 : legendreOneLoop z s 0 = z := by
    simp only [legendreOneLoop]; unfold legendreSmoothStep; norm_num
  have hγ1 : legendreOneLoop z s 1 = z := by
    simp only [legendreOneLoop]; unfold legendreSmoothStep; norm_num
  have hℓ0 : legTr_ell z s 0 = log (z-1) := by
    simp only [legTr_ell]; unfold legendreSmoothStep; norm_num
  have hℓ1 : legTr_ell z s 1 = log (z-1) + 2*π*I*s := by
    simp only [legTr_ell]; unfold legendreSmoothStep; norm_num
  have hp : z + 1 ∈ slitPlane := by simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz
  have hKd : DifferentiableAt ℂ (legTr_K ν μ) z := (legTr_K_analyticAt ν μ hp
    (mem_cutPlane_of_one_add (by simpa [add_comm] using hp))).differentiableAt
  have hu0 : legTr_u ν μ (legendreOneLoop z s) (legTr_ell z s) 0 = associatedP ν (-μ) z := by
    rw [legTr_u, hγ0, hℓ0, legTr_associatedP_eq]
  have hv0 : legTr_v ν μ (legendreOneLoop z s) (legTr_ell z s) 0 = deriv (associatedP ν (-μ)) z := by
    have he : associatedP ν (-μ) = fun w => exp (μ/2*log (w-1)) * legTr_K ν μ w :=
      funext (legTr_associatedP_eq ν μ)
    rw [he, (legTr_hasDerivAt_branch ν μ (legTr_hasDerivAt_log_sub_one hz) hKd).deriv, legTr_v,
      hγ0, hℓ0]
  rw [hu0, hv0] at key
  unfold legendreOneContinued
  rw [key, legTr_u, hγ1, hℓ1, legTr_associatedP_eq, ← mul_assoc, ← exp_add]
  congr 2; ring

end DLMF.Legendre
end
