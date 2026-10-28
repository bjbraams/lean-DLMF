/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Continuation
public import DLMFMathlib.Analysis.SpecificLimits.Pincherle

/-!
# Tools for the Ferrers Fourier series (DLMF §14.13)

The hypergeometric form behind DLMF 14.13.1–14.13.2:
`s(πi/2) 𝖯^μ_ν(cos θ) + 𝖰^μ_ν(cos θ) = √π Γ(ν+μ+1) (2 sin θ)^μ e^{s(ν+μ+1)iθ}
𝐅(ν+μ+1, μ+1/2; ν+3/2; e^{2isθ})`, `s = ±1`, `0 < θ < π` (`legFS_PQ_hyp`), for all `ν, μ`
with `ν + μ ≠ -1, -2, …`. Route:

* the inverse Joukowski map `ζ(z) = z - √(z²-1)` on `ℂ ∖ (-∞, 1]` has `|ζ| < 1`, `ζ ∉ (-∞, 0]`
  (`legInt_norm_zeta_lt_one`, `legInt_zeta_mem_slitPlane` in
  `DLMF.Legendre.IntegralRepresentations`);
* the toroidal form DLMF 14.19.3 (`toroidalQ_hypergeometric`, `z = cosh ξ`, `ζ = e^{-ξ}`) extends
  by the identity theorem to `𝑸^μ_ν(z) = √π (1-ζ²)^μ ζ^{ν+1} 𝐅(μ+1/2, ν+μ+1; ν+3/2; ζ²)` on
  `ℂ ∖ (-∞, 1]` (`legFS_olverQ_eq_G`);
* at `z = cos θ ∓ i0`, `ζ → e^{±iθ}` (`legFS_zeta_lim`); the boundary values DLMF 14.23.2
  (`olverQ_boundary_aux`) then give the identity.

Also, for the continued fractions of DLMF §14.14:

* `legFS_tannery`: `Γ(c+k) 𝐅(a, b+k; c+k; z) → (1-z)^{-a}` as `k → ∞` for `|z| < 1`
  (dominated convergence termwise);
* `legFS_hasCF_of_terminating`, `legFS_hasCF_of_exists_zero`, `legFS_hasCF_of_ratio`: the value `a₀w₁/w₀` of the project's
  `HasContinuedFraction` from a backward solution `w`, in the terminating case and under a
  ratio limit `-w_k/(a_{k+1}w_{k+2}) → ρ`, `|ρ| > 1` (`GenContFract.pinch_cfConv_tendsto`).

Also DLMF 14.12.3 (`ferrersQ_complex_integral`), from the boundary values of DLMF 14.25.2 under
dominated convergence (helpers `legTr_`).

All other helper names carry the prefix `legFS_`.
-/

@[expose] public noncomputable section

open Complex Filter Set DLMF.Hypergeometric DLMF
open scoped Real Topology

namespace DLMF.Legendre

/-! The inverse Joukowski map `ζ(z) = z - √(z²-1)` and its properties are the `legInt_`
helpers of `DLMF.Legendre.IntegralRepresentations` (`legInt_root`, `legInt_zeta`, …,
`legInt_zeta_mem_slitPlane`). The names below are kept as aliases for downstream modules. -/

/-- The inverse Joukowski map `ζ = z - √(z²-1)`; an alias of `legInt_zeta`. -/
abbrev legFS_zeta (z : ℂ) : ℂ := legInt_zeta z

/-- `ζ ≠ 0` on `ℂ ∖ (-∞, 1]`; an alias of `legInt_zeta_ne_zero`. -/
theorem legFS_zeta_ne_zero {z : ℂ} (hz : z-1 ∈ slitPlane) : legFS_zeta z ≠ 0 :=
  legInt_zeta_ne_zero hz

/-- `|ζ| < 1` on `ℂ ∖ (-∞, 1]`; an alias of `legInt_norm_zeta_lt_one`. -/
theorem legFS_norm_zeta_lt_one {z : ℂ} (hz : z-1 ∈ slitPlane) : ‖legFS_zeta z‖ < 1 :=
  legInt_norm_zeta_lt_one hz

/-! The `ζ`-form `legFS_olverQ_eq_G` of `𝑸^μ_ν` is in `DLMF.Legendre.Continuation`. -/

/-- One-sided limit of `log(z-1)` at a point of `(-1, 1)` approached from the side `σ`. -/
theorem legFS_log_sub_one_lim {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : ℝ} (hx : x < 1) :
    Tendsto (fun ε : ℝ => log ((x:ℂ) + (σ:ℂ)*I*ε - 1)) (𝓝[>] (0:ℝ))
      (𝓝 ((Real.log (1-x) : ℂ) + σ*π*I)) := by
  have hpath : Tendsto (fun ε : ℝ => (x:ℂ) + (σ:ℂ)*I*ε - 1) (𝓝[>] (0:ℝ)) (𝓝 ((x - 1 : ℝ) : ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ) + (σ:ℂ)*I*ε - 1) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hre : ((x - 1 : ℝ) : ℂ).re < 0 := by simp; linarith
  have him : ((x - 1 : ℝ) : ℂ).im = 0 := by simp
  have hnorm : Real.log ‖((x - 1 : ℝ) : ℂ)‖ = Real.log (1-x) := by
    rw [norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; ring_nf
  have himε : ∀ ε : ℝ, ((x:ℂ) + (σ:ℂ)*I*ε - 1).im = σ*ε := by intro ε; simp
  rcases hσ with rfl | rfl
  · have hc := continuousWithinAt_log_of_re_neg_of_im_zero hre him
    have hp' : Tendsto (fun ε : ℝ => (x:ℂ) + ((1:ℝ):ℂ)*I*ε - 1) (𝓝[>] (0:ℝ))
        (𝓝[{z : ℂ | 0 ≤ z.im}] ((x - 1 : ℝ) : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hpath, by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        show 0 ≤ _; rw [himε]; simp only [one_mul]; exact le_of_lt hε⟩
    have h := hc.tendsto.comp hp'
    have e : (Real.log (1-x) : ℂ) + ((1:ℝ):ℂ)*π*I = log ((x - 1 : ℝ) : ℂ) := by
      rw [log, hnorm, arg_ofReal_of_neg (by linarith)]; push_cast; ring
    rw [e]; exact h
  · have hc := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him
    have hp' : Tendsto (fun ε : ℝ => (x:ℂ) + ((-1:ℝ):ℂ)*I*ε - 1) (𝓝[>] (0:ℝ))
        (𝓝[{z : ℂ | z.im < 0}] ((x - 1 : ℝ) : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hpath, by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        show _ < 0; rw [himε]; have : (0:ℝ) < ε := hε; linarith⟩
    have h := hc.comp hp'
    rw [hnorm] at h
    have e : (Real.log (1-x) : ℂ) + ((-1:ℝ):ℂ)*π*I = (Real.log (1-x) : ℂ) - π*I := by push_cast; ring
    rw [e]; exact h


/-- One-sided boundary values of `ζ = z - √(z²-1)` on `(-1, 1)`: from the side `σ`,
`ζ(cos θ + σ i 0) = cos θ - σ i sin θ`. -/
theorem legFS_zeta_lim {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    Tendsto (fun ε : ℝ => legInt_zeta ((Real.cos θ:ℂ) + (σ:ℂ)*I*ε)) (𝓝[>] (0:ℝ))
      (𝓝 ((Real.cos θ:ℂ) - (σ:ℂ)*I*(Real.sin θ:ℂ))) := by
  set x := Real.cos θ with hxdef
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hx1 : x < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ.le h0; rw [Real.cos_zero] at this
    exact this
  have hx2 : -1 < x := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ; rw [Real.cos_pi] at this
    exact this
  have hpath : Tendsto (fun ε : ℝ => (x:ℂ) + (σ:ℂ)*I*ε) (𝓝[>] (0:ℝ)) (𝓝 (x : ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ) + (σ:ℂ)*I*ε) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hL1 := legFS_log_sub_one_lim hσ hx1
  have hL2 : Tendsto (fun ε : ℝ => log ((x:ℂ) + (σ:ℂ)*I*ε + 1)) (𝓝[>] (0:ℝ))
      (𝓝 ((Real.log (1+x) : ℂ))) := by
    have hm : ((x:ℂ) + 1) ∈ slitPlane := Or.inl (by simp; linarith)
    have hc := (continuousAt_clog hm).tendsto.comp (hpath.add_const 1)
    rw [show ((x:ℂ) + 1) = ((1 + x : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by linarith)] at hc
    exact hc
  have hR := ((hL1.add hL2).div_const 2).cexp
  have hlim : exp (((Real.log (1-x) : ℂ) + σ*π*I + (Real.log (1+x) : ℂ))/2) =
      (σ:ℂ)*I*(Real.sin θ:ℂ) := by
    have hsq : Real.sin θ = Real.sqrt (1 - x^2) := by
      rw [hxdef, Real.sin_eq_sqrt_one_sub_cos_sq h0.le hπ.le]
    have hl : (Real.log (1-x) : ℂ) + (Real.log (1+x) : ℂ) = ((Real.log (1 - x^2) : ℝ) : ℂ) := by
      rw [← ofReal_add, ← Real.log_mul (by linarith) (by linarith)]; congr 2; ring
    rw [show ((Real.log (1-x) : ℂ) + σ*π*I + (Real.log (1+x) : ℂ))/2 =
      ((Real.log (1-x) : ℂ) + (Real.log (1+x) : ℂ))/2 + σ*π/2*I by ring, hl, exp_add,
      show ((Real.log (1 - x^2) : ℝ) : ℂ)/2 = ((Real.log (1 - x^2)/2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_exp, hsq, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by nlinarith)]
    rw [show Real.log (1 - x^2) * (1/2) = Real.log (1 - x^2)/2 by ring]
    rcases hσ with rfl | rfl
    · push_cast; rw [show (1:ℂ)*π/2*I = (π/2:ℂ)*I by ring, exp_mul_I, cos_pi_div_two, sin_pi_div_two]
      ring
    · push_cast; rw [show (-1:ℂ)*π/2*I = (-(π/2):ℂ)*I by ring, exp_mul_I, cos_neg, sin_neg,
        cos_pi_div_two, sin_pi_div_two]
      ring
  rw [hlim] at hR
  have := hpath.sub hR
  refine this.congr' (Eventually.of_forall fun ε => ?_)
  simp only [legInt_zeta, legInt_root]



/-- `cos θ + s i sin θ = e^{isθ}` for `s = ±1`. -/
theorem legFS_side_exp {s : ℝ} (hs : s = 1 ∨ s = -1) (θ : ℝ) :
    (Real.cos θ:ℂ) - ((-s:ℝ):ℂ)*I*(Real.sin θ:ℂ) = exp ((s:ℂ)*θ*I) := by
  rcases hs with rfl | rfl
  · rw [show ((1:ℝ):ℂ)*θ*I = (θ:ℂ)*I by push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    push_cast; ring
  · rw [show ((-1:ℝ):ℂ)*θ*I = (-(θ:ℂ))*I by push_cast; ring, exp_mul_I, cos_neg, sin_neg,
      ← ofReal_cos, ← ofReal_sin]
    push_cast; ring

/-- `1 - e^{2isθ} = 2 sin θ · e^{is(θ - π/2)}` for `s = ±1`. -/
theorem legFS_one_sub_exp_sq {s : ℝ} (hs : s = 1 ∨ s = -1) (θ : ℝ) :
    1 - exp ((s:ℂ)*θ*I)^2 = ((2*Real.sin θ : ℝ) : ℂ) * exp (((s*(θ - π/2) : ℝ) : ℂ)*I) := by
  have hu : exp ((θ:ℂ)*I) ≠ 0 := exp_ne_zero _
  have hsin : Complex.sin (θ:ℂ) = (exp (-(θ:ℂ)*I) - exp ((θ:ℂ)*I))*I/2 := by
    rw [Complex.sin]
  have hneg : exp (-(θ:ℂ)*I) = (exp ((θ:ℂ)*I))⁻¹ := by rw [neg_mul, exp_neg]
  have hpi : exp ((π/2:ℂ)*I) = I := by rw [exp_mul_I, cos_pi_div_two, sin_pi_div_two]; ring
  have hpi' : exp (-(π/2:ℂ)*I) = -I := by
    rw [neg_mul, exp_neg, hpi, inv_I]
  rcases hs with rfl | rfl
  · rw [show (((1:ℝ)*(θ - π/2) : ℝ) : ℂ)*I = (θ:ℂ)*I + (-(π/2:ℂ)*I) by push_cast; ring, exp_add,
      hpi', show ((1:ℝ):ℂ)*θ*I = (θ:ℂ)*I by push_cast; ring]
    push_cast; rw [hsin, hneg]; field_simp; ring_nf; rw [I_sq]; ring
  · rw [show (((-1:ℝ)*(θ - π/2) : ℝ) : ℂ)*I = -(θ:ℂ)*I + ((π/2:ℂ)*I) by push_cast; ring, exp_add,
      hpi, show ((-1:ℝ):ℂ)*θ*I = -(θ:ℂ)*I by push_cast; ring]
    push_cast; rw [hsin, hneg]; field_simp; ring_nf; rw [I_sq]; ring



/-- DLMF 14.13 (unnumbered) for real side `s = ±1`:
`s(πi/2) 𝖯^μ_ν(cos θ) + 𝖰^μ_ν(cos θ) = √π Γ(ν+μ+1) (2 sin θ)^μ e^{s(ν+μ+1)iθ} 𝐅(ν+μ+1, μ+1/2; ν+3/2; e^{2isθ})`. -/
theorem legFS_PQ_hyp (ν μ : ℂ) (hr : LegendreQRegular ν μ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    (s:ℂ)*π*I/2*ferrersP ν μ (Real.cos θ) + ferrersQ ν μ (Real.cos θ) =
      Real.sqrt π*Gamma (ν+μ+1)*(2*Real.sin θ:ℂ)^μ*exp ((s:ℂ)*(ν+μ+1)*I*θ)*
        regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp ((s:ℂ)*2*I*θ)) := by
  have hσ : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hx : Real.cos θ ∈ Ioo (-1:ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have := Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ; rwa [Real.cos_pi] at this
    · have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ.le h0; rwa [Real.cos_zero] at this
  set w₀ := exp ((s:ℂ)*θ*I) with hw₀
  have hθs : -π < s*θ ∧ s*θ < π := by
    rcases hs with rfl | rfl <;> constructor <;> linarith
  have hw0 : w₀ ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right
    rw [hw₀, show (s:ℂ)*θ*I = ((s*θ:ℝ):ℂ)*I by push_cast; ring, exp_mul_I, ← ofReal_cos,
      ← ofReal_sin]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im, mul_one, zero_add]
    rcases hs with rfl | rfl
    · simpa using hsin.ne'
    · simpa using hsin.ne'
  have hφ : -(π/2) < s*(θ - π/2) ∧ s*(θ - π/2) < π/2 := by
    rcases hs with rfl | rfl <;> constructor <;> linarith
  have hsq : 1 - w₀^2 = ((2*Real.sin θ : ℝ) : ℂ) * exp (((s*(θ - π/2) : ℝ) : ℂ)*I) :=
    legFS_one_sub_exp_sq hs θ
  have hw2 : 1 - w₀^2 ∈ slitPlane := by
    rw [hsq, mem_slitPlane_iff]; left
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    simp only [mul_re, ofReal_re, ofReal_im, add_re, I_re, I_im, zero_mul, mul_zero,
      sub_zero, add_zero, mul_one]
    have := Real.cos_pos_of_mem_Ioo ⟨hφ.1, hφ.2⟩
    simp; positivity
  -- the boundary value of `𝑸^μ_ν` from the side `-s`
  have hlimQ := olverQ_boundary_aux ν μ hr (-s) hσ hx
  have hζ := legFS_zeta_lim hσ h0 hπ
  rw [legFS_side_exp hs] at hζ
  have hG := (legFS_G_analyticAt ν μ hw0 hw2).continuousAt.tendsto.comp hζ
  have heq : (fun ε : ℝ => olverQ ν μ ((Real.cos θ:ℂ) + ((-s:ℝ):ℂ)*I*ε)) =ᶠ[𝓝[>] (0:ℝ)]
      (legFS_G ν μ ∘ fun ε : ℝ => legInt_zeta ((Real.cos θ:ℂ) + ((-s:ℝ):ℂ)*I*ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0:ℝ) < ε := hε
    refine legFS_olverQ_eq_G ν μ ?_
    rw [mem_slitPlane_iff]; right
    simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im, mul_one,
      zero_add, one_im, sub_zero, ofReal_neg, neg_re, neg_im, add_zero, neg_zero]
    rcases hs with rfl | rfl <;> simp <;> exact hε'.ne'
  have huniq := tendsto_nhds_unique hlimQ (hG.congr' heq.symm)
  have hΓ : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero (fun n he => hr n (by linear_combination he))
  have hE : exp (((-s:ℝ):ℂ)*μ*π*I/2) * exp ((s:ℂ)*μ*π*I/2) = 1 := by
    rw [← exp_add, show ((-s:ℝ):ℂ)*μ*π*I/2 + (s:ℂ)*μ*π*I/2 = 0 by push_cast; ring, exp_zero]
  have key : (s:ℂ)*π*I/2*ferrersP ν μ (Real.cos θ) + ferrersQ ν μ (Real.cos θ) =
      Gamma (ν+μ+1) * exp ((s:ℂ)*μ*π*I/2) * legFS_G ν μ w₀ := by
    rw [← huniq]
    have e : ∀ A B C D X : ℂ, C * B * (A / D * X) = (A*B) * (C/D) * X := by intros; ring
    rw [e, hE, div_self hΓ]; push_cast; ring
  have hr0 : (0:ℝ) < 2*Real.sin θ := by positivity
  have hpow1 : (1 - w₀^2)^μ = (2*Real.sin θ:ℂ)^μ * exp ((((s*(θ - π/2) : ℝ) : ℂ)*I)*μ) := by
    rw [hsq, cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hr0.ne') (exp_ne_zero _)),
      log_ofReal_mul hr0 (exp_ne_zero _), log_exp (by simp; linarith [hφ.1, Real.pi_pos])
        (by simp; linarith [hφ.2, Real.pi_pos]),
      show (2*Real.sin θ:ℂ) = ((2*Real.sin θ : ℝ) : ℂ) by push_cast; ring,
      cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr0.ne'), ← ofReal_log hr0.le, ← exp_add]
    congr 1; ring
  have hpow2 : w₀^(ν+1) = exp ((s:ℂ)*θ*I*(ν+1)) := by
    rw [hw₀, cpow_def_of_ne_zero (exp_ne_zero _), log_exp]
    · rw [show (s:ℂ)*θ*I = ((s*θ:ℝ):ℂ)*I by push_cast; ring]; simp; linarith [hθs.1]
    · rw [show (s:ℂ)*θ*I = ((s*θ:ℝ):ℂ)*I by push_cast; ring]; simp; linarith [hθs.2]
  have hsq2 : w₀^2 = exp ((s:ℂ)*2*I*θ) := by
    rw [hw₀, ← exp_nat_mul]; congr 1; push_cast; ring
  rw [key, legFS_G, hpow1, hpow2, regularizedGaussHG_symm _ _ _ (show w₀^2 ∈ cutPlane from hw2),
    hsq2]
  have hx : exp ((s:ℂ)*μ*π*I/2) * exp ((((s*(θ - π/2) : ℝ) : ℂ)*I)*μ) * exp ((s:ℂ)*θ*I*(ν+1)) =
      exp ((s:ℂ)*(ν+μ+1)*I*θ) := by
    rw [← exp_add, ← exp_add]; congr 1; push_cast; ring
  linear_combination (Gamma (ν+μ+1) * Real.sqrt π * (2*Real.sin θ:ℂ)^μ *
    regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp ((s:ℂ)*2*I*θ))) * hx


/-! ### A Tannery limit for `𝐅(a, b+k; c+k; z)` -/

/-- The ratio `(b+k)_n Γ(c+k)/Γ(c+k+n)` appearing in `Γ(c+k) 𝐅(a, b+k; c+k; z)`. -/
def legFS_q (b c : ℂ) (k n : ℕ) : ℂ := poch (b+k) n * Gamma (c+k) / Gamma (c+k+n)

/-- For `Re (c+k) > 0`, the recursion `q_{n+1} = q_n (b+k+n)/(c+k+n)`. -/
theorem legFS_q_succ (b c : ℂ) {k : ℕ} (hk : 0 < (c+k).re) (n : ℕ) :
    legFS_q b c k (n+1) = legFS_q b c k n * ((b+k+n)/(c+k+n)) := by
  have hre : 0 < (c+k+n).re := by simp at hk ⊢; positivity
  have h1 : c+k+n ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hG : Gamma (c+k+n) ≠ 0 := Gamma_ne_zero_of_re_pos hre
  have e : Gamma (c+k+((n+1:ℕ):ℂ)) = (c+k+n) * Gamma (c+k+n) := by
    rw [show c+k+((n+1:ℕ):ℂ) = (c+k+n)+1 by push_cast; ring, Gamma_add_one _ h1]
  simp only [legFS_q, poch, ascPochhammer_succ_eval, e]
  field_simp

/-- For `Re (c+k) > 0`, `q_0 = 1`. -/
theorem legFS_q_zero (b c : ℂ) {k : ℕ} (hk : 0 < (c+k).re) : legFS_q b c k 0 = 1 := by
  simp [legFS_q, poch, Gamma_ne_zero_of_re_pos hk]

/-- `(k+β)/(k+γ) → 1`. -/
theorem legFS_ratio_tendsto (β γ : ℂ) :
    Tendsto (fun k : ℕ => ((k:ℂ)+β)/((k:ℂ)+γ)) atTop (𝓝 1) := by
  have h0 : Tendsto (fun k : ℕ => ((k:ℂ))⁻¹) atTop (𝓝 0) := 
    tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)
  have h : Tendsto (fun k : ℕ => (1 + β*(k:ℂ)⁻¹)/(1 + γ*(k:ℂ)⁻¹)) atTop (𝓝 ((1 + β*0)/(1+γ*0))) :=
    ((tendsto_const_nhds.add (h0.const_mul β)).div (tendsto_const_nhds.add (h0.const_mul γ))
      (by simp))
  simp only [mul_zero, add_zero, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- Per-term limit: `q_k(n) → 1` as `k → ∞`. -/
theorem legFS_q_tendsto (b c : ℂ) (n : ℕ) : Tendsto (fun k => legFS_q b c k n) atTop (𝓝 1) := by
  have hev : ∀ᶠ k : ℕ in atTop, 0 < (c+k).re := by
    obtain ⟨K, hK⟩ := exists_nat_gt (-c.re)
    filter_upwards [eventually_ge_atTop K] with k hk
    have : (K:ℝ) ≤ k := by exact_mod_cast hk
    simp; linarith
  induction n with
  | zero =>
    exact tendsto_const_nhds.congr' (by filter_upwards [hev] with k hk; rw [legFS_q_zero b c hk])
  | succ n ih =>
    have hr : Tendsto (fun k : ℕ => (b+k+n)/(c+k+n)) atTop (𝓝 1) :=
      (legFS_ratio_tendsto (b+n) (c+n)).congr fun k => by ring_nf
    have := ih.mul hr
    rw [one_mul] at this
    exact this.congr' (by filter_upwards [hev] with k hk; rw [legFS_q_succ b c hk])

/-- Uniform bound: `‖q_k(n)‖ ≤ (1+ε)^n` for `k` large. -/
theorem legFS_q_bound (b c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ n, ‖legFS_q b c k n‖ ≤ (1+ε)^n := by
  obtain ⟨K, hK⟩ := exists_nat_gt (‖b-c‖/ε - c.re + 1)
  filter_upwards [eventually_ge_atTop K] with k hk n
  have hkK : (K:ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (c+k).re := by
    simp; have := div_nonneg (norm_nonneg (b-c)) hε.le; linarith
  induction n with
  | zero => rw [legFS_q_zero b c hpos]; simp
  | succ n ih =>
    rw [legFS_q_succ b c hpos, norm_mul, pow_succ]
    refine mul_le_mul ih ?_ (norm_nonneg _) (by positivity)
    have hre : ‖b-c‖/ε < (c+k+n).re := by
      simp; have : (0:ℝ) ≤ n := n.cast_nonneg; linarith
    have hn0 : 0 < ‖c+k+n‖ := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) hre) (re_le_norm _)
    rw [show b+k+n = (c+k+n) + (b-c) by ring, add_div, div_self (norm_pos_iff.mp hn0),
      ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_div]
    gcongr
    rw [div_le_iff₀ hn0]
    have := (div_lt_iff₀ hε).mp hre
    nlinarith [re_le_norm (c+k+n)]

/-- **Tannery limit.** For `‖z‖ < 1`, `Γ(c+k) 𝐅(a, b+k; c+k; z) → (1-z)^{-a}` as `k → ∞`. -/
theorem legFS_tannery (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun k : ℕ => Gamma (c+k) * regularizedGaussHGFun a (b+k) (c+k) z) atTop
      (𝓝 ((1-z)^(-a))) := by
  set ε : ℝ := (1 - ‖z‖)/2
  have hε : 0 < ε := by simp only [ε]; linarith
  set r : ℝ := (1+ε)*‖z‖
  have hr0 : 0 ≤ r := by positivity
  have hr1 : ‖(r:ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr0]
    simp only [r, ε]; nlinarith [norm_nonneg z]
  have hS := (hasSum_one_sub_cpow_neg (‖a‖:ℂ) hr1).summable.norm
  have hlim := hasSum_one_sub_cpow_neg a hz
  rw [← hlim.tsum_eq]
  have key : ∀ k : ℕ, Gamma (c+k) * regularizedGaussHGFun a (b+k) (c+k) z =
      ∑' n : ℕ, poch a n / n.factorial * z^n * legFS_q b c k n := by
    intro k
    rw [regularizedGaussHGFun_eq_tsum, ← tsum_mul_left]
    congr 1; funext n
    simp only [legFS_q, poch]; ring
  simp only [key]
  refine tendsto_tsum_of_dominated_convergence hS (fun n => ?_) ?_
  · have := (legFS_q_tendsto b c n).const_mul (poch a n / n.factorial * z^n)
    rwa [mul_one] at this
  · filter_upwards [legFS_q_bound b c hε] with k hk n
    rw [norm_mul, norm_mul, norm_mul, norm_div, norm_div, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hr0, show r^n = (1+ε)^n * ‖z‖^n from mul_pow _ _ _]
    have h1 := DLMF.OrthogonalPolynomials.norm_poch_le_norm_poch_norm a n
    have h2 := hk n
    have : 0 ≤ ‖z‖^n := by positivity
    have : 0 ≤ ‖((n.factorial : ℕ) : ℂ)‖ := norm_nonneg _
    calc ‖poch a n‖ / ‖((n.factorial : ℕ) : ℂ)‖ * ‖z‖^n * ‖legFS_q b c k n‖
        ≤ ‖poch (‖a‖:ℂ) n‖ / ‖((n.factorial : ℕ) : ℂ)‖ * ‖z‖^n * (1+ε)^n := by gcongr
      _ = _ := by ring

/-! ### Terminating and Pincherle-type continued fractions -/

/-- Up to the first vanishing partial numerator `a_K`, the project's continuants are Mathlib's. -/
theorem legFS_cfContinuants_eq {a b : ℕ → ℂ} {K : ℕ} (ha : ∀ k, 1 ≤ k → k < K → a k ≠ 0)
    (n : ℕ) (hn : n ≤ K) :
    DLMF.cfContinuants a b 0 n =
      ((GenContFract.cfConv_ofFun 0 a b).nums n, (GenContFract.cfConv_ofFun 0 a b).dens n, false) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [DLMF.cfContinuants]; rfl
    · simp [DLMF.cfContinuants, GenContFract.cfConv_nums_one, GenContFract.cfConv_dens_one]
    · have h1 := ih (n + 1) (by omega) (by omega)
      have h0 := ih n (by omega) (by omega)
      have han : a (n + 1) ≠ 0 := ha (n + 1) (by omega) (by omega)
      rw [DLMF.cfContinuants, h1, h0, GenContFract.cfConv_nums_step, GenContFract.cfConv_dens_step]
      simp [han, GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen]

/-- After the first vanishing partial numerator `a_K` (`K ≥ 1`) the project's finite continued
fraction freezes at the `K`-th Mathlib convergent. -/
theorem legFS_cfTail_freeze {a b : ℕ → ℂ} {K : ℕ} (hK : 1 ≤ K)
    (ha : ∀ k, 1 ≤ k → k < K → a k ≠ 0) (haK : a K = 0) {N : ℕ} (hN : K ≤ N) :
    DLMF.cfTail a b 0 N = (GenContFract.cfConv_ofFun 0 a b).convs K := by
  have hfr : ∀ j, DLMF.cfContinuants a b 0 (K + 1 + j) =
      ((GenContFract.cfConv_ofFun 0 a b).nums K, (GenContFract.cfConv_ofFun 0 a b).dens K, true) := by
    intro j
    induction j with
    | zero =>
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      rw [show m + 1 + 1 + 0 = m + 2 by ring, DLMF.cfContinuants,
        legFS_cfContinuants_eq ha (m + 1) le_rfl]
      simp [haK]
    | succ j ih =>
      rw [show K + 1 + (j + 1) = (K + j) + 2 by ring, DLMF.cfContinuants,
        show K + j + 1 = K + 1 + j by ring, ih]
      simp
  rcases hN.eq_or_lt with rfl | hlt
  · simp only [DLMF.cfTail, legFS_cfContinuants_eq ha K le_rfl]; rfl
  · obtain ⟨j, rfl⟩ : ∃ j, N = K + 1 + j := ⟨N - K - 1, by omega⟩
    simp only [DLMF.cfTail, hfr]; rfl

/-- A terminating continued fraction (first vanishing numerator `a_K`, `K ≥ 1`) with a backward
solution `w`, `w₀ ≠ 0`, has the value `a₀ w₁/w₀`. -/
theorem legFS_hasCF_of_terminating {a b w : ℕ → ℂ} {K : ℕ} (hK : 1 ≤ K)
    (ha : ∀ k, 1 ≤ k → k < K → a k ≠ 0) (haK : a K = 0)
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (hw0 : w 0 ≠ 0) :
    DLMF.HasContinuedFraction a b (a 0 * w 1 / w 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  obtain ⟨e1, e2⟩ := GenContFract.cfConv_invariant (h := (0:ℂ)) hw m
  rw [haK, zero_mul, zero_mul, add_zero] at e1 e2
  have hwK : w (m + 1) ≠ 0 := fun h => hw0 (by rw [← e2, h, mul_zero])
  have hB : (GenContFract.cfConv_ofFun 0 a b).dens (m + 1) ≠ 0 :=
    fun h => hw0 (by rw [← e2, h, zero_mul])
  have hval : (GenContFract.cfConv_ofFun 0 a b).convs (m + 1) = a 0 * w 1 / w 0 := by
    change (GenContFract.cfConv_ofFun 0 a b).nums (m + 1) /
      (GenContFract.cfConv_ofFun 0 a b).dens (m + 1) = _
    rw [div_eq_div_iff hB hw0, ← e2]
    linear_combination (GenContFract.cfConv_ofFun 0 a b).dens (m + 1) * e1
  unfold DLMF.HasContinuedFraction
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (m + 1)] with N hN
  rw [legFS_cfTail_freeze hK ha haK hN, hval]

/-- With no vanishing partial numerator, Pincherle's criterion with a ratio limit gives the value
`a₀ w₁/w₀` of the project's continued fraction. -/
theorem legFS_hasCF_of_ratio {a b w : ℕ → ℂ} (ha : ∀ k, a k ≠ 0)
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (hw0 : w 0 ≠ 0)
    (hwev : ∀ᶠ k in atTop, w k ≠ 0) {ρ : ℂ} (hρ : 1 < ‖ρ‖)
    (hlim : Tendsto (fun k => -(w k / (a (k + 1) * w (k + 2)))) atTop (𝓝 ρ)) :
    DLMF.HasContinuedFraction a b (a 0 * w 1 / w 0) := by
  have h := GenContFract.pinch_cfConv_tendsto (h := (0:ℂ)) hw hw0 ha hwev hρ hlim
  rw [zero_add] at h
  unfold DLMF.HasContinuedFraction
  refine h.congr fun N => ?_
  have := legFS_cfContinuants_eq (b := b) (K := N) (fun k _ _ => ha k) N le_rfl
  simp only [DLMF.cfTail, this]; rfl

/-- If `a₀ = 0` every finite continued fraction has numerator `0`. -/
theorem legFS_cfContinuants_fst_zero {a b : ℕ → ℂ} (h0 : a 0 = 0) (n : ℕ) :
    (DLMF.cfContinuants a b 0 n).1 = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [DLMF.cfContinuants]
    · simp [DLMF.cfContinuants, h0]
    · have h1 := ih (n + 1) (by omega)
      have h2 := ih n (by omega)
      rw [DLMF.cfContinuants]
      split_ifs
      · exact h1
      · simp [GenContFract.nextConts, GenContFract.nextNum, h1, h2]

/-- A continued fraction with a vanishing partial numerator and a backward solution `w`,
`w₀ ≠ 0`, has the value `a₀ w₁/w₀`. -/
theorem legFS_hasCF_of_exists_zero {a b w : ℕ → ℂ} (hex : ∃ K, a K = 0)
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (hw0 : w 0 ≠ 0) :
    DLMF.HasContinuedFraction a b (a 0 * w 1 / w 0) := by
  classical
  have hK := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h] at hK
    rw [hK, zero_mul, zero_div]
    unfold DLMF.HasContinuedFraction
    refine tendsto_const_nhds.congr fun N => ?_
    simp only [DLMF.cfTail, legFS_cfContinuants_fst_zero hK, zero_div]
  · exact legFS_hasCF_of_terminating h (fun k _ hk => Nat.find_min hex hk) hK hw hw0


/-! ### DLMF 14.12.3 from the boundary values of DLMF 14.25.2 (prefix `legTr_`) -/

section FerrersQIntegral

open MeasureTheory

/-- The kernel of DLMF 14.25.2 is integrable on `(0, ∞)` (Euler substitution). -/
theorem legTr_integrableOn_kernel {ν μ : ℂ} (h0 : -1/2 < μ.re) (h1 : μ.re < (ν+1).re) {z : ℂ}
    (hz : z-1 ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (Real.sinh t:ℂ)^(2*μ)/(z+legInt_root z*Real.cosh t)^(ν+μ+1))
      (Ioi 0) := by
  have hx : (legInt_zeta z)^2 ∈ cutPlane := by
    refine mem_cutPlane_of_norm_lt_one ?_
    rw [norm_pow]; have := legInt_norm_zeta_lt_one hz; nlinarith [norm_nonneg (legInt_zeta z)]
  have hb : 0 < (μ+1/2).re := by simp; linarith
  have hcb : 0 < (ν+3/2-(μ+1/2)).re := by simp at h1 ⊢; linarith
  have hg := intervalIntegrable_eulerKernel (a := ν+μ+1) hb hcb hx
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo] at hg
  obtain ⟨hI, -⟩ := legInt_hs_cov hg
  refine IntegrableOn.congr_fun (hI.const_mul (2^(2*μ) * (legInt_zeta z)^(ν+μ+1))) ?_ measurableSet_Ioi
  intro t ht
  exact (legInt_kernel_Q (ν := ν) (μ := μ) hz ht).symm

/-- `√(z²-1)` at `z = 3`. -/
theorem legTr_root_three : legInt_root 3 = ((Real.sqrt 8 : ℝ) : ℂ) := by
  have h := legInt_zeta_real (t := 3) (by norm_num)
  have : legInt_root ((3:ℝ):ℂ) = ((3:ℝ):ℂ) - legInt_zeta ((3:ℝ):ℂ) := by rw [legInt_zeta]; ring
  rw [h] at this
  have e : ((3:ℝ):ℂ) = 3 := by norm_num
  rw [e] at this; rw [this]; norm_num


/-- `‖w^{-a}‖ ≤ e^{π|Im a|} ‖w‖^{-Re a}`. -/
theorem legTr_norm_recip_cpow_le {w a : ℂ} (hw : w ≠ 0) :
    ‖1/w^a‖ ≤ Real.exp (π*|a.im|) * ‖w‖^(-a.re) := by
  rw [norm_div, norm_one, norm_cpow_of_ne_zero hw, one_div_div, Real.rpow_neg (norm_nonneg _),
    div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
  calc arg w * a.im ≤ |arg w * a.im| := le_abs_self _
    _ = |arg w| * |a.im| := abs_mul _ _
    _ ≤ π*|a.im| := by gcongr; exact abs_arg_le_pi w

/-- The boundary integrand of DLMF 14.25.2 at `cos θ + σ i 0`. -/
noncomputable def legTr_sideKernel (ν μ : ℂ) (σ θ t : ℝ) : ℂ :=
  Real.sqrt π*exp (μ/2*((Real.log (1-Real.cos θ):ℂ)+σ*π*I+(Real.log (1+Real.cos θ):ℂ)))/
    (2^μ*Gamma (μ+1/2)*Gamma (ν-μ+1))*((Real.sinh t:ℂ)^(2*μ)/
      ((Real.cos θ:ℂ)+(σ:ℂ)*I*(Real.sin θ:ℂ)*Real.cosh t)^(ν+μ+1))

/-- DLMF 14.25.2 at `cos θ + σ i 0`, `σ = ±1`: the boundary integrand is integrable and its
integral is the one-sided limit of `𝑸^μ_ν` (dominated convergence). -/
theorem legTr_side {ν μ : ℂ} (hμ : -1/2 < μ.re) (ha : 0 < (ν+μ+1).re) (h1 : μ.re < (ν+1).re)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {θ : ℝ} (hθ : 0 < θ) (hπ : θ < π) :
    IntegrableOn (legTr_sideKernel ν μ σ θ) (Ioi 0) ∧
    Tendsto (fun ε : ℝ => olverQ ν μ ((Real.cos θ:ℂ)+(σ:ℂ)*I*ε)) (𝓝[>] (0:ℝ))
      (𝓝 (∫ t in Ioi 0, legTr_sideKernel ν μ σ θ t)) := by
  set x := Real.cos θ with hxdef
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hx1 : x < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ.le hθ; rw [Real.cos_zero] at this
    exact this
  have hx2 : -1 < x := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le le_rfl hπ; rw [Real.cos_pi] at this
    exact this
  have hσ2 : σ*σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set z : ℝ → ℂ := fun ε => (x:ℂ)+(σ:ℂ)*I*ε with hzdef
  have hpath : Tendsto z (𝓝[>] (0:ℝ)) (𝓝 (x : ℂ)) := by
    have : Continuous z := by fun_prop
    simpa [z] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hL1 := legFS_log_sub_one_lim hσ hx1
  have hL2 : Tendsto (fun ε : ℝ => log ((x:ℂ) + (σ:ℂ)*I*ε + 1)) (𝓝[>] (0:ℝ))
      (𝓝 ((Real.log (1+x) : ℂ))) := by
    have hm : ((x:ℂ) + 1) ∈ slitPlane := Or.inl (by simp; linarith)
    have hc := (continuousAt_clog hm).tendsto.comp (hpath.add_const 1)
    rw [show ((x:ℂ) + 1) = ((1 + x : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by linarith)] at hc
    exact hc
  set P : ℂ := exp (μ/2*((Real.log (1-x):ℂ)+σ*π*I+(Real.log (1+x):ℂ))) with hP
  have hbp : Tendsto (fun ε => legendreBranchPower μ (z ε)) (𝓝[>] (0:ℝ)) (𝓝 P) :=
    ((hL1.add hL2).const_mul (μ/2)).cexp
  have hroot : Tendsto (fun ε => legInt_root (z ε)) (𝓝[>] (0:ℝ))
      (𝓝 ((σ:ℂ)*I*(Real.sin θ:ℂ))) := by
    have := hpath.sub (legFS_zeta_lim hσ hθ hπ)
    rw [← hxdef, sub_sub_cancel] at this
    refine this.congr' (Eventually.of_forall fun ε => ?_)
    simp only [z, legInt_zeta]; ring
  have hE1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ‖legendreBranchPower μ (z ε)‖ < ‖P‖+1 :=
    hbp.norm.eventually (gt_mem_nhds (by linarith))
  have hE2 : ∀ᶠ ε in 𝓝[>] (0:ℝ), Real.sin θ/2 < σ*(legInt_root (z ε)).im := by
    have h := ((continuous_im.tendsto _).comp hroot).const_mul σ
    have e : σ * ((σ:ℂ)*I*(Real.sin θ:ℂ)).im = Real.sin θ := by
      simp [← mul_assoc, hσ2, sin_ofReal_re]
    rw [Function.comp_def, e] at h
    exact h.eventually (lt_mem_nhds (by linarith))
  set a := ν+μ+1 with ha_def
  set D : ℂ := 2^μ*Gamma (μ+1/2)*Gamma (ν-μ+1) with hD_def
  set c : ℂ := Real.sqrt π/D with hc
  set F : ℝ → ℝ → ℂ := fun ε t => Real.sqrt π*legendreBranchPower μ (z ε)/D*
    ((Real.sinh t:ℂ)^(2*μ)/(z ε+exp ((log (z ε-1)+log (z ε+1))/2)*Real.cosh t)^a) with hF
  set ρ := Real.sqrt 8 with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  set κ : ℝ := (Real.sin θ/2)/(3+ρ) with hκ
  have hκ0 : 0 < κ := by positivity
  set W3 : ℝ → ℝ := fun t => 3 + ρ*Real.cosh t with hW3
  have hW3pos : ∀ t, 0 < W3 t := fun t => by
    have := Real.cosh_pos t; simp only [W3]; positivity
  set B : ℝ → ℝ := fun t => ‖c‖*(‖P‖+1)*Real.exp (π*|a.im|)*κ^(-a.re)*
    (‖(Real.sinh t:ℂ)^(2*μ)‖*(W3 t)^(-a.re)) with hB
  have hK3 := legTr_integrableOn_kernel (ν:=ν) (μ:=μ) hμ h1 (z := 3) (Or.inl (by norm_num))
  have hBint : IntegrableOn B (Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.const_mul hK3.norm (‖c‖*(‖P‖+1)*Real.exp (π*|a.im|)*κ^(-a.re)))
      (fun t _ => ?_) measurableSet_Ioi
    simp only [B]
    congr 1
    rw [legTr_root_three, norm_div, show (3:ℂ) + ((ρ:ℝ):ℂ)*(Real.cosh t:ℂ) = ((W3 t:ℝ):ℂ) by
      simp only [W3]; push_cast; ring, norm_cpow_eq_rpow_re_of_pos (hW3pos t),
      Real.rpow_neg (hW3pos t).le, div_eq_mul_inv]
  have hbound_pt : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ∈ Ioi (0:ℝ), ‖F ε t‖ ≤ B t := by
    filter_upwards [hE1, hE2, self_mem_nhdsWithin] with ε e1 e2 e3
    intro t _
    have e3' : (0:ℝ) < ε := e3
    have hc1 : 1 ≤ Real.cosh t := Real.one_le_cosh t
    set w := z ε + legInt_root (z ε) * Real.cosh t with hw
    have hwim : w.im = σ*ε + (legInt_root (z ε)).im * Real.cosh t := by simp [w, z]
    have hIm : Real.sin θ/2 * Real.cosh t ≤ σ * w.im := by
      have e : σ * w.im = ε + (σ*(legInt_root (z ε)).im) * Real.cosh t := by
        rw [hwim]; linear_combination ε*hσ2
      rw [e]; nlinarith
    have hwn : Real.sin θ/2 * Real.cosh t ≤ ‖w‖ := by
      have h1' : σ * w.im ≤ |w.im| := by
        rcases hσ with rfl | rfl
        · simpa using le_abs_self w.im
        · simpa using neg_le_abs w.im
      linarith [abs_im_le_norm w]
    have hW : κ * W3 t ≤ ‖w‖ := by
      refine le_trans ?_ hwn
      simp only [κ, W3]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : 3 + ρ*Real.cosh t ≤ (3+ρ)*Real.cosh t := by nlinarith
      have hs2 : 0 ≤ Real.sin θ/2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hs2]
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hW; have := hW3pos t; nlinarith
    have e : F ε t = c*legendreBranchPower μ (z ε)*((Real.sinh t:ℂ)^(2*μ) * (1/w^a)) := by
      simp only [F, c, w, legInt_root]; ring
    rw [e, norm_mul, norm_mul, norm_mul]
    have hpow : ‖w‖^(-a.re) ≤ (κ * W3 t)^(-a.re) :=
      Real.rpow_le_rpow_of_nonpos (by have := hW3pos t; positivity) hW (by linarith)
    rw [Real.mul_rpow hκ0.le (hW3pos t).le] at hpow
    have hinv := legTr_norm_recip_cpow_le (a := a) hw0
    calc ‖c‖ * ‖legendreBranchPower μ (z ε)‖ * (‖(Real.sinh t:ℂ)^(2*μ)‖ * ‖1/w^a‖)
        ≤ ‖c‖ * (‖P‖+1) * (‖(Real.sinh t:ℂ)^(2*μ)‖ *
          (Real.exp (π*|a.im|) * (κ^(-a.re) * (W3 t)^(-a.re)))) := by
          gcongr
          exact hinv.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = B t := by simp only [B]; ring
  have hlim_pt : ∀ t : ℝ, Tendsto (fun ε => F ε t) (𝓝[>] (0:ℝ)) (𝓝 (legTr_sideKernel ν μ σ θ t)) := by
    intro t
    have hw : Tendsto (fun ε => z ε + legInt_root (z ε) * Real.cosh t) (𝓝[>] (0:ℝ))
        (𝓝 ((x:ℂ) + (σ:ℂ)*I*(Real.sin θ:ℂ)*Real.cosh t)) := hpath.add (hroot.mul_const _)
    have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hmem : (x:ℂ) + (σ:ℂ)*I*(Real.sin θ:ℂ)*Real.cosh t ∈ slitPlane := by
      refine mem_slitPlane_iff.mpr (Or.inr ?_)
      have : ((x:ℂ) + (σ:ℂ)*I*(Real.sin θ:ℂ)*Real.cosh t).im = σ*Real.sin θ*Real.cosh t := by
        simp [sin_ofReal_re, cosh_ofReal_re]
      rw [this]; have := Real.cosh_pos t; positivity
    have hpw := (continuousAt_cpow_const (b := a) hmem).tendsto.comp hw
    have hne : ((x:ℂ) + (σ:ℂ)*I*(Real.sin θ:ℂ)*Real.cosh t)^a ≠ 0 := by
      rw [cpow_def_of_ne_zero (slitPlane_ne_zero hmem)]; exact exp_ne_zero _
    have h := ((hbp.const_mul (Real.sqrt π:ℂ)).div_const D).mul
      ((tendsto_const_nhds (x := ((Real.sinh t:ℂ)^(2*μ)))).div hpw hne)
    exact h
  have hmeas' : ∀ ε, AEStronglyMeasurable (F ε) (volume.restrict (Ioi 0)) :=
    fun ε => by
      have : Measurable (F ε) := by simp only [F]; fun_prop
      exact this.aestronglyMeasurable
  have hmeas : ∀ᶠ ε in 𝓝[>] (0:ℝ), AEStronglyMeasurable (F ε) (volume.restrict (Ioi 0)) :=
    Eventually.of_forall hmeas'
  have hbound : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), ‖F ε t‖ ≤ B t :=
    hbound_pt.mono fun ε h => (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall h)
  have hDCT := tendsto_integral_filter_of_dominated_convergence B hmeas hbound hBint
    (Eventually.of_forall hlim_pt)
  have hval : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∫ t in Ioi 0, F ε t = olverQ ν μ ((Real.cos θ:ℂ)+(σ:ℂ)*I*ε) := by
    filter_upwards [hbound, self_mem_nhdsWithin] with ε hb e3
    have hint : IntegrableOn (F ε) (Ioi 0) :=
      Integrable.mono' hBint (hmeas' ε) hb
    have e3' : (0:ℝ) < ε := e3
    have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hzs : z ε - 1 ∈ slitPlane := by
      refine mem_slitPlane_iff.mpr (Or.inr ?_)
      simp [z]; exact ⟨hσ0, e3'.ne'⟩
    exact tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id)
      (olverQ_complex_integral hμ h1 hzs)
  refine ⟨?_, hDCT.congr' hval⟩
  refine Integrable.mono' hBint ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => le_of_tendsto (hlim_pt t).norm
      (hbound_pt.mono fun ε h => h t ht)))
  have : Measurable (legTr_sideKernel ν μ σ θ) := by unfold legTr_sideKernel; fun_prop
  exact this.aestronglyMeasurable

/-- `exp(μ/2 (ln(1-cos θ) + σπi + ln(1+cos θ))) = e^{σμπi/2} sin^μ θ`. -/
theorem legTr_side_exp (μ : ℂ) {σ : ℝ} {θ : ℝ} (hθ : 0 < θ) (hπ : θ < π) :
    exp (μ/2*((Real.log (1-Real.cos θ):ℂ)+σ*π*I+(Real.log (1+Real.cos θ):ℂ))) =
      exp (σ*μ*π*I/2)*(Real.sin θ:ℂ)^μ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hc1 : Real.cos θ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ.le hθ; rwa [Real.cos_zero] at this
  have hc2 : -1 < Real.cos θ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le le_rfl hπ; rwa [Real.cos_pi] at this
  have hl : Real.log (1-Real.cos θ) + Real.log (1+Real.cos θ) = 2*Real.log (Real.sin θ) := by
    rw [← Real.log_mul (by linarith) (by linarith),
      show (1-Real.cos θ)*(1+Real.cos θ) = Real.sin θ^2 by rw [Real.sin_sq]; ring, Real.log_pow]
    norm_num
  rw [cpow_def_of_ne_zero (by exact_mod_cast hs.ne'), ← ofReal_log hs.le, ← exp_add]
  congr 1
  have hl' : (Real.log (1-Real.cos θ):ℂ) + (Real.log (1+Real.cos θ):ℂ) = 2*(Real.log (Real.sin θ):ℂ) := by
    exact_mod_cast hl
  linear_combination μ/2*hl'

/-- ferrersQ complex integral.

Moved here from `DLMF.Legendre.IntegralRepresentations` (round 13): the proof takes the
boundary values of DLMF 14.25.2 at `cos θ ± i0` (`olverQ_boundary_upper`/`lower`) under
dominated convergence. -/
@[dlmf 14.12.E3]
theorem ferrersQ_complex_integral {ν μ : ℂ} (hμ : -1/2 < μ.re) (h0 : -1 < (ν+μ).re) (h1 : -1 < (ν-μ).re) {θ : ℝ} (hθ : 0 < θ) (hπ : θ < π) :
    HasIntegralAtTop (fun t : ℝ => Real.sqrt π*Gamma (ν+μ+1)*(Real.sin θ:ℂ)^μ/(2^(μ+1)*Gamma (μ+1/2)*Gamma (ν-μ+1))*(Real.sinh t:ℂ)^(2*μ)*(1/(Real.cos θ+I*Real.sin θ*Real.cosh t)^(ν+μ+1)+1/(Real.cos θ-I*Real.sin θ*Real.cosh t)^(ν+μ+1))) 0 (ferrersQ ν μ (Real.cos θ)) := by
  have ha : 0 < (ν+μ+1).re := by simp at h0 ⊢; linarith
  have h1' : μ.re < (ν+1).re := by simp at h1 ⊢; linarith
  obtain ⟨hIp, hTp⟩ := legTr_side hμ ha h1' (σ := 1) (Or.inl rfl) hθ hπ
  obtain ⟨hIm, hTm⟩ := legTr_side hμ ha h1' (σ := -1) (Or.inr rfl) hθ hπ
  have hx : Real.cos θ ∈ Ioo (-1:ℝ) 1 := by
    constructor
    · have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le le_rfl hπ; rwa [Real.cos_pi] at this
    · have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ.le hθ; rwa [Real.cos_zero] at this
  have hr : LegendreQRegular ν μ := fun n hn => by
    have := congrArg re hn; have h0' := h0; simp at this h0'; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hG : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero_of_re_pos ha
  rw [show ((1:ℝ):ℂ) = 1 from ofReal_one] at hTp
  rw [show ((-1:ℝ):ℂ) = -1 by push_cast; ring] at hTm
  have ep := tendsto_nhds_unique hTp (olverQ_boundary_upper ν μ hr hx)
  have em := tendsto_nhds_unique hTm (olverQ_boundary_lower ν μ hr hx)
  set E := exp (μ*π*I/2) with hE
  have hE0 : E ≠ 0 := exp_ne_zero _
  have e1 : exp ((1:ℂ)*μ*π*I/2) = E := by rw [hE]; ring_nf
  have e2 : exp ((-1:ℂ)*μ*π*I/2) = E⁻¹ := by rw [hE, ← exp_neg]; ring_nf
  have e3 : exp (-μ*π*I/2) = E⁻¹ := by rw [hE, ← exp_neg]; ring_nf
  have e1' : exp (((1:ℝ):ℂ)*μ*π*I/2) = E := by rw [ofReal_one]; exact e1
  have e2' : exp (((-1:ℝ):ℂ)*μ*π*I/2) = E⁻¹ := by rw [show ((-1:ℝ):ℂ) = -1 by push_cast; ring]; exact e2
  have h2 : (2:ℂ)^(μ+1) = 2^μ*2 := by rw [cpow_add _ _ two_ne_zero, cpow_one]
  have hfun : (fun t : ℝ => Real.sqrt π*Gamma (ν+μ+1)*(Real.sin θ:ℂ)^μ/(2^(μ+1)*Gamma (μ+1/2)*Gamma (ν-μ+1))*(Real.sinh t:ℂ)^(2*μ)*(1/(Real.cos θ+I*Real.sin θ*Real.cosh t)^(ν+μ+1)+1/(Real.cos θ-I*Real.sin θ*Real.cosh t)^(ν+μ+1))) =
      fun t => Gamma (ν+μ+1)/2*(E⁻¹*legTr_sideKernel ν μ 1 θ t + E*legTr_sideKernel ν μ (-1) θ t) := by
    funext t
    unfold legTr_sideKernel
    rw [legTr_side_exp μ hθ hπ, legTr_side_exp μ hθ hπ, e1', e2',
      show (Real.cos θ:ℂ)+((1:ℝ):ℂ)*I*(Real.sin θ:ℂ)*Real.cosh t = Real.cos θ+I*Real.sin θ*Real.cosh t by
        push_cast; ring,
      show (Real.cos θ:ℂ)+((-1:ℝ):ℂ)*I*(Real.sin θ:ℂ)*Real.cosh t = Real.cos θ-I*Real.sin θ*Real.cosh t by
        push_cast; ring, h2]
    field_simp
  rw [hfun]
  have hint : IntegrableOn (fun t => Gamma (ν+μ+1)/2*(E⁻¹*legTr_sideKernel ν μ 1 θ t +
      E*legTr_sideKernel ν μ (-1) θ t)) (Ioi 0) :=
    ((hIp.const_mul _).add (hIm.const_mul _)).const_mul _
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hv : ∫ t in Ioi 0, Gamma (ν+μ+1)/2*(E⁻¹*legTr_sideKernel ν μ 1 θ t +
      E*legTr_sideKernel ν μ (-1) θ t) = ferrersQ ν μ (Real.cos θ) := by
    rw [integral_const_mul, integral_add (hIp.const_mul _) (hIm.const_mul _), integral_const_mul,
      integral_const_mul, ep, em, e1, e2]
    field_simp
    ring
  rw [hv] at hlim
  exact hlim
end FerrersQIntegral

end DLMF.Legendre
