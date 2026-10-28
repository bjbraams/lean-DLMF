/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.BoundsAsymptotics.GaussianRemainders

/-!
# Asymptotic remainders for Fresnel functions

Asymptotic terms, Laplace representations and remainder bounds for the auxiliary Fresnel
functions.

Source references and common attribution are retained in
`DLMF.ErrorFunctions.BoundsAsymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat Interval

namespace DLMF.Confluent

/-- The n-th auxiliary Fresnel asymptotic term. -/
def fresnelAsymptoticTerm (aux : Bool) (n : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ)^n*poch (1/2) (2*n+if aux then 1 else 0)/(π*z*(π*z^2/2)^(2*n+if aux then 1 else 0))

/-- Finite Fresnel auxiliary remainder. -/
@[dlmf 7.12.E4, dlmf 7.12.E5]
def fresnelAsymptoticRemainder (aux : Bool) (N : ℕ) (z : ℂ) : ℂ :=
  (if aux then fresnelAuxGComplex z else fresnelAuxFComplex z)-∑ n ∈ Finset.range N, fresnelAsymptoticTerm aux n z

/-- `e^{ζ²} erfc ζ ~ π^{-1/2} ∑ (-1)^m (1/2)_m ζ^{-2m-1}` in the sector `|arg ζ| ≤ 3π/4 - δ`. -/
theorem exp_sq_mul_erfc_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/4) :
    HasAsymptoticExpansion (sector (3*π/4-δ)) (fun (n : ℕ) (z : ℂ) => z^(-(2*(n : ℂ)+1)))
      (fun n => (-1 : ℂ)^n*poch (1/2) n/Real.sqrt π) (fun z => exp (z^2) * erfc z) := by
  have h := (erfc_sector_asymptotic hδ hδ1).1.mul_left (fun z => exp (z^2))
  have hφ : (fun (n : ℕ) (z : ℂ) => exp (z^2) * (exp (-z^2) * z^(-(2*(n : ℂ)+1)))) =
      fun (n : ℕ) (z : ℂ) => z^(-(2*(n : ℂ)+1)) := by
    funext n z; rw [← mul_assoc, ← Complex.exp_add]; simp
  rw [hφ] at h
  simp only [smul_eq_mul] at h
  exact h

/-- `arg (z e^{iθ}) = arg z + θ` when `arg z + θ ∈ (-π, π]`. -/
theorem arg_mul_exp_ofReal_mul_I {z : ℂ} (hz : z ≠ 0) {θ : ℝ} (h1 : -π < arg z + θ)
    (h2 : arg z + θ ≤ π) : arg (z * exp (θ * I)) = arg z + θ := by
  have hlog : log (z * exp (θ * I)) = log z + θ * I := by
    have : z * exp (θ * I) = exp (log z + θ * I) := by rw [exp_add, exp_log hz]
    rw [this, log_exp] <;> simp [log_im] <;> linarith
  rw [← log_im, hlog]; simp [log_im]

/-- `1 - εi = √2 e^{-iεπ/4}` for `ε = ±1`. -/
theorem one_sub_mul_I_eq {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (1 - ε * I : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) * exp (((-ε * π / 4 : ℝ) : ℂ) * I) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext
  · rw [re_ofReal_mul, exp_ofReal_mul_I_re]
    rcases hε with rfl | rfl
    · simp only [sub_re, one_re, mul_re, ofReal_re, I_re, ofReal_im, I_im]
      rw [show -(1:ℝ) * π / 4 = -(π / 4) by ring, Real.cos_neg, Real.cos_pi_div_four]
      nlinarith
    · simp only [sub_re, one_re, mul_re, ofReal_re, I_re, ofReal_im, I_im]
      rw [show -(-1:ℝ) * π / 4 = π / 4 by ring, Real.cos_pi_div_four]
      nlinarith
  · rw [im_ofReal_mul, exp_ofReal_mul_I_im]
    rcases hε with rfl | rfl
    · simp only [sub_im, one_im, mul_im, ofReal_re, I_re, ofReal_im, I_im]
      rw [show -(1:ℝ) * π / 4 = -(π / 4) by ring, Real.sin_neg, Real.sin_pi_div_four]
      nlinarith
    · simp only [sub_im, one_im, mul_im, ofReal_re, I_re, ofReal_im, I_im]
      rw [show -(-1:ℝ) * π / 4 = π / 4 by ring, Real.sin_pi_div_four]
      nlinarith

/-- `ζ_ε(z) = (√π/2)(1 - εi) z` maps the sector `|arg z| ≤ π/2 - δ` into `|arg ζ| ≤ 3π/4 - δ`,
uniformly towards infinity. -/
theorem tendsto_fresnelZetaComplex_sector {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < π/2) :
    Tendsto (fresnelZetaComplex ε) (sector (π/2-δ)) (sector (3*π/4-δ)) := by
  set ρ : ℝ := Real.sqrt π / 2 * Real.sqrt 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  set θ : ℝ := -ε * π / 4 with hθ
  have hζ : ∀ z, fresnelZetaComplex ε z = (ρ : ℂ) * (z * exp (θ * I)) := by
    intro z
    rw [fresnelZetaComplex, one_sub_mul_I_eq hε, hρ, hθ]; push_cast; ring
  have hθa : |θ| = π / 4 := by
    rw [hθ]; rcases hε with rfl | rfl
    · rw [show -(1:ℝ) * π / 4 = -(π / 4) by ring, abs_neg, abs_of_pos (by positivity)]
    · rw [show -(-1:ℝ) * π / 4 = π / 4 by ring, abs_of_pos (by positivity)]
  unfold sector
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · have hn : (norm ∘ fresnelZetaComplex ε) = fun z => ρ * ‖z‖ := by
      funext z
      simp only [Function.comp, hζ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le,
        norm_exp_ofReal_mul_I, mul_one]
    rw [hn]
    exact (tendsto_comap.mono_left inf_le_left).const_mul_atTop hρ0
  · filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    obtain ⟨hz0, hza⟩ := hz
    have hza' := abs_le.mp hza
    have hθ' := abs_eq_abs.mp (hθa.trans (abs_of_pos (by positivity : (0:ℝ) < π / 4)).symm)
    have hb : |arg z + θ| ≤ 3 * π / 4 - δ := by
      rw [abs_le]; rcases hθ' with h | h <;> rw [h] <;> constructor <;> linarith
    have hb' := abs_le.mp hb
    refine ⟨?_, ?_⟩
    · rw [hζ]
      exact mul_ne_zero (ofReal_ne_zero.mpr hρ0.ne') (mul_ne_zero hz0 (exp_ne_zero _))
    · rw [hζ, arg_real_mul _ hρ0, arg_mul_exp_ofReal_mul_I hz0 (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])]
      exact hb

/-- Coefficient algebra for the Fresnel expansions: with `w² = -1` and `c = (√π/2)(1-w)`,
`(1+w)/2 · c^{-2m-1} · (-1)^m (1/2)_m/√π = (-1)^m (1/2)_m w^{m+1} (2/π)^m/π`. -/
theorem fresnel_coeff_algebra {w : ℂ} (hw : w ^ 2 = -1) (p : ℂ) (m : ℕ) :
    (1 + w) / 2 * ((((Real.sqrt π : ℂ) / 2 * (1 - w)) ^ (2 * m + 1))⁻¹ *
      ((-1 : ℂ) ^ m * p / Real.sqrt π)) =
      (-1 : ℂ) ^ m * p * w ^ (m + 1) * (2 / π) ^ m / π := by
  set c : ℂ := (Real.sqrt π : ℂ) / 2 * (1 - w) with hc
  have hsq : ((Real.sqrt π : ℝ) : ℂ) ^ 2 = π := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hs0 : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw1 : 1 - w ≠ 0 := fun h => by
    have : w = 1 := by linear_combination -h
    rw [this] at hw; norm_num at hw
  have hc0 : c ≠ 0 := mul_ne_zero (div_ne_zero hs0 two_ne_zero) hw1
  have hc2 : c ^ 2 = -(π * w / 2) := by
    rw [hc, mul_pow, div_pow, hsq]; linear_combination (π / 4 : ℂ) * hw
  have hinv : (c ^ 2)⁻¹ = 2 * w / π := by
    rw [hc2]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    calc (2 * w / π) * (-(π * w / 2)) = -(w ^ 2) * (π * (π : ℂ)⁻¹) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hπ, hw]; ring
  have hA : (1 + w) / 2 / (Real.sqrt π * c) = w / π := by
    rw [hc]
    field_simp
    rw [hsq]
    linear_combination (π : ℂ) * hw
  rw [pow_succ', pow_mul, mul_inv, ← inv_pow, hinv]
  calc (1 + w) / 2 * (c⁻¹ * (2 * w / π) ^ m * ((-1 : ℂ) ^ m * p / Real.sqrt π))
      = (1 + w) / 2 / (Real.sqrt π * c) * ((-1 : ℂ) ^ m * p * (2 * w / π) ^ m) := by
        field_simp
    _ = _ := by rw [hA, show 2 * w / (π : ℂ) = w * (2 / π) by ring, mul_pow, pow_succ]; ring

/-- Signed combination `g(z) + εi f(z)` in the sector `|arg z| ≤ π/2 - δ`. -/
lemma fresnelAux_signed_sector_asymptotic {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < π/2) :
    HasAsymptoticExpansion (sector (π/2-δ)) (fun n z => z^(-(2*(n : ℂ)+1)))
      (fun n => (-1 : ℂ)^n * poch (1/2) n * (ε*I)^(n+1) * (2/π)^n / π)
      (fun z => fresnelAuxGComplex z + ε*I*fresnelAuxFComplex z) := by
  have h1 := (exp_sq_mul_erfc_sector_asymptotic (δ := δ) hδ (by linarith)).comp_tendsto
    (tendsto_fresnelZetaComplex_sector hε hδ hδ1)
  have h2 := h1.smul_scale (ψ := fun (n : ℕ) (z : ℂ) => z^(-(2*(n : ℂ)+1)))
    (κ := fun n => (((Real.sqrt π : ℂ) / 2 * (1 - ε * I)) ^ (2 * n + 1))⁻¹)
    (fun n => Eventually.of_forall fun z => by
      simp only [fresnelZetaComplex]
      rw [show -(2*(n : ℂ)+1) = -(((2*n+1 : ℕ) : ℂ)) by push_cast; ring, cpow_neg, cpow_neg,
        cpow_natCast, cpow_natCast, mul_pow, mul_inv])
  have h3 := h2.const_smul ((1 + (ε : ℂ) * I) / 2)
  have hw : (ε * I : ℂ) ^ 2 = -1 := by
    rcases hε with rfl | rfl <;> simp
  have hcoef : (((1 + (ε : ℂ) * I) / 2) • fun n => (((Real.sqrt π : ℂ) / 2 * (1 - ε * I)) ^ (2 * n + 1))⁻¹ •
      ((-1 : ℂ)^n*poch (1/2) n/Real.sqrt π)) =
      fun n => (-1 : ℂ)^n * poch (1/2) n * (ε*I)^(n+1) * (2/π)^n / π := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul]
    exact fresnel_coeff_algebra hw _ n
  have hfun : (((1 + (ε : ℂ) * I) / 2) • ((fun z => exp (z^2) * erfc z) ∘ fresnelZetaComplex ε)) =
      fun z => fresnelAuxGComplex z + ε*I*fresnelAuxFComplex z := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp]
    rw [fresnelAux_signed_erfc z hε]; ring
  rw [hcoef, hfun] at h3
  exact h3

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (sector
(π/2-δ)) (fun n z => z^(-(4*(n : ℂ)+1))) (fun n => (-1 : ℂ)^n*poch (1/2)
(2*n+0)*(2/π)^(2*n+0)/π) fresnelAuxFComplex`. -/
@[dlmf 7.12.E2]
theorem fresnelAuxFComplex_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π/2) :
    HasAsymptoticExpansion (sector (π/2-δ)) (fun n z => z^(-(4*(n : ℂ)+1))) (fun n => (-1 : ℂ)^n*poch (1/2) (2*n+0)*(2/π)^(2*n+0)/π) fresnelAuxFComplex := by
  have hp := fresnelAux_signed_sector_asymptotic (Or.inl rfl) hδ hδ1
  have hm := fresnelAux_signed_sector_asymptotic (Or.inr rfl) hδ hδ1
  have h := (hp.sub hm).const_smul (1 / (2 * I))
  have hf : ((1 / (2 * I)) • ((fun z => fresnelAuxGComplex z + ((1:ℝ):ℂ)*I*fresnelAuxFComplex z) -
      (fun z => fresnelAuxGComplex z + ((-1:ℝ):ℂ)*I*fresnelAuxFComplex z))) = fresnelAuxFComplex := by
    funext z
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  rw [hf] at h
  have he := h.even (fun n => by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    push_cast
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul, pow_mul, mul_pow, mul_pow]
    simp [I_sq])
  refine (he.congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only
    congr 1; push_cast; ring
  · funext n
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_zero]
    have h1 : ((((1:ℝ):ℂ) * I))^(2*n+1) = (-1)^n * I := by rw [pow_succ, pow_mul]; simp
    have h2 : ((((-1:ℝ):ℂ) * I))^(2*n+1) = -((-1)^n * I) := by rw [pow_succ, pow_mul]; simp
    rw [h1, h2, pow_mul (-1:ℂ) 2 n]
    field_simp
    ring

/-- In the open sector `|arg z| < π/4`, `|im z| < re z`. -/
theorem abs_im_lt_re_of_abs_arg_lt {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) :
    |z.im| < z.re := by
  have hu := abs_lt.mp hz
  have h0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [← norm_mul_exp_arg_mul_I z, re_ofReal_mul, im_ofReal_mul, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im, abs_mul, abs_of_pos h0]
  refine mul_lt_mul_of_pos_left ?_ h0
  rcases le_total 0 (arg z) with h | h
  · rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith)),
      ← Real.cos_pi_div_two_sub]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two h (by linarith) (by linarith)
  · rw [abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith)),
      ← Real.sin_neg, ← Real.cos_neg (arg z), ← Real.cos_pi_div_two_sub]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

/-- `exp(ε π i/2) = ε i` for `ε = ±1`. -/
theorem exp_sign_mul_pi_div_two_mul_I' {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    exp (((ε * π / 2 : ℝ) : ℂ) * I) = ε * I := by
  rcases hε with rfl | rfl
  · push_cast; rw [show (1:ℂ) * π / 2 * I = π / 2 * I by ring, exp_pi_div_two_mul_I]; ring
  · push_cast; rw [show (-1:ℂ) * π / 2 * I = -π / 2 * I by ring, exp_neg_pi_div_two_mul_I]; ring

/-- **Laplace forms of `g ± i f`** (from DLMF 7.7.2 rotated by `±π/2`): for `z ≠ 0` with
`|arg z| < π/4` and `ε = ±1`,
`g(z) + εi f(z) = εi √2/(2π) ∫₀^∞ e^{-πz²r/2} r^{-1/2}/(1 + εir) dr`. -/
lemma fresnelAux_signed_laplace {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z : ℂ} (hz0 : z ≠ 0)
    (hz : |arg z| < π/4) :
    fresnelAuxGComplex z + ε*I*fresnelAuxFComplex z = ε*I*(Real.sqrt 2/(2*π)) *
      ∫ r in Ioi (0:ℝ), cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + ε*I*r)⁻¹) := by
  have hε2 : (ε : ℂ)^2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  set θ : ℝ := ε * π / 2 with hθ
  have hθa : |θ| < π := by
    rw [hθ]; rcases hε with rfl | rfl
    · rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos]
    · rw [show -(1:ℝ) * π / 2 = -(π / 2) by ring, abs_neg, abs_of_pos (by positivity)]
      linarith [Real.pi_pos]
  have he : exp (θ * I) = ε * I := exp_sign_mul_pi_div_two_mul_I' hε
  have h2 : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h20 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have hω : exp (((θ / 2 : ℝ) : ℂ) * I) = (1 + ε * I) / Real.sqrt 2 := by
    have h := one_sub_mul_I_eq (ε := -ε) (by rcases hε with rfl | rfl <;> norm_num)
    rw [eq_div_iff h20]
    push_cast at h ⊢
    rw [show (1:ℂ) - -(ε:ℂ) * I = 1 + ε * I by ring] at h
    rw [h, hθ]; push_cast; ring_nf
  set ζ := fresnelZetaComplex ε z with hζ
  have hζω : ζ * exp (((θ / 2 : ℝ) : ℂ) * I) = ((Real.sqrt π / Real.sqrt 2 : ℝ) : ℂ) * z := by
    have hprod : (1 - (ε:ℂ) * I) * (1 + ε * I) = 2 := by
      linear_combination (-(ε:ℂ)^2) * I_sq + hε2
    rw [hω, hζ, fresnelZetaComplex]
    push_cast
    calc (Real.sqrt π : ℂ) / 2 * (1 - ε * I) * z * ((1 + ε * I) / Real.sqrt 2)
        = (Real.sqrt π : ℂ) / 2 * z / Real.sqrt 2 * ((1 - ε * I) * (1 + ε * I)) := by ring
      _ = _ := by rw [hprod]; field_simp
  have hpos : 0 < Real.sqrt π / Real.sqrt 2 := by positivity
  have hcond : |(ζ * exp (((θ / 2 : ℝ) : ℂ) * I)).im| < (ζ * exp (((θ / 2 : ℝ) : ℂ) * I)).re := by
    rw [hζω, im_ofReal_mul, re_ofReal_mul, abs_mul, abs_of_pos hpos]
    exact mul_lt_mul_of_pos_left (abs_im_lt_re_of_abs_arg_lt hz0 hz) hpos
  have hrep := erfc_eq_integral_rotate_laplace hθa hcond
  have hs : ((Real.sqrt π : ℝ) : ℂ) ^ 2 = π := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hζ2 : ζ ^ 2 * exp (θ * I) = π * z ^ 2 / 2 := by
    rw [he, hζ, fresnelZetaComplex, mul_pow, mul_pow, div_pow, hs]
    have hq : (1 - (ε:ℂ) * I) ^ 2 * (ε * I) = 2 := by
      linear_combination ((-2)*((ε:ℂ)^2-1) - 2 + ε*I*((ε:ℂ)^2-1) + ε*I) * I_sq +
        (2 - (ε:ℂ)*I) * hε2
    linear_combination (π * z ^ 2 / 4 : ℂ) * hq
  have hθ1 : -π < θ := by linarith [(abs_lt.mp hθa).1]
  have hθ2 : θ ≤ π := (abs_lt.mp hθa).2.le
  have hpt : ∀ r ∈ Ioi (0:ℝ), cexp (-(ζ ^ 2 * exp (θ * I) * r)) *
      (((r : ℂ) * exp (θ * I)) ^ (-1/2 : ℂ) * (1 + (r : ℂ) * exp (θ * I))⁻¹) =
      exp (θ * I * (-1/2 : ℂ)) * (cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + ε*I*r)⁻¹)) := by
    intro r hr
    rw [hζ2, ofReal_mul_exp_cpow hr hθ1 hθ2, he]
    ring_nf
  have hsum := fresnelAux_signed_erfc z hε
  rw [← hζ] at hsum
  rw [hsum, hrep, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hex : exp (θ * I) * exp (θ * I * (-1/2 : ℂ)) = (1 + ε * I) / Real.sqrt 2 := by
    rw [← Complex.exp_add, ← hω]; congr 1; push_cast; ring
  have hsq : (1 + (ε:ℂ) * I) ^ 2 = 2 * (ε * I) := by
    linear_combination (ε:ℂ)^2 * I_sq - hε2
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  set J := ∫ r in Ioi (0:ℝ), cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + ε*I*r)⁻¹)
  calc (1 + (ε:ℂ) * I) / 2 * exp (ζ ^ 2) * (exp (-ζ ^ 2) / π *
        (exp (θ * I) * (exp (θ * I * (-1/2 : ℂ)) * J)))
      = (1 + (ε:ℂ) * I) / 2 * (exp (ζ ^ 2) * exp (-ζ ^ 2)) / π *
        (exp (θ * I) * exp (θ * I * (-1/2 : ℂ))) * J := by ring
    _ = (1 + (ε:ℂ) * I) ^ 2 / (2 * π * Real.sqrt 2) * J := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, hex]; field_simp
    _ = _ := by
        rw [hsq]; field_simp; linear_combination (-(ε:ℂ) * J) * h2

/-- Laplace moments `∫₀^∞ e^{-πz²t/2} t^{M-1/2} dt`, integrability, for `|arg z| < π/4`. -/
theorem fresnel_moment_integrable {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (M : ℕ) :
    IntegrableOn (fun t : ℝ => exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2)) (Ioi 0) := by
  have hre : 0 < (π*z^2/2 : ℂ).re := by
    have h := abs_im_lt_re_of_abs_arg_lt hz0 hz
    have : (π*z^2/2 : ℂ).re = π/2 * (z.re^2 - z.im^2) := by
      simp [sq, mul_re]; ring
    rw [this]
    have h' := abs_lt.mp h
    have : 0 < z.re ^ 2 - z.im ^ 2 := by nlinarith [abs_nonneg z.im]
    positivity
  have hs : 0 < ((M:ℂ) + 1/2).re := by simp; positivity
  have h := kummerU_laplace_integrable (b := (M:ℂ) + 1/2 + 1) hs hre
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  beta_reduce
  rw [show (M:ℂ) + 1/2 + 1 - ((M:ℂ) + 1/2) - 1 = 0 by ring, cpow_zero, mul_one,
    show (M:ℂ) + 1/2 - 1 = (M:ℂ) - 1/2 by ring]
  congr 1; congr 1; ring

/-- Laplace moments for the Fresnel auxiliary functions:
`1/(π√2) ∫₀^∞ e^{-πz²t/2} t^{M-1/2} dt = (1/2)_M/(π z (πz²/2)^M)` for `|arg z| < π/4`. -/
theorem fresnel_moment {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (M : ℕ) :
    1/(π*Real.sqrt 2) * ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) =
      poch (1/2) M / (π*z*(π*z^2/2)^M) := by
  have hre : 0 < (π*z^2/2 : ℂ).re := by
    have h := abs_im_lt_re_of_abs_arg_lt hz0 hz
    have : (π*z^2/2 : ℂ).re = π/2 * (z.re^2 - z.im^2) := by
      simp [sq, mul_re]; ring
    rw [this]
    have h' := abs_lt.mp h
    have : 0 < z.re ^ 2 - z.im ^ 2 := by nlinarith [abs_nonneg z.im]
    positivity
  have hs : 0 < ((M:ℂ) + 1/2).re := by simp; positivity
  have h := kummerU_laplace_shift_one hs hre
  rw [kummerU_shift_one _ (Or.inl hre)] at h
  have hI : ∫ t : ℝ in Ioi 0, exp (-(π*z^2/2) * t) * (t:ℂ)^((M:ℂ) + 1/2 - 1) *
      (1 + (t:ℂ))^(((M:ℂ) + 1/2 + 1) - ((M:ℂ) + 1/2) - 1) =
      ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show ((M:ℂ) + 1/2 + 1) - ((M:ℂ) + 1/2) - 1 = 0 by ring, cpow_zero, mul_one,
      show (M:ℂ) + 1/2 - 1 = (M:ℂ) - 1/2 by ring]
    congr 2; ring
  rw [hI] at h
  -- `(πz²/2)^{-(M+1/2)} = y^{-(2M+1)}` with `y = √(π/2) z`
  set y : ℂ := (Real.sqrt (π/2) : ℂ) * z with hy
  have hpos : 0 < Real.sqrt (π/2) := Real.sqrt_pos.mpr (by positivity)
  have hy0 : y ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hpos.ne') hz0
  have hyarg : arg y = arg z := by rw [hy, arg_real_mul _ hpos]
  have hysq : y ^ 2 = π*z^2/2 := by
    rw [hy, mul_pow, ← ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hcp : (π*z^2/2 : ℂ) ^ (-((M:ℂ) + 1/2)) = (y ^ (2*M+1))⁻¹ := by
    rw [← hysq, ← cpow_ofNat, ← cpow_mul]
    · rw [show (2:ℂ) * -((M:ℂ) + 1/2) = -(((2*M+1 : ℕ) : ℂ)) by push_cast; ring,
        cpow_neg, cpow_natCast]
    · have him : (log y * 2).im = 2 * arg z := by
        rw [← hyarg]; norm_num [mul_im, log_im]; try ring
      rw [him]; have := abs_lt.mp hz; nlinarith [Real.pi_pos]
    · have him : (log y * 2).im = 2 * arg z := by
        rw [← hyarg]; norm_num [mul_im, log_im]; try ring
      rw [him]; have := abs_lt.mp hz; nlinarith [Real.pi_pos]
  rw [hcp] at h
  have hG : Gamma ((M:ℂ) + 1/2) = Real.sqrt π * poch (1/2) M := by
    rw [poch_half_eq_Gamma, show ((M:ℂ) + 1/2) = (((M:ℝ) + 1/2 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal]
    have : (Real.sqrt π) ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    push_cast; field_simp
  have hGne : Gamma ((M:ℂ) + 1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hint : ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) =
      Gamma ((M:ℂ) + 1/2) * (y ^ (2*M+1))⁻¹ := by
    rw [h, ← mul_assoc, mul_one_div_cancel hGne, one_mul]
  rw [hint, hG]
  have hpow : y ^ (2*M+1) = (Real.sqrt (π/2) : ℂ) * z * (π*z^2/2)^M := by
    rw [pow_succ', pow_mul, hysq, hy]
  rw [hpow]
  have h2 : (Real.sqrt 2 : ℂ) * Real.sqrt (π/2) = Real.sqrt π := by
    rw [← ofReal_mul, ← Real.sqrt_mul (by norm_num)]; congr 2; ring
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have hsp : (Real.sqrt (π/2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
  have hsπ : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hzp : (π*z^2/2 : ℂ)^M ≠ 0 := pow_ne_zero _ (by rw [← hysq]; exact pow_ne_zero _ hy0)
  rw [← h2]
  field_simp

/-- `1 + s i r ≠ 0` for real `s, r`, with `‖(1 + s i r)⁻¹‖ ≤ 1`. -/
theorem norm_one_add_sign_I_mul_recip_le (s r : ℝ) :
    1 + (s:ℂ)*I*r ≠ 0 ∧ ‖(1 + (s:ℂ)*I*r)⁻¹‖ ≤ 1 := by
  have hre : (1 + (s:ℂ)*I*r).re = 1 := by simp
  have h1 : 1 ≤ ‖1 + (s:ℂ)*I*r‖ := hre ▸ re_le_norm _
  have hne : 1 + (s:ℂ)*I*r ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
  exact ⟨hne, by rw [norm_inv]; exact inv_le_one_of_one_le₀ h1⟩

/-- Partial fractions: `(1+ir)⁻¹ ± (1-ir)⁻¹`. -/
theorem one_add_I_mul_recip_add_sub (r : ℝ) :
    (1 + I*r)⁻¹ + (1 - I*r)⁻¹ = 2/((r:ℂ)^2+1) ∧
      (1 + I*r)⁻¹ - (1 - I*r)⁻¹ = -2*I*r/((r:ℂ)^2+1) := by
  have hu : (1 + I*r) ≠ 0 := by
    simpa using (norm_one_add_sign_I_mul_recip_le 1 r).1
  have hv : (1 - I*r) ≠ 0 := by
    have := (norm_one_add_sign_I_mul_recip_le (-1) r).1
    push_cast at this; rwa [show (1:ℂ) + -1*I*r = 1 - I*r by ring] at this
  have hw : (r:ℂ)^2 + 1 ≠ 0 := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_add]
    exact ofReal_ne_zero.mpr (by positivity)
  constructor
  · rw [inv_add_inv hu hv, div_eq_div_iff (mul_ne_zero hu hv) hw]
    linear_combination (2*(r:ℂ)^2) * I_sq
  · rw [inv_sub_inv hu hv, div_eq_div_iff (mul_ne_zero hu hv) hw]
    linear_combination (-2*I*(r:ℂ)^3) * I_sq

/-- Integrability of the signed Fresnel Laplace integrands. -/
theorem integrableOn_fresnel_signed (s : ℝ) {z : ℂ} (hz0 : z ≠ 0)
    (hz : |arg z| < π/4) :
    IntegrableOn (fun r : ℝ => cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + s*I*r)⁻¹))
      (Ioi 0) := by
  have h0 := fresnel_moment_integrable hz0 hz 0
  refine h0.norm.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun r hr => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun r hr => ?_) measurableSet_Ioi
    have hr : (0:ℝ) < r := hr
    refine ContinuousAt.continuousWithinAt ?_
    have hm : (r:ℂ) ∈ slitPlane := by simp [mem_slitPlane_iff, hr]
    refine ContinuousAt.mul (by fun_prop) (ContinuousAt.mul ?_ ?_)
    · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hr.ne'))
    · exact ContinuousAt.inv₀ (by fun_prop) (norm_one_add_sign_I_mul_recip_le s r).1
  · rw [norm_mul, norm_mul, norm_mul]
    have := (norm_one_add_sign_I_mul_recip_le s r).2
    rw [show -(π*z^2/2*(r:ℂ)) = -π*z^2*r/2 by ring, show ((0:ℕ):ℂ) - 1/2 = -1/2 by push_cast; ring]
    calc ‖cexp (-π*z^2*r/2)‖ * (‖(r:ℂ)^(-1/2:ℂ)‖ * ‖(1 + (s:ℂ)*I*r)⁻¹‖)
        ≤ ‖cexp (-π*z^2*r/2)‖ * (‖(r:ℂ)^(-1/2:ℂ)‖ * 1) := by gcongr
      _ = _ := by rw [mul_one]

/-- **Laplace forms of `f` and `g`** (DLMF 7.7.10–7.7.11, on the open sector `|arg z| < π/4`):
`f(z), g(z) = 1/(π√2) ∫₀^∞ e^{-πz²t/2} t^{∓1/2}/(t²+1) dt`. -/
theorem fresnelAux_laplace_open (aux : Bool) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) :
    (if aux then fresnelAuxGComplex z else fresnelAuxFComplex z) = 1/(π*Real.sqrt 2) *
      ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^(((if aux then 1 else 0 : ℕ) : ℂ) - 1/2) /
        ((t:ℂ)^2+1) := by
  have hp := fresnelAux_signed_laplace (ε := 1) (Or.inl rfl) hz0 hz
  have hm := fresnelAux_signed_laplace (ε := -1) (Or.inr rfl) hz0 hz
  have ip := integrableOn_fresnel_signed 1 hz0 hz
  have im := integrableOn_fresnel_signed (-1) hz0 hz
  set fp : ℝ → ℂ := fun r => cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + ((1:ℝ):ℂ)*I*r)⁻¹)
  set fm : ℝ → ℂ := fun r => cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + ((-1:ℝ):ℂ)*I*r)⁻¹)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have h2 : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hc : (Real.sqrt 2 : ℂ) / (2 * π) = 1 / (π * Real.sqrt 2) := by
    rw [div_eq_div_iff (mul_ne_zero two_ne_zero hπ) (mul_ne_zero hπ hs2)]
    linear_combination (π : ℂ) * h2
  have hden : ∀ r : ℝ, (1 + ((1:ℝ):ℂ)*I*r) ≠ 0 ∧ (1 + ((-1:ℝ):ℂ)*I*r) ≠ 0 ∧
      ((r:ℂ)^2 + 1) ≠ 0 := by
    intro r
    refine ⟨(norm_one_add_sign_I_mul_recip_le 1 r).1,
      (norm_one_add_sign_I_mul_recip_le (-1) r).1, ?_⟩
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_add]
    exact ofReal_ne_zero.mpr (by positivity)
  cases aux
  · simp only [Bool.false_eq_true, ite_false, Nat.cast_zero, zero_sub]
    have hF : fresnelAuxFComplex z = (Real.sqrt 2 / (2*π)) / 2 *
        ((∫ r in Ioi (0:ℝ), fp r) + ∫ r in Ioi (0:ℝ), fm r) := by
      push_cast at hp hm ⊢
      apply mul_left_cancel₀ (show (2:ℂ) * I ≠ 0 by simp)
      linear_combination hp - hm
    rw [hF, ← integral_add ip im, hc, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    obtain ⟨d1, d2, d3⟩ := hden r
    rw [← mul_add, show (1:ℂ) + ((1:ℝ):ℂ)*I*r = 1 + I*r by push_cast; ring,
      show (1:ℂ) + ((-1:ℝ):ℂ)*I*r = 1 - I*r by push_cast; ring, ← mul_add,
      (one_add_I_mul_recip_add_sub r).1, show -(π*z^2/2*(r:ℂ)) = -π*z^2*r/2 by ring,
      show (-1/2:ℂ) = -(1/2) by ring]
    field_simp
  · simp only [ite_true, Nat.cast_one]
    have hG : fresnelAuxGComplex z = I * (Real.sqrt 2 / (2*π)) / 2 *
        ((∫ r in Ioi (0:ℝ), fp r) - ∫ r in Ioi (0:ℝ), fm r) := by
      push_cast at hp hm ⊢
      linear_combination (hp + hm) / 2
    rw [hG, ← integral_sub ip im, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr : (0:ℝ) < r := hr
    obtain ⟨d1, d2, d3⟩ := hden r
    have hr0 : (r:ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    have hcp : (r:ℂ)^((1:ℂ) - 1/2) = (r:ℂ)^(-1/2:ℂ) * r := by
      rw [show (1:ℂ) - 1/2 = -1/2 + 1 by ring, cpow_add _ _ hr0, cpow_one]
    rw [← mul_sub, show (1:ℂ) + ((1:ℝ):ℂ)*I*r = 1 + I*r by push_cast; ring,
      show (1:ℂ) + ((-1:ℝ):ℂ)*I*r = 1 - I*r by push_cast; ring, ← mul_sub,
      (one_add_I_mul_recip_add_sub r).2, show -(π*z^2/2*(r:ℂ)) = -π*z^2*r/2 by ring, hcp, ← hc,
      show (-1/2:ℂ) = -(1/2) by ring]
    field_simp
    ring_nf
    rw [I_sq]; ring

/-- Integrability of the Fresnel remainder integrands `e^{-πz²t/2} t^{M-1/2}/(t²+1)`. -/
theorem fresnel_kernel_integrable {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (M : ℕ) :
    IntegrableOn (fun t : ℝ => exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) / ((t:ℂ)^2+1))
      (Ioi 0) := by
  have h0 := fresnel_moment_integrable hz0 hz M
  have hw : ∀ t : ℝ, 1 ≤ ‖(t:ℂ)^2+1‖ := fun t => by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_add, Complex.norm_real, Real.norm_of_nonneg
      (by positivity)]
    nlinarith [sq_nonneg t]
  refine h0.norm.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht : (0:ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    have hne : (t:ℂ)^2+1 ≠ 0 := fun h => by have := hw t; rw [h, norm_zero] at this; linarith
    exact ((by fun_prop : Continuous fun t : ℝ => exp (-π*z^2*t/2)).continuousAt.mul
      (continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne'))).div (by fun_prop) hne
  · rw [norm_div]
    exact div_le_self (norm_nonneg _) (hw t)

/-- **Remainder integrals for the Fresnel auxiliary expansions**, with
`M = 2N + (0 or 1)`: `R_N(z) = (-1)^N/(π√2) ∫₀^∞ e^{-πz²t/2} t^{M-1/2}/(t²+1) dt`. -/
theorem fresnel_remainder_eq (aux : Bool) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (N : ℕ) :
    fresnelAsymptoticRemainder aux N z = (-1 : ℂ)^N/(π*Real.sqrt 2) *
      ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) *
        (t:ℂ)^(((2*N + if aux then 1 else 0 : ℕ) : ℂ) - 1/2) / ((t:ℂ)^2+1) := by
  induction N with
  | zero =>
    rw [fresnelAsymptoticRemainder, Finset.range_zero, Finset.sum_empty, sub_zero,
      fresnelAux_laplace_open aux hz0 hz]
    simp
  | succ N ih =>
    set M : ℕ := 2*N + if aux then 1 else 0 with hM
    have hM2 : (2*(N+1) + if aux then 1 else 0 : ℕ) = M + 2 := by rw [hM]; ring
    rw [fresnelAsymptoticRemainder, Finset.sum_range_succ, ← sub_sub,
      ← fresnelAsymptoticRemainder, ih, hM2]
    have hsplit : ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) / ((t:ℂ)^2+1) =
        (∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2)) -
        ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^(((M+2 : ℕ) : ℂ) - 1/2) / ((t:ℂ)^2+1) := by
      rw [← integral_sub (fresnel_moment_integrable hz0 hz M)
        (fresnel_kernel_integrable hz0 hz (M+2))]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht : (0:ℝ) < t := ht
      have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
      have hne : (t:ℂ)^2+1 ≠ 0 := by
        rw [← ofReal_pow, ← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.mpr (by positivity)
      rw [show (((M+2 : ℕ) : ℂ) - 1/2) = ((M:ℂ) - 1/2) + 2 by push_cast; ring,
        cpow_add _ _ ht0, show (2:ℂ) = ((2:ℕ):ℂ) by norm_num, cpow_natCast]
      field_simp
      ring
    have hterm : fresnelAsymptoticTerm aux N z = (-1 : ℂ)^N/(π*Real.sqrt 2) *
        ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) := by
      rw [fresnelAsymptoticTerm, ← hM, mul_div_assoc, ← fresnel_moment hz0 hz M]
      ring
    rw [hsplit, hterm, pow_succ]
    ring

/-- Identity under the stated parameter and domain assumptions: `fresnelAsymptoticRemainder false
N z=(-1 : ℂ)^N/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, exp (-π*z^2*t/2)*(t : ℂ)^(2*N+0-1/2 : ℂ)/((t
: ℂ)^2+1))`. -/
@[dlmf 7.12.E6]
theorem fresnelAuxFComplex_remainder_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (N : ℕ) :
    fresnelAsymptoticRemainder false N z=(-1 : ℂ)^N/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, exp (-π*z^2*t/2)*(t : ℂ)^(2*N+0-1/2 : ℂ)/((t : ℂ)^2+1)) := by
  rw [fresnel_remainder_eq false hz0 hz N]
  simp

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (sector
(π/2-δ)) (fun n z => z^(-(4*(n : ℂ)+3))) (fun n => (-1 : ℂ)^n*poch (1/2)
(2*n+1)*(2/π)^(2*n+1)/π) fresnelAuxGComplex`. -/
@[dlmf 7.12.E3]
theorem fresnelAuxGComplex_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π/2) :
    HasAsymptoticExpansion (sector (π/2-δ)) (fun n z => z^(-(4*(n : ℂ)+3))) (fun n => (-1 : ℂ)^n*poch (1/2) (2*n+1)*(2/π)^(2*n+1)/π) fresnelAuxGComplex := by
  have hp := fresnelAux_signed_sector_asymptotic (Or.inl rfl) hδ hδ1
  have hm := fresnelAux_signed_sector_asymptotic (Or.inr rfl) hδ hδ1
  have h := (hp.add hm).const_smul (1 / 2 : ℂ)
  have hf : ((1 / 2 : ℂ) • ((fun z => fresnelAuxGComplex z + ((1:ℝ):ℂ)*I*fresnelAuxFComplex z) +
      (fun z => fresnelAuxGComplex z + ((-1:ℝ):ℂ)*I*fresnelAuxFComplex z))) = fresnelAuxGComplex := by
    funext z
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast
    ring
  rw [hf] at h
  have ho := h.odd (fun n => by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have h1 : ((((1:ℝ):ℂ) * I))^(2*n+1) = (-1)^n * I := by rw [pow_succ, pow_mul]; simp
    have h2 : ((((-1:ℝ):ℂ) * I))^(2*n+1) = -((-1)^n * I) := by rw [pow_succ, pow_mul]; simp
    rw [h1, h2]
    ring)
  refine (ho.congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only
    congr 1; push_cast; ring
  · funext n
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have h1 : ((((1:ℝ):ℂ) * I))^(2*n+1+1) = (-1)^(n+1) := by
      rw [show 2*n+1+1 = 2*(n+1) by ring, pow_mul]; simp
    have h2 : ((((-1:ℝ):ℂ) * I))^(2*n+1+1) = (-1)^(n+1) := by
      rw [show 2*n+1+1 = 2*(n+1) by ring, pow_mul]; simp
    rw [h1, h2, pow_succ (-1:ℂ) (2*n), pow_mul (-1:ℂ) 2 n, pow_succ (-1:ℂ) n]
    ring

/-- Identity under the stated parameter and domain assumptions: `fresnelAsymptoticRemainder true N
z=(-1 : ℂ)^N/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, exp (-π*z^2*t/2)*(t : ℂ)^(2*N+1-1/2 : ℂ)/((t :
ℂ)^2+1))`. -/
@[dlmf 7.12.E7]
theorem fresnelAuxGComplex_remainder_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (N : ℕ) :
    fresnelAsymptoticRemainder true N z=(-1 : ℂ)^N/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, exp (-π*z^2*t/2)*(t : ℂ)^(2*N+1-1/2 : ℂ)/((t : ℂ)^2+1)) := by
  rw [fresnel_remainder_eq true hz0 hz N]
  simp

/-- Sector-dependent Fresnel next-term bounds. -/
lemma fresnelAux_remainder_bound (aux : Bool) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (N : ℕ) :
    ‖fresnelAsymptoticRemainder aux N z‖ ≤ (if |arg z| ≤ π/8 then 1 else |1/Real.sin (4*arg z)|)*‖fresnelAsymptoticTerm aux N z‖ := by
  set M : ℕ := 2*N + if aux then 1 else 0 with hM
  set α := arg z with hα
  set θ : ℝ := -2*α with hθ
  have hθa : |θ| < π/2 := by rw [hθ, abs_mul, abs_neg, abs_two]; linarith
  set a : ℂ := π*z^2/2 with ha
  set s : ℝ := ‖z‖ with hs
  have hs0 : 0 < s := by rw [hs]; exact norm_pos_iff.mpr hz0
  set A : ℝ := π/2 * s^2 with hA
  have hA0 : 0 < A := by positivity
  have hae : a * exp (θ * I) = (A : ℂ) := by
    have hzω : z * exp (((-α:ℝ):ℂ) * I) = (s : ℂ) := by
      conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
      rw [mul_assoc, ← Complex.exp_add]
      push_cast
      simp [hs, hα]
    have : exp (θ * I) = (exp (((-α:ℝ):ℂ) * I))^2 := by
      rw [← Complex.exp_nat_mul, hθ]; push_cast; ring_nf
    rw [this, ha, hA]
    calc (π:ℂ) * z^2 / 2 * (exp (((-α:ℝ):ℂ) * I))^2
        = π / 2 * (z * exp (((-α:ℝ):ℂ) * I))^2 := by ring
      _ = _ := by rw [hzω]; push_cast; ring
  have hre : 0 < a.re := by
    have h := abs_im_lt_re_of_abs_arg_lt hz0 hz
    have : a.re = π/2 * (z.re^2 - z.im^2) := by rw [ha]; simp [sq, mul_re]; ring
    rw [this]
    have h' := abs_lt.mp h
    have : 0 < z.re ^ 2 - z.im ^ 2 := by nlinarith [abs_nonneg z.im]
    positivity
  have hreθ : 0 < (a * exp (θ * I)).re := by rw [hae, ofReal_re]; exact hA0
  -- lower bound for the denominator along the rotated rays
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_one_add_ofReal_mul_exp (Φ := 2 * |θ|)
    (by linarith)
  have hden : ∀ r y : ℝ, ((r : ℂ) * exp (y * I)) ^ 2 + 1 =
      1 + ((r ^ 2 : ℝ) : ℂ) * exp (((2 * y : ℝ) : ℂ) * I) := by
    intro r y; rw [ofReal_mul_exp_ofReal_mul_I_sq]; ring
  have hdenc : ∀ r : ℝ, ∀ y : ℝ, |y| ≤ |θ| → c ≤ ‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖ := by
    intro r y hy
    rw [hden r y]
    exact hc _ (sq_nonneg r) _ (by rw [abs_mul, abs_two]; linarith)
  have hFn : ∀ r : ℝ, 0 < r → ∀ y : ℝ, |y| ≤ |θ| →
      ‖((r : ℂ) * exp (y * I)) ^ ((M:ℂ) - 1/2) / (((r : ℂ) * exp (y * I)) ^ 2 + 1)‖ ≤
        ‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖⁻¹ * r ^ ((M:ℝ) - 1/2) := by
    intro r hr y hy
    have hy' : |y| < π := by linarith [Real.pi_pos]
    rw [abs_lt] at hy'
    rw [norm_div, ofReal_mul_exp_cpow hr hy'.1 hy'.2.le, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hr,
      show (y : ℂ) * I * ((M:ℂ) - 1/2) = ((y * ((M:ℝ) - 1/2) : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one]
    have : ((M:ℂ) - 1/2).re = (M:ℝ) - 1/2 := by simp
    rw [this, div_eq_inv_mul]
  have hFc : ∀ r : ℝ, 0 < r → ∀ y : ℝ, |y| ≤ |θ| →
      ‖((r : ℂ) * exp (y * I)) ^ ((M:ℂ) - 1/2) / (((r : ℂ) * exp (y * I)) ^ 2 + 1)‖ ≤
        1 / c * r ^ ((M:ℝ) - 1/2) := by
    intro r hr y hy
    refine (hFn r hr y hy).trans ?_
    gcongr
    rw [one_div]; exact inv_anti₀ hc0 (hdenc r y hy)
  have hrot := integral_cexp_neg_mul_mul_eq_rotate
    (F := fun t : ℂ => t ^ ((M:ℂ) - 1/2) / (t ^ 2 + 1)) (θ := θ) (σ := (M:ℝ) + 1/2)
    (C := 1 / c) (k := (M:ℝ) - 1/2) (z := a) (by positivity)
    (fun r hr y hy => by
      have hy1 := abs_le_abs_of_mem_uIcc_zero hy
      have hm := ofReal_mul_exp_mem_slitPlane hr (by linarith [Real.pi_pos] : |y| < π)
      have hne : ((r : ℂ) * exp (y * I)) ^ 2 + 1 ≠ 0 := fun h0 => by
        have := hdenc r y hy1; rw [h0, norm_zero] at this; linarith
      exact (differentiableAt_id.cpow (differentiableAt_const _) hm).div
        ((differentiableAt_pow 2).add_const 1) hne)
    (fun r hr _ y hy => by
      rw [show (M:ℝ) + 1/2 - 1 = (M:ℝ) - 1/2 by ring]
      exact hFc r hr y (abs_le_abs_of_mem_uIcc_zero hy))
    (fun r hr y hy => hFc r (by linarith) y (abs_le_abs_of_mem_uIcc_zero hy))
    (fun y hy => re_mul_exp_pos_of_mem_uIcc hθa hre hreθ hy)
  have hI : ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) / ((t:ℂ)^2+1) =
      ∫ t : ℝ in Ioi 0, cexp (-(a * t)) * ((t:ℂ) ^ ((M:ℂ) - 1/2) / ((t:ℂ) ^ 2 + 1)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [ha]; ring_nf
  -- the sector constant
  set L : ℝ := if |α| ≤ π/8 then 1 else |Real.sin (4*α)| with hL
  have hL0 : 0 < L := by
    rw [hL]; split_ifs with h
    · exact one_pos
    · push Not at h
      refine abs_pos.mpr (fun h0 => ?_)
      have h4 : 0 < |4 * α| ∧ |4 * α| < π := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
        constructor <;> nlinarith [Real.pi_pos, abs_nonneg α]
      have : Real.sin |4 * α| = 0 := by
        rcases le_total 0 (4 * α) with hh | hh
        · rw [abs_of_nonneg hh, h0]
        · rw [abs_of_nonpos hh, Real.sin_neg, h0, neg_zero]
      exact (Real.sin_pos_of_pos_of_lt_pi h4.1 h4.2).ne' this
  have hLden : ∀ r : ℝ, L ≤ ‖((r : ℂ) * exp (θ * I)) ^ 2 + 1‖ := by
    intro r
    rw [hden r θ, hL]; split_ifs with h
    · refine one_le_norm_one_add_ofReal_mul_exp (sq_nonneg r) ?_
      rw [← Real.cos_abs, abs_mul, abs_two, hθ, abs_mul, abs_neg, abs_two]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg α, Real.pi_pos], by linarith⟩
    · have : |Real.sin (2 * θ)| = |Real.sin (4 * α)| := by
        rw [hθ, show 2 * (-2 * α) = -(4 * α) by ring, Real.sin_neg, abs_neg]
      rw [← this]; exact abs_sin_le_norm_one_add_ofReal_mul_exp _ _
  -- bound the rotated integral
  have hbound : ∀ r ∈ Ioi (0 : ℝ), ‖cexp (-((A:ℂ) * r)) *
      (((r : ℂ) * exp (θ * I)) ^ ((M:ℂ) - 1/2) / (((r : ℂ) * exp (θ * I)) ^ 2 + 1))‖ ≤
      1 / L * (r ^ ((M:ℝ) + 1/2 - 1) * Real.exp (-(A * r))) := by
    intro r hr
    have hr : (0:ℝ) < r := hr
    rw [norm_mul, show -((A:ℂ) * r) = ((-(A * r) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal]
    have h1 := hFn r hr θ le_rfl
    have h2 : ‖((r : ℂ) * exp (θ * I)) ^ 2 + 1‖⁻¹ ≤ 1 / L := by
      rw [one_div]; exact inv_anti₀ hL0 (hLden r)
    rw [show (M:ℝ) + 1/2 - 1 = (M:ℝ) - 1/2 by ring]
    calc Real.exp (-(A * r)) * ‖((r : ℂ) * exp (θ * I)) ^ ((M:ℂ) - 1/2) /
          (((r : ℂ) * exp (θ * I)) ^ 2 + 1)‖
        ≤ Real.exp (-(A * r)) * (‖((r : ℂ) * exp (θ * I)) ^ 2 + 1‖⁻¹ * r ^ ((M:ℝ) - 1/2)) := by
          gcongr
      _ ≤ Real.exp (-(A * r)) * (1 / L * r ^ ((M:ℝ) - 1/2)) := by gcongr
      _ = _ := by ring
  have hs1 : (0:ℝ) < (M:ℝ) + 1/2 := by positivity
  have hint : IntegrableOn (fun r : ℝ => 1 / L * (r ^ ((M:ℝ) + 1/2 - 1) *
      Real.exp (-A * r ^ (1:ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (M:ℝ) + 1/2 - 1)
      (b := A) (by linarith) one_pos hA0).const_mul (1 / L)
  have hint' : IntegrableOn (fun r : ℝ => 1 / L * (r ^ ((M:ℝ) + 1/2 - 1) * Real.exp (-(A * r))))
      (Ioi 0) := hint.congr_fun (fun r _ => by simp [Real.rpow_one, neg_mul]) measurableSet_Ioi
  have hnorm := norm_integral_le_of_norm_le hint'
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound))
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hs1 hA0] at hnorm
  -- assemble
  rw [fresnel_remainder_eq aux hz0 hz N, ← hM, hI, hrot, hae, norm_mul, norm_mul,
    norm_exp_ofReal_mul_I, one_mul]
  have hc1 : ‖(-1 : ℂ)^N/(π*Real.sqrt 2)‖ = 1/(π*Real.sqrt 2) := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [hc1]
  have hterm : ‖fresnelAsymptoticTerm aux N z‖ =
      Real.Gamma ((M:ℝ) + 1/2) / Real.sqrt π / (π * s * A ^ M) := by
    rw [fresnelAsymptoticTerm, ← hM, poch_half_eq_Gamma, norm_div, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg (Real.Gamma_pos_of_pos hs1).le (Real.sqrt_nonneg _)), norm_mul, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, ← hs, ← ha]
    have hna : ‖a‖ = A := by
      have := congrArg norm hae
      rwa [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hA0.le] at this
    rw [norm_pow, hna]
  have hc : (if |α| ≤ π/8 then (1:ℝ) else |1/Real.sin (4*α)|) = 1 / L := by
    rw [hL]; split_ifs <;> simp
  rw [hterm, hc]
  have hAr : A ^ ((M:ℝ) + 1/2) = A ^ M * (Real.sqrt (π/2) * s) := by
    rw [Real.rpow_add hA0, Real.rpow_natCast, ← Real.sqrt_eq_rpow, hA,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hs0.le]
  have hsq : Real.sqrt 2 * Real.sqrt (π/2) = Real.sqrt π := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hG0 : 0 < Real.Gamma ((M:ℝ) + 1/2) := Real.Gamma_pos_of_pos hs1
  calc 1 / (π * Real.sqrt 2) * ‖∫ r in Ioi (0:ℝ), cexp (-((A:ℂ) * r)) *
        (((r : ℂ) * exp (θ * I)) ^ ((M:ℂ) - 1/2) / (((r : ℂ) * exp (θ * I)) ^ 2 + 1))‖
      ≤ 1 / (π * Real.sqrt 2) * (1 / L * ((1 / A) ^ ((M:ℝ) + 1/2) * Real.Gamma ((M:ℝ) + 1/2))) := by
        gcongr
    _ = _ := by
        rw [Real.div_rpow zero_le_one hA0.le, Real.one_rpow, hAr, ← hsq]
        have : 0 < Real.sqrt (π/2) := Real.sqrt_pos.mpr (by positivity)
        have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        field_simp

/-- Signed real Fresnel remainder. -/
lemma fresnelAux_remainder_sign (aux : Bool) {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (-1 : ℝ)^N*(fresnelAsymptoticRemainder aux N x).re := by
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x:ℂ)| < π/4 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  set M : ℕ := 2*N + if aux then 1 else 0
  set g : ℝ → ℝ := fun t => Real.exp (-π*x^2*t/2) * t^((M:ℝ) - 1/2) / (t^2+1) with hg
  have hI : ∫ t in Ioi (0:ℝ), exp (-π*(x:ℂ)^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) / ((t:ℂ)^2+1) =
      ((∫ t in Ioi (0:ℝ), g t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : (0:ℝ) < t := ht
    simp only [hg]
    push_cast
    rw [ofReal_cpow ht.le]
    push_cast; ring_nf
  rw [fresnel_remainder_eq aux hx0 harg N, hI]
  have hre : ((-1 : ℂ)^N/(π*Real.sqrt 2) * ((∫ t in Ioi (0:ℝ), g t : ℝ) : ℂ)).re =
      (-1 : ℝ)^N/(π*Real.sqrt 2) * ∫ t in Ioi (0:ℝ), g t := by
    rw [show (-1 : ℂ)^N/(π*Real.sqrt 2) = (((-1 : ℝ)^N/(π*Real.sqrt 2) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_mul, ofReal_re]
  rw [hre, ← mul_assoc, ← mul_div_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
  have ht : (0:ℝ) < t := ht
  simp only [hg]; positivity

end DLMF.Confluent

end
