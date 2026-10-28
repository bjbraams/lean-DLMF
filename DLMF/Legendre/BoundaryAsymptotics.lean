/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Boundary
public import DLMF.Gamma.RecipGammaDeriv
public import DLMF.Legendre.Connections

/-!
# Boundary asymptotics of Legendre functions

Behaviour of the Ferrers functions `𝖯^μ_ν`, `𝖰^μ_ν` as `x → 1⁻` and of `P^μ_ν`, `𝑸^μ_ν` as
`x → 1⁺` and `x → ∞` (DLMF 14.8), for general complex parameters.

The basic tool is an Abelian limit for the regularized Gauss function valid for every `c`
(`legBd_tendsto_rGHG_one`, from the shared regularized Gauss summation and Mathlib's Abel
limit theorem, including nonpositive integer `c`), together with its Euler-transformed
form for `Re(c-a-b) < 0` (`legBd_tendsto_rGHG_one_neg`, DLMF 15.4.23) and the zero-balanced
logarithmic limit (`legBd_tendsto_rGHG_log`, DLMF 15.4.21). Applied to the defining
hypergeometric representations (DLMF 14.3.11–14.3.14 for `𝖰`, 14.3.7 for `𝑸`, 14.3.18 for `P`)
they give the leading behaviour at every order with `Re μ > 0`, integer orders included,
without any connection formula.

For order `0` the logarithmic expansions DLMF 14.8.3 and 14.8.9 rest on DLMF 15.8.10 at
`m = 0`: `𝐅(a,b;a+b;z) = -Γ(a)⁻¹Γ(b)⁻¹ ln(1-z) 𝐅(a,b;1;1-z) + H(1-z)` with `H` a power
series (`legBd_zeroBalanced_eq`, obtained from the connection formula 15.10.21 by a limit in
`c`), whence `𝐅(a,b;a+b;1-t) + K ln t - (K' - 2γK) = O(t ln t)` for all `a, b`
(`legBd_zeroBalanced_isBigO`), with `K = 1/(Γ(a)Γ(b))` and `K'` written through
`(1/Γ)'` so that no pole of `ψ` is excluded.

All helper names carry the prefix `legBd_`.
-/

@[expose] public noncomputable section
open Complex Filter Set Asymptotics DLMF.Hypergeometric
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- For real `x` tending to `1` from the left, eventually `‖(x : ℂ)‖ < 1`. -/
theorem legBd_eventually_norm_lt_one :
    ∀ᶠ x : ℝ in 𝓝[<] (1:ℝ), ‖(x:ℂ)‖ < 1 := by
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; exact hx

/-- DLMF 15.4.20 as an Abelian limit for the regularized function, valid for every `c`:
`𝐅(a,b;c;x) → Γ(c-a-b)/(Γ(c-a)Γ(c-b))` as `x → 1⁻` when `Re(c-a-b) > 0`. -/
theorem legBd_tendsto_rGHG_one {a b c : ℂ} (h : 0 < (c-a-b).re) :
    Tendsto (fun x : ℝ => regularizedGaussHG a b c x) (𝓝[<] 1)
      (𝓝 (Gamma (c-a-b) * ((Gamma (c-a))⁻¹ * (Gamma (c-b))⁻¹))) := by
  simpa only [div_eq_mul_inv, mul_inv] using tendsto_regularizedGaussHG_left_one h

/-- DLMF 15.4.23 for the regularized function, valid for every `c`: when `Re(c-a-b) < 0`,
`(1-x)^(a+b-c) 𝐅(a,b;c;x) → Γ(a+b-c)/(Γ(a)Γ(b))` as `x → 1⁻`. -/
theorem legBd_tendsto_rGHG_one_neg {a b c : ℂ} (h : (c-a-b).re < 0) :
    Tendsto (fun x : ℝ => ((1-x:ℝ):ℂ)^(a+b-c) * regularizedGaussHG a b c x) (𝓝[<] 1)
      (𝓝 (Gamma (a+b-c) * ((Gamma a)⁻¹ * (Gamma b)⁻¹))) := by
  have h' : 0 < (c-(c-a)-(c-b)).re := by
    rw [show c-(c-a)-(c-b) = -(c-a-b) by ring, neg_re]; linarith
  have hT := legBd_tendsto_rGHG_one h'
  rw [show c-(c-a)-(c-b) = a+b-c by ring, sub_sub_cancel, sub_sub_cancel] at hT
  refine hT.congr' ?_
  filter_upwards [legBd_eventually_norm_lt_one, self_mem_nhdsWithin] with x hx hx1
  have hpos : (0:ℝ) < 1-x := by simp only [mem_Iio] at hx1; linarith
  have hne : ((1-x:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
  rw [regularizedGaussHG_euler a b c (mem_cutPlane_of_norm_lt_one hx),
    show (1:ℂ)-x = ((1-x:ℝ):ℂ) by push_cast; ring, ← mul_assoc, ← cpow_add _ _ hne,
    show a+b-c+(c-a-b) = 0 by ring, cpow_zero, one_mul]

/-- `x² → 1⁻` as `x → 1⁻`. -/
theorem legBd_tendsto_sq_nhdsLT :
    Tendsto (fun x : ℝ => x^2) (𝓝[<] (1:ℝ)) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := ((continuous_pow 2).tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
    simp only [mem_Iio]; nlinarith [hx.1, hx.2]

/-- `1-x² ≠ 0`-type cancellation `(1-x²)^(μ/2) (1-x²)^(-μ/2) = 1` on `(-1,1)`. -/
theorem legBd_one_sub_sq_cpow_mul_neg (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-(x:ℂ)^2)^(μ/2) * (1-(x:ℂ)^2)^(-μ/2) = 1 := by
  have hne : (1-(x:ℂ)^2) ≠ 0 := by
    rw [show (1:ℂ)-(x:ℂ)^2 = ((1-x^2:ℝ):ℂ) by push_cast; ring]
    exact ofReal_ne_zero.mpr (by nlinarith [hx.1, hx.2])
  rw [← cpow_add _ _ hne, show μ/2+(-μ/2) = 0 by ring, cpow_zero]

/-- The regularized pullbacks in `ferrersQ` tend to their Gauss values as `x → 1⁻`. -/
theorem legBd_tendsto_rGHG_sq {a b c : ℂ} (h : 0 < (c-a-b).re) :
    Tendsto (fun x : ℝ => regularizedGaussHG a b c ((x:ℂ)^2)) (𝓝[<] 1)
      (𝓝 (Gamma (c-a-b) * ((Gamma (c-a))⁻¹ * (Gamma (c-b))⁻¹))) := by
  have := (legBd_tendsto_rGHG_one h).comp legBd_tendsto_sq_nhdsLT
  simpa [Function.comp_def] using this

/-- Boundary limit behind DLMF 14.8.4 for every order with `Re μ > 0`:
`(1-x²)^(μ/2) 𝖰^μ_ν(x) → 2^(μ-1) Γ(μ) cos(μπ)` as `x → 1⁻`. -/
theorem legBd_ferrersQ_tendsto {ν μ : ℂ} (h : LegendreQRegular ν μ) (hμ : 0 < μ.re) :
    Tendsto (fun x : ℝ => (1-(x:ℂ)^2)^(μ/2) * ferrersQ ν μ x) (𝓝[<] 1)
      (𝓝 (2^(μ-1) * Gamma μ * cos (μ*π))) := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero h
  have h1 := legBd_tendsto_rGHG_sq (a := -(ν+μ)/2) (b := (ν-μ+1)/2) (c := 1/2)
    (by rw [show (1/2:ℂ)-(-(ν+μ)/2)-((ν-μ+1)/2) = μ by ring]; exact hμ)
  have h2 := legBd_tendsto_rGHG_sq (a := (1-ν-μ)/2) (b := (ν-μ+2)/2) (c := 3/2)
    (by rw [show (3/2:ℂ)-((1-ν-μ)/2)-((ν-μ+2)/2) = μ by ring]; exact hμ)
  rw [show (1/2:ℂ)-(-(ν+μ)/2)-((ν-μ+1)/2) = μ by ring,
    show (1/2:ℂ)-(-(ν+μ)/2) = (ν+μ+1)/2 by ring, show (1/2:ℂ)-((ν-μ+1)/2) = -(ν-μ)/2 by ring] at h1
  rw [show (3/2:ℂ)-((1-ν-μ)/2)-((ν-μ+2)/2) = μ by ring,
    show (3/2:ℂ)-((1-ν-μ)/2) = (ν+μ+2)/2 by ring, show (3/2:ℂ)-((ν-μ+2)/2) = (1-(ν-μ))/2 by ring] at h2
  have hx : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[<] 1) (𝓝 1) := by
    have := (continuous_ofReal.tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  have hT := ((h1.const_mul (-π/2*sin ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ+2)/2)))).add
    ((hx.mul h2).const_mul (π/2*cos ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+2)/2)/Gamma ((ν-μ+1)/2)))))
  have eL : -π/2*sin ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ+2)/2)) *
      (Gamma μ * ((Gamma ((ν+μ+1)/2))⁻¹ * (Gamma (-(ν-μ)/2))⁻¹)) +
      π/2*cos ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+2)/2)/Gamma ((ν-μ+1)/2)) *
      (1 * (Gamma μ * ((Gamma ((ν+μ+2)/2))⁻¹ * (Gamma ((1-(ν-μ))/2))⁻¹))) =
      2^(μ-1) * Gamma μ * cos (μ*π) := by
    have ro := legendre_reflection_odd (ν-μ)
    have re := legendre_reflection_even (ν-μ)
    have hc : cos (μ*π) = cos ((ν+μ)*π/2)*cos ((ν-μ)*π/2) + sin ((ν+μ)*π/2)*sin ((ν-μ)*π/2) := by
      rw [← cos_sub]; congr 1; ring
    have h2m : (2:ℂ)^μ = 2 * 2^(μ-1) := by
      rw [show μ = 1 + (μ-1) by ring, cpow_add _ _ (by norm_num : (2:ℂ) ≠ 0), cpow_one]
      ring_nf
    have k1 : Gamma ((ν+μ+1)/2) * (Gamma ((ν+μ+1)/2))⁻¹ = 1 := mul_inv_cancel₀ hg1
    have k2 : Gamma ((ν+μ+2)/2) * (Gamma ((ν+μ+2)/2))⁻¹ = 1 := mul_inv_cancel₀ hg2
    rw [hc, h2m]
    linear_combination (-(1/2)*sin ((ν+μ)*π/2)*2*2^(μ-1)*Gamma μ) * ro * 1 +
      ((1/2)*cos ((ν+μ)*π/2)*2*2^(μ-1)*Gamma μ) * re +
      (-π/2*sin ((ν+μ)*π/2)*(2*2^(μ-1))*Gamma μ*(Gamma ((ν-μ+2)/2))⁻¹*(Gamma (-(ν-μ)/2))⁻¹) * k1 +
      (π/2*cos ((ν+μ)*π/2)*(2*2^(μ-1))*Gamma μ*(Gamma ((ν-μ+1)/2))⁻¹*(Gamma ((1-(ν-μ))/2))⁻¹) * k2
  rw [eL] at hT
  refine hT.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have hc := legBd_one_sub_sq_cpow_mul_neg μ hx
  simp only [ferrersQ, ferrersW1, ferrersW2]
  linear_combination (-(-π/2*sin ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ+2)/2)) *
    regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) ((x:ℂ)^2)) -
    π/2*cos ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+2)/2)/Gamma ((ν-μ+1)/2)) *
          ((x:ℂ) * regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) ((x:ℂ)^2))) * hc


/-- The regularized pullbacks with negative balance, `(1-x²)^(a+b-c) 𝐅(a,b;c;x²)`, as `x → 1⁻`. -/
theorem legBd_tendsto_rGHG_sq_neg {a b c : ℂ} (h : (c-a-b).re < 0) :
    Tendsto (fun x : ℝ => (1-(x:ℂ)^2)^(a+b-c) * regularizedGaussHG a b c ((x:ℂ)^2)) (𝓝[<] 1)
      (𝓝 (Gamma (a+b-c) * ((Gamma a)⁻¹ * (Gamma b)⁻¹))) := by
  have := (legBd_tendsto_rGHG_one_neg h).comp legBd_tendsto_sq_nhdsLT
  simpa [Function.comp_def] using this

/-- `(1-x²)^(μ/2) (1-x²)^(μ/2) = (1-x²)^μ` on `(-1,1)`. -/
theorem legBd_one_sub_sq_cpow_half_mul (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-(x:ℂ)^2)^(μ/2) * (1-(x:ℂ)^2)^(μ/2) = (1-(x:ℂ)^2)^μ := by
  have hne : (1-(x:ℂ)^2) ≠ 0 := by
    rw [show (1:ℂ)-(x:ℂ)^2 = ((1-x^2:ℝ):ℂ) by push_cast; ring]
    exact ofReal_ne_zero.mpr (by nlinarith [hx.1, hx.2])
  rw [← cpow_add _ _ hne]; ring_nf

/-- `2^(-μ) 2^(ν+μ) / 2^(ν-μ) = 2 · 2^(μ-1)`. -/
theorem legBd_two_cpow_identity (ν μ : ℂ) :
    (2:ℂ)^(-μ) * 2^(ν+μ) * (2^(ν-μ))⁻¹ = 2 * 2^(μ-1) := by
  have h2 : (2:ℂ) ≠ 0 := by norm_num
  rw [← cpow_neg, ← cpow_add _ _ h2, ← cpow_add _ _ h2]
  conv_rhs => rw [show (2:ℂ) * 2^(μ-1) = 2^(1:ℂ) * 2^(μ-1) by rw [cpow_one]]
  rw [← cpow_add _ _ h2]; ring_nf

/-- Boundary limit behind DLMF 14.8.6 for every order with `Re μ > 0`:
`(1-x²)^(μ/2) 𝖰^{-μ}_ν(x) → 2^(μ-1) Γ(μ) Γ(ν-μ+1)/Γ(ν+μ+1)` as `x → 1⁻`. -/
theorem legBd_ferrersQ_neg_tendsto {ν μ : ℂ} (hp : LegendreQRegular ν μ)
    (hm : LegendreQRegular ν (-μ)) (hμ : 0 < μ.re) :
    Tendsto (fun x : ℝ => (1-(x:ℂ)^2)^(μ/2) * ferrersQ ν (-μ) x) (𝓝[<] 1)
      (𝓝 (2^(μ-1) * Gamma μ * Gamma (ν-μ+1) / Gamma (ν+μ+1))) := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hp
  obtain ⟨hg3, hg4⟩ := legendre_Gamma_half_ne_zero_neg hm
  have h1 := legBd_tendsto_rGHG_sq_neg (a := -(ν+-μ)/2) (b := (ν-(-μ)+1)/2) (c := 1/2)
    (by rw [show (1/2:ℂ)-(-(ν+-μ)/2)-((ν-(-μ)+1)/2) = -μ by ring, neg_re]; linarith)
  have h2 := legBd_tendsto_rGHG_sq_neg (a := (1-ν-(-μ))/2) (b := (ν-(-μ)+2)/2) (c := 3/2)
    (by rw [show (3/2:ℂ)-((1-ν-(-μ))/2)-((ν-(-μ)+2)/2) = -μ by ring, neg_re]; linarith)
  rw [show -(ν+-μ)/2+(ν-(-μ)+1)/2-1/2 = μ by ring, show -(ν+-μ)/2 = -(ν-μ)/2 by ring,
    show (ν-(-μ)+1)/2 = (ν+μ+1)/2 by ring] at h1
  rw [show (1-ν-(-μ))/2+(ν-(-μ)+2)/2-3/2 = μ by ring, show (1-ν-(-μ))/2 = (1-(ν-μ))/2 by ring,
    show (ν-(-μ)+2)/2 = (ν+μ+2)/2 by ring] at h2
  have hx : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[<] 1) (𝓝 1) := by
    have := (continuous_ofReal.tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  have hT := ((h1.const_mul (-π/2*sin ((ν+-μ)*π/2)*(2^(-μ)*Gamma ((ν+-μ+1)/2)/Gamma ((ν-(-μ)+2)/2)))).add
    ((hx.mul h2).const_mul (π/2*cos ((ν+-μ)*π/2)*(2^(-μ)*Gamma ((ν+-μ+2)/2)/Gamma ((ν-(-μ)+1)/2)))))
  have eL : -π/2*sin ((ν+-μ)*π/2)*(2^(-μ)*Gamma ((ν+-μ+1)/2)/Gamma ((ν-(-μ)+2)/2)) *
      (Gamma μ * ((Gamma (-(ν-μ)/2))⁻¹ * (Gamma ((ν+μ+1)/2))⁻¹)) +
      π/2*cos ((ν+-μ)*π/2)*(2^(-μ)*Gamma ((ν+-μ+2)/2)/Gamma ((ν-(-μ)+1)/2)) *
      (1 * (Gamma μ * ((Gamma ((1-(ν-μ))/2))⁻¹ * (Gamma ((ν+μ+2)/2))⁻¹))) =
      2^(μ-1) * Gamma μ * Gamma (ν-μ+1) / Gamma (ν+μ+1) := by
    have ro := legendre_reflection_odd (ν-μ)
    have re := legendre_reflection_even (ν-μ)
    have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have ro' : (Gamma (-(ν-μ)/2))⁻¹ = -sin ((ν-μ)*π/2) * Gamma ((ν-μ+2)/2) / π := by
      rw [eq_div_iff hpi]
      have k4 : (Gamma ((ν-μ+2)/2))⁻¹ * Gamma ((ν-μ+2)/2) = 1 := inv_mul_cancel₀ hg4
      linear_combination Gamma ((ν-μ+2)/2) * ro - π * (Gamma (-(ν-μ)/2))⁻¹ * k4
    have re' : (Gamma ((1-(ν-μ))/2))⁻¹ = cos ((ν-μ)*π/2) * Gamma ((ν-μ+1)/2) / π := by
      rw [eq_div_iff hpi]
      have k3 : (Gamma ((ν-μ+1)/2))⁻¹ * Gamma ((ν-μ+1)/2) = 1 := inv_mul_cancel₀ hg3
      linear_combination Gamma ((ν-μ+1)/2) * re - π * (Gamma ((1-(ν-μ))/2))⁻¹ * k3
    have d1 := legendre_duplication (ν-μ)
    have d2 := legendre_duplication (ν+μ)
    have hG : Gamma (ν+μ+1) ≠ 0 := by
      rw [d2]; have : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
      exact div_ne_zero (mul_ne_zero (mul_ne_zero hg1 hg2) (by simp)) this
    have hpy := sin_sq_add_cos_sq ((ν-μ)*π/2)
    have h22 := legBd_two_cpow_identity ν μ
    rw [show ν+-μ = ν-μ by ring, show ν-(-μ) = ν+μ by ring, ro', re', d1, d2]
    have hsq : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have h2c : (2:ℂ)^(ν+μ) ≠ 0 := by simp
    have h2d : (2:ℂ)^(ν-μ) ≠ 0 := by simp
    have h22' : (2:ℂ)^(-μ) * 2^(ν+μ) = 2 * 2^(μ-1) * 2^(ν-μ) := by
      rw [← h22]; field_simp
    field_simp
    rw [show (π:ℂ)*(ν-μ)/2 = (ν-μ)*π/2 by ring, hpy]
    linear_combination Gamma μ * h22'
  rw [eL] at hT
  simp only [show ν+-μ = ν-μ by ring, show ν-(-μ) = ν+μ by ring] at hT
  refine hT.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have hc := legBd_one_sub_sq_cpow_half_mul μ hx
  simp only [ferrersQ, ferrersW1, ferrersW2]
  simp only [show ν+-μ = ν-μ by ring, show ν-(-μ) = ν+μ by ring, show -(-μ)/2 = μ/2 by ring]
  rw [show (1-ν-(-μ))/2 = (1-(ν-μ))/2 by ring]
  linear_combination (-(-π/2*sin ((ν-μ)*π/2)*(2^(-μ)*Gamma ((ν-μ+1)/2)/Gamma ((ν+μ+2)/2)) *
    regularizedGaussHG (-(ν-μ)/2) ((ν+μ+1)/2) (1/2) ((x:ℂ)^2)) -
    π/2*cos ((ν-μ)*π/2)*(2^(-μ)*Gamma ((ν-μ+2)/2)/Gamma ((ν+μ+1)/2)) *
          ((x:ℂ) * regularizedGaussHG ((1-(ν-μ))/2) ((ν+μ+2)/2) (3/2) ((x:ℂ)^2))) * hc


/-- `u ~ v` when `u = v g` eventually and `g → 1`. -/
theorem legBd_isEquivalent_of_eventuallyEq_mul {l : Filter ℝ} {u v g : ℝ → ℂ}
    (h : u =ᶠ[l] fun x => v x * g x) (hg : Tendsto g l (𝓝 1)) : u ~[l] v := by
  have h1 : g ~[l] Function.const _ (1:ℂ) := (isEquivalent_const_iff_tendsto one_ne_zero).mpr hg
  have h2 := (IsEquivalent.refl (u := v)).mul h1
  have e : v * Function.const ℝ (1:ℂ) = v := by funext x; simp
  rw [e] at h2
  exact h2.congr_left (h.symm.trans (Eventually.of_forall fun x => rfl))

/-- Transfer of a weighted limit to an asymptotic equivalence: if `r u → K` and `r v → M`
with `K, M ≠ 0`, then `u ~ (K/M) v`. -/
theorem legBd_isEquivalent_of_tendsto {l : Filter ℝ} {u v r : ℝ → ℂ} {K M : ℂ}
    (hu : Tendsto (fun x => r x * u x) l (𝓝 K)) (hv : Tendsto (fun x => r x * v x) l (𝓝 M))
    (hK : K ≠ 0) (hM : M ≠ 0) :
    u ~[l] fun x => K / M * v x := by
  have hne : ∀ᶠ x in l, r x * v x ≠ 0 := hv.eventually_ne hM
  have hg : Tendsto (fun x => (r x * u x) / (r x * v x) * (M / K)) l (𝓝 1) := by
    have := ((hu.div hv hM).mul_const (M / K))
    rwa [show K / M * (M / K) = 1 by field_simp] at this
  refine (legBd_isEquivalent_of_eventuallyEq_mul ?_ hg)
  filter_upwards [hne] with x hx
  have hr : r x ≠ 0 := left_ne_zero_of_mul hx
  have hvx : v x ≠ 0 := right_ne_zero_of_mul hx
  field_simp

/-- `(1-x²)^(μ/2) (2/(1-x))^(μ/2) → 2^μ` as `x → 1⁻`. -/
theorem legBd_tendsto_weight_left (μ : ℂ) :
    Tendsto (fun x : ℝ => (1-(x:ℂ)^2)^(μ/2) * (2/(1-(x:ℂ)))^(μ/2)) (𝓝[<] 1) (𝓝 (2^μ)) := by
  have hc : ContinuousAt (fun x : ℝ => (2*(1+(x:ℂ)))^(μ/2)) 1 :=
    ContinuousAt.cpow (by fun_prop) continuousAt_const (Or.inl (by norm_num))
  have h4 : (2*(1+((1:ℝ):ℂ)))^(μ/2) = (2:ℂ)^μ := by
    have hl : (log (2:ℂ)).im = 0 := by
      rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ← ofReal_log (by norm_num), ofReal_im]
    rw [show (2*(1+((1:ℝ):ℂ))) = (2:ℂ)^(2:ℂ) by norm_num,
      ← cpow_mul _ (by simp [hl, Real.pi_pos]) (by simp [hl, Real.pi_pos.le])]
    ring_nf
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
  rw [h4] at this
  refine this.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  have h1 : (0:ℝ) ≤ 1-x^2 := by nlinarith [hx.1, hx.2]
  have h2 : (0:ℝ) ≤ 2/(1-x) := div_nonneg (by norm_num) (by linarith [hx.2])
  have hx1 : (1:ℝ)-x ≠ 0 := by linarith [hx.2]
  have e := mul_cpow_ofReal_nonneg h1 h2 (μ/2)
  push_cast at e
  rw [← e]
  congr 1
  have : (1:ℂ)-x ≠ 0 := by exact_mod_cast hx1
  field_simp; ring


/-- `2^(μ-1)/2^μ = 1/2`. -/
theorem legBd_two_cpow_sub_one_div (μ : ℂ) : (2:ℂ)^(μ-1) / 2^μ = 1/2 := by
  have h2 : (2:ℂ) ≠ 0 := by norm_num
  rw [cpow_sub _ _ h2, cpow_one]
  have : (2:ℂ)^μ ≠ 0 := by simp
  field_simp

/-- `cos(μπ) ≠ 0` when `Re μ > 0` and `μ` is not a positive half-odd integer. -/
theorem legBd_cos_ne_zero {μ : ℂ} (hμ : 0 < μ.re) (hh : ∀ n : ℕ, μ ≠ n+1/2) : cos (μ*π) ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h0
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hμk : μ = k + 1/2 := by
    have e : μ * π = (k + 1/2) * π := by rw [hk]; ring
    exact mul_right_cancel₀ hpi e
  have hre : (0:ℝ) < k + 1/2 := by
    have := congrArg re hμk; simp at this; linarith
  have hk0 : 0 ≤ k := by
    by_contra hneg; push Not at hneg
    have : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    linarith
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  exact hh n (by rw [hμk]; push_cast; ring)

/-- `1/x² → 1⁻` as `x → 1⁺`. -/
theorem legBd_tendsto_recip_sq_nhdsGT :
    Tendsto (fun x : ℝ => 1/x^2) (𝓝[>] (1:ℝ)) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := ((by fun_prop (disch := norm_num) : ContinuousAt (fun x : ℝ => 1/x^2) 1).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi 1))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    simp only [mem_Iio]
    rw [div_lt_one (by positivity)]; nlinarith

/-- `1-1/x² → 1⁻` as `x → ∞`. -/
theorem legBd_tendsto_one_sub_recip_sq_atTop :
    Tendsto (fun x : ℝ => 1-1/x^2) atTop (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun x : ℝ => 1/x^2) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (two_ne_zero)))
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub h
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [mem_Iio]
    have : 0 < 1/x^2 := by positivity
    linarith

/-- For `x > 1`, the inherited branch is `(x²-1)^(μ/2) = x^μ (1-1/x²)^(μ/2)`. -/
theorem legBd_branchPower_eq (μ : ℂ) {x : ℝ} (hx : 1 < x) :
    legendreBranchPower μ x = (x:ℂ)^μ * (1-1/(x:ℂ)^2)^(μ/2) := by
  have h0 : (0:ℝ) < x := by linarith
  have h1 : (0:ℝ) < x-1 := by linarith
  have h2 : (0:ℝ) < x+1 := by linarith
  have h3 : (0:ℝ) < 1-1/x^2 := by
    rw [sub_pos, div_lt_one (by positivity)]; nlinarith
  have e3 : (1-1/(x:ℂ)^2) = ((1-1/x^2:ℝ):ℂ) := by push_cast; ring
  have l3 : Real.log (1-1/x^2) = Real.log (x-1) + Real.log (x+1) - 2*Real.log x := by
    rw [show 1-1/x^2 = (x-1)*(x+1)/x^2 by field_simp; ring, Real.log_div (by positivity)
      (by positivity), Real.log_mul h1.ne' h2.ne', Real.log_pow]
    push_cast; ring
  have hl1 : log ((x:ℂ)-1) = (Real.log (x-1):ℂ) := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring, ofReal_log h1.le]
  have hl2 : log ((x:ℂ)+1) = (Real.log (x+1):ℂ) := by
    rw [show (x:ℂ)+1 = ((x+1:ℝ):ℂ) by push_cast; ring, ofReal_log h2.le]
  rw [legendreBranchPower, cpow_def_of_ne_zero (ofReal_ne_zero.mpr h0.ne'),
    cpow_def_of_ne_zero (by rw [e3]; exact ofReal_ne_zero.mpr h3.ne'), ← exp_add, e3,
    ← ofReal_log h3.le, ← ofReal_log h0.le, l3, hl1, hl2]
  congr 1; push_cast; ring

/-- `Γ((t+1)/2)⁻¹ Γ((t+2)/2)⁻¹ = 2^t Γ(t+1)⁻¹ / √π` (reciprocal duplication, all `t`). -/
theorem legBd_recip_half_Gammas (t : ℂ) :
    (Gamma ((t+1)/2))⁻¹ * (Gamma ((t+2)/2))⁻¹ = 2^t * (Gamma (t+1))⁻¹ / (Real.sqrt π : ℂ) := by
  have hsq : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2 : (2:ℂ)^t ≠ 0 := by simp
  rw [legendre_recip_duplication t, cpow_neg]
  field_simp

/-- Boundary limit behind DLMF 14.8.11 for every order with `Re μ > 0`:
`(1-1/x²)^(μ/2) 𝑸^μ_ν(x) → 2^(μ-1) Γ(μ)/Γ(ν+μ+1)` as `x → 1⁺`. -/
theorem legBd_olverQ_tendsto (ν : ℂ) {μ : ℂ} (hμ : 0 < μ.re) :
    Tendsto (fun x : ℝ => (1-1/(x:ℂ)^2)^(μ/2) * olverQ ν μ x) (𝓝[>] 1)
      (𝓝 (2^(μ-1) * Gamma μ * (Gamma (ν+μ+1))⁻¹)) := by
  have h1 := (legBd_tendsto_rGHG_one_neg (a := (ν+μ+2)/2) (b := (ν+μ+1)/2) (c := ν+3/2)
    (by rw [show ν+3/2-(ν+μ+2)/2-(ν+μ+1)/2 = -μ by ring, neg_re]; linarith)).comp
    legBd_tendsto_recip_sq_nhdsGT
  rw [show (ν+μ+2)/2+(ν+μ+1)/2-(ν+3/2) = μ by ring] at h1
  have hc : ContinuousAt (fun x : ℝ => (x:ℂ)^μ / (x:ℂ)^(ν+μ+1)) 1 := by
    refine ContinuousAt.div ?_ ?_ (by simp)
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (Or.inl (by norm_num))
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (Or.inl (by norm_num))
  have hc1 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 1))
  simp only [ofReal_one, one_cpow, div_one] at hc1
  have hT := (hc1.mul h1).const_mul ((Real.sqrt π:ℂ) / 2^(ν+1))
  have eK : (Real.sqrt π:ℂ) / 2^(ν+1) * (1 * (Gamma μ * ((Gamma ((ν+μ+2)/2))⁻¹ *
      (Gamma ((ν+μ+1)/2))⁻¹))) = 2^(μ-1) * Gamma μ * (Gamma (ν+μ+1))⁻¹ := by
    have hd := legBd_recip_half_Gammas (ν+μ)
    have hsq : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have h2 : (2:ℂ)^(ν+μ) = 2^(ν+1) * 2^(μ-1) := by
      rw [← cpow_add _ _ (by norm_num)]; ring_nf
    have h2n : (2:ℂ)^(ν+1) ≠ 0 := by simp
    rw [show (Gamma ((ν+μ+2)/2))⁻¹ * (Gamma ((ν+μ+1)/2))⁻¹ =
      (Gamma ((ν+μ+1)/2))⁻¹ * (Gamma ((ν+μ+2)/2))⁻¹ by ring, hd, h2]
    field_simp
  rw [eK] at hT
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  have h0 : (0:ℝ) < x := by linarith
  have h3 : (0:ℝ) < 1-1/x^2 := by
    rw [sub_pos, div_lt_one (by positivity)]; nlinarith
  have e3 : (1-1/(x:ℂ)^2) = ((1-1/x^2:ℝ):ℂ) := by push_cast; ring
  have hne : ((1-1/x^2:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr h3.ne'
  simp only [Function.comp_apply, olverQ]
  rw [legBd_branchPower_eq μ hx]
  have hpp : (1-1/(x:ℂ)^2)^(μ/2) * (1-1/(x:ℂ)^2)^(μ/2) = (1-1/(x:ℂ)^2)^μ := by
    rw [← cpow_add _ _ (by rw [e3]; exact hne)]; ring_nf
  have hx0 : (x:ℂ)^(ν+μ+1) ≠ 0 := by simp [h0.ne']
  have h2n : (2:ℂ)^(ν+1) ≠ 0 := by simp
  push_cast
  rw [← hpp]
  field_simp

/-- `4^(μ/2) = 2^μ`. -/
theorem legBd_four_cpow_half (μ : ℂ) : (4:ℂ)^(μ/2) = 2^μ := by
  have hl : (log (2:ℂ)).im = 0 := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ← ofReal_log (by norm_num), ofReal_im]
  rw [show (4:ℂ) = (2:ℂ)^(2:ℂ) by norm_num,
    ← cpow_mul _ (by simp [hl, Real.pi_pos]) (by simp [hl, Real.pi_pos.le])]
  ring_nf

/-- `(1-1/x²)^(μ/2) (2/(x-1))^(μ/2) → 2^μ` as `x → 1⁺`. -/
theorem legBd_tendsto_weight_right (μ : ℂ) :
    Tendsto (fun x : ℝ => (1-1/(x:ℂ)^2)^(μ/2) * (2/((x:ℂ)-1))^(μ/2)) (𝓝[>] 1) (𝓝 (2^μ)) := by
  have hc : ContinuousAt (fun x : ℝ => (2*((x:ℂ)+1)/(x:ℂ)^2)^(μ/2)) 1 :=
    ContinuousAt.cpow (by fun_prop (disch := norm_num)) continuousAt_const (Or.inl (by norm_num))
  have h4 : (2*(((1:ℝ):ℂ)+1)/((1:ℝ):ℂ)^2)^(μ/2) = (2:ℂ)^μ := by
    rw [← legBd_four_cpow_half]; norm_num
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 1))
  rw [h4] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  have h1 : (0:ℝ) ≤ 1-1/x^2 := by
    rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  have h2 : (0:ℝ) ≤ 2/(x-1) := div_nonneg (by norm_num) (by linarith)
  have e := mul_cpow_ofReal_nonneg h1 h2 (μ/2)
  push_cast at e
  rw [← e]
  congr 1
  have : (x:ℂ)-1 ≠ 0 := by exact_mod_cast (show x-1 ≠ 0 by linarith)
  have : (x:ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith)
  field_simp; ring

/-- Boundary limit behind DLMF 14.8.12, valid for every order: when `Re ν > -1/2`,
`x^(-ν) P^μ_ν(x) → 2^ν Γ(ν+1/2)/(√π Γ(ν-μ+1))` as `x → ∞`. -/
theorem legBd_associatedP_tendsto_atTop {ν : ℂ} (hν : -1/2 < ν.re) (μ : ℂ) :
    Tendsto (fun x : ℝ => (x:ℂ)^(-ν) * associatedP ν μ x) atTop
      (𝓝 (2^ν * Gamma (ν+1/2) * (Gamma (ν-μ+1))⁻¹ / (Real.sqrt π : ℂ))) := by
  have h1 := (legBd_tendsto_rGHG_one (a := (-μ-ν)/2) (b := (-μ-ν+1)/2) (c := -μ+1)
    (by rw [show -μ+1-(-μ-ν)/2-(-μ-ν+1)/2 = ν+1/2 by ring, add_re]; norm_num; linarith)).comp
    legBd_tendsto_one_sub_recip_sq_atTop
  rw [show -μ+1-(-μ-ν)/2-(-μ-ν+1)/2 = ν+1/2 by ring, show -μ+1-(-μ-ν)/2 = ((ν-μ)+2)/2 by ring,
    show -μ+1-(-μ-ν+1)/2 = ((ν-μ)+1)/2 by ring] at h1
  have hw : Tendsto (fun x : ℝ => (1-1/(x:ℂ)^2)^((-μ)/2)) atTop (𝓝 1) := by
    have hc : ContinuousAt (fun w : ℂ => (1-w)^((-μ)/2)) 0 :=
      ContinuousAt.cpow (by fun_prop) continuousAt_const (by norm_num)
    have h0 : Tendsto (fun x : ℝ => 1/(x:ℂ)^2) atTop (𝓝 0) := by
      have h : Tendsto (fun x : ℝ => ((1/x^2 : ℝ) : ℂ)) atTop (𝓝 ((0:ℝ):ℂ)) :=
        (continuous_ofReal.tendsto 0).comp (by
          simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (two_ne_zero))))
      simpa using h
    have := hc.tendsto.comp h0
    simpa [Function.comp_def] using this
  have hT := (hw.mul h1).const_mul ((2:ℂ)^μ)
  have eK : (2:ℂ)^μ * (1 * (Gamma (ν+1/2) * ((Gamma (((ν-μ)+2)/2))⁻¹ * (Gamma (((ν-μ)+1)/2))⁻¹))) =
      2^ν * Gamma (ν+1/2) * (Gamma (ν-μ+1))⁻¹ / (Real.sqrt π : ℂ) := by
    have hd := legBd_recip_half_Gammas (ν-μ)
    have h2 : (2:ℂ)^μ * 2^(ν-μ) = 2^ν := by rw [← cpow_add _ _ (by norm_num)]; ring_nf
    rw [show (Gamma (((ν-μ)+2)/2))⁻¹ * (Gamma (((ν-μ)+1)/2))⁻¹ =
      (Gamma ((ν-μ+1)/2))⁻¹ * (Gamma ((ν-μ+2)/2))⁻¹ by ring, hd, ← h2]
    ring
  rw [eK] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have h0 : (0:ℝ) < x := by linarith
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr h0.ne'
  have hz : (x:ℂ)-1 ∈ slitPlane := Or.inl (by simp; linarith)
  have hq := associatedP_neg_eq_quadratic ν (-μ) hz (by simp; linarith)
  rw [neg_neg] at hq
  simp only [Function.comp_apply]
  rw [hq, legBd_branchPower_eq (-μ) hx]
  have hp : (x:ℂ)^(-ν) * (x:ℂ)^(ν-(-μ)) * (x:ℂ)^(-μ) = 1 := by
    rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]; ring_nf; simp
  push_cast
  linear_combination (-(2:ℂ)^μ * ((1-1/(x:ℂ)^2)^((-μ)/2)) *
    regularizedGaussHG ((-μ-ν)/2) ((-μ-ν+1)/2) (-μ+1) (1-1/(x:ℂ)^2)) * hp

/-- Regular-`c` case of the zero-balanced logarithmic limit. -/
theorem legBd_tendsto_rGHG_log_of_regular {a b : ℂ} (hc : ∀ k : ℕ, a + b ≠ -(k : ℂ)) :
    Tendsto (fun x : ℝ => regularizedGaussHG a b (a+b) x / (-Real.log (1 - x) : ℂ)) (𝓝[<] 1)
      (𝓝 ((Gamma a)⁻¹ * (Gamma b)⁻¹)) := by
  have hΓ : Gamma (a+b) ≠ 0 := Gamma_ne_zero fun k hk => hc k hk
  have hA := (zero_balanced_limit hc).div_const (Gamma (a+b))
  have e : Gamma (a + b) / (Gamma a * Gamma b) / Gamma (a+b) = (Gamma a)⁻¹ * (Gamma b)⁻¹ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (Gamma (a+b)), mul_assoc, mul_inv_cancel₀ hΓ,
      mul_one, mul_inv]
  rw [e] at hA
  refine hA.congr' ?_
  filter_upwards [legBd_eventually_norm_lt_one] with x hx
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hx, regularizedGaussHGFun_eq_div_Gamma hc]
  ring

/-- DLMF 15.4.21 for the regularized function, valid for all `a, b`:
`𝐅(a,b;a+b;x) / (-ln(1-x)) → 1/(Γ(a)Γ(b))` as `x → 1⁻`. -/
theorem legBd_tendsto_rGHG_log (a b : ℂ) :
    Tendsto (fun x : ℝ => regularizedGaussHG a b (a+b) x / (-Real.log (1 - x) : ℂ)) (𝓝[<] 1)
      (𝓝 ((Gamma a)⁻¹ * (Gamma b)⁻¹)) := by
  by_cases hc : ∀ k : ℕ, a + b ≠ -(k : ℂ)
  · exact legBd_tendsto_rGHG_log_of_regular hc
  push Not at hc
  obtain ⟨n, hn⟩ := hc
  have hc2 : ∀ k : ℕ, (a+n+1) + (b+n+1) ≠ -(k : ℂ) := fun k hk => by
    have e : (a+n+1) + (b+n+1) = (n:ℂ)+2 := by linear_combination hn
    rw [e] at hk
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hT := legBd_tendsto_rGHG_log_of_regular hc2
  have hx : Tendsto (fun x : ℝ => (x:ℂ)^(n+1)) (𝓝[<] 1) (𝓝 1) := by
    have := ((by fun_prop : Continuous fun x : ℝ => (x:ℂ)^(n+1)).tendsto 1).mono_left
      (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  have hT2 := (hx.const_mul (poch a (n+1) * poch b (n+1))).mul hT
  have e : poch a (n+1) * poch b (n+1) * 1 * ((Gamma (a+n+1))⁻¹ * (Gamma (b+n+1))⁻¹) =
      (Gamma a)⁻¹ * (Gamma b)⁻¹ := by
    have ha := DLMF.Gamma.poch_mul_recip_Gamma_add_nat a (n+1)
    have hb := DLMF.Gamma.poch_mul_recip_Gamma_add_nat b (n+1)
    push_cast at ha hb
    rw [show a+(n+1) = a+n+1 by ring] at ha
    rw [show b+(n+1) = b+n+1 by ring] at hb
    rw [← ha, ← hb]; ring
  rw [e] at hT2
  refine hT2.congr' ?_
  filter_upwards [legBd_eventually_norm_lt_one] with x hx
  rw [hn, regularizedGaussHG_neg_nat _ _ _ (mem_cutPlane_of_norm_lt_one hx),
    show (n:ℂ)+2 = (a+n+1)+(b+n+1) by linear_combination -hn]
  ring

/-- Boundary limit behind DLMF 14.8.14, valid for every order:
`x^(1/2) P^μ_{-1/2}(x) / ln x → 2^(1/2)/(√π Γ(1/2-μ))` as `x → ∞`. -/
theorem legBd_associatedP_half_tendsto_atTop (μ : ℂ) :
    Tendsto (fun x : ℝ => (x:ℂ)^(1/2:ℂ) / (Real.log x : ℂ) * associatedP (-1/2) μ x) atTop
      (𝓝 (2^(1/2:ℂ) * (Gamma (1/2-μ))⁻¹ / (Real.sqrt π : ℂ))) := by
  have h1 := (legBd_tendsto_rGHG_log ((1/2-μ)/2) ((3/2-μ)/2)).comp
    legBd_tendsto_one_sub_recip_sq_atTop
  have hw : Tendsto (fun x : ℝ => (1-1/(x:ℂ)^2)^((-μ)/2)) atTop (𝓝 1) := by
    have hc : ContinuousAt (fun w : ℂ => (1-w)^((-μ)/2)) 0 :=
      ContinuousAt.cpow (by fun_prop) continuousAt_const (by norm_num)
    have h0 : Tendsto (fun x : ℝ => 1/(x:ℂ)^2) atTop (𝓝 0) := by
      have h : Tendsto (fun x : ℝ => ((1/x^2 : ℝ) : ℂ)) atTop (𝓝 ((0:ℝ):ℂ)) :=
        (continuous_ofReal.tendsto 0).comp (by
          simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (two_ne_zero))))
      simpa using h
    have := hc.tendsto.comp h0
    simpa [Function.comp_def] using this
  have hT := (hw.mul h1).const_mul ((2:ℂ)^μ * 2)
  have eK : (2:ℂ)^μ * 2 * (1 * ((Gamma ((1/2-μ)/2))⁻¹ * (Gamma ((3/2-μ)/2))⁻¹)) =
      2^(1/2:ℂ) * (Gamma (1/2-μ))⁻¹ / (Real.sqrt π : ℂ) := by
    have hd := legBd_recip_half_Gammas (-1/2-μ)
    rw [show (-1/2-μ+1)/2 = (1/2-μ)/2 by ring, show (-1/2-μ+2)/2 = (3/2-μ)/2 by ring,
      show -1/2-μ+1 = 1/2-μ by ring] at hd
    have h2 : (2:ℂ)^μ * 2 * 2^(-1/2-μ) = 2^(1/2:ℂ) := by
      conv_lhs => rw [show (2:ℂ)^μ * 2 * 2^(-1/2-μ) = 2^μ * 2^(1:ℂ) * 2^(-1/2-μ) by rw [cpow_one]]
      rw [← cpow_add _ _ (by norm_num), ← cpow_add _ _ (by norm_num)]; ring_nf
    rw [hd, ← h2]; ring
  rw [eK] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have h0 : (0:ℝ) < x := by linarith
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr h0.ne'
  have hlog : (0:ℝ) < Real.log x := Real.log_pos hx
  have hl : (-Real.log (1 - (1-1/x^2)) : ℂ) = 2 * (Real.log x : ℂ) := by
    rw [show (1:ℝ) - (1-1/x^2) = (x^2)⁻¹ by ring, Real.log_inv, Real.log_pow]; push_cast; ring
  have hz : (x:ℂ)-1 ∈ slitPlane := Or.inl (by simp; linarith)
  have hq := associatedP_neg_eq_quadratic (-1/2) (-μ) hz (by simp; linarith)
  rw [neg_neg] at hq
  simp only [Function.comp_apply]
  rw [hq, legBd_branchPower_eq (-μ) hx, hl]
  have hp : (x:ℂ)^(1/2:ℂ) * (x:ℂ)^(-1/2-(-μ)) * (x:ℂ)^(-μ) = 1 := by
    rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]; ring_nf; simp
  have hc : (1/2-μ)/2 + (3/2-μ)/2 = -μ+1 := by ring
  have hlc : (Real.log x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hlog.ne'
  push_cast
  rw [show ((-μ - -1/2)/2 : ℂ) = (1/2-μ)/2 by ring, show ((-μ - -1/2 + 1)/2 : ℂ) = (3/2-μ)/2 by ring,
    show (-μ + 1 : ℂ) = (1/2-μ)/2 + (3/2-μ)/2 by ring]
  linear_combination (-(2:ℂ)^μ * ((1-1/(x:ℂ)^2)^((-μ)/2)) *
    regularizedGaussHG ((1/2-μ)/2) ((3/2-μ)/2) ((1/2-μ)/2 + (3/2-μ)/2) (1-1/(x:ℂ)^2) /
      (Real.log x : ℂ)) * hp




/-- `2^(1/2)/√π = (2/π)^(1/2)` in complex powers. -/
theorem legBd_sqrt_two_div_sqrt_pi :
    (2:ℂ)^(1/2:ℂ) / (Real.sqrt π : ℂ) = ((2/π:ℝ):ℂ)^(1/2:ℂ) := by
  have h1 : (2:ℂ)^(1/2:ℂ) = (((2:ℝ)^(1/2:ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by norm_num)]; push_cast; rfl
  have h2 : ((2/π:ℝ):ℂ)^(1/2:ℂ) = (((2/π)^(1/2:ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by positivity)]; push_cast; rfl
  rw [h1, h2, Real.sqrt_eq_rpow, ← ofReal_div, Real.div_rpow (by norm_num) Real.pi_pos.le]

/-! ### Zero-balanced logarithmic expansions (DLMF 15.8.10, `m = 0`) and DLMF 14.8.3, 14.8.9 -/

section ZeroBalanced
open DLMF.Gamma


/-- Constant `Γ(a)⁻¹Γ(b)⁻¹` of the zero-balanced expansion. -/
def legBdK (a b : ℂ) : ℂ := (Gamma a)⁻¹ * (Gamma b)⁻¹

/-- Constant `(1/Γ)'(a)/Γ(b) + (1/Γ)'(b)/Γ(a)` of the zero-balanced expansion. -/
def legBdK' (a b : ℂ) : ℂ := recipGammaDeriv 1 b * (Gamma a)⁻¹ + (Gamma b)⁻¹ * recipGammaDeriv 1 a

/-- The analytic part of the zero-balanced expansion of `𝐅(a,b;a+b;1-w)`. -/
def legBdZbH (a b w : ℂ) : ℂ :=
  legBdK a b * deriv (fun c => regularizedGaussHGFun a b (a+b-c+1) w) (a+b) +
    legBdK' a b * regularizedGaussHGFun a b 1 w -
    legBdK a b * deriv (fun c => regularizedGaussHGFun (c-a) (c-b) (c-a-b+1) w) (a+b)

/-- DLMF 15.8.10 at `m = 0` in structural form, valid for all `a, b`:
`𝐅(a,b;a+b;z) = -Γ(a)⁻¹Γ(b)⁻¹ ln(1-z) 𝐅(a,b;1;1-z) + H(1-z)`. -/
theorem legBd_zeroBalanced_eq (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    regularizedGaussHGFun a b (a+b) z =
      -legBdK a b * log (1-z) * regularizedGaussHGFun a b 1 (1-z) + legBdZbH a b (1-z) := by
  set w := 1 - z with hwdef
  set c₀ := a + b with hc₀
  have hw0 : w ≠ 0 := by
    intro h; rw [hwdef, sub_eq_zero] at h; rw [← h] at hz; simp at hz
  have hconn : ∀ c : ℂ, sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z =
      regularizedGaussHGFun a b (a + b - c + 1) w * ((Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹) -
        (Gamma a * Gamma b)⁻¹ * (w ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b)
          (c - a - b + 1) w) := by
    intro c
    rw [regularized_connection_one_sub a b c hz hw]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hRc := (analyticOnNhd_regularizedGaussHGFun_c a b hz c₀ (Set.mem_univ _)).differentiableAt
  have hsin : HasDerivAt (fun c : ℂ => sin (Real.pi * (c - a - b)) / Real.pi)
      (cos (Real.pi * (c₀ - a - b)) * (Real.pi * 1) / Real.pi) c₀ :=
    ((((hasDerivAt_id c₀).sub_const a).sub_const b).const_mul (Real.pi : ℂ)).csin.div_const _
  have hm1 : c₀ - a - b = 0 := by rw [hc₀]; ring
  have hL := hsin.mul hRc.hasDerivAt
  rw [hm1, mul_zero, cos_zero, Complex.sin_zero, zero_div, zero_mul, add_zero, one_mul,
    mul_one, div_self hπ, one_mul] at hL
  have hwn : ‖w‖ < 1 := hw
  set S : ℂ → ℂ := fun c => regularizedGaussHGFun a b (a + b - c + 1) w with hSdef
  have hSa : DifferentiableAt ℂ S c₀ :=
    (analyticOnNhd_regularizedGaussHGFun_comp (A := fun _ => a) (B := fun _ => b)
      (C := fun c => a + b - c + 1) (differentiable_const _) (differentiable_const _)
      (by fun_prop) hwn c₀ (Set.mem_univ _)).differentiableAt
  set Q : ℂ → ℂ := fun c => regularizedGaussHGFun (c - a) (c - b) (c - a - b + 1) w with hQdef
  have hQa : DifferentiableAt ℂ Q c₀ :=
    (analyticOnNhd_regularizedGaussHGFun_comp (A := fun c => c - a) (B := fun c => c - b)
      (C := fun c => c - a - b + 1) (by fun_prop) (by fun_prop) (by fun_prop) hwn c₀
      (Set.mem_univ _)).differentiableAt
  have e1 : c₀ - a = b := by rw [hc₀]; ring
  have e2 : c₀ - b = a := by rw [hc₀]; ring
  have hG1 : HasDerivAt (fun c : ℂ => (Gamma (c - a))⁻¹) (recipGammaDeriv 1 b) c₀ := by
    have h1 : HasDerivAt (fun y => (Gamma y)⁻¹) (recipGammaDeriv 1 b) (c₀ - a) := by
      rw [e1]; exact hasDerivAt_recip_Gamma' _
    simpa [Function.comp_def] using h1.comp c₀ ((hasDerivAt_id c₀).sub_const a)
  have hG2 : HasDerivAt (fun c : ℂ => (Gamma (c - b))⁻¹) (recipGammaDeriv 1 a) c₀ := by
    have h1 : HasDerivAt (fun y => (Gamma y)⁻¹) (recipGammaDeriv 1 a) (c₀ - b) := by
      rw [e2]; exact hasDerivAt_recip_Gamma' _
    simpa [Function.comp_def] using h1.comp c₀ ((hasDerivAt_id c₀).sub_const b)
  have hP : HasDerivAt (fun c : ℂ => w ^ (c - a - b)) (w ^ (0 : ℂ) * log w * 1) c₀ := by
    have h := (((hasDerivAt_id c₀).sub_const a).sub_const b).const_cpow (c := w) (Or.inl hw0)
    rw [show _root_.id c₀ - a - b = (0 : ℂ) by simp only [_root_.id]; rw [hc₀]; ring] at h
    exact h
  have hR := (hSa.hasDerivAt.mul (hG1.mul hG2)).sub
    ((hP.mul hQa.hasDerivAt).const_mul ((Gamma a * Gamma b)⁻¹))
  have hfun : (fun c => sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z) =
      fun c => S c * ((Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹) -
        (Gamma a * Gamma b)⁻¹ * (w ^ (c - a - b) * Q c) := funext hconn
  have hL' : HasDerivAt (fun c => sin (Real.pi * (c - a - b)) / Real.pi *
      regularizedGaussHGFun a b c z) (regularizedGaussHGFun a b c₀ z) c₀ := hL
  rw [hfun] at hL'
  have hkey := hL'.unique hR
  simp only [Pi.mul_apply] at hkey
  rw [e1, e2, cpow_zero, one_mul, mul_one] at hkey
  have hS0 : S c₀ = regularizedGaussHGFun a b 1 w := by
    simp only [hSdef]; congr 1; rw [hc₀]; ring
  have hQ0 : Q c₀ = regularizedGaussHGFun a b 1 w := by
    simp only [hQdef]; rw [show c₀ - a - b + 1 = 1 by rw [hc₀]; ring, e1, e2,
      ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hwn,
      ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hwn,
      regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_norm_lt_one hwn)]
  rw [hS0, hQ0] at hkey
  rw [hkey, legBdZbH, legBdK, legBdK', ← hSdef, ← hQdef, ← hc₀]
  simp only [mul_inv]
  have h00 : w ^ (0:ℂ) = 1 := cpow_zero w
  norm_num
  ring

/-- Power-series coefficients of `legBdZbH`. -/
def legBdZbCoeff (a b : ℂ) (n : ℕ) : ℂ :=
  legBdK a b * deriv (fun c => poch a n * poch b n / n.factorial * (Gamma (a+b-c+1+n))⁻¹) (a+b) +
    legBdK' a b * (poch a n * poch b n / n.factorial * (Gamma (1+n))⁻¹) -
    legBdK a b * deriv (fun c => poch (c-a) n * poch (c-b) n / n.factorial *
      (Gamma (c-a-b+1+n))⁻¹) (a+b)

/-- `deriv (f · w^n) = deriv f · w^n` for a differentiable `f`. -/
theorem legBd_deriv_mul_pow {f : ℂ → ℂ} {c₀ : ℂ} (hf : DifferentiableAt ℂ f c₀) (w : ℂ) (n : ℕ) :
    deriv (fun c => f c * w^n) c₀ = deriv f c₀ * w^n :=
  (hf.hasDerivAt.mul_const (w^n)).deriv

/-- The analytic part of the zero-balanced expansion is a power series on the unit disk. -/
theorem legBd_zbH_hasSum (a b : ℂ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n => legBdZbCoeff a b n * w^n) (legBdZbH a b w) := by
  have hS := hasSum_deriv_regularizedGaussHGFun_comp (A := fun _ => a) (B := fun _ => b)
    (C := fun c => a + b - c + 1) (differentiable_const _) (differentiable_const _)
    (by fun_prop) hw (a+b)
  have hQ := hasSum_deriv_regularizedGaussHGFun_comp (A := fun c => c - a) (B := fun c => c - b)
    (C := fun c => c - a - b + 1) (by fun_prop) (by fun_prop) (by fun_prop) hw (a+b)
  have hF : HasSum (fun n : ℕ => poch a n * poch b n * w ^ n / n.factorial * (Gamma (1 + n))⁻¹)
      (regularizedGaussHGFun a b 1 w) := by
    have h := (summable_regularizedGaussHGFun_term a b 1 hw).hasSum
    rwa [← regularizedGaussHGFun_eq_tsum] at h
  have hsum := ((hS.mul_left (legBdK a b)).add (hF.mul_left (legBdK' a b))).sub
    (hQ.mul_left (legBdK a b))
  convert hsum using 1
  · funext n
    have hd1 : DifferentiableAt ℂ (fun c => poch a n * poch b n / n.factorial *
        (Gamma (a+b-c+1+n))⁻¹) (a+b) :=
      (differentiableAt_const _).mul (DLMF.Gamma.differentiable_recip_Gamma.comp (by fun_prop) _)
    have hd2 : DifferentiableAt ℂ (fun c => poch (c-a) n * poch (c-b) n / n.factorial *
        (Gamma (c-a-b+1+n))⁻¹) (a+b) := by
      have hp : Differentiable ℂ fun y : ℂ => poch y n := Polynomial.differentiable _
      exact ((((hp.comp (by fun_prop : Differentiable ℂ fun c : ℂ => c - a)) _).mul
        ((hp.comp (by fun_prop : Differentiable ℂ fun c : ℂ => c - b)) _)).div_const _).mul
        (DLMF.Gamma.differentiable_recip_Gamma.comp (by fun_prop) _)
    have e1 := legBd_deriv_mul_pow hd1 w n
    have e2 := legBd_deriv_mul_pow hd2 w n
    have r1 : (fun c => poch a n * poch b n * w ^ n / n.factorial * (Gamma (a+b-c+1+n))⁻¹) =
        fun c => poch a n * poch b n / n.factorial * (Gamma (a+b-c+1+n))⁻¹ * w^n := by
      funext c; ring
    have r2 : (fun c => poch (c-a) n * poch (c-b) n * w ^ n / n.factorial * (Gamma (c-a-b+1+n))⁻¹) =
        fun c => poch (c-a) n * poch (c-b) n / n.factorial * (Gamma (c-a-b+1+n))⁻¹ * w^n := by
      funext c; ring
    rw [r1, r2, e1, e2, legBdZbCoeff]
    ring
  · rfl

/-- `(1/Γ)'(1) = γ`. -/
theorem legBd_recipGammaDeriv_one_one : recipGammaDeriv 1 1 = Real.eulerMascheroniConstant := by
  rw [recipGammaDeriv_one_eq (fun m h => by
    have := congrArg re h; simp at this; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]),
    Complex.digamma_one, Complex.Gamma_one]
  simp

/-- The constant term of the analytic part: `H(0) = K' - 2γK`. -/
theorem legBd_zbCoeff_zero (a b : ℂ) :
    legBdZbCoeff a b 0 = legBdK' a b - 2 * Real.eulerMascheroniConstant * legBdK a b := by
  have h1 : HasDerivAt (fun c : ℂ => (Gamma (a+b-c+1))⁻¹) (recipGammaDeriv 1 1 * (-1)) (a+b) := by
    have hi : HasDerivAt (fun c : ℂ => a+b-c+1) (-1) (a+b) := by
      simpa using ((hasDerivAt_id (a+b)).const_sub (a+b)).add_const (1:ℂ)
    exact (hasDerivAt_recip_Gamma' (1:ℂ)).comp_of_eq (a+b) hi (by ring)
  have h2 : HasDerivAt (fun c : ℂ => (Gamma (c-a-b+1))⁻¹) (recipGammaDeriv 1 1 * 1) (a+b) := by
    have hi : HasDerivAt (fun c : ℂ => c-a-b+1) 1 (a+b) := by
      simpa using (((hasDerivAt_id (a+b)).sub_const a).sub_const b).add_const (1:ℂ)
    exact (hasDerivAt_recip_Gamma' (1:ℂ)).comp_of_eq (a+b) hi (by ring)
  simp only [legBdZbCoeff, poch_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
    Nat.cast_zero, add_zero, Complex.Gamma_one, inv_one, mul_one]
  rw [h1.deriv, h2.deriv, legBd_recipGammaDeriv_one_one]
  ring

/-- A power series converging on the unit disk is `H(0) + O(w)` at `w = 0`. -/
theorem legBd_hasSum_sub_isBigO {h : ℕ → ℂ} {H : ℂ → ℂ}
    (hH : ∀ w : ℂ, ‖w‖ < 1 → HasSum (fun n => h n * w^n) (H w)) :
    (fun w => H w - h 0) =O[𝓝 0] (fun w => w) := by
  have hs := (hH (1/2) (by norm_num)).summable
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, ‖h n * (1/2:ℂ)^n‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hs.tendsto_atTop_zero.norm).bddAbove_range
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine Asymptotics.IsBigO.of_bound (4*C) ?_
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (show (0:ℝ) < 1/4 by norm_num)] with w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hsh := (hasSum_nat_add_iff' 1).mpr (hH w (by linarith))
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one] at hsh
  set r := 2*‖w‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hg : HasSum (fun n : ℕ => C * r * r^n) (C * r * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left (C * r)
  have hb : ∀ n : ℕ, ‖h (n+1) * w^(n+1)‖ ≤ C * r * r^n := by
    intro n
    have h1 := hC (n+1)
    have e : ‖h (n+1) * w^(n+1)‖ = ‖h (n+1) * (1/2:ℂ)^(n+1)‖ * r^(n+1) := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, hr, mul_pow]
      have : ‖(1/2:ℂ)‖ = 1/2 := by norm_num
      rw [this]
      have h2 : (2:ℝ)^(n+1) * (1/2)^(n+1) = 1 := by rw [← mul_pow]; norm_num
      calc ‖h (n+1)‖ * ‖w‖^(n+1) = ‖h (n+1)‖ * ‖w‖^(n+1) * ((2:ℝ)^(n+1) * (1/2)^(n+1)) := by
            rw [h2, mul_one]
        _ = _ := by ring
    rw [e, pow_succ, show C * r * r^n = C * (r^n * r) by ring]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hle := hsh.norm_le_of_bounded hg hb
  calc ‖H w - h 0‖ ≤ C * r * (1 - r)⁻¹ := hle
    _ ≤ 4 * C * ‖w‖ := by
      rw [hr]
      have h12 : (1:ℝ)/2 ≤ 1 - 2*‖w‖ := by linarith
      have hpos : 0 < 1 - 2*‖w‖ := by linarith
      rw [mul_inv_le_iff₀ hpos]
      nlinarith [mul_nonneg (mul_nonneg hC0 (norm_nonneg w)) (by linarith : (0:ℝ) ≤ 1/4 - ‖w‖)]

/-- `t → 0` in `ℂ` as `t → 0⁺` in `ℝ`. -/
theorem legBd_tendsto_ofReal_nhdsGT_zero :
    Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have := (continuous_ofReal.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa using this

/-- `t = O(t ln t)` as `t → 0⁺`. -/
theorem legBd_isBigO_self_mul_log :
    (fun t : ℝ => (t:ℂ)) =O[𝓝[>] 0] (fun t : ℝ => t * Real.log t) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.exp (-1) by positivity)] with t ht
  rw [Complex.norm_real, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
  have hl : Real.log t < -1 := by
    rw [← Real.log_exp (-1)]; exact Real.log_lt_log ht.1 ht.2
  rw [abs_of_neg (by linarith : Real.log t < 0)]
  nlinarith [abs_nonneg t]

/-- DLMF 15.8.10 at `m = 0` as an asymptotic statement, valid for all `a, b`:
`𝐅(a,b;a+b;1-t) = -Γ(a)⁻¹Γ(b)⁻¹ (ln t + 2γ) + K' + O(t ln t)` as `t → 0⁺`, where
`K' = (1/Γ)'(a)/Γ(b) + (1/Γ)'(b)/Γ(a)`. -/
theorem legBd_zeroBalanced_isBigO (a b : ℂ) :
    (fun t : ℝ => regularizedGaussHG a b (a+b) (1-t) + legBdK a b * Real.log t -
      (legBdK' a b - 2 * Real.eulerMascheroniConstant * legBdK a b)) =O[𝓝[>] 0]
      (fun t : ℝ => t * Real.log t) := by
  -- the two power series
  have hH := (legBd_hasSum_sub_isBigO (h := legBdZbCoeff a b) (H := legBdZbH a b)
    fun w hw => legBd_zbH_hasSum a b hw).comp_tendsto legBd_tendsto_ofReal_nhdsGT_zero
  have hFs : ∀ w : ℂ, ‖w‖ < 1 → HasSum (fun n => (poch a n * poch b n / n.factorial *
      (Gamma (1+n))⁻¹) * w^n) (regularizedGaussHGFun a b 1 w) := by
    intro w hw
    have h := (summable_regularizedGaussHGFun_term a b 1 hw).hasSum
    rw [← regularizedGaussHGFun_eq_tsum] at h
    convert h using 2 with n
    ring
  have hQ := (legBd_hasSum_sub_isBigO hFs).comp_tendsto legBd_tendsto_ofReal_nhdsGT_zero
  simp only [poch_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, Nat.cast_zero,
    add_zero, Complex.Gamma_one, inv_one] at hQ
  rw [legBd_zbCoeff_zero] at hH
  have hlog : (fun t : ℝ => legBdK a b * (Real.log t : ℂ) * (regularizedGaussHGFun a b 1 t - 1))
      =O[𝓝[>] 0] (fun t : ℝ => t * Real.log t) := by
    have h1 := (hQ.const_mul_left (legBdK a b)).mul (Asymptotics.isBigO_refl
      (fun t : ℝ => (Real.log t : ℂ)) (𝓝[>] 0))
    refine (h1.congr_left fun t => by simp only [Function.comp_apply]; ring).trans ?_
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    simp [norm_mul]
  have hH' := hH.trans legBd_isBigO_self_mul_log
  refine ((hH'.sub hlog).congr' ?_ (EventuallyEq.refl _ _))
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  have hz : ‖((1-t:ℝ):ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have hw : ‖1 - ((1-t:ℝ):ℂ)‖ < 1 := by
    rw [show 1 - ((1-t:ℝ):ℂ) = ((t:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have e := legBd_zeroBalanced_eq a b hz hw
  rw [show 1 - ((1-t:ℝ):ℂ) = ((t:ℝ):ℂ) by push_cast; ring, ← ofReal_log ht.1.le] at e
  simp only [Function.comp_apply]
  rw [show (1:ℂ) - (t:ℂ) = ((1-t:ℝ):ℂ) by push_cast; ring,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz, e]
  ring

/-- The derivative of the duplication formula for `1/Γ`:
`(√π/2^(s+1)) K'((s+2)/2,(s+1)/2) = (1/Γ)'(s+1) + ln 2 / Γ(s+1)`. -/
theorem legBd_duplication_deriv (s : ℂ) :
    (Real.sqrt π : ℂ) / 2^(s+1) * legBdK' ((s+2)/2) ((s+1)/2) =
      recipGammaDeriv 1 (s+1) + Real.log 2 * (Gamma (s+1))⁻¹ := by
  have hfun : (fun u : ℂ => (Gamma (u+1))⁻¹) = fun u =>
      (Gamma ((u+1)/2))⁻¹*(Gamma ((u+2)/2))⁻¹*2^(-u)*(Real.sqrt π:ℂ) :=
    funext legendre_recip_duplication
  have hL : HasDerivAt (fun u : ℂ => (Gamma (u+1))⁻¹) (recipGammaDeriv 1 (s+1)) s := by
    have := (hasDerivAt_recip_Gamma' (s+1)).comp s ((hasDerivAt_id s).add_const 1)
    simpa [Function.comp_def] using this
  have h1 : HasDerivAt (fun u : ℂ => (Gamma ((u+1)/2))⁻¹) (recipGammaDeriv 1 ((s+1)/2) * (1/2)) s := by
    have hi : HasDerivAt (fun u : ℂ => (u+1)/2) (1/2) s := by
      simpa using ((hasDerivAt_id s).add_const (1:ℂ)).div_const 2
    exact (hasDerivAt_recip_Gamma' _).comp s hi
  have h2 : HasDerivAt (fun u : ℂ => (Gamma ((u+2)/2))⁻¹) (recipGammaDeriv 1 ((s+2)/2) * (1/2)) s := by
    have hi : HasDerivAt (fun u : ℂ => (u+2)/2) (1/2) s := by
      simpa using ((hasDerivAt_id s).add_const (2:ℂ)).div_const 2
    exact (hasDerivAt_recip_Gamma' _).comp s hi
  have h3 : HasDerivAt (fun u : ℂ => (2:ℂ)^(-u)) ((2:ℂ)^(-s) * log 2 * (-1)) s :=
    (hasDerivAt_neg s).const_cpow (Or.inl (by norm_num))
  have hR := ((h1.mul h2).mul h3).mul_const (Real.sqrt π:ℂ)
  rw [hfun] at hL
  have hk := hL.unique hR
  simp only [Pi.mul_apply] at hk
  have hd := legendre_recip_duplication s
  have hl2 : log (2:ℂ) = (Real.log 2 : ℂ) := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ofReal_log (by norm_num)]
  have h2s : (2:ℂ)^(s+1) = 2 * 2^s := by
    rw [cpow_add _ _ (by norm_num), cpow_one]; ring
  have h2n : (2:ℂ)^(-s) = (2^s)⁻¹ := cpow_neg _ _
  have h2z : (2:ℂ)^s ≠ 0 := by simp
  rw [hk, hd, legBdK', h2s, h2n]
  rw [h2n, hl2] at *
  field_simp
  ring

/-- Comparison of logarithmic scales: if `s ≤ t ≤ 2s` with `0 < s` and `t < 1` eventually, then
`ln t = O(ln s)` and `t ln t = O(s ln s)`. -/
theorem legBd_log_comparison {l : Filter ℝ} {s t : ℝ → ℝ}
    (h : ∀ᶠ x in l, 0 < s x ∧ s x ≤ t x ∧ t x ≤ 2 * s x ∧ t x < 1) :
    (fun x => (Real.log (t x) : ℂ)) =O[l] (fun x => Real.log (s x)) ∧
    (fun x => t x * Real.log (t x)) =O[l] (fun x => s x * Real.log (s x)) := by
  have hb : ∀ᶠ x in l, |Real.log (t x)| ≤ |Real.log (s x)| := by
    filter_upwards [h] with x ⟨h0, h1, h2, h3⟩
    have ht0 : 0 < t x := lt_of_lt_of_le h0 h1
    have hlt : Real.log (t x) < 0 := Real.log_neg ht0 h3
    have hls : Real.log (s x) ≤ Real.log (t x) := Real.log_le_log h0 h1
    rw [abs_of_neg hlt, abs_of_neg (lt_of_le_of_lt hls hlt)]; linarith
  constructor
  · refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hb] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, one_mul]; exact hx
  · refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [hb, h] with x hx ⟨h0, h1, h2, h3⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos h0,
      abs_of_pos (lt_of_lt_of_le h0 h1)]
    nlinarith [abs_nonneg (Real.log (t x)), abs_nonneg (Real.log (s x))]

/-- `x - 1 → 0⁺` as `x → 1⁺`. -/
theorem legBd_tendsto_sub_one_nhdsGT :
    Tendsto (fun x : ℝ => x - 1) (𝓝[>] (1:ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := ((continuous_sub_right (1:ℝ)).tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    simp only [mem_Ioi, sub_pos]; exact hx

/-- `1 - 1/x² → 0⁺` as `x → 1⁺`. -/
theorem legBd_tendsto_one_sub_recip_sq_nhdsGT :
    Tendsto (fun x : ℝ => 1 - 1/x^2) (𝓝[>] (1:ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := ((by fun_prop (disch := norm_num) : ContinuousAt (fun x : ℝ => 1 - 1/x^2) 1).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi 1))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    simp only [mem_Ioi, sub_pos]
    rw [div_lt_one (by positivity)]; nlinarith

/-- DLMF 14.8.9 with `ψ(ν+1)/Γ(ν+1)` written as `-(1/Γ)'(ν+1)`, for all `ν`. -/
theorem legBd_olverQ_log_isBigO (ν : ℂ) :
    (fun x : ℝ => olverQ ν 0 x+log (x-1:ℂ)/(2*Gamma (ν+1))-(log 2/2-Real.eulerMascheroniConstant)/Gamma (ν+1)-DLMF.Gamma.recipGammaDeriv 1 (ν+1)) =O[𝓝[>] (1:ℝ)] (fun x : ℝ => (x-1)*Real.log (x-1)) := by
  set a : ℂ := (ν+0+2)/2 with ha
  set b : ℂ := (ν+0+1)/2 with hb
  set K := legBdK a b with hK
  set K' := legBdK' a b with hK'
  set γ : ℂ := (Real.eulerMascheroniConstant : ℂ) with hγ
  set p : ℝ → ℂ := fun x => (Real.sqrt π : ℂ) / (2^(ν+1) * (x:ℂ)^(ν+0+1)) with hp
  set p0 : ℂ := (Real.sqrt π : ℂ) / 2^(ν+1) with hp0
  have hsq : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2n : (2:ℂ)^(ν+1) ≠ 0 := by simp
  -- constants
  have hpK : p0 * K = 1 / (2 * Gamma (ν+1)) := by
    have hd := legBd_recip_half_Gammas ν
    have e : K = (Gamma ((ν+1)/2))⁻¹ * (Gamma ((ν+2)/2))⁻¹ := by
      rw [hK, legBdK, ha, hb]; ring_nf
    rw [e, hd, hp0, show (2:ℂ)^(ν+1) = 2 * 2^ν by rw [cpow_add _ _ (by norm_num), cpow_one]; ring]
    have : (2:ℂ)^ν ≠ 0 := by simp
    field_simp
  have hpK' : p0 * K' = DLMF.Gamma.recipGammaDeriv 1 (ν+1) + Real.log 2 * (Gamma (ν+1))⁻¹ := by
    have := legBd_duplication_deriv ν
    rw [hp0, hK', ha, hb, show (ν+0+2)/2 = (ν+2)/2 by ring, show (ν+0+1)/2 = (ν+1)/2 by ring]
    exact this
  -- the pieces
  have hZ := ((legBd_zeroBalanced_isBigO a b).comp_tendsto legBd_tendsto_one_sub_recip_sq_nhdsGT)
  have hcmp := legBd_log_comparison (l := 𝓝[>] (1:ℝ)) (s := fun x => x - 1) (t := fun x => 1 - 1/x^2)
    (by
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (1:ℝ) < 3/2 by norm_num)] with x
        (hx : 1 < x) hx2
      have h0 : (0:ℝ) < x := by linarith
      have e : 1 - 1/x^2 = (x-1)*((x+1)/x^2) := by field_simp; ring
      refine ⟨by linarith, ?_, ?_, ?_⟩
      · rw [e]; have : 1 ≤ (x+1)/x^2 := by rw [le_div_iff₀ (by positivity)]; nlinarith [hx2.2]
        nlinarith
      · rw [e]; have : (x+1)/x^2 ≤ 2 := by rw [div_le_iff₀ (by positivity)]; nlinarith
        nlinarith
      · have : 0 < 1/x^2 := by positivity
        linarith)
  have hS := legBd_isBigO_self_mul_log.comp_tendsto legBd_tendsto_sub_one_nhdsGT
  -- p - p0 = O(x-1)
  have hpd : DifferentiableAt ℝ p 1 := by
    have : DifferentiableAt ℂ (fun z : ℂ => (Real.sqrt π : ℂ) / (2^(ν+1) * z^(ν+0+1)))
        ((1:ℝ):ℂ) := by
      refine DifferentiableAt.div (differentiableAt_const _) ((differentiableAt_const _).mul
        ((differentiableAt_id).cpow (differentiableAt_const _) (by norm_num))) (by simp)
    exact (this.hasDerivAt.comp_ofReal).differentiableAt
  have hp1 : p 1 = p0 := by simp [hp, hp0]
  have hpO : (fun x => p x - p0) =O[𝓝[>] (1:ℝ)] (fun x : ℝ => x - 1) := by
    rw [← hp1]; exact hpd.isBigO_sub.mono nhdsWithin_le_nhds
  -- log((x+1)/x²) - log 2 = O(x-1)
  set g : ℝ → ℂ := fun x => (Real.log ((x+1)/x^2) : ℂ) with hg
  have hgd : DifferentiableAt ℝ g 1 := by
    have : DifferentiableAt ℝ (fun x : ℝ => Real.log ((x+1)/x^2)) 1 :=
      ((by fun_prop (disch := norm_num) : DifferentiableAt ℝ (fun x : ℝ => (x+1)/x^2) 1)).log
        (by norm_num)
    exact (ofRealCLM.differentiableAt.comp _ this)
  have hg1 : g 1 = (Real.log 2 : ℂ) := by simp [hg]; norm_num
  have hgO : (fun x => g x - Real.log 2) =O[𝓝[>] (1:ℝ)] (fun x : ℝ => x - 1) := by
    rw [← hg1]; exact hgd.isBigO_sub.mono nhdsWithin_le_nhds
  -- boundedness of p near 1
  have hpb : (fun x => p x) =O[𝓝[>] (1:ℝ)] (fun _ => (1:ℝ)) :=
    (hpd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  have hS' : (fun x : ℝ => x - 1) =O[𝓝[>] (1:ℝ)] (fun x : ℝ => (x-1)*Real.log (x-1)) := by
    have := Asymptotics.isBigO_norm_left.mpr hS
    simp only [Function.comp_apply, Complex.norm_real] at this
    exact Asymptotics.isBigO_norm_left.mp this
  set L : ℝ → ℂ := fun x => (Real.log (1 - 1/x^2) : ℂ) with hL
  set E : ℝ → ℂ := fun x => regularizedGaussHG a b (a+b) (1 - ((1-1/x^2:ℝ):ℂ)) +
    K * Real.log (1 - 1/x^2) - (K' - 2 * γ * K) with hE
  have hEO : E =O[𝓝[>] (1:ℝ)] (fun x : ℝ => (x-1)*Real.log (x-1)) := hZ.trans hcmp.2
  set R : ℝ → ℝ := fun x => (x-1)*Real.log (x-1) with hR
  have t1 : (fun x => p x * E x) =O[𝓝[>] (1:ℝ)] R :=
    (hpb.mul hEO).congr_right (fun x => one_mul _)
  have t2 : (fun x => (p x - p0) * (-K * L x)) =O[𝓝[>] (1:ℝ)] R :=
    hpO.mul (hcmp.1.const_mul_left (-K))
  have t3 : (fun x => (p x - p0) * (K' - 2*γ*K)) =O[𝓝[>] (1:ℝ)] R :=
    ((hpO.const_mul_left (K' - 2*γ*K)).congr_left (fun x => mul_comm _ _)).trans hS'
  have t4 : (fun x => p0 * K * (g x - Real.log 2)) =O[𝓝[>] (1:ℝ)] R :=
    (hgO.const_mul_left (p0*K)).trans hS'
  refine (((t1.add t2).add t3).sub t4).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  have h0 : (0:ℝ) < x := by linarith
  have h1 : (0:ℝ) < x - 1 := by linarith
  have hlogs : Real.log (1 - 1/x^2) = Real.log (x-1) + Real.log ((x+1)/x^2) := by
    rw [← Real.log_mul h1.ne' (by positivity)]; congr 1; field_simp; ring
  have hcl : log ((x:ℂ)-1) = (Real.log (x-1) : ℂ) := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring, ofReal_log h1.le]
  have hl2 : log (2:ℂ) = (Real.log 2 : ℂ) := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ofReal_log (by norm_num)]
  have hO : olverQ ν 0 x = p x * regularizedGaussHG a b (a+b) (1 - ((1-1/x^2:ℝ):ℂ)) := by
    simp only [olverQ, legendreBranchPower, zero_div, zero_mul, Complex.exp_zero, mul_one, hp]
    rw [show (1:ℂ) - ((1-1/x^2:ℝ):ℂ) = 1/(x:ℂ)^2 by push_cast; ring,
      show a + b = ν + 3/2 by rw [ha, hb]; ring, ha, hb]
  simp only [hE, hL, hg]
  rw [hO, hcl, hl2, hlogs]
  push_cast
  linear_combination ((Real.log (x-1) : ℂ) + 2*γ + Real.log 2) * hpK - hpK'

/-- The derivative of the reflection formula for `1/Γ`:
`π((1/Γ)'(s)/Γ(1-s) - (1/Γ)'(1-s)/Γ(s)) = π cos(πs)`. -/
theorem legBd_reflection_deriv (s : ℂ) :
    π * (recipGammaDeriv 1 s * (Gamma (1-s))⁻¹ - (Gamma s)⁻¹ * recipGammaDeriv 1 (1-s)) =
      π * cos (π * s) := by
  have hfun : (fun u : ℂ => π*((Gamma u)⁻¹*(Gamma (1-u))⁻¹)) = fun u => sin (π*u) :=
    funext legendre_recip_Gamma_reflection
  have h1 := hasDerivAt_recip_Gamma' s
  have h2 : HasDerivAt (fun u : ℂ => (Gamma (1-u))⁻¹) (recipGammaDeriv 1 (1-s) * (-1)) s := by
    have hi : HasDerivAt (fun u : ℂ => 1-u) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (1:ℂ)
    exact (hasDerivAt_recip_Gamma' _).comp s hi
  have hL := (h1.mul h2).const_mul (π:ℂ)
  have hR : HasDerivAt (fun u : ℂ => sin (π*u)) (cos (π*s) * (π*1)) s :=
    ((hasDerivAt_id s).const_mul (π:ℂ)).csin
  simp only [Pi.mul_apply] at hL
  rw [hfun] at hL
  have := hL.unique hR
  linear_combination this

/-- Constants of the logarithmic expansion of `𝖰_ν` at `x = 1`: with
`A₁ = -(π/2) sin(νπ/2) Γ((ν+1)/2)/Γ((ν+2)/2)` and `A₂ = (π/2) cos(νπ/2) Γ((ν+2)/2)/Γ((ν+1)/2)`,
`A₁K₁ + A₂K₂ = 1/2` and `A₁K₁' + A₂K₂' = ln 2 - ψ(ν+1)`. -/
theorem legBd_ferrersQ_consts {ν : ℂ} (h : LegendreQRegular ν 0) :
    -π/2*sin (ν*π/2)*(Gamma ((ν+1)/2)/Gamma ((ν+2)/2)) * legBdK (-ν/2) ((ν+1)/2) +
      π/2*cos (ν*π/2)*(Gamma ((ν+2)/2)/Gamma ((ν+1)/2)) * legBdK ((1-ν)/2) ((ν+2)/2) = 1/2 ∧
    -π/2*sin (ν*π/2)*(Gamma ((ν+1)/2)/Gamma ((ν+2)/2)) * legBdK' (-ν/2) ((ν+1)/2) +
      π/2*cos (ν*π/2)*(Gamma ((ν+2)/2)/Gamma ((ν+1)/2)) * legBdK' ((1-ν)/2) ((ν+2)/2) =
      Real.log 2 - digamma (ν+1) := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero (μ := 0) h
  simp only [add_zero] at hg1 hg2
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  set S := sin (ν*π/2) with hS
  set C := cos (ν*π/2) with hC
  set G1 := Gamma ((ν+1)/2) with hG1
  set G2 := Gamma ((ν+2)/2) with hG2
  have ro := legendre_reflection_odd ν
  have re := legendre_reflection_even ν
  rw [show -ν/2 = -ν/2 from rfl] at ro
  -- α = Γ(-ν/2)⁻¹, β = Γ((1-ν)/2)⁻¹
  have hα : (Gamma (-ν/2))⁻¹ = -S * G2 / π := by
    rw [eq_div_iff hpi]
    have k : G2 * G2⁻¹ = 1 := mul_inv_cancel₀ hg2
    linear_combination G2 * ro - π * (Gamma (-ν/2))⁻¹ * k
  have hβ : (Gamma ((1-ν)/2))⁻¹ = C * G1 / π := by
    rw [eq_div_iff hpi]
    have k : G1 * G1⁻¹ = 1 := mul_inv_cancel₀ hg1
    linear_combination G1 * re - π * (Gamma ((1-ν)/2))⁻¹ * k
  constructor
  · simp only [legBdK]
    rw [hα, hβ]
    have hpy := sin_sq_add_cos_sq (ν*π/2)
    rw [← hS, ← hC] at hpy
    have k1 : G1 * G1⁻¹ = 1 := mul_inv_cancel₀ hg1
    have k2 : G2 * G2⁻¹ = 1 := mul_inv_cancel₀ hg2
    field_simp
    linear_combination hpy + S^2 * k1 + C^2 * k2
  · set Db1 := recipGammaDeriv 1 ((ν+1)/2) with hDb1
    set Db2 := recipGammaDeriv 1 ((ν+2)/2) with hDb2
    have hν1 : ∀ m : ℕ, ν + 1 ≠ -(m:ℂ) := fun m hm => h m (by linear_combination hm)
    have hΓn : Gamma (ν+1) ≠ 0 := Gamma_ne_zero hν1
    -- derivative of the reflection formula at `-ν/2` and `(1-ν)/2`
    have d1 := legBd_reflection_deriv (-ν/2)
    rw [show (1:ℂ) - -ν/2 = (ν+2)/2 by ring, show (π:ℂ) * (-ν/2) = -(ν*π/2) by ring, cos_neg,
      ← hC, ← hG2, ← hDb2] at d1
    have d2 := legBd_reflection_deriv ((1-ν)/2)
    rw [show (1:ℂ) - (1-ν)/2 = (ν+1)/2 by ring,
      show (π:ℂ) * ((1-ν)/2) = π/2 - ν*π/2 by ring, cos_pi_div_two_sub, ← hS, ← hG1, ← hDb1] at d2
    have hDa1 : recipGammaDeriv 1 (-ν/2) = (C + (Gamma (-ν/2))⁻¹ * Db2) * G2 := by
      have k : G2⁻¹ * G2 = 1 := inv_mul_cancel₀ hg2
      have : recipGammaDeriv 1 (-ν/2) * G2⁻¹ - (Gamma (-ν/2))⁻¹ * Db2 = C :=
        mul_left_cancel₀ hpi d1
      linear_combination G2 * this - recipGammaDeriv 1 (-ν/2) * k
    have hDa2 : recipGammaDeriv 1 ((1-ν)/2) = (S + (Gamma ((1-ν)/2))⁻¹ * Db1) * G1 := by
      have k : G1⁻¹ * G1 = 1 := inv_mul_cancel₀ hg1
      have : recipGammaDeriv 1 ((1-ν)/2) * G1⁻¹ - (Gamma ((1-ν)/2))⁻¹ * Db1 = S :=
        mul_left_cancel₀ hpi d2
      linear_combination G1 * this - recipGammaDeriv 1 ((1-ν)/2) * k
    -- the duplication data
    have hkey : G1 * Db1 + G2 * Db2 = 2 * (Real.log 2 - digamma (ν+1)) := by
      have dup' := legBd_duplication_deriv ν
      have dup := legendre_recip_duplication ν
      have psi := recipGammaDeriv_one_eq hν1
      have hsq : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
      have h2 : (2:ℂ)^ν ≠ 0 := by simp
      have hne : (Real.sqrt π:ℂ) / (2^ν * G1 * G2) ≠ 0 := by
        exact div_ne_zero hsq (mul_ne_zero (mul_ne_zero h2 hg1) hg2)
      apply mul_left_cancel₀ hne
      rw [legBdK', psi, dup,
        show (2:ℂ)^(ν+1) = 2 * 2^ν by rw [cpow_add _ _ (by norm_num), cpow_one]; ring,
        cpow_neg, ← hDb1, ← hDb2, ← hG1, ← hG2] at dup'
      clear_value G1 G2 Db1 Db2
      field_simp at dup' ⊢
      linear_combination dup'
    simp only [legBdK']
    rw [hDa1, hDa2, hα, hβ, ← hDb1, ← hDb2, ← hG1, ← hG2]
    have hpy := sin_sq_add_cos_sq (ν*π/2)
    rw [← hS, ← hC] at hpy
    clear_value S C G1 G2 Db1 Db2
    field_simp
    linear_combination (G1 * Db1 + G2 * Db2) * hpy + hkey

/-- `1 - x → 0⁺` as `x → 1⁻`. -/
theorem legBd_tendsto_one_sub_nhdsLT :
    Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1:ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun x : ℝ => 1 - x) (𝓝 1) (𝓝 (1-1)) := tendsto_const_nhds.sub tendsto_id
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Iio 1))
  · filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
    simp only [mem_Ioi, sub_pos]; exact hx

/-- `1 - x² → 0⁺` as `x → 1⁻`. -/
theorem legBd_tendsto_one_sub_sq_nhdsLT :
    Tendsto (fun x : ℝ => 1 - x^2) (𝓝[<] (1:ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := ((by fun_prop : Continuous fun x : ℝ => 1 - x^2).tendsto (1:ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  · filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
    simp only [mem_Ioi, sub_pos]; nlinarith [hx.1, hx.2]

/-- DLMF 14.8.3: `𝖰_ν(x) = ½ ln(2/(1-x)) - γ - ψ(ν+1) + O((1-x) ln(1-x))` as `x → 1⁻`. -/
theorem legBd_ferrersQ_log_isBigO {ν : ℂ} (hν : LegendreQRegular ν 0) :
    (fun x : ℝ => ferrersQ ν 0 x-1/2*log (2/(1-x):ℂ)+Real.eulerMascheroniConstant+digamma (ν+1)) =O[𝓝[<] (1:ℝ)] (fun x : ℝ => (1-x)*Real.log (1-x)) := by
  obtain ⟨hc1, hc2⟩ := legBd_ferrersQ_consts hν
  set a1 : ℂ := -ν/2 with ha1
  set b1 : ℂ := (ν+1)/2 with hb1
  set a2 : ℂ := (1-ν)/2 with ha2
  set b2 : ℂ := (ν+2)/2 with hb2
  set A1 : ℂ := -π/2*sin (ν*π/2)*(Gamma ((ν+1)/2)/Gamma ((ν+2)/2)) with hA1
  set A2 : ℂ := π/2*cos (ν*π/2)*(Gamma ((ν+2)/2)/Gamma ((ν+1)/2)) with hA2
  set K1 := legBdK a1 b1
  set K2 := legBdK a2 b2
  set K1' := legBdK' a1 b1
  set K2' := legBdK' a2 b2
  set γ : ℂ := (Real.eulerMascheroniConstant : ℂ) with hγ
  set R : ℝ → ℝ := fun x => (1-x)*Real.log (1-x) with hR
  set l := 𝓝[<] (1:ℝ) with hl
  have hcmp := legBd_log_comparison (l := l) (s := fun x => 1 - x) (t := fun x => 1 - x^2)
    (by
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x
        (hx : x < 1) hx0
      refine ⟨by linarith, by nlinarith [hx0.1], by nlinarith [hx0.1], by nlinarith [hx0.1]⟩)
  have hZ1 : (fun x : ℝ => regularizedGaussHG a1 b1 (a1+b1) (1 - ((1-x^2:ℝ):ℂ)) +
      K1 * Real.log (1-x^2) - (K1' - 2*γ*K1)) =O[l] R :=
    ((legBd_zeroBalanced_isBigO a1 b1).comp_tendsto legBd_tendsto_one_sub_sq_nhdsLT).trans hcmp.2
  have hZ2 : (fun x : ℝ => regularizedGaussHG a2 b2 (a2+b2) (1 - ((1-x^2:ℝ):ℂ)) +
      K2 * Real.log (1-x^2) - (K2' - 2*γ*K2)) =O[l] R :=
    ((legBd_zeroBalanced_isBigO a2 b2).comp_tendsto legBd_tendsto_one_sub_sq_nhdsLT).trans hcmp.2
  have hS := legBd_isBigO_self_mul_log.comp_tendsto legBd_tendsto_one_sub_nhdsLT
  have hS' : (fun x : ℝ => 1 - x) =O[l] R := by
    have := Asymptotics.isBigO_norm_left.mpr hS
    simp only [Function.comp_apply, Complex.norm_real] at this
    exact Asymptotics.isBigO_norm_left.mp this
  have hxm : (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) =O[l] (fun x : ℝ => 1 - x) := by
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_sub_comm]
  have hxb : (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) =O[l] (fun _ => (1:ℝ)) :=
    (((by fun_prop : Continuous fun x : ℝ => ((x-1:ℝ):ℂ)).tendsto 1).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  -- log(1+x) - log 2 = O(x-1)
  set g : ℝ → ℂ := fun x => (Real.log (1+x) : ℂ) with hg
  have hgd : DifferentiableAt ℝ g 1 := by
    have : DifferentiableAt ℝ (fun x : ℝ => Real.log (1+x)) 1 :=
      ((by fun_prop : DifferentiableAt ℝ (fun x : ℝ => 1+x) 1)).log (by norm_num)
    exact (ofRealCLM.differentiableAt.comp _ this)
  have hg1 : g 1 = (Real.log 2 : ℂ) := by simp [hg]; norm_num
  have hgO : (fun x => g x - Real.log 2) =O[l] (fun x : ℝ => 1 - x) := by
    rw [← hg1]
    refine (hgd.isBigO_sub.mono nhdsWithin_le_nhds).trans ?_
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_sub_comm]
  set L : ℝ → ℂ := fun x => (Real.log (1 - x^2) : ℂ) with hL
  set E2 : ℝ → ℂ := fun x => regularizedGaussHG a2 b2 (a2+b2) (1 - ((1-x^2:ℝ):ℂ)) +
      K2 * Real.log (1-x^2) - (K2' - 2*γ*K2) with hE2
  have t1 := hZ1.const_mul_left A1
  have t2 := hZ2.const_mul_left A2
  have t3 : (fun x => A2 * (((x-1:ℝ):ℂ) * (-K2 * L x))) =O[l] R :=
    ((hxm.mul (hcmp.1.const_mul_left (-K2))).const_mul_left A2)
  have t4 : (fun x => A2 * (((x-1:ℝ):ℂ) * (K2' - 2*γ*K2))) =O[l] R :=
    (((hxm.const_mul_left (K2' - 2*γ*K2)).congr_left (fun x => mul_comm _ _)).trans hS').const_mul_left A2
  have t5 : (fun x => A2 * (((x-1:ℝ):ℂ) * E2 x)) =O[l] R :=
    ((hxb.mul hZ2).congr_right (fun x => one_mul _)).const_mul_left A2
  have t6 : (fun x => (1/2:ℂ) * (g x - Real.log 2)) =O[l] R := (hgO.const_mul_left _).trans hS'
  refine (((((t1.add t2).add t3).add t4).add t5).sub t6).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x
    (hx : x < 1) hx0
  have h1x : (0:ℝ) < 1 - x := by linarith
  have h1x' : (0:ℝ) < 1 + x := by linarith [hx0.1]
  have hsq : ((1 - ((1-x^2:ℝ):ℂ))) = ((x:ℂ))^2 := by push_cast; ring
  have hQ : ferrersQ ν 0 x = A1 * regularizedGaussHG a1 b1 (a1+b1) (1 - ((1-x^2:ℝ):ℂ)) +
      A2 * (x:ℂ) * regularizedGaussHG a2 b2 (a2+b2) (1 - ((1-x^2:ℝ):ℂ)) := by
    rw [hsq, show a1 + b1 = 1/2 by rw [ha1, hb1]; ring, show a2 + b2 = 3/2 by rw [ha2, hb2]; ring]
    simp only [ferrersQ, ferrersW1, ferrersW2, add_zero, sub_zero, neg_zero, zero_div,
      cpow_zero, mul_one, ha1, hb1, ha2, hb2, hA1, hA2, neg_div]
    ring_nf
  have hlog : log (2/(1-x):ℂ) = (Real.log 2 : ℂ) - Real.log (1-x) := by
    rw [show (2/(1-x):ℂ) = ((2/(1-x):ℝ):ℂ) by push_cast; rfl, ← ofReal_log (by positivity),
      Real.log_div (by norm_num) h1x.ne']
    push_cast; ring
  have hLx : L x = (Real.log (1-x) : ℂ) + g x := by
    simp only [hL, hg]
    rw [show 1 - x^2 = (1-x)*(1+x) by ring, Real.log_mul h1x.ne' h1x'.ne']
    push_cast; ring
  simp only [hE2]
  have hx1 : ((x-1:ℝ):ℂ) = (x:ℂ) - 1 := by push_cast; ring
  rw [hQ, hlog, hx1]
  linear_combination (L x + 2*γ) * hc1 - hc2 + (1/2:ℂ) * hLx

end ZeroBalanced

end DLMF.Legendre
