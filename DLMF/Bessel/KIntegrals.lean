/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Relations
public import DLMF.Confluent.IntegralRepresentations

/-!
# Laplace-type integrals for `K_ν` (DLMF 10.32.8)

Kummer's relation `U(ν+½, 2ν+1, 2z) = π^{-1/2} eᶻ (2z)^{-ν} K_ν(z)` (DLMF 13.6.10) and the
Laplace integral for `U` (DLMF 13.4.4) give, for `Re ν > -½` and `Re z > 0`,

`K_ν(z) = √π (2z)^ν e^{-z} / Γ(ν+½) ∫₀^∞ e^{-2zt} t^{ν-½} (1+t)^{ν-½} dt`,

and the substitution `u = 1 + 2t` turns this into DLMF 10.32.8,

`K_ν(z) = √π (z/2)^ν / Γ(ν+½) ∫₁^∞ e^{-zu} (u²-1)^{ν-½} du`.
-/

@[expose] public section

open Complex MeasureTheory Set DLMF.Confluent
open scoped Real

noncomputable section

namespace DLMF.Bessel

/-- The Tricomi form of the Laplace integral for `K_ν`. -/
theorem besselK_eq_integral_tricomi {ν z : ℂ} (hν : -1 / 2 < ν.re) (hz : 0 < z.re) :
    besselK ν z = (Real.sqrt π : ℂ) * (2 * z) ^ ν * exp (-z) / Gamma (ν + 1 / 2) *
      ∫ t : ℝ in Ioi 0, exp (-(2 * z) * t) * (t : ℂ) ^ (ν - 1 / 2) *
        (1 + (t : ℂ)) ^ (ν - 1 / 2) := by
  have hzs : z ∈ slitPlane := Or.inl hz
  have h2z : 2 * z ≠ 0 := mul_ne_zero two_ne_zero (slitPlane_ne_zero hzs)
  have ha : 0 < (ν + 1 / 2).re := by simp; linarith
  have h2re : 0 < (2 * z).re := by simp; linarith
  have hU := kummerU_besselK ν z hzs
  rw [kummerU_laplace ha h2re] at hU
  have hexp : ν + 1 / 2 - 1 = ν - 1 / 2 := by ring
  have hexp' : 2 * ν + 1 - (ν + 1 / 2) - 1 = ν - 1 / 2 := by ring
  rw [hexp, hexp'] at hU
  have hsq : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpow : (2 * z) ^ ν * (2 * z) ^ (-ν) = 1 := by
    rw [cpow_neg, mul_inv_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl h2z))]
  set J := ∫ t : ℝ in Ioi 0, exp (-(2 * z) * t) * (t : ℂ) ^ (ν - 1 / 2) *
    (1 + (t : ℂ)) ^ (ν - 1 / 2)
  rw [show (Real.sqrt π : ℂ) * (2 * z) ^ ν * exp (-z) / Gamma (ν + 1 / 2) * J =
    (Real.sqrt π : ℂ) * (2 * z) ^ ν * exp (-z) * (1 / Gamma (ν + 1 / 2) * J) by ring, hU,
    exp_neg]
  have hE := exp_ne_zero z
  field_simp
  linear_combination (-besselK ν z) * hpow

/-- The affine substitution `u = 1 + 2t` on `(1, ∞)`. -/
theorem integral_Ioi_one_eq_two_mul (G : ℝ → ℂ) :
    ∫ u : ℝ in Ioi 1, G u = 2 * ∫ t : ℝ in Ioi 0, G (1 + 2 * t) := by
  have hscale := integral_comp_mul_left_Ioi (fun s => G (1 + s)) 0 (b := 2) two_pos
  rw [mul_zero] at hscale
  have hshift : ∫ s : ℝ in Ioi 0, G (1 + s) = ∫ u : ℝ in Ioi 1, G u := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    have h : ∀ s : ℝ, (Ioi (0 : ℝ)).indicator (fun s => G (1 + s)) s =
        (Ioi (1 : ℝ)).indicator G (1 + s) := by
      intro s
      by_cases hs : 0 < s
      · rw [indicator_of_mem (show s ∈ Ioi 0 from hs),
          indicator_of_mem (show 1 + s ∈ Ioi 1 by simp [hs])]
      · rw [indicator_of_notMem (show s ∉ Ioi 0 from hs),
          indicator_of_notMem (show 1 + s ∉ Ioi 1 by simpa using hs)]
    simp_rw [h]
    exact integral_add_left_eq_self (fun u => (Ioi (1 : ℝ)).indicator G u) 1
  rw [← hshift, hscale]
  simp

/-- Laplace-type integral `K_ν(z) = √π (z/2)^ν / Γ(ν+½) ∫₁^∞ e^{-zu} (u²-1)^{ν-½} du`
for `Re ν > -½` and `Re z > 0` (DLMF 10.32.8). -/
@[dlmf 10.32.E8]
theorem besselK_eq_integral_Ioi_one {ν z : ℂ} (hν : -1 / 2 < ν.re) (hz : 0 < z.re) :
    besselK ν z = (Real.sqrt π : ℂ) * (z / 2) ^ ν / Gamma (ν + 1 / 2) *
      ∫ u : ℝ in Ioi 1, exp (-z * u) * ((u : ℂ) ^ 2 - 1) ^ (ν - 1 / 2) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  rw [integral_Ioi_one_eq_two_mul, besselK_eq_integral_tricomi hν hz]
  have hint : ∫ t : ℝ in Ioi 0, exp (-z * ((1 + 2 * t : ℝ) : ℂ)) *
        ((((1 + 2 * t : ℝ)) : ℂ) ^ 2 - 1) ^ (ν - 1 / 2) =
      exp (-z) * (4 : ℂ) ^ (ν - 1 / 2) * ∫ t : ℝ in Ioi 0, exp (-(2 * z) * t) *
        (t : ℂ) ^ (ν - 1 / 2) * (1 + (t : ℂ)) ^ (ν - 1 / 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hsq : (((1 + 2 * t : ℝ)) : ℂ) ^ 2 - 1 = ((4 : ℝ) : ℂ) * ((t * (1 + t) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hsq, mul_cpow_ofReal_nonneg (by norm_num) (by positivity), ofReal_mul,
      mul_cpow_ofReal_nonneg ht0 (by linarith)]
    have he : exp (-z * ((1 + 2 * t : ℝ) : ℂ)) = exp (-z) * exp (-(2 * z) * t) := by
      rw [← exp_add]; push_cast; ring_nf
    rw [he]
    push_cast
    ring
  rw [hint]
  have h4 : (4 : ℂ) ^ (ν - 1 / 2) = (4 : ℂ) ^ ν / 2 := by
    rw [cpow_sub _ _ (by norm_num)]
    congr 1
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
      show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have h2z : (2 * z) ^ ν = (4 : ℂ) ^ ν * (z / 2) ^ ν := by
    rw [show 2 * z = ((4 : ℝ) : ℂ) * (z / 2) by push_cast; ring,
      ofReal_mul_cpow' (by norm_num) (div_ne_zero hz0 two_ne_zero)]
    norm_num
  rw [h4, h2z]
  ring

end DLMF.Bessel
