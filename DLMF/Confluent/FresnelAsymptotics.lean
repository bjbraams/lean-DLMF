/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.ErrorFunctions
public import DLMF.Confluent.TricomiRotated

/-!
# Auxiliary Fresnel functions and their asymptotics (Temme §7.3; DLMF 7.2.10, 7.5.10, 7.12.2)

The auxiliary functions `f, g` of DLMF 7.2.10–7.2.11 satisfy
`g(x) + i f(x) = (1+i)/2 · e^{ζ²} erfc ζ` with `ζ = √π (1-i) x / 2` (DLMF 7.5.10), and hence
`g(x) + i f(x) = (1+i)/(2√π) · U(1/2, 1/2, ζ²)`. Since `ζ² = -iπx²/2` lies on the negative
imaginary axis, Tricomi's expansion in the rotated sector of `DLMF.Confluent.TricomiRotated`
(rotation angle `π/4`) gives the asymptotic expansion of `g + i f` as `x → +∞`; the real and
imaginary parts are DLMF 7.12.2 and 7.12.3.

## Main results

* `fresnelAuxG_add_I_mul_fresnelAuxF`: DLMF 7.5.10.
* `hasAsymptoticExpansion_fresnelAuxG_add_I_mul_fresnelAuxF`:
  `g(x) + i f(x) ~ ∑ i (-i)^m (1/2)_m (2/π)^m / (π x^{2m+1})`.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics Set
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- The auxiliary Fresnel function `f(x) = (1/2 - S(x)) cos(πx²/2) - (1/2 - C(x)) sin(πx²/2)`
(DLMF 7.2.10). -/
@[dlmf 7.2.E10]
def fresnelAuxF (x : ℝ) : ℝ :=
  (1 / 2 - Real.fresnelSinInt x) * Real.cos (π * x ^ 2 / 2) - (1 / 2 - Real.fresnelCosInt x)
      * Real.sin (π * x ^ 2 / 2)

/-- The auxiliary Fresnel function `g(x) = (1/2 - C(x)) cos(πx²/2) + (1/2 - S(x)) sin(πx²/2)`
(DLMF 7.2.11). -/
@[dlmf 7.2.E11]
def fresnelAuxG (x : ℝ) : ℝ :=
  (1 / 2 - Real.fresnelCosInt x) * Real.cos (π * x ^ 2 / 2) + (1 / 2 - Real.fresnelSinInt x)
      * Real.sin (π * x ^ 2 / 2)

/-- The Fresnel variable `ζ = √π (1 - i) x / 2` of DLMF 7.5.7. -/
def fresnelZeta (x : ℝ) : ℂ := (Real.sqrt π : ℂ) * (1 - I) / 2 * x

/-- `ζ(x)² = -iπx²/2` for `ζ(x) = √π (1-i) x / 2`. -/
theorem fresnelZeta_sq (x : ℝ) : fresnelZeta x ^ 2 = -(I * (π * x ^ 2 / 2)) := by
  have hπ : (Real.sqrt π : ℂ) ^ 2 = π := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  rw [fresnelZeta, mul_pow, div_pow, mul_pow, hπ]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The auxiliary functions through `erfc`** (DLMF 7.5.10, upper signs):
`g(x) + i f(x) = (1+i)/2 · e^{ζ²} erfc ζ`. -/
@[dlmf 7.5.E10]
theorem fresnelAuxG_add_I_mul_fresnelAuxF (x : ℝ) :
    (fresnelAuxG x : ℂ) + I * fresnelAuxF x =
      (1 + I) / 2 * exp (fresnelZeta x ^ 2) * erfc (fresnelZeta x) := by
  have hCS := Real.fresnelCosInt_add_I_mul_fresnelSinInt x
  rw [show (Real.sqrt π : ℂ) * (1 - I) / 2 * x = fresnelZeta x from rfl] at hCS
  rw [erfc, fresnelZeta_sq, show -(I * ((π : ℂ) * (x : ℂ) ^ 2 / 2)) =
    ((-(π * x ^ 2 / 2) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, fresnelAuxG,
    fresnelAuxF]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_neg]
  generalize (Real.cos (π * x ^ 2 / 2) : ℂ) = c at *
  generalize (Real.sin (π * x ^ 2 / 2) : ℂ) = sn at *
  linear_combination (-(c - I * sn)) * hCS + (sn / 2 - sn * Real.fresnelSinInt x) * Complex.I_sq

/-- `Re ζ(x) = √π x / 2`. -/
theorem re_fresnelZeta (x : ℝ) : (fresnelZeta x).re = Real.sqrt π / 2 * x := by
  simp [fresnelZeta]

/-- As `x → +∞`, `ζ(x)²` tends to infinity in the sector of half-opening `1/2` about the direction
`π/4`. -/
theorem tendsto_fresnelZeta_sq :
    Tendsto (fun x : ℝ => fresnelZeta x ^ 2) atTop (rotSectorAtTop (1 / 2) (π / 4)) := by
  refine tendsto_comap_iff.mpr ?_
  have hval : ∀ x : ℝ, fresnelZeta x ^ 2 * exp ((π / 4 : ℝ) * I) =
      ((π * x ^ 2 / 2 * (Real.sqrt 2 / 2) : ℝ) : ℂ) * (1 - I) := by
    intro x
    rw [fresnelZeta_sq, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast
    linear_combination (-(π * x ^ 2 / 2 * (Real.sqrt 2 / 2)) : ℂ) * Complex.I_sq
  have hnorm : ∀ x : ℝ, ‖fresnelZeta x ^ 2 * exp ((π / 4 : ℝ) * I)‖ = π * x ^ 2 / 2 := by
    intro x
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, fresnelZeta_sq, norm_neg, norm_mul,
      Complex.norm_I, one_mul,
      show (π : ℂ) * x ^ 2 / 2 = ((π * x ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · simp only [Function.comp_def, hnorm]
    refine Tendsto.atTop_div_const (by norm_num) (Tendsto.const_mul_atTop Real.pi_pos ?_)
    exact tendsto_pow_atTop two_ne_zero
  · refine Eventually.of_forall fun x => ?_
    simp only [Function.comp_apply, Set.mem_ofPred_eq]
    rw [hnorm, hval]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.one_re, Complex.I_re, Complex.sub_im, Complex.one_im, Complex.I_im]
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    have : 0 ≤ π * x ^ 2 / 2 := by positivity
    nlinarith

/-- **Asymptotic expansion of the auxiliary Fresnel functions** (DLMF 7.12.2–7.12.3, combined):
`g(x) + i f(x) ~ ∑ i (-i)^m (1/2)_m (2/π)^m / (π x^{2m+1})` as `x → +∞`. -/
@[dlmf 7.12.E2]
theorem hasAsymptoticExpansion_fresnelAuxG_add_I_mul_fresnelAuxF :
    HasAsymptoticExpansion atTop (fun (m : ℕ) (x : ℝ) => (((x : ℂ) ^ (2 * m + 1))⁻¹))
      (fun m => I * (-I) ^ m * poch (1 / 2) m * (2 / π) ^ m / π)
      (fun x => (fresnelAuxG x : ℂ) + I * fresnelAuxF x) := by
  set c : ℂ := (Real.sqrt π : ℂ) * (1 - I) / 2 with hc
  have hsπ : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsπ2 : (Real.sqrt π : ℂ) ^ 2 = π := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc0 : c ≠ 0 := by
    rw [hc]; refine div_ne_zero (mul_ne_zero hsπ ?_) two_ne_zero
    intro h; have := congrArg im h; simp at this
  have hc2 : c ^ 2 = -(I * (π / 2)) := by
    rw [hc, div_pow, mul_pow, hsπ2]; ring_nf; rw [Complex.I_sq]; ring
  have hU := (hasAsymptoticExpansion_kummerU_rotSector (1 / 2) (1 / 2) (δ := 1 / 2)
    (α := π / 4) (by norm_num)
    (by rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos])).comp_tendsto
    tendsto_fresnelZeta_sq
  have hU2 := (hU.smul_scale (ψ := fun (m : ℕ) (x : ℝ) => (((x : ℂ) ^ (2 * m + 1))⁻¹))
    (κ := fun m => (c ^ (2 * m + 1))⁻¹) fun m => ?_).const_smul ((1 + I) / (2 * Real.sqrt π))
  · refine (hU2.congr' ?_).congr_coeff ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      have hre : 0 < (fresnelZeta x).re := by rw [re_fresnelZeta]; positivity
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
      rw [kummerU_erfc (Complex.mem_slitPlane_iff.mpr (Or.inl hre)) hre,
        fresnelAuxG_add_I_mul_fresnelAuxF]
      field_simp
    · funext m
      simp only [Pi.smul_apply, smul_eq_mul, tricomiCoeff]
      rw [show (1 / 2 : ℂ) - 1 / 2 + 1 = 1 by ring, poch_nat_one, pow_succ, pow_mul, hc2]
      have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
      have h1 : (-(I * (π / 2 : ℂ)))⁻¹ = 2 * I / π := by
        refine inv_eq_of_mul_eq_one_right ?_
        field_simp; ring_nf; rw [Complex.I_sq]; ring
      have h2 : (1 + I) / (2 * Real.sqrt π) * c⁻¹ = I / π := by
        have h1I : (1 - I) ≠ 0 := by intro h; have := congrArg im h; simp at this
        rw [hc, ← hsπ2]; field_simp; ring_nf; rw [Complex.I_sq]; ring
      calc (1 + I) / (2 * Real.sqrt π) * ((((-(I * (π / 2 : ℂ))) ^ m) * c)⁻¹ *
            ((-1) ^ m * poch (1 / 2) m * m.factorial / m.factorial))
          = ((1 + I) / (2 * Real.sqrt π) * c⁻¹) * ((-(I * (π / 2 : ℂ)))⁻¹ * (-1)) ^ m *
              poch (1 / 2) m := by
            rw [mul_inv, mul_pow, inv_pow]; field_simp
        _ = _ := by
            rw [h2, h1, show 2 * I / (π : ℂ) * -1 = -I * (2 / π) by ring, mul_pow]; ring
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hre : 0 < (fresnelZeta x).re := by rw [re_fresnelZeta]; positivity
    rw [sq_cpow_of_re_pos hre,
      show 2 * -((m : ℂ) + 1 / 2) = -((2 * m + 1 : ℕ) : ℂ) by push_cast; ring,
      cpow_neg, cpow_natCast, fresnelZeta, mul_pow, mul_inv]

end DLMF.Confluent
