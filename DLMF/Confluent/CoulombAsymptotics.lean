/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.TricomiRotated
public import DLMF.Coulomb.Basic

/-!
# Irregular Coulomb functions and their asymptotics (Temme §7.3.2; DLMF 33.2.8, 33.11.1)

The outgoing and incoming Coulomb functions are
`H^±_ℓ(η,ρ) = e^{±iθ_ℓ} (∓2iρ)^{ℓ+1±iη} U(ℓ+1±iη, 2ℓ+2, ∓2iρ)` (DLMF 33.2.8) with the phase
`θ_ℓ = ρ - η ln(2ρ) - ℓπ/2 + σ_ℓ(η)`, `σ_ℓ(η) = ph Γ(ℓ+1+iη)` (DLMF 33.2.9–33.2.10). We use the
principal phase for `σ_ℓ`; DLMF's continuous branch differs by a multiple of `2π`, which does not
change `e^{±iθ_ℓ}` and hence does not change `H^±_ℓ`.

The argument `∓2iρ` lies on the imaginary axis, where Tricomi's expansion holds by the rotated
sectors of `DLMF.Confluent.TricomiRotated`. This gives the asymptotic expansion DLMF 33.11.1.

## Main results

* `hasAsymptoticExpansion_cpow_mul_kummerU_rotSector`: `z^a U(a,b,z) ~ ∑ cₖ z^{-k}`.
* `hasAsymptoticExpansion_coulombHPlus`, `hasAsymptoticExpansion_coulombHMinus`:
  `e^{∓iθ_ℓ} H^±_ℓ(η,ρ) ~ ∑ (a)_k (b)_k / (k! (±2iρ)^k)` with `a = ±iη - ℓ`, `b = ±iη + ℓ + 1`.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics Set
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Tricomi's expansion normalized by its leading power: `z^a U(a,b,z) ~ ∑ cₖ z^{-k}` in every
rotated sector. -/
theorem hasAsymptoticExpansion_cpow_mul_kummerU_rotSector (a b : ℂ) {δ α : ℝ} (hδ : 0 < δ)
    (hα : |α| < π / 2) :
    HasAsymptoticExpansion (rotSectorAtTop δ α) (fun (k : ℕ) (z : ℂ) => (z ^ k)⁻¹)
      (tricomiCoeff a b) (fun z => z ^ a * kummerU a b z) := by
  refine ((hasAsymptoticExpansion_kummerU_rotSector a b hδ hα).mul_left
    (fun z => z ^ a)).congr_scale fun k => ?_
  filter_upwards [eventually_rotSectorAtTop hδ hα] with z hz
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  rw [← cpow_add _ _ hz0, show a + -((k : ℂ) + a) = -(k : ℂ) by ring, cpow_neg, cpow_natCast]

/-- A ray `ρ ↦ ρ c` tends to the rotated sector if `c e^{iα}` lies in the sector. -/
theorem tendsto_ofReal_mul_rotSectorAtTop {c : ℂ} (hc : c ≠ 0) {δ α : ℝ}
    (h : δ * ‖c‖ ≤ (c * exp (α * I)).re) :
    Tendsto (fun ρ : ℝ => (ρ : ℂ) * c) atTop (rotSectorAtTop δ α) := by
  refine tendsto_comap_iff.mpr (tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, ?_⟩)
  · have : (fun ρ : ℝ => ‖(ρ : ℂ) * c * exp (α * I)‖) =ᶠ[atTop] fun ρ => ρ * ‖c‖ := by
      filter_upwards [eventually_ge_atTop 0] with ρ hρ
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hρ]
    exact (tendsto_congr' this).mpr (tendsto_id.atTop_mul_const (norm_pos_iff.mpr hc))
  · refine tendsto_principal.mpr ?_
    filter_upwards [eventually_ge_atTop 0] with ρ hρ
    simp only [Function.comp_apply]
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hρ, mul_assoc, Complex.re_ofReal_mul]
    nlinarith

/-- The expansion behind DLMF 33.11.1 for `ρ ↦ (ρ c)^a U(a, b, ρ c)` along a ray in a rotated
sector. -/
theorem hasAsymptoticExpansion_ray_cpow_mul_kummerU (a b : ℂ) {c : ℂ} (hc : c ≠ 0) {δ α : ℝ}
    (hδ : 0 < δ) (hα : |α| < π / 2) (h : δ * ‖c‖ ≤ (c * exp (α * I)).re) :
    HasAsymptoticExpansion atTop (fun (k : ℕ) (ρ : ℝ) => ((ρ : ℂ) ^ k)⁻¹)
      (fun k => poch a k * poch (a - b + 1) k / (k ! * (-c) ^ k))
      (fun ρ : ℝ => ((ρ : ℂ) * c) ^ a * kummerU a b ((ρ : ℂ) * c)) := by
  refine ((hasAsymptoticExpansion_cpow_mul_kummerU_rotSector a b hδ hα).comp_tendsto
    (tendsto_ofReal_mul_rotSectorAtTop hc h)).smul_scale (κ := fun k => (c ^ k)⁻¹)
    (fun k => Eventually.of_forall fun ρ => ?_) |>.congr_coeff ?_
  · simp only [mul_pow, mul_inv, mul_comm]
  · funext k
    have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    simp only [smul_eq_mul, tricomiCoeff, neg_pow c]
    field_simp
    rw [← pow_mul, pow_mul', neg_one_sq, one_pow, one_mul]

theorem two_I_ne_zero : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero

/-- **Asymptotic expansion of `H^+_ℓ`** (DLMF 33.11.1, upper signs):
`e^{-iθ_ℓ} H^+_ℓ(η,ρ) ~ ∑ (iη-ℓ)_k (iη+ℓ+1)_k / (k! (2iρ)^k)` as `ρ → +∞`. -/
@[dlmf 33.11.E1]
theorem hasAsymptoticExpansion_coulombHPlus (ℓ : ℕ) (η : ℝ) :
    HasAsymptoticExpansion atTop (fun (k : ℕ) (ρ : ℝ) => ((ρ : ℂ) ^ k)⁻¹)
      (fun k => poch (I * η - ℓ) k * poch (I * η + ℓ + 1) k / (k ! * (2 * I) ^ k))
      (fun ρ => exp (-I * coulombTheta ℓ η ρ) * coulombHPlus ℓ η ρ) := by
  have h := hasAsymptoticExpansion_ray_cpow_mul_kummerU ((ℓ : ℂ) + 1 + I * η) (2 * ℓ + 2)
    (c := -2 * I) (by simp [I_ne_zero]) (δ := 1 / 2) (α := π / 4) (by norm_num)
    (by rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos]) ?_
  · refine (h.congr' (Eventually.of_forall fun ρ => ?_)).congr_coeff (funext fun k => ?_)
    · simp only [coulombHPlus]
      symm
      rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add,
        show -I * (coulombTheta ℓ η ρ : ℂ) + I * coulombTheta ℓ η ρ = 0 by ring, Complex.exp_zero,
        one_mul]
      ring_nf
    · simp only [neg_mul, neg_neg]
      rw [show (ℓ : ℂ) + 1 + I * η - (2 * ℓ + 2) + 1 = I * η - ℓ by ring,
        show (ℓ : ℂ) + 1 + I * η = I * η + ℓ + 1 by ring]
      ring
  · rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    have hn : ‖(-2 * I : ℂ)‖ = 2 := by simp
    rw [hn]
    simp only [mul_re, mul_im, neg_re, neg_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
      re_ofNat, im_ofNat]
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt] <;> norm_num
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- **Asymptotic expansion of `H^-_ℓ`** (DLMF 33.11.1, lower signs):
`e^{iθ_ℓ} H^-_ℓ(η,ρ) ~ ∑ (-iη-ℓ)_k (-iη+ℓ+1)_k / (k! (-2iρ)^k)` as `ρ → +∞`. -/
@[dlmf 33.11.E1]
theorem hasAsymptoticExpansion_coulombHMinus (ℓ : ℕ) (η : ℝ) :
    HasAsymptoticExpansion atTop (fun (k : ℕ) (ρ : ℝ) => ((ρ : ℂ) ^ k)⁻¹)
      (fun k => poch (-I * η - ℓ) k * poch (-I * η + ℓ + 1) k / (k ! * (-2 * I) ^ k))
      (fun ρ => exp (I * coulombTheta ℓ η ρ) * coulombHMinus ℓ η ρ) := by
  have h := hasAsymptoticExpansion_ray_cpow_mul_kummerU ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2)
    (c := 2 * I) two_I_ne_zero (δ := 1 / 2) (α := -(π / 4)) (by norm_num)
    (by rw [abs_neg, abs_of_pos (by positivity)]; linarith [Real.pi_pos]) ?_
  · refine (h.congr' (Eventually.of_forall fun ρ => ?_)).congr_coeff (funext fun k => ?_)
    · simp only [coulombHMinus]
      symm
      rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add,
        show I * (coulombTheta ℓ η ρ : ℂ) + -I * coulombTheta ℓ η ρ = 0 by ring, Complex.exp_zero,
        one_mul]
      ring_nf
    · rw [show (ℓ : ℂ) + 1 - I * η - (2 * ℓ + 2) + 1 = -I * η - ℓ by ring,
        show (ℓ : ℂ) + 1 - I * η = -I * η + ℓ + 1 by ring]
      ring
  · rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    have hn : ‖(2 * I : ℂ)‖ = 2 := by simp
    rw [hn]
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
      re_ofNat, im_ofNat]
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt] <;> norm_num
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

end DLMF.Confluent
