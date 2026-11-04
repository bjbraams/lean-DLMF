/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Reduction
public import DLMF.EllipticIntegrals.Quadratic

/-!
# The singular modulus `k₃` and the integral `∫₁^∞ dt/√(t³ - 1)`

For the singular modulus `k₃ = sin(π/12)`, `k₃² = (2 - √3)/4`, the reduction DLMF 19.14.1 at
`x = 1 + √3` gives `∫₁^{1+√3} dt/√(t³ - 1) = 3^{-1/4} K(k₃)`. The involution
`u ↦ (u + 2)/(u - 1)` fixes `1 + √3`, exchanges `1` and `∞` and preserves `dt/√(t³ - 1)`, so the
complete integral `∫₁^∞ dt/√(t³ - 1)` is `2 · 3^{-1/4} K(k₃)`. This is the input for the
equianharmonic value DLMF 23.5.9.

## Main results

* `completeEllipticK_singular_three_eq_integral`: `K(k₃) = (3^{1/4}/2) ∫₁^∞ dt/√(t³ - 1)`.
* `completeEllipticK_exp_pi_mul_I_div_six`: the Landen step and `K' = conj K` for `k = e^{πi/6}`.
* `exp_pi_mul_I_div_twelve`: `e^{πi/12} = √((2 + √3)/4) + i √((2 - √3)/4)`.
-/

@[expose] public section

open Complex Set Filter MeasureTheory
open scoped Real Topology
open DLMF.JacobiElliptic (jacobiComodulus)

noncomputable section

namespace DLMF.EllipticIntegrals

/-- The involution `u ↦ (u + 2)/(u - 1)` maps `(1, 1 + √3)` onto `(1 + √3, ∞)` and preserves
`dt/√(t³ - 1)`. -/
private lemma integral_Ioi_inv_sqrt_cube_sub_one_eq_Ioo :
    ∫ t in Ioi (1 + √3), (√(t ^ 3 - 1))⁻¹ = ∫ u in Ioo 1 (1 + √3), (√(u ^ 3 - 1))⁻¹ := by
  set a := 1 + √3 with ha
  have hs2 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √3 := by positivity
  have ha2 : a ^ 2 = 2 * a + 2 := by rw [ha]; nlinarith
  have ha1 : 1 < a := by rw [ha]; linarith
  set f : ℝ → ℝ := fun u => (u + 2) / (u - 1) with hf
  set f' : ℝ → ℝ := fun u => -3 / (u - 1) ^ 2 with hf'
  have hderiv : ∀ u ∈ Ioo 1 a, HasDerivWithinAt f (f' u) (Ioo 1 a) u := by
    intro u hu
    have hu1 : u - 1 ≠ 0 := by linarith [hu.1]
    have h := ((hasDerivAt_id u).const_add 2 |>.add_const 0).div
      ((hasDerivAt_id u).sub_const 1) hu1
    refine (h.congr_deriv ?_).hasDerivWithinAt |>.congr_of_mem
      (fun _ _ => by simp only [hf, id, Pi.div_apply]; ring) hu
    simp only [hf', id]; field_simp; ring
  have hinv : ∀ u, 1 < u → f (f u) = u := by
    intro u hu
    have : u - 1 ≠ 0 := by linarith
    simp only [hf]; field_simp; ring
  have hinj : InjOn f (Ioo 1 a) := by
    intro x hx y hy hxy
    have := congrArg f hxy
    rwa [hinv x hx.1, hinv y hy.1] at this
  have hgt : ∀ u, 1 < u → u < a → a < f u := by
    intro u hu1 hua
    simp only [hf]
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  have himg : f '' Ioo 1 a = Ioi a := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hgt u hu.1 hu.2
    · intro hy
      have hy' : a < y := hy
      have hy1 : 1 < y := ha1.trans hy'
      refine ⟨f y, ⟨?_, ?_⟩, hinv y hy1⟩
      · simp only [hf]; rw [lt_div_iff₀ (by linarith)]; linarith
      · simp only [hf]; rw [div_lt_iff₀ (by linarith)]; nlinarith
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hu1 : 0 < u - 1 := by linarith [hu.1]
  have hP : 0 < u ^ 2 + u + 1 := by nlinarith
  have hc : f u ^ 3 - 1 = (3 / (u - 1) ^ 2) ^ 2 * (u ^ 3 - 1) := by
    simp only [hf]; field_simp; ring
  simp only [smul_eq_mul, hf']
  rw [hc, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
    abs_of_neg (by have : 0 < (u - 1) ^ 2 := by positivity
                   exact div_neg_of_neg_of_pos (by norm_num) this)]
  have : 0 < √(u ^ 3 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  field_simp

/-- `K(k₃) = (3^{1/4}/2) ∫₁^∞ dt/√(t³ - 1)` for the singular modulus `k₃² = (2 - √3)/4`. -/
theorem completeEllipticK_singular_three_eq_integral
    (hint : IntegrableOn (fun t : ℝ => (√(t ^ 3 - 1))⁻¹) (Ioi 1)) :
    completeEllipticK (√((2 - √3) / 4)) =
      (((3 : ℝ) ^ (1 / 4 : ℝ) / 2 * ∫ t in Ioi 1, (√(t ^ 3 - 1))⁻¹ : ℝ) : ℂ) := by
  have hs0 : 0 < √3 := by positivity
  have h := integral_inv_sqrt_cube_sub_one (x := √3 + 1) (by linarith) le_rfl
  rw [show √3 + 1 - (√3 + 1) = 0 by ring, zero_div, Real.arccos_zero] at h
  rw [completeEllipticK_eq_incompleteEllipticF]
  have hsplit : ∫ t in Ioi 1, (√(t ^ 3 - 1))⁻¹ =
      2 * ∫ t in (1 : ℝ)..(√3 + 1), (√(t ^ 3 - 1))⁻¹ := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (1 : ℝ) ≤ 1 + √3 by linarith),
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi (by linarith))),
      integral_Ioi_inv_sqrt_cube_sub_one_eq_Ioo, ← integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le (by linarith), add_comm (√3) 1]
    ring
  rw [hsplit, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring]
  set J := ∫ t in (1 : ℝ)..(√3 + 1), (√(t ^ 3 - 1))⁻¹
  have h3 : (((3 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * (((3 : ℝ) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.rpow_add (by norm_num)]; norm_num
  calc incompleteEllipticF ((π / 2 : ℝ) : ℂ) (√((2 - √3) / 4) : ℝ)
      = (((3 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((((3 : ℝ) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ) *
          incompleteEllipticF ((π / 2 : ℝ) : ℂ) (√((2 - √3) / 4) : ℝ)) := by
        rw [← mul_assoc, h3, one_mul]
    _ = _ := by rw [← h]; push_cast; ring

/-- `e^{πi/12} = cos(π/12) + i sin(π/12) = √((2 + √3)/4) + i √((2 - √3)/4)`. -/
theorem exp_pi_mul_I_div_twelve :
    cexp (π * I / 12) = (√((2 + √3) / 4) : ℝ) + (√((2 - √3) / 4) : ℝ) * I := by
  have hcos : Real.cos (π / 12) = √((2 + √3) / 4) := by
    have hpos : 0 < Real.cos (π / 12) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hsq : Real.cos (π / 12) ^ 2 = (2 + √3) / 4 := by
      rw [Real.cos_sq, show 2 * (π / 12) = π / 6 by ring, Real.cos_pi_div_six]; ring
    rw [← hsq, Real.sqrt_sq hpos.le]
  have hsin : Real.sin (π / 12) = √((2 - √3) / 4) := by
    have hpos : 0 < Real.sin (π / 12) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hsq : Real.sin (π / 12) ^ 2 = (2 - √3) / 4 := by
      rw [Real.sin_sq, Real.cos_sq, show 2 * (π / 12) = π / 6 by ring, Real.cos_pi_div_six]
      ring
    rw [← hsq, Real.sqrt_sq hpos.le]
  rw [show (π : ℂ) * I / 12 = ((π / 12 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, hcos, hsin]

open scoped ComplexConjugate in
/-- For `k = e^{πi/6}`: `k = √3/2 + i/2`, the descending Landen transformation
`K(k) = (1 + i(2 - √3)) K(i(2 - √3))` (DLMF 19.8.12, `k₁ = (1 - k')/(1 + k') = i(2 - √3)`), and
`K'(k) = conj K(k)` (since `1 - k² = conj k²`). -/
theorem completeEllipticK_exp_pi_mul_I_div_six :
    cexp (π * I / 6) = √3 / 2 + I / 2 ∧
      completeEllipticK (cexp (π * I / 6)) = (1 + I * (2 - √3)) * completeEllipticK (I * (2 - √3)) ∧
      completeEllipticKPrime (cexp (π * I / 6)) = conj (completeEllipticK (cexp (π * I / 6))) := by
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3lt : √3 < 2 := by nlinarith [Real.sqrt_nonneg 3]
  have hs3c : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by rw [← ofReal_pow, hs3]; norm_num
  have hexp : ∀ x : ℝ, cexp (x * I) = Real.cos x + Real.sin x * I := fun x => by
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hk : cexp (π * I / 6) = √3 / 2 + I / 2 := by
    rw [show (π : ℂ) * I / 6 = ((π / 6 : ℝ) : ℂ) * I by push_cast; ring, hexp,
      Real.cos_pi_div_six, Real.sin_pi_div_six]; push_cast; ring
  have hk2 : cexp (π * I / 6) ^ 2 = cexp (π * I / 3) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h1k : 1 - cexp (π * I / 6) ^ 2 = cexp (-(π * I / 3)) := by
    have : cexp (-(π * I / 3)) = 1 / 2 - √3 / 2 * I := by
      rw [show -((π : ℂ) * I / 3) = ((-(π / 3) : ℝ) : ℂ) * I by push_cast; ring, hexp,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three, Real.sin_pi_div_three]
      push_cast; ring
    rw [this, hk]; ring_nf; rw [I_sq, hs3c]; ring
  have hslit : 1 - cexp (π * I / 6) ^ 2 ∈ slitPlane := by
    rw [h1k]; refine mem_slitPlane_iff.2 (Or.inl ?_)
    rw [exp_re]; simp only [neg_re, div_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, neg_im, div_im, mul_im, zero_mul, add_zero]
    norm_num
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hkp : jacobiComodulus (cexp (π * I / 6)) = √3 / 2 - I / 2 := by
    rw [jacobiComodulus, h1k, cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp]
    · rw [show -((π : ℂ) * I / 3) * (1 / 2) = ((-(π / 6) : ℝ) : ℂ) * I by push_cast; ring, hexp,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six, Real.sin_pi_div_six]
      push_cast; ring
    · simp; linarith [Real.pi_pos]
    · simp; linarith [Real.pi_pos]
  have hk1 : (1 - jacobiComodulus (cexp (π * I / 6))) /
      (1 + jacobiComodulus (cexp (π * I / 6))) = I * (2 - √3) := by
    have hne : (1 : ℂ) + (√3 / 2 - I / 2) ≠ 0 := by
      intro h; have := congrArg re h; simp at this; nlinarith [Real.sqrt_nonneg 3]
    rw [hkp, div_eq_iff hne]
    linear_combination ((2 - √3) / 2) * I_sq + (I / 2) * hs3c
  obtain ⟨hL, -⟩ := compEllInt_landen_descending hslit
  rw [hk1] at hL
  have hKp : completeEllipticKPrime (cexp (π * I / 6)) =
      conj (completeEllipticK (cexp (π * I / 6))) := by
    have hconj : 1 - cexp (π * I / 6) ^ 2 = conj (cexp (π * I / 6) ^ 2) := by
      rw [h1k, hk2, ← Complex.exp_conj]; congr 1
      rw [map_div₀, map_mul, conj_ofReal, conj_I, map_ofNat]; ring
    unfold completeEllipticKPrime completeEllipticK
    rw [intervalIntegral.integral_of_le (by positivity),
      intervalIntegral.integral_of_le (by positivity), ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    rw [hconj]
    have hx : 1 - conj (cexp (π * I / 6) ^ 2) * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane := by
      rw [← hconj, h1k]
      refine mem_slitPlane_iff.2 (Or.inl ?_)
      have e : cexp (-(π * I / 3)) = 1 / 2 - √3 / 2 * I := by
        rw [show -((π : ℂ) * I / 3) = ((-(π / 3) : ℝ) : ℂ) * I by push_cast; ring, hexp,
          Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three, Real.sin_pi_div_three]
        push_cast; ring
      rw [e]
      have : ((1 - (1 / 2 - √3 / 2 * I) * (Real.sin θ : ℂ) ^ 2) : ℂ).re =
          1 - Real.sin θ ^ 2 / 2 := by
        rw [← ofReal_pow, sub_re, one_re, mul_re, ofReal_re, ofReal_im]; simp; ring
      rw [this]; nlinarith [Real.sin_sq_le_one θ]
    have h := cpow_conj _ (-(1 / 2 : ℂ)) (slitPlane_arg_ne_pi hx)
    rw [show conj (-(1 / 2 : ℂ)) = -(1 / 2) by rw [map_neg, map_div₀, map_one, map_ofNat]] at h
    have hx' : conj (1 - conj (cexp (π * I / 6) ^ 2) * (Real.sin θ : ℂ) ^ 2) =
        1 - cexp (π * I / 6) ^ 2 * (Real.sin θ : ℂ) ^ 2 := by
      rw [map_sub, map_one, map_mul, Complex.conj_conj, map_pow, conj_ofReal]
    rw [h, hx']
  exact ⟨hk, hL, hKp⟩

end DLMF.EllipticIntegrals
