/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Integrals.GegenbauerAndLegendre

/-!
# Laguerre fractional integrals and Hermite Gaussian moments

Fractional Laguerre integration and Gaussian moment identities for Hermite polynomials.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Integrals`.
This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

open DLMF.Bessel

open DLMF.Gamma (Gamma_add_nat_eq_poch_mul_Gamma)

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- Gamma normalization converts Laguerre polynomials into the regularized Kummer
function. This uses Mathlib's Gamma/Pochhammer relation at regular parameters. -/
theorem laguerrePolyL_div_Gamma_eq_regularized {α : ℝ} (hα : -1 < α) (n : ℕ) (y : ℂ) :
    laguerrePolyL α n y / Gamma ((α : ℂ) + n + 1) =
      regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} y / (n.factorial : ℂ) := by
  have hp : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simp; linarith)
  have hG : Gamma ((α : ℂ) + n + 1) = poch ((α : ℂ) + 1) n * Gamma ((α : ℂ) + 1) := by
    have h := Gamma_add_nat_div_Gamma_eq (n := n) ((α : ℂ) + 1) hp
    rw [show (α : ℂ) + n + 1 = (α : ℂ) + 1 + n by ring]
    exact (div_eq_iff (Gamma_ne_zero hp)).mp h
  rw [laguerrePolyL, kummerM_eq_mul_regularizedHGFun hp, hG]
  field [Gamma_ne_zero hp, poch_ne_zero_of_not_neg_nat hp n]

/-- Identity under the stated parameter and domain assumptions: `(x : ℂ) ^ ((α : ℂ) + μ) *
laguerrePolyL (α + μ) n x / Gamma (α + μ + n + 1 : ℂ) = ∫ y : ℝ in (0 : ℝ)..x, (y : ℂ) ^ (α :
ℂ) * laguerrePolyL α n y / Gamma (α + n + 1 : ℂ) * (x - y : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ :
ℂ)`. -/
@[dlmf 18.17.E14]
theorem laguerrePolyL_fractional_integral {α μ x : ℝ} (hα : -1 < α) (hμ : 0 < μ) (hx : 0 < x)
    (n : ℕ) :
    (x : ℂ) ^ ((α : ℂ) + μ) * laguerrePolyL (α + μ) n x / Gamma (α + μ + n + 1 : ℂ) =
      ∫ y : ℝ in (0 : ℝ)..x, (y : ℂ) ^ (α : ℂ) * laguerrePolyL α n y / Gamma (α + n + 1 : ℂ) *
        (x - y : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ) := by
  let f : ℝ → ℂ := fun y => (y : ℂ) ^ (α : ℂ) *
    regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} y *
      ((x : ℂ) - y) ^ ((μ : ℂ) - 1)
  let g : ℝ → ℂ := fun t =>
    regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} ((x : ℂ) * t) *
      (t : ℂ) ^ (α : ℂ) * (1 - (t : ℂ)) ^ ((μ : ℂ) - 1)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hscale : (∫ y : ℝ in (0 : ℝ)..x, f y) =
      (x : ℂ) ^ ((α : ℂ) + μ) * ∫ t : ℝ in (0 : ℝ)..1, g t := by
    have hs := intervalIntegral.smul_integral_comp_mul_left f x (a := (0 : ℝ)) (b := 1)
    simp only [mul_zero, mul_one, Complex.real_smul] at hs
    rw [← hs, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have hxp : (x : ℂ) * (x : ℂ) ^ (α : ℂ) * (x : ℂ) ^ ((μ : ℂ) - 1) =
        (x : ℂ) ^ ((α : ℂ) + μ) := by
      calc
        _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (α : ℂ) *
            (x : ℂ) ^ ((μ : ℂ) - 1) := by rw [cpow_one]
        _ = _ := by
          rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]
          congr 1
          ring
    have hptail : ((x : ℂ) * (1 - (t : ℂ))) ^ ((μ : ℂ) - 1) =
        (x : ℂ) ^ ((μ : ℂ) - 1) * (1 - (t : ℂ)) ^ ((μ : ℂ) - 1) := by
      simpa only [ofReal_sub, ofReal_one] using
        mul_cpow_ofReal_nonneg hx.le (sub_nonneg.mpr ht.2.le) ((μ : ℂ) - 1)
    dsimp [f, g]
    simp only [ofReal_mul]
    rw [show (x : ℂ) - (x : ℂ) * t = (x : ℂ) * (1 - (t : ℂ)) by ring,
      mul_cpow_ofReal_nonneg hx.le ht.1.le, hptail]
    linear_combination (t : ℂ) ^ (α : ℂ) *
      regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} ((x : ℂ) * t) *
      (1 - (t : ℂ)) ^ ((μ : ℂ) - 1) * hxp
  have hR := DLMF.Confluent.regularized_parameter_integral (a := -(n : ℂ))
    (b := (α : ℂ) + μ + 1) (c := (α : ℂ) + 1) (z := x)
    (by simp; linarith) (by simp; linarith)
  rw [show (α : ℂ) + 1 - 1 = (α : ℂ) by ring,
    show (α : ℂ) + μ + 1 - ((α : ℂ) + 1) = (μ : ℂ) by ring] at hR
  change regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + μ + 1} x =
    1 / Gamma (μ : ℂ) * ∫ t : ℝ in (0 : ℝ)..1, g t at hR
  have hrhs : (∫ y : ℝ in (0 : ℝ)..x,
      (y : ℂ) ^ (α : ℂ) * laguerrePolyL α n y / Gamma (α + n + 1 : ℂ) *
        (x - y : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ)) =
      (∫ y : ℝ in (0 : ℝ)..x, f y) / ((n.factorial : ℂ) * Gamma (μ : ℂ)) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [show (y : ℂ) ^ (α : ℂ) * laguerrePolyL α n y / Gamma (α + n + 1 : ℂ) =
      (y : ℂ) ^ (α : ℂ) * (laguerrePolyL α n y / Gamma (α + n + 1 : ℂ)) by ring,
      laguerrePolyL_div_Gamma_eq_regularized hα]
    dsimp [f]
    push_cast
    ring
  have hL := laguerrePolyL_div_Gamma_eq_regularized (by linarith : -1 < α + μ) n (x : ℂ)
  push_cast at hL
  rw [hrhs, hscale, show (x : ℂ) ^ ((α : ℂ) + μ) * laguerrePolyL (α + μ) n x /
      Gamma (α + μ + n + 1 : ℂ) = (x : ℂ) ^ ((α : ℂ) + μ) *
      (laguerrePolyL (α + μ) n x / Gamma (α + μ + n + 1 : ℂ)) by ring,
    hL]
  push_cast
  rw [hR]
  ring

/-- Identity under the stated parameter and domain assumptions: `exp (-x) * laguerrePolyL α n x =
∫ y : ℝ in Set.Ioi x, exp (-y) * laguerrePolyL (α + μ) n y * (y - x : ℂ) ^ ((μ : ℂ) - 1) /
Gamma (μ : ℂ)`. -/
@[dlmf 18.17.E15]
theorem laguerrePolyL_fractional_tail_integral {α μ x : ℝ} (hα : -1 < α) (hμ : 0 < μ) (hx : 0 ≤ x)
    (n : ℕ) :
    exp (-x) * laguerrePolyL α n x = ∫ y : ℝ in Set.Ioi x,
      exp (-y) * laguerrePolyL (α + μ) n y * (y - x : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ) := by
  have hβ : -1 < μ - 1 := by linarith
  have hp (a : ℝ) (ha : -1 < a) : ∀ k : ℕ, (a : ℂ) + 1 ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simp; linarith)
  have hΓ : Gamma (μ : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hμ)
  have hadd (y : ℝ) : laguerrePolyL (α + μ) n ((x : ℂ) + y) =
      ∑ k ∈ Finset.range (n + 1), laguerrePolyL α k x * laguerrePolyL (μ - 1) (n - k) y := by
    have h := laguerrePolyL_addition (α : ℂ) ((μ - 1 : ℝ) : ℂ) x y n
    have hparam : (α : ℂ) + ((μ - 1 : ℝ) : ℂ) + 1 = ((α + μ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hparam, laguerreExtended_eq (hp (α + μ) (by linarith))] at h
    simp only [laguerreExtended_eq (hp α hα), laguerreExtended_eq (hp (μ - 1) hβ)] at h
    simpa only [ofReal_add, ofReal_sub, ofReal_one] using h
  let f : ℕ → ℝ → ℂ := fun k y => laguerrePolyL (μ - 1) k y *
    (y : ℂ) ^ ((μ : ℂ) - 1) * exp (-(y : ℂ))
  have hint (k : ℕ) : IntegrableOn (f k) (Set.Ioi 0) := by
    have h := integrable_laguerrePolyL_mul_monomial hβ k 0
    simpa only [IntegrableOn, f, pow_zero, mul_one, ofReal_sub, ofReal_one] using h
  have hmoment (k : ℕ) : (∫ y : ℝ in Set.Ioi 0, f k y) =
      if k = 0 then Gamma (μ : ℂ) else 0 := by
    have h := integral_laguerrePolyL_mul_monomial hβ k 0
    simp only [pow_zero, mul_one, ofReal_sub, ofReal_one, Nat.cast_zero, neg_zero,
      add_zero, sub_add_cancel] at h
    change (∫ y : ℝ in Set.Ioi 0, f k y) = _ at h
    rw [h]
    cases k with
    | zero => simp [poch_zero]
    | succ k => simp
  let F : ℝ → ℂ := fun y => exp (-(y : ℂ)) * laguerrePolyL (α + μ) n y *
    ((y : ℂ) - x) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ)
  have hshift := (measurePreserving_add_left (volume : Measure ℝ) x).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft x).measurableEmbedding F (Set.Ioi x)
  have hpre : (fun y : ℝ => x + y) ⁻¹' Set.Ioi x = Set.Ioi 0 := by
    ext y
    simp
  rw [hpre] at hshift
  change exp (-x) * laguerrePolyL α n x = ∫ y : ℝ in Set.Ioi x, F y
  rw [← hshift]
  have heq (y : ℝ) : F (x + y) = exp (-x) / Gamma (μ : ℂ) *
      ∑ k ∈ Finset.range (n + 1), laguerrePolyL α k x * f (n - k) y := by
    dsimp [F, f]
    rw [ofReal_add, add_sub_cancel_left, neg_add, exp_add, hadd]
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => heq y), integral_const_mul,
    integral_finsetSum _ (fun k _ => (hint (n - k)).const_mul (laguerrePolyL α k x))]
  simp only [integral_const_mul, hmoment]
  rw [Finset.sum_eq_single n]
  · simp only [Nat.sub_self, ↓reduceIte]
    field [hΓ]
  · intro k hk hkn
    have hk' : k < n := by have := Finset.mem_range.mp hk; omega
    simp [Nat.sub_ne_zero_of_lt hk']
  · simp

/-- Identity under the stated parameter and domain assumptions: `(∫ x : ℝ, exp (-(x : ℂ) ^ 2) *
(aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (I * x * y)) / Real.sqrt Real.pi = I ^ n * exp (-(y
: ℂ) ^ 2 / 4) * (y : ℂ) ^ n`. -/
@[dlmf 18.17.E21_2]
theorem hermitePolyH_fourier_transform (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (I * x * y)) /
      Real.sqrt Real.pi = I ^ n * exp (-(y : ℂ) ^ 2 / 4) * (y : ℂ) ^ n := by
  have h := hermitePolyH_laplace_transform n (-I * y)
  have heq : ∀ x : ℝ, exp (-(x : ℂ) ^ 2) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (I * x * y) =
      exp (-x * (-I * y)) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (-(x : ℂ) ^ 2) := fun x => by
    rw [show -(x : ℂ) * (-I * y) = I * x * y by ring]; ring
  simp_rw [heq]
  rw [h]
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [show -(-I * (y : ℂ)) = I * y by ring, mul_pow,
    show (-I * (y : ℂ)) ^ 2 / 4 = -(y : ℂ) ^ 2 / 4 by ring_nf; rw [I_sq]; ring]
  field_simp

/-- TauCeti's Hermite functions with the positive, unit-frequency Fourier convention. -/
theorem hermiteFunction_integral (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, Complex.exp (I * x * y) * (TauCeti.hermiteFunction n x : ℂ)) =
      (Real.sqrt (2 * Real.pi) : ℂ) * I ^ n * (TauCeti.hermiteFunction n y : ℂ) := by
  let s := Real.sqrt (2 * Real.pi)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)
  have hs0 : s ≠ 0 := hs.ne'
  have hs2 : s ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have ha : (Real.sqrt s : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne'
  have he := congrFun (TauCeti.fourier_twoPiHermiteFunction n) (-y / s)
  rw [Real.fourier_real_eq_integral_exp_smul] at he
  have hphase (x : ℝ) : (↑(-2 * Real.pi * x * (-y / s)) : ℂ) * I = I * (s * x) * y := by
    rw [show -2 * Real.pi * x * (-y / s) = s * x * y by
      calc
        _ = (2 * Real.pi) * x * y / s := by ring
        _ = _ := by rw [← hs2]; field_simp]
    push_cast
    ring
  simp_rw [hphase, smul_eq_mul, TauCeti.twoPiHermiteFunction_def, ofReal_mul] at he
  have harg : s * (-y / s) = -y := by field_simp
  change (∫ x : ℝ, exp (I * (s * x) * y) * ((Real.sqrt s : ℂ) * ↑(TauCeti.hermiteFunction n (s * x)))) =
    (-I) ^ n * ((Real.sqrt s : ℂ) * ↑(TauCeti.hermiteFunction n (s * (-y / s)))) at he
  rw [harg, TauCeti.hermiteFunction_neg, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one] at he
  have hmul : (-I) ^ n * ((Real.sqrt s : ℂ) * ((-1) ^ n * ↑(TauCeti.hermiteFunction n y))) =
      (Real.sqrt s : ℂ) * (I ^ n * ↑(TauCeti.hermiteFunction n y)) := by
    rw [show (-I) ^ n = (-1 : ℂ) ^ n * I ^ n by rw [← mul_pow]; congr 1; ring]
    have hn : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp
    calc
      _ = (Real.sqrt s : ℂ) * (I ^ n * ↑(TauCeti.hermiteFunction n y)) * ((-1) ^ n * (-1) ^ n) := by ring
      _ = _ := by rw [hn, mul_one]
  rw [hmul] at he
  have hleft : (∫ x : ℝ, exp (I * (s * x) * y) * ((Real.sqrt s : ℂ) * ↑(TauCeti.hermiteFunction n (s * x)))) =
      (Real.sqrt s : ℂ) * (s : ℂ)⁻¹ * ∫ x : ℝ, exp (I * x * y) * ↑(TauCeti.hermiteFunction n x) := by
    simp_rw [mul_left_comm (exp _)]
    simp_rw [← ofReal_mul s]
    rw [integral_const_mul, Measure.integral_comp_mul_left
      (fun x : ℝ => exp (I * x * y) * ↑(TauCeti.hermiteFunction n x)) s]
    simp [abs_of_pos (inv_pos.mpr hs), Complex.real_smul, mul_assoc]
  rw [hleft] at he
  have hsc0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs0
  field_simp [hsc0] at he
  exact he
/-- Evaluation of integer polynomials commutes with the real-to-complex inclusion. -/
private lemma ofReal_aeval_int (p : ℤ[X]) (x : ℝ) :
    ((aeval x p : ℝ) : ℂ) = aeval (x : ℂ) p := by
  exact (aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x p).symm

/-- The physicists' Hermite envelope differs from TauCeti's function by a constant. -/
theorem hermitePolyH_envelope (n : ℕ) (x : ℝ) :
    exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) =
      ((2 : ℝ) ^ (n / 2 : ℝ) * Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) : ℝ) *
        (TauCeti.hermiteFunction n x : ℂ) := by
  rw [← ofReal_aeval_int, aeval_hermitePolyH_eq_hermite, TauCeti.hermiteFunction_def]
  have hc : Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) ≠ 0 :=
    TauCeti.sqrt_factorial_mul_sqrt_pi_ne_zero n
  have he : exp (-(x : ℂ) ^ 2 / 2) = (Real.exp (-(x ^ 2 / 2)) : ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; ring
  rw [he]
  push_cast
  rw [mul_comm x (Real.sqrt 2)]
  field_simp [ofReal_ne_zero.mpr hc]
  rw [mul_div_cancel_right₀ _ (ofReal_ne_zero.mpr hc)]

/-- The probabilists' Hermite envelope is a dilation of TauCeti's Hermite function. -/
theorem hermite_envelope (n : ℕ) (x : ℝ) :
    exp (-(x : ℂ) ^ 2 / 4) * (aeval (x : ℂ) (hermite n) : ℂ) =
      (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) : ℂ) *
        (TauCeti.hermiteFunction n (x / Real.sqrt 2) : ℂ) := by
  rw [← ofReal_aeval_int, TauCeti.hermiteFunction_def]
  have hc := TauCeti.sqrt_factorial_mul_sqrt_pi_ne_zero n
  have hr : Real.sqrt 2 ≠ 0 := by positivity
  rw [div_mul_cancel₀ x hr]
  rw [show -((x / Real.sqrt 2) ^ 2 / 2) = -(x ^ 2 / 4) by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring]
  have he : exp (-(x : ℂ) ^ 2 / 4) = (Real.exp (-(x ^ 2 / 4)) : ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; ring
  rw [he]
  push_cast
  field_simp [ofReal_ne_zero.mpr hc]
  rw [mul_div_cancel_right₀ _ (ofReal_ne_zero.mpr hc)]

/-- Identity under the stated parameter and domain assumptions: `(∫ x : ℝ, exp (-(x : ℂ) ^ 2 / 2)
* (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (I * x * y)) / Real.sqrt (2 * Real.pi) = I ^ n *
exp (-(y : ℂ) ^ 2 / 2) * aeval (y : ℂ) (hermitePolyH n)`. -/
@[dlmf 18.17.E21_3]
theorem hermitePolyH_fourier_eigenfunction (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (I * x * y)) /
      Real.sqrt (2 * Real.pi) = I ^ n * exp (-(y : ℂ) ^ 2 / 2)
          * aeval (y : ℂ) (hermitePolyH n) := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [show I ^ n * exp (-(y : ℂ) ^ 2 / 2) * aeval (y : ℂ) (hermitePolyH n) =
    I ^ n * (exp (-(y : ℂ) ^ 2 / 2) * aeval (y : ℂ) (hermitePolyH n)) by ring]
  simp_rw [hermitePolyH_envelope]
  simp_rw [mul_assoc, mul_comm (↑(TauCeti.hermiteFunction n _) : ℂ) (exp _)]
  rw [integral_const_mul]
  simp_rw [← mul_assoc I]
  rw [hermiteFunction_integral]
  field_simp

/-- `u^{s-1} e^{-wu}` is integrable on `(0,∞)` for `Re s, Re w > 0`. -/
theorem integrableOn_cpow_mul_cexp_neg {s w : ℂ} (hs : 0 < s.re) (hw : 0 < w.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-(w * u))) (Set.Ioi 0) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1) (b := w.re)
    (by linarith) one_pos hw
  refine Integrable.mono' hb (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 0 < u := hu
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu', Complex.norm_exp, Real.rpow_one]
  simp

/-- Termwise Mellin–Laplace integration of a finite polynomial sum. -/
theorem integral_finite_sum_mellin_laplace {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 0 < z.re) (s : Finset ℕ) (c : ℕ → ℂ) (d : ℕ → ℕ) :
    (∫ x : ℝ in Set.Ioi 0, exp (-a * x) *
      (∑ k ∈ s, c k * (x : ℂ) ^ d k) * (x : ℂ) ^ (z - 1)) =
      ∑ k ∈ s, c k * Gamma (z + d k) / (a : ℂ) ^ (z + d k) := by
  have hs (k : ℕ) : 0 < (z + d k).re := by
    simp only [add_re, natCast_re]; positivity
  have hterm (x : ℝ) (hx : 0 < x) :
      exp (-a * x) * (∑ k ∈ s, c k * (x : ℂ) ^ d k) * (x : ℂ) ^ (z - 1) =
      ∑ k ∈ s, c k * ((x : ℂ) ^ (z + d k - 1) * exp (-((a : ℂ) * x))) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [show z + (d k : ℂ) - 1 = (z - 1) + d k by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_natCast]
    rw [neg_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hterm x hx),
    integral_finsetSum _ (fun k _ =>
      (integrableOn_cpow_mul_cexp_neg (hs k) (by simpa using ha)).const_mul _)]
  simp_rw [integral_const_mul,
    DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (z := (a : ℂ)) (hs _) (by simpa using ha), cpow_neg,
    div_eq_mul_inv, mul_assoc]

/-- The Laplace transform of `e^{-x} x^α L_n^{(α)}(x)` on `(0, ∞)` (DLMF 18.17.34). -/
@[dlmf 18.17.E34]
theorem laguerrePolyL_laplace_transform {α : ℝ} (hα : -1 < α) (n : ℕ) {z : ℂ} (hz : -1 < z.re) :
    ∫ x : ℝ in Set.Ioi 0, exp (-x * z) * laguerrePolyL α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (α + n + 1 : ℂ) * z ^ n / (n.factorial * (z + 1) ^ (α + n + 1 : ℂ)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hw : 0 < (z + 1).re := by simp; linarith
  have hw0 : z + 1 ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hs : ∀ k : ℕ, 0 < ((α : ℂ) + k + 1).re := fun k => by
    simp; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  -- termwise form of the integrand
  have hterm : ∀ x : ℝ, 0 < x → exp (-x * z) * laguerrePolyL α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      ∑ k ∈ Finset.range (n + 1), poch (α + 1 + k) (n - k) / ((n - k).factorial * k.factorial : ℂ) *
        (-1) ^ k * ((x : ℂ) ^ (((α : ℂ) + k + 1) - 1) * cexp (-((z + 1) * x))) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    rw [laguerrePolyL_eq_sum hα', Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : (x : ℂ) ^ (((α : ℂ) + k + 1) - 1) = (x : ℂ) ^ (α : ℂ) * (x : ℂ) ^ k := by
      rw [show ((α : ℂ) + k + 1) - 1 = (α : ℂ) + k by ring, cpow_add _ _ hx0, cpow_natCast]
    have he : cexp (-((z + 1) * x)) = cexp (-x * z) * cexp (-x) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hc, he, neg_pow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hterm x hx)]
  rw [integral_finsetSum _ fun k _ =>
    ((integrableOn_cpow_mul_cexp_neg (hs k) hw).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_congr rfl fun k _ => by rw [DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (hs k) hw]]
  -- resum with the binomial theorem
  have hz1 : z = (z + 1) - 1 := by ring
  have hpowz : z ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (-1) ^ k * (z + 1) ^ (n - k) := by
    conv_lhs => rw [hz1]
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hS : ∀ k ∈ Finset.range (n + 1), poch (α + 1 + k) (n - k) / ((n - k).factorial * k.factorial : ℂ) *
      (-1) ^ k * (Gamma ((α : ℂ) + k + 1) * (z + 1) ^ (-((α : ℂ) + k + 1))) =
      Gamma ((α : ℂ) + n + 1) / (n ! * (z + 1) ^ ((α : ℂ) + n + 1)) *
        ((n.choose k : ℂ) * (-1) ^ k * (z + 1) ^ (n - k)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hG := Gamma_add_nat_eq_poch_mul_Gamma (hs k) (n - k)
    rw [show (α : ℂ) + k + 1 + ((n - k : ℕ) : ℂ) = α + n + 1 by push_cast [Nat.cast_sub hkn]; ring,
      show (α : ℂ) + k + 1 = α + 1 + k by ring] at hG
    rw [show (α : ℂ) + k + 1 = α + 1 + k by ring, hG,
      show (α : ℂ) + n + 1 = α + 1 + k + (n - k : ℕ) by push_cast [Nat.cast_sub hkn]; ring,
      cpow_add _ _ hw0, cpow_neg, cpow_natCast, Nat.cast_choose ℂ hkn]
    have hf1 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hf2 : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
    have hp1 : (z + 1) ^ ((α : ℂ) + 1 + k) ≠ 0 := by
      rw [cpow_def_of_ne_zero hw0]; exact exp_ne_zero _
    have hp2 : (z + 1) ^ (n - k) ≠ 0 := pow_ne_zero _ hw0
    have hfn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  rw [Finset.sum_congr rfl hS, ← Finset.mul_sum, ← hpowz]
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in Set.Ioi 0, exp (-x) *
(x : ℂ) ^ (α : ℂ) * laguerrePolyL α n x * exp (I * x * y) = Gamma (α + n + 1 : ℂ) * (-I * y) ^
n / (n.factorial * (1 - I * y) ^ (α + n + 1 : ℂ))`. -/
@[dlmf 18.17.E28_5]
theorem laguerrePolyL_fourier_transform {α : ℝ} (hα : -1 < α) (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-x) * (x : ℂ) ^ (α : ℂ) * laguerrePolyL α n x * exp (I * x * y) =
      Gamma (α + n + 1 : ℂ) * (-I * y) ^ n / (n.factorial * (1 - I * y) ^ (α + n + 1 : ℂ)) := by
  have h := laguerrePolyL_laplace_transform hα n (z := -I * y) (by simp)
  rw [show -I * (y : ℂ) + 1 = 1 - I * y by ring] at h
  rw [← h]
  congr 1; funext x
  rw [show -(x : ℂ) * (-I * y) = I * x * y by ring]
  ring

/-- Complex-exponent version of `integral_jacobi_weight`. -/
theorem integral_jacobi_weight_cpow {a b : ℂ} (ha : -1 < a.re) (hb : -1 < b.re) :
    (∫ t : ℝ in (-1 : ℝ)..1, (1 - (t : ℂ)) ^ a * (1 + (t : ℂ)) ^ b) =
      (2 : ℂ) ^ (a + b + 1) * (Gamma (a + 1) * Gamma (b + 1) / Gamma (a + b + 2)) := by
  have he := intervalIntegral.integral_comp_add_right
    (fun t : ℝ => (t : ℂ) ^ b * ((2 : ℂ) - t) ^ a) 1
    (a := (-1 : ℝ)) (b := 1)
  norm_num only [neg_add_cancel, one_add_one_eq_two] at he
  have hm := integral_cpow_mul_sub_cpow (a := b) (b := a) hb ha
    (by norm_num : (0 : ℝ) < 2)
  norm_num only [ofReal_ofNat] at hm
  rw [hm] at he
  calc
    _ = ∫ t : ℝ in (-1 : ℝ)..1, ((t + 1 : ℝ) : ℂ) ^ b *
        ((2 : ℂ) - ((t + 1 : ℝ) : ℂ)) ^ a := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      push_cast
      rw [show (2 : ℂ) - ((t : ℂ) + 1) = 1 - t by ring, add_comm (t : ℂ) 1]
      ring
    _ = _ := by rw [he, add_comm b a, mul_comm (Gamma (b + 1))]

/-- Complex-exponent version of `intervalIntegrable_jacobi_weight`. -/
theorem intervalIntegrable_jacobi_weight_cpow {a b : ℂ} (ha : -1 < a.re) (hb : -1 < b.re) :
    IntervalIntegrable (fun t : ℝ => (1 - (t : ℂ)) ^ a * (1 + (t : ℂ)) ^ b) volume (-1) 1 := by
  have hi := (intervalIntegrable_cpow_mul_sub_cpow (a := b) (b := a)
    hb ha (show (0 : ℝ) < 2 by norm_num)).comp_add_right 1
  norm_num only [zero_sub, sub_self, sub_add_cancel] at hi
  convert hi using 1
  · ext t
    push_cast
    rw [show (2 : ℂ) - ((t : ℂ) + 1) = 1 - t by ring]
    rw [add_comm (t : ℂ) 1]
    ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (-1 : ℝ)..1, (1 - (x :
ℂ)) ^ (z - 1) * (1 + (x : ℂ)) ^ (β : ℂ) * jacobiPolyP α β n x = (2 : ℂ) ^ ((β : ℂ) + z) *
Gamma z * Gamma (1 + (β : ℂ) + n) * poch (1 + α - z) n / (n.factorial * Gamma (1 + β + z +
n))`. -/
@[dlmf 18.17.E36]
theorem jacobi_mellin_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1,
        (1 - (x : ℂ)) ^ (z - 1) * (1 + (x : ℂ)) ^ (β : ℂ) * jacobiPolyP α β n x =
      (2 : ℂ) ^ ((β : ℂ) + z) * Gamma z * Gamma (1 + (β : ℂ) + n) * poch (1 + α - z) n /
      (n.factorial * Gamma (1 + β + z + n)) := by
  set a : ℂ := (n : ℂ) + α + β + 1 with ha
  set c : ℂ := (α : ℂ) + 1 with hc
  set C : ℕ → ℂ := fun k => poch c n / n ! * gaussHGCoeff (-(n : ℂ)) a c k / 2 ^ k with hC
  have hexp : Set.EqOn
      (fun x : ℝ => (1 - (x : ℂ)) ^ (z - 1) * (1 + (x : ℂ)) ^ (β : ℂ) * jacobiPolyP α β n x)
      (fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        C k * ((1 - (x : ℂ)) ^ (z - 1 + k) * (1 + (x : ℂ)) ^ (β : ℂ))) (Set.Ioo (-1) 1) := by
    intro x hx
    have h1 : (1 - (x : ℂ)) ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith [hx.2])
    simp only [jacobiPolyP, ordinaryHypergeometric_eq_sum_neg_nat, Finset.mul_sum, hC]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cpow_add _ _ h1, cpow_natCast, div_pow, ← hc, ← ha]
    have h2 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
  have hint (k : ℕ) : IntervalIntegrable
      (fun x : ℝ => C k * ((1 - (x : ℂ)) ^ (z - 1 + k) * (1 + (x : ℂ)) ^ (β : ℂ)))
      volume (-1) 1 :=
    (intervalIntegrable_jacobi_weight_cpow (a := z - 1 + k) (b := (β : ℂ))
      (by simp; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by simpa using hβ)).const_mul _
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num) hexp,
    intervalIntegral.integral_finsetSum fun k _ => hint k]
  simp only [intervalIntegral.integral_const_mul]
  have hzb : 0 < (z + β + 1).re := by simp; linarith
  have hc0 : 0 < c.re := by simp [hc]; linarith
  have hb1 : 0 < ((β : ℂ) + 1).re := by simp; linarith
  have hsum : 1 + a + z - c - n = z + β + 1 := by simp only [ha, hc]; ring
  set K : ℂ := poch c n / n ! * (2 : ℂ) ^ (z + β) * Gamma z * Gamma ((β : ℂ) + 1) /
    Gamma (z + β + 1) with hK
  have hterm : ∀ k ∈ Finset.range (n + 1),
      C k * ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ (z - 1 + k) * (1 + (x : ℂ)) ^ (β : ℂ) =
      K * (poch (-(n : ℂ)) k * poch a k * poch z k /
        (poch c k * poch (1 + a + z - c - n) k * k !)) := by
    intro k _
    rw [integral_jacobi_weight_cpow (by simp; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      (by simpa using hβ)]
    rw [show z - 1 + k + 1 = z + k by ring, show z - 1 + k + β + 2 = (z + β + 1) + k by ring,
      Gamma_add_nat_eq_poch_mul_Gamma hz, Gamma_add_nat_eq_poch_mul_Gamma hzb,
      show z - 1 + k + β + 1 = (z + β) + k by ring, cpow_add _ _ two_ne_zero, cpow_natCast,
      hsum]
    have h1 : poch (z + β + 1) k ≠ 0 := poch_ne_zero_of_re_pos hzb k
    have h2 : poch c k ≠ 0 := poch_ne_zero_of_re_pos hc0 k
    have h3 : Gamma (z + β + 1) ≠ 0 := Gamma_ne_zero_of_re_pos hzb
    have h4 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
    have h5 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    simp only [hC, hK, gaussHGCoeff]
    field_simp
  have hcn : ∀ k : ℕ, c ≠ -k := fun k h => by
    have := congrArg re h; simp [hc] at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hd : poch (1 + a + z - c - n) n ≠ 0 := by rw [hsum]; exact poch_ne_zero_of_re_pos hzb n
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, pfaff_saalschutz n hcn hd]
  rw [show c - a - z = -((n : ℂ) + β + z) by simp only [ha, hc]; ring,
    show c - a = -((n : ℂ) + β) by simp only [ha, hc]; ring,
    DLMF.Gamma.poch_neg_eq, DLMF.Gamma.poch_neg_eq,
    show (n : ℂ) + β - n + 1 = β + 1 by ring, show (n : ℂ) + β + z - n + 1 = z + β + 1 by ring,
    show c - z = 1 + α - z by simp only [hc]; ring,
    show (1 : ℂ) + β + n = (β + 1) + n by ring, show (1 : ℂ) + β + z + n = (z + β + 1) + n by ring,
    Gamma_add_nat_eq_poch_mul_Gamma hb1, Gamma_add_nat_eq_poch_mul_Gamma hzb]
  have h1 : poch (z + β + 1) n ≠ 0 := poch_ne_zero_of_re_pos hzb n
  have h2 : poch c n ≠ 0 := poch_ne_zero_of_re_pos hc0 n
  have h3 : Gamma (z + β + 1) ≠ 0 := Gamma_ne_zero_of_re_pos hzb
  have h5 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have h6 : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [hK]
  rw [add_comm (β : ℂ) z]
  field_simp

/-- The substitution `s = 1 - 2x²` on `(0, 1)`, with no regularity assumption on `F`. -/
theorem integral_mul_comp_one_sub_two_sq (F : ℝ → ℂ) :
    (∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) * F (1 - 2 * x ^ 2)) =
      (1 / 4 : ℂ) * ∫ s : ℝ in (-1 : ℝ)..1, F s := by
  have himg : (fun x : ℝ => 1 - 2 * x ^ 2) '' Set.Ioo 0 1 = Set.Ioo (-1) 1 := by
    ext s
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      constructor <;> nlinarith
    · rintro ⟨hs0, hs1⟩
      refine ⟨Real.sqrt ((1 - s) / 2), ⟨Real.sqrt_pos.mpr (by linarith), ?_⟩, ?_⟩
      · rw [Real.sqrt_lt' one_pos]; linarith
      · show 1 - 2 * Real.sqrt ((1 - s) / 2) ^ 2 = s
        rw [Real.sq_sqrt (by linarith)]; ring
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun x : ℝ => 1 - 2 * x ^ 2) (-(4 * x)) (Set.Ioo 0 1) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).const_mul 2).const_sub 1
    convert this.hasDerivWithinAt using 1
    push_cast; ring
  have hinj : Set.InjOn (fun x : ℝ => 1 - 2 * x ^ 2) (Set.Ioo 0 1) := by
    intro x hx y hy hxy
    have h2 : x ^ 2 = y ^ 2 := by simp only at hxy; linarith
    exact (pow_left_inj₀ hx.1.le hy.1.le two_ne_zero).mp h2
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj F
  rw [himg] at he
  rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, he, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [abs_neg, abs_of_pos (by linarith [hx.1]), Complex.real_smul]
  push_cast
  ring

/-- The substitution `s = 1 - 2x²` turns `(1-x²)^μ x^v` on `(0, 1)` into a Jacobi weight. -/
theorem integral_one_sub_sq_cpow_mul_cpow (μ v : ℂ) (G : ℝ → ℂ) :
    (∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ μ * (x : ℂ) ^ v * G (1 - 2 * x ^ 2)) =
      (1 / 4 : ℂ) * (2 : ℂ) ^ (-(μ + (v - 1) / 2)) * ∫ s : ℝ in (-1 : ℝ)..1,
        (1 - (s : ℂ)) ^ ((v - 1) / 2) * (1 + (s : ℂ)) ^ μ * G s := by
  set w : ℂ := (v - 1) / 2 with hw
  rw [mul_assoc, ← intervalIntegral.integral_const_mul, ← integral_mul_comp_one_sub_two_sq]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun x hx => ?_
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
  have hA : ((2 : ℂ) * (1 - (x : ℂ) ^ 2)) ^ μ = (2 : ℂ) ^ μ * (1 - (x : ℂ) ^ 2) ^ μ := by
    have := mul_cpow_ofReal_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
      (show (0 : ℝ) ≤ 1 - x ^ 2 by nlinarith [hx.1, hx.2]) μ
    push_cast at this; exact this
  have hB : ((2 : ℂ) * (x : ℂ) ^ 2) ^ w = (2 : ℂ) ^ w * ((x : ℂ) ^ 2) ^ w := by
    have := mul_cpow_ofReal_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (sq_nonneg x) w
    push_cast at this; exact this
  have hC : ((x : ℂ) ^ 2) ^ w = (x : ℂ) ^ (2 * w) := by
    rw [cpow_mul _ (by rw [← ofReal_log hx.1.le]; simp; positivity)
      (by rw [← ofReal_log hx.1.le]; simp; positivity), cpow_two]
  have hD : (x : ℂ) ^ v = (x : ℂ) * (x : ℂ) ^ (2 * w) := by
    rw [hw, show 2 * ((v - 1) / 2) = v - 1 by ring, cpow_sub _ _ hx0, cpow_one]
    field_simp
  have h2 : (2 : ℂ) ^ (-(μ + w)) * (2 : ℂ) ^ w * (2 : ℂ) ^ μ = 1 := by
    rw [cpow_neg, cpow_add _ _ two_ne_zero]
    have : (2 : ℂ) ^ μ * (2 : ℂ) ^ w ≠ 0 := mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))
      (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))
    field_simp
  push_cast
  rw [show (1 : ℂ) - (1 - 2 * (x : ℂ) ^ 2) = 2 * (x : ℂ) ^ 2 by ring,
    show (1 : ℂ) + (1 - 2 * (x : ℂ) ^ 2) = 2 * (1 - (x : ℂ) ^ 2) by ring, hA, hB, hC, hD]
  linear_combination -(x : ℂ) * (x : ℂ) ^ (2 * w) * (1 - (x : ℂ) ^ 2) ^ μ *
    G (1 - 2 * x ^ 2) * h2

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (0 : ℝ)..1,
legendrePolyP (2 * n) x * (x : ℂ) ^ (z - 1) = (-1 : ℂ) ^ n * poch (1 / 2 - z / 2) n / (2 *
poch (z / 2) (n + 1))`. -/
@[dlmf 18.17.E38]
theorem legendre_even_mellin_transform {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendrePolyP (2 * n) x * (x : ℂ) ^ (z - 1) =
      (-1 : ℂ) ^ n * poch (1 / 2 - z / 2) n / (2 * poch (z / 2) (n + 1)) := by
  have hrw : ∀ x : ℝ, legendrePolyP (2 * n) x * (x : ℂ) ^ (z - 1) =
      (1 - (x : ℂ) ^ 2) ^ (0 : ℂ) * (x : ℂ) ^ (z - 1) *
        ((-1 : ℂ) ^ n *
          jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n ((1 - 2 * x ^ 2 : ℝ) : ℂ)) := by
    intro x
    have hp : poch (1 / 2 : ℂ) n ≠ 0 := poch_ne_zero_of_re_pos (by norm_num) n
    rw [cpow_zero, one_mul, legendre_eq_ultrasphPoly,
      ultrasphPoly_quadratic_even (by norm_num : -1 / 2 < (1 / 2 : ℂ).re),
      show 2 * (x : ℂ) ^ 2 - 1 = -((1 - 2 * x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      jacobi_reflection (by norm_num) (by norm_num), div_self hp]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr (fun x _ => hrw x),
    integral_one_sub_sq_cpow_mul_cpow 0 (z - 1)
      (fun s => (-1 : ℂ) ^ n * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s)]
  have hz2 : 0 < (z / 2).re := by simp; linarith
  have hJ := jacobi_mellin_transform (α := -1 / 2) (β := 0) (by norm_num) (by norm_num) hz2 n
  have hint : (∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ ((z - 1 - 1) / 2) * (1 + (s : ℂ)) ^ (0 : ℂ) *
      ((-1 : ℂ) ^ n * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s)) =
      (-1 : ℂ) ^ n * ∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ (z / 2 - 1) *
        (1 + (s : ℂ)) ^ ((0 : ℝ) : ℂ) * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [ofReal_zero]
    rw [show (z - 1 - 1) / 2 = z / 2 - 1 by ring]
    ring
  rw [hint, hJ]
  have hG : Gamma (1 + ((0 : ℝ) : ℂ) + z / 2 + n) = poch (z / 2) (n + 1) * Gamma (z / 2) := by
    rw [← Gamma_add_nat_eq_poch_mul_Gamma hz2]; push_cast; ring_nf
  have hG1 : Gamma (1 + ((0 : ℝ) : ℂ) + n) = n ! := by
    rw [show 1 + ((0 : ℝ) : ℂ) + n = (n : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have h2 : (2 : ℂ) ^ (-((0 : ℂ) + (z - 1 - 1) / 2)) * (2 : ℂ) ^ (((0 : ℝ) : ℂ) + z / 2) = 2 := by
    rw [← cpow_add _ _ two_ne_zero, show -((0 : ℂ) + (z - 1 - 1) / 2) + (((0 : ℝ) : ℂ) + z / 2) = 1
      by push_cast; ring, cpow_one]
  rw [hG, hG1]
  have hp : poch (z / 2) (n + 1) ≠ 0 := poch_ne_zero_of_re_pos hz2 _
  have hg : Gamma (z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hz2
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [show (1 : ℂ) + ((-1 / 2 : ℝ) : ℂ) - z / 2 = 1 / 2 - z / 2 by push_cast; ring]
  generalize (2 : ℂ) ^ (-((0 : ℂ) + (z - 1 - 1) / 2)) = P at h2 ⊢
  generalize (2 : ℂ) ^ (((0 : ℝ) : ℂ) + z / 2) = Q at h2 ⊢
  generalize poch (1 / 2 - z / 2) n = R
  field_simp
  linear_combination 2 * R * h2

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (0 : ℝ)..1,
legendrePolyP (2 * n + 1) x * (x : ℂ) ^ (z - 1) = (-1 : ℂ) ^ n * poch (1 - z / 2) n / (2 *
poch (1 / 2 + z / 2) (n + 1))`. -/
@[dlmf 18.17.E39]
theorem legendre_odd_mellin_transform {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendrePolyP (2 * n + 1) x * (x : ℂ) ^ (z - 1) =
      (-1 : ℂ) ^ n * poch (1 - z / 2) n / (2 * poch (1 / 2 + z / 2) (n + 1)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hrw : Set.EqOn (fun x : ℝ => legendrePolyP (2 * n + 1) x * (x : ℂ) ^ (z - 1))
      (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ (0 : ℂ) * (x : ℂ) ^ z *
        ((-1 : ℂ) ^ n * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n ((1 - 2 * x ^ 2 : ℝ) : ℂ)))
      (Set.Ioo 0 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
    have hp : poch (1 / 2 : ℂ) (n + 1) ≠ 0 := poch_ne_zero_of_re_pos (by norm_num) _
    simp only
    rw [cpow_zero, one_mul, legendre_eq_ultrasphPoly,
      ultrasphPoly_quadratic_odd (by norm_num : -1 / 2 < (1 / 2 : ℂ).re),
      show 2 * (x : ℂ) ^ 2 - 1 = -((1 - 2 * x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      jacobi_reflection (by norm_num) (by norm_num), div_self hp,
      show z = (z - 1) + 1 by ring, cpow_add _ _ hx0, cpow_one, show z - 1 + 1 - 1 = z - 1 by ring]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num) hrw,
    integral_one_sub_sq_cpow_mul_cpow 0 z
      (fun s => (-1 : ℂ) ^ n * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s)]
  have hw : 0 < (1 / 2 + z / 2).re := by simp; linarith
  have hJ := jacobi_mellin_transform (α := 1 / 2) (β := 0) (by norm_num) (by norm_num) hw n
  have hint : (∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ ((z - 1) / 2) * (1 + (s : ℂ)) ^ (0 : ℂ) *
      ((-1 : ℂ) ^ n * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s)) =
      (-1 : ℂ) ^ n * ∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ (1 / 2 + z / 2 - 1) *
        (1 + (s : ℂ)) ^ ((0 : ℝ) : ℂ) * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [ofReal_zero]
    rw [show (z - 1) / 2 = 1 / 2 + z / 2 - 1 by ring]
    ring
  rw [hint, hJ]
  have hG : Gamma (1 + ((0 : ℝ) : ℂ) + (1 / 2 + z / 2) + n) =
      poch (1 / 2 + z / 2) (n + 1) * Gamma (1 / 2 + z / 2) := by
    rw [← Gamma_add_nat_eq_poch_mul_Gamma hw]; push_cast; ring_nf
  have hG1 : Gamma (1 + ((0 : ℝ) : ℂ) + n) = n ! := by
    rw [show 1 + ((0 : ℝ) : ℂ) + n = (n : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have h2 : (2 : ℂ) ^ (-((0 : ℂ) + (z - 1) / 2)) * (2 : ℂ) ^ (((0 : ℝ) : ℂ) + (1 / 2 + z / 2)) =
      2 := by
    rw [← cpow_add _ _ two_ne_zero, show -((0 : ℂ) + (z - 1) / 2) +
      (((0 : ℝ) : ℂ) + (1 / 2 + z / 2)) = 1 by push_cast; ring, cpow_one]
  rw [hG, hG1]
  have hp : poch (1 / 2 + z / 2) (n + 1) ≠ 0 := poch_ne_zero_of_re_pos hw _
  have hg : Gamma (1 / 2 + z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hw
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [show (1 : ℂ) + ((1 / 2 : ℝ) : ℂ) - (1 / 2 + z / 2) = 1 - z / 2 by push_cast; ring]
  generalize (2 : ℂ) ^ (-((0 : ℂ) + (z - 1) / 2)) = P at h2 ⊢
  generalize (2 : ℂ) ^ (((0 : ℝ) : ℂ) + (1 / 2 + z / 2)) = Q at h2 ⊢
  generalize poch (1 - z / 2) n = R
  generalize Gamma (1 / 2 + z / 2) = A at hg ⊢
  generalize poch (1 / 2 + z / 2) (n + 1) = B at hp ⊢
  field_simp
  linear_combination 2 * R * h2

/-- Formula under the stated hypotheses: `∫ t : ℝ in (-1 : ℝ)..1, (legendrePolyP n x -
legendrePolyP n t) / (|x - t| : ℝ) = 2 * (∑ k ∈ Finset.range n, ((k + 1 : ℂ)⁻¹)) *
legendrePolyP n x`. -/
@[dlmf 18.17.E44]
theorem legendre_singular_integral (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    ∫ t : ℝ in (-1 : ℝ)..1, (legendrePolyP n x - legendrePolyP n t) / (|x - t| : ℝ) =
      2 * (∑ k ∈ Finset.range n, ((k + 1 : ℂ)⁻¹)) * legendrePolyP n x := by
  simpa only [LegendreSingular.dq, LegendreSingular.harmonicSum] using
    LegendreSingular.singular_integral n hx

/-- Vandermonde convolution applied to an arbitrary finite coefficient sequence. -/
private lemma binomial_double_sum (m n : ℕ) (f : ℕ → ℂ) :
    (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      (m.choose i : ℂ) * (n.choose j : ℂ) * f (i + j)) =
    ∑ k ∈ Finset.range (m + n + 1), ((m + n).choose k : ℂ) * f k := by
  let ell : ℂ[X] →+ ℂ := {
    toFun := fun p => p.sum (fun k c => c * f k)
    map_zero' := sum_zero_index _
    map_add' := fun p q => sum_add_index p q _ (by simp) (by intros; ring) }
  have hs (k : ℕ) : (X + 1 : ℂ[X]) ^ k =
      ∑ i ∈ Finset.range (k + 1), monomial i (k.choose i : ℂ) := by
    have h := as_sum_range' ((X + 1 : ℂ[X]) ^ k) (k + 1)
      (by simpa only [← C_1, natDegree_pow_X_add_C] using Nat.lt_succ_self k)
    simpa only [coeff_X_add_one_pow] using h
  have h := congrArg ell (pow_add (X + 1 : ℂ[X]) m n).symm
  rw [hs m, hs n, hs (m + n), Finset.sum_mul] at h
  simp only [Finset.mul_sum, map_sum, monomial_mul_monomial] at h
  change (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
    (monomial (i + j) ((m.choose i : ℂ) * (n.choose j : ℂ))).sum (fun k c => c * f k)) =
    (∑ k ∈ Finset.range (m + n + 1),
      (monomial k ((m + n).choose k : ℂ)).sum (fun k c => c * f k)) at h
  simpa only [sum_monomial_index, zero_mul] using h

/-- Finite Gamma-normalized expansion of the Laguerre polynomial divided by its value at zero. -/
theorem laguerrePolyL_normalized_sum {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    laguerrePolyL α n x / laguerrePolyL α n 0 =
      Gamma (α + 1) * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * (-x) ^ i / Gamma (α + 1 + i) := by
  have ha : 0 < (α + 1).re := by simp; linarith
  have hc := not_neg_nat_of_re_pos ha
  have hp : poch (α + 1) n / (n.factorial : ℂ) ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hc n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  rw [laguerrePolyL_at_zero, laguerrePolyL, mul_div_cancel_left₀ _ hp,
    kummerM_eq_sum_neg_nat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpi := poch_ne_zero_of_not_neg_nat hc i
  have hgi := Gamma_ne_zero_of_re_pos (show 0 < (α + 1 + i).re by
    simp; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith)
  have hga := Gamma_ne_zero_of_re_pos ha
  have hg := Gamma_add_nat_div_Gamma_eq (n := i) (α + 1) hc
  change Gamma (α + 1 + i) / Gamma (α + 1) = poch (α + 1) i at hg
  have hfi : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [← hg, neg_pow]
  field_simp
  ring

/-- Power expansion of a normalized Laguerre polynomial with its endpoint weight. -/
theorem laguerrePolyL_normalized_weight_sum {α : ℂ} (hα : -1 < α.re)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ α * laguerrePolyL α n t / laguerrePolyL α n 0 =
      Gamma (α + 1) * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * (-1) ^ i / Gamma (α + 1 + i) * (t : ℂ) ^ (α + i) := by
  rw [mul_div_assoc, laguerrePolyL_normalized_sum hα, ← mul_assoc, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast, neg_pow]
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ t : ℝ in (0 : ℝ)..x, (t : ℂ) ^
(α : ℂ) * laguerrePolyL α m t / laguerrePolyL α m 0 * (x - t : ℂ) ^ (β : ℂ) * laguerrePolyL β
n (x - t) / laguerrePolyL β n 0 = Gamma (α + 1 : ℂ) * Gamma (β + 1 : ℂ) / Gamma (α + β + 2 :
ℂ) * (x : ℂ) ^ (α + β + 1 : ℂ) * laguerrePolyL (α + β + 1) (m + n) x / laguerrePolyL (α + β +
1) (m + n) 0`. -/
@[dlmf 18.17.E47]
theorem laguerrePolyL_convolution {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β) (hx : 0 < x) (m n : ℕ) :
    ∫ t : ℝ in (0 : ℝ)..x, (t : ℂ) ^ (α : ℂ) * laguerrePolyL α m t / laguerrePolyL α m 0 *
      (x - t : ℂ) ^ (β : ℂ) * laguerrePolyL β n (x - t) / laguerrePolyL β n 0 =
      Gamma (α + 1 : ℂ) * Gamma (β + 1 : ℂ) / Gamma (α + β + 2 : ℂ) *
      (x : ℂ) ^ (α + β + 1 : ℂ) * laguerrePolyL (α + β + 1) (m + n) x
          / laguerrePolyL (α + β + 1) (m + n) 0 := by
  have ha : -1 < (α : ℂ).re := hα
  have hb : -1 < (β : ℂ).re := hβ
  have hc : -1 < ((α + β + 1 : ℝ) : ℂ).re := by simp; linarith
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  let F (i j : ℕ) (t : ℝ) : ℂ :=
    (m.choose i : ℂ) * (n.choose j : ℂ) * (-1) ^ (i + j) /
      (Gamma ((α : ℂ) + 1 + i) * Gamma ((β : ℂ) + 1 + j)) *
      ((t : ℂ) ^ ((α : ℂ) + i) * ((x : ℂ) - t) ^ ((β : ℂ) + j))
  have hai (i : ℕ) : -1 < ((α : ℂ) + i).re := by
    simp; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith
  have hbj (j : ℕ) : -1 < ((β : ℂ) + j).re := by
    simp; have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
  have hi (i j : ℕ) : IntervalIntegrable (F i j) volume 0 x :=
    (intervalIntegrable_cpow_mul_sub_cpow (hai i) (hbj j) hx).const_mul _
  have hmoment (i j : ℕ) : (∫ t : ℝ in (0 : ℝ)..x, F i j t) =
      (x : ℂ) ^ ((α : ℂ) + β + 1) *
        ((m.choose i : ℂ) * (n.choose j : ℂ) * (- (x : ℂ)) ^ (i + j) /
          Gamma ((α : ℂ) + β + 2 + (i + j : ℕ))) := by
    dsimp only [F]
    rw [intervalIntegral.integral_const_mul, integral_cpow_mul_sub_cpow (hai i) (hbj j) hx]
    have hga : Gamma ((α : ℂ) + 1 + i) ≠ 0 :=
      Gamma_ne_zero_of_re_pos (by simp; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith)
    have hgb : Gamma ((β : ℂ) + 1 + j) ≠ 0 :=
      Gamma_ne_zero_of_re_pos (by simp; have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith)
    rw [show (α : ℂ) + i + ((β : ℂ) + j) + 1 =
        ((α : ℂ) + β + 1) + (i + j : ℕ) by push_cast; ring,
      cpow_add _ _ hx0, cpow_natCast,
      show (α : ℂ) + i + 1 = (α : ℂ) + 1 + i by ring,
      show (β : ℂ) + j + 1 = (β : ℂ) + 1 + j by ring,
      show (α : ℂ) + i + ((β : ℂ) + j) + 2 =
        (α : ℂ) + β + 2 + (i + j : ℕ) by push_cast; ring]
    rw [neg_pow (x : ℂ)]
    field_simp
  have he : (∫ t : ℝ in (0 : ℝ)..x, (t : ℂ) ^ (α : ℂ) * laguerrePolyL α m t / laguerrePolyL α m 0 *
      (x - t : ℂ) ^ (β : ℂ) * laguerrePolyL β n (x - t) / laguerrePolyL β n 0) =
      Gamma ((α : ℂ) + 1) * Gamma ((β : ℂ) + 1) *
        ∫ t : ℝ in (0 : ℝ)..x, ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), F i j t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hx.le
    intro t ht
    dsimp only
    rw [← ofReal_sub x t]
    have ht' : 0 < x - t := sub_pos.mpr ht.2
    rw [show (t : ℂ) ^ (α : ℂ) * laguerrePolyL α m t / laguerrePolyL α m 0 *
        ((x - t : ℝ) : ℂ) ^ (β : ℂ) * laguerrePolyL β n ((x - t : ℝ) : ℂ) / laguerrePolyL β n 0 =
        ((t : ℂ) ^ (α : ℂ) * laguerrePolyL α m t / laguerrePolyL α m 0) *
        (((x - t : ℝ) : ℂ) ^ (β : ℂ) * laguerrePolyL β n ((x - t : ℝ) : ℂ) / laguerrePolyL β n 0) by
            ring,
      laguerrePolyL_normalized_weight_sum ha m ht.1, laguerrePolyL_normalized_weight_sum hb n ht']
    simp only [Finset.mul_sum, Finset.sum_mul, F, ofReal_sub, pow_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, intervalIntegral.integral_finsetSum
    (f := fun i t => ∑ j ∈ Finset.range (n + 1), F i j t)
    (fun i _ => by
      convert IntervalIntegrable.sum (Finset.range (n + 1)) (fun j _ => hi i j) using 1
      ext t
      simp)]
  have hs (i : ℕ) : (∫ t : ℝ in (0 : ℝ)..x, ∑ j ∈ Finset.range (n + 1), F i j t) =
      ∑ j ∈ Finset.range (n + 1), ∫ t : ℝ in (0 : ℝ)..x, F i j t :=
    intervalIntegral.integral_finsetSum (fun j _ => hi i j)
  simp_rw [hs, hmoment]
  simp only [← Finset.mul_sum, div_eq_mul_inv, mul_assoc]
  have hbin := binomial_double_sum m n (fun k => (- (x : ℂ)) ^ k *
    (Gamma ((α : ℂ) + β + 2 + k))⁻¹)
  simp only [mul_assoc, ← Finset.mul_sum] at hbin
  rw [hbin]
  have hgc : Gamma ((α : ℂ) + β + 2) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hn := laguerrePolyL_normalized_sum hc (m + n) (x : ℂ)
  push_cast at hn
  rw [show (α : ℂ) + β + 1 + 1 = (α : ℂ) + β + 2 by ring] at hn
  simp only [div_eq_mul_inv, mul_assoc] at hn
  rw [hn]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `∫ y : ℝ, (aeval y (hermitePolyH
m) : ℝ) * Real.exp (-(y ^ 2)) * aeval (x - y) (hermitePolyH n) * Real.exp (-((x - y) ^ 2)) =
Real.sqrt Real.pi * (2 : ℝ) ^ (-((m : ℝ) + n + 1) / 2) * aeval (x / Real.sqrt 2) (hermitePolyH
(m + n)) * Real.exp (-(x ^ 2) / 2)`. -/
@[dlmf 18.17.E48]
theorem hermitePolyH_convolution (m n : ℕ) (x : ℝ) :
    ∫ y : ℝ, (aeval y (hermitePolyH m) : ℝ) * Real.exp (-(y ^ 2)) *
      aeval (x - y) (hermitePolyH n) * Real.exp (-((x - y) ^ 2)) =
      Real.sqrt Real.pi * (2 : ℝ) ^ (-((m : ℝ) + n + 1) / 2) *
      aeval (x / Real.sqrt 2) (hermitePolyH (m + n)) * Real.exp (-(x ^ 2) / 2) := by
  let g (j : ℕ) (t : ℝ) := (aeval t (hermitePolyH j) : ℝ) * Real.exp (-(t ^ 2))
  have hg (j : ℕ) (t : ℝ) : HasDerivAt (g j) (-g (j + 1) t) t := by
    simpa only [g, aeval_hermitePolyH_eq_eval] using hasDerivAt_hermite_gauss j t
  have hi (j k : ℕ) : Integrable (fun t => g j t * g k (x - t)) := by
    let q := hermitePolyHR j * (hermitePolyHR k).comp (C x - X)
    have he := (TauCeti.integrable_eval_mul_exp_neg_sq q).mul_bdd
      (by fun_prop : Continuous (fun t : ℝ => Real.exp (-((x - t) ^ 2)))).aestronglyMeasurable
      (Eventually.of_forall fun t => show ‖Real.exp (-((x - t) ^ 2))‖ ≤ (1 : ℝ) by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
        exact neg_nonpos.mpr (sq_nonneg _))
    apply he.congr
    filter_upwards [] with t
    simp only [q, g, eval_mul, eval_comp, eval_sub, eval_C, eval_X,
      aeval_hermitePolyH_eq_eval]
    ring
  have htransfer (j k : ℕ) : (∫ t, g (j + 1) t * g k (x - t)) =
      ∫ t, g j t * g (k + 1) (x - t) := by
    have hv (t : ℝ) : HasDerivAt (fun t => g k (x - t)) (g (k + 1) (x - t)) t := by
      convert (hg k (x - t)).comp t ((hasDerivAt_id t).const_sub x) using 1 <;> first | rfl | ring
    have he := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun t _ => hg j t) (fun t _ => hv t) (hi j (k + 1))
      ((hi (j + 1) k).neg.congr (Eventually.of_forall fun t => by simp)) (hi j k)
    rw [← integral_neg] at he
    simpa only [neg_mul, neg_neg] using he.symm
  have hreduce (j k : ℕ) : (∫ t, g j t * g k (x - t)) = ∫ t, g 0 t * g (j + k) (x - t) := by
    induction j generalizing k with
    | zero => simp
    | succ j ih => rw [htransfer, ih]; congr 1; funext t; congr 2; omega
  let s := Real.sqrt 2
  let r := s⁻¹
  let v := x / s
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = 2 := by simp [s]
  have hr : 0 < r := inv_pos.mpr hs
  have hab : r ^ 2 + (-r) ^ 2 = 1 := by dsimp [r]; field_simp; nlinarith
  have hmoment (k : ℕ) : (∫ u : ℝ, (aeval (r * v - r * u) (hermitePolyH k) : ℝ) *
      Real.exp (-(u ^ 2))) = r ^ k * aeval v (hermitePolyH k) * Real.sqrt π := by
    have hfun (u : ℝ) : (aeval (r * v - r * u) (hermitePolyH k) : ℝ) * Real.exp (-(u ^ 2)) =
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * r ^ i * (-r) ^ (k - i) *
          aeval v (hermitePolyH i) * (aeval u (hermitePolyH (k - i)) * Real.exp (-(u ^ 2))) := by
      rw [show r * v - r * u = r * v + (-r) * u by ring,
        hermitePolyH_addition r (-r) v u hab, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hfun]
    rw [integral_finsetSum _ (fun i _ => by
      simpa only [aeval_hermitePolyH_eq_eval] using
        ((TauCeti.integrable_eval_mul_exp_neg_sq (hermitePolyHR (k - i))).const_mul
          ((k.choose i : ℝ) * r ^ i * (-r) ^ (k - i) * aeval v (hermitePolyH i))))]
    simp_rw [integral_const_mul]
    have hm (i : ℕ) : (∫ u : ℝ, (aeval u (hermitePolyH i) : ℝ) * Real.exp (-(u ^ 2))) =
        if i = 0 then Real.sqrt π else 0 := by
      by_cases hi : i = 0
      · subst i; simpa using hermitePolyH_orthogonality 0 0
      · simpa [hi, Ne.symm hi] using hermitePolyH_orthogonality 0 i
    simp_rw [hm]
    rw [Finset.sum_eq_single k]
    · simp
    · intro i hi hik
      have hiz : k - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
      simp [hiz]
    · simp
  have hbase (k : ℕ) : (∫ t, g 0 t * g k (x - t)) =
      Real.sqrt π * (2 : ℝ) ^ (-((k : ℝ) + 1) / 2) *
        aeval v (hermitePolyH k) * Real.exp (-(x ^ 2) / 2) := by
    let F : ℝ → ℝ := fun t => g 0 t * g k (x - t)
    have hchange : (∫ u : ℝ, F (r * u + x / 2)) = s * ∫ t : ℝ, F t := by
      have he := Measure.integral_comp_mul_left (fun t => F (t + x / 2)) r
      simpa only [integral_add_right_eq_self, r, inv_inv, abs_of_pos hs, smul_eq_mul] using he
    have hfun (u : ℝ) : F (r * u + x / 2) = Real.exp (-(x ^ 2) / 2) *
        ((aeval (r * v - r * u) (hermitePolyH k) : ℝ) * Real.exp (-(u ^ 2))) := by
      have hx : x - (r * u + x / 2) = r * v - r * u := by
        dsimp [r, v]
        field_simp [hs.ne']
        ring_nf
        simp [hs2]
        ring
      dsimp only [F, g]
      simp only [hermitePolyH_zero, map_one, one_mul]
      rw [hx]
      have he : Real.exp (-((r * u + x / 2) ^ 2)) * Real.exp (-((r * v - r * u) ^ 2)) =
          Real.exp (-(x ^ 2) / 2) * Real.exp (-(u ^ 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [r, v]
        field_simp [hs.ne']
        ring_nf
        simp [hs2, show s ^ 3 = 2 * s by rw [pow_succ, hs2],
          show s ^ 4 = 4 by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; norm_num]
        ring
      linear_combination (aeval (r * v - r * u) (hermitePolyH k) : ℝ) * he
    simp_rw [hfun] at hchange
    rw [integral_const_mul, hmoment] at hchange
    have hpow : r ^ k / s = (2 : ℝ) ^ (-((k : ℝ) + 1) / 2) := by
      dsimp [r, s]
      rw [inv_pow, div_eq_mul_inv, ← mul_inv, ← pow_succ, Real.sqrt_eq_rpow,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    apply (mul_left_cancel₀ hs.ne')
    change (s * ∫ t, F t) = _
    rw [← hchange, ← hpow]
    field_simp
  have he := (hreduce m n).trans (hbase (m + n))
  simpa only [g, v, s, Nat.cast_add, mul_assoc] using he

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ, (aeval x (hermitePolyH
(a + b)) : ℝ) * aeval x (hermitePolyH (b + c)) * aeval x (hermitePolyH (c + a)) * Real.exp
(-(x ^ 2)) = 2 ^ (a + b + c) * (a + b).factorial * (b + c).factorial * (c + a).factorial *
Real.sqrt Real.pi / ((a.factorial : ℝ) * b.factorial * c.factorial)`. -/
@[dlmf 18.17.E49]
theorem hermitePolyH_triple_integral (a b c : ℕ) :
    ∫ x : ℝ, (aeval x (hermitePolyH (a + b)) : ℝ) * aeval x (hermitePolyH (b + c)) *
      aeval x (hermitePolyH (c + a)) * Real.exp (-(x ^ 2)) =
      2 ^ (a + b + c) * (a + b).factorial * (b + c).factorial * (c + a).factorial *
      Real.sqrt Real.pi / ((a.factorial : ℝ) * b.factorial * c.factorial) := by
  have hl (m n : ℕ) (x : ℝ) :
      (aeval x (hermitePolyH m) : ℝ) * aeval x (hermitePolyH n) =
        ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℝ) * n.choose k * 2 ^ k * k.factorial *
          aeval x (hermitePolyH (m + n - 2 * k)) := by
    have h := hermitePolyH_linearization m n (x : ℂ)
    have castH (j : ℕ) : (aeval (x : ℂ) (hermitePolyH j) : ℂ) =
        ((aeval x (hermitePolyH j) : ℝ) : ℂ) :=
      aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x (hermitePolyH j)
    simp_rw [castH] at h
    exact_mod_cast h
  have hi (k : ℕ) : Integrable (fun x : ℝ =>
      (aeval x (hermitePolyH (a + b + (b + c) - 2 * k)) : ℝ) *
        aeval x (hermitePolyH (c + a)) * Real.exp (-(x ^ 2))) := by
    simp_rw [aeval_hermitePolyH_eq_eval, ← eval_mul]
    exact TauCeti.integrable_eval_mul_exp_neg_sq _
  have heq : (fun x : ℝ => (aeval x (hermitePolyH (a + b)) : ℝ) *
      aeval x (hermitePolyH (b + c)) * aeval x (hermitePolyH (c + a)) * Real.exp (-(x ^ 2))) =
      fun x => ∑ k ∈ Finset.range (min (a + b) (b + c) + 1),
        ((a + b).choose k : ℝ) * (b + c).choose k * 2 ^ k * k.factorial *
          ((aeval x (hermitePolyH (a + b + (b + c) - 2 * k)) : ℝ) *
            aeval x (hermitePolyH (c + a)) * Real.exp (-(x ^ 2))) := by
    funext x
    rw [hl, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [heq, integral_finsetSum _ (fun k _ => (hi k).const_mul _)]
  simp_rw [integral_const_mul, hermitePolyH_orthogonality]
  rw [Finset.sum_eq_single b]
  · rw [if_pos (by omega : a + b + (b + c) - 2 * b = c + a),
      Nat.cast_choose ℝ (by omega : b ≤ a + b), Nat.cast_choose ℝ (by omega : b ≤ b + c)]
    rw [show a + b - b = a by omega, show b + c - b = c by omega]
    have hp : (2 : ℝ) ^ b * 2 ^ (c + a) = 2 ^ (a + b + c) := by
      rw [← pow_add]; congr 1; omega
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero c)]
    linear_combination ((a + b).factorial : ℝ) * (b + c).factorial * (c + a).factorial *
      Real.sqrt Real.pi * hp
  · intro k hk hkb
    have hneq : a + b + (b + c) - 2 * k ≠ c + a := by
      have := Finset.mem_range.mp hk; omega
    simp [hneq]
  · simp only [Finset.mem_range]
    omega

end DLMF.OrthogonalPolynomials
end
end
