/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.RingTheory.Polynomial.Hermite.Derivative
public import DLMF.Confluent.Asymptotics
public import DLMF.Confluent.Relations

/-!
# Parabolic cylinder functions (Temme §7.3.3; DLMF Chapter 12)

Weber's function `U(a,z)` is the solution of `w'' = (z²/4 + a) w` that is recessive as
`z → +∞`. We define it, following DLMF 12.4.1, through the even and odd Kummer solutions
`u₁(a,z) = e^{-z²/4} M(a/2 + 1/4, 1/2, z²/2)` and `u₂(a,z) = z e^{-z²/4} M(a/2 + 3/4, 3/2, z²/2)`
with the initial values 12.2.6 and 12.2.7. This makes `U(a, ·)` entire for every `a`.

## Main results

* `hasDerivAt_pcfU`, `hasDerivAt_pcfUDeriv`, `deriv_deriv_pcfU`: Weber's equation 12.2.2.
* `pcfU_zero`, `pcfUDeriv_zero`: the initial values.
* `pcfU_neg_half`: `U(-1/2, z) = e^{-z²/4}`.
* `pcfU_eq_kummerU`: `U(a,z) = 2^{-1/4-a/2} e^{-z²/4} U(a/2 + 1/4, 1/2, z²/2)` for `re z > 0`.
* `hasAsymptoticExpansion_pcfU`: `U(a,x) ~ e^{-x²/4} x^{-a-1/2} ∑ (-1)^s (a + 1/2)_{2s}/(s! (2x²)^s)`.
* `IsWeberSol.eq_of_initial`: solutions of Weber's equation are determined by `w(0), w'(0)`
  (via constancy of Wronskians against `u₁, u₂`).
* `pcfU_three_term`, `pcfU_recurrence_add`, `pcfU_recurrence_sub`, `pcfU_deriv_recurrence`:
  the recurrences 12.8.1–12.8.4.
* `pcfD_nat`: `D_n(z) = e^{-z²/4} He_n(z)` (12.7.2).
* `pcfU_eq_integral`: `U(a,z) = e^{-z²/4}/Γ(1/2+a) ∫₀^∞ t^{a-1/2} e^{-t²/2-zt} dt` (12.5.1).
* `pcfU_wronskian_neg`, `pcfU_wronskian_mul_I`, `pcfU_wronskian_mul_neg_I`: the Wronskians
  12.2.11–12.2.12.
* `pcfU_connection_mul_I`, `pcfU_connection_mul_neg_I`: the connection formula 12.2.17.
* `pcfV`: the second solution `V(a,z) = V(a,0) u₁ + V'(a,0) u₂` (12.4.2), entire in `a` and `z`,
  with `pcfV_zero`, `pcfVDeriv_zero` (12.2.8–12.2.9) and Weber's equation.
* `pcfV_wronskian`: `𝒲{U, V} = √(2/π)` (12.2.10).
* `pcfU_neg_eq`, `pcfV_neg_eq`: the connection formulas 12.2.15–12.2.16 for every `a`, with the
  parity cases `pcfU_neg_nat_sub_half_neg`, `pcfV_nat_add_half_neg` (12.2.13–12.2.14) and the
  classical form `pcfV_eq` of `V` in terms of `U(a, ±z)`.
* `pcfV_eq_mul_I`, `pcfV_eq_mul_neg_I`: the connection formula 12.2.20 for every `a`.
* `pcfV_three_term`, `pcfV_recurrence_sub`, `pcfV_recurrence_add`, `pcfV_deriv_recurrence`:
  the recurrences 12.8.5–12.8.8.

Whittaker's `D_ν(z) = U(-ν - 1/2, z)` is `pcfD`.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics Set
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- The even solution `u₁(a,z) = e^{-z²/4} M(a/2 + 1/4, 1/2, z²/2)` (DLMF 12.7.12). -/
@[dlmf 12.7.E12]
def pcfEven (a z : ℂ) : ℂ :=
  exp (-z ^ 2 / 4) * kummerM (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2)

/-- The odd solution `u₂(a,z) = z e^{-z²/4} M(a/2 + 3/4, 3/2, z²/2)` (DLMF 12.7.13). -/
@[dlmf 12.7.E13]
def pcfOdd (a z : ℂ) : ℂ :=
  z * exp (-z ^ 2 / 4) * kummerM (a / 2 + 3 / 4) (3 / 2) (z ^ 2 / 2)

/-- `5/2` is not a nonpositive integer. -/
theorem five_halves_ne_neg_nat : ∀ k : ℕ, (5 / 2 : ℂ) ≠ -k := fun k h => by
  have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- Derivative of `z ↦ M(α, b, z²/2)`: it is `z (α/b) M(α+1, b+1, z²/2)`. -/
theorem hasDerivAt_kummerM_half_sq {α b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasDerivAt (fun z : ℂ => kummerM α b (z ^ 2 / 2))
      (z * (α / b * kummerM (α + 1) (b + 1) (z ^ 2 / 2))) z := by
  have h := (hasDerivAt_kummerM_shift (a := α) hb (z ^ 2 / 2)).comp z
    (((hasDerivAt_pow 2 z).div_const 2))
  exact h.congr_deriv (by push_cast; ring)

/-- `d/dz e^{-z²/4} = -(z/2) e^{-z²/4}`. -/
theorem hasDerivAt_exp_neg_sq_div_four (z : ℂ) :
    HasDerivAt (fun z : ℂ => exp (-z ^ 2 / 4)) (-z / 2 * exp (-z ^ 2 / 4)) z := by
  have h := (((hasDerivAt_pow 2 z).neg).div_const 4).cexp
  exact h.congr_deriv (by simp only [Pi.neg_apply]; push_cast; ring)

/-- The derivative of `u₁`. -/
def pcfEvenDeriv (a z : ℂ) : ℂ :=
  z * exp (-z ^ 2 / 4) * (-(1 / 2) * kummerM (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2) +
    (a + 1 / 2) * kummerM (a / 2 + 1 / 4 + 1) (1 / 2 + 1) (z ^ 2 / 2))

/-- The even Weber solution `pcfEven a` has derivative `pcfEvenDeriv a`. -/
theorem hasDerivAt_pcfEven (a z : ℂ) : HasDerivAt (pcfEven a) (pcfEvenDeriv a z) z := by
  have h := (hasDerivAt_exp_neg_sq_div_four z).mul
    (hasDerivAt_kummerM_half_sq (α := a / 2 + 1 / 4) half_ne_neg_nat z)
  exact h.congr_deriv (by unfold pcfEvenDeriv; ring)

/-- `(pcfEvenDeriv a)' = (z²/4 + a) pcfEven a`, i.e. `pcfEven a` solves Weber's equation `w'' =
(z²/4 + a) w` (DLMF 12.2.2). -/
theorem hasDerivAt_pcfEvenDeriv (a z : ℂ) :
    HasDerivAt (pcfEvenDeriv a) ((z ^ 2 / 4 + a) * pcfEven a z) z := by
  have hb1 : ∀ k : ℕ, (1 / 2 + 1 : ℂ) ≠ -k := by
    norm_num; exact three_half_ne_neg_nat
  have h0 := hasDerivAt_kummerM_half_sq (α := a / 2 + 1 / 4) half_ne_neg_nat z
  have h1 := hasDerivAt_kummerM_half_sq (α := a / 2 + 1 / 4 + 1) hb1 z
  have h := (((hasDerivAt_id z).mul (hasDerivAt_exp_neg_sq_div_four z)).mul
    ((h0.const_mul (-(1 / 2))).add (h1.const_mul (a + 1 / 2))))
  have hc := kummerM_ode_contiguous (a := a / 2 + 1 / 4) (b := 1 / 2) half_ne_neg_nat
    (z := z ^ 2 / 2)
  refine h.congr_deriv ?_
  unfold pcfEven
  simp only [id, Pi.add_apply, Pi.mul_apply]
  rw [show a / 2 + 1 / 4 + 1 + 1 = a / 2 + 1 / 4 + 2 by ring]
  norm_num at hc ⊢
  linear_combination (exp (-z ^ 2 / 4) * (8 * (a / 2 + 1 / 4) / 3)) * hc

/-- The derivative of `u₂`. -/
def pcfOddDeriv (a z : ℂ) : ℂ :=
  exp (-z ^ 2 / 4) * ((1 - z ^ 2 / 2) * kummerM (a / 2 + 3 / 4) (3 / 2) (z ^ 2 / 2) +
    (a + 3 / 2) / 3 * z ^ 2 * kummerM (a / 2 + 3 / 4 + 1) (3 / 2 + 1) (z ^ 2 / 2))

/-- The odd Weber solution `pcfOdd a` has derivative `pcfOddDeriv a`. -/
theorem hasDerivAt_pcfOdd (a z : ℂ) : HasDerivAt (pcfOdd a) (pcfOddDeriv a z) z := by
  have h := ((hasDerivAt_id z).mul (hasDerivAt_exp_neg_sq_div_four z)).mul
    (hasDerivAt_kummerM_half_sq (α := a / 2 + 3 / 4) three_half_ne_neg_nat z)
  exact h.congr_deriv (by unfold pcfOddDeriv; simp only [id, Pi.mul_apply]; ring)

/-- `(pcfOddDeriv a)' = (z²/4 + a) pcfOdd a`, i.e. `pcfOdd a` solves Weber's equation. -/
theorem hasDerivAt_pcfOddDeriv (a z : ℂ) :
    HasDerivAt (pcfOddDeriv a) ((z ^ 2 / 4 + a) * pcfOdd a z) z := by
  have hb1 : ∀ k : ℕ, (3 / 2 + 1 : ℂ) ≠ -k := by
    norm_num; exact five_halves_ne_neg_nat
  have h0 := hasDerivAt_kummerM_half_sq (α := a / 2 + 3 / 4) three_half_ne_neg_nat z
  have h1 := hasDerivAt_kummerM_half_sq (α := a / 2 + 3 / 4 + 1) hb1 z
  have h := (hasDerivAt_exp_neg_sq_div_four z).mul
    ((((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_pow 2 z).div_const 2)).mul h0).add
      (((hasDerivAt_pow 2 z).const_mul ((a + 3 / 2) / 3)).mul h1))
  have hc := kummerM_ode_contiguous (a := a / 2 + 3 / 4) (b := 3 / 2)
    three_half_ne_neg_nat (z := z ^ 2 / 2)
  refine h.congr_deriv ?_
  unfold pcfOdd
  rw [show a / 2 + 3 / 4 + 1 + 1 = a / 2 + 3 / 4 + 2 by ring]
  norm_num at hc ⊢
  linear_combination (exp (-z ^ 2 / 4) * (8 * (a / 2 + 3 / 4) * z / 15)) * hc

/-- **Weber's parabolic cylinder function** `U(a,z)`, the entire solution of
`w'' = (z²/4 + a) w` fixed by its initial values (DLMF 12.2.6, 12.2.7, 12.4.1):
`U(a,z) = U(a,0) u₁(a,z) + U'(a,0) u₂(a,z)`. The reciprocal Gamma factors vanish at the
poles, as for the entire function `1/Γ`. -/
@[dlmf 12.4.E1]
def pcfU (a z : ℂ) : ℂ :=
  (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ * pcfEven a z -
    (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹ * pcfOdd a z

/-- The derivative `U'(a,z)`. -/
def pcfUDeriv (a z : ℂ) : ℂ :=
  (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ *
      pcfEvenDeriv a z -
    (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹ * pcfOddDeriv a z

/-- Whittaker's notation `D_ν(z) = U(-ν - 1/2, z)` (DLMF 12.2.5). -/
@[dlmf 12.2.E5]
def pcfD (ν z : ℂ) : ℂ := pcfU (-ν - 1 / 2) z

/-- `U(a,·)` has derivative `pcfUDeriv a`. -/
theorem hasDerivAt_pcfU (a z : ℂ) : HasDerivAt (pcfU a) (pcfUDeriv a z) z :=
  ((hasDerivAt_pcfEven a z).const_mul _).sub ((hasDerivAt_pcfOdd a z).const_mul _)

/-- **Weber's equation** (DLMF 12.2.2): `U''(a,z) = (z²/4 + a) U(a,z)`. -/
@[dlmf 12.2.E2]
theorem hasDerivAt_pcfUDeriv (a z : ℂ) :
    HasDerivAt (pcfUDeriv a) ((z ^ 2 / 4 + a) * pcfU a z) z := by
  refine (((hasDerivAt_pcfEvenDeriv a z).const_mul _).sub
    ((hasDerivAt_pcfOddDeriv a z).const_mul _)).congr_deriv ?_
  rw [pcfU]
  ring

/-- Weber's equation in `deriv` form. -/
theorem deriv_deriv_pcfU (a z : ℂ) :
    deriv (deriv (pcfU a)) z = (z ^ 2 / 4 + a) * pcfU a z := by
  have : deriv (pcfU a) = pcfUDeriv a := funext fun w => (hasDerivAt_pcfU a w).deriv
  rw [this, (hasDerivAt_pcfUDeriv a z).deriv]

/-- `U(a,0)` (DLMF 12.2.6). -/
@[dlmf 12.2.E6]
theorem pcfU_zero (a : ℂ) :
    pcfU a 0 = (Real.sqrt π : ℂ) / ((2 : ℂ) ^ (a / 2 + 1 / 4) * Gamma (3 / 4 + a / 2)) := by
  simp only [pcfU, pcfEven, pcfOdd, zero_pow two_ne_zero, zero_div, neg_zero, Complex.exp_zero,
    kummerM_zero, mul_zero, sub_zero, mul_one, Complex.cpow_neg]
  field_simp

/-- `U'(a,0)` (DLMF 12.2.7). -/
@[dlmf 12.2.E7]
theorem pcfUDeriv_zero (a : ℂ) :
    pcfUDeriv a 0 = -(Real.sqrt π : ℂ) / ((2 : ℂ) ^ (a / 2 - 1 / 4) * Gamma (1 / 4 + a / 2)) := by
  simp only [pcfUDeriv, pcfEvenDeriv, pcfOddDeriv, zero_pow two_ne_zero, zero_div, neg_zero,
    Complex.exp_zero, kummerM_zero, zero_mul, mul_zero, sub_zero, mul_one, add_zero,
    zero_sub, Complex.cpow_neg]
  field_simp

/-- `U(-1/2, z) = D_0(z) = e^{-z²/4}` (DLMF 12.7.1). -/
@[dlmf 12.7.E1]
theorem pcfU_neg_half (z : ℂ) : pcfU (-1 / 2) z = exp (-z ^ 2 / 4) := by
  have h1 : (3 / 4 + -1 / 2 / 2 : ℂ) = 1 / 2 := by ring
  have h2 : (1 / 4 + -1 / 2 / 2 : ℂ) = 0 := by ring
  have h3 : (-1 / 2 / 2 + 1 / 4 : ℂ) = 0 := by ring
  rw [pcfU, pcfEven, h1, h2, h3, Complex.Gamma_zero, inv_zero, Gamma_one_half_eq_sqrt,
    kummerM_of_zero_param, neg_zero, Complex.cpow_zero]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  ring

/-- `2^{1/2} = √2` as complex numbers. -/
theorem two_cpow_half : (2 : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num)]
  norm_num

/-- **`U(a,z)` through Tricomi's function** (DLMF 12.7.14), for `re z > 0`:
`U(a,z) = 2^{-1/4 - a/2} e^{-z²/4} U(a/2 + 1/4, 1/2, z²/2)`. -/
@[dlmf 12.7.E14]
theorem pcfU_eq_kummerU (a : ℂ) {z : ℂ} (hre : 0 < z.re) :
    pcfU a z = (2 : ℂ) ^ (-(1 / 4) - a / 2) * exp (-z ^ 2 / 4) *
      kummerU (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2) := by
  have hb : ∀ k : ℤ, (1 / 2 : ℂ) ≠ k := fun k h => by
    have := congrArg Complex.re h
    simp at this
    have h2 : (2 : ℝ) * k = 1 := by linarith
    have : (2 : ℤ) * k = 1 := by exact_mod_cast h2
    omega
  set s2 : ℂ := (Real.sqrt 2 : ℂ) with hs2
  have hs2sq : s2 * s2 = 2 := by
    rw [hs2, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs20 : s2 ≠ 0 := by intro h; rw [h, zero_mul] at hs2sq; norm_num at hs2sq
  have hy : z ^ 2 / 2 = (z / s2) ^ 2 := by
    rw [div_pow, sq s2, hs2sq]
  have hre' : 0 < (z / s2).re := by
    rw [hs2, Complex.div_ofReal_re]
    exact div_pos hre (Real.sqrt_pos.mpr (by norm_num))
  have hsqrt : (z ^ 2 / 2) ^ (1 / 2 : ℂ) = z / s2 := by
    rw [hy, sq_cpow_of_re_pos hre', show (2 : ℂ) * (1 / 2) = 1 by norm_num, Complex.cpow_one]
  have hGm : Gamma (-1 / 2 : ℂ) = -2 * (Real.sqrt π : ℂ) := by
    have h := Complex.Gamma_add_one (-1 / 2 : ℂ) (by norm_num)
    rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by ring, Gamma_one_half_eq_sqrt] at h
    linear_combination 2 * h
  have h2pow : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) = (2 : ℂ) ^ (-(1 / 4) - a / 2) * s2 := by
    rw [hs2, ← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero]
    ring_nf
  rw [kummerU_eq_connection _ _ _ hb, kummerUConnection, pcfU, pcfEven, pcfOdd,
    show (1 : ℂ) - 1 / 2 = 1 / 2 by ring, show a / 2 + 1 / 4 - 1 / 2 + 1 = 3 / 4 + a / 2 by ring,
    show (1 / 2 : ℂ) - 1 = -1 / 2 by ring, show (2 : ℂ) - 1 / 2 = 3 / 2 by ring,
    show a / 2 + 3 / 4 = 3 / 4 + a / 2 by ring, show a / 2 + 1 / 4 = 1 / 4 + a / 2 by ring,
    hsqrt, hGm, Gamma_one_half_eq_sqrt, h2pow, show -(1 / 4 + a / 2) = -(1 / 4) - a / 2 by ring]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  generalize kummerM (3 / 4 + a / 2) (3 / 2) (z ^ 2 / 2) = N
  generalize kummerM (1 / 4 + a / 2) (1 / 2) (z ^ 2 / 2) = M
  generalize Gamma (1 / 4 + a / 2) = G1
  generalize Gamma (3 / 4 + a / 2) = G3
  field_simp
  linear_combination (-(z * N * G1⁻¹)) * hs2sq

/-- Legendre duplication for Pochhammer symbols: `(2c)_{2s} = 4^s (c)_s (c + 1/2)_s`. -/
theorem poch_two_mul (c : ℂ) (s : ℕ) :
    poch (2 * c) (2 * s) = 4 ^ s * poch c s * poch (c + 1 / 2) s := by
  induction s with
  | zero => simp [poch_zero]
  | succ s ih =>
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring, poch_succ, poch_succ, ih, poch_succ c,
      poch_succ (c + 1 / 2), pow_succ]
    push_cast
    ring

/-- **Asymptotic expansion of `U(a,x)`** (DLMF 12.9.1, Temme §7.3.3):
`U(a,x) ~ e^{-x²/4} x^{-a-1/2} ∑ (-1)^s (a + 1/2)_{2s} / (s! (2x²)^s)` as `x → +∞`. -/
@[dlmf 12.9.E1]
theorem hasAsymptoticExpansion_pcfU (a : ℂ) :
    HasAsymptoticExpansion atTop
      (fun (s : ℕ) (x : ℝ) => exp (-(x : ℂ) ^ 2 / 4) * (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ)))
      (fun s => (-1) ^ s * poch (a + 1 / 2) (2 * s) / (2 ^ s * s.factorial))
      (fun x : ℝ => pcfU a x) := by
  set α : ℂ := a / 2 + 1 / 4 with hα
  have hsq : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h := (((hasAsymptoticExpansion_kummerU α (1 / 2)).comp_tendsto hsq).mul_left
    (fun x : ℝ => (2 : ℂ) ^ (-(1 / 4) - a / 2) * exp (-(x : ℂ) ^ 2 / 4))).smul_scale
    (κ := fun s => (2 : ℂ) ^ s) (ψ := fun (s : ℕ) (x : ℝ) =>
      exp (-(x : ℂ) ^ 2 / 4) * (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ))) (fun s => ?_)
  · refine (h.congr' ?_).congr_coeff ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [Function.comp_apply, smul_eq_mul]
      rw [pcfU_eq_kummerU a (by simpa using hx)]
      push_cast
      ring
    · funext s
      rw [tricomiCoeff, show α - 1 / 2 + 1 = α + 1 / 2 by ring, smul_eq_mul,
        show a + 1 / 2 = 2 * α by rw [hα]; ring, poch_two_mul]
      have hf : (s.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.factorial_ne_zero
      rw [show (4 : ℂ) ^ s = 2 ^ s * 2 ^ s by rw [← mul_pow]; norm_num]
      field_simp
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hxy : (((x ^ 2 / 2 : ℝ)) : ℂ) ^ (-((s : ℂ) + α)) =
        (x : ℂ) ^ (2 * (-((s : ℂ) + α))) * (2 : ℂ) ^ ((s : ℂ) + α) := by
      rw [show (x ^ 2 / 2 : ℝ) = x ^ 2 * (1 / 2) by ring, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (by positivity) (by norm_num), Complex.ofReal_pow,
        sq_cpow_of_re_pos (by simpa using hx), one_div, Complex.ofReal_inv,
        Complex.inv_cpow _ _ (by norm_num [Complex.arg_ofReal_of_nonneg, Real.pi_pos.ne]),
        ← Complex.cpow_neg]
      push_cast
      ring_nf
    rw [hxy]
    have h2 : (2 : ℂ) ^ (-(1 / 4) - a / 2) * (2 : ℂ) ^ ((s : ℂ) + α) = 2 ^ s := by
      rw [← Complex.cpow_add _ _ two_ne_zero, hα,
        show -(1 / 4) - a / 2 + ((s : ℂ) + (a / 2 + 1 / 4)) = (s : ℂ) by ring,
        Complex.cpow_natCast]
    rw [show (x : ℂ) ^ (2 * (-((s : ℂ) + α))) = (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ)) by
      rw [hα]; ring_nf]
    linear_combination (exp (-(x : ℂ) ^ 2 / 4) * (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ))) * h2


/-! ### Uniqueness for Weber's equation -/

/-- The even Weber solution takes the value `1` at `0`. -/
theorem pcfEven_zero (a : ℂ) : pcfEven a 0 = 1 := by
  simp [pcfEven, kummerM_zero]

/-- The derivative of the even Weber solution vanishes at `0`. -/
theorem pcfEvenDeriv_zero (a : ℂ) : pcfEvenDeriv a 0 = 0 := by
  simp [pcfEvenDeriv]

/-- The odd Weber solution vanishes at `0`. -/
theorem pcfOdd_zero (a : ℂ) : pcfOdd a 0 = 0 := by
  simp [pcfOdd]

/-- The derivative of the odd Weber solution is `1` at `0`. -/
theorem pcfOddDeriv_zero (a : ℂ) : pcfOddDeriv a 0 = 1 := by
  simp [pcfOddDeriv, kummerM_zero]

/-- A function and a derivative candidate solve Weber's equation with parameter `a`. -/
def IsWeberSol (a : ℂ) (f f' : ℂ → ℂ) : Prop :=
  ∀ z, HasDerivAt f (f' z) z ∧ HasDerivAt f' ((z ^ 2 / 4 + a) * f z) z

/-- The even Weber solution solves Weber's equation, with derivative `pcfEvenDeriv a`. -/
theorem isWeberSol_pcfEven (a : ℂ) : IsWeberSol a (pcfEven a) (pcfEvenDeriv a) :=
  fun z => ⟨hasDerivAt_pcfEven a z, hasDerivAt_pcfEvenDeriv a z⟩

/-- The odd Weber solution solves Weber's equation, with derivative `pcfOddDeriv a`. -/
theorem isWeberSol_pcfOdd (a : ℂ) : IsWeberSol a (pcfOdd a) (pcfOddDeriv a) :=
  fun z => ⟨hasDerivAt_pcfOdd a z, hasDerivAt_pcfOddDeriv a z⟩

/-- `U(a,z)` solves Weber's equation, with derivative `pcfUDeriv a`. -/
theorem isWeberSol_pcfU (a : ℂ) : IsWeberSol a (pcfU a) (pcfUDeriv a) :=
  fun z => ⟨hasDerivAt_pcfU a z, hasDerivAt_pcfUDeriv a z⟩

/-- The Wronskian of two solutions of Weber's equation is constant. -/
theorem IsWeberSol.wronskian_eq {a : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsWeberSol a f f')
    (hg : IsWeberSol a g g') (z : ℂ) :
    f z * g' z - f' z * g z = f 0 * g' 0 - f' 0 * g 0 := by
  have hd : ∀ w, HasDerivAt (fun w => f w * g' w - f' w * g w) 0 w := fun w =>
    (((hf w).1.mul (hg w).2).sub ((hf w).2.mul (hg w).1)).congr_deriv (by ring)
  exact is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0

/-- A solution of Weber's equation with vanishing initial data vanishes identically. -/
theorem IsWeberSol.eq_zero {a : ℂ} {f f' : ℂ → ℂ} (hf : IsWeberSol a f f') (h0 : f 0 = 0)
    (h1 : f' 0 = 0) (z : ℂ) : f z = 0 := by
  have h₁ := hf.wronskian_eq (isWeberSol_pcfEven a) z
  have h₂ := hf.wronskian_eq (isWeberSol_pcfOdd a) z
  have h₃ := (isWeberSol_pcfEven a).wronskian_eq (isWeberSol_pcfOdd a) z
  simp only [h0, h1, pcfEven_zero, pcfEvenDeriv_zero, pcfOdd_zero, pcfOddDeriv_zero] at h₁ h₂ h₃
  linear_combination (-(pcfOdd a z)) * h₁ + pcfEven a z * h₂ - f z * h₃

/-- Solutions of Weber's equation are determined by their initial data. -/
theorem IsWeberSol.eq_of_initial {a : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsWeberSol a f f')
    (hg : IsWeberSol a g g') (h0 : f 0 = g 0) (h1 : f' 0 = g' 0) (z : ℂ) : f z = g z := by
  have hd : IsWeberSol a (fun w => f w - g w) (fun w => f' w - g' w) := fun w =>
    ⟨(hf w).1.sub (hg w).1, ((hf w).2.sub (hg w).2).congr_deriv (by ring)⟩
  exact sub_eq_zero.mp (hd.eq_zero (by simp [h0]) (by simp [h1]) z)

/-! ### Recurrences (DLMF 12.8) -/

/-- `U(a,0) = √π 2^{-(a/2+1/4)} / Γ(3/4 + a/2)` (DLMF 12.2.6). -/
theorem pcfU_zero' (a : ℂ) :
    pcfU a 0 = (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ := by
  simp [pcfU, pcfEven_zero, pcfOdd_zero]

/-- `U'(a,0) = -√π 2^{-(a/2-1/4)} / Γ(1/4 + a/2)` (DLMF 12.2.7). -/
theorem pcfUDeriv_zero' (a : ℂ) :
    pcfUDeriv a 0 =
      -((Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹) := by
  simp [pcfUDeriv, pcfEvenDeriv_zero, pcfOddDeriv_zero]

/-- `s / Γ(s + 1) = 1 / Γ(s)` for every complex `s`, with Mathlib's totalized `Γ`. -/
theorem mul_recip_Gamma_add_one' (s : ℂ) : s * (Gamma (s + 1))⁻¹ = (Gamma s)⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  rw [Complex.Gamma_add_one s hs]
  rcases eq_or_ne (Gamma s) 0 with hg | hg
  · simp [hg]
  · field_simp

/-- `2^{x-1} = 2^x/2`. -/
theorem two_cpow_sub_one (x : ℂ) : (2 : ℂ) ^ (x - 1) = (2 : ℂ) ^ x / 2 := by
  rw [Complex.cpow_sub _ _ two_ne_zero, Complex.cpow_one]

/-- `deriv (U(a,·)) = pcfUDeriv a`. -/
theorem deriv_pcfU (a : ℂ) : deriv (pcfU a) = pcfUDeriv a :=
  funext fun z => (hasDerivAt_pcfU a z).deriv

/-- DLMF 12.8.3: `U'(a,z) - (z/2) U(a,z) + U(a-1,z) = 0`. -/
@[dlmf 12.8.E3]
theorem pcfU_recurrence_sub (a z : ℂ) :
    deriv (pcfU a) z - z / 2 * pcfU a z + pcfU (a - 1) z = 0 := by
  rw [deriv_pcfU]
  have hs : IsWeberSol (a - 1) (fun w => pcfUDeriv a w - w / 2 * pcfU a w + pcfU (a - 1) w)
      (fun w => (w ^ 2 / 4 + a) * pcfU a w - 1 / 2 * pcfU a w - w / 2 * pcfUDeriv a w +
        pcfUDeriv (a - 1) w) := fun w => by
    have hU := hasDerivAt_pcfU a w
    have hU' := hasDerivAt_pcfUDeriv a w
    have hV := hasDerivAt_pcfU (a - 1) w
    have hV' := hasDerivAt_pcfUDeriv (a - 1) w
    refine ⟨(hU'.sub (((hasDerivAt_id w).div_const 2).mul hU)).add hV |>.congr_deriv ?_, ?_⟩
    · simp only [id]; ring
    · refine ((((((hasDerivAt_pow 2 w).div_const 4).add_const a).mul hU).sub
        (hU.const_mul (1 / 2))).sub (((hasDerivAt_id w).div_const 2).mul hU')).add hV'
        |>.congr_deriv ?_
      simp only [id]; push_cast; ring
  have h0 : pcfUDeriv a 0 - 0 / 2 * pcfU a 0 + pcfU (a - 1) 0 = 0 := by
    rw [pcfUDeriv_zero' a, pcfU_zero' a, pcfU_zero' (a - 1),
      show 3 / 4 + (a - 1) / 2 = 1 / 4 + a / 2 by ring,
      show -((a - 1) / 2 + 1 / 4) = -(a / 2 - 1 / 4) by ring]
    ring
  have h1 : ((0 : ℂ) ^ 2 / 4 + a) * pcfU a 0 - 1 / 2 * pcfU a 0 - 0 / 2 * pcfUDeriv a 0 +
      pcfUDeriv (a - 1) 0 = 0 := by
    have hg := mul_recip_Gamma_add_one' (a / 2 - 1 / 4)
    rw [show a / 2 - 1 / 4 + 1 = 3 / 4 + a / 2 by ring] at hg
    rw [pcfUDeriv_zero' a, pcfU_zero' a, pcfUDeriv_zero' (a - 1),
      show 1 / 4 + (a - 1) / 2 = a / 2 - 1 / 4 by ring,
      show -((a - 1) / 2 - 1 / 4) = -(a / 2 + 1 / 4) + 1 by ring,
      Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one, ← hg]
    ring
  exact hs.eq_zero h0 h1 z

/-- DLMF 12.8.2: `U'(a,z) + (z/2) U(a,z) + (a + 1/2) U(a+1,z) = 0`. -/
@[dlmf 12.8.E2]
theorem pcfU_recurrence_add (a z : ℂ) :
    deriv (pcfU a) z + z / 2 * pcfU a z + (a + 1 / 2) * pcfU (a + 1) z = 0 := by
  rw [deriv_pcfU]
  have hs : IsWeberSol (a + 1)
      (fun w => pcfUDeriv a w + w / 2 * pcfU a w + (a + 1 / 2) * pcfU (a + 1) w)
      (fun w => (w ^ 2 / 4 + a) * pcfU a w + 1 / 2 * pcfU a w + w / 2 * pcfUDeriv a w +
        (a + 1 / 2) * pcfUDeriv (a + 1) w) := fun w => by
    have hU := hasDerivAt_pcfU a w
    have hU' := hasDerivAt_pcfUDeriv a w
    have hV := hasDerivAt_pcfU (a + 1) w
    have hV' := hasDerivAt_pcfUDeriv (a + 1) w
    refine ⟨(hU'.add (((hasDerivAt_id w).div_const 2).mul hU)).add (hV.const_mul (a + 1 / 2))
      |>.congr_deriv ?_, ?_⟩
    · simp only [id]; ring
    · refine ((((((hasDerivAt_pow 2 w).div_const 4).add_const a).mul hU).add
        (hU.const_mul (1 / 2))).add (((hasDerivAt_id w).div_const 2).mul hU')).add
        (hV'.const_mul (a + 1 / 2)) |>.congr_deriv ?_
      simp only [id]; push_cast; ring
  have h0 : pcfUDeriv a 0 + 0 / 2 * pcfU a 0 + (a + 1 / 2) * pcfU (a + 1) 0 = 0 := by
    have hg := mul_recip_Gamma_add_one' (1 / 4 + a / 2)
    rw [show 1 / 4 + a / 2 + 1 = 3 / 4 + (a + 1) / 2 by ring] at hg
    rw [pcfUDeriv_zero' a, pcfU_zero' a, pcfU_zero' (a + 1),
      show -((a + 1) / 2 + 1 / 4) = -(a / 2 - 1 / 4) - 1 by ring,
      two_cpow_sub_one, ← hg]
    ring
  have h1 : ((0 : ℂ) ^ 2 / 4 + a) * pcfU a 0 + 1 / 2 * pcfU a 0 + 0 / 2 * pcfUDeriv a 0 +
      (a + 1 / 2) * pcfUDeriv (a + 1) 0 = 0 := by
    rw [pcfUDeriv_zero' a, pcfU_zero' a, pcfUDeriv_zero' (a + 1),
      show 1 / 4 + (a + 1) / 2 = 3 / 4 + a / 2 by ring,
      show -((a + 1) / 2 - 1 / 4) = -(a / 2 + 1 / 4) by ring]
    ring
  exact hs.eq_zero h0 h1 z

/-- DLMF 12.8.1: `z U(a,z) - U(a-1,z) + (a + 1/2) U(a+1,z) = 0`. -/
@[dlmf 12.8.E1]
theorem pcfU_three_term (a z : ℂ) :
    z * pcfU a z - pcfU (a - 1) z + (a + 1 / 2) * pcfU (a + 1) z = 0 := by
  linear_combination pcfU_recurrence_add a z - pcfU_recurrence_sub a z

/-- DLMF 12.8.4: `2 U'(a,z) + U(a-1,z) + (a + 1/2) U(a+1,z) = 0`. -/
@[dlmf 12.8.E4]
theorem pcfU_deriv_recurrence (a z : ℂ) :
    2 * deriv (pcfU a) z + pcfU (a - 1) z + (a + 1 / 2) * pcfU (a + 1) z = 0 := by
  linear_combination pcfU_recurrence_add a z + pcfU_recurrence_sub a z

/-! ### Hermite specializations (DLMF 12.7) -/

section Hermite

open Polynomial

/-- `U'(-1/2, z) = -(z/2) e^{-z²/4}`. -/
theorem pcfUDeriv_neg_half (z : ℂ) : pcfUDeriv (-1 / 2) z = -z / 2 * exp (-z ^ 2 / 4) := by
  have h : pcfU (-1 / 2) = fun z => exp (-z ^ 2 / 4) := funext pcfU_neg_half
  have hd := hasDerivAt_pcfU (-1 / 2) z
  rw [h] at hd
  exact hd.unique (hasDerivAt_exp_neg_sq_div_four z)

/-- The recurrence 12.8.1 in Whittaker's notation: `D_{ν+2} = z D_{ν+1} - (ν+1) D_ν`. -/
theorem pcfD_add_two (ν z : ℂ) :
    pcfD (ν + 2) z = z * pcfD (ν + 1) z - (ν + 1) * pcfD ν z := by
  have h := pcfU_three_term (-(ν + 1) - 1 / 2) z
  rw [show -(ν + 1) - 1 / 2 - 1 = -(ν + 2) - 1 / 2 by ring,
    show -(ν + 1) - 1 / 2 + 1 = -ν - 1 / 2 by ring] at h
  simp only [pcfD]
  linear_combination -h

/-- **`D_n(z) = e^{-z²/4} He_n(z)`** (DLMF 12.7.2), with Mathlib's probabilists' Hermite
polynomials `He_n = Polynomial.hermite n`. -/
@[dlmf 12.7.E2]
theorem pcfD_nat (n : ℕ) (z : ℂ) : pcfD n z = exp (-z ^ 2 / 4) * aeval z (hermite n) := by
  have key : ∀ n : ℕ, pcfD n z = exp (-z ^ 2 / 4) * aeval z (hermite n) ∧
      pcfD (n + 1 : ℕ) z = exp (-z ^ 2 / 4) * aeval z (hermite (n + 1)) := by
    intro n
    induction n with
    | zero =>
      constructor
      · simp only [pcfD, Nat.cast_zero, hermite_zero, map_one, mul_one]
        rw [show -(0 : ℂ) - 1 / 2 = -1 / 2 by ring, pcfU_neg_half]
      · have h := pcfU_recurrence_sub (-1 / 2) z
        rw [deriv_pcfU, pcfUDeriv_neg_half, pcfU_neg_half] at h
        simp only [pcfD, zero_add, Nat.cast_one, hermite_one, aeval_X]
        rw [show (-1 : ℂ) - 1 / 2 = -1 / 2 - 1 by ring]
        linear_combination h
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := pcfD_add_two (n : ℂ) z
      rw [show (n : ℂ) + 2 = ((n + 1 + 1 : ℕ) : ℂ) by push_cast; ring,
        show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, ih.1, ih.2] at h
      rw [h, hermite_add_two]
      simp only [map_sub, map_mul, aeval_X, nsmul_eq_mul, map_natCast]
      push_cast
      ring
  exact (key n).1

end Hermite

/-! ### The Laplace-type integral 12.5.1 -/

/-- The moments `∫₀^∞ t^c e^{-t²/2 - z t} dt` used in DLMF 12.5.1. -/
def pcfMoment (c z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)

/-- `-t²/2 - xt ≤ -t²/4 + x²`. -/
theorem pcf_exponent_le (t x : ℝ) : -t ^ 2 / 2 - x * t ≤ -t ^ 2 / 4 + x ^ 2 := by
  nlinarith [sq_nonneg (t / 2 + x)]

/-- For `t > 0`, `|t^c e^{-t²/2 - zt}| = t^{Re c} e^{-t²/2 - (Re z) t}`. -/
theorem norm_pcfIntegrand (c z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)‖ =
      t ^ c.re * Real.exp (-t ^ 2 / 2 - z.re * t) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  congr 2
  simp [Complex.sub_re, Complex.mul_re, sq]

/-- For `|Re z| ≤ R` and `t > 0`, `|t^c e^{-t²/2 - zt}| ≤ e^{R²} t^{Re c} e^{-t²/4}`. -/
theorem norm_pcfIntegrand_le (c z : ℂ) {R : ℝ} (hR : |z.re| ≤ R) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)‖ ≤
      Real.exp (R ^ 2) * (t ^ c.re * Real.exp (-t ^ 2 / 4)) := by
  rw [norm_pcfIntegrand c z ht]
  have hx : z.re ^ 2 ≤ R ^ 2 := by
    have := sq_abs z.re ▸ pow_le_pow_left₀ (abs_nonneg _) hR 2
    exact this
  have he : Real.exp (-t ^ 2 / 2 - z.re * t) ≤ Real.exp (R ^ 2) * Real.exp (-t ^ 2 / 4) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [pcf_exponent_le t z.re])
  calc t ^ c.re * Real.exp (-t ^ 2 / 2 - z.re * t)
      ≤ t ^ c.re * (Real.exp (R ^ 2) * Real.exp (-t ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le _)
    _ = _ := by ring

/-- For `p > -1`, `t^p e^{-t²/4}` is integrable on `(0, ∞)`. -/
theorem integrableOn_rpow_mul_exp_neg_sq_div_four {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun t : ℝ => t ^ p * Real.exp (-t ^ 2 / 4)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := p) (p := 2) (b := 1 / 4) hp
    (by norm_num) (by norm_num)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only
  rw [show (t ^ (2 : ℝ)) = t ^ 2 from Real.rpow_two t]
  ring_nf

/-- The integrand `t^c e^{-t²/2 - zt}` is continuous on `(0, ∞)`. -/
theorem continuousOn_pcfIntegrand (c z : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)) (Ioi 0) := by
  refine ContinuousOn.mul (fun t ht => ?_) (by fun_prop)
  exact (Complex.continuousAt_ofReal_cpow_const t c (Or.inr (ne_of_gt ht))).continuousWithinAt

/-- For `Re c > -1`, the integrand `t^c e^{-t²/2 - zt}` is integrable on `(0, ∞)`. -/
theorem integrableOn_pcfIntegrand {c : ℂ} (hc : -1 < c.re) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_rpow_mul_exp_neg_sq_div_four hc).const_mul
    (Real.exp (|z.re| ^ 2))) ((continuousOn_pcfIntegrand c z).aestronglyMeasurable
      measurableSet_Ioi) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
    norm_pcfIntegrand_le c z le_rfl ht

/-- Differentiation of the moments in `z`: `∂_z M_c(z) = -M_{c+1}(z)`. -/
theorem hasDerivAt_pcfMoment {c : ℂ} (hc : -1 < c.re) (z₀ : ℂ) :
    HasDerivAt (pcfMoment c) (-pcfMoment (c + 1) z₀) z₀ := by
  set R : ℝ := ‖z₀‖ + 1
  have hc1 : -1 < (c + 1).re := by simp; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun (z : ℂ) (t : ℝ) => (t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t))
    (F' := fun (z : ℂ) (t : ℝ) => -((t : ℂ) ^ (c + 1) * exp (-(t : ℂ) ^ 2 / 2 - z * t)))
    (x₀ := z₀) (bound := fun t => Real.exp (R ^ 2) * (t ^ (c + 1).re * Real.exp (-t ^ 2 / 4)))
    (s := Metric.ball z₀ 1) (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (continuousOn_pcfIntegrand c z).aestronglyMeasurable
      measurableSet_Ioi)
    (integrableOn_pcfIntegrand hc z₀)
    ((continuousOn_pcfIntegrand (c + 1) z₀).aestronglyMeasurable measurableSet_Ioi).neg
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht z hz => by
      rw [norm_neg]
      refine norm_pcfIntegrand_le (c + 1) z ?_ ht
      have h1 : ‖z‖ < ‖z₀‖ + 1 := by
        have := norm_sub_norm_le z z₀
        rw [Metric.mem_ball, dist_eq_norm] at hz
        linarith
      exact (Complex.abs_re_le_norm z).trans h1.le)
    ((integrableOn_rpow_mul_exp_neg_sq_div_four hc1).const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht z _ => by
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have h := (((hasDerivAt_id z).mul_const (t : ℂ)).const_sub
        (-(t : ℂ) ^ 2 / 2)).cexp.const_mul ((t : ℂ) ^ c)
      refine h.congr_deriv ?_
      rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]
      simp only [id]
      ring)
  have hfun : (fun z => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)) =
      pcfMoment c := rfl
  rw [hfun, integral_neg] at key
  exact key.2

/-- Integration by parts: `M_{c+2}(z) + z M_{c+1}(z) = (c + 1) M_c(z)`. -/
theorem pcfMoment_ibp {c : ℂ} (hc : -1 < c.re) (z : ℂ) :
    pcfMoment (c + 2) z + z * pcfMoment (c + 1) z = (c + 1) * pcfMoment c z := by
  have hc1 : -1 < (c + 1).re := by simp; linarith
  have hc2 : -1 < (c + 2).re := by simp; linarith
  have hc0 : c + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  set E : ℝ → ℂ := fun t => exp (-(t : ℂ) ^ 2 / 2 - z * t) with hE
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (c + 1) * E t with hg
  set g' : ℝ → ℂ := fun t => (c + 1) * ((t : ℂ) ^ c * E t) -
    ((t : ℂ) ^ (c + 2) * E t) - z * ((t : ℂ) ^ (c + 1) * E t) with hg'
  have hEd (t : ℝ) : HasDerivAt E (E t * (-(t : ℂ) - z)) t := by
    have hi : HasDerivAt (fun w : ℂ => -w ^ 2 / 2 - z * w) (-(t : ℂ) - z) (t : ℂ) := by
      convert (((hasDerivAt_pow 2 (t : ℂ)).div_const 2).neg.sub
        ((hasDerivAt_id (t : ℂ)).const_mul z)) using 1
      · funext w; simp only [Pi.sub_apply, Pi.neg_apply, id]; ring
      · ring
    exact hi.cexp.comp_ofReal
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt g (g' t) t := fun t ht => by
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp := hasDerivAt_ofReal_cpow_const (ne_of_gt ht) hc0
    have h1 : (t : ℂ) ^ (c + 1) = (t : ℂ) ^ c * t := by
      rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]
    have h2 : (t : ℂ) ^ (c + 2) = (t : ℂ) ^ c * t ^ 2 := by
      rw [Complex.cpow_add _ _ ht0, Complex.cpow_two]
    refine (hp.mul (hEd t)).congr_deriv ?_
    simp only [hg']
    rw [show c + 1 - 1 = c by ring, h1, h2]
    ring
  have hcont : ContinuousWithinAt g (Ici 0) 0 := by
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ (by fun_prop))
    exact Complex.continuousAt_ofReal_cpow_const 0 (c + 1) (Or.inl (by simp; linarith))
  have hint : IntegrableOn g' (Ioi 0) :=
    (((integrableOn_pcfIntegrand hc z).const_mul (c + 1)).sub
      (integrableOn_pcfIntegrand hc2 z)).sub ((integrableOn_pcfIntegrand hc1 z).const_mul z)
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => Real.exp (|z.re| ^ 2) *
        (t ^ (c + 1).re * Real.exp (-(1 / 4) * t))) atTop (𝓝 0) := by
      have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (c + 1).re (1 / 4)
        (by norm_num)).const_mul (Real.exp (|z.re| ^ 2))
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : 0 < t := by linarith
    refine (norm_pcfIntegrand_le (c + 1) z le_rfl ht0).trans ?_
    gcongr
    nlinarith
  have hibp := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hg0 : g 0 = 0 := by
    simp only [hg, Complex.ofReal_zero]
    rw [Complex.zero_cpow hc0, zero_mul]
  rw [hg0, sub_zero] at hibp
  have hsplit : ∫ t in Ioi (0 : ℝ), g' t =
      (c + 1) * pcfMoment c z - pcfMoment (c + 2) z - z * pcfMoment (c + 1) z := by
    have i0 := (integrableOn_pcfIntegrand hc z).const_mul (c + 1)
    have i1 := integrableOn_pcfIntegrand hc2 z
    have i2 := (integrableOn_pcfIntegrand hc1 z).const_mul z
    have e1 := integral_sub i0 i1
    have e2 := integral_sub (i0.sub i1) i2
    simp only [Pi.sub_apply] at e1 e2
    simp only [pcfMoment]
    rw [← integral_const_mul, ← integral_const_mul, ← e1, ← e2]
  rw [hsplit] at hibp
  linear_combination -hibp

/-- `M_c(0) = 2^{(c-1)/2} Γ((c+1)/2)`, in the form `(1/2) Γ((c+1)/2) 2^{(c+1)/2}`. -/
theorem pcfMoment_zero {c : ℂ} (hc : -1 < c.re) :
    pcfMoment c 0 = 1 / 2 * Gamma ((c + 1) / 2) * (2 : ℂ) ^ ((c + 1) / 2) := by
  have h := DLMF.Gamma.Gamma_laplace_power (μ := 2) (ν := c + 1) (z := 1 / 2) (by norm_num)
    (by norm_num) (by simp; linarith) (by norm_num)
  have hinv : (1 / 2 : ℂ) ^ (-((c + 1) / 2)) = (2 : ℂ) ^ ((c + 1) / 2) := by
    rw [one_div, Complex.inv_cpow _ _ (by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_ne_zero.symm), Complex.cpow_neg,
      inv_inv]
  rw [hinv, show c + 1 - 1 = c by ring] at h
  rw [h, pcfMoment]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.cpow_two, zero_mul, sub_zero]
  ring_nf

/-- **Laplace-type integral for `U(a,z)`** (DLMF 12.5.1): for `re a > -1/2` and all `z`,
`U(a,z) = e^{-z²/4}/Γ(1/2 + a) ∫₀^∞ t^{a-1/2} e^{-t²/2 - z t} dt`. -/
@[dlmf 12.5.E1]
theorem pcfU_eq_integral {a : ℂ} (ha : -1 / 2 < a.re) (z : ℂ) :
    pcfU a z = exp (-z ^ 2 / 4) / Gamma (1 / 2 + a) *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1 / 2) * exp (-(t : ℂ) ^ 2 / 2 - z * t) := by
  have h0 : -1 < (a - 1 / 2).re := by simp; linarith
  have h1 : -1 < (a - 1 / 2 + 1).re := by simp; linarith
  have h2 : -1 < (a - 1 / 2 + 1 + 1).re := by simp; linarith
  set G := (Gamma (1 / 2 + a))⁻¹ with hG
  have hs : IsWeberSol a (fun w => G * (exp (-w ^ 2 / 4) * pcfMoment (a - 1 / 2) w))
      (fun w => G * (exp (-w ^ 2 / 4) *
        (-pcfMoment (a - 1 / 2 + 1) w - w / 2 * pcfMoment (a - 1 / 2) w))) := fun w => by
    have hM0 := hasDerivAt_pcfMoment h0 w
    have hM1 := hasDerivAt_pcfMoment h1 w
    have he := hasDerivAt_exp_neg_sq_div_four w
    have hibp := pcfMoment_ibp h0 w
    rw [show a - 1 / 2 + 2 = a - 1 / 2 + 1 + 1 by ring] at hibp
    refine ⟨((he.mul hM0).const_mul G).congr_deriv (by ring), ?_⟩
    refine ((he.mul ((hM1.neg).sub (((hasDerivAt_id w).div_const 2).mul hM0))).const_mul G)
      |>.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
    · simp only [id, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply]
      linear_combination G * exp (-w ^ 2 / 4) * hibp
    · exact Eventually.of_forall fun v => by simp [Pi.sub_apply, Pi.neg_apply, Pi.mul_apply]
  have hd := Complex.Gamma_mul_Gamma_add_half (a / 2 + 1 / 4)
  rw [show a / 2 + 1 / 4 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 2 * (a / 2 + 1 / 4) = 1 / 2 + a by ring,
    show 1 - (1 / 2 + a) = 1 / 2 - a by ring] at hd
  have hGa : Gamma (1 / 2 + a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG1 : Gamma (a / 2 + 1 / 4) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG3 : Gamma (3 / 4 + a / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hpow (x y : ℂ) (hxy : 1 / 2 - a + x = 1 + y) :
      (2 : ℂ) ^ (1 / 2 - a) * 2 ^ x = 2 * 2 ^ y := by
    rw [← Complex.cpow_add _ _ two_ne_zero, hxy, Complex.cpow_add _ _ two_ne_zero,
      Complex.cpow_one]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hinit0 : G * (exp (-(0 : ℂ) ^ 2 / 4) * pcfMoment (a - 1 / 2) 0) = pcfU a 0 := by
    have hp := hpow (a / 2 + 1 / 4) (-(a / 2 + 1 / 4)) (by ring)
    rw [pcfMoment_zero h0, pcfU_zero', hG, show (a - 1 / 2 + 1) / 2 = a / 2 + 1 / 4 by ring]
    simp only [zero_pow two_ne_zero, neg_zero, zero_div, Complex.exp_zero, one_mul]
    generalize Gamma (1 / 2 + a) = A at hGa hd ⊢
    generalize Gamma (a / 2 + 1 / 4) = B at hG1 hd ⊢
    generalize Gamma (3 / 4 + a / 2) = C at hG3 hd ⊢
    generalize (2 : ℂ) ^ (a / 2 + 1 / 4) = P at hp ⊢
    generalize (2 : ℂ) ^ (-(a / 2 + 1 / 4)) = Q at hp ⊢
    generalize (2 : ℂ) ^ (1 / 2 - a) = T at hd hp
    field_simp
    linear_combination P * hd + A * (Real.sqrt π : ℂ) * hp
  have hinit1 : G * (exp (-(0 : ℂ) ^ 2 / 4) *
      (-pcfMoment (a - 1 / 2 + 1) 0 - 0 / 2 * pcfMoment (a - 1 / 2) 0)) = pcfUDeriv a 0 := by
    have hp := hpow (a / 2 + 3 / 4) (-(a / 2 - 1 / 4)) (by ring)
    rw [pcfMoment_zero h1, pcfUDeriv_zero', hG,
      show (a - 1 / 2 + 1 + 1) / 2 = 3 / 4 + a / 2 by ring,
      show (3 / 4 + a / 2 : ℂ) = a / 2 + 3 / 4 by ring]
    rw [show (1 / 4 + a / 2 : ℂ) = a / 2 + 1 / 4 by ring]
    simp only [zero_pow two_ne_zero, neg_zero, zero_div, Complex.exp_zero, one_mul, zero_mul,
      sub_zero]
    rw [show a / 2 + 3 / 4 = 3 / 4 + a / 2 by ring] at hp ⊢
    generalize Gamma (1 / 2 + a) = A at hGa hd ⊢
    generalize Gamma (a / 2 + 1 / 4) = B at hG1 hd ⊢
    generalize Gamma (3 / 4 + a / 2) = C at hG3 hd ⊢
    generalize (2 : ℂ) ^ (3 / 4 + a / 2) = P at hp ⊢
    generalize (2 : ℂ) ^ (-(a / 2 - 1 / 4)) = Q at hp ⊢
    generalize (2 : ℂ) ^ (1 / 2 - a) = T at hd hp
    field_simp
    linear_combination -P * hd - A * (Real.sqrt π : ℂ) * hp
  have := hs.eq_of_initial (isWeberSol_pcfU a) hinit0 hinit1 z
  rw [← this, pcfMoment, hG]
  ring

/-! ### Wronskians (DLMF 12.2) -/

/-- The derivative of `w ↦ U(a,-w)` is `-U'(a,-z)`. -/
theorem hasDerivAt_pcfU_neg (a z : ℂ) :
    HasDerivAt (fun w => pcfU a (-w)) (-pcfUDeriv a (-z)) z := by
  have h := (hasDerivAt_pcfU a (-z)).comp z (hasDerivAt_neg z)
  exact h.congr_deriv (by ring)

/-- The derivative of `w ↦ U(b, iw)` is `i U'(b, iz)`. -/
theorem hasDerivAt_pcfU_mul_I (b z : ℂ) :
    HasDerivAt (fun w => pcfU b (I * w)) (I * pcfUDeriv b (I * z)) z := by
  have h := (hasDerivAt_pcfU b (I * z)).comp z ((hasDerivAt_id z).const_mul I)
  exact h.congr_deriv (by ring)

/-- The derivative of `w ↦ U(b, -iw)` is `-i U'(b, -iz)`. -/
theorem hasDerivAt_pcfU_mul_neg_I (b z : ℂ) :
    HasDerivAt (fun w => pcfU b (-I * w)) (-I * pcfUDeriv b (-I * z)) z := by
  have h := (hasDerivAt_pcfU b (-I * z)).comp z ((hasDerivAt_id z).const_mul (-I))
  exact h.congr_deriv (by ring)

/-- `U(a,-z)` solves Weber's equation `w'' = (z²/4 + a) w`. -/
theorem isWeberSol_pcfU_neg (a : ℂ) :
    IsWeberSol a (fun w => pcfU a (-w)) (fun w => -pcfUDeriv a (-w)) := fun z => by
  refine ⟨hasDerivAt_pcfU_neg a z, ?_⟩
  have h := ((hasDerivAt_pcfUDeriv a (-z)).comp z (hasDerivAt_neg z)).neg
  exact h.congr_deriv (by ring)

/-- `U(-a, iz)` solves Weber's equation `w'' = (z²/4 + a) w`. -/
theorem isWeberSol_pcfU_mul_I (a : ℂ) :
    IsWeberSol a (fun w => pcfU (-a) (I * w)) (fun w => I * pcfUDeriv (-a) (I * w)) :=
  fun z => by
  refine ⟨hasDerivAt_pcfU_mul_I (-a) z, ?_⟩
  have h := ((hasDerivAt_pcfUDeriv (-a) (I * z)).comp z
    ((hasDerivAt_id z).const_mul I)).const_mul I
  have hI4 : I ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  refine h.congr_deriv ?_
  ring_nf
  simp only [hI4, Complex.I_sq]
  ring

/-- `U(-a, -iz)` solves Weber's equation `w'' = (z²/4 + a) w`. -/
theorem isWeberSol_pcfU_mul_neg_I (a : ℂ) :
    IsWeberSol a (fun w => pcfU (-a) (-I * w)) (fun w => -I * pcfUDeriv (-a) (-I * w)) :=
  fun z => by
  refine ⟨hasDerivAt_pcfU_mul_neg_I (-a) z, ?_⟩
  have h := ((hasDerivAt_pcfUDeriv (-a) (-I * z)).comp z
    ((hasDerivAt_id z).const_mul (-I))).const_mul (-I)
  have hI4 : I ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  refine h.congr_deriv ?_
  ring_nf
  simp only [hI4, Complex.I_sq]
  ring

/-- **Wronskian** (DLMF 12.2.11): `𝒲{U(a,z), U(a,-z)} = √(2π)/Γ(1/2 + a)`. -/
@[dlmf 12.2.E11]
theorem pcfU_wronskian_neg (a z : ℂ) :
    pcfU a z * deriv (fun w => pcfU a (-w)) z - deriv (pcfU a) z * pcfU a (-z) =
      (Real.sqrt (2 * π) : ℂ) / Gamma (1 / 2 + a) := by
  rw [(hasDerivAt_pcfU_neg a z).deriv, deriv_pcfU]
  have hW := (isWeberSol_pcfU a).wronskian_eq (isWeberSol_pcfU_neg a) z
  simp only [neg_zero] at hW
  rw [hW, pcfU_zero', pcfUDeriv_zero']
  have hd := Complex.Gamma_mul_Gamma_add_half (1 / 4 + a / 2)
  rw [show 1 / 4 + a / 2 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 2 * (1 / 4 + a / 2) = 1 / 2 + a by ring,
    show 1 - (1 / 2 + a) = 1 / 2 - a by ring] at hd
  have hinv : (Gamma (3 / 4 + a / 2))⁻¹ * (Gamma (1 / 4 + a / 2))⁻¹ =
      (Gamma (1 / 2 + a))⁻¹ * ((2 : ℂ) ^ (1 / 2 - a))⁻¹ * (Real.sqrt π : ℂ)⁻¹ := by
    rw [← mul_inv, mul_comm, hd, mul_inv, mul_inv]
  have hP : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(a / 2 - 1 / 4)) * (Real.sqrt 2 : ℂ) =
      2 ^ (1 / 2 - a) := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero,
      ← Complex.cpow_add _ _ two_ne_zero]
    ring_nf
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 / 2 - a) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have h2π : (Real.sqrt (2 * π) : ℂ) = (Real.sqrt 2 : ℂ) * (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_mul (by norm_num), Complex.ofReal_mul]
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have h22 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have e : (Real.sqrt π : ℂ) * 2 ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ *
        -(-((Real.sqrt π : ℂ) * 2 ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹)) -
      -((Real.sqrt π : ℂ) * 2 ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹) *
        ((Real.sqrt π : ℂ) * 2 ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹) =
      2 * ((Real.sqrt π : ℂ) * (Real.sqrt π : ℂ)) *
        ((2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(a / 2 - 1 / 4))) *
        ((Gamma (3 / 4 + a / 2))⁻¹ * (Gamma (1 / 4 + a / 2))⁻¹) := by ring
  rw [e, hinv, h2π, div_eq_mul_inv ((Real.sqrt 2 : ℂ) * (Real.sqrt π : ℂ))]
  generalize (Gamma (1 / 2 + a))⁻¹ = A
  generalize hQ : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(a / 2 - 1 / 4)) = Q at hP
  generalize (2 : ℂ) ^ (1 / 2 - a) = T at hP hT
  rw [← hP]
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h; rw [h, zero_mul] at h22; norm_num at h22
  have hQ0 : Q ≠ 0 := by rintro rfl; rw [zero_mul] at hP; exact hT hP.symm
  field_simp
  linear_combination (-A) * h22

/-- Euler's reflection formula for reciprocals, valid for every complex `s`. -/
theorem pi_mul_recip_Gamma_mul_recip_Gamma (s : ℂ) :
    (π : ℂ) * ((Gamma s)⁻¹ * (Gamma (1 - s))⁻¹) = Complex.sin (π * s) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_inv, Complex.Gamma_mul_Gamma_one_sub, inv_div]
  field_simp

/-- **Wronskians** (DLMF 12.2.12, upper signs):
`𝒲{U(a,z), U(-a,iz)} = -i e^{iπ(a/2 + 1/4)}`, as printed in the DLMF. -/
@[dlmf 12.2.E12]
theorem pcfU_wronskian_mul_I (a z : ℂ) :
    pcfU a z * deriv (fun w => pcfU (-a) (I * w)) z - deriv (pcfU a) z * pcfU (-a) (I * z) =
      -I * exp (I * π * (a / 2 + 1 / 4)) := by
  rw [(hasDerivAt_pcfU_mul_I (-a) z).deriv, deriv_pcfU]
  have hW := (isWeberSol_pcfU a).wronskian_eq (isWeberSol_pcfU_mul_I a) z
  simp only [mul_zero] at hW
  rw [hW, pcfU_zero' a, pcfUDeriv_zero' (-a), pcfUDeriv_zero' a, pcfU_zero' (-a),
    show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring,
    show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring,
    show (π : ℂ) * (1 / 4 + a / 2) = π * (a / 2 + 1 / 4) by ring] at q2
  have hc : Complex.sin (π * (1 / 4 - a / 2)) = Complex.cos (π * (a / 2 + 1 / 4)) := by
    rw [← Complex.sin_pi_div_two_sub]; ring_nf
  have hexp : exp (I * π * (a / 2 + 1 / 4)) =
      Complex.cos (π * (a / 2 + 1 / 4)) + Complex.sin (π * (a / 2 + 1 / 4)) * I := by
    rw [← Complex.exp_mul_I]; ring_nf
  have p1 : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 + 1 / 4) + -(-a / 2 - 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have p2 : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 - 1 / 4) + -(-a / 2 + 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hexp]
  set X1 := (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4))
  set X2 := (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4))
  set Y1 := (Gamma (1 / 4 - a / 2))⁻¹ * (Gamma (3 / 4 + a / 2))⁻¹
  set Y2 := (Gamma (1 / 4 + a / 2))⁻¹ * (Gamma (3 / 4 - a / 2))⁻¹
  linear_combination (-I * X1 * Y1 + X2 * Y2) * hππ - I * π * Y1 * p1 - I * q1 - I * hc +
    π * Y2 * p2 + q2 + Complex.sin (π * (a / 2 + 1 / 4)) * Complex.I_sq

/-- **Wronskians** (DLMF 12.2.12, lower signs):
`𝒲{U(a,z), U(-a,-iz)} = i e^{-iπ(a/2 + 1/4)}`. -/
@[dlmf 12.2.E12]
theorem pcfU_wronskian_mul_neg_I (a z : ℂ) :
    pcfU a z * deriv (fun w => pcfU (-a) (-I * w)) z - deriv (pcfU a) z * pcfU (-a) (-I * z) =
      I * exp (-I * π * (a / 2 + 1 / 4)) := by
  rw [(hasDerivAt_pcfU_mul_neg_I (-a) z).deriv, deriv_pcfU]
  have hW := (isWeberSol_pcfU a).wronskian_eq (isWeberSol_pcfU_mul_neg_I a) z
  simp only [mul_zero] at hW
  rw [hW, pcfU_zero' a, pcfUDeriv_zero' (-a), pcfUDeriv_zero' a, pcfU_zero' (-a),
    show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring,
    show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring,
    show (π : ℂ) * (1 / 4 + a / 2) = π * (a / 2 + 1 / 4) by ring] at q2
  have hc : Complex.sin (π * (1 / 4 - a / 2)) = Complex.cos (π * (a / 2 + 1 / 4)) := by
    rw [← Complex.sin_pi_div_two_sub]; ring_nf
  have hexp : exp (-I * π * (a / 2 + 1 / 4)) =
      Complex.cos (π * (a / 2 + 1 / 4)) - Complex.sin (π * (a / 2 + 1 / 4)) * I := by
    rw [show -I * π * (a / 2 + 1 / 4) = (-(π * (a / 2 + 1 / 4))) * I by ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have p1 : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 + 1 / 4) + -(-a / 2 - 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have p2 : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 - 1 / 4) + -(-a / 2 + 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hexp]
  set X1 := (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4))
  set X2 := (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4))
  set Y1 := (Gamma (1 / 4 - a / 2))⁻¹ * (Gamma (3 / 4 + a / 2))⁻¹
  set Y2 := (Gamma (1 / 4 + a / 2))⁻¹ * (Gamma (3 / 4 - a / 2))⁻¹
  linear_combination (I * X1 * Y1 + X2 * Y2) * hππ + I * π * Y1 * p1 + I * q1 + I * hc +
    π * Y2 * p2 + q2 + Complex.sin (π * (a / 2 + 1 / 4)) * Complex.I_sq

/-! ### Connection formula 12.2.17 -/

/-- Linear combinations of solutions of Weber's equation are solutions. -/
theorem IsWeberSol.lincomb {a : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsWeberSol a f f')
    (hg : IsWeberSol a g g') (c₁ c₂ : ℂ) :
    IsWeberSol a (fun w => c₁ * f w + c₂ * g w) (fun w => c₁ * f' w + c₂ * g' w) := fun z =>
  ⟨((hf z).1.const_mul c₁).add ((hg z).1.const_mul c₂),
    (((hf z).2.const_mul c₁).add ((hg z).2.const_mul c₂)).congr_deriv (by ring)⟩

/-- **Connection formula** (DLMF 12.2.17, upper signs):
`√(2π) U(-a, iz) = Γ(1/2 + a) (e^{-iπ(a/2 - 1/4)} U(a,z) + e^{iπ(a/2 - 1/4)} U(a,-z))`.
At the poles of `Γ(1/2 + a)` the bracket vanishes and the right side is a limit `∞ · 0`,
so those parameters are excluded. -/
@[dlmf 12.2.E17]
theorem pcfU_connection_mul_I {a : ℂ} (ha : ∀ n : ℕ, 1 / 2 + a ≠ -n) (z : ℂ) :
    (Real.sqrt (2 * π) : ℂ) * pcfU (-a) (I * z) = Gamma (1 / 2 + a) *
      (exp (-I * π * (a / 2 - 1 / 4)) * pcfU a z +
        exp (I * π * (a / 2 - 1 / 4)) * pcfU a (-z)) := by
  set A := Gamma (1 / 2 + a) with hA
  set e₁ := exp (-I * π * (a / 2 - 1 / 4)) with he₁d
  set e₂ := exp (I * π * (a / 2 - 1 / 4)) with he₂d
  have hf := (isWeberSol_pcfU_mul_I a).lincomb (isWeberSol_pcfU_mul_I a)
    (Real.sqrt (2 * π) : ℂ) 0
  have hg := ((isWeberSol_pcfU a).lincomb (isWeberSol_pcfU_neg a) (A * e₁) (A * e₂))
  have hd := Complex.Gamma_mul_Gamma_add_half (1 / 4 + a / 2)
  rw [show 1 / 4 + a / 2 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 2 * (1 / 4 + a / 2) = 1 / 2 + a by ring,
    show 1 - (1 / 2 + a) = 1 / 2 - a by ring, ← hA] at hd
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 / 2 - a) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hA0 : A ≠ 0 := Complex.Gamma_ne_zero ha
  have hprod : Gamma (1 / 4 + a / 2) * Gamma (3 / 4 + a / 2) ≠ 0 := by
    rw [hd]; exact mul_ne_zero (mul_ne_zero hA0 hT) hπ
  have hΓ1 : Gamma (1 / 4 + a / 2) ≠ 0 := left_ne_zero_of_mul hprod
  have hΓ3 : Gamma (3 / 4 + a / 2) ≠ 0 := right_ne_zero_of_mul hprod
  have hAe : A = Gamma (1 / 4 + a / 2) * Gamma (3 / 4 + a / 2) /
      ((2 : ℂ) ^ (1 / 2 - a) * (Real.sqrt π : ℂ)) := by
    rw [hd]; field_simp
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have hcos : Complex.cos (π * (a / 2 - 1 / 4)) = Complex.sin (π * (1 / 4 + a / 2)) := by
    rw [← Complex.sin_add_pi_div_two]; ring_nf
  have hsin : Complex.sin (π * (a / 2 - 1 / 4)) = -Complex.sin (π * (1 / 4 - a / 2)) := by
    rw [← Complex.sin_neg]; ring_nf
  have he₁ : e₁ = Complex.cos (π * (a / 2 - 1 / 4)) - Complex.sin (π * (a / 2 - 1 / 4)) * I := by
    rw [he₁d, show -I * π * (a / 2 - 1 / 4) = (-(π * (a / 2 - 1 / 4))) * I by ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have he₂ : e₂ = Complex.cos (π * (a / 2 - 1 / 4)) + Complex.sin (π * (a / 2 - 1 / 4)) * I := by
    rw [he₂d, show I * π * (a / 2 - 1 / 4) = (π * (a / 2 - 1 / 4)) * I by ring,
      Complex.exp_mul_I]
  rw [hcos, ← q2] at he₁ he₂
  rw [hsin, ← q1] at he₁ he₂
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have h2π : (Real.sqrt (2 * π) : ℂ) = (Real.sqrt 2 : ℂ) * (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_mul (by norm_num), Complex.ofReal_mul]
  have hpow (x y : ℂ) (hxy : 1 / 2 + x + (1 / 2 - a) = 1 + y) :
      (Real.sqrt 2 : ℂ) * 2 ^ x * 2 ^ (1 / 2 - a) = 2 * 2 ^ y := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero, ← Complex.cpow_add _ _ two_ne_zero,
      hxy, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
  have key := hf.eq_of_initial hg ?_ ?_ z
  · simp only [zero_mul, add_zero] at key
    rw [key]; ring
  · simp only [mul_zero, neg_zero, zero_mul, add_zero]
    rw [pcfU_zero' (-a), pcfU_zero' a, he₁, he₂, hAe, h2π,
      show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
    have r := hpow (-(-a / 2 + 1 / 4)) (-(a / 2 + 1 / 4)) (by ring)
    generalize (Gamma (3 / 4 - a / 2))⁻¹ = m3
    generalize (Gamma (1 / 4 - a / 2))⁻¹ = m1
    generalize (2 : ℂ) ^ (1 / 2 - a) = T at hT r
    generalize Gamma (1 / 4 + a / 2) = B at hΓ1
    generalize Gamma (3 / 4 + a / 2) = C at hΓ3
    generalize (2 : ℂ) ^ (-(a / 2 + 1 / 4)) = P at r
    generalize (2 : ℂ) ^ (-(-a / 2 + 1 / 4)) = P' at r
    field_simp
    have hππ2 : (Real.sqrt π : ℂ) ^ 2 = π := by rw [sq, hππ]
    linear_combination ((Real.sqrt π : ℂ) ^ 2 * m3 * C) * r + (2 * P * m3 * C) * hππ2
  · simp only [mul_zero, neg_zero, zero_mul, add_zero]
    rw [pcfUDeriv_zero' (-a), pcfUDeriv_zero' a, he₁, he₂, hAe, h2π,
      show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring]
    have r := hpow (-(-a / 2 - 1 / 4)) (-(a / 2 - 1 / 4)) (by ring)
    generalize (Gamma (3 / 4 - a / 2))⁻¹ = m3
    generalize (Gamma (1 / 4 - a / 2))⁻¹ = m1
    generalize (2 : ℂ) ^ (1 / 2 - a) = T at hT r
    generalize Gamma (1 / 4 + a / 2) = B at hΓ1
    generalize Gamma (3 / 4 + a / 2) = C at hΓ3
    generalize (2 : ℂ) ^ (-(a / 2 - 1 / 4)) = P at r
    generalize (2 : ℂ) ^ (-(-a / 2 - 1 / 4)) = P' at r
    field_simp
    have hππ2 : (Real.sqrt π : ℂ) ^ 2 = π := by rw [sq, hππ]
    linear_combination (-(Real.sqrt π : ℂ) ^ 2 * I * m1 * B) * r + (-2 * I * P * m1 * B) * hππ2

/-- **Connection formula** (DLMF 12.2.17, lower signs):
`√(2π) U(-a, -iz) = Γ(1/2 + a) (e^{-iπ(a/2 - 1/4)} U(a,-z) + e^{iπ(a/2 - 1/4)} U(a,z))`. -/
@[dlmf 12.2.E17]
theorem pcfU_connection_mul_neg_I {a : ℂ} (ha : ∀ n : ℕ, 1 / 2 + a ≠ -n) (z : ℂ) :
    (Real.sqrt (2 * π) : ℂ) * pcfU (-a) (-I * z) = Gamma (1 / 2 + a) *
      (exp (-I * π * (a / 2 - 1 / 4)) * pcfU a (-z) +
        exp (I * π * (a / 2 - 1 / 4)) * pcfU a z) := by
  have h := pcfU_connection_mul_I ha (-z)
  rwa [neg_neg, show I * -z = -I * z by ring] at h

/-! ### The second solution `V(a,z)` (DLMF 12.2, 12.4.2, 12.8) -/

/-- `V(a,0)` (DLMF 12.2.8), with reciprocal Gamma factors, so that it is entire in `a`. -/
def pcfVZero (a : ℂ) : ℂ :=
  π * (2 : ℂ) ^ (a / 2 + 1 / 4) * (Gamma (3 / 4 - a / 2))⁻¹ ^ 2 * (Gamma (1 / 4 + a / 2))⁻¹

/-- `V'(a,0)` (DLMF 12.2.9), with reciprocal Gamma factors. -/
def pcfVDerivZero (a : ℂ) : ℂ :=
  π * (2 : ℂ) ^ (a / 2 + 3 / 4) * (Gamma (1 / 4 - a / 2))⁻¹ ^ 2 * (Gamma (3 / 4 + a / 2))⁻¹

/-- **Weber's second function** `V(a,z) = V(a,0) u₁(a,z) + V'(a,0) u₂(a,z)` (DLMF 12.4.2). It is
entire in `a` and `z`; see `pcfV_eq` for the classical form in terms of `U(a, ±z)`. -/
@[dlmf 12.4.E2]
def pcfV (a z : ℂ) : ℂ := pcfVZero a * pcfEven a z + pcfVDerivZero a * pcfOdd a z

/-- The derivative `V'(a,z)`. -/
def pcfVDeriv (a z : ℂ) : ℂ := pcfVZero a * pcfEvenDeriv a z + pcfVDerivZero a * pcfOddDeriv a z

/-- `V(a,·)` has derivative `pcfVDeriv a`. -/
theorem hasDerivAt_pcfV (a z : ℂ) : HasDerivAt (pcfV a) (pcfVDeriv a z) z :=
  ((hasDerivAt_pcfEven a z).const_mul _).add ((hasDerivAt_pcfOdd a z).const_mul _)

/-- Weber's equation (DLMF 12.2.2) for `V`. -/
@[dlmf 12.2.E2]
theorem hasDerivAt_pcfVDeriv (a z : ℂ) :
    HasDerivAt (pcfVDeriv a) ((z ^ 2 / 4 + a) * pcfV a z) z := by
  refine (((hasDerivAt_pcfEvenDeriv a z).const_mul _).add
    ((hasDerivAt_pcfOddDeriv a z).const_mul _)).congr_deriv ?_
  rw [pcfV]
  ring

/-- `V(a,z)` solves Weber's equation, with derivative `pcfVDeriv a`. -/
theorem isWeberSol_pcfV (a : ℂ) : IsWeberSol a (pcfV a) (pcfVDeriv a) :=
  fun z => ⟨hasDerivAt_pcfV a z, hasDerivAt_pcfVDeriv a z⟩

/-- `deriv (V(a,·)) = pcfVDeriv a`. -/
theorem deriv_pcfV (a : ℂ) : deriv (pcfV a) = pcfVDeriv a :=
  funext fun z => (hasDerivAt_pcfV a z).deriv

/-- The value `V(a,0)` is `pcfVZero a` (DLMF 12.2.8). -/
theorem pcfV_zero' (a : ℂ) : pcfV a 0 = pcfVZero a := by
  simp [pcfV, pcfEven_zero, pcfOdd_zero]

/-- The value `V'(a,0)` is `pcfVDerivZero a` (DLMF 12.2.9). -/
theorem pcfVDeriv_zero' (a : ℂ) : pcfVDeriv a 0 = pcfVDerivZero a := by
  simp [pcfVDeriv, pcfEvenDeriv_zero, pcfOddDeriv_zero]

/-- `V(a,0)` (DLMF 12.2.8). -/
@[dlmf 12.2.E8]
theorem pcfV_zero (a : ℂ) :
    pcfV a 0 = π * (2 : ℂ) ^ (a / 2 + 1 / 4) /
      (Gamma (3 / 4 - a / 2) ^ 2 * Gamma (1 / 4 + a / 2)) := by
  rw [pcfV_zero', pcfVZero]
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

/-- `V'(a,0)` (DLMF 12.2.9). -/
@[dlmf 12.2.E9]
theorem pcfVDeriv_zero (a : ℂ) :
    pcfVDeriv a 0 = π * (2 : ℂ) ^ (a / 2 + 3 / 4) /
      (Gamma (1 / 4 - a / 2) ^ 2 * Gamma (3 / 4 + a / 2)) := by
  rw [pcfVDeriv_zero', pcfVDerivZero]
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

/-- The derivative of `w ↦ V(a,-w)` is `-V'(a,-z)`. -/
theorem hasDerivAt_pcfV_neg (a z : ℂ) :
    HasDerivAt (fun w => pcfV a (-w)) (-pcfVDeriv a (-z)) z := by
  have h := (hasDerivAt_pcfV a (-z)).comp z (hasDerivAt_neg z)
  exact h.congr_deriv (by ring)

/-- `V(a,-z)` solves Weber's equation. -/
theorem isWeberSol_pcfV_neg (a : ℂ) :
    IsWeberSol a (fun w => pcfV a (-w)) (fun w => -pcfVDeriv a (-w)) := fun z => by
  refine ⟨hasDerivAt_pcfV_neg a z, ?_⟩
  have h := ((hasDerivAt_pcfVDeriv a (-z)).comp z (hasDerivAt_neg z)).neg
  exact h.congr_deriv (by ring)

/-- Legendre duplication for reciprocals, valid for every `a`:
`1/Γ(1/2 + a) = 2^{1/2-a} √π / (Γ(1/4 + a/2) Γ(3/4 + a/2))`. -/
theorem recip_Gamma_half_add (a : ℂ) :
    (Gamma (1 / 2 + a))⁻¹ = (Gamma (1 / 4 + a / 2))⁻¹ * (Gamma (3 / 4 + a / 2))⁻¹ *
      (2 : ℂ) ^ (1 / 2 - a) * (Real.sqrt π : ℂ) := by
  have hd := Complex.Gamma_mul_Gamma_add_half (1 / 4 + a / 2)
  rw [show 1 / 4 + a / 2 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 2 * (1 / 4 + a / 2) = 1 / 2 + a by ring,
    show 1 - (1 / 2 + a) = 1 / 2 - a by ring] at hd
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 / 2 - a) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  rw [← mul_inv, hd, mul_inv, mul_inv]
  field_simp

/-- `sin(π(1/4 - a/2)) = cos(π(1/4 + a/2))`. -/
theorem sin_pi_quarter_sub (a : ℂ) :
    Complex.sin (π * (1 / 4 - a / 2)) = Complex.cos (π * (1 / 4 + a / 2)) := by
  rw [← Complex.sin_pi_div_two_sub]; ring_nf

/-- `sin(πa) = sin²(π(1/4 + a/2)) - cos²(π(1/4 + a/2))`. -/
theorem sin_pi_mul_eq_sq (a : ℂ) :
    Complex.sin (π * a) =
      Complex.sin (π * (1 / 4 + a / 2)) ^ 2 - Complex.cos (π * (1 / 4 + a / 2)) ^ 2 := by
  rw [show (π : ℂ) * a = 2 * (π * (1 / 4 + a / 2)) - π / 2 by ring,
    Complex.sin_sub_pi_div_two, Complex.cos_two_mul]
  linear_combination (-1 : ℂ) * Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))

/-- `cos(πa) = 2 sin(π(1/4 + a/2)) cos(π(1/4 + a/2))`. -/
theorem cos_pi_mul_eq_mul (a : ℂ) :
    Complex.cos (π * a) =
      2 * Complex.sin (π * (1 / 4 + a / 2)) * Complex.cos (π * (1 / 4 + a / 2)) := by
  rw [show (π : ℂ) * a = 2 * (π * (1 / 4 + a / 2)) - π / 2 by ring,
    Complex.cos_sub_pi_div_two, Complex.sin_two_mul]

/-- **Wronskian** (DLMF 12.2.10): `𝒲{U(a,z), V(a,z)} = √(2/π)`. -/
@[dlmf 12.2.E10]
theorem pcfV_wronskian (a z : ℂ) :
    pcfU a z * deriv (pcfV a) z - deriv (pcfU a) z * pcfV a z = (Real.sqrt (2 / π) : ℂ) := by
  rw [deriv_pcfV, deriv_pcfU]
  have hW := (isWeberSol_pcfU a).wronskian_eq (isWeberSol_pcfV a) z
  rw [hW, pcfU_zero', pcfUDeriv_zero', pcfV_zero', pcfVDeriv_zero', pcfVZero, pcfVDerivZero]
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
  have p1 : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (a / 2 + 3 / 4) = (Real.sqrt 2 : ℂ) := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero]; ring_nf
  have p2 : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (a / 2 + 1 / 4) = (Real.sqrt 2 : ℂ) := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero]; ring_nf
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hR : (Real.sqrt (2 / π) : ℂ) * (Real.sqrt π : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg (by norm_num) Real.pi_pos.le),
      div_mul_cancel₀ _ Real.pi_ne_zero]
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  refine mul_left_cancel₀ hπ0 ?_
  set g1m := (Gamma (1 / 4 - a / 2))⁻¹
  set g3m := (Gamma (3 / 4 - a / 2))⁻¹
  set g1p := (Gamma (1 / 4 + a / 2))⁻¹
  set g3p := (Gamma (3 / 4 + a / 2))⁻¹
  set c := Complex.cos (π * (1 / 4 + a / 2))
  set s := Complex.sin (π * (1 / 4 + a / 2))
  set r := (Real.sqrt π : ℂ)
  set R := (Real.sqrt (2 / π) : ℂ)
  set t := (Real.sqrt 2 : ℂ)
  linear_combination (π ^ 2 * r * g3p ^ 2 * g1m ^ 2) * p1 + (π ^ 2 * r * g1p ^ 2 * g3m ^ 2) * p2
    + (r * t * (π * (g1m * g3p) + c)) * q1 + (r * t * (π * (g1p * g3m) + s)) * q2
    + (r * t) * htr + R * hππ - r * hR

/-- Duplication formula: `1/Γ(1/2 - a) = 2^{1/2+a} √π / (Γ(1/4 - a/2) Γ(3/4 - a/2))`. -/
theorem recip_Gamma_half_sub (a : ℂ) :
    (Gamma (1 / 2 - a))⁻¹ = (Gamma (1 / 4 - a / 2))⁻¹ * (Gamma (3 / 4 - a / 2))⁻¹ *
      (2 : ℂ) ^ (1 / 2 + a) * (Real.sqrt π : ℂ) := by
  have h := recip_Gamma_half_add (-a)
  rwa [show (1 / 2 + -a : ℂ) = 1 / 2 - a by ring, show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring,
    show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring,
    show (1 / 2 - -a : ℂ) = 1 / 2 + a by ring] at h

/-- `2^x 2^y = 2^z` when `x + y = z`. -/
theorem two_cpow_mul_two_cpow (x y z : ℂ) (h : x + y = z) :
    (2 : ℂ) ^ x * 2 ^ y = 2 ^ z := by
  rw [← Complex.cpow_add _ _ two_ne_zero, h]

/-- **Connection formula** (DLMF 12.2.15), valid for every `a`:
`U(a,-z) = -sin(πa) U(a,z) + π/Γ(1/2 + a) V(a,z)`. -/
@[dlmf 12.2.E15]
theorem pcfU_neg_eq (a z : ℂ) :
    pcfU a (-z) = -Complex.sin (π * a) * pcfU a z + π / Gamma (1 / 2 + a) * pcfV a z := by
  have hg := (isWeberSol_pcfU a).lincomb (isWeberSol_pcfV a) (-Complex.sin (π * a))
    (π / Gamma (1 / 2 + a))
  refine (isWeberSol_pcfU_neg a).eq_of_initial hg ?_ ?_ z
  · simp only [neg_zero]
    rw [pcfU_zero', pcfV_zero', pcfVZero, div_eq_mul_inv (π : ℂ) (Gamma (1 / 2 + a)),
      recip_Gamma_half_add, sin_pi_mul_eq_sq]
    have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
    rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
    have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
    have pw : (2 : ℂ) ^ (1 / 2 - a) * 2 ^ (a / 2 + 1 / 4) = 2 * 2 ^ (-(a / 2 + 1 / 4)) := by
      rw [two_cpow_mul_two_cpow _ _ (-(a / 2 + 1 / 4) + 1) (by ring),
        Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]; ring
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 - a)
    linear_combination (-(r * g3p * T * B) * (π * (g1p * g3m) + s)) * q2 +
      (-(r * g3p * s ^ 2)) * pw + (-(r * A * g3p)) * htr
  · simp only [neg_zero]
    rw [pcfUDeriv_zero', pcfVDeriv_zero', pcfVDerivZero,
      div_eq_mul_inv (π : ℂ) (Gamma (1 / 2 + a)), recip_Gamma_half_add, sin_pi_mul_eq_sq]
    have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
    rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
    have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
    have pw : (2 : ℂ) ^ (1 / 2 - a) * 2 ^ (a / 2 + 3 / 4) = 2 * 2 ^ (-(a / 2 - 1 / 4)) := by
      rw [two_cpow_mul_two_cpow _ _ (-(a / 2 - 1 / 4) + 1) (by ring),
        Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]; ring
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 - a)
    linear_combination (-(r * g1p * T * B) * (π * (g1m * g3p) + c)) * q1 +
      (-(r * g1p * c ^ 2)) * pw + (-(r * A * g1p)) * htr

/-- **Connection formula** (DLMF 12.2.16), valid for every `a`:
`V(a,-z) = cos(πa)/Γ(1/2 - a) U(a,z) + sin(πa) V(a,z)`. -/
@[dlmf 12.2.E16]
theorem pcfV_neg_eq (a z : ℂ) :
    pcfV a (-z) = Complex.cos (π * a) / Gamma (1 / 2 - a) * pcfU a z +
      Complex.sin (π * a) * pcfV a z := by
  have hg := (isWeberSol_pcfU a).lincomb (isWeberSol_pcfV a)
    (Complex.cos (π * a) / Gamma (1 / 2 - a)) (Complex.sin (π * a))
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  refine (isWeberSol_pcfV_neg a).eq_of_initial hg ?_ ?_ z
  · simp only [neg_zero]
    rw [pcfU_zero', pcfV_zero', pcfVZero, div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, sin_pi_mul_eq_sq, cos_pi_mul_eq_mul]
    have pw : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (-2 * s * c * g1m * g3m * g3p * T * A) * hππ +
      (-2 * s * c * π * g1m * g3m * g3p) * pw + (-2 * s * c * B * g3m) * q1 +
      (B * g3m * (1 - s ^ 2 + c ^ 2)) * q2 + (-s * B * g3m) * htr
  · simp only [neg_zero]
    rw [pcfUDeriv_zero', pcfVDeriv_zero', pcfVDerivZero, div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, sin_pi_mul_eq_sq, cos_pi_mul_eq_mul]
    have pw : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (2 * s * c * g1m * g3m * g1p * T * A) * hππ +
      (2 * s * c * π * g1m * g3m * g1p) * pw + (2 * s * c * B * g1m) * q2 +
      (-(B * g1m * (1 + s ^ 2 - c ^ 2))) * q1 + (c * B * g1m) * htr

/-- `cos(nπ) = (-1)^n` for natural `n`. -/
theorem cos_nat_mul_pi' (n : ℕ) : Complex.cos (n * π) = (-1) ^ n := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos,
    Real.cos_nat_mul_pi]
  push_cast; ring

/-- Parity of `U` at the Hermite parameters (DLMF 12.2.13):
`U(-n - 1/2, -z) = (-1)ⁿ U(-n - 1/2, z)`. -/
@[dlmf 12.2.E13]
theorem pcfU_neg_nat_sub_half_neg (n : ℕ) (z : ℂ) :
    pcfU (-n - 1 / 2) (-z) = (-1) ^ n * pcfU (-n - 1 / 2) z := by
  rw [pcfU_neg_eq, show (1 / 2 + (-(n : ℂ) - 1 / 2)) = -(n : ℂ) by ring,
    Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul, add_zero,
    show (π : ℂ) * (-(n : ℂ) - 1 / 2) = -(n * π) - π / 2 by ring, Complex.sin_sub_pi_div_two,
    Complex.cos_neg, cos_nat_mul_pi']
  ring

/-- Parity of `V` at the parameters `n + 1/2` (DLMF 12.2.14):
`V(n + 1/2, -z) = (-1)ⁿ V(n + 1/2, z)`. -/
@[dlmf 12.2.E14]
theorem pcfV_nat_add_half_neg (n : ℕ) (z : ℂ) :
    pcfV (n + 1 / 2) (-z) = (-1) ^ n * pcfV (n + 1 / 2) z := by
  rw [pcfV_neg_eq, show (1 / 2 - ((n : ℂ) + 1 / 2)) = -(n : ℂ) by ring,
    Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul, zero_add,
    show (π : ℂ) * ((n : ℂ) + 1 / 2) = n * π + π / 2 by ring, Complex.sin_add_pi_div_two,
    cos_nat_mul_pi']

/-- The classical form of `V` (DLMF 12.2.15 solved for `V`):
`V(a,z) = Γ(1/2 + a)/π (sin(πa) U(a,z) + U(a,-z))`, away from the poles of `Γ(1/2 + a)`. -/
theorem pcfV_eq {a : ℂ} (ha : ∀ n : ℕ, 1 / 2 + a ≠ -n) (z : ℂ) :
    pcfV a z = Gamma (1 / 2 + a) / π * (Complex.sin (π * a) * pcfU a z + pcfU a (-z)) := by
  have hΓ := Complex.Gamma_ne_zero ha
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [pcfU_neg_eq, show Complex.sin (π * a) * pcfU a z +
      (-Complex.sin (π * a) * pcfU a z + π / Gamma (1 / 2 + a) * pcfV a z) =
      π / Gamma (1 / 2 + a) * pcfV a z by ring, ← mul_assoc, div_mul_div_comm,
    mul_comm (Gamma (1 / 2 + a)) (π : ℂ), div_self (mul_ne_zero hπ0 hΓ), one_mul]

/-- `exp(-iπ(a/2 - 1/4)) = sin(π(1/4 + a/2)) + i cos(π(1/4 + a/2))`. -/
theorem exp_neg_I_pi_quarter (a : ℂ) :
    exp (-I * π * (a / 2 - 1 / 4)) =
      Complex.sin (π * (1 / 4 + a / 2)) + Complex.cos (π * (1 / 4 + a / 2)) * I := by
  rw [show -I * π * (a / 2 - 1 / 4) = (-(π * (1 / 4 + a / 2) - π / 2)) * I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.cos_sub_pi_div_two,
    Complex.sin_sub_pi_div_two]
  ring

/-- `exp(iπ(a/2 - 1/4)) = sin(π(1/4 + a/2)) - i cos(π(1/4 + a/2))`. -/
theorem exp_I_pi_quarter (a : ℂ) :
    exp (I * π * (a / 2 - 1 / 4)) =
      Complex.sin (π * (1 / 4 + a / 2)) - Complex.cos (π * (1 / 4 + a / 2)) * I := by
  rw [show I * π * (a / 2 - 1 / 4) = (π * (1 / 4 + a / 2) - π / 2) * I by ring,
    Complex.exp_mul_I, Complex.cos_sub_pi_div_two, Complex.sin_sub_pi_div_two]
  ring

/-- **Connection formula** (DLMF 12.2.20, upper signs), valid for every `a`:
`V(a,z) = -i/Γ(1/2 - a) U(a,z) + √(2/π) e^{-iπ(a/2 - 1/4)} U(-a, iz)`. -/
@[dlmf 12.2.E20]
theorem pcfV_eq_mul_I (a z : ℂ) :
    pcfV a z = -I / Gamma (1 / 2 - a) * pcfU a z +
      (Real.sqrt (2 / π) : ℂ) * exp (-I * π * (a / 2 - 1 / 4)) * pcfU (-a) (I * z) := by
  have hg := (isWeberSol_pcfU a).lincomb (isWeberSol_pcfU_mul_I a) (-I / Gamma (1 / 2 - a))
    ((Real.sqrt (2 / π) : ℂ) * exp (-I * π * (a / 2 - 1 / 4)))
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hR : (Real.sqrt (2 / π) : ℂ) * (Real.sqrt π : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg (by norm_num) Real.pi_pos.le),
      div_mul_cancel₀ _ Real.pi_ne_zero]
  refine (isWeberSol_pcfV a).eq_of_initial hg ?_ ?_ z
  · simp only [mul_zero]
    rw [pcfV_zero', pcfVZero, pcfU_zero' a, pcfU_zero' (-a), div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, exp_neg_I_pi_quarter, show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (I * g1m * g3m * T * A * g3p) * hππ + (I * g1m * g3m * g3p * π) * pwA +
      (I * g3m * B) * q1 + (-(s + c * I) * A2 * g3m) * hR + (-(s + c * I) * g3m) * pwB +
      (B * g3m) * q2
  · simp only [mul_zero]
    rw [pcfVDeriv_zero', pcfVDerivZero, pcfUDeriv_zero' a, pcfUDeriv_zero' (-a),
      div_eq_mul_inv _ (Gamma (1 / 2 - a)), recip_Gamma_half_sub, exp_neg_I_pi_quarter,
      show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (-I * g1m * g3m * T * A * g1p) * hππ + (-I * g1m * g3m * g1p * π) * pwA +
      (-I * g1m * B) * q2 + ((s + c * I) * I * A2 * g1m) * hR + ((s + c * I) * I * g1m) * pwB +
      (c * B * g1m) * Complex.I_sq + (B * g1m) * q1

/-- **Connection formula** (DLMF 12.2.20, lower signs), valid for every `a`:
`V(a,z) = i/Γ(1/2 - a) U(a,z) + √(2/π) e^{iπ(a/2 - 1/4)} U(-a, -iz)`. -/
@[dlmf 12.2.E20]
theorem pcfV_eq_mul_neg_I (a z : ℂ) :
    pcfV a z = I / Gamma (1 / 2 - a) * pcfU a z +
      (Real.sqrt (2 / π) : ℂ) * exp (I * π * (a / 2 - 1 / 4)) * pcfU (-a) (-I * z) := by
  have hg := (isWeberSol_pcfU a).lincomb (isWeberSol_pcfU_mul_neg_I a) (I / Gamma (1 / 2 - a))
    ((Real.sqrt (2 / π) : ℂ) * exp (I * π * (a / 2 - 1 / 4)))
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hR : (Real.sqrt (2 / π) : ℂ) * (Real.sqrt π : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg (by norm_num) Real.pi_pos.le),
      div_mul_cancel₀ _ Real.pi_ne_zero]
  refine (isWeberSol_pcfV a).eq_of_initial hg ?_ ?_ z
  · simp only [mul_zero]
    rw [pcfV_zero', pcfVZero, pcfU_zero' a, pcfU_zero' (-a), div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, exp_I_pi_quarter, show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (-I * g1m * g3m * T * A * g3p) * hππ + (-I * g1m * g3m * g3p * π) * pwA +
      (-I * g3m * B) * q1 + (-(s - c * I) * A2 * g3m) * hR + (-(s - c * I) * g3m) * pwB +
      (B * g3m) * q2
  · simp only [mul_zero]
    rw [pcfVDeriv_zero', pcfVDerivZero, pcfUDeriv_zero' a, pcfUDeriv_zero' (-a),
      div_eq_mul_inv _ (Gamma (1 / 2 - a)), recip_Gamma_half_sub, exp_I_pi_quarter,
      show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (I * g1m * g3m * T * A * g1p) * hππ + (I * g1m * g3m * g1p * π) * pwA +
      (I * g1m * B) * q2 + (-(s - c * I) * I * A2 * g1m) * hR + (-(s - c * I) * I * g1m) * pwB +
      (c * B * g1m) * Complex.I_sq + (B * g1m) * q1

/-- DLMF 12.8.7: `V'(a,z) + (z/2) V(a,z) - V(a+1,z) = 0`. -/
@[dlmf 12.8.E7]
theorem pcfV_recurrence_add (a z : ℂ) :
    deriv (pcfV a) z + z / 2 * pcfV a z - pcfV (a + 1) z = 0 := by
  rw [deriv_pcfV]
  have hs : IsWeberSol (a + 1) (fun w => pcfVDeriv a w + w / 2 * pcfV a w - pcfV (a + 1) w)
      (fun w => (w ^ 2 / 4 + a) * pcfV a w + 1 / 2 * pcfV a w + w / 2 * pcfVDeriv a w -
        pcfVDeriv (a + 1) w) := fun w => by
    have hU := hasDerivAt_pcfV a w
    have hU' := hasDerivAt_pcfVDeriv a w
    have hV := hasDerivAt_pcfV (a + 1) w
    have hV' := hasDerivAt_pcfVDeriv (a + 1) w
    refine ⟨(hU'.add (((hasDerivAt_id w).div_const 2).mul hU)).sub hV |>.congr_deriv ?_, ?_⟩
    · simp only [id]; ring
    · refine ((((((hasDerivAt_pow 2 w).div_const 4).add_const a).mul hU).add
        (hU.const_mul (1 / 2))).add (((hasDerivAt_id w).div_const 2).mul hU')).sub hV'
        |>.congr_deriv ?_
      simp only [id]; push_cast; ring
  have h0 : pcfVDeriv a 0 + 0 / 2 * pcfV a 0 - pcfV (a + 1) 0 = 0 := by
    simp only [pcfVDeriv_zero', pcfV_zero', pcfVZero, pcfVDerivZero]
    rw [show 3 / 4 - (a + 1) / 2 = 1 / 4 - a / 2 by ring,
      show 1 / 4 + (a + 1) / 2 = 3 / 4 + a / 2 by ring,
      show (a + 1) / 2 + 1 / 4 = a / 2 + 3 / 4 by ring]
    ring
  have h1 : ((0 : ℂ) ^ 2 / 4 + a) * pcfV a 0 + 1 / 2 * pcfV a 0 + 0 / 2 * pcfVDeriv a 0 -
      pcfVDeriv (a + 1) 0 = 0 := by
    have hgA := mul_recip_Gamma_add_one' (-1 / 4 - a / 2)
    rw [show -1 / 4 - a / 2 + 1 = 3 / 4 - a / 2 by ring] at hgA
    have hgB := mul_recip_Gamma_add_one' (1 / 4 + a / 2)
    rw [show 1 / 4 + a / 2 + 1 = 5 / 4 + a / 2 by ring] at hgB
    have pw : (2 : ℂ) ^ (a / 2 + 5 / 4) = 2 * 2 ^ (a / 2 + 1 / 4) := by
      rw [show a / 2 + 5 / 4 = (a / 2 + 1 / 4) + 1 by ring, Complex.cpow_add _ _ two_ne_zero,
        Complex.cpow_one]; ring
    simp only [pcfVDeriv_zero', pcfV_zero', pcfVZero, pcfVDerivZero]
    rw [show 1 / 4 - (a + 1) / 2 = -1 / 4 - a / 2 by ring,
      show 3 / 4 + (a + 1) / 2 = 5 / 4 + a / 2 by ring,
      show (a + 1) / 2 + 3 / 4 = a / 2 + 5 / 4 by ring, ← hgA, ← hgB, pw]
    ring
  exact hs.eq_zero h0 h1 z

/-- DLMF 12.8.6: `V'(a,z) - (z/2) V(a,z) - (a - 1/2) V(a-1,z) = 0`. -/
@[dlmf 12.8.E6]
theorem pcfV_recurrence_sub (a z : ℂ) :
    deriv (pcfV a) z - z / 2 * pcfV a z - (a - 1 / 2) * pcfV (a - 1) z = 0 := by
  rw [deriv_pcfV]
  have hs : IsWeberSol (a - 1)
      (fun w => pcfVDeriv a w - w / 2 * pcfV a w - (a - 1 / 2) * pcfV (a - 1) w)
      (fun w => (w ^ 2 / 4 + a) * pcfV a w - 1 / 2 * pcfV a w - w / 2 * pcfVDeriv a w -
        (a - 1 / 2) * pcfVDeriv (a - 1) w) := fun w => by
    have hU := hasDerivAt_pcfV a w
    have hU' := hasDerivAt_pcfVDeriv a w
    have hV := hasDerivAt_pcfV (a - 1) w
    have hV' := hasDerivAt_pcfVDeriv (a - 1) w
    refine ⟨(hU'.sub (((hasDerivAt_id w).div_const 2).mul hU)).sub (hV.const_mul (a - 1 / 2))
      |>.congr_deriv ?_, ?_⟩
    · simp only [id]; ring
    · refine ((((((hasDerivAt_pow 2 w).div_const 4).add_const a).mul hU).sub
        (hU.const_mul (1 / 2))).sub (((hasDerivAt_id w).div_const 2).mul hU')).sub
        (hV'.const_mul (a - 1 / 2)) |>.congr_deriv ?_
      simp only [id]; push_cast; ring
  have h0 : pcfVDeriv a 0 - 0 / 2 * pcfV a 0 - (a - 1 / 2) * pcfV (a - 1) 0 = 0 := by
    have hgA := mul_recip_Gamma_add_one' (1 / 4 - a / 2)
    rw [show 1 / 4 - a / 2 + 1 = 5 / 4 - a / 2 by ring] at hgA
    have hgB := mul_recip_Gamma_add_one' (a / 2 - 1 / 4)
    rw [show a / 2 - 1 / 4 + 1 = 3 / 4 + a / 2 by ring] at hgB
    have pw : (2 : ℂ) ^ (a / 2 + 3 / 4) = 2 * 2 ^ (a / 2 - 1 / 4) := by
      rw [show a / 2 + 3 / 4 = (a / 2 - 1 / 4) + 1 by ring, Complex.cpow_add _ _ two_ne_zero,
        Complex.cpow_one]; ring
    simp only [pcfVDeriv_zero', pcfV_zero', pcfVZero, pcfVDerivZero]
    rw [show 3 / 4 - (a - 1) / 2 = 5 / 4 - a / 2 by ring,
      show 1 / 4 + (a - 1) / 2 = a / 2 - 1 / 4 by ring,
      show (a - 1) / 2 + 1 / 4 = a / 2 - 1 / 4 by ring, ← hgA, ← hgB, pw]
    ring
  have h1 : ((0 : ℂ) ^ 2 / 4 + a) * pcfV a 0 - 1 / 2 * pcfV a 0 - 0 / 2 * pcfVDeriv a 0 -
      (a - 1 / 2) * pcfVDeriv (a - 1) 0 = 0 := by
    simp only [pcfVDeriv_zero', pcfV_zero', pcfVZero, pcfVDerivZero]
    rw [show 1 / 4 - (a - 1) / 2 = 3 / 4 - a / 2 by ring,
      show 3 / 4 + (a - 1) / 2 = 1 / 4 + a / 2 by ring,
      show (a - 1) / 2 + 3 / 4 = a / 2 + 1 / 4 by ring]
    ring
  exact hs.eq_zero h0 h1 z

/-- DLMF 12.8.5: `z V(a,z) - V(a+1,z) + (a - 1/2) V(a-1,z) = 0`. -/
@[dlmf 12.8.E5]
theorem pcfV_three_term (a z : ℂ) :
    z * pcfV a z - pcfV (a + 1) z + (a - 1 / 2) * pcfV (a - 1) z = 0 := by
  linear_combination pcfV_recurrence_add a z - pcfV_recurrence_sub a z

/-- DLMF 12.8.8: `2 V'(a,z) - V(a+1,z) - (a - 1/2) V(a-1,z) = 0`. -/
@[dlmf 12.8.E8]
theorem pcfV_deriv_recurrence (a z : ℂ) :
    2 * deriv (pcfV a) z - pcfV (a + 1) z - (a - 1 / 2) * pcfV (a - 1) z = 0 := by
  linear_combination pcfV_recurrence_add a z + pcfV_recurrence_sub a z

end DLMF.Confluent
