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
# Parabolic cylinder equations and Laplace representations

Weber equations, uniqueness, recurrences, Hermite specializations and the Laplace representation
of U.

Source references and common attribution are retained in
`DLMF.Confluent.ParabolicCylinder`.
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

end DLMF.Confluent
end
end
