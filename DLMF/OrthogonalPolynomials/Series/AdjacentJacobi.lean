/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Series.BrafmanAndWeighted

/-!
# Generating functions for adjacent Jacobi families

Generating functions relating adjacent Jacobi parameters, with normalization and convergence
retained.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Series`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

open DLMF.Bessel

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

section AdjacentJacobiGenerating

set_option maxHeartbeats 1000000

/-- The adjacent Jacobi coefficients are consecutive Gegenbauer coefficients. -/
theorem jacobi_adjacent_coefficient {b : ℂ} (hb : -1 < b.re) (n : ℕ) (x : ℂ) :
    poch (2 * b + 2) (n + 1) / poch (b + 1) (n + 1) * jacobiPolyP (b + 1) b (n + 1) x =
      ultrasphPoly (b + 3 / 2) (n + 1) x + ultrasphPoly (b + 3 / 2) n x := by
  have ht : 0 < (b + 1).re := by simp; linarith
  have hp (k : ℕ) : poch (b + 2) k ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) k
  have hb0 : b + 1 ≠ 0 := ne_zero_of_re_pos ht
  have hn0 : (n : ℂ) + b + 2 ≠ 0 := ne_zero_of_re_pos (by
    simp; linarith [Nat.cast_nonneg (α := ℝ) n])
  have hR := jacobi_raise_beta (α := b + 1) (β := b) (by simp; linarith) n x
  have hc (k : ℕ) : ultrasphPoly (b + 3 / 2) k x =
      poch (2 * b + 3) k / poch (b + 2) k * jacobiPolyP (b + 1) (b + 1) k x := by
    have hden : b + 3 / 2 + 1 / 2 = b + 2 := by ring
    have hnum : 2 * (b + 3 / 2) = 2 * b + 3 := by ring
    have hparam : b + 3 / 2 - 1 / 2 = b + 1 := by ring
    have h := ultrasphPoly_eq_jacobiPolyP (lam := b + 3 / 2) k x (by rw [hden]; exact hp k)
    simpa only [hden, hnum, hparam] using h
  rw [hc (n + 1), hc n]
  rw [show 2 * b + 2 = 2 * (b + 1) by ring,
    poch_succ_left (2 * (b + 1)) n, poch_succ_left (b + 1) n,
    show 2 * (b + 1) + 1 = 2 * b + 3 by ring,
    show b + 1 + 1 = b + 2 by ring,
    poch_succ (2 * b + 3) n, poch_succ (b + 2) n]
  have hn0' : b + 2 + (n : ℂ) ≠ 0 := by
    rw [show b + 2 + (n : ℂ) = (n : ℂ) + b + 2 by ring]
    exact hn0
  field_simp [hb0, hp n, hn0']
  linear_combination (poch (2 * b + 3) n) * hR

/-- The series with terms `(fun n : ℕ => poch (2 * β + 2) n / poch (β + 1) n * jacobiPolyP (β + 1)
β n x * z ^ n)` converges to `((1 + z) / (1 - 2 * x * z + z ^ 2) ^ (β + 3 / 2))`. -/
@[dlmf 18.12.E3_5]
theorem jacobi_adjacent_generating_function {β : ℂ} (hβ : -1 < β.re)
    {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => poch (2 * β + 2) n / poch (β + 1) n * jacobiPolyP (β + 1) β n x * z ^ n)
      ((1 + z) / (1 - 2 * x * z + z ^ 2) ^ (β + 3 / 2)) := by
  have h := ultrasphPoly_generating_function (lam := β + 3 / 2)
    (by simp; linarith) hx hz
  let f : ℕ → ℂ := fun n => if n = 0 then 0 else ultrasphPoly (β + 3 / 2) (n - 1) x * z ^ n
  have hs : HasSum f (z * (1 - 2 * x * z + z ^ 2) ^ (-(β + 3 / 2))) := by
    have hh := h.mul_left z
    have hshift : HasSum (fun n => f (n + 1)) (z * (1 - 2 * x * z + z ^ 2) ^ (-(β + 3 / 2))) := by
      simpa [f, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hh
    -- Mathlib's shifted-series identity includes the separate degree-zero term.
    have he := (hasSum_nat_add_iff 1).mp hshift
    simpa [f] using he
  have hh := h.add hs
  convert hh using 1
  · funext n
    cases n with
    | zero => simp [f, poch_zero]
    | succ n => simp only [f, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
                rw [jacobi_adjacent_coefficient hβ]
                ring
  · rw [cpow_neg]
    ring

end AdjacentJacobiGenerating

/-- The series with terms `(fun n : ℕ => 2 * (Chebyshev.T ℂ (n + 1)).eval (x : ℂ) * z ^ (n + 1))`
converges to `((1 - z ^ 2) / (1 - 2 * x * z + z ^ 2) - 1)`. -/
@[dlmf 18.12.E7]
theorem chebyshevT_poisson_generating_function {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => 2 * (Chebyshev.T ℂ (n + 1)).eval (x : ℂ) * z ^ (n + 1))
      ((1 - z ^ 2) / (1 - 2 * x * z + z ^ 2) - 1) := by
  have hD := one_sub_two_mul_add_sq_ne_zero hx hz
  have h := ((hasSum_nat_add_iff' 1).mpr (chebyshevT_generating_function hx hz)).mul_left 2
  convert h using 1
  · funext n; push_cast; ring
  · simp only [Finset.sum_range_one, pow_zero, mul_one, Nat.cast_zero, Chebyshev.T_zero, eval_one]
    rw [div_sub_one hD, div_sub_one hD, ← mul_div_assoc]
    congr 1
    ring

/-- The exponential series in `ℂ`. -/
theorem hasSum_cexp (z : ℂ) : HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

/-- The exponential series converges absolutely. -/
theorem summable_norm_pow_div_factorial (z : ℂ) :
    Summable fun n : ℕ => ‖z ^ n / (n.factorial : ℂ)‖ := by
  simpa [norm_div, norm_pow] using Real.summable_pow_div_factorial ‖z‖

/-- The series with terms `(fun n : ℕ => laguerrePolyL α n x / poch (α + 1) n * (z : ℂ) ^ n)`
converges to `(Gamma (α + 1 : ℂ) * (x * z : ℂ) ^ (-α / 2 : ℂ) * exp z * besselJ α (2 *
Real.sqrt (x * z)))`. -/
@[dlmf 18.12.E14]
theorem laguerrePolyL_bessel_generating_function {α : ℝ} (hα : -1 < α)
    {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    HasSum (fun n : ℕ => laguerrePolyL α n x / poch (α + 1) n * (z : ℂ) ^ n)
      (Gamma (α + 1 : ℂ) * (x * z : ℂ) ^ (-α / 2 : ℂ) * exp z *
        besselJ α (2 * Real.sqrt (x * z))) := by
  have hc : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  set w : ℂ := -((x : ℂ) * z)
  have hf := summable_norm_regularized0F1 (α + 1) w
  have hg := summable_norm_pow_div_factorial (z : ℂ)
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm.hasSum
  rw [← hprod, ((hasFPowerSeriesOnBall_regularized0F1 (α + 1)).hasSum_mul_pow
      (by simp)).tsum_eq, (hasSum_cexp _).tsum_eq] at hsum
  -- the Bessel prefactor
  have hxz : (0 : ℝ) < x * z := mul_pos hx hz
  have hbes : (x * z : ℂ) ^ (-α / 2 : ℂ) * besselJ α (2 * Real.sqrt (x * z)) =
      regularizedHGFun (∅ : Multiset ℂ) {(α : ℂ) + 1} w := by
    set t := x * z
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt hxz.le
    simp only [besselJ_eq_regularized]
    have harg : -((2 * (Real.sqrt t : ℂ)) ^ 2 / 4) = w := by
      simp only [w, t]
      rw [mul_pow, ← Complex.ofReal_pow, hsq]
      simp only [t]; push_cast; ring
    rw [harg, ← mul_assoc]
    convert one_mul _ using 2
    rw [show 2 * (Real.sqrt t : ℂ) / 2 = (Real.sqrt t : ℂ) by ring,
      show (x : ℂ) * z = (t : ℂ) by simp only [t]; push_cast; ring,
      show (-(α : ℂ) / 2) = ((-α / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hxz.le, ← Complex.ofReal_cpow (Real.sqrt_nonneg t),
      ← Complex.ofReal_mul, Real.sqrt_eq_rpow, ← Real.rpow_mul hxz.le, ← Real.rpow_add hxz,
      show -α / 2 + 1 / 2 * α = 0 by ring, Real.rpow_zero, Complex.ofReal_one]
  have hval : Gamma (α + 1 : ℂ) * (x * z : ℂ) ^ (-α / 2 : ℂ) * exp z *
      besselJ α (2 * Real.sqrt (x * z)) =
      Gamma (α + 1 : ℂ) * (regularizedHGFun (∅ : Multiset ℂ) {(α : ℂ) + 1} w * exp z) := by
    rw [← hbes]; ring
  rw [hval]
  refine (hsum.mul_left (Gamma (α + 1 : ℂ))).congr_fun fun n => ?_
  have hpos : 0 < ((α : ℂ) + 1).re := by simp; linarith
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← laguerreExtended_eq hc, laguerreExtended,
    Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsplit : poch ((α : ℂ) + 1) n = poch ((α : ℂ) + 1) k * poch ((α : ℂ) + 1 + k) (n - k) := by
    rw [← poch_add, Nat.add_sub_cancel' hkn]
  have hG : Gamma ((α : ℂ) + 1 + k) = Gamma ((α : ℂ) + 1) * poch ((α : ℂ) + 1) k := by
    have := Complex.Gamma_add_nat_div_Gamma_eq (n := k) ((α : ℂ) + 1) hc
    rw [div_eq_iff (Complex.Gamma_ne_zero hc)] at this
    rw [this, poch]; ring
  have h1 : poch ((α : ℂ) + 1) k ≠ 0 := poch_ne_zero_of_re_pos hpos k
  have h2 : poch ((α : ℂ) + 1 + k) (n - k) ≠ 0 := poch_ne_zero_of_re_pos (by
    simp only [Complex.add_re, Complex.natCast_re] at hpos ⊢; positivity) (n - k)
  have h3 : Gamma ((α : ℂ) + 1) ≠ 0 := Complex.Gamma_ne_zero hc
  have hzn : (z : ℂ) ^ n = (z : ℂ) ^ k * (z : ℂ) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [regularizedHGFunCoeff_empty, hG, hsplit, hzn, show (α : ℂ) + k + 1 = α + 1 + k by ring]
  have hw : w ^ k = (-1) ^ k * (x : ℂ) ^ k * (z : ℂ) ^ k := by
    simp only [w]; rw [neg_pow, mul_pow]; ring
  rw [hw, neg_pow (x : ℂ) k]
  field_simp

/-- The Laguerre generating function as a `HasSum`. -/
theorem hasSum_laguerrePolyL_generating_function {α x t : ℂ} (hα : ∀ k : ℕ, α + 1 ≠ -(k : ℂ))
    (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ => laguerrePolyL α n x * t ^ n)
        ((1 - t) ^ (-α - 1) * exp (-x * t / (1 - t))) := by
  have h := laguerrePolyL_generating_function (x := x) hα ht
  have h1t : (1 : ℂ) - t ≠ 0 := by
    intro h0
    have : t = 1 := by linear_combination -h0
    rw [this, norm_one] at ht; exact lt_irrefl _ ht
  have hne : (1 - t) ^ (-α - 1) * exp (-x * t / (1 - t)) ≠ 0 := by
    refine mul_ne_zero ?_ (exp_ne_zero _)
    rw [cpow_def_of_ne_zero h1t]; exact exp_ne_zero _
  have hs : Summable fun n : ℕ => laguerrePolyL α n x * t ^ n := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at h
    exact hne h
  rw [h]; exact hs.hasSum

/-- DLMF 18.12.17 prints the incorrect convergence condition `|z| < 1`
(checked 2026-09-16). The disk is `|z| < 1/2`: already at `x = 0`,
the even coefficients are `(-1)^k * (2*k)! / (k!)²`, with radius `1/2`. -/
@[dlmf 18.12.E17]
theorem hermitePolyH_half_factorial_generating_function (x : ℂ) {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    HasSum (fun n : ℕ => aeval x (hermitePolyH n) / ((n / 2).factorial : ℂ) * z ^ n)
      ((1 + 2 * x * z + 4 * z ^ 2) / (1 + 4 * z ^ 2) ^ (3 / 2 : ℂ) *
        exp (4 * x ^ 2 * z ^ 2 / (1 + 4 * z ^ 2))) := by
  have ht : ‖-4 * z ^ 2‖ < 1 := by
    rw [norm_mul, norm_neg, norm_pow]
    have := norm_nonneg z
    norm_num; nlinarith
  have hw : (1 : ℂ) + 4 * z ^ 2 ≠ 0 := by
    intro h0
    have : -4 * z ^ 2 = 1 := by linear_combination -h0
    rw [this, norm_one] at ht; exact lt_irrefl _ ht
  have he := hasSum_laguerrePolyL_generating_function (α := -1 / 2) (x := x ^ 2)
    (not_neg_nat_of_re_pos (by norm_num)) ht
  have ho := (hasSum_laguerrePolyL_generating_function (α := 1 / 2) (x := x ^ 2)
    (not_neg_nat_of_re_pos (by norm_num)) ht).mul_left (2 * x * z)
  set E := exp (4 * x ^ 2 * z ^ 2 / (1 + 4 * z ^ 2))
  have hE : exp (-x ^ 2 * (-4 * z ^ 2) / (1 + 4 * z ^ 2)) = E := by
    congr 1; ring_nf
  rw [show (1 : ℂ) - -4 * z ^ 2 = 1 + 4 * z ^ 2 by ring, hE] at he ho
  set f : ℕ → ℂ := fun n => aeval x (hermitePolyH n) / ((n / 2).factorial : ℂ) * z ^ n with hf
  have hev : HasSum (fun m => f (2 * m))
      ((1 + 4 * z ^ 2) ^ (-(-1 / 2) - 1 : ℂ) * E) := by
    refine he.congr_fun fun m => ?_
    have hm : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [hf, show 2 * m / 2 = m by omega]
    rw [hermitePolyH_even_eq_laguerrePolyL, mul_pow, neg_pow (4 : ℂ),
      show z ^ (2 * m) = (z ^ 2) ^ m by rw [pow_mul],
      show (2 : ℂ) ^ (2 * m) = 4 ^ m by rw [pow_mul]; norm_num]
    field_simp
  have hod : HasSum (fun m => f (2 * m + 1))
      (2 * x * z * ((1 + 4 * z ^ 2) ^ (-(1 / 2) - 1 : ℂ) * E)) := by
    refine ho.congr_fun fun m => ?_
    have hm : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [hf, show (2 * m + 1) / 2 = m by omega]
    rw [hermitePolyH_odd_eq_laguerrePolyL, mul_pow, neg_pow (4 : ℂ),
      show z ^ (2 * m + 1) = z * (z ^ 2) ^ m by rw [pow_succ, pow_mul]; ring,
      show (2 : ℂ) ^ (2 * m + 1) = 2 * 4 ^ m by rw [pow_succ, pow_mul]; norm_num; ring]
    field_simp
  have hsum := hev.even_add_odd hod
  convert hsum using 1
  set w := (1 : ℂ) + 4 * z ^ 2
  have h1 : w ^ (-(-1 / 2) - 1 : ℂ) = w * (w ^ (3 / 2 : ℂ))⁻¹ := by
    rw [← cpow_neg, show (-(-1 / 2) - 1 : ℂ) = 1 + -(3 / 2) by norm_num, cpow_add _ _ hw, cpow_one]
  have h2 : w ^ (-(1 / 2) - 1 : ℂ) = (w ^ (3 / 2 : ℂ))⁻¹ := by
    rw [← cpow_neg]; norm_num
  rw [h1, h2]
  ring

end DLMF.OrthogonalPolynomials

end
end
