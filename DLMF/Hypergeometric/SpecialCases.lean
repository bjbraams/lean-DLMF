/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Elementary
public import DLMF.Confluent.ExpIntegral

/-!
# Special cases from Duverney, Chapters 3–4

* `ordinaryHypergeometric_one_one_half`: `F(1,1;a+1;1/2) = a(ψ((a+1)/2) - ψ(a/2))` (Ex. 4.10), from
  Euler's transformation and `half_argument_digamma`.
* `Real.sinInt_eq_regularizedHGFun`: `Si(x) = x ₁F₂(1/2; 3/2, 3/2; -x²/4)` (Duverney (3.19)).
-/

@[expose] public section

open Complex Filter
open scoped Topology Nat Real
open DLMF.Bessel

noncomputable section

namespace DLMF.Hypergeometric

/-- Duverney Ex. 4.10: `F(1,1;a+1;1/2) = a (ψ((a+1)/2) - ψ(a/2))` for `Re a > 0`. -/
theorem ordinaryHypergeometric_one_one_half {a : ℂ} (ha : 0 < a.re) :
    ₂F₁ 1 1 (a + 1) (1 / 2) = a * (digamma ((a + 1) / 2) - digamma (a / 2)) := by
  have hE := euler_transformation (a := 1) (b := 1) (c := a + 1) (z := 1 / 2) (by norm_num)
    (by simpa using ha) (by norm_num)
  rw [show a + 1 - 1 - 1 = a - 1 by ring, show a + 1 - 1 = a by ring] at hE
  have hD := half_argument_digamma ha
  have hpow : (1 - (1 / 2 : ℂ)) ^ (a - 1) = 2 * (2 : ℂ) ^ (-a) := by
    rw [show (1 : ℂ) - 1 / 2 = (2 : ℂ)⁻¹ by norm_num,
      inv_cpow _ _ (by rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, arg_ofReal_of_nonneg
        (by norm_num)]; exact Real.pi_pos.ne),
      ← cpow_neg, show -(a - 1) = -a + 1 by ring, cpow_add _ _ two_ne_zero, cpow_one]
    ring
  rw [hE, hpow]
  linear_combination 2 * hD

/-- The regularized function as a `tsum` of its coefficients. -/
theorem regularizedHGFun_eq_tsum_coeff (a b : Multiset ℂ) (z : ℂ) :
    regularizedHGFun a b z = ∑' n : ℕ, regularizedHGFunCoeff a b n * z ^ n := by
  simp only [regularizedHGFun, FormalMultilinearSeries.sum, regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- **The sine integral as a `₁F₂`** (Duverney (3.19)): in regularized form,
`Si(x) = (π/4) x 𝐅(1/2; 3/2, 3/2; -x²/4)`, i.e. `Si(x) = x ₁F₂(1/2; 3/2, 3/2; -x²/4)` since
`Γ(3/2)² = π/4`. -/
theorem Real.sinInt_eq_regularizedHGFun (x : ℝ) :
    (DLMF.Confluent.Real.sinInt x : ℂ) =
      π / 4 * x * regularizedHGFun {1 / 2} {3 / 2, 3 / 2} (-((x : ℂ) ^ 2) / 4) := by
  have h := (DLMF.Confluent.Real.hasSum_sinInt x).mapL Complex.ofRealCLM
  rw [regularizedHGFun_eq_tsum_coeff, ← tsum_mul_left]
  refine (h.tsum_eq.symm.trans (tsum_congr fun n => ?_))
  simp only [ofRealCLM_apply, regularizedHGFunCoeff,
    Multiset.map_singleton, Multiset.prod_singleton, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.prod_cons]
  have hp : (ascPochhammer ℂ n).eval (1 / 2 : ℂ) = ((2 * n)! : ℂ) / (4 ^ n * n !) := by
    have h1 := Complex.Gamma_add_nat_div_Gamma_eq (n := n) (1 / 2 : ℂ) (fun k hk => by
      have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
    rw [← h1, Gamma_nat_add_half]
    have : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero (fun k hk => by
      have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
    field_simp
  have hG : Gamma ((3 / 2 : ℂ) + n) = ((2 * (n + 1))! : ℂ) / (4 ^ (n + 1) * (n + 1)!) *
      Gamma (1 / 2) := by
    rw [show (3 / 2 : ℂ) + n = 1 / 2 + ((n + 1 : ℕ) : ℂ) by push_cast; ring, Gamma_nat_add_half]
  have hpi : Gamma (1 / 2 : ℂ) ^ 2 = π := by
    rw [Complex.Gamma_one_half_eq, show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow, ← ofReal_pow,
      Real.sq_sqrt Real.pi_pos.le]
  rw [hp, hG]
  have hs : Gamma (1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero (fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
  have hpi0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (2 * (n + 1))! = (2 * n + 2) * ((2 * n + 1) * (2 * n)!) by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ],
    show (2 * n + 1)! = (2 * n + 1) * (2 * n)! from Nat.factorial_succ _, Nat.factorial_succ n]
  have hf : ((2 * n)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf' : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2n : (2 * (n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * n)
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [show (-((x : ℂ) ^ 2) / 4) ^ n = (-1) ^ n * (x : ℂ) ^ (2 * n) / 4 ^ n by
    rw [div_pow, neg_pow, ← pow_mul]]
  push_cast
  field_simp
  rw [hpi]
  ring

end DLMF.Hypergeometric

end
