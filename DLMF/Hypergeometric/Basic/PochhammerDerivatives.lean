/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.Pochhammer
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Derivatives of Pochhammer symbols at their zeros

The polynomial `(s)_m` has a simple zero at `s = -n` whenever `n < m`. Factoring out
its unique vanishing linear factor evaluates the derivative without a gamma quotient.
-/

@[expose] public noncomputable section

namespace DLMF.Hypergeometric

/-- The derivative of the rising factorial at its simple negative-integer zero. -/
theorem hasDerivAt_pochhammer_neg_nat_of_lt {n m : ℕ} (hm : n < m) :
    HasDerivAt (fun s : ℂ => pochhammer s m)
      ((-1 : ℂ) ^ n * n.factorial * (m - n - 1).factorial) (-(n : ℂ)) := by
  have heq : (fun s : ℂ => pochhammer s m) = fun s =>
      pochhammer s n * (s + n) * pochhammer (s + (n + 1 : ℕ)) (m - n - 1) := by
    funext s
    have h := pochhammer_add s (n + 1) (m - n - 1)
    rw [show (n + 1) + (m - n - 1) = m by omega, pochhammer_succ] at h
    exact h
  have hp := (Polynomial.hasDerivAt (ascPochhammer ℂ n) (-(n : ℂ)))
  have h1 : HasDerivAt (fun s : ℂ => s + n) 1 (-(n : ℂ)) :=
    (hasDerivAt_id _).add_const _
  have h2 := (Polynomial.hasDerivAt (ascPochhammer ℂ (m - n - 1))
    (-(n : ℂ) + ((n + 1 : ℕ) : ℂ))).comp (-(n : ℂ))
      ((hasDerivAt_id (-(n : ℂ))).add_const ((n + 1 : ℕ) : ℂ))
  have h := (hp.mul h1).mul h2
  have e1 : -(n : ℂ) + ((n + 1 : ℕ) : ℂ) = 1 := by push_cast; ring
  rw [heq]
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, Pi.mul_apply, id_eq, e1, neg_add_cancel, mul_zero,
    zero_add, mul_one, zero_mul, add_zero]
  change pochhammer (-(n : ℂ)) n * pochhammer 1 (m - n - 1) = _
  rw [pochhammer_nat_one, pochhammer_neg_coe_nat, Nat.descFactorial_self]


end DLMF.Hypergeometric
