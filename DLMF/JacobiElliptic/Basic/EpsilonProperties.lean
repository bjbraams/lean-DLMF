/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Epsilon
public import DLMF.Elliptic.Basic.Jacobi

/-!
# Basic properties of Jacobi's Epsilon function

Jacobi's Epsilon is the incomplete elliptic integral of the second kind evaluated at the
amplitude (DLMF 22.16.31). Its derivative is `dn²`, and translating its argument by `2K`
adds `2E` (DLMF 22.16.29).
-/

public section

open Real DLMF.Elliptic

noncomputable section

namespace DLMF.JacobiElliptic

variable {k : ℝ}

/-- DLMF 22.16.31: `E(am(x,k), k) = ℰ(x, k)`; proved for all real `x` (stronger than DLMF,
which states `-K ≤ x ≤ K`). -/
@[dlmf 22.16.E31 "stronger than DLMF: all real x; real modulus with k² < 1"]
theorem Real.incompleteEllipticEOfParameter_jacobiAmOfParameter (hm : k ^ 2 < 1) (x : ℝ) :
    Real.incompleteEllipticEOfParameter (Real.jacobiAmOfParameter x (k ^ 2)) (k ^ 2) =
        Real.jacobiEpsilon x k := by
  have hd : ∀ t, HasDerivAt
      (fun t => Real.incompleteEllipticEOfParameter (Real.jacobiAmOfParameter t (k ^ 2)) (k ^ 2))
      (Real.jacobiDnOfParameter t (k ^ 2) ^ 2) t := fun t => by
    have := (Real.hasDerivAt_incompleteEllipticEOfParameter hm
        (Real.jacobiAmOfParameter t (k ^ 2))).comp t
      (Real.hasDerivAt_jacobiAmOfParameter hm t)
    refine this.congr_deriv ?_
    rw [Real.jacobiDnOfParameter, Real.jacobiSnOfParameter]; ring
  have h0 : Real.incompleteEllipticEOfParameter (Real.jacobiAmOfParameter 0 (k ^ 2))
      (k ^ 2) = 0 := by
    simp [Real.jacobiAmOfParameter_zero hm, Real.incompleteEllipticEOfParameter]
  rw [Real.jacobiEpsilon, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (((Real.continuous_jacobiDnOfParameter hm).pow 2).intervalIntegrable 0 x), h0, sub_zero]

/-- DLMF 22.16.29: `ℰ(x + 2K, k) = ℰ(x, k) + 2E(k)`. -/
@[dlmf 22.16.E29 "special case: real modulus with k² < 1"]
theorem Real.jacobiEpsilon_add_two_completeEllipticKOfParameter (hm : k ^ 2 < 1) (x : ℝ) :
    Real.jacobiEpsilon (x + 2 * Real.completeEllipticKOfParameter (k ^ 2)) k =
      Real.jacobiEpsilon x k + 2 * Real.completeEllipticEOfParameter (k ^ 2) := by
  rw [← Real.incompleteEllipticEOfParameter_jacobiAmOfParameter hm,
      ← Real.incompleteEllipticEOfParameter_jacobiAmOfParameter hm,
    Real.jacobiAmOfParameter_add_two_completeEllipticKOfParameter hm,
        Real.incompleteEllipticEOfParameter_add_pi hm]

/-- At `x`, the function `(fun x => Real.jacobiEpsilon x k)` has derivative
`(Real.jacobiDnOfParameter x (k ^ 2) ^ 2)`. -/
theorem Real.hasDerivAt_jacobiEpsilon {k : ℝ} (hm : k ^ 2 < 1) (x : ℝ) :
    HasDerivAt (fun x => Real.jacobiEpsilon x k) (Real.jacobiDnOfParameter x (k ^ 2) ^ 2) x :=
  (((Real.continuous_jacobiDnOfParameter hm).pow 2).integral_hasStrictDerivAt 0 x).hasDerivAt

end DLMF.JacobiElliptic
