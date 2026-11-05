/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# An antiderivative from an Appell family

If `F₀' = g` and `Fₖ₊₁' = (k+1) Fₖ`, the alternating binomial combination
`∑_{k=0}ⁿ (-1)ᵏ C(n,k) Fₖ(x) xⁿ⁻ᵏ` has derivative `xⁿ g(x)`.
This is the finite telescoping identity behind repeated integration by parts.
-/

@[expose] public section

open scoped BigOperators

namespace HasDerivAt

/-- The alternating binomial sum of an Appell family differentiates to a monomial times `F₀'`. -/
theorem sum_choose_mul_pow_appell {F : ℕ → ℂ → ℂ} {g x : ℂ} (n : ℕ)
    (h0 : HasDerivAt (F 0) g x)
    (hF : ∀ k < n, HasDerivAt (F (k + 1)) ((k + 1) * F k x) x) :
    HasDerivAt (fun z => ∑ k ∈ Finset.range (n + 1),
      (-1) ^ k * (n.choose k : ℂ) * F k z * z ^ (n - k)) (x ^ n * g) x := by
  let C : ℕ → ℂ := fun k => (-1) ^ k * (n.choose k : ℂ)
  let D : ℕ → ℂ := fun k => if k = 0 then g else k * F (k - 1) x
  have hD (k : ℕ) (hk : k ∈ Finset.range (n + 1)) : HasDerivAt (F k) (D k) x := by
    cases k with
    | zero => simpa [D] using h0
    | succ k => simpa [D] using hF k (by simpa using hk)
  have hsum := HasDerivAt.fun_sum (u := Finset.range (n + 1)) (fun k hk =>
    ((hD k hk).const_mul (C k)).mul ((hasDerivAt_id x).pow (n - k)))
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq, mul_one] at hsum
  have hcoef (k : ℕ) : C (k + 1) * (k + 1) = -C k * ((n - k : ℕ) : ℂ) := by
    have h := congrArg (Nat.cast : ℕ → ℂ) (Nat.choose_succ_right_eq n k)
    push_cast at h
    dsimp only [C]
    rw [pow_succ]
    linear_combination -((-1 : ℂ) ^ k) * h
  have hpair (k : ℕ) : C (k + 1) * D (k + 1) * x ^ (n - (k + 1)) =
      -(C k * F k x * (((n - k : ℕ) : ℂ) * x ^ (n - k - 1))) := by
    simp only [D, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [show n - (k + 1) = n - k - 1 by omega]
    calc C (k + 1) * ((k + 1) * F k x) * x ^ (n - k - 1) =
        (C (k + 1) * (k + 1)) * F k x * x ^ (n - k - 1) := by ring
      _ = _ := by rw [hcoef]; ring
  have hfirst : (∑ k ∈ Finset.range (n + 1), C k * D k * x ^ (n - k)) =
      g * x ^ n - ∑ k ∈ Finset.range n,
        C k * F k x * (((n - k : ℕ) : ℂ) * x ^ (n - k - 1)) := by
    rw [Finset.sum_range_succ']
    simp_rw [hpair]
    simp only [C, D, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      ite_eq_left rfl, one_mul, Nat.sub_zero, Finset.sum_neg_distrib]
    ring
  have hval : (∑ k ∈ Finset.range (n + 1),
      (C k * D k * x ^ (n - k) + C k * F k x *
        (((n - k : ℕ) : ℂ) * x ^ (n - k - 1)))) = x ^ n * g := by
    rw [Finset.sum_add_distrib, hfirst, Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    ring
  have hfinal := hsum.congr_deriv hval
  exact hfinal

end HasDerivAt
