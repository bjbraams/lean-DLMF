/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.LegendreAddition

/-!
# The branch-free polynomial Legendre addition identity

Olver, *Asymptotics and Special Functions*, Chapter 5, Theorem 14.1,
p. 183, synopsis O-5.24. Arbitrary paired square roots are permitted, so
artificial branch restrictions disappear after forming their products.
The source's associated-polynomial version follows by Rodrigues's identity.
-/

@[expose] public noncomputable section

open Complex
open DLMF.OrthogonalPolynomials
open DLMF.OrthogonalPolynomials.LegendreAddition

namespace DLMF.Legendre

/-- The finite addition formula for every pair of complex square roots, with no
principal-branch or slit-plane restrictions on the polynomial arguments.
Olver, Chapter 5, Theorem 14.1, p. 183, synopsis O-5.24. -/
theorem legendrePolynomialP_addition_sqrt_pair (n : ℕ) (z₁ z₂ r₁ r₂ φ : ℂ)
    (hr₁ : r₁ ^ 2 = z₁ ^ 2 - 1) (hr₂ : r₂ ^ 2 = z₂ ^ 2 - 1) :
    legendrePolynomialP n (z₁ * z₂ - r₁ * r₂ * cos φ) =
      legendrePolynomialP n z₁ * legendrePolynomialP n z₂ +
        2 * ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ (k + 1) * ((n - (k + 1)).factorial : ℂ) /
            ((n + (k + 1)).factorial : ℂ) * (r₁ * r₂) ^ (k + 1) *
            iteratedDeriv (k + 1) (legendrePolynomialP n) z₁ *
            iteratedDeriv (k + 1) (legendrePolynomialP n) z₂ * cos ((k + 1) * φ) := by
  have hs : (I * r₁) ^ 2 = 1 - z₁ ^ 2 := by rw [mul_pow, I_sq, hr₁]; ring
  have ht : (I * r₂) ^ 2 = 1 - z₂ ^ 2 := by rw [mul_pow, I_sq, hr₂]; ring
  have hp : (I * r₁) * (I * r₂) = -(r₁ * r₂) := by
    calc
      _ = I ^ 2 * (r₁ * r₂) := by ring
      _ = _ := by rw [I_sq]; ring
  have h := legendre_eq_kernel n z₁ z₂ (I * r₁) (I * r₂) φ hs ht
  simp only [kernel, coeff, weight, jet, hp, iteratedDeriv_zero,
    Nat.sub_zero, Nat.add_zero, pow_zero, mul_one] at h
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [div_self hfac, one_mul] at h
  convert h using 1
  · congr 1
    ring
  · congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (-(r₁ * r₂)) ^ (k + 1) =
      (-1 : ℂ) ^ (k + 1) * (r₁ * r₂) ^ (k + 1) from neg_pow _ _]
    ring

end DLMF.Legendre
