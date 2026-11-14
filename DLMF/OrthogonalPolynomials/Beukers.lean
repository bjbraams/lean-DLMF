/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Topics
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Beukers integrals and integer linear forms in zeta of three

The supporting lemmas of Andrews, Askey and Roy, *Special Functions*, §7.7.
The final irrationality statement is already `irrational_riemannZeta_three`.
-/

@[expose] public section

open Finset Filter MeasureTheory
open scoped Topology Real

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- The monomial double integral on the diagonal. Andrews–Askey–Roy,
*Special Functions*, Lemma 7.7.3 (synopsis AAR-7.7.1–7.7.5). -/
theorem integral_beukers_kernel_diagonal (r : ℕ) :
    (∫ x : ℝ in Set.Ioo 0 1, ∫ y : ℝ in Set.Ioo 0 1,
      -Real.log (x * y) / (1 - x * y) * x ^ r * y ^ r) =
      2 * ((riemannZeta 3).re - ∑ k ∈ Finset.Icc 1 r, (k : ℝ)⁻¹ ^ 3) := by
  sorry

/-- The off-diagonal monomial integral and its exact rational value.
Andrews–Askey–Roy, *Special Functions*, Lemma 7.7.3
(synopsis AAR-7.7.1–7.7.5). -/
theorem integral_beukers_kernel_off_diagonal {r s : ℕ} (hrs : s < r) :
    (∫ x : ℝ in Set.Ioo 0 1, ∫ y : ℝ in Set.Ioo 0 1,
      -Real.log (x * y) / (1 - x * y) * x ^ r * y ^ s) =
      (r - s : ℝ)⁻¹ * ∑ j ∈ Finset.Icc (s + 1) r, (j : ℝ)⁻¹ ^ 2 := by
  sorry

/-- Integration by parts turns the shifted Legendre double integral into a positive
triple integral. Andrews–Askey–Roy, *Special Functions*, Lemmas 7.7.4–7.7.5
(synopsis AAR-7.7.1–7.7.5). -/
theorem integral_beukers_eq_triple (n : ℕ) :
    (∫ x : ℝ in Set.Ioo 0 1, ∫ y : ℝ in Set.Ioo 0 1,
      -Real.log (x * y) / (1 - x * y) *
        (legendrePolynomialP n (1 - 2 * x)).re *
        (legendrePolynomialP n (1 - 2 * y)).re) =
      ∫ x : ℝ in Set.Ioo 0 1, ∫ y : ℝ in Set.Ioo 0 1, ∫ z : ℝ in Set.Ioo 0 1,
        (x * (1 - x) * y * (1 - y) * z * (1 - z)) ^ n /
          (1 - (1 - x * y) * z) ^ (n + 1) := by
  sorry

/-- The sharp elementary bound on the quotient in Beukers's triple integral.
Andrews–Askey–Roy, *Special Functions*, proof of Lemma 7.7.5
(synopsis AAR-7.7.1–7.7.5). -/
theorem beukers_quotient_le {x y z : ℝ} (hx : x ∈ Set.Icc 0 1)
    (hy : y ∈ Set.Icc 0 1) (hz : z ∈ Set.Icc 0 1) :
    x * (1 - x) * y * (1 - y) * z * (1 - z) /
      (1 - (1 - x * y) * z) ≤ (Real.sqrt 2 - 1) ^ 4 := by
  sorry

/-- Beukers's integrals are nonzero integer linear forms divided by `lcm(1,...,n)^3`,
with a geometric bound. Andrews–Askey–Roy, *Special Functions*, Lemmas 7.7.4–7.7.5
(synopsis AAR-7.7.1–7.7.5). -/
theorem exists_integer_linear_form_beukers {n : ℕ} (hn : 0 < n) :
    ∃ A B : ℤ,
      (∫ x : ℝ in Set.Ioo 0 1, ∫ y : ℝ in Set.Ioo 0 1,
        -Real.log (x * y) / (1 - x * y) *
          (legendrePolynomialP n (1 - 2 * x)).re *
          (legendrePolynomialP n (1 - 2 * y)).re) =
        ((A : ℝ) + B * (riemannZeta 3).re) / (Nat.lcmUpto n : ℝ) ^ 3 ∧
      0 < |(A : ℝ) + B * (riemannZeta 3).re| ∧
      |(A : ℝ) + B * (riemannZeta 3).re| / (Nat.lcmUpto n : ℝ) ^ 3 <
        2 * (Real.sqrt 2 - 1) ^ (4 * n) * (riemannZeta 3).re := by
  sorry

/-- Arbitrarily small nonzero integer linear forms with an explicit geometric bound.
Andrews–Askey–Roy, *Special Functions*, Lemma 7.7.1
(synopsis AAR-7.7.1–7.7.5). -/
theorem exists_integer_linear_form_zeta_three_geometric (n : ℕ) :
    ∃ A B : ℤ, 0 < |(A : ℝ) + B * (riemannZeta 3).re| ∧
      |(A : ℝ) + B * (riemannZeta 3).re| ≤ 3 * (9 / 10 : ℝ) ^ n := by
  sorry

end DLMF.OrthogonalPolynomials
