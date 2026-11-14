/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.PolynomialContinuation
public import DLMF.OrthogonalPolynomials.Basic.Classical
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Continued Gegenbauer addition and the dimension-two limit

Andrews, Askey and Roy, *Special Functions*, Theorem 9.8.1, pp. 459–463.
The Jacobi coefficient form cancels the apparent singularity at `λ = 1/2`
before specialization and gives the full positive-parameter addition formula.
-/

@[expose] public section

open Filter Finset

namespace DLMF.SphericalHarmonics

open DLMF.OrthogonalPolynomials DLMF.Hypergeometric

/-- Gegenbauer addition with every removable coefficient canceled, valid also at `λ = 1/2`.
Andrews–Askey–Roy, *Special Functions*, Theorem 9.8.1, pp. 459–463
(synopsis AAR-9.6.1–9.8.1). The finite identity holds for arbitrary complex angles
and argument, since each side is polynomial in the trigonometric coordinates. -/
theorem ultrasphericalPolynomial_addition_of_pos {lam : ℝ} (hlam : 0 < lam)
    (m : ℕ) (θ φ t : ℂ) :
    ultrasphericalPolynomial lam m (Complex.cos θ * Complex.cos φ +
      Complex.sin θ * Complex.sin φ * t) =
      m.factorial / pochhammer (2 * lam) m *
        ultrasphericalPolynomial lam m (Complex.cos θ) *
          ultrasphericalPolynomial lam m (Complex.cos φ) +
      ∑ j ∈ Icc 1 m,
        (4 : ℂ) ^ j * (m - j).factorial * pochhammer lam j * (2 * j + 2 * lam - 1) /
          pochhammer (2 * lam + j - 1) (m + 1) *
          (Complex.sin θ * Complex.sin φ) ^ j *
          ultrasphericalPolynomial (lam + j) (m - j) (Complex.cos θ) *
          ultrasphericalPolynomial (lam + j) (m - j) (Complex.cos φ) *
          jacobiExtended (lam - 1) (lam - 1) j t := by
  sorry

/-- The normalized Gegenbauer polynomial tends to the Chebyshev polynomial as the
parameter tends to zero from above. Andrews–Askey–Roy, *Special Functions*,
§§6.7 and 9.8 (synopses AAR-6.7.1–6.7.4 and AAR-9.6.1–9.8.1).
This is the dimension-two interpretation of the normalized zonal harmonic. -/
theorem tendsto_ultrasphericalPolynomial_div_at_one_zero (n : ℕ) (x : ℂ) :
    Tendsto (fun lam : ℝ =>
      ultrasphericalPolynomial lam n x / ultrasphericalPolynomial lam n 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Polynomial.Chebyshev.T ℂ n).eval x)) := by
  sorry

end DLMF.SphericalHarmonics
