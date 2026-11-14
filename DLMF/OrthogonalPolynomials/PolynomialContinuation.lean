/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.PolynomialContinuation
public import DLMF.OrthogonalPolynomials.Explicit
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# The Jacobi continuation bridge

The finite binomial formula of Andrews, Askey and Roy, *Special Functions*, §6.3
agrees with the hypergeometric definition on its regular parameter domain.
-/

@[expose] public section

namespace DLMF.OrthogonalPolynomials

open Filter

/-- The polynomially continued Jacobi polynomial agrees with its hypergeometric quotient
when the first parameter has real part greater than `-1`.
Andrews–Askey–Roy, *Special Functions*, §6.3 (synopsis AAR-6.3.1–6.4.3). -/
theorem jacobiExtended_eq_jacobiPolynomialP {α β : ℂ} (hα : -1 < α.re)
    (n : ℕ) (x : ℂ) : jacobiExtended α β n x = jacobiPolynomialP α β n x :=
  (jacobi_binomial_sum hα n x).symm

/-- The endpoint value of the continued Jacobi polynomial, including negative integer
parameters. Andrews–Askey–Roy, *Special Functions*, §6.3
(synopsis AAR-6.3.1–6.4.3); Kristensson, *Second Order Differential Equations*, §5.8. -/
theorem jacobiExtended_one (α β : ℂ) (n : ℕ) :
    jacobiExtended α β n 1 = DLMF.Hypergeometric.pochhammer (α + 1) n / n.factorial := by
  sorry

/-- The negative endpoint value of the polynomial continuation. Andrews–Askey–Roy,
*Special Functions*, §6.3 (synopsis AAR-6.3.1–6.4.3); Kristensson, §5.8. -/
theorem jacobiExtended_neg_one (α β : ℂ) (n : ℕ) :
    jacobiExtended α β n (-1) =
      (-1) ^ n * DLMF.Hypergeometric.pochhammer (β + 1) n / n.factorial := by
  sorry

/-- Reflection interchanges the Jacobi parameters throughout their polynomial continuation.
Andrews–Askey–Roy, *Special Functions*, §6.3 (synopsis AAR-6.3.1–6.4.3);
Kristensson, §5.8. -/
theorem jacobiExtended_neg (α β : ℂ) (n : ℕ) (z : ℂ) :
    jacobiExtended α β n (-z) = (-1) ^ n * jacobiExtended β α n z := by
  sorry

/-- The highest derivative records `n!` times the leading coefficient of the polynomial
continuation, including its degree-degenerate parameters. Andrews–Askey–Roy,
*Special Functions*, §6.3 (synopsis AAR-6.3.1–6.4.3); Kristensson, §5.8. -/
theorem iteratedDeriv_jacobiExtended_self (α β : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (jacobiExtended α β n) z =
      DLMF.Hypergeometric.pochhammer ((n : ℂ) + α + β + 1) n / (2 : ℂ) ^ n := by
  sorry

/-- The denominator-cleared Jacobi recurrence holds at every complex parameter pair.
Andrews–Askey–Roy, *Special Functions*, §6.3 (synopsis AAR-6.3.1–6.4.3);
Kristensson, §5.8. Consecutive indices start at one in the central term. -/
theorem jacobiExtended_recurrence (α β : ℂ) (n : ℕ) (z : ℂ) :
    2 * (n + 2 : ℂ) * (n + α + β + 2) * (2 * n + α + β + 2) *
        jacobiExtended α β (n + 2) z =
      (2 * n + α + β + 3) *
        ((2 * n + α + β + 2) * (2 * n + α + β + 4) * z + α ^ 2 - β ^ 2) *
          jacobiExtended α β (n + 1) z -
        2 * (n + α + 1) * (n + β + 1) * (2 * n + α + β + 4) *
          jacobiExtended α β n z := by
  sorry

/-- Mehler–Heine uniformly on every compact complex set, including exceptional Jacobi
parameters and the zero Bessel argument. Andrews–Askey–Roy, *Special Functions*,
Theorem 4.11.6, p. 220 (synopsis AAR-4.11.1–4.11.8). The regularized `₀F₁` is the
entire normalized Bessel function, so no quotient at zero or pole parameter is totalized. -/
theorem jacobiExtended_mehler_heine_uniform_cos (α β : ℝ) :
    TendstoLocallyUniformly
      (fun (n : ℕ) (z : ℂ) => (Real.rpow (n : ℝ) (-α) : ℂ) *
        jacobiExtended α β n (Complex.cos (z / n)))
      (fun z => Complex.regularizedHGFun ∅ {(α : ℂ) + 1} (-(z ^ 2) / 4))
      atTop := by
  sorry

/-- The polynomial endpoint scaling has the same locally uniform Mehler–Heine limit.
Andrews–Askey–Roy, *Special Functions*, Theorem 4.11.6, p. 220
(synopsis AAR-4.11.1–4.11.8). -/
theorem jacobiExtended_mehler_heine_uniform_quadratic (α β : ℝ) :
    TendstoLocallyUniformly
      (fun (n : ℕ) (z : ℂ) => (Real.rpow (n : ℝ) (-α) : ℂ) *
        jacobiExtended α β n (1 - z ^ 2 / (2 * (n : ℂ) ^ 2)))
      (fun z => Complex.regularizedHGFun ∅ {(α : ℂ) + 1} (-(z ^ 2) / 4))
      atTop := by
  sorry

end DLMF.OrthogonalPolynomials
