/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Sums.LegendreDarboux
public import Mathlib.RingTheory.Binomial

/-!
# Full Darboux coefficients and the convergent-series warning

Olver, *Asymptotics and Special Functions*, Chapter 8, §10,
(10.02)–(10.05), pp. 312–313, synopsis O-8.13. The truncation is indexed
by its final retained term, so m means m+1 terms. The complete convergent
coefficient series sums to twice the Legendre polynomial.
-/

@[expose] public noncomputable section
open Filter Asymptotics
open scoped Topology
namespace DLMF.AsymptoticApproximations.LegendreDarboux

/-- The explicit generalized Darboux term for degree n and local index s.
Olver, Chapter 8, (10.03)–(10.05), pp. 312–313. -/
def term (θ : ℝ) (n s : ℕ) : ℝ :=
  Real.sqrt (2 / Real.sin θ) * Ring.choose (-1 / 2 : ℝ) s *
    Ring.choose ((s : ℝ) - 1 / 2) n *
      Real.cos (((n : ℝ) - s + 1 / 2) * θ +
        ((n : ℝ) - (s : ℝ) / 2 - 1 / 4) * Real.pi) / (2 * Real.sin θ) ^ s

/-- The defining binomial and phase formula for the Darboux coefficient. -/
theorem term_def (θ : ℝ) (n s : ℕ) : term θ n s =
    Real.sqrt (2 / Real.sin θ) * Ring.choose (-1 / 2 : ℝ) s *
      Ring.choose ((s : ℝ) - 1 / 2) n *
        Real.cos (((n : ℝ) - s + 1 / 2) * θ +
          ((n : ℝ) - (s : ℝ) / 2 - 1 / 4) * Real.pi) / (2 * Real.sin θ) ^ s := rfl

/-- The sharp remainder after indices 0 through m, inclusive.
Olver, Chapter 8, (10.03)–(10.04), p. 312. -/
theorem isBigO_legendre_sub_sum_term {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) (m : ℕ) :
    (fun n : ℕ => DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos θ) -
      ((∑ s ∈ Finset.range (m + 1), term θ n s : ℝ) : ℂ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (-(m : ℝ) - 3 / 2)) := by
  sorry

/-- The full generalized series converges to twice the polynomial on its
convergence-angle interval. Olver, Chapter 8, (10.05), p. 313. Thus convergence
of the coefficient series does not identify its sum with the asymptotic target. -/
theorem hasSum_term {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 6) (5 * Real.pi / 6)) (n : ℕ) :
    HasSum (fun s : ℕ => (term θ n s : ℂ))
      (2 * DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos θ)) := by
  sorry

end DLMF.AsymptoticApproximations.LegendreDarboux
