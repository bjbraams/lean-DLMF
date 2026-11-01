/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Definitions
public import DLMF.Elliptic.Basic.ThetaPeriodicity

/-!
# Jacobian elliptic functions: Glaisher's relations and parity (DLMF §22.2)

Glaisher's relations between the twelve Jacobian elliptic functions and their parity in `z`,
for all complex `z` and `k`, from the theta-quotient definitions.

## Main results

* `jacobiPQk_eq_one_div`, `jacobiPQk_eq_div`, `jacobiPQk_self`: Glaisher's relations
  `pq = 1/qp`, `pq = pr/qr` and `pp = 1` (DLMF 22.2.10).
* `jacobiZetak_neg`, `jacobiLetterTheta_neg`: `ζ = πz/(2K)` is odd in `z`; `θ_s` is odd and
  `θ_c, θ_d, θ_n` are even.
* `jacobiPQk_neg`: the six functions whose name contains `s` are odd, the others even.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-- Glaisher's reciprocal relation `pq = 1/qp` (DLMF 22.2.10, and the second equalities of
22.2.4–22.2.9). It holds identically, including Lean's junk values at poles. -/
@[dlmf 22.2.E10, dlmf 22.2.E4, dlmf 22.2.E5, dlmf 22.2.E6, dlmf 22.2.E7, dlmf 22.2.E8,
  dlmf 22.2.E9]
theorem jacobiPQk_eq_one_div (p q : JacobiLetter) (z k : ℂ) :
    jacobiPQk p q z k = 1 / jacobiPQk q p z k := by
  unfold jacobiPQk jacobiGlaisher
  by_cases hpq : p = q
  · subst hpq; simp
  · simp only [hpq, Ne.symm hpq, ↓reduceIte, one_div_div]

/-- Glaisher's quotient relation `pq = pr/qr` (DLMF 22.2.10) for three distinct letters, at
points where the `·r` functions are finite. -/
@[dlmf 22.2.E10]
theorem jacobiPQk_eq_div {p q r : JacobiLetter} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {z k : ℂ} (hr : JacobiRegulark r z k) :
    jacobiPQk p q z k = jacobiPQk p r z k / jacobiPQk q r z k := by
  unfold jacobiPQk jacobiGlaisher
  simp only [hpq, hpr, hqr, ↓reduceIte]
  rw [div_div_div_cancel_right₀ hr]

/-- The convention `pp = 1` (DLMF 22.2.10). -/
@[dlmf 22.2.E10]
theorem jacobiPQk_self (p : JacobiLetter) (z k : ℂ) : jacobiPQk p p z k = 1 := by
  simp [jacobiPQk, jacobiGlaisher]

/-- `ζ = πz/(2K)` is odd in `z`. -/
theorem jacobiZetak_neg (z k : ℂ) : jacobiZetak (-z) k = -jacobiZetak z k := by
  simp only [jacobiZetak]; ring

/-- The normalized theta functions: `θ_s` is odd, `θ_c, θ_d, θ_n` are even. -/
theorem jacobiLetterTheta_neg (p : JacobiLetter) (ζ τ : ℂ) :
    jacobiLetterTheta p (-ζ) τ = (if p = .s then -1 else 1) * jacobiLetterTheta p ζ τ := by
  cases p <;> simp [jacobiLetterTheta, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg]

/-- Parity (DLMF §22.2): the six functions whose name contains the letter `s` are odd in `z`;
the other six are even. Holds for all `z` and `k`. -/
@[dlmf 22.2]
theorem jacobiPQk_neg (p q : JacobiLetter) (z k : ℂ) :
    jacobiPQk p q (-z) k =
      (if (p = .s) ≠ (q = .s) then -jacobiPQk p q z k else jacobiPQk p q z k) := by
  unfold jacobiPQk jacobiGlaisher
  rw [jacobiZetak_neg]
  by_cases hpq : p = q
  · subst hpq; simp
  · simp only [hpq, ↓reduceIte, jacobiLetterTheta_neg]
    cases p <;> cases q <;> simp_all <;> ring

end DLMF.JacobiElliptic

end
end
