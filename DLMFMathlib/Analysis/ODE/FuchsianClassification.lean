/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.Singularities
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Classification of rational second-order Fuchsian equations

The partial fractions, moment constraints at infinity and exponent relation in
Kristensson, *Second Order Differential Equations*, Chapters 3–4. Ordinary marked
points are allowed: all regularity statements use `LinearODEAtMostRegularAt`.
The coefficient vector `![q, p]` represents `u″ + p u′ + q u = 0`.
-/

@[expose] public section

open Filter Set
open scoped Topology BigOperators

noncomputable section

namespace Complex

/-- A scalar linear differential equation is Fuchsian on the Riemann sphere if
all finite points and infinity are at most regular. Ordinary points are included.
Kristensson, Chapter 3, §3.1, pp. 29–31. -/
def LinearODEFuchsian {n : ℕ} (c : Fin n → ℂ → ℂ) : Prop :=
  (∀ z : ℂ, LinearODEAtMostRegularAt c z) ∧ LinearODEAtMostRegularAtInfinity c

/-- The pointwise regularity characterization of a Fuchsian equation. -/
theorem linearODEFuchsian_iff {n : ℕ} (c : Fin n → ℂ → ℂ) :
    LinearODEFuchsian c ↔
      (∀ z : ℂ, LinearODEAtMostRegularAt c z) ∧ LinearODEAtMostRegularAtInfinity c :=
  Iff.rfl

/-- Construct Fuchsian data from regularity at every finite point and infinity. -/
theorem LinearODEFuchsian.mk {n : ℕ} {c : Fin n → ℂ → ℂ}
    (hfinite : ∀ z : ℂ, LinearODEAtMostRegularAt c z)
    (hinfty : LinearODEAtMostRegularAtInfinity c) : LinearODEFuchsian c := ⟨hfinite, hinfty⟩

/-- A Fuchsian equation is at most regular at each finite point. -/
theorem LinearODEFuchsian.at {n : ℕ} {c : Fin n → ℂ → ℂ}
    (h : LinearODEFuchsian c) (z : ℂ) : LinearODEAtMostRegularAt c z := h.1 z

/-- A Fuchsian equation is at most regular at infinity. -/
theorem LinearODEFuchsian.atInfinity {n : ℕ} {c : Fin n → ℂ → ℂ}
    (h : LinearODEFuchsian c) : LinearODEAtMostRegularAtInfinity c := h.2


/-- Kristensson, Theorem 3.1, pp. 31–32: the partial-fraction coefficients have at
most regular singularities at all finite points, including removable marked points. -/
theorem linearODEAtMostRegularAt_partial_fractions {n : ℕ}
    (a α β f : Fin n → ℂ) (z₀ : ℂ) :
    LinearODEAtMostRegularAt
      ![fun z => (∑ j, α j * β j / (z - a j) ^ 2) + ∑ j, f j / (z - a j),
        fun z => ∑ j, (1 - α j - β j) / (z - a j)] z₀ := by
  sorry

/-- Kristensson, Theorem 3.1, p. 32: infinity is at most regular precisely when the
sum of the simple-pole residues of the zeroth-order coefficient vanishes. -/
theorem linearODEAtMostRegularAtInfinity_partial_fractions_iff {n : ℕ}
    (a α β f : Fin n → ℂ) :
    LinearODEAtMostRegularAtInfinity
      ![fun z => (∑ j, α j * β j / (z - a j) ^ 2) + ∑ j, f j / (z - a j),
        fun z => ∑ j, (1 - α j - β j) / (z - a j)] ↔ ∑ j, f j = 0 := by
  sorry

/-- Kristensson, Theorem 3.2, pp. 34–35: the four moment constraints characterizing
ordinary infinity. The formula allows coincident marked points and zero residues. -/
theorem linearODEOrdinaryAtInfinity_partial_fractions_iff {n : ℕ}
    (a α β f : Fin n → ℂ) :
    LinearODEOrdinaryAtInfinity
      ![fun z => (∑ j, α j * β j / (z - a j) ^ 2) + ∑ j, f j / (z - a j),
        fun z => ∑ j, (1 - α j - β j) / (z - a j)] ↔
      (∑ j, (α j + β j)) = (n : ℂ) - 2 ∧ (∑ j, f j) = 0 ∧
      (∑ j, α j * β j) + (∑ j, a j * f j) = 0 ∧
      2 * (∑ j, a j * α j * β j) + (∑ j, a j ^ 2 * f j) = 0 := by
  sorry

/-- Kristensson, Theorem 3.1, p. 32: the weighted transformed coefficients at zero
extend analytically, with values giving the indicial polynomial at infinity. -/
theorem exists_analytic_reciprocal_partial_fractions {n : ℕ}
    (a α β f : Fin n → ℂ) (hf : ∑ j, f j = 0) :
    ∃ P Q : ℂ → ℂ, AnalyticAt ℂ P 0 ∧ AnalyticAt ℂ Q 0 ∧
      (fun t => 2 - (∑ j, (1 - α j - β j) / (t⁻¹ - a j)) / t)
        =ᶠ[𝓝[≠] 0] P ∧
      (fun t => ((∑ j, α j * β j / (t⁻¹ - a j) ^ 2) +
        ∑ j, f j / (t⁻¹ - a j)) / t ^ 2) =ᶠ[𝓝[≠] 0] Q ∧
      P 0 = 2 - ∑ j, (1 - α j - β j) ∧
      Q 0 = (∑ j, α j * β j) + ∑ j, a j * f j := by
  sorry

/-- Kristensson, Theorem 3.1 and Comment 3.1, pp. 32, 36: the Fuchs relation for
the finite exponent pairs and the exponent pair at infinity. -/
theorem fuchs_relation_of_infinity_indicial {n : ℕ} (α β : Fin n → ℂ)
    {r s : ℂ} (hsum : r + s = (∑ j, (1 - α j - β j)) - 1) :
    r + s + (∑ j, (α j + β j)) = (n : ℂ) - 1 := by
  rw [hsum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- Kristensson, §3.1, pp. 29–32: coefficients ordinary away from finitely many
marked points and at most regular there and at infinity have these partial fractions. -/
theorem exists_partial_fractions_of_linearODEAtMostRegularAtInfinity {n : ℕ}
    (a : Fin n → ℂ) (ha : Function.Injective a) (p q : ℂ → ℂ)
    (hp : AnalyticOnNhd ℂ p (Set.range a)ᶜ)
    (hq : AnalyticOnNhd ℂ q (Set.range a)ᶜ)
    (hfinite : ∀ j, LinearODEAtMostRegularAt ![q, p] (a j))
    (hinfty : LinearODEAtMostRegularAtInfinity ![q, p]) :
    ∃ b c f : Fin n → ℂ, (∑ j, f j) = 0 ∧
      ∀ z, z ∉ Set.range a →
        p z = (∑ j, b j / (z - a j)) ∧
        q z = (∑ j, c j / (z - a j) ^ 2) + ∑ j, f j / (z - a j) := by
  sorry

/-- Kristensson, §4.1, p. 43: a normalized scalar second-order equation cannot
have ordinary coefficients everywhere on the Riemann sphere. -/
theorem not_linearODEOrdinaryAt_everywhere_and_infinity (p q : ℂ → ℂ) :
    ¬((∀ z, LinearODEOrdinaryAt ![q, p] z) ∧ LinearODEOrdinaryAtInfinity ![q, p]) := by
  sorry

/-- Kristensson, §4.1, pp. 43–44: an equation ordinary at all finite points and
at most regular at infinity has both coefficient germs identically zero. Pointwise
analyticity excludes arbitrary exceptional totalizations. -/
theorem eq_zero_of_entire_linearODEAtMostRegularAtInfinity {p q : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (hinfty : LinearODEAtMostRegularAtInfinity ![q, p]) : p = 0 ∧ q = 0 := by
  sorry

/-- Kristensson, Theorem 3.3, pp. 36–37, with removable points allowed: shifting
the exponent pairs by a logarithmic-derivative gauge preserves at most regular behavior. -/
theorem linearODEAtMostRegularAt_gauge_partial_fractions {n : ℕ}
    (a ρ : Fin n → ℂ) (p q : ℂ → ℂ) (z₀ : ℂ)
    (hregular : LinearODEAtMostRegularAt ![q, p] z₀) :
    LinearODEAtMostRegularAt
      ![fun z => q z + p z * (∑ j, ρ j / (z - a j)) -
          (∑ j, ρ j / (z - a j) ^ 2) + (∑ j, ρ j / (z - a j)) ^ 2,
        fun z => p z + 2 * ∑ j, ρ j / (z - a j)] z₀ := by
  sorry


/-- The finite weighted coefficients have the prescribed indicial values at each
marked point, with the singular values interpreted by analytic germs. Kristensson,
Chapter 3, Theorem 3.1, p. 32. -/
theorem exists_analytic_weighted_partial_fractions_at {n : ℕ}
    (a α β f : Fin n → ℂ) (ha : Function.Injective a) (i : Fin n) :
    ∃ P Q : ℂ → ℂ, AnalyticAt ℂ P (a i) ∧ AnalyticAt ℂ Q (a i) ∧
      (fun z => (z - a i) * ∑ j, (1 - α j - β j) / (z - a j))
        =ᶠ[𝓝[≠] a i] P ∧
      (fun z => (z - a i) ^ 2 *
        ((∑ j, α j * β j / (z - a j) ^ 2) + ∑ j, f j / (z - a j)))
        =ᶠ[𝓝[≠] a i] Q ∧
      P (a i) = 1 - α i - β i ∧ Q (a i) = α i * β i := by
  sorry

/-- For rational Fuchsian coefficients, ordinary infinity is equivalently the two
explicit asymptotic order conditions. Kristensson, Chapter 3, Theorem 3.2,
pp. 34–35. Analyticity of the rational germs is essential for the converse. -/
theorem linearODEOrdinaryAtInfinity_partial_fractions_iff_isBigO {n : ℕ}
    (a α β f : Fin n → ℂ) :
    let p := fun z => ∑ j, (1 - α j - β j) / (z - a j)
    let q := fun z => (∑ j, α j * β j / (z - a j) ^ 2) + ∑ j, f j / (z - a j)
    LinearODEOrdinaryAtInfinity ![q, p] ↔
      Asymptotics.IsBigO (comap (fun z : ℂ => ‖z‖) atTop)
        (fun z : ℂ => p z - 2 / z) (fun z : ℂ => z ^ (-2 : ℤ)) ∧
      Asymptotics.IsBigO (comap (fun z : ℂ => ‖z‖) atTop)
        q (fun z : ℂ => z ^ (-4 : ℤ)) := by
  sorry

/-- A power gauge shifts every finite indicial root by minus its local exponent.
At infinity the same identity uses minus the total gauge exponent, giving the
opposite root shift. Kristensson, Chapter 3, Theorem 3.3, pp. 36–37. -/
theorem indicial_gauge_shift (p q ρ r : ℂ) :
    r * (r - 1) + (p + 2 * ρ) * r + q + ρ * p + ρ * (ρ - 1) =
      (r + ρ) * (r + ρ - 1) + p * (r + ρ) + q := by
  ring


/-- Three finite regular singularities with ordinary infinity are uniquely determined
by their exponent pairs: the coefficient is Papperitz's cyclic rational formula.
Kristensson, Chapter 4, (4.4), pp. 50–51; Olver, Chapter 5, Theorem 8.1,
pp. 156–158. Pointwise analyticity off the marked points excludes arbitrary
exceptional totalizations there. -/
theorem eq_papperitz_coefficients_of_regularSingular
    (a α β : Fin 3 → ℂ) (ha : Function.Injective a) {p q : ℂ → ℂ}
    (hp : AnalyticOnNhd ℂ p (Set.range a)ᶜ)
    (hq : AnalyticOnNhd ℂ q (Set.range a)ᶜ)
    (hlocal : ∀ i : Fin 3, ∃ P Q : ℂ → ℂ,
      AnalyticAt ℂ P (a i) ∧ AnalyticAt ℂ Q (a i) ∧
      (fun z => (z - a i) * p z) =ᶠ[𝓝[≠] a i] P ∧
      (fun z => (z - a i) ^ 2 * q z) =ᶠ[𝓝[≠] a i] Q ∧
      P (a i) = 1 - α i - β i ∧ Q (a i) = α i * β i)
    (hinfty : LinearODEOrdinaryAtInfinity ![q, p]) :
    (∑ i, (α i + β i)) = 1 ∧
      ∀ z, z ∉ Set.range a →
        p z = (∑ i, (1 - α i - β i) / (z - a i)) ∧
        q z = (∑ i : Fin 3,
          α i * β i * (a i - a (i + 1)) * (a i - a (i + 2)) / (z - a i)) /
            ∏ i, (z - a i) := by
  sorry

end Complex
