/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Integrals.Coalescing
public import Mathlib.Logic.Function.OfArity
public import Mathlib.Analysis.Analytic.Constructions

/-!
# The cosine-phase endpoint coalescence example

Olver, *Asymptotics and Special Functions*, Chapter 9, §10,
pp. 346–351, synopsis O-9.12. The monotone inverse is defined on both sides
of its saddle. All endpoint derivatives are taken within the physical interval,
so the coalesced case a=0 is included.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace DLMF.AsymptoticApproximations.CosineEndpoint

/-- The cosine phase in Olver, Chapter 9, §10, pp. 346–351. -/
def phase (a θ : ℝ) : ℝ := Real.cos θ + θ * Real.sin a

/-- The endpoint distance of the canonical quadratic saddle. -/
def saddle (a : ℝ) : ℝ := Real.sqrt (2 * (phase a a - 1))

/-- The transformed upper endpoint of the finite cosine integral. -/
def upperEndpoint (a : ℝ) : ℝ :=
  saddle a + Real.sqrt (2 * (phase a a - phase a (Real.pi / 2)))

/-- The two monotone branches of the actual cosine-phase inverse.
Olver, Chapter 9, §10, pp. 346–351. -/
def inverse (a w : ℝ) : ℝ :=
  if w ≤ saddle a then
    Function.invFunOn (phase a) (Icc 0 a) (1 + saddle a * w - w ^ 2 / 2)
  else Function.invFunOn (phase a) (Icc a (Real.pi / 2))
    (1 + saddle a * w - w ^ 2 / 2)

/-- The actual inverse-Jacobian Taylor coefficient, including the one-sided
coalesced endpoint. Olver, Chapter 9, §10. -/
def coefficient (s : ℕ) (a : ℝ) : ℝ :=
  iteratedDerivWithin s (derivWithin (inverse a) (Icc 0 (upperEndpoint a)))
    (Icc 0 (upperEndpoint a)) (saddle a) / s.factorial

/-- The Gaussian moment with its original centered lower endpoint.
Olver, Chapter 9, §10, pp. 346–351. -/
def moment (s : ℕ) (a x : ℝ) : ℝ :=
  ∫ w in Ioi (0 : ℝ), Real.exp (-x * (w - saddle a) ^ 2 / 2) * (w - saddle a) ^ s

/-- The defining cosine phase. -/
theorem phase_def (a θ : ℝ) : phase a θ = Real.cos θ + θ * Real.sin a := rfl

/-- The defining saddle-distance normalization. -/
theorem saddle_def (a : ℝ) : saddle a = Real.sqrt (2 * (phase a a - 1)) := rfl

/-- The defining transformed upper endpoint. -/
theorem upperEndpoint_def (a : ℝ) : upperEndpoint a =
    saddle a + Real.sqrt (2 * (phase a a - phase a (Real.pi / 2))) := rfl

/-- The defining pair of monotone inverse branches. -/
theorem inverse_def (a w : ℝ) : inverse a w =
    if w ≤ saddle a then
      Function.invFunOn (phase a) (Icc 0 a) (1 + saddle a * w - w ^ 2 / 2)
    else Function.invFunOn (phase a) (Icc a (Real.pi / 2))
      (1 + saddle a * w - w ^ 2 / 2) := rfl

/-- The defining derivative coefficient. -/
theorem coefficient_def (s : ℕ) (a : ℝ) : coefficient s a =
    iteratedDerivWithin s (derivWithin (inverse a) (Icc 0 (upperEndpoint a)))
      (Icc 0 (upperEndpoint a)) (saddle a) / s.factorial := rfl

/-- The defining convergent Gaussian moment. -/
theorem moment_def (s : ℕ) (a x : ℝ) : moment s a x =
    ∫ w in Ioi (0 : ℝ), Real.exp (-x * (w - saddle a) ^ 2 / 2) *
      (w - saddle a) ^ s := rfl

/-- The inverse exactly matches the two phases and endpoint/saddle values.
Olver, Chapter 9, §10, pp. 346–351. -/
theorem inverse_spec {a : ℝ} (ha : a ∈ Ico 0 (Real.pi / 2)) :
    StrictMonoOn (inverse a) (Icc 0 (upperEndpoint a)) ∧
      inverse a 0 = 0 ∧ inverse a (saddle a) = a ∧
      inverse a (upperEndpoint a) = Real.pi / 2 ∧
      ∀ w ∈ Icc 0 (upperEndpoint a),
        phase a (inverse a w) = 1 + saddle a * w - w ^ 2 / 2 := by
  sorry

/-- The inverse Jacobian has a convergent Taylor germ, including at the
coalesced saddle. Olver, Chapter 9, §10, pp. 346–351. -/
theorem hasSum_inverse_jacobian {a : ℝ} (ha : a ∈ Ico 0 (Real.pi / 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ Icc 0 (upperEndpoint a), |w - saddle a| < ε →
      HasSum (fun s : ℕ => coefficient s a * (w - saddle a) ^ s)
        (derivWithin (inverse a) (Icc 0 (upperEndpoint a)) w) := by
  sorry

/-- The first three coefficients of the exact inverse Jacobian.
Olver, Chapter 9, §10, pp. 346–351. -/
theorem first_coefficients {a : ℝ} (ha : a ∈ Ico 0 (Real.pi / 2)) :
    coefficient 0 a = (Real.cos a) ^ (-1 / 2 : ℝ) ∧
      coefficient 1 a = Real.sin a / (3 * Real.cos a ^ 2) ∧
      coefficient 2 a = (5 - 2 * Real.cos a ^ 2) /
        (24 * Real.cos a ^ (7 / 2 : ℝ)) := by
  sorry

/-- The moments are the canonical Bleistein moments after Gaussian scaling.
Olver, Chapter 9, §10, pp. 346–351. -/
theorem moment_eq_bleisteinF (s : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    moment s a x = Real.exp (-x * saddle a ^ 2 / 2) *
      x ^ (-((s : ℝ) + 1) / 2) * bleisteinF 1 s (saddle a * Real.sqrt x) := by
  sorry

/-- The full concrete uniform endpoint expansion, including a=0.
Olver, Chapter 9, §10, pp. 346–351. -/
theorem exists_uniform_remainder_le {a₀ : ℝ} (ha₀ : a₀ ∈ Ico 0 (Real.pi / 2))
    (N : ℕ) :
    ∃ C X : ℝ, 0 < C ∧ 0 < X ∧ ∀ a ∈ Icc 0 a₀, ∀ x : ℝ, X ≤ x →
      |(∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (x * phase a θ)) -
        Real.exp (x * phase a a) * ∑ s ∈ Finset.range N, coefficient s a * moment s a x| ≤
          C * Real.exp (x * phase a a) * x ^ (-((N : ℝ) + 1) / 2) := by
  sorry

end DLMF.AsymptoticApproximations.CosineEndpoint
