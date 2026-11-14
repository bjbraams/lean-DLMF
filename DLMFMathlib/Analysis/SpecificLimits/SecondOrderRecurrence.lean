/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.SpecificLimits.PoincarePerron
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Variable-coefficient second-order recurrence sequences

Continuant determinants, Poincaré–Perron fundamental systems, product normalizations and
power asymptotics from Kristensson, *Second Order Differential Equations*, Appendix B.
The recurrence is `x (n + 2) = A (n + 1) * x (n + 1) + B (n + 1) * x n`.
Initial values are unrestricted unless a theorem explicitly imposes `x 1 = A 0 * x 0`.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators Real Asymptotics

noncomputable section

namespace Complex.SecondOrderRecurrence

/-- Kristensson, Appendix B, p. 179, and Temme, §13.2: arbitrary initial values
uniquely determine a variable-coefficient second-order recurrence solution. -/
theorem existsUnique_solution (A B : ℕ → ℂ) (x₀ x₁ : ℂ) :
    ∃! x : ℕ → ℂ, x 0 = x₀ ∧ x 1 = x₁ ∧
      ∀ n, x (n + 2) = A (n + 1) * x (n + 1) + B (n + 1) * x n := by
  let s : ℕ → ℂ × ℂ := fun n =>
    Nat.rec (x₀, x₁) (fun n v => (v.2, A (n + 1) * v.2 + B (n + 1) * v.1)) n
  refine ⟨fun n => (s n).1, ⟨rfl, rfl, fun _ => rfl⟩, ?_⟩
  intro y hy
  funext n
  induction n using Nat.twoStepInduction with
  | zero => exact hy.1
  | one => exact hy.2.1
  | more n ih ih' => rw [hy.2.2 n, ih, ih']

/-- Kristensson, Appendix B, Lemma B.1: the tridiagonal continuant matrix with diagonal
`A 0, …, A (n - 1)`, superdiagonal `-1`, and subdiagonal `B 1, …, B (n - 1)`. -/
def continuantMatrix (A B : ℕ → ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = j then A i else if j.val = i.val + 1 then -1
    else if i.val = j.val + 1 then B i else 0

/-- The entries of Kristensson's continuant matrix, Appendix B, Lemma B.1. -/
theorem continuantMatrix_apply (A B : ℕ → ℂ) (n : ℕ) (i j : Fin n) :
    continuantMatrix A B n i j =
      if i = j then A i else if j.val = i.val + 1 then -1
        else if i.val = j.val + 1 then B i else 0 := rfl

/-- Kristensson, Appendix B, Lemma B.1: the continuant of order `n`, including `D₀ = 1`. -/
def continuant (A B : ℕ → ℂ) (n : ℕ) : ℂ := (continuantMatrix A B n).det

/-- The determinant defining the continuant, Kristensson, Appendix B, Lemma B.1. -/
theorem continuant_def (A B : ℕ → ℂ) (n : ℕ) :
    continuant A B n = (continuantMatrix A B n).det := rfl

/-- The empty continuant is one, Kristensson, Appendix B, Lemma B.1. -/
@[simp] theorem continuant_zero (A B : ℕ → ℂ) : continuant A B 0 = 1 := by
  simp [continuant]

/-- The first continuant is `A₀`, Kristensson, Appendix B, Lemma B.1. -/
@[simp] theorem continuant_one (A B : ℕ → ℂ) : continuant A B 1 = A 0 := by
  simp [continuant, continuantMatrix]

/-- The continuant recurrence, Kristensson, Appendix B, Lemma B.1, pp. 179–181. -/
theorem continuant_add_two (A B : ℕ → ℂ) (n : ℕ) :
    continuant A B (n + 2) =
      A (n + 1) * continuant A B (n + 1) + B (n + 1) * continuant A B n := by
  sorry

/-- The determinant solution with normalized initial ratio, Kristensson, Appendix B,
Lemma B.1. The statement does not divide by the possibly zero initial value. -/
theorem eq_continuant_mul_initial {A B x : ℕ → ℂ}
    (hrec : ∀ n, x (n + 2) = A (n + 1) * x (n + 1) + B (n + 1) * x n)
    (hinit : x 1 = A 0 * x 0) (n : ℕ) : x n = continuant A B n * x 0 := by
  sorry

/-- Kristensson, Appendix B, Lemma B.2: dividing by the product of the leading
coefficients makes the first recurrence coefficient one. -/
theorem div_prod_recurrence {A B x : ℕ → ℂ}
    (hA : ∀ n, A n ≠ 0)
    (hrec : ∀ n, x (n + 2) = A (n + 1) * x (n + 1) + B (n + 1) * x n)
    (n : ℕ) :
    x (n + 2) / (∏ j ∈ Finset.range (n + 2), A j) =
      x (n + 1) / (∏ j ∈ Finset.range (n + 1), A j) +
        B (n + 1) / (A (n + 1) * A n) *
          (x n / (∏ j ∈ Finset.range n, A j)) := by
  sorry

/-- Kristensson, Appendix B, Theorem B.1: a fundamental pair for distinct characteristic
root moduli. No extra initial-ratio constraint is imposed on these two solutions. -/
theorem exists_fundamental_pair {A B : ℕ → ℂ} {a b r₁ r₂ : ℂ}
    (hA : Tendsto A atTop (𝓝 a)) (hB : Tendsto B atTop (𝓝 b))
    (hBne : ∀ n, B (n + 1) ≠ 0)
    (hsum : r₁ + r₂ = a) (hprod : r₁ * r₂ = -b) (hmod : ‖r₁‖ < ‖r₂‖) :
    ∃ m d : ℕ → ℂ,
      (∀ n, m (n + 2) = A (n + 1) * m (n + 1) + B (n + 1) * m n) ∧
      (∀ n, d (n + 2) = A (n + 1) * d (n + 1) + B (n + 1) * d n) ∧
      m 0 * d 1 - m 1 * d 0 ≠ 0 ∧
      (∀ᶠ n in atTop, m n ≠ 0 ∧ d n ≠ 0) ∧
      Tendsto (fun n => m (n + 1) / m n) atTop (𝓝 r₁) ∧
      Tendsto (fun n => d (n + 1) / d n) atTop (𝓝 r₂) ∧
      Tendsto (fun n => m n / d n) atTop (𝓝 0) := by
  sorry

/-- Kristensson, Appendix B, Theorem B.2: any solution is a unique linear combination
of a pair with nonzero initial Casoratian. -/
theorem existsUnique_linear_combination {A B m d x : ℕ → ℂ}
    (hm : ∀ n, m (n + 2) = A (n + 1) * m (n + 1) + B (n + 1) * m n)
    (hd : ∀ n, d (n + 2) = A (n + 1) * d (n + 1) + B (n + 1) * d n)
    (hx : ∀ n, x (n + 2) = A (n + 1) * x (n + 1) + B (n + 1) * x n)
    (hind : m 0 * d 1 - m 1 * d 0 ≠ 0) :
    ∃! c : ℂ × ℂ, ∀ n, x n = c.1 * d n + c.2 * m n := by
  sorry

/-- Kristensson, Appendix B, Theorem B.2: nonzero dominant contamination determines
the ratio limit. The hypothesis `m/d → 0` explicitly expresses minimality. -/
theorem tendsto_ratio_linear_combination {m d : ℕ → ℂ} {r : ℂ}
    (hd : ∀ᶠ n in atTop, d n ≠ 0)
    (hminimal : Tendsto (fun n => m n / d n) atTop (𝓝 0))
    (hratio : Tendsto (fun n => d (n + 1) / d n) atTop (𝓝 r))
    {α β : ℂ} (hα : α ≠ 0) :
    Tendsto (fun n => (α * d (n + 1) + β * m (n + 1)) /
      (α * d n + β * m n)) atTop (𝓝 r) := by
  sorry

/-- Kristensson, Appendix B, Theorem B.3, corrected: convergence of the tail
continued fraction is equivalent to existence of a minimal solution with nonzero initial
value. Continuants retain intermediate infinite fractions; eventual nonzero denominators
are included to express a finite limit without totalization artifacts. -/
theorem tendsto_continuant_ratio_iff_minimal {A B : ℕ → ℂ}
    (hB : ∀ n, B (n + 1) ≠ 0) (L : ℂ) :
    ((∀ᶠ N in atTop,
        continuant (fun j => A (j + 1)) (fun j => B (j + 1)) (N + 1) ≠ 0) ∧
      Tendsto (fun N => B 1 * continuant (fun j => A (j + 2))
        (fun j => B (j + 2)) N /
          continuant (fun j => A (j + 1)) (fun j => B (j + 1)) (N + 1))
        atTop (𝓝 L)) ↔
    ∃ m d : ℕ → ℂ,
      (∀ n, m (n + 2) = A (n + 1) * m (n + 1) + B (n + 1) * m n) ∧
      (∀ n, d (n + 2) = A (n + 1) * d (n + 1) + B (n + 1) * d n) ∧
      m 0 ≠ 0 ∧ m 0 * d 1 - m 1 * d 0 ≠ 0 ∧
      (∀ᶠ n in atTop, d n ≠ 0) ∧
      Tendsto (fun n => m n / d n) atTop (𝓝 0) ∧ L = -m 1 / m 0 := by
  sorry

/-- Kristensson, Appendix B, Lemma B.3: summably small coefficient defects give a
finite limit, with an explicit algebraic decay order for the error. -/
theorem exists_limit_of_summable_defect {A B x : ℕ → ℂ} {α : ℂ} {lam : ℝ}
    (hα : ‖α‖ < 1) (hlam : 1 < lam)
    (hA : Tendsto A atTop (𝓝 (1 + α))) (hB : Tendsto B atTop (𝓝 (-α)))
    (hdefect : (fun n => A n + B n - 1) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-lam)))
    (hx : ∀ n, x (n + 2) = A (n + 1) * x (n + 1) + B (n + 1) * x n) :
    ∃ d : ℂ, Tendsto x atTop (𝓝 d) ∧
      (fun n => x n - d) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 - lam)) ∧
      Summable (fun n => ‖x (n + 1) - x n‖) := by
  sorry

/-- Kristensson, Appendix B, Lemma B.4: multiplication by a finite product changes
the recurrence coefficients by one or two successive factors. No nonvanishing assumption
on the factors is needed for this forward identity. -/
theorem mul_prod_recurrence {A B x f : ℕ → ℂ}
    (hx : ∀ n, x (n + 2) = A (n + 1) * x (n + 1) + B (n + 1) * x n)
    (n : ℕ) :
    x (n + 2) * (∏ j ∈ Finset.range (n + 2), f (j + 1)) =
      A (n + 1) * f (n + 2) *
        (x (n + 1) * (∏ j ∈ Finset.range (n + 1), f (j + 1))) +
      B (n + 1) * f (n + 2) * f (n + 1) *
        (x n * (∏ j ∈ Finset.range n, f (j + 1))) := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, hx]
  ring

/-- Kristensson, Appendix B, Lemma B.4, corrected initialization: the transformed
initial coefficient is `A₀ f₁`. -/
theorem mul_prod_initial {A x f : ℕ → ℂ} (hx : x 1 = A 0 * x 0) :
    x 1 * f 1 = (A 0 * f 1) * x 0 := by rw [hx]; ring

/-- Kristensson, Appendix B, Lemma B.4: the explicit quadratic normalization
cancels the first two terms of the defect in the sum of recurrence coefficients. -/
theorem normalized_coefficient_sum {A B : ℕ → ℂ} {β₀ β₁ β₂ γ₀ γ₁ γ₂ : ℂ}
    (hne : β₀ + 2 * γ₀ ≠ 0)
    (hA : (fun n => A n - (β₀ + β₁ / n + β₂ / (n : ℂ) ^ 2)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)))
    (hB : (fun n => B n - (γ₀ + γ₁ / n + γ₂ / (n : ℂ) ^ 2)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-3 : ℝ))) :
    let c₁ := -(β₁ + γ₁) / (β₀ + 2 * γ₀)
    let c₂ := (c₁ * (β₀ - 2 * γ₁ - β₁ + γ₀ - c₁ * γ₀) - γ₂ - β₂) /
      (β₀ + 2 * γ₀)
    let f : ℕ → ℂ := fun n => 1 + c₁ / n + c₂ / (n : ℂ) ^ 2
    (fun n => A n * f (n + 1) + B n * f (n + 1) * f n - (β₀ + γ₀))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)) := by
  sorry

/-- Kristensson, Appendix B, Theorem B.4: a solution that does not tend to zero has
the dominant power asymptotic with a first correction term. The power uses positive
integer bases and the principal complex logarithm. -/
theorem exists_power_asymptotic {A B x : ℕ → ℂ} {α β₁ β₂ γ₁ γ₂ : ℂ}
    (hα : ‖α‖ < 1)
    (hA : (fun n => A n - (1 + α + β₁ / n + β₂ / (n : ℂ) ^ 2)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)))
    (hB : (fun n => B n - (-α + γ₁ / n + γ₂ / (n : ℂ) ^ 2)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)))
    (hx : ∀ n, x (n + 2) = A (n + 1) * x (n + 1) + B (n + 1) * x n)
    (hne : ¬Tendsto x atTop (𝓝 0)) :
    ∃ C c : ℂ, C ≠ 0 ∧
      (fun n => x n / (C * (n : ℂ) ^ ((β₁ + γ₁) / (1 - α))) - 1 - c / n)
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
  sorry

/-- Kristensson, Appendix B, Corollary B.1: the ratio expansion of a solution
having the dominant power asymptotic. -/
theorem ratio_power_asymptotic {A B x : ℕ → ℂ} {α β₁ β₂ γ₁ γ₂ : ℂ}
    (hα : ‖α‖ < 1)
    (hA : (fun n => A n - (1 + α + β₁ / n + β₂ / (n : ℂ) ^ 2)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)))
    (hB : (fun n => B n - (-α + γ₁ / n + γ₂ / (n : ℂ) ^ 2)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)))
    (hx : ∀ n, x (n + 2) = A (n + 1) * x (n + 1) + B (n + 1) * x n)
    (hne : ¬Tendsto x atTop (𝓝 0)) :
    (fun n => x (n + 1) / x n - 1 - (β₁ + γ₁) / ((1 - α) * n))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
  sorry

/-- Kristensson, Appendix B, Lemma B.8: a weighted geometric convolution converges
to the geometric-series sum, with error of order `1/n`. -/
theorem weighted_geometric_convolution {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (lam : ℂ) :
    (fun n : ℕ =>
      (∑ k ∈ Finset.Icc 1 n, (c : ℂ) ^ (n - k) * ((n : ℂ) / k) ^ lam) -
        (1 - (c : ℂ))⁻¹) =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  sorry

/-- The exact recurrence of the weighted geometric convolution, with positive
integer bases fixing the complex powers. Kristensson, Appendix B, Lemma B.8,
pp. 197–199. The initial step uses `n>=1`. -/
theorem weighted_geometric_convolution_succ (c : ℝ) (lam : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (∑ k ∈ Finset.Icc 1 (n + 1), (c : ℂ) ^ (n + 1 - k) *
      (((n + 1 : ℕ) : ℂ) / k) ^ lam) =
      1 + (c : ℂ) * (1 + (n : ℂ)⁻¹) ^ lam *
        (∑ k ∈ Finset.Icc 1 n, (c : ℂ) ^ (n - k) * ((n : ℂ) / k) ^ lam) := by
  sorry

/-- The convolution multiplier is eventually a contraction, with a fixed bound
strictly below one. Kristensson, Appendix B, Lemma B.8, pp. 197–199. -/
theorem eventually_norm_weighted_geometric_multiplier_le {c : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (lam : ℂ) :
    ∃ r : ℝ, c < r ∧ r < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ‖(c : ℂ) * (1 + (n : ℂ)⁻¹) ^ lam‖ ≤ r := by
  sorry

/-- Temme, §13.2, (13.1)–(13.3): the Casoratian of two recurrence solutions
multiplies by `-B (n + 1)` at each step. -/
theorem casoratian_add_one {A B f g : ℕ → ℂ}
    (hf : ∀ n, f (n + 2) = A (n + 1) * f (n + 1) + B (n + 1) * f n)
    (hg : ∀ n, g (n + 2) = A (n + 1) * g (n + 1) + B (n + 1) * g n)
    (n : ℕ) :
    f (n + 1) * g (n + 2) - f (n + 2) * g (n + 1) =
      -B (n + 1) * (f n * g (n + 1) - f (n + 1) * g n) := by
  rw [hf, hg]
  ring

/-- Temme, Theorem 13.1, case `α > β/2`: a dominant/minimal pair for power-law
recurrence coefficients. Recurrences and independence are required only on a tail. -/
theorem exists_power_ratio_pair_of_lt {a b : ℕ → ℂ} {a₀ b₀ : ℂ} {α β : ℝ}
    (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0) (hα : β / 2 < α)
    (ha : a ~[atTop] fun n : ℕ => a₀ * (n : ℂ) ^ (α : ℂ))
    (hb : b ~[atTop] fun n : ℕ => b₀ * (n : ℂ) ^ (β : ℂ)) :
    ∃ N : ℕ, ∃ d m : ℕ → ℂ,
      (∀ n, N ≤ n → d (n + 2) + a (n + 1) * d (n + 1) +
        b (n + 1) * d n = 0) ∧
      (∀ n, N ≤ n → m (n + 2) + a (n + 1) * m (n + 1) +
        b (n + 1) * m n = 0) ∧
      d N * m (N + 1) - d (N + 1) * m N ≠ 0 ∧
      (fun n => d (n + 1) / d n) ~[atTop]
        (fun n : ℕ => -a₀ * (n : ℂ) ^ (α : ℂ)) ∧
      (fun n => m (n + 1) / m n) ~[atTop]
        (fun n : ℕ => -(b₀ / a₀) * (n : ℂ) ^ ((β - α : ℝ) : ℂ)) ∧
      Tendsto (fun n => m n / d n) atTop (𝓝 0) := by
  sorry

/-- Temme, Theorem 13.1, case `α = β/2` with unequal root moduli: the two ratio
asymptotics and minimality for coefficients of the same characteristic scale. -/
theorem exists_power_ratio_pair_of_root_gap {a b : ℕ → ℂ} {a₀ b₀ r₁ r₂ : ℂ} {α : ℝ}
    (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0)
    (ha : a ~[atTop] fun n : ℕ => a₀ * (n : ℂ) ^ (α : ℂ))
    (hb : b ~[atTop] fun n : ℕ => b₀ * (n : ℂ) ^ ((2 * α : ℝ) : ℂ))
    (hsum : r₁ + r₂ = -a₀) (hprod : r₁ * r₂ = b₀) (hmod : ‖r₂‖ < ‖r₁‖) :
    ∃ N : ℕ, ∃ d m : ℕ → ℂ,
      (∀ n, N ≤ n → d (n + 2) + a (n + 1) * d (n + 1) +
        b (n + 1) * d n = 0) ∧
      (∀ n, N ≤ n → m (n + 2) + a (n + 1) * m (n + 1) +
        b (n + 1) * m n = 0) ∧
      d N * m (N + 1) - d (N + 1) * m N ≠ 0 ∧
      (fun n => d (n + 1) / d n) ~[atTop]
        (fun n : ℕ => r₁ * (n : ℂ) ^ (α : ℂ)) ∧
      (fun n => m (n + 1) / m n) ~[atTop]
        (fun n : ℕ => r₂ * (n : ℂ) ^ (α : ℂ)) ∧
      Tendsto (fun n => m n / d n) atTop (𝓝 0) := by
  sorry

/-- Temme, Theorem 13.1: equal-modulus characteristic roots determine the
factorially normalized upper exponential growth rate of every nontrivial tail solution. -/
theorem limsup_factorial_normalized_of_equal_root_moduli
    {a b x : ℕ → ℂ} {a₀ b₀ r₁ r₂ : ℂ} {α : ℝ}
    (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0)
    (ha : a ~[atTop] fun n : ℕ => a₀ * (n : ℂ) ^ (α : ℂ))
    (hb : b ~[atTop] fun n : ℕ => b₀ * (n : ℂ) ^ ((2 * α : ℝ) : ℂ))
    (hsum : r₁ + r₂ = -a₀) (hprod : r₁ * r₂ = b₀) (hmod : ‖r₁‖ = ‖r₂‖)
    (hx : ∀ᶠ n in atTop, x (n + 2) + a (n + 1) * x (n + 1) +
      b (n + 1) * x n = 0) (hne : ∃ᶠ n in atTop, x n ≠ 0) :
    limsup (fun n : ℕ => (‖x n‖ * (n.factorial : ℝ) ^ (-α)) ^ ((n : ℝ)⁻¹))
      atTop = ‖r₁‖ := by
  sorry

/-- Temme, Theorem 13.1, case `α < β/2`: the upper exponential growth rate after
factorial normalization is `√‖b₀‖`. -/
theorem limsup_factorial_normalized_of_lt {a b x : ℕ → ℂ}
    {a₀ b₀ : ℂ} {α β : ℝ} (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0) (hα : α < β / 2)
    (ha : a ~[atTop] fun n : ℕ => a₀ * (n : ℂ) ^ (α : ℂ))
    (hb : b ~[atTop] fun n : ℕ => b₀ * (n : ℂ) ^ (β : ℂ))
    (hx : ∀ᶠ n in atTop, x (n + 2) + a (n + 1) * x (n + 1) +
      b (n + 1) * x n = 0) (hne : ∃ᶠ n in atTop, x n ≠ 0) :
    limsup (fun n : ℕ => (‖x n‖ * (n.factorial : ℝ) ^ (-β / 2)) ^ ((n : ℝ)⁻¹))
      atTop = Real.sqrt ‖b₀‖ := by
  sorry

/-- Temme, §13.4, (13.4)–(13.10): Miller's approximation formed from a
minimal/dominant pair and a weighted normalization. Divisions are totalized. -/
def millerApproximation (f g weight : ℕ → ℂ) (s : ℂ) (N n : ℕ) : ℂ :=
  s * (f n - f (N + 1) / g (N + 1) * g n) /
    ∑ j ∈ Finset.range (N + 1), weight j * (f j - f (N + 1) / g (N + 1) * g j)

/-- The defining finite-sum formula for Miller's normalized approximation,
Temme, §13.4, (13.4)–(13.10). -/
theorem millerApproximation_def (f g weight : ℕ → ℂ) (s : ℂ) (N n : ℕ) :
    millerApproximation f g weight s N n =
      s * (f n - f (N + 1) / g (N + 1) * g n) /
        ∑ j ∈ Finset.range (N + 1), weight j *
          (f j - f (N + 1) / g (N + 1) * g j) := rfl

/-- Temme, §13.4, (13.4)–(13.10): convergence of Miller's approximation requires
the weighted dominant contamination to vanish in addition to minimality. -/
theorem tendsto_millerApproximation {f g weight : ℕ → ℂ} {s : ℂ}
    (hs : s ≠ 0) (hf : HasSum (fun n => weight n * f n) s)
    (hminimal : Tendsto (fun n => f n / g n) atTop (𝓝 0))
    (hcontamination : Tendsto (fun N => f (N + 1) / g (N + 1) *
      ∑ j ∈ Finset.range (N + 1), weight j * g j) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun N => millerApproximation f g weight s N n) atTop (𝓝 (f n)) := by
  sorry

/-- Temme, (13.11)–(13.13): the exact relative-error identity in Miller's method,
with the omitted tail supplied by a convergent normalization series. -/
theorem millerApproximation_relative_error {f g weight : ℕ → ℂ} {s : ℂ}
    (hs : s ≠ 0) (N n : ℕ)
    (hfn : f n ≠ 0)
    (hden : 1 - (s - ∑ j ∈ Finset.range (N + 1), weight j * f j) / s -
      (f (N + 1) / g (N + 1) * ∑ j ∈ Finset.range (N + 1), weight j * g j) / s ≠ 0) :
    (millerApproximation f g weight s N n - f n) / f n =
      (((s - ∑ j ∈ Finset.range (N + 1), weight j * f j) / s) +
        (f (N + 1) / g (N + 1) * ∑ j ∈ Finset.range (N + 1), weight j * g j) / s -
        f (N + 1) / g (N + 1) * g n / f n) /
      (1 - (s - ∑ j ∈ Finset.range (N + 1), weight j * f j) / s -
        (f (N + 1) / g (N + 1) * ∑ j ∈ Finset.range (N + 1), weight j * g j) / s) := by
  sorry

/-- Temme, (13.13): a certified relative-error bound from normalization-tail and
dominant-contamination bounds. -/
theorem norm_relative_error_le {σ τ ε : ℂ} (h : ‖σ‖ + ‖τ‖ < 1) :
    ‖(σ + τ - ε) / (1 - σ - τ)‖ ≤
      (‖σ‖ + ‖τ‖ + ‖ε‖) / (1 - ‖σ‖ - ‖τ‖) := by
  sorry

end Complex.SecondOrderRecurrence
