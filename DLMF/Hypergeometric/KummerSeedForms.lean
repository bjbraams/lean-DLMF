/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.Basic.GaussEquation
public import DLMF.Hypergeometric.KummerPermutations

/-!
# The literal six-seed Kummer generator

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), table 3.1,
(3.4), (3.12)–(3.13), pp. 3-2–3-6, synopsis RL-3.03. The ordinary normalization
requires a regular lower parameter. At exceptional lower parameters this auxiliary
family is the whole regularized continuation times Gamma, not independently truncated
finite expressions. The infinity seeds use `(-z)^(-a)`, normalized on negative real z.
-/

@[expose] public noncomputable section

open Complex Set

namespace DLMF.Hypergeometric.KummerSeedForms

/-- The six source upper/lower parameter triples, in their printed seed order.
Rao–Lakshminarayanan table 3.1, synopsis RL-3.03. -/
def parameters (a b c : ℂ) : Fin 6 → ℂ × ℂ × ℂ :=
  ![(a, b, c), (a - c + 1, b - c + 1, 2 - c),
    (a, b, a + b - c + 1), (c - a, c - b, c - a - b + 1),
    (a, a - c + 1, a - b + 1), (b, b - c + 1, b - a + 1)]

/-- The literal argument of each seed.
Rao–Lakshminarayanan table 3.1, synopsis RL-3.03. -/
def argument (i : Fin 6) (z : ℂ) : ℂ :=
  if i.val < 2 then z else if i.val < 4 then 1 - z else 1 / z

/-- The literal source prefactors, including the negative-axis infinity normalization.
Rao–Lakshminarayanan table 3.1, synopsis RL-3.03. -/
def prefactor (a b c z : ℂ) : Fin 6 → ℂ :=
  ![1, z ^ (1 - c), 1, (1 - z) ^ (c - a - b), (-z) ^ (-a), (-z) ^ (-b)]

/-- The four Euler/Pfaff forms of a regularized Gauss function.
Rao–Lakshminarayanan (3.4), synopsis RL-3.03. -/
def fourForms (A B C u : ℂ) : Fin 4 → ℂ :=
  ![regularizedGaussHypergeometric A B C u,
    (1 - u) ^ (-A) * regularizedGaussHypergeometric A (C - B) C (u / (u - 1)),
    (1 - u) ^ (-B) * regularizedGaussHypergeometric (C - A) B C (u / (u - 1)),
    (1 - u) ^ (C - A - B) * regularizedGaussHypergeometric (C - A) (C - B) C u]

/-- The twenty-four literal seed expressions, with ordinary Gamma normalization at
regular lower parameters. Rao–Lakshminarayanan table 3.1, synopsis RL-3.03. -/
def expression (a b c : ℂ) (i : Fin 6) (j : Fin 4) (z : ℂ) : ℂ :=
  let p := parameters a b c i
  prefactor a b c z i * Gamma p.2.2 * fourForms p.1 p.2.1 p.2.2 (argument i z) j

/-- The explicit common principal domain of the source seed and its four forms.
The infinity domain contains the negative real axis. Rao–Lakshminarayanan table 3.1,
synopsis RL-3.03. -/
def domain (i : Fin 6) : Set ℂ :=
  {z | z ≠ 0 ∧ z ≠ 1 ∧ argument i z ∈ cutPlane ∧
    (i = 1 → z ∈ slitPlane) ∧ (i = 3 → 1 - z ∈ slitPlane) ∧
      (4 ≤ i.val → -z ∈ slitPlane)}

/-- The defining six parameter triples. -/
theorem parameters_def (a b c : ℂ) : parameters a b c =
    ![(a, b, c), (a - c + 1, b - c + 1, 2 - c),
      (a, b, a + b - c + 1), (c - a, c - b, c - a - b + 1),
      (a, a - c + 1, a - b + 1), (b, b - c + 1, b - a + 1)] := rfl

/-- The defining seed argument. -/
theorem argument_def (i : Fin 6) (z : ℂ) :
    argument i z = if i.val < 2 then z else if i.val < 4 then 1 - z else 1 / z := rfl

/-- The defining six prefactors with their specified principal branches. -/
theorem prefactor_def (a b c z : ℂ) : prefactor a b c z =
    ![1, z ^ (1 - c), 1, (1 - z) ^ (c - a - b), (-z) ^ (-a), (-z) ^ (-b)] := rfl

/-- The defining four regularized transformation forms. -/
theorem fourForms_def (A B C u : ℂ) : fourForms A B C u =
    ![regularizedGaussHypergeometric A B C u,
      (1 - u) ^ (-A) * regularizedGaussHypergeometric A (C - B) C (u / (u - 1)),
      (1 - u) ^ (-B) * regularizedGaussHypergeometric (C - A) B C (u / (u - 1)),
      (1 - u) ^ (C - A - B) * regularizedGaussHypergeometric (C - A) (C - B) C u] := rfl

/-- The defining Gamma-normalized literal seed expression. -/
theorem expression_def (a b c : ℂ) (i : Fin 6) (j : Fin 4) (z : ℂ) :
    expression a b c i j z =
      let p := parameters a b c i
      prefactor a b c z i * Gamma p.2.2 *
        fourForms p.1 p.2.1 p.2.2 (argument i z) j := rfl

/-- The defining branch-domain conditions. -/
theorem mem_domain_iff (i : Fin 6) (z : ℂ) : z ∈ domain i ↔
    z ≠ 0 ∧ z ≠ 1 ∧ argument i z ∈ cutPlane ∧
      (i = 1 → z ∈ slitPlane) ∧ (i = 3 → 1 - z ∈ slitPlane) ∧
        (4 ≤ i.val → -z ∈ slitPlane) := Iff.rfl

/-- The four regularized transformation forms agree on their common principal domain.
Rao–Lakshminarayanan (3.4), synopsis RL-3.03. This identity does not assign independent
first-termination polynomial values at exceptional lower parameters. -/
theorem fourForms_eq_first (A B C : ℂ) (j : Fin 4) {u : ℂ} (hu : u ∈ cutPlane) :
    fourForms A B C u j = regularizedGaussHypergeometric A B C u := by
  fin_cases j
  · rfl
  · exact (regularizedGaussHypergeometric_pfaff A B C hu).symm
  · change (1 - u) ^ (-B) *
        regularizedGaussHypergeometric (C - A) B C (u / (u - 1)) = _
    rw [regularizedGaussHypergeometric_symm (C - A) B C (div_sub_one_mem_cutPlane hu)]
    rw [← regularizedGaussHypergeometric_pfaff B A C hu]
    exact regularizedGaussHypergeometric_symm B A C hu
  · exact (regularizedGaussHypergeometric_euler A B C hu).symm

/-- The four members of each literal source seed are equal, with the same chosen
continuation. Rao–Lakshminarayanan table 3.1, synopsis RL-3.03. -/
theorem expression_eq_first (a b c : ℂ) (i : Fin 6) (j : Fin 4) {z : ℂ}
    (hz : z ∈ domain i) : expression a b c i j z = expression a b c i 0 z := by
  unfold expression
  dsimp only
  rw [fourForms_eq_first _ _ _ j hz.2.2.1, fourForms_eq_first _ _ _ 0 hz.2.2.1]

/-- There are exactly twenty-four specified expressions, regardless of coincidences or
vanishing at exceptional parameters. Rao–Lakshminarayanan table 3.1, synopsis RL-3.03. -/
theorem card_indices : Fintype.card (Fin 6 × Fin 4) = 24 := by decide

/-- Every literal seed form is an analytic solution of the original complex Gauss
ODE on its actual branch domain, including the negative-axis infinity germs.
Ordinary lower parameters are regular; independently terminating exceptional cases
are covered by the finite polynomial ODE instead.
Rao–Lakshminarayanan table 3.1, (3.12)–(3.13), synopsis RL-3.03. -/
theorem analyticOnNhd_and_gaussOperator_expression (a b c : ℂ) (i : Fin 6) (j : Fin 4)
    (hC : ∀ n : ℕ, (parameters a b c i).2.2 ≠ -(n : ℂ)) :
    AnalyticOnNhd ℂ (expression a b c i j) (domain i) ∧
      ∀ z ∈ domain i, gaussOperator a b c (expression a b c i j) z = 0 := by
  sorry

/-- On either half-plane the literal source normalization agrees with one expression of
the permutation algorithm up to a nonzero constant phase and Gamma normalization.
The factor is constant on the whole half-plane, not chosen separately at each point.
Rao–Lakshminarayanan table 3.1, (3.12)–(3.13), synopsis RL-3.03. -/
theorem expression_eq_const_mul_permutation_solution (a b c : ℂ) (i : Fin 6) (j : Fin 4)
    (hC : ∀ n : ℕ, (parameters a b c i).2.2 ≠ -(n : ℂ)) (upper : Bool) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ first second : Bool, ∃ d : ℂ, d ≠ 0 ∧
      ∀ z : ℂ, (if upper then 0 < z.im else z.im < 0) →
        expression a b c i j z = d * KummerPermutations.solution a b c σ first second z := by
  sorry

end DLMF.Hypergeometric.KummerSeedForms
