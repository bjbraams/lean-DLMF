/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.KummerCubeCoordinates
public import DLMF.Hypergeometric.KummerPermutations

/-!
# The full parameter content of the six-coordinate cube action

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), Chapter 3,
(3.8)–(3.11), pp. 3-5–3-6, synopsis RL-3.02. Opposite-face differences are
the three exponent differences. The full transformed parameter triple, not only
its argument, lies in the explicit twenty-four-form Kummer algorithm.
-/

@[expose] public noncomputable section

open Complex Finset

namespace DLMF.Hypergeometric.TransformationGroups

/-- The opposite-face coordinate differences are exactly `c-1,a+b-c,a-b`.
Rao–Lakshminarayanan (3.8)–(3.11), synopsis RL-3.02. -/
theorem kummerCubeParameters_exponent_differences (x : Fin 6 → ℂ)
    (hx : ∑ i, x i = 0) :
    let p := kummerCubeParameters x
    ![p 2 - 1, p 0 + p 1 - p 2, p 0 - p 1] =
      ![x 0 - x 5, x 1 - x 4, x 2 - x 3] := by
  have hs := hx
  simp only [Fin.sum_univ_succ] at hs
  change x 0 + (x 1 + (x 2 + (x 3 + (x 4 + (x 5 + 0))))) = 0 at hs
  funext i
  fin_cases i
  · simp [kummerCubeParameters]
    ring
  · norm_num [kummerCubeParameters]
    linear_combination hs
  · simp [kummerCubeParameters]

/-- Every cube-rotated triple and its actual argument belong to the explicit Kummer
parameter algorithm, up to the harmless interchange of the two upper parameters.
Both six-coordinate denominators are retained explicitly.
Rao–Lakshminarayanan (3.8)–(3.11), synopsis RL-3.02. -/
theorem kummerCubeParameters_mem_kummer_orbit (x : Fin 6 → ℂ)
    (hx : ∑ i, x i = 0) (hden : x 2 + x 3 ≠ 0) (g : cubeRotations)
    (hgden : x (g.val.symm 2) + x (g.val.symm 3) ≠ 0) :
    let p := kummerCubeParameters x
    let q := kummerCubeParameters (x ∘ g.val.symm)
    ∃ σ : Equiv.Perm (Fin 3), ∃ first second : Bool,
      let r := KummerPermutations.parameters (p 0) (p 1) (p 2) σ first second
      q 3 = KummerPermutations.coordinate σ (p 3) ∧ q 2 = r.2.2 ∧
        ((q 0 = r.1 ∧ q 1 = r.2.1) ∨ (q 0 = r.2.1 ∧ q 1 = r.1)) := by
  sorry

end DLMF.Hypergeometric.TransformationGroups
