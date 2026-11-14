/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.SixJ
public import DLMF.GeneralizedHypergeometric.Basic.ParametersAndSeries
public import Mathlib.Data.Fin.VecNotation

/-!
# Bargmann–Shelepin coordinates and all finite hypergeometric forms

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
§§6.2–6.5, (6.28)–(6.120). Permuting the four face sums and three
quadrilateral sums specifies all 144 Regge transformations.
-/

@[expose] public noncomputable section
open Finset DLMF.Hypergeometric
namespace DLMF.WignerSymbols.SixJCoordinates

/-- The four triangular sums for labels `(a,b,c,d,e,f)` and symbol `{a b e; d c f}`,
Rao–Lakshminarayanan (6.26), synopsis RL-6.02 and RL-6.08. -/
def alpha (v : Fin 6 → ℚ) : Fin 4 → ℚ :=
  ![v 0 + v 1 + v 4, v 2 + v 3 + v 4,
    v 0 + v 2 + v 5, v 1 + v 3 + v 5]

/-- The three quadrilateral sums, Rao–Lakshminarayanan (6.27), RL-6.08. -/
def beta (v : Fin 6 → ℚ) : Fin 3 → ℚ :=
  ![v 0 + v 1 + v 2 + v 3, v 0 + v 3 + v 4 + v 5, v 1 + v 2 + v 4 + v 5]

/-- The inverse linear parameter map on the hyperplane `Σα=Σβ`,
Rao–Lakshminarayanan (6.100)–(6.120), synopsis RL-6.08. -/
def labels (α : Fin 4 → ℚ) (β : Fin 3 → ℚ) : Fin 6 → ℚ :=
  ![(α 0 + α 2 - β 2) / 2, (α 0 + α 3 - β 1) / 2,
    (α 1 + α 2 - β 1) / 2, (α 1 + α 3 - β 2) / 2,
    (α 0 + α 1 - β 0) / 2, (α 2 + α 3 - β 0) / 2]

/-- The nonnegative integer Bargmann–Shelepin array at admissible labels,
Rao–Lakshminarayanan (6.61)–(6.67), synopsis RL-6.07. -/
def array (v : Fin 6 → ℚ) (i : Fin 4) (k : Fin 3) : ℚ := beta v k - alpha v i

/-- The four explicit triangular sums of RL-6.08. -/
theorem alpha_def (v : Fin 6 → ℚ) : alpha v =
    ![v 0 + v 1 + v 4, v 2 + v 3 + v 4,
      v 0 + v 2 + v 5, v 1 + v 3 + v 5] := rfl

/-- The three explicit quadrilateral sums of RL-6.08. -/
theorem beta_def (v : Fin 6 → ℚ) : beta v =
    ![v 0 + v 1 + v 2 + v 3, v 0 + v 3 + v 4 + v 5, v 1 + v 2 + v 4 + v 5] := rfl

/-- The inverse-map formula of RL-6.08. -/
theorem labels_def (α : Fin 4 → ℚ) (β : Fin 3 → ℚ) : labels α β =
    ![(α 0 + α 2 - β 2) / 2, (α 0 + α 3 - β 1) / 2,
      (α 1 + α 2 - β 1) / 2, (α 1 + α 3 - β 2) / 2,
      (α 0 + α 1 - β 0) / 2, (α 2 + α 3 - β 0) / 2] := rfl

/-- Each array entry is a quadrilateral sum minus a triangular sum, RL-6.07. -/
theorem array_def (v : Fin 6 → ℚ) (i : Fin 4) (k : Fin 3) :
    array v i k = beta v k - alpha v i := rfl

/-- Recovering the six spins from the seven sums, Rao–Lakshminarayanan RL-6.08. -/
theorem labels_alpha_beta (v : Fin 6 → ℚ) : labels (alpha v) (beta v) = v := by
  funext i
  fin_cases i <;> simp [labels, alpha, beta] <;> ring

/-- The sums of the two coordinate blocks agree, Rao–Lakshminarayanan RL-6.08. -/
theorem sum_alpha_eq_sum_beta (v : Fin 6 → ℚ) : ∑ i, alpha v i = ∑ k, beta v k := by
  simp [alpha, beta, Fin.sum_univ_succ]
  ring

/-- The inverse gives the prescribed triangular coordinates on the balanced hyperplane,
Rao–Lakshminarayanan RL-6.08. -/
theorem alpha_labels (α : Fin 4 → ℚ) (β : Fin 3 → ℚ)
    (h : ∑ i, α i = ∑ k, β k) : alpha (labels α β) = α := by
  sorry

/-- The inverse gives the prescribed quadrilateral coordinates on the balanced hyperplane,
Rao–Lakshminarayanan RL-6.08. -/
theorem beta_labels (α : Fin 4 → ℚ) (β : Fin 3 → ℚ)
    (h : ∑ i, α i = ∑ k, β k) : beta (labels α β) = β := by
  sorry

/-- Opposite rectangle sums coincide in the Bargmann–Shelepin array,
Rao–Lakshminarayanan (6.61)–(6.67), synopsis RL-6.07. -/
theorem array_rectangle (v : Fin 6 → ℚ) (i l : Fin 4) (j k : Fin 3) :
    array v i j + array v l k = array v i k + array v l j := by
  simp only [array]
  ring

/-- Admissible angular momenta give nonnegative integer array entries,
Rao–Lakshminarayanan (6.61)–(6.67), synopsis RL-6.07. -/
theorem isNatQ_array (v : Fin 6 → ℚ)
    (hv : IsAdmissible6j (v 0) (v 1) (v 4) (v 3) (v 2) (v 5))
    (i : Fin 4) (k : Fin 3) : IsNatQ (array v i k) := by
  sorry

/-- Arbitrary independent block permutations preserve the 6-j symbol,
Rao–Lakshminarayanan (6.100)–(6.120), synopsis RL-6.08. -/
theorem wigner6j_permute (v : Fin 6 → ℚ) (ρ : Equiv.Perm (Fin 4))
    (π : Equiv.Perm (Fin 3)) :
    let w := labels (alpha v ∘ ρ) (beta v ∘ π)
    wigner6j (v 0) (v 1) (v 4) (v 3) (v 2) (v 5) =
      wigner6j (w 0) (w 1) (w 4) (w 3) (w 2) (w 5) := by
  sorry

/-- The 144 parameter actions preserve admissibility, Rao–Lakshminarayanan RL-6.08. -/
theorem isAdmissible6j_permute (v : Fin 6 → ℚ)
    (hv : IsAdmissible6j (v 0) (v 1) (v 4) (v 3) (v 2) (v 5))
    (ρ : Equiv.Perm (Fin 4)) (π : Equiv.Perm (Fin 3)) :
    let w := labels (alpha v ∘ ρ) (beta v ∘ π)
    IsAdmissible6j (w 0) (w 1) (w 4) (w 3) (w 2) (w 5) := by
  sorry

/-- All three set-I representations, choosing any minimal quadrilateral sum,
Rao–Lakshminarayanan (6.28), (6.31)–(6.42), synopsis RL-6.04.
The truncation includes all nonzero terms even if another upper parameter terminates first. -/
theorem wigner6j_set_one (v : Fin 6 → ℚ)
    (hv : IsAdmissible6j (v 0) (v 1) (v 4) (v 3) (v 2) (v 5))
    (k : Fin 3) (hk : ∀ j, beta v k ≤ beta v j) :
    (wigner6j (v 0) (v 1) (v 4) (v 3) (v 2) (v 5) : ℂ) =
      ((triangleDelta (v 0) (v 1) (v 4) * triangleDelta (v 2) (v 3) (v 4) *
        triangleDelta (v 0) (v 2) (v 5) * triangleDelta (v 1) (v 3) (v 5) *
        signPow (beta v k) * ratFactorial (beta v k + 1) /
          ((∏ i, ratFactorial (beta v k - alpha v i)) *
            ∏ j ∈ univ.erase k, ratFactorial (beta v j - beta v k)) : ℝ) : ℂ) *
        generalizedHypergeometricTruncated ⌊beta v k - alpha v 0⌋.toNat
          (parametersOfFin (fun i : Fin 4 => ((alpha v i - beta v k : ℚ) : ℂ)))
          ({((-beta v k - 1 : ℚ) : ℂ)} +
            ((univ.erase k).val.map (fun j => ((1 + beta v j - beta v k : ℚ) : ℂ)))) 1 := by
  sorry

/-- All four set-II representations, choosing any maximal triangular sum,
Rao–Lakshminarayanan (6.29), (6.47)–(6.56), synopsis RL-6.05. -/
theorem wigner6j_set_two (v : Fin 6 → ℚ)
    (hv : IsAdmissible6j (v 0) (v 1) (v 4) (v 3) (v 2) (v 5))
    (l : Fin 4) (hl : ∀ i, alpha v i ≤ alpha v l) :
    (wigner6j (v 0) (v 1) (v 4) (v 3) (v 2) (v 5) : ℂ) =
      ((triangleDelta (v 0) (v 1) (v 4) * triangleDelta (v 2) (v 3) (v 4) *
        triangleDelta (v 0) (v 2) (v 5) * triangleDelta (v 1) (v 3) (v 5) *
        signPow (alpha v l) * ratFactorial (alpha v l + 1) /
          ((∏ i ∈ univ.erase l, ratFactorial (alpha v l - alpha v i)) *
            ∏ j, ratFactorial (beta v j - alpha v l)) : ℝ) : ℂ) *
        generalizedHypergeometricTruncated ⌊beta v 0 - alpha v l⌋.toNat
          ({((alpha v l + 2 : ℚ) : ℂ)} +
            parametersOfFin (fun j : Fin 3 => ((alpha v l - beta v j : ℚ) : ℂ)))
          ((univ.erase l).val.map (fun i => ((1 + alpha v l - alpha v i : ℚ) : ℂ))) 1 := by
  sorry

end DLMF.WignerSymbols.SixJCoordinates
