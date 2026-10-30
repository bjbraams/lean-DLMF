/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.Basic.Ferrers

/-!
# Existence and defining properties of spheroidal Ferrers functions

The canonical definitions are in `DLMF.Spheroidal.Basic.Ferrers`. Existence and
specification statements retain their original domains and coefficient conventions.
-/

@[expose] public noncomputable section

open Complex Set Filter DLMF.Legendre
open scoped Topology Real Classical

namespace DLMF.Spheroidal

/-- `dif_pos` without the deprecation. -/
private lemma s30_dif_pos' {c : Prop} [Decidable c] (h : c) {α : Sort*} {t : c → α}
    {e : ¬c → α} : dite c t e = t h := by simp [h]

/-! ### Existence theorems (flagged) -/

/-- **Existence of the recessive coefficients** `a'^m_{n,k}(γ²)` (DLMF §30.8(ii)), for
`m ≤ n`. Flagged existence theorem (admitted): the recurrence 30.8.4 has, as `k → -∞`, a
recessive solution, unique up to a factor fixed by 30.8.10. -/
@[dlmf 30.8.ii]
theorem exists_isSpheroidalCoeffPrime {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃ f, IsSpheroidalCoeffPrime n m γ2 f := by
  sorry

/-- **Existence of `𝖰s^m_n`** (DLMF §30.5, §30.8(ii)): for `m ≤ n`, when the forward recursion of
§30.8(ii) does not vanish at `k = -R` (otherwise DLMF states that `𝖰s` does not exist). Flagged
existence theorem (admitted); uniqueness holds by the parity argument. -/
@[dlmf 30.5.E1]
theorem exists_isSpheroidalQs {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    ∃ f, IsSpheroidalQs n m γ2 f := by
  sorry

/-- **Existence and uniqueness of `𝑄s^m_n`** (DLMF §30.6), under the hypotheses of
`exists_isSpheroidalQs`. Flagged existence theorem (admitted). -/
@[dlmf 30.6.E1]
theorem existsUnique_isSpheroidalQsC {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    ∃! F, IsSpheroidalQsC n m γ2 F := by
  sorry

/-- The defining property of `𝖰s^m_n` (DLMF 30.5.1), from `exists_isSpheroidalQs`. -/
theorem spheroidalQs_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    IsSpheroidalQs n m γ2 (fun x => spheroidalQs n m x γ2) := by
  have h := exists_isSpheroidalQs hmn γ2 hf
  have he : (fun x => spheroidalQs n m x γ2) = h.choose := by
    funext x; simp only [spheroidalQs, s30_dif_pos' h]
  rw [he]; exact h.choose_spec

/-- The defining property of `𝑄s^m_n` (DLMF 30.6.1), from `existsUnique_isSpheroidalQsC`. -/
theorem spheroidalQsC_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) :
    IsSpheroidalQsC n m γ2 (fun z => spheroidalQsC n m z γ2) := by
  have h := (existsUnique_isSpheroidalQsC hmn γ2 hf).exists
  have he : (fun z => spheroidalQsC n m z γ2) = h.choose := by
    funext z; simp only [spheroidalQsC, s30_dif_pos' h]
  rw [he]; exact h.choose_spec

/-- The defining property of `a'^m_{n,k}` (DLMF §30.8(ii)), from
`exists_isSpheroidalCoeffPrime`. -/
theorem spheroidalCoeffPrime_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    IsSpheroidalCoeffPrime n m γ2 (spheroidalCoeffPrime n m γ2) := by
  have h := exists_isSpheroidalCoeffPrime hmn γ2
  simp only [spheroidalCoeffPrime, s30_dif_pos' h]
  exact h.choose_spec

end DLMF.Spheroidal
