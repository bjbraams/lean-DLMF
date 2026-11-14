/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic

/-!
# Nearly poised terminating 3F2 sums

Andrews, Askey and Roy, *Special Functions*, Theorem 8.9.1(b)–(e). Quotients
with removable parameter factors are canceled before specialization. At k=0
each sum is one. The corrected first case is already `nearly_poised_3F2`.
-/

@[expose] public section

open DLMF.Hypergeometric

namespace DLMF.Selberg

/-- The second nearly poised finite sum, including a zero value of α+β by cancellation.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.9.1(b), p. 429
(synopsis AAR-8.7.1–8.9.1). -/
theorem nearly_poised_threeFTwo_second (α β : ℂ) (k : ℕ)
    (h₁ : ∀ j ≤ 2 * k, pochhammer (1 - α - 2 * k) j ≠ 0)
    (h₂ : ∀ j ≤ 2 * k, pochhammer (α + β + 1) j ≠ 0) :
    generalizedHypergeometricTruncated (2 * k)
      {-(2 * k : ℂ), α, 1 - α - β - 2 * k} {1 - α - 2 * k, α + β + 1} 1 =
      if k = 0 then 1 else
        pochhammer α k * pochhammer (β + 1) k * ((2 * k).factorial : ℂ) /
          (pochhammer (α + β + 1) (k - 1) * k.factorial *
            pochhammer α (2 * k) * (α + β + 2 * k)) := by
  sorry

/-- The third nearly poised finite sum, with the removable α+β factor canceled.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.9.1(c), p. 429
(synopsis AAR-8.7.1–8.9.1). -/
theorem nearly_poised_threeFTwo_third (α β : ℂ) (k : ℕ)
    (h₁ : ∀ j ≤ 2 * k, pochhammer (1 - α - 2 * k) j ≠ 0)
    (h₂ : ∀ j ≤ 2 * k, pochhammer (α + β + 1) j ≠ 0) :
    generalizedHypergeometricTruncated (2 * k)
      {-(2 * k : ℂ), α + 1, 1 - α - β - 2 * k} {1 - α - 2 * k, α + β + 1} 1 =
      if k = 0 then 1 else
        pochhammer (α + 1) k * pochhammer β k * ((2 * k).factorial : ℂ) /
          (pochhammer (α + β + 1) (k - 1) * k.factorial *
            pochhammer α (2 * k) * (α + β + 2 * k)) := by
  sorry

/-- The fourth nearly poised terminating sum. Andrews–Askey–Roy,
*Special Functions*, Theorem 8.9.1(d), p. 429 (synopsis AAR-8.7.1–8.9.1). -/
theorem nearly_poised_threeFTwo_fourth (α β : ℂ) (k : ℕ)
    (h₁ : ∀ j ≤ 2 * k, pochhammer (1 - α - 2 * k) j ≠ 0)
    (h₂ : ∀ j ≤ 2 * k, pochhammer (α + β) j ≠ 0) :
    generalizedHypergeometricTruncated (2 * k)
      {-(2 * k : ℂ), α, -α - β - 2 * k} {1 - α - 2 * k, α + β} 1 =
      pochhammer α k * pochhammer (β + 1) k * ((2 * k).factorial : ℂ) /
        (pochhammer (α + β) k * k.factorial * pochhammer α (2 * k)) := by
  sorry

/-- The fifth nearly poised finite sum, after canceling its overlapping rising factorials.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.9.1(e), p. 429
(synopsis AAR-8.7.1–8.9.1). -/
theorem nearly_poised_threeFTwo_fifth (α β : ℂ) (k : ℕ)
    (h₁ : ∀ j ≤ 2 * k, pochhammer (1 - α - 2 * k) j ≠ 0)
    (h₂ : ∀ j ≤ 2 * k, pochhammer (α + β + 2) j ≠ 0) :
    generalizedHypergeometricTruncated (2 * k)
      {-(2 * k : ℂ), α + 1, 1 - α - β - 2 * k} {1 - α - 2 * k, α + β + 2} 1 =
      if k = 0 then 1 else
        pochhammer (α + 1) k * pochhammer (β + 1) k * ((2 * k).factorial : ℂ) *
          (α + β) * pochhammer (α + β + k + 1) (k - 1) /
          (k.factorial * pochhammer α (2 * k) * pochhammer (α + β + 2) (2 * k)) := by
  sorry

end DLMF.Selberg
