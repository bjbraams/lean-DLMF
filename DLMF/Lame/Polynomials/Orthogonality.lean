/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Polynomials.Defs

/-!
# Lamé polynomials: orthogonality and completeness (DLMF §29.14)

Besides the orthogonality 29.3.19 of the Lamé functions on `(0, K)` (which applies to the
Lamé polynomials by 29.12.1–29.12.8, see `DLMF.Lame.Eigenvalues`), the products
`E(s, k²) E(K + it, k²)` (`lameProduct`, 29.14.1, 29.14.4–29.14.10) of each of the eight types
form an orthogonal and complete system on `[0, K] × [0, K']` for the inner product 29.14.2 with
weight `w(s, t) = sn²(K + it, k) - sn²(s, k)` (29.14.3); together the eight systems are
orthogonal and complete on `[0, 4K] × [0, 2K']` (29.14.11). The inner product has no complex
conjugation (as in DLMF; the Lamé polynomials are real on both segments).

Completeness is stated as: a continuous function `g` on the closed rectangle orthogonal to
every member of the system vanishes on the rectangle. Orthogonality of the system 29.14.1 was
checked numerically. All statements are admitted.
-/

@[expose] public section

open Complex DLMF.Elliptic Set
open scoped Real

noncomputable section

namespace DLMF.Lame

variable {k : ℝ}

/-- 29.14.1–29.14.10, orthogonality: for each type `t`, the products `lameProduct t n m` and
`lameProduct t n' m'` (`m ≤ n`, `m' ≤ n'`, `(n, m) ≠ (n', m')`) are orthogonal for the inner
product 29.14.2 on `[0, K] × [0, K']`. Admitted. -/
@[dlmf 29.14.E1, dlmf 29.14.E2, dlmf 29.14.E3, dlmf 29.14.E4, dlmf 29.14.E5, dlmf 29.14.E6,
  dlmf 29.14.E7, dlmf 29.14.E8, dlmf 29.14.E9, dlmf 29.14.E10]
theorem lameProduct_orthogonal (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m n' m' : ℕ} (hm : m ≤ n) (hm' : m' ≤ n') (hne : (n, m) ≠ (n', m')) :
    lameInner k (Real.compEllIntKm (k ^ 2)) (Real.compEllIntKm (1 - k ^ 2))
      (lameProduct t n m k) (lameProduct t n' m' k) = 0 := by
  sorry

/-- 29.14.1–29.14.10, completeness: for each type `t`, a function `g` continuous on
`[0, K] × [0, K']` that is orthogonal (29.14.2) to every `lameProduct t n m`, `m ≤ n`,
vanishes on that rectangle. Admitted. -/
@[dlmf 29.14.E1, dlmf 29.14.E2, dlmf 29.14.E4, dlmf 29.14.E5, dlmf 29.14.E6, dlmf 29.14.E7,
  dlmf 29.14.E8, dlmf 29.14.E9, dlmf 29.14.E10]
theorem lameProduct_complete (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) {g : ℝ → ℝ → ℂ}
    (hg : ContinuousOn (Function.uncurry g)
      (Icc 0 (Real.compEllIntKm (k ^ 2)) ×ˢ Icc 0 (Real.compEllIntKm (1 - k ^ 2))))
    (horth : ∀ n m : ℕ, m ≤ n →
      lameInner k (Real.compEllIntKm (k ^ 2)) (Real.compEllIntKm (1 - k ^ 2)) g
        (lameProduct t n m k) = 0) :
    ∀ s ∈ Icc 0 (Real.compEllIntKm (k ^ 2)), ∀ τ ∈ Icc 0 (Real.compEllIntKm (1 - k ^ 2)),
      g s τ = 0 := by
  sorry

/-- 29.14.11, orthogonality: the eight systems together are orthogonal for the inner product
on `[0, 4K] × [0, 2K']`. Admitted. -/
@[dlmf 29.14.E11]
theorem lameProduct_orthogonal_all (hk0 : 0 < k) (hk1 : k < 1) {t t' : LamePolyType}
    {n m n' m' : ℕ} (hm : m ≤ n) (hm' : m' ≤ n') (hne : (t, n, m) ≠ (t', n', m')) :
    lameInner k (4 * Real.compEllIntKm (k ^ 2)) (2 * Real.compEllIntKm (1 - k ^ 2))
      (lameProduct t n m k) (lameProduct t' n' m' k) = 0 := by
  sorry

/-- 29.14.11, completeness: a function continuous on `[0, 4K] × [0, 2K']` orthogonal to all
products of all eight types vanishes there. Admitted. -/
@[dlmf 29.14.E11]
theorem lameProduct_complete_all (hk0 : 0 < k) (hk1 : k < 1) {g : ℝ → ℝ → ℂ}
    (hg : ContinuousOn (Function.uncurry g)
      (Icc 0 (4 * Real.compEllIntKm (k ^ 2)) ×ˢ Icc 0 (2 * Real.compEllIntKm (1 - k ^ 2))))
    (horth : ∀ (t : LamePolyType) (n m : ℕ), m ≤ n →
      lameInner k (4 * Real.compEllIntKm (k ^ 2)) (2 * Real.compEllIntKm (1 - k ^ 2)) g
        (lameProduct t n m k) = 0) :
    ∀ s ∈ Icc 0 (4 * Real.compEllIntKm (k ^ 2)),
      ∀ τ ∈ Icc 0 (2 * Real.compEllIntKm (1 - k ^ 2)), g s τ = 0 := by
  sorry

end DLMF.Lame
