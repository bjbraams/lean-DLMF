/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BaileyPairs

/-!
# The weak Bailey transform under its double-series hypothesis

Andrews, Askey and Roy, *Special Functions*, Lemma 12.2.1, pp. 582–583
(synopsis AAR-12.2.1–12.2.3). Only the actual triangular absolute sum is
assumed; separate summability of the transformed sequences is a conclusion.
-/

@[expose] public noncomputable section
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- The weak Bailey transform with exactly the absolute triangular Fubini hypothesis.
Andrews–Askey–Roy, Lemma 12.2.1. -/
theorem limiting_bailey_transform_of_summable_double {a q : ℂ} {alpha beta : ℕ → ℂ}
    (hq : ‖q‖ < 1) (hpair : DLMF.Bailey.IsBaileyPair a q alpha beta)
    (hden : ∀ n, qPochhammer (a * q) q n ≠ 0)
    (hdouble : Summable (fun p : ℕ × ℕ => if p.2 ≤ p.1 then
      a ^ p.1 * q ^ (p.1 * p.1) * alpha p.2 /
        (qPochhammer q q (p.1 - p.2) * qPochhammer (a * q) q (p.1 + p.2)) else 0)) :
    Summable (fun n => a ^ n * q ^ (n * n) * alpha n) ∧
    Summable (fun n => a ^ n * q ^ (n * n) * beta n) ∧
      (∑' n, a ^ n * q ^ (n * n) * beta n) =
        (qPochhammerInf (a * q) q)⁻¹ * ∑' n, a ^ n * q ^ (n * n) * alpha n := by
  sorry

end DLMF.QHypergeometric
