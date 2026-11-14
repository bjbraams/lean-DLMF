/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.DiniZeros
public import DLMF.Bessel.PositiveZeroSequence
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The canonical product of the normalized Bessel function

Andrews, Askey and Roy, *Special Functions*, §4.14, pp. 225–229
(synopsis AAR-4.14.1–4.16.4). Normalization removes the power at zero and
states an entire identity without a choice of power branch.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology
namespace DLMF.Bessel

/-- The complete positive-zero product of the entire normalized Bessel function.
Andrews–Askey–Roy, §4.14. The hypothesis excludes omitted zeros and repetitions. -/
theorem hasProd_normalized_besselJ {nu : ℝ} (hnu : -1 < nu) {j : ℕ → ℝ}
    (hj : StrictMono j) (hjpositive : ∀ k, 0 < j k)
    (hjzero : ∀ k, Complex.besselJ nu (j k) = 0)
    (hjcomplete : ∀ x : ℝ, 0 < x → Complex.besselJ nu x = 0 → ∃ k, j k = x) (z : ℂ) :
    HasProd (fun k => 1 - z ^ 2 / (j k : ℂ) ^ 2)
      (Complex.Gamma (nu + 1) * Complex.regularizedHGFun ∅ {(nu : ℂ) + 1} (-((z / 2) ^ 2))) := by
  sorry

end DLMF.Bessel
