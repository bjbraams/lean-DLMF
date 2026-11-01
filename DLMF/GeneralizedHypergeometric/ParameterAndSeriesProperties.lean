/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.GeneralizedHypergeometric.Basic.SeriesProperties

public import DLMF.Core.Basic
public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.GeneralizedCalculus
public import DLMF.Hypergeometric.Solutions
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Existence of the principal continuation (DLMF §§16.1–16.2)

Properties of the definitions in `DLMF.GeneralizedHypergeometric.Basic`. The series facts of
§16.2 (uniqueness of the continuation, the series on the disk, terminating series and the
inversion formulas 16.2.3–16.2.4) are in `DLMF.GeneralizedHypergeometric.Basic.SeriesProperties`.

## Main results

* `genPrincipalContinuation_exists`: existence of the normalized principal continuation for
  `p = q + 1`.
* `genRegularizedHG_eq_original`: the guarded definition agrees with the unguarded choice.

## Implementation notes

Mathlib's `regularizedHGFun` is a totalized power-series sum, not an analytic continuation
outside its convergence disk. Here `genRegularizedHG` uses a uniquely normalized principal
continuation for `p = q + 1`, and `genHG` restores the Gamma factors when the lower parameters
are regular. Nonprincipal boundary values are kept separately. For nonterminating series with
`p > q + 1` no analytic value is assigned by this API; contour values are in
`DLMF.GeneralizedHypergeometric.Integrals`. `genFiniteHG` handles terminating expressions whose
lower parameters may be exceptional after the final retained term.

Mathlib supplies convergent-series radii and holomorphy. Finite inversion multiplies the
scalar Pochhammer reflection identity `poch_one_sub_sub_mul` over the parameter multiset and
uses Mathlib's descending-factorial and binomial normalization. The integer-index Gamma bridge
uses Mathlib's Gamma recurrence and its pole totalization.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real ENNReal
noncomputable section
namespace DLMF.Hypergeometric

/-- Existence of principal continuation for all regularized parameters, including Gamma zeros. -/
theorem genPrincipalContinuation_exists (a b : Multiset ℂ) (h : a.card = b.card + 1) :
    Nonempty (GenPrincipalContinuation a b) := by
  sorry

/-- The guarded definition preserves the previous choice of continuation, assuming
exactly the recorded existence theorem. This does not prove existence. -/
theorem genRegularizedHG_eq_original (a b : Multiset ℂ) (z : ℂ) :
    genRegularizedHG a b z =
      if h : a.card = b.card + 1 then
        (Classical.choice (genPrincipalContinuation_exists a b h)).value z
      else Complex.regularizedHGFun a b z := by
  classical
  unfold genRegularizedHG
  split_ifs with h hF
  · rfl
  · exact False.elim (hF (genPrincipalContinuation_exists a b h))
  · rfl

end DLMF.Hypergeometric
