/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic

/-!
# The entire-quotient equations for Painlevé II

The bilinear equations Beals–Wong (15.3.10)–(15.3.11) imply that `u = v/w` solves `PII(c)`
wherever `w` is nonzero. The proof is local differentiation and does not assume or claim the
global existence of entire `v` and `w`.

## Main definitions

* `TauEquationsAt`: the two bilinear quotient equations (15.3.10)–(15.3.11) at a point.
* `tauQuotientDeriv`: the first derivative of the quotient `v/w`.

## Main results

* `isPIIOn_quotient_of_tau`: a twice differentiable solution of the two tau equations gives a
  Painlevé II solution on an open set avoiding the zeros of its denominator.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace DLMF.Painleve

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The two bilinear quotient equations (15.3.10)–(15.3.11), at a single point. -/
def TauEquationsAt (c : 𝕜) (v w : 𝕜 → 𝕜) (x : 𝕜) : Prop :=
  w x * deriv (deriv w) x = deriv w x ^ 2 - v x ^ 2 ∧
    w x ^ 2 * deriv (deriv v) x + v x * deriv w x ^ 2 =
      2 * deriv v x * w x * deriv w x + v x ^ 3 + x * v x * w x ^ 2 - c * w x ^ 3

/-- The first derivative of a quotient in the tau representation. -/
def tauQuotientDeriv (v w : 𝕜 → 𝕜) (x : 𝕜) : 𝕜 :=
  (deriv v x * w x - v x * deriv w x) / w x ^ 2

/-- A twice differentiable solution of the two tau equations gives a Painlevé II
solution on an open set avoiding the zeros of its denominator. -/
theorem isPIIOn_quotient_of_tau {c : 𝕜} {v w : 𝕜 → 𝕜} {s : Set 𝕜} (hs : IsOpen s)
    (hv : ∀ x ∈ s, DifferentiableAt 𝕜 v x) (hw : ∀ x ∈ s, DifferentiableAt 𝕜 w x)
    (hv' : ∀ x ∈ s, DifferentiableAt 𝕜 (deriv v) x)
    (hw' : ∀ x ∈ s, DifferentiableAt 𝕜 (deriv w) x)
    (hw0 : ∀ x ∈ s, w x ≠ 0) (hτ : ∀ x ∈ s, TauEquationsAt c v w x) :
    IsPIIOn c (fun x => v x / w x) s := by
  apply isPIIOn_of_hasDerivAt hs (v := tauQuotientDeriv v w)
  · intro x hx
    exact (hv x hx).hasDerivAt.div (hw x hx).hasDerivAt (hw0 x hx)
  · intro x hx
    have hv₁ := (hv x hx).hasDerivAt
    have hw₁ := (hw x hx).hasDerivAt
    have hv₂ := (hv' x hx).hasDerivAt
    have hw₂ := (hw' x hx).hasDerivAt
    have hd := ((hv₂.mul hw₁).sub (hv₁.mul hw₂)).div (hw₁.pow 2) (pow_ne_zero _ (hw0 x hx))
    refine hd.congr_deriv ?_
    obtain ⟨ht1, ht2⟩ := hτ x hx
    simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
    field_simp [hw0 x hx]
    linear_combination (w x) * ht2 - (v x * w x) * ht1

end DLMF.Painleve
