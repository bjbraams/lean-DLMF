/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic

/-!
# Bäcklund transformations for Painlevé II

Beals–Wong Theorem 15.4.2, Proposition 15.4.3, and Corollary 15.4.4.
The proofs differentiate the transformations directly; no existence of a
fundamental solution of the compatible matrix system is assumed. Formulas
are asserted on open sets where their denominators do not vanish.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace DLMF.Painleve

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The denominator of the reflection `c ↦ 1-c`, Beals–Wong (15.4.22). -/
def backlundDenom (u : 𝕜 → 𝕜) (x : 𝕜) : 𝕜 := x + 2 * u x ^ 2 + 2 * deriv u x

/-- The correction term in the parameter reflection. -/
def backlundCorrection (c : 𝕜) (u : 𝕜 → 𝕜) (x : 𝕜) : 𝕜 :=
  (1 - 2 * c) / backlundDenom u x

/-- The Bäcklund reflection taking `PII(c)` to `PII(1-c)`. -/
def backlundReflect (c : 𝕜) (u : 𝕜 → 𝕜) (x : 𝕜) : 𝕜 := u x + backlundCorrection c u x

/-- The explicit derivative of the Bäcklund reflection along a solution. -/
def backlundReflectDeriv (c : 𝕜) (u : 𝕜 → 𝕜) (x : 𝕜) : 𝕜 :=
  deriv u x - 2 * u x * backlundCorrection c u x - backlundCorrection c u x ^ 2

/-- The denominator satisfies a first-order equation with constant inhomogeneous term. -/
theorem IsPIIOn.hasDerivAt_backlundDenom {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s) :
    HasDerivAt (backlundDenom u) (2 * u x * backlundDenom u x + (1 - 2 * c)) x := by
  have hu := h.hasDerivAt hx
  have hv := h.hasDerivAt_deriv x hx
  exact (((hasDerivAt_id x).add ((hu.pow 2).const_mul 2)).add
    (hv.const_mul 2)).congr_deriv (by dsimp only [backlundDenom, id_eq, Pi.pow_apply]; ring)

/-- The Bäcklund correction satisfies a Riccati identity wherever its denominator is nonzero. -/
theorem IsPIIOn.hasDerivAt_backlundCorrection {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s) (hD : backlundDenom u x ≠ 0) :
    HasDerivAt (backlundCorrection c u)
      (-2 * u x * backlundCorrection c u x - backlundCorrection c u x ^ 2) x := by
  refine ((hasDerivAt_const x (1 - 2 * c)).div (h.hasDerivAt_backlundDenom hx) hD).congr_deriv ?_
  dsimp only [backlundCorrection]
  field_simp
  ring

/-- The first derivative of the reflected solution. -/
theorem IsPIIOn.hasDerivAt_backlundReflect {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s) (hD : backlundDenom u x ≠ 0) :
    HasDerivAt (backlundReflect c u) (backlundReflectDeriv c u x) x :=
  ((h.hasDerivAt hx).add (h.hasDerivAt_backlundCorrection hx hD)).congr_deriv (by
    dsimp only [backlundReflectDeriv]; ring)

/-- The explicit first derivative satisfies the reflected Painlevé equation. -/
private lemma IsPIIOn.hasDerivAt_backlundReflectDeriv {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s) (hD : backlundDenom u x ≠ 0) :
    HasDerivAt (backlundReflectDeriv c u)
      (2 * backlundReflect c u x ^ 3 + x * backlundReflect c u x - (1 - c)) x := by
  have hu := h.hasDerivAt hx
  have hv := h.hasDerivAt_deriv x hx
  have ht := h.hasDerivAt_backlundCorrection hx hD
  have hconstraint : backlundCorrection c u x * backlundDenom u x = 1 - 2 * c := by
    exact div_mul_cancel₀ _ hD
  refine ((hv.sub ((hu.const_mul 2).mul ht)).sub (ht.pow 2)).congr_deriv ?_
  dsimp only [backlundReflect]
  dsimp only [backlundDenom] at hconstraint
  linear_combination -hconstraint

/-- Bäcklund reflection, Beals–Wong (15.4.22), on every open set avoiding the denominator
zeros. No parameter exclusion is needed on such a set, even at `c = 1/2`. -/
theorem IsPIIOn.reflect {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) (hs : IsOpen s) (hD : ∀ x ∈ s, backlundDenom u x ≠ 0) :
    IsPIIOn (1 - c) (backlundReflect c u) s :=
  isPIIOn_of_hasDerivAt hs (fun x hx => h.hasDerivAt_backlundReflect hx (hD x hx))
    (fun x hx => h.hasDerivAt_backlundReflectDeriv hx (hD x hx))

/-- Reflection leaves its denominator unchanged along a Painlevé II solution. -/
theorem IsPIIOn.backlundDenom_reflect {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s) (hD : backlundDenom u x ≠ 0) :
    backlundDenom (backlundReflect c u) x = backlundDenom u x := by
  rw [backlundDenom, (h.hasDerivAt_backlundReflect hx hD).deriv]
  dsimp only [backlundReflect, backlundReflectDeriv, backlundDenom]
  ring

/-- The reflection is its own inverse, Beals–Wong Proposition 15.4.3. -/
theorem IsPIIOn.backlundReflect_involutive {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s) (hD : backlundDenom u x ≠ 0) :
    backlundReflect (1 - c) (backlundReflect c u) x = u x := by
  change u x + backlundCorrection c u x +
    (1 - 2 * (1 - c)) / backlundDenom (backlundReflect c u) x = u x
  rw [h.backlundDenom_reflect hx hD]
  dsimp only [backlundCorrection]
  ring

/-- Away from `c = 1/2`, the Bäcklund denominator cannot vanish identically on a
nonempty open set of a Painlevé II solution. -/
theorem IsPIIOn.exists_backlundDenom_ne_zero {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) (hs : IsOpen s) (hne : s.Nonempty) (hc : 1 - 2 * c ≠ 0) :
    ∃ x ∈ s, backlundDenom u x ≠ 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨x, hx⟩ := hne
  have he : backlundDenom u =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hs.mem_nhds hx] with y hy using hno y hy
  have hd := (h.hasDerivAt_backlundDenom hx).deriv
  rw [he.deriv_eq, deriv_const, hno x hx, mul_zero, zero_add] at hd
  exact hc hd.symm

/-- The Bäcklund shift from `c` to `c-1`, Beals–Wong (15.4.23). -/
def backlundDown (c : 𝕜) (u : 𝕜 → 𝕜) (x : 𝕜) : 𝕜 := -backlundReflect c u x

/-- The Bäcklund shift from `c` to `c+1`, Beals–Wong (15.4.24). -/
def backlundUp (c : 𝕜) (u : 𝕜 → 𝕜) : 𝕜 → 𝕜 := backlundReflect (-c) (fun x => -u x)

/-- The usual explicit expression for the upward parameter shift. -/
theorem backlundUp_eq (c : 𝕜) (u : 𝕜 → 𝕜) (x : 𝕜) :
    backlundUp c u x = -u x + (1 + 2 * c) / (x + 2 * u x ^ 2 - 2 * deriv u x) := by
  dsimp only [backlundUp, backlundReflect, backlundCorrection, backlundDenom]
  rw [show deriv (fun x => -u x) x = -deriv u x from deriv.neg]
  congr 1
  congr 1 <;> ring

/-- The downward parameter shift takes solutions to solutions. -/
theorem IsPIIOn.shiftDown {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) (hs : IsOpen s) (hD : ∀ x ∈ s, backlundDenom u x ≠ 0) :
    IsPIIOn (c - 1) (backlundDown c u) s := by
  change IsPIIOn (c - 1) (fun x => -backlundReflect c u x) s
  simpa only [neg_sub] using (h.reflect hs hD).neg

/-- The upward parameter shift takes solutions to solutions. -/
theorem IsPIIOn.shiftUp {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) (hs : IsOpen s)
    (hD : ∀ x ∈ s, backlundDenom (fun x => -u x) x ≠ 0) :
    IsPIIOn (c + 1) (backlundUp c u) s := by
  simpa only [sub_neg_eq_add, add_comm, backlundUp] using h.neg.reflect hs hD

/-- The downward shift followed by the upward shift is the identity. -/
theorem IsPIIOn.backlundUp_down {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s) (hD : backlundDenom u x ≠ 0) :
    backlundUp (c - 1) (backlundDown c u) x = u x := by
  simpa only [backlundUp, backlundDown, neg_neg, neg_sub] using h.backlundReflect_involutive hx hD

/-- The upward shift followed by the downward shift is the identity. -/
theorem IsPIIOn.backlundDown_up {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s)
    (hD : backlundDenom (fun x => -u x) x ≠ 0) :
    backlundDown (c + 1) (backlundUp c u) x = u x := by
  have h1 := h.neg.backlundReflect_involutive hx hD
  rw [sub_neg_eq_add, add_comm] at h1
  simpa only [backlundDown, backlundUp, neg_neg] using congrArg Neg.neg h1

/-- The upward Bäcklund transformation as a rational operation on a first-order jet. -/
def backlundUpJet (c x u v : 𝕜) : 𝕜 × 𝕜 :=
  let h := (1 + 2 * c) / (x + 2 * u ^ 2 - 2 * v)
  (-u + h, -v + 2 * u * h - h ^ 2)

/-- The upward transformation differentiates to the second component of its rational jet. -/
theorem IsPIIOn.hasDerivAt_backlundUp {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s)
    (hD : backlundDenom (fun x => -u x) x ≠ 0) :
    HasDerivAt (backlundUp c u) (backlundUpJet c x (u x) (deriv u x)).2 x := by
  have hd := h.neg.hasDerivAt_backlundReflect hx hD
  refine hd.congr_deriv ?_
  dsimp only [backlundReflectDeriv, backlundCorrection, backlundDenom, backlundUpJet]
  rw [show deriv (fun x => -u x) x = -deriv u x from deriv.neg]
  have hden : x + 2 * (-u x) ^ 2 + 2 * -deriv u x = x + 2 * u x ^ 2 - 2 * deriv u x := by ring
  rw [hden, show 1 - 2 * -c = 1 + 2 * c by ring]
  ring

end DLMF.Painleve
