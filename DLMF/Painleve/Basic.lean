/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar

/-!
# Painlevé II in the Beals–Wong normalization

The equation `PII(c)` is `u'' = 2u³ + xu - c`, as in Beals–Wong (15.2.9).
`IsPIIOn` records actual differentiability, so totalized derivatives cannot
make a nonsolution satisfy the equation. Results apply over both `ℝ` and `ℂ`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace DLMF.Painleve

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A twice differentiable solution of Beals–Wong's `PII(c)` on a specified set.
The parameter is the negative of the common `α` convention for Painlevé II. -/
structure IsPIIOn (c : 𝕜) (u : 𝕜 → 𝕜) (s : Set 𝕜) : Prop where
  /-- The solution is differentiable at every point of the domain. -/
  differentiableAt : ∀ x ∈ s, DifferentiableAt 𝕜 u x
  /-- The first derivative has the derivative prescribed by the differential equation. -/
  hasDerivAt_deriv : ∀ x ∈ s, HasDerivAt (deriv u) (2 * u x ^ 3 + x * u x - c) x

namespace IsPIIOn

variable {c : 𝕜} {u : 𝕜 → 𝕜} {s t : Set 𝕜}

/-- The first derivative of a Painlevé II solution. -/
theorem hasDerivAt (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s) :
    HasDerivAt u (deriv u x) x := (h.differentiableAt x hx).hasDerivAt

/-- The second-order differential equation satisfied by a solution. -/
theorem ode (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s) :
    deriv (deriv u) x = 2 * u x ^ 3 + x * u x - c := (h.hasDerivAt_deriv x hx).deriv

/-- Restriction to a smaller set preserves the equation and differentiability. -/
theorem mono (h : IsPIIOn c u s) (ht : t ⊆ s) : IsPIIOn c u t :=
  ⟨fun x hx => h.differentiableAt x (ht hx), fun x hx => h.hasDerivAt_deriv x (ht hx)⟩

/-- Equality on an open set transports the equation, including both derivatives. -/
theorem congr (h : IsPIIOn c u s) {v : 𝕜 → 𝕜} (hs : IsOpen s) (he : EqOn u v s) :
    IsPIIOn c v s := by
  have hnear (x : 𝕜) (hx : x ∈ s) : v =ᶠ[𝓝 x] u := by
    filter_upwards [hs.mem_nhds hx] with y hy using (he hy).symm
  refine ⟨fun x hx => ((h.hasDerivAt hx).congr_of_eventuallyEq (hnear x hx)).differentiableAt,
    fun x hx => ?_⟩
  exact ((h.hasDerivAt_deriv x hx).congr_of_eventuallyEq (hnear x hx).deriv).congr_deriv
    (by rw [he hx])

/-- The elementary parameter reflection `u ↦ -u`, `c ↦ -c`, Theorem 15.4.2. -/
theorem neg (h : IsPIIOn c u s) : IsPIIOn (-c) (fun x => -u x) s := by
  refine ⟨fun x hx => (h.differentiableAt x hx).neg, fun x hx => ?_⟩
  have he : deriv (fun x => -u x) = fun x => -deriv u x := by
    funext x
    exact deriv.neg
  rw [he]
  exact (h.hasDerivAt_deriv x hx).neg.congr_deriv (by ring)

end IsPIIOn

/-- Build a solution from a first-order pair on an open set. This permits explicit
first derivatives in the proofs of special solutions and transformations. -/
theorem isPIIOn_of_hasDerivAt {c : 𝕜} {u v : 𝕜 → 𝕜} {s : Set 𝕜} (hs : IsOpen s)
    (hu : ∀ x ∈ s, HasDerivAt u (v x) x)
    (hv : ∀ x ∈ s, HasDerivAt v (2 * u x ^ 3 + x * u x - c) x) : IsPIIOn c u s := by
  refine ⟨fun x hx => (hu x hx).differentiableAt, fun x hx => ?_⟩
  apply (hv x hx).congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds hx] with y hy using (hu y hy).deriv

/-- The zero solution at parameter zero. -/
theorem isPIIOn_zero (s : Set 𝕜) : IsPIIOn (0 : 𝕜) (fun _ => 0) s := by
  refine ⟨fun _ _ => differentiableAt_const _, fun x _ => ?_⟩
  simpa using (hasDerivAt_const x (0 : 𝕜))

/-- The explicit rational solution `1/x` of `PII(1)`, away from its pole. -/
theorem isPIIOn_recip : IsPIIOn (1 : 𝕜) (fun x => x⁻¹) {x | x ≠ 0} := by
  apply isPIIOn_of_hasDerivAt isOpen_ne
    (v := fun x => -(x ^ 2)⁻¹)
  · intro x hx
    simpa only [one_div] using hasDerivAt_inv hx
  · intro x hx
    change x ≠ 0 at hx
    have h := (((hasDerivAt_id x).pow 2).inv (pow_ne_zero _ hx)).neg
    refine h.congr_deriv ?_
    simp only [id_eq, Pi.pow_apply] at *
    field_simp
    ring

/-- A useful energy identity: the nonautonomous Hamiltonian has derivative `-u²`. -/
theorem IsPIIOn.hasDerivAt_energy {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s) :
    HasDerivAt (fun x => deriv u x ^ 2 - u x ^ 4 - x * u x ^ 2 + 2 * c * u x)
      (-(u x ^ 2)) x := by
  have hu := h.hasDerivAt hx
  have hv := h.hasDerivAt_deriv x hx
  exact ((((hv.pow 2).sub (hu.pow 4)).sub
    ((hasDerivAt_id x).mul (hu.pow 2))).add (hu.const_mul (2 * c))).congr_deriv (by simp only [id_eq, Pi.pow_apply]; ring)

end DLMF.Painleve
