/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Basic.Analytic
public import DLMF.RiemannTheta.Basic.Periodicity
import Mathlib.Tactic

/-!
# Spaces of theta functions of integral order

The space of entire functions with integer periods and the order-`N` theta
automorphy factor is a complex vector space. Products add orders, powers multiply
orders, and quotients of equal-order sections are lattice periodic, even with
totalized division. The Riemann theta function belongs to the order-one space.

References: Mumford, *Tata Lectures on Theta I*, Chapter II, Definition 1.2;
Igusa, *Theta Functions*, Chapter II, §§3–4; Beals–Wong,
*Explorations in Complex Functions*, §14.3.
-/

public noncomputable section

open Complex Matrix
open scoped Real

namespace DLMF.RiemannTheta

variable {ι : Type*} [Fintype ι]

/-- The order-`N` multiplier for translation by `Ωm`. The convention is
`exp(-πiN mΩm - 2πiN mz)`; order zero has multiplier one. -/
@[expose] def thetaAutomorphyFactor (N : ℕ) (Ω : Matrix ι ι ℂ) (m : ι → ℤ)
    (z : ι → ℂ) : ℂ :=
  exp (-2 * π * I * N * ((1 / 2 : ℂ) * ((fun i => (m i : ℂ)) ⬝ᵥ
    (Ω *ᵥ fun i => (m i : ℂ))) + (fun i => (m i : ℂ)) ⬝ᵥ z))

/-- The exponential formula defining the theta multiplier. -/
theorem thetaAutomorphyFactor_def (N : ℕ) (Ω : Matrix ι ι ℂ) (m : ι → ℤ) (z : ι → ℂ) :
    thetaAutomorphyFactor N Ω m z =
      exp (-2 * π * I * N * ((1 / 2 : ℂ) * ((fun i => (m i : ℂ)) ⬝ᵥ
        (Ω *ᵥ fun i => (m i : ℂ))) + (fun i => (m i : ℂ)) ⬝ᵥ z)) := rfl

/-- Theta multipliers never vanish. -/
theorem thetaAutomorphyFactor_ne_zero (N : ℕ) (Ω : Matrix ι ι ℂ)
    (m : ι → ℤ) (z : ι → ℂ) : thetaAutomorphyFactor N Ω m z ≠ 0 := exp_ne_zero _

/-- The trivial order has trivial automorphy. -/
@[simp] theorem thetaAutomorphyFactor_zero (Ω : Matrix ι ι ℂ) (m : ι → ℤ) (z : ι → ℂ) :
    thetaAutomorphyFactor 0 Ω m z = 1 := by simp [thetaAutomorphyFactor]

/-- Automorphy factors multiply when the orders add. -/
theorem thetaAutomorphyFactor_add (N M : ℕ) (Ω : Matrix ι ι ℂ)
    (m : ι → ℤ) (z : ι → ℂ) :
    thetaAutomorphyFactor (N + M) Ω m z =
      thetaAutomorphyFactor N Ω m z * thetaAutomorphyFactor M Ω m z := by
  simp only [thetaAutomorphyFactor, Nat.cast_add, ← Complex.exp_add]
  congr 1
  ring

/-- The cocycle identity for successive period-matrix translations. -/
theorem thetaAutomorphyFactor_cocycle (N : ℕ) {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω)
    (m n : ι → ℤ) (z : ι → ℂ) :
    thetaAutomorphyFactor N Ω m (z + Ω *ᵥ fun i => (n i : ℂ)) *
        thetaAutomorphyFactor N Ω n z = thetaAutomorphyFactor N Ω (m + n) z := by
  have hcast : (fun i => ((m + n) i : ℂ)) =
      (fun i => (m i : ℂ)) + fun i => (n i : ℂ) := by funext i; simp
  simp only [thetaAutomorphyFactor, hcast, ← Complex.exp_add,
    mulVec_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_mulVec_comm hΩ (fun i => (n i : ℂ)) (fun i => (m i : ℂ))]
  congr 1
  ring

/-- Entire theta functions of order `N` for the period lattice `ℤ^g + Ωℤ^g`.
This is Mumford's space `R_N`; no positivity is needed to define the vector space. -/
@[expose] def thetaSectionSpace (N : ℕ) (Ω : Matrix ι ι ℂ) :
    Submodule ℂ ((ι → ℂ) → ℂ) where
  carrier := {f | Differentiable ℂ f ∧
    (∀ (m : ι → ℤ) z, f (z + fun i => (m i : ℂ)) = f z) ∧
      ∀ (m : ι → ℤ) z, f (z + Ω *ᵥ fun i => (m i : ℂ)) =
        thetaAutomorphyFactor N Ω m z * f z}
  zero_mem' := by simp
  add_mem' hf hg := by
    refine ⟨hf.1.add hg.1, ?_, ?_⟩
    · intro m z
      simp only [Pi.add_apply, hf.2.1 m z, hg.2.1 m z]
    · intro m z
      simp only [Pi.add_apply, hf.2.2 m z, hg.2.2 m z, mul_add]
  smul_mem' c f hf := by
    refine ⟨hf.1.const_smul c, ?_, ?_⟩
    · intro m z
      simp only [Pi.smul_apply, hf.2.1 m z]
    · intro m z
      simp only [Pi.smul_apply, hf.2.2 m z, smul_eq_mul]
      ring

/-- Membership specifies entire analyticity and the two theta translation laws. -/
theorem mem_thetaSectionSpace_iff (N : ℕ) (Ω : Matrix ι ι ℂ) (f : (ι → ℂ) → ℂ) :
    f ∈ thetaSectionSpace N Ω ↔ Differentiable ℂ f ∧
      (∀ (m : ι → ℤ) z, f (z + fun i => (m i : ℂ)) = f z) ∧
        ∀ (m : ι → ℤ) z, f (z + Ω *ᵥ fun i => (m i : ℂ)) =
          thetaAutomorphyFactor N Ω m z * f z := Iff.rfl

/-- Constants are theta functions of order zero. -/
theorem const_mem_thetaSectionSpace_zero (Ω : Matrix ι ι ℂ) (c : ℂ) :
    (fun _ : ι → ℂ => c) ∈ thetaSectionSpace 0 Ω := by
  exact ⟨differentiable_const c, by simp, by simp⟩

/-- Products of theta functions add their orders. -/
theorem mul_mem_thetaSectionSpace {N M : ℕ} {Ω : Matrix ι ι ℂ}
    {f g : (ι → ℂ) → ℂ} (hf : f ∈ thetaSectionSpace N Ω)
    (hg : g ∈ thetaSectionSpace M Ω) : f * g ∈ thetaSectionSpace (N + M) Ω := by
  refine ⟨hf.1.mul hg.1, ?_, ?_⟩
  · intro m z
    simp only [Pi.mul_apply, hf.2.1 m z, hg.2.1 m z]
  · intro m z
    simp only [Pi.mul_apply, hf.2.2 m z, hg.2.2 m z, thetaAutomorphyFactor_add]
    ring

/-- Powers multiply the order, including the zeroth power. -/
theorem pow_mem_thetaSectionSpace {N : ℕ} {Ω : Matrix ι ι ℂ} {f : (ι → ℂ) → ℂ}
    (hf : f ∈ thetaSectionSpace N Ω) (k : ℕ) : f ^ k ∈ thetaSectionSpace (k * N) Ω := by
  induction k with
  | zero => simpa using! const_mem_thetaSectionSpace_zero Ω 1
  | succ k ih => simpa only [pow_succ, Nat.succ_mul] using mul_mem_thetaSectionSpace ih hf

/-- The quotient of equal-order theta functions is lattice periodic. This identity also
holds at totalized denominator zeros; it does not assert analyticity there. -/
theorem periodic_div_of_mem_thetaSectionSpace {N : ℕ} {Ω : Matrix ι ι ℂ}
    {f g : (ι → ℂ) → ℂ} (hf : f ∈ thetaSectionSpace N Ω)
    (hg : g ∈ thetaSectionSpace N Ω) (m n : ι → ℤ) :
    Function.Periodic (fun z => f z / g z)
      ((fun i => (m i : ℂ)) + Ω *ᵥ fun i => (n i : ℂ)) := by
  intro z
  dsimp only
  rw [← add_assoc, hf.2.2, hg.2.2, hf.2.1, hg.2.1]
  exact mul_div_mul_left _ _ (thetaAutomorphyFactor_ne_zero N Ω n _)

/-- The canonical Riemann theta function is an order-one theta function. -/
theorem riemannTheta_mem_thetaSectionSpace {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    (fun z => riemannTheta z Ω) ∈ thetaSectionSpace 1 Ω := by
  refine ⟨differentiable_riemannTheta hΩ, fun m z => riemannTheta_add_int z Ω m, ?_⟩
  intro m z
  simpa only [thetaAutomorphyFactor, Nat.cast_one, mul_one, Pi.zero_apply,
    Int.cast_zero, ← Pi.zero_def, add_zero] using riemannTheta_add_lattice z hΩ.1 0 m

end DLMF.RiemannTheta
