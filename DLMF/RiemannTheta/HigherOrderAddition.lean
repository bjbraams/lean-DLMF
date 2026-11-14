/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Basic.HigherOrder
public import DLMF.RiemannTheta.Products
import Mathlib.Tactic

/-!
# Addition and evenness for second-order theta functions

The product `θ(z+w)θ(z-w)` separates as a finite sum of products of second-order
theta functions at `z` and `w`. In particular it is a section of order two in `z`.
All the second-order functions are even, for arbitrary integer labels.

References: Mumford, *Tata Lectures on Theta I*, Chapter I, §5 and Chapter II, §1;
Igusa, *Theta Functions*, Chapter IV, §1. The finite addition identity is deduced
from the project's proved DLMF 21.6.8 with the existing series normalization.
-/

public noncomputable section

open Complex Matrix

namespace DLMF.RiemannTheta

variable {ι : Type*} [Fintype ι]

/-- The second-order addition formula separates the two vector arguments. -/
theorem riemannTheta_add_mul_sub [DecidableEq ι] {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) (z w : ι → ℂ) :
    riemannTheta (z + w) Ω * riemannTheta (z - w) Ω =
      ∑ a : ι → Fin 2, thetaOfOrder 2 (fun i => (a i : ℤ)) z Ω *
        thetaOfOrder 2 (fun i => (a i : ℤ)) w Ω := by
  have hp : (z + w) + (z - w) = (2 : ℂ) • z := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hm : (z + w) - (z - w) = (2 : ℂ) • w := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h := riemannThetaChar_mul_addition hΩ 0 0 0 0 (z + w) (z - w)
  rw [hp, hm] at h
  simpa [thetaOfOrder, riemannThetaChar_zero, two_smul, Pi.smul_def, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using! h

/-- The square of theta is the sum of second-order theta functions weighted by their constants. -/
theorem riemannTheta_sq_eq_sum_thetaOfOrder_two [DecidableEq ι]
    {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) (z : ι → ℂ) :
    riemannTheta z Ω ^ 2 =
      ∑ a : ι → Fin 2, thetaOfOrder 2 (fun i => (a i : ℤ)) z Ω *
        thetaOfOrder 2 (fun i => (a i : ℤ)) 0 Ω := by
  simpa [pow_two] using riemannTheta_add_mul_sub hΩ z 0

/-- The symmetric product with any fixed translate belongs to the space of order-two sections. -/
theorem riemannTheta_add_mul_sub_mem_thetaSectionSpace [DecidableEq ι]
    {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) (w : ι → ℂ) :
    (fun z => riemannTheta (z + w) Ω * riemannTheta (z - w) Ω) ∈ thetaSectionSpace 2 Ω := by
  have heq : (fun z => riemannTheta (z + w) Ω * riemannTheta (z - w) Ω) =
      ∑ a : ι → Fin 2, thetaOfOrder 2 (fun i => (a i : ℤ)) w Ω •
        (fun z => thetaOfOrder 2 (fun i => (a i : ℤ)) z Ω) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [riemannTheta_add_mul_sub hΩ]
    apply Finset.sum_congr rfl
    intro a _ha
    exact mul_comm _ _
  rw [heq]
  apply Submodule.sum_mem
  intro a _ha
  exact Submodule.smul_mem _ _ (thetaOfOrder_mem_thetaSectionSpace 2 (by norm_num) _ hΩ)

end DLMF.RiemannTheta
