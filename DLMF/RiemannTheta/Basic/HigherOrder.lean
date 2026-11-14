/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Basic.Sections
import Mathlib.Tactic

/-!
# Theta functions of higher integral order

Mumford's functions `θ[a/N;0](Nz|NΩ)` are entire sections of order `N`. Their
integer characteristic labels are periodic modulo `N`. Order one recovers the
canonical Riemann theta function. The definition is totalized at `N = 0`; the
positive-order assertions explicitly assume `0 < N`.

References: Mumford, *Tata Lectures on Theta I*, Chapter II, Proposition 1.3;
Igusa, *Theta Functions*, Chapter II, §4.
-/

public noncomputable section

open Complex Matrix
open scoped Real

namespace DLMF.RiemannTheta

variable {ι : Type*} [Fintype ι]

/-- The order-`N` theta function with integer label `a`, normalized as
`θ[a/N;0](Nz|NΩ)`. All quotients and series are totalized; `N > 0` gives the
usual convergent theta function on the Siegel domain. -/
@[expose] def thetaOfOrder (N : ℕ) (a : ι → ℤ) (z : ι → ℂ)
    (Ω : Matrix ι ι ℂ) : ℂ :=
  riemannThetaChar (fun i => (a i : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • Ω)

/-- The characteristic formula defining the higher-order theta functions. -/
theorem thetaOfOrder_def (N : ℕ) (a : ι → ℤ) (z : ι → ℂ) (Ω : Matrix ι ι ℂ) :
    thetaOfOrder N a z Ω =
      riemannThetaChar (fun i => (a i : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • Ω) := rfl

/-- Positive integral scaling preserves the Siegel upper half-space. -/
theorem natCast_smul_mem_siegelUpperHalfSpace (N : ℕ) (hN : 0 < N)
    {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    (N : ℂ) • Ω ∈ siegelUpperHalfSpace ι := by
  refine ⟨by rw [transpose_smul, hΩ.1], ?_⟩
  have him : ((N : ℂ) • Ω).map Complex.im = (N : ℝ) • Ω.map Complex.im := by
    ext i j
    simp [smul_eq_mul, Complex.mul_im]
  rw [him]
  exact hΩ.2.smul (Nat.cast_pos.mpr hN)

/-- Every integer label at order one gives the canonical Riemann theta function. -/
@[simp] theorem thetaOfOrder_one (a : ι → ℤ) (z : ι → ℂ) (Ω : Matrix ι ι ℂ) :
    thetaOfOrder 1 a z Ω = riemannTheta z Ω := by
  have h := riemannThetaChar_add_int (0 : ι → ℝ) 0 z Ω a 0
  simpa [thetaOfOrder, riemannThetaChar_zero] using! h

/-- The higher-order theta functions are jointly entire in the vector argument. -/
theorem differentiable_thetaOfOrder (N : ℕ) (hN : 0 < N) (a : ι → ℤ)
    {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    Differentiable ℂ (fun z => thetaOfOrder N a z Ω) := by
  exact (differentiable_riemannThetaChar _ _
    (natCast_smul_mem_siegelUpperHalfSpace N hN hΩ)).comp
      (differentiable_id.const_smul (N : ℂ))

/-- Shifting the label by an integral multiple of the order leaves the function unchanged. -/
theorem thetaOfOrder_add_order_smul (N : ℕ) (hN : 0 < N) (a k : ι → ℤ)
    (z : ι → ℂ) (Ω : Matrix ι ι ℂ) :
    thetaOfOrder N (a + N • k) z Ω = thetaOfOrder N a z Ω := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have ha : (fun i => ((a + N • k) i : ℝ) / N) =
      (fun i => (a i : ℝ) / N) + fun i => (k i : ℝ) := by
    funext i
    simp only [Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
      Int.cast_add, Int.cast_mul, Int.cast_natCast]
    field_simp [hn]
  have h := riemannThetaChar_add_int (fun i => (a i : ℝ) / N) 0
    ((N : ℂ) • z) ((N : ℂ) • Ω) k 0
  rw [thetaOfOrder, thetaOfOrder, ha]
  simpa using! h

/-- Integral argument translations are genuine periods of the higher-order theta functions. -/
theorem thetaOfOrder_add_int (N : ℕ) (hN : 0 < N) (a m : ι → ℤ)
    (z : ι → ℂ) {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω) :
    thetaOfOrder N a (z + fun i => (m i : ℂ)) Ω = thetaOfOrder N a z Ω := by
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have harg : (N : ℂ) • (z + fun i => (m i : ℂ)) =
      (N : ℂ) • z + fun i => ((N • m) i : ℂ) := by
    ext i
    simp [smul_eq_mul, mul_add]
  have hphase : (fun i => (((a i : ℝ) / N : ℝ) : ℂ)) ⬝ᵥ
      (fun i => ((N • m) i : ℂ)) = ((a ⬝ᵥ m : ℤ) : ℂ) := by
    simp only [dotProduct, Pi.smul_apply, nsmul_eq_mul, Int.cast_sum, Int.cast_mul,
      Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro i _hi
    push_cast
    field_simp [hn]
  have h := riemannThetaChar_add_lattice (Ω := (N : ℂ) • Ω)
    (fun i => (a i : ℝ) / N) 0 ((N : ℂ) • z)
    (by rw [transpose_smul, hΩ]) (N • m) 0
  simp only [Pi.zero_apply, Int.cast_zero, Complex.ofReal_zero, ← Pi.zero_def,
    mulVec_zero, add_zero, zero_dotProduct, dotProduct_zero, mul_zero, sub_zero] at h
  rw [thetaOfOrder, thetaOfOrder, harg, h, hphase, exp_two_pi_I_intCast, one_mul]

/-- Translation by a column-lattice vector has the order-`N` automorphy factor. -/
theorem thetaOfOrder_add_period (N : ℕ) (a m : ι → ℤ) (z : ι → ℂ)
    {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω) :
    thetaOfOrder N a (z + Ω *ᵥ fun i => (m i : ℂ)) Ω =
      thetaAutomorphyFactor N Ω m z * thetaOfOrder N a z Ω := by
  have harg : (N : ℂ) • (z + Ω *ᵥ fun i => (m i : ℂ)) =
      (N : ℂ) • z + ((N : ℂ) • Ω) *ᵥ fun i => (m i : ℂ) := by
    rw [smul_add, smul_mulVec]
  have h := riemannThetaChar_add_lattice (Ω := (N : ℂ) • Ω)
    (fun i => (a i : ℝ) / N) 0 ((N : ℂ) • z)
    (by rw [transpose_smul, hΩ]) 0 m
  simp only [Pi.zero_apply, Int.cast_zero, Complex.ofReal_zero, ← Pi.zero_def,
    add_zero, zero_dotProduct, dotProduct_zero, sub_zero, zero_sub] at h
  rw [thetaOfOrder, thetaOfOrder, harg, h]
  congr 1
  simp only [thetaAutomorphyFactor, smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  ring

/-- Positive-order theta functions are elements of Mumford's theta section space. -/
theorem thetaOfOrder_mem_thetaSectionSpace (N : ℕ) (hN : 0 < N) (a : ι → ℤ)
    {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    (fun z => thetaOfOrder N a z Ω) ∈ thetaSectionSpace N Ω :=
  ⟨differentiable_thetaOfOrder N hN a hΩ,
    fun m z => thetaOfOrder_add_int N hN a m z hΩ.1,
    fun m z => thetaOfOrder_add_period N a m z hΩ.1⟩

/-- Every second-order theta function is even, including at totalized matrix parameters. -/
theorem thetaOfOrder_two_neg (a : ι → ℤ) (z : ι → ℂ) (Ω : Matrix ι ι ℂ) :
    thetaOfOrder 2 a (-z) Ω = thetaOfOrder 2 a z Ω := by
  have h := riemannThetaChar_neg_half a 0 ((2 : ℂ) • z) ((2 : ℂ) • Ω)
  simpa [thetaOfOrder, smul_neg] using! h

end DLMF.RiemannTheta
