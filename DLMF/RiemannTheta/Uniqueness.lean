/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Basic

import DLMFMathlib.Analysis.Fourier.PeriodicMean
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus
import TauCeti.Analysis.Fourier.Monomial
import Mathlib.Tactic

/-!
# Uniqueness from theta quasi-periodicity

The integer and period-matrix quasi-periods determine an entire function as a constant
multiple of the Riemann theta function (DLMF §21.3(i)). Translation invariance of entire
periodic means determines its Fourier coefficients, and Mathlib's unit-torus Fourier
inversion reconstructs the function. TauCeti supplies descent to the unit torus and the
Fourier monomial evaluation formula. The proof includes the zero-dimensional case.
-/

public noncomputable section

open Complex Matrix Finset Set MeasureTheory
open scoped Real

namespace DLMF.RiemannTheta

variable {ι : Type*} [Fintype ι]

/-- The quasi-periodicity 21.3.3 determines the Riemann theta function up to a constant factor:
every entire function with the same multipliers is a constant multiple of `θ(·|Ω)`
(DLMF §21.3(i)). -/
@[dlmf 21.3.i "quasi-periodicity determines θ up to a constant factor"]
theorem eq_const_mul_riemannTheta_of_quasiPeriodic {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (hper : ∀ (m₁ m₂ : ι → ℤ) (z : ι → ℂ),
      f (z + (fun i => (m₁ i : ℂ)) + Ω *ᵥ fun i => (m₂ i : ℂ)) =
        cexp (-2 * π * I * ((1 / 2 : ℂ) * ((fun i => (m₂ i : ℂ)) ⬝ᵥ
          (Ω *ᵥ fun i => (m₂ i : ℂ))) + (fun i => (m₂ i : ℂ)) ⬝ᵥ z)) * f z) :
    ∃ c : ℂ, ∀ z, f z = c * riemannTheta z Ω := by
  classical
  let B : Set (ι → ℝ) := {u | ∀ i, u i ∈ Ioc (0 : ℝ) 1}
  let c : ℂ := ∫ u : ι → ℝ in B, f (fun i => (u i : ℂ))
  have hp (m : ι → ℤ) (z : ι → ℂ) :
      f (z + fun i => (m i : ℂ)) = f z := by
    simpa only [Pi.zero_apply, Int.cast_zero, ← Pi.zero_def, mulVec_zero, add_zero,
      zero_dotProduct, mul_zero, Complex.exp_zero, one_mul] using hper m 0 z
  let F (n : ι → ℤ) (z : ι → ℂ) : ℂ :=
    cexp (-2 * π * I * ((fun i => (n i : ℂ)) ⬝ᵥ z)) * f z
  have hFdiff (n : ι → ℤ) : Differentiable ℂ (F n) := by
    apply Differentiable.mul _ hf
    apply Differentiable.cexp
    dsimp only [dotProduct]
    fun_prop
  have hFp (n m : ι → ℤ) (z : ι → ℂ) :
      F n (z + fun i => (m i : ℂ)) = F n z := by
    dsimp only [F]
    rw [hp, dotProduct_add, mul_add, Complex.exp_add]
    have hcast : (fun i => (n i : ℂ)) ⬝ᵥ (fun i => (m i : ℂ)) =
        ((n ⬝ᵥ m : ℤ) : ℂ) := by simp [dotProduct]
    rw [hcast]
    have he : cexp (-2 * π * I * ((n ⬝ᵥ m : ℤ) : ℂ)) = 1 := by
      have hphase : -2 * (π : ℂ) * I * ((n ⬝ᵥ m : ℤ) : ℂ) =
          ((-(n ⬝ᵥ m) : ℤ) : ℂ) * (2 * π * I) := by push_cast; ring_nf
      rw [hphase]
      exact Complex.exp_int_mul_two_pi_mul_I (-(n ⬝ᵥ m))
    rw [he, mul_one]
  have hFn (n : ι → ℤ) :
      (∫ u : ι → ℝ in B, F n (fun i => (u i : ℂ))) =
        c * cexp (π * I * ((fun i => (n i : ℂ)) ⬝ᵥ
          (Ω *ᵥ fun i => (n i : ℂ)))) := by
    have hid (z : ι → ℂ) : F n z =
        cexp (π * I * ((fun i => (n i : ℂ)) ⬝ᵥ
          (Ω *ᵥ fun i => (n i : ℂ)))) *
          f (z + Ω *ᵥ fun i => (n i : ℂ)) := by
      have h0 := hper 0 n z
      simp only [Pi.zero_apply, Int.cast_zero, ← Pi.zero_def, add_zero] at h0
      rw [h0]
      dsimp only [F]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      ring_nf
    simp_rw [hid]
    rw [integral_const_mul, Complex.setIntegral_unitCube_add_complex_of_periodic hf hp]
    exact mul_comm _ _
  refine ⟨c, fun w => ?_⟩
  have htrace : Continuous (fun u : ι → ℝ => f ((fun i => (u i : ℂ)) + w)) :=
    hf.continuous.comp (by fun_prop)
  have htper (m : ι → ℤ) : Function.Periodic
      (fun u : ι → ℝ => f ((fun i => (u i : ℂ)) + w)) (fun i => (m i : ℝ)) := by
    intro u
    convert hp m ((fun i => (u i : ℂ)) + w) using 1
    dsimp only
    congr 1
    funext i
    simp only [Pi.add_apply, ofReal_add, ofReal_intCast]
    ring_nf
  obtain ⟨g, hgcont, hg⟩ :=
    TauCeti.UnitAddTorus.exists_continuous_comp_coe_eq htrace htper
  let G : C(UnitAddTorus ι, ℂ) := ⟨g, hgcont⟩
  have hcoeff (n : ι → ℤ) : UnitAddTorus.mFourierCoeff G n = c * riemannThetaTerm w Ω n := by
    have hchar (u : ι → ℝ) :
        UnitAddTorus.mFourier (-n) (fun i => (u i : UnitAddCircle)) =
          cexp (-2 * π * I * ((fun i => (n i : ℂ)) ⬝ᵥ fun i => (u i : ℂ))) := by
      rw [TauCeti.UnitAddTorus.mFourier_coe_apply]
      congr 1
      simp only [Pi.neg_apply, Int.cast_neg, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring_nf
    rw [UnitAddTorus.mFourierCoeff_eq_integral G n (0 : ι → ℝ)]
    simp only [Pi.zero_apply, zero_add, hchar, G, ContinuousMap.coe_mk, hg, smul_eq_mul]
    have he (u : ι → ℝ) :
        cexp (-2 * π * I * ((fun i => (n i : ℂ)) ⬝ᵥ fun i => (u i : ℂ))) *
          f ((fun i => (u i : ℂ)) + w) =
        cexp (2 * π * I * ((fun i => (n i : ℂ)) ⬝ᵥ w)) *
          F n ((fun i => (u i : ℂ)) + w) := by
      dsimp only [F]
      rw [← mul_assoc, ← Complex.exp_add, dotProduct_add]
      congr 2
      ring_nf
    simp_rw [he]
    rw [integral_const_mul,
      Complex.setIntegral_unitCube_add_complex_of_periodic (hFdiff n) (hFp n), hFn]
    dsimp only [riemannThetaTerm]
    rw [mul_left_comm, mul_assoc, ← Complex.exp_add]
    congr 1
    ring_nf
  have hsum : Summable (UnitAddTorus.mFourierCoeff G) := by
    exact ((summable_norm_riemannThetaTerm w hΩ).of_norm.mul_left c).congr
      (fun n => (hcoeff n).symm)
  have hs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum (0 : UnitAddTorus ι)
  have hz : ∀ n : ι → ℤ, UnitAddTorus.mFourier n (0 : UnitAddTorus ι) = 1 := by
    intro n
    simp [UnitAddTorus.mFourier]
  simp_rw [hz, smul_eq_mul, mul_one, hcoeff] at hs
  have ht := (hasSum_riemannTheta w hΩ).mul_left c
  have heq := hs.unique ht
  have hzG : G 0 = f w := by
    simpa [G, ← Pi.zero_def] using hg 0
  rw [hzG] at heq
  exact heq

end DLMF.RiemannTheta
