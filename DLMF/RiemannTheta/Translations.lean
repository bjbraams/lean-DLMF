/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Basic.Sections
import Mathlib.Tactic

/-!
# Rational theta translations and the Heisenberg commutation relation

Integer vectors specify translation by `p/N` and the compensated translation by
`Ωq/N` on order-`N` theta functions. Their commutator is multiplication by
`exp(2πi p·q/N)`, an `N`-th root of unity. Multiples of `N` act trivially on
theta sections. The definitions act on arbitrary functions; the periodicity
consequences explicitly state section membership and positive order.

References: Mumford, *Tata Lectures on Theta I*, Chapter I, §3 and Chapter II, §1;
Igusa, *Theta Functions*, Chapter I, §3. No new Heisenberg group is defined.
-/

public noncomputable section

open Complex Matrix
open scoped Real

namespace DLMF.RiemannTheta

variable {ι : Type*} [Fintype ι]

/-- Translation by the rational integer-vector period `p/N`. -/
@[expose] def thetaTranslation (N : ℕ) (p : ι → ℤ) (f : (ι → ℂ) → ℂ) :
    (ι → ℂ) → ℂ := fun z => f (z + fun i => (p i : ℂ) / N)

omit [Fintype ι] in
/-- The argument formula for a rational theta translation. -/
theorem thetaTranslation_apply (N : ℕ) (p : ι → ℤ) (f : (ι → ℂ) → ℂ) (z : ι → ℂ) :
    thetaTranslation N p f z = f (z + fun i => (p i : ℂ) / N) := rfl

/-- Compensated translation by `Ωq/N`, with the normalization that cancels the
order-`N` multiplier when `q` is a multiple of `N`. -/
@[expose] def thetaDualTranslation (N : ℕ) (Ω : Matrix ι ι ℂ) (q : ι → ℤ)
    (f : (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ := fun z =>
  exp (2 * π * I * (((fun i => (q i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (q i : ℂ))) / (2 * N) +
    (fun i => (q i : ℂ)) ⬝ᵥ z)) * f (z + Ω *ᵥ fun i => (q i : ℂ) / N)

/-- The exponential and shift formula for a dual theta translation. -/
theorem thetaDualTranslation_apply (N : ℕ) (Ω : Matrix ι ι ℂ) (q : ι → ℤ)
    (f : (ι → ℂ) → ℂ) (z : ι → ℂ) :
    thetaDualTranslation N Ω q f z =
      exp (2 * π * I * (((fun i => (q i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (q i : ℂ))) / (2 * N) +
        (fun i => (q i : ℂ)) ⬝ᵥ z)) * f (z + Ω *ᵥ fun i => (q i : ℂ) / N) := rfl

omit [Fintype ι] in
/-- The zero rational translation is the identity. -/
@[simp] theorem thetaTranslation_zero (N : ℕ) (f : (ι → ℂ) → ℂ) :
    thetaTranslation N 0 f = f := by
  funext z
  simp only [thetaTranslation, Pi.zero_apply, Int.cast_zero, zero_div, ← Pi.zero_def, add_zero]

/-- The zero dual translation is the identity. -/
@[simp] theorem thetaDualTranslation_zero (N : ℕ) (Ω : Matrix ι ι ℂ)
    (f : (ι → ℂ) → ℂ) : thetaDualTranslation N Ω 0 f = f := by
  funext z
  simp only [thetaDualTranslation, Pi.zero_apply, Int.cast_zero, zero_div, ← Pi.zero_def,
    mulVec_zero, zero_dotProduct, mul_zero, Complex.exp_zero, one_mul, add_zero]

omit [Fintype ι] in
/-- Rational translations add their integer labels. -/
theorem thetaTranslation_comp (N : ℕ) (p q : ι → ℤ) (f : (ι → ℂ) → ℂ) :
    thetaTranslation N p (thetaTranslation N q f) = thetaTranslation N (p + q) f := by
  funext z
  dsimp only [thetaTranslation]
  congr 1
  ext i
  simp only [Pi.add_apply, Int.cast_add, add_div]
  ring

/-- The Heisenberg relation between rational and compensated theta translations. -/
theorem thetaTranslation_thetaDualTranslation (N : ℕ) (Ω : Matrix ι ι ℂ)
    (p q : ι → ℤ) (f : (ι → ℂ) → ℂ) :
    thetaTranslation N p (thetaDualTranslation N Ω q f) =
      exp (2 * π * I * ((p ⬝ᵥ q : ℤ) : ℂ) / N) •
        thetaDualTranslation N Ω q (thetaTranslation N p f) := by
  have hd : ((fun i => (q i : ℂ)) ⬝ᵥ fun i => (p i : ℂ) / N) =
      ((p ⬝ᵥ q : ℤ) : ℂ) / N := by
    simp only [dotProduct, Finset.sum_div, Int.cast_sum, Int.cast_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  funext z
  simp only [thetaTranslation, thetaDualTranslation, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  · congr 1
    rw [dotProduct_add, hd]
    ring
  · congr 1
    abel

/-- The scalar in the commutation relation is a root of unity of order dividing `N`. -/
theorem thetaTranslation_commutator_phase_pow (N : ℕ) (hN : 0 < N) (p q : ι → ℤ) :
    exp (2 * π * I * ((p ⬝ᵥ q : ℤ) : ℂ) / N) ^ N = 1 := by
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [← Complex.exp_nat_mul]
  have he : (N : ℂ) * (2 * π * I * ((p ⬝ᵥ q : ℤ) : ℂ) / N) =
      2 * π * I * ((p ⬝ᵥ q : ℤ) : ℂ) := by field_simp [hn]
  rw [he, exp_two_pi_I_intCast]

/-- Integral periods act trivially on theta sections under rational translation. -/
theorem thetaTranslation_order_smul {N : ℕ} (hN : 0 < N) {Ω : Matrix ι ι ℂ}
    {f : (ι → ℂ) → ℂ} (hf : f ∈ thetaSectionSpace N Ω) (m : ι → ℤ) :
    thetaTranslation N (N • m) f = f := by
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hv : (fun i => ((N • m) i : ℂ) / N) = fun i => (m i : ℂ) := by
    ext i
    simp [hn]
  funext z
  rw [thetaTranslation, hv, hf.2.1]

/-- Integral period-matrix translations act trivially after compensation. -/
theorem thetaDualTranslation_order_smul {N : ℕ} (hN : 0 < N) {Ω : Matrix ι ι ℂ}
    {f : (ι → ℂ) → ℂ} (hf : f ∈ thetaSectionSpace N Ω) (m : ι → ℤ) :
    thetaDualTranslation N Ω (N • m) f = f := by
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hv : (fun i => ((N • m) i : ℂ) / N) = fun i => (m i : ℂ) := by
    ext i
    simp [hn]
  have hc : (fun i => ((N • m) i : ℂ)) = (N : ℂ) • fun i => (m i : ℂ) := by
    ext i
    simp [smul_eq_mul]
  funext z
  rw [thetaDualTranslation, hv, hf.2.2, ← mul_assoc, thetaAutomorphyFactor,
    ← Complex.exp_add, hc]
  have he : 2 * π * I *
      (((((N : ℂ) • fun i => (m i : ℂ)) ⬝ᵥ
        (Ω *ᵥ (N : ℂ) • fun i => (m i : ℂ))) / (2 * N)) +
          ((N : ℂ) • fun i => (m i : ℂ)) ⬝ᵥ z) +
        -2 * π * I * N * ((1 / 2 : ℂ) * ((fun i => (m i : ℂ)) ⬝ᵥ
          (Ω *ᵥ fun i => (m i : ℂ))) + (fun i => (m i : ℂ)) ⬝ᵥ z) = 0 := by
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp [hn]
    ring
  rw [he, Complex.exp_zero, one_mul]

end DLMF.RiemannTheta
