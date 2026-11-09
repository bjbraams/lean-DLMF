/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Formal coefficient extraction under an inverse coordinate

The Lagrange–Bürmann coefficient identity follows by applying the formal derivative to
powers of the coordinate's unit factor. Finite coefficient sums allow formal series without
any convergence assumption.
-/

@[expose] public noncomputable section

open Finset

namespace PowerSeries

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

omit [CharZero 𝕜] in
/-- A finite coefficient formula for substitution into a series with zero constant term. -/
theorem coeff_subst_eq_sum_range_of_lt {q : 𝕜⟦X⟧} (hq : constantCoeff q = 0)
    (f : 𝕜⟦X⟧) {n N : ℕ} (hN : n < N) :
    coeff n (f.subst q) = ∑ k ∈ range N, coeff k f * coeff n (q ^ k) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hq)]
  rw [finsum_eq_sum_of_support_subset _ (s := range N)]
  · simp only [smul_eq_mul]
  · intro k hk
    simp only [Function.mem_support, ne_eq, coe_range, Set.mem_Iio] at hk ⊢
    by_contra hkn
    apply hk
    have H : X ^ k ∣ q ^ k := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hq) k
    rw [X_pow_dvd_iff] at H
    rw [H n (by omega), smul_zero]

omit [CharZero 𝕜] in
/-- A finite coefficient formula for a weighted substitution. -/
theorem coeff_mul_subst_eq_sum_range (g q f : 𝕜⟦X⟧) (hq : constantCoeff q = 0) (n : ℕ) :
    coeff n (g * f.subst q) =
      ∑ k ∈ range (n + 1), coeff k f * coeff n (g * q ^ k) := by
  let P : 𝕜⟦X⟧ := ∑ k ∈ range (n + 1), C (coeff k f) * q ^ k
  have hdvd : X ^ (n + 1) ∣ f.subst q - P := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, coeff_subst_eq_sum_range_of_lt hq f hm, map_sum]
    simp only [coeff_C_mul, sub_self]
  obtain ⟨R, hR⟩ := hdvd
  rw [show f.subst q = P + X ^ (n + 1) * R by rw [← hR]; ring, mul_add, map_add,
    mul_left_comm, coeff_X_pow_mul', ite_eq_right (by omega), add_zero, mul_sum, map_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, coeff_C_mul]

/-- Differentiating a positive power cancels its logarithmic derivative coefficient. -/
theorem coeff_pow_sub_X_mul_derivative {Φ : 𝕜⟦X⟧} {m : ℕ} (hm : 0 < m) :
    coeff m (Φ ^ m - X * (derivative Φ * Φ ^ (m - 1))) = 0 := by
  have H := congrArg (coeff (m - 1)) (derivative_pow Φ m)
  rw [coeff_derivative, show m - 1 + 1 = m by omega, mul_assoc,
    coeff_natCast_mul] at H
  have hcast : ((m - 1 : ℕ) : 𝕜) + 1 = (m : 𝕜) := by
    exact_mod_cast (show m - 1 + 1 = m by omega)
  rw [hcast] at H
  rw [map_sub, show X * (derivative Φ * Φ ^ (m - 1)) =
    X ^ 1 * (derivative Φ * Φ ^ (m - 1)) by rw [pow_one], coeff_X_pow_mul',
    ite_eq_left (by omega : 1 ≤ m)]
  have hm' : (m : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have He : coeff (m - 1) (derivative Φ * Φ ^ (m - 1)) = coeff m (Φ ^ m) := by
    apply mul_left_cancel₀ hm'
    rw [mul_comm (derivative Φ)]
    simpa only [mul_comm] using H.symm
  rw [He, sub_self]

/-- The logarithmic Jacobian extracts one coefficient from a power of its coordinate. -/
theorem coeff_lagrangeBurmann_basis {Φ : 𝕜⟦X⟧} (hΦ : constantCoeff Φ ≠ 0)
    {k n : ℕ} (hkn : k ≤ n) :
    coeff n ((1 - X * derivative Φ * Φ⁻¹) * (X * Φ⁻¹) ^ k * Φ ^ n) =
      if k = n then 1 else 0 := by
  have hpow : Φ⁻¹ ^ k * Φ ^ n = Φ ^ (n - k) := by
    conv_lhs => rw [show n = k + (n - k) by omega, pow_add]
    rw [← mul_assoc, PowerSeries.inv_pow,
      PowerSeries.inv_mul_cancel _ (by simpa only [map_pow] using pow_ne_zero k hΦ), one_mul]
  have he : (1 - X * derivative Φ * Φ⁻¹) * (X * Φ⁻¹) ^ k * Φ ^ n =
      X ^ k * (Φ ^ (n - k) - X * (derivative Φ * (Φ⁻¹ * Φ ^ (n - k)))) := by
    rw [mul_pow]
    calc _ = X ^ k * ((1 - X * derivative Φ * Φ⁻¹) * (Φ⁻¹ ^ k * Φ ^ n)) := by ring
      _ = _ := by rw [hpow]; ring
  rw [he, coeff_X_pow_mul', ite_eq_left hkn]
  by_cases hkn' : k = n
  · subst k
    simp only [Nat.sub_self, pow_zero, mul_one, map_sub, map_one,
      coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul, sub_zero,
      ite_true]
  · have hnk : 0 < n - k := by omega
    have hcancel : Φ⁻¹ * Φ ^ (n - k) = Φ ^ (n - k - 1) := by
      conv_lhs => rw [show n - k = 1 + (n - k - 1) by omega, pow_add, pow_one]
      rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hΦ, one_mul]
    rw [hcancel, ite_eq_right hkn']
    exact coeff_pow_sub_X_mul_derivative hnk

/-- The formal Lagrange–Bürmann coefficient identity before solving the coordinate equation. -/
theorem coeff_mul_logarithmicJacobian_subst {Φ A : 𝕜⟦X⟧}
    (hΦ : constantCoeff Φ ≠ 0) (n : ℕ) :
    coeff n ((A.subst (X * Φ⁻¹)) * (1 - X * derivative Φ * Φ⁻¹) * Φ ^ n) = coeff n A := by
  have hH : constantCoeff (X * Φ⁻¹) = 0 := by simp only [map_mul, constantCoeff_X, zero_mul]
  rw [show (A.subst (X * Φ⁻¹)) * (1 - X * derivative Φ * Φ⁻¹) * Φ ^ n =
      ((1 - X * derivative Φ * Φ⁻¹) * Φ ^ n) * (A.subst (X * Φ⁻¹)) by ring,
    coeff_mul_subst_eq_sum_range _ _ _ hH]
  have he (k : ℕ) (hk : k ∈ range (n + 1)) :
      coeff n (((1 - X * derivative Φ * Φ⁻¹) * Φ ^ n) * (X * Φ⁻¹) ^ k) =
        if k = n then 1 else 0 := by
    rw [show ((1 - X * derivative Φ * Φ⁻¹) * Φ ^ n) * (X * Φ⁻¹) ^ k =
      (1 - X * derivative Φ * Φ⁻¹) * (X * Φ⁻¹) ^ k * Φ ^ n by ring]
    exact coeff_lagrangeBurmann_basis hΦ (by simpa only [mem_range, Nat.lt_succ_iff] using hk)
  rw [sum_congr rfl (fun k hk => by rw [he k hk]), sum_eq_single n]
  · simp only [ite_true, mul_one]
  · intro k hk hkn
    simp only [ite_eq_right hkn, mul_zero]
  · intro hn
    exact (hn (mem_range.mpr (Nat.lt_succ_self n))).elim

/-- Formal Bürmann extraction from any inverse of the coordinate `X/Φ`. -/
theorem coeff_subst_inverse_coordinate {Φ T F G : 𝕜⟦X⟧}
    (hΦ : constantCoeff Φ ≠ 0) (hT : constantCoeff T = 0)
    (hTH : T.subst (X * Φ⁻¹) = X)
    (hGF : G * (1 - X * derivative Φ * Φ⁻¹) = F) (n : ℕ) :
    coeff n (G.subst T) = coeff n (F * Φ ^ n) := by
  have hH : constantCoeff (X * Φ⁻¹) = 0 := by simp only [map_mul, constantCoeff_X, zero_mul]
  have hcomp : PowerSeries.subst (X * Φ⁻¹) (PowerSeries.subst T G) = G := by
    rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hT)
      (HasSubst.of_constantCoeff_zero' hH) G, hTH, X_subst G]
  have H := coeff_mul_logarithmicJacobian_subst (A := PowerSeries.subst T G) hΦ n
  rw [hcomp, hGF] at H
  exact H.symm

/-- The logarithmic Jacobian of `X/(1 + X C)` gives the exterior reversion coefficients. -/
theorem natCast_mul_coeff_reversion {C : 𝕜⟦X⟧} {n : ℕ} (hn : 0 < n) :
    (n : 𝕜) * coeff n
      (C * (1 - X * derivative (1 + X * C) * (1 + X * C)⁻¹) *
        (1 + X * C) ^ n) = coeff (n + 1) ((1 + X * C) ^ n) := by
  let Φ : 𝕜⟦X⟧ := 1 + X * C
  have hΦ : constantCoeff Φ ≠ 0 := by simp [Φ]
  have hd : derivative Φ = C + X * derivative C := by simp [Φ, mul_comm]
  have hcancel : Φ⁻¹ * Φ ^ n = Φ ^ (n - 1) := by
    conv_lhs => rw [show n = 1 + (n - 1) by omega, pow_add, pow_one]
    rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hΦ, one_mul]
  have hproduct : derivative (C * Φ ^ n) =
      derivative C * Φ ^ n + (n : 𝕜⟦X⟧) * (C * Φ ^ (n - 1) * derivative Φ) := by
    rw [derivative.leibniz, derivative_pow]
    simp only [smul_eq_mul]
    ring
  have hder := congrArg (coeff (n - 1)) hproduct
  rw [coeff_derivative, show n - 1 + 1 = n by omega,
    map_add, coeff_natCast_mul] at hder
  have hcast : ((n - 1 : ℕ) : 𝕜) + 1 = n := by exact_mod_cast (show n - 1 + 1 = n by omega)
  rw [hcast] at hder
  have hnext := congrArg (coeff n) (derivative_pow Φ (n + 1))
  rw [coeff_derivative, mul_assoc, coeff_natCast_mul] at hnext
  have hnext' : coeff (n + 1) (Φ ^ (n + 1)) = coeff n (Φ ^ n * derivative Φ) := by
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (by omega : n + 1 ≠ 0) :
      ((n + 1 : ℕ) : 𝕜) ≠ 0)
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_comm] using hnext
  have hcoeff : coeff (n + 1) (Φ ^ n) = coeff (n - 1) (derivative C * Φ ^ n) := by
    have he : Φ ^ (n + 1) = Φ ^ n + X * (C * Φ ^ n) := by
      rw [pow_succ]
      change Φ ^ n * (1 + X * C) = _
      ring
    have hX : coeff n (X * (derivative C * Φ ^ n)) =
        coeff (n - 1) (derivative C * Φ ^ n) := by
      rw [show X = X ^ 1 by rw [pow_one], coeff_X_pow_mul', ite_eq_left (by omega)]
    rw [he, map_add, coeff_succ_X_mul, hd, mul_add, map_add,
      show Φ ^ n * (X * derivative C) = X * (derivative C * Φ ^ n) by ring,
      hX, mul_comm (Φ ^ n) C] at hnext'
    linear_combination hnext'
  change (n : 𝕜) * coeff n (C * (1 - X * derivative Φ * Φ⁻¹) * Φ ^ n) = _
  rw [show C * (1 - X * derivative Φ * Φ⁻¹) * Φ ^ n =
    C * Φ ^ n - X * (C * derivative Φ * (Φ⁻¹ * Φ ^ n)) by ring,
    hcancel, map_sub,
    show X * (C * derivative Φ * Φ ^ (n - 1)) =
      X ^ 1 * (C * derivative Φ * Φ ^ (n - 1)) by rw [pow_one],
    coeff_X_pow_mul', ite_eq_left (by omega : 1 ≤ n)]
  rw [hcoeff]
  rw [show C * derivative Φ * Φ ^ (n - 1) = C * Φ ^ (n - 1) * derivative Φ by ring]
  linear_combination hder

end PowerSeries
