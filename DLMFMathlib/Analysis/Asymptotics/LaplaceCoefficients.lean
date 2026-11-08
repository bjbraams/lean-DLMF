/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.RamifiedPowerSeries
public import DLMFMathlib.RingTheory.PowerSeries.LagrangeBurmann

/-!
# Formal powers and coefficients of ramified inverse coordinates

For a formal series `P` with nonzero constant coefficient and a logarithm `L` of that
coefficient, its `β`-th power is defined by the binomial series normalized at `P(0)`.
Formal differentiation and Lagrange–Bürmann extraction identify the coefficients of
weighted densities under the coordinate `v=t^μ P(t)`.
-/

@[expose] public noncomputable section

open Finset PowerSeries

namespace PowerSeries

/-- The formal power of a series with a chosen logarithm of its constant coefficient. -/
def logarithmicPower (P : ℂ⟦X⟧) (L β : ℂ) : ℂ⟦X⟧ :=
  C (Complex.exp (β * L)) * binomialSubstitution (C (constantCoeff P)⁻¹ * P - 1) β

/-- The normalized nonconstant part of a unit series has zero constant coefficient. -/
theorem constantCoeff_normalized_sub_one {P : ℂ⟦X⟧} (hP : constantCoeff P ≠ 0) :
    constantCoeff (C (constantCoeff P)⁻¹ * P - 1) = 0 := by
  simp only [map_sub, map_mul, constantCoeff_C, map_one, inv_mul_cancel₀ hP, sub_self]

/-- The constant coefficient of a logarithmic power. -/
theorem constantCoeff_logarithmicPower {P : ℂ⟦X⟧} (hP : constantCoeff P ≠ 0) (L β : ℂ) :
    constantCoeff (logarithmicPower P L β) = Complex.exp (β * L) := by
  have hB : constantCoeff (binomialSubstitution (C (constantCoeff P)⁻¹ * P - 1) β) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply,
      coeff_binomialSubstitution (constantCoeff_normalized_sub_one hP)]
    norm_num only [Nat.zero_add, range_one, sum_singleton, Ring.choose_zero_right, pow_zero,
      coeff_one, ite_true, mul_one]
  rw [logarithmicPower, map_mul, constantCoeff_C, hB, mul_one]

/-- Adding exponents multiplies logarithmic powers. -/
theorem logarithmicPower_add {P : ℂ⟦X⟧} (hP : constantCoeff P ≠ 0) (L β γ : ℂ) :
    logarithmicPower P L (β + γ) = logarithmicPower P L β * logarithmicPower P L γ := by
  simp only [logarithmicPower, add_mul, Complex.exp_add, map_mul,
    binomialSubstitution_add (constantCoeff_normalized_sub_one hP)]
  ring

/-- The zeroth logarithmic power is one. -/
theorem logarithmicPower_zero {P : ℂ⟦X⟧} (hP : constantCoeff P ≠ 0) (L : ℂ) :
    logarithmicPower P L 0 = 1 := by
  rw [logarithmicPower, zero_mul, Complex.exp_zero, map_one,
    binomialSubstitution_zero (constantCoeff_normalized_sub_one hP), mul_one]

/-- The first logarithmic power recovers the series for the prescribed logarithm. -/
theorem logarithmicPower_one {P : ℂ⟦X⟧} {L : ℂ} (hL : Complex.exp L = constantCoeff P) :
    logarithmicPower P L 1 = P := by
  have hP : constantCoeff P ≠ 0 := hL ▸ Complex.exp_ne_zero L
  rw [logarithmicPower, one_mul, hL,
    binomialSubstitution_one (constantCoeff_normalized_sub_one hP)]
  rw [show (1 : ℂ⟦X⟧) + (C (constantCoeff P)⁻¹ * P - 1) =
    C (constantCoeff P)⁻¹ * P by ring, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hP,
    map_one, one_mul]

/-- Negating an exponent inverts the logarithmic power. -/
theorem logarithmicPower_neg {P : ℂ⟦X⟧} (hP : constantCoeff P ≠ 0) (L β : ℂ) :
    logarithmicPower P L (-β) = (logarithmicPower P L β)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by
    rw [constantCoeff_logarithmicPower hP]; exact Complex.exp_ne_zero _)).mpr
  rw [← logarithmicPower_add hP, neg_add_cancel, logarithmicPower_zero hP]

/-- Natural powers multiply the logarithmic exponent. -/
theorem logarithmicPower_mul_natCast {P : ℂ⟦X⟧} (hP : constantCoeff P ≠ 0) (L β : ℂ) (n : ℕ) :
    logarithmicPower P L (β * n) = logarithmicPower P L β ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero, logarithmicPower_zero hP, pow_zero]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, logarithmicPower_add hP, ih, pow_succ]

/-- The formal chain rule for logarithmic powers. -/
theorem derivative_logarithmicPower {P : ℂ⟦X⟧} {L : ℂ}
    (hL : Complex.exp L = constantCoeff P) (β : ℂ) :
    derivative (logarithmicPower P L β) =
      C β * logarithmicPower P L (β - 1) * derivative P := by
  have hP : constantCoeff P ≠ 0 := hL ▸ Complex.exp_ne_zero L
  have hc : Complex.exp (β * L) * (constantCoeff P)⁻¹ = Complex.exp ((β - 1) * L) := by
    rw [← hL, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    ring
  rw [logarithmicPower, derivative.leibniz]
  simp only [derivative_C, smul_eq_mul, mul_zero, add_zero]
  rw [derivative_binomialSubstitution (constantCoeff_normalized_sub_one hP),
    map_sub, derivative.leibniz]
  simp only [derivative_C, derivative_one, smul_eq_mul, mul_zero, add_zero, sub_zero]
  dsimp only [logarithmicPower]
  calc _ = C β * C (Complex.exp (β * L) * (constantCoeff P)⁻¹) *
      binomialSubstitution (C (constantCoeff P)⁻¹ * P - 1) (β - 1) * derivative P := by
        rw [map_mul]
        ring
    _ = _ := by rw [hc]; ring

/-- The logarithmic Jacobian of the ramified inverse coordinate. -/
theorem logarithmicJacobian_logarithmicPower {P : ℂ⟦X⟧} {L μ : ℂ}
    (hL : Complex.exp L = constantCoeff P) (hμ : μ ≠ 0) :
    1 - X * derivative (logarithmicPower P L (-μ⁻¹)) *
      (logarithmicPower P L (-μ⁻¹))⁻¹ =
        (C μ * P + X * derivative P) * C μ⁻¹ * P⁻¹ := by
  have hP : constantCoeff P ≠ 0 := hL ▸ Complex.exp_ne_zero L
  have hcombine : logarithmicPower P L (-μ⁻¹ - 1) *
      (logarithmicPower P L (-μ⁻¹))⁻¹ = P⁻¹ := by
    rw [← logarithmicPower_neg hP, ← logarithmicPower_add hP,
      show -μ⁻¹ - 1 + -(-μ⁻¹) = -1 by ring,
      logarithmicPower_neg hP, logarithmicPower_one hL]
  rw [derivative_logarithmicPower hL]
  calc _ = 1 - X * C (-μ⁻¹) * derivative P *
        (logarithmicPower P L (-μ⁻¹ - 1) *
          (logarithmicPower P L (-μ⁻¹))⁻¹) := by ring
    _ = 1 + X * derivative P * C μ⁻¹ * P⁻¹ := by rw [hcombine, map_neg]; ring
    _ = _ := by
      have H : C μ * P * C μ⁻¹ * P⁻¹ = 1 := by
        calc _ = (C μ * C μ⁻¹) * (P * P⁻¹) := by ring
          _ = 1 := by rw [← map_mul, mul_inv_cancel₀ hμ, map_one,
            PowerSeries.mul_inv_cancel _ hP, one_mul]
      rw [add_mul, add_mul, H]

/-- The weighted density times its inverse-coordinate Jacobian has a simpler power. -/
theorem weightedDensity_mul_logarithmicJacobian {P Q : ℂ⟦X⟧} {L lam μ : ℂ}
    (hL : Complex.exp L = constantCoeff P) (hμ : μ ≠ 0) :
    (Q * (C μ * P + X * derivative P)⁻¹ * logarithmicPower P L (1 - lam / μ)) *
      (1 - X * derivative (logarithmicPower P L (-μ⁻¹)) *
        (logarithmicPower P L (-μ⁻¹))⁻¹) = C μ⁻¹ * Q * logarithmicPower P L (-lam / μ) := by
  have hP : constantCoeff P ≠ 0 := hL ▸ Complex.exp_ne_zero L
  let D : ℂ⟦X⟧ := C μ * P + X * derivative P
  have hD : constantCoeff D ≠ 0 := by
    simp only [D, map_add, map_mul, constantCoeff_C, constantCoeff_X, zero_mul, add_zero]
    exact mul_ne_zero hμ hP
  rw [logarithmicJacobian_logarithmicPower hL hμ]
  change (Q * D⁻¹ * logarithmicPower P L (1 - lam / μ)) *
    (D * C μ⁻¹ * P⁻¹) = _
  calc _ = C μ⁻¹ * Q * (D⁻¹ * D) * (logarithmicPower P L (1 - lam / μ) * P⁻¹) := by ring
    _ = C μ⁻¹ * Q * logarithmicPower P L (-lam / μ) := by
      have hPi : P⁻¹ = logarithmicPower P L (-1) := by
        rw [logarithmicPower_neg hP, logarithmicPower_one hL]
      rw [PowerSeries.inv_mul_cancel _ hD, mul_one, hPi,
        ← logarithmicPower_add hP, show 1 - lam / μ + -1 = -lam / μ by ring]

/-- Finite convolution formula for multiplying an amplitude by a logarithmic power. -/
theorem coeff_mul_logarithmicPower {P Q : ℂ⟦X⟧} (hP : constantCoeff P ≠ 0)
    (L β : ℂ) (n : ℕ) :
    coeff n (Q * logarithmicPower P L β) = Complex.exp (β * L) *
      ∑ j ∈ range (n + 1), coeff j Q *
        ∑ k ∈ range (n - j + 1), Ring.choose β k *
          coeff (n - j) ((C (constantCoeff P)⁻¹ * P - 1) ^ k) := by
  rw [logarithmicPower, show Q * (C (Complex.exp (β * L)) *
      binomialSubstitution (C (constantCoeff P)⁻¹ * P - 1) β) =
        C (Complex.exp (β * L)) * (Q * binomialSubstitution
          (C (constantCoeff P)⁻¹ * P - 1) β) by ring,
    coeff_C_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [coeff_binomialSubstitution (constantCoeff_normalized_sub_one hP)]

/-- Coefficients of a weighted density after reverting its ramified coordinate. -/
theorem coeff_weightedDensity_subst_inverse {P Q T : ℂ⟦X⟧} {L lam μ : ℂ}
    (hL : Complex.exp L = constantCoeff P) (hμ : μ ≠ 0) (hT : constantCoeff T = 0)
    (hTH : T.subst (X * (logarithmicPower P L (-μ⁻¹))⁻¹) = X) (n : ℕ) :
    coeff n ((Q * (C μ * P + X * derivative P)⁻¹ *
        logarithmicPower P L (1 - lam / μ)).subst T) =
      μ⁻¹ * Complex.exp (-((lam + n) / μ) * L) *
        coeff n (Q * binomialSubstitution (C (constantCoeff P)⁻¹ * P - 1) (-((lam + n) / μ))) := by
  have hP : constantCoeff P ≠ 0 := hL ▸ Complex.exp_ne_zero L
  let Φ : ℂ⟦X⟧ := logarithmicPower P L (-μ⁻¹)
  let J := 1 - X * derivative Φ * Φ⁻¹
  let G := Q * (C μ * P + X * derivative P)⁻¹ * logarithmicPower P L (1 - lam / μ)
  have hΦ : constantCoeff Φ ≠ 0 := by
    change constantCoeff (logarithmicPower P L (-μ⁻¹)) ≠ 0
    rw [constantCoeff_logarithmicPower hP]
    exact Complex.exp_ne_zero _
  have hGJ : G * J = C μ⁻¹ * Q * logarithmicPower P L (-lam / μ) :=
    weightedDensity_mul_logarithmicJacobian hL hμ
  have H := coeff_subst_inverse_coordinate hΦ hT hTH hGJ n
  have hprod : (C μ⁻¹ * Q * logarithmicPower P L (-lam / μ)) * Φ ^ n =
      C μ⁻¹ * Q * logarithmicPower P L (-((lam + n) / μ)) := by
    change (C μ⁻¹ * Q * logarithmicPower P L (-lam / μ)) *
      logarithmicPower P L (-μ⁻¹) ^ n = _
    rw [← logarithmicPower_mul_natCast hP]
    rw [mul_assoc (C μ⁻¹ * Q), ← logarithmicPower_add hP]
    congr 2
    field_simp
    ring
  rw [hprod] at H
  rw [H, logarithmicPower]
  rw [show C μ⁻¹ * Q * (C (Complex.exp (-((lam + n) / μ) * L)) *
      binomialSubstitution (C (constantCoeff P)⁻¹ * P - 1) (-((lam + n) / μ))) =
        C (μ⁻¹ * Complex.exp (-((lam + n) / μ) * L)) *
          (Q * binomialSubstitution (C (constantCoeff P)⁻¹ * P - 1) (-((lam + n) / μ))) by
            rw [map_mul]; ring,
    coeff_C_mul]

/-- Real binomial powers agree with complex logarithmic powers at positive constant terms. -/
theorem map_realPower_eq_logarithmicPower {P : ℝ⟦X⟧} (hP : 0 < constantCoeff P) (β : ℝ) :
    PowerSeries.map Complex.ofRealHom (realPower P β) =
      logarithmicPower (PowerSeries.map Complex.ofRealHom P)
        (Real.log (constantCoeff P)) β := by
  have hnorm : constantCoeff (C (constantCoeff P)⁻¹ * P - 1) = 0 := by
    simp only [map_sub, map_mul, constantCoeff_C, map_one, inv_mul_cancel₀ hP.ne', sub_self]
  have hc : ((constantCoeff P ^ β : ℝ) : ℂ) =
      Complex.exp ((β : ℂ) * (Real.log (constantCoeff P) : ℂ)) := by
    rw [Real.rpow_def_of_pos hP, Complex.ofReal_exp, Complex.ofReal_mul]
    congr 1
    ring
  rw [realPower, map_mul, map_C, map_binomialSubstitution Complex.ofRealHom hnorm]
  change C ((constantCoeff P ^ β : ℝ) : ℂ) *
    binomialSubstitution (PowerSeries.map Complex.ofRealHom (C (constantCoeff P)⁻¹ * P - 1))
      (β : ℂ) = _
  rw [hc, map_sub, map_mul, map_C, map_one]
  have hcoeff : constantCoeff (PowerSeries.map Complex.ofRealHom P) =
      Complex.ofRealHom (constantCoeff P) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
  rw [logarithmicPower, hcoeff, map_inv₀]


end PowerSeries
