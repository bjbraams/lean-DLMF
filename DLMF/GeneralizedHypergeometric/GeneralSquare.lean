/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Clausen
public import DLMF.GeneralizedHypergeometric.Basic.ParametersAndSeries
import DLMF.Hypergeometric.Elementary.AlgebraicValues
import DLMF.Hypergeometric.Saalschutz
import Mathlib.Tactic.LinearCombination

/-!
# Coefficients of the square of the Gauss series

The symmetric square of the Gauss differential equation gives the three-term
coefficient recurrence underlying DLMF 16.12.3. A finite telescoping certificate
identifies the terminating four-over-three expression with the square coefficients.

## Main results

* `DLMF.Hypergeometric.gaussPS_square_recurrence`: the general symmetric-square recurrence.
* `DLMF.Hypergeometric.GeneralSquare.coeff_gaussPS_square`: the finite coefficient identity.

## Implementation notes

The formal differential-operator argument follows the method in
`DLMF.Hypergeometric.Clausen`. The finite kernel cancels numerator and denominator
factors polynomially before telescoping, retaining integral upper parameters and
lower exceptions after termination.
-/

public noncomputable section
open PowerSeries Complex
open scoped Nat Real
namespace DLMF.Hypergeometric

/-- The square of the formal Gauss series satisfies its symmetric-square recurrence. -/
theorem gaussPS_square_recurrence {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    ((n : ℂ) + 2) * (c + n + 1) * (2 * c + n) *
        coeff (n + 2) (gaussPS a b c * gaussPS a b c) -
      (4 * a * b * c + 4 * a * b * (n + 1) - 2 * a * b +
        4 * a * c * (n + 1) + 3 * a * (n + 1) ^ 2 - 3 * a * (n + 1) +
        4 * b * c * (n + 1) + 3 * b * (n + 1) ^ 2 - 3 * b * (n + 1) +
        3 * c * (n + 1) ^ 2 - c * (n + 1) + 2 * (n + 1) ^ 3 -
        3 * (n + 1) ^ 2 + (n + 1)) *
          coeff (n + 1) (gaussPS a b c * gaussPS a b c) +
      (2 * a + n) * (2 * b + n) * (a + b + n) *
        coeff n (gaussPS a b c * gaussPS a b c) = 0 := by
  let f := gaussPS a b c
  let f1 := thetaPS f
  let f2 := thetaPS f1
  let f3 := thetaPS f2
  let w := f * f
  have E := gaussPS_ode (a := a) (b := b) hc
  have E1 := congrArg thetaPS E
  simp only [thetaPS_add, thetaPS_sub, thetaPS_C_mul, thetaPS_X_mul] at E1
  rw [show thetaPS (0 : PowerSeries ℂ) = 0 by ext i; simp] at E1
  have w1 : thetaPS w = 2 * f * f1 := by rw [thetaPS_mul]; ring
  have w2 : thetaPS (thetaPS w) = 2 * f1 * f1 + 2 * f * f2 := by
    rw [w1, show (2 : PowerSeries ℂ) * f * f1 = C 2 * (f * f1) by
      simp only [map_ofNat]; ring, thetaPS_C_mul, thetaPS_mul]
    simp only [map_ofNat]
    ring
  have w3 : thetaPS (thetaPS (thetaPS w)) = 6 * f1 * f2 + 2 * f * f3 := by
    rw [w2, show (2 : PowerSeries ℂ) * f1 * f1 + 2 * f * f2 =
        C 2 * (f1 * f1) + C 2 * (f * f2) by simp only [map_ofNat]; ring,
      thetaPS_add, thetaPS_C_mul, thetaPS_C_mul, thetaPS_mul, thetaPS_mul]
    simp only [map_ofNat]
    ring
  have T :
      thetaPS (thetaPS (thetaPS w)) + C (3 * c - 3) * thetaPS (thetaPS w) +
        C ((c - 1) * (2 * c - 2)) * thetaPS w -
      X * (2 * thetaPS (thetaPS (thetaPS w)) + C (3 * a + 3 * b + 3 * c - 3) *
        thetaPS (thetaPS w) + C (4 * a * b + 4 * a * c - 3 * a + 4 * b * c - 3 * b - c + 1) *
        thetaPS w + C (4 * a * b * c - 2 * a * b) * w) +
      X * X * (thetaPS (thetaPS (thetaPS w)) + C (3 * a + 3 * b) *
        thetaPS (thetaPS w) + C (2 * a ^ 2 + 8 * a * b + 2 * b ^ 2) * thetaPS w +
        C (4 * a * b * (a + b)) * w) = 0 := by
    rw [w3, w2, w1]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one] at E E1 ⊢
    linear_combination (2 * (1 - X) * f) * E1 +
      (6 * (1 - X) * f1 + (4 * (C c - 1 - X * (C a + C b)) + 2 * X) * f) * E
  have hT := congrArg (coeff (n + 2)) T
  simp only [LinearMap.map_add, LinearMap.map_sub, coeff_thetaPS, coeff_C_mul,
    mul_assoc, coeff_succ_X_mul, map_zero, coeff_ofNat_mul] at hT
  push_cast at hT
  linear_combination hT

end DLMF.Hypergeometric

namespace DLMF.Hypergeometric.GeneralSquare

/-- The middle coefficient in the symmetric-square recurrence. -/
private def middleFactor (a b c t : ℂ) : ℂ :=
  4 * a * b * c + 4 * a * b * t - 2 * a * b + 4 * a * c * t +
    3 * a * t ^ 2 - 3 * a * t + 4 * b * c * t + 3 * b * t ^ 2 - 3 * b * t +
    3 * c * t ^ 2 - c * t + 2 * t ^ 3 - 3 * t ^ 2 + t

/-- The polynomially cancelled finite kernel of the square coefficient. -/
private def kernel (a b c : ℂ) (n j : ℕ) : ℂ :=
  if 2 * j ≤ n then
    (-1) ^ j * pochhammer a j * pochhammer b j * pochhammer (a + b - c + 1 / 2) j *
      pochhammer (c - 1 / 2) (n - j) * pochhammer (2 * a + 2 * j) (n - 2 * j) *
      pochhammer (2 * b + 2 * j) (n - 2 * j) * (2 * j).factorial /
      ((n - 2 * j).factorial * (j.factorial : ℂ) ^ 2)
  else 0

/-- The finite telescoping certificate for the square coefficient. -/
private def certificate (a b c : ℂ) (n j : ℕ) : ℂ :=
  if 2 * j ≤ n + 2 then
    -(j : ℂ) * (2 * c + n - 1) * (-1) ^ j * pochhammer a j * pochhammer b j *
      pochhammer (a + b - c + 1 / 2) j * pochhammer (c - 1 / 2) (n + 1 - j) *
      pochhammer (2 * a + 2 * j - 1) (n + 2 - 2 * j) *
      pochhammer (2 * b + 2 * j - 1) (n + 2 - 2 * j) * (2 * j).factorial /
      ((n + 2 - 2 * j).factorial * (j.factorial : ℂ) ^ 2)
  else 0

/-- A simultaneous shift of the two doubled upper rising factorials. -/
private lemma shifted_pair (a b : ℂ) (j m : ℕ) :
    (a + j) * (b + j) * pochhammer (2 * a + 2 * j + 1) m *
      pochhammer (2 * b + 2 * j + 1) m =
      (2 * a + 2 * j + m) * (2 * b + 2 * j + m) / 4 *
        pochhammer (2 * a + 2 * j) m * pochhammer (2 * b + 2 * j) m := by
  calc _ = (1 / 4 : ℂ) * ((2 * a + 2 * j) * pochhammer (2 * a + 2 * j + 1) m) *
      ((2 * b + 2 * j) * pochhammer (2 * b + 2 * j + 1) m) := by ring
    _ = _ := by rw [pochhammer_succ_left_mul, pochhammer_succ_left_mul]; ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The certificate telescopes where all three finite kernels are supported. -/
private lemma kernel_telescope_interior (a b c : ℂ) (n j : ℕ) (hj : 2 * j ≤ n) :
    ((n : ℂ) + 2) * kernel a b c (n + 2) j -
      middleFactor a b c (n + 1) * kernel a b c (n + 1) j +
      (2 * a + n) * (2 * b + n) * (a + b + n) * (c + n) * (2 * c + n - 1) *
        kernel a b c n j = certificate a b c n (j + 1) - certificate a b c n j := by
  have hj1 : 2 * j ≤ n + 1 := by omega
  have hj2 : 2 * j ≤ n + 2 := by omega
  have hj3 : 2 * (j + 1) ≤ n + 2 := by omega
  simp only [kernel, certificate, ite_eq_left hj, ite_eq_left hj1, ite_eq_left hj2, ite_eq_left hj3]
  have hn1 : n + 1 - 2 * j = (n - 2 * j) + 1 := by omega
  have hn2 : n + 2 - 2 * j = (n - 2 * j) + 1 + 1 := by omega
  have hn3 : n + 2 - 2 * (j + 1) = n - 2 * j := by omega
  have hc1 : n + 1 - j = (n - j) + 1 := by omega
  have hc2 : n + 2 - j = (n - j) + 1 + 1 := by omega
  have hc3 : n + 1 - (j + 1) = n - j := by omega
  rw [hn1, hn2, hn3, hc1, hc2, hc3]
  have haShift : 2 * a + 2 * (j + 1 : ℕ) - 1 = 2 * a + 2 * j + 1 := by push_cast; ring
  have hbShift : 2 * b + 2 * (j + 1 : ℕ) - 1 = 2 * b + 2 * j + 1 := by push_cast; ring
  have haStart : 2 * a + 2 * j - 1 + 1 = 2 * a + 2 * j := by ring
  have hbStart : 2 * b + 2 * j - 1 + 1 = 2 * b + 2 * j := by ring
  rw [haShift, hbShift,
    pochhammer_succ_left (2 * a + 2 * j - 1) ((n - 2 * j) + 1),
    pochhammer_succ_left (2 * b + 2 * j - 1) ((n - 2 * j) + 1), haStart, hbStart]
  simp only [pochhammer_succ, Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  have hp := shifted_pair a b j (n - 2 * j)
  push_cast [Nat.cast_sub hj] at hp
  have hJ : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hM : ((n - 2 * j).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (n - 2 * j).factorial_ne_zero
  have hm1 : ((n - 2 * j : ℕ) : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (n - 2 * j)
  have hm2 : ((n - 2 * j : ℕ) : ℂ) + 1 + 1 ≠ 0 := by
    exact_mod_cast (n - 2 * j + 1).succ_ne_zero
  have hj0 : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast j.succ_ne_zero
  have h2j : (2 * (j + 1)).factorial = (2 * j + 1 + 1).factorial := by congr 1
  rw [h2j]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  generalize pochhammer a j = P at *
  generalize pochhammer b j = Q at *
  generalize pochhammer (a + b - c + 1 / 2) j = R at *
  generalize pochhammer (c - 1 / 2) (n - j) = S at *
  generalize pochhammer (2 * a + 2 * j) (n - 2 * j) = U at *
  generalize pochhammer (2 * b + 2 * j) (n - 2 * j) = V at *
  generalize pochhammer (2 * a + 2 * j + 1) (n - 2 * j) = U1 at *
  generalize pochhammer (2 * b + 2 * j + 1) (n - 2 * j) = V1 at *
  field_simp [hJ, hM, hm1, hm2, hj0]
  simp only [middleFactor]
  have hjn : j ≤ n := by omega
  push_cast [Nat.cast_sub hj, Nat.cast_sub hjn] at *
  linear_combination
    (-8 * ((n : ℂ) - 2 * j + 1) * ((n : ℂ) - 2 * j + 2) *
      P * Q * R * S * (2 * j).factorial *
      (a + b - c + 1 / 2 + j) * (2 * c + n - 1) * (2 * j + 1) * (j + 1)) * hp

/-- The certificate identity at the penultimate support boundary. -/
private lemma kernel_telescope_boundary_one (a b c : ℂ) (n j : ℕ)
    (hj : 2 * j = n + 1) :
    ((n : ℂ) + 2) * kernel a b c (n + 2) j -
      middleFactor a b c (n + 1) * kernel a b c (n + 1) j +
      (2 * a + n) * (2 * b + n) * (a + b + n) * (c + n) * (2 * c + n - 1) *
        kernel a b c n j = certificate a b c n (j + 1) - certificate a b c n j := by
  have hj0 : ¬2 * j ≤ n := by omega
  have hj1 : 2 * j ≤ n + 1 := by omega
  have hj2 : 2 * j ≤ n + 2 := by omega
  have hj3 : ¬2 * (j + 1) ≤ n + 2 := by omega
  simp only [kernel, certificate, ite_eq_right hj0, ite_eq_left hj1, ite_eq_left hj2,
    ite_eq_right hj3, mul_zero, add_zero, zero_sub]
  have hn1 : n + 1 - 2 * j = 0 := by omega
  have hn2 : n + 2 - 2 * j = 1 := by omega
  have hc1 : n + 1 - j = j := by omega
  have hc2 : n + 2 - j = j + 1 := by omega
  rw [hn1, hn2, hc1, hc2]
  simp only [pochhammer_zero, pochhammer_succ, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, mul_one]
  generalize pochhammer a j = P
  generalize pochhammer b j = Q
  generalize pochhammer (a + b - c + 1 / 2) j = R
  generalize pochhammer (c - 1 / 2) j = S
  have hJ : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  field_simp [hJ]
  simp only [middleFactor]
  have hn : (n : ℂ) = 2 * j - 1 := by
    have h : (n : ℂ) + 1 = 2 * j := by exact_mod_cast hj.symm
    linear_combination h
  rw [hn]
  ring

/-- The certificate identity at the final support boundary. -/
private lemma kernel_telescope_boundary_two (a b c : ℂ) (n j : ℕ)
    (hj : 2 * j = n + 2) :
    ((n : ℂ) + 2) * kernel a b c (n + 2) j -
      middleFactor a b c (n + 1) * kernel a b c (n + 1) j +
      (2 * a + n) * (2 * b + n) * (a + b + n) * (c + n) * (2 * c + n - 1) *
        kernel a b c n j = certificate a b c n (j + 1) - certificate a b c n j := by
  have hj0 : ¬2 * j ≤ n := by omega
  have hj1 : ¬2 * j ≤ n + 1 := by omega
  have hj2 : 2 * j ≤ n + 2 := by omega
  have hj3 : ¬2 * (j + 1) ≤ n + 2 := by omega
  simp only [kernel, certificate, ite_eq_right hj0, ite_eq_right hj1, ite_eq_left hj2,
    ite_eq_right hj3, mul_zero, add_zero, sub_zero, zero_sub]
  have hn2 : n + 2 - 2 * j = 0 := by omega
  have hc1 : n + 1 - j = j - 1 := by omega
  have hc2 : n + 2 - j = j := by omega
  have hjj : j = (j - 1) + 1 := by omega
  rw [hn2, hc1, hc2]
  have hcp : pochhammer (c - 1 / 2) j =
      pochhammer (c - 1 / 2) (j - 1) * (c - 1 / 2 + (j - 1 : ℕ)) := by
    conv_lhs => rw [hjj, pochhammer_succ]
  rw [hcp]
  simp only [pochhammer_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
  have hn : (n : ℂ) = 2 * j - 2 := by
    have h : (n : ℂ) + 2 = 2 * j := by exact_mod_cast hj.symm
    linear_combination h
  have hjj' : ((j - 1 : ℕ) : ℂ) + 1 = j := by exact_mod_cast hjj.symm
  rw [hn]
  have hjc : ((j - 1 : ℕ) : ℂ) = j - 1 := by linear_combination hjj'
  rw [hjc]
  ring

/-- The certificate identity at every natural summation index. -/
private lemma kernel_telescope (a b c : ℂ) (n j : ℕ) :
    ((n : ℂ) + 2) * kernel a b c (n + 2) j -
      middleFactor a b c (n + 1) * kernel a b c (n + 1) j +
      (2 * a + n) * (2 * b + n) * (a + b + n) * (c + n) * (2 * c + n - 1) *
        kernel a b c n j = certificate a b c n (j + 1) - certificate a b c n j := by
  by_cases hj : 2 * j ≤ n
  · exact kernel_telescope_interior a b c n j hj
  by_cases hj1 : 2 * j = n + 1
  · exact kernel_telescope_boundary_one a b c n j hj1
  by_cases hj2 : 2 * j = n + 2
  · exact kernel_telescope_boundary_two a b c n j hj2
  have hj3 : ¬2 * j ≤ n + 1 := by omega
  have hj4 : ¬2 * j ≤ n + 2 := by omega
  have hj5 : ¬2 * (j + 1) ≤ n + 2 := by omega
  simp only [kernel, certificate, ite_eq_right hj, ite_eq_right hj3, ite_eq_right hj4,
    ite_eq_right hj5, mul_zero, add_zero, sub_zero]

/-- The finite polynomial expression for a square coefficient with its lower products cleared. -/
private def finiteSum (a b c : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), kernel a b c n j

/-- The finite kernel vanishes beyond its natural termination index. -/
private lemma kernel_eq_zero_of_lt (a b c : ℂ) {n j : ℕ} (hj : n < 2 * j) :
    kernel a b c n j = 0 := by
  simp only [kernel, ite_eq_right (by omega : ¬2 * j ≤ n)]

/-- The finite polynomial expression satisfies the symmetric-square recurrence. -/
private lemma finiteSum_recurrence (a b c : ℂ) (n : ℕ) :
    ((n : ℂ) + 2) * finiteSum a b c (n + 2) -
      middleFactor a b c (n + 1) * finiteSum a b c (n + 1) +
      (2 * a + n) * (2 * b + n) * (a + b + n) * (c + n) * (2 * c + n - 1) *
        finiteSum a b c n = 0 := by
  have h := Finset.sum_congr (s₁ := Finset.range (n + 3)) rfl
    (fun j _ => kernel_telescope a b c n j)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_range_sub] at h
  have h0 : certificate a b c n 0 = 0 := by simp [certificate]
  have hN : certificate a b c n (n + 3) = 0 := by
    simp only [certificate, ite_eq_right (by omega : ¬2 * (n + 3) ≤ n + 2)]
  have hS1 : ∑ j ∈ Finset.range (n + 3), kernel a b c (n + 1) j =
      finiteSum a b c (n + 1) := by
    rw [Finset.sum_range_succ]
    rw [kernel_eq_zero_of_lt a b c (by omega : n + 1 < 2 * (n + 2)), add_zero]
    rfl
  have hS0 : ∑ j ∈ Finset.range (n + 3), kernel a b c n j = finiteSum a b c n := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [kernel_eq_zero_of_lt a b c (by omega : n < 2 * (n + 1)),
      kernel_eq_zero_of_lt a b c (by omega : n < 2 * (n + 2)), add_zero, add_zero]
    rfl
  rw [h0, hN, sub_self, hS1, hS0] at h
  exact h

/-- The constant square coefficient is one. -/
private lemma finiteSum_zero (a b c : ℂ) : finiteSum a b c 0 = 1 := by
  simp [finiteSum, kernel, pochhammer_zero]

/-- The first square coefficient after clearing the lower products. -/
private lemma finiteSum_one (a b c : ℂ) : finiteSum a b c 1 = 2 * a * b * (2 * c - 1) := by
  simp only [finiteSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [kernel_eq_zero_of_lt a b c (by omega : 1 < 2 * 1), add_zero]
  simp only [kernel, Nat.mul_zero, Nat.zero_le, ite_eq_left, pow_zero, pochhammer_zero,
    Nat.sub_zero, pochhammer_succ, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one,
    Nat.cast_zero, mul_one, one_mul, add_zero]
  ring

/-- The finite polynomial expression equals the cleared formal square coefficient. -/
private lemma finiteSum_eq_coeff {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    finiteSum a b c n = pochhammer c n * pochhammer (2 * c - 1) n *
      coeff n (gaussPS a b c * gaussPS a b c) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [finiteSum_zero, gaussPS, coeff_mul, pochhammer_zero,
      gaussHypergeometricCoeff]
  | one =>
    rw [finiteSum_one]
    simp only [PowerSeries.coeff_one_mul, gaussPS, coeff_mk, PowerSeries.constantCoeff_mk,
      gaussHypergeometricCoeff, pochhammer_succ, pochhammer_zero, Nat.factorial_one,
      Nat.cast_one, mul_one, one_mul]
    have hc0 : c ≠ 0 := by simpa using hc 0
    field_simp [hc0]
    ring
  | more n ih0 ih1 =>
    have hS := finiteSum_recurrence a b c n
    have hD := gaussPS_square_recurrence (a := a) (b := b) hc n
    rw [ih0, ih1] at hS
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
    apply mul_left_cancel₀ hn
    simp only [pochhammer_succ, middleFactor, Nat.cast_add, Nat.cast_one] at hS ⊢
    linear_combination hS - (pochhammer c n * (c + n) *
      pochhammer (2 * c - 1) n * (2 * c - 1 + n)) * hD

/-- Cancelling the terminating hypergeometric summand gives the polynomial kernel. -/
private lemma weightedTerm_eq_kernel (a b c : ℂ)
    (hb : LowerParametersRegular {c, 2 * c - 1, a + 1 / 2, b + 1 / 2}) (n j : ℕ) :
    (pochhammer c n * pochhammer (2 * c - 1) n) *
      (pochhammer (2 * a) n * pochhammer (2 * b) n * pochhammer (c - 1 / 2) n /
        (pochhammer c n * pochhammer (2 * c - 1) n * n.factorial) *
        generalizedHypergeometricCoeff
          {-(n : ℂ) / 2, (1 - (n : ℂ)) / 2, a + b - c + 1 / 2, 1 / 2}
          {a + 1 / 2, b + 1 / 2, 3 / 2 - (n : ℂ) - c} j) = kernel a b c n j := by
  have hdup := pochhammer_two_mul_two_mul (-(n : ℂ) / 2) j
  rw [show 2 * (-(n : ℂ) / 2) = -(n : ℂ) by ring,
    show -(n : ℂ) / 2 + 1 / 2 = (1 - (n : ℂ)) / 2 by ring] at hdup
  have hcoef : generalizedHypergeometricCoeff
      {-(n : ℂ) / 2, (1 - (n : ℂ)) / 2, a + b - c + 1 / 2, 1 / 2}
      {a + 1 / 2, b + 1 / 2, 3 / 2 - (n : ℂ) - c} j =
      (pochhammer (-(n : ℂ) / 2) j * pochhammer ((1 - (n : ℂ)) / 2) j) *
        (pochhammer (a + b - c + 1 / 2) j * pochhammer (1 / 2) j) /
        (pochhammer (a + 1 / 2) j * pochhammer (b + 1 / 2) j *
          pochhammer (3 / 2 - (n : ℂ) - c) j * j.factorial) := by
    simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
      Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
    ring
  rw [hcoef]
  by_cases hj : 2 * j ≤ n
  · rw [kernel, ite_eq_left hj]
    have hjn : j ≤ n := by omega
    have hca : pochhammer c n ≠ 0 :=
      pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n
    have hcb : pochhammer (2 * c - 1) n ≠ 0 :=
      pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n
    have hAa : pochhammer (a + 1 / 2) j ≠ 0 :=
      pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) j
    have hBb : pochhammer (b + 1 / 2) j ≠ 0 :=
      pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) j
    have hC : pochhammer (c - 1 / 2) n =
        (-1) ^ j * pochhammer (c - 1 / 2) (n - j) *
          pochhammer (3 / 2 - (n : ℂ) - c) j := by
      have h := pochhammer_eq_pochhammer_sub_mul (c - 1 / 2) hjn
      rw [show 1 - (c - 1 / 2) - (n : ℂ) = 3 / 2 - (n : ℂ) - c by ring] at h
      linear_combination h
    have hC0 : pochhammer (c - 1 / 2) n ≠ 0 := by
      refine pochhammer_ne_zero_of_not_neg_nat (fun k hk => ?_) n
      exact hb (2 * c - 1) (by simp) (2 * k) (by push_cast; linear_combination 2 * hk)
    have hD : pochhammer (3 / 2 - (n : ℂ) - c) j ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hC
      exact hC0 hC
    have hA : pochhammer (2 * a) n =
        4 ^ j * pochhammer a j * pochhammer (a + 1 / 2) j *
          pochhammer (2 * a + 2 * j) (n - 2 * j) := by
      rw [← Nat.add_sub_of_le hj, pochhammer_add]
      rw [pochhammer_two_mul_two_mul]
      push_cast
      simp only [Nat.add_sub_cancel_left]
    have hB : pochhammer (2 * b) n =
        4 ^ j * pochhammer b j * pochhammer (b + 1 / 2) j *
          pochhammer (2 * b + 2 * j) (n - 2 * j) := by
      rw [← Nat.add_sub_of_le hj, pochhammer_add]
      rw [pochhammer_two_mul_two_mul]
      push_cast
      simp only [Nat.add_sub_cancel_left]
    have h4 : (4 : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    have hN : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hJ : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    have hM : ((n - 2 * j).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (n - 2 * j).factorial_ne_zero
    have hneg : pochhammer (-(n : ℂ) / 2) j * pochhammer ((1 - (n : ℂ)) / 2) j =
        n.factorial / (4 ^ j * (n - 2 * j).factorial) := by
      apply (eq_div_iff (mul_ne_zero h4 hM)).2
      rw [DLMF.Gamma.pochhammer_neg_nat_eq, ite_eq_left hj,
        pow_mul, neg_one_sq, one_pow, one_mul] at hdup
      generalize pochhammer (-(n : ℂ) / 2) j = P at hdup ⊢
      generalize pochhammer ((1 - (n : ℂ)) / 2) j = Q at hdup ⊢
      field_simp [hM] at hdup
      linear_combination -hdup
    have hhalf : pochhammer (1 / 2 : ℂ) j =
        (2 * j).factorial / (4 ^ j * j.factorial) := by
      have h := pochhammer_two_mul_two_mul (1 / 2) j
      rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num,
        show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
        pochhammer_nat_one, pochhammer_nat_one] at h
      apply (eq_div_iff (mul_ne_zero h4 hJ)).2
      linear_combination h.symm
    rw [hA, hB, hC, hneg, hhalf]
    generalize pochhammer c n = C0 at *
    generalize pochhammer (2 * c - 1) n = C1 at *
    generalize pochhammer (a + 1 / 2) j = A0 at *
    generalize pochhammer (b + 1 / 2) j = B0 at *
    generalize pochhammer (3 / 2 - (n : ℂ) - c) j = D0 at *
    field_simp [hca, hcb, hAa, hBb, hD, hN, hJ, hM, h4]
  · have hzero : pochhammer (-(n : ℂ) / 2) j *
        pochhammer ((1 - (n : ℂ)) / 2) j = 0 := by
      rw [pochhammer_neg_nat_eq_zero (by omega : n < 2 * j)] at hdup
      rw [mul_assoc] at hdup
      exact (mul_eq_zero.mp hdup.symm).resolve_left (pow_ne_zero _ (by norm_num))
    simp only [kernel, ite_eq_right hj, hzero, zero_mul, zero_div, mul_zero]

/-- The coefficient of the square of a Gauss series is the terminating four-over-three
expression of DLMF 16.12.3. All lower exceptions after termination are retained. -/
theorem coeff_gaussPS_square (a b c : ℂ)
    (hb : LowerParametersRegular {c, 2 * c - 1, a + 1 / 2, b + 1 / 2}) (n : ℕ) :
    coeff n (gaussPS a b c * gaussPS a b c) =
      pochhammer (2 * a) n * pochhammer (2 * b) n * pochhammer (c - 1 / 2) n /
        (pochhammer c n * pochhammer (2 * c - 1) n * n.factorial) *
        generalizedHypergeometricTruncated n
          {-(n : ℂ) / 2, (1 - (n : ℂ)) / 2, a + b - c + 1 / 2, 1 / 2}
          {a + 1 / 2, b + 1 / 2, 3 / 2 - (n : ℂ) - c} 1 := by
  have hC : pochhammer c n ≠ 0 :=
    pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n
  have hD : pochhammer (2 * c - 1) n ≠ 0 :=
    pochhammer_ne_zero_of_not_neg_nat (hb _ (by simp)) n
  apply mul_left_cancel₀ (mul_ne_zero hC hD)
  rw [← finiteSum_eq_coeff (hb _ (by simp)) n]
  simp only [generalizedHypergeometricTruncated, one_pow, mul_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (weightedTerm_eq_kernel a b c hb n j).symm

end DLMF.Hypergeometric.GeneralSquare
