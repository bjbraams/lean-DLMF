/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module


public import DLMF.Confluent.Whittaker

/-!
# Recurrence relations and derivatives (DLMF §§13.3, 13.15)

Denominator parameters of `kummerM` stay off the nonpositive integers.
Tricomi and Whittaker identities use the principal branch on the slit plane.
The operator `(z d/dz z)` is `mulDerivMul`, matching DLMF 13.3.29.
13.3.15 is already proved as `deriv_kummerM_regular` in
`OrthogonalPolynomials.Differential`; the pointwise form is restated here.
-/

@[expose] public section

open Complex Filter FormalMultilinearSeries
open scoped Real Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- The operator `f ↦ z (z f)'`. -/
def mulDerivMul (f : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv (fun w => w * f w) z

-- NOTE (2026-09-17): the smoothness hypothesis `hf` was added; the DLMF identity is for
-- smooth `f`, and without it the two sides involve junk values of `deriv`. The proof reuses
-- the Gauss-side operator identity `DLMF.Hypergeometric.iterate_mulDerivMul_eq`.
@[dlmf 13.3.E29]
theorem mulDerivMul_eq_mul_iteratedDeriv (n : ℕ) (f : ℂ → ℂ) (hf : ContDiff ℂ ⊤ f) {z : ℂ}
    (hz : z ≠ 0) :
    mulDerivMul^[n] f z = z ^ n * iteratedDeriv n (fun w => w ^ n * f w) z := by
  have h : mulDerivMul = DLMF.Hypergeometric.mulDerivMul := rfl
  rw [h]
  exact DLMF.Hypergeometric.iterate_mulDerivMul_eq n hf z

section KummerContiguous

/-- Kummer's series converges everywhere. -/
theorem hasSum_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n => kummerMCoeff a b n * z ^ n) (kummerM a b z) :=
  (hasFPowerSeriesOnBall_kummerM (a := a) hb).hasSum_mul_pow (by simp)

/-- Termwise differentiation of Kummer's series: `M'(a,b,z) = ∑ (n+1) c_{n+1} zⁿ`. -/
theorem hasSum_deriv_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n : ℕ => (n + 1 : ℂ) * kummerMCoeff a b (n + 1) * z ^ n)
      (deriv (kummerM a b) z) :=
  (hasFPowerSeriesOnBall_kummerM (a := a) hb).deriv_ofScalars.hasSum_mul_pow (by simp)

/-- `z M'(a,b,z) = ∑ n c_n zⁿ`, with `c_n` the Kummer coefficients. -/
theorem hasSum_z_mul_deriv_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n : ℕ => (n : ℂ) * kummerMCoeff a b n * z ^ n)
      (z * deriv (kummerM a b) z) :=
  (hasFPowerSeriesOnBall_kummerM (a := a) hb).hasSum_z_mul_deriv (by simp)

/-- `z M(a,b,z) = ∑_{n ≥ 1} c_{n-1} zⁿ`. -/
theorem hasSum_z_mul_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n : ℕ => (if n = 0 then 0 else kummerMCoeff a b (n - 1)) * z ^ n)
      (z * kummerM a b z) := by
  apply HasSum.mul_pow_shift (c := fun n => if n = 0 then 0 else kummerMCoeff a b (n - 1))
    ?_ (by simp)
  simpa using hasSum_kummerM hb z

/-- Coefficient identity `n c_n(a,b) = a c_n(a+1,b) - a c_n(a,b)`. -/
theorem kummerMCoeff_shift_a (a b : ℂ) (n : ℕ) :
    (n : ℂ) * kummerMCoeff a b n =
      a * kummerMCoeff (a + 1) b n - a * kummerMCoeff a b n := by
  simp only [kummerMCoeff]
  rw [mul_div_assoc', mul_div_assoc', mul_div_assoc', ← sub_div]
  congr 1
  cases n with
  | zero => simp [poch_zero]
  | succ m =>
    rw [← poch_succ_left, poch_succ a (m + 1)]
    push_cast
    ring

/-- Coefficient identity `n c_n(a,b) = (b-1) c_n(a,b-1) - (b-1) c_n(a,b)`. -/
theorem kummerMCoeff_shift_b_pred {a b : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) (n : ℕ) :
    (n : ℂ) * kummerMCoeff a b n =
      (b - 1) * kummerMCoeff a (b - 1) n - (b - 1) * kummerMCoeff a b n := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  cases n with
  | zero => simp [kummerMCoeff, poch_zero]
  | succ m =>
    have hb0 : b - 1 ≠ 0 := by simpa using hb1 0
    have hbm : b + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb m
    have hpb := poch_ne_zero_of_not_neg_nat hb m
    have hf : ((m + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [kummerMCoeff]
    rw [poch_succ_left (b - 1), sub_add_cancel, poch_succ b m]
    push_cast
    field_simp
    ring

/-- Coefficient identity `n c_n(a,b) = (b-a) c_n(a-1,b) + (a-b) c_n(a,b) + c_{n-1}(a,b)`, behind
DLMF 13.3.1. -/
theorem kummerMCoeff_shift_a_pred {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    (n : ℂ) * kummerMCoeff a b n =
      (b - a) * kummerMCoeff (a - 1) b n + (a - b) * kummerMCoeff a b n +
        (if n = 0 then 0 else kummerMCoeff a b (n - 1)) := by
  cases n with
  | zero => simp [kummerMCoeff, poch_zero]
  | succ m =>
    have hbm : b + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb m
    have hpb := poch_ne_zero_of_not_neg_nat hb m
    have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [kummerMCoeff, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [poch_succ_left (a - 1), sub_add_cancel, poch_succ a m, poch_succ b m,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- Coefficient identity `b (n+1) c_{n+1}(a,b) = (a-b) c_n(a,b+1) + b c_n(a,b)`.
-/
theorem kummerMCoeff_shift_b_succ {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    b * ((n + 1 : ℂ) * kummerMCoeff a b (n + 1)) =
      (a - b) * kummerMCoeff a (b + 1) n + b * kummerMCoeff a b n := by
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hbn : b + n ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb n
  have hpb := poch_ne_zero_of_not_neg_nat hb n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hrel : b * poch (b + 1) n = poch b n * (b + n) := by rw [← poch_succ_left, poch_succ]
  have hX : poch (b + 1) n = poch b n * (b + n) / b := by
    rw [eq_div_iff hb0]; linear_combination hrel
  simp only [kummerMCoeff]
  rw [poch_succ a n, poch_succ b n, Nat.factorial_succ, hX]
  push_cast
  field_simp
  ring

/-- Coefficient form of `b M(a,b,z) - b M(a-1,b,z) - z M(a,b+1,z) = 0` (DLMF 13.3.4). -/
theorem kummerMCoeff_contiguous_shift_a {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    b * kummerMCoeff a b n - b * kummerMCoeff (a - 1) b n -
      (if n = 0 then 0 else kummerMCoeff a (b + 1) (n - 1)) = 0 := by
  cases n with
  | zero => simp [kummerMCoeff, poch_zero]
  | succ m =>
    have hb0 : b ≠ 0 := by simpa using hb 0
    have hbm : b + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb m
    have hpb := poch_ne_zero_of_not_neg_nat hb m
    have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hrel : b * poch (b + 1) m = poch b m * (b + m) := by rw [← poch_succ_left, poch_succ]
    have hX : poch (b + 1) m = poch b m * (b + m) / b := by
      rw [eq_div_iff hb0]; linear_combination hrel
    simp only [kummerMCoeff, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [poch_succ_left (a - 1), sub_add_cancel, poch_succ a m, poch_succ b m,
      Nat.factorial_succ, hX]
    push_cast
    field_simp
    ring

/-- Coefficient identity combining the Kummer equation with contiguous relations in `(a,b) →
(a+1,b+1) → (a+2,b+2)`. -/
theorem kummerMCoeff_ode_contiguous {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    (a + 1) * (if n = 0 then 0 else kummerMCoeff (a + 2) (b + 2) (n - 1)) +
      (b + 1) * b * kummerMCoeff (a + 1) (b + 1) n -
      (b + 1) * (if n = 0 then 0 else kummerMCoeff (a + 1) (b + 1) (n - 1)) -
      b * (b + 1) * kummerMCoeff a b n = 0 := by
  cases n with
  | zero => simp [kummerMCoeff, poch_zero]; ring
  | succ m =>
    have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
    have hb0 : b ≠ 0 := by simpa using hb 0
    have hb10 : b + 1 ≠ 0 := by simpa using hb1 0
    have hbm : b + 1 + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb1 m
    have hpb := poch_ne_zero_of_not_neg_nat hb1 m
    have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hrelA : (a + 1) * poch (a + 2) m = poch (a + 1) m * (a + 1 + m) := by
      rw [show (a + 2 : ℂ) = a + 1 + 1 by ring, ← poch_succ_left, poch_succ]
    have hrelB : (b + 1) * poch (b + 2) m = poch (b + 1) m * (b + 1 + m) := by
      rw [show (b + 2 : ℂ) = b + 1 + 1 by ring, ← poch_succ_left, poch_succ]
    have hX : poch (b + 2) m = poch (b + 1) m * (b + 1 + m) / (b + 1) := by
      rw [eq_div_iff hb10]; linear_combination hrelB
    have hA : (a + 1) * kummerMCoeff (a + 2) (b + 2) m =
        poch (a + 1) m * (a + 1 + m) / (poch (b + 2) m * m.factorial) := by
      simp only [kummerMCoeff]
      rw [mul_div_assoc', hrelA]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [hA, hX]
    simp only [kummerMCoeff]
    rw [poch_succ_left a, poch_succ (a + 1) m, poch_succ_left b, poch_succ (b + 1) m,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `z M'(a,b,z) = a (M(a+1,b,z) - M(a,b,z))`. -/
theorem z_mul_deriv_kummerM_eq_shift_a {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    z * deriv (kummerM a b) z = a * kummerM (a + 1) b z - a * kummerM a b z := by
  have h := hasSum_z_mul_deriv_kummerM (a := a) hb z
  have h' := ((hasSum_kummerM (a := a + 1) hb z).mul_left a).sub
    ((hasSum_kummerM (a := a) hb z).mul_left a)
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * kummerMCoeff_shift_a a b n

/-- `z M'(a,b,z) = (b-1) (M(a,b-1,z) - M(a,b,z))`. -/
theorem z_mul_deriv_kummerM_eq_shift_b_pred {a b : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) (z : ℂ) :
    z * deriv (kummerM a b) z =
      (b - 1) * kummerM a (b - 1) z - (b - 1) * kummerM a b z := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  have h := hasSum_z_mul_deriv_kummerM (a := a) hb z
  have h' := ((hasSum_kummerM (a := a) hb1 z).mul_left (b - 1)).sub
    ((hasSum_kummerM (a := a) hb z).mul_left (b - 1))
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * kummerMCoeff_shift_b_pred (a := a) hb1 n

/-- `z M'(a,b,z) = (b-a) M(a-1,b,z) + (a-b+z) M(a,b,z)`. -/
theorem z_mul_deriv_kummerM_eq_shift_a_pred {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    z * deriv (kummerM a b) z =
      (b - a) * kummerM (a - 1) b z + (a - b) * kummerM a b z +
        z * kummerM a b z := by
  have h := hasSum_z_mul_deriv_kummerM (a := a) hb z
  have h' := (((hasSum_kummerM (a := a - 1) hb z).mul_left (b - a)).add
    ((hasSum_kummerM (a := a) hb z).mul_left (a - b))).add (hasSum_z_mul_kummerM (a := a) hb z)
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * kummerMCoeff_shift_a_pred (a := a) hb n

/-- `b M'(a,b,z) = (a-b) M(a,b+1,z) + b M(a,b,z)`. -/
theorem deriv_kummerM_eq_shift_b_succ {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    b * deriv (kummerM a b) z = (a - b) * kummerM a (b + 1) z + b * kummerM a b z := by
  have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have h := (hasSum_deriv_kummerM (a := a) hb z).mul_left b
  have h' := ((hasSum_kummerM (a := a) hb1 z).mul_left (a - b)).add
    ((hasSum_kummerM (a := a) hb z).mul_left b)
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * kummerMCoeff_shift_b_succ (a := a) hb n

end KummerContiguous

@[dlmf 13.3.E1]
theorem kummerM_contiguous_a {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    (b - a) * kummerM (a - 1) b z + (2 * a - b + z) * kummerM a b z -
      a * kummerM (a + 1) b z = 0 := by
  have hA := z_mul_deriv_kummerM_eq_shift_a (a := a) hb z
  have hC := z_mul_deriv_kummerM_eq_shift_a_pred (a := a) hb z
  linear_combination hA - hC

@[dlmf 13.3.E2]
theorem kummerM_contiguous_b {a b z : ℂ} (hb : ∀ k : ℕ, b - 1 ≠ -k) :
    b * (b - 1) * kummerM a (b - 1) z + b * (1 - b - z) * kummerM a b z +
      z * (b - a) * kummerM a (b + 1) z = 0 := by
  have hb' : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hb z
  have hD := deriv_kummerM_eq_shift_b_succ (a := a) hb' z
  linear_combination z * hD - b * hB

@[dlmf 13.3.E3]
theorem kummerM_contiguous_a_b {a b z : ℂ} (hb : ∀ k : ℕ, b - 1 ≠ -k) :
    (a - b + 1) * kummerM a b z - a * kummerM (a + 1) b z +
      (b - 1) * kummerM a (b - 1) z = 0 := by
  have hb' : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hA := z_mul_deriv_kummerM_eq_shift_a (a := a) hb' z
  have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hb z
  linear_combination hA - hB

@[dlmf 13.3.E4]
theorem kummerM_contiguous_shift_a {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    b * kummerM a b z - b * kummerM (a - 1) b z - z * kummerM a (b + 1) z = 0 := by
  have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have h := (((hasSum_kummerM (a := a) hb z).mul_left b).sub
    ((hasSum_kummerM (a := a - 1) hb z).mul_left b)).sub
    (hasSum_z_mul_kummerM (a := a) hb1 z)
  refine h.unique ?_
  convert hasSum_zero using 1
  funext n
  linear_combination (z ^ n) * kummerMCoeff_contiguous_shift_a (a := a) hb n

@[dlmf 13.3.E5]
theorem kummerM_contiguous_mixed {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    b * (a + z) * kummerM a b z + z * (a - b) * kummerM a (b + 1) z -
      a * b * kummerM (a + 1) b z = 0 := by
  have hA := z_mul_deriv_kummerM_eq_shift_a (a := a) hb z
  have hD := deriv_kummerM_eq_shift_b_succ (a := a) hb z
  linear_combination b * hA - z * hD

@[dlmf 13.3.E6]
theorem kummerM_contiguous_down {a b z : ℂ} (hb : ∀ k : ℕ, b - 1 ≠ -k) :
    (a - 1 + z) * kummerM a b z + (b - a) * kummerM (a - 1) b z +
      (1 - b) * kummerM a (b - 1) z = 0 := by
  have hb' : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hb z
  have hC := z_mul_deriv_kummerM_eq_shift_a_pred (a := a) hb' z
  linear_combination hB - hC


@[dlmf 13.3.E13]
theorem kummerM_ode_contiguous {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    (a + 1) * z * kummerM (a + 2) (b + 2) z +
      (b + 1) * (b - z) * kummerM (a + 1) (b + 1) z -
      b * (b + 1) * kummerM a b z = 0 := by
  have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hb2 : ∀ k : ℕ, b + 2 ≠ -k := by simpa using not_neg_nat_add_nat hb 2
  have h := ((((hasSum_z_mul_kummerM (a := a + 2) hb2 z).mul_left (a + 1)).add
    ((hasSum_kummerM (a := a + 1) hb1 z).mul_left ((b + 1) * b))).sub
    ((hasSum_z_mul_kummerM (a := a + 1) hb1 z).mul_left (b + 1))).sub
    ((hasSum_kummerM (a := a) hb z).mul_left (b * (b + 1)))
  have h0 : (a + 1) * (z * kummerM (a + 2) (b + 2) z) +
      (b + 1) * b * kummerM (a + 1) (b + 1) z -
      (b + 1) * (z * kummerM (a + 1) (b + 1) z) - b * (b + 1) * kummerM a b z = 0 := by
    refine h.unique ?_
    convert hasSum_zero using 1
    funext n
    linear_combination (z ^ n) * kummerMCoeff_ode_contiguous (a := a) hb n
  linear_combination h0

@[dlmf 13.3.E15]
theorem deriv_kummerM {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (hb0 : b ≠ 0) :
    deriv (kummerM a b) z = a / b * kummerM (a + 1) (b + 1) z := by
  have hc1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hcoeff (k : ℕ) : (k + 1 : ℂ) * kummerMCoeff a b (k + 1) =
      a / b * kummerMCoeff (a + 1) (b + 1) k := by
    have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hcp := poch_ne_zero_of_not_neg_nat hc1 k
    simp only [kummerMCoeff, poch_succ_left, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp
  have hd := (hasFPowerSeriesOnBall_kummerM (a := a) hb).deriv_ofScalars.hasSum_mul_pow
    (z := z) (by simp)
  have hs := ((hasFPowerSeriesOnBall_kummerM (a := a + 1) hc1).hasSum_mul_pow
    (z := z) (by simp)).mul_left (a / b)
  simp_rw [hcoeff] at hd
  simp only [mul_assoc] at hd hs
  exact hd.unique hs

/-- `a M(a+1,b+1,z) = (a-b) M(a,b+1,z) + b M(a,b,z)`. -/
theorem kummerM_contiguous_shift_b_succ {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    a * kummerM (a + 1) (b + 1) z =
      (a - b) * kummerM a (b + 1) z + b * kummerM a b z := by
  have hb0 : b ≠ 0 := by simpa using hb 0
  have h1 := deriv_kummerM_eq_shift_b_succ (a := a) hb z
  have h2 := deriv_kummerM (a := a) hb hb0 (z := z)
  have h3 : b * (a / b * kummerM (a + 1) (b + 1) z) = a * kummerM (a + 1) (b + 1) z := by
    field_simp
  rw [h2] at h1
  linear_combination h1 - h3

/-- `(b-1) b (M(a,b,z) - M(a,b-1,z)) + a z M(a+1,b+1,z) = 0`. -/
theorem kummerM_contiguous_mixed_b_pred {a b z : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) :
    (b - 1) * b * kummerM a b z - (b - 1) * b * kummerM a (b - 1) z +
      a * z * kummerM (a + 1) (b + 1) z = 0 := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hb1 z
  have h2 := deriv_kummerM (a := a) hb hb0 (z := z)
  have h3 : b * (a / b * kummerM (a + 1) (b + 1) z) = a * kummerM (a + 1) (b + 1) z := by
    field_simp
  rw [h2] at hB
  linear_combination b * hB - z * h3

/-- `(b-1) b M(a-1,b-1,z) + (z-b+1) b M(a,b,z) - a z M(a+1,b+1,z) = 0`. -/
lemma kummerM_contiguous_up_aux {a b z : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) :
    (b - 1) * b * kummerM (a - 1) (b - 1) z + (z - b + 1) * b * kummerM a b z -
      a * z * kummerM (a + 1) (b + 1) z = 0 := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have h4 := kummerM_contiguous_shift_a (a := a) hb1 (z := z)
  rw [sub_add_cancel] at h4
  have h6 := kummerM_contiguous_down (a := a) hb1 (z := z)
  have hC := z_mul_deriv_kummerM_eq_shift_a_pred (a := a) hb z
  have h2 := deriv_kummerM (a := a) hb hb0 (z := z)
  have h3 : b * (a / b * kummerM (a + 1) (b + 1) z) = a * kummerM (a + 1) (b + 1) z := by
    field_simp
  rw [h2] at hC
  linear_combination z * h3 - b * hC - b * h6 - b * h4

/-- `(b-1) b M(a-1,b-1,z) - (b-1) b M(a,b,z) + (b-a) z M(a,b+1,z) = 0`. -/
theorem kummerM_contiguous_up_shift_aux {a b z : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) :
    (b - 1) * b * kummerM (a - 1) (b - 1) z - (b - 1) * b * kummerM a b z +
      (b - a) * z * kummerM a (b + 1) z = 0 := by
  have h4 := kummerM_contiguous_shift_a (a := a) hb1 (z := z)
  rw [sub_add_cancel] at h4
  have h2 := kummerM_contiguous_b (a := a) hb1 (z := z)
  linear_combination h2 - b * h4

/-! ### Tricomi's contiguous relations

Each relation is first proved at noninteger second parameters from the corresponding Kummer
relations, and then transferred to integer parameters through
`tendsto_kummerU_add_intCast`. The transfer needs `z ≠ 0`: at `z = 0` and integer `b`
the totalized `kummerU` has no continued value. -/

/-- If `f` vanishes on `ℂ \ ℤ` and tends to `L` along `ℂ \ ℤ` at `b`, then `L = 0`. -/
theorem eq_zero_of_tendsto_integerComplement {f : ℂ → ℂ} {b L : ℂ}
    (hf : Tendsto f (𝓝[integerComplement] b) (𝓝 L))
    (h0 : ∀ c ∈ integerComplement, f c = 0) : L = 0 := by
  have := integerComplement_nhdsWithin_neBot b
  exact tendsto_nhds_unique hf (tendsto_const_nhds.congr'
    (eventually_nhdsWithin_of_forall fun c hc => (h0 c hc).symm))

/-- The identity tends to `b` along `ℂ \ ℤ` at `b`. -/
theorem tendsto_id_integerComplement (b : ℂ) :
    Tendsto (fun c : ℂ => c) (𝓝[integerComplement] b) (𝓝 b) :=
  (continuous_id.tendsto b).mono_left nhdsWithin_le_nhds

/-- For `z ≠ 0`, `U(a, c-1, z) → U(a, b-1, z)` as `c → b` through `ℂ \ ℤ`. -/
theorem tendsto_kummerU_sub_one (a b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c => kummerU a (c - 1) z) (𝓝[integerComplement] b)
      (𝓝 (kummerU a (b - 1) z)) := by
  have h := tendsto_kummerU_add_intCast a b (-1) hz
  push_cast at h
  simpa [sub_eq_add_neg] using h

/-- For `z ≠ 0`, `U(a, c+1, z) → U(a, b+1, z)` as `c → b` through `ℂ \ ℤ`. -/
theorem tendsto_kummerU_add_one (a b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c => kummerU a (c + 1) z) (𝓝[integerComplement] b)
      (𝓝 (kummerU a (b + 1) z)) := by
  simpa using tendsto_kummerU_add_intCast a b 1 hz

/-- For `z ≠ 0`, `U(a, c+2, z) → U(a, b+2, z)` as `c → b` through `ℂ \ ℤ`. -/
theorem tendsto_kummerU_add_two (a b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c => kummerU a (c + 2) z) (𝓝[integerComplement] b)
      (𝓝 (kummerU a (b + 2) z)) := by
  simpa using tendsto_kummerU_add_intCast a b 2 hz

/-- `ℂ \ ℤ` is invariant under integer translations. -/
theorem intCompl_add_int {c : ℂ} (hc : c ∈ integerComplement) (k : ℤ) :
    c + (k : ℂ) ∈ integerComplement := (add_intCast_mem_integerComplement k).mpr hc

/-- If `c ∉ ℤ` then `c - 1 ∉ ℤ`. -/
theorem intCompl_sub_one {c : ℂ} (hc : c ∈ integerComplement) : c - 1 ∈ integerComplement := by
  simpa [sub_eq_add_neg] using intCompl_add_int hc (-1)

/-- If `c ∉ ℤ` then `c + 1 ∉ ℤ`. -/
theorem intCompl_add_one {c : ℂ} (hc : c ∈ integerComplement) : c + 1 ∈ integerComplement := by
  simpa using intCompl_add_int hc 1

/-- If `c ∉ ℤ` then `-c ∉ ℤ`. -/
theorem intCompl_neg {c : ℂ} (hc : c ∈ integerComplement) : -c ∈ integerComplement :=
  fun ⟨k, hk⟩ => hc ⟨-k, by push_cast; rw [hk]; ring⟩

/-- If `c ∉ ℤ` then `k - c ∉ ℤ` for integer `k`. -/
theorem intCompl_int_sub {c : ℂ} (hc : c ∈ integerComplement) (k : ℤ) :
    (k : ℂ) - c ∈ integerComplement := by
  simpa [sub_eq_add_neg, add_comm] using intCompl_add_int (intCompl_neg hc) k

/-- If `c ∉ ℤ` then `c - k ∉ ℤ` for integer `k`. -/
theorem intCompl_sub_int {c : ℂ} (hc : c ∈ integerComplement) (k : ℤ) :
    c - (k : ℂ) ∈ integerComplement := by
  have := intCompl_add_int hc (-k)
  push_cast at this
  simpa [sub_eq_add_neg] using this

/-- For noninteger `c` and `z ≠ 0`, `U(a,c,z) - a U(a+1,c,z) - U(a,c-1,z) = 0` (DLMF 13.3.9). -/
theorem kummerU_contiguous_a_b_of_mem {a c z : ℂ} (hc : c ∈ integerComplement) (hz : z ≠ 0) :
    kummerU a c z - a * kummerU (a + 1) c z - kummerU a (c - 1) z = 0 := by
  have hc1 := intCompl_sub_one hc
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc1)]
  unfold kummerUConnection
  have h2c : (2 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 2
  have E3 := kummerM_contiguous_a_b (a := a) (b := c) (z := z)
    (not_neg_nat_of_mem_integerComplement hc1)
  have E4 := kummerM_contiguous_shift_a (a := a - c + 2) (b := 2 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h2c)
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c + 1)
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one a
  have hG1 := Gamma_add_one (1 - c)
      (integerComplement.ne_zero (by simpa using intCompl_int_sub hc 1))
  have hc2 : c - 2 ∈ integerComplement := by simpa using intCompl_sub_int hc 2
  have hG2 := Gamma_add_one (c - 2) (integerComplement.ne_zero hc2)
  have hzc : z ^ (2 - c) = z * z ^ (1 - c) := by
    rw [show 2 - c = (1 - c) + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  rw [show a - c + 2 - 1 = a - c + 1 by ring, show 2 - c + 1 = 3 - c by ring] at E4
  rw [show a - c + 1 + 1 = a - c + 2 by ring] at hR
  rw [show 1 - c + 1 = 2 - c by ring] at hG1
  rw [show c - 2 + 1 = c - 1 by ring] at hG2
  rw [show a + 1 - c + 1 = a - c + 2 by ring, show a - (c - 1) + 1 = a - c + 2 by ring,
    show 2 - (c - 1) = 3 - c by ring, show 1 - (c - 1) = 2 - c by ring, show c - 1 - 1 = c - 2 by ring]
  rw [hzc]
  simp only [div_eq_mul_inv]
  rw [hR, hS, hG1, hG2]
  linear_combination Gamma (1 - c) * (Gamma (a - c + 2))⁻¹ * E3 +
    Gamma (c - 2) * a * (Gamma (a + 1))⁻¹ * z ^ (1 - c) * E4

/-- For noninteger `c` and `z ≠ 0`, `(c-a) U(a,c,z) + U(a-1,c,z) - z U(a,c+1,z) = 0` (DLMF 13.3.10).
-/
theorem kummerU_contiguous_shift_a_of_mem {a c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ≠ 0) :
    (c - a) * kummerU a c z + kummerU (a - 1) c z - z * kummerU a (c + 1) z = 0 := by
  have hc1 := intCompl_add_one hc
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc1)]
  unfold kummerUConnection
  have h2c : (2 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 2
  have h1c : (1 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 1
  have E4 := kummerM_contiguous_shift_a (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hc)
  have E3 := kummerM_contiguous_a_b (a := a - c) (b := 2 - c) (z := z)
    (by simpa [show (2 : ℂ) - c - 1 = 1 - c by ring] using not_neg_nat_of_mem_integerComplement h1c)
  rw [show a - c - (2 - c) + 1 = a - 1 by ring, show a - c + 1 = a - c + 1 by ring,
    show (2 : ℂ) - c - 1 = 1 - c by ring] at E3
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c)
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - 1)
  rw [show a - 1 + 1 = a by ring] at hS
  have hG0 := Gamma_add_one (-c) (integerComplement.ne_zero (intCompl_neg hc))
  rw [show -c + 1 = 1 - c by ring] at hG0
  have hG1 := Gamma_add_one (c - 1) (integerComplement.ne_zero (intCompl_sub_one hc))
  rw [show c - 1 + 1 = c by ring] at hG1
  have hzc : z ^ (1 - c) = z * z ^ (-c) := by
    rw [show 1 - c = -c + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  rw [show a - 1 - c + 1 = a - c by ring, show 1 - (c + 1) = -c by ring,
    show a - (c + 1) + 1 = a - c by ring, show c + 1 - 1 = c by ring, show 2 - (c + 1) = 1 - c by ring]
  simp only [div_eq_mul_inv]
  rw [hR, hS, hG0, hG1, hzc]
  linear_combination Gamma (-c) * (Gamma (a - c + 1))⁻¹ * (a - c) * E4 +
    Gamma (c - 1) * (Gamma a)⁻¹ * z ^ (-c) * z * E3

/-- For noninteger `c`, `U(a-1,c,z) + (c-2a-z) U(a,c,z) + a(a-c+1) U(a+1,c,z) = 0` (DLMF 13.3.7). -/
theorem kummerU_contiguous_a_of_mem {a c z : ℂ} (hc : c ∈ integerComplement) :
    kummerU (a - 1) c z + (c - 2 * a - z) * kummerU a c z +
      a * (a - c + 1) * kummerU (a + 1) c z = 0 := by
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc)]
  unfold kummerUConnection
  have h2c : (2 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 2
  have E1 := kummerM_contiguous_a (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hc)
  have E1' := kummerM_contiguous_a (a := a - c + 1) (b := 2 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h2c)
  rw [show a - c + 1 - 1 = a - c by ring, show a - c + 1 + 1 = a - c + 2 by ring] at E1'
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c)
  have hR' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c + 1)
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - 1)
  have hS' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one a
  rw [show a - c + 1 + 1 = a - c + 2 by ring] at hR'
  rw [show a - 1 + 1 = a by ring] at hS
  rw [show a - 1 - c + 1 = a - c by ring, show a + 1 - c + 1 = a - c + 2 by ring]
  simp only [div_eq_mul_inv]
  rw [show a - c + 1 = a - c + 1 by rfl] at hR
  rw [hR, hS, hR', hS']
  linear_combination (-(Gamma (1 - c) * (Gamma (a - c + 2))⁻¹ * (a - c + 1))) * E1 -
    Gamma (c - 1) * (Gamma (a + 1))⁻¹ * z ^ (1 - c) * a * E1'

/-- For noninteger `c` and `z ≠ 0`, `(c-a-1) U(a,c-1,z) + (1-c-z) U(a,c,z) + z U(a,c+1,z) = 0` (DLMF
13.3.8). -/
theorem kummerU_contiguous_b_of_mem {a c z : ℂ} (hc : c ∈ integerComplement) (hz : z ≠ 0) :
    (c - a - 1) * kummerU a (c - 1) z + (1 - c - z) * kummerU a c z +
      z * kummerU a (c + 1) z = 0 := by
  have hcm := intCompl_sub_one hc
  have hcp := intCompl_add_one hc
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcm),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcp)]
  unfold kummerUConnection
  have h1c : (1 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 1
  have E2 := kummerM_contiguous_b (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hcm)
  have E13 := kummerM_ode_contiguous (a := a - c) (b := 1 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h1c)
  rw [show a - c + 2 = a - c + 2 by ring, show 1 - c + 2 = 3 - c by ring,
    show a - c + 1 = a - c + 1 by ring, show 1 - c + 1 = 2 - c by ring] at E13
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c)
  have hR' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c + 1)
  rw [show a - c + 1 + 1 = a - c + 2 by ring] at hR'
  have hG0 := Gamma_add_one (-c) (integerComplement.ne_zero (intCompl_neg hc))
  rw [show -c + 1 = 1 - c by ring] at hG0
  have hG0' := Gamma_add_one (1 - c) (integerComplement.ne_zero h1c)
  rw [show 1 - c + 1 = 2 - c by ring] at hG0'
  have hc2 : c - 2 ∈ integerComplement := by simpa using intCompl_sub_int hc 2
  have hG2 := Gamma_add_one (c - 2) (integerComplement.ne_zero hc2)
  rw [show c - 2 + 1 = c - 1 by ring] at hG2
  have hG1 := Gamma_add_one (c - 1) (integerComplement.ne_zero hcm)
  rw [show c - 1 + 1 = c by ring] at hG1
  have hz1 : z ^ (1 - c) = z * z ^ (-c) := by
    rw [show 1 - c = -c + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  have hz2 : z ^ (2 - c) = z * z * z ^ (-c) := by
    rw [show 2 - c = -c + 1 + 1 by ring, cpow_add _ _ hz, cpow_add _ _ hz, cpow_one]; ring
  rw [show 1 - (c - 1) = 2 - c by ring, show a - (c - 1) + 1 = a - c + 2 by ring,
    show c - 1 - 1 = c - 2 by ring, show 2 - (c - 1) = 3 - c by ring,
    show 1 - (c + 1) = -c by ring, show a - (c + 1) + 1 = a - c by ring,
    show c + 1 - 1 = c by ring, show 2 - (c + 1) = 1 - c by ring]
  simp only [div_eq_mul_inv]
  rw [hR, hR', hG0', hG0, hG1, hG2, hz1, hz2]
  linear_combination (-(Gamma (-c) * (Gamma (a - c + 2))⁻¹ * (a - c + 1))) * E2 -
    Gamma (c - 2) * (Gamma a)⁻¹ * z ^ (-c) * z * E13

/-- For noninteger `c` and `z ≠ 0`, `(a+z) U(a,c,z) - z U(a,c+1,z) + a(c-a-1) U(a+1,c,z) = 0` (DLMF
13.3.11). -/
theorem kummerU_contiguous_mixed_of_mem {a c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ≠ 0) :
    (a + z) * kummerU a c z - z * kummerU a (c + 1) z +
      a * (c - a - 1) * kummerU (a + 1) c z = 0 := by
  have hcp := intCompl_add_one hc
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcp),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc)]
  unfold kummerUConnection
  have h1c : (1 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 1
  have h2c : (2 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 2
  have E5 := kummerM_contiguous_mixed (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hc)
  have E3 := kummerM_contiguous_a_b (a := a - c + 1) (b := 2 - c) (z := z)
    (by simpa [show (2 : ℂ) - c - 1 = 1 - c by ring] using not_neg_nat_of_mem_integerComplement h1c)
  have E4 := kummerM_contiguous_shift_a (a := a - c + 1) (b := 1 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h1c)
  rw [show a - c + 1 - (2 - c) + 1 = a by ring, show a - c + 1 + 1 = a - c + 2 by ring,
    show (2 : ℂ) - c - 1 = 1 - c by ring] at E3
  rw [show a - c + 1 - 1 = a - c by ring, show 1 - c + 1 = 2 - c by ring] at E4
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c)
  have hR' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c + 1)
  rw [show a - c + 1 + 1 = a - c + 2 by ring] at hR'
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one a
  have hG0 := Gamma_add_one (-c) (integerComplement.ne_zero (intCompl_neg hc))
  rw [show -c + 1 = 1 - c by ring] at hG0
  have hG1 := Gamma_add_one (c - 1) (integerComplement.ne_zero (intCompl_sub_one hc))
  rw [show c - 1 + 1 = c by ring] at hG1
  have hz1 : z ^ (1 - c) = z * z ^ (-c) := by
    rw [show 1 - c = -c + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  rw [show 1 - (c + 1) = -c by ring, show a - (c + 1) + 1 = a - c by ring,
    show c + 1 - 1 = c by ring, show 2 - (c + 1) = 1 - c by ring,
    show a + 1 - c + 1 = a - c + 2 by ring]
  simp only [div_eq_mul_inv]
  rw [hR, hR', hS, hG0, hG1, hz1]
  linear_combination (-(Gamma (-c) * (Gamma (a - c + 2))⁻¹ * (a - c + 1))) * E5 +
    Gamma (c - 1) * (Gamma (a + 1))⁻¹ * z ^ (-c) * z * a * (E3 - E4)

/-- For noninteger `c` and `z ≠ 0`, `(a-1+z) U(a,c,z) - U(a-1,c,z) + (a-c+1) U(a,c-1,z) = 0` (DLMF
13.3.12). -/
theorem kummerU_contiguous_down_of_mem {a c z : ℂ} (hc : c ∈ integerComplement)
    (hz : z ≠ 0) :
    (a - 1 + z) * kummerU a c z - kummerU (a - 1) c z +
      (a - c + 1) * kummerU a (c - 1) z = 0 := by
  have hcm := intCompl_sub_one hc
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcm)]
  unfold kummerUConnection
  have h1c : (1 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 1
  have h2c : (2 : ℂ) - c ∈ integerComplement := by simpa using intCompl_int_sub hc 2
  have E6 := kummerM_contiguous_down (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hcm)
  have E4 := kummerM_contiguous_shift_a (a := a - c + 1) (b := 2 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h2c)
  have SBS := kummerM_contiguous_shift_b_succ (a := a - c + 1) (b := 2 - c) (z := z)
    (not_neg_nat_of_mem_integerComplement h2c)
  rw [show a - c + 1 - 1 = a - c by ring, show 2 - c + 1 = 3 - c by ring] at E4
  rw [show a - c + 1 + 1 = a - c + 2 by ring, show 2 - c + 1 = 3 - c by ring,
    show a - c + 1 - (2 - c) = a - 1 by ring] at SBS
  have hR := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c)
  have hR' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - c + 1)
  rw [show a - c + 1 + 1 = a - c + 2 by ring] at hR'
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - 1)
  rw [show a - 1 + 1 = a by ring] at hS
  have hG0' := Gamma_add_one (1 - c) (integerComplement.ne_zero h1c)
  rw [show 1 - c + 1 = 2 - c by ring] at hG0'
  have hc2 : c - 2 ∈ integerComplement := by simpa using intCompl_sub_int hc 2
  have hG2 := Gamma_add_one (c - 2) (integerComplement.ne_zero hc2)
  rw [show c - 2 + 1 = c - 1 by ring] at hG2
  have hz2 : z ^ (2 - c) = z * z ^ (1 - c) := by
    rw [show 2 - c = (1 - c) + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  rw [show a - 1 - c + 1 = a - c by ring, show 1 - (c - 1) = 2 - c by ring,
    show a - (c - 1) + 1 = a - c + 2 by ring, show c - 1 - 1 = c - 2 by ring,
    show 2 - (c - 1) = 3 - c by ring]
  simp only [div_eq_mul_inv]
  rw [hR, hR', hS, hG0', hG2, hz2]
  linear_combination Gamma (1 - c) * (Gamma (a - c + 2))⁻¹ * (a - c + 1) * E6 +
    Gamma (c - 2) * (Gamma a)⁻¹ * z ^ (1 - c) * (z * SBS - (a - 1) * E4)

/-- For noninteger `c` and `z ≠ 0`, `(a+1) z U(a+2,c+2,z) + (z-c) U(a+1,c+1,z) - U(a,c,z) = 0`, the
Kummer equation in contiguous form. -/
theorem kummerU_ode_contiguous_of_mem {a c z : ℂ} (hc : c ∈ integerComplement) (hz : z ≠ 0) :
    (a + 1) * z * kummerU (a + 2) (c + 2) z + (z - c) * kummerU (a + 1) (c + 1) z -
      kummerU a c z = 0 := by
  have hcp := intCompl_add_one hc
  have hcpp : c + 2 ∈ integerComplement := by simpa using intCompl_add_int hc 2
  rw [kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcpp),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hcp),
    kummerU_eq_connection _ _ _ (forall_of_mem_integerComplement hc)]
  unfold kummerUConnection
  have hnc : -c ∈ integerComplement := intCompl_neg hc
  have E13 := kummerM_ode_contiguous (a := a) (b := c) (z := z)
      (not_neg_nat_of_mem_integerComplement hc)
  have E2 := kummerM_contiguous_b (a := a - c + 1) (b := 1 - c) (z := z)
    (by simpa [show (1 : ℂ) - c - 1 = -c by ring] using not_neg_nat_of_mem_integerComplement hnc)
  rw [show (1 : ℂ) - c - 1 = -c by ring, show 1 - c + 1 = 2 - c by ring] at E2
  have hG0 := Gamma_add_one (-c) (integerComplement.ne_zero hnc)
  rw [show -c + 1 = 1 - c by ring] at hG0
  have hm1 : -1 - c ∈ integerComplement := by simpa [sub_eq_add_neg, add_comm] using intCompl_add_int hnc (-1)
  have hGm := Gamma_add_one (-1 - c) (integerComplement.ne_zero hm1)
  rw [show -1 - c + 1 = -c by ring] at hGm
  have hG1 := Gamma_add_one (c - 1) (integerComplement.ne_zero (intCompl_sub_one hc))
  rw [show c - 1 + 1 = c by ring] at hG1
  have hGc := Gamma_add_one c (integerComplement.ne_zero hc)
  have hS := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one a
  have hS' := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a + 1)
  rw [show a + 1 + 1 = a + 2 by ring] at hS'
  have hz1 : z ^ (-c) = z * z ^ (-1 - c) := by
    rw [show -c = (-1 - c) + 1 by ring, cpow_add _ _ hz, cpow_one, mul_comm]
  have hz2 : z ^ (1 - c) = z * z * z ^ (-1 - c) := by
    rw [show 1 - c = (-1 - c) + 1 + 1 by ring, cpow_add _ _ hz, cpow_add _ _ hz, cpow_one]; ring
  rw [show 1 - (c + 2) = -1 - c by ring, show a + 2 - (c + 2) + 1 = a - c + 1 by ring,
    show c + 2 - 1 = c + 1 by ring, show 2 - (c + 2) = -c by ring,
    show 1 - (c + 1) = -c by ring, show a + 1 - (c + 1) + 1 = a - c + 1 by ring,
    show c + 1 - 1 = c by ring, show 2 - (c + 1) = 1 - c by ring]
  simp only [div_eq_mul_inv]
  rw [hG0, hGm, hGc, hG1, hS, hS', hz1, hz2]
  linear_combination Gamma (-1 - c) * (Gamma (a - c + 1))⁻¹ * E13 +
    Gamma (c - 1) * (Gamma (a + 2))⁻¹ * z ^ (-1 - c) * z * (a + 1) * E2

@[dlmf 13.3.E7]
theorem kummerU_contiguous_a (a b z : ℂ) (hz : z ≠ 0) :
    kummerU (a - 1) b z + (b - 2 * a - z) * kummerU a b z +
      a * (a - b + 1) * kummerU (a + 1) b z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c => kummerU (a - 1) c z +
    (c - 2 * a - z) * kummerU a c z + a * (a - c + 1) * kummerU (a + 1) c z) ?_
    fun c hc => kummerU_contiguous_a_of_mem hc
  have hc := tendsto_id_integerComplement b
  exact ((tendsto_kummerU (a - 1) b hz).add (((hc.sub_const _).sub_const _).mul
    (tendsto_kummerU a b hz))).add ((tendsto_const_nhds.mul ((hc.const_sub _).add_const _)).mul
      (tendsto_kummerU (a + 1) b hz))

@[dlmf 13.3.E8]
theorem kummerU_contiguous_b (a b z : ℂ) (hz : z ≠ 0) :
    (b - a - 1) * kummerU a (b - 1) z + (1 - b - z) * kummerU a b z +
      z * kummerU a (b + 1) z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c => (c - a - 1) * kummerU a (c - 1) z +
    (1 - c - z) * kummerU a c z + z * kummerU a (c + 1) z) ?_
    fun c hc => kummerU_contiguous_b_of_mem hc hz
  have hc := tendsto_id_integerComplement b
  exact ((((hc.sub_const _).sub_const _).mul (tendsto_kummerU_sub_one a b hz)).add
    (((hc.const_sub _).sub_const _).mul (tendsto_kummerU a b hz))).add
      (tendsto_const_nhds.mul (tendsto_kummerU_add_one a b hz))

@[dlmf 13.3.E9]
theorem kummerU_contiguous_a_b (a b z : ℂ) (hz : z ≠ 0) :
    kummerU a b z - a * kummerU (a + 1) b z - kummerU a (b - 1) z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c => kummerU a c z -
    a * kummerU (a + 1) c z - kummerU a (c - 1) z) ?_
    fun c hc => kummerU_contiguous_a_b_of_mem hc hz
  exact ((tendsto_kummerU a b hz).sub (tendsto_const_nhds.mul
    (tendsto_kummerU (a + 1) b hz))).sub (tendsto_kummerU_sub_one a b hz)

@[dlmf 13.3.E10]
theorem kummerU_contiguous_shift_a (a b z : ℂ) (hz : z ≠ 0) :
    (b - a) * kummerU a b z + kummerU (a - 1) b z - z * kummerU a (b + 1) z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c => (c - a) * kummerU a c z +
    kummerU (a - 1) c z - z * kummerU a (c + 1) z) ?_
    fun c hc => kummerU_contiguous_shift_a_of_mem hc hz
  have hc := tendsto_id_integerComplement b
  exact (((hc.sub_const _).mul (tendsto_kummerU a b hz)).add
    (tendsto_kummerU (a - 1) b hz)).sub (tendsto_const_nhds.mul
      (tendsto_kummerU_add_one a b hz))

@[dlmf 13.3.E11]
theorem kummerU_contiguous_mixed (a b z : ℂ) (hz : z ≠ 0) :
    (a + z) * kummerU a b z - z * kummerU a (b + 1) z +
      a * (b - a - 1) * kummerU (a + 1) b z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c => (a + z) * kummerU a c z -
    z * kummerU a (c + 1) z + a * (c - a - 1) * kummerU (a + 1) c z) ?_
    fun c hc => kummerU_contiguous_mixed_of_mem hc hz
  have hc := tendsto_id_integerComplement b
  exact ((tendsto_const_nhds.mul (tendsto_kummerU a b hz)).sub (tendsto_const_nhds.mul
    (tendsto_kummerU_add_one a b hz))).add ((tendsto_const_nhds.mul
      ((hc.sub_const _).sub_const _)).mul (tendsto_kummerU (a + 1) b hz))

@[dlmf 13.3.E12]
theorem kummerU_contiguous_down (a b z : ℂ) (hz : z ≠ 0) :
    (a - 1 + z) * kummerU a b z - kummerU (a - 1) b z +
      (a - b + 1) * kummerU a (b - 1) z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c => (a - 1 + z) * kummerU a c z -
    kummerU (a - 1) c z + (a - c + 1) * kummerU a (c - 1) z) ?_
    fun c hc => kummerU_contiguous_down_of_mem hc hz
  have hc := tendsto_id_integerComplement b
  exact ((tendsto_const_nhds.mul (tendsto_kummerU a b hz)).sub
    (tendsto_kummerU (a - 1) b hz)).add (((hc.const_sub _).add_const _).mul
      (tendsto_kummerU_sub_one a b hz))

@[dlmf 13.3.E14]
theorem kummerU_ode_contiguous (a b z : ℂ) (hz : z ≠ 0) :
    (a + 1) * z * kummerU (a + 2) (b + 2) z + (z - b) * kummerU (a + 1) (b + 1) z -
      kummerU a b z = 0 := by
  refine eq_zero_of_tendsto_integerComplement (b := b) (f := fun c =>
    (a + 1) * z * kummerU (a + 2) (c + 2) z + (z - c) * kummerU (a + 1) (c + 1) z -
      kummerU a c z) ?_ fun c hc => kummerU_ode_contiguous_of_mem hc hz
  have hc := tendsto_id_integerComplement b
  exact ((tendsto_const_nhds.mul (tendsto_kummerU_add_two (a + 2) b hz)).add
    ((hc.const_sub _).mul (tendsto_kummerU_add_one (a + 1) b hz))).sub
      (tendsto_kummerU a b hz)

@[dlmf 13.3.E16]
theorem iteratedDeriv_kummerM {a b : ℂ} (n : ℕ) (hb : ∀ k : ℕ, b ≠ -k) :
    iteratedDeriv n (kummerM a b) =
      fun z => poch a n / poch b n * kummerM (a + n) (b + n) z := by
  induction n with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb' : ∀ k : ℕ, b + n ≠ -k := not_neg_nat_add_nat hb n
    have hb0 : b + n ≠ 0 := by
      intro h
      exact hb n ((eq_neg_iff_add_eq_zero).2 h)
    funext z
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_kummerM hb' hb0]
    simp only [poch_succ, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
    ring

/-- `z z^{s-1} = z^s` for `z ≠ 0`. -/
private lemma mul_cpow_pred' {z : ℂ} (hz : z ≠ 0) (s : ℂ) : z * z ^ (s - 1) = z ^ s := by
  calc
    z * z ^ (s - 1) = z ^ (1 : ℂ) * z ^ (s - 1) := by rw [cpow_one]
    _ = z ^ ((1 : ℂ) + (s - 1)) := (cpow_add _ _ hz).symm
    _ = z ^ s := by congr 1; ring

/-- Kummer's function is differentiable everywhere. -/
private lemma hasDerivAt_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasDerivAt (kummerM a b) (deriv (kummerM a b) z) z := by
  have h := (hasFPowerSeriesOnBall_kummerM (a := a) hb).analyticAt_of_mem (y := z) (by simp)
  exact h.differentiableAt.hasDerivAt

/-- Product rule for `w^s M(a,b,w)` on the slit plane. -/
private lemma deriv_cpow_mul_kummerM {a b : ℂ} (s : ℂ) (hb : ∀ k : ℕ, b ≠ -k) {z : ℂ}
    (hz : z ∈ slitPlane) :
    deriv (fun w => w ^ s * kummerM a b w) z =
      s * z ^ (s - 1) * kummerM a b z + z ^ s * deriv (kummerM a b) z := by
  have hM := hasDerivAt_kummerM (a := a) hb z
  have hp := (hasDerivAt_id z).cpow_const (c := s) hz
  have h := (hp.mul hM).deriv
  simp only [id_eq, Pi.mul_def, mul_one] at h
  rw [h]

/-- Product rule for `e^{-w} M(a,b,w)`. -/
private lemma deriv_exp_neg_mul_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    deriv (fun w => exp (-w) * kummerM a b w) z =
      -(exp (-z) * kummerM a b z) + exp (-z) * deriv (kummerM a b) z := by
  have hM := hasDerivAt_kummerM (a := a) hb z
  have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-z) * -1) z := (hasDerivAt_id z).neg.cexp
  have h := (he.mul hM).deriv
  simp only [Pi.mul_def] at h
  rw [h]
  ring

/-- Product rule for `w^s e^{-w} M(a,b,w)` on the slit plane. -/
private lemma deriv_cpow_mul_exp_neg_mul_kummerM {a b : ℂ} (s : ℂ) (hb : ∀ k : ℕ, b ≠ -k)
    {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (fun w => w ^ s * exp (-w) * kummerM a b w) z =
      s * z ^ (s - 1) * exp (-z) * kummerM a b z - z ^ s * exp (-z) * kummerM a b z +
        z ^ s * exp (-z) * deriv (kummerM a b) z := by
  have hM := hasDerivAt_kummerM (a := a) hb z
  have hp := (hasDerivAt_id z).cpow_const (c := s) hz
  have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-z) * -1) z := (hasDerivAt_id z).neg.cexp
  have h := ((hp.mul he).mul hM).deriv
  simp only [id_eq, Pi.mul_def, mul_one] at h
  rw [h]
  ring

@[dlmf 13.3.E17]
theorem iterate_mulDerivMul_kummerM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (a - 1) * kummerM a b w) z =
      poch a n * z ^ (a + n - 1) * kummerM (a + n) b z := by
  induction n generalizing z with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : (fun w => w * mulDerivMul^[n] (fun t => t ^ (a - 1) * kummerM a b t) w)
        =ᶠ[𝓝 z] (fun w => poch a n * (w ^ (a + n) * kummerM (a + n) b w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [ih hw, ← mul_cpow_pred' (slitPlane_ne_zero hw) (a + n)]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_kummerM (a + n) hb hz]
    have hA := z_mul_deriv_kummerM_eq_shift_a (a := a + n) hb z
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have e1 : z ^ (a + ((n + 1 : ℕ) : ℂ) - 1) = z ^ (a + n) := by congr 1; push_cast; ring
    have e2 : a + ((n + 1 : ℕ) : ℂ) = a + n + 1 := by push_cast; ring
    have e4 : z ^ (a + n) = z * z ^ (a + n - 1) := (mul_cpow_pred' hz0 _).symm
    rw [e1, e2, poch_succ, e4]
    linear_combination (poch a n * z * z ^ (a + n - 1)) * hA

@[dlmf 13.3.E18]
theorem iteratedDeriv_mul_cpow_kummerM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b - n ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * kummerM a b w) z =
      poch (b - n) n * z ^ (b - n - 1) * kummerM a (b - n) z := by
  induction n generalizing b with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb0 : ∀ k : ℕ, b ≠ -k := by
      intro k hk
      apply hb (k + (n + 1))
      push_cast
      linear_combination hk
    have hbm : ∀ k : ℕ, b - 1 ≠ -k := by
      intro k hk
      apply hb (k + n)
      push_cast
      linear_combination hk
    have hbn' : ∀ k : ℕ, b - 1 - n ≠ -k := by
      intro k hk
      apply hb k
      push_cast
      linear_combination hk
    have heq : deriv (fun w => w ^ (b - 1) * kummerM a b w) =ᶠ[𝓝 z]
        (fun w => (b - 1) * (w ^ (b - 1 - 1) * kummerM a (b - 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_cpow_mul_kummerM (b - 1) hb0 hw]
      have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hbm w
      have hw0 : w ≠ 0 := slitPlane_ne_zero hw
      have e : w ^ (b - 1) = w * w ^ (b - 1 - 1) := (mul_cpow_pred' hw0 _).symm
      rw [e]
      linear_combination (w ^ (b - 1 - 1)) * hB
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih hbn']
    rw [show b - 1 - (n : ℂ) = b - ((n + 1 : ℕ) : ℂ) by push_cast; ring, poch_succ,
      show b - ((n + 1 : ℕ) : ℂ) + (n : ℂ) = b - 1 by push_cast; ring]
    ring

@[dlmf 13.3.E19]
theorem iterate_mulDerivMul_exp_neg_kummerM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (b - a - 1) * exp (-w) * kummerM a b w) z =
      poch (b - a) n * z ^ (b - a + n - 1) * exp (-z) * kummerM (a - n) b z := by
  induction n generalizing z with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : (fun w => w * mulDerivMul^[n]
          (fun t => t ^ (b - a - 1) * exp (-t) * kummerM a b t) w) =ᶠ[𝓝 z]
        (fun w => poch (b - a) n * (w ^ (b - a + n) * exp (-w) * kummerM (a - n) b w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [ih hw, ← mul_cpow_pred' (slitPlane_ne_zero hw) (b - a + n)]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_exp_neg_mul_kummerM (b - a + n) hb hz]
    have hC := z_mul_deriv_kummerM_eq_shift_a_pred (a := a - n) hb z
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have e1 : z ^ (b - a + ((n + 1 : ℕ) : ℂ) - 1) = z ^ (b - a + n) := by
      congr 1; push_cast; ring
    have e2 : a - ((n + 1 : ℕ) : ℂ) = a - n - 1 := by push_cast; ring
    have e4 : z ^ (b - a + n) = z * z ^ (b - a + n - 1) := (mul_cpow_pred' hz0 _).symm
    rw [e1, e2, poch_succ, e4]
    linear_combination (poch (b - a) n * z * z ^ (b - a + n - 1) * exp (-z)) * hC

@[dlmf 13.3.E20]
theorem iteratedDeriv_exp_neg_kummerM {a b : ℂ} (n : ℕ) (hb : ∀ k : ℕ, b ≠ -k) :
    iteratedDeriv n (fun w => exp (-w) * kummerM a b w) =
      fun z => (-1 : ℂ) ^ n * poch (b - a) n / poch b n * exp (-z) *
        kummerM a (b + n) z := by
  induction n generalizing b with
  | zero =>
    funext z
    simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
    have hb0 : b ≠ 0 := by simpa using hb 0
    have hd : deriv (fun w => exp (-w) * kummerM a b w) =
        fun w => -(b - a) / b * (exp (-w) * kummerM a (b + 1) w) := by
      funext w
      rw [deriv_exp_neg_mul_kummerM hb w]
      have hD := deriv_kummerM_eq_shift_b_succ (a := a) hb w
      field_simp
      linear_combination hD
    funext z
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih hb1]
    beta_reduce
    have hp : poch (b + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat hb1 n
    rw [show b + 1 + (n : ℂ) = b + ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show b + 1 - a = b - a + 1 by ring, poch_succ_left (b - a), poch_succ_left b, pow_succ]
    field_simp

@[dlmf 13.3.E21]
theorem iteratedDeriv_mul_cpow_exp_neg_kummerM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b - n ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * exp (-w) * kummerM a b w) z =
      poch (b - n) n * z ^ (b - n - 1) * exp (-z) * kummerM (a - n) (b - n) z := by
  induction n generalizing a b with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb0 : ∀ k : ℕ, b ≠ -k := by
      intro k hk
      apply hb (k + (n + 1))
      push_cast
      linear_combination hk
    have hbm : ∀ k : ℕ, b - 1 ≠ -k := by
      intro k hk
      apply hb (k + n)
      push_cast
      linear_combination hk
    have hbn' : ∀ k : ℕ, b - 1 - n ≠ -k := by
      intro k hk
      apply hb k
      push_cast
      linear_combination hk
    have heq : deriv (fun w => w ^ (b - 1) * exp (-w) * kummerM a b w) =ᶠ[𝓝 z]
        (fun w => (b - 1) * (w ^ (b - 1 - 1) * exp (-w) * kummerM (a - 1) (b - 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_cpow_mul_exp_neg_mul_kummerM (b - 1) hb0 hw]
      have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hbm w
      have h4 := kummerM_contiguous_shift_a (a := a) hbm (z := w)
      rw [sub_add_cancel] at h4
      have hw0 : w ≠ 0 := slitPlane_ne_zero hw
      have e : w ^ (b - 1) = w * w ^ (b - 1 - 1) := (mul_cpow_pred' hw0 _).symm
      rw [e]
      linear_combination (w ^ (b - 1 - 1) * exp (-w)) * hB + (w ^ (b - 1 - 1) * exp (-w)) * h4
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih hbn']
    rw [show b - 1 - (n : ℂ) = b - ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show a - 1 - (n : ℂ) = a - ((n + 1 : ℕ) : ℂ) by push_cast; ring, poch_succ,
      show b - ((n + 1 : ℕ) : ℂ) + (n : ℂ) = b - 1 by push_cast; ring]
    ring

/-! ### Derivatives of Tricomi's function -/

/-- Kummer's function has derivative `(a/b) M(a+1,b+1,z)`. -/
theorem hasDerivAt_kummerM_shift {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasDerivAt (kummerM a b) (a / b * kummerM (a + 1) (b + 1) z) z := by
  have h := (hasFPowerSeriesOnBall_kummerM (a := a) hb).analyticAt_of_mem (y := z) (by simp)
  have hb0 : b ≠ 0 := by simpa using hb 0
  rw [← deriv_kummerM hb hb0]
  exact h.differentiableAt.hasDerivAt

/-- Derivative of Tricomi's function at noninteger second parameter. -/
theorem hasDerivAt_kummerU_of_mem (a : ℂ) {c w : ℂ} (hc : c ∈ integerComplement)
    (hw : w ∈ slitPlane) :
    HasDerivAt (kummerU a c) (-a * kummerU (a + 1) (c + 1) w) w := by
  by_cases ha : a = 0
  · subst ha
    have : kummerU 0 c = fun _ => 1 := funext fun w => kummerU_zero c w
    rw [this, neg_zero, zero_mul]
    exact hasDerivAt_const _ _
  have hw0 := slitPlane_ne_zero hw
  have hcz := forall_of_mem_integerComplement hc
  have hc1 : c + 1 ∈ integerComplement := by
    simpa using (add_intCast_mem_integerComplement (x := c) 1).mpr hc
  have h2c : 2 - c ∈ integerComplement := by
    have := (add_intCast_mem_integerComplement (x := -c) 2).mpr (by
      intro ⟨k, hk⟩; exact hc ⟨-k, by push_cast; linear_combination -hk⟩)
    simpa [sub_eq_neg_add, add_comm] using this
  have hcnp := not_neg_nat_of_mem_integerComplement hc
  have h2cnp := not_neg_nat_of_mem_integerComplement h2c
  have h1cnp : ∀ k : ℕ, (2 - c) - 1 ≠ -k := by
    have h1c : 1 - c ∈ integerComplement := by
      have := (add_intCast_mem_integerComplement (x := -c) 1).mpr (by
        intro ⟨k, hk⟩; exact hc ⟨-k, by push_cast; linear_combination -hk⟩)
      simpa [sub_eq_neg_add, add_comm] using this
    simpa [show (2 : ℂ) - c - 1 = 1 - c by ring] using not_neg_nat_of_mem_integerComplement h1c
  have hfun : kummerU a c = fun w => kummerUConnection a c w :=
    funext fun w => kummerU_eq_connection a c w hcz
  rw [hfun, kummerU_eq_connection (a + 1) (c + 1) w (forall_of_mem_integerComplement hc1)]
  unfold kummerUConnection
  have hM1 := hasDerivAt_kummerM_shift (a := a) hcnp w
  have hM2 := hasDerivAt_kummerM_shift (a := a - c + 1) h2cnp w
  have hp : HasDerivAt (fun w : ℂ => w ^ (1 - c)) ((1 - c) * w ^ (1 - c - 1)) w := by
    simpa using (hasDerivAt_id w).cpow_const (c := 1 - c) hw
  have hD := ((hM1.const_mul (Gamma (1 - c) / Gamma (a - c + 1))).add
    ((hp.const_mul (Gamma (c - 1) / Gamma a)).mul hM2))
  refine hD.congr_deriv ?_
  -- Gamma recurrences
  have hc0 : c ≠ 0 := by simpa using hcz 0
  have hc10 : c - 1 ≠ 0 := fun h => hcz 1 (by push_cast; linear_combination h)
  have hG1 : Gamma (1 - c) = -c * Gamma (-c) := by
    rw [show (1 : ℂ) - c = -c + 1 by ring, Gamma_add_one _ (neg_ne_zero.mpr hc0)]
  have hG2 : Gamma c = (c - 1) * Gamma (c - 1) := by
    rw [← Gamma_add_one _ hc10]; ring_nf
  have hG3 : Gamma (a + 1) = a * Gamma a := Gamma_add_one _ ha
  have hmix := kummerM_contiguous_mixed_b_pred (a := a - c + 1) (b := 2 - c) h1cnp (z := w)
  have hpow1 : w ^ (1 - c - 1) = w ^ (-c) := by ring_nf
  have hpow2 : w ^ (1 - c) = w * w ^ (-c) := by
    rw [show (1 : ℂ) - c = 1 + -c by ring, cpow_add _ _ hw0, cpow_one]
  rw [show (c + 1 : ℂ) - 1 = c by ring, show (a + 1 : ℂ) - (c + 1) + 1 = a - c + 1 by ring,
    show (1 : ℂ) - (c + 1) = -c by ring, show (2 : ℂ) - (c + 1) = 2 - c - 1 by ring, hpow1]
  have hY : Gamma (1 - c) / Gamma (a - c + 1) = -c * (Gamma (-c) / Gamma (a - c + 1)) := by
    rw [hG1, mul_div_assoc]
  have hX : Gamma c / Gamma (a + 1) = (c - 1) / a * (Gamma (c - 1) / Gamma a) := by
    rw [hG2, hG3, mul_div_mul_comm]
  have h2c0 : (2 : ℂ) - c ≠ 0 := fun h => hcz 2 (by push_cast; linear_combination -h)
  rw [hY, hX, hpow2]
  generalize Gamma (-c) / Gamma (a - c + 1) = Y
  generalize Gamma (c - 1) / Gamma a = X
  field_simp
  linear_combination (X * w ^ (-c)) * hmix

/-- **Derivative of Tricomi's function** for every second parameter, on the slit plane. -/
theorem hasDerivAt_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (kummerU a b) (-a * kummerU (a + 1) (b + 1) z) z := by
  have := integerComplement_nhdsWithin_neBot b
  refine hasDerivAt_of_tendstoUniformlyOnFilter (l := 𝓝[integerComplement] b)
    (f := fun c => kummerU a c) (f' := fun c w => -a * kummerU (a + 1) (c + 1) w)
    (g' := fun w => -a * kummerU (a + 1) (b + 1) w) ?_ ?_ ?_
  · have hc : ContinuousAt (fun p : ℂ × ℂ => -a * kummerU (a + 1) (p.1 + 1) p.2) (b, z) := by
      have h := continuousAt_kummerU (a + 1) (b + 1) hz
      have hf : ContinuousAt (fun p : ℂ × ℂ => (a + 1, p.1 + 1, p.2)) (b, z) := by fun_prop
      exact continuousAt_const.mul
        (ContinuousAt.comp (g := fun q : ℂ × ℂ × ℂ => kummerU q.1 q.2.1 q.2.2)
          (f := fun p : ℂ × ℂ => (a + 1, p.1 + 1, p.2)) h hf)
    exact tendstoUniformlyOnFilter_of_continuousAt
      (F := fun c w => -a * kummerU (a + 1) (c + 1) w) hc nhdsWithin_le_nhds
  · have hm : integerComplement ×ˢ slitPlane ∈ 𝓝[integerComplement] b ×ˢ 𝓝 z :=
      prod_mem_prod self_mem_nhdsWithin (isOpen_slitPlane.mem_nhds hz)
    filter_upwards [hm] with p hp
    exact hasDerivAt_kummerU_of_mem a hp.1 hp.2
  · filter_upwards [isOpen_slitPlane.mem_nhds hz] with y hy
    exact tendsto_kummerU a b (slitPlane_ne_zero hy)

/-- Derivative of Tricomi U. `U` is not complex-differentiable on the cut, so `z` is restricted to
the slit plane. -/
@[dlmf 13.3.E22]
theorem deriv_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (kummerU a b) z = -a * kummerU (a + 1) (b + 1) z :=
  (hasDerivAt_kummerU a b hz).deriv

/-- Product rule for `w^s U(a,b,w)` on the slit plane, with `U' = -a U(a+1,b+1,·)`. -/
private lemma deriv_cpow_mul_kummerU (a b s : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (fun w => w ^ s * kummerU a b w) z =
      s * z ^ (s - 1) * kummerU a b z + z ^ s * (-a * kummerU (a + 1) (b + 1) z) := by
  have hU := hasDerivAt_kummerU a b hz
  have hp := (hasDerivAt_id z).cpow_const (c := s) hz
  have h := (hp.mul hU).deriv
  simp only [id_eq, Pi.mul_def, mul_one] at h
  rw [h]

/-- Product rule for `e^{-w} U(a,b,w)` on the slit plane. -/
private lemma deriv_exp_neg_mul_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (fun w => exp (-w) * kummerU a b w) z =
      -(exp (-z) * kummerU a b z) + exp (-z) * (-a * kummerU (a + 1) (b + 1) z) := by
  have hU := hasDerivAt_kummerU a b hz
  have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-z) * -1) z := (hasDerivAt_id z).neg.cexp
  have h := (he.mul hU).deriv
  simp only [Pi.mul_def] at h
  rw [h]
  ring

/-- Product rule for `w^s e^{-w} U(a,b,w)` on the slit plane. -/
private lemma deriv_cpow_mul_exp_neg_mul_kummerU (a b s : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (fun w => w ^ s * exp (-w) * kummerU a b w) z =
      s * z ^ (s - 1) * exp (-z) * kummerU a b z - z ^ s * exp (-z) * kummerU a b z +
        z ^ s * exp (-z) * (-a * kummerU (a + 1) (b + 1) z) := by
  have hU := hasDerivAt_kummerU a b hz
  have hp := (hasDerivAt_id z).cpow_const (c := s) hz
  have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-z) * -1) z := (hasDerivAt_id z).neg.cexp
  have h := ((hp.mul he).mul hU).deriv
  simp only [id_eq, Pi.mul_def, mul_one] at h
  rw [h]
  ring

/-- Iterated derivatives of Tricomi U. `U` is not complex-differentiable on the cut, so `z` is
restricted to the slit plane. -/
@[dlmf 13.3.E23]
theorem iteratedDeriv_kummerU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (kummerU a b) z =
      (-1 : ℂ) ^ n * poch a n * kummerU (a + n) (b + n) z := by
  induction n generalizing a b with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : deriv (kummerU a b) =ᶠ[𝓝 z] fun w => -a * kummerU (a + 1) (b + 1) w := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact deriv_kummerU a b hw
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih,
      poch_succ_left]
    rw [show a + 1 + (n : ℂ) = a + ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show b + 1 + (n : ℂ) = b + ((n + 1 : ℕ) : ℂ) by push_cast; ring, pow_succ]
    ring

@[dlmf 13.3.E24]
theorem iterate_mulDerivMul_kummerU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (a - 1) * kummerU a b w) z =
      poch a n * poch (a - b + 1) n * z ^ (a + n - 1) * kummerU (a + n) b z := by
  induction n generalizing z with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : (fun w => w * mulDerivMul^[n] (fun t => t ^ (a - 1) * kummerU a b t) w)
        =ᶠ[𝓝 z] (fun w => poch a n * poch (a - b + 1) n *
          (w ^ (a + n) * kummerU (a + n) b w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [ih hw, ← mul_cpow_pred' (slitPlane_ne_zero hw) (a + n)]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_kummerU _ _ (a + n) hz]
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have hA := kummerU_contiguous_shift_a (a + n + 1) b z hz0
    rw [add_sub_cancel_right] at hA
    have e1 : z ^ (a + ((n + 1 : ℕ) : ℂ) - 1) = z ^ (a + n) := by congr 1; push_cast; ring
    have e2 : a + ((n + 1 : ℕ) : ℂ) = a + n + 1 := by push_cast; ring
    have e4 : z ^ (a + n) = z * z ^ (a + n - 1) := (mul_cpow_pred' hz0 _).symm
    rw [e1, e2, poch_succ, poch_succ, e4]
    linear_combination (poch a n * poch (a - b + 1) n * z * z ^ (a + n - 1) * (a + n)) * hA

@[dlmf 13.3.E25]
theorem iteratedDeriv_mul_cpow_kummerU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * kummerU a b w) z =
      (-1 : ℂ) ^ n * poch (a - b + 1) n * z ^ (b - n - 1) * kummerU a (b - n) z := by
  induction n generalizing b with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : deriv (fun w => w ^ (b - 1) * kummerU a b w) =ᶠ[𝓝 z]
        (fun w => -(a - b + 1) * (w ^ (b - 1 - 1) * kummerU a (b - 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_cpow_mul_kummerU _ _ (b - 1) hw]
      have hw0 : w ≠ 0 := slitPlane_ne_zero hw
      have h1 := kummerU_contiguous_shift_a (a + 1) b w hw0
      rw [add_sub_cancel_right] at h1
      have h2 := kummerU_contiguous_a_b a b w hw0
      have e : w ^ (b - 1) = w * w ^ (b - 1 - 1) := (mul_cpow_pred' hw0 _).symm
      rw [e]
      linear_combination (w ^ (b - 1 - 1) * a) * h1 + (w ^ (b - 1 - 1) * (b - a - 1)) * h2
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih]
    rw [show b - 1 - (n : ℂ) = b - ((n + 1 : ℕ) : ℂ) by push_cast; ring, poch_succ_left,
      show a - (b - 1) + 1 = a - b + 1 + 1 by ring, pow_succ]
    ring

@[dlmf 13.3.E26]
theorem iterate_mulDerivMul_exp_neg_kummerU (a b : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (b - a - 1) * exp (-w) * kummerU a b w) z =
      (-1 : ℂ) ^ n * z ^ (b - a + n - 1) * exp (-z) * kummerU (a - n) b z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have heq : (fun w => w * mulDerivMul^[n]
          (fun t => t ^ (b - a - 1) * exp (-t) * kummerU a b t) w) =ᶠ[𝓝 z]
        (fun w => (-1 : ℂ) ^ n * (w ^ (b - a + n) * exp (-w) * kummerU (a - n) b w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [ih hw, ← mul_cpow_pred' (slitPlane_ne_zero hw) (b - a + n)]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_exp_neg_mul_kummerU _ _ (b - a + n) hz]
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have h1 := kummerU_contiguous_shift_a (a - n) b z hz0
    have h2 := kummerU_contiguous_a_b (a - n) (b + 1) z hz0
    rw [add_sub_cancel_right] at h2
    have e1 : z ^ (b - a + ((n + 1 : ℕ) : ℂ) - 1) = z ^ (b - a + n) := by
      congr 1; push_cast; ring
    have e2 : a - ((n + 1 : ℕ) : ℂ) = a - n - 1 := by push_cast; ring
    have e4 : z ^ (b - a + n) = z * z ^ (b - a + n - 1) := (mul_cpow_pred' hz0 _).symm
    rw [e1, e2, show a - (n : ℂ) + 1 = a - n + 1 by ring, e4, pow_succ]
    linear_combination ((-1 : ℂ) ^ n * z * z ^ (b - a + n - 1) * exp (-z)) * h1 +
      ((-1 : ℂ) ^ n * z * z * z ^ (b - a + n - 1) * exp (-z)) * h2

/-- Iterated derivatives of `exp (-z) * U(a,b,z)`. `U` is not complex-differentiable on the cut, so
`z` is restricted to the slit plane. -/
@[dlmf 13.3.E27]
theorem iteratedDeriv_exp_neg_kummerU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w) * kummerU a b w) z =
      (-1 : ℂ) ^ n * exp (-z) * kummerU a (b + n) z := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    have heq : deriv (fun w => exp (-w) * kummerU a b w) =ᶠ[𝓝 z]
        (fun w => -1 * (exp (-w) * kummerU a (b + 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_exp_neg_mul_kummerU _ _ hw]
      have h := kummerU_contiguous_a_b a (b + 1) w (slitPlane_ne_zero hw)
      rw [add_sub_cancel_right] at h
      linear_combination (exp (-w)) * h
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih,
      show b + 1 + (n : ℂ) = b + ((n + 1 : ℕ) : ℂ) by push_cast; ring, pow_succ]
    ring

@[dlmf 13.3.E28]
theorem iteratedDeriv_mul_cpow_exp_neg_kummerU (a b : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * exp (-w) * kummerU a b w) z =
      (-1 : ℂ) ^ n * z ^ (b - n - 1) * exp (-z) * kummerU (a - n) (b - n) z := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
    have heq : deriv (fun w => w ^ (b - 1) * exp (-w) * kummerU a b w) =ᶠ[𝓝 z]
        (fun w => -1 * (w ^ (b - 1 - 1) * exp (-w) * kummerU (a - 1) (b - 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_cpow_mul_exp_neg_mul_kummerU _ _ (b - 1) hw]
      have hw0 : w ≠ 0 := slitPlane_ne_zero hw
      have h1 := kummerU_contiguous_shift_a (a + 1) b w hw0
      rw [add_sub_cancel_right] at h1
      have h2 := kummerU_contiguous_a_b a b w hw0
      have h3 := kummerU_contiguous_shift_a a (b - 1) w hw0
      rw [sub_add_cancel] at h3
      have e : w ^ (b - 1) = w * w ^ (b - 1 - 1) := (mul_cpow_pred' hw0 _).symm
      rw [e]
      linear_combination (w ^ (b - 1 - 1) * exp (-w) * a) * h1 +
        (w ^ (b - 1 - 1) * exp (-w) * (b - a - 1)) * h2 + (w ^ (b - 1 - 1) * exp (-w)) * h3
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih]
    rw [show b - 1 - (n : ℂ) = b - ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show a - 1 - (n : ℂ) = a - ((n + 1 : ℕ) : ℂ) by push_cast; ring, pow_succ]
    ring

@[dlmf 13.15.E1]
theorem whittakerM_contiguous_kappa {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * whittakerM (κ - 1) μ z + (z - 2 * κ) * whittakerM κ μ z +
      (κ + μ + 1 / 2) * whittakerM (κ + 1) μ z = 0 := by
  have hM := kummerM_contiguous_a (a := μ - κ + 1 / 2) hμ (z := z)
  rw [show μ - κ + 1 / 2 - 1 = μ - (κ + 1) + 1 / 2 by ring,
    show μ - κ + 1 / 2 + 1 = μ - (κ - 1) + 1 / 2 by ring] at hM
  unfold whittakerM
  linear_combination (exp (-z / 2) * z ^ (μ + 1 / 2)) * hM

@[dlmf 13.15.E2]
theorem whittakerM_contiguous_mu {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * (z : ℂ) ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ - 1 / 2) z -
      (z + 2 * μ) * (1 + 2 * μ) * whittakerM κ μ z +
      (κ + μ + 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := kummerM_contiguous_b (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show μ + 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM +
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (1 + 2 * μ - (μ - κ + 1 / 2)) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ + 1) z) * hs

@[dlmf 13.15.E3]
theorem whittakerM_contiguous_shift {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * whittakerM (κ - 1 / 2) (μ + 1 / 2) z +
      (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM κ μ z -
      (κ + μ + 1 / 2) * whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hM := kummerM_contiguous_shift_b_succ (a := μ - κ + 1 / 2) hμ (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  unfold whittakerM
  rw [show μ + 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 + 1 by ring,
    show μ + 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP]
  linear_combination (-(exp (-z / 2) * z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ))) * hM

@[dlmf 13.15.E4]
theorem whittakerM_contiguous_half {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * whittakerM (κ - 1 / 2) (μ - 1 / 2) z -
      2 * μ * whittakerM (κ + 1 / 2) (μ - 1 / 2) z -
      z ^ (1 / 2 : ℂ) * whittakerM κ μ z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := kummerM_contiguous_shift_a (a := μ - κ + 1 / 2) hb1 (z := z)
  rw [sub_add_cancel] at hM
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show μ - 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 - 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2)) * hM -
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) z) * hs

@[dlmf 13.15.E5]
theorem whittakerM_contiguous_mixed {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * whittakerM κ μ z -
      2 * μ * (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ - 1 / 2) z -
      (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := kummerM_contiguous_mixed_b_pred (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show μ + 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM +
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (μ - κ + 1 / 2) *
      kummerM (μ - κ + 1 / 2 + 1) (1 + 2 * μ + 1) z) * hs

@[dlmf 13.15.E6]
theorem whittakerM_contiguous_up {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ - 1 / 2) z +
      (z - 2 * μ) * (1 + 2 * μ) * whittakerM κ μ z +
      (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := kummerM_contiguous_up_aux (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 - 1 by ring,
    show μ + 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM -
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (μ - κ + 1 / 2) *
      kummerM (μ - κ + 1 / 2 + 1) (1 + 2 * μ + 1) z) * hs

@[dlmf 13.15.E7]
theorem whittakerM_contiguous_up_shift {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ - 1 / 2) z -
      2 * μ * (1 + 2 * μ) * whittakerM κ μ z +
      (κ + μ + 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := kummerM_contiguous_up_shift_aux (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 - 1 by ring,
    show μ + 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM +
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (1 + 2 * μ - (μ - κ + 1 / 2)) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ + 1) z) * hs

/-- Powers in the Whittaker prefactors. -/
theorem cpow_add_half {z : ℂ} (hz : z ≠ 0) (s : ℂ) : z ^ (s + 1 / 2) = z ^ (1 / 2 : ℂ) * z ^ s := by
  rw [cpow_add _ _ hz, mul_comm]

/-- Powers in the Whittaker prefactors. -/
theorem whittaker_pows {z μ : ℂ} (hz0 : z ≠ 0) :
    z ^ (1 / 2 + μ) = z ^ (1 / 2 : ℂ) * z ^ μ ∧
    z ^ (1 / 2 + (μ + 1 / 2)) = z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) * z ^ μ ∧
    z ^ (1 / 2 + (μ - 1 / 2)) = z ^ μ ∧
    z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
  refine ⟨by rw [cpow_add _ _ hz0], ?_, by congr 1; ring, ?_⟩
  · rw [show (1 : ℂ) / 2 + (μ + 1 / 2) = 1 / 2 + 1 / 2 + μ by ring, cpow_add _ _ hz0,
      cpow_add _ _ hz0]
  · rw [← cpow_add _ _ hz0]; norm_num

@[dlmf 13.15.E8]
theorem whittakerW_contiguous_up (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW (κ + 1 / 2) (μ + 1 / 2) z - z ^ (1 / 2 : ℂ) * whittakerW κ μ z +
      (κ - μ - 1 / 2) * whittakerW (κ - 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  have h := kummerU_contiguous_a_b (1 / 2 + μ - κ) (1 + 2 * μ + 1) z hz0
  unfold whittakerW
  rw [show 1 / 2 + (μ + 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 / 2 + (μ + 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ + 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring,
    show 1 / 2 + (μ + 1 / 2) = (1 / 2 + μ) + 1 / 2 by ring, cpow_add_half hz0]
  rw [show 1 + 2 * μ + 1 - 1 = 1 + 2 * μ by ring] at h
  linear_combination exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ (1 / 2 + μ) * h

@[dlmf 13.15.E9]
theorem whittakerW_contiguous_down (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW (κ + 1 / 2) (μ - 1 / 2) z - z ^ (1 / 2 : ℂ) * whittakerW κ μ z +
      (κ + μ - 1 / 2) * whittakerW (κ - 1 / 2) (μ - 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  have h := kummerU_contiguous_shift_a (1 / 2 + μ - κ) (1 + 2 * μ - 1) z hz0
  unfold whittakerW
  rw [show 1 / 2 + (μ - 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ - 1 by ring,
    show 1 / 2 + (μ - 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show (1 : ℂ) / 2 + (μ - 1 / 2) = μ by ring,
    show z ^ (1 / 2 + μ) = z ^ (1 / 2 : ℂ) * z ^ μ by rw [cpow_add _ _ hz0]]
  rw [show 1 + 2 * μ - 1 + 1 = 1 + 2 * μ by ring] at h
  have hzz : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  linear_combination exp (-z / 2) * z ^ μ * h - exp (-z / 2) * z ^ μ *
    kummerU (1 / 2 + μ - κ) (1 + 2 * μ) z * hzz

@[dlmf 13.15.E10]
theorem whittakerW_contiguous_mu (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    2 * μ * whittakerW κ μ z - z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ + 1 / 2) z +
      z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ - 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨p1, p2, p3, hzz⟩ := whittaker_pows (μ := μ) hz0
  have h10 := kummerU_contiguous_shift_a (1 / 2 + μ - κ) (1 + 2 * μ) z hz0
  have h9 := kummerU_contiguous_a_b (1 / 2 + μ - κ - 1) (1 + 2 * μ) z hz0
  rw [show 1 / 2 + μ - κ - 1 + 1 = 1 / 2 + μ - κ by ring] at h9
  unfold whittakerW
  rw [show 1 / 2 + (μ + 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 / 2 + (μ - 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring, p1, p2, p3]
  linear_combination exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * (h10 - h9) -
    exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * kummerU (1 / 2 + μ - κ) (1 + 2 * μ + 1) z * hzz

@[dlmf 13.15.E11]
theorem whittakerW_contiguous_kappa (κ μ z : ℂ) (hz : z ≠ 0) :
    whittakerW (κ + 1) μ z + (2 * κ - z) * whittakerW κ μ z +
      (κ - μ - 1 / 2) * (κ + μ - 1 / 2) * whittakerW (κ - 1) μ z = 0 := by
  have h7 := kummerU_contiguous_a (1 / 2 + μ - κ) (1 + 2 * μ) z hz
  unfold whittakerW
  rw [show 1 / 2 + μ - (κ + 1) = 1 / 2 + μ - κ - 1 by ring,
    show 1 / 2 + μ - (κ - 1) = 1 / 2 + μ - κ + 1 by ring]
  linear_combination exp (-z / 2) * z ^ (1 / 2 + μ) * h7

@[dlmf 13.15.E12]
theorem whittakerW_contiguous_mixed (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ + 1 / 2) z +
      2 * μ * whittakerW κ μ z -
      (κ + μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ - 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨p1, p2, p3, hzz⟩ := whittaker_pows (μ := μ) hz0
  have h14 := kummerU_ode_contiguous (1 / 2 + μ - κ - 1) (1 + 2 * μ - 1) z hz0
  have h10 := kummerU_contiguous_shift_a (1 / 2 + μ - κ) (1 + 2 * μ - 1) z hz0
  rw [show 1 / 2 + μ - κ - 1 + 2 = 1 / 2 + μ - κ + 1 by ring,
    show 1 + 2 * μ - 1 + 2 = 1 + 2 * μ + 1 by ring,
    show 1 / 2 + μ - κ - 1 + 1 = 1 / 2 + μ - κ by ring,
    show 1 + 2 * μ - 1 + 1 = 1 + 2 * μ by ring] at h14
  rw [show 1 + 2 * μ - 1 + 1 = 1 + 2 * μ by ring] at h10
  unfold whittakerW
  rw [show 1 / 2 + (μ + 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ + 1 by ring,
    show 1 / 2 + (μ - 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring, p1, p2, p3]
  linear_combination (-(exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ)) * (h14 + h10) +
    (κ - μ - 1 / 2) * exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * kummerU (1 / 2 + μ - κ + 1) (1 + 2 * μ + 1) z * hzz

@[dlmf 13.15.E13]
theorem whittakerW_contiguous_sum (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (κ + μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ - 1 / 2) z -
      (z + 2 * μ) * whittakerW κ μ z +
      z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨p1, p2, p3, hzz⟩ := whittaker_pows (μ := μ) hz0
  have h8 := kummerU_contiguous_b (1 / 2 + μ - κ) (1 + 2 * μ) z hz0
  unfold whittakerW
  rw [show 1 / 2 + (μ - 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 / 2 + (μ + 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring, p1, p2, p3]
  linear_combination exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * h8 +
    exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * kummerU (1 / 2 + μ - κ) (1 + 2 * μ + 1) z * hzz

@[dlmf 13.15.E14]
theorem whittakerW_contiguous_diff (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ + 1 / 2) z -
      (z - 2 * μ) * whittakerW κ μ z +
      z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ - 1 / 2) z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨p1, p2, p3, hzz⟩ := whittaker_pows (μ := μ) hz0
  have h14 := kummerU_ode_contiguous (1 / 2 + μ - κ - 1) (1 + 2 * μ - 1) z hz0
  rw [show 1 / 2 + μ - κ - 1 + 2 = 1 / 2 + μ - κ + 1 by ring,
    show 1 + 2 * μ - 1 + 2 = 1 + 2 * μ + 1 by ring,
    show 1 / 2 + μ - κ - 1 + 1 = 1 / 2 + μ - κ by ring,
    show 1 + 2 * μ - 1 + 1 = 1 + 2 * μ by ring] at h14
  unfold whittakerW
  rw [show 1 / 2 + (μ + 1 / 2) - (κ - 1 / 2) = 1 / 2 + μ - κ + 1 by ring,
    show 1 / 2 + (μ - 1 / 2) - (κ + 1 / 2) = 1 / 2 + μ - κ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring, p1, p2, p3]
  linear_combination (-(exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ)) * h14 +
    (κ - μ - 1 / 2) * exp (-z / 2) * z ^ (1 / 2 : ℂ) * z ^ μ * kummerU (1 / 2 + μ - κ + 1) (1 + 2 * μ + 1) z * hzz

/-- Iterates of `mulDerivMul` only depend on the function near the point. -/
private lemma iterate_mulDerivMul_congr {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (h : ∀ w ∈ U, f w = g w) (n : ℕ) :
    ∀ w ∈ U, mulDerivMul^[n] f w = mulDerivMul^[n] g w := by
  induction n with
  | zero => intro w hw; simpa using h w hw
  | succ n ih =>
    intro w hw
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', mulDerivMul, mulDerivMul]
    congr 1
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hU.mem_nhds hw] with t ht
    rw [ih t ht]

/-- `e^{w/2} e^{-w/2} = 1`. -/
private lemma exp_half_mul_exp_neg_half (w : ℂ) : exp (w / 2) * exp (-w / 2) = 1 := by
  rw [← Complex.exp_add, show w / 2 + -w / 2 = (0 : ℂ) by ring, Complex.exp_zero]

/-- `e^{-w/2} e^{-w/2} = e^{-w}`. -/
private lemma exp_neg_half_mul_self (w : ℂ) : exp (-w / 2) * exp (-w / 2) = exp (-w) := by
  rw [← Complex.exp_add]; congr 1; ring

/-- `w^s w^t = w^u` for `w ≠ 0` and `s + t = u`. -/
private lemma cpow_mul_cpow_eq {w : ℂ} (hw : w ≠ 0) {s t u : ℂ} (h : s + t = u) :
    w ^ s * w ^ t = w ^ u := by
  rw [← cpow_add _ _ hw, h]

/-- An iterated Whittaker-M derivative with regular initial and shifted denominators. -/
@[dlmf 13.15.E15]
theorem iteratedDeriv_exp_mul_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane)
    (hshift : ∀ k : ℕ, 1 + 2 * μ - n ≠ -k) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (μ - 1 / 2) * whittakerM κ μ w) z =
      (-1 : ℂ) ^ n * poch (-2 * μ) n * exp (z / 2) * z ^ (μ - (n + 1) / 2) *
        whittakerM (κ - n / 2) (μ - n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (w / 2) * w ^ (μ - 1 / 2) * whittakerM κ μ w) =ᶠ[𝓝 z]
      (fun w => w ^ (1 + 2 * μ - 1) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := μ - 1 / 2) (t := μ + 1 / 2)
      (u := 1 + 2 * μ - 1) (by ring)
    unfold whittakerM
    linear_combination (w ^ (μ - 1 / 2) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * exp_half_mul_exp_neg_half w +
      (kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_mul_cpow_kummerM n hshift hz]
  unfold whittakerM
  rw [show μ - (n : ℂ) / 2 - (κ - n / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring,
    show (-2 * μ : ℂ) = 1 - (1 + 2 * μ - n) - n by ring, DLMF.Hypergeometric.poch_reflect]
  have h2 := cpow_mul_cpow_eq hz0 (s := μ - (n + 1) / 2) (t := μ - n / 2 + 1 / 2)
      (u := 1 + 2 * μ - n - 1) (by ring)
  have hs : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  linear_combination (-(poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (μ - n / 2 + 1 / 2) * exp (z / 2) * exp (-z / 2))) * hs -
    (poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (μ - n / 2 + 1 / 2)) * exp_half_mul_exp_neg_half z -
    (poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2) (1 + 2 * μ - n) z) * h2

@[dlmf 13.15.E16]
theorem iteratedDeriv_exp_mul_whittakerM_neg {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) z =
      poch (1 / 2 + μ - κ) n / poch (1 + 2 * μ) n * exp (z / 2) *
        z ^ (-μ - (n + 1) / 2) * whittakerM (κ - n / 2) (μ + n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) =ᶠ[𝓝 z]
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (w / 2) * exp (-w / 2) = 1 := by
      rw [← Complex.exp_add, show w / 2 + -w / 2 = (0 : ℂ) by ring, Complex.exp_zero]
    have h2 : w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) = 1 := by
      rw [← cpow_add _ _ hw0, show -μ - 1 / 2 + (μ + 1 / 2) = (0 : ℂ) by ring, cpow_zero]
    unfold whittakerM
    linear_combination (w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_kummerM n hμ]
  beta_reduce
  unfold whittakerM
  rw [show μ + (n : ℂ) / 2 - (κ - n / 2) + 1 / 2 = μ - κ + 1 / 2 + n by ring,
    show (1 : ℂ) + 2 * (μ + n / 2) = 1 + 2 * μ + n by ring,
    show (1 : ℂ) / 2 + μ - κ = μ - κ + 1 / 2 by ring]
  have h1 : exp (z / 2) * exp (-z / 2) = 1 := by
    rw [← Complex.exp_add, show z / 2 + -z / 2 = (0 : ℂ) by ring, Complex.exp_zero]
  have h2 : z ^ (-μ - ((n : ℂ) + 1) / 2) * z ^ (μ + n / 2 + 1 / 2) = 1 := by
    rw [← cpow_add _ _ hz0, show -μ - ((n : ℂ) + 1) / 2 + (μ + n / 2 + 1 / 2) = (0 : ℂ) by ring,
      cpow_zero]
  linear_combination (-(poch (μ - κ + 1 / 2) n / poch (1 + 2 * μ) n *
      kummerM (μ - κ + 1 / 2 + n) (1 + 2 * μ + n) z)) * h1 -
    (poch (μ - κ + 1 / 2) n / poch (1 + 2 * μ) n *
      kummerM (μ - κ + 1 / 2 + n) (1 + 2 * μ + n) z * exp (z / 2) * exp (-z / 2)) * h2

@[dlmf 13.15.E17]
theorem iterate_mulDerivMul_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (w / 2) * w ^ (-κ - 1) * whittakerM κ μ w) z =
      poch (1 / 2 + μ - κ) n * exp (z / 2) * z ^ (n - κ - 1) *
        whittakerM (κ - n) μ z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hfun : ∀ w ∈ slitPlane, exp (w / 2) * w ^ (-κ - 1) * whittakerM κ μ w =
      w ^ (μ - κ + 1 / 2 - 1) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w := by
    intro w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (w / 2) * exp (-w / 2) = 1 := by
      rw [← Complex.exp_add, show w / 2 + -w / 2 = (0 : ℂ) by ring, Complex.exp_zero]
    have h2 : w ^ (-κ - 1) * w ^ (μ + 1 / 2) = w ^ (μ - κ + 1 / 2 - 1) := by
      rw [← cpow_add _ _ hw0]; congr 1; ring
    unfold whittakerM
    linear_combination (w ^ (-κ - 1) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [iterate_mulDerivMul_congr isOpen_slitPlane hfun n z hz,
    iterate_mulDerivMul_kummerM n hμ hz]
  unfold whittakerM
  rw [show μ - (κ - (n : ℂ)) + 1 / 2 = μ - κ + 1 / 2 + n by ring,
    show (1 : ℂ) / 2 + μ - κ = μ - κ + 1 / 2 by ring]
  have h1 : exp (z / 2) * exp (-z / 2) = 1 := by
    rw [← Complex.exp_add, show z / 2 + -z / 2 = (0 : ℂ) by ring, Complex.exp_zero]
  have h2 : z ^ ((n : ℂ) - κ - 1) * z ^ (μ + 1 / 2) = z ^ (μ - κ + 1 / 2 + n - 1) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  linear_combination (-(poch (μ - κ + 1 / 2) n * kummerM (μ - κ + 1 / 2 + n) (1 + 2 * μ) z *
      z ^ ((n : ℂ) - κ - 1) * z ^ (μ + 1 / 2))) * h1 -
    (poch (μ - κ + 1 / 2) n * kummerM (μ - κ + 1 / 2 + n) (1 + 2 * μ) z) * h2

/-- An iterated Whittaker-M derivative with regular initial and shifted denominators. -/
@[dlmf 13.15.E18]
theorem iteratedDeriv_exp_neg_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane)
    (hshift : ∀ k : ℕ, 1 + 2 * μ - n ≠ -k) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (μ - 1 / 2) * whittakerM κ μ w) z =
      (-1 : ℂ) ^ n * poch (-2 * μ) n * exp (-z / 2) * z ^ (μ - (n + 1) / 2) *
        whittakerM (κ + n / 2) (μ - n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (-w / 2) * w ^ (μ - 1 / 2) * whittakerM κ μ w) =ᶠ[𝓝 z]
      (fun w => w ^ (1 + 2 * μ - 1) * exp (-w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := μ - 1 / 2) (t := μ + 1 / 2)
      (u := 1 + 2 * μ - 1) (by ring)
    unfold whittakerM
    linear_combination (w ^ (μ - 1 / 2) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * exp_neg_half_mul_self w +
      (exp (-w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_mul_cpow_exp_neg_kummerM n hshift hz]
  unfold whittakerM
  rw [show μ - (n : ℂ) / 2 - (κ + n / 2) + 1 / 2 = μ - κ + 1 / 2 - n by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring,
    show (-2 * μ : ℂ) = 1 - (1 + 2 * μ - n) - n by ring, DLMF.Hypergeometric.poch_reflect]
  have h2 := cpow_mul_cpow_eq hz0 (s := μ - (n + 1) / 2) (t := μ - n / 2 + 1 / 2)
      (u := 1 + 2 * μ - n - 1) (by ring)
  have hs : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  linear_combination (-(poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (μ - n / 2 + 1 / 2) * exp (-z / 2) * exp (-z / 2))) * hs -
    (poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (μ - n / 2 + 1 / 2)) * exp_neg_half_mul_self z -
    (poch (1 + 2 * μ - n) n * kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ - n) z * exp (-z)) * h2

@[dlmf 13.15.E19]
theorem iteratedDeriv_exp_neg_whittakerM_neg {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) z =
      (-1 : ℂ) ^ n * poch (1 / 2 + μ + κ) n / poch (1 + 2 * μ) n * exp (-z / 2) *
        z ^ (-μ - (n + 1) / 2) * whittakerM (κ + n / 2) (μ + n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (-w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) =ᶠ[𝓝 z]
      (fun w => exp (-w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (-w / 2) * exp (-w / 2) = exp (-w) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h2 : w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) = 1 := by
      rw [← cpow_add _ _ hw0, show -μ - 1 / 2 + (μ + 1 / 2) = (0 : ℂ) by ring, cpow_zero]
    unfold whittakerM
    linear_combination (w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (exp (-w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_exp_neg_kummerM n hμ]
  beta_reduce
  unfold whittakerM
  rw [show μ + (n : ℂ) / 2 - (κ + n / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show (1 : ℂ) + 2 * (μ + n / 2) = 1 + 2 * μ + n by ring,
    show (1 : ℂ) + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring]
  have h1 : exp (-z / 2) * exp (-z / 2) = exp (-z) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : z ^ (-μ - ((n : ℂ) + 1) / 2) * z ^ (μ + n / 2 + 1 / 2) = 1 := by
    rw [← cpow_add _ _ hz0, show -μ - ((n : ℂ) + 1) / 2 + (μ + n / 2 + 1 / 2) = (0 : ℂ) by ring,
      cpow_zero]
  linear_combination (-((-1 : ℂ) ^ n * poch (1 / 2 + μ + κ) n / poch (1 + 2 * μ) n *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ + n) z *
      z ^ (-μ - ((n : ℂ) + 1) / 2) * z ^ (μ + n / 2 + 1 / 2))) * h1 -
    ((-1 : ℂ) ^ n * poch (1 / 2 + μ + κ) n / poch (1 + 2 * μ) n *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ + n) z * exp (-z)) * h2

@[dlmf 13.15.E20]
theorem iterate_mulDerivMul_exp_neg_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (-w / 2) * w ^ (κ - 1) * whittakerM κ μ w) z =
      poch (1 / 2 + μ + κ) n * exp (-z / 2) * z ^ (κ + n - 1) *
        whittakerM (κ + n) μ z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hfun : ∀ w ∈ slitPlane, exp (-w / 2) * w ^ (κ - 1) * whittakerM κ μ w =
      w ^ (1 + 2 * μ - (μ - κ + 1 / 2) - 1) * exp (-w) *
        kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w := by
    intro w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (-w / 2) * exp (-w / 2) = exp (-w) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h2 : w ^ (κ - 1) * w ^ (μ + 1 / 2) = w ^ (1 + 2 * μ - (μ - κ + 1 / 2) - 1) := by
      rw [← cpow_add _ _ hw0]; congr 1; ring
    unfold whittakerM
    linear_combination (w ^ (κ - 1) * w ^ (μ + 1 / 2) *
      kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (exp (-w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [iterate_mulDerivMul_congr isOpen_slitPlane hfun n z hz,
    iterate_mulDerivMul_exp_neg_kummerM n hμ hz]
  unfold whittakerM
  rw [show μ - (κ + (n : ℂ)) + 1 / 2 = μ - κ + 1 / 2 - n by ring,
    show (1 : ℂ) + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring]
  have h1 : exp (-z / 2) * exp (-z / 2) = exp (-z) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : z ^ (κ + (n : ℂ) - 1) * z ^ (μ + 1 / 2) = z ^ (1 / 2 + μ + κ + n - 1) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  linear_combination (-(poch (1 / 2 + μ + κ) n * kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ) z *
      z ^ (κ + (n : ℂ) - 1) * z ^ (μ + 1 / 2))) * h1 -
    (poch (1 / 2 + μ + κ) n * kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ) z * exp (-z)) * h2

@[dlmf 13.15.E21]
theorem iteratedDeriv_exp_mul_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * poch (1 / 2 + μ - κ) n * exp (z / 2) *
        z ^ (-μ - (n + 1) / 2) * whittakerW (κ - n / 2) (μ + n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (w / 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) =ᶠ[𝓝 z]
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := -μ - 1 / 2) (t := 1 / 2 + μ)
      (u := 0) (by ring)
    rw [cpow_zero] at h2
    unfold whittakerW
    linear_combination (w ^ (-μ - 1 / 2) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_half_mul_exp_neg_half w +
      (kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + (μ + (n : ℂ) / 2) - (κ - n / 2) = 1 / 2 + μ - κ + n by ring,
    show 1 + 2 * (μ + (n : ℂ) / 2) = 1 + 2 * μ + n by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := -μ - (n + 1) / 2) (t := 1 / 2 + (μ + n / 2))
      (u := 0) (by ring)
  rw [cpow_zero] at h2
  linear_combination (-((-1 : ℂ) ^ n * poch (1 / 2 + μ - κ) n *
    kummerU (1 / 2 + μ - κ + n) (1 + 2 * μ + n) z *
    z ^ (-μ - (n + 1) / 2) * z ^ (1 / 2 + (μ + n / 2)))) * exp_half_mul_exp_neg_half z -
    ((-1 : ℂ) ^ n * poch (1 / 2 + μ - κ) n * kummerU (1 / 2 + μ - κ + n) (1 + 2 * μ + n) z) * h2

@[dlmf 13.15.E22]
theorem iteratedDeriv_exp_mul_whittakerW_pos {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * poch (1 / 2 - μ - κ) n * exp (z / 2) *
        z ^ (μ - (n + 1) / 2) * whittakerW (κ - n / 2) (μ - n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (w / 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) =ᶠ[𝓝 z]
      (fun w => w ^ (1 + 2 * μ - 1) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := μ - 1 / 2) (t := 1 / 2 + μ)
      (u := 1 + 2 * μ - 1) (by ring)
    unfold whittakerW
    linear_combination (w ^ (μ - 1 / 2) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_half_mul_exp_neg_half w +
      (kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_mul_cpow_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + (μ - (n : ℂ) / 2) - (κ - n / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := μ - (n + 1) / 2) (t := 1 / 2 + (μ - n / 2))
      (u := 1 + 2 * μ - n - 1) (by ring)
  linear_combination (-((-1 : ℂ) ^ n * poch (1 / 2 - μ - κ) n *
    kummerU (1 / 2 + μ - κ) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (1 / 2 + (μ - n / 2)))) * exp_half_mul_exp_neg_half z -
    ((-1 : ℂ) ^ n * poch (1 / 2 - μ - κ) n * kummerU (1 / 2 + μ - κ) (1 + 2 * μ - n) z) * h2

@[dlmf 13.15.E23]
theorem iterate_mulDerivMul_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (w / 2) * w ^ (-κ - 1) * whittakerW κ μ w) z =
      poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n * exp (z / 2) *
        z ^ (n - κ - 1) * whittakerW (κ - n) μ z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hfun : ∀ w ∈ slitPlane, exp (w / 2) * w ^ (-κ - 1) * whittakerW κ μ w =
      w ^ (1 / 2 + μ - κ - 1) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w := by
    intro w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := -κ - 1) (t := 1 / 2 + μ)
      (u := 1 / 2 + μ - κ - 1) (by ring)
    unfold whittakerW
    linear_combination (w ^ (-κ - 1) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_half_mul_exp_neg_half w +
      (kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [iterate_mulDerivMul_congr isOpen_slitPlane hfun n z hz,
    iterate_mulDerivMul_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + μ - (κ - (n : ℂ)) = 1 / 2 + μ - κ + n by ring,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := (n : ℂ) - κ - 1) (t := 1 / 2 + μ)
      (u := 1 / 2 + μ - κ + n - 1) (by ring)
  linear_combination (-(poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n *
    kummerU (1 / 2 + μ - κ + n) (1 + 2 * μ) z *
    z ^ ((n : ℂ) - κ - 1) * z ^ (1 / 2 + μ))) * exp_half_mul_exp_neg_half z -
    (poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n *
      kummerU (1 / 2 + μ - κ + n) (1 + 2 * μ) z) * h2

@[dlmf 13.15.E24]
theorem iteratedDeriv_exp_neg_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (-μ - (n + 1) / 2) *
        whittakerW (κ + n / 2) (μ + n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (-w / 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) =ᶠ[𝓝 z]
      (fun w => exp (-w) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := -μ - 1 / 2) (t := 1 / 2 + μ)
      (u := 0) (by ring)
    rw [cpow_zero] at h2
    unfold whittakerW
    linear_combination (w ^ (-μ - 1 / 2) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_neg_half_mul_self w +
      (exp (-w) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_exp_neg_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + (μ + (n : ℂ) / 2) - (κ + n / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ + (n : ℂ) / 2) = 1 + 2 * μ + n by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := -μ - (n + 1) / 2) (t := 1 / 2 + (μ + n / 2))
      (u := 0) (by ring)
  rw [cpow_zero] at h2
  linear_combination (-((-1 : ℂ) ^ n * kummerU (1 / 2 + μ - κ) (1 + 2 * μ + n) z *
    z ^ (-μ - (n + 1) / 2) * z ^ (1 / 2 + (μ + n / 2)))) * exp_neg_half_mul_self z -
    ((-1 : ℂ) ^ n * exp (-z) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ + n) z) * h2

@[dlmf 13.15.E25]
theorem iteratedDeriv_exp_neg_whittakerW_pos {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (μ - (n + 1) / 2) *
        whittakerW (κ + n / 2) (μ - n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (-w / 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) =ᶠ[𝓝 z]
      (fun w => w ^ (1 + 2 * μ - 1) * exp (-w) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := μ - 1 / 2) (t := 1 / 2 + μ)
      (u := 1 + 2 * μ - 1) (by ring)
    unfold whittakerW
    linear_combination (w ^ (μ - 1 / 2) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_neg_half_mul_self w +
      (exp (-w) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_mul_cpow_exp_neg_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + (μ - (n : ℂ) / 2) - (κ + n / 2) = 1 / 2 + μ - κ - n by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := μ - (n + 1) / 2) (t := 1 / 2 + (μ - n / 2))
      (u := 1 + 2 * μ - n - 1) (by ring)
  linear_combination (-((-1 : ℂ) ^ n * kummerU (1 / 2 + μ - κ - n) (1 + 2 * μ - n) z *
    z ^ (μ - (n + 1) / 2) * z ^ (1 / 2 + (μ - n / 2)))) * exp_neg_half_mul_self z -
    ((-1 : ℂ) ^ n * exp (-z) * kummerU (1 / 2 + μ - κ - n) (1 + 2 * μ - n) z) * h2

@[dlmf 13.15.E26]
theorem iterate_mulDerivMul_exp_neg_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (-w / 2) * w ^ (κ - 1) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (κ + n - 1) * whittakerW (κ + n) μ z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hfun : ∀ w ∈ slitPlane, exp (-w / 2) * w ^ (κ - 1) * whittakerW κ μ w =
      w ^ (1 + 2 * μ - (1 / 2 + μ - κ) - 1) * exp (-w) *
        kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w := by
    intro w hw
    have h2 := cpow_mul_cpow_eq (slitPlane_ne_zero hw) (s := κ - 1) (t := 1 / 2 + μ)
      (u := 1 + 2 * μ - (1 / 2 + μ - κ) - 1) (by ring)
    unfold whittakerW
    linear_combination (w ^ (κ - 1) * w ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * exp_neg_half_mul_self w +
      (exp (-w) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) w) * h2
  rw [iterate_mulDerivMul_congr isOpen_slitPlane hfun n z hz,
    iterate_mulDerivMul_exp_neg_kummerU _ _ n hz]
  unfold whittakerW
  rw [show 1 / 2 + μ - (κ + (n : ℂ)) = 1 / 2 + μ - κ - n by ring]
  have h2 := cpow_mul_cpow_eq hz0 (s := κ + (n : ℂ) - 1) (t := 1 / 2 + μ)
      (u := 1 + 2 * μ - (1 / 2 + μ - κ) + n - 1) (by ring)
  linear_combination (-((-1 : ℂ) ^ n * kummerU (1 / 2 + μ - κ - n) (1 + 2 * μ) z *
    z ^ (κ + (n : ℂ) - 1) * z ^ (1 / 2 + μ))) * exp_neg_half_mul_self z -
    ((-1 : ℂ) ^ n * exp (-z) * kummerU (1 / 2 + μ - κ - n) (1 + 2 * μ) z) * h2

end DLMF.Confluent
