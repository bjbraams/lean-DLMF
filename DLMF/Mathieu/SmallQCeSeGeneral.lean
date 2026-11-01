/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.SmallQVector
public import DLMF.Mathieu.SmallQGeneral

/-!
# The expansion DLMF 28.6.26 of `ce_m`, `se_m` for `m ≥ 6`

This file proves DLMF 28.6.26 and its `se` analogue (§28.6(ii)) for `m ≥ 6`, with remainder
`O(q³)`. A trial vector `T_j(m, q)` (`|j| ≤ 2`) rational in `m` has every row of the generic
recurrence `((m + 2j)² - P) T_j + q (T_{j-1} + T_{j+1})` equal to `q³ ceSeResidual m q j`. For
`m ≥ 6` all four recurrences 28.4.5–28.4.8 agree with the generic one on the rows that meet the
support of `T`, so the trial-vector estimates of `DLMF.Mathieu.SmallQVector` apply. The cases
`m = 3, 4, 5` are in `DLMF.Mathieu.SmallQCeSe`.

## Main definitions

* `ceSeTrialVector`: the generic trial vector `T_j(m, q)`.
* `ceSeEigenvalueApprox`, `ceSeNormalizingFactor`: the eigenvalue approximation
  `m² + q²/(2(m²-1))` and the normalizing factor `1 - (m²+1)q²/(16(m²-1)²)`.
* `ceSeResidual`, `ceSeNormResidual`, `ceSeFinalResidual`: the residual quotients.

## Main results

* `mathieuCe_sub_isBigO_of_six_le`: DLMF 28.6.26 for `m ≥ 6`.
* `mathieuSe_sub_isBigO_of_six_le`: the `se` analogue of 28.6.26 for `m ≥ 6`.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-- The generic trial vector of DLMF 28.6.26: `T_0 = 1`, `T_{∓1} = ±q/(4(m∓1))`,
`T_{±2} = q²/(32(m±1)(m±2))`, `T_j = 0` for `|j| ≥ 3`. -/
def ceSeTrialVector (m q : ℂ) (j : ℤ) : ℂ :=
  if j = -2 then q ^ 2 / (32 * (m - 1) * (m - 2))
  else if j = -1 then q / (4 * (m - 1))
  else if j = 0 then 1
  else if j = 1 then -q / (4 * (m + 1))
  else if j = 2 then q ^ 2 / (32 * (m + 1) * (m + 2))
  else 0

/-- The eigenvalue approximation `m² + q²/(2(m²-1))`. -/
def ceSeEigenvalueApprox (m q : ℂ) : ℂ := m ^ 2 + q ^ 2 / (2 * (m ^ 2 - 1))

/-- The normalizing factor `1 - (m²+1)q²/(16(m²-1)²)`. -/
def ceSeNormalizingFactor (m q : ℂ) : ℂ := 1 - (m ^ 2 + 1) * q ^ 2 / (16 * (m ^ 2 - 1) ^ 2)

/-- The residual quotients of `ceSeTrialVector`: row `j` equals `q³ ceSeResidual m q j`. -/
def ceSeResidual (m q : ℂ) (j : ℤ) : ℂ :=
  if j = -3 then 1 / (32 * (m - 2) * (m - 1))
  else if j = -2 then -1 / (64 * (m - 2) * (m - 1) ^ 2 * (m + 1)) * q
  else if j = -1 then (m ^ 2 - 4 * m + 7) / (32 * (m - 2) * (m - 1) ^ 2 * (m + 1))
  else if j = 1 then (m ^ 2 + 4 * m + 7) / (32 * (m - 1) * (m + 1) ^ 2 * (m + 2))
  else if j = 2 then -1 / (64 * (m - 1) * (m + 1) ^ 2 * (m + 2)) * q
  else if j = 3 then 1 / (32 * (m + 1) * (m + 2))
  else 0

/-- The normalization residual quotient. -/
def ceSeNormResidual (m q : ℂ) : ℂ :=
  -(5 * m ^ 8 - 47 * m ^ 6 + 27 * m ^ 4 + 139 * m ^ 2 + 92) /
      (512 * (m - 2) ^ 2 * (m - 1) ^ 4 * (m + 1) ^ 4 * (m + 2) ^ 2) * q +
    (m ^ 2 + 1) * (m ^ 8 - 23 * m ^ 6 + 23 * m ^ 4 + 43 * m ^ 2 + 28) /
      (4096 * (m - 2) ^ 2 * (m - 1) ^ 6 * (m + 1) ^ 6 * (m + 2) ^ 2) * q ^ 3 +
    (m ^ 2 + 1) ^ 2 * (m ^ 4 + 13 * m ^ 2 + 4) /
      (131072 * (m - 2) ^ 2 * (m - 1) ^ 6 * (m + 1) ^ 6 * (m + 2) ^ 2) * q ^ 5

/-- The final residual quotient, in terms of `C₀ = cos mz`, `C_{±2} = cos(m±2)z`,
`C_{±4} = cos(m±4)z` (or the sines). -/
def ceSeFinalResidual (m q C0 Cp2 Cm2 Cp4 Cm4 : ℂ) : ℂ :=
  (m ^ 2 + 1) / (64 * (m - 1) ^ 2 * (m + 1) ^ 3) * Cp2 -
    (m ^ 2 + 1) / (64 * (m - 1) ^ 3 * (m + 1) ^ 2) * Cm2 -
    (m ^ 2 + 1) / (512 * (m - 1) ^ 2 * (m + 1) ^ 3 * (m + 2)) * Cp4 * q -
    (m ^ 2 + 1) / (512 * (m - 2) * (m - 1) ^ 3 * (m + 1) ^ 2) * Cm4 * q + 0 * C0

/-- The trial vector of 28.6.26 vanishes for `|j| ≥ 3`. -/
private lemma ceSeTrialVector_eq_zero_of_three_le_natAbs (m q : ℂ) {j : ℤ} (hj : 3 ≤ j.natAbs) : ceSeTrialVector m q j = 0 := by
  unfold ceSeTrialVector
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The residual quotients `ceSeResidual` vanish for `|j| ≥ 4`. -/
private lemma ceSeResidual_eq_zero_of_four_le_natAbs (m q : ℂ) {j : ℤ} (hj : 4 ≤ j.natAbs) : ceSeResidual m q j = 0 := by
  unfold ceSeResidual
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Row identity: `((m+2j)² - P) T_j + q (T_{j-1} + T_{j+1}) = q³ ceSeResidual m q j` with
`P = m² + q²/(2(m²-1))`. -/
private lemma trial_row {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) (j : ℤ) :
    ((m + 2 * (j : ℂ)) ^ 2 - ceSeEigenvalueApprox m q) * ceSeTrialVector m q j +
      q * (ceSeTrialVector m q (j - 1) + ceSeTrialVector m q (j + 1)) = q ^ 3 * ceSeResidual m q j := by
  have := hm.h1; have := hm.h2; have := hm.h1'; have := hm.h2'; have := hm.sq1
  by_cases hj : j.natAbs ≤ 3
  · have h1 : -3 ≤ j := by omega
    have h2 : j ≤ 3 := by omega
    interval_cases j <;> norm_num [ceSeTrialVector, ceSeResidual, ceSeEigenvalueApprox] <;> field_simp <;> ring
  · rw [ceSeTrialVector_eq_zero_of_three_le_natAbs m q (by omega), ceSeTrialVector_eq_zero_of_three_le_natAbs m q (by omega),
      ceSeTrialVector_eq_zero_of_three_le_natAbs m q (by omega), ceSeResidual_eq_zero_of_four_le_natAbs m q (by omega)]
    ring

/-- Each component of the trial vector `ceSeTrialVector` is continuous in real `q`. -/
private lemma continuous_ceSeTrialVector (m : ℂ) (j : ℤ) : Continuous fun q : ℝ => ceSeTrialVector m q j := by
  unfold ceSeTrialVector
  split_ifs <;> fun_prop

/-- Each residual quotient `ceSeResidual` is continuous in real `q`. -/
private lemma continuous_ceSeResidual (m : ℂ) (j : ℤ) : Continuous fun q : ℝ => ceSeResidual m q j := by
  unfold ceSeResidual
  split_ifs <;> fun_prop

/-- The residual rows of the trial vector `v_i = T_{i-n}` are `O(q³)` in a recurrence whose
diagonal agrees with `(m + 2(i - n))²` for `|i - n| ≤ 2`. -/
private lemma trial_residual_isBigO {D : ℝ → ℕ → ℂ} {β : ℂ} {n : ℕ} {m : ℂ} (hm : IsGenericOrder m) (hn : 2 ≤ n)
    (hβ : n = 2 → β = 1)
    (hD : ∀ q i, n ≤ i + 2 → i ≤ n + 2 → D q i = (m + 2 * ((i : ℂ) - n)) ^ 2) (i : ℕ) :
    (fun q : ℝ => recurrenceOperator (D q) β q (fun i => ceSeTrialVector m q ((i : ℤ) - n)) i -
      ceSeEigenvalueApprox m q * ceSeTrialVector m q ((i : ℤ) - n)) =O[𝓝 0] (fun q : ℝ => q ^ 3) := by
  refine isBigO_pow_of_eq_pow_mul (e := 3) le_rfl
    (s := fun q : ℝ => ceSeResidual m q ((i : ℤ) - n)) (fun q => ?_) (continuous_ceSeResidual m _)
  rw [← trial_row hm]
  have hdiag : D q i * ceSeTrialVector m q ((i : ℤ) - n) =
      (m + 2 * ((((i : ℤ) - n : ℤ)) : ℂ)) ^ 2 * ceSeTrialVector m q ((i : ℤ) - n) := by
    by_cases h : n ≤ i + 2 ∧ i ≤ n + 2
    · rw [hD q i h.1 h.2]; push_cast; ring
    · rw [ceSeTrialVector_eq_zero_of_three_le_natAbs m q (by omega)]; ring
  have hlo : recurrenceLower β (fun i => ceSeTrialVector m q ((i : ℤ) - n)) i = ceSeTrialVector m q ((i : ℤ) - n - 1) := by
    match i with
    | 0 => simp only [recurrenceLower]; rw [ceSeTrialVector_eq_zero_of_three_le_natAbs m q (by omega)]
    | 1 =>
      simp only [recurrenceLower]
      rcases eq_or_lt_of_le hn with h3 | h4
      · subst h3; rw [hβ rfl, one_mul]; congr 1
      · rw [ceSeTrialVector_eq_zero_of_three_le_natAbs m q (by omega), ceSeTrialVector_eq_zero_of_three_le_natAbs m q (by omega), mul_zero]
    | k + 2 => simp only [recurrenceLower]; congr 1; push_cast; ring
  simp only [recurrenceOperator, hdiag, hlo]
  rw [show (((i + 1 : ℕ) : ℤ) - n) = ((i : ℤ) - n) + 1 by push_cast; ring]
  ring

/-- A sum over `i < k + 5` of `f(i - (k+2)) h(i)`, with `f` supported in `|j| ≤ 2`,
reduces to its five middle terms. -/
private lemma sum_range_eq_five_middle_terms (k : ℕ) (f : ℤ → ℂ) (hf : ∀ j, 3 ≤ j.natAbs → f j = 0) (h : ℕ → ℂ) :
    ∑ i ∈ Finset.range (k + 2 + 3), f ((i : ℤ) - ((k + 2 : ℕ) : ℤ)) * h i =
      f (-2) * h k + f (-1) * h (k + 1) + f 0 * h (k + 2) + f 1 * h (k + 3) +
        f 2 * h (k + 4) := by
  rw [show k + 2 + 3 = k + 4 + 1 by ring]
  simp only [Finset.sum_range_succ]
  rw [Finset.sum_eq_zero fun i hi => by
    rw [hf _ (by simp at hi; omega), zero_mul]]
  have e : ∀ a : ℕ, ((k + a : ℕ) : ℤ) - ((k + 2 : ℕ) : ℤ) = (a : ℤ) - 2 := fun a => by
    push_cast; ring
  rw [show ((k : ℕ) : ℤ) - ((k + 2 : ℕ) : ℤ) = -2 by push_cast; ring, e 1, e 2, e 3, e 4]
  norm_num

/-- The normalization identity `c² ∑_j T_j² - 1 = q³ ceSeNormResidual m q`. -/
private lemma trial_normalization {m : ℂ} (hm : IsGenericOrder m) (q : ℂ) :
    ceSeNormalizingFactor m q ^ 2 * (ceSeTrialVector m q (-2) ^ 2 + ceSeTrialVector m q (-1) ^ 2 + ceSeTrialVector m q 0 ^ 2 +
      ceSeTrialVector m q 1 ^ 2 + ceSeTrialVector m q 2 ^ 2) - 1 = q ^ 3 * ceSeNormResidual m q := by
  have := hm.h1; have := hm.h2; have := hm.h1'; have := hm.h2'; have := hm.sq1
  simp only [ceSeTrialVector, ceSeNormalizingFactor, ceSeNormResidual]
  norm_num
  field_simp
  ring

/-- The normalized trial sum `c ∑_j T_j C_{2j}` differs from the 28.6.26 polynomial by
`q³ ceSeFinalResidual`. -/
private lemma trial_sum_sub_poly {m : ℂ} (hm : IsGenericOrder m) (q C0 Cp2 Cm2 Cp4 Cm4 : ℂ) :
    ceSeNormalizingFactor m q * (ceSeTrialVector m q (-2) * Cm4 + ceSeTrialVector m q (-1) * Cm2 + ceSeTrialVector m q 0 * C0 +
      ceSeTrialVector m q 1 * Cp2 + ceSeTrialVector m q 2 * Cp4) -
    (C0 - q / 4 * (Cp2 / (m + 1) - Cm2 / (m - 1)) +
      q ^ 2 / 32 * (Cp4 / ((m + 1) * (m + 2)) + Cm4 / ((m - 1) * (m - 2)) -
        2 * (m ^ 2 + 1) * C0 / (m ^ 2 - 1) ^ 2)) =
      q ^ 3 * ceSeFinalResidual m q C0 Cp2 Cm2 Cp4 Cm4 := by
  have := hm.h1; have := hm.h2; have := hm.h1'; have := hm.h2'; have := hm.sq1
  simp only [ceSeTrialVector, ceSeNormalizingFactor, ceSeFinalResidual]
  norm_num
  field_simp
  ring


/-- DLMF 28.6.26 for `m ≥ 6`. -/
theorem mathieuCe_sub_isBigO_of_six_le {m : ℕ} (hm : 6 ≤ m) (z : ℂ) :
    (fun q : ℝ => mathieuCe m z q - (Complex.cos (m * z) -
      q / 4 * (Complex.cos ((m + 2) * z) / (m + 1) - Complex.cos ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.cos ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.cos ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.cos (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    set M : ℂ := ((2 * (k + 2) : ℕ) : ℂ) with hM
    have hg : IsGenericOrder M := isGenericOrder_natCast (by omega)
    have h := mathieuCe_even_sub_trial_isBigO (k + 2) (N := k + 2 + 3) (K := 3) (by omega) le_rfl
      (by norm_num)
      (p := fun q => ceSeEigenvalueApprox M q) (v := fun q i => ceSeTrialVector M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)))
      (fun q i hi => ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ (by omega)) (fun q => by simp [ceSeTrialVector])
      (fun i _ => isBigO_one_of_continuous (continuous_ceSeTrialVector _ _))
      (fun i _ => trial_residual_isBigO hg (by omega) (fun h => absurd h (by omega))
        (fun q i _ _ => by rw [hM]; push_cast; ring) i)
      (c := fun q => ceSeNormalizingFactor M q)
      (by simpa [ceSeNormalizingFactor] using ((by unfold ceSeNormalizingFactor; fun_prop :
        Continuous fun q : ℝ => ceSeNormalizingFactor M q).tendsto 0))
      (isBigO_pow_of_eq_pow_mul (e := 3) le_rfl (s := fun q : ℝ => ceSeNormResidual M q) (fun q => by
        rw [Finset.sum_congr rfl fun i _ => mul_comm ((if i = 0 then (2 : ℂ) else 1)) _,
          sum_range_eq_five_middle_terms k (fun j => ceSeTrialVector M q j ^ 2) (fun j hj => by rw [ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ hj]; ring)
            (fun i => if i = 0 then (2 : ℂ) else 1)]
        simp only [show k ≠ 0 by omega, show k + 1 ≠ 0 by omega, show k + 2 ≠ 0 by omega,
          show k + 3 ≠ 0 by omega, show k + 4 ≠ 0 by omega, ↓reduceIte, mul_one]
        exact trial_normalization hg q) (by unfold ceSeNormResidual; fun_prop)) z
    have h2 : (fun q : ℝ => ceSeNormalizingFactor M q * ∑ i ∈ Finset.range (k + 2 + 3),
        ceSeTrialVector M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)) * Complex.cos (2 * (i : ℂ) * z) -
        (Complex.cos (M * z) -
      q / 4 * (Complex.cos ((M + 2) * z) / (M + 1) - Complex.cos ((M - 2) * z) / (M - 1)) +
      q ^ 2 / 32 * (Complex.cos ((M + 4) * z) / ((M + 1) * (M + 2)) +
        Complex.cos ((M - 4) * z) / ((M - 1) * (M - 2)) -
        2 * (M ^ 2 + 1) * Complex.cos (M * z) / (M ^ 2 - 1) ^ 2))) =O[𝓝 0]
        (fun q : ℝ => q ^ 3) := by
      refine isBigO_pow_of_eq_pow_mul (e := 3) le_rfl
        (s := fun q : ℝ => ceSeFinalResidual M q (Complex.cos (M * z)) (Complex.cos ((M + 2) * z))
          (Complex.cos ((M - 2) * z)) (Complex.cos ((M + 4) * z)) (Complex.cos ((M - 4) * z)))
        (fun q => ?_) (by unfold ceSeFinalResidual; fun_prop)
      rw [sum_range_eq_five_middle_terms k (ceSeTrialVector M q) (fun j hj => ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ hj)
          (fun i => Complex.cos (2 * (i : ℂ) * z))]
      rw [show Complex.cos (2 * ((k : ℕ) : ℂ) * z) = Complex.cos ((M - 4) * z)
        by rw [hM]; push_cast; ring_nf,
        show Complex.cos (2 * ((k + 1 : ℕ) : ℂ) * z) = Complex.cos ((M - 2) * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.cos (2 * ((k + 2 : ℕ) : ℂ) * z) = Complex.cos (M * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.cos (2 * ((k + 3 : ℕ) : ℂ) * z) = Complex.cos ((M + 2) * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.cos (2 * ((k + 4 : ℕ) : ℂ) * z) = Complex.cos ((M + 4) * z)
          by rw [hM]; push_cast; ring_nf]
      exact trial_sum_sub_poly hg q _ _ _ _ _
    exact (h.add h2).congr_left fun q => by ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    set M : ℂ := ((2 * (k + 2) + 1 : ℕ) : ℂ) with hM
    have hg : IsGenericOrder M := isGenericOrder_natCast (by omega)
    have h := mathieuCe_odd_sub_trial_isBigO (k + 2) (N := k + 2 + 3) (K := 3) (by omega) le_rfl (by norm_num)
      (p := fun q => ceSeEigenvalueApprox M q) (v := fun q i => ceSeTrialVector M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)))
      (fun q i hi => ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ (by omega)) (fun q => by simp [ceSeTrialVector])
      (fun i _ => isBigO_one_of_continuous (continuous_ceSeTrialVector _ _))
      (fun i _ => trial_residual_isBigO hg (by omega) (fun h => absurd h (by omega))
        (fun q i h1 _ => by
        simp only [show i ≠ 0 by omega, ↓reduceIte]; rw [hM]; push_cast; ring) i)
      (c := fun q => ceSeNormalizingFactor M q)
      (by simpa [ceSeNormalizingFactor] using ((by unfold ceSeNormalizingFactor; fun_prop :
        Continuous fun q : ℝ => ceSeNormalizingFactor M q).tendsto 0))
      (isBigO_pow_of_eq_pow_mul (e := 3) le_rfl (s := fun q : ℝ => ceSeNormResidual M q) (fun q => by
        rw [Finset.sum_congr rfl fun i _ => mul_comm (1 : ℂ) _,
          sum_range_eq_five_middle_terms k (fun j => ceSeTrialVector M q j ^ 2) (fun j hj => by rw [ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ hj]; ring)
            (fun _ => 1)]
        simp only [mul_one]
        exact trial_normalization hg q) (by unfold ceSeNormResidual; fun_prop)) z
    have h2 : (fun q : ℝ => ceSeNormalizingFactor M q * ∑ i ∈ Finset.range (k + 2 + 3),
        ceSeTrialVector M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)) * Complex.cos ((2 * (i : ℂ) + 1) * z) -
        (Complex.cos (M * z) -
      q / 4 * (Complex.cos ((M + 2) * z) / (M + 1) - Complex.cos ((M - 2) * z) / (M - 1)) +
      q ^ 2 / 32 * (Complex.cos ((M + 4) * z) / ((M + 1) * (M + 2)) +
        Complex.cos ((M - 4) * z) / ((M - 1) * (M - 2)) -
        2 * (M ^ 2 + 1) * Complex.cos (M * z) / (M ^ 2 - 1) ^ 2))) =O[𝓝 0]
        (fun q : ℝ => q ^ 3) := by
      refine isBigO_pow_of_eq_pow_mul (e := 3) le_rfl
        (s := fun q : ℝ => ceSeFinalResidual M q (Complex.cos (M * z)) (Complex.cos ((M + 2) * z))
          (Complex.cos ((M - 2) * z)) (Complex.cos ((M + 4) * z)) (Complex.cos ((M - 4) * z)))
        (fun q => ?_) (by unfold ceSeFinalResidual; fun_prop)
      rw [sum_range_eq_five_middle_terms k (ceSeTrialVector M q) (fun j hj => ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ hj)
          (fun i => Complex.cos ((2 * (i : ℂ) + 1) * z))]
      rw [show Complex.cos ((2 * ((k : ℕ) : ℂ) + 1) * z) = Complex.cos ((M - 4) * z)
        by rw [hM]; push_cast; ring_nf,
        show Complex.cos ((2 * ((k + 1 : ℕ) : ℂ) + 1) * z) = Complex.cos ((M - 2) * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.cos ((2 * ((k + 2 : ℕ) : ℂ) + 1) * z) = Complex.cos (M * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.cos ((2 * ((k + 3 : ℕ) : ℂ) + 1) * z) = Complex.cos ((M + 2) * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.cos ((2 * ((k + 4 : ℕ) : ℂ) + 1) * z) = Complex.cos ((M + 4) * z)
          by rw [hM]; push_cast; ring_nf]
      exact trial_sum_sub_poly hg q _ _ _ _ _
    exact (h.add h2).congr_left fun q => by ring

/-- The `se` analogue of DLMF 28.6.26 for `m ≥ 6`. -/
theorem mathieuSe_sub_isBigO_of_six_le {m : ℕ} (hm : 6 ≤ m) (z : ℂ) :
    (fun q : ℝ => mathieuSe m z q - (Complex.sin (m * z) -
      q / 4 * (Complex.sin ((m + 2) * z) / (m + 1) - Complex.sin ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.sin ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.sin ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.sin (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show 2 * (k + 3) = 2 * (k + 2) + 2 by ring]
    set M : ℂ := ((2 * (k + 2) + 2 : ℕ) : ℂ) with hM
    have hg : IsGenericOrder M := isGenericOrder_natCast (by omega)
    have h := mathieuSe_even_sub_trial_isBigO (k + 2) (N := k + 2 + 3) (K := 3) (by omega) le_rfl (by norm_num)
      (p := fun q => ceSeEigenvalueApprox M q) (v := fun q i => ceSeTrialVector M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)))
      (fun q i hi => ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ (by omega)) (fun q => by simp [ceSeTrialVector])
      (fun i _ => isBigO_one_of_continuous (continuous_ceSeTrialVector _ _))
      (fun i _ => trial_residual_isBigO hg (by omega) (fun _ => rfl)
        (fun q i _ _ => by rw [hM]; push_cast; ring) i)
      (c := fun q => ceSeNormalizingFactor M q)
      (by simpa [ceSeNormalizingFactor] using ((by unfold ceSeNormalizingFactor; fun_prop :
        Continuous fun q : ℝ => ceSeNormalizingFactor M q).tendsto 0))
      (isBigO_pow_of_eq_pow_mul (e := 3) le_rfl (s := fun q : ℝ => ceSeNormResidual M q) (fun q => by
        rw [Finset.sum_congr rfl fun i _ => mul_comm (1 : ℂ) _,
          sum_range_eq_five_middle_terms k (fun j => ceSeTrialVector M q j ^ 2) (fun j hj => by rw [ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ hj]; ring)
            (fun _ => 1)]
        simp only [mul_one]
        exact trial_normalization hg q) (by unfold ceSeNormResidual; fun_prop)) z
    have h2 : (fun q : ℝ => ceSeNormalizingFactor M q * ∑ i ∈ Finset.range (k + 2 + 3),
        ceSeTrialVector M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)) * Complex.sin ((2 * (i : ℂ) + 2) * z) -
        (Complex.sin (M * z) -
      q / 4 * (Complex.sin ((M + 2) * z) / (M + 1) - Complex.sin ((M - 2) * z) / (M - 1)) +
      q ^ 2 / 32 * (Complex.sin ((M + 4) * z) / ((M + 1) * (M + 2)) +
        Complex.sin ((M - 4) * z) / ((M - 1) * (M - 2)) -
        2 * (M ^ 2 + 1) * Complex.sin (M * z) / (M ^ 2 - 1) ^ 2))) =O[𝓝 0]
        (fun q : ℝ => q ^ 3) := by
      refine isBigO_pow_of_eq_pow_mul (e := 3) le_rfl
        (s := fun q : ℝ => ceSeFinalResidual M q (Complex.sin (M * z)) (Complex.sin ((M + 2) * z))
          (Complex.sin ((M - 2) * z)) (Complex.sin ((M + 4) * z)) (Complex.sin ((M - 4) * z)))
        (fun q => ?_) (by unfold ceSeFinalResidual; fun_prop)
      rw [sum_range_eq_five_middle_terms k (ceSeTrialVector M q) (fun j hj => ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ hj)
          (fun i => Complex.sin ((2 * (i : ℂ) + 2) * z))]
      rw [show Complex.sin ((2 * ((k : ℕ) : ℂ) + 2) * z) = Complex.sin ((M - 4) * z)
        by rw [hM]; push_cast; ring_nf,
        show Complex.sin ((2 * ((k + 1 : ℕ) : ℂ) + 2) * z) = Complex.sin ((M - 2) * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.sin ((2 * ((k + 2 : ℕ) : ℂ) + 2) * z) = Complex.sin (M * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.sin ((2 * ((k + 3 : ℕ) : ℂ) + 2) * z) = Complex.sin ((M + 2) * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.sin ((2 * ((k + 4 : ℕ) : ℂ) + 2) * z) = Complex.sin ((M + 4) * z)
          by rw [hM]; push_cast; ring_nf]
      exact trial_sum_sub_poly hg q _ _ _ _ _
    exact (h.add h2).congr_left fun q => by ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    set M : ℂ := ((2 * (k + 2) + 1 : ℕ) : ℂ) with hM
    have hg : IsGenericOrder M := isGenericOrder_natCast (by omega)
    have h := mathieuSe_odd_sub_trial_isBigO (k + 2) (N := k + 2 + 3) (K := 3) (by omega) le_rfl (by norm_num)
      (p := fun q => ceSeEigenvalueApprox M q) (v := fun q i => ceSeTrialVector M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)))
      (fun q i hi => ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ (by omega)) (fun q => by simp [ceSeTrialVector])
      (fun i _ => isBigO_one_of_continuous (continuous_ceSeTrialVector _ _))
      (fun i _ => trial_residual_isBigO hg (by omega) (fun h => absurd h (by omega))
        (fun q i h1 _ => by
        simp only [show i ≠ 0 by omega, ↓reduceIte]; rw [hM]; push_cast; ring) i)
      (c := fun q => ceSeNormalizingFactor M q)
      (by simpa [ceSeNormalizingFactor] using ((by unfold ceSeNormalizingFactor; fun_prop :
        Continuous fun q : ℝ => ceSeNormalizingFactor M q).tendsto 0))
      (isBigO_pow_of_eq_pow_mul (e := 3) le_rfl (s := fun q : ℝ => ceSeNormResidual M q) (fun q => by
        rw [Finset.sum_congr rfl fun i _ => mul_comm (1 : ℂ) _,
          sum_range_eq_five_middle_terms k (fun j => ceSeTrialVector M q j ^ 2) (fun j hj => by rw [ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ hj]; ring)
            (fun _ => 1)]
        simp only [mul_one]
        exact trial_normalization hg q) (by unfold ceSeNormResidual; fun_prop)) z
    have h2 : (fun q : ℝ => ceSeNormalizingFactor M q * ∑ i ∈ Finset.range (k + 2 + 3),
        ceSeTrialVector M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)) * Complex.sin ((2 * (i : ℂ) + 1) * z) -
        (Complex.sin (M * z) -
      q / 4 * (Complex.sin ((M + 2) * z) / (M + 1) - Complex.sin ((M - 2) * z) / (M - 1)) +
      q ^ 2 / 32 * (Complex.sin ((M + 4) * z) / ((M + 1) * (M + 2)) +
        Complex.sin ((M - 4) * z) / ((M - 1) * (M - 2)) -
        2 * (M ^ 2 + 1) * Complex.sin (M * z) / (M ^ 2 - 1) ^ 2))) =O[𝓝 0]
        (fun q : ℝ => q ^ 3) := by
      refine isBigO_pow_of_eq_pow_mul (e := 3) le_rfl
        (s := fun q : ℝ => ceSeFinalResidual M q (Complex.sin (M * z)) (Complex.sin ((M + 2) * z))
          (Complex.sin ((M - 2) * z)) (Complex.sin ((M + 4) * z)) (Complex.sin ((M - 4) * z)))
        (fun q => ?_) (by unfold ceSeFinalResidual; fun_prop)
      rw [sum_range_eq_five_middle_terms k (ceSeTrialVector M q) (fun j hj => ceSeTrialVector_eq_zero_of_three_le_natAbs _ _ hj)
          (fun i => Complex.sin ((2 * (i : ℂ) + 1) * z))]
      rw [show Complex.sin ((2 * ((k : ℕ) : ℂ) + 1) * z) = Complex.sin ((M - 4) * z)
        by rw [hM]; push_cast; ring_nf,
        show Complex.sin ((2 * ((k + 1 : ℕ) : ℂ) + 1) * z) = Complex.sin ((M - 2) * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.sin ((2 * ((k + 2 : ℕ) : ℂ) + 1) * z) = Complex.sin (M * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.sin ((2 * ((k + 3 : ℕ) : ℂ) + 1) * z) = Complex.sin ((M + 2) * z)
          by rw [hM]; push_cast; ring_nf,
        show Complex.sin ((2 * ((k + 4 : ℕ) : ℂ) + 1) * z) = Complex.sin ((M + 4) * z)
          by rw [hM]; push_cast; ring_nf]
      exact trial_sum_sub_poly hg q _ _ _ _ _
    exact (h.add h2).congr_left fun q => by ring

end DLMF.Mathieu
