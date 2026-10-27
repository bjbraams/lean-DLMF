/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.P3qVector
public import DLMF.Mathieu.P3qGeneral

/-!
# The expansion DLMF 28.6.26 of `ce_m`, `se_m` for `m ≥ 6`

A trial vector `T_j(m, q)` (`p3qHT`, `|j| ≤ 2`) rational in `m`, with every row of the generic
recurrence `((m + 2j)² - P) T_j + q (T_{j-1} + T_{j+1})` equal to `q³ p3qHS m q j`
(`p3q_h_row`). For `m ≥ 6` all four recurrences 28.4.5–28.4.8 agree with the generic one on
the rows that meet the support of `T`, so `p3q_expand_AE`, `p3q_expand_AO`, `p3q_expand_BO`,
`p3q_expand_BE` give DLMF 28.6.26 and its `se` analogue with remainder `O(q³)`
(`p3q_ce_ge6`, `p3q_se_ge6`). The cases `m = 3, 4, 5` are in `DLMF.Mathieu.P3qCeSe`.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-- The generic trial vector of DLMF 28.6.26: `T_0 = 1`, `T_{∓1} = ±q/(4(m∓1))`,
`T_{±2} = q²/(32(m±1)(m±2))`, `T_j = 0` for `|j| ≥ 3`. -/
def p3qHT (m q : ℂ) (j : ℤ) : ℂ :=
  if j = -2 then q ^ 2 / (32 * (m - 1) * (m - 2))
  else if j = -1 then q / (4 * (m - 1))
  else if j = 0 then 1
  else if j = 1 then -q / (4 * (m + 1))
  else if j = 2 then q ^ 2 / (32 * (m + 1) * (m + 2))
  else 0

/-- The eigenvalue approximation `m² + q²/(2(m²-1))`. -/
def p3qHP (m q : ℂ) : ℂ := m ^ 2 + q ^ 2 / (2 * (m ^ 2 - 1))

/-- The normalizing factor `1 - (m²+1)q²/(16(m²-1)²)`. -/
def p3qHc (m q : ℂ) : ℂ := 1 - (m ^ 2 + 1) * q ^ 2 / (16 * (m ^ 2 - 1) ^ 2)

/-- The residual quotients of `p3qHT`: row `j` equals `q³ p3qHS m q j`. -/
def p3qHS (m q : ℂ) (j : ℤ) : ℂ :=
  if j = -3 then 1 / (32 * (m - 2) * (m - 1))
  else if j = -2 then -1 / (64 * (m - 2) * (m - 1) ^ 2 * (m + 1)) * q
  else if j = -1 then (m ^ 2 - 4 * m + 7) / (32 * (m - 2) * (m - 1) ^ 2 * (m + 1))
  else if j = 1 then (m ^ 2 + 4 * m + 7) / (32 * (m - 1) * (m + 1) ^ 2 * (m + 2))
  else if j = 2 then -1 / (64 * (m - 1) * (m + 1) ^ 2 * (m + 2)) * q
  else if j = 3 then 1 / (32 * (m + 1) * (m + 2))
  else 0

/-- The normalization residual quotient. -/
def p3qHN (m q : ℂ) : ℂ :=
  -(5 * m ^ 8 - 47 * m ^ 6 + 27 * m ^ 4 + 139 * m ^ 2 + 92) /
      (512 * (m - 2) ^ 2 * (m - 1) ^ 4 * (m + 1) ^ 4 * (m + 2) ^ 2) * q +
    (m ^ 2 + 1) * (m ^ 8 - 23 * m ^ 6 + 23 * m ^ 4 + 43 * m ^ 2 + 28) /
      (4096 * (m - 2) ^ 2 * (m - 1) ^ 6 * (m + 1) ^ 6 * (m + 2) ^ 2) * q ^ 3 +
    (m ^ 2 + 1) ^ 2 * (m ^ 4 + 13 * m ^ 2 + 4) /
      (131072 * (m - 2) ^ 2 * (m - 1) ^ 6 * (m + 1) ^ 6 * (m + 2) ^ 2) * q ^ 5

/-- The final residual quotient, in terms of `C₀ = cos mz`, `C_{±2} = cos(m±2)z`,
`C_{±4} = cos(m±4)z` (or the sines). -/
def p3qHF (m q C0 Cp2 Cm2 Cp4 Cm4 : ℂ) : ℂ :=
  (m ^ 2 + 1) / (64 * (m - 1) ^ 2 * (m + 1) ^ 3) * Cp2 -
    (m ^ 2 + 1) / (64 * (m - 1) ^ 3 * (m + 1) ^ 2) * Cm2 -
    (m ^ 2 + 1) / (512 * (m - 1) ^ 2 * (m + 1) ^ 3 * (m + 2)) * Cp4 * q -
    (m ^ 2 + 1) / (512 * (m - 2) * (m - 1) ^ 3 * (m + 1) ^ 2) * Cm4 * q + 0 * C0

lemma p3qHT_eq_zero (m q : ℂ) {j : ℤ} (hj : 3 ≤ j.natAbs) : p3qHT m q j = 0 := by
  unfold p3qHT
  split_ifs <;> first | rfl | (exfalso; omega)

lemma p3qHS_eq_zero (m q : ℂ) {j : ℤ} (hj : 4 ≤ j.natAbs) : p3qHS m q j = 0 := by
  unfold p3qHS
  split_ifs <;> first | rfl | (exfalso; omega)

lemma p3q_h_row {m : ℂ} (hm : p3qGood m) (q : ℂ) (j : ℤ) :
    ((m + 2 * (j : ℂ)) ^ 2 - p3qHP m q) * p3qHT m q j +
      q * (p3qHT m q (j - 1) + p3qHT m q (j + 1)) = q ^ 3 * p3qHS m q j := by
  have := hm.h1; have := hm.h2; have := hm.h1'; have := hm.h2'; have := hm.sq1
  by_cases hj : j.natAbs ≤ 3
  · have h1 : -3 ≤ j := by omega
    have h2 : j ≤ 3 := by omega
    interval_cases j <;> norm_num [p3qHT, p3qHS, p3qHP] <;> field_simp <;> ring
  · rw [p3qHT_eq_zero m q (by omega), p3qHT_eq_zero m q (by omega),
      p3qHT_eq_zero m q (by omega), p3qHS_eq_zero m q (by omega)]
    ring

lemma p3qHT_continuous (m : ℂ) (j : ℤ) : Continuous fun q : ℝ => p3qHT m q j := by
  unfold p3qHT
  split_ifs <;> fun_prop

lemma p3qHS_continuous (m : ℂ) (j : ℤ) : Continuous fun q : ℝ => p3qHS m q j := by
  unfold p3qHS
  split_ifs <;> fun_prop

lemma p3q_h_hr {D : ℝ → ℕ → ℂ} {β : ℂ} {n : ℕ} {m : ℂ} (hm : p3qGood m) (hn : 2 ≤ n)
    (hβ : n = 2 → β = 1)
    (hD : ∀ q i, n ≤ i + 2 → i ≤ n + 2 → D q i = (m + 2 * ((i : ℂ) - n)) ^ 2) (i : ℕ) :
    (fun q : ℝ => p3qL (D q) β q (fun i => p3qHT m q ((i : ℤ) - n)) i -
      p3qHP m q * p3qHT m q ((i : ℤ) - n)) =O[𝓝 0] (fun q : ℝ => q ^ 3) := by
  refine p3q_isBigO_of_eq (e := 3) le_rfl
    (s := fun q : ℝ => p3qHS m q ((i : ℤ) - n)) (fun q => ?_) (p3qHS_continuous m _)
  rw [← p3q_h_row hm]
  have hdiag : D q i * p3qHT m q ((i : ℤ) - n) =
      (m + 2 * ((((i : ℤ) - n : ℤ)) : ℂ)) ^ 2 * p3qHT m q ((i : ℤ) - n) := by
    by_cases h : n ≤ i + 2 ∧ i ≤ n + 2
    · rw [hD q i h.1 h.2]; push_cast; ring
    · rw [p3qHT_eq_zero m q (by omega)]; ring
  have hlo : p3qLo β (fun i => p3qHT m q ((i : ℤ) - n)) i = p3qHT m q ((i : ℤ) - n - 1) := by
    match i with
    | 0 => simp only [p3qLo]; rw [p3qHT_eq_zero m q (by omega)]
    | 1 =>
      simp only [p3qLo]
      rcases eq_or_lt_of_le hn with h3 | h4
      · subst h3; rw [hβ rfl, one_mul]; congr 1
      · rw [p3qHT_eq_zero m q (by omega), p3qHT_eq_zero m q (by omega), mul_zero]
    | k + 2 => simp only [p3qLo]; congr 1; push_cast; ring
  simp only [p3qL, hdiag, hlo]
  rw [show (((i + 1 : ℕ) : ℤ) - n) = ((i : ℤ) - n) + 1 by push_cast; ring]
  ring

lemma p3q_h_sum (k : ℕ) (f : ℤ → ℂ) (hf : ∀ j, 3 ≤ j.natAbs → f j = 0) (h : ℕ → ℂ) :
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

lemma p3q_h_norm {m : ℂ} (hm : p3qGood m) (q : ℂ) :
    p3qHc m q ^ 2 * (p3qHT m q (-2) ^ 2 + p3qHT m q (-1) ^ 2 + p3qHT m q 0 ^ 2 +
      p3qHT m q 1 ^ 2 + p3qHT m q 2 ^ 2) - 1 = q ^ 3 * p3qHN m q := by
  have := hm.h1; have := hm.h2; have := hm.h1'; have := hm.h2'; have := hm.sq1
  simp only [p3qHT, p3qHc, p3qHN]
  norm_num
  field_simp
  ring

lemma p3q_h_final {m : ℂ} (hm : p3qGood m) (q C0 Cp2 Cm2 Cp4 Cm4 : ℂ) :
    p3qHc m q * (p3qHT m q (-2) * Cm4 + p3qHT m q (-1) * Cm2 + p3qHT m q 0 * C0 +
      p3qHT m q 1 * Cp2 + p3qHT m q 2 * Cp4) -
    (C0 - q / 4 * (Cp2 / (m + 1) - Cm2 / (m - 1)) +
      q ^ 2 / 32 * (Cp4 / ((m + 1) * (m + 2)) + Cm4 / ((m - 1) * (m - 2)) -
        2 * (m ^ 2 + 1) * C0 / (m ^ 2 - 1) ^ 2)) =
      q ^ 3 * p3qHF m q C0 Cp2 Cm2 Cp4 Cm4 := by
  have := hm.h1; have := hm.h2; have := hm.h1'; have := hm.h2'; have := hm.sq1
  simp only [p3qHT, p3qHc, p3qHF]
  norm_num
  field_simp
  ring


/-- DLMF 28.6.26 for `m ≥ 6`. -/
theorem p3q_ce_ge6 {m : ℕ} (hm : 6 ≤ m) (z : ℂ) :
    (fun q : ℝ => mathieuCe m z q - (Complex.cos (m * z) -
      q / 4 * (Complex.cos ((m + 2) * z) / (m + 1) - Complex.cos ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.cos ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.cos ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.cos (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    set M : ℂ := ((2 * (k + 2) : ℕ) : ℂ) with hM
    have hg : p3qGood M := p3qGood_natCast (by omega)
    have h := p3q_expand_AE (k + 2) (by omega) (N := k + 2 + 3) (K := 3) (by omega) le_rfl
      (by norm_num)
      (p := fun q => p3qHP M q) (v := fun q i => p3qHT M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)))
      (fun q i hi => p3qHT_eq_zero _ _ (by omega)) (fun q => by simp [p3qHT])
      (fun i _ => p3q_cont_isBigO_one (p3qHT_continuous _ _))
      (fun i _ => p3q_h_hr hg (by omega) (fun h => absurd h (by omega))
        (fun q i _ _ => by rw [hM]; push_cast; ring) i)
      (c := fun q => p3qHc M q)
      (by simpa [p3qHc] using ((by unfold p3qHc; fun_prop :
        Continuous fun q : ℝ => p3qHc M q).tendsto 0))
      (p3q_isBigO_of_eq (e := 3) le_rfl (s := fun q : ℝ => p3qHN M q) (fun q => by
        rw [Finset.sum_congr rfl fun i _ => mul_comm ((if i = 0 then (2 : ℂ) else 1)) _,
          p3q_h_sum k (fun j => p3qHT M q j ^ 2) (fun j hj => by rw [p3qHT_eq_zero _ _ hj]; ring)
            (fun i => if i = 0 then (2 : ℂ) else 1)]
        simp only [show k ≠ 0 by omega, show k + 1 ≠ 0 by omega, show k + 2 ≠ 0 by omega,
          show k + 3 ≠ 0 by omega, show k + 4 ≠ 0 by omega, ↓reduceIte, mul_one]
        exact p3q_h_norm hg q) (by unfold p3qHN; fun_prop)) z
    have h2 : (fun q : ℝ => p3qHc M q * ∑ i ∈ Finset.range (k + 2 + 3),
        p3qHT M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)) * Complex.cos (2 * (i : ℂ) * z) -
        (Complex.cos (M * z) -
      q / 4 * (Complex.cos ((M + 2) * z) / (M + 1) - Complex.cos ((M - 2) * z) / (M - 1)) +
      q ^ 2 / 32 * (Complex.cos ((M + 4) * z) / ((M + 1) * (M + 2)) +
        Complex.cos ((M - 4) * z) / ((M - 1) * (M - 2)) -
        2 * (M ^ 2 + 1) * Complex.cos (M * z) / (M ^ 2 - 1) ^ 2))) =O[𝓝 0]
        (fun q : ℝ => q ^ 3) := by
      refine p3q_isBigO_of_eq (e := 3) le_rfl
        (s := fun q : ℝ => p3qHF M q (Complex.cos (M * z)) (Complex.cos ((M + 2) * z))
          (Complex.cos ((M - 2) * z)) (Complex.cos ((M + 4) * z)) (Complex.cos ((M - 4) * z)))
        (fun q => ?_) (by unfold p3qHF; fun_prop)
      rw [p3q_h_sum k (p3qHT M q) (fun j hj => p3qHT_eq_zero _ _ hj)
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
      exact p3q_h_final hg q _ _ _ _ _
    exact (h.add h2).congr_left fun q => by ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    set M : ℂ := ((2 * (k + 2) + 1 : ℕ) : ℂ) with hM
    have hg : p3qGood M := p3qGood_natCast (by omega)
    have h := p3q_expand_AO (k + 2) (N := k + 2 + 3) (K := 3) (by omega) le_rfl (by norm_num)
      (p := fun q => p3qHP M q) (v := fun q i => p3qHT M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)))
      (fun q i hi => p3qHT_eq_zero _ _ (by omega)) (fun q => by simp [p3qHT])
      (fun i _ => p3q_cont_isBigO_one (p3qHT_continuous _ _))
      (fun i _ => p3q_h_hr hg (by omega) (fun h => absurd h (by omega))
        (fun q i h1 _ => by
        simp only [show i ≠ 0 by omega, ↓reduceIte]; rw [hM]; push_cast; ring) i)
      (c := fun q => p3qHc M q)
      (by simpa [p3qHc] using ((by unfold p3qHc; fun_prop :
        Continuous fun q : ℝ => p3qHc M q).tendsto 0))
      (p3q_isBigO_of_eq (e := 3) le_rfl (s := fun q : ℝ => p3qHN M q) (fun q => by
        rw [Finset.sum_congr rfl fun i _ => mul_comm (1 : ℂ) _,
          p3q_h_sum k (fun j => p3qHT M q j ^ 2) (fun j hj => by rw [p3qHT_eq_zero _ _ hj]; ring)
            (fun _ => 1)]
        simp only [mul_one]
        exact p3q_h_norm hg q) (by unfold p3qHN; fun_prop)) z
    have h2 : (fun q : ℝ => p3qHc M q * ∑ i ∈ Finset.range (k + 2 + 3),
        p3qHT M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)) * Complex.cos ((2 * (i : ℂ) + 1) * z) -
        (Complex.cos (M * z) -
      q / 4 * (Complex.cos ((M + 2) * z) / (M + 1) - Complex.cos ((M - 2) * z) / (M - 1)) +
      q ^ 2 / 32 * (Complex.cos ((M + 4) * z) / ((M + 1) * (M + 2)) +
        Complex.cos ((M - 4) * z) / ((M - 1) * (M - 2)) -
        2 * (M ^ 2 + 1) * Complex.cos (M * z) / (M ^ 2 - 1) ^ 2))) =O[𝓝 0]
        (fun q : ℝ => q ^ 3) := by
      refine p3q_isBigO_of_eq (e := 3) le_rfl
        (s := fun q : ℝ => p3qHF M q (Complex.cos (M * z)) (Complex.cos ((M + 2) * z))
          (Complex.cos ((M - 2) * z)) (Complex.cos ((M + 4) * z)) (Complex.cos ((M - 4) * z)))
        (fun q => ?_) (by unfold p3qHF; fun_prop)
      rw [p3q_h_sum k (p3qHT M q) (fun j hj => p3qHT_eq_zero _ _ hj)
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
      exact p3q_h_final hg q _ _ _ _ _
    exact (h.add h2).congr_left fun q => by ring

/-- The `se` analogue of DLMF 28.6.26 for `m ≥ 6`. -/
theorem p3q_se_ge6 {m : ℕ} (hm : 6 ≤ m) (z : ℂ) :
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
    have hg : p3qGood M := p3qGood_natCast (by omega)
    have h := p3q_expand_BE (k + 2) (N := k + 2 + 3) (K := 3) (by omega) le_rfl (by norm_num)
      (p := fun q => p3qHP M q) (v := fun q i => p3qHT M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)))
      (fun q i hi => p3qHT_eq_zero _ _ (by omega)) (fun q => by simp [p3qHT])
      (fun i _ => p3q_cont_isBigO_one (p3qHT_continuous _ _))
      (fun i _ => p3q_h_hr hg (by omega) (fun _ => rfl)
        (fun q i _ _ => by rw [hM]; push_cast; ring) i)
      (c := fun q => p3qHc M q)
      (by simpa [p3qHc] using ((by unfold p3qHc; fun_prop :
        Continuous fun q : ℝ => p3qHc M q).tendsto 0))
      (p3q_isBigO_of_eq (e := 3) le_rfl (s := fun q : ℝ => p3qHN M q) (fun q => by
        rw [Finset.sum_congr rfl fun i _ => mul_comm (1 : ℂ) _,
          p3q_h_sum k (fun j => p3qHT M q j ^ 2) (fun j hj => by rw [p3qHT_eq_zero _ _ hj]; ring)
            (fun _ => 1)]
        simp only [mul_one]
        exact p3q_h_norm hg q) (by unfold p3qHN; fun_prop)) z
    have h2 : (fun q : ℝ => p3qHc M q * ∑ i ∈ Finset.range (k + 2 + 3),
        p3qHT M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)) * Complex.sin ((2 * (i : ℂ) + 2) * z) -
        (Complex.sin (M * z) -
      q / 4 * (Complex.sin ((M + 2) * z) / (M + 1) - Complex.sin ((M - 2) * z) / (M - 1)) +
      q ^ 2 / 32 * (Complex.sin ((M + 4) * z) / ((M + 1) * (M + 2)) +
        Complex.sin ((M - 4) * z) / ((M - 1) * (M - 2)) -
        2 * (M ^ 2 + 1) * Complex.sin (M * z) / (M ^ 2 - 1) ^ 2))) =O[𝓝 0]
        (fun q : ℝ => q ^ 3) := by
      refine p3q_isBigO_of_eq (e := 3) le_rfl
        (s := fun q : ℝ => p3qHF M q (Complex.sin (M * z)) (Complex.sin ((M + 2) * z))
          (Complex.sin ((M - 2) * z)) (Complex.sin ((M + 4) * z)) (Complex.sin ((M - 4) * z)))
        (fun q => ?_) (by unfold p3qHF; fun_prop)
      rw [p3q_h_sum k (p3qHT M q) (fun j hj => p3qHT_eq_zero _ _ hj)
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
      exact p3q_h_final hg q _ _ _ _ _
    exact (h.add h2).congr_left fun q => by ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    set M : ℂ := ((2 * (k + 2) + 1 : ℕ) : ℂ) with hM
    have hg : p3qGood M := p3qGood_natCast (by omega)
    have h := p3q_expand_BO (k + 2) (N := k + 2 + 3) (K := 3) (by omega) le_rfl (by norm_num)
      (p := fun q => p3qHP M q) (v := fun q i => p3qHT M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)))
      (fun q i hi => p3qHT_eq_zero _ _ (by omega)) (fun q => by simp [p3qHT])
      (fun i _ => p3q_cont_isBigO_one (p3qHT_continuous _ _))
      (fun i _ => p3q_h_hr hg (by omega) (fun h => absurd h (by omega))
        (fun q i h1 _ => by
        simp only [show i ≠ 0 by omega, ↓reduceIte]; rw [hM]; push_cast; ring) i)
      (c := fun q => p3qHc M q)
      (by simpa [p3qHc] using ((by unfold p3qHc; fun_prop :
        Continuous fun q : ℝ => p3qHc M q).tendsto 0))
      (p3q_isBigO_of_eq (e := 3) le_rfl (s := fun q : ℝ => p3qHN M q) (fun q => by
        rw [Finset.sum_congr rfl fun i _ => mul_comm (1 : ℂ) _,
          p3q_h_sum k (fun j => p3qHT M q j ^ 2) (fun j hj => by rw [p3qHT_eq_zero _ _ hj]; ring)
            (fun _ => 1)]
        simp only [mul_one]
        exact p3q_h_norm hg q) (by unfold p3qHN; fun_prop)) z
    have h2 : (fun q : ℝ => p3qHc M q * ∑ i ∈ Finset.range (k + 2 + 3),
        p3qHT M q ((i : ℤ) - ((k + 2 : ℕ) : ℤ)) * Complex.sin ((2 * (i : ℂ) + 1) * z) -
        (Complex.sin (M * z) -
      q / 4 * (Complex.sin ((M + 2) * z) / (M + 1) - Complex.sin ((M - 2) * z) / (M - 1)) +
      q ^ 2 / 32 * (Complex.sin ((M + 4) * z) / ((M + 1) * (M + 2)) +
        Complex.sin ((M - 4) * z) / ((M - 1) * (M - 2)) -
        2 * (M ^ 2 + 1) * Complex.sin (M * z) / (M ^ 2 - 1) ^ 2))) =O[𝓝 0]
        (fun q : ℝ => q ^ 3) := by
      refine p3q_isBigO_of_eq (e := 3) le_rfl
        (s := fun q : ℝ => p3qHF M q (Complex.sin (M * z)) (Complex.sin ((M + 2) * z))
          (Complex.sin ((M - 2) * z)) (Complex.sin ((M + 4) * z)) (Complex.sin ((M - 4) * z)))
        (fun q => ?_) (by unfold p3qHF; fun_prop)
      rw [p3q_h_sum k (p3qHT M q) (fun j hj => p3qHT_eq_zero _ _ hj)
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
      exact p3q_h_final hg q _ _ _ _ _
    exact (h.add h2).congr_left fun q => by ring

end DLMF.Mathieu
