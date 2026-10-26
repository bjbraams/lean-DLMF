/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Stirling
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Bell numbers (DLMF §26.7)

DLMF's Bell number `B(n)` (the number of partitions of `{1, …, n}`) is Mathlib's `Nat.bell n`,
defined there by the recurrence 26.7.6 (`Nat.bell_succ`); no new definition is made. The
counting statement (Mathlib's TODO) is acquired here as `card_finpartition_eq_bell`.

**Source corrections (implicit conditions).** 26.7.3 (`B(n) = ∑_{k=1}^m kⁿ/k! ∑_{j=0}^{m-k}
(-1)^j/j!`, `m ≥ n`) and the first form of 26.7.4 (Dobiński, `B(n) = e⁻¹ ∑_{k=1}^∞ kⁿ/k!`)
fail for `n = 0` (e.g. `m = 2` gives `1/2`, Dobiński gives `1 - e⁻¹`): the omitted `k = 0`
term `0⁰/0! = 1` matters only there. Both are acquired for `n ≥ 1`, together with the `k = 0`
forms valid for all `n`. The floor form of 26.7.4 holds for all `n ≥ 0`.
-/

@[expose] public section

open Finset Filter Topology Asymptotics

noncomputable section

namespace DLMF.Combinatorics

/-- DLMF 26.7.6: `B(n+1) = ∑_{k=0}^{n} C(n, k) B(k)` (Mathlib's `Nat.bell_succ` sums
`C(n, k) B(n-k)`). -/
@[dlmf 26.7.E6]
theorem bell_succ_eq_sum (n : ℕ) :
    Nat.bell (n + 1) = ∑ k ∈ range (n + 1), n.choose k * Nat.bell k := by
  rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic, ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm hk, Nat.sub_sub_self hk]

/-- DLMF 26.7.2: `B(n) = ∑_{k=0}^{n} S(n, k)`. -/
@[dlmf 26.7.E2]
theorem bell_eq_sum_stirlingSecond (n : ℕ) :
    Nat.bell n = ∑ k ∈ range (n + 1), Nat.stirlingSecond n k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp
    · rw [bell_succ_eq_sum, sum_range_succ' (fun k => Nat.stirlingSecond (n + 1) k) (n + 1),
        Nat.stirlingSecond_succ_zero, add_zero]
      simp_rw [c26a_stirlingSecond_succ_succ_eq_sum_range]
      rw [sum_comm]
      refine sum_congr rfl fun j hj => ?_
      have hj : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
      rw [ih j (by omega), mul_sum]
      apply sum_subset_zero_on_sdiff
      · intro k hk; simp only [mem_range] at hk ⊢; omega
      · intro k hk
        simp only [Finset.mem_sdiff, mem_range, not_lt] at hk
        rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]; simp
      · intro k _; rfl

/-- DLMF §26.7(i): `B(n)` is the number of partitions of `{1, …, n}` (Mathlib `Nat.bell`;
for `n = 0` the empty set has exactly one partition). -/
@[dlmf 26.7.i]
theorem card_finpartition_eq_bell (n : ℕ) :
    Fintype.card (Finpartition (univ : Finset (Fin n))) = Nat.bell n := by
  rw [bell_eq_sum_stirlingSecond, ← card_univ,
    card_eq_sum_card_fiberwise (f := fun P : Finpartition (univ : Finset (Fin n)) => #P.parts)
      (t := range (n + 1))]
  · exact sum_congr rfl fun k _ => card_finpartition_eq_stirlingSecond n k
  · intro P _
    simpa [Nat.lt_succ_iff] using P.card_parts_le_card

/-- DLMF 26.7.3, `k = 0` form valid for all `n` (`m ≥ n`). -/
theorem q26a_bell_eq_sum_range_mul_sum {n m : ℕ} (hm : n ≤ m) :
    (Nat.bell n : ℚ) = ∑ k ∈ range (m + 1), (k : ℚ) ^ n / k.factorial *
      ∑ j ∈ range (m - k + 1), (-1 : ℚ) ^ j / j.factorial := by
  have h1 : (Nat.bell n : ℚ) = ∑ k ∈ range (m + 1), (Nat.stirlingSecond n k : ℚ) := by
    rw [bell_eq_sum_stirlingSecond]; push_cast
    apply sum_subset_zero_on_sdiff
    · intro k hk; simp only [mem_range] at hk ⊢; omega
    · intro k hk
      simp only [Finset.mem_sdiff, mem_range, not_lt] at hk
      rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]; simp
    · intro _ _; rfl
  rw [h1]
  simp_rw [stirlingSecond_eq_sum, mul_sum]
  have h2 : ∀ k ∈ range (m + 1), ∀ j ∈ range (k + 1),
      1 / (k.factorial : ℚ) * ((-1) ^ (k - j) * (k.choose j : ℚ) * (j : ℚ) ^ n) =
        (j : ℚ) ^ n / j.factorial * ((-1 : ℚ) ^ (k - j) / (k - j).factorial) := by
    intro k _ j hj
    have hj : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [Nat.cast_choose ℚ hj]
    have : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    have : ((k - j).factorial : ℚ) ≠ 0 := by exact_mod_cast (k - j).factorial_ne_zero
    have : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  rw [sum_congr rfl fun k hk => sum_congr rfl (h2 k hk)]
  rw [sum_comm' (t' := range (m + 1)) (s' := fun j => Ico j (m + 1))]
  · refine sum_congr rfl fun j hj => ?_
    have hj : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [sum_Ico_eq_sum_range, show m + 1 - j = m - j + 1 by omega]
    simp
  · intro k j
    simp only [mem_range, mem_Ico]
    omega

/-- `∑_k k(k-1)⋯(k-j+1)/k! = e`. -/
theorem q26a_hasSum_descFactorial_div_factorial(j : ℕ) :
    HasSum (fun k : ℕ => (k.descFactorial j : ℝ) / k.factorial) (Real.exp 1) := by
  rw [← hasSum_nat_add_iff' j]
  have h0 : ∑ i ∈ range j, ((i.descFactorial j : ℕ) : ℝ) / i.factorial = 0 :=
    sum_eq_zero fun i hi => by
      rw [(Nat.descFactorial_eq_zero_iff_lt).mpr (mem_range.mp hi)]; simp
  rw [h0, sub_zero]
  have := NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at this
  convert this using 1
  ext k
  have h := Nat.factorial_mul_descFactorial (show j ≤ k + j by omega)
  rw [Nat.add_sub_cancel] at h
  rw [← h]; push_cast
  have : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have : ((k + j).descFactorial j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
  rw [one_pow, mul_comm, ← div_div, div_self this]

/-- DLMF 26.7.3: `B(n) = ∑_{k=1}^{m} (kⁿ/k!) ∑_{j=0}^{m-k} (-1)^j/j!` for `m ≥ n`, `n ≥ 1`.
**Correction (implicit condition):** fails for `n = 0`, `m ≥ 2`; see
`bell_eq_sum_range_mul_sum` for the `k = 0` form valid for all `n`. -/
@[dlmf 26.7.E3]
theorem bell_eq_sum_mul_sum {n m : ℕ} (hn : 1 ≤ n) (hm : n ≤ m) :
    (Nat.bell n : ℚ) = ∑ k ∈ Icc 1 m, (k : ℚ) ^ n / k.factorial *
      ∑ j ∈ range (m - k + 1), (-1 : ℚ) ^ j / j.factorial := by
  rw [q26a_bell_eq_sum_range_mul_sum hm, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [CharP.cast_eq_zero, zero_pow (by omega : n ≠ 0), zero_div, zero_mul, zero_add]
  rfl

/-- DLMF 26.7.4 (Dobiński's formula, `k = 0` form valid for all `n`):
`e B(n) = ∑_{k=0}^∞ kⁿ/k!`. -/
@[dlmf 26.7.E4]
theorem hasSum_pow_div_factorial (n : ℕ) :
    HasSum (fun k : ℕ => (k : ℝ) ^ n / k.factorial) (Real.exp 1 * Nat.bell n) := by
  have hs := hasSum_sum (s := range (n + 1)) fun j _ =>
    (q26a_hasSum_descFactorial_div_factorial j).mul_left (Nat.stirlingSecond n j : ℝ)
  rw [← sum_mul, mul_comm] at hs
  have hb : (Nat.bell n : ℝ) = ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℝ) := by
    rw [bell_eq_sum_stirlingSecond]; push_cast; rfl
  rw [hb]
  convert hs using 1
  ext k
  rw [← Nat.cast_pow, Nat.pow_eq_sum_stirlingSecond_mul_descFactorial, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun j _ => ?_
  push_cast; ring

/-- DLMF 26.7.4 (first equality, Dobiński's formula): `B(n) = e⁻¹ ∑_{k=1}^∞ kⁿ/k!`, `n ≥ 1`.
**Correction (implicit condition):** fails for `n = 0` (value `1 - e⁻¹`). -/
@[dlmf 26.7.E4]
theorem bell_eq_exp_neg_one_mul_tsum {n : ℕ} (hn : 1 ≤ n) :
    (Nat.bell n : ℝ) = Real.exp (-1) * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ n / (k + 1).factorial := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_pow_div_factorial n)
  simp only [range_one, sum_singleton, CharP.cast_eq_zero, zero_pow (by omega : n ≠ 0),
    zero_div, sub_zero] at h
  rw [h.tsum_eq, ← mul_assoc, ← Real.exp_add]; simp

/-- `kⁿ/k! ≤ 2ⁿ/(k-n)!` for `k ≥ 2n`. -/
theorem q26a_pow_div_factorial_le {n k : ℕ} (hk : 2 * n ≤ k) :
    (k : ℝ) ^ n / k.factorial ≤ 2 ^ n / (k - n).factorial := by
  have h1 : k ^ n ≤ 2 ^ n * k.descFactorial n := by
    calc k ^ n ≤ (2 * (k + 1 - n)) ^ n := Nat.pow_le_pow_left (by omega) n
      _ = 2 ^ n * (k + 1 - n) ^ n := by rw [mul_pow]
      _ ≤ 2 ^ n * k.descFactorial n := Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial k n)
  have h2 := Nat.factorial_mul_descFactorial (show n ≤ k by omega)
  have hD : (0 : ℝ) < k.descFactorial n := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
  have hF : (0 : ℝ) < (k - n).factorial := by exact_mod_cast (k - n).factorial_pos
  rw [← h2, div_le_div_iff₀ (by push_cast; positivity) hF]
  push_cast
  have : ((k : ℝ)) ^ n ≤ 2 ^ n * k.descFactorial n := by exact_mod_cast h1
  nlinarith

/-- `2ⁿ ≤ (n+1)!`. -/
theorem q26a_two_pow_le_factorial_succ (n : ℕ) : 2 ^ n ≤ (n + 1).factorial := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.factorial_succ]
    nlinarith

/-- DLMF 26.7.4 (second equality): `B(n) = 1 + ⌊e⁻¹ ∑_{k=1}^{2n} kⁿ/k!⌋` (all `n ≥ 0`). -/
@[dlmf 26.7.E4]
theorem bell_eq_one_add_floor (n : ℕ) :
    (Nat.bell n : ℤ) =
      1 + ⌊Real.exp (-1) * ∑ k ∈ Icc 1 (2 * n), (k : ℝ) ^ n / k.factorial⌋ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set f : ℕ → ℝ := fun k => (k : ℝ) ^ n / k.factorial with hf
  have hD := hasSum_pow_div_factorial n
  have hT := (hasSum_nat_add_iff' (2 * n + 1)).mpr hD
  set T := Real.exp 1 * Nat.bell n - ∑ i ∈ range (2 * n + 1), f i with hTdef
  have hS : ∑ i ∈ range (2 * n + 1), f i = ∑ k ∈ Icc 1 (2 * n), (k : ℝ) ^ n / k.factorial := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [hf, CharP.cast_eq_zero, zero_pow hn.ne', zero_div, zero_add]
    rfl
  -- positivity of the tail
  have hTpos : 0 < T := by
    have := le_hasSum hT 0 (fun j _ => by positivity)
    have h0 : 0 < f (0 + (2 * n + 1)) := by simp only [hf]; positivity
    linarith
  -- upper bound of the tail
  have hg : HasSum (fun i : ℕ => (2 : ℝ) ^ n / (i + (n + 1)).factorial)
      (2 ^ n * (Real.exp 1 - ∑ i ∈ range (n + 1), (1 : ℝ) ^ i / i.factorial)) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
    rw [← Real.exp_eq_exp_ℝ] at h
    have := ((hasSum_nat_add_iff' (n + 1)).mpr h).mul_left ((2 : ℝ) ^ n)
    convert this using 1
    ext i; simp [div_eq_mul_inv]
  have hle : T ≤ 2 ^ n * (Real.exp 1 - ∑ i ∈ range (n + 1), (1 : ℝ) ^ i / i.factorial) := by
    refine hasSum_le (fun i => ?_) hT hg
    have := q26a_pow_div_factorial_le (n := n) (k := i + (2 * n + 1)) (by omega)
    rw [show i + (2 * n + 1) - n = i + (n + 1) by omega] at this
    simpa [hf] using this
  have hexp := Real.exp_bound (x := 1) (by simp) (n := n + 1) (by omega)
  simp only [abs_one, one_pow, one_mul] at hexp
  have hfac : (2 : ℝ) ^ n * ((n + 1 + 1 : ℕ) / ((n + 1).factorial * (n + 1 : ℕ))) ≤ 3 / 2 := by
    have h1' : (2 : ℝ) ^ n ≤ (n + 1).factorial := by
      exact_mod_cast q26a_two_pow_le_factorial_succ n
    have hF : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast (n + 1).factorial_pos
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    push_cast
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have hT2 : T < Real.exp 1 := by
    have h3 := mul_le_mul_of_nonneg_left (abs_le.mp hexp).2 (by positivity : (0 : ℝ) ≤ 2 ^ n)
    simp only [one_pow] at hle
    push_cast at h3 hfac
    linarith
  have hBe : Real.exp (-1) * ∑ k ∈ Icc 1 (2 * n), (k : ℝ) ^ n / k.factorial =
      Nat.bell n - Real.exp (-1) * T := by
    rw [← hS, hTdef, mul_sub, ← mul_assoc, ← Real.exp_add]; simp
  rw [hBe]
  have h0 : 0 < Real.exp (-1) * T := by positivity
  have h1 : Real.exp (-1) * T < 1 := by
    have := Real.exp_pos (-1)
    calc Real.exp (-1) * T < Real.exp (-1) * Real.exp 1 := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  have : ⌊(Nat.bell n : ℝ) - Real.exp (-1) * T⌋ = (Nat.bell n : ℤ) - 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  rw [this]; ring

/-- DLMF 26.7.5: `∑_{n=0}^∞ B(n) xⁿ/n! = exp(eˣ - 1)`, all real `x`. -/
@[dlmf 26.7.E5]
theorem hasSum_bell_div_factorial (x : ℝ) :
    HasSum (fun n : ℕ => (Nat.bell n : ℝ) * x ^ n / n.factorial) (Real.exp (Real.exp x - 1)) := by
  have h := hasSum_stirlingSecond_bivariate x 1
  simp only [one_pow, mul_one, one_mul] at h
  refine h.prod_fiberwise fun n => ?_
  have hb : (Nat.bell n : ℝ) * x ^ n / n.factorial =
      ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℝ) * x ^ n / n.factorial := by
    rw [bell_eq_sum_stirlingSecond]; push_cast; rw [sum_mul, sum_div]
  rw [hb]
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  simp only [mem_range, not_lt] at hk
  rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]; simp

/-- DLMF 26.7.8: for every real `x ≥ 0` there is a unique `N ≥ 1` with `N ln N = x`
(DLMF: `N = e^{W₀(x)}`, Lambert's `W₀`). -/
@[dlmf 26.7.E8]
theorem existsUnique_mul_log_eq {x : ℝ} (hx : 0 ≤ x) :
    ∃! N : ℝ, 1 ≤ N ∧ N * Real.log N = x := by
  have hmono : ∀ a b : ℝ, 1 ≤ a → a < b → a * Real.log a < b * Real.log b := by
    intro a b ha hab
    have hb : 1 < b := by linarith
    have h1 : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab.le
    have h2 : 0 < Real.log b := Real.log_pos hb
    nlinarith [Real.log_nonneg ha]
  obtain ⟨N, hN, hNx⟩ : ∃ N ∈ Set.Icc (1 : ℝ) (x + Real.exp 1), N * Real.log N = x := by
    have hcont : ContinuousOn (fun N : ℝ => N * Real.log N) (Set.Icc 1 (x + Real.exp 1)) :=
      continuousOn_id.mul (Real.continuousOn_log.mono fun y hy => by
        simp only [Set.mem_Icc] at hy; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith)
    have he : 1 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1; linarith
    have hle : (1 : ℝ) ≤ x + Real.exp 1 := by linarith
    have := intermediate_value_Icc hle hcont
    apply this
    simp only [Set.mem_Icc, Real.log_one, mul_zero]
    refine ⟨hx, ?_⟩
    have hl : 1 ≤ Real.log (x + Real.exp 1) := by
      rw [Real.le_log_iff_exp_le (by positivity)]; linarith
    nlinarith
  refine ⟨N, ⟨hN.1, hNx⟩, ?_⟩
  rintro M ⟨hM, hMx⟩
  rcases lt_trichotomy M N with h | h | h
  · have := hmono M N hM h; linarith
  · exact h
  · have := hmono N M hN.1 h; linarith

/-- DLMF 26.7.7: `B(n) = Nⁿ e^{N-n-1} (1 + ln N)^{-1/2} (1 + O((ln n)^{1/2} n^{-1/2}))` as
`n → ∞`, where `N = N(n) ≥ 1` solves `N ln N = n` (26.7.8). -/
@[dlmf 26.7.E7]
theorem bell_isBigO (N : ℕ → ℝ) (hN : ∀ n : ℕ, 1 ≤ N n ∧ N n * Real.log (N n) = n) :
    (fun n : ℕ => (Nat.bell n : ℝ) /
        (N n ^ n * Real.exp (N n - n - 1) / Real.sqrt (1 + Real.log (N n))) - 1) =O[atTop]
      fun n : ℕ => Real.sqrt (Real.log n) / Real.sqrt n := by
  sorry

end DLMF.Combinatorics
