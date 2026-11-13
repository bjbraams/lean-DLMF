/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Basic.Stirling
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.PSeries

/-!
# Uniform estimates for Stirling numbers of the first kind

The factorial-normalized Stirling recurrence compares `k! |s(n+1,k+1)| / n!` with `H_n^k`.
A second-order power estimate bounds the difference by a quadratic expression in `k`,
multiplied by a partial sum of reciprocal squares. The latter sums are bounded. Thus
`k = o(log n)` makes the relative error tend to zero. The convergence
`H_n - log n → γ` then replaces `H_n^k` with `(log n + γ)^k` uniformly in that range.

The proof uses Mathlib's first-kind Stirling recurrence, harmonic-number bounds and
Euler–Mascheroni limit, p-series summability, and Bernoulli's inequality.

## Main results

* `StirlingFirstEstimates.normalized_div_bounds`: a relative quadratic error bound.
* `StirlingFirstEstimates.tendsto_normalized_div_log_add_constant_pow`: the uniform
  logarithmic approximation underlying DLMF 26.8.40.
-/

public noncomputable section

open Finset Filter Topology Asymptotics

namespace DLMF.Combinatorics.StirlingFirstEstimates

/-- The first-kind Stirling number `s(n+1,k+1)`, without its sign, normalized by `k!/n!`. -/
@[expose] def normalized (n k : ℕ) : ℝ :=
  k.factorial * (Nat.stirlingFirst (n + 1) (k + 1) : ℝ) / n.factorial


/-- The defining factorial normalization of the unsigned first-kind Stirling number. -/
lemma normalized_def (n k : ℕ) :
    normalized n k = k.factorial * (Nat.stirlingFirst (n + 1) (k + 1) : ℝ) / n.factorial := rfl

/-- The normalization is one in the first nonzero column. -/
lemma normalized_zero_right (n : ℕ) : normalized n 0 = 1 := by
  simp [normalized, Nat.stirlingFirst_one_right, Nat.factorial_ne_zero]

/-- The normalization vanishes above the first row. -/
lemma normalized_zero_left (k : ℕ) : normalized 0 (k + 1) = 0 := by
  simp [normalized, Nat.stirlingFirst_eq_zero_of_lt (by omega : 1 < k + 1 + 1)]

/-- The first-kind Stirling recurrence after factorial normalization. -/
lemma normalized_succ_succ (n k : ℕ) :
    normalized (n + 1) (k + 1) = normalized n (k + 1) +
      (k + 1 : ℝ) / (n + 1) * normalized n k := by
  unfold normalized
  rw [show n + 1 + 1 = (n + 1) + 1 by omega, Nat.stirlingFirst_succ_succ,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn' : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- The second nonzero column after normalization is the harmonic number. -/
lemma normalized_one (n : ℕ) : normalized n 1 = (harmonic n : ℝ) := by
  induction n with
  | zero => simp [normalized_zero_left]
  | succ n ih =>
    rw [show 1 = 0 + 1 by omega, normalized_succ_succ, normalized_zero_right, ih]
    simp [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]

/-- A normalized first-kind Stirling number is bounded by the corresponding harmonic power. -/
lemma normalized_le_harmonic_pow (n k : ℕ) :
    normalized n k ≤ (harmonic n : ℝ) ^ k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [normalized_zero_right]
    | succ k => simp [normalized_zero_left]
  | succ n ih =>
    cases k with
    | zero => simp [normalized_zero_right]
    | succ k =>
      rw [normalized_succ_succ, harmonic_succ]
      push_cast
      have hH : (0 : ℝ) ≤ harmonic n := by unfold harmonic; positivity
      calc
        _ ≤ (harmonic n : ℝ) ^ (k + 1) +
            (k + 1 : ℝ) / (n + 1) * (harmonic n : ℝ) ^ k := by
          exact add_le_add (ih (k + 1)) (mul_le_mul_of_nonneg_left (ih k) (by positivity))
        _ ≤ _ := by
          have h := pow_add_mul_le_add_pow hH
            (by positivity : (0 : ℝ) ≤ 2 * (harmonic n : ℝ) + (n + 1 : ℝ)⁻¹) (k + 1)
          simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
            mul_comm, mul_left_comm, mul_assoc] using h

/-- A quadratic collision bound for normalized first-kind Stirling numbers. The error is
controlled by the partial sum of reciprocal squares. -/
lemma harmonic_pow_sub_le_normalized (n k : ℕ) :
    (harmonic n : ℝ) ^ (k + 2) - ((k + 2 : ℝ) * (k + 1) / 2) *
        (∑ j ∈ range n, (j + 1 : ℝ)⁻¹ ^ 2) * (harmonic n : ℝ) ^ k ≤
      normalized n (k + 2) := by

  have power_second_order_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
      (x + y) ^ (k + 2) ≤ x ^ (k + 2) + (k + 2 : ℝ) * y * x ^ (k + 1) +
        ((k + 2 : ℝ) * (k + 1) / 2) * y ^ 2 * (x + y) ^ k := by
    induction k with
    | zero => norm_num; nlinarith
    | succ k ih =>
      have h := mul_le_mul_of_nonneg_left ih (add_nonneg hx hy)
      have hpow := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hx (le_add_of_nonneg_right hy) (k + 1))
        (by positivity : 0 ≤ (k + 2 : ℝ) * y ^ 2)
      simp only [pow_succ] at h hpow ⊢
      push_cast
      nlinarith
  induction n generalizing k with
  | zero => simp [normalized_zero_left]
  | succ n ih =>
    let H : ℝ := harmonic n
    let P : ℝ := ∑ j ∈ range n, (j + 1 : ℝ)⁻¹ ^ 2
    let a : ℝ := (n + 1 : ℝ)⁻¹
    have hH : 0 ≤ H := by dsimp only [H]; unfold harmonic; positivity
    have hP : 0 ≤ P := by dsimp only [P]; positivity
    have ha : 0 ≤ a := by dsimp only [a]; positivity
    rw [harmonic_succ, sum_range_succ]
    push_cast
    -- Fold the harmonic and reciprocal-sum abbreviations after rewriting their recurrences.
    change (H + a) ^ (k + 2) - ((k + 2 : ℝ) * (k + 1) / 2) * (P + a ^ 2) *
      (H + a) ^ k ≤ normalized (n + 1) (k + 2)
    rw [show k + 2 = (k + 1) + 1 by omega, normalized_succ_succ]
    push_cast
    simp only [div_eq_mul_inv]
    -- Express the factorial-normalized recurrence in the same abbreviations.
    change (H + a) ^ (k + 1 + 1) - ((k + 2 : ℝ) * (k + 1) / 2) * (P + a ^ 2) *
      (H + a) ^ k ≤ normalized n (k + 1 + 1) + (k + 1 + 1 : ℝ) * a *
        normalized n (k + 1)
    cases k with
    | zero =>
      have h := ih 0
      norm_num only [Nat.cast_zero, zero_add, mul_one, pow_zero, one_mul, Nat.cast_ofNat] at h
      -- Fold the harmonic and reciprocal-square abbreviations in the induction hypothesis.
      change H ^ 2 - P ≤ normalized n 2 at h
      rw [normalized_one]
      dsimp only [H] at *
      norm_num at h ⊢
      nlinarith
    | succ k =>
      have h1 := ih (k + 1)
      have h2 := ih k
      push_cast at h1
      -- Fold the same abbreviations in the two neighboring induction hypotheses.
      change H ^ (k + 1 + 2) - ((k + 1 + 2 : ℝ) * (k + 1 + 1) / 2) * P *
        H ^ (k + 1) ≤ normalized n (k + 1 + 2) at h1
      change H ^ (k + 2) - ((k + 2 : ℝ) * (k + 1) / 2) * P * H ^ k ≤
        normalized n (k + 2) at h2
      have hmul := mul_le_mul_of_nonneg_left h2
        (mul_nonneg (show (0 : ℝ) ≤ k + 3 by positivity) ha)
      have hpow := power_second_order_bound hH ha (k + 1)
      have hb := pow_add_mul_le_add_pow hH
        (by positivity : (0 : ℝ) ≤ 2 * H + a) (k + 1)
      have hber := mul_le_mul_of_nonneg_left hb
        (by positivity : 0 ≤ ((k + 3 : ℝ) * (k + 2) / 2) * P)
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hpow hber
      simp only [Nat.cast_add, Nat.cast_one] at h1 h2 hmul ⊢
      have he1 : k + 1 + 2 = k + 1 + 1 + 1 := by omega
      rw [he1] at h1 hpow
      nlinarith

/-- The ratio to a harmonic power lies within a quadratic error of one. -/
lemma normalized_div_bounds {n : ℕ} (hn : 0 < (harmonic n : ℝ)) (k : ℕ) :
    1 - (k : ℝ) ^ 2 * (∑ j ∈ range n, (j + 1 : ℝ)⁻¹ ^ 2) / (harmonic n : ℝ) ^ 2 ≤
      normalized n k / (harmonic n : ℝ) ^ k ∧
      normalized n k / (harmonic n : ℝ) ^ k ≤ 1 := by
  have hH : (0 : ℝ) < (harmonic n : ℝ) ^ k := pow_pos hn _
  refine ⟨?_, (div_le_one hH).mpr (normalized_le_harmonic_pow n k)⟩
  cases k with
  | zero => simp [normalized_zero_right]
  | succ k =>
    cases k with
    | zero =>
      rw [normalized_one]
      simp only [zero_add, Nat.cast_one, one_pow, pow_one, div_self hn.ne']
      exact sub_le_self _ (by positivity)
    | succ k =>
      have h := harmonic_pow_sub_le_normalized n k
      have hP : (0 : ℝ) ≤ ∑ j ∈ range n, (j + 1 : ℝ)⁻¹ ^ 2 := by positivity
      have hC : (k + 2 : ℝ) * (k + 1) / 2 ≤ (k + 2 : ℝ) ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      have he : (harmonic n : ℝ) ^ (k + 2) - (k + 2 : ℝ) ^ 2 *
          (∑ j ∈ range n, (j + 1 : ℝ)⁻¹ ^ 2) * (harmonic n : ℝ) ^ k ≤
            normalized n (k + 2) := by
        exact (sub_le_sub_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC hP) (pow_nonneg hn.le k)) _).trans h
      rw [le_div_iff₀ hH]
      push_cast
      have hN : (harmonic n : ℝ) ≠ 0 := hn.ne'
      convert he using 1
      field_simp
      ring

/-- The harmonic-power approximation is uniform for the column index `k = o(log n)`. -/
lemma tendsto_normalized_div_harmonic_pow (k : ℕ → ℕ)
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => Real.log n) :
    Tendsto (fun n : ℕ => normalized n (k n) / (harmonic n : ℝ) ^ k n) atTop (𝓝 1) := by
  have hlog := hk.tendsto_div_nhds_zero
  have hHlog (n : ℕ) : Real.log n ≤ (harmonic n : ℝ) := by
    simpa only [Nat.floor_natCast] using log_le_harmonic_floor (n : ℝ) (Nat.cast_nonneg n)
  have hHpos {n : ℕ} (hn : 2 ≤ n) : 0 < (harmonic n : ℝ) :=
    (Real.log_pos (by exact_mod_cast hn)).trans_le (hHlog n)
  have hsmall : Tendsto (fun n : ℕ => (k n : ℝ) / harmonic n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
    · exact Filter.Eventually.of_forall fun n => by unfold harmonic; positivity
    · filter_upwards [eventually_ge_atTop 2] with n hn
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (Real.log_pos (by exact_mod_cast hn)) (hHlog n)
  have hs : Summable (fun n : ℕ => (n + 1 : ℝ)⁻¹ ^ 2) := by
    simpa only [Function.comp_def, Nat.cast_succ, inv_pow] using
      (Real.summable_nat_pow_inv.mpr (by omega : 1 < 2)).comp_injective
        (fun a b h => Nat.succ_injective h)
  let B : ℝ := ∑' n : ℕ, (n + 1 : ℝ)⁻¹ ^ 2
  have hB (n : ℕ) : (∑ j ∈ range n, (j + 1 : ℝ)⁻¹ ^ 2) ≤ B :=
    hs.sum_le_tsum (range n) (fun _ _ => sq_nonneg _)
  have hlim : Tendsto (fun n : ℕ => 1 - B * ((k n : ℝ) / harmonic n) ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ((hsmall.pow 2).const_mul B)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h := (normalized_div_bounds (hHpos hn) (k n)).1
    apply le_trans _ h
    rw [sub_le_sub_iff_left, div_pow]
    convert mul_le_mul_of_nonneg_left (hB n)
      (by positivity : 0 ≤ (k n : ℝ) ^ 2 / harmonic n ^ 2) using 1 <;> ring
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact (normalized_div_bounds (hHpos hn) (k n)).2

/-- The logarithmic approximation with Euler–Mascheroni constant is uniform for
`k = o(log n)`, as required in DLMF 26.8.40. -/
lemma tendsto_normalized_div_log_add_constant_pow (k : ℕ → ℕ)
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => Real.log n) :
    Tendsto (fun n : ℕ => normalized n (k n) /
      (Real.eulerMascheroniConstant + Real.log n) ^ k n) atTop (𝓝 1) := by

  have hHpow :
      Tendsto (fun n : ℕ => ((harmonic n : ℝ) /
        (Real.eulerMascheroniConstant + Real.log n)) ^ k n) atTop (𝓝 1) := by
    let L : ℕ → ℝ := fun n => Real.eulerMascheroniConstant + Real.log n
    have hγ : 0 < Real.eulerMascheroniConstant := by
      linarith [Real.one_half_lt_eulerMascheroniConstant]
    have hLpos {n : ℕ} (hn : 1 ≤ n) : 0 < L n :=
      add_pos_of_pos_of_nonneg hγ (Real.log_nonneg (by exact_mod_cast hn))
    have hLlog (n : ℕ) : Real.log n ≤ L n := by dsimp only [L]; linarith
    have hLH {n : ℕ} (hn : 1 ≤ n) : L n ≤ (harmonic n : ℝ) := by
      have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
      rw [Real.eulerMascheroniSeq', ite_eq_right (by omega : n ≠ 0)] at h
      dsimp only [L]
      linarith
    have hsmall : Tendsto (fun n : ℕ => (k n : ℝ) / L n) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hk.tendsto_div_nhds_zero
      · filter_upwards [eventually_ge_atTop 1] with n hn
        exact div_nonneg (Nat.cast_nonneg _) (hLpos hn).le
      · filter_upwards [eventually_ge_atTop 2] with n hn
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
          (Real.log_pos (by exact_mod_cast hn)) (hLlog n)
    have hdiff : Tendsto (fun n : ℕ => (harmonic n : ℝ) - L n) atTop (𝓝 0) := by
      convert (by simpa only [sub_self] using
        Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant) using 1
      ext n; dsimp only [L]; ring
    have hexp : Tendsto (fun n : ℕ => Real.exp ((k n : ℝ) / L n *
        ((harmonic n : ℝ) - L n))) atTop (𝓝 1) := by
      have hz : Tendsto (fun n : ℕ => (k n : ℝ) / L n *
          ((harmonic n : ℝ) - L n)) atTop (𝓝 0) := by simpa using hsmall.mul hdiff
      simpa only [Function.comp_def, Real.exp_zero] using
        (Real.continuous_exp.tendsto 0).comp hz
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact one_le_pow₀ ((one_le_div (hLpos hn)).mpr (hLH hn))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      calc
        _ ≤ (Real.exp (((harmonic n : ℝ) - L n) / L n)) ^ k n := by
          apply pow_le_pow_left₀ (div_nonneg ((hLpos hn).le.trans (hLH hn)) (hLpos hn).le)
          have h := Real.add_one_le_exp (((harmonic n : ℝ) - L n) / L n)
          convert h using 1
          field_simp [(hLpos hn).ne']
          ring
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h := (tendsto_normalized_div_harmonic_pow k hk).mul
    hHpow
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hH : (harmonic n : ℝ) ≠ 0 := ne_of_gt <|
    (Real.log_pos (show (1 : ℝ) < n by exact_mod_cast (by omega : 1 < n))).trans_le
      (by simpa only [Nat.floor_natCast] using
        log_le_harmonic_floor (n : ℝ) (Nat.cast_nonneg n))
  rw [div_pow]
  field_simp

end DLMF.Combinatorics.StirlingFirstEstimates
