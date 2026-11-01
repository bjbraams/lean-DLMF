/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.PochhammerProperties
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The `q`-binomial theorem (AAR §10.2)

This file proves the `q`-binomial theorem. The basic properties of the finite and infinite
`q`-Pochhammer symbols and of the `q`-gamma function are in
`DLMF.QSeries.Basic.PochhammerProperties`; Mathlib's Pochhammer file lists `q`-factorials as a
TODO.

## Main results

* `summable_q_binomial_series`: the `q`-binomial series converges for `|q| < 1`, `|z| < 1`.
* `q_binomial_theorem`: the `q`-binomial theorem (DLMF 17.2.37, 17.5.2).
-/

@[expose] public section

open Complex Finset Filter
open scoped Topology Real

noncomputable section

namespace DLMF.QSeries

/-- For `|q| < 1` and `|z| < 1` the `q`-binomial series `∑ (a;q)_n/(q;q)_n zⁿ` converges. -/
theorem summable_q_binomial_series {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      qPochhammer a q n / qPochhammer q q n * z ^ n := by
  obtain ⟨r, hr_lt, hr_one⟩ := exists_between hz
  refine summable_of_ratio_norm_eventually_le hr_one ?_
  have hqn (n : ℕ) : qPochhammer q q n ≠ 0 := qPochhammer_self_ne_zero hq n
  have hq1 (n : ℕ) : 1 - q ^ (n + 1) ≠ 0 := qPochhammerInf_pow_succ_ne_zero hq n
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have hnum : Tendsto (fun n : ℕ => ‖1 - a * q ^ n‖) atTop (𝓝 1) := by
    have h :=
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).mul hpow)).norm
    simpa [norm_one] using h
  have hden : Tendsto (fun n : ℕ => ‖1 - q ^ (n + 1)‖) atTop (𝓝 1) := by
    have h :=
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub
        (hpow.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => q) atTop (𝓝 q)))).norm
    simpa [pow_succ, norm_one] using h
  have hratio : Tendsto (fun n : ℕ =>
      ‖1 - a * q ^ n‖ / ‖1 - q ^ (n + 1)‖ * ‖z‖) atTop (𝓝 ‖z‖) := by
    simpa using (hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖z‖) atTop (𝓝 ‖z‖))
  filter_upwards [hratio.eventually_lt tendsto_const_nhds hr_lt] with n hn
  have hrec := q_binomial_coeff_succ a q n (hqn n) (hq1 n)
  have heq :
      qPochhammer a q (n + 1) / qPochhammer q q (n + 1) * z ^ (n + 1) =
        (1 - a * q ^ n) / (1 - q ^ (n + 1)) * z *
          (qPochhammer a q n / qPochhammer q q n * z ^ n) := by
    rw [hrec, pow_succ]
    ring
  rw [heq, norm_mul, norm_mul, norm_div]
  exact mul_le_mul_of_nonneg_right (le_of_lt hn) (norm_nonneg _)

/-- The functional equation `(1 - w) G(w) = (1 - a w) G(q w)` of the `q`-binomial series
`G(w) = ∑ (a;q)_n/(q;q)_n wⁿ`, for `|q| < 1` and `|w| < 1`. -/
private lemma q_binomial_series_functional_eq {a q w : ℂ} (hq : ‖q‖ < 1) (hw : ‖w‖ < 1) :
    (1 - w) * ∑' n : ℕ, qPochhammer a q n / qPochhammer q q n * w ^ n =
      (1 - a * w) * ∑' n : ℕ, qPochhammer a q n / qPochhammer q q n * (q * w) ^ n := by
  let c : ℕ → ℂ := fun n => qPochhammer a q n / qPochhammer q q n
  let G : ℂ → ℂ := fun w => ∑' n : ℕ, c n * w ^ n
  have hc0 : c 0 = 1 := by simp [c]
  have hsum {w : ℂ} (hw : ‖w‖ < 1) : Summable fun n : ℕ => c n * w ^ n := by
    simpa [c] using summable_q_binomial_series (a := a) hq hw
  have hqw : ‖q * w‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg q) hw.le).trans_lt hq
  change (1 - w) * G w = (1 - a * w) * G (q * w)
  have hS : HasSum (fun n : ℕ => c n * w ^ n) (G w) := (hsum hw).hasSum
  have hS' : HasSum (fun n : ℕ => c n * (q * w) ^ n) (G (q * w)) := (hsum hqw).hasSum
  let g : ℕ → ℂ := fun n =>
    match n with
    | 0 => 0
    | n + 1 => c n * w ^ (n + 1)
  let g' : ℕ → ℂ := fun n =>
    match n with
    | 0 => 0
    | n + 1 => a * c n * q ^ n * w ^ (n + 1)
  have hg0 : g 0 = 0 := rfl
  have hg'0 : g' 0 = 0 := rfl
  have hgs : HasSum (fun n : ℕ => g (n + 1)) (w * G w) :=
    (hS.mul_left w).congr_fun fun n => by ring
  have hg's : HasSum (fun n : ℕ => g' (n + 1)) (a * w * G (q * w)) := by
    refine (hS'.mul_left (a * w)).congr_fun fun n => ?_
    dsimp [g']
    rw [mul_pow]
    ring
  have hg : HasSum g (w * G w) := by
    have h := (hasSum_nat_add_iff (f := g) 1).mp hgs
    simpa [hg0] using h
  have hg' : HasSum g' (a * w * G (q * w)) := by
    have h := (hasSum_nat_add_iff (f := g') 1).mp hg's
    simpa [hg'0] using h
  have hL : HasSum (fun n : ℕ => c n * w ^ n - g n) ((1 - w) * G w) := by
    have h := hS.sub hg
    rwa [show G w - w * G w = (1 - w) * G w by ring] at h
  have hR : HasSum (fun n : ℕ => c n * (q * w) ^ n - g' n) ((1 - a * w) * G (q * w)) := by
    have h := hS'.sub hg'
    rwa [show G (q * w) - a * w * G (q * w) = (1 - a * w) * G (q * w) by ring] at h
  have hterm : ∀ n : ℕ, c n * w ^ n - g n = c n * (q * w) ^ n - g' n := by
    intro n
    cases n with
    | zero =>
      simp [g, g', hc0]
    | succ n =>
      have hid := q_binomial_coeff_sub (a := a) hq n
      simp only [g, g']
      calc
        c (n + 1) * w ^ (n + 1) - c n * w ^ (n + 1)
            = (c (n + 1) - c n) * w ^ (n + 1) := by ring
        _ = (c (n + 1) * q ^ (n + 1) - a * c n * q ^ n) * w ^ (n + 1) := by rw [hid]
        _ = c (n + 1) * (q * w) ^ (n + 1) - a * c n * q ^ n * w ^ (n + 1) := by
          simp only [mul_pow]
          ring
  have hL' : HasSum (fun n : ℕ => c n * w ^ n - g n) ((1 - a * w) * G (q * w)) :=
    hR.congr_fun fun n => hterm n
  exact hL.unique hL'

/-- For `|q| < 1` and `|z| < 1`, the `q`-binomial series at `qⁿ z` tends to `1` as `n → ∞`
(dominated convergence). -/
private lemma tendsto_q_binomial_series_pow_mul {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Tendsto (fun n : ℕ => ∑' k : ℕ, qPochhammer a q k / qPochhammer q q k * (q ^ n * z) ^ k)
      atTop (𝓝 1) := by
  let c : ℕ → ℂ := fun n => qPochhammer a q n / qPochhammer q q n
  let G : ℂ → ℂ := fun w => ∑' n : ℕ, c n * w ^ n
  have hc0 : c 0 = 1 := by simp [c]
  have hsum {w : ℂ} (hw : ‖w‖ < 1) : Summable fun n : ℕ => c n * w ^ n := by
    simpa [c] using summable_q_binomial_series (a := a) hq hw
  change Tendsto (fun n : ℕ => G (q ^ n * z)) atTop (𝓝 1)
  have hbound : Summable fun k : ℕ => ‖c k * z ^ k‖ := (hsum hz).norm
  have hpt (k : ℕ) :
      Tendsto (fun n : ℕ => c k * (q ^ n * z) ^ k) atTop
        (𝓝 (if k = 0 then (1 : ℂ) else 0)) := by
    by_cases hk : k = 0
    · subst hk
      simp [c]
    · have hqn : ‖q ^ k‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg q) hq hk
      have hlim :=
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hqn).mul
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => c k * z ^ k) atTop (𝓝 (c k * z ^ k)))
      have heq (n : ℕ) :
          c k * (q ^ n * z) ^ k = (q ^ k) ^ n * (c k * z ^ k) := by
        rw [mul_pow, ← pow_mul, mul_comm n k, pow_mul]
        ring
      simpa [hk] using hlim.congr fun n => (heq n).symm
  have hbd (n k : ℕ) : ‖c k * (q ^ n * z) ^ k‖ ≤ ‖c k * z ^ k‖ := by
    have hle : ‖q‖ ^ (n * k) ≤ 1 := pow_le_one₀ (norm_nonneg q) hq.le
    calc
      ‖c k * (q ^ n * z) ^ k‖
          = ‖c k‖ * ‖q ^ n * z‖ ^ k := by rw [norm_mul, norm_pow]
      _ = ‖c k‖ * (‖q‖ ^ n * ‖z‖) ^ k := by rw [norm_mul, norm_pow]
      _ = ‖c k‖ * ((‖q‖ ^ n) ^ k * ‖z‖ ^ k) := by rw [mul_pow]
      _ = ‖c k‖ * ‖z‖ ^ k * (‖q‖ ^ n) ^ k := by ring
      _ = ‖c k‖ * ‖z‖ ^ k * ‖q‖ ^ (n * k) := by rw [← pow_mul]
      _ = ‖c k * z ^ k‖ * ‖q‖ ^ (n * k) := by rw [norm_mul, norm_pow]
      _ ≤ ‖c k * z ^ k‖ * 1 := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ‖c k * z ^ k‖ := by rw [mul_one]
  have ht :=
    tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (bound := fun k : ℕ => ‖c k * z ^ k‖)
      (f := fun n k : ℕ => c k * (q ^ n * z) ^ k)
      (g := fun k : ℕ => if k = 0 then (1 : ℂ) else 0)
      hbound hpt (Filter.Eventually.of_forall hbd)
  have hg : (∑' k : ℕ, if k = 0 then (1 : ℂ) else 0) = 1 :=
    tsum_ite_eq (0 : ℕ) (fun _ => (1 : ℂ))
  simpa [G, hg] using ht

/-- The `q`-binomial theorem (AAR §10.2, Heine):
`(az;q)_∞ / (z;q)_∞ = ∑ (a;q)_n z^n / (q;q)_n` for `|z| < 1` and `|q| < 1`. -/
@[dlmf 17.2.E37, dlmf 17.5.E2 "exact: one-phi-zero in |z|<1; local general-notation adapter proved"]
theorem q_binomial_theorem {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    qPochhammerInf (a * z) q / qPochhammerInf z q =
      ∑' n : ℕ, qPochhammer a q n / qPochhammer q q n * z ^ n := by
  let c : ℕ → ℂ := fun n => qPochhammer a q n / qPochhammer q q n
  let G : ℂ → ℂ := fun w => ∑' n : ℕ, c n * w ^ n
  have hFE {w : ℂ} (hw : ‖w‖ < 1) : (1 - w) * G w = (1 - a * w) * G (q * w) :=
    q_binomial_series_functional_eq hq hw
  have hwq (n : ℕ) : ‖q ^ n * z‖ < 1 := by
    rw [norm_mul, norm_pow, mul_comm]
    exact (mul_le_of_le_one_right (norm_nonneg z)
      (pow_le_one₀ (norm_nonneg q) hq.le)).trans_lt hz
  have hiter : ∀ n : ℕ, G z * qPochhammer z q n =
      qPochhammer (a * z) q n * G (q ^ n * z) := by
    intro n
    induction n with
    | zero => simp [G, qPochhammer_zero, pow_zero]
    | succ n ih =>
      have hFE' := hFE (hwq n)
      have hpow : q * (q ^ n * z) = q ^ (n + 1) * z := by
        rw [pow_succ', mul_assoc]
      rw [hpow] at hFE'
      rw [qPochhammer_succ, qPochhammer_succ]
      linear_combination (1 - z * q ^ n) * ih + qPochhammer (a * z) q n * hFE'
  have hG : Tendsto (fun n : ℕ => G (q ^ n * z)) atTop (𝓝 1) :=
    tendsto_q_binomial_series_pow_mul hq hz
  have hzinf : qPochhammerInf z q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hz hq
  have hL : Tendsto (fun n : ℕ => G z * qPochhammer z q n) atTop
      (𝓝 (G z * qPochhammerInf z q)) :=
    tendsto_const_nhds.mul (tendsto_qPochhammer (w := z) hq)
  have hR : Tendsto (fun n : ℕ => G z * qPochhammer z q n) atTop
      (𝓝 (qPochhammerInf (a * z) q)) := by
    simp only [hiter]
    simpa using (tendsto_qPochhammer (w := a * z) hq).mul hG
  have hval : G z * qPochhammerInf z q = qPochhammerInf (a * z) q :=
    tendsto_nhds_unique hL hR
  change qPochhammerInf (a * z) q / qPochhammerInf z q = G z
  rw [div_eq_iff hzinf]
  exact hval.symm

end DLMF.QSeries
