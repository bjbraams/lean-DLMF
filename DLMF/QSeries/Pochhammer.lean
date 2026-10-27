/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The `q`-Pochhammer symbol, `q`-binomial theorem, and `q`-gamma (AAR §§10.1–10.3)

Mathlib's Pochhammer file lists `q`-factorials as a TODO. The `q`-Pochhammer symbol
`(a;q)_n = ∏_{k=0}^{n-1} (1-aq^k)` is defined here.
-/

@[expose] public section

open Complex Finset Filter
open scoped Topology Real

noncomputable section

namespace DLMF.QSeries

/-- The finite `q`-Pochhammer symbol `(a;q)_n`. -/
@[dlmf 17.2.E1]
def qPochhammer (a q : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => qPochhammer a q n * (1 - a * q ^ n)

@[simp]
theorem qPochhammer_zero (a q : ℂ) : qPochhammer a q 0 = 1 := rfl

theorem qPochhammer_succ (a q : ℂ) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer a q n * (1 - a * q ^ n) :=
  rfl

/-- `(a;q)_{m+k} = (a;q)_m (aq^m;q)_k`. -/
theorem qPochhammer_add (a q : ℂ) (m k : ℕ) :
    qPochhammer a q (m + k) = qPochhammer a q m * qPochhammer (a * q ^ m) q k := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, qPochhammer_succ, ih, qPochhammer_succ, pow_add]; ring

theorem qPochhammer_one (a q : ℂ) : qPochhammer a q 1 = 1 - a := by
  simp [qPochhammer_succ]

@[dlmf 17.2.E1]
theorem qPochhammer_eq_prod (a q : ℂ) (n : ℕ) :
    qPochhammer a q n = ∏ k ∈ range n, (1 - a * q ^ k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [qPochhammer_succ, ih, prod_range_succ]

@[simp]
theorem qPochhammer_zero_param (q : ℂ) (n : ℕ) : qPochhammer 0 q n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [qPochhammer_succ, ih]

/-- The infinite `q`-Pochhammer symbol `(a;q)_∞`. -/
@[dlmf 17.2.E4]
def qPochhammerInf (a q : ℂ) : ℂ :=
  ∏' k : ℕ, (1 - a * q ^ k)

/-- The infinite product is nonzero inside the unit disk if none of its factors vanish. -/
theorem qPochhammerInf_ne_zero {a q : ℂ} (hq : ‖q‖ < 1)
    (ha : ∀ n : ℕ, 1 - a * q ^ n ≠ 0) : qPochhammerInf a q ≠ 0 := by
  -- Already follows from Mathlib's `tprod_one_add_ne_zero_of_summable`.
  have hs : Summable (fun n : ℕ => ‖-(a * q ^ n)‖) := by
    simpa only [norm_neg, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖a‖
  simpa only [qPochhammerInf, sub_eq_add_neg] using
    tprod_one_add_ne_zero_of_summable
      (f := fun n : ℕ => -(a * q ^ n)) (by simpa only [← sub_eq_add_neg] using ha) hs

/-- Splitting off the first factor of `(a;q)_∞`, for `|q| < 1`. -/
theorem qPochhammerInf_shift {a q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf a q = (1 - a) * qPochhammerInf (a * q) q := by
  -- This is Mathlib's `tprod_eq_zero_mul'` for a geometric perturbation of one.
  have hs : Multipliable (fun n : ℕ => 1 - (a * q) * q ^ n) := by
    simpa only [sub_eq_add_neg] using
      multipliable_one_add_of_summable (f := fun n : ℕ => -((a * q) * q ^ n))
        (by simpa only [norm_neg, norm_mul, norm_pow] using
          (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖a * q‖)
  simpa only [qPochhammerInf, pow_zero, mul_one, pow_succ', mul_assoc] using
    (tprod_eq_zero_mul' (f := fun n : ℕ => 1 - a * q ^ n)
      (by simpa only [pow_succ', mul_assoc] using hs))

/-- Jackson's `q`-integral `∫_0^a f(t)\,d_q t` (AAR §10.1). -/
@[dlmf 17.2.E46]
def jacksonIntegral (q a : ℂ) (f : ℂ → ℂ) : ℂ :=
  a * (1 - q) * ∑' n : ℕ, f (a * q ^ n) * q ^ n

/-- `∫_0^1 1\,d_q t = 1` for `|q| < 1`. -/
theorem jacksonIntegral_one {q : ℂ} (hq : ‖q‖ < 1) :
    jacksonIntegral q 1 (fun _ => 1) = 1 := by
  unfold jacksonIntegral
  simp only [one_mul]
  have hsum : ∑' n : ℕ, q ^ n = (1 - q)⁻¹ := tsum_geometric_of_norm_lt_one hq
  have hne : 1 - q ≠ 0 := by
    intro h
    have : ‖(1 : ℂ)‖ = ‖q‖ := by simp [sub_eq_zero.mp h]
    simp at this
    linarith
  rw [hsum]
  field [hne]

/-- Splitting `(a;q)_∞ = (a;q)_n (aq^n;q)_∞`. Helper lemma for the `q`-binomial theorem. -/
theorem qPochhammerInf_mul_qPochhammer {a q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf a q = qPochhammer a q n * qPochhammerInf (a * q ^ n) q := by
  induction n with
  | zero => simp [qPochhammer_zero]
  | succ n ih =>
    rw [qPochhammer_succ, ih, mul_assoc, qPochhammerInf_shift (a := a * q ^ n) hq]
    congr 1
    ring_nf

theorem qPochhammer_self_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammer q q n ≠ 0 := by
  have ha : ∀ k : ℕ, 1 - q * q ^ k ≠ 0 := by
    intro k h
    have hn : ‖q ^ (k + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero k)
    have hq1 : (1 : ℂ) = q * q ^ k := sub_eq_zero.mp h
    have : ‖q ^ (k + 1)‖ = 1 := by
      rw [pow_succ', ← hq1, norm_one]
    exact (lt_irrefl (1 : ℝ)) (this ▸ hn)
  have hinf := qPochhammerInf_ne_zero (a := q) hq ha
  rw [qPochhammerInf_mul_qPochhammer hq n] at hinf
  exact left_ne_zero_of_mul hinf

theorem qPochhammerInf_pow_succ_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    1 - q ^ (n + 1) ≠ 0 := by
  intro h
  have hn : ‖q ^ (n + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero n)
  have : ‖q ^ (n + 1)‖ = 1 := by
    rw [← sub_eq_zero.mp h, norm_one]
  exact (lt_irrefl (1 : ℝ)) (this ▸ hn)

/-- Helper lemma for the `q`-binomial theorem. -/
theorem q_binomial_coeff_succ (a q : ℂ) (n : ℕ)
    (hqn : qPochhammer q q n ≠ 0) (hq1 : 1 - q ^ (n + 1) ≠ 0) :
    qPochhammer a q (n + 1) / qPochhammer q q (n + 1) =
      (1 - a * q ^ n) / (1 - q ^ (n + 1)) *
        (qPochhammer a q n / qPochhammer q q n) := by
  have hqq : qPochhammer q q (n + 1) = qPochhammer q q n * (1 - q ^ (n + 1)) := by
    simp [qPochhammer_succ, pow_succ']
  rw [qPochhammer_succ, hqq]
  field [hqn, hq1]

theorem norm_mul_pow_lt_one {w q : ℂ} (hw : ‖w‖ < 1) (hq : ‖q‖ < 1) (n : ℕ) :
    ‖w * q ^ n‖ < 1 := by
  rw [norm_mul, norm_pow]
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg w) hw
    (pow_le_one₀ (norm_nonneg q) hq.le)

theorem one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have : ‖w‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
  linarith

theorem qPochhammerInf_ne_zero_of_norm_lt_one {w q : ℂ} (hw : ‖w‖ < 1) (hq : ‖q‖ < 1) :
    qPochhammerInf w q ≠ 0 :=
  qPochhammerInf_ne_zero hq fun n h =>
    (lt_irrefl (1 : ℝ)) <|
      (show ‖w * q ^ n‖ = 1 by rw [← sub_eq_zero.mp h, norm_one]) ▸
        norm_mul_pow_lt_one hw hq n

theorem multipliable_one_sub_mul_pow {w q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => (1 - w * q ^ n) := by
  simpa only [sub_eq_add_neg] using
    multipliable_one_add_of_summable (f := fun n : ℕ => -(w * q ^ n))
      (by simpa only [norm_neg, norm_mul, norm_pow] using
        (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖w‖)

@[dlmf 17.2.iii "exact: finite shifted factorials tend to the infinite product, |q|<1"]
theorem tendsto_qPochhammer {w q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => qPochhammer w q n) atTop (𝓝 (qPochhammerInf w q)) := by
  simpa only [qPochhammer_eq_prod, qPochhammerInf] using
    (multipliable_one_sub_mul_pow (w := w) hq).tendsto_prod_tprod_nat

theorem one_sub_mul_pow_ne_zero_of_norm {w q : ℂ} (hw : ‖w‖ < 1) (hq : ‖q‖ < 1)
    (n : ℕ) : 1 - w * q ^ n ≠ 0 := by
  intro h
  exact (lt_irrefl (1 : ℝ)) <|
    (show ‖w * q ^ n‖ = 1 by rw [← sub_eq_zero.mp h, norm_one]) ▸
      norm_mul_pow_lt_one hw hq n

theorem qPochhammer_ne_zero_of_factors {w q : ℂ} (hq : ‖q‖ < 1)
    (hw : ∀ n : ℕ, 1 - w * q ^ n ≠ 0) (n : ℕ) : qPochhammer w q n ≠ 0 := by
  have hinf := qPochhammerInf_ne_zero hq hw
  rw [qPochhammerInf_mul_qPochhammer hq n] at hinf
  exact left_ne_zero_of_mul hinf

theorem qPochhammerInf_shift_ne_zero {w q : ℂ} (hq : ‖q‖ < 1)
    (hw : ∀ n : ℕ, 1 - w * q ^ n ≠ 0) (n : ℕ) :
    qPochhammerInf (w * q ^ n) q ≠ 0 :=
  qPochhammerInf_ne_zero hq fun k h => hw (n + k) <| by
    simpa [mul_assoc, pow_add] using h

theorem qPochhammer_eq_div_inf {w q : ℂ} (hq : ‖q‖ < 1)
    (hw : ∀ n : ℕ, 1 - w * q ^ n ≠ 0) (n : ℕ) :
    qPochhammer w q n =
      qPochhammerInf w q / qPochhammerInf (w * q ^ n) q :=
  eq_div_of_mul_eq (qPochhammerInf_shift_ne_zero hq hw n)
    (qPochhammerInf_mul_qPochhammer hq n).symm

/-- Coefficient identity for the Heine generating function. -/
theorem q_binomial_coeff_sub {a q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    let c := fun k : ℕ => qPochhammer a q k / qPochhammer q q k
    c (n + 1) - c n = c (n + 1) * q ^ (n + 1) - a * c n * q ^ n := by
  intro c
  have hqn := qPochhammer_self_ne_zero hq n
  have hq1 := qPochhammerInf_pow_succ_ne_zero hq n
  have hmul : c (n + 1) * (1 - q ^ (n + 1)) = c n * (1 - a * q ^ n) := by
    dsimp [c]
    rw [q_binomial_coeff_succ a q n hqn hq1]
    field [hq1]
  have hdiff :
      c (n + 1) - c n - (c (n + 1) * q ^ (n + 1) - a * c n * q ^ n) =
        c (n + 1) * (1 - q ^ (n + 1)) - c n * (1 - a * q ^ n) := by
    ring
  rw [← sub_eq_zero, hdiff, hmul, sub_self]

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

/-- The `q`-binomial theorem (AAR §10.2, Heine):
`(az;q)_∞ / (z;q)_∞ = ∑ (a;q)_n z^n / (q;q)_n` for `|z| < 1` and `|q| < 1`. -/
@[dlmf 17.2.E37, dlmf 17.5.E2 "exact: one-phi-zero in |z|<1; local general-notation adapter proved"]
theorem q_binomial_theorem {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    qPochhammerInf (a * z) q / qPochhammerInf z q =
      ∑' n : ℕ, qPochhammer a q n / qPochhammer q q n * z ^ n := by
  let c : ℕ → ℂ := fun n => qPochhammer a q n / qPochhammer q q n
  let G : ℂ → ℂ := fun w => ∑' n : ℕ, c n * w ^ n
  have hc0 : c 0 = 1 := by simp [c]
  have hsum {w : ℂ} (hw : ‖w‖ < 1) : Summable fun n : ℕ => c n * w ^ n := by
    simpa [c] using summable_q_binomial_series (a := a) hq hw
  have hqz {w : ℂ} (hw : ‖w‖ < 1) : ‖q * w‖ < 1 := by
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg q) hq hw.le
  -- Functional equation `(1-w) G(w) = (1-aw) G(qw)`.
  have hFE {w : ℂ} (hw : ‖w‖ < 1) : (1 - w) * G w = (1 - a * w) * G (q * w) := by
    have hS : HasSum (fun n : ℕ => c n * w ^ n) (G w) := (hsum hw).hasSum
    have hS' : HasSum (fun n : ℕ => c n * (q * w) ^ n) (G (q * w)) := (hsum (hqz hw)).hasSum
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
  have hwq (n : ℕ) : ‖q ^ n * z‖ < 1 := by
    rw [norm_mul, norm_pow, mul_comm]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg z) hz
      (pow_le_one₀ (norm_nonneg q) hq.le)
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
      have hcomm1 : 1 - q ^ n * z = 1 - z * q ^ n := by ring
      have hcomm2 : 1 - a * (q ^ n * z) = 1 - a * z * q ^ n := by ring
      rw [hcomm1, hcomm2] at hFE'
      calc
        G z * qPochhammer z q (n + 1)
            = G z * (qPochhammer z q n * (1 - z * q ^ n)) := by rw [qPochhammer_succ]
        _ = (G z * qPochhammer z q n) * (1 - z * q ^ n) := by ring
        _ = (qPochhammer (a * z) q n * G (q ^ n * z)) * (1 - z * q ^ n) := by rw [ih]
        _ = qPochhammer (a * z) q n * ((1 - z * q ^ n) * G (q ^ n * z)) := by ring
        _ = qPochhammer (a * z) q n *
            ((1 - a * z * q ^ n) * G (q ^ (n + 1) * z)) := by rw [hFE']
        _ = (qPochhammer (a * z) q n * (1 - a * z * q ^ n)) * G (q ^ (n + 1) * z) := by
          ring
        _ = qPochhammer (a * z) q (n + 1) * G (q ^ (n + 1) * z) := by
          rw [qPochhammer_succ]
  have hG : Tendsto (fun n : ℕ => G (q ^ n * z)) atTop (𝓝 1) := by
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

/-- The `q`-gamma function (AAR §10.3):
`Γ_q(x) = (q;q)_∞ / (q^x;q)_∞ · (1-q)^{1-x}`. -/
@[dlmf 5.18.E4]
def qGamma (q x : ℂ) : ℂ :=
  qPochhammerInf q q / qPochhammerInf (q ^ x) q * (1 - q) ^ (1 - x)

/-- `Γ_q(1) = 1` for `|q| < 1`, as in AAR §10.3, pp. 493–494. -/
@[dlmf 5.18.E5]
theorem qGamma_one {q : ℂ} (hq : ‖q‖ < 1) :
    qGamma q 1 = 1 := by
  have hp : qPochhammerInf q q ≠ 0 := qPochhammerInf_ne_zero hq fun n h => by
    have hn : ‖q * q ^ n‖ < 1 := by
      rw [← pow_succ', norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero n)
    rw [← sub_eq_zero.mp h, norm_one] at hn
    exact (lt_irrefl 1) hn
  simp [qGamma, hp]

/-- The `q`-gamma recurrence from AAR §10.3, p. 494, away from the poles described
after (10.3.3), p. 493. The condition `hx` excludes exactly the zero factors of
`(q^x;q)_∞`. The nonzero condition on `q` makes the complex powers and the
pole description involving `log q` well-defined. -/
@[dlmf 5.18.E7]
theorem qGamma_add_one {q x : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (hx : ∀ n : ℕ, q ^ (x + n) ≠ 1) :
    qGamma q (x + 1) = (1 - q ^ x) / (1 - q) * qGamma q x := by
  have hb : 1 - q ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at hq
    exact (lt_irrefl 1) hq
  have hp : qPochhammerInf (q ^ x) q ≠ 0 := qPochhammerInf_ne_zero hq fun n h => by
    apply hx n
    rw [cpow_add _ _ hq0, cpow_natCast]
    exact (sub_eq_zero.mp h).symm
  have hshift : qPochhammerInf (q ^ x) q =
      (1 - q ^ x) * qPochhammerInf (q ^ (x + 1)) q := by
    simpa only [cpow_add _ _ hq0, cpow_one] using
      (qPochhammerInf_shift (a := q ^ x) hq)
  have hfactor : 1 - q ^ x ≠ 0 := by
    intro h
    exact hp (by rw [hshift, h, zero_mul])
  have hp1 : qPochhammerInf (q ^ (x + 1)) q ≠ 0 := by
    intro h
    exact hp (by rw [hshift, h, mul_zero])
  have hpow : (1 - q) ^ (1 - (x + 1)) = (1 - q) ^ (1 - x) / (1 - q) := by
    rw [show 1 - (x + 1) = (1 - x) - 1 by ring, cpow_sub _ _ hb, cpow_one]
  unfold qGamma
  rw [hpow, hshift]
  field [hb, hfactor, hp1]

end DLMF.QSeries
