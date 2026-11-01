/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.Pochhammer
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Basic properties of the `q`-Pochhammer symbols and of `q`-gamma

This file proves the basic properties of the finite and infinite `q`-Pochhammer symbols
(DLMF §17.2(i)–(iii)) and the functional equation of the `q`-gamma function (DLMF §5.18).

## Main results

* `qPochhammer_zero`, `qPochhammer_succ`, `qPochhammer_one`, `qPochhammer_zero_param`:
  unfolding and special values.
* `qPochhammer_eq_prod`: `(a;q)_n = ∏_{k<n} (1 - aqᵏ)` (DLMF 17.2.1).
* `qPochhammer_add`: `(a;q)_{m+k} = (a;q)_m (aq^m;q)_k`.
* `multipliable_one_sub_mul_pow`, `tendsto_qPochhammer`: `(w;q)_n → (w;q)_∞` for `|q| < 1`
  (DLMF §17.2(iii)).
* `qPochhammerInf_shift`, `qPochhammerInf_mul_qPochhammer`, `qPochhammer_eq_div_inf`:
  relations between the finite and infinite products.
* `qPochhammerInf_ne_zero`, `qPochhammer_self_ne_zero`: nonvanishing.
* `jacksonIntegral_one`: `∫₀¹ 1 d_q t = 1` for `|q| < 1`.
* `qGamma_one`, `qGamma_add_one`: `Γ_q(1) = 1` and the recurrence of `Γ_q`
  (DLMF 5.18.5, 5.18.7).

## Implementation notes

The `q`-binomial theorem is in `DLMF.QSeries.Pochhammer`.
-/

@[expose] public section

open Complex Finset Filter
open scoped Topology Real

noncomputable section

namespace DLMF.QSeries

/-- `(a;q)_0 = 1`. -/
@[simp]
theorem qPochhammer_zero (a q : ℂ) : qPochhammer a q 0 = 1 := rfl

/-- `(a;q)_{n+1} = (a;q)_n (1 - a qⁿ)`. -/
theorem qPochhammer_succ (a q : ℂ) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer a q n * (1 - a * q ^ n) :=
  rfl

/-- `(a;q)_{m+k} = (a;q)_m (aq^m;q)_k`. -/
theorem qPochhammer_add (a q : ℂ) (m k : ℕ) :
    qPochhammer a q (m + k) = qPochhammer a q m * qPochhammer (a * q ^ m) q k := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, qPochhammer_succ, ih, qPochhammer_succ, pow_add]; ring

/-- `(a;q)_1 = 1 - a`. -/
theorem qPochhammer_one (a q : ℂ) : qPochhammer a q 1 = 1 - a := by
  simp [qPochhammer_succ]

/-- `(a;q)_n = ∏_{k<n} (1 - a qᵏ)` (DLMF 17.2.1). -/
@[dlmf 17.2.E1]
theorem qPochhammer_eq_prod (a q : ℂ) (n : ℕ) :
    qPochhammer a q n = ∏ k ∈ range n, (1 - a * q ^ k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [qPochhammer_succ, ih, prod_range_succ]

/-- `(q^{-n};q)_k = 0` for `k > n`. -/
theorem qPochhammer_recip_pow_eq_zero {q : ℂ} (hq0 : q ≠ 0) {n k : ℕ} (hk : n < k) :
    qPochhammer (q ^ n)⁻¹ q k = 0 := by
  rw [qPochhammer_eq_prod]
  exact prod_eq_zero (mem_range.mpr hk) (by field)

/-- `(0;q)_n = 1`. -/
@[simp]
theorem qPochhammer_zero_param (q : ℂ) (n : ℕ) : qPochhammer 0 q n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [qPochhammer_succ, ih]

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

/-- For `|q| < 1`, `(q;q)_n ≠ 0`. -/
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

/-- For `|q| < 1`, `1 - q^{n+1} ≠ 0`. -/
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

/-- `|w qⁿ| < 1` when `|w| < 1` and `|q| < 1`. -/
theorem norm_mul_pow_lt_one {w q : ℂ} (hw : ‖w‖ < 1) (hq : ‖q‖ < 1) (n : ℕ) :
    ‖w * q ^ n‖ < 1 := by
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_right (norm_nonneg w)
    (pow_le_one₀ (norm_nonneg q) hq.le)).trans_lt hw

/-- `1 - w ≠ 0` when `|w| < 1`. -/
theorem one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have : ‖w‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
  linarith

/-- `(w;q)_∞ ≠ 0` when `|w| < 1` and `|q| < 1`. -/
theorem qPochhammerInf_ne_zero_of_norm_lt_one {w q : ℂ} (hw : ‖w‖ < 1) (hq : ‖q‖ < 1) :
    qPochhammerInf w q ≠ 0 :=
  qPochhammerInf_ne_zero hq fun n h =>
    (lt_irrefl (1 : ℝ)) <|
      (show ‖w * q ^ n‖ = 1 by rw [← sub_eq_zero.mp h, norm_one]) ▸
        norm_mul_pow_lt_one hw hq n

/-- For `|q| < 1` the product `∏ (1 - w qⁿ)` is multipliable. -/
theorem multipliable_one_sub_mul_pow {w q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => (1 - w * q ^ n) := by
  simpa only [sub_eq_add_neg] using
    multipliable_one_add_of_summable (f := fun n : ℕ => -(w * q ^ n))
      (by simpa only [norm_neg, norm_mul, norm_pow] using
        (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖w‖)

/-- For `|q| < 1`, `(w;q)_n → (w;q)_∞` as `n → ∞`. -/
@[dlmf 17.2.iii "exact: finite shifted factorials tend to the infinite product, |q|<1"]
theorem tendsto_qPochhammer {w q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => qPochhammer w q n) atTop (𝓝 (qPochhammerInf w q)) := by
  simpa only [qPochhammer_eq_prod, qPochhammerInf] using
    (multipliable_one_sub_mul_pow (w := w) hq).tendsto_prod_tprod_nat

/-- `1 - w qⁿ ≠ 0` when `|w| < 1` and `|q| < 1`. -/
theorem one_sub_mul_pow_ne_zero_of_norm {w q : ℂ} (hw : ‖w‖ < 1) (hq : ‖q‖ < 1)
    (n : ℕ) : 1 - w * q ^ n ≠ 0 := by
  intro h
  exact (lt_irrefl (1 : ℝ)) <|
    (show ‖w * q ^ n‖ = 1 by rw [← sub_eq_zero.mp h, norm_one]) ▸
      norm_mul_pow_lt_one hw hq n

/-- If no factor `1 - w qⁿ` vanishes, then `(w;q)_n ≠ 0`. -/
theorem qPochhammer_ne_zero_of_factors {w q : ℂ} (hq : ‖q‖ < 1)
    (hw : ∀ n : ℕ, 1 - w * q ^ n ≠ 0) (n : ℕ) : qPochhammer w q n ≠ 0 := by
  have hinf := qPochhammerInf_ne_zero hq hw
  rw [qPochhammerInf_mul_qPochhammer hq n] at hinf
  exact left_ne_zero_of_mul hinf

/-- If no factor `1 - w qⁿ` vanishes and `|q| < 1`, then `(w qⁿ;q)_∞ ≠ 0`. -/
theorem qPochhammerInf_shift_ne_zero {w q : ℂ} (hq : ‖q‖ < 1)
    (hw : ∀ n : ℕ, 1 - w * q ^ n ≠ 0) (n : ℕ) :
    qPochhammerInf (w * q ^ n) q ≠ 0 :=
  qPochhammerInf_ne_zero hq fun k h => hw (n + k) <| by
    simpa [mul_assoc, pow_add] using h

/-- `(w;q)_n = (w;q)_∞ / (w qⁿ;q)_∞` for `|q| < 1` when no factor vanishes. -/
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
