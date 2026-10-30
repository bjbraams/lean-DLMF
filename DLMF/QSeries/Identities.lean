/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.Series
public import DLMF.QSeries.QBinomial
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Triple product, Ramanujan `₁ψ₁`, basic hypergeometric series, `q`-beta (AAR §§10.4–10.12)

Mathlib has Jacobi theta functions, the Mellin transform, and the arithmetic theorems on
sums of two and four squares. It does not have the Jacobi triple product as a `q`-Pochhammer
identity, Ramanujan's `₁ψ₁`, or basic hypergeometric series `ᵣφₛ`.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.QSeries

namespace TripleProduct

/-! ### Helpers for the Jacobi triple product

The proof follows AAR §10.4: Cauchy's finite `q`-binomial theorem at `x = z q^{-m}` gives
`(q/z;q)_m (z;q)_m = ∑_{|n|≤m} [2m, m+n]_q (-1)^n q^{n(n-1)/2} z^n`, and Tannery's theorem
passes to the limit `m → ∞` using `[2m, m+n]_q → 1/(q;q)_∞` and a uniform bound on `[n k]_q`. -/

open Finset Filter
open scoped Topology

/-- `2 tri n = n (n - 1)`: the integer division in `tri` is exact. -/
theorem tri_mul_two (n : ℤ) : tri n * 2 = n * (n - 1) :=
  Int.ediv_mul_cancel (even_iff_two_dvd.mp (Int.even_mul_pred_self n))

/-- `q^{n(n-1)/2}` as a complex power equals the integer power `q^{tri n}`. -/
theorem cpow_tri (q : ℂ) (n : ℤ) :
    q ^ ((n : ℂ) * ((n : ℂ) - 1) / 2) = q ^ tri n := by
  have h : ((tri n : ℤ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
    rw [eq_div_iff two_ne_zero]; exact_mod_cast tri_mul_two n
  rw [← h, cpow_intCast]

/-- `(z q^{-m};q)_m q^{C(m+1,2)} = (-z)^m (q/z;q)_m`: reversing a finite `q`-shifted
factorial. -/
theorem qPochhammer_shift_down {q z : ℂ} (hq : q ≠ 0) (hz : z ≠ 0) (m : ℕ) :
    qPochhammer (z / q ^ m) q m * q ^ (m + 1).choose 2 = (-z) ^ m * qPochhammer (q / z) q m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hc : (m + 2).choose 2 = (m + 1).choose 2 + (m + 1) := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    have hx : z / q ^ (m + 1) * q = z / q ^ m := by field_simp; ring
    rw [qPochhammer_succ', hx, hc, qPochhammer_succ, pow_add]
    have hqm : q ^ (m + 1) ≠ 0 := pow_ne_zero _ hq
    linear_combination (norm := (field_simp; ring)) ((1 - z / q ^ (m + 1)) * q ^ (m + 1)) * ih

/-- `C(k,2) + C(m+1,2) - m k = tri (k - m)`. -/
theorem tri_sub_cast (k m : ℕ) :
    ((k.choose 2 : ℕ) : ℤ) + ((m + 1).choose 2 : ℕ) - (m : ℤ) * k = tri ((k : ℤ) - m) := by
  apply Int.cast_injective (α := ℚ)
  have h := tri_mul_two ((k : ℤ) - m)
  have h' : ((tri ((k : ℤ) - m) : ℤ) : ℚ) = ((k : ℚ) - m) * ((k : ℚ) - m - 1) / 2 := by
    rw [eq_div_iff two_ne_zero]; exact_mod_cast h
  push_cast
  rw [h', Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  ring

/-- Shifting the summation index by `m` in the finite triple product turns the `q`-binomial
summand into `(-z)^m` times the triple-product term at `k - m`. -/
theorem term_shift {q z : ℂ} (hq : q ≠ 0) (hz : z ≠ 0) (k m : ℕ) :
    (-1 : ℂ) ^ k * q ^ k.choose 2 * (z / q ^ m) ^ k * q ^ (m + 1).choose 2 =
      (-z) ^ m * term q z ((k : ℤ) - m) := by
  have hQ : q ^ k.choose 2 * q ^ (m + 1).choose 2 / q ^ (m * k) = q ^ tri ((k : ℤ) - m) := by
    rw [← tri_sub_cast, zpow_sub₀ hq, zpow_add₀ hq, ← Nat.cast_mul, zpow_natCast, zpow_natCast,
      zpow_natCast]
  have h1 : (-1 : ℂ) ^ m * (-1 : ℂ) ^ ((k : ℤ) - m) = (-1) ^ k := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num), ← zpow_natCast]; congr 1; ring
  have h2 : z ^ m * z ^ ((k : ℤ) - m) = z ^ k := by
    rw [← zpow_natCast, ← zpow_add₀ hz, ← zpow_natCast]; congr 1; ring
  rw [term, neg_pow z m, ← hQ]
  calc (-1 : ℂ) ^ k * q ^ k.choose 2 * (z / q ^ m) ^ k * q ^ (m + 1).choose 2
      = (-1) ^ k * z ^ k * (q ^ k.choose 2 * q ^ (m + 1).choose 2 / q ^ (m * k)) := by
        rw [div_pow, pow_mul]; field_simp
    _ = _ := by rw [← h1, ← h2]; ring

/-- The finite Jacobi triple product: `(q/z;q)_m (z;q)_m = ∑_{|n| ≤ m} [2m, m+n]_q (-1)ⁿ
q^{n(n-1)/2} zⁿ`. -/
theorem finite_jtp {q z : ℂ} (hq : q ≠ 0) (hz : z ≠ 0) (m : ℕ) :
    qPochhammer (q / z) q m * qPochhammer z q m =
      ∑ n ∈ Icc (-(m : ℤ)) m, qBinom q (2 * m) ((m : ℤ) + n).toNat * term q z n := by
  have hsplit : qPochhammer (z / q ^ m) q (2 * m) =
      qPochhammer (z / q ^ m) q m * qPochhammer z q m := by
    rw [two_mul, qPochhammer_add]; congr 2; field_simp
  have hre : ∑ n ∈ Icc (-(m : ℤ)) m, qBinom q (2 * m) ((m : ℤ) + n).toNat * term q z n =
      ∑ k ∈ range (2 * m + 1), qBinom q (2 * m) k * term q z ((k : ℤ) - m) := by
    refine Finset.sum_nbij' (fun n => ((m : ℤ) + n).toNat) (fun k => (k : ℤ) - m)
      ?_ ?_ ?_ ?_ ?_
    · intro n hn; simp only [mem_Icc, mem_range] at hn ⊢; omega
    · intro k hk; simp only [mem_Icc, mem_range] at hk ⊢; omega
    · intro n hn; simp only [mem_Icc] at hn ⊢; omega
    · intro k _; simp
    · intro n hn
      simp only [mem_Icc] at hn
      congr 2; omega
  have hmz : (-z) ^ m ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hz)
  apply mul_left_cancel₀ hmz
  rw [hre, mul_sum]
  calc (-z) ^ m * (qPochhammer (q / z) q m * qPochhammer z q m)
      = qPochhammer (z / q ^ m) q (2 * m) * q ^ (m + 1).choose 2 := by
        rw [hsplit]
        linear_combination (-qPochhammer z q m) * qPochhammer_shift_down hq hz m
    _ = _ := by
        rw [qPochhammer_eq_sum_qBinom, sum_mul]
        refine sum_congr rfl fun k _ => ?_
        linear_combination qBinom q (2 * m) k * term_shift hq hz k m

/-- `0 < 1 - r^{j+1}` for `0 ≤ r < 1`. -/
theorem one_sub_pow_succ_pos {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (j : ℕ) : 0 < 1 - r ^ (j + 1) :=
  sub_pos.mpr (pow_lt_one₀ h0 h1 (Nat.succ_ne_zero j))

/-- `dprod r k ≥ 0` for `0 ≤ r < 1`. -/
theorem dprod_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (k : ℕ) : 0 ≤ dprod r k :=
  prod_nonneg fun j _ => (inv_pos.mpr (one_sub_pow_succ_pos h0 h1 j)).le

/-- For `|q| < 1`, `‖[n k]_q‖ ≤ ∏_{j<k} (1 - |q|^{j+1})⁻¹`, uniformly in `n`. -/
theorem norm_qBinom_le {q : ℂ} (hq : ‖q‖ < 1) (n k : ℕ) : ‖qBinom q n k‖ ≤ dprod ‖q‖ k := by
  have h0 := norm_nonneg q
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [dprod]
    | succ k => simpa using dprod_nonneg h0 hq (k + 1)
  | succ n ih =>
    cases k with
    | zero => simp [dprod]
    | succ k =>
      have hpos := one_sub_pow_succ_pos h0 hq k
      have hd : dprod ‖q‖ (k + 1) = dprod ‖q‖ k * (1 - ‖q‖ ^ (k + 1))⁻¹ := prod_range_succ _ _
      rw [qBinom_succ_succ]
      calc ‖qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)‖
          ≤ ‖qBinom q n k‖ + ‖q‖ ^ (k + 1) * ‖qBinom q n (k + 1)‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_pow]
        _ ≤ dprod ‖q‖ k + ‖q‖ ^ (k + 1) * dprod ‖q‖ (k + 1) :=
            add_le_add (ih k) (mul_le_mul_of_nonneg_left (ih (k + 1)) (by positivity))
        _ = dprod ‖q‖ (k + 1) := by rw [hd]; field_simp; ring

/-- For `0 ≤ r < 1`, `dprod r k ≤ exp(r/(1-r)²)`, uniformly in `k`. -/
theorem dprod_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (k : ℕ) :
    dprod r k ≤ Real.exp (r / (1 - r) ^ 2) := by
  have hr1 : 0 < 1 - r := sub_pos.mpr h1
  have hfac (j : ℕ) : (1 - r ^ (j + 1))⁻¹ ≤ Real.exp (r ^ (j + 1) / (1 - r)) := by
    have hx := one_sub_pow_succ_pos h0 h1 j
    have hxr : r ^ (j + 1) ≤ r := pow_le_of_le_one h0 h1.le (Nat.succ_ne_zero j)
    calc (1 - r ^ (j + 1))⁻¹ = r ^ (j + 1) / (1 - r ^ (j + 1)) + 1 := by field_simp; ring
      _ ≤ Real.exp (r ^ (j + 1) / (1 - r ^ (j + 1))) := Real.add_one_le_exp _
      _ ≤ Real.exp (r ^ (j + 1) / (1 - r)) := by
        gcongr
  calc dprod r k ≤ ∏ j ∈ range k, Real.exp (r ^ (j + 1) / (1 - r)) :=
        prod_le_prod₀ (fun j _ => (inv_pos.mpr (one_sub_pow_succ_pos h0 h1 j)).le)
          fun j _ => hfac j
    _ = Real.exp (∑ j ∈ range k, r ^ (j + 1) / (1 - r)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (r / (1 - r) ^ 2) := by
      gcongr
      have hg : ∑ j ∈ range k, r ^ j ≤ (1 - r)⁻¹ := by
        have hm : (1 - r)⁻¹ * (r - 1) = -1 := by field_simp; ring
        rw [geom_sum_eq h1.ne, div_le_iff_of_neg (by linarith), hm]
        linarith [pow_nonneg h0 k]
      calc ∑ j ∈ range k, r ^ (j + 1) / (1 - r) = r / (1 - r) * ∑ j ∈ range k, r ^ j := by
            rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; rw [pow_succ]; ring
        _ ≤ r / (1 - r) * (1 - r)⁻¹ := by gcongr
        _ = r / (1 - r) ^ 2 := by field_simp

/-- For `|q| < 1`, the central `q`-binomial `[2m, m+n]_q` tends to `1/(q;q)_∞` as `m → ∞`. -/
theorem tendsto_qBinom_center {q : ℂ} (hq : ‖q‖ < 1) (n : ℤ) :
    Tendsto (fun m : ℕ => qBinom q (2 * m) ((m : ℤ) + n).toNat) atTop
      (𝓝 (qPochhammerInf q q)⁻¹) := by
  have hP := qPochhammerInf_ne_zero_of_norm_lt_one hq hq
  have hlim (f : ℕ → ℕ) (hf : ∀ b : ℕ, ∀ m : ℕ, b + n.natAbs ≤ m → b ≤ f m) :
      Tendsto (fun m => qPochhammer q q (f m)) atTop (𝓝 (qPochhammerInf q q)) :=
    (tendsto_qPochhammer hq).comp
      (tendsto_atTop_atTop.mpr fun b => ⟨b + n.natAbs, fun m hm => hf b m hm⟩)
  have h2 := hlim (fun m => 2 * m) (fun b m hm => by omega)
  have ha := hlim (fun m => ((m : ℤ) + n).toNat) (fun b m hm => by omega)
  have hb := hlim (fun m => ((m : ℤ) - n).toNat) (fun b m hm => by omega)
  have hlim' := h2.div (ha.mul hb) (mul_ne_zero hP hP)
  rw [show qPochhammerInf q q / (qPochhammerInf q q * qPochhammerInf q q) =
    (qPochhammerInf q q)⁻¹ by field_simp] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [eventually_ge_atTop n.natAbs] with m hm
  have hab : ((m : ℤ) + n).toNat + ((m : ℤ) - n).toNat = 2 * m := by omega
  have h := qBinom_mul_qPochhammer q ((m : ℤ) + n).toNat ((m : ℤ) - n).toNat
  rw [hab] at h
  simp only [Pi.div_apply]
  rw [← h]
  field_simp [qPochhammer_self_ne_zero hq]

/-- The norm of the triple-product term equals the norm of the corresponding
`jacobiTheta₂_term` at the matching `z` and `τ`. -/
theorem norm_term_eq {q z : ℂ} (hq : q ≠ 0) (hz : z ≠ 0) (n : ℤ) :
    ‖term q z n‖ = ‖jacobiTheta₂_term n
      (((-(Real.log ‖z‖ - Real.log ‖q‖ / 2) / (2 * π) : ℝ) : ℂ) * I)
      (((-Real.log ‖q‖ / (2 * π) : ℝ) : ℂ) * I)‖ := by
  have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hs : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have ht : ((tri n : ℤ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [eq_div_iff two_ne_zero]; exact_mod_cast tri_mul_two n
  rw [norm_jacobiTheta₂_term, term, norm_mul, norm_mul, norm_zpow, norm_zpow, norm_zpow, norm_neg,
    norm_one, one_zpow, one_mul, ← Real.rpow_intCast, ← Real.rpow_intCast,
    Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hs, ← Real.exp_add, ht]
  congr 1
  simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero, mul_one]
  field_simp
  ring

/-- For `0 < |q| < 1` and `z ≠ 0` the triple-product terms are absolutely summable over `ℤ`. -/
theorem summable_norm_term {q z : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hz : z ≠ 0) :
    Summable fun n : ℤ => ‖term q z n‖ := by
  have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hL : Real.log ‖q‖ < 0 := Real.log_neg hr hq
  simp_rw [norm_term_eq hq0 hz]
  refine summable_norm_iff.mpr ((summable_jacobiTheta₂_term_iff _ _).mpr ?_)
  simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero, mul_one]
  have : 0 < 2 * π := by positivity
  exact div_pos (neg_pos.mpr hL) this

/-- The Jacobi triple product for `0 < |q| < 1`, `z ≠ 0`:
`(q/z;q)_∞ (z;q)_∞ = (q;q)_∞⁻¹ ∑_{n ∈ ℤ} (-1)ⁿ q^{n(n-1)/2} zⁿ`. -/
theorem jtp_ne_zero {q z : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hz : z ≠ 0) :
    qPochhammerInf (q / z) q * qPochhammerInf z q =
      (qPochhammerInf q q)⁻¹ * ∑' n : ℤ, term q z n := by
  classical
  set C := Real.exp (‖q‖ / (1 - ‖q‖) ^ 2)
  let f : ℕ → ℤ → ℂ := fun m n =>
    if n ∈ Icc (-(m : ℤ)) m then qBinom q (2 * m) ((m : ℤ) + n).toNat * term q z n else 0
  have hsum (m : ℕ) : ∑' n, f m n = qPochhammer (q / z) q m * qPochhammer z q m := by
    rw [finite_jtp hq0 hz m, tsum_eq_sum (s := Icc (-(m : ℤ)) m)]
    · exact sum_congr rfl fun n hn => by simp only [f, hn, ↓reduceIte]
    · intro n hn; simp only [f, hn, ↓reduceIte]
  have hT := tendsto_tsum_of_dominated_convergence (f := f)
    (g := fun n => (qPochhammerInf q q)⁻¹ * term q z n) (𝓕 := atTop)
    ((summable_norm_term hq hq0 hz).mul_left C) (fun n => ?_) ?_
  · simp_rw [hsum] at hT
    rw [tsum_mul_left] at hT
    exact tendsto_nhds_unique
      (((tendsto_qPochhammer hq).mul (tendsto_qPochhammer hq))) hT
  · refine ((tendsto_qBinom_center hq n).mul_const (term q z n)).congr' ?_
    filter_upwards [eventually_ge_atTop n.natAbs] with m hm
    have hn : n ∈ Icc (-(m : ℤ)) m := by simp only [mem_Icc]; omega
    simp only [f, hn, ↓reduceIte]
  · refine Eventually.of_forall fun m n => ?_
    simp only [f]
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        ((norm_qBinom_le hq _ _).trans (dprod_le (norm_nonneg q) hq _)) (norm_nonneg _)
    · simp only [norm_zero]; positivity

/-- `(a;0)_∞ = 1 - a`. -/
theorem qPochhammerInf_zero_right (a : ℂ) : qPochhammerInf a 0 = 1 - a := by
  rw [qPochhammerInf, tprod_eq_mulSingle 0 fun k hk => by simp [zero_pow hk]]
  simp

/-- `tri n ≠ 0` unless `n = 0` or `n = 1`. -/
theorem tri_ne_zero {n : ℤ} (h0 : n ≠ 0) (h1 : n ≠ 1) : tri n ≠ 0 := by
  intro h
  have := tri_mul_two n
  rw [h, zero_mul] at this
  rcases mul_eq_zero.mp this.symm with h | h
  · exact h0 h
  · exact h1 (by linarith)

/-- At `q = 0` the triple-product series reduces to `1 - z`. -/
theorem jtp_zero {z : ℂ} : ∑' n : ℤ, term 0 z n = 1 - z := by
  rw [tsum_eq_sum (s := {0, 1})]
  · rw [sum_pair (by norm_num)]
    simp [term, show tri 0 = 0 by decide, show tri 1 = 0 by decide]
    ring
  · intro n hn
    simp only [mem_insert, mem_singleton, not_or] at hn
    simp [term, zero_zpow _ (tri_ne_zero hn.1 hn.2)]

end TripleProduct

open DLMF.QSeries.TripleProduct in
/-- Jacobi triple product (AAR §10.4):
`(q;q)_∞ (z;q)_∞ (q/z;q)_∞ = ∑_{n∈ℤ} (-1)^n q^{n(n-1)/2} z^n`. -/
@[dlmf 17.8.E1]
theorem jacobi_triple_product {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    qPochhammerInf q q * qPochhammerInf z q * qPochhammerInf (q / z) q =
      ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (n - 1) / 2 : ℂ) * z ^ n := by
  have hR : (fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (n - 1) / 2 : ℂ) * z ^ n) = term q z := by
    funext n; rw [term, cpow_tri]
  rw [hR]
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [jtp_zero, qPochhammerInf_zero_right, qPochhammerInf_zero_right,
      qPochhammerInf_zero_right]
    simp
  · have hP := qPochhammerInf_ne_zero_of_norm_lt_one hq hq
    rw [mul_assoc, mul_comm (qPochhammerInf z q), jtp_ne_zero hq hq0 hz]
    field_simp

open DLMF.QSeries.TripleProduct in
/-- The triple product gives the product expansion of `jacobiTheta` (AAR §10.7). -/
theorem jacobiTheta_eq_qPochhammer {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ =
      qPochhammerInf (cexp (2 * π * I * τ)) (cexp (2 * π * I * τ)) *
        qPochhammerInf (-cexp (π * I * τ)) (cexp (2 * π * I * τ)) *
        qPochhammerInf (-cexp (π * I * τ)) (cexp (2 * π * I * τ)) := by
  set Q := cexp (2 * π * I * τ) with hQ
  set E := cexp (π * I * τ) with hE
  have hQE : Q = E ^ 2 := by rw [hQ, hE, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hEne : E ≠ 0 := Complex.exp_ne_zero _
  have hQn : ‖Q‖ < 1 := by
    rw [hQ, Complex.norm_exp]
    simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, I_re,
      mul_im, zero_mul, add_zero, I_im, mul_one, zero_sub]
    simpa using Real.exp_lt_exp.mpr (show -(2 * π * τ.im) < 0 by nlinarith [Real.pi_pos])
  have hdiv : Q / -E = -E := by rw [hQE]; field_simp
  have h := jacobi_triple_product hQn (neg_ne_zero.mpr hEne)
  rw [hdiv] at h
  rw [h, jacobiTheta]
  refine tsum_congr fun n => ?_
  have ht : ((tri n : ℤ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
    rw [eq_div_iff two_ne_zero]; exact_mod_cast tri_mul_two n
  rw [cpow_tri, neg_eq_neg_one_mul E, mul_zpow, ← mul_assoc, mul_assoc ((-1 : ℂ) ^ n),
    mul_comm (Q ^ tri n), ← mul_assoc, ← mul_zpow]
  rw [hQ, hE, ← Complex.exp_int_mul, ← Complex.exp_int_mul,
    show ((-1 : ℂ) * -1) = 1 by norm_num, one_zpow, one_mul, ← Complex.exp_add, ht]
  congr 1
  ring

/-- At a natural index `qPochhammerInt` is the ordinary `q`-shifted factorial. -/
@[simp] theorem qPochhammerInt_natCast (a q : ℂ) (n : ℕ) :
    qPochhammerInt a q n = qPochhammer a q n := rfl

/-- At the index `-(n+1)`, `(a;q)_{-(n+1)} = 1/(a q^{-(n+1)};q)_{n+1}` (AAR (10.5.2)). -/
@[simp] theorem qPochhammerInt_negSucc (a q : ℂ) (n : ℕ) :
    qPochhammerInt a q (Int.negSucc n) =
      (qPochhammer (a * q ^ (-(n + 1 : ℤ))) q (n + 1))⁻¹ := rfl

/-- Ramanujan's `₁ψ₁` summation (AAR §10.5). -/
theorem ramanujan_1psi1 {a b q z : ℂ}
    (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (ha : ∀ k : ℤ, a * q ^ k ≠ 1) (hb : ∀ k : ℤ, b * q ^ k ≠ 1)
    (hz : ‖b / a‖ < ‖z‖ ∧ ‖z‖ < 1) :
    (∑' n : ℤ, qPochhammerInt a q n / qPochhammerInt b q n * z ^ n) =
      qPochhammerInf q q * qPochhammerInf (b / a) q * qPochhammerInf (a * z) q *
          qPochhammerInf (q / (a * z)) q /
        (qPochhammerInf b q * qPochhammerInf (q / a) q * qPochhammerInf z q *
          qPochhammerInf (b / (a * z)) q) := by
  sorry

/-- Heine's transformation of `₂φ₁` (AAR §10.10). -/
@[dlmf 17.6.E6 "exact: both actual series disks, nonzero b, and all literal lower exclusions; local notation adapter proved"]
theorem heine_transformation {a b c q z : ℂ}
    (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hb : ‖b‖ < 1) (hb0 : b ≠ 0)
    (hc : ∀ k : ℕ, c * q ^ k ≠ 1) (haz : ∀ k : ℕ, a * z * q ^ k ≠ 1) :
    basicHG [a, b] [c] q z =
      qPochhammerInf b q * qPochhammerInf (a * z) q / (qPochhammerInf c q * qPochhammerInf z q) *
        basicHG [c / b, z] [a * z] q b := by
  let A (n : ℕ) := qPochhammer a q n / qPochhammer q q n
  let B (m : ℕ) := qPochhammer (c / b) q m / qPochhammer q q m
  let K := qPochhammerInf b q / qPochhammerInf c q
  let L := qPochhammerInf (a * z) q / qPochhammerInf z q
  let D (n m : ℕ) := (A n * z ^ n) * (B m * b ^ m) * q ^ (n * m)
  have hcf : ∀ k : ℕ, 1 - c * q ^ k ≠ 0 := fun k => sub_ne_zero.mpr (hc k).symm
  have haf : ∀ k : ℕ, 1 - (a * z) * q ^ k ≠ 0 := fun k => sub_ne_zero.mpr (haz k).symm
  have hbf := one_sub_mul_pow_ne_zero_of_norm hb hq
  have hzf := one_sub_mul_pow_ne_zero_of_norm hz hq
  have hleft (n : ℕ) : qPochhammer b q n / qPochhammer c q n =
      K * ∑' m : ℕ, B m * (b * q ^ n) ^ m := by
    dsimp only [B]
    rw [← q_binomial_theorem hq (norm_mul_pow_lt_one hb hq n)]
    have he : c / b * (b * q ^ n) = c * q ^ n := by field [hb0]
    rw [he]
    dsimp only [K]
    rw [qPochhammerInf_mul_qPochhammer (a := b) hq n,
      qPochhammerInf_mul_qPochhammer (a := c) hq n]
    field [qPochhammer_ne_zero_of_factors hq hcf n,
      qPochhammerInf_shift_ne_zero hq hbf n, qPochhammerInf_shift_ne_zero hq hcf n]
  have hright (m : ℕ) : (∑' n : ℕ, A n * (z * q ^ m) ^ n) =
      L * qPochhammer z q m / qPochhammer (a * z) q m := by
    dsimp only [A]
    rw [← q_binomial_theorem hq (norm_mul_pow_lt_one hz hq m), ← mul_assoc]
    dsimp only [L]
    rw [qPochhammerInf_mul_qPochhammer (a := a * z) hq m,
      qPochhammerInf_mul_qPochhammer (a := z) hq m]
    field [qPochhammer_ne_zero_of_factors hq haf m,
      qPochhammer_ne_zero_of_factors hq hzf m,
      qPochhammerInf_shift_ne_zero hq hzf m]
  have hsumA : Summable (fun n : ℕ => ‖A n * z ^ n‖) :=
    (summable_q_binomial_series (a := a) hq hz).norm
  have hsumB : Summable (fun m : ℕ => ‖B m * b ^ m‖) :=
    (summable_q_binomial_series (a := c / b) hq hb).norm
  have hs : Summable (Function.uncurry D) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun nm => ?_) (hsumA.mul_norm hsumB)
    dsimp only [Function.uncurry, D]
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg q) hq.le)
  have hrow (n : ℕ) : (∑' m : ℕ, D n m) =
      A n * z ^ n * ∑' m : ℕ, B m * (b * q ^ n) ^ m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    dsimp only [D]
    rw [mul_pow, ← pow_mul]
    ring
  have hcol (m : ℕ) : (∑' n : ℕ, D n m) =
      B m * b ^ m * ∑' n : ℕ, A n * (z * q ^ m) ^ n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [D]
    rw [mul_pow, ← pow_mul, Nat.mul_comm m n]
    ring
  have hlhs : basicHG [a, b] [c] q z = K * ∑' n : ℕ, ∑' m : ℕ, D n m := by
    calc
      _ = ∑' n : ℕ, A n * z ^ n * (qPochhammer b q n / qPochhammer c q n) := by
        simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        apply tsum_congr
        intro n
        dsimp only [A]
        ring
      _ = _ := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [hleft, hrow]
        ring
  have hrhs : basicHG [c / b, z] [a * z] q b =
      ∑' m : ℕ, B m * b ^ m * qPochhammer z q m / qPochhammer (a * z) q m := by
    simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    apply tsum_congr
    intro m
    dsimp only [B]
    ring
  rw [hlhs, ← hs.tsum_comm, hrhs, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [hcol, hright]
  dsimp only [K, L]
  ring

/-- The degree-zero `q`-ultraspherical polynomial is `1`. -/
theorem qGegenbauer_zero (beta q x : ℂ) : qGegenbauer beta q 0 x = 1 := by
  simp [qGegenbauer]

/-- Jackson's `q`-beta integral (AAR §10.8). -/
@[dlmf 5.18.E12]
theorem q_beta_integral {a b : ℂ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 < a.re) (hb : 0 < b.re) :
    jacksonIntegral q 1 (fun t =>
        t ^ (a - 1) * qPochhammerInf (q * t) q / qPochhammerInf (q ^ b * t) q) =
      qGamma q a * qGamma q b / qGamma q (a + b) := by
  have hq : ‖(q : ℂ)‖ < 1 := by simpa [abs_of_pos hq0] using hq1
  have hqz : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq0.ne'
  have hpow_norm (s : ℂ) (hs : 0 < s.re) : ‖(q : ℂ) ^ s‖ < 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos hq0]
    exact Real.rpow_lt_one hq0.le hq1 hs
  have hqa := hpow_norm a ha
  have hqb := hpow_norm b hb
  have hqab := hpow_norm (a + b) (by simpa using add_pos ha hb)
  have hA := qPochhammerInf_ne_zero_of_norm_lt_one hqa hq
  have hB := qPochhammerInf_ne_zero_of_norm_lt_one hqb hq
  have hC := qPochhammerInf_ne_zero_of_norm_lt_one hqab hq
  have hQ := qPochhammerInf_ne_zero_of_norm_lt_one hq hq
  have hterm (n : ℕ) :
      ((q : ℂ) ^ n) ^ (a - 1) * qPochhammerInf ((q : ℂ) * q ^ n) q /
          qPochhammerInf ((q : ℂ) ^ b * q ^ n) q * q ^ n =
        (qPochhammerInf q q / qPochhammerInf ((q : ℂ) ^ b) q) *
          (qPochhammer ((q : ℂ) ^ b) q n / qPochhammer q q n * ((q : ℂ) ^ a) ^ n) := by
    have hp : ((q : ℂ) ^ n) ^ (a - 1) * (q : ℂ) ^ n = ((q : ℂ) ^ a) ^ n := by
      rw [← cpow_nat_mul' (by simp [arg_ofReal_of_nonneg hq0.le, Real.pi_pos])
        (by simp [arg_ofReal_of_nonneg hq0.le, Real.pi_nonneg]), cpow_nat_mul,
        cpow_sub _ _ hqz, cpow_one, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hqz)]
    have hN := qPochhammer_self_ne_zero hq n
    have hD := qPochhammerInf_ne_zero_of_norm_lt_one (norm_mul_pow_lt_one hqb hq n) hq
    rw [qPochhammerInf_mul_qPochhammer (a := (q : ℂ)) hq n,
      qPochhammerInf_mul_qPochhammer (a := (q : ℂ) ^ b) hq n]
    have hBn := qPochhammer_ne_zero_of_factors hq
      (one_sub_mul_pow_ne_zero_of_norm hqb hq) n
    linear_combination (norm := (field_simp; ring))
      (qPochhammerInf ((q : ℂ) * q ^ n) q /
        qPochhammerInf ((q : ℂ) ^ b * q ^ n) q) * hp
  unfold jacksonIntegral
  simp only [one_mul]
  simp_rw [hterm]
  rw [tsum_mul_left, ← q_binomial_theorem hq hqa,
    ← cpow_add _ _ hqz, add_comm b a]
  have hK : (1 - (q : ℂ)) ≠ 0 := by exact_mod_cast (sub_pos.mpr hq1).ne'
  unfold qGamma
  rw [cpow_sub _ _ hK, cpow_sub _ _ hK, cpow_sub _ _ hK, cpow_add _ _ hK, cpow_one]
  have hKa : (1 - (q : ℂ)) ^ a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hK)
  have hKb : (1 - (q : ℂ)) ^ b ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hK)
  field [hA, hB, hC, hQ, hK, hKa, hKb]

end DLMF.QSeries
