/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.SeriesProperties
public import DLMF.QSeries.Pochhammer
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Ramanujan's `₁ψ₁` summation

This file proves Ramanujan's `₁ψ₁` summation
`∑_{n ∈ ℤ} (a;q)_n/(b;q)_n zⁿ = (q, b/a, az, q/(az);q)_∞ / (b, q/a, z, b/(az);q)_∞`
for `|b/a| < |z| < 1`, following Ismail's argument (AAR §10.5): after multiplication by
`(b;q)_∞` both sides are analytic in `b` on the disk `|b| < |az|`, and at `b = q^{m+1}` the
bilateral sum terminates below and reduces to the `q`-binomial theorem.

## Main results

* `differentiable_qPochhammerInf_left`: `b ↦ (b;q)_∞` is entire for `|q| < 1`.
* `norm_qPochhammer_le_exp`, `norm_qPochhammerInf_le_exp`: the bound `exp(|w|/(1-|q|))`.
* `ramanujan_1psi1_of_regular`: Ramanujan's `₁ψ₁` summation under the bilateral regularity
  conditions `b qⁿ ≠ 1` and `a ≠ q^{n+1}` for `n ≥ 0`.
-/

@[expose] public section

open Complex Finset Filter
open scoped Topology

noncomputable section

namespace DLMF.QSeries

/-- For `|q| < 1` the infinite product `b ↦ (b;q)_∞` is entire. -/
theorem differentiable_qPochhammerInf_left {q : ℂ} (hq : ‖q‖ < 1) :
    Differentiable ℂ (fun b : ℂ => qPochhammerInf b q) := by
  intro b0
  set R := ‖b0‖ + 1
  have hopen : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have h := Summable.hasProdLocallyUniformlyOn_one_add (f := fun (k : ℕ) (b : ℂ) => -(b * q ^ k))
    (u := fun k => R * ‖q‖ ^ k) hopen
    ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left R)
    (Filter.Eventually.of_forall fun k b hb => by
      rw [norm_neg, norm_mul, norm_pow]
      have : ‖b‖ ≤ R := by simpa using (Metric.mem_ball.mp hb).le
      exact mul_le_mul_of_nonneg_right this (pow_nonneg (norm_nonneg _) _))
    (fun k => by fun_prop)
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  have hd := h.differentiableOn (Filter.Eventually.of_forall fun s => by
    simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (u := s) (s := Metric.ball (0 : ℂ) R)
        (f := fun (i : ℕ) (b : ℂ) => 1 + -(b * q ^ i)) fun i _ => by fun_prop) hopen
  have : DifferentiableOn ℂ (fun b : ℂ => qPochhammerInf b q) (Metric.ball 0 R) :=
    hd.congr fun b _ => by simp [qPochhammerInf, sub_eq_add_neg]
  exact this.differentiableAt (hopen.mem_nhds (by simp [R]))

/-- The finite product bound `‖(w;q)_n‖ ≤ exp(‖w‖/(1-‖q‖))` for `‖q‖ < 1`. -/
theorem norm_qPochhammer_le_exp {w q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    ‖qPochhammer w q n‖ ≤ Real.exp (‖w‖ / (1 - ‖q‖)) := by
  have key : ∀ n, ‖qPochhammer w q n‖ ≤ Real.exp (‖w‖ * ∑ j ∈ range n, ‖q‖ ^ j) := by
    intro n
    induction n with
    | zero => simp [qPochhammer_zero]
    | succ n ih =>
      rw [qPochhammer_succ, norm_mul, sum_range_succ, mul_add, Real.exp_add]
      refine mul_le_mul ih ?_ (norm_nonneg _) (Real.exp_pos _).le
      calc ‖1 - w * q ^ n‖ ≤ ‖(1 : ℂ)‖ + ‖w * q ^ n‖ := norm_sub_le _ _
        _ = ‖w‖ * ‖q‖ ^ n + 1 := by rw [norm_one, norm_mul, norm_pow]; ring
        _ ≤ Real.exp (‖w‖ * ‖q‖ ^ n) := Real.add_one_le_exp _
  refine (key n).trans (Real.exp_le_exp.mpr ?_)
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg w)
  rw [← tsum_geometric_of_lt_one (norm_nonneg q) hq]
  exact (summable_geometric_of_lt_one (norm_nonneg q) hq).sum_le_tsum _
    (fun j _ => pow_nonneg (norm_nonneg q) j)

/-- The infinite product bound `‖(w;q)_∞‖ ≤ exp(‖w‖/(1-‖q‖))` for `‖q‖ < 1`. -/
theorem norm_qPochhammerInf_le_exp {w q : ℂ} (hq : ‖q‖ < 1) :
    ‖qPochhammerInf w q‖ ≤ Real.exp (‖w‖ / (1 - ‖q‖)) :=
  le_of_tendsto' (tendsto_qPochhammer hq).norm fun n => norm_qPochhammer_le_exp hq n

/-- Reversing `(b q^{-M};q)_M`: `(b/q^M;q)_M q^{C(M+1,2)} = ∏_{k<M} (q^{k+1} - b)`. -/
theorem qPochhammer_div_pow_mul_pow_choose (q b : ℂ) (hq : q ≠ 0) (M : ℕ) :
    qPochhammer (b / q ^ M) q M * q ^ (M + 1).choose 2 =
      ∏ k ∈ range M, (q ^ (k + 1) - b) := by
  induction M with
  | zero => simp [qPochhammer_zero]
  | succ M ih =>
    have hc : (M + 2).choose 2 = (M + 1).choose 2 + (M + 1) := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    have hx : b / q ^ (M + 1) * q = b / q ^ M := by field_simp; ring
    rw [qPochhammer_succ', hx, hc, pow_add, prod_range_succ, ← ih]
    have hqm : q ^ (M + 1) ≠ 0 := pow_ne_zero _ hq
    field_simp
    ring

namespace RamanujanPsi

/-- The summand of `(b;q)_∞` times the `₁ψ₁` series, `(a;q)_n (b qⁿ;q)_∞ zⁿ`, entire in `b`. -/
def term (a q z b : ℂ) (n : ℤ) : ℂ :=
  qPochhammerInt a q n * qPochhammerInf (b * q ^ n) q * z ^ n

/-- The product side of the `₁ψ₁` summation multiplied by `(b;q)_∞`. -/
def prodSide (a q z b : ℂ) : ℂ :=
  qPochhammerInf q q * qPochhammerInf (b / a) q * qPochhammerInf (a * z) q *
      qPochhammerInf (q / (a * z)) q /
    (qPochhammerInf (q / a) q * qPochhammerInf z q * qPochhammerInf (b / (a * z)) q)

/-- `(q/a;q)_∞ ≠ 0` when `a ≠ q^{n+1}` for all `n`. -/
theorem qPochhammerInf_q_div_ne_zero {a q : ℂ} (hq : ‖q‖ < 1) (ha0 : a ≠ 0)
    (ha : ∀ n : ℕ, a ≠ q ^ (n + 1)) : qPochhammerInf (q / a) q ≠ 0 :=
  qPochhammerInf_ne_zero hq fun n h => ha n <| by
    have : q / a * q ^ n = 1 := (sub_eq_zero.mp h).symm
    field_simp at this
    rw [pow_succ]; linear_combination -this

theorem term_negSucc {a q z b : ℂ} (hq0 : q ≠ 0) (ha0 : a ≠ 0) (hq : ‖q‖ < 1) (m : ℕ) :
    term a q z b (Int.negSucc m) =
      ((-a) ^ (m + 1) * qPochhammer (q / a) q (m + 1))⁻¹ *
        (∏ k ∈ range (m + 1), (q ^ (k + 1) - b)) * qPochhammerInf b q * (z ^ (m + 1))⁻¹ := by
  have hqC : q ^ (m + 1 + 1).choose 2 ≠ 0 := pow_ne_zero _ hq0
  have hsplit := qPochhammerInf_mul_qPochhammer hq (a := b / q ^ (m + 1)) (m + 1)
  have hbq : b / q ^ (m + 1) * q ^ (m + 1) = b := by field_simp
  rw [hbq] at hsplit
  have hA := TripleProduct.qPochhammer_shift_down hq0 ha0 (m + 1)
  have hB := qPochhammer_div_pow_mul_pow_choose q b hq0 (m + 1)
  unfold term
  have hqi : q ^ (-((m : ℤ) + 1)) = (q ^ (m + 1))⁻¹ := by rw [zpow_neg]; norm_cast
  rw [qPochhammerInt_negSucc, zpow_negSucc, zpow_negSucc, hqi,
    ← div_eq_mul_inv (a := a), ← div_eq_mul_inv (a := b), hsplit, ← hA, ← hB, mul_inv]
  have := inv_mul_cancel₀ hqC
  generalize qPochhammer (a / q ^ (m + 1)) q (m + 1) = X at *
  generalize qPochhammer (b / q ^ (m + 1)) q (m + 1) = Y at *
  generalize q ^ (m + 1 + 1).choose 2 = C at *
  linear_combination (-X⁻¹ * Y * qPochhammerInf b q * (z ^ (m + 1))⁻¹) * this

/-- `‖∏_{k<M} (q^{k+1} - b)‖ ≤ r^M exp(1/(r(1-‖q‖)))` for `‖b‖ ≤ r`. -/
theorem norm_prod_pow_sub_le {q b : ℂ} {r : ℝ} (hq : ‖q‖ < 1) (hr : 0 < r) (hb : ‖b‖ ≤ r)
    (M : ℕ) :
    ‖∏ k ∈ range M, (q ^ (k + 1) - b)‖ ≤ r ^ M * Real.exp (1 / (r * (1 - ‖q‖))) := by
  have key : ∀ M, ‖∏ k ∈ range M, (q ^ (k + 1) - b)‖ ≤
      r ^ M * Real.exp ((∑ j ∈ range M, ‖q‖ ^ j) / r) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [prod_range_succ, norm_mul, sum_range_succ, add_div, Real.exp_add, pow_succ]
      have h2 : ‖q ^ (M + 1) - b‖ ≤ r * Real.exp (‖q‖ ^ M / r) := by
        calc ‖q ^ (M + 1) - b‖ ≤ ‖q ^ (M + 1)‖ + ‖b‖ := norm_sub_le _ _
          _ ≤ ‖q‖ ^ M + r := by
            rw [norm_pow, pow_succ]
            gcongr
            exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hq.le
          _ = r * (‖q‖ ^ M / r + 1) := by field_simp
          _ ≤ r * Real.exp (‖q‖ ^ M / r) :=
            mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hr.le
      calc ‖∏ k ∈ range M, (q ^ (k + 1) - b)‖ * ‖q ^ (M + 1) - b‖
          ≤ (r ^ M * Real.exp ((∑ j ∈ range M, ‖q‖ ^ j) / r)) *
              (r * Real.exp (‖q‖ ^ M / r)) :=
            mul_le_mul ih h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring
  refine (key M).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  rw [one_div, mul_inv, mul_comm, ← one_div, div_eq_mul_inv, div_eq_mul_inv, one_mul]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hr.le)
  rw [← tsum_geometric_of_lt_one (norm_nonneg q) hq]
  exact (summable_geometric_of_lt_one (norm_nonneg q) hq).sum_le_tsum _
    (fun j _ => pow_nonneg (norm_nonneg q) j)

/-- A sequence `(w;q)_n` with nonzero limit has bounded inverses. -/
theorem exists_norm_inv_qPochhammer_le {w q : ℂ} (hq : ‖q‖ < 1) (hw : qPochhammerInf w q ≠ 0) :
    ∃ C : ℝ, ∀ n : ℕ, ‖(qPochhammer w q n)⁻¹‖ ≤ C := by
  have ht : Tendsto (fun n => ‖(qPochhammer w q n)⁻¹‖) atTop (𝓝 ‖(qPochhammerInf w q)⁻¹‖) :=
    ((tendsto_qPochhammer hq).inv₀ hw).norm
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  exact ⟨C, fun n => hC ⟨n, rfl⟩⟩

/-- A summable bound for `term a q z b` uniformly in `‖b‖ ≤ r < ‖az‖`. -/
theorem exists_summable_bound_term {a q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (ha0 : a ≠ 0)
    (ha : ∀ n : ℕ, a ≠ q ^ (n + 1)) (hz0 : z ≠ 0) (hz : ‖z‖ < 1) {r : ℝ} (hr0 : 0 < r)
    (hr : r < ‖a * z‖) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ (n : ℤ) (b : ℂ), ‖b‖ ≤ r → ‖term a q z b n‖ ≤ u n := by
  obtain ⟨C0, hC0⟩ := exists_norm_inv_qPochhammer_le hq (qPochhammerInf_q_div_ne_zero hq ha0 ha)
  have hC0' : 0 ≤ C0 := (norm_nonneg _).trans (hC0 0)
  set A := Real.exp (‖a‖ / (1 - ‖q‖))
  set E := Real.exp (r / (1 - ‖q‖))
  set K1 := Real.exp (1 / (r * (1 - ‖q‖)))
  have haz : 0 < ‖a * z‖ := norm_pos_iff.mpr (mul_ne_zero ha0 hz0)
  set ρ := r / ‖a * z‖
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one haz).mpr hr
  let u : ℤ → ℝ := fun n => match n with
    | Int.ofNat k => A * E * ‖z‖ ^ k
    | Int.negSucc m => C0 * K1 * E * ρ ^ (m + 1)
  refine ⟨u, ?_, ?_⟩
  · refine Summable.of_nat_of_neg_add_one ?_ ?_
    · exact (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (A * E)
    · exact ((summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one hρ0 hρ1)).mul_left (C0 * K1 * E)
  · intro n b hbr
    have hbinf : ‖qPochhammerInf b q‖ ≤ E :=
      (norm_qPochhammerInf_le_exp hq).trans (Real.exp_le_exp.mpr (by gcongr))
    rcases n with k | m
    · show ‖term a q z b k‖ ≤ A * E * ‖z‖ ^ k
      unfold term
      rw [zpow_natCast, zpow_natCast, norm_mul, norm_mul, norm_pow]
      have h1 : ‖qPochhammerInt a q k‖ ≤ A := norm_qPochhammer_le_exp hq k
      have hbk : ‖b * q ^ k‖ ≤ r := by
        rw [norm_mul, norm_pow]
        exact (mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (norm_nonneg _) hq.le)).trans hbr
      have h2 : ‖qPochhammerInf (b * q ^ k) q‖ ≤ E :=
        (norm_qPochhammerInf_le_exp hq).trans (Real.exp_le_exp.mpr
          (div_le_div_of_nonneg_right hbk (by linarith)))
      gcongr
    · show ‖term a q z b (Int.negSucc m)‖ ≤ C0 * K1 * E * ρ ^ (m + 1)
      rw [term_negSucc hq0 ha0 hq, mul_inv]
      simp only [norm_inv, norm_pow, norm_neg, norm_mul]
      have hP := norm_prod_pow_sub_le hq hr0 hbr (m + 1)
      have hQ : ‖qPochhammer (q / a) q (m + 1)‖⁻¹ ≤ C0 := by
        simpa only [norm_inv] using hC0 (m + 1)
      have hρ : ρ ^ (m + 1) = r ^ (m + 1) * ((‖a‖ ^ (m + 1))⁻¹ * (‖z‖ ^ (m + 1))⁻¹) := by
        simp only [ρ, norm_mul, div_pow, mul_pow]
        field_simp
      rw [hρ]
      calc (‖a‖ ^ (m + 1))⁻¹ * ‖qPochhammer (q / a) q (m + 1)‖⁻¹ *
            ‖∏ k ∈ range (m + 1), (q ^ (k + 1) - b)‖ * ‖qPochhammerInf b q‖ *
            (‖z‖ ^ (m + 1))⁻¹
          ≤ (‖a‖ ^ (m + 1))⁻¹ * C0 * (r ^ (m + 1) * K1) * E * (‖z‖ ^ (m + 1))⁻¹ := by
            gcongr
        _ = C0 * K1 * E * (r ^ (m + 1) * ((‖a‖ ^ (m + 1))⁻¹ * (‖z‖ ^ (m + 1))⁻¹)) := by
            ring

/-- `(b;q)_∞` times the `₁ψ₁` series is holomorphic in `b` on the disk `|b| < |az|`. -/
theorem differentiableOn_tsum_term {a q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (ha0 : a ≠ 0)
    (ha : ∀ n : ℕ, a ≠ q ^ (n + 1)) (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    DifferentiableOn ℂ (fun b => ∑' n : ℤ, term a q z b n) (Metric.ball 0 ‖a * z‖) := by
  have hloc : ∀ r : ℝ, 0 < r → r < ‖a * z‖ →
      DifferentiableOn ℂ (fun b => ∑' n : ℤ, term a q z b n) (Metric.ball 0 r) := by
    intro r hr0 hr
    obtain ⟨u, hu, hle⟩ := exists_summable_bound_term hq0 hq ha0 ha hz0 hz hr0 hr
    refine differentiableOn_tsum_of_summable_norm (u := u) hu ?_ Metric.isOpen_ball ?_
    · intro n
      exact (((differentiable_qPochhammerInf_left hq).comp
        (differentiable_id.mul_const _)).differentiableOn.const_mul _).mul_const _
    · intro n b hb
      exact hle n b (by simpa using (Metric.mem_ball.mp hb).le)
  intro b hb
  have hb' : ‖b‖ < ‖a * z‖ := by simpa using hb
  have hr0 : 0 < (‖b‖ + ‖a * z‖) / 2 := by linarith [norm_nonneg b]
  exact ((hloc _ hr0 (by linarith)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; linarith))).differentiableWithinAt

/-- `(a;q)_{k-m} = (a q^{-m};q)_m⁻¹ (a q^{-m};q)_k` for natural `k`, `m`. -/
theorem qPochhammerInt_natCast_sub {a q : ℂ} (hq0 : q ≠ 0) (m k : ℕ)
    (hx : qPochhammer (a / q ^ m) q m ≠ 0) :
    qPochhammerInt a q ((k : ℤ) - m) =
      (qPochhammer (a / q ^ m) q m)⁻¹ * qPochhammer (a / q ^ m) q k := by
  rcases le_or_gt m k with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    have hj : ((m + j : ℕ) : ℤ) - m = (j : ℕ) := by push_cast; ring
    have hxq : a / q ^ m * q ^ m = a := by field_simp
    rw [hj, qPochhammerInt_natCast, qPochhammer_add, hxq]
    field_simp
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    have hj : (k : ℤ) - ((k + j + 1 : ℕ) : ℤ) = Int.negSucc j := by
      rw [Int.negSucc_eq]; push_cast; ring
    have hsplit := qPochhammer_add (a / q ^ (k + j + 1)) q k (j + 1)
    rw [show k + (j + 1) = k + j + 1 by ring] at hsplit
    have hxq : a / q ^ (k + j + 1) * q ^ k = a * q ^ (-((j : ℤ) + 1)) := by
      rw [zpow_neg, show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      field_simp
      ring
    rw [hj, qPochhammerInt_negSucc, hsplit, ← hxq, mul_inv]
    rw [hsplit] at hx
    have hk : qPochhammer (a / q ^ (k + j + 1)) q k ≠ 0 := left_ne_zero_of_mul hx
    field_simp

/-- `(y;q)_∞ = 0` at `y = q^{-j}`. -/
theorem qPochhammerInf_inv_pow {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (j : ℕ) :
    qPochhammerInf (q ^ j)⁻¹ q = 0 := by
  rw [qPochhammerInf_mul_qPochhammer hq (j + 1), qPochhammer_succ,
    inv_mul_cancel₀ (pow_ne_zero j hq0)]
  simp

/-- At `b = q^{m+1}` the bilateral sum terminates below and is evaluated by the
`q`-binomial theorem. -/
theorem tsum_term_pow {a q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (ha0 : a ≠ 0)
    (ha : ∀ n : ℕ, a ≠ q ^ (n + 1)) (hz0 : z ≠ 0) (hz : ‖z‖ < 1) (m : ℕ)
    (hm : ‖q‖ ^ (m + 1) < ‖a * z‖) :
    ∑' n : ℤ, term a q z (q ^ (m + 1)) n = prodSide a q z (q ^ (m + 1)) := by
  set x := a / q ^ m with hx
  have hfa : ∀ n : ℕ, 1 - q / a * q ^ n ≠ 0 := fun n h => ha n <| by
    have : q / a * q ^ n = 1 := (sub_eq_zero.mp h).symm
    field_simp at this
    rw [pow_succ]; linear_combination -this
  have hQAm : qPochhammer (q / a) q m ≠ 0 := qPochhammer_ne_zero_of_factors hq hfa m
  have hF4 := TripleProduct.qPochhammer_shift_down hq0 ha0 m
  rw [← hx] at hF4
  have hqC : q ^ (m + 1).choose 2 ≠ 0 := pow_ne_zero _ hq0
  have hxm : qPochhammer x q m ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hF4
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr ha0)) hQAm hF4.symm
  set c := qPochhammerInf q q * (qPochhammer x q m)⁻¹ * (z ^ m)⁻¹ with hc
  have hterm : ∀ k : ℕ, term a q z (q ^ (m + 1)) ((k : ℤ) - m) =
      c * (qPochhammer x q k / qPochhammer q q k * z ^ k) := by
    intro k
    unfold term
    rw [qPochhammerInt_natCast_sub hq0 m k hxm, ← hx]
    have hqq : q ^ (m + 1) * q ^ ((k : ℤ) - m) = q * q ^ k := by
      rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
      field_simp
      ring
    have hQk := qPochhammer_self_ne_zero hq k
    have hinf := qPochhammerInf_mul_qPochhammer hq (a := q) k
    rw [hqq, zpow_sub₀ hz0, zpow_natCast, zpow_natCast, hc]
    rw [hinf]
    field_simp
  have hvanish : ∀ n ∉ Set.range (fun k : ℕ => (k : ℤ) - m), term a q z (q ^ (m + 1)) n = 0 := by
    intro n hn
    have hlt : n < -(m : ℤ) := by
      by_contra hge
      push Not at hge
      exact hn ⟨(n + m).toNat, by simp only; omega⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, n = -(m : ℤ) - 1 - j := ⟨(-(n + m + 1)).toNat, by omega⟩
    unfold term
    have hqn : q ^ (m + 1) * q ^ n = (q ^ j)⁻¹ := by
      rw [hj, show -(m : ℤ) - 1 - j = -(((m + 1 + j : ℕ)) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast, pow_add]
      field_simp
      ring
    rw [hqn, qPochhammerInf_inv_pow hq0 hq]
    simp
  have hbin : HasSum (fun k : ℕ => c * (qPochhammer x q k / qPochhammer q q k * z ^ k))
      (c * (qPochhammerInf (x * z) q / qPochhammerInf z q)) := by
    rw [q_binomial_theorem hq hz]
    exact (summable_q_binomial_series hq hz).hasSum.mul_left c
  have hinj : Function.Injective (fun k : ℕ => (k : ℤ) - m) := fun k l h => by
    simpa using h
  have hsum : HasSum (term a q z (q ^ (m + 1)))
      (c * (qPochhammerInf (x * z) q / qPochhammerInf z q)) := by
    rw [← hinj.hasSum_iff hvanish]
    exact hbin.congr_fun fun k => hterm k
  rw [hsum.tsum_eq]
  -- the product identity
  have hF1 := qPochhammerInf_mul_qPochhammer hq (a := q / a) m
  have hF2 := qPochhammerInf_mul_qPochhammer hq (a := q / (a * z)) m
  have hF3 := qPochhammerInf_mul_qPochhammer hq (a := x * z) m
  have hF5 := TripleProduct.qPochhammer_shift_down hq0 (mul_ne_zero ha0 hz0) m
  have e1 : q / a * q ^ m = q ^ (m + 1) / a := by rw [pow_succ]; ring
  have e2 : q / (a * z) * q ^ m = q ^ (m + 1) / (a * z) := by rw [pow_succ]; ring
  have e3 : x * z * q ^ m = a * z := by rw [hx]; field_simp
  have e5 : a * z / q ^ m = x * z := by rw [hx]; ring
  rw [e1] at hF1
  rw [e2] at hF2
  rw [e3] at hF3
  rw [e5] at hF5
  have hQAinf := qPochhammerInf_q_div_ne_zero hq ha0 ha
  have hX : qPochhammerInf (q ^ (m + 1) / a) q ≠ 0 := by
    rw [hF1] at hQAinf; exact right_ne_zero_of_mul hQAinf
  have hY : qPochhammerInf (q ^ (m + 1) / (a * z)) q ≠ 0 := by
    apply qPochhammerInf_ne_zero_of_norm_lt_one _ hq
    rw [norm_div, norm_pow]
    exact (div_lt_one (norm_pos_iff.mpr (mul_ne_zero ha0 hz0))).mpr hm
  have hZ : qPochhammerInf z q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hz hq
  unfold prodSide
  rw [hF1, hF2, hF3, hc]
  have hxm' : (qPochhammer x q m)⁻¹ =
      q ^ (m + 1).choose 2 * ((-a) ^ m * qPochhammer (q / a) q m)⁻¹ := by
    rw [← hF4]; field_simp
  have hxz : qPochhammer (x * z) q m =
      (-(a * z)) ^ m * qPochhammer (q / (a * z)) q m / q ^ (m + 1).choose 2 := by
    rw [← hF5]; field_simp
  rw [hxm', hxz]
  have hmz : (-(a * z)) ^ m = (-a) ^ m * z ^ m := by rw [neg_mul_eq_neg_mul, mul_pow]
  rw [hmz]
  have ha' : (-a) ^ m ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr ha0)
  have hzm : z ^ m ≠ 0 := pow_ne_zero _ hz0
  field_simp

/-- Multiplying the `₁ψ₁` summand by `(b;q)_∞` gives `term`, for `b qⁿ ≠ 1`. -/
theorem qPochhammerInf_mul_summand {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hb : ∀ n : ℕ, b * q ^ n ≠ 1) (n : ℤ) :
    qPochhammerInf b q * (qPochhammerInt a q n / qPochhammerInt b q n * z ^ n) =
      term a q z b n := by
  unfold term
  rcases n with k | m
  · have hbk : qPochhammer b q k ≠ 0 :=
      qPochhammer_ne_zero_of_factors hq (fun n => sub_ne_zero.mpr (hb n).symm) k
    rw [Int.ofNat_eq_natCast, qPochhammerInt_natCast, qPochhammerInt_natCast,
      qPochhammerInf_mul_qPochhammer hq (a := b) k]
    simp only [zpow_natCast]
    field_simp
  · have hqi : q ^ (-((m : ℤ) + 1)) = (q ^ (m + 1))⁻¹ := by rw [zpow_neg]; norm_cast
    have hsplit := qPochhammerInf_mul_qPochhammer hq (a := b * (q ^ (m + 1))⁻¹) (m + 1)
    have hbq : b * (q ^ (m + 1))⁻¹ * q ^ (m + 1) = b := by field_simp
    rw [hbq] at hsplit
    rw [qPochhammerInt_negSucc, qPochhammerInt_negSucc, hqi, zpow_negSucc, zpow_negSucc, hsplit,
      div_inv_eq_mul]
    ring

end RamanujanPsi

namespace RamanujanPsi

/-- The `₁ψ₁` summation multiplied by `(b;q)_∞`, valid for every `b` with `|b| < |az|`, with no
regularity condition on `b`. -/
theorem tsum_term_eq_prodSide {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (ha0 : a ≠ 0)
    (ha : ∀ n : ℕ, a ≠ q ^ (n + 1)) (hz0 : z ≠ 0) (hz : ‖z‖ < 1) (hbaz : ‖b‖ < ‖a * z‖) :
    ∑' n : ℤ, term a q z b n = prodSide a q z b := by
  have haz : 0 < ‖a * z‖ := norm_pos_iff.mpr (mul_ne_zero ha0 hz0)
  set U := Metric.ball (0 : ℂ) ‖a * z‖
  have hU : IsOpen U := Metric.isOpen_ball
  have hH : AnalyticOnNhd ℂ (fun b => ∑' n : ℤ, term a q z b n) U :=
    (differentiableOn_tsum_term hq0 hq ha0 ha hz0 hz).analyticOnNhd hU
  have hden : ∀ w ∈ U, qPochhammerInf (q / a) q * qPochhammerInf z q *
      qPochhammerInf (w / (a * z)) q ≠ 0 := by
    intro w hw
    have hw' : ‖w‖ < ‖a * z‖ := by simpa [U] using hw
    refine mul_ne_zero (mul_ne_zero (qPochhammerInf_q_div_ne_zero hq ha0 ha)
      (qPochhammerInf_ne_zero_of_norm_lt_one hz hq)) ?_
    apply qPochhammerInf_ne_zero_of_norm_lt_one _ hq
    rw [norm_div]; exact (div_lt_one haz).mpr hw'
  have hR : AnalyticOnNhd ℂ (prodSide a q z) U := by
    have hd : DifferentiableOn ℂ (prodSide a q z) U := by
      unfold prodSide
      have hP := differentiable_qPochhammerInf_left hq
      refine DifferentiableOn.div ?_ ?_ hden
      · exact ((((differentiableOn_const _).mul
          ((hP.comp (differentiable_id.div_const a)).differentiableOn)).mul
          (differentiableOn_const _)).mul (differentiableOn_const _))
      · exact (differentiableOn_const _).mul
          ((hP.comp (differentiable_id.div_const (a * z))).differentiableOn)
    exact hd.analyticOnNhd hU
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self haz
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ),
      (∑' n : ℤ, term a q z w n) = prodSide a q z w := by
    have htq : Tendsto (fun m : ℕ => q ^ (m + 1)) atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun m => pow_ne_zero _ hq0⟩
      exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (tendsto_add_atTop_nat 1)
    have hev : ∀ᶠ m : ℕ in atTop, ‖q‖ ^ (m + 1) < ‖a * z‖ :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).comp
        (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds haz)
    exact htq.frequently (hev.frequently.mono fun m hm =>
      tsum_term_pow hq0 hq ha0 ha hz0 hz m hm)
  have heq := hH.eqOn_of_preconnected_of_frequently_eq hR
    (convex_ball (0 : ℂ) _).isPreconnected h0U hfreq
  exact heq (by simpa [U] using hbaz)

/-- The series `∑ term a q z b n` converges absolutely for `|b| < |az|`. -/
theorem summable_term {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (ha0 : a ≠ 0)
    (ha : ∀ n : ℕ, a ≠ q ^ (n + 1)) (hz0 : z ≠ 0) (hz : ‖z‖ < 1) (hbaz : ‖b‖ < ‖a * z‖) :
    Summable (term a q z b) := by
  have hr0 : 0 < (‖b‖ + ‖a * z‖) / 2 := by linarith [norm_nonneg b]
  obtain ⟨u, hu, hle⟩ := exists_summable_bound_term hq0 hq ha0 ha hz0 hz hr0 (by linarith)
  exact Summable.of_norm_bounded hu fun n => hle n b (by linarith)

end RamanujanPsi

open RamanujanPsi in
/-- Ramanujan's `₁ψ₁` summation (DLMF 17.8.2, AAR §10.5) for `|b/a| < |z| < 1` under the
bilateral regularity conditions `b qⁿ ≠ 1` and `a ≠ q^{n+1}` (`n ≥ 0`). The proof is Ismail's:
both sides times `(b;q)_∞` are holomorphic in `b` on `|b| < |az|` and agree at `b = q^{m+1}`. -/
theorem ramanujan_1psi1_of_regular {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (ha0 : a ≠ 0)
    (ha : ∀ n : ℕ, a ≠ q ^ (n + 1)) (hb : ∀ n : ℕ, b * q ^ n ≠ 1)
    (hz : ‖b / a‖ < ‖z‖ ∧ ‖z‖ < 1) :
    (∑' n : ℤ, qPochhammerInt a q n / qPochhammerInt b q n * z ^ n) =
      qPochhammerInf q q * qPochhammerInf (b / a) q * qPochhammerInf (a * z) q *
          qPochhammerInf (q / (a * z)) q /
        (qPochhammerInf b q * qPochhammerInf (q / a) q * qPochhammerInf z q *
          qPochhammerInf (b / (a * z)) q) := by
  have hz0 : z ≠ 0 := fun h => by
    rw [h, norm_zero] at hz; exact (norm_nonneg _).not_gt hz.1
  have haz : 0 < ‖a * z‖ := norm_pos_iff.mpr (mul_ne_zero ha0 hz0)
  have hbaz : ‖b‖ < ‖a * z‖ := by
    have h1 := hz.1
    rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr ha0)] at h1
    rw [norm_mul]; linarith
  have hmain := RamanujanPsi.tsum_term_eq_prodSide hq0 hq ha0 ha hz0 hz.2 hbaz
  have hd : qPochhammerInf (q / a) q * qPochhammerInf z q *
      qPochhammerInf (b / (a * z)) q ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (qPochhammerInf_q_div_ne_zero hq ha0 ha)
      (qPochhammerInf_ne_zero_of_norm_lt_one hz.2 hq)) ?_
    apply qPochhammerInf_ne_zero_of_norm_lt_one _ hq
    rw [norm_div]; exact (div_lt_one haz).mpr hbaz
  have hbinf : qPochhammerInf b q ≠ 0 :=
    qPochhammerInf_ne_zero hq fun n => sub_ne_zero.mpr (hb n).symm
  have hL : (∑' n : ℤ, term a q z b n) =
      qPochhammerInf b q * ∑' n : ℤ, qPochhammerInt a q n / qPochhammerInt b q n * z ^ n := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => (qPochhammerInf_mul_summand hq0 hq hb n).symm
  rw [hL] at hmain
  unfold prodSide at hmain
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hbinf
    (qPochhammerInf_q_div_ne_zero hq ha0 ha)) (qPochhammerInf_ne_zero_of_norm_lt_one hz.2 hq))
    (by simpa using (mul_ne_zero_iff.mp hd).2))]
  rw [eq_div_iff hd] at hmain
  linear_combination hmain

end DLMF.QSeries
