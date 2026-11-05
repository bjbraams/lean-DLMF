/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BasicSummations.OnePhiZero
public import DLMF.QSeries.RamanujanPsi
public import DLMFMathlib.Analysis.SpecificLimits.PowMulPowChoose

/-!
# The Rogers–Fine expansion

Fine's third and fourth expansions (DLMF 17.6.11–17.6.12) follow by iterating functional
relations for `₂φ₁(q, aq; bq; q, z)`. In the fourth expansion the remainder is bounded by
a constant times `‖bz‖ᴺ ‖q‖^(N²)`. The third expansion separates even and odd shifted-factorial
indices and has a geometrically decaying remainder when `‖b‖ < 1`.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Real Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.RogersFine

/-- The two-phi-one series in Fine's fourth expansion. -/
def series (a b q z : ℂ) : ℂ := qPhi [q, a * q] [b * q] q z

/-- The q-factorial in this series cancels, leaving a ratio of two shifted factorials. -/
lemma hasSum_series {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (hb : QDenominatorRegular [b * q] q) :
    HasSum (fun n : ℕ => qPochhammer (a * q) q n / qPochhammer (b * q) q n * z ^ n)
      (series a b q z) := by
  refine (hasSum_qPhi_two_one (a := q) (b := a * q) hq0 hq hz hb).congr_fun fun n => ?_
  have hn := qPochhammer_self_ne_zero hq n
  field_simp

/-- Removing the initial term shifts both finite shifted-factorial parameters. -/
lemma series_eq_one_add {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (hb : QDenominatorRegular [b * q] q) :
    series a b q z = 1 + z * (1 - a * q) / (1 - b * q) * series (a * q) (b * q) q z := by
  have hu := hasSum_series (a := a) hq0 hq hz hb
  have hv := hasSum_series (a := a * q) hq0 hq hz (qDenominatorRegular_mul_q hb)
  rw [hu.tsum_eq.symm, hu.summable.tsum_eq_zero_add]
  simp only [qPochhammer_zero, div_self one_ne_zero, pow_zero, mul_one]
  congr 1
  rw [← hv.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [qPochhammer_succ', qPochhammer_succ', pow_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The first-order q-difference equation for the Fine series. -/
lemma series_qDifference {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (hb : QDenominatorRegular [b * q] q) :
    (1 - z) * series a b q z = 1 - b + (b - a * q * z) * series a b q (z * q) := by
  have hzq : ‖z * q‖ < 1 := by
    simpa only [pow_one] using norm_mul_pow_lt_one hz hq 1
  have hu := hasSum_series (a := a) hq0 hq hz hb
  have hv := hasSum_series (a := a) hq0 hq hzq hb
  have hconst : HasSum (fun n : ℕ => if n = 0 then (1 - b) else 0) (1 - b) := by
    simpa using (hasSum_single (f := fun n : ℕ => if n = 0 then (1 - b) else 0) 0
      (fun n hn => by simp [hn]))
  have hL := hu.sub (hasSum_prependZero (hu.mul_left z))
  have hR := hconst.add ((hv.mul_left b).sub (hasSum_prependZero (hv.mul_left (a * q * z))))
  have he : series a b q z - z * series a b q z =
      1 - b + (b * series a b q (z * q) - a * q * z * series a b q (z * q)) := by
    refine hL.unique (hR.congr_fun ?_)
    intro n
    cases n with
    | zero => simp [prependZero]
    | succ n =>
      have hB := qPochhammer_ne_zero_of_qDenominatorRegular hq hb n
      have hBn := qPochhammer_ne_zero_of_qDenominatorRegular hq hb (n + 1)
      rw [qPochhammer_succ] at hBn
      have hfactor : 1 - b * q * q ^ n ≠ 0 := right_ne_zero_of_mul hBn
      simp only [prependZero, Nat.succ_ne_zero, ite_false, qPochhammer_succ, pow_succ, mul_pow]
      generalize qPochhammer (a * q) q n = A
      generalize qPochhammer (b * q) q n = B at hB ⊢
      generalize q ^ n = Q at hfactor ⊢
      generalize hD : 1 - b * q * Q = D at hfactor ⊢
      field_simp [hB, hfactor]
      simp only [← hD]
      ring
  linear_combination he

/-- One iteration of the Rogers–Fine expansion. -/
lemma series_step {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (hb : QDenominatorRegular [b * q] q) :
    (1 - z) * series a b q z = 1 - a * z * q +
      (z * q * (1 - a * q) * (b - a * z * q) / (1 - b * q)) *
        series (a * q) (b * q) q (z * q) := by
  have hzq : ‖z * q‖ < 1 := by
    simpa only [pow_one, mul_comm] using norm_mul_pow_lt_one hz hq 1
  rw [series_qDifference hq0 hq hz hb, series_eq_one_add hq0 hq hzq hb]
  ring

/-- Lower-parameter regularity is retained by every nonnegative q-shift. -/
lemma regular_shift {b q : ℂ} (hb : QDenominatorRegular [b * q] q) (N : ℕ) :
    QDenominatorRegular [b * q ^ N * q] q := by
  intro x hx k
  simp only [List.mem_singleton] at hx
  subst x
  simpa only [pow_add, pow_succ, mul_assoc, mul_comm, mul_left_comm] using
    hb (b * q) (by simp) (N + k)

/-- The Fine series stays bounded under independent nonnegative q-shifts of its upper and
lower parameters, with its argument shifted by the upper index. -/
lemma exists_norm_series_shift_le {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : ‖z‖ < 1) (hb : QDenominatorRegular [b * q] q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N M : ℕ, ‖series (a * q ^ N) (b * q ^ M) q (z * q ^ N)‖ ≤ C := by
  have hBI : qPochhammerInf (b * q) q ≠ 0 := qPochhammerInf_ne_zero hq
    fun j h => hb (b * q) (by simp) j (sub_eq_zero.mp h).symm
  obtain ⟨B, hB⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq hBI
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let A := Real.exp (‖a * q‖ / (1 - ‖q‖))
  let E := Real.exp (‖b * q‖ / (1 - ‖q‖))
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hcoefficient (N M k : ℕ) :
      ‖qPochhammer (a * q ^ N * q) q k / qPochhammer (b * q ^ M * q) q k‖ ≤ A * E * B := by
    have hU : ‖qPochhammer (a * q ^ N * q) q k‖ ≤ A := by
      refine (norm_qPochhammer_le_exp hq k).trans (Real.exp_le_exp.mpr ?_)
      apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hq.le)
      rw [show a * q ^ N * q = (a * q) * q ^ N by ring, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
    have hD : ‖(qPochhammer (b * q ^ M * q) q k)⁻¹‖ ≤ E * B := by
      have hN := qPochhammer_ne_zero_of_qDenominatorRegular hq hb M
      have hNk := qPochhammer_ne_zero_of_qDenominatorRegular hq hb (M + k)
      have he : (qPochhammer (b * q ^ M * q) q k)⁻¹ =
          qPochhammer (b * q) q M * (qPochhammer (b * q) q (M + k))⁻¹ := by
        rw [qPochhammer_add]
        rw [show b * q * q ^ M = b * q ^ M * q by ring]
        field_simp
      rw [he, norm_mul]
      exact mul_le_mul (norm_qPochhammer_le_exp hq M) (hB (M + k)) (norm_nonneg _) hE0
    rw [div_eq_mul_inv, norm_mul]
    exact (mul_le_mul hU hD (norm_nonneg _) hA0).trans_eq (by ring)
  refine ⟨A * E * B / (1 - ‖z‖), by positivity, ?_⟩
  intro N M
  have hzN := norm_mul_pow_lt_one hz hq N
  have hs := hasSum_series (a := a * q ^ N) hq0 hq hzN (regular_shift hb M)
  have hgeom := (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (A * E * B)
  calc
    ‖series (a * q ^ N) (b * q ^ M) q (z * q ^ N)‖ ≤
        ∑' k, ‖qPochhammer (a * q ^ N * q) q k /
          qPochhammer (b * q ^ M * q) q k * (z * q ^ N) ^ k‖ := by
      rw [← hs.tsum_eq]
      exact norm_tsum_le_tsum_norm hs.summable.norm
    _ ≤ ∑' k, A * E * B * ‖z‖ ^ k := by
      apply hs.summable.norm.tsum_le_tsum _ hgeom
      intro k
      rw [norm_mul, norm_pow]
      apply mul_le_mul (hcoefficient N M k) _ (by positivity) (by positivity)
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
    _ = A * E * B / (1 - ‖z‖) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg z) hz, div_eq_mul_inv]

/-- The multiplying factors generated by iteration of the Fine functional equation. -/
def weight (a b q z : ℂ) (n : ℕ) : ℂ :=
  qPochhammer (a * q) q n * qPochhammer (a * z * q / b) q n /
    (qPochhammer (b * q) q n * qPochhammer (z * q) q n) * (b * z) ^ n * q ^ (n * n)

/-- The Fine iteration weights have summable norms. -/
lemma summable_norm_weight {a b q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (hb : QDenominatorRegular [b * q] q) : Summable (fun n => ‖weight a b q z n‖) := by
  have hBI : qPochhammerInf (b * q) q ≠ 0 := qPochhammerInf_ne_zero hq
    fun j h => hb (b * q) (by simp) j (sub_eq_zero.mp h).symm
  have hzq : ‖z * q‖ < 1 := by simpa only [pow_one] using norm_mul_pow_lt_one hz hq 1
  obtain ⟨B, hB⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq hBI
  obtain ⟨Z, hZ⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq
    (qPochhammerInf_ne_zero_of_norm_lt_one hzq hq)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
  let C := Real.exp (‖a * q‖ / (1 - ‖q‖)) *
    Real.exp (‖a * z * q / b‖ / (1 - ‖q‖)) * B * Z
  have hC0 : 0 ≤ C := by positivity
  have hnorm (n : ℕ) : ‖weight a b q z n‖ ≤ C * (‖b * z‖ ^ n * ‖q‖ ^ (n * n)) := by
    have hAB := mul_le_mul (norm_qPochhammer_le_exp (w := a * q) hq n)
      (norm_qPochhammer_le_exp (w := a * z * q / b) hq n)
      (norm_nonneg _) (by positivity : 0 ≤ Real.exp (‖a * q‖ / (1 - ‖q‖)))
    have hBZ := mul_le_mul (hB n) (hZ n) (norm_nonneg _) hB0
    have hprod := mul_le_mul hAB hBZ (by positivity)
      (by positivity : 0 ≤ Real.exp (‖a * q‖ / (1 - ‖q‖)) *
        Real.exp (‖a * z * q / b‖ / (1 - ‖q‖)))
    have h := mul_le_mul_of_nonneg_right hprod
      (by positivity : 0 ≤ ‖b * z‖ ^ n * ‖q‖ ^ (n * n))
    simpa only [weight, C, div_eq_mul_inv, mul_inv_rev, norm_mul, norm_pow,
      mul_assoc, mul_comm, mul_left_comm] using h
  have hchoose := summable_pow_mul_pow_choose_two (norm_nonneg (b * z)) (norm_nonneg q) hq
  have hgauss : Summable (fun n : ℕ => ‖b * z‖ ^ n * ‖q‖ ^ (n * n)) := by
    apply hchoose.of_nonneg_of_le (fun _ => by positivity)
    intro n
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_of_le_one (norm_nonneg q) hq.le
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))
  exact (hgauss.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hnorm

/-- The remainder after a finite number of Rogers–Fine iterations. -/
def remainder (a b q z : ℂ) (n : ℕ) : ℂ :=
  weight a b q z n * ((1 - z * q ^ n) *
    series (a * q ^ n) (b * q ^ n) q (z * q ^ n))

/-- Consecutive remainders differ by the well-poised summand in Fine's fourth expansion. -/
lemma remainder_step {a b q z : ℂ} (hb0 : b ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : ‖z‖ < 1) (hb : QDenominatorRegular [b * q] q) (n : ℕ) :
    remainder a b q z n - remainder a b q z (n + 1) =
      weight a b q z n * (1 - a * z * q ^ (2 * n + 1)) := by
  have hzq : ‖z * q‖ < 1 := by simpa only [pow_one] using norm_mul_pow_lt_one hz hq 1
  have hZ : QDenominatorRegular [z * q] q := by
    intro x hx j
    simp only [List.mem_singleton] at hx
    subst x
    intro he
    have hh := norm_mul_pow_lt_one hzq hq j
    rw [he, norm_one] at hh
    exact hh.false
  have hB := qPochhammer_ne_zero_of_qDenominatorRegular hq hb n
  have hZn := qPochhammer_ne_zero_of_qDenominatorRegular hq hZ n
  have hBn := one_sub_ne_zero_of_qDenominatorRegular (regular_shift hb n)
  have hZsucc := one_sub_ne_zero_of_qDenominatorRegular (regular_shift hZ n)
  have hstep := series_step (a := a * q ^ n) hq0 hq
    (norm_mul_pow_lt_one hz hq n) (regular_shift hb n)
  have hweight : weight a b q z (n + 1) * (1 - z * q ^ (n + 1)) =
      weight a b q z n * ((z * q ^ n * q * (1 - a * q ^ n * q) *
        (b * q ^ n - a * q ^ n * (z * q ^ n) * q) / (1 - b * q ^ n * q))) := by
    dsimp [weight]
    rw [qPochhammer_succ, qPochhammer_succ, qPochhammer_succ, qPochhammer_succ]
    rw [show (n + 1) * (n + 1) = n * n + n + n + 1 by ring]
    simp only [pow_add, pow_succ, mul_pow]
    have hBn' : 1 - b * q * q ^ n ≠ 0 := by convert hBn using 1; ring
    have hZsucc' : 1 - z * q * q ^ n ≠ 0 := by convert hZsucc using 1; ring
    generalize qPochhammer (a * q) q n = A
    generalize qPochhammer (a * z * q / b) q n = W
    generalize qPochhammer (b * q) q n = B at hB ⊢
    generalize qPochhammer (z * q) q n = Z at hZn ⊢
    generalize q ^ n = Q at hBn' hZsucc' ⊢
    rw [show 1 - b * Q * q = 1 - b * q * Q by ring]
    generalize hDB : 1 - b * q * Q = DB at hBn' ⊢
    generalize hDZ : 1 - z * q * Q = DZ at hZsucc' ⊢
    field_simp [hB, hZn, hBn', hZsucc', hb0]
    simp only [← hDZ]
    ring
  dsimp [remainder]
  rw [hstep]
  have he : (a * q ^ n) * (z * q ^ n) * q = a * z * q ^ (2 * n + 1) := by
    rw [pow_add, pow_mul, pow_two, pow_one]
    ring
  rw [he]
  rw [show a * q ^ (n + 1) = a * q ^ n * q by ring,
    show b * q ^ (n + 1) = b * q ^ n * q by ring,
    show z * q ^ (n + 1) = z * q ^ n * q by ring]
  linear_combination -(series (a * q ^ n * q) (b * q ^ n * q) q (z * q ^ n * q)) * hweight

/-- The Rogers–Fine remainder tends to zero on the open unit disk. -/
lemma tendsto_remainder_zero {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : ‖z‖ < 1) (hb : QDenominatorRegular [b * q] q) :
    Tendsto (remainder a b q z) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_series_shift_le (a := a) hq0 hq hz hb
  have hw := (summable_norm_weight (a := a) hq hz hb).tendsto_atTop_zero
  have hbound (n : ℕ) : ‖remainder a b q z n‖ ≤ ‖weight a b q z n‖ * ((1 + ‖z‖) * C) := by
    dsimp [remainder]
    rw [norm_mul, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply mul_le_mul _ (hC n n) (norm_nonneg _) (by positivity)
    calc ‖1 - z * q ^ n‖ ≤ ‖(1 : ℂ)‖ + ‖z * q ^ n‖ := norm_sub_le _ _
      _ ≤ 1 + ‖z‖ := by
        rw [norm_one, norm_mul, norm_pow]
        gcongr
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hbound (by simpa using hw.mul_const ((1 + ‖z‖) * C))

/-- Fine's fourth expansion as an absolutely convergent sum. -/
lemma hasSum_expansion {a b q z : ℂ} (hb0 : b ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : ‖z‖ < 1) (hb : QDenominatorRegular [b * q] q) :
    HasSum (fun n : ℕ => weight a b q z n * (1 - a * z * q ^ (2 * n + 1)))
      ((1 - z) * series a b q z) := by
  have hsum : Summable (fun n : ℕ => ‖weight a b q z n * (1 - a * z * q ^ (2 * n + 1))‖) := by
    apply ((summable_norm_weight (a := a) hq hz hb).mul_right (1 + ‖a * z * q‖)).of_nonneg_of_le
      (fun _ => norm_nonneg _)
    intro n
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc ‖1 - a * z * q ^ (2 * n + 1)‖ ≤ 1 + ‖a * z * q ^ (2 * n + 1)‖ := by
          simpa only [norm_one] using norm_sub_le (1 : ℂ) (a * z * q ^ (2 * n + 1))
      _ ≤ 1 + ‖a * z * q‖ := by
        rw [show a * z * q ^ (2 * n + 1) = (a * z * q) * q ^ (2 * n) by ring,
          norm_mul, norm_pow]
        gcongr
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
  apply (hasSum_iff_tendsto_nat_of_summable_norm hsum).mpr
  have he (N : ℕ) :
      ∑ n ∈ range N, weight a b q z n * (1 - a * z * q ^ (2 * n + 1)) =
        remainder a b q z 0 - remainder a b q z N := by
    simp_rw [← remainder_step hb0 hq0 hq hz hb]
    exact sum_range_sub' (remainder a b q z) N
  simp_rw [he]
  simpa [remainder, weight] using
    (tendsto_const_nhds (x := remainder a b q z 0)).sub
      (tendsto_remainder_zero hq0 hq hz hb)

/-- A contiguous upper-parameter relation for the Fine series. -/
lemma series_upper_contiguous {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : ‖z‖ < 1) (hb : QDenominatorRegular [b * q] q) :
    (1 - a * q) * series (a * q) b q z = series a b q z - a * q * series a b q (z * q) := by
  have hzq : ‖z * q‖ < 1 := by simpa only [pow_one] using norm_mul_pow_lt_one hz hq 1
  have hL := (hasSum_series (a := a * q) hq0 hq hz hb).mul_left (1 - a * q)
  have hR := (hasSum_series (a := a) hq0 hq hz hb).sub
    ((hasSum_series (a := a) hq0 hq hzq hb).mul_left (a * q))
  refine hL.unique (hR.congr_fun fun n => ?_)
  have hP := qPochhammer_succ' (a * q) q n
  rw [qPochhammer_succ] at hP
  simp only [mul_pow]
  linear_combination -z ^ n / qPochhammer (b * q) q n * hP

/-- The functional relation underlying Fine's expansion with even and odd shifted factorials.
-/
lemma series_step_fixed_lower {a b q z : ℂ} (hb0 : b ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : ‖z‖ < 1) (hb : QDenominatorRegular [b * q] q)
    (ha : QDenominatorRegular [a * q / b] q) :
    (1 - z) * series a b q z =
      (1 - b) * (1 - a * q * (1 - a * z * q / b) / (1 - a * q / b)) +
      b * (1 - a * q) * (1 - a * z * q / b) * (1 - a * z * q ^ 2 / b) /
        (1 - a * q / b) * series (a * q) b q (z * q) := by
  have hzq : ‖z * q‖ < 1 := by simpa only [pow_one] using norm_mul_pow_lt_one hz hq 1
  have h0 := series_qDifference (a := a) hq0 hq hz hb
  have h1 := series_qDifference (a := a) hq0 hq hzq hb
  have hA := series_upper_contiguous (a := a) hq0 hq hzq hb
  have hD : b - a * q ≠ 0 := by
    intro he
    have h := one_sub_ne_zero_of_qDenominatorRegular ha
    apply h
    rw [(sub_eq_zero.mp he).symm, div_self hb0, sub_self]
  have hclear : (b - a * q) * series a b q (z * q) =
      (1 - a * q) * (b - a * z * q ^ 2) * series (a * q) b q (z * q) - a * q * (1 - b) := by
    linear_combination -(b - a * z * q ^ 2) * hA - a * q * h1
  rw [h0]
  rw [mul_comm z q] at hclear ⊢
  field_simp [hb0, hD]
  linear_combination (b - a * z * q) * hclear

namespace OddEvenExpansion

/-- The weights with a retained even or odd shifted-factorial index in Fine's third expansion. -/
def weight (a b q z : ℂ) (p n : ℕ) : ℂ :=
  qPochhammer (a * q) q n * qPochhammer (a * z * q / b) q (2 * n + p) * (b * q ^ p) ^ n /
    (qPochhammer (z * q) q n * qPochhammer (a * q / b) q (n + p))

/-- Each parity of the Fine weights has summable norms when `‖b‖ < 1`. -/
lemma summable_norm_weight {a b q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (hb : ‖b‖ < 1) (ha : QDenominatorRegular [a * q / b] q) (p : ℕ) :
    Summable (fun n => ‖weight a b q z p n‖) := by
  have hAI : qPochhammerInf (a * q / b) q ≠ 0 := qPochhammerInf_ne_zero hq
    fun j h => ha (a * q / b) (by simp) j (sub_eq_zero.mp h).symm
  have hzq : ‖z * q‖ < 1 := by simpa only [pow_one] using norm_mul_pow_lt_one hz hq 1
  obtain ⟨A, hA⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq hAI
  obtain ⟨Z, hZ⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq
    (qPochhammerInf_ne_zero_of_norm_lt_one hzq hq)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
  let C := Real.exp (‖a * q‖ / (1 - ‖q‖)) *
    Real.exp (‖a * z * q / b‖ / (1 - ‖q‖)) * A * Z
  have hC0 : 0 ≤ C := by positivity
  refine ((summable_geometric_of_lt_one (norm_nonneg b) hb).mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _) ?_
  intro n
  have hAB := mul_le_mul (norm_qPochhammer_le_exp (w := a * q) hq n)
    (norm_qPochhammer_le_exp (w := a * z * q / b) hq (2 * n + p))
    (norm_nonneg _) (by positivity : 0 ≤ Real.exp (‖a * q‖ / (1 - ‖q‖)))
  have hAZ := mul_le_mul (hA (n + p)) (hZ n) (norm_nonneg _) hA0
  have hprod := mul_le_mul hAB hAZ (by positivity)
    (by positivity : 0 ≤ Real.exp (‖a * q‖ / (1 - ‖q‖)) *
      Real.exp (‖a * z * q / b‖ / (1 - ‖q‖)))
  have hpow : ‖b * q ^ p‖ ^ n ≤ ‖b‖ ^ n := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
  have H := mul_le_mul hprod hpow (by positivity) (by positivity)
  simpa only [weight, C, div_eq_mul_inv, mul_inv_rev, norm_mul, norm_pow,
    mul_assoc, mul_comm, mul_left_comm] using H

/-- The remainder after truncating Fine's third expansion. -/
def remainder (a b q z : ℂ) (n : ℕ) : ℂ :=
  weight a b q z 0 n * ((1 - z * q ^ n) / (1 - b) *
    series (a * q ^ n) b q (z * q ^ n))

/-- The remainders in the even-odd expansion tend to zero. -/
lemma tendsto_remainder_zero {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : ‖z‖ < 1) (hb : ‖b‖ < 1) (hB : QDenominatorRegular [b * q] q)
    (hA : QDenominatorRegular [a * q / b] q) :
    Tendsto (remainder a b q z) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_series_shift_le (a := a) hq0 hq hz hB
  have hw := (summable_norm_weight (a := a) hq hz hb hA 0).tendsto_atTop_zero
  have hbound (n : ℕ) : ‖remainder a b q z n‖ ≤
      ‖weight a b q z 0 n‖ * ((1 + ‖z‖) / ‖1 - b‖ * C) := by
    dsimp [remainder]
    rw [norm_mul, norm_mul, norm_div]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply mul_le_mul _ (by simpa only [pow_zero, mul_one] using hC n 0)
      (norm_nonneg _) (by positivity)
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc ‖1 - z * q ^ n‖ ≤ ‖(1 : ℂ)‖ + ‖z * q ^ n‖ := norm_sub_le _ _
      _ ≤ 1 + ‖z‖ := by
        rw [norm_one, norm_mul, norm_pow]
        gcongr
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hbound
    (by simpa using hw.mul_const ((1 + ‖z‖) / ‖1 - b‖ * C))

/-- The even and odd weights are the difference of consecutive Fine remainders. -/
lemma remainder_step {a b q z : ℂ} (hb0 : b ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : ‖z‖ < 1) (hb : ‖b‖ < 1) (hB : QDenominatorRegular [b * q] q)
    (hA : QDenominatorRegular [a * q / b] q) (n : ℕ) :
    remainder a b q z n - remainder a b q z (n + 1) =
      weight a b q z 0 n - a * q * weight a b q z 1 n := by
  have hAN : QDenominatorRegular [a * q ^ n * q / b] q := by
    intro x hx j
    simp only [List.mem_singleton] at hx
    subst x
    simpa only [pow_add, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hA (a * q / b) (by simp) (n + j)
  have hstep := series_step_fixed_lower (a := a * q ^ n) hb0 hq0 hq
    (norm_mul_pow_lt_one hz hq n) hB hAN
  have hb1 := one_sub_ne_zero_of_norm_lt_one hb
  have hzq : ‖z * q‖ < 1 := by simpa only [pow_one] using norm_mul_pow_lt_one hz hq 1
  have hZ : QDenominatorRegular [z * q] q := by
    intro x hx j
    simp only [List.mem_singleton] at hx
    subst x
    intro he
    have hh := norm_mul_pow_lt_one hzq hq j
    rw [he, norm_one] at hh
    exact hh.false
  have hD := qPochhammer_ne_zero_of_qDenominatorRegular hq hA n
  have hZn := qPochhammer_ne_zero_of_qDenominatorRegular hq hZ n
  have hfactor : 1 - a * q / b * q ^ n ≠ 0 := by
    intro he
    exact hA _ (by simp) n (sub_eq_zero.mp he).symm
  have hZfactor : 1 - z * q * q ^ n ≠ 0 := by
    intro he
    exact hZ _ (by simp) n (sub_eq_zero.mp he).symm
  have heD : 1 - a * q ^ n * q / b = 1 - a * q / b * q ^ n := by ring
  have hweight : weight a b q z 0 (n + 1) * (1 - z * q ^ (n + 1)) =
      weight a b q z 0 n * (b * (1 - a * q ^ n * q) *
        (1 - (a * q ^ n) * (z * q ^ n) * q / b) *
        (1 - (a * q ^ n) * (z * q ^ n) * q ^ 2 / b) / (1 - a * q ^ n * q / b)) := by
    dsimp [weight]
    simp only [pow_zero, mul_one]
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      qPochhammer_succ, qPochhammer_succ, qPochhammer_succ,
      qPochhammer_succ, qPochhammer_succ]
    simp only [show 2 * n = n + n by omega, pow_add, pow_succ]
    rw [heD]
    generalize qPochhammer (a * q) q n = A
    generalize qPochhammer (a * z * q / b) q (2 * n) = W
    generalize qPochhammer (a * q / b) q n = D at hD ⊢
    generalize qPochhammer (z * q) q n = Z at hZn ⊢
    generalize hDA : 1 - a * q / b * q ^ n = DA at hfactor ⊢
    generalize hDZ : 1 - z * q * q ^ n = DZ at hZfactor ⊢
    field_simp [hD, hZn, hfactor, hZfactor, hb0]
    simp only [← hDZ]
    ring
  have hodd : weight a b q z 0 n *
      (a * q ^ n * q * (1 - (a * q ^ n) * (z * q ^ n) * q / b) /
        (1 - a * q ^ n * q / b)) = a * q * weight a b q z 1 n := by
    dsimp [weight]
    simp only [pow_zero, pow_one, mul_one]
    rw [qPochhammer_succ, qPochhammer_succ, heD]
    simp only [show 2 * n = n + n by omega, pow_add, mul_pow]
    generalize qPochhammer (a * q) q n = A
    generalize qPochhammer (a * z * q / b) q (2 * n) = W
    generalize qPochhammer (a * q / b) q n = D at hD ⊢
    generalize qPochhammer (z * q) q n = Z at hZn ⊢
    generalize hDA : 1 - a * q / b * q ^ n = DA at hfactor ⊢
    field_simp [hD, hZn, hfactor, hb0]
  have hnormstep : (1 - z * q ^ n) / (1 - b) *
      series (a * q ^ n) b q (z * q ^ n) =
      1 - a * q ^ n * q * (1 - (a * q ^ n) * (z * q ^ n) * q / b) /
        (1 - a * q ^ n * q / b) +
      (b * (1 - a * q ^ n * q) * (1 - (a * q ^ n) * (z * q ^ n) * q / b) *
        (1 - (a * q ^ n) * (z * q ^ n) * q ^ 2 / b) /
          (1 - a * q ^ n * q / b)) / (1 - b) *
        series (a * q ^ n * q) b q (z * q ^ n * q) := by
    rw [div_mul_eq_mul_div, hstep]
    field_simp [hb1]
  dsimp [remainder]
  rw [hnormstep]
  rw [show a * q ^ (n + 1) = a * q ^ n * q by ring]
  rw [show z * q ^ (n + 1) = z * q ^ n * q by ring] at hweight ⊢
  linear_combination -hodd -
    (series (a * q ^ n * q) b q (z * q ^ n * q) / (1 - b)) * hweight

/-- Fine's third expansion, with the even and odd series kept separately. -/
lemma expansion {a b q z : ℂ} (hb0 : b ≠ 0) (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : ‖z‖ < 1) (hb : ‖b‖ < 1) (hB : QDenominatorRegular [b * q] q)
    (hA : QDenominatorRegular [a * q / b] q) :
    (1 - z) / (1 - b) * series a b q z =
      (∑' n : ℕ, weight a b q z 0 n) - a * q * ∑' n : ℕ, weight a b q z 1 n := by
  have heven := (summable_norm_weight (a := a) hq hz hb hA 0).of_norm
  have hodd := (summable_norm_weight (a := a) hq hz hb hA 1).of_norm
  have hsum := heven.sub (hodd.mul_left (a * q))
  have H : HasSum (fun n : ℕ => weight a b q z 0 n - a * q * weight a b q z 1 n)
      ((1 - z) / (1 - b) * series a b q z) := by
    apply (hasSum_iff_tendsto_nat_of_summable_norm hsum.norm).mpr
    have he (N : ℕ) :
        ∑ n ∈ range N, (weight a b q z 0 n - a * q * weight a b q z 1 n) =
          remainder a b q z 0 - remainder a b q z N := by
      simp_rw [← remainder_step hb0 hq0 hq hz hb hB hA]
      exact sum_range_sub' (remainder a b q z) N
    simp_rw [he]
    simpa [remainder, weight] using
      (tendsto_const_nhds (x := remainder a b q z 0)).sub
        (tendsto_remainder_zero hq0 hq hz hb hB hA)
  rw [← H.tsum_eq, heven.tsum_sub (hodd.mul_left (a * q)), tsum_mul_left]

end OddEvenExpansion

end DLMF.QHypergeometric.RogersFine
