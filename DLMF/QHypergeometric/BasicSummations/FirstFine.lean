/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BasicSummations.RogersFine

/-!
# Fine's first expansion

Fine's first expansion of `₂φ₁(q, aq; bq; q, z)` follows by iterating its upper-parameter
recurrence. The first series has denominator `(aq²/b;q)ₙ`. The multiplying products tend
to `(aq, azq/b;q)∞/(aq/b;q)∞`, while the shifted series tends to `₂φ₁(q, 0; bq; q, z)`.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Real Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.FineFirstExpansion

open RogersFine

/-- Iteration in the upper parameter of Fine's series. -/
lemma series_recurrence {a b q z : ℂ} (hb0 : b ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hb : QDenominatorRegular [b * q] q) :
    (1 - a * q / b) * series a b q z =
      (1 - a * q) * (1 - a * z * q / b) * series (a * q) b q z -
        (1 - b) * (a * q / b) := by
  have hD := series_qDifference (a := a) hq0 hq hz hb
  have hA := series_upper_contiguous (a := a) hq0 hq hz hb
  field_simp [hb0]
  linear_combination -(b - a * z * q) * hA - a * q * hD

/-- Shifting the upper parameter to zero commutes with the convergent Fine series. -/
lemma tendsto_series_upper_shift {a b q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz : ‖z‖ < 1) (hb : QDenominatorRegular [b * q] q) :
    Tendsto (fun N : ℕ => series (a * q ^ N) b q z) atTop (𝓝 (series 0 b q z)) := by
  have hBI : qPochhammerInf (b * q) q ≠ 0 := qPochhammerInf_ne_zero hq
    fun j h => hb (b * q) (by simp) j (sub_eq_zero.mp h).symm
  obtain ⟨B, hB⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq hBI
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let A := Real.exp (‖a * q‖ / (1 - ‖q‖))
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have hupper (N n : ℕ) : ‖qPochhammer (a * q ^ N * q) q n‖ ≤ A := by
    refine (norm_qPochhammer_le_exp hq n).trans (Real.exp_le_exp.mpr ?_)
    apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hq.le)
    rw [show a * q ^ N * q = (a * q) * q ^ N by ring, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
  have hterm (n : ℕ) : Tendsto (fun N : ℕ =>
      qPochhammer (a * q ^ N * q) q n / qPochhammer (b * q) q n * z ^ n) atTop
      (𝓝 (qPochhammer (0 * q) q n / qPochhammer (b * q) q n * z ^ n)) := by
    have hp : Tendsto (fun N : ℕ => a * q ^ N * q) atTop (𝓝 (0 : ℂ)) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul a |>.mul_const q
    simpa only [zero_mul, Function.comp_def] using
      (((continuous_qPochhammer q n).tendsto 0).comp hp).div_const
        (qPochhammer (b * q) q n) |>.mul_const (z ^ n)
  have h := tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (A * B)) hterm
    (Eventually.of_forall fun N n => by
      simp only [div_eq_mul_inv, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hupper N n) (hB n) (norm_nonneg _) hA0) (by positivity))
  have he (N : ℕ) : (∑' n : ℕ, qPochhammer (a * q ^ N * q) q n /
      qPochhammer (b * q) q n * z ^ n) = series (a * q ^ N) b q z :=
    (hasSum_series hq0 hq hz hb).tsum_eq
  simpa only [he, (hasSum_series (a := 0) hq0 hq hz hb).tsum_eq] using h

/-- The finite multiplying products for the upper-parameter iteration. -/
def weight (a b q z : ℂ) (n : ℕ) : ℂ :=
  qPochhammer (a * q) q n * qPochhammer (a * z * q / b) q n /
    qPochhammer (a * q / b) q n

/-- The summands in the corrected first Fine expansion. -/
def term (a b q z : ℂ) (n : ℕ) : ℂ :=
  qPochhammer (a * q) q n * qPochhammer (a * z * q / b) q n * q ^ n /
    qPochhammer (a * q ^ 2 / b) q n

/-- The finite upper-iteration products converge to their infinite-product quotient. -/
lemma tendsto_weight {a b q z : ℂ} (hq : ‖q‖ < 1)
    (ha : QDenominatorRegular [a * q / b] q) :
    Tendsto (weight a b q z) atTop
      (𝓝 (qPochhammerInf (a * q) q * qPochhammerInf (a * z * q / b) q /
        qPochhammerInf (a * q / b) q)) := by
  have hAI : qPochhammerInf (a * q / b) q ≠ 0 := qPochhammerInf_ne_zero hq
    fun j h => ha (a * q / b) (by simp) j (sub_eq_zero.mp h).symm
  exact ((tendsto_qPochhammer hq).mul (tendsto_qPochhammer hq)).div
    (tendsto_qPochhammer hq) hAI

/-- The corrected first Fine series is absolutely convergent for `‖q‖ < 1`. -/
lemma summable_norm_term {a b q z : ℂ} (hq : ‖q‖ < 1)
    (ha : QDenominatorRegular [a * q / b] q) : Summable (fun n => ‖term a b q z n‖) := by
  have hD : QDenominatorRegular [a * q ^ 2 / b] q := by
    convert qDenominatorRegular_mul_q ha using 1; congr 1; ring
  have hDI : qPochhammerInf (a * q ^ 2 / b) q ≠ 0 := qPochhammerInf_ne_zero hq
    fun j h => hD _ (by simp) j (sub_eq_zero.mp h).symm
  obtain ⟨B, hB⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq hDI
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let C := Real.exp (‖a * q‖ / (1 - ‖q‖)) *
    Real.exp (‖a * z * q / b‖ / (1 - ‖q‖)) * B
  refine ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _) ?_
  intro n
  have hAB := mul_le_mul (norm_qPochhammer_le_exp (w := a * q) hq n)
    (norm_qPochhammer_le_exp (w := a * z * q / b) hq n)
    (norm_nonneg _) (by positivity : 0 ≤ Real.exp (‖a * q‖ / (1 - ‖q‖)))
  have H := mul_le_mul hAB (hB n) (norm_nonneg _)
    (by positivity : 0 ≤ Real.exp (‖a * q‖ / (1 - ‖q‖)) *
      Real.exp (‖a * z * q / b‖ / (1 - ‖q‖)))
  have H' := mul_le_mul_of_nonneg_right H (pow_nonneg (norm_nonneg q) n)
  simpa only [term, C, div_eq_mul_inv, norm_mul, norm_pow, mul_assoc, mul_comm,
    mul_left_comm] using H'

/-- A single telescoping step for the upper-parameter iteration. -/
lemma weight_series_sub_succ {a b q z : ℂ} (hb0 : b ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hb : QDenominatorRegular [b * q] q)
    (ha : QDenominatorRegular [a * q / b] q) (n : ℕ) :
    weight a b q z n * series (a * q ^ n) b q z -
        weight a b q z (n + 1) * series (a * q ^ (n + 1)) b q z =
      (-(1 - b) * (a * q / b) / (1 - a * q / b)) * term a b q z n := by
  have hc := series_recurrence (a := a * q ^ n) hb0 hq0 hq hz hb
  have hC := qPochhammer_ne_zero_of_qDenominatorRegular hq ha n
  have hD := one_sub_ne_zero_of_qDenominatorRegular ha
  have hfactor : 1 - a * q / b * q ^ n ≠ 0 := by
    intro he
    exact ha _ (by simp) n (sub_eq_zero.mp he).symm
  have hshift := qPochhammer_succ' (a * q / b) q n
  have he : a * q / b * q = a * q ^ 2 / b := by ring
  rw [he, qPochhammer_succ] at hshift
  dsimp [weight, term]
  rw [qPochhammer_succ, qPochhammer_succ, qPochhammer_succ,
    show a * q ^ (n + 1) = a * q ^ n * q by ring]
  rw [show 1 - a * q ^ n * q / b = 1 - a * q / b * q ^ n by ring] at hc
  rw [show 1 - a * q ^ n * q = 1 - a * q * q ^ n by ring,
    show 1 - a * q ^ n * z * q / b = 1 - (a * z * q / b) * q ^ n by ring,
    show a * q ^ n * q / b = (a * q / b) * q ^ n by ring] at hc
  generalize qPochhammer (a * q) q n = A
  generalize qPochhammer (a * z * q / b) q n = B
  generalize qPochhammer (a * q / b) q n = C at hC hshift ⊢
  generalize qPochhammer (a * q ^ 2 / b) q n = D at hshift ⊢
  generalize a * q / b = r at hD hfactor hshift hc ⊢
  generalize 1 - a * q * q ^ n = U at hc ⊢
  generalize 1 - a * z * q / b * q ^ n = V at hc ⊢
  generalize 1 - r * q ^ n = W at hfactor hshift hc ⊢
  have hDEq : D = C * W / (1 - r) := by
    apply (eq_div_iff hD).mpr
    linear_combination -hshift
  rw [hDEq]
  field_simp [hC, hfactor, hD]
  linear_combination A * B * hc

/-- Fine's first expansion obtained from the telescoping upper-parameter recurrence. -/
lemma expansion {a b q z : ℂ} (hb0 : b ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hb : QDenominatorRegular [b * q] q)
    (ha : QDenominatorRegular [a * q / b] q) :
    series a b q z = (-(1 - b) * (a * q / b) / (1 - a * q / b)) *
      (∑' n : ℕ, term a b q z n) +
      (qPochhammerInf (a * q) q * qPochhammerInf (a * z * q / b) q /
        qPochhammerInf (a * q / b) q) * series 0 b q z := by
  let K := -(1 - b) * (a * q / b) / (1 - a * q / b)
  let H := qPochhammerInf (a * q) q * qPochhammerInf (a * z * q / b) q /
    qPochhammerInf (a * q / b) q
  have ht := (summable_norm_term (z := z) hq ha).of_norm
  have hsum := ht.mul_left K
  have hrem : Tendsto (fun N : ℕ => weight a b q z N * series (a * q ^ N) b q z)
      atTop (𝓝 (H * series 0 b q z)) :=
    (tendsto_weight hq ha).mul (tendsto_series_upper_shift hq0 hq hz hb)
  have hs : HasSum (fun n : ℕ => K * term a b q z n)
      (series a b q z - H * series 0 b q z) := by
    apply (hasSum_iff_tendsto_nat_of_summable_norm hsum.norm).mpr
    have he (N : ℕ) : ∑ n ∈ range N, K * term a b q z n =
        weight a b q z 0 * series (a * q ^ 0) b q z -
          weight a b q z N * series (a * q ^ N) b q z := by
      simp_rw [K, ← weight_series_sub_succ hb0 hq0 hq hz hb ha]
      exact sum_range_sub' (fun n => weight a b q z n * series (a * q ^ n) b q z) N
    simp_rw [he]
    simpa [weight] using (tendsto_const_nhds (x := series a b q z)).sub hrem
  have he := hs.tsum_eq
  rw [tsum_mul_left] at he
  change series a b q z = K * (∑' n, term a b q z n) + H * series 0 b q z
  linear_combination -he

end DLMF.QHypergeometric.FineFirstExpansion

namespace DLMF.QHypergeometric

/-- Fine's first expansion of `2φ1(q,aq;bq;q,z)` with first-series denominator
`(aq²/b;q)ₙ`. The denominator `(azq²/b;q)ₙ` printed in DLMF 17.6.9 has an extra `z`;
see `fine_first_transformation_counterexample`. -/
@[dlmf 17.6.E9 "corrects printed first-series denominator to (aq²/b;q)_n"]
theorem heine_fine_expansion {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : QDenominatorRegular [b*q,a*q/b] q) :
    qPhi [q,a*q] [b*q] q z= -(1-b)*(a*q/b)/(1-a*q/b)*
      (∑' n : ℕ, qPochhammerList [a*q,a*z*q/b] q n*q^n/qPochhammer (a*q^2/b) q n)+
      qPochhammerListInf [a*q,a*z*q/b] q/qPochhammerInf (a*q/b) q*qPhi [q,0] [b*q] q z := by
  by_cases hq0 : q = 0
  · subst q
    simp [qPochhammerListInf, qPochhammerInf]
  have hB : QDenominatorRegular [b * q] q := by
    intro x hx n
    exact hd x (by simp only [List.mem_singleton] at hx; simp [hx]) n
  have hA : QDenominatorRegular [a * q / b] q := by
    intro x hx n
    exact hd x (by simp only [List.mem_singleton] at hx; simp [hx]) n
  have H := FineFirstExpansion.expansion (a := a) hb0 hq0 hq hz hB hA
  simpa only [RogersFine.series, FineFirstExpansion.term, qPochhammerList,
    qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, zero_mul] using H


end DLMF.QHypergeometric
