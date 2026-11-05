/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.SearsTransformation
public import DLMF.QHypergeometric.BasicSummations.RogersFine

/-!
# Nonterminating limits of Sears' finite transformation

The terminating parameter `q⁻ᴺ` is paired with the lower parameter `q^(1-N)/z`.
Their ratio, including the argument factor `qᵏ`, tends to `zᵏ`. Reversing the two finite
shifted factorials gives a uniform geometric bound for this limit when `‖z‖ < 1`.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.SearsLimit

open SearsTransformation

/-- The lower parameter paired with the terminating upper parameter `q⁻ᴺ`. -/
def movingParameter (z q : ℂ) (N : ℕ) : ℂ := q * q⁻¹ ^ N / z

/-- The ratio of the two moving shifted factorials in the terminating Sears sum. -/
def ratio (z q : ℂ) (N k : ℕ) : ℂ :=
  if k ≤ N then z ^ k * qPochhammer (q ^ (N + 1 - k)) q k /
    qPochhammer (z * q ^ (N - k)) q k else 0

/-- Reversal gives the normalized moving-parameter ratio on its finite support. -/
lemma ratio_eq {z q : ℂ} (hz0 : z ≠ 0) (hq0 : q ≠ 0) {N k : ℕ} (hk : k ≤ N) :
    ratio z q N k = qPochhammer (q⁻¹ ^ N) q k /
      qPochhammer (movingParameter z q N) q k * q ^ k := by
  have hqN : q⁻¹ ^ N ≠ 0 := pow_ne_zero N (inv_ne_zero hq0)
  have hf : movingParameter z q N ≠ 0 := div_ne_zero (mul_ne_zero hq0 hqN) hz0
  have hNk : q ^ (N - k) * q ^ k = q ^ N := by rw [← pow_add, Nat.sub_add_cancel hk]
  have he1 : q * q⁻¹ ^ k / (q⁻¹ ^ N) = q ^ (N + 1 - k) := by
    rw [show N + 1 - k = (N - k) + 1 by omega, pow_succ]
    simp only [inv_pow]
    field_simp
    linear_combination -hNk
  have he2 : q * q⁻¹ ^ k / movingParameter z q N = z * q ^ (N - k) := by
    dsimp [movingParameter]
    simp only [inv_pow]
    field_simp
    linear_combination -hNk
  have he3 : (-(q⁻¹ ^ N)) / (-movingParameter z q N) * q = z := by
    dsimp [movingParameter]
    field_simp
  rw [ratio, ite_eq_left hk, qPochhammer_reverse' hqN hq0 k,
    qPochhammer_reverse' hf hq0 k, he1, he2]
  rw [mul_div_mul_right _ _ (pow_ne_zero (k.choose 2) hq0), mul_div_mul_comm]
  rw [← div_pow, mul_assoc, ← mul_pow, he3]
  ring

/-- The moving denominator is nonzero through its terminating index. -/
lemma qPochhammer_movingParameter_ne_zero {z q : ℂ} (hz0 : z ≠ 0) (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (N : ℕ) :
    qPochhammer (movingParameter z q N) q N ≠ 0 := by
  have hf : movingParameter z q N ≠ 0 :=
    div_ne_zero (mul_ne_zero hq0 (pow_ne_zero N (inv_ne_zero hq0))) hz0
  have he : q * q⁻¹ ^ N / movingParameter z q N = z := by
    dsimp [movingParameter]
    field_simp
  rw [qPochhammer_reverse' hf hq0 N, he]
  exact mul_ne_zero (mul_ne_zero
    (qPochhammer_ne_zero_of_factors hq (one_sub_mul_pow_ne_zero_of_norm hz hq) N)
    (pow_ne_zero N (neg_ne_zero.mpr hf))) (pow_ne_zero _ hq0)

/-- The inverses of the finite products `(zqᴹ;q)ₖ` are bounded uniformly in both indices. -/
lemma exists_norm_inv_qPochhammer_shift_le {z q : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M k : ℕ, ‖(qPochhammer (z * q ^ M) q k)⁻¹‖ ≤ C := by
  have hI := qPochhammerInf_ne_zero_of_norm_lt_one hz hq
  obtain ⟨B, hB⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq hI
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let E := Real.exp (‖z‖ / (1 - ‖q‖))
  refine ⟨E * B, by positivity, ?_⟩
  intro M k
  have hM := qPochhammer_ne_zero_of_factors hq (one_sub_mul_pow_ne_zero_of_norm hz hq) M
  have hMk := qPochhammer_ne_zero_of_factors hq (one_sub_mul_pow_ne_zero_of_norm hz hq) (M + k)
  have he : (qPochhammer (z * q ^ M) q k)⁻¹ =
      qPochhammer z q M * (qPochhammer z q (M + k))⁻¹ := by
    rw [qPochhammer_add]
    field_simp
  rw [he, norm_mul]
  exact mul_le_mul (norm_qPochhammer_le_exp hq M) (hB (M + k))
    (norm_nonneg _) (by positivity)

/-- The moving ratios admit a fixed geometric bound. -/
lemma exists_norm_ratio_le {z q : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N k : ℕ, ‖ratio z q N k‖ ≤ C * ‖z‖ ^ k := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_inv_qPochhammer_shift_le hq hz
  let A := Real.exp (1 / (1 - ‖q‖))
  refine ⟨A * B, by positivity, ?_⟩
  intro N k
  by_cases hk : k ≤ N
  · have hA : ‖qPochhammer (q ^ (N + 1 - k)) q k‖ ≤ A := by
      refine (norm_qPochhammer_le_exp hq k).trans (Real.exp_le_exp.mpr ?_)
      apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hq.le)
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg q) hq.le
    have H := mul_le_mul hA (hB (N - k) k) (norm_nonneg _) (by positivity)
    have H' := mul_le_mul_of_nonneg_left H (pow_nonneg (norm_nonneg z) k)
    simpa only [ratio, ite_eq_left hk, div_eq_mul_inv, norm_mul, norm_pow, mul_assoc,
      mul_comm, mul_left_comm] using H'
  · simp only [ratio, ite_eq_right hk, norm_zero]
    positivity

/-- For fixed index the moving shifted-factorial ratio tends to the classical argument power.
-/
lemma tendsto_ratio {z q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    Tendsto (fun N : ℕ => ratio z q N k) atTop (𝓝 (z ^ k)) := by
  have hpow : Tendsto (fun N : ℕ => q ^ (N - k)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (tendsto_sub_atTop_nat k)
  have hpow' : Tendsto (fun N : ℕ => q ^ (N + 1 - k)) atTop (𝓝 (0 : ℂ)) := by
    have H : Tendsto (fun N : ℕ => q ^ (N - k) * q) atTop (𝓝 (0 : ℂ)) := by
      simpa using hpow.mul_const q
    refine H.congr' ?_
    filter_upwards [eventually_ge_atTop k] with N hN
    rw [show N + 1 - k = (N - k) + 1 by omega, pow_succ]
  have hnum := (continuous_qPochhammer q k).tendsto 0 |>.comp hpow'
  have hpz : Tendsto (fun N : ℕ => z * q ^ (N - k)) atTop (𝓝 (0 : ℂ)) := by
    simpa using hpow.const_mul z
  have hden := (continuous_qPochhammer q k).tendsto 0 |>.comp hpz
  have H := (tendsto_const_nhds (x := z ^ k)).mul (hnum.div hden (by simp [qPochhammer_zero_param]))
  simp only [qPochhammer_zero_param, div_one, mul_one, Function.comp_def, Pi.div_apply] at H
  refine H.congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  simp only [ratio, ite_eq_left hN]
  ring

/-- The fixed coefficient in a three-phi-two series. -/
def coefficient (a b c d e q : ℂ) (k : ℕ) : ℂ :=
  qPochhammer a q k * qPochhammer b q k * qPochhammer c q k /
    (qPochhammer d q k * qPochhammer e q k * qPochhammer q q k)

/-- The three-phi-two series has no residual integer phase. -/
lemma qPhi_eq_tsum (a b c d e q z : ℂ) :
    qPhi [a, b, c] [d, e] q z = ∑' k, coefficient a b c d e q k * z ^ k := by
  unfold qPhi
  apply tsum_congr
  intro k
  simp [qPhiTerm, qPhiExponent, qPochhammerList, coefficient, mul_assoc]

/-- Fixed regular lower parameters give a bounded three-phi-two coefficient sequence. -/
lemma exists_norm_coefficient_le {a b c d e q : ℂ} (hq : ‖q‖ < 1)
    (hde : QDenominatorRegular [d, e] q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖coefficient a b c d e q k‖ ≤ C := by
  have hD : qPochhammerInf d q ≠ 0 := qPochhammerInf_ne_zero hq
    fun j h => hde d (by simp) j (sub_eq_zero.mp h).symm
  have hE : qPochhammerInf e q ≠ 0 := qPochhammerInf_ne_zero hq
    fun j h => hde e (by simp) j (sub_eq_zero.mp h).symm
  have hQ := qPochhammerInf_ne_zero_of_norm_lt_one hq hq
  have ht := (((tendsto_qPochhammer (w := a) hq).mul
    (tendsto_qPochhammer (w := b) hq)).mul (tendsto_qPochhammer (w := c) hq)).div
      (((tendsto_qPochhammer (w := d) hq).mul (tendsto_qPochhammer (w := e) hq)).mul
        (tendsto_qPochhammer (w := q) hq)) (mul_ne_zero (mul_ne_zero hD hE) hQ)
  obtain ⟨C, hC⟩ := ht.norm.bddAbove_range
  have hbound (k : ℕ) : ‖coefficient a b c d e q k‖ ≤ C := hC ⟨k, rfl⟩
  exact ⟨C, (norm_nonneg _).trans (hbound 0), hbound⟩

/-- A terminating Sears sum with a paired moving lower parameter tends to three-phi-two. -/
lemma tendsto_searsSum {a b c d e q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) (hde : QDenominatorRegular [d, e] q) :
    Tendsto (fun N : ℕ => searsSum q N a b c d e (movingParameter z q N)) atTop
      (𝓝 (qPhi [a, b, c] [d, e] q z)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_coefficient_le (a := a) (b := b) (c := c) hq hde
  obtain ⟨B, hB0, hB⟩ := exists_norm_ratio_le hq hz
  have hterm (k : ℕ) := (tendsto_ratio (z := z) hq k).const_mul (coefficient a b c d e q k)
  have H := tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (C * B)) hterm
    (Eventually.of_forall fun N k => by
      rw [norm_mul]
      exact (mul_le_mul (hC k) (hB N k) (norm_nonneg _) hC0).trans_eq (by ring))
  have he (N : ℕ) : (∑' k, coefficient a b c d e q k * ratio z q N k) =
      searsSum q N a b c d e (movingParameter z q N) := by
    rw [tsum_eq_sum (s := range (N + 1))]
    · apply sum_congr rfl
      intro k hk
      rw [ratio_eq hz0 hq0 (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      simp only [coefficient, div_eq_mul_inv, mul_inv_rev]
      ring
    · intro k hk
      have hNk : ¬ k ≤ N := by simp only [Finset.mem_range, not_lt] at hk; omega
      simp only [ratio, ite_eq_right hNk, mul_zero]
  simpa only [he, ← qPhi_eq_tsum] using H

/-- The last two lower parameters of a terminating Sears sum may be interchanged. -/
lemma searsSum_swap_last_lower (q : ℂ) (N : ℕ) (a b c d e f : ℂ) :
    searsSum q N a b c d e f = searsSum q N a b c d f e := by
  unfold searsSum
  apply sum_congr rfl
  intro k hk
  congr 2
  ring

/-- Cancellation of the moving product in the first finite Sears transformation. -/
lemma first_finite_cleared {a b c d e q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0)
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) (he : ‖e / a‖ < 1)
    (hbal : d * e = a * b * c * z) (hreg : QDenominatorRegular [d, e, a * z] q) (N : ℕ) :
    qPochhammer e q N * qPochhammer z q N *
        searsSum q N a b c d e (movingParameter z q N) =
      qPochhammer (e / a) q N * qPochhammer (a * z) q N *
        searsSum q N a (d / b) (d / c) d (a * z) (movingParameter (e / a) q N) := by
  let f := movingParameter z q N
  have hQ : q⁻¹ ^ N ≠ 0 := pow_ne_zero N (inv_ne_zero hq0)
  have hf : f ≠ 0 := div_ne_zero (mul_ne_zero hq0 hQ) hz0
  have hw : e / a ≠ 0 := div_ne_zero he0 ha0
  have hbal' : d * e * f = a * b * c * q * q⁻¹ ^ N := by
    dsimp [f, movingParameter]
    rw [hbal]
    field_simp
  have h₁ : a * q * q⁻¹ ^ N / e = movingParameter (e / a) q N := by
    dsimp [movingParameter]
    field_simp
  have h₂ : a * q * q⁻¹ ^ N / f = a * z := by
    dsimp [f, movingParameter]
    field_simp
  have hnonzero (x : ℂ) (hx : x ∈ [d, e, a * z]) : qPochhammer x q N ≠ 0 :=
    qPochhammer_ne_zero_of_factors hq
      (fun j h => hreg x hx j (sub_eq_zero.mp h).symm) N
  have hF := qPochhammer_movingParameter_ne_zero hz0 hq0 hq hz N
  have hW := qPochhammer_movingParameter_ne_zero hw hq0 hq he N
  have H := searsSum_transformation_first N hq0 hq ha0 hb0 hc0 hd0 he0 hf hbal'
    (hnonzero d (by simp)) (hnonzero e (by simp)) hF
    (by simpa only [h₁] using hW) (by simpa only [h₂] using hnonzero (a * z) (by simp))
  rw [h₁, h₂, searsSum_swap_last_lower q N a (d / b) (d / c) d
    (movingParameter (e / a) q N) (a * z)] at H
  have hrF := qPochhammer_reverse' hf hq0 N
  have hrFa := qPochhammer_reverse' (div_ne_zero hf ha0) hq0 N
  have heF : q * q⁻¹ ^ N / f = z := by dsimp [f, movingParameter]; field_simp
  have heFa : q * q⁻¹ ^ N / (f / a) = a * z := by
    dsimp [f, movingParameter]
    field_simp
  rw [heF] at hrF
  rw [heFa] at hrFa
  rw [hrF, hrFa] at H
  have hp : a ^ N * (-(f / a)) ^ N = (-f) ^ N := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hm : (-f) ^ N * q ^ N.choose 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero N (neg_ne_zero.mpr hf)) (pow_ne_zero _ hq0)
  apply mul_left_cancel₀ hm
  linear_combination H +
    (qPochhammer (e / a) q N * qPochhammer (a * z) q N * q ^ N.choose 2 *
      searsSum q N a (d / b) (d / c) d (a * z) (movingParameter (e / a) q N)) * hp

/-- The first nonterminating Sears transformation, obtained as a dominated finite-sum limit.
-/
lemma first_transformation {a b c d e q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0)
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) (he : ‖e / a‖ < 1)
    (hbal : d * e = a * b * c * z) (hreg : QDenominatorRegular [d, e, a * z] q) :
    qPhi [a, b, c] [d, e] q z =
      (qPochhammerInf (e / a) q * qPochhammerInf (a * z) q /
        (qPochhammerInf e q * qPochhammerInf z q)) *
      qPhi [a, d / b, d / c] [d, a * z] q (e / a) := by
  have hde : QDenominatorRegular [d, e] q := by
    intro x hx j
    exact hreg x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) j
  have hdaz : QDenominatorRegular [d, a * z] q := by
    intro x hx j
    exact hreg x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) j
  have hL := ((tendsto_qPochhammer (w := e) hq).mul (tendsto_qPochhammer (w := z) hq)).mul
    (tendsto_searsSum (a := a) (b := b) (c := c) hq0 hq hz0 hz hde)
  have hR := ((tendsto_qPochhammer (w := e / a) hq).mul
    (tendsto_qPochhammer (w := a * z) hq)).mul
      (tendsto_searsSum (a := a) (b := d / b) (c := d / c) hq0 hq
        (div_ne_zero he0 ha0) he hdaz)
  have hprod := tendsto_nhds_unique hL (hR.congr fun N =>
    (first_finite_cleared hq0 hq ha0 hb0 hc0 hd0 he0 hz0 hz he hbal hreg N).symm)
  have hEI : qPochhammerInf e q ≠ 0 := qPochhammerInf_ne_zero hq
    fun j h => hreg e (by simp) j (sub_eq_zero.mp h).symm
  have hZI := qPochhammerInf_ne_zero_of_norm_lt_one hz hq
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero hEI hZI)).mpr
  linear_combination hprod

/-- Two zero parameters in each list cancel in a three-phi-two series. -/
lemma qPhi_three_two_zero_parameters (a q z : ℂ) :
    qPhi [a, 0, 0] [0, 0] q z = qPhi [a] [] q z := by
  unfold qPhi
  apply tsum_congr
  intro k
  simp [qPhiTerm, qPhiExponent, qPochhammerList, qPochhammer_zero_param]

/-- The second finite Sears transformation with its moving parameter in the first lower slot.
-/
lemma second_finite_cleared {a b c d e q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0)
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) (hb : ‖b‖ < 1)
    (hbal : d * e = a * b * c * z)
    (hreg : QDenominatorRegular [d, e, z, d * e / (a * b), d * e / (b * c)] q) (N : ℕ) :
    qPochhammer d q N * qPochhammer e q N * qPochhammer z q N *
        searsSum q N a b c d e (movingParameter z q N) =
      qPochhammer b q N * qPochhammer (d * e / (a * b)) q N *
        qPochhammer (d * e / (b * c)) q N * searsSum q N (d / b) (e / b) z
          (d * e / (a * b)) (d * e / (b * c)) (movingParameter b q N) := by
  let f := movingParameter z q N
  have hf : f ≠ 0 := div_ne_zero (mul_ne_zero hq0
    (pow_ne_zero N (inv_ne_zero hq0))) hz0
  have hbal' : f * d * e = b * a * c * q * q⁻¹ ^ N := by
    calc f * d * e = (d * e) * f := by ring
      _ = _ := by rw [hbal]; dsimp [f, movingParameter]; field_simp
  have hz' : d * e / (b * a * c) = z := by
    field_simp
    linear_combination hbal
  have hv : d * e / (b * a) = d * e / (a * b) := by ring
  have hnonzero (x : ℂ) (hx : x ∈ [d, e, z, d * e / (a * b), d * e / (b * c)]) :
      qPochhammer x q N ≠ 0 := qPochhammer_ne_zero_of_factors hq
        (fun j h => hreg x hx j (sub_eq_zero.mp h).symm) N
  have hF := qPochhammer_movingParameter_ne_zero hz0 hq0 hq hz N
  have hB := qPochhammer_movingParameter_ne_zero hb0 hq0 hq hb N
  have H := searsSum_transformation_second N hq0 hq hb0 ha0 hc0 hf hd0 he0 hbal'
    hF (hnonzero d (by simp)) (hnonzero e (by simp))
    (by simpa only [hv] using hnonzero (d * e / (a * b)) (by simp))
    (hnonzero (d * e / (b * c)) (by simp)) hB
  rw [hv, hz'] at H
  have hs : searsSum q N b a c f d e = searsSum q N a b c d e f := by
    unfold searsSum
    exact sum_congr rfl fun k _ => by ring
  rw [hs] at H
  exact H

/-- The second nonterminating Sears transformation follows from the same dominated finite limit.
-/
lemma second_transformation {a b c d e q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e ≠ 0)
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) (hb : ‖b‖ < 1)
    (hbal : d * e = a * b * c * z)
    (hreg : QDenominatorRegular [d, e, z, d * e / (a * b), d * e / (b * c)] q) :
    qPhi [a, b, c] [d, e] q z =
      (qPochhammerInf b q * qPochhammerInf (d * e / (a * b)) q *
        qPochhammerInf (d * e / (b * c)) q /
        (qPochhammerInf d q * qPochhammerInf e q * qPochhammerInf z q)) *
      qPhi [d / b, e / b, z] [d * e / (a * b), d * e / (b * c)] q b := by
  have hde : QDenominatorRegular [d, e] q := by
    intro x hx j
    exact hreg x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) j
  have hV : QDenominatorRegular [d * e / (a * b), d * e / (b * c)] q := by
    intro x hx j
    exact hreg x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) j
  have hL := (((tendsto_qPochhammer (w := d) hq).mul
    (tendsto_qPochhammer (w := e) hq)).mul (tendsto_qPochhammer (w := z) hq)).mul
      (tendsto_searsSum (a := a) (b := b) (c := c) hq0 hq hz0 hz hde)
  have hR := (((tendsto_qPochhammer (w := b) hq).mul
    (tendsto_qPochhammer (w := d * e / (a * b)) hq)).mul
      (tendsto_qPochhammer (w := d * e / (b * c)) hq)).mul
        (tendsto_searsSum (a := d / b) (b := e / b) (c := z) hq0 hq hb0 hb hV)
  have hprod := tendsto_nhds_unique hL (hR.congr fun N =>
    (second_finite_cleared hq0 hq ha0 hb0 hc0 hd0 he0 hz0 hz hb hbal hreg N).symm)
  have hDI : qPochhammerInf d q ≠ 0 := qPochhammerInf_ne_zero hq
    fun j h => hreg d (by simp) j (sub_eq_zero.mp h).symm
  have hEI : qPochhammerInf e q ≠ 0 := qPochhammerInf_ne_zero hq
    fun j h => hreg e (by simp) j (sub_eq_zero.mp h).symm
  have hZI := qPochhammerInf_ne_zero_of_norm_lt_one hz hq
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero hDI hEI) hZI)).mpr
  linear_combination hprod

/-- The remaining upper parameter may occupy the middle slot after cancelling zero pairs. -/
lemma qPhi_three_two_zero_parameters_middle (a q z : ℂ) :
    qPhi [0, a, 0] [0, 0] q z = qPhi [a] [] q z := by
  unfold qPhi
  apply tsum_congr
  intro k
  simp [qPhiTerm, qPhiExponent, qPochhammerList, qPochhammer_zero_param]

end DLMF.QHypergeometric.SearsLimit
