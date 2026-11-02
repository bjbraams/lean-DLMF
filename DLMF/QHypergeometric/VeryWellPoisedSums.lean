/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.HigherSummations

/-!
# Nonterminating very-well-poised `₆φ₅` and `₄φ₃` sums (DLMF 17.7.15, 17.7.7)

This file proves the nonterminating very-well-poised `₆φ₅` summation of DLMF 17.7.15 from its
terminating case 17.7.16 (`six_phi_five_terminating`) by analytic continuation in `w = 1/d`, and
deduces the very-well-poised `₄φ₃` sum of DLMF 17.7.7 as its case `d = √a`.

## Main results

* `eventually_mul_pow_ne_one_nhdsNE`, `eventually_mul_pow_ne_one_nhds`: avoiding the lattice
  `{q^{-j}}` near a point.
* `six_phi_five_sum`: the nonterminating very-well-poised `₆φ₅` sum (DLMF 17.7.15).
* `four_phi_three_sum`: the very-well-poised `₄φ₃` sum (DLMF 17.7.7).

## Implementation notes

After multiplication by `(aqw;q)_∞`, the series and the product side are holomorphic in `w`
on the disk `|w| < |bc/(aq)|`: the factor `(d;q)_k (aq/(bcd))^k` of the `k`-th term is the
polynomial `∏_{j<k} (w - q^j)` times `(aq/(bc))^k`. At `w = q^n` the series terminates and the
two sides agree by 17.7.16; the points `q^n` accumulate at `w = 0`.

The `₄φ₃` sum is the case `d = √a` of the `₆φ₅` sum when `√a` avoids the lattice `{q^{-j}}`.
For `√a = q^{-j}` the `₆φ₅` series has vanishing denominators; there the identity follows by
continuity in `r = √a`, after clearing the lower parameters by their infinite products.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set DLMF.QSeries
open scoped Topology
namespace DLMF.QHypergeometric

/-- The polynomial `∏_{j<k} (w - q^j)`, equal to `(1/w;q)_k w^k` for `w ≠ 0`. -/
private def lowerPoly (q w : ℂ) (k : ℕ) : ℂ := ∏ j ∈ range k, (w - q^j)

private lemma lowerPoly_pow {q : ℂ} (hq0 : q ≠ 0) (n k : ℕ) :
    lowerPoly q (q^n) k = q^(n*k) * qPochhammer (q^(-(n:ℤ))) q k := by
  induction k with
  | zero => simp [lowerPoly, qPochhammer_zero]
  | succ k ih =>
    have h1 : lowerPoly q (q^n) (k+1) = lowerPoly q (q^n) k * (q^n - q^k) := by
      simp only [lowerPoly, prod_range_succ]
    have h2 : q^n * (1 - q^(-(n:ℤ)) * q^k) = q^n - q^k := by
      rw [mul_sub, mul_one, ← mul_assoc, ← zpow_natCast q n, ← zpow_add₀ hq0]; simp
    rw [h1, ih, qPochhammer_succ, ← h2, show n*(k+1) = n*k + n by ring, pow_add]
    ring

private lemma lowerPoly_inv {d q : ℂ} (hd : d ≠ 0) (k : ℕ) :
    lowerPoly q d⁻¹ k = qPochhammer d q k * d⁻¹^k := by
  induction k with
  | zero => simp [lowerPoly, qPochhammer_zero]
  | succ k ih =>
    have h1 : lowerPoly q d⁻¹ (k+1) = lowerPoly q d⁻¹ k * (d⁻¹ - q^k) := by
      simp only [lowerPoly, prod_range_succ]
    rw [h1, ih, qPochhammer_succ, pow_succ]
    field_simp

private lemma norm_lowerPoly_le {q w : ℂ} {ρ : ℝ} (hw : ‖w‖ ≤ ρ) (k : ℕ) :
    ‖lowerPoly q w k‖ ≤ ∏ j ∈ range k, (ρ + ‖q‖^j) := by
  unfold lowerPoly
  refine (Finset.norm_prod_le _ _).trans ?_
  gcongr with j
  refine (norm_sub_le _ _).trans ?_
  rw [norm_pow]
  linarith

private lemma summable_lowerPoly_bound {q z : ℂ} {ρ : ℝ} (hq : ‖q‖ < 1) (hρ : 0 < ρ)
    (hz0 : z ≠ 0) (hρz : ρ * ‖z‖ < 1) :
    Summable fun k : ℕ => (∏ j ∈ range k, (ρ + ‖q‖^j)) * ‖z‖^k := by
  refine summable_of_ratio_test_tendsto_lt_one hρz (Eventually.of_forall fun k => ?_) ?_
  · exact mul_ne_zero (prod_ne_zero_iff.mpr fun j _ => by positivity) (by positivity)
  · have hlim : Tendsto (fun k : ℕ => (ρ + ‖q‖^k) * ‖z‖) atTop (𝓝 (ρ * ‖z‖)) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_add ρ).mul_const
        ‖z‖
      simpa using this
    refine hlim.congr fun k => ?_
    have hP : 0 < ∏ j ∈ range k, (ρ + ‖q‖^j) := prod_pos fun j _ => by positivity
    rw [prod_range_succ, pow_succ, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity), abs_of_pos (by positivity)]
    field_simp


/-- The `d`-independent coefficient of the very-well-poised `₆φ₅` series. -/
private def sixCoeff (a b c q : ℂ) (k : ℕ) : ℂ :=
  qPochhammer a q k * qPochhammer (q*Complex.sqrt a) q k * qPochhammer (-q*Complex.sqrt a) q k *
    qPochhammer b q k * qPochhammer c q k / (qPochhammer (Complex.sqrt a) q k *
    qPochhammer (-Complex.sqrt a) q k * qPochhammer (a*q/b) q k * qPochhammer (a*q/c) q k *
    qPochhammer q q k)

private lemma sixPhiTerm_mul (a b c d e q z : ℂ) (k : ℕ) (hk : qPochhammer e q k ≠ 0) :
    qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,e] q z k * qPochhammer e q k =
    sixCoeff a b c q k * qPochhammer d q k * z^k := by
  simp only [sixCoeff, qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil]
  generalize qPochhammer e q k = X at hk ⊢
  norm_num
  field_simp

/-- The `₆φ₅` series multiplied by `(aqw;q)_∞`, as a function of `w = 1/d`. -/
private def sixSeriesCleared (a b c q w : ℂ) : ℂ :=
  ∑' k, sixCoeff a b c q k * lowerPoly q w k * qPochhammerInf (a*q*w*q^k) q * (a*q/(b*c))^k

/-- The product side of the `₆φ₅` sum multiplied by `(aqw;q)_∞`, as a function of `w = 1/d`. -/
private def sixProductCleared (a b c q w : ℂ) : ℂ :=
  qPochhammerListInf [a*q, a*q/(b*c)] q / qPochhammerListInf [a*q/b, a*q/c] q *
    qPochhammerInf (a*q*w/b) q * qPochhammerInf (a*q*w/c) q / qPochhammerInf (a*q/(b*c)*w) q

private lemma sixSeriesCleared_pow {a b c q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (n : ℕ)
    (hAn : ∀ k, qPochhammer (a*q^(n+1)) q k ≠ 0) :
    sixSeriesCleared a b c q (q^n) = qPochhammerInf (a*q^(n+1)) q *
      qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,q^(-(n:ℤ))]
        [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q^(n+1)] q (a*q^(n+1)/(b*c)) := by
  unfold sixSeriesCleared qPhi
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h1 := sixPhiTerm_mul a b c (q^(-(n:ℤ))) (a*q^(n+1)) q (a*q^(n+1)/(b*c)) k (hAn k)
  rw [qPochhammerInf_mul_qPochhammer hq k (a := a*q^(n+1))]
  rw [lowerPoly_pow hq0, show a*q*q^n*q^k = a*q^(n+1)*q^k by ring]
  rw [show a*q^(n+1)/(b*c) = a*q/(b*c)*q^n by ring] at h1 ⊢
  linear_combination (-qPochhammerInf (a*q^(n+1)*q^k) q) * h1

private lemma sixSeriesCleared_inv {a b c d q : ℂ} (hq : ‖q‖ < 1) (hd0 : d ≠ 0)
    (hk : ∀ k, qPochhammer (a*q/d) q k ≠ 0) :
    sixSeriesCleared a b c q d⁻¹ = qPochhammerInf (a*q/d) q *
      qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d]
        [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q (a*q/(b*c*d)) := by
  unfold sixSeriesCleared qPhi
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h1 := sixPhiTerm_mul a b c d (a*q/d) q (a*q/(b*c*d)) k (hk k)
  rw [qPochhammerInf_mul_qPochhammer hq k (a := a*q/d)]
  rw [lowerPoly_inv hd0, show a*q*d⁻¹*q^k = a*q/d*q^k by ring]
  rw [show a*q/(b*c*d) = a*q/(b*c)*d⁻¹ by field_simp] at h1 ⊢
  linear_combination (-qPochhammerInf (a*q/d*q^k) q) * h1

private lemma sixProductCleared_pow {a b c q : ℂ} (hq : ‖q‖ < 1) (n : ℕ)
    (hB : qPochhammerInf (a*q/b*q^n) q ≠ 0) (hC : qPochhammerInf (a*q/c*q^n) q ≠ 0)
    (hBC : qPochhammerInf (a*q/(b*c)*q^n) q ≠ 0) (hBn : qPochhammer (a*q/b) q n ≠ 0)
    (hCn : qPochhammer (a*q/c) q n ≠ 0) :
    sixProductCleared a b c q (q^n) = qPochhammerInf (a*q^(n+1)) q *
      (qPochhammerList [a*q,a*q/(b*c)] q n/qPochhammerList [a*q/b,a*q/c] q n) := by
  unfold sixProductCleared
  simp only [qPochhammerListInf, qPochhammerList, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [qPochhammerInf_mul_qPochhammer hq n (a := a*q), qPochhammerInf_mul_qPochhammer hq n
    (a := a*q/(b*c)), qPochhammerInf_mul_qPochhammer hq n (a := a*q/b),
    qPochhammerInf_mul_qPochhammer hq n (a := a*q/c), show a*q*q^n/b = a*q/b*q^n by ring,
    show a*q*q^n/c = a*q/c*q^n by ring, show a*q*q^n = a*q^(n+1) by ring]
  generalize qPochhammerInf (a*q/b*q^n) q = PB at hB ⊢
  generalize qPochhammerInf (a*q/c*q^n) q = PC at hC ⊢
  generalize qPochhammerInf (a*q/(b*c)*q^n) q = PD at hBC ⊢
  field_simp

private lemma sixProductCleared_inv {a b c d q : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) (hd0 : d ≠ 0)
    (hD : qPochhammerInf (a*q/d) q ≠ 0) :
    sixProductCleared a b c q d⁻¹ = qPochhammerInf (a*q/d) q *
      (qPochhammerListInf [a*q,a*q/(b*c),a*q/(b*d),a*q/(c*d)] q/
        qPochhammerListInf [a*q/b,a*q/c,a*q/d,a*q/(b*c*d)] q) := by
  unfold sixProductCleared
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [show a*q*d⁻¹/b = a*q/(b*d) by field_simp, show a*q*d⁻¹/c = a*q/(c*d) by field_simp,
    show a*q/(b*c)*d⁻¹ = a*q/(b*c*d) by field_simp]
  field_simp

/-- The nonterminating very-well-poised `6φ5` summation (DLMF 17.7.E15). -/
@[dlmf 17.7.E15]
theorem six_phi_five_sum {a b c d q : ℂ} (hq : ‖q‖<1) (hz : ‖a*q‖<‖b*c*d‖)
    (hd : QDenominatorRegular [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q (a*q/(b*c*d))=
      qPochhammerListInf [a*q,a*q/(b*c),a*q/(b*d),a*q/(c*d)] q/
        qPochhammerListInf [a*q/b,a*q/c,a*q/d,a*q/(b*c*d)] q := by
  have hbcd : b*c*d ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact (norm_nonneg _).not_gt hz
  have hb : b ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc : c ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd0 : d ≠ 0 := right_ne_zero_of_mul hbcd
  by_cases haq : a*q = 0
  · have e1 : ∀ x : ℂ, a*q/x = 0 := fun x => by rw [haq, zero_div]
    simp only [e1, qPhi_zero, qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, qPochhammerInf_zero, mul_one, div_one]
    rw [haq, qPochhammerInf_zero]
  have ha : a ≠ 0 := left_ne_zero_of_mul haq
  have hq0 : q ≠ 0 := right_ne_zero_of_mul haq
  have hregk : ∀ x : ℂ, (∀ j : ℕ, x*q^j ≠ 1) → ∀ k, qPochhammer x q k ≠ 0 :=
    fun x hx k => qPochhammer_ne_zero_of_factors hq (fun j h => hx j (sub_eq_zero.mp h).symm) k
  have hregI : ∀ x : ℂ, (∀ j : ℕ, x*q^j ≠ 1) → qPochhammerInf x q ≠ 0 :=
    fun x hx => qPochhammerInf_ne_zero hq (fun j h => hx j (sub_eq_zero.mp h).symm)
  have hsmall : ∀ x : ℂ, ‖x‖ < 1 → ∀ j : ℕ, x*q^j ≠ 1 := fun x hx j h => by
    have := norm_mul_pow_lt_one hx hq j; rw [h, norm_one] at this; exact lt_irrefl _ this
  have hshift : ∀ x : ℂ, (∀ j : ℕ, x*q^j ≠ 1) → ∀ n j : ℕ, x*q^n*q^j ≠ 1 :=
    fun x hx n j => by rw [mul_assoc, ← pow_add]; exact hx _
  have hR : ∀ j : ℕ, Complex.sqrt a*q^j ≠ 1 := hd _ (by simp)
  have hR' : ∀ j : ℕ, -Complex.sqrt a*q^j ≠ 1 := hd _ (by simp)
  have hB : ∀ j : ℕ, a*q/b*q^j ≠ 1 := hd (a*q/b) (by simp)
  have hC : ∀ j : ℕ, a*q/c*q^j ≠ 1 := hd (a*q/c) (by simp)
  have hD : ∀ j : ℕ, a*q/d*q^j ≠ 1 := hd (a*q/d) (by simp)
  have hqq : ∀ j : ℕ, q*q^j ≠ 1 := hsmall q hq
  have hz0 : a*q/(b*c) ≠ 0 := by simp [ha, hq0, hb, hc]
  have hz0p : 0 < ‖a*q/(b*c)‖ := norm_pos_iff.mpr hz0
  have hw0 : ‖d⁻¹‖ * ‖a*q/(b*c)‖ < 1 := by
    have : ‖d⁻¹‖ * ‖a*q/(b*c)‖ = ‖a*q‖/‖b*c*d‖ := by
      simp only [norm_inv, norm_div, norm_mul]; field_simp
    rw [this, div_lt_one (norm_pos_iff.mpr hbcd)]; exact hz
  obtain ⟨ρ, hw0ρ, hρz⟩ : ∃ ρ : ℝ, ‖d⁻¹‖ < ρ ∧ ρ * ‖a*q/(b*c)‖ < 1 := by
    refine ⟨(‖d⁻¹‖ + 1/‖a*q/(b*c)‖)/2, ?_, ?_⟩
    · have : ‖d⁻¹‖ < 1/‖a*q/(b*c)‖ := by rw [lt_div_iff₀ hz0p]; exact hw0
      linarith
    · rw [div_mul_eq_mul_div, add_mul, one_div, inv_mul_cancel₀ hz0p.ne', div_lt_one two_pos]
      linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hw0ρ
  -- bound on the coefficients
  have hCt : Tendsto (sixCoeff a b c q) atTop (𝓝 (qPochhammerInf a q *
      qPochhammerInf (q*Complex.sqrt a) q * qPochhammerInf (-q*Complex.sqrt a) q *
      qPochhammerInf b q * qPochhammerInf c q / (qPochhammerInf (Complex.sqrt a) q *
      qPochhammerInf (-Complex.sqrt a) q * qPochhammerInf (a*q/b) q *
      qPochhammerInf (a*q/c) q * qPochhammerInf q q))) := by
    have t := fun x : ℂ => tendsto_qPochhammer (w := x) hq
    exact ((((t a).mul (t _)).mul (t _)).mul (t b) |>.mul (t c)).div
      ((((t _).mul (t _)).mul (t _)).mul (t _) |>.mul (t q))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hregI _ hR) (hregI _ hR'))
        (hregI _ hB)) (hregI _ hC)) (hregI q hqq))
  obtain ⟨M, hM⟩ := hCt.norm.bddAbove_range
  have hCM : ∀ k, ‖sixCoeff a b c q k‖ ≤ M := fun k => hM ⟨k, rfl⟩
  have hPB : ∀ w : ℂ, ‖w‖ ≤ ρ → ∀ k : ℕ,
      ‖qPochhammerInf (a*q*w*q^k) q‖ ≤ Real.exp (‖a*q‖ * ρ / (1 - ‖q‖)) := by
    intro w hw k
    refine (norm_qPochhammerInf_le_exp hq).trans (Real.exp_le_exp.mpr ?_)
    have h1q : 0 < 1 - ‖q‖ := by linarith
    refine div_le_div_of_nonneg_right ?_ h1q.le
    rw [norm_mul, norm_mul, norm_pow]
    have : ‖q‖^k ≤ 1 := pow_le_one₀ (norm_nonneg _) hq.le
    calc ‖a*q‖ * ‖w‖ * ‖q‖^k ≤ ‖a*q‖ * ρ * 1 := by gcongr
      _ = _ := by ring
  have dG : DifferentiableOn ℂ (sixSeriesCleared a b c q) (Metric.ball 0 ρ) := by
    refine differentiableOn_tsum_of_summable_norm
      (((summable_lowerPoly_bound hq hρ0 hz0 hρz).mul_left
        (M*Real.exp (‖a*q‖ * ρ / (1 - ‖q‖))))) (fun k => ?_)
      Metric.isOpen_ball (fun k w hw => ?_)
    · intro w _
      refine DifferentiableAt.differentiableWithinAt ?_
      have h1 : DifferentiableAt ℂ (fun w => lowerPoly q w k) w := by
        unfold lowerPoly; fun_prop
      have h2 : DifferentiableAt ℂ (fun w => qPochhammerInf (a*q*w*q^k) q) w :=
        ((qPochhammerInf_analytic hq _ (mem_univ _)).differentiableAt).comp w (by fun_prop)
      exact ((h1.const_mul _).mul h2).mul_const _
    · have hw' : ‖w‖ ≤ ρ := by
        rw [Metric.mem_ball, dist_zero_right] at hw; exact hw.le
      rw [norm_mul, norm_mul, norm_mul, norm_pow]
      have := norm_lowerPoly_le (q := q) hw' k
      calc _ ≤ M * (∏ j ∈ range k, (ρ + ‖q‖^j)) * Real.exp (‖a*q‖ * ρ / (1 - ‖q‖)) *
            ‖a*q/(b*c)‖^k := by
            have hM0 : 0 ≤ M := (norm_nonneg _).trans (hCM 0)
            gcongr
            all_goals first | exact hCM k | exact hPB w hw' k
        _ = _ := by ring
  have hzw : ∀ w ∈ Metric.ball (0:ℂ) ρ, ‖a*q/(b*c)*w‖ < 1 := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    rw [norm_mul]; nlinarith [norm_nonneg w]
  have dH : DifferentiableOn ℂ (sixProductCleared a b c q) (Metric.ball 0 ρ) := by
    intro w hw
    have hA := qPochhammerInf_analytic hq
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.div ?_ ((hA _ (mem_univ _)).differentiableAt.comp w (by fun_prop))
      (qPochhammerInf_ne_zero_of_norm_lt_one (hzw w hw) hq)
    exact (((hA _ (mem_univ _)).differentiableAt.comp w (by fun_prop)).const_mul _).mul
      ((hA _ (mem_univ _)).differentiableAt.comp w (by fun_prop))
  -- the terminating case `w = q^n`
  have hev : ∀ᶠ n : ℕ in atTop, ‖a*q*q^n‖ < 1 ∧ ‖a*q/(b*c)*q^n‖ < 1 := by
    have t := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
    have t1 := (t.const_mul (a*q)).norm
    have t2 := (t.const_mul (a*q/(b*c))).norm
    simp only [mul_zero, norm_zero] at t1 t2
    exact (t1.eventually (gt_mem_nhds one_pos)).and (t2.eventually (gt_mem_nhds one_pos))
  have hGH : ∀ᶠ n : ℕ in atTop,
      sixSeriesCleared a b c q (q^n) = sixProductCleared a b c q (q^n) := by
    filter_upwards [hev] with n ⟨hn1, hn2⟩
    have hAn : ∀ j : ℕ, a*q^(n+1)*q^j ≠ 1 := by
      rw [show a*q^(n+1) = a*q*q^n by ring]; exact hsmall _ hn1
    have hdn : QDenominatorRegularThrough [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,
        a*q^(n+1)] q n := by
      simp only [QDenominatorRegularThrough, qPochhammerList, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
      exact mul_ne_zero (hregk _ hR n) (mul_ne_zero (hregk _ hR' n) (mul_ne_zero (hregk _ hB n)
        (mul_ne_zero (hregk _ hC n) (hregk _ hAn n))))
    rw [sixSeriesCleared_pow hq hq0 n (hregk _ hAn),
      six_phi_five_terminating hq0 hq n (mul_ne_zero hb hc) hdn,
      sixProductCleared_pow hq n (hregI _ (hshift _ hB n)) (hregI _ (hshift _ hC n))
        (hregI _ (hsmall _ hn2)) (hregk _ hB n) (hregk _ hC n)]
  have hfreq : ∃ᶠ w in 𝓝[≠] (0:ℂ), sixSeriesCleared a b c q w = sixProductCleared a b c q w := by
    have ht : Tendsto (fun n : ℕ => q^n) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq,
        Eventually.of_forall fun n => pow_ne_zero n hq0⟩
    exact ht.frequently hGH.frequently
  have hEq := (dG.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_frequently_eq
    (dH.analyticOnNhd Metric.isOpen_ball) (convex_ball (0:ℂ) ρ).isPreconnected
    (Metric.mem_ball_self hρ0) hfreq
  have hw0U : d⁻¹ ∈ Metric.ball (0:ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hw0ρ
  have key := hEq hw0U
  rw [sixSeriesCleared_inv hq hd0 (hregk _ hD), sixProductCleared_inv hb hc hd0 (hregI _ hD)]
    at key
  exact mul_left_cancel₀ (hregI _ hD) key


/-- Near any point `x₀`, every point other than `x₀` avoids the lattice `{q^{-j} : j ∈ ℕ}`. -/
theorem eventually_mul_pow_ne_one_nhdsNE {q : ℂ} (hq : ‖q‖ < 1) (x₀ : ℂ) :
    ∀ᶠ x in 𝓝[≠] x₀, ∀ j : ℕ, x*q^j ≠ 1 := by
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, (‖x₀‖ + 1) * ‖q‖^J < 1 := by
    have t := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul (‖x₀‖ + 1)
    rw [mul_zero] at t
    exact (t.eventually (gt_mem_nhds one_pos)).exists
  have hbig : ∀ᶠ x in 𝓝[≠] x₀, ∀ j : ℕ, J ≤ j → x*q^j ≠ 1 := by
    have hball : ∀ᶠ x in 𝓝 x₀, ‖x‖ < ‖x₀‖ + 1 := by
      have := (continuous_norm.tendsto x₀).eventually (gt_mem_nhds (lt_add_one ‖x₀‖))
      exact this
    filter_upwards [nhdsWithin_le_nhds hball] with x hx j hj h
    have h1 : ‖x*q^j‖ < 1 := by
      rw [norm_mul, norm_pow]
      calc ‖x‖ * ‖q‖^j ≤ (‖x₀‖ + 1) * ‖q‖^j := by gcongr
        _ ≤ (‖x₀‖ + 1) * ‖q‖^J :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg q) hq.le hj)
              (by positivity)
        _ < 1 := hJ
    rw [h, norm_one] at h1
    exact lt_irrefl _ h1
  have hsmall : ∀ᶠ x in 𝓝[≠] x₀, ∀ j ∈ range J, x*q^j ≠ 1 := by
    rw [eventually_all_finset]
    intro j _
    by_cases hp : x₀*q^j = 1
    · filter_upwards [self_mem_nhdsWithin] with x (hx : x ≠ x₀) h
      apply hx
      have hq0 : q^j ≠ 0 := by rintro h0; rw [h0, mul_zero] at hp; exact zero_ne_one hp
      exact mul_right_cancel₀ hq0 (h.trans hp.symm)
    · apply nhdsWithin_le_nhds
      exact ((continuous_id.mul continuous_const).continuousAt (x := x₀)).eventually_ne hp
  filter_upwards [hbig, hsmall] with x h1 h2 j
  by_cases hj : J ≤ j
  · exact h1 j hj
  · exact h2 j (mem_range.mpr (not_le.mp hj))

/-- Avoiding the lattice `{q^{-j} : j ∈ ℕ}` is an open condition. -/
theorem eventually_mul_pow_ne_one_nhds {q x₀ : ℂ} (hq : ‖q‖ < 1) (h : ∀ j : ℕ, x₀*q^j ≠ 1) :
    ∀ᶠ x in 𝓝 x₀, ∀ j : ℕ, x*q^j ≠ 1 := by
  rw [← nhdsNE_sup_pure, eventually_sup]
  exact ⟨eventually_mul_pow_ne_one_nhdsNE hq x₀, eventually_pure.mpr h⟩

private lemma sqrt_sq_eq (x : ℂ) : (Complex.sqrt x)^2 = x := by
  rw [Complex.sqrt, ← Complex.cpow_nat_mul]; norm_num

/-- The very-well-poised `₄φ₃` sum for a square-root parameter `r` off the lattice `{q^{-j}}`. -/
private lemma four_phi_three_generic {r b c q : ℂ} (hq : ‖q‖<1) (hr0 : r ≠ 0)
    (hz : ‖q*r‖ < ‖b*c‖) (hreg : ∀ j : ℕ, r*q^j ≠ 1)
    (hd : QDenominatorRegular [-r, r^2*q/b, r^2*q/c] q) :
    qPhi [r^2,-q*r,b,c] [-r,r^2*q/b,r^2*q/c] q (q*r/(b*c)) =
      qPochhammerListInf [r*Complex.sqrt q,-r*Complex.sqrt q,-r*q,q*r/b,q*r/c,r^2*q/(b*c)] q /
        qPochhammerListInf [r^2*q/b,r^2*q/c,q*r/(b*c)] q := by
  have hbc : b*c ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact (norm_nonneg _).not_gt hz
  have hb : b ≠ 0 := left_ne_zero_of_mul hbc
  have hc : c ≠ 0 := right_ne_zero_of_mul hbc
  set s := Complex.sqrt (r^2) with hsdef
  have hs : s = r ∨ s = -r := sq_eq_sq_iff_eq_or_eq_neg.mp (sqrt_sq_eq _)
  have hR' : ∀ j : ℕ, -r*q^j ≠ 1 := hd (-r) (by simp)
  have hqr : ∀ j : ℕ, q*r*q^j ≠ 1 := fun j => by
    rw [show q*r*q^j = r*q^(j+1) by ring]; exact hreg _
  have hd6 : QDenominatorRegular [s, -s, r^2*q/b, r^2*q/c, r^2*q/r] q := by
    intro x hx j
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rcases hs with h | h <;> rw [h]
      · exact hreg j
      · exact hR' j
    · rcases hs with h | h <;> rw [h]
      · exact hR' j
      · rw [neg_neg]; exact hreg j
    · exact hd _ (by simp) j
    · exact hd _ (by simp) j
    · rw [show r^2*q/r = q*r by field_simp]; exact hqr j
  have hz6 : ‖r^2*q‖ < ‖b*c*r‖ := by
    rw [norm_mul, norm_mul, norm_pow]; rw [norm_mul] at hz
    nlinarith [norm_pos_iff.mpr hr0]
  have h6 := six_phi_five_sum hq hz6 hd6
  have hregk : ∀ x : ℂ, (∀ j : ℕ, x*q^j ≠ 1) → ∀ k, qPochhammer x q k ≠ 0 :=
    fun x hx k => qPochhammer_ne_zero_of_factors hq (fun j h => hx j (sub_eq_zero.mp h).symm) k
  have hregI : ∀ x : ℂ, (∀ j : ℕ, x*q^j ≠ 1) → qPochhammerInf x q ≠ 0 :=
    fun x hx => qPochhammerInf_ne_zero hq (fun j h => hx j (sub_eq_zero.mp h).symm)
  -- the left sides
  have hL : qPhi [r^2,q*s,-q*s,b,c,r] [s,-s,r^2*q/b,r^2*q/c,r^2*q/r] q (r^2*q/(b*c*r)) =
      qPhi [r^2,-q*r,b,c] [-r,r^2*q/b,r^2*q/c] q (q*r/(b*c)) := by
    unfold qPhi
    refine tsum_congr fun k => ?_
    have e1 : qPochhammer (q*s) q k * qPochhammer (-q*s) q k =
        qPochhammer (q*r) q k * qPochhammer (-(q*r)) q k := by
      rw [neg_mul, ← qPochhammer_squared, ← qPochhammer_squared, mul_pow, mul_pow,
        sqrt_sq_eq]
    have e2 : qPochhammer s q k * qPochhammer (-s) q k =
        qPochhammer r q k * qPochhammer (-r) q k := by
      rw [← qPochhammer_squared, ← qPochhammer_squared, sqrt_sq_eq]
    have h1 := hregk _ hreg k
    have h2 := hregk _ hqr k
    simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil]
    rw [show r^2*q/r = q*r by field_simp, show r^2*q/(b*c*r) = q*r/(b*c) by field_simp]
    have h3 := hregk _ hR' k
    have h4 := hregk _ (hd (r^2*q/b) (by simp)) k
    have h5 := hregk _ (hd (r^2*q/c) (by simp)) k
    have h6 := qPochhammer_self_ne_zero hq k
    norm_num only [zpow_zero, mul_one]
    simp only [neg_mul] at e1 ⊢
    calc _ = qPochhammer (r ^ 2) q k * (qPochhammer (q * s) q k * qPochhammer (-(q * s)) q k) *
          qPochhammer b q k * qPochhammer c q k * qPochhammer r q k /
          ((qPochhammer s q k * qPochhammer (-s) q k) * qPochhammer (r ^ 2 * q / b) q k *
            qPochhammer (r ^ 2 * q / c) q k * qPochhammer (q * r) q k * qPochhammer q q k) *
          (q * r / (b * c)) ^ k := by ring
      _ = _ := by
          rw [e1, e2]
          have h2' : qPochhammer (r*q) q k ≠ 0 := by rwa [mul_comm]
          field_simp
  rw [← hL, h6]
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [show r^2*q/(b*r) = q*r/b by field_simp, show r^2*q/(c*r) = q*r/c by field_simp,
    show r^2*q/r = q*r by field_simp, show r^2*q/(b*c*r) = q*r/(b*c) by field_simp]
  have hsq : (r*Complex.sqrt q)^2 = r^2*q := by rw [mul_pow, sqrt_sq_eq]
  have hsplit : qPochhammerInf (r^2*q) q = qPochhammerInf (r*Complex.sqrt q) q *
      qPochhammerInf (-r*Complex.sqrt q) q * qPochhammerInf (-r*q) q * qPochhammerInf (q*r) q := by
    rw [qPochhammerInf_split_sq hq (a := r^2*q), neg_mul, neg_mul,
      qPochhammerInf_mul_qPochhammerInf_neg hq, hsq, mul_assoc _ (qPochhammerInf (-(r*q)) q),
      mul_comm (qPochhammerInf (-(r*q)) q), mul_comm q r, qPochhammerInf_mul_qPochhammerInf_neg hq]
    ring_nf
  have hQR : qPochhammerInf (r*q) q ≠ 0 := by rw [mul_comm]; exact hregI _ hqr
  rw [hsplit]
  field_simp

/-- A term of the `₄φ₃` series multiplied by the lower-parameter products, as a function of the
square-root parameter `r`. -/
private def fourClearedTerm (b c q r : ℂ) (k : ℕ) : ℂ :=
  qPochhammer (r^2) q k * qPochhammer (-q*r) q k * qPochhammer b q k * qPochhammer c q k *
    qPochhammerInf (-r*q^k) q * qPochhammerInf (r^2*q/b*q^k) q * qPochhammerInf (r^2*q/c*q^k) q /
    qPochhammer q q k * (q*r/(b*c))^k

/-- The lower-parameter products clearing the `₄φ₃` denominators. -/
private def fourDen (b c q r : ℂ) : ℂ :=
  qPochhammerInf (-r) q * qPochhammerInf (r^2*q/b) q * qPochhammerInf (r^2*q/c) q

/-- The product side of the `₄φ₃` sum multiplied by `fourDen`. -/
private def fourProdCleared (b c q r : ℂ) : ℂ :=
  qPochhammerListInf [r*Complex.sqrt q,-r*Complex.sqrt q,-r*q,q*r/b,q*r/c,r^2*q/(b*c)] q *
    qPochhammerInf (-r) q / qPochhammerInf (q*r/(b*c)) q

private lemma fourClearedTerm_eq {b c q r : ℂ} (hq : ‖q‖ < 1) (k : ℕ)
    (h1 : qPochhammer (-r) q k ≠ 0) (h2 : qPochhammer (r^2*q/b) q k ≠ 0)
    (h3 : qPochhammer (r^2*q/c) q k ≠ 0) :
    fourClearedTerm b c q r k = fourDen b c q r *
      qPhiTerm [r^2,-q*r,b,c] [-r,r^2*q/b,r^2*q/c] q (q*r/(b*c)) k := by
  have h4 := qPochhammer_self_ne_zero hq k
  unfold fourClearedTerm fourDen
  rw [qPochhammerInf_mul_qPochhammer hq k (a := -r),
    qPochhammerInf_mul_qPochhammer hq k (a := r^2*q/b),
    qPochhammerInf_mul_qPochhammer hq k (a := r^2*q/c)]
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil]
  norm_num only [zpow_zero, mul_one]
  generalize qPochhammer (-r) q k = X1 at h1 ⊢
  generalize qPochhammer (r^2*q/b) q k = X2 at h2 ⊢
  generalize qPochhammer (r^2*q/c) q k = X3 at h3 ⊢
  field_simp

private lemma continuousAt_fourCleared {b c q r₀ : ℂ} (hq : ‖q‖ < 1) (hb : b ≠ 0) (hc : c ≠ 0)
    (hz : ‖q*r₀‖ < ‖b*c‖) :
    ContinuousAt (fun r => ∑' k, fourClearedTerm b c q r k) r₀ := by
  have hbc : 0 < ‖b*c‖ := norm_pos_iff.mpr (mul_ne_zero hb hc)
  set δ := (‖b*c‖ - ‖q‖*‖r₀‖)/(2*(‖q‖+1)) with hδ
  have hgap : 0 < ‖b*c‖ - ‖q‖*‖r₀‖ := by rw [norm_mul] at hz; linarith
  have hδ0 : 0 < δ := div_pos hgap (by positivity)
  set R₁ := ‖r₀‖ + δ with hR₁
  have hqR : ‖q‖ * R₁ < ‖b*c‖ := by
    have : ‖q‖ * δ ≤ (‖b*c‖ - ‖q‖*‖r₀‖)/2 := by
      rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [norm_nonneg q]
    rw [hR₁]; nlinarith
  set ρ := ‖q‖ * R₁ / ‖b*c‖ with hρ
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hbc]; exact hqR
  have hρ0 : 0 ≤ ρ := by positivity
  set Y := R₁^2 + ‖q‖*R₁ + ‖b‖ + ‖c‖ + R₁ + R₁^2*‖q‖/‖b‖ + R₁^2*‖q‖/‖c‖ with hY
  set E := Real.exp (Y / (1 - ‖q‖)) with hE
  obtain ⟨C, hC⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq
    (qPochhammerInf_ne_zero_of_norm_lt_one hq hq)
  have hR0 : 0 ≤ R₁ := by positivity
  have hEP : ∀ x : ℂ, ‖x‖ ≤ Y → ∀ k, ‖qPochhammer x q k‖ ≤ E := fun x hx k =>
    (norm_qPochhammer_le_exp hq k).trans (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right hx (by linarith)))
  have hEI : ∀ x : ℂ, ‖x‖ ≤ Y → ‖qPochhammerInf x q‖ ≤ E := fun x hx =>
    (norm_qPochhammerInf_le_exp hq).trans (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right hx (by linarith)))
  have hpow : ∀ k : ℕ, ‖q‖^k ≤ 1 := fun k => pow_le_one₀ (norm_nonneg _) hq.le
  have hcI : Continuous fun x => qPochhammerInf x q :=
    continuousOn_univ.mp (qPochhammerInf_analytic hq).continuousOn
  have hcont : ContinuousOn (fun r => ∑' k, fourClearedTerm b c q r k)
      (Metric.closedBall r₀ δ) := by
    refine continuousOn_tsum (u := fun k => E^7 * C * ρ^k) (fun k => ?_)
      ((summable_geometric_of_lt_one hρ0 hρ1).mul_left _) (fun k r hr => ?_)
    · refine Continuous.continuousOn ?_
      unfold fourClearedTerm
      have h1 := continuous_qPochhammer q k
      refine (((((((h1.comp (continuous_pow 2)).mul (h1.comp (by fun_prop))).mul
        continuous_const).mul continuous_const).mul (hcI.comp (by fun_prop))).mul
        (hcI.comp (by fun_prop))).mul (hcI.comp (by fun_prop))).div_const _ |>.mul (by fun_prop)
    · have hr' : ‖r‖ ≤ R₁ := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hr
        have := norm_le_norm_add_norm_sub' r r₀
        rw [hR₁]; linarith [norm_sub_rev r r₀]
      have hb0 : 0 < ‖b‖ := norm_pos_iff.mpr hb
      have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
      have hr2 : ‖r‖^2 ≤ R₁^2 := pow_le_pow_left₀ (norm_nonneg _) hr' 2
      have hY1 : R₁^2 ≤ Y := by
        have : 0 ≤ R₁^2*‖q‖/‖b‖ := by positivity
        have : 0 ≤ R₁^2*‖q‖/‖c‖ := by positivity
        rw [hY]; nlinarith [norm_nonneg q, norm_nonneg b, norm_nonneg c]
      have hn1 : 0 ≤ R₁^2*‖q‖/‖b‖ := by positivity
      have hn2 : 0 ≤ R₁^2*‖q‖/‖c‖ := by positivity
      have hn3 : 0 ≤ ‖q‖*R₁ := by positivity
      have hqr : ‖q‖ * ‖r‖ ≤ ‖q‖ * R₁ := mul_le_mul_of_nonneg_left hr' (norm_nonneg q)
      have hR2 : 0 ≤ R₁^2 := sq_nonneg _
      have hbn := norm_nonneg b
      have hcn := norm_nonneg c
      have a1 : ‖r^2‖ ≤ Y := by rw [norm_pow]; linarith
      have a2 : ‖-q*r‖ ≤ Y := by rw [norm_mul, norm_neg]; linarith
      have a3 : ‖b‖ ≤ Y := by linarith
      have a4 : ‖c‖ ≤ Y := by linarith
      have a5 : ‖-r*q^k‖ ≤ Y := by
        rw [norm_mul, norm_neg, norm_pow]
        nlinarith [hpow k, norm_nonneg r, pow_nonneg (norm_nonneg q) k]
      have hsq : ∀ x : ℂ, 0 < ‖x‖ → ‖r^2*q/x*q^k‖ ≤ R₁^2*‖q‖/‖x‖ := by
        intro x hx
        rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow]
        have h1 : ‖r‖^2*‖q‖/‖x‖ ≤ R₁^2*‖q‖/‖x‖ := by gcongr
        have h2 : 0 ≤ ‖r‖^2*‖q‖/‖x‖ := by positivity
        nlinarith [hpow k, pow_nonneg (norm_nonneg q) k]
      have a6 : ‖r^2*q/b*q^k‖ ≤ Y := by linarith [hsq b hb0]
      have a7 : ‖r^2*q/c*q^k‖ ≤ Y := by linarith [hsq c hc0]
      have hz' : ‖q*r/(b*c)‖ ≤ ρ := by
        rw [norm_div, norm_mul, hρ]; gcongr
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      have hform : fourClearedTerm b c q r k = qPochhammer (r^2) q k * qPochhammer (-q*r) q k *
          qPochhammer b q k * qPochhammer c q k * qPochhammerInf (-r*q^k) q *
          qPochhammerInf (r^2*q/b*q^k) q * qPochhammerInf (r^2*q/c*q^k) q *
          (qPochhammer q q k)⁻¹ * (q*r/(b*c))^k := by
        unfold fourClearedTerm; ring
      rw [hform]
      simp only [norm_mul, norm_pow]
      calc _ ≤ E * E * E * E * E * E * E * C * ρ^k := by
            gcongr
            all_goals first
              | exact hEP _ a1 k | exact hEP _ a2 k | exact hEP _ a3 k | exact hEP _ a4 k
              | exact hEI _ a5 | exact hEI _ a6 | exact hEI _ a7 | exact hC k
              | exact mul_nonneg (by rw [hE]; positivity) ((norm_nonneg _).trans (hC 0))
        _ = E^7 * C * ρ^k := by ring
  exact hcont.continuousAt (Metric.closedBall_mem_nhds r₀ hδ0)

/-- The very-well-poised `4φ3` summation at argument `q√a/(bc)` (DLMF 17.7.E7). -/
@[dlmf 17.7.E7]
theorem four_phi_three_sum {a b c q : ℂ} (hq : ‖q‖<1) (hz : ‖q*Complex.sqrt a‖<‖b*c‖)
    (hd : QDenominatorRegular [-Complex.sqrt a,a*q/b,a*q/c] q) :
    qPhi [a,-q*Complex.sqrt a,b,c] [-Complex.sqrt a,a*q/b,a*q/c] q
      (q*Complex.sqrt a/(b*c))=qFourPhiThreeValue a b c q := by
  have hbc : b*c ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact (norm_nonneg _).not_gt hz
  have hb : b ≠ 0 := left_ne_zero_of_mul hbc
  have hc : c ≠ 0 := right_ne_zero_of_mul hbc
  unfold qFourPhiThreeValue
  have ha : a = (Complex.sqrt a)^2 := (sqrt_sq_eq a).symm
  generalize Complex.sqrt a = r₀ at ha hz hd ⊢
  subst ha
  by_cases hr0 : r₀ = 0
  · subst hr0
    simp [qPochhammerListInf]
  have hregI : ∀ x : ℂ, (∀ j : ℕ, x*q^j ≠ 1) → qPochhammerInf x q ≠ 0 :=
    fun x hx => qPochhammerInf_ne_zero hq (fun j h => hx j (sub_eq_zero.mp h).symm)
  have hregk : ∀ x : ℂ, (∀ j : ℕ, x*q^j ≠ 1) → ∀ k, qPochhammer x q k ≠ 0 :=
    fun x hx k => qPochhammer_ne_zero_of_factors hq (fun j h => hx j (sub_eq_zero.mp h).symm) k
  -- the identity at regular parameters, in cleared form
  have hcleared : ∀ r : ℂ, r ≠ 0 → ‖q*r‖ < ‖b*c‖ → (∀ j : ℕ, r*q^j ≠ 1) →
      QDenominatorRegular [-r, r^2*q/b, r^2*q/c] q →
      ∑' k, fourClearedTerm b c q r k = fourProdCleared b c q r := by
    intro r hr hzr hreg hdr
    have h1 := hdr (-r) (by simp)
    have h2 := hdr (r^2*q/b) (by simp)
    have h3 := hdr (r^2*q/c) (by simp)
    rw [tsum_congr fun k => fourClearedTerm_eq hq k (hregk _ h1 k) (hregk _ h2 k) (hregk _ h3 k),
      tsum_mul_left]
    change fourDen b c q r * qPhi _ _ q _ = _
    rw [four_phi_three_generic hq hr hzr hreg hdr]
    unfold fourDen fourProdCleared
    simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    have e2 := hregI _ h2
    have e3 := hregI _ h3
    field_simp
  have hcI : Continuous fun x => qPochhammerInf x q :=
    continuousOn_univ.mp (qPochhammerInf_analytic hq).continuousOn
  have hcL := continuousAt_fourCleared hq hb hc hz
  have hzr : ‖q*r₀/(b*c)‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hbc)]; exact hz
  have hcR : ContinuousAt (fourProdCleared b c q) r₀ := by
    unfold fourProdCleared
    simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    refine ContinuousAt.div (Continuous.continuousAt ?_) (hcI.comp (by fun_prop)).continuousAt
      (qPochhammerInf_ne_zero_of_norm_lt_one hzr hq)
    exact ((hcI.comp (by fun_prop)).mul ((hcI.comp (by fun_prop)).mul ((hcI.comp
      (by fun_prop)).mul ((hcI.comp (by fun_prop)).mul ((hcI.comp (by fun_prop)).mul
      (hcI.comp (by fun_prop))))))).mul (hcI.comp (by fun_prop))
  have hev : ∀ᶠ r in 𝓝[≠] r₀, ∑' k, fourClearedTerm b c q r k = fourProdCleared b c q r := by
    have e1 : ∀ᶠ r in 𝓝 r₀, r ≠ 0 := isOpen_ne.mem_nhds hr0
    have e2 : ∀ᶠ r in 𝓝 r₀, ‖q*r‖ < ‖b*c‖ :=
      ((by fun_prop : Continuous fun r : ℂ => ‖q*r‖).tendsto r₀).eventually (gt_mem_nhds hz)
    have e3 : ∀ᶠ r in 𝓝 r₀, ∀ j : ℕ, -r*q^j ≠ 1 :=
      (continuous_neg.tendsto r₀).eventually
        (eventually_mul_pow_ne_one_nhds hq (hd (-r₀) (by simp)))
    have e4 : ∀ᶠ r in 𝓝 r₀, ∀ j : ℕ, r^2*q/b*q^j ≠ 1 :=
      ((by fun_prop : Continuous fun r : ℂ => r^2*q/b).tendsto r₀).eventually
        (eventually_mul_pow_ne_one_nhds hq (hd _ (by simp)))
    have e5 : ∀ᶠ r in 𝓝 r₀, ∀ j : ℕ, r^2*q/c*q^j ≠ 1 :=
      ((by fun_prop : Continuous fun r : ℂ => r^2*q/c).tendsto r₀).eventually
        (eventually_mul_pow_ne_one_nhds hq (hd _ (by simp)))
    filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, nhdsWithin_le_nhds e3,
      nhdsWithin_le_nhds e4, nhdsWithin_le_nhds e5, eventually_mul_pow_ne_one_nhdsNE hq r₀]
      with r h1 h2 h3 h4 h5 h6
    refine hcleared r h1 h2 h6 fun x hx => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact h3
    · exact h4
    · exact h5
  have hlim := tendsto_nhds_unique (hcL.tendsto.mono_left nhdsWithin_le_nhds)
    ((hcR.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun r h => h.symm))
  have h1 := hd (-r₀) (by simp)
  have h2 := hd (r₀^2*q/b) (by simp)
  have h3 := hd (r₀^2*q/c) (by simp)
  rw [tsum_congr fun k => fourClearedTerm_eq hq k (hregk _ h1 k) (hregk _ h2 k) (hregk _ h3 k),
    tsum_mul_left] at hlim
  change fourDen b c q r₀ * qPhi _ _ q _ = _ at hlim
  have hD : fourDen b c q r₀ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hregI _ h1) (hregI _ h2)) (hregI _ h3)
  refine mul_left_cancel₀ hD (hlim.trans ?_)
  unfold fourDen fourProdCleared
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  have e2 := hregI _ h2
  have e3 := hregI _ h3
  field_simp

end DLMF.QHypergeometric
