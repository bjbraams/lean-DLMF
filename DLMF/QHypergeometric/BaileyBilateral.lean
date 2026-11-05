/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BasicSummations.Heine

/-!
# Analytic continuation for Bailey's bilateral summation

The bilateral `₂ψ₂` summation of DLMF 17.8.4 follows from the Bailey–Daum `₂φ₁`
summation by continuation in the reciprocal of an upper parameter. Multiplication by
the denominator products removes its apparent parameter singularities.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BaileyBilateral

/-- The polynomial `xⁿ(d/x;q)ₙ`, including its value at `x = 0`. -/
def reversedProduct (d q x : ℂ) (n : ℕ) : ℂ :=
  ∏ j ∈ range n, (x - d * q ^ j)

/-- The polynomial form of a shifted factorial with reciprocal parameter. -/
lemma reversedProduct_eq {d q x : ℂ} (hx : x ≠ 0) (n : ℕ) :
    reversedProduct d q x n = x ^ n * qPochhammer (d / x) q n := by
  induction n with
  | zero => simp [reversedProduct]
  | succ n ih =>
    simp only [reversedProduct, prod_range_succ] at ih ⊢
    rw [ih, qPochhammer_succ, pow_succ]
    field_simp

/-- A geometric bound for the reversed polynomial on a closed disk. -/
lemma norm_reversedProduct_le {d q x : ℂ} {r : ℝ} (hq : ‖q‖ < 1) (hr : 0 < r)
    (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖reversedProduct d q x n‖ ≤ r ^ n *
      Real.exp (‖d‖ / (r * (1 - ‖q‖))) := by
  have key : ∀ n, ‖reversedProduct d q x n‖ ≤
      r ^ n * Real.exp (‖d‖ * (∑ j ∈ range n, ‖q‖ ^ j) / r) := by
    intro n
    induction n with
    | zero => simp [reversedProduct]
    | succ n ih =>
      simp only [reversedProduct, prod_range_succ, norm_mul] at ih ⊢
      have hfactor : ‖x - d * q ^ n‖ ≤ r * Real.exp (‖d‖ * ‖q‖ ^ n / r) := by
        calc ‖x - d * q ^ n‖ ≤ ‖x‖ + ‖d * q ^ n‖ := norm_sub_le _ _
          _ ≤ r + ‖d‖ * ‖q‖ ^ n := by rw [norm_mul, norm_pow]; gcongr
          _ = r * (‖d‖ * ‖q‖ ^ n / r + 1) := by field_simp; ring
          _ ≤ r * Real.exp (‖d‖ * ‖q‖ ^ n / r) :=
            mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hr.le
      rw [sum_range_succ, mul_add, add_div, Real.exp_add, pow_succ]
      calc _ ≤ (r ^ n * Real.exp (‖d‖ * (∑ j ∈ range n, ‖q‖ ^ j) / r)) *
            (r * Real.exp (‖d‖ * ‖q‖ ^ n / r)) :=
          mul_le_mul ih hfactor (norm_nonneg _) (by positivity)
        _ = _ := by ring
  refine (key n).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  have hsum : (∑ j ∈ range n, ‖q‖ ^ j) ≤ (1 - ‖q‖)⁻¹ := by
    rw [← tsum_geometric_of_lt_one (norm_nonneg q) hq]
    exact (summable_geometric_of_lt_one (norm_nonneg q) hq).sum_le_tsum _
      (fun j _ => pow_nonneg (norm_nonneg _) j)
  calc ‖d‖ * (∑ j ∈ range n, ‖q‖ ^ j) / r ≤ ‖d‖ * (1 - ‖q‖)⁻¹ / r := by gcongr
    _ = ‖d‖ / (r * (1 - ‖q‖)) := by rw [div_mul_eq_div_mul_one_div]; ring

/-- The denominator-cleared positive terms of Bailey's bilateral series. -/
def positiveTerm (a b q x : ℂ) (n : ℕ) : ℂ :=
  qPochhammer b q n * reversedProduct 1 q x n *
    qPochhammerInf (a * q / b * q ^ n) q *
    qPochhammerInf (a * q * x * q ^ n) q *
    qPochhammerInf (q * x) q * qPochhammerInf (-a * q * x / b) q * (-a * q / b) ^ n

/-- The denominator-cleared negative terms, with negative index `-n`. -/
def negativeTerm (a b q x : ℂ) (n : ℕ) : ℂ :=
  qPochhammer (b / a) q n * reversedProduct (1 / a) q x n *
    qPochhammerInf (a * q / b) q * qPochhammerInf (a * q * x) q *
    qPochhammerInf (q * x * q ^ n) q * qPochhammerInf (-a * q * x / b) q *
    (qPochhammer (q / b) q n)⁻¹ * (-a * q / b) ^ n

/-- The entire product obtained by clearing Bailey's quotient. -/
def productSide (a b q x : ℂ) : ℂ :=
  qPochhammerInf (a * q * x / b) q *
    qPochhammerListInf [a * q ^ 2 / b ^ 2, a * q ^ 2 * x ^ 2, q ^ 2, a * q, q / a] (q ^ 2) /
      qPochhammerInf (q / b) q

/-- The common clearing product for the two halves of the bilateral series. -/
def denominator (a b q x : ℂ) : ℂ :=
  qPochhammerInf (a * q / b) q * qPochhammerInf (a * q * x) q *
    qPochhammerInf (q * x) q * qPochhammerInf (-a * q * x / b) q

/-- The cleared bilateral term, polynomial in the reciprocal parameter. -/
def term (a b q x : ℂ) : ℤ → ℂ
  | .ofNat n => positiveTerm a b q x n
  | .negSucc n => negativeTerm a b q x (n + 1)

/-- Uniform geometric bounds for both halves of the cleared bilateral series. -/
lemma norm_terms_le {a b q : ℂ} {r : ℝ} (hq : ‖q‖ < 1) (hr : 0 < r)
    (hb : qPochhammerInf (q / b) q ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, ‖x‖ ≤ r → ∀ n : ℕ,
      ‖positiveTerm a b q x n‖ ≤ C * (r * ‖a * q / b‖) ^ n ∧
      ‖negativeTerm a b q x n‖ ≤ C * (r * ‖a * q / b‖) ^ n := by
  obtain ⟨B, hB⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq hb
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let Y := ‖b‖ + ‖b / a‖ + ‖a * q / b‖ + ‖a * q‖ * r + ‖q‖ * r +
    ‖a * q / b‖ * r
  let E := Real.exp (Y / (1 - ‖q‖))
  let K₁ := Real.exp (1 / (r * (1 - ‖q‖)))
  let K₂ := Real.exp (‖(1 : ℂ) / a‖ / (r * (1 - ‖q‖)))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hK₁ : 0 ≤ K₁ := (Real.exp_pos _).le
  have hK₂ : 0 ≤ K₂ := (Real.exp_pos _).le
  have hb₀ := norm_nonneg b
  have hba₀ := norm_nonneg (b / a)
  have haqb₀ := norm_nonneg (a * q / b)
  have haq₀ := norm_nonneg (a * q)
  have hq₀ := norm_nonneg q
  have h₁ : ‖b‖ ≤ Y := by dsimp [Y]; nlinarith
  have h₂ : ‖b / a‖ ≤ Y := by dsimp [Y]; nlinarith
  have h₃ : ‖a * q / b‖ ≤ Y := by dsimp [Y]; nlinarith
  have h₄ : ‖a * q‖ * r ≤ Y := by dsimp [Y]; nlinarith
  have h₅ : ‖q‖ * r ≤ Y := by dsimp [Y]; nlinarith
  have h₆ : ‖a * q / b‖ * r ≤ Y := by dsimp [Y]; nlinarith
  have hfin : ∀ d : ℂ, ‖d‖ ≤ Y → ∀ n, ‖qPochhammer d q n‖ ≤ E := by
    intro d hd n
    exact (norm_qPochhammer_le_exp hq n).trans
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hd (by linarith)))
  have hinf : ∀ d : ℂ, ‖d‖ ≤ Y → ‖qPochhammerInf d q‖ ≤ E := by
    intro d hd
    exact (norm_qPochhammerInf_le_exp hq).trans
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hd (by linarith)))
  refine ⟨E ^ 5 * K₁ + E ^ 5 * K₂ * B, by positivity, fun x hx n => ?_⟩
  have hpow : ‖q‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hq.le
  have hqx : ‖q * x‖ ≤ Y := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg q)).trans h₅
  have haqx : ‖a * q * x‖ ≤ Y := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans h₄
  have hz : ‖-a * q * x / b‖ ≤ Y := by
    rw [show -a * q * x / b = -(a * q / b * x) by ring, norm_neg, norm_mul]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans h₆
  have hshift : ∀ d : ℂ, ‖d‖ ≤ Y → ‖d * q ^ n‖ ≤ Y := by
    intro d hd
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg _) hpow).trans hd
  have hP₁ := norm_reversedProduct_le (d := (1 : ℂ)) hq hr hx n
  have hP₂ := norm_reversedProduct_le (d := (1 : ℂ) / a) hq hr hx n
  simp only [norm_one] at hP₁
  have hpos : ‖positiveTerm a b q x n‖ ≤ E ^ 5 * K₁ * (r * ‖a * q / b‖) ^ n := by
    simp only [positiveTerm, norm_mul, norm_pow,
      show -a * q / b = -(a * q / b) by ring, norm_neg]
    calc _ ≤ E * (r ^ n * K₁) * E * E * E * E * ‖a * q / b‖ ^ n := by
          gcongr <;> first
            | exact hfin _ h₁ n | exact hinf _ (hshift _ h₃)
            | exact hinf _ (hshift _ haqx) | exact hinf _ hqx | exact hinf _ hz
      _ = _ := by rw [mul_pow]; ring
  have hneg : ‖negativeTerm a b q x n‖ ≤ E ^ 5 * K₂ * B *
      (r * ‖a * q / b‖) ^ n := by
    simp only [negativeTerm, norm_mul, norm_pow,
      show -a * q / b = -(a * q / b) by ring, norm_neg]
    calc _ ≤ E * (r ^ n * K₂) * E * E * E * E * B * ‖a * q / b‖ ^ n := by
          gcongr <;> first
            | exact hfin _ h₂ n | exact hinf _ h₃ | exact hinf _ haqx
            | exact hinf _ (hshift _ hqx) | exact hinf _ hz | exact hB n
      _ = _ := by rw [mul_pow]; ring
  constructor
  · exact hpos.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
      (by positivity))
  · exact hneg.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity))
      (by positivity))

/-- Each cleared term is entire in the reciprocal parameter. -/
lemma differentiable_term {a b q : ℂ} (hq : ‖q‖ < 1) (n : ℤ) :
    Differentiable ℂ (fun x => term a b q x n) := by
  have hP := differentiable_qPochhammerInf_left hq
  have hrev (d : ℂ) (k : ℕ) : Differentiable ℂ (fun x => reversedProduct d q x k) := by
    unfold reversedProduct
    fun_prop
  rcases n with n | n
  · simp only [term, positiveTerm]
    exact ((((((differentiable_const _).mul (hrev 1 n)).mul (differentiable_const _)).mul
      (hP.comp (by fun_prop))).mul (hP.comp (by fun_prop))).mul
      (hP.comp (by fun_prop))).mul (differentiable_const _)
  · simp only [term, negativeTerm]
    exact (((((((differentiable_const _).mul (hrev (1 / a) (n + 1))).mul
      (differentiable_const _)).mul (hP.comp (by fun_prop))).mul
      (hP.comp (by fun_prop))).mul (hP.comp (by fun_prop))).mul
      (differentiable_const _)).mul (differentiable_const _)

/-- A summable majorant on each closed disk strictly inside the convergence disk. -/
lemma exists_summable_bound {a b q : ℂ} {r : ℝ} (hq : ‖q‖ < 1) (hr : 0 < r)
    (hρ : r * ‖a * q / b‖ < 1) (hb : qPochhammerInf (q / b) q ≠ 0) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ n x, ‖x‖ ≤ r → ‖term a b q x n‖ ≤ u n := by
  obtain ⟨C, hC, hbound⟩ := norm_terms_le hq hr hb
  let ρ := r * ‖a * q / b‖
  have hρ0 : 0 ≤ ρ := mul_nonneg hr.le (norm_nonneg _)
  let u : ℤ → ℝ := fun n => match n with
    | .ofNat k => C * ρ ^ k
    | .negSucc k => C * ρ ^ (k + 1)
  refine ⟨u, ?_, ?_⟩
  · refine Summable.of_nat_of_neg_add_one ?_ ?_
    · exact (summable_geometric_of_lt_one hρ0 hρ).mul_left C
    · exact ((summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one hρ0 hρ)).mul_left C
  · intro n x hx
    rcases n with n | n
    · exact (hbound x hx n).1
    · exact (hbound x hx (n + 1)).2

/-- The cleared bilateral series is holomorphic on `|aqx/b| < 1`. -/
lemma differentiableOn_tsum_term {a b q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hb0 : b ≠ 0) (hb : qPochhammerInf (q / b) q ≠ 0) :
    DifferentiableOn ℂ (fun x => ∑' n : ℤ, term a b q x n)
      (Metric.ball 0 ‖a * q / b‖⁻¹) := by
  have hC : 0 < ‖a * q / b‖ :=
    norm_pos_iff.mpr (div_ne_zero (mul_ne_zero ha hq0) hb0)
  have hR : 0 < ‖a * q / b‖⁻¹ := inv_pos.mpr hC
  have hlocal : ∀ r : ℝ, 0 < r → r < ‖a * q / b‖⁻¹ →
      DifferentiableOn ℂ (fun x => ∑' n : ℤ, term a b q x n) (Metric.ball 0 r) := by
    intro r hr hrR
    have hρ : r * ‖a * q / b‖ < 1 := by
      have := mul_lt_mul_of_pos_right hrR hC
      simpa only [inv_mul_cancel₀ hC.ne'] using this
    obtain ⟨u, hu, hbound⟩ := exists_summable_bound hq hr hρ hb
    refine differentiableOn_tsum_of_summable_norm hu
      (fun n => (differentiable_term hq n).differentiableOn) Metric.isOpen_ball ?_
    intro n x hx
    exact hbound n x (by simpa using (Metric.mem_ball.mp hx).le)
  intro x hx
  have hxR : ‖x‖ < ‖a * q / b‖⁻¹ := by simpa using hx
  let r := (‖x‖ + ‖a * q / b‖⁻¹) / 2
  have hr : 0 < r := by dsimp [r]; linarith [norm_nonneg x]
  have hxball : x ∈ Metric.ball 0 r := by
    simp only [mem_ball_zero_iff]
    dsimp [r]
    linarith
  exact ((hlocal r hr (by dsimp [r]; linarith)).differentiableAt
    (Metric.isOpen_ball.mem_nhds hxball)).differentiableWithinAt

/-- Clearing the denominator products commutes with splitting the bilateral series. -/
lemma denominator_mul_qPsi {a b q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) (hz : ‖-a * q * x / b‖ < 1)
    (hreg : QBilateralRegular [b, 1 / x] [a * q / b, a * q * x] q) :
    denominator a b q x * qPsi [b, 1 / x] [a * q / b, a * q * x] q (-a * q * x / b) =
      (∑' n : ℕ, positiveTerm a b q x n) +
        ∑' n : ℕ, negativeTerm a b q x (n + 1) := by
  have haQ : a * q ≠ 0 := mul_ne_zero ha hq0
  have hz0 : -a * q * x / b ≠ 0 := div_ne_zero
    (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha) hq0) hx) hb
  have hprod : [b, 1 / x].prod ≠ 0 := by simp [hb, hx]
  have hlower : [a * q / b, a * q * x].prod ≠ 0 := by simp [haQ, hb, hx]
  have hr : [b, 1 / x].length ≤ [a * q / b, a * q * x].length := by simp
  have harg : [a * q / b, a * q * x].prod /
      ([b, 1 / x].prod * (-a * q * x / b)) = -a * q * x / b := by
    simp only [List.prod_cons, List.prod_nil, mul_one]
    field_simp
  rw [qPsi_split hq0 hq hreg hprod hlower hz0 hr (by rwa [harg]) (fun _ => hz), mul_add,
    ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  · refine tsum_congr fun n => ?_
    have hA := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hreg.1
      (by simp : a * q / b ∈ [a * q / b, a * q * x]) n
    have hB := qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hreg.1
      (by simp : a * q * x ∈ [a * q / b, a * q * x]) n
    simp only [qPsiTerm, qPsiExponent, qPochhammerListInt_natCast,
      qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil, sub_self, zpow_zero, zpow_natCast, mul_one]
    rw [positiveTerm, reversedProduct_eq hx]
    rw [denominator, qPochhammerInf_mul_qPochhammer hq n (a := a * q / b),
      qPochhammerInf_mul_qPochhammer hq n (a := a * q * x)]
    rw [show -a * q * x / b = (-a * q / b) * x by ring, mul_pow]
    field_simp
  · refine tsum_congr fun n => ?_
    have hqb : qPochhammer (q / b) q (n + 1) ≠ 0 :=
      qPochhammer_ne_zero_of_factors hq (fun k hk => hreg.2 b (by simp) k (by
        have hk' : q / b * q ^ k = 1 := (sub_eq_zero.mp hk).symm
        field_simp at hk'
        rw [pow_succ]
        linear_combination -hk')) (n + 1)
    have hqx : qPochhammer (q * x) q (n + 1) ≠ 0 :=
      qPochhammer_ne_zero_of_factors hq (fun k hk => hreg.2 (1 / x) (by simp) k (by
        have hk' : q * x * q ^ k = 1 := (sub_eq_zero.mp hk).symm
        rw [pow_succ]
        field_simp
        linear_combination -hk')) (n + 1)
    rw [harg]
    simp only [List.map_cons, List.map_nil, qPochhammerList, List.prod_cons, List.prod_nil,
      mul_one]
    rw [show q / (a * q / b) = b / a by field_simp,
      show q / (a * q * x) = (1 / a) / x by field_simp,
      show q / (1 / x) = q * x by field_simp]
    rw [negativeTerm, reversedProduct_eq hx]
    rw [denominator, qPochhammerInf_mul_qPochhammer hq (n + 1) (a := q * x)]
    rw [show -a * q * x / b = (-a * q / b) * x by ring, mul_pow]
    field_simp

/-- A reversed shifted-factorial identity for the first lower parameter. -/
lemma prod_pow_sub_lower {a b q : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    (∏ k ∈ range n, (q ^ (k + 1) - a * q / b)) =
      (-a * q / b) ^ n * qPochhammer (b / a) q n := by
  induction n with
  | zero => simp [qPochhammer_zero]
  | succ n ih =>
    rw [prod_range_succ, ih, qPochhammer_succ, pow_succ, pow_succ]
    field_simp; ring

/-- A reversed shifted-factorial identity for the moving lower parameter. -/
lemma prod_pow_sub_moving {a q x : ℂ} (ha : a ≠ 0) (n : ℕ) :
    (∏ k ∈ range n, (q ^ (k + 1) - a * q * x)) =
      (-a * q) ^ n * reversedProduct (1 / a) q x n := by
  induction n with
  | zero => simp [reversedProduct]
  | succ n ih =>
    simp only [reversedProduct, prod_range_succ] at ih ⊢
    rw [ih, pow_succ, pow_succ]
    field_simp; ring

/-- The cleared term as the product of two cleared `₁ψ₁` terms. -/
lemma term_eq_ramanujan_terms {a b q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0)
    (hbr : ∀ k : ℕ, b ≠ q ^ (k + 1))
    (hxr : ∀ k : ℕ, 1 / x ≠ q ^ (k + 1)) (n : ℤ) :
    term a b q x n = RamanujanPsi.term b q (-a * q * x / b) (a * q / b) n *
      RamanujanPsi.term (1 / x) q 1 (a * q * x) n *
      qPochhammerInf (q * x) q * qPochhammerInf (-a * q * x / b) q := by
  rcases n with n | n
  · simp only [term, positiveTerm, RamanujanPsi.term, Int.ofNat_eq_natCast,
      qPochhammerInt_natCast,
      zpow_natCast, one_pow, mul_one]
    rw [reversedProduct_eq hx]
    rw [show -a * q * x / b = (-a * q / b) * x by ring, mul_pow]
    ring
  · have hx0 : 1 / x ≠ 0 := one_div_ne_zero hx
    have hB := RamanujanPsi.qPochhammerInf_q_div_ne_zero hq hb hbr
    have hX := RamanujanPsi.qPochhammerInf_q_div_ne_zero hq hx0 hxr
    have hqb : qPochhammer (q / b) q (n + 1) ≠ 0 := by
      rw [qPochhammerInf_mul_qPochhammer hq (n + 1)] at hB
      exact left_ne_zero_of_mul hB
    have hqx : qPochhammer (q * x) q (n + 1) ≠ 0 := by
      rw [show q / (1 / x) = q * x by field_simp,
        qPochhammerInf_mul_qPochhammer hq (n + 1)] at hX
      exact left_ne_zero_of_mul hX
    simp only [term, negativeTerm]
    rw [RamanujanPsi.term_negSucc hq0 hb hq,
      RamanujanPsi.term_negSucc hq0 hx0 hq,
      prod_pow_sub_lower ha hb, prod_pow_sub_moving ha]
    rw [show q / (1 / x) = q * x by field_simp,
      qPochhammerInf_mul_qPochhammer hq (n + 1) (a := q * x)]
    rw [show -a * q * x / b = (-a * q / b) * x by ring, mul_pow]
    simp only [one_pow, inv_one, mul_one]
    have hpow : (-a * q) ^ (n + 1) = (-a * q / b) ^ (n + 1) *
        (-b) ^ (n + 1) * (-(1 / x)) ^ (n + 1) * x ^ (n + 1) := by
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      congr 1
      field_simp
    rw [hpow]
    have hbp := pow_ne_zero (n + 1) (neg_ne_zero.mpr hb)
    have hxp := pow_ne_zero (n + 1) (neg_ne_zero.mpr hx0)
    field_simp [hbp, hxp]


/-- Shifting a regular upper parameter downward preserves its finite nonvanishing product. -/
lemma qPochhammer_div_pow_ne_zero {b q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hb : b ≠ 0) (hbr : ∀ k : ℕ, b ≠ q ^ (k + 1)) (m : ℕ) :
    qPochhammer (b / q ^ m) q m ≠ 0 := by
  have hB := RamanujanPsi.qPochhammerInf_q_div_ne_zero hq hb hbr
  rw [qPochhammerInf_mul_qPochhammer hq m] at hB
  have hfin := left_ne_zero_of_mul hB
  have hs := TripleProduct.qPochhammer_shift_down hq0 hb m
  intro hz
  rw [hz, zero_mul] at hs
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hb)) hfin hs.symm

/-- The constant in the unilateral series obtained by shifting the bilateral index. -/
def shiftFactor (a b q : ℂ) (m : ℕ) : ℂ :=
  qPochhammerInf q q * qPochhammerInf (q ^ (m + 1) / a) q *
    qPochhammerInf (-q ^ (m + 1) / b) q /
    (qPochhammer (b / q ^ m) q m * qPochhammer (a / q ^ (2 * m)) q m *
      (-q ^ (m + 1) / b) ^ m)

/-- At `x = qᵐ/a`, the cleared bilateral summand shifts to a cleared Bailey–Daum summand. -/
lemma term_pow_shift {a b q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hbr : ∀ j : ℕ, b ≠ q ^ (j + 1))
    (m : ℕ) (hcr : ∀ j : ℕ, a / q ^ m ≠ q ^ (j + 1)) (k : ℕ) :
    term a b q (q ^ m / a) ((k : ℤ) - m) = shiftFactor a b q m *
      (qPochhammer (a / q ^ (2 * m)) q k *
        (qPochhammer (b / q ^ m) q k / qPochhammer q q k * (-q ^ (m + 1) / b) ^ k *
          qPochhammerInf ((a / q ^ (2 * m)) * q / (b / q ^ m) * q ^ k) q)) := by
  have hqm := pow_ne_zero m hq0
  have hx : q ^ m / a ≠ 0 := div_ne_zero hqm ha
  have hc : 1 / (q ^ m / a) = a / q ^ m := by field_simp
  have hc0 : a / q ^ m ≠ 0 := div_ne_zero ha hqm
  have hbm := qPochhammer_div_pow_ne_zero hq0 hq hb hbr m
  have hcm := qPochhammer_div_pow_ne_zero hq0 hq hc0 hcr m
  have hcm' : qPochhammer (a / q ^ (2 * m)) q m ≠ 0 := by
    convert hcm using 1; rw [two_mul, pow_add]; field_simp
  rw [term_eq_ramanujan_terms hq0 hq ha hb hx hbr (by simpa only [hc] using hcr), hc]
  unfold RamanujanPsi.term
  rw [RamanujanPsi.qPochhammerInt_natCast_sub hq0 m k hbm,
    RamanujanPsi.qPochhammerInt_natCast_sub hq0 m k hcm]
  have hz : -a * q * (q ^ m / a) / b = -q ^ (m + 1) / b := by
    rw [pow_succ]
    field_simp
  have he₁ : a * q / b * q ^ ((k : ℤ) - m) =
      (a / q ^ (2 * m)) * q / (b / q ^ m) * q ^ k := by
    rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast, two_mul, pow_add]
    field_simp
  have he₂ : a * q * (q ^ m / a) * q ^ ((k : ℤ) - m) = q * q ^ k := by
    rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp
  have he₃ : q * (q ^ m / a) = q ^ (m + 1) / a := by rw [pow_succ]; ring
  have he₄ : a / q ^ m / q ^ m = a / q ^ (2 * m) := by
    rw [two_mul, pow_add]
    field_simp
  rw [he₁, he₂, he₃, he₄, hz, zpow_sub₀ (by simp [hq0, hb]), zpow_natCast,
    zpow_natCast]
  simp only [one_zpow, mul_one]
  have hQ := qPochhammer_self_ne_zero hq k
  have hInf := qPochhammerInf_mul_qPochhammer hq k (a := q)
  rw [shiftFactor, hInf]
  field_simp

/-- The finite products cancelling in the shifted Bailey–Daum formula. -/
lemma shifted_finite_products {a b q : ℂ} (hq0 : q ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (m : ℕ) :
    qPochhammer (a / q ^ (2 * m) * q) (q ^ 2) m * qPochhammer (q / b) q m *
      qPochhammer (q ^ (m + 1) / a) q m =
    qPochhammer (b / q ^ m) q m * qPochhammer (a / q ^ (2 * m)) q m *
      (-q ^ (m + 1) / b) ^ m * qPochhammer (q / a) (q ^ 2) m := by
  have hqm := pow_ne_zero m hq0
  have hqC := pow_ne_zero ((m + 1).choose 2) hq0
  have hB := TripleProduct.qPochhammer_shift_down hq0 hb m
  have hC := TripleProduct.qPochhammer_shift_down hq0 (div_ne_zero ha hqm) m
  have hA := TripleProduct.qPochhammer_shift_down (pow_ne_zero 2 hq0)
    (mul_ne_zero ha hq0) m
  have eC₁ : a / q ^ m / q ^ m = a / q ^ (2 * m) := by
    rw [two_mul, pow_add]; field_simp
  have eC₂ : q / (a / q ^ m) = q ^ (m + 1) / a := by rw [pow_succ]; field_simp
  have eA₁ : a * q / (q ^ 2) ^ m = a / q ^ (2 * m) * q := by
    rw [← pow_mul]; field_simp
  have eA₂ : q ^ 2 / (a * q) = q / a := by field_simp
  have eA₃ : (q ^ 2) ^ (m + 1).choose 2 = (q ^ (m + 1).choose 2) ^ 2 := by
    rw [pow_right_comm]
  rw [eC₁, eC₂] at hC
  rw [eA₁, eA₂, eA₃] at hA
  have hB' := (eq_div_iff hqC).mpr hB
  have hC' := (eq_div_iff hqC).mpr hC
  have hA' := (eq_div_iff (pow_ne_zero 2 hqC)).mpr hA
  rw [hB', hC', hA']
  have hp : (-b) ^ m * (-(a / q ^ m)) ^ m * (-q ^ (m + 1) / b) ^ m =
      (-(a * q)) ^ m := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    rw [pow_succ]
    field_simp
  rw [← hp]
  simp only [div_eq_mul_inv]
  ring

/-- The shifted Bailey–Daum product is the cleared bilateral product. -/
lemma shiftFactor_mul_baileyDaum {a b q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hbr : ∀ j : ℕ, b ≠ q ^ (j + 1))
    (m : ℕ) (hcr : ∀ j : ℕ, a / q ^ m ≠ q ^ (j + 1))
    (hz : ‖-q ^ (m + 1) / b‖ < 1) :
    shiftFactor a b q m *
      (qPochhammerInf (-q) q * (qPochhammerInf ((a / q ^ (2 * m)) * q) (q ^ 2) *
        qPochhammerInf ((a / q ^ (2 * m)) * q ^ 2 / (b / q ^ m) ^ 2) (q ^ 2)) /
          qPochhammerInf (-q ^ (m + 1) / b) q) = productSide a b q (q ^ m / a) := by
  have hqm := pow_ne_zero m hq0
  have hc0 : a / q ^ m ≠ 0 := div_ne_zero ha hqm
  have hB := RamanujanPsi.qPochhammerInf_q_div_ne_zero hq hb hbr
  have hC := RamanujanPsi.qPochhammerInf_q_div_ne_zero hq hc0 hcr
  have eC : q / (a / q ^ m) = q ^ (m + 1) / a := by rw [pow_succ]; field_simp
  rw [eC] at hC
  have hBm : qPochhammer (q / b) q m ≠ 0 := by
    rw [qPochhammerInf_mul_qPochhammer hq m] at hB
    exact left_ne_zero_of_mul hB
  have hCm : qPochhammer (q ^ (m + 1) / a) q m ≠ 0 := by
    rw [qPochhammerInf_mul_qPochhammer hq m] at hC
    exact left_ne_zero_of_mul hC
  have hFB := qPochhammer_div_pow_ne_zero hq0 hq hb hbr m
  have hFC : qPochhammer (a / q ^ (2 * m)) q m ≠ 0 := by
    have H := qPochhammer_div_pow_ne_zero hq0 hq hc0 hcr m
    convert H using 1; rw [two_mul, pow_add]; field_simp
  have hZ := qPochhammerInf_ne_zero_of_norm_lt_one hz hq
  have hzp : (-q ^ (m + 1) / b) ^ m ≠ 0 := by simp [hq0, hb]
  have hZ' : qPochhammerInf (-(q ^ (m + 1) / b)) q ≠ 0 := by
    simpa only [neg_div] using hZ
  have hzp' : (-(q ^ (m + 1) / b)) ^ m ≠ 0 := by simpa only [neg_div] using hzp
  have hfinite := shifted_finite_products hq0 ha hb m
  have hFA : qPochhammer (a / q ^ (2 * m) * q) (q ^ 2) m =
      (qPochhammer (b / q ^ m) q m * qPochhammer (a / q ^ (2 * m)) q m *
        (-q ^ (m + 1) / b) ^ m * qPochhammer (q / a) (q ^ 2) m) /
          (qPochhammer (q / b) q m * qPochhammer (q ^ (m + 1) / a) q m) :=
    (eq_div_iff (mul_ne_zero hBm hCm)).mpr (by simpa [mul_assoc] using hfinite)
  have hQ : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hIA := qPochhammerInf_mul_qPochhammer hQ m (a := a / q ^ (2 * m) * q)
  have hIC := qPochhammerInf_mul_qPochhammer hq m (a := q ^ (m + 1) / a)
  have hIB := qPochhammerInf_mul_qPochhammer hq m (a := q / b)
  have hIQ := qPochhammerInf_mul_qPochhammer hQ m (a := q / a)
  have eIA : a / q ^ (2 * m) * q * (q ^ 2) ^ m = a * q := by
    rw [← pow_mul]
    field_simp
  have eIC : q ^ (m + 1) / a * q ^ m = q ^ (2 * m + 1) / a := by
    rw [div_mul_eq_mul_div, ← pow_add]
    congr 2
    omega
  have eIB : q / b * q ^ m = q ^ (m + 1) / b := by rw [pow_succ]; ring
  have eIQ : q / a * (q ^ 2) ^ m = q ^ (2 * m + 1) / a := by
    rw [← pow_mul, div_mul_eq_mul_div, ← pow_succ']
  rw [eIA] at hIA
  rw [eIC, qPochhammerInf_split_sq (a := q ^ (2 * m + 1) / a) hq,
    show q ^ (2 * m + 1) / a * q = q ^ (2 * m + 2) / a by
      rw [div_mul_eq_mul_div, ← pow_succ]] at hIC
  rw [eIB] at hIB
  rw [eIQ] at hIQ
  have hp := qPochhammerInf_mul_qPochhammerInf_neg (x := q) hq
  have eArg : (a / q ^ (2 * m)) * q ^ 2 / (b / q ^ m) ^ 2 = a * q ^ 2 / b ^ 2 := by
    rw [two_mul, pow_add]
    field_simp
  rw [eArg]
  calc _ = (qPochhammerInf q q * qPochhammerInf (-q) q) *
        qPochhammerInf (q ^ (m + 1) / a) q *
        qPochhammerInf (a / q ^ (2 * m) * q) (q ^ 2) *
        qPochhammerInf (a * q ^ 2 / b ^ 2) (q ^ 2) /
        (qPochhammer (b / q ^ m) q m * qPochhammer (a / q ^ (2 * m)) q m *
          (-q ^ (m + 1) / b) ^ m) := by
          unfold shiftFactor
          field_simp [hZ', hzp']
    _ = productSide a b q (q ^ m / a) := by
      rw [hp, hIC, hIA, hFA]
      unfold productSide
      simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
      rw [show a * q * (q ^ m / a) / b = q ^ (m + 1) / b by
        rw [pow_succ]; field_simp]
      rw [show a * q ^ 2 * (q ^ m / a) ^ 2 = q ^ (2 * m + 2) / a by
        rw [two_mul, pow_add]; field_simp; simp [pow_two, pow_add]]
      rw [hIQ, hIB]
      have hBI : qPochhammerInf (q ^ (m + 1) / b) q ≠ 0 :=
        right_ne_zero_of_mul (hIB ▸ hB)
      field_simp [hzp']

/-- Evaluation of the cleared bilateral sum on the geometric parameter sequence. -/
lemma tsum_term_pow {a b q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hbr : ∀ j : ℕ, b ≠ q ^ (j + 1))
    (m : ℕ) (hcr : ∀ j : ℕ, a / q ^ m ≠ q ^ (j + 1))
    (hmb : ‖q‖ < ‖b / q ^ m‖) :
    (∑' n : ℤ, term a b q (q ^ m / a) n) = productSide a b q (q ^ m / a) := by
  have hqm := pow_ne_zero m hq0
  have hx : q ^ m / a ≠ 0 := div_ne_zero hqm ha
  have hc : 1 / (q ^ m / a) = a / q ^ m := by field_simp
  have hvanish : ∀ n ∉ Set.range (fun k : ℕ => (k : ℤ) - m),
      term a b q (q ^ m / a) n = 0 := by
    intro n hn
    have hlt : n < -(m : ℤ) := by
      by_contra hge
      push Not at hge
      exact hn ⟨(n + m).toNat, by simp only; omega⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, n = -(m : ℤ) - 1 - j :=
      ⟨(-(n + m + 1)).toNat, by omega⟩
    rw [term_eq_ramanujan_terms hq0 hq ha hb hx hbr (by simpa only [hc] using hcr)]
    unfold RamanujanPsi.term
    have he : a * q * (q ^ m / a) * q ^ n = (q ^ j)⁻¹ := by
      rw [hj, show -(m : ℤ) - 1 - j = -(((m + 1 + j : ℕ)) : ℤ) by push_cast; ring,
        zpow_neg, zpow_natCast, pow_add, pow_succ]
      field_simp
    rw [he, RamanujanPsi.qPochhammerInf_inv_pow hq0 hq]
    simp
  have hinj : Function.Injective (fun k : ℕ => (k : ℤ) - m) := fun k l h => by
    simpa using h
  rw [← hinj.tsum_eq (by
    intro n hn
    by_contra h
    exact hn (hvanish n h))]
  simp_rw [term_pow_shift hq0 hq ha hb hbr m hcr]
  rw [tsum_mul_left]
  have hz : -q / (b / q ^ m) = -q ^ (m + 1) / b := by rw [pow_succ]; field_simp
  have H := tsum_baileyDaum_cleared (a := a / q ^ (2 * m)) hq hmb
  rw [hz] at H
  rw [H]
  apply shiftFactor_mul_baileyDaum hq0 hq ha hb hbr m hcr
  rw [← hz, norm_div, norm_neg, div_lt_one (norm_pos_iff.mpr (div_ne_zero hb hqm))]
  exact hmb

/-- The denominator-cleared bilateral summation throughout its convergence disk. -/
lemma tsum_term_eq_productSide {a b q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hbr : ∀ j : ℕ, b ≠ q ^ (j + 1))
    (hx : ‖x‖ < ‖a * q / b‖⁻¹) :
    (∑' n : ℤ, term a b q x n) = productSide a b q x := by
  have hB := RamanujanPsi.qPochhammerInf_q_div_ne_zero hq hb hbr
  have hC : 0 < ‖a * q / b‖ :=
    norm_pos_iff.mpr (div_ne_zero (mul_ne_zero ha hq0) hb)
  let U := Metric.ball (0 : ℂ) ‖a * q / b‖⁻¹
  have hH : AnalyticOnNhd ℂ (fun x => ∑' n : ℤ, term a b q x n) U :=
    (differentiableOn_tsum_term hq0 hq ha hb hB).analyticOnNhd Metric.isOpen_ball
  have hQ : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hd : Differentiable ℂ (productSide a b q) := by
    unfold productSide
    simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    have hP := differentiable_qPochhammerInf_left hq
    have hP₂ := differentiable_qPochhammerInf_left hQ
    exact ((hP.comp (by fun_prop)).mul
      ((differentiable_const _).mul ((hP₂.comp (by fun_prop)).mul
        ((differentiable_const _).mul ((differentiable_const _).mul
          (differentiable_const _)))))).div_const _
  have hR : AnalyticOnNhd ℂ (productSide a b q) U := fun x _ => hd.analyticAt x
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self (inv_pos.mpr hC)
  have ht : Tendsto (fun m : ℕ => q ^ m / a) atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun m =>
      div_ne_zero (pow_ne_zero m hq0) ha⟩
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).div_const a
  have hnorm : Tendsto (fun m : ℕ => ‖q ^ m‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).norm
  have hev : ∀ᶠ m : ℕ in atTop,
      (∀ j : ℕ, a / q ^ m ≠ q ^ (j + 1)) ∧ ‖q‖ < ‖b / q ^ m‖ := by
    filter_upwards [hnorm.eventually_lt tendsto_const_nhds (norm_pos_iff.mpr ha),
      hnorm.eventually_lt tendsto_const_nhds (norm_pos_iff.mpr hb)] with m hma hmb
    have hqm : 0 < ‖q ^ m‖ := norm_pos_iff.mpr (pow_ne_zero m hq0)
    constructor
    · intro j hj
      have hlarge : 1 < ‖a / q ^ m‖ := by rw [norm_div, one_lt_div hqm]; exact hma
      rw [hj, norm_pow] at hlarge
      exact (not_lt.mpr (pow_le_one₀ (norm_nonneg q) hq.le)) hlarge
    · rw [norm_div, lt_div_iff₀ hqm]
      exact (mul_le_of_le_one_left (norm_nonneg _) hq.le).trans_lt hmb
  have hfreq : ∃ᶠ y in 𝓝[≠] (0 : ℂ),
      (∑' n : ℤ, term a b q y n) = productSide a b q y :=
    ht.frequently (hev.frequently.mono fun m hm =>
      tsum_term_pow hq0 hq ha hb hbr m hm.1 hm.2)
  exact (hH.eqOn_of_preconnected_of_frequently_eq hR
    (convex_ball (0 : ℂ) _).isPreconnected h0U hfreq) (by simpa [U] using hx)

/-- Absolute convergence of the cleared bilateral series inside its parameter disk. -/
lemma summable_term {a b q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hbr : ∀ j : ℕ, b ≠ q ^ (j + 1))
    (hx : ‖x‖ < ‖a * q / b‖⁻¹) : Summable (term a b q x) := by
  have hC : 0 < ‖a * q / b‖ :=
    norm_pos_iff.mpr (div_ne_zero (mul_ne_zero ha hq0) hb)
  let r := (‖x‖ + ‖a * q / b‖⁻¹) / 2
  have hr : 0 < r := by dsimp [r]; linarith [norm_nonneg x, inv_pos.mpr hC]
  have hrC : r * ‖a * q / b‖ < 1 := by
    have H : r < ‖a * q / b‖⁻¹ := by dsimp [r]; linarith
    simpa only [inv_mul_cancel₀ hC.ne'] using mul_lt_mul_of_pos_right H hC
  obtain ⟨u, hu, hbound⟩ := exists_summable_bound hq hr hrC
    (RamanujanPsi.qPochhammerInf_q_div_ne_zero hq hb hbr)
  exact Summable.of_norm_bounded hu (fun n => hbound n x (by dsimp [r]; linarith))

/-- Bailey's bilateral sum after multiplication by its denominator products. -/
lemma denominator_mul_qPsi_eq_productSide {a b q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hx0 : x ≠ 0) (hz : ‖-a * q * x / b‖ < 1)
    (hreg : QBilateralRegular [b, 1 / x] [a * q / b, a * q * x] q) :
    denominator a b q x * qPsi [b, 1 / x] [a * q / b, a * q * x] q (-a * q * x / b) =
      productSide a b q x := by
  have hbr : ∀ j : ℕ, b ≠ q ^ (j + 1) := hreg.2 _ (by simp)
  have hC : 0 < ‖a * q / b‖ :=
    norm_pos_iff.mpr (div_ne_zero (mul_ne_zero ha hq0) hb)
  have hx : ‖x‖ < ‖a * q / b‖⁻¹ := by
    rw [← one_div, lt_div_iff₀ hC]
    have H : ‖-a * q * x / b‖ = ‖x‖ * ‖a * q / b‖ := by
      rw [show -a * q * x / b = -(x * (a * q / b)) by ring, norm_neg, norm_mul]
    rwa [← H]
  have hs := summable_term hq0 hq ha hb hbr hx
  have hpos : Summable (fun n : ℕ => term a b q x n) :=
    hs.comp_injective (by intro n m h; exact_mod_cast h)
  have hinjNeg : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro n m h
    exact_mod_cast (add_right_cancel (neg_injective h))
  have hneg := hs.comp_injective hinjNeg
  rw [denominator_mul_qPsi hq0 hq ha hb hx0 hz hreg]
  have hsplit := tsum_of_nat_of_neg_add_one hpos hneg
  rw [tsum_term_eq_productSide hq0 hq ha hb hbr hx] at hsplit
  exact hsplit.symm

end DLMF.QHypergeometric.BaileyBilateral
