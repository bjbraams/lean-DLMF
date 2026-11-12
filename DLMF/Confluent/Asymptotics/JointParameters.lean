/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.KummerContiguous
public import DLMF.Gamma.ScaledGammaEstimates
public import DLMFMathlib.Analysis.SpecialFunctions.ExponentialSeries

/-!
# Joint large-parameter expansion of Kummer’s function

For fixed `0 < ν < 1`, the Pochhammer quotient `(a)_n/(a/ν)_n` has a two-term
expansion with a uniform remainder bounded by `n⁴/a²`. Summation against the exponential
series proves DLMF 13.8.17 for every complex argument. The scaled-Gamma ratio converts
the direct coefficient correction to the normalization printed in DLMF.
-/

@[expose] public noncomputable section
open Complex Filter Set Asymptotics
open scoped Real Topology Nat

namespace DLMF.Confluent.KummerLargeParameter

/-- The ratio `(a)_n/(a/ν)_n`, written as a product of real factors. -/
def ratioCoefficient (ν a : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, ν * (a + j) / (a + ν * j)

/-- The first correction coefficient in the joint-parameter expansion of the ratio. -/
def firstCoefficient (ν : ℝ) (n : ℕ) : ℝ :=
  ν ^ n * (1 - ν) * n * (n - 1 : ℝ) / 2

/-- The first correction coefficient is nonnegative and bounded by `n²`. -/
lemma nonneg_firstCoefficient_and_le {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (n : ℕ) :
    0 ≤ firstCoefficient ν n ∧ firstCoefficient ν n ≤ (n : ℝ) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hp : ν ^ n ≤ 1 := pow_le_one₀ hν.le hν1.le
  have hp0 := pow_nonneg hν.le n
  have hc : 0 ≤ (n : ℝ) * (n - 1) := by
    by_cases h : n = 0
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      positivity
  have hprod : 0 ≤ ν ^ n * (1 - ν) ∧ ν ^ n * (1 - ν) ≤ 1 := by
    constructor
    · positivity
    · nlinarith
  dsimp [firstCoefficient]
  constructor
  · nlinarith [mul_nonneg hprod.1 hc]
  · have hh := mul_le_mul_of_nonneg_right hprod.2 hc
    nlinarith

/-- Recurrence for the first correction coefficient. -/
lemma firstCoefficient_succ (ν : ℝ) (n : ℕ) :
    firstCoefficient ν (n + 1) = ν * firstCoefficient ν n + ν ^ (n + 1) * (1 - ν) * n := by
  simp only [firstCoefficient, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

/-- Each ratio factor lies in `[0,1]`, with a uniform quadratic remainder in `1/a`. -/
lemma factor_bounds {ν a : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (ha : 0 < a) (n : ℕ) :
    let r := ν * (a + n) / (a + ν * n)
    0 ≤ r ∧ r ≤ 1 ∧ |r - ν| ≤ n / a ∧
      |r - ν - ν * (1 - ν) * n / a| ≤ (n : ℝ) ^ 2 / a ^ 2 := by
  dsimp only
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hd : 0 < a + ν * n := by positivity
  have hd' : a ≤ a + ν * n := by nlinarith
  have hνprod : 0 ≤ ν * (1 - ν) ∧ ν * (1 - ν) ≤ 1 := by constructor <;> nlinarith
  have he : ν * (a + n) / (a + ν * n) - ν = ν * (1 - ν) * n / (a + ν * n) := by field_simp; ring
  have he2 : ν * (a + n) / (a + ν * n) - ν - ν * (1 - ν) * n / a =
      -(ν ^ 2 * (1 - ν) * n ^ 2 / (a * (a + ν * n))) := by field_simp; ring
  have h2 : 0 ≤ ν ^ 2 * (1 - ν) ∧ ν ^ 2 * (1 - ν) ≤ 1 := by
    constructor
    · positivity
    · have hp : ν ^ 2 ≤ 1 := pow_le_one₀ hν.le hν1.le
      nlinarith [sq_nonneg ν]
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_le_one hd]
    nlinarith
  · rw [he, abs_of_nonneg (by positivity)]
    calc
      ν * (1 - ν) * n / (a + ν * n) ≤ n / (a + ν * n) := by
        apply div_le_div_of_nonneg_right _ hd.le
        nlinarith [mul_le_mul_of_nonneg_right hνprod.2 hn]
      _ ≤ n / a := div_le_div_of_nonneg_left hn ha hd'
  · rw [he2, abs_neg, abs_of_nonneg (by positivity)]
    calc
      ν ^ 2 * (1 - ν) * n ^ 2 / (a * (a + ν * n)) ≤ n ^ 2 / (a * (a + ν * n)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_right h2.2 (sq_nonneg (n : ℝ))]
      _ ≤ n ^ 2 / a ^ 2 := by
        apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos ha)
        nlinarith

/-- The joint-parameter Pochhammer ratio has a uniform remainder bounded by `n⁴/a²`. -/
lemma abs_ratioCoefficient_sub_le {ν a : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (ha : 0 < a) (n : ℕ) :
    |ratioCoefficient ν a n - ν ^ n - firstCoefficient ν n / a| ≤ (n : ℝ) ^ 4 / a ^ 2 := by
  induction n with
  | zero => simp [ratioCoefficient, firstCoefficient]
  | succ n ih =>
    let r := ν * (a + n) / (a + ν * n)
    obtain ⟨hr0, hr1, hrν, hrerr⟩ := factor_bounds hν hν1 ha n
    change 0 ≤ r at hr0
    change r ≤ 1 at hr1
    change |r - ν| ≤ n / a at hrν
    change |r - ν - ν * (1 - ν) * n / a| ≤ (n : ℝ) ^ 2 / a ^ 2 at hrerr
    have hc := nonneg_firstCoefficient_and_le hν hν1 n
    have hp : ν ^ n ≤ 1 := pow_le_one₀ hν.le hν1.le
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have he : ratioCoefficient ν a (n + 1) - ν ^ (n + 1) - firstCoefficient ν (n + 1) / a =
        r * (ratioCoefficient ν a n - ν ^ n - firstCoefficient ν n / a) +
        (r - ν) * firstCoefficient ν n / a +
        ν ^ n * (r - ν - ν * (1 - ν) * n / a) := by
      rw [ratioCoefficient, Finset.prod_range_succ, firstCoefficient_succ, pow_succ]
      dsimp [r, ratioCoefficient]
      ring
    rw [he]
    calc
      _ ≤ |r * (ratioCoefficient ν a n - ν ^ n - firstCoefficient ν n / a)| +
          |(r - ν) * firstCoefficient ν n / a| + |ν ^ n * (r - ν - ν * (1 - ν) * n / a)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (n : ℝ) ^ 4 / a ^ 2 + (n / a) * (n ^ 2) / a + (n : ℝ) ^ 2 / a ^ 2 := by
        simp only [abs_mul, abs_div, abs_of_nonneg hr0, abs_of_nonneg hc.1,
          abs_of_pos ha, abs_of_nonneg (pow_nonneg hν.le n)]
        apply add_le_add
        · apply add_le_add
          · simpa only [one_mul] using mul_le_mul hr1 ih (abs_nonneg _) (by positivity)
          · exact div_le_div_of_nonneg_right (mul_le_mul hrν hc.2 hc.1 (by positivity)) ha.le
        · simpa only [one_mul] using mul_le_mul hp hrerr (abs_nonneg _) (by positivity)
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ 4 / a ^ 2 := by
        have hh : (n : ℝ) ^ 4 + (n : ℝ) ^ 3 + (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 4 := by
          nlinarith [sq_nonneg (n : ℝ)]
        calc _ = ((n : ℝ) ^ 4 + (n : ℝ) ^ 3 + (n : ℝ) ^ 2) / a ^ 2 := by ring
          _ ≤ _ := by norm_num only [Nat.cast_add, Nat.cast_one]; gcongr

/-- The real product agrees with the totalized complex Pochhammer quotient. -/
lemma ratioCoefficient_eq_pochhammer_div {ν a : ℝ} (hν : 0 < ν) (n : ℕ) :
    (ratioCoefficient ν a n : ℂ) =
      DLMF.Hypergeometric.pochhammer (a : ℂ) n /
        DLMF.Hypergeometric.pochhammer ((a / ν : ℝ) : ℂ) n := by
  have hp (x : ℂ) : (∏ j ∈ Finset.range n, (x + j)) =
      DLMF.Hypergeometric.pochhammer x n := by
    simpa using (DLMF.Hypergeometric.pochhammer_mul_pow x 1 n).symm
  calc
    (ratioCoefficient ν a n : ℂ) = ∏ j ∈ Finset.range n,
        ((a : ℂ) + j) / (((a / ν : ℝ) : ℂ) + j) := by
      unfold ratioCoefficient
      rw [Complex.ofReal_prod]
      apply Finset.prod_congr rfl
      intro j hj
      push_cast
      have hν0 : (ν : ℂ) ≠ 0 := ofReal_ne_zero.mpr hν.ne'
      field_simp
    _ = _ := by rw [Finset.prod_div_distrib, hp, hp]

/-- The first correction series is an exponential multiplied by a quadratic polynomial. -/
lemma hasSum_firstCoefficient (ν : ℝ) (z : ℂ) :
    HasSum (fun n : ℕ => (firstCoefficient ν n : ℂ) * z ^ n / n.factorial)
      ((1 - ν) / 2 * (ν * z) ^ 2 * exp (ν * z)) := by
  rw [← hasSum_nat_add_iff' 2]
  have hs : HasSum (fun n : ℕ => ((ν : ℂ) * z) ^ n / n.factorial) (exp (ν * z)) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp ((ν : ℂ) * z)
  convert hs.mul_left ((1 - ν) / 2 * (ν * z) ^ 2) using 1
  · funext n
    simp only [firstCoefficient, ofReal_div, ofReal_mul, ofReal_pow, ofReal_sub, ofReal_one,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    push_cast
    rw [mul_pow, pow_add, pow_add]
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hn2 : (n : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 + 1 ≠ 0)
    field_simp
    ring
  · simp [firstCoefficient, Finset.sum_range_succ]

/-- The product coefficients sum to Kummer’s function on the positive parameter ray. -/
lemma hasSum_ratioCoefficient {ν a : ℝ} (hν : 0 < ν) (ha : 0 < a) (z : ℂ) :
    HasSum (fun n : ℕ => (ratioCoefficient ν a n : ℂ) * z ^ n / n.factorial)
      (kummerM a (a / ν : ℝ) z) := by
  have hb : ∀ k : ℕ, ((a / ν : ℝ) : ℂ) ≠ -k := by
    intro k hk
    have hh := congrArg Complex.re hk
    simp only [ofReal_re, neg_re, natCast_re] at hh
    have haν := div_pos ha hν
    linarith [(Nat.cast_nonneg k : (0 : ℝ)≤k)]
  refine (hasSum_kummerM hb z).congr_fun ?_
  intro n
  rw [ratioCoefficient_eq_pochhammer_div hν]
  dsimp [kummerMCoeff]
  ring

/-- The direct two-term joint-parameter expansion of Kummer’s function. -/
lemma isBigO_kummerM_sub_exp {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (z : ℂ) :
    (fun a : ℝ => kummerM a (a / ν : ℝ) z - exp (ν * z) -
      ((1 - ν) / 2 * (ν * z) ^ 2 * exp (ν * z)) / (a : ℂ)) =O[atTop]
        (fun a : ℝ => (a : ℂ)⁻¹ ^ 2) := by
  have hS := Real.summable_nat_pow_mul_pow_div_factorial 4 (norm_nonneg z)
  apply IsBigO.of_bound (∑' n : ℕ, (n : ℝ) ^ 4 * ‖z‖ ^ n / n.factorial)
  filter_upwards [eventually_gt_atTop 0] with a ha
  have hs := ((hasSum_ratioCoefficient hν ha z).sub
    (show HasSum (fun n : ℕ => ((ν : ℂ) * z) ^ n / n.factorial) (exp (ν * z)) by
      simpa only [Complex.exp_eq_exp_ℂ] using
        NormedSpace.expSeries_div_hasSum_exp ((ν : ℂ) * z))).sub
        ((hasSum_firstCoefficient ν z).div_const (a : ℂ))
  let E : ℕ → ℂ := fun n => ((ratioCoefficient ν a n : ℂ) - (ν : ℂ) ^ n-
    (firstCoefficient ν n : ℂ) / (a : ℂ)) * z ^ n / n.factorial
  have hEsum : HasSum E (kummerM a (a / ν : ℝ) z - exp (ν * z) -
      ((1 - ν) / 2 * (ν * z) ^ 2 * exp (ν * z)) / (a : ℂ)) := by
    apply hs.congr_fun
    intro n
    dsimp [E]
    rw [mul_pow]
    ring
  have hbd (n : ℕ) : ‖E n‖ ≤ ((n : ℝ) ^ 4 * ‖z‖ ^ n / n.factorial) / a ^ 2 := by
    have hb := abs_ratioCoefficient_sub_le hν hν1 ha n
    dsimp [E]
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    have hn : ‖(ratioCoefficient ν a n : ℂ) - (ν : ℂ) ^ n-
        (firstCoefficient ν n : ℂ) / (a : ℂ)‖ ≤ (n : ℝ) ^ 4 / a ^ 2 := by
      rw [← ofReal_pow, ← ofReal_div, ← ofReal_sub, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      exact hb
    calc _ ≤ ((n : ℝ) ^ 4 / a ^ 2) * ‖z‖ ^ n / n.factorial := by gcongr
      _ = _ := by ring
  rw [← hEsum.tsum_eq]
  have hS' := hS.div_const (a ^ 2)
  have hSn : Summable (fun n => ‖E n‖) := hS'.of_nonneg_of_le (fun _ => norm_nonneg _) hbd
  refine (norm_tsum_le_tsum_norm hSn).trans ?_
  calc ∑' n : ℕ, ‖E n‖ ≤ ∑' n : ℕ, ((n : ℝ) ^ 4 * ‖z‖ ^ n / n.factorial) / a ^ 2 :=
      hSn.tsum_le_tsum hbd hS'
    _ = _ := by
      rw [tsum_div_const, norm_pow, norm_inv, norm_real, Real.norm_of_nonneg ha.le]
      ring

end DLMF.Confluent.KummerLargeParameter

namespace DLMF.Confluent

/-- Identity under the stated parameter and domain assumptions: `Asymptotics.IsBigO atTop (fun a :
ℝ => kummerM a (a / ν) z - exp (ν * z) * DLMF.Gamma.scaledGamma (a / ν : ℂ) /
DLMF.Gamma.scaledGamma (a : ℂ) * (1 + (1 - ν) * (1 + 6 * ν ^ 2 * z ^ 2) / (12 * a))) (fun a :
ℝ => (a : ℂ)⁻¹ ^ 2)`. -/
@[dlmf 13.8.E17]
theorem kummerM_large_a_b (ν : ℝ) (z : ℂ) (hν : 0 < ν) (hν1 : ν < 1) :
    Asymptotics.IsBigO atTop
      (fun a : ℝ => kummerM a (a / ν) z -
        exp (ν * z) * DLMF.Gamma.scaledGamma (a / ν : ℂ) / DLMF.Gamma.scaledGamma (a : ℂ) *
          (1 + (1 - ν) * (1 + 6 * ν ^ 2 * z ^ 2) / (12 * a)))
      (fun a : ℝ => (a : ℂ)⁻¹ ^ 2) := by
  let c : ℂ := ((ν : ℂ) - 1) / 12
  let d : ℂ := (1 - ν) * (1 + 6 * (ν : ℂ) ^ 2 * z ^ 2) / 12
  let G : ℝ → ℂ := fun a => DLMF.Gamma.scaledGamma ((a / ν : ℝ) : ℂ) / DLMF.Gamma.scaledGamma a
  have hG : (fun a : ℝ => G a - 1 - c / (a : ℂ)) =O[atTop] (fun a : ℝ => (a : ℂ)⁻¹ ^ 2) :=
    (DLMF.Gamma.isBigO_scaledGamma_div_sub_main hν).congr_left fun a => by dsimp [G, c]; ring
  have hi : Tendsto (fun a : ℝ => (a : ℂ)⁻¹) atTop (𝓝 0) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero
    simpa only [Function.comp_def, ofReal_inv, ofReal_zero] using! h
  have hP : Tendsto (fun a : ℝ => 1 + d / (a : ℂ)) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero, div_eq_mul_inv] using (hi.const_mul d).const_add 1
  have hprod := (hG.mul (hP.isBigO_one ℂ)).congr_right fun a => mul_one _
  have hcross := isBigO_const_mul_self (c * d) (fun a : ℝ => (a : ℂ)⁻¹ ^ 2) atTop
  have hcompare : (fun a : ℝ => G a * (1 + d / (a : ℂ)) - 1 - (c + d) / (a : ℂ)) =O[atTop]
      (fun a : ℝ => (a : ℂ)⁻¹ ^ 2) := by
    apply (hprod.add hcross).congr_left
    intro a
    ring
  have h := (KummerLargeParameter.isBigO_kummerM_sub_exp hν hν1 z).sub
    (hcompare.const_mul_left (exp (ν * z)))
  apply h.congr_left
  intro a
  dsimp [G, c, d]
  push_cast
  ring

end DLMF.Confluent
