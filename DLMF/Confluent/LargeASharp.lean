/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.LargeA
public import DLMF.Bessel.Elementary

/-!
# Sharp rates for Kummer's and Tricomi's functions with large negative `a`

This file sharpens the `o(1)` results of `DLMF.Confluent.LargeA` to the error orders of
Beals–Wong (13.2.7)–(13.2.8) and DLMF 13.8.9 and 18.15.14.

The route keeps the Liouville form `u_κ(s) = s^{c-1/2} e^{-s²/(8κ)} 𝐌(c/2 - κ, c, s²/(4κ))` of
`LargeA`, which solves `u'' + u = g_κ u` with `g_κ = ((c-1)² - 1/4)/s² + s²/(16κ²)`, and the
Bessel limit `u₀(s) = 2^{c-1} √s J_{c-1}(s)`, which solves `u₀'' + u₀ = g₀ u₀` with
`g₀ = ((c-1)² - 1/4)/s²`. Two quantitative ingredients replace the limits of `LargeA`:

* a **quantitative Tannery estimate** `𝐌(d - κ, b, w/κ) = ₀F̃₁(;b;-w) + O(κ⁻¹)`
  (`isBigO_regularizedConfluent_sub_div`), which gives the data of `u_κ` at `s = 1` to
  within `O(κ⁻¹)`;
* a **comparison estimate** on `[s₀, S]` (`norm_largeAU_sub_largeAU0_le_sharp`): the
  difference `w = u_κ - u₀` solves `w'' + w = g₀ w + (s²/(16κ²)) u_κ`, so the Volterra equation
  and Gronwall's inequality bound `‖w(S)‖` by the data difference plus
  `sup ‖u_κ‖ · S³/(16κ²)`, times `exp (∫|g₀|)`. Only the *difference* `g_κ - g₀` enters, so the
  `1/s²` term costs a fixed factor `exp(|(c-1)² - 1/4|/s₀)` rather than an error.

Along `S = 2√(κx)` this gives `u_κ(S) - u₀(S) = O(κ^{-1/2})`.

## Main results

* `largeAU_sub_largeAU0_isBigO`: `u_κ(2√(κx)) - u₀(2√(κx)) = O(κ^{-1/2})`.
* `regularizedConfluent_atBot_besselJ_isBigO` (DLMF 13.8.9): with `S = √(2x(c - 2a))`,
  `((c/2 - a)x)^{(c-1)/2} e^{-x/2} 𝐌(a, c, x) - J_{c-1}(S) = O(S^{-1/2} |a|^{-1/2})`.
* `regularizedConfluent_atBot_cos_isBigO` (Beals–Wong (13.2.8)): the cosine form with error
  `O(|a|^{-1/2})`.
* `kummerU_atBot_isBigO` (DLMF 13.8.10): for non-integer `c`,
  `x^{(c-1)/2} e^{-x/2} U(a, c, x)/Γ(c/2 - a + 1/2) - (cos(aπ) J_{c-1}(S) - sin(aπ) Y_{c-1}(S))
  = O(S^{-1/2} |a|^{-1/2})`, from the connection formula 13.2.42, two instances of 13.8.9 and
  `J_{-ν} = cos(νπ) J_ν - sin(νπ) Y_ν`.
* `laguerrePolyL_fejer_isBigO` (DLMF 18.15.14 with `M = 1`): Fejér's formula with error
  `O(n^{-1/2})`.

In 13.8.9 and 13.8.10 DLMF writes the error as `env J_{c-1}(S) O(|a|^{-1/2})` and
`env Y_{c-1}(S) O(|a|^{-1/2})`; since the envelopes are `≍ S^{-1/2}` as `S → ∞`, the statements
here use `S^{-1/2} |a|^{-1/2}`.
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric Asymptotics
open scoped Real Nat Topology

noncomputable section

namespace DLMF.Confluent

/-! ### A quantitative Tannery estimate -/

/-- For `x ≥ 1`, `(x)_n ≥ 1`. -/
theorem one_le_ascPochhammer_eval {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    1 ≤ (ascPochhammer ℝ n).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    have : 1 ≤ x + n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    nlinarith

/-- `‖(d - κ)_n / κⁿ - (-1)ⁿ‖ ≤ n (1 + |d|)_n / κ` for `κ ≥ 1`. -/
theorem norm_poch_sub_div_pow_sub_le (d : ℝ) {κ : ℝ} (hκ : 1 ≤ κ) (n : ℕ) :
    ‖poch ((d - κ : ℝ) : ℂ) n / (κ : ℂ) ^ n - (-1 : ℂ) ^ n‖ ≤
      n * (ascPochhammer ℝ n).eval (1 + |d|) / κ := by
  have hκ0 : 0 < κ := by linarith
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0.ne'
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    set P := poch ((d - κ : ℝ) : ℂ) n / (κ : ℂ) ^ n
    set r : ℂ := (((d - κ : ℝ) : ℂ) + n) / κ
    have hsplit : poch ((d - κ : ℝ) : ℂ) (n + 1) / (κ : ℂ) ^ (n + 1) = P * r := by
      simp only [P, r]
      rw [poch_succ, pow_succ]
      field_simp
    have hr1 : r + 1 = (((d + n) / κ : ℝ) : ℂ) := by
      simp only [r]
      push_cast
      field_simp
      ring
    have hid : P * r - (-1 : ℂ) ^ (n + 1) =
        (P - (-1 : ℂ) ^ n) * r + (-1 : ℂ) ^ n * (((d + n) / κ : ℝ) : ℂ) := by
      rw [← hr1, pow_succ]
      ring
    have hfac : ‖r‖ ≤ 1 + |d| + n := by
      simp only [r]
      rw [show (((d - κ : ℝ) : ℂ) + n) / κ = (((d - κ + n) / κ : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hκ0, div_le_iff₀ hκ0]
      have h1 : |d - κ + n| ≤ |d| + κ + n := by
        have := abs_add_le (d + n) (-κ)
        rw [show d + n + -κ = d - κ + n by ring, abs_neg, abs_of_pos hκ0] at this
        have h2 : |d + n| ≤ |d| + n := by
          have := abs_add_le d (n : ℝ)
          rwa [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at this
        linarith
      have hdn : 0 ≤ |d| + n := by positivity
      nlinarith
    have hdn : ‖(-1 : ℂ) ^ n * (((d + n) / κ : ℝ) : ℂ)‖ ≤ (|d| + n) / κ := by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_div, abs_of_pos hκ0]
      gcongr
      have := abs_add_le d (n : ℝ)
      rwa [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at this
    set A := (ascPochhammer ℝ n).eval (1 + |d|)
    have hA1 : 1 ≤ A := one_le_ascPochhammer_eval (by linarith [abs_nonneg d]) n
    have hA' : (ascPochhammer ℝ (n + 1)).eval (1 + |d|) = A * (1 + |d| + n) := by
      rw [ascPochhammer_succ_eval]
    rw [hsplit, hid, hA']
    calc ‖(P - (-1 : ℂ) ^ n) * r + (-1 : ℂ) ^ n * (((d + n) / κ : ℝ) : ℂ)‖
        ≤ ‖P - (-1 : ℂ) ^ n‖ * ‖r‖ + (|d| + n) / κ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ hdn)
          rw [norm_mul]
      _ ≤ n * A / κ * (1 + |d| + n) + (|d| + n) / κ := by
          gcongr
      _ ≤ ((n + 1 : ℕ) : ℝ) * (A * (1 + |d| + n)) / κ := by
          rw [div_mul_eq_mul_div, ← add_div, div_le_div_iff_of_pos_right hκ0]
          push_cast
          have h0 : 0 ≤ |d| := abs_nonneg d
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith

/-- **Quantitative Tannery estimate**: `𝐌(d - κ, b, w/κ) = ₀F̃₁(;b;-w) + O(κ⁻¹)` as
`κ → +∞`. -/
theorem isBigO_regularizedConfluent_sub_div (d : ℝ) (b w : ℂ) :
    (fun κ : ℝ => regularizedHGFun {((d - κ : ℝ) : ℂ)} {b} (w / κ) -
      regularizedHGFun (∅ : Multiset ℂ) {b} (-w)) =O[atTop] (fun κ : ℝ => κ⁻¹) := by
  set T : ℕ → ℂ := fun n => w ^ n / n ! * (Gamma (b + n))⁻¹ with hT
  set x : ℝ := 1 + |d| with hx
  have hx1 : 1 ≤ x := by simp only [hx]; linarith [abs_nonneg d]
  have hL : ∀ κ : ℝ, κ ≠ 0 → regularizedHGFun {((d - κ : ℝ) : ℂ)} {b} (w / κ) =
      ∑' n : ℕ, poch ((d - κ : ℝ) : ℂ) n / (κ : ℂ) ^ n * T n := by
    intro κ hκ
    have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
    rw [regularizedConfluent_eq_tsum]
    refine tsum_congr fun n => ?_
    simp only [hT, div_pow]
    field_simp
  have hR : regularizedHGFun (∅ : Multiset ℂ) {b} (-w) = ∑' n : ℕ, (-1 : ℂ) ^ n * T n := by
    rw [regularizedHGFun_eq_tsum]
    refine tsum_congr fun n => ?_
    rw [DLMF.Bessel.regularizedHGFunCoeff_empty, hT, neg_pow]
    field_simp
  -- the majorant `n (x)_n ‖T n‖ ≤ x (x+1)_n ‖T n‖`
  have hsumB : Summable fun n : ℕ => (ascPochhammer ℝ n).eval (x + 1) * ‖T n‖ := by
    have hs := summable_norm_iff.mpr
      (summable_regularizedConfluent_term (((x + 1 : ℝ)) : ℂ) b (‖w‖ : ℂ))
    refine hs.congr fun n => ?_
    rw [poch_ofReal]
    simp only [hT, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      norm_inv, Complex.norm_natCast, abs_norm]
    rw [abs_of_nonneg ((ascPochhammer_pos n _ (by linarith)).le)]
    ring
  have hmaj : ∀ n : ℕ, (n : ℝ) * (ascPochhammer ℝ n).eval x ≤
      x * (ascPochhammer ℝ n).eval (x + 1) := by
    intro n
    have h1 : (ascPochhammer ℝ (n + 1)).eval x = x * (ascPochhammer ℝ n).eval (x + 1) := by
      rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    rw [← h1, ascPochhammer_succ_eval]
    have hp := (ascPochhammer_pos n x (by linarith)).le
    have : (n : ℝ) ≤ x + n := by linarith
    nlinarith
  have hsum : Summable fun n : ℕ => (n : ℝ) * (ascPochhammer ℝ n).eval x * ‖T n‖ := by
    refine Summable.of_nonneg_of_le (fun n => by
      have := (ascPochhammer_pos n x (by linarith)).le
      positivity) (fun n => ?_) (hsumB.mul_left x)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hmaj n) (norm_nonneg _)
  set K := ∑' n : ℕ, (n : ℝ) * (ascPochhammer ℝ n).eval x * ‖T n‖
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with κ hκ
  have hκ0 : 0 < κ := by linarith
  have hsκ : Summable fun n : ℕ => poch ((d - κ : ℝ) : ℂ) n / (κ : ℂ) ^ n * T n := by
    refine Summable.of_norm_bounded (g := fun n => (ascPochhammer ℝ n).eval x * ‖T n‖) ?_
      fun n => ?_
    · have hs := summable_norm_iff.mpr
        (summable_regularizedConfluent_term (((x : ℝ)) : ℂ) b (‖w‖ : ℂ))
      refine hs.congr fun n => ?_
      rw [poch_ofReal]
      simp only [hT, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        norm_inv, Complex.norm_natCast, abs_norm]
      rw [abs_of_nonneg ((ascPochhammer_pos n _ (by linarith)).le)]
      ring
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_poch_sub_div_pow_le d hκ n) (norm_nonneg _)
  have hs1 : Summable fun n : ℕ => (-1 : ℂ) ^ n * T n := by
    refine Summable.of_norm_bounded (g := fun n => ‖T n‖) ?_ fun n => ?_
    · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsumB
      exact le_mul_of_one_le_left (norm_nonneg _)
        (one_le_ascPochhammer_eval (by linarith) n)
    · rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [hL κ hκ0.ne', hR, ← hsκ.tsum_sub hs1, Real.norm_eq_abs, abs_inv, abs_of_pos hκ0]
  have hb : ∀ n : ℕ, ‖poch ((d - κ : ℝ) : ℂ) n / (κ : ℂ) ^ n * T n - (-1 : ℂ) ^ n * T n‖ ≤
      (n : ℝ) * (ascPochhammer ℝ n).eval x * ‖T n‖ * κ⁻¹ := by
    intro n
    rw [← sub_mul, norm_mul]
    have := norm_poch_sub_div_pow_sub_le d hκ n
    calc _ ≤ (n * (ascPochhammer ℝ n).eval (1 + |d|) / κ) * ‖T n‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := by rw [hx]; field_simp
  calc ‖∑' n : ℕ, (poch ((d - κ : ℝ) : ℂ) n / (κ : ℂ) ^ n * T n - (-1 : ℂ) ^ n * T n)‖
      ≤ ∑' n : ℕ, (n : ℝ) * (ascPochhammer ℝ n).eval x * ‖T n‖ * κ⁻¹ :=
        tsum_of_norm_bounded (hsum.mul_right κ⁻¹).hasSum hb
    _ = K * κ⁻¹ := tsum_mul_right

/-! ### Rates for the data at a fixed point -/

/-- A product of two convergent families converges at the rate of its factors. -/
theorem isBigO_mul_sub_mul {f g : ℝ → ℂ} {f₀ g₀ : ℂ}
    (hf : (fun κ => f κ - f₀) =O[atTop] (fun κ : ℝ => κ⁻¹))
    (hg : (fun κ => g κ - g₀) =O[atTop] (fun κ : ℝ => κ⁻¹)) :
    (fun κ => f κ * g κ - f₀ * g₀) =O[atTop] (fun κ : ℝ => κ⁻¹) := by
  have hinv : (fun κ : ℝ => κ⁻¹) =O[atTop] (fun _ => (1 : ℝ)) :=
    tendsto_inv_atTop_zero.isBigO_one ℝ
  have hgb : g =O[atTop] (fun _ => (1 : ℝ)) :=
    ((hg.trans hinv).add (isBigO_const_const g₀ one_ne_zero atTop)).congr_left
      fun κ => by ring
  have h1 := (hf.mul hgb).congr_right (fun κ => mul_one κ⁻¹)
  have h2 := hg.const_mul_left f₀
  exact (h1.add h2).congr_left fun κ => by ring

/-- If `f - f₀` and `g - g₀` are `O(1/κ)`, so is `f + g - (f₀ + g₀)`. -/
theorem isBigO_add_sub_add {f g : ℝ → ℂ} {f₀ g₀ : ℂ}
    (hf : (fun κ => f κ - f₀) =O[atTop] (fun κ : ℝ => κ⁻¹))
    (hg : (fun κ => g κ - g₀) =O[atTop] (fun κ : ℝ => κ⁻¹)) :
    (fun κ => f κ + g κ - (f₀ + g₀)) =O[atTop] (fun κ : ℝ => κ⁻¹) :=
  (hf.add hg).congr_left fun κ => by ring

/-- `M̃(c/2-κ, c, s²/(4κ)) - ₀F̃₁(;c;-s²/4) = O(1/κ)` as `κ → ∞`. -/
theorem largeAW_sub_isBigO (c s : ℝ) :
    (fun κ : ℝ => largeAW c κ s - largeAV c s) =O[atTop] (fun κ : ℝ => κ⁻¹) := by
  have h := isBigO_regularizedConfluent_sub_div (c / 2) (c : ℂ) ((s ^ 2 / 4 : ℝ) : ℂ)
  have hV : largeAV c s =
      regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} (-((s ^ 2 / 4 : ℝ) : ℂ)) := by
    simp only [largeAV]
    push_cast
    ring_nf
  rw [hV]
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  simp only [largeAW, largeAParam]
  congr 2
  push_cast
  field_simp

/-- `largeAW1 - largeAV1 = O(1/κ)` as `κ → ∞`. -/
lemma largeAW1_sub_isBigO (c s : ℝ) :
    (fun κ : ℝ => largeAW1 c κ s - largeAV1 c s) =O[atTop] (fun κ : ℝ => κ⁻¹) := by
  have hX := isBigO_regularizedConfluent_sub_div (c / 2 + 1) ((c : ℂ) + 1) ((s ^ 2 / 4 : ℝ) : ℂ)
  have hA : (fun κ : ℝ => (((c / 2) / κ - 1 : ℝ) : ℂ) - (-1 : ℂ)) =O[atTop]
      (fun κ : ℝ => κ⁻¹) := by
    refine Asymptotics.IsBigO.of_bound |c / 2| ?_
    filter_upwards with κ
    rw [show (((c / 2) / κ - 1 : ℝ) : ℂ) - (-1 : ℂ) = ((c / 2 * κ⁻¹ : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  have hP := isBigO_mul_sub_mul (isBigO_mul_sub_mul hA hX)
    (g := fun _ => ((s / 2 : ℝ) : ℂ)) (g₀ := ((s / 2 : ℝ) : ℂ))
    (by simp only [sub_self]; exact isBigO_zero _ _)
  have hV : largeAV1 c s = (-1 : ℂ) *
      regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ) + 1} (-((s ^ 2 / 4 : ℝ) : ℂ)) *
        ((s / 2 : ℝ) : ℂ) := by
    simp only [largeAV1]
    push_cast
    ring_nf
  rw [hV]
  refine hP.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  simp only [largeAW1, largeAParam]
  have harg : (((s ^ 2 / 4 : ℝ) : ℂ) / κ) = ((s ^ 2 / (4 * κ) : ℝ) : ℂ) := by
    push_cast
    field_simp
  have hpar : (((c / 2 + 1 - κ : ℝ)) : ℂ) = ((c / 2 - κ : ℝ) : ℂ) + 1 := by push_cast; ring
  rw [harg, hpar]
  push_cast
  field_simp

/-- The gauge factor satisfies `s^{c-1/2} e^{-s²/(8κ)} - s^{c-1/2} = O(1/κ)` as `κ → ∞`. -/
theorem largeAP_sub_isBigO (c s : ℝ) :
    (fun κ : ℝ => ((largeAP c κ s : ℝ) : ℂ) - ((largeAQ c s : ℝ) : ℂ)) =O[atTop]
      (fun κ : ℝ => κ⁻¹) := by
  refine Asymptotics.IsBigO.of_bound (|s ^ (c - 1 / 2)| * (s ^ 2 / 8)) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
  rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
    abs_of_pos hκ]
  simp only [largeAP, largeAQ]
  rw [← mul_sub_one, abs_mul]
  have hy : 0 ≤ s ^ 2 / (8 * κ) := by positivity
  have h1 : |Real.exp (-(s ^ 2 / (8 * κ))) - 1| ≤ s ^ 2 / (8 * κ) := by
    have h2 := Real.add_one_le_exp (-(s ^ 2 / (8 * κ)))
    have h3 : Real.exp (-(s ^ 2 / (8 * κ))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_of_nonpos (by linarith)]
    linarith
  calc |s ^ (c - 1 / 2)| * |Real.exp (-(s ^ 2 / (8 * κ))) - 1|
      ≤ |s ^ (c - 1 / 2)| * (s ^ 2 / (8 * κ)) := by gcongr
    _ = |s ^ (c - 1 / 2)| * (s ^ 2 / 8) * κ⁻¹ := by field_simp

/-- `largeAH - largeAH0 = -s/(4κ) = O(1/κ)` as `κ → ∞`. -/
theorem largeAH_sub_isBigO (c s : ℝ) :
    (fun κ : ℝ => ((largeAH c κ s : ℝ) : ℂ) - ((largeAH0 c s : ℝ) : ℂ)) =O[atTop]
      (fun κ : ℝ => κ⁻¹) := by
  refine Asymptotics.IsBigO.of_bound (|s| / 4) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
  rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
    abs_of_pos hκ]
  simp only [largeAH, largeAH0]
  rw [show (c - 1 / 2) / s - s / (4 * κ) - (c - 1 / 2) / s = -(s / 4) * κ⁻¹ by
    ring, abs_mul, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_inv, abs_of_pos hκ]

/-- The data of `u_κ` at a fixed point converge at the rate `O(κ⁻¹)`. -/
theorem largeAU_sub_largeAU0_isBigO_const (c s : ℝ) :
    (fun κ : ℝ => largeAU c κ s - largeAU0 c s) =O[atTop] (fun κ : ℝ => κ⁻¹) :=
  isBigO_mul_sub_mul (largeAP_sub_isBigO c s) (largeAW_sub_isBigO c s)

/-- `u' - u₀' = O(1/κ)` as `κ → ∞`, at fixed `s`. -/
theorem largeAU'_sub_largeAU0'_isBigO_const (c s : ℝ) :
    (fun κ : ℝ => largeAU' c κ s - largeAU0' c s) =O[atTop] (fun κ : ℝ => κ⁻¹) :=
  isBigO_mul_sub_mul (largeAP_sub_isBigO c s)
    (isBigO_add_sub_add (isBigO_mul_sub_mul (largeAH_sub_isBigO c s) (largeAW_sub_isBigO c s))
      (largeAW1_sub_isBigO c s))

/-! ### The comparison estimate -/

/-- `g - g₀ = t²/(16κ²)`. -/
theorem largeAG_sub_largeAG0 (c κ t : ℝ) : largeAG c κ t - largeAG0 c t = t ^ 2 / (16 * κ ^ 2) := by
  simp only [largeAG, largeAG0]
  ring

/-- **Comparison of `u_κ` with its Bessel limit `u₀` on `[s₀, S]`.** The difference solves
`w'' + w = g₀ w + (s²/(16κ²)) u_κ`; the Volterra equation and Gronwall's inequality give
`‖w(S)‖ ≤ (δ + U · S³/(16κ²)) exp(|(c-1)² - 1/4|/s₀)`, where `δ` is the data difference at
`s₀` and `U = (‖u_κ(s₀)‖ + ‖u_κ'(s₀)‖) exp(|(c-1)² - 1/4|/s₀ + S³/(16κ²))` bounds `u_κ`. -/
theorem norm_largeAU_sub_largeAU0_le_sharp (c : ℝ) {κ s₀ S : ℝ} (hκ : 0 < κ) (hs₀ : 0 < s₀)
    (hS : s₀ ≤ S) :
    ‖largeAU c κ S - largeAU0 c S‖ ≤
      ((‖largeAU c κ s₀ - largeAU0 c s₀‖ + ‖largeAU' c κ s₀ - largeAU0' c s₀‖) +
        (‖largeAU c κ s₀‖ + ‖largeAU' c κ s₀‖) *
          Real.exp (|(c - 1) ^ 2 - 1 / 4| / s₀ + S ^ 3 / (16 * κ ^ 2)) *
            (S ^ 3 / (16 * κ ^ 2))) * Real.exp (|(c - 1) ^ 2 - 1 / 4| / s₀) := by
  set A := |(c - 1) ^ 2 - 1 / 4| with hA
  set B := S ^ 3 / (16 * κ ^ 2) with hB
  set N := ‖largeAU c κ s₀‖ + ‖largeAU' c κ s₀‖ with hN
  set U := N * Real.exp (A / s₀ + B) with hU
  set δ := ‖largeAU c κ s₀ - largeAU0 c s₀‖ + ‖largeAU' c κ s₀ - largeAU0' c s₀‖ with hδ
  set u := largeAU c κ
  set u0 := largeAU0 c
  set w : ℝ → ℂ := fun t => u t - u0 t with hw
  set g := largeAG c κ
  set g0 := largeAG0 c
  have hpos : ∀ t ∈ Icc s₀ S, 0 < t := fun t ht => lt_of_lt_of_le hs₀ ht.1
  have hu : ∀ t ∈ Icc s₀ S, HasDerivAt u (largeAU' c κ t) t :=
    fun t ht => hasDerivAt_largeAU c κ (hpos t ht)
  have hu' : ∀ t ∈ Icc s₀ S, HasDerivAt (largeAU' c κ)
      ((g t - (1 : ℝ) ^ 2) • u t) t :=
    fun t ht => by simpa using hasDerivAt_largeAU' c hκ (hpos t ht)
  have hv : ∀ t ∈ Icc s₀ S, HasDerivAt u0 (largeAU0' c t) t :=
    fun t ht => hasDerivAt_largeAU0 c (hpos t ht)
  have hv' : ∀ t ∈ Icc s₀ S, HasDerivAt (largeAU0' c) ((g0 t - (1 : ℝ) ^ 2) • u0 t) t :=
    fun t ht => by simpa using hasDerivAt_largeAU0' c (hpos t ht)
  have hgc : ContinuousOn g (Icc s₀ S) := continuousOn_largeAG c κ hs₀
  have hg0c : ContinuousOn g0 (Icc s₀ S) := continuousOn_largeAG0 c hs₀
  have huc : ContinuousOn u (Icc s₀ S) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hvc : ContinuousOn u0 (Icc s₀ S) := fun t ht => (hv t ht).continuousAt.continuousWithinAt
  have hwc : ContinuousOn w (Icc s₀ S) := huc.sub hvc
  have hA0 : 0 ≤ A := abs_nonneg _
  have hSpos : 0 < S := lt_of_lt_of_le hs₀ hS
  have hB0 : 0 ≤ B := div_nonneg (pow_nonneg hSpos.le 3) (by positivity)
  have hN0 : 0 ≤ N := by positivity
  have hU0 : 0 ≤ U := by positivity
  -- the bound for `u_κ`
  have hUb : ∀ t ∈ Icc s₀ S, ‖u t‖ ≤ U := by
    intro t ht
    have hsub : Icc s₀ t ⊆ Icc s₀ S := Icc_subset_Icc le_rfl ht.2
    have h1 := ODE.norm_sub_oscFree_le' (E := ℂ) (ω := 1) one_ne_zero (hgc.mono hsub)
      (fun τ hτ => hu τ (hsub hτ)) (fun τ hτ => hu' τ (hsub hτ)) (b := t) ⟨ht.1, le_rfl⟩
    have h2 := ODE.norm_oscFree_le 1 s₀ (u s₀) (largeAU' c κ s₀) t
    simp only [abs_one, div_one] at h1 h2
    have hI := integral_abs_largeAG_le c hκ hs₀ ht.1
    have ht0 : 0 ≤ t := (hpos t ht).le
    have ht3 : t ^ 3 / (16 * κ ^ 2) ≤ B := by
      rw [hB]
      gcongr
      exact ht.2
    have hexp : Real.exp (∫ τ in s₀..t, |largeAG c κ τ|) ≤ Real.exp (A / s₀ + B) :=
      Real.exp_le_exp.mpr (by linarith)
    calc ‖u t‖ ≤ ‖ODE.oscFree 1 s₀ (u s₀) (largeAU' c κ s₀) t‖ +
          ‖u t - ODE.oscFree 1 s₀ (u s₀) (largeAU' c κ s₀) t‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ N + N * (Real.exp (∫ τ in s₀..t, |largeAG c κ τ|) - 1) := add_le_add h2 h1
      _ = N * Real.exp (∫ τ in s₀..t, |largeAG c κ τ|) := by ring
      _ ≤ U := mul_le_mul_of_nonneg_left hexp hN0
  -- the integral inequality for `w`
  have key : ∀ t ∈ Icc s₀ S, ‖w t‖ ≤ (δ + U * B) + ∫ τ in s₀..t, |g0 τ| * ‖w τ‖ := by
    intro t ht
    have hsub : Icc s₀ t ⊆ Icc s₀ S := Icc_subset_Icc le_rfl ht.2
    have hst : s₀ ≤ t := ht.1
    have hV1 := ODE.eq_oscFree_add_integral (E := ℂ) one_ne_zero hgc hu hu' ht
    have hV0 := ODE.eq_oscFree_add_integral (E := ℂ) one_ne_zero hg0c hv hv' ht
    simp only [inv_one, one_smul, one_mul] at hV1 hV0
    have hsin : Continuous fun τ : ℝ => Real.sin (t - τ) := by fun_prop
    have hi1 : IntervalIntegrable (fun τ => (Real.sin (t - τ) * g τ) • u τ) MeasureTheory.volume
        s₀ t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hst]
      exact (hsin.continuousOn.mul (hgc.mono hsub)).smul (huc.mono hsub)
    have hi0 : IntervalIntegrable (fun τ => (Real.sin (t - τ) * g0 τ) • u0 τ)
        MeasureTheory.volume s₀ t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hst]
      exact (hsin.continuousOn.mul (hg0c.mono hsub)).smul (hvc.mono hsub)
    have hwt : w t = ODE.oscFree 1 s₀ (u s₀ - u0 s₀) (largeAU' c κ s₀ - largeAU0' c s₀) t +
        ∫ τ in s₀..t, ((Real.sin (t - τ) * g τ) • u τ - (Real.sin (t - τ) * g0 τ) • u0 τ) := by
      rw [intervalIntegral.integral_sub hi1 hi0, ← oscFree_sub]
      simp only [hw]
      rw [hV1, hV0]
      abel
    have hpt : ∀ τ ∈ Icc s₀ t,
        ‖(Real.sin (t - τ) * g τ) • u τ - (Real.sin (t - τ) * g0 τ) • u0 τ‖ ≤
          |g0 τ| * ‖w τ‖ + U * (S ^ 2 / (16 * κ ^ 2)) := by
      intro τ hτ
      have hτS := hsub hτ
      have heq : (Real.sin (t - τ) * g τ) • u τ - (Real.sin (t - τ) * g0 τ) • u0 τ =
          (Real.sin (t - τ) : ℂ) * ((g0 τ : ℂ) * w τ + ((g τ - g0 τ : ℝ) : ℂ) * u τ) := by
        simp only [hw, real_smul]
        push_cast
        ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hd : g τ - g0 τ = τ ^ 2 / (16 * κ ^ 2) := largeAG_sub_largeAG0 c κ τ
      have hτ0 : 0 ≤ τ := (hpos τ hτS).le
      have hτ2 : τ ^ 2 / (16 * κ ^ 2) ≤ S ^ 2 / (16 * κ ^ 2) := by
        gcongr
        exact hτS.2
      calc |Real.sin (t - τ)| * ‖(g0 τ : ℂ) * w τ + ((g τ - g0 τ : ℝ) : ℂ) * u τ‖
          ≤ 1 * (|g0 τ| * ‖w τ‖ + τ ^ 2 / (16 * κ ^ 2) * U) := by
            gcongr
            · exact Real.abs_sin_le_one _
            · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hd,
                  abs_of_nonneg (by positivity)]
                exact mul_le_mul_of_nonneg_left (hUb τ hτS) (by positivity)
        _ ≤ |g0 τ| * ‖w τ‖ + U * (S ^ 2 / (16 * κ ^ 2)) := by
            rw [one_mul]
            nlinarith
    have hrc : ContinuousOn (fun τ => |g0 τ| * ‖w τ‖ + U * (S ^ 2 / (16 * κ ^ 2)))
        (Icc s₀ t) := ((hg0c.mono hsub).abs.mul (hwc.mono hsub).norm).add continuousOn_const
    have hint : ‖∫ τ in s₀..t, ((Real.sin (t - τ) * g τ) • u τ -
        (Real.sin (t - τ) * g0 τ) • u0 τ)‖ ≤
        ∫ τ in s₀..t, (|g0 τ| * ‖w τ‖ + U * (S ^ 2 / (16 * κ ^ 2))) := by
      refine (intervalIntegral.norm_integral_le_integral_norm hst).trans ?_
      refine intervalIntegral.integral_mono_on hst (hi1.sub hi0).norm
        (hrc.intervalIntegrable_of_Icc hst) hpt
    have hsplit : ∫ τ in s₀..t, (|g0 τ| * ‖w τ‖ + U * (S ^ 2 / (16 * κ ^ 2))) =
        (∫ τ in s₀..t, |g0 τ| * ‖w τ‖) + (t - s₀) * (U * (S ^ 2 / (16 * κ ^ 2))) := by
      rw [intervalIntegral.integral_add (f := fun τ => |g0 τ| * ‖w τ‖)
        (g := fun _ => U * (S ^ 2 / (16 * κ ^ 2)))
        (((hg0c.mono hsub).abs.mul (hwc.mono hsub).norm).intervalIntegrable_of_Icc hst)
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
    have hlen : (t - s₀) * (U * (S ^ 2 / (16 * κ ^ 2))) ≤ U * B := by
      rw [hB, show S ^ 3 / (16 * κ ^ 2) = S * (S ^ 2 / (16 * κ ^ 2)) by ring]
      have h1 : t - s₀ ≤ S := by linarith [ht.2]
      have h2 : 0 ≤ U * (S ^ 2 / (16 * κ ^ 2)) := by positivity
      nlinarith
    have hosc := ODE.norm_oscFree_le 1 s₀ (u s₀ - u0 s₀) (largeAU' c κ s₀ - largeAU0' c s₀) t
    simp only [abs_one, div_one] at hosc
    rw [hwt]
    calc _ ≤ ‖ODE.oscFree 1 s₀ (u s₀ - u0 s₀) (largeAU' c κ s₀ - largeAU0' c s₀) t‖ +
          ‖∫ τ in s₀..t, ((Real.sin (t - τ) * g τ) • u τ - (Real.sin (t - τ) * g0 τ) • u0 τ)‖ :=
          norm_add_le _ _
      _ ≤ δ + ((∫ τ in s₀..t, |g0 τ| * ‖w τ‖) + U * B) := by
          refine add_le_add hosc ?_
          rw [hsplit] at hint
          linarith
      _ = (δ + U * B) + ∫ τ in s₀..t, |g0 τ| * ‖w τ‖ := by ring
  -- Gronwall
  have hS' : S ∈ Icc s₀ S := ⟨hS, le_rfl⟩
  have hgr := ODE.add_integral_le_mul_exp_integral hwc.norm hg0c.abs
    (fun t _ => abs_nonneg _) key hS'
  have hI0 := integral_abs_largeAG0_le c hs₀ hS
  have hδU : 0 ≤ δ + U * B := by positivity
  have hexp : Real.exp (∫ τ in s₀..S, |g0 τ|) ≤ Real.exp (A / s₀) := Real.exp_le_exp.mpr hI0
  calc ‖largeAU c κ S - largeAU0 c S‖ = ‖w S‖ := rfl
    _ ≤ (δ + U * B) + ∫ τ in s₀..S, |g0 τ| * ‖w τ‖ := key S hS'
    _ ≤ (δ + U * B) * Real.exp (∫ τ in s₀..S, |g0 τ|) := hgr
    _ ≤ (δ + U * B) * Real.exp (A / s₀) := mul_le_mul_of_nonneg_left hexp hδU
    _ = _ := by rw [hU]

/-! ### The rate along `S = 2√(κx)` -/

/-- For `x, κ > 0`, `(2√(κx))³/(16κ²) = x√x/(2√κ)`. -/
theorem cube_div_eq (x : ℝ) (hx : 0 < x) {κ : ℝ} (hκ : 0 < κ) :
    (2 * Real.sqrt (κ * x)) ^ 3 / (16 * κ ^ 2) = x * Real.sqrt x / (2 * Real.sqrt κ) := by
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hk : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  rw [Real.sqrt_mul hκ.le]
  set a := Real.sqrt κ
  set b := Real.sqrt x
  rw [← hk, ← hxx]
  field_simp
  ring

/-- **The sharp matching rate**: `u_κ(2√(κx)) - u₀(2√(κx)) = O(κ^{-1/2})` as `κ → +∞`. -/
theorem largeAU_sub_largeAU0_isBigO (c : ℝ) {x : ℝ} (hx : 0 < x) :
    (fun κ : ℝ => largeAU c κ (2 * Real.sqrt (κ * x)) - largeAU0 c (2 * Real.sqrt (κ * x)))
      =O[atTop] (fun κ : ℝ => (Real.sqrt κ)⁻¹) := by
  set A := |(c - 1) ^ 2 - 1 / 4|
  set N0 := ‖largeAU0 c 1‖ + ‖largeAU0' c 1‖
  set X := x * Real.sqrt x / 2
  obtain ⟨C0, hC0⟩ := (largeAU_sub_largeAU0_isBigO_const c 1).bound
  obtain ⟨C1, hC1⟩ := (largeAU'_sub_largeAU0'_isBigO_const c 1).bound
  set Cδ := |C0| + |C1|
  have hX0 : 0 ≤ X := by positivity
  refine Asymptotics.IsBigO.of_bound
    ((Cδ + (N0 + Cδ) * Real.exp (A + X) * X) * Real.exp A) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ), hC0, hC1,
    (tendsto_two_sqrt_mul x hx).eventually_ge_atTop 1] with κ hκ1 h0 h1 hS1
  have hκ : 0 < κ := by linarith
  have hsk : 1 ≤ Real.sqrt κ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hκ1
  have hsk0 : 0 < Real.sqrt κ := by linarith
  set S := 2 * Real.sqrt (κ * x)
  have hb := norm_largeAU_sub_largeAU0_le_sharp c hκ one_pos hS1
  simp only [div_one] at hb
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hκ] at h0 h1
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hsk0]
  set δ := ‖largeAU c κ 1 - largeAU0 c 1‖ + ‖largeAU' c κ 1 - largeAU0' c 1‖
  have hinv : κ⁻¹ ≤ (Real.sqrt κ)⁻¹ := by
    calc κ⁻¹ = (Real.sqrt κ)⁻¹ * (Real.sqrt κ)⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt hκ.le]
      _ ≤ (Real.sqrt κ)⁻¹ :=
          mul_le_of_le_one_left (inv_nonneg.mpr hsk0.le) (inv_le_one_of_one_le₀ hsk)
  have hδ : δ ≤ Cδ * (Real.sqrt κ)⁻¹ := by
    have : δ ≤ Cδ * κ⁻¹ := by
      have := le_abs_self C0
      have := le_abs_self C1
      have hk0 : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
      simp only [δ, Cδ]
      nlinarith
    exact this.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
  have hδ1 : δ ≤ Cδ := hδ.trans (mul_le_of_le_one_right (by positivity)
    (inv_le_one_of_one_le₀ hsk))
  have hN : ‖largeAU c κ 1‖ + ‖largeAU' c κ 1‖ ≤ N0 + Cδ := by
    have h1 := norm_le_norm_add_norm_sub' (largeAU c κ 1) (largeAU0 c 1)
    have h2 := norm_le_norm_add_norm_sub' (largeAU' c κ 1) (largeAU0' c 1)
    simp only [N0]
    linarith
  have hBeq : S ^ 3 / (16 * κ ^ 2) = X * (Real.sqrt κ)⁻¹ := by
    rw [cube_div_eq x hx hκ]
    simp only [X]
    field_simp
  have hBX : S ^ 3 / (16 * κ ^ 2) ≤ X := by
    rw [hBeq]
    exact mul_le_of_le_one_right hX0 (inv_le_one_of_one_le₀ hsk)
  have hE : Real.exp (A + S ^ 3 / (16 * κ ^ 2)) ≤ Real.exp (A + X) :=
    Real.exp_le_exp.mpr (by linarith)
  have hA0 : 0 ≤ A := abs_nonneg _
  have hN0 : 0 ≤ N0 := by positivity
  have hCδ : 0 ≤ Cδ := by positivity
  have hsi : 0 ≤ (Real.sqrt κ)⁻¹ := by positivity
  refine hb.trans ?_
  have h2 : (‖largeAU c κ 1‖ + ‖largeAU' c κ 1‖) * Real.exp (A + S ^ 3 / (16 * κ ^ 2)) *
      (S ^ 3 / (16 * κ ^ 2)) ≤ (N0 + Cδ) * Real.exp (A + X) * X * (Real.sqrt κ)⁻¹ := by
    calc (‖largeAU c κ 1‖ + ‖largeAU' c κ 1‖) * Real.exp (A + S ^ 3 / (16 * κ ^ 2)) *
          (S ^ 3 / (16 * κ ^ 2)) ≤ (N0 + Cδ) * Real.exp (A + X) * (S ^ 3 / (16 * κ ^ 2)) := by
          have hB0 : 0 ≤ S ^ 3 / (16 * κ ^ 2) := by rw [hBeq]; positivity
          gcongr
      _ = (N0 + Cδ) * Real.exp (A + X) * X * (Real.sqrt κ)⁻¹ := by rw [hBeq]; ring
  calc (δ + (‖largeAU c κ 1‖ + ‖largeAU' c κ 1‖) * Real.exp (A + S ^ 3 / (16 * κ ^ 2)) *
        (S ^ 3 / (16 * κ ^ 2))) * Real.exp A
      ≤ (Cδ * (Real.sqrt κ)⁻¹ + (N0 + Cδ) * Real.exp (A + X) * X * (Real.sqrt κ)⁻¹) *
          Real.exp A := by gcongr
    _ = (Cδ + (N0 + Cδ) * Real.exp (A + X) * X) * Real.exp A * (Real.sqrt κ)⁻¹ := by ring

/-! ### DLMF 13.8.9 -/

/-- The prefactor identity behind the Bessel form:
`√S (κx)^{(c-1)/2} e^{-x/2} 𝐌(c/2 - κ, c, x) - √S J_{c-1}(S) = 2^{1-c} (u_κ(S) - u₀(S))` with
`S = 2√(κx)`. -/
theorem largeA_besselJ_identity (c : ℝ) {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) :
    ((Real.sqrt (2 * Real.sqrt (κ * x)) * (κ * x) ^ ((c - 1) / 2) *
          Real.exp (-(x / 2)) : ℝ) : ℂ) *
        regularizedHGFun {((c / 2 - κ : ℝ) : ℂ)} {(c : ℂ)} (x : ℂ) -
      ((Real.sqrt (2 * Real.sqrt (κ * x)) : ℝ) : ℂ) *
        besselJ ((c - 1 : ℝ) : ℂ) ((2 * Real.sqrt (κ * x) : ℝ) : ℂ) =
      ((((2 : ℝ) ^ (1 - c) : ℝ)) : ℂ) *
        (largeAU c κ (2 * Real.sqrt (κ * x)) - largeAU0 c (2 * Real.sqrt (κ * x))) := by
  have hkx : 0 < κ * x := by positivity
  have hS : 0 < 2 * Real.sqrt (κ * x) := by positivity
  have hS2 : (2 * Real.sqrt (κ * x)) ^ 2 = 4 * (κ * x) := by
    rw [mul_pow, Real.sq_sqrt hkx.le]
    norm_num
  have harg : (2 * Real.sqrt (κ * x)) ^ 2 / (4 * κ) = x := by
    rw [hS2]
    field_simp
  have hexp : (2 * Real.sqrt (κ * x)) ^ 2 / (8 * κ) = x / 2 := by
    rw [hS2]
    field_simp
    ring
  rw [largeAU0_eq c hS]
  simp only [largeAU, largeAP, largeAW, largeAParam]
  rw [harg, hexp]
  have hpre : (2 : ℝ) ^ (1 - c) * (2 * Real.sqrt (κ * x)) ^ (c - 1 / 2) =
      Real.sqrt (2 * Real.sqrt (κ * x)) * (κ * x) ^ ((c - 1) / 2) := by
    have h1 : (2 * Real.sqrt (κ * x)) ^ (c - 1 / 2) =
        Real.sqrt (2 * Real.sqrt (κ * x)) * (2 * Real.sqrt (κ * x)) ^ (c - 1) := by
      rw [show Real.sqrt (2 * Real.sqrt (κ * x)) = (2 * Real.sqrt (κ * x)) ^ (1 / 2 : ℝ) from
        Real.sqrt_eq_rpow _, ← Real.rpow_add hS]
      congr 1
      ring
    have h2 : (2 * Real.sqrt (κ * x)) ^ (c - 1) =
        (2 : ℝ) ^ (c - 1) * (κ * x) ^ ((c - 1) / 2) := by
      rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hkx.le]
      congr 2
      ring
    have h3 : (2 : ℝ) ^ (1 - c) * (2 : ℝ) ^ (c - 1) = 1 := by
      rw [← Real.rpow_add two_pos]
      simp
    rw [h1, h2]
    linear_combination Real.sqrt (2 * Real.sqrt (κ * x)) * (κ * x) ^ ((c - 1) / 2) * h3
  have h3 : (2 : ℝ) ^ (1 - c) * (2 : ℝ) ^ (c - 1) = 1 := by
    rw [← Real.rpow_add two_pos]
    simp
  have hprec := congrArg (fun r : ℝ => (r : ℂ)) hpre
  have h3c := congrArg (fun r : ℝ => (r : ℂ)) h3
  simp only [ofReal_mul, ofReal_one] at hprec h3c ⊢
  linear_combination -((Real.exp (-(x / 2)) : ℂ) *
      regularizedHGFun {((c / 2 - κ : ℝ) : ℂ)} {(c : ℂ)} (x : ℂ) * hprec) +
    (Real.sqrt (2 * Real.sqrt (κ * x)) : ℂ) *
      besselJ ((c - 1 : ℝ) : ℂ) (((2 : ℝ) : ℂ) * (Real.sqrt (κ * x) : ℂ)) * h3c

/-- `c/2 - a → +∞` as `a → -∞`. -/
theorem tendsto_half_sub_atBot (c : ℝ) : Tendsto (fun a : ℝ => c / 2 - a) atBot atTop :=
  (tendsto_neg_atBot_atTop.atTop_add (tendsto_const_nhds (x := c / 2))).congr fun a => by ring

/-- `(c/2 - a)^{-1/2} = O(|a|^{-1/2})` as `a → -∞`. -/
theorem recip_sqrt_half_sub_isBigO (c : ℝ) :
    (fun a : ℝ => (Real.sqrt (c / 2 - a))⁻¹) =O[atBot] (fun a : ℝ => |a| ^ (-(1 / 2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (Real.sqrt 2) ?_
  filter_upwards [eventually_le_atBot (-|c| - 1)] with a ha
  have ha0 : a < 0 := by linarith [abs_nonneg c]
  have habs : |a| = -a := abs_of_neg ha0
  have hκ : |a| / 2 ≤ c / 2 - a := by
    rw [habs]
    have := neg_abs_le c
    linarith
  have hapos : 0 < |a| := by rw [habs]; linarith
  have hκpos : 0 < c / 2 - a := lt_of_lt_of_le (by positivity) hκ
  have hinv : (c / 2 - a)⁻¹ ≤ 2 * |a|⁻¹ :=
    calc (c / 2 - a)⁻¹ ≤ (|a| / 2)⁻¹ := inv_anti₀ (by positivity) hκ
      _ = 2 * |a|⁻¹ := by field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.mpr hκpos),
    abs_of_pos (Real.rpow_pos_of_pos hapos _), Real.rpow_neg hapos.le, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_mul (by norm_num)]
  exact Real.sqrt_le_sqrt hinv

/-- **DLMF 13.8.9**: as `a → -∞` with `c` fixed and fixed `x > 0`,
`𝐌(a, c, x) = e^{x/2} ((c/2 - a)x)^{1/2 - c/2} (J_{c-1}(S) + env J_{c-1}(S) O(|a|^{-1/2}))`
with `S = √(2x(c - 2a))`. This is stronger than DLMF, which assumes `b ≥ 1`: here
`𝐌 = M/Γ(c)` is the regularized function and `c` is any real number. Since
`env J_{c-1}(S) ≍ S^{-1/2}` as `S → ∞`, the error term is written as `O(S^{-1/2} |a|^{-1/2})`. -/
@[dlmf 13.8.E9]
theorem regularizedConfluent_atBot_besselJ_isBigO (c : ℝ) {x : ℝ} (hx : 0 < x) :
    (fun a : ℝ => ((((c / 2 - a) * x) ^ ((c - 1) / 2) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
          regularizedHGFun {(a : ℂ)} {(c : ℂ)} (x : ℂ) -
        besselJ ((c - 1 : ℝ) : ℂ) ((Real.sqrt (2 * x * (c - 2 * a)) : ℝ) : ℂ))
      =O[atBot] (fun a : ℝ => Real.sqrt (2 * x * (c - 2 * a)) ^ (-(1 / 2 : ℝ)) *
        |a| ^ (-(1 / 2 : ℝ))) := by
  have hκ := tendsto_half_sub_atBot c
  have h := ((largeAU_sub_largeAU0_isBigO c hx).comp_tendsto hκ).const_mul_left
    ((((2 : ℝ) ^ (1 - c) : ℝ)) : ℂ)
  have hr : (fun a : ℝ => ((Real.sqrt (2 * x * (c - 2 * a)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
      =O[atBot] (fun a : ℝ => Real.sqrt (2 * x * (c - 2 * a)) ^ (-(1 / 2 : ℝ))) :=
    Asymptotics.IsBigO.of_bound 1 (by
      filter_upwards with a
      rw [Complex.norm_real, one_mul])
  have h2 := hr.mul (h.trans (recip_sqrt_half_sub_isBigO c))
  refine h2.congr' ?_ EventuallyEq.rfl
  filter_upwards [hκ.eventually (eventually_gt_atTop 0)] with a ha
  obtain ⟨κ, rfl⟩ : ∃ κ, a = c / 2 - κ := ⟨c / 2 - a, by ring⟩
  have hk : c / 2 - (c / 2 - κ) = κ := by ring
  simp only [Function.comp_apply, hk] at ha ⊢
  have hkx : 0 < κ * x := by positivity
  have hSeq : Real.sqrt (2 * x * (c - 2 * (c / 2 - κ))) = 2 * Real.sqrt (κ * x) := by
    rw [show 2 * x * (c - 2 * (c / 2 - κ)) = 2 ^ 2 * (κ * x) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [hSeq]
  have hid := largeA_besselJ_identity c ha hx
  set S := 2 * Real.sqrt (κ * x)
  have hS : 0 < S := by positivity
  have hsS : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hrp : S ^ (-(1 / 2 : ℝ)) = (Real.sqrt S)⁻¹ := by
    rw [Real.rpow_neg hS.le, Real.sqrt_eq_rpow]
  have key : (((κ * x) ^ ((c - 1) / 2) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
        regularizedHGFun {((c / 2 - κ : ℝ) : ℂ)} {(c : ℂ)} (x : ℂ) -
      besselJ ((c - 1 : ℝ) : ℂ) (S : ℂ) =
      (((Real.sqrt S)⁻¹ : ℝ) : ℂ) * (((((2 : ℝ) ^ (1 - c) : ℝ)) : ℂ) *
        (largeAU c κ S - largeAU0 c S)) := by
    rw [← hid]
    have hs' : ((Real.sqrt S : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsS.ne'
    push_cast
    field_simp
  rw [hrp, key]

/-! ### The cosine form with rate -/

/-- `u₀(S) = 2^{c-1} √(2/π) cos(S - cπ/2 + π/4) + O(S⁻¹)` as `S → +∞`. -/
lemma largeAU0_sub_cos_isBigO (c : ℝ) :
    (fun S : ℝ => largeAU0 c S -
      (((2 : ℝ) ^ (c - 1) * Real.sqrt (2 / π) * Real.cos (S - c * π / 2 + π / 4) : ℝ) : ℂ))
      =O[atTop] (fun S : ℝ => S⁻¹) := by
  have hJ := DLMF.Bessel.besselJ_sub_cos_isBigO ((c - 1 : ℝ) : ℂ)
  have h0 : (fun s : ℝ => ((((2 : ℝ) ^ (c - 1) * Real.sqrt s : ℝ)) : ℂ)) =O[atTop]
      (fun s => (2 : ℝ) ^ (c - 1) * Real.sqrt s) :=
    Asymptotics.IsBigO.of_bound 1 (by
      filter_upwards with s
      rw [Complex.norm_real, one_mul])
  have h1 := h0.mul hJ
  have h2 : (fun s : ℝ => (2 : ℝ) ^ (c - 1) * Real.sqrt s * s ^ (-(3 / 2) : ℝ)) =O[atTop]
      (fun s : ℝ => s⁻¹) := by
    refine Asymptotics.IsBigO.of_bound ((2 : ℝ) ^ (c - 1)) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hs, ← Real.rpow_neg_one]
    norm_num
    rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  refine (h1.trans h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [largeAU0_eq c hs]
  have hsq : Real.sqrt s * Real.sqrt (2 / (π * s)) = Real.sqrt (2 / π) := by
    rw [← Real.sqrt_mul hs.le]
    congr 1
    field_simp
  have hc : cos ((s : ℂ) - ((c - 1 : ℝ) : ℂ) * π / 2 - π / 4) =
      ((Real.cos (s - c * π / 2 + π / 4) : ℝ) : ℂ) := by
    rw [show s - c * π / 2 + π / 4 = s - (c - 1) * π / 2 - π / 4 by ring]
    push_cast
    rfl
  rw [hc]
  have hsq' : ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt (2 / (π * s)) : ℝ) : ℂ) =
      ((Real.sqrt (2 / π) : ℝ) : ℂ) := by
    rw [← ofReal_mul, hsq]
  simp only [ofReal_mul]
  linear_combination (-(((2 : ℝ) ^ (c - 1) : ℝ) : ℂ) *
    ((Real.cos (s - c * π / 2 + π / 4) : ℝ) : ℂ)) * hsq'

/-- `S^{c-1/2} e^{-x/2} 𝐌(a, c, x) = 2^{c-1} √(2/π) cos(S - cπ/2 + π/4) + O(κ^{-1/2})` along
`S = 2√(κx)`, `a = c/2 - κ`. -/
theorem largeAU_sub_cos_isBigO (c : ℝ) {x : ℝ} (hx : 0 < x) :
    (fun κ : ℝ => largeAU c κ (2 * Real.sqrt (κ * x)) -
      (((2 : ℝ) ^ (c - 1) * Real.sqrt (2 / π) *
        Real.cos (2 * Real.sqrt (κ * x) - c * π / 2 + π / 4) : ℝ) : ℂ))
      =O[atTop] (fun κ : ℝ => (Real.sqrt κ)⁻¹) := by
  have h1 := largeAU_sub_largeAU0_isBigO c hx
  have h2 := (largeAU0_sub_cos_isBigO c).comp_tendsto (tendsto_two_sqrt_mul x hx)
  have h3 : ((fun S : ℝ => S⁻¹) ∘ fun κ : ℝ => 2 * Real.sqrt (κ * x)) =O[atTop]
      (fun κ : ℝ => (Real.sqrt κ)⁻¹) := by
    refine Asymptotics.IsBigO.of_bound (2 * Real.sqrt x)⁻¹ ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
    have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    simp only [Function.comp_apply]
    rw [Real.sqrt_mul hκ.le, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_inv,
      abs_of_pos (by positivity), abs_of_pos hsk]
    apply le_of_eq
    field_simp
  refine (h1.add (h2.trans h3)).congr_left fun κ => ?_
  simp only [Function.comp_apply]
  ring

/-- **The Erdélyi–Schmidt–Fejér asymptotics with rate** (Beals–Wong (13.2.8), (8.1.12)): for
real `c` and fixed `x > 0`, as `a → -∞`,
`√π ((c/2 - a)x)^{c/2-1/4} e^{-x/2} 𝐌(a, c, x) = cos(2√((c/2 - a)x) - cπ/2 + π/4)
  + O(|a|^{-1/2})`. -/
theorem regularizedConfluent_atBot_cos_isBigO (c : ℝ) {x : ℝ} (hx : 0 < x) :
    (fun a : ℝ =>
      ((Real.sqrt π * ((c / 2 - a) * x) ^ (c / 2 - 1 / 4) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
          regularizedHGFun {(a : ℂ)} {(c : ℂ)} (x : ℂ) -
        ((Real.cos (2 * Real.sqrt ((c / 2 - a) * x) - c * π / 2 + π / 4) : ℝ) : ℂ))
      =O[atBot] (fun a : ℝ => |a| ^ (-(1 / 2 : ℝ))) := by
  have hκ := tendsto_half_sub_atBot c
  have h := (((largeAU_sub_cos_isBigO c hx).comp_tendsto hκ).const_mul_left
    (((2 : ℝ) ^ (1 / 2 - c) * Real.sqrt π : ℝ) : ℂ)).trans (recip_sqrt_half_sub_isBigO c)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hκ.eventually (eventually_gt_atTop 0)] with a ha
  obtain ⟨κ, rfl⟩ : ∃ κ, a = c / 2 - κ := ⟨c / 2 - a, by ring⟩
  have hk : c / 2 - (c / 2 - κ) = κ := by ring
  simp only [Function.comp_apply, hk] at ha ⊢
  have hkx : 0 ≤ κ * x := by positivity
  have hS2 : (2 * Real.sqrt (κ * x)) ^ 2 = 4 * (κ * x) := by
    rw [mul_pow, Real.sq_sqrt hkx]
    norm_num
  have harg : (2 * Real.sqrt (κ * x)) ^ 2 / (4 * κ) = x := by
    rw [hS2]
    field_simp
  have hexp : (2 * Real.sqrt (κ * x)) ^ 2 / (8 * κ) = x / 2 := by
    rw [hS2]
    field_simp
    ring
  simp only [largeAU, largeAP, largeAW, largeAParam]
  rw [harg, hexp]
  have hr := two_rpow_mul_two_sqrt_rpow hkx c
  have hc := two_rpow_sqrt_pi_mul c
  rw [mul_sub]
  congr 1
  · rw [← mul_assoc, ← ofReal_mul]
    congr 2
    rw [← hr]
    ring
  · rw [← ofReal_mul]
    congr 1
    calc (2 : ℝ) ^ (1 / 2 - c) * Real.sqrt π *
          ((2 : ℝ) ^ (c - 1) * Real.sqrt (2 / π) *
            Real.cos (2 * Real.sqrt (κ * x) - c * π / 2 + π / 4))
        = ((2 : ℝ) ^ (1 / 2 - c) * Real.sqrt π * ((2 : ℝ) ^ (c - 1) * Real.sqrt (2 / π))) *
            Real.cos (2 * Real.sqrt (κ * x) - c * π / 2 + π / 4) := by ring
      _ = _ := by rw [hc, one_mul]

/-! ### Fejér's formula with rate (DLMF 18.15.14) -/

/-- `Γ(t + a)/Γ(t + b) = t^{a-b} (1 + O(t⁻¹))` as `t → +∞`. -/
theorem Gamma_ratio_sub_one_isBigO (a b : ℂ) :
    (fun t : ℝ => Complex.Gamma (t + a) / Complex.Gamma (t + b) / (t : ℂ) ^ (a - b) - 1)
      =O[atTop] (fun t : ℝ => t⁻¹) := by
  obtain ⟨C, hC⟩ := (DLMF.Gamma.Gamma_ratio_expansion a b 1).bound
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with t ht htp
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast htp.ne'
  have hp : (t : ℂ) ^ (a - b) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h => ht0 h.1
  simp only [Finset.range_one, Finset.sum_singleton, DLMF.Gamma.stirlingRatioG_zero, pow_zero,
    div_one, mul_one] at ht
  rw [show a - b - ((1 : ℕ) : ℂ) = (a - b) - 1 by push_cast; ring, cpow_sub (a - b) 1 ht0,
    cpow_one] at ht
  rw [div_sub_one hp, norm_div, Real.norm_eq_abs, abs_inv, abs_of_pos htp]
  rw [norm_div] at ht
  have hn : 0 < ‖(t : ℂ) ^ (a - b)‖ := norm_pos_iff.mpr hp
  rw [div_le_iff₀ hn]
  calc ‖Complex.Gamma (t + a) / Complex.Gamma (t + b) - (t : ℂ) ^ (a - b)‖
      ≤ C * (‖(t : ℂ) ^ (a - b)‖ / ‖(t : ℂ)‖) := ht
    _ = C * t⁻¹ * ‖(t : ℂ) ^ (a - b)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htp]
        ring

/-- `√(t + d) - √t ≤ d/√t`. -/
theorem sqrt_add_sub_sqrt_le {d t : ℝ} (hd : 0 ≤ d) (ht : 0 < t) :
    Real.sqrt (t + d) - Real.sqrt t ≤ d / Real.sqrt t := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hprod : (Real.sqrt (t + d) - Real.sqrt t) * (Real.sqrt (t + d) + Real.sqrt t) = d := by
    have h1 := Real.sq_sqrt (show 0 ≤ t + d by linarith)
    have h2 := Real.sq_sqrt ht.le
    nlinarith
  have hdiff : 0 ≤ Real.sqrt (t + d) - Real.sqrt t :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  rw [le_div_iff₀ hst]
  nlinarith [Real.sqrt_nonneg (t + d)]

/-- **Fejér's formula with rate** (DLMF 18.15.14 with `M = 1`, where `a₀ = 1`; Szegő (8.22.4)):
for `α > -1` and fixed `x > 0`,
`L_n^{(α)}(x) = n^{α/2-1/4} e^{x/2} π^{-1/2} x^{-α/2-1/4} (cos θ_n + O(n^{-1/2}))` with
`θ_n = 2√(nx) - (α/2 + 1/4)π`. -/
@[dlmf 18.15.E14]
theorem laguerrePolyL_fejer_isBigO {α : ℝ} (hα : -1 < α) {x : ℝ} (hx : 0 < x) :
    (fun n : ℕ => (((n : ℝ) ^ (1 / 4 - α / 2) : ℝ) : ℂ) *
        DLMF.OrthogonalPolynomials.laguerrePolyL (α : ℂ) n (x : ℂ) -
      ((Real.exp (x / 2) * x ^ (-(α / 2) - 1 / 4) / Real.sqrt π *
        Real.cos (2 * Real.sqrt (n * x) - α * π / 2 - π / 4) : ℝ) : ℂ))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  set c : ℝ := α + 1 with hcdef
  set p : ℝ := α / 2 + 1 / 4 with hpdef
  set K : ℝ := Real.exp (x / 2) * x ^ (-(α / 2) - 1 / 4) / Real.sqrt π with hK
  have hc0 : 0 < c := by linarith
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hn : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hnat
  -- `n⁻¹ = O(n^{-1/2})` and `1 = O(1)` along the naturals
  have hinv : (fun n : ℕ => ((n : ℝ))⁻¹) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith),
      abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hn0 (by norm_num)
  have hhalf : (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [one_mul, norm_one, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn0 (by norm_num)
  -- the cosine form along `a = -n`
  set E : ℕ → ℂ := fun n => ((Real.sqrt π * ((c / 2 - -(n : ℝ)) * x) ^ (c / 2 - 1 / 4) *
      Real.exp (-(x / 2)) : ℝ) : ℂ) * regularizedHGFun {((-(n : ℝ) : ℝ) : ℂ)} {(c : ℂ)} (x : ℂ) -
    ((Real.cos (2 * Real.sqrt ((c / 2 - -(n : ℝ)) * x) - c * π / 2 + π / 4) : ℝ) : ℂ) with hEdef
  have hE : E =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    refine ((regularizedConfluent_atBot_cos_isBigO c hx).comp_tendsto hn).trans ?_
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with n
    simp only [Function.comp_apply, abs_neg, Nat.abs_cast, one_mul]
    exact le_rfl
  set cK : ℕ → ℂ := fun n =>
    ((Real.cos (2 * Real.sqrt ((c / 2 - -(n : ℝ)) * x) - c * π / 2 + π / 4) : ℝ) : ℂ)
  set cN : ℕ → ℂ := fun n =>
    ((Real.cos (2 * Real.sqrt (n * x) - α * π / 2 - π / 4) : ℝ) : ℂ)
  -- the Gamma ratio
  set R : ℕ → ℂ := fun n => Complex.Gamma ((n : ℂ) + c) / (n ! : ℂ) / (((n : ℝ) ^ α : ℝ) : ℂ)
  have hR : (fun n => R n - 1) =O[atTop] (fun n : ℕ => ((n : ℝ))⁻¹) := by
    have h := (Gamma_ratio_sub_one_isBigO (c : ℂ) 1).comp_tendsto hnat
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards with n
    simp only [Function.comp_apply, R]
    rw [ofReal_natCast, Complex.Gamma_nat_eq_factorial, ofReal_cpow (Nat.cast_nonneg n)]
    congr 3
    rw [hcdef]
    push_cast
    ring
  set Q : ℕ → ℝ := fun n => ((n : ℝ) / (n + c / 2)) ^ p
  have hQ : (fun n => ((Q n : ℝ) : ℂ) - 1) =O[atTop] (fun n : ℕ => ((n : ℝ))⁻¹) := by
    -- `(1 + y)^{-p} - 1 = O(y)` near `0`
    have hd : HasDerivAt (fun y : ℝ => (1 + y) ^ (-p)) (-p * (1 + 0) ^ (-p - 1)) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_add 1).rpow_const (p := -p) (Or.inl (by norm_num))
      simpa using this
    have h0 := hd.isBigO_sub
    simp only [add_zero, Real.one_rpow, sub_zero] at h0
    have hy : Tendsto (fun n : ℕ => (c / 2) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnat
    have h1 := h0.comp_tendsto hy
    have h2 : (fun n : ℕ => (c / 2) / (n : ℝ)) =O[atTop] (fun n : ℕ => ((n : ℝ))⁻¹) := by
      refine Asymptotics.IsBigO.of_bound |c / 2| ?_
      filter_upwards with n
      rw [div_eq_mul_inv, norm_mul, Real.norm_eq_abs]
    refine (Asymptotics.IsBigO.of_norm_left ?_)
    refine ((h1.trans h2).norm_left).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    simp only [Function.comp_apply, Q]
    rw [← ofReal_one, ← ofReal_sub, Complex.norm_real]
    congr 2
    rw [show (n : ℝ) / (n + c / 2) = (1 + c / 2 / n)⁻¹ by field_simp,
      Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), hpdef]
  have hRQ : (fun n => R n * (Q n : ℂ) - 1) =O[atTop] (fun n : ℕ => ((n : ℝ))⁻¹) := by
    have hinv1 : (fun n : ℕ => ((n : ℝ))⁻¹) =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
      (tendsto_inv_atTop_zero.comp hnat).isBigO_one ℝ
    have hQb : (fun n => ((Q n : ℝ) : ℂ)) =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
      ((hQ.trans hinv1).add (isBigO_const_const (1 : ℂ) one_ne_zero atTop)).congr_left
        fun n => by ring
    have := (((hR.mul hQb).congr_right fun n => mul_one _).add hQ).congr_left
      (fun n => show (R n - 1) * (Q n : ℂ) + ((Q n : ℂ) - 1) = R n * (Q n : ℂ) - 1 by ring)
    exact this.congr_right fun n => by simp
  -- the phase difference
  have hcos : (fun n => cK n - cN n) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound (2 * (c / 2 * x) / Real.sqrt x) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnx : 0 < (n : ℝ) * x := by positivity
    simp only [cK, cN]
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    have hph : 2 * Real.sqrt ((c / 2 - -(n : ℝ)) * x) - c * π / 2 + π / 4 -
        (2 * Real.sqrt (n * x) - α * π / 2 - π / 4) =
        2 * (Real.sqrt ((n : ℝ) * x + c / 2 * x) - Real.sqrt ((n : ℝ) * x)) := by
      rw [show (c / 2 - -(n : ℝ)) * x = (n : ℝ) * x + c / 2 * x by ring, hcdef]
      ring
    rw [hph]
    have hb := sqrt_add_sub_sqrt_le (d := c / 2 * x) (by positivity) hnx
    have hpos : 0 ≤ Real.sqrt ((n : ℝ) * x + c / 2 * x) - Real.sqrt ((n : ℝ) * x) :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by nlinarith))
    rw [abs_of_nonneg (by linarith), Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow]
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    calc 2 * (Real.sqrt ((n : ℝ) * x + c / 2 * x) - Real.sqrt ((n : ℝ) * x))
        ≤ 2 * (c / 2 * x / Real.sqrt ((n : ℝ) * x)) := by linarith
      _ = 2 * (c / 2 * x) / Real.sqrt x * (Real.sqrt n)⁻¹ := by
          rw [Real.sqrt_mul hn0.le]
          field_simp
  -- assemble
  have hcKb : cK =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with n
    simp only [cK, Complex.norm_real, Real.norm_eq_abs, norm_one, one_mul]
    exact Real.abs_cos_le_one _
  have hRQ' := hRQ.trans hinv
  have hRQb := hRQ'.trans hhalf
  have t1 := (hRQ'.mul hcKb).congr_right (fun n => mul_one _)
  have t2 := (hRQb.mul hE).congr_right (fun n => one_mul _)
  have hlim := (((t1.add t2).add hE).add hcos).const_mul_left (K : ℂ)
  refine hlim.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hκ : 0 < c / 2 - -(n : ℝ) := by linarith
  have hcpole : ∀ k : ℕ, ((α : ℂ) + 1) ≠ -k := by
    intro k hk
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hL : DLMF.OrthogonalPolynomials.laguerrePolyL (α : ℂ) n (x : ℂ) =
      Complex.Gamma ((n : ℂ) + c) / (n ! : ℂ) *
        regularizedHGFun {((-(n : ℝ) : ℝ) : ℂ)} {(c : ℂ)} (x : ℂ) := by
    rw [DLMF.OrthogonalPolynomials.laguerrePolyL, kummerM_eq_mul_regularizedHGFun hcpole]
    have hG := Complex.Gamma_add_nat_div_Gamma_eq (n := n) ((α : ℂ) + 1) hcpole
    have hG0 : Complex.Gamma ((α : ℂ) + 1) ≠ 0 := Complex.Gamma_ne_zero hcpole
    rw [show ((-(n : ℝ) : ℝ) : ℂ) = -(n : ℂ) by push_cast; ring,
      show ((c : ℝ) : ℂ) = (α : ℂ) + 1 by rw [hcdef]; push_cast; ring,
      show (n : ℂ) + ((α : ℂ) + 1) = (α : ℂ) + 1 + n by ring]
    rw [poch, ← hG]
    field_simp
  have hpow : (n : ℝ) ^ (1 / 4 - α / 2) * (n : ℝ) ^ α = Q n * K *
      (Real.sqrt π * ((c / 2 - -(n : ℝ)) * x) ^ (c / 2 - 1 / 4) * Real.exp (-(x / 2))) := by
    have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    simp only [Q, hK]
    rw [← Real.rpow_add hn0, Real.div_rpow hn0.le (by linarith),
      Real.mul_rpow hκ.le hx.le,
      show c / 2 - 1 / 4 = p by rw [hcdef, hpdef]; ring,
      show 1 / 4 - α / 2 + α = p by rw [hpdef]; ring,
      show -(α / 2) - 1 / 4 = -p by rw [hpdef]; ring, Real.rpow_neg hx.le,
      show (n : ℝ) + c / 2 = c / 2 - -(n : ℝ) by ring]
    set κ := c / 2 - -(n : ℝ) with hκdef
    have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx p
    have hkp : 0 < κ ^ p := Real.rpow_pos_of_pos hκ p
    have he : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have : (n : ℝ) ^ p / κ ^ p * (Real.exp (x / 2) * (x ^ p)⁻¹ / Real.sqrt π) *
        (Real.sqrt π * (κ ^ p * x ^ p) * Real.exp (-(x / 2))) =
        (n : ℝ) ^ p * (Real.exp (x / 2) * Real.exp (-(x / 2))) := by
      field_simp
    rw [this, he, mul_one]
  have hR' : R n * (((n : ℝ) ^ α : ℝ) : ℂ) = Complex.Gamma ((n : ℂ) + c) / (n ! : ℂ) := by
    have : (((n : ℝ) ^ α : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hn0 α).ne'
    simp only [R]
    field_simp
  simp only [hEdef, cK, cN]
  rw [hL, ← hR']
  have hpowc := congrArg (fun r : ℝ => (r : ℂ)) hpow
  simp only [ofReal_mul] at hpowc ⊢
  linear_combination (-R n) * regularizedHGFun {((-(n : ℝ) : ℝ) : ℂ)} {(c : ℂ)} (x : ℂ) * hpowc

/-! ### DLMF 13.8.10 -/

/-- The connection formula for `U` in the normalization of DLMF 13.8.10:
`x^{(c-1)/2} e^{-x/2} U(a, c, x)/Γ(κ + 1/2) = (H₁ sin(π(c-a)) B₁ - H₂ sin(πa) B₂)/sin(πc)`
with `κ = c/2 - a`, `H₁ = Γ(c-a)/(Γ(κ+1/2) κ^{(c-1)/2})`, `H₂ = Γ(1-a)/(Γ(κ+1/2) κ^{(1-c)/2})`,
`B₁ = (κx)^{(c-1)/2} e^{-x/2} 𝐌(a, c, x)` and `B₂ = (κx)^{(1-c)/2} e^{-x/2} 𝐌(a-c+1, 2-c, x)`. -/
theorem kummerU_large_a_eq_half (c : ℝ) (hc : ∀ k : ℤ, c ≠ k) {a x : ℝ} (hx : 0 < x)
    (hκ : 0 < c / 2 - a) (hca : 0 < c - a) (h1a : 0 < 1 - a) :
    ((x ^ ((c - 1) / 2) * Real.exp (-(x / 2)) : ℝ) : ℂ) /
        Complex.Gamma (((c / 2 - a + 1 / 2 : ℝ) : ℂ)) * kummerU (a : ℂ) (c : ℂ) (x : ℂ) =
      (Complex.Gamma (((c - a : ℝ) : ℂ)) /
            (Complex.Gamma (((c / 2 - a + 1 / 2 : ℝ) : ℂ)) *
              (((c / 2 - a) ^ ((c - 1) / 2) : ℝ) : ℂ)) *
          ((Real.sin (π * (c - a)) : ℝ) : ℂ) *
          (((((c / 2 - a) * x) ^ ((c - 1) / 2) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
            regularizedHGFun {(a : ℂ)} {(c : ℂ)} (x : ℂ)) -
        Complex.Gamma (((1 - a : ℝ) : ℂ)) /
            (Complex.Gamma (((c / 2 - a + 1 / 2 : ℝ) : ℂ)) *
              (((c / 2 - a) ^ ((1 - c) / 2) : ℝ) : ℂ)) *
          ((Real.sin (π * a) : ℝ) : ℂ) *
          (((((c / 2 - a) * x) ^ ((1 - c) / 2) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
            regularizedHGFun {((a - c + 1 : ℝ) : ℂ)} {((2 - c : ℝ) : ℂ)} (x : ℂ))) /
        ((Real.sin (π * c) : ℝ) : ℂ) := by
  set κ := c / 2 - a with hκdef
  have hcZ : ∀ k : ℤ, (c : ℂ) ≠ k := fun k h => hc k (by exact_mod_cast h)
  have hcN : ∀ k : ℕ, (c : ℂ) ≠ -k := fun k h => hcZ (-k) (by push_cast; exact h)
  have h2N : ∀ k : ℕ, (2 : ℂ) - c ≠ -k := fun k h =>
    hcZ (k + 2) (by push_cast; linear_combination -h)
  have hs : Real.sin (π * c) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
    exact hc k (by nlinarith [Real.pi_pos])
  have hs' : ((Real.sin (π * c) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hGκ : Complex.Gamma (((κ + 1 / 2 : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hGca : Complex.Gamma (((c - a : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.Gamma_ofReal]; exact_mod_cast (Real.Gamma_pos_of_pos hca).ne'
  have hG1a : Complex.Gamma (((1 - a : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.Gamma_ofReal]; exact_mod_cast (Real.Gamma_pos_of_pos h1a).ne'
  have hr1 := recip_Gamma_one_sub_eq hGca
  have hr2 := recip_Gamma_one_sub_eq hG1a
  rw [show (1 : ℂ) - ((c - a : ℝ) : ℂ) = (a : ℂ) - c + 1 by push_cast; ring] at hr1
  rw [show (1 : ℂ) - ((1 - a : ℝ) : ℂ) = (a : ℂ) by push_cast; ring] at hr2
  have hΓ1 := Complex.Gamma_mul_Gamma_one_sub (c : ℂ)
  have hΓ2 := Complex.Gamma_mul_Gamma_one_sub ((c : ℂ) - 1)
  rw [show (1 : ℂ) - ((c : ℂ) - 1) = 2 - c by ring,
    show (π : ℂ) * ((c : ℂ) - 1) = π * c - π by ring, Complex.sin_sub_pi] at hΓ2
  have hsin : Complex.sin (π * c) = ((Real.sin (π * c) : ℝ) : ℂ) := by push_cast; rfl
  have hsin1 : Complex.sin (π * ((c - a : ℝ) : ℂ)) = ((Real.sin (π * (c - a)) : ℝ) : ℂ) := by
    push_cast; rfl
  have hsin2 : Complex.sin (π * ((1 - a : ℝ) : ℂ)) = ((Real.sin (π * a) : ℝ) : ℂ) := by
    rw [show (π : ℂ) * ((1 - a : ℝ) : ℂ) = π - π * a by push_cast; ring, Complex.sin_pi_sub]
    push_cast
    rfl
  rw [hsin1] at hr1
  rw [hsin2] at hr2
  rw [hsin] at hΓ1
  rw [hsin] at hΓ2
  have hGc : Complex.Gamma (c : ℂ) ≠ 0 := Complex.Gamma_ne_zero hcN
  have hG2c : Complex.Gamma (2 - (c : ℂ)) ≠ 0 := Complex.Gamma_ne_zero h2N
  have hΓ1' : Complex.Gamma (1 - (c : ℂ)) =
      π / (((Real.sin (π * c) : ℝ) : ℂ) * Complex.Gamma c) := by
    rw [eq_div_iff (mul_ne_zero hs' hGc)]
    have : Complex.Gamma c * Complex.Gamma (1 - c) * ((Real.sin (π * c) : ℝ) : ℂ) = π := by
      rw [hΓ1]; field_simp
    linear_combination this
  have hΓ2' : Complex.Gamma ((c : ℂ) - 1) =
      π / (-((Real.sin (π * c) : ℝ) : ℂ) * Complex.Gamma (2 - c)) := by
    rw [eq_div_iff (mul_ne_zero (neg_ne_zero.mpr hs') hG2c)]
    have : Complex.Gamma (c - 1) * Complex.Gamma (2 - c) * -((Real.sin (π * c) : ℝ) : ℂ) = π := by
      rw [hΓ2]; field_simp
    linear_combination this
  -- real power identities
  have hκx1 : x ^ ((c - 1) / 2) * κ ^ ((c - 1) / 2) = (κ * x) ^ ((c - 1) / 2) := by
    rw [Real.mul_rpow hκ.le hx.le]; ring
  have hκx2 : x ^ ((c - 1) / 2) * x ^ (1 - c) * κ ^ ((1 - c) / 2) =
      (κ * x) ^ ((1 - c) / 2) := by
    rw [← Real.rpow_add hx, Real.mul_rpow hκ.le hx.le, show (c - 1) / 2 + (1 - c) =
      (1 - c) / 2 by ring]
    ring
  have hκp1 : (κ ^ ((c - 1) / 2) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hκ _).ne'
  have hκp2 : (κ ^ ((1 - c) / 2) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hκ _).ne'
  rw [kummerU_eq_connection _ _ _ hcZ, kummerUConnection, kummerM_eq_mul_regularizedHGFun hcN,
    kummerM_eq_mul_regularizedHGFun h2N, div_eq_mul_inv (Complex.Gamma (1 - (c : ℂ))), hr1,
    div_eq_mul_inv (Complex.Gamma ((c : ℂ) - 1)), hr2, hΓ1', hΓ2',
    show (1 : ℂ) - (c : ℂ) = ((1 - c : ℝ) : ℂ) by push_cast; ring, ofReal_cpow_eq hx,
    show ((a - c + 1 : ℝ) : ℂ) = (a : ℂ) - c + 1 by push_cast; ring,
    show ((2 - c : ℝ) : ℂ) = 2 - (c : ℂ) by push_cast; ring,
    show (κ * x) ^ ((c - 1) / 2) = x ^ ((c - 1) / 2) * κ ^ ((c - 1) / 2) from hκx1.symm,
    show (κ * x) ^ ((1 - c) / 2) = x ^ ((c - 1) / 2) * x ^ (1 - c) * κ ^ ((1 - c) / 2)
      from hκx2.symm]
  have hκp1' : ((κ ^ ((c - 1) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκp1
  have hκp2' : ((κ ^ ((1 - c) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκp2
  simp only [ofReal_mul]
  generalize ((κ ^ ((c - 1) / 2) : ℝ) : ℂ) = P1 at hκp1' ⊢
  generalize ((κ ^ ((1 - c) / 2) : ℝ) : ℂ) = P2 at hκp2' ⊢
  generalize ((x ^ ((c - 1) / 2) : ℝ) : ℂ) = X1
  generalize ((x ^ (1 - c) : ℝ) : ℂ) = X2
  generalize Complex.Gamma (((κ + 1 / 2 : ℝ) : ℂ)) = G at hGκ ⊢
  field_simp
  ring

/-- For `x > 0`, `√(2x(c - 2a)) → +∞` as `a → -∞`. -/
theorem tendsto_sqrt_two_mul_atBot (c : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun a : ℝ => Real.sqrt (2 * x * (c - 2 * a))) atBot atTop := by
  have h1 : Tendsto (fun a : ℝ => 4 * x * -a + 2 * x * c) atBot atTop :=
    (tendsto_neg_atBot_atTop.const_mul_atTop (by positivity)).atTop_add tendsto_const_nhds
  exact Real.tendsto_sqrt_atTop.comp (h1.congr fun a => by ring)

/-- `J_μ(S) = O(S^{-1/2})` along `S = √(2x(c - 2a))`, `a → -∞`. -/
theorem besselJ_sqrt_two_mul_isBigO (μ c : ℝ) {x : ℝ} (hx : 0 < x) :
    (fun a : ℝ => besselJ (μ : ℂ) ((Real.sqrt (2 * x * (c - 2 * a)) : ℝ) : ℂ)) =O[atBot]
      (fun a : ℝ => Real.sqrt (2 * x * (c - 2 * a)) ^ (-(1 / 2 : ℝ))) := by
  have hS := tendsto_sqrt_two_mul_atBot c hx
  have h1 := (sqrt_mul_besselJ_isBigO μ).comp_tendsto hS
  have h0 : (fun a : ℝ => (((Real.sqrt (Real.sqrt (2 * x * (c - 2 * a))))⁻¹ : ℝ) : ℂ)) =O[atBot]
      (fun a : ℝ => Real.sqrt (2 * x * (c - 2 * a)) ^ (-(1 / 2 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with a
    rw [one_mul, Complex.norm_real, Real.sqrt_eq_rpow, ← Real.rpow_neg (Real.sqrt_nonneg _)]
  refine ((h0.mul h1).congr_right fun a => mul_one _).congr' ?_ EventuallyEq.rfl
  filter_upwards [hS.eventually (eventually_gt_atTop 0)] with a ha
  simp only [Function.comp_apply]
  have hs : ((Real.sqrt (Real.sqrt (2 * x * (c - 2 * a))) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ha).ne'
  push_cast
  field_simp

/-- `(c/2 - a)⁻¹ = O(|a|^{-1/2})` as `a → -∞`. -/
theorem recip_half_sub_isBigO (c : ℝ) :
    (fun a : ℝ => (c / 2 - a)⁻¹) =O[atBot] (fun a : ℝ => |a| ^ (-(1 / 2 : ℝ))) := by
  refine Asymptotics.IsBigO.trans ?_ (recip_sqrt_half_sub_isBigO c)
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [(tendsto_half_sub_atBot c).eventually (eventually_ge_atTop 1)] with a ha
  have hk : 0 < c / 2 - a := by linarith
  have hsk : 1 ≤ Real.sqrt (c / 2 - a) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt ha
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_inv, abs_of_pos hk,
    abs_of_pos (Real.sqrt_pos.mpr hk)]
  calc (c / 2 - a)⁻¹ = (Real.sqrt (c / 2 - a))⁻¹ * (Real.sqrt (c / 2 - a))⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt hk.le]
    _ ≤ (Real.sqrt (c / 2 - a))⁻¹ :=
        mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hsk)

/-- `Γ(c/2 - a + p)/(Γ(c/2 - a + 1/2) (c/2 - a)^{p - 1/2}) - 1 = O((c/2 - a)⁻¹)`. -/
theorem Gamma_half_ratio_isBigO (c p : ℝ) :
    (fun a : ℝ => Complex.Gamma (((c / 2 - a + p : ℝ) : ℂ)) /
        (Complex.Gamma (((c / 2 - a + 1 / 2 : ℝ) : ℂ)) *
          (((c / 2 - a) ^ (p - 1 / 2) : ℝ) : ℂ)) - 1) =O[atBot] (fun a : ℝ => (c / 2 - a)⁻¹) := by
  have h := (Gamma_ratio_sub_one_isBigO ((p : ℝ) : ℂ) ((1 / 2 : ℝ) : ℂ)).comp_tendsto
    (tendsto_half_sub_atBot c)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [(tendsto_half_sub_atBot c).eventually (eventually_gt_atTop 0)] with a ha
  simp only [Function.comp_apply]
  rw [show ((p : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) = ((p - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow ha.le, div_div]
  push_cast
  ring_nf

/-- **DLMF 13.8.10**: for real non-integer `c` and fixed `x > 0`, as `a → -∞`,
`U(a, c, x) = Γ(c/2 - a + 1/2) e^{x/2} x^{1/2 - c/2}
  (cos(aπ) J_{c-1}(S) - sin(aπ) Y_{c-1}(S) + env Y_{c-1}(S) O(|a|^{-1/2}))`
with `S = √(2x(c - 2a))`. Since `env Y_{c-1}(S) ≍ S^{-1/2}` as `S → ∞`, the error term is
written as `O(S^{-1/2} |a|^{-1/2})`. -/
@[dlmf 13.8.E10]
theorem kummerU_atBot_isBigO (c : ℝ) (hc : ∀ k : ℤ, c ≠ k) {x : ℝ} (hx : 0 < x) :
    (fun a : ℝ => ((x ^ ((c - 1) / 2) * Real.exp (-(x / 2)) : ℝ) : ℂ) /
          Complex.Gamma (((c / 2 - a + 1 / 2 : ℝ) : ℂ)) * kummerU (a : ℂ) (c : ℂ) (x : ℂ) -
        (((Real.cos (a * π) : ℝ) : ℂ) *
            besselJ ((c - 1 : ℝ) : ℂ) ((Real.sqrt (2 * x * (c - 2 * a)) : ℝ) : ℂ) -
          ((Real.sin (a * π) : ℝ) : ℂ) *
            DLMF.Bessel.besselY ((c - 1 : ℝ) : ℂ) ((Real.sqrt (2 * x * (c - 2 * a)) : ℝ) : ℂ)))
      =O[atBot] (fun a : ℝ => Real.sqrt (2 * x * (c - 2 * a)) ^ (-(1 / 2 : ℝ)) *
        |a| ^ (-(1 / 2 : ℝ))) := by
  set S : ℝ → ℝ := fun a => Real.sqrt (2 * x * (c - 2 * a)) with hSdef
  set r : ℝ → ℝ := fun a => S a ^ (-(1 / 2 : ℝ)) * |a| ^ (-(1 / 2 : ℝ)) with hrdef
  set J1 : ℝ → ℂ := fun a => besselJ ((c - 1 : ℝ) : ℂ) ((S a : ℝ) : ℂ)
  set J2 : ℝ → ℂ := fun a => besselJ ((1 - c : ℝ) : ℂ) ((S a : ℝ) : ℂ)
  set E1 : ℝ → ℂ := fun a => ((((c / 2 - a) * x) ^ ((c - 1) / 2) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
    regularizedHGFun {(a : ℂ)} {(c : ℂ)} (x : ℂ) - J1 a with hE1def
  set E2 : ℝ → ℂ := fun a => ((((c / 2 - a) * x) ^ ((1 - c) / 2) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
    regularizedHGFun {((a - c + 1 : ℝ) : ℂ)} {((2 - c : ℝ) : ℂ)} (x : ℂ) - J2 a with hE2def
  set H1 : ℝ → ℂ := fun a => Complex.Gamma (((c - a : ℝ) : ℂ)) /
    (Complex.Gamma (((c / 2 - a + 1 / 2 : ℝ) : ℂ)) * (((c / 2 - a) ^ ((c - 1) / 2) : ℝ) : ℂ))
    with hH1def
  set H2 : ℝ → ℂ := fun a => Complex.Gamma (((1 - a : ℝ) : ℂ)) /
    (Complex.Gamma (((c / 2 - a + 1 / 2 : ℝ) : ℂ)) * (((c / 2 - a) ^ ((1 - c) / 2) : ℝ) : ℂ))
    with hH2def
  set S1 : ℝ → ℂ := fun a => ((Real.sin (π * (c - a)) : ℝ) : ℂ)
  set S2 : ℝ → ℂ := fun a => ((Real.sin (π * a) : ℝ) : ℂ)
  -- the two Bessel forms
  have hE1 : E1 =O[atBot] r := regularizedConfluent_atBot_besselJ_isBigO c hx
  have hshift : Tendsto (fun a : ℝ => a - c + 1) atBot atBot :=
    (tendsto_atBot_add_const_right _ (1 - c) tendsto_id).congr fun a => by
      simp only [id]
      ring
  have hE2 : E2 =O[atBot] r := by
    have h := (regularizedConfluent_atBot_besselJ_isBigO (2 - c) hx).comp_tendsto hshift
    have hr : ((fun a : ℝ => Real.sqrt (2 * x * ((2 - c) - 2 * a)) ^ (-(1 / 2 : ℝ)) *
        |a| ^ (-(1 / 2 : ℝ))) ∘ fun a : ℝ => a - c + 1) =O[atBot] r := by
      refine Asymptotics.IsBigO.of_bound (Real.sqrt 2) ?_
      filter_upwards [eventually_le_atBot (-2 * |c| - 2)] with a ha
      have ha0 : a < 0 := by linarith [abs_nonneg c]
      have hapos : 0 < |a| := abs_pos.mpr ha0.ne
      have hb : |a| / 2 ≤ |a - c + 1| := by
        rw [abs_of_neg ha0]
        have h1 : -(a - c + 1) ≤ |a - c + 1| := neg_le_abs _
        have h2 := neg_abs_le c
        linarith
      simp only [Function.comp_apply, hrdef, hSdef]
      rw [show 2 * x * ((2 - c) - 2 * (a - c + 1)) = 2 * x * (c - 2 * a) by ring,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      have hk : |a - c + 1| ^ (-(1 / 2 : ℝ)) ≤ (|a| / 2) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hb (by norm_num)
      have h2 : (|a| / 2) ^ (-(1 / 2 : ℝ)) = Real.sqrt 2 * |a| ^ (-(1 / 2 : ℝ)) := by
        rw [Real.div_rpow hapos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.sqrt_eq_rpow, div_inv_eq_mul, mul_comm]
      have hS0 : 0 ≤ Real.sqrt (2 * x * (c - 2 * a)) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg (Real.sqrt_nonneg _) _
      calc Real.sqrt (2 * x * (c - 2 * a)) ^ (-(1 / 2 : ℝ)) * |a - c + 1| ^ (-(1 / 2 : ℝ))
          ≤ Real.sqrt (2 * x * (c - 2 * a)) ^ (-(1 / 2 : ℝ)) * (|a| / 2) ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hk hS0
        _ = Real.sqrt 2 * (Real.sqrt (2 * x * (c - 2 * a)) ^ (-(1 / 2 : ℝ)) *
            |a| ^ (-(1 / 2 : ℝ))) := by rw [h2]; ring
    refine (h.trans hr).congr' ?_ EventuallyEq.rfl
    filter_upwards with a
    simp only [Function.comp_apply, hE2def, J2]
    rw [show (2 - c) / 2 - (a - c + 1) = c / 2 - a by ring,
      show (2 - c - 1) / 2 = (1 - c) / 2 by ring,
      show 2 * x * ((2 - c) - 2 * (a - c + 1)) = 2 * x * (c - 2 * a) by ring,
      show ((2 - c - 1 : ℝ) : ℂ) = ((1 - c : ℝ) : ℂ) by push_cast; ring]
  -- the Gamma ratios
  have hinv1 : (fun a : ℝ => |a| ^ (-(1 / 2 : ℝ))) =O[atBot] (fun _ : ℝ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with a ha
    have h1 : 1 ≤ |a| := by rw [abs_of_neg (by linarith)]; linarith
    rw [one_mul, norm_one, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
  have hH1 : (fun a => H1 a - 1) =O[atBot] (fun a : ℝ => |a| ^ (-(1 / 2 : ℝ))) := by
    refine ((Gamma_half_ratio_isBigO c (c / 2)).trans (recip_half_sub_isBigO c)).congr' ?_
      EventuallyEq.rfl
    filter_upwards with a
    simp only [hH1def]
    rw [show c / 2 - a + c / 2 = c - a by ring, show c / 2 - 1 / 2 = (c - 1) / 2 by ring]
  have hH2 : (fun a => H2 a - 1) =O[atBot] (fun a : ℝ => |a| ^ (-(1 / 2 : ℝ))) := by
    refine ((Gamma_half_ratio_isBigO c (1 - c / 2)).trans (recip_half_sub_isBigO c)).congr' ?_
      EventuallyEq.rfl
    filter_upwards with a
    simp only [hH2def]
    rw [show c / 2 - a + (1 - c / 2) = 1 - a by ring,
      show 1 - c / 2 - 1 / 2 = (1 - c) / 2 by ring]
  have hH1b : H1 =O[atBot] (fun _ : ℝ => (1 : ℝ)) :=
    ((hH1.trans hinv1).add (isBigO_const_const (1 : ℂ) one_ne_zero atBot)).congr_left
      fun a => by ring
  have hH2b : H2 =O[atBot] (fun _ : ℝ => (1 : ℝ)) :=
    ((hH2.trans hinv1).add (isBigO_const_const (1 : ℂ) one_ne_zero atBot)).congr_left
      fun a => by ring
  have hS1 : S1 =O[atBot] (fun _ : ℝ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with a
    simp only [S1, Complex.norm_real, Real.norm_eq_abs, norm_one, one_mul]
    exact Real.abs_sin_le_one _
  have hS2 : S2 =O[atBot] (fun _ : ℝ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with a
    simp only [S2, Complex.norm_real, Real.norm_eq_abs, norm_one, one_mul]
    exact Real.abs_sin_le_one _
  have hJ1 : J1 =O[atBot] (fun a : ℝ => S a ^ (-(1 / 2 : ℝ))) :=
    besselJ_sqrt_two_mul_isBigO (c - 1) c hx
  have hJ2 : J2 =O[atBot] (fun a : ℝ => S a ^ (-(1 / 2 : ℝ))) :=
    besselJ_sqrt_two_mul_isBigO (1 - c) c hx
  have hreq : ∀ a, |a| ^ (-(1 / 2 : ℝ)) * 1 * S a ^ (-(1 / 2 : ℝ)) = r a := fun a => by
    simp only [hrdef]; ring
  have hreq' : ∀ a, 1 * 1 * r a = r a := fun a => by ring
  have t1 := ((hH1.mul hS1).mul hJ1).congr_right hreq
  have t2 := ((hH1b.mul hS1).mul hE1).congr_right hreq'
  have t3 := ((hH2.mul hS2).mul hJ2).congr_right hreq
  have t4 := ((hH2b.mul hS2).mul hE2).congr_right hreq'
  have hs : Real.sin (π * c) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
    exact hc k (by nlinarith [Real.pi_pos])
  have hs' : ((Real.sin (π * c) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hall := ((((t1.add t2).sub t3).sub t4).const_mul_left
    (((Real.sin (π * c) : ℝ) : ℂ))⁻¹)
  refine hall.congr' ?_ EventuallyEq.rfl
  filter_upwards [(tendsto_half_sub_atBot c).eventually (eventually_gt_atTop 0),
    eventually_lt_atBot (c : ℝ), eventually_lt_atBot (1 : ℝ),
    (tendsto_sqrt_two_mul_atBot c hx).eventually (eventually_gt_atTop 0)] with a ha hca h1a hSa
  have hU := kummerU_large_a_eq_half c hc hx ha (by linarith) (by linarith)
  -- `J_{1-c} = cos((c-1)π) J_{c-1} - sin((c-1)π) Y_{c-1}`
  have hJneg := DLMF.Bessel.besselJ_neg_eq ((c - 1 : ℝ) : ℂ)
    (z := ((S a : ℝ) : ℂ)) (Complex.ofReal_mem_slitPlane.mpr (by simpa [hSdef] using hSa))
  rw [show -((c - 1 : ℝ) : ℂ) = ((1 - c : ℝ) : ℂ) by push_cast; ring] at hJneg
  have hc1 : Complex.cos (((c - 1 : ℝ) : ℂ) * π) = -((Real.cos (π * c) : ℝ) : ℂ) := by
    rw [show ((c - 1 : ℝ) : ℂ) * π = ((π * c - π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      Real.cos_sub_pi]
    push_cast
    ring
  have hs1 : Complex.sin (((c - 1 : ℝ) : ℂ) * π) = -((Real.sin (π * c) : ℝ) : ℂ) := by
    rw [show ((c - 1 : ℝ) : ℂ) * π = ((π * c - π : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
      Real.sin_sub_pi]
    push_cast
    ring
  rw [hc1, hs1] at hJneg
  have hsca : Real.sin (π * (c - a)) = Real.sin (π * c) * Real.cos (π * a) -
      Real.cos (π * c) * Real.sin (π * a) := by
    rw [show π * (c - a) = π * c - π * a by ring, Real.sin_sub]
  have hscac := congrArg (fun t : ℝ => (t : ℂ)) hsca
  simp only [ofReal_sub, ofReal_mul] at hscac
  simp only [hE1def, hE2def, J1, J2, S1, S2, hH1def, hH2def] at hJneg ⊢
  rw [hU, show a * π = π * a by ring]
  simp only [hSdef] at hJneg ⊢
  set Jv := besselJ ((c - 1 : ℝ) : ℂ) ((Real.sqrt (2 * x * (c - 2 * a)) : ℝ) : ℂ)
  set Jm := besselJ ((1 - c : ℝ) : ℂ) ((Real.sqrt (2 * x * (c - 2 * a)) : ℝ) : ℂ)
  set Yv := DLMF.Bessel.besselY ((c - 1 : ℝ) : ℂ) ((Real.sqrt (2 * x * (c - 2 * a)) : ℝ) : ℂ)
  rw [hJneg, hscac]
  generalize Complex.Gamma (((c - a : ℝ) : ℂ)) /
    (Complex.Gamma (((c / 2 - a + 1 / 2 : ℝ) : ℂ)) * (((c / 2 - a) ^ ((c - 1) / 2) : ℝ) : ℂ)) = h1
  generalize Complex.Gamma (((1 - a : ℝ) : ℂ)) /
    (Complex.Gamma (((c / 2 - a + 1 / 2 : ℝ) : ℂ)) * (((c / 2 - a) ^ ((1 - c) / 2) : ℝ) : ℂ)) = h2
  generalize ((((c / 2 - a) * x) ^ ((c - 1) / 2) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
    regularizedHGFun {(a : ℂ)} {(c : ℂ)} (x : ℂ) = B1
  generalize ((((c / 2 - a) * x) ^ ((1 - c) / 2) * Real.exp (-(x / 2)) : ℝ) : ℂ) *
    regularizedHGFun {((a - c + 1 : ℝ) : ℂ)} {((2 - c : ℝ) : ℂ)} (x : ℂ) = B2
  field_simp
  ring

end DLMF.Confluent
