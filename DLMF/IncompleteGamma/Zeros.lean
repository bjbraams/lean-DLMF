/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.SeriesRecurrences

/-!
# Real and parameter zeros of the incomplete Gamma function, DLMF §8.13

Real zeros of `γ*(a,x)` in `x` and in `a`, including uniqueness between consecutive
parameter poles for negative `x`.
## Main definitions

* `Real.scIncGammaNegativeZero`, `Real.scIncGammaPositiveZero`: the negative and positive real
  zeros of `γ*(a,·)` when they exist.
* `scIncGammaDoubleZero`: the double parameter zero `(a_n*, x_n*)`.

## Main results

* `tricomiIncompleteGamma_nonnegative_parameter_no_real_zeros`: no real zeros for `a ≥ 0`.
* `tricomiIncompleteGamma_one_negative_zero`, `tricomiIncompleteGamma_two_real_zeros`: one or two
  real zeros, according to the range of `a` (DLMF §8.13(i)).
* `Real.scIncGammaNegativeZero_strictAnti`, `Real.scIncGammaNegativeZero_bounds`: monotonicity
  and the bounds DLMF 8.13.1.
* `tricomiIncompleteGamma_two_parameter_zeros_negative_x`,
  `tricomiIncompleteGamma_two_parameter_zeros_positive_x`,
  `tricomiIncompleteGamma_double_parameter_zero`,
  `tricomiIncompleteGamma_parameter_zeros_at_x_zero`,
  `tricomiIncompleteGamma_conjugate_zero_trajectories`: the parameter zeros of DLMF §8.13(ii).

## Implementation notes

At coalescence the two parameter zeros are counted with multiplicity. The partial-fraction
series is strictly decreasing on every interval between its parameter poles. Together with
opposite endpoint signs this proves the exact negative-argument parameter-zero count.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Statistical

/-- The negative x-zero when it exists. -/
def Real.scIncGammaNegativeZero (a : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x < 0 ∧ tricomiIncompleteGamma a x=0)

/-- The positive x-zero when it exists. -/
def Real.scIncGammaPositiveZero (a : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ tricomiIncompleteGamma a x=0)

/-- A complex sum of nonnegative real terms with positive leading term is nonzero. -/
theorem ne_zero_of_hasSum_ofReal_nonneg {f : ℕ → ℝ} {S : ℂ} (h : HasSum (fun k => (f k : ℂ)) S)
    (hf : ∀ k, 0 ≤ f k) (h0 : 0 < f 0) : S ≠ 0 := by
  have hr : HasSum f S.re := by
    have := (Complex.reCLM.hasSum h)
    simpa using this
  have hS : S = (S.re : ℂ) := by
    have hi := (Complex.imCLM.hasSum h)
    simp at hi
    apply Complex.ext <;> simp [hi.unique hasSum_zero]
  rw [hS]
  exact ofReal_ne_zero.mpr (lt_of_lt_of_le h0 (le_hasSum hr 0 fun j _ => hf j)).ne'

/-- Nonvanishing under the stated hypotheses: `tricomiIncompleteGamma a x ≠ 0`. -/
theorem tricomiIncompleteGamma_nonnegative_parameter_no_real_zeros {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    tricomiIncompleteGamma a x ≠ 0 := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have := tricomiIncompleteGamma_neg_nat 0 (x:ℂ)
    simp only [Nat.cast_zero, neg_zero, pow_zero] at this
    rw [ofReal_zero, this]; exact one_ne_zero
  have hG : ∀ k : ℕ, 0 < Real.Gamma (a+k+1) := fun k => Real.Gamma_pos_of_pos (by positivity)
  rcases le_or_gt 0 x with hx | hx
  · have h := tricomiIncompleteGamma_hasSum_exponential (a:ℂ) x
    refine ne_zero_of_hasSum_ofReal_nonneg (f := fun k => Real.exp (-x)*x^k/Real.Gamma (a+k+1))
      ?_ (fun k => by have := hG k; positivity) (by have := hG 0; simp; positivity)
    refine h.congr_fun fun k => ?_
    rw [show (a:ℂ)+k+1 = ((a+k+1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; rfl
  · have hs := (hasFPowerSeriesOnBall_regularizedConfluent (a:ℂ) (a+1)).hasSum_mul_pow
      (by simp : ((-x:ℝ):ℂ) ∈ Metric.eball (0:ℂ) ⊤)
    rw [ofReal_neg, regularizedConfluent_self_succ_neg] at hs
    refine ne_zero_of_hasSum_ofReal_nonneg
      (f := fun k => (ascPochhammer ℝ k).eval a/(k.factorial*Real.Gamma (a+1+k))*(-x)^k)
      ?_ (fun k => by
        have := ascPochhammer_pos k a hpos
        have : 0 < Real.Gamma (a+1+k) := Real.Gamma_pos_of_pos (by positivity)
        have : 0 ≤ -x := by linarith
        positivity) (by
        have : 0 < Real.Gamma (a+1+0) := Real.Gamma_pos_of_pos (by positivity)
        simp; positivity)
    refine hs.congr_fun fun k => ?_
    rw [regularizedHGFunCoeff_singleton, pochhammer_ofReal,
      show (a:ℂ)+1+k = ((a+1+k : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast
    ring

/-! ### Real zeros of `γ*(a, ·)` for negative `a`

`U(x) = e^x γ*(a,x)` satisfies `x U' = (x - a) U + 1/Γ(a)`, so `|x|^a e^{-x} U(x)` is strictly
monotone on each half-line. The signs at `0` and at `±∞` come from the two power series. -/

/-- `e^z γ*(a,z) = ∑ zᵏ / Γ(a+k+1)`. -/
theorem IncompleteGammaZeros.hasSum_expScaled (a z : ℂ) :
    HasSum (fun k : ℕ => z ^ k / Gamma (a + k + 1)) (regularizedHGFun {1} {a + 1} z) := by
  have h := (tricomiIncompleteGamma_hasSum_exponential a z).mul_left (exp z)
  have he : exp z * exp (-z) = 1 := by rw [← Complex.exp_add]; simp
  rw [tricomiIncompleteGamma, ← mul_assoc, he, one_mul] at h
  refine h.congr_fun fun k => ?_
  rw [← mul_div_assoc, ← mul_assoc, he, one_mul]

/-- The series with terms `(fun k : ℕ => (k + 1) * z ^ k / Gamma (a + k + 2))` converges to
`(regularizedHGFun {2} {a + 2} z)`. -/
theorem IncompleteGammaZeros.hasSum_expScaled' (a z : ℂ) :
    HasSum (fun k : ℕ => (k + 1) * z ^ k / Gamma (a + k + 2)) (regularizedHGFun {2} {a + 2} z) := by
  have hs := (hasFPowerSeriesOnBall_regularizedConfluent 2 (a + 2)).hasSum_mul_pow
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)
  refine hs.congr_fun fun k => ?_
  rw [regularizedHGFunCoeff_singleton]
  have hp : pochhammer (2 : ℂ) k = (k + 1 : ℕ)! := by
    have h1 := pochhammer_succ_left (1 : ℂ) k
    rw [one_mul, show (1 : ℂ) + 1 = 2 by norm_num] at h1
    rw [← h1, pochhammer_nat_one]
  rw [hp, Nat.factorial_succ]
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  push_cast
  rw [show a + 2 + k = a + k + 2 by ring]
  field_simp

/-- The first-order ODE `z U' = (z - a) U + 1/Γ(a)` of `U(z) = e^z γ*(a,z)`. -/
theorem IncompleteGammaZeros.ode {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    z * deriv (regularizedHGFun {1} {a + 1}) z =
      (z - a) * regularizedHGFun {1} {a + 1} z + (Gamma a)⁻¹ := by
  rw [deriv_regularizedConfluent, one_mul, show (1 : ℂ) + 1 = 2 by norm_num,
    show a + 1 + 1 = a + 2 by ring]
  have hU := IncompleteGammaZeros.hasSum_expScaled a z
  have hU2 := (IncompleteGammaZeros.hasSum_expScaled' a z).mul_left z
  have hzU := hU.mul_left z
  have haU := (hasSum_nat_add_iff' 1).mpr (hU.mul_left a)
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, add_zero, one_div] at haU
  have ha0 : a ≠ 0 := by simpa using ha 0
  have hG : (Gamma a)⁻¹ = a * (Gamma (a + 1))⁻¹ := by
    rw [Complex.Gamma_add_one a ha0, mul_inv, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
  have hR : HasSum (fun k : ℕ => z * (z ^ k / Gamma (a + k + 1)) -
      a * (z ^ (k + 1) / Gamma (a + ((k + 1 : ℕ) : ℂ) + 1)))
      ((z - a) * regularizedHGFun {1} {a + 1} z + (Gamma a)⁻¹) := by
    convert hzU.sub haU using 1
    rw [hG]; ring
  refine hU2.unique (hR.congr_fun fun k => ?_)
  have hk : a + k + 1 ≠ 0 := by
    intro h; exact ha (k + 1) (by push_cast; linear_combination h)
  have hk2 : Gamma (a + k + 2) = (a + k + 1) * Gamma (a + k + 1) := by
    rw [show a + k + 2 = (a + k + 1) + 1 by ring, Complex.Gamma_add_one _ hk]
  have hG0 : Gamma (a + k + 1) ≠ 0 := Complex.Gamma_ne_zero fun m h =>
    ha (m + k + 1) (by push_cast; linear_combination h)
  push_cast
  rw [show a + (k + 1) + 1 = a + k + 2 by ring, hk2]
  field_simp
  ring

/-- The real function `U(x) = e^x γ*(a,x)`. -/
noncomputable def IncompleteGammaZeros.expScaled (a x : ℝ) : ℝ :=
    (regularizedHGFun {1} {(a : ℂ) + 1} x).re

/-- Convergent series representation: `HasSum (fun k : ℕ => x ^ k / Real.Gamma (a + k + 1))
(IncompleteGammaZeros.expScaled a x) ∧ regularizedHGFun {1} {(a : ℂ) + 1} x =
(IncompleteGammaZeros.expScaled a x : ℂ)`. -/
theorem IncompleteGammaZeros.hasSum_real (a x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / Real.Gamma (a + k + 1)) (IncompleteGammaZeros.expScaled a x) ∧
      regularizedHGFun {1} {(a : ℂ) + 1} x = (IncompleteGammaZeros.expScaled a x : ℂ) := by
  have h := IncompleteGammaZeros.hasSum_expScaled (a : ℂ) (x : ℂ)
  have hr : HasSum (fun k : ℕ => ((x ^ k / Real.Gamma (a + k + 1) : ℝ) : ℂ))
      (regularizedHGFun {1} {(a : ℂ) + 1} x) := by
    refine h.congr_fun fun k => ?_
    rw [show (a : ℂ) + k + 1 = ((a + k + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  have hre : HasSum (fun k : ℕ => x ^ k / Real.Gamma (a + k + 1))
      (IncompleteGammaZeros.expScaled a x) := by
    have := Complex.hasSum_re hr
    simp only [ofReal_re] at this
    exact this
  refine ⟨hre, ?_⟩
  exact hr.unique (Complex.hasSum_ofReal.mpr hre)

/-- Identity under the stated parameter and domain assumptions:
`IncompleteGammaZeros.expScaled a 0 = (Real.Gamma (a + 1))⁻¹`. -/
theorem IncompleteGammaZeros.expScaled_zero (a : ℝ) : IncompleteGammaZeros.expScaled a 0 =
    (Real.Gamma (a + 1))⁻¹ := by
  have h := (IncompleteGammaZeros.hasSum_real a 0).1
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, add_zero, one_div] at h
  have h0 : HasSum (fun k : ℕ => (0 : ℝ) ^ (k + 1) / Real.Gamma (a + ↑(k + 1) + 1)) 0 := by
    simp
  linarith [h0.unique h]

/-- Identity under the stated parameter and domain assumptions:
`tricomiIncompleteGamma a x = exp (-(x : ℂ)) * (IncompleteGammaZeros.expScaled a x : ℂ)`. -/
theorem IncompleteGammaZeros.tricomiIncompleteGamma_eq_exp_mul (a x : ℝ) : tricomiIncompleteGamma a
    x = exp (-(x : ℂ)) *
    (IncompleteGammaZeros.expScaled a x : ℂ) := by
  rw [tricomiIncompleteGamma, (IncompleteGammaZeros.hasSum_real a x).2]

/-- Identity under the stated parameter and domain assumptions:
`tricomiIncompleteGamma a x = 0 ↔ IncompleteGammaZeros.expScaled a x = 0`. -/
theorem IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff (a x : ℝ) :
    tricomiIncompleteGamma a x = 0 ↔
    IncompleteGammaZeros.expScaled a x = 0 := by
  rw [IncompleteGammaZeros.tricomiIncompleteGamma_eq_exp_mul, mul_eq_zero, ofReal_eq_zero];
      simp [exp_ne_zero]

/-- Identity under the stated parameter and domain assumptions:
`∃ d : ℝ, HasDerivAt (IncompleteGammaZeros.expScaled a) d x ∧ x * d = (x - a) *
IncompleteGammaZeros.expScaled a x + (Real.Gamma a)⁻¹`. -/
theorem IncompleteGammaZeros.exists_hasDerivAt_expScaled {a : ℝ} (ha : ∀ n : ℕ, (a : ℂ) ≠ -n)
    (x : ℝ) :
    ∃ d : ℝ, HasDerivAt (IncompleteGammaZeros.expScaled a) d x ∧ x * d = (x - a) *
        IncompleteGammaZeros.expScaled a x + (Real.Gamma a)⁻¹ := by
  refine ⟨(deriv (regularizedHGFun {1} {(a : ℂ) + 1}) x).re,
    (differentiableAt_regularizedConfluent _ _ _).hasDerivAt.real_of_complex, ?_⟩
  have h := congrArg re (IncompleteGammaZeros.ode ha (x : ℂ))
  rw [(IncompleteGammaZeros.hasSum_real a x).2, show (x : ℂ) - a = ((x - a : ℝ) : ℂ) by
      push_cast; ring,
    Complex.Gamma_ofReal, ← ofReal_inv] at h
  simpa only [re_ofReal_mul, add_re, ofReal_re] using h

/-- The function `(IncompleteGammaZeros.expScaled a)` is continuous. -/
theorem IncompleteGammaZeros.continuous_expScaled {a : ℝ} (ha : ∀ n : ℕ, (a : ℂ) ≠ -n) : Continuous
    (IncompleteGammaZeros.expScaled a) :=
  continuous_iff_continuousAt.mpr fun x =>
      (IncompleteGammaZeros.exists_hasDerivAt_expScaled ha x).choose_spec.1.continuousAt

/-- The sign of `Γ` on `(-k-1, -k)`. -/
theorem IncompleteGammaZeros.Gamma_sign (k : ℕ) {x : ℝ} (h1 : -(k : ℝ) - 1 < x) (h2 : x < -k) :
    0 < (-1) ^ (k + 1) * Real.Gamma x := by
  induction k generalizing x with
  | zero =>
    have hx : x ≠ 0 := by simp at h2; linarith
    have h := Real.Gamma_add_one hx
    have hp : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by simp at h1; linarith)
    simp at h2
    rw [h] at hp
    have : Real.Gamma x < 0 := by
      by_contra hc; push Not at hc; nlinarith
    simp; linarith
  | succ k ih =>
    have hx : x ≠ 0 := by push_cast at h2; linarith
    have h := Real.Gamma_add_one hx
    have hp := ih (x := x + 1) (by push_cast at h1; linarith) (by push_cast at h2; linarith)
    rw [h] at hp
    rw [pow_succ]
    have hx0 : x < 0 := by push_cast at h2; linarith
    nlinarith

/-- A power series with eventually nonnegative coefficients and a positive one is eventually
positive at `+∞`. -/
theorem IncompleteGammaZeros.eventually_pos {c : ℕ → ℝ} {S : ℝ → ℝ} (m : ℕ)
    (hc : ∀ k, m ≤ k → 0 ≤ c k)
    (hm : 0 < c m) (hS : ∀ y, 0 ≤ y → HasSum (fun k => c k * y ^ k) (S y)) :
    ∀ᶠ y in atTop, 0 < S y := by
  set C := ∑ k ∈ Finset.range m, |c k|
  have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => abs_nonneg _
  filter_upwards [eventually_gt_atTop (max 1 (C / c m))] with y hy
  have hy1 : 1 < y := (le_max_left _ _).trans_lt hy
  have hyC : C / c m < y := (le_max_right _ _).trans_lt hy
  have hy0 : 0 < y := by linarith
  have h := hS y hy0.le
  have ht := (hasSum_nat_add_iff' m).mpr h
  have htail : c m * y ^ m ≤ S y - ∑ k ∈ Finset.range m, c k * y ^ k := by
    have := le_hasSum ht 0 fun j _ => mul_nonneg (hc _ (by omega)) (by positivity)
    simpa using this
  have hhead : |∑ k ∈ Finset.range m, c k * y ^ k| ≤ C * y ^ m / y := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_div_assoc, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [abs_mul, abs_of_pos (pow_pos hy0 k)]
    gcongr
    rw [le_div_iff₀ hy0]
    calc y ^ k * y = y ^ (k + 1) := (pow_succ _ _).symm
      _ ≤ y ^ m := pow_le_pow_right₀ hy1.le (Finset.mem_range.mp hk)
  have hym : 0 < y ^ m := pow_pos hy0 m
  have h1 : C * y ^ m / y < c m * y ^ m := by
    rw [div_lt_iff₀ hy0]
    have : C < c m * y := by rwa [div_lt_iff₀ hm, mul_comm] at hyC
    nlinarith
  have := neg_abs_le (∑ k ∈ Finset.range m, c k * y ^ k)
  linarith

/-- Nonvanishing under the stated hypotheses: `∀ n : ℕ, (a : ℂ) ≠ -n`. -/
theorem IncompleteGammaZeros.nonInteger {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) : ∀ n : ℕ, (a : ℂ) ≠ -n := by
  intro n h
  exact ha (-n) (by exact_mod_cast congrArg re h |>.trans (by simp))

/-- Estimate under the stated parameter and domain assumptions:
`∀ᶠ y in atTop, 0 < IncompleteGammaZeros.expScaled a y`. -/
theorem IncompleteGammaZeros.expScaled_atTop (a : ℝ) : ∀ᶠ y in atTop, 0 <
    IncompleteGammaZeros.expScaled a y := by
  refine IncompleteGammaZeros.eventually_pos (c := fun k => (Real.Gamma (a + k + 1))⁻¹) (⌈|a|⌉₊)
    (fun k hk => inv_nonneg.mpr (Real.Gamma_nonneg_of_nonneg ?_)) ?_ fun y _ =>
      (IncompleteGammaZeros.hasSum_real a y).1.congr_fun fun k => by ring
  · have := Nat.le_ceil |a|
    have : (⌈|a|⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    linarith [neg_abs_le a]
  · refine inv_pos.mpr (Real.Gamma_pos_of_pos ?_)
    have := Nat.le_ceil |a|
    linarith [neg_abs_le a]

/-- The series with terms `(fun k : ℕ => ((k ! : ℝ) * (a + k))⁻¹ * y ^ k)` converges to
`(Real.Gamma a * Real.exp y * IncompleteGammaZeros.expScaled a (-y))`. -/
theorem IncompleteGammaZeros.hasSum_alternating {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) (y : ℝ) :
    HasSum (fun k : ℕ => ((k ! : ℝ) * (a + k))⁻¹ * y ^ k)
      (Real.Gamma a * Real.exp y * IncompleteGammaZeros.expScaled a (-y)) := by
  have ha' := IncompleteGammaZeros.nonInteger ha
  have hG : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero fun m h => ha (-m) (by rw [h]; simp)
  have h := tricomiIncompleteGamma_hasSum_alternating ha' (((-y : ℝ)) : ℂ)
  rw [IncompleteGammaZeros.tricomiIncompleteGamma_eq_exp_mul] at h
  have hr : HasSum (fun k : ℕ => ((((k ! : ℝ) * (a + k))⁻¹ * y ^ k / Real.Gamma a : ℝ) : ℂ))
      (exp (-((-y : ℝ) : ℂ)) * (IncompleteGammaZeros.expScaled a (-y) : ℂ)) := by
    refine h.congr_fun fun k => ?_
    rw [Complex.Gamma_ofReal]
    push_cast; field_simp
  rw [← ofReal_neg, ← ofReal_exp, ← ofReal_mul] at hr
  have hr' := Complex.hasSum_ofReal.mp hr
  have := hr'.mul_left (Real.Gamma a)
  convert this using 1
  · funext k; field_simp
  · simp only [neg_neg]; ring

/-- Estimate under the stated parameter and domain assumptions: `∀ᶠ x in atBot, 0 < Real.Gamma a *
IncompleteGammaZeros.expScaled a x`. -/
theorem IncompleteGammaZeros.expScaled_atBot {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) :
    ∀ᶠ x in atBot, 0 < Real.Gamma a * IncompleteGammaZeros.expScaled a x := by
  have ha' := IncompleteGammaZeros.nonInteger ha
  have hG : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero fun m h => ha (-m) (by rw [h]; simp)
  set m := ⌈|a|⌉₊ + 1
  have hm : ∀ k, m ≤ k → 0 < a + k := by
    intro k hk
    have := Nat.le_ceil |a|
    have : ((⌈|a|⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at this
    linarith [neg_abs_le a]
  have hpos := IncompleteGammaZeros.eventually_pos (c := fun k => ((k ! : ℝ) * (a + k))⁻¹)
    (S := fun y => Real.Gamma a * Real.exp y * IncompleteGammaZeros.expScaled a (-y)) m
    (fun k hk => inv_nonneg.mpr (mul_nonneg (by positivity) (hm k hk).le))
    (inv_pos.mpr (mul_pos (by positivity) (hm m le_rfl))) fun y _ =>
        IncompleteGammaZeros.hasSum_alternating ha y
  filter_upwards [tendsto_neg_atBot_atTop.eventually hpos] with x hx
  simp only [neg_neg] at hx
  have he := Real.exp_pos (-x)
  by_contra hc
  push Not at hc
  nlinarith

/-- On each half-line `γ*(a, ·)` has at most one zero: `|x|^a e^{-x} U(x)` is strictly monotone. -/
theorem IncompleteGammaZeros.mono_pos {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) :
    StrictMonoOn (fun t : ℝ => Real.Gamma a *
        (t ^ a * Real.exp (-t) * IncompleteGammaZeros.expScaled a t)) (Ioi 0) := by
  have ha' := IncompleteGammaZeros.nonInteger ha
  have hG : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero fun m h => ha (-m) (by rw [h]; simp)
  set g := fun t : ℝ => Real.Gamma a * (t ^ a * Real.exp (-t) * IncompleteGammaZeros.expScaled a t)
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt g (t ^ (a - 1) * Real.exp (-t)) t := by
    intro t ht
    obtain ⟨d, hdU, hode⟩ := IncompleteGammaZeros.exists_hasDerivAt_expScaled ha' t
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := a) (Or.inl ht.ne')
    have h2 := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    have h := ((h1.mul h2).mul hdU).const_mul (Real.Gamma a)
    refine h.congr_deriv ?_
    have hr : t ^ a = t * t ^ (a - 1) := by
      have := ht.ne'
      rw [Real.rpow_sub_one ht.ne']; field_simp
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [hr]
    have : Real.Gamma a * (Real.Gamma a)⁻¹ = 1 := mul_inv_cancel₀ hG
    linear_combination (Real.Gamma a * t ^ (a - 1) * Real.exp (-t)) * hode -
      (-(t ^ (a - 1) * Real.exp (-t))) * this
  have hm : StrictMonoOn g (Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt) fun t ht => ?_
    rw [interior_Ioi] at ht
    rw [(hd t ht).deriv]
    exact mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  exact hm

/-- Identity under the stated parameter and domain assumptions: `StrictAntiOn (fun t : ℝ =>
Real.Gamma a * ((-t) ^ a * Real.exp (-t) * IncompleteGammaZeros.expScaled a t)) (Iio 0)`. -/
theorem IncompleteGammaZeros.mono_neg {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) :
    StrictAntiOn (fun t : ℝ => Real.Gamma a *
        ((-t) ^ a * Real.exp (-t) * IncompleteGammaZeros.expScaled a t)) (Iio 0) := by
  have ha' := IncompleteGammaZeros.nonInteger ha
  have hG : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero fun m h => ha (-m) (by rw [h]; simp)
  set g := fun t : ℝ => Real.Gamma a *
      ((-t) ^ a * Real.exp (-t) * IncompleteGammaZeros.expScaled a t)
  have hd : ∀ t : ℝ, t < 0 → HasDerivAt g (-((-t) ^ (a - 1) * Real.exp (-t))) t := by
    intro t ht
    obtain ⟨d, hdU, hode⟩ := IncompleteGammaZeros.exists_hasDerivAt_expScaled ha' t
    have h1 := (Real.hasDerivAt_rpow_const (x := -t) (p := a) (Or.inl (by linarith))).comp t
      (hasDerivAt_neg t)
    have h2 := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    have h := ((h1.mul h2).mul hdU).const_mul (Real.Gamma a)
    refine h.congr_deriv ?_
    have ht0 : -t ≠ 0 := (by linarith : (0:ℝ) < -t).ne'
    have ht1 : t ≠ 0 := ht.ne
    have hr : (-t) ^ a = (-t) * (-t) ^ (a - 1) := by
      rw [Real.rpow_sub_one ht0]; field_simp
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [hr]
    have : Real.Gamma a * (Real.Gamma a)⁻¹ = 1 := mul_inv_cancel₀ hG
    linear_combination (-(Real.Gamma a * (-t) ^ (a - 1) * Real.exp (-t))) * hode +
      (-((-t) ^ (a - 1) * Real.exp (-t))) * this
  have hm : StrictAntiOn g (Iio 0) := by
    refine strictAntiOn_of_deriv_neg (convex_Iio 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt) fun t ht => ?_
    rw [interior_Iio] at ht
    rw [(hd t ht).deriv, neg_lt_zero]
    exact mul_pos (Real.rpow_pos_of_pos (by simpa using ht) _) (Real.exp_pos _)
  exact hm

/-- Identity under the stated parameter and domain assumptions: `x = y`. -/
theorem IncompleteGammaZeros.unique_pos {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hUx : IncompleteGammaZeros.expScaled a x = 0)
        (hUy : IncompleteGammaZeros.expScaled a y = 0) : x = y :=
  (IncompleteGammaZeros.mono_pos ha).injOn hx hy (by simp only [hUx, hUy, mul_zero])

/-- Identity under the stated parameter and domain assumptions: `x = y`. -/
theorem IncompleteGammaZeros.unique_neg {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) {x y : ℝ}
    (hx : x < 0) (hy : y < 0)
    (hUx : IncompleteGammaZeros.expScaled a x = 0)
        (hUy : IncompleteGammaZeros.expScaled a y = 0) : x = y :=
  (IncompleteGammaZeros.mono_neg ha).injOn hx hy (by simp only [hUx, hUy, mul_zero])

/-- Nonvanishing under the stated hypotheses: `∀ n : ℤ, a ≠ n`. -/
theorem IncompleteGammaZeros.nonInteger_of_Ioo {a : ℝ} {m : ℤ} (h1 : (m : ℝ) < a) (h2 : a < m + 1) :
    ∀ n : ℤ, a ≠ n := by
  intro n hn
  rw [hn] at h1 h2
  have : m < n := by exact_mod_cast h1
  have : n < m + 1 := by exact_mod_cast h2
  omega

/-- The negative zero, when it exists and is unique, is the `ε`-chosen one. -/
theorem IncompleteGammaZeros.neg_exists {a : ℝ} (ha : ∀ n : ℤ, a ≠ n)
    (hs : 0 < Real.Gamma a * IncompleteGammaZeros.expScaled a 0 → False)
    (h0 : IncompleteGammaZeros.expScaled a 0 ≠ 0) :
    ∃ x, x < 0 ∧ IncompleteGammaZeros.expScaled a x = 0 := by
  have ha' := IncompleteGammaZeros.nonInteger ha
  obtain ⟨X, hX, hX0⟩ :=
      ((IncompleteGammaZeros.expScaled_atBot ha).and (eventually_lt_atBot 0)).exists
  have hc := (IncompleteGammaZeros.continuous_expScaled ha').continuousOn (s := Icc X 0)
  have hG : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero fun m h => ha (-m) (by rw [h]; simp)
  rcases lt_or_gt_of_ne hG with hGn | hGp
  · -- `U X < 0 < U 0`
    have hUX : IncompleteGammaZeros.expScaled a X < 0 := by nlinarith
    have hU0 : 0 < IncompleteGammaZeros.expScaled a 0 := by
      rcases lt_or_gt_of_ne h0 with h | h
      · exact absurd (mul_pos_of_neg_of_neg hGn h) hs
      · exact h
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo hX0.le hc ⟨hUX, hU0⟩
    exact ⟨x, hx.2, hx0⟩
  · have hUX : 0 < IncompleteGammaZeros.expScaled a X := by nlinarith
    have hU0 : IncompleteGammaZeros.expScaled a 0 < 0 := by
      rcases lt_or_gt_of_ne h0 with h | h
      · exact h
      · exact absurd (mul_pos hGp h) hs
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' hX0.le hc ⟨hU0, hUX⟩
    exact ⟨x, hx.2, hx0⟩

/-- The series with terms `(fun k : ℕ => y ^ k / (k ! : ℝ))` converges to `(Real.exp y)`. -/
theorem IncompleteGammaZeros.exp_series (y : ℝ) : HasSum (fun k : ℕ => y ^ k / (k ! : ℝ))
    (Real.exp y) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y

/-- Estimate under the stated parameter and domain assumptions: `Real.scIncGammaNegativeZero a < 0
∧ ∀ x : ℝ, tricomiIncompleteGamma a x=0 ↔ x=Real.scIncGammaNegativeZero a`. -/
theorem tricomiIncompleteGamma_one_negative_zero {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha0 : 1-2*(n : ℝ) < a)
    (ha1 : a < 2-2*(n : ℝ)) :
    Real.scIncGammaNegativeZero a < 0 ∧ ∀ x : ℝ, tricomiIncompleteGamma a x=0 ↔
        x=Real.scIncGammaNegativeZero a := by
  have ha : ∀ m : ℤ, a ≠ m :=
      IncompleteGammaZeros.nonInteger_of_Ioo (m := 1 - 2 * n) (by push_cast; linarith)
    (by push_cast; linarith)
  have hG : Real.Gamma a < 0 := by
    have h := IncompleteGammaZeros.Gamma_sign (2 * n - 2) (x := a)
        (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
      (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
    rw [show 2 * n - 2 + 1 = 2 * (n - 1) + 1 by omega, pow_succ, pow_mul] at h
    norm_num at h; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hneg : a < 0 := by linarith
  have hG1 : 0 < Real.Gamma (a + 1) := by
    rw [Real.Gamma_add_one hneg.ne]
    nlinarith
  have hU0 : 0 < IncompleteGammaZeros.expScaled a 0 := by rw [IncompleteGammaZeros.expScaled_zero];
                                                          exact inv_pos.mpr hG1
  obtain ⟨x0, hx0, hUx0⟩ := IncompleteGammaZeros.neg_exists ha (fun h => by nlinarith) hU0.ne'
  -- no zeros on `[0, ∞)`
  have hpos : ∀ x, 0 < x → IncompleteGammaZeros.expScaled a x ≠ 0 := by
    intro x hx hUx
    obtain ⟨Y, hY, hYx⟩ :=
        ((IncompleteGammaZeros.expScaled_atTop a).and (eventually_gt_atTop x)).exists
    have hm := IncompleteGammaZeros.mono_pos ha hx (hx.trans hYx) hYx
    simp only [hUx, mul_zero] at hm
    have : 0 < Y ^ a * Real.exp (-Y) * IncompleteGammaZeros.expScaled a Y :=
      mul_pos (mul_pos (Real.rpow_pos_of_pos (hx.trans hYx) _) (Real.exp_pos _)) hY
    nlinarith
  have hzero : ∀ x : ℝ, IncompleteGammaZeros.expScaled a x = 0 ↔ x = x0 := by
    intro x
    refine ⟨fun hx => ?_, fun hx => hx ▸ hUx0⟩
    rcases lt_trichotomy x 0 with h | h | h
    · exact IncompleteGammaZeros.unique_neg ha h hx0 hx hUx0
    · rw [h] at hx; exact absurd hx hU0.ne'
    · exact absurd hx (hpos x h)
  have he : Real.scIncGammaNegativeZero a = x0 := by
    have hs := Classical.epsilon_spec (p := fun x : ℝ => x < 0 ∧ tricomiIncompleteGamma a x = 0)
      ⟨x0, hx0, (IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff a x0).mpr hUx0⟩
    exact (hzero _).mp ((IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff a _).mp hs.2)
  rw [he]
  exact ⟨hx0, fun x =>
      (IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff a x).trans (hzero x)⟩

/-- Estimate under the stated parameter and domain assumptions: `Real.scIncGammaNegativeZero a < 0
∧ 0 < Real.scIncGammaPositiveZero a ∧ ∀ x : ℝ, tricomiIncompleteGamma a x=0 ↔
x=Real.scIncGammaNegativeZero a ∨ x=Real.scIncGammaPositiveZero a`. -/
theorem tricomiIncompleteGamma_two_real_zeros {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : -2*(n : ℝ) < a)
    (ha1 : a < 1-2*(n : ℝ)) :
    Real.scIncGammaNegativeZero a < 0 ∧ 0 < Real.scIncGammaPositiveZero a ∧ ∀ x : ℝ,
        tricomiIncompleteGamma a x=0 ↔ x=Real.scIncGammaNegativeZero a ∨
            x=Real.scIncGammaPositiveZero a := by
  have ha : ∀ m : ℤ, a ≠ m :=
      IncompleteGammaZeros.nonInteger_of_Ioo (m := -2 * n) (by push_cast; linarith)
    (by push_cast; linarith)
  have hG : 0 < Real.Gamma a := by
    have h := IncompleteGammaZeros.Gamma_sign (2 * n - 1) (x := a)
        (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
      (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
    rw [show 2 * n - 1 + 1 = 2 * n by omega, pow_mul] at h
    norm_num at h; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hneg : a < 0 := by linarith
  have hG1 : Real.Gamma (a + 1) < 0 := by
    rw [Real.Gamma_add_one hneg.ne]; nlinarith
  have hU0 : IncompleteGammaZeros.expScaled a 0 < 0 := by rw [IncompleteGammaZeros.expScaled_zero];
                                                          exact inv_lt_zero.mpr hG1
  obtain ⟨x0, hx0, hUx0⟩ := IncompleteGammaZeros.neg_exists ha (fun h => by nlinarith) hU0.ne
  -- the positive zero
  have hc : Continuous (IncompleteGammaZeros.expScaled a) :=
      IncompleteGammaZeros.continuous_expScaled (IncompleteGammaZeros.nonInteger ha)
  obtain ⟨Y, hY, hY0⟩ :=
      ((IncompleteGammaZeros.expScaled_atTop a).and (eventually_gt_atTop 0)).exists
  obtain ⟨y0, hy0, hUy0⟩ := intermediate_value_Ioo hY0.le hc.continuousOn ⟨hU0, hY⟩
  have hzero : ∀ x : ℝ, IncompleteGammaZeros.expScaled a x = 0 ↔ x = x0 ∨ x = y0 := by
    intro x
    refine ⟨fun hx => ?_, fun hx => hx.elim (fun h => h ▸ hUx0) (fun h => h ▸ hUy0)⟩
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inl (IncompleteGammaZeros.unique_neg ha h hx0 hx hUx0)
    · rw [h] at hx; exact absurd hx hU0.ne
    · exact Or.inr (IncompleteGammaZeros.unique_pos ha h hy0.1 hx hUy0)
  have he1 : Real.scIncGammaNegativeZero a = x0 := by
    have hs := Classical.epsilon_spec (p := fun x : ℝ => x < 0 ∧ tricomiIncompleteGamma a x = 0)
      ⟨x0, hx0, (IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff a x0).mpr hUx0⟩
    rcases (hzero _).mp ((IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff a _).mp
        hs.2) with h | h
    · exact h
    · exact absurd hs.1 (not_lt.mpr (h ▸ hy0.1.le))
  have he2 : Real.scIncGammaPositiveZero a = y0 := by
    have hs := Classical.epsilon_spec (p := fun x : ℝ => 0 < x ∧ tricomiIncompleteGamma a x = 0)
      ⟨y0, hy0.1, (IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff a y0).mpr hUy0⟩
    rcases (hzero _).mp ((IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff a _).mp
        hs.2) with h | h
    · exact absurd hs.1 (not_lt.mpr (h ▸ hx0.le))
    · exact h
  rw [he1, he2]
  exact ⟨hx0, hy0.1, fun x =>
      (IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff a x).trans (hzero x)⟩

/-- The stated relation follows from the given hypotheses: `StrictAntiOn
Real.scIncGammaNegativeZero (Ioo (-1) 0)`. -/
theorem Real.scIncGammaNegativeZero_strictAnti  :
    StrictAntiOn Real.scIncGammaNegativeZero (Ioo (-1) 0) := by
  intro a1 ha1 a2 ha2 h12
  have hn : ∀ a ∈ Ioo (-1 : ℝ) 0, (∀ m : ℤ, a ≠ m) := fun a ha =>
    IncompleteGammaZeros.nonInteger_of_Ioo (m := -1) (by push_cast; linarith [ha.1])
        (by push_cast; linarith [ha.2])
  have hz : ∀ a ∈ Ioo (-1 : ℝ) 0, Real.scIncGammaNegativeZero a < 0 ∧
      IncompleteGammaZeros.expScaled a (Real.scIncGammaNegativeZero a) = 0 := by
    intro a ha
    obtain ⟨hneg, hiff⟩ := tricomiIncompleteGamma_one_negative_zero (n := 1) le_rfl (a := a)
      (by norm_num; linarith [ha.1]) (by norm_num; linarith [ha.2])
    exact ⟨hneg, (IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff a _).mp
        ((hiff _).mpr rfl)⟩
  have hG : ∀ a ∈ Ioo (-1 : ℝ) 0, Real.Gamma a < 0 := by
    intro a ha
    have h := IncompleteGammaZeros.Gamma_sign 0 (x := a) (by norm_num; linarith [ha.1])
        (by norm_num; linarith [ha.2])
    norm_num at h; linarith
  obtain ⟨hx1, hU1⟩ := hz a1 ha1
  obtain ⟨hx2, hU2⟩ := hz a2 ha2
  set x1 := Real.scIncGammaNegativeZero a1
  set x2 := Real.scIncGammaNegativeZero a2
  set y := -x1
  have hy : 0 < y := by simp only [y]; linarith
  have hS1 := IncompleteGammaZeros.hasSum_alternating (hn a1 ha1) y
  have hS2 := IncompleteGammaZeros.hasSum_alternating (hn a2 ha2) y
  simp only [y, neg_neg, hU1, mul_zero] at hS1
  have hlt := hasSum_lt (i := 0) (fun k => ?_) ?_ hS2 hS1
  · -- `U_{a₂}(x₁) > 0`
    simp only [y, neg_neg] at hlt
    have hU : 0 < IncompleteGammaZeros.expScaled a2 x1 := by
      have := Real.exp_pos (-x1)
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.mpr (hG a2 ha2).le) this.le)
          (neg_nonneg.mpr hc)]
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt' | heq
    · have := IncompleteGammaZeros.mono_neg (hn a2 ha2) hx1 hx2 hlt'
      simp only [hU2, mul_zero] at this
      have hp : 0 < (-x1) ^ a2 * Real.exp (-x1) :=
        mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.exp_pos _)
      nlinarith [mul_pos (mul_pos (neg_pos.mpr (hG a2 ha2)) hp) hU]
    · rw [heq, hU2] at hU; exact lt_irrefl _ hU
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [Nat.factorial_zero, Nat.cast_one, CharP.cast_eq_zero, add_zero, one_mul, pow_zero,
        mul_one]
      exact (inv_lt_inv_of_neg ha2.2 ha1.2).mpr h12 |>.le
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have h1 : 0 < a1 + k := by linarith [ha1.1]
      have hinv : ((k ! : ℝ) * (a2 + k))⁻¹ ≤ ((k ! : ℝ) * (a1 + k))⁻¹ :=
        inv_anti₀ (by positivity) (by gcongr)
      exact mul_le_mul_of_nonneg_right hinv (by positivity)
  · simp only [Nat.factorial_zero, Nat.cast_one, CharP.cast_eq_zero, add_zero, one_mul, pow_zero,
      mul_one]
    exact (inv_lt_inv_of_neg ha2.2 ha1.2).mpr h12

/-- Estimate under the stated parameter and domain assumptions: `1+1/a <
Real.scIncGammaNegativeZero a ∧ Real.scIncGammaNegativeZero a < Real.log |a|`. -/
@[dlmf 8.13.E1]
theorem Real.scIncGammaNegativeZero_bounds {a : ℝ} (ha0 : -1 < a) (ha1 : a < 0) :
    1+1/a < Real.scIncGammaNegativeZero a ∧ Real.scIncGammaNegativeZero a < Real.log |a| := by
  have ha : ∀ m : ℤ, a ≠ m :=
      IncompleteGammaZeros.nonInteger_of_Ioo (m := -1) (by push_cast; linarith)
    (by push_cast; linarith)
  obtain ⟨hneg, hiff⟩ := tricomiIncompleteGamma_one_negative_zero (n := 1) le_rfl (a := a)
    (by norm_num; linarith) (by norm_num; linarith)
  set x0 := Real.scIncGammaNegativeZero a
  have hUx0 : IncompleteGammaZeros.expScaled a x0 = 0 :=
      (IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff a x0).mp ((hiff x0).mpr rfl)
  have hG : Real.Gamma a < 0 := by
    have h := IncompleteGammaZeros.Gamma_sign 0 (x := a) (by norm_num; linarith)
        (by norm_num; linarith)
    norm_num at h; linarith
  have hm := IncompleteGammaZeros.mono_neg ha
  have hS := IncompleteGammaZeros.hasSum_alternating ha
  have hpa : 0 < -a := by linarith
  have h1a : 0 < 1 + a := by linarith
  have ha0' : a ≠ 0 := ha1.ne
  have h1a' : 1 + a ≠ 0 := h1a.ne'
  constructor
  · -- `U(1 + 1/a) < 0`
    set y := (1 + a) / (-a)
    have hy : 0 < y := div_pos h1a hpa
    have hpt : -y = 1 + 1 / a := by simp only [y]; field_simp; ring
    have ht := (hasSum_nat_add_iff' 2).mpr (hS y)
    have htpos : 0 < Real.Gamma a * Real.exp y * IncompleteGammaZeros.expScaled a (-y) -
        ∑ k ∈ Finset.range 2, ((k ! : ℝ) * (a + k))⁻¹ * y ^ k := by
      refine lt_of_lt_of_le ?_ (le_hasSum ht 0 fun k _ => ?_)
      · have : 0 < a + ((0 + 2 : ℕ) : ℝ) := by push_cast; linarith
        positivity
      · have : 0 < a + ((k + 2 : ℕ) : ℝ) := by push_cast; linarith
        positivity
    have h01 : ∑ k ∈ Finset.range 2, ((k ! : ℝ) * (a + k))⁻¹ * y ^ k = 0 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial,
        Nat.cast_one, Nat.cast_zero, add_zero, pow_zero, pow_one, one_mul, mul_one, zero_add]
      simp only [y]
      have : a + 1 ≠ 0 := by linarith
      field_simp
      ring_nf
    rw [h01, sub_zero] at htpos
    have hU : IncompleteGammaZeros.expScaled a (1 + 1 / a) < 0 := by
      rw [← hpt]
      have := Real.exp_pos y
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.mpr hG.le) this.le) hc]
    have hlt : 1 + 1 / a < 0 := by rw [← hpt]; linarith
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt' | heq
    · have := hm hneg hlt hlt'
      simp only [hUx0, mul_zero] at this
      have hp : 0 < (-(1 + 1 / a)) ^ a * Real.exp (-(1 + 1 / a)) :=
        mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.exp_pos _)
      nlinarith [mul_pos (mul_pos (neg_pos.mpr hG) hp) (neg_pos.mpr hU)]
    · rw [← heq, hUx0] at hU; exact lt_irrefl _ hU
  · -- `U(log|a|) > 0`
    set L := -Real.log (-a)
    have hL : 0 < L := by
      simp only [L, neg_pos]; exact Real.log_neg hpa (by linarith)
    have heL : Real.exp L = -1 / a := by
      simp only [L]; rw [Real.exp_neg, Real.exp_log hpa]; field_simp
    have hpt : -L = Real.log |a| := by simp only [L, neg_neg, abs_of_neg ha1]
    -- comparison series
    have hb : HasSum (fun k : ℕ => (1 + a)⁻¹ * (L ^ k / (k ! : ℝ)) +
        if k = 0 then a⁻¹ - (1 + a)⁻¹ else 0) 0 := by
      have := ((IncompleteGammaZeros.exp_series L).mul_left (1 + a)⁻¹).add
          (hasSum_ite_eq 0 (a⁻¹ - (1 + a)⁻¹))
      convert this using 1
      rw [heL]; field_simp; ring
    have hlt := hasSum_lt (f := fun k : ℕ => ((k ! : ℝ) * (a + k))⁻¹ * L ^ k) (i := 2)
      (fun k => ?_) ?_ (hS L) hb
    · have hU : 0 < IncompleteGammaZeros.expScaled a (Real.log |a|) := by
        rw [← hpt]
        have := Real.exp_pos L
        by_contra hc; push Not at hc
        nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.mpr hG.le) this.le) (neg_nonneg.mpr hc)]
      have hlog : Real.log |a| < 0 := by rw [← hpt]; linarith
      by_contra hle
      push Not at hle
      rcases hle.lt_or_eq with hlt' | heq
      · have := hm hlog hneg hlt'
        simp only [hUx0, mul_zero] at this
        have hp : 0 < (-Real.log |a|) ^ a * Real.exp (-Real.log |a|) :=
          mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.exp_pos _)
        nlinarith [mul_pos (mul_pos (neg_pos.mpr hG) hp) hU]
      · rw [heq, hUx0] at hU; exact lt_irrefl _ hU
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · simp only [Nat.pos_iff_ne_zero.mp hk, ite_false, add_zero]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have h1 : 0 < a + k := by linarith
        have hinv : (a + k)⁻¹ ≤ (1 + a)⁻¹ := inv_anti₀ h1a (by linarith)
        have hnn : 0 ≤ L ^ k / (k ! : ℝ) := by positivity
        calc ((k ! : ℝ) * (a + k))⁻¹ * L ^ k = (a + k)⁻¹ * (L ^ k / (k ! : ℝ)) := by
              rw [mul_inv]; ring
          _ ≤ (1 + a)⁻¹ * (L ^ k / (k ! : ℝ)) := mul_le_mul_of_nonneg_right hinv hnn
    · simp only [OfNat.ofNat_ne_zero, ite_false, add_zero]
      rw [mul_inv, mul_comm ((2 : ℕ) ! : ℝ)⁻¹, mul_assoc, ← div_eq_inv_mul (L ^ 2)]
      have : 0 < L ^ 2 / ((2 : ℕ) ! : ℝ) := by positivity
      have h2 : (a + ((2 : ℕ) : ℝ))⁻¹ < (1 + a)⁻¹ := by
        rw [inv_lt_inv₀ (by push_cast; linarith) h1a]; push_cast; linarith
      exact mul_lt_mul_of_pos_right h2 this

/-- On each interval between consecutive nonpositive integers there is at most one
parameter zero of `γ*(a,x)` when `x < 0`. The partial-fraction series is strictly decreasing
between its poles. -/
theorem IncompleteGammaZeros.unique_parameter_zero_negative_x (m : ℕ) {x a b : ℝ}
    (hx : x < 0) (ha : -(m : ℝ)-1 < a ∧ a < -m)
    (hb : -(m : ℝ)-1 < b ∧ b < -m)
    (hza : tricomiIncompleteGamma a x = 0)
    (hzb : tricomiIncompleteGamma b x = 0) : a = b := by
  have hn (c : ℝ) (hc : -(m : ℝ)-1 < c ∧ c < -m) : ∀ j : ℤ, c ≠ j :=
    IncompleteGammaZeros.nonInteger_of_Ioo (m := -(m : ℤ)-1)
      (by push_cast; linarith [hc.1]) (by push_cast; linarith [hc.2])
  have hz (c : ℝ) (hc : tricomiIncompleteGamma c x = 0) :
      IncompleteGammaZeros.expScaled c x = 0 :=
    (IncompleteGammaZeros.tricomiIncompleteGamma_eq_zero_iff c x).mp hc
  have hnot (c d : ℝ) (hc : -(m : ℝ)-1 < c ∧ c < -m)
      (hd : -(m : ℝ)-1 < d ∧ d < -m) (hcd : c < d)
      (hzc : IncompleteGammaZeros.expScaled c x = 0)
      (hzd : IncompleteGammaZeros.expScaled d x = 0) : False := by
    have hS := IncompleteGammaZeros.hasSum_alternating (hn c hc) (-x)
    have hT := IncompleteGammaZeros.hasSum_alternating (hn d hd) (-x)
    simp only [neg_neg, hzc, hzd, mul_zero] at hS hT
    have hlt := hasSum_lt (i := 0) (fun k => ?_) ?_ hT hS
    · exact lt_irrefl _ hlt
    · apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) k)
      have hk : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
      by_cases hkm : k ≤ m
      · have hkm' : (k:ℝ) ≤ m := by exact_mod_cast hkm
        have hc0 : k.factorial * (c+k) < 0 :=
          mul_neg_of_pos_of_neg hk (by linarith [hc.2])
        have hd0 : k.factorial * (d+k) < 0 :=
          mul_neg_of_pos_of_neg hk (by linarith [hd.2])
        exact ((inv_lt_inv_of_neg hd0 hc0).mpr (by nlinarith)).le
      · have hmk : (m:ℝ)+1 ≤ k := by exact_mod_cast (by omega : m+1 ≤ k)
        have hc0 : 0 < k.factorial * (c+k) := mul_pos hk (by linarith [hc.1])
        have hd0 : 0 < k.factorial * (d+k) := mul_pos hk (by linarith [hd.1])
        exact (inv_lt_inv₀ hd0 hc0).mpr (by nlinarith) |>.le
    · simp only [Nat.factorial_zero, Nat.cast_one, CharP.cast_eq_zero, add_zero,
        one_mul, pow_zero, mul_one]
      have hc0 : c < 0 := by have := Nat.cast_nonneg (α := ℝ) m; linarith [hc.2]
      have hd0 : d < 0 := by have := Nat.cast_nonneg (α := ℝ) m; linarith [hd.2]
      exact (inv_lt_inv_of_neg hd0 hc0).mpr hcd
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (hnot a b ha hb hab (hz a hza) (hz b hzb)).elim
  · exact hab
  · exact (hnot b a hb ha hab (hz b hzb) (hz a hza)).elim

/-- For `x < 0`, each interval `(-m-1,-m)` contains a unique parameter zero of `γ*(a,x)`.
The values at its endpoints are `x^(m+1)` and `x^m`, which have opposite signs. -/
theorem IncompleteGammaZeros.existsUnique_parameter_zero_negative_x (m : ℕ) {x : ℝ}
    (hx : x < 0) : ∃! a : ℝ, -(m : ℝ)-1 < a ∧ a < -m ∧
      tricomiIncompleteGamma a x = 0 := by
  let f : ℝ → ℝ := fun a => (tricomiIncompleteGamma a x).re
  have hf : Continuous f := continuous_re.comp
    ((continuous_tricomiIncompleteGamma_param x).comp continuous_ofReal)
  have hreal (a : ℝ) : tricomiIncompleteGamma a x = (f a : ℂ) := by
    rw [IncompleteGammaZeros.tricomiIncompleteGamma_eq_exp_mul,
      ← ofReal_neg, ← ofReal_exp, ← ofReal_mul]
    simp only [f, IncompleteGammaZeros.tricomiIncompleteGamma_eq_exp_mul,
      ← ofReal_neg, ← ofReal_exp, ← ofReal_mul, ofReal_re]
  have hval (k : ℕ) : f (-k) = x^k := by
    simp only [f, ofReal_neg, ofReal_natCast, tricomiIncompleteGamma_neg_nat,
      ← ofReal_pow, ofReal_re]
  have hleft : f (-(m:ℝ)-1) = x^(m+1) := by
    rw [show -(m:ℝ)-1 = -((m+1:ℕ):ℝ) by push_cast; ring, hval]
  have hright : f (-(m:ℝ)) = x^m := hval m
  have hprod : f (-(m:ℝ)-1) * f (-(m:ℝ)) < 0 := by
    rw [hleft, hright, pow_succ]
    have hp : 0 < (x^m)^2 := sq_pos_of_ne_zero (pow_ne_zero m hx.ne)
    nlinarith
  have he : ∃ a ∈ Ioo (-(m:ℝ)-1) (-m), f a = 0 := by
    rcases lt_or_ge (f (-(m:ℝ)-1)) 0 with hl | hl
    · have hr : 0 < f (-(m:ℝ)) := by nlinarith
      exact intermediate_value_Ioo (by linarith) hf.continuousOn ⟨hl, hr⟩
    · have hl' : 0 < f (-(m:ℝ)-1) := by
        apply lt_of_le_of_ne hl
        intro heq
        rw [← heq, zero_mul] at hprod
        exact lt_irrefl _ hprod
      have hr : f (-(m:ℝ)) < 0 := by nlinarith
      exact intermediate_value_Ioo' (by linarith) hf.continuousOn ⟨hr, hl'⟩
  obtain ⟨a, ha, hfa⟩ := he
  have hza : tricomiIncompleteGamma a x = 0 := by rw [hreal a, hfa, ofReal_zero]
  refine ⟨a, ⟨ha.1, ha.2, hza⟩, fun b hb => ?_⟩
  exact IncompleteGammaZeros.unique_parameter_zero_negative_x m hx ⟨hb.1, hb.2.1⟩ ha hb.2.2 hza

/-- The double parameter-zero pair (a_n*,x_n*). -/
def scIncGammaDoubleZero (n : ℕ) : ℝ × ℝ :=
  Classical.epsilon (fun p : ℝ × ℝ => -2*(n : ℝ) < p.1 ∧ p.1 < 1-2*(n : ℝ) ∧ 0 < p.2 ∧
      tricomiIncompleteGamma p.1 p.2=0 ∧ deriv (fun a : ℂ => tricomiIncompleteGamma a p.2) p.1=0)

/-- Estimate under the stated parameter and domain assumptions: `({a : ℝ | -2*(n : ℝ) < a ∧ a <
2-2*(n : ℝ) ∧ tricomiIncompleteGamma a x=0} : Set ℝ).ncard=2`. -/
theorem tricomiIncompleteGamma_two_parameter_zeros_negative_x {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : x < 0) :
    ({a : ℝ | -2*(n : ℝ) < a ∧ a < 2-2*(n : ℝ) ∧ tricomiIncompleteGamma a x=0} : Set
        ℝ).ncard=2 := by
  obtain ⟨a, ha, hua⟩ :=
    IncompleteGammaZeros.existsUnique_parameter_zero_negative_x (2*n-1) hx
  obtain ⟨b, hb, hub⟩ :=
    IncompleteGammaZeros.existsUnique_parameter_zero_negative_x (2*n-2) hx
  have hn1 : 1 ≤ 2*n := by omega
  have hn2 : 2 ≤ 2*n := by omega
  rw [Nat.cast_sub hn1] at ha hua
  rw [Nat.cast_sub hn2] at hb hub
  push_cast at ha hb hua hub
  have hab : a ≠ b := by linarith [ha.2.1, hb.1]
  have hs : {c : ℝ | -2*(n:ℝ) < c ∧ c < 2-2*(n:ℝ) ∧
      tricomiIncompleteGamma c x = 0} = {a,b} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hc0, hc1, hcz⟩
      rcases lt_trichotomy c (1-2*(n:ℝ)) with hc | hc | hc
      · exact Or.inl (hua c ⟨by linarith, by linarith, hcz⟩)
      · have he : (c:ℂ) = -((2*n-1:ℕ):ℂ) := by
          rw [hc, Nat.cast_sub hn1]; push_cast; ring
        rw [he, tricomiIncompleteGamma_neg_nat] at hcz
        exact (pow_ne_zero _ (ofReal_ne_zero.mpr hx.ne) hcz).elim
      · exact Or.inr (hub c ⟨by linarith, by linarith, hcz⟩)
    · rintro (rfl | rfl)
      · exact ⟨by linarith [ha.1], by linarith [ha.2.1], ha.2.2⟩
      · exact ⟨by linarith [hb.1], by linarith [hb.2.1], hb.2.2⟩
  rw [hs]
  exact Set.ncard_pair hab

/-- Estimate under the stated parameter and domain assumptions: `({a : ℝ | -2*(n : ℝ) < a ∧ a <
1-2*(n : ℝ) ∧ tricomiIncompleteGamma a x=0} : Set ℝ).ncard=2`. -/
theorem tricomiIncompleteGamma_two_parameter_zeros_positive_x {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < (scIncGammaDoubleZero n).2) :
    ({a : ℝ | -2*(n : ℝ) < a ∧ a < 1-2*(n : ℝ) ∧ tricomiIncompleteGamma a x=0} : Set
        ℝ).ncard=2 := by
  sorry

/-- At coalescence the two zeros are counted with multiplicity, not as distinct points. -/
theorem tricomiIncompleteGamma_double_parameter_zero {n : ℕ} (hn : 1 ≤ n) :
    let p := scIncGammaDoubleZero n; -2*(n : ℝ) < p.1 ∧ p.1 < 1-2*(n : ℝ) ∧ 0 < p.2 ∧
        tricomiIncompleteGamma p.1 p.2=0 ∧ deriv (fun a : ℂ => tricomiIncompleteGamma a p.2) p.1=0 ∧
        iteratedDeriv 2 (fun a : ℂ => tricomiIncompleteGamma a p.2) p.1 ≠ 0 ∧
        ({a : ℝ | -2*(n : ℝ) < a ∧ a < 1-2*(n : ℝ) ∧ tricomiIncompleteGamma a p.2=0} : Set
            ℝ).ncard=1 := by
  sorry

/-- Estimate under the stated parameter and domain assumptions:
`tricomiIncompleteGamma a 0=0 ↔ ∃ n : ℕ, 1 ≤ n ∧ a = -(n : ℝ)`. -/
theorem tricomiIncompleteGamma_parameter_zeros_at_x_zero (a : ℝ) :
    tricomiIncompleteGamma a 0=0 ↔ ∃ n : ℕ, 1 ≤ n ∧ a = -(n : ℝ) := by
  have h := tricomiIncompleteGamma_hasSum_exponential (a:ℂ) 0
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.sum_range_one, pow_zero, neg_zero, Complex.exp_zero, one_mul, Nat.cast_zero,
    add_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    mul_zero, zero_div] at h
  have h0 := (hasSum_zero.unique h)
  rw [show tricomiIncompleteGamma a 0 = 1/Gamma (a+1) by linear_combination -h0,
                                                           one_div, inv_eq_zero,
    Complex.Gamma_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m+1, by omega, ?_⟩
    have := congrArg Complex.re hm
    simp at this; push_cast; linarith
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n-1, ?_⟩
    rw [Nat.cast_sub hn]; push_cast; ring

/-- Estimate under the stated parameter and domain assumptions: `∃ δ : ℝ, 0 < δ ∧ ∃ f : ℝ → ℂ,
ContinuousOn f (Icc (scIncGammaDoubleZero n).2 ((scIncGammaDoubleZero n).2+δ)) ∧ f
(scIncGammaDoubleZero n).2=(scIncGammaDoubleZero n).1 ∧ ∀ x ∈ Ioo (scIncGammaDoubleZero n).2
((scIncGammaDoubleZero n).2+δ), 0 < (f x).im ∧ tricomiIncompleteGamma (f x) x=0 ∧
tricomiIncompleteGamma (star (f x)) x=0`. -/
theorem tricomiIncompleteGamma_conjugate_zero_trajectories {n : ℕ} (hn : 1 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ f : ℝ → ℂ,
        ContinuousOn f (Icc (scIncGammaDoubleZero n).2 ((scIncGammaDoubleZero n).2+δ)) ∧
        f (scIncGammaDoubleZero n).2=(scIncGammaDoubleZero n).1 ∧ ∀ x ∈
        Ioo (scIncGammaDoubleZero n).2 ((scIncGammaDoubleZero n).2+δ), 0 < (f x).im ∧
        tricomiIncompleteGamma (f x) x=0 ∧ tricomiIncompleteGamma (star (f x)) x=0 := by
  sorry


end DLMF.Confluent
