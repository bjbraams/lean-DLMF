/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.SpecialValues
public import DLMF.Confluent.Integrals
public import DLMF.IncompleteGamma.SeriesRecurrences
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.Bernoulli
public import DLMF.Zeta.S25bHurwitzCore

/-!
# Zeros, transforms and sums, DLMF §§8.13–8.15

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Statistical

/-- The negative x-zero when it exists. -/
def Real.scIncGammaNegativeZero (a : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x < 0 ∧ scIncGamma a x=0)

/-- The positive x-zero when it exists. -/
def Real.scIncGammaPositiveZero (a : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ scIncGamma a x=0)

/-- A complex sum of nonnegative real terms with positive leading term is nonzero. -/
lemma ne_zero_of_hasSum_ofReal_nonneg {f : ℕ → ℝ} {S : ℂ} (h : HasSum (fun k => (f k : ℂ)) S)
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

/-- scIncGamma nonnegative parameter no real zeros. -/
theorem scIncGamma_nonnegative_parameter_no_real_zeros {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    scIncGamma a x ≠ 0 := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have := scIncGamma_neg_nat 0 (x:ℂ)
    simp only [Nat.cast_zero, neg_zero, pow_zero] at this
    rw [ofReal_zero, this]; exact one_ne_zero
  have hG : ∀ k : ℕ, 0 < Real.Gamma (a+k+1) := fun k => Real.Gamma_pos_of_pos (by positivity)
  rcases le_or_gt 0 x with hx | hx
  · have h := scIncGamma_hasSum_exponential (a:ℂ) x
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
    rw [regularizedHGFunCoeff_singleton, poch_ofReal,
      show (a:ℂ)+1+k = ((a+1+k : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast
    ring

/-! ### Real zeros of `γ*(a, ·)` for negative `a`

`U(x) = e^x γ*(a,x)` satisfies `x U' = (x - a) U + 1/Γ(a)`, so `|x|^a e^{-x} U(x)` is strictly
monotone on each half-line. The signs at `0` and at `±∞` come from the two power series. -/

/-- `e^z γ*(a,z) = ∑ zᵏ / Γ(a+k+1)`. -/
lemma gzero_hasSum_U (a z : ℂ) :
    HasSum (fun k : ℕ => z ^ k / Gamma (a + k + 1)) (regularizedHGFun {1} {a + 1} z) := by
  have h := (scIncGamma_hasSum_exponential a z).mul_left (exp z)
  have he : exp z * exp (-z) = 1 := by rw [← Complex.exp_add]; simp
  rw [scIncGamma, ← mul_assoc, he, one_mul] at h
  refine h.congr_fun fun k => ?_
  rw [← mul_div_assoc, ← mul_assoc, he, one_mul]

lemma gzero_hasSum_U' (a z : ℂ) :
    HasSum (fun k : ℕ => (k + 1) * z ^ k / Gamma (a + k + 2)) (regularizedHGFun {2} {a + 2} z) := by
  have hs := (hasFPowerSeriesOnBall_regularizedConfluent 2 (a + 2)).hasSum_mul_pow
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)
  refine hs.congr_fun fun k => ?_
  rw [regularizedHGFunCoeff_singleton]
  have hp : poch (2 : ℂ) k = (k + 1 : ℕ)! := by
    have h1 := poch_succ_left (1 : ℂ) k
    rw [one_mul, show (1 : ℂ) + 1 = 2 by norm_num] at h1
    rw [← h1, poch_nat_one]
  rw [hp, Nat.factorial_succ]
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  push_cast
  rw [show a + 2 + k = a + k + 2 by ring]
  field_simp

/-- The first-order ODE `z U' = (z - a) U + 1/Γ(a)` of `U(z) = e^z γ*(a,z)`. -/
lemma gzero_ode {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    z * deriv (regularizedHGFun {1} {a + 1}) z =
      (z - a) * regularizedHGFun {1} {a + 1} z + (Gamma a)⁻¹ := by
  rw [deriv_regularizedConfluent, one_mul, show (1 : ℂ) + 1 = 2 by norm_num,
    show a + 1 + 1 = a + 2 by ring]
  have hU := gzero_hasSum_U a z
  have hU2 := (gzero_hasSum_U' a z).mul_left z
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
noncomputable def gzero_U (a x : ℝ) : ℝ := (regularizedHGFun {1} {(a : ℂ) + 1} x).re

lemma gzero_hasSum_real (a x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / Real.Gamma (a + k + 1)) (gzero_U a x) ∧
      regularizedHGFun {1} {(a : ℂ) + 1} x = (gzero_U a x : ℂ) := by
  have h := gzero_hasSum_U (a : ℂ) (x : ℂ)
  have hr : HasSum (fun k : ℕ => ((x ^ k / Real.Gamma (a + k + 1) : ℝ) : ℂ))
      (regularizedHGFun {1} {(a : ℂ) + 1} x) := by
    refine h.congr_fun fun k => ?_
    rw [show (a : ℂ) + k + 1 = ((a + k + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  have hre : HasSum (fun k : ℕ => x ^ k / Real.Gamma (a + k + 1)) (gzero_U a x) := by
    have := Complex.hasSum_re hr
    simp only [ofReal_re] at this
    exact this
  refine ⟨hre, ?_⟩
  exact hr.unique (Complex.hasSum_ofReal.mpr hre)

lemma gzero_U_zero (a : ℝ) : gzero_U a 0 = (Real.Gamma (a + 1))⁻¹ := by
  have h := (gzero_hasSum_real a 0).1
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, add_zero, one_div] at h
  have h0 : HasSum (fun k : ℕ => (0 : ℝ) ^ (k + 1) / Real.Gamma (a + ↑(k + 1) + 1)) 0 := by
    simp
  linarith [h0.unique h]

lemma gzero_scIncGamma (a x : ℝ) : scIncGamma a x = exp (-(x : ℂ)) * (gzero_U a x : ℂ) := by
  rw [scIncGamma, (gzero_hasSum_real a x).2]

lemma gzero_scIncGamma_eq_zero (a x : ℝ) : scIncGamma a x = 0 ↔ gzero_U a x = 0 := by
  rw [gzero_scIncGamma, mul_eq_zero, ofReal_eq_zero]; simp [exp_ne_zero]

lemma gzero_deriv {a : ℝ} (ha : ∀ n : ℕ, (a : ℂ) ≠ -n) (x : ℝ) :
    ∃ d : ℝ, HasDerivAt (gzero_U a) d x ∧ x * d = (x - a) * gzero_U a x + (Real.Gamma a)⁻¹ := by
  refine ⟨(deriv (regularizedHGFun {1} {(a : ℂ) + 1}) x).re,
    (differentiableAt_regularizedConfluent _ _ _).hasDerivAt.real_of_complex, ?_⟩
  have h := congrArg re (gzero_ode ha (x : ℂ))
  rw [(gzero_hasSum_real a x).2, show (x : ℂ) - a = ((x - a : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, ← ofReal_inv] at h
  simpa only [re_ofReal_mul, add_re, ofReal_re] using h

lemma gzero_continuous {a : ℝ} (ha : ∀ n : ℕ, (a : ℂ) ≠ -n) : Continuous (gzero_U a) :=
  continuous_iff_continuousAt.mpr fun x => (gzero_deriv ha x).choose_spec.1.continuousAt

/-- The sign of `Γ` on `(-k-1, -k)`. -/
lemma gzero_Gamma_sign (k : ℕ) {x : ℝ} (h1 : -(k : ℝ) - 1 < x) (h2 : x < -k) :
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
lemma gzero_eventually_pos {c : ℕ → ℝ} {S : ℝ → ℝ} (m : ℕ) (hc : ∀ k, m ≤ k → 0 ≤ c k)
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

lemma gzero_nonint {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) : ∀ n : ℕ, (a : ℂ) ≠ -n := by
  intro n h
  exact ha (-n) (by exact_mod_cast congrArg re h |>.trans (by simp))

lemma gzero_U_atTop (a : ℝ) : ∀ᶠ y in atTop, 0 < gzero_U a y := by
  refine gzero_eventually_pos (c := fun k => (Real.Gamma (a + k + 1))⁻¹) (⌈|a|⌉₊)
    (fun k hk => inv_nonneg.mpr (Real.Gamma_nonneg_of_nonneg ?_)) ?_ fun y _ =>
      (gzero_hasSum_real a y).1.congr_fun fun k => by ring
  · have := Nat.le_ceil |a|
    have : (⌈|a|⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    linarith [neg_abs_le a]
  · refine inv_pos.mpr (Real.Gamma_pos_of_pos ?_)
    have := Nat.le_ceil |a|
    linarith [neg_abs_le a]

lemma gzero_hasSum_alt {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) (y : ℝ) :
    HasSum (fun k : ℕ => ((k ! : ℝ) * (a + k))⁻¹ * y ^ k)
      (Real.Gamma a * Real.exp y * gzero_U a (-y)) := by
  have ha' := gzero_nonint ha
  have hG : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero fun m h => ha (-m) (by rw [h]; simp)
  have h := scIncGamma_hasSum_alternating ha' (((-y : ℝ)) : ℂ)
  rw [gzero_scIncGamma] at h
  have hr : HasSum (fun k : ℕ => ((((k ! : ℝ) * (a + k))⁻¹ * y ^ k / Real.Gamma a : ℝ) : ℂ))
      (exp (-((-y : ℝ) : ℂ)) * (gzero_U a (-y) : ℂ)) := by
    refine h.congr_fun fun k => ?_
    rw [Complex.Gamma_ofReal]
    push_cast; field_simp
  rw [← ofReal_neg, ← ofReal_exp, ← ofReal_mul] at hr
  have hr' := Complex.hasSum_ofReal.mp hr
  have := hr'.mul_left (Real.Gamma a)
  convert this using 1
  · funext k; field_simp
  · simp only [neg_neg]; ring

lemma gzero_U_atBot {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) :
    ∀ᶠ x in atBot, 0 < Real.Gamma a * gzero_U a x := by
  have ha' := gzero_nonint ha
  have hG : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero fun m h => ha (-m) (by rw [h]; simp)
  set m := ⌈|a|⌉₊ + 1
  have hm : ∀ k, m ≤ k → 0 < a + k := by
    intro k hk
    have := Nat.le_ceil |a|
    have : ((⌈|a|⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at this
    linarith [neg_abs_le a]
  have hpos := gzero_eventually_pos (c := fun k => ((k ! : ℝ) * (a + k))⁻¹)
    (S := fun y => Real.Gamma a * Real.exp y * gzero_U a (-y)) m
    (fun k hk => inv_nonneg.mpr (mul_nonneg (by positivity) (hm k hk).le))
    (inv_pos.mpr (mul_pos (by positivity) (hm m le_rfl))) fun y _ => gzero_hasSum_alt ha y
  filter_upwards [tendsto_neg_atBot_atTop.eventually hpos] with x hx
  simp only [neg_neg] at hx
  have he := Real.exp_pos (-x)
  by_contra hc
  push Not at hc
  nlinarith

/-- On each half-line `γ*(a, ·)` has at most one zero: `|x|^a e^{-x} U(x)` is strictly monotone. -/
lemma gzero_mono_pos {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) :
    StrictMonoOn (fun t : ℝ => Real.Gamma a * (t ^ a * Real.exp (-t) * gzero_U a t)) (Ioi 0) := by
  have ha' := gzero_nonint ha
  have hG : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero fun m h => ha (-m) (by rw [h]; simp)
  set g := fun t : ℝ => Real.Gamma a * (t ^ a * Real.exp (-t) * gzero_U a t)
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt g (t ^ (a - 1) * Real.exp (-t)) t := by
    intro t ht
    obtain ⟨d, hdU, hode⟩ := gzero_deriv ha' t
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

lemma gzero_mono_neg {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) :
    StrictAntiOn (fun t : ℝ => Real.Gamma a * ((-t) ^ a * Real.exp (-t) * gzero_U a t)) (Iio 0) := by
  have ha' := gzero_nonint ha
  have hG : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero fun m h => ha (-m) (by rw [h]; simp)
  set g := fun t : ℝ => Real.Gamma a * ((-t) ^ a * Real.exp (-t) * gzero_U a t)
  have hd : ∀ t : ℝ, t < 0 → HasDerivAt g (-((-t) ^ (a - 1) * Real.exp (-t))) t := by
    intro t ht
    obtain ⟨d, hdU, hode⟩ := gzero_deriv ha' t
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

lemma gzero_unique_pos {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hUx : gzero_U a x = 0) (hUy : gzero_U a y = 0) : x = y :=
  (gzero_mono_pos ha).injOn hx hy (by simp only [hUx, hUy, mul_zero])

lemma gzero_unique_neg {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) {x y : ℝ} (hx : x < 0) (hy : y < 0)
    (hUx : gzero_U a x = 0) (hUy : gzero_U a y = 0) : x = y :=
  (gzero_mono_neg ha).injOn hx hy (by simp only [hUx, hUy, mul_zero])

lemma gzero_nonint_of_Ioo {a : ℝ} {m : ℤ} (h1 : (m : ℝ) < a) (h2 : a < m + 1) :
    ∀ n : ℤ, a ≠ n := by
  intro n hn
  rw [hn] at h1 h2
  have : m < n := by exact_mod_cast h1
  have : n < m + 1 := by exact_mod_cast h2
  omega

/-- The negative zero, when it exists and is unique, is the `ε`-chosen one. -/
lemma gzero_neg_exists {a : ℝ} (ha : ∀ n : ℤ, a ≠ n) (hs : 0 < Real.Gamma a * gzero_U a 0 → False)
    (h0 : gzero_U a 0 ≠ 0) :
    ∃ x, x < 0 ∧ gzero_U a x = 0 := by
  have ha' := gzero_nonint ha
  obtain ⟨X, hX, hX0⟩ := ((gzero_U_atBot ha).and (eventually_lt_atBot 0)).exists
  have hc := (gzero_continuous ha').continuousOn (s := Icc X 0)
  have hG : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero fun m h => ha (-m) (by rw [h]; simp)
  rcases lt_or_gt_of_ne hG with hGn | hGp
  · -- `U X < 0 < U 0`
    have hUX : gzero_U a X < 0 := by nlinarith
    have hU0 : 0 < gzero_U a 0 := by
      rcases lt_or_gt_of_ne h0 with h | h
      · exact absurd (mul_pos_of_neg_of_neg hGn h) hs
      · exact h
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo hX0.le hc ⟨hUX, hU0⟩
    exact ⟨x, hx.2, hx0⟩
  · have hUX : 0 < gzero_U a X := by nlinarith
    have hU0 : gzero_U a 0 < 0 := by
      rcases lt_or_gt_of_ne h0 with h | h
      · exact h
      · exact absurd (mul_pos hGp h) hs
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' hX0.le hc ⟨hU0, hUX⟩
    exact ⟨x, hx.2, hx0⟩



lemma gzero_exp_series (y : ℝ) : HasSum (fun k : ℕ => y ^ k / (k ! : ℝ)) (Real.exp y) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y

/-- scIncGamma one negative zero. -/
theorem scIncGamma_one_negative_zero {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : 1-2*(n : ℝ) < a) (ha1 : a < 2-2*(n : ℝ)) :
    Real.scIncGammaNegativeZero a < 0 ∧ ∀ x : ℝ, scIncGamma a x=0 ↔ x=Real.scIncGammaNegativeZero a := by
  have ha : ∀ m : ℤ, a ≠ m := gzero_nonint_of_Ioo (m := 1 - 2 * n) (by push_cast; linarith)
    (by push_cast; linarith)
  have hG : Real.Gamma a < 0 := by
    have h := gzero_Gamma_sign (2 * n - 2) (x := a) (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
      (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
    rw [show 2 * n - 2 + 1 = 2 * (n - 1) + 1 by omega, pow_succ, pow_mul] at h
    norm_num at h; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hneg : a < 0 := by linarith
  have hG1 : 0 < Real.Gamma (a + 1) := by
    rw [Real.Gamma_add_one hneg.ne]
    nlinarith
  have hU0 : 0 < gzero_U a 0 := by rw [gzero_U_zero]; exact inv_pos.mpr hG1
  obtain ⟨x0, hx0, hUx0⟩ := gzero_neg_exists ha (fun h => by nlinarith) hU0.ne'
  -- no zeros on `[0, ∞)`
  have hpos : ∀ x, 0 < x → gzero_U a x ≠ 0 := by
    intro x hx hUx
    obtain ⟨Y, hY, hYx⟩ := ((gzero_U_atTop a).and (eventually_gt_atTop x)).exists
    have hm := gzero_mono_pos ha hx (hx.trans hYx) hYx
    simp only [hUx, mul_zero] at hm
    have : 0 < Y ^ a * Real.exp (-Y) * gzero_U a Y :=
      mul_pos (mul_pos (Real.rpow_pos_of_pos (hx.trans hYx) _) (Real.exp_pos _)) hY
    nlinarith
  have hzero : ∀ x : ℝ, gzero_U a x = 0 ↔ x = x0 := by
    intro x
    refine ⟨fun hx => ?_, fun hx => hx ▸ hUx0⟩
    rcases lt_trichotomy x 0 with h | h | h
    · exact gzero_unique_neg ha h hx0 hx hUx0
    · rw [h] at hx; exact absurd hx hU0.ne'
    · exact absurd hx (hpos x h)
  have he : Real.scIncGammaNegativeZero a = x0 := by
    have hs := Classical.epsilon_spec (p := fun x : ℝ => x < 0 ∧ scIncGamma a x = 0)
      ⟨x0, hx0, (gzero_scIncGamma_eq_zero a x0).mpr hUx0⟩
    exact (hzero _).mp ((gzero_scIncGamma_eq_zero a _).mp hs.2)
  rw [he]
  exact ⟨hx0, fun x => (gzero_scIncGamma_eq_zero a x).trans (hzero x)⟩

/-- scIncGamma two real zeros. -/
theorem scIncGamma_two_real_zeros {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : -2*(n : ℝ) < a) (ha1 : a < 1-2*(n : ℝ)) :
    Real.scIncGammaNegativeZero a < 0 ∧ 0 < Real.scIncGammaPositiveZero a ∧ ∀ x : ℝ, scIncGamma a x=0 ↔ x=Real.scIncGammaNegativeZero a ∨ x=Real.scIncGammaPositiveZero a := by
  have ha : ∀ m : ℤ, a ≠ m := gzero_nonint_of_Ioo (m := -2 * n) (by push_cast; linarith)
    (by push_cast; linarith)
  have hG : 0 < Real.Gamma a := by
    have h := gzero_Gamma_sign (2 * n - 1) (x := a) (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
      (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
    rw [show 2 * n - 1 + 1 = 2 * n by omega, pow_mul] at h
    norm_num at h; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hneg : a < 0 := by linarith
  have hG1 : Real.Gamma (a + 1) < 0 := by
    rw [Real.Gamma_add_one hneg.ne]; nlinarith
  have hU0 : gzero_U a 0 < 0 := by rw [gzero_U_zero]; exact inv_lt_zero.mpr hG1
  obtain ⟨x0, hx0, hUx0⟩ := gzero_neg_exists ha (fun h => by nlinarith) hU0.ne
  -- the positive zero
  have hc : Continuous (gzero_U a) := gzero_continuous (gzero_nonint ha)
  obtain ⟨Y, hY, hY0⟩ := ((gzero_U_atTop a).and (eventually_gt_atTop 0)).exists
  obtain ⟨y0, hy0, hUy0⟩ := intermediate_value_Ioo hY0.le hc.continuousOn ⟨hU0, hY⟩
  have hzero : ∀ x : ℝ, gzero_U a x = 0 ↔ x = x0 ∨ x = y0 := by
    intro x
    refine ⟨fun hx => ?_, fun hx => hx.elim (fun h => h ▸ hUx0) (fun h => h ▸ hUy0)⟩
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inl (gzero_unique_neg ha h hx0 hx hUx0)
    · rw [h] at hx; exact absurd hx hU0.ne
    · exact Or.inr (gzero_unique_pos ha h hy0.1 hx hUy0)
  have he1 : Real.scIncGammaNegativeZero a = x0 := by
    have hs := Classical.epsilon_spec (p := fun x : ℝ => x < 0 ∧ scIncGamma a x = 0)
      ⟨x0, hx0, (gzero_scIncGamma_eq_zero a x0).mpr hUx0⟩
    rcases (hzero _).mp ((gzero_scIncGamma_eq_zero a _).mp hs.2) with h | h
    · exact h
    · exact absurd hs.1 (not_lt.mpr (h ▸ hy0.1.le))
  have he2 : Real.scIncGammaPositiveZero a = y0 := by
    have hs := Classical.epsilon_spec (p := fun x : ℝ => 0 < x ∧ scIncGamma a x = 0)
      ⟨y0, hy0.1, (gzero_scIncGamma_eq_zero a y0).mpr hUy0⟩
    rcases (hzero _).mp ((gzero_scIncGamma_eq_zero a _).mp hs.2) with h | h
    · exact absurd hs.1 (not_lt.mpr (h ▸ hx0.le))
    · exact h
  rw [he1, he2]
  exact ⟨hx0, hy0.1, fun x => (gzero_scIncGamma_eq_zero a x).trans (hzero x)⟩

/-- Real.scIncGammaNegativeZero strictAnti. -/
theorem Real.scIncGammaNegativeZero_strictAnti  :
    StrictAntiOn Real.scIncGammaNegativeZero (Ioo (-1) 0) := by
  intro a1 ha1 a2 ha2 h12
  have hn : ∀ a ∈ Ioo (-1 : ℝ) 0, (∀ m : ℤ, a ≠ m) := fun a ha =>
    gzero_nonint_of_Ioo (m := -1) (by push_cast; linarith [ha.1]) (by push_cast; linarith [ha.2])
  have hz : ∀ a ∈ Ioo (-1 : ℝ) 0, Real.scIncGammaNegativeZero a < 0 ∧
      gzero_U a (Real.scIncGammaNegativeZero a) = 0 := by
    intro a ha
    obtain ⟨hneg, hiff⟩ := scIncGamma_one_negative_zero (n := 1) le_rfl (a := a)
      (by norm_num; linarith [ha.1]) (by norm_num; linarith [ha.2])
    exact ⟨hneg, (gzero_scIncGamma_eq_zero a _).mp ((hiff _).mpr rfl)⟩
  have hG : ∀ a ∈ Ioo (-1 : ℝ) 0, Real.Gamma a < 0 := by
    intro a ha
    have h := gzero_Gamma_sign 0 (x := a) (by norm_num; linarith [ha.1]) (by norm_num; linarith [ha.2])
    norm_num at h; linarith
  obtain ⟨hx1, hU1⟩ := hz a1 ha1
  obtain ⟨hx2, hU2⟩ := hz a2 ha2
  set x1 := Real.scIncGammaNegativeZero a1
  set x2 := Real.scIncGammaNegativeZero a2
  set y := -x1
  have hy : 0 < y := by simp only [y]; linarith
  have hS1 := gzero_hasSum_alt (hn a1 ha1) y
  have hS2 := gzero_hasSum_alt (hn a2 ha2) y
  simp only [y, neg_neg, hU1, mul_zero] at hS1
  have hlt := hasSum_lt (i := 0) (fun k => ?_) ?_ hS2 hS1
  · -- `U_{a₂}(x₁) > 0`
    simp only [y, neg_neg] at hlt
    have hU : 0 < gzero_U a2 x1 := by
      have := Real.exp_pos (-x1)
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.mpr (hG a2 ha2).le) this.le) (neg_nonneg.mpr hc)]
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt' | heq
    · have := gzero_mono_neg (hn a2 ha2) hx1 hx2 hlt'
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

/-- Real.scIncGammaNegativeZero bounds. -/
@[dlmf 8.13.E1]
theorem Real.scIncGammaNegativeZero_bounds {a : ℝ} (ha0 : -1 < a) (ha1 : a < 0) :
    1+1/a < Real.scIncGammaNegativeZero a ∧ Real.scIncGammaNegativeZero a < Real.log |a| := by
  have ha : ∀ m : ℤ, a ≠ m := gzero_nonint_of_Ioo (m := -1) (by push_cast; linarith)
    (by push_cast; linarith)
  obtain ⟨hneg, hiff⟩ := scIncGamma_one_negative_zero (n := 1) le_rfl (a := a)
    (by norm_num; linarith) (by norm_num; linarith)
  set x0 := Real.scIncGammaNegativeZero a
  have hUx0 : gzero_U a x0 = 0 := (gzero_scIncGamma_eq_zero a x0).mp ((hiff x0).mpr rfl)
  have hG : Real.Gamma a < 0 := by
    have h := gzero_Gamma_sign 0 (x := a) (by norm_num; linarith) (by norm_num; linarith)
    norm_num at h; linarith
  have hm := gzero_mono_neg ha
  have hS := gzero_hasSum_alt ha
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
    have htpos : 0 < Real.Gamma a * Real.exp y * gzero_U a (-y) -
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
    have hU : gzero_U a (1 + 1 / a) < 0 := by
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
      have := ((gzero_exp_series L).mul_left (1 + a)⁻¹).add (hasSum_ite_eq 0 (a⁻¹ - (1 + a)⁻¹))
      convert this using 1
      rw [heL]; field_simp; ring
    have hlt := hasSum_lt (f := fun k : ℕ => ((k ! : ℝ) * (a + k))⁻¹ * L ^ k) (i := 2)
      (fun k => ?_) ?_ (hS L) hb
    · have hU : 0 < gzero_U a (Real.log |a|) := by
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

/-- The double parameter-zero pair (a_n*,x_n*). -/
def scIncGammaDoubleZero (n : ℕ) : ℝ × ℝ :=
  Classical.epsilon (fun p : ℝ × ℝ => -2*(n : ℝ) < p.1 ∧ p.1 < 1-2*(n : ℝ) ∧ 0 < p.2 ∧ scIncGamma p.1 p.2=0 ∧ deriv (fun a : ℂ => scIncGamma a p.2) p.1=0)

/-- scIncGamma two parameter zeros negative x. -/
theorem scIncGamma_two_parameter_zeros_negative_x {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x < 0) :
    ({a : ℝ | -2*(n : ℝ) < a ∧ a < 2-2*(n : ℝ) ∧ scIncGamma a x=0} : Set ℝ).ncard=2 := by
  sorry

/-- scIncGamma two parameter zeros positive x. -/
theorem scIncGamma_two_parameter_zeros_positive_x {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) (hx1 : x < (scIncGammaDoubleZero n).2) :
    ({a : ℝ | -2*(n : ℝ) < a ∧ a < 1-2*(n : ℝ) ∧ scIncGamma a x=0} : Set ℝ).ncard=2 := by
  sorry

/-- At coalescence the two zeros are counted with multiplicity, not as distinct points. -/
theorem scIncGamma_double_parameter_zero {n : ℕ} (hn : 1 ≤ n) :
    let p := scIncGammaDoubleZero n; -2*(n : ℝ) < p.1 ∧ p.1 < 1-2*(n : ℝ) ∧ 0 < p.2 ∧ scIncGamma p.1 p.2=0 ∧ deriv (fun a : ℂ => scIncGamma a p.2) p.1=0 ∧ iteratedDeriv 2 (fun a : ℂ => scIncGamma a p.2) p.1 ≠ 0 ∧ ({a : ℝ | -2*(n : ℝ) < a ∧ a < 1-2*(n : ℝ) ∧ scIncGamma a p.2=0} : Set ℝ).ncard=1 := by
  sorry

/-- scIncGamma parameter zeros at x zero. -/
theorem scIncGamma_parameter_zeros_at_x_zero (a : ℝ) :
    scIncGamma a 0=0 ↔ ∃ n : ℕ, 1 ≤ n ∧ a = -(n : ℝ) := by
  have h := scIncGamma_hasSum_exponential (a:ℂ) 0
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.sum_range_one, pow_zero, neg_zero, Complex.exp_zero, one_mul, Nat.cast_zero,
    add_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    mul_zero, zero_div] at h
  have h0 := (hasSum_zero.unique h)
  rw [show scIncGamma a 0 = 1/Gamma (a+1) by linear_combination -h0, one_div, inv_eq_zero,
    Complex.Gamma_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m+1, by omega, ?_⟩
    have := congrArg Complex.re hm
    simp at this; push_cast; linarith
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n-1, ?_⟩
    rw [Nat.cast_sub hn]; push_cast; ring

/-- scIncGamma conjugate zero trajectories. -/
theorem scIncGamma_conjugate_zero_trajectories {n : ℕ} (hn : 1 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ f : ℝ → ℂ, ContinuousOn f (Icc (scIncGammaDoubleZero n).2 ((scIncGammaDoubleZero n).2+δ)) ∧ f (scIncGammaDoubleZero n).2=(scIncGammaDoubleZero n).1 ∧ ∀ x ∈ Ioo (scIncGammaDoubleZero n).2 ((scIncGammaDoubleZero n).2+δ), 0 < (f x).im ∧ scIncGamma (f x) x=0 ∧ scIncGamma (star (f x)) x=0 := by
  sorry

/-- The lower Gamma in the exponentially weighted regularized Kummer normalization. -/
theorem lowerIncGamma_eq_exp_regularized {b : ℂ} (hb : ∀ k : ℕ, b≠-k) (x : ℂ) :
    lowerIncGamma b x=Gamma b*x^b*exp (-x)*regularizedHGFun {1} {b+1} x := by
  rw [lowerIncGamma_eq_regularized hb,
    regularizedConfluent_kummer_transform b (b+1) (-x)]
  simp only [show b+1-b=1 by ring, neg_neg]
  ring

/-- normIncGammaP laplace. -/
@[dlmf 8.14.E1]
theorem normIncGammaP_laplace {a b : ℂ} (ha : 0 < a.re) (hb : -1 < b.re) :
    (∫ x : ℝ in Ioi 0, exp (-a*x)*normIncGammaPContinued b x)=(1+a)^(-b)/a := by
  have ha0 := ne_zero_of_re_pos ha
  have ha1 : 1+a≠0 := ne_zero_of_re_pos (by simp; linarith)
  have hi : (∫ x : ℝ in Ioi 0, exp (-a*x)*normIncGammaPContinued b x)=
      ∫ x : ℝ in Ioi 0, exp (-(1+a)*x)*(x:ℂ)^((b+1)-1)*regularizedHGFun {1} {b+1} x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [normIncGammaPContinued,scIncGamma, add_sub_cancel_right]
    have he : exp (-a*x)*exp (-(x:ℂ))=exp (-(1+a)*x) := by rw [← Complex.exp_add]; congr 1; ring
    linear_combination (x:ℂ)^b*regularizedHGFun {1} {b+1} x*he
  rw [hi,laplace_regularizedHGFun_self (by simp; linarith) (by simp; linarith),
    show -(b+1)= -b-1 by ring, cpow_sub _ _ ha1, cpow_one, cpow_neg_one]
  field_simp [ha0]
  ring

/-- upperIncGamma laplace. -/
@[dlmf 8.14.E2]
theorem upperIncGamma_laplace {a b : ℂ} (ha : -1 < a.re) (hb : -1 < b.re) :
    (∫ x : ℝ in Ioi 0, exp (-a*x)*upperIncGamma b x)=if a=0 then Gamma (b+1) else if b=0 then log (1+a)/a else Gamma b*(1-(1+a)^(-b))/a := by
  have hm := (laplace_kummerU_gauss (a:=1-b) (b:=1) (c:=1-b) (z:=1+a)
    (by simp) (by simp only [sub_re,one_re]; linarith) (by simp; linarith)).2
  have hi : (∫ x : ℝ in Ioi 0, exp (-a*x)*upperIncGamma b x)=
      ∫ x : ℝ in Ioi 0, tricomiLaplaceKernel (1-b) 1 (1-b) (1+a) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [upperIncGamma,tricomiLaplaceKernel]
    simp only [sub_self,cpow_zero,mul_one]
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    ring
  rw [hi,hm,show 1-(1-b)+1=b+1 by ring,show (1-b)+1-(1-b)+1=(2:ℂ) by ring,
    show 1-(1+a)= -a by ring,Gamma_one,one_mul]
  have hcut : -a∈cutPlane := by change 1-(-a)∈slitPlane; left; simp; linarith
  rw [regularizedGaussHG_symm 1 (b+1) 2 hcut,
    regularizedGaussHG_eq_regularizedGaussHGIntegral (by norm_num) (by norm_num) hcut]
  simp only [regularizedGaussHGIntegral,eulerKernel,sub_self,cpow_zero,one_mul,
    show (2:ℂ)-1-1=0 by ring,show (2:ℂ)-1=1 by ring,Gamma_one,inv_one]
  simp_rw [show ∀ t : ℝ, 1-(-a)*(t:ℂ)=1+a*t by intro t; ring]
  have hslit (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : 1+a*(t:ℂ)∈slitPlane := by
    left
    simp only [add_re,one_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
    by_cases h : 0≤a.re
    · nlinarith [mul_nonneg h ht.1]
    · have hp := mul_nonneg (show 0≤ -a.re by linarith) (show 0≤1-t by linarith [ht.2])
      nlinarith
  have hcont : ContinuousOn (fun t : ℝ => (1+a*(t:ℂ))^(-(b+1))) (Icc (0:ℝ) 1) :=
    (by fun_prop : Continuous (fun t : ℝ => 1+a*(t:ℂ))).continuousOn.cpow_const hslit
  have hint : IntervalIntegrable (fun t : ℝ => (1+a*(t:ℂ))^(-(b+1))) volume 0 1 := hcont.intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
  by_cases ha0 : a=0
  · subst a
    simp
  rw [if_neg ha0]
  by_cases hb0 : b=0
  · subst b
    rw [if_pos rfl]
    norm_num only [zero_add,Gamma_one,one_mul,neg_add_rev,neg_zero,add_zero] at *
    have hd (t : ℝ) (ht : t∈uIcc (0:ℝ) 1) :
        HasDerivAt (fun u : ℝ => log (1+a*(u:ℂ))/a) ((1+a*(t:ℂ))^(-1:ℂ)) t := by
      have ht' : t∈Icc (0:ℝ) 1 := by simpa using ht
      have h := (((hasDerivAt_id (t:ℂ)).const_mul a).const_add 1).clog (hslit t ht')
      have h' := (h.div_const a).comp_ofReal
      refine (h'.congr_of_eventuallyEq (Eventually.of_forall fun u=>rfl)).congr_deriv ?_
      simp only [id_eq,mul_one,cpow_neg_one]
      field_simp
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
    simpa using hh
  rw [if_neg hb0]
  have hd (t : ℝ) (ht : t∈uIcc (0:ℝ) 1) :
      HasDerivAt (fun u : ℝ => (1+a*(u:ℂ))^(-b)/(-a*b)) ((1+a*(t:ℂ))^(-(b+1))) t := by
    have ht' : t∈Icc (0:ℝ) 1 := by simpa using ht
    have h := (((hasDerivAt_id (t:ℂ)).const_mul a).const_add 1).cpow_const (c:= -b) (hslit t ht')
    have h' := (h.div_const (-a*b)).comp_ofReal
    refine (h'.congr_of_eventuallyEq (Eventually.of_forall fun u=>rfl)).congr_deriv ?_
    simp only [id_eq,mul_one]
    rw [show -b-1= -(b+1) by ring]
    field_simp
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,add_zero,one_cpow] at hh
  rw [hh,Gamma_add_one b hb0]
  field_simp
  ring

/-- lowerIncGamma mellin. -/
@[dlmf 8.14.E3]
theorem lowerIncGamma_mellin {a b : ℂ} (ha : a.re < 0) (hab : 0 < (a+b).re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*lowerIncGamma b x) = -Gamma (a+b)/a := by
  have hbpos : 0<b.re := by simp only [add_re] at hab; linarith
  have hb := not_neg_nat_of_re_pos hbpos
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*lowerIncGamma b x)=Gamma b*
      ∫ x : ℝ in Ioi 0, exp (-(x:ℂ))*(x:ℂ)^((a+b)-1)*regularizedHGFun {1} {b+1} x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [lowerIncGamma_eq_exp_regularized hb]
    have hp : (x:ℂ)^(a-1)*(x:ℂ)^b=(x:ℂ)^((a+b)-1) := by
      rw [← cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]; congr 1; ring
    linear_combination Gamma b*exp (-(x:ℂ))*regularizedHGFun {1} {b+1} x*hp
  rw [hi,mellin_regularizedHGFun_exp hab (by simp only [add_re,sub_re,one_re]; linarith)]
  rw [show b+1-1-(a+b)= -a by ring, show b+1-1=b by ring,
    show b+1-(a+b)= -a+1 by ring, Gamma_add_one (-a) (by intro h; simp at h; simp [h] at ha)]
  have hg := Gamma_ne_zero_of_re_pos hbpos
  have hga := Gamma_ne_zero_of_re_pos (show 0<(-a).re by simpa)
  field_simp

/-- upperIncGamma mellin. -/
@[dlmf 8.14.E4]
theorem upperIncGamma_mellin {a b : ℂ} (ha : 0 < a.re) (hab : 0 < (a+b).re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*upperIncGamma b x)=Gamma (a+b)/a := by
  have hm := (laplace_kummerU_gauss (a:=1-b) (b:=a) (c:=1-b) (z:=1)
    ha (by simp only [sub_re,one_re]; simp only [add_re] at hab; linarith) (by simp)).2
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*upperIncGamma b x)=
      ∫ x : ℝ in Ioi 0, tricomiLaplaceKernel (1-b) a (1-b) 1 x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    simp only [upperIncGamma,tricomiLaplaceKernel,one_mul]
    ring
  rw [hi,hm]
  rw [show a-(1-b)+1=a+b by ring, show 1-b+a-(1-b)+1=a+1 by ring]
  simp only [sub_self]
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by simp)]
  rw [regularizedGaussHGFun_eq_div_Gamma (not_neg_nat_of_re_pos (by simp; linarith))]
  simp only [ordinaryHypergeometric_zero]
  rw [Gamma_add_one a (ne_zero_of_re_pos ha)]
  field_simp [Gamma_ne_zero_of_re_pos ha]

/-- lowerIncGamma mellin laplace. -/
@[dlmf 8.14.E5]
theorem lowerIncGamma_mellin_laplace {a b s : ℂ} (hs : 0 < s.re) (hab : 0 < (a+b).re) (hb : ∀ n : ℕ, b ≠ -n) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*exp (-s*x)*lowerIncGamma b x)=Gamma (a+b)/(b*(1+s)^(a+b))*Gamma (1+b)*DLMF.Hypergeometric.regularizedGaussHG 1 (a+b) (1+b) (1/(1+s)) := by
  have hm := laplace_regularizedHGFun (a:=1) (b:=a+b) (c:=b+1) (k:=1) (z:=1+s)
    hab (by simp; linarith) (by simp; linarith)
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*exp (-s*x)*lowerIncGamma b x)=Gamma b*
      ∫ x : ℝ in Ioi 0, exp (-(1+s)*x)*(x:ℂ)^((a+b)-1)*regularizedHGFun {1} {b+1} (1*x) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [lowerIncGamma_eq_exp_regularized hb]
    have hp : (x:ℂ)^(a-1)*(x:ℂ)^b=(x:ℂ)^((a+b)-1) := by
      rw [← cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]; congr 1; ring
    have he : exp (-s*x)*exp (-(x:ℂ))=exp (-(1+s)*x) := by rw [← Complex.exp_add]; congr 1; ring
    simp only [one_mul]
    calc
      _ = Gamma b*((x:ℂ)^(a-1)*(x:ℂ)^b)*(exp (-s*x)*exp (-(x:ℂ)))*regularizedHGFun {1} {b+1} x := by ring
      _ = _ := by rw [hp,he]; ring
  rw [hi,hm,show (1:ℂ)+b=b+1 by ring, Gamma_add_one b (by simpa using hb 0), cpow_neg]
  field_simp [show b≠0 by simpa using hb 0]

/-- upperIncGamma mellin laplace. -/
@[dlmf 8.14.E6]
theorem upperIncGamma_mellin_laplace {a b s : ℂ} (hs : -1 < s.re) (hab : 0 < (a+b).re) (ha : 0 < a.re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*exp (-s*x)*upperIncGamma b x)=Gamma (a+b)/(a*(1+s)^(a+b))*Gamma (1+a)*DLMF.Hypergeometric.regularizedGaussHG 1 (a+b) (1+a) (s/(1+s)) := by
  have hm := (laplace_kummerU_gauss (a:=1) (b:=a+b) (c:=b+1) (z:=1+s)
    hab (by simp only [add_re,sub_re,one_re]; linarith) (by simp; linarith)).2
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*exp (-s*x)*upperIncGamma b x)=
      ∫ x : ℝ in Ioi 0, tricomiLaplaceKernel 1 (a+b) (b+1) (1+s) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [upperIncGamma_eq_cpow_mul_kummerU _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]
    unfold tricomiLaplaceKernel
    have hp : (x:ℂ)^(a-1)*(x:ℂ)^b=(x:ℂ)^((a+b)-1) := by
      rw [← cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]; congr 1; ring
    have he : exp (-s*x)*exp (-(x:ℂ))=exp (-(1+s)*x) := by rw [← Complex.exp_add]; congr 1; ring
    calc
      _ = ((x:ℂ)^(a-1)*(x:ℂ)^b)*(exp (-s*x)*exp (-(x:ℂ)))*kummerU 1 (b+1) x := by ring
      _ = _ := by rw [hp,he]; ring
  rw [hi,hm,show a+b-(b+1)+1=a by ring, show 1+(a+b)-(b+1)+1=a+1 by ring,
    show 1-(1+s)= -s by ring]
  have hcut : -s∈cutPlane := by change 1-(-s)∈slitPlane; left; simp; linarith
  rw [regularizedGaussHG_pfaff (a+b) a (a+1) hcut,
    show (a+1)-a=1 by ring, show 1-(-s)=1+s by ring,
    show (-s)/(-s-1)=s/(1+s) by rw [show -s-1= -(1+s) by ring, neg_div_neg_eq]]
  have hmap : s/(1+s)∈cutPlane := by
    convert div_sub_one_mem_cutPlane hcut using 1
    rw [show -s-1= -(1+s) by ring, neg_div_neg_eq]
  rw [regularizedGaussHG_symm (a+b) 1 (a+1) hmap]
  rw [show (1:ℂ)+a=a+1 by ring,Gamma_add_one a (ne_zero_of_re_pos ha),cpow_neg]
  field_simp [ne_zero_of_re_pos ha]

/-- lowerIncGamma multiplication hasSum. -/
@[dlmf 8.15.E1]
theorem lowerIncGamma_multiplication_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (u v : ℂ) :
    HasSum (fun k : ℕ => exp (a*v)*lowerIncGammaOnLog (a+k) u*(1-exp v)^k/(k.factorial : ℂ)) (lowerIncGammaOnLog a (u+v)) := by
  have hsc (b z : ℂ) : scIncGamma b z = regularizedHGFun {b} {b+1} (-z) := by
    simpa only [add_comm 1 b] using (scIncGamma_regularized_pair b z).2
  have hf : Differentiable ℂ (regularizedHGFun {a} {a+1}) :=
    fun z => differentiableAt_regularizedConfluent _ _ z
  have ht := (Complex.hasSum_taylorSeries_of_entire hf (-exp u) (-exp (u+v))).mul_left
    (Gamma a * exp (a*(u+v)))
  have hv : Gamma a * exp (a*(u+v)) * regularizedHGFun {a} {a+1} (-exp (u+v)) =
      lowerIncGammaOnLog a (u+v) := by
    rw [lowerIncGammaOnLog, hsc]
  rw [hv] at ht
  refine ht.congr_fun fun k => ?_
  rw [iteratedDeriv_regularizedConfluent,
    show a+1+(k:ℂ) = (a+k)+1 by ring,
    ← hsc]
  have hg : Gamma a * poch a k = Gamma (a+k) := by
    rw [poch, ← Gamma_add_nat_div_Gamma_eq a ha]
    field_simp [Gamma_ne_zero ha]
  have he : exp (a*(u+v)) * exp u ^ k = exp (a*v) * exp ((a+k)*u) := by
    rw [← exp_nat_mul, ← exp_add, ← exp_add]
    congr 1
    ring
  have hd : -exp (u+v) - -exp u = exp u * (1-exp v) := by
    rw [exp_add]
    ring
  simp only [smul_eq_mul, hd, mul_pow, lowerIncGammaOnLog]
  symm
  calc
    _ = (Gamma a * poch a k) * (exp (a*(u+v)) * exp u ^ k) *
        scIncGamma (a+k) (exp u) * (1-exp v)^k / k.factorial := by ring
    _ = _ := by rw [hg, he]; ring

-- `hurwitzZetaComplex` (Euler–Maclaurin continuation) is defined in `DLMF.Zeta.S25bHurwitzCore`.

/-- Bridge to Mathlib; its existing Hurwitz zeta is periodic in a real second argument. -/
theorem hurwitzZetaComplex_mathlib {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {s : ℂ} (hs : s ≠ 1) :
    hurwitzZetaComplex s x=HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s :=
  DLMF.Zeta.s25b_hzc_mathlib hx hx1 hs

/-- Inherited logarithms and a right-half-plane convergence domain are explicit. -/
@[dlmf 8.15.E2]
theorem incompleteGamma_hurwitz_fourier_sum {a z : ℂ} (ha : a ≠ -1) (hz : 0 < z.re) {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    HasSum (fun k : ℕ => let j : ℂ := k+1; a*(exp (2*π*I*j*(z+h))/(2*π*I*j)^(a+1)*upperIncGammaOnLog a (log z+log (2*π*j)+π*I/2)+exp (-2*π*I*j*(z+h))/(-2*π*I*j)^(a+1)*upperIncGammaOnLog a (log z+log (2*π*j)-π*I/2))) (hurwitzZetaComplex (-a) (z+h)+z^(a+1)/(a+1)+(h-1/2)*z^a) := by
  sorry

/-- The function F(p,x) approximated in DLMF §8.27(i). -/
def Real.gammaDiDonatoF (p x : ℝ) : ℝ :=
  x^(-p)*Real.exp (x^2/2)*(∫ t : ℝ in Ioi x, Real.exp (-t^2/2)*t^p)

/-- The explicit approximation denominator in DLMF §8.27(i). -/
def Real.gammaDiDonatoH (p x : ℝ) : ℝ :=
  3*(x^2-p)+Real.sqrt ((x^2-p)^2+8*(x^2+p))

/-- The change of variable mentioned in DLMF §8.27(i). -/
theorem Real.gammaDiDonato_gamma (p : ℝ) {x : ℝ} (hx : 0 < x) :
    (Real.gammaDiDonatoF p x : ℂ)=(x : ℂ)^(-(p : ℂ))*Real.exp (x^2/2)*(2 : ℂ)^(((p : ℂ)-1)/2)*upperIncGamma ((p+1)/2) (x^2/2) := by
  have hx2 : 0 < x^2/2 := by positivity
  have hU := upperIncGamma_eq_integral (((p:ℂ)+1)/2) hx2
  push_cast at hU
  rw [hU]
  -- real substitution
  have himg : (fun t : ℝ => t^2/2) '' Ioi x = Ioi (x^2/2) := by
    ext u
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have : x^2 < t^2 := by nlinarith
      linarith
    · intro hu
      refine ⟨Real.sqrt (2*u), ?_, ?_⟩
      · rw [show x = Real.sqrt (x^2) from (Real.sqrt_sq hx.le).symm]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
      · rw [Real.sq_sqrt (by nlinarith [sq_nonneg x])]; ring
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioi x) (f := fun t : ℝ => t^2/2)
    (f' := fun t => t) measurableSet_Ioi
    (fun t _ => by
      have := ((hasDerivAt_pow 2 t).div_const 2)
      convert this.hasDerivWithinAt using 1; push_cast; ring)
    (fun s hs t ht hst => by
      simp only at hst
      have h1 : 0 < s := lt_trans hx hs
      have h2 : 0 < t := lt_trans hx ht
      nlinarith [sq_nonneg (s-t), sq_nonneg (s+t)])
    (fun u : ℝ => (u : ℂ)^(((p:ℂ)+1)/2-1)*cexp (-(u:ℂ)))
  rw [himg] at hsub
  have key : (∫ t : ℝ in Ioi x, ((Real.exp (-t^2/2)*t^p : ℝ) : ℂ)) =
      (2:ℂ)^(((p:ℂ)-1)/2) * ∫ u : ℝ in Ioi (x^2/2), (u : ℂ)^(((p:ℂ)+1)/2-1)*cexp (-(u:ℂ)) := by
    rw [hsub, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_trans hx ht
    simp only [Complex.real_smul]
    rw [abs_of_pos ht0]
    have hq : ((t^2/2 : ℝ) : ℂ)^(((p:ℂ)+1)/2-1) = ((t^(p-1)/2^((p-1)/2) : ℝ) : ℂ) := by
      rw [show ((p:ℂ)+1)/2-1 = (((p-1)/2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow (by positivity), Real.div_rpow (by positivity) (by norm_num),
        ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      congr 3; push_cast; ring
    have h2 : (2:ℂ)^(((p:ℂ)-1)/2) = ((2^((p-1)/2) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by norm_num)]; push_cast; ring_nf
    have htp : t^p = t * t^(p-1) := by
      conv_lhs => rw [show p = 1 + (p-1) by ring]
      rw [Real.rpow_add ht0, Real.rpow_one]
    have h2p : (0:ℝ) < 2^((p-1)/2) := by positivity
    have h2c : ((2^((p-1)/2) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h2p.ne'
    rw [hq, h2, htp]
    push_cast
    rw [show -(t:ℂ)^2/2 = -((t:ℂ)^2/2) by ring]
    field_simp
  rw [Real.gammaDiDonatoF, ofReal_mul, ofReal_mul, ← integral_complex_ofReal, ofReal_cpow hx.le, key]
  push_cast
  ring

/-- The explicit O(x^-7) approximation theorem in DLMF §8.27(i). -/
theorem Real.gammaDiDonato_approximation (p : ℝ) :
    IsBigO atTop (fun x : ℝ => Real.gammaDiDonatoF p x-4*x/Real.gammaDiDonatoH p x) (fun x => x^(-7 : ℤ)) := by
  sorry

end DLMF.Confluent
