/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.SpecialValues.RealAndHalfPeriods

/-!
# Limits of Jacobian elliptic functions as the modulus degenerates

The limiting forms of Table 22.5.3 (`k → 0+`), where the Jacobian elliptic functions tend to
trigonometric functions, and of Table 22.5.4 (`k → 1-`), where they tend to hyperbolic
functions.

## Main definitions

* `jacobiLetterThetaLimit`: the limits of the normalized theta functions as `Im τ → ∞`.

## Main results

* `tendsto_jacobiSnk_zero`, `tendsto_jacobiCnk_zero`, `tendsto_jacobiDnk_zero` and the nine
  companions such as `tendsto_jacobiCsk_zero`: Table 22.5.3.
* `tendsto_jacobiSnk_one`, `tendsto_jacobiCnk_one`, `tendsto_jacobiDnk_one` and the nine
  companions such as `tendsto_jacobiCsk_one`: Table 22.5.4.

## Implementation notes

Table 22.5.3 is proved from `Im τ(k) → ∞`, `πz/(2K) → z` and the limits of the normalized theta
functions (dominated convergence of the theta series); Table 22.5.4 follows by Jacobi's
imaginary transformation. Limits are taken away from the poles of the limit function, except
for `cd`, `dc`, `sd`, `sc` as `k → 1-`, which hold for every `z` (DLMF excludes the poles of
the limit, where Lean's junk values still give the stated limit).
-/

@[expose] public section

open Complex DLMF.Elliptic Filter

open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

macro "jacobi_value_tac " hk:term:max : tactic => `(tactic|
  (simp only [jacobiSnk_zero $hk, jacobiCnk_zero $hk, jacobiDnk_zero $hk, jacobiCdk_zero $hk,
    jacobiSdk_zero $hk, jacobiNdk_zero $hk, jacobiDck_zero $hk, jacobiNck_zero $hk,
    jacobiSck_zero $hk, mul_one, mul_zero, neg_zero] <;> try ring))

section ModulusLimits
variable {α : Type*} {l : Filter α} {w τ : α → ℂ} {w0 : ℂ}

/-- The map `(fun i => Real.exp (-π * a * (τ i).im - 2 * π * b * (w i).im))` tends to `(𝓝 0)`
along `l`. -/
private lemma tendsto_exp_theta_term_bound_zero (hw : Tendsto w l (𝓝 w0))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun i => Real.exp (-π * a * (τ i).im - 2 * π * b * (w i).im)) l (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have h1 : Tendsto (fun i => -π * a * (τ i).im) l atBot :=
    hτ.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos])
  have h2 : Tendsto (fun i => 2 * π * b * (w i).im) l (𝓝 (2 * π * b * w0.im)) :=
    ((continuous_im.tendsto w0).comp hw).const_mul _
  exact h1.atBot_add (h2.neg) |>.congr fun i => by ring

/-- Estimate under the stated parameter and domain assumptions: `∀ᶠ i in l, |(w i).im| ≤ |w0.im| +
1 ∧ 1 ≤ (τ i).im`. -/
private lemma eventually_abs_im_le_and_one_le_im (hw : Tendsto w l (𝓝 w0)) (hτ : Tendsto (fun i => (τ i).im) l atTop) :
    ∀ᶠ i in l, |(w i).im| ≤ |w0.im| + 1 ∧ 1 ≤ (τ i).im := by
  have h1 : ∀ᶠ i in l, |(w i).im - w0.im| < 1 := by
    have := ((continuous_im.tendsto w0).comp hw)
    exact (Metric.tendsto_nhds.mp this) 1 one_pos |>.mono fun i hi => by
      simpa [Real.dist_eq] using hi
  filter_upwards [h1, hτ.eventually_ge_atTop 1] with i hi h2
  refine ⟨?_, h2⟩
  have := abs_sub_abs_le_abs_sub (w i).im w0.im
  linarith

/-- `θ(w | τ) → 1` as `Im τ → ∞`, locally uniformly in `w`. -/
private lemma tendsto_jacobiTheta₂_one (hw : Tendsto w l (𝓝 w0))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) :
    Tendsto (fun i => jacobiTheta₂ (w i) (τ i)) l (𝓝 1) := by
  have key : Tendsto (fun i => ∑' n : ℤ, jacobiTheta₂_term n (w i) (τ i)) l
      (𝓝 (∑' n : ℤ, if n = 0 then (1 : ℂ) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n : ℤ => Real.exp (-π * (1 * n ^ 2 - 2 * (|w0.im| + 1) * |n|)))
      (by simpa using summable_pow_mul_jacobiTheta₂_term_bound (|w0.im| + 1) one_pos 0)
      (fun n => ?_) ?_
    · by_cases hn : n = 0
      · subst hn; simpa [jacobiTheta₂_term] using tendsto_const_nhds
      · simp only [hn, ↓reduceIte]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simp_rw [norm_jacobiTheta₂_term]
        have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
        refine (tendsto_exp_theta_term_bound_zero hw hτ hn2 n).congr fun i => by ring_nf
    · filter_upwards [eventually_abs_im_le_and_one_le_im hw hτ] with i hi n
      exact norm_jacobiTheta₂_term_le one_pos hi.1 hi.2 n
  rw [tsum_ite_eq] at key
  exact key

/-- Identity under the stated parameter and domain assumptions: `jacobiTheta₂_term n (z + τ / 2) τ
= cexp (2 * π * I * n * z + π * I * (n ^ 2 + n) * τ)`. -/
private lemma jacobiTheta₂_term_add_half (n : ℤ) (z τ : ℂ) :
    jacobiTheta₂_term n (z + τ / 2) τ = cexp (2 * π * I * n * z + π * I * (n ^ 2 + n) * τ) := by
  rw [jacobiTheta₂_term]; congr 1; ring

/-- `θ(w + τ/2 | τ) → 1 + e^{-2πiw}` as `Im τ → ∞`. -/
private lemma tendsto_jacobiTheta₂_add_half (hw : Tendsto w l (𝓝 w0))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) :
    Tendsto (fun i => jacobiTheta₂ (w i + τ i / 2) (τ i)) l
      (𝓝 (1 + cexp (-(2 * π * I * w0)))) := by
  set S := |w0.im| + 1 + 1 / 2
  have key : Tendsto (fun i => ∑' n : ℤ, jacobiTheta₂_term n (w i + τ i / 2) (τ i)) l
      (𝓝 (∑' n : ℤ, ((if n = 0 then (1 : ℂ) else 0) +
        (if n = -1 then cexp (-(2 * π * I * w0)) else 0)))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n : ℤ => Real.exp (-π * (1 * n ^ 2 - 2 * S * |n|)))
      (by simpa using summable_pow_mul_jacobiTheta₂_term_bound S one_pos 0)
      (fun n => ?_) ?_
    · simp_rw [jacobiTheta₂_term_add_half]
      by_cases h0 : n = 0
      · subst h0; simpa using tendsto_const_nhds
      by_cases h1 : n = -1
      · subst h1; simp only [Int.reduceNeg, ↓reduceIte, zero_add, Int.cast_neg, Int.cast_one]
        have : ∀ i, cexp (2 * π * I * -1 * w i + π * I * ((-1) ^ 2 + -1) * τ i) =
            cexp (-(2 * π * I * w i)) := fun i => by congr 1; ring
        simp_rw [this]
        rw [show (if (-1 : ℤ) = 0 then (1 : ℂ) else 0) = 0 by norm_num, zero_add]
        exact (Complex.continuous_exp.tendsto _).comp ((tendsto_const_nhds.mul hw).neg)
      · simp only [h0, h1, ↓reduceIte, add_zero]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hn : (0 : ℝ) < (n : ℝ) ^ 2 + n := by
          have : n ≥ 1 ∨ n ≤ -2 := by omega
          rcases this with h | h
          · have : (1 : ℝ) ≤ n := by exact_mod_cast h
            nlinarith
          · have : (n : ℝ) ≤ -2 := by exact_mod_cast h
            nlinarith
        refine (tendsto_exp_theta_term_bound_zero hw hτ hn n).congr fun i => ?_
        rw [Complex.norm_exp]; congr 1
        simp only [add_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, intCast_re,
          intCast_im, add_im, pow_two, re_ofNat, im_ofNat]
        ring
    · filter_upwards [eventually_abs_im_le_and_one_le_im hw hτ] with i hi n
      rw [jacobiTheta₂_term_add_half, Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : (2 * π * I * n * w i + π * I * (n ^ 2 + n) * τ i).re =
          -π * ((n : ℝ) ^ 2 + n) * (τ i).im - 2 * π * n * (w i).im := by
        simp only [add_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, intCast_re,
          intCast_im, add_im, pow_two, re_ofNat, im_ofNat]
        ring
      rw [hre]
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 + n := by
        have : n ≥ 0 ∨ n ≤ -1 := by omega
        rcases this with h | h
        · have : (0 : ℝ) ≤ n := by exact_mod_cast h
          nlinarith
        · have : (n : ℝ) ≤ -1 := by exact_mod_cast h
          nlinarith
      have h1 : -π * ((n : ℝ) ^ 2 + n) * (τ i).im ≤ -π * ((n : ℝ) ^ 2 + n) := by
        have := mul_le_mul_of_nonneg_left hi.2 hnn
        nlinarith [Real.pi_pos]
      have h2 : -(2 * π * n * (w i).im) ≤ 2 * π * |(n : ℝ)| * (|w0.im| + 1) := by
        have := abs_mul (n : ℝ) (w i).im
        have h3 : -((n : ℝ) * (w i).im) ≤ |(n : ℝ)| * |(w i).im| := by
          rw [← abs_mul]; exact neg_le_abs _
        have h4 : |(n : ℝ)| * |(w i).im| ≤ |(n : ℝ)| * (|w0.im| + 1) :=
          mul_le_mul_of_nonneg_left hi.1 (abs_nonneg _)
        nlinarith [Real.pi_pos]
      have h5 : -(n : ℝ) ≤ |(n : ℝ)| := neg_le_abs _
      have h6 := mul_le_mul_of_nonneg_left h5 Real.pi_pos.le
      simp only [S, Int.cast_abs]
      nlinarith [Real.pi_pos]
  have hs1 : Summable fun n : ℤ => if n = 0 then (1 : ℂ) else 0 :=
    summable_of_ne_finset_zero (s := {0}) (by intro n hn; simp_all)
  have hs2 : Summable fun n : ℤ => if n = -1 then cexp (-(2 * π * I * w0)) else 0 :=
    summable_of_ne_finset_zero (s := {-1}) (by intro n hn; simp_all)
  rw [Summable.tsum_add hs1 hs2, tsum_ite_eq, tsum_ite_eq] at key
  exact key

/-- Limits of the normalized theta functions as `Im τ → ∞`. -/
noncomputable def jacobiLetterThetaLimit (p : JacobiLetter) (z : ℂ) : ℂ :=
  match p with
  | .s => Complex.sin z
  | .c => Complex.cos z
  | .d => 1
  | .n => 1

/-- The map `(fun i => jacobiThetaThreeTau (ζ i) (τ i))` tends to `(𝓝 1)` along `l`. -/
private lemma tendsto_jacobiThetaThreeTau_one {ζ : α → ℂ} {z : ℂ} (hζ : Tendsto ζ l (𝓝 z))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) :
    Tendsto (fun i => jacobiThetaThreeTau (ζ i) (τ i)) l (𝓝 1) :=
  tendsto_jacobiTheta₂_one (hζ.div_const _) hτ

/-- The map `(fun i => jacobiThetaTwoTau (ζ i) (τ i) / jacobiThetaTwoTau 0 (τ i))` tends to `(𝓝
(Complex.cos z))` along `l`. -/
private lemma tendsto_jacobiThetaTwoTau_div_cos {ζ : α → ℂ} {z : ℂ} (hζ : Tendsto ζ l (𝓝 z))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) :
    Tendsto (fun i => jacobiThetaTwoTau (ζ i) (τ i) / jacobiThetaTwoTau 0 (τ i)) l
      (𝓝 (Complex.cos z)) := by
  have e : ∀ i, jacobiThetaTwoTau (ζ i) (τ i) / jacobiThetaTwoTau 0 (τ i) =
      cexp (I * ζ i) * jacobiTheta₂ (ζ i / π + τ i / 2) (τ i) /
        jacobiTheta₂ (0 / π + τ i / 2) (τ i) := fun i => by
    simp only [jacobiThetaTwoTau, jacobiThetaThreeTau]
    rw [show (ζ i + π * τ i / 2) / π = ζ i / π + τ i / 2 by field_simp,
      show (0 + π * τ i / 2) / π = 0 / π + τ i / 2 by field_simp, Complex.exp_add,
      mul_zero, add_zero, mul_assoc, mul_div_mul_left _ _ (exp_ne_zero _)]
  simp_rw [e]
  have h1 := tendsto_jacobiTheta₂_add_half (hζ.div_const (π : ℂ)) hτ
  have h0 := tendsto_jacobiTheta₂_add_half (w := fun _ => (0 : ℂ) / π) tendsto_const_nhds hτ
  have h2 : Tendsto (fun i => cexp (I * ζ i)) l (𝓝 (cexp (I * z))) :=
    (Complex.continuous_exp.tendsto _).comp (hζ.const_mul I)
  have hne : (1 + cexp (-(2 * π * I * (0 / π)))) ≠ 0 := by norm_num
  have H : Tendsto (fun i => cexp (I * ζ i) * jacobiTheta₂ (ζ i / π + τ i / 2) (τ i) /
      jacobiTheta₂ (0 / π + τ i / 2) (τ i)) l
      (𝓝 (cexp (I * z) * (1 + cexp (-(2 * π * I * (z / π)))) /
        (1 + cexp (-(2 * π * I * (0 / π)))))) := (h2.mul h1).div h0 hne
  convert H using 2
  rw [Complex.cos]
  have : cexp (-(2 * π * I * (z / π))) = cexp (-z * I) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; field_simp; ring
  rw [this, show cexp (I * z) = cexp (z * I) by ring_nf]
  simp only [zero_div, mul_zero, neg_zero, Complex.exp_zero]
  have hm : cexp (z * I) * cexp (-z * I) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  simp only [neg_mul] at hm this ⊢
  field_simp
  linear_combination (-2 * cexp (-(z * I))) * hm

/-- The map `(fun i => jacobiLetterTheta p (ζ i) (τ i))` tends to `(𝓝 (jacobiLetterThetaLimit p z))` along `l`. -/
private lemma tendsto_jacobiLetterTheta_limit {ζ : α → ℂ} {z : ℂ} (hζ : Tendsto ζ l (𝓝 z))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) (p : JacobiLetter) :
    Tendsto (fun i => jacobiLetterTheta p (ζ i) (τ i)) l (𝓝 (jacobiLetterThetaLimit p z)) := by
  have t30 := tendsto_jacobiThetaThreeTau_one (ζ := fun _ => (0 : ℂ)) tendsto_const_nhds hτ
  have t40 := tendsto_jacobiThetaThreeTau_one (ζ := fun _ => (0 : ℂ) + π / 2) tendsto_const_nhds hτ
  cases p
  · simp only [jacobiLetterTheta, jacobiLetterThetaLimit, jacobiThetaOneTau]
    have h := tendsto_jacobiThetaTwoTau_div_cos (hζ.add_const (π / 2 : ℂ)) hτ
    have e : ∀ i, jacobiThetaThreeTau 0 (τ i) / (jacobiThetaTwoTau 0 (τ i) *
        jacobiThetaFourTau 0 (τ i)) * -jacobiThetaTwoTau (ζ i + π / 2) (τ i) =
        -(jacobiThetaThreeTau 0 (τ i) / jacobiThetaThreeTau (0 + π / 2) (τ i)) *
          (jacobiThetaTwoTau (ζ i + π / 2) (τ i) / jacobiThetaTwoTau 0 (τ i)) := fun i => by
      rw [jacobiThetaFourTau]; ring
    simp_rw [e]
    have hq : Tendsto (fun i => jacobiThetaThreeTau 0 (τ i) / jacobiThetaThreeTau (0 + π / 2) (τ i))
        l (𝓝 1) := by
      have := t30.div t40 one_ne_zero
      simpa only [Pi.div_def, div_one] using this
    convert (hq.neg.mul h) using 1
    rw [Complex.cos_add_pi_div_two]; ring
  · simpa [jacobiLetterTheta, jacobiLetterThetaLimit] using tendsto_jacobiThetaTwoTau_div_cos hζ hτ
  · have := (tendsto_jacobiThetaThreeTau_one hζ hτ).div t30 one_ne_zero
    simpa only [Pi.div_def, div_one, jacobiLetterTheta, jacobiLetterThetaLimit] using this
  · simp only [jacobiLetterTheta, jacobiLetterThetaLimit, jacobiThetaFourTau]
    have := (tendsto_jacobiThetaThreeTau_one (hζ.add_const (π / 2 : ℂ)) hτ).div t40 one_ne_zero
    simpa only [Pi.div_def, div_one, zero_add] using this

end ModulusLimits
/-- The map `(fun k : ℝ => (jacobiTauk (k : ℂ)).im)` tends to `atTop` along `(𝓝[>] 0)`. -/
private lemma tendsto_im_jacobiTauk_atTop :
    Tendsto (fun k : ℝ => (jacobiTauk (k : ℂ)).im) (𝓝[>] 0) atTop := by
  have hc : Tendsto (fun k : ℝ => Real.compEllIntKm (k ^ 2)) (𝓝 0) (𝓝 (π / 2)) := by
    have h1 : ContinuousAt Real.compEllIntKm ((0 : ℝ) ^ 2) :=
      Real.continuousAt_compEllIntKm (by norm_num)
    have := (h1.comp (f := fun k : ℝ => k ^ 2) (continuous_pow 2).continuousAt).tendsto
    simpa [Real.compEllIntKm_zero, Function.comp_def] using this
  have hev : ∀ᶠ k : ℝ in 𝓝[>] 0, Real.compEllIntKm (k ^ 2) < 2 :=
    nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds (by linarith [Real.pi_lt_four])))
  have hlog : Tendsto (fun k : ℝ => Real.log (π / 2 / k) / √2 / 2) (𝓝[>] 0) atTop :=
    tendsto_log_pi_div_two_div_div_sqrt_two.atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hK hk
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  have hKpos := Real.compEllIntKm_pos hk2
  have hτ : jacobiTauk (k : ℂ) = I * ((Real.compEllIntKm (1 - k ^ 2) /
      Real.compEllIntKm (k ^ 2) : ℝ) : ℂ) := by
    rw [jacobiTauk, compEllIntKk_ofReal hk2, compEllIntKpk_ofReal (by nlinarith [hk.1])]
    push_cast; ring
  rw [hτ, Complex.mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]
  have hge := log_div_sqrt_two_le_compEllIntKm hk.1 (by linarith [hk.2, Real.pi_gt_three])
  have hKp : 0 ≤ Real.compEllIntKm (1 - k ^ 2) := by
    rw [Real.compEllIntKm]
    exact intervalIntegral.integral_nonneg (by positivity) fun θ _ =>
      Real.rpow_nonneg (one_sub_mul_sin_sq_pos (by nlinarith [hk.1]) θ).le _
  rw [le_div_iff₀ hKpos]
  calc Real.log (π / 2 / k) / √2 / 2 * Real.compEllIntKm (k ^ 2)
      ≤ Real.compEllIntKm (1 - k ^ 2) / 2 * Real.compEllIntKm (k ^ 2) := by
        gcongr
    _ ≤ Real.compEllIntKm (1 - k ^ 2) := by nlinarith

/-- The map `(fun k : ℝ => jacobiZetak z k)` tends to `(𝓝 z)` along `(𝓝[>] 0)`. -/
private lemma tendsto_jacobiZetak_modulus_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiZetak z k) (𝓝[>] 0) (𝓝 z) := by
  have h := (tendsto_compEllIntKk_zero.const_mul (2 : ℂ))
  have hne : (2 : ℂ) * (π / 2 : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have := (tendsto_const_nhds (x := (π : ℂ) * z)).div h hne
  convert this using 2
  · rfl
  · field_simp

/-- The map `(fun k : ℝ => jacobiPQk p q z k)` tends to `(𝓝 (jacobiLetterThetaLimit p z / jacobiLetterThetaLimit q z))` along
`(𝓝[>] 0)`. -/
private lemma tendsto_jacobiPQk_modulus_zero {p q : JacobiLetter} (hpq : p ≠ q) (z : ℂ)
    (hq : jacobiLetterThetaLimit q z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiPQk p q z k) (𝓝[>] 0) (𝓝 (jacobiLetterThetaLimit p z / jacobiLetterThetaLimit q z)) := by
  unfold jacobiPQk jacobiGlaisher
  simp only [hpq, ↓reduceIte]
  exact (tendsto_jacobiLetterTheta_limit (tendsto_jacobiZetak_modulus_zero z) tendsto_im_jacobiTauk_atTop p).div
    (tendsto_jacobiLetterTheta_limit (tendsto_jacobiZetak_modulus_zero z) tendsto_im_jacobiTauk_atTop q) hq

/-- Table T3: `sn(z, k) → Complex.sin z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiSnk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiSnk z k) (𝓝[>] 0) (𝓝 (Complex.sin z)) := by
  simpa [jacobiLetterThetaLimit, jacobiSnk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .s) (q := .n) (by decide) z (by simp [jacobiLetterThetaLimit])

/-- Table T3: `cd(z, k) → Complex.cos z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiCdk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiCdk z k) (𝓝[>] 0) (𝓝 (Complex.cos z)) := by
  simpa [jacobiLetterThetaLimit, jacobiCdk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .c) (q := .d) (by decide) z (by simp [jacobiLetterThetaLimit])

/-- Table T3: `dc(z, k) → (Complex.cos z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiDck_zero (z : ℂ) (hz : Complex.cos z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDck z k) (𝓝[>] 0) (𝓝 ((Complex.cos z)⁻¹)) := by
  simpa [jacobiLetterThetaLimit, jacobiDck, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .d) (q := .c) (by decide) z (by simpa [jacobiLetterThetaLimit] using hz)

/-- Table T3: `ns(z, k) → (Complex.sin z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiNsk_zero (z : ℂ) (hz : Complex.sin z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNsk z k) (𝓝[>] 0) (𝓝 ((Complex.sin z)⁻¹)) := by
  simpa [jacobiLetterThetaLimit, jacobiNsk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .n) (q := .s) (by decide) z (by simpa [jacobiLetterThetaLimit] using hz)

/-- Table T3: `cn(z, k) → Complex.cos z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiCnk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiCnk z k) (𝓝[>] 0) (𝓝 (Complex.cos z)) := by
  simpa [jacobiLetterThetaLimit, jacobiCnk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .c) (q := .n) (by decide) z (by simp [jacobiLetterThetaLimit])

/-- Table T3: `sd(z, k) → Complex.sin z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiSdk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiSdk z k) (𝓝[>] 0) (𝓝 (Complex.sin z)) := by
  simpa [jacobiLetterThetaLimit, jacobiSdk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .s) (q := .d) (by decide) z (by simp [jacobiLetterThetaLimit])

/-- Table T3: `nc(z, k) → (Complex.cos z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiNck_zero (z : ℂ) (hz : Complex.cos z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNck z k) (𝓝[>] 0) (𝓝 ((Complex.cos z)⁻¹)) := by
  simpa [jacobiLetterThetaLimit, jacobiNck, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .n) (q := .c) (by decide) z (by simpa [jacobiLetterThetaLimit] using hz)

/-- Table T3: `ds(z, k) → (Complex.sin z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiDsk_zero (z : ℂ) (hz : Complex.sin z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDsk z k) (𝓝[>] 0) (𝓝 ((Complex.sin z)⁻¹)) := by
  simpa [jacobiLetterThetaLimit, jacobiDsk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .d) (q := .s) (by decide) z (by simpa [jacobiLetterThetaLimit] using hz)

/-- Table T3: `dn(z, k) → 1` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiDnk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiDnk z k) (𝓝[>] 0) (𝓝 (1)) := by
  simpa [jacobiLetterThetaLimit, jacobiDnk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .d) (q := .n) (by decide) z (by simp [jacobiLetterThetaLimit])

/-- Table T3: `nd(z, k) → 1` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiNdk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiNdk z k) (𝓝[>] 0) (𝓝 (1)) := by
  simpa [jacobiLetterThetaLimit, jacobiNdk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .n) (q := .d) (by decide) z (by simp [jacobiLetterThetaLimit])

/-- Table T3: `sc(z, k) → Complex.tan z` as real `k → 0+`, away from the poles of the
limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiSck_zero (z : ℂ) (hz : Complex.cos z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiSck z k) (𝓝[>] 0) (𝓝 (Complex.tan z)) := by
  simpa [jacobiLetterThetaLimit, jacobiSck, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .s) (q := .c) (by decide) z (by simpa [jacobiLetterThetaLimit] using hz)

/-- Table T3: `cs(z, k) → Complex.cot z` as real `k → 0+`, away from the poles of the
limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiCsk_zero (z : ℂ) (hz : Complex.sin z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiCsk z k) (𝓝[>] 0) (𝓝 (Complex.cot z)) := by
  simpa [jacobiLetterThetaLimit, jacobiCsk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    tendsto_jacobiPQk_modulus_zero (p := .c) (q := .s) (by decide) z (by simpa [jacobiLetterThetaLimit] using hz)

/-- Identity under the stated parameter and domain assumptions: `jacobiComodulusk (x : ℂ) = ((√(1
- x ^ 2) : ℝ) : ℂ)`. -/
lemma jacobiComodulusk_ofReal {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    jacobiComodulusk (x : ℂ) = ((√(1 - x ^ 2) : ℝ) : ℂ) := by
  rw [jacobiComodulusk, Real.sqrt_eq_rpow, ofReal_cpow (by nlinarith)]
  push_cast; ring_nf

/-- The map `(fun k : ℝ => √(1 - k ^ 2))` tends to `(𝓝[>] 0)` along `(𝓝[<] 1)`. -/
private lemma tendsto_sqrt_one_sub_sq :
    Tendsto (fun k : ℝ => √(1 - k ^ 2)) (𝓝[<] 1) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun k : ℝ => √(1 - k ^ 2)) (𝓝 1) (𝓝 (√(1 - 1 ^ 2))) :=
      ((continuous_const.sub (continuous_pow 2)).sqrt).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
    exact Real.sqrt_pos.mpr (by nlinarith [hk.1, hk.2])

/-- The map `(fun k : ℝ => jacobiPQk p q z k)` tends to `(𝓝 ((if p = .s then -I else 1) / (if q =
.s then -I else 1) * ((if p = .s then -1 else 1) * (if q = .s then -1 else 1)) * (jacobiLetterThetaLimit
(jacobiLetterModularSwap p) (-I * z) / jacobiLetterThetaLimit (jacobiLetterModularSwap q) (-I * z))))` along `(𝓝[<] 1)`. -/
private lemma tendsto_jacobiPQk_modulus_one {p q : JacobiLetter} (hpq : p ≠ q) (z : ℂ)
    (hq : jacobiLetterThetaLimit (jacobiLetterModularSwap q) (-I * z) ≠ 0) :
    Tendsto (fun k : ℝ => jacobiPQk p q z k) (𝓝[<] 1)
      (𝓝 ((if p = .s then -I else 1) / (if q = .s then -I else 1) *
        ((if p = .s then -1 else 1) * (if q = .s then -1 else 1)) *
        (jacobiLetterThetaLimit (jacobiLetterModularSwap p) (-I * z) / jacobiLetterThetaLimit (jacobiLetterModularSwap q) (-I * z)))) := by
  have hσ : jacobiLetterModularSwap p ≠ jacobiLetterModularSwap q := by
    cases p <;> cases q <;> simp_all [jacobiLetterModularSwap]
  have h := ((tendsto_jacobiPQk_modulus_zero hσ (-I * z) hq).comp tendsto_sqrt_one_sub_sq).const_mul
    ((if p = .s then -I else 1) / (if q = .s then -I else 1) *
        ((if p = .s then -1 else 1) * (if q = .s then -1 else 1)))
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
  have hk' := ofReal_mem_jacobiModulusDomain hk.1 hk.2
  simp only [Function.comp_apply]
  rw [← jacobiComodulusk_ofReal hk.1 hk.2, ← jacobiPQk_I_mul hk' p q hpq,
    show I * (-I * z) = z by ring_nf; rw [I_sq]; ring]

/-- Identity under the stated parameter and domain assumptions: `Complex.sin (I * z) =
Complex.sinh z * I`. -/
private lemma sin_I_mul_eq_sinh_mul_I (z : ℂ) : Complex.sin (I * z) = Complex.sinh z * I := by
  rw [mul_comm, Complex.sin_mul_I]

/-- Identity under the stated parameter and domain assumptions: `Complex.cos (I * z) =
Complex.cosh z`. -/
private lemma cos_I_mul_eq_cosh (z : ℂ) : Complex.cos (I * z) = Complex.cosh z := by
  rw [mul_comm, Complex.cos_mul_I]

/-- Identity under the stated parameter and domain assumptions: `Complex.sin (-I * z) =
-(Complex.sinh z * I)`. -/
private lemma sin_neg_I_mul_eq_neg_sinh_mul_I (z : ℂ) : Complex.sin (-I * z) = -(Complex.sinh z * I) := by
  rw [show -I * z = (-z) * I by ring, Complex.sin_mul_I, Complex.sinh_neg]; ring

/-- Identity under the stated parameter and domain assumptions: `Complex.cos (-I * z) =
Complex.cosh z`. -/
private lemma cos_neg_I_mul_eq_cosh (z : ℂ) : Complex.cos (-I * z) = Complex.cosh z := by
  rw [show -I * z = (-z) * I by ring, Complex.cos_mul_I, Complex.cosh_neg]

/-- Table T4: `sn(z, k) → Complex.tanh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiSnk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiSnk z k) (𝓝[<] 1) (𝓝 (Complex.tanh z)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .s) (q := .n) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `cd(z, k) → 1` as real `k → 1-`, for every `z`; DLMF excludes
the poles of the limit, where Lean's division by zero applies. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiCdk_one (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiCdk z k) (𝓝[<] 1) (𝓝 (1)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .c) (q := .d) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `dc(z, k) → 1` as real `k → 1-`, for every `z`; DLMF excludes
the poles of the limit, where Lean's division by zero applies. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiDck_one (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiDck z k) (𝓝[<] 1) (𝓝 (1)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .d) (q := .c) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `ns(z, k) → (Complex.tanh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiNsk_one (z : ℂ) (hz : Complex.sinh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNsk z k) (𝓝[<] 1) (𝓝 ((Complex.tanh z)⁻¹)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .n) (q := .s) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `cn(z, k) → (Complex.cosh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiCnk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiCnk z k) (𝓝[<] 1) (𝓝 ((Complex.cosh z)⁻¹)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .c) (q := .n) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `sd(z, k) → Complex.sinh z` as real `k → 1-`, for every `z`; DLMF excludes
the poles of the limit, where Lean's division by zero applies. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiSdk_one (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiSdk z k) (𝓝[<] 1) (𝓝 (Complex.sinh z)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .s) (q := .d) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `nc(z, k) → Complex.cosh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiNck_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNck z k) (𝓝[<] 1) (𝓝 (Complex.cosh z)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .n) (q := .c) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `ds(z, k) → (Complex.sinh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiDsk_one (z : ℂ) (hz : Complex.sinh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDsk z k) (𝓝[<] 1) (𝓝 ((Complex.sinh z)⁻¹)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .d) (q := .s) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `dn(z, k) → (Complex.cosh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiDnk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDnk z k) (𝓝[<] 1) (𝓝 ((Complex.cosh z)⁻¹)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .d) (q := .n) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `nd(z, k) → Complex.cosh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiNdk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNdk z k) (𝓝[<] 1) (𝓝 (Complex.cosh z)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .n) (q := .d) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `sc(z, k) → Complex.sinh z` as real `k → 1-`, for every `z`; DLMF excludes
the poles of the limit, where Lean's division by zero applies. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiSck_one (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiSck z k) (𝓝[<] 1) (𝓝 (Complex.sinh z)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .s) (q := .c) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `cs(z, k) → (Complex.sinh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiCsk_one (z : ℂ) (hz : Complex.sinh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiCsk z k) (𝓝[<] 1) (𝓝 ((Complex.sinh z)⁻¹)) := by
  have h := tendsto_jacobiPQk_modulus_one (p := .c) (q := .s) (by decide) z
    (by simp [jacobiLetterThetaLimit, jacobiLetterModularSwap, sin_I_mul_eq_sinh_mul_I, cos_I_mul_eq_cosh, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [jacobiLetterThetaLimit, jacobiLetterModularSwap, reduceCtorEq, ↓reduceIte, sin_neg_I_mul_eq_neg_sinh_mul_I, cos_neg_I_mul_eq_cosh,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

end DLMF.JacobiElliptic

end
end
