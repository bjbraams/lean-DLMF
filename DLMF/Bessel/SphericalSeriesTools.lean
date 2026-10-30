/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Bessel.RegularizedSeries
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Tools for series in spherical Bessel functions (DLMF §§6.10, 7.6, 10.51)

Series such as `C(z) = z ∑ₙ j_{2n}(πz²/2)` (DLMF 7.6.10) or `Si(z) = z ∑ₙ j_n(z/2)²`
(DLMF 6.10.4) share one mechanism: by the recurrences of DLMF 10.51.1–10.51.2 the
derivative of the `n`-th term is a difference `gₙ - gₙ₊₁`, so the differentiated series
telescopes to `g₀`, which is the derivative of the left-hand side.

This file provides
* `sphSeries_hasSum_of_hasDerivAt`: the telescoping principle for entire terms that are
  bounded on balls by a summable sequence (termwise differentiation through
  `hasSum_deriv_of_summable_norm`);
* norm bounds and summability for the spherical Bessel functions `sphericalJ`, `sphericalI`;
* the derivative and three-term recurrences of DLMF 10.51.1–10.51.2 for `sphericalJ`, valid for
  all complex arguments (no division by `z`);
* the elementary values `z j₀(z) = sin z` and `j₀(z) - z j₁(z) = cos z`.
-/

@[expose] public noncomputable section
open Complex Filter Set
open scoped Real Topology Nat

namespace DLMF

/-! ### The telescoping principle -/

/-- Telescoping principle for series of entire functions: if `fₙ' = gₙ - gₙ₊₁`, `gₙ → 0`
pointwise, the `fₙ` are bounded on each ball by a summable sequence, `F' = g₀`, and the
series sums to `F` at the origin, then it sums to `F` everywhere. -/
theorem sphSeries_hasSum_of_hasDerivAt {f g : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hf : ∀ n w, HasDerivAt (f n) (g n w - g (n+1) w) w)
    (hg : ∀ w, Tendsto (fun n => g n w) atTop (𝓝 0))
    (hb : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n w, ‖w‖ < R → ‖f n w‖ ≤ u n)
    (hF : ∀ w, HasDerivAt F (g 0 w) w)
    (h0 : HasSum (fun n => f n 0) (F 0)) (z : ℂ) :
    HasSum (fun n => f n z) (F z) := by
  set S : ℂ → ℂ := fun w => ∑' n, f n w with hS
  have hwball : ∀ w : ℂ, w ∈ Metric.ball (0:ℂ) (‖w‖+1) := fun w => by simp
  have hloc : ∀ w : ℂ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, ∀ v ∈ Metric.ball (0:ℂ) (‖w‖+1), ‖f n v‖ ≤ u n := by
    intro w
    obtain ⟨u, hu, h⟩ := hb (‖w‖+1)
    exact ⟨u, hu, fun n v hv => h n v (by simpa using hv)⟩
  have hdiff : ∀ (U : Set ℂ) n, DifferentiableOn ℂ (f n) U := fun U n v _ =>
    (hf n v).differentiableAt.differentiableWithinAt
  have hSum : ∀ w, Summable (fun n => f n w) := fun w => by
    obtain ⟨u, hu, h⟩ := hloc w
    exact Summable.of_norm_bounded hu (fun n => h n w (hwball w))
  have hSd : ∀ w, HasDerivAt S (g 0 w) w := by
    intro w
    obtain ⟨u, hu, h⟩ := hloc w
    have hD := differentiableOn_tsum_of_summable_norm hu (hdiff _) Metric.isOpen_ball h
    have hd := hasSum_deriv_of_summable_norm hu (hdiff _) Metric.isOpen_ball h (hwball w)
    have hdw : DifferentiableAt ℂ S w :=
      (hD w (hwball w)).differentiableAt (Metric.isOpen_ball.mem_nhds (hwball w))
    have hval : deriv S w = g 0 w := by
      simp_rw [(hf _ w).deriv] at hd
      have ht := hd.tendsto_sum_nat
      have ht2 : Tendsto (fun N => ∑ n ∈ Finset.range N, (g n w - g (n+1) w)) atTop
          (𝓝 (g 0 w - 0)) := by
        simp_rw [Finset.sum_range_sub']
        exact tendsto_const_nhds.sub (hg w)
      rw [sub_zero] at ht2
      exact tendsto_nhds_unique ht ht2
    rw [← hval]
    exact hdw.hasDerivAt
  have hc : ∀ w, S w - F w = S 0 - F 0 := by
    have hD : Differentiable ℂ (fun w => S w - F w) := fun w =>
      ((hSd w).sub (hF w)).differentiableAt
    intro w
    exact is_const_of_deriv_eq_zero hD
      (fun v => by rw [((hSd v).fun_sub (hF v)).deriv, sub_self]) w 0
  have hS0 : S 0 = F 0 := h0.tsum_eq
  have hz : S z = F z := by have := hc z; rw [hS0] at this; linear_combination this
  rw [← hz]
  exact (hSum z).hasSum

/-! ### Norm bounds -/

/-- Norm bound for regularized `₀F₁` with a real parameter `c ≥ 1`. -/
theorem sphSeries_norm_regularized0F1_le {c : ℝ} (hc : 1 ≤ c) (w : ℂ) :
    ‖regularizedHGFun (∅ : Multiset ℂ) {(c : ℂ)} w‖ ≤ Real.exp ‖w‖ / Real.Gamma c := by
  have hG : ∀ k : ℕ, Real.Gamma c ≤ Real.Gamma (c + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hpos : 0 < Real.Gamma (c+k) := Real.Gamma_pos_of_pos (by positivity)
      rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity)]
      have : (1:ℝ) ≤ c + k := by have : (0:ℝ) ≤ k := k.cast_nonneg; linarith
      nlinarith
  have hGc : 0 < Real.Gamma c := Real.Gamma_pos_of_pos (by linarith)
  have hs := (NormedSpace.expSeries_div_hasSum_exp ‖w‖).div_const (Real.Gamma c)
  rw [← Real.exp_eq_exp_ℝ] at hs
  rw [DLMF.Confluent.regularizedHGFun_eq_tsum]
  refine tsum_of_norm_bounded hs fun k => ?_
  rw [DLMF.Bessel.regularizedHGFunCoeff_empty,
    show (c : ℂ) + k = ((c + k : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
  have hGk : 0 < Real.Gamma (c + k) := Real.Gamma_pos_of_pos (by positivity)
  rw [norm_mul, norm_pow, norm_div, norm_one, norm_mul, Complex.norm_natCast,
    Complex.norm_real, Real.norm_of_nonneg hGk.le]
  rw [div_div, one_div, inv_mul_eq_div]
  gcongr
  exact hG k

/-- Norm bound for the spherical Bessel function `jₙ`. -/
theorem sphSeries_norm_sphericalJ_le (n : ℕ) (z : ℂ) :
    ‖sphericalJ n z‖ ≤ Real.sqrt π * ‖z‖^n / 2^(n+1) *
      (Real.exp (‖z‖^2/4) / Real.Gamma (n+3/2)) := by
  have h := sphSeries_norm_regularized0F1_le (c := (n:ℝ)+3/2)
    (by have : (0:ℝ) ≤ n := n.cast_nonneg; linarith) (-z^2/4)
  push_cast at h
  have hw : ‖-z^2/4‖ = ‖z‖^2/4 := by simp [norm_pow]
  rw [hw] at h
  have e : ‖sphericalJ n z‖ = Real.sqrt π * ‖z‖^n / 2^(n+1) *
      ‖regularizedHGFun (∅ : Multiset ℂ) {(n:ℂ)+3/2} (-z^2/4)‖ := by
    simp [sphericalJ, norm_pow]
  rw [e]
  gcongr

/-- Norm bound for the modified spherical Bessel function `iₙ`. -/
theorem sphSeries_norm_sphericalI_le (n : ℕ) (z : ℂ) :
    ‖sphericalI n z‖ ≤ Real.sqrt π * ‖z‖^n / 2^(n+1) *
      (Real.exp (‖z‖^2/4) / Real.Gamma (n+3/2)) := by
  have h := sphSeries_norm_regularized0F1_le (c := (n:ℝ)+3/2)
    (by have : (0:ℝ) ≤ n := n.cast_nonneg; linarith) (z^2/4)
  push_cast at h
  have hw : ‖z^2/4‖ = ‖z‖^2/4 := by simp [norm_pow]
  rw [hw] at h
  have e : ‖sphericalI n z‖ = Real.sqrt π * ‖z‖^n / 2^(n+1) *
      ‖regularizedHGFun (∅ : Multiset ℂ) {(n:ℂ)+3/2} (z^2/4)‖ := by
    simp [sphericalI, norm_pow]
  rw [e]
  gcongr

/-- The bounding sequence of `sphSeries_norm_sphericalJ_le` is summable. -/
theorem sphSeries_summable_bound {R : ℝ} (hR : 0 ≤ R) :
    Summable (fun n : ℕ => Real.sqrt π * R^n / 2^(n+1) *
      (Real.exp (R^2/4) / Real.Gamma (n+3/2))) := by
  rw [← summable_nat_add_iff 1]
  have hs : Summable (fun n : ℕ => Real.sqrt π * Real.exp (R^2/4) * (R^(n+1) / (n+1)!)) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial R)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have hG : ((n+1)! : ℝ) ≤ Real.Gamma ((n+1:ℕ) + 3/2) := by
    rw [← Real.Gamma_nat_eq_factorial]
    refine Real.Gamma_strictMonoOn_Ici.monotoneOn ?_ ?_ ?_
    · simp only [mem_Ici]; push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    · simp only [mem_Ici]; push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    · push_cast; linarith
  have hf : (0:ℝ) < (n+1)! := by positivity
  have h2 : (1:ℝ) ≤ 2^(n+1+1) := one_le_pow₀ (by norm_num)
  calc Real.sqrt π * R^(n+1) / 2^(n+1+1) * (Real.exp (R^2/4) / Real.Gamma ((n+1:ℕ) + 3/2))
      ≤ Real.sqrt π * R^(n+1) / 1 * (Real.exp (R^2/4) / ((n+1)! : ℝ)) := by
        gcongr
    _ = _ := by ring

/-- Uniform summable bounds for `jₙ` on closed balls. -/
theorem sphSeries_sphericalJ_bound (R : ℝ) : ∃ u : ℕ → ℝ, Summable u ∧ (∀ n, 0 ≤ u n) ∧
    ∀ n z, ‖z‖ ≤ R → ‖sphericalJ n z‖ ≤ u n := by
  refine ⟨_, sphSeries_summable_bound (abs_nonneg R), fun n => by positivity, fun n z hz => ?_⟩
  have hz' : ‖z‖ ≤ |R| := hz.trans (le_abs_self R)
  refine (sphSeries_norm_sphericalJ_le n z).trans ?_
  have hG : 0 < Real.Gamma ((n:ℝ) + 3/2) := Real.Gamma_pos_of_pos (by positivity)
  gcongr

/-- Uniform summable bounds for `iₙ` on closed balls. -/
theorem sphSeries_sphericalI_bound (R : ℝ) : ∃ u : ℕ → ℝ, Summable u ∧ (∀ n, 0 ≤ u n) ∧
    ∀ n z, ‖z‖ ≤ R → ‖sphericalI n z‖ ≤ u n := by
  refine ⟨_, sphSeries_summable_bound (abs_nonneg R), fun n => by positivity, fun n z hz => ?_⟩
  have hz' : ‖z‖ ≤ |R| := hz.trans (le_abs_self R)
  refine (sphSeries_norm_sphericalI_le n z).trans ?_
  have hG : 0 < Real.Gamma ((n:ℝ) + 3/2) := Real.Gamma_pos_of_pos (by positivity)
  gcongr

/-- `jₙ(z) → 0` as `n → ∞`. -/
theorem sphSeries_tendsto_sphericalJ (z : ℂ) :
    Tendsto (fun n => sphericalJ n z) atTop (𝓝 0) := by
  obtain ⟨u, hu, -, h⟩ := sphSeries_sphericalJ_bound ‖z‖
  exact squeeze_zero_norm (fun n => h n z le_rfl) hu.tendsto_atTop_zero

/-- `iₙ(z) → 0` as `n → ∞`. -/
theorem sphSeries_tendsto_sphericalI (z : ℂ) :
    Tendsto (fun n => sphericalI n z) atTop (𝓝 0) := by
  obtain ⟨u, hu, -, h⟩ := sphSeries_sphericalI_bound ‖z‖
  exact squeeze_zero_norm (fun n => h n z le_rfl) hu.tendsto_atTop_zero

/-! ### Recurrences and derivatives, DLMF 10.51.1–10.51.2 -/

/-- Identity under the stated parameter and domain assumptions: `((n+1 : ℕ) : ℂ) + 3/2 = (n : ℂ) +
3/2 + 1`. -/
private lemma sphSeries_param_succ (n : ℕ) :
    ((n+1 : ℕ) : ℂ) + 3/2 = (n : ℂ) + 3/2 + 1 := by push_cast; ring

/-- Identity under the stated parameter and domain assumptions: `((n+2 : ℕ) : ℂ) + 3/2 = (n : ℂ) +
3/2 + 1 + 1`. -/
private lemma sphSeries_param_succ_succ (n : ℕ) :
    ((n+2 : ℕ) : ℂ) + 3/2 = (n : ℂ) + 3/2 + 1 + 1 := by push_cast; ring

/-- Three-term recurrence `z (j_n(z) + j_{n+2}(z)) = (2n+3) j_{n+1}(z)` (DLMF 10.51.1),
valid for all complex `z`. -/
theorem sphSeries_sphericalJ_recurrence (n : ℕ) (z : ℂ) :
    z * (sphericalJ n z + sphericalJ (n+2) z) = (2*n+3) * sphericalJ (n+1) z := by
  unfold sphericalJ
  rw [sphSeries_param_succ_succ, sphSeries_param_succ,
    DLMF.Bessel.regularized0F1_contiguous ((n:ℂ)+3/2)]
  ring

/-- Derivative of `j₀`: `j₀' = -j₁`. -/
theorem sphSeries_hasDerivAt_sphericalJ_zero (z : ℂ) :
    HasDerivAt (sphericalJ 0) (-sphericalJ 1 z) z := by
  have hw : HasDerivAt (fun z : ℂ => -z^2/4) (-(2*z)/4) z := by
    simpa using ((hasDerivAt_pow 2 z).neg.div_const 4)
  have hF := (DLMF.Bessel.hasDerivAt_regularized0F1 ((0:ℕ) + 3/2 : ℂ) (-z^2/4)).comp z hw
  have h := hF.const_mul (Real.sqrt π * z^0 / 2^(0+1) : ℂ)
  have e : sphericalJ 0 = fun z => (Real.sqrt π * z^0 / 2^(0+1) : ℂ) *
      regularizedHGFun (∅ : Multiset ℂ) {((0:ℕ) : ℂ) + 3/2} (-z^2/4) := by
    funext w; simp [sphericalJ]
  rw [e]
  convert h using 1
  · funext w; simp
  · simp only [sphericalJ]
    rw [show ((1:ℕ):ℂ) + 3/2 = ((0:ℕ):ℂ) + 3/2 + 1 by push_cast; ring]
    ring

/-- Derivative of `j_{n+1}` (DLMF 10.51.2 in the form
`(2n+3) j_{n+1}' = (n+1) j_n - (n+2) j_{n+2}`), valid for all complex `z`. -/
theorem sphSeries_hasDerivAt_sphericalJ_succ (n : ℕ) (z : ℂ) :
    HasDerivAt (sphericalJ (n+1))
      (((n+1) * sphericalJ n z - (n+2) * sphericalJ (n+2) z) / (2*n+3)) z := by
  have hw : HasDerivAt (fun z : ℂ => -z^2/4) (-(2*z)/4) z := by
    simpa using ((hasDerivAt_pow 2 z).neg.div_const 4)
  have hF := (DLMF.Bessel.hasDerivAt_regularized0F1 ((n:ℂ) + 3/2 + 1) (-z^2/4)).comp z hw
  have h := (((hasDerivAt_pow (n+1) z).const_mul (Real.sqrt π : ℂ)).div_const
    ((2:ℂ)^(n+1+1))).mul hF
  have e : sphericalJ (n+1) = fun z => (Real.sqrt π * z^(n+1)) / (2:ℂ)^(n+1+1) *
      regularizedHGFun (∅ : Multiset ℂ) {(n : ℂ) + 3/2 + 1} (-z^2/4) := by
    funext w; simp only [sphericalJ]; rw [sphSeries_param_succ]
  rw [e]
  convert h using 1
  · funext w; simp only [Pi.mul_apply, Function.comp_apply]
  simp only [sphericalJ, Function.comp_apply, Nat.add_sub_cancel]
  rw [sphSeries_param_succ_succ, DLMF.Bessel.regularized0F1_contiguous ((n:ℂ)+3/2)]
  have h3 : (2*n+3 : ℂ) ≠ 0 := by
    have : (0:ℝ) < 2*n+3 := by positivity
    exact_mod_cast this.ne'
  rw [div_eq_iff h3]
  push_cast
  ring

/-! ### Elementary values -/

/-- Power series of `j₀`: `j₀(z) = ∑ₖ (-1)ᵏ z²ᵏ/(2k+1)!`. -/
theorem sphSeries_hasSum_sphericalJ_zero (z : ℂ) :
    HasSum (fun k : ℕ => (-1)^k * z^(2*k) / ((2*k+1)! : ℂ)) (sphericalJ 0 z) := by
  have hs := ((DLMF.Bessel.hasFPowerSeriesOnBall_regularized0F1 ((0:ℕ) + 3/2 : ℂ)).hasSum_mul_pow
    (z := -z^2/4) (by simp)).mul_left (Real.sqrt π * z^0 / 2^(0+1) : ℂ)
  refine hs.congr_fun fun k => ?_
  rw [DLMF.Bessel.regularizedHGFunCoeff_empty,
    show ((0:ℕ):ℂ) + 3/2 + k = (((k+1 : ℕ) : ℝ) + 1/2 : ℝ) by push_cast; ring,
    Complex.Gamma_ofReal, Real.Gamma_nat_add_half, show 2*(k+1)-1 = 2*k+1 by omega,
    Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hd : (((2*k+1)‼ : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  have hf : ((k ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast
  field_simp
  rw [neg_pow (z^2/4) k, div_pow, ← pow_mul,
    show (4:ℂ)^k = 2^k*2^k by rw [← mul_pow]; norm_num]
  field_simp
  ring

/-- `z j₀(z) = sin z`. -/
theorem sphSeries_mul_sphericalJ_zero (z : ℂ) : z * sphericalJ 0 z = sin z := by
  refine ((sphSeries_hasSum_sphericalJ_zero z).mul_left z).unique ?_
  refine (Complex.hasSum_sin z).congr_fun fun k => ?_
  ring

/-- `j₀(0) = 1`. -/
theorem sphSeries_sphericalJ_zero_zero : sphericalJ 0 0 = 1 := by
  have h := sphSeries_hasSum_sphericalJ_zero 0
  refine h.unique ?_
  convert hasSum_ite_eq (0:ℕ) (1:ℂ) using 1
  funext k
  rcases k with _ | k <;> simp

/-- `j₀(z) - z j₁(z) = cos z`. -/
theorem sphSeries_sphericalJ_zero_sub (z : ℂ) :
    sphericalJ 0 z - z * sphericalJ 1 z = cos z := by
  have h := (hasDerivAt_id z).fun_mul (sphSeries_hasDerivAt_sphericalJ_zero z)
  have e : (fun w => id w * sphericalJ 0 w) = sin := funext sphSeries_mul_sphericalJ_zero
  rw [e] at h
  have h' := h.unique (Complex.hasDerivAt_sin z)
  simp only [id, one_mul] at h'
  linear_combination h'

/-- `j₀` is the difference quotient of the sine at the origin. -/
theorem sphSeries_sphericalJ_zero_eq_dslope (z : ℂ) : sphericalJ 0 z = dslope sin 0 z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [dslope_same, sphSeries_sphericalJ_zero_zero, Complex.deriv_sin, Complex.cos_zero]
  · rw [dslope_of_ne _ hz, slope_def_field, Complex.sin_zero, sub_zero, sub_zero,
      ← sphSeries_mul_sphericalJ_zero]
    field_simp

/-! ### Derivatives of the terms of the harvested series -/

/-- The term `w j_{n+1}(p w²)` differentiates to `x (j_n(x) - j_{n+2}(x))`, `x = p w²`. -/
theorem sphSeries_hasDerivAt_mul_sphericalJ_succ_sq (p : ℂ) (n : ℕ) (w : ℂ) :
    HasDerivAt (fun w => w * sphericalJ (n+1) (p*w^2))
      (p*w^2 * (sphericalJ n (p*w^2) - sphericalJ (n+2) (p*w^2))) w := by
  have hx : HasDerivAt (fun w : ℂ => p*w^2) (p*(2*w)) w := by
    simpa using (hasDerivAt_pow 2 w).const_mul p
  have h := (hasDerivAt_id w).fun_mul ((sphSeries_hasDerivAt_sphericalJ_succ n (p*w^2)).comp w hx)
  refine h.congr_deriv ?_
  have hr := sphSeries_sphericalJ_recurrence n (p*w^2)
  have h3 : (2*n+3 : ℂ) ≠ 0 := by
    have : (0:ℝ) < 2*n+3 := by positivity
    exact_mod_cast this.ne'
  have hc : (2*(n:ℂ)+3) * (2*(n:ℂ)+3)⁻¹ = 1 := mul_inv_cancel₀ h3
  simp only [id, Function.comp_apply]
  linear_combination (-(2*(n:ℂ)+3)⁻¹) * hr + (p*w^2 * (sphericalJ n (p*w^2) -
    sphericalJ (n+2) (p*w^2)) - sphericalJ (n+1) (p*w^2)) * hc

/-- The term `w j₀(p w²)` differentiates to `cos x - x j₁(x)`, `x = p w²`. -/
theorem sphSeries_hasDerivAt_mul_sphericalJ_zero_sq (p : ℂ) (w : ℂ) :
    HasDerivAt (fun w => w * sphericalJ 0 (p*w^2))
      (cos (p*w^2) - p*w^2 * sphericalJ 1 (p*w^2)) w := by
  have hx : HasDerivAt (fun w : ℂ => p*w^2) (p*(2*w)) w := by
    simpa using (hasDerivAt_pow 2 w).const_mul p
  have h := (hasDerivAt_id w).fun_mul ((sphSeries_hasDerivAt_sphericalJ_zero (p*w^2)).comp w hx)
  refine h.congr_deriv ?_
  rw [← sphSeries_sphericalJ_zero_sub]
  simp only [id, Function.comp_apply]
  ring

/-- The term `w j_{n+1}(w/2)²` differentiates to
`x j_n(x) j_{n+1}(x) - x j_{n+1}(x) j_{n+2}(x)`, `x = w/2`. -/
theorem sphSeries_hasDerivAt_mul_sphericalJ_succ_half_sq (n : ℕ) (w : ℂ) :
    HasDerivAt (fun w => w * sphericalJ (n+1) (w/2)^2)
      (w/2 * sphericalJ n (w/2) * sphericalJ (n+1) (w/2) -
        w/2 * sphericalJ (n+1) (w/2) * sphericalJ (n+2) (w/2)) w := by
  have hx : HasDerivAt (fun w : ℂ => w/2) (1/2) w := by
    simpa using (hasDerivAt_id w).div_const 2
  have h := (hasDerivAt_id w).fun_mul
    (((sphSeries_hasDerivAt_sphericalJ_succ n (w/2)).comp w hx).fun_pow 2)
  refine h.congr_deriv ?_
  have hr := sphSeries_sphericalJ_recurrence n (w/2)
  have h3 : (2*n+3 : ℂ) ≠ 0 := by
    have : (0:ℝ) < 2*n+3 := by positivity
    exact_mod_cast this.ne'
  have hc : (2*(n:ℂ)+3) * (2*(n:ℂ)+3)⁻¹ = 1 := mul_inv_cancel₀ h3
  simp only [id, Function.comp_apply]
  linear_combination sphericalJ (n+1) (w/2) * ((-(2*(n:ℂ)+3)⁻¹) * hr + (w/2 *
    (sphericalJ n (w/2) - sphericalJ (n+2) (w/2)) - sphericalJ (n+1) (w/2)) * hc)

/-- The term `w j₀(w/2)²` differentiates to `j₀(x) cos x - x j₀(x) j₁(x)`, `x = w/2`. -/
theorem sphSeries_hasDerivAt_mul_sphericalJ_zero_half_sq (w : ℂ) :
    HasDerivAt (fun w => w * sphericalJ 0 (w/2)^2)
      (sphericalJ 0 (w/2) * cos (w/2) - w/2 * sphericalJ 0 (w/2) * sphericalJ 1 (w/2)) w := by
  have hx : HasDerivAt (fun w : ℂ => w/2) (1/2) w := by
    simpa using (hasDerivAt_id w).div_const 2
  have h := (hasDerivAt_id w).fun_mul
    (((sphSeries_hasDerivAt_sphericalJ_zero (w/2)).comp w hx).fun_pow 2)
  refine h.congr_deriv ?_
  rw [← sphSeries_sphericalJ_zero_sub]
  simp only [id, Function.comp_apply]
  ring

/-! ### Bounds for the terms of the harvested series -/

/-- Summable bounds on balls for `w j_{σ n}(p w²)`, `σ` injective. -/
theorem sphSeries_bound_mul_sphericalJ_sq (p : ℂ) {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    (R : ℝ) : ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n w, ‖w‖ < R → ‖w * sphericalJ (σ n) (p*w^2)‖ ≤ u n := by
  obtain ⟨u, hu, hu0, h⟩ := sphSeries_sphericalJ_bound (‖p‖ * R^2)
  refine ⟨fun n => |R| * u (σ n), (hu.comp_injective hσ).mul_left _, fun n w hw => ?_⟩
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  rw [norm_mul]
  refine mul_le_mul (hw.le.trans (le_abs_self R)) (h _ _ ?_) (norm_nonneg _) (abs_nonneg R)
  rw [norm_mul, norm_pow]
  gcongr

/-- Summable bounds on balls for `w jₙ(w/2)²`. -/
theorem sphSeries_bound_mul_sphericalJ_half_sq (R : ℝ) : ∃ u : ℕ → ℝ, Summable u ∧
    ∀ n w, ‖w‖ < R → ‖w * sphericalJ n (w/2)^2‖ ≤ u n := by
  obtain ⟨u, hu, hu0, h⟩ := sphSeries_sphericalJ_bound R
  refine ⟨fun n => |R| * (u n * ∑' k, u k), (hu.mul_right _).mul_left _, fun n w hw => ?_⟩
  have hw' : ‖w/2‖ ≤ R := by
    rw [norm_div]; simp only [Complex.norm_ofNat]
    have := norm_nonneg w
    linarith
  have hb := h n (w/2) hw'
  rw [norm_mul, norm_pow, sq]
  exact mul_le_mul (hw.le.trans (le_abs_self R))
    (mul_le_mul hb (hb.trans (hu.le_tsum n (fun k _ => hu0 k))) (norm_nonneg _) (hu0 n))
    (by positivity) (abs_nonneg R)

/-! ### The modified functions `iₙ` -/

/-- `i₀(z) = j₀(iz)`. -/
theorem sphSeries_sphericalI_zero_eq (z : ℂ) : sphericalI 0 z = sphericalJ 0 (I*z) := by
  simp only [sphericalI, sphericalJ, pow_zero, mul_pow, I_sq]
  ring_nf

/-- Three-term recurrence `z (i_n(z) - i_{n+2}(z)) = (2n+3) i_{n+1}(z)` (DLMF 10.51.4),
valid for all complex `z`. -/
theorem sphSeries_sphericalI_recurrence (n : ℕ) (z : ℂ) :
    z * (sphericalI n z - sphericalI (n+2) z) = (2*n+3) * sphericalI (n+1) z := by
  unfold sphericalI
  rw [sphSeries_param_succ_succ, sphSeries_param_succ,
    DLMF.Bessel.regularized0F1_contiguous ((n:ℂ)+3/2)]
  ring

/-- Derivative of `i₀`: `i₀' = i₁`. -/
theorem sphSeries_hasDerivAt_sphericalI_zero (z : ℂ) :
    HasDerivAt (sphericalI 0) (sphericalI 1 z) z := by
  have hw : HasDerivAt (fun z : ℂ => z^2/4) ((2*z)/4) z := by
    simpa using ((hasDerivAt_pow 2 z).div_const 4)
  have hF := (DLMF.Bessel.hasDerivAt_regularized0F1 ((0:ℕ) + 3/2 : ℂ) (z^2/4)).comp z hw
  have h := hF.const_mul (Real.sqrt π * z^0 / 2^(0+1) : ℂ)
  have e : sphericalI 0 = fun z => (Real.sqrt π * z^0 / 2^(0+1) : ℂ) *
      regularizedHGFun (∅ : Multiset ℂ) {((0:ℕ) : ℂ) + 3/2} (z^2/4) := by
    funext w; simp [sphericalI]
  rw [e]
  convert h using 1
  · funext w; simp
  · simp only [sphericalI]
    rw [show ((1:ℕ):ℂ) + 3/2 = ((0:ℕ):ℂ) + 3/2 + 1 by push_cast; ring]
    ring

/-- Derivative of `i_{n+1}` (DLMF 10.51.5 in the form
`(2n+3) i_{n+1}' = (n+1) i_n + (n+2) i_{n+2}`), valid for all complex `z`. -/
theorem sphSeries_hasDerivAt_sphericalI_succ (n : ℕ) (z : ℂ) :
    HasDerivAt (sphericalI (n+1))
      (((n+1) * sphericalI n z + (n+2) * sphericalI (n+2) z) / (2*n+3)) z := by
  have hw : HasDerivAt (fun z : ℂ => z^2/4) ((2*z)/4) z := by
    simpa using ((hasDerivAt_pow 2 z).div_const 4)
  have hF := (DLMF.Bessel.hasDerivAt_regularized0F1 ((n:ℂ) + 3/2 + 1) (z^2/4)).comp z hw
  have h := (((hasDerivAt_pow (n+1) z).const_mul (Real.sqrt π : ℂ)).div_const
    ((2:ℂ)^(n+1+1))).mul hF
  have e : sphericalI (n+1) = fun z => (Real.sqrt π * z^(n+1)) / (2:ℂ)^(n+1+1) *
      regularizedHGFun (∅ : Multiset ℂ) {(n : ℂ) + 3/2 + 1} (z^2/4) := by
    funext w; simp only [sphericalI]; rw [sphSeries_param_succ]
  rw [e]
  convert h using 1
  · funext w; simp only [Pi.mul_apply, Function.comp_apply]
  simp only [sphericalI, Function.comp_apply, Nat.add_sub_cancel]
  rw [sphSeries_param_succ_succ, DLMF.Bessel.regularized0F1_contiguous ((n:ℂ)+3/2)]
  have h3 : (2*n+3 : ℂ) ≠ 0 := by
    have : (0:ℝ) < 2*n+3 := by positivity
    exact_mod_cast this.ne'
  rw [div_eq_iff h3]
  push_cast
  ring

/-- `z i₀(z) = sinh z`. -/
theorem sphSeries_mul_sphericalI_zero (z : ℂ) : z * sphericalI 0 z = sinh z := by
  rw [sphSeries_sphericalI_zero_eq, show I*z = z*I by ring]
  have h := sphSeries_mul_sphericalJ_zero (z*I)
  rw [Complex.sin_mul_I] at h
  apply mul_left_cancel₀ I_ne_zero
  linear_combination h

/-- `i₀(z) + z i₁(z) = cosh z`. -/
theorem sphSeries_sphericalI_zero_add (z : ℂ) :
    sphericalI 0 z + z * sphericalI 1 z = cosh z := by
  have h := (hasDerivAt_id z).fun_mul (sphSeries_hasDerivAt_sphericalI_zero z)
  have e : (fun w => id w * sphericalI 0 w) = sinh := funext sphSeries_mul_sphericalI_zero
  rw [e] at h
  have h' := h.unique (Complex.hasDerivAt_sinh z)
  simp only [id, one_mul] at h'
  linear_combination h'

/-- The term `w i_{n+1}(p w²)` differentiates to `x (i_n(x) + i_{n+2}(x))`, `x = p w²`. -/
theorem sphSeries_hasDerivAt_mul_sphericalI_succ_sq (p : ℂ) (n : ℕ) (w : ℂ) :
    HasDerivAt (fun w => w * sphericalI (n+1) (p*w^2))
      (p*w^2 * (sphericalI n (p*w^2) + sphericalI (n+2) (p*w^2))) w := by
  have hx : HasDerivAt (fun w : ℂ => p*w^2) (p*(2*w)) w := by
    simpa using (hasDerivAt_pow 2 w).const_mul p
  have h := (hasDerivAt_id w).fun_mul ((sphSeries_hasDerivAt_sphericalI_succ n (p*w^2)).comp w hx)
  refine h.congr_deriv ?_
  have hr := sphSeries_sphericalI_recurrence n (p*w^2)
  have h3 : (2*n+3 : ℂ) ≠ 0 := by
    have : (0:ℝ) < 2*n+3 := by positivity
    exact_mod_cast this.ne'
  have hc : (2*(n:ℂ)+3) * (2*(n:ℂ)+3)⁻¹ = 1 := mul_inv_cancel₀ h3
  simp only [id, Function.comp_apply]
  linear_combination (-(2*(n:ℂ)+3)⁻¹) * hr + (p*w^2 * (sphericalI n (p*w^2) +
    sphericalI (n+2) (p*w^2)) - sphericalI (n+1) (p*w^2)) * hc

/-- The term `w i₀(p w²)` differentiates to `cosh x + x i₁(x)`, `x = p w²`. -/
theorem sphSeries_hasDerivAt_mul_sphericalI_zero_sq (p : ℂ) (w : ℂ) :
    HasDerivAt (fun w => w * sphericalI 0 (p*w^2))
      (cosh (p*w^2) + p*w^2 * sphericalI 1 (p*w^2)) w := by
  have hx : HasDerivAt (fun w : ℂ => p*w^2) (p*(2*w)) w := by
    simpa using (hasDerivAt_pow 2 w).const_mul p
  have h := (hasDerivAt_id w).fun_mul ((sphSeries_hasDerivAt_sphericalI_zero (p*w^2)).comp w hx)
  refine h.congr_deriv ?_
  rw [← sphSeries_sphericalI_zero_add]
  simp only [id, Function.comp_apply]
  ring

/-- Summable bounds on balls for `w i_{σ n}(p w²)`, `σ` injective. -/
theorem sphSeries_bound_mul_sphericalI_sq (p : ℂ) {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    (R : ℝ) : ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n w, ‖w‖ < R → ‖w * sphericalI (σ n) (p*w^2)‖ ≤ u n := by
  obtain ⟨u, hu, hu0, h⟩ := sphSeries_sphericalI_bound (‖p‖ * R^2)
  refine ⟨fun n => |R| * u (σ n), (hu.comp_injective hσ).mul_left _, fun n w hw => ?_⟩
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  rw [norm_mul]
  refine mul_le_mul (hw.le.trans (le_abs_self R)) (h _ _ ?_) (norm_nonneg _) (abs_nonneg R)
  rw [norm_mul, norm_pow]
  gcongr

/-- `i₀(0) = 1`. -/
theorem sphSeries_sphericalI_zero_zero : sphericalI 0 0 = 1 := by
  rw [sphSeries_sphericalI_zero_eq, mul_zero, sphSeries_sphericalJ_zero_zero]

/-- `iₙ(z) = j_n(iz)/iⁿ`. -/
theorem sphSeries_sphericalI_eq (n : ℕ) (z : ℂ) :
    sphericalI n z = sphericalJ n (I*z) / I^n := by
  have hI : (I:ℂ)^n ≠ 0 := pow_ne_zero _ I_ne_zero
  simp only [sphericalI, sphericalJ, mul_pow, I_sq]
  field_simp

/-! ### The Euler operator `z ∂ + a` -/

/-- Entire functions annihilated by the Euler operator `z ∂ + a` vanish, provided their
`m`-th derivative at the origin vanishes whenever `a = -m`. -/
theorem sphSeries_eq_zero_of_euler {D : ℂ → ℂ} (hD : Differentiable ℂ D) (a : ℂ)
    (hode : ∀ z, z * deriv D z + a * D z = 0)
    (h0 : ∀ m : ℕ, a + m = 0 → iteratedDeriv m D 0 = 0) (z : ℂ) : D z = 0 := by
  have hcd : ContDiff ℂ ⊤ D := hD.contDiff
  have hdi : ∀ m, Differentiable ℂ (iteratedDeriv m D) := fun m =>
    hcd.differentiable_iteratedDeriv m (by exact_mod_cast WithTop.coe_lt_top _)
  have hder : ∀ m w, HasDerivAt (iteratedDeriv m D) (iteratedDeriv (m+1) D w) w := by
    intro m w
    rw [iteratedDeriv_succ]
    exact (hdi m w).hasDerivAt
  have hP : ∀ n w, w * iteratedDeriv (n+1) D w + (a + n) * iteratedDeriv n D w = 0 := by
    intro n
    induction n with
    | zero => intro w; simpa [iteratedDeriv_one] using hode w
    | succ n ih =>
      intro w
      have h := ((hasDerivAt_id w).mul (hder (n+1) w)).add ((hder n w).const_mul (a + n))
      have hz : (fun w => id w * iteratedDeriv (n+1) D w + (a + n) * iteratedDeriv n D w) =
          fun _ => 0 := funext ih
      have h' : HasDerivAt (fun w => id w * iteratedDeriv (n+1) D w +
          (a + n) * iteratedDeriv n D w) _ w := h
      rw [hz] at h'
      have := h'.unique (hasDerivAt_const w (0:ℂ))
      simp only [id] at this
      push_cast
      linear_combination this
  have hz0 : ∀ n, iteratedDeriv n D 0 = 0 := by
    intro n
    by_cases ha : a + n = 0
    · exact h0 n ha
    · have := hP n 0
      simp only [zero_mul, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left ha
  have hs := Complex.hasSum_taylorSeries_of_entire hD 0 z
  simp only [hz0, smul_zero] at hs
  exact (hasSum_zero.unique hs).symm

/-- Parity kills Taylor coefficients: if `D(-w) = ε D(w)` then `((-1)^m - ε) D^{(m)}(0) = 0`. -/
theorem sphSeries_iteratedDeriv_parity {D : ℂ → ℂ} {ε : ℂ} (hD : ∀ w, D (-w) = ε * D w)
    (m : ℕ) : ((-1)^m - ε) * iteratedDeriv m D 0 = 0 := by
  have h1 := iteratedDeriv_comp_neg m D 0
  have e : (fun x => D (-x)) = fun x => ε * D x := funext hD
  rw [e, iteratedDeriv_const_mul_field, neg_zero, smul_eq_mul] at h1
  linear_combination -h1

/-- Termwise Euler operator: for entire terms bounded on balls by summable sequences, the sum
is entire and `w S' + a S = ∑ (w fₙ' + a fₙ)`. -/
theorem sphSeries_euler_hasSum {f f' : ℕ → ℂ → ℂ} (a : ℂ)
    (hf : ∀ n w, HasDerivAt (f n) (f' n w) w)
    (hb : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n w, ‖w‖ < R → ‖f n w‖ ≤ u n) :
    Differentiable ℂ (fun w => ∑' n, f n w) ∧ ∀ w, HasSum (fun n => w * f' n w + a * f n w)
      (w * deriv (fun w => ∑' n, f n w) w + a * ∑' n, f n w) := by
  have hwball : ∀ w : ℂ, w ∈ Metric.ball (0:ℂ) (‖w‖+1) := fun w => by simp
  have hloc : ∀ w : ℂ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, ∀ v ∈ Metric.ball (0:ℂ) (‖w‖+1), ‖f n v‖ ≤ u n := by
    intro w
    obtain ⟨u, hu, h⟩ := hb (‖w‖+1)
    exact ⟨u, hu, fun n v hv => h n v (by simpa using hv)⟩
  have hdiff : ∀ (U : Set ℂ) n, DifferentiableOn ℂ (f n) U := fun U n v _ =>
    (hf n v).differentiableAt.differentiableWithinAt
  have hD : Differentiable ℂ (fun w => ∑' n, f n w) := by
    intro w
    obtain ⟨u, hu, h⟩ := hloc w
    exact (differentiableOn_tsum_of_summable_norm hu (hdiff _) Metric.isOpen_ball h w
      (hwball w)).differentiableAt (Metric.isOpen_ball.mem_nhds (hwball w))
  refine ⟨hD, fun w => ?_⟩
  obtain ⟨u, hu, h⟩ := hloc w
  have hd := hasSum_deriv_of_summable_norm hu (hdiff _) Metric.isOpen_ball h (hwball w)
  simp_rw [(hf _ w).deriv] at hd
  have hs : Summable (fun n => f n w) :=
    Summable.of_norm_bounded hu (fun n => h n w (hwball w))
  exact (hd.mul_left w).add (hs.hasSum.mul_left a)

/-- Telescoping principle for the Euler operator `z ∂ + a`. -/
theorem sphSeries_hasSum_of_euler {f f' g : ℕ → ℂ → ℂ} {F : ℂ → ℂ} (a : ℂ)
    (hf : ∀ n w, HasDerivAt (f n) (f' n w) w)
    (hL : ∀ n w, w * f' n w + a * f n w = g n w - g (n+1) w)
    (hg : ∀ w, Tendsto (fun n => g n w) atTop (𝓝 0))
    (hb : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n w, ‖w‖ < R → ‖f n w‖ ≤ u n)
    (hF : Differentiable ℂ F) (hFL : ∀ w, w * deriv F w + a * F w = g 0 w)
    (h0 : ∀ m : ℕ, a + m = 0 → iteratedDeriv m (fun w => ∑' n, f n w - F w) 0 = 0)
    (z : ℂ) : HasSum (fun n => f n z) (F z) := by
  obtain ⟨hD, hS⟩ := sphSeries_euler_hasSum a hf hb
  have hode : ∀ w, w * deriv (fun w => ∑' n, f n w - F w) w +
      a * (∑' n, f n w - F w) = 0 := by
    intro w
    have h1 := (hS w).tendsto_sum_nat
    simp_rw [hL, Finset.sum_range_sub'] at h1
    have h2 := tendsto_nhds_unique h1 ((tendsto_const_nhds (x := g 0 w)).sub (hg w))
    rw [sub_zero] at h2
    rw [deriv_fun_sub (hD w) (hF w)]
    linear_combination h2 - hFL w
  have hz := sphSeries_eq_zero_of_euler (hD.sub hF) a hode h0 z
  obtain ⟨u, hu, h⟩ := hb (‖z‖+1)
  have hs : Summable (fun n => f n z) :=
    Summable.of_norm_bounded hu (fun n => h n z (by linarith))
  have hz' : ∑' n, f n z - F z = 0 := hz
  have : ∑' n, f n z = F z := by linear_combination hz'
  rw [← this]
  exact hs.hasSum

/-- Parity `j_n(-z) = (-1)ⁿ j_n(z)`. -/
theorem sphSeries_sphericalJ_neg (n : ℕ) (z : ℂ) :
    sphericalJ n (-z) = (-1)^n * sphericalJ n z := by
  simp only [sphericalJ, neg_pow z, even_two.neg_pow, one_pow, one_mul]
  ring

/-- The bounding sequence of `sphSeries_norm_sphericalJ_le` gains a factor
`R²/(4(n+3/2)(n+5/2))` when the order rises by two. -/
private lemma sphSeries_bound_step (R : ℝ) (n : ℕ) :
    Real.sqrt π * R^(n+2) / 2^(n+2+1) * (Real.exp (R^2/4) / Real.Gamma ((n+2:ℕ)+3/2)) =
      Real.sqrt π * R^n / 2^(n+1) * (Real.exp (R^2/4) / Real.Gamma (n+3/2)) *
        (R^2 / (4*((n+3/2)*(n+5/2)))) := by
  have h1 : Real.Gamma ((n+2:ℕ)+3/2) = (n+5/2)*((n+3/2)*Real.Gamma (n+3/2)) := by
    rw [show ((n+2:ℕ):ℝ)+3/2 = ((n:ℝ)+3/2+1)+1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), Real.Gamma_add_one (by positivity)]
    ring
  have hG : 0 < Real.Gamma ((n:ℝ)+3/2) := Real.Gamma_pos_of_pos (by positivity)
  rw [h1]
  field_simp
  ring

/-- Summable bounds on balls for `c_k j_{2k+d}(w)` when `‖c_{k+1}‖ ≤ C ‖c_k‖` eventually. -/
theorem sphSeries_bound_coeff_mul_sphericalJ (c : ℕ → ℂ) {C : ℝ}
    (hc : ∀ᶠ k in atTop, ‖c (k+1)‖ ≤ C * ‖c k‖) (d : ℕ) (R : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ k w, ‖w‖ < R → ‖c k * sphericalJ (2*k+d) w‖ ≤ u k := by
  set B : ℕ → ℝ := fun n => Real.sqrt π * |R|^n / 2^(n+1) *
    (Real.exp (|R|^2/4) / Real.Gamma (n+3/2)) with hB
  have hB0 : ∀ n, 0 ≤ B n := fun n => by
    have : 0 < Real.Gamma ((n:ℝ)+3/2) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  refine ⟨fun k => ‖c k‖ * B (2*k+d), ?_, fun k w hw => ?_⟩
  · refine summable_of_ratio_norm_eventually_le (r := 1/2) (by norm_num) ?_
    filter_upwards [hc, eventually_ge_atTop ⌈C * |R|^2⌉₊] with k hk hk2
    have hk3 : C * |R|^2 ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk2)
    have e : 2*(k+1)+d = (2*k+d)+2 := by ring
    simp only [norm_mul, norm_norm, Real.norm_of_nonneg (hB0 _), e]
    rw [hB]; simp only
    rw [sphSeries_bound_step]
    set m : ℕ := 2*k+d
    have hm : (k:ℝ) ≤ m := by simp only [m]; push_cast; linarith [(d.cast_nonneg : (0:ℝ) ≤ d)]
    have hq : C * (|R|^2 / (4*((m+3/2)*(m+5/2)))) ≤ 1/2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
    have hb := hB0 m
    simp only [hB] at hb
    calc ‖c (k+1)‖ * (Real.sqrt π * |R|^m / 2^(m+1) * (Real.exp (|R|^2/4) /
          Real.Gamma (m+3/2)) * (|R|^2 / (4*((m+3/2)*(m+5/2)))))
        ≤ (C * ‖c k‖) * (Real.sqrt π * |R|^m / 2^(m+1) * (Real.exp (|R|^2/4) /
          Real.Gamma (m+3/2)) * (|R|^2 / (4*((m+3/2)*(m+5/2))))) := by gcongr
      _ = (C * (|R|^2 / (4*((m+3/2)*(m+5/2))))) * (‖c k‖ * (Real.sqrt π * |R|^m / 2^(m+1) *
          (Real.exp (|R|^2/4) / Real.Gamma (m+3/2)))) := by ring
      _ ≤ 1/2 * (‖c k‖ * (Real.sqrt π * |R|^m / 2^(m+1) *
          (Real.exp (|R|^2/4) / Real.Gamma (m+3/2)))) := by gcongr
  · rw [norm_mul]
    show ‖c k‖ * _ ≤ ‖c k‖ * B (2*k+d)
    gcongr
    refine (sphSeries_norm_sphericalJ_le _ w).trans ?_
    have hw' : ‖w‖ ≤ |R| := hw.le.trans (le_abs_self R)
    have : 0 < Real.Gamma (((2*k+d : ℕ) : ℝ) + 3/2) := Real.Gamma_pos_of_pos (by positivity)
    simp only [hB]
    gcongr

/-- `c_k j_{2k+d}(w) → 0` when `‖c_{k+1}‖ ≤ C ‖c_k‖` eventually. -/
theorem sphSeries_tendsto_coeff_mul_sphericalJ (c : ℕ → ℂ) {C : ℝ}
    (hc : ∀ᶠ k in atTop, ‖c (k+1)‖ ≤ C * ‖c k‖) (d : ℕ) (w : ℂ) :
    Tendsto (fun k => c k * sphericalJ (2*k+d) w) atTop (𝓝 0) := by
  obtain ⟨u, hu, h⟩ := sphSeries_bound_coeff_mul_sphericalJ c hc d (‖w‖+1)
  exact squeeze_zero_norm (fun k => h k w (by linarith)) hu.tendsto_atTop_zero

/-- Eventually `‖α + k‖ ≤ 2 ‖β + k‖`. -/
theorem sphSeries_eventually_norm_add_le (α β : ℂ) :
    ∀ᶠ k : ℕ in atTop, ‖α + k‖ ≤ 2 * ‖β + k‖ := by
  filter_upwards [eventually_ge_atTop ⌈2*‖β‖+‖α‖⌉₊] with k hk
  have hk' : 2*‖β‖+‖α‖ ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have h1 : ‖α + k‖ ≤ ‖α‖ + k := by
    refine (norm_add_le _ _).trans ?_; simp
  have h2 : (k:ℝ) - ‖β‖ ≤ ‖β + k‖ := by
    have := norm_sub_norm_le ((k:ℂ)) (-β)
    simp only [Complex.norm_natCast, norm_neg, sub_neg_eq_add] at this
    rw [add_comm] at this; linarith
  linarith

/-- The bounding sequence of `sphSeries_norm_sphericalI_le` gains a factor `R/(2(n+3/2))`
when the order rises by one. -/
private lemma sphSeries_bound_step_one (R : ℝ) (n : ℕ) :
    Real.sqrt π * R^(n+1) / 2^(n+1+1) * (Real.exp (R^2/4) / Real.Gamma ((n+1:ℕ)+3/2)) =
      Real.sqrt π * R^n / 2^(n+1) * (Real.exp (R^2/4) / Real.Gamma (n+3/2)) *
        (R / (2*(n+3/2))) := by
  have h1 : Real.Gamma ((n+1:ℕ)+3/2) = (n+3/2)*Real.Gamma (n+3/2) := by
    rw [show ((n+1:ℕ):ℝ)+3/2 = ((n:ℝ)+3/2)+1 by push_cast; ring,
      Real.Gamma_add_one (by positivity)]
  have hG : 0 < Real.Gamma ((n:ℝ)+3/2) := Real.Gamma_pos_of_pos (by positivity)
  rw [h1]
  field_simp
  ring

/-- Summable bounds on balls for `c_k i_{k+d}(w)` when `‖c_{k+1}‖ ≤ C ‖c_k‖` eventually. -/
theorem sphSeries_bound_coeff_mul_sphericalI (c : ℕ → ℂ) {C : ℝ}
    (hc : ∀ᶠ k in atTop, ‖c (k+1)‖ ≤ C * ‖c k‖) (d : ℕ) (R : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ k w, ‖w‖ < R → ‖c k * sphericalI (k+d) w‖ ≤ u k := by
  set B : ℕ → ℝ := fun n => Real.sqrt π * |R|^n / 2^(n+1) *
    (Real.exp (|R|^2/4) / Real.Gamma (n+3/2)) with hB
  have hB0 : ∀ n, 0 ≤ B n := fun n => by
    have : 0 < Real.Gamma ((n:ℝ)+3/2) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  refine ⟨fun k => ‖c k‖ * B (k+d), ?_, fun k w hw => ?_⟩
  · refine summable_of_ratio_norm_eventually_le (r := 1/2) (by norm_num) ?_
    filter_upwards [hc, eventually_ge_atTop ⌈C * |R|⌉₊] with k hk hk2
    have hk3 : C * |R| ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk2)
    have e : (k+1)+d = (k+d)+1 := by ring
    simp only [norm_mul, norm_norm, Real.norm_of_nonneg (hB0 _), e]
    rw [hB]; simp only
    rw [sphSeries_bound_step_one]
    set m : ℕ := k+d
    have hm : (k:ℝ) ≤ m := by simp only [m]; push_cast; linarith [(d.cast_nonneg : (0:ℝ) ≤ d)]
    have hq : C * (|R| / (2*(m+3/2))) ≤ 1/2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
    have hb := hB0 m
    simp only [hB] at hb
    calc ‖c (k+1)‖ * (Real.sqrt π * |R|^m / 2^(m+1) * (Real.exp (|R|^2/4) /
          Real.Gamma (m+3/2)) * (|R| / (2*(m+3/2))))
        ≤ (C * ‖c k‖) * (Real.sqrt π * |R|^m / 2^(m+1) * (Real.exp (|R|^2/4) /
          Real.Gamma (m+3/2)) * (|R| / (2*(m+3/2)))) := by gcongr
      _ = (C * (|R| / (2*(m+3/2)))) * (‖c k‖ * (Real.sqrt π * |R|^m / 2^(m+1) *
          (Real.exp (|R|^2/4) / Real.Gamma (m+3/2)))) := by ring
      _ ≤ 1/2 * (‖c k‖ * (Real.sqrt π * |R|^m / 2^(m+1) *
          (Real.exp (|R|^2/4) / Real.Gamma (m+3/2)))) := by gcongr
  · rw [norm_mul]
    show ‖c k‖ * _ ≤ ‖c k‖ * B (k+d)
    gcongr
    refine (sphSeries_norm_sphericalI_le _ w).trans ?_
    have hw' : ‖w‖ ≤ |R| := hw.le.trans (le_abs_self R)
    have : 0 < Real.Gamma (((k+d : ℕ) : ℝ) + 3/2) := Real.Gamma_pos_of_pos (by positivity)
    simp only [hB]
    gcongr

/-- `c_k i_{k+d}(w) → 0` when `‖c_{k+1}‖ ≤ C ‖c_k‖` eventually. -/
theorem sphSeries_tendsto_coeff_mul_sphericalI (c : ℕ → ℂ) {C : ℝ}
    (hc : ∀ᶠ k in atTop, ‖c (k+1)‖ ≤ C * ‖c k‖) (d : ℕ) (w : ℂ) :
    Tendsto (fun k => c k * sphericalI (k+d) w) atTop (𝓝 0) := by
  obtain ⟨u, hu, h⟩ := sphSeries_bound_coeff_mul_sphericalI c hc d (‖w‖+1)
  exact squeeze_zero_norm (fun k => h k w (by linarith)) hu.tendsto_atTop_zero

end DLMF
