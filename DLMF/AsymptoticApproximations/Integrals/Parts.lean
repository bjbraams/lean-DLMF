/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Basics.Basic
public import DLMF.AsymptoticApproximations.Integrals.Watson
public import DLMF.AlgebraicAnalytic.Transforms.Laplace
public import DLMFMathlib.Analysis.Integral.RepeatedIntegrationByParts
public import DLMFMathlib.Analysis.SpecificLimits.Oscillation
public import DLMFMathlib.Analysis.Asymptotics.ExponentialGrowth
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Integration by parts (DLMF §2.3(i))

* 2.3.2: the Laplace transform of a function smooth at the origin has the expansion
  `∑ q^{(s)}(0)/x^{s+1}`; proved from the general Watson lemma of
  `DLMF.AsymptoticApproximations.Integrals.Watson` and Taylor's theorem.
* 2.3.3: the error bound `|q^{(n)}(0)/(xⁿ(x - σₙ))|`, from a common exponential
  bound for the lower derivatives and the iterated Laplace derivative identity.
* 2.3.4–2.3.6: Fourier integrals over finite and infinite intervals, with the error bound
  `x⁻ⁿ 𝒱_{a,b}(q^{(n-1)})` in terms of the variational operator 2.3.6. Repeated
  integration by parts gives exact remainders. In the improper case convergence at
  two frequencies forces the boundary terms to vanish.

Smoothness "in a neighbourhood of the origin" is smoothness on some `[0, r]`, `r > 0` (only
`t ≥ 0` enters the Laplace transform), with one-sided derivatives `iteratedDerivWithin`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology Real ContDiff Nat

namespace DLMF.AsymptoticApproximations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- DLMF 2.3.2: if the Laplace transform 2.3.1 converges for large `x` (here `e^{-ct} q(t)` is
integrable on `(0, ∞)`) and `q` is infinitely differentiable on `[0, r]`, `r > 0`, then
`∫₀^∞ e^{-xt} q(t) dt ∼ ∑ q^{(s)}(0)/x^{s+1}` as `x → +∞` (one-sided derivatives at `0`). -/
@[dlmf 2.3.E2]
theorem laplace_hasAsymptoticExpansion_of_contDiffOn {q : ℝ → E} {c r : ℝ} (hr : 0 < r)
    (hq : ContDiffOn ℝ ∞ q (Icc 0 r))
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • q t) (Ioi 0)) :
    HasAsymptoticExpansion atTop (fun (s : ℕ) (x : ℝ) => x ^ (-((s : ℝ) + 1)))
      (fun s => iteratedDerivWithin s q (Icc 0 r) 0)
      (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • q t) := by
  set d : ℕ → E := fun s => iteratedDerivWithin s q (Icc 0 r) 0 with hd
  have hmem : Ioo (0 : ℝ) r ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hr
  have hT : ∀ N : ℕ, (fun t => q t - ∑ n ∈ range N, t ^ (((n : ℝ) + 1) - 1) •
      (((n ! : ℝ)⁻¹) • d n)) =O[𝓝[>] 0] fun t => t ^ (((N : ℝ) + 1) - 1) := by
    intro N
    rcases N with _ | n
    · obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hq.continuousOn
      refine IsBigO.of_bound C ?_
      filter_upwards [hmem] with t ht
      simpa using hC t (Ioo_subset_Icc_self ht)
    · have hcont : ContinuousOn (iteratedDerivWithin (n + 1) q (Icc 0 r)) (Icc 0 r) :=
        hq.continuousOn_iteratedDerivWithin (mod_cast le_top) (uniqueDiffOn_Icc hr)
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      refine IsBigO.of_bound (C / n !) ?_
      filter_upwards [hmem] with t ht
      have ht' : t ∈ Icc 0 r := Ioo_subset_Icc_self ht
      have hb := taylor_mean_remainder_bound hr.le (hq.of_le (mod_cast le_top)) ht' hC
      have heq : taylorWithinEval q n (Icc 0 r) 0 t = ∑ k ∈ range (n + 1),
          t ^ (((k : ℝ) + 1) - 1) • (((k ! : ℝ)⁻¹) • d k) := by
        rw [taylor_within_apply]
        refine sum_congr rfl fun k _ => ?_
        rw [smul_smul, add_sub_cancel_right, Real.rpow_natCast, sub_zero, mul_comm]
      rw [← heq]
      have h0 : 0 ≤ t := ht'.1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _), Nat.cast_add, Nat.cast_one,
        add_sub_cancel_right, ← Nat.cast_succ, Real.rpow_natCast]
      calc _ ≤ C * (t - 0) ^ (n + 1) / n ! := hb
        _ = C / n ! * t ^ (n + 1) := by rw [sub_zero]; ring
  have h := hasAsymptoticExpansion_integral_exp_smul_rpow_seq (e := fun s => (s : ℝ) + 1)
    (a := fun s => ((s ! : ℝ)⁻¹) • d s) (fun n => by positivity) hint hT
  refine h.congr_coeff (funext fun s => ?_)
  rw [smul_smul, Real.Gamma_nat_eq_factorial, mul_inv_cancel₀ (by positivity), one_smul]

/-- An exponential bound on one derivative supplies a common, slightly larger
exponential rate for all lower derivatives on the nonnegative half-line. -/
private theorem laplace_derivatives_exp_bound {q : ℝ → ℂ} {n : ℕ} {σ α : ℝ}
    (hq : ContDiffOn ℝ ∞ q (Ici 0)) (hα : 0 < α) (hσα : σ ≤ α)
    (hσ : ∀ t ≥ 0, ‖iteratedDerivWithin n q (Ici 0) t‖ ≤
      ‖iteratedDerivWithin n q (Ici 0) 0‖ * Real.exp (σ * t)) :
    ∀ k ≤ n, DLMF.AlgebraicAnalytic.IsOfExponentialGrowth
      (iteratedDerivWithin k q (Ici 0)) α := by
  have hc (k : ℕ) : ContinuousOn (iteratedDerivWithin k q (Ici 0)) (Ici 0) :=
    hq.continuousOn_iteratedDerivWithin (mod_cast le_top) (uniqueDiffOn_Ici 0)
  have hd (k : ℕ) (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
      HasDerivWithinAt (iteratedDerivWithin k q (Ici 0))
        (iteratedDerivWithin (k + 1) q (Ici 0) t) (Ici 0) t := by
    rw [iteratedDerivWithin_succ]
    exact (hq.differentiableOn_iteratedDerivWithin
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) (uniqueDiffOn_Ici 0) t ht).hasDerivWithinAt
  have hbase : ∃ M ≥ 0, ∀ t ≥ 0, ‖iteratedDerivWithin n q (Ici 0) t‖ ≤ M * Real.exp (α * t) := by
    refine ⟨‖iteratedDerivWithin n q (Ici 0) 0‖, norm_nonneg _, fun t ht => ?_⟩
    exact (hσ t ht).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσα ht)) (norm_nonneg _))
  have hdown : ∀ j : ℕ, ∀ k : ℕ, k + j = n → ∃ M ≥ 0,
      ∀ t ≥ 0, ‖iteratedDerivWithin k q (Ici 0) t‖ ≤ M * Real.exp (α * t) := by
    intro j
    induction j with
    | zero => intro k hk; simp only [Nat.add_zero] at hk; subst k; exact hbase
    | succ j ih =>
      intro k hk
      obtain ⟨M, hM, hb⟩ := ih (k + 1) (by omega)
      refine ⟨‖iteratedDerivWithin k q (Ici 0) 0‖ + M / α, by positivity, fun t ht => ?_⟩
      exact norm_le_mul_exp_of_hasDerivWithinAt hα hM (hc k) (hc (k + 1)) (hd k) hb ht
  intro k hk
  obtain ⟨M, _, hb⟩ := hdown (n - k) k (by omega)
  exact ⟨M, hb⟩

/-- DLMF 2.3.3 and the bound after it: let `q` be infinitely differentiable on `[0, ∞)` with
`q^{(n)}(0) ≠ 0`, and let `σ` bound `t⁻¹ ln|q^{(n)}(t)/q^{(n)}(0)|` on `(0, ∞)`, that is,
`|q^{(n)}(t)| ≤ |q^{(n)}(0)| e^{σt}` (DLMF's `σₙ` of 2.3.3 is the least such `σ`). Then for
`x > max(0, σ)` the `n`th error term of 2.3.2 is bounded by `|q^{(n)}(0)/(xⁿ(x - σ))|`. -/
@[dlmf 2.3.E3, dlmf 2.3.i]
theorem laplace_error_bound {q : ℝ → ℂ} {n : ℕ} {σ x : ℝ} (hq : ContDiffOn ℝ ∞ q (Ici 0))
    (hn : iteratedDerivWithin n q (Ici 0) 0 ≠ 0)
    (hσ : ∀ t, 0 < t →
      ‖iteratedDerivWithin n q (Ici 0) t‖ ≤ ‖iteratedDerivWithin n q (Ici 0) 0‖ * Real.exp (σ * t))
    (hx0 : 0 < x) (hxσ : σ < x) :
    ‖(∫ t in Ioi (0 : ℝ), Complex.exp (-(x * t)) * q t) -
        ∑ s ∈ range n, iteratedDerivWithin s q (Ici 0) 0 / (x : ℂ) ^ (s + 1)‖ ≤
      ‖iteratedDerivWithin n q (Ici 0) 0‖ / (x ^ n * (x - σ)) := by
  clear hn
  have hx : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have hσ' : ∀ t ≥ 0, ‖iteratedDerivWithin n q (Ici 0) t‖ ≤
      ‖iteratedDerivWithin n q (Ici 0) 0‖ * Real.exp (σ * t) := by
    intro t ht
    rcases eq_or_lt_of_le ht with rfl | ht
    · simp
    · exact hσ t ht
  let α := (max σ 0 + x) / 2
  have hα : 0 < α := by dsimp [α]; positivity
  have hσα : σ ≤ α := by dsimp [α]; linarith [le_max_left σ 0]
  have hαx : α < x := by dsimp [α]; linarith [max_lt_iff.mpr ⟨hxσ, hx0⟩]
  have hg := laplace_derivatives_exp_bound hq hα hσα hσ'
  have hc (k : ℕ) : ContinuousOn (iteratedDerivWithin k q (Ici 0)) (Ici 0) :=
    hq.continuousOn_iteratedDerivWithin (mod_cast le_top) (uniqueDiffOn_Ici 0)
  have h := DLMF.AlgebraicAnalytic.laplaceTransform_iteratedDeriv
    (fun k _ => hc k) (fun k _ t ht => by
      rw [iteratedDerivWithin_succ]
      exact (hq.differentiableOn_iteratedDerivWithin
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
        (uniqueDiffOn_Ici 0) t ht.le).hasDerivWithinAt.hasDerivAt
          (Ici_mem_nhds ht)) ((hc n).locallyIntegrableOn measurableSet_Ici) hg
    (s := (x : ℂ)) (by simpa using hαx)
  have hsum : ∑ k ∈ range n, (x : ℂ) ^ (n - 1 - k) * iteratedDerivWithin k q (Ici 0) 0 =
      (x : ℂ) ^ n * ∑ k ∈ range n, iteratedDerivWithin k q (Ici 0) 0 / (x : ℂ) ^ (k + 1) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    have he : n - 1 - k = n - (k + 1) := by omega
    rw [he, pow_sub₀ (x : ℂ) hx (by have := mem_range.mp hk; omega)]
    ring
  rw [hsum, iteratedDerivWithin_zero] at h
  have he : (∫ t in Ioi (0 : ℝ), Complex.exp (-(x * t)) * q t) -
      ∑ k ∈ range n, iteratedDerivWithin k q (Ici 0) 0 / (x : ℂ) ^ (k + 1) =
      DLMF.AlgebraicAnalytic.laplaceTransform (iteratedDerivWithin n q (Ici 0)) x /
        (x : ℂ) ^ n := by
    apply (eq_div_iff (pow_ne_zero n hx)).mpr
    unfold DLMF.AlgebraicAnalytic.laplaceTransform at h ⊢
    simp only [neg_mul] at h ⊢
    linear_combination -h
  rw [he, norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have hb := DLMF.AlgebraicAnalytic.norm_laplaceTransform_le hσ'
    (s := (x : ℂ)) (by simpa using hxσ)
  calc _ ≤ (‖iteratedDerivWithin n q (Ici 0) 0‖ / (x - σ)) / x ^ n :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by rw [div_div, mul_comm (x - σ) (x ^ n)]

/-- Repeated integration by parts for the finite Fourier integral, with an exact
remainder involving the next one-sided derivative. -/
private theorem fourier_eq_sum_add_remainder {q : ℝ → ℂ} {a b x : ℝ} (hab : a < b)
    (hq : ContDiffOn ℝ ∞ q (Icc a b)) (hx : x ≠ 0) (n : ℕ) :
    (∫ t in a..b, Complex.exp (I * x * t) * q t) = ∑ s ∈ range n,
      (Complex.exp (I * a * x) * iteratedDerivWithin s q (Icc a b) a -
        Complex.exp (I * b * x) * iteratedDerivWithin s q (Icc a b) b) * (I / x) ^ (s + 1) +
      (I / x) ^ n * ∫ t in a..b,
        Complex.exp (I * x * t) * iteratedDerivWithin n q (Icc a b) t := by
  have hz : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx)
  have hi : -(I * (x : ℂ))⁻¹ = I / x := by
    field_simp
    simp [I_sq, div_eq_mul_inv]
  have h := intervalIntegral.integral_cexp_mul_eq_sum_add hab.le hz
    (fun k => iteratedDerivWithin k q (Icc a b)) n
    (fun k _ => hq.continuousOn_iteratedDerivWithin (mod_cast le_top) (uniqueDiffOn_Icc hab))
    (fun k _ t ht => by
      rw [iteratedDerivWithin_succ]
      exact (hq.differentiableOn_iteratedDerivWithin (by exact_mod_cast WithTop.coe_lt_top k)
        (uniqueDiffOn_Icc hab) t ht).hasDerivWithinAt)
  rw [hi, iteratedDerivWithin_zero] at h
  convert h using 1
  congr 1
  apply sum_congr rfl
  intro k _
  rw [pow_succ]
  have ha : I * (a : ℂ) * x = I * x * a := by ring
  have hb : I * (b : ℂ) * x = I * x * b := by ring
  rw [ha, hb]
  rw [← hi]
  ring

/-- The modulus of the finite Fourier remainder is bounded by the integral of the
modulus of its highest derivative. -/
private theorem norm_fourier_remainder_le {q : ℝ → ℂ} {a b x : ℝ} (hab : a < b)
    (hq : ContDiffOn ℝ ∞ q (Icc a b)) (hx : 0 < x) (n : ℕ) :
    ‖(∫ t in a..b, Complex.exp (I * x * t) * q t) - ∑ s ∈ range n,
      (Complex.exp (I * a * x) * iteratedDerivWithin s q (Icc a b) a -
        Complex.exp (I * b * x) * iteratedDerivWithin s q (Icc a b) b) * (I / x) ^ (s + 1)‖ ≤
      x⁻¹ ^ n * ∫ t in a..b, ‖iteratedDerivWithin n q (Icc a b) t‖ := by
  rw [fourier_eq_sum_add_remainder hab hq hx.ne' n, add_sub_cancel_left, norm_mul,
    norm_pow, norm_div, norm_I, norm_real, Real.norm_eq_abs, abs_of_pos hx, one_div]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (intervalIntegral.norm_integral_le_integral_norm hab.le).trans_eq ?_
  apply intervalIntegral.integral_congr
  intro t _
  simp [Complex.norm_exp]

/-- DLMF 2.3.4 (finite Fourier integral): if `q` is infinitely differentiable on `[a, b]`, then
`∫ₐᵇ e^{ixt} q(t) dt ∼ e^{iax} ∑ q^{(s)}(a)(i/x)^{s+1} - e^{ibx} ∑ q^{(s)}(b)(i/x)^{s+1}` as
`x → +∞`, a generalized asymptotic expansion with respect to the scale `x^{-s-1}`
(one-sided derivatives at the endpoints). -/
@[dlmf 2.3.E4]
theorem fourier_hasGeneralizedAsymptoticExpansion {q : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hq : ContDiffOn ℝ ∞ q (Icc a b)) :
    HasGeneralizedAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + 1)))
      (fun s x => (Complex.exp (I * a * x) * iteratedDerivWithin s q (Icc a b) a -
        Complex.exp (I * b * x) * iteratedDerivWithin s q (Icc a b) b) * (I / x) ^ (s + 1))
      (fun x => ∫ t in a..b, Complex.exp (I * x * t) * q t) := by
  have hp (n : ℕ) (x : ℝ) : (x : ℂ) ^ (-((n : ℂ) + 1)) = (x : ℂ)⁻¹ ^ (n + 1) := by
    rw [← Nat.cast_add_one, Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
  constructor
  · intro n
    have ht : Tendsto (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    have h := (isLittleO_pow_pow (𝕜 := ℂ) (Nat.lt_succ_self (n + 1))).comp_tendsto ht
    simpa only [Function.comp_def, ofReal_inv, hp, Nat.succ_eq_add_one] using h
  · intro n
    let D := fun k => iteratedDerivWithin k q (Icc a b)
    let C := ‖D n a‖ + ‖D n b‖ + ∫ t in a..b, ‖D (n + 1) t‖
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    let B := fun k => (Complex.exp (I * a * x) * D k a -
      Complex.exp (I * b * x) * D k b) * (I / x) ^ (k + 1)
    have he := fourier_eq_sum_add_remainder hab hq hx.ne' (n + 1)
    change (∫ t in a..b, Complex.exp (I * x * t) * q t) =
      ∑ k ∈ range (n + 1), B k + _ at he
    rw [sum_range_succ] at he
    have hbn : ‖B n‖ ≤ (‖D n a‖ + ‖D n b‖) * x⁻¹ ^ (n + 1) := by
      dsimp [B]
      rw [norm_mul, norm_pow, norm_div, norm_I, norm_real, Real.norm_eq_abs,
        abs_of_pos hx, one_div]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa [Complex.norm_exp] using norm_sub_le
        (Complex.exp (I * a * x) * D n a) (Complex.exp (I * b * x) * D n b)
    have hr : ‖(I / (x : ℂ)) ^ (n + 1) * ∫ t in a..b,
        Complex.exp (I * x * t) * D (n + 1) t‖ ≤
        x⁻¹ ^ (n + 1) * ∫ t in a..b, ‖D (n + 1) t‖ := by
      rw [norm_mul, norm_pow, norm_div, norm_I, norm_real, Real.norm_eq_abs,
        abs_of_pos hx, one_div]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (intervalIntegral.norm_integral_le_integral_norm hab.le).trans_eq ?_
      apply intervalIntegral.integral_congr
      intro t _
      simp [Complex.norm_exp]
    rw [he, add_assoc, add_sub_cancel_left, hp, norm_pow, norm_inv, norm_real,
      Real.norm_eq_abs, abs_of_pos hx]
    calc _ ≤ ‖B n‖ + ‖(I / (x : ℂ)) ^ (n + 1) * ∫ t in a..b,
          Complex.exp (I * x * t) * D (n + 1) t‖ := norm_add_le _ _
      _ ≤ (‖D n a‖ + ‖D n b‖) * x⁻¹ ^ (n + 1) +
          x⁻¹ ^ (n + 1) * ∫ t in a..b, ‖D (n + 1) t‖ := add_le_add hbn hr
      _ = _ := by dsimp [C]; ring

/-- DLMF 2.3.4 with the error bound after 2.3.6: for `n ≥ 1` and `x > 0` the `n`th error term
of 2.3.4 is bounded in absolute value by `x⁻ⁿ 𝒱_{a,b}(q^{(n-1)})`, with the variational operator
2.3.6. -/
@[dlmf 2.3.E4, dlmf 2.3.E6, dlmf 2.3.i]
theorem fourier_error_bound {q : ℝ → ℂ} {a b x : ℝ} {n : ℕ} (hab : a < b)
    (hq : ContDiffOn ℝ ∞ q (Icc a b)) (hn : 1 ≤ n) (hx : 0 < x) :
    ‖(∫ t in a..b, Complex.exp (I * x * t) * q t) - ∑ s ∈ range n,
        (Complex.exp (I * a * x) * iteratedDerivWithin s q (Icc a b) a -
          Complex.exp (I * b * x) * iteratedDerivWithin s q (Icc a b) b) * (I / x) ^ (s + 1)‖ ≤
      x ^ (-(n : ℤ)) * variationalOperator a b (iteratedDerivWithin (n - 1) q (Icc a b)) := by
  have hv : variationalOperator a b (iteratedDerivWithin (n - 1) q (Icc a b)) =
      ∫ t in a..b, ‖iteratedDerivWithin n q (Icc a b) t‖ := by
    unfold variationalOperator
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro t ht
    have hD := (hq.differentiableOn_iteratedDerivWithin
      (m := n - 1) (ENat.natCast_lt_of_coe_top_le_withTop le_rfl (n - 1)) (uniqueDiffOn_Icc hab) t
      (Ioo_subset_Icc_self ht)).hasDerivWithinAt.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    dsimp only
    rw [hD.deriv, ← iteratedDerivWithin_succ, Nat.sub_add_cancel hn]
  rw [hv, zpow_neg, zpow_natCast, ← inv_pow]
  exact norm_fourier_remainder_le hab hq hx n

/-- One integration by parts determines the limiting boundary phase from two
successive oscillatory integrals. -/
private theorem fourier_boundary_limit {q : ℝ → ℂ} {a x₀ : ℝ}
    (hq : ContDiffOn ℝ ∞ q (Ici a)) {L : ℕ → ℝ → ℂ}
    (hlim : ∀ s : ℕ, ∀ x ≥ x₀, Tendsto (fun T : ℝ =>
      ∫ t in a..T, Complex.exp (I * x * t) * iteratedDerivWithin s q (Ici a) t)
      atTop (𝓝 (L s x))) (s : ℕ) {x : ℝ} (hx₀ : x₀ ≤ x) (hx : x ≠ 0) :
    Tendsto (fun T : ℝ => Complex.exp (I * x * T) * iteratedDerivWithin s q (Ici a) T)
      atTop (𝓝 (Complex.exp (I * x * a) * iteratedDerivWithin s q (Ici a) a +
        (I * x) * L s x + L (s + 1) x)) := by
  have ht := ((tendsto_const_nhds
    (x := Complex.exp (I * x * a) * iteratedDerivWithin s q (Ici a) a)).add
      ((hlim s x hx₀).const_mul (I * (x : ℂ)))).add
    (hlim (s + 1) x hx₀)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop a] with T hT
  have hcont (k : ℕ) : ContinuousOn (iteratedDerivWithin k q (Ici a)) (Icc a T) :=
    (hq.continuousOn_iteratedDerivWithin (mod_cast le_top) (uniqueDiffOn_Ici a)).mono
      Icc_subset_Ici_self
  have hd (t : ℝ) (ht : t ∈ Icc a T) : HasDerivWithinAt (iteratedDerivWithin s q (Ici a))
      (iteratedDerivWithin (s + 1) q (Ici a) t) (Icc a T) t := by
    rw [iteratedDerivWithin_succ]
    exact (hq.differentiableOn_iteratedDerivWithin
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl s)
      (uniqueDiffOn_Ici a) t ht.1).hasDerivWithinAt.mono
      Icc_subset_Ici_self
  have hz : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx)
  have h := intervalIntegral.integral_cexp_mul_eq_boundary_sub hT.le hz (hcont s)
    (hcont (s + 1)) hd
  field_simp [ofReal_ne_zero.mpr hx] at h
  linear_combination h

/-- Convergence at two frequencies forces the boundary phase to tend to zero. -/
private theorem fourier_boundary_tendsto_zero {q : ℝ → ℂ} {a x₀ : ℝ}
    (hq : ContDiffOn ℝ ∞ q (Ici a)) {L : ℕ → ℝ → ℂ}
    (hlim : ∀ s : ℕ, ∀ x ≥ x₀, Tendsto (fun T : ℝ =>
      ∫ t in a..T, Complex.exp (I * x * t) * iteratedDerivWithin s q (Ici a) t)
      atTop (𝓝 (L s x))) (s : ℕ) {x : ℝ} (hx₀ : x₀ ≤ x) (hx : 0 < x) :
    Tendsto (fun T : ℝ => Complex.exp (I * x * T) * iteratedDerivWithin s q (Ici a) T)
      atTop (𝓝 0) := by
  have hA := fourier_boundary_limit hq hlim s hx₀ hx.ne'
  have hB := fourier_boundary_limit hq hlim s
    (x := x + Real.pi) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have he : (fun T : ℝ => (Complex.exp (I * x * T) * iteratedDerivWithin s q (Ici a) T) *
      Complex.exp (Real.pi * I * T)) = fun T : ℝ =>
      Complex.exp (I * (x + Real.pi) * T) * iteratedDerivWithin s q (Ici a) T := by
    funext T
    rw [mul_right_comm, ← Complex.exp_add]
    congr 2
    ring
  have h0 := Complex.eq_zero_of_tendsto_mul_exp_pi_I hA (by simpa only [he, ofReal_add] using hB)
  rwa [h0] at hA

/-- Repeated integration by parts for an improper Fourier integral, after its
boundary terms have been shown to vanish. -/
private theorem fourier_Ioi_eq_sum_add_remainder {q : ℝ → ℂ} {a x₀ : ℝ}
    (hq : ContDiffOn ℝ ∞ q (Ici a)) {L : ℕ → ℝ → ℂ}
    (hlim : ∀ s : ℕ, ∀ x ≥ x₀, Tendsto (fun T : ℝ =>
      ∫ t in a..T, Complex.exp (I * x * t) * iteratedDerivWithin s q (Ici a) t)
      atTop (𝓝 (L s x))) {x : ℝ} (hx₀ : x₀ ≤ x) (hx : 0 < x) (n : ℕ) :
    L 0 x = ∑ s ∈ range n, Complex.exp (I * a * x) * iteratedDerivWithin s q (Ici a) a *
      (I / x) ^ (s + 1) + (I / x) ^ n * L n x := by
  have hz : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have hInv : -(I * (x : ℂ))⁻¹ = I / x := by field_simp; simp [I_sq, div_eq_mul_inv]
  have hfin : ∀ᶠ T : ℝ in atTop,
      (∫ t in a..T, Complex.exp (I * x * t) * q t) =
      ∑ s ∈ range n, (Complex.exp (I * a * x) * iteratedDerivWithin s q (Ici a) a -
        Complex.exp (I * x * T) * iteratedDerivWithin s q (Ici a) T) * (I / x) ^ (s + 1) +
      (I / x) ^ n * ∫ t in a..T, Complex.exp (I * x * t) * iteratedDerivWithin n q (Ici a) t := by
    filter_upwards [eventually_gt_atTop a] with T hT
    have h := intervalIntegral.integral_cexp_mul_eq_sum_add hT.le hz
      (fun k => iteratedDerivWithin k q (Ici a)) n
      (fun k _ => (hq.continuousOn_iteratedDerivWithin (mod_cast le_top)
        (uniqueDiffOn_Ici a)).mono Icc_subset_Ici_self)
      (fun k _ t ht => by
        rw [iteratedDerivWithin_succ]
        exact (hq.differentiableOn_iteratedDerivWithin
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
          (uniqueDiffOn_Ici a) t ht.1).hasDerivWithinAt.mono
            Icc_subset_Ici_self)
    rw [iteratedDerivWithin_zero, hInv] at h
    convert h using 1
    congr 1
    apply sum_congr rfl
    intro k _
    rw [pow_succ, show I * (a : ℂ) * x = I * x * a by ring, ← hInv]
    ring
  have hsum : Tendsto (fun T : ℝ => ∑ s ∈ range n,
      (Complex.exp (I * a * x) * iteratedDerivWithin s q (Ici a) a -
        Complex.exp (I * x * T) * iteratedDerivWithin s q (Ici a) T) * (I / x) ^ (s + 1))
      atTop (𝓝 (∑ s ∈ range n, Complex.exp (I * a * x) * iteratedDerivWithin s q (Ici a) a *
        (I / x) ^ (s + 1))) := by
    apply tendsto_finsetSum
    intro k _
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub (fourier_boundary_tendsto_zero hq hlim k hx₀ hx)).mul_const
        ((I / (x : ℂ)) ^ (k + 1))
  have hr := hsum.add ((hlim n x hx₀).const_mul ((I / (x : ℂ)) ^ n))
  have hl := hlim 0 x hx₀
  simp only [iteratedDerivWithin_zero] at hl
  exact tendsto_nhds_unique hl (hr.congr' (hfin.mono fun T hT => hT.symm))

/-- Uniform convergence on a frequency half-line transfers the finite-interval
Riemann–Lebesgue limit to the improper Fourier integral. -/
private theorem tendsto_zero_of_uniform_fourier_Ioi {q : ℝ → ℂ} {a x₀ : ℝ} {L : ℝ → ℂ}
    (hunif : TendstoUniformlyOn (fun (T x : ℝ) => ∫ t in a..T,
      Complex.exp (I * x * t) * q t) L atTop (Ici x₀)) : Tendsto L atTop (𝓝 0) := by
  have hu := hunif.tendstoUniformlyOnFilter.mono_right
    (show (atTop : Filter ℝ) ≤ 𝓟 (Ici x₀) from le_principal_iff.mpr (eventually_ge_atTop x₀))
  refine hu.tendsto_of_eventually_tendsto ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop a] with T hT
  let g : ℝ → ℂ := (Ioc a T).indicator q
  have h := ((DLMF.AlgebraicAnalytic.tendsto_fourierTransform_cocompact g).mono_left
    atTop_le_cocompact).const_mul (Real.sqrt (2 * Real.pi) : ℂ)
  simp only [mul_zero] at h
  refine h.congr fun x => ?_
  unfold DLMF.AlgebraicAnalytic.fourierTransform
  have he : (fun t : ℝ => g t * Complex.exp (I * x * t)) =
      (Ioc a T).indicator (fun t => Complex.exp (I * x * t) * q t) := by
    ext t
    by_cases ht : t ∈ Ioc a T <;> simp [g, ht, mul_comm]
  rw [he, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hT, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'), one_mul]

/-- DLMF 2.3.5 (infinite Fourier integral): if `q` is infinitely differentiable on `[a, ∞)` and
each integral `∫ₐ^∞ e^{ixt} q^{(s)}(t) dt` converges (as `lim_{T→∞} ∫ₐᵀ`) uniformly for
`x ≥ x₀`, then the improper integral `I(x) = ∫ₐ^∞ e^{ixt} q(t) dt` satisfies
`I(x) ∼ e^{iax} ∑ q^{(s)}(a)(i/x)^{s+1}` as `x → +∞` (generalized expansion, scale `x^{-s-1}`),
and for `n ≥ 1`, `x ≥ max(x₀, 0)`, `x > 0`, the `n`th error term is at most
`x⁻ⁿ ∫ₐ^∞ |q^{(n)}(t)| dt` (`= x⁻ⁿ 𝒱_{a,∞}(q^{(n-1)})`) when that integral is finite. -/
@[dlmf 2.3.E5, dlmf 2.3.i]
theorem fourier_Ioi_hasGeneralizedAsymptoticExpansion {q : ℝ → ℂ} {a x₀ : ℝ}
    (hq : ContDiffOn ℝ ∞ q (Ici a)) {I₀ : ℝ → ℂ} {L : ℕ → ℝ → ℂ}
    (hunif : ∀ s : ℕ, TendstoUniformlyOn (fun (T x : ℝ) =>
      ∫ t in a..T, Complex.exp (I * x * t) * iteratedDerivWithin s q (Ici a) t) (L s) atTop
      (Ici x₀))
    (hI : ∀ x, x₀ ≤ x → I₀ x = L 0 x) :
    HasGeneralizedAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + 1)))
      (fun s x => Complex.exp (I * a * x) * iteratedDerivWithin s q (Ici a) a * (I / x) ^ (s + 1))
      I₀ ∧
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, x₀ ≤ x → 0 < x →
      IntegrableOn (iteratedDerivWithin n q (Ici a)) (Ioi a) →
      ‖I₀ x - ∑ s ∈ range n,
          Complex.exp (I * a * x) * iteratedDerivWithin s q (Ici a) a * (I / x) ^ (s + 1)‖ ≤
        x ^ (-(n : ℤ)) * ∫ t in Ioi a, ‖iteratedDerivWithin n q (Ici a) t‖ := by
  have hlim : ∀ s : ℕ, ∀ x ≥ x₀, Tendsto (fun T : ℝ =>
      ∫ t in a..T, Complex.exp (I * x * t) * iteratedDerivWithin s q (Ici a) t)
      atTop (𝓝 (L s x)) := fun s x hx => (hunif s).tendsto_at hx
  have hp (n : ℕ) (x : ℝ) : (x : ℂ) ^ (-((n : ℂ) + 1)) = (x : ℂ)⁻¹ ^ (n + 1) := by
    rw [← Nat.cast_add_one, Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
  constructor
  · constructor
    · intro n
      have ht : Tendsto (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) :=
        (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
      have h := (isLittleO_pow_pow (𝕜 := ℂ) (Nat.lt_succ_self (n + 1))).comp_tendsto ht
      simpa only [Function.comp_def, ofReal_inv, hp, Nat.succ_eq_add_one] using h
    · intro n
      let C := ‖iteratedDerivWithin n q (Ici a) a‖ + 1
      have hL := tendsto_zero_of_uniform_fourier_Ioi (hunif (n + 1))
      have hLb : ∀ᶠ x : ℝ in atTop, ‖L (n + 1) x‖ ≤ 1 :=
        (hL.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)).mono fun x hx =>
          (by simpa [Metric.mem_ball, dist_zero_right] using hx.le)
      refine IsBigO.of_bound C ?_
      filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop x₀, hLb] with x hx hx₀ hxL
      rw [hI x hx₀, fourier_Ioi_eq_sum_add_remainder hq hlim hx₀ hx (n + 1),
        sum_range_succ, add_assoc, add_sub_cancel_left]
      rw [hp, norm_pow, norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos hx]
      have hb : ‖Complex.exp (I * a * x) * iteratedDerivWithin n q (Ici a) a *
          (I / x) ^ (n + 1)‖ = ‖iteratedDerivWithin n q (Ici a) a‖ * x⁻¹ ^ (n + 1) := by
        simp [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hx,
          Complex.norm_exp]
      have hr : ‖(I / (x : ℂ)) ^ (n + 1) * L (n + 1) x‖ ≤ x⁻¹ ^ (n + 1) := by
        rw [norm_mul, norm_pow, norm_div, norm_I, norm_real, Real.norm_eq_abs,
          abs_of_pos hx, one_div]
        exact mul_le_of_le_one_right (by positivity) hxL
      calc _ ≤ ‖Complex.exp (I * a * x) * iteratedDerivWithin n q (Ici a) a * (I / x) ^ (n + 1)‖ +
          ‖(I / (x : ℂ)) ^ (n + 1) * L (n + 1) x‖ := norm_add_le _ _
        _ ≤ ‖iteratedDerivWithin n q (Ici a) a‖ * x⁻¹ ^ (n + 1) + x⁻¹ ^ (n + 1) :=
          add_le_add hb.le hr
        _ = _ := by dsimp [C]; ring
  · intro n hn x hx₀ hx hint
    have hk : IntegrableOn (fun t : ℝ => Complex.exp (I * x * t) *
        iteratedDerivWithin n q (Ici a) t) (Ioi a) := by
      refine hint.norm.mono' ((by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (I * x * t)).aestronglyMeasurable.mul hint.aestronglyMeasurable) ?_
      exact Filter.Eventually.of_forall fun t => by simp [Complex.norm_exp]
    have hL : L n x = ∫ t in Ioi a, Complex.exp (I * x * t) * iteratedDerivWithin n q (Ici a) t :=
      tendsto_nhds_unique (hlim n x hx₀) (intervalIntegral_tendsto_integral_Ioi a hk tendsto_id)
    rw [hI x hx₀, fourier_Ioi_eq_sum_add_remainder hq hlim hx₀ hx n,
      add_sub_cancel_left, norm_mul, norm_pow, norm_div, norm_I, norm_real,
      Real.norm_eq_abs, abs_of_pos hx, one_div, zpow_neg, zpow_natCast, ← inv_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hL]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp [Complex.norm_exp]

end DLMF.AsymptoticApproximations
