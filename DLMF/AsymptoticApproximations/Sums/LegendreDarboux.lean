/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Sums.Basic
public import DLMF.Gamma.Asymptotics.ShiftedStirling
public import DLMF.OrthogonalPolynomials.Series
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The two algebraic singularities of the Legendre generating function

The generating function for `P_n(cos alpha)` factors into two principal inverse square
roots on the unit disk. Subtracting the leading term at each boundary singularity gives
Darboux's comparison function. The local derivative estimates follow the construction
in Olver, *Asymptotics and Special Functions*, Chapter 8, sections 9–10, pp.310–313.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Real Topology Nat

namespace DLMF.AsymptoticApproximations.LegendreDarboux

/-- A principal inverse square root with its singularity on the unit circle. -/
def squareRootFactor (alpha : ℝ) (z : ℂ) : ℂ :=
  (1 - z * exp (I * alpha)) ^ (-1 / 2 : ℂ)

/-- The product of the two normalized square-root factors of the Legendre generator. -/
def generatingFunction (alpha : ℝ) (z : ℂ) : ℂ :=
  squareRootFactor alpha z * squareRootFactor (-alpha) z

/-- The phase defining either algebraic singularity has unit norm. -/
theorem norm_phase (alpha : ℝ) : ‖exp (I * alpha)‖ = 1 := by
  rw [mul_comm I]
  exact norm_exp_ofReal_mul_I alpha

/-- The linear factor lies in the right half-plane in the open unit disk. -/
theorem re_linearFactor_pos (alpha : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    0 < (1 - z * exp (I * alpha)).re := by
  have h := (re_le_norm (z * exp (I * alpha))).trans_lt (by
    simpa only [norm_mul, norm_phase, mul_one] using hz)
  simp only [sub_re, one_re]
  linarith

/-- The linear factor remains in the slit plane on the closed disk away from its root. -/
theorem linearFactor_mem_slitPlane (alpha : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hne : z ≠ exp (-(I * alpha))) : 1 - z * exp (I * alpha) ∈ slitPlane := by
  have hw : 1 - z * exp (I * alpha) ≠ 0 := by
    intro h
    apply hne
    have he : exp (I * alpha) ≠ 0 := exp_ne_zero _
    rw [exp_neg]
    have hm : z * exp (I * alpha) = 1 := by linear_combination -h
    simpa only [one_div] using (eq_div_iff he).mpr hm
  have hr : 0 ≤ (1 - z * exp (I * alpha)).re := by
    have h := (re_le_norm (z * exp (I * alpha))).trans (by
      simpa only [norm_mul, norm_phase, mul_one] using hz)
    simp only [sub_re, one_re]
    linarith
  by_cases hi : (1 - z * exp (I * alpha)).im = 0
  · exact Or.inl (lt_of_le_of_ne hr (fun h => hw (Complex.ext h.symm hi)))
  · exact Or.inr hi

/-- Each square-root factor is analytic on the closed disk away from its singularity. -/
theorem analyticAt_squareRootFactor (alpha : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hne : z ≠ exp (-(I * alpha))) : AnalyticAt ℂ (squareRootFactor alpha) z :=
  (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).cpow analyticAt_const
    (linearFactor_mem_slitPlane alpha hz hne)

/-- Differentiating the inverse square root increases the algebraic singularity by one. -/
theorem hasDerivAt_squareRootFactor (alpha : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hne : z ≠ exp (-(I * alpha))) :
    HasDerivAt (squareRootFactor alpha)
      (exp (I * alpha) / 2 * (1 - z * exp (I * alpha)) ^ (-3 / 2 : ℂ)) z := by
  have h := ((hasDerivAt_id z).mul_const (exp (I * alpha))).const_sub 1
  convert h.cpow_const (c := (-1 / 2 : ℂ))
    (linearFactor_mem_slitPlane alpha hz hne) using 1
  · funext w; rfl
  · norm_num
    ring

/-- The two factors give the principal Legendre generating function in the unit disk. -/
theorem generatingFunction_eq (alpha : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    generatingFunction alpha z =
      (1 - 2 * (Real.cos alpha : ℂ) * z + z ^ 2) ^ (-1 / 2 : ℂ) := by
  let A : ℂ := 1 - z * exp (I * alpha)
  let B : ℂ := 1 - z * exp (I * (-alpha : ℝ))
  have hA : 0 < A.re := re_linearFactor_pos alpha hz
  have hB : 0 < B.re := re_linearFactor_pos (-alpha) hz
  have hA0 : A ≠ 0 := by intro h; simp [h] at hA
  have hB0 : B ≠ 0 := by intro h; simp [h] at hB
  have ha := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA))
  have hb := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hB))
  have hlog := Complex.log_mul hA0 hB0 (show arg A + arg B ∈ Ioc (-π) π from
    ⟨by linarith [ha.1, hb.1], by linarith [ha.2, hb.2]⟩)
  have he : exp (I * alpha) + exp (I * (-alpha : ℝ)) = 2 * (Real.cos alpha : ℂ) := by
    have H := (Complex.two_cos (alpha : ℂ)).symm
    rw [← Complex.ofReal_cos] at H
    convert H using 1 <;> push_cast <;> ring
  have hi : exp (I * alpha) * exp (I * (-alpha : ℝ)) = 1 := by
    rw [← exp_add]
    convert exp_zero using 1 <;> push_cast <;> ring
  have hp : A * B = 1 - 2 * (Real.cos alpha : ℂ) * z + z ^ 2 := by
    calc A * B = 1 - z * (exp (I * alpha) + exp (I * (-alpha : ℝ))) +
        z ^ 2 * (exp (I * alpha) * exp (I * (-alpha : ℝ))) := by dsimp [A, B]; ring
      _ = _ := by rw [he, hi]; ring
  change A ^ (-1 / 2 : ℂ) * B ^ (-1 / 2 : ℂ) = _
  rw [← hp, cpow_def_of_ne_zero hA0, cpow_def_of_ne_zero hB0,
    cpow_def_of_ne_zero (mul_ne_zero hA0 hB0), hlog, add_mul, exp_add]

/-- The Taylor coefficients of the factored generator are Legendre polynomials. -/
theorem hasSum_generatingFunction (alpha : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos alpha) * z ^ n)
      (generatingFunction alpha z) := by
  rw [generatingFunction_eq alpha hz]
  exact DLMF.OrthogonalPolynomials.legendre_generating_function (Real.abs_cos_le_one alpha) hz

/-- The factored generator is analytic on the closed disk except at its two roots. -/
theorem analyticAt_generatingFunction (alpha : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hneg : z ≠ exp (-(I * alpha))) (hpos : z ≠ exp (I * alpha)) :
    AnalyticAt ℂ (generatingFunction alpha) z := by
  apply (analyticAt_squareRootFactor alpha hz hneg).mul
  apply analyticAt_squareRootFactor (-alpha) hz
  simpa only [ofReal_neg, mul_neg, neg_neg] using hpos

/-- The distance to the root is the norm of the normalized linear factor. -/
theorem norm_linearFactor (alpha : ℝ) (z : ℂ) :
    ‖1 - z * exp (I * alpha)‖ = ‖z - exp (-(I * alpha))‖ := by
  have h : (z - exp (-(I * alpha))) * exp (I * alpha) =
      -(1 - z * exp (I * alpha)) := by
    rw [sub_mul, exp_neg, inv_mul_cancel₀ (exp_ne_zero _)]
    ring
  have H := congrArg norm h
  simpa only [norm_mul, norm_phase, mul_one, norm_neg] using H.symm

/-- The two boundary roots are distinct for an interior real angle. -/
theorem phase_ne_neg_phase {alpha : ℝ} (ha : alpha ∈ Ioo 0 π) :
    exp (I * alpha) ≠ exp (-(I * alpha)) := by
  intro he
  have H := congrArg im he
  have hs := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  simp only [exp_im, mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul,
    zero_add, mul_re, zero_mul, sub_self, Real.exp_zero, neg_im, neg_re, Real.sin_neg,
    neg_zero, Real.exp_zero, one_mul] at H
  linarith

/-- The nonsingular factor evaluated at the opposite root gives the leading phase. -/
theorem squareRootFactor_neg_root {alpha : ℝ} (ha : alpha ∈ Ioo 0 π) :
    squareRootFactor (-alpha) (exp (-(I * alpha))) =
      (((2 * Real.sin alpha) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        exp (-(π * I / 4) + I * alpha / 2) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have he : 1 - exp (-(I * alpha)) * exp (I * (-alpha : ℝ)) =
      ((2 * Real.sin alpha : ℝ) : ℂ) * exp (I * (π / 2 - alpha)) := by
    have ht := Complex.two_sin (alpha : ℂ)
    rw [← ofReal_sin] at ht
    have hei : exp (I * (π / 2 - alpha)) = I * exp (-(I * alpha)) := by
      rw [mul_sub, exp_sub, exp_neg]
      have hi : exp (I * ((π : ℂ) / 2)) = I := by
        convert exp_pi_div_two_mul_I using 1 <;> push_cast <;> ring
      rw [hi, div_eq_mul_inv]
    rw [hei]
    have hp : exp (I * alpha) * exp (-(I * alpha)) = 1 := by
      rw [← exp_add, add_neg_cancel, exp_zero]
    have hm : exp (I * (-alpha : ℝ)) = exp (-(I * alpha)) := by
      congr 1; push_cast; ring
    have ht' : (2 * Real.sin alpha : ℝ) =
        (exp (-(I * alpha)) - exp (I * alpha)) * I := by
      have h₁ : -(alpha : ℂ) * I = -(I * alpha) := by ring
      have h₂ : (alpha : ℂ) * I = I * alpha := by ring
      rw [h₁, h₂] at ht
      simpa only [ofReal_mul, ofReal_ofNat] using ht
    rw [hm, ht', ← hp]
    ring_nf
    simp only [I_sq]
    ring
  have hc : (((2 * Real.sin alpha) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      ((2 * Real.sin alpha : ℝ) : ℂ) ^ (-1 / 2 : ℂ) := by
    convert ofReal_cpow (by positivity : 0 ≤ 2 * Real.sin alpha) (-1 / 2 : ℝ) using 1 <;>
      norm_num
  unfold squareRootFactor
  rw [he, TauCeti.ofReal_mul_cpow (by positivity), ← hc,
    cpow_def_of_ne_zero (exp_ne_zero _)]
  have hlog : log (exp (I * (π / 2 - alpha))) = I * (π / 2 - alpha) := by
    apply log_exp <;> norm_num [mul_im, mul_re] <;> linarith [Real.pi_pos, ha.1, ha.2]
  rw [hlog]
  congr 2
  push_cast
  ring

/-- The conjugate root gives the conjugate leading phase. -/
theorem squareRootFactor_pos_root {alpha : ℝ} (ha : alpha ∈ Ioo 0 π) :
    squareRootFactor alpha (exp (I * alpha)) =
      (((2 * Real.sin alpha) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        exp (π * I / 4 - I * alpha / 2) := by
  have he : starRingEnd ℂ (exp (-(I * alpha))) = exp (I * alpha) := by
    rw [← exp_conj]
    congr 1
    simp
  have hslit : 1 - exp (-(I * alpha)) * exp (I * (-alpha : ℝ)) ∈ slitPlane := by
    apply linearFactor_mem_slitPlane (-alpha)
    · rw [norm_exp]; norm_num [mul_re]
    · simpa only [ofReal_neg, mul_neg, neg_neg] using (phase_ne_neg_phase ha).symm
  have H := conj_cpow (1 - exp (-(I * alpha)) * exp (I * (-alpha : ℝ)))
    (-1 / 2 : ℂ) (slitPlane_arg_ne_pi hslit)
  have hc : starRingEnd ℂ (squareRootFactor (-alpha) (exp (-(I * alpha)))) =
      squareRootFactor alpha (exp (I * alpha)) := by
    unfold squareRootFactor
    convert H.symm using 1 <;>
      simp only [map_sub, map_one, map_mul, he, ← exp_conj, map_neg, conj_I, conj_ofReal,
        ofReal_neg, neg_mul, mul_neg, neg_neg, map_div₀, map_ofNat]
  rw [← hc, squareRootFactor_neg_root ha, map_mul, conj_ofReal, ← exp_conj]
  congr 2
  simp only [map_add, map_neg, map_div₀, map_mul, conj_ofReal, conj_I, map_ofNat]
  ring

/-- Darboux's comparison function subtracts the leading part at each of the two roots. -/
theorem legendreComparison_eq {alpha : ℝ} (ha : alpha ∈ Ioo 0 π) (z : ℂ) :
    legendreComparison alpha z =
      squareRootFactor (-alpha) (exp (-(I * alpha))) * squareRootFactor alpha z +
      squareRootFactor alpha (exp (I * alpha)) * squareRootFactor (-alpha) z := by
  rw [squareRootFactor_neg_root ha, squareRootFactor_pos_root ha]
  simp only [legendreComparison, squareRootFactor, ofReal_neg, mul_neg, sub_eq_add_neg,
    exp_add]
  ring

/-- The leading Taylor constants at the two simple linear factors define a comparison
without choosing polar phases. -/
def rootComparison (alpha : ℝ) (z : ℂ) : ℂ :=
  squareRootFactor (-alpha) (exp (-(I * alpha))) * squareRootFactor alpha z +
    squareRootFactor alpha (exp (I * alpha)) * squareRootFactor (-alpha) z

/-- The phase-normalized and root-evaluation forms of the comparison agree. -/
theorem legendreComparison_eq_rootComparison {alpha : ℝ} (ha : alpha ∈ Ioo 0 π) :
    legendreComparison alpha = rootComparison alpha := by
  funext z
  exact legendreComparison_eq ha z

/-- Exchanging the roots leaves the factored generating function unchanged. -/
theorem generatingFunction_neg (alpha : ℝ) : generatingFunction (-alpha) =
    generatingFunction alpha := by
  funext z
  simp only [generatingFunction, neg_neg, mul_comm]

/-- Exchanging the roots leaves the comparison unchanged. -/
theorem rootComparison_neg (alpha : ℝ) : rootComparison (-alpha) =
    rootComparison alpha := by
  funext z
  simp only [rootComparison, neg_neg, ofReal_neg, mul_neg, neg_neg]
  ring

/-- The norm of either inverse square root is the inverse square root of the root distance. -/
theorem norm_squareRootFactor (alpha : ℝ) (z : ℂ) :
    ‖squareRootFactor alpha z‖ = ‖z - exp (-(I * alpha))‖ ^ (-(1 / 2) : ℝ) := by
  calc
    ‖squareRootFactor alpha z‖ = ‖1 - z * exp (I * alpha)‖ ^ (-(1 / 2) : ℝ) := by
      unfold squareRootFactor
      convert norm_cpow_real (1 - z * exp (I * alpha)) (-(1 / 2) : ℝ) using 1 <;> norm_num
    _ = _ := by rw [norm_linearFactor]

/-- The derivative of either inverse square root has a distance power of order `-3/2`. -/
theorem norm_deriv_squareRootFactor (alpha : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hne : z ≠ exp (-(I * alpha))) :
    ‖deriv (squareRootFactor alpha) z‖ =
      (1 / 2 : ℝ) * ‖z - exp (-(I * alpha))‖ ^ (-(3 / 2) : ℝ) := by
  rw [(hasDerivAt_squareRootFactor alpha hz hne).deriv, norm_mul, norm_div,
    norm_phase, norm_ofNat]
  congr 1
  calc
    ‖(1 - z * exp (I * alpha)) ^ (-3 / 2 : ℂ)‖ =
        ‖1 - z * exp (I * alpha)‖ ^ (-(3 / 2) : ℝ) := by
      convert norm_cpow_real (1 - z * exp (I * alpha)) (-(3 / 2) : ℝ) using 1 <;> norm_num
    _ = _ := by rw [norm_linearFactor]

/-- Removing the leading term at a square-root singularity leaves an integrable derivative.
The subtraction at the other root contributes an analytic term locally. -/
theorem isBigO_deriv_sub_rootComparison (alpha : ℝ)
    (hroots : exp (-(I * alpha)) ≠ exp (I * alpha)) :
    deriv (generatingFunction alpha - rootComparison alpha)
      =O[𝓝[puncturedDisc 1] (exp (-(I * alpha)))]
        fun z => ‖z - exp (-(I * alpha))‖ ^ (-(1 / 2) : ℝ) := by
  let w := exp (-(I * alpha))
  have hw : ‖w‖ = 1 := by rw [show w = exp (I * (-alpha : ℝ)) by
    dsimp only [w]; rw [ofReal_neg, mul_neg]]; exact norm_phase _
  have hBw : AnalyticAt ℂ (squareRootFactor (-alpha)) w := by
    apply analyticAt_squareRootFactor (-alpha) hw.le
    simpa only [ofReal_neg, mul_neg, neg_neg] using hroots
  obtain ⟨C, hC, hb⟩ := hBw.differentiableAt.hasDerivAt.isBigO_sub.exists_pos
  obtain ⟨D, hD, hd⟩ := (hBw.deriv.continuousAt.tendsto.isBigO_one ℝ).exists_pos
  let K := squareRootFactor alpha (exp (I * alpha))
  refine IsBigO.of_bound (C / 2 + D * (1 + ‖K‖)) ?_
  have hnear : ∀ᶠ z in 𝓝[puncturedDisc 1] w, ‖z - w‖ < 1 := by
    have h : ∀ᶠ z in 𝓝 w, ‖z - w‖ < 1 := by
      filter_upwards [Metric.ball_mem_nhds w (by norm_num : (0 : ℝ) < 1)] with z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact hz
    exact h.filter_mono nhdsWithin_le_nhds
  filter_upwards [hb.bound.filter_mono nhdsWithin_le_nhds,
    hd.bound.filter_mono nhdsWithin_le_nhds, hnear, self_mem_nhdsWithin] with z hB hD' hn hz
  have hz1 : ‖z‖ < 1 := hz.2
  have hzw : z ≠ w := by intro he; rw [he, hw] at hz1; exact lt_irrefl 1 hz1
  have hzr : z ≠ exp (I * alpha) := by
    intro he
    rw [he, norm_phase] at hz1
    exact lt_irrefl 1 hz1
  have hA := hasDerivAt_squareRootFactor alpha hz1.le hzw
  have hB' := hasDerivAt_squareRootFactor (-alpha) hz1.le
    (by simpa only [ofReal_neg, mul_neg, neg_neg] using hzr)
  have H := (hA.mul hB').sub
    ((hA.const_mul (squareRootFactor (-alpha) w)).add (hB'.const_mul K))
  have heq : deriv (generatingFunction alpha - rootComparison alpha) z =
      deriv (squareRootFactor alpha) z *
          (squareRootFactor (-alpha) z - squareRootFactor (-alpha) w) +
        deriv (squareRootFactor (-alpha)) z * (squareRootFactor alpha z - K) := by
    rw [show deriv (generatingFunction alpha - rootComparison alpha) z = _ from H.deriv]
    rw [hA.deriv, hB'.deriv]
    ring
  have hdpos : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hunit : 1 ≤ ‖z - w‖ ^ (-(1 / 2) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdpos hn.le (by norm_num)
  have hrpow : ‖z - w‖ ^ (-(3 / 2) : ℝ) * ‖z - w‖ =
      ‖z - w‖ ^ (-(1 / 2) : ℝ) := by
    nth_rw 2 [← Real.rpow_one ‖z - w‖]
    rw [← Real.rpow_add hdpos]
    norm_num
  simp only [Real.norm_eq_abs, abs_one, mul_one] at hD'
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), heq]
  calc
    ‖deriv (squareRootFactor alpha) z *
          (squareRootFactor (-alpha) z - squareRootFactor (-alpha) w) +
        deriv (squareRootFactor (-alpha)) z * (squareRootFactor alpha z - K)‖ ≤
        ‖deriv (squareRootFactor alpha) z‖ *
          ‖squareRootFactor (-alpha) z - squareRootFactor (-alpha) w‖ +
        ‖deriv (squareRootFactor (-alpha)) z‖ * (‖squareRootFactor alpha z‖ + ‖K‖) := by
      exact (norm_add_le _ _).trans (by
        rw [norm_mul, norm_mul]
        gcongr
        exact norm_sub_le _ _)
    _ ≤ ((1 / 2) * ‖z - w‖ ^ (-(3 / 2) : ℝ)) * (C * ‖z - w‖) +
        D * (‖z - w‖ ^ (-(1 / 2) : ℝ) + ‖K‖) := by
      rw [norm_deriv_squareRootFactor alpha hz1.le hzw, norm_squareRootFactor]
      exact add_le_add (mul_le_mul_of_nonneg_left hB (by positivity))
        (mul_le_mul_of_nonneg_right hD' (by positivity))
    _ ≤ (C / 2 + D * (1 + ‖K‖)) * ‖z - w‖ ^ (-(1 / 2) : ℝ) := by
      have hm : ‖K‖ ≤ ‖K‖ * ‖z - w‖ ^ (-(1 / 2) : ℝ) :=
        le_mul_of_one_le_right (norm_nonneg _) hunit
      calc
        _ = C / 2 * (‖z - w‖ ^ (-(3 / 2) : ℝ) * ‖z - w‖) +
            D * (‖z - w‖ ^ (-(1 / 2) : ℝ) + ‖K‖) := by ring
        _ ≤ C / 2 * ‖z - w‖ ^ (-(1 / 2) : ℝ) +
            D * (‖z - w‖ ^ (-(1 / 2) : ℝ) +
              ‖K‖ * ‖z - w‖ ^ (-(1 / 2) : ℝ)) := by rw [hrpow]; gcongr
        _ = _ := by ring

/-- The derivative estimate also holds at the conjugate root. -/
theorem isBigO_deriv_sub_rootComparison_pos (alpha : ℝ)
    (hroots : exp (-(I * alpha)) ≠ exp (I * alpha)) :
    deriv (generatingFunction alpha - rootComparison alpha)
      =O[𝓝[puncturedDisc 1] (exp (I * alpha))]
        fun z => ‖z - exp (I * alpha)‖ ^ (-(1 / 2) : ℝ) := by
  have h := isBigO_deriv_sub_rootComparison (-alpha)
    (by simpa only [ofReal_neg, mul_neg, neg_neg] using hroots.symm)
  simpa only [generatingFunction_neg, rootComparison_neg, ofReal_neg, mul_neg, neg_neg] using h

/-- The comparison is analytic on the closed disk away from the two roots. -/
theorem analyticAt_rootComparison (alpha : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hneg : z ≠ exp (-(I * alpha))) (hpos : z ≠ exp (I * alpha)) :
    AnalyticAt ℂ (rootComparison alpha) z := by
  exact (analyticAt_const.mul (analyticAt_squareRootFactor alpha hz hneg)).add
    (analyticAt_const.mul (analyticAt_squareRootFactor (-alpha) hz
      (by simpa only [ofReal_neg, mul_neg, neg_neg] using hpos)))

/-- The first Gamma-ratio remainder vanishes after multiplication by the degree. -/
theorem tendsto_nat_mul_gammaRatio_error :
    Tendsto (fun n : ℕ => (n : ℝ) * ‖Gamma ((n : ℂ) + 1 / 2) /
      Gamma ((n : ℂ) + 1) - (n : ℂ) ^ (-(1 / 2) : ℂ)‖) atTop (𝓝 0) := by
  have H := (DLMF.Gamma.Gamma_ratio_expansion (1 / 2) 1 1).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  norm_num [DLMF.Gamma.stirlingRatioG_zero, Function.comp_def] at H
  have HB : (fun n : ℕ => Gamma ((n : ℂ) + 1 / 2) / Gamma ((n : ℂ) + 1) -
      (n : ℂ) ^ (-(1 / 2) : ℂ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ) := by
    refine H.norm_right.congr_right fun n => ?_
    change ‖(n : ℂ) ^ (-(3 / 2) : ℂ)‖ = (n : ℝ) ^ (-(3 / 2) : ℝ)
    convert norm_cpow_real (n : ℂ) (-(3 / 2) : ℝ) using 1 <;> simp
  obtain ⟨C, hC⟩ := HB.exists_pos
  have hlim : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hlim
  filter_upwards [hC.2.bound, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn0
  have he : (n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ) = (n : ℝ) ^ (-(1 / 2) : ℝ) := by
    nth_rw 1 [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hnp]
    norm_num
  have hb := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnp.le _)] at hb
  calc (n : ℝ) * ‖_‖ ≤ (n : ℝ) * (C * (n : ℝ) ^ (-(3 / 2) : ℝ)) := hb
    _ = C * (n : ℝ) ^ (-(1 / 2) : ℝ) := by rw [mul_left_comm, he]

end DLMF.AsymptoticApproximations.LegendreDarboux
