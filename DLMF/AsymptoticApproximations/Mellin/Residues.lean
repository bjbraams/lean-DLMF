/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Residues at simple and double poles

Residues in the sense of `DLMF.AlgebraicAnalytic.residueAt` (DLMF §1.10(iii)) at poles of
order at most two, computed by the Cauchy integral formula for the first derivative. These are
the residue computations behind the Mellin-transform examples of DLMF §2.5, where the factor
`π/sin(πz)` (or its square) produces poles at the integers.

## Main results

* `residueAt_eq_deriv_of_eq_div_sq`: if `f(z) = g(z)/(z - z₀)²` near `z₀`, `z ≠ z₀`, with `g`
  holomorphic, then `Res_{z₀} f = g'(z₀)`.
* `residueAt_eq_of_eq_div`: if `f(z) = g(z)/(z - z₀)` near `z₀`, then `Res_{z₀} f = g(z₀)`.
* `residueAt_mul_pi_div_sin_sq_add`: at an integer `n`,
  `Res_{z=n} [u(z) (π/sin(πz))² + v(z)/(z - n)] = u'(n) + v(n)` for `u`, `v` holomorphic near `n`.
-/

@[expose] public noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace DLMF.AsymptoticApproximations

/-- If the Laurent coefficient `a_{-1}` on all small circles equals `c`, the residue is `c`. -/
private lemma residueAt_eq_of_forall_laurentCoeff {f : ℂ → ℂ} {z₀ c : ℂ} {R : ℝ} (hR : 0 < R)
    (h : ∀ r ∈ Ioo 0 R, DLMF.AlgebraicAnalytic.laurentCoeff f z₀ r (-1) = c) :
    DLMF.AlgebraicAnalytic.residueAt f z₀ = c := by
  unfold DLMF.AlgebraicAnalytic.residueAt
  exact Tendsto.limUnder_eq (tendsto_nhds_of_eventually_eq (by
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr using h r hr))

/-- Residue at a pole of order at most two: if `f(z) = g(z)/(z - z₀)²` for `0 < |z - z₀| < R`
and `g` is holomorphic on `|z - z₀| < R`, then `Res_{z₀} f = g'(z₀)`. -/
theorem residueAt_eq_deriv_of_eq_div_sq {f g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball z₀ R))
    (hfg : ∀ z ∈ ball z₀ R, z ≠ z₀ → f z = g z / (z - z₀) ^ 2) :
    DLMF.AlgebraicAnalytic.residueAt f z₀ = deriv g z₀ := by
  refine residueAt_eq_of_forall_laurentCoeff hR fun r hr => ?_
  have hc := (hg.mono (closedBall_subset_ball hr.2)).deriv_eq_smul_circleIntegral hr.1
  rw [DLMF.AlgebraicAnalytic.laurentCoeff, show -(-1 : ℤ) - 1 = 0 by norm_num]
  simp only [zpow_zero, mul_one]
  have hcongr : (∮ z in C(z₀, r), f z) = ∮ z in C(z₀, r), (1 / (z - z₀) ^ 2) • g z := by
    refine circleIntegral.integral_congr hr.1.le fun z hz => ?_
    have hz0 : z ≠ z₀ := by
      rintro rfl
      rw [mem_sphere, dist_self] at hz
      exact hr.1.ne hz
    rw [hfg z (sphere_subset_closedBall.trans (closedBall_subset_ball hr.2) hz) hz0,
      smul_eq_mul]
    ring
  rw [hcongr, hc, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

/-- Residue at a pole of order at most one: if `f(z) = g(z)/(z - z₀)` for `0 < |z - z₀| < R`
and `g` is holomorphic on `|z - z₀| < R`, then `Res_{z₀} f = g(z₀)`. -/
theorem residueAt_eq_of_eq_div {f g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball z₀ R))
    (hfg : ∀ z ∈ ball z₀ R, z ≠ z₀ → f z = g z / (z - z₀)) :
    DLMF.AlgebraicAnalytic.residueAt f z₀ = g z₀ := by
  have hd : DifferentiableOn ℂ (fun z => (z - z₀) * g z) (ball z₀ R) :=
    ((differentiableOn_id.sub_const z₀).mul hg)
  rw [residueAt_eq_deriv_of_eq_div_sq hR hd fun z hz hz0 => by
    rw [hfg z hz hz0]
    have : z - z₀ ≠ 0 := sub_ne_zero.2 hz0
    field_simp]
  have hga : DifferentiableAt ℂ g z₀ := hg.differentiableAt (ball_mem_nhds z₀ hR)
  have : HasDerivAt (fun z => (z - z₀) * g z) (1 * g z₀ + (z₀ - z₀) * deriv g z₀) z₀ :=
    ((hasDerivAt_id' z₀).sub_const z₀).mul hga.hasDerivAt
  rw [this.deriv]
  simp

/-- The entire function `w ↦ sin(πw)/w`, with value `π` at `w = 0`. -/
private def sincPi : ℂ → ℂ := dslope (fun w => Complex.sin (π * w)) 0

/-- `w ↦ sin(πw)/w` is entire. -/
private lemma sincPi_differentiable : Differentiable ℂ sincPi := by
  intro w
  have h : DifferentiableOn ℂ (dslope (fun w => Complex.sin (π * w)) 0) univ :=
    (differentiableOn_dslope univ_mem).2
      ((Complex.differentiable_sin.comp (differentiable_id.const_mul _)).differentiableOn)
  exact h.differentiableAt univ_mem

/-- Off the origin, `sincPi w = sin(πw)/w`. -/
private lemma sincPi_of_ne {w : ℂ} (hw : w ≠ 0) : sincPi w = Complex.sin (π * w) / w := by
  rw [sincPi, dslope_of_ne _ hw, slope_def_field]
  simp

/-- The value `sincPi 0 = π`. -/
private lemma sincPi_zero : sincPi 0 = π := by
  rw [sincPi, dslope_same]
  have : HasDerivAt (fun w => Complex.sin (π * w)) (Complex.cos (π * 0) * (π * 1)) 0 :=
    (Complex.hasDerivAt_sin _).comp (0 : ℂ) ((hasDerivAt_id' (0 : ℂ)).const_mul (π : ℂ))
  rw [this.deriv]
  simp

/-- `sincPi` has no zeros in the unit disc. -/
private lemma sincPi_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : sincPi w ≠ 0 := by
  by_cases h0 : w = 0
  · rw [h0, sincPi_zero]; exact ofReal_ne_zero.2 Real.pi_ne_zero
  rw [sincPi_of_ne h0]
  refine div_ne_zero (fun hs => ?_) h0
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 hs
  have hwk : w = k := by
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    apply mul_left_cancel₀ hπ
    rw [hk]; ring
  have hk0 : k ≠ 0 := by rintro rfl; simp at hwk; exact h0 hwk
  have : (1 : ℝ) ≤ ‖w‖ := by
    rw [hwk, norm_intCast]
    exact_mod_cast Int.one_le_abs hk0
  linarith

/-- `sincPi` is even. -/
private lemma sincPi_neg (w : ℂ) : sincPi (-w) = sincPi w := by
  by_cases h0 : w = 0
  · rw [h0, neg_zero]
  rw [sincPi_of_ne (neg_ne_zero.2 h0), sincPi_of_ne h0, mul_neg, Complex.sin_neg, neg_div_neg_eq]

/-- `φ(w) = (πw/sin(πw))²`, holomorphic on `|w| < 1` with `φ(0) = 1`. -/
private def piDivSincSq (w : ℂ) : ℂ := ((π : ℂ) / sincPi w) ^ 2

/-- `(πw/sin(πw))²` is holomorphic on the unit disc. -/
private lemma piDivSincSq_differentiableOn : DifferentiableOn ℂ piDivSincSq (ball 0 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa using hw
  exact ((differentiableAt_const _).div (sincPi_differentiable w)
    (sincPi_ne_zero hw')).pow 2 |>.differentiableWithinAt

/-- The value `(πw/sin(πw))² = 1` at `w = 0`. -/
private lemma piDivSincSq_zero : piDivSincSq 0 = 1 := by
  rw [piDivSincSq, sincPi_zero, div_self (ofReal_ne_zero.2 Real.pi_ne_zero), one_pow]

/-- The even function `(πw/sin(πw))²` has derivative `0` at `w = 0`. -/
private lemma deriv_piDivSincSq_zero : deriv piDivSincSq 0 = 0 := by
  have he : (fun w => piDivSincSq (-w)) = piDivSincSq := by
    funext w; rw [piDivSincSq, piDivSincSq, sincPi_neg]
  have h := deriv_comp_neg (f := piDivSincSq) (x := (0 : ℂ))
  rw [he, neg_zero] at h
  have : (2 : ℂ) * deriv piDivSincSq 0 = 0 := by linear_combination h
  simpa using this

/-- `sin²(πz)` is invariant under integer translation. -/
private lemma sin_sq_sub_int (z : ℂ) (n : ℤ) :
    Complex.sin (π * (z - n)) ^ 2 = Complex.sin (π * z) ^ 2 := by
  have hs : Complex.sin (n * π) = 0 := Complex.sin_eq_zero_iff.2 ⟨n, rfl⟩
  have hc : Complex.cos (n * π) ^ 2 = 1 := by
    have := Complex.sin_sq_add_cos_sq ((n : ℂ) * π)
    rw [hs] at this; linear_combination this
  rw [show (π : ℂ) * (z - n) = π * z - n * π by ring, Complex.sin_sub, hs]
  linear_combination (Complex.sin (π * z)) ^ 2 * hc

/-- Residues at the integer poles of `(π/sin(πz))²`: if `u` and `v` are holomorphic on
`|z - n| < R`, then `Res_{z=n} [u(z) (π/sin(πz))² + v(z)/(z - n)] = u'(n) + v(n)`. -/
theorem residueAt_mul_pi_div_sin_sq_add {f u v : ℂ → ℂ} {n : ℤ} {R : ℝ} (hR : 0 < R)
    (hu : DifferentiableOn ℂ u (ball (n : ℂ) R)) (hv : DifferentiableOn ℂ v (ball (n : ℂ) R))
    (hf : ∀ z ∈ ball (n : ℂ) R, z ≠ n →
      f z = u z * ((π : ℂ) / Complex.sin (π * z)) ^ 2 + v z / (z - n)) :
    DLMF.AlgebraicAnalytic.residueAt f n = deriv u n + v n := by
  set R' := min R 1 with hR'
  have hR'0 : 0 < R' := lt_min hR one_pos
  have hsub : ball (n : ℂ) R' ⊆ ball (n : ℂ) R := ball_subset_ball (min_le_left _ _)
  set g : ℂ → ℂ := fun z => u z * piDivSincSq (z - n) + (z - n) * v z with hg
  have hφ : ∀ z ∈ ball (n : ℂ) R', DifferentiableAt ℂ (fun z => piDivSincSq (z - n)) z := by
    intro z hz
    have hz' : z - n ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right, ← dist_eq_norm]
      exact lt_of_lt_of_le hz (min_le_right _ _)
    exact (piDivSincSq_differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz')).comp z
      ((hasDerivAt_id z).sub_const (n : ℂ)).differentiableAt
  have hgd : DifferentiableOn ℂ g (ball (n : ℂ) R') := by
    intro z hz
    have hzu := (hu.mono hsub).differentiableAt (isOpen_ball.mem_nhds hz)
    have hzv := (hv.mono hsub).differentiableAt (isOpen_ball.mem_nhds hz)
    exact ((hzu.mul (hφ z hz)).add ((differentiableAt_id.sub_const _).mul hzv))
      |>.differentiableWithinAt
  rw [residueAt_eq_deriv_of_eq_div_sq hR'0 hgd fun z hz hzn => by
    rw [hf z (hsub hz) hzn]
    have hw : z - n ≠ 0 := sub_ne_zero.2 hzn
    have hw1 : ‖z - n‖ < 1 := by
      rw [← dist_eq_norm]; exact lt_of_lt_of_le hz (min_le_right _ _)
    have hsn := sincPi_ne_zero hw1
    rw [sincPi_of_ne hw] at hsn
    have hs0 : Complex.sin (π * (z - n)) ≠ 0 := fun h => hsn (by rw [h, zero_div])
    have hsz : Complex.sin (π * z) ^ 2 ≠ 0 := by
      rw [← sin_sq_sub_int z n]; exact pow_ne_zero 2 hs0
    simp only [g, piDivSincSq, sincPi_of_ne hw, div_pow]
    rw [← sin_sq_sub_int z n] at hsz ⊢
    field_simp]
  have hn : (n : ℂ) ∈ ball (n : ℂ) R' := mem_ball_self hR'0
  have hun := (hu.mono hsub).differentiableAt (isOpen_ball.mem_nhds hn)
  have hvn := (hv.mono hsub).differentiableAt (isOpen_ball.mem_nhds hn)
  have hφn : HasDerivAt (fun z => piDivSincSq (z - n)) 0 n := by
    have := (piDivSincSq_differentiableOn.differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self one_pos))).hasDerivAt
    rw [deriv_piDivSincSq_zero] at this
    have h0 : HasDerivAt piDivSincSq 0 ((n : ℂ) - n) := by rwa [sub_self]
    exact h0.comp_sub_const (n : ℂ) (n : ℂ)
  have hd : HasDerivAt g (deriv u n * piDivSincSq ((n : ℂ) - n) + u n * 0 +
      (1 * v n + ((n : ℂ) - n) * deriv v n)) n :=
    (hun.hasDerivAt.mul hφn).add
      (((hasDerivAt_id' (n : ℂ)).sub_const (n : ℂ)).mul hvn.hasDerivAt)
  rw [hd.deriv]
  simp [piDivSincSq_zero]

end DLMF.AsymptoticApproximations
