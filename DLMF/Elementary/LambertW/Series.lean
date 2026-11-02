/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.LambertW.Asymptotics

/-!
# Series, asymptotic expansions and integrals of Lambert W

This file proves the Maclaurin and power series of the Lambert W function, the expansions at the
branch point `-1/e`, the large-argument and small-argument asymptotic expansions, antiderivatives
and integral representations (DLMF §4.13).

## Main definitions

* `powMulExpTaylorCoeff`: the truncated Taylor coefficients `K_j`.

## Main results

* `lambertW_hasSum`: the Maclaurin series with its exact disk of convergence (DLMF 4.13.5).
* `lambertW_power_hasSum`, `lambertW_reciprocal_hasSum`, `lambertW_square_hasSum`: series for
  powers of `W` (DLMF 4.13.5_1–4.13.5_3).
* `lambertC_hasSum`, `lambertC_real_branches`: the branch-point expansion (DLMF 4.13.6).
* `lambertC_initial`, `lambertC_recurrence`, `lambertC_stirling`: its coefficients
  (DLMF 4.13.7–4.13.9).
* `lambertW_puiseux_hasSum`, `lambertW_minus_one_puiseux_hasSum`,
  `lambertW_one_lower_puiseux_hasSum`: Puiseux series (DLMF 4.13.9_1).
* `lambertD_initial`, `lambertD_recurrence`: the Puiseux coefficients (DLMF 4.13.9_2).
* `lambertW_asymptotic`, `lambertW_asymptotic_converges`, `lambertW_asymptotic_real_converges`:
  the large-argument expansion (DLMF 4.13.10).
* `lambertW_lower_asymptotic`: the real lower branches at zero (DLMF 4.13.11).
* `lambertW_primitive`, `lambertW_div_primitive`, `sin_lambertW_primitive`: antiderivatives
  (DLMF 4.13.12–4.13.14).
* `lambertW_integral_rational`, `lambertW_integral_log`: integral representations on the
  principal slit domain (DLMF 4.13.15–4.13.16).
* `lambertW_other_norm_tendsto_zero`, `lambertW_other_logarithmic_growth`: the logarithmic
  singularity of the nonprincipal branches at zero.
-/

@[expose] public section

open Complex Filter Set Finset

open scoped Topology Real

noncomputable section

namespace DLMF.Elementary

section LambertSeries
open Metric
open scoped Nat

/-- Near the origin the principal branch is small. -/
private lemma exists_norm_lambertW_zero_lt_half : ∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → ‖lambertW 0 z‖ < 1 /
    2 := by
  have h0 : (0 : ℂ) ∈ lambertPrincipalDomain := by
    left; simp [Real.exp_pos]
  have hc := (lambertW_principal_analytic 0 h0).continuousAt
  have hW0 : lambertW 0 0 = 0 := (Classical.choice exists_lambertBranchFamily).zero 0
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have := h (x := z) (by simpa using hz)
  simpa [hW0] using this

/-- The fixed-point equation `t = z e^{-t}` has at most one root in the unit disc
when `‖z‖ e ≤ 1/2`. -/
private lemma eq_of_eq_mul_exp_neg_of_mem_closedBall {z t w : ℂ} (hz : ‖z‖ * Real.exp 1 ≤ 1 / 2)
    (ht : t ∈ closedBall (0 : ℂ) 1) (hw : w ∈ closedBall (0 : ℂ) 1)
    (h1 : t = z * Complex.exp (-t)) (h2 : w = z * Complex.exp (-w)) : t = w := by
  have hlip : ‖Complex.exp (-t) - Complex.exp (-w)‖ ≤ Real.exp 1 * ‖t - w‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun u => Complex.exp (-u))
      (f' := fun u => -Complex.exp (-u)) (fun u _ => ?_) (fun u hu => ?_) (convex_closedBall 0 1)
      hw ht
    · simpa using ((hasDerivAt_neg u).cexp).hasDerivWithinAt
    · rw [norm_neg, Complex.norm_exp, Real.exp_le_exp, neg_re]
      have := Complex.abs_re_le_norm u
      simp only [mem_closedBall, dist_zero_right] at hu
      rw [abs_le] at this; linarith
  have : ‖t - w‖ ≤ 1 / 2 * ‖t - w‖ := by
    calc ‖t - w‖ = ‖z‖ * ‖Complex.exp (-t) - Complex.exp (-w)‖ := by
          rw [← norm_mul, mul_sub, ← h1, ← h2]
      _ ≤ ‖z‖ * (Real.exp 1 * ‖t - w‖) := by gcongr
      _ = (‖z‖ * Real.exp 1) * ‖t - w‖ := by ring
      _ ≤ 1 / 2 * ‖t - w‖ := by gcongr
  have : ‖t - w‖ = 0 := by linarith [norm_nonneg (t - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Lagrange–Bürmann for the principal Lambert branch near the origin:
`F(W(z)) / (1 + W(z)) = ∑ zⁿ [tⁿ] (F(t) e^{-nt})`. -/
private lemma hasSum_lagrangeBurmann_lambertW_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    ∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ →
      HasSum (fun n : ℕ => z ^ n *
        (iteratedDeriv n (fun t => F t * Complex.exp (-t) ^ n) 0 / n.factorial))
        (F (lambertW 0 z) / (1 + lambertW 0 z)) := by
  obtain ⟨δ₁, hδ₁, hsmall⟩ := exists_norm_lambertW_zero_lt_half
  refine ⟨min δ₁ (Real.exp (-1) / 2), lt_min hδ₁ (by positivity), fun z hz => ?_⟩
  set w := lambertW 0 z with hwdef
  have hw : ‖w‖ < 1 / 2 := hsmall z (lt_of_lt_of_le hz (min_le_left _ _))
  have hze : ‖z‖ * Real.exp 1 ≤ 1 / 2 := by
    have h := lt_of_lt_of_le hz (min_le_right _ _)
    have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos 1]
  have heq : w * Complex.exp w = z := lambertW_equation 0 z (Or.inr rfl)
  have hwfix : w = z * Complex.exp (-w) := by
    rw [← heq, mul_assoc, ← Complex.exp_add]; simp
  set h : ℂ → ℂ := fun t => t - z * Complex.exp (-t) with hh
  have hhd : ∀ t, HasDerivAt h (1 + z * Complex.exp (-t)) t := by
    intro t
    have := (hasDerivAt_id' t).fun_sub (((hasDerivAt_neg t).cexp).const_mul z)
    convert this using 1; ring
  have hhw : h w = 0 := by show w - z * Complex.exp (-w) = 0; rw [← hwfix]; ring
  set g := dslope h w
  have hwball : w ∈ ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hnhds : closedBall (0 : ℂ) 1 ∈ 𝓝 w :=
    mem_of_superset (isOpen_ball.mem_nhds hwball) ball_subset_closedBall
  have hgd : DifferentiableOn ℂ g (closedBall 0 1) :=
    (Complex.differentiableOn_dslope hnhds).mpr
      (fun t _ => (hhd t).differentiableAt.differentiableWithinAt)
  have hgw : g w = 1 + w := by
    simp only [g, dslope_same, (hhd w).deriv]; rw [← hwfix]
  have hg0 : ∀ t ∈ closedBall (0 : ℂ) 1, g t ≠ 0 := by
    intro t ht
    by_cases htw : t = w
    · rw [htw, hgw]; intro h0
      have : ‖w‖ = 1 := by rw [show w = -1 by linear_combination h0]; simp
      linarith
    · intro h0
      have hs := sub_smul_dslope h w t
      rw [show dslope h w t = g t from rfl, h0, smul_zero, hhw, sub_zero] at hs
      apply htw
      refine eq_of_eq_mul_exp_neg_of_mem_closedBall hze ht (ball_subset_closedBall hwball) ?_ hwfix
      simp only [hh] at hs; linear_combination -hs
  have hfac : ∀ t ∈ sphere (0 : ℂ) 1, t - z * Complex.exp (-t) = (t - w) * g t := by
    intro t _
    have hs := sub_smul_dslope h w t
    rw [hhw, sub_zero, smul_eq_mul] at hs
    rw [hs]
  have hzΦ : ∀ t ∈ sphere (0 : ℂ) 1, ‖z * Complex.exp (-t)‖ ≤ 1 / 2 := by
    intro t ht
    rw [norm_mul, Complex.norm_exp, neg_re]
    have := Complex.abs_re_le_norm t
    simp only [mem_sphere, dist_zero_right] at ht
    rw [abs_le] at this
    calc ‖z‖ * Real.exp (-t.re) ≤ ‖z‖ * Real.exp 1 := by
          gcongr; linarith
      _ ≤ 1 / 2 := hze
  have := Complex.lagB_hasSum_iteratedDeriv (F := F) (Φ := fun t => Complex.exp (-t)) (g := g)
    (r := 1) (ρ := 1 / 2) one_pos hF.differentiableOn
    (fun t _ => ((hasDerivAt_neg t).cexp).differentiableAt.differentiableWithinAt) hgd hg0
    (by norm_num) hzΦ (by linarith) hfac
  rw [hgw] at this
  exact this

/-- Taylor coefficients of `t^j e^{ct}` at the origin. -/
private lemma iteratedDeriv_pow_mul_exp_zero (j n : ℕ) (c : ℂ) :
    iteratedDeriv n (fun t : ℂ => t ^ j * Complex.exp (c * t)) 0 =
      if j ≤ n then (n.choose j * j.factorial : ℂ) * c ^ (n - j) else 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_fun_pow_zero, iteratedDeriv_cexp_const_mul, mul_zero,
    Complex.exp_zero, mul_one]
  split_ifs with h
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · intro hj; simp at hj; omega
  · apply Finset.sum_eq_zero
    intro i hi
    simp at hi
    have : i ≠ j := by omega
    simp [this]

/-- The truncated Taylor coefficient `K_j`. -/
def powMulExpTaylorCoeff (n j : ℕ) (c : ℂ) : ℂ := if j ≤ n then (n.choose j * j.factorial : ℂ) * c ^
    (n - j) else 0

/-- Taylor coefficients of a cubic polynomial times `e^{ct}`. -/
private lemma iteratedDeriv_cubic_mul_exp_zero (α β γ δ c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℂ => (α + β * t + γ * t ^ 2 + δ * t ^ 3) * Complex.exp (c * t)) 0 =
      α * powMulExpTaylorCoeff n 0 c + β * powMulExpTaylorCoeff n 1 c + γ * powMulExpTaylorCoeff n 2
          c + δ * powMulExpTaylorCoeff n 3 c := by
  have hfun : (fun t : ℂ => (α + β * t + γ * t ^ 2 + δ * t ^ 3) * Complex.exp (c * t)) =
      fun t => ((α * (t ^ 0 * Complex.exp (c * t)) + β * (t ^ 1 * Complex.exp (c * t))) +
        γ * (t ^ 2 * Complex.exp (c * t))) + δ * (t ^ 3 * Complex.exp (c * t)) := by
    funext t; ring
  rw [hfun, iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow_mul_exp_zero, powMulExpTaylorCoeff]

/-- Rewriting `F(t) e^{-nt}` with `F(t) = q(t) e^{-at}`. -/
private lemma cubic_mul_exp_mul_exp_pow_eq (α β γ δ a : ℂ) (n : ℕ) :
    (fun t : ℂ => ((α + β * t + γ * t ^ 2 + δ * t ^ 3) * Complex.exp (-a * t)) *
      Complex.exp (-t) ^ n) =
    fun t => (α + β * t + γ * t ^ 2 + δ * t ^ 3) * Complex.exp (-(a + n) * t) := by
  funext t
  rw [← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
  congr 2; ring

/-- The open disc of radius `1/e` lies in the principal domain. -/
private lemma ball_exp_neg_one_subset_lambertPrincipalDomain : ball (0 : ℂ) (Real.exp (-1)) ⊆
    lambertPrincipalDomain := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  left
  have := Complex.abs_re_le_norm z
  rw [abs_le] at this
  linarith

/-- The principal branch is differentiable on the disc of radius `1/e`. -/
private lemma differentiableOn_lambertW_zero_ball : DifferentiableOn ℂ (lambertW 0)
    (Metric.ball 0 (Real.exp (-1))) :=
  fun z hz => (lambertW_principal_analytic z
      (ball_exp_neg_one_subset_lambertPrincipalDomain hz)).differentiableAt.differentiableWithinAt

/-- `1 + W₀(z) ≠ 0` on the disc of radius `1/e`. -/
private lemma one_add_lambertW_zero_ne_zero_of_norm_lt {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) : 1 +
    lambertW 0 z ≠ 0 :=
  one_add_lambertW_ne_zero (k := 0) (z := z) (by
    simp only [lambertBranchDomain, ↓reduceIte]; exact
        ball_exp_neg_one_subset_lambertPrincipalDomain (mem_ball_zero_iff.mpr hz))

/-- The series part of 4.13.E5_1 with the coefficients of `zⁿ`. -/
private lemma hasSum_exp_neg_mul_lambertW_zero (a : ℂ) {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => ((if n = 0 then 1 else a * (n + a) ^ (n - 1) / n.factorial) * (-1) ^ n) * z
        ^ n)
      (Complex.exp (-a * lambertW 0 z)) := by
  obtain ⟨δ, hδ, hLB⟩ := hasSum_lagrangeBurmann_lambertW_zero
      (F := fun t => (1 + 1 * t + 0 * t ^ 2 + 0 * t ^ 3) *
    Complex.exp (-a * t)) (by fun_prop)
  refine Complex.lagB_hasSum_of_differentiableOn (f := fun z => Complex.exp (-a * lambertW 0 z))
    (lt_min hδ (Real.exp_pos (-1))) ?_ (fun z hz => ?_) (by simpa using hz)
  · exact (differentiableOn_lambertW_zero_ball.const_mul _).cexp
  · rw [Metric.mem_ball, dist_zero_right] at hz
    have h := hLB z (lt_of_lt_of_le hz (min_le_left _ _))
    have h1 := one_add_lambertW_zero_ne_zero_of_norm_lt (lt_of_lt_of_le hz (min_le_right _ _))
    have hval : (1 + 1 * lambertW 0 z + 0 * lambertW 0 z ^ 2 + 0 * lambertW 0 z ^ 3) *
        Complex.exp (-a * lambertW 0 z) / (1 + lambertW 0 z) = Complex.exp (-a * lambertW 0 z) := by
      field_simp; ring
    simp only [cubic_mul_exp_mul_exp_pow_eq, iteratedDeriv_cubic_mul_exp_zero, hval] at h
    convert h using 2 with n
    rcases n with _ | m
    · simp [powMulExpTaylorCoeff]
    · simp only [powMulExpTaylorCoeff, Nat.zero_le, ↓reduceIte, Nat.choose_zero_right,
          Nat.factorial_zero,
        Nat.cast_one, one_mul, Nat.sub_zero, show 1 ≤ m + 1 by omega, Nat.choose_one_right,
        Nat.factorial_one, mul_one, zero_mul, add_zero,
        Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false]
      simp only [neg_pow (a + _)]
      push_cast
      have := Nat.factorial_ne_zero (m + 1)
      field_simp
      ring

end LambertSeries
/-- Maclaurin series with its exact open convergence disk. -/
@[dlmf 4.13.E5]
theorem lambertW_hasSum {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => (-(n + 1) : ℂ) ^ n / (n + 1).factorial * z ^ (n + 1))
      (lambertW 0 z) := by
  have h := (hasSum_exp_neg_mul_lambertW_zero 1 hz).mul_left z
  have heq : lambertW 0 z * Complex.exp (lambertW 0 z) = z := lambertW_equation 0 z (Or.inr rfl)
  have hW : z * Complex.exp (-1 * lambertW 0 z) = lambertW 0 z := by
    have h' := heq
    generalize lambertW 0 z = w at h' ⊢
    subst h'
    rw [mul_assoc, ← Complex.exp_add]; simp
  rw [hW] at h
  convert h using 1
  funext n
  rcases n with _ | m
  · simp
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
      one_mul]
    rw [neg_pow, Nat.factorial_succ]
    push_cast
    have := Nat.factorial_ne_zero m
    have h2 : (m : ℂ) + 1 + 1 ≠ 0 := by norm_cast
    field_simp
    ring

section LambertSeries
open Metric
open scoped Nat

/-- On the disc of radius `1/e` the principal branch has modulus less than one. -/
private lemma norm_lambertW_zero_lt_one {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) : ‖lambertW 0 z‖ < 1 :=
    by
  have hr : ‖(-(‖z‖ : ℂ))‖ < Real.exp (-1) := by simpa using hz
  have hs := lambertW_hasSum hr
  have hterm : ∀ n : ℕ, (-(n + 1) : ℂ) ^ n / (n + 1).factorial * (-(‖z‖ : ℂ)) ^ (n + 1) =
      -((‖(-(n + 1) : ℂ) ^ n / (n + 1).factorial * z ^ (n + 1)‖ : ℝ) : ℂ) := by
    intro n
    have hn : ‖(-(n + 1) : ℂ)‖ = (n + 1 : ℝ) := by
      rw [norm_neg, show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [norm_mul, norm_div, norm_pow, norm_pow, hn, Complex.norm_natCast]
    rw [neg_pow, neg_pow (‖z‖ : ℂ)]
    have h1 : (-1 : ℂ) ^ n * (-1) ^ (n + 1) = -1 := by
      rw [← pow_add]; exact Odd.neg_one_pow ⟨n, by ring⟩
    push_cast
    linear_combination ((n + 1 : ℂ) ^ n / ((n + 1).factorial : ℂ) * (‖z‖ : ℂ) ^ (n + 1)) * h1
  simp only [hterm] at hs
  have hreal := im_lambertW_zero_ofReal_and_neg_one_lt_re (x := -‖z‖) (by linarith)
  push_cast at hreal
  have hs' : HasSum (fun n : ℕ => ‖(-(n + 1) : ℂ) ^ n / (n + 1).factorial * z ^ (n + 1)‖)
      (-(lambertW 0 (-(‖z‖ : ℂ))).re) := by
    have := hs.neg
    simp only [neg_neg] at this
    have hW : -lambertW 0 (-(‖z‖ : ℂ)) = ((-(lambertW 0 (-(‖z‖ : ℂ))).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hreal.1]
    rw [hW] at this
    exact Complex.hasSum_ofReal.mp this
  have hle : ‖lambertW 0 z‖ ≤ -(lambertW 0 (-(‖z‖ : ℂ))).re := by
    rw [← (lambertW_hasSum hz).tsum_eq, ← hs'.tsum_eq]
    exact norm_tsum_le_tsum_norm hs'.summable
  linarith [hreal.2]

end LambertSeries
/-- General complex power series, with the n=0 coefficient continued to one for every a. -/
@[dlmf 4.13.E5_1]
theorem lambertW_power_hasSum (a : ℂ) {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    lambertWOver z ^ a = Complex.exp (-a * lambertW 0 z) ∧
    HasSum (fun n : ℕ => (if n = 0 then 1 else a * (n + a) ^ (n - 1) / n.factorial) * (-z) ^ n)
      (Complex.exp (-a * lambertW 0 z)) := by
  refine ⟨?_, ?_⟩
  · by_cases hz0 : z = 0
    · subst hz0
      have hW0 : lambertW 0 0 = 0 := (Classical.choice exists_lambertBranchFamily).zero 0
      simp [lambertWOver, hW0]
    · have heq : lambertW 0 z * Complex.exp (lambertW 0 z) = z :=
        lambertW_equation 0 z (Or.inr rfl)
      have hover : lambertWOver z = Complex.exp (-lambertW 0 z) := by
        simp only [lambertWOver, hz0, ↓reduceIte]
        rw [eq_comm, eq_div_iff hz0]
        calc Complex.exp (-lambertW 0 z) * z =
            Complex.exp (-lambertW 0 z) * (lambertW 0 z * Complex.exp (lambertW 0 z)) := by
              rw [heq]
          _ = lambertW 0 z := by
              rw [mul_comm (lambertW 0 z), ← mul_assoc, ← Complex.exp_add]; simp
      have hn := norm_lambertW_zero_lt_one hz
      have him := Complex.abs_im_le_norm (-lambertW 0 z)
      rw [norm_neg, abs_le] at him
      have hpi := Real.pi_gt_three
      rw [hover, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
        Complex.log_exp (by linarith) (by linarith)]
      ring_nf
  · convert hasSum_exp_neg_mul_lambertW_zero a hz using 2 with n
    rw [neg_pow z]; ring

/-- Reciprocal series, including its constant term `0^0=1`. -/
@[dlmf 4.13.E5_2]
theorem lambertW_reciprocal_hasSum {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => (n : ℂ) ^ n / n.factorial * z ^ n)
      (1 / (1 + lambertW 0 (-z))) := by
  obtain ⟨δ, hδ, hLB⟩ := hasSum_lagrangeBurmann_lambertW_zero
      (F := fun t => (1 + 0 * t + 0 * t ^ 2 + 0 * t ^ 3) *
    Complex.exp (-0 * t)) (by fun_prop)
  refine Complex.lagB_hasSum_of_differentiableOn (f := fun z => 1 / (1 + lambertW 0 (-z)))
    (lt_min hδ (Real.exp_pos (-1))) ?_ (fun z hz => ?_) (by simpa using hz)
  · have hd : DifferentiableOn ℂ (fun z => lambertW 0 (-z)) (Metric.ball 0 (Real.exp (-1))) :=
      differentiableOn_lambertW_zero_ball.comp (differentiableOn_neg _)
          (fun z hz => by simpa using hz)
    refine (differentiableOn_const 1).div (hd.const_add 1) (fun z hz => ?_)
    exact one_add_lambertW_zero_ne_zero_of_norm_lt (by simpa using hz)
  · rw [Metric.mem_ball, dist_zero_right] at hz
    have h := hLB (-z) (by rw [norm_neg]; exact lt_of_lt_of_le hz (min_le_left _ _))
    have h1 := one_add_lambertW_zero_ne_zero_of_norm_lt (z := -z)
      (by rw [norm_neg]; exact lt_of_lt_of_le hz (min_le_right _ _))
    have hval : (1 + 0 * lambertW 0 (-z) + 0 * lambertW 0 (-z) ^ 2 + 0 * lambertW 0 (-z) ^ 3) *
        Complex.exp (-0 * lambertW 0 (-z)) / (1 + lambertW 0 (-z)) =
          1 / (1 + lambertW 0 (-z)) := by simp
    simp only [cubic_mul_exp_mul_exp_pow_eq, iteratedDeriv_cubic_mul_exp_zero, hval] at h
    convert h using 2 with n
    simp only [powMulExpTaylorCoeff, Nat.zero_le, ↓reduceIte, Nat.choose_zero_right,
        Nat.factorial_zero,
      Nat.cast_one, one_mul, Nat.sub_zero, zero_mul, add_zero, zero_add]
    have hp : (-z) ^ n * (-(n : ℂ)) ^ n = (n : ℂ) ^ n * z ^ n := by
      rw [← mul_pow, ← mul_pow]; ring_nf
    rw [← mul_div_assoc, hp]; ring

section LambertSeries
open Metric
open scoped Nat

/-- `powMulExpTaylorCoeff` via descending factorials. -/
private lemma powMulExpTaylorCoeff_eq_descFactorial (n j : ℕ) (c : ℂ) :
    powMulExpTaylorCoeff n j c = if j ≤ n then (n.descFactorial j : ℂ) * c ^ (n - j) else 0 := by
  simp only [powMulExpTaylorCoeff, Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring_nf

end LambertSeries
/-- Squared-branch series with the negative integer power at n=1 preserved. -/
@[dlmf 4.13.E5_3]
theorem lambertW_square_hasSum {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => (n + 1 : ℂ) ^ ((n : ℤ) - 1) / (n + 1).factorial * (-z) ^ (n + 1))
      ((1 - (1 + lambertW 0 z) ^ 2) / 2) := by
  obtain ⟨δ, hδ, hLB⟩ := hasSum_lagrangeBurmann_lambertW_zero
      (F := fun t => (0 + (-1) * t + (-3 / 2) * t ^ 2 + (-1 / 2) * t ^ 3) *
    Complex.exp (-0 * t)) (by fun_prop)
  set c : ℕ → ℂ := fun n =>
      (0 * powMulExpTaylorCoeff n 0 (-(0 + n)) + (-1) * powMulExpTaylorCoeff n 1 (-(0 + n)) +
    (-3 / 2) * powMulExpTaylorCoeff n 2 (-(0 + n)) + (-1 / 2) * powMulExpTaylorCoeff n 3 (-(0 + n)))
        / n.factorial with hc
  have hfull : HasSum (fun n => c n * z ^ n) ((1 - (1 + lambertW 0 z) ^ 2) / 2) := by
    refine Complex.lagB_hasSum_of_differentiableOn
      (f := fun z => (1 - (1 + lambertW 0 z) ^ 2) / 2)
      (lt_min hδ (Real.exp_pos (-1))) ?_ (fun z hz => ?_) (by simpa using hz)
    · exact (((differentiableOn_lambertW_zero_ball.const_add 1).pow 2).const_sub 1).div_const 2
    · rw [Metric.mem_ball, dist_zero_right] at hz
      have h := hLB z (lt_of_lt_of_le hz (min_le_left _ _))
      have h1 := one_add_lambertW_zero_ne_zero_of_norm_lt (lt_of_lt_of_le hz (min_le_right _ _))
      have hval : (0 + (-1) * lambertW 0 z + (-3 / 2) * lambertW 0 z ^ 2 +
          (-1 / 2) * lambertW 0 z ^ 3) * Complex.exp (-0 * lambertW 0 z) / (1 + lambertW 0 z) =
            (1 - (1 + lambertW 0 z) ^ 2) / 2 := by
        simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one]
        field_simp; ring
      simp only [cubic_mul_exp_mul_exp_pow_eq, iteratedDeriv_cubic_mul_exp_zero, hval] at h
      convert h using 2 with n
      simp only [hc]; ring
  have hc0 : c 0 = 0 := by simp [hc, powMulExpTaylorCoeff]
  have hshift := (hasSum_nat_add_iff' 1).mpr hfull
  simp only [Finset.range_one, Finset.sum_singleton, hc0, zero_mul, sub_zero] at hshift
  convert hshift using 1
  funext n
  simp only [hc, powMulExpTaylorCoeff_eq_descFactorial]
  rcases n with _ | _ | k
  · simp
  · norm_num [Nat.factorial]
  · have hk : ((k + 2 : ℕ) : ℤ) - 1 = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hk, zpow_natCast]
    simp only [show 1 ≤ k + 2 + 1 by omega, show 2 ≤ k + 2 + 1 by omega,
      show 3 ≤ k + 2 + 1 by omega, Nat.zero_le, ↓reduceIte,
      Nat.succ_descFactorial_succ, Nat.descFactorial_zero]
    simp only [show k + 2 + 1 - 1 = k + 2 by omega, show k + 2 + 1 - 2 = k + 1 by omega,
      show k + 2 + 1 - 3 = k by omega]
    have e : (-(0 + ((k + 2 + 1 : ℕ) : ℂ))) = -((k : ℂ) + 3) := by push_cast; ring
    rw [e]
    simp only [neg_pow ((k : ℂ) + 3), neg_pow z]
    push_cast
    have h3 : ((k + 2 + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
    ring

/-- Unfolding the defining recurrence of `lambertC` at `n + 2`. -/
private lemma lambertC_add_two (n : ℕ) : lambertC (n + 2) = lambertC (n + 1) / (n + 3 : ℝ) - 1 / 2 *
      ∑ k ∈ range n, lambertC (k + 2) * lambertC (n + 1 - k) := by
  have ha : ¬ (n + 2 = 0) := by omega
  have hb : ¬ (n + 2 = 1) := by omega
  rw [lambertC]
  simp only [ha, hb, ↓reduceDIte]
  rw [    Fin.sum_univ_eq_sum_range (fun k => lambertC (k + 2) * lambertC (n + 2 - 1 - k))
      (n + 2 - 2)]
  simp only [Nat.add_sub_cancel, show n + 2 - 1 = n + 1 by omega]
  push_cast; ring_nf

/-- Exact initial branch-point coefficients. -/
@[dlmf 4.13.E7]
theorem lambertC_initial  :
    lambertC 0 = 1 ∧ lambertC 1 = 1 ∧ lambertC 2 = 1 / 3 ∧
    lambertC 3 = 1 / 36 ∧ lambertC 4 = -1 / 270 := by
  have h0 : lambertC 0 = 1 := by rw [lambertC]; simp
  have h1 : lambertC 1 = 1 := by rw [lambertC]; simp
  have h2 : lambertC 2 = 1/3 := by rw [lambertC_add_two]; simp [h1]
  have h3 : lambertC 3 = 1/36 := by rw [lambertC_add_two]; simp [h2]; norm_num
  have h4 : lambertC 4 = -1/270 := by
    rw [lambertC_add_two]; simp [h2, h3, Finset.sum_range_succ]; norm_num
  exact ⟨h0, h1, h2, h3, h4⟩

/-- The coefficient recurrence for every order n≥2. -/
@[dlmf 4.13.E8]
theorem lambertC_recurrence {n : ℕ} (hn : 2 ≤ n) :
    lambertC n = lambertC (n - 1) / (n + 1) - 1 / 2 *
      ∑ k ∈ Finset.Icc 2 (n - 1), lambertC k * lambertC (n + 1 - k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [lambertC_add_two]
  have : ∑ k ∈ Finset.Icc 2 (m + 2 - 1), lambertC k * lambertC (m + 2 + 1 - k) =
      ∑ k ∈ range m, lambertC (k + 2) * lambertC (m + 1 - k) := by
    rw [show Finset.Icc 2 (m + 2 - 1) = Finset.Ico 2 (2 + m) by ext x; simp; omega,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [add_comm 2 x]; congr 2; omega
  rw [this, show m + 2 - 1 = m + 1 by omega]; push_cast; ring_nf

/-- The exact relation with the Gamma Stirling coefficients. -/
@[dlmf 4.13.E9]
theorem lambertC_stirling (n : ℕ) :
    (DLMF.Core.oddProduct n) * lambertC (2 * n + 1) = DLMF.Gamma.stirlingG n := by
  sorry

/-- Convergent analytic branch-point parametrization on the full complex t-disk. -/
@[dlmf 4.13.E6]
theorem lambertC_hasSum {t : ℂ} (ht : ‖t‖ < 2 * Real.sqrt Real.pi) :
    ∃ w : ℂ, HasSum (fun n : ℕ => (-1 : ℂ) ^ ((n : ℤ) - 1) * lambertC n * t ^ n) w ∧
      w * Complex.exp w = -Complex.exp (-1 - t ^ 2 / 2) := by
  sorry

/-- The signs of the real parameter select the two real inverse branches. -/
@[dlmf 4.13.E6]
theorem lambertC_real_branches {t : ℝ} (ht : |t| < 2 * Real.sqrt Real.pi) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ ((n : ℤ) - 1) * lambertC n * (t : ℂ) ^ n)
      (if 0 ≤ t then lambertW 0 (-Real.exp (-1 - t ^ 2 / 2))
       else lambertW (-1) (-Real.exp (-1 - t ^ 2 / 2))) := by
  sorry

/-- Unfolding the defining recurrence of `lambertD` at `m + 2`. -/
private lemma lambertD_add_two (m : ℕ) : lambertD (m + 2) =
    (-2 * lambertD (m + 1) + (m + 1 : ℝ) / 2 *
      (∑ k ∈ range m, lambertD (k + 1) * lambertD (m - k)) -
      (m + 3 : ℝ) / 2 *
      (∑ k ∈ range m, lambertD (k + 2) * lambertD (m + 1 - k))) /
      ((m + 3 : ℝ) * Real.sqrt 2) := by
  have ha : ¬ (m + 2 = 0) := by omega
  have hb : ¬ (m + 2 = 1) := by omega
  rw [lambertD]
  simp only [ha, hb, ↓reduceDIte]
  rw [    Fin.sum_univ_eq_sum_range (fun k => lambertD (k + 1) * lambertD (m + 2 - 2 - k))
      (m + 2 - 2),
    Fin.sum_univ_eq_sum_range (fun k => lambertD (k + 2) * lambertD (m + 2 - 1 - k)) (m + 2 - 2)]
  simp only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega]
  push_cast; ring_nf

/-- Exact initial Puiseux coefficients. -/
@[dlmf 4.13.E9_2]
theorem lambertD_initial  :
    lambertD 0 = -1 ∧ lambertD 1 = Real.sqrt 2 ∧ lambertD 2 = -2 / 3 ∧
    lambertD 3 = 11 / 36 * Real.sqrt 2 ∧ lambertD 4 = -43 / 135 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have h0 : lambertD 0 = -1 := by rw [lambertD]; simp
  have h1 : lambertD 1 = Real.sqrt 2 := by rw [lambertD]; simp
  have h2 : lambertD 2 = -2/3 := by
    rw [lambertD_add_two]; simp [h1]; field_simp
  have h3 : lambertD 3 = 11 / 36 * Real.sqrt 2 := by
    rw [lambertD_add_two]; simp [h1, h2]; field_simp; linear_combination (-396 : ℝ) * hs
  have h4 : lambertD 4 = -43/135 := by
    rw [lambertD_add_two]; simp [h1, h2, h3, Finset.sum_range_succ]; field_simp
    linear_combination (0:ℝ) * hs
  exact ⟨h0, h1, h2, h3, h4⟩

/-- The full Puiseux-coefficient recurrence. -/
@[dlmf 4.13.E9_2]
theorem lambertD_recurrence {n : ℕ} (hn : 1 ≤ n) :
    (n + 2 : ℝ) * lambertD 1 * lambertD (n + 1) = -2 * lambertD n +
      (n : ℝ) / 2 * (∑ k ∈ Finset.Icc 1 (n - 1), lambertD k * lambertD (n - k)) -
      (n + 2 : ℝ) / 2 * (∑ k ∈ Finset.Icc 1 (n - 1), lambertD (k + 1) * lambertD (n - k + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : lambertD 1 = Real.sqrt 2 := by rw [lambertD]; simp
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  rw [h1, lambertD_add_two]
  have e1 : ∑ k ∈ Finset.Icc 1 (m + 1 - 1), lambertD k * lambertD (m + 1 - k) =
      ∑ k ∈ range m, lambertD (k + 1) * lambertD (m - k) := by
    rw [show Finset.Icc 1 (m + 1 - 1) = Finset.Ico 1 (1 + m) by ext x; simp; omega,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [add_comm 1 x]; congr 2; omega
  have e2 : ∑ k ∈ Finset.Icc 1 (m + 1 - 1), lambertD (k + 1) * lambertD (m + 1 - k + 1) =
      ∑ k ∈ range m, lambertD (k + 2) * lambertD (m + 1 - k) := by
    rw [show Finset.Icc 1 (m + 1 - 1) = Finset.Ico 1 (1 + m) by ext x; simp; omega,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp at hx
    congr 2 <;> omega
  rw [e1, e2]; push_cast; field_simp; ring

/-- Principal Puiseux series with the exact disk and branch exclusion. -/
@[dlmf 4.13.E9_1]
theorem lambertW_puiseux_hasSum {z : ℂ} (hz : ‖(Real.exp 1 : ℂ) * z + 1‖ < 1)
    (harg : |(z + (Real.exp (-1) : ℂ)).arg| < Real.pi) :
    HasSum (fun n : ℕ => (lambertD n : ℂ) * ((Real.exp 1 : ℂ) * z + 1) ^ ((n : ℂ) / 2))
      (lambertW 0 z) := by
  sorry

/-- All orders of the large-argument expansion, with a next-term logarithmic remainder. -/
@[dlmf 4.13.E10]
theorem lambertW_asymptotic (k : ℤ) (N : ℕ) :
    Asymptotics.IsBigO (Bornology.cobounded ℂ)
      (fun z => lambertW k z - lambertXi k z + Complex.log (lambertXi k z) -
        ∑ n ∈ range N, lambertAsymptoticTerm k z n)
      (fun z => (Complex.log (lambertXi k z)) ^ (N + 1) / lambertXi k z ^ (N + 1)) := by
  sorry

/-- The large-argument series is eventually absolutely convergent to the branch. -/
@[dlmf 4.13.E10]
theorem lambertW_asymptotic_converges (k : ℤ) :
    ∀ᶠ z : ℂ in Bornology.cobounded ℂ,
      Summable (fun n => ‖lambertAsymptoticTerm k z n‖) ∧
      HasSum (lambertAsymptoticTerm k z)
        (lambertW k z - lambertXi k z + Complex.log (lambertXi k z)) := by
  sorry

/-- For the real principal branch convergence already holds at e. -/
@[dlmf 4.13.E10]
theorem lambertW_asymptotic_real_converges {x : ℝ} (hx : Real.exp 1 ≤ x) :
    Summable (fun n => ‖lambertAsymptoticTerm 0 x n‖) ∧
    HasSum (lambertAsymptoticTerm 0 x)
      (lambertW 0 x - lambertXi 0 x + Complex.log (lambertXi 0 x)) := by
  sorry

/-- All orders for both real lower cut branches at zero from below. -/
@[dlmf 4.13.E11]
theorem lambertW_lower_asymptotic (N : ℕ) :
    Asymptotics.IsBigO (𝓝[<] (0 : ℝ))
      (fun x => lambertW (-1) x + Real.log (-1 / x) +
        Real.log (Real.log (-1 / x)) -
        ∑ n ∈ range N, (1 : ℂ) / (Real.log (-1 / x) : ℂ) ^ (n + 1) *
          ∑ m ∈ range (n + 1), (Nat.stirlingFirst (n + 1) (n + 1 - m) : ℂ) *
            (-Real.log (Real.log (-1 / x)) : ℂ) ^ (m + 1) / (m + 1).factorial)
      (fun x => (Real.log (Real.log (-1 / x)) : ℂ) ^ (N + 1) /
        (Real.log (-1 / x) : ℂ) ^ (N + 1)) := by
  sorry

/-- An antiderivative on each analytic branch away from zero. -/
@[dlmf 4.13.E12]
theorem lambertW_primitive (k : ℤ) {z : ℂ} (hne : z ≠ 0)
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => z / lambertW k z + z * lambertW k z - z) (lambertW k z) z := by
  rw [ite_mem_iff_mem_lambertBranchDomain] at hz
  have hd := hasDerivAt_lambertW hz
  have h1 := one_add_lambertW_ne_zero hz
  have hW := lambertW_ne_zero hz hne
  have := (((hasDerivAt_id z).div hd hW).add ((hasDerivAt_id z).mul hd)).sub (hasDerivAt_id z)
  convert this using 1
  · ext u; simp
  simp only [id_eq]
  clear this hd
  have heq := lambertW_mul_exp_lambertW hz
  generalize lambertW k z = w at *
  subst heq
  rw [Complex.exp_neg]
  have := Complex.exp_ne_zero w
  field_simp
  ring

/-- An antiderivative of W(z)/z. -/
@[dlmf 4.13.E13]
theorem lambertW_div_primitive (k : ℤ) {z : ℂ} (hne : z ≠ 0)
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => (lambertW k z) ^ 2 / 2 + lambertW k z) (lambertW k z / z) z := by
  rw [ite_mem_iff_mem_lambertBranchDomain] at hz
  have hd := hasDerivAt_lambertW hz
  have h1 := one_add_lambertW_ne_zero hz
  have hW := lambertW_ne_zero hz hne
  have := ((hd.pow 2).div_const 2).add hd
  convert this using 1
  clear this hd
  have heq := lambertW_mul_exp_lambertW hz
  generalize lambertW k z = w at *
  subst heq
  rw [Complex.exp_neg]
  have := Complex.exp_ne_zero w
  field_simp
  ring

/-- The sine-of-W antiderivative on every branch. -/
@[dlmf 4.13.E14]
theorem sin_lambertW_primitive (k : ℤ) {z : ℂ} (hne : z ≠ 0)
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => z * (1 + 1 / lambertW k z) * Complex.sin (lambertW k z) -
      z * Complex.cos (lambertW k z)) (2 * Complex.sin (lambertW k z)) z := by
  rw [ite_mem_iff_mem_lambertBranchDomain] at hz
  have hd := hasDerivAt_lambertW hz
  have h1 := one_add_lambertW_ne_zero hz
  have hW := lambertW_ne_zero hz hne
  have := (((hasDerivAt_id z).mul ((hasDerivAt_const z (1 : ℂ)).add
    ((hasDerivAt_const z (1 : ℂ)).div hd hW))).mul (hd.csin)).sub
    ((hasDerivAt_id z).mul hd.ccos)
  convert this using 1
  · ext u; simp
  simp only [id_eq, Pi.add_apply, Pi.mul_apply, Pi.div_apply]
  clear this hd
  have heq := lambertW_mul_exp_lambertW hz
  generalize lambertW k z = w at *
  subst heq
  rw [Complex.exp_neg]
  have := Complex.exp_ne_zero w
  field_simp
  ring

/-- Rational integral representation on the full principal slit domain. -/
@[dlmf 4.13.E15]
theorem lambertW_integral_rational {z : ℂ} (hz : z ∈ lambertPrincipalDomain) :
    lambertW 0 z = z / Real.pi * ∫ t in (0 : ℝ)..Real.pi,
      (((1 - t * Real.cos t / Real.sin t) ^ 2 + t ^ 2 : ℝ) : ℂ) /
        (z + t * Real.exp (-t * Real.cos t / Real.sin t) / Real.sin t) := by
  sorry

/-- Logarithmic integral representation on the full principal slit domain. -/
@[dlmf 4.13.E16]
theorem lambertW_integral_log {z : ℂ} (hz : z ∈ lambertPrincipalDomain) :
    lambertW 0 z = 1 / Real.pi * ∫ t in (0 : ℝ)..Real.pi,
      Complex.log (1 + z * (Real.sin t / t * Real.exp (t * Real.cos t / Real.sin t) : ℝ)) := by
  sorry

/-- The slit plane lies in the principal domain. -/
private lemma slitPlane_subset_lambertPrincipalDomain : Complex.slitPlane ⊆
    lambertPrincipalDomain := by
  intro z hz
  rcases Complex.mem_slitPlane_iff.mp hz with h | h
  · left; linarith [Real.exp_pos (-1)]
  · right; exact h

/-- A nonprincipal branch differs from the principal one throughout the slit plane. -/
private lemma lambertW_ne_lambertW_zero {k : ℤ} (hk : k ≠ 0) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    lambertW k z ≠ lambertW 0 z := by
  have hU := Complex.isOpen_slitPlane
  have hUc : IsPreconnected Complex.slitPlane := (Complex.starConvex_one_slitPlane.isPathConnected
    (by simp [Complex.mem_slitPlane_iff])).isConnected.isPreconnected
  have h0 := (lambertW_principal_analytic.mono slitPlane_subset_lambertPrincipalDomain).continuousOn
  have hk' := (lambertW_other_analytic k hk).continuousOn
  have hdom : ∀ z ∈ Complex.slitPlane, z ∈ lambertBranchDomain 0 := fun z hz => by
    simp only [lambertBranchDomain, ↓reduceIte]; exact slitPlane_subset_lambertPrincipalDomain hz
  have hdomk : ∀ z ∈ Complex.slitPlane, z ∈ lambertBranchDomain k := fun z hz => by
    simp only [lambertBranchDomain, hk, ↓reduceIte]; exact hz
  rcases eqOn_or_ne_of_mul_exp_eq hU hUc h0 hk' (fun z hz => lambertW_mul_exp_lambertW (hdom z hz))
      (fun z hz => lambertW_mul_exp_lambertW (hdomk z hz))
      (fun z hz => one_add_lambertW_ne_zero (hdom z hz)) with h | h
  · exfalso
    have h1 : (1 : ℂ) ∈ Complex.slitPlane := by simp [Complex.mem_slitPlane_iff]
    have e := h 1 h1
    have him0 : (lambertW 0 1).im = 0 :=
      ((Classical.choice exists_lambertBranchFamily).principal_basepoint).1
    have himk : (lambertW k 1).im ≠ 0 := by
      rcases lt_or_gt_of_ne hk with hneg | hpos
      · have := ((Classical.choice exists_lambertBranchFamily).negative_basepoint k hneg).2
        have : ((2 * k + 1 : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : 2 * k + 1 ≤ -1)
        push_cast at this
        change (lambertW k 1).im < _ at *
        nlinarith [Real.pi_pos]
      · have := ((Classical.choice exists_lambertBranchFamily).positive_basepoint k hpos).1
        have : (1 : ℝ) ≤ ((2 * k - 1 : ℤ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * k - 1)
        push_cast at this
        change _ < (lambertW k 1).im at *
        nlinarith [Real.pi_pos]
    exact himk (by rw [← e]; exact him0)
  · exact fun e => h z hz e.symm

/-- Nonprincipal branches have a logarithmic singularity at zero (4.13, prose). -/
theorem lambertW_other_norm_tendsto_zero (k : ℤ) (hk : k ≠ 0) :
    Tendsto (fun z : ℂ => ‖lambertW k z‖)
      (𝓝[Complex.slitPlane] 0) atTop := by
  obtain ⟨ε, hε, hinj⟩ := injOn_mul_exp_ball (w₀ := 0) (by norm_num)
  have h0 : (0 : ℂ) ∈ lambertPrincipalDomain := by left; simp [Real.exp_pos]
  have hc := (lambertW_principal_analytic 0 h0).continuousAt
  have hW0 : lambertW 0 0 = 0 := (Classical.choice exists_lambertBranchFamily).zero 0
  obtain ⟨δ, hδ, hδW⟩ := Metric.continuousAt_iff.mp hc ε hε
  rw [hW0] at hδW
  rw [tendsto_atTop]
  intro M
  set ρ := min δ (ε * Real.exp (-M))
  have hρ : 0 < ρ := lt_min hδ (by positivity)
  filter_upwards [inter_mem_nhdsWithin Complex.slitPlane (Metric.ball_mem_nhds (0 : ℂ) hρ)]
    with z ⟨hz, hzb⟩
  rw [Metric.mem_ball, dist_zero_right] at hzb
  have hbig : ε ≤ ‖lambertW k z‖ := by
    by_contra hlt
    push Not at hlt
    apply lambertW_ne_lambertW_zero hk hz
    have hk' : z ∈ lambertBranchDomain k := by simp only [lambertBranchDomain, hk, ↓reduceIte];
                                               exact hz
    have h0' : z ∈ lambertBranchDomain 0 := by simp only [lambertBranchDomain, ↓reduceIte]; exact
                                                 slitPlane_subset_lambertPrincipalDomain hz
    refine hinj (by simpa using hlt) ?_
        ((lambertW_mul_exp_lambertW hk').trans (lambertW_mul_exp_lambertW h0').symm)
    have := hδW (x := z) (by rw [dist_zero_right]; exact lt_of_lt_of_le hzb (min_le_left _ _))
    simpa using this
  have hk' : z ∈ lambertBranchDomain k := by simp only [lambertBranchDomain, hk, ↓reduceIte]; exact
                                               hz
  have heq := congrArg norm (lambertW_mul_exp_lambertW hk')
  rw [norm_mul, Complex.norm_exp] at heq
  have hexp : Real.exp (lambertW k z).re < Real.exp (-M) := by
    have h1 : ε * Real.exp (lambertW k z).re ≤ ‖z‖ := by
      rw [← heq]; exact mul_le_mul_of_nonneg_right hbig (Real.exp_pos _).le
    have h2 : ‖z‖ < ε * Real.exp (-M) := lt_of_lt_of_le hzb (min_le_right _ _)
    have := lt_of_le_of_lt h1 h2
    exact lt_of_mul_lt_mul_left this hε.le
  have hre : (lambertW k z).re < -M := Real.exp_lt_exp.mp hexp
  have := Complex.abs_re_le_norm (lambertW k z)
  rw [abs_le] at this
  linarith

/-- `t cot t < 1` on `(0, π)`. -/
private lemma mul_cos_div_sin_lt_one {t : ℝ} (h0 : 0 < t) (hπ : t < π) : t * Real.cos t / Real.sin t
    < 1 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  rw [div_lt_one hs]
  rcases lt_or_ge t (π / 2) with h | h
  · have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith, h⟩
    have := Real.lt_tan h0 h
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hc] at this
    linarith
  · have hc : Real.cos t ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith)
    nlinarith

/-- The polynomial-times-exponential bound `(1-x)² + π² ≤ (2+π²) e^{1-x}` for `x ≤ 1`. -/
private lemma one_sub_sq_add_pi_sq_le_mul_exp {x : ℝ} (hx : x ≤ 1) :
    (1 - x) ^ 2 + π ^ 2 ≤ (2 + π ^ 2) * Real.exp (1 - x) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 1 - x) (by linarith)
  have hpi : 0 ≤ π ^ 2 := by positivity
  nlinarith

/-- The rational principal-branch integrand is bounded. -/
private lemma exists_bound_lambertW_rational_integrand {z : ℂ} (hz : z ∈ lambertPrincipalDomain) :
    ∃ M : ℝ, ∀ t ∈ Ioo 0 π, ‖(((1 - t * Real.cos t / Real.sin t) ^ 2 + t ^ 2 : ℝ) : ℂ) /
        (z + t * Real.exp (-t * Real.cos t / Real.sin t) / Real.sin t)‖ ≤ M := by
  -- the uniform lower bound of the denominator
  obtain ⟨c, hc, hcD⟩ : ∃ c > 0, ∀ v : ℝ, Real.exp (-1) < v → c ≤ ‖z + v‖ := by
    by_cases him : z.im = 0
    · have hre : -Real.exp (-1) < z.re := by
        rcases hz with h | h
        · exact h
        · exact absurd him h
      refine ⟨z.re + Real.exp (-1), by linarith, fun v hv => ?_⟩
      have := Complex.re_le_norm (z + v)
      simp at this; linarith
    · refine ⟨|z.im|, abs_pos.mpr him, fun v _ => ?_⟩
      have := Complex.abs_im_le_norm (z + v)
      simpa using this
  set B := Real.exp 1 * (2 + π ^ 2)
  have hB : 0 ≤ B := by positivity
  refine ⟨2 * B + 2 * B * ‖z‖ / c, fun t ht => ?_⟩
  obtain ⟨h0, hπ⟩ := ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  set x := t * Real.cos t / Real.sin t with hxdef
  have hx : x < 1 := mul_cos_div_sin_lt_one h0 hπ
  set v := t * Real.exp (-t * Real.cos t / Real.sin t) / Real.sin t with hvdef
  have hneg : -t * Real.cos t / Real.sin t = -x := by rw [hxdef]; ring
  have hts : 1 ≤ t / Real.sin t := by rw [le_div_iff₀ hs]; linarith [Real.sin_le h0.le]
  have hv : v = t / Real.sin t * Real.exp (-x) := by rw [hvdef, hneg]; ring
  have hvx : Real.exp (-x) ≤ v := by
    rw [hv]; nlinarith [Real.exp_pos (-x)]
  have hve : Real.exp (-1) < v := lt_of_lt_of_le (Real.exp_lt_exp.mpr (by linarith)) hvx
  set N := (1 - x) ^ 2 + t ^ 2
  have hN0 : 0 ≤ N := by positivity
  have hNB : N ≤ B * v := by
    have h1 := one_sub_sq_add_pi_sq_le_mul_exp hx.le
    have h2 : Real.exp (1 - x) = Real.exp 1 * Real.exp (-x) := by
      rw [← Real.exp_add]; ring_nf
    have ht2 : t ^ 2 ≤ π ^ 2 := by nlinarith
    calc N ≤ (1 - x) ^ 2 + π ^ 2 := by simp only [N]; linarith
      _ ≤ (2 + π ^ 2) * Real.exp (1 - x) := h1
      _ = B * Real.exp (-x) := by rw [h2]; ring
      _ ≤ B * v := by gcongr
  have hcast : ((t : ℂ) * ((Real.exp (-t * Real.cos t / Real.sin t) : ℝ) : ℂ) /
      ((Real.sin t : ℝ) : ℂ)) = ((v : ℝ) : ℂ) := by rw [hvdef]; push_cast; ring
  rw [hcast, norm_div, Complex.norm_real, Real.norm_of_nonneg hN0]
  have hD := hcD v hve
  have hDpos : 0 < ‖z + v‖ := lt_of_lt_of_le hc hD
  have hDv : v - ‖z‖ ≤ ‖z + v‖ := by
    have := norm_sub_norm_le (v : ℂ) (-z)
    simp only [Complex.norm_real, Real.norm_of_nonneg (by linarith [Real.exp_pos (-1)] : (0:ℝ) ≤ v),
      norm_neg, sub_neg_eq_add] at this
    rw [add_comm] at this; exact this
  rw [div_le_iff₀ hDpos]
  rcases le_or_gt (2 * ‖z‖) v with hbig | hsmall
  · -- the denominator is at least `v / 2`
    have : v / 2 ≤ ‖z + v‖ := by linarith
    have hzc : 0 ≤ 2 * B * ‖z‖ / c * ‖z + ↑v‖ := by positivity
    nlinarith
  · have : N ≤ 2 * B * ‖z‖ := by nlinarith
    have h2 : 2 * B * ‖z‖ / c * ‖z + ↑v‖ ≥ 2 * B * ‖z‖ := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hc]
      have : 0 ≤ 2 * B * ‖z‖ := by positivity
      nlinarith
    nlinarith [norm_nonneg (z + ↑v)]

/-- A bound for the principal logarithm on an annulus. -/
private lemma norm_log_le_of_mem_annulus {w : ℂ} {c C : ℝ} (hc : 0 < c) (h1 : c ≤ ‖w‖)
    (h2 : ‖w‖ ≤ C) :
    ‖Complex.log w‖ ≤ |Real.log c| + |Real.log C| + π := by
  have hw : 0 < ‖w‖ := lt_of_lt_of_le hc h1
  have hlog : |Real.log ‖w‖| ≤ |Real.log c| + |Real.log C| := by
    have a1 := Real.log_le_log hc h1
    have a2 := Real.log_le_log hw h2
    rw [abs_le]; constructor
    · have := neg_abs_le (Real.log c); have := abs_nonneg (Real.log C); linarith
    · have := le_abs_self (Real.log C); have := abs_nonneg (Real.log c); linarith
  calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖w‖| + |w.arg| := by rw [Complex.log_re, Complex.log_im]
    _ ≤ |Real.log c| + |Real.log C| + π := by linarith [Complex.abs_arg_le_pi w]

/-- The logarithmic principal-branch integrand is bounded. -/
private lemma exists_bound_lambertW_log_integrand {z : ℂ} (hz : z ∈ lambertPrincipalDomain) :
    ∃ M : ℝ, ∀ t ∈ Ioo 0 π, ‖Complex.log (1 + z *
      (Real.sin t / t * Real.exp (t * Real.cos t / Real.sin t) : ℝ))‖ ≤ M := by
  -- a lower bound for `‖1 + z u‖` with `0 < u < e`
  obtain ⟨c, hc, hcw⟩ : ∃ c > 0, ∀ u : ℝ, 0 < u → u < Real.exp 1 → c ≤ ‖1 + z * u‖ := by
    by_cases him : z.im = 0
    · have hre : -Real.exp (-1) < z.re := by
        rcases hz with h | h
        · exact h
        · exact absurd him h
      have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
      have hpos : 0 < 1 + z.re * Real.exp 1 := by nlinarith [Real.exp_pos 1]
      refine ⟨min 1 (1 + z.re * Real.exp 1), lt_min one_pos hpos, fun u hu hue => ?_⟩
      have := Complex.re_le_norm (1 + z * u)
      simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero] at this
      rcases le_or_gt 0 z.re with h | h
      · have : 1 ≤ 1 + z.re * u := by nlinarith
        linarith [min_le_left 1 (1 + z.re * Real.exp 1)]
      · have : 1 + z.re * Real.exp 1 ≤ 1 + z.re * u := by nlinarith
        linarith [min_le_right 1 (1 + z.re * Real.exp 1)]
    · have hz0 : z ≠ 0 := by intro h; apply him; rw [h]; simp
      have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      refine ⟨|z.im| / ‖z‖, div_pos (abs_pos.mpr him) hnz, fun u _ _ => ?_⟩
      rw [div_le_iff₀ hnz]
      have key : ((1 + z * u) * (starRingEnd ℂ) z).im = -z.im := by
        simp [Complex.mul_im, Complex.mul_re]; ring_nf
      have := Complex.abs_im_le_norm ((1 + z * u) * (starRingEnd ℂ) z)
      rw [key, abs_neg, norm_mul, Complex.norm_conj] at this
      exact this
  refine ⟨|Real.log c| + |Real.log (1 + ‖z‖ * Real.exp 1)| + π, fun t ht => ?_⟩
  obtain ⟨h0, hπ⟩ := ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hx := mul_cos_div_sin_lt_one h0 hπ
  set u := Real.sin t / t * Real.exp (t * Real.cos t / Real.sin t)
  have hu0 : 0 < u := by positivity
  have hst : Real.sin t / t ≤ 1 := by rw [div_le_one h0]; exact Real.sin_le h0.le
  have hue : u < Real.exp 1 := by
    have := Real.exp_lt_exp.mpr hx
    calc u ≤ 1 * Real.exp (t * Real.cos t / Real.sin t) :=
          mul_le_mul_of_nonneg_right hst (Real.exp_pos _).le
      _ < Real.exp 1 := by rw [one_mul]; exact this
  apply norm_log_le_of_mem_annulus hc (hcw u hu0 hue)
  calc ‖1 + z * u‖ ≤ ‖(1 : ℂ)‖ + ‖z * u‖ := norm_add_le _ _
    _ = 1 + ‖z‖ * u := by rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    _ ≤ 1 + ‖z‖ * Real.exp 1 := by gcongr

/-- The rational principal-branch integral is convergent on the stated domain. -/
@[dlmf 4.13.E15]
theorem lambertW_integral_rational_integrable {z : ℂ} (hz : z ∈ lambertPrincipalDomain) :
    IntervalIntegrable (fun t : ℝ =>
      (((1 - t * Real.cos t / Real.sin t) ^ 2 + t ^ 2 : ℝ) : ℂ) /
        (z + t * Real.exp (-t * Real.cos t / Real.sin t) / Real.sin t))
      MeasureTheory.volume 0 Real.pi := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le]
  obtain ⟨M, hM⟩ := exists_bound_lambertW_rational_integrand hz
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioo_lt_top ?_ M
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hM)
  apply Measurable.aestronglyMeasurable
  fun_prop

/-- The logarithmic principal-branch integral is convergent on the stated domain. -/
@[dlmf 4.13.E16]
theorem lambertW_integral_log_integrable {z : ℂ} (hz : z ∈ lambertPrincipalDomain) :
    IntervalIntegrable (fun t : ℝ =>
      Complex.log (1 + z * (Real.sin t / t * Real.exp (t * Real.cos t / Real.sin t) : ℝ)))
      MeasureTheory.volume 0 Real.pi := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le]
  obtain ⟨M, hM⟩ := exists_bound_lambertW_log_integrand hz
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioo_lt_top ?_ M
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hM)
  apply Measurable.aestronglyMeasurable
  fun_prop

/-- Puiseux expansion of the decreasing real branch continued into the upper half-plane.
Together with its nonzero first coefficient this records its square-root branch point. -/
@[dlmf 4.13.E9_1]
theorem lambertW_minus_one_puiseux_hasSum {z : ℂ}
    (hz : ‖(Real.exp 1 : ℂ) * z + 1‖ < 1)
    (harg : |(z + (Real.exp (-1) : ℂ)).arg| < Real.pi) (him : 0 ≤ z.im) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * lambertD n *
      ((Real.exp 1 : ℂ) * z + 1) ^ ((n : ℂ) / 2)) (lambertW (-1) z) := by
  sorry

/-- Lower-side counterpart of the real-branch Puiseux expansion. -/
@[dlmf 4.13.E9_1]
theorem lambertW_one_lower_puiseux_hasSum {z : ℂ}
    (hz : ‖(Real.exp 1 : ℂ) * z + 1‖ < 1)
    (harg : |(z + (Real.exp (-1) : ℂ)).arg| < Real.pi) (him : z.im ≤ 0) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * lambertD n *
      ((Real.exp 1 : ℂ) * z + 1) ^ ((n : ℂ) / 2)) (lambertWLower 1 z) := by
  sorry

/-- The singular growth of a nonprincipal branch at zero is logarithmic. -/
theorem lambertW_other_logarithmic_growth (k : ℤ) (hk : k ≠ 0) :
    Tendsto (fun z : ℂ => ‖lambertW k z‖ / |Real.log ‖z‖|)
      (𝓝[Complex.slitPlane] 0) (𝓝 1) := by
  set C : ℝ := Real.pi + 2 * Real.pi * |(k : ℝ)|
  have hC : 0 ≤ C := by positivity
  set l := 𝓝[Complex.slitPlane] (0 : ℂ)
  have hL : Tendsto (fun z : ℂ => |Real.log ‖z‖|) l atTop := by
    have h0 : Tendsto (fun z : ℂ => ‖z‖) l (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_norm.tendsto (0 : ℂ)).mono_left (nhdsWithin_le_nhds (s :=
          Complex.slitPlane))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact norm_pos_iff.mpr (Complex.slitPlane_ne_zero hz)
    exact tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h0)
  -- the estimate
  have key : ∀ z ∈ Complex.slitPlane, 1 ≤ |Real.log ‖z‖| →
      abs (‖lambertW k z‖ - |Real.log ‖z‖|) ≤ 8 * Real.sqrt (|Real.log ‖z‖| + C) + Real.pi + C := by
    intro z hz hL1
    set ξ := Complex.log z + 2 * Real.pi * I * k
    have hΩ := log_add_mem_lambertOmegaDomain k hz
    have hW : lambertW k z = lambertLogMapInv ξ := by
      rw [lambertW_eq_lambertBranchValue, lambertBranchValue_of_mem_slitPlane k hz]
    obtain ⟨hS, hg⟩ := lambertLogMapInv_spec hΩ
    have him : |ξ.im| ≤ C := by
      rw [im_log_add_two_pi_mul_I_mul]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      simp only [C]; linarith [abs_arg_le_pi z]
    have him2 : Real.pi ≤ |ξ.im| := by
      rw [im_log_add_two_pi_mul_I_mul]
      have hk' : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
      have := abs_arg_le_pi z
      have h2 : 2 * Real.pi * |(k : ℝ)| ≤ |arg z + 2 * Real.pi * k| + |arg z| := by
        have := abs_sub (arg z + 2 * Real.pi * k) (arg z)
        rwa [add_sub_cancel_left, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          at this
      nlinarith [Real.pi_pos]
    have hW1 : 1 ≤ ‖lambertLogMapInv ξ‖ :=
      one_le_norm_of_pi_le_abs_lambertLogMap_im hS (by rw [hg]; exact him2)
    have hre : ξ.re = Real.log ‖z‖ := re_log_add_two_pi_mul_I_mul k z
    have hξ1 : |Real.log ‖z‖| ≤ ‖ξ‖ := by rw [← hre]; exact Complex.abs_re_le_norm ξ
    have hξ2 : ‖ξ‖ ≤ |Real.log ‖z‖| + C := by
      refine (Complex.norm_le_abs_re_add_abs_im ξ).trans ?_; rw [hre]; linarith
    have hd := norm_lambertLogMapInv_sub_le hΩ hW1 (by linarith)
    have hsq : Real.sqrt ‖ξ‖ ≤ Real.sqrt (|Real.log ‖z‖| + C) := Real.sqrt_le_sqrt hξ2
    rw [hW, abs_le]
    have t1 := norm_sub_norm_le (lambertLogMapInv ξ) ξ
    have t2 := norm_sub_norm_le ξ (lambertLogMapInv ξ)
    rw [norm_sub_rev] at t2
    constructor <;> nlinarith [Real.pi_pos]
  have hB : Tendsto (fun t : ℝ => (8 * Real.sqrt (t + C) + Real.pi + C) / t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 8 * (Real.sqrt t)⁻¹ +
        (8 * Real.sqrt C + Real.pi + C) * t⁻¹) atTop (𝓝 0) := by
      have a := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul 8
      have b := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (8 * Real.sqrt C + Real.pi + C)
      simpa using a.add b
    refine squeeze_zero' ?_ ?_ h1
    · filter_upwards [eventually_gt_atTop 0] with t ht; positivity
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have hs : Real.sqrt (t + C) ≤ Real.sqrt t + Real.sqrt C := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [Real.sq_sqrt ht.le, Real.sq_sqrt hC, Real.sqrt_nonneg t, Real.sqrt_nonneg C]
      have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
      rw [div_le_iff₀ ht]
      have e : (8 * (Real.sqrt t)⁻¹ + (8 * Real.sqrt C + Real.pi + C) * t⁻¹) * t =
          8 * Real.sqrt t + (8 * Real.sqrt C + Real.pi + C) := by
        field_simp; linear_combination (-8) * Real.sq_sqrt ht.le
      rw [e]; linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (hB.comp hL)
  filter_upwards [self_mem_nhdsWithin, hL.eventually (eventually_ge_atTop 1)] with z hz hL1
  have hpos : 0 < |Real.log ‖z‖| := by linarith
  simp only [Function.comp, Real.norm_eq_abs]
  rw [div_sub_one hpos.ne', abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right (key z hz hL1) hpos.le

/-- Differential of the inverse substitution `z=w exp w` used in Lambert integrals. -/
theorem lambert_forward_hasDerivAt (w : ℂ) :
    HasDerivAt (fun w : ℂ => w * Complex.exp w) ((w + 1) * Complex.exp w) w := by
  simpa only [id_eq, Pi.mul_apply, one_mul, add_mul, add_comm] using
    (hasDerivAt_id w).fun_mul (Complex.hasDerivAt_exp w)

end DLMF.Elementary

end
end
