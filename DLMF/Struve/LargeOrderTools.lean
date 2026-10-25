/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import DLMFMathlib.Analysis.Asymptotics.WatsonSector

/-!
# Large-order tools for the Anger–Weber coefficients

The coefficients `A_k(λ)` of the scaled Anger–Weber expansion DLMF 11.11.8 are the Taylor
coefficients `[u^{2k}] dt/du` of the inverse of `u = t + λ sinh t`; by Lagrange inversion
`A_k(λ) = Res_{t=0} (t + λ sinh t)^{-(2k+1)}`. This file works with the circle integrals

`I_m(λ) = ∮_{|t|=r} g(t) (t + λ sinh t)^{-m} dt`  (`struveLO_I`)

on a small circle on which `t + λ sinh t = t (1 + λ σ(t))`, `σ = dslope sinh 0`, has no zero
other than `t = 0` for all `λ` in a closed disc around `λ₀ ≠ -1` (`struveLO_Good`,
`struveLO_good_exists`). The integrals are holomorphic in `λ`
(`struveLO_hasDerivAt_I`, by differentiation under the integral sign,
`struveLO_hasDerivAt_circleIntegral`), `I_1 = 2πi/(1+λ)` (`struveLO_I_one`, Cauchy's
formula), and since

`λ² n(n+1) sinh² t u^{-n-2} - λ n sinh t u^{-n-1} - (1-λ²) n(n+1) u^{-n-2}
  = d/dt [-n (λ cosh t - 1) u^{-n-1}]`

(`struveLO_hasDerivAt_exact`), the identity
`θ² I_n = (1-λ²) n(n+1) I_{n+2}`, `θ = λ d/dλ`, holds (`struveLO_recurrence`). This is the
recurrence DLMF 11.11(iii) for `A_k = (2πi)⁻¹ I_{2k+1}`, and it shows that the singularity of
the recurrence at `λ = 1` is removable (`angerScaledA_removable` in `DLMF.Struve.Asymptotics`).

The second part treats the large-order expansions DLMF 11.6.6–11.6.7 of `𝐊_ν(λν)` and
`𝐌_ν(λν)` by expanding `(1 ± t²)^{ν-1/2}` binomially inside the integrals 11.5.2 and 11.5.4.
For complex `a` and real `u > -1` the remainder `R_N(a, u) = (1+u)^a - ∑_{j<N} (a choose j) u^j`
(`struveLO_R`) satisfies `|R_N(a,u)| ≤ ∏_{i<N} |a-i| |u|^N (1 + max u 0)^{re a - N}` for
`N ≤ re a` (`struveLO_norm_R_le`, by induction with the mean value inequality). Integrating
against `e^{-zt}` gives explicit error bounds for
`∫₀^∞ e^{-zt} (1+t²)^a dt` (`struveLO_K_integral_bound`, `re a < re z`) and for
`∫₀¹ e^{-zt} (1-t²)^a dt` (`struveLO_M_integral_bound`, `re z > 0`), uniform in complex `a`, `z`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Metric
open scoped Real Topology Interval

namespace DLMF.Struve

/-- Differentiation under a circle integral in a parameter. -/
theorem struveLO_hasDerivAt_circleIntegral {F F' : ℂ → ℂ → ℂ} {s : Set ℂ} (hs : IsCompact s)
    {z₀ : ℂ} (hz : s ∈ 𝓝 z₀) {r : ℝ}
    (hF : ContinuousOn (fun p : ℂ × ℝ => F p.1 (circleMap 0 r p.2)) (s ×ˢ univ))
    (hF' : ContinuousOn (fun p : ℂ × ℝ => F' p.1 (circleMap 0 r p.2)) (s ×ˢ univ))
    (hd : ∀ z ∈ s, ∀ θ : ℝ, HasDerivAt (fun w => F w (circleMap 0 r θ))
      (F' z (circleMap 0 r θ)) z) :
    HasDerivAt (fun z => ∮ t in C(0, r), F z t) (∮ t in C(0, r), F' z₀ t) z₀ := by
  simp only [circleIntegral, deriv_circleMap]
  have hz0 : z₀ ∈ s := mem_of_mem_nhds hz
  have hc : ∀ {G : ℂ → ℂ → ℂ}, ContinuousOn (fun p : ℂ × ℝ => G p.1 (circleMap 0 r p.2))
      (s ×ˢ univ) → ContinuousOn
      (fun p : ℂ × ℝ => (circleMap 0 r p.2 * I) • G p.1 (circleMap 0 r p.2)) (s ×ˢ univ) :=
    fun h => (((continuous_circleMap 0 r).comp continuous_snd).mul continuous_const).continuousOn.smul h
  have hθ : ∀ {G : ℂ → ℂ → ℂ}, ContinuousOn (fun p : ℂ × ℝ => G p.1 (circleMap 0 r p.2))
      (s ×ˢ univ) → ∀ z ∈ s, Continuous fun θ : ℝ => (circleMap 0 r θ * I) • G z (circleMap 0 r θ) := by
    intro G h z hzs
    have := (hc h).comp_continuous (Continuous.prodMk_right z) (fun θ => ⟨hzs, mem_univ _⟩)
    exact this
  obtain ⟨C, hC⟩ := (hs.prod (isCompact_uIcc (a := (0:ℝ)) (b := 2 * π))).exists_bound_of_continuousOn
    ((hc hF').mono (prod_mono le_rfl (subset_univ _)))
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (F := fun z θ => (circleMap 0 r θ * I) • F z (circleMap 0 r θ))
    (F' := fun z θ => (circleMap 0 r θ * I) • F' z (circleMap 0 r θ))
    hz ?_ ((hθ hF z₀ hz0).intervalIntegrable _ _) (hθ hF' z₀ hz0).aestronglyMeasurable ?_
    intervalIntegrable_const ?_).2
  · filter_upwards [hz] with z hzs using (hθ hF z hzs).aestronglyMeasurable
  · refine Eventually.of_forall fun θ hθ' z hzs => hC (z, θ) ⟨hzs, uIoc_subset_uIcc hθ'⟩
  · refine Eventually.of_forall fun θ _ z hzs => ?_
    exact (hd z hzs θ).const_smul (circleMap 0 r θ * I)


/-- The circle integral `∮_{|t|=r} g(t) (t + λ sinh t)^{-m} dt`. -/
def struveLO_I (r : ℝ) (g : ℂ → ℂ) (m : ℕ) (lam : ℂ) : ℂ :=
  ∮ t in C(0, r), g t * ((t + lam * sinh t) ^ m)⁻¹

/-- `sinh t = t · σ(t)` with the entire slope `σ = dslope sinh 0`. -/
lemma struveLO_sinh_eq (t : ℂ) : sinh t = t * dslope sinh 0 t := by
  have h := sub_smul_dslope sinh 0 t
  simp only [sub_zero, smul_eq_mul, sinh_zero] at h
  exact h.symm

/-- The slope `σ = dslope sinh 0` is entire. -/
lemma struveLO_differentiable_dslope : Differentiable ℂ (dslope sinh 0) := by
  intro t
  exact ((differentiableOn_dslope (s := univ) univ_mem).2
    differentiable_sinh.differentiableOn t (mem_univ _)).differentiableAt univ_mem

/-- `σ(0) = 1`. -/
lemma struveLO_dslope_zero : dslope sinh 0 0 = 1 := by
  rw [dslope_same, Complex.deriv_sinh, cosh_zero]

/-- The good-set condition: on the closed disc `|λ - λ₀| ≤ ε` and `|t| ≤ r` the factor
`1 + λ σ(t)` of `t + λ sinh t = t (1 + λ σ(t))` does not vanish. -/
def struveLO_Good (r ε : ℝ) (lam₀ : ℂ) : Prop :=
  ∀ lam ∈ closedBall lam₀ ε, ∀ t ∈ closedBall (0 : ℂ) r, 1 + lam * dslope sinh 0 t ≠ 0

/-- For `1 + λ₀ ≠ 0` a good disc pair exists. -/
lemma struveLO_good_exists {lam₀ : ℂ} (h : 1 + lam₀ ≠ 0) :
    ∃ r > 0, ∃ ε > 0, struveLO_Good r ε lam₀ := by
  set m := ‖1 + lam₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 h
  set L := ‖lam₀‖ + m / 4 + 1 with hL
  have hL0 : 0 < L := by positivity
  have hcont : ContinuousAt (dslope sinh 0) 0 := struveLO_differentiable_dslope.continuous.continuousAt
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousAt_iff.1 hcont (m / (2 * L)) (by positivity)
  refine ⟨ρ / 2, by positivity, m / 4, by positivity, fun lam hlam t ht => ?_⟩
  have ht' : dist t 0 < ρ := by
    have := mem_closedBall.1 ht; linarith
  have hσ := hρ' ht'
  rw [struveLO_dslope_zero, dist_eq_norm] at hσ
  rw [mem_closedBall, dist_eq_norm] at hlam
  have hlamL : ‖lam‖ ≤ L := by
    have := norm_le_norm_add_norm_sub' lam lam₀
    linarith
  have h1 : m - m / 4 ≤ ‖1 + lam‖ := by
    have := norm_sub_norm_le (1 + lam₀) (lam₀ - lam)
    rw [show 1 + lam₀ - (lam₀ - lam) = 1 + lam by ring, norm_sub_rev] at this; linarith
  have h2 : ‖lam * (dslope sinh 0 t - 1)‖ ≤ m / 2 := by
    rw [norm_mul]
    calc ‖lam‖ * ‖dslope sinh 0 t - 1‖ ≤ L * (m / (2 * L)) := by gcongr
      _ = m / 2 := by field_simp
  intro h0
  have : 1 + lam = -(lam * (dslope sinh 0 t - 1)) := by linear_combination h0
  rw [this, norm_neg] at h1
  linarith

/-- On a good disc pair the denominator `t + λ sinh t` does not vanish for `0 < |t| ≤ r`. -/
lemma struveLO_u_ne {r ε : ℝ} {lam₀ : ℂ} (hG : struveLO_Good r ε lam₀) {lam : ℂ}
    (hlam : lam ∈ closedBall lam₀ ε) {t : ℂ} (ht : t ∈ closedBall (0 : ℂ) r) (ht0 : t ≠ 0) :
    t + lam * sinh t ≠ 0 := by
  rw [struveLO_sinh_eq, show t + lam * (t * dslope sinh 0 t) = t * (1 + lam * dslope sinh 0 t) by
    ring]
  exact mul_ne_zero ht0 (hG lam hlam t ht)

/-- Points of the circle `|t| = r`, `r > 0`, as values of `circleMap`. -/
lemma struveLO_circleMap_mem {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    circleMap 0 r θ ∈ closedBall (0 : ℂ) r ∧ circleMap 0 r θ ≠ 0 :=
  ⟨sphere_subset_closedBall (circleMap_mem_sphere 0 hr.le θ), circleMap_ne_center hr.ne'⟩

/-- Derivative of `c (a + w b)^{-m}` in `w`. -/
lemma struveLO_hasDerivAt_recip_pow (a b c : ℂ) (m : ℕ) {w : ℂ} (h : a + w * b ≠ 0) :
    HasDerivAt (fun w => c * ((a + w * b) ^ m)⁻¹)
      (-(m : ℂ) * (c * b * ((a + w * b) ^ (m + 1))⁻¹)) w := by
  have hu : HasDerivAt (fun w => a + w * b) b w := by
    simpa using ((hasDerivAt_id w).mul_const b).const_add a
  have := ((hu.inv h).pow m).const_mul c
  simp only [← inv_pow]
  convert this using 1
  rcases m with _ | m
  · simp
  · simp only [Pi.inv_apply, div_eq_mul_inv, ← inv_pow, Nat.add_sub_cancel]
    push_cast
    ring

/-- Continuity of the circle integrands on a good disc. -/
lemma struveLO_continuousOn {r ε : ℝ} {lam₀ : ℂ} (hr : 0 < r) (hG : struveLO_Good r ε lam₀)
    {g : ℂ → ℂ} (hg : Continuous g) (m : ℕ) :
    ContinuousOn (fun p : ℂ × ℝ => g (circleMap 0 r p.2) *
      ((circleMap 0 r p.2 + p.1 * sinh (circleMap 0 r p.2)) ^ m)⁻¹) (closedBall lam₀ ε ×ˢ univ) := by
  have hc : Continuous fun p : ℂ × ℝ => circleMap 0 r p.2 :=
    (continuous_circleMap 0 r).comp continuous_snd
  refine (hg.comp hc).continuousOn.mul (ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop))
    fun p hp => pow_ne_zero _ ?_)
  obtain ⟨h1, h2⟩ := struveLO_circleMap_mem hr p.2
  exact struveLO_u_ne hG hp.1 h1 h2

/-- `λ ↦ ∮ g (t + λ sinh t)^{-m}` is differentiable on a good disc, with derivative
`-m ∮ g sinh (t + λ sinh t)^{-(m+1)}`. -/
theorem struveLO_hasDerivAt_I {r ε : ℝ} {lam₀ : ℂ} (hr : 0 < r) (hG : struveLO_Good r ε lam₀)
    {g : ℂ → ℂ} (hg : Continuous g) (m : ℕ) {lam : ℂ} (hlam : lam ∈ ball lam₀ ε) :
    HasDerivAt (struveLO_I r g m)
      (-(m : ℂ) * struveLO_I r (fun t => g t * sinh t) (m + 1) lam) lam := by
  have h := struveLO_hasDerivAt_circleIntegral (isCompact_closedBall lam₀ ε)
    (closedBall_mem_nhds_of_mem hlam) (r := r)
    (F := fun w t => g t * ((t + w * sinh t) ^ m)⁻¹)
    (F' := fun w t => -(m : ℂ) * (g t * sinh t * ((t + w * sinh t) ^ (m + 1))⁻¹))
    (struveLO_continuousOn hr hG hg m)
    (continuousOn_const.mul (struveLO_continuousOn hr hG (hg.mul continuous_sinh) (m + 1)))
    (fun z hz θ => by
      obtain ⟨h1, h2⟩ := struveLO_circleMap_mem hr θ
      exact struveLO_hasDerivAt_recip_pow _ _ _ m (struveLO_u_ne hG hz h1 h2))
  rw [circleIntegral.integral_const_mul] at h
  exact h

/-- The exact-derivative identity behind the recurrence: with `u = t + λ sinh t`,
`λ² n(n+1) sinh² t u^{-n-2} - λ n sinh t u^{-n-1} - (1-λ²) n(n+1) u^{-n-2}` is the
`t`-derivative of `-n (λ cosh t - 1) u^{-n-1}`. -/
lemma struveLO_hasDerivAt_exact (lam : ℂ) (n : ℕ) {t : ℂ} (h : t + lam * sinh t ≠ 0) :
    HasDerivAt (fun t => -(n : ℂ) * (lam * cosh t - 1) * ((t + lam * sinh t) ^ (n + 1))⁻¹)
      (lam ^ 2 * (n * (n + 1)) * (1 * sinh t * sinh t * ((t + lam * sinh t) ^ (n + 1 + 1))⁻¹) -
        lam * n * (1 * sinh t * ((t + lam * sinh t) ^ (n + 1))⁻¹) -
        (1 - lam ^ 2) * (n * (n + 1)) * (1 * ((t + lam * sinh t) ^ (n + 2))⁻¹)) t := by
  have hu : HasDerivAt (fun t => t + lam * sinh t) (1 + lam * cosh t) t :=
    (hasDerivAt_id t).add ((hasDerivAt_sinh t).const_mul lam)
  have hv : HasDerivAt (fun t => -(n : ℂ) * (lam * cosh t - 1)) (-(n : ℂ) * (lam * sinh t)) t :=
    (((hasDerivAt_cosh t).const_mul lam).sub_const 1).const_mul _
  have := hv.mul ((hu.inv h).pow (n + 1))
  simp only [← inv_pow]
  convert this using 1
  simp only [Pi.pow_apply, Pi.inv_apply, div_eq_mul_inv, ← inv_pow, Nat.add_sub_cancel]
  push_cast
  linear_combination (-(n : ℂ) * (n + 1) * (t + lam * sinh t)⁻¹ ^ (n + 2) * lam ^ 2) * cosh_sq t

/-- Circle integrability of the integrands on a good disc. -/
lemma struveLO_circleIntegrable {r ε : ℝ} {lam₀ : ℂ} (hr : 0 < r) (hG : struveLO_Good r ε lam₀)
    {g : ℂ → ℂ} (hg : Continuous g) (m : ℕ) {lam : ℂ} (hlam : lam ∈ closedBall lam₀ ε) (c : ℂ) :
    CircleIntegrable (fun t => c * (g t * ((t + lam * sinh t) ^ m)⁻¹)) 0 r := by
  refine ContinuousOn.circleIntegrable hr.le (continuousOn_const.mul (hg.continuousOn.mul
    (ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) fun t ht => pow_ne_zero _ ?_)))
  exact struveLO_u_ne hG hlam (sphere_subset_closedBall ht) (ne_of_mem_sphere ht hr.ne')

/-- The recurrence identity for the circle integrals:
`λ² n(n+1) I(sinh², n+2) - λ n I(sinh, n+1) = (1-λ²) n(n+1) I(1, n+2)`. -/
theorem struveLO_recurrence {r ε : ℝ} {lam₀ : ℂ} (hr : 0 < r) (hG : struveLO_Good r ε lam₀)
    (n : ℕ) {lam : ℂ} (hlam : lam ∈ closedBall lam₀ ε) :
    lam ^ 2 * (n * (n + 1)) * struveLO_I r (fun t => 1 * sinh t * sinh t) (n + 1 + 1) lam -
      lam * n * struveLO_I r (fun t => 1 * sinh t) (n + 1) lam =
      (1 - lam ^ 2) * (n * (n + 1)) * struveLO_I r (fun _ => 1) (n + 2) lam := by
  have h0 := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr.le (c := 0)
    (fun z hz => (struveLO_hasDerivAt_exact lam n (struveLO_u_ne hG hlam
      (sphere_subset_closedBall hz) (ne_of_mem_sphere hz hr.ne'))).hasDerivWithinAt)
  have i1 := struveLO_circleIntegrable hr hG (g := fun t => 1 * sinh t * sinh t) (by fun_prop)
    (n + 1 + 1) hlam (lam ^ 2 * (n * (n + 1)))
  have i2 := struveLO_circleIntegrable hr hG (g := fun t => 1 * sinh t) (by fun_prop) (n + 1) hlam
    (lam * n)
  have i3 := struveLO_circleIntegrable hr hG (g := fun _ => 1) continuous_const (n + 2) hlam
    ((1 - lam ^ 2) * (n * (n + 1)))
  have e1 := circleIntegral.integral_sub (i1.sub i2) i3
  simp only [Pi.sub_apply] at e1
  rw [e1, circleIntegral.integral_sub i1 i2,
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
    circleIntegral.integral_const_mul] at h0
  simp only [struveLO_I]
  linear_combination h0

/-- Base case: `∮ (t + λ sinh t)^{-1} dt = 2πi/(1+λ)` on a good disc. -/
theorem struveLO_I_one {r ε : ℝ} {lam₀ : ℂ} (hr : 0 < r) (hG : struveLO_Good r ε lam₀)
    {lam : ℂ} (hlam : lam ∈ closedBall lam₀ ε) :
    struveLO_I r (fun _ => 1) 1 lam = 2 * π * I / (1 + lam) := by
  have hd : DifferentiableOn ℂ (fun t => (1 + lam * dslope sinh 0 t)⁻¹) (closedBall 0 r) :=
    ((differentiableOn_const _).add ((differentiableOn_const _).mul
      struveLO_differentiable_dslope.differentiableOn)).inv fun t ht => hG lam hlam t ht
  have h := hd.circleIntegral_sub_inv_smul (mem_ball_self hr)
  rw [struveLO_dslope_zero, mul_one] at h
  rw [struveLO_I, circleIntegral.integral_congr hr.le (g := fun t =>
    (t - 0)⁻¹ • (1 + lam * dslope sinh 0 t)⁻¹), h, smul_eq_mul, div_eq_mul_inv]
  intro t ht
  simp only [one_mul, pow_one, sub_zero, smul_eq_mul]
  rw [struveLO_sinh_eq t, show t + lam * (t * dslope sinh 0 t) = t * (1 + lam * dslope sinh 0 t) by
    ring, mul_inv]

/-! ### Complex binomial remainders -/

/-- Binomial coefficient `a(a-1)⋯(a-j+1)/j!` for complex `a`. -/
def struveLO_b (a : ℂ) (j : ℕ) : ℂ := (∏ r ∈ Finset.range j, (a - r)) / (j.factorial : ℂ)

/-- Complex binomial remainder `(1+u)^a - ∑_{j<N} (a choose j) u^j` for real `u`. -/
def struveLO_R (a : ℂ) (N : ℕ) (u : ℝ) : ℂ :=
  (1 + (u : ℂ)) ^ a - ∑ j ∈ Finset.range N, struveLO_b a j * (u : ℂ) ^ j

/-- `(j+1) (a choose j+1) = a (a-1 choose j)`. -/
lemma struveLO_succ_mul_b (a : ℂ) (j : ℕ) :
    ((j + 1 : ℕ) : ℂ) * struveLO_b a (j + 1) = a * struveLO_b (a - 1) j := by
  unfold struveLO_b
  rw [Finset.prod_range_succ', Nat.factorial_succ]
  push_cast
  have : ∏ r ∈ Finset.range j, (a - ((r : ℂ) + 1)) = ∏ r ∈ Finset.range j, (a - 1 - r) :=
    Finset.prod_congr rfl fun r _ => by ring
  rw [this]
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  field_simp
  ring

/-- Derivative of the binomial remainder in `u`. -/
lemma struveLO_hasDerivAt_R (a : ℂ) (N : ℕ) {u : ℝ} (hu : -1 < u) :
    HasDerivAt (struveLO_R a (N + 1)) (a * struveLO_R (a - 1) N u) u := by
  have hpos : (0 : ℝ) < 1 + u := by linarith
  have h1 : HasDerivAt (fun x : ℝ => (1 + (x : ℂ)) ^ a) (a * (1 + (u : ℂ)) ^ (a - 1)) u := by
    have hz : (1 + (u : ℂ)) ∈ slitPlane := by
      rw [← ofReal_one, ← ofReal_add]; exact ofReal_mem_slitPlane.2 hpos
    have hc := ((hasDerivAt_id (u : ℂ)).const_add 1).cpow_const (c := a) hz
    simpa using hc.comp_ofReal
  have h2 : HasDerivAt (fun x : ℝ => ∑ j ∈ Finset.range (N + 1), struveLO_b a j * (x : ℂ) ^ j)
      (∑ j ∈ Finset.range N, a * struveLO_b (a - 1) j * (u : ℂ) ^ j) u := by
    have hs := HasDerivAt.fun_sum (u := Finset.range (N + 1)) (fun j _ =>
      ((((hasDerivAt_id u).ofReal_comp).pow j).const_mul (struveLO_b a j)))
    convert hs using 1
    · funext x; simp
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, id]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← struveLO_succ_mul_b]
    simp only [Nat.add_sub_cancel, ofReal_one, mul_one]
    ring
  have := h1.sub h2
  convert this using 1
  · funext x; simp [struveLO_R]
  simp only [struveLO_R, mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The remainder after at least one term vanishes at `0`. -/
lemma struveLO_R_succ_zero (a : ℂ) (N : ℕ) : struveLO_R a (N + 1) 0 = 0 := by
  simp [struveLO_R, Finset.sum_range_succ', struveLO_b]

/-- Bound for the binomial remainder: for `N ≤ re a` and `u > -1`,
`|R_N(a, u)| ≤ ∏_{i<N} |a - i| · |u|^N · (1 + max u 0)^{re a - N}`. -/
theorem struveLO_norm_R_le : ∀ (N : ℕ) (a : ℂ), (N : ℝ) ≤ a.re → ∀ u : ℝ, -1 < u →
    ‖struveLO_R a N u‖ ≤ (∏ i ∈ Finset.range N, ‖a - i‖) * |u| ^ N *
      (1 + max u 0) ^ (a.re - N) := by
  intro N
  induction N with
  | zero =>
    intro a ha u hu
    simp only [struveLO_R, Finset.range_zero, Finset.sum_empty, sub_zero, Finset.prod_empty,
      pow_zero, one_mul, Nat.cast_zero]
    have hpos : (0 : ℝ) < 1 + u := by linarith
    rw [← ofReal_one, ← ofReal_add, norm_cpow_eq_rpow_re_of_pos hpos]
    exact Real.rpow_le_rpow hpos.le (by linarith [le_max_left u 0]) (by simpa using ha)
  | succ N ih =>
    intro a ha u hu
    set C : ℝ := (∏ i ∈ Finset.range (N + 1), ‖a - i‖) * |u| ^ N * (1 + max u 0) ^ (a.re - (N + 1 : ℕ))
      with hC
    have hs : Convex ℝ (uIcc 0 u) := convex_uIcc 0 u
    have hmem : ∀ v ∈ uIcc 0 u, -1 < v ∧ |v| ≤ |u| ∧ max v 0 ≤ max u 0 := by
      intro v hv
      rcases le_total 0 u with h | h
      · rw [uIcc_of_le h] at hv
        exact ⟨by linarith [hv.1], by rw [abs_of_nonneg hv.1, abs_of_nonneg h]; exact hv.2,
          max_le_max hv.2 le_rfl⟩
      · rw [uIcc_of_ge h] at hv
        refine ⟨by linarith [hv.1], by rw [abs_of_nonpos hv.2, abs_of_nonpos h]; linarith [hv.1], ?_⟩
        rw [max_eq_right hv.2, max_eq_right h]
    have hd : ∀ v ∈ uIcc 0 u, HasDerivWithinAt (struveLO_R a (N + 1))
        (a * struveLO_R (a - 1) N v) (uIcc 0 u) v :=
      fun v hv => (struveLO_hasDerivAt_R a N (hmem v hv).1).hasDerivWithinAt
    have hb : ∀ v ∈ uIcc 0 u, ‖a * struveLO_R (a - 1) N v‖ ≤ C := by
      intro v hv
      obtain ⟨hv1, hv2, hv3⟩ := hmem v hv
      have hre : (N : ℝ) ≤ (a - 1).re := by
        simp only [sub_re, one_re]; push_cast at ha; linarith
      have := ih (a - 1) hre v hv1
      rw [norm_mul]
      have hexp : (a - 1).re - N = a.re - (N + 1 : ℕ) := by simp; ring
      rw [hexp] at this
      have he : 0 ≤ a.re - (N + 1 : ℕ) := by linarith
      calc ‖a‖ * ‖struveLO_R (a - 1) N v‖
          ≤ ‖a‖ * ((∏ i ∈ Finset.range N, ‖a - 1 - i‖) * |v| ^ N *
              (1 + max v 0) ^ (a.re - (N + 1 : ℕ))) := by gcongr
        _ ≤ ‖a‖ * ((∏ i ∈ Finset.range N, ‖a - 1 - i‖) * |u| ^ N *
              (1 + max u 0) ^ (a.re - (N + 1 : ℕ))) := by
            gcongr
        _ = C := by
            rw [hC, Finset.prod_range_succ']
            have : ∏ i ∈ Finset.range N, ‖a - ((i + 1 : ℕ) : ℂ)‖ =
                ∏ i ∈ Finset.range N, ‖a - 1 - i‖ :=
              Finset.prod_congr rfl fun i _ => by push_cast; ring_nf
            rw [this]; simp; ring
    have key := hs.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (left_mem_uIcc) (right_mem_uIcc)
    rw [struveLO_R_succ_zero, sub_zero, Real.norm_eq_abs, sub_zero] at key
    calc ‖struveLO_R a (N + 1) u‖ ≤ C * |u| := key
      _ = _ := by rw [hC, pow_succ]; ring

/-! ### The Laplace integral of `𝐊_ν` with a binomial expansion -/

/-- `1 + t² ≤ e^t` for `t ≥ 0`. -/
lemma struveLO_one_add_sq_le_exp {t : ℝ} (ht : 0 ≤ t) : 1 + t ^ 2 ≤ Real.exp t := by
  have h := Real.sum_le_exp_of_nonneg ht 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [sq_nonneg (t - 3 / 2), sq_nonneg t, mul_nonneg ht (sq_nonneg (t - 3/2))]

/-- Laplace transform of an even power: `∫₀^∞ e^{-zt} t^{n} dt = n!/z^{n+1}` for `re z > 0`. -/
lemma struveLO_integral_exp_mul_pow (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), exp (-z * t) * (t : ℂ) ^ n = (n.factorial : ℂ) / z ^ (n + 1) := by
  have h := integral_cpow_mul_cexp_neg_mul_Ioi (s := (n : ℂ) + 1) (by simp; positivity) hz
  have hG : Gamma ((n : ℂ) + 1) = n.factorial := Complex.Gamma_nat_eq_factorial n
  rw [hG, show -((n : ℂ) + 1) = -((n + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg, cpow_natCast] at h
  rw [div_eq_mul_inv, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [add_sub_cancel_right, cpow_natCast]
  ring_nf

/-- Integrability of `e^{-zt} t^n` on `(0, ∞)` for `re z > 0`. -/
lemma struveLO_integrableOn_exp_mul_pow (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => exp (-z * t) * (t : ℂ) ^ n) (Ioi 0) := by
  have hb := integrableOn_exp_neg_mul_mul_rpow_sub_one (s := (n : ℝ) + 1) (by positivity) hz
  refine hb.mono' (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
    fun t ht => ?_))
  have ht : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_exp, norm_pow, norm_real, Real.norm_of_nonneg ht.le,
    add_sub_cancel_right, Real.rpow_natCast]
  simp [mul_comm]

/-- The `𝐊_ν` Laplace integral with its binomial expansion: for `N ≤ re a < re z`,
`∫₀^∞ e^{-zt} (1+t²)^a dt = ∑_{j<N} (a choose j) (2j)!/z^{2j+1} + E` with
`|E| ≤ ∏_{i<N} |a-i| · (2N)!/(re z - re a)^{2N+1}`. -/
theorem struveLO_K_integral_bound (N : ℕ) {z a : ℂ} (ha : (N : ℝ) ≤ a.re) (hza : a.re < z.re) :
    ‖(∫ t in Ioi (0 : ℝ), exp (-z * t) * (1 + (t : ℂ) ^ 2) ^ a) -
        ∑ j ∈ Finset.range N, struveLO_b a j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)‖ ≤
      (∏ i ∈ Finset.range N, ‖a - i‖) * (2 * N).factorial / (z.re - a.re) ^ (2 * N + 1) := by
  set c := z.re - a.re with hc
  have hc0 : 0 < c := by linarith
  have hz : 0 < z.re := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  set P := ∏ i ∈ Finset.range N, ‖a - i‖ with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hpt : ∀ t : ℝ, exp (-z * t) * (1 + (t : ℂ) ^ 2) ^ a =
      ∑ j ∈ Finset.range N, struveLO_b a j * (exp (-z * t) * (t : ℂ) ^ (2 * j)) +
        exp (-z * t) * struveLO_R a N (t ^ 2) := by
    intro t
    simp only [struveLO_R, ofReal_pow, mul_sub, Finset.mul_sum]
    have : ∑ j ∈ Finset.range N, struveLO_b a j * (exp (-z * t) * (t : ℂ) ^ (2 * j)) =
        ∑ i ∈ Finset.range N, exp (-z * t) * (struveLO_b a i * ((t : ℂ) ^ 2) ^ i) :=
      Finset.sum_congr rfl fun j _ => by rw [← pow_mul]; ring
    rw [this]; ring
  have hRc : Continuous fun t : ℝ => exp (-z * t) * struveLO_R a N (t ^ 2) := by
    unfold struveLO_R
    refine (by fun_prop : Continuous fun t : ℝ => exp (-z * t)).mul (Continuous.sub ?_ (by fun_prop))
    refine Continuous.cpow (by fun_prop) continuous_const fun t => ?_
    rw [← ofReal_one, ← ofReal_add]; exact ofReal_mem_slitPlane.2 (by positivity)
  have hbd : ∀ t ∈ Ioi (0 : ℝ), ‖exp (-z * t) * struveLO_R a N (t ^ 2)‖ ≤
      P * (Real.exp (-c * t) * t ^ (((2 * N : ℕ) : ℝ) + 1 - 1)) := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    have hR := struveLO_norm_R_le N a ha (t ^ 2) (by nlinarith)
    rw [abs_of_nonneg (by positivity), max_eq_left (by positivity)] at hR
    have he : 0 ≤ a.re - N := by linarith
    have h1 : (1 + t ^ 2) ^ (a.re - N) ≤ Real.exp (a.re * t) := by
      calc (1 + t ^ 2) ^ (a.re - N) ≤ (Real.exp t) ^ (a.re - N) :=
            Real.rpow_le_rpow (by positivity) (struveLO_one_add_sq_le_exp ht.le) he
        _ = Real.exp ((a.re - N) * t) := by rw [← Real.exp_mul]; ring_nf
        _ ≤ Real.exp (a.re * t) := Real.exp_le_exp.2 (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
    rw [norm_mul, Complex.norm_exp, add_sub_cancel_right, Real.rpow_natCast]
    have hre : (-z * t).re = -z.re * t := by simp
    rw [hre]
    calc Real.exp (-z.re * t) * ‖struveLO_R a N (t ^ 2)‖
        ≤ Real.exp (-z.re * t) * (P * (t ^ 2) ^ N * Real.exp (a.re * t)) := by
          gcongr
          exact hR.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
      _ = P * (Real.exp (-c * t) * t ^ (2 * N)) := by
          rw [hc, ← pow_mul]
          have : Real.exp (-z.re * t) * Real.exp (a.re * t) = Real.exp (-(z.re - a.re) * t) := by
            rw [← Real.exp_add]; ring_nf
          linear_combination (P * t ^ (2 * N)) * this
  have hgint : IntegrableOn (fun t : ℝ => P * (Real.exp (-c * t) * t ^ (((2 * N : ℕ) : ℝ) + 1 - 1)))
      (Ioi 0) := (integrableOn_exp_neg_mul_mul_rpow_sub_one (by positivity) hc0).const_mul P
  have hRint : IntegrableOn (fun t : ℝ => exp (-z * t) * struveLO_R a N (t ^ 2)) (Ioi 0) :=
    hgint.mono' hRc.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbd))
  have hjint : ∀ j ∈ Finset.range N, IntegrableOn
      (fun t : ℝ => struveLO_b a j * (exp (-z * t) * (t : ℂ) ^ (2 * j))) (Ioi 0) :=
    fun j _ => (struveLO_integrableOn_exp_mul_pow (2 * j) hz).const_mul _
  have hsplit : (∫ t in Ioi (0 : ℝ), exp (-z * t) * (1 + (t : ℂ) ^ 2) ^ a) =
      ∑ j ∈ Finset.range N, struveLO_b a j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1) +
        ∫ t in Ioi (0 : ℝ), exp (-z * t) * struveLO_R a N (t ^ 2) := by
    simp_rw [hpt]
    rw [integral_add (integrable_finsetSum _ hjint) hRint, integral_finsetSum _ hjint]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, struveLO_integral_exp_mul_pow _ hz, mul_div_assoc]
  rw [hsplit, add_sub_cancel_left]
  calc ‖∫ t in Ioi (0 : ℝ), exp (-z * t) * struveLO_R a N (t ^ 2)‖
      ≤ ∫ t in Ioi (0 : ℝ), P * (Real.exp (-c * t) * t ^ (((2 * N : ℕ) : ℝ) + 1 - 1)) :=
        norm_integral_le_of_norm_le hgint
          ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbd))
    _ = P * (2 * N).factorial / c ^ (2 * N + 1) := by
        rw [integral_const_mul, integral_exp_neg_mul_mul_rpow_sub_one (by positivity) hc0,
          Real.Gamma_nat_eq_factorial, Real.rpow_neg hc0.le,
          show (((2 * N : ℕ) : ℝ) + 1) = ((2 * N + 1 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
        field_simp

/-! ### The integral of `𝐌_ν` with a binomial expansion -/

/-- `x^m/m! ≤ e^x` for `x ≥ 0`. -/
lemma struveLO_pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    x ^ m / m.factorial ≤ Real.exp x := by
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx (m + 1))
  exact Finset.single_le_sum (f := fun i => x ^ i / i.factorial)
    (fun i _ => by positivity) (Finset.self_mem_range_succ m)

/-- `e^{-y} ≤ m!/y^m` for `y > 0`. -/
lemma struveLO_exp_neg_le {y : ℝ} (hy : 0 < y) (m : ℕ) :
    Real.exp (-y) ≤ m.factorial / y ^ m := by
  have h := struveLO_pow_div_factorial_le_exp hy.le m
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
  exact h

/-- Tail bound: `|∫₁^∞ e^{-zt} tⁿ dt| ≤ e^{-c/2} n! (2/c)^{n+1}` for `c = re z > 0`. -/
lemma struveLO_norm_integral_Ioi_one_le (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ‖∫ t in Ioi (1 : ℝ), exp (-z * t) * (t : ℂ) ^ n‖ ≤
      Real.exp (-(z.re / 2)) * (n.factorial * (2 / z.re) ^ (n + 1)) := by
  set c := z.re
  have hc2 : 0 < c / 2 := by positivity
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-(c / 2)) *
      (Real.exp (-(c / 2) * t) * t ^ ((n : ℝ) + 1 - 1))) (Ioi 0) :=
    (integrableOn_exp_neg_mul_mul_rpow_sub_one (by positivity) hc2).const_mul _
  have hbd : ∀ t ∈ Ioi (1 : ℝ), ‖exp (-z * t) * (t : ℂ) ^ n‖ ≤ Real.exp (-(c / 2)) *
      (Real.exp (-(c / 2) * t) * t ^ ((n : ℝ) + 1 - 1)) := by
    intro t ht
    have ht : (1 : ℝ) < t := ht
    rw [norm_mul, Complex.norm_exp, norm_pow, norm_real, Real.norm_of_nonneg (by linarith),
      add_sub_cancel_right, Real.rpow_natCast, ← mul_assoc, ← Real.exp_add]
    gcongr
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    nlinarith
  calc ‖∫ t in Ioi (1 : ℝ), exp (-z * t) * (t : ℂ) ^ n‖
      ≤ ∫ t in Ioi (1 : ℝ), Real.exp (-(c / 2)) *
          (Real.exp (-(c / 2) * t) * t ^ ((n : ℝ) + 1 - 1)) :=
        norm_integral_le_of_norm_le (hg.mono_set (Ioi_subset_Ioi zero_le_one))
          ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbd))
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(c / 2)) *
          (Real.exp (-(c / 2) * t) * t ^ ((n : ℝ) + 1 - 1)) := by
        refine setIntegral_mono_set hg ((ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall fun t ht => ?_)) (Eventually.of_forall
            (Ioi_subset_Ioi zero_le_one))
        have ht : (0 : ℝ) < t := ht
        positivity
    _ = _ := by
        rw [integral_const_mul, integral_exp_neg_mul_mul_rpow_sub_one (by positivity) hc2,
          Real.Gamma_nat_eq_factorial, Real.rpow_neg hc2.le,
          show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
        rw [show 2 / c = (c / 2)⁻¹ by field_simp, inv_pow]

/-- The `𝐌_ν` integral with its binomial expansion: for `N ≤ re a` and `re z > 0`,
`∫₀¹ e^{-zt} (1-t²)^a dt = ∑_{j<N} (a choose j) (-1)^j (2j)!/z^{2j+1} + E`, where `E` is bounded by
`∏_{i<N} |a-i| (2N)!/(re z)^{2N+1}` plus exponentially small tails. -/
theorem struveLO_M_integral_bound (N : ℕ) {z a : ℂ} (ha : (N : ℝ) ≤ a.re) (hz : 0 < z.re) :
    ‖(∫ t in (0 : ℝ)..1, exp (-z * t) * (1 - (t : ℂ) ^ 2) ^ a) -
        ∑ j ∈ Finset.range N, struveLO_b a j * (-1) ^ j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1)‖ ≤
      (∏ i ∈ Finset.range N, ‖a - i‖) * (2 * N).factorial / z.re ^ (2 * N + 1) +
        ∑ j ∈ Finset.range N, ‖struveLO_b a j‖ *
          (Real.exp (-(z.re / 2)) * ((2 * j).factorial * (2 / z.re) ^ (2 * j + 1))) := by
  set c := z.re with hc
  set P := ∏ i ∈ Finset.range N, ‖a - i‖ with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun _ _ => norm_nonneg _
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hpt : ∀ t : ℝ, exp (-z * t) * (1 - (t : ℂ) ^ 2) ^ a =
      ∑ j ∈ Finset.range N, struveLO_b a j * (-1) ^ j * (exp (-z * t) * (t : ℂ) ^ (2 * j)) +
        exp (-z * t) * struveLO_R a N (-t ^ 2) := by
    intro t
    simp only [struveLO_R, ofReal_neg, ofReal_pow, mul_sub, Finset.mul_sum, ← sub_eq_add_neg]
    have : ∑ j ∈ Finset.range N, struveLO_b a j * (-1) ^ j * (exp (-z * t) * (t : ℂ) ^ (2 * j)) =
        ∑ i ∈ Finset.range N, exp (-z * t) * (struveLO_b a i * (-(t : ℂ) ^ 2) ^ i) :=
      Finset.sum_congr rfl fun j _ => by rw [neg_pow ((t : ℂ) ^ 2), ← pow_mul]; ring
    rw [this]; ring
  have hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ‖exp (-z * t) * struveLO_R a N (-t ^ 2)‖ ≤
      P * (Real.exp (-c * t) * t ^ (((2 * N : ℕ) : ℝ) + 1 - 1)) := by
    intro t ht
    have hR := struveLO_norm_R_le N a ha (-t ^ 2) (by nlinarith [ht.1, ht.2])
    rw [abs_neg, abs_of_nonneg (by positivity), max_eq_right (by nlinarith), add_zero,
      Real.one_rpow, mul_one, ← pow_mul] at hR
    rw [norm_mul, Complex.norm_exp, add_sub_cancel_right, Real.rpow_natCast]
    have hre : (-z * t).re = -c * t := by simp [hc]
    rw [hre]
    calc Real.exp (-c * t) * ‖struveLO_R a N (-t ^ 2)‖ ≤ Real.exp (-c * t) * (P * t ^ (2 * N)) := by
          gcongr
      _ = _ := by ring
  have hgint : IntegrableOn (fun t : ℝ => P * (Real.exp (-c * t) * t ^ (((2 * N : ℕ) : ℝ) + 1 - 1)))
      (Ioi 0) := (integrableOn_exp_neg_mul_mul_rpow_sub_one (by positivity) hz).const_mul P
  have hRc : ContinuousOn (fun t : ℝ => exp (-z * t) * struveLO_R a N (-t ^ 2)) (Ioo 0 1) := by
    unfold struveLO_R
    refine ((by fun_prop : Continuous fun t : ℝ => exp (-z * t)).continuousOn).mul
      (ContinuousOn.sub ?_ (by fun_prop))
    refine ContinuousOn.cpow (by fun_prop) continuousOn_const fun t ht => ?_
    rw [← ofReal_one, ← ofReal_add]; exact ofReal_mem_slitPlane.2 (by nlinarith [ht.1, ht.2])
  have hRint : IntegrableOn (fun t : ℝ => exp (-z * t) * struveLO_R a N (-t ^ 2)) (Ioo 0 1) :=
    (hgint.mono_set Ioo_subset_Ioi_self).mono' (hRc.aestronglyMeasurable measurableSet_Ioo)
      ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hbd))
  have hjI : ∀ j : ℕ, IntegrableOn (fun t : ℝ => exp (-z * t) * (t : ℂ) ^ (2 * j)) (Ioi 0) :=
    fun j => struveLO_integrableOn_exp_mul_pow (2 * j) hz
  have hjint : ∀ j ∈ Finset.range N, IntegrableOn
      (fun t : ℝ => struveLO_b a j * (-1) ^ j * (exp (-z * t) * (t : ℂ) ^ (2 * j))) (Ioo 0 1) :=
    fun j _ => ((hjI j).mono_set Ioo_subset_Ioi_self).const_mul _
  have hpiece : ∀ j : ℕ, ∫ t in Ioo (0 : ℝ) 1, exp (-z * t) * (t : ℂ) ^ (2 * j) =
      ((2 * j).factorial : ℂ) / z ^ (2 * j + 1) - ∫ t in Ioi (1 : ℝ), exp (-z * t) * (t : ℂ) ^ (2 * j) := by
    intro j
    have hu := setIntegral_union (μ := volume) (f := fun t : ℝ => exp (-z * t) * (t : ℂ) ^ (2 * j))
      (s := Ioo 0 1) (t := Ici 1)
      (Set.disjoint_left.2 fun x hx hx' => by simp only [mem_Ioo, mem_Ici] at hx hx'; linarith)
      measurableSet_Ici ((hjI j).mono_set Ioo_subset_Ioi_self)
      ((hjI j).mono_set (Ici_subset_Ioi.2 zero_lt_one))
    rw [Ioo_union_Ici_eq_Ioi zero_lt_one, struveLO_integral_exp_mul_pow _ hz,
      integral_Ici_eq_integral_Ioi] at hu
    rw [hu]; ring
  have hsplit : (∫ t in Ioo (0 : ℝ) 1, exp (-z * t) * (1 - (t : ℂ) ^ 2) ^ a) -
      ∑ j ∈ Finset.range N, struveLO_b a j * (-1) ^ j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1) =
      -(∑ j ∈ Finset.range N, struveLO_b a j * (-1) ^ j *
          ∫ t in Ioi (1 : ℝ), exp (-z * t) * (t : ℂ) ^ (2 * j)) +
        ∫ t in Ioo (0 : ℝ) 1, exp (-z * t) * struveLO_R a N (-t ^ 2) := by
    simp_rw [hpt]
    rw [integral_add (integrable_finsetSum _ hjint) hRint, integral_finsetSum _ hjint]
    simp_rw [integral_const_mul, hpiece, mul_sub, Finset.sum_sub_distrib]
    have : ∀ j ∈ Finset.range N, struveLO_b a j * (-1) ^ j * (((2 * j).factorial : ℂ) / z ^ (2 * j + 1)) =
        struveLO_b a j * (-1) ^ j * ((2 * j).factorial : ℂ) / z ^ (2 * j + 1) :=
      fun j _ => by ring
    rw [Finset.sum_congr rfl this]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [add_comm]
  gcongr
  · calc ‖∫ t in Ioo (0 : ℝ) 1, exp (-z * t) * struveLO_R a N (-t ^ 2)‖
        ≤ ∫ t in Ioo (0 : ℝ) 1, P * (Real.exp (-c * t) * t ^ (((2 * N : ℕ) : ℝ) + 1 - 1)) :=
          norm_integral_le_of_norm_le (hgint.mono_set Ioo_subset_Ioi_self)
            ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hbd))
      _ ≤ ∫ t in Ioi (0 : ℝ), P * (Real.exp (-c * t) * t ^ (((2 * N : ℕ) : ℝ) + 1 - 1)) := by
          refine setIntegral_mono_set hgint ((ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun t ht => ?_)) (Eventually.of_forall Ioo_subset_Ioi_self)
          have ht : (0 : ℝ) < t := ht
          positivity
      _ = P * (2 * N).factorial / c ^ (2 * N + 1) := by
          rw [integral_const_mul, integral_exp_neg_mul_mul_rpow_sub_one (by positivity) hz,
            Real.Gamma_nat_eq_factorial, Real.rpow_neg hz.le,
            show (((2 * N : ℕ) : ℝ) + 1) = ((2 * N + 1 : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_natCast]
          field_simp
  · rw [norm_neg]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
    gcongr
    exact struveLO_norm_integral_Ioi_one_le (2 * j) hz

end DLMF.Struve