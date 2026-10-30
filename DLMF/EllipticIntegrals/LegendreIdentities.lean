/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.Symmetric
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Legendre's integrals: the statements of DLMF §19.2

The definitions of DLMF §19.2 are in `DLMF.EllipticIntegrals.Legendre`; this module states the
remaining content of §19.2:

* §19.2(i): the reduction of a general elliptic integrand `r(s, t)` to `ρ/s + σ` (19.2.1–19.2.3),
  as a field identity;
* §19.2(ii): `D = (F - E)/k²` (19.2.6), `D(k) = (K - E)/k²` (19.2.8), the parity and
  holomorphy of the principal `K`, `E` and `K'`, `E'` (prose), the integral forms of `K'`, `E'`
  (19.2.8_1, 19.2.8_2), the circular/hyperbolic alternation (prose) and the quasi-periodicity
  (19.2.10);
* §19.2(iii): Bulirsch's integrals as Legendre integrals (19.2.13–19.2.16);
* §19.2(iv): the function `R_C` (19.2.17–19.2.22), with ACQ19C's `symEllIntRC`.

Real amplitudes `φ` are used where DLMF's identities are path statements; the principal
domain `1 - k² ∈ ℂ \ (-∞, 0]` makes the integrand `(1 - k² sin²θ)^{∓1/2}` continuous for real `θ`.
The negative-real `R_C` formula is proved by evaluating the symmetrically truncated integral
with a logarithmic primitive. Mathlib's FTC lemmas for derivatives of constant sign provide
integrability on both sides, including the square-root singularity at the endpoint `x = 0`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### §19.2(i) General elliptic integrals -/

/-- DLMF 19.2.1–19.2.3: if `s² = P` (a cubic or quartic in `t`) then every rational function of
`s` and `t` with an odd power of `s`, written `(p₁ + p₂ s)/(p₃ + p₄ s)`, equals `ρ/s + σ` with
`ρ = (p₂p₃ - p₁p₄)P/(p₃² - p₄²P)` and `σ = (p₁p₃ - p₂p₄P)/(p₃² - p₄²P)` rational in `t`; so the
elliptic part of `∫ r(s, t) dt` is `∫ ρ(t)/s(t) dt`. Stated as an identity in any field. -/
@[dlmf 19.2.E2]
theorem ellipticIntegrand_eq {F : Type*} [Field F] (p₁ p₂ p₃ p₄ s P : F) (hs : s ^ 2 = P)
    (hs0 : s ≠ 0) (hden : p₃ ^ 2 - p₄ ^ 2 * P ≠ 0) :
    (p₁ + p₂ * s) / (p₃ + p₄ * s) =
      ((p₂ * p₃ - p₁ * p₄) * P / (p₃ ^ 2 - p₄ ^ 2 * P)) / s +
        (p₁ * p₃ - p₂ * p₄ * P) / (p₃ ^ 2 - p₄ ^ 2 * P) := by
  have h3 : p₃ + p₄ * s ≠ 0 := by
    intro h
    apply hden
    have : p₃ = -(p₄ * s) := by linear_combination h
    rw [this, ← hs]; ring
  rw [← hs] at hden ⊢
  rw [div_div, div_add_div _ _ (mul_ne_zero hden hs0) hden,
    div_eq_div_iff h3 (mul_ne_zero (mul_ne_zero hden hs0) hden)]
  ring

/-- DLMF 19.2.1 and 19.2.3 (terminology): `∫ r(s, t) dt` with `r` rational and `s²` a cubic or
quartic with simple zeros is an elliptic integral, and its elliptic part is `∫ ρ(t)/s(t) dt`;
the reduction is `ellipticIntegrand_eq`. -/
@[dlmf 19.2.E1, dlmf 19.2.E3]
theorem ellipticIntegrand_elliptic_part {F : Type*} [Field F] (p₁ p₂ p₃ p₄ s P : F)
    (hs : s ^ 2 = P) (hs0 : s ≠ 0) (hden : p₃ ^ 2 - p₄ ^ 2 * P ≠ 0) :
    ∃ ρ σ : F, (p₁ + p₂ * s) / (p₃ + p₄ * s) = ρ / s + σ :=
  ⟨_, _, ellipticIntegrand_eq p₁ p₂ p₃ p₄ s P hs hs0 hden⟩

/-! ### §19.2(ii) Legendre's integrals -/

/-- `x^{1/2} = x · x^{-1/2}` for every complex `x` (both sides vanish at `0`). -/
lemma ei19a_cpow_half_eq (x : ℂ) : x ^ (1 / 2 : ℂ) = x * x ^ (-(1 / 2 : ℂ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · conv_lhs => rw [show (1 / 2 : ℂ) = 1 + (-(1 / 2 : ℂ)) by ring]
    rw [cpow_add _ _ hx, cpow_one]

/-- DLMF 19.2.6: `D(φ, k) = (F(φ, k) - E(φ, k))/k²` for `k ≠ 0`, whenever the integrand of `F` is
integrable along the segment `[0, φ]` (Lean's integrals are totalized). -/
@[dlmf 19.2.E6]
theorem incEllIntDk_eq {φ k : ℂ} (hk : k ≠ 0)
    (hF : IntervalIntegrable
      (fun t : ℝ => φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ))) volume 0 1) :
    incEllIntDk φ k = (incEllIntFk φ k - incEllIntEk φ k) / k ^ 2 := by
  have hb : ContinuousOn (fun t : ℝ => 1 - k ^ 2 * Complex.sin (t * φ) ^ 2) (uIcc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ => 1 - k ^ 2 * Complex.sin (t * φ) ^ 2).continuousOn
  have hE : IntervalIntegrable (fun t : ℝ => (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) *
      (φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ)))) volume 0 1 :=
    hF.continuousOn_mul hb
  rw [eq_div_iff (pow_ne_zero 2 hk), incEllIntDk, incEllIntFk, incEllIntEk, ei19a_segmentIntegral,
    ei19a_segmentIntegral, ei19a_segmentIntegral, ← intervalIntegral.integral_mul_const]
  have h1 : (fun t : ℝ => φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (1 / 2 : ℂ)) =
      fun t : ℝ => (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) *
        (φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
    funext t; rw [ei19a_cpow_half_eq]; ring
  rw [h1, ← intervalIntegral.integral_sub hF hE]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- DLMF 19.2.6 for real amplitude in the principal domain `1 - k² ∈ ℂ \ (-∞, 0]`, `k ≠ 0`. -/
@[dlmf 19.2.E6]
theorem incEllIntDk_eq_of_real {k : ℂ} (hk : k ≠ 0) (hk1 : 1 - k ^ 2 ∈ slitPlane) (φ : ℝ) :
    incEllIntDk φ k = (incEllIntFk φ k - incEllIntEk φ k) / k ^ 2 := by
  refine incEllIntDk_eq hk (Continuous.intervalIntegrable ?_ _ _)
  refine continuous_const.mul (Continuous.cpow (by fun_prop) continuous_const fun t => ?_)
  have := ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk1 (t * φ)
  simpa using this

/-- DLMF 19.2.8: `D(k) = (K(k) - E(k))/k²` in the principal domain `1 - k² ∈ ℂ \ (-∞, 0]`,
`k ≠ 0`. -/
@[dlmf 19.2.E8]
theorem compEllIntDk_eq {k : ℂ} (hk : k ≠ 0) (hk1 : 1 - k ^ 2 ∈ slitPlane) :
    compEllIntDk k = (compEllIntKk k - compEllIntEk k) / k ^ 2 := by
  have h := incEllIntDk_eq_of_real hk hk1 (π / 2)
  push_cast at h
  rw [compEllIntDk, h, compEllIntKk_eq_incEllIntFk, compEllIntEk]

/-- DLMF §19.2(ii): the principal values of `K(k)` and `E(k)` are even functions. -/
@[dlmf 19.2.ii]
theorem compEllIntKk_neg (k : ℂ) : compEllIntKk (-k) = compEllIntKk k := by
  simp [compEllIntKk]

/-- DLMF §19.2(ii): the principal value of `E(k)` is even. -/
@[dlmf 19.2.ii]
theorem compEllIntEk_neg (k : ℂ) : compEllIntEk (-k) = compEllIntEk k := by
  simp [compEllIntEk, incEllIntEk]

/-- `∫₀^b (1 - k² sin²θ)^s dθ` is holomorphic in `k` on the principal domain
`1 - k² ∈ ℂ \ (-∞, 0]`, for every exponent `s` and real `b`. -/
lemma p19lR1_differentiableOn_integral_cpow (s : ℂ) (b : ℝ) :
    DifferentiableOn ℂ (fun k : ℂ => ∫ θ in (0 : ℝ)..b, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ s)
      {k | 1 - k ^ 2 ∈ slitPlane} := by
  have hU : IsOpen {k : ℂ | 1 - k ^ 2 ∈ slitPlane} :=
    isOpen_slitPlane.preimage (by fun_prop)
  refine Complex.differentiableOn_intervalIntegral_of_locally_dominated hU 0 b ?_ ?_ ?_
  · intro k hk
    refine (Continuous.cpow (by fun_prop) continuous_const fun θ =>
      ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk θ).aestronglyMeasurable
  · refine Eventually.of_forall fun θ k hk => ?_
    have hd : DifferentiableAt ℂ (fun x : ℂ => 1 - x ^ 2 * (Real.sin θ : ℂ) ^ 2) k := by fun_prop
    exact (hd.cpow (differentiableAt_const s)
      (ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk θ)).differentiableWithinAt
  · intro k0 hk0
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU k0 hk0
    have hball : Metric.closedBall k0 (ε / 2) ⊆ {k : ℂ | 1 - k ^ 2 ∈ slitPlane} :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεU
    have hcomp : IsCompact (Metric.closedBall k0 (ε / 2) ×ˢ Icc (0 : ℝ) 1) :=
      (isCompact_closedBall _ _).prod isCompact_Icc
    have hcont : ContinuousOn (fun p : ℂ × ℝ => ‖(1 - p.1 ^ 2 * (p.2 : ℂ)) ^ s‖)
        (Metric.closedBall k0 (ε / 2) ×ˢ Icc (0 : ℝ) 1) := by
      refine ContinuousOn.norm (ContinuousOn.cpow (by fun_prop) continuousOn_const ?_)
      rintro ⟨k, u⟩ ⟨hk, hu⟩
      have := ei19a_one_sub_mul_mem_slitPlane (hball hk) hu.1 hu.2
      simpa using this
    obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
    refine ⟨Metric.closedBall k0 (ε / 2), Metric.closedBall_mem_nhds _ (by linarith),
      fun _ => M, ?_, Eventually.of_forall fun θ k hk => ?_⟩
    · have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) b)) :=
        isFiniteMeasure_restrict.2 (by
          rw [uIoc_eq_union]; exact (measure_union_le _ _).trans_lt
            (ENNReal.add_lt_top.2 ⟨measure_Ioc_lt_top, measure_Ioc_lt_top⟩) |>.ne)
      exact integrable_const M
    · have := hM (k, Real.sin θ ^ 2) ⟨hk, sq_nonneg _, Real.sin_sq_le_one θ⟩
      simpa using this

/-- DLMF §19.2(ii): the principal branches of `K(k)` and `E(k)` are holomorphic off
the cuts `(-∞, -1] ∪ [1, ∞)`, i.e. on `{k | 1 - k² ∈ ℂ \ (-∞, 0]}`. -/
@[dlmf 19.2.ii]
theorem differentiableOn_compEllIntKk_compEllIntEk :
    DifferentiableOn ℂ compEllIntKk {k | 1 - k ^ 2 ∈ slitPlane} ∧
      DifferentiableOn ℂ compEllIntEk {k | 1 - k ^ 2 ∈ slitPlane} := by
  refine ⟨p19lR1_differentiableOn_integral_cpow _ _, ?_⟩
  have h : compEllIntEk = fun k : ℂ => ∫ θ in (0 : ℝ)..(π / 2),
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) := funext compEllIntEk_eq_integral
  rw [h]; exact p19lR1_differentiableOn_integral_cpow _ _

/-- **Admitted.** DLMF §19.2(ii) and 19.2.9: `K'` and `E'` (defined by 19.2.9) are holomorphic on
`ℂ \ (-∞, 0]`: the branch point is `k = 0` and the principal branch is `|ph k| ≤ π`
(`cCompEllIntKk` is the analytic continuation of the literal integral from `Re k > 0`). -/
@[dlmf 19.2.ii]
theorem differentiableOn_cCompEllIntKk_cCompEllIntEk :
    DifferentiableOn ℂ cCompEllIntKk slitPlane ∧ DifferentiableOn ℂ cCompEllIntEk slitPlane := by
  sorry

/-- The substitution `t = sin θ`: `∫₀^{π/2} h(sin²θ) dθ = ∫₀¹ (1-t²)^{-1/2} h(t²) dt`. -/
lemma p19lR1_integral_sin_subst (h : ℂ → ℂ) :
    ∫ θ in (0 : ℝ)..(π / 2), h ((Real.sin θ : ℂ) ^ 2) =
      ∫ t in (0 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) * h ((t : ℂ) ^ 2) := by
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := (0 : ℝ)) (b := π / 2) (f := Real.sin) (f' := Real.cos)
    (g := fun t : ℝ => (1 - (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) * h ((t : ℂ) ^ 2))
    Real.continuous_sin.continuousOn (fun θ _ => Real.hasDerivAt_sin θ) (fun θ hθ => by
      rw [min_eq_left Real.pi_div_two_pos.le, max_eq_right Real.pi_div_two_pos.le] at hθ
      exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).le)
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr_Ioo_of_le Real.pi_div_two_pos.le fun θ hθ => ?_
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsq : 1 - (Real.sin θ : ℂ) ^ 2 = (Real.cos θ : ℂ) ^ 2 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq θ] :
      1 - Real.sin θ ^ 2 = Real.cos θ ^ 2)
  simp only [Function.comp_apply, real_smul]
  rw [hsq, DLMF.Hypergeometric.cpow_sq_neg_half hc]
  have : (Real.cos θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  field_simp

/-- DLMF 19.2.8_1: `K'(k) = ∫₀¹ dt/(√(1-t²) √(1-(1-k²)t²))` for `|ph k| < π/2`
(an improper integral at `t = 1`). -/
@[dlmf 19.2.E8_1]
theorem cCompEllIntKk_eq_integral {k : ℂ} (hk : 0 < k.re) :
    cCompEllIntKk k = ∫ t in (0 : ℝ)..1,
      (1 - (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) * (1 - (1 - k ^ 2) * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [(cCompEllIntKk_of_re_pos (Or.inl hk)).1, compEllIntKk_jacobiComodulusk, compEllIntKpk,
    p19lR1_integral_sin_subst (fun u => (1 - (1 - k ^ 2) * u) ^ (-(1 / 2 : ℂ)))]

/-- DLMF 19.2.8_2: `E'(k) = ∫₀¹ √(1-(1-k²)t²)/√(1-t²) dt` for `|ph k| < π/2`. -/
@[dlmf 19.2.E8_2]
theorem cCompEllIntEk_eq_integral {k : ℂ} (hk : 0 < k.re) :
    cCompEllIntEk k = ∫ t in (0 : ℝ)..1,
      (1 - (1 - k ^ 2) * (t : ℂ) ^ 2) ^ (1 / 2 : ℂ) * (1 - (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  have h : jacobiComodulusk k ^ 2 = 1 - k ^ 2 := by
    rw [jacobiComodulusk, one_div, Complex.cpow_ofNat_inv_pow]
  rw [(cCompEllIntKk_of_re_pos (Or.inl hk)).2, compEllIntEk_eq_integral, h,
    p19lR1_integral_sin_subst (fun u => (1 - (1 - k ^ 2) * u) ^ (1 / 2 : ℂ))]
  simp only [mul_comm]

/-- Real bridge for `K'`: for real `k > 0`, `K'(k) = Real.compEllIntKm (1 - k²)`. -/
theorem cCompEllIntKk_ofReal {k : ℝ} (hk : 0 < k) :
    cCompEllIntKk k = (DLMF.Elliptic.Real.compEllIntKm (1 - k ^ 2) : ℂ) := by
  have h : 0 < (k : ℂ).re ∨ ((k : ℂ).re = 0 ∧ 0 ≤ (k : ℂ).im) := Or.inl (by simpa using hk)
  simp only [cCompEllIntKk, h, ↓reduceIte]
  exact compEllIntKpk_ofReal (by positivity)

/-- Real bridge for `E'`: for real `k > 0`, `E'(k) = Real.compEllIntEm (1 - k²)`. -/
theorem cCompEllIntEk_ofReal {k : ℝ} (hk : 0 < k) :
    cCompEllIntEk k = (DLMF.Elliptic.Real.compEllIntEm (1 - k ^ 2) : ℂ) := by
  have h : 0 < (k : ℂ).re ∨ ((k : ℂ).re = 0 ∧ 0 ≤ (k : ℂ).im) := Or.inl (by simpa using hk)
  simp only [cCompEllIntEk, h, ↓reduceIte]
  refine compEllIntEk_eq_ofReal ?_ (by nlinarith [sq_nonneg k])
  rw [jacobiComodulusk, one_div, Complex.cpow_ofNat_inv_pow]; push_cast; ring

/-- DLMF §19.2(ii) (prose): for real `k²` with `0 < k² < 1` and real `α²`, the sign of
`α²(α² - k²)(α² - 1)` alternates on the four intervals separated by `0, k², 1`: negative
(circular case) on `(-∞, 0)` and `(k², 1)`, positive (hyperbolic case) on `(0, k²)` and
`(1, ∞)`. -/
@[dlmf 19.2.ii]
theorem circular_hyperbolic_alternate {k2 α2 : ℝ} (hk0 : 0 < k2) (hk1 : k2 < 1) :
    (α2 < 0 → α2 * (α2 - k2) * (α2 - 1) < 0) ∧
      (0 < α2 → α2 < k2 → 0 < α2 * (α2 - k2) * (α2 - 1)) ∧
      (k2 < α2 → α2 < 1 → α2 * (α2 - k2) * (α2 - 1) < 0) ∧
      (1 < α2 → 0 < α2 * (α2 - k2) * (α2 - 1)) := by
  refine ⟨fun h => ?_, fun h h' => ?_, fun h h' => ?_, fun h => ?_⟩
  · have : 0 < α2 * (α2 - k2) := mul_pos_of_neg_of_neg h (by linarith)
    nlinarith
  · have : α2 * (α2 - k2) < 0 := mul_neg_of_pos_of_neg h (by linarith)
    nlinarith
  · have : 0 < α2 * (α2 - k2) := mul_pos (by linarith) (by linarith)
    nlinarith
  · have : 0 < α2 * (α2 - k2) := mul_pos (by linarith) (by linarith)
    nlinarith

/-- A continuous, `π`-periodic, even function integrates over `[0, π]` to twice its integral
over `[0, π/2]`. -/
lemma ei19a_integral_zero_pi {g : ℝ → ℂ} (hc : Continuous g) (hp : Function.Periodic g π)
    (he : ∀ x, g (-x) = g x) :
    ∫ x in (0 : ℝ)..π, g x = 2 * ∫ x in (0 : ℝ)..(π / 2), g x := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_sub_left g (a := 0) (b := π / 2) π
  simp only [sub_zero, show π - π / 2 = π / 2 by ring] at h
  have h' : ∫ x in (0 : ℝ)..(π / 2), g (π - x) = ∫ x in (0 : ℝ)..(π / 2), g x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [sub_eq_neg_add, hp (-x), he]
  rw [← h, h']; ring

/-- For a continuous, `π`-periodic, even `g` and an integer `m`,
`∫₀^{mπ + φ} g = 2m ∫₀^{π/2} g + ∫₀^φ g`. -/
lemma ei19a_integral_add_int_mul_pi {g : ℝ → ℂ} (hc : Continuous g) (hp : Function.Periodic g π)
    (he : ∀ x, g (-x) = g x) (m : ℤ) (φ : ℝ) :
    ∫ x in (0 : ℝ)..(m * π + φ), g x =
      2 * m * (∫ x in (0 : ℝ)..(π / 2), g x) + ∫ x in (0 : ℝ)..φ, g x := by
  have hi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hc.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := m * π) (hi _ _) (hi _ _)]
  have h1 : ∫ x in (0 : ℝ)..(m * π), g x = m * ∫ x in (0 : ℝ)..π, g x := by
    have := hp.intervalIntegral_add_zsmul_eq m 0 hi
    simpa [zsmul_eq_mul] using this
  have h2 : ∫ x in (m * π : ℝ)..(m * π + φ), g x = ∫ x in (0 : ℝ)..φ, g x := by
    have := intervalIntegral.integral_comp_add_right g (a := 0) (b := φ) (m * π)
    rw [zero_add, add_comm φ] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun x _ => ?_
    exact (hp.int_mul m) x
  rw [h1, h2, ei19a_integral_zero_pi hc hp he]; ring

/-- For a continuous even `g`, `∫₀^{-φ} g = -∫₀^φ g`. -/
lemma ei19a_integral_neg {g : ℝ → ℂ} (he : ∀ x, g (-x) = g x) (φ : ℝ) :
    ∫ x in (0 : ℝ)..(-φ), g x = -∫ x in (0 : ℝ)..φ, g x := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := φ) g
  simp only [neg_zero, he] at h
  rw [h, intervalIntegral.integral_symm]

/-- The Legendre integrands `sin^{2j}θ (1 - k² sin²θ)^{p}` are continuous in real `θ` in the
principal domain, `π`-periodic and even. -/
lemma ei19a_legendre_integrand_props {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (j : ℕ) (p : ℂ) :
    let g : ℝ → ℂ := fun θ => (Real.sin θ : ℂ) ^ (2 * j) * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ p
    Continuous g ∧ Function.Periodic g π ∧ ∀ x, g (-x) = g x := by
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · refine (by fun_prop : Continuous fun θ : ℝ => (Real.sin θ : ℂ) ^ (2 * j)).mul
      (Continuous.cpow (by fun_prop) continuous_const fun θ => ?_)
    exact ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk θ
  · simp only [Real.sin_add_pi, ofReal_neg, pow_mul, neg_sq]
  · simp only [Real.sin_neg, ofReal_neg, pow_mul, neg_sq]

/-- DLMF 19.2.10 for real amplitude in the principal domain `1 - k² ∈ ℂ \ (-∞, 0]`:
`F(mπ ± φ, k) = 2mK(k) ± F(φ, k)`, `E(mπ ± φ, k) = 2mE(k) ± E(φ, k)`,
`D(mπ ± φ, k) = 2mD(k) ± D(φ, k)` for every integer `m`. -/
@[dlmf 19.2.E10]
theorem incEllInt_add_int_mul_pi {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (m : ℤ) (φ : ℝ) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    incEllIntFk (m * π + s * φ) k = 2 * m * compEllIntKk k + (s : ℂ) * incEllIntFk φ k ∧
      incEllIntEk (m * π + s * φ) k = 2 * m * compEllIntEk k + (s : ℂ) * incEllIntEk φ k ∧
      incEllIntDk (m * π + s * φ) k = 2 * m * compEllIntDk k + (s : ℂ) * incEllIntDk φ k := by
  have hcast : ((m : ℂ) * π + s * φ) = ((m * π + s * φ : ℝ) : ℂ) := by push_cast; ring
  have hpi : ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
  have key : ∀ (j : ℕ) (p : ℂ),
      ∫ x in (0 : ℝ)..(m * π + s * φ),
        (Real.sin x : ℂ) ^ (2 * j) * (1 - k ^ 2 * (Real.sin x : ℂ) ^ 2) ^ p =
      2 * m * (∫ x in (0 : ℝ)..(π / 2),
        (Real.sin x : ℂ) ^ (2 * j) * (1 - k ^ 2 * (Real.sin x : ℂ) ^ 2) ^ p) +
      (s : ℂ) * ∫ x in (0 : ℝ)..φ,
        (Real.sin x : ℂ) ^ (2 * j) * (1 - k ^ 2 * (Real.sin x : ℂ) ^ 2) ^ p := by
    intro j p
    obtain ⟨hc, hp, he⟩ := ei19a_legendre_integrand_props hk j p
    rw [ei19a_integral_add_int_mul_pi hc hp he]
    rcases hs with rfl | rfl
    · simp
    · rw [show (-1 : ℝ) * φ = -φ by ring, ei19a_integral_neg he]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hcast, incEllIntFk_ofReal_eq_integral, incEllIntFk_ofReal_eq_integral,
      compEllIntKk_eq_incEllIntFk, hpi, incEllIntFk_ofReal_eq_integral]
    simpa using key 0 (-(1 / 2 : ℂ))
  · rw [hcast, incEllIntEk_ofReal_eq_integral, incEllIntEk_ofReal_eq_integral,
      compEllIntEk_eq_integral]
    simpa using key 0 (1 / 2 : ℂ)
  · rw [hcast, incEllIntDk_ofReal_eq_integral, incEllIntDk_ofReal_eq_integral,
      compEllIntDk_eq_integral]
    simpa using key 1 (-(1 / 2 : ℂ))

/-! ### §19.2(iii) Bulirsch's integrals -/

/-- `cos²θ + (1 - k²) sin²θ = 1 - k² sin²θ`. -/
lemma ei19a_cos_sq_add_comod (k θ : ℂ) :
    Complex.cos θ ^ 2 + (1 - k ^ 2) * Complex.sin θ ^ 2 = 1 - k ^ 2 * Complex.sin θ ^ 2 := by
  linear_combination Complex.cos_sq_add_sin_sq θ

/-- `k'² = 1 - k²` for the principal `k' = √(1 - k²)`. -/
theorem ei19a_jacobiComodulusk_sq (k : ℂ) : jacobiComodulusk k ^ 2 = 1 - k ^ 2 := by
  rw [jacobiComodulusk, one_div, Complex.cpow_ofNat_inv_pow]

/-- With `p = 1` Bulirsch's `cel` needs no principal value. -/
lemma ei19a_bulirschCel_one (kc : ℂ) (a b : ℝ) :
    bulirschCel kc 1 a b = ei19a_segmentIntegral (fun θ => (a * Complex.cos θ ^ 2 +
      b * Complex.sin θ ^ 2) * (Complex.cos θ ^ 2 + kc ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ)))
        (π / 2) := by
  rw [bulirschCel, ei19a_pvSegmentIntegral_eq (δ := 1) one_pos]
  · congr 1; funext θ; simp [Complex.cos_sq_add_sin_sq]
  · intro t _; simp [Complex.cos_sq_add_sin_sq]

/-- DLMF 19.2.13–19.2.14: with `k_c = k'`, `K(k) = cel(k_c, 1, 1, 1)` and `D(k) = cel(k_c, 1, 0, 1)`
for every complex `k`, and `Π(α², k) = cel(k_c, 1 - α², 1, 1)` for real `α²` (`p = 1 - α²`, a
principal value on both sides when `α² > 1`). -/
@[dlmf 19.2.E14, dlmf 19.2.E13]
theorem compEllInt_eq_bulirschCel (k : ℂ) (α2 : ℝ) :
    compEllIntKk k = bulirschCel (jacobiComodulusk k) 1 1 1 ∧
      compEllIntDk k = bulirschCel (jacobiComodulusk k) 1 0 1 ∧
      compEllIntPik α2 k = bulirschCel (jacobiComodulusk k) (1 - α2) 1 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ei19a_bulirschCel_one, compEllIntKk_eq_incEllIntFk, incEllIntFk]
    congr 1; funext θ
    rw [ei19a_jacobiComodulusk_sq, ei19a_cos_sq_add_comod]; push_cast
    rw [one_mul, one_mul, Complex.cos_sq_add_sin_sq, one_mul]
  · rw [ei19a_bulirschCel_one, compEllIntDk, incEllIntDk]
    congr 1; funext θ
    rw [ei19a_jacobiComodulusk_sq, ei19a_cos_sq_add_comod]; push_cast; ring
  · rw [compEllIntPik, incEllIntPik, bulirschCel]
    have hg : ∀ θ : ℂ, Complex.cos θ ^ 2 + ((1 - α2 : ℝ) : ℂ) * Complex.sin θ ^ 2 =
        1 - α2 * Complex.sin θ ^ 2 := fun θ => by
      push_cast; linear_combination Complex.cos_sq_add_sin_sq θ
    simp only [hg, ei19a_jacobiComodulusk_sq, ei19a_cos_sq_add_comod, ofReal_one, one_mul,
      Complex.cos_sq_add_sin_sq, div_eq_inv_mul, mul_one]

/-- DLMF 19.2.14: `E(k) = cel(k_c, 1, 1, k_c²)` for every real `k` (`k_c² = 1 - k²` is real, as
`cel` requires). -/
@[dlmf 19.2.E14]
theorem compEllIntEk_eq_bulirschCel (k : ℝ) :
    compEllIntEk k = bulirschCel (jacobiComodulusk k) 1 1 (1 - k ^ 2) := by
  rw [ei19a_bulirschCel_one, compEllIntEk, incEllIntEk]
  congr 1; funext θ
  rw [ei19a_jacobiComodulusk_sq]
  push_cast
  rw [ei19a_cos_sq_add_comod, show (1 : ℂ) * Complex.cos θ ^ 2 + (1 - (k : ℂ) ^ 2) *
    Complex.sin θ ^ 2 = 1 - (k : ℂ) ^ 2 * Complex.sin θ ^ 2 from by
      rw [one_mul, ei19a_cos_sq_add_comod], ei19a_cpow_half_eq]

/-- DLMF 19.2.14: `(E(k) - k'² K(k))/k² = cel(k_c, 1, 1, 0)` in the principal domain
`1 - k² ∈ ℂ \ (-∞, 0]`, `k ≠ 0`. -/
@[dlmf 19.2.E14]
theorem compEllIntEk_sub_eq_bulirschCel {k : ℂ} (hk : k ≠ 0) (hk1 : 1 - k ^ 2 ∈ slitPlane) :
    (compEllIntEk k - jacobiComodulusk k ^ 2 * compEllIntKk k) / k ^ 2 =
      bulirschCel (jacobiComodulusk k) 1 1 0 := by
  have hc : Continuous fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) :=
    Continuous.cpow (by fun_prop) continuous_const fun θ =>
      ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk1 θ
  have hpi : ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
  have hE : Continuous fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) :=
    Continuous.cpow (by fun_prop) continuous_const fun θ =>
      ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk1 θ
  rw [div_eq_iff (pow_ne_zero 2 hk), ei19a_bulirschCel_one, hpi, ei19a_segmentIntegral_ofReal,
    compEllIntEk_eq_integral, compEllIntKk, ei19a_jacobiComodulusk_sq,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hE.intervalIntegrable _ _) ((hc.intervalIntegrable _ _).const_mul (1 - k ^ 2)),
    ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Complex.ofReal_sin, Complex.ofReal_one, Complex.ofReal_zero]
  rw [ei19a_cos_sq_add_comod, ei19a_cpow_half_eq]
  linear_combination (-(k ^ 2) * (1 - k ^ 2 * Complex.sin (θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) *
    Complex.cos_sq_add_sin_sq (θ : ℂ)

/-- DLMF 19.2.15: `F(φ, k) = el1(x, k_c)` with `x = tan φ`, `k_c = k'`, for real `|φ| < π/2` and
every complex `k`. -/
@[dlmf 19.2.E15, dlmf 19.2.E13]
theorem incEllIntFk_eq_bulirschEl1 (k : ℂ) {φ : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) :
    incEllIntFk φ k = bulirschEl1 (Real.tan φ) (jacobiComodulusk k) := by
  rw [bulirschEl1, ← Complex.ofReal_arctan, Real.arctan_tan h0 h1, incEllIntFk]
  congr 1; funext θ
  rw [ei19a_jacobiComodulusk_sq, ei19a_cos_sq_add_comod]

/-- **Admitted.** DLMF 19.2.15: `F(φ, k) = el2(x, k_c, 1, 1)`, `E(φ, k) = el2(x, k_c, 1, k_c²)`,
`D(φ, k) = el2(x, k_c, 0, 1)` with `x = tan φ`, `k_c = k'`, for real `k` with `k² < 1` and real
`|φ| < π/2`. -/
@[dlmf 19.2.E15]
theorem incEllInt_eq_bulirschEl2 {k φ : ℝ} (hk : k ^ 2 < 1) (h0 : -(π / 2) < φ)
    (h1 : φ < π / 2) :
    incEllIntFk φ k = bulirschEl2 (Real.tan φ) (jacobiComodulusk k) 1 1 ∧
      incEllIntEk φ k = bulirschEl2 (Real.tan φ) (jacobiComodulusk k) 1 (1 - k ^ 2) ∧
      incEllIntDk φ k = bulirschEl2 (Real.tan φ) (jacobiComodulusk k) 0 1 := by
  sorry

/-- DLMF 19.2.16: `el3(x, k_c, p) = Π(arctan x, 1 - p, k)` with `k_c = k'`, for every complex `x`
and `k` and real `p` (both sides are principal values at an interior singularity). -/
@[dlmf 19.2.E16]
theorem bulirschEl3_eq_incEllIntPik (x k : ℂ) (p : ℝ) :
    bulirschEl3 x (jacobiComodulusk k) p = incEllIntPik (Complex.arctan x) (1 - p) k := by
  rw [bulirschEl3, incEllIntPik]
  have hg : ∀ θ : ℂ, Complex.cos θ ^ 2 + (p : ℂ) * Complex.sin θ ^ 2 =
      1 - (1 - (p : ℂ)) * Complex.sin θ ^ 2 := fun θ => by
    linear_combination Complex.cos_sq_add_sin_sq θ
  simp only [hg, ei19a_jacobiComodulusk_sq, ei19a_cos_sq_add_comod]

/-- **Admitted.** DLMF §19.2(iii): the integrals are complete if `x = ∞`: as real `x → +∞`,
`el1(x, k_c) → cel(k_c, 1, 1, 1)`, `el2(x, k_c, a, b) → cel(k_c, 1, a, b)` and, for `p > 0`,
`el3(x, k_c, p) → cel(k_c, p, 1, 1)`, when `k_c² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.2.iii]
theorem tendsto_bulirsch_atTop {kc : ℂ} (hkc : kc ^ 2 ∈ slitPlane) (a b : ℝ) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun x : ℝ => bulirschEl1 x kc) atTop (𝓝 (bulirschCel kc 1 1 1)) ∧
      Tendsto (fun x : ℝ => bulirschEl2 x kc a b) atTop (𝓝 (bulirschCel kc 1 a b)) ∧
      Tendsto (fun x : ℝ => bulirschEl3 x kc p) atTop (𝓝 (bulirschCel kc p 1 1)) := by
  sorry

/-! ### §19.2(iv) The function `R_C(x, y)` -/

/-- DLMF 19.2.17: for `y` not a negative real number, `R_C(x, y) = ½ ∫₀^∞ dt/(√(t+x)(t+y))`
(ACQ19C's `symEllIntRC`; a Cauchy principal value when `y < 0`). -/
@[dlmf 19.2.E17]
theorem symEllIntRC_eq_integral {x y : ℂ} (hy : ¬IsNegReal y) :
    symEllIntRC x y =
      (1 / 2) * ∫ t in Ioi (0 : ℝ), (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹ := by
  simp [symEllIntRC, hy]

/-- DLMF 19.2.17 (principal-value case): for `y < 0`, `R_C(x, y)` is one half of the Cauchy
principal value of `∫₀^∞ dt/(√(t+x)(t+y))` at `t = -y`. -/
@[dlmf 19.2.E17]
theorem symEllIntRC_eq_cauchyPV {x y : ℂ} (hy : IsNegReal y) :
    symEllIntRC x y =
      (1 / 2) * cauchyPVIoi (fun t => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹) (-y.re) := by
  simp [symEllIntRC, hy]

/-- `R_C(0, y) = (π/2) y^{-1/2}` for `y ∈ ℂ \ (-∞, 0]` (via `R_F(0, y, y)`, DLMF 19.16.20). -/
lemma p19lR1_symEllIntRC_zero_left {y : ℂ} (hy : y ∈ slitPlane) :
    symEllIntRC 0 y = π / 2 * y ^ (-(1 / 2 : ℂ)) := by
  rw [symEllIntRC_eq_symEllIntRF 0 (ei19c_not_isNegReal_of_mem_slitPlane hy),
    symEllIntRF_zero_left hy hy]
  have : (![y, y] : Fin 2 → ℂ) = fun _ => y := by funext i; fin_cases i <;> rfl
  rw [this, symEllIntR_const _ _ hy (by norm_num)]

/-- `R_C(x, x) = x^{-1/2}` for `x ∈ ℂ \ (-∞, 0]` (DLMF 19.16.11 with `R_C = R_{-1/2}(1/2, 1)`). -/
lemma p19lR1_symEllIntRC_self {x : ℂ} (hx : x ∈ slitPlane) :
    symEllIntRC x x = x ^ (-(1 / 2 : ℂ)) := by
  rw [symEllIntRC_eq_symEllIntR hx hx]
  have : (![x, x] : Fin 2 → ℂ) = fun _ => x := by funext i; fin_cases i <;> rfl
  rw [this, symEllIntR_const _ _ hx]
  norm_num
  rw [show (3/2 : ℂ) = 1/2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]
  exact mul_ne_zero (by norm_num) ei19c_Gamma_half_ne

/-- `R_C(0, y) = (π/2)/√y` for real `y > 0`. -/
lemma p19lR1_symEllIntRC_zero_left_real {y : ℝ} (hy : 0 < y) :
    symEllIntRC 0 y = ((π / 2 / Real.sqrt y : ℝ) : ℂ) := by
  rw [p19lR1_symEllIntRC_zero_left (by simpa using hy),
    show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow hy.le, Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow]
  push_cast; ring

/-- For `0 < y < x`, `artanh √((x-y)/x) = ln((√x + √(x-y))/√y)`. -/
lemma p19lR1_artanh_eq_log {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
    Real.artanh (Real.sqrt ((x - y) / x)) =
      Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt y) := by
  have hx : 0 < x := hy.trans hxy
  have ha : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hb : 0 < Real.sqrt (x - y) := Real.sqrt_pos.2 (by linarith)
  have hc : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hbx : Real.sqrt (x - y) < Real.sqrt x := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hs : Real.sqrt ((x - y) / x) = Real.sqrt (x - y) / Real.sqrt x := Real.sqrt_div' _ hx.le
  have hs1 : Real.sqrt (x - y) / Real.sqrt x < 1 := (div_lt_one ha).2 hbx
  rw [hs, Real.artanh_eq_half_log ⟨by linarith [div_pos hb ha], hs1.le⟩]
  have hsq : (1 + Real.sqrt (x - y) / Real.sqrt x) / (1 - Real.sqrt (x - y) / Real.sqrt x) =
      ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt y) ^ 2 := by
    have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
    have h2 : Real.sqrt (x - y) ^ 2 = x - y := Real.sq_sqrt (by linarith)
    have h3 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    have hne : Real.sqrt x - Real.sqrt (x - y) ≠ 0 := by linarith
    field_simp
    rw [h3]; nlinarith [h1, h2]
  rw [hsq, Real.log_pow]; push_cast; ring

/-- DLMF 19.2.18: for `0 ≤ x < y`,
`R_C(x, y) = (y-x)^{-1/2} arctan √((y-x)/x) = (y-x)^{-1/2} arccos √(x/y)` (the arctan form for
`x > 0`). -/
@[dlmf 19.2.E18]
theorem symEllIntRC_of_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    symEllIntRC x y = ((Real.arccos (Real.sqrt (x / y)) / Real.sqrt (y - x) : ℝ) : ℂ) ∧
      (0 < x → symEllIntRC x y =
        ((Real.arctan (Real.sqrt ((y - x) / x)) / Real.sqrt (y - x) : ℝ) : ℂ)) := by
  have hy : 0 < y := hx.trans_lt hxy
  rcases hx.lt_or_eq with hx | rfl
  · have h : symEllIntRC x y =
        ((Real.arccos (Real.sqrt (x / y)) / Real.sqrt (y - x) : ℝ) : ℂ) := by
      rw [symEllIntRC_eq_carlsonRC (by simpa using hx) (by simpa using hy),
        Carlson.TwoVariable.carlsonRC_of_lt hx hxy]
    refine ⟨h, fun _ => ?_⟩
    rw [h]
    congr 3
    have hz : 0 < Real.sqrt (x / y) := Real.sqrt_pos.mpr (div_pos hx hy)
    rw [Real.arccos_eq_arctan hz]
    congr 1
    have h1 : 1 - Real.sqrt (x / y) ^ 2 = (y - x) / y := by
      rw [Real.sq_sqrt (div_pos hx hy).le]; field_simp
    rw [h1, Real.sqrt_div' _ hy.le, Real.sqrt_div' _ hy.le, Real.sqrt_div' _ hx.le]
    have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    field_simp
  · refine ⟨?_, fun h => absurd h (lt_irrefl _)⟩
    rw [show ((0 : ℝ) : ℂ) = 0 by simp, p19lR1_symEllIntRC_zero_left_real hy]
    simp

/-- DLMF 19.2.19: for `0 < y < x`,
`R_C(x, y) = (x-y)^{-1/2} artanh √((x-y)/x) = (x-y)^{-1/2} ln((√x + √(x-y))/√y)`. -/
@[dlmf 19.2.E19]
theorem symEllIntRC_of_gt {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
    symEllIntRC x y =
        ((Real.artanh (Real.sqrt ((x - y) / x)) / Real.sqrt (x - y) : ℝ) : ℂ) ∧
      symEllIntRC x y =
        ((Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt y) / Real.sqrt (x - y) : ℝ) :
          ℂ) := by
  have hx : 0 < x := hy.trans hxy
  have h : symEllIntRC x y = ((Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt y) /
      Real.sqrt (x - y) : ℝ) : ℂ) := by
    rw [symEllIntRC_eq_carlsonRC (by simpa using hx) (by simpa using hy),
      Carlson.TwoVariable.carlsonRC_of_gt hy hxy]
  exact ⟨by rw [h, p19lR1_artanh_eq_log hy hxy], h⟩

/-- The logarithmic primitive of the real RC kernel away from its pole. -/
private lemma hasDerivAt_rcNeg_primitive {x y t : ℝ} (hx : 0 ≤ x) (hy : y < 0) (ht : 0 < t) (h : t + y ≠ 0) :
    HasDerivAt (fun u : ℝ => (Real.log (u + y) -
      2 * Real.log (Real.sqrt (u + x) + Real.sqrt (x - y))) / Real.sqrt (x - y))
      (Real.sqrt (t + x) * (t + y))⁻¹ t := by
  have hs : 0 < Real.sqrt (t + x) := Real.sqrt_pos.mpr (by linarith)
  have ha : 0 < Real.sqrt (x - y) := Real.sqrt_pos.mpr (by linarith)
  have hsq := Real.sq_sqrt (show 0 ≤ t + x by linarith)
  have haq := Real.sq_sqrt (show 0 ≤ x - y by linarith)
  have hd := (((hasDerivAt_id t).add_const y).log h).sub
    (((((hasDerivAt_id t).add_const x).sqrt (by dsimp; linarith)).add_const (Real.sqrt (x - y))).log
      (show Real.sqrt (t + x) + Real.sqrt (x - y) ≠ 0 by positivity) |>.const_mul 2)
  simp only [id_eq] at hd
  convert hd.div_const (Real.sqrt (x - y)) using 1
  field_simp [h, hs.ne', ha.ne', show Real.sqrt (t + x) + Real.sqrt (x - y) ≠ 0 by positivity]
  nlinarith
/-- The logarithmic RC primitive vanishes at infinity. -/
private lemma tendsto_rcNeg_primitive_atTop {x y : ℝ} (hx : 0 ≤ x) (hy : y < 0) :
    Tendsto (fun t : ℝ => (Real.log (t + y) -
      2 * Real.log (Real.sqrt (t + x) + Real.sqrt (x - y))) / Real.sqrt (x - y))
      atTop (𝓝 0) := by
  let a := Real.sqrt (x - y)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ht : Tendsto (fun t : ℝ => Real.sqrt (t + x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ x tendsto_id)
  have hi : Tendsto (fun t : ℝ => a / Real.sqrt (t + x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  have hr : Tendsto (fun t : ℝ =>
      (1 - a / Real.sqrt (t + x)) / (1 + a / Real.sqrt (t + x))) atTop (𝓝 1) := by
    convert ((tendsto_const_nhds.sub hi).div (tendsto_const_nhds.add hi) (by norm_num : (1 : ℝ) + 0 ≠ 0)) using 1; norm_num
  have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  have hld := hl.div_const a
  simp only [Real.log_one, zero_div] at hld
  apply hld.congr'
  filter_upwards [eventually_gt_atTop (max 0 (-y))] with t ht'
  have ht0 : 0 < t := lt_of_le_of_lt (le_max_left _ _) ht'
  have hty : 0 < t + y := by have := lt_of_le_of_lt (le_max_right 0 (-y)) ht'; linarith
  have hs : 0 < Real.sqrt (t + x) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : 0 < Real.sqrt (t + x) - a := by
    have hsq := Real.sq_sqrt (show 0 ≤ t + x by linarith)
    have haq := Real.sq_sqrt (show 0 ≤ x - y by linarith)
    change 0 < Real.sqrt (t + x) - Real.sqrt (x - y)
    exact sub_pos.mpr (Real.sqrt_lt_sqrt (by linarith) (by linarith))
  have he : t + y = (Real.sqrt (t + x) - a) * (Real.sqrt (t + x) + a) := by
    have hsq := Real.sq_sqrt (show 0 ≤ t + x by linarith)
    have haq := Real.sq_sqrt (show 0 ≤ x - y by linarith)
    dsimp [a]
    nlinarith
  have hrat : (1 - a / Real.sqrt (t + x)) / (1 + a / Real.sqrt (t + x)) =
      (Real.sqrt (t + x) - a) / (Real.sqrt (t + x) + a) := by field_simp
  dsimp only [Function.comp_def]
  rw [hrat, Real.log_div hs1.ne' (by positivity), he, Real.log_mul hs1.ne' (by positivity)]
  dsimp [a]
  ring
/-- The RC primitive is continuous away from its logarithmic pole, including at zero. -/
private lemma continuousAt_rcNeg_primitive {x y t : ℝ} (hx : 0 ≤ x) (hy : y < 0) (ht : t + y ≠ 0) :
    ContinuousAt (fun u : ℝ => (Real.log (u + y) -
      2 * Real.log (Real.sqrt (u + x) + Real.sqrt (x - y))) / Real.sqrt (x - y)) t := by
  have ha : 0 < Real.sqrt (x - y) := Real.sqrt_pos.mpr (by linarith)
  apply ContinuousAt.div_const
  apply ContinuousAt.sub
  · exact (continuousAt_id.add_const y).log ht
  · apply ContinuousAt.const_mul
    apply ContinuousAt.log
    · fun_prop
    · positivity
/-- The real RC integral with a symmetric interval removed is the sum of its two primitive differences. -/
private lemma integral_rcNeg_kernel_truncated {x y ε : ℝ} (hx : 0 ≤ x) (hy : y < 0) (he : 0 < ε) (hec : ε < -y) :
    let F := fun u : ℝ => (Real.log (u + y) -
      2 * Real.log (Real.sqrt (u + x) + Real.sqrt (x - y))) / Real.sqrt (x - y)
    (∫ t in Ioi (0 : ℝ) \ Icc (-y - ε) (-y + ε), (Real.sqrt (t + x) * (t + y))⁻¹) =
      F (-y - ε) - F 0 - F (-y + ε) := by
  let F := fun u : ℝ => (Real.log (u + y) -
    2 * Real.log (Real.sqrt (u + x) + Real.sqrt (x - y))) / Real.sqrt (x - y)
  let f := fun t : ℝ => (Real.sqrt (t + x) * (t + y))⁻¹
  have hF (t : ℝ) (ht : t + y ≠ 0) : ContinuousAt F t := continuousAt_rcNeg_primitive hx hy ht
  have hD (t : ℝ) (ht : 0 < t) (hty : t + y ≠ 0) : HasDerivAt F (f t) t :=
    hasDerivAt_rcNeg_primitive hx hy ht hty
  have hleftcont : ContinuousOn F (Icc 0 (-y - ε)) := by
    intro t ht
    exact (hF t (by linarith [ht.2])).continuousWithinAt
  have hleft : IntegrableOn f (Ioo 0 (-y - ε)) := by
    have hi := intervalIntegral.integrableOn_deriv_of_nonneg hleftcont.neg
      (fun t ht => (hD t ht.1 (by linarith [ht.2])).neg) (fun t ht => ?_)
    · rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      simpa using hi.neg
    · dsimp [f]
      have : t + y < 0 := by linarith [ht.2]
      exact neg_nonneg.mpr (inv_nonpos.mpr (by nlinarith [Real.sqrt_nonneg (t + x)]))
  have hleftval : (∫ t in Ioo 0 (-y - ε), f t) = F (-y - ε) - F 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith : 0 ≤ -y - ε)]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hleftcont
      (fun t ht => hD t ht.1 (by linarith [ht.2]))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    rwa [integrableOn_Ioc_iff_integrableOn_Ioo]
  have hrightD : ∀ t ∈ Ioi (-y + ε), HasDerivAt F (f t) t := by
    intro t ht
    change -y + ε < t at ht
    exact hD t (by linarith [ht]) (by linarith [ht])
  have hrightpos : ∀ t ∈ Ioi (-y + ε), 0 ≤ f t := by
    intro t ht
    change -y + ε < t at ht
    dsimp [f]
    have : 0 < t + y := by linarith [ht]
    positivity
  have hright := integrableOn_Ioi_deriv_of_nonneg
    (hF (-y + ε) (by linarith)).continuousWithinAt hrightD hrightpos (tendsto_rcNeg_primitive_atTop hx hy)
  have hrightval := integral_Ioi_of_hasDerivAt_of_nonneg
    (hF (-y + ε) (by linarith)).continuousWithinAt hrightD hrightpos (tendsto_rcNeg_primitive_atTop hx hy)
  have hset : Ioi (0 : ℝ) \ Icc (-y - ε) (-y + ε) = Ioo 0 (-y - ε) ∪ Ioi (-y + ε) := by
    ext t
    simp only [Set.mem_sdiff, mem_Ioi, mem_Icc, mem_union, mem_Ioo]
    constructor
    · rintro ⟨ht, h⟩
      by_cases h1 : t < -y - ε
      · exact Or.inl ⟨ht, h1⟩
      · exact Or.inr (lt_of_not_ge fun h2 => h ⟨by linarith, h2⟩)
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨h1, by rintro ⟨h3, h4⟩; linarith⟩
      · exact ⟨show 0 < t by linarith, by rintro ⟨h3, h4⟩; linarith⟩
  change (∫ t in Ioi (0 : ℝ) \ Icc (-y - ε) (-y + ε), f t) = _
  rw [hset, setIntegral_union (by
    apply disjoint_left.mpr
    intro t ht1 ht2
    have h1 := ht1.2
    have h2 : -y + ε < t := ht2
    linarith) measurableSet_Ioi hleft hright, hleftval, hrightval]
  ring
/-- The logarithms at the two sides of the RC pole cancel in the symmetric truncation limit. -/
private lemma tendsto_integral_rcNeg_kernel_truncated {x y : ℝ} (hx : 0 ≤ x) (hy : y < 0) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ) \ Icc (-y - ε) (-y + ε),
      (Real.sqrt (t + x) * (t + y))⁻¹) (𝓝[>] 0)
      (𝓝 (-(Real.log y - 2 * Real.log (Real.sqrt x + Real.sqrt (x - y))) / Real.sqrt (x - y))) := by
  let a := Real.sqrt (x - y)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hc : Continuous (fun ε : ℝ =>
      (2 * Real.log (Real.sqrt (-y + ε + x) + a) - 2 * Real.log (Real.sqrt (-y - ε + x) + a)) / a -
      (Real.log y - 2 * Real.log (Real.sqrt x + a)) / a) := by
    have hp (s : ℝ → ℝ) (hs : Continuous s) :
        Continuous (fun ε => Real.log (Real.sqrt (s ε) + a)) :=
      ((Real.continuous_sqrt.comp hs).add_const a).log
        (fun ε => (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) ha).ne')
    exact (((hp _ (by fun_prop)).const_mul 2).sub
      ((hp _ (by fun_prop)).const_mul 2) |>.div_const a).sub continuous_const
  have hl := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [add_zero, sub_zero, sub_self, zero_div, zero_sub] at hl
  have hl' : Tendsto (fun ε : ℝ =>
      (2 * Real.log (Real.sqrt (-y + ε + x) + a) - 2 * Real.log (Real.sqrt (-y - ε + x) + a)) / a -
      (Real.log y - 2 * Real.log (Real.sqrt x + a)) / a) (𝓝[>] 0)
      (𝓝 (-(Real.log y - 2 * Real.log (Real.sqrt x + Real.sqrt (x - y))) / Real.sqrt (x - y))) := by
    simpa only [a, neg_div] using hl
  apply hl'.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < -y by linarith)).filter_mono nhdsWithin_le_nhds]
    with ε he hec
  rw [integral_rcNeg_kernel_truncated hx hy he hec]
  dsimp [a]
  rw [show -y - ε + y = -ε by ring, show -y + ε + y = ε by ring, Real.log_neg_eq_log]
  ring_nf
/-- The negative-real RC principal value equals its real logarithmic expression. -/
private lemma symEllIntRC_of_neg_log {x y : ℝ} (hx : 0 ≤ x) (hy : y < 0) :
    symEllIntRC x y = ((Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt (-y)) /
      Real.sqrt (x - y) : ℝ) : ℂ) := by
  have ha : 0 < Real.sqrt (x - y) := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < Real.sqrt (-y) := Real.sqrt_pos.mpr (by linarith)
  have hcast (ε : ℝ) :
      (∫ t in Ioi (0 : ℝ) \ Icc (-y - ε) (-y + ε),
        (((t : ℂ) + (x : ℂ)) ^ (1 / 2 : ℂ) * ((t : ℂ) + (y : ℂ)))⁻¹) =
        ((∫ t in Ioi (0 : ℝ) \ Icc (-y - ε) (-y + ε),
          (Real.sqrt (t + x) * (t + y))⁻¹ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun (measurableSet_Ioi.diff measurableSet_Icc)
    intro t ht
    have ht0 : 0 < t := ht.1
    have hpow : ((t : ℂ) + (x : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt (t + x) : ℂ) := by
      rw [← ofReal_add, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow (by linarith : 0 ≤ t + x), ← Real.sqrt_eq_rpow]
    dsimp only
    rw [hpow]
    push_cast
    rfl
  have hl := Complex.continuous_ofReal.tendsto _ |>.comp (tendsto_integral_rcNeg_kernel_truncated hx hy)
  have hl' : Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ) \ Icc (-y - ε) (-y + ε),
      (((t : ℂ) + (x : ℂ)) ^ (1 / 2 : ℂ) * ((t : ℂ) + (y : ℂ)))⁻¹) (𝓝[>] 0)
      (𝓝 ((-(Real.log y - 2 * Real.log (Real.sqrt x + Real.sqrt (x - y))) / Real.sqrt (x - y) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, hcast] using hl
  rw [symEllIntRC_eq_cauchyPV (show IsNegReal (y : ℂ) by exact ⟨by simp, by simpa using hy⟩),
    cauchyPVIoi, ofReal_re, hl'.limUnder_eq]
  rw [Real.log_div (by positivity) hb.ne', Real.log_sqrt (by linarith : 0 ≤ -y),
    ← Real.log_neg_eq_log y]
  push_cast
  ring

/-- DLMF 19.2.20: for `y < 0 ≤ x` the Cauchy principal value is hyperbolic:
`R_C(x, y) = √(x/(x-y)) R_C(x-y, -y) = (x-y)^{-1/2} artanh √(x/(x-y))
= (x-y)^{-1/2} ln((√x + √(x-y))/√(-y))`. -/
@[dlmf 19.2.E20]
theorem symEllIntRC_of_neg {x y : ℝ} (hy : y < 0) (hx : 0 ≤ x) :
    symEllIntRC x y = (Real.sqrt (x / (x - y)) : ℂ) * symEllIntRC (x - y) (-y) ∧
      symEllIntRC x y =
        ((Real.artanh (Real.sqrt (x / (x - y))) / Real.sqrt (x - y) : ℝ) : ℂ) ∧
      symEllIntRC x y =
        ((Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt (-y)) / Real.sqrt (x - y) : ℝ) :
          ℂ) := by
  have hlog := symEllIntRC_of_neg_log hx hy
  have hxy : 0 < x - y := by linarith
  have hy' : 0 < -y := by linarith
  rcases hx.eq_or_lt with hx0 | hx
  · subst x
    have hs : Real.sqrt (-y) ≠ 0 := (Real.sqrt_pos.mpr hy').ne'
    simp only [Real.sqrt_zero, zero_add, zero_sub, div_self hs, Real.log_one,
      zero_div, ofReal_zero] at hlog
    simp only [ofReal_zero]
    rw [hlog]
    simp [hs]
  · have ha : 0 < Real.sqrt (x - y) := Real.sqrt_pos.mpr hxy
    have hb : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have hc := symEllIntRC_of_gt hy' (by linarith : -y < x - y)
    have hat := p19lR1_artanh_eq_log hy' (by linarith : -y < x - y)
    rw [show x - y- -y = x by ring, add_comm (Real.sqrt (x - y))] at hc hat
    have he : Real.sqrt (x / (x - y)) = Real.sqrt x / Real.sqrt (x - y) := Real.sqrt_div' _ hxy.le
    refine ⟨?_, ?_, hlog⟩
    · rw [hlog, ← ofReal_sub, ← ofReal_neg, hc.2, he]
      push_cast
      field_simp [ofReal_ne_zero.mpr hb.ne', ofReal_ne_zero.mpr ha.ne']
    · rw [hlog, hat]

/-- **Admitted.** DLMF 19.2.21: if the segment with endpoints `x` and `y` lies in
`ℂ \ (-∞, 0]`, `R_C(x, y) = ∫₀¹ (v²x + (1-v²)y)^{-1/2} dv`. -/
@[dlmf 19.2.E21]
theorem symEllIntRC_eq_integral_segment {x y : ℂ} (h : segment ℝ x y ⊆ slitPlane) :
    symEllIntRC x y =
      ∫ v in (0 : ℝ)..1, ((v : ℂ) ^ 2 * x + (1 - (v : ℂ) ^ 2) * y) ^ (-(1 / 2 : ℂ)) := by
  sorry

/-- **Admitted.** DLMF 19.2.22: if the segment with endpoints `x` and `y` lies in
`ℂ \ (-∞, 0]`, `R_C(x, y) = (2/π) ∫₀^{π/2} R_C(y, x cos²θ + y sin²θ) dθ`. -/
@[dlmf 19.2.E22]
theorem symEllIntRC_eq_integral_RC {x y : ℂ} (h : segment ℝ x y ⊆ slitPlane) :
    symEllIntRC x y = 2 / π * ∫ θ in (0 : ℝ)..(π / 2),
      symEllIntRC y (x * (Real.cos θ : ℂ) ^ 2 + y * (Real.sin θ : ℂ) ^ 2) := by
  sorry

end DLMF.EllipticIntegrals
