/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.EllipticIntegrals.SymmetricIntegrals
public import Carlson.R.IntegralEvaluation
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Legendre's integrals: the statements of DLMF §19.2

The definitions of DLMF §19.2 are in `DLMF.EllipticIntegrals.Legendre`; this file states the
remaining content of §19.2: the reduction of a general elliptic integrand (§19.2(i)), the
relations, symmetries and quasi-periodicity of Legendre's integrals (§19.2(ii)), Bulirsch's
integrals as Legendre integrals (§19.2(iii)), and the function `R_C = symmetricEllipticRC`
(§19.2(iv)).

## Main results

* `ellipticIntegrand_eq`, `ellipticIntegrand_elliptic_part`: the reduction of a rational
  integrand `r(s, t)` to `ρ/s + σ`, as a field identity (DLMF 19.2.1–19.2.3).
* `incompleteEllipticD_eq`, `incompleteEllipticD_eq_of_real`, `completeEllipticD_eq`:
  `D = (F - E)/k²` (DLMF 19.2.6, 19.2.8).
* `completeEllipticK_neg`, `completeEllipticE_neg`,
  `differentiableOn_completeEllipticK_completeEllipticE`,
  `differentiableOn_complementaryEllipticK_complementaryEllipticE`: parity and holomorphy of the
  principal `K`, `E`, `K'`, `E'` (DLMF §19.2(ii)).
* `complementaryEllipticK_eq_integral`, `complementaryEllipticE_eq_integral`: the integral forms of
  `K'`, `E'` (DLMF 19.2.8_1, 19.2.8_2).
* `circular_hyperbolic_alternate`: the circular/hyperbolic alternation (DLMF §19.2(ii), prose).
* `incEllInt_add_int_mul_pi`: the quasi-periodicity in `φ` (DLMF 19.2.10).
* `compEllInt_eq_bulirschCel`, `completeEllipticE_eq_bulirschCel`,
  `incompleteEllipticF_eq_bulirschEl1`, `incEllInt_eq_bulirschEl2`,
  `bulirschEl3_eq_incompleteEllipticPi`: Bulirsch's integrals (DLMF 19.2.13–19.2.16).
* `tendsto_bulirsch_atTop`: the incomplete Bulirsch integrals become complete as `x → ∞`
  (DLMF §19.2(iii)).
* `symmetricEllipticRC_eq_integral`, `symmetricEllipticRC_eq_cauchyPV`: the integral of `R_C` (DLMF
  19.2.17).
* `symmetricEllipticRC_of_lt`, `symmetricEllipticRC_of_gt`, `symmetricEllipticRC_of_neg`: `R_C` in
  elementary functions (DLMF 19.2.18–19.2.20).
* `symmetricEllipticRC_eq_integral_segment`, `symmetricEllipticRC_eq_integral_RC`: DLMF 19.2.21,
  19.2.22.

## Implementation notes

Real amplitudes `φ` are used where DLMF's identities are path statements; the principal domain
`1 - k² ∈ ℂ \ (-∞, 0]` makes the integrand `(1 - k² sin²θ)^{∓1/2}` continuous for real `θ`.
The negative-real `R_C` formula is proved by evaluating the symmetrically truncated integral
with a logarithmic primitive. Mathlib's FTC lemmas for derivatives of constant sign provide
integrability on both sides, including the square-root singularity at the endpoint `x = 0`.

## References

* NIST DLMF §19.2.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Real Topology

open DLMF.Core

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
private lemma cpow_half_eq_mul_cpow_neg_half (x : ℂ) : x ^ (1 / 2 : ℂ) = x *
    x ^ (-(1 / 2 : ℂ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · conv_lhs => rw [show (1 / 2 : ℂ) = 1 + (-(1 / 2 : ℂ)) by ring]
    rw [cpow_add _ _ hx, cpow_one]

/-- DLMF 19.2.6: `D(φ, k) = (F(φ, k) - E(φ, k))/k²` for `k ≠ 0`, whenever the integrand of `F` is
integrable along the segment `[0, φ]` (Lean's integrals are totalized). -/
@[dlmf 19.2.E6]
theorem incompleteEllipticD_eq {φ k : ℂ} (hk : k ≠ 0)
    (hF : IntervalIntegrable
      (fun t : ℝ => φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ))) volume 0 1) :
    incompleteEllipticD φ k = (incompleteEllipticF φ k - incompleteEllipticE φ k) / k ^ 2 := by
  have hb : ContinuousOn (fun t : ℝ => 1 - k ^ 2 * Complex.sin (t * φ) ^ 2) (uIcc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ => 1 - k ^ 2 * Complex.sin (t * φ) ^ 2).continuousOn
  have hE : IntervalIntegrable (fun t : ℝ => (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) *
      (φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ)))) volume 0 1 :=
    hF.continuousOn_mul hb
  rw [eq_div_iff (pow_ne_zero 2 hk), incompleteEllipticD, incompleteEllipticF, incompleteEllipticE,
      primitive_eq_integral,
    primitive_eq_integral, primitive_eq_integral, ← intervalIntegral.integral_mul_const]
  have h1 : (fun t : ℝ => φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (1 / 2 : ℂ)) =
      fun t : ℝ => (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) *
        (φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
    funext t; rw [cpow_half_eq_mul_cpow_neg_half]; ring
  rw [h1, ← intervalIntegral.integral_sub hF hE]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- DLMF 19.2.6 for real amplitude in the principal domain `1 - k² ∈ ℂ \ (-∞, 0]`, `k ≠ 0`. -/
@[dlmf 19.2.E6]
theorem incompleteEllipticD_eq_of_real {k : ℂ} (hk : k ≠ 0) (hk1 : 1 - k ^ 2 ∈ slitPlane) (φ : ℝ) :
    incompleteEllipticD φ k = (incompleteEllipticF φ k - incompleteEllipticE φ k) / k ^ 2 := by
  refine incompleteEllipticD_eq hk (Continuous.intervalIntegrable ?_ _ _)
  refine continuous_const.mul (Continuous.cpow (by fun_prop) continuous_const fun t => ?_)
  have := one_sub_sq_mul_sin_sq_mem_slitPlane hk1 (t * φ)
  simpa using this

/-- DLMF 19.2.8: `D(k) = (K(k) - E(k))/k²` in the principal domain `1 - k² ∈ ℂ \ (-∞, 0]`,
`k ≠ 0`. -/
@[dlmf 19.2.E8]
theorem completeEllipticD_eq {k : ℂ} (hk : k ≠ 0) (hk1 : 1 - k ^ 2 ∈ slitPlane) :
    completeEllipticD k = (completeEllipticK k - completeEllipticE k) / k ^ 2 := by
  have h := incompleteEllipticD_eq_of_real hk hk1 (π / 2)
  push_cast at h
  rw [completeEllipticD, h, completeEllipticK_eq_incompleteEllipticF, completeEllipticE]

/-- DLMF §19.2(ii): the principal values of `K(k)` and `E(k)` are even functions. -/
@[dlmf 19.2.ii]
theorem completeEllipticK_neg (k : ℂ) : completeEllipticK (-k) = completeEllipticK k := by
  simp [completeEllipticK]

/-- DLMF §19.2(ii): the principal value of `E(k)` is even. -/
@[dlmf 19.2.ii]
theorem completeEllipticE_neg (k : ℂ) : completeEllipticE (-k) = completeEllipticE k := by
  simp [completeEllipticE, incompleteEllipticE]

/-- `∫₀^b (1 - k² sin²θ)^s dθ` is holomorphic in `k` on the principal domain
`1 - k² ∈ ℂ \ (-∞, 0]`, for every exponent `s` and real `b`. -/
private lemma differentiableOn_integral_cpow (s : ℂ) (b : ℝ) :
    DifferentiableOn ℂ (fun k : ℂ => ∫ θ in (0 : ℝ)..b, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ s)
      {k | 1 - k ^ 2 ∈ slitPlane} := by
  have hU : IsOpen {k : ℂ | 1 - k ^ 2 ∈ slitPlane} :=
    isOpen_slitPlane.preimage (by fun_prop)
  refine Complex.differentiableOn_intervalIntegral_of_locally_dominated hU 0 b ?_ ?_ ?_
  · intro k hk
    refine (Continuous.cpow (by fun_prop) continuous_const fun θ =>
      one_sub_sq_mul_sin_sq_mem_slitPlane hk θ).aestronglyMeasurable
  · refine Eventually.of_forall fun θ k hk => ?_
    have hd : DifferentiableAt ℂ (fun x : ℂ => 1 - x ^ 2 * (Real.sin θ : ℂ) ^ 2) k := by fun_prop
    exact (hd.cpow (differentiableAt_const s)
      (one_sub_sq_mul_sin_sq_mem_slitPlane hk θ)).differentiableWithinAt
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
      have := one_sub_mul_ofReal_mem_slitPlane (hball hk) hu.1 hu.2
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
theorem differentiableOn_completeEllipticK_completeEllipticE :
    DifferentiableOn ℂ completeEllipticK {k | 1 - k ^ 2 ∈ slitPlane} ∧
      DifferentiableOn ℂ completeEllipticE {k | 1 - k ^ 2 ∈ slitPlane} := by
  refine ⟨differentiableOn_integral_cpow _ _, ?_⟩
  have h : completeEllipticE = fun k : ℂ => ∫ θ in (0 : ℝ)..(π / 2),
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) := funext completeEllipticE_eq_integral
  rw [h]; exact differentiableOn_integral_cpow _ _

/-- **Admitted.** DLMF §19.2(ii) and 19.2.9: `K'` and `E'` (defined by 19.2.9) are holomorphic on
`ℂ \ (-∞, 0]`: the branch point is `k = 0` and the principal branch is `|ph k| ≤ π`
(`complementaryEllipticK` is the analytic continuation of the literal integral from `Re k > 0`). -/
@[dlmf 19.2.ii]
theorem differentiableOn_complementaryEllipticK_complementaryEllipticE :
    DifferentiableOn ℂ complementaryEllipticK slitPlane ∧
        DifferentiableOn ℂ complementaryEllipticE slitPlane := by
  sorry

/-- The substitution `t = sin θ`: `∫₀^{π/2} h(sin²θ) dθ = ∫₀¹ (1-t²)^{-1/2} h(t²) dt`. -/
private lemma integral_sin_sq_subst (h : ℂ → ℂ) :
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
theorem complementaryEllipticK_eq_integral {k : ℂ} (hk : 0 < k.re) :
    complementaryEllipticK k = ∫ t in (0 : ℝ)..1,
      (1 - (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) * (1 - (1 - k ^ 2) * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  rw [(complementaryEllipticK_of_re_pos (Or.inl hk)).1, completeEllipticK_jacobiComodulusk,
      completeEllipticKPrime,
    integral_sin_sq_subst (fun u => (1 - (1 - k ^ 2) * u) ^ (-(1 / 2 : ℂ)))]

/-- DLMF 19.2.8_2: `E'(k) = ∫₀¹ √(1-(1-k²)t²)/√(1-t²) dt` for `|ph k| < π/2`. -/
@[dlmf 19.2.E8_2]
theorem complementaryEllipticE_eq_integral {k : ℂ} (hk : 0 < k.re) :
    complementaryEllipticE k = ∫ t in (0 : ℝ)..1,
      (1 - (1 - k ^ 2) * (t : ℂ) ^ 2) ^ (1 / 2 : ℂ) * (1 - (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  have h : jacobiComodulus k ^ 2 = 1 - k ^ 2 := by
    rw [jacobiComodulus, one_div, Complex.cpow_ofNat_inv_pow]
  rw [(complementaryEllipticK_of_re_pos (Or.inl hk)).2, completeEllipticE_eq_integral, h,
    integral_sin_sq_subst (fun u => (1 - (1 - k ^ 2) * u) ^ (1 / 2 : ℂ))]
  simp only [mul_comm]

/-- Real bridge for `K'`: for real `k > 0`, `K'(k) = Real.completeEllipticKOfParameter (1 - k²)`. -/
theorem complementaryEllipticK_ofReal {k : ℝ} (hk : 0 < k) :
    complementaryEllipticK k =
        (DLMF.Elliptic.Real.completeEllipticKOfParameter (1 - k ^ 2) : ℂ) := by
  have h : 0 < (k : ℂ).re ∨ ((k : ℂ).re = 0 ∧ 0 ≤ (k : ℂ).im) := Or.inl (by simpa using hk)
  simp only [complementaryEllipticK, h, ↓reduceIte]
  exact completeEllipticKPrime_ofReal (by positivity)

/-- Real bridge for `E'`: for real `k > 0`, `E'(k) = Real.completeEllipticEOfParameter (1 - k²)`. -/
theorem complementaryEllipticE_ofReal {k : ℝ} (hk : 0 < k) :
    complementaryEllipticE k =
        (DLMF.Elliptic.Real.completeEllipticEOfParameter (1 - k ^ 2) : ℂ) := by
  have h : 0 < (k : ℂ).re ∨ ((k : ℂ).re = 0 ∧ 0 ≤ (k : ℂ).im) := Or.inl (by simpa using hk)
  simp only [complementaryEllipticE, h, ↓reduceIte]
  refine completeEllipticE_eq_ofReal ?_ (by nlinarith [sq_nonneg k])
  rw [jacobiComodulus, one_div, Complex.cpow_ofNat_inv_pow]; push_cast; ring

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
private lemma integral_zero_pi_eq_two_mul {g : ℝ → ℂ} (hc : Continuous g)
    (hp : Function.Periodic g π)
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
private lemma integral_int_mul_pi_add {g : ℝ → ℂ} (hc : Continuous g) (hp : Function.Periodic g π)
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
  rw [h1, h2, integral_zero_pi_eq_two_mul hc hp he]; ring

/-- For a continuous even `g`, `∫₀^{-φ} g = -∫₀^φ g`. -/
private lemma integral_zero_neg_of_even {g : ℝ → ℂ} (he : ∀ x, g (-x) = g x) (φ : ℝ) :
    ∫ x in (0 : ℝ)..(-φ), g x = -∫ x in (0 : ℝ)..φ, g x := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := φ) g
  simp only [neg_zero, he] at h
  rw [h, intervalIntegral.integral_symm]

/-- The Legendre integrands `sin^{2j}θ (1 - k² sin²θ)^{p}` are continuous in real `θ` in the
principal domain, `π`-periodic and even. -/
private lemma legendre_integrand_continuous_periodic_even {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane)
    (j : ℕ) (p : ℂ) :
    let g : ℝ → ℂ := fun θ => (Real.sin θ : ℂ) ^ (2 * j) * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ p
    Continuous g ∧ Function.Periodic g π ∧ ∀ x, g (-x) = g x := by
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · refine (by fun_prop : Continuous fun θ : ℝ => (Real.sin θ : ℂ) ^ (2 * j)).mul
      (Continuous.cpow (by fun_prop) continuous_const fun θ => ?_)
    exact one_sub_sq_mul_sin_sq_mem_slitPlane hk θ
  · simp only [Real.sin_add_pi, ofReal_neg, pow_mul, neg_sq]
  · simp only [Real.sin_neg, ofReal_neg, pow_mul, neg_sq]

/-- DLMF 19.2.10 for real amplitude in the principal domain `1 - k² ∈ ℂ \ (-∞, 0]`:
`F(mπ ± φ, k) = 2mK(k) ± F(φ, k)`, `E(mπ ± φ, k) = 2mE(k) ± E(φ, k)`,
`D(mπ ± φ, k) = 2mD(k) ± D(φ, k)` for every integer `m`. -/
@[dlmf 19.2.E10]
theorem incEllInt_add_int_mul_pi {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (m : ℤ) (φ : ℝ) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    incompleteEllipticF (m * π + s * φ) k = 2 * m * completeEllipticK k + (s : ℂ) *
        incompleteEllipticF φ k ∧
      incompleteEllipticE (m * π + s * φ) k = 2 * m * completeEllipticE k + (s : ℂ) *
          incompleteEllipticE φ k ∧
      incompleteEllipticD (m * π + s * φ) k = 2 * m * completeEllipticD k + (s : ℂ) *
          incompleteEllipticD φ k := by
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
    obtain ⟨hc, hp, he⟩ := legendre_integrand_continuous_periodic_even hk j p
    rw [integral_int_mul_pi_add hc hp he]
    rcases hs with rfl | rfl
    · simp
    · rw [show (-1 : ℝ) * φ = -φ by ring, integral_zero_neg_of_even he]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hcast, incompleteEllipticF_ofReal_eq_integral, incompleteEllipticF_ofReal_eq_integral,
      completeEllipticK_eq_incompleteEllipticF, hpi, incompleteEllipticF_ofReal_eq_integral]
    simpa using key 0 (-(1 / 2 : ℂ))
  · rw [hcast, incompleteEllipticE_ofReal_eq_integral, incompleteEllipticE_ofReal_eq_integral,
      completeEllipticE_eq_integral]
    simpa using key 0 (1 / 2 : ℂ)
  · rw [hcast, incompleteEllipticD_ofReal_eq_integral, incompleteEllipticD_ofReal_eq_integral,
      completeEllipticD_eq_integral]
    simpa using key 1 (-(1 / 2 : ℂ))

/-! ### §19.2(iii) Bulirsch's integrals -/

/-- `cos²θ + (1 - k²) sin²θ = 1 - k² sin²θ`. -/
private lemma cos_sq_add_one_sub_sq_mul_sin_sq (k θ : ℂ) :
    Complex.cos θ ^ 2 + (1 - k ^ 2) * Complex.sin θ ^ 2 = 1 - k ^ 2 * Complex.sin θ ^ 2 := by
  linear_combination Complex.cos_sq_add_sin_sq θ

/-- `k'² = 1 - k²` for the principal `k' = √(1 - k²)`. -/
theorem jacobiComodulus_sq_eq_one_sub_sq (k : ℂ) : jacobiComodulus k ^ 2 = 1 - k ^ 2 := by
  rw [jacobiComodulus, one_div, Complex.cpow_ofNat_inv_pow]

/-- With `p = 1` Bulirsch's `cel` needs no principal value. -/
theorem bulirschCel_one_eq_primitive (kc : ℂ) (a b : ℝ) :
    bulirschCel kc 1 a b = Core.primitive (fun θ => (a * Complex.cos θ ^ 2 +
      b * Complex.sin θ ^ 2) * (Complex.cos θ ^ 2 + kc ^ 2 * Complex.sin θ ^ 2) ^ (-(1 / 2 : ℂ)))
        (π / 2) := by
  rw [bulirschCel, principalValueSegmentIntegral_eq_primitive (δ := 1) one_pos]
  · congr 1; funext θ; simp [Complex.cos_sq_add_sin_sq]
  · intro t _; simp [Complex.cos_sq_add_sin_sq]

/-- DLMF 19.2.13–19.2.14: with `k_c = k'`, `K(k) = cel(k_c, 1, 1, 1)` and `D(k) = cel(k_c, 1, 0, 1)`
for every complex `k`, and `Π(α², k) = cel(k_c, 1 - α², 1, 1)` for real `α²` (`p = 1 - α²`, a
principal value on both sides when `α² > 1`). -/
@[dlmf 19.2.E14, dlmf 19.2.E13]
theorem compEllInt_eq_bulirschCel (k : ℂ) (α2 : ℝ) :
    completeEllipticK k = bulirschCel (jacobiComodulus k) 1 1 1 ∧
      completeEllipticD k = bulirschCel (jacobiComodulus k) 1 0 1 ∧
      completeEllipticPi α2 k = bulirschCel (jacobiComodulus k) (1 - α2) 1 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bulirschCel_one_eq_primitive, completeEllipticK_eq_incompleteEllipticF,
        incompleteEllipticF]
    congr 1; funext θ
    rw [jacobiComodulus_sq_eq_one_sub_sq, cos_sq_add_one_sub_sq_mul_sin_sq]; push_cast
    rw [one_mul, one_mul, Complex.cos_sq_add_sin_sq, one_mul]
  · rw [bulirschCel_one_eq_primitive, completeEllipticD, incompleteEllipticD]
    congr 1; funext θ
    rw [jacobiComodulus_sq_eq_one_sub_sq, cos_sq_add_one_sub_sq_mul_sin_sq]; push_cast; ring
  · rw [completeEllipticPi, incompleteEllipticPi, bulirschCel]
    have hg : ∀ θ : ℂ, Complex.cos θ ^ 2 + ((1 - α2 : ℝ) : ℂ) * Complex.sin θ ^ 2 =
        1 - α2 * Complex.sin θ ^ 2 := fun θ => by
      push_cast; linear_combination Complex.cos_sq_add_sin_sq θ
    simp only [hg, jacobiComodulus_sq_eq_one_sub_sq, cos_sq_add_one_sub_sq_mul_sin_sq,
        ofReal_one, one_mul,
      Complex.cos_sq_add_sin_sq, div_eq_inv_mul, mul_one]

/-- DLMF 19.2.14: `E(k) = cel(k_c, 1, 1, k_c²)` for every real `k` (`k_c² = 1 - k²` is real, as
`cel` requires). -/
@[dlmf 19.2.E14]
theorem completeEllipticE_eq_bulirschCel (k : ℝ) :
    completeEllipticE k = bulirschCel (jacobiComodulus k) 1 1 (1 - k ^ 2) := by
  rw [bulirschCel_one_eq_primitive, completeEllipticE, incompleteEllipticE]
  congr 1; funext θ
  rw [jacobiComodulus_sq_eq_one_sub_sq]
  push_cast
  rw [cos_sq_add_one_sub_sq_mul_sin_sq, show (1 : ℂ) * Complex.cos θ ^ 2 + (1 - (k : ℂ) ^ 2) *
    Complex.sin θ ^ 2 = 1 - (k : ℂ) ^ 2 * Complex.sin θ ^ 2 from by
      rw [one_mul, cos_sq_add_one_sub_sq_mul_sin_sq], cpow_half_eq_mul_cpow_neg_half]

/-- DLMF 19.2.14: `(E(k) - k'² K(k))/k² = cel(k_c, 1, 1, 0)` in the principal domain
`1 - k² ∈ ℂ \ (-∞, 0]`, `k ≠ 0`. -/
@[dlmf 19.2.E14]
theorem completeEllipticE_sub_eq_bulirschCel {k : ℂ} (hk : k ≠ 0) (hk1 : 1 - k ^ 2 ∈ slitPlane) :
    (completeEllipticE k - jacobiComodulus k ^ 2 * completeEllipticK k) / k ^ 2 =
      bulirschCel (jacobiComodulus k) 1 1 0 := by
  have hc : Continuous fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) :=
    Continuous.cpow (by fun_prop) continuous_const fun θ =>
      one_sub_sq_mul_sin_sq_mem_slitPlane hk1 θ
  have hpi : ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
  have hE : Continuous fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) :=
    Continuous.cpow (by fun_prop) continuous_const fun θ =>
      one_sub_sq_mul_sin_sq_mem_slitPlane hk1 θ
  rw [div_eq_iff (pow_ne_zero 2 hk), bulirschCel_one_eq_primitive, hpi,
      primitive_ofReal,
    completeEllipticE_eq_integral, completeEllipticK, jacobiComodulus_sq_eq_one_sub_sq,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hE.intervalIntegrable _ _) ((hc.intervalIntegrable _ _).const_mul (1 - k ^ 2)),
    ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Complex.ofReal_sin, Complex.ofReal_one, Complex.ofReal_zero]
  rw [cos_sq_add_one_sub_sq_mul_sin_sq, cpow_half_eq_mul_cpow_neg_half]
  linear_combination (-(k ^ 2) * (1 - k ^ 2 * Complex.sin (θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) *
    Complex.cos_sq_add_sin_sq (θ : ℂ)

/-- DLMF 19.2.15: `F(φ, k) = el1(x, k_c)` with `x = tan φ`, `k_c = k'`, for real `|φ| < π/2` and
every complex `k`. -/
@[dlmf 19.2.E15, dlmf 19.2.E13]
theorem incompleteEllipticF_eq_bulirschEl1 (k : ℂ) {φ : ℝ} (h0 : -(π / 2) < φ) (h1 : φ < π / 2) :
    incompleteEllipticF φ k = bulirschEl1 (Real.tan φ) (jacobiComodulus k) := by
  rw [bulirschEl1, ← Complex.ofReal_arctan, Real.arctan_tan h0 h1, incompleteEllipticF]
  congr 1; funext θ
  rw [jacobiComodulus_sq_eq_one_sub_sq, cos_sq_add_one_sub_sq_mul_sin_sq]

/-- `r^{-1/2} = (√r)⁻¹` for real `r ≥ 0`. -/
private lemma ofReal_cpow_neg_half_eq {r : ℝ} (hr : 0 ≤ r) :
    (r : ℂ) ^ (-(1 / 2 : ℂ)) = (((√r)⁻¹ : ℝ) : ℂ) := by
  rw [cpow_neg, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hr,
    ← Real.sqrt_eq_rpow, ofReal_inv]

/-- `r^{1/2} = √r` for real `r ≥ 0`. -/
private lemma ofReal_cpow_half_eq {r : ℝ} (hr : 0 ≤ r) :
    (r : ℂ) ^ (1 / 2 : ℂ) = ((√r : ℝ) : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hr,
    ← Real.sqrt_eq_rpow]

/-- The integrand of `el2(tan φ, k', a, b)` at real `θ` with `cos θ > 0`:
`(a + b tan²θ)((1 + tan²θ)(1 + k'² tan²θ))^{-1/2} = (a cos²θ + b sin²θ)/√(1 - k² sin²θ)`. -/
private lemma bulirschEl2_integrand_ofReal {k θ : ℝ} (hk : k ^ 2 < 1) (hc : 0 < Real.cos θ)
    (a b : ℝ) :
    ((a : ℂ) + b * Complex.tan θ ^ 2) * ((1 + Complex.tan θ ^ 2) *
      (1 + jacobiComodulus k ^ 2 * Complex.tan θ ^ 2)) ^ (-(1 / 2 : ℂ)) =
      (((a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2) / √(1 - k ^ 2 * Real.sin θ ^ 2) : ℝ) : ℂ) := by
  have hD : 0 < 1 - k ^ 2 * Real.sin θ ^ 2 := by nlinarith [Real.sin_sq_le_one θ]
  have hsc := Real.sin_sq_add_cos_sq θ
  set T := Real.tan θ with hT
  have hTe : T = Real.sin θ / Real.cos θ := Real.tan_eq_sin_div_cos θ
  have e : ((a : ℂ) + b * Complex.tan θ ^ 2) * ((1 + Complex.tan θ ^ 2) *
      (1 + jacobiComodulus k ^ 2 * Complex.tan θ ^ 2)) ^ (-(1 / 2 : ℂ)) =
      (((a + b * T ^ 2) : ℝ) : ℂ) * ((((1 + T ^ 2) * (1 + (1 - k ^ 2) * T ^ 2)) : ℝ) : ℂ) ^
        (-(1 / 2 : ℂ)) := by
    rw [jacobiComodulus_sq_eq_one_sub_sq, ← ofReal_tan, ← hT]
    push_cast; ring
  have e2 : (1 + T ^ 2) * (1 + (1 - k ^ 2) * T ^ 2) =
      (√(1 - k ^ 2 * Real.sin θ ^ 2) / Real.cos θ ^ 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hD.le, hTe]
    field_simp
    linear_combination (Real.cos θ ^ 2 - k ^ 2 * Real.sin θ ^ 2 + 1 + Real.sin θ ^ 2) * hsc
  rw [e, e2, ofReal_cpow_neg_half_eq (sq_nonneg _), Real.sqrt_sq (by positivity), ← ofReal_mul]
  congr 1
  rw [hTe]
  have h1 : 0 < √(1 - k ^ 2 * Real.sin θ ^ 2) := Real.sqrt_pos.mpr hD
  field_simp

/-- DLMF 19.2.15: `F(φ, k) = el2(x, k_c, 1, 1)`, `E(φ, k) = el2(x, k_c, 1, k_c²)`,
`D(φ, k) = el2(x, k_c, 0, 1)` with `x = tan φ`, `k_c = k'`, for real `k` with `k² < 1` and real
`|φ| < π/2`. -/
@[dlmf 19.2.E15]
theorem incEllInt_eq_bulirschEl2 {k φ : ℝ} (hk : k ^ 2 < 1) (h0 : -(π / 2) < φ)
    (h1 : φ < π / 2) :
    incompleteEllipticF φ k = bulirschEl2 (Real.tan φ) (jacobiComodulus k) 1 1 ∧
      incompleteEllipticE φ k = bulirschEl2 (Real.tan φ) (jacobiComodulus k) 1 (1 - k ^ 2) ∧
      incompleteEllipticD φ k = bulirschEl2 (Real.tan φ) (jacobiComodulus k) 0 1 := by
  have hc : ∀ θ ∈ uIcc 0 φ, 0 < Real.cos θ := fun θ hθ => by
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
    · rcases le_total 0 φ with h | h
      · rw [uIcc_of_le h] at hθ; linarith [hθ.1, Real.pi_pos]
      · rw [uIcc_of_ge h] at hθ; linarith [hθ.1]
    · rcases le_total 0 φ with h | h
      · rw [uIcc_of_le h] at hθ; linarith [hθ.2]
      · rw [uIcc_of_ge h] at hθ; linarith [hθ.2, Real.pi_pos]
  have hD : ∀ θ : ℝ, 0 < 1 - k ^ 2 * Real.sin θ ^ 2 := fun θ => by
    nlinarith [Real.sin_sq_le_one θ]
  have hcast : ∀ θ : ℝ, (1 - (k : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) =
      ((1 - k ^ 2 * Real.sin θ ^ 2 : ℝ) : ℂ) := fun θ => by push_cast; ring
  have hel2 : ∀ a b : ℝ, bulirschEl2 (Real.tan φ) (jacobiComodulus k) a b =
      ∫ θ in (0 : ℝ)..φ, (((a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2) /
        √(1 - k ^ 2 * Real.sin θ ^ 2) : ℝ) : ℂ) := fun a b => by
    rw [bulirschEl2, ← Complex.ofReal_arctan, Real.arctan_tan h0 h1, primitive_ofReal]
    exact intervalIntegral.integral_congr fun θ hθ =>
      bulirschEl2_integrand_ofReal hk (hc θ hθ) a b
  refine ⟨?_, ?_, ?_⟩
  · rw [hel2, incompleteEllipticF_ofReal_eq_integral]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [hcast, ofReal_cpow_neg_half_eq (hD θ).le]
    congr 1
    have := Real.sin_sq_add_cos_sq θ
    have h1 : 0 < √(1 - k ^ 2 * Real.sin θ ^ 2) := Real.sqrt_pos.mpr (hD θ)
    field_simp
    linarith
  · rw [hel2, incompleteEllipticE_ofReal_eq_integral]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [hcast, ofReal_cpow_half_eq (hD θ).le]
    congr 1
    have := Real.sin_sq_add_cos_sq θ
    have h1 : 0 < √(1 - k ^ 2 * Real.sin θ ^ 2) := Real.sqrt_pos.mpr (hD θ)
    rw [eq_div_iff h1.ne', Real.mul_self_sqrt (hD θ).le]
    linear_combination -this
  · rw [hel2, incompleteEllipticD_ofReal_eq_integral]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [hcast, ofReal_cpow_neg_half_eq (hD θ).le]
    push_cast
    ring

/-- DLMF 19.2.16: `el3(x, k_c, p) = Π(arctan x, 1 - p, k)` with `k_c = k'`, for every complex `x`
and `k` and real `p` (both sides are principal values at an interior singularity). -/
@[dlmf 19.2.E16]
theorem bulirschEl3_eq_incompleteEllipticPi (x k : ℂ) (p : ℝ) :
    bulirschEl3 x (jacobiComodulus k) p = incompleteEllipticPi (Complex.arctan x) (1 - p) k := by
  rw [bulirschEl3, incompleteEllipticPi]
  have hg : ∀ θ : ℂ, Complex.cos θ ^ 2 + (p : ℂ) * Complex.sin θ ^ 2 =
      1 - (1 - (p : ℂ)) * Complex.sin θ ^ 2 := fun θ => by
    linear_combination Complex.cos_sq_add_sin_sq θ
  simp only [hg, jacobiComodulus_sq_eq_one_sub_sq, cos_sq_add_one_sub_sq_mul_sin_sq]

/-- `(r w)^s = r^s w^s` for real `r > 0`. -/
private lemma ofReal_mul_cpow_of_pos' {r : ℝ} (hr : 0 < r) (w s : ℂ) :
    ((r : ℂ) * w) ^ s = (r : ℂ) ^ s * w ^ s := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  by_cases hw : w = 0
  · subst hw
    by_cases hs : s = 0
    · simp [hs]
    · simp [zero_cpow hs]
  · rw [cpow_def_of_ne_zero (mul_ne_zero hr0 hw), log_ofReal_mul hr hw, cpow_def_of_ne_zero hr0,
      cpow_def_of_ne_zero hw, ← Complex.exp_add, ← ofReal_log hr.le]
    congr 1; ring

/-- `cos²θ + k_c² sin²θ ∈ ℂ \ (-∞, 0]` for real `θ` when `k_c² ∈ ℂ \ (-∞, 0]`. -/
private lemma cos_sq_add_mul_sin_sq_mem_slitPlane {kc : ℂ} (hkc : kc ^ 2 ∈ slitPlane) (θ : ℝ) :
    Complex.cos θ ^ 2 + kc ^ 2 * Complex.sin θ ^ 2 ∈ slitPlane := by
  have h := starConvex_one_slitPlane.add_smul_mem (y := kc ^ 2 - 1) (by simpa using hkc)
    (sq_nonneg (Real.sin θ)) (Real.sin_sq_le_one θ)
  convert h using 1
  rw [real_smul, ofReal_pow, ofReal_sin]
  linear_combination Complex.sin_sq_add_cos_sq (θ : ℂ)

/-- `∫₀^{arctan x} G → ∫₀^{π/2} G` as `x → +∞`, for continuous `G`. -/
private lemma tendsto_integral_arctan {G : ℝ → ℂ} (hG : Continuous G) :
    Tendsto (fun x : ℝ => ∫ θ in (0 : ℝ)..Real.arctan x, G θ) atTop
      (𝓝 (∫ θ in (0 : ℝ)..(π / 2), G θ)) := by
  have hc : Continuous fun u : ℝ => ∫ θ in (0 : ℝ)..u, G θ :=
    intervalIntegral.continuous_primitive (fun a b => hG.intervalIntegrable a b) 0
  exact (hc.tendsto _).comp (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds)

/-- DLMF §19.2(iii): the integrals are complete if `x = ∞`: as real `x → +∞`,
`el1(x, k_c) → cel(k_c, 1, 1, 1)`, `el2(x, k_c, a, b) → cel(k_c, 1, a, b)` and, for `p > 0`,
`el3(x, k_c, p) → cel(k_c, p, 1, 1)`, when `k_c² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.2.iii]
theorem tendsto_bulirsch_atTop {kc : ℂ} (hkc : kc ^ 2 ∈ slitPlane) (a b : ℝ) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun x : ℝ => bulirschEl1 x kc) atTop (𝓝 (bulirschCel kc 1 1 1)) ∧
      Tendsto (fun x : ℝ => bulirschEl2 x kc a b) atTop (𝓝 (bulirschCel kc 1 a b)) ∧
      Tendsto (fun x : ℝ => bulirschEl3 x kc p) atTop (𝓝 (bulirschCel kc p 1 1)) := by
  set w : ℝ → ℂ := fun θ => Complex.cos θ ^ 2 + kc ^ 2 * Complex.sin θ ^ 2 with hw
  have hwS : ∀ θ : ℝ, w θ ∈ slitPlane := cos_sq_add_mul_sin_sq_mem_slitPlane hkc
  have hwc : Continuous fun θ : ℝ => w θ ^ (-(1 / 2 : ℂ)) :=
    Continuous.cpow (by fun_prop) continuous_const hwS
  have hpi : ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
  have harc : ∀ x : ℝ, Complex.arctan (x : ℂ) = ((Real.arctan x : ℝ) : ℂ) := fun x =>
    (ofReal_arctan x).symm
  -- the real form of `cos² + p sin²`
  have hg : ∀ θ : ℝ, Complex.cos θ ^ 2 + (p : ℂ) * Complex.sin θ ^ 2 =
      ((Real.cos θ ^ 2 + p * Real.sin θ ^ 2 : ℝ) : ℂ) := fun θ => by push_cast; ring
  have hgpos : ∀ θ : ℝ, min 1 p ≤ Real.cos θ ^ 2 + p * Real.sin θ ^ 2 := fun θ => by
    have := Real.sin_sq_add_cos_sq θ
    have h1 : min 1 p ≤ 1 := min_le_left _ _
    have h2 : min 1 p ≤ p := min_le_right _ _
    nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]
  have hmin : 0 < min 1 p := lt_min one_pos hp
  have hpv : ∀ (f : ℂ → ℂ) (u : ℝ),
      principalValueSegmentIntegral (fun θ => Complex.cos θ ^ 2 + (p : ℂ) * Complex.sin θ ^ 2) f u =
        ∫ θ in (0 : ℝ)..u, f θ := fun f u => by
    rw [principalValueSegmentIntegral_eq_primitive (δ := min 1 p) hmin,
        primitive_ofReal]
    intro t _
    rw [← ofReal_mul, hg, Complex.norm_real, Real.norm_eq_abs]
    exact (hgpos _).trans (le_abs_self _)
  refine ⟨?_, ?_, ?_⟩
  · have e : ∀ x : ℝ, bulirschEl1 x kc = ∫ θ in (0 : ℝ)..Real.arctan x, w θ ^ (-(1 / 2 : ℂ)) :=
      fun x => by rw [bulirschEl1, harc, primitive_ofReal]
    simp only [e]
    convert tendsto_integral_arctan hwc using 2
    rw [bulirschCel_one_eq_primitive, hpi, primitive_ofReal]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hw]
    rw [ofReal_one, one_mul, one_mul, Complex.cos_sq_add_sin_sq, one_mul]
  · have hint : ∀ θ : ℝ, 0 < Real.cos θ → ((a : ℂ) + b * Complex.tan θ ^ 2) *
        ((1 + Complex.tan θ ^ 2) * (1 + kc ^ 2 * Complex.tan θ ^ 2)) ^ (-(1 / 2 : ℂ)) =
        (a * Complex.cos θ ^ 2 + b * Complex.sin θ ^ 2) * w θ ^ (-(1 / 2 : ℂ)) := by
      intro θ hc
      have hc0 : Complex.cos (θ : ℂ) ≠ 0 := by
        rw [← ofReal_cos]; exact ofReal_ne_zero.mpr hc.ne'
      have hsc := Complex.sin_sq_add_cos_sq (θ : ℂ)
      have e1 : (1 + Complex.tan θ ^ 2) * (1 + kc ^ 2 * Complex.tan θ ^ 2) =
          (((1 / Real.cos θ ^ 2) ^ 2 : ℝ) : ℂ) * w θ := by
        simp only [hw]
        rw [Complex.tan_eq_sin_div_cos]
        push_cast
        field_simp
        linear_combination (kc ^ 2 * Complex.sin θ ^ 2 + Complex.cos (θ : ℂ) ^ 2) * hsc
      rw [e1, ofReal_mul_cpow_of_pos' (by positivity), ofReal_cpow_neg_half_eq (by positivity),
        Real.sqrt_sq (by positivity), Complex.tan_eq_sin_div_cos, ← mul_assoc]
      congr 1
      push_cast
      field_simp
    have e : ∀ x : ℝ, bulirschEl2 x kc a b = ∫ θ in (0 : ℝ)..Real.arctan x,
        (a * Complex.cos θ ^ 2 + b * Complex.sin θ ^ 2) * w θ ^ (-(1 / 2 : ℂ)) := fun x => by
      rw [bulirschEl2, harc, primitive_ofReal]
      refine intervalIntegral.integral_congr fun θ hθ => hint θ ?_
      have h1 := Real.arctan_lt_pi_div_two x
      have h2 := Real.neg_pi_div_two_lt_arctan x
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · rcases le_total 0 (Real.arctan x) with h | h
        · rw [uIcc_of_le h] at hθ; linarith [hθ.1, Real.pi_pos]
        · rw [uIcc_of_ge h] at hθ; linarith [hθ.1]
      · rcases le_total 0 (Real.arctan x) with h | h
        · rw [uIcc_of_le h] at hθ; linarith [hθ.2]
        · rw [uIcc_of_ge h] at hθ; linarith [hθ.2, Real.pi_pos]
    simp only [e]
    have hc : Continuous fun θ : ℝ =>
        ((a : ℂ) * Complex.cos θ ^ 2 + b * Complex.sin θ ^ 2) * w θ ^ (-(1 / 2 : ℂ)) :=
      Continuous.mul (by fun_prop) hwc
    convert tendsto_integral_arctan hc using 2
    rw [bulirschCel_one_eq_primitive, hpi, primitive_ofReal]
  · have e : ∀ x : ℝ, bulirschEl3 x kc p =
        ∫ θ in (0 : ℝ)..Real.arctan x, (Complex.cos θ ^ 2 + (p : ℂ) * Complex.sin θ ^ 2)⁻¹ *
          w θ ^ (-(1 / 2 : ℂ)) := fun x => by
      rw [bulirschEl3, harc, hpv]
    simp only [e]
    have hc : Continuous fun θ : ℝ => (Complex.cos θ ^ 2 + (p : ℂ) * Complex.sin θ ^ 2)⁻¹ *
        w θ ^ (-(1 / 2 : ℂ)) := by
      refine Continuous.mul (Continuous.inv₀ (by fun_prop) fun θ => ?_) hwc
      rw [hg]; exact ofReal_ne_zero.mpr (hmin.trans_le (hgpos θ)).ne'
    convert tendsto_integral_arctan hc using 2
    rw [bulirschCel, hpi, hpv]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hw]
    rw [ofReal_one, one_mul, one_mul, Complex.cos_sq_add_sin_sq, one_div]

/-! ### §19.2(iv) The function `R_C(x, y)` -/

/-- DLMF 19.2.17: for `y` not a negative real number, `R_C(x, y) = ½ ∫₀^∞ dt/(√(t+x)(t+y))`
(ACQ19C's `symmetricEllipticRC`; a Cauchy principal value when `y < 0`). -/
@[dlmf 19.2.E17]
theorem symmetricEllipticRC_eq_integral {x y : ℂ} (hy : ¬IsNegReal y) :
    symmetricEllipticRC x y =
      (1 / 2) * ∫ t in Ioi (0 : ℝ), (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹ := by
  simp [symmetricEllipticRC, hy]

/-- DLMF 19.2.17 (principal-value case): for `y < 0`, `R_C(x, y)` is one half of the Cauchy
principal value of `∫₀^∞ dt/(√(t+x)(t+y))` at `t = -y`. -/
@[dlmf 19.2.E17]
theorem symmetricEllipticRC_eq_cauchyPV {x y : ℂ} (hy : IsNegReal y) :
    symmetricEllipticRC x y =
      (1 / 2) * principalValueIoi
          (fun t => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹) (-y.re) := by
  simp [symmetricEllipticRC, hy]

/-- `R_C(0, y) = (π/2) y^{-1/2}` for `y ∈ ℂ \ (-∞, 0]` (via `R_F(0, y, y)`, DLMF 19.16.20). -/
private lemma symmetricEllipticRC_zero_left {y : ℂ} (hy : y ∈ slitPlane) :
    symmetricEllipticRC 0 y = π / 2 * y ^ (-(1 / 2 : ℂ)) := by
  rw [symmetricEllipticRC_eq_symmetricEllipticRF 0 (not_isNegReal_of_mem_slitPlane hy),
    symmetricEllipticRF_zero_left hy hy]
  have : (![y, y] : Fin 2 → ℂ) = fun _ => y := by funext i; fin_cases i <;> rfl
  rw [this, symmetricEllipticR_const _ _ hy (by norm_num)]

/-- `R_C(x, x) = x^{-1/2}` for `x ∈ ℂ \ (-∞, 0]` (DLMF 19.16.11 with `R_C = R_{-1/2}(1/2, 1)`). -/
private lemma symmetricEllipticRC_self {x : ℂ} (hx : x ∈ slitPlane) :
    symmetricEllipticRC x x = x ^ (-(1 / 2 : ℂ)) := by
  rw [symmetricEllipticRC_eq_symmetricEllipticR hx hx]
  have : (![x, x] : Fin 2 → ℂ) = fun _ => x := by funext i; fin_cases i <;> rfl
  rw [this, symmetricEllipticR_const _ _ hx]
  norm_num
  rw [show (3/2 : ℂ) = 1/2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]
  exact mul_ne_zero (by norm_num) Gamma_one_half_ne_zero

/-- `R_C(0, y) = (π/2)/√y` for real `y > 0`. -/
private lemma symmetricEllipticRC_zero_left_ofReal {y : ℝ} (hy : 0 < y) :
    symmetricEllipticRC 0 y = ((π / 2 / Real.sqrt y : ℝ) : ℂ) := by
  rw [symmetricEllipticRC_zero_left (by simpa using hy),
    show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow hy.le, Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow]
  push_cast; ring

/-- For `0 < y < x`, `artanh √((x-y)/x) = ln((√x + √(x-y))/√y)`. -/
private lemma artanh_sqrt_eq_log {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
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
theorem symmetricEllipticRC_of_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    symmetricEllipticRC x y = ((Real.arccos (Real.sqrt (x / y)) / Real.sqrt (y - x) : ℝ) : ℂ) ∧
      (0 < x → symmetricEllipticRC x y =
        ((Real.arctan (Real.sqrt ((y - x) / x)) / Real.sqrt (y - x) : ℝ) : ℂ)) := by
  have hy : 0 < y := hx.trans_lt hxy
  rcases hx.lt_or_eq with hx | rfl
  · have h : symmetricEllipticRC x y =
        ((Real.arccos (Real.sqrt (x / y)) / Real.sqrt (y - x) : ℝ) : ℂ) := by
      rw [symmetricEllipticRC_eq_carlsonRC (by simpa using hx) (by simpa using hy),
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
    rw [show ((0 : ℝ) : ℂ) = 0 by simp, symmetricEllipticRC_zero_left_ofReal hy]
    simp

/-- DLMF 19.2.19: for `0 < y < x`,
`R_C(x, y) = (x-y)^{-1/2} artanh √((x-y)/x) = (x-y)^{-1/2} ln((√x + √(x-y))/√y)`. -/
@[dlmf 19.2.E19]
theorem symmetricEllipticRC_of_gt {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
    symmetricEllipticRC x y =
        ((Real.artanh (Real.sqrt ((x - y) / x)) / Real.sqrt (x - y) : ℝ) : ℂ) ∧
      symmetricEllipticRC x y =
        ((Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt y) / Real.sqrt (x - y) : ℝ) :
          ℂ) := by
  have hx : 0 < x := hy.trans hxy
  have h : symmetricEllipticRC x y = ((Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt y) /
      Real.sqrt (x - y) : ℝ) : ℂ) := by
    rw [symmetricEllipticRC_eq_carlsonRC (by simpa using hx) (by simpa using hy),
      Carlson.TwoVariable.carlsonRC_of_gt hy hxy]
  exact ⟨by rw [h, artanh_sqrt_eq_log hy hxy], h⟩

/-- The logarithmic primitive of the real RC kernel away from its pole. -/
private lemma hasDerivAt_rcNeg_primitive {x y t : ℝ} (hx : 0 ≤ x) (hy : y < 0) (ht : 0 < t)
    (h : t + y ≠ 0) :
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
    convert ((tendsto_const_nhds.sub hi).div (tendsto_const_nhds.add hi)
        (by norm_num : (1 : ℝ) + 0 ≠ 0)) using 1; norm_num
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
/-- The real RC integral with a symmetric interval removed is the sum of its two primitive
differences. -/
private lemma integral_rcNeg_kernel_truncated {x y ε : ℝ} (hx : 0 ≤ x) (hy : y < 0) (he : 0 < ε)
    (hec : ε < -y) :
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
    rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith : 0 ≤ -y - ε)]
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
    (hF (-y + ε) (by linarith)).continuousWithinAt hrightD hrightpos
        (tendsto_rcNeg_primitive_atTop hx hy)
  have hrightval := integral_Ioi_of_hasDerivAt_of_nonneg
    (hF (-y + ε) (by linarith)).continuousWithinAt hrightD hrightpos
        (tendsto_rcNeg_primitive_atTop hx hy)
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
/-- The complex symmetric truncations of the RC kernel converge to the real logarithmic value. -/
private lemma tendsto_integral_rcNeg_kernel_truncated_complex {x y : ℝ} (hx : 0 ≤ x) (hy : y < 0) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ) \ Icc (-y - ε) (-y + ε),
      (((t : ℂ) + (x : ℂ)) ^ (1 / 2 : ℂ) * ((t : ℂ) + (y : ℂ)))⁻¹) (𝓝[>] 0)
      (𝓝 ((-(Real.log y - 2 * Real.log (Real.sqrt x + Real.sqrt (x - y))) /
        Real.sqrt (x - y) : ℝ) : ℂ)) := by
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
  have hl := Complex.continuous_ofReal.tendsto _ |>.comp
      (tendsto_integral_rcNeg_kernel_truncated hx hy)
  simpa only [Function.comp_def, hcast] using hl

/-- For real `x ≥ 0 > y`, the symmetric truncations of `∫₀^∞ dt/(√(t+x)(t+y))` about `t = -y`
converge to `2 R_C(x, y)`: the Cauchy principal value defining `R_C` exists. -/
theorem tendsto_integral_symmetricEllipticRC_truncated {x y : ℝ} (hx : 0 ≤ x) (hy : y < 0) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ) \ Icc (-y - ε) (-y + ε),
      (((t : ℂ) + (x : ℂ)) ^ (1 / 2 : ℂ) * ((t : ℂ) + (y : ℂ)))⁻¹) (𝓝[>] 0)
      (𝓝 (2 * symmetricEllipticRC x y)) := by
  have hl' := tendsto_integral_rcNeg_kernel_truncated_complex hx hy
  convert hl' using 2
  rw [symmetricEllipticRC_eq_cauchyPV
      (show IsNegReal (y : ℂ) by exact ⟨by simp, by simpa using hy⟩),
    principalValueIoi, ofReal_re, hl'.limUnder_eq]
  ring

/-- The negative-real RC principal value equals its real logarithmic expression. -/
private lemma symmetricEllipticRC_of_neg_log {x y : ℝ} (hx : 0 ≤ x) (hy : y < 0) :
    symmetricEllipticRC x y = ((Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt (-y)) /
      Real.sqrt (x - y) : ℝ) : ℂ) := by
  have ha : 0 < Real.sqrt (x - y) := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < Real.sqrt (-y) := Real.sqrt_pos.mpr (by linarith)
  have hl' := tendsto_integral_rcNeg_kernel_truncated_complex hx hy
  rw [symmetricEllipticRC_eq_cauchyPV
      (show IsNegReal (y : ℂ) by exact ⟨by simp, by simpa using hy⟩),
    principalValueIoi, ofReal_re, hl'.limUnder_eq]
  rw [Real.log_div (by positivity) hb.ne', Real.log_sqrt (by linarith : 0 ≤ -y),
    ← Real.log_neg_eq_log y]
  push_cast
  ring

/-- DLMF 19.2.20: for `y < 0 ≤ x` the Cauchy principal value is hyperbolic:
`R_C(x, y) = √(x/(x-y)) R_C(x-y, -y) = (x-y)^{-1/2} artanh √(x/(x-y))
= (x-y)^{-1/2} ln((√x + √(x-y))/√(-y))`. -/
@[dlmf 19.2.E20]
theorem symmetricEllipticRC_of_neg {x y : ℝ} (hy : y < 0) (hx : 0 ≤ x) :
    symmetricEllipticRC x y = (Real.sqrt (x / (x - y)) : ℂ) * symmetricEllipticRC (x - y) (-y) ∧
      symmetricEllipticRC x y =
        ((Real.artanh (Real.sqrt (x / (x - y))) / Real.sqrt (x - y) : ℝ) : ℂ) ∧
      symmetricEllipticRC x y =
        ((Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt (-y)) / Real.sqrt (x - y) : ℝ) :
          ℂ) := by
  have hlog := symmetricEllipticRC_of_neg_log hx hy
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
    have hc := symmetricEllipticRC_of_gt hy' (by linarith : -y < x - y)
    have hat := artanh_sqrt_eq_log hy' (by linarith : -y < x - y)
    rw [show x - y- -y = x by ring, add_comm (Real.sqrt (x - y))] at hc hat
    have he : Real.sqrt (x / (x - y)) = Real.sqrt x / Real.sqrt (x - y) := Real.sqrt_div' _ hxy.le
    refine ⟨?_, ?_, hlog⟩
    · rw [hlog, ← ofReal_sub, ← ofReal_neg, hc.2, he]
      push_cast
      field_simp [ofReal_ne_zero.mpr hb.ne', ofReal_ne_zero.mpr ha.ne']
    · rw [hlog, hat]

/-- The substitution `u = v²` in a unit-interval integral. -/
private lemma integral_sq_subst (h : ℂ → ℂ) :
    ∫ v in (0 : ℝ)..1, h ((v : ℂ) ^ 2) =
      (1 / 2) * ∫ u in (0 : ℝ)..1, (u : ℂ) ^ (-(1 / 2) : ℂ) * h u := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have himg : (fun v : ℝ => v ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
    ext u; constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨by nlinarith [hv.1], by nlinarith [hv.1, hv.2]⟩
    · intro hu
      refine ⟨Real.sqrt u, ⟨Real.sqrt_pos.mpr hu.1, ?_⟩, Real.sq_sqrt hu.1.le⟩
      rw [Real.sqrt_lt' one_pos]; simpa using hu.2
  have H := integral_image_eq_integral_abs_deriv_smul (f := fun v : ℝ => v ^ 2)
    (f' := fun v => 2 * v) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (fun v _ => by simpa using (hasDerivAt_pow 2 v).hasDerivWithinAt)
    (fun a ha b hb hab => (pow_left_inj₀ ha.1.le hb.1.le two_ne_zero).mp hab)
    (fun u : ℝ => (u : ℂ) ^ (-(1 / 2) : ℂ) * h u)
  rw [himg] at H
  rw [H, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  have hv0 : 0 < v := hv.1
  have hc : ((v ^ 2 : ℝ) : ℂ) ^ (-(1 / 2) : ℂ) = (v : ℂ)⁻¹ := by
    rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; rfl,
      ← ofReal_cpow (sq_nonneg v), ← ofReal_inv]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv0.le]
    norm_num [Real.rpow_neg_one]
  rw [hc, abs_of_pos (by positivity : 0 < 2 * v), real_smul, ofReal_pow]
  push_cast
  field_simp [ofReal_ne_zero.mpr hv0.ne']

/-- DLMF 19.2.21: if the segment with endpoints `x` and `y` lies in `ℂ \ (-∞, 0]`,
`R_C(x, y) = ∫₀¹ (v²x + (1-v²)y)^{-1/2} dv`. Proved from Euler's integral (19.23.10) after
factoring `y^{-1/2}` along the segment and substituting `u = v²`. -/
@[dlmf 19.2.E21]
theorem symmetricEllipticRC_eq_integral_segment {x y : ℂ} (h : segment ℝ x y ⊆ slitPlane) :
    symmetricEllipticRC x y =
      ∫ v in (0 : ℝ)..1, ((v : ℂ) ^ 2 * x + (1 - (v : ℂ) ^ 2) * y) ^ (-(1 / 2 : ℂ)) := by
  have hx : x ∈ slitPlane := h (left_mem_segment ℝ x y)
  have hy : y ∈ slitPlane := h (right_mem_segment ℝ x y)
  have hseg : ∀ u ∈ Icc (0 : ℝ) 1, (1 - u : ℂ) * y + (u : ℂ) * x ∈ slitPlane := by
    intro u hu
    refine h ⟨u, 1 - u, hu.1, by linarith [hu.2], by ring, ?_⟩
    simp only [real_smul]; push_cast; ring
  have hy0 : y ≠ 0 := slitPlane_ne_zero hy
  set w := x / y with hw
  obtain ⟨hw1, harg1⟩ := Carlson.arg_add_arg_segment_mem hseg (u := 1) ⟨zero_le_one, le_rfl⟩
  simp only [ofReal_one, sub_self, one_mul, zero_add] at hw1 harg1
  have hwmem : (![w, 1] : Fin 2 → ℂ) ∈ Carlson.carlsonRSlitDomain :=
    vec2_mem_carlsonRSlitDomain hw1 one_mem_slitPlane
  have hyarg := mem_slitPlane_iff_arg.mp hy
  have hxarg := mem_slitPlane_iff_arg.mp hx
  have harg : ∀ i, arg y + arg ((![w, 1] : Fin 2 → ℂ) i) ∈ Ioo (-π) π := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      refine ⟨harg1.1, lt_of_le_of_ne harg1.2 fun he => hxarg.1 ?_⟩
      rw [show x = y * w by rw [hw]; field_simp, arg_mul hy0 (slitPlane_ne_zero hw1) harg1, he]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        arg_one, add_zero]
      exact ⟨neg_pi_lt_arg y, lt_of_le_of_ne (arg_le_pi y) hyarg.1⟩
  have hR := symmetricEllipticR_mul (1 / 2) ![1 / 2, 1] hwmem hy harg
  have hxy : (fun i => y * (![w, 1] : Fin 2 → ℂ) i) = ![x, y] := by
    funext i; fin_cases i
    · simp [hw]; field_simp
    · simp
  rw [hxy] at hR
  rw [symmetricEllipticRC_eq_symmetricEllipticR hx hy, hR,
    symmetricEllipticR_eq_integral_unitInterval (a' := 1) (by norm_num) (by norm_num)
      (by simp [Fin.sum_univ_two]) hwmem,
    inv_betaIntegral (by norm_num) (by norm_num)]
  rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, Carlson.Gamma_three_halves, Gamma_one, mul_one]
  have hcongr : ∀ v ∈ uIcc (0 : ℝ) 1,
      ((v : ℂ) ^ 2 * x + (1 - (v : ℂ) ^ 2) * y) ^ (-(1 / 2 : ℂ)) =
        y ^ (-(1 / 2 : ℂ)) * (fun u : ℂ => (1 - u + u * w) ^ (-(1 / 2 : ℂ))) ((v : ℂ) ^ 2) := by
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    have hv2 : v ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg v, by nlinarith [hv.1, hv.2]⟩
    have := Carlson.segment_cpow_eq hseg hv2 (-(1 / 2 : ℂ))
    push_cast at this
    simp only
    rw [← hw] at this
    rw [show (v : ℂ) ^ 2 * x + (1 - (v : ℂ) ^ 2) * y = (1 - (v : ℂ) ^ 2) * y + (v : ℂ) ^ 2 * x by
      ring, this]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    integral_sq_subst (fun u : ℂ => (1 - u + u * w) ^ (-(1 / 2 : ℂ))),
    mul_div_assoc, div_self Gamma_one_half_ne_zero, mul_one]
  congr 2
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    sub_self, cpow_zero, mul_one, sub_add_cancel, one_cpow]
  norm_num


/-- **Admitted.** DLMF 19.2.22: if the segment with endpoints `x` and `y` lies in
`ℂ \ (-∞, 0]`, `R_C(x, y) = (2/π) ∫₀^{π/2} R_C(y, x cos²θ + y sin²θ) dθ`. -/
@[dlmf 19.2.E22]
theorem symmetricEllipticRC_eq_integral_RC {x y : ℂ} (h : segment ℝ x y ⊆ slitPlane) :
    symmetricEllipticRC x y = 2 / π * ∫ θ in (0 : ℝ)..(π / 2),
      symmetricEllipticRC y (x * (Real.cos θ : ℂ) ^ 2 + y * (Real.sin θ : ℂ) ^ 2) := by
  sorry

end DLMF.EllipticIntegrals
