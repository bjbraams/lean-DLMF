/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Legendre
public import DLMF.EllipticIntegrals.Expansions
public import DLMF.EllipticIntegrals.LegendreIdentities
public import DLMF.Hypergeometric.Basic.RealPochhammer
public import DLMF.Elementary.Trigonometric
public import Carlson.Elliptic.Standard
public import Carlson.Elliptic.CapacityBound
public import Carlson.Mean.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Inequalities for Legendre's elliptic integrals (DLMF §19.9)

DLMF §19.9 states inequalities for real modulus `0 < k < 1`, `k' = √(1 - k²)`, and, in
§19.9(ii), real amplitude `0 ≤ φ ≤ π/2` with `Δ = √(1 - k² sin²φ) > 0`. The Legendre integrals
are the complex DLMF integrals of `DLMF.EllipticIntegrals` (`incEllIntFk`, `incEllIntEk`,
`incEllIntPik`, `compEllIntEk`, `compEllIntPik`, and `DLMF.EllipticIntegrals.compEllIntKk`,
`cCompEllIntKk`), evaluated at real arguments; there they are real
(`incEllIntFk_eq_ofReal` etc.), and the inequalities are stated for their real parts.

## Main definitions

* `ellipsePerimeter`: the perimeter `L(a, b)` of an ellipse (DLMF §19.9(i)).

## Main results

* `log_four_le_compEllIntKk_add_log`, `one_le_compEllIntEk_le`, `one_le_compEllIntPik_le`:
  the three lines of DLMF 19.9.1.
* `tendsto_compEllIntKk_sub_log`: the sharp limit `K(k) - ln(4/k') → 0` as `k → 1-`, which
  gives the lower bound in the first line of DLMF 19.9.1.
* `compEllIntKk_div_log_bounds`, `eight_add_sq_mul_compEllIntKk_div_log_bounds`: bounds for
  `K(k)/ln(4/k')` (DLMF 19.9.2, 19.9.3).
* `compEllIntEk_bounds`, `pi_mul_cCompEllIntKk_div_bounds`: DLMF 19.9.4, 19.9.5.
* `compEllIntKk_sub_compEllIntEk_bounds`, `compEllIntEk_sub_mul_compEllIntKk_bounds`,
  `compEllIntEk_div_compEllIntKk_bounds`: DLMF 19.9.6–19.9.8.
* `ellipsePerimeter_eq`: `L(a, b) = 4a E(k)` (DLMF 19.9.9).
* `pi_mul_ramanujan_le_ellipsePerimeter`: Ramanujan's approximation to `L(a, b)` is from below
  (DLMF §19.9(i)).
* `incEllIntFk_bounds`, `incEllIntEk_bounds`, `incEllIntPik_bounds`: DLMF 19.9.11–19.9.13.
* `incEllIntFk_div_sin_bounds`, `incEllIntFk_div_sin_mul_log_bounds`,
  `incEllIntFk_eq_log_sub_bounds`: DLMF 19.9.14–19.9.16.
* `incEllIntFk_arctanh_bounds`: Carlson's bounds by inverse hyperbolic tangents
  (DLMF 19.9.17, 19.9.18).

## Implementation notes

The strict bounds (19.9.14) use the normalized first-kind integral from
`Carlson.Elliptic.Standard`, the strict capacity lower bound from
`Carlson.Elliptic.CapacityBound`, and the geometric upper bound from `Carlson.Mean.Bounds`
(all in lean-codes).

Domain qualifications (Lean totalization; DLMF's own statements are kept otherwise):

* (19.9.1), third line, and (19.9.13): the characteristic `α²` is real with `α² < 1`, as DLMF
  states for (19.9.1); for (19.9.13) DLMF leaves the range of `α²` implicit, and `α² < 1` is the
  range where the defining integral is an ordinary positive integral.
* (19.9.11): the bound by `gd⁻¹(φ)` is stated for `φ < π/2` (at `φ = π/2`, `gd⁻¹ = ∞`, and the
  minimum is `φ/Δ`). Likewise in (19.9.13) the bound by `Π(φ, α², 1)` needs `φ < π/2`.
* (19.9.14)–(19.9.16) need `sin φ > 0`; (19.9.14) and (19.9.17) also need `cos φ > 0`
  (otherwise a side is infinite), so they are stated for `0 < φ < π/2`; (19.9.15), (19.9.16)
  for `0 < φ ≤ π/2`.
* The perimeter `L(a, b)` of (19.9.9) is the arc length of `t ↦ (a cos t, b sin t)`.

The approximations of §19.9(i) ((19.9.10) and the cited accuracy figures) are numerical and
excluded, except the analytical statement that Ramanujan's approximation is from below
(Barnard et al. 2000).

## References

* NIST DLMF §19.9.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology NNReal

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic
open DLMF.Hypergeometric (poch_ofReal hasSum_poch_div_factorial)

/-! ### Real-variable helpers -/

/-- `x^{-1/2} = (√x)⁻¹` for `x ≥ 0`. -/
theorem rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 / 2) : ℝ) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

/-- `x^{1/2} = √x`. -/
theorem rpow_half_eq_sqrt (x : ℝ) : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm

/-- On `[0, π/2]` the sine is monotone: `sin² θ ≤ sin² φ` for `0 ≤ θ ≤ φ ≤ π/2`. -/
private lemma sin_sq_le_sin_sq {θ φ : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≤ φ) (hφ : φ ≤ π / 2) :
    Real.sin θ ^ 2 ≤ Real.sin φ ^ 2 := by
  have hs : Real.sin θ ≤ Real.sin φ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hφ hθ
  have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  exact pow_le_pow_left₀ h1 hs 2

/-- `1 - m sin²θ ≥ cos²θ` for `m ≤ 1`. -/
private lemma cos_sq_le_one_sub_mul_sin_sq {m : ℝ} (hm : m ≤ 1) (θ : ℝ) :
    Real.cos θ ^ 2 ≤ 1 - m * Real.sin θ ^ 2 := by
  have := Real.sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (Real.sin θ)]

/-- `1 - m sin²θ ≥ 1 - m sin²φ` for `0 ≤ m` and `0 ≤ θ ≤ φ ≤ π/2`. -/
private lemma one_sub_mul_sin_sq_le_of_le {m θ φ : ℝ} (hm : 0 ≤ m) (h0 : 0 ≤ θ) (hθ : θ ≤ φ)
    (hφ : φ ≤ π / 2) :
    1 - m * Real.sin φ ^ 2 ≤ 1 - m * Real.sin θ ^ 2 := by
  nlinarith [sin_sq_le_sin_sq h0 hθ hφ]

/-- `1 - m sin²θ ≤ 1` for `m ≥ 0`. -/
private lemma one_sub_mul_sin_sq_le_one {m : ℝ} (hm : 0 ≤ m) (θ : ℝ) : 1 - m *
    Real.sin θ ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg (Real.sin θ)]

/-- The third-kind factor `(1 - n sin²θ)⁻¹` is positive for `n < 1`. -/
private lemma inv_one_sub_mul_sin_sq_pos {n : ℝ} (hn : n < 1) (θ : ℝ) : 0 <
    (1 - n * Real.sin θ ^ 2)⁻¹ :=
  inv_pos.mpr (DLMF.Elliptic.one_sub_mul_sin_sq_pos hn θ)

/-! ### Real forms of the integrals -/

/-- `Re F(φ, k) = F(φ | k²)` for real `φ` and `k² ≤ 1`. -/
private lemma re_incEllIntFk_ofReal {φ k : ℝ} (hk : k ^ 2 ≤ 1) :
    (incEllIntFk φ k).re = DLMF.Elliptic.Real.incEllIntFm φ (k ^ 2) := by
  rw [incEllIntFk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk φ, ofReal_re]

/-- `Re E(φ, k) = E(φ | k²)` for real `φ` and `k² ≤ 1`. -/
private lemma re_incEllIntEk_ofReal {φ k : ℝ} (hk : k ^ 2 ≤ 1) :
    (incEllIntEk φ k).re = DLMF.Elliptic.Real.incEllIntEm φ (k ^ 2) := by
  rw [incEllIntEk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk φ, ofReal_re]

/-- `Re Π(φ, α², k) = Π(φ, α² | k²)` for real `φ`, `α² < 1` and `k² ≤ 1`. -/
private lemma re_incEllIntPik_ofReal {φ α2 k : ℝ} (hα : α2 < 1) (hk : k ^ 2 ≤ 1) :
    (incEllIntPik φ α2 k).re = DLMF.Elliptic.Real.incEllIntPim φ α2 (k ^ 2) := by
  rw [incEllIntPik_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk hα φ, ofReal_re]

/-- `E(k) = E(π/2, k)` with a real amplitude cast. -/
private lemma compEllIntEk_eq_incEllIntEk (k : ℂ) : compEllIntEk k =
    incEllIntEk ((π / 2 : ℝ) : ℂ) k := by
  rw [compEllIntEk]; push_cast; rfl

/-- `Π(α², k) = Π(π/2, α², k)` with a real amplitude cast. -/
private lemma compEllIntPik_eq_incEllIntPik (α2 k : ℂ) :
    compEllIntPik α2 k = incEllIntPik ((π / 2 : ℝ) : ℂ) α2 k := by
  rw [compEllIntPik]; push_cast; rfl

/-! ### §19.9(i) Complete integrals -/

/-! ### The sharp limit of `K(k) - ln(4/k')` -/

/-- `sin² φ + a cos² φ > 0` for `a > 0`. -/
private lemma sin_sq_add_mul_cos_sq_pos {a : ℝ} (ha : 0 < a) (φ : ℝ) :
    0 < Real.sin φ ^ 2 + a * Real.cos φ ^ 2 := by
  rcases eq_or_ne (Real.cos φ) 0 with h | h
  · have := Real.sin_sq_add_cos_sq φ
    rw [h] at this ⊢; nlinarith
  · have := pow_pos (abs_pos.mpr h) 2
    rw [sq_abs] at this
    positivity

/-- `(1 - cos φ)/sin φ = tan(φ/2)` written with half angles. -/
private lemma one_sub_cos_mul_inv_sin (φ : ℝ) :
    (1 - Real.cos φ) * (Real.sin φ)⁻¹ = Real.sin (φ / 2) / Real.cos (φ / 2) := by
  have h1 : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    rw [show φ = 2 * (φ / 2) by ring, Real.cos_two_mul, ← Real.sin_sq_add_cos_sq (φ / 2)]
    ring_nf
  have h2 : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    rw [show φ = 2 * (φ / 2) by ring, Real.sin_two_mul]; ring_nf
  rw [h1, h2]
  rcases eq_or_ne (Real.sin (φ / 2)) 0 with hs | hs
  · simp [hs]
  rcases eq_or_ne (Real.cos (φ / 2)) 0 with hc | hc
  · simp [hc]
  field_simp
  ring

/-- `∫₀^{π/2} (1 - cos φ)/sin φ dφ = ln 2`. -/
private lemma integral_one_sub_cos_div_sin :
    ∫ φ in (0 : ℝ)..(π / 2), (1 - Real.cos φ) * (Real.sin φ)⁻¹ = Real.log 2 := by
  simp_rw [one_sub_cos_mul_inv_sin]
  have hd : ∀ φ ∈ uIcc (0 : ℝ) (π / 2),
      HasDerivAt (fun u => -2 * Real.log (Real.cos (u / 2)))
        (Real.sin (φ / 2) / Real.cos (φ / 2)) φ := by
    intro φ hφ
    rw [uIcc_of_le (by positivity)] at hφ
    have hc : 0 < Real.cos (φ / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], by linarith [hφ.2, Real.pi_pos]⟩
    have h0 : HasDerivAt (fun u : ℝ => Real.cos (u / 2)) (-Real.sin (φ / 2) * (1 / 2)) φ := by
      have := (Real.hasDerivAt_cos (φ / 2)).comp φ ((hasDerivAt_id φ).div_const 2)
      simpa [Function.comp_def] using this
    have h := h0.log hc.ne'
    convert h.const_mul (-2) using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · rw [show π / 2 / 2 = π / 4 by ring, Real.cos_pi_div_four, zero_div, Real.cos_zero,
      Real.log_one, Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]
    ring
  · refine ContinuousOn.intervalIntegrable fun φ hφ => ?_
    rw [uIcc_of_le (by positivity)] at hφ
    have hc : 0 < Real.cos (φ / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], by linarith [hφ.2, Real.pi_pos]⟩
    exact ((Real.continuous_sin.comp (continuous_id.div_const 2)).continuousAt.div
      (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousAt hc.ne').continuousWithinAt


/-- As `a → 0+`, `∫₀^{π/2} (1 - cos φ)(sin² φ + a cos² φ)^{-1/2} dφ → ln 2`. -/
private lemma tendsto_integral_one_sub_cos_mul_rpow :
    Tendsto (fun a : ℝ => ∫ φ in (0 : ℝ)..(π / 2),
      (1 - Real.cos φ) * (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ))
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
  rw [← integral_one_sub_cos_div_sin]
  have hIoc : ∀ φ ∈ uIoc (0 : ℝ) (π / 2), 0 < Real.sin φ ∧ 0 ≤ Real.cos φ := by
    intro φ hφ
    rw [uIoc_of_le (by positivity)] at hφ
    exact ⟨Real.sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, Real.pi_pos]),
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩⟩
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    refine Continuous.aestronglyMeasurable ?_
    exact (continuous_const.sub Real.continuous_cos).mul
      ((by fun_prop : Continuous fun φ => Real.sin φ ^ 2 + a * Real.cos φ ^ 2).rpow_const
        fun φ => Or.inl (sin_sq_add_mul_cos_sq_pos ha φ).ne')
  · filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    refine Eventually.of_forall fun φ hφ => ?_
    obtain ⟨hs, hc⟩ := hIoc φ hφ
    have hpos := sin_sq_add_mul_cos_sq_pos ha φ
    have h1 : 0 ≤ 1 - Real.cos φ := by linarith [Real.cos_le_one φ]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 (Real.rpow_nonneg hpos.le _))]
    have hle : (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ) ≤ (Real.sin φ)⁻¹ := by
      rw [rpow_neg_half_eq_inv_sqrt hpos.le]
      apply inv_anti₀ hs
      have h2 := Real.sqrt_le_sqrt (show Real.sin φ ^ 2 ≤ Real.sin φ ^ 2 + a * Real.cos φ ^ 2 by
        nlinarith)
      rwa [Real.sqrt_sq hs.le] at h2
    have hsc : 1 - Real.cos φ ≤ Real.sin φ := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    calc (1 - Real.cos φ) * (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ)
        ≤ (1 - Real.cos φ) * (Real.sin φ)⁻¹ := mul_le_mul_of_nonneg_left hle h1
      _ ≤ Real.sin φ * (Real.sin φ)⁻¹ := mul_le_mul_of_nonneg_right hsc (inv_nonneg.mpr hs.le)
      _ = 1 := mul_inv_cancel₀ hs.ne'
  · refine Eventually.of_forall fun φ hφ => ?_
    obtain ⟨hs, hc⟩ := hIoc φ hφ
    have hs2 : 0 < Real.sin φ ^ 2 := by positivity
    have hcont : ContinuousAt (fun a : ℝ => (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ))
        0 := by
      refine ContinuousAt.rpow_const (by fun_prop) (Or.inl ?_)
      simp only [zero_mul, add_zero]; exact hs2.ne'
    have h := (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).const_mul
      (1 - Real.cos φ)
    simp only [zero_mul, add_zero] at h
    rwa [rpow_neg_half_eq_inv_sqrt hs2.le, Real.sqrt_sq hs.le] at h

/-- `∫₀^{π/2} cos φ (sin² φ + a cos² φ)^{-1/2} dφ = ln((1 + √(1 - a))/√a)/√(1 - a)` for
`0 < a < 1`. -/
private lemma integral_cos_mul_rpow {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∫ φ in (0 : ℝ)..(π / 2), Real.cos φ * (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ) =
      Real.log ((1 + Real.sqrt (1 - a)) / Real.sqrt a) / Real.sqrt (1 - a) := by
  set b := Real.sqrt (1 - a) with hb
  set c := Real.sqrt a with hc
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hc0 : 0 < c := Real.sqrt_pos.mpr ha
  have hb2 : b ^ 2 = 1 - a := Real.sq_sqrt (by linarith)
  have hc2 : c ^ 2 = a := Real.sq_sqrt ha.le
  have hd : ∀ φ ∈ uIcc (0 : ℝ) (π / 2),
      HasDerivAt (fun u => Real.arsinh (b / c * Real.sin u) / b)
        (Real.cos φ * (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ)) φ := by
    intro φ _
    have h := (((Real.hasDerivAt_sin φ).const_mul (b / c)).arsinh).div_const b
    convert h using 1
    have hpos := sin_sq_add_mul_cos_sq_pos ha φ
    rw [rpow_neg_half_eq_inv_sqrt hpos.le]
    have he : 1 + (b / c * Real.sin φ) ^ 2 = (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) / c ^ 2 := by
      rw [mul_pow, div_pow, hb2, hc2]; field_simp; nlinarith [Real.sin_sq_add_cos_sq φ]
    rw [he, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hc0.le]
    have hs := Real.sqrt_pos.mpr hpos
    rw [smul_eq_mul]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · rw [Real.sin_pi_div_two, Real.sin_zero, mul_one, mul_zero, Real.arsinh_zero, zero_div, sub_zero,
      Real.arsinh]
    congr 1
    congr 1
    have he : 1 + (b / c) ^ 2 = (1 / c) ^ 2 := by
      rw [div_pow, div_pow, hb2, hc2]; field_simp; ring
    rw [he, Real.sqrt_sq (by positivity)]
    field_simp
    ring
  · refine (Continuous.intervalIntegrable ?_ _ _)
    exact Real.continuous_cos.mul
      ((by fun_prop : Continuous fun φ => Real.sin φ ^ 2 + a * Real.cos φ ^ 2).rpow_const
        fun φ => Or.inl (sin_sq_add_mul_cos_sq_pos ha φ).ne')


/-- `K(m) = ∫₀^{π/2} (sin² φ + (1 - m) cos² φ)^{-1/2} dφ`. -/
private lemma compEllIntKm_eq_integral_sin_sq_add (m : ℝ) :
    DLMF.Elliptic.Real.compEllIntKm m = ∫ φ in (0 : ℝ)..(π / 2),
      (Real.sin φ ^ 2 + (1 - m) * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ) := by
  rw [DLMF.Elliptic.Real.compEllIntKm]
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ)) (π / 2) (a := 0) (b := π / 2)
  simp only [sub_self, sub_zero, Real.sin_pi_div_two_sub] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  congr 1
  nlinarith [Real.sin_sq_add_cos_sq φ]

/-- The sharp limit `K(m) + ½ ln(1 - m) → ln 4` as `m → 1-`, i.e. `K(k) - ln(4/k') → 0` as
`k → 1-`. -/
theorem tendsto_compEllIntKm_add_log :
    Tendsto (fun m : ℝ => DLMF.Elliptic.Real.compEllIntKm m + 1 / 2 * Real.log (1 - m))
      (𝓝[<] 1) (𝓝 (Real.log 4)) := by
  -- the explicit part `P(a) + ½ ln a`
  set h : ℝ → ℝ := fun a => Real.log (1 + Real.sqrt (1 - a)) / Real.sqrt (1 - a) -
    a * Real.log a / (2 * Real.sqrt (1 - a) * (1 + Real.sqrt (1 - a))) with hh
  have hcont : ContinuousAt h 0 := by
    have hs : ContinuousAt (fun a : ℝ => Real.sqrt (1 - a)) 0 := by fun_prop
    have hs0 : Real.sqrt (1 - 0) = 1 := by simp
    refine ContinuousAt.sub ?_ ?_
    · refine ContinuousAt.div ?_ hs (by norm_num)
      exact (continuousAt_const.add hs).log (by norm_num)
    · refine ContinuousAt.div Real.continuous_mul_log.continuousAt ?_ (by norm_num)
      exact (continuousAt_const.mul hs).mul (continuousAt_const.add hs)
  have h0 : h 0 = Real.log 2 := by simp [hh]; norm_num
  have hP : Tendsto h (𝓝[>] 0) (𝓝 (Real.log 2)) := h0 ▸ hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hG : Tendsto (fun a : ℝ => (∫ φ in (0 : ℝ)..(π / 2),
      (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ)) + 1 / 2 * Real.log a)
      (𝓝[>] 0) (𝓝 (Real.log 4)) := by
    rw [show Real.log 4 = Real.log 2 + Real.log 2 by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num]
    refine (hP.add tendsto_integral_one_sub_cos_mul_rpow).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with a ha
    have hcI : Continuous fun φ : ℝ => (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ) :=
      (by fun_prop : Continuous fun φ => Real.sin φ ^ 2 + a * Real.cos φ ^ 2).rpow_const
        fun φ => Or.inl (sin_sq_add_mul_cos_sq_pos ha.1 φ).ne'
    have hsplit : (∫ φ in (0 : ℝ)..(π / 2),
        (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ)) =
        (∫ φ in (0 : ℝ)..(π / 2), Real.cos φ *
          (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ)) +
        ∫ φ in (0 : ℝ)..(π / 2), (1 - Real.cos φ) *
          (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ) := by
      rw [← intervalIntegral.integral_add
        (f := fun φ => Real.cos φ * (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ))
        (g := fun φ => (1 - Real.cos φ) * (Real.sin φ ^ 2 + a * Real.cos φ ^ 2) ^ (-(1 / 2) : ℝ))
        ((Real.continuous_cos.mul hcI).intervalIntegrable _ _)
        (((continuous_const.sub Real.continuous_cos).mul hcI).intervalIntegrable _ _)]
      congr 1; funext φ; ring
    rw [hsplit, integral_cos_mul_rpow ha.1 ha.2]
    simp only [hh]
    set b := Real.sqrt (1 - a) with hb
    have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith [ha.2])
    have hb2 : b ^ 2 = 1 - a := Real.sq_sqrt (by linarith [ha.2])
    have hc : Real.log (Real.sqrt a) = 1 / 2 * Real.log a := by
      rw [Real.log_sqrt ha.1.le]; ring
    rw [Real.log_div (by positivity) (Real.sqrt_pos.mpr ha.1).ne', hc]
    have key : (Real.log (1 + b) - 1 / 2 * Real.log a) / b + 1 / 2 * Real.log a =
        Real.log (1 + b) / b - a * Real.log a / (2 * b * (1 + b)) := by
      field_simp
      linear_combination (Real.log a) * hb2
    linear_combination -key
  have hm : Tendsto (fun m : ℝ => 1 - m) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 := (continuous_sub_left (1 : ℝ)).tendsto 1
      simpa using h1.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    · filter_upwards [self_mem_nhdsWithin] with m (hm : m < 1) using sub_pos.mpr hm
  refine (hG.comp hm).congr' (Eventually.of_forall fun m => ?_)
  simp only [Function.comp_def, compEllIntKm_eq_integral_sin_sq_add]


/-- `E(m) - (1 - m) K(m) ≤ m` for `0 ≤ m < 1`. -/
private lemma compEllIntEm_sub_mul_compEllIntKm_le {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    DLMF.Elliptic.Real.compEllIntEm m - (1 - m) * DLMF.Elliptic.Real.compEllIntKm m ≤ m := by
  have hpos : ∀ θ, 0 < 1 - m * Real.sin θ ^ 2 := fun θ => by
    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ)]
  have hc : ∀ p : ℝ, Continuous fun θ : ℝ => (1 - m * Real.sin θ ^ 2) ^ p := fun p =>
    (by fun_prop : Continuous fun θ : ℝ => 1 - m * Real.sin θ ^ 2).rpow_const
      fun θ => Or.inl (hpos θ).ne'
  rw [DLMF.Elliptic.Real.compEllIntEm, DLMF.Elliptic.Real.compEllIntKm,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (f := fun θ => (1 - m * Real.sin θ ^ 2) ^ (1 / 2 : ℝ))
      (g := fun θ => (1 - m) * (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ))
      ((hc _).intervalIntegrable _ _) ((continuous_const.mul (hc _)).intervalIntegrable _ _)]
  calc _ ≤ ∫ θ in (0 : ℝ)..(π / 2), m * Real.cos θ := by
        refine intervalIntegral.integral_mono_on (by positivity)
          (((hc _).sub (continuous_const.mul (hc _))).intervalIntegrable _ _)
          ((continuous_const.mul Real.continuous_cos).intervalIntegrable _ _) fun θ hθ => ?_
        have hcos : 0 ≤ Real.cos θ :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
        set u := (1 - m * Real.sin θ ^ 2) ^ (1 / 2 : ℝ) with hu
        have hu0 : 0 < u := Real.rpow_pos_of_pos (hpos θ) _
        have hu2 : u ^ 2 = 1 - m * Real.sin θ ^ 2 := by
          rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (hpos θ).le]; norm_num
        have hinv : (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ) = u⁻¹ := by
          rw [hu, Real.rpow_neg (hpos θ).le]
        rw [hinv]
        have hcu : Real.cos θ ≤ u := by
          have h2 : Real.cos θ ^ 2 ≤ u ^ 2 := by
            rw [hu2]; nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
          nlinarith
        have key : u - (1 - m) * u⁻¹ = m * Real.cos θ ^ 2 / u := by
          field_simp
          nlinarith [Real.sin_sq_add_cos_sq θ]
        rw [key, div_le_iff₀ hu0]
        nlinarith [mul_le_mul_of_nonneg_left hcu (mul_nonneg hm0 hcos)]
    _ = m := by
        rw [intervalIntegral.integral_const_mul, integral_cos, Real.sin_pi_div_two, Real.sin_zero]
        ring


/-- `ln 4 ≤ K(m) + ½ ln(1 - m) ≤ π/2` for `0 ≤ m < 1` (DLMF 19.9.1 in the parameter `m`):
the middle term decreases from `π/2` at `m = 0` to its limit `ln 4` at `m = 1`. -/
private lemma compEllIntKm_add_log_bounds {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    Real.log 4 ≤ DLMF.Elliptic.Real.compEllIntKm m + 1 / 2 * Real.log (1 - m) ∧
      DLMF.Elliptic.Real.compEllIntKm m + 1 / 2 * Real.log (1 - m) ≤ π / 2 := by
  set f : ℝ → ℝ := fun m => DLMF.Elliptic.Real.compEllIntKm m + 1 / 2 * Real.log (1 - m)
    with hf
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f
      ((DLMF.Elliptic.Real.compEllIntEm x - (1 - x) * DLMF.Elliptic.Real.compEllIntKm x) /
        (2 * x * (1 - x)) + 1 / 2 * (-1 / (1 - x))) x := by
    intro x hx
    have h1 : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have hl := ((hasDerivAt_id x).const_sub 1).log h1
    simp only [id] at hl
    exact (DLMF.Elliptic.Real.hasDerivAt_compEllIntKm hx.2 hx.1.ne').add (hl.const_mul (1 / 2))
  have hanti : AntitoneOn f (Ico 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ico 0 1) (fun x hx => ?_) ?_ ?_
    · have h1 : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
      exact ((DLMF.Elliptic.Real.continuousAt_compEllIntKm hx.2).add
        (((continuousAt_const.sub continuousAt_id).log h1).const_mul _)).continuousWithinAt
    · rw [interior_Ico]
      exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ico]
      intro x hx
      rw [(hderiv x hx).deriv]
      have h1 : 0 < 1 - x := by linarith [hx.2]
      have h2 : 0 < 2 * x * (1 - x) := by have := hx.1; positivity
      have hle := compEllIntEm_sub_mul_compEllIntKm_le hx.1.le hx.2
      rw [div_add' _ _ _ h2.ne', div_nonpos_iff]
      right
      refine ⟨?_, h2.le⟩
      have : 1 / 2 * (-1 / (1 - x)) * (2 * x * (1 - x)) = -x := by field_simp
      linarith
  have hmem : m ∈ Ico (0 : ℝ) 1 := ⟨hm0, hm1⟩
  refine ⟨?_, ?_⟩
  · refine le_of_tendsto tendsto_compEllIntKm_add_log ?_
    filter_upwards [Ioo_mem_nhdsLT hm1] with x hx
    exact hanti hmem ⟨hm0.trans hx.1.le, hx.2⟩ hx.1.le
  · have h := hanti ⟨le_rfl, one_pos⟩ hmem hm0
    simp only [hf, DLMF.Elliptic.Real.compEllIntKm_zero, sub_zero, Real.log_one, mul_zero,
      add_zero] at h
    exact h

/-- The sharp limit `K(k) - ln(4/k') → 0` as `k → 1-` (real `k`, `k' = √(1 - k²)`). -/
theorem tendsto_compEllIntKk_sub_log :
    Tendsto (fun k : ℝ => (compEllIntKk k).re - Real.log (4 / Real.sqrt (1 - k ^ 2)))
      (𝓝[<] 1) (𝓝 0) := by
  have hsq : Tendsto (fun k : ℝ => k ^ 2) (𝓝[<] 1) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((continuous_pow 2).tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Iio 1))
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
      exact (sq_lt_one_iff₀ hk.1.le).mpr hk.2
  have h := (tendsto_compEllIntKm_add_log.comp hsq).sub_const (Real.log 4)
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
  have hk2 : k ^ 2 < 1 := (sq_lt_one_iff₀ hk.1.le).mpr hk.2
  have h1 : 0 < 1 - k ^ 2 := by linarith
  rw [Function.comp_apply, compEllIntKk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk2.le,
    ofReal_re, Real.log_div (by norm_num) (Real.sqrt_pos.mpr h1).ne', Real.log_sqrt h1.le]
  ring

/-! ### Bounds -/

/-- DLMF 19.9.1, first line: `ln 4 ≤ K(k) + ln k' ≤ π/2` for `0 < k < 1`. -/
@[dlmf 19.9.E1]
theorem log_four_le_compEllIntKk_add_log {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    Real.log 4 ≤ (compEllIntKk k).re + Real.log (Real.sqrt (1 - k ^ 2)) ∧
      (compEllIntKk k).re + Real.log (Real.sqrt (1 - k ^ 2)) ≤ π / 2 := by
  have hk2 : k ^ 2 < 1 := (sq_lt_one_iff₀ hk0.le).mpr hk1
  rw [compEllIntKk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk2.le, ofReal_re,
    Real.log_sqrt (by linarith)]
  have h := compEllIntKm_add_log_bounds (sq_nonneg k) hk2
  constructor <;> linarith [h.1, h.2]

/-- DLMF 19.9.2: `1 + k'²/8 < K(k)/ln(4/k') < 1 + k'²/4` for `0 < k < 1`. -/
@[dlmf 19.9.E2]
theorem compEllIntKk_div_log_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    1 + (1 - k ^ 2) / 8 < (compEllIntKk k).re / Real.log (4 / Real.sqrt (1 - k ^ 2)) ∧
      (compEllIntKk k).re / Real.log (4 / Real.sqrt (1 - k ^ 2)) < 1 + (1 - k ^ 2) / 4 := by
  sorry

/-- DLMF 19.9.3: `9 + k²k'²/8 < (8 + k²) K(k)/ln(4/k') < 9.096` for `0 < k < 1`. -/
@[dlmf 19.9.E3]
theorem eight_add_sq_mul_compEllIntKk_div_log_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    9 + k ^ 2 * (1 - k ^ 2) / 8 <
        (8 + k ^ 2) * (compEllIntKk k).re / Real.log (4 / Real.sqrt (1 - k ^ 2)) ∧
      (8 + k ^ 2) * (compEllIntKk k).re / Real.log (4 / Real.sqrt (1 - k ^ 2)) < 9.096 := by
  sorry

/-- DLMF 19.9.4: `((1 + k'^{3/2})/2)^{2/3} ≤ (2/π) E(k) ≤ ((1 + k'²)/2)^{1/2}` for
`0 ≤ k ≤ 1`. -/
@[dlmf 19.9.E4]
theorem compEllIntEk_bounds {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    ((1 + Real.sqrt (1 - k ^ 2) ^ (3 / 2 : ℝ)) / 2) ^ (2 / 3 : ℝ) ≤ 2 / π * (compEllIntEk k).re ∧
      2 / π * (compEllIntEk k).re ≤ Real.sqrt ((1 + (1 - k ^ 2)) / 2) := by
  sorry

/-- DLMF 19.9.5: `ln((1 + √k')²/k) < π K'(k)/(2K(k)) < ln(2(1 + k')/k)` for `0 < k < 1`, with
DLMF's complementary integral `K'(k)` (`cCompEllIntKk`, equal to `K(k')` here). -/
@[dlmf 19.9.E5]
theorem pi_mul_cCompEllIntKk_div_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    Real.log ((1 + Real.sqrt (Real.sqrt (1 - k ^ 2))) ^ 2 / k) <
        π * (cCompEllIntKk k).re / (2 * (compEllIntKk k).re) ∧
      π * (cCompEllIntKk k).re / (2 * (compEllIntKk k).re) <
        Real.log (2 * (1 + Real.sqrt (1 - k ^ 2)) / k) := by
  sorry

/-- The real binomial series `∑ (β)ₘ/m! xᵐ = (1 - x)^{-β}` for `0 ≤ x < 1`. -/
private lemma hasSum_ascPochhammer_binomial (β : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun m : ℕ => (ascPochhammer ℝ m).eval β / Nat.factorial m * x ^ m)
      ((1 - x) ^ (-β)) := by
  have hz : ‖(x : ℂ)‖ < 1 := by rwa [norm_real, Real.norm_of_nonneg hx0]
  have h := Complex.hasSum_re (hasSum_poch_div_factorial (β := (β : ℂ)) hz)
  rw [← ofReal_one, ← ofReal_sub, ← ofReal_neg, ← ofReal_cpow (by linarith), ofReal_re] at h
  refine h.congr_fun fun m => ?_
  rw [poch_ofReal, ← ofReal_natCast, ← ofReal_div, ← ofReal_pow, ← ofReal_mul, ofReal_re]

/-- Coefficientwise comparison of two power series with nonnegative ratios. -/
private lemma le_of_ratio_le {u v r s : ℕ → ℝ} (hu : ∀ m, u (m + 1) = u m * r m)
    (hv : ∀ m, v (m + 1) = v m * s m) (h0 : u 0 = v 0) (hu0 : 0 < u 0)
    (hr : ∀ m, 0 ≤ r m) (hrs : ∀ m, r m ≤ s m) (hr0 : 0 < r 0) (hr1 : r 1 < s 1) :
    (∀ m, u m ≤ v m) ∧ u 2 < v 2 := by
  have key : ∀ m, 0 ≤ u m ∧ u m ≤ v m := by
    intro m
    induction m with
    | zero => exact ⟨hu0.le, h0.le⟩
    | succ m ih =>
      rw [hu, hv]
      have hs : 0 ≤ s m := (hr m).trans (hrs m)
      exact ⟨mul_nonneg ih.1 (hr m), (mul_le_mul_of_nonneg_left (hrs m) ih.1).trans
        (mul_le_mul_of_nonneg_right ih.2 hs)⟩
  refine ⟨fun m => (key m).2, ?_⟩
  have hu1 : 0 < u 1 := by rw [hu]; exact mul_pos hu0 hr0
  rw [hu, hv]
  exact (mul_lt_mul_of_pos_left hr1 hu1).trans_le
    (mul_le_mul_of_nonneg_right (key 1).2 ((hr 1).trans (hrs 1)))

/-- Comparison of sums of power series with coefficientwise comparable coefficients. -/
private lemma hasSum_lt_of_coeff {u v : ℕ → ℝ} {x A B : ℝ} (hx : 0 < x)
    (hA : HasSum (fun m => u m * x ^ m) A) (hB : HasSum (fun m => v m * x ^ m) B)
    (h : ∀ m, u m ≤ v m) (h2 : u 2 < v 2) : A < B :=
  hasSum_lt (f := fun m => u m * x ^ m) (g := fun m => v m * x ^ m) (i := 2)
    (fun m => mul_le_mul_of_nonneg_right (h m) (by positivity))
    (mul_lt_mul_of_pos_right h2 (by positivity)) hA hB

/-- `(3/2)ₘ = 2 (m + 1/2) (1/2)ₘ`. -/
private lemma ascPochhammer_three_halves (m : ℕ) :
    (ascPochhammer ℝ m).eval (3 / 2 : ℝ) = 2 * (1 / 2 + m) * (ascPochhammer ℝ m).eval (1 / 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih]
    push_cast; ring

/-- The ratio of consecutive coefficients of the binomial series of `(1 - cx)^{-β}`. -/
private lemma binomial_coeff_succ (β c : ℝ) (m : ℕ) :
    (ascPochhammer ℝ (m + 1)).eval β / (Nat.factorial (m + 1) : ℕ) * c ^ (m + 1) =
      (ascPochhammer ℝ m).eval β / (Nat.factorial m : ℕ) * c ^ m * ((β + m) / (m + 1) * c) := by
  rw [ascPochhammer_succ_eval, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The coefficients `(a)ₘ (1/2)ₘ/((m+1)! m!)` and their ratio. -/
private lemma hg2_coeff_succ (a : ℝ) (m : ℕ) :
    (ascPochhammer ℝ (m + 1)).eval a * (ascPochhammer ℝ (m + 1)).eval (1 / 2) /
        ((Nat.factorial (m + 1 + 1) : ℕ) * (Nat.factorial (m + 1) : ℕ)) =
      (ascPochhammer ℝ m).eval a * (ascPochhammer ℝ m).eval (1 / 2) /
        ((Nat.factorial (m + 1) : ℕ) * (Nat.factorial m : ℕ)) *
        ((a + m) * (1 / 2 + m) / ((m + 2) * (m + 1))) := by
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ (m + 1),
    Nat.factorial_succ m]
  push_cast
  field_simp
  ring

/-- `(4/π) D(k) = ∑ₘ (3/2)ₘ (1/2)ₘ/((m+1)! m!) k^{2m}` for real `0 < k < 1`. -/
private lemma hasSum_compEllIntDk_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    HasSum (fun m : ℕ => (ascPochhammer ℝ m).eval (3 / 2 : ℝ) *
        (ascPochhammer ℝ m).eval (1 / 2 : ℝ) /
        ((Nat.factorial (m + 1) : ℕ) * (Nat.factorial m : ℕ)) * (k ^ 2) ^ m)
      (4 / (π * k ^ 2) * ((compEllIntKk k).re - (compEllIntEk k).re)) := by
  have hk : ‖(k : ℂ)‖ < 1 := by rwa [norm_real, Real.norm_of_nonneg hk0.le]
  have h := (Complex.hasSum_re (compEllIntDk_hasSum hk).1).mul_left (4 / π)
  have hk2 : 1 - (k : ℂ) ^ 2 ∈ slitPlane := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_sub]
    exact ofReal_mem_slitPlane.mpr (by nlinarith)
  rw [compEllIntDk_eq (ofReal_ne_zero.mpr hk0.ne') hk2, ← ofReal_pow, div_ofReal_re,
    sub_re] at h
  convert h using 1
  · funext m
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, poch_ofReal, poch_ofReal,
      pow_mul, ← ofReal_pow, ← ofReal_pow]
    simp only [← ofReal_natCast, ← ofReal_mul, ← ofReal_div, ← ofReal_ofNat]
    rw [ofReal_re]
    have := Real.pi_pos
    field_simp
  · have := Real.pi_pos
    field_simp

/-- `(4/(πk²))(E(k) - k'² K(k)) = ∑ₘ (1/2)ₘ (1/2)ₘ/((m+1)! m!) k^{2m}` for real `0 < k < 1`. -/
private lemma hasSum_compEllIntEk_sub_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    HasSum (fun m : ℕ => (ascPochhammer ℝ m).eval (1 / 2 : ℝ) *
        (ascPochhammer ℝ m).eval (1 / 2 : ℝ) /
        ((Nat.factorial (m + 1) : ℕ) * (Nat.factorial m : ℕ)) * (k ^ 2) ^ m)
      (4 / (π * k ^ 2) * ((compEllIntEk k).re - (1 - k ^ 2) * (compEllIntKk k).re)) := by
  have hk : ‖(k : ℂ)‖ < 1 := by rwa [norm_real, Real.norm_of_nonneg hk0.le]
  have hK := (Complex.hasSum_re (compEllIntKk_hasSum hk).1).mul_left (4 / π)
  have hD := hasSum_compEllIntDk_real hk0 hk1
  convert hK.sub hD using 1
  · funext m
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, poch_ofReal, pow_mul,
      ← ofReal_pow, ← ofReal_pow]
    simp only [← ofReal_natCast, ← ofReal_mul, ← ofReal_div, ← ofReal_ofNat]
    rw [ofReal_re, ascPochhammer_three_halves, Nat.factorial_succ]
    have := Real.pi_pos
    push_cast
    field_simp
    ring
  · have := Real.pi_pos
    field_simp
    ring

/-- `E(k) - k'² K(k) < k²` for real `0 < k < 1`. -/
private lemma compEllIntEk_sub_mul_compEllIntKk_lt {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    (compEllIntEk k).re - (1 - k ^ 2) * (compEllIntKk k).re < k ^ 2 := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hkm : ((k : ℂ)) ^ 2 = ((k ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [compEllIntEk_eq_ofReal hkm hk2.le, compEllIntKk_eq_ofReal hkm hk2.le, ofReal_re, ofReal_re,
    DLMF.Elliptic.Real.compEllIntEm, DLMF.Elliptic.Real.compEllIntKm,
    ← intervalIntegral.integral_const_mul]
  have hcE := DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hk2 (1 / 2)
  have hcK := DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hk2 (-(1 / 2))
  rw [← intervalIntegral.integral_sub (hcE.intervalIntegrable _ _)
    ((hcK.const_mul _).intervalIntegrable _ _)]
  have hcos : ∫ θ in (0 : ℝ)..(π / 2), k ^ 2 * Real.cos θ = k ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_cos]; simp
  conv_rhs => rw [← hcos]
  have hpt : ∀ θ, 0 ≤ Real.cos θ →
      (1 - k ^ 2 * Real.sin θ ^ 2) ^ (1 / 2 : ℝ) -
          (1 - k ^ 2) * (1 - k ^ 2 * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ) =
        k ^ 2 * Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ∧
      Real.cos θ ≤ Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) := by
    intro θ hc
    have hs := Real.sin_sq_add_cos_sq θ
    have hu : 0 < 1 - k ^ 2 * Real.sin θ ^ 2 := by nlinarith [Real.sin_sq_le_one θ]
    have hsq := Real.sqrt_pos.mpr hu
    refine ⟨?_, ?_⟩
    · rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
      have h2 := Real.sq_sqrt hu.le
      field_simp
      linear_combination (-(k ^ 2) * hs + h2)
    · rw [Real.le_sqrt hc hu.le]; nlinarith [sq_nonneg (Real.sin θ)]
  have hle : ∀ θ, 0 ≤ Real.cos θ →
      k ^ 2 * Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ≤ k ^ 2 * Real.cos θ := by
    intro θ hc
    rcases hc.eq_or_lt with h | h
    · rw [← h]; simp
    have h2 := (hpt θ hc).2
    rw [div_le_iff₀ (h.trans_le h2)]
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg k) hc)
    nlinarith
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by positivity) ((hcE.sub (hcK.const_mul _)).continuousOn) (by fun_prop) ?_ ?_
  · intro θ hθ
    have hc : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [(hpt θ hc).1]; exact hle θ hc
  · refine ⟨π / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩, ?_⟩
    have hc : 0 < Real.cos (π / 4) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hsn : 0 < Real.sin (π / 4) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by linarith [Real.pi_pos])
    rw [(hpt _ hc.le).1]
    have hs := Real.sin_sq_add_cos_sq (π / 4)
    have hu : 0 < 1 - k ^ 2 * Real.sin (π / 4) ^ 2 := by
      nlinarith [Real.sin_sq_le_one (π / 4)]
    have hlt : Real.cos (π / 4) < Real.sqrt (1 - k ^ 2 * Real.sin (π / 4) ^ 2) := by
      rw [Real.lt_sqrt hc.le]; nlinarith [mul_pos hsn hsn]
    rw [div_lt_iff₀ (hc.trans hlt)]
    have := mul_lt_mul_of_pos_left hlt (mul_pos (pow_pos hk0 2) hc)
    nlinarith

/-- The binomial series `(1 - cx)^{-β}` in powers of `x`. -/
private lemma hasSum_binomial_mul (β c : ℝ) {x : ℝ} (hcx0 : 0 ≤ c * x) (hcx : c * x < 1) :
    HasSum (fun m : ℕ => (ascPochhammer ℝ m).eval β / (Nat.factorial m : ℕ) * c ^ m * x ^ m)
      ((1 - c * x) ^ (-β)) :=
  (hasSum_ascPochhammer_binomial β hcx0 hcx).congr_fun fun m => by rw [mul_pow]; ring

/-- A power series with coefficient ratios above those of `(1 - cx)^{-β}` exceeds it. -/
private lemma binomial_lt_of_ratio {β c x A : ℝ} {w ρ : ℕ → ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hx : 0 < x) (hcx : c * x < 1) (hA : HasSum (fun m => w m * x ^ m) A)
    (hw : ∀ m, w (m + 1) = w m * ρ m) (hw0 : w 0 = 1)
    (hrs : ∀ m : ℕ, (β + m) / (m + 1) * c ≤ ρ m) (hr1 : (β + 1) / (1 + 1) * c < ρ 1) :
    (1 - c * x) ^ (-β) < A := by
  obtain ⟨h, h2⟩ := le_of_ratio_le
    (u := fun m => (ascPochhammer ℝ m).eval β / (Nat.factorial m : ℕ) * c ^ m)
    (v := w) (r := fun m : ℕ => (β + m) / (m + 1) * c) (s := ρ)
    (fun m => binomial_coeff_succ β c m) hw (by simp [hw0]) (by simp)
    (fun m => by positivity) hrs (by simp; positivity) (by simpa using hr1)
  exact hasSum_lt_of_coeff hx (hasSum_binomial_mul β c (by positivity) hcx) hA h h2

/-- A power series with coefficient ratios below those of `(1 - x)^{-β}` is below it. -/
private lemma lt_binomial_of_ratio {β x A : ℝ} {w ρ : ℕ → ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hA : HasSum (fun m => w m * x ^ m) A)
    (hw : ∀ m, w (m + 1) = w m * ρ m) (hw0 : w 0 = 1) (hr : ∀ m, 0 ≤ ρ m) (hr0 : 0 < ρ 0)
    (hrs : ∀ m : ℕ, ρ m ≤ (β + m) / (m + 1) * 1) (hr1 : ρ 1 < (β + 1) / (1 + 1) * 1) :
    A < (1 - x) ^ (-β) := by
  obtain ⟨h, h2⟩ := le_of_ratio_le (u := w)
    (v := fun m => (ascPochhammer ℝ m).eval β / (Nat.factorial m : ℕ) * 1 ^ m)
    (r := ρ) (s := fun m : ℕ => (β + m) / (m + 1) * 1)
    hw (fun m => binomial_coeff_succ β 1 m) (by simp [hw0]) (by simp [hw0])
    hr hrs hr0 (by simpa using hr1)
  have hB := hasSum_binomial_mul β 1 (x := x) (by linarith) (by linarith)
  rw [one_mul] at hB
  exact hasSum_lt_of_coeff hx hA hB h h2

/-- DLMF 19.9.6: `(1 - ¾k²)^{-1/2} < (4/(πk²))(K(k) - E(k)) < k'^{-3/4}` for `0 < k < 1`. -/
@[dlmf 19.9.E6]
theorem compEllIntKk_sub_compEllIntEk_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    (1 - 3 / 4 * k ^ 2) ^ (-(1 / 2) : ℝ) <
        4 / (π * k ^ 2) * ((compEllIntKk k).re - (compEllIntEk k).re) ∧
      4 / (π * k ^ 2) * ((compEllIntKk k).re - (compEllIntEk k).re) <
        Real.sqrt (1 - k ^ 2) ^ (-(3 / 4) : ℝ) := by
  have hx : 0 < k ^ 2 := by positivity
  have hx1 : k ^ 2 < 1 := by nlinarith
  have hA := hasSum_compEllIntDk_real hk0 hk1
  have hw := hg2_coeff_succ (3 / 2)
  constructor
  · refine binomial_lt_of_ratio (by norm_num) (by norm_num) hx (by linarith) hA hw (by simp)
      (fun m => ?_) (by norm_num)
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hm (by linarith : (0 : ℝ) ≤ 1 / 2 + m))
      (by linarith : (0 : ℝ) ≤ m + 1)]
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
    rw [show (1 / 2 : ℝ) * -(3 / 4) = -(3 / 8) by norm_num]
    refine lt_binomial_of_ratio hx hx1 hA hw (by simp) (fun m => by positivity)
      (by norm_num) (fun m => ?_) (by norm_num)
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    rw [mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- DLMF 19.9.7: `(1 - ¼k²)^{-1/2} < (4/(πk²))(E(k) - k'² K(k)) < min(k'^{-1/4}, 4/π)` for
`0 < k < 1`. -/
@[dlmf 19.9.E7]
theorem compEllIntEk_sub_mul_compEllIntKk_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    (1 - 1 / 4 * k ^ 2) ^ (-(1 / 2) : ℝ) <
        4 / (π * k ^ 2) * ((compEllIntEk k).re - (1 - k ^ 2) * (compEllIntKk k).re) ∧
      4 / (π * k ^ 2) * ((compEllIntEk k).re - (1 - k ^ 2) * (compEllIntKk k).re) <
        min (Real.sqrt (1 - k ^ 2) ^ (-(1 / 4) : ℝ)) (4 / π) := by
  have hx : 0 < k ^ 2 := by positivity
  have hx1 : k ^ 2 < 1 := by nlinarith
  have hA := hasSum_compEllIntEk_sub_real hk0 hk1
  have hw := hg2_coeff_succ (1 / 2)
  refine ⟨?_, lt_min ?_ ?_⟩
  · refine binomial_lt_of_ratio (by norm_num) (by norm_num) hx (by linarith) hA hw (by simp)
      (fun m => ?_) (by norm_num)
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
    rw [show (1 / 2 : ℝ) * -(1 / 4) = -(1 / 8) by norm_num]
    refine lt_binomial_of_ratio hx hx1 hA hw (by simp) (fun m => by positivity)
      (by norm_num) (fun m => ?_) (by norm_num)
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    rw [mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · have h := compEllIntEk_sub_mul_compEllIntKk_lt hk0 hk1
    have := Real.pi_pos
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) this]
    nlinarith

/-- Facts on the AGM sequence started at `(1, g₀)` with `0 < g₀ ≤ 1`. -/
private lemma agmSeqG_pos_and_le_agmSeqA {g₀ : ℝ≥0} (hg : 0 < g₀) (h1 : g₀ ≤ 1) (n : ℕ) :
    0 < (agmSeqG 1 g₀ n : ℝ) ∧ (agmSeqG 1 g₀ n : ℝ) ≤ agmSeqA 1 g₀ n := by
  induction n with
  | zero => exact ⟨by exact_mod_cast hg, by exact_mod_cast h1⟩
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · rw [(agmSeq_succ 1 g₀ n).2, Real.coe_sqrt]
      exact Real.sqrt_pos.mpr (by push_cast; nlinarith [ih.1, ih.2])
    · exact_mod_cast NNReal.agmSequences_fst_le_snd n n

/-- `cₙ² = aₙ² - gₙ²` along the AGM sequence started at `(1, g₀)`. -/
private lemma agmSeqC_sq_eq {g₀ : ℝ≥0} (hg : 0 < g₀) (h1 : g₀ ≤ 1) (n : ℕ) :
    agmSeqC 1 g₀ n ^ 2 = (agmSeqA 1 g₀ n : ℝ) ^ 2 - (agmSeqG 1 g₀ n : ℝ) ^ 2 := by
  obtain ⟨h0, hle⟩ := agmSeqG_pos_and_le_agmSeqA hg h1 n
  rw [agmSeqC, Real.sq_sqrt (by nlinarith)]

/-- `4 c_{n+1}² ≤ cₙ²` along the AGM sequence started at `(1, g₀)`. -/
private lemma four_mul_agmSeqC_sq_succ_le {g₀ : ℝ≥0} (hg : 0 < g₀) (h1 : g₀ ≤ 1) (n : ℕ) :
    4 * agmSeqC 1 g₀ (n + 1) ^ 2 ≤ agmSeqC 1 g₀ n ^ 2 := by
  obtain ⟨h0, hle⟩ := agmSeqG_pos_and_le_agmSeqA hg h1 n
  rw [(agmSeqC_succ hg h1 n).1, agmSeqC_sq_eq hg h1 n]
  nlinarith

/-- DLMF 19.9.8: `k' < E(k)/K(k) < ((1 + k')/2)²` for `0 < k < 1`. -/
@[dlmf 19.9.E8]
theorem compEllIntEk_div_compEllIntKk_bounds {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    Real.sqrt (1 - k ^ 2) < (compEllIntEk k).re / (compEllIntKk k).re ∧
      (compEllIntEk k).re / (compEllIntKk k).re < ((1 + Real.sqrt (1 - k ^ 2)) / 2) ^ 2 := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hkm : ((k : ℂ)) ^ 2 = ((k ^ 2 : ℝ) : ℂ) := by push_cast; ring
  obtain ⟨-, hE⟩ := compEllIntEk_eq_agm hkm hk2
  have hK := compEllIntKk_eq_pi_div_agm hkm hk2
  set g₀ : ℝ≥0 := NNReal.sqrt (1 - k ^ 2).toNNReal with hg₀def
  have hg₀ : (g₀ : ℝ) = Real.sqrt (1 - k ^ 2) := by
    simp [g₀, Real.coe_sqrt, Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ 1 - k ^ 2)]
  have hgpos : 0 < g₀ := by
    rw [← NNReal.coe_pos, hg₀]; exact Real.sqrt_pos.mpr (by linarith)
  have hg1' : (g₀ : ℝ) < 1 := by
    rw [hg₀, Real.sqrt_lt' one_pos]; nlinarith
  have hg1 : g₀ ≤ 1 := by rw [← NNReal.coe_le_coe]; exact_mod_cast hg1'.le
  have hM : (0 : ℝ) < NNReal.agm 1 g₀ := by exact_mod_cast NNReal.agm_pos one_pos hgpos
  set c := agmSeqC 1 g₀ with hc
  set t : ℕ → ℝ := fun n => (2 : ℝ) ^ (n + 1) * c (n + 2) ^ 2 with ht
  have ht_le : ∀ n, t n ≤ t 0 * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := four_mul_agmSeqC_sq_succ_le hgpos hg1 (n + 2)
      rw [← hc] at h
      have ih' : (2 : ℝ) ^ (n + 1) * c (n + 2) ^ 2 ≤ t 0 * (1 / 2) ^ n := ih
      show (2 : ℝ) ^ (n + 1 + 1) * c (n + 1 + 2) ^ 2 ≤ t 0 * (1 / 2) ^ (n + 1)
      have hp : (0 : ℝ) < 2 ^ (n + 1) := by positivity
      rw [pow_succ, pow_succ (1 / 2 : ℝ), show n + 1 + 2 = n + 2 + 1 by ring]
      nlinarith [mul_le_mul_of_nonneg_left h hp.le]
  have ht0 : ∀ n, 0 ≤ t n := fun n => by positivity
  have hsum : Summable t :=
    Summable.of_nonneg_of_le ht0 ht_le ((summable_geometric_two).mul_left _)
  -- the AGM members at `n = 1`
  have hA1 : (agmSeqA 1 g₀ 1 : ℝ) = (1 + Real.sqrt (1 - k ^ 2)) / 2 := by
    rw [(agmSeq_succ 1 g₀ 0).1]; push_cast; simp [agmSeqA, agmSeqG, hg₀]
  have hc1 : c 1 = (1 - Real.sqrt (1 - k ^ 2)) / 2 := by
    rw [hc, (agmSeqC_succ hgpos hg1 0).1]; simp [agmSeqA, agmSeqG, hg₀]
  have hc1pos : 0 < c 1 := by rw [hc1]; rw [hg₀] at hg1'; linarith
  -- `c₂ > 0` and `4c₂² < c₁²`
  obtain ⟨hG1, hGA1⟩ := agmSeqG_pos_and_le_agmSeqA hgpos hg1 1
  have hc2 : c 2 = c 1 ^ 2 / (4 * agmSeqA 1 g₀ 2) := (agmSeqC_succ hgpos hg1 1).2
  have hA2 : (0 : ℝ) < agmSeqA 1 g₀ 2 := lt_of_lt_of_le (agmSeqG_pos_and_le_agmSeqA hgpos hg1 2).1
    (agmSeqG_pos_and_le_agmSeqA hgpos hg1 2).2
  have hc2pos : 0 < c 2 := by rw [hc2]; positivity
  have hc2' : c 2 = ((agmSeqA 1 g₀ 1 : ℝ) - agmSeqG 1 g₀ 1) / 2 := (agmSeqC_succ hgpos hg1 1).1
  have hc1sq : c 1 ^ 2 = _ := agmSeqC_sq_eq hgpos hg1 1
  have h4 : 4 * c 2 ^ 2 < c 1 ^ 2 := by
    rw [hc1sq, hc2']
    nlinarith
  -- bounds on the sum
  have hSpos : 0 < ∑' n, t n := by
    have := hsum.tsum_pos ht0 0 (by simp only [ht]; positivity)
    exact this
  have hSle : ∑' n, t n ≤ 2 * t 0 := by
    have := hsum.tsum_le_tsum ht_le ((summable_geometric_two).mul_left _)
    rw [tsum_mul_left, tsum_geometric_two] at this
    linarith
  have ht0' : t 0 = 2 * c 2 ^ 2 := by simp [ht]
  -- the ratio
  have hratio : (compEllIntEk k).re / (compEllIntKk k).re =
      (agmSeqA 1 g₀ 1 : ℝ) ^ 2 - ∑' n, t n := by
    have hKre : (compEllIntKk k).re = π / (2 * (NNReal.agm 1 g₀ : ℝ)) := by
      rw [hK]; norm_cast
    have : π / (2 * (NNReal.agm 1 g₀ : ℝ)) ≠ 0 := by positivity
    rw [hE, re_mul_ofReal, hKre]
    field_simp
  rw [hratio, hA1]
  have hs := Real.sqrt_nonneg (1 - k ^ 2)
  rw [hc1] at h4
  constructor
  · nlinarith
  · linarith

/-- The perimeter `L(a, b)` of an ellipse with semiaxes `a, b` (DLMF §19.9(i)): the arc length
`∫₀^{2π} √(a² sin²t + b² cos²t) dt` of `t ↦ (a cos t, b sin t)`. -/
@[dlmf 19.9.i]
def ellipsePerimeter (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * π), Real.sqrt (a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2)

/-- DLMF 19.9.9: `L(a, b) = 4a E(k)`, `k² = 1 - b²/a²`, `a > b` (here `b ≥ 0`). -/
@[dlmf 19.9.E9]
theorem ellipsePerimeter_eq {a b : ℝ} (hb : 0 ≤ b) (hab : b < a) :
    (ellipsePerimeter a b : ℂ) = 4 * a * compEllIntEk (Real.sqrt (1 - b ^ 2 / a ^ 2)) := by
  have ha : 0 < a := lt_of_le_of_lt hb hab
  set m := 1 - b ^ 2 / a ^ 2 with hmdef
  have hba : b ^ 2 / a ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hm0 : 0 ≤ m := by rw [hmdef]; linarith
  have hm1 : m ≤ 1 := by
    rw [hmdef]; have : 0 ≤ b ^ 2 / a ^ 2 := by positivity
    linarith
  set f : ℝ → ℝ := fun θ => Real.sqrt (1 - m * Real.sin θ ^ 2) with hf
  have hfc : Continuous f := by fun_prop
  have hfper : Function.Periodic f π := fun θ => by simp [hf, Real.sin_add_pi]
  have hfsym : ∀ θ, f (π - θ) = f θ := fun θ => by simp [hf, Real.sin_pi_sub]
  -- (i) factor out `a`
  have h1 : ellipsePerimeter a b = a * ∫ t in (0 : ℝ)..(2 * π), f (t + π / 2) := by
    rw [ellipsePerimeter, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hf, Real.sin_add_pi_div_two]
    have hst := Real.sin_sq_add_cos_sq t
    have hX : 0 ≤ 1 - m * Real.cos t ^ 2 := by
      nlinarith [Real.cos_sq_le_one t, sq_nonneg (Real.cos t)]
    rw [show a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2 = a ^ 2 * (1 - m * Real.cos t ^ 2) by
      rw [hmdef]; field_simp; linear_combination a ^ 2 * hst,
      Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le]
  -- (ii) shift and periodicity
  have hper2 : Function.Periodic f (2 * π) := by
    intro θ; rw [show θ + 2 * π = θ + π + π by ring, hfper, hfper]
  have h2 : ∫ t in (0 : ℝ)..(2 * π), f (t + π / 2) = ∫ t in (0 : ℝ)..(2 * π), f t := by
    rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (2 * π),
      hper2.intervalIntegral_add_eq (π / 2) 0, zero_add]
  -- (iii) reduce to a quarter period
  have h3 : ∫ t in (0 : ℝ)..(2 * π), f t = 4 * ∫ t in (0 : ℝ)..(π / 2), f t := by
    have hq : ∫ t in (π / 2)..π, f t = ∫ t in (0 : ℝ)..(π / 2), f t := by
      have := intervalIntegral.integral_comp_sub_left f (a := 0) (b := π / 2) π
      simp only [hfsym, sub_zero, show π - π / 2 = π / 2 by ring] at this
      exact this.symm
    have hh : ∫ t in π..(2 * π), f t = ∫ t in (0 : ℝ)..π, f t := by
      have := intervalIntegral.integral_comp_add_right f (a := 0) (b := π) π
      simp only [zero_add, show π + π = 2 * π by ring] at this
      rw [← this]
      exact intervalIntegral.integral_congr fun t _ => hfper t
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := π)
      (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _), hh,
      ← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
      (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _), hq]
    ring
  -- (iv) identify `E(m)`
  have hk : ((Real.sqrt (1 - b ^ 2 / a ^ 2) : ℝ) : ℂ) ^ 2 = ((m : ℝ) : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt hm0]
  have h4 : compEllIntEk ((Real.sqrt (1 - b ^ 2 / a ^ 2) : ℝ) : ℂ) =
      ((∫ t in (0 : ℝ)..(π / 2), f t : ℝ) : ℂ) := by
    rw [compEllIntEk_eq_ofReal hk hm1, DLMF.Elliptic.Real.compEllIntEm]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hf, rpow_half_eq_sqrt]
  rw [h1, h2, h3, h4]
  push_cast
  ring

/-- DLMF §19.9(i) (Barnard et al. 2000): Ramanujan's approximation is from below,
`π(a + b)(1 + 3λ²/(10 + √(4 - 3λ²))) ≤ L(a, b)`, `λ = (a - b)/(a + b)`, `a > b ≥ 0`. -/
@[dlmf 19.9.i]
theorem pi_mul_ramanujan_le_ellipsePerimeter {a b : ℝ} (hb : 0 ≤ b) (hab : b < a) :
    π * (a + b) * (1 + 3 * ((a - b) / (a + b)) ^ 2 /
        (10 + Real.sqrt (4 - 3 * ((a - b) / (a + b)) ^ 2))) ≤ ellipsePerimeter a b := by
  sorry

/-! ### §19.9(ii) Incomplete integrals -/

/-- DLMF 19.9.11: `φ ≤ F(φ, k) ≤ min(φ/Δ, gd⁻¹(φ))` for `0 < k < 1`, `0 ≤ φ ≤ π/2`,
`Δ = √(1 - k² sin²φ)`; the bound `gd⁻¹(φ)` (DLMF 4.23.41,
`DLMF.Elementary.inverseGudermannian`) is stated for `φ < π/2`. -/
@[dlmf 19.9.E11]
theorem incEllIntFk_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) :
    φ ≤ (incEllIntFk φ k).re ∧
      (incEllIntFk φ k).re ≤ φ / Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) ∧
      (φ < π / 2 → (incEllIntFk φ k).re ≤ DLMF.Elementary.inverseGudermannian φ) := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hm0 : 0 ≤ k ^ 2 := sq_nonneg k
  rw [re_incEllIntFk_ofReal hk2.le, DLMF.Elliptic.Real.incEllIntFm]
  have hc := DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hk2 (-(1 / 2))
  have hΔ : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 φ
  refine ⟨?_, ?_, ?_⟩
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (continuous_const.intervalIntegrable 0 φ)
      (hc.intervalIntegrable 0 φ) (f := fun _ => (1 : ℝ)) (fun θ hθ => by
        rw [rpow_neg_half_eq_inv_sqrt (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
        have h1 := one_sub_mul_sin_sq_le_one hm0 θ
        have h2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ
        rw [one_le_inv₀ (Real.sqrt_pos.mpr h2)]
        exact Real.sqrt_le_one.mpr h1)
    simpa using h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (hc.intervalIntegrable 0 φ)
      (continuous_const.intervalIntegrable 0 φ)
      (g := fun _ => (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2))⁻¹)
      (fun θ hθ => by
        rw [rpow_neg_half_eq_inv_sqrt (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
        exact inv_anti₀ (Real.sqrt_pos.mpr hΔ)
          (Real.sqrt_le_sqrt (one_sub_mul_sin_sq_le_of_le hm0 hθ.1 hθ.2 hφ1)))
    simpa [div_eq_mul_inv] using h
  · intro hφ2
    unfold DLMF.Elementary.inverseGudermannian
    have hcos : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < Real.cos θ := fun θ hθ =>
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    refine intervalIntegral.integral_mono_on hφ0 (hc.intervalIntegrable 0 φ) ?_ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hφ0]
      exact (Real.continuous_cos.continuousOn).inv₀ fun θ hθ => (hcos θ hθ).ne'
    · intro θ hθ
      rw [rpow_neg_half_eq_inv_sqrt (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
      refine inv_anti₀ (hcos θ hθ) ?_
      rw [← Real.sqrt_sq (hcos θ hθ).le]
      exact Real.sqrt_le_sqrt (cos_sq_le_one_sub_mul_sin_sq hk2.le θ)

/-- DLMF 19.9.12: `max(sin φ, φΔ) ≤ E(φ, k) ≤ φ` for `0 < k < 1`, `0 ≤ φ ≤ π/2`. -/
@[dlmf 19.9.E12]
theorem incEllIntEk_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) :
    max (Real.sin φ) (φ * Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2)) ≤ (incEllIntEk φ k).re ∧
      (incEllIntEk φ k).re ≤ φ := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hm0 : 0 ≤ k ^ 2 := sq_nonneg k
  rw [re_incEllIntEk_ofReal hk2.le, DLMF.Elliptic.Real.incEllIntEm]
  have hc := DLMF.Elliptic.continuous_one_sub_mul_sin_sq_rpow hk2 (1 / 2)
  refine ⟨max_le ?_ ?_, ?_⟩
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (Real.continuous_cos.intervalIntegrable 0 φ)
      (hc.intervalIntegrable 0 φ) (fun θ hθ => by
        rw [rpow_half_eq_sqrt]
        have hcos : 0 ≤ Real.cos θ :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
        rw [← Real.sqrt_sq hcos]
        exact Real.sqrt_le_sqrt (cos_sq_le_one_sub_mul_sin_sq hk2.le θ))
    simpa using h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (continuous_const.intervalIntegrable 0 φ)
      (hc.intervalIntegrable 0 φ) (f := fun _ => Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2))
      (fun θ hθ => by
        rw [rpow_half_eq_sqrt]
        exact Real.sqrt_le_sqrt (one_sub_mul_sin_sq_le_of_le hm0 hθ.1 hθ.2 hφ1))
    simpa using h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hφ0
      (hc.intervalIntegrable 0 φ)
      (continuous_const.intervalIntegrable 0 φ) (g := fun _ => (1 : ℝ)) (fun θ _ => by
        rw [rpow_half_eq_sqrt]
        exact Real.sqrt_le_one.mpr (one_sub_mul_sin_sq_le_one hm0 θ))
    simpa using h

/-- Pointwise comparison of the third-kind integrands in the modulus. -/
private lemma piIntegrand_le_piIntegrand_of_le {n m m' θ : ℝ} (hn : n < 1) (hm : m ≤ m')
    (hm' : m' * Real.sin θ ^ 2 < 1)
    (hm0 : m * Real.sin θ ^ 2 < 1) :
    DLMF.Elliptic.piIntegrand n m θ ≤ DLMF.Elliptic.piIntegrand n m' θ := by
  unfold DLMF.Elliptic.piIntegrand
  refine mul_le_mul_of_nonneg_left ?_ (inv_one_sub_mul_sin_sq_pos hn θ).le
  rw [rpow_neg_half_eq_inv_sqrt (by linarith), rpow_neg_half_eq_inv_sqrt (by linarith)]
  refine inv_anti₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt ?_)
  nlinarith [sq_nonneg (Real.sin θ)]

/-- DLMF 19.9.13: `Π(φ, α², 0) ≤ Π(φ, α², k) ≤ min(Π(φ, α², 0)/Δ, Π(φ, α², 1))` for
`0 < k < 1`, `0 ≤ φ ≤ π/2` and real `α² < 1`; the bound by `Π(φ, α², 1)` is stated for
`φ < π/2` (it is infinite at `φ = π/2`). -/
@[dlmf 19.9.E13]
theorem incEllIntPik_bounds {φ α2 k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) (hα : α2 < 1) :
    (incEllIntPik φ α2 0).re ≤ (incEllIntPik φ α2 k).re ∧
      (incEllIntPik φ α2 k).re ≤
        (incEllIntPik φ α2 0).re / Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) ∧
      (φ < π / 2 → (incEllIntPik φ α2 k).re ≤ (incEllIntPik φ α2 1).re) := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hm0 : 0 ≤ k ^ 2 := sq_nonneg k
  have e0 : incEllIntPik φ α2 0 = incEllIntPik φ α2 ((0 : ℝ) : ℂ) := by simp
  have e1 : incEllIntPik φ α2 1 = incEllIntPik φ α2 ((1 : ℝ) : ℂ) := by simp
  rw [e0, e1, re_incEllIntPik_ofReal hα hk2.le, re_incEllIntPik_ofReal (k := 0) hα (by norm_num),
    re_incEllIntPik_ofReal (k := 1) hα (by norm_num)]
  simp only [DLMF.Elliptic.Real.incEllIntPim]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, one_pow]
  have hcont : ∀ m : ℝ, m < 1 → Continuous (DLMF.Elliptic.piIntegrand α2 m) :=
    fun m hm => DLMF.Elliptic.continuous_piIntegrand hα hm
  have hΔ : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 φ
  refine ⟨?_, ?_, ?_⟩
  · refine intervalIntegral.integral_mono_on hφ0 ((hcont 0 (by norm_num)).intervalIntegrable _ _)
      ((hcont _ hk2).intervalIntegrable _ _) fun θ _ => ?_
    have h := piIntegrand_le_piIntegrand_of_le (θ := θ) hα hm0 (by nlinarith [Real.sin_sq_le_one θ])
      (by simp)
    simpa using h
  · rw [div_eq_mul_inv, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_mono_on hφ0 ((hcont _ hk2).intervalIntegrable _ _)
      (((hcont 0 (by norm_num)).mul continuous_const).intervalIntegrable _ _) fun θ hθ => ?_
    unfold DLMF.Elliptic.piIntegrand
    simp only [zero_mul, sub_zero, Real.one_rpow, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ (inv_one_sub_mul_sin_sq_pos hα θ).le
    rw [rpow_neg_half_eq_inv_sqrt (DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ).le]
    exact inv_anti₀ (Real.sqrt_pos.mpr hΔ)
      (Real.sqrt_le_sqrt (one_sub_mul_sin_sq_le_of_le hm0 hθ.1 hθ.2 hφ1))
  · intro hφ2
    have hcos : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < Real.cos θ := fun θ hθ =>
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    have hbase : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < 1 - 1 * Real.sin θ ^ 2 := fun θ hθ => by
      have := Real.sin_sq_add_cos_sq θ
      have := hcos θ hθ
      nlinarith
    refine intervalIntegral.integral_mono_on hφ0 ((hcont _ hk2).intervalIntegrable _ _) ?_
      fun θ hθ => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hφ0]
      unfold DLMF.Elliptic.piIntegrand
      refine ContinuousOn.mul ((Continuous.inv₀ (by fun_prop)
        fun θ => (DLMF.Elliptic.one_sub_mul_sin_sq_pos hα θ).ne').continuousOn) ?_
      · exact ContinuousOn.rpow_const (by fun_prop) fun θ hθ => Or.inl (hbase θ hθ).ne'
    · have hb := hbase θ hθ
      exact piIntegrand_le_piIntegrand_of_le hα hk2.le (by linarith)
        (by nlinarith [Real.sin_sq_le_one θ])

/-- DLMF 19.9.1, second line: `1 ≤ E(k) ≤ π/2` for `0 < k < 1`. -/
@[dlmf 19.9.E1]
theorem one_le_compEllIntEk_le {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    1 ≤ (compEllIntEk k).re ∧ (compEllIntEk k).re ≤ π / 2 := by
  rw [compEllIntEk_eq_incEllIntEk]
  have h := incEllIntEk_bounds (φ := π / 2) hk0 hk1 (by positivity) le_rfl
  rw [Real.sin_pi_div_two] at h
  exact ⟨le_trans (le_max_left _ _) h.1, h.2⟩

/-- DLMF 19.9.1, third line: `1 ≤ (2/π)√(1 - α²) Π(α², k) ≤ 1/k'` for `0 < k < 1` and real
`α² < 1`. -/
@[dlmf 19.9.E1]
theorem one_le_compEllIntPik_le {α2 k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hα : α2 < 1) :
    1 ≤ 2 / π * Real.sqrt (1 - α2) * (compEllIntPik α2 k).re ∧
      2 / π * Real.sqrt (1 - α2) * (compEllIntPik α2 k).re ≤ 1 / Real.sqrt (1 - k ^ 2) := by
  rw [compEllIntPik_eq_incEllIntPik]
  have h := incEllIntPik_bounds (φ := π / 2) hk0 hk1 (by positivity) le_rfl hα
  rw [Real.sin_pi_div_two, one_pow, mul_one] at h
  have e0 : incEllIntPik ((π / 2 : ℝ) : ℂ) α2 0 = incEllIntPik ((π / 2 : ℝ) : ℂ) α2 ((0 : ℝ) : ℂ) :=
    by simp
  rw [e0, re_incEllIntPik_ofReal (k := 0) hα (by norm_num)] at h
  have hz : DLMF.Elliptic.Real.incEllIntPim (π / 2) α2 (0 ^ 2) = π / (2 * Real.sqrt (1 - α2)) := by
    rw [zero_pow two_ne_zero]
    exact DLMF.Elliptic.Real.compEllIntPim_param_zero hα
  rw [hz] at h
  have hs : 0 < Real.sqrt (1 - α2) := Real.sqrt_pos.mpr (by linarith)
  have hk' : 0 < Real.sqrt (1 - k ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hc : 0 < 2 / π * Real.sqrt (1 - α2) := by positivity
  obtain ⟨h1, h2, -⟩ := h
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hc.le
    calc (1 : ℝ) = 2 / π * Real.sqrt (1 - α2) * (π / (2 * Real.sqrt (1 - α2))) := by
          field_simp
      _ ≤ _ := this
  · have := mul_le_mul_of_nonneg_left h2 hc.le
    calc _ ≤ 2 / π * Real.sqrt (1 - α2) * (π / (2 * Real.sqrt (1 - α2)) / Real.sqrt (1 - k ^ 2)) :=
          this
      _ = 1 / Real.sqrt (1 - k ^ 2) := by field_simp

/-- DLMF 19.9.14: `3/(1 + Δ + cos φ) < F(φ, k)/sin φ < (Δ cos φ)^{-1/3}` for `0 < k < 1`,
`0 < φ < π/2`. -/
@[dlmf 19.9.E14]
theorem incEllIntFk_div_sin_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) :
    3 / (1 + Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ) <
        (incEllIntFk φ k).re / Real.sin φ ∧
      (incEllIntFk φ k).re / Real.sin φ <
        (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) * Real.cos φ) ^ (-(1 / 3) : ℝ) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ1⟩
  have hx : 0 < Real.cos φ ^ 2 := sq_pos_of_pos hc
  have hy : 0 < 1 - k ^ 2 * Real.sin φ ^ 2 := DLMF.Elliptic.one_sub_mul_sin_sq_pos hk φ
  have hxy : ¬(Real.cos φ ^ 2 = 1 - k ^ 2 * Real.sin φ ^ 2 ∧ 1 - k ^ 2 * Real.sin φ ^ 2 = 1) := by
    intro he
    nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_pos hs]
  have hF : (incEllIntFk φ k).re / Real.sin φ =
      (Carlson.carlsonRF ((Real.cos φ ^ 2 : ℝ) : ℂ)
          ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1).re := by
    have h := congrArg Complex.re (Carlson.Real.incEllIntFk_eq hφ0 hφ1 hk)
    have he := incEllIntFk_eq_ofReal (m:=k ^ 2) (k:=(k : ℂ)) (by push_cast; rfl) hk.le φ
    rw [he, ofReal_re]
    change DLMF.Elliptic.Real.incEllIntFm φ (k ^ 2) / Real.sin φ = _
    simp only [ofReal_re] at h
    have hreal : Carlson.Real.incEllIntFk φ k = DLMF.Elliptic.Real.incEllIntFm φ (k ^ 2) := by
      simp only [Carlson.Real.incEllIntFk, DLMF.Elliptic.Real.incEllIntFm, neg_div]
    rw [hreal] at h
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at h
    rw [h]
    field_simp
  rw [hF]
  constructor
  · have h := Carlson.carlsonRF_capacity_lower_bound hx hy (by norm_num : (0 : ℝ) < 1) hxy
    simpa only [Real.sqrt_sq hc.le, Real.sqrt_one, ofReal_one, add_comm, add_left_comm] using h
  · let b : Fin 3 → ℝ := fun _ => 1 / 2
    let v : Fin 3 → ℝ := ![Real.cos φ ^ 2, 1 - k ^ 2 * Real.sin φ ^ 2, 1]
    have hb : b ∈ ProbabilityTheory.mvRealBetaDomain := by intro i; norm_num [b]
    have hv : ∀ i, 0 < v i := by intro i; fin_cases i <;> first | exact hx | exact hy | norm_num [v]
    have hn : ∃ i j, v i ≠ v j := by
      refine ⟨0, 2, ?_⟩
      dsimp [v]
      nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_pos hs]
    have hh := (Carlson.carlsonRReal_bounds_between_neg_sum_zero hb hv hn
      (by norm_num : (-1 / 2 : ℝ) < 0) (by norm_num [b, Fin.sum_univ_succ])).2
    have he := Carlson.ofReal_carlsonRReal (-1 / 2) hb hv
    have he' : (Carlson.carlsonRF ((Real.cos φ ^ 2 : ℝ) : ℂ)
        ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ) 1).re =
        Carlson.carlsonRReal (-1 / 2) b v := by
      unfold Carlson.carlsonRF
      have ev : (fun i => (v i : ℂ)) =
          ![((Real.cos φ ^ 2 : ℝ) : ℂ), ((1 - k ^ 2 * Real.sin φ ^ 2 : ℝ) : ℂ), 1] := by
        ext i; fin_cases i <;> simp [v]
      norm_num only [b, ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat, ev] at he
      rw [neg_div, ←he, ofReal_re]
      simp only [neg_div, b]
    rw [he']
    refine hh.trans_eq ?_
    rw [←Real.exp_mul, Real.rpow_def_of_pos (mul_pos (Real.sqrt_pos.mpr hy) hc)]
    congr 1
    simp only [b, v, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Real.log_one, mul_zero,
          Real.log_mul (Real.sqrt_pos.mpr hy).ne' hc.ne',
      Real.log_sqrt hy.le, Real.log_pow]
    ring

/-- DLMF 19.9.15: `1 < F(φ, k)/((sin φ) ln(4/(Δ + cos φ))) < 4/(2 + (1 + k²) sin²φ)` for
`0 < k < 1`, `0 < φ ≤ π/2`. -/
@[dlmf 19.9.E15]
theorem incEllIntFk_div_sin_mul_log_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ ≤ π / 2) :
    1 < (incEllIntFk φ k).re /
        (Real.sin φ * Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ))) ∧
      (incEllIntFk φ k).re /
          (Real.sin φ * Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ))) <
        4 / (2 + (1 + k ^ 2) * Real.sin φ ^ 2) := by
  sorry

/-- DLMF 19.9.16: `F(φ, k) = (2/π) K(k') ln(4/(Δ + cos φ)) - θΔ²` with
`(sin φ)/8 < θ < (ln 2)/(k² sin φ)`, for `0 < k < 1`, `0 < φ ≤ π/2`; here `θ` is defined by the
equation. -/
@[dlmf 19.9.E16]
theorem incEllIntFk_eq_log_sub_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 < φ)
    (hφ1 : φ ≤ π / 2) :
    Real.sin φ / 8 <
        (2 / π * (compEllIntKk (Real.sqrt (1 - k ^ 2))).re *
            Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ)) -
          (incEllIntFk φ k).re) / (1 - k ^ 2 * Real.sin φ ^ 2) ∧
      (2 / π * (compEllIntKk (Real.sqrt (1 - k ^ 2))).re *
            Real.log (4 / (Real.sqrt (1 - k ^ 2 * Real.sin φ ^ 2) + Real.cos φ)) -
          (incEllIntFk φ k).re) / (1 - k ^ 2 * Real.sin φ ^ 2) <
        Real.log 2 / (k ^ 2 * Real.sin φ) := by
  sorry

/-! ### Helpers for 19.9.17–19.9.18 -/

/-- At `x`, the function `Real.artanh` has derivative `(1 / (1 - x ^ 2))`. -/
private lemma hasDerivAt_artanh_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  have heq : (fun y => 1 / 2 * (Real.log (1 + y) - Real.log (1 - y))) =ᶠ[𝓝 x] Real.artanh := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    have h1' : 0 < 1 + y := by linarith [hy.1]
    have h2' : 0 < 1 - y := by linarith [hy.2]
    rw [Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩, Real.log_div h1'.ne' h2'.ne']
  have hd := (((hasDerivAt_id x).const_add 1).log h1.ne').sub
    (((hasDerivAt_id x).const_sub 1).log h2.ne') |>.const_mul (1 / 2 : ℝ)
  refine (hd.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  have h3 : (1 - x ^ 2) ≠ 0 := by nlinarith
  simp only [id]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ θ in (0 : ℝ)..φ, Real.cos θ /
(1 - q ^ 2 * Real.sin θ ^ 2) = q⁻¹ * Real.artanh (q * Real.sin φ)`. -/
private lemma integral_cos_div_one_sub_sq_mul_sin_sq {q φ : ℝ} (hq : 0 < q) (hφ0 : 0 ≤ φ)
    (hφ1 : φ < π / 2)
    (hqs : q * Real.sin φ < 1) :
    ∫ θ in (0 : ℝ)..φ, Real.cos θ / (1 - q ^ 2 * Real.sin θ ^ 2) =
      q⁻¹ * Real.artanh (q * Real.sin φ) := by
  have hmem : ∀ θ ∈ uIcc 0 φ, q * Real.sin θ ∈ Ioo (-1 : ℝ) 1 := by
    intro θ hθ
    rw [uIcc_of_le hφ0] at hθ
    have h0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2])
    have h1 : Real.sin θ ≤ Real.sin φ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hθ.1, Real.pi_pos]) hφ1.le hθ.2
    exact ⟨by nlinarith, by nlinarith⟩
  have hden : ∀ θ ∈ uIcc 0 φ, 0 < 1 - q ^ 2 * Real.sin θ ^ 2 := by
    intro θ hθ
    have := hmem θ hθ
    nlinarith [this.1, this.2]
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ => q⁻¹ * Real.artanh (q * Real.sin θ))
    (f' := fun θ => Real.cos θ / (1 - q ^ 2 * Real.sin θ ^ 2)) (a := 0) (b := φ)
    (fun θ hθ => by
      have h := ((hasDerivAt_artanh_of_mem_Ioo (hmem θ hθ)).comp θ
        ((Real.hasDerivAt_sin θ).const_mul q)).const_mul q⁻¹
      refine h.congr_deriv ?_
      have := (hden θ hθ).ne'
      rw [mul_pow]
      field_simp)
    (ContinuousOn.intervalIntegrable (by
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun θ hθ => (hden θ hθ).ne'))
  rw [this]
  simp

/-- Cauchy–Schwarz for interval integrals of continuous nonnegative functions. -/
private lemma sq_integral_sqrt_mul_sqrt_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : Continuous f)
    (hg : Continuous g) (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x) :
    (∫ x in a..b, Real.sqrt (f x) * Real.sqrt (g x)) ^ 2 ≤
      (∫ x in a..b, f x) * ∫ x in a..b, g x := by
  set A := ∫ x in a..b, f x
  set B := ∫ x in a..b, g x
  set C := ∫ x in a..b, Real.sqrt (f x) * Real.sqrt (g x)
  have hsf : Continuous fun x => Real.sqrt (f x) := hf.sqrt
  have hsg : Continuous fun x => Real.sqrt (g x) := hg.sqrt
  have hq : ∀ t : ℝ, 0 ≤ A * (t * t) + (-2 * C) * t + B := by
    intro t
    have h0 : 0 ≤ ∫ x in a..b, (t * Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have hexp : ∫ x in a..b, (t * Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 =
        ∫ x in a..b, (t ^ 2 * f x - 2 * t * (Real.sqrt (f x) * Real.sqrt (g x)) + g x) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hab] at hx
      have h1 := Real.sq_sqrt (hf0 x hx)
      have h2 := Real.sq_sqrt (hg0 x hx)
      linear_combination t ^ 2 * h1 + h2
    rw [hexp, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
    · linarith
    all_goals first
      | exact (hf.intervalIntegrable _ _).const_mul _
      | exact ((hsf.mul hsg).intervalIntegrable _ _).const_mul _
      | exact hg.intervalIntegrable _ _
      | exact (((hf.intervalIntegrable _ _).const_mul _).sub
          (((hsf.mul hsg).intervalIntegrable _ _).const_mul _))
  have := discrim_le_zero hq
  rw [discrim] at this
  nlinarith

/-- Estimate under the stated parameter and domain assumptions: `c / ((a + b) / 2) ≤ c * (a⁻¹ +
b⁻¹) / 2`. -/
private lemma div_avg_le_mul_avg_inv {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) :
    c / ((a + b) / 2) ≤ c * (a⁻¹ + b⁻¹) / 2 := by
  rw [div_le_iff₀ (by positivity)]
  have : c * (a⁻¹ + b⁻¹) / 2 * ((a + b) / 2) = c * ((a + b) ^ 2 / (4 * a * b)) := by
    field_simp; ring
  rw [this]
  have h1 : 1 ≤ (a + b) ^ 2 / (4 * a * b) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (a - b)]
  nlinarith

/-- Estimate under the stated parameter and domain assumptions: `c / ((c ^ 2 + b) / 2) ≤
(Real.sqrt b)⁻¹`. -/
private lemma div_avg_sq_add_le_inv_sqrt {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    c / ((c ^ 2 + b) / 2) ≤ (Real.sqrt b)⁻¹ := by
  have hsb := Real.sq_sqrt hb.le
  have hsb0 := Real.sqrt_pos.2 hb
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hsb0]
  nlinarith [sq_nonneg (c - Real.sqrt b)]

/-- Identity under the stated parameter and domain assumptions: `Real.sqrt (c * ((c ^ 2)⁻¹ + b⁻¹)
/ 2) * Real.sqrt (c / ((c ^ 2 + b) / 2)) = (Real.sqrt b)⁻¹`. -/
private lemma sqrt_mul_sqrt_avg_eq_inv_sqrt {b c : ℝ} (hc : 0 < c) (hb : 0 < b) :
    Real.sqrt (c * ((c ^ 2)⁻¹ + b⁻¹) / 2) * Real.sqrt (c / ((c ^ 2 + b) / 2)) =
      (Real.sqrt b)⁻¹ := by
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_inv]
  congr 1
  field_simp
  ring

/-- DLMF 19.9.17–19.9.18 (Carlson 1961b): `L ≤ F(φ, k) ≤ √(UL) ≤ (U + L)/2 ≤ U` with
`L = σ⁻¹ arctanh(σ sin φ)`, `σ = √((1 + k²)/2)`, and
`U = ½ arctanh(sin φ) + ½ k⁻¹ arctanh(k sin φ)`, for `0 < k < 1`, `0 ≤ φ < π/2`. In the variable
`θ` the three integrands are `cos θ/√(ab)`, `cos θ (1/a + 1/b)/2` and `2 cos θ/(a + b)` with
`a = cos²θ`, `b = 1 - k² sin²θ`; the bounds follow from AM–GM and Cauchy–Schwarz. -/
@[dlmf 19.9.E17, dlmf 19.9.E18]
theorem incEllIntFk_arctanh_bounds {φ k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ < π / 2) :
    let σ := Real.sqrt ((1 + k ^ 2) / 2)
    let L := σ⁻¹ * Real.artanh (σ * Real.sin φ)
    let U := Real.artanh (Real.sin φ) / 2 + k⁻¹ * Real.artanh (k * Real.sin φ) / 2
    L ≤ (incEllIntFk φ k).re ∧ (incEllIntFk φ k).re ≤ Real.sqrt (U * L) ∧
      Real.sqrt (U * L) ≤ (U + L) / 2 ∧ (U + L) / 2 ≤ U := by
  intro σ L U
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hσ2 : σ ^ 2 = (1 + k ^ 2) / 2 := Real.sq_sqrt (by positivity)
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by positivity)
  have hσ1 : σ < 1 := by nlinarith
  have hs0 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos])
  have hs1 : Real.sin φ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl hφ1
  -- pointwise data on `[0, φ]`
  have hc : ∀ θ ∈ Icc (0 : ℝ) φ, 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hb : ∀ θ : ℝ, 0 < 1 - k ^ 2 * Real.sin θ ^ 2 := fun θ =>
    DLMF.Elliptic.one_sub_mul_sin_sq_pos hk2 θ
  have hsq : ∀ θ : ℝ, 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := fun θ => by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  set A : ℝ → ℝ := fun θ => Real.cos θ * ((1 - Real.sin θ ^ 2)⁻¹ +
    (1 - k ^ 2 * Real.sin θ ^ 2)⁻¹) / 2 with hA
  set G : ℝ → ℝ := fun θ => Real.cos θ / (1 - σ ^ 2 * Real.sin θ ^ 2) with hG
  set Φ : ℝ → ℝ := fun θ => (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹ with hΦ
  have hF : (incEllIntFk φ k).re = ∫ θ in (0 : ℝ)..φ, Φ θ := by
    rw [re_incEllIntFk_ofReal hk2.le, DLMF.Elliptic.Real.incEllIntFm]
    exact intervalIntegral.integral_congr fun θ _ => rpow_neg_half_eq_inv_sqrt (hb θ).le
  have hU : U = ∫ θ in (0 : ℝ)..φ, A θ := by
    have h1 := integral_cos_div_one_sub_sq_mul_sin_sq one_pos hφ0 hφ1 (by linarith)
    have h2 := integral_cos_div_one_sub_sq_mul_sin_sq hk0 hφ0 hφ1 (by nlinarith)
    simp only [one_pow, one_mul, inv_one] at h1
    have hi1 : IntervalIntegrable (fun θ => Real.cos θ / (1 - Real.sin θ ^ 2)) volume 0 φ := by
      refine ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
      intro θ hθ; rw [uIcc_of_le hφ0] at hθ; rw [hsq]; exact pow_ne_zero _ (hc θ hθ).ne'
    have hi2 : IntervalIntegrable (fun θ => Real.cos θ / (1 - k ^ 2 * Real.sin θ ^ 2)) volume 0 φ :=
      (Continuous.div (by fun_prop) (by fun_prop) fun θ => (hb θ).ne').intervalIntegrable _ _
    have : (∫ θ in (0 : ℝ)..φ, A θ) = ((∫ θ in (0 : ℝ)..φ, Real.cos θ / (1 - Real.sin θ ^ 2)) +
        ∫ θ in (0 : ℝ)..φ, Real.cos θ / (1 - k ^ 2 * Real.sin θ ^ 2)) / 2 := by
      rw [← intervalIntegral.integral_add hi1 hi2, ← intervalIntegral.integral_div]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [hA]; ring
    rw [this, h1, h2]
    show Real.artanh (Real.sin φ) / 2 + k⁻¹ * Real.artanh (k * Real.sin φ) / 2 = _
    ring
  have hL : L = ∫ θ in (0 : ℝ)..φ, G θ :=
    (integral_cos_div_one_sub_sq_mul_sin_sq hσ0 hφ0 hφ1 (by nlinarith)).symm
  have hab : ∀ θ ∈ Icc (0 : ℝ) φ, 1 - σ ^ 2 * Real.sin θ ^ 2 =
      ((1 - Real.sin θ ^ 2) + (1 - k ^ 2 * Real.sin θ ^ 2)) / 2 := fun θ _ => by
    rw [hσ2]; ring
  -- pointwise inequalities
  have hGΦ : ∀ θ ∈ Icc (0 : ℝ) φ, G θ ≤ Φ θ := by
    intro θ hθ
    simp only [hG, hΦ]
    rw [hab θ hθ, hsq]
    exact div_avg_sq_add_le_inv_sqrt (hb θ) (hc θ hθ)
  have hGA : ∀ θ ∈ Icc (0 : ℝ) φ, G θ ≤ A θ := by
    intro θ hθ
    simp only [hG, hA]
    rw [hab θ hθ, hsq]
    exact div_avg_le_mul_avg_inv (pow_pos (hc θ hθ) 2) (hb θ) (hc θ hθ).le
  have hAG : ∀ θ ∈ Icc (0 : ℝ) φ, Real.sqrt (A θ) * Real.sqrt (G θ) = Φ θ := by
    intro θ hθ
    simp only [hG, hA, hΦ]
    rw [hab θ hθ, hsq]
    exact sqrt_mul_sqrt_avg_eq_inv_sqrt (hc θ hθ) (hb θ)
  have hG0 : ∀ θ ∈ Icc (0 : ℝ) φ, 0 ≤ G θ := fun θ hθ => by
    simp only [hG]; rw [hab θ hθ]
    exact div_nonneg (hc θ hθ).le (by linarith [hb θ, sq_nonneg (Real.sin θ), Real.sin_sq_le_one θ])
  have hA0 : ∀ θ ∈ Icc (0 : ℝ) φ, 0 ≤ A θ := fun θ hθ => (hG0 θ hθ).trans (hGA θ hθ)
  -- continuity
  have hdenσ : ∀ θ : ℝ, 0 < 1 - σ ^ 2 * Real.sin θ ^ 2 := fun θ => by
    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ)]
  have hGc : Continuous G := Continuous.div (by fun_prop) (by fun_prop) fun θ => (hdenσ θ).ne'
  have hΦc : Continuous Φ :=
    (Continuous.sqrt (by fun_prop)).inv₀ fun θ => (Real.sqrt_pos.2 (hb θ)).ne'
  -- `A` is continuous on `[0, φ]`; use a continuous extension for Cauchy–Schwarz
  have hAc : ContinuousOn A (Icc 0 φ) := by
    refine ContinuousOn.div_const (ContinuousOn.mul (by fun_prop) (ContinuousOn.add ?_ ?_)) _
    · refine ContinuousOn.inv₀ (by fun_prop) fun θ hθ => ?_
      rw [hsq]; exact pow_ne_zero _ (hc θ hθ).ne'
    · exact (Continuous.inv₀ (by fun_prop) fun θ => (hb θ).ne').continuousOn
  obtain ⟨A', hA'c, hA'eq⟩ : ∃ A' : ℝ → ℝ, Continuous A' ∧ EqOn A' A (Icc 0 φ) := by
    refine ⟨IccExtend hφ0 (domRestrict (Icc 0 φ) A), ?_, fun θ hθ => ?_⟩
    · exact continuous_IccExtend_iff.2 (hAc.domRestrict)
    · rw [IccExtend_of_mem hφ0 _ hθ]; rfl
  have hint_eq : ∀ {f g : ℝ → ℝ}, EqOn f g (Icc 0 φ) → ∫ θ in (0 : ℝ)..φ, f θ =
      ∫ θ in (0 : ℝ)..φ, g θ :=
    fun h => intervalIntegral.integral_congr (by rw [uIcc_of_le hφ0]; exact h)
  have hUA' : U = ∫ θ in (0 : ℝ)..φ, A' θ := by rw [hU]; exact (hint_eq hA'eq).symm
  have hcs := sq_integral_sqrt_mul_sqrt_le hφ0 hA'c hGc (fun θ hθ => (hA'eq hθ).symm ▸ hA0 θ hθ) hG0
  have hFeq : (∫ θ in (0 : ℝ)..φ, Real.sqrt (A' θ) * Real.sqrt (G θ)) = (incEllIntFk φ k).re := by
    rw [hF]; exact hint_eq fun θ hθ => by rw [hA'eq hθ]; exact hAG θ hθ
  rw [hFeq, ← hUA', ← hL] at hcs
  have hLF : L ≤ (incEllIntFk φ k).re := by
    rw [hL, hF]
    exact intervalIntegral.integral_mono_on hφ0 (hGc.intervalIntegrable _ _)
      (hΦc.intervalIntegrable _ _) hGΦ
  have hLU : L ≤ U := by
    rw [hL, hUA']
    exact intervalIntegral.integral_mono_on hφ0 (hGc.intervalIntegrable _ _)
      (hA'c.intervalIntegrable _ _) fun θ hθ => (hA'eq hθ).symm ▸ hGA θ hθ
  have hL0 : 0 ≤ L := by rw [hL]; exact intervalIntegral.integral_nonneg hφ0 hG0
  have hF0 : 0 ≤ (incEllIntFk φ k).re := hL0.trans hLF
  have hU0 : 0 ≤ U := hL0.trans hLU
  refine ⟨hLF, ?_, ?_, by linarith⟩
  · rw [← Real.sqrt_sq hF0]; exact Real.sqrt_le_sqrt hcs
  · rw [← Real.sqrt_sq (by linarith : 0 ≤ (U + L) / 2)]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (U - L)])

end DLMF.EllipticIntegrals
