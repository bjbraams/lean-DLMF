/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.LegendreIdentities
public import DLMF.EllipticIntegrals.SpecialCases

/-!
# Derivatives and differential equations of Legendre's integrals (DLMF §19.4)

Complex-modulus forms of DLMF 19.4.1–19.4.9. Here `k'² = 1 - k²`. The complete integrals are
differentiated on the principal domain `{k ≠ 0, 1 - k² ∈ ℂ \ (-∞, 0]}`; the incomplete ones at
a complex amplitude `φ` whose path `[0, φ]` keeps `1 - k² sin²θ` in `ℂ \ (-∞, 0]`
(`legendrePathOK`), with `Δ = (1 - k² sin²φ)^{1/2}`. The real-parameter forms (in `m = k²`) are
the existing `DLMF.Elliptic.Real.hasDerivAt_compEllIntKm`, `Real.hasDerivAt_compEllIntEm`,
`Real.hasDerivAt_compEllIntKm_sq` and `Real.hasDerivAt_compEllIntEm_sq` (tagged 19.4.E1–E2).

All of 19.4.1–19.4.9 are proved: the first relations of 19.4.1, 19.4.2 and 19.4.4–19.4.7 by
differentiation under the integral sign (`p19lR1_hasDerivAt_integral_cpow` for real paths,
`p19lR1_hasDerivAt_path` along the segment `[0, φ]`) together with the closed form of
`∫ Δ⁻³` (`p19lR1_integral_cube`, `p19lR1_path_integral_cube`); the second relations, 19.4.3 and the
differential equations 19.4.8–19.4.9 follow. The hypergeometric equations of the prose (19.4.ii)
follow from 19.4.8–19.4.9.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-- The path condition for Legendre's integrals at amplitude `φ`: `1 - k² sin²θ` stays in
`ℂ \ (-∞, 0]` along the segment `[0, φ]`, so the integrand is holomorphic near the path. -/
def legendrePathOK (φ k : ℂ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, 1 - k ^ 2 * Complex.sin (t * φ) ^ 2 ∈ slitPlane

/-- For a real amplitude the path condition follows from `1 - k² ∈ ℂ \ (-∞, 0]`. -/
theorem legendrePathOK_ofReal {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (φ : ℝ) :
    legendrePathOK φ k := fun t _ => by
  simpa using ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk (t * φ)

/-- The principal domain of `K` and `E` as a differentiable function: `k ≠ 0`, `k² ∉ [1, ∞)`. -/
def compEllIntDomain : Set ℂ := {k | k ≠ 0 ∧ 1 - k ^ 2 ∈ slitPlane}

/-- The indicated domain is open: `IsOpen compEllIntDomain`. -/
theorem isOpen_compEllIntDomain : IsOpen compEllIntDomain := by
  exact (isOpen_ne (x := (0 : ℂ))).inter
    (Complex.isOpen_slitPlane.preimage (by fun_prop : Continuous fun k : ℂ => 1 - k ^ 2))

/-! ### §19.4(i) Derivatives -/

/-- Differentiation under the integral sign: for continuous `w`,
`d/dk ∫₀^b w(θ) (1 - k² sin²θ)^s dθ = ∫₀^b w(θ) s (1 - k² sin²θ)^{s-1} (-2k sin²θ) dθ` on the
principal domain `1 - k² ∈ ℂ \ (-∞, 0]`. -/
lemma p19lR1_hasDerivAt_integral_cpow {w : ℝ → ℂ} (hw : Continuous w) (s : ℂ) (b : ℝ) {k0 : ℂ}
    (hk0 : 1 - k0 ^ 2 ∈ slitPlane) :
    HasDerivAt (fun k : ℂ => ∫ θ in (0 : ℝ)..b, w θ * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ s)
      (∫ θ in (0 : ℝ)..b, w θ * (s * (1 - k0 ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (s - 1) *
        (-(2 * k0 * (Real.sin θ : ℂ) ^ 2)))) k0 := by
  have hU : IsOpen {k : ℂ | 1 - k ^ 2 ∈ slitPlane} :=
    isOpen_slitPlane.preimage (by fun_prop)
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU k0 hk0
  have hball : Metric.closedBall k0 (ε / 2) ⊆ {k : ℂ | 1 - k ^ 2 ∈ slitPlane} :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεU
  have hcontk : ∀ k : ℂ, 1 - k ^ 2 ∈ slitPlane → Continuous fun θ : ℝ =>
      w θ * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ s := fun k hk =>
    hw.mul (Continuous.cpow (by fun_prop) continuous_const fun θ =>
      ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk θ)
  have hcontk' : ∀ k : ℂ, 1 - k ^ 2 ∈ slitPlane → Continuous fun θ : ℝ =>
      w θ * (s * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (s - 1) *
        (-(2 * k * (Real.sin θ : ℂ) ^ 2))) := fun k hk =>
    hw.mul (((continuous_const.mul (Continuous.cpow (by fun_prop) continuous_const fun θ =>
      ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk θ))).mul (by fun_prop))
  -- a uniform bound on the derivative
  obtain ⟨W, hW⟩ := (isCompact_uIcc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
    (hw.norm.continuousOn)
  have hcomp : IsCompact (Metric.closedBall k0 (ε / 2) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℂ × ℝ =>
      ‖s * (1 - p.1 ^ 2 * (p.2 : ℂ)) ^ (s - 1) * (-(2 * p.1 * (p.2 : ℂ)))‖)
      (Metric.closedBall k0 (ε / 2) ×ˢ Icc (0 : ℝ) 1) := by
    refine ContinuousOn.norm ((continuousOn_const.mul
      (ContinuousOn.cpow (by fun_prop) continuousOn_const ?_)).mul (by fun_prop))
    rintro ⟨k, u⟩ ⟨hk, hu⟩
    have := ei19a_one_sub_mul_mem_slitPlane (hball hk) hu.1 hu.2
    simpa using this
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := b) (x₀ := k0) (bound := fun _ => ‖W‖ * M)
    (F := fun k θ => w θ * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ s)
    (F' := fun k θ => w θ * (s * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (s - 1) *
        (-(2 * k * (Real.sin θ : ℂ) ^ 2))))
    (Metric.closedBall_mem_nhds k0 (by linarith : (0 : ℝ) < ε / 2))
    (Filter.eventually_of_mem (hU.mem_nhds hk0) fun k hk => (hcontk k hk).aestronglyMeasurable)
    ((hcontk k0 hk0).intervalIntegrable _ _) ((hcontk' k0 hk0).aestronglyMeasurable) ?_
    intervalIntegrable_const ?_
  · exact hd.2
  · refine Eventually.of_forall fun θ hθ k hk => ?_
    rw [norm_mul]
    have h1 : ‖w θ‖ ≤ ‖W‖ := by
      have := hW θ (uIoc_subset_uIcc hθ)
      rw [norm_norm] at this
      exact this.trans (le_abs_self _)
    have h2 := hM (k, Real.sin θ ^ 2) ⟨hk, sq_nonneg _, Real.sin_sq_le_one θ⟩
    simp only [Real.norm_eq_abs, ofReal_pow] at h2
    have h2' : ‖s * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (s - 1) *
        (-(2 * k * (Real.sin θ : ℂ) ^ 2))‖ ≤ M := (le_abs_self _).trans h2
    exact mul_le_mul h1 h2' (norm_nonneg _) (norm_nonneg _)
  · refine Eventually.of_forall fun θ _ k hk => ?_
    have hb : HasDerivAt (fun k : ℂ => 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)
        (-(2 * k * (Real.sin θ : ℂ) ^ 2)) k := by
      have := ((hasDerivAt_pow 2 k).mul_const ((Real.sin θ : ℂ) ^ 2)).const_sub 1
      convert this using 1; ring
    exact (hb.cpow_const (ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane (hball hk) θ)).const_mul (w θ)

/-- The case `w = 1` of `p19lR1_hasDerivAt_integral_cpow`. -/
lemma p19lR1_hasDerivAt_integral_cpow_one (s : ℂ) (b : ℝ) {k0 : ℂ}
    (hk0 : 1 - k0 ^ 2 ∈ slitPlane) :
    HasDerivAt (fun k : ℂ => ∫ θ in (0 : ℝ)..b, (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ s)
      (∫ θ in (0 : ℝ)..b, s * (1 - k0 ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (s - 1) *
        (-(2 * k0 * (Real.sin θ : ℂ) ^ 2))) k0 := by
  simpa using p19lR1_hasDerivAt_integral_cpow continuous_const s b hk0 (w := fun _ => 1)

/-- If `1 - a ∈ ℂ \ (-∞, 0]`, then `1 - a sin²θ` is bounded away from `0` for real `θ`. -/
theorem p19lR1_exists_norm_lower_gen {a : ℂ} (ha : 1 - a ∈ slitPlane) :
    ∃ δ > 0, ∀ θ : ℝ, δ ≤ ‖1 - a * (Real.sin θ : ℂ) ^ 2‖ := by
  obtain ⟨u0, hu0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    (nonempty_Icc.2 zero_le_one)
    (by fun_prop : Continuous fun u : ℝ => ‖1 - a * (u : ℂ)‖).continuousOn
  refine ⟨‖1 - a * (u0 : ℂ)‖, norm_pos_iff.2 (slitPlane_ne_zero
    (ei19a_one_sub_mul_mem_slitPlane ha hu0.1 hu0.2)), fun θ => ?_⟩
  have := hmin (show Real.sin θ ^ 2 ∈ Icc (0 : ℝ) 1 from ⟨sq_nonneg _, Real.sin_sq_le_one θ⟩)
  simpa using this

/-- DLMF 19.4.1 (first relation): `dK/dk = (E - k'²K)/(k k'²)` on the principal
domain. -/
@[dlmf 19.4.E1]
theorem hasDerivAt_compEllIntKk {k : ℂ} (hk : k ∈ compEllIntDomain) :
    HasDerivAt compEllIntKk
      ((compEllIntEk k - (1 - k ^ 2) * compEllIntKk k) / (k * (1 - k ^ 2))) k := by
  have h := p19lR1_hasDerivAt_integral_cpow_one (-(1 / 2) : ℂ) (π / 2) hk.2
  refine (show compEllIntKk = _ from rfl) ▸ h.congr_deriv ?_
  have hk0 := hk.1
  have hk1 : 1 - k ^ 2 ≠ 0 := slitPlane_ne_zero hk.2
  have hb0 : ∀ θ : ℝ, 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2 ≠ 0 := fun θ =>
    slitPlane_ne_zero (ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk.2 θ)
  have hpt : ∀ θ : ℝ, (-(1 / 2) : ℂ) * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ ((-(1 / 2) : ℂ) - 1) *
      (-(2 * k * (Real.sin θ : ℂ) ^ 2)) = k⁻¹ * ((1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) -
          (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := fun θ => by
    rw [cpow_sub _ _ (hb0 θ), cpow_one]
    have h0 := hb0 θ
    set B := 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2 with hB
    have hks : k ^ 2 * (Real.sin θ : ℂ) ^ 2 = 1 - B := by rw [hB]; ring
    field_simp
    rw [mul_assoc, hks]
  have hc1 : Continuous fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) :=
    Continuous.cpow (by fun_prop) continuous_const fun θ =>
      ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk.2 θ
  have hc2 : Continuous fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) :=
    ((by fun_prop : Continuous fun θ : ℝ => 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2).inv₀ hb0).mul hc1
  simp only [hpt, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub (hc2.intervalIntegrable _ _) (hc1.intervalIntegrable _ _),
    p19lR1_integral_cube hk.2, ← compEllIntKk]
  simp only [Real.sin_pi_div_two, Real.cos_pi_div_two, ofReal_zero, mul_zero, zero_div,
    sub_zero, compEllIntEk]
  push_cast
  field_simp

/-- DLMF 19.4.2 (first relation): `dE/dk = (E - K)/k` on the principal domain. -/
@[dlmf 19.4.E2]
theorem hasDerivAt_compEllIntEk {k : ℂ} (hk : k ∈ compEllIntDomain) :
    HasDerivAt compEllIntEk ((compEllIntEk k - compEllIntKk k) / k) k := by
  have hE : compEllIntEk = fun k : ℂ => ∫ θ in (0 : ℝ)..(π / 2),
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (1 / 2 : ℂ) := funext compEllIntEk_eq_integral
  have h := p19lR1_hasDerivAt_integral_cpow_one (1 / 2 : ℂ) (π / 2) hk.2
  rw [← hE] at h
  refine h.congr_deriv ?_
  have hpt : ∀ θ : ℝ, (1 / 2 : ℂ) * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ ((1 / 2 : ℂ) - 1) *
      (-(2 * k * (Real.sin θ : ℂ) ^ 2)) = (-k) * ((Real.sin θ : ℂ) ^ 2 *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := fun θ => by
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num]; ring
  simp only [hpt, intervalIntegral.integral_const_mul, ← compEllIntDk_eq_integral,
    compEllIntDk_eq hk.1 hk.2]
  have := hk.1
  field_simp
  ring

/-- Nonvanishing under the stated hypotheses: `1 - k ^ 2 ≠ 0`. -/
lemma ei19a_one_sub_sq_ne_zero {k : ℂ} (hk : k ∈ compEllIntDomain) : 1 - k ^ 2 ≠ 0 :=
  slitPlane_ne_zero hk.2

/-- DLMF 19.4.1 (second relation): `d(E - k'²K)/dk = kK`. -/
@[dlmf 19.4.E1]
theorem hasDerivAt_compEllIntEk_sub {k : ℂ} (hk : k ∈ compEllIntDomain) :
    HasDerivAt (fun k => compEllIntEk k - (1 - k ^ 2) * compEllIntKk k) (k * compEllIntKk k) k := by
  have h := (hasDerivAt_compEllIntEk hk).sub
    (((hasDerivAt_pow 2 k).const_sub 1).mul (hasDerivAt_compEllIntKk hk))
  convert h using 1
  have h0 := hk.1
  have h1 := ei19a_one_sub_sq_ne_zero hk
  field_simp
  ring

/-- DLMF 19.4.2 (second relation): `d(E - K)/dk = -kE/k'²`. -/
@[dlmf 19.4.E2]
theorem hasDerivAt_compEllIntEk_sub_compEllIntKk {k : ℂ} (hk : k ∈ compEllIntDomain) :
    HasDerivAt (fun k => compEllIntEk k - compEllIntKk k)
      (-(k * compEllIntEk k) / (1 - k ^ 2)) k := by
  have h := (hasDerivAt_compEllIntEk hk).sub (hasDerivAt_compEllIntKk hk)
  convert h using 1
  have h0 := hk.1
  have h1 := ei19a_one_sub_sq_ne_zero hk
  field_simp
  ring

/-- DLMF 19.4.3: `d²E/dk² = -(1/k) dK/dk = (k'²K - E)/(k²k'²)` on the principal domain. -/
@[dlmf 19.4.E3]
theorem deriv_deriv_compEllIntEk {k : ℂ} (hk : k ∈ compEllIntDomain) :
    deriv (deriv compEllIntEk) k = -(1 / k) * deriv compEllIntKk k ∧
      deriv (deriv compEllIntEk) k =
        ((1 - k ^ 2) * compEllIntKk k - compEllIntEk k) / (k ^ 2 * (1 - k ^ 2)) := by
  have hev : deriv compEllIntEk =ᶠ[𝓝 k] fun k => (compEllIntEk k - compEllIntKk k) / k :=
    Filter.eventually_of_mem (isOpen_compEllIntDomain.mem_nhds hk) fun z hz =>
      (hasDerivAt_compEllIntEk hz).deriv
  have hd : HasDerivAt (fun k => (compEllIntEk k - compEllIntKk k) / k)
      ((-(k * compEllIntEk k) / (1 - k ^ 2) * k - (compEllIntEk k - compEllIntKk k) * 1) /
        k ^ 2) k :=
    (hasDerivAt_compEllIntEk_sub_compEllIntKk hk).div (hasDerivAt_id k) hk.1
  rw [hev.deriv_eq, hd.deriv, (hasDerivAt_compEllIntKk hk).deriv]
  have h0 := hk.1
  have h1 := ei19a_one_sub_sq_ne_zero hk
  constructor <;> (field_simp; ring)

/-- DLMF 19.4.4:
`∂Π(α², k)/∂k = k/(k'²(k² - α²)) (E(k) - k'²Π(α², k))` on the principal domain, for `α² ≠ k²`
with `1 - α² ∈ ℂ \ (-∞, 0]` (no principal value). -/
@[dlmf 19.4.E4]
theorem hasDerivAt_compEllIntPik {α2 k : ℂ} (hk : k ∈ compEllIntDomain)
    (hα : 1 - α2 ∈ slitPlane) (hαk : k ^ 2 ≠ α2) :
    HasDerivAt (fun k => compEllIntPik α2 k) (k / ((1 - k ^ 2) * (k ^ 2 - α2)) *
      (compEllIntEk k - (1 - k ^ 2) * compEllIntPik α2 k)) k := by
  obtain ⟨δ, hδ, hlow⟩ := p19lR1_exists_norm_lower_gen hα
  have ha0 : ∀ θ : ℝ, 1 - α2 * (Real.sin θ : ℂ) ^ 2 ≠ 0 := fun θ =>
    norm_pos_iff.1 (hδ.trans_le (hlow θ))
  have hw : Continuous fun θ : ℝ => (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ :=
    (by fun_prop : Continuous fun θ : ℝ => 1 - α2 * (Real.sin θ : ℂ) ^ 2).inv₀ ha0
  have hPi : ∀ k : ℂ, compEllIntPik α2 k = ∫ θ in (0 : ℝ)..(π / 2),
      (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
    intro k
    rw [compEllIntPik, show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
      p19lR1_incEllIntPik_ofReal hδ (fun t _ => hlow _)]
  have h := p19lR1_hasDerivAt_integral_cpow hw (-(1 / 2) : ℂ) (π / 2) hk.2
  rw [← funext hPi] at h
  refine h.congr_deriv ?_
  have hk0 := hk.1
  have hk1 : 1 - k ^ 2 ≠ 0 := slitPlane_ne_zero hk.2
  have hka : k ^ 2 - α2 ≠ 0 := sub_ne_zero.2 hαk
  have hb0 : ∀ θ : ℝ, 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2 ≠ 0 := fun θ =>
    slitPlane_ne_zero (ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk.2 θ)
  have hpt : ∀ θ : ℝ, (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ * ((-(1 / 2) : ℂ) *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ ((-(1 / 2) : ℂ) - 1) *
      (-(2 * k * (Real.sin θ : ℂ) ^ 2))) = (k / (k ^ 2 - α2)) *
        ((1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) -
          (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
            (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := fun θ => by
    rw [cpow_sub _ _ (hb0 θ), cpow_one]
    have h0 := hb0 θ
    have h1 := ha0 θ
    set B := 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2 with hB
    set A := 1 - α2 * (Real.sin θ : ℂ) ^ 2 with hA
    set P := B ^ (-(1 / 2) : ℂ)
    field_simp
    rw [hA, hB]
    ring
  have hc1 : Continuous fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) :=
    Continuous.cpow (by fun_prop) continuous_const fun θ =>
      ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk.2 θ
  have hc2 : Continuous fun θ : ℝ => (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) :=
    ((by fun_prop : Continuous fun θ : ℝ => 1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2).inv₀ hb0).mul hc1
  simp only [hpt, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub (hc2.intervalIntegrable _ _)
    ((show Continuous fun θ : ℝ => (1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) from hw.mul hc1).intervalIntegrable _ _),
    p19lR1_integral_cube hk.2, ← hPi]
  simp only [Real.sin_pi_div_two, Real.cos_pi_div_two, ofReal_zero, mul_zero, zero_div,
    sub_zero, compEllIntEk]
  push_cast
  field_simp

/-- The condition `1 - k² g(t) ∈ ℂ \ (-∞, 0]` for all `t ∈ [0, 1]` is open in `k`. -/
lemma p19lR1_eventually_path {g : ℝ → ℂ} (hg : Continuous g) {k0 : ℂ}
    (hk0 : ∀ t ∈ Icc (0 : ℝ) 1, 1 - k0 ^ 2 * g t ∈ slitPlane) :
    ∀ᶠ k in 𝓝 k0, ∀ t ∈ Icc (0 : ℝ) 1, 1 - k ^ 2 * g t ∈ slitPlane := by
  refine isCompact_Icc.eventually_forall_of_forall_eventually fun t ht => ?_
  have hc : Continuous fun z : ℂ × ℝ => 1 - z.1 ^ 2 * g z.2 := by fun_prop
  exact hc.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds (hk0 t ht))

/-- Differentiation under the integral sign along `t ∈ [0, 1]`:
`d/dk ∫₀¹ w(t) (1 - k² g(t))^s dt = ∫₀¹ w(t) s (1 - k² g(t))^{s-1} (-2k g(t)) dt`. -/
lemma p19lR1_hasDerivAt_path {g w : ℝ → ℂ} (hg : Continuous g) (hw : ContinuousOn w (Icc 0 1))
    (s : ℂ)
    {k0 : ℂ} (hk0 : ∀ t ∈ Icc (0 : ℝ) 1, 1 - k0 ^ 2 * g t ∈ slitPlane) :
    HasDerivAt (fun k : ℂ => ∫ t in (0 : ℝ)..1, w t * (1 - k ^ 2 * g t) ^ s)
      (∫ t in (0 : ℝ)..1, w t * (s * (1 - k0 ^ 2 * g t) ^ (s - 1) * (-(2 * k0 * g t)))) k0 := by
  obtain ⟨ε, hε, hεU⟩ := Metric.eventually_nhds_iff_ball.1 (p19lR1_eventually_path hg hk0)
  have hball : ∀ k ∈ Metric.closedBall k0 (ε / 2), ∀ t ∈ Icc (0 : ℝ) 1,
      1 - k ^ 2 * g t ∈ slitPlane := fun k hk =>
    hεU k (Metric.closedBall_subset_ball (by linarith) hk)
  have hcomp : IsCompact (Metric.closedBall k0 (ε / 2) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℂ × ℝ =>
      ‖w p.2 * (s * (1 - p.1 ^ 2 * g p.2) ^ (s - 1) * (-(2 * p.1 * g p.2)))‖)
      (Metric.closedBall k0 (ε / 2) ×ˢ Icc (0 : ℝ) 1) := by
    refine ContinuousOn.norm ((hw.comp continuousOn_snd
      fun p (hp : p ∈ Metric.closedBall k0 (ε / 2) ×ˢ Icc (0 : ℝ) 1) => hp.2).mul
      ((continuousOn_const.mul (ContinuousOn.cpow (by fun_prop) continuousOn_const ?_)).mul
        (by fun_prop)))
    rintro ⟨k, u⟩ ⟨hk, hu⟩
    exact hball k hk u hu
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  have hcontk : ∀ k ∈ Metric.closedBall k0 (ε / 2), ContinuousOn (fun t : ℝ =>
      w t * (1 - k ^ 2 * g t) ^ s) (uIcc 0 1) := fun k hk => by
    rw [uIcc_of_le zero_le_one]
    exact hw.mul (ContinuousOn.cpow (by fun_prop) continuousOn_const (hball k hk))
  have hcontk' : ContinuousOn (fun t : ℝ =>
      w t * (s * (1 - k0 ^ 2 * g t) ^ (s - 1) * (-(2 * k0 * g t)))) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact hw.mul ((continuousOn_const.mul (ContinuousOn.cpow (by fun_prop)
      continuousOn_const (hball k0 (Metric.mem_closedBall_self (by linarith))))).mul
        (by fun_prop))
  have hmeas : ∀ {f : ℝ → ℂ}, ContinuousOn f (uIcc 0 1) →
      AEStronglyMeasurable f (volume.restrict (uIoc (0 : ℝ) 1)) := fun hf =>
    (hf.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (x₀ := k0) (bound := fun _ => M)
    (F := fun k t => w t * (1 - k ^ 2 * g t) ^ s)
    (F' := fun k t => w t * (s * (1 - k ^ 2 * g t) ^ (s - 1) * (-(2 * k * g t))))
    (Metric.closedBall_mem_nhds k0 (by linarith : (0 : ℝ) < ε / 2))
    (Filter.eventually_of_mem (Metric.closedBall_mem_nhds k0 (by linarith : (0 : ℝ) < ε / 2))
      fun k hk => hmeas (hcontk k hk))
    ((hcontk k0 (Metric.mem_closedBall_self (by linarith))).intervalIntegrable)
    (hmeas hcontk') ?_ intervalIntegrable_const ?_
  · exact hd.2
  · refine Eventually.of_forall fun t ht k hk => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [← uIcc_of_le zero_le_one]; exact uIoc_subset_uIcc ht
    have := hM (k, t) ⟨hk, ht'⟩
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  · refine Eventually.of_forall fun t ht k hk => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [← uIcc_of_le zero_le_one]; exact uIoc_subset_uIcc ht
    have hb : HasDerivAt (fun k : ℂ => 1 - k ^ 2 * g t) (-(2 * k * g t)) k := by
      have := ((hasDerivAt_pow 2 k).mul_const (g t)).const_sub 1
      convert this using 1; ring
    exact (hb.cpow_const (hball k hk t ht')).const_mul (w t)

/-- `Δ(z) = (1 - k² sin²z)^{1/2}` for complex `z`. -/
noncomputable abbrev p19lR1_Δc (k z : ℂ) : ℂ := (1 - k ^ 2 * Complex.sin z ^ 2) ^ (1 / 2 : ℂ)

/-- `Δ′(z) = -k² sin z cos z/Δ(z)` where `1 - k² sin²z ∈ ℂ \ (-∞, 0]`. -/
lemma p19lR1_hasDerivAt_Δc {k z : ℂ} (hz : 1 - k ^ 2 * Complex.sin z ^ 2 ∈ slitPlane) :
    HasDerivAt (p19lR1_Δc k)
      (-(k ^ 2 * Complex.sin z * Complex.cos z) * (p19lR1_Δc k z)⁻¹) z := by
  have hb : HasDerivAt (fun z : ℂ => 1 - k ^ 2 * Complex.sin z ^ 2)
      (-(k ^ 2 * (2 * Complex.sin z * Complex.cos z))) z := by
    have := (((Complex.hasDerivAt_sin z).pow 2).const_mul (k ^ 2)).const_sub 1
    convert this using 1; ring
  refine (hb.cpow_const hz).congr_deriv ?_
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, cpow_neg]
  ring

/-- `Δ(z) ≠ 0` where `1 - k² sin²z ∈ ℂ \ (-∞, 0]`. -/
lemma p19lR1_Δc_ne_zero {k z : ℂ} (hz : 1 - k ^ 2 * Complex.sin z ^ 2 ∈ slitPlane) :
    p19lR1_Δc k z ≠ 0 := by
  rw [p19lR1_Δc, Ne, cpow_eq_zero_iff]; exact fun h' => slitPlane_ne_zero hz h'.1

/-- The complex-path form of `∫ Δ⁻³`: along the segment `[0, φ]`,
`∫₀¹ φ Δ(tφ)⁻³ dt = (E(φ, k) - k² sin φ cos φ/Δ(φ))/k′²`. -/
lemma p19lR1_path_integral_cube {φ k : ℂ} (hk1 : k ^ 2 ≠ 1) (hφ : legendrePathOK φ k) :
    ∫ t in (0 : ℝ)..1, φ * ((1 - k ^ 2 * Complex.sin (t * φ) ^ 2)⁻¹ *
        (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ))) =
      (incEllIntEk φ k - k ^ 2 * Complex.sin φ * Complex.cos φ / p19lR1_Δc k φ) / (1 - k ^ 2) := by
  have hk1' : 1 - k ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hk1)
  set G : ℂ → ℂ := fun z => Complex.sin z * Complex.cos z / p19lR1_Δc k z with hG
  set G' : ℂ → ℂ := fun z => ((Complex.cos z * Complex.cos z + Complex.sin z * -Complex.sin z) *
      p19lR1_Δc k z - Complex.sin z * Complex.cos z *
        (-(k ^ 2 * Complex.sin z * Complex.cos z) * (p19lR1_Δc k z)⁻¹)) / p19lR1_Δc k z ^ 2
    with hG'
  have hGd : ∀ z : ℂ, 1 - k ^ 2 * Complex.sin z ^ 2 ∈ slitPlane → HasDerivAt G (G' z) z :=
    fun z hz => ((Complex.hasDerivAt_sin z).mul (Complex.hasDerivAt_cos z)).div
      (p19lR1_hasDerivAt_Δc hz) (p19lR1_Δc_ne_zero hz)
  -- the path-composed version
  have hGt : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => G (t * φ)) (G' (t * φ) * φ) t := by
    intro t ht
    have h1 : HasDerivAt (fun z : ℂ => z * φ) φ (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const φ
    exact ((hGd _ (hφ t ht)).comp (t : ℂ) h1).comp_ofReal
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, φ * ((1 - k ^ 2 * Complex.sin (t * φ) ^ 2)⁻¹ *
      (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ))) =
        (φ * p19lR1_Δc k (t * φ) - k ^ 2 * (G' (t * φ) * φ)) / (1 - k ^ 2) := by
    intro t ht
    have hz := hφ t ht
    simp only [hG']
    generalize (t : ℂ) * φ = z at hz ⊢
    have hD0 := p19lR1_Δc_ne_zero hz
    have h2 : p19lR1_Δc k z ^ 2 = 1 - k ^ 2 * Complex.sin z ^ 2 := by
      rw [p19lR1_Δc, sq, ei19c_cpow_half_sq]
    have hsc := Complex.sin_sq_add_cos_sq z
    rw [cpow_neg, ← p19lR1_Δc, ← h2]
    generalize p19lR1_Δc k z = D at hD0 h2 ⊢
    field_simp
    linear_combination (-φ * (D ^ 2 + (1 - k ^ 2 * Complex.sin z ^ 2) +
      k ^ 2 * (Complex.sin z ^ 2 - Complex.cos z ^ 2))) * h2 + φ * k ^ 2 * hsc
  have hG'c : ContinuousOn (fun t : ℝ => G' (t * φ) * φ) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    have hz := hφ t ht
    have hDc : ContinuousAt (p19lR1_Δc k) ((t : ℂ) * φ) := (p19lR1_hasDerivAt_Δc hz).continuousAt
    have hD0 := p19lR1_Δc_ne_zero hz
    have hc : ContinuousAt G' ((t : ℂ) * φ) := by
      simp only [hG']
      exact (((by fun_prop : ContinuousAt (fun z : ℂ => Complex.cos z * Complex.cos z +
        Complex.sin z * -Complex.sin z) _).mul hDc).sub
        ((by fun_prop : ContinuousAt (fun z : ℂ => Complex.sin z * Complex.cos z) _).mul
          ((by fun_prop : ContinuousAt (fun z : ℂ => -(k ^ 2 * Complex.sin z * Complex.cos z)) _).mul
            (hDc.inv₀ hD0)))).div (hDc.pow 2) (pow_ne_zero 2 hD0)
    exact ((hc.comp (f := fun t : ℝ => (t : ℂ) * φ) (by fun_prop)).mul
      continuousAt_const).continuousWithinAt
  have hΔc : ContinuousOn (fun t : ℝ => φ * p19lR1_Δc k (t * φ)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul (ContinuousOn.cpow (by fun_prop) continuousOn_const hφ)
  rw [intervalIntegral.integral_congr (fun t ht => hpt t (by rwa [uIcc_of_le zero_le_one] at ht)),
    intervalIntegral.integral_div, intervalIntegral.integral_sub hΔc.intervalIntegrable
      (hG'c.intervalIntegrable.const_mul _),
    intervalIntegral.integral_const_mul (k ^ 2) (fun x : ℝ => G' (x * φ) * φ),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hGt t (by rwa [uIcc_of_le zero_le_one] at ht)) hG'c.intervalIntegrable]
  simp only [hG, incEllIntEk, ei19a_segmentIntegral, ofReal_one, one_mul, ofReal_zero, zero_mul,
    Complex.sin_zero, zero_mul, zero_div, sub_zero]
  ring

/-- DLMF 19.4.5:
`∂F(φ, k)/∂k = (E(φ, k) - k'²F(φ, k))/(k k'²) - k sin φ cos φ/(k'² Δ)`, `Δ = √(1 - k² sin²φ)`,
for `k ≠ 0`, `k² ≠ 1` and a path `[0, φ]` satisfying `legendrePathOK`. -/
@[dlmf 19.4.E5]
theorem hasDerivAt_incEllIntFk {φ k : ℂ} (hk0 : k ≠ 0) (hk1 : k ^ 2 ≠ 1)
    (hφ : legendrePathOK φ k) :
    HasDerivAt (fun k => incEllIntFk φ k)
      ((incEllIntEk φ k - (1 - k ^ 2) * incEllIntFk φ k) / (k * (1 - k ^ 2)) -
        k * Complex.sin φ * Complex.cos φ /
          ((1 - k ^ 2) * (1 - k ^ 2 * Complex.sin φ ^ 2) ^ (1 / 2 : ℂ))) k := by
  have hk1' : 1 - k ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hk1)
  have hg : Continuous fun t : ℝ => Complex.sin (t * φ) ^ 2 := by fun_prop
  have h := p19lR1_hasDerivAt_path hg continuousOn_const (-(1 / 2) : ℂ) (w := fun _ => φ) hφ
  refine h.congr_deriv ?_
  have hpt : ∀ t ∈ uIcc (0 : ℝ) 1, φ * ((-(1 / 2) : ℂ) *
      (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ ((-(1 / 2) : ℂ) - 1) *
      (-(2 * k * Complex.sin (t * φ) ^ 2))) = k⁻¹ * (φ * ((1 - k ^ 2 * Complex.sin (t * φ) ^ 2)⁻¹ *
        (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ))) -
          φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h0 := slitPlane_ne_zero (hφ t ht)
    rw [cpow_sub _ _ h0, cpow_one]
    generalize Complex.sin ((t : ℂ) * φ) = S at h0 ⊢
    set B := 1 - k ^ 2 * S ^ 2 with hB
    have hks : k ^ 2 * S ^ 2 = 1 - B := by rw [hB]; ring
    field_simp
    linear_combination (-(φ * B ^ (-(1 / 2) : ℂ))) * hks
  have hc1 : ContinuousOn (fun t : ℝ => φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ)))
      (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul (ContinuousOn.cpow (by fun_prop) continuousOn_const hφ)
  have hc2 : ContinuousOn (fun t : ℝ => φ * ((1 - k ^ 2 * Complex.sin (t * φ) ^ 2)⁻¹ *
      (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ)))) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul (((by fun_prop : Continuous fun t : ℝ =>
      1 - k ^ 2 * Complex.sin (t * φ) ^ 2).continuousOn.inv₀ fun t ht =>
        slitPlane_ne_zero (hφ t ht)).mul (ContinuousOn.cpow (by fun_prop) continuousOn_const hφ))
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hc2.intervalIntegrable hc1.intervalIntegrable,
    p19lR1_path_integral_cube hk1 hφ]
  have hF : incEllIntFk φ k = ∫ t in (0 : ℝ)..1,
      φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ)) := rfl
  rw [← hF]
  field_simp
  ring

/-- DLMF 19.4.6: `∂E(φ, k)/∂k = (E(φ, k) - F(φ, k))/k` for `k ≠ 0` and a path
satisfying `legendrePathOK`. -/
@[dlmf 19.4.E6]
theorem hasDerivAt_incEllIntEk {φ k : ℂ} (hk0 : k ≠ 0) (hφ : legendrePathOK φ k) :
    HasDerivAt (fun k => incEllIntEk φ k) ((incEllIntEk φ k - incEllIntFk φ k) / k) k := by
  have hg : Continuous fun t : ℝ => Complex.sin (t * φ) ^ 2 := by fun_prop
  have h := p19lR1_hasDerivAt_path hg continuousOn_const (1 / 2 : ℂ) (w := fun _ => φ) hφ
  refine h.congr_deriv ?_
  have hF : IntervalIntegrable
      (fun t : ℝ => φ * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul (ContinuousOn.cpow (by fun_prop) continuousOn_const hφ)
  have hpt : ∀ t : ℝ, φ * ((1 / 2 : ℂ) * (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ ((1 / 2 : ℂ) - 1) *
      (-(2 * k * Complex.sin (t * φ) ^ 2))) = (-k) * (φ * (Complex.sin (t * φ) ^ 2 *
        (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ)))) := fun t => by
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num]; ring
  simp only [hpt, intervalIntegral.integral_const_mul]
  have hD := incEllIntDk_eq hk0 hF
  rw [incEllIntDk, ei19a_segmentIntegral, intervalIntegral.integral_const_mul] at hD
  rw [hD]
  field_simp
  ring

/-- DLMF 19.4.7:
`∂Π(φ, α², k)/∂k = k/(k'²(k² - α²)) (E(φ, k) - k'²Π(φ, α², k) - k² sin φ cos φ/Δ)`, for `k ≠ 0`,
`k² ≠ 1`, `k² ≠ α²`, a path satisfying `legendrePathOK` on which `1 - α² sin²θ ≠ 0`. -/
@[dlmf 19.4.E7]
theorem hasDerivAt_incEllIntPik {φ α2 k : ℂ} (hk0 : k ≠ 0) (hk1 : k ^ 2 ≠ 1) (hαk : k ^ 2 ≠ α2)
    (hφ : legendrePathOK φ k) (hα : ∀ t ∈ Icc (0 : ℝ) 1, 1 - α2 * Complex.sin (t * φ) ^ 2 ≠ 0) :
    HasDerivAt (fun k => incEllIntPik φ α2 k) (k / ((1 - k ^ 2) * (k ^ 2 - α2)) *
      (incEllIntEk φ k - (1 - k ^ 2) * incEllIntPik φ α2 k -
        k ^ 2 * Complex.sin φ * Complex.cos φ /
          (1 - k ^ 2 * Complex.sin φ ^ 2) ^ (1 / 2 : ℂ))) k := by
  have hk1' : 1 - k ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hk1)
  have hka : k ^ 2 - α2 ≠ 0 := sub_ne_zero.2 hαk
  have hAc : Continuous fun t : ℝ => ‖1 - α2 * Complex.sin (t * φ) ^ 2‖ := by fun_prop
  obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    (nonempty_Icc.2 zero_le_one) hAc.continuousOn
  have hδ : 0 < ‖1 - α2 * Complex.sin (t0 * φ) ^ 2‖ := norm_pos_iff.2 (hα t0 ht0)
  have hPi : ∀ k : ℂ, incEllIntPik φ α2 k = ∫ t in (0 : ℝ)..1,
      φ * ((1 - α2 * Complex.sin (t * φ) ^ 2)⁻¹ *
        (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ))) := fun k => by
    rw [incEllIntPik_eq_segmentIntegral hδ (fun t ht => hmin ht), ei19a_segmentIntegral]
  have hw : ContinuousOn (fun t : ℝ => φ * (1 - α2 * Complex.sin (t * φ) ^ 2)⁻¹) (Icc 0 1) :=
    continuousOn_const.mul ((by fun_prop : Continuous fun t : ℝ =>
      1 - α2 * Complex.sin (t * φ) ^ 2).continuousOn.inv₀ hα)
  have hg : Continuous fun t : ℝ => Complex.sin (t * φ) ^ 2 := by fun_prop
  have h := p19lR1_hasDerivAt_path hg hw (-(1 / 2) : ℂ) hφ
  simp only [mul_assoc] at h
  rw [← funext hPi] at h
  refine h.congr_deriv ?_
  have hpt : ∀ t ∈ uIcc (0 : ℝ) 1, φ * ((1 - α2 * Complex.sin (t * φ) ^ 2)⁻¹ * ((-(1 / 2) : ℂ) *
      ((1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ ((-(1 / 2) : ℂ) - 1) *
      (-(2 * (k * Complex.sin (t * φ) ^ 2)))))) = (k / (k ^ 2 - α2)) *
        (φ * ((1 - k ^ 2 * Complex.sin (t * φ) ^ 2)⁻¹ *
          (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ))) -
          φ * ((1 - α2 * Complex.sin (t * φ) ^ 2)⁻¹ *
            (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ)))) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h0 := slitPlane_ne_zero (hφ t ht)
    have h1 := hα t ht
    rw [cpow_sub _ _ h0, cpow_one]
    generalize Complex.sin ((t : ℂ) * φ) = S at h0 h1 ⊢
    set B := 1 - k ^ 2 * S ^ 2 with hB
    set A := 1 - α2 * S ^ 2 with hA
    set P := B ^ (-(1 / 2) : ℂ)
    field_simp
    rw [hA, hB]
    ring
  have hc1 : ContinuousOn (fun t : ℝ => φ * ((1 - α2 * Complex.sin (t * φ) ^ 2)⁻¹ *
      (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ)))) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    simp only [← mul_assoc]
    exact hw.mul (ContinuousOn.cpow (by fun_prop) continuousOn_const hφ)
  have hc2 : ContinuousOn (fun t : ℝ => φ * ((1 - k ^ 2 * Complex.sin (t * φ) ^ 2)⁻¹ *
      (1 - k ^ 2 * Complex.sin (t * φ) ^ 2) ^ (-(1 / 2 : ℂ)))) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul (((by fun_prop : Continuous fun t : ℝ =>
      1 - k ^ 2 * Complex.sin (t * φ) ^ 2).continuousOn.inv₀ fun t ht =>
        slitPlane_ne_zero (hφ t ht)).mul (ContinuousOn.cpow (by fun_prop) continuousOn_const hφ))
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hc2.intervalIntegrable hc1.intervalIntegrable,
    p19lR1_path_integral_cube hk1 hφ, ← hPi]
  field_simp
  ring

/-! ### §19.4(ii) Differential equations -/

/-- The hypotheses `k ≠ 0`, `k² ≠ 1` and `legendrePathOK φ k` hold near `k`. -/
lemma p19lR1_eventually_good {φ k : ℂ} (hk0 : k ≠ 0) (hk1 : k ^ 2 ≠ 1)
    (hφ : legendrePathOK φ k) :
    ∀ᶠ z in 𝓝 k, z ≠ 0 ∧ z ^ 2 ≠ 1 ∧ legendrePathOK φ z := by
  have hg : Continuous fun t : ℝ => Complex.sin (t * φ) ^ 2 := by fun_prop
  filter_upwards [isOpen_ne.mem_nhds hk0,
    (isOpen_ne.preimage (continuous_pow 2)).mem_nhds (show k ∈ (fun z : ℂ => z ^ 2) ⁻¹' {x | x ≠ 1} from hk1),
    p19lR1_eventually_path hg hφ] with z h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- DLMF 19.4.8: with `D_k = ∂/∂k`,
`(k k'² D_k² + (1 - 3k²) D_k - k) F(φ, k) = -k sin φ cos φ/(1 - k² sin²φ)^{3/2}`, for `k ≠ 0`,
`k² ≠ 1` and a path satisfying `legendrePathOK`. -/
@[dlmf 19.4.E8]
theorem incEllIntFk_ode {φ k : ℂ} (hk0 : k ≠ 0) (hk1 : k ^ 2 ≠ 1) (hφ : legendrePathOK φ k) :
    k * (1 - k ^ 2) * deriv (deriv fun k => incEllIntFk φ k) k +
        (1 - 3 * k ^ 2) * deriv (fun k => incEllIntFk φ k) k - k * incEllIntFk φ k =
      -(k * Complex.sin φ * Complex.cos φ) / (1 - k ^ 2 * Complex.sin φ ^ 2) ^ (3 / 2 : ℂ) := by
  have hev : deriv (fun k => incEllIntFk φ k) =ᶠ[𝓝 k]
      fun k => (incEllIntEk φ k - (1 - k ^ 2) * incEllIntFk φ k) / (k * (1 - k ^ 2)) -
        k * Complex.sin φ * Complex.cos φ /
          ((1 - k ^ 2) * (1 - k ^ 2 * Complex.sin φ ^ 2) ^ (1 / 2 : ℂ)) := by
    filter_upwards [p19lR1_eventually_good hk0 hk1 hφ] with z hz
    exact (hasDerivAt_incEllIntFk hz.1 hz.2.1 hz.2.2).deriv
  have hk1' : 1 - k ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hk1)
  have hb : 1 - k ^ 2 * Complex.sin φ ^ 2 ∈ slitPlane := by
    have := hφ 1 ⟨zero_le_one, le_rfl⟩
    simpa using this
  have hb0 := slitPlane_ne_zero hb
  have hE := hasDerivAt_incEllIntEk hk0 hφ
  have hF := hasDerivAt_incEllIntFk hk0 hk1 hφ
  set S := Complex.sin φ
  set C := Complex.cos φ
  have hΔ : HasDerivAt (fun z : ℂ => (1 - z ^ 2 * S ^ 2) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (1 - k ^ 2 * S ^ 2) ^ ((1 / 2 : ℂ) - 1) * (-(2 * k * S ^ 2))) k := by
    have h1 : HasDerivAt (fun z : ℂ => 1 - z ^ 2 * S ^ 2) (-(2 * k * S ^ 2)) k := by
      have := ((hasDerivAt_pow 2 k).mul_const (S ^ 2)).const_sub 1
      convert this using 1; ring
    exact h1.cpow_const hb
  have hD0 : (1 - k ^ 2 * S ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h' => hb0 h'.1
  have hp : HasDerivAt (fun z : ℂ => 1 - z ^ 2) (-(2 * k)) k := by
    have := (hasDerivAt_pow 2 k).const_sub 1
    convert this using 1; ring
  have hd : HasDerivAt (fun z => (incEllIntEk φ z - (1 - z ^ 2) * incEllIntFk φ z) /
      (z * (1 - z ^ 2)) - z * S * C / ((1 - z ^ 2) * (1 - z ^ 2 * S ^ 2) ^ (1 / 2 : ℂ))) _ k :=
    ((hE.sub (hp.mul hF)).div ((hasDerivAt_id k).mul hp) (mul_ne_zero hk0 hk1')).sub
      ((((hasDerivAt_id k).mul_const S).mul_const C).div (hp.mul hΔ) (mul_ne_zero hk1' hD0))
  rw [hev.deriv_eq, hd.deriv, hF.deriv]
  have h2 : (1 - k ^ 2 * S ^ 2) ^ (1 / 2 : ℂ) * (1 - k ^ 2 * S ^ 2) ^ (1 / 2 : ℂ) =
      1 - k ^ 2 * S ^ 2 := ei19c_cpow_half_sq _
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, cpow_neg,
    show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, cpow_add _ _ hb0, cpow_one]
  generalize (1 - k ^ 2 * S ^ 2) ^ (1 / 2 : ℂ) = D at hD0 h2 ⊢
  simp only [Pi.sub_apply, Pi.mul_apply, id]
  rw [← h2]
  field_simp
  linear_combination (-(S * C * k ^ 2 * (1 - k ^ 2))) * h2

/-- DLMF 19.4.9:
`(k k'² D_k² + k'² D_k + k) E(φ, k) = k sin φ cos φ/√(1 - k² sin²φ)`, for `k ≠ 0`, `k² ≠ 1` and a
path satisfying `legendrePathOK`. -/
@[dlmf 19.4.E9]
theorem incEllIntEk_ode {φ k : ℂ} (hk0 : k ≠ 0) (hk1 : k ^ 2 ≠ 1) (hφ : legendrePathOK φ k) :
    k * (1 - k ^ 2) * deriv (deriv fun k => incEllIntEk φ k) k +
        (1 - k ^ 2) * deriv (fun k => incEllIntEk φ k) k + k * incEllIntEk φ k =
      k * Complex.sin φ * Complex.cos φ / (1 - k ^ 2 * Complex.sin φ ^ 2) ^ (1 / 2 : ℂ) := by
  have hev : deriv (fun k => incEllIntEk φ k) =ᶠ[𝓝 k]
      fun k => (incEllIntEk φ k - incEllIntFk φ k) / k := by
    filter_upwards [p19lR1_eventually_good hk0 hk1 hφ] with z hz
    exact (hasDerivAt_incEllIntEk hz.1 hz.2.2).deriv
  have hd : HasDerivAt (fun k => (incEllIntEk φ k - incEllIntFk φ k) / k) _ k :=
    ((hasDerivAt_incEllIntEk hk0 hφ).sub (hasDerivAt_incEllIntFk hk0 hk1 hφ)).div
      (hasDerivAt_id k) hk0
  rw [hev.deriv_eq, hd.deriv, (hasDerivAt_incEllIntEk hk0 hφ).deriv]
  have hk1' : 1 - k ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hk1)
  have hD : (1 - k ^ 2 * Complex.sin φ ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    have := hφ 1 ⟨zero_le_one, le_rfl⟩
    simp only [ofReal_one, one_mul] at this
    rw [Ne, cpow_eq_zero_iff]; exact fun h' => slitPlane_ne_zero this h'.1

  simp only [Pi.sub_apply]
  field_simp
  ring

/-- DLMF §19.4(ii) (prose): at `φ = π/2`, 19.4.8 and 19.4.9 become the hypergeometric equations
(15.10.1, in the variable `k²`) of `K` and `E`:
`k k'² K'' + (1 - 3k²) K' - kK = 0` and `k k'² E'' + k'² E' + kE = 0` on the principal domain
(from 19.4.8–19.4.9). -/
@[dlmf 19.4.ii]
theorem compEllIntKk_compEllIntEk_ode {k : ℂ} (hk : k ∈ compEllIntDomain) :
    k * (1 - k ^ 2) * deriv (deriv compEllIntKk) k + (1 - 3 * k ^ 2) * deriv compEllIntKk k -
        k * compEllIntKk k = 0 ∧
      k * (1 - k ^ 2) * deriv (deriv compEllIntEk) k + (1 - k ^ 2) * deriv compEllIntEk k +
        k * compEllIntEk k = 0 := by
  have hk1 : k ^ 2 ≠ 1 := fun h => ei19a_one_sub_sq_ne_zero hk (by rw [h]; ring)
  have hp : legendrePathOK (π / 2) k := by
    have := legendrePathOK_ofReal hk.2 (π / 2)
    simpa using this
  have hcos : Complex.cos (π / 2) = 0 := by
    rw [show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      Real.cos_pi_div_two, ofReal_zero]
  have hK : compEllIntKk = fun k => incEllIntFk (π / 2) k := funext compEllIntKk_eq_incEllIntFk
  have hE : compEllIntEk = fun k => incEllIntEk (π / 2) k := rfl
  constructor
  · have h := incEllIntFk_ode hk.1 hk1 hp
    rw [hcos] at h
    rw [hK]
    simpa using h
  · have h := incEllIntEk_ode hk.1 hk1 hp
    rw [hcos] at h
    rw [hE]
    simpa using h

end DLMF.EllipticIntegrals
