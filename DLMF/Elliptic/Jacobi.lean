/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Complete

/-!
# Incomplete elliptic integrals and Jacobi's elliptic functions (Temme §§12.2–12.3)

For a real parameter `m < 1` (`m = k²`), Legendre's incomplete integrals
`F(φ|m) = ∫₀^φ (1 - m sin²θ)^{-1/2} dθ` and `E(φ|m) = ∫₀^φ (1 - m sin²θ)^{1/2} dθ` are odd
and quasi-periodic, `F(φ + π|m) = F(φ|m) + 2K(m)`. Since `∂F/∂φ > 0` and `F(nπ|m) = 2nK(m)`,
`φ ↦ F(φ|m)` is an order isomorphism of `ℝ`; its inverse is Jacobi's amplitude `am(u|m)`
(Temme (12.21)–(12.22)), and `sn = sin ∘ am`, `cn = cos ∘ am`, `dn = (1 - m sn²)^{1/2}`. The
inverse function theorem gives `am' = dn` and the derivatives of DLMF 22.13.1–22.13.3.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

noncomputable section

namespace DLMF.Elliptic

/-- Legendre's incomplete integral of the first kind `F(φ|m) = ∫₀^φ (1 - m sin²θ)^{-1/2} dθ`
(DLMF 19.2.4, Temme (12.15)). -/
@[dlmf 19.2.E4]
def Real.incEllIntFm (φ m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..φ, (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)

/-- Legendre's incomplete integral of the second kind `E(φ|m) = ∫₀^φ (1 - m sin²θ)^{1/2} dθ`
(DLMF 19.2.5, Temme (12.16)). -/
@[dlmf 19.2.E5]
def Real.incEllIntEm (φ m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..φ, (1 - m * sin θ ^ 2) ^ (1 / 2 : ℝ)

/-- The integrand `(1 - m sin²θ)^p` is `π`-periodic and even, so its integral over a period is
twice the integral over `[0, π/2]`. -/
lemma integral_period {m : ℝ} (hm : m < 1) (p : ℝ) :
    ∫ θ in (0 : ℝ)..π, (1 - m * sin θ ^ 2) ^ p =
      2 * ∫ θ in (0 : ℝ)..(π / 2), (1 - m * sin θ ^ 2) ^ p := by
  have hc := continuous_one_sub_mul_sin_sq_rpow hm p
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ => (1 - m * sin θ ^ 2) ^ p) (a := 0) (b := π / 2) π
  simp only [sin_pi_sub, sub_zero, show π - π / 2 = π / 2 by ring] at h
  rw [← h]; ring

/-- Quasi-periodicity of the incomplete integrals in the amplitude. -/
lemma integral_add_pi {m : ℝ} (hm : m < 1) (p φ : ℝ) :
    ∫ θ in (0 : ℝ)..(φ + π), (1 - m * sin θ ^ 2) ^ p =
      (∫ θ in (0 : ℝ)..φ, (1 - m * sin θ ^ 2) ^ p) +
        2 * ∫ θ in (0 : ℝ)..(π / 2), (1 - m * sin θ ^ 2) ^ p := by
  have hc := continuous_one_sub_mul_sin_sq_rpow hm p
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), integral_period hm]
  have h := intervalIntegral.integral_comp_add_right
    (fun θ => (1 - m * sin θ ^ 2) ^ p) (a := 0) (b := φ) π
  simp only [sin_add_pi, neg_sq, zero_add] at h
  rw [← h, add_comm]

/-- `F(φ + π|m) = F(φ|m) + 2K(m)` (DLMF §19.2(ii)). -/
theorem Real.incEllIntFm_add_pi {m : ℝ} (hm : m < 1) (φ : ℝ) :
    Real.incEllIntFm (φ + π) m = Real.incEllIntFm φ m + 2 * Real.compEllIntKm m := by
  unfold Real.incEllIntFm Real.compEllIntKm; exact integral_add_pi hm _ φ

/-- `E(φ + π|m) = E(φ|m) + 2E(m)` (DLMF §19.2(ii)). -/
theorem Real.incEllIntEm_add_pi {m : ℝ} (hm : m < 1) (φ : ℝ) :
    Real.incEllIntEm (φ + π) m = Real.incEllIntEm φ m + 2 * Real.compEllIntEm m := by
  unfold Real.incEllIntEm Real.compEllIntEm; exact integral_add_pi hm _ φ

/-- `F(π/2|m) = K(m)`. -/
theorem Real.incEllIntFm_pi_div_two (m : ℝ) :
    Real.incEllIntFm (π / 2) m = Real.compEllIntKm m := rfl

/-- `E(π/2|m) = E(m)`. -/
theorem Real.incEllIntEm_pi_div_two (m : ℝ) :
    Real.incEllIntEm (π / 2) m = Real.compEllIntEm m := rfl

/-- `F(-φ|m) = -F(φ|m)`. -/
theorem Real.incEllIntFm_neg (φ m : ℝ) : Real.incEllIntFm (-φ) m = -Real.incEllIntFm φ m := by
  have h : ∫ θ in (0 : ℝ)..(-φ), (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) =
      ∫ θ in (0 : ℝ)..(-φ), (1 - m * sin (-θ) ^ 2) ^ (-(1 / 2) : ℝ) := by
    simp only [sin_neg, neg_sq]
  rw [Real.incEllIntFm, Real.incEllIntFm, h,
    intervalIntegral.integral_comp_neg (fun θ => (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)), neg_neg,
    neg_zero,
    intervalIntegral.integral_symm]

/-- `F(φ|0) = φ`. -/
theorem Real.incEllIntFm_zero_param (φ : ℝ) : Real.incEllIntFm φ 0 = φ := by simp [Real.incEllIntFm]

/-- `∂F/∂φ = (1 - m sin²φ)^{-1/2}`. -/
theorem Real.hasDerivAt_incEllIntFm {m : ℝ} (hm : m < 1) (φ : ℝ) :
    HasDerivAt (fun φ => Real.incEllIntFm φ m) ((1 - m * sin φ ^ 2) ^ (-(1 / 2) : ℝ)) φ :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
    ((continuous_one_sub_mul_sin_sq_rpow hm _).stronglyMeasurableAtFilter _ _)
    (continuous_one_sub_mul_sin_sq_rpow hm _).continuousAt

/-- `∂E/∂φ = (1 - m sin²φ)^{1/2}`. -/
theorem Real.hasDerivAt_incEllIntEm {m : ℝ} (hm : m < 1) (φ : ℝ) :
    HasDerivAt (fun φ => Real.incEllIntEm φ m) ((1 - m * sin φ ^ 2) ^ (1 / 2 : ℝ)) φ :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
    ((continuous_one_sub_mul_sin_sq_rpow hm _).stronglyMeasurableAtFilter _ _)
    (continuous_one_sub_mul_sin_sq_rpow hm _).continuousAt

/-- `φ ↦ F(φ|m)` is strictly increasing for `m < 1`. -/
lemma Real.strictMono_incEllIntFm {m : ℝ} (hm : m < 1) : StrictMono fun φ => Real.incEllIntFm φ m :=
  strictMono_of_deriv_pos fun φ => by
    rw [(Real.hasDerivAt_incEllIntFm hm φ).deriv]
    exact rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm φ) _

/-- `φ ↦ F(φ|m)` maps `ℝ` onto `ℝ` for `m < 1`. -/
lemma Real.surjective_incEllIntFm {m : ℝ} (hm : m < 1) :
    Function.Surjective fun φ => Real.incEllIntFm φ m := by
  have hcont : Continuous fun φ => Real.incEllIntFm φ m :=
    continuous_iff_continuousAt.mpr fun φ => (Real.hasDerivAt_incEllIntFm hm φ).continuousAt
  have hK : 0 < Real.compEllIntKm m := by
    rw [Real.compEllIntKm]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
      (fun θ _ => rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm θ) _) (by positivity)
  -- `F(nπ) = 2nK`
  have hnat : ∀ n : ℕ, Real.incEllIntFm (n * π) m = 2 * n * Real.compEllIntKm m := by
    intro n
    induction n with
    | zero => simp [Real.incEllIntFm]
    | succ n ih => push_cast; rw [add_mul, one_mul, Real.incEllIntFm_add_pi hm, ih]; ring
  have hmono := Real.strictMono_incEllIntFm hm
  refine hcont.surjective ?_ ?_
  · refine tendsto_atTop_atTop.mpr fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (b / (2 * Real.compEllIntKm m))
    refine ⟨n * π, fun φ hφ => ?_⟩
    have := hmono.monotone hφ
    rw [hnat] at this
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith
  · refine tendsto_atBot_atBot.mpr fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (-b / (2 * Real.compEllIntKm m))
    refine ⟨-(n * π), fun φ hφ => ?_⟩
    have := hmono.monotone hφ
    rw [Real.incEllIntFm_neg, hnat] at this
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith

/-- For `m < 1`, `φ ↦ F(φ|m)` as an order isomorphism of `ℝ`. -/
def Real.incEllIntFmOrderIso {m : ℝ} (hm : m < 1) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ (Real.strictMono_incEllIntFm hm)
      (Real.surjective_incEllIntFm hm)

/-- Jacobi's amplitude `am(u|m)`, the inverse of `φ ↦ F(φ|m)` for `m < 1` (Temme (12.21),
DLMF §22.16(i)); it is set to `u` for `m ≥ 1`. -/
def Real.jacobiAmm (u m : ℝ) : ℝ := if h : m < 1 then (Real.incEllIntFmOrderIso h).symm u else u

/-- `F(am(u|m)|m) = u`. -/
@[dlmf 22.16.E11]
theorem Real.incEllIntFm_jacobiAmm {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.incEllIntFm (Real.jacobiAmm u m) m = u := by
  simp only [Real.jacobiAmm, hm, ↓reduceDIte]
  exact (Real.incEllIntFmOrderIso hm).apply_symm_apply u

/-- `am(F(φ|m)|m) = φ`. -/
theorem Real.jacobiAmm_incEllIntFm {m : ℝ} (hm : m < 1) (φ : ℝ) :
    Real.jacobiAmm (Real.incEllIntFm φ m) m = φ := by
  simp only [Real.jacobiAmm, hm, ↓reduceDIte]
  exact (Real.incEllIntFmOrderIso hm).symm_apply_apply φ

/-- The amplitude is continuous. -/
lemma Real.continuous_jacobiAmm {m : ℝ} (hm : m < 1) : Continuous fun u => Real.jacobiAmm u m := by
  simp only [Real.jacobiAmm, hm, ↓reduceDIte]
  exact (Real.incEllIntFmOrderIso hm).symm.continuous

/-- `d am/du = dn(u|m) = (1 - m sin² am)^{1/2}`. -/
@[dlmf 22.16.i]
theorem Real.hasDerivAt_jacobiAmm {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiAmm u m)
      ((1 - m * sin (Real.jacobiAmm u m) ^ 2) ^ (1 / 2 : ℝ)) u := by
  have hpos := one_sub_mul_sin_sq_pos hm (Real.jacobiAmm u m)
  have h := HasDerivAt.of_local_left_inverse (f := fun φ => Real.incEllIntFm φ m)
    (Real.continuous_jacobiAmm hm).continuousAt
    (Real.hasDerivAt_incEllIntFm hm (Real.jacobiAmm u m))
    (rpow_pos_of_pos hpos _).ne' (Eventually.of_forall fun y => Real.incEllIntFm_jacobiAmm hm y)
  rwa [rpow_neg hpos.le, inv_inv] at h

/-- `am(0|m) = 0`. -/
theorem Real.jacobiAmm_zero {m : ℝ} (hm : m < 1) : Real.jacobiAmm 0 m = 0 := by
  simpa [Real.incEllIntFm] using Real.jacobiAmm_incEllIntFm hm 0

/-- `am(K|m) = π/2`. -/
theorem Real.jacobiAmm_compEllIntKm {m : ℝ} (hm : m < 1) :
    Real.jacobiAmm (Real.compEllIntKm m) m = π / 2 := by
  rw [← Real.incEllIntFm_pi_div_two, Real.jacobiAmm_incEllIntFm hm]

/-- `am(u + 2K|m) = am(u|m) + π`. -/
@[dlmf 22.16.E2]
theorem Real.jacobiAmm_add_two_compEllIntKm {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiAmm (u + 2 * Real.compEllIntKm m) m = Real.jacobiAmm u m + π := by
  conv_lhs => rw [← Real.incEllIntFm_jacobiAmm hm u, ← Real.incEllIntFm_add_pi hm]
  exact Real.jacobiAmm_incEllIntFm hm _

/-- `am(-u|m) = -am(u|m)`. -/
theorem Real.jacobiAmm_neg {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiAmm (-u) m = -Real.jacobiAmm u m := by
  conv_lhs => rw [← Real.incEllIntFm_jacobiAmm hm u, ← Real.incEllIntFm_neg]
  exact Real.jacobiAmm_incEllIntFm hm _

/-- `am(u|0) = u`. -/
@[dlmf 22.16.E4]
theorem Real.jacobiAmm_zero_param (u : ℝ) : Real.jacobiAmm u 0 = u := by
  simpa [Real.incEllIntFm_zero_param] using Real.jacobiAmm_incEllIntFm (m := 0) (by norm_num) u

/-- Jacobi's elliptic function `sn(u|m) = sin am(u|m)`. -/
def Real.jacobiSnm (u m : ℝ) : ℝ := sin (Real.jacobiAmm u m)

/-- Jacobi's elliptic function `cn(u|m) = cos am(u|m)`. -/
def Real.jacobiCnm (u m : ℝ) : ℝ := cos (Real.jacobiAmm u m)

/-- Jacobi's elliptic function `dn(u|m) = (1 - m sn²(u|m))^{1/2}` (DLMF 22.6.1). -/
def Real.jacobiDnm (u m : ℝ) : ℝ := (1 - m * Real.jacobiSnm u m ^ 2) ^ (1 / 2 : ℝ)

/-- `sn² + cn² = 1` (DLMF 22.6.1). -/
@[dlmf 22.6.E1]
theorem Real.jacobiSnm_sq_add_jacobiCnm_sq (u m : ℝ) :
    Real.jacobiSnm u m ^ 2 + Real.jacobiCnm u m ^ 2 = 1 :=
  sin_sq_add_cos_sq _

/-- `m sn² + dn² = 1` (DLMF 22.6.1). -/
@[dlmf 22.6.E1]
theorem Real.mul_jacobiSnm_sq_add_jacobiDnm_sq {m : ℝ} (hm : m < 1) (u : ℝ) :
    m * Real.jacobiSnm u m ^ 2 + Real.jacobiDnm u m ^ 2 = 1 := by
  have hx : 0 < 1 - m * Real.jacobiSnm u m ^ 2 := one_sub_mul_sin_sq_pos hm (Real.jacobiAmm u m)
  rw [Real.jacobiDnm, ← rpow_natCast ((1 - m * Real.jacobiSnm u m ^ 2) ^ (1 / 2 : ℝ)) 2,
      ← rpow_mul hx.le]
  norm_num

/-- `dn > 0` for `m < 1`. -/
theorem Real.jacobiDnm_pos {m : ℝ} (hm : m < 1) (u : ℝ) : 0 < Real.jacobiDnm u m :=
  rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm _) _

/-- `d sn/du = cn dn` (DLMF Table 22.13.1). -/
@[dlmf 22.13.T1]
theorem Real.hasDerivAt_jacobiSnm {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiSnm u m) (Real.jacobiCnm u m * Real.jacobiDnm u m) u :=
  (hasDerivAt_sin _).comp u (Real.hasDerivAt_jacobiAmm hm u)

/-- `d cn/du = -sn dn` (DLMF Table 22.13.1). -/
@[dlmf 22.13.T1]
theorem Real.hasDerivAt_jacobiCnm {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiCnm u m) (-(Real.jacobiSnm u m * Real.jacobiDnm u m)) u := by
  have h := (hasDerivAt_cos _).comp u (Real.hasDerivAt_jacobiAmm hm u)
  exact h.congr_deriv (by simp [Real.jacobiSnm, Real.jacobiDnm])

/-- `d dn/du = -m sn cn` (DLMF Table 22.13.1). -/
@[dlmf 22.13.T1]
theorem Real.hasDerivAt_jacobiDnm {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiDnm u m)
      (-(m * Real.jacobiSnm u m * Real.jacobiCnm u m)) u := by
  have hx : 0 < 1 - m * Real.jacobiSnm u m ^ 2 := one_sub_mul_sin_sq_pos hm (Real.jacobiAmm u m)
  have h1 := (((Real.hasDerivAt_jacobiSnm hm u).pow 2).const_mul m).const_sub 1
  have h := h1.rpow_const (p := 1 / 2) (Or.inl hx.ne')
  have hdpos := Real.jacobiDnm_pos hm u
  have hr : (1 - m * Real.jacobiSnm u m ^ 2) ^ (1 / 2 - 1 : ℝ) = (Real.jacobiDnm u m)⁻¹ := by
    rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, rpow_neg hx.le]
    rfl
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  rw [hr]
  field_simp
  ring

/-- `sn(u + 2K) = -sn u`, `cn(u + 2K) = -cn u`, `dn(u + 2K) = dn u` (DLMF Table 22.4.3). -/
@[dlmf 22.4.T3 "real parameter m < 1 and real argument: the 2K column for sn, cn, dn"]
theorem Real.jacobi_add_two_compEllIntKm {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiSnm (u + 2 * Real.compEllIntKm m) m = -Real.jacobiSnm u m ∧
      Real.jacobiCnm (u + 2 * Real.compEllIntKm m) m = -Real.jacobiCnm u m ∧
      Real.jacobiDnm (u + 2 * Real.compEllIntKm m) m = Real.jacobiDnm u m := by
  simp only [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiCnm, Real.jacobiAmm_add_two_compEllIntKm hm,
      sin_add_pi,
    cos_add_pi, neg_sq, and_self]

/-- `sn` and `cn` have period `4K` (DLMF §22.4). -/
@[dlmf 22.4.T1 "real parameter m < 1 and real argument: the period 4K of sn and cn"]
theorem Real.jacobiSnm_add_four_compEllIntKm {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiSnm (u + 4 * Real.compEllIntKm m) m = Real.jacobiSnm u m ∧
      Real.jacobiCnm (u + 4 * Real.compEllIntKm m) m = Real.jacobiCnm u m := by
  have h := Real.jacobi_add_two_compEllIntKm hm (u + 2 * Real.compEllIntKm m)
  have h' := Real.jacobi_add_two_compEllIntKm hm u
  rw [show u + 2 * Real.compEllIntKm m + 2 * Real.compEllIntKm m =
      u + 4 * Real.compEllIntKm m by ring] at h
  exact ⟨by rw [h.1, h'.1, neg_neg], by rw [h.2.1, h'.2.1, neg_neg]⟩

/-- Special values at `u = K` (DLMF Table 22.5.1): `sn K = 1`, `cn K = 0`, `dn K = (1-m)^{1/2}`. -/
@[dlmf 22.5.T1 "real parameter m < 1: values of sn, cn, dn at K"]
theorem Real.jacobi_compEllIntKm {m : ℝ} (hm : m < 1) :
    Real.jacobiSnm (Real.compEllIntKm m) m = 1 ∧ Real.jacobiCnm (Real.compEllIntKm m) m = 0 ∧
      Real.jacobiDnm (Real.compEllIntKm m) m = (1 - m) ^ (1 / 2 : ℝ) := by
  simp [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiCnm, Real.jacobiAmm_compEllIntKm hm]

/-- Values at `u = 0`: `sn 0 = 0`, `cn 0 = 1`, `dn 0 = 1`. -/
@[dlmf 22.5.T1 "real parameter m < 1: values of sn, cn, dn at 0"]
theorem jacobi_zero {m : ℝ} (hm : m < 1) :
    Real.jacobiSnm 0 m = 0 ∧ Real.jacobiCnm 0 m = 1 ∧ Real.jacobiDnm 0 m = 1 := by
  simp [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiCnm, Real.jacobiAmm_zero hm]

/-- `sn` is odd and `cn`, `dn` are even. -/
@[dlmf 22.2 "real parameter m < 1: sn odd, cn and dn even"]
theorem jacobi_neg {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiSnm (-u) m = -Real.jacobiSnm u m ∧ Real.jacobiCnm (-u) m = Real.jacobiCnm u m ∧
      Real.jacobiDnm (-u) m = Real.jacobiDnm u m := by
  simp [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiCnm, Real.jacobiAmm_neg hm]

/-- For `m = 0` the Jacobi functions reduce to `sin`, `cos`, `1` (DLMF §22.5(ii)). -/
@[dlmf 22.5.T3 "exact at m = 0 for real argument"]
theorem jacobi_zero_param (u : ℝ) :
    Real.jacobiSnm u 0 = sin u ∧ Real.jacobiCnm u 0 = cos u ∧ Real.jacobiDnm u 0 = 1 := by
  simp [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiCnm, Real.jacobiAmm_zero_param]

end DLMF.Elliptic
