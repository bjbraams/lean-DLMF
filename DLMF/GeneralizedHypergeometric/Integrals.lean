/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuationExistence
public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.Hypergeometric.Basic.GeneralizedCalculus
public import Mathlib.RingTheory.PowerSeries.Basic
public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.Solutions
public import DLMFMathlib.Analysis.Complex.SeparatingContour
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Integral representations of `ₚF_q` (DLMF §16.5)

## Main definitions

* `GenBarnesSeparates`: separation of the upper-parameter poles from the nonnegative integers.
* `GenVerticalBarnesContour`, `GenRightBarnesContour`: vertical and right-loop Barnes contours.
* `genZeroLogSector`: approach to zero on a closed sector of the logarithmic cover.

## Main results

* `genBarnesContours_exist`: separating Barnes contours exist for nonsingular upper parameters.
* `generalizedHypergeometric_barnes_right`, `generalizedHypergeometric_barnes_vertical`,
  `generalizedHypergeometric_barnes_formal_asymptotic`: Barnes integrals, DLMF 16.5.1.
* `generalizedHypergeometric_euler_integral`: the Euler integral, DLMF 16.5.2 (stronger form
  `generalizedHypergeometric_euler_integral'`).
* `generalizedHypergeometric_laplace_integral`: the Laplace integral, DLMF 16.5.3.
* `generalizedHypergeometric_inverse_laplace`: the inverse Laplace integral, DLMF 16.5.4.

## Implementation notes

Barnes contours are specified by absolute continuity on finite pieces, their exact oriented
tails, and separation of the two pole families into distinct components of the contour
complement. This permits finite indentations for arbitrary upper parameters; positive real
parts of the upper parameters are not imposed. The logarithm sheet of `-z` is explicit. Inverse
Laplace integrals assert convergence of both oscillatory tails, not absolute Bochner
integrability where that would be false.
-/

@[expose] public section
open Complex Filter Set Finset MeasureTheory
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

/-- Topological separation of the upper-parameter poles from the nonnegative integers. -/
def GenBarnesSeparates (a : Multiset ℂ) (L : ℝ → ℂ) : Prop :=
  Complex.SeparatesPoleSets L {s | ∃ x ∈ a, ∃ n : ℕ, s = -x - n}
    {s | ∃ n : ℕ, s = n}

/-- An upward Barnes contour with finite indentations and two vertical tails. -/
def GenVerticalBarnesContour (a : Multiset ℂ) (L : ℝ → ℂ) : Prop :=
  (∀ T : ℝ, 0 < T → AbsolutelyContinuousOnInterval L (-T) T) ∧
  GenBarnesSeparates a L ∧ Complex.HasVerticalTails L

/-- A negatively oriented right-infinite Barnes loop, with horizontal tails. -/
def GenRightBarnesContour (a : Multiset ℂ) (L : ℝ → ℂ) : Prop :=
  (∀ T : ℝ, 0 < T → AbsolutelyContinuousOnInterval L (-T) T) ∧
  GenBarnesSeparates a L ∧ Complex.HasHorizontalRightTails L

/-- Approach to zero on a closed sector of the logarithmic cover. -/
def genZeroLogSector (θ : ℝ) : Filter ℂ :=
  comap Complex.re atBot ⊓ 𝓟 {w : ℂ | |w.im| ≤ θ}

/-- Separating Barnes contours exist for every nonsingular upper parameter family. -/
theorem genBarnesContours_exist (a : Multiset ℂ) (ha : LowerParametersRegular a) :
    (∃ L : ℝ → ℂ, GenVerticalBarnesContour a L) ∧
    (∃ L : ℝ → ℂ, GenRightBarnesContour a L) := by
  sorry

/-- The right-loop integral in the entire case and the full open disk in the balanced case. -/
@[dlmf 16.5.E1]
theorem generalizedHypergeometric_barnes_right (a b : Multiset ℂ) (ha : LowerParametersRegular a)
    (hb : LowerParametersRegular b)
    (L : ℝ → ℂ) (hL : GenRightBarnesContour a L) (w : ℂ)
    (h : a.card ≤ b.card ∨ (a.card = b.card + 1 ∧ w.re < 0)) :
    HasBarnesValueLog a b L w (generalizedHypergeometric a b (-Complex.exp w)) := by
  sorry

/-- The full vertical convergence sector; for p=q or p=q+1 it gives the principal continued
function. -/
@[dlmf 16.5.E1]
theorem generalizedHypergeometric_barnes_vertical (a b : Multiset ℂ) (ha : LowerParametersRegular a)
    (hb : LowerParametersRegular b)
    (L : ℝ → ℂ) (hL : GenVerticalBarnesContour a L) (w : ℂ)
    (hpq : b.card < a.card + 1)
    (harg : |w.im| < (a.card + 1 - b.card : ℝ) * Real.pi / 2) :
    HasBarnesValueLog a b L w (barnesHypergeometricLog a b L w) ∧
    (a.card ≤ b.card + 1 → barnesHypergeometricLog a b L w =
        generalizedHypergeometric a b (-Complex.exp w)) := by
  sorry

/-- For p>q+1 the divergent formal series is the Barnes value asymptotic on every closed proper
logarithmic sector. -/
@[dlmf 16.5.E1]
theorem generalizedHypergeometric_barnes_formal_asymptotic (a b : Multiset ℂ)
    (ha : LowerParametersRegular a)
    (hb : LowerParametersRegular b)
    (hpq : b.card + 1 < a.card) (L : ℝ → ℂ) (hL : GenVerticalBarnesContour a L)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδpq : δ < a.card + 1 - b.card) :
    Asymptotics.IsBigO (genZeroLogSector ((a.card + 1 - b.card - δ) * Real.pi / 2))
      (fun w => barnesHypergeometricLog a b L w -
        ∑ n ∈ range N, generalizedHypergeometricCoeff a b n * (-Complex.exp w) ^ n)
      (fun w : ℂ => Real.exp (N * w.re)) := by
  sorry

/-- Off the balanced case the regularized function is the native series. -/
private lemma regularizedGeneralizedHypergeometric_eq_of_card_ne {a b : Multiset ℂ}
    (h : a.card ≠ b.card + 1) :
    regularizedGeneralizedHypergeometric a b = Complex.regularizedHGFun a b := by
  funext w
  unfold regularizedGeneralizedHypergeometric
  simp only [h, ↓reduceIte]

/-- The regularized function with an added Euler pair is the Euler transform. -/
private lemma regularizedGeneralizedHypergeometric_cons_eq_eulerTransform
    {a b : Multiset ℂ} {a₀ b₀ : ℂ}
    (ha₀ : 0 < a₀.re) (hab : 0 < (b₀ - a₀).re) {z : ℂ}
    (h : a.card ≤ b.card ∨ (a.card = b.card + 1 ∧ z ∈ cutPlane)) :
    regularizedGeneralizedHypergeometric (a₀ ::ₘ a) (b₀ ::ₘ b) z =
        eulerTransform a₀ b₀ (regularizedGeneralizedHypergeometric a b) z := by
  rcases h with h | ⟨h, hz⟩
  · rw [regularizedGeneralizedHypergeometric_eq_of_card_ne (a := a) (b := b) (by omega),
      regularizedGeneralizedHypergeometric_eq_of_card_ne (a := a₀ ::ₘ a) (b := b₀ ::ₘ b)
          (by simp; omega),
      regularizedHGFun_cons_eq_integral ha₀ hab a b
      (by rw [Complex.radius_regularizedHGFunSeries_eq_top h]; simp), eulerTransform]
    rfl
  · have hc : (a₀ ::ₘ a).card = (b₀ ::ₘ b).card + 1 := by simp [h]
    have hf := analyticOnNhd_regularizedGeneralizedHypergeometric hc
    have hg : AnalyticOnNhd ℂ
        (eulerTransform a₀ b₀ (regularizedGeneralizedHypergeometric a b)) cutPlane :=
      (differentiableOn_eulerTransform ha₀ hab
        (analyticOnNhd_regularizedGeneralizedHypergeometric h).differentiableOn).analyticOnNhd
            isOpen_cutPlane
    have h0 : (0 : ℂ) ∈ cutPlane := mem_cutPlane_of_norm_lt_one (by simp)
    refine hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_cutPlane h0 ?_ hz
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with w hw
    rw [mem_ball_zero_iff] at hw
    rw [regularizedGeneralizedHypergeometric_eq_series hw,
        eulerTransform_eq_regularizedHGFun ha₀ hab h
      (fun z hz => regularizedGeneralizedHypergeometric_eq_series hz) hw]

/-- Euler integral on the entire domain or the full continued principal slit, with convergence.
Stronger than DLMF, which assumes regular lower parameters `b`. -/
@[dlmf 16.5.E2]
theorem generalizedHypergeometric_euler_integral' (a b : Multiset ℂ) (a₀ b₀ : ℂ)
    (ha₀ : 0 < a₀.re) (hb₀ : a₀.re < b₀.re) {z : ℂ}
    (h : a.card ≤ b.card ∨ (a.card = b.card + 1 ∧ z ∈ cutPlane)) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (a₀ - 1) *
      (1 - (t : ℂ)) ^ (b₀ - a₀ - 1) * generalizedHypergeometric a b (z * t)) volume 0 1 ∧
    generalizedHypergeometric (a₀ ::ₘ a) (b₀ ::ₘ b) z = Gamma b₀ / (Gamma a₀ * Gamma (b₀ - a₀)) *
      ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (a₀ - 1) *
        (1 - (t : ℂ)) ^ (b₀ - a₀ - 1) * generalizedHypergeometric a b (z * t) := by
  have hab : 0 < (b₀ - a₀).re := by simp; linarith
  have hcont : ContinuousOn (fun t : ℝ => generalizedHypergeometric a b (z * t)) (uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    refine continuousOn_const.mul ?_
    rcases h with h | ⟨h, hz⟩
    · rw [regularizedGeneralizedHypergeometric_eq_of_card_ne (by omega)]
      exact ((Complex.analyticOnNhd_regularizedHGFun_of_card_le h).continuous).comp_continuousOn
        (by fun_prop)
    · exact (analyticOnNhd_regularizedGeneralizedHypergeometric h).continuousOn.comp (by fun_prop)
        fun t ht => mul_ofReal_mem_cutPlane hz ht
  refine ⟨(intervalIntegrable_eulerWeight ha₀ hab).mul_continuousOn hcont, ?_⟩
  unfold generalizedHypergeometric
  rw [regularizedGeneralizedHypergeometric_cons_eq_eulerTransform ha₀ hab h, eulerTransform]
  simp only [gammaProduct, Multiset.map_cons, Multiset.prod_cons, eulerWeight]
  have e : ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (a₀ - 1) * (1 - (t : ℂ)) ^ (b₀ - a₀ - 1) *
      ((b.map Gamma).prod * regularizedGeneralizedHypergeometric a b (z * t)) = (b.map Gamma).prod *
      ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (a₀ - 1) * (1 - (t : ℂ)) ^ (b₀ - a₀ - 1) *
        regularizedGeneralizedHypergeometric a b (z * t) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  rw [e]
  ring

/-- Euler integral on the entire domain or the full continued principal slit, with convergence. -/
@[dlmf 16.5.E2]
theorem generalizedHypergeometric_euler_integral (a b : Multiset ℂ) (a₀ b₀ : ℂ)
    (_hb : LowerParametersRegular b)
    (ha₀ : 0 < a₀.re) (hb₀ : a₀.re < b₀.re) {z : ℂ}
    (h : a.card ≤ b.card ∨ (a.card = b.card + 1 ∧ z ∈ cutPlane)) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (a₀ - 1) *
      (1 - (t : ℂ)) ^ (b₀ - a₀ - 1) * generalizedHypergeometric a b (z * t)) volume 0 1 ∧
    generalizedHypergeometric (a₀ ::ₘ a) (b₀ ::ₘ b) z = Gamma b₀ / (Gamma a₀ * Gamma (b₀ - a₀)) *
      ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (a₀ - 1) *
        (1 - (t : ℂ)) ^ (b₀ - a₀ - 1) * generalizedHypergeometric a b (z * t) :=
  generalizedHypergeometric_euler_integral' a b a₀ b₀ ha₀ hb₀ h

/-- Laplace integral with the z restriction removed whenever p<q. -/
@[dlmf 16.5.E3]
theorem generalizedHypergeometric_laplace_integral (a b : Multiset ℂ) (a₀ : ℂ)
    (hb : LowerParametersRegular b)
    (ha₀ : 0 < a₀.re) (hpq : a.card ≤ b.card) {z : ℂ}
    (hz : a.card < b.card ∨ z.re < 1) :
    IntegrableOn (fun t : ℝ => Complex.exp (-t) * (t : ℂ) ^ (a₀ - 1) *
        generalizedHypergeometric a b (z * t)) (Ioi 0) ∧
    DLMF.Core.HasIntegralAtTop
      (fun t : ℝ => Complex.exp (-t) * (t : ℂ) ^ (a₀ - 1) * generalizedHypergeometric a b (z * t)) 0
      (Gamma a₀ * generalizedHypergeometric (a₀ ::ₘ a) b z) := by
  sorry

/-- Inverse Laplace integral with separate oscillatory tails and the full p=q+1 extension. -/
@[dlmf 16.5.E4]
theorem generalizedHypergeometric_inverse_laplace (a b : Multiset ℂ) (b₀ : ℂ)
    (hb : LowerParametersRegular b) (hb₀ : 0 < b₀.re)
    {c : ℝ} (hc : 0 < c) (z : ℂ)
    (h : a.card ≤ b.card ∨ (a.card = b.card + 1 ∧ max 0 z.re < c)) :
    DLMF.Core.HasIntegralWholeLine (fun y : ℝ =>
      Complex.exp (c + y * I) * (c + y * I) ^ (-b₀) *
          generalizedHypergeometric a b (z / (c + y * I)))
      (2 * Real.pi / Gamma b₀ * generalizedHypergeometric a (b₀ ::ₘ b) z) := by
  sorry

end DLMF.Hypergeometric
