/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import TauCeti.Analysis.SpecialFunctions.Artanh
public import DLMFMathlib.Analysis.Calculus.DoubleZeroSqrt
public import DLMF.Bessel.Elementary
public import DLMF.ParabolicCylinder.ElementaryProperties
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Turning-point coordinate maps for Legendre functions

The parameters and implicitly defined coordinates of the large-order and large-degree uniform
approximations of DLMF §14.15(ii) and §14.15(iv), with the existence, uniqueness and monotonicity
of the coordinate maps.

## Main definitions

* `legendreOrderAlpha`, `legendreOrderP`, `legendreOrderRho`: the quantities `α`, `p`, `ρ` of the
  large-order expansions (DLMF 14.15.5–14.15.7).
* `LegendreEtaRelation`, `legendreOrderEta`: the relation of DLMF 14.15.10 and the variable `η`
  chosen as its positive solution.
* `legendreDegreeAlpha`, `legendreDegreeBeta`: the quantities `α`, `β` of the large-degree
  expansions (DLMF 14.15.19, 14.15.20).
* `LegendreYRelation`, `legendreDegreeY`: the relations of DLMF 14.15.21–14.15.22 and the
  variable `y` chosen as their solution.

## Main results

* `legendreOrderEta_spec`, `legendreOrderEta_bijective`: for `0 ≤ α < 1` and `x > 1`, `η` is the
  unique positive solution of DLMF 14.15.10, and `x ↦ η` is a strictly decreasing bijection of
  `(1,∞)` onto `(0,∞)` (DLMF §14.15(ii)).
* `DegreeCoordinate.existsUnique`: existence and uniqueness of the solution `y` of DLMF
  14.15.21–14.15.22.

## Implementation notes

Since DLMF defines `η`, `y` only implicitly, `legendreOrderEta` and `legendreDegreeY` are chosen
solutions; `legendreOrderEta_spec` and `legendreDegreeY_spec` (in `InverseCoordinates`) give
the defining relations and uniqueness. Helper names live in the namespaces `OrderEta` and
`DegreeCoordinate`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Legendre

open DLMF.Bessel DLMF.Confluent

/-- DLMF 14.15.5: the ratio `α = (ν+1/2)/μ` used in the large-order uniform expansions
14.15.4–14.15.10. -/
@[dlmf 14.15.E5]
def legendreOrderAlpha (ν μ : ℝ) : ℝ :=
  (ν+1/2)/μ

/-- DLMF 14.15.6: the auxiliary variable `p = x/(α²x² + 1 − α²)^{1/2}` of the large-order expansion
14.15.4. -/
@[dlmf 14.15.E6]
def legendreOrderP (α x : ℝ) : ℝ :=
  x/Real.sqrt (α^2*x^2+1-α^2)

/-- DLMF 14.15.7: the exponent `ρ = ½ ln((1+p)/(1−p)) + (α/2) ln((1−αp)/(1+αp))`, with `p` from
14.15.6, of the large-order expansion 14.15.4. -/
@[dlmf 14.15.E7]
def legendreOrderRho (α x : ℝ) : ℝ :=
  let p:=legendreOrderP α x; Real.log ((1+p)/(1-p))/2+α/2*Real.log ((1-α*p)/(1+α*p))

/-- DLMF 14.15.10: the relation `α ln((α²+η²)^{1/2} + α) − α ln η − (α²+η²)^{1/2} = ½ ln(((1+α²)x² +
1 − α² − 2x(α²x² − α² + 1)^{1/2})/((x²−1)(1−α²))) + (α/2) ln((α²(2x²−1) + 1 + 2αx(α²x² − α² +
1)^{1/2})/(1−α²))` defining `η` in 14.15.8–14.15.9. -/
@[dlmf 14.15.E10]
def LegendreEtaRelation (α x η : ℝ) : Prop :=
  α*Real.log (Real.sqrt (α^2+η^2)+α)-α*Real.log η-Real.sqrt (α^2+η^2) =
      Real.log (((1+α^2)*x^2+1-α^2-2*x*Real.sqrt (α^2*x^2-α^2+1))/((x^2-1)*(1-α^2)))/2+α/2*Real.log
      ((α^2*(2*x^2-1)+1+2*α*x*Real.sqrt (α^2*x^2-α^2+1))/(1-α^2))

/-- DLMF 14.15.10: the variable `η`, chosen as a positive solution of `LegendreEtaRelation α x η`
(unique for `0 ≤ α < 1`, `x > 1`; see `legendreOrderEta_spec`). -/
@[dlmf 14.15.E10]
def legendreOrderEta (α x : ℝ) : ℝ :=
  Classical.epsilon (fun η : ℝ => 0 < η ∧ LegendreEtaRelation α x η)

/-- The left side of DLMF 14.15.10 as a function of `η`. -/
noncomputable def OrderEta.lhs (α η : ℝ) : ℝ :=
  α*Real.log (Real.sqrt (α^2+η^2)+α)-α*Real.log η-Real.sqrt (α^2+η^2)

/-- `L'(η) = -√(α²+η²)/η`. -/
theorem OrderEta.lhs_hasDerivAt {α η : ℝ} (hα : 0 ≤ α) (hη : 0 < η) :
    HasDerivAt (OrderEta.lhs α) (-(Real.sqrt (α^2+η^2)/η)) η := by
  have hp : 0 < α^2+η^2 := by positivity
  set s := Real.sqrt (α^2+η^2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hp
  have hs2 : s^2 = α^2+η^2 := Real.sq_sqrt hp.le
  have hsd : HasDerivAt (fun η => Real.sqrt (α^2+η^2)) (2*η/(2*s)) η := by
    have : HasDerivAt (fun η : ℝ => α^2+η^2) (2*η) η := by
      simpa using (hasDerivAt_pow 2 η).const_add (α^2)
    exact this.sqrt hp.ne'
  have hsa : 0 < s + α := by linarith
  have h := ((((hsd.add_const α).log hsa.ne').const_mul α).sub
    ((Real.hasDerivAt_log hη.ne').const_mul α)).sub hsd
  convert h using 1
  · funext y; simp only [OrderEta.lhs, Pi.sub_apply]
  · rw [← hs]
    field_simp
    linear_combination (-s) * hs2

/-- `L` decreases strictly on `(0, ∞)`. -/
theorem OrderEta.lhs_strictAntiOn {α : ℝ} (hα : 0 ≤ α) : StrictAntiOn (OrderEta.lhs α) (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun η hη => (OrderEta.lhs_hasDerivAt hα hη).continuousAt.continuousWithinAt) fun η hη => ?_
  rw [interior_Ioi] at hη
  have hη : (0:ℝ) < η := hη
  rw [(OrderEta.lhs_hasDerivAt hα hη).deriv, neg_lt_zero]
  have : 0 < Real.sqrt (α^2+η^2) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- `L → ∞` as `η → 0⁺` when `α > 0`. -/
theorem OrderEta.lhs_tendsto_zero {α : ℝ} (hα : 0 < α) : Tendsto (OrderEta.lhs α)
    (𝓝[>] 0) atTop := by
  have hg : ContinuousAt
      (fun η : ℝ => α*Real.log (Real.sqrt (α^2+η^2)+α) - Real.sqrt (α^2+η^2)) 0 := by
    have h : Real.sqrt (α^2+0^2)+α ≠ 0 := by positivity
    fun_prop (disch := exact h)
  have := (Real.tendsto_log_nhdsGT_zero.const_mul_atBot_of_neg (show -α < 0 by linarith)).atTop_add
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
  refine this.congr fun η => ?_
  simp only [OrderEta.lhs]; ring

/-- `L → -∞` as `η → ∞`. -/
theorem OrderEta.lhs_tendsto_atTop {α : ℝ} (hα : 0 ≤ α) : Tendsto (OrderEta.lhs α) atTop atBot := by
  have hb : ∀ᶠ η in atTop, OrderEta.lhs α η ≤ α*Real.log 3 - η := by
    filter_upwards [eventually_ge_atTop (α+1)] with η hη
    have hη0 : 0 < η := by linarith
    have hp : 0 < α^2+η^2 := by positivity
    set s := Real.sqrt (α^2+η^2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hp
    have hs2 : s^2 = α^2+η^2 := Real.sq_sqrt hp.le
    have hsη : η ≤ s := by nlinarith
    have hsle : s ≤ η + α := by nlinarith
    have hsa : 0 < s + α := by linarith
    have hl : Real.log (s+α) - Real.log η ≤ Real.log 3 := by
      rw [← Real.log_div hsa.ne' hη0.ne']
      exact Real.log_le_log (by positivity) (by rw [div_le_iff₀ hη0]; linarith)
    simp only [OrderEta.lhs]
    rw [← hs]
    nlinarith
  exact tendsto_atBot_mono' _ hb (tendsto_atBot_add_const_left _ _ tendsto_neg_atTop_atBot)

/-- The right side of DLMF 14.15.10 as a function of `x`. -/
noncomputable def OrderEta.rhs (α x : ℝ) : ℝ :=
  Real.log (((1+α^2)*x^2+1-α^2-2*x*Real.sqrt (α^2*x^2-α^2+1))/((x^2-1)*(1-α^2)))/2+α/2*Real.log
      ((α^2*(2*x^2-1)+1+2*α*x*Real.sqrt (α^2*x^2-α^2+1))/(1-α^2))

/-- DLMF 14.15.10: for `0 ≤ α < 1` and `x > 1`, `η = legendreOrderEta α x` is positive, satisfies
`LegendreEtaRelation α x η`, and is the unique positive solution. -/
@[dlmf 14.15.E10]
theorem legendreOrderEta_spec {α x : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hx : 1 < x) :
    0 < legendreOrderEta α x ∧ LegendreEtaRelation α x (legendreOrderEta α x) ∧ ∀ η : ℝ, 0 < η →
        LegendreEtaRelation α x η → η=legendreOrderEta α x := by
  have hrel : ∀ η, LegendreEtaRelation α x η ↔ OrderEta.lhs α η = OrderEta.rhs α x :=
      fun η => Iff.rfl
  have hex : ∃ η : ℝ, 0 < η ∧ LegendreEtaRelation α x η := by
    rcases hα.lt_or_eq with hα | hα
    · obtain ⟨η, hη, h⟩ := DoubleZeroSqrt.exists_eq_of_tendsto (f := fun η => -OrderEta.lhs α η)
        (fun η hη => (OrderEta.lhs_hasDerivAt hα.le hη).continuousAt.neg.continuousWithinAt)
        (tendsto_neg_atTop_atBot.comp (OrderEta.lhs_tendsto_zero hα))
        (tendsto_neg_atBot_atTop.comp (OrderEta.lhs_tendsto_atTop hα.le)) (-OrderEta.rhs α x)
      exact ⟨η, hη, (hrel η).2 (by simpa using h)⟩
    · subst hα
      have h1 : 0 < x - 1 := by linarith
      have h2 : 0 < x + 1 := by linarith
      have hq : ((1+0^2)*x^2+1-0^2-2*x*Real.sqrt (0^2*x^2-0^2+1))/((x^2-1)*(1-0^2))
          = (x-1)/(x+1) := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero,
          zero_add, Real.sqrt_one, add_zero, mul_one]
        rw [div_eq_div_iff (by nlinarith) h2.ne']; ring
      have hlt : Real.log ((x-1)/(x+1)) < 0 :=
        Real.log_neg (by positivity) (by rw [div_lt_one h2]; linarith)
      refine ⟨-(Real.log ((x-1)/(x+1))/2), by linarith, ?_⟩
      simp only [LegendreEtaRelation]
      rw [hq]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, zero_mul,
        sub_zero]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (by linarith)]
      ring
  have hs := Classical.epsilon_spec hex
  refine ⟨hs.1, hs.2, fun η hη h => ?_⟩
  exact (OrderEta.lhs_strictAntiOn hα).injOn hη hs.1 (((hrel η).1 h).trans ((hrel _).1 hs.2).symm)

/-- The first logarithm argument in DLMF 14.15.10 is positive for `x > 1`. -/
theorem OrderEta.logArg_pos {α x : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hx : 1 < x) :
    0 < (1+α^2)*x^2+1-α^2-2*x*Real.sqrt (α^2*x^2-α^2+1) := by
  have hB : 0 < 1 - α^2 := by nlinarith
  have hW : Real.sqrt (α^2*x^2-α^2+1) ^ 2 = α^2*x^2-α^2+1 :=
    Real.sq_sqrt (by nlinarith [mul_nonneg (sq_nonneg α) (sq_nonneg x)])
  set W := Real.sqrt (α^2*x^2-α^2+1)
  have hNN : ((1+α^2)*x^2+1-α^2-2*x*W) * ((1+α^2)*x^2+1-α^2+2*x*W)
      = (1-α^2)^2*(x^2-1)^2 := by
    linear_combination (-4*x^2) * hW
  have hx2 : 0 < x^2 - 1 := by nlinarith
  have hp : 0 < ((1+α^2)*x^2+1-α^2-2*x*W) * ((1+α^2)*x^2+1-α^2+2*x*W) := by
    rw [hNN]; positivity
  have hsum : 0 < ((1+α^2)*x^2+1-α^2-2*x*W) + ((1+α^2)*x^2+1-α^2+2*x*W) := by
    nlinarith [sq_nonneg x, sq_nonneg α]
  by_contra h
  push Not at h
  nlinarith

/-- `R'(x) = √(α²x²-α²+1)/(x²-1)`. -/
theorem OrderEta.rhs_hasDerivAt {α x : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hx : 1 < x) :
    HasDerivAt (OrderEta.rhs α) (Real.sqrt (α^2*x^2-α^2+1)/(x^2-1)) x := by
  have hB : 0 < 1 - α^2 := by nlinarith
  have hx2 : 0 < x^2 - 1 := by nlinarith
  have hWp : 0 < α^2*x^2-α^2+1 := by nlinarith [mul_nonneg (sq_nonneg α) hx2.le]
  set W := Real.sqrt (α^2*x^2-α^2+1) with hWdef
  have hW0 : 0 < W := Real.sqrt_pos.2 hWp
  have hW : W^2 = α^2*x^2-α^2+1 := Real.sq_sqrt hWp.le
  have hN := OrderEta.logArg_pos hα hα1 hx
  have hP : 0 < α^2*(2*x^2-1)+1+2*α*x*W := by
    have : 0 ≤ α*x*W := by positivity
    nlinarith [mul_nonneg (sq_nonneg α) hx2.le]
  have hWd : HasDerivAt (fun x => Real.sqrt (α^2*x^2-α^2+1)) (α^2*(2*x)/(2*W)) x := by
    have : HasDerivAt (fun x => α^2*x^2-α^2+1) (α^2*(2*x)) x := by
      simpa using (((hasDerivAt_pow 2 x).const_mul (α^2)).sub_const (α^2)).add_const 1
    exact this.sqrt hWp.ne'
  have hNd : HasDerivAt (fun x => (1+α^2)*x^2+1-α^2-2*x*Real.sqrt (α^2*x^2-α^2+1))
      ((1+α^2)*(2*x) - (2*W + 2*x*(α^2*(2*x)/(2*W)))) x := by
    have h1 : HasDerivAt (fun x => (1+α^2)*x^2) ((1+α^2)*(2*x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (1+α^2)
    have h2 := ((hasDerivAt_id x).const_mul 2).mul hWd
    simp only [id, mul_one] at h2
    have := ((h1.add_const 1).sub_const (α^2)).sub h2
    convert this using 1
  have hDd : HasDerivAt (fun x : ℝ => (x^2-1)*(1-α^2)) ((2*x)*(1-α^2)) x := by
    simpa using ((hasDerivAt_pow 2 x).sub_const 1).mul_const (1-α^2)
  have hPd : HasDerivAt (fun x => α^2*(2*x^2-1)+1+2*α*x*Real.sqrt (α^2*x^2-α^2+1))
      (α^2*(2*(2*x)) + (2*α*W + 2*α*x*(α^2*(2*x)/(2*W)))) x := by
    have h1 : HasDerivAt (fun x => α^2*(2*x^2-1)) (α^2*(2*(2*x))) x := by
      simpa using (((hasDerivAt_pow 2 x).const_mul 2).sub_const 1).const_mul (α^2)
    have h2 := ((hasDerivAt_id x).const_mul (2*α)).mul hWd
    simp only [id, mul_one] at h2
    have := (h1.add_const 1).add h2
    convert this using 1
  have hL1 := ((hNd.div hDd (by positivity)).log (div_pos hN (by positivity)).ne').div_const 2
  have hL2 := ((hPd.div_const (1-α^2)).log (div_pos hP hB).ne').const_mul (α/2)
  have := hL1.add hL2
  convert this using 1
  · funext y; simp [OrderEta.rhs]
  · simp only [Pi.div_apply]
    rw [← hWdef]
    have hN2 : x^2*(1+α^2)+1-α^2-W*x*2 ≠ 0 := by
      rw [← hWdef] at hN; linarith
    have hP2 : α^2*(x^2*2-1)+1+W*x*α*2 ≠ 0 := by linarith
    field_simp
    field_simp
    linear_combination (-4*W^2*α*x^2 + W*(2*α^3*x^3 - 2*α^3*x - 2*α^2*x^3 - 2*x) + α^4*x^4
      - α^4*x^2 - α^2*x^4 + α^2*x^2) * hW

/-- Rationalized form of the first logarithm argument. -/
theorem OrderEta.logArg_ratio {α x : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hx : 1 < x) :
    ((1+α^2)*x^2+1-α^2-2*x*Real.sqrt (α^2*x^2-α^2+1))/((x^2-1)*(1-α^2))
      = (1-α^2)*(x^2-1)/((1+α^2)*x^2+1-α^2+2*x*Real.sqrt (α^2*x^2-α^2+1)) := by
  have hB : 0 < 1 - α^2 := by nlinarith
  have hx2 : 0 < x^2 - 1 := by nlinarith
  have hW : Real.sqrt (α^2*x^2-α^2+1) ^ 2 = α^2*x^2-α^2+1 :=
    Real.sq_sqrt (by nlinarith [mul_nonneg (sq_nonneg α) (sq_nonneg x)])
  have hT : 0 < (1+α^2)*x^2+1-α^2+2*x*Real.sqrt (α^2*x^2-α^2+1) := by
    have := Real.sqrt_nonneg (α^2*x^2-α^2+1)
    nlinarith [sq_nonneg α]
  rw [div_eq_div_iff (by positivity) hT.ne']
  linear_combination (-4*x^2) * hW

/-- `R → -∞` as `x → 1⁺`. -/
theorem OrderEta.rhs_tendsto_one {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    Tendsto (OrderEta.rhs α) (𝓝[>] (1:ℝ)) atBot := by
  have hB : 0 < 1 - α^2 := by nlinarith
  set T : ℝ → ℝ := fun x => (1+α^2)*x^2+1-α^2+2*x*Real.sqrt (α^2*x^2-α^2+1) with hTdef
  have hT1 : Tendsto T (𝓝 1) (𝓝 4) := by
    have hc : Continuous T := by rw [hTdef]; fun_prop
    have e : T 1 = 4 := by
      simp only [hTdef]
      rw [show α^2*(1:ℝ)^2-α^2+1 = 1 by ring, Real.sqrt_one]; ring
    rw [← e]; exact hc.tendsto 1
  have hnum : Tendsto (fun x : ℝ => (1-α^2)*(x^2-1)) (𝓝 1) (𝓝 0) := by
    have hc : Continuous fun x : ℝ => (1-α^2)*(x^2-1) := by fun_prop
    have h := hc.tendsto 1
    rwa [show (1-α^2)*((1:ℝ)^2-1) = 0 by ring] at h
  have harg : Tendsto (fun x => (1-α^2)*(x^2-1) / T x) (𝓝[>] (1:ℝ)) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := hnum.div hT1 (by norm_num)
      rw [zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx : (1:ℝ) < x := hx
      have hx2 : 0 < x^2 - 1 := by nlinarith
      have hTx : 0 < T x := by
        have := Real.sqrt_nonneg (α^2*x^2-α^2+1)
        simp only [hTdef]; nlinarith [sq_nonneg α]
      exact div_pos (by positivity) hTx
  have hl := (Real.tendsto_log_nhdsGT_zero.comp harg).atBot_div_const (show (0:ℝ) < 2 by norm_num)
  have h2 : ContinuousAt
      (fun x : ℝ => α/2*Real.log
      ((α^2*(2*x^2-1)+1+2*α*x*Real.sqrt (α^2*x^2-α^2+1))/(1-α^2))) 1 := by
    have hP : (α^2*(2*1^2-1)+1+2*α*1*Real.sqrt (α^2*1^2-α^2+1))/(1-α^2) ≠ 0 := by
      rw [show α^2*(1:ℝ)^2-α^2+1 = 1 by ring, Real.sqrt_one]
      exact div_ne_zero (by nlinarith) hB.ne'
    have hB' : (1:ℝ) - α^2 ≠ 0 := hB.ne'
    fun_prop (disch := assumption)
  refine (hl.atBot_add (h2.tendsto.mono_left nhdsWithin_le_nhds)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp, OrderEta.rhs]
  rw [OrderEta.logArg_ratio hα hα1 hx]

/-- `R → ∞` as `x → ∞` when `α > 0`. -/
theorem OrderEta.rhs_tendsto_atTop {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (OrderEta.rhs α) atTop atTop := by
  have hB : 0 < 1 - α^2 := by nlinarith
  have hb : ∀ᶠ x in atTop, Real.log ((1-α^2)/8)/2 + α/2*Real.log (α^2*x^2) ≤ OrderEta.rhs α x := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hx1 : (1:ℝ) < x := by linarith
    have hx2 : 0 < x^2 - 1 := by nlinarith
    have hWp : 0 ≤ α^2*x^2-α^2+1 := by nlinarith [mul_nonneg (sq_nonneg α) hx2.le]
    set W := Real.sqrt (α^2*x^2-α^2+1) with hWdef
    have hW0 : 0 ≤ W := Real.sqrt_nonneg _
    have hW : W^2 = α^2*x^2-α^2+1 := Real.sq_sqrt hWp
    have hWx : W ≤ x := by nlinarith
    have hT : 0 < (1+α^2)*x^2+1-α^2+2*x*W := by nlinarith [sq_nonneg α]
    have hP : 0 < α^2*(2*x^2-1)+1+2*α*x*W := by
      have : 0 ≤ α*x*W := by positivity
      nlinarith [mul_nonneg (sq_nonneg α) hx2.le]
    have h1 : Real.log ((1-α^2)/8) ≤ Real.log ((1-α^2)*(x^2-1)/((1+α^2)*x^2+1-α^2+2*x*W)) := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_div_iff₀ (by norm_num) hT]
      have hxW : x * W ≤ x^2 := by nlinarith
      have hTle : (1+α^2)*x^2+1-α^2+2*x*W ≤ 8*(x^2-1) := by
        nlinarith [mul_nonneg hB.le (show (0:ℝ) ≤ x^2 - 1 by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hTle hB.le]
    have h2 : Real.log (α^2*x^2) ≤ Real.log ((α^2*(2*x^2-1)+1+2*α*x*W)/(1-α^2)) := by
      refine Real.log_le_log (by positivity) ?_
      rw [le_div_iff₀ hB]
      have : 0 ≤ α*x*W := by positivity
      nlinarith [mul_nonneg (sq_nonneg α) (sq_nonneg x),
          mul_nonneg (mul_nonneg (sq_nonneg α) (sq_nonneg x)) (sq_nonneg α),
          mul_nonneg (sq_nonneg α) hx2.le]
    simp only [OrderEta.rhs]
    rw [OrderEta.logArg_ratio hα.le hα1 hx1, ← hWdef]
    nlinarith
  refine tendsto_atTop_mono' _ hb (tendsto_atTop_add_const_left _ _ ?_)
  refine (Real.tendsto_log_atTop.comp ?_).const_mul_atTop (by positivity)
  exact (tendsto_pow_atTop (two_ne_zero)).const_mul_atTop (by positivity)

/-- `L` at `α = 0`. -/
theorem OrderEta.lhs_zero (b : ℝ) (hb : 0 < b) : OrderEta.lhs 0 b = -b := by
  simp [OrderEta.lhs, Real.sqrt_sq hb.le]

/-- `R` at `α = 0`. -/
theorem OrderEta.rhs_zero {x : ℝ} (hx : 1 < x) : OrderEta.rhs 0 x = Real.log ((x-1)/(x+1))/2 := by
  have h2 : 0 < x + 1 := by linarith
  simp only [OrderEta.rhs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul, sub_zero,
    zero_add, Real.sqrt_one, add_zero, mul_one, zero_div, one_mul]
  rw [show (x^2+1-2*x)/(x^2-1) = (x-1)/(x+1) by
    rw [div_eq_div_iff (by nlinarith) h2.ne']; ring]

/-- Eventually `R(x) > L(b)` for every `b > 0`. -/
theorem OrderEta.rhs_eventually_gt {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, OrderEta.lhs α b < OrderEta.rhs α x := by
  rcases hα.lt_or_eq with hα | hα
  · exact (OrderEta.rhs_tendsto_atTop hα hα1).eventually (eventually_gt_atTop _)
  · subst hα
    rw [OrderEta.lhs_zero b hb]
    have hq : Tendsto (fun x : ℝ => 1 - 2/(x+1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub ((tendsto_const_nhds (x := (2:ℝ))).div_atTop
        (tendsto_atTop_add_const_right _ 1 tendsto_id))
    rw [sub_zero] at hq
    have hl := ((Real.continuousAt_log one_ne_zero).tendsto.comp hq).div_const 2
    rw [Real.log_one, zero_div] at hl
    filter_upwards [hl.eventually (lt_mem_nhds (show -b < 0 by linarith)), eventually_gt_atTop 1]
      with x hx hx1
    rw [OrderEta.rhs_zero hx1]
    simp only [Function.comp] at hx
    rwa [show (x-1)/(x+1) = 1 - 2/(x+1) by field_simp; ring]

/-- One-to-one correspondence and endpoint behavior in DLMF 14.15(ii). -/
theorem legendreOrderEta_bijective {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    Set.BijOn (legendreOrderEta α) (Ioi 1) (Ioi 0) ∧ StrictAntiOn (legendreOrderEta α) (Ioi 1) ∧
        Tendsto (legendreOrderEta α) (𝓝[>] 1) atTop ∧ Tendsto (legendreOrderEta α) atTop (𝓝 0) := by
  have hE : ∀ x ∈ Ioi (1:ℝ), 0 < legendreOrderEta α x ∧
      OrderEta.lhs α (legendreOrderEta α x) = OrderEta.rhs α x :=
    fun x hx => ⟨(legendreOrderEta_spec hα hα1 hx).1, (legendreOrderEta_spec hα hα1 hx).2.1⟩
  have hL := OrderEta.lhs_strictAntiOn hα
  have hRc : ContinuousOn (OrderEta.rhs α) (Ioi 1) :=
    fun x hx => (OrderEta.rhs_hasDerivAt hα hα1 hx).continuousAt.continuousWithinAt
  have hR : StrictMonoOn (OrderEta.rhs α) (Ioi 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi _) hRc fun x hx => ?_
    rw [interior_Ioi] at hx
    have hx : (1:ℝ) < x := hx
    rw [(OrderEta.rhs_hasDerivAt hα hα1 hx).deriv]
    have hx2 : 0 < x^2 - 1 := by nlinarith
    have : 0 < Real.sqrt (α^2*x^2-α^2+1) :=
      Real.sqrt_pos.2 (by nlinarith [mul_nonneg (sq_nonneg α) hx2.le])
    positivity
  have hanti : StrictAntiOn (legendreOrderEta α) (Ioi 1) := by
    intro x hx y hy hxy
    have h1 := hR hx hy hxy
    rw [← (hE x hx).2, ← (hE y hy).2] at h1
    exact (hL.lt_iff_gt (hE x hx).1 (hE y hy).1).1 h1
  have hI : ∀ᶠ x in 𝓝[>] (1:ℝ), x ∈ Ioi (1:ℝ) := self_mem_nhdsWithin
  refine ⟨⟨fun x hx => (hE x hx).1, hanti.injOn, fun e he => ?_⟩, hanti, ?_, ?_⟩
  · have he : (0:ℝ) < e := he
    obtain ⟨a, ha, haI⟩ := (((OrderEta.rhs_tendsto_one hα hα1).eventually
      (eventually_lt_atBot (OrderEta.lhs α e))).and hI).exists
    obtain ⟨b, hb, hab⟩ :=
        ((OrderEta.rhs_eventually_gt hα hα1 he).and (eventually_ge_atTop a)).exists
    have hsub : Icc a b ⊆ Ioi (1:ℝ) := fun x hx => lt_of_lt_of_le haI hx.1
    obtain ⟨c, hc, hcy⟩ := intermediate_value_Icc hab (hRc.mono hsub) ⟨ha.le, hb.le⟩
    exact ⟨c, hsub hc, ((legendreOrderEta_spec hα hα1 (hsub hc)).2.2 e he hcy.symm).symm⟩
  · refine tendsto_atTop.2 fun M => ?_
    have hM : (0:ℝ) < max M 1 := lt_max_of_lt_right one_pos
    filter_upwards [(OrderEta.rhs_tendsto_one hα hα1).eventually
      (eventually_lt_atBot (OrderEta.lhs α (max M 1))), hI] with x hx hxI
    rw [← (hE x hxI).2] at hx
    exact (le_max_left _ _).trans ((hL.lt_iff_gt (hE x hxI).1 hM).1 hx).le
  · refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · filter_upwards [eventually_gt_atTop 1] with x hx
      exact ha.trans (hE x hx).1
    · filter_upwards [OrderEta.rhs_eventually_gt hα hα1 hb, eventually_gt_atTop 1] with x hx hxI
      rw [← (hE x hxI).2] at hx
      exact (hL.lt_iff_gt hb (hE x hxI).1).1 hx

/-- DLMF 14.15.19: the ratio `α = μ/(ν+1/2)` used in the large-degree uniform expansions
14.15.15–14.15.22. -/
@[dlmf 14.15.E19]
def legendreDegreeAlpha (ν μ : ℝ) : ℝ :=
  μ/(ν+1/2)

/-- DLMF 14.15.20: the normalizing factor `β = e^μ ((ν−μ+1/2)/(ν+μ+1/2))^{ν/2+1/4} ((ν+1/2)² −
μ²)^{−μ/2}` of the large-degree expansions 14.15.15–14.15.18. -/
@[dlmf 14.15.E20]
def legendreDegreeBeta (ν μ : ℝ) : ℝ :=
  Real.exp μ*((ν-μ+1/2)/(ν+μ+1/2))^(ν/2+1/4)*((ν+1/2)^2-μ^2)^(-μ/2)

/-- LegendreYRelation. For `x ≥ √(1−α²)` the equation 14.15.22 has a root in `(0, α²)` and one
in `(−∞, 0)` whenever its right side is negative; DLMF's `y` decreases through `0` at `x = 1`, so
the sign conditions `x < 1 → 0 < y` and `1 < x → y < 0` select it (corrected 2026-10-22; at
`α = 0.6`, `x = 0.9` both `y = 0.177237` and `y = −0.116411` solve the equation). -/
@[dlmf 14.15.E21, dlmf 14.15.E22]
def LegendreYRelation (α x y : ℝ) : Prop :=
  if x=1 then y=0 else if x ≤ Real.sqrt (1-α^2) then α^2 ≤ y ∧
      Real.sqrt (y-α^2)-α*Real.arctan (Real.sqrt (y-α^2)/α)=Real.arccos
      (x/Real.sqrt (1-α^2))-α/2*Real.arccos (((1+α^2)*x^2-1+α^2)/((1-α^2)*(1-x^2))) else y ≤ α^2 ∧
      (x < 1 → 0 < y) ∧ (1 < x → y < 0) ∧
      Real.sqrt (α^2-y)+α/2*Real.log |y|-α*Real.log (Real.sqrt (α^2-y)+α)=Real.log
      ((x+Real.sqrt (x^2-1+α^2))/Real.sqrt (1-α^2))+α/2*Real.log
      ((1-α^2)*|1-x^2|/((1+α^2)*x^2-1+α^2+2*α*x*Real.sqrt (x^2-1+α^2)))

/-- DLMF 14.15.21–14.15.22: the variable `y`, chosen as a solution of `LegendreYRelation α x y`
(unique for `0 ≤ α < 1`, `x ≥ 0`; see `legendreDegreeY_spec`). -/
def legendreDegreeY (α x : ℝ) : ℝ :=
  Classical.epsilon (LegendreYRelation α x)

/-- Left side of 14.15.21 in the variable `s = √(y - α²)`. -/
noncomputable def DegreeCoordinate.lhsLeft (a s : ℝ) : ℝ := s - a * Real.arctan (s / a)

/-- Left side of 14.15.22 in the variable `s = √(α² - y)`. -/
noncomputable def DegreeCoordinate.lhsRight (a s : ℝ) : ℝ := s + a/2 * Real.log (a^2 - s^2) - a *
    Real.log (s + a)

/-- `L₁` is continuous. -/
theorem DegreeCoordinate.lhsLeft_continuous (a : ℝ) : Continuous (DegreeCoordinate.lhsLeft a) := by
  unfold DegreeCoordinate.lhsLeft
  exact continuous_id.sub (continuous_const.mul (Real.continuous_arctan.comp
    (continuous_id.div_const a)))

/-- `L₁(0) = 0`. -/
theorem DegreeCoordinate.lhsLeft_zero (a : ℝ) : DegreeCoordinate.lhsLeft a 0 = 0 := by
    simp [DegreeCoordinate.lhsLeft]

/-- `L₁` increases strictly on `[0, ∞)`. -/
theorem DegreeCoordinate.lhsLeft_strictMonoOn {a : ℝ} (ha : 0 ≤ a) : StrictMonoOn
    (DegreeCoordinate.lhsLeft a) (Ici 0) := by
  rcases ha.eq_or_lt with rfl | ha
  · intro s _ t _ h; simpa [DegreeCoordinate.lhsLeft] using h
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      (DegreeCoordinate.lhsLeft_continuous a).continuousOn ?_
  intro s hs
  rw [interior_Ici] at hs
  have hs : (0:ℝ) < s := hs
  have hd : HasDerivAt (DegreeCoordinate.lhsLeft a) (1 - a * (1 / (1 + (s/a)^2) * (1/a))) s := by
    have := (hasDerivAt_id' s).fun_sub ((((hasDerivAt_id' s).div_const a).arctan).const_mul a)
    exact this
  rw [hd.deriv]
  have : a * (1 / (1 + (s/a)^2) * (1/a)) = a^2 / (a^2 + s^2) := by
    field_simp
  rw [this, sub_pos, div_lt_one (by positivity)]
  nlinarith

/-- A linear lower bound for `L₁`. -/
theorem DegreeCoordinate.lhsLeft_ge {a : ℝ} (ha : 0 ≤ a) (s : ℝ) : s - a * (π/2) ≤
    DegreeCoordinate.lhsLeft a s := by
  unfold DegreeCoordinate.lhsLeft
  nlinarith [Real.arctan_lt_pi_div_two (s/a)]

/-- `L₁` maps `[0, ∞)` onto `[0, ∞)`. -/
theorem DegreeCoordinate.lhsLeft_surj {a : ℝ} (ha : 0 ≤ a) {v : ℝ} (hv : 0 ≤ v) :
    ∃ s, 0 ≤ s ∧ DegreeCoordinate.lhsLeft a s = v := by
  have h0 : (0:ℝ) ≤ v + a * (π/2) := by positivity
  obtain ⟨s, hs, hsv⟩ :=
      intermediate_value_Icc h0 (DegreeCoordinate.lhsLeft_continuous a).continuousOn
    (show v ∈ Icc (DegreeCoordinate.lhsLeft a 0) (DegreeCoordinate.lhsLeft a (v + a * (π/2)))
        from ⟨by rw [DegreeCoordinate.lhsLeft_zero]; exact hv, by
      have := DegreeCoordinate.lhsLeft_ge ha (v + a * (π/2)); linarith⟩)
  exact ⟨s, hs.1, hsv⟩

/-- `L₂(0) = 0`. -/
theorem DegreeCoordinate.lhsRight_zero (a : ℝ) : DegreeCoordinate.lhsRight a 0 = 0 := by
  simp [DegreeCoordinate.lhsRight, Real.log_pow]; ring

/-- `L₂` is continuous away from `s = α` and `s = -α`. -/
theorem DegreeCoordinate.lhsRight_continuousOn (a : ℝ) :
    ContinuousOn (DegreeCoordinate.lhsRight a) {s | 0 ≤ s ∧ s ≠ a ∧ 0 < s + a} := by
  intro s ⟨hs, hsa, hsa'⟩
  have h1 : a^2 - s^2 ≠ 0 := by
    intro h
    have : (a - s) * (a + s) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact hsa (by linarith)
    · linarith
  refine ContinuousAt.continuousWithinAt ?_
  unfold DegreeCoordinate.lhsRight
  exact (continuousAt_id.add (continuousAt_const.mul
    ((continuous_const.sub (continuous_pow 2)).continuousAt.log h1))).sub
    (continuousAt_const.mul ((continuous_id.add continuous_const).continuousAt.log hsa'.ne'))

/-- `L₂'(s) = -s²/(α² - s²)`. -/
theorem DegreeCoordinate.lhsRight_hasDerivAt {a s : ℝ} (hsa : a^2 - s^2 ≠ 0) (hsa' : s + a ≠ 0) :
    HasDerivAt (DegreeCoordinate.lhsRight a) (-s^2/(a^2 - s^2)) s := by
  have h1 : HasDerivAt (fun s : ℝ => a^2 - s^2) (-(2*s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_sub (a^2)
  have h2 : HasDerivAt (fun s : ℝ => s + a) 1 s := (hasDerivAt_id s).add_const a
  have := ((hasDerivAt_id' s).fun_add ((h1.log hsa).const_mul (a/2))).fun_sub
    ((h2.log hsa').const_mul a)
  refine this.congr_deriv ?_
  have : a^2 - s^2 = (a - s) * (s + a) := by ring
  field_simp
  rw [this]
  ring

/-- `L₂` decreases strictly on `[0, α)`. -/
theorem DegreeCoordinate.lhsRight_strictAntiOn {a : ℝ} (ha : 0 < a) : StrictAntiOn
    (DegreeCoordinate.lhsRight a) (Ico 0 a) := by
  refine strictAntiOn_of_deriv_neg (convex_Ico 0 a)
    ((DegreeCoordinate.lhsRight_continuousOn a).mono fun s hs =>
        ⟨hs.1, hs.2.ne, by linarith [hs.1]⟩) ?_
  intro s hs
  rw [interior_Ico] at hs
  have hp : 0 < a^2 - s^2 := by nlinarith [hs.1, hs.2]
  rw [(DegreeCoordinate.lhsRight_hasDerivAt hp.ne' (by linarith [hs.1])).deriv]
  have : 0 < s^2 := by nlinarith [hs.1]
  exact div_neg_of_neg_of_pos (by linarith) hp

/-- `L₂` increases strictly on `(α, ∞)`. -/
theorem DegreeCoordinate.lhsRight_strictMonoOn {a : ℝ} (ha : 0 ≤ a) : StrictMonoOn
    (DegreeCoordinate.lhsRight a) (Ioi a) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi a)
    ((DegreeCoordinate.lhsRight_continuousOn a).mono fun s hs =>
        ⟨by have : a < s := hs; linarith, (ne_of_gt hs),
      by have : a < s := hs; linarith⟩) ?_
  intro s hs
  rw [interior_Ioi] at hs
  have hs : a < s := hs
  have hp : a^2 - s^2 < 0 := by nlinarith
  rw [(DegreeCoordinate.lhsRight_hasDerivAt hp.ne (by linarith)).deriv]
  have : 0 < s^2 := by nlinarith
  exact div_pos_of_neg_of_neg (by linarith) hp

/-- `L₂ → -∞` at `s = α`. -/
theorem DegreeCoordinate.lhsRight_tendsto_nhdsNE {a : ℝ} (ha : 0 < a) : Tendsto
    (DegreeCoordinate.lhsRight a) (𝓝[≠] a) atBot := by
  have h1 : Tendsto (fun s : ℝ => a^2 - s^2) (𝓝[≠] a) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_const.sub (continuous_pow 2)).tendsto a (f := fun s : ℝ => a^2 - s^2))
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds (show 0 < a from ha))]
        with s hs hs0
      have hs0 : 0 < s := hs0
      have hs : s ≠ a := hs
      intro h
      have h : a^2 - s^2 = 0 := h
      have : (a - s) * (a + s) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h | h
      · exact hs (by linarith)
      · linarith
  have h2 := (Real.tendsto_log_nhdsNE_zero.comp h1).const_mul_atBot (show 0 < a/2 by positivity)
  have h3 : Tendsto (fun s : ℝ => s - a * Real.log (s + a)) (𝓝[≠] a)
      (𝓝 (a - a * Real.log (a + a))) := by
    refine ContinuousAt.tendsto ?_ |>.mono_left nhdsWithin_le_nhds
    exact continuousAt_id.sub (continuousAt_const.mul
      ((continuous_id.add continuous_const).continuousAt.log (by simp; linarith)))
  refine (h2.atBot_add h3).congr fun s => ?_
  simp only [Function.comp, DegreeCoordinate.lhsRight]; ring

/-- A linear lower bound for `L₂` for large `s`. -/
theorem DegreeCoordinate.lhsRight_ge {a s : ℝ} (ha : 0 ≤ a) (hs : 3*a + 1 ≤ s) :
    s - a/2 * Real.log 2 ≤ DegreeCoordinate.lhsRight a s := by
  have h1 : 0 < s - a := by linarith
  have h2 : 0 < s + a := by linarith
  have e : Real.log (a^2 - s^2) = Real.log (s - a) + Real.log (s + a) := by
    rw [← Real.log_mul h1.ne' h2.ne', ← Real.log_neg_eq_log]; congr 1; ring
  have h3 : Real.log (s + a) - Real.log 2 ≤ Real.log (s - a) := by
    rw [← Real.log_div h2.ne' two_ne_zero]
    exact Real.log_le_log (by positivity) (by linarith)
  unfold DegreeCoordinate.lhsRight
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h3 ha]

/-- `L₂ → ∞` at `∞`. -/
theorem DegreeCoordinate.lhsRight_tendsto_atTop {a : ℝ} (ha : 0 ≤ a) : Tendsto
    (DegreeCoordinate.lhsRight a) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-(a/2 * Real.log 2)) tendsto_id)
  filter_upwards [eventually_ge_atTop (3*a+1)] with s hs
  have := DegreeCoordinate.lhsRight_ge ha hs
  simp only [id]; linarith

/-- Right side of 14.15.21. -/
noncomputable def DegreeCoordinate.rhsLeft (a x : ℝ) : ℝ :=
  Real.arccos (x/Real.sqrt (1-a^2))-a/2*Real.arccos (((1+a^2)*x^2-1+a^2)/((1-a^2)*(1-x^2)))

/-- Right side of 14.15.22. -/
noncomputable def DegreeCoordinate.rhsRight (a x : ℝ) : ℝ :=
  Real.log ((x+Real.sqrt (x^2-1+a^2))/Real.sqrt (1-a^2))+a/2*Real.log
      ((1-a^2)*|1-x^2|/((1+a^2)*x^2-1+a^2+2*a*x*Real.sqrt (x^2-1+a^2)))

/-- `√(1-α²) > 0`. -/
theorem DegreeCoordinate.turningPoint_pos {a : ℝ} (ha1 : a < 1) (ha : 0 ≤ a) : 0 <
    Real.sqrt (1 - a^2) :=
  Real.sqrt_pos.2 (by nlinarith)

/-- `√(1-α²)² = 1-α²`. -/
theorem DegreeCoordinate.turningPoint_sq {a : ℝ} (ha1 : a < 1) (ha : 0 ≤ a) : Real.sqrt (1 - a^2)
    ^ 2 = 1 - a^2 :=
  Real.sq_sqrt (by nlinarith)

/-- The right side of 14.15.21 vanishes at `x = √(1-α²)`. -/
theorem DegreeCoordinate.rhsLeft_turningPoint {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    DegreeCoordinate.rhsLeft a (Real.sqrt (1 - a^2)) = 0 := by
  have h0 := DegreeCoordinate.turningPoint_pos ha1 ha
  have h2 := DegreeCoordinate.turningPoint_sq ha1 ha
  unfold DegreeCoordinate.rhsLeft
  rw [div_self h0.ne', Real.arccos_one]
  rcases ha.eq_or_lt with rfl | ha
  · simp
  have : ((1+a^2)*Real.sqrt (1 - a^2)^2-1+a^2)/((1-a^2)*(1-Real.sqrt (1 - a^2)^2)) = 1 := by
    rw [h2, div_eq_one_iff_eq (by have : 0 < 1 - a^2 := by nlinarith
                                  have : 0 < a^2 := by positivity
                                  rw [show 1 - (1 - a^2) = a^2 by ring]; positivity)]
    ring
  rw [this, Real.arccos_one]; ring

/-- At `α = 0` the right side of 14.15.21 is `arccos x`. -/
theorem DegreeCoordinate.rhsLeft_zero_alpha (x : ℝ) : DegreeCoordinate.rhsLeft 0 x =
    Real.arccos x := by
  simp [DegreeCoordinate.rhsLeft]

/-- Derivative of the right side of 14.15.21: `-√(1-α²-x²)/(1-x²)`. -/
theorem DegreeCoordinate.rhsLeft_hasDerivAt {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x)
    (hx1 : x < Real.sqrt (1 - a^2)) :
    HasDerivAt (DegreeCoordinate.rhsLeft a) (-Real.sqrt (1 - a^2 - x^2) / (1 - x^2)) x := by
  set c := Real.sqrt (1 - a^2) with hc
  have hc0 : 0 < c := DegreeCoordinate.turningPoint_pos ha1 ha.le
  have hc2 : c^2 = 1 - a^2 := DegreeCoordinate.turningPoint_sq ha1 ha.le
  have hxc : x^2 < 1 - a^2 := by nlinarith
  set V := Real.sqrt (1 - a^2 - x^2) with hV
  have hV0 : 0 < V := Real.sqrt_pos.2 (by linarith)
  have hV2 : V^2 = 1 - a^2 - x^2 := Real.sq_sqrt (by linarith)
  have hx2 : 0 < 1 - x^2 := by nlinarith
  have ha2 : 0 < 1 - a^2 := by nlinarith
  set D := (1 - a^2) * (1 - x^2) with hD
  have hD0 : 0 < D := by positivity
  set N := (1+a^2)*x^2-1+a^2 with hN
  -- first arccos
  have hq1 : x / c < 1 := by rw [div_lt_one hc0]; exact hx1
  have hq1' : -1 < x / c := by have : 0 < x / c := by positivity
                               linarith
  have hd1 := (Real.hasDerivAt_arccos hq1'.ne' hq1.ne).comp x ((hasDerivAt_id x).div_const c)
  have hs1 : Real.sqrt (1 - (x/c)^2) = V / c := by
    rw [show 1 - (x/c)^2 = (V/c)^2 by rw [div_pow, div_pow, hV2, hc2]; field_simp]
    exact Real.sqrt_sq (by positivity)
  -- second arccos
  have hQm : 0 < 1 - N / D := by
    rw [show 1 - N / D = 2 * V^2 / D by rw [hV2]; field_simp; try ring]; positivity
  have hQp : 0 < 1 + N / D := by
    rw [show 1 + N / D = 2 * a^2 * x^2 / D by field_simp; try ring]; positivity
  have hdQ : HasDerivAt (fun x => ((1+a^2)*x^2-1+a^2)/((1-a^2)*(1-x^2)))
      ((2*(1+a^2)*x * D - N * ((1-a^2)*(-(2*x)))) / D^2) x := by
    have h1 : HasDerivAt (fun x : ℝ => (1+a^2)*x^2-1+a^2) (2*(1+a^2)*x) x := by
      have := (((hasDerivAt_pow 2 x).const_mul (1+a^2)).sub_const 1).add_const (a^2)
      convert this using 1; simp; ring
    have h2 : HasDerivAt (fun x : ℝ => (1-a^2)*(1-x^2)) ((1-a^2)*(-(2*x))) x := by
      have := ((hasDerivAt_pow 2 x).const_sub 1).const_mul (1-a^2)
      convert this using 1; simp
    exact h1.div h2 hD0.ne'
  have hd2 := (Real.hasDerivAt_arccos (by linarith : N/D ≠ -1) (by linarith : N/D ≠ 1)).comp x hdQ
  have hs2 : Real.sqrt (1 - (N/D)^2) = 2 * a * x * V / D := by
    rw [show 1 - (N/D)^2 = (2 * a * x * V / D)^2 by
      rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow, hV2]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  have := hd1.sub (hd2.const_mul (a/2))
  refine this.congr_deriv ?_
  simp only [Function.comp_def] at *
  rw [hs1, hs2]
  field_simp
  rw [hD, hN]
  linear_combination (2 * ((1 - a^2) * (1 - x^2))) * hV2

/-- The right side of 14.15.21 decreases strictly on `[0, √(1-α²)]`. -/
theorem DegreeCoordinate.rhsLeft_strictAntiOn {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    StrictAntiOn (DegreeCoordinate.rhsLeft a) (Icc 0 (Real.sqrt (1 - a^2))) := by
  rcases ha.eq_or_lt with rfl | ha
  · intro x hx y hy hxy
    simp only [DegreeCoordinate.rhsLeft_zero_alpha]
    refine Real.strictAntiOn_arccos ⟨by linarith [hx.1], ?_⟩ ⟨by linarith [hy.1], ?_⟩ hxy
    · simpa using hx.2
    · simpa using hy.2
  have hc0 := DegreeCoordinate.turningPoint_pos ha1 ha.le
  have hc2 := DegreeCoordinate.turningPoint_sq ha1 ha.le
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
  · intro x hx
    have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
    have ha2 : 0 < 1 - a^2 := by nlinarith
    have hD : (1 - a^2) * (1 - x^2) ≠ 0 := by positivity
    refine ContinuousAt.continuousWithinAt ?_
    unfold DegreeCoordinate.rhsLeft
    exact (Real.continuous_arccos.continuousAt.comp (continuousAt_id.div_const _)).sub
      (continuousAt_const.mul (Real.continuous_arccos.continuousAt.comp
        ((by fun_prop : Continuous fun x : ℝ => (1+a^2)*x^2-1+a^2).continuousAt.div
          (by fun_prop : Continuous fun x : ℝ => (1-a^2)*(1-x^2)).continuousAt hD)))
  · intro x hx
    rw [interior_Icc] at hx
    rw [(DegreeCoordinate.rhsLeft_hasDerivAt ha ha1 hx.1 hx.2).deriv]
    have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
    have : 0 < Real.sqrt (1 - a^2 - x^2) := Real.sqrt_pos.2 (by nlinarith [hx.1, hx.2])
    exact div_neg_of_neg_of_pos (by linarith) hx2

/-- The right side of 14.15.21 is nonnegative on `[0, √(1-α²)]`. -/
theorem DegreeCoordinate.rhsLeft_nonneg {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : 0 ≤ x)
    (hx1 : x ≤ Real.sqrt (1 - a^2)) : 0 ≤ DegreeCoordinate.rhsLeft a x := by
  rcases hx1.lt_or_eq with h | h
  · rw [← DegreeCoordinate.rhsLeft_turningPoint ha ha1]
    exact (DegreeCoordinate.rhsLeft_strictAntiOn ha ha1 ⟨hx, hx1⟩
        ⟨(DegreeCoordinate.turningPoint_pos ha1 ha).le, le_rfl⟩ h).le
  · rw [h, DegreeCoordinate.rhsLeft_turningPoint ha ha1]

/-- The right side of 14.15.22 without the absolute value (the logarithm is even). -/
theorem DegreeCoordinate.rhsRight_eq (a x : ℝ) : DegreeCoordinate.rhsRight a x =
    Real.log ((x+Real.sqrt (x^2-1+a^2))/Real.sqrt (1-a^2)) +
        a/2*Real.log ((1-a^2)*(1-x^2)/((1+a^2)*x^2-1+a^2+2*a*x*Real.sqrt (x^2-1+a^2))) := by
  unfold DegreeCoordinate.rhsRight
  congr 2
  rcases abs_choice (1 - x^2) with h | h
  · rw [h]
  · rw [h, ← Real.log_neg_eq_log]; congr 1; ring

/-- `√(1-α²) ≤ x ↔ x² - 1 + α² ≥ 0` for `x ≥ 0`. -/
theorem DegreeCoordinate.turningPoint_le_iff {a x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (1 - a^2) ≤ x ↔ 0 ≤ x^2 - 1 + a^2 := by
  rw [Real.sqrt_le_left hx]; constructor <;> intro h <;> linarith

/-- `√(1-α²) < x ↔ x² - 1 + α² > 0` for `x ≥ 0`. -/
theorem DegreeCoordinate.turningPoint_lt_iff {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : 0 ≤ x) :
    Real.sqrt (1 - a^2) < x ↔ 0 < x^2 - 1 + a^2 := by
  have h0 := DegreeCoordinate.turningPoint_pos ha1 ha
  have h2 := DegreeCoordinate.turningPoint_sq ha1 ha
  constructor
  · intro h
    have := pow_lt_pow_left₀ h h0.le two_ne_zero
    linarith
  · intro h
    have := Real.sqrt_lt_sqrt (by nlinarith) (show 1 - a^2 < x^2 by linarith)
    rwa [Real.sqrt_sq hx] at this

/-- Derivative of the right side of 14.15.22: `√(x²-1+α²)/(x²-1)`. -/
theorem DegreeCoordinate.rhsRight_hasDerivAt {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : 0 ≤ x)
    (hx0 : Real.sqrt (1 - a^2) < x) (hx1 : x ≠ 1) :
    HasDerivAt (DegreeCoordinate.rhsRight a) (Real.sqrt (x^2 - 1 + a^2) / (x^2 - 1)) x := by
  have hW0' := (DegreeCoordinate.turningPoint_lt_iff ha ha1 hx).1 hx0
  have hxpos : 0 < x := lt_of_le_of_lt (DegreeCoordinate.turningPoint_pos ha1 ha).le hx0
  set c := Real.sqrt (1 - a^2) with hc
  have hc0 : 0 < c := DegreeCoordinate.turningPoint_pos ha1 ha
  set W := Real.sqrt (x^2 - 1 + a^2) with hW
  have hW0 : 0 < W := Real.sqrt_pos.2 hW0'
  have hW2 : W^2 = x^2 - 1 + a^2 := Real.sq_sqrt hW0'.le
  have hx2 : x^2 - 1 ≠ 0 := by
    intro h
    have : (x - 1) * (x + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact hx1 (by linarith)
    · linarith
  have ha2 : 0 < 1 - a^2 := by nlinarith
  have hG : (1+a^2)*x^2-1+a^2+2*a*x*W = (W + a*x)^2 := by linear_combination (-1) * hW2
  have hG0 : 0 < W + a * x := by positivity
  have hdW : HasDerivAt (fun x => Real.sqrt (x^2 - 1 + a^2)) (2*x / (2*W)) x := by
    have := (((hasDerivAt_pow 2 x).sub_const 1).add_const (a^2)).sqrt hW0'.ne'
    convert this using 1; simp [hW]
  have h1 : HasDerivAt (fun x => (x + Real.sqrt (x^2 - 1 + a^2)) / c) ((1 + 2*x/(2*W)) / c) x :=
    ((hasDerivAt_id x).add hdW).div_const c
  have hG' : HasDerivAt (fun x => (1+a^2)*x^2-1+a^2+2*a*x*Real.sqrt (x^2-1+a^2))
      ((1+a^2)*(2*x) + 2*a*(1*W + x*(2*x/(2*W)))) x := by
    have := ((((hasDerivAt_pow 2 x).const_mul (1+a^2)).sub_const 1).add_const (a^2)).add
      (((hasDerivAt_id x).mul hdW).const_mul (2*a))
    convert this using 1
    · funext y; simp; ring
    · simp [hW]
  have hN' : HasDerivAt (fun x : ℝ => (1-a^2)*(1-x^2)) ((1-a^2)*(-(2*x))) x := by
    have := ((hasDerivAt_pow 2 x).const_sub 1).const_mul (1-a^2)
    convert this using 1; simp
  have hGne : (1+a^2)*x^2-1+a^2+2*a*x*W ≠ 0 := by rw [hG]; positivity
  have h2 := hN'.div hG' hGne
  have hf1 : (x + W) / c ≠ 0 := by positivity
  have hf2 : (1-a^2)*(1-x^2) / ((1+a^2)*x^2-1+a^2+2*a*x*W) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero ha2.ne' ?_) hGne
    intro h; exact hx2 (by linarith)
  have := (h1.log hf1).add ((h2.log hf2).const_mul (a/2))
  rw [show DegreeCoordinate.rhsRight a = _ from funext (DegreeCoordinate.rhsRight_eq a)]
  refine this.congr_deriv ?_
  simp only [Pi.div_apply, ← hW]
  rw [hG]
  have hx2' : 1 - x^2 ≠ 0 := fun h => hx2 (by linarith)
  field_simp
  linear_combination (W^3*(x^2 - 1) + W^2*(a*x^3 - a*x + x^3 - x) + W*(a*x^4 - a*x^2)) * hW2

/-- The right side of 14.15.22 vanishes at `x = √(1-α²)`. -/
theorem DegreeCoordinate.rhsRight_turningPoint {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    DegreeCoordinate.rhsRight a (Real.sqrt (1 - a^2)) = 0 := by
  have h0 := DegreeCoordinate.turningPoint_pos ha1 ha.le
  have h2 := DegreeCoordinate.turningPoint_sq ha1 ha.le
  have hW : Real.sqrt (Real.sqrt (1 - a^2) ^ 2 - 1 + a^2) = 0 := by
    rw [h2]; simp
  unfold DegreeCoordinate.rhsRight
  rw [hW, add_zero, div_self h0.ne', Real.log_one, zero_add, h2,
    show 1 - (1 - a^2) = a^2 by ring, abs_of_pos (by positivity)]
  have : (1 - a^2) * a^2 / ((1 + a^2) * (1 - a^2) - 1 + a^2 + 2 * a * Real.sqrt (1 - a^2) * 0)
      = 1 := by
    rw [div_eq_one_iff_eq (by have : 0 < 1 - a^2 := by nlinarith
                              nlinarith [mul_pos this (show 0 < a^2 by positivity)])]
    ring
  rw [this, Real.log_one, mul_zero]

/-- Continuity of the right side of 14.15.22. -/
theorem DegreeCoordinate.rhsRight_continuousAt {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx1 : x ≠ 1)
    (hx1' : x ≠ -1)
    (hpos : 0 < x + Real.sqrt (x^2-1+a^2))
    (hG : (1+a^2)*x^2-1+a^2+2*a*x*Real.sqrt (x^2-1+a^2) ≠ 0) :
    ContinuousAt (DegreeCoordinate.rhsRight a) x := by
  have ha2 : 0 < Real.sqrt (1 - a^2) := Real.sqrt_pos.2 (by nlinarith)
  have hab : |1 - x^2| ≠ 0 := by
    rw [abs_ne_zero]; intro h
    have : (1 - x) * (1 + x) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact hx1 (by linarith)
    · exact hx1' (by linarith)
  have ha3 : 1 - a^2 ≠ 0 := by nlinarith
  unfold DegreeCoordinate.rhsRight
  refine ContinuousAt.add ?_ (continuousAt_const.mul ?_)
  · exact ((by fun_prop : Continuous fun x : ℝ => (x + Real.sqrt (x^2-1+a^2)) /
      Real.sqrt (1-a^2)).continuousAt).log (by positivity)
  · refine ContinuousAt.log ?_ (div_ne_zero (mul_ne_zero ha3 hab) hG)
    exact ((by fun_prop : Continuous fun x : ℝ => (1-a^2)*|1-x^2|).continuousAt).div
      ((by fun_prop : Continuous fun x : ℝ =>
        (1+a^2)*x^2-1+a^2+2*a*x*Real.sqrt (x^2-1+a^2)).continuousAt) hG

/-- For `x ≥ √(1-α²)` the denominator in 14.15.22 is the square `(W + αx)²`. -/
theorem DegreeCoordinate.denominator_eq_sq {a x : ℝ} (hW : 0 ≤ x^2 - 1 + a^2) :
    (1+a^2)*x^2-1+a^2+2*a*x*Real.sqrt (x^2-1+a^2) = (Real.sqrt (x^2-1+a^2) + a*x)^2 := by
  have := Real.sq_sqrt hW
  linear_combination (-1) * this

/-- The right side of 14.15.22 decreases strictly on `[√(1-α²), 1)`. -/
theorem DegreeCoordinate.rhsRight_strictAntiOn {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    StrictAntiOn (DegreeCoordinate.rhsRight a) (Ico (Real.sqrt (1 - a^2)) 1) := by
  have h0 := DegreeCoordinate.turningPoint_pos ha1 ha.le
  refine strictAntiOn_of_deriv_neg (convex_Ico _ _) ?_ ?_
  · intro x hx
    have hx0 : 0 ≤ x := h0.le.trans hx.1
    have hW := (DegreeCoordinate.turningPoint_le_iff hx0).1 hx.1
    refine (DegreeCoordinate.rhsRight_continuousAt ha.le ha1 hx.2.ne (by linarith) ?_
        ?_).continuousWithinAt
    · have := Real.sqrt_nonneg (x^2-1+a^2); linarith [lt_of_lt_of_le h0 hx.1]
    · rw [DegreeCoordinate.denominator_eq_sq hW]
      have : 0 < a * x := mul_pos ha (lt_of_lt_of_le h0 hx.1)
      have := Real.sqrt_nonneg (x^2-1+a^2)
      positivity
  · intro x hx
    rw [interior_Ico] at hx
    have hx0 : 0 ≤ x := h0.le.trans hx.1.le
    rw [(DegreeCoordinate.rhsRight_hasDerivAt ha.le ha1 hx0 hx.1 hx.2.ne).deriv]
    have hW := (DegreeCoordinate.turningPoint_lt_iff ha.le ha1 hx0).1 hx.1
    exact div_neg_of_pos_of_neg (Real.sqrt_pos.2 hW) (by nlinarith [hx.2])

/-- The right side of 14.15.22 is negative on `(√(1-α²), 1)`. -/
theorem DegreeCoordinate.rhsRight_neg {a x : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx0 : Real.sqrt (1 - a^2) < x)
    (hx1 : x < 1) : DegreeCoordinate.rhsRight a x < 0 := by
  rw [← DegreeCoordinate.rhsRight_turningPoint ha ha1]
  exact DegreeCoordinate.rhsRight_strictAntiOn ha ha1 ⟨le_rfl, by
    have := DegreeCoordinate.turningPoint_sq ha1 ha.le
    nlinarith [DegreeCoordinate.turningPoint_pos ha1 ha.le]⟩ ⟨hx0.le, hx1⟩ hx0

/-- `√(1-α²) ≤ 1`. -/
theorem DegreeCoordinate.turningPoint_le_one (a : ℝ) : Real.sqrt (1 - a^2) ≤ 1 := by
  rw [Real.sqrt_le_one]; nlinarith

/-- The right side of 14.15.22 increases strictly on `(1, ∞)`. -/
theorem DegreeCoordinate.rhsRight_strictMonoOn {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    StrictMonoOn (DegreeCoordinate.rhsRight a) (Ioi 1) := by
  have hd : ∀ x ∈ Ioi (1:ℝ), HasDerivAt (DegreeCoordinate.rhsRight a)
      (Real.sqrt (x^2 - 1 + a^2) / (x^2 - 1)) x := fun x hx =>
    DegreeCoordinate.rhsRight_hasDerivAt ha ha1 (by linarith [show (1:ℝ) < x from hx])
      (lt_of_le_of_lt (DegreeCoordinate.turningPoint_le_one a) hx) (ne_of_gt hx)
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [interior_Ioi] at hx
  rw [(hd x hx).deriv]
  have hx : (1:ℝ) < x := hx
  exact div_pos (Real.sqrt_pos.2 (by nlinarith)) (by nlinarith)

/-- The right side of 14.15.22 tends to `∞`. -/
theorem DegreeCoordinate.rhsRight_tendsto_atTop {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (DegreeCoordinate.rhsRight a) atTop atTop := by
  set c := Real.sqrt (1 - a^2)
  have hc0 : 0 < c := DegreeCoordinate.turningPoint_pos ha1 ha
  have ha2 : 0 < 1 - a^2 := by nlinarith
  set k := 3 * (1 - a^2) / 16
  have hk : 0 < k := by positivity
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (- Real.log c + a/2 * Real.log k)
    Real.tendsto_log_atTop)
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
  have hW0 : 0 ≤ x^2 - 1 + a^2 := by nlinarith
  set W := Real.sqrt (x^2 - 1 + a^2) with hWd
  have hW : 0 ≤ W := Real.sqrt_nonneg _
  have hWx : W ≤ x := by
    rw [hWd, Real.sqrt_le_left (by linarith)]; nlinarith
  have h1 : Real.log x - Real.log c ≤ Real.log ((x + W) / c) := by
    rw [← Real.log_div (by linarith) hc0.ne']
    exact Real.log_le_log (by positivity) (by gcongr; linarith)
  have hG : (1+a^2)*x^2-1+a^2+2*a*x*W = (W + a*x)^2 := DegreeCoordinate.denominator_eq_sq hW0
  have hGpos : 0 < (W + a*x)^2 := by
    have : 0 < W + a*x := by
      rcases ha.eq_or_lt with rfl | ha'
      · simp only [zero_mul, add_zero]; exact Real.sqrt_pos.2 (by nlinarith)
      · positivity
    positivity
  have h2 : k ≤ (1-a^2)*|1-x^2|/((1+a^2)*x^2-1+a^2+2*a*x*W) := by
    rw [hG, le_div_iff₀ hGpos, abs_of_neg (by nlinarith)]
    have : (W + a*x)^2 ≤ 4 * x^2 := by
      have h5 : W + a*x ≤ 2*x := by nlinarith
      have h6 := pow_le_pow_left₀ (by positivity) h5 2
      linarith [show (2*x)^2 = 4*x^2 by ring]
    have : 3 * x^2 / 4 ≤ -(1 - x^2) := by nlinarith
    simp only [k]
    nlinarith [mul_le_mul_of_nonneg_left this ha2.le]
  have h3 : a/2 * Real.log k ≤ a/2 * Real.log ((1-a^2)*|1-x^2|/((1+a^2)*x^2-1+a^2+2*a*x*W)) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hk h2) (by positivity)
  show Real.log x + (-Real.log c + a/2 * Real.log k) ≤ DegreeCoordinate.rhsRight a x
  unfold DegreeCoordinate.rhsRight
  linarith

/-- At `α = 0` the right side of 14.15.22 is positive for `x > 1`. -/
theorem DegreeCoordinate.rhsRight_pos_zero {x : ℝ} (hx : 1 < x) : 0 <
    DegreeCoordinate.rhsRight 0 x := by
  simp only [DegreeCoordinate.rhsRight]
  norm_num
  apply Real.log_pos
  have : 0 < Real.sqrt (x^2 - 1) := Real.sqrt_pos.2 (by nlinarith)
  linarith

/-- The relation at `x = 1`. -/
theorem DegreeCoordinate.relation_one (a y : ℝ) : LegendreYRelation a 1 y ↔ y = 0 := by
  simp [LegendreYRelation]

/-- The relation for `x ≤ √(1-α²)`, `x ≠ 1`, through `L₁`. -/
theorem DegreeCoordinate.relation_left {a x y : ℝ} (hx1 : x ≠ 1) (hx0 : x ≤ Real.sqrt (1 - a^2)) :
    LegendreYRelation a x y ↔ a^2 ≤ y ∧ DegreeCoordinate.lhsLeft a (Real.sqrt (y - a^2)) =
        DegreeCoordinate.rhsLeft a x := by
  simp only [LegendreYRelation, hx1, hx0, ↓reduceIte]; rfl

/-- The left side of 14.15.22 through `L₂`. -/
theorem DegreeCoordinate.lhsRight_sqrt {a y : ℝ} (hy : y ≤ a^2) :
    Real.sqrt (a^2-y)+a/2*Real.log |y|-a*Real.log (Real.sqrt (a^2-y)+a)
      = DegreeCoordinate.lhsRight a (Real.sqrt (a^2-y)) := by
  unfold DegreeCoordinate.lhsRight
  rw [Real.sq_sqrt (by linarith), Real.log_abs, show a^2 - (a^2 - y) = y by ring]

/-- The relation for `x > √(1-α²)`, `x ≠ 1`, through `L₂`. -/
theorem DegreeCoordinate.relation_right {a x y : ℝ} (hx1 : x ≠ 1)
    (hx0 : ¬ x ≤ Real.sqrt (1 - a^2)) :
    LegendreYRelation a x y ↔ y ≤ a^2 ∧ (x < 1 → 0 < y) ∧ (1 < x → y < 0) ∧
      DegreeCoordinate.lhsRight a (Real.sqrt (a^2-y)) = DegreeCoordinate.rhsRight a x := by
  simp only [LegendreYRelation, hx1, hx0, ↓reduceIte]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, by rw [← DegreeCoordinate.lhsRight_sqrt h1]; exact h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, by rw [DegreeCoordinate.lhsRight_sqrt h1]; exact h4⟩

/-- Existence and uniqueness of the solution of 14.15.21–22. -/
theorem DegreeCoordinate.existsUnique {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : 0 ≤ x) :
    (∃ y, LegendreYRelation a x y) ∧
      ∀ y₁ y₂, LegendreYRelation a x y₁ → LegendreYRelation a x y₂ → y₁ = y₂ := by
  have hc0 := DegreeCoordinate.turningPoint_pos ha1 ha
  have hc1 := DegreeCoordinate.turningPoint_le_one a
  by_cases h1 : x = 1
  · subst h1
    simp only [DegreeCoordinate.relation_one]
    exact ⟨⟨0, rfl⟩, fun y₁ y₂ h₁ h₂ => h₁.trans h₂.symm⟩
  by_cases h0 : x ≤ Real.sqrt (1 - a^2)
  · simp only [DegreeCoordinate.relation_left h1 h0]
    refine ⟨?_, fun y₁ y₂ h₁ h₂ => ?_⟩
    · obtain ⟨s, hs, hsv⟩ :=
          DegreeCoordinate.lhsLeft_surj ha (DegreeCoordinate.rhsLeft_nonneg ha ha1 hx h0)
      refine ⟨a^2 + s^2, by nlinarith, ?_⟩
      rw [show a^2 + s^2 - a^2 = s^2 by ring, Real.sqrt_sq hs, hsv]
    · have := (DegreeCoordinate.lhsLeft_strictMonoOn ha).injOn (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
        (h₁.2.trans h₂.2.symm)
      have := (Real.sqrt_inj (by linarith [h₁.1]) (by linarith [h₂.1])).1 this
      linarith
  simp only [DegreeCoordinate.relation_right h1 h0]
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · -- `√(1-α²) < x < 1`, so `α > 0`
    have ha0 : 0 < a := by
      rcases ha.eq_or_lt with rfl | h
      · exfalso; apply h0; simp; linarith
      · exact h
    have hv := DegreeCoordinate.rhsRight_neg ha0 ha1 (not_le.1 h0) hlt
    have hsl : ∀ y, 0 < y → y ≤ a^2 → Real.sqrt (a^2 - y) ∈ Ico 0 a := by
      intro y hy hya
      refine ⟨Real.sqrt_nonneg _, ?_⟩
      rw [Real.sqrt_lt' ha0]; linarith
    refine ⟨?_, fun y₁ y₂ h₁ h₂ => ?_⟩
    · obtain ⟨s₁, hs₁, hs₁a⟩ := (((DegreeCoordinate.lhsRight_tendsto_nhdsNE ha0).mono_left
        (nhdsWithin_mono _ (show Iio a ⊆ ({a}ᶜ : Set ℝ) from fun s (hs : s < a) =>
            ne_of_lt hs))).eventually
        (eventually_lt_atBot (DegreeCoordinate.rhsRight a x)) |>.and (Ioo_mem_nhdsLT ha0)).exists
      have hcont : ContinuousOn (DegreeCoordinate.lhsRight a) (Icc 0 s₁) :=
        (DegreeCoordinate.lhsRight_continuousOn a).mono fun s hs =>
          ⟨hs.1, ne_of_lt (lt_of_le_of_lt hs.2 hs₁a.2), by linarith [hs.1]⟩
      obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc' hs₁a.1.le hcont
        (show DegreeCoordinate.rhsRight a x ∈
            Icc (DegreeCoordinate.lhsRight a s₁) (DegreeCoordinate.lhsRight a 0) from
          ⟨hs₁.le, by rw [DegreeCoordinate.lhsRight_zero]; exact hv.le⟩)
      have hsa : s < a := lt_of_le_of_lt hs.2 hs₁a.2
      refine ⟨a^2 - s^2, by nlinarith [hs.1], fun _ => by nlinarith [hs.1], fun h => absurd h
        (by linarith), ?_⟩
      rw [show a^2 - (a^2 - s^2) = s^2 by ring, Real.sqrt_sq hs.1, hsv]
    · have e₁ := h₁.2.1 hlt
      have e₂ := h₂.2.1 hlt
      have := (DegreeCoordinate.lhsRight_strictAntiOn ha0).injOn (hsl _ e₁ h₁.1) (hsl _ e₂ h₂.1)
        (h₁.2.2.2.trans h₂.2.2.2.symm)
      have := (Real.sqrt_inj (by linarith [h₁.1]) (by linarith [h₂.1])).1 this
      linarith
  · -- `x > 1`
    have hsr : ∀ y, y < 0 → Real.sqrt (a^2 - y) ∈ Ioi a := by
      intro y hy
      show a < Real.sqrt (a^2 - y)
      calc a = Real.sqrt (a^2) := (Real.sqrt_sq ha).symm
        _ < _ := Real.sqrt_lt_sqrt (by positivity) (by linarith)
    refine ⟨?_, fun y₁ y₂ h₁ h₂ => ?_⟩
    · set v := DegreeCoordinate.rhsRight a x
      obtain ⟨s₁, hs₁a, hs₁⟩ : ∃ s₁, a < s₁ ∧ DegreeCoordinate.lhsRight a s₁ < v := by
        rcases ha.eq_or_lt with ha0 | ha0
        · subst ha0
          have hv := DegreeCoordinate.rhsRight_pos_zero hgt
          refine ⟨v/2, by positivity, ?_⟩
          simp only [DegreeCoordinate.lhsRight]; simp; linarith
        · obtain ⟨s₁, hs₁, hs₁a⟩ := (((DegreeCoordinate.lhsRight_tendsto_nhdsNE ha0).mono_left
            (nhdsWithin_mono _ (show Ioi a ⊆ ({a}ᶜ : Set ℝ) from fun s (hs : a < s) =>
                ne_of_gt hs))).eventually
            (eventually_lt_atBot v) |>.and self_mem_nhdsWithin).exists
          exact ⟨s₁, hs₁a, hs₁⟩
      obtain ⟨s₂, hs₂, hs₂a⟩ :=
          ((DegreeCoordinate.lhsRight_tendsto_atTop ha).eventually (eventually_gt_atTop v)
        |>.and (eventually_ge_atTop s₁)).exists
      have hcont : ContinuousOn (DegreeCoordinate.lhsRight a) (Icc s₁ s₂) :=
        (DegreeCoordinate.lhsRight_continuousOn a).mono fun s hs =>
          ⟨by linarith [hs.1], ne_of_gt (lt_of_lt_of_le hs₁a hs.1), by linarith [hs.1]⟩
      obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc hs₂a hcont ⟨hs₁.le, hs₂.le⟩
      have hsa : a < s := lt_of_lt_of_le hs₁a hs.1
      refine ⟨a^2 - s^2, by nlinarith, fun h => absurd h (by linarith), fun _ => by nlinarith, ?_⟩
      rw [show a^2 - (a^2 - s^2) = s^2 by ring, Real.sqrt_sq (by linarith), hsv]
    · have e₁ := h₁.2.2.1 hgt
      have e₂ := h₂.2.2.1 hgt
      have := (DegreeCoordinate.lhsRight_strictMonoOn ha).injOn (hsr _ e₁) (hsr _ e₂)
        (h₁.2.2.2.trans h₂.2.2.2.symm)
      have := (Real.sqrt_inj (by linarith [h₁.1]) (by linarith [h₂.1])).1 this
      linarith

end DLMF.Legendre
end
