/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import DLMF.Legendre.Conical
public import DLMF.ParabolicCylinder.WeberUniform
public import DLMFMathlib.Analysis.Calculus.DoubleZeroSqrt

/-!
# Coordinate changes and envelopes for Legendre uniform approximations

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

open DLMF.Bessel DLMF.Confluent

/-- legendreOrderAlpha. -/
@[dlmf 14.15.E5]
def legendreOrderAlpha (ν μ : ℝ) : ℝ :=
  (ν+1/2)/μ

/-- legendreOrderP. -/
@[dlmf 14.15.E6]
def legendreOrderP (α x : ℝ) : ℝ :=
  x/Real.sqrt (α^2*x^2+1-α^2)

/-- legendreOrderRho. -/
@[dlmf 14.15.E7]
def legendreOrderRho (α x : ℝ) : ℝ :=
  let p:=legendreOrderP α x; Real.log ((1+p)/(1-p))/2+α/2*Real.log ((1-α*p)/(1+α*p))

/-- LegendreEtaRelation. -/
@[dlmf 14.15.E10]
def LegendreEtaRelation (α x η : ℝ) : Prop :=
  α*Real.log (Real.sqrt (α^2+η^2)+α)-α*Real.log η-Real.sqrt (α^2+η^2) = Real.log (((1+α^2)*x^2+1-α^2-2*x*Real.sqrt (α^2*x^2-α^2+1))/((x^2-1)*(1-α^2)))/2+α/2*Real.log ((α^2*(2*x^2-1)+1+2*α*x*Real.sqrt (α^2*x^2-α^2+1))/(1-α^2))

/-- legendreOrderEta. -/
@[dlmf 14.15.E10]
def legendreOrderEta (α x : ℝ) : ℝ :=
  Classical.epsilon (fun η : ℝ => 0 < η ∧ LegendreEtaRelation α x η)

/-- The left side of DLMF 14.15.10 as a function of `η`. -/
noncomputable def legO_L (α η : ℝ) : ℝ :=
  α*Real.log (Real.sqrt (α^2+η^2)+α)-α*Real.log η-Real.sqrt (α^2+η^2)

/-- `L'(η) = -√(α²+η²)/η`. -/
lemma legO_hasDerivAt {α η : ℝ} (hα : 0 ≤ α) (hη : 0 < η) :
    HasDerivAt (legO_L α) (-(Real.sqrt (α^2+η^2)/η)) η := by
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
  · funext y; simp only [legO_L, Pi.sub_apply]
  · rw [← hs]
    field_simp
    linear_combination (-s) * hs2

/-- `L` decreases strictly on `(0, ∞)`. -/
lemma legO_strictAntiOn {α : ℝ} (hα : 0 ≤ α) : StrictAntiOn (legO_L α) (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun η hη => (legO_hasDerivAt hα hη).continuousAt.continuousWithinAt) fun η hη => ?_
  rw [interior_Ioi] at hη
  have hη : (0:ℝ) < η := hη
  rw [(legO_hasDerivAt hα hη).deriv, neg_lt_zero]
  have : 0 < Real.sqrt (α^2+η^2) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- `L → ∞` as `η → 0⁺` when `α > 0`. -/
lemma legO_tendsto_zero {α : ℝ} (hα : 0 < α) : Tendsto (legO_L α) (𝓝[>] 0) atTop := by
  have hg : ContinuousAt (fun η : ℝ => α*Real.log (Real.sqrt (α^2+η^2)+α) - Real.sqrt (α^2+η^2)) 0 := by
    have h : Real.sqrt (α^2+0^2)+α ≠ 0 := by positivity
    fun_prop (disch := exact h)
  have := (Real.tendsto_log_nhdsGT_zero.const_mul_atBot_of_neg (show -α < 0 by linarith)).atTop_add
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
  refine this.congr fun η => ?_
  simp only [legO_L]; ring

/-- `L → -∞` as `η → ∞`. -/
lemma legO_tendsto_atTop {α : ℝ} (hα : 0 ≤ α) : Tendsto (legO_L α) atTop atBot := by
  have hb : ∀ᶠ η in atTop, legO_L α η ≤ α*Real.log 3 - η := by
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
    simp only [legO_L]
    rw [← hs]
    nlinarith
  exact tendsto_atBot_mono' _ hb (tendsto_atBot_add_const_left _ _ tendsto_neg_atTop_atBot)

/-- The right side of DLMF 14.15.10 as a function of `x`. -/
noncomputable def legO_R (α x : ℝ) : ℝ :=
  Real.log (((1+α^2)*x^2+1-α^2-2*x*Real.sqrt (α^2*x^2-α^2+1))/((x^2-1)*(1-α^2)))/2+α/2*Real.log ((α^2*(2*x^2-1)+1+2*α*x*Real.sqrt (α^2*x^2-α^2+1))/(1-α^2))

/-- legendreOrderEta spec. -/
@[dlmf 14.15.E10]
theorem legendreOrderEta_spec {α x : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hx : 1 < x) :
    0 < legendreOrderEta α x ∧ LegendreEtaRelation α x (legendreOrderEta α x) ∧ ∀ η : ℝ, 0 < η → LegendreEtaRelation α x η → η=legendreOrderEta α x := by
  have hrel : ∀ η, LegendreEtaRelation α x η ↔ legO_L α η = legO_R α x := fun η => Iff.rfl
  have hex : ∃ η : ℝ, 0 < η ∧ LegendreEtaRelation α x η := by
    rcases hα.lt_or_eq with hα | hα
    · obtain ⟨η, hη, h⟩ := dblZero_exists_eq_of_tendsto (f := fun η => -legO_L α η)
        (fun η hη => (legO_hasDerivAt hα.le hη).continuousAt.neg.continuousWithinAt)
        (tendsto_neg_atTop_atBot.comp (legO_tendsto_zero hα))
        (tendsto_neg_atBot_atTop.comp (legO_tendsto_atTop hα.le)) (-legO_R α x)
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
  exact (legO_strictAntiOn hα).injOn hη hs.1 (((hrel η).1 h).trans ((hrel _).1 hs.2).symm)

/-- The first logarithm argument in DLMF 14.15.10 is positive for `x > 1`. -/
lemma legO_N_pos {α x : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hx : 1 < x) :
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
lemma legO_R_hasDerivAt {α x : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hx : 1 < x) :
    HasDerivAt (legO_R α) (Real.sqrt (α^2*x^2-α^2+1)/(x^2-1)) x := by
  have hB : 0 < 1 - α^2 := by nlinarith
  have hx2 : 0 < x^2 - 1 := by nlinarith
  have hWp : 0 < α^2*x^2-α^2+1 := by nlinarith [mul_nonneg (sq_nonneg α) hx2.le]
  set W := Real.sqrt (α^2*x^2-α^2+1) with hWdef
  have hW0 : 0 < W := Real.sqrt_pos.2 hWp
  have hW : W^2 = α^2*x^2-α^2+1 := Real.sq_sqrt hWp.le
  have hN := legO_N_pos hα hα1 hx
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
  · funext y; simp [legO_R]
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
lemma legO_ratio {α x : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hx : 1 < x) :
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
lemma legO_R_tendsto_one {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    Tendsto (legO_R α) (𝓝[>] (1:ℝ)) atBot := by
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
  have h2 : ContinuousAt (fun x : ℝ => α/2*Real.log ((α^2*(2*x^2-1)+1+2*α*x*Real.sqrt (α^2*x^2-α^2+1))/(1-α^2))) 1 := by
    have hP : (α^2*(2*1^2-1)+1+2*α*1*Real.sqrt (α^2*1^2-α^2+1))/(1-α^2) ≠ 0 := by
      rw [show α^2*(1:ℝ)^2-α^2+1 = 1 by ring, Real.sqrt_one]
      exact div_ne_zero (by nlinarith) hB.ne'
    have hB' : (1:ℝ) - α^2 ≠ 0 := hB.ne'
    fun_prop (disch := assumption)
  refine (hl.atBot_add (h2.tendsto.mono_left nhdsWithin_le_nhds)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp, legO_R]
  rw [legO_ratio hα hα1 hx]

/-- `R → ∞` as `x → ∞` when `α > 0`. -/
lemma legO_R_tendsto_atTop {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (legO_R α) atTop atTop := by
  have hB : 0 < 1 - α^2 := by nlinarith
  have hb : ∀ᶠ x in atTop, Real.log ((1-α^2)/8)/2 + α/2*Real.log (α^2*x^2) ≤ legO_R α x := by
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
      nlinarith [mul_nonneg (sq_nonneg α) (sq_nonneg x), mul_nonneg (mul_nonneg (sq_nonneg α) (sq_nonneg x)) (sq_nonneg α), mul_nonneg (sq_nonneg α) hx2.le]
    simp only [legO_R]
    rw [legO_ratio hα.le hα1 hx1, ← hWdef]
    nlinarith
  refine tendsto_atTop_mono' _ hb (tendsto_atTop_add_const_left _ _ ?_)
  refine (Real.tendsto_log_atTop.comp ?_).const_mul_atTop (by positivity)
  exact (tendsto_pow_atTop (two_ne_zero)).const_mul_atTop (by positivity)

/-- `L` at `α = 0`. -/
lemma legO_L_zero (b : ℝ) (hb : 0 < b) : legO_L 0 b = -b := by
  simp [legO_L, Real.sqrt_sq hb.le]

/-- `R` at `α = 0`. -/
lemma legO_R_zero {x : ℝ} (hx : 1 < x) : legO_R 0 x = Real.log ((x-1)/(x+1))/2 := by
  have h2 : 0 < x + 1 := by linarith
  simp only [legO_R, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero,
    zero_add, Real.sqrt_one, add_zero, mul_one, zero_div, one_mul]
  rw [show (x^2+1-2*x)/(x^2-1) = (x-1)/(x+1) by
    rw [div_eq_div_iff (by nlinarith) h2.ne']; ring]

/-- Eventually `R(x) > L(b)` for every `b > 0`. -/
lemma legO_R_eventually_gt {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, legO_L α b < legO_R α x := by
  rcases hα.lt_or_eq with hα | hα
  · exact (legO_R_tendsto_atTop hα hα1).eventually (eventually_gt_atTop _)
  · subst hα
    rw [legO_L_zero b hb]
    have hq : Tendsto (fun x : ℝ => 1 - 2/(x+1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub ((tendsto_const_nhds (x := (2:ℝ))).div_atTop
        (tendsto_atTop_add_const_right _ 1 tendsto_id))
    rw [sub_zero] at hq
    have hl := ((Real.continuousAt_log one_ne_zero).tendsto.comp hq).div_const 2
    rw [Real.log_one, zero_div] at hl
    filter_upwards [hl.eventually (lt_mem_nhds (show -b < 0 by linarith)), eventually_gt_atTop 1]
      with x hx hx1
    rw [legO_R_zero hx1]
    simp only [Function.comp] at hx
    rwa [show (x-1)/(x+1) = 1 - 2/(x+1) by field_simp; ring]

/-- One-to-one correspondence and endpoint behavior in DLMF 14.15(ii). -/
theorem legendreOrderEta_bijective {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    Set.BijOn (legendreOrderEta α) (Ioi 1) (Ioi 0) ∧ StrictAntiOn (legendreOrderEta α) (Ioi 1) ∧ Tendsto (legendreOrderEta α) (𝓝[>] 1) atTop ∧ Tendsto (legendreOrderEta α) atTop (𝓝 0) := by
  have hE : ∀ x ∈ Ioi (1:ℝ), 0 < legendreOrderEta α x ∧ legO_L α (legendreOrderEta α x) = legO_R α x :=
    fun x hx => ⟨(legendreOrderEta_spec hα hα1 hx).1, (legendreOrderEta_spec hα hα1 hx).2.1⟩
  have hL := legO_strictAntiOn hα
  have hRc : ContinuousOn (legO_R α) (Ioi 1) :=
    fun x hx => (legO_R_hasDerivAt hα hα1 hx).continuousAt.continuousWithinAt
  have hR : StrictMonoOn (legO_R α) (Ioi 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi _) hRc fun x hx => ?_
    rw [interior_Ioi] at hx
    have hx : (1:ℝ) < x := hx
    rw [(legO_R_hasDerivAt hα hα1 hx).deriv]
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
    obtain ⟨a, ha, haI⟩ := (((legO_R_tendsto_one hα hα1).eventually
      (eventually_lt_atBot (legO_L α e))).and hI).exists
    obtain ⟨b, hb, hab⟩ := ((legO_R_eventually_gt hα hα1 he).and (eventually_ge_atTop a)).exists
    have hsub : Icc a b ⊆ Ioi (1:ℝ) := fun x hx => lt_of_lt_of_le haI hx.1
    obtain ⟨c, hc, hcy⟩ := intermediate_value_Icc hab (hRc.mono hsub) ⟨ha.le, hb.le⟩
    exact ⟨c, hsub hc, ((legendreOrderEta_spec hα hα1 (hsub hc)).2.2 e he hcy.symm).symm⟩
  · refine tendsto_atTop.2 fun M => ?_
    have hM : (0:ℝ) < max M 1 := lt_max_of_lt_right one_pos
    filter_upwards [(legO_R_tendsto_one hα hα1).eventually
      (eventually_lt_atBot (legO_L α (max M 1))), hI] with x hx hxI
    rw [← (hE x hxI).2] at hx
    exact (le_max_left _ _).trans ((hL.lt_iff_gt (hE x hxI).1 hM).1 hx).le
  · refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · filter_upwards [eventually_gt_atTop 1] with x hx
      exact ha.trans (hE x hx).1
    · filter_upwards [legO_R_eventually_gt hα hα1 hb, eventually_gt_atTop 1] with x hx hxI
      rw [← (hE x hxI).2] at hx
      exact (hL.lt_iff_gt hb (hE x hxI).1).1 hx

/-- legendreDegreeAlpha. -/
@[dlmf 14.15.E19]
def legendreDegreeAlpha (ν μ : ℝ) : ℝ :=
  μ/(ν+1/2)

/-- legendreDegreeBeta. -/
@[dlmf 14.15.E20]
def legendreDegreeBeta (ν μ : ℝ) : ℝ :=
  Real.exp μ*((ν-μ+1/2)/(ν+μ+1/2))^(ν/2+1/4)*((ν+1/2)^2-μ^2)^(-μ/2)

/-- LegendreYRelation. For `x ≥ √(1−α²)` the equation 14.15.22 has a root in `(0, α²)` and one
in `(−∞, 0)` whenever its right side is negative; DLMF's `y` decreases through `0` at `x = 1`, so the
sign conditions `x < 1 → 0 < y` and `1 < x → y < 0` select it (corrected 2026-10-22; at `α = 0.6`,
`x = 0.9` both `y = 0.177237` and `y = −0.116411` solve the equation). -/
@[dlmf 14.15.E21, dlmf 14.15.E22]
def LegendreYRelation (α x y : ℝ) : Prop :=
  if x=1 then y=0 else if x ≤ Real.sqrt (1-α^2) then α^2 ≤ y ∧ Real.sqrt (y-α^2)-α*Real.arctan (Real.sqrt (y-α^2)/α)=Real.arccos (x/Real.sqrt (1-α^2))-α/2*Real.arccos (((1+α^2)*x^2-1+α^2)/((1-α^2)*(1-x^2))) else y ≤ α^2 ∧ (x < 1 → 0 < y) ∧ (1 < x → y < 0) ∧ Real.sqrt (α^2-y)+α/2*Real.log |y|-α*Real.log (Real.sqrt (α^2-y)+α)=Real.log ((x+Real.sqrt (x^2-1+α^2))/Real.sqrt (1-α^2))+α/2*Real.log ((1-α^2)*|1-x^2|/((1+α^2)*x^2-1+α^2+2*α*x*Real.sqrt (x^2-1+α^2)))

/-- legendreDegreeY. -/
def legendreDegreeY (α x : ℝ) : ℝ :=
  Classical.epsilon (LegendreYRelation α x)

/-- Left side of 14.15.21 in the variable `s = √(y - α²)`. -/
noncomputable def legY_L1 (a s : ℝ) : ℝ := s - a * Real.arctan (s / a)

/-- Left side of 14.15.22 in the variable `s = √(α² - y)`. -/
noncomputable def legY_L2 (a s : ℝ) : ℝ := s + a/2 * Real.log (a^2 - s^2) - a * Real.log (s + a)

/-- `L₁` is continuous. -/
lemma legY_L1_continuous (a : ℝ) : Continuous (legY_L1 a) := by
  unfold legY_L1
  exact continuous_id.sub (continuous_const.mul (Real.continuous_arctan.comp
    (continuous_id.div_const a)))

/-- `L₁(0) = 0`. -/
lemma legY_L1_zero (a : ℝ) : legY_L1 a 0 = 0 := by simp [legY_L1]

/-- `L₁` increases strictly on `[0, ∞)`. -/
lemma legY_L1_strictMonoOn {a : ℝ} (ha : 0 ≤ a) : StrictMonoOn (legY_L1 a) (Ici 0) := by
  rcases ha.eq_or_lt with rfl | ha
  · intro s _ t _ h; simpa [legY_L1] using h
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) (legY_L1_continuous a).continuousOn ?_
  intro s hs
  rw [interior_Ici] at hs
  have hs : (0:ℝ) < s := hs
  have hd : HasDerivAt (legY_L1 a) (1 - a * (1 / (1 + (s/a)^2) * (1/a))) s := by
    have := (hasDerivAt_id' s).fun_sub ((((hasDerivAt_id' s).div_const a).arctan).const_mul a)
    exact this
  rw [hd.deriv]
  have : a * (1 / (1 + (s/a)^2) * (1/a)) = a^2 / (a^2 + s^2) := by
    field_simp
  rw [this, sub_pos, div_lt_one (by positivity)]
  nlinarith

/-- A linear lower bound for `L₁`. -/
lemma legY_L1_ge {a : ℝ} (ha : 0 ≤ a) (s : ℝ) : s - a * (π/2) ≤ legY_L1 a s := by
  unfold legY_L1
  nlinarith [Real.arctan_lt_pi_div_two (s/a)]

/-- `L₁` maps `[0, ∞)` onto `[0, ∞)`. -/
lemma legY_L1_surj {a : ℝ} (ha : 0 ≤ a) {v : ℝ} (hv : 0 ≤ v) :
    ∃ s, 0 ≤ s ∧ legY_L1 a s = v := by
  have h0 : (0:ℝ) ≤ v + a * (π/2) := by positivity
  obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc h0 (legY_L1_continuous a).continuousOn
    (show v ∈ Icc (legY_L1 a 0) (legY_L1 a (v + a * (π/2))) from ⟨by rw [legY_L1_zero]; exact hv, by
      have := legY_L1_ge ha (v + a * (π/2)); linarith⟩)
  exact ⟨s, hs.1, hsv⟩

/-- `L₂(0) = 0`. -/
lemma legY_L2_zero (a : ℝ) : legY_L2 a 0 = 0 := by
  simp [legY_L2, Real.log_pow]; ring

/-- `L₂` is continuous away from `s = α` and `s = -α`. -/
lemma legY_L2_continuousOn (a : ℝ) :
    ContinuousOn (legY_L2 a) {s | 0 ≤ s ∧ s ≠ a ∧ 0 < s + a} := by
  intro s ⟨hs, hsa, hsa'⟩
  have h1 : a^2 - s^2 ≠ 0 := by
    intro h
    have : (a - s) * (a + s) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact hsa (by linarith)
    · linarith
  refine ContinuousAt.continuousWithinAt ?_
  unfold legY_L2
  exact (continuousAt_id.add (continuousAt_const.mul
    ((continuous_const.sub (continuous_pow 2)).continuousAt.log h1))).sub
    (continuousAt_const.mul ((continuous_id.add continuous_const).continuousAt.log hsa'.ne'))

/-- `L₂'(s) = -s²/(α² - s²)`. -/
lemma legY_L2_hasDerivAt {a s : ℝ} (hsa : a^2 - s^2 ≠ 0) (hsa' : s + a ≠ 0) :
    HasDerivAt (legY_L2 a) (-s^2/(a^2 - s^2)) s := by
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
lemma legY_L2_strictAntiOn {a : ℝ} (ha : 0 < a) : StrictAntiOn (legY_L2 a) (Ico 0 a) := by
  refine strictAntiOn_of_deriv_neg (convex_Ico 0 a)
    ((legY_L2_continuousOn a).mono fun s hs => ⟨hs.1, hs.2.ne, by linarith [hs.1]⟩) ?_
  intro s hs
  rw [interior_Ico] at hs
  have hp : 0 < a^2 - s^2 := by nlinarith [hs.1, hs.2]
  rw [(legY_L2_hasDerivAt hp.ne' (by linarith [hs.1])).deriv]
  have : 0 < s^2 := by nlinarith [hs.1]
  exact div_neg_of_neg_of_pos (by linarith) hp

/-- `L₂` increases strictly on `(α, ∞)`. -/
lemma legY_L2_strictMonoOn {a : ℝ} (ha : 0 ≤ a) : StrictMonoOn (legY_L2 a) (Ioi a) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi a)
    ((legY_L2_continuousOn a).mono fun s hs => ⟨by have : a < s := hs; linarith, (ne_of_gt hs),
      by have : a < s := hs; linarith⟩) ?_
  intro s hs
  rw [interior_Ioi] at hs
  have hs : a < s := hs
  have hp : a^2 - s^2 < 0 := by nlinarith
  rw [(legY_L2_hasDerivAt hp.ne (by linarith)).deriv]
  have : 0 < s^2 := by nlinarith
  exact div_pos_of_neg_of_neg (by linarith) hp

/-- `L₂ → -∞` at `s = α`. -/
lemma legY_L2_tendsto_nhdsNE {a : ℝ} (ha : 0 < a) : Tendsto (legY_L2 a) (𝓝[≠] a) atBot := by
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
  simp only [Function.comp, legY_L2]; ring

/-- A linear lower bound for `L₂` for large `s`. -/
lemma legY_L2_ge {a s : ℝ} (ha : 0 ≤ a) (hs : 3*a + 1 ≤ s) :
    s - a/2 * Real.log 2 ≤ legY_L2 a s := by
  have h1 : 0 < s - a := by linarith
  have h2 : 0 < s + a := by linarith
  have e : Real.log (a^2 - s^2) = Real.log (s - a) + Real.log (s + a) := by
    rw [← Real.log_mul h1.ne' h2.ne', ← Real.log_neg_eq_log]; congr 1; ring
  have h3 : Real.log (s + a) - Real.log 2 ≤ Real.log (s - a) := by
    rw [← Real.log_div h2.ne' two_ne_zero]
    exact Real.log_le_log (by positivity) (by linarith)
  unfold legY_L2
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h3 ha]

/-- `L₂ → ∞` at `∞`. -/
lemma legY_L2_tendsto_atTop {a : ℝ} (ha : 0 ≤ a) : Tendsto (legY_L2 a) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-(a/2 * Real.log 2)) tendsto_id)
  filter_upwards [eventually_ge_atTop (3*a+1)] with s hs
  have := legY_L2_ge ha hs
  simp only [id]; linarith


/-- Right side of 14.15.21. -/
noncomputable def legY_R1 (a x : ℝ) : ℝ :=
  Real.arccos (x/Real.sqrt (1-a^2))-a/2*Real.arccos (((1+a^2)*x^2-1+a^2)/((1-a^2)*(1-x^2)))

/-- Right side of 14.15.22. -/
noncomputable def legY_R2 (a x : ℝ) : ℝ :=
  Real.log ((x+Real.sqrt (x^2-1+a^2))/Real.sqrt (1-a^2))+a/2*Real.log ((1-a^2)*|1-x^2|/((1+a^2)*x^2-1+a^2+2*a*x*Real.sqrt (x^2-1+a^2)))

/-- `√(1-α²) > 0`. -/
lemma legY_x0_pos {a : ℝ} (ha1 : a < 1) (ha : 0 ≤ a) : 0 < Real.sqrt (1 - a^2) :=
  Real.sqrt_pos.2 (by nlinarith)

/-- `√(1-α²)² = 1-α²`. -/
lemma legY_x0_sq {a : ℝ} (ha1 : a < 1) (ha : 0 ≤ a) : Real.sqrt (1 - a^2) ^ 2 = 1 - a^2 :=
  Real.sq_sqrt (by nlinarith)

/-- The right side of 14.15.21 vanishes at `x = √(1-α²)`. -/
lemma legY_R1_x0 {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) : legY_R1 a (Real.sqrt (1 - a^2)) = 0 := by
  have h0 := legY_x0_pos ha1 ha
  have h2 := legY_x0_sq ha1 ha
  unfold legY_R1
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
lemma legY_R1_zero_alpha (x : ℝ) : legY_R1 0 x = Real.arccos x := by
  simp [legY_R1]


/-- Derivative of the right side of 14.15.21: `-√(1-α²-x²)/(1-x²)`. -/
lemma legY_R1_hasDerivAt {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x)
    (hx1 : x < Real.sqrt (1 - a^2)) :
    HasDerivAt (legY_R1 a) (-Real.sqrt (1 - a^2 - x^2) / (1 - x^2)) x := by
  set c := Real.sqrt (1 - a^2) with hc
  have hc0 : 0 < c := legY_x0_pos ha1 ha.le
  have hc2 : c^2 = 1 - a^2 := legY_x0_sq ha1 ha.le
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
lemma legY_R1_strictAntiOn {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    StrictAntiOn (legY_R1 a) (Icc 0 (Real.sqrt (1 - a^2))) := by
  rcases ha.eq_or_lt with rfl | ha
  · intro x hx y hy hxy
    simp only [legY_R1_zero_alpha]
    refine Real.strictAntiOn_arccos ⟨by linarith [hx.1], ?_⟩ ⟨by linarith [hy.1], ?_⟩ hxy
    · simpa using hx.2
    · simpa using hy.2
  have hc0 := legY_x0_pos ha1 ha.le
  have hc2 := legY_x0_sq ha1 ha.le
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
  · intro x hx
    have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
    have ha2 : 0 < 1 - a^2 := by nlinarith
    have hD : (1 - a^2) * (1 - x^2) ≠ 0 := by positivity
    refine ContinuousAt.continuousWithinAt ?_
    unfold legY_R1
    exact (Real.continuous_arccos.continuousAt.comp (continuousAt_id.div_const _)).sub
      (continuousAt_const.mul (Real.continuous_arccos.continuousAt.comp
        ((by fun_prop : Continuous fun x : ℝ => (1+a^2)*x^2-1+a^2).continuousAt.div
          (by fun_prop : Continuous fun x : ℝ => (1-a^2)*(1-x^2)).continuousAt hD)))
  · intro x hx
    rw [interior_Icc] at hx
    rw [(legY_R1_hasDerivAt ha ha1 hx.1 hx.2).deriv]
    have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
    have : 0 < Real.sqrt (1 - a^2 - x^2) := Real.sqrt_pos.2 (by nlinarith [hx.1, hx.2])
    exact div_neg_of_neg_of_pos (by linarith) hx2

/-- The right side of 14.15.21 is nonnegative on `[0, √(1-α²)]`. -/
lemma legY_R1_nonneg {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : 0 ≤ x)
    (hx1 : x ≤ Real.sqrt (1 - a^2)) : 0 ≤ legY_R1 a x := by
  rcases hx1.lt_or_eq with h | h
  · rw [← legY_R1_x0 ha ha1]
    exact (legY_R1_strictAntiOn ha ha1 ⟨hx, hx1⟩ ⟨(legY_x0_pos ha1 ha).le, le_rfl⟩ h).le
  · rw [h, legY_R1_x0 ha ha1]


/-- The right side of 14.15.22 without the absolute value (the logarithm is even). -/
lemma legY_R2_eq (a x : ℝ) : legY_R2 a x =
    Real.log ((x+Real.sqrt (x^2-1+a^2))/Real.sqrt (1-a^2)) + a/2*Real.log ((1-a^2)*(1-x^2)/((1+a^2)*x^2-1+a^2+2*a*x*Real.sqrt (x^2-1+a^2))) := by
  unfold legY_R2
  congr 2
  rcases abs_choice (1 - x^2) with h | h
  · rw [h]
  · rw [h, ← Real.log_neg_eq_log]; congr 1; ring

/-- `√(1-α²) ≤ x ↔ x² - 1 + α² ≥ 0` for `x ≥ 0`. -/
lemma legY_x0_le_iff {a x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (1 - a^2) ≤ x ↔ 0 ≤ x^2 - 1 + a^2 := by
  rw [Real.sqrt_le_left hx]; constructor <;> intro h <;> linarith

/-- `√(1-α²) < x ↔ x² - 1 + α² > 0` for `x ≥ 0`. -/
lemma legY_x0_lt_iff {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : 0 ≤ x) :
    Real.sqrt (1 - a^2) < x ↔ 0 < x^2 - 1 + a^2 := by
  have h0 := legY_x0_pos ha1 ha
  have h2 := legY_x0_sq ha1 ha
  constructor
  · intro h
    have := pow_lt_pow_left₀ h h0.le two_ne_zero
    linarith
  · intro h
    have := Real.sqrt_lt_sqrt (by nlinarith) (show 1 - a^2 < x^2 by linarith)
    rwa [Real.sqrt_sq hx] at this

/-- Derivative of the right side of 14.15.22: `√(x²-1+α²)/(x²-1)`. -/
lemma legY_R2_hasDerivAt {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : 0 ≤ x)
    (hx0 : Real.sqrt (1 - a^2) < x) (hx1 : x ≠ 1) :
    HasDerivAt (legY_R2 a) (Real.sqrt (x^2 - 1 + a^2) / (x^2 - 1)) x := by
  have hW0' := (legY_x0_lt_iff ha ha1 hx).1 hx0
  have hxpos : 0 < x := lt_of_le_of_lt (legY_x0_pos ha1 ha).le hx0
  set c := Real.sqrt (1 - a^2) with hc
  have hc0 : 0 < c := legY_x0_pos ha1 ha
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
  rw [show legY_R2 a = _ from funext (legY_R2_eq a)]
  refine this.congr_deriv ?_
  simp only [Pi.div_apply, ← hW]
  rw [hG]
  have hx2' : 1 - x^2 ≠ 0 := fun h => hx2 (by linarith)
  field_simp
  linear_combination (W^3*(x^2 - 1) + W^2*(a*x^3 - a*x + x^3 - x) + W*(a*x^4 - a*x^2)) * hW2


/-- The right side of 14.15.22 vanishes at `x = √(1-α²)`. -/
lemma legY_R2_x0 {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : legY_R2 a (Real.sqrt (1 - a^2)) = 0 := by
  have h0 := legY_x0_pos ha1 ha.le
  have h2 := legY_x0_sq ha1 ha.le
  have hW : Real.sqrt (Real.sqrt (1 - a^2) ^ 2 - 1 + a^2) = 0 := by
    rw [h2]; simp
  unfold legY_R2
  rw [hW, add_zero, div_self h0.ne', Real.log_one, zero_add, h2,
    show 1 - (1 - a^2) = a^2 by ring, abs_of_pos (by positivity)]
  have : (1 - a^2) * a^2 / ((1 + a^2) * (1 - a^2) - 1 + a^2 + 2 * a * Real.sqrt (1 - a^2) * 0)
      = 1 := by
    rw [div_eq_one_iff_eq (by have : 0 < 1 - a^2 := by nlinarith
                              nlinarith [mul_pos this (show 0 < a^2 by positivity)])]
    ring
  rw [this, Real.log_one, mul_zero]

/-- Continuity of the right side of 14.15.22. -/
lemma legY_R2_continuousAt {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx1 : x ≠ 1) (hx1' : x ≠ -1)
    (hpos : 0 < x + Real.sqrt (x^2-1+a^2))
    (hG : (1+a^2)*x^2-1+a^2+2*a*x*Real.sqrt (x^2-1+a^2) ≠ 0) :
    ContinuousAt (legY_R2 a) x := by
  have ha2 : 0 < Real.sqrt (1 - a^2) := Real.sqrt_pos.2 (by nlinarith)
  have hab : |1 - x^2| ≠ 0 := by
    rw [abs_ne_zero]; intro h
    have : (1 - x) * (1 + x) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact hx1 (by linarith)
    · exact hx1' (by linarith)
  have ha3 : 1 - a^2 ≠ 0 := by nlinarith
  unfold legY_R2
  refine ContinuousAt.add ?_ (continuousAt_const.mul ?_)
  · exact ((by fun_prop : Continuous fun x : ℝ => (x + Real.sqrt (x^2-1+a^2)) /
      Real.sqrt (1-a^2)).continuousAt).log (by positivity)
  · refine ContinuousAt.log ?_ (div_ne_zero (mul_ne_zero ha3 hab) hG)
    exact ((by fun_prop : Continuous fun x : ℝ => (1-a^2)*|1-x^2|).continuousAt).div
      ((by fun_prop : Continuous fun x : ℝ =>
        (1+a^2)*x^2-1+a^2+2*a*x*Real.sqrt (x^2-1+a^2)).continuousAt) hG

/-- For `x ≥ √(1-α²)` the denominator in 14.15.22 is the square `(W + αx)²`. -/
lemma legY_G_eq {a x : ℝ} (hW : 0 ≤ x^2 - 1 + a^2) :
    (1+a^2)*x^2-1+a^2+2*a*x*Real.sqrt (x^2-1+a^2) = (Real.sqrt (x^2-1+a^2) + a*x)^2 := by
  have := Real.sq_sqrt hW
  linear_combination (-1) * this

/-- The right side of 14.15.22 decreases strictly on `[√(1-α²), 1)`. -/
lemma legY_R2_strictAntiOn {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    StrictAntiOn (legY_R2 a) (Ico (Real.sqrt (1 - a^2)) 1) := by
  have h0 := legY_x0_pos ha1 ha.le
  refine strictAntiOn_of_deriv_neg (convex_Ico _ _) ?_ ?_
  · intro x hx
    have hx0 : 0 ≤ x := h0.le.trans hx.1
    have hW := (legY_x0_le_iff hx0).1 hx.1
    refine (legY_R2_continuousAt ha.le ha1 hx.2.ne (by linarith) ?_ ?_).continuousWithinAt
    · have := Real.sqrt_nonneg (x^2-1+a^2); linarith [lt_of_lt_of_le h0 hx.1]
    · rw [legY_G_eq hW]
      have : 0 < a * x := mul_pos ha (lt_of_lt_of_le h0 hx.1)
      have := Real.sqrt_nonneg (x^2-1+a^2)
      positivity
  · intro x hx
    rw [interior_Ico] at hx
    have hx0 : 0 ≤ x := h0.le.trans hx.1.le
    rw [(legY_R2_hasDerivAt ha.le ha1 hx0 hx.1 hx.2.ne).deriv]
    have hW := (legY_x0_lt_iff ha.le ha1 hx0).1 hx.1
    exact div_neg_of_pos_of_neg (Real.sqrt_pos.2 hW) (by nlinarith [hx.2])

/-- The right side of 14.15.22 is negative on `(√(1-α²), 1)`. -/
lemma legY_R2_neg {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx0 : Real.sqrt (1 - a^2) < x)
    (hx1 : x < 1) : legY_R2 a x < 0 := by
  rw [← legY_R2_x0 ha ha1]
  exact legY_R2_strictAntiOn ha ha1 ⟨le_rfl, by
    have := legY_x0_sq ha1 ha.le
    nlinarith [legY_x0_pos ha1 ha.le]⟩ ⟨hx0.le, hx1⟩ hx0

/-- `√(1-α²) ≤ 1`. -/
lemma legY_x0_le_one (a : ℝ) : Real.sqrt (1 - a^2) ≤ 1 := by
  rw [Real.sqrt_le_one]; nlinarith

/-- The right side of 14.15.22 increases strictly on `(1, ∞)`. -/
lemma legY_R2_strictMonoOn {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    StrictMonoOn (legY_R2 a) (Ioi 1) := by
  have hd : ∀ x ∈ Ioi (1:ℝ), HasDerivAt (legY_R2 a)
      (Real.sqrt (x^2 - 1 + a^2) / (x^2 - 1)) x := fun x hx =>
    legY_R2_hasDerivAt ha ha1 (by linarith [show (1:ℝ) < x from hx])
      (lt_of_le_of_lt (legY_x0_le_one a) hx) (ne_of_gt hx)
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [interior_Ioi] at hx
  rw [(hd x hx).deriv]
  have hx : (1:ℝ) < x := hx
  exact div_pos (Real.sqrt_pos.2 (by nlinarith)) (by nlinarith)

/-- The right side of 14.15.22 tends to `∞`. -/
lemma legY_R2_tendsto_atTop {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (legY_R2 a) atTop atTop := by
  set c := Real.sqrt (1 - a^2)
  have hc0 : 0 < c := legY_x0_pos ha1 ha
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
  have hG : (1+a^2)*x^2-1+a^2+2*a*x*W = (W + a*x)^2 := legY_G_eq hW0
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
  show Real.log x + (-Real.log c + a/2 * Real.log k) ≤ legY_R2 a x
  unfold legY_R2
  linarith

/-- At `α = 0` the right side of 14.15.22 is positive for `x > 1`. -/
lemma legY_R2_pos_zero {x : ℝ} (hx : 1 < x) : 0 < legY_R2 0 x := by
  simp only [legY_R2]
  norm_num
  apply Real.log_pos
  have : 0 < Real.sqrt (x^2 - 1) := Real.sqrt_pos.2 (by nlinarith)
  linarith


/-- The relation at `x = 1`. -/
lemma legY_rel_one (a y : ℝ) : LegendreYRelation a 1 y ↔ y = 0 := by
  simp [LegendreYRelation]

/-- The relation for `x ≤ √(1-α²)`, `x ≠ 1`, through `L₁`. -/
lemma legY_rel_left {a x y : ℝ} (hx1 : x ≠ 1) (hx0 : x ≤ Real.sqrt (1 - a^2)) :
    LegendreYRelation a x y ↔ a^2 ≤ y ∧ legY_L1 a (Real.sqrt (y - a^2)) = legY_R1 a x := by
  simp only [LegendreYRelation, hx1, hx0, ↓reduceIte]; rfl

/-- The left side of 14.15.22 through `L₂`. -/
lemma legY_L2_sqrt {a y : ℝ} (hy : y ≤ a^2) :
    Real.sqrt (a^2-y)+a/2*Real.log |y|-a*Real.log (Real.sqrt (a^2-y)+a)
      = legY_L2 a (Real.sqrt (a^2-y)) := by
  unfold legY_L2
  rw [Real.sq_sqrt (by linarith), Real.log_abs, show a^2 - (a^2 - y) = y by ring]

/-- The relation for `x > √(1-α²)`, `x ≠ 1`, through `L₂`. -/
lemma legY_rel_right {a x y : ℝ} (hx1 : x ≠ 1) (hx0 : ¬ x ≤ Real.sqrt (1 - a^2)) :
    LegendreYRelation a x y ↔ y ≤ a^2 ∧ (x < 1 → 0 < y) ∧ (1 < x → y < 0) ∧
      legY_L2 a (Real.sqrt (a^2-y)) = legY_R2 a x := by
  simp only [LegendreYRelation, hx1, hx0, ↓reduceIte]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, by rw [← legY_L2_sqrt h1]; exact h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, by rw [legY_L2_sqrt h1]; exact h4⟩

/-- Existence and uniqueness of the solution of 14.15.21–22. -/
lemma legY_existsUnique {a x : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : 0 ≤ x) :
    (∃ y, LegendreYRelation a x y) ∧
      ∀ y₁ y₂, LegendreYRelation a x y₁ → LegendreYRelation a x y₂ → y₁ = y₂ := by
  have hc0 := legY_x0_pos ha1 ha
  have hc1 := legY_x0_le_one a
  by_cases h1 : x = 1
  · subst h1
    simp only [legY_rel_one]
    exact ⟨⟨0, rfl⟩, fun y₁ y₂ h₁ h₂ => h₁.trans h₂.symm⟩
  by_cases h0 : x ≤ Real.sqrt (1 - a^2)
  · simp only [legY_rel_left h1 h0]
    refine ⟨?_, fun y₁ y₂ h₁ h₂ => ?_⟩
    · obtain ⟨s, hs, hsv⟩ := legY_L1_surj ha (legY_R1_nonneg ha ha1 hx h0)
      refine ⟨a^2 + s^2, by nlinarith, ?_⟩
      rw [show a^2 + s^2 - a^2 = s^2 by ring, Real.sqrt_sq hs, hsv]
    · have := (legY_L1_strictMonoOn ha).injOn (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        (h₁.2.trans h₂.2.symm)
      have := (Real.sqrt_inj (by linarith [h₁.1]) (by linarith [h₂.1])).1 this
      linarith
  simp only [legY_rel_right h1 h0]
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · -- `√(1-α²) < x < 1`, so `α > 0`
    have ha0 : 0 < a := by
      rcases ha.eq_or_lt with rfl | h
      · exfalso; apply h0; simp; linarith
      · exact h
    have hv := legY_R2_neg ha0 ha1 (not_le.1 h0) hlt
    have hsl : ∀ y, 0 < y → y ≤ a^2 → Real.sqrt (a^2 - y) ∈ Ico 0 a := by
      intro y hy hya
      refine ⟨Real.sqrt_nonneg _, ?_⟩
      rw [Real.sqrt_lt' ha0]; linarith
    refine ⟨?_, fun y₁ y₂ h₁ h₂ => ?_⟩
    · obtain ⟨s₁, hs₁, hs₁a⟩ := (((legY_L2_tendsto_nhdsNE ha0).mono_left
        (nhdsWithin_mono _ (show Iio a ⊆ ({a}ᶜ : Set ℝ) from fun s (hs : s < a) => ne_of_lt hs))).eventually
        (eventually_lt_atBot (legY_R2 a x)) |>.and (Ioo_mem_nhdsLT ha0)).exists
      have hcont : ContinuousOn (legY_L2 a) (Icc 0 s₁) :=
        (legY_L2_continuousOn a).mono fun s hs =>
          ⟨hs.1, ne_of_lt (lt_of_le_of_lt hs.2 hs₁a.2), by linarith [hs.1]⟩
      obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc' hs₁a.1.le hcont
        (show legY_R2 a x ∈ Icc (legY_L2 a s₁) (legY_L2 a 0) from
          ⟨hs₁.le, by rw [legY_L2_zero]; exact hv.le⟩)
      have hsa : s < a := lt_of_le_of_lt hs.2 hs₁a.2
      refine ⟨a^2 - s^2, by nlinarith [hs.1], fun _ => by nlinarith [hs.1], fun h => absurd h
        (by linarith), ?_⟩
      rw [show a^2 - (a^2 - s^2) = s^2 by ring, Real.sqrt_sq hs.1, hsv]
    · have e₁ := h₁.2.1 hlt
      have e₂ := h₂.2.1 hlt
      have := (legY_L2_strictAntiOn ha0).injOn (hsl _ e₁ h₁.1) (hsl _ e₂ h₂.1)
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
    · set v := legY_R2 a x
      obtain ⟨s₁, hs₁a, hs₁⟩ : ∃ s₁, a < s₁ ∧ legY_L2 a s₁ < v := by
        rcases ha.eq_or_lt with ha0 | ha0
        · subst ha0
          have hv := legY_R2_pos_zero hgt
          refine ⟨v/2, by positivity, ?_⟩
          simp only [legY_L2]; simp; linarith
        · obtain ⟨s₁, hs₁, hs₁a⟩ := (((legY_L2_tendsto_nhdsNE ha0).mono_left
            (nhdsWithin_mono _ (show Ioi a ⊆ ({a}ᶜ : Set ℝ) from fun s (hs : a < s) => ne_of_gt hs))).eventually
            (eventually_lt_atBot v) |>.and self_mem_nhdsWithin).exists
          exact ⟨s₁, hs₁a, hs₁⟩
      obtain ⟨s₂, hs₂, hs₂a⟩ := ((legY_L2_tendsto_atTop ha).eventually (eventually_gt_atTop v)
        |>.and (eventually_ge_atTop s₁)).exists
      have hcont : ContinuousOn (legY_L2 a) (Icc s₁ s₂) :=
        (legY_L2_continuousOn a).mono fun s hs =>
          ⟨by linarith [hs.1], ne_of_gt (lt_of_lt_of_le hs₁a hs.1), by linarith [hs.1]⟩
      obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc hs₂a hcont ⟨hs₁.le, hs₂.le⟩
      have hsa : a < s := lt_of_lt_of_le hs₁a hs.1
      refine ⟨a^2 - s^2, by nlinarith, fun h => absurd h (by linarith), fun _ => by nlinarith, ?_⟩
      rw [show a^2 - (a^2 - s^2) = s^2 by ring, Real.sqrt_sq (by linarith), hsv]
    · have e₁ := h₁.2.2.1 hgt
      have e₂ := h₂.2.2.1 hgt
      have := (legY_L2_strictMonoOn ha).injOn (hsr _ e₁) (hsr _ e₂)
        (h₁.2.2.2.trans h₂.2.2.2.symm)
      have := (Real.sqrt_inj (by linarith [h₁.1]) (by linarith [h₂.1])).1 this
      linarith

/-- legendreDegreeY spec. -/
@[dlmf 14.15.E21, dlmf 14.15.E22]
theorem legendreDegreeY_spec {α x : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hx : 0 ≤ x) :
    LegendreYRelation α x (legendreDegreeY α x) ∧ ∀ y : ℝ, LegendreYRelation α x y → y=legendreDegreeY α x := by
  obtain ⟨hex, huniq⟩ := legY_existsUnique hα hα1 hx
  have hs := Classical.epsilon_spec hex
  exact ⟨hs, fun y hy => huniq y _ hy hs⟩

/-- Mapping and endpoint properties in DLMF 14.15(iv). -/
theorem legendreDegreeY_monotone {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    StrictAntiOn (legendreDegreeY α) (Ici 0) ∧ legendreDegreeY α (Real.sqrt (1-α^2))=α^2 ∧ legendreDegreeY α 1=0 ∧ Tendsto (legendreDegreeY α) atTop atBot := by
  set a := α
  set Y := legendreDegreeY a with hYdef
  have hc0 := legY_x0_pos hα1 hα
  have hc1 := legY_x0_le_one a
  have hrel : ∀ x, 0 ≤ x → LegendreYRelation a x (Y x) := fun x hx =>
    (legendreDegreeY_spec hα hα1 hx).1
  have hY1 : Y 1 = 0 := (legY_rel_one a _).1 (hrel 1 zero_le_one)
  -- region 1
  have r1 : ∀ x, 0 ≤ x → x ≠ 1 → x ≤ Real.sqrt (1 - a^2) →
      a^2 ≤ Y x ∧ legY_L1 a (Real.sqrt (Y x - a^2)) = legY_R1 a x := fun x hx h1 h0 =>
    (legY_rel_left h1 h0).1 (hrel x hx)
  have r1' : ∀ x, 0 ≤ x → x < Real.sqrt (1 - a^2) → a^2 < Y x := by
    intro x hx h0
    have h1 : x ≠ 1 := by intro h; linarith
    obtain ⟨hy, he⟩ := r1 x hx h1 h0.le
    have hR : 0 < legY_R1 a x := by
      rw [← legY_R1_x0 hα hα1]
      exact legY_R1_strictAntiOn hα hα1 ⟨hx, h0.le⟩ ⟨hc0.le, le_rfl⟩ h0
    rcases hy.lt_or_eq with h | h
    · exact h
    · rw [← h, sub_self, Real.sqrt_zero, legY_L1_zero] at he; linarith
  -- region 2
  have r2 : ∀ x, Real.sqrt (1 - a^2) < x → x < 1 →
      0 < Y x ∧ Y x < a^2 ∧ legY_L2 a (Real.sqrt (a^2 - Y x)) = legY_R2 a x := by
    intro x h0 h1
    have hx : 0 ≤ x := hc0.le.trans h0.le
    obtain ⟨hy, hp, -, he⟩ := (legY_rel_right h1.ne (not_le.2 h0)).1 (hrel x hx)
    have ha0 : 0 < a := by
      rcases hα.eq_or_lt with h | h
      · exfalso; rw [← h] at h0; simp at h0; linarith
      · exact h
    refine ⟨hp h1, lt_of_le_of_ne hy fun h => ?_, he⟩
    rw [h, sub_self, Real.sqrt_zero, legY_L2_zero] at he
    linarith [legY_R2_neg ha0 hα1 h0 h1]
  -- region 3
  have r3 : ∀ x, 1 < x → Y x < 0 ∧ legY_L2 a (Real.sqrt (a^2 - Y x)) = legY_R2 a x := by
    intro x h1
    have h0 : ¬ x ≤ Real.sqrt (1 - a^2) := fun h => by linarith
    obtain ⟨-, -, hn, he⟩ := (legY_rel_right (ne_of_gt h1) h0).1 (hrel x (by linarith))
    exact ⟨hn h1, he⟩
  have hsr : ∀ y, y < 0 → Real.sqrt (a^2 - y) ∈ Ioi a := by
    intro y hy
    show a < Real.sqrt (a^2 - y)
    calc a = Real.sqrt (a^2) := (Real.sqrt_sq hα).symm
      _ < _ := Real.sqrt_lt_sqrt (by positivity) (by linarith)
  -- `Y ≥ 0` on `[0, 1]`
  have hnn : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ Y x := by
    intro x hx h1
    rcases h1.lt_or_eq with h1 | h1
    · by_cases h0 : x ≤ Real.sqrt (1 - a^2)
      · exact (sq_nonneg a).trans (r1 x hx h1.ne h0).1
      · exact (r2 x (not_le.1 h0) h1).1.le
    · rw [h1, hY1]
  refine ⟨?_, ?_, hY1, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ h12
    have hx₁ : 0 ≤ x₁ := hx₁
    have hx₂ : 0 ≤ x₂ := hx₂
    by_cases hA : x₂ ≤ Real.sqrt (1 - a^2) ∧ x₂ ≠ 1
    · obtain ⟨hA0, hA1⟩ := hA
      have hB0 : x₁ ≤ Real.sqrt (1 - a^2) := by linarith
      have hB1 : x₁ ≠ 1 := by intro h; linarith
      obtain ⟨hy₁, he₁⟩ := r1 x₁ hx₁ hB1 hB0
      obtain ⟨hy₂, he₂⟩ := r1 x₂ hx₂ hA1 hA0
      have hR := legY_R1_strictAntiOn hα hα1 ⟨hx₁, hB0⟩ ⟨hx₂, hA0⟩ h12
      rw [← he₁, ← he₂] at hR
      have := (legY_L1_strictMonoOn hα).lt_iff_lt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        |>.1 hR
      rw [Real.sqrt_lt_sqrt_iff (by linarith)] at this
      linarith
    rcases lt_trichotomy x₂ 1 with h2 | h2 | h2
    · have h20 : Real.sqrt (1 - a^2) < x₂ := by
        by_contra h; exact hA ⟨not_lt.1 h, h2.ne⟩
      obtain ⟨-, hy₂, he₂⟩ := r2 x₂ h20 h2
      by_cases h10 : x₁ ≤ Real.sqrt (1 - a^2)
      · exact lt_of_lt_of_le hy₂ (r1 x₁ hx₁ (by intro h; linarith) h10).1
      · obtain ⟨hp₁, hy₁, he₁⟩ := r2 x₁ (not_le.1 h10) (by linarith)
        have ha0 : 0 < a := by
          rcases hα.eq_or_lt with h | h
          · exfalso; rw [← h] at h20; simp at h20; linarith
          · exact h
        have hR := legY_R2_strictAntiOn ha0 hα1 ⟨(not_le.1 h10).le, by linarith⟩
          ⟨h20.le, h2⟩ h12
        rw [← he₁, ← he₂] at hR
        have hI : ∀ y, 0 < y → y < a^2 → Real.sqrt (a^2 - y) ∈ Ico 0 a := by
          intro y hy hya
          refine ⟨Real.sqrt_nonneg _, ?_⟩
          rw [Real.sqrt_lt' ha0]; linarith
        have := (legY_L2_strictAntiOn ha0).lt_iff_gt (hI _ (r2 x₂ h20 h2).1 hy₂)
          (hI _ hp₁ hy₁) |>.1 hR
        rw [Real.sqrt_lt_sqrt_iff (by linarith)] at this
        linarith
    · subst h2
      rw [hY1]
      by_cases h10 : x₁ ≤ Real.sqrt (1 - a^2)
      · rcases h10.lt_or_eq with h | h
        · exact lt_of_le_of_lt (sq_nonneg a) (r1' x₁ hx₁ h)
        · have ha0 : 0 < a := by
            rcases hα.eq_or_lt with h' | h'
            · exfalso; rw [← h'] at h; simp at h; linarith
            · exact h'
          exact lt_of_lt_of_le (by positivity) (r1 x₁ hx₁ (by intro h; linarith) h10).1
      · exact (r2 x₁ (not_le.1 h10) h12).1
    · obtain ⟨hn₂, he₂⟩ := r3 x₂ h2
      rcases le_or_gt x₁ 1 with h1 | h1
      · exact lt_of_lt_of_le hn₂ (hnn x₁ hx₁ h1)
      · obtain ⟨hn₁, he₁⟩ := r3 x₁ h1
        have hR := legY_R2_strictMonoOn hα hα1 h1 h2 h12
        rw [← he₁, ← he₂] at hR
        have := (legY_L2_strictMonoOn hα).lt_iff_lt (hsr _ hn₁) (hsr _ hn₂) |>.1 hR
        rw [Real.sqrt_lt_sqrt_iff (by linarith [sq_nonneg a])] at this
        linarith
  · rcases hα.eq_or_lt with h | ha0
    · have : Real.sqrt (1 - a^2) = 1 := by rw [← h]; simp
      rw [this, hY1, ← h]; ring
    · have hlt : Real.sqrt (1 - a^2) < 1 := by
        rw [Real.sqrt_lt' one_pos]; nlinarith
      obtain ⟨hy, he⟩ := r1 _ hc0.le hlt.ne le_rfl
      rw [legY_R1_x0 hα hα1, ← legY_L1_zero a] at he
      have := (legY_L1_strictMonoOn hα).injOn (Real.sqrt_nonneg _) (le_refl (0:ℝ)) he
      rw [Real.sqrt_eq_zero'] at this
      linarith
  · rw [tendsto_atBot]
    intro M
    set T := Real.sqrt |a^2 - M| + a + 1 with hT
    have hT0 : a < T := by have := Real.sqrt_nonneg |a^2 - M|; linarith
    have hT2 : a^2 - M ≤ T^2 := by
      have h1 := Real.sq_sqrt (abs_nonneg (a^2 - M))
      have h2 := le_abs_self (a^2 - M)
      have h3 : Real.sqrt |a^2 - M| ≤ T := by linarith
      nlinarith [Real.sqrt_nonneg |a^2 - M|]
    filter_upwards [(legY_R2_tendsto_atTop hα hα1).eventually (eventually_gt_atTop (legY_L2 a T)),
      eventually_gt_atTop (1:ℝ)] with x hx h1
    obtain ⟨hn, he⟩ := r3 x h1
    rw [← he] at hx
    have hs : T < Real.sqrt (a^2 - Y x) := by
      by_contra hle
      have := (legY_L2_strictMonoOn hα).monotoneOn (hsr _ hn) hT0 (not_lt.1 hle)
      linarith
    have h5 := Real.sq_sqrt (show 0 ≤ a^2 - Y x by nlinarith)
    have h6 : T^2 < Real.sqrt (a^2 - Y x) ^ 2 := by
      exact pow_lt_pow_left₀ hs (by linarith) two_ne_zero
    linarith

/-- Removable turning-point amplitude, including x=sqrt(1-alpha squared). -/
def legendreDegreeAmplitude (α x : ℝ) : ℝ :=
  limUnder (𝓝[≠] x) (fun t : ℝ => ((legendreDegreeY α t-α^2)/(1-α^2-t^2))^(1/4:ℝ))

/-- First positive crossing used in DLMF 2.8(iv). -/
def besselEnvelopeCross (ν : ℝ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ besselJ ν x+besselY ν x=0}

/-- Exact Bessel envelopes from DLMF 2.8.33–34, used in 14.15. -/
def legendreBesselEnvelope (second : Bool) (ν x : ℝ) : ℝ :=
  if x ≤ besselEnvelopeCross ν then Real.sqrt 2*(if second then ‖besselY ν x‖ else (besselJ ν x).re) else Real.sqrt (‖besselJ ν x‖^2+‖besselY ν x‖^2)

/-- cylinderEnvelopeCross. -/
@[dlmf 14.15.E23]
def cylinderEnvelopeCross (c : ℝ) : ℝ :=
  sSup {x : ℝ | 0 < x ∧ pcfU (-c) x=pcfUBar (-c) x}

/-- legendreCylinderEnvelope. -/
@[dlmf 14.15.E23]
def legendreCylinderEnvelope (barred : Bool) (c x : ℝ) : ℝ :=
  if x ≤ cylinderEnvelopeCross c then Real.sqrt (‖pcfU (-c) x‖^2+‖pcfUBar (-c) x‖^2) else Real.sqrt 2*(if barred then (pcfUBar (-c) x).re else (pcfU (-c) x).re)

/-- legendreCylinderA. -/
@[dlmf 14.15.E26]
def legendreCylinderA (ν μ : ℝ) : ℝ :=
  Real.sqrt ((ν+μ+1/2)*|ν-μ+1/2|)/(ν+1/2)

/-- legendreCylinderAlpha. -/
@[dlmf 14.15.E26]
def legendreCylinderAlpha (ν μ : ℝ) : ℝ :=
  Real.sqrt (2*|ν-μ+1/2|/(ν+1/2))

/-- LegendreCylinderRelation. -/
@[dlmf 14.15.E27, dlmf 14.15.E28, dlmf 14.15.E29, dlmf 14.15.E31]
def LegendreCylinderRelation (ν μ x ζ : ℝ) : Prop :=
  let a:=legendreCylinderA ν μ; let α:=legendreCylinderAlpha ν μ; if a=0 then ζ^2=-Real.log (1-x^2) ∧ 0 ≤ x*ζ else if μ ≤ ν+1/2 then if x = -a then ζ = -α else if a ≤ x then α ≤ ζ ∧ ζ*Real.sqrt (ζ^2-α^2)/2-α^2/2*Real.arcosh (ζ/α)=Real.sqrt (1-a^2)*Real.artanh (Real.sqrt ((x^2-a^2)/(1-a^2))/x)-Real.arcosh (x/a) else |ζ| ≤ α ∧ α^2/2*Real.arcsin (ζ/α)+ζ/2*Real.sqrt (α^2-ζ^2)=Real.arcsin (x/a)-Real.sqrt (1-a^2)*Real.arctan (x*Real.sqrt ((1-a^2)/(a^2-x^2))) else ζ*Real.sqrt (ζ^2+α^2)/2+α^2/2*Real.arsinh (ζ/α)=Real.sqrt (1+a^2)*Real.artanh (x*Real.sqrt ((1+a^2)/(x^2+a^2)))-Real.arsinh (x/a)

/-- legendreCylinderZeta. -/
def legendreCylinderZeta (ν μ x : ℝ) : ℝ :=
  Classical.epsilon (LegendreCylinderRelation ν μ x)

/-- Left side of DLMF 14.15.31 (hyperbolic case). -/
noncomputable def legC_P (α ζ : ℝ) : ℝ :=
  ζ*Real.sqrt (ζ^2+α^2)/2+α^2/2*Real.arsinh (ζ/α)

/-- Helper `legC_P_hasDerivAt` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_P_hasDerivAt {α : ℝ} (hα : 0 < α) (ζ : ℝ) :
    HasDerivAt (legC_P α) (Real.sqrt (ζ^2+α^2)) ζ := by
  have hp : 0 < ζ^2+α^2 := by positivity
  set s := Real.sqrt (ζ^2+α^2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hp
  have hs2 : s^2 = ζ^2+α^2 := Real.sq_sqrt hp.le
  have hsd : HasDerivAt (fun ζ => Real.sqrt (ζ^2+α^2)) (2*ζ/(2*s)) ζ := by
    have : HasDerivAt (fun ζ : ℝ => ζ^2+α^2) (2*ζ) ζ := by
      simpa using (hasDerivAt_pow 2 ζ).add_const (α^2)
    exact this.sqrt hp.ne'
  have ha := (Real.hasDerivAt_arsinh (ζ/α)).comp ζ ((hasDerivAt_id ζ).div_const α)
  have h := (((hasDerivAt_id ζ).mul hsd).div_const 2).add (ha.const_mul (α^2/2))
  convert h using 1
  · funext y; simp [legC_P, Function.comp]
  · simp only [id, one_mul]
    have h1 : 1 + (ζ/α)^2 = s^2/α^2 := by rw [hs2]; field_simp; ring
    rw [h1, Real.sqrt_div' _ (sq_nonneg α), Real.sqrt_sq hs0.le, Real.sqrt_sq hα.le]
    field_simp
    linear_combination hs2

/-- Helper `legC_P_strictMono` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_P_strictMono {α : ℝ} (hα : 0 < α) : StrictMono (legC_P α) :=
  strictMono_of_deriv_pos fun ζ => by
    rw [(legC_P_hasDerivAt hα ζ).deriv]; exact Real.sqrt_pos.2 (by positivity)

/-- Helper `legC_P_neg` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_P_neg (α ζ : ℝ) : legC_P α (-ζ) = -legC_P α ζ := by
  simp only [legC_P, neg_sq, neg_div, Real.arsinh_neg]; ring

/-- Helper `legC_P_ge` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_P_ge {α ζ : ℝ} (hα : 0 < α) (hζ : 0 ≤ ζ) : ζ^2/2 ≤ legC_P α ζ := by
  have h1 : ζ ≤ Real.sqrt (ζ^2+α^2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h2 : 0 ≤ Real.arsinh (ζ/α) := Real.arsinh_nonneg_iff.2 (by positivity)
  simp only [legC_P]
  nlinarith [mul_nonneg (sq_nonneg α) h2]

/-- Helper `legC_P_surj` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_P_surj {α : ℝ} (hα : 0 < α) (c : ℝ) : ∃ ζ, legC_P α ζ = c := by
  have hc : Continuous (legC_P α) := continuous_iff_continuousAt.2 fun ζ =>
    (legC_P_hasDerivAt hα ζ).continuousAt
  set T := |c| + 2
  have hT : |c| < legC_P α T := by
    have := legC_P_ge hα (show 0 ≤ T by positivity)
    nlinarith [abs_nonneg c]
  have hT' : legC_P α (-T) < -|c| := by rw [legC_P_neg]; linarith
  have hT0 : 0 ≤ T := by positivity
  obtain ⟨ζ, -, h⟩ := intermediate_value_Icc (show -T ≤ T by linarith) hc.continuousOn
    (show c ∈ Icc (legC_P α (-T)) (legC_P α T) from
      ⟨by linarith [neg_abs_le c], by linarith [le_abs_self c]⟩)
  exact ⟨ζ, h⟩

/-- Left side of DLMF 14.15.27 (oscillatory-free side `ζ ≥ α`). -/
noncomputable def legC_F (α ζ : ℝ) : ℝ :=
  ζ*Real.sqrt (ζ^2-α^2)/2-α^2/2*Real.arcosh (ζ/α)

/-- Helper `legC_F_hasDerivAt` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_F_hasDerivAt {α ζ : ℝ} (hα : 0 < α) (hζ : α < ζ) :
    HasDerivAt (legC_F α) (Real.sqrt (ζ^2-α^2)) ζ := by
  have hp : 0 < ζ^2-α^2 := by nlinarith
  set s := Real.sqrt (ζ^2-α^2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hp
  have hs2 : s^2 = ζ^2-α^2 := Real.sq_sqrt hp.le
  have hsd : HasDerivAt (fun ζ => Real.sqrt (ζ^2-α^2)) (2*ζ/(2*s)) ζ := by
    have : HasDerivAt (fun ζ : ℝ => ζ^2-α^2) (2*ζ) ζ := by
      simpa using (hasDerivAt_pow 2 ζ).sub_const (α^2)
    exact this.sqrt hp.ne'
  have h1 : (1:ℝ) < ζ/α := by rw [lt_div_iff₀ hα]; linarith
  have ha := (Real.hasDerivAt_arcosh h1).comp ζ ((hasDerivAt_id ζ).div_const α)
  have h := (((hasDerivAt_id ζ).mul hsd).div_const 2).sub (ha.const_mul (α^2/2))
  convert h using 1
  · funext y; simp [legC_F, Function.comp]
  · simp only [id, one_mul]
    have h2 : (ζ/α)^2 - 1 = s^2/α^2 := by rw [hs2]; field_simp
    rw [h2, Real.sqrt_div' _ (sq_nonneg α), Real.sqrt_sq hs0.le, Real.sqrt_sq hα.le]
    field_simp
    linear_combination hs2

/-- Helper `legC_F_continuousOn` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_F_continuousOn {α : ℝ} (hα : 0 < α) : ContinuousOn (legC_F α) (Ici α) := by
  have h1 : ContinuousOn (fun ζ : ℝ => Real.arcosh (ζ/α)) (Ici α) :=
    Real.continuousOn_arcosh.comp (continuous_id.div_const α).continuousOn fun ζ hζ => by
      show 1 ≤ ζ/α; rw [le_div_iff₀ hα]; simpa using hζ
  unfold legC_F
  exact ((continuous_id.mul (by fun_prop : Continuous fun ζ : ℝ => Real.sqrt (ζ^2-α^2))).div_const
    2).continuousOn.sub (h1.const_smul (α^2/2))

/-- Helper `legC_F_strictMonoOn` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_F_strictMonoOn {α : ℝ} (hα : 0 < α) : StrictMonoOn (legC_F α) (Ici α) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici α) (legC_F_continuousOn hα) fun ζ hζ => ?_
  rw [interior_Ici] at hζ
  have hζ : α < ζ := hζ
  rw [(legC_F_hasDerivAt hα hζ).deriv]
  exact Real.sqrt_pos.2 (by nlinarith)

/-- Helper `legC_F_self` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_F_self {α : ℝ} (hα : 0 < α) : legC_F α α = 0 := by
  simp [legC_F, hα.ne', Real.arcosh_zero]

/-- Helper `legC_F_ge` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_F_ge {α ζ : ℝ} (hα : 0 < α) (hζ : 2*α ≤ ζ) : ζ^2/4 - α*ζ ≤ legC_F α ζ := by
  have hζ0 : 0 < ζ := by linarith
  have h1 : ζ/2 ≤ Real.sqrt (ζ^2-α^2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hy : 1 ≤ ζ/α := by rw [le_div_iff₀ hα]; linarith
  have h2 : Real.arcosh (ζ/α) ≤ 2*(ζ/α) := by
    have hpos : 0 < ζ/α + Real.sqrt ((ζ/α)^2-1) := by positivity
    have hsq : Real.sqrt ((ζ/α)^2-1) ≤ ζ/α := by
      rw [Real.sqrt_le_left (by positivity)]; linarith
    unfold Real.arcosh
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have h3 : α^2/2*Real.arcosh (ζ/α) ≤ α*ζ := by
    have : α^2/2*(2*(ζ/α)) = α*ζ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ α^2/2 by positivity)]
  simp only [legC_F]
  nlinarith

/-- Helper `legC_F_surj` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_F_surj {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c) : ∃ ζ, α ≤ ζ ∧ legC_F α ζ = c := by
  set T := 2*α + 2*Real.sqrt c + 4*α + 1 with hT
  have hsc := Real.sq_sqrt hc
  have hsc0 := Real.sqrt_nonneg c
  have hT2 : 2*α ≤ T := by rw [hT]; linarith
  have h1 := legC_F_ge hα hT2
  have hcT : c ≤ legC_F α T := by
    have : c ≤ T^2/4 - α*T := by rw [hT]; nlinarith
    linarith
  obtain ⟨ζ, hζ, h⟩ := intermediate_value_Icc (show α ≤ T by linarith)
    ((legC_F_continuousOn hα).mono Icc_subset_Ici_self)
    (show c ∈ Icc (legC_F α α) (legC_F α T) from ⟨by rw [legC_F_self hα]; exact hc, hcT⟩)
  exact ⟨ζ, hζ.1, h⟩

/-- Helper `legC_hasDerivAt_artanh` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_hasDerivAt_artanh {v : ℝ} (hv : v ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt Real.artanh (1/(1-v^2)) v := by
  have h1 : 0 < 1 + v := by linarith [hv.1]
  have h2 : 0 < 1 - v := by linarith [hv.2]
  have he : (fun w => 1/2 * Real.log ((1+w)/(1-w))) =ᶠ[𝓝 v] Real.artanh := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
    exact (Real.artanh_eq_half_log ⟨hw.1.le, hw.2.le⟩).symm
  have hd : HasDerivAt (fun w : ℝ => (1+w)/(1-w)) ((1*(1-v) - (1+v)*(-1))/(1-v)^2) v :=
    ((hasDerivAt_id v).const_add 1).div ((hasDerivAt_id v).const_sub 1) h2.ne'
  have := (hd.log (div_pos h1 h2).ne').const_mul (1/2)
  refine (this.congr_of_eventuallyEq he.symm).congr_deriv ?_
  have h3 : 1 - v^2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- Right side of DLMF 14.15.27 as a function of `x ∈ [a, 1)`. -/
noncomputable def legC_G (a x : ℝ) : ℝ :=
  Real.sqrt (1-a^2)*Real.artanh (Real.sqrt ((x^2-a^2)/(1-a^2))/x)-Real.arcosh (x/a)

/-- Helper `legC_G_v` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_G_v {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Real.sqrt ((x^2-a^2)/(1-a^2))/x = Real.sqrt (x^2-a^2)/(Real.sqrt (1-a^2)*x) := by
  rw [Real.sqrt_div' _ (by nlinarith), div_div]

/-- Helper `legC_G_hasDerivAt` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_G_hasDerivAt {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : x ∈ Ioo a 1) :
    HasDerivAt (legC_G a) (Real.sqrt (x^2-a^2)/(1-x^2)) x := by
  have hx0 : 0 < x := ha.trans hx.1
  have hw2p : 0 < x^2-a^2 := by nlinarith [hx.1]
  have hx2 : 0 < 1 - x^2 := by nlinarith [hx.2]
  have hc2p : 0 < 1 - a^2 := by nlinarith
  set w := Real.sqrt (x^2-a^2) with hw
  set c := Real.sqrt (1-a^2) with hc
  have hw0 : 0 < w := Real.sqrt_pos.2 hw2p
  have hc0 : 0 < c := Real.sqrt_pos.2 hc2p
  have hw2 : w^2 = x^2-a^2 := Real.sq_sqrt hw2p.le
  have hc2 : c^2 = 1-a^2 := Real.sq_sqrt hc2p.le
  have hG : legC_G a = fun y => c*Real.artanh (Real.sqrt (y^2-a^2)/(c*y)) - Real.arcosh (y/a) := by
    funext y; simp only [legC_G]; rw [legC_G_v ha ha1]
  have hwd : HasDerivAt (fun y => Real.sqrt (y^2-a^2)) (2*x/(2*w)) x := by
    have : HasDerivAt (fun y : ℝ => y^2-a^2) (2*x) x := by
      simpa using (hasDerivAt_pow 2 x).sub_const (a^2)
    exact this.sqrt hw2p.ne'
  have hvd : HasDerivAt (fun y => Real.sqrt (y^2-a^2)/(c*y)) ((2*x/(2*w)*(c*x) - w*(c*1))/(c*x)^2) x :=
    hwd.div ((hasDerivAt_id x).const_mul c) (by positivity)
  have hv : w/(c*x) ∈ Ioo (-1:ℝ) 1 := by
    have hpos : 0 < w/(c*x) := by positivity
    refine ⟨by linarith, ?_⟩
    rw [div_lt_one (by positivity)]
    have : w^2 < (c*x)^2 := by rw [mul_pow, hw2, hc2]; nlinarith [mul_pos (pow_pos ha 2) hx2]
    nlinarith [mul_pos hc0 hx0]
  have hat := (legC_hasDerivAt_artanh hv).comp x hvd
  have h1 : (1:ℝ) < x/a := by rw [lt_div_iff₀ ha]; linarith [hx.1]
  have hac := (Real.hasDerivAt_arcosh h1).comp x ((hasDerivAt_id x).div_const a)
  have h := (hat.const_mul c).sub hac
  rw [hG]
  convert h using 1
  · funext y; simp [Function.comp]
  · have h3 : (x/a)^2 - 1 = w^2/a^2 := by rw [hw2]; field_simp
    rw [h3, Real.sqrt_div' _ (sq_nonneg a), Real.sqrt_sq hw0.le, Real.sqrt_sq ha.le]
    have h4 : 1 - (w/(c*x))^2 = a^2*(1-x^2)/(c^2*x^2) := by
      rw [div_pow, mul_pow, hw2, hc2]; field_simp; ring
    rw [h4]
    field_simp
    rw [hw2, hc2]; ring

/-- Helper `legC_continuousAt_artanh` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_continuousAt_artanh {v : ℝ} (hv : v ∈ Ioo (-1:ℝ) 1) : ContinuousAt Real.artanh v :=
  (legC_hasDerivAt_artanh hv).continuousAt

/-- Helper `legC_G_nonneg` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_G_nonneg {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : x ∈ Ico a 1) : 0 ≤ legC_G a x := by
  have hc2p : 0 < 1 - a^2 := by nlinarith
  set c := Real.sqrt (1-a^2) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 hc2p
  have hc2 : c^2 = 1-a^2 := Real.sq_sqrt hc2p.le
  have hG : legC_G a = fun y => c*Real.artanh (Real.sqrt (y^2-a^2)/(c*y)) - Real.arcosh (y/a) := by
    funext y; simp only [legC_G]; rw [legC_G_v ha ha1]
  have hcont : ContinuousOn (legC_G a) (Ico a 1) := by
    rw [hG]
    intro y hy
    have hy0 : 0 < y := ha.trans_le hy.1
    have hv : Real.sqrt (y^2-a^2)/(c*y) ∈ Ioo (-1:ℝ) 1 := by
      have hpos : 0 ≤ Real.sqrt (y^2-a^2)/(c*y) := by positivity
      refine ⟨by linarith, ?_⟩
      rw [div_lt_one (by positivity)]
      have hy2 : 0 < 1 - y^2 := by nlinarith [hy.2]
      have h0 : 0 ≤ y^2-a^2 := by nlinarith [hy.1]
      have : Real.sqrt (y^2-a^2)^2 < (c*y)^2 := by
        rw [mul_pow, Real.sq_sqrt h0, hc2]; nlinarith [mul_pos (pow_pos ha 2) hy2]
      nlinarith [mul_pos hc0 hy0, Real.sqrt_nonneg (y^2-a^2)]
    have h1 : ContinuousAt (fun y => Real.sqrt (y^2-a^2)/(c*y)) y :=
      ((by fun_prop : Continuous fun y : ℝ => Real.sqrt (y^2-a^2)).continuousAt).div
        (continuousAt_const.mul continuousAt_id) (by positivity)
    have h2 : ContinuousWithinAt (fun y => Real.arcosh (y/a)) (Ico a 1) y := by
      have := (Real.continuousOn_arcosh (x := y/a) (by
        show 1 ≤ y/a; rw [le_div_iff₀ ha]; linarith [hy.1]))
      refine ContinuousWithinAt.comp (g := Real.arcosh) (f := fun y => y/a) (t := Ici 1) this
        ((continuous_id.div_const a).continuousWithinAt) fun z hz => ?_
      show 1 ≤ z/a; rw [le_div_iff₀ ha]; linarith [hz.1]
    have h3 : ContinuousAt (fun y => Real.artanh (Real.sqrt (y^2-a^2)/(c*y))) y :=
      ContinuousAt.comp (g := Real.artanh) (legC_continuousAt_artanh hv) h1
    exact ((continuousAt_const.mul h3).continuousWithinAt).sub h2
  have hmono : MonotoneOn (legC_G a) (Ico a 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico a 1) hcont ?_ ?_
    · intro y hy
      rw [interior_Ico] at hy
      exact (legC_G_hasDerivAt ha ha1 hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      rw [(legC_G_hasDerivAt ha ha1 hy).deriv]
      have : 0 < 1 - y^2 := by nlinarith [hy.2, ha.trans hy.1]
      positivity
  have h0 : legC_G a a = 0 := by
    simp [legC_G, ha.ne', Real.artanh_zero, Real.arcosh_zero]
  rw [← h0]
  exact hmono ⟨le_refl a, ha1⟩ hx hx.1

/-- Left side of DLMF 14.15.28 (oscillatory side `|ζ| ≤ α`). -/
noncomputable def legC_H (α ζ : ℝ) : ℝ :=
  α^2/2*Real.arcsin (ζ/α)+ζ/2*Real.sqrt (α^2-ζ^2)

/-- Helper `legC_H_hasDerivAt` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_H_hasDerivAt {α ζ : ℝ} (hα : 0 < α) (hζ : ζ ∈ Ioo (-α) α) :
    HasDerivAt (legC_H α) (Real.sqrt (α^2-ζ^2)) ζ := by
  have hp : 0 < α^2-ζ^2 := by nlinarith [hζ.1, hζ.2]
  set s := Real.sqrt (α^2-ζ^2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hp
  have hs2 : s^2 = α^2-ζ^2 := Real.sq_sqrt hp.le
  have hsd : HasDerivAt (fun ζ => Real.sqrt (α^2-ζ^2)) (-(2*ζ)/(2*s)) ζ := by
    have : HasDerivAt (fun ζ : ℝ => α^2-ζ^2) (-(2*ζ)) ζ := by
      simpa using (hasDerivAt_pow 2 ζ).const_sub (α^2)
    exact this.sqrt hp.ne'
  have h1 : -1 < ζ/α := by rw [lt_div_iff₀ hα]; linarith [hζ.1]
  have h2 : ζ/α < 1 := by rw [div_lt_one hα]; exact hζ.2
  have ha := (Real.hasDerivAt_arcsin h1.ne' h2.ne).comp ζ ((hasDerivAt_id ζ).div_const α)
  have h := (ha.const_mul (α^2/2)).add (((hasDerivAt_id ζ).div_const 2).mul hsd)
  convert h using 1
  · funext y; simp [legC_H, Function.comp]
  · simp only [id]
    have h3 : 1 - (ζ/α)^2 = s^2/α^2 := by rw [hs2]; field_simp
    rw [h3, Real.sqrt_div' _ (sq_nonneg α), Real.sqrt_sq hs0.le, Real.sqrt_sq hα.le]
    field_simp
    linear_combination hs2

/-- Helper `legC_H_continuous` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_H_continuous (α : ℝ) : Continuous (legC_H α) := by
  unfold legC_H; fun_prop

/-- Helper `legC_H_strictMonoOn` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_H_strictMonoOn {α : ℝ} (hα : 0 < α) : StrictMonoOn (legC_H α) (Icc (-α) α) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (legC_H_continuous α).continuousOn
    fun ζ hζ => ?_
  rw [interior_Icc] at hζ
  rw [(legC_H_hasDerivAt hα hζ).deriv]
  exact Real.sqrt_pos.2 (by nlinarith [hζ.1, hζ.2])

/-- Helper `legC_H_right` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_H_right {α : ℝ} (hα : 0 < α) : legC_H α α = π*α^2/4 := by
  simp [legC_H, hα.ne', Real.arcsin_one]; ring

/-- Helper `legC_H_left` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_H_left {α : ℝ} (hα : 0 < α) : legC_H α (-α) = -(π*α^2/4) := by
  simp [legC_H, hα.ne', Real.arcsin_neg, Real.arcsin_one]; ring

/-- Right side of DLMF 14.15.28 as a function of `x ∈ (-a, a)`. -/
noncomputable def legC_K (a x : ℝ) : ℝ :=
  Real.arcsin (x/a)-Real.sqrt (1-a^2)*Real.arctan (x*Real.sqrt ((1-a^2)/(a^2-x^2)))

/-- Helper `legC_K_neg` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_K_neg (a x : ℝ) : legC_K a (-x) = -legC_K a x := by
  simp only [legC_K, neg_div, Real.arcsin_neg, neg_sq, neg_mul, Real.arctan_neg]; ring

/-- Helper `legC_K_hasDerivAt` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_K_hasDerivAt {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (legC_K a) (Real.sqrt (a^2-x^2)/(1-x^2)) x := by
  have hm2p : 0 < a^2-x^2 := by nlinarith [hx.1, hx.2]
  have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hc2p : 0 < 1 - a^2 := by nlinarith
  set m := Real.sqrt (a^2-x^2) with hm
  set c := Real.sqrt (1-a^2) with hc
  have hm0 : 0 < m := Real.sqrt_pos.2 hm2p
  have hc0 : 0 < c := Real.sqrt_pos.2 hc2p
  have hm2 : m^2 = a^2-x^2 := Real.sq_sqrt hm2p.le
  have hc2 : c^2 = 1-a^2 := Real.sq_sqrt hc2p.le
  have hmd : HasDerivAt (fun y => Real.sqrt (a^2-y^2)) (-(2*x)/(2*m)) x := by
    have : HasDerivAt (fun y : ℝ => a^2-y^2) (-(2*x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub (a^2)
    exact this.sqrt hm2p.ne'
  have hK : legC_K a = fun y => Real.arcsin (y/a) - c*Real.arctan (c*y/Real.sqrt (a^2-y^2)) := by
    funext y
    simp only [legC_K]
    rw [Real.sqrt_div hc2p.le, ← hc]
    ring_nf
  have hu1 : -1 < x/a := by rw [lt_div_iff₀ ha]; linarith [hx.1]
  have hu2 : x/a < 1 := by rw [div_lt_one ha]; exact hx.2
  have has := (Real.hasDerivAt_arcsin hu1.ne' hu2.ne).comp x ((hasDerivAt_id x).div_const a)
  have hq : HasDerivAt (fun y => c*y/Real.sqrt (a^2-y^2)) ((c*1*m - c*x*(-(2*x)/(2*m)))/m^2) x :=
    ((hasDerivAt_id x).const_mul c).div hmd hm0.ne'
  have hat := (Real.hasDerivAt_arctan (c*x/m)).comp x hq
  have h := has.sub (hat.const_mul c)
  rw [hK]
  convert h using 1
  · funext y; simp [Function.comp]
  · have h3 : 1 - (x/a)^2 = m^2/a^2 := by rw [hm2]; field_simp
    rw [h3, Real.sqrt_div' _ (sq_nonneg a), Real.sqrt_sq hm0.le, Real.sqrt_sq ha.le]
    have h4 : 1 + (c*x/m)^2 = a^2*(1-x^2)/m^2 := by
      rw [div_pow, mul_pow, hm2, hc2]; field_simp; ring
    rw [h4]
    field_simp
    rw [hm2, hc2]; ring

/-- Helper `legC_K_tendsto` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_K_tendsto {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (legC_K a) (𝓝[<] a) (𝓝 (π/2 - Real.sqrt (1-a^2)*(π/2))) := by
  have hc2p : 0 < 1 - a^2 := by nlinarith
  have h1 : Tendsto (fun x : ℝ => Real.arcsin (x/a)) (𝓝[<] a) (𝓝 (π/2)) := by
    have h := ((Real.continuous_arcsin.comp (continuous_id.div_const a)).tendsto a)
    simp only [Function.comp, id, div_self ha.ne', Real.arcsin_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hD : Tendsto (fun x : ℝ => (a^2-x^2)⁻¹) (𝓝[<] a) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Continuous fun x : ℝ => a^2-x^2 := by fun_prop
      have h := this.tendsto a
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT ha] with x hx
      show 0 < a^2-x^2
      nlinarith [hx.1, hx.2]
  have harg : Tendsto (fun x : ℝ => x*Real.sqrt ((1-a^2)/(a^2-x^2))) (𝓝[<] a) atTop := by
    have hs : Tendsto (fun x : ℝ => Real.sqrt ((1-a^2)/(a^2-x^2))) (𝓝[<] a) atTop := by
      refine Real.tendsto_sqrt_atTop.comp ?_
      simpa [div_eq_mul_inv] using hD.const_mul_atTop hc2p
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).pos_mul_atTop ha hs
  have h2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp harg
  exact h1.sub (h2.const_mul _)

/-- Helper `legC_K_bound` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_K_bound {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : x ∈ Ioo (-a) a) :
    legC_K a x < π/2 - Real.sqrt (1-a^2)*(π/2) := by
  have hmono : StrictMonoOn (legC_K a) (Ioo (-a) a) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (fun y hy => (legC_K_hasDerivAt ha ha1 hy).continuousAt.continuousWithinAt) fun y hy => ?_
    rw [interior_Ioo] at hy
    rw [(legC_K_hasDerivAt ha ha1 hy).deriv]
    have h1 : 0 < 1 - y^2 := by nlinarith [hy.1, hy.2]
    have h2 : 0 < Real.sqrt (a^2-y^2) := Real.sqrt_pos.2 (by nlinarith [hy.1, hy.2])
    positivity
  set y := (x + a)/2 with hydef
  have hy : y ∈ Ioo (-a) a := ⟨by linarith [hx.1, hx.2], by linarith [hx.2]⟩
  have hxy : legC_K a x < legC_K a y := hmono hx hy (by linarith [hx.2])
  have hle : legC_K a y ≤ π/2 - Real.sqrt (1-a^2)*(π/2) := by
    refine ge_of_tendsto (legC_K_tendsto ha ha1) ?_
    filter_upwards [Ioo_mem_nhdsLT hy.2] with z hz
    exact (hmono hy ⟨by linarith [hy.1, hz.1], hz.2⟩ hz.1).le
  linarith

/-- Helper `legC_params_lt` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_params_lt {ν μ : ℝ} (hν : -1/2 < ν) (hμ : 0 < μ) (hlt : μ < ν+1/2) :
    0 < legendreCylinderA ν μ ∧ legendreCylinderA ν μ < 1 ∧ 0 < legendreCylinderAlpha ν μ ∧
      π/2 - Real.sqrt (1-legendreCylinderA ν μ^2)*(π/2) = π*legendreCylinderAlpha ν μ^2/4 := by
  have hp : 0 < ν+1/2 := by linarith
  have habs : |ν-μ+1/2| = ν+1/2-μ := by
    rw [abs_of_pos (by linarith : (0:ℝ) < ν-μ+1/2)]; ring
  have hprod : 0 < (ν+μ+1/2)*|ν-μ+1/2| := by rw [habs]; nlinarith
  have hA2 : legendreCylinderA ν μ^2 = (ν+μ+1/2)*(ν+1/2-μ)/(ν+1/2)^2 := by
    rw [legendreCylinderA, div_pow, Real.sq_sqrt hprod.le, habs]
  have hA0 : 0 < legendreCylinderA ν μ := div_pos (Real.sqrt_pos.2 hprod) hp
  have h1a : 1 - legendreCylinderA ν μ^2 = (μ/(ν+1/2))^2 := by
    rw [hA2, show ν+μ+1/2 = (ν+1/2)+μ by ring]
    generalize ν + 1/2 = p at hp ⊢
    have hp' : p ≠ 0 := hp.ne'
    field_simp; ring
  have hα2 : legendreCylinderAlpha ν μ^2 = 2*(ν+1/2-μ)/(ν+1/2) := by
    rw [legendreCylinderAlpha, Real.sq_sqrt (div_nonneg (by positivity) hp.le), habs]
  refine ⟨hA0, ?_, Real.sqrt_pos.2 (div_pos (by rw [habs]; linarith) hp), ?_⟩
  · have : legendreCylinderA ν μ^2 < 1 := by
      have : 0 < (μ/(ν+1/2))^2 := by positivity
      linarith
    nlinarith
  · rw [h1a, Real.sqrt_sq (by positivity), hα2]
    generalize ν + 1/2 = p at hp ⊢
    have hp' : p ≠ 0 := hp.ne'
    field_simp
    ring

/-- Helper `legC_alpha_pos_of_gt` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_alpha_pos_of_gt {ν μ : ℝ} (hν : -1/2 < ν) (hgt : ν+1/2 < μ) :
    0 < legendreCylinderAlpha ν μ := by
  have hp : 0 < ν+1/2 := by linarith
  have habs : |ν-μ+1/2| = μ-(ν+1/2) := by rw [abs_of_neg (by linarith)]; ring
  exact Real.sqrt_pos.2 (div_pos (by rw [habs]; linarith) hp)

/-- Helper `legC_A_eq_zero` for DLMF 14.15(v) (Legendre–cylinder coordinate). -/
lemma legC_A_eq_zero {ν μ : ℝ} (h : μ = ν+1/2) :
    legendreCylinderA ν μ = 0 := by
  rw [legendreCylinderA, show ν-μ+1/2 = 0 by linarith]; simp

/-- legendreCylinderZeta spec. -/
@[dlmf 14.15.E27, dlmf 14.15.E28, dlmf 14.15.E29, dlmf 14.15.E31]
theorem legendreCylinderZeta_spec {ν μ x : ℝ} (hν : -1/2 < ν) (hμ : 0 < μ) (hx : x ∈ Ioo (-1:ℝ) 1) (hdom : μ ≤ ν+1/2 → -legendreCylinderA ν μ ≤ x) :
    LegendreCylinderRelation ν μ x (legendreCylinderZeta ν μ x) ∧ ∀ ζ : ℝ, LegendreCylinderRelation ν μ x ζ → ζ=legendreCylinderZeta ν μ x := by
  suffices key : (∃ ζ, LegendreCylinderRelation ν μ x ζ) ∧
      ∀ ζ₁ ζ₂, LegendreCylinderRelation ν μ x ζ₁ → LegendreCylinderRelation ν μ x ζ₂ → ζ₁ = ζ₂ by
    have hs := Classical.epsilon_spec key.1
    exact ⟨hs, fun ζ h => key.2 _ _ h hs⟩
  unfold LegendreCylinderRelation
  dsimp only
  set a := legendreCylinderA ν μ with ha
  set α := legendreCylinderAlpha ν μ with hα
  by_cases ha0 : a = 0
  · simp only [ha0, ↓reduceIte]
    have hc : 0 ≤ -Real.log (1 - x^2) := by
      have h1 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
      have h2 : 1 - x^2 ≤ 1 := by nlinarith
      linarith [Real.log_nonpos h1.le h2]
    refine ⟨⟨if 0 ≤ x then Real.sqrt (-Real.log (1 - x^2)) else -Real.sqrt (-Real.log (1 - x^2)), ?_, ?_⟩, ?_⟩
    · split_ifs <;> simp [Real.sq_sqrt hc]
    · split_ifs with h
      · exact mul_nonneg h (Real.sqrt_nonneg _)
      · have := Real.sqrt_nonneg (-Real.log (1 - x^2)); nlinarith
    · rintro ζ₁ ζ₂ ⟨h1, h1'⟩ ⟨h2, h2'⟩
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans h2.symm) with h | h
      · exact h
      · rcases lt_trichotomy x 0 with hx0 | hx0 | hx0
        · nlinarith
        · subst hx0
          simp at h1 h2
          rw [h1, h2]
        · nlinarith
  · simp only [ha0, ↓reduceIte]
    by_cases hle : μ ≤ ν+1/2
    · have hlt : μ < ν+1/2 := lt_of_le_of_ne hle fun h => ha0 (legC_A_eq_zero h)
      obtain ⟨hA0, hA1, hα0, hid⟩ := legC_params_lt hν hμ hlt
      simp only [hle, ↓reduceIte]
      by_cases hxa : x = -a
      · simp only [hxa, ↓reduceIte]
        exact ⟨⟨-α, rfl⟩, fun ζ₁ ζ₂ h1 h2 => h1.trans h2.symm⟩
      · simp only [hxa, ↓reduceIte]
        by_cases hax : a ≤ x
        · simp only [hax, ↓reduceIte]
          obtain ⟨ζ, hζ, h⟩ := legC_F_surj hα0 (legC_G_nonneg hA0 hA1 ⟨hax, hx.2⟩)
          refine ⟨⟨ζ, hζ, h⟩, fun ζ₁ ζ₂ h1 h2 => ?_⟩
          exact (legC_F_strictMonoOn hα0).injOn h1.1 h2.1 (h1.2.trans h2.2.symm)
        · simp only [hax, ↓reduceIte]
          have hxI : x ∈ Ioo (-a) a :=
            ⟨lt_of_le_of_ne (hdom hle) (Ne.symm hxa), not_le.1 hax⟩
          have hu := legC_K_bound hA0 hA1 hxI
          have hl := legC_K_bound hA0 hA1 (x := -x) ⟨by linarith [hxI.2], by linarith [hxI.1]⟩
          rw [legC_K_neg] at hl
          rw [hid] at hu hl
          obtain ⟨ζ, hζ, h⟩ := intermediate_value_Icc (show -α ≤ α by linarith)
            (legC_H_continuous α).continuousOn
            (show legC_K a x ∈ Icc (legC_H α (-α)) (legC_H α α) from by
              rw [legC_H_left hα0, legC_H_right hα0]; constructor <;> linarith)
          refine ⟨⟨ζ, abs_le.2 hζ, h⟩, fun ζ₁ ζ₂ h1 h2 => ?_⟩
          exact (legC_H_strictMonoOn hα0).injOn (abs_le.1 h1.1) (abs_le.1 h2.1) (h1.2.trans h2.2.symm)
    · simp only [hle, ↓reduceIte]
      have hα0 := legC_alpha_pos_of_gt hν (not_le.1 hle)
      obtain ⟨ζ, h⟩ := legC_P_surj hα0 (Real.sqrt (1+a^2)*Real.artanh (x*Real.sqrt ((1+a^2)/(x^2+a^2)))-Real.arsinh (x/a))
      exact ⟨⟨ζ, h⟩, fun ζ₁ ζ₂ h1 h2 => (legC_P_strictMono hα0).injective (h1.trans h2.symm)⟩

/-- legendreCylinderAmplitude. -/
def legendreCylinderAmplitude (ν μ x : ℝ) : ℝ :=
  limUnder (𝓝[≠] x) (fun t : ℝ => let a:=legendreCylinderA ν μ; let α:=legendreCylinderAlpha ν μ; let ζ:=legendreCylinderZeta ν μ t; if μ ≤ ν+1/2 then ((ζ^2-α^2)/(t^2-a^2))^(1/4:ℝ) else ((ζ^2+α^2)/(t^2+a^2))^(1/4:ℝ))

/-- Uniform approach in the large first parameter, with both other parameters varying. -/
def legendreUniformFilter (S : Set (ℝ × ℝ × ℝ)) : Filter (ℝ × ℝ × ℝ) :=
  comap Prod.fst atTop ⊓ 𝓟 S

/-- For real order and positive argument, `Y_ν(x)` is real. -/
lemma legBes_besselY_im (ν x : ℝ) (hx : 0 < x) : (besselY ν x).im = 0 := by
  have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
  have hnot : ∀ μ : ℝ, (∀ k : ℤ, (μ : ℂ) ≠ k) → (besselY μ x).im = 0 := by
    intro μ hμ
    rw [besselY_eq_of_not_int hμ, besselD, besselJ_ofReal_eq_re μ x hx,
      show -(μ : ℂ) = ((-μ : ℝ) : ℂ) by push_cast; ring, besselJ_ofReal_eq_re (-μ) x hx,
      show (μ : ℂ) * π = ((μ * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos, ← ofReal_sin,
      ← ofReal_mul, ← ofReal_sub, ← ofReal_div, ofReal_im]
  by_cases hν : ∀ k : ℤ, (ν : ℂ) ≠ k
  · exact hnot ν hν
  push Not at hν
  obtain ⟨k, hk⟩ := hν
  have hk' : ν = k := by exact_mod_cast hk
  have hc : ContinuousAt (fun μ : ℝ => (besselY μ x).im) ν := by
    have h1 := continuousAt_besselY (ν : ℂ) hs
    have h2 : ContinuousAt (fun μ : ℝ => ((μ : ℂ), (x : ℂ))) ν := by fun_prop
    exact continuous_im.continuousAt.comp (h1.comp_of_eq h2 rfl)
  have hev : ∀ᶠ μ : ℝ in 𝓝[≠] ν, (besselY μ x).im = 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds ν
      (show (0:ℝ) < 1/2 by norm_num))] with μ hμ hμb
    refine hnot μ fun j hj => hμ ?_
    have hj' : μ = j := by exact_mod_cast hj
    have hd : |(j:ℝ) - k| < 1/2 := by
      rw [← hj', ← hk']; simpa [Real.dist_eq] using hμb
    have : j = k := by
      have h1 : |((j - k : ℤ) : ℝ)| < 1 := by push_cast; linarith
      have h2 : |j - k| < 1 := by exact_mod_cast h1
      have := Int.abs_lt_one_iff.mp h2
      omega
    rw [hj', hk', this]; rfl
  exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (hev.mono fun μ h => h.symm))

/-- For real order and positive argument, `Y_ν(x)` is real. -/
lemma legBes_besselY_ofReal_eq_re (ν x : ℝ) (hx : 0 < x) :
    besselY ν x = ((besselY ν x).re : ℂ) :=
  Complex.ext (by simp) (by simp [legBes_besselY_im ν x hx])

/-- `x ↦ J_ν(x) + Y_ν(x)` is real-continuous on `(0, ∞)`. -/
lemma legBes_continuousOn (ν : ℝ) :
    ContinuousOn (fun x : ℝ => (besselJ ν x + besselY ν x).re) (Ioi 0) := by
  intro x hx
  have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
  have hY : ContinuousAt (fun t : ℝ => (besselY ν t).re) x := by
    have h1 := continuousAt_besselY (ν : ℂ) hs
    have h2 : ContinuousAt (fun t : ℝ => ((ν : ℂ), (t : ℂ))) x := by fun_prop
    exact continuous_re.continuousAt.comp (h1.comp_of_eq h2 rfl)
  simp only [add_re]
  exact ((continuousOn_re_besselJ ν) x hx).add hY.continuousWithinAt

/-- On the positive axis `J_ν + Y_ν` vanishes iff its real part does. -/
lemma legBes_eq_zero_iff {ν x : ℝ} (hx : 0 < x) :
    besselJ ν x + besselY ν x = 0 ↔ (besselJ ν x + besselY ν x).re = 0 := by
  rw [besselJ_ofReal_eq_re ν x hx, legBes_besselY_ofReal_eq_re ν x hx, ← ofReal_add, ofReal_re,
    ofReal_eq_zero]


/-- Large-argument positivity: `J_ν + Y_ν > 0` at points `x ≡ νπ/2 + π/4 (mod 2π)` beyond any
bound. -/
lemma legBes_large (ν : ℝ) (X : ℝ) :
    ∃ x, X ≤ x ∧ 0 < x ∧ 0 < (besselJ ν x + besselY ν x).re := by
  obtain ⟨C, hC⟩ := ((besselJ_sub_cos_isBigO (ν : ℂ)).add (besselY_sub_sin_isBigO (ν : ℂ))).bound
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hC
  have hpi := Real.pi_pos
  have hk : 0 < Real.sqrt (2 / π) := Real.sqrt_pos.mpr (by positivity)
  set B := max (max (max X0 1) (|C| / Real.sqrt (2 / π) + 1)) X
  obtain ⟨n, hn⟩ := exists_nat_gt ((B - ν * π / 2 - π / 4) / (2 * π))
  set x := ν * π / 2 + π / 4 + n * (2 * π) with hxdef
  have hxB : B < x := by rw [div_lt_iff₀ (by positivity)] at hn; linarith
  have hx1 : 1 ≤ x := by
    have : 1 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    linarith
  have hx0 : 0 < x := by linarith
  have hxC : |C| / Real.sqrt (2 / π) < x := by
    have : |C| / Real.sqrt (2 / π) + 1 ≤ B := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  refine ⟨x, by linarith [le_max_right (max (max X0 1) (|C| / Real.sqrt (2 / π) + 1)) X], hx0, ?_⟩
  have hb := hX0 x (by
    have : X0 ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    linarith)
  have harg : (x : ℂ) - (ν : ℂ) * π / 2 - π / 4 = ((n * (2 * π) : ℝ) : ℂ) := by
    rw [hxdef]; push_cast; ring
  have hsin : Real.sin (n * (2 * π)) = 0 := by
    rw [show (n:ℝ) * (2 * π) = ((2 * n : ℕ) : ℝ) * π by push_cast; ring, Real.sin_nat_mul_pi]
  rw [harg, ← ofReal_cos, ← ofReal_sin, Real.cos_nat_mul_two_pi, hsin,
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hb
  simp only [ofReal_one, ofReal_zero, mul_one, mul_zero, sub_zero] at hb
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hamp : Real.sqrt (2 / (π * x)) = Real.sqrt (2 / π) / Real.sqrt x := by
    rw [← Real.sqrt_div' _ hx0.le, div_div]
  have hrpow : x ^ (-(3 / 2) : ℝ) = 1 / (x * Real.sqrt x) := by
    rw [Real.rpow_neg hx0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0,
      Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
  have hlt : C * x ^ (-(3 / 2) : ℝ) < Real.sqrt (2 / (π * x)) := by
    rw [hamp, hrpow]
    have h1 : |C| < Real.sqrt (2 / π) * x := by
      rwa [div_lt_iff₀ hk, mul_comm] at hxC
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) hsx]
    have := le_abs_self C
    nlinarith
  set z := besselJ ν x + besselY ν x
  have e : besselJ ν x - (Real.sqrt (2 / (π * x)) : ℂ) + besselY ν x = z - (Real.sqrt (2 / (π * x)) : ℂ) := by
    simp only [z]; ring
  rw [e] at hb
  have hre : |z.re - Real.sqrt (2 / (π * x))| ≤ ‖z - (Real.sqrt (2 / (π * x)) : ℂ)‖ := by
    have := Complex.abs_re_le_norm (z - (Real.sqrt (2 / (π * x)) : ℂ))
    simpa using this
  have := abs_lt.mp (lt_of_le_of_lt (hre.trans hb) hlt)
  have : 0 < Real.sqrt (2 / (π * x)) := Real.sqrt_pos.2 (by positivity)
  linarith


/-- Near `0`, `J_ν` is positive and bounded (`ν ≥ 0`). -/
lemma legBes_besselJ_small {ν : ℝ} (hν : 0 ≤ ν) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      0 < (besselJ ν t).re ∧ (besselJ ν t).re ≤ M := by
  set G : ℝ → ℂ := fun x => regularizedHGFun (∅ : Multiset ℂ) {(ν : ℂ) + 1} (-((x : ℂ) ^ 2 / 4))
  have hG : ContinuousAt G 0 :=
    (analyticAt_regularized0F1 _ _).continuousAt.comp (by fun_prop)
  have hG0 : G 0 = ((Real.Gamma (ν + 1))⁻¹ : ℝ) := by
    simp only [G]
    rw [show -(((0 : ℝ) : ℂ) ^ 2 / 4) = 0 by simp, DLMF.Confluent.regularizedHGFun_zero,
      regularizedHGFunCoeff_empty]
    push_cast
    rw [← Gamma_ofReal]; push_cast; simp
  have hpos : 0 < (G 0).re := by
    rw [hG0, ofReal_re]; exact inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < (G x).re ∧ ‖G x‖ < ‖G 0‖ + 1 :=
    ((continuous_re.continuousAt.comp hG).eventually (lt_mem_nhds hpos)).and
      ((continuous_norm.continuousAt.comp hG).eventually (gt_mem_nhds (lt_add_one _)))
  obtain ⟨δ0, hδ0, hδ⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨min (δ0/2) 1, ‖G 0‖ + 1, by positivity, by positivity, fun t ht htδ => ?_⟩
  have htδ0 : t < δ0 := by linarith [min_le_left (δ0/2) 1]
  have ht1 : t ≤ 1 := htδ.trans (min_le_right _ _)
  obtain ⟨h1, h2⟩ := hδ (y := t) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact htδ0)
  have hJ : besselJ ν t = (((t / 2) ^ ν : ℝ) : ℂ) * G t := by
    simp only [besselJ_eq_regularized, G]
    rw [ofReal_cpow (by positivity)]
    push_cast; ring_nf
  have hp : 0 < (t/2) ^ ν := Real.rpow_pos_of_pos (by positivity) _
  have hp1 : (t/2) ^ ν ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) hν
  rw [hJ, re_ofReal_mul]
  refine ⟨mul_pos hp h1, ?_⟩
  calc (t/2)^ν * (G t).re ≤ 1 * ‖G t‖ :=
        mul_le_mul hp1 ((re_le_norm _)) h1.le zero_le_one
    _ ≤ ‖G 0‖ + 1 := by rw [one_mul]; exact h2.le

/-- Small-argument behaviour: `J_ν + Y_ν < 0` on some interval `(0, ε)` (`ν ≥ 0`), from
`(Y_ν/J_ν)' = 2/(π x J_ν²)` (Wronskian, DLMF 10.5.2) and the boundedness of `J_ν`. -/
lemma legBes_small {ν : ℝ} (hν : 0 ≤ ν) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, 0 < x → x < ε → (besselJ ν x + besselY ν x).re < 0 := by
  obtain ⟨δ, M, hδ, hM, hJ⟩ := legBes_besselJ_small hν
  set j : ℝ → ℝ := fun t => (besselJ ν t).re with hj
  set y : ℝ → ℝ := fun t => (besselY ν t).re with hy
  set dj : ℝ → ℝ := fun t => (deriv (besselJ ν) t).re
  set dy : ℝ → ℝ := fun t => (deriv (besselY ν) t).re
  have hs : ∀ t : ℝ, 0 < t → (t : ℂ) ∈ slitPlane := fun t ht => Or.inl (by simpa using ht)
  have hdj : ∀ t : ℝ, 0 < t → HasDerivAt j (dj t) t := fun t ht =>
    ((hasDerivAt_besselJ (ν := ν) (hs t ht)).differentiableAt.hasDerivAt).real_of_complex
  have hdy : ∀ t : ℝ, 0 < t → HasDerivAt y (dy t) t := fun t ht =>
    ((hasDerivAt_besselY (ν : ℂ) (hs t ht)).differentiableAt.hasDerivAt).real_of_complex
  have hW : ∀ t : ℝ, 0 < t → j t * dy t - dj t * y t = 2 / (π * t) := by
    intro t ht
    have h := congrArg Complex.re (wronskian_besselJ_besselY (ν : ℂ) (hs t ht))
    rw [besselJ_ofReal_eq_re ν t ht, legBes_besselY_ofReal_eq_re ν t ht] at h
    rw [show (2 : ℂ) / (π * t) = ((2 / (π * t) : ℝ) : ℂ) by push_cast; ring, ofReal_re] at h
    simpa [sub_re, re_ofReal_mul, re_mul_ofReal] using h
  set k := 2 / (π * M^2) with hk
  have hk0 : 0 < k := by positivity
  set h : ℝ → ℝ := fun t => y t / j t - k * Real.log t with hh
  have hdh : ∀ t, 0 < t → t ≤ δ →
      HasDerivAt h ((dy t * j t - y t * dj t) / j t ^ 2 - k * t⁻¹) t := by
    intro t ht htδ
    exact ((hdy t ht).div (hdj t ht) (hJ t ht htδ).1.ne').sub
      ((Real.hasDerivAt_log ht.ne').const_mul k)
  have hmono : MonotoneOn h (Ioc 0 δ) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 δ)
      (fun t ht => (hdh t ht.1 ht.2).continuousAt.continuousWithinAt)
      (fun t ht => by
        rw [interior_Ioc] at ht
        exact (hdh t ht.1 ht.2.le).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Ioc] at ht
    rw [(hdh t ht.1 ht.2.le).deriv]
    obtain ⟨hj0, hjM⟩ := hJ t ht.1 ht.2.le
    have e : dy t * j t - y t * dj t = 2 / (π * t) := by rw [← hW t ht.1]; ring
    rw [e, sub_nonneg]
    have hj2 : j t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hj0.le hjM 2
    rw [hk, ← div_eq_mul_inv, div_div, div_div]
    have hpt : 0 < π * t := mul_pos Real.pi_pos ht.1
    have : π * t * j t ^ 2 ≤ π * M ^ 2 * t := by nlinarith
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) this
  set L := (-1 - h δ) / k
  refine ⟨min δ (Real.exp L), lt_min hδ (Real.exp_pos _), fun x hx hxε => ?_⟩
  have hxδ : x ≤ δ := (hxε.trans_le (min_le_left _ _)).le
  have hxL : Real.log x < L := by
    rw [Real.log_lt_iff_lt_exp hx]; exact hxε.trans_le (min_le_right _ _)
  have h1 := hmono ⟨hx, hxδ⟩ ⟨hδ, le_rfl⟩ hxδ
  obtain ⟨hj0, -⟩ := hJ x hx hxδ
  have h2 : y x / j x < -1 := by
    have : k * Real.log x < k * L := mul_lt_mul_of_pos_left hxL hk0
    have e : k * L = -1 - h δ := by simp only [L]; field_simp
    simp only [hh] at h1
    linarith
  rw [div_lt_iff₀ hj0] at h2
  rw [add_re]
  change j x + y x < 0
  linarith


/-- Existence of the first positive Bessel crossing used by the envelopes. -/
theorem besselEnvelopeCross_spec {ν : ℝ} (hν : 0 ≤ ν) :
    0 < besselEnvelopeCross ν ∧
      besselJ ν (besselEnvelopeCross ν)+DLMF.Bessel.besselY ν (besselEnvelopeCross ν)=0 ∧
      ∀ x : ℝ, 0 < x → x < besselEnvelopeCross ν → besselJ ν x+DLMF.Bessel.besselY ν x ≠ 0 := by
  obtain ⟨ε, hε, hsmall⟩ := legBes_small hν
  set f : ℝ → ℝ := fun x => (besselJ ν x + besselY ν x).re with hf
  set Z := {x : ℝ | 0 < x ∧ besselJ ν x + besselY ν x = 0} with hZ
  have hlow : ∀ z ∈ Z, ε ≤ z := by
    intro z hz
    by_contra h
    have := hsmall z hz.1 (not_le.1 h)
    rw [(legBes_eq_zero_iff hz.1).1 hz.2] at this
    exact lt_irrefl _ this
  have hne : Z.Nonempty := by
    obtain ⟨X, hX, hX0, hXpos⟩ := legBes_large ν ε
    have hneg := hsmall (ε/2) (by positivity) (by linarith)
    obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc (show ε/2 ≤ X by linarith)
      ((legBes_continuousOn ν).mono fun t ht => show (0:ℝ) < t by linarith [ht.1])
      ⟨hneg.le, hXpos.le⟩
    have hz0 : 0 < z := by linarith [hz.1]
    exact ⟨z, hz0, (legBes_eq_zero_iff hz0).2 hfz⟩
  have hbdd : BddBelow Z := ⟨ε, hlow⟩
  have hZc : Z = Ici ε ∩ f ⁻¹' {0} := by
    ext z
    simp only [hZ, mem_ofPred_eq, mem_inter_iff, mem_Ici, mem_preimage, mem_singleton_iff, hf]
    constructor
    · intro h; exact ⟨hlow z h, (legBes_eq_zero_iff h.1).1 h.2⟩
    · intro h
      have hz0 : 0 < z := lt_of_lt_of_le hε h.1
      exact ⟨hz0, (legBes_eq_zero_iff hz0).2 h.2⟩
  have hclosed : IsClosed Z := by
    rw [hZc]
    exact ((legBes_continuousOn ν).mono (show Ici ε ⊆ Ioi 0 from fun t (ht : ε ≤ t) =>
      show (0:ℝ) < t by linarith)).preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
  have hmem : sInf Z ∈ Z := hclosed.csInf_mem hne hbdd
  refine ⟨hmem.1, hmem.2, fun x hx hxs h => ?_⟩
  exact absurd (csInf_le hbdd ⟨hx, h⟩) (not_le.2 hxs)

/-- DLMF 14.15(v): the last positive crossing defining the cylinder envelopes exists.
At `c = 0` the equation `U(0, x) = Ū(0, x)` holds only at `x = 0` (`U − Ū < 0` on `(0, ∞)`), so
DLMF's "largest positive root" degenerates and `X₀ = 0` (the supremum of the empty set); positivity
is asserted only for `c > 0` (corrected 2026-10-22). -/
@[dlmf 14.15.E23]
theorem cylinderEnvelopeCross_spec {c : ℝ} (hc : 0 ≤ c) :
    (0 < c → 0 < cylinderEnvelopeCross c) ∧
      DLMF.Confluent.pcfU (-c) (cylinderEnvelopeCross c)=DLMF.Confluent.pcfUBar (-c) (cylinderEnvelopeCross c) ∧
      ∀ x : ℝ, cylinderEnvelopeCross c < x → DLMF.Confluent.pcfU (-c) x ≠ DLMF.Confluent.pcfUBar (-c) x := by
  sorry

end DLMF.Legendre
