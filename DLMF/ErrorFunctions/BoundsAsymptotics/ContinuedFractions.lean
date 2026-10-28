/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Relations
public import DLMF.IncompleteGamma.FractionTools
public import DLMFMathlib.Analysis.Asymptotics.WatsonRotated

/-!
# Continued fractions and bounds for error functions

Real and complex error-function bounds and convergent continued-fraction representations.

Source references and common attribution are retained in
`DLMF.ErrorFunctions.BoundsAsymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat Interval

namespace DLMF.Confluent

/-- Mills ratio in DLMF normalization. -/
@[dlmf 7.8.E1]
def Real.millsRatio (x : ℝ) : ℝ :=
  Real.sqrt π/2*Real.exp (x^2)*(erfc x).re

/-- Identity under the stated parameter and domain assumptions: `Real.millsRatio x=Real.exp
(x^2)*(∫ t : ℝ in Ioi x, Real.exp (-t^2))`. -/
@[dlmf 7.8.E1]
theorem Real.millsRatio_integral (x : ℝ) :
    Real.millsRatio x=Real.exp (x^2)*(∫ t : ℝ in Ioi x, Real.exp (-t^2)) := by
  have hre : (erfc x).re = TauCeti.Real.erfc x := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; simp
  have hd (t : ℝ) : HasDerivAt (fun t => -(Real.sqrt π/2*TauCeti.Real.erfc t)) (Real.exp (-t^2)) t := by
    have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    convert ((TauCeti.Real.hasDerivAt_erfc t).const_mul (Real.sqrt π/2)).neg using 1
    field_simp
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => -(Real.sqrt π/2*TauCeti.Real.erfc t))
    (m := 0) (a := x) (hd x).continuousAt.continuousWithinAt (fun t _ => hd t)
    (by simpa using (integrable_exp_neg_mul_sq one_pos).integrableOn)
    (by simpa using (TauCeti.Real.tendsto_erfc_atTop.const_mul (Real.sqrt π/2)).neg)
  rw [Real.millsRatio, hre, hi]
  ring

/-- Estimate under the stated parameter and domain assumptions: `0 ≤ E x`. -/
theorem bndAsy_tail_nonneg {E E' : ℝ → ℝ} {x : ℝ} (hE : ∀ y, x ≤ y → HasDerivAt E (E' y) y)
    (hlim : Tendsto E atTop (𝓝 0)) (hneg : ∀ y, x < y → E' y ≤ 0) : 0 ≤ E x := by
  have hanti : AntitoneOn E (Ici x) :=
    antitoneOn_of_deriv_nonpos (convex_Ici x)
      (fun y hy => (hE y hy).continuousAt.continuousWithinAt)
      (fun y hy => by rw [interior_Ici] at hy; exact (hE y (le_of_lt hy)).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [interior_Ici] at hy; rw [(hE y (le_of_lt hy)).deriv]; exact hneg y hy)
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop x] with t ht
  exact hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

/-- Estimate under the stated parameter and domain assumptions: `0 < E x`. -/
theorem bndAsy_tail_pos {E E' : ℝ → ℝ} {x : ℝ} (hE : ∀ y, x ≤ y → HasDerivAt E (E' y) y)
    (hlim : Tendsto E atTop (𝓝 0)) (hneg : ∀ y, x < y → E' y < 0) : 0 < E x := by
  have hanti : StrictAntiOn E (Ici x) :=
    strictAntiOn_of_deriv_neg (convex_Ici x)
      (fun y hy => (hE y hy).continuousAt.continuousWithinAt)
      (fun y hy => by rw [interior_Ici] at hy; rw [(hE y (le_of_lt hy)).deriv]; exact hneg y hy)
  have h1 : 0 ≤ E (x+1) := bndAsy_tail_nonneg (fun y hy => hE y (by linarith))
    hlim (fun y hy => (hneg y (by linarith)).le)
  have := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith : x ≤ x+1)) (by linarith)
  linarith

/-- Estimate under the stated parameter and domain assumptions: `E 0 ≤ E x`. -/
theorem bndAsy_head_le {E E' : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) (hE : ∀ y, 0 ≤ y → y ≤ x → HasDerivAt E (E' y) y)
    (hpos : ∀ y, 0 < y → y < x → 0 ≤ E' y) : E 0 ≤ E x := by
  have hmono : MonotoneOn E (Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
      (fun y hy => (hE y hy.1 hy.2).continuousAt.continuousWithinAt)
      (fun y hy => by rw [interior_Icc] at hy; exact (hE y hy.1.le hy.2.le).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [interior_Icc] at hy; rw [(hE y hy.1.le hy.2.le).deriv]; exact hpos y hy.1 hy.2)
  exact hmono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx

/-- The tail integral `∫ₓ^∞ e^{-t²}` in terms of `erfc`. -/

theorem bndAsy_millsRatio_eq (x : ℝ) :
    Real.millsRatio x = Real.exp (x^2) * (Real.sqrt π/2 * TauCeti.Real.erfc x) := by
  have hre : (erfc x).re = TauCeti.Real.erfc x := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; simp
  rw [Real.millsRatio, hre]; ring

/-- The comparison function `E = e^{-y²} g − ∫_y^∞ e^{-t²}` of a candidate bound `g`. -/

theorem bndAsy_hasDerivAt_E {g : ℝ → ℝ} {g' y : ℝ} (hg : HasDerivAt g g' y) :
    HasDerivAt (fun y => Real.exp (-y^2) * g y - Real.sqrt π/2 * TauCeti.Real.erfc y)
      (Real.exp (-y^2) * (g' - 2*y*g y + 1)) y := by
  have he : HasDerivAt (fun y => Real.exp (-y^2)) (Real.exp (-y^2) * (-(2*y))) y := by
    have := (hasDerivAt_pow 2 y).neg.exp
    exact this.congr_deriv (by norm_num)
  have := (he.mul hg).sub ((TauCeti.Real.hasDerivAt_erfc y).const_mul (Real.sqrt π/2))
  refine this.congr_deriv ?_
  have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  ring

/-- The map `(fun y => Real.exp (-y^2) * g y - Real.sqrt π/2 * TauCeti.Real.erfc y)` tends to `(𝓝
0)` along `atTop`. -/
theorem bndAsy_tendsto_E {g : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun y => Real.exp (-y^2) * g y - Real.sqrt π/2 * TauCeti.Real.erfc y) atTop (𝓝 0) := by
  have he : Tendsto (fun y : ℝ => Real.exp (-y^2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
  have := (he.mul hg).sub (TauCeti.Real.tendsto_erfc_atTop.const_mul (Real.sqrt π/2))
  simpa using this

/-- Upper bound principle: if `g' − 2yg + 1 < 0` beyond `x` and `g → 0`, then `M(x) < g(x)`. -/

theorem bndAsy_millsRatio_lt {g g' : ℝ → ℝ} {x : ℝ} (hg : ∀ y, x ≤ y → HasDerivAt g (g' y) y)
    (hlim : Tendsto g atTop (𝓝 0)) (hP : ∀ y, x < y → g' y - 2*y*g y + 1 < 0) :
    Real.millsRatio x < g x := by
  have h := bndAsy_tail_pos (fun y hy => bndAsy_hasDerivAt_E (hg y hy)) (bndAsy_tendsto_E hlim)
    (fun y hy => mul_neg_of_pos_of_neg (Real.exp_pos _) (hP y hy))
  rw [bndAsy_millsRatio_eq]
  have he := Real.exp_pos (x^2)
  have h1 : Real.exp (x^2) * Real.exp (-x^2) = 1 := by rw [← Real.exp_add]; simp
  have key : Real.exp (x^2) * (Real.exp (-x^2) * g x - Real.sqrt π/2 * TauCeti.Real.erfc x) =
      g x - Real.exp (x^2) * (Real.sqrt π/2 * TauCeti.Real.erfc x) := by
    linear_combination (g x) * h1
  nlinarith [mul_pos he h]

/-- Estimate under the stated parameter and domain assumptions: `g x < Real.millsRatio x`. -/
theorem bndAsy_lt_millsRatio {g g' : ℝ → ℝ} {x : ℝ} (hg : ∀ y, x ≤ y → HasDerivAt g (g' y) y)
    (hlim : Tendsto g atTop (𝓝 0)) (hP : ∀ y, x < y → 0 < g' y - 2*y*g y + 1) :
    g x < Real.millsRatio x := by
  have h := bndAsy_tail_pos (E := fun y => -(Real.exp (-y^2) * g y - Real.sqrt π/2 * TauCeti.Real.erfc y))
    (fun y hy => (bndAsy_hasDerivAt_E (hg y hy)).neg) (by simpa using (bndAsy_tendsto_E hlim).neg)
    (fun y hy => neg_neg_of_pos (mul_pos (Real.exp_pos _) (hP y hy)))
  rw [bndAsy_millsRatio_eq]
  have he := Real.exp_pos (x^2)
  have h1 : Real.exp (x^2) * Real.exp (-x^2) = 1 := by rw [← Real.exp_add]; simp
  have key : Real.exp (x^2) * (Real.exp (-x^2) * g x - Real.sqrt π/2 * TauCeti.Real.erfc x) =
      g x - Real.exp (x^2) * (Real.sqrt π/2 * TauCeti.Real.erfc x) := by
    linear_combination (g x) * h1
  nlinarith [mul_pos he h]

/-- Estimate under the stated parameter and domain assumptions: `Real.millsRatio x ≤ g x`. -/
theorem bndAsy_millsRatio_le_of {g : ℝ → ℝ} {x : ℝ}
    (h : 0 ≤ Real.exp (-x^2) * g x - Real.sqrt π/2 * TauCeti.Real.erfc x) :
    Real.millsRatio x ≤ g x := by
  rw [bndAsy_millsRatio_eq]
  have he := Real.exp_pos (x^2)
  have h1 : Real.exp (x^2) * Real.exp (-x^2) = 1 := by rw [← Real.exp_add]; simp
  have key : Real.exp (x^2) * (Real.exp (-x^2) * g x - Real.sqrt π/2 * TauCeti.Real.erfc x) =
      g x - Real.exp (x^2) * (Real.sqrt π/2 * TauCeti.Real.erfc x) := by
    linear_combination (g x) * h1
  nlinarith [mul_nonneg he.le h]

/-- Estimate under the stated parameter and domain assumptions: `g x ≤ Real.millsRatio x`. -/
theorem bndAsy_le_millsRatio_of {g : ℝ → ℝ} {x : ℝ}
    (h : Real.exp (-x^2) * g x - Real.sqrt π/2 * TauCeti.Real.erfc x ≤ 0) :
    g x ≤ Real.millsRatio x := by
  rw [bndAsy_millsRatio_eq]
  have he := Real.exp_pos (x^2)
  have h1 : Real.exp (x^2) * Real.exp (-x^2) = 1 := by rw [← Real.exp_add]; simp
  have key : Real.exp (x^2) * (Real.exp (-x^2) * g x - Real.sqrt π/2 * TauCeti.Real.erfc x) =
      g x - Real.exp (x^2) * (Real.sqrt π/2 * TauCeti.Real.erfc x) := by
    linear_combination (g x) * h1
  nlinarith [mul_nonneg he.le (neg_nonneg.mpr h)]

/-- Derivative of the candidate bound `α/(βy + √(y²+c))`. -/

theorem bndAsy_hasDerivAt_sqrtFrac (α β c : ℝ) (hc : 0 < c) {y : ℝ}
    (hy : β*y + Real.sqrt (y^2+c) ≠ 0) :
    HasDerivAt (fun y => α/(β*y + Real.sqrt (y^2+c)))
      (-α*(β + y/Real.sqrt (y^2+c))/(β*y + Real.sqrt (y^2+c))^2) y := by
  have hpos : 0 < y^2+c := by positivity
  have hs0 : Real.sqrt (y^2+c) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hs : HasDerivAt (fun y => Real.sqrt (y^2+c)) (y/Real.sqrt (y^2+c)) y := by
    have := ((hasDerivAt_pow 2 y).add_const c).sqrt hpos.ne'
    refine this.congr_deriv ?_
    field_simp
    norm_num
  have hD : HasDerivAt (fun y => β*y + Real.sqrt (y^2+c)) (β + y/Real.sqrt (y^2+c)) y := by
    have := ((hasDerivAt_id y).const_mul β).add hs
    exact this.congr_deriv (by simp)
  have := (hasDerivAt_const y α).div hD hy
  refine this.congr_deriv ?_
  ring

/-- The map `(fun y => α/(β*y + Real.sqrt (y^2+c)))` tends to `(𝓝 0)` along `atTop`. -/
theorem bndAsy_tendsto_sqrtFrac (α β c : ℝ) (hβ : 0 ≤ β) (hc : 0 ≤ c) :
    Tendsto (fun y => α/(β*y + Real.sqrt (y^2+c))) atTop (𝓝 0) := by
  refine tendsto_const_nhds.div_atTop ?_
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop 0] with y hy
  have h1 : y ≤ Real.sqrt (y^2+c) := by
    calc y = Real.sqrt (y^2) := (Real.sqrt_sq hy).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  show y ≤ β*y + Real.sqrt (y^2+c)
  nlinarith [mul_nonneg hβ hy]

/-- Estimate under the stated parameter and domain assumptions: `y₁*(Real.sqrt (y₁^2+c) - y₁) ≤
y₂*(Real.sqrt (y₂^2+c) - y₂)`. -/
theorem bndAsy_sqrt_gap_mono {c y₁ y₂ : ℝ} (hc : 0 < c) (h0 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) :
    y₁*(Real.sqrt (y₁^2+c) - y₁) ≤ y₂*(Real.sqrt (y₂^2+c) - y₂) := by
  have hs : ∀ y : ℝ, Real.sqrt (y^2+c)^2 = y^2+c := fun y => Real.sq_sqrt (by positivity)
  have hp : ∀ y : ℝ, 0 < Real.sqrt (y^2+c) := fun y => Real.sqrt_pos.mpr (by positivity)
  have hgt : ∀ y : ℝ, 0 ≤ y → y < Real.sqrt (y^2+c) := fun y hy => by
    nlinarith [hs y, hp y]
  have hrw : ∀ y : ℝ, 0 ≤ y → Real.sqrt (y^2+c) - y = c/(Real.sqrt (y^2+c) + y) := by
    intro y hy
    rw [eq_div_iff (by linarith [hp y])]; nlinarith [hs y]
  have h2 : 0 ≤ y₂ := h0.trans h12
  rw [hrw y₁ h0, hrw y₂ h2, mul_div_assoc', mul_div_assoc',
    div_le_div_iff₀ (by linarith [hp y₁]) (by linarith [hp y₂])]
  have hkey : y₁ * Real.sqrt (y₂^2+c) ≤ y₂ * Real.sqrt (y₁^2+c) := by
    refine le_of_not_gt fun hcon => ?_
    have hnn : 0 ≤ y₂ * Real.sqrt (y₁^2+c) := mul_nonneg h2 (hp _).le
    have := mul_self_lt_mul_self hnn hcon
    nlinarith [hs y₁, hs y₂, mul_le_mul h12 h12 h0 h2]
  nlinarith

/-- Estimate under the stated parameter and domain assumptions: `0 < f x`. -/
theorem bndAsy_pos_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hpos : ∀ x, 0 < x → 0 < f' x) {x : ℝ} (hx : 0 < x) : 0 < f x := by
  have hmono : StrictMonoOn f (Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun y _ => (hf y).continuousAt.continuousWithinAt)
      (fun y hy => by rw [interior_Ici] at hy; rw [(hf y).deriv]; exact hpos y hy)
  simpa [h0] using hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx

/-- At `x`, the function `(fun x => ∫ t in (0:ℝ)..x, Real.exp (a*t^2))` has derivative `(Real.exp
(a*x^2))`. -/
theorem bndAsy_hasDerivAt_integral_exp (a x : ℝ) :
    HasDerivAt (fun x => ∫ t in (0:ℝ)..x, Real.exp (a*t^2)) (Real.exp (a*x^2)) x :=
  ((by fun_prop : Continuous fun t : ℝ => Real.exp (a*t^2)).integral_hasStrictDerivAt 0 x).hasDerivAt

/-- Estimate under the stated parameter and domain assumptions: `1/(x+Real.sqrt (x^2+2)) <
Real.millsRatio x ∧ Real.millsRatio x ≤ 1/(x+Real.sqrt (x^2+4/π))`. -/
@[dlmf 7.8.E2]
theorem Real.millsRatio_bound_2 {x : ℝ} (hx : 0 ≤ x) :
    1/(x+Real.sqrt (x^2+2)) < Real.millsRatio x ∧ Real.millsRatio x ≤ 1/(x+Real.sqrt (x^2+4/π)) := by
  have hsq : ∀ c y : ℝ, 0 < c → Real.sqrt (y^2+c)^2 = y^2+c := fun c y hc => Real.sq_sqrt (by positivity)
  have hsp : ∀ c y : ℝ, 0 < c → 0 < Real.sqrt (y^2+c) := fun c y hc => Real.sqrt_pos.mpr (by positivity)
  have hD : ∀ c y : ℝ, 0 < c → 0 ≤ y → 1*y + Real.sqrt (y^2+c) ≠ 0 := fun c y hc hy => by
    have := hsp c y hc; positivity
  -- the key identity for `P`
  have hP : ∀ c y : ℝ, 0 < c → 0 ≤ y →
      -1*(1 + y/Real.sqrt (y^2+c))/(1*y + Real.sqrt (y^2+c))^2 - 2*y*(1/(1*y + Real.sqrt (y^2+c))) + 1
        = (c - 1 - y*(Real.sqrt (y^2+c) - y))/(Real.sqrt (y^2+c)*(y + Real.sqrt (y^2+c))) := by
    intro c y hc hy
    have h1 := hsp c y hc
    have h2 : y + Real.sqrt (y^2+c) ≠ 0 := by positivity
    have h3 := hsq c y hc
    rw [show c - 1 - y*(Real.sqrt (y^2+c) - y) = Real.sqrt (y^2+c)^2 - y*Real.sqrt (y^2+c) - 1 by
      rw [h3]; ring]
    field_simp
    ring
  constructor
  · have := bndAsy_lt_millsRatio (x := x) (g := fun y => 1/(1*y + Real.sqrt (y^2+2)))
      (fun y hy => bndAsy_hasDerivAt_sqrtFrac 1 1 2 two_pos (hD 2 y two_pos (hx.trans hy)))
      (bndAsy_tendsto_sqrtFrac 1 1 2 zero_le_one zero_le_two) ?_
    · simpa only [one_mul] using this
    intro y hy
    have hy0 : 0 ≤ y := hx.trans hy.le
    rw [hP 2 y two_pos hy0]
    have h1 := hsp 2 y two_pos
    have h3 := hsq 2 y two_pos
    have hlt : y < Real.sqrt (y^2+2) := by nlinarith
    apply div_pos _ (by positivity)
    nlinarith [sq_pos_of_pos (sub_pos.mpr hlt)]
  · have hc : (0:ℝ) < 4/π := by positivity
    have hc1 : 1 < 4/π := by rw [lt_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
    set c : ℝ := 4/π with hcdef
    set N : ℝ → ℝ := fun y => c - 1 - y*(Real.sqrt (y^2+c) - y) with hN
    set E : ℝ → ℝ := fun y => Real.exp (-y^2) * (1/(1*y + Real.sqrt (y^2+c))) -
      Real.sqrt π/2 * TauCeti.Real.erfc y with hE
    have hEd : ∀ y, 0 ≤ y → HasDerivAt E (Real.exp (-y^2) *
        (N y/(Real.sqrt (y^2+c)*(y + Real.sqrt (y^2+c))))) y := by
      intro y hy
      have := bndAsy_hasDerivAt_E (bndAsy_hasDerivAt_sqrtFrac 1 1 c hc (hD c y hc hy))
      rw [hP c y hc hy] at this
      exact this
    have hEP : ∀ y, 0 ≤ y → (0 ≤ N y ↔ 0 ≤ Real.exp (-y^2) *
        (N y/(Real.sqrt (y^2+c)*(y + Real.sqrt (y^2+c))))) := by
      intro y hy
      have h1 := hsp c y hc
      have hq : 0 < Real.sqrt (y^2+c)*(y + Real.sqrt (y^2+c)) := by positivity
      rw [mul_nonneg_iff_of_pos_left (Real.exp_pos _), div_nonneg_iff]
      constructor
      · intro h; exact Or.inl ⟨h, hq.le⟩
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact h
        · linarith
    have hE0 : 0 ≤ E x := by
      rcases le_or_gt (N x) 0 with hNx | hNx
      · refine bndAsy_tail_nonneg (fun y hy => hEd y (hx.trans hy)) ?_ ?_
        · exact bndAsy_tendsto_E (bndAsy_tendsto_sqrtFrac 1 1 c zero_le_one hc.le)
        · intro y hy
          have hNy : N y ≤ 0 := by
            have := bndAsy_sqrt_gap_mono hc hx hy.le
            simp only [hN]; linarith
          have h1 := hsp c y (hc)
          have hq : 0 < Real.sqrt (y^2+c)*(y + Real.sqrt (y^2+c)) := by
            have := hx.trans hy.le; positivity
          exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (div_nonpos_of_nonpos_of_nonneg hNy hq.le)
      · have h := bndAsy_head_le hx (fun y hy _ => hEd y hy) (fun y hy hyx => by
          rw [← hEP y hy.le]
          have := bndAsy_sqrt_gap_mono hc hy.le hyx.le
          simp only [hN] at hNx ⊢; linarith)
        have h0 : E 0 = 0 := by
          simp only [hE, hcdef]
          norm_num [TauCeti.Real.erfc_zero]
        linarith
    have := bndAsy_millsRatio_le_of (g := fun y => 1/(1*y + Real.sqrt (y^2+c))) hE0
    simpa only [one_mul] using this

/-- Estimate under the stated parameter and domain assumptions: `Real.sqrt π/(2*Real.sqrt π*x+2) ≤
Real.millsRatio x ∧ Real.millsRatio x < 1/(x+1)`. -/
@[dlmf 7.8.E3]
theorem Real.millsRatio_bound_3 {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt π/(2*Real.sqrt π*x+2) ≤ Real.millsRatio x ∧ Real.millsRatio x < 1/(x+1) := by
  constructor
  · set k := Real.sqrt π with hk
    have hk0 : 0 < k := Real.sqrt_pos.mpr Real.pi_pos
    have hk2 : k^2 = π := Real.sq_sqrt Real.pi_pos.le
    set N : ℝ → ℝ := fun y => 4 - 2*k^2 + 4*k*y with hN
    set F : ℝ → ℝ := fun y => -(Real.exp (-y^2) * (k/(2*k*y+2)) - k/2 * TauCeti.Real.erfc y) with hF
    have hg : ∀ y, 0 ≤ y → HasDerivAt (fun y => k/(2*k*y+2)) (-(2*k^2)/(2*k*y+2)^2) y := by
      intro y hy
      have hD : HasDerivAt (fun y => 2*k*y+2) (2*k) y := by
        have := ((hasDerivAt_id y).const_mul (2*k)).add_const 2
        exact this.congr_deriv (by simp)
      have := (hasDerivAt_const y k).div hD (by positivity)
      exact this.congr_deriv (by ring)
    have hFd : ∀ y, 0 ≤ y → HasDerivAt F (-(Real.exp (-y^2) * (N y/(2*k*y+2)^2))) y := by
      intro y hy
      have := (bndAsy_hasDerivAt_E (hg y hy)).neg
      refine this.congr_deriv ?_
      have : (2*k*y+2) ≠ 0 := by positivity
      simp only [hN]
      field_simp
      ring
    have hF0 : 0 ≤ F x := by
      rcases le_or_gt 0 (N x) with hNx | hNx
      · refine bndAsy_tail_nonneg (fun y hy => hFd y (hx.trans hy)) ?_ ?_
        · have hlim : Tendsto (fun y => k/(2*k*y+2)) atTop (𝓝 0) := by
            refine tendsto_const_nhds.div_atTop ?_
            exact tendsto_atTop_add_const_right _ 2 (tendsto_id.const_mul_atTop (by positivity))
          have := (bndAsy_tendsto_E hlim).neg
          rw [neg_zero] at this
          exact this
        · intro y hy
          have hNy : 0 ≤ N y := by simp only [hN] at hNx ⊢; nlinarith
          have : 0 ≤ Real.exp (-y^2) * (N y/(2*k*y+2)^2) := by positivity
          linarith
      · have h := bndAsy_head_le hx (fun y hy _ => hFd y hy) (fun y hy hyx => by
          have hNy : N y < 0 := by simp only [hN] at hNx ⊢; nlinarith
          have : Real.exp (-y^2) * (N y/(2*k*y+2)^2) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
              (div_nonpos_of_nonpos_of_nonneg hNy.le (by positivity))
          linarith)
        have h0 : F 0 = 0 := by
          simp only [hF]
          norm_num [TauCeti.Real.erfc_zero]
        linarith
    have := bndAsy_le_millsRatio_of (g := fun y => k/(2*k*y+2)) (x := x) (by simp only [hF] at hF0; linarith)
    exact this
  · have hg : ∀ y : ℝ, 0 ≤ y → HasDerivAt (fun y : ℝ => 1/(y+1)) (-1/(y+1)^2) y := by
      intro y hy
      have := (hasDerivAt_const y (1:ℝ)).div ((hasDerivAt_id y).add_const 1) (by simp only [id]; positivity)
      exact this.congr_deriv (by simp)
    refine bndAsy_millsRatio_lt (fun y hy => hg y (hx.trans hy)) ?_ ?_
    · refine tendsto_const_nhds.div_atTop ?_
      exact tendsto_atTop_add_const_right _ 1 tendsto_id
    · intro y hy
      have hy0 : 0 < y := lt_of_le_of_lt hx hy
      have : -1/(y+1)^2 - 2*y*(1/(y+1)) + 1 = -(y^2/(y+1)^2) := by
        field_simp; ring
      rw [this]
      have : 0 < y^2/(y+1)^2 := by positivity
      linarith

/-- Estimate under the stated parameter and domain assumptions: `Real.millsRatio x <
2/(3*x+Real.sqrt (x^2+4))`. -/
@[dlmf 7.8.E4]
theorem Real.millsRatio_bound_four {x : ℝ} (hx : -Real.sqrt 2/2 < x) :
    Real.millsRatio x < 2/(3*x+Real.sqrt (x^2+4)) := by
  have hsq : ∀ y : ℝ, Real.sqrt (y^2+4)^2 = y^2+4 := fun y => Real.sq_sqrt (by positivity)
  have hsp : ∀ y : ℝ, 0 < Real.sqrt (y^2+4) := fun y => Real.sqrt_pos.mpr (by positivity)
  have h2 : Real.sqrt 2^2 = 2 := Real.sq_sqrt (by norm_num)
  have h2p : 0 < Real.sqrt 2 := by positivity
  have hD : ∀ y, x ≤ y → 0 < 3*y + Real.sqrt (y^2+4) := by
    intro y hy
    rcases le_or_gt 0 y with h | h
    · have := hsp y; linarith
    · have hy2 : y^2 < 1/2 := by nlinarith
      nlinarith [hsq y, hsp y]
  refine bndAsy_millsRatio_lt (g := fun y => 2/(3*y + Real.sqrt (y^2+4)))
    (fun y hy => bndAsy_hasDerivAt_sqrtFrac 2 3 4 (by norm_num) (hD y hy).ne')
    (bndAsy_tendsto_sqrtFrac 2 3 4 (by norm_num) (by norm_num)) ?_
  intro y hy
  have hDy := hD y hy.le
  have h1 := hsp y
  have h3 := hsq y
  set s := Real.sqrt (y^2+4) with hs
  have hid : -2*(3 + y/s)/(3*y+s)^2 - 2*y*(2/(3*y+s)) + 1 =
      (2*y*(3+y^2) - 2*s*(1+y^2))/(s*(3*y+s)^2) := by
    field_simp
    linear_combination (2*y + s) * h3
  rw [hid]
  apply div_neg_of_neg_of_pos _ (by positivity)
  rcases le_or_gt y 0 with hy0 | hy0
  · nlinarith [sq_nonneg y]
  · have hkey : (s*(1+y^2))^2 - (y*(3+y^2))^2 = 4 := by
      linear_combination (1+y^2)^2 * h3
    nlinarith [sq_nonneg (s*(1+y^2) - y*(3+y^2)), mul_pos h1 (by positivity : (0:ℝ) < 1+y^2),
      mul_pos hy0 (by positivity : (0:ℝ) < 3+y^2)]

/-- Estimate under the stated parameter and domain assumptions: `x^2/(2*x^2+1) ≤
x^2*(2*x^2+5)/(4*x^4+12*x^2+3) ∧ x^2*(2*x^2+5)/(4*x^4+12*x^2+3) ≤ x*Real.millsRatio x ∧
x*Real.millsRatio x < (2*x^4+9*x^2+4)/(4*x^4+20*x^2+15) ∧ (2*x^4+9*x^2+4)/(4*x^4+20*x^2+15) <
(x^2+1)/(2*x^2+3)`. -/
@[dlmf 7.8.E5]
theorem Real.millsRatio_rational_bounds {x : ℝ} (hx : 0 ≤ x) :
    x^2/(2*x^2+1) ≤ x^2*(2*x^2+5)/(4*x^4+12*x^2+3) ∧ x^2*(2*x^2+5)/(4*x^4+12*x^2+3) ≤ x*Real.millsRatio x ∧ x*Real.millsRatio x < (2*x^4+9*x^2+4)/(4*x^4+20*x^2+15) ∧ (2*x^4+9*x^2+4)/(4*x^4+20*x^2+15) < (x^2+1)/(2*x^2+3) := by
  have hq1 : ∀ y : ℝ, 0 < 4*y^4+12*y^2+3 := fun y => by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (hq1 x)]; nlinarith [sq_nonneg x, pow_nonneg (sq_nonneg x) 2]
  · -- lower bound via `g₁ = y(2y²+5)/(4y⁴+12y²+3)`, with `q₁² (g₁' − 2y g₁ + 1) = 24`
    have hg : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y*(2*y^2+5)/(4*y^4+12*y^2+3))
        (((6*y^2+5)*(4*y^4+12*y^2+3) - y*(2*y^2+5)*(16*y^3+24*y))/(4*y^4+12*y^2+3)^2) y := by
      intro y
      have hp : HasDerivAt (fun y : ℝ => y*(2*y^2+5)) (6*y^2+5) y := by
        have := (hasDerivAt_id y).mul (((hasDerivAt_pow 2 y).const_mul 2).add_const 5)
        exact this.congr_deriv (by simp; ring)
      have hq : HasDerivAt (fun y : ℝ => 4*y^4+12*y^2+3) (16*y^3+24*y) y := by
        have := (((hasDerivAt_pow 4 y).const_mul 4).add ((hasDerivAt_pow 2 y).const_mul 12)).add_const 3
        exact this.congr_deriv (by simp; ring)
      exact hp.div hq (hq1 y).ne'
    have hlim : Tendsto (fun y : ℝ => y*(2*y^2+5)/(4*y^4+12*y^2+3)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun y : ℝ => 2/y) atTop (𝓝 0)) ?_ ?_
      · filter_upwards [eventually_ge_atTop 0] with y hy
        exact div_nonneg (by positivity) (hq1 y).le
      · filter_upwards [eventually_ge_atTop 1] with y hy
        rw [div_le_div_iff₀ (hq1 y) (by linarith)]
        nlinarith [pow_le_pow_left₀ zero_le_one hy 2, pow_le_pow_left₀ zero_le_one hy 3,
          pow_le_pow_left₀ zero_le_one hy 4]
    have h := bndAsy_lt_millsRatio (x := x) (fun y _ => hg y) hlim (fun y _ => by
      have : 0 < (4*y^4+12*y^2+3) := hq1 y
      rw [show ((6*y^2+5)*(4*y^4+12*y^2+3) - y*(2*y^2+5)*(16*y^3+24*y))/(4*y^4+12*y^2+3)^2
          - 2*y*(y*(2*y^2+5)/(4*y^4+12*y^2+3)) + 1 = 24/(4*y^4+12*y^2+3)^2 by
        field_simp; ring]
      positivity)
    rw [show x^2*(2*x^2+5)/(4*x^4+12*x^2+3) = x * (x*(2*x^2+5)/(4*x^4+12*x^2+3)) by ring]
    exact mul_le_mul_of_nonneg_left h.le hx
  · rcases hx.eq_or_lt with h0 | hx0
    · subst h0; norm_num
    have hq2 : ∀ y : ℝ, 0 < y → 0 < y*(4*y^4+20*y^2+15) := fun y hy => by positivity
    have hg : ∀ y : ℝ, 0 < y → HasDerivAt (fun y : ℝ => (2*y^4+9*y^2+4)/(y*(4*y^4+20*y^2+15)))
        (((8*y^3+18*y)*(y*(4*y^4+20*y^2+15)) - (2*y^4+9*y^2+4)*(20*y^4+60*y^2+15))/
          (y*(4*y^4+20*y^2+15))^2) y := by
      intro y hy
      have hp : HasDerivAt (fun y : ℝ => 2*y^4+9*y^2+4) (8*y^3+18*y) y := by
        have := (((hasDerivAt_pow 4 y).const_mul 2).add ((hasDerivAt_pow 2 y).const_mul 9)).add_const 4
        exact this.congr_deriv (by simp; ring)
      have hq : HasDerivAt (fun y : ℝ => y*(4*y^4+20*y^2+15)) (20*y^4+60*y^2+15) y := by
        have := (hasDerivAt_id y).mul ((((hasDerivAt_pow 4 y).const_mul 4).add
          ((hasDerivAt_pow 2 y).const_mul 20)).add_const 15)
        exact this.congr_deriv (by simp; ring)
      exact hp.div hq (hq2 y hy).ne'
    have hlim : Tendsto (fun y : ℝ => (2*y^4+9*y^2+4)/(y*(4*y^4+20*y^2+15))) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun y : ℝ => 4/y) atTop (𝓝 0)) ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact div_nonneg (by positivity) (hq2 y hy).le
      · filter_upwards [eventually_ge_atTop 1] with y hy
        rw [div_le_div_iff₀ (hq2 y (by linarith)) (by linarith)]
        nlinarith [pow_le_pow_left₀ zero_le_one hy 2, pow_le_pow_left₀ zero_le_one hy 3,
          pow_le_pow_left₀ zero_le_one hy 4, pow_le_pow_left₀ zero_le_one hy 5]
    have h := bndAsy_millsRatio_lt (x := x) (fun y hy => hg y (hx0.trans_le hy)) hlim (fun y hy => by
      have hy0 : 0 < y := hx0.trans hy
      have : 0 < y*(4*y^4+20*y^2+15) := hq2 y hy0
      rw [show ((8*y^3+18*y)*(y*(4*y^4+20*y^2+15)) - (2*y^4+9*y^2+4)*(20*y^4+60*y^2+15))/
          (y*(4*y^4+20*y^2+15))^2 - 2*y*((2*y^4+9*y^2+4)/(y*(4*y^4+20*y^2+15))) + 1
          = -60/(y*(4*y^4+20*y^2+15))^2 by
        field_simp; ring]
      have : 0 < 60/(y*(4*y^4+20*y^2+15))^2 := by positivity
      rw [neg_div]; linarith)
    have := mul_lt_mul_of_pos_left h hx0
    rw [show x * ((2*x^4+9*x^2+4)/(x*(4*x^4+20*x^2+15))) = (2*x^4+9*x^2+4)/(4*x^4+20*x^2+15) by
      field_simp] at this
    exact this
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg x, pow_nonneg (sq_nonneg x) 2]

/-- Estimate under the stated parameter and domain assumptions: `(∫ t in (0 : ℝ)..x, Real.exp
(a*t^2)) < (2*Real.exp (a*x^2)+a*x^2-2)/(3*a*x)`. -/
@[dlmf 7.8.E6]
theorem Real.exp_sq_integral_bound {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, Real.exp (a*t^2)) < (2*Real.exp (a*x^2)+a*x^2-2)/(3*a*x) := by
  set I : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, Real.exp (a*t^2) with hI
  have hId : ∀ y, HasDerivAt I (Real.exp (a*y^2)) y := bndAsy_hasDerivAt_integral_exp a
  have hI0 : I 0 = 0 := by simp [hI]
  -- ψ = (x e^{ax²} + 2x)/3 − I
  have hψ : ∀ y, HasDerivAt (fun y => (y*Real.exp (a*y^2)+2*y)/3 - I y)
      ((2/3)*(1+(a*y^2-1)*Real.exp (a*y^2))) y := by
    intro y
    have h1 : HasDerivAt (fun y => Real.exp (a*y^2)) (Real.exp (a*y^2)*(a*(2*y))) y := by
      have := ((hasDerivAt_pow 2 y).const_mul a).exp
      exact this.congr_deriv (by norm_num)
    have := (((hasDerivAt_id y).mul h1).add ((hasDerivAt_id y).const_mul 2)).div_const 3 |>.sub (hId y)
    exact this.congr_deriv (by (try simp only [id_eq]); ring)
  have hψpos : ∀ y, 0 < y → 0 < (2/3)*(1+(a*y^2-1)*Real.exp (a*y^2)) := by
    intro y hy
    have hu : 0 < a*y^2 := by positivity
    have he := Real.add_one_lt_exp (by linarith : -(a*y^2) < 0).ne
    have hE := Real.exp_pos (a*y^2)
    have : 1 + (a*y^2-1)*Real.exp (a*y^2) = Real.exp (a*y^2) * (Real.exp (-(a*y^2)) - (1 - a*y^2)) := by
      rw [mul_sub, ← Real.exp_add]; simp; ring
    rw [this]; have : 0 < Real.exp (-(a*y^2)) - (1 - a*y^2) := by linarith
    exact mul_pos (by norm_num) (mul_pos hE this)
  have hφ : ∀ y, HasDerivAt (fun y => (2*Real.exp (a*y^2)+a*y^2-2)/(3*a) - y * I y)
      ((y*Real.exp (a*y^2)+2*y)/3 - I y) y := by
    intro y
    have h1 : HasDerivAt (fun y => Real.exp (a*y^2)) (Real.exp (a*y^2)*(a*(2*y))) y := by
      have := ((hasDerivAt_pow 2 y).const_mul a).exp
      exact this.congr_deriv (by norm_num)
    have := ((((h1.const_mul 2).add ((hasDerivAt_pow 2 y).const_mul a)).sub_const 2).div_const (3*a)).sub
      ((hasDerivAt_id y).mul (hId y))
    exact this.congr_deriv (by (try simp only [id_eq]); field_simp; ring)
  have hpos := bndAsy_pos_of_hasDerivAt hφ (by simp [hI0])
    (fun y hy => bndAsy_pos_of_hasDerivAt hψ (by simp [hI0]) hψpos hy) hx
  rw [lt_div_iff₀ (by positivity)]
  have : (2*Real.exp (a*x^2)+a*x^2-2) = 3*a*((2*Real.exp (a*x^2)+a*x^2-2)/(3*a)) := by
    field_simp
  nlinarith

/-- Estimate under the stated parameter and domain assumptions: `Real.sinh (x^2)/x < Real.exp
(x^2)*Real.dawsonF x ∧ Real.exp (x^2)*Real.dawsonF x < (Real.exp (x^2)-1)/x`. -/
@[dlmf 7.8.E7]
theorem Real.dawsonF_integral_bounds {x : ℝ} (hx : 0 < x) :
    Real.sinh (x^2)/x < Real.exp (x^2)*Real.dawsonF x ∧ Real.exp (x^2)*Real.dawsonF x < (Real.exp (x^2)-1)/x := by
  have hD : Real.exp (x^2)*Real.dawsonF x = ∫ t in (0 : ℝ)..x, Real.exp (1*t^2) := by
    rw [Real.dawsonF, ← mul_assoc, ← Real.exp_add]; simp
  rw [hD]
  set I : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, Real.exp (1*t^2) with hI
  have hId : ∀ y, HasDerivAt I (Real.exp (1*y^2)) y := bndAsy_hasDerivAt_integral_exp 1
  have hI0 : I 0 = 0 := by simp [hI]
  have hE : ∀ y, HasDerivAt (fun y => Real.exp (1*y^2)) (Real.exp (1*y^2)*(1*(2*y))) y := by
    intro y; have := ((hasDerivAt_pow 2 y).const_mul 1).exp
    exact this.congr_deriv (by norm_num)
  have hEn : ∀ y, HasDerivAt (fun y => Real.exp (-(1*y^2))) (Real.exp (-(1*y^2))*(-(1*(2*y)))) y := by
    intro y; have := ((hasDerivAt_pow 2 y).const_mul 1).neg.exp
    exact this.congr_deriv (by norm_num)
  constructor
  · -- K = x I − sinh(x²); K' = I − x e^{-x²}; K'' = e^{x²} − e^{-x²} + 2x² e^{-x²}
    have hK2 : ∀ y, HasDerivAt (fun y => I y - y*Real.exp (-(1*y^2)))
        (Real.exp (1*y^2) - Real.exp (-(1*y^2)) + 2*y^2*Real.exp (-(1*y^2))) y := by
      intro y
      have := (hId y).sub ((hasDerivAt_id y).mul (hEn y))
      exact this.congr_deriv (by (try simp only [id_eq]); ring)
    have hK2pos : ∀ y, 0 < y → 0 < Real.exp (1*y^2) - Real.exp (-(1*y^2)) + 2*y^2*Real.exp (-(1*y^2)) := by
      intro y hy
      have : Real.exp (-(1*y^2)) < Real.exp (1*y^2) := Real.exp_lt_exp.mpr (by nlinarith)
      have : 0 < 2*y^2*Real.exp (-(1*y^2)) := by positivity
      linarith
    have hK : ∀ y, HasDerivAt (fun y => y * I y - Real.sinh (y^2))
        (I y - y*Real.exp (-(1*y^2))) y := by
      intro y
      have := ((hasDerivAt_id y).mul (hId y)).sub ((hasDerivAt_pow 2 y).sinh)
      exact this.congr_deriv (by (try simp only [id_eq]); rw [Real.cosh_eq]; ring_nf)
    have hp := bndAsy_pos_of_hasDerivAt hK (by simp [hI0])
      (fun y hy => bndAsy_pos_of_hasDerivAt hK2 (by simp [hI0]) hK2pos hy) hx
    rw [div_lt_iff₀ hx]; linarith
  · have hH : ∀ y, HasDerivAt (fun y => y*Real.exp (1*y^2) - I y) (2*y^2*Real.exp (1*y^2)) y := by
      intro y
      have := ((hasDerivAt_id y).mul (hE y)).sub (hId y)
      exact this.congr_deriv (by (try simp only [id_eq]); ring)
    have hG : ∀ y, HasDerivAt (fun y => Real.exp (1*y^2) - 1 - y * I y)
        (y*Real.exp (1*y^2) - I y) y := by
      intro y
      have := ((hE y).sub_const 1).sub ((hasDerivAt_id y).mul (hId y))
      exact this.congr_deriv (by (try simp only [id_eq]); ring)
    have hp := bndAsy_pos_of_hasDerivAt hG (by simp [hI0])
      (fun y hy => bndAsy_pos_of_hasDerivAt hH (by simp [hI0]) (fun z hz => by positivity) hy) hx
    rw [lt_div_iff₀ hx, one_mul] at *
    change 0 < Real.exp (x^2) - 1 - x * I x at hp
    change I x * x < _
    linarith [mul_comm x (I x)]

/-- Secant bound for `ph(u) = e^{-ku} - 1 + mu`: `ph(t) < (t/s) ph(s)` for `0 < t < s`. -/
theorem bndAsy_phi_lt {k m t s : ℝ} (hk : 0 < k) (ht : 0 < t) (hts : t < s) :
    Real.exp (-(k*t)) - 1 + m*t < t/s * (Real.exp (-(k*s)) - 1 + m*s) := by
  have hs : 0 < s := ht.trans hts
  set θ := t/s with hθ
  have hθ0 : 0 < θ := div_pos ht hs
  have hθ1 : θ < 1 := (div_lt_one hs).mpr hts
  have hne : (0:ℝ) ≠ -(k*s) := by have : 0 < k*s := mul_pos hk hs; linarith
  have h := strictConvexOn_exp.2 (mem_univ 0) (mem_univ (-(k*s))) hne (by linarith : 0 < 1-θ) hθ0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have ht' : t = θ * s := by simp only [hθ]; field_simp
  rw [ht', show -(k*(θ*s)) = θ * -(k*s) by ring]
  nlinarith

/-- Estimate under the stated parameter and domain assumptions: `(erf x).re < Real.sqrt
(1-Real.exp (-4*x^2/π))`. -/
@[dlmf 7.8.E8]
theorem Real.erf_exponential_bound {x : ℝ} (hx : 0 < x) :
    (erf x).re < Real.sqrt (1-Real.exp (-4*x^2/π)) := by
  have hre : (erf x).re = TauCeti.Real.erf x := by
    rw [erf_ofReal]; simp
  rw [hre]
  set k : ℝ := 4/π with hk
  set c : ℝ := 2/Real.sqrt π with hc
  have hπ := Real.pi_pos
  have hsπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have hk0 : 0 < k := by positivity
  have hc0 : 0 < c := by positivity
  have hck : c^2 = k := by
    simp only [hc, hk, div_pow, Real.sq_sqrt hπ.le]; norm_num
  have hk1 : 1 < k := by rw [hk, lt_div_iff₀ hπ]; linarith [Real.pi_lt_four]
  set m : ℝ := 2*(k-1) with hm
  have hk2 : 0 < 2 - k := by
    have : k < 2 := by rw [hk, div_lt_iff₀ hπ]; linarith [Real.pi_gt_three]
    linarith
  set ph : ℝ → ℝ := fun u => Real.exp (-((2-k)*u)) - 1 + m*u with hph
  set D : ℝ → ℝ := fun y => TauCeti.Real.erf y - c*y*Real.exp ((1-k)*y^2) with hD
  have hDd : ∀ y, HasDerivAt D (c*Real.exp ((1-k)*y^2) * ph (y^2)) y := by
    intro y
    have he : HasDerivAt (fun y : ℝ => Real.exp ((1-k)*y^2)) (Real.exp ((1-k)*y^2) * ((1-k)*(2*y))) y := by
      have := ((hasDerivAt_pow 2 y).const_mul (1-k)).exp
      exact this.congr_deriv (by norm_num)
    have := (TauCeti.Real.hasDerivAt_erf y).sub (((hasDerivAt_id y).const_mul c).mul he)
    refine this.congr_deriv ?_
    simp only [hph, hm, id, ← hc]
    have : Real.exp (-y^2) = Real.exp ((1-k)*y^2) * Real.exp (-((2-k)*y^2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have hD0 : D 0 = 0 := by simp [hD]
  -- (P): once `D ≥ 0` at a positive point, it stays positive afterwards
  have hP : ∀ y, 0 < y → 0 ≤ D y → ∀ t, y < t → 0 < D t := by
    intro y hy hDy
    have hphy : 0 < ph (y^2) := by
      by_contra hcon
      push Not at hcon
      have hneg : ∀ s, 0 < s → s < y → c*Real.exp ((1-k)*s^2) * ph (s^2) < 0 := by
        intro s hs hsy
        have h1 := bndAsy_phi_lt (m := m) hk2 (by positivity : 0 < s^2)
          (by nlinarith : s^2 < y^2)
        have h2 : s^2/y^2 * ph (y^2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
        have : ph (s^2) < 0 := by simp only [hph] at h2 ⊢; linarith
        exact mul_neg_of_pos_of_neg (by positivity) this
      have hanti : StrictAntiOn D (Icc 0 y) :=
        strictAntiOn_of_deriv_neg (convex_Icc 0 y) (fun s _ => (hDd s).continuousAt.continuousWithinAt)
          (fun s hs => by rw [interior_Icc] at hs; rw [(hDd s).deriv]; exact hneg s hs.1 hs.2)
      have := hanti ⟨le_rfl, hy.le⟩ ⟨hy.le, le_rfl⟩ hy
      linarith
    have hpos : ∀ s, y ≤ s → 0 < c*Real.exp ((1-k)*s^2) * ph (s^2) := by
      intro s hs
      rcases hs.eq_or_lt with h | h
      · subst h; positivity
      · have h1 := bndAsy_phi_lt (m := m) hk2 (by positivity : 0 < y^2) (by nlinarith : y^2 < s^2)
        have h2 : 0 < ph (s^2) := by
          by_contra hcon
          push Not at hcon
          have : y^2/s^2 * ph (s^2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
          simp only [hph] at this hphy h1; linarith
        positivity
    have hmono : StrictMonoOn D (Ici y) :=
      strictMonoOn_of_deriv_pos (convex_Ici y) (fun s _ => (hDd s).continuousAt.continuousWithinAt)
        (fun s hs => by rw [interior_Ici] at hs; rw [(hDd s).deriv]; exact hpos s hs.le)
    intro t ht
    have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht.le) ht
    linarith
  -- `h = 1 - e^{-ky²} - erf² ` with `h' = -2c e^{-y²} D`
  set h : ℝ → ℝ := fun y => 1 - Real.exp (-(k*y^2)) - TauCeti.Real.erf y^2 with hh
  have hhd : ∀ y, HasDerivAt h (-(2*c*Real.exp (-y^2)) * D y) y := by
    intro y
    have he : HasDerivAt (fun y : ℝ => Real.exp (-(k*y^2))) (Real.exp (-(k*y^2)) * (-(k*(2*y)))) y := by
      have := ((hasDerivAt_pow 2 y).const_mul k).neg.exp
      exact this.congr_deriv (by norm_num)
    have := (he.const_sub 1).sub ((TauCeti.Real.hasDerivAt_erf y).pow 2)
    refine this.congr_deriv ?_
    simp only [hD, ← hc]
    have : Real.exp (-(k*y^2)) = Real.exp (-y^2) * Real.exp ((1-k)*y^2) := by
      rw [← Real.exp_add]; ring_nf
    rw [this, ← hck]; norm_num; ring
  have hh0 : h 0 = 0 := by simp [hh, TauCeti.Real.erf_zero]
  have hhx : 0 < h x := by
    rcases le_or_gt 0 (D x) with hDx | hDx
    · have hlim : Tendsto h atTop (𝓝 0) := by
        have h1 : Tendsto (fun y : ℝ => Real.exp (-(k*y^2))) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
            ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hk0))
        have h2 := TauCeti.Real.tendsto_erf_atTop.pow 2
        have := (h1.const_sub 1).sub h2
        simpa using this
      refine bndAsy_tail_pos (fun y _ => hhd y) hlim (fun y hy => ?_)
      have := hP x hx hDx y hy
      have : 0 < 2*c*Real.exp (-y^2) := by positivity
      nlinarith
    · have hneg : ∀ y, 0 < y → y < x → D y < 0 := by
        intro y hy hyx
        by_contra hcon
        push Not at hcon
        have := hP y hy hcon x hyx
        linarith
      have hmono : StrictMonoOn h (Icc 0 x) :=
        strictMonoOn_of_deriv_pos (convex_Icc 0 x) (fun s _ => (hhd s).continuousAt.continuousWithinAt)
          (fun s hs => by
            rw [interior_Icc] at hs; rw [(hhd s).deriv]
            have := hneg s hs.1 hs.2
            have : 0 < 2*c*Real.exp (-s^2) := by positivity
            nlinarith)
      have := hmono ⟨le_rfl, hx.le⟩ ⟨hx.le, le_rfl⟩ hx
      linarith
  rw [Real.lt_sqrt (TauCeti.Real.erf_nonneg hx.le)]
  have : -4*x^2/π = -(k*x^2) := by rw [hk]; ring
  rw [this]
  simp only [hh] at hhx
  linarith

/-- Monotonicity theorem stated in the prose of DLMF §7.8. -/
theorem Real.dawsonF_normalized_strictAnti  :
    StrictAntiOn (fun x : ℝ => Real.dawsonF x/Real.sqrt (1-Real.exp (-2*x^2))) (Ioi 0) := by
  have hF : ∀ x : ℝ, HasDerivAt Real.dawsonF (1 - 2*x*Real.dawsonF x) x := by
    intro x
    have hI : HasDerivAt (fun x => ∫ t in (0:ℝ)..x, Real.exp (t^2)) (Real.exp (x^2)) x :=
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (t^2)).integral_hasStrictDerivAt 0 x).hasDerivAt
    have he : HasDerivAt (fun x : ℝ => Real.exp (-x^2)) (Real.exp (-x^2) * (-(2*x))) x := by
      have := (hasDerivAt_pow 2 x).neg.exp
      exact this.congr_deriv (by norm_num)
    have := he.mul hI
    refine this.congr_deriv ?_
    rw [Real.dawsonF, show Real.exp (-x^2) * Real.exp (x^2) = 1 by rw [← Real.exp_add]; simp]
    ring
  have hu : ∀ x : ℝ, 0 < x → 0 < 1 - Real.exp (-2*x^2) := by
    intro x hx
    have : Real.exp (-2*x^2) < 1 := by
      have := Real.exp_lt_exp.mpr (show -2*x^2 < 0 by nlinarith); rwa [Real.exp_zero] at this
    linarith
  have hg : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => Real.sqrt (1-Real.exp (-2*x^2)))
      ((4*x*Real.exp (-2*x^2))/(2*Real.sqrt (1-Real.exp (-2*x^2)))) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => 1 - Real.exp (-2*x^2)) (4*x*Real.exp (-2*x^2)) x := by
      have := (((hasDerivAt_pow 2 x).const_mul (-2)).exp).const_sub 1
      exact this.congr_deriv (by push_cast; ring)
    exact h1.sqrt (hu x hx).ne'
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · intro x hx
    exact ((hF x).continuousAt.div (hg x hx).continuousAt
      (Real.sqrt_pos.mpr (hu x hx)).ne').continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    have hgp := Real.sqrt_pos.mpr (hu x hx0)
    have hd : HasDerivAt (fun x : ℝ => Real.dawsonF x/Real.sqrt (1-Real.exp (-2*x^2))) _ x :=
      (hF x).div (hg x hx0) hgp.ne'
    rw [hd.deriv]
    set E := Real.exp (-2*x^2) with hE
    set g := Real.sqrt (1-E) with hgdef
    have hg2 : g^2 = 1 - E := Real.sq_sqrt (hu x hx0).le
    -- `2xF > 1 - E` from DLMF 7.8.7
    have hb := (Real.dawsonF_integral_bounds hx0).1
    have hkey : 1 - E < 2*x*Real.dawsonF x := by
      have hex : Real.exp (x^2) * Real.exp (-x^2) = 1 := by rw [← Real.exp_add]; simp
      have hE' : E = Real.exp (-x^2) * Real.exp (-x^2) := by rw [hE, ← Real.exp_add]; ring_nf
      rw [Real.sinh_eq, div_lt_iff₀ hx0] at hb
      have hp := Real.exp_pos (-x^2)
      have := mul_lt_mul_of_pos_left hb (by positivity : (0:ℝ) < 2*Real.exp (-x^2))
      have h2 : Real.exp (x^2) * Real.exp (-(x^2)) = 1 := hex
      rw [hE']
      nlinarith [h2]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have : (1 - 2*x*Real.dawsonF x) * g - Real.dawsonF x * (4*x*E/(2*g)) =
        (1 - E - 2*x*Real.dawsonF x)/g := by
      field_simp
      rw [hg2]; ring
    rw [this]
    exact div_neg_of_neg_of_pos (by linarith) hgp

/-- Continued-fraction representation: `HasContinuedFraction (fun k => if k=0 then z else (k :
ℂ)/2) (fun k => if Even k then z^2 else 1) (Real.sqrt π*exp (z^2)*erfc z)`. -/
@[dlmf 7.9.E1]
theorem erfc_continuedFraction_one {z : ℂ} (hz : 0 < z.re) :
    HasContinuedFraction (fun k => if k=0 then z else (k : ℂ)/2) (fun k => if Even k then z^2 else 1) (Real.sqrt π*exp (z^2)*erfc z) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hw : z ^ 2 ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    by_cases hi : z.im = 0
    · left
      have : (z ^ 2).re = z.re ^ 2 := by simp [sq, hi]
      rw [this]; positivity
    · right
      have : (z ^ 2).im = 2 * z.re * z.im := by simp [sq]; ring
      rw [this]; exact mul_ne_zero (mul_ne_zero two_ne_zero hz.ne') hi
  have hc : ∀ k : ℕ, 1 ≤ k → (k : ℂ) / 2 = (incGF_c (1/2) k : ℂ) := by
    intro k _
    unfold incGF_c
    split_ifs with h
    · have : (k : ℂ) = ((k / 2 : ℕ) : ℂ) * 2 + 1 := by
        have : k = k / 2 * 2 + 1 := by omega
        exact_mod_cast this
      rw [this]; push_cast; ring
    · have : (k : ℂ) = ((k / 2 : ℕ) : ℂ) * 2 := by
        have : k = k / 2 * 2 := by omega
        exact_mod_cast this
      rw [this]; push_cast; ring
  rw [incGF_hasContinuedFraction_iff (fun k hk => by
    simp only [show k ≠ 0 by omega, ↓reduceIte]
    exact div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) two_ne_zero)]
  have h := incGF_formB_tendsto (α := 1/2) (by norm_num) z hw
    (a := fun k => if k=0 then z else (k : ℂ)/2) (by simp)
    (fun k hk => by simp only [show k ≠ 0 by omega, ↓reduceIte]; exact hc k hk)
  convert h using 2
  have hp : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [erfc_upperIncGamma hz, sq_cpow_of_re_pos hz]
  push_cast
  rw [show (2 : ℂ) * -(1/2) = -1 by norm_num, cpow_neg_one]
  field_simp

/-- Continued-fraction representation: `HasContinuedFraction (fun k => if k=0 then 2*z else
-(2*k-1 : ℂ)*(2*k)) (fun k => 2*z^2+4*k+1) (Real.sqrt π*exp (z^2)*erfc z)`. -/
@[dlmf 7.9.E2]
theorem erfc_continuedFraction_two {z : ℂ} (hz : 0 < z.re) :
    HasContinuedFraction (fun k => if k=0 then 2*z else -(2*k-1 : ℂ)*(2*k)) (fun k => 2*z^2+4*k+1) (Real.sqrt π*exp (z^2)*erfc z) := by
  set a1 : ℕ → ℂ := fun k => if k=0 then z else (k : ℂ)/2 with ha1
  set b1 : ℕ → ℂ := fun k => if Even k then z^2 else 1 with hb1
  set a2 : ℕ → ℂ := fun k => if k=0 then 2*z else -(2*k-1 : ℂ)*(2*k) with ha2
  set b2 : ℕ → ℂ := fun k => 2*z^2+4*k+1 with hb2
  have h1 := erfc_continuedFraction_one hz
  have hn1 : ∀ k, 1 ≤ k → a1 k ≠ 0 := fun k hk => by
    simp only [a1, show k ≠ 0 by omega, ↓reduceIte]
    exact div_ne_zero (Nat.cast_ne_zero.mpr (by omega)) two_ne_zero
  have hn2 : ∀ k, 1 ≤ k → a2 k ≠ 0 := fun k hk => by
    simp only [a2, show k ≠ 0 by omega, ↓reduceIte]
    refine mul_ne_zero (neg_ne_zero.mpr ?_) (mul_ne_zero two_ne_zero
      (Nat.cast_ne_zero.mpr (by omega)))
    intro h
    have : (2 * k - 1 : ℂ) = ((2 * k - 1 : ℕ) : ℂ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, Nat.cast_eq_zero] at h
    omega
  -- the even contraction of the continuants
  have hb1o : ∀ n : ℕ, b1 (2 * n + 1) = 1 := fun n => by
    have : ¬ Even (2 * n + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one n)
    simp only [b1, this, ↓reduceIte]
  have hb1e : ∀ n : ℕ, b1 (2 * n + 2) = z ^ 2 := fun n => by
    simp only [b1, show Even (2 * n + 2) from ⟨n + 1, by ring⟩, ↓reduceIte]
  have hcontr : ∀ X : ℕ → ℂ, (∀ m, X (m + 2) = b1 (m + 1) * X (m + 1) + a1 (m + 1) * X m) →
      ∀ n, X (2 * n + 4) = (z ^ 2 + a1 (2 * n + 2) + a1 (2 * n + 3)) * X (2 * n + 2)
        - a1 (2 * n + 1) * a1 (2 * n + 2) * X (2 * n) := by
    intro X hX n
    have E1 : X (2 * n + 4) = b1 (2 * (n + 1) + 1) * X (2 * n + 3)
        + a1 (2 * n + 3) * X (2 * n + 2) := hX (2 * n + 2)
    have E2 : X (2 * n + 3) = b1 (2 * n + 2) * X (2 * n + 2)
        + a1 (2 * n + 2) * X (2 * n + 1) := hX (2 * n + 1)
    have E3 : X (2 * n + 2) = b1 (2 * n + 1) * X (2 * n + 1)
        + a1 (2 * n + 1) * X (2 * n) := hX (2 * n)
    rw [hb1o] at E1 E3
    rw [hb1e] at E2
    linear_combination E1 + E2 - a1 (2 * n + 2) * E3
  have ha1v : ∀ n : ℕ, a1 (n + 1) = ((n : ℂ) + 1) / 2 := fun n => by
    simp only [a1, Nat.succ_ne_zero, ↓reduceIte]; push_cast; ring
  have key : ∀ X Y : ℕ → ℂ, (∀ m, X (m + 2) = b1 (m + 1) * X (m + 1) + a1 (m + 1) * X m) →
      (∀ m, Y (m + 2) = b2 (m + 1) * Y (m + 1) + a2 (m + 1) * Y m) →
      Y 0 = X 0 → Y 1 = 2 * X 2 → ∀ N, Y N = 2 ^ N * X (2 * N) := by
    intro X Y hX hY h0 h1' N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      rcases N with _ | _ | n
      · simpa using h0
      · simpa using h1'
      · rw [hY n, ih (n + 1) (by omega), ih n (by omega),
          show 2 * (n + 2) = 2 * n + 4 by ring, hcontr X hX n,
          show 2 * (n + 1) = 2 * n + 2 by ring]
        rw [show 2 * n + 2 = (2 * n + 1) + 1 by ring, show 2 * n + 3 = (2 * n + 2) + 1 by ring,
          ha1v, ha1v, show 2 * n + 1 = (2 * n) + 1 by ring, ha1v]
        simp only [b2, a2, Nat.succ_ne_zero, ↓reduceIte]
        push_cast
        ring
  set g1 := GenContFract.cfConv_ofFun (0 : ℂ) a1 b1
  set g2 := GenContFract.cfConv_ofFun (0 : ℂ) a2 b2
  have hX : ∀ m, g1.nums (m + 2) = b1 (m + 1) * g1.nums (m + 1) + a1 (m + 1) * g1.nums m :=
    GenContFract.cfConv_nums_step 0 a1 b1
  have hXd : ∀ m, g1.dens (m + 2) = b1 (m + 1) * g1.dens (m + 1) + a1 (m + 1) * g1.dens m :=
    GenContFract.cfConv_dens_step 0 a1 b1
  have hNum := key _ _ hX (GenContFract.cfConv_nums_step 0 a2 b2) rfl (by
      rw [GenContFract.cfConv_nums_one, show g1.nums 2 = g1.nums (0 + 2) from rfl, hX,
        GenContFract.cfConv_nums_one, GenContFract.cfConv_nums_zero]
      simp [a1, a2, b1, b2])
  have hDen := key _ _ hXd (GenContFract.cfConv_dens_step 0 a2 b2) (by
      simp [g1, g2, GenContFract.cfConv_dens_zero]) (by
      rw [GenContFract.cfConv_dens_one, show g1.dens 2 = g1.dens (0 + 2) from rfl, hXd,
        GenContFract.cfConv_dens_one, GenContFract.cfConv_dens_zero]
      simp [a1, a2, b1, b2]; ring)
  have htail : ∀ N, DLMF.cfTail a2 b2 0 N = DLMF.cfTail a1 b1 0 (2 * N) := by
    intro N
    rw [incGF_cfTail_eq hn2, incGF_cfTail_eq hn1]
    change g2.nums N / g2.dens N = g1.nums (2 * N) / g1.dens (2 * N)
    rw [hNum, hDen, mul_div_mul_left _ _ (pow_ne_zero _ two_ne_zero)]
  unfold HasContinuedFraction at h1 ⊢
  rw [show DLMF.cfTail a2 b2 0 = fun N => DLMF.cfTail a1 b1 0 (2 * N) from funext htail]
  exact h1.comp (tendsto_atTop_mono (fun n => show n ≤ 2 * n by omega) tendsto_id)

end DLMF.Confluent
end
