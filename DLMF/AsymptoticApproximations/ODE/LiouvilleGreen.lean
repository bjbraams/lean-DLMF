/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Basic
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenReal

/-!
# The Liouville–Green (WKBJ) approximation (DLMF §2.7(iii))

The Liouville–Green theorem 2.7.20–2.7.25 for `w'' = (f + g) w` on an interval `(a₁, a₂)`,
with the error bounds controlled by the variation of the error-control function
`F = ∫ (f^{-1/4} (f^{-1/4})'' - g f^{-1/2})`. The integrand of `F` is DLMFMathlib's
`LiouvilleGreen.errorDensity f f' f'' g` (with `f'`, `f''` the derivatives of `f`), so
`𝒱_{a₁,x}(F) = ∫_{(a₁,x]} |errorDensity|` (2.7.25).

* `liouvilleGreen_interval`: the theorem on a finite interval (admitted).
* `liouvilleGreen_recessive_atTop`: the case `a₂ = +∞`, `j = 2`, a corollary of DLMFMathlib's
  `LiouvilleGreen.exists_solution_exp_of_pos` (Olver, Ch. 6, Thm. 2.1) with `u = 1` (proved).
* `liouvilleGreen_recessive_isEquivalent`: 2.7.27 for `a₂ = +∞` (proved).
* 2.7.26–2.7.30 on a finite interval, and the example 2.7.31–2.7.34 (admitted).
-/

@[expose] public noncomputable section

open Set Filter Asymptotics MeasureTheory
open scoped Topology

namespace DLMF.AsymptoticApproximations

open LiouvilleGreen

/-- **The Liouville–Green approximation theorem** (DLMF 2.7.20–2.7.25) on a finite interval
`(a₁, a₂)`: if `f > 0` is `C²` and `g` continuous, then `w'' = (f + g) w` has `C²` solutions
`w₁ = f^{-1/4} e^{ξ} (1 + ε₁)` and `w₂ = f^{-1/4} e^{-ξ} (1 + ε₂)` with
`|ε_j(x)|, ½ f^{-1/2}(x) |ε_j'(x)| ≤ exp(½ 𝒱_{a_j,x}(F)) - 1`, provided the variations
`𝒱_{a₁,x}(F) = ∫_{a₁}^x |F'|` and `𝒱_{x,a₂}(F)` are finite (integrability hypotheses). -/
@[dlmf 2.7.E20, dlmf 2.7.E21, dlmf 2.7.E22, dlmf 2.7.E23, dlmf 2.7.E24, dlmf 2.7.E25]
theorem liouvilleGreen_interval {a₁ a₂ : ℝ} (ha : a₁ < a₂) {f f' f'' g ξ : ℝ → ℝ}
    (hd : IsLGData f f' f'' g ξ (Ioo a₁ a₂)) :
    ((∀ x ∈ Ioo a₁ a₂, IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioc a₁ x)) →
      ∃ ε ε' : ℝ → ℝ, IsLGSolOn f g (fun x => lgApproximant f ξ 1 x * (1 + ε x)) (Ioo a₁ a₂) ∧
        ∀ x ∈ Ioo a₁ a₂, HasDerivAt ε (ε' x) x ∧
          |ε x| ≤ Real.exp ((∫ t in Ioc a₁ x, |errorDensity f f' f'' g t|) / 2) - 1 ∧
          (√(f x))⁻¹ * |ε' x| / 2 ≤
            Real.exp ((∫ t in Ioc a₁ x, |errorDensity f f' f'' g t|) / 2) - 1) ∧
    ((∀ x ∈ Ioo a₁ a₂, IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ico x a₂)) →
      ∃ ε ε' : ℝ → ℝ, IsLGSolOn f g (fun x => lgApproximant f ξ (-1) x * (1 + ε x)) (Ioo a₁ a₂) ∧
        ∀ x ∈ Ioo a₁ a₂, HasDerivAt ε (ε' x) x ∧
          |ε x| ≤ Real.exp ((∫ t in Ico x a₂, |errorDensity f f' f'' g t|) / 2) - 1 ∧
          (√(f x))⁻¹ * |ε' x| / 2 ≤
            Real.exp ((∫ t in Ico x a₂, |errorDensity f f' f'' g t|) / 2) - 1) := by
  sorry

/-- DLMF 2.7.22–2.7.23 for the half-line `(a, ∞)` (`a₂ = +∞`, `j = 2`): the recessive solution
`w₂ = f^{-1/4} e^{-ξ} (1 + ε₂)` with `|ε₂|, ½ f^{-1/2} |ε₂'| ≤ exp(½ 𝒱_{x,∞}(F)) - 1`.
Corollary of DLMFMathlib's `LiouvilleGreen.exists_solution_exp_of_pos` with `u = 1`. -/
@[dlmf 2.7.E22, dlmf 2.7.E23, dlmf 2.7.E20]
theorem liouvilleGreen_recessive_atTop {a : ℝ} {f f' f'' g ξ : ℝ → ℝ}
    (hd : IsLGData f f' f'' g ξ (Ioi a))
    (hV : ∀ c, a < c → IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioi c)) :
    ∃ ε ε' : ℝ → ℝ, IsLGSolOn f g (fun x => lgApproximant f ξ (-1) x * (1 + ε x)) (Ioi a) ∧
      ∀ x ∈ Ioi a, HasDerivAt ε (ε' x) x ∧
        |ε x| ≤ Real.exp ((∫ t in Ioi x, |errorDensity f f' f'' g t|) / 2) - 1 ∧
        (√(f x))⁻¹ * |ε' x| / 2 ≤
          Real.exp ((∫ t in Ioi x, |errorDensity f f' f'' g t|) / 2) - 1 := by
  obtain ⟨ε, ε', w', H⟩ := exists_solution_exp_of_pos (a := a) one_pos (g := g)
    (fun x hx => hd.pos x hx) (fun x hx => hd.hasDerivAt_f x hx)
    (fun x hx => hd.hasDerivAt_f' x hx) hd.continuousOn_f'' hd.continuousOn_g
    (fun x hx => hd.hasDerivAt_ξ x hx) hV
  refine ⟨ε, ε', ⟨w', fun x hx => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨-, h2, h3, -, -⟩ := H x hx
    refine ⟨?_, ?_⟩
    · convert h2 using 2 with y
      simp [lgApproximant]
    · convert h3 using 1
      simp [lgApproximant]
  · obtain ⟨h1, -, -, h4, h5⟩ := H x hx
    refine ⟨h1, by simpa using h4, ?_⟩
    have hs : 0 < √(f x) := Real.sqrt_pos.2 (hd.pos x hx)
    rw [mul_one] at h5
    rw [inv_mul_eq_div, div_div, div_le_iff₀ (by positivity)]
    calc |ε' x| ≤ 2 * √(f x) * (Real.exp ((∫ t in Ioi x, |errorDensity f f' f'' g t|) / 2) - 1) :=
          h5
      _ = _ := by ring

/-- DLMF 2.7.27 for `a₂ = +∞`: `w₂(x) ∼ f^{-1/4}(x) exp(-∫ f^{1/2})` as `x → +∞`, for the
recessive solution of `liouvilleGreen_recessive_atTop`. -/
@[dlmf 2.7.E27]
theorem liouvilleGreen_recessive_isEquivalent {a : ℝ} {f f' f'' g ξ : ℝ → ℝ}
    (hd : IsLGData f f' f'' g ξ (Ioi a))
    (hV : ∀ c, a < c → IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioi c)) :
    ∃ ε : ℝ → ℝ, IsLGSolOn f g (fun x => lgApproximant f ξ (-1) x * (1 + ε x)) (Ioi a) ∧
      (fun x => lgApproximant f ξ (-1) x * (1 + ε x)) ~[atTop] lgApproximant f ξ (-1) := by
  obtain ⟨ε, ε', hsol, H⟩ := liouvilleGreen_recessive_atTop hd hV
  refine ⟨ε, hsol, ?_⟩
  have hε : Tendsto ε atTop (𝓝 0) := by
    have hb := lg_tendsto_exp_integral_Ioi_sub_one (hV (a + 1) (by linarith)) (1 / 2)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop a] with x hx
    rw [Real.norm_eq_abs, show 1 / 2 * ∫ t in Ioi x, |errorDensity f f' f'' g t| =
      (∫ t in Ioi x, |errorDensity f f' f'' g t|) / 2 by ring]
    exact (H x hx).2.1
  refine isEquivalent_of_tendsto_one ?_
  have h1 : Tendsto (fun x => 1 + ε x) atTop (𝓝 1) := by simpa using hε.const_add 1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop a] with x hx
  have hne : lgApproximant f ξ (-1) x ≠ 0 := by
    unfold lgApproximant
    exact mul_ne_zero (Real.rpow_pos_of_pos (hd.pos x hx) _).ne' (Real.exp_pos _).ne'
  simp only [Pi.div_apply]
  field_simp

/-- DLMF 2.7.26–2.7.27 on a finite interval: if moreover `𝒱_{a₁,a₂}(F) < ∞`, then the solutions
of `liouvilleGreen_interval` satisfy `w₁(x) ∼ f^{-1/4} e^{ξ}` as `x → a₁+` and
`w₂(x) ∼ f^{-1/4} e^{-ξ}` as `x → a₂-`; solutions with these properties are unique.

**Qualification needed:** the uniqueness assertion fails at regular endpoints under the
present hypotheses. For `f = 1`, `g = 0`, `ξ(x) = x` on `(0, 1)`, both `exp x` and
`exp x + sinh x` solve the equation and are equivalent to `exp x` at `0+`.
An endpoint condition is missing; see the proof-round review of 2026-10-29. -/
@[dlmf 2.7.E26, dlmf 2.7.E27]
theorem liouvilleGreen_interval_isEquivalent {a₁ a₂ : ℝ} (ha : a₁ < a₂) {f f' f'' g ξ : ℝ → ℝ}
    (hd : IsLGData f f' f'' g ξ (Ioo a₁ a₂))
    (hV : IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioo a₁ a₂)) :
    (∃ w₁ : ℝ → ℝ, IsLGSolOn f g w₁ (Ioo a₁ a₂) ∧ w₁ ~[𝓝[>] a₁] lgApproximant f ξ 1 ∧
      ∀ v, IsLGSolOn f g v (Ioo a₁ a₂) → v ~[𝓝[>] a₁] lgApproximant f ξ 1 →
        EqOn v w₁ (Ioo a₁ a₂)) ∧
    (∃ w₂ : ℝ → ℝ, IsLGSolOn f g w₂ (Ioo a₁ a₂) ∧ w₂ ~[𝓝[<] a₂] lgApproximant f ξ (-1) ∧
      ∀ v, IsLGSolOn f g v (Ioo a₁ a₂) → v ~[𝓝[<] a₂] lgApproximant f ξ (-1) →
        EqOn v w₂ (Ioo a₁ a₂)) := by
  sorry

/-- DLMF 2.7.28–2.7.30: if in addition `|ξ|` is unbounded as `x → a₁+` and as `x → a₂-`, there
are solutions `w₃ ∼ f^{-1/4} e^{ξ}` as `x → a₂-` and `w₄ ∼ f^{-1/4} e^{-ξ}` as `x → a₁+`, and
`w₁/w₄ → 0` as `x → a₁+` (`w₁` recessive, `w₄` dominant), `w₂/w₃ → 0` as `x → a₂-`. -/
@[dlmf 2.7.E28, dlmf 2.7.E29, dlmf 2.7.E30, dlmf 2.7.iii]
theorem liouvilleGreen_dominant {a₁ a₂ : ℝ} (ha : a₁ < a₂) {f f' f'' g ξ : ℝ → ℝ}
    (hd : IsLGData f f' f'' g ξ (Ioo a₁ a₂))
    (hV : IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioo a₁ a₂))
    (hξ₁ : ¬ IsBoundedUnder (· ≤ ·) (𝓝[>] a₁) (fun x => |ξ x|))
    (hξ₂ : ¬ IsBoundedUnder (· ≤ ·) (𝓝[<] a₂) (fun x => |ξ x|))
    {w₁ w₂ : ℝ → ℝ} (hw₁ : IsLGSolOn f g w₁ (Ioo a₁ a₂)) (hw₂ : IsLGSolOn f g w₂ (Ioo a₁ a₂))
    (hw₁e : w₁ ~[𝓝[>] a₁] lgApproximant f ξ 1) (hw₂e : w₂ ~[𝓝[<] a₂] lgApproximant f ξ (-1)) :
    ∃ w₃ w₄ : ℝ → ℝ, IsLGSolOn f g w₃ (Ioo a₁ a₂) ∧ IsLGSolOn f g w₄ (Ioo a₁ a₂) ∧
      w₃ ~[𝓝[<] a₂] lgApproximant f ξ 1 ∧ w₄ ~[𝓝[>] a₁] lgApproximant f ξ (-1) ∧
      Tendsto (fun x => w₁ x / w₄ x) (𝓝[>] a₁) (𝓝 0) ∧
      Tendsto (fun x => w₂ x / w₃ x) (𝓝[<] a₂) (𝓝 0) := by
  sorry

/-- DLMF 2.7.32: `(x + ln x)^{1/2} = x^{1/2} + ½ x^{-1/2} ln x + O(x^{-3/2} (ln x)²)` as
`x → +∞`. -/
@[dlmf 2.7.E32]
theorem sqrt_add_log_expansion :
    (fun x : ℝ => √(x + Real.log x) - (√x + Real.log x / (2 * √x)))
      =O[atTop] (fun x : ℝ => x ^ (-(3 / 2) : ℝ) * Real.log x ^ 2) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  let a := Real.sqrt (x + Real.log x)
  let b := Real.sqrt x
  have hb : 0 < b := Real.sqrt_pos.mpr hx0
  have ha : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hb2 : b ^ 2 = x := Real.sq_sqrt hx0.le
  have ha2 : a ^ 2 = x + Real.log x := Real.sq_sqrt (by linarith)
  have hsum : a + b ≠ 0 := by linarith
  have hlog : Real.log x = a ^ 2 - b ^ 2 := by linarith
  have herr : a - (b + Real.log x / (2 * b)) =
      -(Real.log x ^ 2 / (2 * b * (a + b) ^ 2)) := by
    rw [hlog]
    field_simp
    ring
  have hd : 0 < 2 * b * (a + b) ^ 2 := by positivity
  have hden : x * b ≤ 2 * b * (a + b) ^ 2 := by
    have hs : x ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg a]
    nlinarith
  have hp : x ^ (-(3 / 2) : ℝ) = 1 / (x * b) := by
    rw [Real.rpow_neg hx0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hx0, Real.rpow_one, ← Real.sqrt_eq_rpow]
    simp only [one_div, b]
  change ‖a - (b + Real.log x / (2 * b))‖ ≤ _
  rw [herr, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), hp]
  calc Real.log x ^ 2 / (2 * b * (a + b) ^ 2) ≤ Real.log x ^ 2 / (x * b) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    _ = 1 / (x * b) * Real.log x ^ 2 := by ring

/-- DLMF 2.7.31, 2.7.33–2.7.34 (example): the equation `w'' = (x + ln x) w` on `(0, ∞)` has a
recessive solution `w₂(x) ∼ x^{-1/4-√x} exp(2x^{1/2} - (2/3)x^{3/2})` and a dominant solution
`w₃(x) ∼ x^{-1/4+√x} exp((2/3)x^{3/2} - 2x^{1/2})` as `x → +∞`. -/
@[dlmf 2.7.E31, dlmf 2.7.E33, dlmf 2.7.E34]
theorem liouvilleGreen_example :
    ∃ w₂ w₃ : ℝ → ℝ,
      IsLGSolOn (fun x => x + Real.log x) (fun _ => 0) w₂ (Ioi 0) ∧
      IsLGSolOn (fun x => x + Real.log x) (fun _ => 0) w₃ (Ioi 0) ∧
      w₂ ~[atTop] (fun x => x ^ (-(1 / 4) - √x) *
        Real.exp (2 * x ^ (1 / 2 : ℝ) - 2 / 3 * x ^ (3 / 2 : ℝ))) ∧
      w₃ ~[atTop] (fun x => x ^ (-(1 / 4) + √x) *
        Real.exp (2 / 3 * x ^ (3 / 2 : ℝ) - 2 * x ^ (1 / 2 : ℝ))) := by
  sorry

end DLMF.AsymptoticApproximations
