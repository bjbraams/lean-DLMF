/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LiouvilleGreenVolterra

/-!
# Perturbation of a comparison equation (towards turning points)

Let `y₁, y₂` solve the comparison equation `y'' = Q y` on `(a, ∞)` with Wronskian `𝒲 ≠ 0`.
For the perturbed equation `w'' = (Q + ψ) w` we construct the solution `w = y₁ + η` with
`η x = ∫_{(x,∞)} K x t ψ t w t dt`, `K x t = (y₁ x y₂ t - y₂ x y₁ t)/𝒲`, and bound `η` and `η'`
by an envelope `Φ ≥ |y₁|` and a derivative envelope `Φ₁` (F. W. J. Olver, *Asymptotics and
Special Functions*, Ch. 6, §10; the same estimate drives Ch. 11, §3 and Ch. 12, §§3–4). The
Liouville–Green theorem is the special case `y₁ = A E`, `y₂ = A / E`.

## Main results

* `LiouvilleGreen.exists_solution_of_comparison`.
* `LiouvilleGreen.wronskian_eq`: constancy of the Wronskian.

## Plan for turning points (Olver, Ch. 11)

For `w'' = (u² f + g) w` with a simple zero of `f` at `x₀` (`f (x) / (x - x₀) > 0`):

1. *Liouville transformation.* Define `ζ` by `(2/3) ζ^{3/2} = ∫_{x₀}^x f^{1/2}` for `x ≥ x₀` and
   `(2/3) (-ζ)^{3/2} = ∫_x^{x₀} (-f)^{1/2}` for `x ≤ x₀`; then `ζ ζ'² = f`, `ζ' > 0`, and `ζ` is
   `C²` when `f` is `C²` (write `f = (x - x₀) φ` with `φ > 0`).
2. *Comparison functions.* `y₁ = ζ'^{-1/2} Ai (u^{2/3} ζ)` and `y₂ = ζ'^{-1/2} Bi (u^{2/3} ζ)`
   solve `y'' = (u² f + Q₀) y` with `Q₀ = ζ'^{1/2} (ζ'^{-1/2})''` and Wronskian `u^{2/3}/π`; put
   `ψ = g - Q₀` and apply `exists_solution_of_comparison` (in the original variable `x`, so no
   change of independent variable is needed).
3. *Airy envelopes* (Olver, Ch. 11, §2): with the weight `E` and modulus `M` of the Airy
   functions, `|Ai| ≤ M / E`, `|Bi| ≤ M E`, and for `x ≤ t`,
   `|Ai x Bi t - Bi x Ai t| ≤ M(x) M(t) E(t) / E(x)`; also `λ = sup |x|^{1/2} M(x)² < ∞`. Taking
   `Φ = ζ'^{-1/2} M / E` and `ρ = λ |ψ| / (u ζ'|ζ|^{1/2})` gives Olver's Ch. 11, Thm. 3.1:
   `|ε| ≤ (M/E)(u^{2/3} ζ) (exp (λ V(H) / u) - 1)` with `H = ∫ |ψ| |ζ|^{-1/2} dζ`.
4. The Airy facts in step 3 are real-variable properties of `Ai`, `Bi` and must be proved
   alongside the Airy functions themselves (the `DLMF.Airy` area); this file deliberately depends
   on Mathlib only.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace LiouvilleGreen

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Perturbation of an equation with known solutions** (Olver, *Asymptotics and Special
Functions*, Ch. 6, §10, and the error bounds of Ch. 11, §3 and Ch. 12 in the original variable).
Let `y₁, y₂` solve `y'' = Q y` on `(a, ∞)` with constant Wronskian `y₁ y₂' - y₁' y₂ = 𝒲 ≠ 0`,
and let `Φ > 0` be an envelope of `y₁`. If the variation-of-constants kernel
`K x t = (y₁ x y₂ t - y₂ x y₁ t)/𝒲` and its `x`-derivative satisfy
`‖K x t‖ Φ t ‖ψ t‖ ≤ Φ x ρ t` and `‖∂ₓ K x t‖ Φ t ‖ψ t‖ ≤ Φ₁ x ρ t` for `a < x < t`, with `ρ`
continuous and integrable at infinity, then `w'' = (Q + ψ) w` has the solution `w = y₁ + η` with

`‖η x‖ ≤ Φ x (exp (∫_{(x,∞)} ρ) - 1)`,   `‖η' x‖ ≤ Φ₁ x (exp (∫_{(x,∞)} ρ) - 1)`.

This is the form used for turning points (comparison with Airy functions) and for
Bessel-type comparison equations. -/
theorem exists_solution_of_comparison {a : ℝ} {𝒲 : 𝕜} {Q ψ y₁ y₁' y₂ y₂' : ℝ → 𝕜}
    {Φ Φ₁ ρ : ℝ → ℝ} (h𝒲 : 𝒲 ≠ 0)
    (hy₁ : ∀ x, a < x → HasDerivAt y₁ (y₁' x) x)
    (hy₁' : ∀ x, a < x → HasDerivAt y₁' (Q x * y₁ x) x)
    (hy₂ : ∀ x, a < x → HasDerivAt y₂ (y₂' x) x)
    (hy₂' : ∀ x, a < x → HasDerivAt y₂' (Q x * y₂ x) x)
    (hW : ∀ x, a < x → y₁ x * y₂' x - y₁' x * y₂ x = 𝒲)
    (hψc : ContinuousOn ψ (Ioi a))
    (hΦ : ∀ x, a < x → 0 < Φ x) (hΦc : ContinuousOn Φ (Ioi a))
    (hy₁Φ : ∀ t, a < t → ‖y₁ t‖ ≤ Φ t)
    (hi₁ : ∀ c, a < c → IntegrableOn (fun t => y₂ t * (Φ t : 𝕜) * ψ t) (Ioi c))
    (hi₂ : ∀ c, a < c → IntegrableOn (fun t => y₁ t * (Φ t : 𝕜) * ψ t) (Ioi c))
    (hρc : ContinuousOn ρ (Ioi a)) (hρi : ∀ c, a < c → IntegrableOn ρ (Ioi c))
    (hK : ∀ x t, a < x → x < t →
      ‖y₁ x * y₂ t - y₂ x * y₁ t‖ * Φ t * ‖ψ t‖ ≤ ‖𝒲‖ * Φ x * ρ t)
    (hK₁ : ∀ x t, a < x → x < t →
      ‖y₁' x * y₂ t - y₂' x * y₁ t‖ * Φ t * ‖ψ t‖ ≤ ‖𝒲‖ * Φ₁ x * ρ t) :
    ∃ η η' : ℝ → 𝕜, ∀ x, a < x →
      HasDerivAt (fun y => y₁ y + η y) (y₁' x + η' x) x ∧
      HasDerivAt (fun y => y₁' y + η' y) ((Q x + ψ x) * (y₁ x + η x)) x ∧
      ‖η x‖ ≤ Φ x * (Real.exp (∫ t in Ioi x, ρ t) - 1) ∧
      ‖η' x‖ ≤ Φ₁ x * (Real.exp (∫ t in Ioi x, ρ t) - 1) := by
  have hy₁c : ContinuousOn y₁ (Ioi a) := fun x hx => (hy₁ x hx).continuousAt.continuousWithinAt
  have hy₂c : ContinuousOn y₂ (Ioi a) := fun x hx => (hy₂ x hx).continuousAt.continuousWithinAt
  have hΦc' : ContinuousOn (fun x => (Φ x : 𝕜)) (Ioi a) :=
    (RCLike.continuous_ofReal (K := 𝕜)).comp_continuousOn hΦc
  have hΦ0 : ∀ x, a < x → (Φ x : 𝕜) ≠ 0 := fun x hx => RCLike.ofReal_ne_zero.2 (hΦ x hx).ne'
  have hp₁c : ContinuousOn (fun x => y₁ x / (𝒲 * Φ x)) (Ioi a) :=
    hy₁c.div (continuousOn_const.mul hΦc') fun x hx => mul_ne_zero h𝒲 (hΦ0 x hx)
  have hp₂c : ContinuousOn (fun x => -y₂ x / (𝒲 * Φ x)) (Ioi a) :=
    hy₂c.neg.div (continuousOn_const.mul hΦc') fun x hx => mul_ne_zero h𝒲 (hΦ0 x hx)
  have hJc : ContinuousOn (fun t => y₁ t / (Φ t : 𝕜)) (Ioi a) := hy₁c.div hΦc' hΦ0
  obtain ⟨h, hhm, hhb, hheq⟩ := exists_volterra_solution (𝕜 := 𝕜)
    (p₁ := fun x => y₁ x / (𝒲 * Φ x)) (q₁ := fun t => y₂ t * (Φ t : 𝕜))
    (p₂ := fun x => -y₂ x / (𝒲 * Φ x)) (q₂ := fun t => y₁ t * (Φ t : 𝕜)) (ψ := ψ)
    (J := fun t => y₁ t / (Φ t : 𝕜)) (ρ := ρ) (a := a)
    (hp₁c.aestronglyMeasurable measurableSet_Ioi) (hp₂c.aestronglyMeasurable measurableSet_Ioi)
    hi₁ hi₂ (hJc.aestronglyMeasurable measurableSet_Ioi)
    (fun t ht => by
      rw [norm_div, RCLike.norm_ofReal, abs_of_pos (hΦ t ht), div_le_one (hΦ t ht)]
      exact hy₁Φ t ht)
    hρc hρi (fun x t hx ht => by
      have hΦx := hΦ x hx
      have h𝒲' : 0 < ‖𝒲‖ := norm_pos_iff.2 h𝒲
      have heq : (y₁ x / (𝒲 * Φ x) * (y₂ t * (Φ t : 𝕜)) + -y₂ x / (𝒲 * Φ x) * (y₁ t * Φ t)) *
          ψ t = (y₁ x * y₂ t - y₂ x * y₁ t) * (Φ t : 𝕜) * ψ t / (𝒲 * Φ x) := by
        field_simp
        ring
      rw [heq, norm_div, norm_mul, norm_mul, norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal,
        abs_of_pos (hΦ t (hx.trans ht)), abs_of_pos hΦx, div_le_iff₀ (by positivity)]
      have := hK x t hx ht
      nlinarith)
  have h𝒲' : 0 < ‖𝒲‖ := norm_pos_iff.2 h𝒲
  have hρ0 : ∀ t, a < t → 0 ≤ ρ t := fun t ht => by
    have h1 := hK ((a + t) / 2) t (by linarith) (by linarith)
    have h2 := hΦ ((a + t) / 2) (by linarith)
    have h3 : 0 ≤ ‖y₁ ((a + t) / 2) * y₂ t - y₂ ((a + t) / 2) * y₁ t‖ * Φ t * ‖ψ t‖ := by
      have := hΦ t ht; positivity
    by_contra hneg
    have hneg' : ρ t < 0 := lt_of_not_ge hneg
    nlinarith [mul_pos h𝒲' h2]
  set R : ℝ → ℝ := fun t => ∫ s in Ioi t, ρ s with hR
  set η : ℝ → 𝕜 := fun x => (Φ x : 𝕜) * h x with hηdef
  have hw : ∀ t, a < t → y₁ t / (Φ t : 𝕜) + h t = (y₁ t + η t) / (Φ t : 𝕜) := fun t ht => by
    have := hΦ0 t ht
    simp only [hηdef]
    field_simp
  have hwb : ∀ t, a < t → ‖y₁ t + η t‖ ≤ Φ t * Real.exp (R t) := fun t ht => by
    have h1 := hhb t ht
    calc ‖y₁ t + η t‖ ≤ ‖y₁ t‖ + ‖η t‖ := norm_add_le _ _
      _ ≤ Φ t + Φ t * (Real.exp (R t) - 1) := by
          refine add_le_add (hy₁Φ t ht) ?_
          simp only [hηdef, norm_mul, RCLike.norm_ofReal, abs_of_pos (hΦ t ht)]
          exact mul_le_mul_of_nonneg_left h1 (hΦ t ht).le
      _ = Φ t * Real.exp (R t) := by ring
  -- integrability of the integrands
  have hJh_b : ∀ c, a < c → ∀ t ∈ Ioi c, ‖y₁ t / (Φ t : 𝕜) + h t‖ ≤ Real.exp (R c) :=
    fun c hc t ht => by
      have ht' : a < t := hc.trans ht
      calc ‖y₁ t / (Φ t : 𝕜) + h t‖ ≤ ‖y₁ t / (Φ t : 𝕜)‖ + ‖h t‖ := norm_add_le _ _
        _ ≤ 1 + (Real.exp (R t) - 1) := by
            refine add_le_add ?_ (hhb t ht')
            rw [norm_div, RCLike.norm_ofReal, abs_of_pos (hΦ t ht'), div_le_one (hΦ t ht')]
            exact hy₁Φ t ht'
        _ ≤ Real.exp (R c) := by
            have := Real.exp_le_exp.2 (lg_tail_anti hρ0 hρi hc (le_of_lt ht))
            linarith
  have hJhm : AEStronglyMeasurable (fun t => y₁ t / (Φ t : 𝕜) + h t) (volume.restrict (Ioi a)) :=
    (hJc.aestronglyMeasurable measurableSet_Ioi).add hhm
  have hint : ∀ {q : ℝ → 𝕜}, (∀ c, a < c → IntegrableOn (fun t => q t * (Φ t : 𝕜) * ψ t) (Ioi c)) →
      ∀ c, a < c → IntegrableOn (fun t => q t * ψ t * (y₁ t + η t)) (Ioi c) := by
    intro q hq c hc
    refine IntegrableOn.congr_fun ((hq c hc).mul_bdd (hJhm.mono_measure (Measure.restrict_mono
      (Ioi_subset_Ioi hc.le) le_rfl))
      (ae_restrict_of_forall_mem measurableSet_Ioi (hJh_b c hc)))
      (fun t ht => ?_) measurableSet_Ioi
    have ht' : a < t := hc.trans ht
    rw [hw t ht']
    have := hΦ0 t ht'
    field_simp
  have hI₁i := hint hi₁
  have hI₂i := hint hi₂
  set I₁ : ℝ → 𝕜 := fun x => ∫ t in Ioi x, y₂ t * ψ t * (y₁ t + η t) with hI₁
  set I₂ : ℝ → 𝕜 := fun x => ∫ t in Ioi x, y₁ t * ψ t * (y₁ t + η t) with hI₂
  have hrep : ∀ x, a < x → η x = 𝒲⁻¹ * (y₁ x * I₁ x - y₂ x * I₂ x) := by
    intro x hx
    have hcongr : ∀ {q : ℝ → 𝕜}, ∫ t in Ioi x, q t * (Φ t : 𝕜) * ψ t *
        (y₁ t / (Φ t : 𝕜) + h t) = ∫ t in Ioi x, q t * ψ t * (y₁ t + η t) := by
      intro q
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht' : a < t := hx.trans ht
      rw [hw t ht']
      have := hΦ0 t ht'
      field_simp
    have := hheq x hx
    simp only [volterraOp] at this
    rw [hcongr, hcongr] at this
    simp only [hηdef]
    rw [this]
    have := hΦ0 x hx
    field_simp
    ring
  have hηc : ContinuousOn η (Ioi a) :=
    (continuousOn_const.mul ((hy₁c.mul (lg_continuousOn_integral_Ioi hI₁i)).sub
      (hy₂c.mul (lg_continuousOn_integral_Ioi hI₂i)))).congr fun x hx => hrep x hx
  have hI₁d : ∀ x, a < x → HasDerivAt I₁ (-(y₂ x * ψ x * (y₁ x + η x))) x := fun x hx =>
    lg_hasDerivAt_integral_Ioi hI₁i hx ((hy₂c.mul hψc).mul (hy₁c.add hηc) |>.continuousAt
      (Ioi_mem_nhds hx))
  have hI₂d : ∀ x, a < x → HasDerivAt I₂ (-(y₁ x * ψ x * (y₁ x + η x))) x := fun x hx =>
    lg_hasDerivAt_integral_Ioi hI₂i hx ((hy₁c.mul hψc).mul (hy₁c.add hηc) |>.continuousAt
      (Ioi_mem_nhds hx))
  obtain ⟨η', hη'def⟩ : ∃ η' : ℝ → 𝕜, η' = fun x => 𝒲⁻¹ * (y₁' x * I₁ x - y₂' x * I₂ x) :=
    ⟨_, rfl⟩
  have hηd : ∀ x, a < x → HasDerivAt η (η' x) x := by
    intro x hx
    have := (((hy₁ x hx).mul (hI₁d x hx)).sub ((hy₂ x hx).mul (hI₂d x hx))).const_mul 𝒲⁻¹
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · rw [hη'def]
      ring
    · filter_upwards [Ioi_mem_nhds hx] with y hy using hrep y hy
  have hη'd : ∀ x, a < x → HasDerivAt η'
      (𝒲⁻¹ * (Q x * y₁ x * I₁ x + y₁' x * -(y₂ x * ψ x * (y₁ x + η x)) -
        (Q x * y₂ x * I₂ x + y₂' x * -(y₁ x * ψ x * (y₁ x + η x))))) x := by
    intro x hx
    rw [hη'def]
    exact (((hy₁' x hx).mul (hI₁d x hx)).sub ((hy₂' x hx).mul (hI₂d x hx))).const_mul 𝒲⁻¹
  refine ⟨η, η', fun x hx => ⟨(hy₁ x hx).add (hηd x hx), ?_, ?_, ?_⟩⟩
  · refine ((hy₁' x hx).add (hη'd x hx)).congr_deriv ?_
    have hr := hrep x hx
    have hWx := hW x hx
    have hinv : 𝒲 * 𝒲⁻¹ = 1 := mul_inv_cancel₀ h𝒲
    rw [hr]
    linear_combination (ψ x * (y₁ x + 𝒲⁻¹ * (y₁ x * I₁ x - y₂ x * I₂ x)) * 𝒲⁻¹) * hWx +
      (ψ x * (y₁ x + 𝒲⁻¹ * (y₁ x * I₁ x - y₂ x * I₂ x))) * hinv
  · simp only [hηdef, norm_mul, RCLike.norm_ofReal, abs_of_pos (hΦ x hx)]
    exact mul_le_mul_of_nonneg_left (hhb x hx) (hΦ x hx).le
  · have hexpt := lg_integral_Ioi_mul_exp_tail hρc hρ0 hρi hx
    have hη'x : η' x = ∫ t in Ioi x, 𝒲⁻¹ * ((y₁' x * y₂ t - y₂' x * y₁ t) * ψ t *
        (y₁ t + η t)) := by
      rw [hη'def, integral_const_mul]
      simp only [hI₁, hI₂]
      rw [← integral_const_mul, ← integral_const_mul, ← integral_sub ((hI₁i x hx).const_mul _)
        ((hI₂i x hx).const_mul _)]
      rw [mul_right_inj' (inv_ne_zero h𝒲)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only
      ring
    rw [hη'x, ← hexpt.2, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hexpt.1.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have ht' : a < t := hx.trans ht
    rw [norm_mul, norm_inv, norm_mul, norm_mul]
    have h1 := hK₁ x t hx ht
    have h2 := hwb t ht'
    have hΦt := hΦ t ht'
    calc ‖𝒲‖⁻¹ * (‖y₁' x * y₂ t - y₂' x * y₁ t‖ * ‖ψ t‖ * ‖y₁ t + η t‖)
        ≤ ‖𝒲‖⁻¹ * (‖y₁' x * y₂ t - y₂' x * y₁ t‖ * ‖ψ t‖ * (Φ t * Real.exp (R t))) := by
          gcongr
      _ = ‖𝒲‖⁻¹ * (‖y₁' x * y₂ t - y₂' x * y₁ t‖ * Φ t * ‖ψ t‖) * Real.exp (R t) := by ring
      _ ≤ ‖𝒲‖⁻¹ * (‖𝒲‖ * Φ₁ x * ρ t) * Real.exp (R t) := by gcongr
      _ = Φ₁ x * (ρ t * Real.exp (R t)) := by field_simp

/-- The **Wronskian** `w₁ w₂' - w₁' w₂` of two solutions of `w'' = q w` is constant on `(a, ∞)`;
used to identify the recessive solution produced above with a given special function. -/
theorem wronskian_eq {a : ℝ} {q w₁ w₁' w₂ w₂' : ℝ → 𝕜}
    (h₁ : ∀ x, a < x → HasDerivAt w₁ (w₁' x) x)
    (h₁' : ∀ x, a < x → HasDerivAt w₁' (q x * w₁ x) x)
    (h₂ : ∀ x, a < x → HasDerivAt w₂ (w₂' x) x)
    (h₂' : ∀ x, a < x → HasDerivAt w₂' (q x * w₂ x) x) {x y : ℝ} (hx : a < x) (hy : a < y) :
    w₁ x * w₂' x - w₁' x * w₂ x = w₁ y * w₂' y - w₁' y * w₂ y := by
  have hd : ∀ z, a < z → HasDerivAt (fun z => w₁ z * w₂' z - w₁' z * w₂ z) 0 z := fun z hz =>
    (((h₁ z hz).mul (h₂' z hz)).sub ((h₁' z hz).mul (h₂ z hz))).congr_deriv (by ring)
  exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) (show x ∈ Ioi a from hx) (show y ∈ Ioi a from hy)

end LiouvilleGreen
