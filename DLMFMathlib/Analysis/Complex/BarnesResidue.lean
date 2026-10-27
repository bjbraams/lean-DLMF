/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Shifting a vertical line of integration across a simple pole

Let `φ` be holomorphic on the closed strip `c₁ ≤ Re s ≤ c₂` and let `p` be an interior point.
For `f s = φ s / (s - p)`, if `f` is integrable on the two boundary lines and its integrals over
horizontal cross-sections of the strip tend to `0` at `±i∞`, then

`∫ f(c₂ + iy) dy - ∫ f(c₁ + iy) dy = 2π φ(p)`,

i.e. moving the line `Re s = c` to the left past the pole loses `2π` times the residue (the line
integrals carry `dy`, not `ds = i dy`). This is the basic step of Barnes-integral contour shifts.

The proof applies Cauchy's theorem for rectangles to the removable-singularity function
`dslope φ p` and evaluates the rectangle integral of `(s - p)⁻¹` by the explicit primitive
`arctan (t / c) - (i/2) log (c² + t²)` of `(c + it)⁻¹` (the same primitive is used for the Perron
kernel in TauCeti, `TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron.Basic`).

## Main results

* `Complex.barnesRes_integral_recip`: `∫_{-T}^{T} (c + it)⁻¹ dt = 2 arctan (T / c)`.
* `Complex.barnesRes_vertical_shift`: the residue formula for moving a vertical line past a pole.
* `Complex.barnesRes_vertical_shift_of_differentiableOn`: the pole-free version.
* `Complex.barnesRes_sq_norm_sin` and the lower bounds `|sinh y| ≤ ‖sin (x + iy)‖`,
  `|sin x| cosh y ≤ ‖sin (x + iy)‖`, used to bound `Γ` through the reflection formula.
* `Complex.barnesRes_norm_Gamma_mul_sin_le`: `‖Γ(w)‖ ‖sin πw‖ ≤ π ‖Γ(1-w)⁻¹‖`, with the lower
  bounds `barnesRes_sin_lower_line`, `barnesRes_sin_lower_far` for `‖sin(π(x+iy))‖`.
* `Complex.barnesRes_prod_sub_nat`: `∏_{j<n} (j - n) = (-1)^n n!` (residues of `Γ`).
* `Complex.barnesRes_Gamma_add_nat_succ`: `Γ(w + n + 1) = Γ(w) ∏_{j ≤ n} (w + j)`, the
  removable-singularity form of `(s - p) Γ(·)` at a Gamma pole.
* `Complex.barnesRes_isOpen_ne_sub_nat`, `Complex.barnesRes_isPreconnected_ne_sub_nat`: the
  complement of a half-lattice `b - ℕ` is a domain (for analytic continuation in parameters).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real intervalIntegral

open scoped Topology Interval

namespace Complex

/-- A primitive of `t ↦ (c + it)⁻¹` on `ℝ` for `c ≠ 0`. -/
theorem barnesRes_hasDerivAt_primitive {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => (Real.arctan (u / c) : ℂ) - I / 2 * (Real.log (c ^ 2 + u ^ 2) : ℂ))
      (((c : ℂ) + t * I)⁻¹) t := by
  have hpos : (0 : ℝ) < c ^ 2 + t ^ 2 := by positivity
  have harctan : HasDerivAt (fun u : ℝ => Real.arctan (u / c)) (c / (c ^ 2 + t ^ 2)) t := by
    have h := ((hasDerivAt_id t).div_const c).arctan
    simp only [id_eq] at h
    convert h using 1
    field_simp
  have hlog : HasDerivAt (fun u : ℝ => Real.log (c ^ 2 + u ^ 2)) (2 * t / (c ^ 2 + t ^ 2)) t := by
    have hsq : HasDerivAt (fun u : ℝ => c ^ 2 + u ^ 2) (2 * t) t :=
      ((hasDerivAt_pow 2 t).const_add (c ^ 2)).congr_deriv (by norm_num)
    exact hsq.log hpos.ne'
  have h := harctan.ofReal_comp.sub (hlog.ofReal_comp.const_mul (I / 2))
  refine h.congr_deriv ?_
  have hposC : ((c : ℂ) ^ 2 + (t : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by exact_mod_cast hpos.ne' : ((c ^ 2 + t ^ 2 : ℝ) : ℂ) ≠ 0)
  refine eq_inv_of_mul_eq_one_left ?_
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `t ↦ (c + it)⁻¹` is continuous for `c ≠ 0`. -/
theorem barnesRes_continuous_recip {c : ℝ} (hc : c ≠ 0) :
    Continuous fun t : ℝ => ((c : ℂ) + t * I)⁻¹ :=
  Continuous.inv₀ (by fun_prop) fun t h => hc (by simpa using congrArg re h)

/-- `∫_{-T}^{T} (c + it)⁻¹ dt = 2 arctan (T / c)` for `c ≠ 0`. -/
theorem barnesRes_integral_recip {c : ℝ} (hc : c ≠ 0) (T : ℝ) :
    ∫ t in -T..T, ((c : ℂ) + t * I)⁻¹ = 2 * (Real.arctan (T / c) : ℂ) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => barnesRes_hasDerivAt_primitive hc u)
    ((barnesRes_continuous_recip hc).intervalIntegrable _ _), neg_div, Real.arctan_neg, neg_sq]
  push_cast; ring

/-- `∫_{-T}^{T} (c + it)⁻¹ dt → π sign c` as `T → ∞`. -/
theorem barnesRes_tendsto_integral_recip {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun T : ℝ => ∫ t in -T..T, ((c : ℂ) + t * I)⁻¹) atTop
      (𝓝 (if 0 < c then (π : ℂ) else -π)) := by
  simp_rw [barnesRes_integral_recip hc]
  have key : Tendsto (fun T : ℝ => Real.arctan (T / c)) atTop
      (𝓝 (if 0 < c then π / 2 else -(π / 2))) := by
    split_ifs with h
    · exact (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
        (tendsto_id.atTop_div_const h)
    · have hneg : c < 0 := lt_of_le_of_ne (not_lt.mp h) hc
      exact (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp
        (tendsto_id.atTop_div_const_of_neg hneg)
  have := ((continuous_ofReal.tendsto _).comp key).const_mul (2 : ℂ)
  have hv : (if 0 < c then (π : ℂ) else -π) =
      2 * ((if 0 < c then π / 2 else -(π / 2) : ℝ) : ℂ) := by
    split_ifs <;> push_cast <;> ring
  rw [hv]
  exact this

/-- The bound `‖∫_{c₁}^{c₂} (x + iy - p)⁻¹ dx‖ ≤ (c₂ - c₁) / |y - Im p|`. -/
theorem barnesRes_norm_horizontal_recip_le {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) (p : ℂ) {y : ℝ}
    (hy : y ≠ p.im) :
    ‖∫ x in c₁..c₂, ((x : ℂ) + y * I - p)⁻¹‖ ≤ (c₂ - c₁) * |y - p.im|⁻¹ := by
  have hb : ∀ x : ℝ, ‖((x : ℂ) + y * I - p)⁻¹‖ ≤ |y - p.im|⁻¹ := by
    intro x
    rw [norm_inv]
    have hpos : 0 < |y - p.im| := abs_pos.mpr (sub_ne_zero.mpr hy)
    refine inv_anti₀ hpos ?_
    have := abs_im_le_norm ((x : ℂ) + y * I - p)
    simpa using this
  calc ‖∫ x in c₁..c₂, ((x : ℂ) + y * I - p)⁻¹‖ ≤ |y - p.im|⁻¹ * |c₂ - c₁| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hb x)
    _ = (c₂ - c₁) * |y - p.im|⁻¹ := by
        rw [abs_of_nonneg (sub_nonneg.mpr h : (0:ℝ) ≤ c₂ - c₁)]; ring

/-- **Shifting a vertical line of integration past a simple pole.** Let `φ` be holomorphic on the
closed strip `c₁ ≤ Re s ≤ c₂`, `c₁ < Re p < c₂`, and `f s = φ s / (s - p)`. If `f` is integrable
on both boundary lines and its integrals over horizontal cross-sections tend to `0` at `±i∞`, then
`∫ f(c₂+iy) dy - ∫ f(c₁+iy) dy = 2π φ(p)`. -/
theorem barnesRes_vertical_shift {φ : ℂ → ℂ} {c₁ c₂ : ℝ} {p : ℂ} (h₁ : c₁ < p.re)
    (h₂ : p.re < c₂) (hφ : DifferentiableOn ℂ φ (re ⁻¹' Icc c₁ c₂))
    (hi₁ : Integrable fun y : ℝ => φ (c₁ + y * I) / (c₁ + y * I - p))
    (hi₂ : Integrable fun y : ℝ => φ (c₂ + y * I) / (c₂ + y * I - p))
    (htop : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, φ (x + T * I) / (x + T * I - p)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, φ (x + T * I) / (x + T * I - p)) atBot (𝓝 0)) :
    (∫ y : ℝ, φ (c₂ + y * I) / (c₂ + y * I - p)) - ∫ y : ℝ, φ (c₁ + y * I) / (c₁ + y * I - p) =
      2 * π * φ p := by
  set S : Set ℂ := re ⁻¹' Icc c₁ c₂ with hS
  set f : ℂ → ℂ := fun s => φ s / (s - p) with hf
  set g : ℂ → ℂ := dslope φ p with hg
  set β : ℝ := p.im with hβ
  have hc : c₁ ≤ c₂ := by linarith
  have hSp : S ∈ 𝓝 p := by
    have : re ⁻¹' Ioo c₁ c₂ ⊆ S := preimage_mono Ioo_subset_Icc_self
    exact Filter.mem_of_superset ((isOpen_Ioo.preimage continuous_re).mem_nhds ⟨h₁, h₂⟩) this
  have hgd : DifferentiableOn ℂ g S := (differentiableOn_dslope hSp).mpr hφ
  have hgc : ContinuousOn g S := hgd.continuousOn
  -- decomposition off the pole
  have hdec : ∀ s : ℂ, s ≠ p → f s = φ p * (s - p)⁻¹ + g s := by
    intro s hs
    have h := sub_smul_dslope φ p s
    rw [smul_eq_mul] at h
    have hs' : s - p ≠ 0 := sub_ne_zero.mpr hs
    have h2 : φ s = φ p + (s - p) * g s := by rw [hg]; linear_combination -h
    simp only [hf]
    rw [h2]
    field_simp
  -- continuity of `g` along the four sides
  have hgh' : ∀ y : ℝ, IntervalIntegrable (fun x : ℝ => g (x + y * I)) volume c₁ c₂ := by
    intro y
    refine ContinuousOn.intervalIntegrable (hgc.comp
      (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + y * I).continuousOn fun x hx => ?_)
    rw [uIcc_of_le hc] at hx
    simpa [hS] using hx
  have hgv : ∀ c : ℝ, c ∈ Icc c₁ c₂ → Continuous fun y : ℝ => g (c + y * I) := by
    intro c hcI
    exact hgc.comp_continuous (by fun_prop) fun y => by simpa [hS] using hcI
  -- the identity at height `T`
  have hTid : ∀ T : ℝ, 0 < T →
      I * ((∫ y in β - T..β + T, f (c₂ + y * I)) - ∫ y in β - T..β + T, f (c₁ + y * I)) =
        φ p * ((∫ x in c₁..c₂, ((x : ℂ) + (β - T : ℝ) * I - p)⁻¹) -
            (∫ x in c₁..c₂, ((x : ℂ) + (β + T : ℝ) * I - p)⁻¹) +
            I * ((∫ y in β - T..β + T, ((c₂ : ℂ) + y * I - p)⁻¹) -
              ∫ y in β - T..β + T, ((c₁ : ℂ) + y * I - p)⁻¹)) -
          ((∫ x in c₁..c₂, f (x + (β - T : ℝ) * I)) - ∫ x in c₁..c₂, f (x + (β + T : ℝ) * I)) := by
    intro T hT0
    have hrect := integral_boundary_rect_eq_zero_of_differentiableOn g
      ((c₁ : ℂ) + (β - T : ℝ) * I) ((c₂ : ℂ) + (β + T : ℝ) * I) (by
        refine hgd.mono fun s hs => ?_
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero] at hs
        simpa [hS, uIcc_of_le hc] using hs.1)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, smul_eq_mul] at hrect
    -- pointwise decompositions on the four sides
    have hne_h : ∀ (x : ℝ) (y : ℝ), y ≠ β → (x : ℂ) + y * I ≠ p := by
      intro x y hy h; apply hy; have := congrArg im h; simpa [hβ] using this
    have hne_v : ∀ (c : ℝ) (y : ℝ), c ≠ p.re → (c : ℂ) + y * I ≠ p := by
      intro c y hc' h; apply hc'; have := congrArg re h; simpa using this
    have hinvh : ∀ y : ℝ, y ≠ β → Continuous fun x : ℝ => ((x : ℂ) + y * I - p)⁻¹ :=
      fun y hy => Continuous.inv₀ (by fun_prop) fun x => sub_ne_zero.mpr (hne_h x y hy)
    have hinvv : ∀ c : ℝ, c ≠ p.re → Continuous fun y : ℝ => ((c : ℂ) + y * I - p)⁻¹ :=
      fun c hc' => Continuous.inv₀ (by fun_prop) fun y => sub_ne_zero.mpr (hne_v c y hc')
    have hyb1 : β - T ≠ β := by linarith
    have hyb2 : β + T ≠ β := by linarith
    have hH : ∀ y : ℝ, y ≠ β → ∫ x in c₁..c₂, f (x + y * I) =
        φ p * (∫ x in c₁..c₂, ((x : ℂ) + y * I - p)⁻¹) + ∫ x in c₁..c₂, g (x + y * I) := by
      intro y hy
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        (((hinvh y hy).intervalIntegrable _ _).const_mul _) (hgh' y)]
      exact intervalIntegral.integral_congr fun x _ => hdec _ (hne_h x y hy)
    have hV : ∀ c : ℝ, c ∈ Icc c₁ c₂ → c ≠ p.re → ∫ y in β - T..β + T, f (c + y * I) =
        φ p * (∫ y in β - T..β + T, ((c : ℂ) + y * I - p)⁻¹) +
          ∫ y in β - T..β + T, g (c + y * I) := by
      intro c hcI hc'
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        (((hinvv c hc').intervalIntegrable _ _).const_mul _)
        ((hgv c hcI).intervalIntegrable _ _)]
      exact intervalIntegral.integral_congr fun y _ => hdec _ (hne_v c y hc')
    rw [hH _ hyb1, hH _ hyb2, hV c₂ ⟨hc, le_rfl⟩ h₂.ne', hV c₁ ⟨le_rfl, hc⟩ h₁.ne]
    linear_combination hrect
  -- limits
  have hTt : Tendsto (fun T : ℝ => β - T) atTop atBot := tendsto_atBot_add_const_left _ _
    (tendsto_neg_atTop_atBot)
  have hTt' : Tendsto (fun T : ℝ => β + T) atTop atTop := tendsto_atTop_add_const_left _ _
    tendsto_id
  have hvert : ∀ c : ℝ, Integrable (fun y : ℝ => f (c + y * I)) →
      Tendsto (fun T : ℝ => ∫ y in β - T..β + T, f (c + y * I)) atTop
        (𝓝 (∫ y : ℝ, f (c + y * I))) :=
    fun c hi => intervalIntegral_tendsto_integral hi hTt hTt'
  have hLHS := ((hvert c₂ hi₂).sub (hvert c₁ hi₁)).const_mul I
  -- the reciprocal-kernel rectangle integral
  have hshift : ∀ (c : ℝ) (T : ℝ), ∫ y in β - T..β + T, ((c : ℂ) + y * I - p)⁻¹ =
      ∫ t in -T..T, (((c - p.re : ℝ) : ℂ) + t * I)⁻¹ := by
    intro c T
    have := intervalIntegral.integral_comp_add_right
      (fun y : ℝ => ((c : ℂ) + y * I - p)⁻¹) β (a := -T) (b := T)
    rw [show -T + β = β - T by ring, show T + β = β + T by ring] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun t _ => ?_
    congr 1
    apply Complex.ext <;> simp [hβ]
  have hinv2 := barnesRes_tendsto_integral_recip (c := c₂ - p.re) (by linarith)
  have hinv1 := barnesRes_tendsto_integral_recip (c := c₁ - p.re) (by linarith)
  simp only [show (0:ℝ) < c₂ - p.re by linarith, ↓reduceIte] at hinv2
  simp only [show ¬ (0:ℝ) < c₁ - p.re by linarith, ↓reduceIte] at hinv1
  have hhinv : ∀ (s : ℝ → ℝ), Tendsto s atTop (atBot ⊔ atTop) → (∀ᶠ T in atTop, s T ≠ β) →
      Tendsto (fun T : ℝ => |s T - β|⁻¹) atTop (𝓝 0) → Tendsto (fun T : ℝ =>
        ∫ x in c₁..c₂, ((x : ℂ) + (s T : ℝ) * I - p)⁻¹) atTop (𝓝 0) := by
    intro s _ hs hlim
    refine squeeze_zero_norm' ?_ (by simpa using hlim.const_mul (c₂ - c₁))
    filter_upwards [hs] with T hT
    exact barnesRes_norm_horizontal_recip_le hc p hT
  have hb1 : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, ((x : ℂ) + (β - T : ℝ) * I - p)⁻¹) atTop
      (𝓝 0) := by
    refine hhinv (fun T => β - T) (hTt.mono_right le_sup_left) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with T hT; linarith
    · have : (fun T : ℝ => |β - T - β|⁻¹) =ᶠ[atTop] fun T => T⁻¹ := by
        filter_upwards [eventually_gt_atTop 0] with T hT
        rw [show β - T - β = -T by ring, abs_neg, abs_of_pos hT]
      exact (tendsto_inv_atTop_zero).congr' this.symm
  have hb2 : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, ((x : ℂ) + (β + T : ℝ) * I - p)⁻¹) atTop
      (𝓝 0) := by
    refine hhinv (fun T => β + T) (hTt'.mono_right le_sup_right) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with T hT; linarith
    · have : (fun T : ℝ => |β + T - β|⁻¹) =ᶠ[atTop] fun T => T⁻¹ := by
        filter_upwards [eventually_gt_atTop 0] with T hT
        rw [show β + T - β = T by ring, abs_of_pos hT]
      exact (tendsto_inv_atTop_zero).congr' this.symm
  have hRHS := ((((hb1.sub hb2).add (((hinv2.congr fun T => (hshift c₂ T).symm).sub
      (hinv1.congr fun T => (hshift c₁ T).symm)).const_mul I)).const_mul (φ p)).sub
      ((hbot.comp hTt).sub (htop.comp hTt')))
  have hRHS' := hRHS.congr' (by
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact (hTid T hT).symm)
  have huniq := tendsto_nhds_unique hLHS hRHS'
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have : I * ((∫ y : ℝ, f (c₂ + y * I)) - ∫ y : ℝ, f (c₁ + y * I)) = I * (2 * π * φ p) := by
    rw [huniq]; ring
  exact mul_left_cancel₀ hI this

/-- **Shifting a vertical line of integration with no pole in between.** -/
theorem barnesRes_vertical_shift_of_differentiableOn {f : ℂ → ℂ} {c₁ c₂ : ℝ} (h : c₁ < c₂)
    (hf : DifferentiableOn ℂ f (re ⁻¹' Icc c₁ c₂))
    (hi₁ : Integrable fun y : ℝ => f (c₁ + y * I))
    (hi₂ : Integrable fun y : ℝ => f (c₂ + y * I))
    (htop : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, f (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, f (x + T * I)) atBot (𝓝 0)) :
    (∫ y : ℝ, f (c₂ + y * I)) = ∫ y : ℝ, f (c₁ + y * I) := by
  set p : ℂ := (((c₁ + c₂) / 2 : ℝ) : ℂ)
  have hpre : p.re = (c₁ + c₂) / 2 := by simp [p]
  have hpim : p.im = 0 := by simp [p]
  set Φ : ℂ → ℂ := fun s => (s - p) * f s
  have hdiv : ∀ s : ℂ, s ≠ p → Φ s / (s - p) = f s := fun s hs => by
    simp only [Φ]; field_simp [sub_ne_zero.mpr hs]
  have hv : ∀ c : ℝ, c ≠ (c₁ + c₂) / 2 → (fun y : ℝ => Φ (c + y * I) / (c + y * I - p)) =
      fun y : ℝ => f (c + y * I) := fun c hc => funext fun y => hdiv _ (fun he => hc (by
        have := congrArg re he; simpa [hpre] using this))
  have hne1 : c₁ ≠ (c₁ + c₂) / 2 := by intro h'; linarith
  have hne2 : c₂ ≠ (c₁ + c₂) / 2 := by intro h'; linarith
  have hH : ∀ T : ℝ, T ≠ 0 → (∫ x in c₁..c₂, Φ (x + T * I) / (x + T * I - p)) =
      ∫ x in c₁..c₂, f (x + T * I) := fun T hT => intervalIntegral.integral_congr fun x _ =>
    hdiv _ (fun he => hT (by have := congrArg im he; simpa [hpim] using this))
  have key := barnesRes_vertical_shift (φ := Φ) (p := p) (by rw [hpre]; linarith)
    (by rw [hpre]; linarith) ((differentiableOn_id.sub_const p).mul hf)
    (by rw [hv c₁ hne1]; exact hi₁) (by rw [hv c₂ hne2]; exact hi₂)
    (htop.congr' (by filter_upwards [eventually_gt_atTop 0] with T hT; exact (hH T hT.ne').symm))
    (hbot.congr' (by filter_upwards [eventually_lt_atBot 0] with T hT; exact (hH T hT.ne).symm))
  rw [hv c₁ hne1, hv c₂ hne2] at key
  simp only [Φ, sub_self, zero_mul, mul_zero] at key
  exact sub_eq_zero.mp key

/-- `‖sin (x + iy)‖² = sin² x + sinh² y`. -/
theorem barnesRes_sq_norm_sin (x y : ℝ) :
    ‖Complex.sin (x + y * I)‖ ^ 2 = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  have h : Complex.sin (x + y * I) = ((Real.sin x * Real.cosh y : ℝ) : ℂ) +
      ((Real.cos x * Real.sinh y : ℝ) : ℂ) * I := by
    rw [Complex.sin_add_mul_I]; push_cast; rfl
  rw [h, norm_add_mul_I, Real.sq_sqrt (by positivity)]
  have := Real.cosh_sq y
  have := Real.sin_sq_add_cos_sq x
  nlinarith [this]

/-- `|sinh y| ≤ ‖sin (x + iy)‖`. -/
theorem barnesRes_abs_sinh_le_norm_sin (x y : ℝ) : |Real.sinh y| ≤ ‖Complex.sin (x + y * I)‖ := by
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs, barnesRes_sq_norm_sin]
  nlinarith [sq_nonneg (Real.sin x)]

/-- `|sin x| cosh y ≤ ‖sin (x + iy)‖`. -/
theorem barnesRes_abs_sin_mul_cosh_le_norm_sin (x y : ℝ) :
    |Real.sin x| * Real.cosh y ≤ ‖Complex.sin (x + y * I)‖ := by
  rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), mul_pow, sq_abs, barnesRes_sq_norm_sin,
    Real.cosh_sq]
  have h1 : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  nlinarith [sq_nonneg (Real.sinh y), sq_nonneg (Real.sin x)]

/-- `Γ(w + n + 1) = Γ(w) ∏_{j ≤ n} (w + j)` when `w + j ≠ 0` for `j ≤ n`. -/
theorem barnesRes_Gamma_add_nat_succ (w : ℂ) (n : ℕ) (h : ∀ j : ℕ, j ≤ n → w + j ≠ 0) :
    Gamma (w + n + 1) = Gamma w * ∏ j ∈ Finset.range (n + 1), (w + j) := by
  induction n with
  | zero =>
    have := h 0 le_rfl
    simp only [Nat.cast_zero, add_zero] at this ⊢
    rw [Gamma_add_one w this]; simp; ring
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih (fun j hj => h j (by omega))]
    have := h (n + 1) le_rfl
    push_cast at this ⊢
    rw [show w + (n + 1) + 1 = (w + n + 1) + 1 by ring, Gamma_add_one _ (by
      rw [show w + n + 1 = w + (n + 1) by ring]; exact this)]
    ring

/-- The set `{a | a ≠ b - n for all n : ℕ}` is open. -/
theorem barnesRes_isOpen_ne_sub_nat (b : ℂ) : IsOpen {a : ℂ | ∀ n : ℕ, a ≠ b - n} := by
  have hc : IsClosed (range (fun n : ℕ => b - n)) := by
    have h1 : IsClosed (range ((↑) : ℕ → ℝ)) := Nat.isClosedEmbedding_coe_real.isClosed_range
    have h2 : IsClosed (((↑) : ℝ → ℂ) '' range ((↑) : ℕ → ℝ)) :=
      Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ h1
    have h3 : IsClosed ((fun a : ℂ => b - a) ⁻¹' (((↑) : ℝ → ℂ) '' range ((↑) : ℕ → ℝ))) :=
      h2.preimage (by fun_prop)
    convert h3 using 1
    ext a
    simp only [mem_range, mem_preimage, mem_image, exists_exists_eq_and]
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨n, by push_cast; ring⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by push_cast at hn; linear_combination -hn⟩
  convert hc.isOpen_compl using 1
  ext a; simp [eq_comm]

/-- The set `{a | a ≠ b - n for all n : ℕ}` is preconnected. -/
theorem barnesRes_isPreconnected_ne_sub_nat (b : ℂ) :
    IsPreconnected {a : ℂ | ∀ n : ℕ, a ≠ b - n} := by
  have hs : (range (fun n : ℕ => b - n)).Countable := countable_range _
  have := (hs.isPathConnected_compl_of_one_lt_rank (by
    rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  convert this using 1
  ext a; simp [eq_comm]

/-- `‖Γ(w)‖ ‖sin(πw)‖ ≤ π ‖Γ(1-w)⁻¹‖` (reflection formula, all `w`). -/
theorem barnesRes_norm_Gamma_mul_sin_le (w : ℂ) :
    ‖Gamma w‖ * ‖Complex.sin (π*w)‖ ≤ π * ‖(Gamma (1-w))⁻¹‖ := by
  have hr := Complex.Gamma_mul_Gamma_one_sub w
  by_cases hs : Complex.sin (π*w) = 0
  · rw [hs, norm_zero, mul_zero]; positivity
  by_cases hg : Gamma (1-w) = 0
  · rw [hg, mul_zero] at hr
    exact absurd (div_eq_zero_iff.mp hr.symm) (by
      push Not; exact ⟨ofReal_ne_zero.mpr Real.pi_ne_zero, hs⟩)
  have : Gamma w * Complex.sin (π*w) = π * (Gamma (1-w))⁻¹ := by
    rw [eq_div_iff hs] at hr
    rw [eq_mul_inv_iff_mul_eq₀ hg]; linear_combination hr
  rw [← norm_mul, this, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- `‖sin(π(x+iy))‖ ≥ (|sin πx|/2) e^{π|y|}`. -/
theorem barnesRes_sin_lower_line (x y : ℝ) :
    |Real.sin (π*x)|/2 * Real.exp (π*|y|) ≤ ‖Complex.sin (π*((x:ℂ) + y*I))‖ := by
  have hw : (π:ℂ)*((x:ℂ) + y*I) = ((π*x:ℝ):ℂ) + ((π*y:ℝ):ℂ)*I := by push_cast; ring
  rw [hw]
  refine le_trans ?_ (barnesRes_abs_sin_mul_cosh_le_norm_sin (π*x) (π*y))
  have hcosh : Real.exp (π*|y|)/2 ≤ Real.cosh (π*y) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq]
    have := Real.exp_pos (-(π*|y|)); linarith
  have := abs_nonneg (Real.sin (π*x))
  nlinarith

/-- `‖sin(π(x+iy))‖ ≥ e^{π|y|}/4` for `|y| ≥ 1`. -/
theorem barnesRes_sin_lower_far (x : ℝ) {y : ℝ} (hy : 1 ≤ |y|) :
    1/4 * Real.exp (π*|y|) ≤ ‖Complex.sin (π*((x:ℂ) + y*I))‖ := by
  have hw : (π:ℂ)*((x:ℂ) + y*I) = ((π*x:ℝ):ℂ) + ((π*y:ℝ):ℂ)*I := by push_cast; ring
  rw [hw]
  refine le_trans ?_ (barnesRes_abs_sinh_le_norm_sin (π*x) (π*y))
  rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos, Real.sinh_eq]
  have h4 := Real.add_one_le_exp (π*|y|)
  have h5 : Real.exp (-(π*|y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  nlinarith [Real.two_le_pi]

/-- `sin(πs) ≠ 0` when `sin(π Re s) ≠ 0`. -/
theorem barnesRes_sin_ne_zero_of_re {s : ℂ} (h : Real.sin (π*s.re) ≠ 0) :
    Complex.sin (π*s) ≠ 0 := by
  intro h0
  have := barnesRes_sin_lower_line s.re s.im
  rw [show ((s.re:ℂ) + s.im*I) = s from re_add_im s, h0, norm_zero] at this
  have h1 : 0 < |Real.sin (π*s.re)|/2 * Real.exp (π*|s.im|) := by positivity
  linarith

/-- `sin(πx) ≠ 0` for real `x ≤ 0` that is not a non-positive integer. -/
theorem barnesRes_real_sin_ne_zero {x : ℝ} (hx0 : x ≤ 0) (hx : ∀ n : ℕ, x ≠ -n) :
    Real.sin (π*x) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  have hxn : x = n := by
    have := Real.pi_pos
    have h2 : ((n:ℝ) - x) * π = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · linarith
  have hn0 : n ≤ 0 := by
    have : (n:ℝ) ≤ 0 := hxn ▸ hx0
    exact_mod_cast this
  apply hx (-n).toNat
  rw [hxn]
  have : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
  have h4 : (((-n).toNat : ℕ) : ℝ) = -(n:ℝ) := by
    rw [← Int.cast_natCast, this, Int.cast_neg]
  rw [h4]; ring

/-- `∏_{j<n} (n - j) = n!`. -/
theorem barnesRes_prod_nat_sub (n : ℕ) : ∏ j ∈ Finset.range n, ((n:ℂ) - j) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ', Nat.factorial_succ]
    have : ∏ j ∈ Finset.range n, (((n+1 : ℕ) : ℂ) - ((j+1 : ℕ) : ℂ)) =
        ∏ j ∈ Finset.range n, ((n:ℂ) - j) :=
      Finset.prod_congr rfl fun j _ => by push_cast; ring
    rw [this, ih]; push_cast; ring

/-- `∏_{j<n} (j - n) = (-1)^n n!`, the residue factor of `Γ` at `-n`. -/
theorem barnesRes_prod_sub_nat (n : ℕ) :
    ∏ j ∈ Finset.range n, ((j:ℂ) - n) = (-1)^n * n.factorial := by
  calc ∏ j ∈ Finset.range n, ((j:ℂ) - n) = ∏ j ∈ Finset.range n, ((-1) * ((n:ℂ) - j)) :=
        Finset.prod_congr rfl fun j _ => by ring
    _ = (-1)^n * ∏ j ∈ Finset.range n, ((n:ℂ) - j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ = _ := by rw [barnesRes_prod_nat_sub]

/-- `(1+u)^K e^{-bu} → 0` as `u → ∞`. -/
theorem barnesRes_tendsto_poly_exp {b : ℝ} (hb : 0 < b) (K : ℕ) :
    Tendsto (fun u : ℝ => (1 + u) ^ K * Real.exp (-(b * u))) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp
    ((tendsto_id.const_mul_atTop hb).comp (tendsto_atTop_add_const_left _ 1 tendsto_id))).const_mul
    ((b ^ K)⁻¹ * Real.exp b)
  rw [mul_zero] at h
  refine h.congr fun u => ?_
  simp only [Function.comp_def, id]
  rw [mul_pow, show -(b * (1 + u)) = -b + -(b*u) by ring, Real.exp_add, Real.exp_neg b]
  have : b ^ K ≠ 0 := by positivity
  field_simp

end Complex
