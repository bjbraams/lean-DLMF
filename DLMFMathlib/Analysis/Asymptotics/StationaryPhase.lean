/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
public import DLMFMathlib.Analysis.Complex.RotateRay

/-!
# Stationary phase at a cubic stationary point

For a real phase `φ` on `[0, b]` with `φ(x) = c x³ + O(x⁴)` (`c > 0`), `φ'' ≥ 0` and
`φ'(x) ≥ m x²`, the oscillatory integral satisfies

`λ^{1/3} ∫₀^b e^{iλφ(x)} dx → Γ(4/3) c^{-1/3} e^{iπ/6}`   (`λ → +∞`).

The proof splits `[0, b]` at `δ = λ^{-3/10}`. On `[δ, b]` one integration by parts
(`statPh_norm_integral_le`, the first-derivative test) gives `O(λ^{-1/15})` after scaling; on
`[0, δ]` the phase is replaced by `c x³` at cost `O(λ^{-1/6})`, and the model integral is
rescaled to `∫₀^R e^{it³} dt`. Its limit `Γ(4/3) e^{iπ/6}` (`statPh_tendsto_integral_exp_cube`)
is obtained by rotating the ray `arg t = α`, `0 < α < π/9`, to `arg t = π/6`
(`Complex.integral_Ioi_eq_exp_mul_integral_Ioi_rotate`) and letting `α → 0` with a uniform
tail bound `4/(3R²)`.

This is the leading term of the classical stationary-phase method at a degenerate stationary
point (Olver, *Asymptotics and Special Functions*, Ch. 3, §13; Temme, *Special Functions*,
§2.5); it is used for the Anger–Weber functions `𝐉_ν(ν)`, `𝐄_ν(ν)` (DLMF 11.11.18–19).

## Main results

* `Complex.statPh_norm_integral_le`: `‖∫_a^b ψ φ' e^{iφ}‖ ≤ 2ψ(a)` for nonincreasing `ψ ≥ 0`.
* `Complex.statPh_tendsto_integral_exp_cube`: `∫₀^R e^{it³} dt → Γ(4/3) e^{iπ/6}`.
* `Complex.statPh_tendsto_cubic`: the stationary-phase limit above.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

open scoped Topology Interval Real

namespace Complex

/-- **First-derivative bound for oscillatory integrals.** If `ψ` is nonincreasing (`ψ' ≤ 0`,
continuous) on `[a, b]` with `ψ(b) ≥ 0`, then `‖∫_a^b ψ φ' e^{iφ}‖ ≤ 2 ψ(a)` for any real
`C¹` phase `φ`. -/
theorem statPh_norm_integral_le {a b : ℝ} (hab : a ≤ b) {φ φ' ψ ψ' : ℝ → ℝ}
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x) (hψ : ∀ x ∈ Icc a b, HasDerivAt ψ (ψ' x) x)
    (hφ'c : ContinuousOn φ' (Icc a b)) (hψ'c : ContinuousOn ψ' (Icc a b))
    (hψ' : ∀ x ∈ Icc a b, ψ' x ≤ 0) (hψb : 0 ≤ ψ b) :
    ‖∫ x in a..b, ((ψ x * φ' x : ℝ) : ℂ) * exp (φ x * I)‖ ≤ 2 * ψ a := by
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  have hu : ∀ x ∈ [[a, b]], HasDerivAt (fun x => (ψ x : ℂ)) (ψ' x : ℂ) x := fun x hx =>
    (hψ x (hI ▸ hx)).ofReal_comp
  have hv : ∀ x ∈ [[a, b]], HasDerivAt (fun x => -I * exp (φ x * I))
      ((φ' x : ℂ) * exp (φ x * I)) x := by
    intro x hx
    have h1 := (((hφ x (hI ▸ hx)).ofReal_comp).mul_const I).cexp.const_mul (-I)
    convert h1 using 1
    ring_nf; rw [I_sq]; ring
  have hφc : ContinuousOn φ (Icc a b) := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hψc : ContinuousOn ψ (Icc a b) := fun x hx => (hψ x hx).continuousAt.continuousWithinAt
  have hu'i : IntervalIntegrable (fun x => (ψ' x : ℂ)) volume a b :=
    (continuous_ofReal.comp_continuousOn (hI ▸ hψ'c)).intervalIntegrable
  have hv'i : IntervalIntegrable (fun x => (φ' x : ℂ) * exp (φ x * I)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hI]
    exact (continuous_ofReal.comp_continuousOn hφ'c).mul
      ((continuous_ofReal.comp_continuousOn hφc).mul continuousOn_const).cexp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'i hv'i
  have heq : ∫ x in a..b, ((ψ x * φ' x : ℝ) : ℂ) * exp (φ x * I) =
      ∫ x in a..b, (ψ x : ℂ) * ((φ' x : ℂ) * exp (φ x * I)) :=
    intervalIntegral.integral_congr fun x _ => by push_cast; ring
  rw [heq, hibp]
  -- FTC for ψ
  have hftc : ∫ x in a..b, ψ' x = ψ b - ψ a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hψ x (hI ▸ hx))
      (hψ'c.intervalIntegrable_of_Icc hab)
  have hab' : ψ b ≤ ψ a := by
    have : ∫ x in a..b, ψ' x ≤ 0 := by
      have := intervalIntegral.integral_nonneg (μ := volume) (f := fun x => -ψ' x) hab
        fun x hx => neg_nonneg.2 (hψ' x hx)
      rw [intervalIntegral.integral_neg] at this; linarith
    linarith
  have hnv : ∀ x, ‖-I * exp (φ x * I)‖ = 1 := fun x => by
    rw [norm_mul, norm_neg, norm_I, one_mul, norm_exp_ofReal_mul_I]
  have hint : ‖∫ x in a..b, (ψ' x : ℂ) * (-I * exp (φ x * I))‖ ≤ ψ a - ψ b := by
    have := intervalIntegral.norm_integral_le_of_norm_le (f := fun x =>
        (ψ' x : ℂ) * (-I * exp (φ x * I))) (g := fun x => -ψ' x) hab
      (Eventually.of_forall fun x hx => by
        rw [norm_mul, hnv, mul_one, norm_real, Real.norm_eq_abs,
          abs_of_nonpos (hψ' x (Ioc_subset_Icc_self hx))])
      ((hψ'c.intervalIntegrable_of_Icc (μ := volume) hab).neg)
    rw [intervalIntegral.integral_neg, hftc] at this
    linarith
  calc ‖(ψ b : ℂ) * (-I * exp (φ b * I)) - (ψ a : ℂ) * (-I * exp (φ a * I)) -
        ∫ x in a..b, (ψ' x : ℂ) * (-I * exp (φ x * I))‖
      ≤ ‖(ψ b : ℂ) * (-I * exp (φ b * I))‖ + ‖(ψ a : ℂ) * (-I * exp (φ a * I))‖ +
          ‖∫ x in a..b, (ψ' x : ℂ) * (-I * exp (φ x * I))‖ := by
          refine (norm_sub_le _ _).trans ?_; gcongr; exact norm_sub_le _ _
    _ ≤ ψ b + ψ a + (ψ a - ψ b) := by
        rw [norm_mul (ψ b : ℂ), norm_mul (ψ a : ℂ), hnv, hnv, mul_one, mul_one, norm_real, norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hψb,
          abs_of_nonneg (hψb.trans hab')]
        linarith
    _ = 2 * ψ a := by ring


/-- Tail bound for a damped cubic phase: `‖∫_R^S e^{-s r³ + i c r³} dr‖ ≤ 2/(3 c R²)`. -/
theorem statPh_norm_integral_damped_cube {s c R S : ℝ} (hs : 0 ≤ s) (hc : 0 < c) (hR : 0 < R)
    (hRS : R ≤ S) :
    ‖∫ r in R..S, exp ((-(s * r ^ 3) : ℝ) + ((c * r ^ 3 : ℝ) : ℂ) * I)‖ ≤ 2 / (3 * c * R ^ 2) := by
  set ψ : ℝ → ℝ := fun r => Real.exp (-(s * r ^ 3)) / (3 * c * r ^ 2) with hψd
  set ψ' : ℝ → ℝ := fun r => (-(s * (3 * r ^ 2)) * Real.exp (-(s * r ^ 3)) * (3 * c * r ^ 2) -
      Real.exp (-(s * r ^ 3)) * (3 * c * (2 * r))) / (3 * c * r ^ 2) ^ 2 with hψ'd
  have hpos : ∀ x ∈ Icc R S, 0 < x := fun x hx => hR.trans_le hx.1
  have hden : ∀ x ∈ Icc R S, 3 * c * x ^ 2 ≠ 0 := fun x hx => by
    have := hpos x hx; positivity
  have hψ : ∀ x ∈ Icc R S, HasDerivAt ψ (ψ' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun r : ℝ => Real.exp (-(s * r ^ 3)))
        (-(s * (3 * x ^ 2)) * Real.exp (-(s * x ^ 3))) x := by
      have h0 : HasDerivAt (fun r : ℝ => -(s * r ^ 3)) (-(s * (3 * x ^ 2))) x := by
        have := ((hasDerivAt_pow 3 x).const_mul s).neg
        convert this using 1
      convert h0.exp using 1; ring
    have h2 : HasDerivAt (fun r : ℝ => 3 * c * r ^ 2) (3 * c * (2 * x)) x := by
      have := (hasDerivAt_pow 2 x).const_mul (3 * c)
      convert this using 1; push_cast; ring
    exact h1.div h2 (hden x hx)
  have hφ : ∀ x ∈ Icc R S, HasDerivAt (fun r : ℝ => c * r ^ 3) (3 * c * x ^ 2) x := by
    intro x _
    have := (hasDerivAt_pow 3 x).const_mul c
    convert this using 1; push_cast; ring
  have hb := statPh_norm_integral_le hRS hφ hψ (by fun_prop)
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => pow_ne_zero 2 (hden x hx))
    (fun x hx => by
      have := hpos x hx
      refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
      have he := Real.exp_pos (-(s * x ^ 3))
      have : 0 ≤ s * (3 * x ^ 2) * Real.exp (-(s * x ^ 3)) * (3 * c * x ^ 2) := by positivity
      have : 0 ≤ Real.exp (-(s * x ^ 3)) * (3 * c * (2 * x)) := by positivity
      linarith)
    (by have := hpos S ⟨hRS, le_rfl⟩; positivity)
  have heq : ∫ r in R..S, exp ((-(s * r ^ 3) : ℝ) + ((c * r ^ 3 : ℝ) : ℂ) * I) =
      ∫ x in R..S, ((ψ x * (3 * c * x ^ 2) : ℝ) : ℂ) * exp (((c * x ^ 3 : ℝ) : ℂ) * I) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hRS] at hx
    have h0 := hden x hx
    simp only [hψd]
    rw [div_mul_cancel₀ _ h0, ofReal_exp, ← exp_add]
  rw [heq]
  refine hb.trans ?_
  simp only [hψd]
  have : 0 < 3 * c * R ^ 2 := by positivity
  rw [mul_div_assoc']
  gcongr
  have : Real.exp (-(s * R ^ 3)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  linarith

/-- `|exp(i (r e^{iθ})³)| = e^{-r³ sin 3θ}`. -/
theorem statPh_norm_exp_cube_ray (r θ : ℝ) :
    ‖exp (((r : ℂ) * exp (θ * I)) ^ 3 * I)‖ = Real.exp (-(r ^ 3 * Real.sin (3 * θ))) := by
  rw [norm_exp]
  congr 1
  have : ((r : ℂ) * exp (θ * I)) ^ 3 = ((r ^ 3 : ℝ) : ℂ) * exp (((3 * θ : ℝ) : ℂ) * I) := by
    rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  rw [this, mul_re, re_ofReal_mul, im_ofReal_mul, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im]
  simp

/-- The value of the cubic oscillatory integral along a ray `arg t = α`, `0 < α < π/6`:
`e^{iα} ∫₀^∞ exp(i (r e^{iα})³) dr = Γ(4/3) e^{iπ/6}`. -/
theorem statPh_integral_ray {α : ℝ} (hα0 : 0 < α) (hα : α < π / 6) :
    exp (α * I) * ∫ r in Ioi (0 : ℝ), exp (((r : ℂ) * exp (α * I)) ^ 3 * I) =
      (Real.Gamma (4 / 3) : ℂ) * exp ((π / 6 : ℝ) * I) := by
  set β := π / 6 - α with hβ
  have hκ : 0 < Real.sin (3 * α) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hrw : ∀ (r y : ℝ), (r : ℂ) * exp (y * I) * exp (α * I) = r * exp (((y + α : ℝ) : ℂ) * I) :=
    fun r y => by rw [mul_assoc, ← exp_add]; push_cast; ring_nf
  have hsin : ∀ y ∈ [[0, β]], Real.sin (3 * α) ≤ Real.sin (3 * (y + α)) := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · rw [← h, zero_add]
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (x := 3 * α) (y := 3 * (y + α))
      (by linarith [Real.pi_pos]) (by linarith [hy.2]) (by linarith)
    exact this.le
  have hrot := integral_Ioi_eq_exp_mul_integral_Ioi_rotate (f := fun w =>
      exp ((w * exp (α * I)) ^ 3 * I)) (α := β) (σ := 1) (κ := Real.sin (3 * α)) (C := 1)
    one_pos hκ (fun r _ y _ => by fun_prop)
    (fun r hr _ y hy => by
      simp only [hrw, statPh_norm_exp_cube_ray, sub_self, Real.rpow_zero, mul_one]
      rw [Real.exp_le_one_iff, neg_nonpos]
      have := hκ.trans_le (hsin y hy)
      positivity)
    (fun r hr y hy => by
      simp only [hrw, statPh_norm_exp_cube_ray, one_mul]
      rw [Real.exp_le_exp, neg_mul, neg_le_neg_iff]
      have h3 : r ≤ r ^ 3 := by nlinarith [mul_le_mul hr hr zero_le_one (by linarith)]
      have := hsin y hy
      nlinarith [mul_le_mul_of_nonneg_left h3 hκ.le,
        mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ r ^ 3)])
  rw [hrot]
  have hcube : ∀ r : ℝ, (((r : ℂ) * exp (β * I) * exp (α * I)) ^ 3 * I) = -((r ^ 3 : ℝ) : ℂ) := by
    intro r
    rw [hrw, show β + α = π / 6 by rw [hβ]; ring, mul_pow, ← exp_nat_mul]
    have : ((3 : ℕ) : ℂ) * (((π / 6 : ℝ) : ℂ) * I) = (π / 2 : ℝ) * I := by push_cast; ring
    rw [this, exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring_nf; rw [I_sq]; ring
  simp only [hcube]
  have hG : ∫ r in Ioi (0 : ℝ), exp (-((r ^ 3 : ℝ) : ℂ)) = (Real.Gamma (4 / 3) : ℂ) := by
    have h := _root_.integral_exp_neg_rpow (p := 3) (by norm_num)
    rw [show (1 : ℝ) / 3 + 1 = 4 / 3 by norm_num] at h
    rw [← h, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    rw [ofReal_exp, show (r : ℝ) ^ (3 : ℝ) = r ^ 3 by exact_mod_cast Real.rpow_natCast r 3]
    push_cast; rfl
  rw [hG, ← mul_assoc, ← exp_add, mul_comm]
  congr 2
  rw [hβ]; push_cast; ring


/-- The improper integral `∫₀^∞ e^{i t³} dt = Γ(4/3) e^{iπ/6}`, with the explicit rate
`‖∫₀^R e^{it³} dt - Γ(4/3) e^{iπ/6}‖ ≤ 4/(3R²)`. -/
theorem statPh_norm_integral_exp_cube_sub_le {R : ℝ} (hR : 0 < R) :
    ‖(∫ t in (0 : ℝ)..R, exp ((t : ℂ) ^ 3 * I)) -
      (Real.Gamma (4 / 3) : ℂ) * exp ((π / 6 : ℝ) * I)‖ ≤ 4 / (3 * R ^ 2) := by
  set L : ℂ := (Real.Gamma (4 / 3) : ℂ) * exp ((π / 6 : ℝ) * I)
  set F : ℝ → ℂ := fun α => exp (α * I) * ∫ r in (0 : ℝ)..R, exp (((r : ℂ) * exp (α * I)) ^ 3 * I)
  have hFc : Continuous F := by
    refine (by fun_prop : Continuous fun α : ℝ => exp (α * I)).mul ?_
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (α r : ℝ) => exp (((r : ℂ) * exp (α * I)) ^ 3 * I)) (by fun_prop) 0 R
  have hF0 : F 0 = ∫ t in (0 : ℝ)..R, exp ((t : ℂ) ^ 3 * I) := by simp [F]
  have hπ9 : 0 < π / 9 := by positivity
  have hbound : ∀ α ∈ Ioo 0 (π / 9), ‖F α - L‖ ≤ 4 / (3 * R ^ 2) := by
    intro α hα
    obtain ⟨hα0, hα9⟩ := hα
    set s := Real.sin (3 * α)
    set c := Real.cos (3 * α)
    have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hc : 1 / 2 < c := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (x := 3 * α) (y := π / 3)
        (by linarith) (by linarith [Real.pi_pos]) (by linarith)
      rwa [Real.cos_pi_div_three] at this
    set g : ℝ → ℂ := fun r => exp (((r : ℂ) * exp (α * I)) ^ 3 * I)
    have hg : ∀ r : ℝ, g r = exp ((-(s * r ^ 3) : ℝ) + ((c * r ^ 3 : ℝ) : ℂ) * I) := by
      intro r
      simp only [g]
      congr 1
      have : ((r : ℂ) * exp (α * I)) ^ 3 = ((r ^ 3 : ℝ) : ℂ) * exp (((3 * α : ℝ) : ℂ) * I) := by
        rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf
      rw [this, exp_ofReal_mul_I]
      simp only [ofReal_neg, ofReal_mul, ofReal_pow]
      linear_combination ((r : ℂ) ^ 3 * (s : ℂ)) * I_sq
    have hgi : IntegrableOn g (Ioi 0) := by
      refine integrableOn_ray_of_bounds (f := fun w => exp (w ^ 3 * I)) (σ := 1) (C := 1)
        one_pos hs (fun r _ => by fun_prop) (fun r hr _ => ?_) (fun r hr => ?_)
      · rw [statPh_norm_exp_cube_ray, sub_self, Real.rpow_zero, mul_one, Real.exp_le_one_iff,
          neg_nonpos]
        positivity
      · rw [statPh_norm_exp_cube_ray, one_mul, Real.exp_le_exp, neg_mul, neg_le_neg_iff]
        have h3 : r ≤ r ^ 3 := by nlinarith [mul_le_mul hr hr zero_le_one (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_left h3 hs.le]
    have htail : ∀ S, R ≤ S → ‖(∫ r in (0 : ℝ)..S, g r) - ∫ r in (0 : ℝ)..R, g r‖ ≤
        4 / (3 * R ^ 2) := by
      intro S hS
      have hii : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
        (by fun_prop : Continuous g).intervalIntegrable a b
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 R) (hii R S), add_sub_cancel_left]
      have := statPh_norm_integral_damped_cube hs.le (by linarith : 0 < c) hR hS
      simp only [hg]
      refine this.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg R, mul_pos hR hR]
    have hlim : Tendsto (fun S => ∫ r in (0 : ℝ)..S, g r) atTop (𝓝 (∫ r in Ioi (0 : ℝ), g r)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hgi tendsto_id
    have hI : ‖(∫ r in Ioi (0 : ℝ), g r) - ∫ r in (0 : ℝ)..R, g r‖ ≤ 4 / (3 * R ^ 2) :=
      le_of_tendsto ((hlim.sub_const _).norm) (eventually_atTop.2 ⟨R, htail⟩)
    have hval := statPh_integral_ray hα0 (by linarith)
    have : F α - L = exp (α * I) * ((∫ r in (0 : ℝ)..R, g r) - ∫ r in Ioi (0 : ℝ), g r) := by
      simp only [F, L, ← hval, g]; ring
    rw [this, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_sub_rev]
    exact hI
  have hlim : Tendsto F (𝓝[Ioo 0 (π / 9)] 0) (𝓝 (F 0)) :=
    (hFc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hne : (𝓝[Ioo 0 (π / 9)] (0 : ℝ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hπ9.ne]
    exact ⟨le_rfl, hπ9.le⟩
  rw [← hF0]
  exact le_of_tendsto ((hlim.sub_const L).norm) (eventually_nhdsWithin_of_forall hbound)

/-- `∫₀^R e^{i t³} dt → Γ(4/3) e^{iπ/6}` as `R → ∞`. -/
theorem statPh_tendsto_integral_exp_cube :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, exp ((t : ℂ) ^ 3 * I)) atTop
      (𝓝 ((Real.Gamma (4 / 3) : ℂ) * exp ((π / 6 : ℝ) * I))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ((eventually_gt_atTop 0).mono fun R hR => statPh_norm_integral_exp_cube_sub_le hR) ?_
  have : Tendsto (fun R : ℝ => (4 / 3) * (R ^ 2)⁻¹) atTop (𝓝 ((4 / 3) * 0)) :=
    ((tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop).const_mul _
  rw [mul_zero] at this
  refine this.congr fun R => ?_
  field_simp


/-- Rescaling of the model integral: `λ^{1/3} ∫₀^δ e^{iλc x³} dx = c^{-1/3} ∫₀^{(λc)^{1/3} δ} e^{it³} dt`. -/
theorem statPh_integral_model {lam c δ : ℝ} (hlam : 0 < lam) (hc : 0 < c) :
    ((lam ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ∫ x in (0 : ℝ)..δ, exp (((lam * (c * x ^ 3) : ℝ) : ℂ) * I) =
      ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..((lam * c) ^ (1 / 3 : ℝ) * δ), exp ((t : ℂ) ^ 3 * I) := by
  set κ := (lam * c) ^ (1 / 3 : ℝ) with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ3 : κ ^ 3 = lam * c := by
    rw [hκ, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := δ)
    (fun t : ℝ => exp ((t : ℂ) ^ 3 * I)) hκ0.ne'
  simp only [mul_zero] at h
  have hint : ∫ x in (0 : ℝ)..δ, exp (((lam * (c * x ^ 3) : ℝ) : ℂ) * I) =
      ∫ x in (0 : ℝ)..δ, exp (((κ * x : ℝ) : ℂ) ^ 3 * I) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    congr 2
    rw [← ofReal_pow, mul_pow, hκ3]; push_cast; ring
  rw [hint, h, real_smul, ← mul_assoc]
  congr 1
  have hsplit : κ = lam ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) := Real.mul_rpow hlam.le hc.le
  rw [hsplit, Real.rpow_neg hc.le]
  have h1 : 0 < lam ^ (1 / 3 : ℝ) := by positivity
  have h2 : 0 < c ^ (1 / 3 : ℝ) := by positivity
  have h1' : ((lam ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 h1.ne'
  have h2' : ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 h2.ne'
  push_cast
  field_simp

/-- `‖e^{ia} - e^{ib}‖ ≤ |a - b|` for real `a`, `b`. -/
theorem statPh_norm_exp_sub_exp_le (a b : ℝ) :
    ‖exp ((a : ℂ) * I) - exp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have : exp ((a : ℂ) * I) - exp ((b : ℂ) * I) = exp ((b : ℂ) * I) * (exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← exp_add]; push_cast; ring_nf
  rw [this, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

/-- **Stationary phase at a cubic point.** Let `φ` be `C²` on `[0, b]` with `φ'' ≥ 0`,
`φ'(x) ≥ m x²` (`m > 0`) and `|φ(x) - c x³| ≤ K x⁴` (`c > 0`). Then, as `λ → +∞`,
`λ^{1/3} ∫₀^b e^{iλφ(x)} dx → Γ(4/3) c^{-1/3} e^{iπ/6}`. -/
theorem statPh_tendsto_cubic {b c m K : ℝ} (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    {φ φ' φ'' : ℝ → ℝ}
    (hφ : ∀ x ∈ Icc 0 b, HasDerivAt φ (φ' x) x) (hφ' : ∀ x ∈ Icc 0 b, HasDerivAt φ' (φ'' x) x)
    (hφ''c : ContinuousOn φ'' (Icc 0 b)) (hφ''0 : ∀ x ∈ Icc 0 b, 0 ≤ φ'' x)
    (hφ'm : ∀ x ∈ Icc 0 b, m * x ^ 2 ≤ φ' x)
    (hφK : ∀ x ∈ Icc 0 b, |φ x - c * x ^ 3| ≤ K * x ^ 4) :
    Tendsto (fun lam : ℝ => ((lam ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        ∫ x in (0 : ℝ)..b, exp (((lam * φ x : ℝ) : ℂ) * I)) atTop
      (𝓝 (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * ((Real.Gamma (4 / 3) : ℂ) * exp ((π / 6 : ℝ) * I)))) := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg _).trans (hφK b ⟨hb.le, le_rfl⟩)
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hφc : ContinuousOn φ (Icc 0 b) := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hφ'c : ContinuousOn φ' (Icc 0 b) := fun x hx => (hφ' x hx).continuousAt.continuousWithinAt
  set δ : ℝ → ℝ := fun lam => lam ^ (-(3 / 10 : ℝ)) with hδ
  set A : ℝ → ℂ := fun lam => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) *
    ∫ t in (0 : ℝ)..((lam * c) ^ (1 / 3 : ℝ) * δ lam), exp ((t : ℂ) ^ 3 * I)
  set B : ℝ → ℂ := fun lam => ((lam ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ∫ x in (0 : ℝ)..δ lam,
    (exp (((lam * φ x : ℝ) : ℂ) * I) - exp (((lam * (c * x ^ 3) : ℝ) : ℂ) * I))
  set C : ℝ → ℂ := fun lam => ((lam ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
    ∫ x in δ lam..b, exp (((lam * φ x : ℝ) : ℂ) * I)
  have hev : ∀ᶠ lam : ℝ in atTop, 0 < lam ∧ δ lam < b :=
    (eventually_gt_atTop 0).and ((tendsto_rpow_neg_atTop (by norm_num)).eventually (Iio_mem_nhds hb))
  -- decomposition
  have hdec : ∀ᶠ lam : ℝ in atTop, A lam + B lam + C lam = ((lam ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      ∫ x in (0 : ℝ)..b, exp (((lam * φ x : ℝ) : ℂ) * I) := by
    filter_upwards [hev] with lam ⟨hl, hδb⟩
    have hδ0 : 0 < δ lam := by simp only [hδ]; positivity
    have hsub : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ b → uIcc u v ⊆ Icc 0 b := fun hu huv hvb => by
      rw [uIcc_of_le huv]; exact Icc_subset_Icc hu hvb
    have i1 : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ b →
        IntervalIntegrable (fun x => exp (((lam * φ x : ℝ) : ℂ) * I)) volume u v :=
      fun hu huv hvb => ContinuousOn.intervalIntegrable
        ((continuous_ofReal.comp_continuousOn ((hφc.mono (hsub hu huv hvb)).const_smul lam)).mul
          continuousOn_const).cexp
    have i2 : IntervalIntegrable (fun x : ℝ => exp (((lam * (c * x ^ 3) : ℝ) : ℂ) * I)) volume 0 (δ lam) :=
      (by fun_prop : Continuous fun x : ℝ => exp (((lam * (c * x ^ 3) : ℝ) : ℂ) * I)).intervalIntegrable _ _
    simp only [A, B, C]
    rw [← statPh_integral_model hl hc, intervalIntegral.integral_sub (i1 le_rfl hδ0.le hδb.le) i2,
      ← intervalIntegral.integral_add_adjacent_intervals (i1 le_rfl hδ0.le hδb.le)
        (i1 hδ0.le hδb.le le_rfl)]
    ring
  -- the model part
  have hA : Tendsto A atTop
      (𝓝 (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * ((Real.Gamma (4 / 3) : ℂ) * exp ((π / 6 : ℝ) * I)))) := by
    refine (statPh_tendsto_integral_exp_cube.comp ?_).const_mul _
    have h30 : Tendsto (fun lam : ℝ => c ^ (1 / 3 : ℝ) * lam ^ (1 / 30 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).const_mul_atTop (by positivity)
    refine h30.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with lam hl
    simp only [hδ]
    rw [Real.mul_rpow hl.le hc.le, mul_comm (lam ^ (1 / 3 : ℝ)), mul_assoc, ← Real.rpow_add hl]
    norm_num
  -- the Taylor part
  have hB : Tendsto B atTop (𝓝 0) := by
    have hbd : ∀ᶠ lam : ℝ in atTop, ‖B lam‖ ≤ K * lam ^ (-(1 / 6 : ℝ)) := by
      filter_upwards [hev] with lam ⟨hl, hδb⟩
      have hδ0 : 0 < δ lam := by simp only [hδ]; positivity
      have hin : ∀ x ∈ Ι 0 (δ lam), ‖exp (((lam * φ x : ℝ) : ℂ) * I) -
          exp (((lam * (c * x ^ 3) : ℝ) : ℂ) * I)‖ ≤ lam * K * δ lam ^ 4 := by
        intro x hx
        rw [uIoc_of_le hδ0.le] at hx
        refine (statPh_norm_exp_sub_exp_le _ _).trans ?_
        rw [← mul_sub, abs_mul, abs_of_pos hl, mul_assoc]
        gcongr
        refine (hφK x ⟨hx.1.le, hx.2.trans hδb.le⟩).trans ?_
        gcongr
        · exact hx.1.le
        · exact hx.2
      have := intervalIntegral.norm_integral_le_of_norm_le_const hin
      simp only [B]
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      refine (mul_le_mul_of_nonneg_left this (by positivity)).trans (le_of_eq ?_)
      rw [sub_zero, abs_of_pos hδ0]
      simp only [hδ]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
      have e : lam ^ (1 / 3 : ℝ) * (lam * K * lam ^ (-(3 / 10 : ℝ) * ((4 : ℕ) : ℝ)) *
          lam ^ (-(3 / 10 : ℝ))) = K * (lam ^ (1 / 3 : ℝ) * lam ^ (1 : ℝ) *
          lam ^ (-(3 / 10 : ℝ) * ((4 : ℕ) : ℝ)) * lam ^ (-(3 / 10 : ℝ))) := by
        rw [Real.rpow_one]; ring
      rw [e, ← Real.rpow_add hl, ← Real.rpow_add hl, ← Real.rpow_add hl]
      norm_num
    have h0 : Tendsto (fun lam : ℝ => K * lam ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul K
    exact squeeze_zero_norm' hbd h0
  -- the non-stationary part
  have hC : Tendsto C atTop (𝓝 0) := by
    have hbd : ∀ᶠ lam : ℝ in atTop, ‖C lam‖ ≤ 2 / m * lam ^ (-(1 / 15 : ℝ)) := by
      filter_upwards [hev] with lam ⟨hl, hδb⟩
      have hδ0 : 0 < δ lam := by simp only [hδ]; positivity
      have hsub : Icc (δ lam) b ⊆ Icc 0 b := Icc_subset_Icc hδ0.le le_rfl
      have hpos : ∀ x ∈ Icc (δ lam) b, 0 < φ' x := fun x hx => by
        have := hφ'm x (hsub hx)
        have : 0 < x := hδ0.trans_le hx.1
        nlinarith [mul_pos hm (mul_pos this this)]
      have hne : ∀ x ∈ Icc (δ lam) b, lam * φ' x ≠ 0 := fun x hx =>
        (mul_pos hl (hpos x hx)).ne'
      have key := statPh_norm_integral_le hδb.le (φ := fun x => lam * φ x)
        (φ' := fun x => lam * φ' x) (ψ := fun x => (lam * φ' x)⁻¹)
        (ψ' := fun x => -(lam * φ'' x) / (lam * φ' x) ^ 2)
        (fun x hx => (hφ x (hsub hx)).const_mul lam)
        (fun x hx => ((hφ' x (hsub hx)).const_mul lam).inv (hne x hx))
        ((hφ'c.mono hsub).const_smul lam)
        (ContinuousOn.div ((hφ''c.mono hsub).const_smul lam).neg
          (((hφ'c.mono hsub).const_smul lam).pow 2) fun x hx => pow_ne_zero 2 (hne x hx))
        (fun x hx => div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.2 (mul_nonneg hl.le (hφ''0 x (hsub hx)))) (sq_nonneg _))
        (inv_nonneg.2 (mul_pos hl (hpos b ⟨hδb.le, le_rfl⟩)).le)
      have heq : ∫ x in δ lam..b, exp (((lam * φ x : ℝ) : ℂ) * I) =
          ∫ x in δ lam..b, (((lam * φ' x)⁻¹ * (lam * φ' x) : ℝ) : ℂ) *
            exp (((lam * φ x : ℝ) : ℂ) * I) := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [uIcc_of_le hδb.le] at hx
        rw [inv_mul_cancel₀ (hne x hx), ofReal_one, one_mul]
      simp only [C]
      rw [heq, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      refine (mul_le_mul_of_nonneg_left key (by positivity)).trans ?_
      have hm' : m * δ lam ^ 2 ≤ φ' (δ lam) := hφ'm _ ⟨hδ0.le, hδb.le⟩
      have hmd : 0 < m * δ lam ^ 2 := by positivity
      have : (lam * φ' (δ lam))⁻¹ ≤ (lam * (m * δ lam ^ 2))⁻¹ :=
        inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hm' hl.le)
      calc lam ^ (1 / 3 : ℝ) * (2 * (lam * φ' (δ lam))⁻¹)
          ≤ lam ^ (1 / 3 : ℝ) * (2 * (lam * (m * δ lam ^ 2))⁻¹) := by gcongr
        _ = 2 / m * (lam ^ (1 / 3 : ℝ) * lam ^ (-(1 : ℝ)) *
              lam ^ (-(-(3 / 10 : ℝ) * ((2 : ℕ) : ℝ)))) := by
            simp only [hδ]
            rw [← Real.rpow_natCast (lam ^ _), ← Real.rpow_mul hl.le, Real.rpow_neg hl.le,
              Real.rpow_neg hl.le, Real.rpow_one]
            field_simp
        _ = 2 / m * lam ^ (-(1 / 15 : ℝ)) := by
            rw [← Real.rpow_add hl, ← Real.rpow_add hl]; norm_num
    have h0 : Tendsto (fun lam : ℝ => 2 / m * lam ^ (-(1 / 15 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 15)).const_mul (2 / m)
    exact squeeze_zero_norm' hbd h0
  have := (hA.add hB).add hC
  rw [add_zero, add_zero] at this
  exact this.congr' hdec

end Complex
