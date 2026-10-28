/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.Representations.LowerBarnes

/-!
# Gamma strip bounds and upper incomplete Gamma representations

Uniform vertical Gamma bounds support the upper incomplete-Gamma Barnes representation and its
continuation.

Source references and common attribution are retained in
`DLMF.IncompleteGamma.Representations`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

open DLMF.Statistical

/-! ### Tools for DLMF 8.6.12 -/

/-- Uniform vertical bounds for `Γ` on a strip `|Re w| ≤ X`: with the factor `|sin(π Re w)|`
for all heights, and without it for `|Im w| ≥ 1`. -/
theorem incRep_Gamma_bound (X : ℝ) :
    ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ x ∈ Icc (-X) X, ∀ y : ℝ,
      ‖Gamma (x + I*y)‖ * |Real.sin (π*x)| ≤ C * (1+|y|)^K * Real.exp (-(π*|y|)/2) ∧
      (1 ≤ |y| → ‖Gamma (x + I*y)‖ ≤ C * (1+|y|)^K * Real.exp (-(π*|y|)/2)) := by
  obtain ⟨C, K, hC⟩ := DLMF.Gamma.exists_norm_recip_Gamma_le (X+1)
  set C0 : ℝ := max C 0
  refine ⟨4*π*C0, K, by positivity, fun x hx y => ?_⟩
  set E : ℝ := Real.exp (π*|y|/2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (π*|y|) = E*E := by rw [hE, ← Real.exp_add]; ring_nf
  have hEi : Real.exp (-(π*|y|)/2) = E⁻¹ := by rw [hE, ← Real.exp_neg]; ring_nf
  have hP : 0 ≤ (1+|y|)^K := by positivity
  have h1 : ‖(Gamma (1 - (x + I*y)))⁻¹‖ ≤ C0 * (1+|y|)^K * E := by
    have := hC (1-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩ (-y)
    rw [show ((1-x:ℝ):ℂ) + I*((-y:ℝ):ℂ) = 1 - (x + I*y) by push_cast; ring, abs_neg] at this
    refine this.trans ?_
    gcongr
    exact le_max_left _ _
  have h2 := (Complex.barnesRes_norm_Gamma_mul_sin_le (x + I*y)).trans (mul_le_mul_of_nonneg_left h1 Real.pi_pos.le)
  have hw : (π:ℂ)*(x + I*y) = ((π*x:ℝ):ℂ) + ((π*y:ℝ):ℂ)*I := by push_cast; ring
  rw [hw] at h2
  have hcosh : E*E/2 ≤ Real.cosh (π*y) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq, ← hE2]
    have := Real.exp_pos (-(π*|y|)); linarith
  have hG0 := norm_nonneg (Gamma (x + I*y))
  constructor
  · have hs := Complex.barnesRes_abs_sin_mul_cosh_le_norm_sin (π*x) (π*y)
    have h3 : ‖Gamma (x + I*y)‖ * |Real.sin (π*x)| * (E*E/2) ≤ π * (C0 * (1+|y|)^K * E) := by
      refine le_trans ?_ h2
      rw [mul_assoc]
      gcongr
      exact (mul_le_mul_of_nonneg_left hcosh (abs_nonneg _)).trans hs
    rw [hEi]
    rw [← le_div_iff₀ (by positivity)] at h3
    refine h3.trans ?_
    have e : π * (C0 * (1+|y|)^K * E) / (E*E/2) = 2*(π*C0*(1+|y|)^K*E⁻¹) := by field_simp
    have : 0 ≤ π*C0*(1+|y|)^K*E⁻¹ := by positivity
    rw [e]; linarith
  · intro hy
    have hs := Complex.barnesRes_abs_sinh_le_norm_sin (π*x) (π*y)
    have hsinh : E*E/4 ≤ |Real.sinh (π*y)| := by
      rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos, Real.sinh_eq, ← hE2]
      have hu : π ≤ π*|y| := by nlinarith [Real.pi_pos]
      have h4 := Real.add_one_le_exp (π*|y|)
      have h5 : Real.exp (-(π*|y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
      nlinarith [Real.pi_gt_three]
    have h3 : ‖Gamma (x + I*y)‖ * (E*E/4) ≤ π * (C0 * (1+|y|)^K * E) := by
      refine le_trans ?_ h2
      gcongr
      exact hsinh.trans hs
    rw [hEi]
    rw [← le_div_iff₀ (by positivity)] at h3
    refine h3.trans (le_of_eq ?_)
    field_simp

/-- Vertical bound for `Γ` on a line `Re w = x` missing the poles. -/
theorem incRep_Gamma_bound_pt {x : ℝ} (hx : ∀ n : ℕ, x ≠ -n) :
    ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ y : ℝ,
      ‖Gamma (x + I*y)‖ ≤ C * (1+|y|)^K * Real.exp (-(π*|y|)/2) := by
  by_cases hx0 : 0 < x
  · obtain ⟨C, K, h⟩ := DLMF.Gamma.exists_norm_Gamma_le hx0
    exact ⟨C, K, (norm_nonneg _).trans (by simpa using h 0), h⟩
  · push Not at hx0
    have hs := Complex.barnesRes_real_sin_ne_zero hx0 hx
    have hs0 : 0 < |Real.sin (π*x)| := abs_pos.mpr hs
    obtain ⟨C, K, hC0, h⟩ := incRep_Gamma_bound |x|
    refine ⟨C / |Real.sin (π*x)|, K, by positivity, fun y => ?_⟩
    have := (h x ⟨neg_abs_le x, le_abs_self x⟩ y).1
    rw [← le_div_iff₀ hs0] at this
    refine this.trans (le_of_eq ?_)
    field_simp

/-- The DLMF 8.6.12 integrand `Γ(s+1-a) π/sin(πs) e^{-sw}`. -/
def incRep_f (a w s : ℂ) : ℂ := Gamma (s+1-a)*π/Complex.sin (π*s)*exp (-s*w)

/-- Pointwise bound for the 8.6.12 integrand. -/
theorem incRep_norm_f_le {a w : ℂ} (x y : ℝ) {C S : ℝ} {K : ℕ} (hC : 0 ≤ C) (hS : 0 < S)
    (g : ‖Gamma ((x+1-a.re : ℝ) + I*(y - a.im : ℝ))‖ ≤
      C * (1+|y - a.im|)^K * Real.exp (-(π*|y - a.im|)/2))
    (gs : S * Real.exp (π*|y|) ≤ ‖Complex.sin (π*((x:ℂ) + y*I))‖) :
    ‖incRep_f a w (x + y*I)‖ ≤ C * (1+|a.im|)^K * Real.exp (π*|a.im|/2) * (π/S) *
      Real.exp (-(x*w.re)) * ((1+|y|)^K * Real.exp (-((3*π/2 - |w.im|)*|y|))) := by
  have e1 : (x:ℂ) + y*I + 1 - a = ((x+1-a.re : ℝ) : ℂ) + I*((y - a.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hp : (1 + |y - a.im|)^K ≤ (1+|a.im|)^K * (1+|y|)^K := by
    rw [← mul_pow]; gcongr
    have := abs_sub y a.im
    nlinarith [abs_nonneg a.im, abs_nonneg y]
  have he : Real.exp (-(π * |y - a.im|) / 2) ≤ Real.exp (π*|a.im|/2) * Real.exp (-(π*|y|)/2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have := abs_sub_abs_le_abs_sub y a.im
    nlinarith [Real.pi_pos]
  have hE : ‖exp (-((x:ℂ) + y*I)*w)‖ ≤ Real.exp (-(x*w.re)) * Real.exp (|w.im| * |y|) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (-((x:ℂ) + y*I)*w).re = -(x*w.re) + y*w.im := by simp
    rw [this]
    have := neg_abs_le (y*w.im); have := le_abs_self (y*w.im)
    rw [abs_mul] at *; nlinarith [abs_nonneg y, abs_nonneg w.im]
  have hsin0 : 0 < ‖Complex.sin (π*((x:ℂ) + y*I))‖ :=
    lt_of_lt_of_le (by positivity) gs
  have hpis : ‖(π:ℂ) / Complex.sin (π*((x:ℂ) + y*I))‖ ≤ π/S * Real.exp (-(π*|y|)) := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_iff₀ hsin0]
    calc π = π/S * Real.exp (-(π*|y|)) * (S * Real.exp (π*|y|)) := by
          rw [show π/S * Real.exp (-(π*|y|)) * (S * Real.exp (π*|y|)) =
            π * (Real.exp (-(π*|y|)) * Real.exp (π*|y|)) * (S/S) by ring, ← Real.exp_add,
            neg_add_cancel, Real.exp_zero, div_self hS.ne']; ring
      _ ≤ _ := by gcongr
  unfold incRep_f
  rw [mul_div_assoc, norm_mul, norm_mul, e1]
  calc ‖Gamma (((x+1-a.re : ℝ) : ℂ) + I*((y - a.im : ℝ) : ℂ))‖ *
        ‖(π:ℂ) / Complex.sin (π*((x:ℂ) + y*I))‖ * ‖exp (-((x:ℂ) + y*I)*w)‖
      ≤ (C * ((1+|a.im|)^K * (1+|y|)^K) * (Real.exp (π*|a.im|/2) * Real.exp (-(π*|y|)/2))) *
          (π/S * Real.exp (-(π*|y|))) * (Real.exp (-(x*w.re)) * Real.exp (|w.im| * |y|)) := by
        gcongr
        exact g.trans (by gcongr)
    _ = C * (1+|a.im|)^K * Real.exp (π*|a.im|/2) * (π/S) * Real.exp (-(x*w.re)) *
          ((1+|y|)^K * (Real.exp (-(π*|y|)/2) * Real.exp (-(π*|y|)) * Real.exp (|w.im| * |y|))) := by
        ring
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (incRep_f a w) s`. -/
theorem incRep_f_differentiableAt {a w s : ℂ} (hs : Complex.sin (π*s) ≠ 0)
    (hA : ∀ m : ℕ, s+1-a ≠ -m) : DifferentiableAt ℂ (incRep_f a w) s := by
  unfold incRep_f
  exact ((((differentiableAt_Gamma _ hA).comp s (by fun_prop)).mul_const _).div
    ((Complex.differentiable_sin _).comp s (by fun_prop)) hs).mul (by fun_prop)

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (fun a => incRep_f a w s) a`. -/
theorem incRep_f_differentiableAt_param {a w s : ℂ} (hA : ∀ m : ℕ, s+1-a ≠ -m) :
    DifferentiableAt ℂ (fun a => incRep_f a w s) a := by
  unfold incRep_f
  exact ((((differentiableAt_Gamma _ hA).comp a (by fun_prop)).mul_const _).div_const _).mul_const _

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (fun w => incRep_f a w s) w`. -/
theorem incRep_f_differentiableAt_w {a w s : ℂ} : DifferentiableAt ℂ (fun w => incRep_f a w s) w := by
  unfold incRep_f; fun_prop

/-- Nonvanishing under the stated hypotheses: `∀ m : ℕ, (x:ℂ) + y*I + 1 - a ≠ -m`. -/
theorem incRep_ne_pole {a : ℂ} {x : ℝ} (hav : ∀ n : ℕ, a.re - 1 - n ≠ x) (y : ℝ) :
    ∀ m : ℕ, (x:ℂ) + y*I + 1 - a ≠ -m := fun m h => by
  have := congrArg re h; simp at this; exact hav m (by linarith)

/-- Continuity of the indicated function: `Continuous fun y : ℝ => incRep_f a w (c + y*I)`. -/
theorem incRep_f_continuous {a w : ℂ} {c : ℝ} (hs : Real.sin (π*c) ≠ 0)
    (hav : ∀ n : ℕ, a.re - 1 - n ≠ c) : Continuous fun y : ℝ => incRep_f a w (c + y*I) :=
  continuous_iff_continuousAt.mpr fun y => by
    have h := (incRep_f_differentiableAt (w := w) (Complex.barnesRes_sin_ne_zero_of_re (by simpa using hs))
      (incRep_ne_pole hav y)).continuousAt
    exact h.comp (f := fun y : ℝ => (c:ℂ) + y*I) (by fun_prop)

/-- The 8.6.12 integrand is integrable on admissible lines. -/
theorem incRep_f_integrable {a w : ℂ} (hw : |w.im| < 3*π/2) {c : ℝ} (hs : Real.sin (π*c) ≠ 0)
    (hav : ∀ n : ℕ, a.re - 1 - n ≠ c) : Integrable fun y : ℝ => incRep_f a w (c + y*I) := by
  obtain ⟨C, K, hC, h⟩ := incRep_Gamma_bound_pt (x := c+1-a.re) (fun n h => hav n (by linarith))
  have hS : 0 < |Real.sin (π*c)|/2 := by positivity
  refine ((DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (c := 3*π/2 - |w.im|)
    (by linarith) K).const_mul _).mono' (incRep_f_continuous hs hav).aestronglyMeasurable
    (Eventually.of_forall fun y => incRep_norm_f_le c y hC hS (h _) (Complex.barnesRes_sin_lower_line c y))

open scoped Interval in
/-- Horizontal cross-sections of the 8.6.12 integrand vanish at `±i∞`. -/
theorem incRep_f_horizontal {a w : ℂ} (hw : |w.im| < 3*π/2) {c₁ c₂ : ℝ} (h12 : c₁ ≤ c₂) :
    Tendsto (fun T : ℝ => ∫ x in c₁..c₂, incRep_f a w (x + T*I)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => ∫ x in c₁..c₂, incRep_f a w (x + T*I)) atBot (𝓝 0) := by
  obtain ⟨C, K, hC, h⟩ := incRep_Gamma_bound (|c₁| + |c₂| + 1 + |a.re|)
  set b : ℝ := 3*π/2 - |w.im|
  have hb : 0 < b := by simp only [b]; linarith
  set M : ℝ := C * (1+|a.im|)^K * Real.exp (π*|a.im|/2) * (π/(1/4)) *
    Real.exp ((|c₁| + |c₂|) * |w.re|)
  have key : ∀ T : ℝ, 1 ≤ |T| → 1 ≤ |T - a.im| → ‖∫ x in c₁..c₂, incRep_f a w (x + T*I)‖ ≤
      (c₂ - c₁) * (M * ((1 + |T|) ^ K * Real.exp (-(b * |T|)))) := by
    intro T hT hTa
    have hpt : ∀ x ∈ Ι c₁ c₂, ‖incRep_f a w (x + T*I)‖ ≤
        M * ((1 + |T|) ^ K * Real.exp (-(b * |T|))) := by
      intro x hx
      rw [uIoc_of_le h12] at hx
      have hX : x + 1 - a.re ∈ Icc (-(|c₁| + |c₂| + 1 + |a.re|)) (|c₁| + |c₂| + 1 + |a.re|) := by
        have := abs_le.mp (le_refl |c₁|); have := abs_le.mp (le_refl |c₂|)
        have := abs_le.mp (le_refl |a.re|)
        constructor <;> linarith [hx.1, hx.2]
      refine (incRep_norm_f_le x T hC (by norm_num) ((h _ hX _).2 hTa)
        (Complex.barnesRes_sin_lower_far x hT)).trans ?_
      have hxw : Real.exp (-(x*w.re)) ≤ Real.exp ((|c₁| + |c₂|) * |w.re|) := by
        apply Real.exp_le_exp.mpr
        have h1 : |x| ≤ |c₁| + |c₂| := by
          rw [abs_le]; constructor <;> linarith [hx.1, hx.2, abs_le.mp (le_refl |c₁|),
            abs_le.mp (le_refl |c₂|)]
        have := neg_abs_le (x*w.re); rw [abs_mul] at this
        nlinarith [abs_nonneg w.re, abs_nonneg x]
      simp only [M, b]
      gcongr
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_nonneg (sub_nonneg.mpr h12)] at this
    linarith
  have hlim := Complex.barnesRes_tendsto_poly_exp hb K
  have l1 := ((hlim.comp tendsto_abs_atTop_atTop).const_mul M).const_mul (c₂ - c₁)
  have l2 := ((hlim.comp tendsto_abs_atBot_atTop).const_mul M).const_mul (c₂ - c₁)
  simp only [mul_zero] at l1 l2
  constructor
  · refine squeeze_zero_norm' ?_ l1
    filter_upwards [eventually_ge_atTop (|a.im| + 1)] with T hT
    have h0 := abs_nonneg a.im
    exact key T (by rw [abs_of_nonneg (by linarith)]; linarith) (by
      rw [abs_of_nonneg (by linarith [le_abs_self a.im])]; linarith [le_abs_self a.im])
  · refine squeeze_zero_norm' ?_ l2
    filter_upwards [eventually_le_atBot (-(|a.im| + 1))] with T hT
    have h0 := abs_nonneg a.im
    exact key T (by rw [abs_of_nonpos (by linarith)]; linarith) (by
      rw [abs_of_nonpos (by linarith [neg_abs_le a.im])]; linarith [neg_abs_le a.im])

/-- Shifting the 8.6.12 line when no pole lies in the closed strip. -/
theorem incRep_shift_none {a w : ℂ} (hw : |w.im| < 3*π/2) {c₁ c₂ : ℝ} (h12 : c₁ < c₂)
    (hsin : ∀ x ∈ Icc c₁ c₂, Real.sin (π*x) ≠ 0) (hno : ∀ n : ℕ, a.re - 1 - n ∉ Icc c₁ c₂) :
    (∫ y : ℝ, incRep_f a w (c₂ + y*I)) = ∫ y : ℝ, incRep_f a w (c₁ + y*I) := by
  have hav : ∀ c ∈ Icc c₁ c₂, ∀ n : ℕ, a.re - 1 - n ≠ c := fun c hcI n h => hno n (h ▸ hcI)
  obtain ⟨ht, hb⟩ := incRep_f_horizontal (a := a) hw h12.le
  have h1I : c₁ ∈ Icc c₁ c₂ := ⟨le_rfl, h12.le⟩
  have h2I : c₂ ∈ Icc c₁ c₂ := ⟨h12.le, le_rfl⟩
  refine Complex.barnesRes_vertical_shift_of_differentiableOn h12 (fun t htS => ?_)
    (incRep_f_integrable hw (hsin c₁ h1I) (hav c₁ h1I))
    (incRep_f_integrable hw (hsin c₂ h2I) (hav c₂ h2I)) ht hb
  have htS' : t.re ∈ Icc c₁ c₂ := htS
  refine (incRep_f_differentiableAt (Complex.barnesRes_sin_ne_zero_of_re (hsin _ htS')) fun m h => ?_
    ).differentiableWithinAt
  have := congrArg re h; simp at this
  exact hno m (by rw [show a.re - 1 - m = t.re by linarith]; exact htS')

/-- The residue of the 8.6.12 integrand at `s = a-1-n`. -/
def incRep_res (a w : ℂ) (n : ℕ) : ℂ :=
  (-1)^n/(n.factorial:ℂ) * (π/Complex.sin (π*(a-1-n))) * exp (-(a-1-n)*w)

/-- The removable-singularity form `(s - (a-1-n)) f(s)`. -/
def incRep_phi (a w : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  Gamma (s+1-a+n+1) / (∏ j ∈ Finset.range n, (s+1-a+j)) * (π/Complex.sin (π*s)) * exp (-s*w)

/-- Identity under the stated parameter and domain assumptions: `incRep_phi a w n (a-1-n) =
incRep_res a w n`. -/
theorem incRep_phi_pole (a w : ℂ) (n : ℕ) : incRep_phi a w n (a-1-n) = incRep_res a w n := by
  unfold incRep_phi incRep_res
  have h1 : a-1-n+1-a+n+1 = (1:ℂ) := by ring
  have h2 : ∏ j ∈ Finset.range n, (a-1-n+1-a+(j:ℂ)) = (-1)^n * n.factorial := by
    rw [← Complex.barnesRes_prod_sub_nat n]; exact Finset.prod_congr rfl fun j _ => by ring
  rw [h1, h2, Gamma_one]
  have hinv : ((-1:ℂ)^n)⁻¹ = (-1)^n := by rw [← inv_pow, inv_neg, inv_one]
  rw [div_eq_mul_inv (1:ℂ), one_mul, mul_inv, hinv]
  ring

/-- `φ(s)/(s - p) = f(s)` away from the pole `p = a-1-n` and from the poles of index `< n`. -/
theorem incRep_phi_div {a w s : ℂ} {n : ℕ} (hs : s ≠ a-1-n)
    (hj : ∀ j : ℕ, j < n → s+1-a+j ≠ 0) :
    incRep_phi a w n s / (s - (a-1-n)) = incRep_f a w s := by
  have hn : s+1-a+n ≠ 0 := fun h => hs (by linear_combination h)
  have hall : ∀ j : ℕ, j ≤ n → s+1-a+j ≠ 0 := fun j hjn => by
    rcases lt_or_eq_of_le hjn with h | rfl
    · exact hj j h
    · exact hn
  have hG := Complex.barnesRes_Gamma_add_nat_succ (s+1-a) n hall
  rw [Finset.prod_range_succ] at hG
  have hP : ∏ j ∈ Finset.range n, (s+1-a+j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj' => hj j (Finset.mem_range.mp hj')
  have hd : s - (a-1-n) ≠ 0 := sub_ne_zero.mpr hs
  unfold incRep_phi incRep_f
  rw [hG, show s+1-a+(n:ℂ) = s - (a-1-n) by ring]
  field_simp

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (incRep_phi a w n) s`. -/
theorem incRep_phi_differentiableAt {a w s : ℂ} {n : ℕ} (hs : Complex.sin (π*s) ≠ 0)
    (hA : ∀ m : ℕ, s+1-a+n+1 ≠ -m) (hj : ∀ j : ℕ, j < n → s+1-a+j ≠ 0) :
    DifferentiableAt ℂ (incRep_phi a w n) s := by
  have hP : ∏ j ∈ Finset.range n, (s+1-a+j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj' => hj j (Finset.mem_range.mp hj')
  unfold incRep_phi
  refine ((((differentiableAt_Gamma _ hA).comp s (by fun_prop)).div (by fun_prop) hP).mul
    ((differentiableAt_const _).div ((Complex.differentiable_sin _).comp s (by fun_prop)) hs)).mul
    (by fun_prop)

/-- Shifting the 8.6.12 line across exactly one pole `s = a-1-n`. -/
theorem incRep_shift_one {a w : ℂ} (hw : |w.im| < 3*π/2) {c₁ c₂ : ℝ}
    (hsin : ∀ x ∈ Icc c₁ c₂, Real.sin (π*x) ≠ 0) {n : ℕ} (hn₁ : c₁ < a.re - 1 - n)
    (hn₂ : a.re - 1 - n < c₂) (hno : ∀ m : ℕ, m ≠ n → a.re - 1 - m ∉ Icc c₁ c₂) :
    (∫ y : ℝ, incRep_f a w (c₂ + y*I)) - (∫ y : ℝ, incRep_f a w (c₁ + y*I)) =
      2*π*incRep_res a w n := by
  have h12 : c₁ < c₂ := hn₁.trans hn₂
  set p : ℂ := a-1-n with hp
  have hpre : p.re = a.re - 1 - n := by simp [hp]
  have hpim : p.im = a.im := by simp [hp]
  have hj : ∀ t : ℂ, t.re ∈ Icc c₁ c₂ → ∀ j : ℕ, j < n → t+1-a+j ≠ 0 := by
    intro t htS j hjn h
    have := congrArg re h; simp at this
    exact hno j hjn.ne (by rw [show a.re - 1 - j = t.re by linarith]; exact htS)
  have hdiv : ∀ t : ℂ, t.re ∈ Icc c₁ c₂ → t ≠ p → incRep_phi a w n t / (t - p) = incRep_f a w t :=
    fun t htS htp => incRep_phi_div htp (hj t htS)
  have hav : ∀ c ∈ Icc c₁ c₂, c ≠ a.re - 1 - n → ∀ m : ℕ, a.re - 1 - m ≠ c := by
    intro c hcI hcn m h
    by_cases hm : m = n
    · subst hm; exact hcn h.symm
    · exact hno m hm (h ▸ hcI)
  have hline : ∀ c ∈ Icc c₁ c₂, c ≠ a.re - 1 - n →
      (fun y : ℝ => incRep_phi a w n (c + y*I) / (c + y*I - p)) =
        fun y : ℝ => incRep_f a w (c + y*I) := by
    intro c hcI hcn
    funext y
    exact hdiv _ (by simpa using hcI) (fun h => hcn (by
      have := congrArg re h; simp at this; rw [this, hpre]))
  have h1I : c₁ ∈ Icc c₁ c₂ := ⟨le_rfl, h12.le⟩
  have h2I : c₂ ∈ Icc c₁ c₂ := ⟨h12.le, le_rfl⟩
  have hn1 : c₁ ≠ a.re - 1 - n := hn₁.ne
  have hn2 : c₂ ≠ a.re - 1 - n := hn₂.ne'
  obtain ⟨ht, hb⟩ := incRep_f_horizontal (a := a) hw h12.le
  have hH : ∀ T : ℝ, T ≠ a.im → (∫ x in c₁..c₂, incRep_phi a w n (x + T*I) / (x + T*I - p)) =
      ∫ x in c₁..c₂, incRep_f a w (x + T*I) := by
    intro T hT
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le h12.le] at hx
    exact hdiv _ (by simpa using hx) (fun h => hT (by
      have := congrArg im h; simp at this; rw [this, hpim]))
  have hΦ : DifferentiableOn ℂ (incRep_phi a w n) (re ⁻¹' Icc c₁ c₂) := by
    intro t htS
    have htS' : t.re ∈ Icc c₁ c₂ := htS
    refine (incRep_phi_differentiableAt (Complex.barnesRes_sin_ne_zero_of_re (hsin _ htS'))
      (fun m h => ?_) (hj t htS')).differentiableWithinAt
    have := congrArg re h; simp at this
    exact hno (n+1+m) (by omega) (by
      rw [show a.re - 1 - ((n+1+m : ℕ) : ℝ) = t.re by push_cast; linarith]; exact htS')
  have key := Complex.barnesRes_vertical_shift (p := p)
    (by rw [hpre]; exact hn₁) (by rw [hpre]; exact hn₂) hΦ
    (by rw [hline c₁ h1I hn1]; exact incRep_f_integrable hw (hsin c₁ h1I) (hav c₁ h1I hn1))
    (by rw [hline c₂ h2I hn2]; exact incRep_f_integrable hw (hsin c₂ h2I) (hav c₂ h2I hn2))
    (ht.congr' (by
      filter_upwards [eventually_gt_atTop a.im] with T hT
      exact (hH T hT.ne').symm))
    (hb.congr' (by
      filter_upwards [eventually_lt_atBot a.im] with T hT
      exact (hH T hT.ne).symm))
  rw [hline c₁ h1I hn1, hline c₂ h2I hn2, hp, incRep_phi_pole] at key
  exact key

/-- The `limUnder` residue of `gammaBarnesResidueSum` is the explicit residue. -/
theorem incRep_limUnder_res {a w : ℂ} {n : ℕ} (hs : Complex.sin (π*(a-1-n)) ≠ 0) :
    limUnder (𝓝[≠] (a-1-n)) (fun s : ℂ => (s-(a-1-n))*Gamma (s+1-a)*π/Complex.sin (π*s)*
      exp (-s*w)) = incRep_res a w n := by
  set p : ℂ := a-1-n with hp
  have hjp : ∀ j : ℕ, j < n → p+1-a+j ≠ 0 := fun j hj h => by
    have : (j:ℂ) = n := by linear_combination h
    exact hj.ne (by exact_mod_cast this)
  have hd := incRep_phi_differentiableAt (a := a) (w := w) (n := n) hs
    (fun m h => by
      have : (m:ℂ) = -1 := by rw [hp] at h; linear_combination h
      have := congrArg re this; simp at this; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]) hjp
  have hc := hd.continuousAt
  rw [← incRep_phi_pole]
  refine Tendsto.limUnder_eq ?_
  have hev : ∀ᶠ s in 𝓝[≠] p, incRep_phi a w n s =
      (s-p)*Gamma (s+1-a)*π/Complex.sin (π*s)*exp (-s*w) := by
    have hcj : ∀ j ∈ Finset.range n, ∀ᶠ s in 𝓝 p, s+1-a+j ≠ 0 := fun j hj =>
      ((continuous_id.add continuous_const).sub continuous_const |>.add
        continuous_const).continuousAt.eventually_ne (hjp j (Finset.mem_range.mp hj))
    have hall := (Finset.eventually_all (Finset.range n)).mpr hcj
    filter_upwards [nhdsWithin_le_nhds hall, self_mem_nhdsWithin] with s hs1 hs2
    have := incRep_phi_div (w := w) hs2 (fun j hj => hs1 j (Finset.mem_range.mpr hj))
    rw [div_eq_iff (sub_ne_zero.mpr hs2)] at this
    rw [this]; unfold incRep_f; ring
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' hev

/-- `sin(πc) ≠ 0` for `-1 < c < 0`. -/
theorem incRep_sin_ne_zero_strip {c : ℝ} (h0 : -1 < c) (h1 : c < 0) : Real.sin (π*c) ≠ 0 := by
  have : 0 < Real.sin (-(π*c)) := Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])
  rw [Real.sin_neg] at this; linarith

/-- The right-hand side of DLMF 8.6.12 (without residues). -/
def incRep_W (a w : ℂ) : ℂ := -Gamma (1-a)*exp ((1-a)*w+exp w)*upperIncGammaOnLog a w

/-- DLMF 8.6.12 for real `w` and `Re a < 1 + c`, from the Barnes integral for `U` (13.4.17). -/
theorem incRep_base_real {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 0)
    (hac : a.re < 1 + c) (w : ℝ) :
    ∫ y : ℝ, incRep_f a w (c + y*I) = 2*π*incRep_W a w := by
  set x : ℝ := Real.exp w with hx
  have hx0 : 0 < x := Real.exp_pos w
  have hb := kummerU_barnes (a := 1-a) (b := 1-a) (σ := c) hx0 (by simp; linarith)
    (by simp; linarith) hc1
  have hG1 : Gamma (1-a) ≠ 0 := Gamma_ne_zero fun m h => ha m (by linear_combination -h)
  have hxc : ∀ s : ℂ, (x:ℂ)^s = exp (s*w) := fun s => by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx0.ne'), hx, ofReal_exp,
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]; ring_nf
  have hpt : ∀ t : ℝ, Gamma (1-a + c + I*t) * Gamma (1 + (1-a) - (1-a) + c + I*t) *
      Gamma (-(c + I*t)) / (Gamma (1-a) * Gamma (1 + (1-a) - (1-a))) * (x:ℂ)^(-(c + I*t)) * I =
      (-I/Gamma (1-a)) * incRep_f a w (c + t*I) := by
    intro t
    have hr := Complex.Gamma_mul_Gamma_one_sub (-(c + I*t))
    rw [show 1 - -((c:ℂ) + I*t) = 1 + (1-a) - (1-a) + c + I*t by ring,
      show (π:ℂ) * -((c:ℂ) + I*t) = -(π*(c + t*I)) by ring, Complex.sin_neg] at hr
    rw [show 1 + (1-a) - (1-a) = (1:ℂ) by ring, Gamma_one, mul_one, hxc]
    unfold incRep_f
    rw [show (1:ℂ) + c + I*t = 1 + (1-a) - (1-a) + c + I*t by ring,
      show (1-a + c + I*t : ℂ) = c + t*I + 1 - a by ring, show -((c:ℂ) + I*t) = -(c + t*I) by ring]
    rw [show (c:ℂ) + t*I + 1 - a = (c + t*I) + 1 - a by ring] at *
    have hrr : Gamma (1 + (1-a) - (1-a) + c + I*t) * Gamma (-(c + t*I)) =
        -(π / Complex.sin (π*(c + t*I))) := by
      rw [show -((c:ℂ) + t*I) = -(c + I*t) by ring, mul_comm, hr, div_neg]
    rw [div_mul_eq_mul_div, mul_assoc (Gamma _), hrr]
    field_simp
  simp only [hpt] at hb
  rw [integral_const_mul] at hb
  rw [incRep_W, upperIncGammaOnLog_eq_upperIncGamma a (by simp [Real.pi_pos])
    (by simp [Real.pi_pos.le]), upperIncGamma, ← ofReal_exp, ← hx, hb, hxc]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : exp (-(1-a)*w) * exp ((1-a)*w) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have he2 : exp (-(x:ℂ)) * exp (x:ℂ) = 1 := by rw [← Complex.exp_add]; simp
  rw [show (1-a)*(w:ℂ) + (x:ℂ) = (1-a)*w + x by ring, Complex.exp_add]
  field_simp
  have hI : (∫ y : ℝ, incRep_f a w (c + I*y)) = ∫ y : ℝ, incRep_f a w (c + y*I) := by
    congr 1; funext y; ring_nf
  rw [hI]
  have he3 : exp ((1-a)*(w:ℂ)) * exp (-((1-a)*(w:ℂ))) = 1 := by
    rw [← Complex.exp_add]; simp
  set J := ∫ y : ℝ, incRep_f a w (c + y*I)
  linear_combination (-J) * he3 - (J * exp ((1-a)*(w:ℂ)) * exp (-((1-a)*(w:ℂ)))) * he2

/-- The 8.6.12 line integral is holomorphic in `w` on the strip `|Im w| < 3π/2`. -/
theorem incRep_integral_differentiableOn_w (a : ℂ) {c : ℝ} (hs : Real.sin (π*c) ≠ 0)
    (hav : ∀ n : ℕ, a.re - 1 - n ≠ c) :
    DifferentiableOn ℂ (fun w => ∫ y : ℝ, incRep_f a w (c + y*I))
      {w : ℂ | |w.im| < 3*π/2} := by
  have hU : IsOpen {w : ℂ | |w.im| < 3*π/2} :=
    isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  obtain ⟨C, K, hC, h⟩ := incRep_Gamma_bound_pt (x := c+1-a.re) (fun n h => hav n (by linarith))
  have hS : 0 < |Real.sin (π*c)|/2 := by positivity
  refine Complex.differentiableOn_integral_of_locally_dominated hU
    (fun w hw => (incRep_f_continuous hs hav).aestronglyMeasurable)
    (Eventually.of_forall fun y w hw => incRep_f_differentiableAt_w.differentiableWithinAt) ?_
  intro w₀ hw₀
  have hw₀' : |w₀.im| < 3*π/2 := hw₀
  set θ : ℝ := (|w₀.im| + 3*π/2)/2
  have harg : ∀ᶠ w in 𝓝 w₀, |w.im| < θ :=
    (continuous_abs.comp continuous_im).continuousAt.eventually_lt continuousAt_const
      (by show |w₀.im| < θ; simp only [θ]; linarith)
  have hre : ∀ᶠ w in 𝓝 w₀, |w.re - w₀.re| < 1 := by
    have : Continuous fun w : ℂ => |w.re - w₀.re| := by fun_prop
    exact this.continuousAt.eventually_lt continuousAt_const (by simp)
  refine ⟨_, harg.and hre, fun y => C * (1+|a.im|)^K * Real.exp (π*|a.im|/2) *
      (π/(|Real.sin (π*c)|/2)) * Real.exp (|c| * (|w₀.re| + 1)) *
      ((1+|y|)^K * Real.exp (-((3*π/2 - θ)*|y|))),
    (DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (by simp only [θ]; linarith) K).const_mul _,
    Eventually.of_forall fun y w hw => ?_⟩
  obtain ⟨h1, h2⟩ := hw
  refine (incRep_norm_f_le c y hC hS (h _) (Complex.barnesRes_sin_lower_line c y)).trans ?_
  have hx : Real.exp (-(c*w.re)) ≤ Real.exp (|c| * (|w₀.re| + 1)) := by
    apply Real.exp_le_exp.mpr
    have h3 : |w.re| ≤ |w₀.re| + 1 := by
      have := abs_sub_abs_le_abs_sub w.re w₀.re; linarith
    have := neg_abs_le (c*w.re); rw [abs_mul] at this
    nlinarith [abs_nonneg c, abs_nonneg w.re]
  have he : Real.exp (-((3*π/2 - |w.im|)*|y|)) ≤ Real.exp (-((3*π/2 - θ)*|y|)) := by
    apply Real.exp_le_exp.mpr; nlinarith [abs_nonneg y]
  dsimp only
  gcongr

/-- DLMF 8.6.12 in the base regime `Re a < 1 + c` (no crossed poles). -/
theorem incRep_base {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 0)
    (hac : a.re < 1 + c) {w : ℂ} (hw : |w.im| < 3*π/2) :
    ∫ y : ℝ, incRep_f a w (c + y*I) = 2*π*incRep_W a w := by
  have hs := incRep_sin_ne_zero_strip hc0 hc1
  have hav : ∀ n : ℕ, a.re - 1 - n ≠ c := fun n h => by
    linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  set U : Set ℂ := {w : ℂ | |w.im| < 3*π/2}
  have hUo : IsOpen U := isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have hF := (incRep_integral_differentiableOn_w a hs hav).analyticOnNhd hUo
  have hG : AnalyticOnNhd ℂ (fun w => 2*π*incRep_W a w) U := by
    refine DifferentiableOn.analyticOnNhd (fun w _ => ?_) hUo
    unfold incRep_W
    exact (((differentiableAt_const _).mul (by fun_prop)).mul
      (hasDerivAt_upperIncGammaOnLog a w).differentiableAt).const_mul _ |>.differentiableWithinAt
  have h0 : (0:ℂ) ∈ U := by simp [U, Real.pi_pos]
  have hfreq : ∃ᶠ v in 𝓝[≠] (0:ℂ), (∫ y : ℝ, incRep_f a v (c + y*I)) = 2*π*incRep_W a v := by
    have hmap : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[≠] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
      have := continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (s := {(0:ℝ)}ᶜ)
        (t := {(0:ℂ)}ᶜ) (x := 0) (fun x hx h => hx (by simp at h ⊢; exact_mod_cast h))
      simpa using this
    have hev : ∀ᶠ x : ℝ in 𝓝[≠] (0:ℝ), (∫ y : ℝ, incRep_f a (x:ℂ) (c + y*I)) =
        2*π*incRep_W a x := Eventually.of_forall fun x => incRep_base_real ha hc0 hc1 hac x
    exact hmap.frequently hev.frequently
  have hconv : Convex ℝ U := by
    have : U = im ⁻¹' Ioo (-(3*π/2)) (3*π/2) := by
      ext v; simp [U, abs_lt]
    rw [this]; exact (convex_Ioo _ _).linear_preimage imLm
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hconv.isPreconnected h0 hfreq hw

/-- A natural-number ceiling is determined by the naturals below it. -/
theorem incRep_ceil_eq_of_iff {x : ℝ} {k : ℕ} (h : ∀ n : ℕ, (n:ℝ) < x ↔ n < k) : ⌈x⌉₊ = k := by
  apply le_antisymm
  · by_contra h'
    push Not at h'
    have := (h k).mp (Nat.lt_ceil.mp h')
    exact lt_irrefl _ this
  · by_contra h'
    push Not at h'
    exact lt_irrefl _ (Nat.lt_ceil.mpr ((h _).mpr h'))

/-- The residue-corrected 8.6.12 line integral. -/
def incRep_J (a w : ℂ) (c : ℝ) : ℂ :=
  (∫ y : ℝ, incRep_f a w (c + y*I)) + 2*π*∑ n ∈ Finset.range ⌈a.re-1-c⌉₊, incRep_res a w n

/-- Formula under the stated hypotheses: `∀ x ∈ Icc c₁ c₂, Real.sin (π*x) ≠ 0`. -/
theorem incRep_sin_strip_Icc {c₁ c₂ : ℝ} (h1 : -1 < c₁) (h2 : c₂ < 0) :
    ∀ x ∈ Icc c₁ c₂, Real.sin (π*x) ≠ 0 := fun x hx =>
  incRep_sin_ne_zero_strip (by linarith [hx.1]) (by linarith [hx.2])

/-- Identity under the stated parameter and domain assumptions: `incRep_J a w c₁ = incRep_J a w
c₂`. -/
theorem incRep_J_eq_of_le {a w : ℂ} (hw : |w.im| < 3*π/2) {c₁ c₂ : ℝ} (h1 : -1 < c₁)
    (h12 : c₁ ≤ c₂) (h2 : c₂ < 0) (hav₁ : ∀ n : ℕ, a.re - 1 - n ≠ c₁)
    (hav₂ : ∀ n : ℕ, a.re - 1 - n ≠ c₂) : incRep_J a w c₁ = incRep_J a w c₂ := by
  rcases eq_or_lt_of_le h12 with h | h12'
  · rw [h]
  have hsin := incRep_sin_strip_Icc h1 h2
  by_cases hex : ∃ n₀ : ℕ, a.re - 1 - n₀ ∈ Icc c₁ c₂
  · obtain ⟨n₀, hn₀⟩ := hex
    have hp1 : c₁ < a.re - 1 - n₀ := lt_of_le_of_ne hn₀.1 (hav₁ n₀).symm
    have hp2 : a.re - 1 - n₀ < c₂ := lt_of_le_of_ne hn₀.2 (hav₂ n₀)
    have hno : ∀ m : ℕ, m ≠ n₀ → a.re - 1 - m ∉ Icc c₁ c₂ := by
      intro m hm hmI
      rcases lt_or_gt_of_ne hm with h' | h'
      · have : (m:ℝ) + 1 ≤ n₀ := by exact_mod_cast h'
        linarith [hmI.2]
      · have : (n₀:ℝ) + 1 ≤ m := by exact_mod_cast h'
        linarith [hmI.1]
    have hsh := incRep_shift_one hw hsin hp1 hp2 hno
    have hN1 : ⌈a.re - 1 - c₁⌉₊ = n₀ + 1 := incRep_ceil_eq_of_iff fun n => by
      constructor
      · intro hn
        by_contra h'
        have : (n₀:ℝ) + 1 ≤ n := by exact_mod_cast (show n₀ + 1 ≤ n by omega)
        linarith
      · intro hn
        have : (n:ℝ) ≤ n₀ := by exact_mod_cast (show n ≤ n₀ by omega)
        linarith
    have hN2 : ⌈a.re - 1 - c₂⌉₊ = n₀ := incRep_ceil_eq_of_iff fun n => by
      constructor
      · intro hn
        by_contra h'
        have : (n₀:ℝ) ≤ n := by exact_mod_cast (show n₀ ≤ n by omega)
        linarith
      · intro hn
        have : (n:ℝ) + 1 ≤ n₀ := by exact_mod_cast (show n + 1 ≤ n₀ by omega)
        linarith
    unfold incRep_J
    rw [hN1, hN2, Finset.sum_range_succ]
    linear_combination -hsh
  · push Not at hex
    have hN : ⌈a.re - 1 - c₁⌉₊ = ⌈a.re - 1 - c₂⌉₊ := incRep_ceil_eq_of_iff fun n => by
      rw [Nat.lt_ceil]
      constructor
      · intro hn
        by_contra h'
        exact hex n ⟨by linarith, by linarith⟩
      · intro hn; linarith
    unfold incRep_J
    rw [hN, incRep_shift_none hw h12' hsin hex]

/-- Identity under the stated parameter and domain assumptions: `incRep_J a w c₁ = incRep_J a w
c₂`. -/
theorem incRep_J_eq {a w : ℂ} (hw : |w.im| < 3*π/2) {c₁ c₂ : ℝ} (h1 : -1 < c₁) (h1' : c₁ < 0)
    (h2 : -1 < c₂) (h2' : c₂ < 0) (hav₁ : ∀ n : ℕ, a.re - 1 - n ≠ c₁)
    (hav₂ : ∀ n : ℕ, a.re - 1 - n ≠ c₂) : incRep_J a w c₁ = incRep_J a w c₂ := by
  rcases le_total c₁ c₂ with h | h
  · exact incRep_J_eq_of_le hw h1 h h2' hav₁ hav₂
  · exact (incRep_J_eq_of_le hw h2 h h1' hav₂ hav₁).symm

/-- A canonical admissible line in `(-1, 0)`. -/
def incRep_cg (a : ℂ) : ℝ :=
  if Int.fract a.re < 1/2 then (Int.fract a.re - 1)/2 else (Int.fract a.re - 2)/2

/-- Estimate under the stated parameter and domain assumptions: `∃ m : ℤ, -1 < incRep_cg a ∧
incRep_cg a < 0 ∧ (m:ℝ) + 1/4 ≤ a.re - 1 - incRep_cg a ∧ a.re - 1 - incRep_cg a ≤ m + 3/4`. -/
theorem incRep_cg_spec (a : ℂ) : ∃ m : ℤ, -1 < incRep_cg a ∧ incRep_cg a < 0 ∧
    (m:ℝ) + 1/4 ≤ a.re - 1 - incRep_cg a ∧ a.re - 1 - incRep_cg a ≤ m + 3/4 := by
  have h0 := Int.fract_nonneg a.re
  have h1 := Int.fract_lt_one a.re
  have he : a.re = ⌊a.re⌋ + Int.fract a.re := (Int.floor_add_fract a.re).symm
  unfold incRep_cg
  split_ifs with h
  · exact ⟨⌊a.re⌋ - 1, by linarith, by linarith, by push_cast; linarith, by push_cast; linarith⟩
  · push Not at h
    exact ⟨⌊a.re⌋, by linarith, by linarith, by linarith, by linarith⟩

/-- Nonvanishing under the stated hypotheses: `(n:ℝ) ≠ x`. -/
theorem incRep_no_nat {m : ℤ} {x : ℝ} (h1 : (m:ℝ) < x) (h2 : x < m + 1) (n : ℕ) : (n:ℝ) ≠ x := by
  intro h
  rw [← h] at h1 h2
  have : (m:ℤ) < n := by exact_mod_cast h1
  have : (n:ℤ) < m + 1 := by exact_mod_cast h2
  omega

/-- Identity under the stated parameter and domain assumptions: `⌈x⌉₊ = ⌈y⌉₊`. -/
theorem incRep_ceil_near {m : ℤ} {x y : ℝ} (hx1 : (m:ℝ) < x) (hx2 : x < m + 1) (hy1 : (m:ℝ) < y)
    (hy2 : y < m + 1) : ⌈x⌉₊ = ⌈y⌉₊ :=
  incRep_ceil_eq_of_iff fun n => by
    rw [Nat.lt_ceil]
    have key : ∀ u : ℝ, (m:ℝ) < u → u < m + 1 → ((n:ℝ) < u ↔ (n:ℤ) ≤ m) := by
      intro u hu1 hu2
      constructor
      · intro hn
        have : ((n:ℤ):ℝ) < m + 1 := by push_cast; linarith
        exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
      · intro hn
        have : ((n:ℤ):ℝ) ≤ m := by exact_mod_cast hn
        push_cast at this; linarith
    rw [key x hx1 hx2, key y hy1 hy2]

/-- Estimate under the stated parameter and domain assumptions: `∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Icc ((m:ℝ)
+ 1/8) (m + 7/8), δ ≤ |Real.sin (π*x)|`. -/
theorem incRep_sin_lower (m : ℤ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ Icc ((m:ℝ) + 1/8) (m + 7/8), δ ≤ |Real.sin (π*x)| := by
  obtain ⟨x₁, hx₁, hmin⟩ := (isCompact_Icc (a := (m:ℝ) + 1/8) (b := m + 7/8)).exists_isMinOn
    (nonempty_Icc.mpr (by linarith)) ((Real.continuous_sin.comp (continuous_const.mul
      continuous_id)).abs.continuousOn)
  refine ⟨|Real.sin (π*x₁)|, abs_pos.mpr fun h => ?_, fun x hx => hmin hx⟩
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
  have hxk : x₁ = k := by
    have := Real.pi_pos
    have h2 : ((k:ℝ) - x₁) * π = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3 <;> linarith
  rw [hxk] at hx₁
  have h1 : (m:ℝ) < k := by linarith [hx₁.1]
  have h2 : (k:ℝ) < m + 1 := by linarith [hx₁.2]
  have : m < k := by exact_mod_cast h1
  have : k < m + 1 := by exact_mod_cast h2
  omega

/-- Estimate under the stated parameter and domain assumptions: `∃ m : ℤ, (m:ℝ) + 1/8 < a.re - 1 -
incRep_cg a₀ ∧ a.re - 1 - incRep_cg a₀ < m + 7/8 ∧ (m:ℝ) + 1/8 < a₀.re - 1 - incRep_cg a₀ ∧
a₀.re - 1 - incRep_cg a₀ < m + 7/8`. -/
theorem incRep_cg_near {a₀ a : ℂ} (h : |a.re - a₀.re| < 1/8) : ∃ m : ℤ,
    (m:ℝ) + 1/8 < a.re - 1 - incRep_cg a₀ ∧ a.re - 1 - incRep_cg a₀ < m + 7/8 ∧
    (m:ℝ) + 1/8 < a₀.re - 1 - incRep_cg a₀ ∧ a₀.re - 1 - incRep_cg a₀ < m + 7/8 := by
  obtain ⟨m, -, -, h1, h2⟩ := incRep_cg_spec a₀
  have := abs_lt.mp h
  exact ⟨m, by linarith, by linarith, by linarith, by linarith⟩

/-- Nonvanishing under the stated hypotheses: `a.re - 1 - n ≠ incRep_cg a₀`. -/
theorem incRep_cg_avoid {a₀ a : ℂ} (h : |a.re - a₀.re| < 1/8) (n : ℕ) :
    a.re - 1 - n ≠ incRep_cg a₀ := by
  obtain ⟨m, h1, h2, -, -⟩ := incRep_cg_near h
  intro he
  exact incRep_no_nat (m := m) (x := a.re - 1 - incRep_cg a₀) (by linarith) (by linarith) n
    (by linarith)

/-- On the canonical line of `a₀` the 8.6.12 integral is holomorphic in `a` near `a₀`. -/
theorem incRep_integral_differentiableOn_a {w : ℂ} (hw : |w.im| < 3*π/2) (a₀ : ℂ) :
    DifferentiableOn ℂ (fun a => ∫ y : ℝ, incRep_f a w (incRep_cg a₀ + y*I))
      (Metric.ball a₀ (1/8)) := by
  set c₀ := incRep_cg a₀ with hc₀
  obtain ⟨m, hcm1, hcm2, -, -⟩ := incRep_cg_spec a₀
  have hs := incRep_sin_ne_zero_strip hcm1 hcm2
  have hre : ∀ a ∈ Metric.ball a₀ (1/8), |a.re - a₀.re| < 1/8 := fun a ha => by
    have := abs_re_le_norm (a - a₀)
    rw [Metric.mem_ball, dist_eq_norm] at ha
    simp only [sub_re] at this; linarith
  have him : ∀ a ∈ Metric.ball a₀ (1/8), |a.im| ≤ |a₀.im| + 1/8 := fun a ha => by
    have := abs_im_le_norm (a - a₀)
    rw [Metric.mem_ball, dist_eq_norm] at ha
    simp only [sub_im] at this
    have := abs_sub_abs_le_abs_sub a.im a₀.im; linarith
  obtain ⟨m', hm'1, hm'2, hm'3, hm'4⟩ := incRep_cg_near (a₀ := a₀) (a := a₀) (by simp)
  obtain ⟨C, K, hC, h⟩ := incRep_Gamma_bound (|(m':ℝ)| + 2)
  obtain ⟨δ, hδ, hδx⟩ := incRep_sin_lower (-m'-1)
  have hS : 0 < |Real.sin (π*c₀)|/2 := by positivity
  set M : ℝ := |a₀.im| + 1/8
  set b : ℝ := 3*π/2 - |w.im|
  have hb : 0 < b := by simp only [b]; linarith
  set K0 : ℝ := C/δ * (1+M)^K * Real.exp (π*M/2) * (π/(|Real.sin (π*c₀)|/2)) *
    Real.exp (-(c₀*w.re))
  have hbound : ∀ a ∈ Metric.ball a₀ (1/8), ∀ y : ℝ,
      ‖incRep_f a w (c₀ + y*I)‖ ≤ K0 * ((1+|y|)^K * Real.exp (-(b*|y|))) := by
    intro a ha y
    obtain ⟨m, h1, h2, h3, h4⟩ := incRep_cg_near (hre a ha)
    have hmm : m = m' := by
      have e1 : (m:ℝ) < m' + 1 := by linarith
      have e2 : (m':ℝ) < m + 1 := by linarith
      have : m < m' + 1 := by exact_mod_cast e1
      have : m' < m + 1 := by exact_mod_cast e2
      omega
    subst hmm
    have hxI : c₀ + 1 - a.re ∈ Icc (((-m-1 : ℤ):ℝ) + 1/8) (((-m-1 : ℤ):ℝ) + 7/8) := by
      push_cast; constructor <;> linarith
    have hxX : c₀ + 1 - a.re ∈ Icc (-(|(m:ℝ)| + 2)) (|(m:ℝ)| + 2) := by
      have := le_abs_self (m:ℝ); have := neg_abs_le (m:ℝ)
      push_cast at hxI
      constructor <;> linarith [hxI.1, hxI.2]
    have hsx := hδx _ hxI
    have hG : ‖Gamma ((c₀+1-a.re : ℝ) + I*(y - a.im : ℝ))‖ ≤
        C/δ * (1+|y - a.im|)^K * Real.exp (-(π*|y - a.im|)/2) := by
      have h' := (h _ hxX (y - a.im)).1
      have h'' : ‖Gamma ((c₀+1-a.re : ℝ) + I*(y - a.im : ℝ))‖ * δ ≤
          C * (1+|y - a.im|)^K * Real.exp (-(π*|y - a.im|)/2) :=
        le_trans (mul_le_mul_of_nonneg_left hsx (norm_nonneg _)) h'
      rw [← le_div_iff₀ hδ] at h''
      exact h''.trans (le_of_eq (by ring))
    refine (incRep_norm_f_le c₀ y (by positivity) hS hG
      (Complex.barnesRes_sin_lower_line c₀ y)).trans ?_
    have hAim := him a ha
    simp only [K0, b, M]
    gcongr
  have hav : ∀ a ∈ Metric.ball a₀ (1/8), ∀ n : ℕ, a.re - 1 - n ≠ c₀ := fun a ha =>
    incRep_cg_avoid (hre a ha)
  refine Complex.differentiableOn_integral_of_locally_dominated Metric.isOpen_ball
    (fun a ha => (incRep_f_continuous hs (hav a ha)).aestronglyMeasurable)
    (Eventually.of_forall fun y a ha =>
      (incRep_f_differentiableAt_param (incRep_ne_pole (hav a ha) y)).differentiableWithinAt)
    (fun a ha => ⟨_, Metric.isOpen_ball.mem_nhds ha,
      fun y => K0 * ((1+|y|)^K * Real.exp (-(b*|y|))),
      (DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg hb _).const_mul _,
      Eventually.of_forall fun y a' ha' => hbound a' ha' y⟩)

/-- Nonvanishing under the stated hypotheses: `Complex.sin (π*(a-1-n)) ≠ 0`. -/
theorem incRep_sin_res_ne {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) {c : ℝ} (hc : -1 < c) {n : ℕ}
    (hn : c < a.re - 1 - n) : Complex.sin (π*(a-1-n)) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk' : a - 1 - n = k := by
    have := hk; rw [mul_comm (k:ℂ)] at this; exact mul_left_cancel₀ hpi this
  have hre := congrArg re hk'
  simp at hre
  have hk0 : 0 ≤ k := by
    have : (-1:ℝ) < k := by linarith
    have : (-1:ℤ) < k := by exact_mod_cast this
    omega
  apply ha (k.toNat + n)
  have : ((k.toNat : ℕ) : ℂ) = k := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0]
  push_cast
  rw [this]
  linear_combination hk'

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (fun a => incRep_res a w n)
a₀`. -/
theorem incRep_res_differentiableAt (w : ℂ) {a₀ : ℂ} {n : ℕ}
    (hs : Complex.sin (π*(a₀-1-n)) ≠ 0) :
    DifferentiableAt ℂ (fun a => incRep_res a w n) a₀ := by
  have h1 : DifferentiableAt ℂ (fun a : ℂ => Complex.sin (π*(a-1-n))) a₀ :=
    ((differentiableAt_const (π:ℂ)).mul ((differentiableAt_id.sub_const 1).sub_const
      (n:ℂ))).csin
  have h2 : DifferentiableAt ℂ (fun a : ℂ => exp (-(a-1-n)*w)) a₀ :=
    (((differentiableAt_id.sub_const 1).sub_const (n:ℂ)).neg.mul_const w).cexp
  unfold incRep_res
  exact ((differentiableAt_const _).mul ((differentiableAt_const (π:ℂ)).div h1 hs)).mul h2

/-- The canonical-line value of the residue-corrected 8.6.12 integral. -/
def incRep_G (w a : ℂ) : ℂ := incRep_J a w (incRep_cg a)

/-- Identity under the stated parameter and domain assumptions: `incRep_J a w c = incRep_G w a`. -/
theorem incRep_G_eq_J {w : ℂ} (hw : |w.im| < 3*π/2) (a : ℂ) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 0)
    (hav : ∀ n : ℕ, a.re - 1 - n ≠ c) : incRep_J a w c = incRep_G w a := by
  obtain ⟨m, h1, h2, -, -⟩ := incRep_cg_spec a
  exact incRep_J_eq hw hc0 hc1 h1 h2 hav (incRep_cg_avoid (by simp))

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (incRep_G w) a₀`. -/
theorem incRep_G_differentiableAt {w : ℂ} (hw : |w.im| < 3*π/2) {a₀ : ℂ}
    (ha : ∀ n : ℕ, a₀ ≠ n+1) : DifferentiableAt ℂ (incRep_G w) a₀ := by
  obtain ⟨m₀, hc1, hc2, -, -⟩ := incRep_cg_spec a₀
  set H : ℂ → ℂ := fun a => (∫ y : ℝ, incRep_f a w (incRep_cg a₀ + y*I)) +
    2*π*∑ n ∈ Finset.range ⌈a₀.re-1-incRep_cg a₀⌉₊, incRep_res a w n
  have hre : ∀ a ∈ Metric.ball a₀ (1/8), |a.re - a₀.re| < 1/8 := fun a ha' => by
    have := abs_re_le_norm (a - a₀)
    rw [Metric.mem_ball, dist_eq_norm] at ha'
    simp only [sub_re] at this; linarith
  have heq : incRep_G w =ᶠ[𝓝 a₀] H := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1/8))]
      with a ha'
    rw [← incRep_G_eq_J hw a hc1 hc2 (incRep_cg_avoid (hre a ha'))]
    obtain ⟨m, h1, h2, h3, h4⟩ := incRep_cg_near (hre a ha')
    unfold incRep_J
    rw [incRep_ceil_near (m := m) (x := a.re - 1 - incRep_cg a₀) (y := a₀.re - 1 - incRep_cg a₀)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  refine DifferentiableAt.add ?_ ((DifferentiableAt.fun_sum fun n hn =>
    incRep_res_differentiableAt w (incRep_sin_res_ne (n := n) ha hc1 (by
      have := Nat.lt_ceil.mp (Finset.mem_range.mp hn); linarith))).const_mul _)
  exact (incRep_integral_differentiableOn_a hw a₀).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))

/-- Finitely many residues recording indentation past right-hand Gamma poles. -/
def gammaBarnesResidueSum (a w : ℂ) (c : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈a.re-1-c⌉₊, limUnder (𝓝[≠] (a-1-n)) (fun s : ℂ => (s-(a-1-n))*Gamma (s+1-a)*π/sin (π*s)*exp (-s*w))

/-- Formula under the stated hypotheses: `gammaBarnesResidueSum a w c = ∑ n ∈ Finset.range
⌈a.re-1-c⌉₊, incRep_res a w n`. -/
theorem incRep_residueSum_eq {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) (w : ℂ) {c : ℝ} (hc0 : -1 < c) :
    gammaBarnesResidueSum a w c = ∑ n ∈ Finset.range ⌈a.re-1-c⌉₊, incRep_res a w n := by
  unfold gammaBarnesResidueSum
  refine Finset.sum_congr rfl fun n hn => incRep_limUnder_res (incRep_sin_res_ne ha hc0 ?_)
  have := Nat.lt_ceil.mp (Finset.mem_range.mp hn); linarith

/-- Logarithmic-plane formula with explicit separating-contour residues. -/
@[dlmf 8.6.E12]
theorem upperIncGamma_mellinBarnes_continued {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) (w : ℂ) (hw : |w.im| < 3*π/2) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 0) (hca : ∀ n : ℕ, a.re-1-n ≠ c) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; Gamma (s+1-a)*π/sin (π*s)*exp (-s*w)) (2*π*(-Gamma (1-a)*exp ((1-a)*w+exp w)*upperIncGammaOnLog a w-gammaBarnesResidueSum a w c)) := by
  set D : Set ℂ := {a : ℂ | ∀ n : ℕ, a ≠ n+1}
  set E : Set ℂ := {b : ℂ | ∀ n : ℕ, b ≠ 0 - n}
  have hDE : D = (fun a : ℂ => 1 - a) ⁻¹' E := by
    ext b; simp only [D, E, mem_ofPred_eq, mem_preimage]
    exact forall_congr' fun n => not_congr ⟨fun h => by linear_combination -h,
      fun h => by linear_combination -h⟩
  have hDE' : D = (fun b : ℂ => 1 - b) '' E := by
    ext b; constructor
    · intro hb; refine ⟨1 - b, ?_, by ring⟩
      have : b ∈ (fun a : ℂ => 1 - a) ⁻¹' E := hDE ▸ hb
      exact this
    · rintro ⟨e, he, rfl⟩
      rw [hDE]; show 1 - (1 - e) ∈ E; rw [show 1 - (1 - e) = e by ring]; exact he
  have hDo : IsOpen D := hDE ▸ (Complex.barnesRes_isOpen_ne_sub_nat 0).preimage (by fun_prop)
  have hDc : IsPreconnected D :=
    hDE' ▸ (Complex.barnesRes_isPreconnected_ne_sub_nat 0).image _ (by fun_prop)
  have hGa : AnalyticOnNhd ℂ (incRep_G w) D := DifferentiableOn.analyticOnNhd
    (fun b hb => (incRep_G_differentiableAt hw hb).differentiableWithinAt) hDo
  have hWa : AnalyticOnNhd ℂ (fun b => 2*π*incRep_W b w) D := by
    refine DifferentiableOn.analyticOnNhd (fun b hb => ?_) hDo
    have hG : ∀ m : ℕ, 1 - b ≠ -m := fun m h => hb m (by linear_combination -h)
    unfold incRep_W
    exact ((((differentiableAt_Gamma _ hG).comp b (by fun_prop)).neg.mul (by fun_prop)).mul
      (upperIncGammaOnLog_parameter_entire w b)).const_mul _ |>.differentiableWithinAt
  have hpos : ∀ b : ℂ, b.re < 1/2 → incRep_G w b = 2*π*incRep_W b w := by
    intro b hb
    have hbD : ∀ n : ℕ, b ≠ n+1 := fun n h => by
      have := congrArg re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hav : ∀ n : ℕ, b.re - 1 - n ≠ -1/2 := fun n h => by
      linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    rw [← incRep_G_eq_J hw b (by norm_num) (by norm_num) hav]
    unfold incRep_J
    rw [Nat.ceil_eq_zero.mpr (by linarith), Finset.range_zero, Finset.sum_empty, mul_zero,
      add_zero]
    exact incRep_base hbD (by norm_num) (by norm_num) (by linarith) hw
  have h0 : (0:ℂ) ∈ D := fun n h => by
    have := congrArg re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hev : incRep_G w =ᶠ[𝓝 0] fun b => 2*π*incRep_W b w := by
    have ho : IsOpen {b : ℂ | b.re < 1/2} := isOpen_lt continuous_re continuous_const
    filter_upwards [ho.mem_nhds (by simp)] with b hb
    exact hpos b hb
  have hEq := hGa.eqOn_of_preconnected_of_eventuallyEq hWa hDc h0 hev ha
  have hJ := incRep_G_eq_J hw a hc0 hc1 hca
  rw [hEq] at hJ
  have hfun : (fun y : ℝ => let s : ℂ := c+y*I; Gamma (s+1-a)*π/sin (π*s)*exp (-s*w)) =
      fun y : ℝ => incRep_f a w (c + y*I) := rfl
  rw [hfun, incRep_residueSum_eq ha w hc0]
  have hint := incRep_f_integrable hw (incRep_sin_ne_zero_strip hc0 hc1) hca
  have hv : ∫ y : ℝ, incRep_f a w (c + y*I) = 2*π*(-Gamma (1-a)*exp ((1-a)*w+exp w)*
      upperIncGammaOnLog a w - ∑ n ∈ Finset.range ⌈a.re-1-c⌉₊, incRep_res a w n) := by
    unfold incRep_J at hJ; unfold incRep_W at hJ
    linear_combination hJ
  rw [← hv]
  exact incRep_hasIntegralWholeLine hint

end DLMF.Confluent

end
