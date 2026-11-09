/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.VerticalBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import DLMFMathlib.Analysis.Complex.BarnesResidue

/-!
# Uniform Gamma bounds on vertical strips

On a bounded strip, away from the nonpositive integers, Gamma is bounded by a polynomial
in the imaginary part times `exp (-π |Im z| / 2)`. On a strip in the right half-plane the
separation condition is unnecessary. The proof uses the Gamma product and recurrence,
so no asymptotic Stirling formula is needed. These bounds support DLMF §2.5 contour shifts.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology

namespace DLMF.Gamma

/-- Gamma has uniform exponential decay on each closed vertical strip in the right half-plane. -/
theorem exists_norm_Gamma_le_positive_strip {u v : ℝ} (hu : 0 < u) (_huv : u ≤ v) :
    ∃ C > 0, ∃ K : ℕ, ∀ x ∈ Icc u v, ∀ y : ℝ,
      ‖Complex.Gamma (x + I * y)‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  let V := max v 1
  have hV : 0 < V := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcont : ContinuousOn Real.Gamma (Icc u v) := fun x hx =>
    (Real.differentiableAt_Gamma fun n hn => by
      have hx0 : 0 < x := hu.trans_le hx.1
      rw [hn] at hx0
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let A := max M 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hGA := fun x (hx : x ∈ Icc u v) =>
    (le_abs_self (Real.Gamma x)).trans ((hM x hx).trans (le_max_left M 1))
  obtain ⟨C, K, hb⟩ := exists_norm_Gamma_le hV
  have hC : 0 < C := by
    have h := hb 0
    simp only [ofReal_zero, mul_zero, add_zero, abs_zero, zero_div,
      neg_zero, Real.exp_zero, mul_one, one_pow, Gamma_ofReal, norm_real] at h
    exact (Real.Gamma_pos_of_pos hV).trans_le ((le_abs_self _).trans h)
  refine ⟨A / Real.Gamma V * C, by positivity, K, fun x hx y => ?_⟩
  have hx0 : 0 < x := hu.trans_le hx.1
  have hxV : x ≤ V := hx.2.trans (le_max_left _ _)
  have hPV : 0 < gammaVertProd V y := lt_of_lt_of_le zero_lt_one (one_le_gammaVertProd _ _)
  have hprod := gammaVertProd_anti hx0 hxV y
  have hratio : ‖Complex.Gamma (x + I * y)‖ ≤
      A / Real.Gamma V * ‖Complex.Gamma (V + I * y)‖ := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
    rw [mul_pow, div_pow, norm_Gamma_sq_eq hx0, norm_Gamma_sq_eq hV]
    calc Real.Gamma x ^ 2 / gammaVertProd x y ≤ A ^ 2 / gammaVertProd V y :=
          div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (Real.Gamma_pos_of_pos hx0).le
            (hGA x hx) 2) hPV hprod
      _ = _ := by field_simp
  calc ‖Complex.Gamma (x + I * y)‖ ≤
        A / Real.Gamma V * ‖Complex.Gamma (V + I * y)‖ := hratio
    _ ≤ A / Real.Gamma V * (C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) :=
      mul_le_mul_of_nonneg_left (hb y) (by positivity)
    _ = _ := by ring

/-- Uniform Gamma decay on a bounded strip whose points stay a fixed distance from every pole. -/
theorem exists_norm_Gamma_le_strip_of_separated {u v η : ℝ} (huv : u ≤ v) (hη : 0 < η) :
    ∃ C > 0, ∃ K : ℕ, ∀ x ∈ Icc u v, ∀ y : ℝ,
      (∀ n : ℕ, η ≤ ‖(x : ℂ) + I * y + n‖) →
      ‖Complex.Gamma (x + I * y)‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-u)
  have huN : 0 < u + N := by linarith
  obtain ⟨C, hC, K, hb⟩ := exists_norm_Gamma_le_positive_strip huN (by linarith : u + N ≤ v + N)
  refine ⟨C / η ^ N, by positivity, K, fun x hx y hsep => ?_⟩
  let z : ℂ := x + I * y
  have hpoles : ∀ n : ℕ, z ≠ -n := by
    intro n hn
    have h := hsep n
    change η ≤ ‖z + n‖ at h
    rw [hn, neg_add_cancel, norm_zero] at h
    linarith
  have hprod : ∀ n : ℕ, η ^ n ≤ ‖(ascPochhammer ℂ n).eval z‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ascPochhammer_succ_eval, norm_mul, pow_succ]
      exact mul_le_mul ih (hsep n) hη.le (norm_nonneg _)
  have hshift : Complex.Gamma (z + N) =
      (ascPochhammer ℂ N).eval z * Complex.Gamma z :=
    (div_eq_iff (Gamma_ne_zero hpoles)).mp (Gamma_add_nat_div_Gamma_eq z hpoles)
  have hbound := hb (x + N) ⟨by linarith [hx.1], by linarith [hx.2]⟩ y
  have hzshift : ((x + (N : ℝ) : ℝ) : ℂ) + I * y = z + N := by dsimp [z]; push_cast; ring
  rw [hzshift, hshift, norm_mul] at hbound
  have hle := (mul_le_mul_of_nonneg_right (hprod N) (norm_nonneg (Complex.Gamma z))).trans hbound
  calc ‖Complex.Gamma z‖ ≤
        (C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) / η ^ N :=
          (le_div_iff₀ (pow_pos hη N)).mpr (by simpa only [mul_comm] using hle)
    _ = _ := by ring

/-- Above height one, a bounded vertical strip is automatically separated from the Gamma poles. -/
theorem exists_norm_Gamma_le_strip_of_one_le_abs_im {u v : ℝ} (huv : u ≤ v) :
    ∃ C > 0, ∃ K : ℕ, ∀ x ∈ Icc u v, ∀ y : ℝ, 1 ≤ |y| →
      ‖Complex.Gamma (x + I * y)‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  obtain ⟨C, hC, K, hb⟩ := exists_norm_Gamma_le_strip_of_separated huv zero_lt_one
  refine ⟨C, hC, K, fun x hx y hy => hb x hx y fun n => ?_⟩
  exact hy.trans (by simpa using (abs_im_le_norm ((x : ℂ) + I * y + n)))

/-- A vertical line through a real point other than a Gamma pole is uniformly separated
from every Gamma pole, so the exponential Gamma bound holds at all heights. -/
theorem exists_norm_Gamma_le_line {x : ℝ} (hx : ∀ n : ℕ, x ≠ -n) :
    ∃ C > 0, ∃ K : ℕ, ∀ y : ℝ,
      ‖Complex.Gamma (x + I * y)‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  have hx' : (x : ℂ) ∈ {z : ℂ | ∀ n : ℕ, z ≠ 0 - n} := by
    intro n hn
    apply hx n
    have h := congrArg Complex.re hn
    simpa only [ofReal_re, sub_re, zero_re, natCast_re, zero_sub, neg_re] using h
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp (BarnesResidue.isOpen_ne_sub_nat 0) _ hx'
  have hsep : ∀ n : ℕ, η ≤ |x + n| := by
    intro n
    by_contra! hn
    have hmem : -(n : ℂ) ∈ Metric.ball (x : ℂ) η := by
      rw [Metric.mem_ball, dist_eq_norm,
        show -(n : ℂ) - x = -((x + n : ℝ) : ℂ) by push_cast; ring,
        norm_neg, Complex.norm_real, Real.norm_eq_abs]
      exact hn
    exact hball hmem n (by simp)
  obtain ⟨C, hC, K, hb⟩ := exists_norm_Gamma_le_strip_of_separated (u := x) (v := x) le_rfl hη
  refine ⟨C, hC, K, fun y => hb x ⟨le_rfl, le_rfl⟩ y fun n => ?_⟩
  exact (hsep n).trans (by simpa using (abs_re_le_norm ((x : ℂ) + I * y + n)))

/-- Gamma on a line avoiding its poles remains integrable after multiplication by
`exp (θ |y|)` for every `θ < π/2`. -/
theorem integrable_Gamma_vertical_mul_exp {x θ : ℝ} (hx : ∀ n : ℕ, x ≠ -n)
    (hθ : θ < π / 2) :
    Integrable (fun y : ℝ => Complex.Gamma (x + y * I) * (Real.exp (θ * |y|) : ℂ)) := by
  obtain ⟨C, hC, K, hb⟩ := exists_norm_Gamma_le_line hx
  have hcont : Continuous (fun y : ℝ => Complex.Gamma (x + y * I)) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    refine (Complex.continuousAt_Gamma _ fun n hn => hx n ?_).comp (by fun_prop)
    have h := congrArg Complex.re hn
    simpa only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
      zero_mul, sub_zero, add_zero, neg_re, natCast_re] using h
  refine ((Real.integrable_one_add_abs_pow_mul_exp_neg (sub_pos.mpr hθ) K).const_mul C).mono'
    (hcont.aestronglyMeasurable.mul (by fun_prop)) (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  calc ‖Complex.Gamma (x + y * I)‖ * Real.exp (θ * |y|) ≤
        (C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) * Real.exp (θ * |y|) :=
          mul_le_mul_of_nonneg_right (by simpa only [mul_comm I] using hb y)
            (Real.exp_pos _).le
    _ = _ := by
      have he : Real.exp (-(π * |y|) / 2) * Real.exp (θ * |y|) =
          Real.exp (-((π / 2 - θ) * |y|)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc _ = C * (1 + |y|) ^ K *
          (Real.exp (-(π * |y|) / 2) * Real.exp (θ * |y|)) := by ring
        _ = _ := by rw [he]; ring

/-- Gamma is vertically integrable on every line that does not contain one of its poles. -/
theorem verticalIntegrable_Gamma_of_ne_neg_nat {x : ℝ} (hx : ∀ n : ℕ, x ≠ -n) :
    VerticalIntegrable Complex.Gamma x := by
  simpa only [VerticalIntegrable, zero_mul, Real.exp_zero, ofReal_one, mul_one] using
    integrable_Gamma_vertical_mul_exp (θ := 0) hx (by positivity)

/-- Multiplication by a function uniformly bounded at large height preserves uniform
vertical decay of `Γ(1-z)` on a bounded strip. -/
theorem tendsto_iSup_norm_Gamma_one_sub_mul {F : ℂ → ℂ} {a b B Y : ℝ}
    (hab : a ≤ b) (hB : 0 ≤ B)
    (hb : ∀ z : ℂ, z.re ∈ Icc a b → Y ≤ |z.im| → ‖F z‖ ≤ B) :
    Tendsto (fun y : ℝ => ⨆ σ : Icc a b,
      ‖Complex.Gamma (1 - (σ + y * I)) * F (σ + y * I)‖) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, hC, K, hΓ⟩ := exists_norm_Gamma_le_strip_of_one_le_abs_im
    (u := 1 - b) (v := 1 - a) (by linarith)
  letI : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  have ht : Tendsto (fun y : ℝ => 1 + |y|) (cocompact ℝ) atTop := by
    have hn : Tendsto (fun y : ℝ => ‖y‖) (cocompact ℝ) atTop :=
      tendsto_norm_cocompact_atTop
    simpa only [Real.norm_eq_abs] using tendsto_atTop_add_const_left _ 1 hn
  have hlim := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (K : ℝ) (π / 2)
    (by positivity)).comp ht).const_mul (B * C * Real.exp (π / 2))
  simp only [mul_zero] at hlim
  have hlim' : Tendsto (fun y : ℝ => B * C * (1 + |y|) ^ K *
      Real.exp (-(π * |y|) / 2)) (cocompact ℝ) (𝓝 0) := by
    refine hlim.congr fun y => ?_
    dsimp only [Function.comp_def]
    rw [Real.rpow_natCast]
    simp only [neg_mul]
    have he : Real.exp (π / 2) * Real.exp (-(π / 2 * (1 + |y|))) =
        Real.exp (-(π * |y|) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc B * C * Real.exp (π / 2) *
        ((1 + |y|) ^ K * Real.exp (-(π / 2 * (1 + |y|)))) =
        B * C * (1 + |y|) ^ K *
          (Real.exp (π / 2) * Real.exp (-(π / 2 * (1 + |y|)))) := by ring
      _ = _ := by rw [he]
  refine squeeze_zero' ?_ ?_ hlim'
  · exact Eventually.of_forall fun y => Real.iSup_nonneg fun _ => norm_nonneg _
  · filter_upwards [ht.eventually_ge_atTop (max Y 1 + 1)] with y hy
    have hY : Y ≤ |y| := by linarith [le_max_left Y 1]
    have hy1 : 1 ≤ |y| := by linarith [le_max_right Y 1]
    apply ciSup_le
    intro σ
    have he : 1 - ((σ : ℂ) + y * I) = ((1 - (σ : ℝ) : ℝ) : ℂ) + I * (-y : ℝ) := by
      push_cast
      ring
    rw [norm_mul, he]
    have hσ : (1 - (σ : ℝ)) ∈ Icc (1 - b) (1 - a) := by
      constructor <;> linarith [σ.property.1, σ.property.2]
    have hG := hΓ _ hσ (-y) (by simpa using hy1)
    have hF := hb ((σ : ℂ) + y * I) (by simpa using σ.property) (by simpa using hY)
    calc ‖Complex.Gamma (((1 - (σ : ℝ) : ℝ) : ℂ) + I * (-y : ℝ))‖ *
          ‖F ((σ : ℂ) + y * I)‖ ≤
        (C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) * B := by
          apply mul_le_mul (by simpa only [abs_neg] using hG) hF
            (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- A continuous factor bounded at large height preserves vertical integrability of
`Γ(1-z)` on every line avoiding the positive integers. -/
theorem verticalIntegrable_Gamma_one_sub_mul {F : ℂ → ℂ} {σ B Y : ℝ}
    (hσ : ∀ n : ℕ, 1 - σ ≠ -n)
    (hF : Continuous fun y : ℝ => F (σ + y * I))
    (hb : ∀ y : ℝ, Y ≤ |y| → ‖F (σ + y * I)‖ ≤ B) :
    VerticalIntegrable (fun z => Complex.Gamma (1 - z) * F z) σ := by
  let R := max Y 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hF.continuousOn
  have hbound (y : ℝ) : ‖F (σ + y * I)‖ ≤ max B M := by
    by_cases hy : Y ≤ |y|
    · exact (hb y hy).trans (le_max_left _ _)
    · have hyR : |y| ≤ R := (not_le.mp hy).le.trans (le_max_left _ _)
      exact (hM y (abs_le.mp hyR)).trans (le_max_right _ _)
  have hi : Integrable (fun y : ℝ => Complex.Gamma (1 - (σ + y * I))) := by
    have h := (verticalIntegrable_Gamma_of_ne_neg_nat hσ).comp_neg
    convert h using 1
    funext y
    congr 1
    push_cast
    ring
  apply (hi.norm.const_mul (max B M)).mono'
    (hi.aestronglyMeasurable.mul hF.aestronglyMeasurable)
  filter_upwards [] with y
  simp only [Pi.mul_apply, norm_mul]
  exact (mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _)).trans_eq (by ring)

/-- On a line avoiding the positive integers, continuity of `Γ(1-z) F(z)` implies
continuity of `F`, since Gamma is continuous and nonzero there. -/
theorem continuous_vertical_of_Gamma_one_sub_mul {F : ℂ → ℂ} {σ : ℝ}
    (hσ : ∀ n : ℕ, 1 - σ ≠ -n)
    (hF : Continuous fun y : ℝ => Complex.Gamma (1 - (σ + y * I)) * F (σ + y * I)) :
    Continuous fun y : ℝ => F (σ + y * I) := by
  have hp (y : ℝ) (n : ℕ) : 1 - ((σ : ℂ) + y * I) ≠ -n := by
    intro h
    apply hσ n
    have he := congrArg Complex.re h
    simpa using he
  have hΓ : Continuous fun y : ℝ => Complex.Gamma (1 - (σ + y * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact ContinuousAt.comp (g := Complex.Gamma)
      (f := fun y : ℝ => 1 - ((σ : ℂ) + y * I)) (continuousAt_Gamma _ (hp y)) (by fun_prop)
  have hn (y : ℝ) : Complex.Gamma (1 - (σ + y * I)) ≠ 0 := Gamma_ne_zero (hp y)
  apply (hF.div hΓ hn).congr
  intro y
  change (Complex.Gamma (1 - (σ + y * I)) * F (σ + y * I)) /
    Complex.Gamma (1 - (σ + y * I)) = F (σ + y * I)
  field_simp [hn y]

end DLMF.Gamma
