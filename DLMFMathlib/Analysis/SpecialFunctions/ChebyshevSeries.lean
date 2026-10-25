/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Complex Chebyshev series of entire functions

Complex-valued coefficient decay and pointwise reconstruction, generalized from
`DLMF/OrthogonalPolynomials/ChebyshevExpansion.lean`. The proofs use Mathlib's
Fourier series on `AddCircle` and the rectangular Cauchy theorem.
-/

@[expose] public noncomputable section
open Complex Filter MeasureTheory Set Polynomial
open scoped Real Topology Nat
namespace Polynomial.Chebyshev

/-- Complex Chebyshev coefficients with the customary doubled zeroth coefficient. -/
def complexCoeff (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  2 / π * ∫ θ in (0 : ℝ)..π, f (Real.cos θ) * Real.cos (n * θ)

/-- `θ ↦ f(cos θ)` as a continuous function on the circle `ℝ/2πℤ`. -/
def complexCircleFun {f : ℝ → ℂ} (hf : ContinuousOn f (Icc (-1) 1)) :
    C(AddCircle (2 * π), ℂ) where
  toFun := (show Function.Periodic (fun θ : ℝ => f (Real.cos θ)) (2 * π) from
    fun θ => by simp [Real.cos_add_two_pi]).lift
  continuous_toFun := by
    refine continuous_coinduced_dom.mpr ?_
    have hc : Continuous fun θ : ℝ => f (Real.cos θ) :=
      hf.comp_continuous Real.continuous_cos fun θ =>
        ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    exact hc

lemma complexCircleFun_coe {f : ℝ → ℂ} (hf : ContinuousOn f (Icc (-1) 1)) (θ : ℝ) :
    complexCircleFun hf (θ : AddCircle (2 * π)) = f (Real.cos θ) := rfl

local instance instTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The full-period integral `∫₀^{2π} e^{-inθ} f(cos θ) dθ = π c_{|n|}`. -/
lemma integral_exp_mul_comp_cos_complex {f : ℝ → ℂ} (hcf : Continuous fun x : ℝ => f (Real.cos x))
    (n : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), Complex.exp (-(I * n * x)) * f (Real.cos x) =
      π * complexCoeff f n.natAbs := by
  set h : ℝ → ℂ := fun x => Complex.exp (-(I * n * x)) * f (Real.cos x) with hh
  have hhc : Continuous h := by
    rw [hh]; exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(I * n * x))).mul
      hcf
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := π)
    (c := 2 * π) (hhc.intervalIntegrable _ _) (hhc.intervalIntegrable _ _)
  have hrefl := intervalIntegral.integral_comp_sub_left h (a := 0) (b := π) (2 * π)
  rw [show 2 * π - π = π by ring, sub_zero] at hrefl
  have hsym : ∫ x in (0 : ℝ)..π, h (2 * π - x) =
      ∫ x in (0 : ℝ)..π, Complex.exp (I * n * x) * f (Real.cos x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hh, Real.cos_two_pi_sub]
    congr 1
    rw [show -(I * n * ((2 * π - x : ℝ) : ℂ)) = I * n * x + (-n : ℤ) * (2 * π * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hsum : ∫ x in (0 : ℝ)..(2 * π), h x =
      2 * ∫ x in (0 : ℝ)..π, (Real.cos (n.natAbs * x) : ℂ) * f (Real.cos x) := by
    have hg : Continuous fun x : ℝ => Complex.exp (I * n * x) * f (Real.cos x) :=
      (by fun_prop : Continuous fun x : ℝ => Complex.exp (I * n * x)).mul
        hcf
    rw [← hsplit, ← hrefl, hsym, ← intervalIntegral.integral_add (hhc.intervalIntegrable 0 π)
      (hg.intervalIntegrable 0 π), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le Real.pi_pos.le] at hx; exact hx.1
    have hcos : Real.cos (n.natAbs * x) = Real.cos (n * x) := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← Real.cos_abs ((n : ℝ) * x), abs_mul, abs_of_nonneg hx0]
    simp only [hh]
    rw [hcos, Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  rw [hsum, complexCoeff]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have heq : (∫ x in (0 : ℝ)..π, (Real.cos (n.natAbs * x) : ℂ) * f (Real.cos x)) =
      ∫ θ in (0 : ℝ)..π, f (Real.cos θ) * Real.cos (n.natAbs * θ) :=
    intervalIntegral.integral_congr fun x _ => by ring
  rw [heq]
  push_cast
  field_simp

/-- The Fourier coefficients of `θ ↦ f(cos θ)` are half the Chebyshev coefficients. -/
lemma fourierCoeff_complexCircleFun {f : ℝ → ℂ} (hf : ContinuousOn f (Icc (-1) 1)) (n : ℤ) :
    fourierCoeff (complexCircleFun hf) n = complexCoeff f n.natAbs / 2 := by
  rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
  have hcf : Continuous fun x : ℝ => f (Real.cos x) :=
    hf.comp_continuous Real.continuous_cos fun θ => ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hint : ∫ x in (0 : ℝ)..(2 * π), fourier (-n) (x : AddCircle (2 * π)) •
      complexCircleFun hf x = ∫ x in (0 : ℝ)..(2 * π),
        Complex.exp (-(I * n * x)) * f (Real.cos x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [fourier_coe_apply, complexCircleFun_coe, smul_eq_mul]
    congr 1
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    congr 1
    push_cast
    field_simp
  rw [hint, integral_exp_mul_comp_cos_complex hcf, Complex.real_smul]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- **Convergence of Chebyshev series** (Temme (6.65)–(6.66)): if `f` is continuous on `[-1,1]`
and its Chebyshev coefficients are absolutely summable, then
`f(x) = c₀/2 + ∑_{n≥1} cₙ Tₙ(x)` for every `x ∈ [-1,1]`. -/
theorem hasSum_complexCoeff_mul_T {f : ℝ → ℂ} (hf : ContinuousOn f (Icc (-1) 1))
    (hs : Summable fun n => ‖complexCoeff f n‖) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    HasSum (fun n : ℕ => (if n = 0 then 1 / 2 else 1) * complexCoeff f n *
      (Chebyshev.T ℂ n).eval (x : ℂ)) (f x) := by
  set g := complexCircleFun hf with hg
  set c := complexCoeff f with hc
  have hsC : Summable fun n : ℕ => c n / 2 :=
    (Summable.of_norm hs).div_const 2
  have hsum : Summable (fourierCoeff g) := by
    refine Summable.of_nat_of_neg ?_ ?_
    · refine hsC.congr fun n => ?_
      rw [hg, fourierCoeff_complexCircleFun]; simp [hc]
    · refine hsC.congr fun n => ?_
      rw [hg, fourierCoeff_complexCircleFun]; simp [hc]
  set θ := Real.arccos x with hθ
  have hxθ : Real.cos θ = x := Real.cos_arccos hx.1 hx.2
  have hp := (has_pointwise_sum_fourier_series_of_summable hsum (θ : AddCircle (2 * π))).nat_add_neg
  have hterm : ∀ n : ℕ, fourierCoeff g n • fourier (n : ℤ) (θ : AddCircle (2 * π)) +
      fourierCoeff g (-(n : ℤ)) • fourier (-(n : ℤ)) (θ : AddCircle (2 * π)) =
      c n * (Chebyshev.T ℂ n).eval (x : ℂ) := by
    intro n
    rw [hg, fourierCoeff_complexCircleFun, fourierCoeff_complexCircleFun, fourier_coe_apply,
      fourier_coe_apply, ← hxθ, Complex.ofReal_cos, Chebyshev.T_complex_cos]
    simp only [Int.natAbs_neg, Int.natAbs_natCast, smul_eq_mul]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [show 2 * (π : ℂ) * I * ((n : ℤ) : ℂ) * (θ : ℂ) / (2 * π : ℝ) = (n * θ : ℝ) * I by
        push_cast; field_simp,
      show 2 * (π : ℂ) * I * ((-(n : ℤ) : ℤ) : ℂ) * (θ : ℂ) / (2 * π : ℝ) =
        ((-(n * θ) : ℝ) : ℂ) * I by push_cast; field_simp]
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, hc]
    push_cast
    ring
  have hR : HasSum (fun n : ℕ => c n * (Chebyshev.T ℂ n).eval (x : ℂ)) (f x + c 0 / 2) := by
    convert hp using 1
    · funext n; exact (hterm n).symm
    · rw [hg, complexCircleFun_coe, hxθ, fourierCoeff_complexCircleFun]
      simp [hc]
  have h := hR.sub (hasSum_ite_eq 0 (c 0 / 2))
  rw [add_sub_cancel_right] at h
  refine h.congr_fun fun n => ?_
  split_ifs with hn
  · subst hn; simp [Chebyshev.T_zero]; ring
  · simp


/-- **Geometric decay of Chebyshev coefficients** (Temme §6.9.2; Rivlin): if `f` extends to a
function `F` analytic on the closed Bernstein ellipse `E_ρ = cos({|Im w| ≤ s})`, `ρ = e^s`, with
`|F| ≤ M` there, then `|cₙ| ≤ 2M ρ^{-n}`. -/
theorem norm_complexCoeff_le {f : ℝ → ℂ} {F : ℂ → ℂ} {s M : ℝ} (hs : 0 ≤ s)
    (hF : ∀ w : ℂ, |w.im| ≤ s → DifferentiableAt ℂ F (Complex.cos w))
    (hM : ∀ w : ℂ, |w.im| ≤ s → ‖F (Complex.cos w)‖ ≤ M)
    (hFf : ∀ x ∈ Icc (-1 : ℝ) 1, F x = f x) (n : ℕ) :
    ‖complexCoeff f n‖ ≤ 2 * M * Real.exp (-(n * s)) := by
  set G : ℂ → ℂ := fun w => F (Complex.cos w) * Complex.exp (-(I * n * w)) with hG
  have hcosmem : ∀ x : ℝ, Real.cos x ∈ Icc (-1 : ℝ) 1 :=
    fun x => ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
  have hreal : ∀ x : ℝ, G x = Complex.exp (-(I * n * x)) * f (Real.cos x) := by
    intro x
    simp only [hG]
    rw [← Complex.ofReal_cos, hFf _ (hcosmem x)]
    ring
  have hGd : ∀ w : ℂ, |w.im| ≤ s → DifferentiableAt ℂ G w := fun w hw =>
    ((hF w hw).comp w Complex.differentiable_cos.differentiableAt).mul
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-(I * n * w))) w)
  have hcf : Continuous fun x : ℝ => f (Real.cos x) := by
    have hc : Continuous fun x : ℝ => F (Complex.cos x) :=
      continuous_iff_continuousAt.mpr fun x =>
        (((hF x (by simp [hs])).continuousAt.comp Complex.continuous_cos.continuousAt).comp
          Complex.continuous_ofReal.continuousAt)
    refine hc.congr fun x => ?_
    rw [← Complex.ofReal_cos, hFf _ (hcosmem x)]
  -- Cauchy's theorem on the rectangle `[0, 2π] × [-s, 0]`
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
    (⟨0, -s⟩ : ℂ) (⟨2 * π, 0⟩ : ℂ) (fun w hw => (hGd w (by
      rw [mem_reProdIm] at hw
      have h2 := hw.2
      rw [uIcc_of_le (by simp; linarith)] at h2
      simp only at h2
      rw [abs_le]; constructor <;> linarith [h2.1, h2.2])).differentiableWithinAt)
  simp only at hrect
  have hper : ∀ y : ℝ, G ((2 * π : ℝ) + y * I) = G ((0 : ℝ) + y * I) := by
    intro y
    simp only [hG]
    push_cast
    rw [show 2 * (π : ℂ) + y * I = y * I + 2 * π by ring, Complex.cos_add_two_pi, zero_add,
      show -(I * n * (y * I + 2 * π)) = -(I * n * (y * I)) + (-n : ℤ) * (2 * π * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [hper, add_zero, Complex.ofReal_zero, zero_mul] at hrect
  rw [add_sub_cancel_right, sub_eq_zero] at hrect
  have hB : ∫ x : ℝ in (0 : ℝ)..(2 * π), G x = π * complexCoeff f n := by
    rw [intervalIntegral.integral_congr fun x _ => hreal x]
    exact_mod_cast integral_exp_mul_comp_cos_complex hcf n
  rw [hB] at hrect
  have hbound : ∀ x ∈ uIoc (0 : ℝ) (2 * π), ‖G (x + ((-s : ℝ) : ℂ) * I)‖ ≤ M * Real.exp (-(n * s)) := by
    intro x _
    have him : |((x : ℂ) + ((-s : ℝ) : ℂ) * I).im| ≤ s := by simp [abs_of_nonneg hs]
    simp only [hG]
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul (hM _ him) (le_of_eq ?_) (by positivity)
      ((norm_nonneg _).trans (hM _ him))
    congr 1
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.natCast_re, Complex.natCast_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hrect, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    sub_zero, abs_of_pos Real.two_pi_pos] at hI
  have hπ := Real.pi_pos
  nlinarith [norm_nonneg (complexCoeff f n), Real.exp_pos (-(n * s))]

/-- The cosine of a point in a fixed horizontal strip lies in a fixed disk. -/
lemma norm_cos_le_exp_one {w : ℂ} (hw : |w.im| ≤ 1) : ‖Complex.cos w‖ ≤ Real.exp 1 := by
  have hp : ‖Complex.exp (w * I)‖ ≤ Real.exp 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using (neg_le_neg (abs_le.mp hw).1)
  have hm : ‖Complex.exp (-w * I)‖ ≤ Real.exp 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using (abs_le.mp hw).2
  have hb := norm_add_le (Complex.exp (w * I)) (Complex.exp (-w * I))
  rw [← Complex.two_cos, norm_mul, Complex.norm_two] at hb
  linarith

/-- Every entire complex-valued function has an absolutely summable Chebyshev
series on the real interval `[-1,1]`, including both endpoints. -/
theorem exists_summable_series_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    ∃ c : ℕ → ℂ, Summable c ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      HasSum (fun n : ℕ => c n * (T ℂ (n : ℤ)).eval (x : ℂ)) (F x) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (Real.exp 1)).exists_bound_of_continuousOn
    hF.continuous.continuousOn
  let f : ℝ → ℂ := fun x => F x
  have hfc : ContinuousOn f (Icc (-1) 1) :=
    (hF.continuous.comp Complex.continuous_ofReal).continuousOn
  have hbound (w : ℂ) (hw : |w.im| ≤ 1) : ‖F (Complex.cos w)‖ ≤ M :=
    hM _ (by simpa using norm_cos_le_exp_one hw)
  have hdecay (n : ℕ) : ‖complexCoeff f n‖ ≤ 2 * M * Real.exp (-1) ^ n := by
    have h := norm_complexCoeff_le (s := 1) (M := M) (by norm_num)
      (fun w _ => hF _) hbound (fun _ _ => rfl) n
    convert h using 1
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  have hs : Summable fun n => ‖complexCoeff f n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdecay
      ((summable_geometric_of_lt_one (Real.exp_pos (-1)).le
        (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left (2 * M))
  let c : ℕ → ℂ := fun n => (if n = 0 then 1 / 2 else 1) * complexCoeff f n
  have hc : Summable c := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs
    dsimp [c]
    split_ifs
    · rw [norm_mul]
      norm_num
      exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
    · simp
  exact ⟨c, hc, fun x hx => hasSum_complexCoeff_mul_T hfc hs hx⟩

end Polynomial.Chebyshev
