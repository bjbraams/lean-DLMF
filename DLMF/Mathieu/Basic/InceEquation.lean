/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Hill.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Differential equations of Ince polynomials and paraboloidal wave functions

The canonical Ince polynomials solve Ince's equation at their chosen eigenvalues, including
the zero fallback. Multiplication by `exp(-ξ cos(2z)/4)` transforms Ince's equation into the
Whittaker–Hill equation (DLMF 28.31.2). This gives the defining differential equations of the
paraboloidal wave functions (28.31.18).

## Main results

* `isInceSolution_inceC`, `isInceSolution_inceS`: defining equations of the Ince polynomials.
* `isWhittakerHillSolution_iff_isInceSolution`: the gauge transformation (28.31.2).
* `paraboloidal_isWhittakerHillSolution`: the paraboloidal wave equation (28.31.18).
-/

public noncomputable section

open Complex

namespace DLMF.Mathieu

/-- The zero function solves Ince's homogeneous differential equation. -/
lemma isInceSolution_zero (ξ η p : ℂ) : IsInceSolution ξ η p (fun _ => 0) := by
  refine ⟨differentiable_const 0, ?_⟩
  intro z
  have hd : deriv (fun _ : ℂ => (0 : ℂ)) = fun _ => 0 := by
    funext w
    exact deriv_const w 0
  rw [hd]
  simpa only [mul_zero, neg_zero, sub_zero] using hasDerivAt_const z (0 : ℂ)

/-- The canonical Ince cosine polynomial solves Ince's equation at its chosen eigenvalue. -/
lemma isInceSolution_inceC (p m : ℕ) (ξ : ℝ) :
    IsInceSolution ξ (inceA p m ξ) p (fun z => inceC p m z ξ) := by
  classical
  unfold inceC
  split_ifs with h
  · exact h.choose_spec.1.2.1
  · exact isInceSolution_zero _ _ _

/-- The canonical Ince sine polynomial solves Ince's equation at its chosen eigenvalue. -/
lemma isInceSolution_inceS (p m : ℕ) (ξ : ℝ) :
    IsInceSolution ξ (inceB p m ξ) p (fun z => inceS p m z ξ) := by
  classical
  unfold inceS
  split_ifs with h
  · exact h.choose_spec.1.2.1
  · exact isInceSolution_zero _ _ _

/-- `cos 4z = 1 - 2 sin² 2z`. -/
private lemma cos_four_mul_eq_one_sub_two_mul_sin_sq (z : ℂ) : Complex.cos (4 * z) = 1 - 2 *
    Complex.sin (2 * z) ^ 2 := by
  have harg : (4 : ℂ) * z = 2 * (2 * z) := by ring
  rw [harg, Complex.cos_two_mul]
  have := Complex.sin_sq_add_cos_sq (2 * z)
  linear_combination (2 : ℂ) * this

/-- The derivative of `-ξ cos(2z)/4`. -/
private lemma hasDerivAt_neg_mul_cos_two_mul_div_four (ξ z : ℂ) :
    HasDerivAt (fun z => -(ξ * Complex.cos (2 * z)) / 4) (ξ * Complex.sin (2 * z) / 2) z := by
  have h2 : HasDerivAt (fun z : ℂ => 2 * z) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have := ((h2.ccos).const_mul ξ).neg.div_const 4
  convert this using 1; ring

/-- The derivative of `ξ sin(2z)/2`. -/
private lemma hasDerivAt_mul_sin_two_mul_div_two (ξ z : ℂ) :
    HasDerivAt (fun z => ξ * Complex.sin (2 * z) / 2) (ξ * Complex.cos (2 * z)) z := by
  have h2 : HasDerivAt (fun z : ℂ => 2 * z) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have := ((h2.csin).const_mul ξ).div_const 2
  convert this using 1; ring

/-- **Reduction to Ince's equation** (DLMF 28.31.2–28.31.3): with `ξ² = -4k²c²`,
`A = η - ξ²/8`, `B = -(p+1)ξ` and `W(z) = w(z) exp(-¼ξ cos 2z)`, `W` solves the Whittaker–Hill
equation 28.31.1 iff `w` solves Ince's equation 28.31.3. (DLMF makes the substitution for
`k² < 0`; the algebra holds for all complex parameters.) -/
@[dlmf 28.31.E2]
theorem isWhittakerHillSolution_iff_isInceSolution {k c ξ η p : ℂ}
    (hξ : ξ ^ 2 = -4 * k ^ 2 * c ^ 2) {w : ℂ → ℂ} :
    IsWhittakerHillSolution (η - ξ ^ 2 / 8) (-(p + 1) * ξ) k c
        (fun z => w z * Complex.exp (-(ξ * Complex.cos (2 * z)) / 4)) ↔
      IsInceSolution ξ η p w := by
  set g : ℂ → ℂ := fun z => -(ξ * Complex.cos (2 * z)) / 4
  set g' : ℂ → ℂ := fun z => ξ * Complex.sin (2 * z) / 2
  set E : ℂ → ℂ := fun z => Complex.exp (g z)
  have hE : ∀ z, HasDerivAt E (E z * g' z) z := fun z =>
      (hasDerivAt_neg_mul_cos_two_mul_div_four ξ z).cexp
  have hF : ∀ z, HasDerivAt (fun z => Complex.exp (-g z)) (Complex.exp (-g z) * -g' z) z :=
    fun z => (hasDerivAt_neg_mul_cos_two_mul_div_four ξ z).neg.cexp
  have hg' : ∀ z, HasDerivAt g' (ξ * Complex.cos (2 * z)) z := hasDerivAt_mul_sin_two_mul_div_two ξ
  have hEF : ∀ z, E z * Complex.exp (-g z) = 1 := fun z => by
    simp only [E]; rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  constructor
  · rintro ⟨hWd, hW⟩
    set W : ℂ → ℂ := fun z => w z * E z
    have hw : w = fun z => W z * Complex.exp (-g z) := by
      funext z; simp only [W]; rw [mul_assoc, hEF, mul_one]
    have hWd' : ∀ z, HasDerivAt W (deriv W z) z := fun z => (hWd z).hasDerivAt
    have hw' : ∀ z, HasDerivAt w ((deriv W z - g' z * W z) * Complex.exp (-g z)) z := by
      intro z; rw [hw]
      convert (hWd' z).mul (hF z) using 1; ring
    have hdw : deriv w = fun z => (deriv W z - g' z * W z) * Complex.exp (-g z) :=
      funext fun z => (hw' z).deriv
    refine ⟨fun z => (hw' z).differentiableAt, fun z => ?_⟩
    rw [hdw]
    have := (((hW z).sub ((hg' z).mul (hWd' z))).mul (hF z))
    convert this using 1
    have h4 := cos_four_mul_eq_one_sub_two_mul_sin_sq z
    have hwz : w z = W z * Complex.exp (-g z) := congrFun hw z
    rw [hwz]
    simp only [W, g', Pi.sub_apply, Pi.mul_apply]
    rw [h4]
    linear_combination
      (-1 / 8 * w z * E z * Complex.exp (-g z) * (1 - 2 * Complex.sin (2 * z) ^ 2)) * hξ
  · rintro ⟨hwd, hw⟩
    have hwd' : ∀ z, HasDerivAt w (deriv w z) z := fun z => (hwd z).hasDerivAt
    have hW' : ∀ z, HasDerivAt (fun z => w z * E z) ((deriv w z + w z * g' z) * E z) z := by
      intro z; convert (hwd' z).mul (hE z) using 1; ring
    have hdW : deriv (fun z => w z * E z) = fun z => (deriv w z + w z * g' z) * E z :=
      funext fun z => (hW' z).deriv
    refine ⟨fun z => (hW' z).differentiableAt, fun z => ?_⟩
    rw [hdW]
    have := (((hw z).add ((hwd' z).mul (hg' z))).mul (hE z))
    convert this using 1
    have h4 := cos_four_mul_eq_one_sub_two_mul_sin_sq z
    simp only [g', Pi.mul_apply, Pi.add_apply]
    rw [h4]
    linear_combination (1 / 8 * w z * E z * (1 - 2 * Complex.sin (2 * z) ^ 2)) * hξ


/-- **Differential equation of the paraboloidal wave functions** (DLMF 28.31.18):
`w'' + (η - ⅛ξ² - (p+1)ξ cos 2z + ⅛ξ² cos 4z) w = 0` with `η = a_p^m(ξ)` for `hc_p^m` and
`η = b_p^m(ξ)` for `hs_p^m`; this is the Whittaker–Hill equation 28.31.1 with
`A = η - ξ²/8`, `B = -(p+1)ξ`, `k = iξ/2`, `c = 1`. -/
@[dlmf 28.31.E18]
theorem paraboloidal_isWhittakerHillSolution {p m : ℕ} (hm : m ≤ p) (hpm : m % 2 = p % 2)
    (ξ : ℝ) :
    IsWhittakerHillSolution (inceA p m ξ - (ξ : ℂ) ^ 2 / 8) (-((p : ℂ) + 1) * ξ) (I * ξ / 2) 1
        (fun z => paraboloidalHc p m z ξ) ∧
      (1 ≤ m → IsWhittakerHillSolution (inceB p m ξ - (ξ : ℂ) ^ 2 / 8) (-((p : ℂ) + 1) * ξ)
        (I * ξ / 2) 1 (fun z => paraboloidalHs p m z ξ)) := by
  clear hm hpm
  have hk : ((ξ : ℂ)) ^ 2 = -4 * (I * ξ / 2) ^ 2 * 1 ^ 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  have hfun : ∀ (F : ℂ → ℂ), (fun z => F z * Complex.exp (-((ξ : ℂ) * Complex.cos (2 * z)) / 4)) =
      fun z => Complex.exp (-((ξ : ℂ) * Complex.cos (2 * z)) / 4) * F z :=
    fun F => funext fun z => mul_comm _ _
  refine ⟨?_, fun _ => ?_⟩
  · have := (isWhittakerHillSolution_iff_isInceSolution (η := (inceA p m ξ : ℂ)) (p := (p : ℂ))
      hk).mpr (isInceSolution_inceC p m ξ)
    rw [hfun] at this
    exact this
  · have := (isWhittakerHillSolution_iff_isInceSolution (η := (inceB p m ξ : ℂ)) (p := (p : ℂ))
      hk).mpr (isInceSolution_inceS p m ξ)
    rw [hfun] at this
    exact this

end DLMF.Mathieu
