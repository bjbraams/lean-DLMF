/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.UniformAsymptotics
public import DLMF.Elementary.LambertW.Asymptotics
public import DLMFMathlib.Analysis.Calculus.Deriv.SignPropagation

/-!
# Lambert W branch-point coefficients and the incomplete-gamma saddle coordinate

The inverse of the incomplete-gamma saddle coordinate gives a convergent parametrization of
`W exp W = -exp(-1-t²/2)` on `‖t‖ < 2√π`. Its Taylor coefficients equal the recursively defined
Lambert coefficients, since both satisfy the same quadratic convolution recurrence.
-/

@[expose] public noncomputable section

open Complex Finset Filter
open scoped Nat Topology

namespace DLMF.Elementary

open DLMF.Confluent

/-- The Lambert branch-point coefficients are the inverse incomplete-gamma coefficients. -/
theorem ofReal_lambertC (n : ℕ) : (lambertC n : ℂ) = gammaUniformAlpha n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [lambertC]
    · simp [lambertC]
    · rw [lambertC, gammaUniformAlpha_recurrence]
      simp only [show n+2≠0 by omega, show n+2≠1 by omega, ↓reduceDIte,
        show n+2-1=n+1 by omega]
      rw [Fin.sum_univ_eq_sum_range (fun k => lambertC (k+2) * lambertC (n+1-k)) (n+1+1-2)]
      rw [show n+1+1-2=n by omega]
      push_cast
      rw [ih (n+1) (by omega)]
      have he : (n : ℂ)+1+1+1=(n:ℂ)+3 := by ring
      rw [he]
      congr 2
      apply sum_congr rfl
      intro k hk
      rw [ih (k+2) (by have := mem_range.mp hk; omega),
        ih (n+1-k) (by omega)]

/-- The branch-point series sums to the exponential of the inverse saddle coordinate. -/
theorem hasSum_lambertC_inverse {t : ℂ} (ht : ‖t‖ < 2 * Real.sqrt Real.pi) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ ((n : ℤ) - 1) * lambertC n * t ^ n)
      (-exp (gammaUniformInverseLog (-t))) := by
  have h := (gammaUniformAlpha_hasSum (η := -t) (by simpa using ht)).neg
  have hsign (n : ℕ) : (-1 : ℂ) ^ ((n : ℤ) - 1) = -(-1 : ℂ) ^ n := by
    rw [zpow_sub₀ (by norm_num)]
    simp only [zpow_natCast, zpow_one, div_neg, div_one]
  refine h.congr_fun fun n => ?_
  rw [hsign, ← ofReal_lambertC]
  rw [neg_pow t]
  ring

/-- The inverse saddle coordinate parametrizes the Lambert equation on its full Taylor disk. -/
theorem lambertC_inverse_equation {t : ℂ} (ht : ‖t‖ < 2 * Real.sqrt Real.pi) :
    (-exp (gammaUniformInverseLog (-t))) * exp (-exp (gammaUniformInverseLog (-t))) =
      -exp (-1 - t ^ 2 / 2) := by
  obtain ⟨_, hs, he⟩ := gammaUniformInverseLog_spec.2.2 (-t) (by simpa using ht)
  have h := gammaUniformEta_equation hs
  rw [he] at h
  have harg : gammaUniformInverseLog (-t) - exp (gammaUniformInverseLog (-t)) =
      -1 - t ^ 2 / 2 := by
    simp only [neg_sq] at h
    linear_combination h
  rw [neg_mul, ← Complex.exp_add]
  congr 1
  rw [← sub_eq_add_neg, harg]

/-- The inverse saddle coordinate is real on the real Taylor interval. -/
private theorem gammaUniformInverseLog_im_eq_zero {x : ℝ}
    (hx : |x| < 2 * Real.sqrt Real.pi) : (gammaUniformInverseLog x).im = 0 := by
  have hs := gammaUniformAlpha_hasSum (η := (x : ℂ)) (by simpa using hx)
  have hi := Complex.hasSum_im hs
  simp_rw [← ofReal_lambertC, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_im] at hi
  have he : (exp (gammaUniformInverseLog x)).im = 0 := hi.unique (by simp)
  obtain ⟨_, hw, hinv⟩ := gammaUniformInverseLog_spec.2.2 (x : ℂ) (by simpa using hx)
  have h := congrArg Complex.im (gammaUniformEta_equation hw)
  rw [hinv] at h
  have hx2 : ((x : ℂ) ^ 2).im = 0 := by simp [pow_two, Complex.mul_im]
  have hz : 0 = -(gammaUniformInverseLog x).im := by simpa [he, hx2] using h
  linarith

/-- Away from zero the inverse coordinate has nonzero real part on the real Taylor interval. -/
private theorem gammaUniformInverseLog_re_ne_zero {x : ℝ}
    (hx : |x| < 2 * Real.sqrt Real.pi) (hx0 : x ≠ 0) :
    (gammaUniformInverseLog x).re ≠ 0 := by
  intro he
  have hw : gammaUniformInverseLog x = 0 :=
    Complex.ext he (gammaUniformInverseLog_im_eq_zero hx)
  have hi := (gammaUniformInverseLog_spec.2.2 (x : ℂ) (by simpa using hx)).2.2
  rw [hw, gammaUniformEta_normalization.2] at hi
  exact hx0 (Complex.ofReal_injective hi.symm)

/-- On either side of the origin the real inverse coordinate has the sign of its argument. -/
private theorem gammaUniformInverseLog_re_sign {x : ℝ}
    (hx : |x| < 2 * Real.sqrt Real.pi) :
    (0 < x → 0 < (gammaUniformInverseLog x).re) ∧
      (x < 0 → (gammaUniformInverseLog x).re < 0) := by
  let f : ℝ → ℝ := fun x => (gammaUniformInverseLog x).re
  have hf (x : ℝ) (hx : |x| < 2 * Real.sqrt Real.pi) :
      DifferentiableAt ℝ f x := by
    exact (gammaUniformInverseLog_spec.2.2 (x : ℂ) (by simpa using hx)).1.hasDerivAt
      |>.real_of_complex |>.differentiableAt
  have hf0 : f 0 = 0 := by simp [f, gammaUniformInverseLog_spec.1]
  have hd : HasDerivAt f 1 0 := by
    have h := (gammaUniformInverseLog_spec.2.2 (0 : ℂ) (by simp; positivity)).1.hasDerivAt
    rw [gammaUniformInverseLog_spec.2.1] at h
    simpa [f] using h.real_of_complex
  constructor
  · intro hx0
    apply pos_of_deriv_pos_of_continuousOn_of_ne_zero
      (f := f) (R := 2 * Real.sqrt Real.pi) ?_ ?_ hf0
      (by rw [hd.deriv]; norm_num) ⟨hx0, (le_abs_self x).trans_lt hx⟩
    · intro y hy
      exact (hf y (by rw [abs_of_pos hy.1]; exact hy.2)).continuousAt.continuousWithinAt
    · intro y hy
      exact gammaUniformInverseLog_re_ne_zero (by rw [abs_of_pos hy.1]; exact hy.2) hy.1.ne'
  · intro hx0
    have hd' : HasDerivAt (fun y : ℝ => -f (-y)) 1 0 := by
      have hd0 : HasDerivAt f 1 (-(0 : ℝ)) := by simpa using hd
      simpa only [Function.comp_def, mul_neg, one_mul, neg_neg] using!
        (hd0.comp 0 (hasDerivAt_neg (0 : ℝ))).neg
    have hp : 0 < -f (-(-x)) := by
      apply pos_of_deriv_pos_of_continuousOn_of_ne_zero
        (f := fun y => -f (-y)) (R := 2 * Real.sqrt Real.pi) ?_ ?_ (by simp [hf0])
        (by rw [hd'.deriv]; norm_num) ⟨by linarith, (neg_le_abs x).trans_lt hx⟩
      · intro y hy
        exact (((hf (-y) (by simpa [abs_of_pos hy.1] using hy.2)).comp y
          (hasDerivAt_neg y).differentiableAt).neg).continuousAt.continuousWithinAt
      · intro y hy
        exact neg_ne_zero.mpr (gammaUniformInverseLog_re_ne_zero
          (by simpa [abs_of_pos hy.1] using hy.2) (neg_ne_zero.mpr hy.1.ne'))
    simpa [f] using neg_pos.mp hp

/-- The inverse saddle coordinate selects the principal and lower real Lambert branches. -/
theorem lambertC_inverse_ofReal {t : ℝ} (ht : |t| < 2 * Real.sqrt Real.pi) :
    -exp (gammaUniformInverseLog (-(t : ℂ))) =
      if 0 ≤ t then lambertW 0 (-Real.exp (-1 - t ^ 2 / 2))
      else lambertW (-1) (-Real.exp (-1 - t ^ 2 / 2)) := by
  by_cases ht0 : t = 0
  · subst t
    simp only [ofReal_zero, neg_zero, gammaUniformInverseLog_spec.1, Complex.exp_zero,
      zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
    rw [ite_eq_left (le_refl (0 : ℝ))]
    exact lambertW_special_values.1.symm
  let u : ℝ := (gammaUniformInverseLog (-(t : ℂ))).re
  have hwu : gammaUniformInverseLog (-(t : ℂ)) = (u : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]; rfl
    · simp only [Complex.ofReal_im]
      simpa using gammaUniformInverseLog_im_eq_zero (x := -t) (by simpa using ht)
  have hv : -exp (gammaUniformInverseLog (-(t : ℂ))) = ((-Real.exp u : ℝ) : ℂ) := by
    rw [hwu, ← Complex.ofReal_exp, Complex.ofReal_neg]
  have heq : (-Real.exp u) * Real.exp (-Real.exp u) = -Real.exp (-1 - t ^ 2 / 2) := by
    apply Complex.ofReal_injective
    have he := lambertC_inverse_equation (t := (t : ℂ)) (by simpa using ht)
    rw [hv, ← Complex.ofReal_exp] at he
    simpa only [← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
      ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_div, ← Complex.ofReal_ofNat] using he
  by_cases htpos : 0 ≤ t
  · rw [ite_eq_left htpos, hv]
    have hu : u < 0 := by
      simpa [u] using (gammaUniformInverseLog_re_sign (x := -t) (by simpa using ht)).2
        (neg_neg_of_pos (lt_of_le_of_ne htpos (Ne.symm ht0)))
    have hlu : -1 ≤ -Real.exp u := by
      have := Real.exp_lt_one_iff.mpr hu
      linarith
    have hi := lambertW_exp_inverse hlu
    rw [← Complex.ofReal_mul, heq] at hi
    simpa only [Complex.ofReal_neg] using hi.symm
  · rw [ite_eq_right htpos, hv]
    have hu : 0 < u := by
      simpa [u] using (gammaUniformInverseLog_re_sign (x := -t) (by simpa using ht)).1
        (show 0 < -t by linarith)
    have hlu : -Real.exp u < -1 := by
      have := Real.one_lt_exp_iff.mpr hu
      linarith
    have hi := (lambertW_lower_exp_inverse hlu).1
    rw [← Complex.ofReal_mul, heq] at hi
    simpa only [Complex.ofReal_neg] using hi.symm

end DLMF.Elementary
