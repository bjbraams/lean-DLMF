/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Basic

/-!
# Airy functions and Bessel functions of order `±1/3` (DLMF §§9.6, 9.7)

For real `x > 0` and `ζ = (2/3) x^{3/2}` (`airyZeta`, DLMF 9.6.1) we prove

* `airyAi_eq_besselI`, `airyAi_eq_besselK`: `Ai(x) = (√x/3)(I_{-1/3}(ζ) - I_{1/3}(ζ))
  = π⁻¹ √(x/3) K_{1/3}(ζ)` (9.6.2);
* `airyBi_eq_besselI`: `Bi(x) = √(x/3)(I_{1/3}(ζ) + I_{-1/3}(ζ))` (9.6.4);
* `airyAi_neg_eq_besselJ`: `Ai(-x) = (√x/3)(J_{1/3}(ζ) + J_{-1/3}(ζ))` (9.6.6);
* `airyBi_neg_eq_besselJ`: `Bi(-x) = √(x/3)(J_{-1/3}(ζ) - J_{1/3}(ζ))` (9.6.8);

and the leading terms of the large-`x` expansions (DLMF 9.7.5, 9.7.7):

* `airyAi_isEquivalent`: `Ai(x) ~ e^{-ζ}/(2√π x^{1/4})`;
* `airyBi_isEquivalent`: `Bi(x) ~ e^{ζ}/(√π x^{1/4})`;

and `airyAi_ofReal_pos`, `airyBi_ofReal_pos`: both functions are positive on `[0, ∞)`.

The asymptotics come from Hankel's expansion of `K_ν` (`besselK_ray_isBigO`) and the
large-argument behaviour of `I_ν` (`besselI_sub_exp_isBigO`).
-/

@[expose] public section

open Complex Filter Asymptotics
open scoped Real Topology

noncomputable section

namespace DLMF.Airy

open DLMF.Bessel

/-- The variable `ζ = (2/3) x^{3/2}` (DLMF 9.6.1), for real `x`. -/
@[dlmf 9.6.E1]
def airyZeta (x : ℝ) : ℝ := 2 / 3 * x ^ (3 / 2 : ℝ)

theorem airyZeta_pos {x : ℝ} (hx : 0 < x) : 0 < airyZeta x := by
  unfold airyZeta; positivity

theorem tendsto_airyZeta : Tendsto airyZeta atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul_atTop (by norm_num)

/-! ### Powers of `x` written through `q = x^{1/4}` -/

theorem rpow_three_halves_eq {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = Real.sqrt x ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

theorem airyZeta_eq {x : ℝ} (hx : 0 ≤ x) : airyZeta x = 2 / 3 * Real.sqrt x ^ 3 := by
  rw [airyZeta, rpow_three_halves_eq hx]

/-- `(ζ/2)^{1/3} = 3^{-1/3} √x`. -/
theorem half_airyZeta_rpow_third {x : ℝ} (hx : 0 ≤ x) :
    (airyZeta x / 2) ^ (1 / 3 : ℝ) = (3 : ℝ) ^ (-(1 / 3 : ℝ)) * Real.sqrt x := by
  rw [airyZeta_eq hx, show 2 / 3 * Real.sqrt x ^ 3 / 2 = Real.sqrt x ^ 3 * 3⁻¹ by ring,
    Real.mul_rpow (by positivity) (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul
      (Real.sqrt_nonneg x), Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  norm_num
  ring

/-- `(ζ/2)^{-1/3} = 3^{1/3} / √x`. -/
theorem half_airyZeta_rpow_neg_third {x : ℝ} (hx : 0 < x) :
    (airyZeta x / 2) ^ (-(1 / 3) : ℝ) = (3 : ℝ) ^ (1 / 3 : ℝ) * (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg (by have := airyZeta_pos hx; positivity), half_airyZeta_rpow_third hx.le,
    mul_inv, Real.rpow_neg (by norm_num), inv_inv]

theorem airyZeta_sq_div_four {x : ℝ} (hx : 0 ≤ x) :
    ((airyZeta x : ℂ)) ^ 2 / 4 = (x : ℂ) ^ 3 / 9 := by
  have h : airyZeta x ^ 2 / 4 = x ^ 3 / 9 := by
    rw [airyZeta_eq hx]
    have hs := Real.sq_sqrt hx
    calc (2 / 3 * Real.sqrt x ^ 3) ^ 2 / 4 = (Real.sqrt x ^ 2) ^ 3 / 9 := by ring
      _ = x ^ 3 / 9 := by rw [hs]
  exact_mod_cast h

theorem half_airyZeta_cpow {x : ℝ} (hx : 0 ≤ x) (ν : ℝ) :
    ((airyZeta x : ℂ) / 2) ^ (ν : ℂ) = (((airyZeta x / 2) ^ ν : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (by unfold airyZeta; positivity)]
  push_cast
  ring_nf

/-! ### Bessel functions at `ζ` -/

theorem besselI_airyZeta_third {x : ℝ} (hx : 0 ≤ x) :
    besselI (1 / 3) (airyZeta x) = (((3 : ℝ) ^ (-(1 / 3 : ℝ)) * Real.sqrt x : ℝ) : ℂ) *
      regularizedHGFun (∅ : Multiset ℂ) {4 / 3} ((x : ℂ) ^ 3 / 9) := by
  rw [besselI, airyZeta_sq_div_four hx, ← half_airyZeta_rpow_third hx]
  have h := half_airyZeta_cpow hx (1 / 3)
  push_cast at h ⊢
  rw [h]
  norm_num

theorem besselI_airyZeta_neg_third {x : ℝ} (hx : 0 < x) :
    besselI (-1 / 3) (airyZeta x) = (((3 : ℝ) ^ (1 / 3 : ℝ) * (Real.sqrt x)⁻¹ : ℝ) : ℂ) *
      regularizedHGFun (∅ : Multiset ℂ) {2 / 3} ((x : ℂ) ^ 3 / 9) := by
  rw [besselI, airyZeta_sq_div_four hx.le, ← half_airyZeta_rpow_neg_third hx]
  have h := half_airyZeta_cpow hx.le (-(1 / 3))
  push_cast at h ⊢
  rw [show (-1 / 3 : ℂ) = -(1 / 3) by ring, h]
  norm_num

theorem besselJ_airyZeta_third {x : ℝ} (hx : 0 ≤ x) :
    besselJ (1 / 3) (airyZeta x) = (((3 : ℝ) ^ (-(1 / 3 : ℝ)) * Real.sqrt x : ℝ) : ℂ) *
      regularizedHGFun (∅ : Multiset ℂ) {4 / 3} ((-(x : ℂ)) ^ 3 / 9) := by
  rw [besselJ_eq_regularized, airyZeta_sq_div_four hx, ← half_airyZeta_rpow_third hx,
    show (-(x : ℂ)) ^ 3 / 9 = -((x : ℂ) ^ 3 / 9) by ring]
  have h := half_airyZeta_cpow hx (1 / 3)
  push_cast at h ⊢
  rw [h]
  norm_num

theorem besselJ_airyZeta_neg_third {x : ℝ} (hx : 0 < x) :
    besselJ (-1 / 3) (airyZeta x) = (((3 : ℝ) ^ (1 / 3 : ℝ) * (Real.sqrt x)⁻¹ : ℝ) : ℂ) *
      regularizedHGFun (∅ : Multiset ℂ) {2 / 3} ((-(x : ℂ)) ^ 3 / 9) := by
  rw [besselJ_eq_regularized, airyZeta_sq_div_four hx.le, ← half_airyZeta_rpow_neg_third hx,
    show (-(x : ℂ)) ^ 3 / 9 = -((x : ℂ) ^ 3 / 9) by ring]
  have h := half_airyZeta_cpow hx.le (-(1 / 3))
  push_cast at h ⊢
  rw [show (-1 / 3 : ℂ) = -(1 / 3) by ring, h]
  norm_num

/-! ### Constants -/

theorem three_rpow_third_div : (3 : ℝ) ^ (1 / 3 : ℝ) / 3 = (3 : ℝ) ^ (-(2 / 3 : ℝ)) := by
  rw [← Real.rpow_sub_one (by norm_num)]; norm_num

theorem three_rpow_neg_third_div : (3 : ℝ) ^ (-(1 / 3 : ℝ)) / 3 = (3 : ℝ) ^ (-(4 / 3 : ℝ)) := by
  rw [← Real.rpow_sub_one (by norm_num)]; norm_num

theorem sqrt_three_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem airy_const₁ {x : ℝ} (hx : 0 < x) :
    Real.sqrt x / 3 * ((3 : ℝ) ^ (1 / 3 : ℝ) * (Real.sqrt x)⁻¹) = (3 : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hr : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  rw [← three_rpow_third_div]
  field_simp

theorem airy_const₂ {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x / 3 * ((3 : ℝ) ^ (-(1 / 3 : ℝ)) * Real.sqrt x) =
      (3 : ℝ) ^ (-(4 / 3 : ℝ)) * x := by
  rw [← three_rpow_neg_third_div]
  linear_combination ((3 : ℝ) ^ (-(1 / 3 : ℝ)) / 3) * Real.mul_self_sqrt hx

theorem sqrt_div_three {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x / 3) = Real.sqrt 3 * (Real.sqrt x / 3) := by
  have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [Real.sqrt_div hx, div_eq_iff h3]
  linear_combination (-(Real.sqrt x / 3)) * sqrt_three_mul_self

theorem airy_const₃ {x : ℝ} (hx : 0 < x) :
    Real.sqrt (x / 3) * ((3 : ℝ) ^ (1 / 3 : ℝ) * (Real.sqrt x)⁻¹) =
      Real.sqrt 3 * (3 : ℝ) ^ (-(2 / 3 : ℝ)) := by
  rw [sqrt_div_three hx.le, mul_assoc, airy_const₁ hx]

theorem airy_const₄ {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x / 3) * ((3 : ℝ) ^ (-(1 / 3 : ℝ)) * Real.sqrt x) =
      Real.sqrt 3 * ((3 : ℝ) ^ (-(4 / 3 : ℝ)) * x) := by
  rw [sqrt_div_three hx, mul_assoc, airy_const₂ hx]

theorem ofReal_eq_of_eq {a b : ℝ} (h : a = b) : (a : ℂ) = b := by rw [h]

/-! ### Bessel-function forms (DLMF 9.6(i)) -/

/-- `Ai(x) = (√x/3)(I_{-1/3}(ζ) - I_{1/3}(ζ))` for `x > 0` (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_besselI {x : ℝ} (hx : 0 < x) :
    airyAi x = ((Real.sqrt x / 3 : ℝ) : ℂ) *
      (besselI (-1 / 3) (airyZeta x) - besselI (1 / 3) (airyZeta x)) := by
  rw [besselI_airyZeta_neg_third hx, besselI_airyZeta_third hx.le]
  have c1 := ofReal_eq_of_eq (airy_const₁ hx)
  have c2 := ofReal_eq_of_eq (airy_const₂ hx.le)
  push_cast at c1 c2 ⊢
  simp only [airyAi, airyF, airyG]
  linear_combination (-regularizedHGFun (∅ : Multiset ℂ) {2 / 3} ((x : ℂ) ^ 3 / 9)) * c1 +
    regularizedHGFun (∅ : Multiset ℂ) {4 / 3} ((x : ℂ) ^ 3 / 9) * c2

/-- `Bi(x) = √(x/3)(I_{1/3}(ζ) + I_{-1/3}(ζ))` for `x > 0` (DLMF 9.6.4). -/
@[dlmf 9.6.E4]
theorem airyBi_eq_besselI {x : ℝ} (hx : 0 < x) :
    airyBi x = ((Real.sqrt (x / 3) : ℝ) : ℂ) *
      (besselI (1 / 3) (airyZeta x) + besselI (-1 / 3) (airyZeta x)) := by
  rw [besselI_airyZeta_neg_third hx, besselI_airyZeta_third hx.le]
  have c3 := ofReal_eq_of_eq (airy_const₃ hx)
  have c4 := ofReal_eq_of_eq (airy_const₄ hx.le)
  push_cast at c3 c4 ⊢
  simp only [airyBi, airyF, airyG]
  linear_combination (-regularizedHGFun (∅ : Multiset ℂ) {2 / 3} ((x : ℂ) ^ 3 / 9)) * c3 -
    regularizedHGFun (∅ : Multiset ℂ) {4 / 3} ((x : ℂ) ^ 3 / 9) * c4

/-- `Ai(-x) = (√x/3)(J_{1/3}(ζ) + J_{-1/3}(ζ))` for `x > 0` (DLMF 9.6.6). -/
@[dlmf 9.6.E6]
theorem airyAi_neg_eq_besselJ {x : ℝ} (hx : 0 < x) :
    airyAi (-x) = ((Real.sqrt x / 3 : ℝ) : ℂ) *
      (besselJ (1 / 3) (airyZeta x) + besselJ (-1 / 3) (airyZeta x)) := by
  rw [besselJ_airyZeta_neg_third hx, besselJ_airyZeta_third hx.le]
  have c1 := ofReal_eq_of_eq (airy_const₁ hx)
  have c2 := ofReal_eq_of_eq (airy_const₂ hx.le)
  push_cast at c1 c2 ⊢
  simp only [airyAi, airyF, airyG]
  linear_combination (-regularizedHGFun (∅ : Multiset ℂ) {2 / 3} ((-(x : ℂ)) ^ 3 / 9)) * c1 -
    regularizedHGFun (∅ : Multiset ℂ) {4 / 3} ((-(x : ℂ)) ^ 3 / 9) * c2

/-- `Bi(-x) = √(x/3)(J_{-1/3}(ζ) - J_{1/3}(ζ))` for `x > 0` (DLMF 9.6.8). -/
@[dlmf 9.6.E8]
theorem airyBi_neg_eq_besselJ {x : ℝ} (hx : 0 < x) :
    airyBi (-x) = ((Real.sqrt (x / 3) : ℝ) : ℂ) *
      (besselJ (-1 / 3) (airyZeta x) - besselJ (1 / 3) (airyZeta x)) := by
  rw [besselJ_airyZeta_neg_third hx, besselJ_airyZeta_third hx.le]
  have c3 := ofReal_eq_of_eq (airy_const₃ hx)
  have c4 := ofReal_eq_of_eq (airy_const₄ hx.le)
  push_cast at c3 c4 ⊢
  simp only [airyBi, airyF, airyG]
  linear_combination (-regularizedHGFun (∅ : Multiset ℂ) {2 / 3} ((-(x : ℂ)) ^ 3 / 9)) * c3 +
    regularizedHGFun (∅ : Multiset ℂ) {4 / 3} ((-(x : ℂ)) ^ 3 / 9) * c4

theorem third_ne_int : ∀ k : ℤ, (1 / 3 : ℂ) ≠ k := by
  intro k hk
  have h := congrArg Complex.re hk
  simp only [div_re, one_re, intCast_re] at h
  norm_num [Complex.normSq] at h
  have h3 : ((3 * k : ℤ) : ℝ) = 1 := by push_cast; linarith
  have : 3 * k = 1 := by exact_mod_cast h3
  omega

/-- `Ai(x) = π⁻¹ √(x/3) K_{1/3}(ζ)` for `x > 0` (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_besselK {x : ℝ} (hx : 0 < x) :
    airyAi x = ((π⁻¹ * Real.sqrt (x / 3) : ℝ) : ℂ) * besselK (1 / 3) (airyZeta x) := by
  have hs : Complex.sin (1 / 3 * π) = ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
    rw [show (1 / 3 * π : ℂ) = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin,
      Real.sin_pi_div_three]
  have hK : besselK (1 / 3) (airyZeta x) = ((π / Real.sqrt 3 : ℝ) : ℂ) *
      (besselI (-1 / 3) (airyZeta x) - besselI (1 / 3) (airyZeta x)) := by
    rw [besselK_eq_of_not_int third_ne_int, besselE, hs,
      show (-(1 / 3) : ℂ) = -1 / 3 by ring]
    have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
    push_cast
    field_simp
  have hc : π⁻¹ * Real.sqrt (x / 3) * (π / Real.sqrt 3) = Real.sqrt x / 3 := by
    have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    rw [sqrt_div_three hx.le]
    field_simp
  rw [hK, ← mul_assoc, ← ofReal_mul, hc, airyAi_eq_besselI hx]

/-! ### Large-`x` behaviour (DLMF 9.7.5, 9.7.7) -/

/-- If `‖m‖ = c g` and `f - m = O(t⁻¹ g)` as `t → ∞`, then `f ~ m`. -/
theorem isEquivalent_of_sub_isBigO {f m : ℝ → ℂ} {g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hm : ∀ᶠ t in atTop, ‖m t‖ = c * g t)
    (h : (fun t => f t - m t) =O[atTop] fun t => t⁻¹ * g t) : f ~[atTop] m := by
  have h1 : (fun t : ℝ => t⁻¹) =o[atTop] (fun _ => (1 : ℂ)) :=
    (isLittleO_one_iff ℂ).mpr tendsto_inv_atTop_zero
  have h2 : g =O[atTop] m := by
    refine IsBigO.of_bound c⁻¹ ?_
    filter_upwards [hm] with t ht
    have hg : 0 ≤ g t := by
      have := norm_nonneg (m t)
      rw [ht] at this
      exact nonneg_of_mul_nonneg_right this hc
    rw [ht, Real.norm_of_nonneg hg]
    field_simp
    exact le_refl _
  have h3 := h1.mul_isBigO h2
  have h4 : (fun t => t⁻¹ * g t) =o[atTop] m := by
    refine h3.congr' (Eventually.of_forall fun t => rfl) (Eventually.of_forall fun t => ?_)
    simp
  exact h.trans_isLittleO h4

theorem rpow_neg_three_halves {t : ℝ} (ht : 0 < t) :
    t ^ (-(3 / 2) : ℝ) = t⁻¹ * t ^ (-(1 / 2) : ℝ) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add ht]; norm_num

/-- `K_ν(t) ~ e^{-t} √π (2t)^{-1/2}` as `t → +∞`. -/
theorem besselK_isEquivalent (ν : ℂ) :
    (fun t : ℝ => besselK ν t) ~[atTop]
      fun t : ℝ => exp (-(t : ℂ)) * ((2 * (t : ℂ)) ^ (-(1 / 2 : ℂ)) * (Real.sqrt π : ℂ)) := by
  have h := besselK_ray_isBigO ν (c := 1) (by simp) (α := 0) (by simp [Real.pi_pos])
    (by norm_num)
  simp only [one_mul] at h
  have he : (fun t : ℝ => exp (t : ℂ) * besselK ν t) ~[atTop]
      fun t : ℝ => (2 * (t : ℂ)) ^ (-(1 / 2 : ℂ)) * (Real.sqrt π : ℂ) := by
    refine isEquivalent_of_sub_isBigO (g := fun t => t ^ (-(1 / 2) : ℝ))
      (c := Real.sqrt π * (2 : ℝ) ^ (-(1 / 2) : ℝ)) (by positivity) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have h2t : (2 * (t : ℂ)) = ((2 * t : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, h2t, norm_cpow_eq_rpow_re_of_pos (by positivity), norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.mul_rpow (by norm_num) ht.le]
      norm_num
      ring
    · refine h.congr' (Eventually.of_forall fun _ => rfl) ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact rpow_neg_three_halves ht
  have hm := (IsEquivalent.refl (u := fun t : ℝ => exp (-(t : ℂ))) (l := atTop)).mul he
  refine hm.congr_left (Eventually.of_forall fun t => ?_)
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

theorem sq_rpow_quarter {x : ℝ} (hx : 0 ≤ x) : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = Real.sqrt x := by
  rw [← Real.rpow_add' hx (by norm_num), Real.sqrt_eq_rpow]; norm_num

/-- `√(2ζ) = 2 √x x^{1/4} / √3`. -/
theorem sqrt_two_airyZeta {x : ℝ} (hx : 0 < x) :
    Real.sqrt (2 * airyZeta x) = 2 * Real.sqrt x * x ^ (1 / 4 : ℝ) / Real.sqrt 3 := by
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hq : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity), airyZeta_eq hx.le]
  have hqq := sq_rpow_quarter hx.le
  have h33 := sqrt_three_mul_self
  rw [div_mul_div_comm, div_eq_iff (by positivity)]
  linear_combination (4 * Real.sqrt x ^ 2) * hqq - (4 / 3 * Real.sqrt x ^ 3) * h33

theorem two_airyZeta_cpow {x : ℝ} (hx : 0 < x) :
    (2 * (airyZeta x : ℂ)) ^ (-(1 / 2 : ℂ)) =
      ((Real.sqrt 3 / (2 * Real.sqrt x * x ^ (1 / 4 : ℝ)) : ℝ) : ℂ) := by
  have hz := airyZeta_pos hx
  rw [show (2 * (airyZeta x : ℂ)) = ((2 * airyZeta x : ℝ) : ℂ) by push_cast; ring,
    show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
    sqrt_two_airyZeta hx, inv_div]

/-- The leading term of the expansion of `Ai(x)` as `x → +∞` (DLMF 9.7.5):
`Ai(x) ~ e^{-ζ}/(2√π x^{1/4})`. -/
@[dlmf 9.7.E5]
theorem airyAi_isEquivalent :
    (fun x : ℝ => airyAi x) ~[atTop]
      fun x : ℝ => ((Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (1 / 4 : ℝ)) : ℝ) : ℂ) := by
  have hK := (besselK_isEquivalent (1 / 3)).comp_tendsto tendsto_airyZeta
  have hP := IsEquivalent.refl (u := fun x : ℝ => ((π⁻¹ * Real.sqrt (x / 3) : ℝ) : ℂ))
    (l := atTop)
  refine ((hP.mul hK).congr_left ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Pi.mul_apply, Function.comp]
    rw [airyAi_eq_besselK hx]
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Pi.mul_apply, Function.comp]
    rw [two_airyZeta_cpow hx, ← ofReal_neg, ← ofReal_exp]
    have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have hq : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
    have hp : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    have hpp : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
    have h33 := sqrt_three_mul_self
    have key : π⁻¹ * Real.sqrt (x / 3) *
        (Real.exp (-airyZeta x) * (Real.sqrt 3 / (2 * Real.sqrt x * x ^ (1 / 4 : ℝ)) *
          Real.sqrt π)) =
        Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (1 / 4 : ℝ)) := by
      rw [sqrt_div_three hx.le]
      field_simp
      linear_combination (Real.sqrt π ^ 2) * h33 + 3 * hpp
    exact_mod_cast key

theorem one_add_two_mul_ne (ν : ℝ) (hν : 0 < 1 + 2 * ν) : ∀ k : ℕ, 1 + 2 * (ν : ℂ) ≠ -k := by
  intro k hk
  have h := congrArg Complex.re hk
  simp only [add_re, one_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
    sub_zero, neg_re, natCast_re] at h
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- `I_{1/3}(t) + I_{-1/3}(t) ~ 2eᵗ/√(2πt)` as `t → +∞`. -/
theorem besselI_third_add_isEquivalent :
    (fun t : ℝ => besselI (1 / 3) t + besselI (-1 / 3) t) ~[atTop]
      fun t : ℝ => ((2 * (Real.exp t / Real.sqrt (2 * π * t)) : ℝ) : ℂ) := by
  have h₁ := besselI_sub_exp_isBigO (ν := ((1 / 3 : ℝ) : ℂ)) (one_add_two_mul_ne _ (by norm_num))
  have h₂ := besselI_sub_exp_isBigO (ν := ((-1 / 3 : ℝ) : ℂ))
    (one_add_two_mul_ne _ (by norm_num))
  push_cast at h₁ h₂
  refine isEquivalent_of_sub_isBigO (g := fun t => Real.exp t * t ^ (-(1 / 2) : ℝ))
    (c := 2 / Real.sqrt (2 * π)) (by positivity) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_mul (by positivity),
      Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
    field_simp
  · have h := h₁.add h₂
    refine h.congr' (Eventually.of_forall fun t => ?_) ?_
    · simp only
      push_cast
      ring
    · filter_upwards [eventually_gt_atTop 0] with t ht
      rw [rpow_neg_three_halves ht]
      ring

/-- The leading term of the expansion of `Bi(x)` as `x → +∞` (DLMF 9.7.7):
`Bi(x) ~ e^{ζ}/(√π x^{1/4})`. -/
@[dlmf 9.7.E7]
theorem airyBi_isEquivalent :
    (fun x : ℝ => airyBi x) ~[atTop]
      fun x : ℝ => ((Real.exp (airyZeta x) / (Real.sqrt π * x ^ (1 / 4 : ℝ)) : ℝ) : ℂ) := by
  have hI := besselI_third_add_isEquivalent.comp_tendsto tendsto_airyZeta
  have hP := IsEquivalent.refl (u := fun x : ℝ => ((Real.sqrt (x / 3) : ℝ) : ℂ)) (l := atTop)
  refine ((hP.mul hI).congr_left ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Pi.mul_apply, Function.comp]
    rw [airyBi_eq_besselI hx]
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Pi.mul_apply, Function.comp]
    have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have hq : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
    have hp : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    have h33 := sqrt_three_mul_self
    have hz := airyZeta_pos hx
    have key : Real.sqrt (x / 3) * (2 * (Real.exp (airyZeta x) /
        Real.sqrt (2 * π * airyZeta x))) =
        Real.exp (airyZeta x) / (Real.sqrt π * x ^ (1 / 4 : ℝ)) := by
      rw [show 2 * π * airyZeta x = π * (2 * airyZeta x) by ring,
        Real.sqrt_mul Real.pi_pos.le, sqrt_two_airyZeta hx, sqrt_div_three hx.le]
      field_simp
      linear_combination h33
    exact_mod_cast key

/-! ### Positivity on `[0, ∞)` -/

theorem Gamma_two_thirds_eq : Complex.Gamma (2 / 3) = ((Real.Gamma (2 / 3) : ℝ) : ℂ) := by
  rw [← Complex.Gamma_ofReal]; push_cast; ring_nf

/-- `Ai(x)` is a positive real number for `x ≥ 0` (DLMF 9.7(ii)/9.9(i): `Ai` has no
nonnegative zeros). -/
theorem airyAi_ofReal_pos {x : ℝ} (hx : 0 ≤ x) : ∃ r : ℝ, 0 < r ∧ airyAi x = r := by
  rcases hx.eq_or_lt with rfl | hx
  · refine ⟨1 / ((3 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)), by
      have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3); positivity, ?_⟩
    rw [ofReal_zero, airyAi_zero, Gamma_two_thirds_eq]
    push_cast
    ring
  · obtain ⟨r, hr, hK⟩ := besselK_ofReal_pos (1 / 3) (airyZeta_pos hx)
    refine ⟨π⁻¹ * Real.sqrt (x / 3) * r, ?_, ?_⟩
    · have : 0 < Real.sqrt (x / 3) := Real.sqrt_pos.mpr (by positivity)
      have := Real.pi_pos
      positivity
    · rw [airyAi_eq_besselK hx]
      push_cast at hK ⊢
      rw [hK]

/-- `Bi(x)` is a positive real number for `x ≥ 0`. -/
theorem airyBi_ofReal_pos {x : ℝ} (hx : 0 ≤ x) : ∃ r : ℝ, 0 < r ∧ airyBi x = r := by
  rcases hx.eq_or_lt with rfl | hx
  · refine ⟨1 / ((3 : ℝ) ^ (1 / 6 : ℝ) * Real.Gamma (2 / 3)), by
      have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3); positivity, ?_⟩
    rw [ofReal_zero, airyBi_zero, Gamma_two_thirds_eq]
    push_cast
    ring
  · obtain ⟨r₁, hr₁, h₁⟩ := besselI_ofReal_pos (ν := 1 / 3) (by norm_num) (airyZeta_pos hx)
    obtain ⟨r₂, hr₂, h₂⟩ := besselI_ofReal_pos (ν := -1 / 3) (by norm_num) (airyZeta_pos hx)
    refine ⟨Real.sqrt (x / 3) * (r₁ + r₂), ?_, ?_⟩
    · have : 0 < Real.sqrt (x / 3) := Real.sqrt_pos.mpr (by positivity)
      positivity
    · rw [airyBi_eq_besselI hx]
      push_cast at h₁ h₂ ⊢
      rw [h₁, h₂]

end DLMF.Airy
