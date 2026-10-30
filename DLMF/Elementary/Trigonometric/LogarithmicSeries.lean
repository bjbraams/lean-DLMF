/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMFMathlib.NumberTheory.BernoulliTaylor
public import DLMFMathlib.Analysis.Complex.TrigR4SeriesExtension
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Convex.Deriv
public import TauCeti.Analysis.SpecialFunctions.Artanh

/-!
# Principal logarithmic Bernoulli series

The logarithms of the removable sine and tangent quotients and of cosine have Bernoulli
expansions on their full first zero-free disks. Slit-plane estimates retain the principal
branches, including the removable value at the origin. The sine quotient uses strict
concavity of sine and TauCeti’s `Real.tanh_le_self`; the series integrate the existing
Bernoulli cotangent and tangent expansions through Cauchy–Taylor uniqueness.

Source references and common attribution are retained in `DLMF.Elementary.Trigonometric`.
This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
-/

@[expose] public noncomputable section

open Complex Filter Set
open scoped Real Topology Nat

namespace DLMF.Elementary

/-- Strict concavity of sine bounds the derivative below the secant slope from zero. -/
private lemma sin_div_gt_cos {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < π) :
    Real.cos x < Real.sin x / x := by
  have hp {t : ℝ} (ht : 0 < t) (htπ : t < π) : Real.cos t < Real.sin t / t := by
    have h := StrictConcaveOn.lt_slope_of_hasDerivAt strictConcaveOn_sin_Icc
      (by exact ⟨le_rfl, Real.pi_pos.le⟩) (by exact ⟨ht.le, htπ.le⟩) ht
      (Real.hasDerivAt_sin t)
    simpa [slope, vsub_eq_sub, div_eq_mul_inv, mul_comm] using h
  rcases lt_or_gt_of_ne hx0 with hn | hp'
  · have hh := hp (neg_pos.mpr hn) (by simpa [abs_of_neg hn] using hx)
    simpa using hh
  · exact hp hp' (by simpa [abs_of_pos hp'] using hx)
/-- TauCeti’s hyperbolic tangent inequality bounds the hyperbolic sine secant slope by its derivative. -/
private lemma sinh_div_le_cosh {y : ℝ} (hy : y ≠ 0) : Real.sinh y / y ≤ Real.cosh y := by
  have hp {t : ℝ} (ht : 0 < t) : Real.sinh t / t ≤ Real.cosh t := by
    have h := Real.tanh_le_self ht.le
    rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos t)] at h
    exact (div_le_iff₀ ht).mpr (by nlinarith)
  rcases lt_or_gt_of_ne hy with hn | hp'
  · simpa using hp (neg_pos.mpr hn)
  · exact hp hp'
/-- Off the coordinate axes, the removable sine quotient cannot be real in its first vertical strip. -/
private lemma sine_quotient_im_ne {z : ℂ} (hx0 : z.re ≠ 0) (hy0 : z.im ≠ 0)
    (hx : |z.re| < π) : (Complex.sin z / z).im ≠ 0 := by
  have hs : 0 < Real.sin z.re / z.re := by
    rcases lt_or_gt_of_ne hx0 with hn | hp
    · apply div_pos_of_neg_of_neg _ hn
      have h := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hn) (by simpa [abs_of_neg hn] using hx)
      simpa using neg_neg_of_pos h
    · exact div_pos (Real.sin_pos_of_pos_of_lt_pi hp (by simpa [abs_of_pos hp] using hx)) hp
  have hsh : 0 < Real.sinh z.im / z.im := by
    rcases lt_or_gt_of_ne hy0 with hn | hp
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hn) hn
    · exact div_pos (Real.sinh_pos_iff.mpr hp) hp
  have htr : Real.cos z.re * (Real.sinh z.im / z.im) <
      (Real.sin z.re / z.re) * Real.cosh z.im := by
    have hsc := sin_div_gt_cos hx0 hx
    have hhc := sinh_div_le_cosh hy0
    rcases le_or_gt 0 (Real.cos z.re) with h | h
    · nlinarith [mul_nonneg h (sub_nonneg.mpr hhc),
        mul_pos (sub_pos.mpr hsc) (Real.cosh_pos z.im)]
    · nlinarith [mul_neg_of_neg_of_pos h hsh,
        mul_pos hs (Real.cosh_pos z.im)]
  intro hi
  have hparts : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im ∧
      (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
    constructor <;> (conv_lhs => rw [← Complex.re_add_im z, Complex.sin_add_mul_I])
    all_goals simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
  rw [Complex.div_im, hparts.1, hparts.2] at hi
  rw [← sub_div] at hi
  have hn := (div_eq_zero_iff.mp hi).resolve_right (by
    exact (Complex.normSq_pos.mpr (by intro h; subst z; simp at hx0)).ne')
  apply (ne_of_lt htr)
  field_simp
  nlinarith
/-- The sine quotient avoids the principal logarithm cut in its first zero-free vertical strip. -/
private lemma sine_quotient_slit {z : ℂ} (hz0 : z ≠ 0) (hx : |z.re| < π) :
    Complex.sin z / z ∈ Complex.slitPlane := by
  by_cases hx0 : z.re = 0
  · apply Or.inl
    have hz : z = z.im * I := by apply Complex.ext <;> simp [hx0]
    rw [hz, Complex.sin_mul_I, mul_div_mul_right _ _ Complex.I_ne_zero,
      ← Complex.ofReal_sinh, ← Complex.ofReal_div, Complex.ofReal_re]
    have hy : z.im ≠ 0 := by intro h; apply hz0; apply Complex.ext <;> simp [hx0, h]
    have hh : 0 < Real.sinh z.im / z.im := by
      rcases lt_or_gt_of_ne hy with hn | hp
      · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hn) hn
      · exact div_pos (Real.sinh_pos_iff.mpr hp) hp
    exact hh
  · by_cases hy0 : z.im = 0
    · apply Or.inl
      have hz : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hy0]
      rw [hz, ← Complex.ofReal_sin, ← Complex.ofReal_div, Complex.ofReal_re]
      rcases lt_or_gt_of_ne hx0 with hn | hp
      · apply div_pos_of_neg_of_neg _ hn
        have h := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hn) (by simpa [abs_of_neg hn] using hx)
        simpa using neg_neg_of_pos h
      · exact div_pos (Real.sin_pos_of_pos_of_lt_pi hp (by simpa [abs_of_pos hp] using hx)) hp
    · exact Or.inr (sine_quotient_im_ne hx0 hy0 hx)
/-- Removing the cotangent pole shifts the Bernoulli expansion to an odd power series. -/
private lemma cot_sub_inv_series {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖<π) :
    HasSum (fun n : ℕ => (-1:ℂ)^(n+1)*2^(2*n+2)*(bernoulli (2*n+2):ℂ)/
      ((2*n+2).factorial:ℂ)*z^(2*n+1)) (Complex.cot z-z⁻¹) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw : ‖z/π‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      div_lt_one Real.pi_pos]
    exact hz
  have h := Complex.hasSum_pi_mul_cot_bernoulli hw (div_ne_zero hz0 hπ)
  have h2 : HasSum (fun k : ℕ => (-1:ℂ)^k*(bernoulli (2*k):ℂ)*(2*z)^(2*k)/
      ((2*k).factorial:ℂ)) (z*Complex.cot z) := by
    convert h using 1
    · funext k
      rw [show (2:ℂ)*π*(z/π) = 2*z by field_simp]
    · rw [show (π:ℂ)*(z/π) = z by field_simp]
  have ht := ((hasSum_nat_add_iff' 1).mpr h2).div_const z
  convert ht using 1
  · funext n
    rw [show 2*(n+1) = 2*n+2 by omega, mul_pow]
    field_simp
    ring
  · simp [bernoulli_zero]
    field_simp
/-- An even complex function differentiable at the origin has zero derivative there. -/
private lemma even_deriv_zero {f : ℂ → ℂ} (hd : DifferentiableAt ℂ f 0)
    (he : ∀ w, f (-w) = f w) : deriv f 0 = 0 := by
  have hh := hd.hasDerivAt
  have hn := hh.comp_of_eq (0:ℂ) ((hasDerivAt_id (0:ℂ)).neg) (by simp)
  have hh' : HasDerivAt f (-deriv f 0) 0 := by
    simpa only [Function.comp_def, Pi.neg_apply, id_eq, he, mul_neg, mul_one] using hn
  linear_combination (1/2:ℂ) * hh.unique hh'
/-- The principal logarithm of the removable sine quotient has its Bernoulli expansion
on the full disk `‖z‖ < π`. -/
@[dlmf 4.19.E7]
theorem hasSum_log_sinc_bernoulli {z : ℂ} (hz : ‖z‖<π) :
    HasSum (fun n : ℕ => ((-1:ℂ)^(n+1)*2^(2*(n+1)-1)*(bernoulli (2*(n+1)):ℂ)/
      ((n+1)*(2*(n+1))!))*z^(2*(n+1)))
      (Complex.log (if z=0 then 1 else Complex.sin z/z)) := by
  let f := dslope Complex.sin 0
  let L := fun w => Complex.log (f w)
  have heq : f = fun w : ℂ => if w=0 then 1 else Complex.sin w/w := by
    funext w
    by_cases hw : w=0
    · subst w; simp [f, dslope, Complex.deriv_sin]
    · simp [f, dslope, slope, hw, div_eq_mul_inv, mul_comm]
  have hslit {w : ℂ} (hw : ‖w‖<π) : f w ∈ Complex.slitPlane := by
    rw [heq]
    by_cases hw0 : w=0
    · simp [hw0, Complex.slitPlane]
    · simp only [ite_eq_right hw0]
      exact sine_quotient_slit hw0 ((Complex.abs_re_le_norm w).trans_lt hw)
  have hdiff {w : ℂ} (hw : ‖w‖<π) : DifferentiableAt ℂ L w := by
    have hh : AnalyticAt ℂ f w := Complex.analyticAt_sin.dslope 0
    exact hh.differentiableAt.clog (hslit hw)
  let b : ℕ → ℂ := fun n => (-1:ℂ)^(n+1)*2^(2*n+2)*(bernoulli (2*n+2):ℂ)/
      ((2*n+2).factorial:ℂ)
  have hb : ∀ w : ℂ, ‖w‖<π → HasSum (fun n => b n*w^(2*n+1)) (deriv L w) := by
    intro w hw
    by_cases hw0 : w=0
    · subst w
      have hd := even_deriv_zero (hdiff (by simpa using Real.pi_pos)) (by
        intro w; dsimp only [L]; rw [heq]; simp)
      rw [hd]
      convert hasSum_zero using 1
      ext n
      simp
    · have he : f =ᶠ[𝓝 w] (fun v => Complex.sin v/v) := by
        filter_upwards [eventually_ne_nhds hw0] with v hv
        rw [heq]; simp [hv]
      have hd := (((Complex.hasDerivAt_sin w).div (hasDerivAt_id w) hw0).congr_of_eventuallyEq he).clog
        (hslit hw)
      have hs : Complex.sin w ≠ 0 := by
        have hh := Complex.slitPlane_ne_zero (hslit hw)
        simp only [heq, ite_eq_right hw0] at hh
        exact (div_ne_zero_iff.mp hh).1
      have hd' : deriv L w = Complex.cot w-w⁻¹ := by
        rw [hd.deriv]
        simp only [heq, ite_eq_right hw0, Complex.cot]
        simp only [id_eq, mul_one]
        field_simp
      rw [hd']
      exact cot_sub_inv_series hw0 hw
  have hs := Complex.hasSum_odd_primitive_on_ball Real.pi_pos
    (fun w hw => (hdiff (by simpa using hw)).differentiableWithinAt)
    (by simp [L, heq]) hb hz
  rw [show L z = Complex.log (if z=0 then 1 else Complex.sin z/z) by dsimp only [L]; rw [heq]] at hs
  convert hs using 1
  ext n
  dsimp only [b]
  rw [show 2*(n+1)-1 = 2*n+1 by omega, show 2*(n+1)=2*n+2 by omega,
    show 2*n+2=(2*n+1)+1 by omega, pow_succ (2:ℂ)]
  have hn0 : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : ((2*n+1+1).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  ring
/-- The odd Bernoulli series of tangent, obtained from the existing scaled tangent series. -/
private lemma trigR4_hasSum_tan_bernoulli {z : ℂ} (hz : ‖z‖ < π / 2) :
    HasSum (fun n : ℕ => (-1 : ℂ)^n * 2^(2*(n+1)) * (2^(2*(n+1))-1) *
      (bernoulli (2*(n+1)) : ℂ) / ((2*(n+1)).factorial : ℂ) * z^(2*n+1))
      (Complex.tan z) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hz0 : z = 0
  · subst z
    simp
  have hw : ‖z / π‖ < 1/2 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, div_lt_iff₀ Real.pi_pos]
    linarith
  have hw0 : z / π ≠ 0 := div_ne_zero hz0 hπ
  have h := Complex.hasSum_pi_mul_tan_bernoulli hw hw0
  have h2 : HasSum (fun k : ℕ => (-1:ℂ)^k * (bernoulli (2*k):ℂ) *
      (1-4^k) * (2*z)^(2*k) / ((2*k).factorial:ℂ)) (z * Complex.tan z) := by
    convert h using 1
    · funext k
      rw [show (2:ℂ)*π*(z/π) = 2*z by field_simp]
    · rw [show (π:ℂ)*(z/π) = z by field_simp]
  have h3 := ((hasSum_nat_add_iff' 1).mpr h2).div_const z
  convert h3 using 1
  · funext n
    have e : 2*(n+1) = 2*n+2 := by ring
    have e4 : (4:ℂ)^(n+1) = 2^(2*n+2) := by
      rw [show 2*n+2 = 2*(n+1) by ring, pow_mul]; norm_num
    rw [e, e4, pow_succ (-1 : ℂ) n]
    simp only [mul_pow]
    field_simp
    ring
  · simp
    field_simp


/-- Cosine has positive real part on its first zero-free centered disk. -/
private lemma trigR4_cos_mem_slitPlane {z : ℂ} (hz : ‖z‖ < π/2) :
    Complex.cos z ∈ Complex.slitPlane := by
  have hx : |z.re| < π/2 := (Complex.abs_re_le_norm z).trans_lt hz
  have hc := Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)
  apply Or.inl
  have hre : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    conv_lhs => rw [← Complex.re_add_im z, Complex.cos_add_mul_I]
    simp [← Complex.ofReal_cos]
  rw [hre]
  exact mul_pos hc (Real.cosh_pos z.im)

/-- The principal logarithm of cosine has derivative minus tangent on its first zero-free disk. -/
private lemma trigR4_hasDerivAt_log_cos {z : ℂ} (hz : ‖z‖ < π/2) :
    HasDerivAt (fun w => Complex.log (Complex.cos w)) (-Complex.tan z) z := by
  have h := (Complex.hasDerivAt_cos z).clog (trigR4_cos_mem_slitPlane hz)
  convert h using 1
  simp [Complex.tan, div_eq_mul_inv]

/-- DLMF 4.19.E8: hasSum log cos bernoulli. -/
@[dlmf 4.19.E8]
theorem hasSum_log_cos_bernoulli {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => ((-1:ℂ)^(n+1)*2^(2*(n+1)-1)*(2^(2*(n+1))-1)*(bernoulli (2*(n+1)):ℂ)/((n+1)*(2*(n+1))!))*z^(2*(n+1))) (Complex.log (Complex.cos z)) := by
  let b : ℕ → ℂ := fun n => (-1 : ℂ)^n * 2^(2*(n+1)) * (2^(2*(n+1))-1) *
      (bernoulli (2*(n+1)) : ℂ) / ((2*(n+1)).factorial : ℂ)
  let c : ℕ → ℂ := fun m => if Even m then 0 else -b (m/2)
  have hf : DifferentiableOn ℂ (fun w => Complex.log (Complex.cos w)) (Metric.ball 0 (π/2)) := by
    intro w hw
    exact (trigR4_hasDerivAt_log_cos (by simpa using hw)).differentiableAt.differentiableWithinAt
  have hc : ∀ w : ℂ, ‖w‖ < π/2 → HasSum (fun m => c m * w^m)
      (deriv (fun w => Complex.log (Complex.cos w)) w) := by
    intro w hw
    have ht := (trigR4_hasSum_tan_bernoulli hw).neg
    have he : (fun m => c m * w^m) =
        fun m => if Even m then 0 else -(b (m/2) * w^(2*(m/2)+1)) := by
      funext m
      by_cases hm : Even m
      · simp [c, hm]
      · have hmod : m % 2 ≠ 0 := by simpa only [Nat.even_iff] using hm
        have hme : 2*(m/2)+1=m := by omega
        simp [c, hm, hme]
    rw [he, (trigR4_hasDerivAt_log_cos hw).deriv]
    exact Complex.trigR4_hasSum_odd_iff.mpr ht
  have hs := Complex.hasSum_primitive_on_ball (by positivity : 0 < π/2) hf (by simp) hc hz
  let a : ℕ → ℂ := fun n =>
    ((-1:ℂ)^(n+1)*2^(2*(n+1)-1)*(2^(2*(n+1))-1)*(bernoulli (2*(n+1)):ℂ)/
      ((n+1)*(2*(n+1))!))*z^(2*(n+1))
  have he : (fun m => c m / (m+1) * z^(m+1)) =
      fun m => if Even m then 0 else a (m/2) := by
    funext m
    by_cases hm : Even m
    · simp [c, hm]
    · have hmod : m % 2 ≠ 0 := by simpa only [Nat.even_iff] using hm
      have hme : m=2*(m/2)+1 := by omega
      simp only [c, hm, ite_false]
      generalize hn : m/2 = n
      have hmn : m=2*n+1 := by omega
      rw [hmn]
      dsimp only [a, b]
      have hexp : 2*(n+1)-1=2*n+1 := by omega
      rw [hexp, show 2*(n+1)=(2*n+1)+1 by omega, pow_succ (-1:ℂ), pow_succ (2:ℂ)]
      push_cast
      have hn0 : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [show (2:ℂ)*n+1+1 = 2*((n:ℂ)+1) by ring]
      have hfact : ((2*n+1+1)!:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*n+1+1)
      field_simp [hn0, hfact]
  rw [he] at hs
  exact Complex.trigR4_hasSum_odd_iff.mp hs

/-- The tangent quotient has positive real part in its first zero-free vertical strip. -/
private lemma tan_div_re_pos {z : ℂ} (hz0 : z ≠ 0) (hx : |z.re|<π/2) :
    0 < (Complex.tan z/z).re := by
  have hc : 0 < Real.cos z.re := Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)
  have hcz : Complex.cos z ≠ 0 := by
    have hh : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
      conv_lhs => rw [← Complex.re_add_im z, Complex.cos_add_mul_I]
      simp [← Complex.ofReal_cos]
    intro h
    rw [h] at hh
    have hp := mul_pos hc (Real.cosh_pos z.im)
    simp [← hh] at hp
  have hparts : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im ∧
      (Complex.sin z).im = Real.cos z.re * Real.sinh z.im ∧
      (Complex.cos z).re = Real.cos z.re * Real.cosh z.im ∧
      (Complex.cos z).im = -Real.sin z.re * Real.sinh z.im := by
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals first
      | (conv_lhs => rw [← Complex.re_add_im z, Complex.sin_add_mul_I])
      | (conv_lhs => rw [← Complex.re_add_im z, Complex.cos_add_mul_I])
    all_goals simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
  have hform : (Complex.tan z/z).re =
      (z.re*Real.sin z.re*Real.cos z.re+z.im*Real.sinh z.im*Real.cosh z.im)/
        (Complex.normSq (Complex.cos z)*Complex.normSq z) := by
    rw [Complex.tan, Complex.div_re, Complex.div_re, Complex.div_im,
      hparts.1, hparts.2.1, hparts.2.2.1, hparts.2.2.2]
    have hns := (Complex.normSq_pos.mpr hz0).ne'
    have hnc := (Complex.normSq_pos.mpr hcz).ne'
    field_simp
    linear_combination (z.re*Real.sin z.re*Real.cos z.re)*(Real.cosh_sq_sub_sinh_sq z.im) +
      (z.im*Real.sinh z.im*Real.cosh z.im)*(Real.sin_sq_add_cos_sq z.re)
  rw [hform]
  apply div_pos _ (mul_pos (Complex.normSq_pos.mpr hcz) (Complex.normSq_pos.mpr hz0))
  have hs : 0 ≤ z.re*Real.sin z.re ∧ (z.re ≠ 0 → 0 < z.re*Real.sin z.re) := by
    by_cases hh : z.re=0
    · simp [hh]
    · have hp : 0 < z.re*Real.sin z.re := by
        rcases lt_or_gt_of_ne hh with hn | hp
        · apply mul_pos_of_neg_of_neg hn
          have h := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hn) (by
            rw [abs_of_neg hn] at hx; linarith [Real.pi_pos])
          simpa using neg_neg_of_pos h
        · exact mul_pos hp (Real.sin_pos_of_pos_of_lt_pi hp (by
            rw [abs_of_pos hp] at hx; linarith [Real.pi_pos]))
      exact ⟨hp.le, fun _ => hp⟩
  have hsh : 0 ≤ z.im*Real.sinh z.im ∧ (z.im ≠ 0 → 0 < z.im*Real.sinh z.im) := by
    by_cases hh : z.im=0
    · simp [hh]
    · have hp : 0 < z.im*Real.sinh z.im := by
        rcases lt_or_gt_of_ne hh with hn | hp
        · exact mul_pos_of_neg_of_neg hn (Real.sinh_neg_iff.mpr hn)
        · exact mul_pos hp (Real.sinh_pos_iff.mpr hp)
      exact ⟨hp.le, fun _ => hp⟩
  by_cases hx0 : z.re=0
  · have hy0 : z.im ≠ 0 := by intro h; apply hz0; apply Complex.ext <;> simp [hx0,h]
    nlinarith [mul_pos (hsh.2 hy0) (Real.cosh_pos z.im)]
  · nlinarith [mul_pos (hs.2 hx0) hc,
      mul_nonneg hsh.1 (Real.cosh_pos z.im).le]
/-- Positive real parts of cosine and the tangent quotient permit subtraction of their principal logarithms. -/
private lemma log_tan_div_eq {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖<π/2) :
    Complex.log (Complex.tan z/z) = Complex.log (Complex.sin z/z) - Complex.log (Complex.cos z) := by
  have hx := (Complex.abs_re_le_norm z).trans_lt hz
  have ht := tan_div_re_pos hz0 hx
  have hc : 0 < (Complex.cos z).re := by
    have h := Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)
    have he : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
      conv_lhs => rw [← Complex.re_add_im z, Complex.cos_add_mul_I]
      simp [← Complex.ofReal_cos]
    rw [he]
    exact mul_pos h (Real.cosh_pos z.im)
  have ht0 : Complex.tan z/z ≠ 0 := by intro h; rw [h] at ht; simp at ht
  have hc0 : Complex.cos z ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have hta := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ht))
  have hca := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hc))
  have hl := Complex.log_mul ht0 hc0
    (show (Complex.tan z/z).arg+(Complex.cos z).arg ∈ Ioc (-π) π from
      ⟨by linarith, by linarith⟩)
  have he : (Complex.tan z/z)*Complex.cos z = Complex.sin z/z := by
    rw [Complex.tan]
    field_simp
  rw [he] at hl
  linear_combination -hl
/-- The principal logarithm of the removable tangent quotient has its Bernoulli expansion
on the disk `‖z‖ < π / 2`. -/
@[dlmf 4.19.E9]
theorem hasSum_log_tan_div_bernoulli {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => ((-1:ℂ)^n*2^(2*(n+1))*(2^(2*(n+1)-1)-1)*
      (bernoulli (2*(n+1)):ℂ)/((n+1)*(2*(n+1))!))*z^(2*(n+1)))
      (Complex.log (if z=0 then 1 else Complex.tan z/z)) := by
  by_cases hz0 : z=0
  · subst z
    convert hasSum_zero using 1 <;> simp
  have hzπ : ‖z‖<π := lt_trans hz (by linarith [Real.pi_pos])
  have h := (hasSum_log_sinc_bernoulli hzπ).sub (hasSum_log_cos_bernoulli hz)
  simp only [ite_eq_right hz0] at h ⊢
  rw [← log_tan_div_eq hz0 hz] at h
  convert h using 1
  ext n
  rw [show 2*(n+1)-1=2*n+1 by omega, show 2*(n+1)=2*n+2 by omega,
    show 2*n+2=(2*n+1)+1 by omega, pow_succ (2:ℂ), pow_succ (-1:ℂ)]
  ring

end DLMF.Elementary
