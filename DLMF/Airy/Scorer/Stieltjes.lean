/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Bessel
public import DLMF.Airy.Framework
import DLMF.Airy.Scorer.MellinBarnes
import DLMF.Bessel.KMellin
import DLMF.Gamma.Multiplication
import DLMFMathlib.Analysis.MellinQuadraticKernel
import DLMFMathlib.Analysis.Integral.CauchyBoundary
import DLMF.Airy.IntegralRepresentations

/-!
# Stieltjes representations of Scorer functions

Mellin Parseval and Gamma triplication identify the integral of `K_{1/3}(t)/(ζ²+t²)`
with the cubic Laplace integral of `Hi(-x)` for `x > 0`, where `ζ = (2/3)x^(3/2)`.
Holomorphic continuation gives the identity on `|arg z| < π/3`. The two Cauchy boundary
values and Scorer's connection formula give the principal value for `Gi(x)`, `x > 0`.
The changes of variables preserve the principal complex powers.

## Main results

* `ScorerStieltjes.mellin_factor_identity`: the Gamma-factor identity behind Parseval.
* `ScorerStieltjes.scorerHi_stieltjes_positive`: the Stieltjes formula on the positive axis.
* `scorerHi_stieltjes_integral`: the full sectorial formula (DLMF 9.12.22).
* `scorerGi_principalValue`: the real principal-value formula (DLMF 9.12.23).
-/

public noncomputable section

open Complex MeasureTheory Set Filter DLMF.Core
open scoped Real Topology

set_option maxHeartbeats 1000000
namespace DLMF.Airy.ScorerStieltjes

/-- The positive Airy scale separates into powers of `2`, `3` and `x`. -/
lemma airy_scale_cpow {x a : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hla : Real.log a = Real.log 2 - Real.log 3 + 3 / 2 * Real.log x) (w : ℂ) :
    (a : ℂ) ^ w = (2 : ℂ) ^ w * (3 : ℂ) ^ (-w) * (x : ℂ) ^ (3 / 2 * w) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ha.ne'),
    cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
    cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'),
    ← ofReal_log ha.le,
    show log (2 : ℂ) = (Real.log 2 : ℂ) by simp,
    show log (3 : ℂ) = (Real.log 3 : ℂ) by simp,
    ← ofReal_log hx.le, hla,
    ← exp_add, ← exp_add]
  congr 1
  push_cast
  ring

/-- The Mellin factors for the Bessel and cubic Laplace integrals differ by an elementary
factor after the affine change of vertical-line parameter. -/
lemma mellin_factor_identity {x a : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hla : Real.log a = Real.log 2 - Real.log 3 + 3 / 2 * Real.log x) (s : ℂ) :
    ((2 : ℂ) ^ (s - 2) * Gamma ((s - 1 / 3) / 2) * Gamma ((s + 1 / 3) / 2)) *
      ((a : ℂ) ^ (-1 - s) * Gamma ((1 - s) / 2) * Gamma ((1 + s) / 2) / 2) =
    (Real.pi / 8 * (3 : ℂ) ^ (5 / 2 : ℂ) * (x : ℂ) ^ (-2 : ℂ)) *
      ((Gamma ((3 * s - 1) / 2) * (x : ℂ) ^ (-((3 * s - 1) / 2))) *
        (Gamma ((1 - s) / 2) * (1 / 3 : ℂ) ^ (-((1 - s) / 2)) / 3)) := by
  have htrip : Gamma ((s - 1 / 3) / 2) * Gamma ((s + 1 / 3) / 2) *
      Gamma ((1 + s) / 2) = (2 * Real.pi) * (3 : ℂ) ^ (1 - 3 * s / 2) *
        Gamma ((3 * s - 1) / 2) := by
    have h := DLMF.Gamma.Gamma_prod_add_div (m := 3) (by norm_num) (s / 2 - 1 / 6)
    norm_num only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_ofNat,
      Nat.cast_zero, zero_div, add_zero, one_mul] at h
    have he0 : s / 2 - 1 / 6 = (s - 1 / 3) / 2 := by ring
    have he1 : s / 2 - 1 / 6 + 1 / 3 = (s + 1 / 3) / 2 := by ring
    have he2 : s / 2 - 1 / 6 + 2 / 3 = (1 + s) / 2 := by ring
    have he3 : 3 * (s / 2 - 1 / 6) = (3 * s - 1) / 2 := by ring
    have he4 : (1 / 2 : ℂ) - 3 * (s / 2 - 1 / 6) = 1 - 3 * s / 2 := by ring
    norm_num at h
    rw [he1, he2, he4, he3, he0] at h
    exact h
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hleft : (2 : ℂ) ^ (s - 2) * (a : ℂ) ^ (-1 - s) *
      (3 : ℂ) ^ (1 - 3 * s / 2) =
      (1 / 8 : ℂ) * (3 : ℂ) ^ (2 - s / 2) * (x : ℂ) ^ (-3 / 2 - 3 * s / 2) := by
    rw [airy_scale_cpow hx ha hla]
    calc _ = ((2 : ℂ) ^ (s - 2) * (2 : ℂ) ^ (-1 - s)) *
        ((3 : ℂ) ^ (-(-1 - s)) * (3 : ℂ) ^ (1 - 3 * s / 2)) *
        (x : ℂ) ^ (3 / 2 * (-1 - s)) := by ring
      _ = _ := by
        rw [← cpow_add _ _ h2, ← cpow_add _ _ h3]
        rw [show s - 2 + (-1 - s) = (-3 : ℂ) by ring,
          show -(-1 - s) + (1 - 3 * s / 2) = 2 - s / 2 by ring,
          show (3 / 2 : ℂ) * (-1 - s) = -3 / 2 - 3 * s / 2 by ring]
        norm_num [cpow_neg, cpow_ofNat]
  have hright : (3 : ℂ) ^ (5 / 2 : ℂ) * (x : ℂ) ^ (-2 : ℂ) *
      (x : ℂ) ^ (-((3 * s - 1) / 2)) * (1 / 3 : ℂ) ^ (-((1 - s) / 2)) / 3 =
      (3 : ℂ) ^ (2 - s / 2) * (x : ℂ) ^ (-3 / 2 - 3 * s / 2) := by
    have hinv : (1 / 3 : ℂ) ^ (-((1 - s) / 2)) = (3 : ℂ) ^ ((1 - s) / 2) := by
      rw [one_div, Complex.inv_cpow (3 : ℂ) _ (by
        norm_num; exact ne_of_lt Real.pi_pos), ← cpow_neg]
      congr 1
      ring
    rw [hinv, div_eq_mul_inv,
      show (3 : ℂ)⁻¹ = (3 : ℂ) ^ (-1 : ℂ) by rw [cpow_neg_one]]
    calc _ = ((3 : ℂ) ^ (5 / 2 : ℂ) * (3 : ℂ) ^ ((1 - s) / 2) *
        (3 : ℂ) ^ (-1 : ℂ)) * ((x : ℂ) ^ (-2 : ℂ) *
        (x : ℂ) ^ (-((3 * s - 1) / 2))) := by ring
      _ = _ := by
        rw [← cpow_add _ _ h3, ← cpow_add _ _ h3, ← cpow_add _ _ hx0]
        congr 2 <;> ring
  calc _ = Real.pi * ((2 : ℂ) ^ (s - 2) * (a : ℂ) ^ (-1 - s) *
        (3 : ℂ) ^ (1 - 3 * s / 2)) * Gamma ((3 * s - 1) / 2) *
        Gamma ((1 - s) / 2) := by
          linear_combination ((2 : ℂ) ^ (s - 2) * (a : ℂ) ^ (-1 - s) *
            Gamma ((1 - s) / 2) / 2) * htrip
    _ = _ := by
      rw [hleft]
      linear_combination -(Real.pi / 8 * Gamma ((3 * s - 1) / 2) *
        Gamma ((1 - s) / 2)) * hright

open Complex.CubicLaplace

/-- Mellin Parseval identifies the Bessel kernel integral on the positive axis. -/
lemma scorerHi_stieltjes_positive {x : ℝ} (hx : 0 < x) :
    scorerHi (-(x : ℂ)) = 4 * (x : ℂ) ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * Real.pi ^ 2) *
      ∫ t : ℝ in Ioi 0, DLMF.Bessel.besselK (1 / 3) t /
        ((airyZeta x : ℂ) ^ 2 + (t : ℂ) ^ 2) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have ha := airyZeta_pos hx
  have hla : Real.log (airyZeta x) =
      Real.log 2 - Real.log 3 + 3 / 2 * Real.log x := by
    rw [airyZeta, Real.log_mul (by norm_num) (by positivity),
      Real.log_div (by norm_num) (by norm_num), Real.log_rpow hx]
  let E : ℝ → ℂ := fun t => exp (-((x : ℂ) * t))
  let Q : ℝ → ℂ := fun t => exp (-((1 / 3 : ℂ) * (t : ℂ) ^ 3))
  let M : ℝ → ℂ := fun y => mellin E (1 - ((1 / 2 : ℂ) + y * I)) *
    mellin Q ((1 / 2 : ℂ) + y * I)
  let C : ℂ := Real.pi / 8 * (3 : ℂ) ^ (5 / 2 : ℂ) * (x : ℂ) ^ (-2 : ℂ)
  have hEf (s : ℂ) (hs : 0 < s.re) : mellin E s = Gamma s * (x : ℂ) ^ (-s) :=
    mellin_exp_neg_mul hs (by simpa using hx)
  have hQg (s : ℂ) (hs : 0 < s.re) :
      mellin Q s = Gamma (s / 3) * (1 / 3 : ℂ) ^ (-(s / 3)) / 3 :=
    mellin_exp_neg_mul_cube hs (by norm_num)
  have hEM : Integrable (fun y : ℝ => mellin E (1 - ((1 / 2 : ℂ) + y * I))) := by
    have h := (DLMF.Gamma.integrable_Gamma_mul_cpow_neg
      (c := 1 / 2) (by norm_num) (w := (x : ℂ)) (by simpa using hx)).comp_neg
    refine h.congr (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hEf _ (by norm_num)]
    have he : ((1 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I =
        1 - ((1 / 2 : ℂ) + y * I) := by push_cast; ring
    rw [he]
  have hEM' : Integrable
      (fun y : ℝ => mellin E (1 - (((1 / 2 : ℝ) : ℂ) + y * I))) := by
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using hEM
  have hLaplace : (∫ t in Ioi (0 : ℝ), E t * Q t) =
      (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, M y := by
    have h := integral_mul_eq_mellin_parseval
      (f := E) (g := Q) (σ := 1 / 2)
      (mellinConvergent_exp_neg_mul (by norm_num) (by simpa using hx))
      (mellinConvergent_exp_neg_mul_cube (by norm_num) (by norm_num)) (Or.inr hEM')
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using h
  have hHi : Real.pi * scorerHi (-(x : ℂ)) =
      (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, M y := by
    have h := ScorerMellin.scorerHi_eq_rotated (z := -(x : ℂ)) (θ := 0)
      (by simp; positivity)
    simp only [mul_zero, ofReal_zero, zero_mul, exp_zero, one_mul, mul_one, neg_neg] at h
    rw [hLaplace] at h
    exact h
  have hK := integral_mul_eq_mellin_parseval
    (f := fun t : ℝ => 1 / ((airyZeta x : ℂ) ^ 2 + (t : ℂ) ^ 2))
    (g := fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t) (σ := 2 / 3)
    (mellinConvergent_one_div_sq_add_sq ha (by norm_num) (by norm_num))
    (DLMF.Bessel.besselK_mellinConvergent (by norm_num))
    (Or.inl (DLMF.Bessel.verticalIntegrable_mellin_besselK (by norm_num)))
  push_cast at hK
  have hpoint (y : ℝ) :
      mellin (fun t : ℝ => 1 / ((airyZeta x : ℂ) ^ 2 + (t : ℂ) ^ 2))
        (1 - ((2 / 3 : ℂ) + y * I)) *
      mellin (fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t) ((2 / 3 : ℂ) + y * I) =
        C * M ((-3 / 2 : ℝ) * y) := by
    let s : ℂ := (2 / 3 : ℂ) + y * I
    have hΓ := mellin_factor_identity hx ha hla s
    have hr : 1 - ((1 / 2 : ℂ) + (((-3 / 2 : ℝ) * y : ℝ) : ℂ) * I) =
        (3 * s - 1) / 2 := by dsimp only [s]; push_cast; ring
    have hv : ((1 / 2 : ℂ) + (((-3 / 2 : ℝ) * y : ℝ) : ℂ) * I) / 3 =
        (1 - s) / 2 := by dsimp only [s]; push_cast; ring
    dsimp only [C, M]
    rw [hEf _ (by norm_num), hQg _ (by norm_num), hr, hv,
      mellin_one_div_sq_add_sq ha (by norm_num) (by norm_num),
      DLMF.Bessel.mellin_besselK (by norm_num)]
    dsimp only [s] at hΓ
    have hu0 : 1 - ((2 / 3 : ℂ) + y * I) - 2 = -1 - ((2 / 3 : ℂ) + y * I) := by ring
    have hu1 : 1 - (1 - ((2 / 3 : ℂ) + y * I)) / 2 =
        (1 + ((2 / 3 : ℂ) + y * I)) / 2 := by ring
    rw [hu0, hu1]
    exact (mul_comm _ _).trans hΓ
  have hsub := Measure.integral_comp_mul_left M (-3 / 2)
  norm_num only [abs_of_neg (by norm_num : (-3 / 2 : ℝ) < 0), neg_div,
    neg_neg, Complex.real_smul, ofReal_inv, ofReal_div, ofReal_ofNat] at hsub
  simp only [neg_div] at hpoint
  have hK' : (∫ t : ℝ in Ioi 0, DLMF.Bessel.besselK (1 / 3) t /
      ((airyZeta x : ℂ) ^ 2 + (t : ℂ) ^ 2)) =
      (1 / (2 * Real.pi) : ℂ) * C * (2 / 3) * ∫ y : ℝ, M y := by
    have hfun : (fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t /
        ((airyZeta x : ℂ) ^ 2 + (t : ℂ) ^ 2)) =
        fun t : ℝ => (1 / ((airyZeta x : ℂ) ^ 2 + (t : ℂ) ^ 2)) *
          DLMF.Bessel.besselK (1 / 3) t := by funext t; ring
    rw [hfun, hK, integral_congr_ae (Eventually.of_forall hpoint),
      integral_const_mul, hsub]
    ring
  have hπ0 : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h3 : (3 : ℂ) ^ (5 / 2 : ℂ) = 3 * (3 : ℂ) ^ (3 / 2 : ℂ) := by
    rw [show (5 / 2 : ℂ) = 1 + 3 / 2 by ring, cpow_add _ _ (by norm_num), cpow_one]
  have h3ne : (3 : ℂ) ^ (3 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  rw [hK']
  dsimp only [C]
  rw [h3, cpow_neg, cpow_ofNat]
  apply (mul_left_cancel₀ hπ0)
  rw [hHi]
  field_simp
  ring



/-- The two-thirds power of the inverse Airy scale maps the right half-plane to
`|arg z| < π/3` and inverts the Airy variable. -/
lemma inverseAiry_spec {w : ℂ} (hw : 0 < w.re) :
    let z := ((3 / 2 : ℂ) * w) ^ (2 / 3 : ℂ)
    z ≠ 0 ∧ |arg z| < Real.pi / 3 ∧ airyZetaComplex z = w := by
  dsimp only
  let u : ℂ := (3 / 2 : ℂ) * w
  have hu : 0 < u.re := by dsimp only [u]; norm_num [mul_re]; linarith
  have hu0 : u ≠ 0 := ne_zero_of_re_pos hu
  have harg : |arg u| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have him : (log u * (2 / 3 : ℂ)).im = 2 / 3 * arg u := by
    norm_num [mul_im, log_im]
    ring
  have hlog : log (u ^ (2 / 3 : ℂ)) = log u * (2 / 3 : ℂ) := by
    rw [cpow_def_of_ne_zero hu0]
    apply log_exp
    · rw [him]
      linarith [neg_abs_le (arg u), Real.pi_pos]
    · rw [him]
      linarith [le_abs_self (arg u), Real.pi_pos]
  have hpow : u ^ (2 / 3 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hu0)
  refine ⟨hpow, ?_, ?_⟩
  · rw [← log_im, hlog, him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
    linarith
  · rw [airyZetaComplex, cpow_def_of_ne_zero hpow, hlog,
      show log u * (2 / 3 : ℂ) * (3 / 2 : ℂ) = log u by ring, exp_log hu0]
    dsimp only [u]
    ring

/-- At a signed imaginary Airy variable the inverse coordinate has argument `±π/3`. -/
lemma inverseAiry_imaginary {x ε : ℝ} (hx : 0 < x) (hε : ε = 1 ∨ ε = -1) :
    ((3 / 2 : ℂ) * ((ε * airyZeta x : ℝ) * I)) ^ (2 / 3 : ℂ) =
      (x : ℂ) * exp ((ε : ℂ) * Real.pi * I / 3) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hbase : (3 / 2 : ℂ) * ((ε * airyZeta x : ℝ) * I) =
      ((x ^ (3 / 2 : ℝ) : ℝ) : ℂ) * ((ε : ℂ) * I) := by
    simp only [airyZeta, ofReal_mul, ofReal_div, ofReal_ofNat]
    ring
  have hε0 : (ε : ℂ) * I ≠ 0 := by
    rcases hε with rfl | rfl <;> norm_num
  have hlogε : log ((ε : ℂ) * I) = (ε : ℂ) * Real.pi * I / 2 := by
    rcases hε with rfl | rfl <;> norm_num [log_I, log_neg_I] <;> ring
  rw [hbase, cpow_def_of_ne_zero (mul_ne_zero
    (ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx (3 / 2)).ne') hε0),
    log_ofReal_mul (Real.rpow_pos_of_pos hx (3 / 2)) hε0, hlogε, Real.log_rpow hx,
    show ((3 / 2 * Real.log x : ℝ) : ℂ) + (ε : ℂ) * Real.pi * I / 2 =
      log (x : ℂ) * (3 / 2 : ℂ) + (ε : ℂ) * Real.pi * I / 2 by
        rw [← ofReal_log hx.le]; push_cast; ring]
  rw [add_mul, exp_add,
    show log (x : ℂ) * (3 / 2 : ℂ) * (2 / 3 : ℂ) = log x by ring,
    exp_log hx0]
  congr 2
  ring

end DLMF.Airy.ScorerStieltjes

namespace DLMF.Airy

/-- For `|arg z| < π/3`,
`Hi(-z) = 4z²/(3^{3/2} π²) ∫₀^∞ K_{1/3}(t)/(ζ² + t²) dt` with `ζ = (2/3) z^{3/2}` (DLMF 9.12.22). -/
@[dlmf 9.12.E22]
theorem scorerHi_stieltjes_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π / 3) :
    scorerHi (-z) = 4 * z ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * π ^ 2) *
      ∫ t : ℝ in Ioi 0, DLMF.Bessel.besselK (1 / 3) t / (airyZetaComplex z ^ 2 + (t : ℂ) ^ 2) := by
  let U := IntegralRepresentation.sector (Real.pi / 3)
  have hα : Real.pi / 3 ≤ Real.pi := by linarith [Real.pi_pos]
  have hU : IsOpen U := IntegralRepresentation.isOpen_sector _
  have hζ : DifferentiableOn ℂ airyZetaComplex U := by
    intro w hw
    exact (((Complex.hasStrictDerivAt_cpow_const (c := (3 / 2 : ℂ)) hw.1).hasDerivAt).const_mul
      (2 / 3)).differentiableAt.differentiableWithinAt
  have hmap : MapsTo airyZetaComplex U {w : ℂ | 0 < w.re} := by
    intro w hw
    have hw0 := slitPlane_ne_zero hw.1
    have hcos : 0 < Real.cos (3 / 2 * arg w) := by
      apply Real.cos_pos_of_mem_Ioo
      rcases abs_lt.mp (show |arg w| < Real.pi / 3 from hw.2) with ⟨hlo, hhi⟩
      constructor <;> linarith
    have he : (airyZetaComplex w).re =
        2 / 3 * Real.exp ((log w * (3 / 2 : ℂ)).re) * Real.cos (3 / 2 * arg w) := by
      have him : (log w * (3 / 2 : ℂ)).im = 3 / 2 * arg w := by
        norm_num [mul_im, log_im]
        ring
      rw [airyZetaComplex, cpow_def_of_ne_zero hw0,
        show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by norm_num,
        re_ofReal_mul, exp_re, him]
      ring
    dsimp only [Set.mem_ofPred_eq]
    rw [he]
    positivity
  have hK : IntegrableOn (fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t) (Ioi 0) := by
    simpa only [sub_self, cpow_zero, one_mul] using
      (DLMF.Bessel.besselK_mellin (μ := 1) (ν := 1 / 3) (by norm_num)).1
  have hF := (differentiableOn_integral_div_sq_add_sq hK).comp hζ hmap
  have hR : DifferentiableOn ℂ (fun w : ℂ =>
      4 * w ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * Real.pi ^ 2) *
        ∫ t : ℝ in Ioi 0, DLMF.Bessel.besselK (1 / 3) t /
          (airyZetaComplex w ^ 2 + (t : ℂ) ^ 2)) U := by
    exact ((differentiable_const 4).mul (differentiable_id.pow 2)).div_const _
      |>.differentiableOn.mul hF
  have hL : DifferentiableOn ℂ (fun w : ℂ => scorerHi (-w)) U :=
    (differentiable_scorerHi.comp differentiable_neg).differentiableOn
  have h1 : (1 : ℂ) ∈ U :=
    IntegralRepresentation.mem_sector hα one_ne_zero (by simp; positivity)
  have heq : ∀ x : ℝ, 0 < x → (x : ℂ) ∈ U →
      scorerHi (-(x : ℂ)) = 4 * (x : ℂ) ^ 2 /
        ((3 : ℂ) ^ (3 / 2 : ℂ) * Real.pi ^ 2) *
        ∫ t : ℝ in Ioi 0, DLMF.Bessel.besselK (1 / 3) t /
          (airyZetaComplex x ^ 2 + (t : ℂ) ^ 2) := by
    intro x hx _
    have hreal : airyZetaComplex x = (airyZeta x : ℂ) := by
      rw [airyZetaComplex, airyZeta, ofReal_mul, ofReal_div, ofReal_ofNat]
      rw [ofReal_cpow hx.le]
      push_cast
      rfl
    rw [hreal]
    exact ScorerStieltjes.scorerHi_stieltjes_positive hx
  exact IntegralRepresentation.eqOn_of_pos_real hU
    (IntegralRepresentation.isPreconnected_sector hα) h1 hL hR heq
    (IntegralRepresentation.mem_sector hα hz0 hz)



end DLMF.Airy

namespace DLMF.Airy.ScorerStieltjes


local notation "kernel" => (fun c t : ℝ => DLMF.Bessel.besselK (1 / 3) t /
  ((c : ℂ) ^ 2 - (t : ℂ) ^ 2))
local notation "density" => (fun c t : ℝ => DLMF.Bessel.besselK (1 / 3) t / ((t : ℂ) + c))
local notation "finitePart" => (fun c : ℝ =>
  (∫ t in 0..2 * c, (density c t - density c c) / ((t : ℂ) - c)) +
    ∫ t in Ioi (2 * c), density c t / ((t : ℂ) - c))

/-- The symmetric Bessel principal value is the negative Cauchy finite part. -/
lemma principalValue_besselK_eq_neg_finitePart {c : ℝ} (hc : 0 < c) :
    principalValueIoi (kernel c) c = -finitePart c := by
  have hf : IntegrableOn (fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t) (Ioi 0) := by
    simpa only [sub_self, cpow_zero, one_mul] using
      (DLMF.Bessel.besselK_mellin (μ := 1) (ν := 1 / 3) (by norm_num)).1
  have hd : DifferentiableAt ℝ (fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t) c :=
    ((DLMF.Bessel.hasDerivAt_besselK (1 / 3)
      (ofReal_mem_slitPlane.mpr hc)).comp_ofReal).differentiableAt
  have hg : IntegrableOn (density c) (Ioi 0) := by
    simpa only [ofReal_neg, sub_neg_eq_add, ofReal_zero, zero_mul, add_zero] using
      integrableOn_Ioi_div_sub_add_mul_I (c := -c) (d := 0) (by linarith) hf 0
  have hpoint (t : ℝ) : -(density c t / ((t : ℂ) - c)) = kernel c t := by
    rw [div_div, ← div_neg]
    congr 1
    ring
  have htail (ε : ℝ) (hε : 0 < ε) : IntegrableOn (kernel c) (Ioi (c + ε)) := by
    have h := (integrableOn_Ioi_div_sub_add_mul_I (c := c) (d := c + ε) (by linarith)
      (hg.mono_set (Ioi_subset_Ioi (by linarith))) 0).neg
    simpa only [Pi.neg_def, ofReal_zero, zero_mul, add_zero, hpoint] using h
  have himproper (ε : ℝ) (hε : 0 < ε) :
      improperAtTop (kernel c) (c + ε) = ∫ t in Ioi (c + ε), kernel c t := by
    exact (intervalIntegral_tendsto_integral_Ioi (c + ε) (htail ε hε) tendsto_id).limUnder_eq
  have h := pv_tendsto_div_sq_sub_sq hc hf hd
  have h' : Tendsto (fun ε : ℝ => (∫ t in 0..c - ε, kernel c t) +
      improperAtTop (kernel c) (c + ε)) (𝓝[>] 0) (𝓝 (-finitePart c)) := by
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [himproper ε hε]
  exact h'.limUnder_eq

/-- The two rotated `Hi` values are the two boundary values of its Bessel Stieltjes integral. -/
lemma scorerHi_boundary_eq_finitePart {x ε : ℝ} (hx : 0 < x) (hε : ε = 1 ∨ ε = -1) :
    scorerHi (-((x : ℂ) * exp ((ε : ℂ) * Real.pi * I / 3))) =
      4 * ((x : ℂ) * exp ((ε : ℂ) * Real.pi * I / 3)) ^ 2 /
        ((3 : ℂ) ^ (3 / 2 : ℂ) * Real.pi ^ 2) *
          (finitePart (airyZeta x) - (ε : ℂ) * Real.pi * I *
            density (airyZeta x) (airyZeta x)) := by
  let c : ℝ := airyZeta x
  let Z : ℝ → ℂ := fun η => ((3 / 2 : ℂ) * ((η : ℂ) + (ε * c : ℝ) * I)) ^ (2 / 3 : ℂ)
  have hc : 0 < c := airyZeta_pos hx
  have hf : IntegrableOn (fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t) (Ioi 0) := by
    simpa only [sub_self, cpow_zero, one_mul] using
      (DLMF.Bessel.besselK_mellin (μ := 1) (ν := 1 / 3) (by norm_num)).1
  have hd : DifferentiableAt ℝ (fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t) c :=
    ((DLMF.Bessel.hasDerivAt_besselK (1 / 3)
      (ofReal_mem_slitPlane.mpr hc)).comp_ofReal).differentiableAt
  have hbase : Tendsto (fun η : ℝ => (3 / 2 : ℂ) * ((η : ℂ) + (ε * c : ℝ) * I))
      (𝓝[>] 0) (𝓝 ((3 / 2 : ℂ) * ((ε * c : ℝ) * I))) := by
    have hi : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [ofReal_zero] using
        (continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [ofReal_zero, zero_add] using (hi.add_const ((ε * c : ℝ) * I)).const_mul (3 / 2)
  have hslit : (3 / 2 : ℂ) * ((ε * c : ℝ) * I) ∈ slitPlane := by
    right
    rcases hε with rfl | rfl <;> norm_num [mul_im] <;> linarith
  have hZ : Tendsto Z (𝓝[>] 0) (𝓝 ((x : ℂ) * exp ((ε : ℂ) * Real.pi * I / 3))) := by
    have h := (continuousAt_cpow_const (b := (2 / 3 : ℂ)) hslit).tendsto.comp hbase
    rw [inverseAiry_imaginary hx hε] at h
    exact h
  have hLeft := (differentiable_scorerHi.continuous.continuousAt.tendsto).comp hZ.neg
  have hF := tendsto_integral_Ioi_div_quadratic_sign_mul_I hc hε hf hd
  have hpre := ((hZ.pow 2).const_mul (4 : ℂ)).div_const
    ((3 : ℂ) ^ (3 / 2 : ℂ) * Real.pi ^ 2)
  have hRight := hpre.mul hF
  refine tendsto_nhds_unique hLeft (hRight.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hspec := inverseAiry_spec (w := (η : ℂ) + (ε * c : ℝ) * I)
    (by simpa using (show 0 < η from hη))
  have heq := scorerHi_stieltjes_integral hspec.1 hspec.2.1
  rw [hspec.2.2] at heq
  exact heq.symm

/-- Combining the two boundary values cancels the imaginary residues in Scorer's connection
formula for `Gi`. -/
lemma scorerGi_eq_neg_finitePart {x : ℝ} (hx : 0 < x) :
    scorerGi x = -(4 * (x : ℂ) ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * Real.pi ^ 2)) *
      finitePart (airyZeta x) := by
  have hp := scorerHi_boundary_eq_finitePart (ε := 1) hx (Or.inl rfl)
  have hm := scorerHi_boundary_eq_finitePart (ε := -1) hx (Or.inr rfl)
  simp only [ofReal_one, one_mul] at hp
  simp only [ofReal_neg, ofReal_one, neg_mul, neg_div, sub_neg_eq_add, one_mul] at hm
  rw [show -(Real.pi * I / 3) = -Real.pi * I / 3 by ring] at hm
  have harp : (x : ℂ) * exp (-2 * Real.pi * I / 3) =
      -((x : ℂ) * exp (Real.pi * I / 3)) := by
    rw [exp_neg_two_pi_I_div_three', exp_pi_I_div_three]
    ring
  have harm : (x : ℂ) * exp (2 * Real.pi * I / 3) =
      -((x : ℂ) * exp (-Real.pi * I / 3)) := by
    rw [exp_two_pi_I_div_three, exp_neg_pi_I_div_three']
    ring
  have hApow : exp (Real.pi * I / 3) ^ 3 = -1 := by
    rw [← exp_nat_mul]
    convert Complex.exp_pi_mul_I using 1
    congr 1
    push_cast
    ring
  have hBpow : exp (-Real.pi * I / 3) ^ 3 = -1 := by
    rw [← exp_nat_mul]
    convert Complex.exp_neg_pi_mul_I using 1
    congr 1
    push_cast
    ring
  rw [scorerGi_rotations, harp, harm, hp, hm]
  calc _ = (4 * (x : ℂ) ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * Real.pi ^ 2)) *
      (exp (Real.pi * I / 3) ^ 3 / 2 *
          (finitePart (airyZeta x) - Real.pi * I * density (airyZeta x) (airyZeta x)) +
        exp (-Real.pi * I / 3) ^ 3 / 2 *
          (finitePart (airyZeta x) + Real.pi * I * density (airyZeta x) (airyZeta x))) := by ring
    _ = _ := by rw [hApow, hBpow]; ring

end DLMF.Airy.ScorerStieltjes

namespace DLMF.Airy

/-- For `x > 0`, `Gi(x) = 4x²/(3^{3/2} π²) ⨍₀^∞ K_{1/3}(t)/(ζ² - t²) dt` (principal value at
`t = ζ = (2/3) x^{3/2}`) (DLMF 9.12.23). -/
@[dlmf 9.12.E23]
theorem scorerGi_principalValue {x : ℝ} (hx : 0 < x) :
    scorerGi x = 4 * (x : ℂ) ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * π ^ 2) *
      principalValueIoi (fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t /
        ((airyZeta x : ℂ) ^ 2 - (t : ℂ) ^ 2)) (airyZeta x) := by
  rw [ScorerStieltjes.principalValue_besselK_eq_neg_finitePart (airyZeta_pos hx),
    ScorerStieltjes.scorerGi_eq_neg_finitePart hx]
  ring


end DLMF.Airy
