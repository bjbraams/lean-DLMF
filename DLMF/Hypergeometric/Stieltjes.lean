/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.IntegralRepresentations
public import DLMF.Hypergeometric.Boundary
public import DLMF.Gamma.BetaFunction.ParameterIntegrals
public import DLMF.Confluent.Basic.KummerContiguous
public import DLMF.Confluent.Integrals.Stieltjes
public import DLMFMathlib.MeasureTheory.Integral.FractionalSubstitution
public import Mathlib.Analysis.Complex.Convex

/-!
# A self-Stieltjes transform of the symmetric Gauss function

For `0 < Re a < 1` and `x > 0`,

`∫₀∞ F̃(a,1-a;1;-u)/(u+1+x) du = Γ(a)Γ(1-a) F̃(a,1-a;1;-x)`.

Pfaff's transformation and beta-weighted Gauss moments evaluate the resolvent moments.
A geometric expansion proves the identity near zero; the holomorphy of the Stieltjes
transform and analytic uniqueness extend it throughout the positive real axis. All
Gauss functions use their principal branch, and the displayed integral converges absolutely.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology Nat ComplexConjugate

namespace DLMF.Hypergeometric.GaussMoments

/-- The squared-numerator Gauss coefficient `(a)ₙ²/(n!)²`. -/
def squareCoeff (a : ℂ) (n : ℕ) : ℂ := pochhammer a n ^ 2 / (n.factorial : ℂ)^2

/-- The absolute beta moment of a squared-numerator Gauss term. -/
lemma integral_norm_square_term (a h : ℂ) (hh : 0 < h.re) (n : ℕ) :
    (∫ t : ℝ in 0..1, ‖squareCoeff a n * (t:ℂ)^n * (1-(t:ℂ))^(h-1)‖) =
      ‖squareCoeff a n‖ * (Real.Gamma (n+1) * Real.Gamma h.re /
        Real.Gamma (n+1+h.re)) := by
  calc _ = ∫ t : ℝ in 0..1, ‖squareCoeff a n‖ *
      (t^((n:ℝ)+1-1) * (1-t)^(h.re-1)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
        intro t ht
        dsimp only
        rw [norm_mul,norm_mul,norm_pow,norm_real,Real.norm_of_nonneg ht.1.le,
          show 1-(t:ℂ)=((1-t:ℝ):ℂ) by push_cast; ring,
          norm_cpow_eq_rpow_re_of_pos (by linarith [ht.2])]
        simp only [sub_re,one_re,add_sub_cancel_right,Real.rpow_natCast]
        ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,DLMF.Gamma.real_betaIntegral (by positivity) hh]

/-- The conjugate-parameter Gauss coefficient controls the squared-numerator term. -/
lemma norm_regularized_coefficient (a : ℂ) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ‖pochhammer a n * pochhammer (conj a) n /
      ((n.factorial:ℂ)*Gamma (((r+1:ℝ):ℂ)+n))‖ =
    ‖pochhammer a n‖^2 / ((n.factorial:ℝ)*Real.Gamma ((n:ℝ)+1+r)) := by
  rw [←DLMF.Confluent.conj_pochhammer,norm_div,norm_mul,norm_mul,norm_conj,norm_natCast,
    show ((r+1:ℝ):ℂ)+(n:ℂ) = (((n:ℝ)+1+r:ℝ):ℂ) by push_cast; ring,
    Gamma_ofReal,norm_real,Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le]
  ring

/-- Absolute beta moments of the Gauss series are summable when `2 Re a < Re h + 1`. -/
lemma summable_integral_norm_square_term {a h : ℂ} (hh : 0 < h.re)
    (ha : 2*a.re < h.re+1) :
    Summable (fun n : ℕ => ∫ t : ℝ in 0..1,
      ‖squareCoeff a n * (t:ℂ)^n * (1-(t:ℂ))^(h-1)‖) := by
  have hs := (hasSum_regularizedGauss_one (a := a) (b := conj a)
    (c := ((h.re+1:ℝ):ℂ)) (by simp; linarith)).summable.norm
  refine (hs.mul_left (Real.Gamma h.re)).congr fun n => ?_
  rw [integral_norm_square_term a h hh,norm_regularized_coefficient a hh]
  rw [squareCoeff,norm_div,norm_pow,norm_pow,norm_natCast,Real.Gamma_nat_eq_factorial]
  have hn : (n.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp


/-- A beta-weighted integral of `F̃(a,a;1;t)`, allowing an inner series singular at one. -/
lemma square_gauss_moment {a h : ℂ} (hh : 0 < h.re) (ha : 2*a.re < h.re+1) :
    (∫ t : ℝ in 0..1, regularizedGaussHGFun a a 1 t * (1-(t:ℂ))^(h-1)) =
      Gamma h * Gamma (h+1-2*a) / Gamma (h+1-a)^2 := by
  let F : ℕ → ℝ → ℂ := fun n t => squareCoeff a n * (t:ℂ)^n * (1-(t:ℂ))^(h-1)
  have hi (n : ℕ) : IntervalIntegrable (F n) volume 0 1 := by
    have hb := (betaIntegral_convergent (u := (n:ℂ)+1) (v := h)
      (by simp; positivity) hh).const_mul (squareCoeff a n)
    convert hb using 1
    funext t
    dsimp [F]
    rw [show (n:ℂ)+1-1 = n by ring,cpow_natCast]
    ring
  have hnorm := summable_integral_norm_square_term hh ha
  simp only [intervalIntegral.integral_of_le zero_le_one] at hnorm
  have hs := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Ioc (0:ℝ) 1))
    (fun n => (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hi n)) hnorm
  have hfun : (fun t : ℝ => ∑' n, F n t) =ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
      (fun t => regularizedGaussHGFun a a 1 t * (1-(t:ℂ))^(h-1)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
    filter_upwards [volume.ae_ne (1:ℝ)] with t ht hmem
    have ht' : ‖(t:ℂ)‖ < 1 := by
      rw [norm_real,Real.norm_of_nonneg hmem.1.le]
      exact lt_of_le_of_ne hmem.2 ht
    have hf := (hasSum_regularizedGaussHypergeometricFun_coeff a a 1 ht').mul_right
      ((1-(t:ℂ))^(h-1))
    have hF : HasSum (fun n => F n t)
        (regularizedGaussHGFun a a 1 t * (1-(t:ℂ))^(h-1)) := by
      convert hf using 1
      funext n
      dsimp [F,squareCoeff]
      rw [show (1:ℂ)+n = (n:ℂ)+1 by ring,Gamma_nat_eq_factorial]
      ring
    exact hF.tsum_eq
  rw [integral_congr_ae hfun] at hs
  have hterm (n : ℕ) : (∫ t : ℝ in Ioc (0:ℝ) 1, F n t) =
      Gamma h * (pochhammer a n * pochhammer a n /
        ((n.factorial:ℂ)*Gamma (h+1+n))) := by
    have hn : 0 < ((n:ℂ)+1).re := by simp; positivity
    have hnh : Gamma ((n:ℂ)+1+h) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hb := Gamma_mul_Gamma_eq_betaIntegral hn hh
    have hbeta : betaIntegral ((n:ℂ)+1) h =
        Gamma ((n:ℂ)+1)*Gamma h/Gamma ((n:ℂ)+1+h) := by
      rw [eq_div_iff hnh,mul_comm]
      exact hb.symm
    have he : (∫ t : ℝ in Ioc (0:ℝ) 1, F n t) =
        squareCoeff a n * betaIntegral ((n:ℂ)+1) h := by
      rw [betaIntegral,←intervalIntegral.integral_const_mul,
        intervalIntegral.integral_of_le zero_le_one]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t _
      dsimp [F]
      rw [show (n:ℂ)+1-1 = n by ring,cpow_natCast]
      ring
    rw [he,hbeta,Gamma_nat_eq_factorial,squareCoeff,
      show (n:ℂ)+1+h = h+1+n by ring]
    have hn0 : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  simp_rw [hterm] at hs
  have hgap : 0 < (h+1-a-a).re := by simp; linarith
  have hG := (hasSum_regularizedGauss_one (a := a) (b := a) (c := h+1) hgap).mul_left (Gamma h)
  have he := hs.unique hG
  rw [←intervalIntegral.integral_of_le zero_le_one] at he
  rw [show h+1-a-a = h+1-2*a by ring] at he
  simpa only [pow_two,mul_div_assoc] using he


/-- Pfaff's transformation maps the negative half-line onto the unit interval. -/
lemma pfaff_positive (a : ℂ) {u : ℝ} (hu : 0 < u) :
    regularizedGaussHypergeometric a (1-a) 1 (-u) =
      (1+(u:ℂ))^(-a) * regularizedGaussHGFun a a 1 (u/(1+u)) := by
  have hz : -(u:ℂ) ∈ cutPlane := Or.inl (by simp; linarith)
  have hq : ‖((u/(1+u):ℝ):ℂ)‖ < 1 := by
    rw [norm_real,Real.norm_of_nonneg (by positivity)]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  rw [regularizedGaussHypergeometric_pfaff _ _ _ hz,sub_neg_eq_add,
    show (1:ℂ)-(1-a) = a by ring,
    show -(u:ℂ)/(-(u:ℂ)-1) = ((u/(1+u):ℝ):ℂ) by
      push_cast
      rw [show -(u:ℂ)-1 = -(1+(u:ℂ)) by ring,neg_div_neg_eq],
    regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hq]
  push_cast
  rfl


/-- The substitution `q = u/(1+u)` gives the weighted negative-axis Gauss moments. -/
lemma symmetric_gauss_moment_transform (a : ℂ) (n : ℕ) :
    (∫ u : ℝ in Ioi 0, regularizedGaussHypergeometric a (1-a) 1 (-(u:ℂ)) /
      (1+(u:ℂ))^(n+1)) =
    ∫ q : ℝ in Ioo 0 1,
      regularizedGaussHGFun a a 1 q * (1-(q:ℂ))^(a+n-1) := by
  let g : ℝ → ℂ := fun q => regularizedGaussHGFun a a 1 q * (1-(q:ℂ))^(a+n-1)
  have hf := integral_comp_div_one_add_Ioi g
  have hpoint : ∀ u ∈ Ioi (0:ℝ), (1/(1+u)^2) • g (u/(1+u)) =
      regularizedGaussHypergeometric a (1-a) 1 (-(u:ℂ)) / (1+(u:ℂ))^(n+1) := by
    intro u hu
    have hu' : 0 < u := hu
    have hb : 1+(u:ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1+u:ℝ) ≠ 0)
    have hq : (1:ℂ)-((u/(1+u):ℝ):ℂ) = (1+(u:ℂ))⁻¹ := by
      push_cast
      field_simp
      ring
    have hi : (1+(u:ℂ))⁻¹^(a+n-1) = (1+(u:ℂ))^(-(a+n-1)) := by
      rw [show 1+(u:ℂ) = ((1+u:ℝ):ℂ) by push_cast; rfl,
        inv_cpow_ofReal_nonneg (by linarith),cpow_neg]
    have hp : (1+(u:ℂ))^(-a)/(1+(u:ℂ))^(n+1) =
        (1+(u:ℂ))^(-2:ℂ) * (1+(u:ℂ))^(-(a+n-1)) := by
      rw [←cpow_natCast,←cpow_sub _ _ hb,←cpow_add _ _ hb]
      congr 1
      push_cast
      ring
    have hj : ((1+(u:ℂ))^2)⁻¹ = (1+(u:ℂ))^(-2:ℂ) := by
      rw [cpow_neg,cpow_ofNat]
    dsimp [g]
    rw [hq,hi,pfaff_positive a hu']
    simp only [ofReal_div,ofReal_one,ofReal_pow,ofReal_add]
    rw [one_div,hj]
    calc _ = ((1+(u:ℂ))^(-2:ℂ) * (1+(u:ℂ))^(-(a+n-1))) *
        regularizedGaussHGFun a a 1 (u/(1+u)) := by ring
      _ = _ := by rw [←hp];ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint] at hf
  exact hf

/-- The negative-axis moments of `F̃(a,1-a;1;-u)` for `0 < Re a < 1`. -/
lemma symmetric_gauss_moment {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1) (n : ℕ) :
    (∫ u : ℝ in Ioi 0, regularizedGaussHypergeometric a (1-a) 1 (-(u:ℂ)) /
      (1+(u:ℂ))^(n+1)) =
      Gamma (a+n)*Gamma (1-a+n)/(n.factorial:ℂ)^2 := by
  rw [symmetric_gauss_moment_transform,←integral_Ioc_eq_integral_Ioo,
    ←intervalIntegral.integral_of_le zero_le_one]
  have hh : 0 < (a+(n:ℂ)).re := by simp; positivity
  have hb : 2*a.re < (a+(n:ℂ)).re+1 := by
    simp only [add_re,natCast_re]
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  rw [square_gauss_moment hh hb,
    show a+(n:ℂ)+1-2*a = 1-a+n by ring,
    show a+(n:ℂ)+1-a = (n:ℂ)+1 by ring,Gamma_nat_eq_factorial]



/-- The weighted principal Gauss kernel `F̃(a,1-a;1;-u)/(1+u)`, totalized for real `u`. -/
def stieltjesBase (a : ℂ) (u : ℝ) : ℂ :=
  regularizedGaussHypergeometric a (1-a) 1 (-(u:ℂ)) / (1+(u:ℂ))

/-- The totalized positive-half-line Stieltjes transform of the principal Gauss kernel. -/
def stieltjesTransform (a z : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi 0, regularizedGaussHypergeometric a (1-a) 1 (-(u:ℂ)) /
    ((u:ℂ)+(1+z))

/-- The weighted Gauss kernel is integrable when `0 < Re a < 1`. -/
lemma integrable_stieltjesBase {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1) :
    IntegrableOn (stieltjesBase a) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  have hm := symmetric_gauss_moment ha0 ha1 0
  simp only [Nat.cast_zero,zero_add,add_zero,Nat.factorial_zero,Nat.cast_one,one_pow,
    pow_one,div_one] at hm
  rw [show (∫ u : ℝ in Ioi 0, stieltjesBase a u) = Gamma a*Gamma (1-a) by exact hm]
  exact mul_ne_zero (Gamma_ne_zero_of_re_pos ha0)
    (Gamma_ne_zero_of_re_pos (by simp; linarith))

/-- The weighted Gauss resolvent remains integrable for a positive real shift. -/
lemma integrable_stieltjesBase_div {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => stieltjesBase a u / ((u:ℂ)+(1+x))) (Ioi 0) := by
  have hg := integrable_stieltjesBase ha0 ha1
  refine hg.norm.mono' ?_ ?_
  · exact hg.aestronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu : 0 < u := hu
    have hden : 1 ≤ u+(1+x) := by linarith [hu]
    rw [norm_div,show (u:ℂ)+(1+x) = ((u+(1+x):ℝ):ℂ) by push_cast; rfl,
      norm_real,Real.norm_of_nonneg (by linarith)]
    exact div_le_self (norm_nonneg _) hden


/-- A geometric resolvent expansion proves the self-transform identity for `0 < x < 1`. -/
lemma stieltjesTransform_eq_small {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    stieltjesTransform a x = Gamma a * Gamma (1-a) *
      regularizedGaussHypergeometric a (1-a) 1 (-(x:ℂ)) := by
  let F : ℕ → ℝ → ℂ := fun n u => (-(x:ℂ)/(1+(u:ℂ)))^n * stieltjesBase a u
  have hg := integrable_stieltjesBase ha0 ha1
  have hgeom : Summable (fun n : ℕ => x^n) := summable_geometric_of_norm_lt_one
    (by rw [Real.norm_eq_abs,abs_of_pos hx0];exact hx1)
  have hn (u : ℝ) (hu : 0 < u) : ‖-(x:ℂ)/(1+(u:ℂ))‖ ≤ x := by
    rw [norm_div,norm_neg,norm_real,Real.norm_of_nonneg hx0.le,
      show 1+(u:ℂ) = ((1+u:ℝ):ℂ) by push_cast;rfl,
      norm_real,Real.norm_of_nonneg (by linarith)]
    exact div_le_self hx0.le (by linarith)
  have hs := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := F) (f := fun u => regularizedGaussHypergeometric a (1-a) 1 (-(u:ℂ)) /
      ((u:ℂ)+(1+x))) (fun n u => x^n * ‖stieltjesBase a u‖)
    (fun n => (Measurable.aestronglyMeasurable (by fun_prop)).mul hg.aestronglyMeasurable)
    (fun n => ?_) (Eventually.of_forall fun u => hgeom.mul_right ‖stieltjesBase a u‖)
    (by simp_rw [tsum_mul_right];exact hg.norm.const_mul _) ?_
  · have hterm (n : ℕ) : (∫ u : ℝ in Ioi 0, F n u) =
        (Gamma a * Gamma (1-a)) *
          (pochhammer a n * pochhammer (1-a) n / ((n.factorial:ℂ)*Gamma (1+n)) *
            (-(x:ℂ))^n) := by
      calc _ = (-(x:ℂ))^n * (∫ u : ℝ in Ioi 0,
          regularizedGaussHypergeometric a (1-a) 1 (-(u:ℂ)) / (1+(u:ℂ))^(n+1)) := by
            rw [←integral_const_mul]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro u _
            dsimp [F,stieltjesBase]
            simp only [pow_succ,div_eq_mul_inv,mul_inv_rev]
            ring
        _ = _ := by
          rw [symmetric_gauss_moment ha0 ha1]
          have hGa : Gamma (a+n) = pochhammer a n * Gamma a :=
            (div_eq_iff (Gamma_ne_zero_of_re_pos ha0)).mp
              (Gamma_add_nat_div_Gamma_eq (n := n) a (not_neg_nat_of_re_pos ha0))
          have hb : 0 < (1-a).re := by simp;linarith
          have hGb : Gamma (1-a+n) = pochhammer (1-a) n * Gamma (1-a) :=
            (div_eq_iff (Gamma_ne_zero_of_re_pos hb)).mp
              (Gamma_add_nat_div_Gamma_eq (n := n) (1-a) (not_neg_nat_of_re_pos hb))
          rw [hGa,hGb,show (1:ℂ)+n = (n:ℂ)+1 by ring,Gamma_nat_eq_factorial]
          ring
    simp_rw [hterm] at hs
    have hx : ‖-(x:ℂ)‖ < 1 := by
      rw [norm_neg,norm_real,Real.norm_of_nonneg hx0.le]
      exact hx1
    have hF := (hasSum_regularizedGaussHypergeometricFun_coeff a (1-a) 1 hx).mul_left
      (Gamma a*Gamma (1-a))
    have he := hs.unique hF
    unfold stieltjesTransform
    rw [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hx]
    exact he
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu : 0 < u := hu
    dsimp [F]
    rw [norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hn u hu) n)
      (norm_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu : 0 < u := hu
    have hr : ‖-(x:ℂ)/(1+(u:ℂ))‖ < 1 := (hn u hu).trans_lt hx1
    have ht := (hasSum_geometric_of_norm_lt_one hr).mul_right (stieltjesBase a u)
    convert ht using 1
    dsimp [stieltjesBase]
    have h0 : 1+(u:ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1+u:ℝ) ≠ 0)
    have h1 : (u:ℂ)+(1+x) ≠ 0 := by exact_mod_cast (by linarith : (u+(1+x):ℝ) ≠ 0)
    have h2 : (1:ℂ)+u+x ≠ 0 := by
      simpa only [add_assoc,add_comm,add_left_comm] using h1
    field_simp [h0,h2]
    ring


/-- The Gauss Stieltjes kernel is absolutely integrable for every positive real shift. -/
lemma integrable_stieltjes_kernel {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ =>
      regularizedGaussHypergeometric a (1-a) 1 (-(u:ℂ)) / ((u:ℂ)+(1+x))) (Ioi 0) := by
  have hg := integrable_stieltjesBase ha0 ha1
  have hd := integrable_stieltjesBase_div ha0 ha1 hx
  refine (hg.sub (hd.const_mul (x:ℂ))).congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu : 0 < u := hu
  have h0 : 1+(u:ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1+u:ℝ) ≠ 0)
  have h1 : (u:ℂ)+(1+x) ≠ 0 := by exact_mod_cast (by linarith : (u+(1+x):ℝ) ≠ 0)
  dsimp [stieltjesBase]
  field_simp
  ring

/-- The Gauss Stieltjes transform is holomorphic on the right half-plane. -/
lemma differentiableOn_stieltjesTransform {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1) :
    DifferentiableOn ℂ (stieltjesTransform a) {z : ℂ | 0 < z.re} := by
  have hg := integrable_stieltjesBase ha0 ha1
  have hS := DLMF.Confluent.KummerIntegrals.differentiableOn_stieltjes
    (g := fun u : ℝ => regularizedGaussHypergeometric a (1-a) 1 (-(u:ℂ)))
    (by
      convert hg using 1
      funext u
      dsimp [stieltjesBase]
      rw [add_comm])
  intro z hz
  have hz0 : 0 < z.re := hz
  have hz1 : 1+z ∈ slitPlane := Or.inl (by simp;linarith [hz0])
  have hAt := hS.differentiableAt (isOpen_slitPlane.mem_nhds hz1)
  simpa only [stieltjesTransform,Function.comp_def] using!
    (hAt.comp z
      ((differentiableAt_const (c := (1:ℂ))).add differentiableAt_id)).differentiableWithinAt

/-- Analytic uniqueness extends the Gauss self-transform identity to every `x > 0`. -/
lemma stieltjesTransform_eq {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1)
    {x : ℝ} (hx : 0 < x) :
    stieltjesTransform a x = Gamma a * Gamma (1-a) *
      regularizedGaussHypergeometric a (1-a) 1 (-(x:ℂ)) := by
  let D : Set ℂ := {z : ℂ | 0 < z.re}
  have hDo : IsOpen D := isOpen_lt continuous_const continuous_re
  have hDp : IsPreconnected D := (convex_halfSpace_re_gt 0).isPreconnected
  have hM : AnalyticOnNhd ℂ (stieltjesTransform a) D :=
    (differentiableOn_stieltjesTransform ha0 ha1).analyticOnNhd hDo
  have hG : AnalyticOnNhd ℂ (fun z : ℂ => Gamma a * Gamma (1-a) *
      regularizedGaussHypergeometric a (1-a) 1 (-z)) D := by
    apply DifferentiableOn.analyticOnNhd _ hDo
    intro z hz
    have hz0 : 0 < z.re := hz
    have hz' : -z ∈ cutPlane := Or.inl (by simp;linarith [hz0])
    exact ((differentiableAt_const (c := Gamma a*Gamma (1-a))).mul
      ((differentiableAt_regularizedGaussHypergeometric a (1-a) 1 hz').comp z
        differentiableAt_id.neg)).differentiableWithinAt
  have ht : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[≠] (1/2:ℝ)) (𝓝[≠] ((1/2:ℝ):ℂ)) :=
    (continuous_ofReal.tendsto _).inf (tendsto_principal_principal.mpr fun t ht =>
      fun h => ht (ofReal_injective h))
  have hf : ∃ᶠ z in 𝓝[≠] (((1/2:ℝ):ℂ)), stieltjesTransform a z =
      Gamma a * Gamma (1-a) * regularizedGaussHypergeometric a (1-a) 1 (-z) := by
    apply ht.frequently
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (1/2:ℝ), stieltjesTransform a t =
        Gamma a * Gamma (1-a) * regularizedGaussHypergeometric a (1-a) 1 (-(t:ℂ)) := by
      apply eventually_nhdsWithin_of_eventually_nhds
      filter_upwards [Ioo_mem_nhds (by norm_num : (0:ℝ)<1/2)
        (by norm_num : (1/2:ℝ)<1)] with t ht
      exact stieltjesTransform_eq_small ha0 ha1 ht.1 ht.2
    exact hev.frequently
  exact hM.eqOn_of_preconnected_of_frequently_eq hG hDp
    (by norm_num [D]) hf (by exact hx)

/-- The self-Stieltjes identity for `F̃(a,1-a;1;-x)` on the positive real axis. -/
lemma symmetric_stieltjes {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1)
    {x : ℝ} (hx : 0 < x) :
    (∫ u : ℝ in Ioi 0,
      regularizedGaussHypergeometric a (1-a) 1 (-(u:ℂ)) / ((u:ℂ)+(1+x))) =
      Gamma a * Gamma (1-a) * regularizedGaussHypergeometric a (1-a) 1 (-(x:ℂ)) := by
  exact stieltjesTransform_eq ha0 ha1 hx



end DLMF.Hypergeometric.GaussMoments
