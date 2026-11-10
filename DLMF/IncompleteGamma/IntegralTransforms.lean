/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.Zeros
public import DLMF.Zeta.HurwitzEulerMaclaurin

/-!
# Transforms, sums and approximations of incomplete Gamma functions

Laplace and Mellin transforms of the incomplete Gamma functions (DLMF §8.14), the
multiplication and Fourier sums of DLMF §8.15, and DiDonato's approximation from DLMF §8.27(i).
The inherited logarithms and a right-half-plane domain are explicit in the Fourier sum.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Statistical

/-- The lower Gamma in the exponentially weighted regularized Kummer normalization. -/
theorem lowerIncompleteGamma_eq_exp_regularized {b : ℂ} (hb : ∀ k : ℕ, b≠-k) (x : ℂ) :
    lowerIncompleteGamma b x=Gamma b*x^b*exp (-x)*regularizedHGFun {1} {b+1} x := by
  rw [lowerIncompleteGamma_eq_regularized hb,
    regularizedConfluent_kummer_transform b (b+1) (-x)]
  simp only [show b+1-b=1 by ring, neg_neg]
  ring

/-- Identity under the stated parameter and domain assumptions: `(∫ x : ℝ in Ioi 0, exp
(-a*x)*regularizedGamma b x)=(1+a)^(-b)/a`. -/
@[dlmf 8.14.E1]
theorem regularizedGamma_laplace {a b : ℂ} (ha : 0 < a.re) (hb : -1 < b.re) :
    (∫ x : ℝ in Ioi 0, exp (-a*x)*regularizedGamma b x)=(1+a)^(-b)/a := by
  have ha0 := ne_zero_of_re_pos ha
  have ha1 : 1+a≠0 := ne_zero_of_re_pos (by simp; linarith)
  have hi : (∫ x : ℝ in Ioi 0, exp (-a*x)*regularizedGamma b x)=
      ∫ x : ℝ in Ioi 0, exp (-(1+a)*x)*(x:ℂ)^((b+1)-1)*regularizedHGFun {1} {b+1} x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [regularizedGamma,tricomiIncompleteGamma, add_sub_cancel_right]
    have he : exp (-a*x)*exp (-(x:ℂ))=exp (-(1+a)*x) := by rw [← Complex.exp_add]; congr 1; ring
    linear_combination (x:ℂ)^b*regularizedHGFun {1} {b+1} x*he
  rw [hi,laplace_regularizedHGFun_self (by simp; linarith) (by simp; linarith),
    show -(b+1)= -b-1 by ring, cpow_sub _ _ ha1, cpow_one, cpow_neg_one]
  field_simp [ha0]
  ring

/-- Identity under the stated parameter and domain assumptions: `(∫ x : ℝ in Ioi 0, exp
(-a*x)*upperIncompleteGamma b x)=if a=0 then Gamma (b+1) else if b=0 then log (1+a)/a else Gamma
b*(1-(1+a)^(-b))/a`. -/
@[dlmf 8.14.E2]
theorem upperIncompleteGamma_laplace {a b : ℂ} (ha : -1 < a.re) (hb : -1 < b.re) :
    (∫ x : ℝ in Ioi 0, exp (-a*x)*upperIncompleteGamma b x)=if a=0 then Gamma (b+1) else if b=0 then
        log (1+a)/a else Gamma b*(1-(1+a)^(-b))/a := by
  have hm := (laplace_kummerU_gauss (a:=1-b) (b:=1) (c:=1-b) (z:=1+a)
    (by simp) (by simp only [sub_re,one_re]; linarith) (by simp; linarith)).2
  have hi : (∫ x : ℝ in Ioi 0, exp (-a*x)*upperIncompleteGamma b x)=
      ∫ x : ℝ in Ioi 0, tricomiLaplaceKernel (1-b) 1 (1-b) (1+a) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [upperIncompleteGamma,tricomiLaplaceKernel]
    simp only [sub_self,cpow_zero,mul_one]
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    ring
  rw [hi,hm,show 1-(1-b)+1=b+1 by ring,show (1-b)+1-(1-b)+1=(2:ℂ) by ring,
    show 1-(1+a)= -a by ring,Gamma_one,one_mul]
  have hcut : -a∈cutPlane := by change 1-(-a)∈slitPlane; left; simp; linarith
  rw [regularizedGaussHypergeometric_symm 1 (b+1) 2 hcut,
    regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral (by norm_num)
        (by norm_num) hcut]
  simp only [regularizedGaussHypergeometricIntegral,eulerKernel,sub_self,cpow_zero,one_mul,
    show (2:ℂ)-1-1=0 by ring,show (2:ℂ)-1=1 by ring,Gamma_one,inv_one]
  simp_rw [show ∀ t : ℝ, 1-(-a)*(t:ℂ)=1+a*t by intro t; ring]
  have hslit (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : 1+a*(t:ℂ)∈slitPlane := by
    left
    simp only [add_re,one_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
    by_cases h : 0≤a.re
    · nlinarith [mul_nonneg h ht.1]
    · have hp := mul_nonneg (show 0≤ -a.re by linarith) (show 0≤1-t by linarith [ht.2])
      nlinarith
  have hcont : ContinuousOn (fun t : ℝ => (1+a*(t:ℂ))^(-(b+1))) (Icc (0:ℝ) 1) :=
    (by fun_prop : Continuous (fun t : ℝ => 1+a*(t:ℂ))).continuousOn.cpow_const hslit
  have hint : IntervalIntegrable (fun t : ℝ => (1+a*(t:ℂ))^(-(b+1))) volume 0 1 :=
      hcont.intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
  by_cases ha0 : a=0
  · subst a
    simp
  rw [if_neg ha0]
  by_cases hb0 : b=0
  · subst b
    rw [if_pos rfl]
    norm_num only [zero_add,Gamma_one,one_mul,neg_add_rev,neg_zero,add_zero] at *
    have hd (t : ℝ) (ht : t∈uIcc (0:ℝ) 1) :
        HasDerivAt (fun u : ℝ => log (1+a*(u:ℂ))/a) ((1+a*(t:ℂ))^(-1:ℂ)) t := by
      have ht' : t∈Icc (0:ℝ) 1 := by simpa using ht
      have h := (((hasDerivAt_id (t:ℂ)).const_mul a).const_add 1).clog (hslit t ht')
      have h' := (h.div_const a).comp_ofReal
      refine (h'.congr_of_eventuallyEq (Eventually.of_forall fun u=>rfl)).congr_deriv ?_
      simp only [id_eq,mul_one,cpow_neg_one]
      field_simp
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
    simpa using hh
  rw [if_neg hb0]
  have hd (t : ℝ) (ht : t∈uIcc (0:ℝ) 1) :
      HasDerivAt (fun u : ℝ => (1+a*(u:ℂ))^(-b)/(-a*b)) ((1+a*(t:ℂ))^(-(b+1))) t := by
    have ht' : t∈Icc (0:ℝ) 1 := by simpa using ht
    have h := (((hasDerivAt_id (t:ℂ)).const_mul a).const_add 1).cpow_const (c:= -b) (hslit t ht')
    have h' := (h.div_const (-a*b)).comp_ofReal
    refine (h'.congr_of_eventuallyEq (Eventually.of_forall fun u=>rfl)).congr_deriv ?_
    simp only [id_eq,mul_one]
    rw [show -b-1= -(b+1) by ring]
    field_simp
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,add_zero,one_cpow] at hh
  rw [hh,Gamma_add_one b hb0]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `(∫ x : ℝ in Ioi 0, (x :
ℂ)^(a-1)*lowerIncompleteGamma b x) = -Gamma (a+b)/a`. -/
@[dlmf 8.14.E3]
theorem lowerIncompleteGamma_mellin {a b : ℂ} (ha : a.re < 0) (hab : 0 < (a+b).re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*lowerIncompleteGamma b x) = -Gamma (a+b)/a := by
  have hbpos : 0<b.re := by simp only [add_re] at hab; linarith
  have hb := not_neg_nat_of_re_pos hbpos
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*lowerIncompleteGamma b x)=Gamma b*
      ∫ x : ℝ in Ioi 0, exp (-(x:ℂ))*(x:ℂ)^((a+b)-1)*regularizedHGFun {1} {b+1} x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [lowerIncompleteGamma_eq_exp_regularized hb]
    have hp : (x:ℂ)^(a-1)*(x:ℂ)^b=(x:ℂ)^((a+b)-1) := by
      rw [← cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]; congr 1; ring
    linear_combination Gamma b*exp (-(x:ℂ))*regularizedHGFun {1} {b+1} x*hp
  rw [hi,mellin_regularizedHGFun_exp hab (by simp only [add_re,sub_re,one_re]; linarith)]
  rw [show b+1-1-(a+b)= -a by ring, show b+1-1=b by ring,
    show b+1-(a+b)= -a+1 by ring, Gamma_add_one (-a) (by intro h; simp at h; simp [h] at ha)]
  have hg := Gamma_ne_zero_of_re_pos hbpos
  have hga := Gamma_ne_zero_of_re_pos (show 0<(-a).re by simpa)
  field_simp

/-- Identity under the stated parameter and domain assumptions: `(∫ x : ℝ in Ioi 0, (x :
ℂ)^(a-1)*upperIncompleteGamma b x)=Gamma (a+b)/a`. -/
@[dlmf 8.14.E4]
theorem upperIncompleteGamma_mellin {a b : ℂ} (ha : 0 < a.re) (hab : 0 < (a+b).re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*upperIncompleteGamma b x)=Gamma (a+b)/a := by
  have hm := (laplace_kummerU_gauss (a:=1-b) (b:=a) (c:=1-b) (z:=1)
    ha (by simp only [sub_re,one_re]; simp only [add_re] at hab; linarith) (by simp)).2
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*upperIncompleteGamma b x)=
      ∫ x : ℝ in Ioi 0, tricomiLaplaceKernel (1-b) a (1-b) 1 x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    simp only [upperIncompleteGamma,tricomiLaplaceKernel,one_mul]
    ring
  rw [hi,hm]
  rw [show a-(1-b)+1=a+b by ring, show 1-b+a-(1-b)+1=a+1 by ring]
  simp only [sub_self]
  rw [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ (by simp)]
  rw [regularizedGaussHypergeometricFun_eq_div_Gamma (not_neg_nat_of_re_pos (by simp; linarith))]
  simp only [ordinaryHypergeometric_zero]
  rw [Gamma_add_one a (ne_zero_of_re_pos ha)]
  field_simp [Gamma_ne_zero_of_re_pos ha]

/-- Identity under the stated parameter and domain assumptions: `(∫ x : ℝ in Ioi 0, (x :
ℂ)^(a-1)*exp (-s*x)*lowerIncompleteGamma b x)=Gamma (a+b)/(b*(1+s)^(a+b))*Gamma
(1+b)*DLMF.Hypergeometric.regularizedGaussHypergeometric 1 (a+b) (1+b) (1/(1+s))`. -/
@[dlmf 8.14.E5]
theorem lowerIncompleteGamma_mellin_laplace {a b s : ℂ} (hs : 0 < s.re) (hab : 0 < (a+b).re)
    (hb : ∀ n : ℕ, b ≠ -n) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*exp (-s*x)*lowerIncompleteGamma b x)=Gamma
        (a+b)/(b*(1+s)^(a+b))*Gamma
        (1+b)*DLMF.Hypergeometric.regularizedGaussHypergeometric 1 (a+b) (1+b) (1/(1+s)) := by
  have hm := laplace_regularizedHGFun (a:=1) (b:=a+b) (c:=b+1) (k:=1) (z:=1+s)
    hab (by simp; linarith) (by simp; linarith)
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*exp (-s*x)*lowerIncompleteGamma b x)=Gamma b*
      ∫ x : ℝ in Ioi 0, exp (-(1+s)*x)*(x:ℂ)^((a+b)-1)*regularizedHGFun {1} {b+1} (1*x) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [lowerIncompleteGamma_eq_exp_regularized hb]
    have hp : (x:ℂ)^(a-1)*(x:ℂ)^b=(x:ℂ)^((a+b)-1) := by
      rw [← cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]; congr 1; ring
    have he : exp (-s*x)*exp (-(x:ℂ))=exp (-(1+s)*x) := by rw [← Complex.exp_add]; congr 1; ring
    simp only [one_mul]
    calc
      _ = Gamma b*((x:ℂ)^(a-1)*(x:ℂ)^b)*(exp (-s*x)*exp (-(x:ℂ)))*regularizedHGFun {1}
          {b+1} x := by ring
      _ = _ := by rw [hp,he]; ring
  rw [hi,hm,show (1:ℂ)+b=b+1 by ring, Gamma_add_one b (by simpa using hb 0), cpow_neg]
  field_simp [show b≠0 by simpa using hb 0]

/-- Identity under the stated parameter and domain assumptions: `(∫ x : ℝ in Ioi 0, (x :
ℂ)^(a-1)*exp (-s*x)*upperIncompleteGamma b x)=Gamma (a+b)/(a*(1+s)^(a+b))*Gamma
(1+a)*DLMF.Hypergeometric.regularizedGaussHypergeometric 1 (a+b) (1+a) (s/(1+s))`. -/
@[dlmf 8.14.E6]
theorem upperIncompleteGamma_mellin_laplace {a b s : ℂ} (hs : -1 < s.re) (hab : 0 < (a+b).re)
    (ha : 0 < a.re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*exp (-s*x)*upperIncompleteGamma b x)=Gamma
        (a+b)/(a*(1+s)^(a+b))*Gamma
        (1+a)*DLMF.Hypergeometric.regularizedGaussHypergeometric 1 (a+b) (1+a) (s/(1+s)) := by
  have hm := (laplace_kummerU_gauss (a:=1) (b:=a+b) (c:=b+1) (z:=1+s)
    hab (by simp only [add_re,sub_re,one_re]; linarith) (by simp; linarith)).2
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*exp (-s*x)*upperIncompleteGamma b x)=
      ∫ x : ℝ in Ioi 0, tricomiLaplaceKernel 1 (a+b) (b+1) (1+s) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [upperIncompleteGamma_eq_cpow_mul_kummerU _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]
    unfold tricomiLaplaceKernel
    have hp : (x:ℂ)^(a-1)*(x:ℂ)^b=(x:ℂ)^((a+b)-1) := by
      rw [← cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]; congr 1; ring
    have he : exp (-s*x)*exp (-(x:ℂ))=exp (-(1+s)*x) := by rw [← Complex.exp_add]; congr 1; ring
    calc
      _ = ((x:ℂ)^(a-1)*(x:ℂ)^b)*(exp (-s*x)*exp (-(x:ℂ)))*kummerU 1 (b+1) x := by ring
      _ = _ := by rw [hp,he]; ring
  rw [hi,hm,show a+b-(b+1)+1=a by ring, show 1+(a+b)-(b+1)+1=a+1 by ring,
    show 1-(1+s)= -s by ring]
  have hcut : -s∈cutPlane := by change 1-(-s)∈slitPlane; left; simp; linarith
  rw [regularizedGaussHypergeometric_pfaff (a+b) a (a+1) hcut,
    show (a+1)-a=1 by ring, show 1-(-s)=1+s by ring,
    show (-s)/(-s-1)=s/(1+s) by rw [show -s-1= -(1+s) by ring, neg_div_neg_eq]]
  have hmap : s/(1+s)∈cutPlane := by
    convert div_sub_one_mem_cutPlane hcut using 1
    rw [show -s-1= -(1+s) by ring, neg_div_neg_eq]
  rw [regularizedGaussHypergeometric_symm (a+b) 1 (a+1) hmap]
  rw [show (1:ℂ)+a=a+1 by ring,Gamma_add_one a (ne_zero_of_re_pos ha),cpow_neg]
  field_simp [ne_zero_of_re_pos ha]

/-- The series with terms `(fun k : ℕ => exp (a*v)*lowerIncompleteGammaOnLog (a+k) u*(1-exp
v)^k/(k.factorial : ℂ))` converges to `(lowerIncompleteGammaOnLog a (u+v))`. -/
@[dlmf 8.15.E1]
theorem lowerIncompleteGamma_multiplication_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (u v : ℂ) :
    HasSum (fun k : ℕ => exp (a*v)*lowerIncompleteGammaOnLog (a+k) u*(1-exp v)^k/(k.factorial : ℂ))
        (lowerIncompleteGammaOnLog a (u+v)) := by
  have hsc (b z : ℂ) : tricomiIncompleteGamma b z = regularizedHGFun {b} {b+1} (-z) := by
    simpa only [add_comm 1 b] using (tricomiIncompleteGamma_regularized_pair b z).2
  have hf : Differentiable ℂ (regularizedHGFun {a} {a+1}) :=
    fun z => differentiableAt_regularizedConfluent _ _ z
  have ht := (Complex.hasSum_taylorSeries_of_entire hf (-exp u) (-exp (u+v))).mul_left
    (Gamma a * exp (a*(u+v)))
  have hv : Gamma a * exp (a*(u+v)) * regularizedHGFun {a} {a+1} (-exp (u+v)) =
      lowerIncompleteGammaOnLog a (u+v) := by
    rw [lowerIncompleteGammaOnLog, hsc]
  rw [hv] at ht
  refine ht.congr_fun fun k => ?_
  rw [iteratedDeriv_regularizedConfluent,
    show a+1+(k:ℂ) = (a+k)+1 by ring,
    ← hsc]
  have hg : Gamma a * pochhammer a k = Gamma (a+k) := by
    rw [pochhammer, ← Gamma_add_nat_div_Gamma_eq a ha]
    field_simp [Gamma_ne_zero ha]
  have he : exp (a*(u+v)) * exp u ^ k = exp (a*v) * exp ((a+k)*u) := by
    rw [← exp_nat_mul, ← exp_add, ← exp_add]
    congr 1
    ring
  have hd : -exp (u+v) - -exp u = exp u * (1-exp v) := by
    rw [exp_add]
    ring
  simp only [smul_eq_mul, hd, mul_pow, lowerIncompleteGammaOnLog]
  symm
  calc
    _ = (Gamma a * pochhammer a k) * (exp (a*(u+v)) * exp u ^ k) *
        tricomiIncompleteGamma (a+k) (exp u) * (1-exp v)^k / k.factorial := by ring
    _ = _ := by rw [hg, he]; ring

-- `hurwitzZetaComplex` (Euler–Maclaurin continuation) is defined in `DLMF.Zeta.Basic.Hurwitz`.

/-- Bridge to Mathlib; its existing Hurwitz zeta is periodic in a real second argument. -/
theorem hurwitzZetaComplex_mathlib {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {s : ℂ} (hs : s ≠ 1) :
    DLMF.Zeta.hurwitzZetaComplex s x=HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s :=
  DLMF.Zeta.hurwitzZetaComplex_eq_hurwitzZeta hx hx1 hs

/-- Inherited logarithms and a right-half-plane convergence domain are explicit. -/
@[dlmf 8.15.E2]
theorem incompleteGamma_hurwitz_fourier_sum {a z : ℂ} (ha : a ≠ -1) (hz : 0 < z.re) {h : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    HasSum (fun k : ℕ => let j : ℂ := k+1;
        a*(exp (2*π*I*j*(z+h))/(2*π*I*j)^(a+1)*upperIncompleteGammaOnLog a
            (log z+log (2*π*j)+π*I/2)+exp
        (-2*π*I*j*(z+h))/(-2*π*I*j)^(a+1)*upperIncompleteGammaOnLog a (log z+log (2*π*j)-π*I/2)))
        (DLMF.Zeta.hurwitzZetaComplex (-a) (z+h)+z^(a+1)/(a+1)+(h-1/2)*z^a) := by
  sorry

/-- The function F(p,x) approximated in DLMF §8.27(i). -/
def Real.gammaDiDonatoF (p x : ℝ) : ℝ :=
  x^(-p)*Real.exp (x^2/2)*(∫ t : ℝ in Ioi x, Real.exp (-t^2/2)*t^p)

/-- The explicit approximation denominator in DLMF §8.27(i). -/
def Real.gammaDiDonatoH (p x : ℝ) : ℝ :=
  3*(x^2-p)+Real.sqrt ((x^2-p)^2+8*(x^2+p))

/-- The change of variable mentioned in DLMF §8.27(i). -/
theorem Real.gammaDiDonato_gamma (p : ℝ) {x : ℝ} (hx : 0 < x) :
    (Real.gammaDiDonatoF p x : ℂ)=(x : ℂ)^(-(p : ℂ))*Real.exp
        (x^2/2)*(2 : ℂ)^(((p : ℂ)-1)/2)*upperIncompleteGamma ((p+1)/2) (x^2/2) := by
  have hx2 : 0 < x^2/2 := by positivity
  have hU := upperIncompleteGamma_eq_integral (((p:ℂ)+1)/2) hx2
  push_cast at hU
  rw [hU]
  -- real substitution
  have himg : (fun t : ℝ => t^2/2) '' Ioi x = Ioi (x^2/2) := by
    ext u
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have : x^2 < t^2 := by nlinarith
      linarith
    · intro hu
      refine ⟨Real.sqrt (2*u), ?_, ?_⟩
      · rw [show x = Real.sqrt (x^2) from (Real.sqrt_sq hx.le).symm]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
      · rw [Real.sq_sqrt (by nlinarith [sq_nonneg x])]; ring
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioi x) (f := fun t : ℝ => t^2/2)
    (f' := fun t => t) measurableSet_Ioi
    (fun t _ => by
      have := ((hasDerivAt_pow 2 t).div_const 2)
      convert this.hasDerivWithinAt using 1; push_cast; ring)
    (fun s hs t ht hst => by
      simp only at hst
      have h1 : 0 < s := lt_trans hx hs
      have h2 : 0 < t := lt_trans hx ht
      nlinarith [sq_nonneg (s-t), sq_nonneg (s+t)])
    (fun u : ℝ => (u : ℂ)^(((p:ℂ)+1)/2-1)*cexp (-(u:ℂ)))
  rw [himg] at hsub
  have key : (∫ t : ℝ in Ioi x, ((Real.exp (-t^2/2)*t^p : ℝ) : ℂ)) =
      (2:ℂ)^(((p:ℂ)-1)/2) * ∫ u : ℝ in Ioi (x^2/2), (u : ℂ)^(((p:ℂ)+1)/2-1)*cexp (-(u:ℂ)) := by
    rw [hsub, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_trans hx ht
    simp only [Complex.real_smul]
    rw [abs_of_pos ht0]
    have hq : ((t^2/2 : ℝ) : ℂ)^(((p:ℂ)+1)/2-1) = ((t^(p-1)/2^((p-1)/2) : ℝ) : ℂ) := by
      rw [show ((p:ℂ)+1)/2-1 = (((p-1)/2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow (by positivity), Real.div_rpow (by positivity) (by norm_num),
        ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      congr 3; push_cast; ring
    have h2 : (2:ℂ)^(((p:ℂ)-1)/2) = ((2^((p-1)/2) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by norm_num)]; push_cast; ring_nf
    have htp : t^p = t * t^(p-1) := by
      conv_lhs => rw [show p = 1 + (p-1) by ring]
      rw [Real.rpow_add ht0, Real.rpow_one]
    have h2p : (0:ℝ) < 2^((p-1)/2) := by positivity
    have h2c : ((2^((p-1)/2) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h2p.ne'
    rw [hq, h2, htp]
    push_cast
    rw [show -(t:ℂ)^2/2 = -((t:ℂ)^2/2) by ring]
    field_simp
  rw [Real.gammaDiDonatoF, ofReal_mul, ofReal_mul, ← integral_complex_ofReal,
      ofReal_cpow hx.le, key]
  push_cast
  ring

/-- Integrability of `exp (-t²/2) t^q` on `(x, ∞)`, `x > 0`. -/
private lemma DiDonatoApproximation.integrableOn (q : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-t^2/2) * t^q) (Ioi x) := by
  rcases le_or_gt 0 q with hq | hq
  · have h := (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1/2) (by norm_num) (s := q)
      (by linarith)).mono_set (Ioi_subset_Ioi hx.le)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only; rw [mul_comm]; congr 1; ring_nf
  · have h : IntegrableOn (fun t : ℝ => x^q * Real.exp (-(1/2) * t^2)) (Ioi x) :=
      ((integrable_exp_neg_mul_sq (b := 1/2) (by norm_num)).const_mul (x^q)).integrableOn
    refine h.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have ht0 : 0 < t := lt_trans hx ht
      exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t^2/2)).continuousAt.mul
        (Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne'))).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      have ht0 : 0 < t := lt_trans hx ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
      refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hx (le_of_lt ht) hq.le) (le_of_eq ?_)
        (by positivity) (by positivity)
      congr 1; ring

/-- The integral `∫_x^∞ exp (-t²/2) t^q dt`. -/
private noncomputable def DiDonatoApproximation.gaussTail (q x : ℝ) : ℝ := ∫ t : ℝ in Ioi x,
    Real.exp (-t^2/2) * t^q

private lemma DiDonatoApproximation.gaussTail_nonneg (q : ℝ) {x : ℝ} (hx : 0 < x) : 0 ≤
    DiDonatoApproximation.gaussTail q x :=
  setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : 0 < t := lt_trans hx ht
    positivity

/-- Integration by parts: `G(p) = x^{p-1} e^{-x²/2} + (p-1) G(p-2)`. -/
private lemma DiDonatoApproximation.gaussTail_rec (p : ℝ) {x : ℝ} (hx : 0 < x) :
    DiDonatoApproximation.gaussTail p x = x^(p-1) * Real.exp (-x^2/2) + (p-1) *
        DiDonatoApproximation.gaussTail (p-2) x := by
  set f : ℝ → ℝ := fun t => -(t^(p-1) * Real.exp (-t^2/2))
  have hderiv : ∀ t ∈ Ioi x, HasDerivAt f
      (Real.exp (-t^2/2) * t^p - (p-1) * (Real.exp (-t^2/2) * t^(p-2))) t := by
    intro t ht
    have ht0 : 0 < t := lt_trans hx ht
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := p-1) (Or.inl ht0.ne')
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t^2/2)) (Real.exp (-t^2/2) * (-t)) t := by
      have h3 : HasDerivAt (fun t : ℝ => -t^2/2) (-t) t := by
        convert (hasDerivAt_pow 2 t).const_mul (-1/2 : ℝ) using 1
        · funext s; ring
        · push_cast; ring
      exact h3.exp
    convert (h1.mul h2).neg using 1
    have e1 : t^(p-1-1) = t^(p-2) := by ring_nf
    have e2 : t^p = t^(p-1) * t := by
      rw [← Real.rpow_add_one ht0.ne']; ring_nf
    rw [e1, e2]; ring
  have hcont : ContinuousWithinAt f (Ici x) x := by
    refine ContinuousAt.continuousWithinAt ?_
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hx.ne')).mul
      (by fun_prop : Continuous fun t : ℝ => Real.exp (-t^2/2)).continuousAt).neg
  have hint : IntegrableOn
      (fun t => Real.exp (-t^2/2) * t^p - (p-1) * (Real.exp (-t^2/2) * t^(p-2))) (Ioi x) :=
    (DiDonatoApproximation.integrableOn p hx).sub
        ((DiDonatoApproximation.integrableOn (p-2) hx).const_mul _)
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((p-1)/2) (1/2) (by norm_num)).comp
      (tendsto_pow_atTop (n := 2) (by norm_num) : Tendsto (fun t : ℝ => t^2) atTop atTop)
    have h' := h.neg
    rw [neg_zero] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp, f]
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
    congr 2
    · ring_nf
    · congr 1; push_cast; ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [integral_sub (DiDonatoApproximation.integrableOn p hx)
      ((DiDonatoApproximation.integrableOn (p-2) hx).const_mul _),
    integral_const_mul] at h
  simp only [DiDonatoApproximation.gaussTail, f] at h ⊢
  linarith

/-- `G(1) = e^{-x²/2}`. -/
private lemma DiDonatoApproximation.gaussTail_one {x : ℝ} (hx : 0 < x) :
    DiDonatoApproximation.gaussTail 1 x = Real.exp (-x^2/2) := by
  rw [DiDonatoApproximation.gaussTail_rec 1 hx]; simp

/-- For `q ≤ 1`, `G(q) ≤ x^{q-1} e^{-x²/2}`. -/
private lemma DiDonatoApproximation.gaussTail_le {q : ℝ} (hq : q ≤ 1) {x : ℝ} (hx : 0 < x) :
    DiDonatoApproximation.gaussTail q x ≤ x^(q-1) * Real.exp (-x^2/2) := by
  rw [← DiDonatoApproximation.gaussTail_one hx, DiDonatoApproximation.gaussTail,
      DiDonatoApproximation.gaussTail, ← integral_const_mul]
  refine setIntegral_mono_on (DiDonatoApproximation.integrableOn q hx)
      ((DiDonatoApproximation.integrableOn 1 hx).const_mul _)
    measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := lt_trans hx ht
  have e : t^q = t^(q-1) * t := by rw [← Real.rpow_add_one ht0.ne']; ring_nf
  rw [e, Real.rpow_one]
  have := Real.rpow_le_rpow_of_nonpos hx (le_of_lt ht) (by linarith : q - 1 ≤ 0)
  have h0 : 0 ≤ Real.exp (-t^2/2) * t := by positivity
  nlinarith [h0, this]

private lemma DiDonatoApproximation.F_eq (p x : ℝ) :
    Real.gammaDiDonatoF p x = x^(-p) * Real.exp (x^2/2) * DiDonatoApproximation.gaussTail p x := rfl

/-- `F(p) = 1/x + (p-1) x^{-2} F(p-2)`. -/
private lemma DiDonatoApproximation.F_rec (p : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.gammaDiDonatoF p x = x⁻¹ + (p-1) * x⁻¹^2 * Real.gammaDiDonatoF (p-2) x := by
  rw [DiDonatoApproximation.F_eq p x, DiDonatoApproximation.F_eq (p-2) x,
      DiDonatoApproximation.gaussTail_rec p hx]
  have e1 : x^(-p) * x^(p-1) = x⁻¹ := by
    rw [← Real.rpow_add hx, show -p + (p-1) = -1 by ring, Real.rpow_neg_one]
  have e2 : x^(-p) = x⁻¹^2 * x^(-(p-2)) := by
    rw [show -p = -2 + -(p-2) by ring, Real.rpow_add hx, Real.rpow_neg hx.le,
      Real.rpow_two, inv_pow]
  have e3 : Real.exp (x^2/2) * Real.exp (-x^2/2) = 1 := by
    rw [← Real.exp_add, show x^2/2 + -x^2/2 = (0:ℝ) by ring, Real.exp_zero]
  calc x^(-p) * Real.exp (x^2/2) *
         (x^(p-1) * Real.exp (-x^2/2) + (p-1) * DiDonatoApproximation.gaussTail (p-2) x)
      = (x^(-p) * x^(p-1)) * (Real.exp (x^2/2) * Real.exp (-x^2/2))
        + (p-1) * x^(-p) * Real.exp (x^2/2) * DiDonatoApproximation.gaussTail (p-2) x := by ring
    _ = _ := by rw [e1, e3, e2]; ring

/-- For `q ≤ 1`, `0 ≤ F(q, x) ≤ 1/x`. -/
private lemma DiDonatoApproximation.F_le {q : ℝ} (hq : q ≤ 1) {x : ℝ} (hx : 0 < x) :
    0 ≤ Real.gammaDiDonatoF q x ∧ Real.gammaDiDonatoF q x ≤ x⁻¹ := by
  rw [DiDonatoApproximation.F_eq q x]
  refine ⟨by have := DiDonatoApproximation.gaussTail_nonneg q hx; positivity, ?_⟩
  have h := DiDonatoApproximation.gaussTail_le hq hx
  have hpos : 0 ≤ x^(-q) * Real.exp (x^2/2) := by positivity
  calc x^(-q) * Real.exp (x^2/2) * DiDonatoApproximation.gaussTail q x
      ≤ x^(-q) * Real.exp (x^2/2) * (x^(q-1) * Real.exp (-x^2/2)) :=
        mul_le_mul_of_nonneg_left h hpos
    _ = (x^(-q) * x^(q-1)) * (Real.exp (x^2/2) * Real.exp (-x^2/2)) := by ring
    _ = x⁻¹ := by
      rw [← Real.rpow_add hx, show -q + (q-1) = -1 by ring, Real.rpow_neg_one, ← Real.exp_add,
        show x^2/2 + -x^2/2 = (0:ℝ) by ring, Real.exp_zero, mul_one]

/-- `F(q, x) = O(1/x)` as `x → ∞`, for every real `q`. -/
private lemma DiDonatoApproximation.F_isBigO_of_le (n : ℕ) : ∀ q : ℝ, q ≤ 1 + 2*n →
    (fun x => Real.gammaDiDonatoF q x) =O[atTop] (fun x : ℝ => x⁻¹) := by
  induction n with
  | zero =>
    intro q hq
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have h := DiDonatoApproximation.F_le (by simpa using hq) hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h.1, abs_of_pos (inv_pos.mpr hx),
      one_mul]
    exact h.2
  | succ n ih =>
    intro q hq
    have h2 := ih (q-2) (by push_cast at hq; linarith)
    have hx2 : (fun x : ℝ => (q-1) * x⁻¹^2) =O[atTop] (fun _ : ℝ => (1:ℝ)) := by
      refine IsBigO.const_mul_left ?_ _
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop 1] with x hx
      have : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
      have h0 : 0 ≤ x⁻¹ := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_one, one_mul]
      nlinarith
    have hm := (hx2.mul h2).congr_right (fun x => one_mul _)
    refine ((isBigO_refl (fun x : ℝ => x⁻¹) atTop).add hm).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [DiDonatoApproximation.F_rec q hx]

private lemma DiDonatoApproximation.F_isBigO (q : ℝ) :
    (fun x => Real.gammaDiDonatoF q x) =O[atTop] (fun x : ℝ => x⁻¹) := by
  obtain ⟨n, hn⟩ := exists_nat_ge q
  exact DiDonatoApproximation.F_isBigO_of_le n q (by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])


/-- The polynomial `q` with `D P² - R² = u³ q(u)` in the proof of DLMF §8.27(i). -/
private noncomputable def DiDonatoApproximation.polyQ (p u : ℝ) : ℝ :=
  (104 - 168*p + 72*p^2 - 8*p^3) + u*(24*p^3 - 168*p^2 + 264*p - 120)
    + u^2*(-24*p^4 + 96*p^3 - 48*p^2 - 96*p + 72)
    + u^3*(-8*p^6 + 72*p^5 - 240*p^4 + 368*p^3 - 264*p^2 + 72*p)

private noncomputable def DiDonatoApproximation.polyP (p u : ℝ) : ℝ := 1 + (p-1)*u + (p-1)*(p-3)*u^2
private noncomputable def DiDonatoApproximation.polyD (p u : ℝ) : ℝ := (1 - p*u)^2 + 8*u + 8*p*u^2
private noncomputable def DiDonatoApproximation.polyR (p u : ℝ) : ℝ := 4 -
    3*(1 - p*u)*DiDonatoApproximation.polyP p u
private noncomputable def DiDonatoApproximation.polyG (p u : ℝ) : ℝ := 3*(1 - p*u) +
    Real.sqrt (DiDonatoApproximation.polyD p u)
private noncomputable def DiDonatoApproximation.polyW (p u : ℝ) : ℝ :=
    Real.sqrt (DiDonatoApproximation.polyD p u) * DiDonatoApproximation.polyP p u +
    DiDonatoApproximation.polyR p u

private lemma DiDonatoApproximation.polyD_identity (p u : ℝ) :
    DiDonatoApproximation.polyD p u * DiDonatoApproximation.polyP p u^2 -
        DiDonatoApproximation.polyR p u^2 = u^3 * DiDonatoApproximation.polyQ p u := by
  simp only [DiDonatoApproximation.polyD, DiDonatoApproximation.polyP, DiDonatoApproximation.polyR,
      DiDonatoApproximation.polyQ]; ring

private lemma DiDonatoApproximation.continuous_polyD (p : ℝ) : Continuous
    (DiDonatoApproximation.polyD p) := by
  unfold DiDonatoApproximation.polyD; fun_prop

private lemma DiDonatoApproximation.tendsto (p : ℝ) :
    Tendsto (fun x : ℝ => x⁻¹^2) atTop (𝓝[≥] 0) ∧
    Tendsto (fun u => DiDonatoApproximation.polyQ p u /
        (DiDonatoApproximation.polyG p u * DiDonatoApproximation.polyW p u)) (𝓝 0)
      (𝓝 (DiDonatoApproximation.polyQ p 0 /
          (DiDonatoApproximation.polyG p 0 * DiDonatoApproximation.polyW p 0))) ∧
          DiDonatoApproximation.polyG p 0 = 4 ∧ DiDonatoApproximation.polyW p 0 = 2 := by
  have hD0 : DiDonatoApproximation.polyD p 0 = 1 := by simp [DiDonatoApproximation.polyD]
  have hG0 : DiDonatoApproximation.polyG p 0 = 4 := by
      rw [DiDonatoApproximation.polyG, hD0]; norm_num
  have hW0 : DiDonatoApproximation.polyW p 0 = 2 := by
      rw [DiDonatoApproximation.polyW, DiDonatoApproximation.polyR, hD0];
      norm_num [DiDonatoApproximation.polyP]
  refine ⟨?_, ?_, hG0, hW0⟩
  · refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun x => ?_⟩
    · simpa using ((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2 :
        Tendsto (fun x : ℝ => x⁻¹^2) atTop (𝓝 (0^2)))
    · exact sq_nonneg (x⁻¹)
  · have hc : ContinuousAt
        (fun u => DiDonatoApproximation.polyQ p u /
        (DiDonatoApproximation.polyG p u * DiDonatoApproximation.polyW p u)) 0 := by
      refine ContinuousAt.div ?_ ?_ (by rw [hG0, hW0]; norm_num)
      · unfold DiDonatoApproximation.polyQ; fun_prop
      · have hs : Continuous fun u => Real.sqrt (DiDonatoApproximation.polyD p u) :=
          (DiDonatoApproximation.continuous_polyD p).sqrt
        unfold DiDonatoApproximation.polyG DiDonatoApproximation.polyW DiDonatoApproximation.polyR
            DiDonatoApproximation.polyP
        exact (Continuous.mul (by fun_prop) (by fun_prop)).continuousAt
    exact hc.tendsto

/-- The algebraic identity behind the `O(x^{-7})` estimate, in the variable `y = 1/x`. -/
private lemma DiDonatoApproximation.identity_reciprocal (p y s : ℝ) (hy : y ≠ 0)
    (hs2 : s^2 = DiDonatoApproximation.polyD p (y^2))
    (hG : 3*(1-p*y^2)+s ≠ 0)
        (hW : s*DiDonatoApproximation.polyP p (y^2) + DiDonatoApproximation.polyR p (y^2) ≠ 0) :
    y + (p-1)*y^3 + (p-1)*(p-3)*y^5 - 4*y/(3*(1-p*y^2)+s) =
      y^7 * (DiDonatoApproximation.polyQ p (y^2) /
          ((3*(1-p*y^2)+s) * (s*DiDonatoApproximation.polyP p (y^2) +
          DiDonatoApproximation.polyR p (y^2)))) := by
  have hpoly := DiDonatoApproximation.polyD_identity p (y^2)
  rw [← hs2] at hpoly
  set G := 3*(1-p*y^2)+s
  set W := s*DiDonatoApproximation.polyP p (y^2) + DiDonatoApproximation.polyR p (y^2) with hWdef
  have hnum : y^7 * DiDonatoApproximation.polyQ p (y^2) -
      ((y + (p-1)*y^3 + (p-1)*(p-3)*y^5) * G - 4*y) * W = 0 := by
    simp only [G, hWdef, DiDonatoApproximation.polyP, DiDonatoApproximation.polyR] at hpoly ⊢
    linear_combination (-y) * hpoly
  rw [eq_comm, ← sub_eq_zero]
  have e : y^7 * (DiDonatoApproximation.polyQ p (y^2) / (G * W)) -
      (y + (p-1)*y^3 + (p-1)*(p-3)*y^5 - 4*y/G) =
      (y^7 * DiDonatoApproximation.polyQ p (y^2) - ((y + (p-1)*y^3 + (p-1)*(p-3)*y^5) * G - 4*y) *
          W) / (G * W) := by
    field_simp
  rw [e, hnum, zero_div]

private lemma DiDonatoApproximation.H_eq (p : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.gammaDiDonatoH p x = x^2 * DiDonatoApproximation.polyG p (x⁻¹^2) := by
  have hDx : (x^2-p)^2+8*(x^2+p) = (x^2)^2 * DiDonatoApproximation.polyD p (x⁻¹^2) := by
    simp only [DiDonatoApproximation.polyD]; field_simp; ring
  rw [Real.gammaDiDonatoH, hDx, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
    DiDonatoApproximation.polyG]
  field_simp

/-- The explicit O(x^-7) approximation theorem in DLMF §8.27(i). -/
theorem Real.gammaDiDonato_approximation (p : ℝ) :
    IsBigO atTop (fun x : ℝ => Real.gammaDiDonatoF p x-4*x/Real.gammaDiDonatoH p x)
        (fun x => x^(-7 : ℤ)) := by
  obtain ⟨hu, hφ, hG0, hW0⟩ := DiDonatoApproximation.tendsto p
  have hu' : Tendsto (fun x : ℝ => x⁻¹^2) atTop (𝓝 0) := tendsto_nhdsWithin_iff.mp hu |>.1
  have hDc : Continuous (DiDonatoApproximation.polyD p) := DiDonatoApproximation.continuous_polyD p
  have hD0 : DiDonatoApproximation.polyD p 0 = 1 := by simp [DiDonatoApproximation.polyD]
  have hGc : Continuous (DiDonatoApproximation.polyG p) := by
    have := hDc.sqrt; unfold DiDonatoApproximation.polyG; fun_prop
  have hWc : Continuous (DiDonatoApproximation.polyW p) := by
    have := hDc.sqrt; unfold DiDonatoApproximation.polyW DiDonatoApproximation.polyR
        DiDonatoApproximation.polyP; fun_prop
  have hGl : Tendsto (fun x : ℝ => DiDonatoApproximation.polyG p (x⁻¹^2)) atTop (𝓝 4) := by
    rw [← hG0]; exact (hGc.tendsto 0).comp hu'
  have hWl : Tendsto (fun x : ℝ => DiDonatoApproximation.polyW p (x⁻¹^2)) atTop (𝓝 2) := by
    rw [← hW0]; exact (hWc.tendsto 0).comp hu'
  have hDl : Tendsto (fun x : ℝ => DiDonatoApproximation.polyD p (x⁻¹^2)) atTop (𝓝 1) := by
    rw [← hD0]; exact (hDc.tendsto 0).comp hu'
  have hz : (fun x : ℝ => x^(-7 : ℤ)) = fun x => x⁻¹^7 := by
    funext x; rw [zpow_neg, inv_pow]; norm_cast
  rw [hz]
  -- the series part
  have hA : (fun x : ℝ => Real.gammaDiDonatoF p x -
      (x⁻¹ + (p-1)*x⁻¹^3 + (p-1)*(p-3)*x⁻¹^5)) =O[atTop] (fun x : ℝ => x⁻¹^7) := by
    have h6 := ((isBigO_refl (fun x : ℝ => x⁻¹^6) atTop).mul
        (DiDonatoApproximation.F_isBigO (p-6))).const_mul_left
      ((p-1)*(p-3)*(p-5))
    refine (h6.congr' ?_ ?_)
    · filter_upwards [eventually_gt_atTop 0] with x hx
      have r1 := DiDonatoApproximation.F_rec p hx
      have r2 := DiDonatoApproximation.F_rec (p-2) hx
      have r3 := DiDonatoApproximation.F_rec (p-4) hx
      rw [show p-2-2 = p-4 by ring] at r2
      rw [show p-4-2 = p-6 by ring] at r3
      rw [r1, r2, r3]; ring
    · filter_upwards with x; ring
  have hB : (fun x : ℝ => (x⁻¹ + (p-1)*x⁻¹^3 + (p-1)*(p-3)*x⁻¹^5) -
      4*x/Real.gammaDiDonatoH p x) =O[atTop] (fun x : ℝ => x⁻¹^7) := by
    have hb := (isBigO_refl (fun x : ℝ => x⁻¹^7) atTop).mul
      ((hφ.comp hu').isBigO_one ℝ)
    refine (hb.congr' ?_ ?_)
    · filter_upwards [eventually_gt_atTop 0, hGl.eventually (lt_mem_nhds (by norm_num : (0:ℝ) < 4)),
        hWl.eventually (lt_mem_nhds (by norm_num : (0:ℝ) < 2)),
        hDl.eventually (lt_mem_nhds (by norm_num : (0:ℝ) < 1))] with x hx hG hW hD
      have hy : x⁻¹ ≠ 0 := inv_ne_zero hx.ne'
      have h := DiDonatoApproximation.identity_reciprocal p x⁻¹
          (Real.sqrt (DiDonatoApproximation.polyD p (x⁻¹^2))) hy (Real.sq_sqrt hD.le)
        hG.ne' hW.ne'
      have hH : 4*x/Real.gammaDiDonatoH p x = 4*x⁻¹/DiDonatoApproximation.polyG p (x⁻¹^2) := by
        rw [DiDonatoApproximation.H_eq p hx]; field_simp
      simp only [Function.comp]
      rw [hH]
      exact h.symm
    · filter_upwards with x; simp
  exact (hA.add hB).congr_left (fun x => by ring)


end DLMF.Confluent
