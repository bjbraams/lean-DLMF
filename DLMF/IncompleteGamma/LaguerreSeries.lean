/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.RealAxisBounds
public import DLMF.Bessel.IntegralTransforms
public import DLMF.OrthogonalPolynomials.Classical
public import DLMF.Confluent.IncompleteGamma
public import DLMFMathlib.Analysis.SpecialFunctions.ExponentialSeries
public import DLMFMathlib.MeasureTheory.Integral.FractionalSubstitution
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Laguerre expansion of the upper incomplete Gamma function

The series in DLMF 8.7.6 converges absolutely for `Re a < 1/2` at every positive real
argument, using the polynomial continuation of the Laguerre family. A Bessel–Gaussian
transform gives an integrable majorant for its tail. Termwise integration of the Laguerre
generating function and the substitution `u/(1+u)` then identify the sum with `Γ(a,x)`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology Nat
namespace DLMF.Confluent.IncompleteGammaLaguerre
open DLMF.Bessel DLMF.OrthogonalPolynomials

/-- The sum of absolute values of the shifted Bessel–Gaussian expansion. -/
def normSeries (a : ℂ) (c : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  t^(a.re+1)*Real.exp (-t^2)*‖besselJ a (c*t)‖ *
    ∑' n : ℕ, (t^2)^(n+N)/((n+N).factorial:ℝ)/(n+N+1)

/-- The absolute-value series is measurable on the positive half-line. -/
theorem aestronglyMeasurable_normSeries (a : ℂ) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    AEStronglyMeasurable (normSeries a c N) (volume.restrict (Ioi 0)) := by
  have hw : ContinuousOn (fun t : ℝ => t^(a.re+1)*Real.exp (-t^2)*‖besselJ a (c*t)‖)
      (Ioi 0) := by
    intro t ht
    have hp : ContinuousAt (fun t : ℝ => t^(a.re+1)) t :=
      Real.continuousAt_rpow_const t _ (Or.inl (ne_of_gt ht))
    exact ((hp.mul (by fun_prop)).mul
      (continuousAt_besselJ_mul a hc ht).norm).continuousWithinAt
  have hS : AEStronglyMeasurable
      (fun t : ℝ => ∑' n : ℕ, (t^2)^(n+N)/((n+N).factorial:ℝ)/(n+N+1)) volume := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (k : ℕ) (t : ℝ) => ∑ n ∈ Finset.range k,
        (t^2)^(n+N)/((n+N).factorial:ℝ)/(n+N+1))
    · intro k
      exact (by fun_prop : Continuous fun t : ℝ => ∑ n ∈ Finset.range k,
        (t^2)^(n+N)/((n+N).factorial:ℝ)/(n+N+1)).aestronglyMeasurable
    · exact ae_of_all _ fun t => (Real.summable_pow_div_factorial_mul_succ N
        (sq_nonneg t)).hasSum.tendsto_sum_nat
  exact (hw.aestronglyMeasurable measurableSet_Ioi).mul hS.restrict

/-- The absolute-value series is integrable when `Re a < 1/2` and the shift
ensures integrability at zero. -/
theorem integrableOn_normSeries {a : ℂ} (ha : a.re < 1/2) {c : ℝ} (hc : 0 < c)
    (N : ℕ) (hN : 0 < (a+N+1).re) : IntegrableOn (normSeries a c N) (Ioi 0) := by
  obtain ⟨T,M,K,hT,hM,hK,hnear,htail⟩ := exists_norm_besselJ_mul_bounds a hc
  have hm := aestronglyMeasurable_normSeries a hc N
  have hI : IntegrableOn (normSeries a c N) (Ioc 0 T) := by
    have hp : -1 < (2*N:ℕ)+2*a.re+1 := by
      simp only [add_re, natCast_re, one_re] at hN
      push_cast
      linarith
    have hi : IntegrableOn (fun t : ℝ => M*t^((2*N:ℕ)+2*a.re+1)) (Ioc 0 T) := by
      simpa only [uIoc_of_le hT.le] using
        ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T) hp).const_mul M).1
    apply hi.mono' (hm.mono_set Ioc_subset_Ioi_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have hS := Real.tsum_pow_div_factorial_mul_succ_le N (sq_nonneg t)
    have hs0 : 0 ≤ ∑' n : ℕ, (t^2)^(n+N)/((n+N).factorial:ℝ)/(n+N+1) :=
      tsum_nonneg fun n => by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ normSeries a c N t by
      unfold normSeries; positivity)]
    calc normSeries a c N t ≤
        (t^(a.re+1)*Real.exp (-t^2)*(M*t^a.re))*((t^2)^N*Real.exp (t^2)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hnear t ht) (by positivity)) hS hs0
            (by positivity)
      _ = M*t^((2*N:ℕ)+2*a.re+1) := by
        have he : Real.exp (-t^2)*Real.exp (t^2)=1 := by rw [←Real.exp_add]; simp
        have hp : t^(a.re+1)*t^a.re*(t^2)^N = t^((2*N:ℕ)+2*a.re+1) := by
          rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add ht0, ← Real.rpow_add ht0]
          congr 1
          push_cast
          ring
        calc _ = M*(Real.exp (-t^2)*Real.exp (t^2))*(t^(a.re+1)*t^a.re*(t^2)^N) := by ring
          _ = _ := by rw [he, mul_one, hp]
  have hJ : IntegrableOn (normSeries a c N) (Ioi T) := by
    have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : a.re-3/2 < -1) hT).const_mul K
    apply hi.mono' (hm.mono_set (Ioi_subset_Ioi hT.le))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hT.trans ht
    have hS : (∑' n : ℕ, (t^2)^(n+N)/((n+N).factorial:ℝ)/(n+N+1)) ≤
        Real.exp (t^2)/t^2 := by
      rw [le_div_iff₀ (sq_pos_of_pos ht0)]
      simpa only [mul_comm] using Real.mul_tsum_pow_div_factorial_mul_succ_le N (sq_nonneg t)
    have hs0 : 0 ≤ ∑' n : ℕ, (t^2)^(n+N)/((n+N).factorial:ℝ)/(n+N+1) :=
      tsum_nonneg fun n => by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ normSeries a c N t by
      unfold normSeries; positivity)]
    calc normSeries a c N t ≤
        (t^(a.re+1)*Real.exp (-t^2)*(K*t^(-(1/2):ℝ)))*(Real.exp (t^2)/t^2) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left (htail t ht) (by positivity)) hS hs0
            (by positivity)
      _ = K*t^(a.re-3/2) := by
        have he : Real.exp (-t^2)*Real.exp (t^2)=1 := by rw [←Real.exp_add]; simp
        have hp : t^(a.re+1)*t^(-(1/2):ℝ)/t^2 = t^(a.re-3/2) := by
          rw [←Real.rpow_natCast t 2, ←Real.rpow_add ht0, ←Real.rpow_sub ht0]
          congr 1
          ring
        calc _ = K*(Real.exp (-t^2)*Real.exp (t^2))*(t^(a.re+1)*t^(-(1/2):ℝ)/t^2) := by ring
          _ = _ := by rw [he, mul_one, hp]
  rw [← Ioc_union_Ioi_eq_Ioi hT.le]
  exact hI.union hJ

/-- A Bessel–Gaussian integral gives the Laguerre polynomial, including exceptional
parameters, when the terminal Gamma argument has positive real part. -/
theorem integral_gaussian_eq_laguerre {a : ℂ} {n : ℕ}
    (ha : 0 < (a+n+1).re) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in Ioi 0, (t:ℂ)^(a+2*n+1)*exp (-(t:ℂ)^2)*
      besselJ a ((2*Real.sqrt x:ℝ)*t)) =
      ((Real.sqrt x:ℂ)^a/2*exp (-(x:ℂ)))*(n.factorial:ℂ)*laguerreExtended a n x := by
  have he : ((a+2*n+2)+a)/2 = a+n+1 := by ring
  have hi := besselJ_gaussian_integral_complex (μ := a+2*n+2) (ν := a) (s := 1)
    (w := 2*Real.sqrt x) (by simp at ha ⊢; linarith) (by norm_num) (by positivity)
  rw [he, one_cpow, mul_one] at hi
  have hw : -(↑(2*Real.sqrt x):ℂ)^2/(4*1) = -(x:ℂ) := by
    push_cast
    rw [mul_pow, ← ofReal_pow, Real.sq_sqrt hx.le]
    ring
  have hw2 : (↑(2*Real.sqrt x):ℂ)/2 = (Real.sqrt x:ℂ) := by push_cast; ring
  rw [hw, hw2, regularizedConfluent_kummer_transform, neg_neg,
    show (a+1)-(a+n+1) = -(n:ℂ) by ring] at hi
  have hg := laguerreExtended_eq_gamma_mul_regularized ha (x:ℂ)
  have hn : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hg' : Gamma (a+n+1)*regularizedHGFun {-(n:ℂ)} {a+1} x =
      (n.factorial:ℂ)*laguerreExtended a n x := by
    rw [hg]
    field_simp
  have he' : a+2*n+2-1 = a+2*n+1 := by ring
  rw [he'] at hi
  simp only [one_mul, neg_mul] at hi
  rw [hi]
  linear_combination ((Real.sqrt x:ℂ)^a/2*exp (-(x:ℂ)))*hg'

/-- A normalized Bessel–Gaussian term for the shifted Laguerre series. -/
def gaussianTerm (a : ℂ) (c : ℝ) (N n : ℕ) (t : ℝ) : ℂ :=
  (t:ℂ)^(a+1)*exp (-(t:ℂ)^2)*besselJ a (c*t)*
    (t:ℂ)^(2*(n+N))/((n+N).factorial:ℂ)/(n+N+1)

/-- The norm of a Bessel–Gaussian term separates into a positive weight and an
exponential-series coefficient. -/
theorem norm_gaussianTerm (a : ℂ) (c : ℝ) (N n : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖gaussianTerm a c N n t‖ =
      (t^(a.re+1)*Real.exp (-t^2)*‖besselJ a (c*t)‖)*
        ((t^2)^(n+N)/((n+N).factorial:ℝ)/(n+N+1)) := by
  have he : exp (-(t:ℂ)^2) = (Real.exp (-t^2):ℂ) := by
    rw [← ofReal_pow, ← ofReal_neg, ofReal_exp]
  have hd : ‖((n+N:ℕ):ℂ)+1‖ = (n:ℝ)+N+1 := by
    rw [← ofReal_natCast, ← ofReal_one, ← ofReal_add, norm_real,
      Real.norm_of_nonneg (by positivity)]
    push_cast
    rfl
  simp only [Nat.cast_add] at hd
  rw [gaussianTerm, norm_div, norm_div, norm_mul, norm_mul, norm_mul,
    norm_cpow_eq_rpow_re_of_pos ht, he, norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_natCast, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg ht.le, hd]
  simp only [add_re, one_re]
  rw [pow_mul]
  ring

/-- Each Bessel–Gaussian term is continuous on the positive half-line. -/
theorem continuousOn_gaussianTerm (a : ℂ) {c : ℝ} (hc : 0 < c) (N n : ℕ) :
    ContinuousOn (gaussianTerm a c N n) (Ioi 0) := by
  intro t ht
  have hp : ContinuousAt (fun t : ℝ => (t:ℂ)^(a+1)) t := by
    have h := (hasDerivAt_id (t:ℂ)).cpow_const (c := a+1) (Or.inl (by simpa using ht))
    exact (h.comp_ofReal (z := t)).continuousAt
  exact (((hp.mul (by fun_prop)).mul (continuousAt_besselJ_mul a hc ht)).mul
    (by fun_prop)).div_const _ |>.div_const _ |>.continuousWithinAt

/-- The Bessel–Gaussian expansion is pointwise absolutely summable at positive arguments. -/
theorem summable_norm_gaussianTerm (a : ℂ) (c : ℝ) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ‖gaussianTerm a c N n t‖) := by
  simp_rw [norm_gaussianTerm a c N _ ht]
  exact (Real.summable_pow_div_factorial_mul_succ N (sq_nonneg t)).mul_left _

/-- Dominated summation makes the Bessel–Gaussian integrals a summable family. -/
theorem summable_integral_gaussianTerm {a : ℂ} (ha : a.re < 1/2) {c : ℝ} (hc : 0 < c)
    (N : ℕ) (hN : 0 < (a+N+1).re) :
    Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0, gaussianTerm a c N n t) := by
  have hi : IntegrableOn (fun t : ℝ => ∑' n : ℕ, ‖gaussianTerm a c N n t‖) (Ioi 0) := by
    refine (integrableOn_normSeries ha hc N hN).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp_rw [norm_gaussianTerm a c N _ ht]
    rw [tsum_mul_left]
    rfl
  have h := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi 0)) (bound := fun n t => ‖gaussianTerm a c N n t‖)
    (fun n => (continuousOn_gaussianTerm a hc N n).aestronglyMeasurable measurableSet_Ioi)
    (fun n => ae_of_all _ fun _ => le_rfl)
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ fun t ht => summable_norm_gaussianTerm a c N ht)) hi
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ fun t ht => (Summable.of_norm (summable_norm_gaussianTerm a c N ht)).hasSum))
  exact h.summable

/-- The Laguerre series divided by `n+1` converges absolutely for `Re a < 1/2`
and positive real argument. -/
theorem summable_laguerre_div_succ {a : ℂ} (ha : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => laguerreExtended a n x/(n+1)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (-a.re)
  have hN' : 0 < (a+N+1).re := by simp; linarith
  let C : ℂ := (Real.sqrt x:ℂ)^a/2*exp (-(x:ℂ))
  have hC : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (div_ne_zero (cpow_ne_zero_iff.mpr (Or.inl
      (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'))) (by norm_num)) (Complex.exp_ne_zero _)
  have hs := summable_integral_gaussianTerm ha (by positivity : 0 < 2*Real.sqrt x) N hN'
  have he (n : ℕ) : (∫ t : ℝ in Ioi 0, gaussianTerm a (2*Real.sqrt x) N n t) =
      C*(laguerreExtended a (n+N) x/(n+N+1)) := by
    have hn : 0 < (a+(n+N)+1).re := by simp at hN' ⊢; linarith [Nat.cast_nonneg (α := ℝ) n]
    calc
      _ = (∫ t : ℝ in Ioi 0,
        ((t:ℂ)^(a+2*(n+N)+1)*exp (-(t:ℂ)^2)*besselJ a ((2*Real.sqrt x:ℝ)*t))/
          ((n+N).factorial:ℂ)/(n+N+1)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [gaussianTerm, show a+2*(n+N)+1 = (a+1)+((2*(n+N):ℕ):ℂ) by push_cast; ring]
        conv_rhs => rw [cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt ht)), cpow_natCast]
        ring
      _ = _ := by
        have hg := integral_gaussian_eq_laguerre (a := a) (n := n+N)
          (by simpa only [Nat.cast_add] using hn) hx
        simp only [Nat.cast_add] at hg
        rw [integral_div, integral_div, hg]
        dsimp [C]
        field_simp [(Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n+N)) : ((n+N).factorial:ℂ) ≠ 0)]
  have hs' : Summable (fun n : ℕ => C*(laguerreExtended a (n+N) x/(n+N+1))) := hs.congr he
  have hs'' := hs'.mul_left C⁻¹
  have hs''' : Summable (fun n : ℕ => laguerreExtended a (n+N) x/(n+N+1)) :=
    hs''.congr fun n => by rw [←mul_assoc, inv_mul_cancel₀ hC, one_mul]
  apply (summable_nat_add_iff N).mp
  simpa only [Nat.cast_add] using hs'''

/-- The Laguerre generating kernel on the open unit interval. -/
def generatingKernel (a : ℂ) (x t : ℝ) : ℂ :=
  (1-(t:ℂ))^(-a-1)*exp (-(x:ℂ)*t/(1-t))

/-- The fractional substitution turns the generating kernel into a Tricomi Laplace kernel. -/
theorem generatingKernel_substitution (a : ℂ) (x : ℝ) {u : ℝ} (hu : 0 < u) :
    (1/(1+u)^2) • generatingKernel a x (u/(1+u)) =
      exp (-(x:ℂ)*u)*(1+(u:ℂ))^(a-1) := by
  have hw : 0 < 1+u := by linarith
  have hwc : (1+(u:ℂ)) ≠ 0 := by exact_mod_cast hw.ne'
  have hbase : 1-((u/(1+u):ℝ):ℂ) = ((1+u:ℝ):ℂ)⁻¹ := by
    push_cast
    field_simp
    ring
  have he : -(x:ℂ)*((u/(1+u):ℝ):ℂ)/(1-((u/(1+u):ℝ):ℂ)) = -(x:ℂ)*u := by
    rw [hbase]
    push_cast
    field_simp
  have hp : (1+(u:ℂ))^(a+1)/(1+(u:ℂ))^2 = (1+(u:ℂ))^(a-1) := by
    rw [← cpow_natCast (1+(u:ℂ)) 2, ← cpow_sub _ _ hwc]
    congr 1
    norm_num
    ring
  rw [generatingKernel, he, hbase, inv_cpow_ofReal_nonneg hw.le, ←cpow_neg,
    show -(-a-1) = a+1 by ring, Complex.real_smul]
  push_cast
  calc _ = exp (-(x:ℂ)*u)*((1+(u:ℂ))^(a+1)/(1+(u:ℂ))^2) := by ring
    _ = _ := by rw [hp]

/-- The integral of the Laguerre generating kernel gives the upper incomplete Gamma function. -/
theorem integral_generatingKernel_eq_upperIncompleteGamma (a : ℂ) {x : ℝ} (hx : 0 < x) :
    (x:ℂ)^a*exp (-(x:ℂ))*(∫ t : ℝ in Ioo 0 1, generatingKernel a x t) =
      upperIncompleteGamma a x := by
  have hs := integral_comp_div_one_add_Ioi (generatingKernel a x)
  have hi : (∫ u : ℝ in Ioi 0, (1/(1+u)^2) • generatingKernel a x (u/(1+u))) =
      ∫ u : ℝ in Ioi 0, exp (-(x:ℂ)*u)*(1+(u:ℂ))^(a-1) :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => generatingKernel_substitution a x hu
  rw [←hs, hi, upperIncompleteGamma_eq_cpow_mul_kummerU a (ofReal_ne_zero.mpr hx.ne'),
    kummerU_laplace (by norm_num) (by simpa using hx), Gamma_one, div_one, one_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [sub_self, cpow_zero, mul_one, show a+1-1-1 = a-1 by ring]


/-- A convergent Laguerre series has the incomplete-Gamma value obtained by integrating
the generating function termwise. -/
theorem hasSum_laguerre_of_summable (a : ℂ) {x : ℝ} (hx : 0 < x)
    (hs : Summable (fun n : ℕ => laguerreExtended a n x/(n+1))) :
    HasSum (fun n : ℕ => (x:ℂ)^a*exp (-(x:ℂ))*laguerreExtended a n x/(n+1))
      (upperIncompleteGamma a x) := by
  have hpow (n : ℕ) :
      (∫ t : ℝ in Ioo 0 1, t^n) = 1/(n+1:ℝ) := by
    rw [←integral_Ioc_eq_integral_Ioo, ←intervalIntegral.integral_of_le zero_le_one,
      _root_.integral_pow]
    norm_num
  let F : ℕ → ℝ → ℂ := fun n t => laguerreExtended a n x*(t:ℂ)^n
  have hF (n : ℕ) : IntegrableOn (F n) (Ioo 0 1) := by
    have h : IntervalIntegrable (F n) volume (0:ℝ) 1 :=
      (by fun_prop : Continuous (F n)).intervalIntegrable (0:ℝ) 1
    exact h.1.mono_set Ioo_subset_Ioc_self
  have hden (n : ℕ) : ‖(n:ℂ)+1‖ = (n:ℝ)+1 := by
    rw [←ofReal_natCast, ←ofReal_one, ←ofReal_add, norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hnorm (n : ℕ) : (∫ t : ℝ in Ioo 0 1, ‖F n t‖) =
      ‖laguerreExtended a n x‖/(n+1:ℝ) := by
    calc _ = ∫ t : ℝ in Ioo 0 1, ‖laguerreExtended a n x‖*t^n := by
          refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
          simp only [F, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg ht.1.le]
      _ = _ := by rw [integral_const_mul, hpow]; ring
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ in Ioo 0 1, ‖F n t‖) := by
    simp_rw [hnorm]
    simpa only [norm_div, hden] using hs.norm
  have hi := hasSum_integral_of_summable_integral_norm hF hsum
  have hval (n : ℕ) : (∫ t : ℝ in Ioo 0 1, F n t) = laguerreExtended a n x/(n+1) := by
    rw [show (F n) = fun t : ℝ => laguerreExtended a n x*((t^n:ℝ):ℂ) by
      funext t; simp [F], integral_const_mul, integral_complex_ofReal, hpow]
    push_cast
    ring
  simp_rw [hval] at hi
  have hpoint : (∫ t : ℝ in Ioo 0 1, ∑' n : ℕ, F n t) =
      ∫ t : ℝ in Ioo 0 1, generatingKernel a x t := by
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    exact (hasSum_laguerreExtended_generating_function (α := a) (x := (x:ℂ))
      (t := (t:ℂ)) (by simpa only [norm_real, Real.norm_of_nonneg ht.1.le] using ht.2)).tsum_eq
  rw [hpoint] at hi
  have h := hi.mul_left ((x:ℂ)^a*exp (-(x:ℂ)))
  rw [integral_generatingKernel_eq_upperIncompleteGamma a hx] at h
  exact h.congr_fun fun n => by ring

end DLMF.Confluent.IncompleteGammaLaguerre
