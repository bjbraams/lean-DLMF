/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import DLMF.Confluent.IncompleteGamma
public import DLMF.ErrorFunctions.Basic

/-!
# Generalized and inverse error functions, DLMF §§7.16–7.17

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics Polynomial DLMF.Hypergeometric DLMF
open scoped Real Topology Nat ContDiff
namespace DLMF.Confluent

/-- Generalized error integral of DLMF §7.16. -/
def Real.generalizedErrorIntegral (p x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.exp (-t^p)

/-- Generalized unscaled Dawson integral of DLMF §7.16. -/
def Real.generalizedDawsonIntegral (p x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.exp (t^p)

/-- Change of variable to incomplete Gamma in DLMF §7.16. -/
theorem Real.generalizedErrorIntegral_gamma {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    (Real.generalizedErrorIntegral p x : ℂ)=lowerIncGamma (1/p) ((x^p : ℝ) : ℂ)/p := by
  have hxp : 0 < x^p := Real.rpow_pos_of_pos hx p
  -- real change of variables u = t^p
  let G : ℝ → ℝ := fun u => u^(1/p-1)*Real.exp (-u)/p
  have hreal : (∫ t in (0:ℝ)..x, Real.exp (-t^p)) = ∫ u in (0:ℝ)..x^p, G u := by
    rw [intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_of_le hxp.le]
    have h := integral_comp_rpow_Ioi_of_pos (g := (Iic (x^p)).indicator G) hp
    have hR : (∫ y in Ioi 0, (Iic (x^p)).indicator G y) = ∫ u in Ioc 0 (x^p), G u := by
      rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        Iic_inter_Ioi]
    have hL : (∫ t in Ioi 0, (p * t^(p-1)) • (Iic (x^p)).indicator G (t^p)) =
        ∫ t in Ioc 0 x, Real.exp (-t^p) := by
      rw [← Iic_inter_Ioi, ← Measure.restrict_restrict measurableSet_Iic,
        ← integral_indicator measurableSet_Iic]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := ht
      by_cases htx : t ≤ x
      · have h1 : t^p ≤ x^p := Real.rpow_le_rpow ht0.le htx hp.le
        rw [indicator_of_mem (show t^p ∈ Iic (x^p) from h1),
          indicator_of_mem (show t ∈ Iic x from htx), smul_eq_mul]
        simp only [G]
        rw [← Real.rpow_mul ht0.le, show p*(1/p-1) = 1-p by field_simp]
        have h2 : t^(p-1)*t^(1-p) = 1 := by
          rw [← Real.rpow_add ht0, show p-1+(1-p) = 0 by ring, Real.rpow_zero]
        calc p*t^(p-1)*(t^(1-p)*Real.exp (-t^p)/p) = (t^(p-1)*t^(1-p))*Real.exp (-t^p) := by
              field_simp
          _ = _ := by rw [h2, one_mul]
      · have h1 : ¬ t^p ≤ x^p := fun h => htx ((Real.rpow_le_rpow_iff ht0.le hx.le hp).mp h)
        rw [indicator_of_notMem (show t^p ∉ Iic (x^p) from h1),
          indicator_of_notMem (show t ∉ Iic x from htx), smul_zero]
    rw [← hL, h, hR]
  have hpc : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [lowerIncGamma_eq_integral (by simp [hp]) hxp, Real.generalizedErrorIntegral, hreal,
    ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun u hu => ?_)
  rw [uIoc_of_le hxp.le] at hu
  simp only [G]
  push_cast
  rw [Complex.ofReal_cpow hu.1.le]
  push_cast
  ring

/-- `(a)_n (a+n) = a (a+1)_n`. -/
theorem poch_mul_add_nat (a : ℂ) (n : ℕ) : poch a n*(a+n) = a*poch (a+1) n := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, poch_succ, mul_assoc, ← mul_assoc (poch a n), ih]; push_cast; ring

/-- Termwise integration of `exp(t^p)` on `[0, x]`. -/
theorem hasSum_generalizedDawsonIntegral {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    HasSum (fun n : ℕ => x^(p*n+1)/((p*n+1)*(n ! : ℝ))) (Real.generalizedDawsonIntegral p x) := by
  have hexp (y : ℝ) : HasSum (fun n : ℕ => y^n/(n ! : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y
  have hc : Continuous fun t : ℝ => t^p := Real.continuous_rpow_const hp.le
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0) (b := x)
    (F := fun (n : ℕ) (t : ℝ) => (t^p)^n/(n ! : ℝ)) (f := fun t => Real.exp (t^p))
    (fun n t => (t^p)^n/(n ! : ℝ))
    (fun n => ((hc.pow n).div_const _).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun t ht => by
      rw [uIoc_of_le hx.le] at ht
      have : 0 ≤ (t^p)^n/(n ! : ℝ) := by
        have := Real.rpow_nonneg ht.1.le p; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg this])
    (Eventually.of_forall fun t _ => (hexp _).summable)
    (by
      have : (fun t : ℝ => ∑' n : ℕ, (t^p)^n/(n ! : ℝ)) = fun t => Real.exp (t^p) :=
        funext fun t => (hexp _).tsum_eq
      rw [this]; exact (Real.continuous_exp.comp hc).intervalIntegrable _ _)
    (Eventually.of_forall fun t _ => hexp _)
  refine h.congr_fun fun n => ?_
  rw [intervalIntegral.integral_div]
  have he : ∫ t in (0:ℝ)..x, (t^p)^n = ∫ t in (0:ℝ)..x, t^(p*n) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hx.le] at ht
    rw [Real.rpow_mul ht.1, Real.rpow_natCast]
  rw [he, integral_rpow (Or.inl (by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])),
    Real.zero_rpow (by positivity)]
  field_simp
  ring

/-- The negative-argument Gamma formula retains the compensating branch factor. -/
theorem Real.generalizedDawsonIntegral_gamma {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    (Real.generalizedDawsonIntegral p x : ℂ)=exp (-π*I/p)/p*lowerIncGamma (1/p) (-(x^p : ℝ)) := by
  set X : ℝ := x^p with hXdef
  have hX : 0 < X := Real.rpow_pos_of_pos hx p
  set a : ℂ := ((1/p:ℝ):ℂ) with ha
  have hpc : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hxc : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  -- the Kummer series
  have hS : HasSum (fun n : ℕ => poch a n/(poch (a+1) n*n !)*(X:ℂ)^n)
      ((Real.generalizedDawsonIntegral p x : ℂ)/x) := by
    have h := (Complex.hasSum_ofReal.mpr (hasSum_generalizedDawsonIntegral hp hx)).div_const (x:ℂ)
    refine h.congr_fun fun n => ?_
    have hna : (a+1) ∉ Set.range (fun k : ℕ => -(k:ℂ)) := by
      rintro ⟨k, hk⟩
      have := congrArg Complex.re hk
      simp [ha] at this
      have : (0:ℝ) < p⁻¹+1 := by positivity
      linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hp0 : poch (a+1) n ≠ 0 := poch_ne_zero_of_not_neg_nat
      (fun k hk => hna ⟨k, hk.symm⟩) n
    have han : a+n ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp [ha] at this
      have : (0:ℝ) < p⁻¹ := by positivity
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hpoch : poch a n = a*poch (a+1) n/(a+n) := by
      rw [← poch_mul_add_nat]; field_simp
    rw [hpoch]
    have hxn : ((x^(p*n+1):ℝ):ℂ) = (x:ℂ)*(X:ℂ)^n := by
      rw [Real.rpow_add hx, Real.rpow_one, Real.rpow_mul hx.le, Real.rpow_natCast]; push_cast; ring
    push_cast
    rw [hxn]
    have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hpn : (p:ℂ)*n+1 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this
      nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    rw [show a*poch (a+1) n/(a+n)/(poch (a+1) n*n !) = a/((a+n)*n !) by field_simp]
    have hpn' : 1+(p:ℂ)*n ≠ 0 := by rw [add_comm]; exact hpn
    rw [ha]
    push_cast
    field_simp
    ring
  have hM : kummerM a (a+1) X = (Real.generalizedDawsonIntegral p x : ℂ)/x := by
    unfold kummerM; exact hS.tsum_eq
  have hpow : ((-(X:ℂ)))^a = x*exp (π*I*a) := by
    rw [show -(X:ℂ) = ((-X:ℝ):ℂ) by push_cast; ring, ofReal_cpow_of_nonpos (by linarith),
      show -((-X:ℝ):ℂ) = ((X:ℝ):ℂ) by push_cast; ring, ha, ← ofReal_cpow hX.le, one_div,
      hXdef, Real.rpow_rpow_inv hx.le hp.ne']
  have ha0 : a ≠ 0 := by simp [ha, hp.ne']
  rw [lowerIncGamma, show (1/(p:ℂ)) = a by simp [ha], hpow, neg_neg, hM]
  simp only [ha]
  push_cast
  have he' : exp (-(π*I/p))*exp (π*I/p) = 1 := by rw [← Complex.exp_add]; simp
  field_simp
  linear_combination (-(Real.generalizedDawsonIntegral p x:ℂ))*he'

/-- Inverse erf on (-1,1), reusing TauCeti; zero outside that interval. -/
@[dlmf 7.17.E1]
def Real.invErf (x : ℝ) : ℝ :=
  _root_.Real.erfInv x

/-- Inverse erfc on (0,2), with totalization inherited from invErf. -/
@[dlmf 7.17.E1]
def Real.invErfc (x : ℝ) : ℝ :=
  Real.invErf (1-x)

/-- Inverse identity; `Real.erf_erfInv` from TauCeti supplies the real theorem. -/
theorem Real.invErf_spec {x : ℝ} (hx : |x| < 1) :
    (erf (Real.invErf x)).re=x := by
  rw [erf_ofReal]
  simpa [Real.invErf] using _root_.Real.erf_erfInv (abs_lt.mp hx)

/-- Inverse complementary error function identity. -/
theorem Real.invErfc_spec {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    (erfc (Real.invErfc x)).re=x := by
  have h : |1-x| < 1 := abs_lt.mpr (by constructor <;> linarith)
  have he := Real.invErf_spec h
  change (erfc (Real.invErf (1-x))).re=x
  change (1-erf (Real.invErf (1-x))).re=x
  simp only [Complex.sub_re, Complex.one_re, he]
  ring

/-- Coefficients of the inverse-erf series from the unnumbered recurrence after 7.17.2. -/
def invErfSeriesCoeff : ℕ → ℝ
  | 0 => 1
  | m+1 => (∑ n ∈ Finset.range (m+1), (2*n+1 : ℝ)/(m-n+1 : ℕ)*
      invErfSeriesCoeff (m-n)*invErfSeriesCoeff (m-(m-n)))/(2*m+3)
termination_by m => m

/-- invErfSeriesCoeff initial. -/
@[dlmf 7.17.E2]
theorem invErfSeriesCoeff_initial  :
    ∀ n < 4, invErfSeriesCoeff n=([1,1/3,7/30,127/630] : List ℝ)[n]! := by
  intro n hn
  interval_cases n <;> norm_num [invErfSeriesCoeff, Finset.sum_range_succ]

/-- The unnumbered inverse-erf coefficient recurrence. -/
theorem invErfSeriesCoeff_recurrence (m : ℕ) :
    invErfSeriesCoeff (m+1)=(∑ n ∈ Finset.range (m+1), (2*n+1 : ℝ)/(m-n+1 : ℕ)*invErfSeriesCoeff n*invErfSeriesCoeff (m-n))/(2*m+3) := by
  rw [invErfSeriesCoeff]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  ring

/-- Analyticity of the real inverse error function on its full interval. -/
theorem invErf_analyticAt {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    AnalyticAt ℝ Real.invErf x := by
  have hf : AnalyticAt ℝ TauCeti.Real.erf (_root_.Real.erfInv x) := by
    have h := (differentiable_erf_complex.analyticAt (_root_.Real.erfInv x : ℂ)).re_ofReal
    simpa only [erf_ofReal, Complex.ofReal_re] using h
  have hd : deriv TauCeti.Real.erf (_root_.Real.erfInv x) ≠ 0 := by
    rw [(TauCeti.Real.hasDerivAt_erf _).deriv]
    positivity
  have hcomp : AnalyticAt ℝ (_root_.Real.erfInv ∘ TauCeti.Real.erf) (_root_.Real.erfInv x) := by
    apply (analyticAt_id : AnalyticAt ℝ id (_root_.Real.erfInv x)).congr
    exact Eventually.of_forall fun y => (_root_.Real.erfInv_erf y).symm
  have h := (analyticAt_comp_iff_of_deriv_ne_zero hf hd).mp hcomp
  rw [_root_.Real.erf_erfInv hx] at h
  exact h.congr (Eventually.of_forall fun y => rfl)

/-- The derivative of the project's real inverse error function. -/
theorem hasDerivAt_invErf {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.invErf (Real.sqrt π / 2 * Real.exp (Real.invErf x ^ 2)) x := by
  change HasDerivAt _root_.Real.erfInv _ x
  exact _root_.Real.hasDerivAt_erfInv hx

/-- Polynomials controlling the successive inverse-erf derivatives. -/
def invErfDerivativePoly : ℕ → Polynomial ℝ
  | 0 => X
  | n+1 => (invErfDerivativePoly n).derivative + C (2*(n : ℝ)) * (X * invErfDerivativePoly n)

/-- Every coefficient of the inverse-erf derivative polynomials is nonnegative. -/
theorem invErfDerivativePoly_coeff_nonneg (n k : ℕ) :
    0 ≤ (invErfDerivativePoly n).coeff k := by
  induction n generalizing k with
  | zero => simp only [invErfDerivativePoly, coeff_X]; split_ifs <;> positivity
  | succ n ih =>
    rw [invErfDerivativePoly, coeff_add, coeff_derivative, coeff_C_mul]
    refine add_nonneg (mul_nonneg (ih _) (by positivity)) ?_
    refine mul_nonneg (by positivity) ?_
    cases k with
    | zero => simp
    | succ k => simpa only [Nat.succ_eq_add_one, coeff_X_mul] using ih k

/-- Evaluation of the derivative polynomials is nonnegative on the positive axis. -/
theorem invErfDerivativePoly_eval_nonneg (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (invErfDerivativePoly n).eval u := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (invErfDerivativePoly_coeff_nonneg n k)
    (pow_nonneg hu _)

/-- Explicit polynomial form of every derivative on the inverse interval. -/
theorem iteratedDeriv_invErf (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    iteratedDeriv n Real.invErf x =
      (Real.sqrt π / 2)^n * (invErfDerivativePoly n).eval (Real.invErf x) *
        Real.exp ((n : ℝ) * Real.invErf x ^ 2) := by
  induction n generalizing x with
  | zero => simp [invErfDerivativePoly]
  | succ n ih =>
    have he : iteratedDeriv n Real.invErf =ᶠ[𝓝 x]
        fun y => (Real.sqrt π / 2)^n * (invErfDerivativePoly n).eval (Real.invErf y) *
          Real.exp ((n : ℝ) * Real.invErf y ^ 2) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using ih hy
    have hf := hasDerivAt_invErf hx
    have hp := ((invErfDerivativePoly n).hasDerivAt (Real.invErf x)).comp x hf
    have hE := ((hf.pow 2).const_mul (n : ℝ)).exp
    have hD := (hp.const_mul ((Real.sqrt π / 2)^n)).mul hE
    have hD' := hD.congr_of_eventuallyEq he
    rw [iteratedDeriv_succ, hD'.deriv]
    simp only [invErfDerivativePoly, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Nat.cast_add, Nat.cast_one, pow_succ,
      Function.comp_apply, Pi.pow_apply, Nat.reduceSub]
    rw [add_mul, Real.exp_add]
    ring

/-- The real inverse error function is nonnegative on the positive half-interval. -/
theorem invErf_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : 0 ≤ Real.invErf x := by
  have h := _root_.Real.strictMonoOn_erfInv.monotoneOn
    (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by norm_num)
    (show x ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith, hx1⟩) hx0
  simpa only [_root_.Real.erfInv_zero, Real.invErf] using h

/-- Every real derivative of inverse erf is nonnegative on `[0,1)`. -/
theorem iteratedDeriv_invErf_nonneg (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ iteratedDeriv n Real.invErf x := by
  rw [iteratedDeriv_invErf n ⟨by linarith, hx1⟩]
  exact mul_nonneg (mul_nonneg (by positivity)
    (invErfDerivativePoly_eval_nonneg n (invErf_nonneg hx0 hx1))) (Real.exp_pos _).le

/-- The full Taylor coefficients of inverse erf at zero. -/
def invErfTaylorCoeff (n : ℕ) : ℝ := iteratedDeriv n Real.invErf 0 / (n.factorial : ℝ)

/-- Its Taylor coefficients are all nonnegative. -/
theorem invErfTaylorCoeff_nonneg (n : ℕ) : 0 ≤ invErfTaylorCoeff n :=
  div_nonneg (iteratedDeriv_invErf_nonneg n (by norm_num) (by norm_num)) (by positivity)

/-- Every Taylor partial sum on the positive half-interval is below inverse erf. -/
theorem invErfTaylor_sum_le {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), invErfTaylorCoeff k * y^k ≤ Real.invErf y := by
  have hcont : ContDiffOn ℝ (n + 1) Real.invErf (uIcc (0 : ℝ) y) := by
    intro z hz
    rw [uIcc_of_le hy0.le] at hz
    exact (invErf_analyticAt ⟨by linarith [hz.1], by linarith [hz.2]⟩).contDiffAt.contDiffWithinAt
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hy0.ne'.symm hcont
  have ht : taylorWithinEval Real.invErf n (uIcc (0 : ℝ) y) 0 y =
      ∑ k ∈ Finset.range (n+1), invErfTaylorCoeff k*y^k := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hy0.ne'.symm)
      (invErf_analyticAt (x := 0) (by norm_num)).contDiffAt (by simp)]
    simp only [sub_zero, smul_eq_mul, invErfTaylorCoeff, div_eq_mul_inv]
    ring
  rw [ht] at he
  rw [uIoo_of_lt hy0] at hz
  have hn : 0 ≤ iteratedDeriv (n+1) Real.invErf z :=
    iteratedDeriv_invErf_nonneg _ hz.1.le (hz.2.trans hy1)
  have hr : 0 ≤ iteratedDeriv (n+1) Real.invErf z * (y-0)^(n+1)/(n+1).factorial := by positivity
  linarith

/-- A positive-axis value bounds each nonnegative Taylor term individually. -/
theorem invErfTaylor_term_le {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (n : ℕ) :
    invErfTaylorCoeff n * y^n ≤ Real.invErf y := by
  have ht : invErfTaylorCoeff n*y^n ≤ ∑ k ∈ Finset.range (n+1), invErfTaylorCoeff k*y^k :=
    Finset.single_le_sum (f := fun k : ℕ => invErfTaylorCoeff k*y^k)
      (fun k _ => mul_nonneg (invErfTaylorCoeff_nonneg k) (pow_nonneg hy0.le k))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  exact ht.trans (invErfTaylor_sum_le hy0 hy1 n)

/-- The Taylor series of inverse erf converges absolutely throughout `(-1,1)`. -/
theorem summable_invErfTaylor {x : ℝ} (hx : |x| < 1) :
    Summable fun n => invErfTaylorCoeff n*x^n := by
  let y := (|x|+1)/2
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hxy : |x| < y := by dsimp [y]; linarith
  have hy1 : y < 1 := by dsimp [y]; linarith
  have hq0 : 0 ≤ |x|/y := div_nonneg (abs_nonneg _) hy0.le
  have hq1 : |x|/y < 1 := (div_lt_one hy0).mpr hxy
  have hg : Summable fun n : ℕ => Real.invErf y*(|x|/y)^n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hg
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (invErfTaylorCoeff_nonneg _), abs_pow]
  calc invErfTaylorCoeff n * |x|^n =
        (invErfTaylorCoeff n*y^n)*(|x|/y)^n := by
          rw [div_pow |x| y n]
          field_simp [hy0.ne']
    _ ≤ Real.invErf y*(|x|/y)^n :=
      mul_le_mul_of_nonneg_right (invErfTaylor_term_le hy0 hy1 n) (pow_nonneg hq0 _)

/-- The actual Taylor series represents inverse erf throughout its full interval. -/
theorem hasSum_invErfTaylor {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n => invErfTaylorCoeff n*x^n) (Real.invErf x) := by
  let p := FormalMultilinearSeries.ofScalars ℝ invErfTaylorCoeff
  have hr : (1 : ENNReal) ≤ p.radius := by
    refine ENNReal.le_of_forall_pos_nnreal_lt fun r hr hr1 => ?_
    have hr1' : (r : ℝ) < 1 := by exact_mod_cast hr1
    have hs := (summable_invErfTaylor (x := (r : ℝ))
      (by simpa only [abs_of_nonneg r.coe_nonneg] using hr1')).norm
    apply p.le_radius_of_summable_norm
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg] using hs
  have ha : AnalyticOn ℝ Real.invErf (Metric.eball (0 : ℝ) (1 : ENNReal)) := by
    intro y hy
    have hy' : |y| < 1 := by
      simpa only [← ENNReal.coe_one, Metric.eball_coe, Metric.mem_ball, Real.dist_eq,
        sub_zero, NNReal.coe_one] using hy
    exact (invErf_analyticAt (abs_lt.mp hy')).analyticWithinAt
  have hp := ha.hasFPowerSeriesOnSubball (by norm_num : (0 : ENNReal) < 1) hr
  have hx' : x ∈ Metric.eball (0 : ℝ) (1 : ENNReal) := by
    simpa only [← ENNReal.coe_one, Metric.eball_coe, Metric.mem_ball, Real.dist_eq,
      sub_zero, NNReal.coe_one] using hx
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add,
    invErfTaylorCoeff, mul_comm] using hp.hasSum hx'

/-- Scalar Taylor coefficients at zero, used for the convolution calculation. -/
private def erfInvTC (f : ℝ → ℝ) (n : ℕ) : ℝ := iteratedDeriv n f 0 / (n.factorial : ℝ)

/-- Differentiation shifts scalar Taylor coefficients. -/
private lemma erfInvTC_deriv (f : ℝ → ℝ) (n : ℕ) :
    erfInvTC (deriv f) n = (n+1) * erfInvTC f (n+1) := by
  unfold erfInvTC
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

/-- The Leibniz rule gives convolution of scalar Taylor coefficients. -/
private lemma erfInvTC_mul {f g : ℝ → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (hg : ContDiffAt ℝ ∞ g 0) (n : ℕ) :
    erfInvTC (fun x => f x*g x) n =
      ∑ k ∈ Finset.range (n+1), erfInvTC f k * erfInvTC g (n-k) := by
  unfold erfInvTC
  rw [iteratedDeriv_fun_mul (hf.of_le (by exact_mod_cast le_top))
    (hg.of_le (by exact_mod_cast le_top)), Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hchoose : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n-k).factorial : ℝ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  field_simp
  linear_combination iteratedDeriv k f 0 * iteratedDeriv (n-k) g 0 * hchoose

/-- All even Taylor coefficients of inverse erf vanish by oddness. -/
theorem invErfTaylorCoeff_even (m : ℕ) : invErfTaylorCoeff (2*m) = 0 := by
  have he : (fun x : ℝ => Real.invErf (-x)) = fun x => -Real.invErf x := by
    funext x
    exact _root_.Real.erfInv_neg x
  have h := congrArg (fun f : ℝ → ℝ => iteratedDeriv (2*m) f 0) he
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at h
  simp only [neg_zero, Even.neg_one_pow (even_two_mul m), one_smul] at h
  unfold invErfTaylorCoeff
  have hz : iteratedDeriv (2*m) Real.invErf 0 = 0 := by linarith
  rw [hz, zero_div]

/-- Pairing adjacent terms in an even-length finite sum. -/
private lemma erfInv_sum_pairs (f : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (2*m), f k = ∑ k ∈ Finset.range m, (f (2*k)+f (2*k+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1)=2*m+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- The auxiliary primitive obtained from the inverse Gaussian differential equation. -/
private def erfInvAuxH (x : ℝ) : ℝ := 1-Real.exp (-(Real.invErf x)^2)

/-- Its derivative is a constant multiple of inverse erf. -/
private lemma erfInvAuxH_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt erfInvAuxH (2*(Real.sqrt π/2)*Real.invErf x) x := by
  change HasDerivAt (fun y : ℝ => 1-Real.exp (-(Real.invErf y)^2)) _ x
  have h := (((hasDerivAt_invErf hx).pow 2).neg.exp).const_sub 1
  apply h.congr_deriv
  simp only [Nat.reduceSub, pow_one]
  have hE : Real.exp (-(Real.invErf x)^2)*Real.exp ((Real.invErf x)^2)=1 := by
    rw [← Real.exp_add]; simp
  linear_combination (2*(Real.sqrt π/2)*Real.invErf x)*hE

/-- The primitive normalizes the first derivative multiplicatively. -/
private lemma deriv_invErf_eq_add_mul_H {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    deriv Real.invErf x = Real.sqrt π/2 + deriv Real.invErf x*erfInvAuxH x := by
  rw [(hasDerivAt_invErf hx).deriv, erfInvAuxH]
  have hE : Real.exp ((Real.invErf x)^2)*Real.exp (-(Real.invErf x)^2)=1 := by
    rw [← Real.exp_add]; simp
  linear_combination (Real.sqrt π/2)*hE

/-- Coefficients of the auxiliary primitive in terms of the inverse-erf coefficients. -/
private lemma erfInvTC_H (n : ℕ) :
    erfInvTC erfInvAuxH (n+1) = 2*(Real.sqrt π/2)*invErfTaylorCoeff n/(n+1) := by
  have he : deriv erfInvAuxH =ᶠ[𝓝 (0 : ℝ)] fun x => 2*(Real.sqrt π/2)*Real.invErf x := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ)<0) (by norm_num : (0 : ℝ)<1)] with x hx
    exact (erfInvAuxH_hasDerivAt hx).deriv
  have h := he.iteratedDeriv_eq n
  have hc := congrArg (fun z : ℝ => z/(n.factorial : ℝ)) h
  rw [iteratedDeriv_const_mul_field] at hc
  have hc' : erfInvTC (deriv erfInvAuxH) n = 2*(Real.sqrt π/2)*invErfTaylorCoeff n := by
    simpa only [erfInvTC, invErfTaylorCoeff, mul_div_assoc] using hc
  rw [erfInvTC_deriv] at hc'
  apply (eq_div_iff (by positivity : (n : ℝ)+1 ≠ 0)).mpr
  linear_combination hc'

/-- Taylor's convolution identity for the inverse differential equation. -/
private lemma invErfTaylor_recurrence {n : ℕ} (hn : 0 < n) :
    (n+1)*invErfTaylorCoeff (n+1) =
      ∑ k ∈ Finset.range (n+1), (k+1)*invErfTaylorCoeff (k+1)*erfInvTC erfInvAuxH (n-k) := by
  have he : deriv Real.invErf =ᶠ[𝓝 (0 : ℝ)]
      fun x => Real.sqrt π/2 + deriv Real.invErf x*erfInvAuxH x := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ)<0) (by norm_num : (0 : ℝ)<1)] with x hx
    exact deriv_invErf_eq_add_mul_H hx
  have h := he.iteratedDeriv_eq n
  rw [iteratedDeriv_const_add hn] at h
  have hc := congrArg (fun z : ℝ => z/(n.factorial : ℝ)) h
  change erfInvTC (deriv Real.invErf) n = erfInvTC (fun x => deriv Real.invErf x*erfInvAuxH x) n at hc
  have ha := invErf_analyticAt (x := 0) (by norm_num)
  have hH : AnalyticAt ℝ erfInvAuxH 0 := analyticAt_const.sub (ha.pow 2).neg.rexp'
  rw [erfInvTC_deriv, erfInvTC_mul ha.deriv.contDiffAt hH.contDiffAt] at hc
  simp_rw [erfInvTC_deriv] at hc
  exact hc

/-- The constant coefficient of the auxiliary primitive vanishes. -/
private lemma erfInvTC_H_zero : erfInvTC erfInvAuxH 0 = 0 := by
  simp only [erfInvTC, iteratedDeriv_zero, erfInvAuxH, Real.invErf,
    _root_.Real.erfInv_zero, zero_pow (by norm_num : 2 ≠ 0), neg_zero, Real.exp_zero,
    sub_self, zero_div]

/-- Pairing parity in the Taylor equation yields the odd-coefficient recurrence. -/
private lemma invErfTaylor_odd_recurrence (m : ℕ) :
    (2*(m : ℝ)+3)*invErfTaylorCoeff (2*(m+1)+1) =
      (Real.sqrt π/2)* ∑ j ∈ Finset.range (m+1),
        (2*(j : ℝ)+1)/(m-j+1 : ℕ)*invErfTaylorCoeff (2*j+1)*
          invErfTaylorCoeff (2*(m-j)+1) := by
  have h := invErfTaylor_recurrence (n := 2*m+2) (by omega)
  rw [Finset.sum_range_succ] at h
  simp only [Nat.sub_self, erfInvTC_H_zero, mul_zero, add_zero] at h
  have hpair : (∑ k ∈ Finset.range (2*m+2),
      (k+1)*invErfTaylorCoeff (k+1)*erfInvTC erfInvAuxH (2*m+2-k)) =
      ∑ j ∈ Finset.range (m+1), (Real.sqrt π/2)*
        ((2*(j : ℝ)+1)/(m-j+1 : ℕ)*invErfTaylorCoeff (2*j+1)*
          invErfTaylorCoeff (2*(m-j)+1)) := by
    rw [show 2*m+2 = 2*(m+1) by omega, erfInv_sum_pairs]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have heven : invErfTaylorCoeff (2*j+1+1) = 0 := by
      convert invErfTaylorCoeff_even (j+1) using 1
    rw [heven, mul_zero, zero_mul, add_zero]
    have hdiff : 2*(m+1)-2*j = (2*(m-j)+1)+1 := by omega
    rw [hdiff, erfInvTC_H]
    push_cast
    field_simp
    ring
  rw [hpair, ← Finset.mul_sum] at h
  rw [show 2*m+2+1=2*(m+1)+1 by omega] at h
  convert h using 1
  push_cast
  ring

/-- The odd Taylor coefficients are exactly the acquired recurrence coefficients. -/
theorem invErfTaylorCoeff_odd (m : ℕ) :
    invErfTaylorCoeff (2*m+1) = (Real.sqrt π/2)^(2*m+1)*invErfSeriesCoeff m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      simp only [Nat.mul_zero, zero_add, invErfTaylorCoeff, iteratedDeriv_one,
        (hasDerivAt_invErf (x := 0) (by norm_num)).deriv, Real.invErf,
        _root_.Real.erfInv_zero, zero_pow (by norm_num : 2 ≠ 0), Real.exp_zero,
        mul_one, Nat.factorial_one, Nat.cast_one, div_one, invErfSeriesCoeff, pow_one]
    | succ m =>
      have h := invErfTaylor_odd_recurrence m
      have hsum : (∑ j ∈ Finset.range (m+1),
          (2*(j : ℝ)+1)/(m-j+1 : ℕ)*invErfTaylorCoeff (2*j+1)*
            invErfTaylorCoeff (2*(m-j)+1)) =
          (Real.sqrt π/2)^(2*(m+1))*
            ∑ j ∈ Finset.range (m+1), (2*(j : ℝ)+1)/(m-j+1 : ℕ)*
              invErfSeriesCoeff j*invErfSeriesCoeff (m-j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [ih j (by omega), ih (m-j) (by omega)]
        have hp : (Real.sqrt π/2)^(2*j+1)*(Real.sqrt π/2)^(2*(m-j)+1) =
            (Real.sqrt π/2)^(2*(m+1)) := by
          rw [← pow_add]
          congr 1
          omega
        linear_combination ((2*(j : ℝ)+1)/(m-j+1 : ℕ)*
          invErfSeriesCoeff j*invErfSeriesCoeff (m-j))*hp
      rw [hsum] at h
      have hcoeff : (∑ j ∈ Finset.range (m+1), (2*(j : ℝ)+1)/(m-j+1 : ℕ)*
          invErfSeriesCoeff j*invErfSeriesCoeff (m-j)) =
          (2*(m : ℝ)+3)*invErfSeriesCoeff (m+1) := by
        rw [invErfSeriesCoeff_recurrence]
        field_simp
      rw [hcoeff] at h
      have hden : (2*(m : ℝ)+3) ≠ 0 := by positivity
      apply mul_left_cancel₀ hden
      calc
        (2*(m : ℝ)+3)*invErfTaylorCoeff (2*(m+1)+1) =
            (Real.sqrt π/2)*((Real.sqrt π/2)^(2*(m+1))*
              ((2*(m : ℝ)+3)*invErfSeriesCoeff (m+1))) := h
        _ = (2*(m : ℝ)+3)*((Real.sqrt π/2)^(2*(m+1)+1)*invErfSeriesCoeff (m+1)) := by
          rw [pow_succ]
          ring

/-- The acquired inverse-erf expansion, with its full interval of convergence. -/
@[dlmf 7.17.E2]
theorem hasSum_invErf {x : ℝ} (hx : |x| < 1) :
    HasSum (fun m : ℕ => invErfSeriesCoeff m*(Real.sqrt π*x/2)^(2*m+1)) (Real.invErf x) := by
  have hfull := hasSum_invErfTaylor hx
  have hodd : Summable fun m : ℕ => invErfTaylorCoeff (2*m+1)*x^(2*m+1) :=
    hfull.summable.comp_injective (by
      intro m n h
      change 2*m+1=2*n+1 at h
      omega)
  have heven : HasSum (fun m : ℕ => invErfTaylorCoeff (2*m)*x^(2*m)) 0 := by
    simpa only [invErfTaylorCoeff_even, zero_mul] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have he := hfull.unique (heven.even_add_odd hodd.hasSum)
  rw [zero_add] at he
  have ho : HasSum (fun m : ℕ => invErfTaylorCoeff (2*m+1)*x^(2*m+1)) (Real.invErf x) := by
    rw [he]
    exact hodd.hasSum
  refine ho.congr_fun fun m => ?_
  rw [invErfTaylorCoeff_odd]
  have hb : Real.sqrt π*x/2=(Real.sqrt π/2)*x := by ring
  rw [hb, mul_pow]
  ring

/-- Small-argument inverse-erfc variable u. -/
@[dlmf 7.17.E5]
def invErfcAsymptoticU (x : ℝ) : ℝ :=
  -2/Real.log (π*x^2*Real.log (1/x))

/-- Small-argument inverse-erfc logarithmic variable v. -/
@[dlmf 7.17.E6]
def invErfcAsymptoticV (x : ℝ) : ℝ :=
  Real.log (Real.log (1/x))-2+Real.log π

/-- All-order expansion with polynomial logarithmic coefficients. -/
@[dlmf 7.17.E3, dlmf 7.17.E4]
theorem invErfc_asymptotic  :
    ∃ c : ℕ → Polynomial ℝ, (∀ v : ℝ, (c 0).eval v=1 ∧ (c 1).eval v=0 ∧ (c 2).eval v=v/8 ∧ (c 3).eval v = -(v^2+6*v-6)/32 ∧ (c 4).eval v=(4*v^3+27*v^2+108*v-300)/384) ∧ ∀ N : ℕ, IsBigO (𝓝[>] (0 : ℝ)) (fun x => Real.invErfc x-∑ n ∈ Finset.range N, (c n).eval (invErfcAsymptoticV x)*(invErfcAsymptoticU x)^((n : ℝ)-1/2)) (fun x => (invErfcAsymptoticU x)^((N : ℝ)-1/2)*(1+|invErfcAsymptoticV x|)^N) := by
  sorry

end DLMF.Confluent
