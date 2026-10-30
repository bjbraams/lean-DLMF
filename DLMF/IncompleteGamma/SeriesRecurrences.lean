/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.SphericalSeriesTools
public import DLMF.IncompleteGamma.SpecialValues

/-!
# Series, recurrences and derivatives, DLMF §§8.7–8.8

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Statistical

/-- The series with terms `(fun k : ℕ => (-z)^k/(Gamma a*(k.factorial : ℂ)*(a+k)))` converges to
`(scIncGamma a z)`. -/
@[dlmf 8.7.E1]
theorem scIncGamma_hasSum_alternating {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    HasSum (fun k : ℕ => (-z)^k/(Gamma a*(k.factorial : ℂ)*(a+k))) (scIncGamma a z) := by
  have hs := (hasFPowerSeriesOnBall_regularizedConfluent a (a+1)).hasSum_mul_pow
    (by simp : -z ∈ Metric.eball (0:ℂ) ⊤)
  have he : regularizedHGFun {a} {a+1} (-z)=scIncGamma a z := by
    simpa [add_comm] using (scIncGamma_regularized_pair a z).2.symm
  rw [he] at hs
  refine hs.congr_fun fun k => ?_
  have hk : a+(k:ℂ) ≠ 0 := by intro h; exact ha k (by linear_combination h)
  have hG : Gamma (a+k) ≠ 0 := Gamma_ne_zero (fun n h => ha (k+n) (by push_cast; linear_combination h))
  rw [regularizedHGFunCoeff_singleton, poch, ← Gamma_add_nat_div_Gamma_eq a ha,
    show a+1+k=(a+k)+1 by ring, Gamma_add_one _ hk]
  field_simp [Gamma_ne_zero ha, hG]

/-- Derivative of the exponential partial sum: `e_n' = e_n - z^n/n!`. -/
theorem incrSer_hasDerivAt_expPartialSum (n : ℕ) (s : ℂ) :
    HasDerivAt (expPartialSum n) (expPartialSum n s - s^n/(n.factorial : ℂ)) s := by
  induction n with
  | zero =>
    have : expPartialSum 0 = fun _ => 1 := by funext w; simp [expPartialSum]
    rw [this]; simpa using hasDerivAt_const s (1:ℂ)
  | succ n ih =>
    have he : expPartialSum (n+1) = fun w => expPartialSum n w + w^(n+1)/((n+1).factorial : ℂ) := by
      funext w; simp [expPartialSum, Finset.sum_range_succ]
    rw [he]
    have hp := (hasDerivAt_pow (n+1) s).div_const ((n+1).factorial : ℂ)
    refine (ih.add hp).congr_deriv ?_
    simp only [expPartialSum, Finset.sum_range_succ, Nat.factorial_succ]
    have h1 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have h2 : ((n:ℂ)+1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    push_cast
    field_simp
    ring

/-- `-n! e^{-s} e_n(s)` is a primitive of `s^n e^{-s}`. -/
theorem incrSer_hasDerivAt_primitive (n : ℕ) (s : ℂ) :
    HasDerivAt (fun w => -(n.factorial : ℂ)*(exp (-w)*expPartialSum n w)) (s^n*exp (-s)) s := by
  have h := (((hasDerivAt_neg s).cexp).mul (incrSer_hasDerivAt_expPartialSum n s)).const_mul
    (-(n.factorial : ℂ))
  refine h.congr_deriv ?_
  have h1 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp
  ring

/-- incompleteGamma increment series. The segment from `x` to `x + y` must stay in the cut plane
(corrected 2026-10-22): the series is the continuation of `γ(a, ·)` from `x` along it, and with only
`x + y ∈ slitPlane` the identity fails, e.g. at `a = 0.3`, `x = −1 + 0.1i`, `y = −0.2i`. -/
@[dlmf 8.7.E2]
theorem incompleteGamma_increment_series {a x y : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hx : x ∈ slitPlane)
    (hxy : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t * y ∈ slitPlane) (hy : ‖y‖ < ‖x‖) :
    HasSum (fun n : ℕ => exp (-x)*x^(a-1)*poch (1-a) n/(-x)^n*(1-exp (-y)*expPartialSum n y)) (lowerIncGamma a (x+y)-lowerIncGamma a x) ∧ lowerIncGamma a (x+y)-lowerIncGamma a x=upperIncGamma a x-upperIncGamma a (x+y) := by
  have hx0 : x ≠ 0 := slitPlane_ne_zero hx
  have hxy1 : x + y ∈ slitPlane := by simpa using hxy 1 ⟨zero_le_one, le_rfl⟩
  refine ⟨?_, ?_⟩
  swap
  · have h1 := lowerIncGamma_add_upperIncGamma ha hx0
    have h2 := lowerIncGamma_add_upperIncGamma ha (slitPlane_ne_zero hxy1)
    linear_combination h2 - h1
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set r : ℝ := ‖y/x‖ with hr
  have hr1 : r < 1 := by rw [hr, norm_div, div_lt_one hxn]; exact hy
  have hr0 : 0 ≤ r := norm_nonneg _
  have hI : Icc (0:ℝ) 1 = uIcc 0 1 := (uIcc_of_le zero_le_one).symm
  -- the ratio stays in the unit disk
  have hsmall : ∀ t ∈ Icc (0:ℝ) 1, ‖(t:ℂ)*y/x‖ ≤ r := by
    intro t ht
    rw [mul_div_assoc, norm_mul, hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hone : ∀ t ∈ Icc (0:ℝ) 1, 1 + (t:ℂ)*y/x ∈ slitPlane := fun t ht =>
    mem_slitPlane_of_norm_lt_one ((hsmall t ht).trans_lt hr1)
  -- branch identity along the segment
  have hlog : ∀ t ∈ Icc (0:ℝ) 1, log (x+t*y) - log (1+t*y/x) = log x := by
    have hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun t:ℝ => log (x+t*y) - log (1+t*y/x)) 0 t := by
      intro t ht
      have h1 : HasDerivAt (fun s:ℂ => x+s*y) y (t:ℂ) := by
        simpa using ((hasDerivAt_id (t:ℂ)).mul_const y).const_add x
      have h2 : HasDerivAt (fun s:ℂ => 1+s*y/x) (y/x) (t:ℂ) := by
        simpa [mul_div_assoc] using ((hasDerivAt_id (t:ℂ)).mul_const (y/x)).const_add 1
      have h := ((h1.clog (hxy t ht)).sub (h2.clog (hone t ht))).comp_ofReal
      refine h.congr_deriv ?_
      have hne : x + t*y ≠ 0 := slitPlane_ne_zero (hxy t ht)
      have hne' : 1 + t*y/x ≠ 0 := slitPlane_ne_zero (hone t ht)
      rw [show (1:ℂ) + t*y/x = (x+t*y)/x by field_simp] at hne' ⊢
      field_simp
      ring
    have hc := constant_of_has_deriv_right_zero (f := fun t:ℝ => log (x+t*y) - log (1+t*y/x))
      (a := 0) (b := 1) (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    intro t ht
    simpa using hc t ht
  have hpow : ∀ t ∈ Icc (0:ℝ) 1, (x+t*y)^(a-1) = x^(a-1)*(1+t*y/x)^(a-1) := by
    intro t ht
    rw [cpow_def_of_ne_zero (slitPlane_ne_zero (hxy t ht)), cpow_def_of_ne_zero hx0,
      cpow_def_of_ne_zero (slitPlane_ne_zero (hone t ht)), ← Complex.exp_add,
      show log (x+t*y) = log x + log (1+t*y/x) by linear_combination hlog t ht]
    ring_nf
  -- the integrand and its series
  set g : ℝ → ℂ := fun t => y*((x+t*y)^(a-1)*exp (-(x+t*y))) with hg
  set u : ℕ → ℝ → ℂ := fun n t => y*exp (-(x+t*y))*x^(a-1)*
    (poch (1-a) n/(n.factorial : ℂ)*(-((t:ℂ)*y/x))^n) with hu
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, HasSum (fun n => u n t) (g t) := by
    intro t ht
    have h := (hasSum_poch_div_factorial (β := 1-a) (z := -((t:ℂ)*y/x))
      (by rw [norm_neg]; exact (hsmall t ht).trans_lt hr1)).mul_left (y*exp (-(x+t*y))*x^(a-1))
    rw [show (1:ℂ) - -((t:ℂ)*y/x) = 1+t*y/x by ring, show -(1-a) = a-1 by ring] at h
    rw [hg]; simp only
    rw [hpow t ht]
    convert h using 1
    ring
  -- FTC for the lower incomplete Gamma along the segment
  have hFTC : ∫ t in (0:ℝ)..1, g t = lowerIncGamma a (x+y) - lowerIncGamma a x := by
    have hd : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t:ℝ => lowerIncGamma a (x+t*y)) (g t) t := by
      intro t ht
      rw [← hI] at ht
      have h1 : HasDerivAt (fun s:ℂ => x+s*y) y (t:ℂ) := by
        simpa using ((hasDerivAt_id (t:ℂ)).mul_const y).const_add x
      have h := ((hasDerivAt_incompleteGamma ha (hxy t ht)).1.comp (t:ℂ) h1).comp_ofReal
      refine h.congr_deriv ?_
      rw [hg]; ring
    have hcont : ContinuousOn g (uIcc 0 1) := by
      intro t ht
      rw [← hI] at ht
      refine ContinuousAt.continuousWithinAt ?_
      rw [hg]
      refine continuousAt_const.mul (ContinuousAt.mul ?_ (by fun_prop))
      exact ((continuousAt_const.add (continuous_ofReal.continuousAt.mul continuousAt_const)).cpow
        continuousAt_const (hxy t ht))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)]
    simp
  -- termwise integrals
  have hterm : ∀ n : ℕ, ∫ t in (0:ℝ)..1, u n t =
      exp (-x)*x^(a-1)*poch (1-a) n/(-x)^n*(1-exp (-y)*expPartialSum n y) := by
    intro n
    set c : ℂ := exp (-x)*x^(a-1)*poch (1-a) n/(n.factorial : ℂ)/(-x)^n with hc
    have hd : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt
        (fun t:ℝ => c*(-(n.factorial : ℂ)*(exp (-(t*y))*expPartialSum n (t*y)))) (u n t) t := by
      intro t _
      have h1 : HasDerivAt (fun s:ℂ => s*y) y (t:ℂ) := by
        simpa using (hasDerivAt_id (t:ℂ)).mul_const y
      have h := (((incrSer_hasDerivAt_primitive n ((t:ℂ)*y)).comp (t:ℂ) h1).const_mul c).comp_ofReal
      refine h.congr_deriv ?_
      rw [hu, hc]; simp only
      have hxn' : (-x)^n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hx0)
      have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
      rw [show -((t:ℂ)*y/x) = (t*y)/(-x) by field_simp, div_pow,
        show -(x+t*y) = -x + -(t*y) by ring, Complex.exp_add]
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by rw [hu]; fun_prop : Continuous (u n)).intervalIntegrable _ _)]
    rw [hc]
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have he0 : expPartialSum n 0 = 1 := by
      simp [expPartialSum, Finset.sum_range_succ']
    simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, he0]
    field_simp
    ring
  -- dominated convergence
  set K : ℝ := ‖y‖*Real.exp (‖x‖+‖y‖)*‖x^(a-1)‖ with hK
  have hsum := summable_norm_gaussHGCoeff_mul_pow (1-a) 1 1 (z := (r:ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := 1) (F := u) (f := g)
    (fun n t => K*‖gaussHGCoeff (1-a) 1 1 n * (r:ℂ)^n‖)
    (fun n => ((by rw [hu]; fun_prop : Continuous (u n))).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun t ht => ?_)
    (Eventually.of_forall fun t _ => hsum.mul_left K)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht => hpt t (Ioc_subset_Icc_self (by simpa using ht)))
  · rw [hFTC] at h
    exact h.congr_fun fun n => (hterm n).symm
  · have ht' : t ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self (by simpa using ht)
    rw [hu]; simp only
    rw [gaussHGCoeff_self_right, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow,
      norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hK]
    have hE : ‖exp (-(x+t*y))‖ ≤ Real.exp (‖x‖+‖y‖) := by
      refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_neg]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht'.2
    have hP : ‖(t:ℂ)*y/x‖^n ≤ r^n := pow_le_pow_left₀ (norm_nonneg _) (hsmall t ht') n
    have := mul_le_mul hE hP (by positivity) (by positivity)
    calc ‖y‖*‖exp (-(x+t*y))‖*‖x^(a-1)‖*(‖poch (1-a) n/(n.factorial:ℂ)‖*‖(t:ℂ)*y/x‖^n)
        = ‖y‖*‖x^(a-1)‖*‖poch (1-a) n/(n.factorial:ℂ)‖*(‖exp (-(x+t*y))‖*‖(t:ℂ)*y/x‖^n) := by ring
      _ ≤ ‖y‖*‖x^(a-1)‖*‖poch (1-a) n/(n.factorial:ℂ)‖*(Real.exp (‖x‖+‖y‖)*r^n) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring

/-- The series with terms `(fun k : ℕ => (-1 : ℂ)^k*z^(a+k)/((k.factorial : ℂ)*(a+k)))` converges
to `(Gamma a-upperIncGamma a z)`. -/
@[dlmf 8.7.E3]
theorem upperIncGamma_hasSum_alternating {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => (-1 : ℂ)^k*z^(a+k)/((k.factorial : ℂ)*(a+k))) (Gamma a-upperIncGamma a z) := by
  have hs := (scIncGamma_hasSum_alternating ha z).mul_left (Gamma a*z^a)
  have he : Gamma a*z^a*scIncGamma a z=Gamma a-upperIncGamma a z := by
    rw [scIncGamma_eq ha hz]
    have hp : z^a*z^(-a)=1 := by rw [← cpow_add _ _ hz]; simp
    have hc := lowerIncGamma_add_upperIncGamma ha hz
    calc
      Gamma a*z^a*(z^(-a)*lowerIncGamma a z/Gamma a) =
          (z^a*z^(-a))*lowerIncGamma a z := by field_simp [Gamma_ne_zero ha]
      _ = lowerIncGamma a z := by rw [hp, one_mul]
      _ = Gamma a-upperIncGamma a z := by linear_combination hc
  rw [he] at hs
  refine hs.congr_fun fun k => ?_
  rw [neg_pow, show a+(k:ℂ)=a+(k:ℂ) by rfl, cpow_add _ _ hz, cpow_natCast]
  field_simp [Gamma_ne_zero ha]
  ring

/-- The series with terms `(fun k : ℕ => Gamma a*z^a*exp (-z)*z^k/Gamma (a+k+1))` converges to
`(Gamma a-upperIncGamma a z)`. -/
@[dlmf 8.7.E3]
theorem upperIncGamma_hasSum_exponential {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => Gamma a*z^a*exp (-z)*z^k/Gamma (a+k+1)) (Gamma a-upperIncGamma a z) := by
  have hs := (scIncGamma_hasSum_exponential a z).mul_left (Gamma a*z^a)
  have he : Gamma a*z^a*scIncGamma a z=Gamma a-upperIncGamma a z := by
    rw [scIncGamma_eq ha hz]
    have hp : z^a*z^(-a)=1 := by rw [← cpow_add _ _ hz]; simp
    have hc := lowerIncGamma_add_upperIncGamma ha hz
    calc
      Gamma a*z^a*(z^(-a)*lowerIncGamma a z/Gamma a) =
          (z^a*z^(-a))*lowerIncGamma a z := by field_simp [Gamma_ne_zero ha]
      _ = lowerIncGamma a z := by rw [hp, one_mul]
      _ = Gamma a-upperIncGamma a z := by linear_combination hc
  rw [he] at hs
  exact hs.congr_fun fun k => by ring

/-- Formula under the stated hypotheses: `∑ p ∈ Finset.antidiagonal n, (-1 : ℂ)^p.1/((p.1)! *
(p.2)!) = 0`. -/
theorem serRec_sum_antidiagonal_neg_one_pow {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ Finset.antidiagonal n, (-1 : ℂ)^p.1/((p.1)! * (p.2)!) = 0 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hb := add_pow (-1 : ℂ) 1 n
  rw [show (-1 : ℂ) + 1 = 0 by ring, zero_pow (by omega)] at hb
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have : ∑ k ∈ Finset.range n.succ, (-1 : ℂ)^k/((k)! * ((n-k))!) =
      (∑ k ∈ Finset.range (n+1), (-1 : ℂ)^k * 1^(n-k) * (n.choose k)) / n ! := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Nat.cast_choose ℂ hk']
    have h1 : ((k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have h2 : (((n-k))! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    simp
  rw [this, ← hb, zero_div]

/-- Formula under the stated hypotheses: `∑ p ∈ Finset.antidiagonal j, expPartialSum p.1
(-1)/((p.2)! : ℂ) = 1`. -/
theorem serRec_sum_antidiagonal_expPartialSum (j : ℕ) :
    ∑ p ∈ Finset.antidiagonal j, expPartialSum p.1 (-1)/((p.2)! : ℂ) = 1 := by
  induction j with
  | zero => simp [expPartialSum]
  | succ j ih =>
    rw [Finset.Nat.sum_antidiagonal_succ]
    have hsplit : ∀ p : ℕ × ℕ, expPartialSum (p.1+1) (-1)/((p.2)! : ℂ) =
        expPartialSum p.1 (-1)/((p.2)! : ℂ) + (-1 : ℂ)^(p.1+1)/(((p.1+1))! * (p.2)!) := by
      intro p
      rw [expPartialSum, Finset.sum_range_succ, ← expPartialSum]
      have h1 : (((p.1+1))! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : ((p.2)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
    simp only [hsplit, Finset.sum_add_distrib, ih]
    have h0 := serRec_sum_antidiagonal_neg_one_pow (n := j+1) (by omega)
    rw [Finset.Nat.sum_antidiagonal_succ] at h0
    simp only [expPartialSum, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, one_div] at h0 ⊢
    simp only [one_mul] at h0
    linear_combination h0

/-- Identity under the stated parameter and domain assumptions: `((Real.sqrt x : ℝ) : ℂ)^s = (x :
ℂ)^(s/2)`. -/
theorem serRec_sqrt_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((Real.sqrt x : ℝ) : ℂ)^s = (x : ℂ)^(s/2) := by
  have h1 : ((Real.sqrt x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hx).ne'
  have h2 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [cpow_def_of_ne_zero h1, cpow_def_of_ne_zero h2, ← ofReal_log (Real.sqrt_nonneg x),
    ← ofReal_log hx.le, Real.log_sqrt hx.le]
  push_cast
  ring_nf

/-- Nonvanishing under the stated hypotheses: `a + k ≠ 0`. -/
theorem scSph_add_ne {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (k : ℕ) : a + k ≠ 0 := fun h =>
  ha k (by linear_combination h)

/-- Euler image of `w ↦ γ*(a, 2w)`. -/

theorem scSph_euler_F {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) :
    Differentiable ℂ (fun w => scIncGamma a (2*w)) ∧ ∀ w,
      w * deriv (fun w => scIncGamma a (2*w)) w + a * scIncGamma a (2*w) =
        exp (-(2*w)) / Gamma a := by
  set h : ℕ → ℂ → ℂ := fun k w => (2*w)^k * (Gamma (a+k+1))⁻¹ with hh
  have hne : ∀ k : ℕ, a + k + 1 ≠ 0 := fun k e => ha (k+1) (by push_cast; linear_combination e)
  have hf : ∀ k w, HasDerivAt (h k) ((k:ℂ) * (2*w)^(k-1) * 2 * (Gamma (a+k+1))⁻¹) w := by
    intro k w
    have := (((hasDerivAt_id w).const_mul 2).pow k).mul_const (Gamma (a+k+1))⁻¹
    refine this.congr_deriv ?_
    simp
  have hb : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n w, ‖w‖ < R → ‖h n w‖ ≤ u n := by
    intro R
    refine ⟨fun k => (2*|R|)^k * ‖(Gamma (a+k+1))⁻¹‖, ?_, fun k w hw => ?_⟩
    · refine summable_of_ratio_norm_eventually_le (r := 1/2) (by norm_num) ?_
      have hev := sphSeries_eventually_norm_add_le (16*|R|) (a+1)
      filter_upwards [hev] with k hk
      have hG : Gamma (a+((k+1:ℕ):ℂ)+1) = (a+k+1) * Gamma (a+k+1) := by
        rw [show a+((k+1:ℕ):ℂ)+1 = (a+k+1)+1 by push_cast; ring, Gamma_add_one _ (hne k)]
      rw [hG]
      have hq : 0 < ‖a + k + 1‖ := norm_pos_iff.mpr (hne k)
      have hk' : 16*|R| ≤ 2*‖a+k+1‖ := by
        have : ‖((16*|R| : ℝ) : ℂ) + k‖ = 16*|R| + k := by
          rw [show ((16*|R| : ℝ) : ℂ) + k = ((16*|R| + k : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have h2 : ‖(16*|R| : ℂ) + k‖ ≤ 2 * ‖a + 1 + k‖ := by
          simpa using hk
        rw [show (16*|R| : ℂ) = ((16*|R| : ℝ) : ℂ) by push_cast; ring, this,
          show a + 1 + (k:ℂ) = a + k + 1 by ring] at h2
        linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
      simp only [norm_mul, norm_inv, norm_norm, norm_pow, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2*|R|)]
      rw [pow_succ]
      have hG0 : 0 ≤ ‖Gamma (a+k+1)‖⁻¹ := by positivity
      calc (2*|R|)^k * (2*|R|) * (‖a+k+1‖ * ‖Gamma (a+k+1)‖)⁻¹
          = (2*|R|)^k * ‖Gamma (a+k+1)‖⁻¹ * ((2*|R|)/‖a+k+1‖) := by
            rw [mul_inv]; field_simp
        _ ≤ (2*|R|)^k * ‖Gamma (a+k+1)‖⁻¹ * (1/2) := by
            have : (2*|R|)/‖a+k+1‖ ≤ 1/2 := by rw [div_le_iff₀ hq]; linarith
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ = 1/2 * ((2*|R|)^k * ‖Gamma (a+k+1)‖⁻¹) := by ring
    · have hw' : ‖w‖ ≤ |R| := hw.le.trans (le_abs_self R)
      simp only [hh, norm_mul, norm_pow, norm_inv]
      gcongr
      simp
  obtain ⟨hD, hS⟩ := sphSeries_euler_hasSum a hf hb
  have hH : ∀ w, scIncGamma a (2*w) = exp (-(2*w)) * ∑' k, h k w := by
    intro w
    rw [← tsum_mul_left]
    refine (scIncGamma_hasSum_exponential a (2*w)).tsum_eq.symm.trans ?_
    exact tsum_congr fun k => by simp only [hh]; ring
  have hEu : ∀ w, w * deriv (fun w => ∑' k, h k w) w + a * ∑' k, h k w =
      1 / Gamma a + 2*w * ∑' k, h k w := by
    intro w
    refine (hS w).unique ?_
    have hs : HasSum (fun k => h k w) (∑' k, h k w) := by
      obtain ⟨u, hu, hle⟩ := hb (‖w‖+1)
      exact (Summable.of_norm_bounded hu (fun n => hle n w (by linarith))).hasSum
    have key : HasSum (fun k : ℕ => (2*w)^k * (Gamma (a+k))⁻¹) (1/Gamma a + 2*w*∑' k, h k w) := by
      refine (hasSum_nat_add_iff' 1).mp ?_
      simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, add_zero, one_mul]
      convert hs.mul_left (2*w) using 1
      · funext k; simp only [hh]; push_cast
        rw [pow_succ, show a + ((k:ℂ)+1) = a+k+1 by ring]; ring
      · rw [one_div]; ring
    refine key.congr_fun fun k => ?_
    simp only [hh]
    have hak := scSph_add_ne ha k
    rw [Gamma_add_one _ hak, mul_inv]
    rcases k with _ | k
    · simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, pow_zero, one_mul, add_zero] at hak ⊢
      field_simp
    · rw [show (k+1) - 1 = k by omega, pow_succ]
      have hG : Gamma (a + ((k+1:ℕ):ℂ)) ≠ 0 := Gamma_ne_zero (fun m e => ha (m+(k+1))
        (by push_cast at e ⊢; linear_combination e))
      field_simp
      push_cast
      ring
  have hFd : ∀ w, HasDerivAt (fun w => scIncGamma a (2*w))
      (exp (-(2*w)) * (-2) * ∑' k, h k w + exp (-(2*w)) * deriv (fun w => ∑' k, h k w) w) w := by
    intro w
    have he : HasDerivAt (fun w : ℂ => exp (-(2*w))) (exp (-(2*w)) * (-2)) w := by
      have := (((hasDerivAt_id w).const_mul 2).neg).cexp
      exact this.congr_deriv (by simp)
    have := he.mul (hD w).hasDerivAt
    rw [show (fun w => scIncGamma a (2*w)) = fun w => exp (-(2*w)) * ∑' k, h k w from funext hH]
    exact this
  refine ⟨fun w => (hFd w).differentiableAt, fun w => ?_⟩
  rw [(hFd w).deriv, hH w]
  linear_combination (exp (-(2*w))) * hEu w

/-- The series with terms `(fun n : ℕ => exp (-w) * (poch (1-a) n/Gamma (n+a+1)*(2*n+1) *
sphericalI n w))` converges to `(scIncGamma a (2*w))`. -/
theorem scSph_generic {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (w : ℂ) :
    HasSum (fun n : ℕ => exp (-w) * (poch (1-a) n/Gamma (n+a+1)*(2*n+1) * sphericalI n w))
      (scIncGamma a (2*w)) := by
  have hΓ : ∀ k : ℕ, Gamma (k+a) ≠ 0 := fun k => Gamma_ne_zero (fun m e => ha (m+k)
    (by push_cast; linear_combination e))
  have hΓ1 : ∀ k : ℕ, Gamma (k+a+1) = (k+a) * Gamma (k+a) := fun k =>
    Gamma_add_one _ (by rw [add_comm]; exact scSph_add_ne ha k)
  have hka : ∀ k : ℕ, (k+a : ℂ) ≠ 0 := fun k => by rw [add_comm]; exact scSph_add_ne ha k
  set c : ℕ → ℂ := fun n => poch (1-a) n/Gamma (n+a+1) with hc
  set e : ℕ → ℂ := fun n => poch (1-a) n/Gamma (n+a) with he
  have hce : ∀ n : ℕ, e n = (n+a) * c n := by
    intro n; simp only [hc, he, hΓ1]; field_simp [hΓ n, hka n]
  have hec : ∀ n : ℕ, e (n+1) = (1-a+n) * c n := by
    intro n; simp only [hc, he, poch_succ]
    rw [show ((n+1:ℕ):ℂ)+a = n+a+1 by push_cast; ring]; ring
  have hcc : ∀ n : ℕ, c (n+1) * (n+1+a) = (1-a+n) * c n := by
    intro n; rw [← hec n, hce (n+1)]; push_cast; ring
  clear_value c e
  set C : ℕ → ℂ := fun n => c n * (2*n+1) with hC
  have hdi : ∀ n w, HasDerivAt (sphericalI n) (deriv (sphericalI n) w) w := by
    intro n w
    rcases n with _ | n
    · exact (sphSeries_hasDerivAt_sphericalI_zero w).differentiableAt.hasDerivAt
    · exact (sphSeries_hasDerivAt_sphericalI_succ n w).differentiableAt.hasDerivAt
  have hexp : ∀ w : ℂ, HasDerivAt (fun w : ℂ => exp (-w)) (exp (-w) * (-1)) w := fun w => by
    have := (hasDerivAt_id w).neg.cexp
    exact this.congr_deriv (by simp)
  set f' : ℕ → ℂ → ℂ := fun n w => exp (-w) * (-1) * (C n * sphericalI n w) +
    exp (-w) * (C n * deriv (sphericalI n) w) with hf'
  have hf : ∀ n w, HasDerivAt (fun w => exp (-w) * (C n * sphericalI n w)) (f' n w) w :=
    fun n w => (hexp w).mul ((hdi n w).const_mul (C n))
  set g : ℕ → ℂ → ℂ := fun n w => if n = 0 then exp (-(2*w)) / Gamma a else
    exp (-w) * (w * (e n * (sphericalI (n-1) w - sphericalI n w))) with hg
  have hL : ∀ n w, w * f' n w + a * (exp (-w) * (C n * sphericalI n w)) = g n w - g (n+1) w := by
    intro n w
    simp only [hf', hg, hC]
    rcases n with _ | n
    · rw [(sphSeries_hasDerivAt_sphericalI_zero w).deriv]
      simp only [ite_true, one_ne_zero, ite_false, show (0+1-1 : ℕ) = 0 by rfl, Nat.cast_zero,
        mul_zero, zero_add]
      have h1 := hec 0
      have hc0 : c 0 * a = 1 / Gamma a := by
        have := hce 0; simp only [Nat.cast_zero, zero_add] at this
        rw [mul_comm, ← this]; simp [he, poch_zero]
      have hE : exp (-(2*w)) = exp (-w) * (cosh w - sinh w) := by
        rw [cosh_sub_sinh, ← Complex.exp_add]; ring_nf
      rw [hE, ← sphSeries_mul_sphericalI_zero, ← sphSeries_sphericalI_zero_add]
      simp only [Nat.cast_zero, add_zero] at h1
      rw [h1, div_eq_mul_inv, ← one_div, ← hc0]
      ring
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
        show n+1-1 = n by omega, show n+1+1-1 = n+1 by omega]
      have hd := (sphSeries_hasDerivAt_sphericalI_succ n w).deriv
      have h3 : (2*(n:ℂ)+3) ≠ 0 := by
        have : (0:ℝ) < 2*n+3 := by positivity
        exact_mod_cast this.ne'
      have hd' : (2*(n:ℂ)+3) * deriv (sphericalI (n+1)) w =
          (n+1) * sphericalI n w + (n+2) * sphericalI (n+2) w := by
        rw [hd]; field_simp
      have hr := sphSeries_sphericalI_recurrence n w
      have he1 := hce (n+1)
      have he2 := hec (n+1)
      push_cast at he1 he2 ⊢
      linear_combination (w * exp (-w) * c (n+1)) * hd' + (-(exp (-w) * c (n+1) * a)) * hr
        + (-(exp (-w) * w * (sphericalI n w - sphericalI (n+1) w))) * he1
        + (exp (-w) * w * (sphericalI (n+1) w - sphericalI (n+2) w)) * he2
  have hratio_e : ∀ᶠ k in atTop, ‖e (k+1+1)‖ ≤ 2 * ‖e (k+1)‖ := by
    filter_upwards [sphSeries_eventually_norm_add_le (1-a+1) (a+1)] with k hk
    rw [hec (k+1), hce (k+1), norm_mul, norm_mul]
    have h' : ‖1 - a + ((k+1:ℕ):ℂ)‖ ≤ 2*‖((k+1:ℕ):ℂ)+a‖ := by
      push_cast
      rw [show (1-a+((k:ℂ)+1)) = 1-a+1+k by ring, show ((k:ℂ)+1+a) = a+1+k by ring]; exact hk
    have := mul_le_mul_of_nonneg_right h' (norm_nonneg (c (k+1)))
    linarith
  have hgt : ∀ w, Tendsto (fun n => g n w) atTop (𝓝 0) := by
    intro w
    rw [← tendsto_add_atTop_iff_nat 1]
    have t0 := sphSeries_tendsto_coeff_mul_sphericalI (fun k => e (k+1)) hratio_e 0 w
    have t1 := sphSeries_tendsto_coeff_mul_sphericalI (fun k => e (k+1)) hratio_e 1 w
    have := (t0.sub t1).const_mul (exp (-w) * w)
    rw [sub_zero, mul_zero] at this
    refine this.congr fun k => ?_
    simp only [hg, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, show k+1-1 = k by omega,
      add_zero]
    ring
  have hratio_C : ∀ᶠ k in atTop, ‖C (k+1)‖ ≤ 6 * ‖C k‖ := by
    filter_upwards [sphSeries_eventually_norm_add_le (1-a) (a+1)] with k hk
    have hq : 0 < ‖(k:ℂ)+1+a‖ := norm_pos_iff.mpr (by
      have := hka (k+1); push_cast at this; exact this)
    have h1 : ‖c (k+1)‖ ≤ 2 * ‖c k‖ := by
      have e1 := congrArg norm (hcc k)
      rw [norm_mul, norm_mul] at e1
      have h' : ‖1 - a + (k:ℂ)‖ ≤ 2*‖(k:ℂ)+1+a‖ := by
        rw [show ((k:ℂ)+1+a) = a+1+k by ring]; exact hk
      have := mul_le_mul_of_nonneg_right h' (norm_nonneg (c k))
      nlinarith [norm_nonneg (c (k+1))]
    have h2 : ‖(2*((k+1:ℕ):ℂ)+1)‖ ≤ 3 * ‖(2*(k:ℂ)+1)‖ := by
      rw [show (2*((k+1:ℕ):ℂ)+1) = ((2*k+3 : ℝ) : ℂ) by push_cast; ring,
        show (2*(k:ℂ)+1) = ((2*k+1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
      linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    simp only [hC, norm_mul]
    calc ‖c (k+1)‖ * ‖(2*((k+1:ℕ):ℂ)+1)‖ ≤ (2 * ‖c k‖) * (3 * ‖(2*(k:ℂ)+1)‖) := by gcongr
      _ = 6 * (‖c k‖ * ‖(2*(k:ℂ)+1)‖) := by ring
  have hb : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n w, ‖w‖ < R →
      ‖exp (-w) * (C n * sphericalI n w)‖ ≤ u n := by
    intro R
    obtain ⟨u, hu, hle⟩ := sphSeries_bound_coeff_mul_sphericalI C hratio_C 0 R
    refine ⟨fun k => Real.exp |R| * u k, hu.mul_left _, fun k w hw => ?_⟩
    rw [norm_mul]
    have hw' : ‖w‖ ≤ |R| := hw.le.trans (le_abs_self R)
    have h1 : ‖exp (-w)‖ ≤ Real.exp |R| := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ((Complex.re_le_norm (-w)).trans ?_)
      rw [norm_neg]; exact hw'
    have h2 : ‖C k * sphericalI k w‖ ≤ u k := by simpa using hle k w hw
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨hFd, hFL⟩ := scSph_euler_F ha
  have key := sphSeries_hasSum_of_euler (f := fun n w => exp (-w) * (C n * sphericalI n w))
    (f' := f') (g := g) (F := fun w => scIncGamma a (2*w)) a hf hL hgt hb hFd
    (fun w => by rw [hFL w]; simp [hg])
    (fun m hm => absurd (by linear_combination hm : a = -m) (ha m)) w
  refine key.congr_fun fun n => ?_
  simp only [hC, hc]

/-- The coefficient recursion `c_{n+1}(n+1+a) = (1-a+n) c_n` holds for every `a`,
the poles of `Γ` included. -/

theorem scSph_coeff_succ (a : ℂ) (n : ℕ) :
    poch (1-a) (n+1)/Gamma ((n+1:ℕ)+a+1) * (n+1+a) = (1-a+n) * (poch (1-a) n/Gamma (n+a+1)) := by
  rw [poch_succ, show ((n+1:ℕ):ℂ)+a+1 = (n+a+1)+1 by push_cast; ring]
  by_cases h0 : (n:ℂ)+a+1 = 0
  · rw [h0, zero_add, Gamma_zero]
    rw [show (n:ℂ)+1+a = 0 by linear_combination h0]
    simp
  · rw [Gamma_add_one _ h0, show (n:ℂ)+1+a = n+a+1 by ring]
    by_cases hG : Gamma ((n:ℂ)+a+1) = 0
    · simp [hG]
    · field_simp

/-- Locally uniform geometric bound for the coefficients `(1-a)_n/Γ(n+a+1)`. -/

theorem scSph_coeff_bound (a₀ : ℂ) : ∃ K : ℝ, ∀ n : ℕ, ∀ a ∈ Metric.closedBall a₀ (1/2),
    ‖poch (1-a) n/Gamma (n+a+1)‖ ≤ K * 2^n := by
  set s := Metric.closedBall a₀ (1/2) with hs
  set A : ℝ := ‖a₀‖ + 1/2 with hA
  have hAa : ∀ a ∈ s, ‖a‖ ≤ A := fun a ha => by
    have := norm_le_norm_add_norm_sub' a a₀
    rw [Metric.mem_closedBall, dist_eq_norm] at ha
    linarith
  have hcont : ∀ n : ℕ, ContinuousOn (fun a : ℂ => poch (1-a) n/Gamma (n+a+1)) s := by
    intro n
    simp only [div_eq_mul_inv]
    refine (Continuous.continuousOn ?_)
    exact ((ascPochhammer ℂ n).continuous.comp (continuous_const.sub continuous_id)).mul
      (differentiable_one_div_Gamma.continuous.comp (by fun_prop))
  have hcpt : IsCompact s := isCompact_closedBall a₀ (1/2)
  choose Kf hKf using fun n => (hcpt.exists_bound_of_continuousOn (hcont n))
  set N₀ : ℕ := ⌈3*A⌉₊ with hN₀
  set K : ℝ := ∑ n ∈ Finset.range (N₀+1), max (Kf n) 0 with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun n _ => le_max_right _ _
  have hle : ∀ n ≤ N₀, ∀ a ∈ s, ‖poch (1-a) n/Gamma (n+a+1)‖ ≤ K := by
    intro n hn a ha
    refine (hKf n a ha).trans ((le_max_left (Kf n) 0).trans ?_)
    exact Finset.single_le_sum (f := fun n => max (Kf n) 0) (fun n _ => le_max_right _ _)
      (Finset.mem_range.mpr (by omega))
  refine ⟨K, fun n a ha => ?_⟩
  induction n with
  | zero => exact (hle 0 (Nat.zero_le _) a ha).trans (by simp)
  | succ n ih =>
    rcases le_or_gt (n+1) N₀ with hn | hn
    · exact (hle (n+1) hn a ha).trans (le_mul_of_one_le_right hK0 (one_le_pow₀ (by norm_num)))
    · have hN : 3*A ≤ n := by
        have := Nat.le_ceil (3*A); rw [← hN₀] at this
        have : (N₀:ℝ) ≤ n := by exact_mod_cast (by omega : N₀ ≤ n)
        linarith
      have ha' := hAa a ha
      have hA0 : 0 ≤ A := by positivity
      have hlow : (n:ℝ) + 1 - A ≤ ‖(n:ℂ)+1+a‖ := by
        have := norm_sub_norm_le (((n:ℂ)+1)) (-a)
        rw [sub_neg_eq_add, norm_neg, show ((n:ℂ)+1) = (((n+1:ℕ):ℝ):ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)] at this
        push_cast at this; linarith
      have hup : ‖1-a+(n:ℂ)‖ ≤ n + 1 + A := by
        refine (norm_add_le _ _).trans ?_
        have := norm_sub_le (1:ℂ) a
        simp only [norm_one, Complex.norm_natCast] at this ⊢; linarith
      have hpos : 0 < (n:ℝ) + 1 - A := by linarith
      have e := congrArg norm (scSph_coeff_succ a n)
      rw [norm_mul, norm_mul] at e
      have h2 : ‖poch (1-a) (n+1)/Gamma ((n+1:ℕ)+a+1)‖ * ((n:ℝ)+1-A) ≤
          2 * ((n:ℝ)+1-A) * ‖poch (1-a) n/Gamma (n+a+1)‖ := by
        calc ‖poch (1-a) (n+1)/Gamma ((n+1:ℕ)+a+1)‖ * ((n:ℝ)+1-A)
            ≤ ‖poch (1-a) (n+1)/Gamma ((n+1:ℕ)+a+1)‖ * ‖(n:ℂ)+1+a‖ := by gcongr
          _ = ‖1-a+(n:ℂ)‖ * ‖poch (1-a) n/Gamma (n+a+1)‖ := e
          _ ≤ (n+1+A) * ‖poch (1-a) n/Gamma (n+a+1)‖ := by gcongr
          _ ≤ 2 * ((n:ℝ)+1-A) * ‖poch (1-a) n/Gamma (n+a+1)‖ := by gcongr; linarith
      have h3 : ‖poch (1-a) (n+1)/Gamma ((n+1:ℕ)+a+1)‖ ≤ 2 * ‖poch (1-a) n/Gamma (n+a+1)‖ := by
        nlinarith [norm_nonneg (poch (1-a) n/Gamma (n+a+1))]
      rw [pow_succ]
      nlinarith [ih]

/-- DLMF 8.7.5 for every `a`: the generic case by the Euler operator, the poles of `Γ(a)`
by continuity in `a`. -/
theorem scSph_series (a z : ℂ) :
    HasSum (fun n : ℕ => exp (-z/2)*poch (1-a) n/Gamma (n+a+1)*(2*n+1)*sphericalI n (z/2)) (scIncGamma a z) := by
  have hgen : ∀ a : ℂ, (∀ n : ℕ, a ≠ -n) → HasSum (fun n : ℕ => exp (-z/2)*poch (1-a) n/Gamma (n+a+1)*(2*n+1)*sphericalI n (z/2)) (scIncGamma a z) := by
    intro a ha
    have h := scSph_generic ha (z/2)
    rw [show 2*(z/2) = z by ring] at h
    refine h.congr_fun fun n => ?_
    rw [neg_div]; ring
  by_cases ha : ∀ n : ℕ, a ≠ -n
  · exact hgen a ha
  simp only [not_forall, not_not] at ha
  obtain ⟨m, rfl⟩ := ha
  set a₀ : ℂ := -(m:ℂ) with ha₀
  set s := Metric.closedBall a₀ (1/2) with hs
  set T : ℂ → ℕ → ℂ := fun a n => exp (-z/2)*poch (1-a) n/Gamma (n+a+1)*(2*n+1)*sphericalI n (z/2)
    with hT
  obtain ⟨K, hK⟩ := scSph_coeff_bound a₀
  have hr6 : ∀ᶠ k in atTop, ‖((2:ℂ)^(k+1)*(2*((k+1:ℕ):ℂ)+1))‖ ≤ 6 * ‖((2:ℂ)^k*(2*(k:ℂ)+1))‖ := by
    refine Eventually.of_forall fun k => ?_
    rw [show ((2:ℂ)^(k+1)*(2*((k+1:ℕ):ℂ)+1)) = (((2:ℝ)^(k+1)*(2*k+3) : ℝ) : ℂ) by push_cast; ring,
      show ((2:ℂ)^k*(2*(k:ℂ)+1)) = (((2:ℝ)^k*(2*k+1) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity), pow_succ]
    nlinarith [pow_pos (two_pos : (0:ℝ) < 2) k, (k.cast_nonneg : (0:ℝ) ≤ k)]
  obtain ⟨u, hu, hle⟩ := sphSeries_bound_coeff_mul_sphericalI (fun k => (2:ℂ)^k*(2*(k:ℂ)+1)) hr6 0
    (‖z/2‖+1)
  have hbound : ∀ n, ∀ a ∈ s, ‖T a n‖ ≤ ‖exp (-z/2)‖ * K * u n := by
    intro n a ha
    have h1 := hK n a ha
    have h2 : ‖(2:ℂ)^n*(2*(n:ℂ)+1) * sphericalI n (z/2)‖ ≤ u n := by
      simpa using hle n (z/2) (by linarith)
    have hK0 : 0 ≤ K := by
      have := (norm_nonneg _).trans (hK 0 a ha); simpa using this
    simp only [hT]
    rw [show exp (-z/2)*poch (1-a) n/Gamma (n+a+1)*(2*n+1)*sphericalI n (z/2) =
      exp (-z/2) * (poch (1-a) n/Gamma (n+a+1)) * ((2*n+1)*sphericalI n (z/2)) by ring,
      norm_mul, norm_mul]
    have h3 : ‖((2:ℂ)*n+1)*sphericalI n (z/2)‖ * 2^n ≤ u n := by
      have h22 : ‖(2:ℂ)‖ = 2 := by simp
      rw [norm_mul, norm_mul, norm_pow, h22] at h2
      rw [norm_mul]; linarith
    calc ‖exp (-z/2)‖ * ‖poch (1-a) n/Gamma (n+a+1)‖ * ‖((2:ℂ)*n+1)*sphericalI n (z/2)‖
        ≤ ‖exp (-z/2)‖ * (K * 2^n) * ‖((2:ℂ)*n+1)*sphericalI n (z/2)‖ := by gcongr
      _ = ‖exp (-z/2)‖ * K * (‖((2:ℂ)*n+1)*sphericalI n (z/2)‖ * 2^n) := by ring
      _ ≤ ‖exp (-z/2)‖ * K * u n := by gcongr
  have hsum : Summable fun n => ‖exp (-z/2)‖ * K * u n := hu.mul_left _
  have hTc : ∀ n, ContinuousOn (fun a => T a n) s := by
    intro n
    have hp : Continuous fun a : ℂ => poch (1-a) n :=
      (ascPochhammer ℂ n).continuous.comp (continuous_const.sub continuous_id)
    have hg : Continuous fun a : ℂ => (Gamma (n+a+1))⁻¹ :=
      differentiable_one_div_Gamma.continuous.comp (by fun_prop)
    simp only [hT, div_eq_mul_inv]
    exact ((((continuous_const.mul hp).mul hg).mul continuous_const).mul
      continuous_const).continuousOn
  have hΦ : ContinuousOn (fun a => ∑' n, T a n) s := continuousOn_tsum hTc hsum hbound
  have hmem : s ∈ 𝓝 a₀ := Metric.closedBall_mem_nhds a₀ (by norm_num)
  have hΦa : ContinuousAt (fun a => ∑' n, T a n) a₀ := hΦ.continuousAt hmem
  have hSa : ContinuousAt (fun a => scIncGamma a z) a₀ :=
    (scIncGamma_joint_entire.continuous.comp (by fun_prop : Continuous fun a : ℂ => (a, z))).continuousAt
  have heq : ∀ᶠ a in 𝓝[≠] a₀, ∑' n, T a n = scIncGamma a z := by
    have hb : Metric.ball a₀ (1/2) ∈ 𝓝 a₀ := Metric.ball_mem_nhds a₀ (by norm_num)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hb] with a hne hball
    refine (hgen a fun k hk => hne ?_).tsum_eq
    rw [Metric.mem_ball, dist_eq_norm, hk, ha₀] at hball
    have hkm : k = m := by
      by_contra hkm
      have : (1:ℝ) ≤ ‖(-(k:ℂ)) - -(m:ℂ)‖ := by
        rw [show (-(k:ℂ)) - -(m:ℂ) = (((m:ℤ) - k : ℤ) : ℂ) by push_cast; ring, Complex.norm_intCast]
        have : ((m:ℤ) - k) ≠ 0 := by omega
        exact_mod_cast Int.one_le_abs this
      linarith
    rw [hk, hkm, Set.mem_singleton_iff]
  have hlim1 := hΦa.tendsto.mono_left (nhdsWithin_le_nhds (s := {a₀}ᶜ))
  have hlim2 := (hSa.tendsto.mono_left (nhdsWithin_le_nhds (s := {a₀}ᶜ))).congr' (heq.mono fun a h => h.symm)
  have hval : ∑' n, T a₀ n = scIncGamma a₀ z := tendsto_nhds_unique hlim1 hlim2
  have hsT : Summable (fun n => T a₀ n) :=
    Summable.of_norm_bounded hsum (fun n => hbound n a₀ (Metric.mem_closedBall_self (by norm_num)))
  rw [← hval]
  exact hsT.hasSum

/-- The series with terms `(fun n : ℕ => Gamma a*(x : ℂ)^(a/2)*exp (-x : ℂ)*expPartialSum n
(-1)*(x : ℂ)^((n : ℂ)/2)*DLMF.Bessel.besselI (n+a) (2*Real.sqrt x))` converges to
`(lowerIncGamma a x)`. -/
@[dlmf 8.7.E4]
theorem lowerIncGamma_besselI_series {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => Gamma a*(x : ℂ)^(a/2)*exp (-x : ℂ)*expPartialSum n (-1)*(x : ℂ)^((n : ℂ)/2)*DLMF.Bessel.besselI (n+a) (2*Real.sqrt x)) (lowerIncGamma a x) := by
  set r : ℂ := ((Real.sqrt x : ℝ) : ℂ) with hr
  have hr0 : r ≠ 0 := by simp only [hr]; exact_mod_cast (Real.sqrt_pos.mpr hx).ne'
  have hz : (2*r) ≠ 0 := mul_ne_zero two_ne_zero hr0
  have hz2 : 2*r/2 = r := by field_simp
  have hnr : ‖r‖ = Real.sqrt x := by
    simp only [hr, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x)]
  have hr2 : ∀ k : ℕ, r^(2*k) = (x:ℂ)^k := by
    intro k; rw [pow_mul]; simp only [hr]; rw [← ofReal_pow, Real.sq_sqrt hx.le]
  -- summability of the Neumann coefficients
  set C : ℝ := ∑' i : ℕ, (1:ℝ)^i/(i)! with hC
  have he : ∀ k : ℕ, ‖expPartialSum k (-1)‖ ≤ C := by
    intro k
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ Finset.range (k+1), ‖(-1:ℂ)^i/(i.factorial : ℂ)‖ = (1:ℝ)^i/(i)! := by
      intro i _; simp
    rw [Finset.sum_congr rfl this]
    exact Summable.sum_le_tsum _ (fun i _ => by positivity) (Real.summable_pow_div_factorial 1)
  have hsum : Summable fun k : ℕ => ‖expPartialSum k (-1)‖ * ‖2*r/2‖^(2*k) * (2^k/(k)!) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((Real.summable_pow_div_factorial (2*x)).mul_left C)
    rw [hz2, hnr, pow_mul, Real.sq_sqrt hx.le, mul_pow]
    have := he k
    calc ‖expPartialSum k (-1)‖ * x^k * (2^k/(k)!) ≤ C * x^k * (2^k/(k)!) := by gcongr
      _ = C * (2^k*x^k/(k)!) := by ring
  have hN := DLMF.Bessel.hasSum_besselI_neumann hz a (fun k => expPartialSum k (-1))
    (fun k => k) (fun k => k) (fun k => by ring) hsum
  rw [hz2] at hN
  have hcoef : ∀ j : ℕ, DLMF.Bessel.neumannCoeff a 1 (fun k => expPartialSum k (-1)) (fun k => k) j
      = 1/Gamma (a+j+1) := by
    intro j
    simp only [DLMF.Bessel.neumannCoeff, one_pow, mul_one, DLMF.Bessel.regularizedHGFunCoeff_empty]
    have : ∀ p ∈ Finset.antidiagonal j, expPartialSum p.1 (-1) * (1/((p.2)! * Gamma (a + p.1 + 1 + p.2)))
        = (1/Gamma (a+j+1)) * (expPartialSum p.1 (-1)/((p.2)! : ℂ)) := by
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      rw [show a + (p.1:ℂ) + 1 + p.2 = a + j + 1 by rw [← hp]; push_cast; ring]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, serRec_sum_antidiagonal_expPartialSum, mul_one]
  have hS := scIncGamma_eq_tsum a x
  have hlow : lowerIncGamma a x = Gamma a * (x:ℂ)^a * scIncGamma a x := by
    have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [scIncGamma_eq ha hx0]
    have hΓ := Gamma_ne_zero ha
    have : (x:ℂ)^a * (x:ℂ)^(-a) = 1 := by
      rw [cpow_neg, mul_inv_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hx0))]
    field_simp
    linear_combination (-lowerIncGamma a x) * this
  have hval : lowerIncGamma a x = Gamma a*(x : ℂ)^(a/2)*exp (-x : ℂ) *
      (r^a * ∑' j, DLMF.Bessel.neumannCoeff a 1 (fun k => expPartialSum k (-1)) (fun k => k) j * r^(2*j)) := by
    rw [hlow, hS]
    simp only [hcoef, hr2]
    have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have : r^a * (x:ℂ)^(a/2) = (x:ℂ)^a := by
      rw [hr, serRec_sqrt_cpow hx, ← cpow_add _ _ hx0]; ring_nf
    rw [show Gamma a*(x : ℂ)^(a/2)*exp (-x : ℂ) * (r^a * ∑' j : ℕ, 1/Gamma (a+j+1) * (x:ℂ)^j) =
      Gamma a * (r^a * (x:ℂ)^(a/2)) * (exp (-x : ℂ) * ∑' j : ℕ, 1/Gamma (a+j+1) * (x:ℂ)^j) by ring,
      this]
    congr 2
    exact tsum_congr fun j => by ring
  rw [hval]
  refine (hN.mul_left _).congr_fun fun n => ?_
  have hxn : (x : ℂ)^((n : ℂ)/2) = r^n := by
    rw [hr, ← cpow_natCast, serRec_sqrt_cpow hx]
  rw [hxn, show ((n:ℂ) + a) = a + (n:ℕ) by ring]
  ring

/-- The series with terms `(fun n : ℕ => exp (-z/2)*poch (1-a) n/Gamma (n+a+1)*(2*n+1)*sphericalI
n (z/2))` converges to `(scIncGamma a z)`. -/
@[dlmf 8.7.E5]
theorem scIncGamma_sphericalI_series (a z : ℂ) :
    HasSum (fun n : ℕ => exp (-z/2)*poch (1-a) n/Gamma (n+a+1)*(2*n+1)*sphericalI n (z/2)) (scIncGamma a z) := by
  exact scSph_series a z

/-- The series with terms `(fun n : ℕ => (x : ℂ)^a*exp (-x :
ℂ)*DLMF.OrthogonalPolynomials.laguerrePolyL a n x/(n+1))` converges to `(upperIncGamma a x)`. -/
@[dlmf 8.7.E6]
theorem upperIncGamma_laguerre_series {a : ℂ} (ha : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (x : ℂ)^a*exp (-x : ℂ)*DLMF.OrthogonalPolynomials.laguerrePolyL a n x/(n+1)) (upperIncGamma a x) := by
  sorry

/-- Formula under the stated hypotheses: `∀ f ∈ ({lowerIncGamma,upperIncGamma} : Set (ℂ → ℂ → ℂ)),
f (a+2) z-(a+1+z)*f (a+1) z+a*z*f a z=0`. -/
@[dlmf 8.8.E3]
theorem incompleteGamma_threeTerm {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    ∀ f ∈ ({lowerIncGamma,upperIncGamma} : Set (ℂ → ℂ → ℂ)), f (a+2) z-(a+1+z)*f (a+1) z+a*z*f a z=0 := by
  intro f hf
  rcases hf with rfl | rfl
  · have h0 := lowerIncGamma_add_one ha hz
    have h1 := lowerIncGamma_add_one (add_one_ne_neg_nat ha) hz
    rw [show a+1+1=a+2 by ring, cpow_add _ _ hz, cpow_one] at h1
    linear_combination h1 - z*h0
  · have h0 := upperIncGamma_add_one a hz
    have h1 := upperIncGamma_add_one (a+1) hz
    rw [show a+1+1=a+2 by ring, cpow_add _ _ hz, cpow_one] at h1
    linear_combination h1 - z*h0

/-- Formula under the stated hypotheses: `lowerIncGamma (a+n) z=poch a n*lowerIncGamma a z -
z^a*exp (-z)*(∑ k ∈ Finset.range n, Gamma (a+n)/Gamma (a+k+1)*z^k)`. -/
@[dlmf 8.8.E7]
theorem lowerIncGamma_shift_up (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma (a+n) z=poch a n*lowerIncGamma a z - z^a*exp (-z)*(∑ k ∈ Finset.range n, Gamma (a+n)/Gamma (a+k+1)*z^k) := by
  have han := not_neg_nat_add_nat ha n
  have hGa := Gamma_ne_zero ha
  have hGan := Gamma_ne_zero han
  have hs := normIncGammaPContinued_shift_up n a hz
  rw [normIncGammaPContinued_eq han, normIncGammaPContinued_eq ha,
    normIncGammaP, normIncGammaP] at hs
  have hg := Gamma_add_nat_div_Gamma_eq (n := n) a ha
  rw [← poch] at hg
  rw [← hg]
  have hsum : ∑ k ∈ Finset.range n, Gamma (a+n)/Gamma (a+k+1)*z^k =
      Gamma (a+n)*∑ k ∈ Finset.range n, z^k/Gamma (a+k+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum]
  calc
    lowerIncGamma (a+n) z = Gamma (a+n)*(lowerIncGamma a z/Gamma a-
        z^a*exp (-z)*∑ k ∈ Finset.range n, z^k/Gamma (a+k+1)) := by
      rw [← hs]
      field_simp
    _ = _ := by ring

/-- Reversing the finite upward-shift correction gives the downward-shift indexing. -/
theorem incompleteGamma_shift_sum_reverse (n : ℕ) (a : ℂ) {z : ℂ} (hz : z≠0) :
    z^(a-n)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-n+k+1)*z^k)=
      z^(a-1)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-k)*z^(-(k:ℤ))) := by
  rw [Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_range_reflect (fun k => z^(a-n)*(Gamma a/Gamma (a-n+k+1)*z^k)) n]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k<n := Finset.mem_range.mp hk
  have hcast : ((n-1-k:ℕ):ℂ)=(n:ℂ)-1-k := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  rw [show a-n+(n-1-k:ℕ)+1=a-k by rw [hcast]; ring]
  have he : z^(a-n)*z^(n-1-k)=z^(a-1)*z^(-(k:ℤ)) := by
    rw [← cpow_natCast, ← cpow_intCast, ← cpow_add _ _ hz, ← cpow_add _ _ hz, hcast]
    congr 1
    push_cast
    ring
  linear_combination (Gamma a/Gamma (a-k))*he

/-- Formula under the stated hypotheses: `lowerIncGamma a z=Gamma a/Gamma (a-n)*lowerIncGamma
(a-n) z - z^(a-1)*exp (-z)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-k)*z^(-(k : ℤ)))`. -/
@[dlmf 8.8.E8]
theorem lowerIncGamma_shift_down (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma a z=Gamma a/Gamma (a-n)*lowerIncGamma (a-n) z - z^(a-1)*exp (-z)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-k)*z^(-(k : ℤ))) := by
  have hs := lowerIncGamma_shift_up n ha hz
  have hg := Gamma_add_nat_div_Gamma_eq (n:=n) (a-n) ha
  rw [show a-(n:ℂ)+n=a by ring] at hs hg
  rw [← poch] at hg
  rw [← hg] at hs
  have he := incompleteGamma_shift_sum_reverse n a hz
  linear_combination hs-exp (-z)*he

/-- Formula under the stated hypotheses: `upperIncGamma (a+n) z=poch a n*upperIncGamma a z +
z^a*exp (-z)*(∑ k ∈ Finset.range n, Gamma (a+n)/Gamma (a+k+1)*z^k)`. -/
@[dlmf 8.8.E9]
theorem upperIncGamma_shift_up (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma (a+n) z=poch a n*upperIncGamma a z + z^a*exp (-z)*(∑ k ∈ Finset.range n, Gamma (a+n)/Gamma (a+k+1)*z^k) := by
  have h0 := lowerIncGamma_add_upperIncGamma ha hz
  have hn := lowerIncGamma_add_upperIncGamma (not_neg_nat_add_nat ha n) hz
  have hs := lowerIncGamma_shift_up n ha hz
  have hg := Gamma_add_nat_div_Gamma_eq (n := n) a ha
  rw [← poch, div_eq_iff (Gamma_ne_zero ha)] at hg
  linear_combination hn-hs-poch a n*h0+hg

/-- Formula under the stated hypotheses: `upperIncGamma a z=Gamma a/Gamma (a-n)*upperIncGamma
(a-n) z + z^(a-1)*exp (-z)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-k)*z^(-(k : ℤ)))`. -/
@[dlmf 8.8.E10]
theorem upperIncGamma_shift_down (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma a z=Gamma a/Gamma (a-n)*upperIncGamma (a-n) z + z^(a-1)*exp (-z)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-k)*z^(-(k : ℤ))) := by
  have hs := upperIncGamma_shift_up n ha hz
  have hg := Gamma_add_nat_div_Gamma_eq (n:=n) (a-n) ha
  rw [show a-(n:ℂ)+n=a by ring] at hs hg
  rw [← poch] at hg
  rw [← hg] at hs
  have he := incompleteGamma_shift_sum_reverse n a hz
  linear_combination hs+exp (-z)*he

/-- Identity under the stated parameter and domain assumptions: `deriv (fun a => scIncGamma a z) 0
= -genExpIntE 1 z-log z`. -/
@[dlmf 8.8.E14]
theorem scIncGamma_deriv_parameter_zero {z : ℂ} (hz : z ≠ 0) :
    deriv (fun a => scIncGamma a z) 0 = -genExpIntE 1 z-log z := by
  have he : (fun a : ℂ => scIncGamma a z)=
      (fun a => regularizedHGFun {a} {a+1} (-z)) := by
    funext a
    rw [regularizedConfluent_kummer_transform a (a+1) (-z)]
    simp only [show a+1-a=1 by ring, neg_neg, scIncGamma]
  rw [he, (hasDerivAt_regularizedConfluent_Ein z).deriv, expIntE1_eq_Ein_complex hz]
  ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun t =>
t^(-a)*lowerIncGamma a t) z=(-1 : ℂ)^n*z^(-a-n)*lowerIncGamma (a+n) z`. -/
@[dlmf 8.8.E15]
theorem lowerIncGamma_iteratedDeriv_scaled_power (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => t^(-a)*lowerIncGamma a t) z=(-1 : ℂ)^n*z^(-a-n)*lowerIncGamma (a+n) z := by
  have hz0 := slitPlane_ne_zero hz
  have ha0 : a≠0 := by simpa using ha 0
  have ha1 := add_one_ne_neg_nat ha
  have han0 : a+(n:ℂ)≠0 := by intro h; exact ha n (by linear_combination h)
  have he : (fun t => t^(-a)*lowerIncGamma a t)=ᶠ[𝓝 z]
      (fun t => (1/a)*kummerM a (a+1) (-t)) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with t ht
    rw [lowerIncGamma]
    have hp : t^(-a)*t^a=1 := by rw [← cpow_add _ _ (slitPlane_ne_zero ht)]; simp
    linear_combination kummerM a (a+1) (-t)/a*hp
  rw [he.iteratedDeriv_eq n, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_neg, iteratedDeriv_kummerM n ha1, lowerIncGamma]
  simp only [smul_eq_mul]
  rw [show a+1+(n:ℂ)=a+n+1 by ring]
  have hp : z^(-a-n)*z^(a+n)=1 := by rw [← cpow_add _ _ hz0]; ring_nf; simp
  have hpoch : a*poch (a+1) n=(a+n)*poch a n := by
    rw [← poch_succ_left, poch_succ]
    ring
  have hpc := poch_ne_zero_of_not_neg_nat ha1 n
  rw [show (-1:ℂ)^n*z^(-a-n)*(z^(a+n)/(a+n)*kummerM (a+n) (a+n+1) (-z))=
      (-1:ℂ)^n/(a+n)*kummerM (a+n) (a+n+1) (-z) by
    linear_combination (-1:ℂ)^n/(a+n)*kummerM (a+n) (a+n+1) (-z)*hp]
  field_simp [ha0,han0,hpc]
  linear_combination -kummerM (a+n) (a+n+1) (-z)*hpoch

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun t =>
t^(-a)*upperIncGamma a t) z=(-1 : ℂ)^n*z^(-a-n)*upperIncGamma (a+n) z`. -/
@[dlmf 8.8.E16]
theorem upperIncGamma_iteratedDeriv_scaled_power (n : ℕ) {a : ℂ} {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => t^(-a)*upperIncGamma a t) z=(-1 : ℂ)^n*z^(-a-n)*upperIncGamma (a+n) z := by
  have he : (fun t => t^(-a)*upperIncGamma a t)=ᶠ[𝓝 z]
      (fun t => exp (-t)*kummerU 1 (1+a) t) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with t ht
    have ht0 := slitPlane_ne_zero ht
    rw [upperIncGamma_eq_cpow_mul_kummerU _ ht0, add_comm a 1]
    have hp : t^(-a)*t^a=1 := by rw [← cpow_add _ _ ht0]; simp
    linear_combination exp (-t)*kummerU 1 (1+a) t*hp
  rw [he.iteratedDeriv_eq n, iteratedDeriv_exp_neg_kummerU _ _ _ hz,
    upperIncGamma_eq_cpow_mul_kummerU _ (slitPlane_ne_zero hz)]
  have hp : z^(-a-n)*z^(a+n)=1 := by rw [← cpow_add _ _ (slitPlane_ne_zero hz)]; ring_nf; simp
  rw [show a+(n:ℂ)+1=1+a+n by ring]
  linear_combination -(-1:ℂ)^n*exp (-z)*kummerU 1 (1+a+n) z*hp

/-- Exponentially weighted upper-Gamma differentiation holds at every parameter. -/
theorem hasDerivAt_exp_mul_upperIncGamma (a : ℂ) {z : ℂ} (hz : z∈slitPlane) :
    HasDerivAt (fun t => exp t*upperIncGamma a t)
      ((a-1)*exp z*upperIncGamma (a-1) z) z := by
  have hd := (Complex.hasDerivAt_exp z).mul (hasDerivAt_upperIncGamma_complex a hz)
  refine hd.congr_deriv ?_
  have hr := upperIncGamma_add_one (a-1) (slitPlane_ne_zero hz)
  rw [sub_add_cancel] at hr
  have he : exp z*exp (-z)=1 := by rw [← Complex.exp_add]; simp
  linear_combination exp z*hr

/-- Exponentially weighted lower-Gamma differentiation away from the shifted poles. -/
theorem hasDerivAt_exp_mul_lowerIncGamma (a : ℂ)
    (ha : ∀ k : ℕ, a-1≠-k) {z : ℂ} (hz : z∈slitPlane) :
    HasDerivAt (fun t => exp t*lowerIncGamma a t)
      ((a-1)*exp z*lowerIncGamma (a-1) z) z := by
  have ha0 : ∀ k : ℕ, a≠-k := by simpa using add_one_ne_neg_nat ha
  have hd := (Complex.hasDerivAt_exp z).mul (hasDerivAt_incompleteGamma ha0 hz).1
  refine hd.congr_deriv ?_
  have hr := lowerIncGamma_add_one ha (slitPlane_ne_zero hz)
  rw [sub_add_cancel] at hr
  have he : exp z*exp (-z)=1 := by rw [← Complex.exp_add]; simp
  linear_combination exp z*hr

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun t => exp
t*lowerIncGamma a t) z=(-1 : ℂ)^n*poch (1-a) n*exp z*lowerIncGamma (a-n) z`. -/
@[dlmf 8.8.E17]
theorem lowerIncGamma_iteratedDeriv_scaled_exp (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => exp t*lowerIncGamma a t) z=(-1 : ℂ)^n*poch (1-a) n*exp z*lowerIncGamma (a-n) z := by
  induction n generalizing a with
  | zero => simp [poch_zero]
  | succ n ih =>
    have ha1 : ∀ k : ℕ, a-1≠-k := by
      intro k hk
      apply ha (k+n)
      push_cast
      linear_combination hk
    have has : ∀ k : ℕ, (a-1)-n≠-k := by
      intro k hk
      apply ha k
      push_cast
      linear_combination hk
    have he : deriv (fun t => exp t*lowerIncGamma a t)=ᶠ[𝓝 z]
        (fun t => (a-1)*(exp t*lowerIncGamma (a-1) t)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with t ht
      simpa only [mul_assoc] using (hasDerivAt_exp_mul_lowerIncGamma a ha1 ht).deriv
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih has,
      poch_succ_left, pow_succ]
    rw [show (1:ℂ)-(a-1)=1-a+1 by ring,
      show a-1-(n:ℂ)=a-(n+1:ℕ) by push_cast; ring]
    ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun t => exp
t*upperIncGamma a t) z=(-1 : ℂ)^n*poch (1-a) n*exp z*upperIncGamma (a-n) z`. -/
@[dlmf 8.8.E19]
theorem upperIncGamma_iteratedDeriv_scaled_exp (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => exp t*upperIncGamma a t) z=(-1 : ℂ)^n*poch (1-a) n*exp z*upperIncGamma (a-n) z := by
  induction n generalizing a with
  | zero => simp [poch_zero]
  | succ n ih =>
    have ha1 : ∀ k : ℕ, a-1≠-k := by
      intro k hk
      apply ha (k+n)
      push_cast
      linear_combination hk
    have has : ∀ k : ℕ, (a-1)-n≠-k := by
      intro k hk
      apply ha k
      push_cast
      linear_combination hk
    have he : deriv (fun t => exp t*upperIncGamma a t)=ᶠ[𝓝 z]
        (fun t => (a-1)*(exp t*upperIncGamma (a-1) t)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with t ht
      simpa only [mul_assoc] using (hasDerivAt_exp_mul_upperIncGamma a ht).deriv
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih has,
      poch_succ_left, pow_succ]
    rw [show (1:ℂ)-(a-1)=1-a+1 by ring,
      show a-1-(n:ℂ)=a-(n+1:ℕ) by push_cast; ring]
    ring

/-- A weighted regularized Kummer derivative, valid at every denominator parameter. -/
theorem hasDerivAt_cpow_mul_regularized_one (a : ℂ) {z : ℂ} (hz : z∈slitPlane) :
    HasDerivAt (fun t => t^a*regularizedHGFun {1} {a+1} t)
      (z^(a-1)*regularizedHGFun {1} {a} z) z := by
  have hm := (differentiableAt_regularizedConfluent 1 (a+1) z).hasDerivAt
  rw [deriv_regularizedConfluent] at hm
  have hd := ((hasDerivAt_id z).cpow_const (c:=a) hz).mul hm
  refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun t => rfl)).congr_deriv ?_
  have hc := regularizedConfluent_contiguous_mixed_b_pred 1 (a+1) z
  simp only [add_sub_cancel_right, show (1:ℂ)+1=2 by norm_num, one_mul] at hc
  have hp : z^a=z*z^(a-1) := by
    calc
      z^a=z^((1:ℂ)+(a-1)) := by congr 1; ring
      _ = _ := by rw [cpow_add _ _ (slitPlane_ne_zero hz), cpow_one]
  simp only [id_eq, mul_one, show (1:ℂ)+1=2 by norm_num]
  rw [hp]
  linear_combination z^(a-1)*hc

/-- Iterating the all-parameter weighted regularized derivative. -/
theorem iteratedDeriv_cpow_mul_regularized_one (n : ℕ) (a : ℂ) {z : ℂ} (hz : z∈slitPlane) :
    iteratedDeriv n (fun t => t^a*regularizedHGFun {1} {a+1} t) z=
      z^(a-n)*regularizedHGFun {1} {a-n+1} z := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have he : deriv (fun t => t^a*regularizedHGFun {1} {a+1} t)=ᶠ[𝓝 z]
        (fun t => t^(a-1)*regularizedHGFun {1} {a} t) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with t ht
      exact (hasDerivAt_cpow_mul_regularized_one a ht).deriv
    rw [iteratedDeriv_succ',he.iteratedDeriv_eq n]
    have hf : (fun t : ℂ => t^(a-1)*regularizedHGFun {1} {a} t)=
        (fun t : ℂ => t^(a-1)*regularizedHGFun {1} {(a-1)+1} t) := by simp
    rw [hf,ih (a-1)]
    congr 1 <;> push_cast <;> ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun t => t^a*exp
t*scIncGamma a t) z=z^(a-n)*exp z*scIncGamma (a-n) z`. -/
@[dlmf 8.8.E18]
theorem scIncGamma_iteratedDeriv_scaled (n : ℕ) (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => t^a*exp t*scIncGamma a t) z=z^(a-n)*exp z*scIncGamma (a-n) z := by
  have he (a t : ℂ) : t^a*exp t*scIncGamma a t=t^a*regularizedHGFun {1} {a+1} t := by
    rw [scIncGamma]
    have hE : exp t*exp (-t)=1 := by rw [← Complex.exp_add]; simp
    linear_combination t^a*regularizedHGFun {1} {a+1} t*hE
  simp_rw [he]
  exact iteratedDeriv_cpow_mul_regularized_one n a hz

/-- At parameter zero the logarithmic-plane upper Gamma function is `Ein(e^w)-w-γ`. -/
theorem upperIncGammaOnLog_zero (w : ℂ) :
    upperIncGammaOnLog 0 w=expIntEin (exp w)-w-Real.eulerMascheroniConstant := by
  have hz : exp w ≠ 0 := Complex.exp_ne_zero w
  have hd (u : ℂ) : HasDerivAt (fun v => -(expIntEin (exp v)-v)) (exp (0*u-exp u)) u := by
    have h := ((hasDerivAt_expIntEin_complex (Complex.exp_ne_zero u)).comp u
      (Complex.hasDerivAt_exp u)).sub (hasDerivAt_id u)
    refine h.neg.congr_deriv ?_
    have he : exp u ≠ 0 := Complex.exp_ne_zero u
    simp only [zero_mul, zero_sub]
    field_simp
    ring
  have hi := segmentIntegral_eq_sub hd (log (exp w)) w
  rw [upperIncGammaOnLog, hi, upperIncGamma_zero_E1 hz, expIntE1_eq_Ein_complex hz,
    Complex.exp_log hz]
  ring

/-- A full turn of the logarithmic variable does not change `exp`. -/
theorem exp_add_two_pi_int_mul_I (w : ℂ) (m : ℤ) : exp (w+2*π*m*I)=exp w := by
  rw [Complex.exp_add, show (2:ℂ)*π*m*I=m*(2*π*I) by ring, exp_int_mul_two_pi_mul_I, mul_one]

/-- At nonpositive integral parameters the logarithmic-plane upper Gamma function changes by an
additive constant under a full turn. -/
theorem upperIncGammaOnLog_neg_nat_monodromy (k : ℕ) (w : ℂ) (m : ℤ) :
    upperIncGammaOnLog (-k) (w+2*π*m*I)=upperIncGammaOnLog (-k) w-2*π*m*I*(-1 : ℂ)^k/k.factorial := by
  induction k with
  | zero =>
    simp only [CharP.cast_eq_zero, neg_zero, upperIncGammaOnLog_zero, exp_add_two_pi_int_mul_I,
      pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    ring
  | succ k ih =>
    have hk : (-((k+1:ℕ):ℂ)) ≠ 0 := by push_cast; exact neg_ne_zero.mpr (by exact_mod_cast k.succ_ne_zero)
    have hr (v : ℂ) := upperIncGammaOnLog_add_one (-((k+1:ℕ):ℂ)) v
    rw [show -((k+1:ℕ):ℂ)+1=-(k:ℂ) by push_cast; ring] at hr
    have he : exp (-((k+1:ℕ):ℂ)*(w+2*π*m*I))=exp (-((k+1:ℕ):ℂ)*w) := by
      have := exp_add_two_pi_int_mul_I (-((k+1:ℕ):ℂ)*w) (-((k+1:ℕ):ℤ)*m)
      rw [← this]; congr 1; push_cast; ring
    have h1 := hr (w+2*π*m*I)
    have h0 := hr w
    rw [ih, exp_add_two_pi_int_mul_I, show -((k+1:ℕ):ℂ)*(w+2*π*m*I)-exp w
      =-((k+1:ℕ):ℂ)*(w+2*π*m*I)+(-exp w) by ring, Complex.exp_add, he] at h1
    rw [show -((k+1:ℕ):ℂ)*w-exp w=-((k+1:ℕ):ℂ)*w+(-exp w) by ring, Complex.exp_add] at h0
    have hf : ((k+1).factorial : ℂ)=(k+1)*k.factorial := by push_cast [Nat.factorial_succ]; ring
    rw [hf]
    have hk' : (k:ℂ)+1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
    have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hinv : ((k:ℂ)+1)⁻¹*((k:ℂ)+1)=1 := inv_mul_cancel₀ hk'
    push_cast at h1 h0 ⊢
    rw [pow_succ, div_eq_mul_inv, mul_inv]
    linear_combination ((k:ℂ)+1)⁻¹*(h1-h0)-(upperIncGammaOnLog (-(k+1)) (w+2*π*m*I)-upperIncGammaOnLog (-(k+1)) w)*hinv

/-- On the principal strip the logarithmic-plane upper Gamma function is the principal one. -/
theorem upperIncGammaOnLog_eq_upperIncGamma (a : ℂ) {w : ℂ} (h1 : -π < w.im) (h2 : w.im ≤ π) :
    upperIncGammaOnLog a w=upperIncGamma a (exp w) := by
  rw [upperIncGammaOnLog, Complex.log_exp h1 h2]
  simp [segmentIntegral]

/-- The logarithmic-plane upper Gamma function has derivative `-exp (a w - e^w)` at every
parameter. -/
theorem hasDerivAt_upperIncGammaOnLog (a w : ℂ) :
    HasDerivAt (upperIncGammaOnLog a) (-exp (a*w-exp w)) w := by
  by_cases ha : ∀ n : ℕ, a ≠ -n
  · have h := (hasDerivAt_lowerIncGammaOnLog ha w).const_sub (Gamma a)
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun v => upperIncGammaOnLog_eq_Gamma_sub ha v)
  push Not at ha
  obtain ⟨n, rfl⟩ := ha
  induction n generalizing w with
  | zero =>
    have h := (((hasDerivAt_expIntEin_complex (Complex.exp_ne_zero w)).comp w
      (Complex.hasDerivAt_exp w)).sub (hasDerivAt_id w)).sub_const (Real.eulerMascheroniConstant:ℂ)
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)).congr_deriv ?_
    · simp [upperIncGammaOnLog_zero]
    · have he : exp w ≠ 0 := Complex.exp_ne_zero w
      simp only [CharP.cast_eq_zero, neg_zero, zero_mul, zero_sub, id, Function.comp_apply]
      field_simp
      ring
  | succ n ih =>
    have hk : (-((n+1:ℕ):ℂ)) ≠ 0 := by
      push_cast; exact neg_ne_zero.mpr (by exact_mod_cast n.succ_ne_zero)
    set a : ℂ := -((n+1:ℕ):ℂ) with ha
    have hr (v : ℂ) : upperIncGammaOnLog a v = (upperIncGammaOnLog (-(n:ℂ)) v - exp (a*v-exp v))/a := by
      have := upperIncGammaOnLog_add_one a v
      rw [show a+1 = -(n:ℂ) by rw [ha]; push_cast; ring] at this
      rw [this]; field_simp; ring
    have he : HasDerivAt (fun v => exp (a*v-exp v)) (exp (a*w-exp w)*(a-exp w)) w := by
      have := (((hasDerivAt_id w).const_mul a).sub (Complex.hasDerivAt_exp w)).cexp
      simpa using this
    have h := ((ih w).sub he).div_const a
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun v => hr v)).congr_deriv ?_
    rw [show -(n:ℂ) = a+1 by rw [ha]; push_cast; ring,
      show (a+1)*w-exp w = (a*w-exp w)+w by ring, Complex.exp_add (a*w-exp w)]
    field_simp
    ring

end DLMF.Confluent
