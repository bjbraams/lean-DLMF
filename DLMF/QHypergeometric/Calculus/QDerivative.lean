/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Convergence
public import DLMF.QSeries.QCalculus
public import DLMF.QSeries.Saalschutz
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import DLMF.QHypergeometric.Calculus.QBinomial

/-!
# The q-derivative (DLMF 17.2.41–17.2.44)

Jackson's q-derivative `qDerivExtended` reuses `DLMF.QSeries.qDeriv` at nonzero arguments
and takes the ordinary derivative at the origin, as DLMF prescribes; `qDerivIterate` is its
`n`-fold iterate.

## Main results

* `qDeriv_iterate_finite_difference`, `qDeriv_iterate_origin`: the finite-difference form
  17.2.42, away from and at the origin.
* `qDeriv_product_extended`, `qDeriv_leibniz`, `qDeriv_leibniz_origin`: 17.2.43–17.2.44.
* `qDeriv_limit`, `qDeriv_iterate_limit`: the q-derivatives tend to ordinary derivatives as
  `q → 1`.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory Asymptotics
open scoped Real Topology
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- Jackson's q-derivative with the derivative value at the origin specified in DLMF. -/
@[dlmf 17.2.E41]
def qDerivExtended (q : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z=0 then deriv f 0 else DLMF.QSeries.qDeriv q f z
/-- The n-fold q-derivative, including its DLMF value at the origin. -/
def qDerivIterate (n : ℕ) (q : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (fun g : ℂ → ℂ => qDerivExtended q g)^[n] f
/-- Away from the origin the existing q-derivative is reused exactly. -/
theorem qDerivExtended_of_ne_zero {z : ℂ} (hz : z≠0) (q : ℂ) (f : ℂ → ℂ) :
    qDerivExtended q f z=DLMF.QSeries.qDeriv q f z := by simp [qDerivExtended,hz]
/-- The value at the origin is the ordinary derivative, rather than division by zero. -/
theorem qDerivExtended_zero (q : ℂ) (f : ℂ → ℂ) : qDerivExtended q f 0=deriv f 0 := by
  simp [qDerivExtended]
/-- Away from the origin the `n`-th q-derivative is a finite q-difference: an alternating sum of
`f(zq^j)` weighted by q-binomials (DLMF 17.2.E42). -/
@[dlmf 17.2.E42]
theorem qDeriv_iterate_finite_difference {q z : ℂ} (hq0 : q≠0) (hq1 : q≠1) (hz : z≠0)
    (f : ℂ → ℂ) (n : ℕ) :
    qDerivIterate n q f z=z^(-(n:ℤ))*(1-q)^(-(n:ℤ))*
      ∑ j∈range (n+1), q^(-(n:ℤ)*j+((j+1).choose 2:ℤ))*(-1:ℂ)^j*qBinom q n j*f (z*q^j) := by
  change _=z^(-(n:ℤ))*(1-q)^(-(n:ℤ))*∑ j∈range (n+1), qFiniteDiffCoeff q n j*f (z*q^j)
  have hq1' : (1:ℂ)-q≠0 := sub_ne_zero.mpr (Ne.symm hq1)
  induction n generalizing z with
  | zero => simp [qDerivIterate,qFiniteDiffCoeff]
  | succ n ih =>
    have hqz : q*z≠0 := mul_ne_zero hq0 hz
    rw [qDerivIterate,Function.iterate_succ_apply',← qDerivIterate,qDerivExtended_of_ne_zero hz,
      qDeriv,ih hz,ih hqz,sum_qFiniteDiffCoeff_succ hq0 (fun j => f (z*q^j)) n]
    have e : ∀ j : ℕ, q*z*q^j=z*q^(j+1) := fun j => by rw [pow_succ]; ring
    simp only [e]
    generalize ∑ j∈range (n+1), qFiniteDiffCoeff q n j*f (z*q^j) = A
    generalize ∑ j∈range (n+1), qFiniteDiffCoeff q n j*f (z*q^(j+1)) = B
    rw [mul_zpow]
    simp only [zpow_neg,zpow_natCast]
    rw [pow_succ,pow_succ]
    field_simp

/-- The q-derivative shifts Taylor coefficients and multiplies them by q-numbers. -/
private lemma qDerivative_taylor_step {q : ℂ} (hq : q ≠ 1) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0) :
    ∃ r : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (qDerivExtended q f) r 0 ∧
      ∀ n, r.coeff n = ((1-q^(n+1))/(1-q))*p.coeff (n+1) := by
  let u : ℂ →L[ℂ] ℂ := q • ContinuousLinearMap.id ℂ ℂ
  have hu (z : ℂ) : u z = q*z := by simp [u,smul_eq_mul]
  have hs := hp.dslope_fslope
  have hs0 : HasFPowerSeriesAt (dslope f 0) p.fslope (u 0) := by simpa [hu] using hs
  have hsc := hs0.compContinuousLinearMap
  let r : FormalMultilinearSeries ℂ ℂ ℂ :=
    (1-q)⁻¹ • (p.fslope - q • p.fslope.compContinuousLinearMap u)
  have hr : HasFPowerSeriesAt (qDerivExtended q f) r 0 := by
    have ht := ((hs.sub (hsc.const_smul (c := q))).const_smul (c := (1-q)⁻¹))
    apply ht.congr
    filter_upwards with z
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Function.comp_apply, hu]
    by_cases hz : z=0
    · subst z
      simp only [qDerivExtended, ite_true, mul_zero, dslope_same]
      have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
      field_simp
    · rw [qDerivExtended_of_ne_zero hz,qDeriv]
      have h1 := sub_smul_dslope f 0 z
      have h2 := sub_smul_dslope f 0 (q*z)
      simp only [sub_zero, smul_eq_mul] at h1 h2
      have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
      field_simp
      linear_combination h1-h2
  refine ⟨r,hr,?_⟩
  intro n
  change ((1-q)⁻¹ • (p.fslope - q • p.fslope.compContinuousLinearMap u)).coeff n = _
  simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.smul_apply,
    FormalMultilinearSeries.sub_apply, _root_.smul_apply, _root_.sub_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply, smul_eq_mul, hu,
    Pi.one_apply, mul_one, Function.comp_def]
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  change (1-q)⁻¹ * (p.fslope.coeff n - q * (q^n * p.fslope.coeff n)) =
    (1-q^(n+1))/(1-q)*p.coeff (n+1)
  rw [FormalMultilinearSeries.coeff_fslope, pow_succ]
  ring

/-- Iterating q-differentiation at zero multiplies the Taylor coefficient by q-factorials. -/
private lemma qDerivative_taylor_iter {q : ℂ} (hq : q ≠ 1) (n : ℕ) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0) :
    qDerivIterate n q f 0 = p.coeff n*qPochhammer q q n/(1-q)^n := by
  induction n generalizing f p with
  | zero =>
    simp only [qDerivIterate, Function.iterate_zero, id_eq, qPochhammer_zero,
      pow_zero,mul_one,div_one]
    exact (hp.coeff_zero 1).symm
  | succ n ih =>
    obtain ⟨r,hr,hcoeff⟩ := qDerivative_taylor_step hq hp
    have he : qDerivIterate (n+1) q f =
        qDerivIterate n q (qDerivExtended q f) := by
      change (fun g : ℂ → ℂ => qDerivExtended q g)^[n+1] f =
        (fun g : ℂ → ℂ => qDerivExtended q g)^[n] (qDerivExtended q f)
      rw [Function.iterate_succ_apply]
    rw [he, ih hr, hcoeff, qPochhammer_succ, pow_succ]
    have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
    field_simp
    ring

/-- At the origin the `n`-th q-derivative of an analytic function is `f^(n)(0) (q;q)_n/(n!
(1-q)^n)` (DLMF 17.2.E42). -/
@[dlmf 17.2.E42]
theorem qDeriv_iterate_origin {q : ℂ} (hq1 : q≠1) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    qDerivIterate n q f 0=iteratedDeriv n f 0*qPochhammer q q n/
      ((n.factorial:ℂ)*(1-q)^n) := by
  obtain ⟨p,hp⟩ := hf
  rw [qDerivative_taylor_iter hq1 n hp]
  have heq := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  have hn : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hc' : p.coeff n = iteratedDeriv n f 0 / n.factorial := by simpa using hc
  rw [hc']
  field_simp

/-- The q-product rule `D_q(fg)(z) = g(z) D_q f(z) + f(zq) D_q g(z)` (DLMF 17.2.E43). -/
@[dlmf 17.2.E43]
theorem qDeriv_product_extended (q z : ℂ) (f g : ℂ → ℂ)
    (hf : z=0 → DifferentiableAt ℂ f 0) (hg : z=0 → DifferentiableAt ℂ g 0) :
    qDerivExtended q (fun w => f w*g w) z=
      g z*qDerivExtended q f z+f (z*q)*qDerivExtended q g z := by
  by_cases hz : z=0
  · subst z
    simpa [qDerivExtended,mul_comm] using deriv_fun_mul (hf rfl) (hg rfl)
  · simpa [qDerivExtended,hz,mul_comm] using qDeriv_mul q f g z

/-- The q-Pascal recurrence combines the two finite sums arising in the product rule. -/
private lemma qLeibniz_sum (q : ℂ) (n : ℕ) (F G : ℕ → ℂ) :
    (∑ j ∈ range (n+2), qBinom q (n+1) j * F j * G j) =
      (∑ j ∈ range (n+1), qBinom q n j * q^j * F j * G j) +
      (∑ j ∈ range (n+1), qBinom q n j * F (j+1) * G (j+1)) := by
  rw [sum_range_succ' _ (n+1)]
  simp only [qBinom_zero_right, one_mul]
  have h : ∑ j ∈ range (n+1), qBinom q (n+1) (j+1) * F (j+1) * G (j+1) =
      (∑ j ∈ range (n+1), qBinom q n j * F (j+1) * G (j+1)) +
      ∑ j ∈ range (n+1), q^(j+1) * qBinom q n (j+1) * F (j+1) * G (j+1) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rw [qBinom_succ_succ]
    ring
  have hb : (∑ j ∈ range (n+1), qBinom q n j * q^j * F j * G j) =
      F 0 * G 0 + ∑ j ∈ range n, qBinom q n (j+1) * q^(j+1) * F (j+1) * G (j+1) := by
    rw [sum_range_succ' _ n]
    simp only [qBinom_zero_right,pow_zero,one_mul]
    ring
  have hc : (∑ j ∈ range (n+1), q^(j+1)*qBinom q n (j+1)*F (j+1)*G (j+1)) =
      ∑ j ∈ range n, qBinom q n (j+1)*q^(j+1)*F (j+1)*G (j+1) := by
    rw [sum_range_succ, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
    simp only [mul_zero, zero_mul, add_zero]
    apply sum_congr rfl
    intro j hj
    ring
  rw [h, hb, hc]
  ring

/-- The q-difference of a product with its first argument scaled by a power of q. -/
private lemma qLeibniz_product {q z : ℂ} (hq : q ≠ 0) (hq1 : q ≠ 1) (hz : z ≠ 0)
    (f g : ℂ → ℂ) (j : ℕ) :
    (f (z*q^j)*g z - f (q*z*q^j)*g (q*z)) / ((1-q)*z) =
      q^j*qDeriv q f (z*q^j)*g z + f (z*q^(j+1))*qDeriv q g z := by
  have h1 : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  simp only [qDeriv,pow_succ]
  field_simp
  ring

/-- At a nonzero argument, the next extended q-derivative is the ordinary q-difference. -/
private lemma qLeibniz_iter_succ {q z : ℂ} (hz : z ≠ 0) (f : ℂ → ℂ) (n : ℕ) :
    qDeriv q (qDerivIterate n q f) z = qDerivIterate (n+1) q f z := by
  change qDeriv q (qDerivIterate n q f) z =
    ((fun g : ℂ → ℂ => qDerivExtended q g)^[n+1] f) z
  rw [Function.iterate_succ_apply',← qDerivIterate,qDerivExtended_of_ne_zero hz]

/-- The q-Leibniz rule for the `n`-th q-derivative of a product, away from the origin (DLMF
17.2.E44). -/
@[dlmf 17.2.E44]
theorem qDeriv_leibniz {q z : ℂ} (hq0 : q≠0) (hq1 : q≠1) (hz : z≠0)
    (f g : ℂ → ℂ) (n : ℕ) :
    qDerivIterate n q (fun w => f w*g w) z=
      ∑ j∈range (n+1), qBinom q n j*qDerivIterate (n-j) q f (z*q^j)*qDerivIterate j q g z := by
  induction n generalizing z with
  | zero => simp [qDerivIterate]
  | succ n ih =>
    have hqz : q*z ≠ 0 := mul_ne_zero hq0 hz
    rw [qDerivIterate,Function.iterate_succ_apply',← qDerivIterate,
      qDerivExtended_of_ne_zero hz,qDeriv, ih hz, ih hqz, ← sum_sub_distrib, sum_div]
    rw [qLeibniz_sum q n (fun j => qDerivIterate (n+1-j) q f (z*q^j))
      (fun j => qDerivIterate j q g z), ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
    have hpow : z*q^j ≠ 0 := mul_ne_zero hz (pow_ne_zero j hq0)
    have h := qLeibniz_product hq0 hq1 hz (qDerivIterate (n-j) q f)
      (qDerivIterate j q g) j
    rw [qLeibniz_iter_succ hpow, qLeibniz_iter_succ hz] at h
    have hindex : n+1-j = (n-j)+1 := by omega
    rw [hindex, show n+1-(j+1)=n-j by omega]
    convert congrArg (fun w : ℂ => qBinom q n j * w) h using 1 <;> ring

/-- The extended q-derivative of a germ analytic at zero is analytic there. -/
private lemma qLeibniz_analytic {q : ℂ} (hq : q ≠ 1) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (qDerivExtended q f) 0 := by
  have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hd : AnalyticAt ℂ (dslope f 0) 0 := hf.dslope 0
  have ha : AnalyticAt ℂ (fun z : ℂ =>
      (dslope f 0 z - q*dslope f 0 (q*z))/(1-q)) 0 := by
    have hqz : AnalyticAt ℂ (fun z : ℂ => q*z) 0 := analyticAt_const.mul analyticAt_id
    have hc : AnalyticAt ℂ (fun z : ℂ => dslope f 0 (q*z)) 0 := by
      have hd' : AnalyticAt ℂ (dslope f 0) (q*0) := by rw [mul_zero]; exact hd
      exact hd'.comp hqz
    exact (hd.sub (analyticAt_const.mul hc)).div_const
  apply ha.congr
  filter_upwards with z
  by_cases hz : z=0
  · subst z
    simp only [qDerivExtended, ite_true, mul_zero, dslope_same]
    field_simp
  · rw [qDerivExtended_of_ne_zero hz,qDeriv]
    have h1 := sub_smul_dslope f 0 z
    have h2 := sub_smul_dslope f 0 (q*z)
    simp only [sub_zero, smul_eq_mul] at h1 h2
    field_simp
    linear_combination h1 - h2

/-- Every iterated extended q-derivative preserves analyticity at zero. -/
private lemma qLeibniz_iter_analytic {q : ℂ} (hq : q ≠ 1) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (n : ℕ) : AnalyticAt ℂ (qDerivIterate n q f) 0 := by
  induction n with
  | zero => simpa [qDerivIterate] using hf
  | succ n ih =>
    rw [qDerivIterate,Function.iterate_succ_apply',← qDerivIterate]
    exact qLeibniz_analytic hq ih

/-- Extended q-differentiation is additive for germs analytic at zero. -/
private lemma qLeibniz_add {q : ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    qDerivExtended q (fun z => f z + g z) =
      fun z => qDerivExtended q f z + qDerivExtended q g z := by
  funext z
  by_cases hz : z=0
  · subst z
    simpa [qDerivExtended] using deriv_fun_add hf.differentiableAt hg.differentiableAt
  · simp only [qDerivExtended,hz,ite_false]
    exact qDeriv_add q f g z

/-- Extended q-differentiation commutes with constant multiplication. -/
private lemma qLeibniz_const {q c : ℂ} (f : ℂ → ℂ) :
    qDerivExtended q (fun z => c*f z) = fun z => c*qDerivExtended q f z := by
  funext z
  by_cases hz : z=0
  · subst z
    simp [qDerivExtended,deriv_const_mul_field]
  · simp only [qDerivExtended,hz,ite_false]
    exact qDeriv_const_mul q c f z

/-- An iterated q-derivative can be differentiated once more. -/
private lemma qLeibniz_succ (q : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    qDerivIterate (n+1) q f = qDerivExtended q (qDerivIterate n q f) := by
  rw [qDerivIterate,Function.iterate_succ_apply',← qDerivIterate]

/-- An initial q-derivative can be incorporated into an iterate. -/
private lemma qLeibniz_succ_input (q : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    qDerivIterate n q (qDerivExtended q f) = qDerivIterate (n+1) q f := by
  change (fun g : ℂ → ℂ => qDerivExtended q g)^[n] (qDerivExtended q f) =
    (fun g : ℂ → ℂ => qDerivExtended q g)^[n+1] f
  rw [Function.iterate_succ_apply]

/-- Iterated extended q-differentiation is additive on analytic germs. -/
private lemma qLeibniz_iter_add {q : ℂ} (hq : q≠1) {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    qDerivIterate n q (fun z => f z + g z) =
      fun z => qDerivIterate n q f z + qDerivIterate n q g z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qLeibniz_succ]
    rw [ih, qLeibniz_add (qLeibniz_iter_analytic hq hf n) (qLeibniz_iter_analytic hq hg n)]

/-- Iterated extended q-differentiation commutes with constant multiplication. -/
private lemma qLeibniz_iter_const {q c : ℂ} (f : ℂ → ℂ) (n : ℕ) :
    qDerivIterate n q (fun z => c*f z) = fun z => c*qDerivIterate n q f z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qLeibniz_succ]
    rw [ih,qLeibniz_const]

/-- At base zero the Gaussian coefficient is one in the triangular range. -/
private lemma qLeibniz_binom_zero (n j : ℕ) (hj : j ≤ n) : qBinom 0 n j = 1 := by
  induction n generalizing j with
  | zero =>
    have h : j=0 := by omega
    subst j
    simp
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [qBinom_succ_succ]
      simp [ih j (by omega)]

/-- At base zero, the q-derivatives of a product at zero form a convolution. -/
private lemma qLeibniz_zero_conv {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    qDerivIterate n 0 (fun z => f z*g z) 0 =
      ∑ j ∈ range (n+1), qDerivIterate (n-j) 0 f 0*qDerivIterate j 0 g 0 := by
  induction n generalizing f g with
  | zero => simp [qDerivIterate]
  | succ n ih =>
    have h0 : (0 : ℂ) ≠ 1 := by norm_num
    have hprod : qDerivExtended 0 (fun z => f z*g z) =
        fun z => qDerivExtended 0 f z*g z + f 0*qDerivExtended 0 g z := by
      funext z
      simpa [mul_comm] using qDeriv_product_extended 0 z f g
        (fun _ => hf.differentiableAt) (fun _ => hg.differentiableAt)
    have hs : qDerivIterate (n+1) 0 (fun z => f z*g z) =
        qDerivIterate n 0 (qDerivExtended 0 (fun z => f z*g z)) := by
      rw [qDerivIterate,Function.iterate_succ_apply,← qDerivIterate]
    rw [hs,hprod,qLeibniz_iter_add (f := fun z => qDerivExtended 0 f z*g z)
      (g := fun z => f 0*qDerivExtended 0 g z) h0 ((qLeibniz_analytic h0 hf).mul hg)
      (analyticAt_const.mul (qLeibniz_analytic h0 hg)),qLeibniz_iter_const]
    dsimp only
    rw [ih (qLeibniz_analytic h0 hf) hg]
    rw [qLeibniz_succ_input]
    conv_rhs => rw [sum_range_succ]
    have heq : (∑ j ∈ range (n+1),
        qDerivIterate (n-j) 0 (qDerivExtended 0 f) 0*qDerivIterate j 0 g 0) =
        ∑ j ∈ range (n+1), qDerivIterate (n+1-j) 0 f 0*qDerivIterate j 0 g 0 := by
      apply sum_congr rfl
      intro j hj
      rw [show n+1-j=(n-j)+1 by have := mem_range.mp hj; omega,
        qLeibniz_succ_input]
    rw [heq]
    simp [qDerivIterate]

/-- The q-Leibniz rule at the origin for analytic factors (DLMF 17.2.E44). -/
@[dlmf 17.2.E44]
theorem qDeriv_leibniz_origin {q : ℂ} (hq1 : q≠1) {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    qDerivIterate n q (fun w => f w*g w) 0=
      ∑ j∈range (n+1), qBinom q n j*qDerivIterate (n-j) q f 0*qDerivIterate j q g 0 := by
  by_cases hq0 : q=0
  · subst q
    rw [qLeibniz_zero_conv hf hg]
    apply sum_congr rfl
    intro j hj
    rw [qLeibniz_binom_zero n j (Nat.le_of_lt_succ (mem_range.mp hj))]
    ring
  have hL : ContinuousAt (qDerivIterate n q (fun w => f w*g w)) 0 :=
    (qLeibniz_iter_analytic hq1 (hf.mul hg) n).continuousAt
  have hR : ContinuousAt (fun z : ℂ => ∑ j ∈ range (n+1),
      qBinom q n j*qDerivIterate (n-j) q f (z*q^j)*qDerivIterate j q g z) 0 := by
    apply tendsto_finsetSum
    intro j hj
    have hF : ContinuousAt (fun z : ℂ => qDerivIterate (n-j) q f (z*q^j)) 0 := by
      have ht : ContinuousAt (qDerivIterate (n-j) q f) ((0:ℂ)*q^j) := by
        simpa using (qLeibniz_iter_analytic hq1 hf (n-j)).continuousAt
      exact ht.comp (f := fun z : ℂ => z*q^j) (continuousAt_id.mul_const (q^j))
    exact ((continuousAt_const.mul hF).mul (qLeibniz_iter_analytic hq1 hg j).continuousAt).tendsto
  have he : (fun z : ℂ => qDerivIterate n q (fun w => f w*g w) z) =ᶠ[𝓝[≠] 0]
      (fun z : ℂ => ∑ j ∈ range (n+1),
        qBinom q n j*qDerivIterate (n-j) q f (z*q^j)*qDerivIterate j q g z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact qDeriv_leibniz hq0 hq1 hz f g n
  have h := tendsto_nhds_unique (hL.tendsto.mono_left nhdsWithin_le_nhds)
    ((hR.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  simpa using h

/-- As `q → 1`, the q-derivative of a differentiable function tends to its derivative. -/
theorem qDeriv_limit {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    Tendsto (fun q : ℂ => qDerivExtended q f z) (𝓝[≠] 1) (𝓝 (deriv f z)) := by
  by_cases hz : z=0
  · subst z
    simp [qDerivExtended]
  · simpa [qDerivExtended,hz] using DLMF.QSeries.tendsto_qDeriv hf.hasDerivAt hz

/-- The finite geometric q-number tends to its integer index as the complex base tends to one. -/
private lemma qLimit_qnum_limit (m : ℕ) :
    Tendsto (fun q : ℂ => qNum q m) (𝓝[≠] 1) (𝓝 (m : ℂ)) := by
  have h : Tendsto (fun q : ℂ => ∑ j ∈ range m, q^j) (𝓝[≠] 1)
      (𝓝 (∑ j ∈ range m, (1 : ℂ)^j)) := by
    apply tendsto_finsetSum
    intro j hj
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).pow j
  simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  unfold qNum
  apply (eq_div_iff hq').2
  exact geom_sum_mul_neg q m

/-- The normalized finite q-factorial tends to the ordinary factorial as the complex base
tends to one. -/
private lemma qLimit_qfactorial_limit (n : ℕ) :
    Tendsto (fun q : ℂ => qPochhammer q q n/(1-q)^n) (𝓝[≠] 1)
      (𝓝 (n.factorial : ℂ)) := by
  induction n with
  | zero => simp [qPochhammer_zero]
  | succ n ih =>
    have ht := ih.mul (qLimit_qnum_limit (n+1))
    have heq : (fun q : ℂ => qPochhammer q q (n+1)/(1-q)^(n+1)) =ᶠ[𝓝[≠] 1]
        (fun q => qPochhammer q q n/(1-q)^n*qNum q (n+1)) := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
      rw [qPochhammer_succ,pow_succ,qNum,pow_succ]
      field_simp
    convert ht.congr' heq.symm using 1;
      simp [Nat.factorial_succ, mul_comm]

/-- The extended q-derivative of a monomial, including its removable value at the origin. -/
private lemma qLimit_qderiv_monomial {q : ℂ} (hq : q≠1) (m : ℕ) :
    qDerivExtended q (fun z : ℂ => z^m) = fun z => qNum q m*z^(m-1) := by
  funext z
  by_cases hz : z=0
  · subst z
    cases m with
    | zero => simp [qDerivExtended,qNum]
    | succ m =>
      cases m with
      | zero =>
        have hq' : (1:ℂ)-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
        simp [qDerivExtended,qNum,deriv_id'',hq']
      | succ m => simp [qDerivExtended]
  · rw [qDerivExtended_of_ne_zero hz]
    exact qDeriv_pow hq hz m

/-- Constant scalar multiplication commutes with the extended q-derivative. -/
private lemma qLimit_qconst {q c : ℂ} (f : ℂ → ℂ) :
    qDerivExtended q (fun z => c*f z) = fun z => c*qDerivExtended q f z := by
  funext z
  by_cases hz : z=0
  · subst z
    simp [qDerivExtended,deriv_const_mul_field]
  · simp only [qDerivExtended,hz,ite_false]
    exact qDeriv_const_mul q c f z

/-- Repeated q-differentiation of a monomial multiplies by successive q-numbers. -/
private lemma qLimit_qmonomial_iter {q : ℂ} (hq : q≠1) (m n : ℕ) :
    qDerivIterate n q (fun z : ℂ => z^m) =
      fun z => (∏ j ∈ range n, qNum q (m-j))*z^(m-n) := by
  induction n with
  | zero => simp [qDerivIterate]
  | succ n ih =>
    rw [qDerivIterate,Function.iterate_succ_apply',← qDerivIterate,ih,qLimit_qconst,
      qLimit_qderiv_monomial hq, prod_range_succ]
    simp only [show m-(n+1)=(m-n)-1 by omega]
    funext z
    ring

/-- Each iterated q-derivative of a monomial tends to its ordinary iterated derivative. -/
private lemma qLimit_qmonomial_limit (m n : ℕ) (z : ℂ) :
    Tendsto (fun q : ℂ => qDerivIterate n q (fun z : ℂ => z^m) z) (𝓝[≠] 1)
      (𝓝 (iteratedDeriv n (fun z : ℂ => z^m) z)) := by
  have h : Tendsto (fun q : ℂ => (∏ j ∈ range n, qNum q (m-j))*z^(m-n))
      (𝓝[≠] 1) (𝓝 ((∏ j ∈ range n, ((m-j : ℕ):ℂ))*z^(m-n))) := by
    apply Tendsto.mul_const
    apply tendsto_finsetProd
    intro j hj
    exact qLimit_qnum_limit (m-j)
  have hprod : (∏ j ∈ range n, ((m-j : ℕ):ℂ)) = (m.descFactorial n : ℂ) := by
    rw [Nat.descFactorial_eq_prod_range]
    exact (Nat.cast_prod _ _).symm
  rw [hprod, ← iteratedDeriv_pow] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (congrFun (qLimit_qmonomial_iter hq m n) z).symm

/-- Away from zero, iterated q-differentiation commutes with finite linear combinations. -/
private lemma qLimit_qiter_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (F : ι → ℂ → ℂ)
    {q z : ℂ} (hq0 : q≠0) (hq1 : q≠1) (hz : z≠0) (n : ℕ) :
    qDerivIterate n q (fun w => ∑ i ∈ s, a i*F i w) z =
      ∑ i ∈ s, a i*qDerivIterate n q (F i) z := by
  rw [qDeriv_iterate_finite_difference hq0 hq1 hz]
  simp_rw [qDeriv_iterate_finite_difference hq0 hq1 hz]
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

/-- Away from zero, iterated q-differentiation commutes with finite linear combinations. -/
private lemma qLimit_qLimit_qiter_sum_limit {ι : Type*} (s : Finset ι) (a : ι → ℂ) (m : ι → ℕ)
    {z : ℂ} (hz : z≠0) (n : ℕ) :
    Tendsto (fun q : ℂ => qDerivIterate n q (fun w => ∑ i ∈ s, a i*w^(m i)) z)
      (𝓝[≠] 1) (𝓝 (iteratedDeriv n (fun w => ∑ i ∈ s, a i*w^(m i)) z)) := by
  have ht : Tendsto (fun q : ℂ => ∑ i ∈ s, a i*qDerivIterate n q (fun w : ℂ => w^(m i)) z)
      (𝓝[≠] 1) (𝓝 (∑ i ∈ s, a i*iteratedDeriv n (fun w : ℂ => w^(m i)) z)) := by
    apply tendsto_finsetSum
    intro i hi
    exact (qLimit_qmonomial_limit (m i) n z).const_mul (a i)
  have he : iteratedDeriv n (fun w : ℂ => ∑ i ∈ s, a i*w^(m i)) z =
      ∑ i ∈ s, a i*iteratedDeriv n (fun w : ℂ => w^(m i)) z := by
    rw [iteratedDeriv_fun_sum]
    · apply sum_congr rfl
      intro i hi
      exact iteratedDeriv_const_mul_field _ _
    · intro i hi
      fun_prop
  rw [he]
  apply ht.congr'
  have hq0 : ∀ᶠ q : ℂ in 𝓝[≠] 1, q≠0 := by
    exact (eventually_ne_nhds (by norm_num : (1:ℂ)≠0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hq0,self_mem_nhdsWithin] with q hq0 hq1
  exact (qLimit_qiter_sum s a (fun i w => w^(m i)) hq0 hq1 hz n).symm

/-- The iterated q-derivatives of a translated monomial have their classical limits. -/
private lemma qLimit_qiter_centered_limit (m n : ℕ) {z : ℂ} (hz : z≠0) :
    Tendsto (fun q : ℂ => qDerivIterate n q (fun w => (w-z)^m) z)
      (𝓝[≠] 1) (𝓝 (iteratedDeriv n (fun w => (w-z)^m) z)) := by
  have he : (fun w : ℂ => (w-z)^m) =
      fun w => ∑ k ∈ range (m+1), ((m.choose k:ℂ)*(-z)^(m-k))*w^k := by
    funext w
    rw [sub_eq_add_neg,add_pow]
    apply sum_congr rfl
    intro k hk
    ring
  rw [he]
  exact qLimit_qLimit_qiter_sum_limit (range (m+1)) _ _ hz n

/-- A Taylor remainder of order `n + 1` contributes zero to the classical limit of the
`n`th q-derivative. -/
private lemma qLimit_qiter_remainder_limit {R : ℂ → ℂ} {z : ℂ} (hz : z≠0) (n : ℕ)
    (hR : (fun h : ℂ => R (z+h)) =O[𝓝 0] fun h => ‖h‖^(n+1)) :
    Tendsto (fun q : ℂ => qDerivIterate n q R z) (𝓝[≠] 1) (𝓝 0) := by
  have hterm (j : ℕ) : Tendsto (fun q : ℂ => R (z*q^j)/(1-q)^n) (𝓝[≠] 1) (𝓝 0) := by
    have hh : Tendsto (fun q : ℂ => z*q^j-z) (𝓝[≠] 1) (𝓝 0) := by
      simpa using ((((tendsto_id : Tendsto (fun q : ℂ => q) (𝓝 1) (𝓝 1)).mono_left
        nhdsWithin_le_nhds).pow j).const_mul z).sub_const z
    have hd : DifferentiableAt ℂ (fun q : ℂ => z*q^j) 1 := by fun_prop
    have hb : (fun q : ℂ => z*q^j-z) =O[𝓝[≠] 1] fun q => q-1 := by
      simpa using hd.isBigO_sub.mono nhdsWithin_le_nhds
    have he := hR.comp_tendsto hh
    have hb' := hb.norm_left.pow (n+1)
    have hs : (fun q : ℂ => R (z*q^j)) =O[𝓝[≠] 1] fun q => ‖q-1‖^(n+1) := by
      have ht := he.trans hb'.norm_right
      simp only [norm_pow, Function.comp_def] at ht
      convert ht using 1
      funext q
      congr 1
      ring
    have hl := hs.trans_isLittleO
      ((isLittleO_pow_sub_pow_sub (1:ℂ) (Nat.lt_succ_self n)).mono nhdsWithin_le_nhds)
    have hl' : (fun q : ℂ => R (z*q^j)) =o[𝓝[≠] 1] fun q => (1-q)^n := by
      rw [← isLittleO_norm_right]
      simpa only [norm_pow, norm_sub_rev] using hl
    exact hl'.tendsto_div_nhds_zero
  have hsum : Tendsto (fun q : ℂ => ∑ j ∈ range (n+1),
      q^(-(n:ℤ)*j+((j+1).choose 2:ℤ))*(-1:ℂ)^j*qBinom q n j*
        (R (z*q^j)/(1-q)^n)) (𝓝[≠] 1) (𝓝 0) := by
    have hc (j : ℕ) : ContinuousAt (fun q : ℂ =>
        q^(-(n:ℤ)*j+((j+1).choose 2:ℤ))*(-1:ℂ)^j*qBinom q n j) 1 := by
      exact ((continuousAt_id.zpow₀ _ (by norm_num)).mul_const _).mul
        (continuous_qBinom n j).continuousAt
    have ht := tendsto_finsetSum (range (n+1)) (fun j hj =>
      ((hc j).tendsto.mono_left nhdsWithin_le_nhds).mul (hterm j))
    simpa only [mul_zero, sum_const_zero] using ht
  have ht := hsum.const_mul (z^(-(n:ℤ)))
  simp only [mul_zero] at ht
  apply ht.congr'
  have hq0 : ∀ᶠ q : ℂ in 𝓝[≠] 1, q≠0 :=
    (eventually_ne_nhds (by norm_num : (1:ℂ)≠0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hq0,self_mem_nhdsWithin] with q hq0 hq1
  rw [qDeriv_iterate_finite_difference hq0 hq1 hz]
  simp only [zpow_neg,zpow_natCast]
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro j hj
  ring

/-- Finite Taylor polynomials have the expected classical q-derivative limit. -/
private lemma qLimit_qiter_taylor_limit (a : ℕ → ℂ) (N n : ℕ) {z : ℂ} (hz : z≠0) :
    Tendsto (fun q : ℂ => qDerivIterate n q (fun w => ∑ k ∈ range N, a k*(w-z)^k) z)
      (𝓝[≠] 1) (𝓝 (iteratedDeriv n (fun w => ∑ k ∈ range N, a k*(w-z)^k) z)) := by
  have ht := tendsto_finsetSum (range N)
    (fun k hk => (qLimit_qiter_centered_limit k n hz).const_mul (a k))
  have he : iteratedDeriv n (fun w : ℂ => ∑ k ∈ range N, a k*(w-z)^k) z =
      ∑ k ∈ range N, a k*iteratedDeriv n (fun w : ℂ => (w-z)^k) z := by
    rw [iteratedDeriv_fun_sum]
    · apply sum_congr rfl
      intro k hk
      exact iteratedDeriv_const_mul_field _ _
    · intro k hk
      fun_prop
  rw [he]
  apply ht.congr'
  have hq0 : ∀ᶠ q : ℂ in 𝓝[≠] 1, q≠0 :=
    (eventually_ne_nhds (by norm_num : (1:ℂ)≠0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hq0,self_mem_nhdsWithin] with q hq0 hq1
  exact (qLimit_qiter_sum (range N) a (fun k w => (w-z)^k) hq0 hq1 hz n).symm

/-- The `n`th derivative of the degree-`n` Taylor polynomial at its center extracts its
top coefficient. -/
private lemma qLimit_deriv_taylor (a : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w => ∑ k ∈ range (n+1), a k*(w-z)^k) z = a n*n.factorial := by
  rw [iteratedDeriv_fun_sum]
  · simp_rw [iteratedDeriv_const_mul_field]
    have ht (k : ℕ) (hk : k ≤ n) :
        iteratedDeriv n (fun w : ℂ => (w-z)^k) z = if k=n then n.factorial else 0 := by
      rw [iteratedDeriv_comp_sub_const (f := fun w : ℂ => w^k)]
      simp only [sub_self, iteratedDeriv_pow]
      by_cases hkn : k=n
      · subst k
        simp [Nat.descFactorial_self]
      · have hlt : k<n := lt_of_le_of_ne hk hkn
        simp [hkn,Nat.descFactorial_of_lt hlt]
    calc (∑ i ∈ range (n+1), a i*iteratedDeriv n (fun w : ℂ => (w-z)^i) z) =
        ∑ i ∈ range (n+1), if i=n then a i*n.factorial else 0 := by
          apply sum_congr rfl
          intro k hk
          rw [ht k (Nat.le_of_lt_succ (mem_range.mp hk))]
          split_ifs <;> simp
      _ = a n*n.factorial := by simp
  · intro k hk
    fun_prop

/-- Away from zero, iterated q-differentiation commutes with subtraction. -/
private lemma qLimit_qiter_sub {f g : ℂ → ℂ} {q z : ℂ}
    (hq0 : q≠0) (hq1 : q≠1) (hz : z≠0) (n : ℕ) :
    qDerivIterate n q (fun w => f w-g w) z = qDerivIterate n q f z-qDerivIterate n q g z := by
  simp only [qDeriv_iterate_finite_difference hq0 hq1 hz,mul_sub,sum_sub_distrib]

/-- As `q → 1`, the `n`-th q-derivative of an analytic function tends to its `n`-th derivative. -/
theorem qDeriv_iterate_limit {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (n : ℕ) :
    Tendsto (fun q : ℂ => qDerivIterate n q f z) (𝓝[≠] 1) (𝓝 (iteratedDeriv n f z)) := by
  by_cases hz : z=0
  · subst z
    have ht := (qLimit_qfactorial_limit n).const_mul (iteratedDeriv n f 0/(n.factorial:ℂ))
    have hn : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have ht' : Tendsto (fun q : ℂ => iteratedDeriv n f 0*qPochhammer q q n /
        ((n.factorial:ℂ)*(1-q)^n)) (𝓝[≠] 1) (𝓝 (iteratedDeriv n f 0)) := by
      convert ht using 1 <;> field_simp
    apply ht'.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (qDeriv_iterate_origin hq hf n).symm
  obtain ⟨p,hp⟩ := hf
  let P : ℂ → ℂ := fun w => ∑ k ∈ range (n+1), p.coeff k*(w-z)^k
  have hR : (fun h : ℂ => (f (z+h)-P (z+h))) =O[𝓝 0] fun h => ‖h‖^(n+1) := by
    have h := hp.isBigO_sub_partialSum_pow (n+1)
    convert h using 1
    funext w
    dsimp [P,FormalMultilinearSeries.partialSum]
    congr 1
    apply sum_congr rfl
    intro k hk
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    simp [smul_eq_mul,mul_comm]
  have ht := (qLimit_qiter_taylor_limit p.coeff (n+1) n hz).add
    (qLimit_qiter_remainder_limit (R := fun w => f w-P w) hz n hR)
  simp only [add_zero] at ht
  have hcoeff : p.coeff n = iteratedDeriv n f z/n.factorial := by
    have heq := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
    simpa using hc
  rw [qLimit_deriv_taylor,hcoeff,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))] at ht
  apply ht.congr'
  have hq0 : ∀ᶠ q : ℂ in 𝓝[≠] 1, q≠0 :=
    (eventually_ne_nhds (by norm_num : (1:ℂ)≠0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hq0,self_mem_nhdsWithin] with q hq0 hq1
  change qDerivIterate n q P z+qDerivIterate n q (fun w => f w-P w) z = _
  rw [qLimit_qiter_sub hq0 hq1 hz n]
  ring

end DLMF.QHypergeometric
