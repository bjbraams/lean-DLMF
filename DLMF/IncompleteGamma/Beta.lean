/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.BetaBarnes
public import DLMF.Core.Basic
public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Statistical.IncompleteBeta
public import DLMF.IncompleteGamma.Basic.IncompleteBeta
public import DLMF.IncompleteGamma.BetaContinuedFraction

/-!
# Incomplete Beta function: continuation, recurrences and continued fraction (DLMF §8.17)

## Main definitions

* `incBetaComplement`, `incBetaContiguousParameter`: the data of the contiguous recurrences,
  DLMF 8.17.11.
* `incBetaFractionD`, `incBetaFractionConvergent`: the continued fraction, DLMF 8.17.22–8.17.23.

## Main results

* `incompleteBeta_ofReal`, `regularizedIncompleteBeta_ofReal`: agreement with the real definitions,
  DLMF 8.17.1–8.17.2.
* `regularizedIncompleteBeta_quadratic`: DLMF 8.17.6.
* `incompleteBeta_hypergeometric_euler`, `incompleteBeta_hypergeometric_pfaff`: hypergeometric
  representations, DLMF 8.17.8–8.17.9.
* `regularizedIncompleteBeta_mellinBarnes`: the Mellin–Barnes integral, DLMF 8.17.10.
* `regularizedIncompleteBeta_contiguous_12`, …, `regularizedIncompleteBeta_contiguous_19`: the
  recurrences DLMF 8.17.12–8.17.19, with `regularizedIncompleteBeta_contiguous_limit_12`,
  `regularizedIncompleteBeta_contiguous_limit_16`, `regularizedIncompleteBeta_contiguous_limit_17`
  at the singular case `a + b = 1`.
* `incompleteBeta_continuedFraction`, `incompleteBeta_continuedFraction_endpoint_limit`: the
  continued fraction, DLMF 8.17.22.
* `regularizedIncompleteBeta_negative_binomial_sum`: DLMF 8.17.24.
* `incompleteBeta_cf_upper_bound_counterexample`, `incompleteBeta_cf_third_bound_counterexample`:
  counterexamples to the unqualified claim after 8.17.23 that the convergents are upper bounds.

## Implementation notes

The continued functions `incompleteBeta` and `regularizedIncompleteBeta` are defined in
`DLMF.IncompleteGamma.Basic.IncompleteBeta`; at parameter poles `incompleteBeta` keeps its totalized
values and `regularizedIncompleteBeta` preserves the removable specialization `a = 0`. Results
already in Mathlib are referenced, not reproved.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Statistical

/-- Identity under the stated parameter and domain assumptions:
`incompleteBeta a b x=Real.incompleteBeta a b x`. -/
@[dlmf 8.17.E1]
theorem incompleteBeta_ofReal {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    incompleteBeta a b x=Real.incompleteBeta a b x := by
  have ha0 : a ≠ 0 := ne_zero_of_re_pos ha
  have ha1 : ∀ k : ℕ, a+1 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hab : Gamma (a+b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  by_cases hx1 : x=1
  · subst x
    rw [incompleteBeta, Complex.ofReal_one, if_pos rfl, Real.incompleteBeta_one]
    apply (div_eq_iff hab).mpr
    simpa [mul_comm] using Gamma_mul_Gamma_eq_betaIntegral ha hb
  by_cases hx0 : x=0
  · subst x
    simp [incompleteBeta, zero_cpow ha0]
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
  have hxn : ‖(x:ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_of_nonneg hx.1] using hxlt
  rw [incompleteBeta, if_neg (by exact_mod_cast hx1),
      Real.incompleteBeta_eq_ordinaryHypergeometric ha b hxpos hxlt,
    regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hxn,
    regularizedGaussHypergeometricFun_eq_div_Gamma ha1, Gamma_add_one a ha0]
  field_simp [Gamma_ne_zero_of_re_pos ha]

/-- Identity under the stated parameter and domain assumptions: `regularizedIncompleteBeta a b
x=Real.regularizedIncompleteBeta a b x`. -/
@[dlmf 8.17.E2]
theorem regularizedIncompleteBeta_ofReal {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    regularizedIncompleteBeta a b x=Real.regularizedIncompleteBeta a b x := by
  by_cases hx1 : x=1
  · subst x
    rw [regularizedIncompleteBeta, Complex.ofReal_one, if_pos rfl,
        Real.regularizedIncompleteBeta_one ha hb]
  have hGa := Gamma_ne_zero_of_re_pos ha
  have hGb := Gamma_ne_zero_of_re_pos hb
  have hGab := Gamma_ne_zero_of_re_pos (show 0 < (a+b).re by simp; linarith)
  have hB : betaIntegral a b=Gamma a*Gamma b/Gamma (a+b) := by
    apply (eq_div_iff hGab).mpr
    simpa [mul_comm] using (Gamma_mul_Gamma_eq_betaIntegral ha hb).symm
  rw [Real.regularizedIncompleteBeta, ← incompleteBeta_ofReal ha hb hx, incompleteBeta,
      regularizedIncompleteBeta,
    if_neg (by exact_mod_cast hx1), if_neg (by exact_mod_cast hx1), hB]
  field_simp

/-- The quadratic substitution `u = 4t(1-t)` in the symmetric Beta integral. -/
theorem integral_beta_quadratic_subst {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1/2) :
    (∫ u in (0:ℝ)..4*x*(1-x), u^(a-1)*(1-u)^((1/2:ℝ)-1)) =
      4^a * ∫ t in (0:ℝ)..x, t^(a-1)*(1-t)^(a-1) := by
  set f : ℝ → ℝ := fun t => 4*t*(1-t) with hf
  set g : ℝ → ℝ := fun u => u^(a-1)*(1-u)^((1/2:ℝ)-1) with hg
  have hpt : ∀ t : ℝ, 0 < t → t < 1/2 →
      (g ∘ f) t * (4*(1-2*t)) = 4^a * (t^(a-1)*(1-t)^(a-1)) := by
    intro t ht0 ht1
    have h2 : 0 < 1-2*t := by linarith
    have hf1 : 1 - f t = (1-2*t)^(2:ℕ) := by simp only [hf]; ring
    simp only [Function.comp_apply, hg]
    rw [hf1, ← Real.rpow_natCast, ← Real.rpow_mul h2.le, hf,
      Real.mul_rpow (by positivity) (by linarith), Real.mul_rpow (by norm_num) ht0.le]
    rw [show ((2:ℕ):ℝ)*((1/2:ℝ)-1) = -1 by norm_num, Real.rpow_neg_one]
    rw [show (4:ℝ)^a = 4^(a-1)*4 by rw [← Real.rpow_add_one (by norm_num)]; ring_nf]
    have h2' : 1 - t*2 ≠ 0 := by linarith
    field_simp
  have hae : ∀ᵐ t ∂(volume.restrict (uIcc 0 x)), (g ∘ f) t * (4*(1-2*t)) =
      4^a * (t^(a-1)*(1-t)^(a-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_uIcc,
      ae_restrict_of_ae (Measure.ae_ne volume (0:ℝ)),
      ae_restrict_of_ae (Measure.ae_ne volume (1/2:ℝ))] with t ht h0 h12
    rw [uIcc_of_le hx] at ht
    exact hpt t (lt_of_le_of_ne ht.1 (Ne.symm h0)) (lt_of_le_of_ne (ht.2.trans hx1) h12)
  have hI : IntervalIntegrable (fun t : ℝ => t^(a-1)*(1-t)^(a-1)) volume 0 x :=
    TauCeti.intervalIntegrable_rpow_mul_one_sub_rpow ha ha ⟨le_rfl, zero_le_one⟩
      ⟨hx, by linarith⟩
  have hsub := intervalIntegral.integral_comp_mul_deriv''' (a := 0) (b := x) (f := f)
    (f' := fun t => 4*(1-2*t)) (g := g) (by fun_prop)
    (fun t _ => by
      have : HasDerivAt f (4*(1-2*t)) t := by
        exact (((hasDerivAt_id' t).const_mul 4).mul ((hasDerivAt_id' t).const_sub 1)).congr_deriv
          (by ring)
      exact this.hasDerivWithinAt)
    ?_ ?_ ?_
  · simp only [hf, mul_zero, zero_mul] at hsub
    rw [← hsub, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hx]
    have := (ae_restrict_iff' (measurableSet_uIcc (a := (0:ℝ)) (b := x))).mp hae
    filter_upwards [this] with t ht hmem
    exact ht (by rw [uIcc_of_le hx]; exact Ioc_subset_Icc_self hmem)
  · rintro u ⟨t, ht, rfl⟩
    rw [min_eq_left hx, max_eq_right hx] at ht
    have hu0 : f t ≠ 0 := by
      simp only [hf]; exact (mul_pos (mul_pos four_pos ht.1) (by linarith [ht.2])).ne'
    have hu1 : 1 - f t ≠ 0 := by
      simp only [hf]; nlinarith [ht.1, ht.2]
    refine ContinuousAt.continuousWithinAt ?_
    exact (Real.continuousAt_rpow_const _ _ (Or.inl hu0)).mul
      ((Real.continuousAt_rpow_const _ _ (Or.inl hu1)).comp
          (continuousAt_const.sub continuousAt_id))
  · have h01 : IntervalIntegrable g volume 0 1 :=
      TauCeti.intervalIntegrable_rpow_mul_one_sub_rpow ha (by norm_num : (0:ℝ) < 1/2)
        ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    have h01' : IntegrableOn g (Icc 0 1) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h01
    refine h01'.mono_set ?_
    rintro u ⟨t, ht, rfl⟩
    rw [uIcc_of_le hx] at ht
    simp only [hf]
    constructor <;> nlinarith [ht.1, ht.2]
  · have h := ((intervalIntegrable_iff_integrableOn_Icc_of_le hx).mp hI).const_mul (4^a)
    rw [← uIcc_of_le hx] at h
    exact Integrable.congr h (by filter_upwards [hae] with t ht using ht.symm)

/-- Identity under the stated parameter and domain assumptions:
`regularizedIncompleteBeta a a x=regularizedIncompleteBeta a (1/2) (4*x*(1-x))/2`. -/
@[dlmf 8.17.E6]
theorem regularizedIncompleteBeta_quadratic {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x)
    (hx1 : x ≤ 1/2) :
    regularizedIncompleteBeta a a x=regularizedIncompleteBeta a (1/2) (4*x*(1-x))/2 := by
  have hy : 4*x*(1-x) ∈ Icc (0:ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
  have hxI : x ∈ Icc (0:ℝ) 1 := ⟨hx, by linarith⟩
  have hh : (0:ℝ) < 1/2 := by norm_num
  have ha' : 0 < (a:ℂ).re := by simpa using ha
  rw [show 4*(x:ℂ)*(1-(x:ℂ)) = ((4*x*(1-x) : ℝ) : ℂ) by push_cast; ring,
    show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring,
    regularizedIncompleteBeta_ofReal ha' ha' hxI, regularizedIncompleteBeta_ofReal ha' (by simp) hy,
    Real.regularizedIncompleteBeta_ofReal ha ha hxI, Real.regularizedIncompleteBeta_ofReal ha hh hy,
    TauCeti.regularizedIncompleteBeta_def_of_mem_Icc ha ha hxI,
    TauCeti.regularizedIncompleteBeta_def_of_mem_Icc ha hh hy,
    integral_beta_quadratic_subst ha hx hx1]
  -- the half-way value of the symmetric integral
  have hhalf : TauCeti.regularizedIncompleteBeta a a (1/2) = 1/2 := by
    have := TauCeti.regularizedIncompleteBeta_symm ha ha (1/2)
    rw [show (1:ℝ) - 1/2 = 1/2 by norm_num] at this
    linarith
  have hhalfI := TauCeti.regularizedIncompleteBeta_def_of_mem_Icc ha ha
    (x := 1/2) ⟨by norm_num, by norm_num⟩
  have h1 := integral_beta_quadratic_subst ha (x := 1/2) (by norm_num) le_rfl
  rw [show (4:ℝ)*(1/2)*(1-1/2) = 1 by norm_num, TauCeti.integral_rpow_mul_one_sub_rpow ha hh] at h1
  have hB : 0 < ProbabilityTheory.beta a a := ProbabilityTheory.beta_pos ha ha
  have h4 : 0 < (4:ℝ)^a := by positivity
  rw [hhalf] at hhalfI
  have hBh : ProbabilityTheory.beta a (1/2) = 4^a * (ProbabilityTheory.beta a a / 2) := by
    rw [h1]; congr 1; field_simp at hhalfI ⊢; linarith
  rw [hBh]
  push_cast
  field_simp

/-- Identity under the stated parameter and domain assumptions: `incompleteBeta a b x=(x : ℂ)^(a :
ℂ)*(1-x : ℂ)^(b : ℂ)/a*Gamma (a+1)*DLMF.Hypergeometric.regularizedGaussHypergeometric (a+b) 1 (a+1)
x`. -/
@[dlmf 8.17.E8]
theorem incompleteBeta_hypergeometric_euler {a b : ℝ} (ha : 0 < a) {x : ℝ} (hx1 : x < 1) :
    incompleteBeta a b x=(x : ℂ)^(a : ℂ)*(1-x : ℂ)^(b : ℂ)/a*Gamma
        (a+1)*DLMF.Hypergeometric.regularizedGaussHypergeometric (a+b) 1 (a+1) x := by
  have hc : (x:ℂ) ∈ cutPlane := by
    change 1-(x:ℂ) ∈ slitPlane
    left
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have ha0 : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [incompleteBeta, if_neg (by intro h; have h' := congrArg Complex.re h; simp at h'; linarith),
    regularizedGaussHypergeometric_euler _ _ _ hc,
    show ((a:ℂ)+1)-a-(1-b)=b by ring,
    show ((a:ℂ)+1)-a=1 by ring,
    show ((a:ℂ)+1)-(1-b)=a+b by ring,
    regularizedGaussHypergeometric_symm 1 (a+b) (a+1) hc, Gamma_add_one a ha0]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `incompleteBeta a b x=(x : ℂ)^(a :
ℂ)*(1-x : ℂ)^((b : ℂ)-1)/a*Gamma (a+1)*DLMF.Hypergeometric.regularizedGaussHypergeometric 1 (1-b)
(a+1) (x/(x-1))`. -/
@[dlmf 8.17.E9]
theorem incompleteBeta_hypergeometric_pfaff {a b : ℝ} (ha : 0 < a) {x : ℝ} (hx1 : x < 1) :
    incompleteBeta a b x=(x : ℂ)^(a : ℂ)*(1-x : ℂ)^((b : ℂ)-1)/a*Gamma
        (a+1)*DLMF.Hypergeometric.regularizedGaussHypergeometric 1 (1-b) (a+1) (x/(x-1)) := by
  have hc : (x:ℂ) ∈ cutPlane := by
    change 1-(x:ℂ) ∈ slitPlane
    left
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have ha0 : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [incompleteBeta, if_neg (by intro h; have h' := congrArg Complex.re h; simp at h'; linarith),
    regularizedGaussHypergeometric_symm a (1-b) (a+1) hc,
    regularizedGaussHypergeometric_pfaff _ _ _ hc,
    show -(1-(b:ℂ))=b-1 by ring,
    show ((a:ℂ)+1)-a=1 by ring,
    regularizedGaussHypergeometric_symm (1-b) 1 (a+1) (div_sub_one_mem_cutPlane hc),
        Gamma_add_one a ha0]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `HasIntegralWholeLine (fun y : ℝ
=> let s : ℂ := c+y*I; s^(-(a : ℂ))*(1-s)^(-(b : ℂ))/(s-x)) (2*π*regularizedIncompleteBeta a b x/((x
: ℂ)^(a : ℂ)*(1-x : ℂ)^(b : ℂ)))`. -/
@[dlmf 8.17.E10]
theorem regularizedIncompleteBeta_mellinBarnes {a b x c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hxc : x < c)
    (hc1 : c < 1) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; s^(-(a : ℂ))*(1-s)^(-(b : ℂ))/(s-x))
        (2*π*regularizedIncompleteBeta a b x/((x : ℂ)^(a : ℂ)*(1-x : ℂ)^(b : ℂ))) := by
  have h := DLMF.Confluent.IncompleteBetaBarnes.integral_vertical ha hb hx hxc hc1
  have hx1 : x < 1 := hxc.trans hc1
  have hc : (x:ℂ) ∈ cutPlane := by
    change 1-(x:ℂ) ∈ slitPlane
    left
    simp only [sub_re, one_re, ofReal_re]
    linarith
  have hbeta : regularizedIncompleteBeta a b x = Gamma ((a:ℂ)+b)/Gamma b *
      (x:ℂ)^(a:ℂ)*(1-x:ℂ)^(b:ℂ) *
      regularizedGaussHypergeometric 1 ((a:ℂ)+b) ((a:ℂ)+1) x := by
    rw [regularizedIncompleteBeta, if_neg (by exact_mod_cast hx1.ne),
      regularizedGaussHypergeometric_euler _ _ _ hc,
      show (a:ℂ)+1-a-(1-b) = b by ring,
      show (a:ℂ)+1-a = 1 by ring,
      show (a:ℂ)+1-(1-b) = a+b by ring]
    ring
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have h1x0 : (1-x:ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hx1).ne'
  have hval : (∫ y : ℝ, let s : ℂ := c+y*I;
      s^(-(a:ℂ))*(1-s)^(-(b:ℂ))/(s-x)) =
      2*π*regularizedIncompleteBeta a b x/((x:ℂ)^(a:ℂ)*(1-x:ℂ)^(b:ℂ)) := by
    rw [h.2, hbeta]
    field_simp [cpow_ne_zero_iff.mpr (Or.inl hx0),
      cpow_ne_zero_iff.mpr (Or.inl h1x0)]
  refine ⟨_, _, intervalIntegral_tendsto_integral_Iic 0 h.1.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi 0 h.1.integrableOn tendsto_id, ?_⟩
  rw [intervalIntegral.integral_Iic_add_Ioi h.1.integrableOn h.1.integrableOn]
  exact hval

/-- The complementary argument x prime. -/
@[dlmf 8.17.E11]
def incBetaComplement (x : ℂ) : ℂ :=
  1-x

/-- The parameter c of the contiguous recurrences. -/
@[dlmf 8.17.E11]
def incBetaContiguousParameter (a b : ℂ) : ℂ :=
  a+b-1

/-- The regularized self-parameter binomial formula on the convergence disk. -/
theorem regularizedGaussHypergeometric_self_disk (a c : ℂ) (hc : ∀ k : ℕ, c≠-k)
    {z : ℂ} (hz : ‖z‖<1) : regularizedGaussHypergeometric a c c z=(1-z)^(-a)/Gamma c := by
  rw [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hz,
    regularizedGaussHypergeometricFun_eq_div_Gamma hc,
    ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k hk => hc k (by linear_combination hk)) hz]

/-- Diagonal incomplete-Beta shift, with reciprocal Gamma retaining exceptional parameters. -/
theorem regularizedIncompleteBeta_shift_diagonal (a b : ℂ) (ha : ∀ k : ℕ, a+1≠-k)
    {z : ℂ} (hz : ‖z‖<1) (hz0 : z≠0) :
    regularizedIncompleteBeta a b z=regularizedIncompleteBeta (a+1) (b-1) z+
      Gamma (a+b)/Gamma b*z^a*(1-z)^(b-1)/Gamma (a+1) := by
  have hz1 : z≠1 := by intro h; simp [h] at hz
  have hcut : z∈cutPlane := mem_cutPlane_of_norm_lt_one hz
  have h := regularizedGaussHypergeometric_contiguous_shift_b (1-b) a (a+1) hcut
  rw [regularizedGaussHypergeometric_symm (1-b) a (a+1) hcut,
    regularizedGaussHypergeometric_self_disk (1-b) (a+1) ha hz,
    regularizedGaussHypergeometric_symm ((1:ℂ)-b+1) (a+1) (a+1+1) hcut] at h
  rw [show (1:ℂ)-b+1=1-(b-1) by ring, show -(1-b)=b-1 by ring,
    show a+1+1=(a+1)+1 by ring] at h
  have hg := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (b-1)
  rw [sub_add_cancel] at hg
  simp only [regularizedIncompleteBeta, if_neg hz1,
    show a+1+(b-1)=a+b by ring, div_eq_mul_inv, hg]
  rw [cpow_add _ _ hz0, cpow_one]
  linear_combination Gamma (a+b)*(Gamma b)⁻¹*z^a*h

/-- Right incomplete-Beta shift on the disk, valid also when the starting b is zero. -/
theorem regularizedIncompleteBeta_shift_right (a b : ℂ) (ha : ∀ k : ℕ, a+1≠-k)
    (hab : a+b≠0) {z : ℂ} (hz : ‖z‖<1) :
    regularizedIncompleteBeta a (b+1) z=regularizedIncompleteBeta a b z+
      Gamma (a+b)/Gamma (b+1)*z^a*(1-z)^b/Gamma a := by
  have hz1 : z≠1 := by intro h; simp [h] at hz
  have hcut : z∈cutPlane := mem_cutPlane_of_norm_lt_one hz
  have h := regularizedGaussHypergeometric_contiguous_a_b_pred a (1-b) (a+1) hcut
  rw [regularizedGaussHypergeometric_symm (a+1) (1-b) (a+1) hcut,
    regularizedGaussHypergeometric_self_disk (1-b) (a+1) ha hz] at h
  rw [show a+1-a-(1-b)=b by ring, show a+1-(1-b)=a+b by ring,
    show (1:ℂ)-b-1=1-(b+1) by ring, show -(1-b)=b-1 by ring] at h
  have hzcomp : 1-z≠0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hp : (1-z)*(1-z)^(b-1)=(1-z)^b := by
    calc
      (1-z)*(1-z)^(b-1)=(1-z)^(1:ℂ)*(1-z)^(b-1) := by rw [cpow_one]
      _ = _ := by rw [← cpow_add _ _ hzcomp]; congr 1; ring
  have hga := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one a
  have hgb := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one b
  simp only [regularizedIncompleteBeta, if_neg hz1,
    show a+(b+1)=(a+b)+1 by ring, Gamma_add_one _ hab, div_eq_mul_inv, hga, hgb]
  have hp' : (1-z)^(b-1)*(1-z)=(1-z)^b := by simpa [mul_comm] using hp
  -- Keep the whole boundary factor together before scalar algebra.
  have h' : (a+b)*regularizedGaussHypergeometric a (1-(b+1)) (a+1) z=
      b*regularizedGaussHypergeometric a (1-b) (a+1) z+a*(1-z)^b/Gamma (a+1) := by
    linear_combination -h+a/Gamma (a+1)*hp
  linear_combination Gamma (a+b)*(Gamma (b+1))⁻¹*z^a*h'

/-- Left incomplete-Beta shift on the disk without imposing positivity on shifted parameters. -/
theorem regularizedIncompleteBeta_shift_left (a b : ℂ) (ha : ∀ k : ℕ, a+1≠-k)
    (hab : a+b≠0) {z : ℂ} (hz : ‖z‖<1) (hz0 : z≠0) :
    regularizedIncompleteBeta (a+1) b z=regularizedIncompleteBeta a b z-
      Gamma (a+b)/Gamma b*z^a*(1-z)^b/Gamma (a+1) := by
  have hd := regularizedIncompleteBeta_shift_diagonal a (b+1) ha hz hz0
  rw [add_sub_cancel_right] at hd
  rw [regularizedIncompleteBeta_shift_right a b ha hab hz,
    show a+(b+1)=(a+b)+1 by ring, Gamma_add_one _ hab] at hd
  have hga := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one a
  have hgb := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one b
  simp only [div_eq_mul_inv, hga,hgb] at hd ⊢
  linear_combination -hd

/-- Four adjacent-parameter formulas; the shifted parameters need not be positive. -/
theorem regularizedIncompleteBeta_neighbors {a b z : ℂ} (ha : 0<a.re) (hb : 0<b.re)
    (hz : ‖z‖<1) (hz0 : z≠0) :
    let D := z^a*(1-z)^b/betaIntegral a b
    regularizedIncompleteBeta (a+1) b z=regularizedIncompleteBeta a b z-D/a ∧
    regularizedIncompleteBeta a (b+1) z=regularizedIncompleteBeta a b z+D/b ∧
    regularizedIncompleteBeta (a+1) (b-1) z=regularizedIncompleteBeta a b z-D/(a*(1-z)) ∧
    regularizedIncompleteBeta (a-1) (b+1) z=regularizedIncompleteBeta a b z+D/(b*z) := by
  dsimp only
  have ha0 := ne_zero_of_re_pos ha
  have hb0 := ne_zero_of_re_pos hb
  have hab : a+b≠0 := ne_zero_of_re_pos (by simp; linarith)
  have ha1 := not_neg_nat_of_re_pos (show 0<(a+1).re by simp; linarith)
  have hB : betaIntegral a b=Gamma a*Gamma b/Gamma (a+b) := by
    apply (eq_div_iff (Gamma_ne_zero_of_re_pos (by simp; linarith))).mpr
    simpa [mul_comm] using (Gamma_mul_Gamma_eq_betaIntegral ha hb).symm
  have hA : Gamma (a+b)/Gamma b/Gamma (a+1)=1/(a*betaIntegral a b) := by
    rw [hB, Gamma_add_one a ha0]
    field_simp
  have hC : Gamma (a+b)/Gamma (b+1)/Gamma a=1/(b*betaIntegral a b) := by
    rw [hB, Gamma_add_one b hb0]
    field_simp
  have hleft := regularizedIncompleteBeta_shift_left a b ha1 hab hz hz0
  have hright := regularizedIncompleteBeta_shift_right a b ha1 hab hz
  have hdiag := regularizedIncompleteBeta_shift_diagonal a b ha1 hz hz0
  have hdiag' := regularizedIncompleteBeta_shift_diagonal (a-1) (b+1)
    (by simpa using not_neg_nat_of_re_pos ha) hz hz0
  rw [sub_add_cancel, add_sub_cancel_right, show a-1+(b+1)=a+b by ring] at hdiag'
  have hz1 : 1-z≠0 := sub_ne_zero.mpr (by intro h; rw [←h] at hz; simp at hz)
  rw [cpow_sub _ _ hz1, cpow_one] at hdiag
  rw [cpow_sub _ _ hz0, cpow_one] at hdiag'
  have eA (u v : ℂ) : Gamma (a+b)/Gamma b*u*v/Gamma (a+1)=u*v/(a*betaIntegral a b) := by
    linear_combination u*v*hA
  have eC (u v : ℂ) : Gamma (a+b)/Gamma (b+1)*u*v/Gamma a=u*v/(b*betaIntegral a b) := by
    linear_combination u*v*hC
  rw [eA] at hleft hdiag
  rw [eC] at hright hdiag'
  refine ⟨?_,?_,?_,?_⟩
  · rw [hleft]; ring
  · rw [hright]; ring
  · rw [hdiag]; field_simp; ring
  · rw [hdiag']; field_simp

/-- Downward neighboring Beta formulas, excluding only the singular whole-expression sum. -/
theorem regularizedIncompleteBeta_neighbors_down {a b z : ℂ} (ha : 0<a.re) (hb : 0<b.re)
    (hab : a+b≠1) (hz : ‖z‖<1) (hz0 : z≠0) :
    let D := z^a*(1-z)^b/betaIntegral a b
    regularizedIncompleteBeta (a-1) b z=regularizedIncompleteBeta a b z+D/((a+b-1)*z) ∧
    regularizedIncompleteBeta a (b-1) z=regularizedIncompleteBeta a b z-D/((a+b-1)*(1-z)) := by
  dsimp only
  have hs0 : a+b-1≠0 := sub_ne_zero.mpr hab
  have hz1 : 1-z≠0 := sub_ne_zero.mpr (by intro h; rw [←h] at hz; simp at hz)
  have ha1 := not_neg_nat_of_re_pos (show 0<(a+1).re by simp; linarith)
  have hl := regularizedIncompleteBeta_shift_left (a-1) b (by simpa using not_neg_nat_of_re_pos ha)
    (by convert hs0 using 1 <;> ring) hz hz0
  have hr := regularizedIncompleteBeta_shift_right a (b-1) ha1 (by convert hs0 using 1 <;> ring) hz
  rw [sub_add_cancel, show a-1+b=a+b-1 by ring] at hl
  rw [sub_add_cancel, show a+(b-1)=a+b-1 by ring] at hr
  have hg := Gamma_add_one (a+b-1) hs0
  rw [sub_add_cancel] at hg
  have hB : betaIntegral a b=Gamma a*Gamma b/Gamma (a+b) := by
    apply (eq_div_iff (Gamma_ne_zero_of_re_pos (by simp; linarith))).mpr
    simpa [mul_comm] using (Gamma_mul_Gamma_eq_betaIntegral ha hb).symm
  have hc : Gamma (a+b-1)/Gamma b/Gamma a=1/((a+b-1)*betaIntegral a b) := by
    rw [hB,hg]
    field_simp
  have he (u v : ℂ) : Gamma (a+b-1)/Gamma b*u*v/Gamma a=
      u*v/((a+b-1)*betaIntegral a b) := by linear_combination u*v*hc
  rw [he,cpow_sub _ _ hz0,cpow_one] at hl
  rw [he,cpow_sub _ _ hz1,cpow_one] at hr
  constructor
  · rw [hl]; field_simp; ring
  · rw [hr]; field_simp; ring

/-- Three downward contiguous identities in a complex neighborhood of positive parameters. -/
theorem regularizedIncompleteBeta_contiguous_complex {a b z : ℂ} (ha : 0<a.re) (hb : 0<b.re)
    (hab : a+b≠1) (hz : ‖z‖<1) (hz0 : z≠0) :
    regularizedIncompleteBeta a b z=z*regularizedIncompleteBeta (a-1) b
        z+(1-z)*regularizedIncompleteBeta a (b-1) z ∧
    a*regularizedIncompleteBeta (a+1) b z=(a+(a+b-1)*z)*regularizedIncompleteBeta a b z-
      (a+b-1)*z*regularizedIncompleteBeta (a-1) b z ∧
    b*regularizedIncompleteBeta a (b+1) z=(b+(a+b-1)*(1-z))*regularizedIncompleteBeta a b z-
      (a+b-1)*(1-z)*regularizedIncompleteBeta a (b-1) z := by
  have hu := regularizedIncompleteBeta_neighbors ha hb hz hz0
  have hd := regularizedIncompleteBeta_neighbors_down ha hb hab hz hz0
  dsimp only at hu hd
  have hs0 : a+b-1≠0 := sub_ne_zero.mpr hab
  have hz1 : 1-z≠0 := sub_ne_zero.mpr (by intro h; rw [←h] at hz; simp at hz)
  have ha0 := ne_zero_of_re_pos ha
  have hb0 := ne_zero_of_re_pos hb
  refine ⟨?_,?_,?_⟩
  · rw [hd.1,hd.2]; field_simp; ring
  · rw [hu.1,hd.1]; field_simp; ring
  · rw [hu.2.1,hd.2]; field_simp; ring

/-- Identity under the stated parameter and domain assumptions:
`regularizedIncompleteBeta (a) (b) x=(x : ℂ)*regularizedIncompleteBeta (a-1) (b) x+(1-x :
ℂ)*regularizedIncompleteBeta (a) (b-1) x`. -/
@[dlmf 8.17.E12]
theorem regularizedIncompleteBeta_contiguous_12 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) (hab : a+b ≠ 1) :
    regularizedIncompleteBeta (a) (b) x=(x : ℂ)*regularizedIncompleteBeta (a-1) (b)
        x+(1-x : ℂ)*regularizedIncompleteBeta (a) (b-1) x := by
  have h := (regularizedIncompleteBeta_contiguous_complex (a:=(a:ℂ)) (b:=(b:ℂ)) ha hb
    (by exact_mod_cast hab) (by simpa [Complex.norm_real, Real.norm_of_nonneg hx.le] using hx1)
    (Complex.ofReal_ne_zero.mpr hx.ne')).1
  push_cast at h ⊢
  exact h

/-- Identity under the stated parameter and domain assumptions:
`((a+b : ℝ) : ℂ)*regularizedIncompleteBeta (a) (b) x=(a : ℂ)*regularizedIncompleteBeta (a+1) (b)
x+(b : ℂ)*regularizedIncompleteBeta (a) (b+1) x`. -/
@[dlmf 8.17.E13]
theorem regularizedIncompleteBeta_contiguous_13 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) :
    ((a+b : ℝ) : ℂ)*regularizedIncompleteBeta (a) (b) x=(a : ℂ)*regularizedIncompleteBeta (a+1) (b)
        x+(b : ℂ)*regularizedIncompleteBeta
        (a) (b+1) x := by
  have ha' : 0 < (a:ℂ).re := ha
  have hb' : 0 < (b:ℂ).re := hb
  have hxx : x ∈ Icc (0:ℝ) 1 := ⟨hx.le,hx1.le⟩
  have hl := Real.regularizedIncompleteBeta_add_one_left ha' hb' hxx
  have hr := Real.regularizedIncompleteBeta_add_one_right ha' hb' hxx
  rw [regularizedIncompleteBeta_ofReal ha' hb' hxx,
    regularizedIncompleteBeta_ofReal (by simpa using (show 0<a+1 by linarith)) hb' hxx,
    regularizedIncompleteBeta_ofReal ha' (by simpa using (show 0<b+1 by linarith)) hxx]
  push_cast
  rw [hl,hr]
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne', Complex.ofReal_ne_zero.mpr hb.ne',
    betaIntegral_ne_zero ha' hb']
  ring

/-- Identity under the stated parameter and domain assumptions:
`((a+b*x : ℝ) : ℂ)*regularizedIncompleteBeta (a) (b) x=(x : ℂ)*b*regularizedIncompleteBeta (a-1)
(b+1) x+(a : ℂ)*regularizedIncompleteBeta (a+1) (b) x`. -/
@[dlmf 8.17.E14]
theorem regularizedIncompleteBeta_contiguous_14 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) :
    ((a+b*x : ℝ) : ℂ)*regularizedIncompleteBeta (a) (b)
        x=(x : ℂ)*b*regularizedIncompleteBeta (a-1) (b+1)
        x+(a : ℂ)*regularizedIncompleteBeta (a+1) (b) x := by
  have h := regularizedIncompleteBeta_neighbors (a:=(a:ℂ)) (b:=(b:ℂ)) (z:=(x:ℂ)) ha hb
    (by simpa [Complex.norm_real, Real.norm_of_nonneg hx.le] using hx1)
    (Complex.ofReal_ne_zero.mpr hx.ne')
  dsimp only at h
  push_cast
  rw [h.2.2.2,h.1]
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne', Complex.ofReal_ne_zero.mpr hb.ne',
      Complex.ofReal_ne_zero.mpr hx.ne']
  ring

/-- Identity under the stated parameter and domain assumptions: `((b+a*(1-x) : ℝ) :
ℂ)*regularizedIncompleteBeta (a) (b) x=(a : ℂ)*(1-x)*regularizedIncompleteBeta (a+1) (b-1) x+(b :
ℂ)*regularizedIncompleteBeta (a) (b+1) x`. -/
@[dlmf 8.17.E15]
theorem regularizedIncompleteBeta_contiguous_15 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) :
    ((b+a*(1-x) : ℝ) : ℂ)*regularizedIncompleteBeta (a) (b)
        x=(a : ℂ)*(1-x)*regularizedIncompleteBeta (a+1) (b-1)
        x+(b : ℂ)*regularizedIncompleteBeta (a) (b+1) x := by
  have h := regularizedIncompleteBeta_neighbors (a:=(a:ℂ)) (b:=(b:ℂ)) (z:=(x:ℂ)) ha hb
    (by simpa [Complex.norm_real, Real.norm_of_nonneg hx.le] using hx1)
    (Complex.ofReal_ne_zero.mpr hx.ne')
  dsimp only at h
  push_cast
  rw [h.2.2.1,h.2.1]
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne', Complex.ofReal_ne_zero.mpr hb.ne',
      show (1:ℂ)-x≠0 by exact_mod_cast (sub_pos.mpr hx1).ne']
  ring

/-- Identity under the stated parameter and domain assumptions:
`(a : ℂ)*regularizedIncompleteBeta (a+1) (b) x=((a : ℂ)+(a+b-1)*x)*regularizedIncompleteBeta (a) (b)
x-((a+b-1 : ℝ) : ℂ)*x*regularizedIncompleteBeta (a-1) (b) x`. -/
@[dlmf 8.17.E16]
theorem regularizedIncompleteBeta_contiguous_16 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) (hab : a+b ≠ 1) :
    (a : ℂ)*regularizedIncompleteBeta (a+1) (b)
        x=((a : ℂ)+(a+b-1)*x)*regularizedIncompleteBeta (a) (b)
        x-((a+b-1 : ℝ) : ℂ)*x*regularizedIncompleteBeta (a-1) (b) x := by
  have h := (regularizedIncompleteBeta_contiguous_complex (a:=(a:ℂ)) (b:=(b:ℂ)) ha hb
    (by exact_mod_cast hab) (by simpa [Complex.norm_real, Real.norm_of_nonneg hx.le] using hx1)
    (Complex.ofReal_ne_zero.mpr hx.ne')).2.1
  push_cast at h ⊢
  exact h

/-- Identity under the stated parameter and domain assumptions:
`(b : ℂ)*regularizedIncompleteBeta (a) (b+1) x=((b : ℂ)+(a+b-1)*(1-x))*regularizedIncompleteBeta (a)
(b) x-((a+b-1 : ℝ) : ℂ)*(1-x)*regularizedIncompleteBeta (a) (b-1) x`. -/
@[dlmf 8.17.E17]
theorem regularizedIncompleteBeta_contiguous_17 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) (hab : a+b ≠ 1) :
    (b : ℂ)*regularizedIncompleteBeta (a) (b+1)
        x=((b : ℂ)+(a+b-1)*(1-x))*regularizedIncompleteBeta (a) (b)
        x-((a+b-1 : ℝ) : ℂ)*(1-x)*regularizedIncompleteBeta (a) (b-1) x := by
  have h := (regularizedIncompleteBeta_contiguous_complex (a:=(a:ℂ)) (b:=(b:ℂ)) ha hb
    (by exact_mod_cast hab) (by simpa [Complex.norm_real, Real.norm_of_nonneg hx.le] using hx1)
    (Complex.ofReal_ne_zero.mpr hx.ne')).2.2
  push_cast at h ⊢
  exact h

/-- Identity under the stated parameter and domain assumptions: `regularizedIncompleteBeta (a) (b)
x=regularizedIncompleteBeta (a+1) (b-1) x+(x : ℂ)^(a : ℂ)*(1-x : ℂ)^((b : ℂ)-1)/(a*betaIntegral a
b)`. -/
@[dlmf 8.17.E18]
theorem regularizedIncompleteBeta_contiguous_18 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) :
    regularizedIncompleteBeta (a) (b) x=regularizedIncompleteBeta (a+1) (b-1)
        x+(x : ℂ)^(a : ℂ)*(1-x : ℂ)^((b : ℂ)-1)/(a*betaIntegral a b) := by
  have h := regularizedIncompleteBeta_neighbors (a:=(a:ℂ)) (b:=(b:ℂ)) (z:=(x:ℂ)) ha hb
    (by simpa [Complex.norm_real, Real.norm_of_nonneg hx.le] using hx1)
    (Complex.ofReal_ne_zero.mpr hx.ne')
  dsimp only at h
  rw [h.2.2.1, cpow_sub _ _ (show (1:ℂ)-x≠0 by exact_mod_cast (sub_pos.mpr hx1).ne'), cpow_one]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `regularizedIncompleteBeta (a) (b)
x=regularizedIncompleteBeta (a-1) (b+1) x-(x : ℂ)^((a : ℂ)-1)*(1-x : ℂ)^(b : ℂ)/(b*betaIntegral a
b)`. -/
@[dlmf 8.17.E19]
theorem regularizedIncompleteBeta_contiguous_19 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) :
    regularizedIncompleteBeta (a) (b) x=regularizedIncompleteBeta (a-1) (b+1)
        x-(x : ℂ)^((a : ℂ)-1)*(1-x : ℂ)^(b : ℂ)/(b*betaIntegral a b) := by
  have h := regularizedIncompleteBeta_neighbors (a:=(a:ℂ)) (b:=(b:ℂ)) (z:=(x:ℂ)) ha hb
    (by simpa [Complex.norm_real, Real.norm_of_nonneg hx.le] using hx1)
    (Complex.ofReal_ne_zero.mpr hx.ne')
  dsimp only at h
  rw [h.2.2.2, cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), cpow_one]
  field_simp
  ring

/-- Continuity in the unshifted Beta parameter, on the unit disk and in the positive half-planes. -/
theorem continuousAt_regularizedIncompleteBeta_left {a b z : ℂ} (ha : 0<a.re) (hb : 0<b.re)
    (hz : ‖z‖<1) (hz0 : z≠0) : ContinuousAt (fun w => regularizedIncompleteBeta w b z) a := by
  have hz1 : z≠1 := by intro h; simp [h] at hz
  have he : (fun w => regularizedIncompleteBeta w b z)=(fun w => Gamma (w+b)/Gamma b*z^w*
      regularizedGaussHGFun w (1-b) (w+1) z) := by
    funext w
    rw [regularizedIncompleteBeta, if_neg hz1,
        regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hz]
  rw [he]
  have hG := (continuousAt_Gamma (a+b) (not_neg_nat_of_re_pos (add_pos ha hb))).comp_of_eq
    (continuousAt_id.add_const b : ContinuousAt (fun w : ℂ=>w+b) a) rfl
  have hP : ContinuousAt (fun w : ℂ => z^w) a := by
    simp_rw [cpow_def_of_ne_zero hz0]
    fun_prop
  have hF := ((analyticOnNhd_regularizedGaussHypergeometricFun_comp
    (A:=id) (B:=fun _ => 1-b) (C:=fun w=>w+1) (by fun_prop) (by fun_prop) (by fun_prop) hz) a
        (mem_univ _)).continuousAt
  exact ((hG.div_const (Gamma b)).mul hP).mul hF

/-- Along a punctured perturbation, the three contiguous whole expressions agree with unshifted
values. -/
theorem eventually_regularizedIncompleteBeta_contiguous {a b z : ℂ} (ha : 0<a.re) (hb : 0<b.re)
    (hz : ‖z‖<1) (hz0 : z≠0) :
    ∀ᶠ ε : ℂ in 𝓝[≠] 0,
      regularizedIncompleteBeta (a+ε) b z=z*regularizedIncompleteBeta (a+ε-1) b
          z+(1-z)*regularizedIncompleteBeta (a+ε) (b-1) z ∧
      (a+ε)*regularizedIncompleteBeta (a+ε+1) b
          z=(a+ε+(a+ε+b-1)*z)*regularizedIncompleteBeta (a+ε) b z-
        (a+ε+b-1)*z*regularizedIncompleteBeta (a+ε-1) b z ∧
      b*regularizedIncompleteBeta (a+ε) (b+1)
          z=(b+(a+ε+b-1)*(1-z))*regularizedIncompleteBeta (a+ε) b z-
        (a+ε+b-1)*(1-z)*regularizedIncompleteBeta (a+ε) (b-1) z := by
  have hp : ∀ᶠ ε : ℂ in 𝓝 0, 0<(a+ε).re :=
    (isOpen_lt continuous_const (by fun_prop : Continuous (fun ε : ℂ => (a+ε).re))).mem_nhds
        (by simpa using ha)
  have hsum : ∀ᶠ ε : ℂ in 𝓝[≠] 0, a+ε+b≠1 := by
    by_cases h : a+b=1
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε≠0 := hε
      intro he
      apply hε0
      linear_combination he-h
    · have hn : ∀ᶠ ε : ℂ in 𝓝 0, a+ε+b≠1 :=
        (isOpen_ne.preimage (by fun_prop : Continuous (fun ε : ℂ=>a+ε+b))).mem_nhds
          (by simpa using h)
      exact hn.filter_mono nhdsWithin_le_nhds
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds,hsum] with ε hε hs
  exact regularizedIncompleteBeta_contiguous_complex hε hb hs hz hz0

/-- Limiting interpretation at the otherwise singular a+b=1 recurrence. -/
@[dlmf 8.17.E12]
theorem regularizedIncompleteBeta_contiguous_limit_12 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) :
    Tendsto (fun ε : ℂ =>
        (x : ℂ)*regularizedIncompleteBeta (((a : ℂ)+ε)-1) (b) x+(1-x : ℂ)*regularizedIncompleteBeta
            (((a : ℂ)+ε)) (b-1) x)
        (𝓝[≠] 0) (𝓝 (regularizedIncompleteBeta (a) (b) x)) := by
  have hnorm : ‖(x:ℂ)‖<1 := by simpa [Complex.norm_real, Real.norm_of_nonneg hx.le] using hx1
  have hx0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have he := eventually_regularizedIncompleteBeta_contiguous (a:=(a:ℂ)) (b:=(b:ℂ)) ha hb hnorm hx0
  have hc := (continuousAt_regularizedIncompleteBeta_left (a:=(a:ℂ)) (b:=(b:ℂ)) ha hb hnorm
      hx0).comp_of_eq
    (continuousAt_const.add continuousAt_id : ContinuousAt (fun ε:ℂ=>(a:ℂ)+ε) 0) (by simp)
  have ht : Tendsto (fun ε:ℂ=>regularizedIncompleteBeta ((a:ℂ)+ε) b x) (𝓝[≠] 0)
      (𝓝 (regularizedIncompleteBeta a b x)) := by
    convert hc.tendsto.mono_left (nhdsWithin_le_nhds : (𝓝[≠] (0:ℂ))≤𝓝 0) using 1 <;>
      first | (funext ε; rfl) | simp [Function.comp_apply,Pi.add_apply,Pi.mul_apply,id_eq]
  apply ht.congr'
  filter_upwards [he] with ε hε
  exact hε.1

/-- Limiting interpretation at the otherwise singular a+b=1 recurrence. -/
@[dlmf 8.17.E16]
theorem regularizedIncompleteBeta_contiguous_limit_16 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) :
    Tendsto (fun ε : ℂ =>
        ((((a : ℂ)+ε) : ℂ)+(((a : ℂ)+ε)+b-1)*x)*regularizedIncompleteBeta (((a : ℂ)+ε)) (b)
        x-((((a : ℂ)+ε)+b-1 : ℂ) : ℂ)*x*regularizedIncompleteBeta (((a : ℂ)+ε)-1) (b) x) (𝓝[≠] 0)
        (𝓝 ((a : ℂ)*regularizedIncompleteBeta (a+1) (b) x)) := by
  have hnorm : ‖(x:ℂ)‖<1 := by simpa [Complex.norm_real, Real.norm_of_nonneg hx.le] using hx1
  have hx0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have he := eventually_regularizedIncompleteBeta_contiguous (a:=(a:ℂ)) (b:=(b:ℂ)) ha hb hnorm hx0
  have hc := (continuousAt_regularizedIncompleteBeta_left (a:=((a:ℂ)+1)) (b:=(b:ℂ))
    (by simp; linarith) hb hnorm hx0).comp_of_eq
    (by fun_prop : ContinuousAt (fun ε:ℂ=>(a:ℂ)+ε+1) 0) (by simp)
  have hv := (continuousAt_const.add continuousAt_id : ContinuousAt (fun ε:ℂ=>(a:ℂ)+ε) 0).mul hc
  have ht : Tendsto (fun ε:ℂ=>((a:ℂ)+ε)*regularizedIncompleteBeta ((a:ℂ)+ε+1) b x) (𝓝[≠] 0)
      (𝓝 ((a:ℂ)*regularizedIncompleteBeta ((a:ℂ)+1) b x)) := by
    convert hv.tendsto.mono_left (nhdsWithin_le_nhds : (𝓝[≠] (0:ℂ))≤𝓝 0) using 1 <;>
      first | (funext ε; rfl) | simp [Function.comp_apply,Pi.add_apply,Pi.mul_apply,id_eq]
  apply ht.congr'
  filter_upwards [he] with ε hε
  exact hε.2.1

/-- Limiting interpretation at the otherwise singular a+b=1 recurrence. -/
@[dlmf 8.17.E17]
theorem regularizedIncompleteBeta_contiguous_limit_17 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) :
    Tendsto (fun ε : ℂ =>
        ((b : ℂ)+(((a : ℂ)+ε)+b-1)*(1-x))*regularizedIncompleteBeta (((a : ℂ)+ε)) (b)
        x-((((a : ℂ)+ε)+b-1 : ℂ) : ℂ)*(1-x)*regularizedIncompleteBeta (((a : ℂ)+ε))
            (b-1) x) (𝓝[≠] 0)
        (𝓝 ((b : ℂ)*regularizedIncompleteBeta (a) (b+1) x)) := by
  have hnorm : ‖(x:ℂ)‖<1 := by simpa [Complex.norm_real, Real.norm_of_nonneg hx.le] using hx1
  have hx0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have he := eventually_regularizedIncompleteBeta_contiguous (a:=(a:ℂ)) (b:=(b:ℂ)) ha hb hnorm hx0
  have hc := (continuousAt_regularizedIncompleteBeta_left (a:=(a:ℂ)) (b:=((b:ℂ)+1)) ha
      (by simp; linarith) hnorm
      hx0).comp_of_eq
    (continuousAt_const.add continuousAt_id : ContinuousAt (fun ε:ℂ=>(a:ℂ)+ε) 0) (by simp)
  have hv := hc.const_mul (b:ℂ)
  have ht : Tendsto (fun ε:ℂ=>(b:ℂ)*regularizedIncompleteBeta ((a:ℂ)+ε) ((b:ℂ)+1) x) (𝓝[≠] 0)
      (𝓝 ((b:ℂ)*regularizedIncompleteBeta a ((b:ℂ)+1) x)) := by
    convert hv.tendsto.mono_left (nhdsWithin_le_nhds : (𝓝[≠] (0:ℂ))≤𝓝 0) using 1 <;>
      first | (funext ε; rfl) | simp [Function.comp_apply,Pi.add_apply,Pi.mul_apply,id_eq]
  apply ht.congr'
  filter_upwards [he] with ε hε
  exact hε.2.2

/-- The Gauss continued-fraction numerators d_k. -/
@[dlmf 8.17.E23]
def incBetaFractionD (a b x : ℝ) (k : ℕ) : ℂ :=
  if Even k then let m : ℂ := (k/2 : ℕ); m*(b-m)*x/((a+2*m-1)*(a+2*m)) else
      let m : ℂ := ((k-1)/2 : ℕ); -(a+m)*(a+b+m)*x/((a+2*m)*(a+2*m+1))

/-- The N-level scaled continued fraction; N=1 is the initial prefactor. -/
def incBetaFractionConvergent (a b x : ℝ) (N : ℕ) : ℂ :=
  (x : ℂ)^(a : ℂ)*(1-x : ℂ)^(b : ℂ)/(a*betaIntegral a b)*continuedFractionTail
      (fun k => if k=0 then 1 else incBetaFractionD a b x k) (fun _ => 1) 0 N

/-- The numerators `d_k` are real. -/
private theorem incBetaFractionD_eq (a b x : ℝ) (k : ℕ) :
    incBetaFractionD a b x k =
      ((DLMF.Confluent.IncompleteBetaFraction.partialNumerator a b x k : ℝ) : ℂ) := by
  simp only [incBetaFractionD, DLMF.Confluent.IncompleteBetaFraction.partialNumerator]
  split_ifs <;> push_cast <;> rfl

/-- `I_x(a,b)` is the prefactor times the backward solution `W₁ = F(a+b, 1; a+1; x)`. -/
private theorem regularizedIncompleteBeta_eq_solution {a b x : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hx : 0 ≤ x)
    (hx1 : x < 1) :
    regularizedIncompleteBeta a b x = (x : ℂ)^(a : ℂ)*(1-x : ℂ)^(b : ℂ)/(a*betaIntegral a b) *
      ((DLMF.Confluent.IncompleteBetaFraction.solution a b x 1 : ℝ) : ℂ) := by
  have hGa := Gamma_ne_zero_of_re_pos (show 0 < (a : ℂ).re by simpa using ha)
  have hGb := Gamma_ne_zero_of_re_pos (show 0 < (b : ℂ).re by simpa using hb)
  have hGab := Gamma_ne_zero_of_re_pos (show 0 < ((a : ℂ)+b).re by simp; linarith)
  have hB : betaIntegral a b=Gamma a*Gamma b/Gamma (a+b) := by
    apply (eq_div_iff hGab).mpr
    simpa [mul_comm] using (Gamma_mul_Gamma_eq_betaIntegral
      (show 0 < (a : ℂ).re by simpa using ha) (show 0 < (b : ℂ).re by simpa using hb)).symm
  have hx1' : (x : ℂ) ≠ 1 := by exact_mod_cast hx1.ne
  have hE := incompleteBeta_hypergeometric_euler (b := b) ha hx1
  have hW : ((DLMF.Confluent.IncompleteBetaFraction.solution a b x 1 : ℝ) : ℂ) =
      Gamma (a+1) * regularizedGaussHypergeometric (a+b) 1 (a+1) x := by
    rw [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _
      (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]; exact hx1)]
    have := GaussContinuedFraction.ofReal (a + b) 1 (a + 1) x
    simp only [DLMF.Confluent.IncompleteBetaFraction.solution,
      GaussContinuedFraction.backwardSolutionReal]
    push_cast
    norm_num
    rw [← Complex.Gamma_ofReal]
    push_cast at this
    rw [this]
    push_cast
    rfl
  have hI : regularizedIncompleteBeta a b x = Gamma (a+b)/(Gamma a*Gamma b) *
      incompleteBeta a b x := by
    simp only [regularizedIncompleteBeta, incompleteBeta, hx1', ↓reduceIte]
    field_simp
  rw [hI, hE, hW, hB]
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp

/-- The map `(incBetaFractionConvergent a b x)` tends to `(𝓝 (regularizedIncompleteBeta a b x))`
along `atTop`.
-/
@[dlmf 8.17.E22]
theorem incompleteBeta_continuedFraction {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x)
    (hx1 : x < 1) :
    Tendsto (incBetaFractionConvergent a b x) atTop (𝓝 (regularizedIncompleteBeta a b x)) := by
  have hf : (fun k => if k=0 then 1 else incBetaFractionD a b x k) =
      fun k => ((DLMF.Confluent.IncompleteBetaFraction.fractionNumerator a b x k : ℝ) : ℂ) := by
    funext k
    by_cases hk : k = 0 <;>
      simp [hk, DLMF.Confluent.IncompleteBetaFraction.fractionNumerator, incBetaFractionD_eq]
  rw [regularizedIncompleteBeta_eq_solution ha hb hx hx1]
  unfold incBetaFractionConvergent
  rw [hf]
  exact (DLMF.Confluent.IncompleteBetaFraction.tendsto_continuedFractionTail ha hb hx
      hx1).const_mul _


/-- The map `(fun x : ℝ => regularizedIncompleteBeta a b x)` tends to `(𝓝 1)` along `(𝓝[<] 1)`. -/
@[dlmf 8.17.E22]
theorem incompleteBeta_continuedFraction_endpoint_limit {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x : ℝ => regularizedIncompleteBeta a b x) (𝓝[<] 1) (𝓝 1) := by
  have hc := (Complex.continuous_ofReal.comp
    (TauCeti.continuous_regularizedIncompleteBeta ha hb)).continuousAt (x:=1) |>.tendsto
  have he : (fun x : ℝ => regularizedIncompleteBeta a b x)=ᶠ[𝓝[<] (1:ℝ)]
      (fun x => (TauCeti.regularizedIncompleteBeta a b x:ℂ)) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ)<1 by norm_num)] with x hx
    rw [regularizedIncompleteBeta_ofReal ha hb ⟨hx.1.le,hx.2.le⟩,
      Real.regularizedIncompleteBeta_ofReal ha hb ⟨hx.1.le,hx.2.le⟩]
  simpa only [Function.comp_apply,
      TauCeti.regularizedIncompleteBeta_eq_one_of_one_le ha.le hb le_rfl,
      Complex.ofReal_one] using (hc.mono_left nhdsWithin_le_nhds).congr' he.symm

/-- Counterexample to the unqualified upper-convergent claim following 8.17.23: the second
convergent is sqrt(2)/5. -/
theorem incompleteBeta_cf_upper_bound_counterexample  :
    (Real.regularizedIncompleteBeta 1 (1/2) (1/2)).re > Real.sqrt 2/5 := by
  have h := Real.regularizedIncompleteBeta_symm (a := 1) (b := 1/2) (x := 1/2)
    (by norm_num) (by norm_num) (by norm_num)
  rw [Real.regularizedIncompleteBeta_one_right (by norm_num)] at h
  norm_num at h
  have hs : Real.sqrt (1/2) = Real.sqrt 2/2 := by
    have h1 := Real.sq_sqrt (by norm_num : 0 ≤ (1/2 : ℝ))
    have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    nlinarith [Real.sqrt_nonneg (1/2), Real.sqrt_nonneg 2]
  have hp : ((1/2 : ℂ)^(1/2 : ℂ)).re=Real.sqrt 2/2 := by
    have hh := Complex.ofReal_cpow (by norm_num : 0 ≤ (1/2 : ℝ)) (1/2)
    rw [← Real.sqrt_eq_rpow, hs] at hh
    simpa using congrArg Complex.re hh.symm
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, hp] at hr
  have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
  nlinarith [Real.sqrt_nonneg 2]

/-- Exact value of the second continued-fraction convergent in the counterexample. -/
theorem incompleteBeta_cf_second_counterexample_value  :
    incBetaFractionConvergent 1 (1/2) (1/2) 2=(Real.sqrt 2/5 : ℝ) := by
  have hb : betaIntegral (1 : ℂ) (1/2)=2 := by
    rw [betaIntegral_symm (1/2) 1, betaIntegral_eval_one_right (by norm_num)]
    norm_num
  have hs : Real.sqrt (1/2) = Real.sqrt 2/2 := by
    have h1 := Real.sq_sqrt (by norm_num : 0 ≤ (1/2 : ℝ))
    have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    nlinarith [Real.sqrt_nonneg (1/2), Real.sqrt_nonneg 2]
  have hp : (1/2 : ℂ)^(1/2 : ℂ)=(Real.sqrt 2/2 : ℝ) := by
    have hh := Complex.ofReal_cpow (by norm_num : 0 ≤ (1/2 : ℝ)) (1/2)
    rw [← Real.sqrt_eq_rpow, hs] at hh
    simpa using hh.symm
  norm_num [incBetaFractionConvergent, continuedFractionTail, continuedFractionContinuants,
      GenContFract.nextConts,
      GenContFract.nextNum, GenContFract.nextDen, incBetaFractionD, hb, hp]
  push_cast
  ring

/-- The series with terms `(fun j : ℕ => if m ≤ j then (1-x : ℂ)^n*((n+j-1).choose j : ℂ)*(x :
ℂ)^j else 0)` converges to `(regularizedIncompleteBeta m n x)`. -/
@[dlmf 8.17.E24]
theorem regularizedIncompleteBeta_negative_binomial_sum {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {x : ℝ} (hx : 0 ≤ x)
    (hx1 : x < 1) :
    HasSum (fun j : ℕ => if m ≤ j then (1-x : ℂ)^n*((n+j-1).choose j : ℂ)*(x : ℂ)^j else 0)
        (regularizedIncompleteBeta m n x) := by
  have hmpos : 0<(m:ℂ).re := by exact_mod_cast hm
  have hnpos : 0<(n:ℂ).re := by exact_mod_cast hn
  have hz : ‖(x:ℂ)‖<1 := by simpa [Complex.norm_real,Real.norm_of_nonneg hx] using hx1
  have hxne1 : (x:ℂ)≠1 := by exact_mod_cast hx1.ne
  have hcut := mem_cutPlane_of_norm_lt_one hz
  have hE : regularizedIncompleteBeta m n x=
      (Gamma ((m:ℂ)+n)/Gamma n*(x:ℂ)^m*(1-x:ℂ)^n)*
        regularizedGaussHGFun 1 ((m:ℂ)+n) ((m:ℂ)+1) x := by
    rw [regularizedIncompleteBeta,if_neg hxne1,regularizedGaussHypergeometric_euler _ _ _ hcut]
    rw [show (m:ℂ)+1-m-(1-n)=n by ring,show (m:ℂ)+1-m=1 by ring,
      show (m:ℂ)+1-(1-n)=m+n by ring,
      regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hz,
          cpow_natCast, cpow_natCast]
    ring
  have hs := (summable_regularizedGaussHypergeometricFun_term 1 ((m:ℂ)+n) ((m:ℂ)+1) hz).hasSum
  rw [← regularizedGaussHypergeometricFun_eq_tsum] at hs
  have ht := hs.mul_left (Gamma ((m:ℂ)+n)/Gamma n*(x:ℂ)^m*(1-x:ℂ)^n)
  rw [← hE] at ht
  have hcoeff (k : ℕ) : Gamma ((m:ℂ)+n)/Gamma n*
      (pochhammer ((m:ℂ)+n) k/Gamma ((m:ℂ)+1+k))=
      ((n+(k+m)-1).choose (k+m):ℂ) := by
    have hGmn := Gamma_ne_zero_of_re_pos (show 0<((m:ℂ)+n).re by exact add_pos hmpos hnpos)
    have hp := Gamma_add_nat_div_Gamma_eq (n:=k) ((m:ℂ)+n)
      (not_neg_nat_of_re_pos (add_pos hmpos hnpos))
    rw [← pochhammer] at hp
    have hgm : Gamma ((m:ℂ)+1+k)=((m+k).factorial:ℂ) := by
      rw [show (m:ℂ)+1+k=((m+k:ℕ):ℂ)+1 by push_cast; ring,Gamma_nat_eq_factorial]
    have hgn : Gamma (n:ℂ)=((n-1).factorial:ℂ) := by
      rw [show (n:ℂ)=((n-1:ℕ):ℂ)+1 by rw [Nat.cast_sub (by omega)]; norm_num,
        Gamma_nat_eq_factorial]
    have hgt : Gamma ((m:ℂ)+n+k)=((n+(k+m)-1).factorial:ℂ) := by
      rw [show (m:ℂ)+n+k=((n+(k+m)-1:ℕ):ℂ)+1 by
        rw [Nat.cast_sub (by omega)]; push_cast; ring,Gamma_nat_eq_factorial]
    rw [← hp,hgm,hgn,hgt]
    have hc := Nat.choose_mul_factorial_mul_factorial (show k+m≤n+(k+m)-1 by omega)
    have hc' : (((n+(k+m)-1).choose (k+m):ℂ))*((k+m).factorial:ℂ)*((n-1).factorial:ℂ)=
        ((n+(k+m)-1).factorial:ℂ) := by
      exact_mod_cast (by simpa [show n+(k+m)-1-(k+m)=n-1 by omega] using hc)
    rw [Nat.add_comm m k]
    field_simp [hGmn, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n-1)),
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k+m))]
    linear_combination -hc'
  let F : ℕ → ℂ := fun j => if m≤j then (1-x:ℂ)^n*((n+j-1).choose j:ℂ)*(x:ℂ)^j else 0
  have htail : HasSum (fun k => F (k+m)) (regularizedIncompleteBeta m n x) := by
    refine ht.congr_fun fun k => ?_
    dsimp [F]
    rw [if_pos (by omega),pow_add]
    change _ = Gamma ((m:ℂ)+n)/Gamma n*(x:ℂ)^m*(1-x:ℂ)^n*
      (pochhammer 1 k*pochhammer ((m:ℂ)+n) k*(x:ℂ)^k/(k.factorial:ℂ)*(Gamma ((m:ℂ)+1+k))⁻¹)
    rw [pochhammer_nat_one]
    have hf : (k.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    symm
    calc
      _ = ((x:ℂ)^k*(x:ℂ)^m*(1-x:ℂ)^n)*
          (Gamma ((m:ℂ)+n)/Gamma n*(pochhammer ((m:ℂ)+n) k/Gamma ((m:ℂ)+1+k))) := by field_simp [hf]
      _ = _ := by rw [hcoeff]; ring
  have hzero : ∑ j ∈ Finset.range m, F j=0 := Finset.sum_eq_zero fun j hj => by
    simp only [F,if_neg (show ¬m≤j by have := Finset.mem_range.mp hj; omega)]
  apply (hasSum_nat_add_iff' (f:=F) m).mp
  rw [hzero,sub_zero]
  exact htail

/-- The three-level convergent is also below I, independently of the indexing convention. -/
theorem incompleteBeta_cf_third_bound_counterexample  :
    (Real.regularizedIncompleteBeta 1 (1/2) (1/2)).re > 23*Real.sqrt 2/112 := by
  have h := Real.regularizedIncompleteBeta_symm (a := 1) (b := 1/2) (x := 1/2)
    (by norm_num) (by norm_num) (by norm_num)
  rw [Real.regularizedIncompleteBeta_one_right (by norm_num)] at h
  norm_num at h
  have hs : Real.sqrt (1/2) = Real.sqrt 2/2 := by
    have h1 := Real.sq_sqrt (by norm_num : 0 ≤ (1/2 : ℝ))
    have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    nlinarith [Real.sqrt_nonneg (1/2), Real.sqrt_nonneg 2]
  have hp : ((1/2 : ℂ)^(1/2 : ℂ)).re=Real.sqrt 2/2 := by
    have hh := Complex.ofReal_cpow (by norm_num : 0 ≤ (1/2 : ℝ)) (1/2)
    rw [← Real.sqrt_eq_rpow, hs] at hh
    simpa using congrArg Complex.re hh.symm
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, hp] at hr
  have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
  nlinarith [Real.sqrt_nonneg 2]

/-- Exact value of the three-level convergent used for the alternative indexing convention. -/
theorem incompleteBeta_cf_third_counterexample_value  :
    incBetaFractionConvergent 1 (1/2) (1/2) 3=(23*Real.sqrt 2/112 : ℝ) := by
  have hb : betaIntegral (1 : ℂ) (1/2)=2 := by
    rw [betaIntegral_symm (1/2) 1, betaIntegral_eval_one_right (by norm_num)]
    norm_num
  have hs : Real.sqrt (1/2) = Real.sqrt 2/2 := by
    have h1 := Real.sq_sqrt (by norm_num : 0 ≤ (1/2 : ℝ))
    have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    nlinarith [Real.sqrt_nonneg (1/2), Real.sqrt_nonneg 2]
  have hp : (1/2 : ℂ)^(1/2 : ℂ)=(Real.sqrt 2/2 : ℝ) := by
    have hh := Complex.ofReal_cpow (by norm_num : 0 ≤ (1/2 : ℝ)) (1/2)
    rw [← Real.sqrt_eq_rpow, hs] at hh
    simpa using hh.symm
  norm_num [incBetaFractionConvergent, continuedFractionTail, continuedFractionContinuants,
      GenContFract.nextConts,
      GenContFract.nextNum, GenContFract.nextDen, incBetaFractionD, hb, hp]
  push_cast
  ring

end DLMF.Statistical
