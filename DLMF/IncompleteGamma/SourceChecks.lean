/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.BetaEndpointBounds

public import DLMF.IncompleteGamma.RealIntegrals
public import DLMF.IncompleteGamma.BetaAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import DLMF.OrthogonalPolynomials.Basic.Classical

/-!
# Source checks for incomplete Gamma and Beta formulas

The Laguerre expansion in DLMF 8.7.6 uses the polynomial continuation in its parameter.
The totalized hypergeometric realization `laguerrePolynomialL` instead vanishes in every
positive degree at parameter `-1`. Its series at argument `1` therefore sums to `exp(-1)`,
which differs from `Γ(-1, 1)` by the positive number `Γ(0, 1)`.

These results identify the exceptional-parameter obstruction to using that realization in
DLMF 8.7.6 under the sole hypothesis `Re a < 1/2`. The definition `laguerreExtended` supplies
the polynomial continuation at such parameters.

The counterexample uses the upper-Gamma recurrence, positivity of its real integral, and the
Laguerre definition directly; it does not use the Laguerre expansion of the incomplete Gamma
function.

The formulation of DLMF 8.18.3 with comparison function `a⁻ᴺ F₀(a,b,ξ)` uniformly
for every `0 < x ≤ 1` fails already for `b = 1/2` and `N = 0`.
The Gamma-normalized incomplete Beta integral is at least `xᵃ/(a Γ(1/2))`, whereas
`F₀(a,1/2,ξ) ≤ ξ⁻¹ᐟ² exp(-aξ)/(a Γ(1/2))`. At `x = exp(-ξ)` their ratio is therefore
at least `√ξ`, which is unbounded as `x` approaches zero. The proof uses exact real integral
bounds and is independent of the uniform asymptotic estimate.
-/

@[expose] public noncomputable section

open Complex DLMF.Hypergeometric DLMF.OrthogonalPolynomials

namespace DLMF.Confluent.LaguerreSeries

/-- The totalized hypergeometric Laguerre realization vanishes in positive degree at `α = -1`. -/
theorem laguerrePolynomialL_neg_one_succ (n : ℕ) (x : ℂ) :
    laguerrePolynomialL (-1) (n + 1) x = 0 := by
  simp [laguerrePolynomialL]

/-- At `a = -1` and `x = 1`, the Laguerre quotient series sums to `exp(-1)`. -/
theorem hasSum_laguerrePolynomialL_neg_one_one :
    HasSum (fun n : ℕ => (1 : ℂ)^(-1 : ℂ) * exp (-1) *
      laguerrePolynomialL (-1) n 1 / (n + 1)) (exp (-1)) := by
  convert hasSum_single (f := fun n : ℕ => (1 : ℂ)^(-1 : ℂ) * exp (-1) *
      laguerrePolynomialL (-1) n 1 / (n + 1)) 0 (fun n hn => ?_) using 1
  · simp [laguerrePolynomialL_zero]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [laguerrePolynomialL_neg_one_succ]

/-- The upper-Gamma recurrence and `Γ(0, 1) > 0` imply `Γ(-1, 1) ≠ exp(-1)`. -/
theorem upperIncompleteGamma_neg_one_one_ne_exp_neg_one :
    upperIncompleteGamma (-1) 1 ≠ exp (-1) := by
  have hp : 0 < (upperIncompleteGamma 0 1).re :=
    IncompleteGammaRealIntegrals.upperIncompleteGamma_re_pos (a := 0) (by norm_num)
      (IncompleteGammaRealIntegrals.integrableOn_rpow_exp_of_le_one (by norm_num)
        (by norm_num))
  have hr := upperIncompleteGamma_add_one (-1) (z := 1) one_ne_zero
  norm_num at hr
  intro he
  rw [he] at hr
  have hz : upperIncompleteGamma 0 1 = 0 := by linear_combination hr
  rw [hz] at hp
  simp at hp

/-- A counterexample to the Laguerre quotient version of DLMF 8.7.6: `a = -1`, `x = 1`
satisfy `Re a < 1/2` and `x > 0`, but the series does not sum to `Γ(a, x)`. -/
theorem not_hasSum_laguerrePolynomialL_neg_one_one :
    ¬ HasSum (fun n : ℕ => (1 : ℂ)^(-1 : ℂ) * exp (-1) *
      laguerrePolynomialL (-1) n 1 / (n + 1)) (upperIncompleteGamma (-1) 1) := by
  intro hs
  exact upperIncompleteGamma_neg_one_one_ne_exp_neg_one
    (hs.unique hasSum_laguerrePolynomialL_neg_one_one)

end DLMF.Confluent.LaguerreSeries

namespace DLMF.Confluent.BetaUniformEndpoint

open Filter Set MeasureTheory Asymptotics DLMF.Statistical
open scoped Topology

/-- The Gamma-normalized incomplete Beta function with `b = 1/2` is a real integral divided
by `Γ(1/2)` for positive real `a` and `0 ≤ x ≤ 1`. -/
lemma normalizedIncompleteBeta_eq_integral {a x : ℝ} (ha : 0 < a) (hx : x ∈ Icc (0:ℝ) 1) :
    Gamma a/Gamma (a+(1/2:ℝ))*regularizedIncompleteBeta a (1/2) x =
      (((∫ t in (0:ℝ)..x, t^(a-1)*(1-t)^(-1/2:ℝ))/Real.Gamma (1/2):ℝ):ℂ) := by
  have h := DLMF.Confluent.IncompleteBetaUniform.normalizedIncompleteBeta_eq_integral
    (b := (1/2:ℝ)) ha (by norm_num) hx
  convert h using 1 <;> norm_num

/-- For positive `a` and `0 < x ≤ 1`, omitting the factor `(1-t)⁻¹ᐟ² ≥ 1` gives a lower
bound for the incomplete Beta integral. -/
lemma div_le_integral_beta_half {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hx1 : x ≤ 1) :
    x^a/a ≤ ∫ t in (0:ℝ)..x, t^(a-1)*(1-t)^(-1/2:ℝ) := by
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hx.le
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < a-1))
    (TauCeti.intervalIntegrable_rpow_mul_one_sub_rpow ha (by norm_num : 0 < (1/2:ℝ))
      (u := 0) (v := x) ⟨le_rfl, zero_le_one⟩ ⟨hx.le,hx1⟩)
    (fun t ht => show t^(a-1) ≤ t^(a-1)*(1-t)^((1/2:ℝ)-1) from ?_)
  · have he : (∫ t in (0:ℝ)..x, t^(a-1)) = x^a/a := by
      rw [integral_rpow (Or.inl (by linarith))]
      rw [sub_add_cancel, Real.zero_rpow ha.ne', sub_zero]
    simpa only [show (1/2:ℝ)-1=(-1/2:ℝ) by norm_num, he] using hmono
  · have ht1 : t < 1 := ht.2.trans_le hx1
    have hp : 1 ≤ (1-t)^((1/2:ℝ)-1) := by
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith [ht.1])
        (by norm_num)
    nlinarith [Real.rpow_nonneg ht.1.le (a-1)]

/-- For positive `a` and `ξ`, monotonicity of `t⁻¹ᐟ²` bounds `F₀(a,1/2,ξ)` by an
exponential tail. -/
lemma norm_betaAuxF_zero_le {a ξ : ℝ} (ha : 0 < a) (hξ : 0 < ξ) :
    ‖betaAuxF 0 a (1/2) ξ‖ ≤ ξ^(-1/2:ℝ)*Real.exp (-a*ξ)/(a*Real.Gamma (1/2)) := by
  have hI : IntegrableOn (fun t : ℝ => t^(-1/2:ℝ)*Real.exp (-a*t)) (Ioi ξ) := by
    simpa only [pow_zero, one_mul, show (1/2:ℝ)-1=(-1/2:ℝ) by norm_num] using
      integrableOn_betaAux_integrand 0 ha (by norm_num : 0 < (1/2:ℝ)) hξ.le
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-a*t)) (Ioi ξ) :=
    integrableOn_exp_mul_Ioi (by linarith : -a < 0) ξ
  have hle : (∫ t in Ioi ξ, t^(-1/2:ℝ)*Real.exp (-a*t)) ≤
      ξ^(-1/2:ℝ)*Real.exp (-a*ξ)/a := by
    have h := integral_mono_ae hI (hE.const_mul (ξ^(-1/2:ℝ)))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht =>
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hξ ht.le (by norm_num))
          (Real.exp_pos _).le))
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -a < 0)] at h
    convert h using 1; ring
  have hpos : 0 ≤ ∫ t in Ioi ξ, t^(-1/2:ℝ)*Real.exp (-a*t) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (hξ.trans ht).le _) (Real.exp_pos _).le
  have hG := Real.Gamma_pos_of_pos (show (0:ℝ) < 1/2 by norm_num)
  have haux : betaAuxF 0 a (1/2) ξ =
      (((∫ t in Ioi ξ, t^(-1/2:ℝ)*Real.exp (-a*t))/Real.Gamma (1/2):ℝ):ℂ) := by
    rw [betaAuxF, Complex.Gamma_ofReal]
    simp only [pow_zero, one_mul, show (1/2:ℝ)-1=(-1/2:ℝ) by norm_num, Complex.ofReal_div]
  rw [haux, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hpos hG.le)]
  convert div_le_div_of_nonneg_right hle hG.le using 1; ring

/-- The Gamma-normalized incomplete Beta function for `b = 1/2` is not uniformly `O(F₀)`
on the entire interval `0 < x ≤ 1` as `a` tends to infinity. -/
lemma not_isBigO_normalizedIncompleteBeta_half : ¬ IsBigO
    (comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1})
    (fun p : ℝ × ℝ => Gamma p.1/Gamma (p.1+(1/2:ℝ))*
      regularizedIncompleteBeta p.1 (1/2) p.2)
    (fun p : ℝ × ℝ => betaAuxF 0 p.1 (1/2) (Real.betaXi p.2)) := by
  intro h
  obtain ⟨C, hC⟩ := h.bound
  let D := |C|
  let ξ := (D+1)^2
  let x := Real.exp (-ξ)
  have hD : 0 ≤ D := abs_nonneg C
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hx : 0 < x := Real.exp_pos _
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ht : Tendsto (fun a : ℝ => (a,x)) atTop
      (comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1}) := by
    apply tendsto_inf.mpr
    constructor
    · rw [tendsto_comap_iff]
      exact tendsto_id
    · apply tendsto_principal.mpr
      filter_upwards [eventually_gt_atTop 0] with a ha
      exact ⟨ha,hx,hx1⟩
  obtain ⟨a,ha,hbound⟩ := ((eventually_gt_atTop 0).and (ht.eventually hC)).exists
  have hbig : ‖Gamma a/Gamma (a+(1/2:ℝ))*regularizedIncompleteBeta a (1/2) x‖ ≤
      D*‖betaAuxF 0 a (1/2) ξ‖ := by
    have hxi : Real.betaXi x = ξ := by simp [Real.betaXi, x]
    simp only [hxi] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
  have hG : 0 < Real.Gamma (1/2) := Real.Gamma_pos_of_pos (by norm_num)
  have hL := div_le_integral_beta_half ha hx hx1
  have hJ : 0 ≤ ∫ t in (0:ℝ)..x, t^(a-1)*(1-t)^(-1/2:ℝ) :=
    (div_pos (Real.rpow_pos_of_pos hx _) ha).le.trans hL
  have hN : Real.exp (-a*ξ)/(a*Real.Gamma (1/2)) ≤
      ‖Gamma a/Gamma (a+(1/2:ℝ))*regularizedIncompleteBeta a (1/2) x‖ := by
    rw [normalizedIncompleteBeta_eq_integral ha ⟨hx.le,hx1⟩, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hJ hG.le)]
    have hxp : x^a = Real.exp (-a*ξ) := by
      rw [Real.rpow_def_of_pos hx, show Real.log x = -ξ by simp [x]]
      congr 1
      ring
    have hh := div_le_div_of_nonneg_right hL hG.le
    rw [hxp] at hh
    convert hh using 1; ring
  have hu := norm_betaAuxF_zero_le ha hξ
  have hR := hN.trans (hbig.trans (mul_le_mul_of_nonneg_left hu hD))
  have hpow : ξ^(-1/2:ℝ) = (D+1)⁻¹ := by
    rw [show (-1/2:ℝ)=-(1/2) by norm_num, Real.rpow_neg hξ.le,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  rw [hpow] at hR
  have hden : 0 < a*Real.Gamma (1/2) := mul_pos ha hG
  have he : 0 < Real.exp (-a*ξ) := Real.exp_pos _
  have hdp : 0 < D+1 := by linarith
  have hh : (D+1)*(Real.exp (-a*ξ)/(a*Real.Gamma (1/2))) ≤
      D*(Real.exp (-a*ξ)/(a*Real.Gamma (1/2))) := by
    have hmul := mul_le_mul_of_nonneg_left hR hdp.le
    convert hmul using 1; field_simp
  have hpos : 0 < Real.exp (-a*ξ)/(a*Real.Gamma (1/2)) := div_pos he hden
  nlinarith

/-- The `b = 1/2`, `N = 0` specialization of the unrestricted uniform estimate is false. -/
lemma not_incompleteBeta_large_a_uniform_zero : ¬ IsBigO
    (comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1})
    (fun p : ℝ × ℝ => Gamma p.1/Gamma (p.1+(1/2:ℝ))*
      regularizedIncompleteBeta p.1 (1/2) p.2-∑ k ∈ Finset.range 0,
        Real.betaGeneratingCoeff (1/2) (Real.betaXi p.2) k*
          betaAuxF k p.1 (1/2) (Real.betaXi p.2))
    (fun p : ℝ × ℝ => (p.1:ℂ)^(-(0:ℤ))*betaAuxF 0 p.1 (1/2) (Real.betaXi p.2)) := by
  simpa only [Finset.range_zero, Finset.sum_empty, sub_zero, neg_zero, zpow_zero, one_mul]
    using not_isBigO_normalizedIncompleteBeta_half

end DLMF.Confluent.BetaUniformEndpoint
