/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Scorer
public import DLMF.Airy.IntegralTools
public import DLMF.IncompleteGamma.ContinuedProperties
public import DLMFMathlib.Analysis.Integral.PrincipalValue
public import DLMF.Bessel.KMellin
public import DLMFMathlib.Analysis.Complex.NonInteger

/-!
# Airy primitives and bilateral Laplace transforms

Integral identities for the Airy functions and the bilateral Laplace transform, including
convergence and normalization.

Source references and common attribution are retained in
`DLMF.Airy.Integrals`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology

namespace DLMF.Airy

/-- `Gi' = Bi'(1/3 - ∫Ai) + Ai' ∫Bi`, the derivative of 9.12.4. -/
theorem scorerGiDeriv_variation (z : ℂ) :
    scorerGiDeriv z = airyBiDeriv z * (1 / 3 - primitive airyAi z) +
      airyAiDeriv z * primitive airyBi z := by
  have hfun : scorerGi = fun z => airyBi z * (1 / 3 - primitive airyAi z) +
      airyAi z * primitive airyBi z := funext scorerGi_variation
  have pA := hasDerivAt_primitive differentiable_airyAi z
  have pB := hasDerivAt_primitive differentiable_airyBi z
  have hd := (((hasDerivAt_airyBi z).mul ((hasDerivAt_const z (1 / 3 : ℂ)).sub pA)).add
      ((hasDerivAt_airyAi z).mul pB))
  rw [scorerGiDeriv, hfun]
  refine hd.deriv.trans ?_
  simp only [Pi.sub_apply]; ring

/-- `Hi' = Bi'(2/3 + ∫Ai) - Ai' ∫Bi`, the derivative of 9.12.5. -/
theorem scorerHiDeriv_variation (z : ℂ) :
    scorerHiDeriv z = airyBiDeriv z * (2 / 3 + primitive airyAi z) -
      airyAiDeriv z * primitive airyBi z := by
  have h := scorerGiDeriv_eq z
  rw [scorerGiDeriv_variation] at h
  linear_combination h

/-- `1/3 - ∫₀^z Ai = π (Ai(z) Gi'(z) - Ai'(z) Gi(z))` (DLMF 9.10.1). -/
@[dlmf 9.10.E1]
theorem airyAi_integral_scorerGi (z : ℂ) :
    1 / 3 - primitive airyAi z = π * (airyAi z * scorerGiDeriv z - airyAiDeriv z * scorerGi z) := by
  rw [scorerGiDeriv_variation, scorerGi_variation]
  have hW := wronskian_airyAi_airyBi z
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show airyAi z * (airyBiDeriv z * (1 / 3 - primitive airyAi z) +
      airyAiDeriv z * primitive airyBi z) - airyAiDeriv z * (airyBi z * (1 / 3 - primitive airyAi z) +
      airyAi z * primitive airyBi z) = (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) *
      (1 / 3 - primitive airyAi z) by ring, hW]
  field_simp

/-- `2/3 + ∫₀^z Ai = π (Ai(z) Hi'(z) - Ai'(z) Hi(z))` (DLMF 9.10.2). -/
@[dlmf 9.10.E2]
theorem airyAi_integral_scorerHi (z : ℂ) :
    2 / 3 + primitive airyAi z = π * (airyAi z * scorerHiDeriv z - airyAiDeriv z * scorerHi z) := by
  rw [scorerHiDeriv_variation, scorerHi_variation]
  have hW := wronskian_airyAi_airyBi z
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show airyAi z * (airyBiDeriv z * (2 / 3 + primitive airyAi z) -
      airyAiDeriv z * primitive airyBi z) - airyAiDeriv z * (airyBi z * (2 / 3 + primitive airyAi z) -
      airyAi z * primitive airyBi z) = (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) *
      (2 / 3 + primitive airyAi z) by ring, hW]
  field_simp

/-- `∫₀^z Bi = π (Bi'(z) Gi(z) - Bi(z) Gi'(z)) = π (Bi(z) Hi'(z) - Bi'(z) Hi(z))` (DLMF 9.10.3). -/
@[dlmf 9.10.E3]
theorem airyBi_integral_scorer (z : ℂ) :
    primitive airyBi z = π * (airyBiDeriv z * scorerGi z - airyBi z * scorerGiDeriv z) ∧
      primitive airyBi z = π * (airyBi z * scorerHiDeriv z - airyBiDeriv z * scorerHi z) := by
  have hW := wronskian_airyAi_airyBi z
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  constructor
  · rw [scorerGiDeriv_variation, scorerGi_variation]
    rw [show airyBiDeriv z * (airyBi z * (1 / 3 - primitive airyAi z) + airyAi z * primitive airyBi z) -
        airyBi z * (airyBiDeriv z * (1 / 3 - primitive airyAi z) + airyAiDeriv z * primitive airyBi z) =
        (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) * primitive airyBi z by ring, hW]
    field_simp
  · rw [scorerHiDeriv_variation, scorerHi_variation]
    rw [show airyBi z * (airyBiDeriv z * (2 / 3 + primitive airyAi z) - airyAiDeriv z * primitive airyBi z) -
        airyBiDeriv z * (airyBi z * (2 / 3 + primitive airyAi z) - airyAi z * primitive airyBi z) =
        (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) * primitive airyBi z by ring, hW]
    field_simp

/-- For real `x`, `∫_{-∞}^x Ai = 2/3 + ∫₀^x Ai` as a convergent improper integral (DLMF 9.10.2). -/
@[dlmf 9.10.E2]
theorem airyAi_lower_integral_scorerHi (x : ℝ) :
    HasIntegralAtBot (fun t => airyAi t) x (2 / 3 + primitive airyAi x) :=
  airyInt_hasIntegralAtBot_of_cross differentiable_airyAi
    (g := fun z => airyAi z * scorerHiDeriv z - airyAiDeriv z * scorerHi z)
    (fun x => airyAi_integral_scorerHi x)
    (airyInt_tendsto_cross_atBot airyInt_ai_neg_isBigO airyInt_aiDeriv_neg_isBigO) x

/-- For real `x`, `∫_{-∞}^x Bi = ∫₀^x Bi` as a convergent improper integral (DLMF 9.10.3). -/
@[dlmf 9.10.E3]
theorem airyBi_lower_integral_scorer (x : ℝ) :
    HasIntegralAtBot (fun t => airyBi t) x (primitive airyBi x) := by
  have h := airyInt_hasIntegralAtBot_of_cross differentiable_airyBi (c := 0)
    (g := fun z => airyBi z * scorerHiDeriv z - airyBiDeriv z * scorerHi z)
    (fun x => by rw [zero_add]; exact (airyBi_integral_scorer x).2)
    (airyInt_tendsto_cross_atBot airyInt_bi_neg_isBigO airyInt_biDeriv_neg_isBigO) x
  simpa using h

/-- `∫₀^∞ Ai(t) dt = 1/3` (DLMF 9.10.11). -/
@[dlmf 9.10.E11]
theorem airyAi_positive_integral  :
    HasIntegralAtTop (fun t => airyAi t) 0 (1 / 3) := by
  have h := ((airyInt_tendsto_cross_gi_atTop.const_mul (π : ℂ)).const_sub (1 / 3 : ℂ))
  simp only [mul_zero, sub_zero] at h
  refine h.congr fun R => ?_
  rw [← airyAi_integral_scorerGi, ← airyInt_primitive_ofReal differentiable_airyAi]
  ring

/-- `∫_x^∞ Ai(t) dt ∼ e^{-ζ}/(2√π x^{3/4})` as `x → ∞`, with `ζ = (2/3) x^{3/2}` (DLMF 9.10.4). -/
@[dlmf 9.10.E4]
theorem airyAi_tail_integral_asymptotic  :
    (fun x : ℝ => improperAtTop (fun t => airyAi t) x) ~[atTop]
      (fun x : ℝ => ((Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (3 / 4 : ℝ)) : ℝ) : ℂ)) := by
  have hπ := Real.pi_pos
  set v : ℝ → ℂ := fun x => ((Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (3 / 4 : ℝ)) : ℝ) : ℂ)
    with hvdef
  have hv : ∀ x : ℝ, 0 < x → ‖v x‖ = Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (3 / 4 : ℝ)) :=
    fun x hx => by rw [hvdef, norm_real, Real.norm_of_nonneg (by positivity)]
  have hval : ∀ x : ℝ, improperAtTop (fun t => airyAi t) x =
      π * (airyAi x * scorerGiDeriv x - airyAiDeriv x * scorerGi x) := by
    intro x
    have hc : Continuous fun t : ℝ => airyAi t := differentiable_airyAi.continuous.comp continuous_ofReal
    have hI : HasIntegralAtTop (fun t => airyAi t) x (1 / 3 - primitive airyAi x) := by
      have h := airyAi_positive_integral.sub_const (primitive airyAi x)
      refine h.congr fun R => ?_
      rw [airyInt_primitive_ofReal differentiable_airyAi,
        intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _)]
    unfold improperAtTop
    exact hI.limUnder_eq.trans (airyAi_integral_scorerGi x)
  refine IsEquivalent.congr_left ?_ (Eventually.of_forall fun x => (hval x).symm)
  refine airyInt_cross_equiv_atTop (A := fun x => airyAi x) (A' := fun x => airyAiDeriv x) ?_ ?_
  · refine (airyInt_poincare0_real .ai).trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [airyReal_norm_prefactor_ai hx, one_mul, Real.norm_of_nonneg (by positivity), hv x hx]
    obtain ⟨-, h2, -⟩ := airyInt_quarter_rpow hx
    have p1 : 0 < x ^ (1 / 4 : ℝ) := by positivity
    have p3 : 0 < x ^ (3 / 4 : ℝ) := by positivity
    have ps : 0 < Real.sqrt π := Real.sqrt_pos.2 hπ
    apply le_of_eq
    field_simp
    exact h2.symm
  · have hP : ∀ x : ℝ, 0 < x → airyAiDeriv x + x * v x =
        airyFunction .aiDeriv x - airyPrefactor .aiDeriv x := by
      intro x hx
      obtain ⟨h1, -, -⟩ := airyInt_quarter_rpow hx
      have p3 : 0 < x ^ (3 / 4 : ℝ) := by positivity
      have ps : 0 < Real.sqrt π := Real.sqrt_pos.2 hπ
      simp only [airyFunction, airyPrefactor, hvdef]
      have R : x * (Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (3 / 4 : ℝ))) =
          x ^ (1 / 4 : ℝ) * Real.exp (-airyZeta x) / (2 * Real.sqrt π) := by
        calc x * (Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (3 / 4 : ℝ)))
            = (x ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ)) *
              (Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (3 / 4 : ℝ))) := by rw [h1]
          _ = _ := by field_simp
      have key : (x : ℂ) * ((Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (3 / 4 : ℝ)) : ℝ) : ℂ) =
          (((x ^ (1 / 4 : ℝ)) * Real.exp (-airyZeta x) / (2 * Real.sqrt π) : ℝ) : ℂ) := by
        rw [← ofReal_mul, R]
      rw [key, airyInt_cpow_quarter_ofReal hx, airyReal_zeta_ofReal hx]
      push_cast; ring
    refine ((airyInt_poincare_real .aiDeriv).congr' ?_ EventuallyEq.rfl).trans
      (IsBigO.of_bound (3 / 2) ?_)
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact (hP x hx).symm
    · filter_upwards [eventually_gt_atTop 0] with x hx
      obtain ⟨-, -, h3⟩ := airyInt_quarter_rpow hx
      rw [airyInt_norm_div_zeta .aiDeriv hx, airyReal_norm_prefactor_aiDeriv hx,
        Real.norm_of_nonneg (by positivity), hv x hx]
      have p3 : 0 < x ^ (3 / 4 : ℝ) := by positivity
      have ps : 0 < Real.sqrt π := Real.sqrt_pos.2 hπ
      apply le_of_eq
      field_simp
      rw [← h3]; ring

/-- `∫₀^x Bi(t) dt ∼ e^{ζ}/(√π x^{3/4})` as `x → ∞`, with `ζ = (2/3) x^{3/2}` (DLMF 9.10.5). -/
@[dlmf 9.10.E5]
theorem airyBi_integral_asymptotic  :
    (fun x : ℝ => primitive airyBi x) ~[atTop]
      (fun x : ℝ => ((Real.exp (airyZeta x) / (Real.sqrt π * x ^ (3 / 4 : ℝ)) : ℝ) : ℂ)) := by
  have hπ := Real.pi_pos
  set v : ℝ → ℂ := fun x => ((Real.exp (airyZeta x) / (Real.sqrt π * x ^ (3 / 4 : ℝ)) : ℝ) : ℂ)
    with hvdef
  have hv : ∀ x : ℝ, 0 < x → ‖v x‖ = Real.exp (airyZeta x) / (Real.sqrt π * x ^ (3 / 4 : ℝ)) :=
    fun x hx => by rw [hvdef, norm_real, Real.norm_of_nonneg (by positivity)]
  suffices hmain : (fun x : ℝ => (π : ℂ) * ((-airyBi x) * scorerGiDeriv x -
      (-airyBiDeriv x) * scorerGi x)) ~[atTop] v by
    refine hmain.congr_left (Eventually.of_forall fun x => ?_)
    simp only
    rw [(airyBi_integral_scorer x).1]; ring
  refine airyInt_cross_equiv_atTop (A := fun x => -airyBi x) (A' := fun x => -airyBiDeriv x) ?_ ?_
  · refine (airyInt_poincare0_real .bi).neg_left.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [airySt_norm_prefactor_bi hx, one_mul, Real.norm_of_nonneg (by positivity), hv x hx]
    obtain ⟨-, h2, -⟩ := airyInt_quarter_rpow hx
    have p1 : 0 < x ^ (1 / 4 : ℝ) := by positivity
    have p3 : 0 < x ^ (3 / 4 : ℝ) := by positivity
    have ps : 0 < Real.sqrt π := Real.sqrt_pos.2 hπ
    apply le_of_eq
    field_simp
    exact h2.symm
  · have hP : ∀ x : ℝ, 0 < x → -airyBiDeriv x + x * v x =
        -(airyFunction .biDeriv x - airyPrefactor .biDeriv x) := by
      intro x hx
      obtain ⟨h1, -, -⟩ := airyInt_quarter_rpow hx
      have p3 : 0 < x ^ (3 / 4 : ℝ) := by positivity
      have ps : 0 < Real.sqrt π := Real.sqrt_pos.2 hπ
      simp only [airyFunction, airyPrefactor, hvdef]
      have R : x * (Real.exp (airyZeta x) / (Real.sqrt π * x ^ (3 / 4 : ℝ))) =
          x ^ (1 / 4 : ℝ) * Real.exp (airyZeta x) / Real.sqrt π := by
        calc x * (Real.exp (airyZeta x) / (Real.sqrt π * x ^ (3 / 4 : ℝ)))
            = (x ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ)) *
              (Real.exp (airyZeta x) / (Real.sqrt π * x ^ (3 / 4 : ℝ))) := by rw [h1]
          _ = _ := by field_simp
      have key : (x : ℂ) * ((Real.exp (airyZeta x) / (Real.sqrt π * x ^ (3 / 4 : ℝ)) : ℝ) : ℂ) =
          (((x ^ (1 / 4 : ℝ)) * Real.exp (airyZeta x) / Real.sqrt π : ℝ) : ℂ) := by
        rw [← ofReal_mul, R]
      rw [key, airyInt_cpow_quarter_ofReal hx, airyReal_zeta_ofReal hx]
      push_cast; ring
    refine ((airyInt_poincare_real .biDeriv).neg_left.congr' ?_ EventuallyEq.rfl).trans
      (IsBigO.of_bound (3 / 2) ?_)
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact (hP x hx).symm
    · filter_upwards [eventually_gt_atTop 0] with x hx
      obtain ⟨-, -, h3⟩ := airyInt_quarter_rpow hx
      rw [airyInt_norm_div_zeta .biDeriv hx, airyInt_norm_prefactor_biDeriv hx,
        Real.norm_of_nonneg (by positivity), hv x hx]
      have p3 : 0 < x ^ (3 / 4 : ℝ) := by positivity
      have ps : 0 < Real.sqrt π := Real.sqrt_pos.2 hπ
      apply le_of_eq
      field_simp
      rw [← h3]; ring

/-- As `x → -∞`, `∫_{-∞}^x Ai(t) dt = cos((2/3)(-x)^{3/2} + π/4)/(√π (-x)^{3/4}) + O(|x|^{-9/4})`
(DLMF 9.10.6). -/
@[dlmf 9.10.E6]
theorem airyAi_negative_integral_asymptotic  :
    IsBigO atBot (fun x : ℝ => improperAtBot (fun t => airyAi t) x -
      ((Real.cos (2 / 3 * (-x) ^ (3 / 2 : ℝ) + π / 4) /
        (Real.sqrt π * (-x) ^ (3 / 4 : ℝ)) : ℝ) : ℂ))
      (fun x : ℝ => |x| ^ (-9 / 4 : ℝ)) := by
  have h := (airyInt_cross_expansion (f := airyAi) (f' := airyAiDeriv)
    (φ := fun s => Real.sin (airyZeta s - π / 4)) (fun s => Real.abs_sin_le_one _)
    airyInt_ai_neg_isBigO airyInt_aiDeriv_neg_sub).comp_tendsto tendsto_neg_atBot_atTop
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_lt_atBot 0] with x hx
    have hs : 0 < -x := by linarith
    have hv : improperAtBot (fun t => airyAi t) x = 2 / 3 + primitive airyAi x :=
      (airyAi_lower_integral_scorerHi x).limUnder_eq
    simp only [Function.comp_apply, ofReal_neg, neg_neg]
    rw [hv, airyAi_integral_scorerHi]
    have hc : Real.cos (2 / 3 * (-x) ^ (3 / 2 : ℝ) + π / 4) = -Real.sin (airyZeta (-x) - π / 4) := by
      rw [airyZeta, show 2 / 3 * (-x) ^ (3 / 2 : ℝ) - π / 4 =
        (2 / 3 * (-x) ^ (3 / 2 : ℝ) + π / 4) - π / 2 by ring, Real.sin_sub_pi_div_two]
      ring
    have hc' : (-x) ^ (-(3 / 4) : ℝ) / Real.sqrt π * Real.sin (airyZeta (-x) - π / 4) =
        -(Real.cos (2 / 3 * (-x) ^ (3 / 2 : ℝ) + π / 4) / (Real.sqrt π * (-x) ^ (3 / 4 : ℝ))) := by
      rw [hc, Real.rpow_neg hs.le]
      field_simp
    rw [hc', ofReal_neg]; ring
  · filter_upwards [eventually_lt_atBot 0] with x hx
    simp only [Function.comp_apply]
    rw [abs_of_neg hx]; norm_num

/-- Asymptotics of `∫_{-∞}^x Bi` as `x → -∞` (DLMF 9.10.7), corrected:
`∫_{-∞}^x Bi(t) dt = -π^{-1/2} (-x)^{-3/4} sin(⅔(-x)^{3/2} + π/4) + O(|x|^{-9/4})` as `x → -∞`.

DLMF prints a plus sign in front of the leading term. Evidence for the erratum: at `x = -10`
the integral is `-0.01504…` while the printed formula gives `+0.01240…`, and by 9.7.11 the
derivative of the printed leading term is `-Bi(x)` (whereas 9.10.6 checks out). -/
@[dlmf 9.10.E7 "source erratum: leading term has a minus sign"]
theorem airyBi_negative_integral_asymptotic :
    IsBigO atBot (fun x : ℝ => improperAtBot (fun t => airyBi t) x +
      ((Real.sin (2 / 3 * (-x) ^ (3 / 2 : ℝ) + π / 4) /
        (Real.sqrt π * (-x) ^ (3 / 4 : ℝ)) : ℝ) : ℂ))
      (fun x : ℝ => |x| ^ (-9 / 4 : ℝ)) := by
  have h := (airyInt_cross_expansion (f := airyBi) (f' := airyBiDeriv)
    (φ := fun s => Real.cos (airyZeta s - π / 4)) (fun s => Real.abs_cos_le_one _)
    airyInt_bi_neg_isBigO airyInt_biDeriv_neg_sub).comp_tendsto tendsto_neg_atBot_atTop
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_lt_atBot 0] with x hx
    have hs : 0 < -x := by linarith
    have hv : improperAtBot (fun t => airyBi t) x = primitive airyBi x :=
      (airyBi_lower_integral_scorer x).limUnder_eq
    simp only [Function.comp_apply, ofReal_neg, neg_neg]
    rw [hv, (airyBi_integral_scorer x).2]
    have hc : Real.sin (2 / 3 * (-x) ^ (3 / 2 : ℝ) + π / 4) = Real.cos (airyZeta (-x) - π / 4) := by
      rw [airyZeta, show 2 / 3 * (-x) ^ (3 / 2 : ℝ) - π / 4 =
        (2 / 3 * (-x) ^ (3 / 2 : ℝ) + π / 4) - π / 2 by ring, Real.cos_sub_pi_div_two]
    have hc' : (-x) ^ (-(3 / 4) : ℝ) / Real.sqrt π * Real.cos (airyZeta (-x) - π / 4) =
        Real.sin (2 / 3 * (-x) ^ (3 / 2 : ℝ) + π / 4) / (Real.sqrt π * (-x) ^ (3 / 4 : ℝ)) := by
      rw [hc, Real.rpow_neg hs.le]
      field_simp
    rw [hc']
  · filter_upwards [eventually_lt_atBot 0] with x hx
    simp only [Function.comp_apply]
    rw [abs_of_neg hx]; norm_num

/-- For an Airy solution `w`, an antiderivative of `z w(z)` is `w'(z)` (DLMF 9.10.8). -/
@[dlmf 9.10.E8]
theorem airy_linear_antiderivative {w w' : ℂ → ℂ} (hw : IsAirySol w w') (z : ℂ) :
    HasDerivAt w' (z * w z) z := by
  exact (hw z).2

/-- For an Airy solution `w`, an antiderivative of `z² w(z)` is `z w'(z) - w(z)` (DLMF 9.10.9). -/
@[dlmf 9.10.E9]
theorem airy_quadratic_antiderivative {w w' : ℂ → ℂ} (hw : IsAirySol w w') (z : ℂ) :
    HasDerivAt (fun t => t * w' t - w t) (z ^ 2 * w z) z := by
  have h := ((hasDerivAt_id z).mul (hw z).2).sub (hw z).1
  exact h.congr_deriv (by simp only [id]; ring)

/-- For an Airy solution `w`, `z^{n+2} w' - (n+2) z^{n+1} w` is an antiderivative of
`z^{n+3} w - (n+1)(n+2) z^n w`, the recurrence for the moments `∫ z^n w` (DLMF 9.10.10). -/
@[dlmf 9.10.E10]
theorem airy_moment_antiderivative_recurrence {w w' : ℂ → ℂ} (hw : IsAirySol w w') (n : ℕ) (z : ℂ) :
    HasDerivAt (fun t => t ^ (n + 2) * w' t - (n + 2 : ℂ) * t ^ (n + 1) * w t)
      (z ^ (n + 3) * w z - (n + 1 : ℂ) * (n + 2 : ℂ) * z ^ n * w z) z := by
  have h := ((hasDerivAt_pow (n + 2) z).mul (hw z).2).sub
    (((hasDerivAt_pow (n + 1) z).mul (hw z).1).const_mul (n + 2 : ℂ))
  convert h using 1
  · funext t
    change t ^ (n + 2) * w' t - (n + 2 : ℂ) * t ^ (n + 1) * w t =
      t ^ (n + 2) * w' t - (n + 2 : ℂ) * (t ^ (n + 1) * w t)
    ring
  · simp only [show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ]
    ring

/-- `∫_{-∞}^0 Ai(t) dt = 2/3` (DLMF 9.10.11). -/
@[dlmf 9.10.E11]
theorem airyAi_negative_integral  :
    HasIntegralAtBot (fun t => airyAi t) 0 (2 / 3) := by
  simpa [primitive_zero] using airyAi_lower_integral_scorerHi 0

/-- `∫_{-∞}^0 Bi(t) dt = 0` (DLMF 9.10.12). -/
@[dlmf 9.10.E12]
theorem airyBi_negative_integral  :
    HasIntegralAtBot (fun t => airyBi t) 0 0 := by
  simpa [primitive_zero] using airyBi_lower_integral_scorer 0

/-! ### The bilateral Laplace transform 9.10.13 -/

section AiryLaplace

/-- `|Ai(x)| ≤ e^{-ζ}` and `|Ai'(x)| ≤ 2 x^{1/4} e^{-ζ}` for `x ≥ 1`. -/
theorem airyLap_norm_le_exp {x : ℝ} (hx : 1 ≤ x) :
    ‖airyAi x‖ ≤ Real.exp (-airyZeta x) ∧
      ‖airyAiDeriv x‖ ≤ 2 * x ^ (1 / 4 : ℝ) * Real.exp (-airyZeta x) := by
  have hx0 : 0 < x := by linarith
  have hs : 1 ≤ Real.sqrt π := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hq1 : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  constructor
  · have h := (airy_ai_real_error hx0 (N := 0) le_rfl).1
    simp only [airyRemainder, airyExponentialSum, Finset.range_zero, Finset.sum_empty, sub_zero,
      airyExpansionCoeff, pow_zero, div_one, one_mul, airyReal_airyU_zero, ofReal_one, norm_one,
      airyFunction] at h
    have hp : airyPrefactor .ai x ≠ 0 :=
      airyRot_prefactor_ne_zero .ai (ofReal_ne_zero.mpr hx0.ne')
    have hpn : ‖airyPrefactor .ai x‖ ≤ Real.exp (-airyZeta x) := by
      rw [airyReal_norm_prefactor_ai hx0, div_le_iff₀ (by positivity)]
      have : 0 < Real.exp (-airyZeta x) := Real.exp_pos _
      have h2 : 1 ≤ 2 * Real.sqrt π * x ^ (1 / 4 : ℝ) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h2 this.le]
    calc ‖airyAi x‖ = ‖airyPrefactor .ai x‖ * ‖airyAi x / airyPrefactor .ai x‖ := by
          rw [← norm_mul, mul_div_cancel₀ _ hp]
      _ ≤ Real.exp (-airyZeta x) * 1 := by gcongr
      _ = _ := mul_one _
  · have h := airy_aiDeriv_bound hx0
    rw [airyAiDeriv_ofReal_eq, norm_real, Real.norm_eq_abs]
    have hz := airyInt_two_thirds_le_airyZeta hx
    have h3 : 7 / (72 * airyZeta x) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hq : 0 ≤ x ^ (1 / 4 : ℝ) * Real.exp (-airyZeta x) := by positivity
    calc _ ≤ _ := h
      _ ≤ x ^ (1 / 4 : ℝ) * Real.exp (-airyZeta x) / (2 * 1) * (1 + 1) := by gcongr
      _ ≤ 2 * x ^ (1 / 4 : ℝ) * Real.exp (-airyZeta x) := by linarith

/-- **Superexponential decay on the positive axis**: for every `b` there is `C` with
`|Ai(t)|, |Ai'(t)| ≤ C e^{-bt}` for `t ≥ 0`. -/
theorem airyLap_pos_bound (b : ℝ) : ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
    ‖airyAi t‖ ≤ C * Real.exp (-b * t) ∧ ‖airyAiDeriv t‖ ≤ C * Real.exp (-b * t) := by
  set B := max b 0
  set T := max 1 ((3 * (B + 1) / 2) ^ 2)
  have hcont : ContinuousOn (fun t : ℝ => (‖airyAi t‖ + ‖airyAiDeriv t‖) * Real.exp (B * t))
      (Icc 0 T) := by
    have h1 : Continuous fun t : ℝ => airyAi t :=
      (differentiable_airyAi.continuous).comp continuous_ofReal
    have h2 : Continuous fun t : ℝ => airyAiDeriv t :=
      (continuous_iff_continuousAt.mpr fun z => (hasDerivAt_airyAiDeriv z).continuousAt).comp
        continuous_ofReal
    fun_prop
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max K 0 + 2, by positivity, fun t ht => ?_⟩
  have hBt : Real.exp (-B * t) ≤ Real.exp (-b * t) :=
    Real.exp_le_exp.mpr (by nlinarith [le_max_left b 0])
  have hE : 0 < Real.exp (B * t) := Real.exp_pos _
  suffices h : ‖airyAi t‖ ≤ (max K 0 + 2) * Real.exp (-B * t) ∧
      ‖airyAiDeriv t‖ ≤ (max K 0 + 2) * Real.exp (-B * t) by
    have hC : 0 ≤ max K 0 + 2 := by positivity
    exact ⟨h.1.trans (by gcongr), h.2.trans (by gcongr)⟩
  rcases le_or_gt t T with htT | htT
  · have h := hK t ⟨ht, htT⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    have hm : (‖airyAi t‖ + ‖airyAiDeriv t‖) ≤ max K 0 * Real.exp (-B * t) := by
      rw [show -B * t = -(B * t) by ring, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hE]
      exact h.trans (le_max_left _ _)
    have h0 : 0 ≤ 2 * Real.exp (-B * t) := by positivity
    constructor <;> nlinarith [norm_nonneg (airyAi t), norm_nonneg (airyAiDeriv t)]
  · have ht1 : 1 ≤ t := le_trans (le_max_left _ _) htT.le
    have ht0 : 0 < t := by linarith
    obtain ⟨hA, hD⟩ := airyLap_norm_le_exp ht1
    -- `ζ(t) ≥ (B+1) t`
    have hsq : 3 * (B + 1) / 2 ≤ Real.sqrt t := by
      rw [show 3 * (B + 1) / 2 = Real.sqrt ((3 * (B + 1) / 2) ^ 2) by
        rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (le_trans (le_max_right _ _) htT.le)
    have hz : (B + 1) * t ≤ airyZeta t := by
      have e : airyZeta t = 2 / 3 * t * Real.sqrt t := by
        rw [airyZeta, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht0, Real.rpow_one,
          Real.sqrt_eq_rpow]; ring
      rw [e]; nlinarith
    have hq : t ^ (1 / 4 : ℝ) ≤ Real.exp t := by
      calc t ^ (1 / 4 : ℝ) ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
        _ = t := Real.rpow_one t
        _ ≤ t + 1 := by linarith
        _ ≤ Real.exp t := Real.add_one_le_exp t
    have e1 : Real.exp (-airyZeta t) ≤ Real.exp (-B * t) * Real.exp (-t) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have hK0 : 0 ≤ max K 0 := le_max_right _ _
    have hEB : 0 < Real.exp (-B * t) := Real.exp_pos _
    have hEt : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    constructor
    · calc ‖airyAi t‖ ≤ Real.exp (-airyZeta t) := hA
        _ ≤ Real.exp (-B * t) * Real.exp (-t) := e1
        _ ≤ Real.exp (-B * t) * 1 := by gcongr
        _ ≤ _ := by nlinarith
    · calc ‖airyAiDeriv t‖ ≤ 2 * t ^ (1 / 4 : ℝ) * Real.exp (-airyZeta t) := hD
        _ ≤ 2 * Real.exp t * (Real.exp (-B * t) * Real.exp (-t)) := by gcongr
        _ = 2 * Real.exp (-B * t) := by
          rw [show 2 * Real.exp t * (Real.exp (-B * t) * Real.exp (-t)) =
            2 * Real.exp (-B * t) * (Real.exp t * Real.exp (-t)) by ring, ← Real.exp_add]
          simp
        _ ≤ _ := by nlinarith

/-- **Bounds on the negative axis**: `|Ai(t)| ≤ C` and `|Ai'(t)| ≤ C (1 + |t|)` for `t ≤ 0`. -/
theorem airyLap_neg_bound : ∃ C, 0 ≤ C ∧ ∀ t : ℝ, t ≤ 0 →
    ‖airyAi t‖ ≤ C ∧ ‖airyAiDeriv t‖ ≤ C * (1 + |t|) := by
  obtain ⟨c1, hc1⟩ := airyInt_ai_neg_isBigO.bound
  obtain ⟨c2, hc2⟩ := airyInt_aiDeriv_neg_isBigO.bound
  obtain ⟨S, hS⟩ := eventually_atTop.1 ((hc1.and hc2).and (eventually_ge_atTop 1))
  set S' := max S 1
  have hcont : ContinuousOn (fun t : ℝ => ‖airyAi t‖ + ‖airyAiDeriv t‖) (Icc (-S') 0) := by
    have h1 : Continuous fun t : ℝ => airyAi t :=
      (differentiable_airyAi.continuous).comp continuous_ofReal
    have h2 : Continuous fun t : ℝ => airyAiDeriv t :=
      (continuous_iff_continuousAt.mpr fun z => (hasDerivAt_airyAiDeriv z).continuousAt).comp
        continuous_ofReal
    fun_prop
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max K 0 + |c1| + |c2|, by positivity, fun t ht => ?_⟩
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have ha := abs_nonneg t
  rcases le_or_gt (-S') t with htS | htS
  · have h := hK t ⟨htS, ht⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    have h' := h.trans (le_max_left K 0)
    have n1 := norm_nonneg (airyAi t)
    have n2 := norm_nonneg (airyAiDeriv t)
    constructor
    · nlinarith [abs_nonneg c1, abs_nonneg c2]
    · nlinarith [abs_nonneg c1, abs_nonneg c2]
  · set s := -t
    have hs : S ≤ s := by simp only [s]; linarith [le_max_left S 1]
    obtain ⟨⟨h1, h2⟩, hs1⟩ := hS s hs
    have hs0 : 0 < s := by linarith
    have ht' : ((t : ℝ) : ℂ) = -((s : ℝ) : ℂ) := by simp [s]
    rw [ht']
    have hq1 : ‖s ^ (-(1 / 4) : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
    have hq2 : ‖s ^ (1 / 4 : ℝ)‖ ≤ 1 + |t| := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonpos ht]
      calc s ^ (1 / 4 : ℝ) ≤ s ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
        _ = s := Real.rpow_one s
        _ ≤ 1 + -t := by simp only [s]; linarith
    have hc1' : c1 ≤ |c1| := le_abs_self c1
    have hc2' : c2 ≤ |c2| := le_abs_self c2
    constructor
    · calc ‖airyAi (-(s : ℂ))‖ ≤ c1 * ‖s ^ (-(1 / 4) : ℝ)‖ := h1
        _ ≤ |c1| * 1 := by
          rcases le_or_gt 0 c1 with hc | hc
          · gcongr
          · nlinarith [norm_nonneg (s ^ (-(1 / 4) : ℝ)), abs_nonneg c1]
        _ ≤ _ := by nlinarith [abs_nonneg c2]
    · calc ‖airyAiDeriv (-(s : ℂ))‖ ≤ c2 * ‖s ^ (1 / 4 : ℝ)‖ := h2
        _ ≤ |c2| * (1 + |t|) := by
          rcases le_or_gt 0 c2 with hc | hc
          · gcongr
          · nlinarith [norm_nonneg (s ^ (1 / 4 : ℝ)), abs_nonneg c2]
        _ ≤ _ := by nlinarith [abs_nonneg c1]

/-- `1 + |t| ≤ c⁻¹ e^{c|t|}` for `0 < c ≤ 1`. -/
theorem airyLap_one_add_abs_le {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (t : ℝ) :
    1 + |t| ≤ c⁻¹ * Real.exp (c * |t|) := by
  have h := Real.add_one_le_exp (c * |t|)
  rw [le_inv_mul_iff₀ hc]
  nlinarith [abs_nonneg t]

/-- `|e^{qt}| = e^{(Re q) t}`. -/
theorem airyLap_norm_exp (q : ℂ) (t : ℝ) : ‖exp (q * t)‖ = Real.exp (q.re * t) := by
  rw [Complex.norm_exp]; simp

/-- **The dominating function**: for `a ≤ Re q ≤ b` with `a > 0`,
`(1 + |t|) |e^{qt} Ai(t)|` and `|e^{qt} Ai'(t)|` are at most `K e^{-c|t|}`, `c = min a 1 / 2`. -/
theorem airyLap_dom {a : ℝ} (ha : 0 < a) (b : ℝ) : ∃ K, 0 ≤ K ∧ ∀ q : ℂ, a ≤ q.re → q.re ≤ b →
    ∀ t : ℝ, (1 + |t|) * ‖exp (q * t) * airyAi t‖ ≤ K * Real.exp (-(min a 1 / 2) * |t|) ∧
      ‖exp (q * t) * airyAiDeriv t‖ ≤ K * Real.exp (-(min a 1 / 2) * |t|) := by
  set c := min a 1 / 2 with hcdef
  have hc : 0 < c := by positivity
  have hc1 : c ≤ 1 := by have := min_le_right a 1; linarith
  have h2a : 2 * c ≤ a := by have := min_le_left a 1; linarith
  have h21 : 2 * c ≤ 1 := by have := min_le_right a 1; linarith
  obtain ⟨Cp, hCp0, hCp⟩ := airyLap_pos_bound (b + 1)
  obtain ⟨Cn, hCn0, hCn⟩ := airyLap_neg_bound
  refine ⟨c⁻¹ * (Cp + Cn), by positivity, fun q hqa hqb t => ?_⟩
  have hone := airyLap_one_add_abs_le hc hc1 t
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  rw [norm_mul, norm_mul, airyLap_norm_exp]
  have hE := Real.exp_pos (q.re * t)
  rcases le_total t 0 with ht | ht
  · obtain ⟨hA, hD⟩ := hCn t ht
    have he : Real.exp (q.re * t) ≤ Real.exp (-a * |t|) :=
      Real.exp_le_exp.mpr (by rw [abs_of_nonpos ht]; nlinarith)
    -- `e^{c|t|} e^{-a|t|} ≤ e^{-c|t|}`
    have hk : Real.exp (c * |t|) * Real.exp (-a * |t|) ≤ Real.exp (-c * |t|) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg t])
    have hEc := Real.exp_pos (-c * |t|)
    have hEa := Real.exp_pos (-a * |t|)
    have hEp := Real.exp_pos (c * |t|)
    constructor
    · calc (1 + |t|) * (Real.exp (q.re * t) * ‖airyAi t‖)
          ≤ (c⁻¹ * Real.exp (c * |t|)) * (Real.exp (-a * |t|) * Cn) := by gcongr
        _ = c⁻¹ * Cn * (Real.exp (c * |t|) * Real.exp (-a * |t|)) := by ring
        _ ≤ c⁻¹ * Cn * Real.exp (-c * |t|) := by gcongr
        _ ≤ _ := by gcongr; linarith
    · calc Real.exp (q.re * t) * ‖airyAiDeriv t‖
          ≤ Real.exp (-a * |t|) * (Cn * (c⁻¹ * Real.exp (c * |t|))) := by
            gcongr; exact hD.trans (by gcongr)
        _ = c⁻¹ * Cn * (Real.exp (c * |t|) * Real.exp (-a * |t|)) := by ring
        _ ≤ c⁻¹ * Cn * Real.exp (-c * |t|) := by gcongr
        _ ≤ _ := by gcongr; linarith
  · obtain ⟨hA, hD⟩ := hCp t ht
    have hat : |t| = t := abs_of_nonneg ht
    have he : Real.exp (q.re * t) * Real.exp (-(b + 1) * t) ≤ Real.exp (-t) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    have hk : Real.exp (c * |t|) * Real.exp (-t) ≤ Real.exp (-c * |t|) := by
      rw [← Real.exp_add, hat]; exact Real.exp_le_exp.mpr (by nlinarith)
    have hk' : Real.exp (-t) ≤ Real.exp (-c * |t|) := by
      rw [hat]; exact Real.exp_le_exp.mpr (by nlinarith)
    have hEb := Real.exp_pos (-(b + 1) * t)
    have hEp := Real.exp_pos (c * |t|)
    have hcinv : 1 ≤ c⁻¹ := by rw [le_inv_comm₀ one_pos hc]; simpa using hc1
    constructor
    · calc (1 + |t|) * (Real.exp (q.re * t) * ‖airyAi t‖)
          ≤ (c⁻¹ * Real.exp (c * |t|)) * (Real.exp (q.re * t) * (Cp * Real.exp (-(b + 1) * t))) := by
            gcongr
        _ = c⁻¹ * Cp * (Real.exp (c * |t|) *
            (Real.exp (q.re * t) * Real.exp (-(b + 1) * t))) := by ring
        _ ≤ c⁻¹ * Cp * (Real.exp (c * |t|) * Real.exp (-t)) := by gcongr
        _ ≤ c⁻¹ * Cp * Real.exp (-c * |t|) := by gcongr
        _ ≤ _ := by gcongr; linarith
    · calc Real.exp (q.re * t) * ‖airyAiDeriv t‖
          ≤ Real.exp (q.re * t) * (Cp * Real.exp (-(b + 1) * t)) := by gcongr
        _ = Cp * (Real.exp (q.re * t) * Real.exp (-(b + 1) * t)) := by ring
        _ ≤ Cp * Real.exp (-c * |t|) := by gcongr; exact he.trans hk'
        _ ≤ 1 * (Cp + Cn) * Real.exp (-c * |t|) := by
            gcongr; linarith
        _ ≤ _ := by gcongr

/-- `e^{-c|t|}` is integrable on `ℝ` for `c > 0`. -/
theorem airyLap_integrable_exp_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => Real.exp (-c * |t|)) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-c * |t|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic hc 0).congr_fun (fun t ht => ?_) measurableSet_Iic
    simp only [mem_Iic] at ht
    rw [abs_of_nonpos ht]; ring_nf
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-c * |t|)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [mem_Ioi] at ht
    rw [abs_of_pos ht]
  have := h1.union h2
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- Continuity of `t ↦ Ai(t)` and `t ↦ Ai'(t)` on the real line. -/
theorem airyLap_continuous : Continuous (fun t : ℝ => airyAi t) ∧
    Continuous (fun t : ℝ => airyAiDeriv t) :=
  ⟨(differentiable_airyAi.continuous).comp continuous_ofReal,
    (continuous_iff_continuousAt.mpr fun z => (hasDerivAt_airyAiDeriv z).continuousAt).comp
      continuous_ofReal⟩

/-- Integrability of `e^{pt} Ai(t)` and `t e^{pt} Ai(t)` on `ℝ` for `Re p > 0`. -/
theorem airyLap_integrable {p : ℂ} (hp : 0 < p.re) :
    Integrable (fun t : ℝ => exp (p * t) * airyAi t) ∧
      Integrable (fun t : ℝ => (t : ℂ) * (exp (p * t) * airyAi t)) := by
  obtain ⟨K, hK0, hK⟩ := airyLap_dom hp p.re
  have hc : 0 < min p.re 1 / 2 := by positivity
  have hI := (airyLap_integrable_exp_abs hc).const_mul K
  have hm1 : Continuous fun t : ℝ => exp (p * t) * airyAi t := by
    have := airyLap_continuous.1; fun_prop
  constructor
  · refine hI.mono' hm1.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    have h := (hK p le_rfl le_rfl t).1
    have : ‖exp (p * t) * airyAi t‖ ≤ (1 + |t|) * ‖exp (p * t) * airyAi t‖ := by
      nlinarith [abs_nonneg t, norm_nonneg (exp (p * t) * airyAi t)]
    linarith
  · refine hI.mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
    have h := (hK p le_rfl le_rfl t).1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg t, norm_nonneg (exp (p * t) * airyAi t)]

/-- The bilateral Laplace transform `F(q) = ∫ e^{qt} Ai(t) dt`. -/
noncomputable def airyLapF (q : ℂ) : ℂ := ∫ t : ℝ, exp (q * t) * airyAi t

/-- `F` is differentiable on `Re q > 0`, with `F'(q) = ∫ t e^{qt} Ai(t) dt`. -/
theorem airyLap_hasDerivAt {p : ℂ} (hp : 0 < p.re) :
    HasDerivAt airyLapF (∫ t : ℝ, (t : ℂ) * (exp (p * t) * airyAi t)) p := by
  obtain ⟨K, hK0, hK⟩ := airyLap_dom (a := p.re / 2) (by positivity) (3 * p.re / 2)
  have hc : 0 < min (p.re / 2) 1 / 2 := by positivity
  have hI := (airyLap_integrable_exp_abs hc).const_mul K
  have hball : Metric.ball p (p.re / 2) ∈ 𝓝 p := Metric.ball_mem_nhds p (by positivity)
  have hAc := airyLap_continuous.1
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) hball
    (F := fun q (t : ℝ) => exp (q * t) * airyAi t)
    (F' := fun q (t : ℝ) => (t : ℂ) * (exp (q * t) * airyAi t))
    (Eventually.of_forall fun q => (by fun_prop : Continuous fun t : ℝ =>
      exp (q * t) * airyAi t).aestronglyMeasurable)
    (airyLap_integrable hp).1
    ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) * (exp (p * t) * airyAi t)).aestronglyMeasurable)
    (Eventually.of_forall fun t q hq => ?_) hI
    (Eventually.of_forall fun t q _ => ?_)
  · exact h.2
  · have hd : |q.re - p.re| < p.re / 2 := by
      have := Metric.mem_ball.mp hq
      rw [dist_eq_norm] at this
      calc |q.re - p.re| = |(q - p).re| := by simp
        _ ≤ ‖q - p‖ := Complex.abs_re_le_norm _
        _ < _ := this
    have hd' := abs_lt.mp hd
    have h1 := (hK q (by linarith) (by linarith) t).1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg t, norm_nonneg (exp (q * t) * airyAi t)]
  · have := (((hasDerivAt_id' q).mul_const (t : ℂ)).cexp).mul_const (airyAi t)
    convert this using 1
    ring

/-- The antiderivative `e^{pt}(Ai'(t) - p Ai(t))` of `e^{pt}(t - p²) Ai(t)`. -/
theorem airyLap_hasDerivAt_g (p : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => exp (p * t) * (airyAiDeriv t - p * airyAi t))
      (exp (p * t) * (((t : ℂ) - p ^ 2) * airyAi t)) t := by
  have he : HasDerivAt (fun t : ℝ => exp (p * t)) (exp (p * t) * p) t := by
    have := ((hasDerivAt_id (t : ℂ)).const_mul p).cexp.comp_ofReal
    simpa using this
  have hA : HasDerivAt (fun t : ℝ => airyAi t) (airyAiDeriv t) t :=
    (hasDerivAt_airyAi (t : ℂ)).comp_ofReal
  have hD : HasDerivAt (fun t : ℝ => airyAiDeriv t) ((t : ℂ) * airyAi t) t :=
    (hasDerivAt_airyAiDeriv (t : ℂ)).comp_ofReal
  convert he.mul (hD.sub (hA.const_mul p)) using 1
  simp only [Pi.sub_apply]; ring

/-- **The transform equation**: `∫ t e^{pt} Ai(t) dt = p² F(p)` for `Re p > 0`. -/
theorem airyLap_moment {p : ℂ} (hp : 0 < p.re) :
    (∫ t : ℝ, (t : ℂ) * (exp (p * t) * airyAi t)) = p ^ 2 * airyLapF p := by
  obtain ⟨K, hK0, hK⟩ := airyLap_dom hp p.re
  set c := min p.re 1 / 2
  have hc : 0 < c := by positivity
  obtain ⟨i1, i2⟩ := airyLap_integrable hp
  have hint : Integrable fun t : ℝ => exp (p * t) * (((t : ℂ) - p ^ 2) * airyAi t) := by
    refine (i2.sub (i1.const_mul (p ^ 2))).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]; ring
  -- the antiderivative is `O(e^{-c|t|})`
  have hg : ∀ t : ℝ, ‖exp (p * t) * (airyAiDeriv t - p * airyAi t)‖ ≤
      (K + ‖p‖ * K) * Real.exp (-c * |t|) := by
    intro t
    obtain ⟨h1, h2⟩ := hK p le_rfl le_rfl t
    have h1' : ‖exp (p * t) * airyAi t‖ ≤ K * Real.exp (-c * |t|) := by
      nlinarith [abs_nonneg t, norm_nonneg (exp (p * t) * airyAi t)]
    calc ‖exp (p * t) * (airyAiDeriv t - p * airyAi t)‖
        = ‖exp (p * t) * airyAiDeriv t - p * (exp (p * t) * airyAi t)‖ := by ring_nf
      _ ≤ ‖exp (p * t) * airyAiDeriv t‖ + ‖p‖ * ‖exp (p * t) * airyAi t‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ K * Real.exp (-c * |t|) + ‖p‖ * (K * Real.exp (-c * |t|)) := by gcongr
      _ = _ := by ring
  have hdec : ∀ l : Filter ℝ, Tendsto (fun t : ℝ => |t|) l atTop →
      Tendsto (fun t : ℝ => exp (p * t) * (airyAiDeriv t - p * airyAi t)) l (𝓝 0) := by
    intro l hl
    have h0 : Tendsto (fun t : ℝ => (K + ‖p‖ * K) * Real.exp (-c * |t|)) l (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp ((tendsto_const_nhds (x := -c)).neg_mul_atTop
        (by linarith) hl |>.congr' (Eventually.of_forall fun t => rfl)))
      simpa using this.const_mul (K + ‖p‖ * K)
    exact squeeze_zero_norm hg h0
  have hftc := integral_of_hasDerivAt_of_tendsto (fun t => airyLap_hasDerivAt_g p t) hint
    (hdec atBot tendsto_abs_atBot_atTop) (hdec atTop tendsto_abs_atTop_atTop)
  have e : (fun t : ℝ => exp (p * t) * (((t : ℂ) - p ^ 2) * airyAi t)) =
      fun t : ℝ => (t : ℂ) * (exp (p * t) * airyAi t) - p ^ 2 * (exp (p * t) * airyAi t) := by
    funext t; ring
  rw [e, integral_sub i2 (i1.const_mul _), integral_const_mul, sub_self] at hftc
  rw [airyLapF]
  exact sub_eq_zero.mp hftc

/-- **Constancy**: `F(q) e^{-q³/3}` is constant on `Re q > 0`. -/
theorem airyLap_const {p q : ℂ} (hp : 0 < p.re) (hq : 0 < q.re) :
    airyLapF p * exp (-p ^ 3 / 3) = airyLapF q * exp (-q ^ 3 / 3) := by
  set U := {c : ℂ | 0 < c.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hD : ∀ z ∈ U, HasDerivAt (fun q => airyLapF q * exp (-q ^ 3 / 3)) 0 z := by
    intro z hz
    have h1 := airyLap_hasDerivAt hz
    rw [airyLap_moment hz] at h1
    have h2 : HasDerivAt (fun q : ℂ => exp (-q ^ 3 / 3)) (exp (-z ^ 3 / 3) * (-z ^ 2)) z := by
      have := (((hasDerivAt_pow 3 z).neg).div_const 3).cexp
      convert this using 1; simp only [Pi.neg_apply]; ring
    convert h1.mul h2 using 1; ring
  exact hU.is_const_of_deriv_eq_zero (convex_halfSpace_re_gt 0).isPreconnected
    (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hD z hz).deriv) hp hq

/-- `∫₀^∞ Ai = 1/3` as a Lebesgue integral, with integrability. -/
theorem airyLap_integral_Ioi :
    IntegrableOn (fun t : ℝ => airyAi t) (Ioi 0) ∧ (∫ t : ℝ in Ioi 0, airyAi t) = 1 / 3 := by
  obtain ⟨C, hC0, hC⟩ := airyLap_pos_bound 1
  have hi : IntegrableOn (fun t : ℝ => airyAi t) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul C).mono'
      airyLap_continuous.1.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    exact (hC t (le_of_lt ht)).1
  refine ⟨hi, tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id) ?_⟩
  exact airyAi_positive_integral

/-- **Positive half of the Abelian limit**: `∫₀^∞ e^{xt} Ai(t) dt → 1/3` as `x → 0+`. -/
theorem airyLap_pos_tendsto :
    Tendsto (fun x : ℝ => ∫ t : ℝ in Ioi 0, exp ((x : ℂ) * t) * airyAi t) (𝓝[>] 0)
      (𝓝 (1 / 3)) := by
  obtain ⟨C, hC0, hC⟩ := airyLap_pos_bound 2
  rw [← airyLap_integral_Ioi.2]
  refine tendsto_integral_filter_of_dominated_convergence (fun t => C * Real.exp (-1 * t)) ?_ ?_
    ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul C) ?_
  · refine Eventually.of_forall fun x => ?_
    have := airyLap_continuous.1
    exact (by fun_prop : Continuous fun t : ℝ => exp ((x : ℂ) * t) * airyAi t).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [norm_mul, show ((x : ℂ) * t) = ((x * t : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    have h1 : Real.exp (x * t) ≤ Real.exp t := Real.exp_le_exp.mpr (by nlinarith [hx.2])
    calc Real.exp (x * t) * ‖airyAi t‖ ≤ Real.exp t * (C * Real.exp (-2 * t)) := by
          gcongr; exact (hC t ht0).1
      _ = C * Real.exp (-1 * t) := by rw [mul_left_comm, ← Real.exp_add]; ring_nf
  · refine Eventually.of_forall fun t => ?_
    have : Tendsto (fun x : ℝ => exp ((x : ℂ) * t) * airyAi t) (𝓝 0)
        (𝓝 (exp (((0 : ℝ) : ℂ) * t) * airyAi t)) := by
      have := airyLap_continuous.1; exact ((by fun_prop : Continuous fun x : ℝ =>
        exp ((x : ℂ) * t) * airyAi t).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds

/-- The running integral `A(s) = ∫₀^s Ai(-u) du`. -/
noncomputable def airyLapA (s : ℝ) : ℂ := ∫ u : ℝ in 0..s, airyAi (-(u : ℂ))

/-- `A(s) → 2/3` as `s → ∞` (DLMF 9.10.11), and `A' = Ai(-s)`. -/
theorem airyLapA_tendsto : Tendsto airyLapA atTop (𝓝 (2 / 3)) := by
  have h := airyAi_negative_integral.comp tendsto_neg_atTop_atBot
  refine h.congr fun s => ?_
  simp only [Function.comp, airyLapA]
  have := intervalIntegral.integral_comp_neg (a := 0) (b := s) (fun u : ℝ => airyAi (u : ℂ))
  simp only [ofReal_neg, neg_zero] at this
  exact this.symm

/-- The running integral `A(s) = ∫₀^s Ai(-u) du` has derivative `Ai(-s)`. -/
theorem airyLapA_hasDerivAt (s : ℝ) : HasDerivAt airyLapA (airyAi (-(s : ℂ))) s := by
  have hc : Continuous fun u : ℝ => airyAi (-(u : ℂ)) :=
    differentiable_airyAi.continuous.comp (continuous_ofReal.neg)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

/-- `A` is bounded on `[0, ∞)`. -/
theorem airyLapA_bound : ∃ M, 0 ≤ M ∧ ∀ s : ℝ, 0 ≤ s → ‖airyLapA s‖ ≤ M := by
  have hcont : Continuous airyLapA :=
    continuous_iff_continuousAt.mpr fun s => (airyLapA_hasDerivAt s).continuousAt
  obtain ⟨S, hS⟩ := eventually_atTop.1 (airyLapA_tendsto.norm.eventually
    (gt_mem_nhds (show ‖(2 / 3 : ℂ)‖ < ‖(2 / 3 : ℂ)‖ + 1 by linarith)))
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := S)).exists_bound_of_continuousOn
    hcont.norm.continuousOn
  refine ⟨max K 0 + ‖(2 / 3 : ℂ)‖ + 1, by positivity, fun s hs => ?_⟩
  rcases le_or_gt s S with h | h
  · have := hK s ⟨hs, h⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
    have := le_max_left K 0
    linarith [norm_nonneg (2 / 3 : ℂ)]
  · have := hS s h.le
    linarith [le_max_right K 0]

/-- For `x > 0`, integration by parts and `u = xs` give
`∫_{-∞}^0 e^{xt} Ai(t) dt = ∫₀^∞ e^{-u} A(u/x) du`, with `A(s) = ∫₀^s Ai(-v) dv`. -/
private lemma airyLap_neg_eq_integral_A {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in Iic 0, exp ((x : ℂ) * t) * airyAi t) =
      ∫ u : ℝ in Ioi 0, (Real.exp (-u) : ℂ) * airyLapA (u / x) := by
  obtain ⟨M, hM0, hM⟩ := airyLapA_bound
  obtain ⟨Cn, hCn0, hCn⟩ := airyLap_neg_bound
  have hAc : Continuous airyLapA :=
    continuous_iff_continuousAt.mpr fun s => (airyLapA_hasDerivAt s).continuousAt
  rw [show (Iic (0 : ℝ)) = Iic (-0) by simp, ← integral_comp_neg_Ioi]
  -- integration by parts
  have hu : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt (fun s : ℝ => (Real.exp (-x * s) : ℂ))
      (((-x * Real.exp (-x * s) : ℝ)) : ℂ) s := by
    intro s _
    have := (((hasDerivAt_id' s).const_mul (-x)).exp).ofReal_comp
    refine this.congr_deriv ?_
    congr 1; ring
  have hv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt airyLapA (airyAi (-(s : ℂ))) s :=
    fun s _ => airyLapA_hasDerivAt s
  have hint1 : IntegrableOn (fun s : ℝ => (Real.exp (-x * s) : ℂ) * airyAi (-(s : ℂ))) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 hx).const_mul Cn).mono'
      (by have := differentiable_airyAi.continuous; fun_prop : Continuous fun s : ℝ =>
        (Real.exp (-x * s) : ℂ) * airyAi (-(s : ℂ))).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
    have := (hCn (-s) (by linarith [mem_Ioi.mp hs])).1
    push_cast at this
    gcongr
  have hint2 : IntegrableOn (fun s : ℝ => (((-x * Real.exp (-x * s) : ℝ)) : ℂ) * airyLapA s)
      (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 hx).const_mul (x * M)).mono'
      (by fun_prop : Continuous fun s : ℝ =>
        (((-x * Real.exp (-x * s) : ℝ)) : ℂ) * airyLapA s).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hx,
      abs_of_pos (Real.exp_pos _)]
    have := hM s (le_of_lt hs)
    have h0 := Real.exp_pos (-x * s)
    calc x * Real.exp (-x * s) * ‖airyLapA s‖ ≤ x * Real.exp (-x * s) * M := by gcongr
      _ = _ := by ring
  have h0 : Tendsto ((fun s : ℝ => (Real.exp (-x * s) : ℂ)) * airyLapA) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto ((fun s : ℝ => (Real.exp (-x * s) : ℂ)) * airyLapA) (𝓝 0)
        (𝓝 ((Real.exp (-x * 0) : ℂ) * airyLapA 0)) :=
      ((by fun_prop : Continuous fun s : ℝ => (Real.exp (-x * s) : ℂ)).mul hAc).tendsto 0
    simpa [airyLapA] using this.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto ((fun s : ℝ => (Real.exp (-x * s) : ℂ)) * airyLapA) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => (Real.exp (-x * s) : ℂ)) atTop (𝓝 0) := by
      have hr : Tendsto (fun s : ℝ => Real.exp (-x * s)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
      have := (Complex.continuous_ofReal.tendsto 0).comp hr
      rw [Complex.ofReal_zero] at this
      exact this
    have := h1.mul airyLapA_tendsto
    rw [zero_mul] at this
    exact this
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hint1 hint2 h0 hinf
  have e1 : (∫ s : ℝ in Ioi 0, exp ((x : ℂ) * ((-s : ℝ) : ℂ)) * airyAi ((-s : ℝ) : ℂ)) =
      ∫ s : ℝ in Ioi 0, (Real.exp (-x * s) : ℂ) * airyAi (-(s : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [ofReal_exp, ofReal_mul, ofReal_neg]; ring_nf
  rw [e1, hibp, sub_zero, zero_sub]
  -- the substitution `u = x s`
  have e2 := integral_comp_mul_left_Ioi
    (fun u : ℝ => (Real.exp (-u) : ℂ) * airyLapA (u / x)) 0 hx
  simp only [mul_zero] at e2
  have e3 : (∫ s : ℝ in Ioi 0, (Real.exp (-(x * s)) : ℂ) * airyLapA (x * s / x)) =
      ∫ s : ℝ in Ioi 0, (Real.exp (-x * s) : ℂ) * airyLapA s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [mul_div_cancel_left₀ _ hx.ne', neg_mul]
  rw [e3] at e2
  have e4 : (∫ s : ℝ in Ioi 0, (((-x * Real.exp (-x * s) : ℝ)) : ℂ) * airyLapA s) =
      (-x : ℂ) * ∫ s : ℝ in Ioi 0, (Real.exp (-x * s) : ℂ) * airyLapA s := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    push_cast; ring
  rw [e4, e2, Complex.real_smul]
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  push_cast
  field_simp

/-- Dominated convergence: `∫₀^∞ e^{-u} A(u/x) du → ∫₀^∞ e^{-u} (2/3) du` as `x → 0+`. -/
private lemma airyLap_integral_A_tendsto :
    Tendsto (fun x : ℝ => ∫ u : ℝ in Ioi 0, (Real.exp (-u) : ℂ) * airyLapA (u / x))
      (𝓝[>] 0) (𝓝 (∫ u : ℝ in Ioi 0, (Real.exp (-u) : ℂ) * (2 / 3))) := by
  obtain ⟨M, hM0, hM⟩ := airyLapA_bound
  have hAc : Continuous airyLapA :=
    continuous_iff_continuousAt.mpr fun s => (airyLapA_hasDerivAt s).continuousAt
  refine tendsto_integral_filter_of_dominated_convergence (fun u => M * Real.exp (-1 * u)) ?_ ?_
    ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul M) ?_
  · refine Eventually.of_forall fun x => ?_
    exact ((by fun_prop : Continuous fun u : ℝ => (Real.exp (-u) : ℂ)).mul
      (hAc.comp (by fun_prop : Continuous fun u : ℝ => u / x))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with x hx
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm,
      neg_one_mul]
    gcongr
    exact hM _ (div_nonneg (le_of_lt hu) (le_of_lt hx))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    refine Tendsto.const_mul _ (airyLapA_tendsto.comp ?_)
    have := tendsto_inv_nhdsGT_zero.const_mul_atTop (mem_Ioi.mp hu)
    exact this.congr fun x => by simp [div_eq_mul_inv]

/-- **Negative half of the Abelian limit**: `∫₋∞^0 e^{xt} Ai(t) dt → 2/3` as `x → 0+`. -/
theorem airyLap_neg_tendsto :
    Tendsto (fun x : ℝ => ∫ t : ℝ in Iic 0, exp ((x : ℂ) * t) * airyAi t) (𝓝[>] 0)
      (𝓝 (2 / 3)) := by
  have hlim := airyLap_integral_A_tendsto
  have hv : (∫ u : ℝ in Ioi 0, (Real.exp (-u) : ℂ) * (2 / 3)) = 2 / 3 := by
    rw [integral_mul_const, integral_complex_ofReal, integral_exp_neg_Ioi_zero]; simp
  rw [hv] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (airyLap_neg_eq_integral_A hx).symm

/-- **The Abelian limit**: `F(x) → 1` as `x → 0+`. -/
theorem airyLap_tendsto_zero :
    Tendsto (fun x : ℝ => airyLapF x) (𝓝[>] 0) (𝓝 1) := by
  have h := airyLap_neg_tendsto.add airyLap_pos_tendsto
  rw [show (2 / 3 + 1 / 3 : ℂ) = 1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hi := (airyLap_integrable (p := (x : ℂ)) (by simpa using hx)).1
  have e := setIntegral_union (Iic_disjoint_Ioi (a := (0 : ℝ)) le_rfl) measurableSet_Ioi
    hi.integrableOn hi.integrableOn
  rw [Iic_union_Ioi, setIntegral_univ] at e
  rw [airyLapF, e]

/-- **9.10.13 (proof)**: `∫ e^{pt} Ai(t) dt = e^{p³/3}` for `Re p > 0`. -/
theorem airyLap_bilateral {p : ℂ} (hp : 0 < p.re) : airyLapF p = exp (p ^ 3 / 3) := by
  have hH : Tendsto (fun x : ℝ => airyLapF x * exp (-(x : ℂ) ^ 3 / 3)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Tendsto (fun x : ℝ => exp (-(x : ℂ) ^ 3 / 3)) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun x : ℝ => exp (-(x : ℂ) ^ 3 / 3)) (𝓝 0)
          (𝓝 (exp (-((0 : ℝ) : ℂ) ^ 3 / 3))) :=
        ((by fun_prop : Continuous fun x : ℝ => exp (-(x : ℂ) ^ 3 / 3)).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    simpa using airyLap_tendsto_zero.mul hc
  have hconst : Tendsto (fun x : ℝ => airyLapF x * exp (-(x : ℂ) ^ 3 / 3)) (𝓝[>] 0)
      (𝓝 (airyLapF p * exp (-p ^ 3 / 3))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact airyLap_const hp (by simpa using hx)
  have h1 := tendsto_nhds_unique hconst hH
  have : airyLapF p = airyLapF p * exp (-p ^ 3 / 3) * exp (p ^ 3 / 3) := by
    rw [mul_assoc, ← Complex.exp_add]; ring_nf; simp
  rw [this, h1, one_mul]

end AiryLaplace

/-- For `Re p > 0`, `t ↦ e^{pt} Ai(t)` is integrable on `ℝ` and `∫ e^{pt} Ai(t) dt = e^{p³/3}` (DLMF
9.10.13). -/
@[dlmf 9.10.E13]
theorem airyAi_bilateral_laplace {p : ℂ} (hp : 0 < p.re) :
    Integrable (fun t : ℝ => exp (p * t) * airyAi t) ∧
      (∫ t : ℝ, exp (p * t) * airyAi t) = exp (p ^ 3 / 3) :=
  ⟨(airyLap_integrable hp).1, airyLap_bilateral hp⟩

end DLMF.Airy
end
