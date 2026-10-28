/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Scorer
public import DLMF.Airy.IntegralTools
public import DLMF.IncompleteGamma.Basic
public import DLMFMathlib.Analysis.Integral.PrincipalValue
public import DLMF.Bessel.KMellin
public import DLMFMathlib.Analysis.Complex.NonInteger

/-!
# Airy indefinite integrals and transforms, DLMF §9.10

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
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

/-! ### The one-sided Laplace transform 9.10.14 -/

section AiryLaplaceOneSided
open scoped Nat

/-- `(a)_{n+1} = a (a+1)_n`. -/
theorem airyLap_poch_succ_left (a : ℂ) (n : ℕ) : poch a (n + 1) = a * poch (a + 1) n := by
  simp [poch, ascPochhammer_succ_left, Polynomial.eval_comp]

/-- The coefficients of `M(a, a+1, z)`: `a / ((a + n) n!)`. -/
theorem airyLap_coeff {a : ℂ} (ha : 0 < a.re) (n : ℕ) :
    kummerMCoeff a (a + 1) n = a / ((a + n) * n !) := by
  have h1 : poch (a + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat
    (Hypergeometric.not_neg_nat_of_re_pos (by simp; linarith)) n
  have h2 := Complex.add_natCast_ne_zero_of_re_pos ha n
  have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have e : poch a n * (a + n) = a * poch (a + 1) n := by
    rw [← poch_succ, airyLap_poch_succ_left]
  simp only [kummerMCoeff]
  rw [div_eq_div_iff (mul_ne_zero h1 hf) (mul_ne_zero h2 hf)]
  linear_combination (n ! : ℂ) * e

/-- **The Kummer identity behind `∫₀ᶻ t^{a-1} e^t dt`**:
`a M(a,a+1,z) + z (a/(a+1)) M(a+1,a+2,z) = a e^z` for `Re a > 0`. -/
theorem airyLap_kummer_identity {a : ℂ} (ha : 0 < a.re) (z : ℂ) :
    a * kummerM a (a + 1) z + z * (a / (a + 1) * kummerM (a + 1) (a + 1 + 1) z) =
      a * exp z := by
  have ha1 : 0 < (a + 1).re := by simp; linarith
  have ha2 : 0 < (a + 1 + 1).re := by simp; linarith
  have S1 := (hasSum_kummerM (a := a) (Hypergeometric.not_neg_nat_of_re_pos ha1) z).mul_left a
  have S2 := ((hasSum_kummerM (a := a + 1) (Hypergeometric.not_neg_nat_of_re_pos ha2) z).mul_left
    (z * (a / (a + 1))))
  set g : ℕ → ℂ := fun n => if n = 0 then 0 else
    z * (a / (a + 1)) * (kummerMCoeff (a + 1) (a + 1 + 1) (n - 1) * z ^ (n - 1))
  have S2' : HasSum g (z * (a / (a + 1) * kummerM (a + 1) (a + 1 + 1) z)) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [g, mul_assoc] using S2
  have hexp : HasSum (fun n : ℕ => a * (z ^ n / n !)) (a * exp z) := by
    have := NormedSpace.expSeries_div_hasSum_exp z
    simpa only [exp_eq_exp_ℂ] using this.mul_left a
  refine (S1.add S2').unique (hexp.congr_fun fun n => ?_)
  rcases n with _ | m
  · simp [g, kummerMCoeff, poch]
  · simp only [g, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [airyLap_coeff ha, show a + 1 + 1 = (a + 1) + 1 by ring, airyLap_coeff ha1]
    have h1 := Complex.add_natCast_ne_zero_of_re_pos ha (m + 1)
    have h2 := Complex.add_natCast_ne_zero_of_re_pos ha1 m
    have ha0 : a + 1 ≠ 0 := by simpa using Complex.add_natCast_ne_zero_of_re_pos ha 1
    have hf : (m ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    rw [Nat.factorial_succ]
    push_cast at h1 h2 ⊢
    have e : a + 1 + m = a + (m + 1) := by ring
    rw [e] at h2 ⊢
    field_simp
    ring

/-- `d/dp [p M(1/3, 4/3, p³/3)] = e^{p³/3}`. -/
theorem airyLap_hasDerivAt_E1 (p : ℂ) :
    HasDerivAt (fun p : ℂ => p * kummerM (1 / 3) (4 / 3) (p ^ 3 / 3)) (exp (p ^ 3 / 3)) p := by
  have ha : (0 : ℝ) < (1 / 3 : ℂ).re := by norm_num
  have hb : ∀ k : ℕ, (4 / 3 : ℂ) ≠ -k := Hypergeometric.not_neg_nat_of_re_pos (by norm_num)
  have hK := (hasDerivAt_kummerM_shift (a := 1 / 3) hb (p ^ 3 / 3)).comp p
    ((hasDerivAt_pow 3 p).div_const 3)
  have h : HasDerivAt (fun p : ℂ => p * kummerM (1 / 3) (4 / 3) (p ^ 3 / 3))
      (1 * kummerM (1 / 3) (4 / 3) (p ^ 3 / 3) +
        p * (1 / 3 / (4 / 3) * kummerM (1 / 3 + 1) (4 / 3 + 1) (p ^ 3 / 3) *
          (((3 : ℕ) : ℂ) * p ^ (3 - 1) / 3))) p := (hasDerivAt_id' p).mul hK
  have hid := airyLap_kummer_identity ha (p ^ 3 / 3)
  rw [show (1 / 3 : ℂ) + 1 = 4 / 3 by norm_num] at hid h
  refine h.congr_deriv ?_
  simp only [show (3 : ℕ) - 1 = 2 from rfl]
  push_cast
  linear_combination (3 : ℂ) * hid

/-- `d/dp [p² M(2/3, 5/3, p³/3) / 2] = p e^{p³/3}`. -/
theorem airyLap_hasDerivAt_E2 (p : ℂ) :
    HasDerivAt (fun p : ℂ => p ^ 2 * kummerM (2 / 3) (5 / 3) (p ^ 3 / 3) / 2)
      (p * exp (p ^ 3 / 3)) p := by
  have ha : (0 : ℝ) < (2 / 3 : ℂ).re := by norm_num
  have hb : ∀ k : ℕ, (5 / 3 : ℂ) ≠ -k := Hypergeometric.not_neg_nat_of_re_pos (by norm_num)
  have hK := (hasDerivAt_kummerM_shift (a := 2 / 3) hb (p ^ 3 / 3)).comp p
    ((hasDerivAt_pow 3 p).div_const 3)
  have h : HasDerivAt (fun p : ℂ => p ^ 2 * kummerM (2 / 3) (5 / 3) (p ^ 3 / 3) / 2)
      ((((2 : ℕ) : ℂ) * p ^ (2 - 1) * kummerM (2 / 3) (5 / 3) (p ^ 3 / 3) +
        p ^ 2 * (2 / 3 / (5 / 3) * kummerM (2 / 3 + 1) (5 / 3 + 1) (p ^ 3 / 3) *
          (((3 : ℕ) : ℂ) * p ^ (3 - 1) / 3))) / 2) p := ((hasDerivAt_pow 2 p).mul hK).div_const 2
  have hid := airyLap_kummer_identity ha (p ^ 3 / 3)
  rw [show (2 / 3 : ℂ) + 1 = 5 / 3 by norm_num] at hid h
  refine h.congr_deriv ?_
  simp only [show (3 : ℕ) - 1 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl]
  push_cast
  linear_combination (3 / 2 * p : ℂ) * hid

/-- Domination on the positive axis: for `‖q‖ ≤ R` and `t ≥ 0`,
`(1 + t) |e^{-qt} Ai(t)|` and `|e^{-qt} Ai'(t)|` are at most `K e^{-t}`. -/
theorem airyLap_pos_dom (R : ℝ) : ∃ K, 0 ≤ K ∧ ∀ q : ℂ, ‖q‖ ≤ R → ∀ t : ℝ, 0 ≤ t →
    (1 + t) * ‖exp (-q * t) * airyAi t‖ ≤ K * Real.exp (-t) ∧
      ‖exp (-q * t) * airyAiDeriv t‖ ≤ K * Real.exp (-t) := by
  obtain ⟨C, hC0, hC⟩ := airyLap_pos_bound (R + 2)
  refine ⟨C, hC0, fun q hq t ht => ?_⟩
  obtain ⟨hA, hD⟩ := hC t ht
  have hre : -q.re * t ≤ R * t := by
    have := Complex.abs_re_le_norm q
    have := abs_le.mp (this.trans hq)
    nlinarith
  have hn : ‖exp (-q * t)‖ ≤ Real.exp (R * t) := by
    rw [airyLap_norm_exp]; exact Real.exp_le_exp.mpr (by simpa using hre)
  have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have e1 : Real.exp (R * t) * Real.exp (-(R + 2) * t) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have he := Real.exp_pos (-t)
  have hle : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  rw [norm_mul, norm_mul]
  constructor
  · calc (1 + t) * (‖exp (-q * t)‖ * ‖airyAi t‖)
        ≤ Real.exp t * (Real.exp (R * t) * (C * Real.exp (-(R + 2) * t))) := by gcongr
      _ = C * (Real.exp t * Real.exp (-t)) * Real.exp (-t) := by
          rw [show Real.exp t * (Real.exp (R * t) * (C * Real.exp (-(R + 2) * t))) =
            C * Real.exp t * (Real.exp (R * t) * Real.exp (-(R + 2) * t)) by ring, e1]; ring
      _ = C * Real.exp (-t) := by rw [hE, mul_one]
  · calc ‖exp (-q * t)‖ * ‖airyAiDeriv t‖
        ≤ Real.exp (R * t) * (C * Real.exp (-(R + 2) * t)) := by gcongr
      _ = C * Real.exp (-t) * Real.exp (-t) := by rw [mul_left_comm, e1]; ring
      _ ≤ C * Real.exp (-t) * 1 := by gcongr
      _ = _ := mul_one _

/-- The one-sided Laplace transform `L(p) = ∫₀^∞ e^{-pt} Ai(t) dt`. -/
noncomputable def airyLapL (p : ℂ) : ℂ := ∫ t : ℝ in Ioi 0, exp (-p * t) * airyAi t

/-- Integrability of `e^{-pt} Ai(t)` and `t e^{-pt} Ai(t)` on `(0, ∞)`, for every `p`. -/
theorem airyLap_integrableOn (p : ℂ) :
    IntegrableOn (fun t : ℝ => exp (-p * t) * airyAi t) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => (t : ℂ) * (exp (-p * t) * airyAi t)) (Ioi 0) := by
  obtain ⟨K, hK0, hK⟩ := airyLap_pos_dom ‖p‖
  have hI := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul K
  have hAc := airyLap_continuous.1
  constructor
  · refine hI.mono' (by fun_prop : Continuous fun t : ℝ =>
      exp (-p * t) * airyAi t).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have h := (hK p le_rfl t (le_of_lt ht)).1
    have ht0 : (0 : ℝ) < t := ht
    simp only [neg_mul, one_mul] at h ⊢
    nlinarith [norm_nonneg (exp (-(p * t)) * airyAi t)]
  · refine hI.mono' (by fun_prop : Continuous fun t : ℝ =>
      (t : ℂ) * (exp (-p * t) * airyAi t)).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have h := (hK p le_rfl t (le_of_lt ht)).1
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    simp only [neg_mul, one_mul] at h ⊢
    nlinarith [norm_nonneg (exp (-(p * t)) * airyAi t)]

/-- `L'(p) = -∫₀^∞ t e^{-pt} Ai(t) dt`. -/
theorem airyLapL_hasDerivAt (p : ℂ) :
    HasDerivAt airyLapL (-∫ t : ℝ in Ioi 0, (t : ℂ) * (exp (-p * t) * airyAi t)) p := by
  obtain ⟨K, hK0, hK⟩ := airyLap_pos_dom (‖p‖ + 1)
  have hI := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul K
  have hball : Metric.ball p 1 ∈ 𝓝 p := Metric.ball_mem_nhds p one_pos
  have hAc := airyLap_continuous.1
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0)) hball
    (F := fun q (t : ℝ) => exp (-q * t) * airyAi t)
    (F' := fun q (t : ℝ) => -((t : ℂ) * (exp (-q * t) * airyAi t)))
    (Eventually.of_forall fun q => (by fun_prop : Continuous fun t : ℝ =>
      exp (-q * t) * airyAi t).aestronglyMeasurable)
    (airyLap_integrableOn p).1
    ((by fun_prop : Continuous fun t : ℝ =>
      -((t : ℂ) * (exp (-p * t) * airyAi t))).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht q hq => ?_)) hI
    (Eventually.of_forall fun t q _ => ?_)
  · rw [integral_neg] at h
    exact h.2
  · have hq' : ‖q‖ ≤ ‖p‖ + 1 := by
      have := Metric.mem_ball.mp hq
      rw [dist_eq_norm] at this
      have := norm_sub_norm_le q p
      linarith
    have h1 := (hK q hq' t (le_of_lt ht)).1
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le, neg_one_mul]
    nlinarith [norm_nonneg (exp (-q * t) * airyAi t)]
  · have := (((hasDerivAt_id' q).neg.mul_const (t : ℂ)).cexp).mul_const (airyAi t)
    simp only [Pi.neg_apply] at this
    refine this.congr_deriv ?_
    ring

/-- **The transform equation**: `L'(p) = -p² L(p) + Ai'(0) + p Ai(0)`. -/
theorem airyLapL_ode (p : ℂ) :
    HasDerivAt airyLapL (-p ^ 2 * airyLapL p + airyAiDeriv 0 + p * airyAi 0) p := by
  obtain ⟨K, hK0, hK⟩ := airyLap_pos_dom ‖p‖
  obtain ⟨i1, i2⟩ := airyLap_integrableOn p
  have hint : IntegrableOn (fun t : ℝ => exp (-p * t) * (((t : ℂ) - p ^ 2) * airyAi t)) (Ioi 0) := by
    refine (i2.sub (i1.const_mul (p ^ 2))).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]; ring
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => exp (-p * t) * (airyAiDeriv t + p * airyAi t))
      (exp (-p * t) * (((t : ℂ) - p ^ 2) * airyAi t)) t := by
    intro t
    have := airyLap_hasDerivAt_g (-p) t
    convert this using 1
    · funext t; ring_nf
    · ring
  have hlim : Tendsto (fun t : ℝ => exp (-p * t) * (airyAiDeriv t + p * airyAi t)) atTop
      (𝓝 0) := by
    have hb : ∀ᶠ t : ℝ in atTop, ‖exp (-p * t) * (airyAiDeriv t + p * airyAi t)‖ ≤
        (K + ‖p‖ * K) * Real.exp (-t) := by
      filter_upwards [eventually_ge_atTop 0] with t ht
      obtain ⟨h1, h2⟩ := hK p le_rfl t ht
      have h1' : ‖exp (-p * t) * airyAi t‖ ≤ K * Real.exp (-t) := by
        nlinarith [norm_nonneg (exp (-p * t) * airyAi t)]
      calc ‖exp (-p * t) * (airyAiDeriv t + p * airyAi t)‖
          = ‖exp (-p * t) * airyAiDeriv t + p * (exp (-p * t) * airyAi t)‖ := by ring_nf
        _ ≤ ‖exp (-p * t) * airyAiDeriv t‖ + ‖p‖ * ‖exp (-p * t) * airyAi t‖ := by
            rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ K * Real.exp (-t) + ‖p‖ * (K * Real.exp (-t)) := by gcongr
        _ = _ := by ring
    have h0 : Tendsto (fun t : ℝ => (K + ‖p‖ * K) * Real.exp (-t)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (K + ‖p‖ * K)
    exact squeeze_zero_norm' hb h0
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hg t) hint hlim
  have e : (fun t : ℝ => exp (-p * t) * (((t : ℂ) - p ^ 2) * airyAi t)) =
      fun t : ℝ => (t : ℂ) * (exp (-p * t) * airyAi t) - p ^ 2 * (exp (-p * t) * airyAi t) := by
    funext t; ring
  rw [e, integral_sub i2 (i1.const_mul _), integral_const_mul] at hftc
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, one_mul, zero_sub] at hftc
  refine (airyLapL_hasDerivAt p).congr_deriv ?_
  rw [airyLapL]
  linear_combination -hftc

/-- The closed form of 9.10.14 before rewriting the constants. -/
noncomputable def airyLapR (p : ℂ) : ℂ :=
  exp (-p ^ 3 / 3) * (1 / 3 + airyAiDeriv 0 * (p * kummerM (1 / 3) (4 / 3) (p ^ 3 / 3)) +
    airyAi 0 * (p ^ 2 * kummerM (2 / 3) (5 / 3) (p ^ 3 / 3) / 2))

/-- The closed form `R(p)` of 9.10.14 satisfies `R' = -p² R + Ai'(0) + p Ai(0)`, the equation
satisfied by the Laplace transform of `Ai`. -/
theorem airyLapR_ode (p : ℂ) :
    HasDerivAt airyLapR (-p ^ 2 * airyLapR p + airyAiDeriv 0 + p * airyAi 0) p := by
  have h2 : HasDerivAt (fun q : ℂ => exp (-q ^ 3 / 3)) (exp (-p ^ 3 / 3) * (-p ^ 2)) p := by
    have := (((hasDerivAt_pow 3 p).neg).div_const 3).cexp
    convert this using 1; simp only [Pi.neg_apply]; ring
  have h := h2.mul ((((airyLap_hasDerivAt_E1 p).const_mul (airyAiDeriv 0)).const_add (1 / 3)).add
    ((airyLap_hasDerivAt_E2 p).const_mul (airyAi 0)))
  refine h.congr_deriv ?_
  simp only [Pi.add_apply]
  rw [airyLapR]
  have : exp (-p ^ 3 / 3) * exp (p ^ 3 / 3) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  linear_combination (airyAiDeriv 0 + p * airyAi 0) * this

/-- **9.10.14 (proof)**: `L = R` by uniqueness for the first-order equation. -/
theorem airyLapL_eq (p : ℂ) : airyLapL p = airyLapR p := by
  set D : ℂ → ℂ := fun q => (airyLapL q - airyLapR q) * exp (q ^ 3 / 3)
  have hD : ∀ q, HasDerivAt D 0 q := by
    intro q
    have h3 : HasDerivAt (fun q : ℂ => exp (q ^ 3 / 3)) (exp (q ^ 3 / 3) * q ^ 2) q := by
      have := ((hasDerivAt_pow 3 q).div_const 3).cexp
      convert this using 1; ring
    have := ((airyLapL_ode q).sub (airyLapR_ode q)).mul h3
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply]
    ring
  have hc := is_const_of_deriv_eq_zero (fun q => (hD q).differentiableAt)
    (fun q => (hD q).deriv) p 0
  have h0 : D 0 = 0 := by
    simp only [D, airyLapL, airyLapR]
    simp only [neg_zero, zero_mul, Complex.exp_zero, one_mul, mul_zero,
      add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
      mul_one]
    rw [airyLap_integral_Ioi.2]; ring
  have hDp : D p = 0 := hc.trans h0
  have hE : exp (p ^ 3 / 3) ≠ 0 := Complex.exp_ne_zero _
  have := mul_eq_zero.mp hDp
  rcases this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hE

/-- `3^{4/3} Γ(4/3) = 3^{1/3} Γ(1/3)` and `3^{5/3} Γ(5/3) = 2 · 3^{2/3} Γ(2/3)`. -/
theorem airyLap_const_identities :
    (3 : ℂ) ^ (4 / 3 : ℂ) * Gamma (4 / 3) = (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * Gamma (1 / 3) ∧
      (3 : ℂ) ^ (5 / 3 : ℂ) * Gamma (5 / 3) =
        2 * ((((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) * Gamma (2 / 3)) := by
  have c1 : (3 : ℂ) ^ (4 / 3 : ℂ) = 3 * (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num), show (4 / 3 : ℂ) = 1 + ((1 / 3 : ℝ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
    push_cast; ring
  have c2 : (3 : ℂ) ^ (5 / 3 : ℂ) = 3 * (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num), show (5 / 3 : ℂ) = 1 + ((2 / 3 : ℝ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
    push_cast; ring
  have g1 : Gamma (4 / 3) = 1 / 3 * Gamma (1 / 3) := by
    rw [show (4 / 3 : ℂ) = 1 / 3 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]
  have g2 : Gamma (5 / 3) = 2 / 3 * Gamma (2 / 3) := by
    rw [show (5 / 3 : ℂ) = 2 / 3 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]
  rw [c1, c2, g1, g2]
  constructor <;> ring

/-- **9.10.14 (proof)** in the printed form. -/
theorem airyLap_laplace (p : ℂ) :
    (∫ t : ℝ in Ioi 0, exp (-p * t) * airyAi t) = exp (-p ^ 3 / 3) *
        (1 / 3 - p * kummerM (1 / 3) (4 / 3) (p ^ 3 / 3) /
          ((3 : ℂ) ^ (4 / 3 : ℂ) * Gamma (4 / 3)) +
          p ^ 2 * kummerM (2 / 3) (5 / 3) (p ^ 3 / 3) /
          ((3 : ℂ) ^ (5 / 3 : ℂ) * Gamma (5 / 3))) := by
  have h := airyLapL_eq p
  rw [airyLapL, airyLapR, airyAiDeriv_zero, airyAi_zero] at h
  rw [h, airyLap_const_identities.1, airyLap_const_identities.2]
  ring

end AiryLaplaceOneSided

/-- For every `p`, `∫₀^∞ e^{-pt} Ai(t) dt` converges and equals
`e^{-p³/3}(1/3 - p M(1/3, 4/3, p³/3)/(3^{4/3} Γ(4/3)) + p² M(2/3, 5/3, p³/3)/(3^{5/3} Γ(5/3)))`
(DLMF 9.10.14). -/
@[dlmf 9.10.E14]
theorem airyAi_laplace (p : ℂ) :
    IntegrableOn (fun t : ℝ => exp (-p * t) * airyAi t) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-p * t) * airyAi t) = exp (-p ^ 3 / 3) *
        (1 / 3 - p * kummerM (1 / 3) (4 / 3) (p ^ 3 / 3) /
          ((3 : ℂ) ^ (4 / 3 : ℂ) * Gamma (4 / 3)) +
          p ^ 2 * kummerM (2 / 3) (5 / 3) (p ^ 3 / 3) /
          ((3 : ℂ) ^ (5 / 3 : ℂ) * Gamma (5 / 3))) :=
  ⟨(airyLap_integrableOn p).1, airyLap_laplace p⟩

/-! ### The Laplace transform of `Ai(-t)`, 9.10.15 -/

section AiryLaplaceNeg

/-- The logarithmic-plane upper incomplete Gamma function through Kummer's function:
`Γ(a, e^w) = Γ(a) - e^{aw} M(a, a+1, -e^w)/a` on the whole logarithmic plane. -/
theorem airyLap_upperGamma_eq {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (w : ℂ) :
    airyUpperGammaOnLog a w = Gamma a - exp (a * w) * kummerM a (a + 1) (-exp w) / a := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  have h1 : airyUpperGammaOnLog a w = upperIncGammaOnLog a w := rfl
  rw [h1, upperIncGammaOnLog_eq_Gamma_sub ha w, lowerIncGammaOnLog]
  have hz : exp w ≠ 0 := Complex.exp_ne_zero w
  have hl := lowerIncGamma_eq_regularized ha (exp w)
  rw [regularizedConfluent_self_succ_neg, lowerIncGamma] at hl
  have hza : (exp w) ^ a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  have key : Gamma a * DLMF.Statistical.scIncGamma a (exp w) = kummerM a (a + 1) (-exp w) / a := by
    field_simp
    have := hl
    field_simp at this
    linear_combination -this
  linear_combination (-exp (a * w)) * key

/-- `e^{c(3 log p - log 3)} = p^{3c} / 3^c` style evaluations used for 9.10.15. -/
theorem airyLap_exp_w {p : ℂ} (hp : p ≠ 0) :
    exp (3 * log p - log 3) = p ^ 3 / 3 ∧
      exp (1 / 3 * (3 * log p - log 3)) = p / (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ∧
      exp (2 / 3 * (3 * log p - log 3)) = p ^ 2 / (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
  have h3 : ∀ r : ℝ, (((3 : ℝ) ^ r : ℝ) : ℂ) = exp (r * log 3) := by
    intro r
    rw [Real.rpow_def_of_pos (by norm_num), Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.ofReal_log (by norm_num)]
    push_cast; ring_nf
  have hl3 : exp (log 3) = (3 : ℂ) := Complex.exp_log (by norm_num)
  have hlp : exp (log p) = p := Complex.exp_log hp
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.exp_sub, show (3 : ℂ) * log p = (3 : ℕ) * log p by norm_num, Complex.exp_nat_mul,
      hlp, hl3]
  · rw [h3, show (1 / 3 : ℂ) * (3 * log p - log 3) = log p - ((1 / 3 : ℝ) : ℂ) * log 3 by
      push_cast; ring, Complex.exp_sub, hlp]
  · rw [h3, show (2 / 3 : ℂ) * (3 * log p - log 3) = (2 : ℕ) * log p - ((2 / 3 : ℝ) : ℂ) * log 3 by
      push_cast; ring, Complex.exp_sub, Complex.exp_nat_mul, hlp]

/-- `∫₀^∞ e^{-pt} Ai(-t) dt = e^{p³/3} - L(-p)` for `Re p > 0`, with integrability. -/
theorem airyLap_neg_eq {p : ℂ} (hp : 0 < p.re) :
    IntegrableOn (fun t : ℝ => exp (-p * t) * airyAi (-t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-p * t) * airyAi (-t)) = exp (p ^ 3 / 3) - airyLapL (-p) := by
  obtain ⟨Cn, hCn0, hCn⟩ := airyLap_neg_bound
  constructor
  · refine ((exp_neg_integrableOn_Ioi 0 hp).const_mul Cn).mono'
      (by have := differentiable_airyAi.continuous; fun_prop : Continuous fun t : ℝ =>
        exp (-p * t) * airyAi (-t)).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_mul, airyLap_norm_exp, mul_comm]
    have := (hCn (-t) (by linarith)).1
    push_cast at this
    have e : Real.exp ((-p).re * t) = Real.exp (-p.re * t) := by simp
    rw [e]
    gcongr
  · have hi := (airyLap_integrable hp).1
    have e := setIntegral_union (Iic_disjoint_Ioi (a := (0 : ℝ)) le_rfl) measurableSet_Ioi
      hi.integrableOn hi.integrableOn
    rw [Iic_union_Ioi, setIntegral_univ] at e
    have e2 : (∫ t : ℝ in Ioi 0, exp (-p * t) * airyAi (-t)) =
        ∫ t : ℝ in Iic 0, exp (p * t) * airyAi t := by
      rw [show (Iic (0 : ℝ)) = Iic (-0) by simp, ← integral_comp_neg_Ioi]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      push_cast; ring_nf
    have e3 : airyLapL (-p) = ∫ t : ℝ in Ioi 0, exp (p * t) * airyAi t := by
      rw [airyLapL]; simp only [neg_neg]
    rw [e2, e3, ← airyLap_bilateral hp, airyLapF, e]
    ring

/-- **9.10.15 (proof)**. -/
theorem airyLap_negative_laplace {p : ℂ} (hp : 0 < p.re) :
    (∫ t : ℝ in Ioi 0, exp (-p * t) * airyAi (-t)) = exp (p ^ 3 / 3) / 3 *
      (airyUpperGammaOnLog (1 / 3) (3 * log p - log 3) / Gamma (1 / 3) +
        airyUpperGammaOnLog (2 / 3) (3 * log p - log 3) / Gamma (2 / 3)) := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; simp at hp
  rw [(airyLap_neg_eq hp).2, airyLapL_eq, airyLapR, airyAiDeriv_zero, airyAi_zero]
  have h13 : ∀ n : ℕ, (1 / 3 : ℂ) ≠ -n := Hypergeometric.not_neg_nat_of_re_pos (by norm_num)
  have h23 : ∀ n : ℕ, (2 / 3 : ℂ) ≠ -n := Hypergeometric.not_neg_nat_of_re_pos (by norm_num)
  rw [airyLap_upperGamma_eq h13, airyLap_upperGamma_eq h23]
  obtain ⟨e0, e1, e2⟩ := airyLap_exp_w hp0
  rw [e0, e1, e2, show (1 / 3 : ℂ) + 1 = 4 / 3 by norm_num, show (2 / 3 : ℂ) + 1 = 5 / 3 by norm_num]
  have hg1 : Gamma (1 / 3 : ℂ) ≠ 0 := Complex.Gamma_ne_zero h13
  have hg2 : Gamma (2 / 3 : ℂ) ≠ 0 := Complex.Gamma_ne_zero h23
  have hr1 : (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have hr2 : (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  rw [show -(-p) ^ 3 / 3 = p ^ 3 / 3 by ring]
  field_simp
  ring

end AiryLaplaceNeg

/-- For `Re p > 0`, `∫₀^∞ e^{-pt} Ai(-t) dt` converges and equals
`(e^{p³/3}/3)(Γ(1/3, p³/3)/Γ(1/3) + Γ(2/3, p³/3)/Γ(2/3))`, with the incomplete Gamma functions
continued on the logarithmic plane (DLMF 9.10.15). -/
@[dlmf 9.10.E15]
theorem airyAi_negative_laplace {p : ℂ} (hp : 0 < p.re) :
    IntegrableOn (fun t : ℝ => exp (-p * t) * airyAi (-t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-p * t) * airyAi (-t)) = exp (p ^ 3 / 3) / 3 * (airyUpperGammaOnLog (1 / 3) (3 * log p - log 3) / Gamma (1 / 3) + airyUpperGammaOnLog (2 / 3) (3 * log p - log 3) / Gamma (2 / 3)) :=
  ⟨(airyLap_neg_eq hp).1, airyLap_negative_laplace hp⟩

/-! ### The Laplace transform of `Bi(-t)`, 9.10.16 -/

section AiryLaplaceNegBi

/-- `|Bi(-s)| ≤ C` and `|Bi'(-s)| ≤ C (1 + s)` for `s ≥ 0`. -/
theorem airyLapB_bound : ∃ C, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
    ‖airyBi (-(s : ℂ))‖ ≤ C ∧ ‖airyBiDeriv (-(s : ℂ))‖ ≤ C * (1 + s) := by
  obtain ⟨c1, hc1⟩ := airyInt_bi_neg_isBigO.bound
  obtain ⟨c2, hc2⟩ := airyInt_biDeriv_neg_isBigO.bound
  obtain ⟨S, hS⟩ := eventually_atTop.1 ((hc1.and hc2).and (eventually_ge_atTop 1))
  have h1 : Continuous fun s : ℝ => airyBi (-(s : ℂ)) :=
    differentiable_airyBi.continuous.comp continuous_ofReal.neg
  have h2 : Continuous fun s : ℝ => airyBiDeriv (-(s : ℂ)) :=
    (continuous_iff_continuousAt.mpr fun z => (hasDerivAt_airyBiDeriv z).continuousAt).comp
      continuous_ofReal.neg
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max S 1)).exists_bound_of_continuousOn
    (by fun_prop : Continuous fun s : ℝ => ‖airyBi (-(s : ℂ))‖ + ‖airyBiDeriv (-(s : ℂ))‖).continuousOn
  refine ⟨max K 0 + |c1| + |c2|, by positivity, fun s hs => ?_⟩
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have n1 := norm_nonneg (airyBi (-(s : ℂ)))
  have n2 := norm_nonneg (airyBiDeriv (-(s : ℂ)))
  rcases le_or_gt s (max S 1) with h | h
  · have hk := hK s ⟨hs, h⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hk
    have hk' := hk.trans (le_max_left K 0)
    constructor <;> nlinarith [abs_nonneg c1, abs_nonneg c2]
  · obtain ⟨⟨k1, k2⟩, hs1⟩ := hS s (le_trans (le_max_left _ _) h.le)
    have hq1 : ‖s ^ (-(1 / 4) : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
    have hq2 : ‖s ^ (1 / 4 : ℝ)‖ ≤ 1 + s := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc s ^ (1 / 4 : ℝ) ≤ s ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
        _ = s := Real.rpow_one s
        _ ≤ 1 + s := by linarith
    have hn1 := norm_nonneg (s ^ (-(1 / 4) : ℝ))
    have hn2 := norm_nonneg (s ^ (1 / 4 : ℝ))
    have e1 : c1 * ‖s ^ (-(1 / 4) : ℝ)‖ ≤ |c1| * 1 := by
      calc c1 * ‖s ^ (-(1 / 4) : ℝ)‖ ≤ |c1| * ‖s ^ (-(1 / 4) : ℝ)‖ := by
            gcongr; exact le_abs_self c1
        _ ≤ |c1| * 1 := by gcongr
    have e2 : c2 * ‖s ^ (1 / 4 : ℝ)‖ ≤ |c2| * (1 + s) := by
      calc c2 * ‖s ^ (1 / 4 : ℝ)‖ ≤ |c2| * ‖s ^ (1 / 4 : ℝ)‖ := by
            gcongr; exact le_abs_self c2
        _ ≤ |c2| * (1 + s) := by gcongr
    constructor
    · nlinarith [abs_nonneg c1, abs_nonneg c2]
    · nlinarith [abs_nonneg c1, abs_nonneg c2]

/-- `∫₀^∞ e^{-qt} Bi(-t) dt`. -/
noncomputable def airyLapNB (q : ℂ) : ℂ := ∫ t : ℝ in Ioi 0, exp (-q * t) * airyBi (-t)

/-- Domination for `Re q ≥ a > 0`: `(1+t) |e^{-qt} Bi(-t)|, |e^{-qt} Bi'(-t)| ≤ K e^{-(a/2) t}`. -/
theorem airyLapB_dom {a : ℝ} (ha : 0 < a) : ∃ K, 0 ≤ K ∧ ∀ q : ℂ, a ≤ q.re → ∀ t : ℝ, 0 ≤ t →
    (1 + t) * ‖exp (-q * t) * airyBi (-t)‖ ≤ K * Real.exp (-(a / 2) * t) ∧
      ‖exp (-q * t) * airyBiDeriv (-t)‖ ≤ K * Real.exp (-(a / 2) * t) := by
  obtain ⟨C, hC0, hC⟩ := airyLapB_bound
  have hc : 0 < min (a / 2) 1 := by positivity
  refine ⟨C * (min (a / 2) 1)⁻¹, by positivity, fun q hq t ht => ?_⟩
  obtain ⟨hB, hD⟩ := hC t ht
  have hone := airyLap_one_add_abs_le hc (min_le_right _ _) t
  rw [abs_of_nonneg ht] at hone
  have hexp : Real.exp (min (a / 2) 1 * t) * Real.exp (-q.re * t) ≤ Real.exp (-(a / 2) * t) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [min_le_left (a / 2) 1])
  have hn : ‖exp (-q * t)‖ = Real.exp (-q.re * t) := by rw [airyLap_norm_exp]; simp
  rw [norm_mul, norm_mul, hn]
  have hE := Real.exp_pos (-q.re * t)
  have hci := inv_pos.mpr hc
  have hE2 := Real.exp_pos (min (a / 2) 1 * t)
  constructor
  · calc (1 + t) * (Real.exp (-q.re * t) * ‖airyBi (-(t : ℂ))‖)
        ≤ ((min (a / 2) 1)⁻¹ * Real.exp (min (a / 2) 1 * t)) * (Real.exp (-q.re * t) * C) := by
          gcongr
      _ = C * (min (a / 2) 1)⁻¹ * (Real.exp (min (a / 2) 1 * t) * Real.exp (-q.re * t)) := by ring
      _ ≤ _ := by gcongr
  · calc Real.exp (-q.re * t) * ‖airyBiDeriv (-(t : ℂ))‖
        ≤ Real.exp (-q.re * t) * (C * ((min (a / 2) 1)⁻¹ * Real.exp (min (a / 2) 1 * t))) := by
          gcongr; exact hD.trans (by gcongr)
      _ = C * (min (a / 2) 1)⁻¹ * (Real.exp (min (a / 2) 1 * t) * Real.exp (-q.re * t)) := by ring
      _ ≤ _ := by gcongr

/-- Integrability of `e^{-pt} Bi(-t)` and `t e^{-pt} Bi(-t)` on `(0, ∞)` for `Re p > 0`. -/
theorem airyLapB_integrableOn {p : ℂ} (hp : 0 < p.re) :
    IntegrableOn (fun t : ℝ => exp (-p * t) * airyBi (-t)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => (t : ℂ) * (exp (-p * t) * airyBi (-t))) (Ioi 0) := by
  obtain ⟨K, hK0, hK⟩ := airyLapB_dom hp
  have hI := (exp_neg_integrableOn_Ioi 0 (by positivity : 0 < p.re / 2)).const_mul K
  have hBc : Continuous fun t : ℝ => airyBi (-(t : ℂ)) :=
    differentiable_airyBi.continuous.comp continuous_ofReal.neg
  constructor
  · refine hI.mono' (by fun_prop : Continuous fun t : ℝ =>
      exp (-p * t) * airyBi (-t)).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have h := (hK p le_rfl t (le_of_lt ht)).1
    have ht0 : (0 : ℝ) < t := ht
    nlinarith [norm_nonneg (exp (-p * t) * airyBi (-t))]
  · refine hI.mono' (by fun_prop : Continuous fun t : ℝ =>
      (t : ℂ) * (exp (-p * t) * airyBi (-t))).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have h := (hK p le_rfl t (le_of_lt ht)).1
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    nlinarith [norm_nonneg (exp (-p * t) * airyBi (-t))]

/-- `N_B'(p) = -∫₀^∞ t e^{-pt} Bi(-t) dt` on `Re p > 0`. -/
theorem airyLapNB_hasDerivAt {p : ℂ} (hp : 0 < p.re) :
    HasDerivAt airyLapNB (-∫ t : ℝ in Ioi 0, (t : ℂ) * (exp (-p * t) * airyBi (-t))) p := by
  obtain ⟨K, hK0, hK⟩ := airyLapB_dom (a := p.re / 2) (by positivity)
  have hI := (exp_neg_integrableOn_Ioi 0 (by positivity : 0 < p.re / 2 / 2)).const_mul K
  have hball : Metric.ball p (p.re / 2) ∈ 𝓝 p := Metric.ball_mem_nhds p (by positivity)
  have hBc : Continuous fun t : ℝ => airyBi (-(t : ℂ)) :=
    differentiable_airyBi.continuous.comp continuous_ofReal.neg
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0)) hball
    (F := fun q (t : ℝ) => exp (-q * t) * airyBi (-t))
    (F' := fun q (t : ℝ) => -((t : ℂ) * (exp (-q * t) * airyBi (-t))))
    (Eventually.of_forall fun q => (by fun_prop : Continuous fun t : ℝ =>
      exp (-q * t) * airyBi (-t)).aestronglyMeasurable)
    (airyLapB_integrableOn hp).1
    ((by fun_prop : Continuous fun t : ℝ =>
      -((t : ℂ) * (exp (-p * t) * airyBi (-t)))).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht q hq => ?_)) hI
    (Eventually.of_forall fun t q _ => ?_)
  · rw [integral_neg] at h
    exact h.2
  · have hd : |q.re - p.re| < p.re / 2 := by
      have := Metric.mem_ball.mp hq
      rw [dist_eq_norm] at this
      calc |q.re - p.re| = |(q - p).re| := by simp
        _ ≤ ‖q - p‖ := Complex.abs_re_le_norm _
        _ < _ := this
    have hd' := abs_lt.mp hd
    have h1 := (hK q (by linarith) t (le_of_lt ht)).1
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    nlinarith [norm_nonneg (exp (-q * t) * airyBi (-t))]
  · have := (((hasDerivAt_id' q).neg.mul_const (t : ℂ)).cexp).mul_const (airyBi (-t))
    simp only [Pi.neg_apply] at this
    refine this.congr_deriv ?_
    ring

/-- **The transform equation for `Bi(-t)`**: `N_B' = p² N_B + Bi'(0) - p Bi(0)`. -/
theorem airyLapNB_ode {p : ℂ} (hp : 0 < p.re) :
    HasDerivAt airyLapNB (p ^ 2 * airyLapNB p + airyBiDeriv 0 - p * airyBi 0) p := by
  obtain ⟨K, hK0, hK⟩ := airyLapB_dom hp
  obtain ⟨i1, i2⟩ := airyLapB_integrableOn hp
  have hint : IntegrableOn (fun t : ℝ => exp (-p * t) * ((-(t : ℂ) - p ^ 2) * airyBi (-t)))
      (Ioi 0) := by
    refine ((i2.neg).sub (i1.const_mul (p ^ 2))).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, Pi.neg_apply]; ring
  have hg : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => exp (-p * t) * (-airyBiDeriv (-t) + p * airyBi (-t)))
      (exp (-p * t) * ((-(t : ℂ) - p ^ 2) * airyBi (-t))) t := by
    intro t
    have he : HasDerivAt (fun t : ℝ => exp (-p * t)) (exp (-p * t) * (-p)) t := by
      have := ((hasDerivAt_id (t : ℂ)).const_mul (-p)).cexp.comp_ofReal
      simpa using this
    have hn : HasDerivAt (fun t : ℝ => -(t : ℂ)) (-1) t := (hasDerivAt_id (t : ℂ)).comp_ofReal.neg
    have hB : HasDerivAt (fun t : ℝ => airyBi (-(t : ℂ))) (airyBiDeriv (-(t : ℂ)) * (-1)) t :=
      ((hasDerivAt_airyBi (-(t : ℂ))).comp (t : ℂ) (hasDerivAt_neg (t : ℂ))).comp_ofReal
    have hD : HasDerivAt (fun t : ℝ => airyBiDeriv (-(t : ℂ)))
        ((-(t : ℂ)) * airyBi (-(t : ℂ)) * (-1)) t :=
      ((hasDerivAt_airyBiDeriv (-(t : ℂ))).comp (t : ℂ) (hasDerivAt_neg (t : ℂ))).comp_ofReal
    have := he.mul ((hD.neg).add (hB.const_mul p))
    simp only [Pi.add_apply, Pi.neg_apply] at this
    refine this.congr_deriv ?_
    ring
  have hlim : Tendsto (fun t : ℝ => exp (-p * t) * (-airyBiDeriv (-t) + p * airyBi (-t))) atTop
      (𝓝 0) := by
    have hb : ∀ᶠ t : ℝ in atTop, ‖exp (-p * t) * (-airyBiDeriv (-t) + p * airyBi (-t))‖ ≤
        (K + ‖p‖ * K) * Real.exp (-(p.re / 2) * t) := by
      filter_upwards [eventually_ge_atTop 0] with t ht
      obtain ⟨h1, h2⟩ := hK p le_rfl t ht
      have h1' : ‖exp (-p * t) * airyBi (-t)‖ ≤ K * Real.exp (-(p.re / 2) * t) := by
        nlinarith [norm_nonneg (exp (-p * t) * airyBi (-t))]
      calc ‖exp (-p * t) * (-airyBiDeriv (-t) + p * airyBi (-t))‖
          = ‖-(exp (-p * t) * airyBiDeriv (-t)) + p * (exp (-p * t) * airyBi (-t))‖ := by ring_nf
        _ ≤ ‖exp (-p * t) * airyBiDeriv (-t)‖ + ‖p‖ * ‖exp (-p * t) * airyBi (-t)‖ := by
            rw [← norm_mul, ← norm_neg (exp (-p * t) * airyBiDeriv (-t))]; exact norm_add_le _ _
        _ ≤ K * Real.exp (-(p.re / 2) * t) + ‖p‖ * (K * Real.exp (-(p.re / 2) * t)) := by gcongr
        _ = _ := by ring
    have h0 : Tendsto (fun t : ℝ => (K + ‖p‖ * K) * Real.exp (-(p.re / 2) * t)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (by linarith : -(p.re / 2) < 0))
      simpa using this.const_mul (K + ‖p‖ * K)
    exact squeeze_zero_norm' hb h0
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hg t) hint hlim
  have e : (fun t : ℝ => exp (-p * t) * ((-(t : ℂ) - p ^ 2) * airyBi (-t))) =
      fun t : ℝ => -((t : ℂ) * (exp (-p * t) * airyBi (-t))) - p ^ 2 * (exp (-p * t) * airyBi (-t)) := by
    funext t; ring
  rw [e, integral_sub (f := fun t : ℝ => -((t : ℂ) * (exp (-p * t) * airyBi (-t))))
    (g := fun t : ℝ => p ^ 2 * (exp (-p * t) * airyBi (-t))) i2.neg (i1.const_mul _),
    integral_neg, integral_const_mul] at hftc
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, one_mul, zero_sub, neg_zero] at hftc
  refine (airyLapNB_hasDerivAt hp).congr_deriv ?_
  rw [airyLapNB]
  linear_combination hftc

/-- The closed form of 9.10.16 before rewriting the constants. -/
noncomputable def airyLapRB (p : ℂ) : ℂ :=
  exp (p ^ 3 / 3) * (airyBiDeriv 0 * (p * kummerM (1 / 3) (4 / 3) (-(p ^ 3 / 3))) -
    airyBi 0 * (p ^ 2 * kummerM (2 / 3) (5 / 3) (-(p ^ 3 / 3)) / 2))

/-- The closed form `R_B(p)` of 9.10.16 satisfies `R_B' = p² R_B + Bi'(0) - p Bi(0)`. -/
theorem airyLapRB_ode (p : ℂ) :
    HasDerivAt airyLapRB (p ^ 2 * airyLapRB p + airyBiDeriv 0 - p * airyBi 0) p := by
  have h2 : HasDerivAt (fun q : ℂ => exp (q ^ 3 / 3)) (exp (p ^ 3 / 3) * p ^ 2) p := by
    have := ((hasDerivAt_pow 3 p).div_const 3).cexp
    convert this using 1; ring
  have hG1 : HasDerivAt (fun q : ℂ => q * kummerM (1 / 3) (4 / 3) (-(q ^ 3 / 3)))
      (exp (-p ^ 3 / 3)) p := by
    have := ((airyLap_hasDerivAt_E1 (-p)).comp p (hasDerivAt_neg p)).neg
    have e : (fun q : ℂ => q * kummerM (1 / 3) (4 / 3) (-(q ^ 3 / 3))) =
        -((fun p : ℂ => p * kummerM (1 / 3) (4 / 3) (p ^ 3 / 3)) ∘ Neg.neg) := by
      funext q; simp only [Function.comp, Pi.neg_apply]
      rw [show (-q) ^ 3 / 3 = -(q ^ 3 / 3) by ring]; ring
    rw [e]; refine this.congr_deriv ?_
    rw [show (-p) ^ 3 / 3 = -p ^ 3 / 3 by ring]; ring
  have hG2 : HasDerivAt (fun q : ℂ => q ^ 2 * kummerM (2 / 3) (5 / 3) (-(q ^ 3 / 3)) / 2)
      (p * exp (-p ^ 3 / 3)) p := by
    have := (airyLap_hasDerivAt_E2 (-p)).comp p (hasDerivAt_neg p)
    have e : (fun q : ℂ => q ^ 2 * kummerM (2 / 3) (5 / 3) (-(q ^ 3 / 3)) / 2) =
        ((fun p : ℂ => p ^ 2 * kummerM (2 / 3) (5 / 3) (p ^ 3 / 3) / 2) ∘ Neg.neg) := by
      funext q; simp only [Function.comp]
      rw [show (-q) ^ 3 / 3 = -(q ^ 3 / 3) by ring]; ring
    rw [e]; refine this.congr_deriv ?_
    rw [show (-p) ^ 3 / 3 = -p ^ 3 / 3 by ring]; ring
  have h := h2.mul ((hG1.const_mul (airyBiDeriv 0)).sub (hG2.const_mul (airyBi 0)))
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply]
  rw [airyLapRB]
  have : exp (p ^ 3 / 3) * exp (-p ^ 3 / 3) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  linear_combination (airyBiDeriv 0 - p * airyBi 0) * this

/-- The real-power identities `√3 · 3^{1/3} · 3^{1/6} = 3` and `√3² · 3^{1/3} · 3^{2/3} = 9`. -/
theorem airyLapB_consts :
    (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) = 3 / ((Real.sqrt 3 : ℝ) * (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) ∧
      (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) =
        9 / ((Real.sqrt 3 : ℝ) ^ 2 * (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) := by
  have h1 : Real.sqrt 3 * (3 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ) = 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    norm_num
  have h2 : Real.sqrt 3 ^ 2 * (3 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (2 / 3 : ℝ) = 9 := by
    rw [Real.sq_sqrt (by norm_num), mul_assoc, ← Real.rpow_add (by norm_num)]
    norm_num
  have hq : (Real.sqrt 3 : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  have hr : (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  have h1c : ((Real.sqrt 3 : ℝ) : ℂ) * (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) = 3 := by exact_mod_cast h1
  have h2c : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) = 9 := by exact_mod_cast h2
  constructor
  · field_simp; linear_combination h1c
  · field_simp; linear_combination h2c

/-- The closed form `R_B` agrees with the printed right-hand side of 9.10.16. -/
theorem airyLapRB_eq_printed {p : ℂ} (hp0 : p ≠ 0) :
    airyLapRB p = exp (p ^ 3 / 3) / Real.sqrt 3 *
      (airyUpperGammaOnLog (2 / 3) (3 * log p - log 3) / Gamma (2 / 3) -
        airyUpperGammaOnLog (1 / 3) (3 * log p - log 3) / Gamma (1 / 3)) := by
  have h13 : ∀ n : ℕ, (1 / 3 : ℂ) ≠ -n := Hypergeometric.not_neg_nat_of_re_pos (by norm_num)
  have h23 : ∀ n : ℕ, (2 / 3 : ℂ) ≠ -n := Hypergeometric.not_neg_nat_of_re_pos (by norm_num)
  rw [airyLapRB, airyBiDeriv_zero, airyBi_zero, airyLap_upperGamma_eq h13, airyLap_upperGamma_eq h23]
  obtain ⟨e0, e1, e2⟩ := airyLap_exp_w hp0
  rw [e0, e1, e2, show (1 / 3 : ℂ) + 1 = 4 / 3 by norm_num, show (2 / 3 : ℂ) + 1 = 5 / 3 by norm_num,
    airyLapB_consts.1, airyLapB_consts.2]
  have hg1 : Gamma (1 / 3 : ℂ) ≠ 0 := Complex.Gamma_ne_zero h13
  have hg2 : Gamma (2 / 3 : ℂ) ≠ 0 := Complex.Gamma_ne_zero h23
  have hq : (Real.sqrt 3 : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  have hr : (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  field_simp
  ring

/-- On the positive axis the logarithmic-plane upper Gamma is the ordinary one. -/
theorem airyLap_upperGamma_real (a : ℂ) {x : ℝ} (hx : 0 < x) :
    airyUpperGammaOnLog a (3 * log (x : ℂ) - log 3) = upperIncGamma a ((x ^ 3 / 3 : ℝ) : ℂ) := by
  have hw : 3 * log (x : ℂ) - log 3 = ((3 * Real.log x - Real.log 3 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hx.le, show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)]
    push_cast; ring
  have hlog : log (exp (((3 * Real.log x - Real.log 3 : ℝ) : ℂ))) =
      ((3 * Real.log x - Real.log 3 : ℝ) : ℂ) := by
    apply Complex.log_exp
    · rw [Complex.ofReal_im]; linarith [Real.pi_pos]
    · rw [Complex.ofReal_im]; linarith [Real.pi_pos]
  have he : exp (((3 * Real.log x - Real.log 3 : ℝ) : ℂ)) = ((x ^ 3 / 3 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_sub, show 3 * Real.log x = ((3 : ℕ) : ℝ) * Real.log x by
      norm_num, Real.exp_nat_mul, Real.exp_log hx, Real.exp_log (by norm_num)]
  rw [hw, airyUpperGammaOnLog, hlog, he]
  simp [lineIntegral]

/-- `Γ(a, y) → 0` as `y → +∞` for `Re a > 0`. -/
theorem airyLap_upperIncGamma_tendsto {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun y : ℝ => upperIncGamma a (y : ℂ)) atTop (𝓝 0) := by
  set f : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * Real.exp (-t)
  have hi : IntegrableOn f (Ioi 0) := by
    have := Complex.GammaIntegral_convergent ha
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [f]; push_cast; ring
  have h1 := intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id
  have h2 : Tendsto (fun y : ℝ => (∫ t in Ioi 0, f t) - ∫ t in (0 : ℝ)..y, f t) atTop (𝓝 0) := by
    simpa using h1.const_sub (∫ t in Ioi 0, f t)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [upperIncGamma_eq_integral a hy, intervalIntegral.integral_of_le hy.le]
  have e := setIntegral_union (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := y)) measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hy.le))
  rw [Ioc_union_Ioi_eq_Ioi hy.le] at e
  rw [e]; simp only [f]; ring

/-- **9.10.16 (proof)**: `N_B = R_B` on `Re p > 0`. -/
theorem airyLapNB_eq {p : ℂ} (hp : 0 < p.re) : airyLapNB p = airyLapRB p := by
  set U := {c : ℂ | 0 < c.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set D : ℂ → ℂ := fun q => (airyLapNB q - airyLapRB q) * exp (-q ^ 3 / 3)
  have hD : ∀ z ∈ U, HasDerivAt D 0 z := by
    intro z hz
    have h3 : HasDerivAt (fun q : ℂ => exp (-q ^ 3 / 3)) (exp (-z ^ 3 / 3) * (-z ^ 2)) z := by
      have := (((hasDerivAt_pow 3 z).neg).div_const 3).cexp
      convert this using 1; simp only [Pi.neg_apply]; ring
    have := ((airyLapNB_ode hz).sub (airyLapRB_ode z)).mul h3
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply]; ring
  have hc : ∀ x : ℝ, 0 < x → D x = D p := fun x hx =>
    hU.is_const_of_deriv_eq_zero (convex_halfSpace_re_gt 0).isPreconnected
      (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hD z hz).deriv) (show (0 : ℝ) < ((x : ℂ)).re by simpa using hx) hp
  -- `D(x) → 0` as `x → +∞`
  have hlim : Tendsto (fun x : ℝ => D x) atTop (𝓝 0) := by
    obtain ⟨K, hK0, hK⟩ := airyLapB_dom (a := 1) one_pos
    have hI := (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul K
    have hNb : ∀ x : ℝ, 1 ≤ x → ‖airyLapNB x‖ ≤ ∫ t in Ioi (0 : ℝ), K * Real.exp (-(1 / 2) * t) := by
      intro x hx
      refine norm_integral_le_of_norm_le hI ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun t ht => ?_))
      have h := (hK x (by simpa using hx) t (le_of_lt ht)).1
      nlinarith [norm_nonneg (exp (-(x : ℂ) * t) * airyBi (-t)), (le_of_lt ht : (0 : ℝ) ≤ t)]
    have he : Tendsto (fun x : ℝ => exp (-(x : ℂ) ^ 3 / 3)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : Tendsto (fun x : ℝ => Real.exp (-(x ^ 3 / 3))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
          ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).atTop_div_const (by norm_num)))
      refine this.congr fun x => ?_
      rw [Complex.norm_exp]; congr 1; simp [pow_succ]; ring
    have hN : Tendsto (fun x : ℝ => airyLapNB x * exp (-(x : ℂ) ^ 3 / 3)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (he.norm.const_mul (∫ t in Ioi (0 : ℝ), K * Real.exp (-(1 / 2) * t)) |>.trans (by simp))
      filter_upwards [eventually_ge_atTop 1] with x hx
      rw [norm_mul]; gcongr; exact hNb x hx
    have hR : Tendsto (fun x : ℝ => airyLapRB x * exp (-(x : ℂ) ^ 3 / 3)) atTop (𝓝 0) := by
      have hy : Tendsto (fun x : ℝ => x ^ 3 / 3) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).atTop_div_const (by norm_num)
      have g1 := (airyLap_upperIncGamma_tendsto (a := 1 / 3) (by norm_num)).comp hy
      have g2 := (airyLap_upperIncGamma_tendsto (a := 2 / 3) (by norm_num)).comp hy
      have := ((g2.div_const (Gamma (2 / 3))).sub (g1.div_const (Gamma (1 / 3)))).const_mul
        ((Real.sqrt 3 : ℂ))⁻¹
      rw [zero_div, zero_div, sub_zero, mul_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
      simp only [Function.comp]
      rw [airyLapRB_eq_printed hx0, airyLap_upperGamma_real _ hx, airyLap_upperGamma_real _ hx]
      have : exp ((x : ℂ) ^ 3 / 3) * exp (-(x : ℂ) ^ 3 / 3) = 1 := by
        rw [← Complex.exp_add]; ring_nf; simp
      have key : ∀ A : ℂ, ((Real.sqrt 3 : ℂ))⁻¹ * A =
          exp ((x : ℂ) ^ 3 / 3) / (Real.sqrt 3 : ℂ) * A * exp (-(x : ℂ) ^ 3 / 3) := fun A => by
        rw [div_eq_mul_inv]; linear_combination (-((Real.sqrt 3 : ℂ))⁻¹ * A) * this
      exact key _
    have := hN.sub hR
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards with x
    simp only [D]; ring
  have hDp : D p = 0 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact (hc x hx).symm
  have hE : exp (-p ^ 3 / 3) ≠ 0 := Complex.exp_ne_zero _
  rcases mul_eq_zero.mp hDp with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hE

end AiryLaplaceNegBi

/-- For `Re p > 0`, `∫₀^∞ e^{-pt} Bi(-t) dt` converges and equals
`(e^{p³/3}/√3)(Γ(2/3, p³/3)/Γ(2/3) - Γ(1/3, p³/3)/Γ(1/3))`, with the incomplete Gamma functions
continued on the logarithmic plane (DLMF 9.10.16). -/
@[dlmf 9.10.E16]
theorem airyBi_negative_laplace {p : ℂ} (hp : 0 < p.re) :
    IntegrableOn (fun t : ℝ => exp (-p * t) * airyBi (-t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-p * t) * airyBi (-t)) = exp (p ^ 3 / 3) / Real.sqrt 3 * (airyUpperGammaOnLog (2 / 3) (3 * log p - log 3) / Gamma (2 / 3) - airyUpperGammaOnLog (1 / 3) (3 * log p - log 3) / Gamma (1 / 3)) := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; simp at hp
  exact ⟨(airyLapB_integrableOn hp).1, (airyLapNB_eq hp).trans (airyLapRB_eq_printed hp0)⟩

/-- On `(0, ∞)`, `t^{α-1} Ai(t) = (π√3)⁻¹ t^{(α+½)-1} K_{1/3}((2/3) t^{3/2})` (DLMF 9.6.2). -/
theorem airyMel_integrand {α : ℂ} {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (α - 1) * airyAi t = ((π⁻¹ * (Real.sqrt 3)⁻¹ : ℝ) : ℂ) •
      ((t : ℂ) ^ ((α + 1 / 2) - 1) •
        (fun u : ℝ => DLMF.Bessel.besselK (1 / 3) ((2 / 3 * u : ℝ) : ℂ)) (t ^ (3 / 2 : ℝ))) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [airyAi_eq_besselK ht, Real.sqrt_div' t (by norm_num : (0:ℝ) ≤ 3)]
  have hs : ((Real.sqrt t : ℝ) : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow ht.le]; push_cast; rfl
  have e : (t : ℂ) ^ (α - 1) * (t : ℂ) ^ (1 / 2 : ℂ) = (t : ℂ) ^ ((α + 1 / 2) - 1) := by
    rw [← cpow_add _ _ ht0]; ring_nf
  simp only [smul_eq_mul, airyZeta]
  push_cast
  rw [hs, ← e]
  ring

/-- The Mellin transform of `Ai`: for `Re α > 0`,
`∫₀^∞ t^{α-1} Ai(t) dt = Γ(α)/(3^{(α+2)/3} Γ(α/3 + 2/3))` (DLMF 9.10.17). Proved from the Mellin
transform of `K_{1/3}` (DLMF 10.43.19), the substitution `ζ = (2/3) t^{3/2}` and Gauss's
multiplication formula for `m = 3`. -/
@[dlmf 9.10.E17]
theorem airyAi_mellin {α : ℂ} (hα : 0 < α.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (α - 1) * airyAi t) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (α - 1) * airyAi t) =
        Gamma α / ((3 : ℂ) ^ ((α + 2) / 3) * Gamma (α / 3 + 2 / 3)) := by
  set f : ℝ → ℂ := fun u => DLMF.Bessel.besselK (1 / 3) (u : ℂ) with hf
  set g : ℝ → ℂ := fun u => DLMF.Bessel.besselK (1 / 3) ((2 / 3 * u : ℝ) : ℂ) with hg
  set w : ℂ := (α + 1 / 2) / ((3 / 2 : ℝ) : ℂ) with hw
  have hwre : |(1 / 3 : ℂ).re| < w.re := by
    have : w.re = (2 * α.re + 1) / 3 := by
      rw [hw]; simp [div_re, Complex.normSq]; ring_nf
    rw [this]; norm_num; linarith
  have hconv : MellinConvergent (fun t : ℝ => g (t ^ (3 / 2 : ℝ))) (α + 1 / 2) := by
    rw [MellinConvergent.comp_rpow (by norm_num)]
    exact (MellinConvergent.comp_mul_left (f := f) (by norm_num)).mpr
      (DLMF.Bessel.besselK_mellinConvergent hwre)
  have hEq : EqOn (fun t : ℝ => (t : ℂ) ^ (α - 1) * airyAi t)
      (fun t : ℝ => ((π⁻¹ * (Real.sqrt 3)⁻¹ : ℝ) : ℂ) • ((t : ℂ) ^ ((α + 1 / 2) - 1) •
        g (t ^ (3 / 2 : ℝ)))) (Ioi 0) := fun t ht => airyMel_integrand ht
  refine ⟨IntegrableOn.congr_fun (Integrable.smul (((π⁻¹ * (Real.sqrt 3)⁻¹ : ℝ) : ℂ)) hconv)
    hEq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hEq, integral_smul]
  change ((π⁻¹ * (Real.sqrt 3)⁻¹ : ℝ) : ℂ) • mellin (fun t : ℝ => g (t ^ (3 / 2 : ℝ))) (α + 1 / 2) = _
  rw [mellin_comp_rpow, show g = fun t => f (2 / 3 * t) from rfl,
    mellin_comp_mul_left f _ (a := 2 / 3) (by norm_num), ← hw, DLMF.Bessel.mellin_besselK hwre]
  have hw' : w = (2 * α + 1) / 3 := by rw [hw]; push_cast; field_simp
  have hG := Complex.Gamma_prod_add_div (m := 3) (by norm_num) (α / 3)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero] at hG
  push_cast at hG
  norm_num at hG
  rw [show 3 * (α / 3) = α by ring, show (1 : ℂ) / 2 - α = 1 / 2 - α from rfl] at hG
  have g1 : (w - 1 / 3) / 2 = α / 3 := by rw [hw']; ring
  have g2 : (w + 1 / 3) / 2 = α / 3 + 1 / 3 := by rw [hw']; ring
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have h3 : (3 : ℂ) ≠ 0 := three_ne_zero
  have c1 : (((2 / 3 : ℝ)) : ℂ) ^ (-w) = (2 : ℂ) ^ (-w) * (3 : ℂ) ^ w := by
    rw [show ((2 / 3 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) / ((3 : ℝ) : ℂ) by push_cast; ring,
      div_cpow_ofReal_nonneg (by norm_num) (by norm_num), cpow_neg, cpow_neg]
    push_cast; field_simp; rw [← cpow_add _ _ h2]; simp
  have c2 : (2 : ℂ) ^ (-w) * 2 ^ (w - 2) = 1 / 4 := by
    rw [← cpow_add _ _ h2, show -w + (w - 2) = -(2 : ℕ) by push_cast; ring, cpow_neg,
      cpow_natCast]; norm_num
  have c3 : (3 : ℂ) ^ w * 3 ^ (1 / 2 - α) =
      3 * (3 : ℂ) ^ (1 / 2 : ℂ) * ((3 : ℂ) ^ ((α + 2) / 3))⁻¹ := by
    rw [← cpow_add _ _ h3, show w + (1 / 2 - α) = (1 : ℂ) + 1 / 2 + (-((α + 2) / 3)) by
      rw [hw']; ring, cpow_add _ _ h3, cpow_add _ _ h3, cpow_one, cpow_neg]
  have c4 : ((Real.sqrt 3 : ℝ) : ℂ) = (3 : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by norm_num)]; push_cast; rfl
  have hs3 : (3 : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by rw [← c4]; exact_mod_cast (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hG3 : Gamma (α / 3 + 2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [div_ofNat_re]; linarith)
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc3 : (3 : ℂ) ^ ((α + 2) / 3) ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero (by
    intro h; have := congrArg Complex.re h; simp [div_ofNat_re] at this; linarith)).mpr h3
  rw [g1, g2, c1, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  simp only [smul_eq_mul, real_smul]
  push_cast
  rw [c4]
  have key : Gamma (α / 3) * Gamma (α / 3 + 1 / 3) =
      2 * π * 3 ^ (1 / 2 - α) * Gamma α / Gamma (α / 3 + 2 / 3) := by
    rw [eq_div_iff hG3, hG]
  rw [mul_assoc (2 ^ (w - 2)), key]
  have hA0 : (2 : ℂ) ^ (-w) ≠ 0 := by rw [cpow_def_of_ne_zero h2]; exact exp_ne_zero _
  have hC0 : (3 : ℂ) ^ w ≠ 0 := by rw [cpow_def_of_ne_zero h3]; exact exp_ne_zero _
  generalize (2 : ℂ) ^ (-w) = A at c2 hA0 ⊢
  generalize (2 : ℂ) ^ (w - 2) = B at c2 ⊢
  generalize (3 : ℂ) ^ w = C at c3 hC0 ⊢
  generalize (3 : ℂ) ^ (1 / 2 - α) = D at c3 ⊢
  generalize (3 : ℂ) ^ (1 / 2 : ℂ) = S at c3 hs3 ⊢
  generalize (3 : ℂ) ^ ((α + 2) / 3) = X at c3 hc3 ⊢
  generalize Gamma (α / 3 + 2 / 3) = Gm at hG3 ⊢
  have hB : B = 1 / (4 * A) := by field_simp; linear_combination 4 * c2
  have hD : D = 3 * S / (X * C) := by
    rw [eq_div_iff (mul_ne_zero hc3 hC0)]
    field_simp at c3
    linear_combination c3
  subst hB hD
  field_simp
  ring

/-- For `z ≠ 0`, `|ph z| < 2π/3`:
`Ai(z) = (3 z^{5/4} e^{-ζ}/(4π)) ∫₀^∞ t^{-3/4} e^{-(2/3)t^{3/2}} Ai(t)/(z^{3/2} + t^{3/2}) dt` (DLMF
9.10.18). -/
@[dlmf 9.10.E18]
theorem airyAi_stieltjes {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAi z = 3 * z ^ (5 / 4 : ℂ) * exp (-airyZetaComplex z) / (4 * π) *
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) *
        airyAi t / (z ^ (3 / 2 : ℂ) + (t : ℂ) ^ (3 / 2 : ℂ)) := by
  sorry

/-- For `x > 0`:
`Bi(x) = (3 x^{5/4} e^{ζ}/(2π)) ⨍₀^∞ t^{-3/4} e^{-(2/3)t^{3/2}} Ai(t)/(x^{3/2} - t^{3/2}) dt`, a
Cauchy principal value at `t = x` (DLMF 9.10.19). -/
@[dlmf 9.10.E19]
theorem airyBi_stieltjes_principalValue {x : ℝ} (hx : 0 < x) :
    airyBi x = 3 * (x : ℂ) ^ (5 / 4 : ℂ) * exp (airyZeta x) / (2 * π) *
      principalValueIoi (fun t : ℝ => (t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) *
        airyAi t / ((x : ℂ) ^ (3 / 2 : ℂ) - (t : ℂ) ^ (3 / 2 : ℂ))) x := by
  sorry

/-- For a solution `w` of Airy's equation on the real line,
`∫₀ˣ ∫₀ᵛ w = x ∫₀ˣ w - w'(x) + w'(0)`. -/
theorem airySol_double_integral {w w' : ℂ → ℂ} (hw : IsAirySol w w') (x : ℝ) :
    (∫ v : ℝ in 0..x, ∫ t : ℝ in 0..v, w t) =
      (x : ℂ) * (∫ t : ℝ in 0..x, w t) - w' x + w' 0 := by
  have hc : Continuous fun t : ℝ => w t :=
    (continuous_iff_continuousAt.mpr fun z => (hw z).1.continuousAt).comp continuous_ofReal
  have hP : ∀ v : ℝ, HasDerivAt (fun v : ℝ => ∫ t : ℝ in 0..v, w t) (w v) v := fun v =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hPc : Continuous fun v : ℝ => ∫ t : ℝ in 0..v, w t :=
    continuous_iff_continuousAt.mpr fun v => (hP v).continuousAt
  have hH : ∀ v : ℝ, HasDerivAt (fun v : ℝ => (v : ℂ) * (∫ t : ℝ in 0..v, w t) - w' v)
      (∫ t : ℝ in 0..v, w t) v := by
    intro v
    have h1 := (hasDerivAt_id (v : ℂ)).comp_ofReal.mul (hP v)
    have h2 := (hw v).2.comp_ofReal
    exact (h1.sub h2).congr_deriv (by simp)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
    (fun v _ => hH v) (hPc.intervalIntegrable _ _)
  rw [h]
  simp

/-- `∫₀^x ∫₀^v Ai(t) dt dv = x ∫₀^x Ai - Ai'(x) + Ai'(0)` (DLMF 9.10.20). -/
@[dlmf 9.10.E20]
theorem airyAi_double_integral (x : ℝ) :
    (∫ v : ℝ in 0..x, ∫ t : ℝ in 0..v, airyAi t) =
      (x : ℂ) * (∫ t : ℝ in 0..x, airyAi t) - airyAiDeriv x + airyAiDeriv 0 := by
  exact airySol_double_integral isAirySol_airyAi x

/-- `∫₀^x ∫₀^v Bi(t) dt dv = x ∫₀^x Bi - Bi'(x) + Bi'(0)` (DLMF 9.10.21). -/
@[dlmf 9.10.E21]
theorem airyBi_double_integral (x : ℝ) :
    (∫ v : ℝ in 0..x, ∫ t : ℝ in 0..v, airyBi t) =
      (x : ℂ) * (∫ t : ℝ in 0..x, airyBi t) - airyBiDeriv x + airyBiDeriv 0 := by
  exact airySol_double_integral isAirySol_airyBi x

/-- Repeated upper ordinary improper integrals, including the unintegrated base function. -/
def airyRepeatedTail : ℕ → ℝ → ℂ
  | 0 => fun t => airyAi (-t)
  | n + 1 => fun t => improperAtTop (airyRepeatedTail n) t

/-- For `n ≥ 1`, the `n`-fold repeated integral of `Ai(-t)` from `0` to `∞` equals
`2 cos((n-1)π/3)/(3^{(n+2)/3} Γ(n/3 + 2/3))` (DLMF 9.10.22). -/
@[dlmf 9.10.E22]
theorem airyAi_repeated_integrals {n : ℕ} (hn : 1 ≤ n) :
    HasIntegralAtTop (airyRepeatedTail (n - 1)) 0
      (2 * cos (((n : ℂ) - 1) * π / 3) /
        ((3 : ℂ) ^ (((n : ℂ) + 2) / 3) * Gamma ((n : ℂ) / 3 + 2 / 3))) := by
  sorry

/-- Existence of a symmetric principal value on `(0, ∞)` at `c > 0`, in the form of
`HasPrincipalValueIoi`, from the subtraction hypothesis near `c` and integrable tails. -/
theorem airyPV_hasPrincipalValueIoi {f : ℝ → ℂ} {b c : ℝ} (A : ℂ) (hc : 0 < c) (hcb : c < b)
    (hsub : IntegrableOn (fun t => f t - A / (t - c)) (Icc 0 b))
    (htail : ∀ d : ℝ, c < d → IntegrableOn f (Ioi d)) :
    HasPrincipalValueIoi f c
      ((∫ t in (0:ℝ)..b, (f t - A / (t - c))) + A * Real.log ((b - c) / (c - 0)) +
        ∫ t in Ioi b, f t) := by
  have hI : ∀ d : ℝ, c < d → HasIntegralAtTop f d (∫ t in Ioi d, f t) := fun d hd =>
    intervalIntegral_tendsto_integral_Ioi d (htail d hd) tendsto_id
  have himp : ∀ d : ℝ, c < d → improperAtTop f d = ∫ t in Ioi d, f t := fun d hd =>
    (hI d hd).limUnder_eq
  refine ⟨fun ε hε => ?_, ?_⟩
  · rw [himp _ (by linarith)]; exact hI _ (by linarith)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∫ t in (0:ℝ)..c - ε, f t) + improperAtTop f (c + ε) =
      ((∫ t in (0:ℝ)..c - ε, f t) + ∫ t in c + ε..b, f t) + ∫ t in Ioi b, f t := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hcb)] with ε hε
    have hd : c < c + ε := by linarith [hε.1]
    have hdb : c + ε ≤ b := by linarith [hε.2]
    have hfi : IntervalIntegrable f volume (c + ε) b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hdb).mpr
        ((htail _ hd).mono_set Ioc_subset_Ioi_self)
    have hloc : ∀ R, b ≤ R → IntervalIntegrable f volume b R := fun R hR =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
        ((htail _ (by linarith)).mono_set Ioc_subset_Ioi_self)
    have h := pv_tendsto_intervalIntegral_atTop_of_le (hI b hcb) hfi hloc
    rw [himp _ hd, tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi _ (htail _ hd) tendsto_id) h]
    ring
  exact ((pv_tendsto_of_integrableOn_sub A hc hcb hsub).add_const _).congr'
    (EventuallyEq.symm hev)

/-- `(t:ℂ)^(3/2)` is the real power for `t ≥ 0`. -/
theorem airyPV_cpow_three_halves {t : ℝ} (ht : 0 ≤ t) :
    (t : ℂ) ^ (3 / 2 : ℂ) = ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow ht]; push_cast; ring_nf

/-- `t ↦ t^{3/2}` is injective on `[0, ∞)`. -/
theorem airyPV_cpow_ne {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) (htx : t ≠ x) :
    (t : ℂ) ^ (3 / 2 : ℂ) - (x : ℂ) ^ (3 / 2 : ℂ) ≠ 0 := by
  rw [airyPV_cpow_three_halves ht, airyPV_cpow_three_halves hx, ← Complex.ofReal_sub,
    Complex.ofReal_ne_zero, sub_ne_zero]
  rcases lt_or_gt_of_ne htx with h | h
  · exact (Real.rpow_lt_rpow ht h (by norm_num)).ne
  · exact (Real.rpow_lt_rpow hx h (by norm_num)).ne'

/-- The disc `|s - x| < x` around `x > 0` lies in the slit plane. -/
private lemma airyPV_ball_slitPlane {x : ℝ} (_hx : 0 < x) :
    ∀ s ∈ Metric.ball (x : ℂ) x, s ∈ slitPlane := by
  intro s hs
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  have h1 := abs_re_le_norm (s - x)
  rw [Metric.mem_ball, dist_eq_norm] at hs
  simp only [sub_re, ofReal_re] at h1
  linarith [neg_abs_le (s.re - x)]

/-- The difference quotient `D = dslope (s ↦ s^{3/2}) x`, `x > 0`, is differentiable at `x`,
nonzero and continuous at every `t ≥ 0`. -/
private lemma airyPV_dslope_facts {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℂ (dslope (fun s : ℂ => s ^ (3 / 2 : ℂ)) x) x ∧
      dslope (fun s : ℂ => s ^ (3 / 2 : ℂ)) x x ≠ 0 ∧
      (∀ t : ℝ, 0 ≤ t → dslope (fun s : ℂ => s ^ (3 / 2 : ℂ)) x t ≠ 0) ∧
      ∀ t : ℝ, 0 ≤ t → ContinuousAt (dslope (fun s : ℂ => s ^ (3 / 2 : ℂ)) x) t := by
  set φ : ℂ → ℂ := fun s => s ^ (3 / 2 : ℂ) with hφ
  set D : ℂ → ℂ := dslope φ x with hD
  have hslit := airyPV_ball_slitPlane hx
  have hball : Metric.ball (x : ℂ) x ∈ 𝓝 (x : ℂ) := Metric.ball_mem_nhds _ hx
  have hφd : DifferentiableOn ℂ φ (Metric.ball (x : ℂ) x) := fun s hs =>
    (Complex.hasStrictDerivAt_cpow_const (c := (3/2 : ℂ)) (hslit s hs)).hasDerivAt
      |>.differentiableAt.differentiableWithinAt
  have hDd : DifferentiableAt ℂ D x :=
    ((differentiableOn_dslope hball).mpr hφd).differentiableAt hball
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hDx : D x ≠ 0 := by
    have hxs : (x : ℂ) ∈ slitPlane := hslit _ (Metric.mem_ball_self hx)
    rw [hD, dslope_same, (Complex.hasStrictDerivAt_cpow_const (c := (3/2 : ℂ)) hxs).hasDerivAt.deriv]
    refine mul_ne_zero (by norm_num) ?_
    rw [Ne, cpow_eq_zero_iff]; tauto
  have hDne : ∀ t : ℝ, 0 ≤ t → D t ≠ 0 := by
    intro t ht
    by_cases htx : t = x
    · rw [htx]; exact hDx
    have htx' : (t : ℂ) ≠ x := by exact_mod_cast htx
    simp only [hD, dslope_of_ne _ htx', slope_def_module, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr htx')) (airyPV_cpow_ne ht hx.le htx)
  have hDc : ∀ t : ℝ, 0 ≤ t → ContinuousAt D t := by
    intro t ht
    by_cases htx : t = x
    · rw [htx]; exact hDd.continuousAt
    have htx' : (t : ℂ) ≠ x := by exact_mod_cast htx
    have hφc : ContinuousAt φ t :=
      continuousAt_cpow_const_of_re_pos (Or.inl (by simpa using ht)) (by norm_num)
    have hsl : ContinuousAt (fun s : ℂ => (s - x)⁻¹ * (φ s - φ x)) t :=
      ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr htx')).mul
        (hφc.sub continuousAt_const)
    refine hsl.congr ?_
    filter_upwards [isOpen_ne.mem_nhds htx'] with s hs
    simp only [hD, dslope_of_ne _ hs, slope_def_module, smul_eq_mul]
  exact ⟨hDd, hDx, hDne, hDc⟩

/-- The integrand of the principal value in DLMF 9.10.19 is integrable on `(d, ∞)` for
`d > x > 0`: it is `O(t^{-3/2})` there. -/
private lemma airyPV_tail_integrableOn {x : ℝ} (hx : 0 < x) {d : ℝ} (hd : x < d) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) *
      airyAi t / ((x : ℂ) ^ (3 / 2 : ℂ) - (t : ℂ) ^ (3 / 2 : ℂ))) (Ioi d) := by
  have hAc : Continuous fun t : ℝ => airyAi t := differentiable_airyAi.continuous.comp
    continuous_ofReal
  have hζc : Continuous airyZeta := by
    unfold airyZeta; exact continuous_const.mul (Real.continuous_rpow_const (by norm_num))
  have hd0 : 0 < d := lt_trans hx hd
  obtain ⟨C, hC0, hC⟩ := airyLap_pos_bound 0
  set ρ : ℝ := (x / d) ^ (3 / 2 : ℝ) with hρ
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by positivity) ((div_lt_one hd0).mpr hd) (by norm_num)
  set K : ℝ := d ^ (-3 / 4 : ℝ) * C / (1 - ρ)
  have hK : IntegrableOn (fun t : ℝ => K * t ^ (-3 / 2 : ℝ)) (Ioi d) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hd0).const_mul K
  refine hK.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := lt_trans hd0 ht
    have htx : t ≠ x := ne_of_gt (lt_trans hd ht)
    refine ContinuousAt.continuousWithinAt (ContinuousAt.div ?_ ?_ ?_)
    · refine ContinuousAt.mul (ContinuousAt.mul ?_
        (Complex.continuous_exp.comp (continuous_ofReal.comp hζc).neg).continuousAt)
        hAc.continuousAt
      exact continuousAt_ofReal_cpow_const _ _ (Or.inr ht0.ne')
    · exact continuousAt_const.sub
        (continuousAt_ofReal_cpow_const _ _ (Or.inr ht0.ne'))
    · intro h0; exact airyPV_cpow_ne ht0.le hx.le htx (by linear_combination -h0)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hd0 ht
    have hdt : d ≤ t := le_of_lt ht
    have h32 : 0 < t ^ (3 / 2 : ℝ) := by positivity
    have hden : (1 - ρ) * t ^ (3 / 2 : ℝ) ≤ t ^ (3 / 2 : ℝ) - x ^ (3 / 2 : ℝ) := by
      have : x ^ (3 / 2 : ℝ) ≤ ρ * t ^ (3 / 2 : ℝ) := by
        rw [hρ, ← Real.mul_rpow (by positivity) ht0.le]
        refine Real.rpow_le_rpow hx.le ?_ (by norm_num)
        rw [div_mul_eq_mul_div, le_div_iff₀ hd0]
        exact mul_le_mul_of_nonneg_left hdt hx.le
      linarith
    have hnd : ‖(x : ℂ) ^ (3 / 2 : ℂ) - (t : ℂ) ^ (3 / 2 : ℂ)‖ =
        t ^ (3 / 2 : ℝ) - x ^ (3 / 2 : ℝ) := by
      rw [airyPV_cpow_three_halves hx.le, airyPV_cpow_three_halves ht0.le, ← ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg]
      have := Real.rpow_le_rpow hx.le (lt_trans hd ht).le (by norm_num : (0:ℝ) ≤ 3/2)
      linarith
    have hn1 : ‖(t : ℂ) ^ (-3 / 4 : ℂ)‖ ≤ d ^ (-3 / 4 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have : ((-3 / 4 : ℂ)).re = (-3/4 : ℝ) := by norm_num
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos hd0 hdt (by norm_num)
    have hn2 : ‖exp (-(airyZeta t : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      simp only [neg_re, ofReal_re, Real.exp_le_one_iff, neg_nonpos]
      unfold airyZeta; positivity
    have hn3 : ‖airyAi t‖ ≤ C := by
      have := (hC t ht0.le).1; simpa using this
    have hnum : ‖(t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) * airyAi t‖ ≤
        d ^ (-3 / 4 : ℝ) * C := by
      rw [norm_mul, norm_mul]
      calc ‖(t : ℂ) ^ (-3 / 4 : ℂ)‖ * ‖exp (-(airyZeta t : ℂ))‖ * ‖airyAi t‖
          ≤ d ^ (-3 / 4 : ℝ) * 1 * C := by gcongr
        _ = _ := by ring
    rw [norm_div, hnd, show (-3 / 2 : ℝ) = -(3 / 2) by norm_num, Real.rpow_neg ht0.le,
      mul_comm K, ← div_eq_inv_mul]
    have h1ρ : 0 < 1 - ρ := by linarith
    calc _ ≤ d ^ (-3 / 4 : ℝ) * C / ((1 - ρ) * t ^ (3 / 2 : ℝ)) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = K / t ^ (3 / 2 : ℝ) := by simp only [K]; field_simp

/-- Convergence of the symmetric principal value in DLMF 9.10.19. -/
@[dlmf 9.10.E19]
theorem airyBi_stieltjes_principalValue_converges {x : ℝ} (hx : 0 < x) :
    let f := fun t : ℝ => (t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) *
      airyAi t / ((x : ℂ) ^ (3 / 2 : ℂ) - (t : ℂ) ^ (3 / 2 : ℂ))
    HasPrincipalValueIoi f x (principalValueIoi f x) := by
  intro f
  set φ : ℂ → ℂ := fun s => s ^ (3 / 2 : ℂ) with hφ
  set D : ℂ → ℂ := dslope φ x with hD
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) * airyAi t with hg
  set h : ℝ → ℂ := fun t => g t * (-(D t)⁻¹) with hh
  have hfh : ∀ t : ℝ, t ≠ x → f t = h t / (t - x) := by
    intro t htx
    have htx' : (t : ℂ) ≠ x := by exact_mod_cast htx
    have hDt : D t = ((t : ℂ) - x)⁻¹ * (φ t - φ x) := by
      simp only [hD, dslope_of_ne _ htx', slope_def_module, smul_eq_mul]
    have hsub : (t : ℂ) - x ≠ 0 := sub_ne_zero.mpr htx'
    simp only [f, h, hDt, hφ, hg]
    rw [mul_inv, inv_inv]
    by_cases hz : (t : ℂ) ^ (3 / 2 : ℂ) - (x : ℂ) ^ (3 / 2 : ℂ) = 0
    · rw [hz, show (x : ℂ) ^ (3 / 2 : ℂ) - (t : ℂ) ^ (3 / 2 : ℂ) = 0 by
        linear_combination -hz]
      simp
    · have hz' : (x : ℂ) ^ (3 / 2 : ℂ) - (t : ℂ) ^ (3 / 2 : ℂ) ≠ 0 := by
        intro h0; exact hz (by linear_combination -h0)
      field_simp
      ring
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hslit := airyPV_ball_slitPlane hx
  obtain ⟨hDd, hDx, hDne, hDc⟩ := airyPV_dslope_facts hx
  have hζc : Continuous airyZeta := by
    unfold airyZeta; exact continuous_const.mul (Real.continuous_rpow_const (by norm_num))
  have hAc : Continuous fun t : ℝ => airyAi t := differentiable_airyAi.continuous.comp
    continuous_ofReal
  set b : ℝ := 2 * x with hb
  have hxb : x < b := by rw [hb]; linarith
  have hgi : IntegrableOn g (Icc 0 b) := by
    have h1 := intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := b)
      (r := (-3/4 : ℂ)) (by norm_num)
    have hec : Continuous fun t : ℝ => exp (-(airyZeta t : ℂ)) :=
      Complex.continuous_exp.comp (continuous_ofReal.comp hζc).neg
    have h2 := (h1.mul_continuousOn hec.continuousOn).mul_continuousOn hAc.continuousOn
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp h2
  have hqc : ContinuousOn (fun t : ℝ => -(D t)⁻¹) (Icc 0 b) := fun t ht =>
    (((hDc t ht.1).comp continuous_ofReal.continuousAt).inv₀ (hDne t ht.1)).neg.continuousWithinAt
  have hhi : IntegrableOn h (Icc 0 b) := hgi.mul_continuousOn hqc isCompact_Icc
  have hgd : DifferentiableAt ℝ g x := by
    have h1 : DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) ^ (-3 / 4 : ℂ)) x :=
      ((hasDerivAt_id (x : ℂ)).cpow_const (c := (-3/4 : ℂ))
        (hslit _ (Metric.mem_ball_self hx))).comp_ofReal.differentiableAt
    have hζ : DifferentiableAt ℝ airyZeta x := by
      unfold airyZeta
      exact (differentiableAt_id.rpow_const (Or.inl hx.ne')).const_mul _
    have h2 : DifferentiableAt ℝ (fun t : ℝ => exp (-(airyZeta t : ℂ))) x :=
      (hζ.hasDerivAt.ofReal_comp.neg.cexp).differentiableAt
    have h3 : DifferentiableAt ℝ (fun t : ℝ => airyAi t) x :=
      (hasDerivAt_airyAi (x : ℂ)).comp_ofReal.differentiableAt
    exact (h1.mul h2).mul h3
  have hhd : DifferentiableAt ℝ h x := by
    have hq : DifferentiableAt ℝ (fun t : ℝ => -(D t)⁻¹) x :=
      ((hDd.inv hDx).neg).hasDerivAt.comp_ofReal.differentiableAt
    exact hgd.mul hq
  have hsub0 := pv_integrableOn_sub_of_differentiableAt hhi hhd
  have hsub : IntegrableOn (fun t => f t - h x / (t - x)) (Icc 0 b) := by
    refine hsub0.congr_fun_ae ?_
    have : ∀ᵐ t ∂(volume.restrict (Icc 0 b)), t ≠ x :=
      ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
    filter_upwards [this] with t ht
    simp only [hfh t ht]
  have htail : ∀ d : ℝ, x < d → IntegrableOn f (Ioi d) := fun d hd =>
    airyPV_tail_integrableOn hx hd
  have hP := airyPV_hasPrincipalValueIoi (h x) hx hxb hsub htail
  refine ⟨hP.1, ?_⟩
  rw [principalValueIoi, hP.2.limUnder_eq]
  exact hP.2

end DLMF.Airy
