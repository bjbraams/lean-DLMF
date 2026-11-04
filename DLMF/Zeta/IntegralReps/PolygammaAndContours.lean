/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.IntegralReps.ElementaryKernels
public import ToMathlib.Analysis.Complex.Carlson
public import DLMF.Gamma.MellinBarnes
public import DLMF.Gamma.IntegralRepresentations.DigammaAndBinet
public import DLMFMathlib.Analysis.Complex.KeyholeIntegral

/-!
# Polygamma and contour representations of zeta

The theta-function integral (DLMF 25.5.13–25.5.14), integrals involving polygamma functions
(DLMF 25.5.15–25.5.19) and the contour integrals (DLMF §25.5(iii)) of the Riemann zeta
function. The conventions are described in `DLMF.Zeta.IntegralReps`.

## Main definitions

* `zetaOmega`: `ω(x) = ∑_{n≥1} e^{-n²πx}` (DLMF 25.5.14).
* `keyholeLoopIntegral`: the keyhole loop integral around the negative real axis.

## Main results

* `zetaOmega_eq_jacobiTheta`: DLMF 25.5.14, `ω(x) = ½ (θ₃(0|ix) - 1)`.
* `riemannZeta_eq_integral_zetaOmega`: DLMF 25.5.13.
* `riemannZeta_eq_integral_log_sub_digamma`, `riemannZeta_eq_integral_inv_sub_trigamma`:
  DLMF 25.5.15–25.5.16.
* `riemannZeta_one_add_eq_integral_digamma`, `riemannZeta_one_add_eq_integral_trigamma`,
  `riemannZeta_nat_add_eq_integral_polygamma`: DLMF 25.5.17–25.5.19.
* `riemannZeta_eq_loop_integral`: DLMF 25.5.20.
* `riemannZeta_eq_loop_integral_add`: DLMF 25.5.21 in multiplied form.
* `eq_Gamma_one_sub_mul_of_eq_sin_mul_Gamma`: the continuation principle behind the loop
  integrals 25.5.20–25.5.21 and 25.11.30.
-/

@[expose] public noncomputable section

open Complex Filter Topology MeasureTheory Set Finset

open scoped Real

namespace DLMF.Zeta

/-! ### §25.5(ii) In terms of other functions -/

/-- DLMF 25.5.14: `ω(x) = ∑_{n≥1} e^{-n²πx}` (for `x > 0`; the `tsum` is `0` where the series
diverges, i.e. for `x ≤ 0`). -/
@[dlmf 25.5.E14]
def zetaOmega (x : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-((n + 1 : ℝ) ^ 2) * π * x)

/-- DLMF 25.5.14: `ω(x) = ½ (θ₃(0|ix) - 1)` for `x > 0`, with Mathlib's
`jacobiTheta τ = θ₃(0|τ) = ∑_{n ∈ ℤ} e^{πin²τ}`. -/
@[dlmf 25.5.E14]
theorem zetaOmega_eq_jacobiTheta {x : ℝ} (hx : 0 < x) :
    (zetaOmega x : ℂ) = (jacobiTheta (I * x) - 1) / 2 := by
  have hτ : 0 < (I * (x : ℂ)).im := by simpa using hx
  rw [jacobiTheta_eq_tsum_nat hτ]
  rw [zetaOmega, Complex.ofReal_tsum]
  have : ∀ n : ℕ, ((Real.exp (-((n + 1 : ℝ) ^ 2) * π * x) : ℝ) : ℂ) =
      cexp (π * I * ((n : ℂ) + 1) ^ 2 * (I * x)) := by
    intro n
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  simp_rw [this]
  ring

section StieltjesConstants
open HurwitzZeta

/-- The tail `x ↦ θ(x) - 1` of the even kernel on `(1, ∞)`. -/
noncomputable def evenKernelTail : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun x => (hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀)

/-- On `(1, ∞)` the tail is `2ω(x)`. -/
private lemma evenKernelTail_eq {x : ℝ} (hx : 1 < x) : evenKernelTail x = 2 *
    (zetaOmega x : ℂ) := by
  have hx0 : 0 < x := by linarith
  rw [evenKernelTail, indicator_of_mem (Set.mem_Ioi.mpr hx), zetaOmega_eq_jacobiTheta hx0]
  simp only [hurwitzEvenFEPair, Function.comp_apply, ite_true]
  rw [show (0 : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) by simp, evenKernel_def,
    jacobiTheta_eq_jacobiTheta₂]
  simp
  ring_nf

/-- The modified even kernel is `tail(x) + x^{-1/2} tail(1/x)` on `(0, ∞)`. -/
private lemma hurwitzEvenFEPair_zero_f_modif_eq {x : ℝ} (hx : 0 < x) :
    (hurwitzEvenFEPair 0).f_modif x =
      evenKernelTail x + (x : ℂ) ^ (-(1 / 2 : ℂ)) * evenKernelTail x⁻¹ := by
  rcases lt_trichotomy x 1 with h | rfl | h
  · have hi : 1 < x⁻¹ := one_lt_inv_iff₀.mpr ⟨hx, h⟩
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr h.le),
      indicator_of_mem (Set.mem_Ioo.mpr ⟨hx, h⟩), evenKernelTail,
      indicator_of_notMem (notMem_Ioi.mpr h.le), indicator_of_mem (Set.mem_Ioi.mpr hi)]
    simp only [hurwitzEvenFEPair, Function.comp_apply, ite_true, zero_add, smul_eq_mul, mul_one,
      one_mul]
    rw [evenKernel_functional_equation, ← evenKernel_eq_cosKernel_of_zero]
    push_cast
    rw [ofReal_cpow hx.le, ofReal_cpow hx.le, cpow_neg, one_div, one_div]
    push_cast
    rw [cpow_neg, one_div x, one_div (2 : ℂ)]
    ring
  · simp [WeakFEPair.f_modif, evenKernelTail]
  · have hi : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioo_of_ge h.le),
      evenKernelTail, indicator_of_notMem (notMem_Ioi.mpr hi.le)]
    simp

/-- The tail has a convergent Mellin transform everywhere. -/
private lemma mellinConvergent_evenKernelTail (a : ℂ) : MellinConvergent evenKernelTail a := by
  have hloc : LocallyIntegrableOn evenKernelTail (Set.Ioi 0) := by
    intro x hx
    obtain ⟨t, ht, ht'⟩ := (hurwitzEvenFEPair 0).hf_int.sub (locallyIntegrableOn_const _) x hx
    exact ⟨t, ht, ht'.indicator measurableSet_Ioi⟩
  refine mellinConvergent_of_isBigO_rpow (a := a.re + 1) (b := a.re - 1) hloc ?_
    (by linarith) ?_ (by linarith)
  · refine ((hurwitzEvenFEPair 0).hf_top (-(a.re + 1))).congr' ?_ .rfl
    filter_upwards [eventually_gt_atTop 1] with x hx
    rw [evenKernelTail, indicator_of_mem (Set.mem_Ioi.mpr hx)]
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ .rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [evenKernelTail, indicator_of_notMem (notMem_Ioi.mpr hx.2.le)]

/-- The Mellin transform of the tail as an integral of `ω` over `(1, ∞)`. -/
private lemma mellin_evenKernelTail (a : ℂ) :
    mellin evenKernelTail a = 2 * ∫ x in Set.Ioi (1 : ℝ), (x : ℂ) ^ a * zetaOmega x / x := by
  rw [mellin, ← integral_const_mul]
  have : ∀ x ∈ Set.Ioi (0 : ℝ), (x : ℂ) ^ (a - 1) • evenKernelTail x =
      (Set.Ioi 1).indicator (fun x : ℝ => 2 * ((x : ℂ) ^ a * zetaOmega x / x)) x := by
    intro x hx
    by_cases h : 1 < x
    · rw [indicator_of_mem (Set.mem_Ioi.mpr h), evenKernelTail_eq h, smul_eq_mul,
        cpow_sub _ _ (ofReal_ne_zero.mpr (ne_of_gt hx)), cpow_one]
      ring
    · rw [indicator_of_notMem (notMem_Ioi.mpr (not_lt.mp h)), evenKernelTail,
        indicator_of_notMem (notMem_Ioi.mpr (not_lt.mp h)), smul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi this, setIntegral_indicator measurableSet_Ioi,
    Set.Ioi_inter_Ioi, max_eq_right zero_le_one]

/-- `x^a ω(x)/x` is integrable on `(1, ∞)`. -/
private lemma integrableOn_cpow_mul_zetaOmega_div (a : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ a * zetaOmega x / x) (Set.Ioi 1) := by
  have h := ((mellinConvergent_evenKernelTail a).mono_set
      (Set.Ioi_subset_Ioi zero_le_one)).const_mul
    (1 / 2 : ℂ)
  refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simp only [smul_eq_mul]
  rw [evenKernelTail_eq hx, cpow_sub _ _ (ofReal_ne_zero.mpr hx0.ne'), cpow_one]
  ring

/-- The theta split of `Λ₀(s/2)`. -/
private lemma hurwitzEvenFEPair_zero_Λ₀_eq (s : ℂ) : (hurwitzEvenFEPair 0).Λ₀ (s / 2) =
    mellin evenKernelTail (s / 2) + mellin evenKernelTail ((1 - s) / 2) := by
  have h2 : MellinConvergent (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) • evenKernelTail x⁻¹)
      (s / 2) := by
    rw [MellinConvergent.cpow_smul]
    have e : (s / 2 + -(1 / 2)) / ((-1 : ℝ) : ℂ) = (1 - s) / 2 := by push_cast; ring
    have := (MellinConvergent.comp_rpow (f := evenKernelTail) (s := s / 2 + -(1 / 2))
      (a := -1) (by norm_num)).mpr (by rw [e]; exact mellinConvergent_evenKernelTail _)
    simpa only [Real.rpow_neg_one] using this
  have h3 : mellin (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) • evenKernelTail x⁻¹) (s / 2) =
      mellin evenKernelTail ((1 - s) / 2) := by
    rw [mellin_cpow_smul, mellin_comp_inv]; congr 1; ring
  rw [WeakFEPair.Λ₀, ← h3, ← (hasMellin_add (mellinConvergent_evenKernelTail _) h2).2]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  simp only [hurwitzEvenFEPair_zero_f_modif_eq hx, smul_eq_mul]

end StieltjesConstants
/-- DLMF 25.5.13: for `s ≠ 0, 1`,
`ζ(s) = π^{s/2}/(s(s-1)Γ(s/2)) + π^{s/2}/Γ(s/2) ∫₁^∞ (x^{s/2} + x^{(1-s)/2}) ω(x)/x dx`
(DLMF: `s ≠ 1`; at `s = 0` the printed first term is a removable `1/(0·∞)` form). -/
@[dlmf 25.5.E13]
theorem riemannZeta_eq_integral_zetaOmega {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => ((x : ℂ) ^ (s / 2) + (x : ℂ) ^ ((1 - s) / 2)) * zetaOmega x / x)
        (Ioi 1) ∧
      riemannZeta s = (π : ℂ) ^ (s / 2) / (s * (s - 1) * Gamma (s / 2)) +
        (π : ℂ) ^ (s / 2) / Gamma (s / 2) * ∫ x in Ioi (1 : ℝ),
          ((x : ℂ) ^ (s / 2) + (x : ℂ) ^ ((1 - s) / 2)) * zetaOmega x / x := by
  have he : (fun x : ℝ => ((x : ℂ) ^ (s / 2) + (x : ℂ) ^ ((1 - s) / 2)) * zetaOmega x / x) =
      fun x : ℝ => (x : ℂ) ^ (s / 2) * zetaOmega x / x +
        (x : ℂ) ^ ((1 - s) / 2) * zetaOmega x / x := by
    funext x; ring
  refine ⟨he ▸ (integrableOn_cpow_mul_zetaOmega_div _).add
      (integrableOn_cpow_mul_zetaOmega_div _), ?_⟩
  rw [he, integral_add (integrableOn_cpow_mul_zetaOmega_div _)
      (integrableOn_cpow_mul_zetaOmega_div _),
    riemannZeta_eq_completedRiemannZeta₀ hs0]
  have hc : completedRiemannZeta₀ s = (HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2 := rfl
  rw [hc, hurwitzEvenFEPair_zero_Λ₀_eq, mellin_evenKernelTail, mellin_evenKernelTail]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs1'' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hπ : (π : ℂ) ^ (-s / 2) = ((π : ℂ) ^ (s / 2))⁻¹ := by
    rw [neg_div, cpow_neg]
  have hπ0 : (π : ℂ) ^ (s / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [hπ]
  rcases eq_or_ne (Gamma (s / 2)) 0 with hG | hG
  · simp [hG]
  · field_simp
    ring

/-- The real kernel `tᵐ e^{-t}/(1 - e^{-t})` of the polygamma Laplace integral. -/
noncomputable def polygammaKernel (m : ℕ) (t : ℝ) : ℝ := t ^ m * Real.exp (-t) / (1 - Real.exp (-t))

/-- Estimate under the stated parameter and domain assumptions: `0 < polygammaKernel m t`. -/
private lemma polygammaKernel_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < polygammaKernel m t := by
  have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold polygammaKernel
  have := Real.exp_pos (-t)
  positivity

/-- `polygammaKernel m t · t^{σ-1} = t^{m+σ-1}/(eᵗ-1)`. -/
private lemma polygammaKernel_mul_rpow (m : ℕ) (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    polygammaKernel m t * t ^ (σ - 1) = t ^ ((m : ℝ) + σ - 1) / (Real.exp t - 1) := by
  have h1 : Real.exp t - 1 ≠ 0 := by
    have := Real.add_one_lt_exp (x := t) ht.ne'; linarith
  have h2 : 1 - Real.exp (-t) ≠ 0 := by
    have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [show (m : ℝ) + σ - 1 = (m : ℝ) + (σ - 1) by ring, Real.rpow_add ht, Real.rpow_natCast]
  unfold polygammaKernel
  rw [Real.exp_neg]
  have := Real.exp_pos t
  field_simp

/-- DLMF 25.5.19 core: `∫₀^∞ ψ^{(m)}(1+x) x^{-s} dx = (-1)^{m+1} Γ(1-s) Γ(m+s) ζ(m+s)`. -/
private lemma integral_polygamma_one_add_mul_cpow {s : ℂ} {m : ℕ} (hm : 1 ≤ m) (hs : 0 < s.re)
    (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s)) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) =
        (-1) ^ (m + 1) * (Gamma (1 - s) * Gamma (m + s) * riemannZeta (m + s)) := by
  set μ := volume.restrict (Ioi (0 : ℝ))
  set K : ℝ → ℝ → ℂ := fun x t =>
    (x : ℂ) ^ (-s) * cexp (-((t : ℂ) * x)) * (polygammaKernel m t : ℂ) with hK
  have h1s : 0 < (1 - s).re := by simp; linarith
  -- pointwise: the polygamma Laplace integral
  have hpt : ∀ x : ℝ, 0 < x → DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) =
      (-1) ^ (m + 1) * ∫ t in Ioi (0 : ℝ), K x t := by
    intro x hx
    have h := DLMF.Gamma.polygamma_eq_integral (n := m) (by omega) (x := 1 + x) (by linarith)
    push_cast at h
    rw [h, mul_comm, ← mul_assoc, mul_comm ((x : ℂ) ^ (-s)), mul_assoc,
      ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    simp only [hK, polygammaKernel]
    push_cast
    rw [show -((1 + (x : ℂ)) * t) = -(t : ℂ) + -((t : ℂ) * x) by ring, Complex.exp_add]
    ring
  -- the `x`-integral for fixed `t`
  have hxint : ∀ t : ℝ, 0 < t → Integrable (fun x => K x t) μ := by
    intro t ht
    have := (DLMF.Gamma.integrableOn_cpow_mul_exp_neg_mul h1s ht).mul_const
        (polygammaKernel m t : ℂ)
    simp only [sub_sub_cancel_left] at this
    exact this
  have hxval : ∀ t : ℝ, 0 < t → ∫ x in Ioi (0 : ℝ), K x t =
      Gamma (1 - s) * (t : ℂ) ^ (s - 1) * (polygammaKernel m t : ℂ) := by
    intro t ht
    simp only [hK]
    rw [integral_mul_const]
    have h := DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi h1s (z := (t : ℂ)) (by simpa using ht)
    simp only [sub_sub_cancel_left] at h
    rw [h, show -(1 - s) = s - 1 by ring]
  have hxnorm : ∀ t : ℝ, 0 < t → ∫ x in Ioi (0 : ℝ), ‖K x t‖ =
      Real.Gamma (1 - s.re) * (t ^ ((m : ℝ) + s.re - 1) / (Real.exp t - 1)) := by
    intro t ht
    have hA := polygammaKernel_pos m ht
    have e : ∀ x ∈ Ioi (0 : ℝ), ‖K x t‖ = x ^ ((1 - s.re) - 1) * Real.exp (-(t * x)) *
        polygammaKernel m t := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      simp only [hK, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hA, neg_re]
      rw [show -((t : ℂ) * x) = ((-(t * x) : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_mul_const,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) ht,
      ← polygammaKernel_mul_rpow m s.re ht, one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    ring_nf
  -- product integrability
  have hcont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : (0 : ℝ) < p.1 := hp1
    have hp2' : (0 : ℝ) < p.2 := hp2
    have hne : 1 - Real.exp (-p.2) ≠ 0 := by
      have : Real.exp (-p.2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hK, polygammaKernel]
    refine ContinuousAt.mul (ContinuousAt.mul ?_ (by fun_prop)) ?_
    · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hp1'.ne')).comp continuousAt_fst
    · refine Complex.continuous_ofReal.continuousAt.comp ?_
      exact ContinuousAt.div (by fun_prop) (by fun_prop) hne
  have hmeas : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ) := by
    rw [show μ.prod μ = volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) by
      rw [Measure.volume_eq_prod, Measure.prod_restrict]]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  have hms : 1 < ((m : ℂ) + s.re).re := by
    simp
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hint : Integrable (Function.uncurry K) (μ.prod μ) := by
    refine (integrable_prod_iff' hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hxint t ht
    · have h := ((integrableOn_cpow_div_exp_sub_one hms).norm.const_mul (Real.Gamma (1 - s.re)))
      refine h.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      simp only [Function.uncurry_apply_pair]
      rw [hxnorm t ht0, norm_div, norm_cpow_eq_rpow_re_of_pos ht0]
      congr 1
      have h1 : 0 < Real.exp t - 1 := by have := Real.add_one_lt_exp (x := t) ht0.ne'; linarith
      rw [show cexp (t : ℂ) - 1 = ((Real.exp t - 1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos h1]
      simp
  have hLHS : ∀ x ∈ Ioi (0 : ℝ), DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) =
      (-1) ^ (m + 1) * ∫ t, Function.uncurry K (x, t) ∂μ := fun x hx => hpt x hx
  refine ⟨?_, ?_⟩
  · refine ((hint.integral_prod_left).const_mul ((-1) ^ (m + 1))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using (hLHS x hx).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi hLHS, integral_const_mul]
    congr 1
    have hsw := integral_integral_swap (μ := μ) (ν := μ) (f := K) hint
    simp only [Function.uncurry_apply_pair]
    rw [hsw, setIntegral_congr_fun measurableSet_Ioi (fun t ht => hxval t ht)]
    have hval := DLMF.Gamma.integral_cpow_mul_exp_div_one_sub_exp (s := (m : ℂ) + s)
      (by simpa using hms) (x := 1) one_pos
    have e : ∀ t ∈ Ioi (0 : ℝ), Gamma (1 - s) * (t : ℂ) ^ (s - 1) * (polygammaKernel m t : ℂ) =
        Gamma (1 - s) * ((t : ℂ) ^ ((m : ℂ) + s - 1) * cexp (-(((1 : ℝ) : ℂ) * t)) /
          (1 - cexp (-(t : ℂ)))) := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      simp only [polygammaKernel]
      push_cast
      rw [show (m : ℂ) + s - 1 = (m : ℂ) + (s - 1) by ring, cpow_add _ _ ht0, cpow_natCast]
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, hval,
      zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hms)]
    push_cast
    ring

/-- DLMF 25.5.19 in the form proved, for use in 25.5.18. -/
private lemma riemannZeta_natCast_add_eq_integral_polygamma {s : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s)) (Ioi 0) ∧
      riemannZeta (m + s) = (-1) ^ (m - 1) * (Gamma s * sin (π * s) / (π * Gamma (m + s))) *
        ∫ x in Ioi (0 : ℝ), DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) := by
  obtain ⟨hI, hv⟩ := integral_polygamma_one_add_mul_cpow hm hs hs'
  refine ⟨hI, ?_⟩
  rw [hv]
  have hsin := Complex.sin_pi_mul_ne_zero_of_re_mem hs hs'
  have hG : Gamma ((m : ℂ) + s) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr := Complex.Gamma_mul_Gamma_one_sub s
  have hpow : (-1 : ℂ) ^ (m - 1) * (-1) ^ (m + 1) = 1 := by
    rw [← pow_add, show m - 1 + (m + 1) = 2 * m by omega, pow_mul]; norm_num
  have key : Gamma s * Gamma (1 - s) * sin (π * s) = π := by
    rw [hr]; field_simp
  calc riemannZeta (m + s)
      = ((-1 : ℂ) ^ (m - 1) * (-1) ^ (m + 1)) * (Gamma s * Gamma (1 - s) * sin (π * s)) / π *
          (Gamma (m + s) / Gamma (m + s)) * riemannZeta (m + s) := by
        rw [hpow, key, one_mul, div_self hπ, div_self hG]; ring
    _ = _ := by ring

/-- `∫₀^∞ u^{-s-1}(1 - e^{-u}) du = -Γ(-s)` for `0 < Re s < 1`, with integrability. -/
private lemma integral_cpow_mul_one_sub_exp_neg {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1) * (1 - cexp (-(u : ℂ)))) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (-s - 1) * (1 - cexp (-(u : ℂ))) = -Gamma (-s) := by
  have h := DLMF.Gamma.Gamma_truncated_exp (z := -s) (n := 0) (by simp; linarith)
    (by simp; linarith)
  simp at h
  have hG : Gamma (-s) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm => ?_
    have := congrArg re hm; simp at this
    rw [this] at hs hs'
    have h1 : 0 < m := by exact_mod_cast hs
    have h2 : m < 1 := by exact_mod_cast hs'
    omega
  have hI : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1) * (cexp (-(u : ℂ)) - 1)) (Ioi 0) := by
    by_contra hn
    rw [integral_undef hn] at h
    exact hG h
  refine ⟨hI.neg.congr_fun (fun u _ => by simp; ring) measurableSet_Ioi, ?_⟩
  rw [h, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  ring

/-- Scaling: `x^w (1 - e^{-tx}) = t^{-w} g(tx)` with `g(u) = u^w (1 - e^{-u})`. -/
private lemma cpow_mul_one_sub_exp_neg_scale (w : ℂ) {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    (x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x))) =
      (t : ℂ) ^ (-w) * (((t * x : ℝ) : ℂ) ^ w * (1 - cexp (-((t * x : ℝ) : ℂ)))) := by
  rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg ht.le hx.le, cpow_neg]
  have : (t : ℂ) ^ w ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast ht.ne'))
  field_simp

/-- DLMF 25.5.17: for `0 < Re s < 1`,
`ζ(1+s) = (sin(πs)/π) ∫₀^∞ (γ + ψ(1+x)) x^{-s-1} dx`. -/
@[dlmf 25.5.E17]
theorem riemannZeta_one_add_eq_integral_digamma {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => ((Real.eulerMascheroniConstant : ℂ) + digamma (1 + x)) *
        (x : ℂ) ^ (-s - 1)) (Ioi 0) ∧
      riemannZeta (1 + s) = sin (π * s) / π * ∫ x in Ioi (0 : ℝ),
        ((Real.eulerMascheroniConstant : ℂ) + digamma (1 + x)) * (x : ℂ) ^ (-s - 1) := by
  set μ := volume.restrict (Ioi (0 : ℝ))
  set w : ℂ := -s - 1 with hw
  set g : ℝ → ℂ := fun u => (u : ℂ) ^ w * (1 - cexp (-(u : ℂ))) with hg
  obtain ⟨hgI, hgV⟩ := integral_cpow_mul_one_sub_exp_neg hs hs'
  set C := ∫ u in Ioi (0 : ℝ), g u with hC
  set Cn := ∫ u in Ioi (0 : ℝ), ‖g u‖ with hCn
  set K : ℝ → ℝ → ℂ := fun x t =>
    (x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x))) * (1 / (cexp t - 1)) with hK
  have hscale : ∀ t : ℝ, 0 < t → IntegrableOn (fun x : ℝ => (x : ℂ) ^ w *
      (1 - cexp (-((t : ℂ) * x)))) (Ioi 0) ∧ ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ w *
      (1 - cexp (-((t : ℂ) * x))) = (t : ℂ) ^ s * C ∧
      ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x)))‖ = t ^ s.re * Cn := by
    intro t ht
    have hgt : IntegrableOn (fun x => g (t * x)) (Ioi 0) :=
      (integrableOn_Ioi_comp_mul_left_iff g 0 ht).mpr (by simpa using hgI)
    have e := fun x (hx : x ∈ Ioi (0 : ℝ)) => cpow_mul_one_sub_exp_neg_scale w ht hx
    refine ⟨IntegrableOn.congr_fun (hgt.const_mul ((t : ℂ) ^ (-w)))
      (fun x hx => (e x hx).symm) measurableSet_Ioi, ?_, ?_⟩
    · rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul]
      have := integral_comp_mul_left_Ioi g 0 ht
      simp only [mul_zero] at this
      simp only [hg] at this ⊢
      rw [this, Complex.real_smul, ← mul_assoc, ofReal_inv, ← cpow_neg_one,
        ← cpow_add _ _ (by exact_mod_cast ht.ne')]
      congr 2
      rw [hw]; ring
    · have e' : ∀ x ∈ Ioi (0 : ℝ), ‖(x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x)))‖ =
          t ^ (s.re + 1) * ‖g (t * x)‖ := by
        intro x hx
        rw [e x hx, norm_mul, norm_cpow_eq_rpow_re_of_pos ht]
        simp [hg, hw, add_comm]
      rw [setIntegral_congr_fun measurableSet_Ioi e', integral_const_mul]
      have := integral_comp_mul_left_Ioi (fun u => ‖g u‖) 0 ht
      simp only [mul_zero, smul_eq_mul] at this
      rw [this, ← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add ht]
      congr 2; ring
  -- the digamma Laplace integral
  have hpt : ∀ x : ℝ, 0 < x → ((Real.eulerMascheroniConstant : ℂ) + digamma (1 + x)) *
      (x : ℂ) ^ w = ∫ t in Ioi (0 : ℝ), K x t := by
    intro x hx
    have h1x : (0 : ℝ) < 1 + x := by linarith
    have hd := DLMF.Gamma.digamma_ofReal h1x
    push_cast at hd
    rw [hd, ← ofReal_add, add_comm, DLMF.Gamma.digamma_add_euler_Ioi h1x, ← integral_complex_ofReal,
      ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    have h1 : cexp (t : ℂ) - 1 ≠ 0 := exp_ofReal_sub_one_ne_zero ht0
    have h2 : (1 : ℂ) - cexp (-(t : ℂ)) ≠ 0 := by
      rw [sub_ne_zero, ← ofReal_neg, ← ofReal_exp]
      exact_mod_cast (Real.exp_lt_one_iff.mpr (by linarith)).ne'
    simp only [hK]
    push_cast
    rw [show -(1 + (x : ℂ)) * t = -(t : ℂ) + -((t : ℂ) * x) by ring, Complex.exp_add]
    rw [Complex.exp_neg (t : ℂ)] at h2 ⊢
    have h3 : cexp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  -- Fubini
  have hcont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : (0 : ℝ) < p.1 := hp1
    have hp2' : (0 : ℝ) < p.2 := hp2
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hK]
    refine ContinuousAt.mul (ContinuousAt.mul ?_ (by fun_prop)) ?_
    · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hp1'.ne')).comp continuousAt_fst
    · exact continuousAt_const.div (by fun_prop) (exp_ofReal_sub_one_ne_zero hp2')
  have hmeas : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ) := by
    rw [show μ.prod μ = volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) by
      rw [Measure.volume_eq_prod, Measure.prod_restrict]]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  have hBn : ∀ t : ℝ, 0 < t → ‖(1 : ℂ) / (cexp t - 1)‖ = 1 / (Real.exp t - 1) := by
    intro t ht
    have h1 : 0 < Real.exp t - 1 := by have := Real.add_one_lt_exp (x := t) ht.ne'; linarith
    rw [show cexp (t : ℂ) - 1 = ((Real.exp t - 1 : ℝ) : ℂ) by push_cast; rfl, norm_div,
      norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1]
  have hms : 1 < ((1 : ℂ) + s.re).re := by simp; linarith
  have hint : Integrable (Function.uncurry K) (μ.prod μ) := by
    refine (integrable_prod_iff' hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [Function.uncurry_apply_pair, hK] using
        (hscale t ht).1.mul_const ((1 : ℂ) / (cexp (t : ℂ) - 1))
    · have h := ((integrableOn_cpow_div_exp_sub_one hms).norm.mul_const Cn)
      refine h.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      simp only [Function.uncurry_apply_pair, hK]
      rw [show (fun x : ℝ => ‖(x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x))) * (1 / (cexp t - 1))‖) =
        fun x : ℝ => ‖(x : ℂ) ^ w * (1 - cexp (-((t : ℂ) * x)))‖ * ‖(1 : ℂ) / (cexp t - 1)‖ from
        funext fun x => norm_mul _ _]
      rw [integral_mul_const, (hscale t ht0).2.2, hBn t ht0, norm_div,
        norm_cpow_eq_rpow_re_of_pos ht0]
      have h1 : 0 < Real.exp t - 1 := by have := Real.add_one_lt_exp (x := t) ht0.ne'; linarith
      rw [show cexp (t : ℂ) - 1 = ((Real.exp t - 1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos h1]
      simp
      ring
  have hLHS : ∀ x ∈ Ioi (0 : ℝ), ((Real.eulerMascheroniConstant : ℂ) + digamma (1 + x)) *
      (x : ℂ) ^ (-s - 1) = ∫ t, Function.uncurry K (x, t) ∂μ := fun x hx => hpt x hx
  have hval : ∫ x in Ioi (0 : ℝ), ((Real.eulerMascheroniConstant : ℂ) + digamma (1 + x)) *
      (x : ℂ) ^ (-s - 1) = C * (Gamma (s + 1) * riemannZeta (s + 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hLHS]
    have hsw := integral_integral_swap (μ := μ) (ν := μ) (f := K) hint
    simp only [Function.uncurry_apply_pair]
    rw [hsw]
    have e : ∀ t ∈ Ioi (0 : ℝ), ∫ x, K x t ∂μ =
        C * ((t : ℂ) ^ (s + 1 - 1) / (cexp t - 1)) := by
      intro t ht
      simp only [hK]
      rw [integral_mul_const, (hscale t ht).2.1, show s + 1 - 1 = s by ring]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul]
    have hz := riemannZeta_eq_integral_exp_sub_one (s := s + 1) (by simp; linarith)
    have hG : Gamma (s + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    rw [hz.2]
    field_simp
  refine ⟨?_, ?_⟩
  · refine (hint.integral_prod_left).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using (hLHS x hx).symm
  · rw [hval, hgV, add_comm (1 : ℂ) s]
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs
    have hsin := Complex.sin_pi_mul_ne_zero_of_re_mem hs hs'
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hr := Complex.Gamma_mul_Gamma_one_sub s
    have h1 : Gamma (1 - s) = -s * Gamma (-s) := by
      rw [show 1 - s = -s + 1 by ring, Complex.Gamma_add_one _ (neg_ne_zero.mpr hs0)]
    rw [Complex.Gamma_add_one s hs0]
    have key : Gamma s * Gamma (1 - s) * sin (π * s) = π := by rw [hr]; field_simp
    rw [h1] at key
    have key2 : sin (π * s) * (-Gamma (-s) * (s * Gamma s)) = π := by linear_combination key
    rw [show sin (π * s) / π * (-Gamma (-s) * (s * Gamma s * riemannZeta (s + 1))) =
      (sin (π * s) * (-Gamma (-s) * (s * Gamma s))) / π * riemannZeta (s + 1) by ring, key2,
      div_self hπ, one_mul]

/-- DLMF 25.5.18: for `0 < Re s < 1`, `ζ(1+s) = (sin(πs)/(πs)) ∫₀^∞ ψ'(1+x) x^{-s} dx`. -/
@[dlmf 25.5.E18]
theorem riemannZeta_one_add_eq_integral_trigamma {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => DLMF.Gamma.polygamma 1 (1 + x) * (x : ℂ) ^ (-s)) (Ioi 0) ∧
      riemannZeta (1 + s) = sin (π * s) / (π * s) * ∫ x in Ioi (0 : ℝ),
        DLMF.Gamma.polygamma 1 (1 + x) * (x : ℂ) ^ (-s) := by
  obtain ⟨hI, hv⟩ := riemannZeta_natCast_add_eq_integral_polygamma (m := 1) le_rfl hs hs'
  refine ⟨hI, ?_⟩
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  rw [Nat.cast_one] at hv
  rw [hv, add_comm (1 : ℂ) s, Complex.Gamma_add_one s hs0]
  simp only [Nat.sub_self, pow_zero, one_mul]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-! ### DLMF 25.5.15–25.5.16 -/

/-- Telescoping: `∑_k (1/(y+k) - 1/(y+k+1)) = 1/y` for `y > 0`. -/
private lemma hasSum_inv_add_sub_inv_add_succ {y : ℝ} (hy : 0 < y) :
    HasSum (fun k : ℕ => (y + k)⁻¹ - (y + k + 1)⁻¹) y⁻¹ := by
  have hnn : ∀ k : ℕ, 0 ≤ (y + k)⁻¹ - (y + k + 1)⁻¹ := fun k => by
    have : 0 < y + k := by positivity
    rw [sub_nonneg]; exact inv_anti₀ this (by linarith)
  refine (hasSum_iff_tendsto_nat_of_nonneg hnn _).mpr ?_
  simp_rw [DLMF.Gamma.Real.sum_recip_sub_recip_range]
  have h : Tendsto (fun N : ℕ => (y + N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ y tendsto_natCast_atTop_atTop)
  simpa using h.const_sub y⁻¹

/-- `1/y ≤ ∑_k 1/(y+k)² ≤ 1/y + 1/y²` for `y > 0`. -/
private lemma tsum_inv_add_sq_bounds {y : ℝ} (hy : 0 < y) :
    y⁻¹ ≤ ∑' k : ℕ, (y + k)⁻¹ ^ 2 ∧ ∑' k : ℕ, (y + k)⁻¹ ^ 2 ≤ y⁻¹ + y⁻¹ ^ 2 := by
  have hS := (DLMF.Gamma.Real.summable_trigamma hy).hasSum
  have hT := hasSum_inv_add_sub_inv_add_succ hy
  constructor
  · refine hasSum_le (fun k => ?_) hT hS
    have h0 : 0 < y + k := by positivity
    rw [inv_sub_inv h0.ne' (by positivity : y + k + 1 ≠ 0), inv_pow]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  · have hS' := (hasSum_nat_add_iff' 1).mpr hS
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, add_zero] at hS'
    have hle : ∑' k : ℕ, (y + k)⁻¹ ^ 2 - y⁻¹ ^ 2 ≤ y⁻¹ := by
      refine hasSum_le (fun k => ?_) hS' hT
      have h0 : 0 < y + k := by positivity
      push_cast
      rw [inv_sub_inv h0.ne' (by positivity : y + k + 1 ≠ 0), inv_pow,
        show y + ((k : ℝ) + 1) = y + k + 1 by ring, show y + k + 1 - (y + k) = (1 : ℝ) by ring,
        ← one_div]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    linarith

/-- For real `x ≥ 0`, `ψ'(1+x)` is real with `|1/(1+x) - ψ'(1+x)| ≤ 1/(1+x)²`. -/
private lemma norm_inv_sub_polygamma_one_le {x : ℝ} (hx : 0 ≤ x) :
    ‖1 / (1 + (x : ℂ)) - DLMF.Gamma.polygamma 1 (1 + x)‖ ≤ 1 / (1 + x) ^ 2 := by
  have hy : 0 < 1 + x := by linarith
  have hmem : (1 + (x : ℂ)) ∈ DLMF.Gamma.notNegNat := by
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hP := DLMF.Gamma.polygamma_eq_tsum (n := 1) one_pos hmem
  have hterm : ∀ k : ℕ, ((1 + (x : ℂ)) + k) ^ (-1 - ((1 : ℕ) : ℤ)) =
      (((1 + x + k)⁻¹ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [show (-1 - ((1 : ℕ) : ℤ)) = -2 by norm_num, zpow_neg, zpow_ofNat, inv_pow]
    push_cast
    rfl
  simp_rw [hterm] at hP
  rw [← Complex.ofReal_tsum] at hP
  obtain ⟨h1, h2⟩ := tsum_inv_add_sq_bounds hy
  rw [hP]
  simp only [pow_add, pow_one, neg_one_mul, neg_neg, Nat.factorial_one, Nat.cast_one, mul_one,
    one_mul]
  rw [show (1 : ℂ) / (1 + (x : ℂ)) = (((1 + x)⁻¹ : ℝ) : ℂ) by push_cast; ring, ← ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_le]
  rw [one_div, ← inv_pow]
  constructor <;> linarith


/-- The strip `0 < Re s < 2` with `s = 1` removed is preconnected. -/
private lemma isPreconnected_strip_diff_one :
    IsPreconnected ({s : ℂ | 0 < s.re ∧ s.re < 2} \ {1}) := by
  set S : Set ℂ := {s | 0 < s.re} ∩ {s | s.re < 2}
  have cS : Convex ℝ S := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 2)
  set Q1 : Set ℂ := S ∩ {s | 0 < s.im}
  set Q2 : Set ℂ := S ∩ {s | s.im < 0}
  set Q3 : Set ℂ := S ∩ {s | s.re < 1}
  set Q4 : Set ℂ := S ∩ {s | 1 < s.re}
  have c1 : Convex ℝ Q1 := cS.inter (convex_halfSpace_im_gt 0)
  have c2 : Convex ℝ Q2 := cS.inter (convex_halfSpace_im_lt 0)
  have c3 : Convex ℝ Q3 := cS.inter (convex_halfSpace_re_lt 1)
  have c4 : Convex ℝ Q4 := cS.inter (convex_halfSpace_re_gt 1)
  have h13 := c1.isPreconnected.union ((1 / 2 : ℂ) + I) (by simp [Q1, S]; norm_num)
    (by simp [Q3, S]; norm_num) c3.isPreconnected
  have h132 := h13.union ((1 / 2 : ℂ) - I) (Or.inr (by simp [Q3, S]; norm_num))
    (by simp [Q2, S]; norm_num) c2.isPreconnected
  have h := h132.union ((3 / 2 : ℂ) + I) (Or.inl (Or.inl (by simp [Q1, S]; norm_num)))
    (by simp [Q4, S]; norm_num) c4.isPreconnected
  convert h using 1
  ext s
  simp only [Q1, Q2, Q3, Q4, S, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    Set.mem_union, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨h0, h2⟩, h1⟩
    rcases lt_trichotomy s.im 0 with hi | hi | hi
    · exact Or.inl (Or.inr ⟨⟨h0, h2⟩, hi⟩)
    · rcases lt_trichotomy s.re 1 with hr | hr | hr
      · exact Or.inl (Or.inl (Or.inr ⟨⟨h0, h2⟩, hr⟩))
      · exact absurd (Complex.ext (by simpa using hr) (by simpa using hi)) h1
      · exact Or.inr ⟨⟨h0, h2⟩, hr⟩
    · exact Or.inl (Or.inl (Or.inl ⟨⟨h0, h2⟩, hi⟩))
  · rintro (((⟨hS, hi⟩ | ⟨hS, hi⟩) | ⟨hS, hi⟩) | ⟨hS, hi⟩) <;>
      exact ⟨hS, fun h => by rw [h] at hi; norm_num at hi⟩

/-- The kernel `1/(1+x) - ψ'(1+x)` of DLMF 25.5.16. -/
private def trigammaRemainder (x : ℝ) : ℂ :=
  1 / (1 + (x : ℂ)) - DLMF.Gamma.polygamma 1 (1 + x)

/-- `1/(1+x) - ψ'(1+x)` is continuous on `[0, ∞)`. -/
private lemma continuousOn_trigammaRemainder : ContinuousOn trigammaRemainder (Ici 0) := by
  intro x hx
  have hx : (0 : ℝ) ≤ x := hx
  have hne : ∀ m : ℕ, (1 + (x : ℂ)) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have ha : AnalyticAt ℂ (DLMF.Gamma.polygamma 1) (1 + x) := by
    have : DLMF.Gamma.polygamma 1 = deriv Complex.digamma := by
      funext z; simp [DLMF.Gamma.polygamma]
    rw [this]; exact (DLMF.Gamma.analyticAt_digamma hne).deriv
  have hc : ContinuousAt (fun y : ℝ => (1 + (y : ℂ))) x := by fun_prop
  apply ContinuousAt.continuousWithinAt
  refine ContinuousAt.sub ?_ (ContinuousAt.comp (g := DLMF.Gamma.polygamma 1) ha.continuousAt hc)
  refine continuousAt_const.div hc ?_
  intro h
  have := congrArg re h
  simp at this
  linarith

/-- `1/(1+x) - ψ'(1+x)` is locally integrable on `(0, ∞)`. -/
private lemma locallyIntegrableOn_trigammaRemainder :
    LocallyIntegrableOn trigammaRemainder (Ioi 0) :=
  (continuousOn_trigammaRemainder.mono Ioi_subset_Ici_self).locallyIntegrableOn measurableSet_Ioi

/-- `1/(1+x) - ψ'(1+x) = O(x⁻²)` as `x → ∞`. -/
private lemma trigammaRemainder_isBigO_top :
    trigammaRemainder =O[atTop] (· ^ (-(2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _), Real.rpow_neg hx.le,
    Real.rpow_two]
  refine (norm_inv_sub_polygamma_one_le hx.le).trans ?_
  rw [one_div]
  exact inv_anti₀ (by positivity) (by nlinarith)

/-- `1/(1+x) - ψ'(1+x) = O(1)` as `x → 0+`. -/
private lemma trigammaRemainder_isBigO_bot :
    trigammaRemainder =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx : (0 : ℝ) < x := hx
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  refine (norm_inv_sub_polygamma_one_le hx.le).trans ?_
  rw [div_le_one (by positivity)]
  nlinarith

/-- The integral of DLMF 25.5.16 as a Mellin transform at `2 - s`. -/
private lemma mellin_trigammaRemainder (s : ℂ) :
    mellin trigammaRemainder (2 - s) =
      ∫ x in Ioi (0 : ℝ), trigammaRemainder x * (x : ℂ) ^ (1 - s) := by
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [smul_eq_mul, mul_comm, show 2 - s - 1 = 1 - s by ring]

/-- The integrand of DLMF 25.5.16 is integrable for `0 < Re s < 2`. -/
private lemma integrableOn_trigammaRemainder_mul_cpow {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 2) :
    IntegrableOn (fun x : ℝ => trigammaRemainder x * (x : ℂ) ^ (1 - s)) (Ioi 0) := by
  have h := mellinConvergent_of_isBigO_rpow (s := 2 - s) locallyIntegrableOn_trigammaRemainder
    trigammaRemainder_isBigO_top (by simp; linarith) trigammaRemainder_isBigO_bot
    (by simp; linarith)
  refine IntegrableOn.congr_fun h (fun x _ => ?_) measurableSet_Ioi
  rw [smul_eq_mul, mul_comm, show 2 - s - 1 = 1 - s by ring]

/-- The integral of DLMF 25.5.16 is holomorphic in `s` on the strip `0 < Re s < 2`. -/
private lemma differentiableAt_mellin_trigammaRemainder {s : ℂ} (hs : 0 < s.re)
    (hs' : s.re < 2) : DifferentiableAt ℂ (fun z => mellin trigammaRemainder (2 - z)) s :=
  (mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_trigammaRemainder
    trigammaRemainder_isBigO_top (by simp; linarith) trigammaRemainder_isBigO_bot
    (by simp; linarith)).comp s ((differentiableAt_const _).sub differentiableAt_id)

/-- DLMF 25.5.16 written at `s = 1 + t` for `0 < Re t < 1`. -/
private lemma riemannZeta_one_add_eq_integral_trigammaRemainder {t : ℂ} (ht : 0 < t.re)
    (ht' : t.re < 1) :
    riemannZeta (1 + t) = 1 / t + sin (π * (1 + t)) / (π * t) *
      ∫ x in Ioi (0 : ℝ), trigammaRemainder x * (x : ℂ) ^ (-t) := by
  obtain ⟨hJ, hv⟩ := riemannZeta_one_add_eq_integral_trigamma ht ht'
  have h1t : 0 < (1 - t).re := by simp; linarith
  have h1t' : (1 - t).re < (1 : ℂ).re := by simp; linarith
  have hM := DLMF.Gamma.mellin_one_add_cpow_neg (a := 1) h1t h1t'
  rw [show (1 : ℂ) - (1 - t) = t by ring, Complex.Gamma_one, div_one] at hM
  simp only [mellin] at hM
  have hsin := Complex.sin_pi_mul_ne_zero_of_re_mem ht ht'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr := Complex.Gamma_mul_Gamma_one_sub t
  have hGne : Gamma (1 - t) * Gamma t ≠ 0 := by
    rw [mul_comm, hr]; exact div_ne_zero hπ hsin
  have hMI : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (1 - t - 1) • ((1 + x : ℝ) : ℂ) ^ (-(1 : ℂ))) (Ioi 0) := by
    by_contra hn
    exact hGne (by rw [← hM, integral_undef hn])
  have hpt : ∀ x ∈ Ioi (0 : ℝ), trigammaRemainder x * (x : ℂ) ^ (-t) =
      (x : ℂ) ^ (1 - t - 1) • ((1 + x : ℝ) : ℂ) ^ (-(1 : ℂ)) -
        DLMF.Gamma.polygamma 1 (1 + x) * (x : ℂ) ^ (-t) := by
    intro x _
    rw [show (1 : ℂ) - t - 1 = -t by ring, smul_eq_mul, Complex.cpow_neg_one]
    simp only [trigammaRemainder]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub hMI hJ, hM, hv]
  have hsin1 : sin (π * (1 + t)) = -sin (π * t) := by
    rw [mul_add, mul_one, add_comm, Complex.sin_add_pi]
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  rw [hsin1, mul_comm (Gamma (1 - t)), hr]
  field_simp
  ring

/-- DLMF 25.5.16: for `0 < Re s < 2`, `s ≠ 1` (DLMF's wider range for this formula),
`ζ(s) = 1/(s-1) + (sin(πs)/(π(s-1))) ∫₀^∞ (1/(1+x) - ψ'(1+x)) x^{1-s} dx`. -/
@[dlmf 25.5.E16]
theorem riemannZeta_eq_integral_inv_sub_trigamma {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 2)
    (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (1 / (1 + (x : ℂ)) - DLMF.Gamma.polygamma 1 (1 + x)) *
        (x : ℂ) ^ (1 - s)) (Ioi 0) ∧
      riemannZeta s = 1 / (s - 1) + sin (π * s) / (π * (s - 1)) * ∫ x in Ioi (0 : ℝ),
        (1 / (1 + (x : ℂ)) - DLMF.Gamma.polygamma 1 (1 + x)) * (x : ℂ) ^ (1 - s) := by
  refine ⟨integrableOn_trigammaRemainder_mul_cpow hs hs', ?_⟩
  set U : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 2} \ {1}
  have hUo : IsOpen U :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)).sdiff isClosed_singleton
  set F : ℂ → ℂ := fun z =>
    1 / (z - 1) + sin (π * z) / (π * (z - 1)) * mellin trigammaRemainder (2 - z)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hFd : DifferentiableOn ℂ F U := by
    intro z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz.2
    have hm := differentiableAt_mellin_trigammaRemainder hz.1.1 hz.1.2
    have hlin : DifferentiableAt ℂ (fun w : ℂ => w - 1) z :=
      differentiableAt_id.sub (differentiableAt_const _)
    have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 / (w - 1)) z :=
      (differentiableAt_const _).div hlin hz1
    have hsn : DifferentiableAt ℂ (fun w : ℂ => sin (π * w)) z :=
      Complex.differentiable_sin.differentiableAt.comp z
        ((differentiableAt_const _).mul differentiableAt_id)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => sin (π * w) / (π * (w - 1))) z :=
      hsn.div ((differentiableAt_const _).mul hlin) (mul_ne_zero hπ hz1)
    exact (h1.add (h2.mul hm)).differentiableWithinAt
  have hζd : DifferentiableOn ℂ riemannZeta U := fun z hz =>
    (differentiableAt_riemannZeta hz.2).differentiableWithinAt
  have h32 : (3 / 2 : ℂ) ∈ U := ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
  have heq : EqOn riemannZeta F U := by
    refine (hζd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
      (hFd.analyticOnNhd hUo) isPreconnected_strip_diff_one h32 ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re ∧ z.re < 2} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds (show (3 / 2 : ℂ) ∈ {z : ℂ | 1 < z.re ∧ z.re < 2} from
      ⟨by norm_num, by norm_num⟩)] with z hz
    have h := riemannZeta_one_add_eq_integral_trigammaRemainder (t := z - 1)
      (by simp; linarith [hz.1]) (by simp; linarith [hz.2])
    rw [show 1 + (z - 1) = z by ring] at h
    simp only [neg_sub] at h
    simp only [F, mellin_trigammaRemainder]
    exact h
  rw [heq ⟨⟨hs, hs'⟩, hs1⟩]
  simp only [F, mellin_trigammaRemainder]
  rfl


/-- The kernel `ln(1+x) - ψ(1+x)` of DLMF 25.5.15. -/
private def logDigammaRemainder (x : ℝ) : ℂ :=
  (Real.log (1 + x) : ℂ) - digamma (1 + x)

/-- `0 ≤ ln(1+x) - ψ(1+x) ≤ 1/(1+x)` gives `‖ln(1+x) - ψ(1+x)‖ ≤ 1/(1+x)` for `x ≥ 0`. -/
private lemma norm_logDigammaRemainder_le {x : ℝ} (hx : 0 ≤ x) :
    ‖logDigammaRemainder x‖ ≤ 1 / (1 + x) := by
  have h := DLMF.Gamma.digamma_ofReal (x := 1 + x) (by linarith)
  push_cast at h
  have he : logDigammaRemainder x =
      ((Real.log (1 + x) - DLMF.Gamma.Real.digamma (1 + x) : ℝ) : ℂ) := by
    simp only [logDigammaRemainder, h]; push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
  obtain ⟨h1, h2⟩ := DLMF.Gamma.digamma_le_log_and (x := 1 + x) (by linarith)
  have : 0 < 1 / (1 + x) := by positivity
  constructor <;> linarith

/-- The derivative of `ln(1+x) - ψ(1+x)` is `1/(1+x) - ψ'(1+x)`. -/
private lemma hasDerivAt_logDigammaRemainder {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt logDigammaRemainder (trigammaRemainder x) x := by
  have hne : ∀ m : ℕ, (1 + (x : ℂ)) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hd : HasDerivAt Complex.digamma (DLMF.Gamma.polygamma 1 (1 + x)) (1 + x) := by
    have : DLMF.Gamma.polygamma 1 (1 + (x : ℂ)) = deriv Complex.digamma (1 + x) := by
      simp [DLMF.Gamma.polygamma]
    rw [this]; exact (DLMF.Gamma.analyticAt_digamma hne).differentiableAt.hasDerivAt
  have hc : HasDerivAt (fun w : ℂ => Complex.digamma (1 + w))
      (DLMF.Gamma.polygamma 1 (1 + x)) (x : ℂ) := by
    have h := hd.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).const_add 1)
    rw [mul_one] at h
    exact h
  have hl : HasDerivAt (fun y : ℝ => ((Real.log (1 + y) : ℝ) : ℂ)) (((1 / (1 + x)) : ℝ) : ℂ) x :=
    (((hasDerivAt_id x).const_add 1).log (by simp; linarith)).ofReal_comp
  convert hl.sub hc.comp_ofReal using 1
  all_goals first
    | rfl
    | (simp only [trigammaRemainder]; push_cast; ring)

/-- `ln(1+x) - ψ(1+x)` is continuous on `[0, ∞)`. -/
private lemma continuousOn_logDigammaRemainder : ContinuousOn logDigammaRemainder (Ici 0) :=
  fun _ hx => (hasDerivAt_logDigammaRemainder hx).continuousAt.continuousWithinAt

/-- DLMF 25.5.15: for `0 < Re s < 1`,
`ζ(s) = 1/(s-1) + (sin(πs)/π) ∫₀^∞ (ln(1+x) - ψ(1+x)) x^{-s} dx`. -/
@[dlmf 25.5.E15]
theorem riemannZeta_eq_integral_log_sub_digamma {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => ((Real.log (1 + x) : ℂ) - digamma (1 + x)) * (x : ℂ) ^ (-s))
        (Ioi 0) ∧
      riemannZeta s = 1 / (s - 1) + sin (π * s) / π * ∫ x in Ioi (0 : ℝ),
        ((Real.log (1 + x) : ℂ) - digamma (1 + x)) * (x : ℂ) ^ (-s) := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs'
  have hs1' : -s + 1 ≠ 0 := by
    intro h; apply hs1; linear_combination -h
  have hnorm1 : 0 < ‖-s + 1‖ := norm_pos_iff.mpr hs1'
  -- the majorant `x^{-s}/(1+x)`
  have h1s : 0 < (1 - s).re := by simp; linarith
  have h1s' : (1 - s).re < (1 : ℂ).re := by simp; linarith
  have hM := DLMF.Gamma.mellin_one_add_cpow_neg (a := 1) h1s h1s'
  simp only [mellin] at hM
  have hsin := Complex.sin_pi_mul_ne_zero_of_re_mem hs hs'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hGne : Gamma (1 - s) * Gamma (1 - (1 - s)) / Gamma 1 ≠ 0 := by
    rw [show (1 : ℂ) - (1 - s) = s by ring, Complex.Gamma_one, div_one, mul_comm,
      Complex.Gamma_mul_Gamma_one_sub]
    exact div_ne_zero hπ hsin
  have hMI : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (1 - s - 1) • ((1 + x : ℝ) : ℂ) ^ (-(1 : ℂ))) (Ioi 0) := by
    by_contra hn
    exact hGne (by rw [← hM, integral_undef hn])
  have hInt : IntegrableOn (fun x : ℝ => logDigammaRemainder x * (x : ℂ) ^ (-s)) (Ioi 0) := by
    refine hMI.norm.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine (continuousOn_logDigammaRemainder.mono Ioi_subset_Ici_self).mul ?_
      intro x hx
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
      have hx : (0 : ℝ) < x := hx
      rw [show (1 : ℂ) - s - 1 = -s by ring, smul_eq_mul, Complex.cpow_neg_one, norm_mul,
        norm_mul, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_logDigammaRemainder_le hx.le).trans (le_of_eq ?_)
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), one_div]
  refine ⟨hInt, ?_⟩
  -- integration by parts
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt logDigammaRemainder (trigammaRemainder x) x :=
    fun x hx => hasDerivAt_logDigammaRemainder (le_of_lt hx)
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s + 1) / (-s + 1))
      ((x : ℂ) ^ (-s)) x := fun x hx =>
    hasDerivAt_ofReal_cpow_const' (ne_of_gt hx) (r := -s) (fun h => hs1 (by
      linear_combination -h))
  have hu'v : IntegrableOn
      (fun x : ℝ => trigammaRemainder x * ((x : ℂ) ^ (-s + 1) / (-s + 1))) (Ioi 0) := by
    refine IntegrableOn.congr_fun ((integrableOn_trigammaRemainder_mul_cpow hs
      (by linarith)).div_const (-s + 1)) (fun x _ => ?_) measurableSet_Ioi
    rw [show (1 : ℂ) - s = -s + 1 by ring]; ring
  have hbound : ∀ x : ℝ, 0 < x → ‖logDigammaRemainder x * ((x : ℂ) ^ (-s + 1) / (-s + 1))‖ ≤
      1 / (1 + x) * x ^ (1 - s.re) / ‖-s + 1‖ := by
    intro x hx
    rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, mul_div_assoc]
    refine mul_le_mul_of_nonneg_right (norm_logDigammaRemainder_le hx.le) (by positivity) |>.trans
      (le_of_eq ?_)
    simp only [add_re, neg_re, one_re]
    ring_nf
  have h_zero : Tendsto (fun x : ℝ => logDigammaRemainder x *
      ((x : ℂ) ^ (-s + 1) / (-s + 1))) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => x ^ (1 - s.re) / ‖-s + 1‖) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (1 - s.re) (Or.inr (by linarith))).tendsto
      rw [Real.zero_rpow (by linarith)] at this
      simpa using (this.mono_left nhdsWithin_le_nhds).div_const ‖-s + 1‖
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx : (0 : ℝ) < x := hx
    refine (hbound x hx).trans ?_
    rw [one_div_mul_eq_div]
    gcongr
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.rpow_nonneg hx.le (1 - s.re)]
  have h_infty : Tendsto (fun x : ℝ => logDigammaRemainder x *
      ((x : ℂ) ^ (-s + 1) / (-s + 1))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => x ^ (-s.re) / ‖-s + 1‖) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hs).div_const ‖-s + 1‖
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with x hx
    refine (hbound x hx).trans ?_
    gcongr
    rw [show -s.re = (1 - s.re) - 1 by ring, Real.rpow_sub_one hx.ne', one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left (by positivity) hx (by linarith)
  have hparts := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hInt hu'v h_zero h_infty
  have hI : ∫ x in Ioi (0 : ℝ), logDigammaRemainder x * (x : ℂ) ^ (-s) =
      (∫ x in Ioi (0 : ℝ), trigammaRemainder x * (x : ℂ) ^ (1 - s)) / (s - 1) := by
    rw [hparts, sub_self, zero_sub]
    have hfx : ∀ x : ℝ, trigammaRemainder x * ((x : ℂ) ^ (-s + 1) / (-s + 1)) =
        trigammaRemainder x * (x : ℂ) ^ (1 - s) / (-s + 1) := fun x => by
      rw [show (1 : ℂ) - s = -s + 1 by ring]; ring
    simp_rw [hfx]
    rw [integral_div]
    have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    ring
  have h16 : riemannZeta s = 1 / (s - 1) + sin (π * s) / (π * (s - 1)) *
      ∫ x in Ioi (0 : ℝ), trigammaRemainder x * (x : ℂ) ^ (1 - s) :=
    (riemannZeta_eq_integral_inv_sub_trigamma hs (by linarith) hs1).2
  show riemannZeta s = 1 / (s - 1) + sin (π * s) / π *
    ∫ x in Ioi (0 : ℝ), logDigammaRemainder x * (x : ℂ) ^ (-s)
  have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [hI, h16]
  field_simp


/-- DLMF 25.5.19: for `m ≥ 1` and `0 < Re s < 1`,
`ζ(m+s) = (-1)^{m-1} (Γ(s) sin(πs)/(π Γ(m+s))) ∫₀^∞ ψ^{(m)}(1+x) x^{-s} dx`. -/
@[dlmf 25.5.E19]
theorem riemannZeta_nat_add_eq_integral_polygamma {s : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s)) (Ioi 0) ∧
      riemannZeta (m + s) = (-1) ^ (m - 1) * (Gamma s * sin (π * s) / (π * Gamma (m + s))) *
        ∫ x in Ioi (0 : ℝ), DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) :=
  riemannZeta_natCast_add_eq_integral_polygamma hm hs hs'

/-! ### §25.5(iii) Contour integrals -/

/-- The keyhole loop integral `∫_{-∞}^{(0+)} z^a g(z) dz` around the negative real axis: from
`-∞` along the lower edge of the cut (`arg z = -π`) to `-δ`, once around the circle `|z| = δ`
in the positive direction, and back along the upper edge (`arg z = π`) to `-∞`. The power `z^a`
takes the boundary values `x^a e^{∓iπa}` on the two edges and its principal value
`δ^a e^{iaθ}`, `-π < θ < π`, on the circle. Parametrized,
`(e^{-iπa} - e^{iπa}) ∫_δ^∞ x^a g(-x) dx + ∫_{-π}^{π} δ^a e^{iaθ} g(δe^{iθ}) iδe^{iθ} dθ`
(DLMF §25.5(iii), the contour of 25.5.20–25.5.21). -/
@[dlmf 25.5.iii]
def keyholeLoopIntegral (g : ℂ → ℂ) (a : ℂ) (δ : ℝ) : ℂ :=
  (cexp (-(π * I * a)) - cexp (π * I * a)) * (∫ x in Ioi δ, (x : ℂ) ^ a * g (-x)) +
    ∫ θ in (-π)..π, (δ : ℂ) ^ a * cexp (I * a * θ) * g (δ * cexp (I * θ)) *
      (I * δ * cexp (I * θ))

/-- `e^{-iπ(s-1)} - e^{iπ(s-1)} = 2i sin(πs)`. -/
private lemma exp_sub_exp_loop (s : ℂ) :
    cexp (-(π * I * (s - 1))) - cexp (π * I * (s - 1)) = 2 * I * Complex.sin (π * s) := by
  rw [Complex.sin, show -(π * I * (s - 1)) = -(π * s) * I + π * I by ring,
    show π * I * (s - 1) = π * s * I - π * I by ring, exp_add, exp_sub, exp_pi_mul_I]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **Loop-integral continuation principle**: if `Φ` is holomorphic on `ℂ \ {1}`, `k` is entire
and `k(s) = (e^{-iπ(s-1)} - e^{iπ(s-1)}) Γ(s) Φ(s)` for `Re s > 1`, then
`Φ(s) = Γ(1-s)/(2πi) k(s)` for `s ≠ 1, 2, 3, …`. -/
theorem eq_Gamma_one_sub_mul_of_eq_sin_mul_Gamma {Φ k : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ {1}ᶜ) (hk : Differentiable ℂ k)
    (heq : ∀ s : ℂ, 1 < s.re →
      k s = (cexp (-(π * I * (s - 1))) - cexp (π * I * (s - 1))) * Gamma s * Φ s) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ n + 1) :
    Φ s = Gamma (1 - s) / (2 * π * I) * k s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  set F : ℂ → ℂ := fun t => Φ t * (Gamma (1 - t))⁻¹
  set G : ℂ → ℂ := fun t => k t / (2 * π * I)
  have hF : DifferentiableOn ℂ F {1}ᶜ := hΦ.mul
    ((differentiable_one_div_Gamma.comp (differentiable_id.const_sub 1)).differentiableOn)
  have hG : DifferentiableOn ℂ G {1}ᶜ := (hk.div_const _).differentiableOn
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) _).isPreconnected
  have h32 : (3 / 2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hFG : EqOn F G {1}ᶜ := by
    refine (hF.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hU)
      hpc h32 ?_
    filter_upwards [Metric.ball_mem_nhds (3 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)]
      with t ht
    rw [Metric.mem_ball, dist_eq_norm] at ht
    have hre := abs_re_le_norm (t - 3 / 2)
    have hre' : |t.re - 3 / 2| < 1 / 4 := by
      have : (t - 3 / 2 : ℂ).re = t.re - 3 / 2 := by simp
      rw [this] at hre; linarith
    have ht1 : 1 < t.re := by linarith [neg_abs_le (t.re - 3 / 2)]
    have hsin : Complex.sin (π * t) ≠ 0 := by
      rw [Complex.sin_ne_zero_iff]
      intro m hm
      have h1 : t = m := by
        have := Real.pi_ne_zero
        have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast this
        apply mul_left_cancel₀ hπ; rw [hm]; ring
      have h2 : t.re = m := by rw [h1]; simp
      rw [h2] at hre'
      have h3 : (1 : ℝ) < m := by rw [← h2]; exact ht1
      have h4 : (m : ℝ) < 2 := by linarith [le_abs_self ((m : ℝ) - 3 / 2)]
      have h5 : (1 : ℤ) < m := by exact_mod_cast h3
      have h6 : m < (2 : ℤ) := by exact_mod_cast h4
      omega
    have hΓ := Gamma_mul_Gamma_one_sub t
    have hΓ1 : Gamma (1 - t) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hΓ
      exact (div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hsin) hΓ.symm
    simp only [F, G, heq t ht1, exp_sub_exp_loop]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [eq_div_iff hsin] at hΓ
    have hinv : (Gamma (1 - t))⁻¹ = Gamma t * Complex.sin (π * t) / π := by
      field_simp
      rw [show t * (π : ℂ) = π * t by ring]
      linear_combination -hΓ
    rw [hinv]
    field_simp
  have hΓ1 : Gamma (1 - s) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm => hs m ?_
    linear_combination -hm
  have hs1 : s ∈ ({1}ᶜ : Set ℂ) := by
    simpa using (by simpa using hs 0 : s ≠ 1)
  have := hFG hs1
  simp only [F, G] at this
  field_simp at this
  rw [div_mul_eq_mul_div, eq_div_iff (by simp [Real.pi_ne_zero, I_ne_zero])]
  linear_combination this

/-- `e^{-z} ≠ 1` for `0 < |z| < 2π`. -/
private lemma exp_neg_sub_one_ne_zero {z : ℂ} (h0 : 0 < ‖z‖) (h : ‖z‖ < 2 * π) :
    cexp (-z) - 1 ≠ 0 :=
  sub_ne_zero.mpr (Complex.exp_ne_one_of_norm_lt (neg_ne_zero.mpr (norm_pos_iff.mp h0))
    (by rwa [norm_neg]))

/-- `|e^{-z} - 1| ≥ |z|/2` for `|z| ≤ 1/2`. -/
private lemma norm_exp_neg_sub_one_ge {z : ℂ} (h : ‖z‖ ≤ 1 / 2) :
    ‖z‖ / 2 ≤ ‖cexp (-z) - 1‖ := by
  simpa using Complex.half_norm_le_norm_exp_sub_one (z := -z) (by rwa [norm_neg])

/-- The integrand `1/(e^{-z} - 1)` of DLMF 25.5.20. -/
private lemma loopKernel_props {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π) :
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 2 * π → DifferentiableAt ℂ (fun z => 1 / (cexp (-z) - 1)) z) ∧
    (∃ M r : ℝ, 0 < r ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r → ‖z * (1 / (cexp (-z) - 1))‖ ≤ M) ∧
    ContinuousOn (fun z => 1 / (cexp (-z) - 1)) (Metric.sphere 0 δ) ∧
    ContinuousOn (fun x : ℝ => 1 / (cexp (-(-(x : ℂ))) - 1)) (Ioi δ) ∧
    ∀ x : ℝ, δ < x → ‖1 / (cexp (-(-(x : ℂ))) - 1)‖ ≤
      (1 - Real.exp (-δ))⁻¹ * Real.exp (-1 * x) := by
  have hd : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 2 * π →
      DifferentiableAt ℂ (fun z => 1 / (cexp (-z) - 1)) z := fun z h0 h =>
    (differentiableAt_const _).div ((differentiableAt_id.neg.cexp).sub_const 1)
      (exp_neg_sub_one_ne_zero h0 h)
  refine ⟨hd, ⟨2, 1 / 2, by norm_num, fun z h0 h => ?_⟩, fun z hz => ?_, fun x hx => ?_,
    fun x hx => ?_⟩
  · have := norm_exp_neg_sub_one_ge h.le
    rw [mul_one_div, norm_div, div_le_iff₀ (by linarith)]
    linarith
  · rw [mem_sphere_zero_iff_norm] at hz
    exact (hd z (by rw [hz]; exact hδ) (by rw [hz]; exact hδ')).continuousAt.continuousWithinAt
  · have hx0 : (0 : ℝ) < x := hδ.trans hx
    simp only [neg_neg]
    exact ((continuousAt_const.div ((continuous_exp.comp continuous_ofReal).continuousAt.sub
      continuousAt_const) (exp_ofReal_sub_one_ne_zero hx0))).continuousWithinAt
  · have hx0 : (0 : ℝ) < x := hδ.trans hx
    have he : 0 < Real.exp x - 1 := by linarith [Real.add_one_lt_exp hx0.ne']
    have hed : Real.exp (-δ) < 1 := by
      have := Real.exp_lt_exp.mpr (show -δ < 0 by linarith); simpa using this
    have hv : Real.exp (-1 * x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have hvu : Real.exp (-1 * x) ≤ Real.exp (-δ) := Real.exp_le_exp.mpr (by linarith)
    have hn : ‖1 / (cexp (-(-(x : ℂ))) - 1)‖ = 1 / (Real.exp x - 1) := by
      rw [neg_neg, show cexp (x : ℂ) - 1 = ((Real.exp x - 1 : ℝ) : ℂ) by push_cast; rfl,
        norm_div, norm_one, norm_real, Real.norm_of_nonneg he.le]
    have key : (1 - Real.exp (-δ))⁻¹ * Real.exp (-1 * x) * (Real.exp x - 1) =
        (1 - Real.exp (-δ))⁻¹ * (1 - Real.exp (-1 * x)) := by
      rw [mul_assoc, mul_sub, hv, mul_one]
    rw [hn, div_le_iff₀ he, key, le_inv_mul_iff₀ (by linarith)]
    linarith

/-- `e^{-z} ≠ -1` for `|z| < π`. -/
private lemma exp_neg_add_one_ne_zero {z : ℂ} (h : ‖z‖ < π) : cexp (-z) + 1 ≠ 0 := by
  intro h'
  have h2 : cexp (-(2 * z)) = 1 := by
    rw [show -(2 * z) = -z + -z by ring, exp_add, show cexp (-z) = -1 by
      linear_combination h']
    ring
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
  have hz : ‖z‖ = |(n : ℝ)| * π := by
    rw [show z = -(n * (π * I)) by linear_combination -hn / 2, norm_neg, norm_mul,
      norm_mul, norm_I, norm_intCast, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    ring
  rcases eq_or_ne n 0 with rfl | hn0
  · have hz0 : z = 0 := by simpa using hn
    rw [hz0, neg_zero, Complex.exp_zero] at h'
    norm_num at h'
  · have : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
    nlinarith [Real.pi_pos]

/-- The integrand `1/(e^{-z} + 1)` of DLMF 25.5.21. -/
private lemma loopKernelAdd_props {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < π → DifferentiableAt ℂ (fun z => 1 / (cexp (-z) + 1)) z) ∧
    (∃ M r : ℝ, 0 < r ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r → ‖z * (1 / (cexp (-z) + 1))‖ ≤ M) ∧
    ContinuousOn (fun z => 1 / (cexp (-z) + 1)) (Metric.sphere 0 δ) ∧
    ContinuousOn (fun x : ℝ => 1 / (cexp (-(-(x : ℂ))) + 1)) (Ioi δ) ∧
    ∀ x : ℝ, δ < x → ‖1 / (cexp (-(-(x : ℂ))) + 1)‖ ≤ 1 * Real.exp (-1 * x) := by
  have hd : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < π →
      DifferentiableAt ℂ (fun z => 1 / (cexp (-z) + 1)) z := fun z _ h =>
    (differentiableAt_const _).div ((differentiableAt_id.neg.cexp).add_const 1)
      (exp_neg_add_one_ne_zero h)
  have hpos : ∀ x : ℝ, 0 < Real.exp x + 1 := fun x => by positivity
  have hn : ∀ x : ℝ, ‖1 / (cexp (-(-(x : ℂ))) + 1)‖ = 1 / (Real.exp x + 1) := fun x => by
    rw [neg_neg, show cexp (x : ℂ) + 1 = ((Real.exp x + 1 : ℝ) : ℂ) by push_cast; rfl,
      norm_div, norm_one, norm_real, Real.norm_of_nonneg (hpos x).le]
  refine ⟨hd, ⟨1, 1 / 2, by norm_num, fun z h0 h => ?_⟩, fun z hz => ?_, fun x hx => ?_,
    fun x hx => ?_⟩
  · have h1 := Complex.norm_exp_sub_one_sub_id_le (x := -z) (by rw [norm_neg]; linarith)
    rw [norm_neg] at h1
    have h2 : 1 ≤ ‖cexp (-z) + 1‖ := by
      have := norm_sub_le (cexp (-z) + 1) (cexp (-z) - 1)
      rw [show cexp (-z) + 1 - (cexp (-z) - 1) = 2 by ring, Complex.norm_ofNat] at this
      have h3 := norm_sub_le (cexp (-z) - 1 - -z) z
      rw [show cexp (-z) - 1 - -z - z = cexp (-z) - 1 by ring] at h3
      nlinarith [norm_nonneg z]
    rw [mul_one_div, norm_div, div_le_iff₀ (by linarith)]
    nlinarith
  · rw [mem_sphere_zero_iff_norm] at hz
    exact (hd z (by rw [hz]; exact hδ) (by rw [hz]; exact hδ')).continuousAt.continuousWithinAt
  · simp only [neg_neg]
    refine ((continuousAt_const.div ((continuous_exp.comp continuous_ofReal).continuousAt.add
      continuousAt_const) ?_)).continuousWithinAt
    show cexp (x : ℂ) + 1 ≠ 0
    rw [show cexp (x : ℂ) + 1 = ((Real.exp x + 1 : ℝ) : ℂ) by push_cast; rfl]
    exact_mod_cast (hpos x).ne'
  · rw [hn, one_mul, div_le_iff₀ (hpos x)]
    have hv : Real.exp (-1 * x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-1 * x)]

/-- DLMF 25.5.20: for `s ∉ {1, 2, 3, …}`,
`ζ(s) = (Γ(1-s)/(2πi)) ∫_{-∞}^{(0+)} z^{s-1}/(e^{-z} - 1) dz`, the loop encircling the origin
once positively without enclosing `±2πi, ±4πi, …`; here over the keyhole of radius
`0 < δ < 2π`. -/
@[dlmf 25.5.E20]
theorem riemannZeta_eq_loop_integral {s : ℂ} (hs : ∀ n : ℕ, s ≠ n + 1) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 2 * π) :
    riemannZeta s = Gamma (1 - s) / (2 * π * I) *
      keyholeLoopIntegral (fun z => 1 / (cexp (-z) - 1)) (s - 1) δ := by
  obtain ⟨hd, hbd, hcirc, hedge, hdec⟩ := loopKernel_props hδ hδ'
  refine eq_Gamma_one_sub_mul_of_eq_sin_mul_Gamma (Φ := riemannZeta)
    (k := fun s => keyholeLoopIntegral (fun z => 1 / (cexp (-z) - 1)) (s - 1) δ)
    (fun t ht => (differentiableAt_riemannZeta ht).differentiableWithinAt) ?_ (fun t ht => ?_) hs
  · exact (Complex.differentiable_keyholeIntegral hδ one_pos hcirc hedge hdec).comp
      (differentiable_id.sub_const 1)
  · have ha : 0 < (t - 1).re := by simp; linarith
    have hint := (riemannZeta_eq_integral_exp_sub_one ht)
    simp only [keyholeLoopIntegral]
    rw [Complex.keyholeIntegral_eq_mul_integral_Ioi ha hδ hδ' hd ?_ hbd]
    · simp only [neg_neg, mul_one_div]
      rw [hint.2]
      have hG : Gamma t ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
      field_simp
    · simpa only [neg_neg, mul_one_div] using hint.1

/-- DLMF 25.5.21 (multiplied form): for `s ∉ {1, 2, 3, …}`,
`(1 - 2^{1-s}) ζ(s) = (Γ(1-s)/(2πi)) ∫_{-∞}^{(0+)} z^{s-1}/(e^{-z} + 1) dz`, the loop not
enclosing `±πi, ±3πi, …`; here over the keyhole of radius `0 < δ < π`. -/
@[dlmf 25.5.E21]
theorem riemannZeta_eq_loop_integral_add {s : ℂ} (hs : ∀ n : ℕ, s ≠ n + 1) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < π) :
    (1 - 2 ^ (1 - s)) * riemannZeta s = Gamma (1 - s) / (2 * π * I) *
      keyholeLoopIntegral (fun z => 1 / (cexp (-z) + 1)) (s - 1) δ := by
  obtain ⟨hd, hbd, hcirc, hedge, hdec⟩ := loopKernelAdd_props hδ hδ'
  refine eq_Gamma_one_sub_mul_of_eq_sin_mul_Gamma (Φ := fun t => (1 - 2 ^ (1 - t)) * riemannZeta t)
    (k := fun s => keyholeLoopIntegral (fun z => 1 / (cexp (-z) + 1)) (s - 1) δ)
    (fun t ht => ?_) ?_ (fun t ht => ?_) hs
  · refine (DifferentiableAt.mul ?_ (differentiableAt_riemannZeta ht)).differentiableWithinAt
    exact (differentiableAt_const _).sub ((differentiableAt_id.const_sub 1).const_cpow
      (Or.inl two_ne_zero))
  · exact (Complex.differentiable_keyholeIntegral hδ one_pos hcirc hedge hdec).comp
      (differentiable_id.sub_const 1)
  · have ha : 0 < (t - 1).re := by simp; linarith
    have ht1 : t ≠ 1 := by rintro rfl; simp at ht
    have hint := riemannZeta_eq_integral_exp_add_one (by linarith : 0 < t.re) ht1
    simp only [keyholeLoopIntegral]
    rw [Complex.keyholeIntegral_eq_mul_integral_Ioi ha hδ hδ' hd ?_ hbd]
    · simp only [neg_neg, mul_one_div]
      rw [← hint.2]
      ring
    · simpa only [neg_neg, mul_one_div] using hint.1

end DLMF.Zeta

end
