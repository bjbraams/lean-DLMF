/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.IntegralReps.ElementaryKernels

/-!
# Polygamma and contour representations of zeta

Integral formulas involving polygamma functions and the contour representations of the Riemann
zeta function.

Source references and common attribution are retained in
`DLMF.Zeta.IntegralReps`.
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

section s25a
open HurwitzZeta

/-- The tail `x ↦ θ(x) - 1` of the even kernel on `(1, ∞)`. -/
noncomputable def s25a_tail : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun x => (hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀)

/-- On `(1, ∞)` the tail is `2ω(x)`. -/
lemma s25a_tail_eq {x : ℝ} (hx : 1 < x) : s25a_tail x = 2 * (zetaOmega x : ℂ) := by
  have hx0 : 0 < x := by linarith
  rw [s25a_tail, indicator_of_mem (Set.mem_Ioi.mpr hx), zetaOmega_eq_jacobiTheta hx0]
  simp only [hurwitzEvenFEPair, Function.comp_apply, ite_true]
  rw [show (0 : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) by simp, evenKernel_def,
    jacobiTheta_eq_jacobiTheta₂]
  simp
  ring_nf

/-- The modified even kernel is `tail(x) + x^{-1/2} tail(1/x)` on `(0, ∞)`. -/
lemma s25a_f_modif_eq {x : ℝ} (hx : 0 < x) :
    (hurwitzEvenFEPair 0).f_modif x =
      s25a_tail x + (x : ℂ) ^ (-(1 / 2 : ℂ)) * s25a_tail x⁻¹ := by
  rcases lt_trichotomy x 1 with h | rfl | h
  · have hi : 1 < x⁻¹ := one_lt_inv_iff₀.mpr ⟨hx, h⟩
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr h.le),
      indicator_of_mem (Set.mem_Ioo.mpr ⟨hx, h⟩), s25a_tail,
      indicator_of_notMem (notMem_Ioi.mpr h.le), indicator_of_mem (Set.mem_Ioi.mpr hi)]
    simp only [hurwitzEvenFEPair, Function.comp_apply, ite_true, zero_add, smul_eq_mul, mul_one,
      one_mul]
    rw [evenKernel_functional_equation, ← evenKernel_eq_cosKernel_of_zero]
    push_cast
    rw [ofReal_cpow hx.le, ofReal_cpow hx.le, cpow_neg, one_div, one_div]
    push_cast
    rw [cpow_neg, one_div x, one_div (2 : ℂ)]
    ring
  · simp [WeakFEPair.f_modif, s25a_tail]
  · have hi : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioo_of_ge h.le),
      s25a_tail, indicator_of_notMem (notMem_Ioi.mpr hi.le)]
    simp

/-- The tail has a convergent Mellin transform everywhere. -/
lemma s25a_tail_mellinConvergent (a : ℂ) : MellinConvergent s25a_tail a := by
  have hloc : LocallyIntegrableOn s25a_tail (Set.Ioi 0) := by
    intro x hx
    obtain ⟨t, ht, ht'⟩ := (hurwitzEvenFEPair 0).hf_int.sub (locallyIntegrableOn_const _) x hx
    exact ⟨t, ht, ht'.indicator measurableSet_Ioi⟩
  refine mellinConvergent_of_isBigO_rpow (a := a.re + 1) (b := a.re - 1) hloc ?_
    (by linarith) ?_ (by linarith)
  · refine ((hurwitzEvenFEPair 0).hf_top (-(a.re + 1))).congr' ?_ .rfl
    filter_upwards [eventually_gt_atTop 1] with x hx
    rw [s25a_tail, indicator_of_mem (Set.mem_Ioi.mpr hx)]
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ .rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [s25a_tail, indicator_of_notMem (notMem_Ioi.mpr hx.2.le)]

/-- The Mellin transform of the tail as an integral of `ω` over `(1, ∞)`. -/
lemma s25a_tail_mellin (a : ℂ) :
    mellin s25a_tail a = 2 * ∫ x in Set.Ioi (1 : ℝ), (x : ℂ) ^ a * zetaOmega x / x := by
  rw [mellin, ← integral_const_mul]
  have : ∀ x ∈ Set.Ioi (0 : ℝ), (x : ℂ) ^ (a - 1) • s25a_tail x =
      (Set.Ioi 1).indicator (fun x : ℝ => 2 * ((x : ℂ) ^ a * zetaOmega x / x)) x := by
    intro x hx
    by_cases h : 1 < x
    · rw [indicator_of_mem (Set.mem_Ioi.mpr h), s25a_tail_eq h, smul_eq_mul,
        cpow_sub _ _ (ofReal_ne_zero.mpr (ne_of_gt hx)), cpow_one]
      ring
    · rw [indicator_of_notMem (notMem_Ioi.mpr (not_lt.mp h)), s25a_tail,
        indicator_of_notMem (notMem_Ioi.mpr (not_lt.mp h)), smul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi this, setIntegral_indicator measurableSet_Ioi,
    Set.Ioi_inter_Ioi, max_eq_right zero_le_one]

/-- `x^a ω(x)/x` is integrable on `(1, ∞)`. -/
lemma s25a_integrableOn (a : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ a * zetaOmega x / x) (Set.Ioi 1) := by
  have h := ((s25a_tail_mellinConvergent a).mono_set (Set.Ioi_subset_Ioi zero_le_one)).const_mul
    (1 / 2 : ℂ)
  refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simp only [smul_eq_mul]
  rw [s25a_tail_eq hx, cpow_sub _ _ (ofReal_ne_zero.mpr hx0.ne'), cpow_one]
  ring

/-- The theta split of `Λ₀(s/2)`. -/
lemma s25a_Λ₀ (s : ℂ) : (hurwitzEvenFEPair 0).Λ₀ (s / 2) =
    mellin s25a_tail (s / 2) + mellin s25a_tail ((1 - s) / 2) := by
  have h2 : MellinConvergent (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) • s25a_tail x⁻¹)
      (s / 2) := by
    rw [MellinConvergent.cpow_smul]
    have e : (s / 2 + -(1 / 2)) / ((-1 : ℝ) : ℂ) = (1 - s) / 2 := by push_cast; ring
    have := (MellinConvergent.comp_rpow (f := s25a_tail) (s := s / 2 + -(1 / 2))
      (a := -1) (by norm_num)).mpr (by rw [e]; exact s25a_tail_mellinConvergent _)
    simpa only [Real.rpow_neg_one] using this
  have h3 : mellin (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) • s25a_tail x⁻¹) (s / 2) =
      mellin s25a_tail ((1 - s) / 2) := by
    rw [mellin_cpow_smul, mellin_comp_inv]; congr 1; ring
  rw [WeakFEPair.Λ₀, ← h3, ← (hasMellin_add (s25a_tail_mellinConvergent _) h2).2]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  simp only [s25a_f_modif_eq hx, smul_eq_mul]

end s25a

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
  refine ⟨he ▸ (s25a_integrableOn _).add (s25a_integrableOn _), ?_⟩
  rw [he, integral_add (s25a_integrableOn _) (s25a_integrableOn _),
    riemannZeta_eq_completedRiemannZeta₀ hs0]
  have hc : completedRiemannZeta₀ s = (HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2 := rfl
  rw [hc, s25a_Λ₀, s25a_tail_mellin, s25a_tail_mellin]
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

/-- DLMF 25.5.15: for `0 < Re s < 1`,
`ζ(s) = 1/(s-1) + (sin(πs)/π) ∫₀^∞ (ln(1+x) - ψ(1+x)) x^{-s} dx`. -/
@[dlmf 25.5.E15]
theorem riemannZeta_eq_integral_log_sub_digamma {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => ((Real.log (1 + x) : ℂ) - digamma (1 + x)) * (x : ℂ) ^ (-s))
        (Ioi 0) ∧
      riemannZeta s = 1 / (s - 1) + sin (π * s) / π * ∫ x in Ioi (0 : ℝ),
        ((Real.log (1 + x) : ℂ) - digamma (1 + x)) * (x : ℂ) ^ (-s) := by
  sorry

/-- DLMF 25.5.16: for `0 < Re s < 2`, `s ≠ 1` (DLMF's wider range for this formula),
`ζ(s) = 1/(s-1) + (sin(πs)/(π(s-1))) ∫₀^∞ (1/(1+x) - ψ'(1+x)) x^{1-s} dx`. -/
@[dlmf 25.5.E16]
theorem riemannZeta_eq_integral_inv_sub_trigamma {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 2)
    (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (1 / (1 + (x : ℂ)) - DLMF.Gamma.polygamma 1 (1 + x)) *
        (x : ℂ) ^ (1 - s)) (Ioi 0) ∧
      riemannZeta s = 1 / (s - 1) + sin (π * s) / (π * (s - 1)) * ∫ x in Ioi (0 : ℝ),
        (1 / (1 + (x : ℂ)) - DLMF.Gamma.polygamma 1 (1 + x)) * (x : ℂ) ^ (1 - s) := by
  sorry

/-- The real kernel `tᵐ e^{-t}/(1 - e^{-t})` of the polygamma Laplace integral. -/
noncomputable def r25a_Ar (m : ℕ) (t : ℝ) : ℝ := t ^ m * Real.exp (-t) / (1 - Real.exp (-t))

/-- Estimate under the stated parameter and domain assumptions: `0 < r25a_Ar m t`. -/
lemma r25a_Ar_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < r25a_Ar m t := by
  have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold r25a_Ar
  have := Real.exp_pos (-t)
  positivity

/-- `r25a_Ar m t · t^{σ-1} = t^{m+σ-1}/(eᵗ-1)`. -/
lemma r25a_Ar_mul_rpow (m : ℕ) (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    r25a_Ar m t * t ^ (σ - 1) = t ^ ((m : ℝ) + σ - 1) / (Real.exp t - 1) := by
  have h1 : Real.exp t - 1 ≠ 0 := by
    have := Real.add_one_lt_exp (x := t) ht.ne'; linarith
  have h2 : 1 - Real.exp (-t) ≠ 0 := by
    have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [show (m : ℝ) + σ - 1 = (m : ℝ) + (σ - 1) by ring, Real.rpow_add ht, Real.rpow_natCast]
  unfold r25a_Ar
  rw [Real.exp_neg]
  have := Real.exp_pos t
  field_simp

/-- DLMF 25.5.19 core: `∫₀^∞ ψ^{(m)}(1+x) x^{-s} dx = (-1)^{m+1} Γ(1-s) Γ(m+s) ζ(m+s)`. -/
lemma r25a_integral_polygamma {s : ℂ} {m : ℕ} (hm : 1 ≤ m) (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s)) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) =
        (-1) ^ (m + 1) * (Gamma (1 - s) * Gamma (m + s) * riemannZeta (m + s)) := by
  set μ := volume.restrict (Ioi (0 : ℝ))
  set K : ℝ → ℝ → ℂ := fun x t =>
    (x : ℂ) ^ (-s) * cexp (-((t : ℂ) * x)) * (r25a_Ar m t : ℂ) with hK
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
    simp only [hK, r25a_Ar]
    push_cast
    rw [show -((1 + (x : ℂ)) * t) = -(t : ℂ) + -((t : ℂ) * x) by ring, Complex.exp_add]
    ring
  -- the `x`-integral for fixed `t`
  have hxint : ∀ t : ℝ, 0 < t → Integrable (fun x => K x t) μ := by
    intro t ht
    have := (DLMF.Gamma.integrableOn_cpow_mul_exp_neg_mul h1s ht).mul_const (r25a_Ar m t : ℂ)
    simp only [sub_sub_cancel_left] at this
    exact this
  have hxval : ∀ t : ℝ, 0 < t → ∫ x in Ioi (0 : ℝ), K x t =
      Gamma (1 - s) * (t : ℂ) ^ (s - 1) * (r25a_Ar m t : ℂ) := by
    intro t ht
    simp only [hK]
    rw [integral_mul_const]
    have h := DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi h1s (z := (t : ℂ)) (by simpa using ht)
    simp only [sub_sub_cancel_left] at h
    rw [h, show -(1 - s) = s - 1 by ring]
  have hxnorm : ∀ t : ℝ, 0 < t → ∫ x in Ioi (0 : ℝ), ‖K x t‖ =
      Real.Gamma (1 - s.re) * (t ^ ((m : ℝ) + s.re - 1) / (Real.exp t - 1)) := by
    intro t ht
    have hA := r25a_Ar_pos m ht
    have e : ∀ x ∈ Ioi (0 : ℝ), ‖K x t‖ = x ^ ((1 - s.re) - 1) * Real.exp (-(t * x)) *
        r25a_Ar m t := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      simp only [hK, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hA, neg_re]
      rw [show -((t : ℂ) * x) = ((-(t * x) : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_mul_const,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) ht,
      ← r25a_Ar_mul_rpow m s.re ht, one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
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
    simp only [hK, r25a_Ar]
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
    · have h := ((q25a_integrableOn_exp_sub_one hms).norm.const_mul (Real.Gamma (1 - s.re)))
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
    have e : ∀ t ∈ Ioi (0 : ℝ), Gamma (1 - s) * (t : ℂ) ^ (s - 1) * (r25a_Ar m t : ℂ) =
        Gamma (1 - s) * ((t : ℂ) ^ ((m : ℂ) + s - 1) * cexp (-(((1 : ℝ) : ℂ) * t)) /
          (1 - cexp (-(t : ℂ)))) := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      simp only [r25a_Ar]
      push_cast
      rw [show (m : ℂ) + s - 1 = (m : ℂ) + (s - 1) by ring, cpow_add _ _ ht0, cpow_natCast]
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, hval,
      zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hms)]
    push_cast
    ring

/-- Nonvanishing under the stated hypotheses: `sin (π * s) ≠ 0`. -/
lemma r25a_sin_pi_ne_zero {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) : sin (π * s) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  have h := congrArg re hk
  simp at h
  have hk' : s.re = k := by
    have := Real.pi_pos
    field_simp at h
    linarith
  rw [hk'] at hs hs'
  have h1 : (0 : ℤ) < k := by exact_mod_cast hs
  have h2 : k < (1 : ℤ) := by exact_mod_cast hs'
  omega

/-- DLMF 25.5.19 in the form proved, for use in 25.5.18. -/
lemma r25a_zeta_nat_add_eq_integral {s : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s)) (Ioi 0) ∧
      riemannZeta (m + s) = (-1) ^ (m - 1) * (Gamma s * sin (π * s) / (π * Gamma (m + s))) *
        ∫ x in Ioi (0 : ℝ), DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) := by
  obtain ⟨hI, hv⟩ := r25a_integral_polygamma hm hs hs'
  refine ⟨hI, ?_⟩
  rw [hv]
  have hsin := r25a_sin_pi_ne_zero hs hs'
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
lemma r25a_integral_cpow_one_sub_exp {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
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
lemma r25a_cpow_one_sub_exp_scale (w : ℂ) {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
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
  obtain ⟨hgI, hgV⟩ := r25a_integral_cpow_one_sub_exp hs hs'
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
    have e := fun x (hx : x ∈ Ioi (0 : ℝ)) => r25a_cpow_one_sub_exp_scale w ht hx
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
    have h1 : cexp (t : ℂ) - 1 ≠ 0 := q25a_exp_sub_one_ne ht0
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
    · exact continuousAt_const.div (by fun_prop) (q25a_exp_sub_one_ne hp2')
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
    · have h := ((q25a_integrableOn_exp_sub_one hms).norm.mul_const Cn)
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
    have hsin := r25a_sin_pi_ne_zero hs hs'
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
  obtain ⟨hI, hv⟩ := r25a_zeta_nat_add_eq_integral (m := 1) le_rfl hs hs'
  refine ⟨hI, ?_⟩
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  rw [Nat.cast_one] at hv
  rw [hv, add_comm (1 : ℂ) s, Complex.Gamma_add_one s hs0]
  simp only [Nat.sub_self, pow_zero, one_mul]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- DLMF 25.5.19: for `m ≥ 1` and `0 < Re s < 1`,
`ζ(m+s) = (-1)^{m-1} (Γ(s) sin(πs)/(π Γ(m+s))) ∫₀^∞ ψ^{(m)}(1+x) x^{-s} dx`. -/
@[dlmf 25.5.E19]
theorem riemannZeta_nat_add_eq_integral_polygamma {s : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (fun x : ℝ => DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s)) (Ioi 0) ∧
      riemannZeta (m + s) = (-1) ^ (m - 1) * (Gamma s * sin (π * s) / (π * Gamma (m + s))) *
        ∫ x in Ioi (0 : ℝ), DLMF.Gamma.polygamma m (1 + x) * (x : ℂ) ^ (-s) :=
  r25a_zeta_nat_add_eq_integral hm hs hs'

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

/-- DLMF 25.5.20: for `s ∉ {1, 2, 3, …}`,
`ζ(s) = (Γ(1-s)/(2πi)) ∫_{-∞}^{(0+)} z^{s-1}/(e^{-z} - 1) dz`, the loop encircling the origin
once positively without enclosing `±2πi, ±4πi, …`; here over the keyhole of radius
`0 < δ < 2π`. -/
@[dlmf 25.5.E20]
theorem riemannZeta_eq_loop_integral {s : ℂ} (hs : ∀ n : ℕ, s ≠ n + 1) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ < 2 * π) :
    riemannZeta s = Gamma (1 - s) / (2 * π * I) *
      keyholeLoopIntegral (fun z => 1 / (cexp (-z) - 1)) (s - 1) δ := by
  sorry

/-- DLMF 25.5.21 (multiplied form): for `s ∉ {1, 2, 3, …}`,
`(1 - 2^{1-s}) ζ(s) = (Γ(1-s)/(2πi)) ∫_{-∞}^{(0+)} z^{s-1}/(e^{-z} + 1) dz`, the loop not
enclosing `±πi, ±3πi, …`; here over the keyhole of radius `0 < δ < π`. -/
@[dlmf 25.5.E21]
theorem riemannZeta_eq_loop_integral_add {s : ℂ} (hs : ∀ n : ℕ, s ≠ n + 1) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < π) :
    (1 - 2 ^ (1 - s)) * riemannZeta s = Gamma (1 - s) / (2 * π * I) *
      keyholeLoopIntegral (fun z => 1 / (cexp (-z) + 1)) (s - 1) δ := by
  sorry

end DLMF.Zeta

end
