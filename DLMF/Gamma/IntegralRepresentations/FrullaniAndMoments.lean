/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.IntegralRepresentations.DigammaAndBinet

/-!
# Frullani integrals and Gamma logarithmic moments

Frullani-type digamma integrals and derivatives of the Gamma integral with respect to its order.

Source references and common attribution are retained in
`DLMF.Gamma.IntegralRepresentations`.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral

open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

local macro "deriv_simp" : tactic => `(tactic| first
  | (simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, id_eq];
      field_simp; ring)
  | (simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, id_eq];
      field_simp; done)
  | (simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, id_eq];
      ring)
  | (field_simp; ring) | (field_simp; done) | ring | (simp; field_simp; ring) | (simp; done))

open Set in
/-- DLMF 5.9.12, Gauss: `ψ(x) = ∫₀^∞ (e^(-t)/t - e^(-xt)/(1 - e^(-t))) dt` for `x > 0`. -/
@[dlmf 5.9.E12]
theorem digamma_gauss {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-t) / t - Real.exp (-x * t) / (1 - Real.exp (-t)) := by
  have hJ1 := integral_exp_mul_binetKernel_one
  have hA := integrableOn_digamma_add_euler hx
  have heq : EqOn (fun t => Real.exp (-t) / t - Real.exp (-x * t) / (1 - Real.exp (-t)))
      (fun t => (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) -
        Real.exp (-1 * t) * binetKernel t) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    simp only [binetKernel, neg_mul, one_mul]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_sub hA (integrableOn_exp_mul_binetKernel one_pos), ← digamma_add_euler_Ioi hx, hJ1]
  ring

open Set in
/-- DLMF 5.9.13: `ψ(x) = ln x + ∫₀^∞ (1/t - 1/(1 - e^(-t))) e^(-tx) dt` for `x > 0`. -/
@[dlmf 5.9.E13]
theorem digamma_binet {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      Real.log x +
        ∫ t : ℝ in Set.Ioi 0,
          (1 / t - 1 / (1 - Real.exp (-t))) * Real.exp (-t * x) := by
  rw [digamma_eq_log_sub hx, sub_eq_add_neg, ← MeasureTheory.integral_neg]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [binetKernel]
  ring_nf

section Frullani

/-! ### The Frullani-type integrals for `ψ` and `γ`

The substitution `u = eᵗ - 1` turns the integral `ψ(x) + γ = ∫₀^∞ (e^{-t} - e^{-xt})/(1 - e^{-t})`
into `∫₀^∞ ((1+u)⁻¹ - (1+u)^{-x})/u`. The constant `γ = ∫₀^∞ ((1+t)⁻¹ - e^{-t})/t` is found by
truncating at `ε`, where both `∫_ε^∞ dt/(t(1+t)) = log((1+ε)/ε)` and
`∫_ε^∞ dt/(eᵗ - 1) = -log(1 - e^{-ε})` are elementary. -/

open Set

/-- `0 ≤ ((1+t)⁻¹ - e^{-t})/t ≤ 2/(1+t²)` for `t > 0`. -/
theorem eulerIntegrand_mem {t : ℝ} (ht : 0 < t) :
    0 ≤ (1 / (1 + t) - Real.exp (-t)) / t ∧
      (1 / (1 + t) - Real.exp (-t)) / t ≤ 2 / (1 + t ^ 2) := by
  have he := Real.exp_pos (-t)
  have h1 : (1 + t) * Real.exp (-t) ≤ 1 := by
    have h := Real.add_one_le_exp t
    have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hN : 1 / (1 + t) - Real.exp (-t) = (1 - (1 + t) * Real.exp (-t)) / (1 + t) := by
    field_simp
  have hkey : 1 - t ≤ (1 + t) ^ 2 * Real.exp (-t) := by
    rcases le_or_gt t 1 with h | h
    · have := Real.add_one_le_exp (-t)
      nlinarith [sq_nonneg t]
    · nlinarith [mul_pos (pow_pos (by linarith : (0 : ℝ) < 1 + t) 2) he]
  rw [hN, div_div]
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    set N := 1 - (1 + t) * Real.exp (-t)
    have hN0 : 0 ≤ N := by linarith
    have hNk : (1 + t) * N ≤ 2 * t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hNk (by positivity : (0 : ℝ) ≤ 1 + t),
      mul_nonneg hN0 ht.le]

/-- `(1/(1 + t) - e^(-t))/t` is continuous on `(0, ∞)`. -/
theorem continuousOn_eulerIntegrand :
    ContinuousOn (fun t : ℝ => (1 / (1 + t) - Real.exp (-t)) / t) (Ioi 0) := by
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  have h1 : 1 + t ≠ 0 := by linarith
  have h2 : t ≠ 0 := ht'.ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

/-- `(1/(1 + t) - e^(-t))/t` is integrable on `(0, ∞)`. -/
theorem integrableOn_eulerIntegrand :
    IntegrableOn (fun t : ℝ => (1 / (1 + t) - Real.exp (-t)) / t) (Ioi 0) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul 2).integrableOn)
    (continuousOn_eulerIntegrand.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  obtain ⟨h0, h1⟩ := eulerIntegrand_mem ht
  rw [Real.norm_of_nonneg h0]
  simpa [div_eq_mul_inv] using h1

/-- `∫_ε^∞ dt/(t(1+t)) = log((1+ε)/ε)`. -/
theorem integral_Ioi_one_div_mul_one_add {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t => 1 / (t * (1 + t))) (Ioi ε) ∧
      ∫ t in Ioi ε, 1 / (t * (1 + t)) = Real.log ((1 + ε) / ε) := by
  set F : ℝ → ℝ := fun t => -Real.log (1 + t⁻¹) with hF
  have hd : ∀ t ∈ Ioi ε, HasDerivAt F (1 / (t * (1 + t))) t := by
    intro t ht
    have ht' : 0 < t := hε.trans ht
    have hpos : 0 < 1 + t⁻¹ := by positivity
    have := ((hasDerivAt_inv ht'.ne').const_add 1).log hpos.ne' |>.neg
    have h0 : t ≠ 0 := ht'.ne'
    have h1 : 1 + t ≠ 0 := by linarith
    exact this.congr_deriv (by deriv_simp)
  have hcont : ContinuousWithinAt F (Ici ε) ε := by
    have hpos : 0 < 1 + ε⁻¹ := by positivity
    exact (((continuousAt_inv₀ hε.ne').const_add 1).log hpos.ne').neg.continuousWithinAt
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_add 1)
    rw [add_zero] at h
    have := ((Real.continuousAt_log one_ne_zero).tendsto.comp h).neg
    simpa [hF, Function.comp_def] using this
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hd
    (fun t ht => by have : 0 < t := hε.trans ht; positivity) hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint hlim]
  simp only [hF, zero_sub, neg_neg]
  congr 1
  field_simp
  ring

/-- `∫_ε^∞ dt/(eᵗ - 1) = -log(1 - e^{-ε})`. -/
theorem integral_Ioi_one_div_exp_sub_one {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t => 1 / (Real.exp t - 1)) (Ioi ε) ∧
      ∫ t in Ioi ε, 1 / (Real.exp t - 1) = -Real.log (1 - Real.exp (-ε)) := by
  set F : ℝ → ℝ := fun t => Real.log (1 - Real.exp (-t)) with hF
  have hlt : ∀ t : ℝ, 0 < t → 0 < 1 - Real.exp (-t) := fun t ht => by
    have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
  have hd : ∀ t ∈ Ioi ε, HasDerivAt F (1 / (Real.exp t - 1)) t := by
    intro t ht
    have ht' : 0 < t := hε.trans ht
    have := (((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_sub 1).log
      (hlt t ht').ne'
    have h1 := (exp_sub_one_pos ht').ne'
    have h2 := (hlt t ht').ne'
    have h4 : Real.exp t ≠ 0 := Real.exp_ne_zero t
    rw [Real.exp_neg] at h2
    exact this.congr_deriv (by
      simp only [Function.comp_apply, Real.exp_neg]
      field_simp)
  have hcont : ContinuousWithinAt F (Ici ε) ε :=
    ((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousAt.log
      (hlt ε hε).ne').continuousWithinAt
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h : Tendsto (fun t => 1 - Real.exp (-t)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
    simpa [hF, Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp h
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hd
    (fun t ht => by have := exp_sub_one_pos (hε.trans ht); positivity) hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint hlim]
  simp [hF]

/-- `log((1+ε)/ε) + log(1 - e^{-ε}) → 0` as `ε → 0⁺`. -/
theorem tendsto_log_add_log_one_sub_exp :
    Tendsto (fun ε : ℝ => Real.log ((1 + ε) / ε) + Real.log (1 - Real.exp (-ε)))
      (𝓝[>] 0) (𝓝 0) := by
  have hone : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun ε : ℝ => 1 + ε) (𝓝 0) (𝓝 (1 + 0)) := tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hratio : Tendsto (fun ε : ℝ => (1 - Real.exp (-ε)) / ε) (𝓝[>] 0) (𝓝 1) := by
    have hlo : Tendsto (fun ε : ℝ => 1 / (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).div hone one_ne_zero
      rwa [div_one] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have h := Real.add_one_le_exp ε
      have h3 : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
      rw [div_le_div_iff₀ (by positivity) hε']
      nlinarith [Real.exp_pos (-ε)]
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      rw [div_le_one hε']
      have := Real.add_one_le_exp (-ε)
      linarith
  have hprod := (Real.continuousAt_log (by norm_num : (1 : ℝ) * 1 ≠ 0)).tendsto.comp
    (hone.mul hratio)
  rw [mul_one, Real.log_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hlt : 0 < 1 - Real.exp (-ε) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -ε < 0); linarith
  simp only [Function.comp_apply]
  rw [← Real.log_mul (by positivity) hlt.ne']
  congr 1
  field_simp

/-- `γ = ∫₀^∞ ((1+t)⁻¹ - e^{-t})/t dt`. -/
theorem eulerMascheroni_eq_integral_recip_one_add :
    Real.eulerMascheroniConstant = ∫ t in Ioi (0 : ℝ), (1 / (1 + t) - Real.exp (-t)) / t := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hmono : Monotone fun n => Ioi (ε n) := by
    intro m n hmn
    apply Ioi_subset_Ioi
    simp only [hε]
    gcongr
  have hU : (⋃ n, Ioi (ε n)) = Ioi 0 := by
    ext t
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩; exact (hεpos n).trans hn
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
      exact ⟨n, by simpa [hε] using hn⟩
  set f : ℝ → ℝ := fun t => (1 / (1 + t) - Real.exp (-t)) / t with hf
  set g : ℝ → ℝ := fun t => Real.exp (-1 * t) * binetKernel t with hg
  have hA := tendsto_setIntegral_of_monotone (μ := volume) (f := f)
    (fun n => measurableSet_Ioi) hmono (by rw [hU]; exact integrableOn_eulerIntegrand)
  have hB := tendsto_setIntegral_of_monotone (μ := volume) (f := g)
    (fun n => measurableSet_Ioi) hmono (by rw [hU]; exact integrableOn_exp_mul_binetKernel one_pos)
  rw [hU] at hA hB
  have hdiff : ∀ n, (∫ t in Ioi (ε n), f t) - ∫ t in Ioi (ε n), g t =
      Real.log ((1 + ε n) / ε n) + Real.log (1 - Real.exp (-ε n)) := by
    intro n
    obtain ⟨hi1, hv1⟩ := integral_Ioi_one_div_mul_one_add (hεpos n)
    obtain ⟨hi2, hv2⟩ := integral_Ioi_one_div_exp_sub_one (hεpos n)
    have hfi : IntegrableOn f (Ioi (ε n)) :=
      integrableOn_eulerIntegrand.mono_set (Ioi_subset_Ioi (hεpos n).le)
    have hgi : IntegrableOn g (Ioi (ε n)) :=
      (integrableOn_exp_mul_binetKernel one_pos).mono_set (Ioi_subset_Ioi (hεpos n).le)
    rw [← integral_sub hfi hgi]
    have heq : EqOn (fun t => f t - g t) (fun t => 1 / (t * (1 + t)) - 1 / (Real.exp t - 1))
        (Ioi (ε n)) := by
      intro t ht
      have ht' : 0 < t := (hεpos n).trans ht
      have h1 := (exp_sub_one_pos ht').ne'
      have h2 : 1 - Real.exp (-t) ≠ 0 := by
        have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
      have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
      simp only [hf, hg, binetKernel, neg_mul, one_mul]
      rw [Real.exp_neg t] at h2 ⊢
      have h4 : 1 + t ≠ 0 := by linarith
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hi1 hi2, hv1, hv2]
    ring
  have hε0 : Tendsto ε atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hεpos⟩
  have hlim := (hA.sub hB)
  have hlim' := tendsto_log_add_log_one_sub_exp.comp hε0
  have hzero : (∫ t in Ioi (0 : ℝ), f t) - ∫ t in Ioi (0 : ℝ), g t = 0 :=
    tendsto_nhds_unique (hlim.congr fun n => hdiff n) hlim'
  rw [hg, integral_exp_mul_binetKernel_one] at hzero
  linarith

/-- The substitution `u = eᵗ - 1`:
`∫₀^∞ ((1+u)⁻¹ - (1+u)^{-x})/u du = ∫₀^∞ (e^{-t} - e^{-xt})/(1 - e^{-t}) dt`. -/
theorem integral_rpow_sub_rpow_div_eq {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => (1 / (1 + u) - (1 + u) ^ (-x)) / u) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), (1 / (1 + u) - (1 + u) ^ (-x)) / u =
        ∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) := by
  set f : ℝ → ℝ := fun t => Real.exp t - 1 with hf
  set g : ℝ → ℝ := fun u => (1 / (1 + u) - (1 + u) ^ (-x)) / u with hg
  have hf' : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt f (Real.exp t) (Ioi 0) t := fun t _ =>
    ((Real.hasDerivAt_exp t).sub_const 1).hasDerivWithinAt
  have hinj : InjOn f (Ioi 0) := fun a _ b _ h => Real.exp_injective (by simpa [hf] using h)
  have himg : f '' Ioi 0 = Ioi 0 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact exp_sub_one_pos ht
    · intro hu
      have hu' : (0 : ℝ) < u := hu
      refine ⟨Real.log (1 + u), Real.log_pos (by linarith), ?_⟩
      simp [hf, Real.exp_log (by linarith : (0 : ℝ) < 1 + u)]
  have hcomp : EqOn (fun t => |Real.exp t| • g (f t))
      (fun t => (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t))) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 := (exp_sub_one_pos ht').ne'
    have h2 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have hpow : Real.exp t ^ (-x) = Real.exp (-x * t) := by
      rw [← Real.exp_mul]; ring_nf
    simp only [hg, hf, smul_eq_mul, Real.abs_exp, add_sub_cancel, hpow]
    rw [Real.exp_neg t] at h2 ⊢
    field_simp
  have hRint := integrableOn_digamma_add_euler hx
  constructor
  · have := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hf' hinj g).mpr
      (hRint.congr_fun hcomp.symm measurableSet_Ioi)
    rwa [himg] at this
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf' hinj g
    rw [himg] at h
    rw [h]
    exact setIntegral_congr_fun measurableSet_Ioi hcomp

/-- DLMF 5.9.14: `ψ(x) = ∫₀^∞ (e^(-t) - (1 + t)^(-x)) dt/t` for `x > 0`. -/
@[dlmf 5.9.E14]
theorem digamma_frullani {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      ∫ t : ℝ in Set.Ioi 0, (Real.exp (-t) - (1 + t) ^ (-x)) / t := by
  obtain ⟨hint, heq⟩ := integral_rpow_sub_rpow_div_eq hx
  have hψ : Real.digamma x = (Real.digamma x + Real.eulerMascheroniConstant) -
      Real.eulerMascheroniConstant := by ring
  rw [hψ, digamma_add_euler_Ioi hx, ← heq]
  conv_lhs => rw [eulerMascheroni_eq_integral_recip_one_add]
  rw [← integral_sub hint integrableOn_eulerIntegrand]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

end Frullani

open Set in
/-- `t e^(-xt)` is integrable on `(0, ∞)` for `x > 0`. -/
theorem integrableOn_mul_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => t * Real.exp (-x * t)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := x) (by norm_num)
    one_pos hx
  refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

open Set in
/-- `∫₀^∞ t e^(-xt) dt = 1/x²` for `x > 0`. -/
theorem integral_mul_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-x * t) = 1 / x ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := x) two_pos hx
  norm_num at h
  rw [one_div, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [neg_mul]

open Set in
/-- DLMF 5.9.15: `ψ(x) = ln x - 1/(2x) - 2 ∫₀^∞ t dt/((t² + x²)(e^(2πt) - 1))` for `x > 0`. -/
@[dlmf 5.9.E15]
theorem digamma_coth {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      Real.log x - 1 / (2 * x) -
        2 * ∫ t : ℝ in Set.Ioi 0,
          t / ((t ^ 2 + x ^ 2) * (Real.exp (2 * π * t) - 1)) := by
  rw [digamma_eq_log_sub_binetBeta hx]
  congr 1
  have ha : ∀ m : ℕ, 0 < 2 * π * (m + 1) := fun m => by positivity
  set F : ℕ → ℝ → ℝ := fun m t =>
    2 * (Real.exp (-x * t) * (t / (t ^ 2 + (2 * π * (m + 1)) ^ 2))) with hF
  set G : ℕ → ℝ → ℝ := fun m u =>
    2 * (Real.exp (-(2 * π * (m + 1)) * u) * (u / (u ^ 2 + x ^ 2))) with hG
  have hFG : ∀ m, ∫ t in Ioi (0 : ℝ), F m t = ∫ u in Ioi (0 : ℝ), G m u := by
    intro m
    simp only [hF, hG, MeasureTheory.integral_const_mul]
    rw [integral_exp_mul_div_sq_add_sq_symm hx (ha m)]
  -- `0 ≤ e^{-ct} t/(t² + d²) ≤ t e^{-ct}/d²`
  have hle : ∀ c d t : ℝ, 0 < d → 0 < t →
      Real.exp (-c * t) * (t / (t ^ 2 + d ^ 2)) ≤ 1 / d ^ 2 * (t * Real.exp (-c * t)) := by
    intro c d t hd ht
    have := Real.exp_pos (-c * t)
    rw [div_mul_eq_mul_div, one_mul, mul_div_assoc', div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [mul_pos (mul_pos this ht) (pow_pos ht 2)]
  have hint_gen : ∀ c d : ℝ, 0 < c → 0 < d → IntegrableOn
      (fun t => 2 * (Real.exp (-c * t) * (t / (t ^ 2 + d ^ 2)))) (Ioi 0) := by
    intro c d hc hd
    refine Integrable.mono' (((integrableOn_mul_exp_neg_mul hc).const_mul (1 / d ^ 2)).const_mul 2)
      ?_ ?_
    · exact (Continuous.mul continuous_const (Continuous.mul (by fun_prop)
        (Continuous.div continuous_id (by fun_prop) fun t => by positivity))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht' : (0 : ℝ) < t := ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hle c d t hd ht') zero_le_two
  have hintF : ∀ m, Integrable (F m) (volume.restrict (Ioi (0 : ℝ))) := fun m =>
    hint_gen x _ hx (ha m)
  have hintG : ∀ m, Integrable (G m) (volume.restrict (Ioi (0 : ℝ))) := fun m =>
    hint_gen _ x (ha m) hx
  have hnormF : ∀ m, ∫ t in Ioi (0 : ℝ), ‖F m t‖ = ∫ t in Ioi (0 : ℝ), F m t := fun m =>
    setIntegral_congr_fun measurableSet_Ioi fun t ht => Real.norm_of_nonneg (by
      have : (0 : ℝ) < t := ht; positivity)
  have hnormG : ∀ m, ∫ u in Ioi (0 : ℝ), ‖G m u‖ = ∫ u in Ioi (0 : ℝ), G m u := fun m =>
    setIntegral_congr_fun measurableSet_Ioi fun u hu => Real.norm_of_nonneg (by
      have : (0 : ℝ) < u := hu; positivity)
  have hboundG : ∀ m, ∫ u in Ioi (0 : ℝ), G m u ≤ 2 * (1 / ((2 * π * (m + 1)) ^ 2 * x ^ 2)) := by
    intro m
    have h := setIntegral_mono_on (hintG m)
      (((integrableOn_mul_exp_neg_mul (ha m)).const_mul (1 / x ^ 2)).const_mul 2)
      measurableSet_Ioi fun u hu => mul_le_mul_of_nonneg_left
        (hle _ x u hx (by exact hu)) zero_le_two
    simp only [MeasureTheory.integral_const_mul, integral_mul_exp_neg_mul (ha m)] at h
    refine h.trans (le_of_eq ?_)
    field_simp
  have hsumG : Summable fun m => ∫ u in Ioi (0 : ℝ), ‖G m u‖ := by
    simp_rw [hnormG]
    exact Summable.of_nonneg_of_le (fun m => setIntegral_nonneg measurableSet_Ioi fun u hu => by
      have : (0 : ℝ) < u := hu; positivity) hboundG
      ((summable_recip_sq_two_pi (x := x ^ 2)).mul_left 2)
  have hsumF : Summable fun m => ∫ t in Ioi (0 : ℝ), ‖F m t‖ :=
    hsumG.congr fun m => by rw [hnormG m, hnormF m, hFG m]
  have keyF := integral_tsum_of_summable_integral_norm hintF hsumF
  have keyG := integral_tsum_of_summable_integral_norm hintG hsumG
  have h1 : ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetBeta t =
      ∫ t in Ioi (0 : ℝ), ∑' m, F m t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    rw [← ((hasSum_binetBeta ht').mul_left (Real.exp (-x * t))).tsum_eq]
    congr 1
    funext m
    simp only [hF]
    ring
  have h2 : 2 * ∫ t in Ioi (0 : ℝ), t / ((t ^ 2 + x ^ 2) * (Real.exp (2 * π * t) - 1)) =
      ∫ u in Ioi (0 : ℝ), ∑' m, G m u := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    have hs := (hasSum_recip_exp_two_pi_sub_one hu').mul_left (2 * (u / (u ^ 2 + x ^ 2)))
    have hG' : (fun m => G m u) = fun m : ℕ =>
        2 * (u / (u ^ 2 + x ^ 2)) * Real.exp (-(2 * π * (m + 1)) * u) := by
      funext m; simp only [hG]; ring
    rw [hG', hs.tsum_eq]
    have := (exp_sub_one_pos (by positivity : 0 < 2 * π * u)).ne'
    field_simp
  rw [h1, h2, ← keyF, ← keyG]
  simp_rw [hFG]

/-- DLMF 5.9.16: `ψ(x) + γ = ∫₀^∞ (e^(-t) - e^(-xt))/(1 - e^(-t)) dt = ∫₀¹ (1 - t^(x-1))/(1 - t) dt`
for `x > 0`. -/
@[dlmf 5.9.E16]
theorem digamma_add_euler {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t : ℝ in Set.Ioi 0,
        (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) ∧
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t : ℝ in (0 : ℝ)..1, (1 - t ^ (x - 1)) / (1 - t) := by
  refine ⟨digamma_add_euler_Ioi hx, ?_⟩
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  exact digamma_add_euler_Ioo hx

/-- DLMF 5.9.18: `γ = -∫₀^∞ e^(-t) ln t dt = ∫₀^∞ (1/(1 + t) - e^(-t)) dt/t`. -/
@[dlmf 5.9.E18]
theorem eulerMascheroni_integrals :
    Real.eulerMascheroniConstant =
      -∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * Real.log t ∧
    Real.eulerMascheroniConstant =
      ∫ t : ℝ in Set.Ioi 0, (1 / (1 + t) - Real.exp (-t)) / t := by
  refine ⟨?_, eulerMascheroni_eq_integral_recip_one_add⟩
  rw [Real.eulerMascheroniConstant_eq_neg_integral_log]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _

section LogMoments

/-! ### Derivatives and integrals of `Γ` in the order (DLMF 5.9.19–20)

Both formulas differentiate Euler's integral under the integral sign. The integrands are
dominated using `|log t|^k ≤ (t^{kε} + t^{-kε})/εᵏ` and the convergence of Euler's integral. -/

open Set

/-- `|log t|^k ≤ (t^{kε} + t^{-kε})/εᵏ` for `t, ε > 0`. -/
theorem abs_log_pow_le {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (k : ℕ) :
    |Real.log t| ^ k ≤ (t ^ (k * ε) + t ^ (-(k * ε))) / ε ^ k := by
  have hpow : ∀ a : ℝ, (t ^ a / ε) ^ k = t ^ (k * a) / ε ^ k := fun a => by
    rw [div_pow, ← Real.rpow_natCast (t ^ a), ← Real.rpow_mul ht.le, mul_comm]
  rcases le_or_gt 1 t with h1 | h1
  · have hl : 0 ≤ Real.log t := Real.log_nonneg h1
    rw [abs_of_nonneg hl]
    calc Real.log t ^ k ≤ (t ^ ε / ε) ^ k := pow_le_pow_left₀ hl (Real.log_le_rpow_div ht.le hε) k
      _ = t ^ (k * ε) / ε ^ k := hpow ε
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right (by positivity)
  · have hl : Real.log t < 0 := Real.log_neg ht h1
    have hle := Real.log_le_rpow_div (inv_pos.mpr ht).le hε
    rw [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at hle
    rw [abs_of_neg hl]
    calc (-Real.log t) ^ k ≤ (t ^ (-ε) / ε) ^ k := pow_le_pow_left₀ (by linarith) hle k
      _ = t ^ (-(k * ε)) / ε ^ k := by rw [hpow (-ε)]; ring_nf
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left (by positivity)

/-- `|log t|^k e^(-t) t^(s-1)` is continuous on `(0, ∞)`. -/
theorem continuousOn_abs_log_pow_mul_Gamma (k : ℕ) (s : ℝ) :
    ContinuousOn (fun t => |Real.log t| ^ k * Real.exp (-t) * t ^ (s - 1)) (Ioi 0) := by
  intro t ht
  have ht' : t ≠ 0 := (ne_of_gt ht)
  exact (((continuous_abs.continuousAt.comp (Real.continuousAt_log ht')).pow k).mul
    (Real.continuous_exp.comp continuous_neg).continuousAt).mul
    (Real.continuousAt_rpow_const t (s - 1) (Or.inl ht')) |>.continuousWithinAt

/-- `(log t)^k e^(-t) t^(s-1)` is continuous on `(0, ∞)`. -/
theorem continuousOn_log_pow_mul_Gamma (k : ℕ) (s : ℝ) :
    ContinuousOn (fun t => Real.log t ^ k * Real.exp (-t) * t ^ (s - 1)) (Ioi 0) := by
  intro t ht
  have ht' : t ≠ 0 := (ne_of_gt ht)
  exact (((Real.continuousAt_log ht').pow k).mul
    (Real.continuous_exp.comp continuous_neg).continuousAt).mul
    (Real.continuousAt_rpow_const t (s - 1) (Or.inl ht')) |>.continuousWithinAt

/-- Integrability of `|log t|ᵏ e^{-t} t^{s-1}` on `(0, ∞)` for `s > 0`. -/
theorem integrableOn_abs_log_pow_mul_Gamma {s : ℝ} (hs : 0 < s) (k : ℕ) :
    IntegrableOn (fun t => |Real.log t| ^ k * Real.exp (-t) * t ^ (s - 1)) (Ioi 0) := by
  set ε := s / (2 * (k + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hkε : k * ε < s := by
    have h : (k : ℝ) * ε = s * (k / (2 * (k + 1))) := by rw [hε]; ring
    have h' : (k : ℝ) / (2 * (k + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    rw [h]; nlinarith
  have hkε0 : 0 ≤ (k : ℝ) * ε := by positivity
  have h1 := Real.GammaIntegral_convergent (by linarith : 0 < s + k * ε)
  have h2 := Real.GammaIntegral_convergent (by linarith : 0 < s - k * ε)
  refine Integrable.mono' ((h1.add h2).div_const (ε ^ k))
    ((continuousOn_abs_log_pow_mul_Gamma k s).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht' : (0 : ℝ) < t := ht
  rw [Real.norm_of_nonneg (by positivity)]
  have hb := abs_log_pow_le ht' hε0 k
  have he1 : t ^ (s + k * ε - 1) = t ^ (k * ε) * t ^ (s - 1) := by
    rw [← Real.rpow_add ht']; ring_nf
  have he2 : t ^ (s - k * ε - 1) = t ^ (-(k * ε)) * t ^ (s - 1) := by
    rw [← Real.rpow_add ht']; ring_nf
  simp only [Pi.add_apply, he1, he2]
  have hp : 0 ≤ Real.exp (-t) * t ^ (s - 1) := by positivity
  calc |Real.log t| ^ k * Real.exp (-t) * t ^ (s - 1)
      = |Real.log t| ^ k * (Real.exp (-t) * t ^ (s - 1)) := by ring
    _ ≤ (t ^ (k * ε) + t ^ (-(k * ε))) / ε ^ k * (Real.exp (-t) * t ^ (s - 1)) :=
        mul_le_mul_of_nonneg_right hb hp
    _ = _ := by ring

/-- `(log t)^k e^(-t) t^(s-1)` is integrable on `(0, ∞)` for `s > 0`. -/
theorem integrableOn_log_pow_mul_Gamma {s : ℝ} (hs : 0 < s) (k : ℕ) :
    IntegrableOn (fun t => Real.log t ^ k * Real.exp (-t) * t ^ (s - 1)) (Ioi 0) := by
  refine (integrableOn_abs_log_pow_mul_Gamma hs k).mono'
    ((continuousOn_log_pow_mul_Gamma k s).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht' : (0 : ℝ) < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Real.abs_exp,
    abs_of_pos (Real.rpow_pos_of_pos ht' _)]

/-- `t^{y-1} ≤ t^{a-1} + t^{b-1}` for `t > 0` and `a ≤ y ≤ b`. -/
theorem rpow_le_rpow_add_rpow {t a b y : ℝ} (ht : 0 < t) (hay : a ≤ y) (hyb : y ≤ b) :
    t ^ (y - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
  rcases le_or_gt 1 t with h1 | h1
  · have := Real.rpow_le_rpow_of_exponent_le h1 (by linarith : y - 1 ≤ b - 1)
    have := Real.rpow_pos_of_pos ht (a - 1)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ht h1.le (by linarith : a - 1 ≤ y - 1)
    have := Real.rpow_pos_of_pos ht (b - 1)
    linarith

/-- `y ↦ t^(y-1)` has derivative `t^(y-1) log t` for `t > 0`. -/
theorem hasDerivAt_rpow_sub_one {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun y => t ^ (y - 1)) (t ^ (y - 1) * Real.log t) y := by
  have h := (Real.hasStrictDerivAt_const_rpow ht (y - 1)).hasDerivAt.comp y
    ((hasDerivAt_id y).sub_const 1)
  simp only [id_eq, mul_one, Function.comp_def] at h
  exact h

/-- `Iₙ(x) = ∫₀^∞ (log t)ⁿ e^{-t} t^{x-1} dt`. -/
def gammaLogMoment (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.log t ^ n * Real.exp (-t) * t ^ (x - 1)

/-- The log-moments `∫₀^∞ (log t)ⁿ e^(-t) t^(x-1) dt` satisfy `d/dx Mₙ(x) = M_{n+1}(x)` for `x > 0`.
-/
theorem hasDerivAt_gammaLogMoment (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gammaLogMoment n) (gammaLogMoment (n + 1) x) x := by
  have hball : Metric.ball x (x / 2) ∈ 𝓝 x := Metric.ball_mem_nhds _ (by positivity)
  have hy : ∀ y ∈ Metric.ball x (x / 2), x / 2 ≤ y ∧ y ≤ 2 * x := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    constructor <;> linarith [hy.1, hy.2]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun y t => Real.log t ^ n * Real.exp (-t) * t ^ (y - 1))
    (F' := fun y t => Real.log t ^ (n + 1) * Real.exp (-t) * t ^ (y - 1))
    (bound := fun t => |Real.log t| ^ (n + 1) * Real.exp (-t) * t ^ (x / 2 - 1) +
      |Real.log t| ^ (n + 1) * Real.exp (-t) * t ^ (2 * x - 1))
    hball (Eventually.of_forall fun y =>
      (continuousOn_log_pow_mul_Gamma n y).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_log_pow_mul_Gamma hx n)
    (integrableOn_log_pow_mul_Gamma hx (n + 1)).aestronglyMeasurable ?_
    ((integrableOn_abs_log_pow_mul_Gamma (by positivity) _).add
      (integrableOn_abs_log_pow_mul_Gamma (by positivity) _)) ?_
  · exact h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y hy'
    have ht' : (0 : ℝ) < t := ht
    obtain ⟨hy1, hy2⟩ := hy y hy'
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Real.abs_exp,
      abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    have hA : 0 ≤ |Real.log t| ^ (n + 1) * Real.exp (-t) := by positivity
    calc |Real.log t| ^ (n + 1) * Real.exp (-t) * t ^ (y - 1)
        ≤ |Real.log t| ^ (n + 1) * Real.exp (-t) * (t ^ (x / 2 - 1) + t ^ (2 * x - 1)) :=
          mul_le_mul_of_nonneg_left (rpow_le_rpow_add_rpow ht' hy1 hy2) hA
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y _
    have ht' : (0 : ℝ) < t := ht
    have := (hasDerivAt_rpow_sub_one ht' y).const_mul (Real.log t ^ n * Real.exp (-t))
    exact this.congr_deriv (by deriv_simp)

/-- DLMF 5.9.19: `Γ^(n)(x) = ∫₀^∞ (ln t)ⁿ e^(-t) t^(x-1) dt` for `x > 0`. -/
@[dlmf 5.9.E19]
theorem iteratedDeriv_Gamma {n : ℕ} {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n Real.Gamma x =
      ∫ t : ℝ in Set.Ioi 0, (Real.log t) ^ n * Real.exp (-t) * t ^ (x - 1) := by
  induction n generalizing x with
  | zero =>
    rw [iteratedDeriv_zero, Real.Gamma_eq_integral hx]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n Real.Gamma =ᶠ[𝓝 x] gammaLogMoment n := by
      filter_upwards [Ioi_mem_nhds hx] with y hy using ih hy
    rw [heq.deriv_eq, (hasDerivAt_gammaLogMoment n hx).deriv]
    rfl

/-- `|(t^{a-1} - t^{b-1})/log t| ≤ |a - b| (t^{m-1} + t^{M-1})` with `m = min a b`,
`M = max a b`, by the mean value theorem in the exponent. -/
theorem abs_rpow_sub_rpow_div_log_le {t a b : ℝ} (ht : 0 < t) :
    |(t ^ (a - 1) - t ^ (b - 1)) / Real.log t| ≤
      |a - b| * (t ^ (min a b - 1) + t ^ (max a b - 1)) := by
  rcases eq_or_ne t 1 with rfl | ht1
  · simp
  have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht ht1
  have key : ∀ a b : ℝ, a < b → ∃ c ∈ Ioo a b,
      (t ^ (b - 1) - t ^ (a - 1)) / Real.log t = (b - a) * t ^ (c - 1) := by
    intro a b hab
    obtain ⟨c, hc, hd⟩ := exists_hasDerivAt_eq_slope (fun y => t ^ (y - 1))
      (fun y => t ^ (y - 1) * Real.log t) hab
      (fun y _ => (hasDerivAt_rpow_sub_one ht y).continuousAt.continuousWithinAt)
      (fun y _ => hasDerivAt_rpow_sub_one ht y)
    refine ⟨c, hc, ?_⟩
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    rw [eq_div_iff hba] at hd
    field_simp
    linarith
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨c, hc, hv⟩ := key a b hab
    rw [show (t ^ (a - 1) - t ^ (b - 1)) / Real.log t =
      -((t ^ (b - 1) - t ^ (a - 1)) / Real.log t) by ring, hv, min_eq_left hab.le,
      max_eq_right hab.le, abs_neg, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _),
      abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_add_rpow ht hc.1.le hc.2.le) (abs_nonneg _)
  · simp
  · obtain ⟨c, hc, hv⟩ := key b a hab
    rw [hv, min_eq_right hab.le, max_eq_left hab.le, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos ht _), abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_add_rpow ht hc.1.le hc.2.le) (abs_nonneg _)

/-- `(t^(a-1) - t^(b-1)) e^(-t)/log t` is continuous on `(0, ∞) \ {1}`. -/
theorem continuousOn_rpow_sub_rpow_div_log (a b : ℝ) :
    ContinuousOn (fun t => (t ^ (a - 1) - t ^ (b - 1)) / Real.log t * Real.exp (-t))
      (Ioi 0 \ {1}) := by
  intro t ht
  have ht0 : t ≠ 0 := (ne_of_gt ht.1)
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one ht.1 ht.2
  exact ((((Real.continuousAt_rpow_const t (a - 1) (Or.inl ht0)).sub
    (Real.continuousAt_rpow_const t (b - 1) (Or.inl ht0))).div (Real.continuousAt_log ht0)
    hlog).mul (Real.continuous_exp.comp continuous_neg).continuousAt).continuousWithinAt

/-- `(t^(a-1) - t^(b-1)) e^(-t)/log t` is integrable on `(0, ∞)` for `a, b > 0`. -/
theorem integrableOn_rpow_sub_rpow_div_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t => (t ^ (a - 1) - t ^ (b - 1)) / Real.log t * Real.exp (-t)) (Ioi 0) := by
  have hm : 0 < min a b := lt_min ha hb
  have hM : 0 < max a b := lt_max_of_lt_left ha
  have hdom := ((Real.GammaIntegral_convergent hm).add
    (Real.GammaIntegral_convergent hM)).const_mul |a - b|
  have hdiff : Ioi (0 : ℝ) =ᵐ[volume] (Ioi 0 \ {1} : Set ℝ) :=
    (sdiff_null_ae_eq_self (measure_singleton 1)).symm
  rw [IntegrableOn, Measure.restrict_congr_set hdiff]
  refine Integrable.mono' (hdom.mono_measure (Measure.restrict_mono sdiff_subset le_rfl))
    ((continuousOn_rpow_sub_rpow_div_log a b).aestronglyMeasurable
      (measurableSet_Ioi.diff (measurableSet_singleton 1))) ?_
  refine (ae_restrict_iff' (measurableSet_Ioi.diff (measurableSet_singleton 1))).mpr
    (Eventually.of_forall fun t ht => ?_)
  have ht' : (0 : ℝ) < t := ht.1
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  have := abs_rpow_sub_rpow_div_log_le (a := a) (b := b) ht'
  simp only [Pi.add_apply]
  calc |(t ^ (a - 1) - t ^ (b - 1)) / Real.log t| * Real.exp (-t)
      ≤ |a - b| * (t ^ (min a b - 1) + t ^ (max a b - 1)) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    _ = _ := by ring

/-- DLMF 5.9.20: `∫_c^x Γ(t) dt = ∫₀^∞ (t^(x-1) - t^(c-1)) e^(-t)/ln t dt` for `c, x > 0`. -/
@[dlmf 5.9.E20]
theorem integral_Gamma {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ∫ t : ℝ in c..x, Real.Gamma t =
      ∫ t : ℝ in Set.Ioi 0,
        (t ^ (x - 1) - t ^ (c - 1)) / Real.log t * Real.exp (-t) := by
  set H : ℝ → ℝ := fun y =>
    ∫ t in Ioi (0 : ℝ), (t ^ (y - 1) - t ^ (c - 1)) / Real.log t * Real.exp (-t) with hH
  have hderiv : ∀ y, 0 < y → HasDerivAt H (Real.Gamma y) y := by
    intro y hy
    have hball : Metric.ball y (y / 2) ∈ 𝓝 y := Metric.ball_mem_nhds _ (by positivity)
    have hy' : ∀ z ∈ Metric.ball y (y / 2), y / 2 ≤ z ∧ z ≤ 2 * y := by
      intro z hz
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hz
      constructor <;> linarith [hz.1, hz.2]
    have hpos : ∀ z ∈ Metric.ball y (y / 2), 0 < z := fun z hz => by
      linarith [(hy' z hz).1]
    have hne1 : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), t ≠ 1 :=
      ae_restrict_of_ae (Measure.ae_ne volume 1)
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun z t => (t ^ (z - 1) - t ^ (c - 1)) / Real.log t * Real.exp (-t))
      (F' := fun z t => Real.exp (-t) * t ^ (z - 1))
      (bound := fun t => Real.exp (-t) * t ^ (y / 2 - 1) + Real.exp (-t) * t ^ (2 * y - 1))
      hball ?_ (integrableOn_rpow_sub_rpow_div_log hy hc)
      (Real.GammaIntegral_convergent hy).aestronglyMeasurable ?_
      ((Real.GammaIntegral_convergent (by positivity)).add
        (Real.GammaIntegral_convergent (by positivity))) ?_
    · rw [Real.Gamma_eq_integral hy]
      exact h.2
    · filter_upwards [hball] with z hz
      exact (integrableOn_rpow_sub_rpow_div_log (hpos z hz) hc).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht' : (0 : ℝ) < t := ht
      obtain ⟨hz1, hz2⟩ := hy' z hz
      rw [Real.norm_of_nonneg (by positivity)]
      have := rpow_le_rpow_add_rpow ht' hz1 hz2
      have he := Real.exp_pos (-t)
      nlinarith
    · filter_upwards [ae_restrict_mem measurableSet_Ioi, hne1] with t ht ht1 z _
      have ht' : (0 : ℝ) < t := ht
      have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht' ht1
      have := (((hasDerivAt_rpow_sub_one ht' z).sub_const (t ^ (c - 1))).div_const
        (Real.log t)).mul_const (Real.exp (-t))
      exact this.congr_deriv (by deriv_simp)
  have hpos : ∀ y ∈ uIcc c x, 0 < y := fun y hy => by
    rcases (mem_uIcc.mp hy) with h | h
    · exact hc.trans_le h.1
    · exact hx.trans_le h.1
  have hcont : ContinuousOn Real.Gamma (uIcc c x) := fun y hy =>
    (Real.differentiableAt_Gamma fun m =>
      (lt_of_le_of_lt (neg_nonpos.mpr m.cast_nonneg) (hpos y hy)).ne').continuousAt
      |>.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hderiv y (hpos y hy))
    (hcont.intervalIntegrable)]
  have hHc : H c = 0 := by simp [hH]
  rw [hHc, sub_zero]

end LogMoments

end DLMF.Gamma

end
end
