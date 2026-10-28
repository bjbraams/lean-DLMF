/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ExpIntegrals.Asymptotics
public import DLMF.ExpIntegrals.Representations

/-!
# Laplace and Fourier tools for exponential integrals

Transform kernels, integrability and analytic continuation used in exponential-integral
identities.

Source references and common attribution are retained in
`DLMF.ExpIntegrals.TransformTools`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

/-- Complex Laplace transform of `1`: `∫₀^∞ e^{-ct} dt = 1/c` for `Re c > 0`. -/
theorem eiTr_integral_exp_neg {c : ℂ} (hc : 0 < c.re) :
    ∫ t : ℝ in Ioi 0, cexp (-c * t) = 1 / c := by
  have := integral_exp_mul_complex_Ioi (a := -c) (by simpa using hc) 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero] at this
  rw [this]; field_simp

/-- `t ↦ e^{-ct}` is integrable on `(0, ∞)` for `Re c > 0`. -/
theorem eiTr_integrableOn_exp_neg {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (fun t : ℝ => cexp (-c * t)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using hc) 0

/-- Real form: `∫₀^∞ e^{-ct} dt = 1/c` for `c > 0`. -/
theorem eiTr_real_integral_exp_neg {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ in Ioi 0, Real.exp (-(c * t)) = 1 / c := by
  have := integral_exp_mul_Ioi (a := -c) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at this
  rw [this]; field_simp

/-- `E₁(t) = ∫₁^∞ e^{-tu}/u du`. -/
theorem eiTr_E1_eq {t : ℝ} (ht : 0 < t) :
    genExpIntE 1 t = ∫ u in Ioi (1 : ℝ), ((Real.exp (-(t * u)) / u : ℝ) : ℂ) := by
  rw [genExpIntE_eq_integral 1 ht]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0:ℝ) < u := lt_trans one_pos hu
  simp only [Complex.cpow_neg_one, Complex.real_smul]
  push_cast; ring_nf

/-- the lower bound on `Re a + u`. -/
theorem eiTr_re_add_ge {a : ℂ} {u : ℝ} (hu : 1 ≤ u) :
    min 1 (1 + a.re) * u ≤ a.re + u := by
  rcases le_or_gt 0 a.re with h | h
  · nlinarith [min_le_left 1 (1 + a.re)]
  · nlinarith [min_le_right 1 (1 + a.re)]

/-- Integrability of the kernel `e^{-at} e^{-tu}/u` on `(0,∞) × (1,∞)` for `Re a > -1`. -/
theorem eiTr_integrable_E1_kernel {a : ℂ} (ha : -1 < a.re) :
    Integrable (Function.uncurry fun (t u : ℝ) =>
      cexp (-a * t) * ((Real.exp (-(t * u)) / u : ℝ) : ℂ))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (1:ℝ)))) := by
  set δ := min 1 (1 + a.re)
  have hδ : 0 < δ := lt_min one_pos (by linarith)
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (t u : ℝ) =>
      cexp (-a * t) * ((Real.exp (-(t * u)) / u : ℝ) : ℂ))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (1:ℝ)))) := by
    apply Measurable.aestronglyMeasurable
    unfold Function.uncurry
    fun_prop
  refine (integrable_prod_iff' hmeas).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1:ℝ) < u := hu
    have hc : 0 < (a + u).re := by simp; linarith
    refine IntegrableOn.congr_fun ((eiTr_integrableOn_exp_neg hc).const_mul ((u:ℂ)⁻¹))
      (fun t _ => ?_) measurableSet_Ioi
    simp only [Function.uncurry_apply_pair]
    push_cast
    rw [show -(a + u) * (t:ℂ) = -a * t + -(t * u) by ring, Complex.exp_add]
    ring
  · have hint : IntegrableOn (fun u : ℝ => (δ * u ^ 2)⁻¹) (Ioi 1) := by
      have := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul δ⁻¹
      refine IntegrableOn.congr_fun this (fun u hu => ?_) measurableSet_Ioi
      have hu0 : (0:ℝ) < u := lt_trans one_pos hu
      rw [Real.rpow_neg hu0.le, show (2:ℝ) = (2:ℕ) by norm_num, Real.rpow_natCast, mul_inv]
    refine hint.mono' ?_ ?_
    · exact hmeas.norm.prod_swap.integral_prod_right'
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu1 : (1:ℝ) < u := hu
      have hu0 : (0:ℝ) < u := lt_trans one_pos hu
      have hc : 0 < a.re + u := by nlinarith [eiTr_re_add_ge (a := a) hu1.le]
      have heq : ∫ t in Ioi (0:ℝ), ‖Function.uncurry (fun (t u : ℝ) =>
          cexp (-a * t) * ((Real.exp (-(t * u)) / u : ℝ) : ℂ)) (t, u)‖ =
          ∫ t in Ioi (0:ℝ), u⁻¹ * Real.exp (-((a.re + u) * t)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_exp, Complex.norm_real,
          Real.norm_eq_abs]
        rw [abs_of_pos (by positivity), show (-a * (t:ℂ)).re = -(a.re * t) by simp,
          show -((a.re + u) * t) = -(a.re * t) + -(t * u) by ring, Real.exp_add]
        field_simp
      rw [heq, integral_const_mul, eiTr_real_integral_exp_neg hc, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      have := eiTr_re_add_ge (a := a) hu1.le
      rw [one_div, ← mul_inv]
      exact inv_anti₀ (by positivity) (by nlinarith)

/-- `u ↦ 1/((a+u)u)` is integrable on `(1, ∞)` for `Re a > -1`. -/
theorem eiTr_integrableOn_recip_mul {a : ℂ} (ha : -1 < a.re) :
    IntegrableOn (fun u : ℝ => 1 / ((a + u) * u)) (Ioi 1) := by
  set δ := min 1 (1 + a.re)
  have hδ : 0 < δ := lt_min one_pos (by linarith)
  have hint : IntegrableOn (fun u : ℝ => (δ * u ^ 2)⁻¹) (Ioi 1) := by
    have := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul δ⁻¹
    refine IntegrableOn.congr_fun this (fun u hu => ?_) measurableSet_Ioi
    have hu0 : (0:ℝ) < u := lt_trans one_pos hu
    rw [Real.rpow_neg hu0.le, show (2:ℝ) = (2:ℕ) by norm_num, Real.rpow_natCast, mul_inv]
  refine hint.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : (1:ℝ) < u := hu
  have hu0 : (0:ℝ) < u := lt_trans one_pos hu
  have := eiTr_re_add_ge (a := a) hu1.le
  have hre : a.re + u ≤ ‖a + u‖ := by
    have := Complex.re_le_norm (a + u); simpa using this
  rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0, one_div]
  refine inv_anti₀ (by positivity) ?_
  nlinarith

/-- `∫₁^∞ du/((a+u)u) = log(1+a)/a` (and `1` at `a = 0`) for `Re a > -1`. -/
theorem eiTr_integral_recip_mul {a : ℂ} (ha : -1 < a.re) :
    ∫ u in Ioi (1:ℝ), 1 / ((a + u) * u) = if a = 0 then 1 else log (1 + a) / a := by
  split_ifs with h0
  · subst h0
    have hd : ∀ x ∈ Ioi (1:ℝ), HasDerivAt (fun u : ℝ => -((u:ℂ))⁻¹) (1 / ((0 + x) * x)) x := by
      intro x hx
      have hx0 : (x:ℂ) ≠ 0 := by
        have : (0:ℝ) < x := lt_trans one_pos hx
        exact_mod_cast this.ne'
      exact (hasDerivAt_inv hx0).comp_ofReal.neg.congr_deriv (by rw [zero_add]; field_simp)
    have hl : Tendsto (fun u : ℝ => -((u:ℂ))⁻¹) atTop (𝓝 0) := by
      have : Tendsto (fun u : ℝ => ((u⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0:ℝ):ℂ)) :=
        (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
      simpa using this.neg
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (by fun_prop (disch := norm_num)) hd
      (by simpa using eiTr_integrableOn_recip_mul (a := 0) (by simp)) hl]
    simp
  · have hslit : ∀ x : ℝ, 1 ≤ x → a + x ∈ slitPlane := by
      intro x hx
      left; simp; nlinarith [eiTr_re_add_ge (a := a) hx, min_le_left 1 (1 + a.re),
        lt_min (one_pos (α := ℝ)) (show (0:ℝ) < 1 + a.re by linarith)]
    have hd : ∀ x ∈ Ioi (1:ℝ), HasDerivAt (fun u : ℝ => (log u - log (a + u)) / a)
        (1 / ((a + x) * x)) x := by
      intro x hx
      have hx1 : (1:ℝ) < x := hx
      have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast (lt_trans one_pos hx1).ne'
      have hax : a + x ≠ 0 := slitPlane_ne_zero (hslit x hx1.le)
      have h1 := (ofRealCLM.hasDerivAt (x := x)).clog_real
        (by simpa using ofReal_mem_slitPlane.2 (by linarith : (0:ℝ) < x))
      have h2 := ((ofRealCLM.hasDerivAt (x := x)).const_add a).clog_real (hslit x hx1.le)
      simp only [ofRealCLM_apply] at h1 h2
      convert (h1.sub h2).div_const a using 1
      push_cast
      field_simp
      ring
    have hl : Tendsto (fun u : ℝ => (log u - log (a + u)) / a) atTop (𝓝 0) := by
      have h1 : Tendsto (fun u : ℝ => 1 + a * ((u⁻¹ : ℝ) : ℂ)) atTop (𝓝 (1 + a * ((0:ℝ):ℂ))) :=
        tendsto_const_nhds.add (((continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero).const_mul a)
      simp only [ofReal_zero, mul_zero, add_zero] at h1
      have h2 := ((continuousAt_clog (by simp : (1:ℂ) ∈ slitPlane)).tendsto.comp h1).neg.div_const a
      simp only [log_one, neg_zero, zero_div] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with u hu
      have hu0 : (0:ℝ) < u := lt_trans one_pos hu
      have hu0' : (u:ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
      have hne : (1 + a * ((u⁻¹ : ℝ) : ℂ)) ≠ 0 := by
        have : a + u = (u:ℂ) * (1 + a * ((u⁻¹ : ℝ) : ℂ)) := by
          push_cast; field_simp; ring
        intro h; rw [h, mul_zero] at this; exact slitPlane_ne_zero (hslit u hu.le) this
      have : log (a + u) = Real.log u + log (1 + a * ((u⁻¹ : ℝ) : ℂ)) := by
        rw [← log_ofReal_mul hu0 hne]; congr 1; push_cast; field_simp; ring
      simp only [Function.comp_apply, this, ← ofReal_log hu0.le]
      ring
    rw [integral_Ioi_of_hasDerivAt_of_tendsto ?_ hd (eiTr_integrableOn_recip_mul ha) hl]
    · simp [add_comm]; ring
    · have hc : ContinuousAt (fun u : ℝ => (log u - log (a + u)) / a) 1 := by
        refine ContinuousAt.div_const (ContinuousAt.sub ?_ ?_) a
        · exact (continuousAt_clog (by simp)).comp continuous_ofReal.continuousAt
        · exact (continuousAt_clog (by simpa using hslit 1 le_rfl)).comp
            (continuous_const.add continuous_ofReal).continuousAt
      exact hc.continuousWithinAt

/-- Fubini swap of a Laplace transform with an inner integral over `[0,1]` whose integrand grows
  at most quadratically in `t`. -/
theorem eiTr_swap01 {a : ℂ} (ha : 0 < a.re) {F : ℝ → ℝ → ℂ}
    (hF : Measurable (Function.uncurry F)) {C : ℝ}
    (hb : ∀ t u : ℝ, 0 < t → u ∈ Ioc (0:ℝ) 1 → ‖F t u‖ ≤ C * (1 + t ^ 2)) :
    ∫ t in Ioi (0:ℝ), cexp (-a * t) * ∫ u in (0:ℝ)..1, F t u =
      ∫ u in (0:ℝ)..1, ∫ t in Ioi (0:ℝ), cexp (-a * t) * F t u := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
  refine integral_integral_swap ?_
  have hg : Integrable (fun t : ℝ => C * (‖cexp (-a * t) * (t:ℂ) ^ 0‖ +
      ‖cexp (-a * t) * (t:ℂ) ^ 2‖)) (volume.restrict (Ioi 0)) :=
    ((laplace_nat_pow ha 0).1.norm.add (laplace_nat_pow ha 2).1.norm).const_mul C
  have hprod := hg.mul_prod (integrable_const (1:ℝ) : Integrable (fun _ : ℝ => (1:ℝ))
    (volume.restrict (Ioc (0:ℝ) 1)))
  refine hprod.mono' ?_ ?_
  · exact (Measurable.mul (by fun_prop) hF).aestronglyMeasurable
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have ht : (0:ℝ) < p.1 := hp1
    simp only [Function.uncurry, norm_mul, pow_zero, mul_one, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    have := hb p.1 p.2 ht hp2
    have h0 : 0 ≤ ‖cexp (-a * p.1)‖ := norm_nonneg _
    calc ‖cexp (-a * p.1)‖ * ‖F p.1 p.2‖ ≤ ‖cexp (-a * p.1)‖ * (C * (1 + p.1 ^ 2)) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring

/-- `log((1+ia)/(1-ia)) = log(1+ia) - log(1-ia)` for `Re a > 0`. -/
theorem eiTr_log_div {a : ℂ} (ha : 0 < a.re) :
    log ((1 + a * I) / (1 - a * I)) = log (1 + a * I) - log (1 - a * I) := by
  have hz1 : (1 + a * I).im = a.re := by simp
  have hz2 : (1 - a * I).im = -a.re := by simp
  have hne2 : (1 - a * I) ≠ 0 := fun h => by
    have := congrArg Complex.im h; rw [hz2] at this; simp at this; linarith
  have hne1 : (1 + a * I) ≠ 0 := fun h => by
    have := congrArg Complex.im h; rw [hz1] at this; simp at this; linarith
  set q := (1 + a * I) / (1 - a * I) with hq
  have hq0 : q ≠ 0 := div_ne_zero hne1 hne2
  have hqim : 0 < q.im := by
    rw [hq, Complex.div_im]
    have hn : 0 < Complex.normSq (1 - a * I) := Complex.normSq_pos.2 hne2
    have e1 : (1 + a * I).re = 1 - a.im := by simp; ring
    have e2 : (1 - a * I).re = 1 + a.im := by simp
    rw [hz1, hz2, e1, e2, ← sub_div, div_pos_iff]
    left; exact ⟨by nlinarith, hn⟩
  set D := log (1 + a * I) - log (1 - a * I)
  have hexp : exp D = exp (log q) := by
    rw [exp_sub, exp_log hne1, exp_log hne2, exp_log hq0]
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 hexp
  have him := congrArg Complex.im hn
  simp only [D, sub_im, log_im, add_im] at him
  have h1 : 0 ≤ arg (1 + a * I) := arg_nonneg_iff.2 (by rw [hz1]; exact ha.le)
  have h2 : arg (1 - a * I) < 0 := arg_neg_iff.2 (by rw [hz2]; linarith)
  have h3 : 0 ≤ arg q := arg_nonneg_iff.2 hqim.le
  have h4 : arg q < π := arg_lt_pi_iff.2 (Or.inr hqim.ne')
  have h5 := arg_le_pi (1 + a * I)
  have h6 := neg_pi_lt_arg (1 - a * I)
  have hni : ((n : ℂ) * (2 * π * I)).im = 2 * π * n := by simp; ring
  rw [hni] at him
  have hn0 : n = 0 := by
    have hlo : (-1 : ℝ) < 2 * n := by nlinarith [Real.pi_pos]
    have hhi : (2 * n : ℝ) < 2 := by nlinarith [Real.pi_pos]
    have : (-1 : ℤ) < 2 * n := by exact_mod_cast hlo
    have : 2 * n < (2 : ℤ) := by exact_mod_cast hhi
    omega
  rw [hn0] at hn; simp at hn; exact hn.symm

/-- `log(ia) - log(-ia) = iπ` for `Re a > 0`. -/
theorem eiTr_log_I_mul_sub {a : ℂ} (ha : 0 < a.re) :
    log (I * a) - log (-(I * a)) = π * I := by
  have him : 0 < (I * a).im := by simp [ha]
  apply Complex.ext
  · simp [log_re]
  · simp only [sub_im, log_im, arg_neg_eq_arg_sub_pi_of_im_pos him]; simp

/-- `arctan(1/a)`-free form: `∫₀¹ du/(a²+u²) = (π/2 - arctan a)/a` for `Re a > 0`. -/
theorem eiTr_integral_recip_sq_add_sq {a : ℂ} (ha : 0 < a.re) :
    ∫ u in (0:ℝ)..1, 1 / (a ^ 2 + (u:ℂ) ^ 2) = (π / 2 - arctan a) / a := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hm : ∀ u : ℝ, (u:ℂ) - I * a ∈ slitPlane := fun u => by
    right; simp; exact ha.ne'
  have hp : ∀ u : ℝ, (u:ℂ) + I * a ∈ slitPlane := fun u => by
    right; simp; exact ha.ne'
  have hden : ∀ u : ℝ, a ^ 2 + (u:ℂ) ^ 2 ≠ 0 := fun u h => by
    have : ((u:ℂ) - I * a) * ((u:ℂ) + I * a) = 0 := by linear_combination h - a ^ 2 * I_sq
    rcases mul_eq_zero.1 this with h' | h'
    · exact slitPlane_ne_zero (hm u) h'
    · exact slitPlane_ne_zero (hp u) h'
  have hd : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt
      (fun u : ℝ => (log ((u:ℂ) - I * a) - log ((u:ℂ) + I * a)) / (2 * I * a))
      (1 / (a ^ 2 + (x:ℂ) ^ 2)) x := by
    intro x _
    have h1 := ((ofRealCLM.hasDerivAt (x := x)).sub_const (I * a)).clog_real (hm x)
    have h2 := ((ofRealCLM.hasDerivAt (x := x)).add_const (I * a)).clog_real (hp x)
    simp only [ofRealCLM_apply] at h1 h2
    convert (h1.sub h2).div_const (2 * I * a) using 1
    have e1 := slitPlane_ne_zero (hm x)
    have e2 := slitPlane_ne_zero (hp x)
    have e3 := hden x
    have hpr : a ^ 2 + (x:ℂ) ^ 2 = ((x:ℂ) - I * a) * ((x:ℂ) + I * a) := by
      linear_combination a ^ 2 * I_sq
    rw [hpr]
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Continuous.div continuous_const (by fun_prop) hden).intervalIntegrable _ _)]
  have hl := eiTr_log_I_mul_sub ha
  have hd2 := eiTr_log_div ha
  simp only [ofReal_one, ofReal_zero, zero_sub, zero_add]
  rw [arctan, hd2]
  rw [show (1:ℂ) - I * a = 1 - a * I by ring, show (1:ℂ) + I * a = 1 + a * I by ring]
  rw [show I * a = a * I by ring] at hl ⊢
  field_simp
  linear_combination (1:ℂ) * hl + (log (1 - a * I) - log (1 + a * I)) * I_sq

/-- `a² + u² ≠ 0` for `Re a > 0` and real `u`. -/
theorem eiTr_sq_add_sq_ne {a : ℂ} (ha : 0 < a.re) (u : ℝ) : a ^ 2 + (u:ℂ) ^ 2 ≠ 0 := by
  intro h
  have : (a + u * I) * (a - u * I) = 0 := by linear_combination h - (u:ℂ) ^ 2 * I_sq
  rcases mul_eq_zero.1 this with h' | h'
  · have := congrArg Complex.re h'; simp at this; linarith
  · have := congrArg Complex.re h'; simp at this; linarith

/-- Laplace transform of `sin(tu)`: `u/(a²+u²)` for `Re a > 0`. -/
theorem eiTr_laplace_sin {a : ℂ} (ha : 0 < a.re) (u : ℝ) :
    ∫ t in Ioi (0:ℝ), cexp (-a * t) * ((Real.sin (t * u) : ℝ) : ℂ) = u / (a ^ 2 + (u:ℂ) ^ 2) := by
  have h1 : 0 < (a + u * I).re := by simpa using ha
  have h2 : 0 < (a - u * I).re := by simpa using ha
  have he : ∀ t : ℝ, cexp (-a * t) * ((Real.sin (t * u) : ℝ) : ℂ) =
      (I / 2) * (cexp (-(a + u * I) * t) - cexp (-(a - u * I) * t)) := by
    intro t
    rw [ofReal_sin, Complex.sin]
    push_cast
    rw [show -(a + ↑u * I) * ↑t = -a * ↑t + -(↑t * ↑u * I) by ring,
      show -(a - ↑u * I) * ↑t = -a * ↑t + ↑t * ↑u * I by ring, Complex.exp_add, Complex.exp_add]
    ring_nf
  simp_rw [he]
  rw [integral_const_mul, integral_sub (eiTr_integrableOn_exp_neg h1) (eiTr_integrableOn_exp_neg h2),
    eiTr_integral_exp_neg h1, eiTr_integral_exp_neg h2]
  have n1 : a + u * I ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have n2 : a - u * I ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have hpr : a ^ 2 + (u:ℂ) ^ 2 = (a + u * I) * (a - u * I) := by linear_combination (u:ℂ) ^ 2 * I_sq
  rw [hpr, div_sub_div _ _ n1 n2, ← mul_div_assoc]
  congr 1
  linear_combination (-(u:ℂ)) * I_sq

/-- Laplace transform of `cos(tu)`: `a/(a²+u²)` for `Re a > 0`. -/
theorem eiTr_laplace_cos {a : ℂ} (ha : 0 < a.re) (u : ℝ) :
    ∫ t in Ioi (0:ℝ), cexp (-a * t) * ((Real.cos (t * u) : ℝ) : ℂ) = a / (a ^ 2 + (u:ℂ) ^ 2) := by
  have h1 : 0 < (a + u * I).re := by simpa using ha
  have h2 : 0 < (a - u * I).re := by simpa using ha
  have he : ∀ t : ℝ, cexp (-a * t) * ((Real.cos (t * u) : ℝ) : ℂ) =
      (1 / 2) * (cexp (-(a - u * I) * t) + cexp (-(a + u * I) * t)) := by
    intro t
    rw [ofReal_cos, Complex.cos]
    push_cast
    rw [show -(a + ↑u * I) * ↑t = -a * ↑t + -(↑t * ↑u * I) by ring,
      show -(a - ↑u * I) * ↑t = -a * ↑t + ↑t * ↑u * I by ring, Complex.exp_add, Complex.exp_add]
    ring_nf
  simp_rw [he]
  rw [integral_const_mul, integral_add (eiTr_integrableOn_exp_neg h2) (eiTr_integrableOn_exp_neg h1),
    eiTr_integral_exp_neg h1, eiTr_integral_exp_neg h2]
  have n1 : a + u * I ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have n2 : a - u * I ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have hpr : a ^ 2 + (u:ℂ) ^ 2 = (a + u * I) * (a - u * I) := by linear_combination (u:ℂ) ^ 2 * I_sq
  rw [hpr]
  field_simp
  ring

/-- `Si(t) = ∫₀¹ sin(tu)/u du`. -/
theorem eiTr_sinInt_eq (t : ℝ) :
    Real.sinInt t = ∫ u in (0:ℝ)..1, Real.sin (t * u) / u := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [Real.sinInt]
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) Real.sinc ht
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  rw [Real.sinInt, ← mul_inv_cancel_left₀ ht (∫ x in (0:ℝ)..t, Real.sinc x), ← h,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
  rw [uIoc_of_le zero_le_one] at hu
  have hu0 : u ≠ 0 := hu.1.ne'
  rw [Real.sinc_of_ne_zero (mul_ne_zero ht hu0)]
  field_simp

/-- `Ein(t) - Cin(t) = ∫₀¹ (cos(tu) - e^{-tu})/u du`. -/
theorem eiTr_cinIntegrand_intervalIntegrable {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun s : ℝ => (1 - Real.cos s) / s) volume 0 b := by
  refine (intervalIntegrable_const (c := b)).mono_fun'
    (by fun_prop : Measurable fun s : ℝ => (1 - Real.cos s) / s).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun s hs => ?_)
  rw [uIoc_of_le hb] at hs
  have hs0 : 0 < s := hs.1
  have h1 := Real.one_sub_sq_div_two_le_cos (x := s)
  have h2 := Real.cos_le_one s
  show ‖(1 - Real.cos s) / s‖ ≤ b
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hs0, abs_of_nonneg (by linarith), div_le_iff₀ hs0]
  nlinarith [hs.2]

/-- `Ein(t) - Cin(t) = ∫₀¹ (cos(tu) - e^{-tu})/u du` for `t ≥ 0`. -/
theorem eiTr_ein_sub_cin_eq {t : ℝ} (ht0 : 0 ≤ t) :
    Real.expIntEin t - Real.cosIntCin t =
      ∫ u in (0:ℝ)..1, (Real.cos (t * u) - Real.exp (-(t * u))) / u := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [Real.expIntEin, Real.cosIntCin]
  have hsub : Real.expIntEin t - Real.cosIntCin t =
      ∫ s in (0:ℝ)..t, (Real.cos s - Real.exp (-s)) / s := by
    rw [Real.expIntEin, Real.cosIntCin, ← intervalIntegral.integral_sub
      (intervalIntegrable_einIntegrand le_rfl ht0) (eiTr_cinIntegrand_intervalIntegrable ht0)]
    congr 1; funext s; ring
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun s : ℝ => (Real.cos s - Real.exp (-s)) / s) ht
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  rw [hsub, ← mul_inv_cancel_left₀ ht (∫ x in (0:ℝ)..t, (Real.cos x - Real.exp (-x)) / x), ← h,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
  rw [uIoc_of_le zero_le_one] at hu
  have hu0 : u ≠ 0 := hu.1.ne'
  field_simp

/-- The real sine integral `Si` is continuous. -/
theorem eiTr_continuous_sinInt : Continuous Real.sinInt :=
  continuous_iff_continuousAt.2 fun x => (Real.hasDerivAt_sinInt x).continuousAt

/-- `|Si(t)| ≤ t` for `t ≥ 0`. -/
theorem eiTr_abs_sinInt_le {t : ℝ} (ht : 0 ≤ t) : |Real.sinInt t| ≤ t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := 1)
    (f := Real.sinc) (fun x _ => by rw [Real.norm_eq_abs]; exact Real.abs_sinc_le_one x)
  rw [Real.sinInt, ← Real.norm_eq_abs]
  simpa [abs_of_nonneg ht] using h

/-- Laplace transform of `Si`. -/
theorem eiTr_laplace_sinInt {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => cexp (-a * t) * (Real.sinInt t : ℂ)) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), cexp (-a * t) * (Real.sinInt t : ℂ) = (π / 2 - arctan a) / a := by
  constructor
  · refine (laplace_nat_pow ha 1).1.norm.mono'
      ((Continuous.mul (by fun_prop) (continuous_ofReal.comp eiTr_continuous_sinInt)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    rw [norm_mul, norm_mul, Complex.norm_real, pow_one, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht0]; exact eiTr_abs_sinInt_le ht0.le)
      (norm_nonneg _)
  have h1 : ∫ t in Ioi (0:ℝ), cexp (-a * t) * (Real.sinInt t : ℂ) =
      ∫ t in Ioi (0:ℝ), cexp (-a * t) * ∫ u in (0:ℝ)..1, ((Real.sin (t * u) / u : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [eiTr_sinInt_eq, intervalIntegral.integral_ofReal]
  rw [h1, eiTr_swap01 ha (C := 1) (by unfold Function.uncurry; fun_prop) ?_,
    ← eiTr_integral_recip_sq_add_sq ha]
  · refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
    rw [uIoc_of_le zero_le_one] at hu
    have hu0 : (u:ℂ) ≠ 0 := by exact_mod_cast hu.1.ne'
    have : ∀ t : ℝ, cexp (-a * t) * ((Real.sin (t * u) / u : ℝ) : ℂ) =
        cexp (-a * t) * ((Real.sin (t * u) : ℝ) : ℂ) * (u:ℂ)⁻¹ := fun t => by
      push_cast; ring
    simp_rw [this]
    rw [integral_mul_const, eiTr_laplace_sin ha]
    have := eiTr_sq_add_sq_ne ha u
    field_simp
  · intro t u ht hu
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hu.1, div_le_iff₀ hu.1]
    have := Real.abs_sin_le_abs (x := t * u)
    rw [abs_of_nonneg (by nlinarith [hu.1] : (0:ℝ) ≤ t * u)] at this
    have h2 : t * u ≤ 1 * (1 + t ^ 2) * u :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (t - 1)]) hu.1.le
    linarith

/-- Integrability of a Laplace transform of an inner `[0,1]` integral with quadratically bounded
  integrand. -/
theorem eiTr_integrable01 {a : ℂ} (ha : 0 < a.re) {F : ℝ → ℝ → ℂ}
    (hF : Measurable (Function.uncurry F)) {C : ℝ}
    (hb : ∀ t u : ℝ, 0 < t → u ∈ Ioc (0:ℝ) 1 → ‖F t u‖ ≤ C * (1 + t ^ 2)) :
    IntegrableOn (fun t : ℝ => cexp (-a * t) * ∫ u in (0:ℝ)..1, F t u) (Ioi 0) := by
  have hg : Integrable (fun t : ℝ => C * (‖cexp (-a * t) * (t:ℂ) ^ 0‖ +
      ‖cexp (-a * t) * (t:ℂ) ^ 2‖)) (volume.restrict (Ioi 0)) :=
    ((laplace_nat_pow ha 0).1.norm.add (laplace_nat_pow ha 2).1.norm).const_mul C
  have hprod := hg.mul_prod (integrable_const (1:ℝ) : Integrable (fun _ : ℝ => (1:ℝ))
    (volume.restrict (Ioc (0:ℝ) 1)))
  have hI : Integrable (Function.uncurry fun (t u : ℝ) => cexp (-a * t) * F t u)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    refine hprod.mono' ?_ ?_
    · exact (Measurable.mul (by fun_prop) hF).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)] with p hp
      obtain ⟨hp1, hp2⟩ := hp
      have ht : (0:ℝ) < p.1 := hp1
      simp only [Function.uncurry, norm_mul, pow_zero, mul_one, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht]
      have := hb p.1 p.2 ht hp2
      have h0 : 0 ≤ ‖cexp (-a * p.1)‖ := norm_nonneg _
      calc ‖cexp (-a * p.1)‖ * ‖F p.1 p.2‖ ≤ ‖cexp (-a * p.1)‖ * (C * (1 + p.1 ^ 2)) :=
            mul_le_mul_of_nonneg_left this h0
        _ = _ := by ring
  have := hI.integral_prod_left
  refine Integrable.congr this (Eventually.of_forall fun t => ?_)
  simp only [Function.uncurry_apply_pair]
  rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one]

/-- `a²` lies in the slit plane when `Re a > 0`. -/
theorem eiTr_sq_mem_slitPlane {a : ℂ} (ha : 0 < a.re) : a ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases eq_or_ne a.im 0 with h | h
  · left; simp [sq, h]; positivity
  · right; simp only [sq, mul_im]
    intro h'
    have : a.re * a.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact h h1

/-- `log(a²) = 2 log a` for `Re a > 0` (principal branch). -/
theorem eiTr_log_sq {a : ℂ} (ha : 0 < a.re) : log (a ^ 2) = 2 * log a := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have harg := abs_arg_lt_pi_div_two_iff.2 (Or.inl ha)
  rw [abs_lt] at harg
  rw [show a ^ 2 = exp (2 * log a) by rw [two_mul, exp_add, exp_log ha0, sq]]
  refine log_exp ?_ ?_
  · simp [log_im]; linarith
  · simp [log_im]; linarith

/-- Closed form of the inner integral arising in the Laplace transform of `Ci`. -/
theorem eiTr_integral_ci_kernel {a : ℂ} (ha : 0 < a.re) :
    ∫ u in (0:ℝ)..1, (a / (a ^ 2 + (u:ℂ) ^ 2) - 1 / (a + u)) / u =
      (log (1 + a) - log (1 + a ^ 2) / 2) / a := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hs1 : ∀ u : ℝ, 0 ≤ u → a + u ∈ slitPlane := fun u hu => by
    left; simp; linarith
  have hs2 : ∀ u : ℝ, a ^ 2 + (u:ℂ) ^ 2 ∈ slitPlane := fun u => by
    have := add_ofReal_mem_slitPlane (eiTr_sq_mem_slitPlane ha) (sq_nonneg u)
    simpa using this
  have hn1 : ∀ u : ℝ, 0 ≤ u → a + u ≠ 0 := fun u hu => slitPlane_ne_zero (hs1 u hu)
  have hn2 : ∀ u : ℝ, a ^ 2 + (u:ℂ) ^ 2 ≠ 0 := fun u => slitPlane_ne_zero (hs2 u)
  have hcongr : ∫ u in (0:ℝ)..1, (a / (a ^ 2 + (u:ℂ) ^ 2) - 1 / (a + u)) / u =
      ∫ u in (0:ℝ)..1, (1 / (a + u) - u / (a ^ 2 + (u:ℂ) ^ 2)) / a := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
    rw [uIoc_of_le zero_le_one] at hu
    have hu0 : (u:ℂ) ≠ 0 := by exact_mod_cast hu.1.ne'
    have h1 := hn1 u hu.1.le
    have h2 := hn2 u
    field_simp
    ring
  have hd : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt
      (fun u : ℝ => (log (a + u) - log (a ^ 2 + (u:ℂ) ^ 2) / 2) / a)
      ((1 / (a + x) - x / (a ^ 2 + (x:ℂ) ^ 2)) / a) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have h1 := ((ofRealCLM.hasDerivAt (x := x)).const_add a).clog_real (hs1 x hx.1)
    have hq : HasDerivAt (fun u : ℝ => a ^ 2 + (u:ℂ) ^ 2) (2 * x) x := by
      have := ((hasDerivAt_pow 2 (x:ℂ)).comp_ofReal (z := x)).const_add (a ^ 2)
      simpa using this
    have h2 := hq.clog_real (hs2 x)
    simp only [ofRealCLM_apply] at h1
    convert (h1.sub (h2.div_const 2)).div_const a using 1
    push_cast
    have := hn2 x
    field_simp
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hd ?_]
  · simp only [ofReal_one, ofReal_zero, add_zero, one_pow, zero_pow two_ne_zero]
    rw [eiTr_log_sq ha, add_comm a 1, add_comm (a ^ 2) 1]
    field_simp
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.div_const (ContinuousOn.sub ?_ ?_) a
    · exact continuousOn_const.div (by fun_prop) fun x hx => hn1 x hx.1
    · exact (Continuous.div (by fun_prop) (by fun_prop) hn2).continuousOn

/-- Laplace transform of `E₁`: `∫₀^∞ e^{-at} E₁(t) dt = log(1+a)/a` for `Re a > -1`, with
  integrability. -/
theorem eiTr_laplace_E1 {a : ℂ} (ha : -1 < a.re) :
    IntegrableOn (fun t : ℝ => cexp (-a * t) * genExpIntE 1 t) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), cexp (-a * t) * genExpIntE 1 t = if a = 0 then 1 else log (1 + a) / a := by
  have hI := eiTr_integrable_E1_kernel ha
  have hcongr : ∀ t ∈ Ioi (0:ℝ), cexp (-a * t) * genExpIntE 1 t =
      ∫ u in Ioi (1:ℝ), cexp (-a * t) * ((Real.exp (-(t * u)) / u : ℝ) : ℂ) := by
    intro t ht
    rw [eiTr_E1_eq ht, integral_const_mul]
  constructor
  · refine IntegrableOn.congr_fun ?_ (fun t ht => (hcongr t ht).symm) measurableSet_Ioi
    exact hI.integral_prod_left
  rw [← eiTr_integral_recip_mul ha, setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_integral_swap hI]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu1 : (1:ℝ) < u := hu
  have hu0 : (u:ℂ) ≠ 0 := by exact_mod_cast (lt_trans one_pos hu1).ne'
  have hc : 0 < (a + u).re := by simp; linarith
  have hca : a + u ≠ 0 := fun h => by rw [h] at hc; simp at hc
  calc ∫ t in Ioi (0:ℝ), cexp (-a * t) * ((Real.exp (-(t * u)) / u : ℝ) : ℂ)
      = ∫ t in Ioi (0:ℝ), (u:ℂ)⁻¹ * cexp (-(a + u) * t) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        push_cast
        rw [show -(a + u) * (t:ℂ) = -a * t + -(t * u) by ring, Complex.exp_add]
        ring
    _ = 1 / ((a + u) * u) := by
        rw [integral_const_mul, eiTr_integral_exp_neg hc]; field_simp

/-- Uniform bound for the kernel `(cos(tu) - e^{-tu})/u` on `u ∈ (0,1]`. -/
theorem eiTr_ein_cin_bound {t u : ℝ} (ht : 0 < t) (hu : u ∈ Ioc (0:ℝ) 1) :
    ‖(((Real.cos (t * u) - Real.exp (-(t * u))) / u : ℝ) : ℂ)‖ ≤ 1 * (1 + t ^ 2) := by
  have hu0 := hu.1
  have hx : 0 ≤ t * u := by positivity
  have c1 := Real.one_sub_sq_div_two_le_cos (x := t * u)
  have c2 := Real.cos_le_one (t * u)
  have e1 := Real.add_one_le_exp (-(t * u))
  have e2 : Real.exp (-(t * u)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hu0, div_le_iff₀ hu0, abs_le]
  have h1 : t * u ≤ t := by nlinarith [hu.2]
  have h2 : (t * u) ^ 2 / 2 ≤ t ^ 2 * u / 2 := by
    have : (t * u) ^ 2 = t ^ 2 * u * u := by ring
    rw [this]; nlinarith [hu.2, sq_nonneg t, mul_nonneg (sq_nonneg t) hu0.le]
  constructor <;> nlinarith [sq_nonneg (t - 1), mul_nonneg (sq_nonneg t) hu0.le]

/-- The entire cosine integral `Cin` is continuous on `ℝ`. -/
theorem eiTr_continuous_cosIntCin : Continuous Real.cosIntCin := by
  have h : Real.cosIntCin = fun x : ℝ => (cosIntCin (x:ℂ)).re := by
    funext x; rw [cosIntCin_ofReal]; simp
  rw [h]
  exact Complex.continuous_re.comp (cosIntCin_entire.continuous.comp continuous_ofReal)

/-- `Ci(x) → 0` as `x → ∞`. -/
theorem eiTr_tendsto_cosInt_real : Tendsto Real.cosInt atTop (𝓝 0) := by
  have h := (Complex.continuous_re.tendsto 0).comp cosInt_tendsto_atTop
  simp only [Complex.zero_re] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp [Function.comp_apply, cosInt_ofReal hx]

/-- `Si(x) - π/2 → 0` as `x → ∞`. -/
theorem eiTr_tendsto_sinIntTail_real : Tendsto (fun x => Real.sinInt x - π / 2) atTop (𝓝 0) := by
  have := Real.tendsto_sinInt_atTop.sub_const (π / 2)
  simpa using this

/-- `sin t · log t = sinc t · (t log t)` for all real `t`. -/
theorem eiTr_sin_mul_log (t : ℝ) : Real.sin t * Real.log t = Real.sinc t * (t * Real.log t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [Real.sinc_of_ne_zero ht]; field_simp

/-- `t ↦ sin t · Ci(t)` is continuous (with the totalized value at `0`). -/
theorem eiTr_continuous_sin_mul_cosInt : Continuous fun t => Real.sin t * Real.cosInt t := by
  have h : (fun t => Real.sin t * Real.cosInt t) = fun t =>
      Real.sin t * (-Real.cosIntCin t + Real.eulerMascheroniConstant) +
        Real.sinc t * (t * Real.log t) := by
    funext t; rw [Real.cosInt, ← eiTr_sin_mul_log]; ring
  rw [h]
  exact ((Real.continuous_sin.mul (eiTr_continuous_cosIntCin.neg.add continuous_const)).add
    (Real.continuous_sinc.mul Real.continuous_mul_log))

/-- `t ↦ cos t · Ci(t)` is interval integrable on `[0, R]`. -/
theorem eiTr_intervalIntegrable_cos_mul_cosInt (R : ℝ) :
    IntervalIntegrable (fun t => Real.cos t * Real.cosInt t) volume 0 R := by
  have h : (fun t => Real.cos t * Real.cosInt t) = fun t =>
      Real.cos t * (-Real.cosIntCin t + Real.eulerMascheroniConstant) +
        Real.cos t * Real.log t := by
    funext t; rw [Real.cosInt]; ring
  rw [h]
  exact ((Real.continuous_cos.mul (eiTr_continuous_cosIntCin.neg.add continuous_const)).intervalIntegrable
    _ _).add (intervalIntegral.intervalIntegrable_log'.continuousOn_mul Real.continuous_cos.continuousOn)

/-- `∫₀^R cos t Ci(t) dt = sin R Ci(R) - Si(2R)/2` for `R ≥ 0`. -/
theorem eiTr_integral_cos_mul_cosInt {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (0:ℝ)..R, Real.cos t * Real.cosInt t = Real.sin R * Real.cosInt R - Real.sinInt (2 * R) / 2 := by
  have hc : Continuous fun t => Real.sin t * Real.cosInt t - Real.sinInt (2 * t) / 2 :=
    eiTr_continuous_sin_mul_cosInt.sub ((eiTr_continuous_sinInt.comp (continuous_const.mul continuous_id)).div_const 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR hc.continuousOn ?_
    (eiTr_intervalIntegrable_cos_mul_cosInt R)]
  · simp [Real.sinInt]
  · intro x hx
    have hx0 : 0 < x := hx.1
    have h1 := (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cosInt hx0)
    have h2 := ((Real.hasDerivAt_sinInt (2 * x)).comp x ((hasDerivAt_id x).const_mul 2)).div_const 2
    refine (h1.sub h2).congr_deriv ?_
    rw [Real.sinc_of_ne_zero (by positivity : (2:ℝ) * x ≠ 0), Real.sin_two_mul]
    field_simp
    ring

/-- `∫₀^R cos t · Ci(t) dt → -π/4` as `R → ∞`. -/
theorem eiTr_tendsto_integral_cos_mul_cosInt :
    Tendsto (fun R => ∫ t in (0:ℝ)..R, Real.cos t * Real.cosInt t) atTop (𝓝 (-(π / 4))) := by
  have h1 : Tendsto (fun R => Real.sin R * Real.cosInt R) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun R => ‖Real.cosInt R‖) (fun R => ?_)
      (by simpa using eiTr_tendsto_cosInt_real.norm)
    rw [norm_mul, Real.norm_eq_abs]
    simpa [Real.norm_eq_abs] using mul_le_of_le_one_left (abs_nonneg (Real.cosInt R)) (Real.abs_sin_le_one R)
  have h2 : Tendsto (fun R : ℝ => Real.sinInt (2 * R) / 2) atTop (𝓝 (π / 2 / 2)) :=
    (Real.tendsto_sinInt_atTop.comp (tendsto_id.const_mul_atTop two_pos)).div_const 2
  have := h1.sub h2
  rw [show (0:ℝ) - π / 2 / 2 = -(π / 4) by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  rw [eiTr_integral_cos_mul_cosInt hR]

/-- `∫₀^R sin t si(t) dt = -cos R si(R) - π/2 + Si(2R)/2`. -/
theorem eiTr_integral_sin_mul_sinIntTail (R : ℝ) :
    ∫ t in (0:ℝ)..R, Real.sin t * (Real.sinInt t - π / 2) =
      -Real.cos R * (Real.sinInt R - π / 2) + Real.sinInt (2 * R) / 2 - π / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t =>
      -Real.cos t * (Real.sinInt t - π / 2) + Real.sinInt (2 * t) / 2)
      (f' := fun t => Real.sin t * (Real.sinInt t - π / 2)) ?_
    ((Real.continuous_sin.mul (eiTr_continuous_sinInt.sub continuous_const)).intervalIntegrable _ _)]
  · simp [Real.sinInt]
  · intro x _
    have h1 := ((Real.hasDerivAt_cos x).neg).mul ((Real.hasDerivAt_sinInt x).sub_const (π / 2))
    have h2 := ((Real.hasDerivAt_sinInt (2 * x)).comp x ((hasDerivAt_id x).const_mul 2)).div_const 2
    refine (h1.add h2).congr_deriv ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rw [Real.sinc_of_ne_zero (by positivity : (2:ℝ) * x ≠ 0), Real.sinc_of_ne_zero hx, Real.sin_two_mul]
    simp only [Pi.neg_apply]
    field_simp
    ring

/-- `∫₀^R sin t · (Si(t) - π/2) dt → -π/4` as `R → ∞`. -/
theorem eiTr_tendsto_integral_sin_mul_sinIntTail :
    Tendsto (fun R => ∫ t in (0:ℝ)..R, Real.sin t * (Real.sinInt t - π / 2)) atTop
      (𝓝 (-(π / 4))) := by
  have h1 : Tendsto (fun R => -Real.cos R * (Real.sinInt R - π / 2)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun R => ‖Real.sinInt R - π / 2‖) (fun R => ?_)
      (by simpa using eiTr_tendsto_sinIntTail_real.norm)
    rw [norm_mul, norm_neg, Real.norm_eq_abs (Real.cos R)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one R)
  have h2 : Tendsto (fun R : ℝ => Real.sinInt (2 * R) / 2) atTop (𝓝 (π / 2 / 2)) :=
    (Real.tendsto_sinInt_atTop.comp (tendsto_id.const_mul_atTop two_pos)).div_const 2
  have := (h1.add h2).sub_const (π / 2)
  rw [show (0:ℝ) + π / 2 / 2 - π / 2 = -(π / 4) by ring] at this
  refine this.congr' (Eventually.of_forall fun R => ?_)
  exact (eiTr_integral_sin_mul_sinIntTail R).symm

/-- `|log t| ≤ 4 t^{-1/4}` for `0 < t ≤ 1`. -/
theorem eiTr_abs_log_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : |Real.log t| ≤ 4 * t ^ (-(1/4:ℝ)) := by
  have h1 := Real.neg_rpow_div_le_log ht.le (by norm_num : (0:ℝ) < 1/4)
  have h2 := Real.log_nonpos ht.le ht1
  rw [abs_of_nonpos h2]
  have : -t ^ (-(1/4:ℝ)) / (1/4) = -(4 * t ^ (-(1/4:ℝ))) := by ring
  linarith

/-- `t^{-1/4} ≤ t^{-1/2}` for `0 < t ≤ 1`. -/
theorem eiTr_rpow_quarter_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    t ^ (-(1/4:ℝ)) ≤ t ^ (-(1/2:ℝ)) :=
  Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)

/-- `1 ≤ t^{-1/4}` for `0 < t ≤ 1`. -/
theorem eiTr_one_le_rpow {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : 1 ≤ t ^ (-(1/4:ℝ)) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by norm_num)

/-- A function bounded by `A + B t^{-1/2}` on `(0,1]` and by `C/t²` on `(1,∞)` is integrable. -/
theorem eiTr_integrableOn_Ioi_of_bound {h : ℝ → ℝ} (hm : AEStronglyMeasurable h (volume.restrict (Ioi 0)))
    {A B C : ℝ} (h1 : ∀ t ∈ Ioc (0:ℝ) 1, |h t| ≤ A + B * t ^ (-(1/2:ℝ)))
    (h2 : ∀ t : ℝ, 1 < t → |h t| ≤ C / t ^ 2) : IntegrableOn h (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hi : IntegrableOn (fun t : ℝ => A + B * t ^ (-(1/2:ℝ))) (Ioc 0 1) := by
      have : IntervalIntegrable (fun t : ℝ => A + B * t ^ (-(1/2:ℝ))) volume 0 1 :=
        (intervalIntegrable_const (c := A)).add
        ((intervalIntegral.intervalIntegrable_rpow' (r := -(1/2:ℝ)) (by norm_num)).const_mul B)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    refine hi.mono' (hm.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]; exact h1 t ht
  · have hi : IntegrableOn (fun t : ℝ => C * t ^ (-2:ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul C
    refine hi.mono' (hm.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) < t := ht
    rw [Real.norm_eq_abs, Real.rpow_neg (by linarith), show (2:ℝ) = (2:ℕ) by norm_num,
      Real.rpow_natCast, ← div_eq_mul_inv]
    exact h2 t ht1

/-- `|f(x)| ≤ 1/x`, `|g(x)| ≤ 1/x` for `x > 0`. -/
lemma eiTr_norm_aux_le {x : ℝ} (hx : 0 < x) :
    ‖expIntAuxF x‖ ≤ 1 / x ∧ ‖expIntAuxG x‖ ≤ 1 / x := by
  obtain ⟨hF, hG⟩ := expIntAux_ofReal_laplace_Ioi hx
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-(x * u))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hx
  have hval : ∫ u in Ioi (0:ℝ), Real.exp (-(x * u)) = 1 / x := by
    have := integral_exp_mul_Ioi (a := -x) (by linarith) 0
    simp only [mul_zero, Real.exp_zero, neg_mul] at this
    rw [this]; field_simp
  have hE : ∀ u : ℝ, ‖cexp (-(x : ℂ) * u)‖ = Real.exp (-(x * u)) := fun u => by
    rw [Complex.norm_exp]; congr 1; simp
  have hden : ∀ u : ℝ, ((u : ℂ) ^ 2 + 1) = ((u ^ 2 + 1 : ℝ) : ℂ) := fun u => by push_cast; ring
  constructor
  · rw [hF, ← hval]
    refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun u => ?_)
    rw [norm_div, hE, hden, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact div_le_self (Real.exp_pos _).le (by nlinarith [sq_nonneg u])
  · rw [hG, ← hval]
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0:ℝ) < u := hu
    rw [norm_div, norm_mul, hE, hden, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hu0, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    have := (Real.exp_pos (-(x * u))).le
    nlinarith [sq_nonneg (u - 1)]

/-- `|Ci(x)| ≤ 2/x` for `x > 0`. -/
theorem eiTr_abs_cosInt_le {x : ℝ} (hx : 0 < x) : |Real.cosInt x| ≤ 2 / x := by
  obtain ⟨h1, h2⟩ := eiTr_norm_aux_le hx
  have h := cosInt_eq_aux (x:ℂ)
  rw [cosInt_ofReal hx] at h
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h]
  calc ‖expIntAuxF x * sin x - expIntAuxG x * cos x‖
      ≤ ‖expIntAuxF x‖ * ‖sin (x:ℂ)‖ + ‖expIntAuxG x‖ * ‖cos (x:ℂ)‖ := by
        rw [← norm_mul, ← norm_mul]; exact norm_sub_le _ _
    _ ≤ 1 / x * 1 + 1 / x * 1 := by
        gcongr
        · exact norm_sin_ofReal_le_one x
        · exact norm_cos_ofReal_le_one x
    _ = 2 / x := by ring

/-- `|Si(x) - π/2| ≤ 2/x` for `x > 0`. -/
theorem eiTr_abs_sinIntTail_le {x : ℝ} (hx : 0 < x) : |Real.sinInt x - π / 2| ≤ 2 / x := by
  obtain ⟨h1, h2⟩ := eiTr_norm_aux_le hx
  have h := sinInt_eq_aux (x:ℂ)
  rw [sinInt_ofReal] at h
  have h' : ((Real.sinInt x - π / 2 : ℝ) : ℂ) = -(expIntAuxF x * cos x) - expIntAuxG x * sin x := by
    push_cast; rw [h]; ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h']
  calc ‖-(expIntAuxF x * cos x) - expIntAuxG x * sin x‖
      ≤ ‖expIntAuxF x‖ * ‖cos (x:ℂ)‖ + ‖expIntAuxG x‖ * ‖sin (x:ℂ)‖ := by
        rw [← norm_mul, ← norm_mul, ← norm_neg (expIntAuxF x * cos x)]; exact norm_sub_le _ _
    _ ≤ 1 / x * 1 + 1 / x * 1 := by
        gcongr
        · exact norm_cos_ofReal_le_one x
        · exact norm_sin_ofReal_le_one x
    _ = 2 / x := by ring

/-- `|Cin(t)| ≤ 1` for `0 ≤ t ≤ 1`. -/
theorem eiTr_abs_cosIntCin_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : |Real.cosIntCin t| ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := 1)
    (f := fun s : ℝ => (1 - Real.cos s) / s) (fun s hs => ?_)
  · rw [Real.cosIntCin, ← Real.norm_eq_abs]
    calc _ ≤ 1 * |t - 0| := h
      _ ≤ 1 := by rw [sub_zero, abs_of_nonneg ht]; linarith
  · rw [uIoc_of_le ht] at hs
    have hs0 : 0 < s := hs.1
    have c1 := Real.one_sub_sq_div_two_le_cos (x := s)
    have c2 := Real.cos_le_one s
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hs0, abs_of_nonneg (by linarith), div_le_iff₀ hs0]
    nlinarith [hs.2]

/-- `|Ci(t)| ≤ 2 + 4 t^{-1/4}` for `0 < t ≤ 1`. -/
theorem eiTr_abs_cosInt_le_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |Real.cosInt t| ≤ 2 + 4 * t ^ (-(1/4:ℝ)) := by
  have h1 := eiTr_abs_cosIntCin_le ht.le ht1
  have h2 := eiTr_abs_log_le ht ht1
  have h3 := Real.eulerMascheroniConstant_lt_two_thirds
  have h4 := Real.one_half_lt_eulerMascheroniConstant
  rw [Real.cosInt]
  calc |-Real.cosIntCin t + Real.log t + Real.eulerMascheroniConstant|
      ≤ |Real.cosIntCin t| + |Real.log t| + |Real.eulerMascheroniConstant| := by
        have := abs_add_le (-Real.cosIntCin t + Real.log t) Real.eulerMascheroniConstant
        have := abs_add_le (-Real.cosIntCin t) (Real.log t)
        rw [abs_neg] at this; linarith
    _ ≤ 2 + 4 * t ^ (-(1/4:ℝ)) := by
        rw [abs_of_pos (by linarith : (0:ℝ) < Real.eulerMascheroniConstant)]; linarith

/-- `|Si(t) - π/2| ≤ 3` for `0 ≤ t ≤ 1`. -/
theorem eiTr_abs_sinIntTail_le_small {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |Real.sinInt t - π / 2| ≤ 3 := by
  have h1 : |Real.sinInt t| ≤ t := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := 1)
      (f := Real.sinc) (fun x _ => by rw [Real.norm_eq_abs]; exact Real.abs_sinc_le_one x)
    rw [Real.sinInt, ← Real.norm_eq_abs]
    simpa [abs_of_nonneg ht] using h
  have := abs_sub (Real.sinInt t) (π / 2)
  rw [abs_of_pos (by positivity : 0 < π / 2)] at this
  linarith [Real.pi_lt_four]

/-- The real cosine integral `Ci` is measurable. -/
theorem eiTr_measurable_cosInt : Measurable Real.cosInt := by
  have : Real.cosInt = fun t => -Real.cosIntCin t + Real.log t + Real.eulerMascheroniConstant := by
    funext t; rfl
  rw [this]
  exact ((eiTr_continuous_cosIntCin.measurable.neg).add Real.measurable_log).add_const _

/-- `Ci` is continuous at every `x > 0`. -/
theorem eiTr_continuousAt_cosInt {x : ℝ} (hx : 0 < x) : ContinuousAt Real.cosInt x :=
  (Real.hasDerivAt_cosInt hx).continuousAt

/-- `t Ci(t) = t (γ - Cin t) + t log t` (all real `t`). -/
theorem eiTr_mul_cosInt (t : ℝ) : t * Real.cosInt t =
    t * (-Real.cosIntCin t + Real.eulerMascheroniConstant) + t * Real.log t := by
  rw [Real.cosInt]; ring

/-- `t ↦ t · Ci(t)` is continuous. -/
theorem eiTr_continuous_mul_cosInt : Continuous fun t => t * Real.cosInt t := by
  simp_rw [eiTr_mul_cosInt]
  exact (continuous_id.mul (eiTr_continuous_cosIntCin.neg.add continuous_const)).add
    Real.continuous_mul_log

/-- `Ci²` is integrable on `(0, ∞)`. -/
theorem eiTr_integrableOn_cosInt_sq : IntegrableOn (fun t => Real.cosInt t ^ 2) (Ioi 0) := by
  refine eiTr_integrableOn_Ioi_of_bound (A := 4) (B := 32) (C := 4)
    (eiTr_measurable_cosInt.pow_const 2).aestronglyMeasurable (fun t ht => ?_) (fun t ht => ?_)
  · have h := eiTr_abs_cosInt_le_small ht.1 ht.2
    have h1 := eiTr_rpow_quarter_le ht.1 ht.2
    have h2 := eiTr_one_le_rpow ht.1 ht.2
    have hq : (t ^ (-(1/4:ℝ))) ^ 2 = t ^ (-(1/2:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]; norm_num
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have h0 : 0 ≤ |Real.cosInt t| := abs_nonneg _
    calc |Real.cosInt t| ^ 2 ≤ (2 + 4 * t ^ (-(1/4:ℝ))) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = 4 + 16 * t ^ (-(1/4:ℝ)) + 16 * (t ^ (-(1/4:ℝ))) ^ 2 := by ring
      _ ≤ 4 + 32 * t ^ (-(1/2:ℝ)) := by rw [hq]; nlinarith
  · have h := eiTr_abs_cosInt_le (by linarith : (0:ℝ) < t)
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc |Real.cosInt t| ^ 2 ≤ (2 / t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 4 / t ^ 2 := by ring

end DLMF.Confluent
end
