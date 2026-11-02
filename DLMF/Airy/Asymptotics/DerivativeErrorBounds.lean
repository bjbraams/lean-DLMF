/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Asymptotics.DerivativeRemainders

/-!
# Error bounds for the `Ai'` and `Bi'` expansions

The normalized derivative `F(w) = w^{-1/6} U(-1/6, -1/3, w)`, `w = 2ζ`, is the Stieltjes
transform `F(w) = 1 + (2π)⁻¹ ∫₀^∞ ρ(t)/(t + w) dt` of a positive density `ρ`
(`DLMF.Airy.Asymptotics.DerivativeRemainders`). Expanding `1/(t + w)` gives the exact
remainder `(2π)⁻¹ (-1)^N w^{-N} ∫₀^∞ ρ(t) t^N/(t + w) dt`, whose moments `m_j` are the
coefficients `v_{j+1} 2^{j+1} = -m_j/(2π)`. Writing `ρ(t) = e^{-t} + ∫₀^∞ e^{-(1+v)t} g(v) dv`
with `g ≥ 0`, the chi estimates of `DLMF.Airy.StieltjesForm` bound the remainder by `χ(N) + 1`
times the first neglected term on `0 < |arg z| < 2π/3`; continuity extends this to the rays
`|arg z| = 2π/3`, and the derivative of DLMF 9.2.10 transfers it to `Bi'` on the positive axis.

## Main results

* `airy_biDeriv_real_error`: `|R^{Bi'}_N(x)| ≤ (χ(N) + 1) |v_N ζ^{-N}|` for `x > 0`, `N ≥ 1`
  (DLMF §9.7(iii)).
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology Interval

namespace DLMF.Airy


/-- The moments `m_j = Γ(j+5/6) Γ(j+13/6)/Γ(j+2)` of the derivative density. -/
private noncomputable def airyDerMoment (j : ℕ) : ℝ :=
  Real.Gamma ((j : ℝ) + 5 / 6) * Real.Gamma ((j : ℝ) + 13 / 6) / Real.Gamma ((j : ℝ) + 2)

/-- `u_{k+1} = u_k (k + 1/6)(k + 5/6)/(2(k+1))`. -/
private lemma airyU_succ_real (k : ℕ) :
    airyU (k + 1) = airyU k * ((k + 1 / 6) * (k + 5 / 6) / (2 * (k + 1))) := by
  simp only [airyU, ascPochhammer_succ_eval, pow_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- `Γ(5/6) Γ(7/6) = π/3`. -/
private lemma gamma_five_sixths_mul_seven_sixths :
    Real.Gamma (5 / 6) * Real.Gamma (7 / 6) = π / 3 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 6)
  have hg := Real.Gamma_add_one (show (1 / 6 : ℝ) ≠ 0 by norm_num)
  rw [show π * (1 / 6) = π / 6 by ring, Real.sin_pi_div_six] at h
  norm_num at h hg
  rw [hg]
  linear_combination (1 / 6 : ℝ) * h

/-- `v_{j+1} 2^{j+1} = -m_j/(2π)`: the coefficients are the Stieltjes moments. -/
private lemma airyV_succ_mul_two_pow (j : ℕ) :
    airyV (j + 1) * 2 ^ (j + 1) = -(1 / (2 * π)) * airyDerMoment j := by
  induction j with
  | zero =>
    simp only [zero_add, pow_one, airyReal_airyV_one, airyDerMoment, Nat.cast_zero]
    norm_num
    rw [show (13 / 6 : ℝ) = 7 / 6 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
    have := gamma_five_sixths_mul_seven_sixths
    have hπ := Real.pi_pos
    rw [show Real.Gamma (5 / 6) * (7 / 6 * Real.Gamma (7 / 6)) = 7 / 6 * (π / 3) by
      rw [← this]; ring]
    field_simp
    ring
  | succ j ih =>
    have hm : airyDerMoment (j + 1) =
        airyDerMoment j * ((j + 5 / 6) * (j + 13 / 6) / (j + 2)) := by
      simp only [airyDerMoment]
      push_cast
      rw [show (j : ℝ) + 1 + 5 / 6 = (j + 5 / 6) + 1 by ring,
        show (j : ℝ) + 1 + 13 / 6 = (j + 13 / 6) + 1 by ring,
        show (j : ℝ) + 1 + 2 = (j + 2) + 1 by ring,
        Real.Gamma_add_one (by positivity), Real.Gamma_add_one (by positivity),
        Real.Gamma_add_one (by positivity)]
      have := Real.Gamma_pos_of_pos (show (0 : ℝ) < j + 2 by positivity)
      field_simp
    have hv : airyV (j + 2) * 2 ^ (j + 2) =
        airyV (j + 1) * 2 ^ (j + 1) * ((j + 5 / 6) * (j + 13 / 6) / (j + 2)) := by
      simp only [airyV]
      rw [show j + 2 = (j + 1) + 1 by ring, airyU_succ_real (j + 1)]
      push_cast
      have h1 : (1 : ℝ) - 6 * ((j : ℝ) + 1 + 1) ≠ 0 := by
        have : (0 : ℝ) ≤ j := j.cast_nonneg; intro h; linarith
      have h2 : (1 : ℝ) - 6 * ((j : ℝ) + 1) ≠ 0 := by
        have : (0 : ℝ) ≤ j := j.cast_nonneg; intro h; linarith
      field_simp
      ring
    rw [hv, ih, hm]
    ring


/-- The density `ρ` is continuous on `(0, ∞)`. -/
private lemma continuousOn_airyDer_density : ContinuousOn airyDer_density (Ioi 0) := by
  intro t ht
  have ht' : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 ht
  have hU : ContinuousAt (fun t : ℝ => airyDer_normalizedU t) t := by
    unfold airyDer_normalizedU
    exact ((continuousAt_cpow_const ht').comp continuous_ofReal.continuousAt).mul
      ((differentiableAt_kummerU _ _ ht').continuousAt.comp continuous_ofReal.continuousAt)
  exact ((Real.continuous_exp.comp continuous_neg).continuousAt.mul
    (Complex.continuous_re.continuousAt.comp hU)).continuousWithinAt

/-- The density `ρ` is integrable on `(0, ∞)`. -/
private lemma integrableOn_airyDer_density : IntegrableOn airyDer_density (Ioi 0) := by
  simpa using (airyDer_density_moment 0).1

/-- The density `ρ` is a.e. strongly measurable on `(0, ∞)`. -/
private lemma aestronglyMeasurable_airyDer_density :
    AEStronglyMeasurable airyDer_density (volume.restrict (Ioi 0)) :=
  continuousOn_airyDer_density.aestronglyMeasurable measurableSet_Ioi

/-- The Laplace density `g(v) = (2π)⁻¹ ∫₀^∞ ρ(s) e^{-sv} ds`, continued as `g(0)` for `v ≤ 0`. -/
private noncomputable def airyDerLaplace (v : ℝ) : ℝ :=
  1 / (2 * π) * ∫ s in Ioi (0 : ℝ), airyDer_density s * Real.exp (-(s * max v 0))

/-- The Laplace density `g` is continuous. -/
private lemma continuous_airyDerLaplace : Continuous airyDerLaplace := by
  refine continuous_const.mul (continuous_of_dominated (bound := airyDer_density) ?_ ?_
    integrableOn_airyDer_density ?_)
  · intro v
    exact aestronglyMeasurable_airyDer_density.mul (by fun_prop : Continuous fun s : ℝ =>
      Real.exp (-(s * max v 0))).aestronglyMeasurable
  · intro v
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (airyDer_density_nonneg hs),
      abs_of_pos (Real.exp_pos _)]
    refine mul_le_of_le_one_right (airyDer_density_nonneg hs) (Real.exp_le_one_iff.mpr ?_)
    have := mul_nonneg hs.le (le_max_right v 0)
    linarith
  · exact ae_of_all _ fun s => by fun_prop

/-- The Laplace density `g` is nonnegative. -/
private lemma airyDerLaplace_nonneg (v : ℝ) : 0 ≤ airyDerLaplace v := by
  unfold airyDerLaplace
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun s hs => ?_)
  exact mul_nonneg (airyDer_density_nonneg hs) (Real.exp_pos _).le

/-- The Laplace density `g` is bounded by `(1/2π)∫ρ`. -/
private lemma airyDerLaplace_le (v : ℝ) :
    airyDerLaplace v ≤ 1 / (2 * π) * ∫ s in Ioi (0 : ℝ), airyDer_density s := by
  unfold airyDerLaplace
  refine mul_le_mul_of_nonneg_left (setIntegral_mono_on ?_ integrableOn_airyDer_density
    measurableSet_Ioi fun s hs => ?_) (by positivity)
  · exact integrableOn_airyDer_density.mul_of_top_left (memLp_top_of_bound
      (by fun_prop : Continuous fun s : ℝ => Real.exp (-(s * max v 0))).aestronglyMeasurable 1
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        have := mul_nonneg hs.le (le_max_right v 0)
        linarith))
  · refine mul_le_of_le_one_right (airyDer_density_nonneg hs) (Real.exp_le_one_iff.mpr ?_)
    have := mul_nonneg (le_of_lt hs) (le_max_right v 0)
    linarith

/-- `Re F(r) = 1 + ∫₀^∞ e^{-vr} g(v) dv` for `r > 0`. -/
private lemma airyDer_normalizedU_re_eq {r : ℝ} (hr : 0 < r) :
    (airyDer_normalizedU r).re =
      1 + ∫ v in Ioi (0 : ℝ), Real.exp (-(v * r)) * airyDerLaplace v := by
  have hS := airyDer_stieltjes (ofReal_mem_slitPlane.2 hr)
  have hI : (∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * airyDer_normalizedU t / ((t : ℂ) + r)) =
      ((∫ t in Ioi (0 : ℝ), airyDer_density t / (t + r) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [← airyDer_density_coe ht]
    push_cast; rfl
  rw [hI] at hS
  have hre := congrArg Complex.re hS
  rw [show (1 : ℂ) / (2 * π : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; rfl, ← ofReal_mul,
    add_re, one_re, ofReal_re] at hre
  rw [hre]
  congr 1
  -- Tonelli
  set f : ℝ → ℝ → ℝ := fun v s => airyDer_density s * Real.exp (-((s + r) * v)) with hf
  have hinner : ∀ s, 0 < s → ∫ v in Ioi (0 : ℝ), f v s = airyDer_density s / (s + r) := by
    intro s hs
    simp only [hf]
    rw [integral_const_mul]
    have h := integral_exp_mul_Ioi (a := -(s + r)) (by linarith) 0
    simp only [mul_zero, Real.exp_zero] at h
    rw [show (fun v : ℝ => Real.exp (-((s + r) * v))) = fun v => Real.exp (-(s + r) * v) by
      funext v; ring_nf, h]
    field_simp
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry f)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
      have h1 := aestronglyMeasurable_airyDer_density.comp_snd
        (μ := volume.restrict (Ioi (0 : ℝ)))
      exact h1.mul (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Real.exp (-((p.2 + r) * p.1))).aestronglyMeasurable
    have hnorm : ∀ s, 0 < s →
        ∫ v in Ioi (0 : ℝ), ‖Function.uncurry f (v, s)‖ = airyDer_density s / (s + r) := by
      intro s hs
      rw [← hinner s hs]
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
      simp only [Function.uncurry, hf]
      exact Real.norm_of_nonneg (mul_nonneg (airyDer_density_nonneg hs) (Real.exp_pos _).le)
    refine (integrable_prod_iff' hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
      exact IntegrableOn.congr_fun ((exp_neg_integrableOn_Ioi 0
        (show 0 < s + r by linarith)).const_mul (airyDer_density s))
        (fun v _ => by simp only [hf, Function.uncurry]; ring_nf) measurableSet_Ioi
    · refine (integrableOn_airyDer_density.div_const r).mono' ?_ ?_
      · refine ((continuousOn_airyDer_density.div (continuousOn_id.add continuousOn_const)
          fun s (hs : 0 < s) => by
            change s + r ≠ 0; linarith).aestronglyMeasurable
            measurableSet_Ioi).congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
        exact (hnorm s hs).symm
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
        rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _), hnorm s hs]
        show _ ≤ airyDer_density s / r
        exact div_le_div_of_nonneg_left (airyDer_density_nonneg hs) hr (by linarith)
  have hswap := integral_integral_swap hint
  rw [setIntegral_congr_fun measurableSet_Ioi hinner] at hswap
  rw [← hswap, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
  simp only [airyDerLaplace, max_eq_left hv.le, hf]
  rw [mul_left_comm, ← integral_const_mul (Real.exp _)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only
  rw [show -((s + r) * v) = -(v * r) + -(s * v) by ring, Real.exp_add]
  ring


/-- `ρ(t) = e^{-t} + ∫₀^∞ e^{-(1+v)t} g(v) dv` for `t > 0`. -/
private lemma airyDer_density_eq {t : ℝ} (ht : 0 < t) :
    airyDer_density t = Real.exp (-t) +
      ∫ v in Ioi (0 : ℝ), Real.exp (-((1 + v) * t)) * airyDerLaplace v := by
  rw [airyDer_density, airyDer_normalizedU_re_eq ht, mul_add, mul_one, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  rw [show -((1 + v) * t) = -t + -(v * t) by ring, Real.exp_add]
  ring

/-- `X |sin θ| ≤ ‖X + t e^{iθ}‖` for real `t`. -/
private lemma le_norm_add_mul_exp {X θ : ℝ} (hX : 0 ≤ X) (t : ℝ) :
    X * |Real.sin θ| ≤ ‖(X : ℂ) + t * exp (θ * I)‖ := by
  have h : ‖(X : ℂ) + t * exp (θ * I)‖ = ‖(X : ℂ) * exp (-(θ * I)) + t‖ := by
    rw [← mul_one ‖(X : ℂ) + t * exp (θ * I)‖, ← norm_exp_ofReal_mul_I (-θ), ← norm_mul]
    congr 1
    rw [add_mul, mul_assoc, ← exp_add]
    push_cast
    ring_nf
    simp
  rw [h]
  refine le_trans ?_ (abs_im_le_norm _)
  have : ((X : ℂ) * exp (-(θ * I)) + t).im = -(X * Real.sin θ) := by
    rw [show -(θ * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I]
    simp [← ofReal_cos, ← ofReal_sin]
  rw [this, abs_neg, abs_mul, abs_of_nonneg hX]

/-- Dividing an integrable function by `X + t e^{iθ}`, `sin θ ≠ 0`, keeps it integrable. -/
private lemma integrableOn_div_den {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) {X θ : ℝ}
    (hX : 0 < X) (hsin : Real.sin θ ≠ 0) :
    IntegrableOn (fun t : ℝ => f t / ((X : ℂ) + t * exp (θ * I))) (Ioi 0) := by
  have hc : 0 < X * |Real.sin θ| := mul_pos hX (abs_pos.mpr hsin)
  refine (hf.norm.div_const (X * |Real.sin θ|)).mono' ?_ ?_
  · simp_rw [div_eq_mul_inv]
    exact hf.aestronglyMeasurable.mul (by fun_prop : Measurable fun t : ℝ =>
      ((X : ℂ) + t * exp (θ * I))⁻¹).aestronglyMeasurable
  · refine ae_of_all _ fun t => ?_
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hc (le_norm_add_mul_exp hX.le t)

/-- `v ↦ e^{-vr} g(v)` is integrable on `(0, ∞)` for `r > 0`. -/
private lemma integrableOn_airyDerLaplace_exp {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun v : ℝ => Real.exp (-(v * r)) * airyDerLaplace v) (Ioi 0) := by
  set C := 1 / (2 * π) * ∫ s in Ioi (0 : ℝ), airyDer_density s
  refine ((exp_neg_integrableOn_Ioi 0 hr).mul_const C).mono' ?_ (ae_of_all _ fun v => ?_)
  · exact (by fun_prop : Continuous fun v : ℝ => Real.exp (-(v * r))).aestronglyMeasurable.mul
      continuous_airyDerLaplace.aestronglyMeasurable
  · rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (airyDerLaplace_nonneg v), show -r * v = -(v * r) by ring]
    exact mul_le_mul_of_nonneg_left (airyDerLaplace_le v) (Real.exp_pos _).le

/-- The χ bound for the Stieltjes moments of the derivative density. -/
private lemma airyDer_J_bound {N : ℕ} (hN : 1 ≤ N) {X θ : ℝ} (hX : 0 < X)
    (hsin : Real.sin θ ≠ 0) :
    ‖∫ t in Ioi (0 : ℝ), (airyDer_density t : ℂ) * (t : ℂ) ^ N / (X + t * exp (θ * I))‖ ≤
      airyChi N * airyDerMoment (N - 1) := by
  have hm : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr : ((N : ℝ) : ℂ) = (N : ℂ) := by push_cast; rfl
  have hrp : ∀ r : ℝ, 0 < r → r ^ ((N : ℝ) - 1) = r ^ (N - 1) := by
    intro r hr
    rw [← Real.rpow_natCast, Nat.cast_sub hN, Nat.cast_one]
  -- the two Laplace pieces
  have hG : ∀ r : ℝ, 0 < r → (∫ v in Ioi (0 : ℝ), Real.exp (-((1 + v) * r)) * airyDerLaplace v) =
      airyDer_density r - Real.exp (-r) := fun r hr => by rw [airyDer_density_eq hr]; ring
  have hMomN := (airyDer_density_moment N).1
  have hMomN1 := (airyDer_density_moment (N - 1)).1
  have hExpN : IntegrableOn (fun r : ℝ => r ^ N * Real.exp (-r)) (Ioi 0) := by
    simpa using StieltjesRemainder.integrableOn_rpow_exp (m := (N : ℝ)) (by linarith) one_pos
  have hExpN1 : IntegrableOn (fun r : ℝ => r ^ (N - 1) * Real.exp (-r)) (Ioi 0) := by
    have := StieltjesRemainder.integrableOn_rpow_exp (m := ((N - 1 : ℕ) : ℝ))
      (by have := (N - 1 : ℕ).cast_nonneg (α := ℝ); linarith) one_pos
    simpa using this
  have hprod := laplaceChi_prod_integrable hm airyDerLaplace continuous_airyDerLaplace.measurable
    (fun v _ => airyDerLaplace_nonneg v) (fun r hr => integrableOn_airyDerLaplace_exp hr)
    (hMomN1.congr_fun (fun r (hr : 0 < r) => by
      change r ^ (N - 1) * airyDer_density r = _
      rw [hrp r hr, ← airyDer_normalizedU_re_eq hr, mul_assoc]
      rfl) measurableSet_Ioi)
  have hA := laplaceChi_kernel hm one_pos hX hsin
  have hB := laplaceChi_mixture hm hX hsin airyDerLaplace (fun v _ => airyDerLaplace_nonneg v) hprod
  -- integrability
  have hIntW : IntegrableOn (fun t : ℝ =>
      (airyDer_density t : ℂ) * (t : ℂ) ^ N / (X + t * exp (θ * I))) (Ioi 0) := by
    refine integrableOn_div_den ?_ hX hsin
    refine (hMomN.ofReal (𝕜 := ℂ)).congr_fun (fun t _ => ?_) measurableSet_Ioi
    change ((t ^ N * airyDer_density t : ℝ) : ℂ) = _
    push_cast; ring
  have hIntA : IntegrableOn (fun r : ℝ => (r : ℂ) ^ ((N : ℝ) : ℂ) *
      Complex.exp (-((1 : ℝ) * r)) / (X + r * exp (θ * I))) (Ioi 0) := by
    refine integrableOn_div_den ?_ hX hsin
    refine (hExpN.ofReal (𝕜 := ℂ)).congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [hNr, cpow_natCast]
    change ((t ^ N * Real.exp (-t) : ℝ) : ℂ) = _
    push_cast; ring_nf
  have hsplit : (∫ t in Ioi (0 : ℝ),
      (airyDer_density t : ℂ) * (t : ℂ) ^ N / (X + t * exp (θ * I))) =
      (∫ r in Ioi (0 : ℝ), (r : ℂ) ^ ((N : ℝ) : ℂ) *
        Complex.exp (-((1 : ℝ) * r)) / (X + r * exp (θ * I))) +
      ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ ((N : ℝ) : ℂ) *
        (∫ v in Ioi (0 : ℝ), (Real.exp (-((1 + v) * r)) * airyDerLaplace v : ℝ)) /
          (X + r * exp (θ * I)) := by
    rw [← integral_add hIntA]
    · refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
      rw [hNr, cpow_natCast, airyDer_density_eq ht, Complex.ofReal_add, Complex.ofReal_exp,
        Complex.ofReal_neg, Complex.ofReal_one, one_mul]
      ring
    · refine (hIntW.sub hIntA).congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply]
      rw [hNr, cpow_natCast, airyDer_density_eq ht, Complex.ofReal_add, Complex.ofReal_exp,
        Complex.ofReal_neg, Complex.ofReal_one, one_mul]
      ring
  have hmom : airyDerMoment (N - 1) = (∫ r in Ioi (0 : ℝ), r ^ ((N : ℝ) - 1) *
      Real.exp (-((1 : ℝ) * r))) + ∫ r in Ioi (0 : ℝ), r ^ ((N : ℝ) - 1) *
        ∫ v in Ioi (0 : ℝ), Real.exp (-((1 + v) * r)) * airyDerLaplace v := by
    have hm2 := (airyDer_density_moment (N - 1)).2
    simp only [airyDerMoment]
    rw [← hm2, ← integral_add]
    · refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
      rw [hrp t ht, airyDer_density_eq ht, one_mul]
      ring
    · exact hExpN1.congr_fun (fun t (ht : 0 < t) => by rw [hrp t ht]; ring_nf)
        measurableSet_Ioi
    · refine (hMomN1.sub hExpN1).congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply]
      rw [hrp t ht, hG t ht]
      ring
  change _ ≤ airySt_chi N * _
  rw [hsplit, hmom, mul_add]
  exact (norm_add_le _ _).trans (add_le_add hA hB)

/-- The Stieltjes moment integral `J_N(w) = ∫₀^∞ ρ(t) t^N/(t+w) dt`. -/
private noncomputable def airyDerJ (N : ℕ) (w : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (airyDer_density t : ℂ) * (t : ℂ) ^ N / ((t : ℂ) + w)

/-- `t ↦ ρ(t) t^N` is integrable on `(0, ∞)`. -/
private lemma integrableOn_airyDer_density_pow (N : ℕ) :
    IntegrableOn (fun t : ℝ => (airyDer_density t : ℂ) * (t : ℂ) ^ N) (Ioi 0) := by
  refine ((airyDer_density_moment N).1.ofReal (𝕜 := ℂ)).congr_fun (fun t _ => ?_)
    measurableSet_Ioi
  change ((t ^ N * airyDer_density t : ℝ) : ℂ) = _
  push_cast; ring

/-- `∫₀^∞ ρ(t) t^N dt = m_N`. -/
private lemma integral_airyDer_density_pow (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), (airyDer_density t : ℂ) * (t : ℂ) ^ N) = (airyDerMoment N : ℂ) := by
  rw [airyDerMoment, ← (airyDer_density_moment N).2, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast; ring

/-- `t + w ≠ 0` for `t > 0` and `w` in the slit plane. -/
private lemma ofReal_add_ne_zero {w : ℂ} (hw : w ∈ slitPlane) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) + w ≠ 0 := by
  intro h
  have hw' : w = ((-t : ℝ) : ℂ) := by push_cast; linear_combination h
  rw [hw'] at hw
  exact (ofReal_mem_slitPlane.not.mpr (by linarith)) hw

/-- `J_N(w) = m_N/w - J_{N+1}(w)/w`. -/
private lemma airyDerJ_succ {w : ℂ} (hw : w ∈ slitPlane) (N : ℕ) :
    airyDerJ N w = (airyDerMoment N : ℂ) / w - airyDerJ (N + 1) w / w := by
  have hw0 := slitPlane_ne_zero hw
  have h1 := airyDer_integrable_cauchy (integrableOn_airyDer_density_pow (N + 1)) hw
  have key : airyDerJ N w * w = (airyDerMoment N : ℂ) - airyDerJ (N + 1) w := by
    rw [airyDerJ, airyDerJ, ← integral_mul_const, ← integral_airyDer_density_pow,
      ← integral_sub (integrableOn_airyDer_density_pow N) h1]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    have := ofReal_add_ne_zero hw ht
    field_simp
    ring
  field_simp
  linear_combination key

/-- The exact remainder of the normalized derivative expansion. -/
private lemma airyDer_stieltjes_rem {w : ℂ} (hw : w ∈ slitPlane) (N : ℕ) :
    airyDer_normalizedU w - 1 - ∑ k ∈ Finset.range N,
        (1 / (2 * π) : ℂ) * (-1) ^ k * (airyDerMoment k : ℂ) / w ^ (k + 1) =
      (1 / (2 * π) : ℂ) * (-1) ^ N / w ^ N * airyDerJ N w := by
  have hw0 := slitPlane_ne_zero hw
  induction N with
  | zero =>
    rw [airyDer_stieltjes hw, airyDerJ]
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, div_one, mul_one, sub_zero]
    rw [add_sub_cancel_left]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [airyDer_density_coe ht]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih, airyDerJ_succ hw N]
    field_simp
    ring

/-- The moments `m_j` are positive. -/
private lemma airyDerMoment_pos (j : ℕ) : 0 < airyDerMoment j := by
  unfold airyDerMoment
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < j + 5 / 6 by positivity)
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < j + 13 / 6 by positivity)
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < j + 2 by positivity)
  positivity

/-- `‖J_N(X e^{iφ})‖ ≤ χ(N) m_{N-1}` when `sin φ ≠ 0`. -/
private lemma norm_airyDerJ_le {N : ℕ} (hN : 1 ≤ N) {X φ : ℝ} (hX : 0 < X)
    (hsin : Real.sin φ ≠ 0) :
    ‖airyDerJ N ((X : ℂ) * exp (φ * I))‖ ≤ airyChi N * airyDerMoment (N - 1) := by
  have hs : Real.sin (-φ) ≠ 0 := by rwa [Real.sin_neg, neg_ne_zero]
  have h := airyDer_J_bound hN hX hs
  have hJ : airyDerJ N ((X : ℂ) * exp (φ * I)) = exp (((-φ : ℝ) : ℂ) * I) *
      ∫ t in Ioi (0 : ℝ), (airyDer_density t : ℂ) * (t : ℂ) ^ N /
        (X + t * exp (((-φ : ℝ) : ℂ) * I)) := by
    rw [airyDerJ, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    have h1 : exp (((-φ : ℝ) : ℂ) * I) * exp (φ * I) = 1 := by
      rw [← exp_add]; push_cast; simp
    have h2 : (X : ℂ) + t * exp (((-φ : ℝ) : ℂ) * I) =
        exp (((-φ : ℝ) : ℂ) * I) * ((t : ℂ) + X * exp (φ * I)) := by
      linear_combination (-(X : ℂ)) * h1
    dsimp only
    rw [h2]
    have h3 : exp (((-φ : ℝ) : ℂ) * I) ≠ 0 := exp_ne_zero _
    by_cases h4 : (t : ℂ) + X * exp (φ * I) = 0
    · simp [h4]
    · field_simp
  rw [hJ, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact h

/-- The `χ + 1` bound for `Ai'` on `|arg z| < 2π/3`, `arg z ≠ 0`. -/
private lemma airyDer_aiDeriv_le_chi {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < 2 * π / 3)
    (hsin : Real.sin (3 * arg z / 2) ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N z‖ ≤ (airyChi (N + 0) + 1) *
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  set ℓ := log 2 + airyLogZeta z with hℓ
  set X : ℝ := Real.exp ℓ.re with hXdef
  set φ : ℝ := 3 / 2 * arg z with hφ
  have hX : 0 < X := Real.exp_pos _
  have hw : 2 * airyZetaComplex z = (X : ℂ) * exp (φ * I) := by
    rw [← exp_log_two_add_airyLogZeta hz, ← hℓ, hXdef, hφ, ← im_log_two_add_airyLogZeta z,
      ← hℓ, ofReal_exp, ← exp_add]
    congr 1
    exact (re_add_im ℓ).symm
  have hφlt : |φ| < π := by
    rw [hφ, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; linarith
  set w := 2 * airyZetaComplex z with hwdef
  have hws : w ∈ slitPlane := by
    rw [hw, mem_slitPlane_iff_arg, airyRot_arg hX (by linarith [abs_lt.mp hφlt])
      (by linarith [abs_lt.mp hφlt])]
    exact ⟨fun h => by rw [h, abs_of_pos hπ] at hφlt; linarith,
      mul_ne_zero (ofReal_ne_zero.mpr hX.ne') (exp_ne_zero _)⟩
  have hw0 : w ≠ 0 := slitPlane_ne_zero hws
  have hζ : airyZetaComplex z = w / 2 := by rw [hwdef]; ring
  have hc : ∀ j : ℕ, airyExpansionCoeff .aiDeriv (j + 1) / airyZetaComplex z ^ (j + 1) =
      (1 / (2 * π) : ℂ) * (-1) ^ j * (airyDerMoment j : ℂ) / w ^ (j + 1) := by
    intro j
    have hv := airyV_succ_mul_two_pow j
    have hv' : (airyV (j + 1) : ℂ) = -(1 / (2 * π)) * airyDerMoment j / 2 ^ (j + 1) := by
      rw [eq_div_iff (pow_ne_zero _ two_ne_zero)]
      exact_mod_cast hv
    rw [airyExpansionCoeff, hv', hζ, div_pow]
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr hπ.ne'
    field_simp
    ring
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hR : airyRemainder .aiDeriv (M + 1) z =
      (1 / (2 * π) : ℂ) * (-1) ^ (M + 1) / w ^ (M + 1) * airyDerJ (M + 1) w +
        airyExpansionCoeff .aiDeriv (M + 1) / airyZetaComplex z ^ (M + 1) := by
    rw [← airyDer_stieltjes_rem hws, hc M, Finset.sum_range_succ]
    simp only [airyRemainder, airyFunction, airyExponentialSum]
    rw [airyDer_normalizedU_eq hz harg, ← hwdef, Finset.sum_range_succ']
    simp only [hc]
    simp only [pow_zero, div_one, airyExpansionCoeff, airyReal_airyV_zero, ofReal_one,
      mul_one]
    ring
  have hT : ‖airyExpansionCoeff .aiDeriv (M + 1) / airyZetaComplex z ^ (M + 1)‖ =
      1 / (2 * π) * airyDerMoment M / X ^ (M + 1) := by
    rw [hc M, hw]
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
      norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg hX.le,
      Real.norm_of_nonneg (airyDerMoment_pos M).le]
    rw [Complex.norm_two, Real.norm_of_nonneg hπ.le]
  have hJ := norm_airyDerJ_le (N := M + 1) (by omega) hX
    (show Real.sin φ ≠ 0 by rwa [hφ, show 3 / 2 * arg z = 3 * arg z / 2 by ring])
  rw [← hw] at hJ
  simp only [Nat.add_sub_cancel] at hJ
  rw [hR, hT]
  have hrem : ‖(1 / (2 * π) : ℂ) * (-1) ^ (M + 1) / w ^ (M + 1) * airyDerJ (M + 1) w‖ ≤
      airyChi ((M + 1 : ℕ) : ℝ) * (1 / (2 * π) * airyDerMoment M / X ^ (M + 1)) := by
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, mul_one,
      hw, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hX.le, ← hw]
    have h2π : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real,
        Real.norm_of_nonneg hπ.le]
    rw [h2π]
    have hXp : 0 < X ^ (M + 1) := pow_pos hX _
    calc 1 / (2 * π) / X ^ (M + 1) * ‖airyDerJ (M + 1) w‖
        ≤ 1 / (2 * π) / X ^ (M + 1) * (airyChi ((M + 1 : ℕ) : ℝ) * airyDerMoment M) :=
          mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = _ := by ring
  rw [add_zero]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ airyChi ((M + 1 : ℕ) : ℝ) * (1 / (2 * π) * airyDerMoment M / X ^ (M + 1)) +
        ‖airyExpansionCoeff .aiDeriv (M + 1) / airyZetaComplex z ^ (M + 1)‖ :=
          add_le_add hrem le_rfl
    _ = _ := by rw [hT]; ring

/-- The normalized `Ai'` remainder is continuous on the slit plane. -/
private lemma continuousAt_airyRemainder_aiDeriv {w : ℂ} (hw : w ∈ slitPlane) (N : ℕ) :
    ContinuousAt (airyRemainder .aiDeriv N) w := by
  have hw0 := slitPlane_ne_zero hw
  have hz := (airyRot_differentiableAt_zeta hw).continuousAt
  have hq : ContinuousAt (fun w : ℂ => w ^ (1 / 4 : ℂ)) w := continuousAt_cpow_const hw
  have hp : ContinuousAt (airyPrefactor .aiDeriv) w := by
    have he : airyPrefactor .aiDeriv =
        fun w => -w ^ (1 / 4 : ℂ) * exp (-airyZetaComplex w) / (2 * Real.sqrt π) := by
      funext w; rfl
    rw [he]
    exact (hq.neg.mul hz.neg.cexp).div continuousAt_const
      (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'))
  have hs : ContinuousAt (airyExponentialSum .aiDeriv N) w := by
    unfold airyExponentialSum
    exact tendsto_finsetSum _ fun k _ => continuousAt_const.div (hz.pow k)
      (pow_ne_zero _ (airySt_zeta_ne_zero hw0))
  unfold airyRemainder airyFunction
  exact ((hasDerivAt_airyAiDeriv w).continuousAt.div hp
    (airyRot_prefactor_ne_zero .aiDeriv hw0)).sub hs

/-- The `χ + 1` bound for `Ai'` on the rays `|arg z| = 2π/3`, by continuity. -/
private lemma airyDer_aiDeriv_boundary {z : ℂ} (hz : z ≠ 0) (harg : |arg z| = 2 * π / 3)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N z‖ ≤ (airyChi (N + 0) + 1) *
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  set p : ℝ → ℂ := fun φ => (‖z‖ : ℂ) * exp (φ * I) with hp
  have hpz : p (arg z) = z := norm_mul_exp_arg_mul_I z
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpc : Continuous p := by fun_prop
  have hzs : z ∈ slitPlane := by
    rw [mem_slitPlane_iff_arg]; refine ⟨fun h => ?_, hz⟩; rw [h, abs_of_pos hπ] at harg; linarith
  have hT : ContinuousAt (fun w => airyExpansionCoeff .aiDeriv N / airyZetaComplex w ^ N) z :=
    continuousAt_const.div ((airyRot_differentiableAt_zeta hzs).continuousAt.pow N)
      (pow_ne_zero _ (airySt_zeta_ne_zero hz))
  have hg := ((continuousAt_airyRemainder_aiDeriv (hpz ▸ hzs) N).comp hpc.continuousAt).norm
  have hh := (((hpz ▸ hT).comp hpc.continuousAt).norm).const_mul (airyChi (N + 0) + 1)
  have hb : ∀ φ : ℝ, π / 3 < |φ| → |φ| < 2 * π / 3 →
      ‖airyRemainder .aiDeriv N (p φ)‖ ≤ (airyChi (N + 0) + 1) *
        ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex (p φ) ^ N‖ := by
    intro φ h1 h2
    have hφ : arg (p φ) = φ := airyRot_arg hr (by linarith [neg_abs_le φ])
      (by linarith [le_abs_self φ])
    have hp0 : p φ ≠ 0 := airyRot_ofReal_mul_exp_ne_zero hr φ
    exact airyDer_aiDeriv_le_chi hp0 (by rw [hφ]; exact h2)
      (by rw [hφ]; exact airySt_sin_ne_zero h1 h2) hN
  rw [← hpz]
  rcases le_or_gt 0 (arg z) with h0 | h0
  · rw [abs_of_nonneg h0] at harg
    have hev : ∀ᶠ φ in 𝓝[<] (arg z), φ ∈ Ioo (π / 3) (2 * π / 3) := by
      rw [harg]; exact Ioo_mem_nhdsLT (by linarith)
    refine le_of_tendsto_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds)
      (hh.tendsto.mono_left nhdsWithin_le_nhds) (hev.mono fun φ hφ => ?_)
    have : 0 < φ := by linarith [hφ.1]
    exact hb φ (by rw [abs_of_pos this]; exact hφ.1) (by rw [abs_of_pos this]; exact hφ.2)
  · rw [abs_of_neg h0] at harg
    have hev : ∀ᶠ φ in 𝓝[>] (arg z), φ ∈ Ioo (-(2 * π / 3)) (-(π / 3)) := by
      rw [show arg z = -(2 * π / 3) by linarith]; exact Ioo_mem_nhdsGT (by linarith)
    refine le_of_tendsto_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds)
      (hh.tendsto.mono_left nhdsWithin_le_nhds) (hev.mono fun φ hφ => ?_)
    have : φ < 0 := by linarith [hφ.2]
    exact hb φ (by rw [abs_of_neg this]; linarith [hφ.2]) (by rw [abs_of_neg this]; linarith [hφ.1])

/-- `Bi'(z) = e^{-πi/6} ω̄ Ai'(z ω̄) + e^{πi/6} ω Ai'(z ω)`, the derivative of DLMF 9.2.10. -/
private lemma airyBiDeriv_eq_airyAiDeriv_omega (z : ℂ) :
    airyBiDeriv z = exp (-(π * I / 6)) * (exp (-(2 * π * I / 3)) *
        airyAiDeriv (z * exp (-(2 * π * I / 3)))) +
      exp (π * I / 6) * (exp (2 * π * I / 3) * airyAiDeriv (z * exp (2 * π * I / 3))) := by
  have hf : airyBi = fun z => exp (-(π * I / 6)) * airyAi (z * exp (-(2 * π * I / 3))) +
      exp (π * I / 6) * airyAi (z * exp (2 * π * I / 3)) := funext airyBi_eq_airyAi_omega
  have h1 := ((hasDerivAt_airyAi (z * exp (-(2 * π * I / 3)))).comp z
    ((hasDerivAt_id z).mul_const (exp (-(2 * π * I / 3))))).const_mul (exp (-(π * I / 6)))
  have h2 := ((hasDerivAt_airyAi (z * exp (2 * π * I / 3))).comp z
    ((hasDerivAt_id z).mul_const (exp (2 * π * I / 3)))).const_mul (exp (π * I / 6))
  have h := h1.add h2
  refine (hasDerivAt_airyBi z).unique ?_
  convert h using 1
  · rw [hf]; rfl
  · ring

/-- **The Bi' remainder through 9.2.10**. -/
private lemma airyDer_biDeriv_rem {x : ℝ} (hx : 0 < x) (N : ℕ) :
    airyRemainder .biDeriv N x =
      (airyRemainder .aiDeriv N ((x : ℂ) * exp (((1 * (2 * π / 3)) : ℝ) * I)) +
        airyRemainder .aiDeriv N ((x : ℂ) * exp ((((-1) * (2 * π / 3)) : ℝ) * I))) / 2 := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hz1 := airyRot_zeta_rot hx0 harg (Or.inl rfl)
  have hz2 := airyRot_zeta_rot hx0 harg (Or.inr rfl)
  have hq1 := airyRot_quarter_rot hx0 harg (Or.inl rfl)
  have hq2 := airyRot_quarter_rot hx0 harg (Or.inr rfl)
  have hB := airyBiDeriv_eq_airyAiDeriv_omega (x : ℂ)
  have e1 : exp (2 * π * I / 3) = exp (((1 * (2 * π / 3)) : ℝ) * I) := by congr 1; push_cast; ring
  have e2 : exp (-(2 * π * I / 3)) = exp ((((-1) * (2 * π / 3)) : ℝ) * I) := by
    congr 1; push_cast; ring
  set E := exp (((1 * (π / 6)) : ℝ) * I) with hE
  have e3 : exp (π * I / 6) = E := by rw [hE]; congr 1; push_cast; ring
  have e4 : exp (-(π * I / 6)) = E⁻¹ := by rw [hE, ← exp_neg]; congr 1; push_cast; ring
  have e5 : exp ((((-1) * (π / 6)) : ℝ) * I) = E⁻¹ := by
    rw [hE, ← exp_neg]; congr 1; push_cast; ring
  have e6 : exp (((1 * (2 * π / 3)) : ℝ) * I) = E ^ 4 := by
    rw [hE, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e7 : exp ((((-1) * (2 * π / 3)) : ℝ) * I) = (E ^ 4)⁻¹ := by
    rw [hE, ← Complex.exp_nat_mul, ← exp_neg]; congr 1; push_cast; ring
  rw [e1, e2, e3, e4] at hB
  rw [e5] at hq2
  have hE0 : E ≠ 0 := exp_ne_zero _
  have hS : ∀ w : ℂ, airyZetaComplex w = -airyZetaComplex (x : ℂ) →
      airyExponentialSum .aiDeriv N w = airyExponentialSum .biDeriv N x := by
    intro w hw
    unfold airyExponentialSum
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hw, airyExpansionCoeff, airyExpansionCoeff,
      neg_eq_neg_one_mul (airyZetaComplex (x : ℂ)), mul_pow]
    have : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : airyZetaComplex (x : ℂ) ^ k ≠ 0 := pow_ne_zero _ (airySt_zeta_ne_zero hx0)
    field_simp
  simp only [airyRemainder, airyFunction]
  rw [hS _ hz1, hS _ hz2, hB]
  simp only [airyPrefactor, hz1, hz2, hq1, hq2, neg_neg]
  generalize airyAiDeriv ((x : ℂ) * exp (((1 * (2 * π / 3)) : ℝ) * I)) = A1
  generalize airyAiDeriv ((x : ℂ) * exp ((((-1) * (2 * π / 3)) : ℝ) * I)) = A2
  rw [e6, e7]
  have hX0 : exp (airyZetaComplex (x : ℂ)) ≠ 0 := exp_ne_zero _
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : (x : ℂ) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hE6 : E ^ 6 = -1 := by
    rw [hE, ← Complex.exp_nat_mul, show ((6 : ℕ) : ℂ) * (((1 * (π / 6)) : ℝ) * I) = π * I by
      push_cast; ring, exp_pi_mul_I]
  field_simp
  linear_combination (2 * (Real.sqrt π : ℂ) * (A2 + E ^ 4 * A1)) * hE6

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_biDeriv_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .biDeriv N x‖ ≤ (airyChi (N + 0) + 1) *
      ‖airyExpansionCoeff .biDeriv N / airyZetaComplex x ^ N‖ := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hT : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ‖airyRemainder .aiDeriv N ((x : ℂ) * exp (((ε * (2 * π / 3)) : ℝ) * I))‖ ≤
        (airyChi (N + 0) + 1) * ‖airyExpansionCoeff .biDeriv N / airyZetaComplex x ^ N‖ := by
    intro ε hε
    have hw0 : (x : ℂ) * exp (((ε * (2 * π / 3)) : ℝ) * I) ≠ 0 :=
      airyRot_ofReal_mul_exp_ne_zero hx _
    have hwa : |arg ((x : ℂ) * exp (((ε * (2 * π / 3)) : ℝ) * I))| = 2 * π / 3 := by
      have hπ := Real.pi_pos
      rcases hε with rfl | rfl
      · rw [airyRot_arg hx (by linarith) (by linarith), one_mul, abs_of_pos (by positivity)]
      · rw [airyRot_arg hx (by linarith) (by linarith), abs_of_neg (by linarith)]; ring
    have h := airyDer_aiDeriv_boundary hw0 hwa hN
    rw [airyRot_zeta_rot hx0 harg hε] at h
    convert h using 2
    simp only [airyExpansionCoeff, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
  rw [airyDer_biDeriv_rem hx N]
  calc _ ≤ (‖airyRemainder .aiDeriv N ((x : ℂ) * exp (((1 * (2 * π / 3)) : ℝ) * I))‖ +
        ‖airyRemainder .aiDeriv N ((x : ℂ) * exp ((((-1) * (2 * π / 3)) : ℝ) * I))‖) / 2 := by
        rw [norm_div, Complex.norm_two]; gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith [hT 1 (Or.inl rfl), hT (-1) (Or.inr rfl)]

end DLMF.Airy

end
