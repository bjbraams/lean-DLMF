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
The same representation gives the multipliers `1` on `|arg z| ≤ π/3` and `|csc(3 arg z/2)|` on
`|arg z| < 2π/3`; on `2π/3 < |arg z| < π` the derivative of the connection formula 9.2.12 and
the numerical inequality `e^{-2s}(s^N + (7/72)s^{N-1}) ≤ √(2πN)|v_N|` give the last sector.

## Main results

* `airyAiDeriv_complex_error`: the remainder bound of DLMF 9.7.17 for `Ai'` on the slit plane,
  `N ≥ 1`.
* `airyBiDeriv_real_error`: `|R^{Bi'}_N(x)| ≤ (χ(N) + 1) |v_N ζ^{-N}|` for `x > 0`, `N ≥ 1`
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
    simp only [zero_add, pow_one, RealRemainders.airyV_one, airyDerMoment, Nat.cast_zero]
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
private lemma continuousOn_airyDer_density : ContinuousOn DerivativeRemainders.density (Ioi 0) := by
  intro t ht
  have ht' : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 ht
  have hU : ContinuousAt (fun t : ℝ => DerivativeRemainders.normalizedU t) t := by
    unfold DerivativeRemainders.normalizedU
    exact ((continuousAt_cpow_const ht').comp continuous_ofReal.continuousAt).mul
      ((differentiableAt_kummerU _ _ ht').continuousAt.comp continuous_ofReal.continuousAt)
  exact ((Real.continuous_exp.comp continuous_neg).continuousAt.mul
    (Complex.continuous_re.continuousAt.comp hU)).continuousWithinAt

/-- The density `ρ` is integrable on `(0, ∞)`. -/
private lemma integrableOn_airyDer_density : IntegrableOn DerivativeRemainders.density (Ioi 0) := by
  simpa using (DerivativeRemainders.density_moment 0).1

/-- The density `ρ` is a.e. strongly measurable on `(0, ∞)`. -/
private lemma aestronglyMeasurable_airyDer_density :
    AEStronglyMeasurable DerivativeRemainders.density (volume.restrict (Ioi 0)) :=
  continuousOn_airyDer_density.aestronglyMeasurable measurableSet_Ioi

/-- The Laplace density `g(v) = (2π)⁻¹ ∫₀^∞ ρ(s) e^{-sv} ds`, continued as `g(0)` for `v ≤ 0`. -/
private noncomputable def airyDerLaplace (v : ℝ) : ℝ :=
  1 / (2 * π) * ∫ s in Ioi (0 : ℝ), DerivativeRemainders.density s * Real.exp (-(s * max v 0))

/-- The Laplace density `g` is continuous. -/
private lemma continuous_airyDerLaplace : Continuous airyDerLaplace := by
  refine continuous_const.mul (continuous_of_dominated (bound := DerivativeRemainders.density) ?_ ?_
    integrableOn_airyDer_density ?_)
  · intro v
    exact aestronglyMeasurable_airyDer_density.mul (by fun_prop : Continuous fun s : ℝ =>
      Real.exp (-(s * max v 0))).aestronglyMeasurable
  · intro v
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (DerivativeRemainders.density_nonneg hs),
      abs_of_pos (Real.exp_pos _)]
    refine mul_le_of_le_one_right (DerivativeRemainders.density_nonneg hs)
        (Real.exp_le_one_iff.mpr ?_)
    have := mul_nonneg hs.le (le_max_right v 0)
    linarith
  · exact ae_of_all _ fun s => by fun_prop

/-- The Laplace density `g` is nonnegative. -/
private lemma airyDerLaplace_nonneg (v : ℝ) : 0 ≤ airyDerLaplace v := by
  unfold airyDerLaplace
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun s hs => ?_)
  exact mul_nonneg (DerivativeRemainders.density_nonneg hs) (Real.exp_pos _).le

/-- The Laplace density `g` is bounded by `(1/2π)∫ρ`. -/
private lemma airyDerLaplace_le (v : ℝ) :
    airyDerLaplace v ≤ 1 / (2 * π) * ∫ s in Ioi (0 : ℝ), DerivativeRemainders.density s := by
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
  · refine mul_le_of_le_one_right (DerivativeRemainders.density_nonneg hs)
        (Real.exp_le_one_iff.mpr ?_)
    have := mul_nonneg (le_of_lt hs) (le_max_right v 0)
    linarith

/-- `Re F(r) = 1 + ∫₀^∞ e^{-vr} g(v) dv` for `r > 0`. -/
private lemma DerivativeRemainders.normalizedU_re_eq {r : ℝ} (hr : 0 < r) :
    (DerivativeRemainders.normalizedU r).re =
      1 + ∫ v in Ioi (0 : ℝ), Real.exp (-(v * r)) * airyDerLaplace v := by
  have hS := DerivativeRemainders.stieltjes (ofReal_mem_slitPlane.2 hr)
  have hI : (∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * DerivativeRemainders.normalizedU t /
      ((t : ℂ) + r)) =
      ((∫ t in Ioi (0 : ℝ), DerivativeRemainders.density t / (t + r) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [← DerivativeRemainders.density_coe ht]
    push_cast; rfl
  rw [hI] at hS
  have hre := congrArg Complex.re hS
  rw [show (1 : ℂ) / (2 * π : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; rfl, ← ofReal_mul,
    add_re, one_re, ofReal_re] at hre
  rw [hre]
  congr 1
  -- Tonelli
  set f : ℝ → ℝ → ℝ := fun v s => DerivativeRemainders.density s * Real.exp (-((s + r) * v)) with hf
  have hinner : ∀ s, 0 < s → ∫ v in Ioi (0 : ℝ), f v s =
      DerivativeRemainders.density s / (s + r) := by
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
        ∫ v in Ioi (0 : ℝ), ‖Function.uncurry f (v, s)‖ =
            DerivativeRemainders.density s / (s + r) := by
      intro s hs
      rw [← hinner s hs]
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
      simp only [Function.uncurry, hf]
      exact Real.norm_of_nonneg
          (mul_nonneg (DerivativeRemainders.density_nonneg hs) (Real.exp_pos _).le)
    refine (integrable_prod_iff' hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
      exact IntegrableOn.congr_fun ((exp_neg_integrableOn_Ioi 0
        (show 0 < s + r by linarith)).const_mul (DerivativeRemainders.density s))
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
        show _ ≤ DerivativeRemainders.density s / r
        exact div_le_div_of_nonneg_left (DerivativeRemainders.density_nonneg hs) hr (by linarith)
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
private lemma DerivativeRemainders.density_eq {t : ℝ} (ht : 0 < t) :
    DerivativeRemainders.density t = Real.exp (-t) +
      ∫ v in Ioi (0 : ℝ), Real.exp (-((1 + v) * t)) * airyDerLaplace v := by
  rw [DerivativeRemainders.density, DerivativeRemainders.normalizedU_re_eq ht, mul_add, mul_one,
      ← integral_const_mul]
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
  set C := 1 / (2 * π) * ∫ s in Ioi (0 : ℝ), DerivativeRemainders.density s
  refine ((exp_neg_integrableOn_Ioi 0 hr).mul_const C).mono' ?_ (ae_of_all _ fun v => ?_)
  · exact (by fun_prop : Continuous fun v : ℝ => Real.exp (-(v * r))).aestronglyMeasurable.mul
      continuous_airyDerLaplace.aestronglyMeasurable
  · rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (airyDerLaplace_nonneg v), show -r * v = -(v * r) by ring]
    exact mul_le_mul_of_nonneg_left (airyDerLaplace_le v) (Real.exp_pos _).le

/-- The χ bound for the Stieltjes moments of the derivative density. -/
private lemma DerivativeRemainders.J_bound {N : ℕ} (hN : 1 ≤ N) {X θ : ℝ} (hX : 0 < X)
    (hsin : Real.sin θ ≠ 0) :
    ‖∫ t in Ioi (0 : ℝ), (DerivativeRemainders.density t : ℂ) * (t : ℂ) ^ N /
        (X + t * exp (θ * I))‖ ≤
      airyChi N * airyDerMoment (N - 1) := by
  have hm : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr : ((N : ℝ) : ℂ) = (N : ℂ) := by push_cast; rfl
  have hrp : ∀ r : ℝ, 0 < r → r ^ ((N : ℝ) - 1) = r ^ (N - 1) := by
    intro r hr
    rw [← Real.rpow_natCast, Nat.cast_sub hN, Nat.cast_one]
  -- the two Laplace pieces
  have hG : ∀ r : ℝ, 0 < r → (∫ v in Ioi (0 : ℝ), Real.exp (-((1 + v) * r)) * airyDerLaplace v) =
      DerivativeRemainders.density r - Real.exp (-r) := fun r hr => by
          rw [DerivativeRemainders.density_eq hr]; ring
  have hMomN := (DerivativeRemainders.density_moment N).1
  have hMomN1 := (DerivativeRemainders.density_moment (N - 1)).1
  have hExpN : IntegrableOn (fun r : ℝ => r ^ N * Real.exp (-r)) (Ioi 0) := by
    simpa using StieltjesRemainder.integrableOn_rpow_exp (m := (N : ℝ)) (by linarith) one_pos
  have hExpN1 : IntegrableOn (fun r : ℝ => r ^ (N - 1) * Real.exp (-r)) (Ioi 0) := by
    have := StieltjesRemainder.integrableOn_rpow_exp (m := ((N - 1 : ℕ) : ℝ))
      (by have := (N - 1 : ℕ).cast_nonneg (α := ℝ); linarith) one_pos
    simpa using this
  have hprod := laplaceChi_prod_integrable hm airyDerLaplace continuous_airyDerLaplace.measurable
    (fun v _ => airyDerLaplace_nonneg v) (fun r hr => integrableOn_airyDerLaplace_exp hr)
    (hMomN1.congr_fun (fun r (hr : 0 < r) => by
      change r ^ (N - 1) * DerivativeRemainders.density r = _
      rw [hrp r hr, ← DerivativeRemainders.normalizedU_re_eq hr, mul_assoc]
      rfl) measurableSet_Ioi)
  have hA := laplaceChi_kernel hm one_pos hX hsin
  have hB := laplaceChi_mixture hm hX hsin airyDerLaplace (fun v _ => airyDerLaplace_nonneg v) hprod
  -- integrability
  have hIntW : IntegrableOn (fun t : ℝ =>
      (DerivativeRemainders.density t : ℂ) * (t : ℂ) ^ N / (X + t * exp (θ * I))) (Ioi 0) := by
    refine integrableOn_div_den ?_ hX hsin
    refine (hMomN.ofReal (𝕜 := ℂ)).congr_fun (fun t _ => ?_) measurableSet_Ioi
    change ((t ^ N * DerivativeRemainders.density t : ℝ) : ℂ) = _
    push_cast; ring
  have hIntA : IntegrableOn (fun r : ℝ => (r : ℂ) ^ ((N : ℝ) : ℂ) *
      Complex.exp (-((1 : ℝ) * r)) / (X + r * exp (θ * I))) (Ioi 0) := by
    refine integrableOn_div_den ?_ hX hsin
    refine (hExpN.ofReal (𝕜 := ℂ)).congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [hNr, cpow_natCast]
    change ((t ^ N * Real.exp (-t) : ℝ) : ℂ) = _
    push_cast; ring_nf
  have hsplit : (∫ t in Ioi (0 : ℝ),
      (DerivativeRemainders.density t : ℂ) * (t : ℂ) ^ N / (X + t * exp (θ * I))) =
      (∫ r in Ioi (0 : ℝ), (r : ℂ) ^ ((N : ℝ) : ℂ) *
        Complex.exp (-((1 : ℝ) * r)) / (X + r * exp (θ * I))) +
      ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ ((N : ℝ) : ℂ) *
        (∫ v in Ioi (0 : ℝ), (Real.exp (-((1 + v) * r)) * airyDerLaplace v : ℝ)) /
          (X + r * exp (θ * I)) := by
    rw [← integral_add hIntA]
    · refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
      rw [hNr, cpow_natCast, DerivativeRemainders.density_eq ht, Complex.ofReal_add,
          Complex.ofReal_exp,
        Complex.ofReal_neg, Complex.ofReal_one, one_mul]
      ring
    · refine (hIntW.sub hIntA).congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply]
      rw [hNr, cpow_natCast, DerivativeRemainders.density_eq ht, Complex.ofReal_add,
          Complex.ofReal_exp,
        Complex.ofReal_neg, Complex.ofReal_one, one_mul]
      ring
  have hmom : airyDerMoment (N - 1) = (∫ r in Ioi (0 : ℝ), r ^ ((N : ℝ) - 1) *
      Real.exp (-((1 : ℝ) * r))) + ∫ r in Ioi (0 : ℝ), r ^ ((N : ℝ) - 1) *
        ∫ v in Ioi (0 : ℝ), Real.exp (-((1 + v) * r)) * airyDerLaplace v := by
    have hm2 := (DerivativeRemainders.density_moment (N - 1)).2
    simp only [airyDerMoment]
    rw [← hm2, ← integral_add]
    · refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
      rw [hrp t ht, DerivativeRemainders.density_eq ht, one_mul]
      ring
    · exact hExpN1.congr_fun (fun t (ht : 0 < t) => by rw [hrp t ht]; ring_nf)
        measurableSet_Ioi
    · refine (hMomN1.sub hExpN1).congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply]
      rw [hrp t ht, hG t ht]
      ring
  change _ ≤ StieltjesBounds.chi N * _
  rw [hsplit, hmom, mul_add]
  exact (norm_add_le _ _).trans (add_le_add hA hB)

/-- The Stieltjes moment integral `J_N(w) = ∫₀^∞ ρ(t) t^N/(t+w) dt`. -/
private noncomputable def airyDerJ (N : ℕ) (w : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (DerivativeRemainders.density t : ℂ) * (t : ℂ) ^ N / ((t : ℂ) + w)

/-- `t ↦ ρ(t) t^N` is integrable on `(0, ∞)`. -/
private lemma integrableOn_airyDer_density_pow (N : ℕ) :
    IntegrableOn (fun t : ℝ => (DerivativeRemainders.density t : ℂ) * (t : ℂ) ^ N) (Ioi 0) := by
  refine ((DerivativeRemainders.density_moment N).1.ofReal (𝕜 := ℂ)).congr_fun (fun t _ => ?_)
    measurableSet_Ioi
  change ((t ^ N * DerivativeRemainders.density t : ℝ) : ℂ) = _
  push_cast; ring

/-- `∫₀^∞ ρ(t) t^N dt = m_N`. -/
private lemma integral_airyDer_density_pow (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), (DerivativeRemainders.density t : ℂ) * (t : ℂ) ^ N) =
        (airyDerMoment N : ℂ) := by
  rw [airyDerMoment, ← (DerivativeRemainders.density_moment N).2, ← integral_complex_ofReal]
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
  have h1 := DerivativeRemainders.integrable_cauchy (integrableOn_airyDer_density_pow (N + 1)) hw
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
private lemma DerivativeRemainders.stieltjes_remainder {w : ℂ} (hw : w ∈ slitPlane) (N : ℕ) :
    DerivativeRemainders.normalizedU w - 1 - ∑ k ∈ Finset.range N,
        (1 / (2 * π) : ℂ) * (-1) ^ k * (airyDerMoment k : ℂ) / w ^ (k + 1) =
      (1 / (2 * π) : ℂ) * (-1) ^ N / w ^ N * airyDerJ N w := by
  have hw0 := slitPlane_ne_zero hw
  induction N with
  | zero =>
    rw [DerivativeRemainders.stieltjes hw, airyDerJ]
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, div_one, mul_one, sub_zero]
    rw [add_sub_cancel_left]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [DerivativeRemainders.density_coe ht]
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
  have h := DerivativeRemainders.J_bound hN hX hs
  have hJ : airyDerJ N ((X : ℂ) * exp (φ * I)) = exp (((-φ : ℝ) : ℂ) * I) *
      ∫ t in Ioi (0 : ℝ), (DerivativeRemainders.density t : ℂ) * (t : ℂ) ^ N /
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
private lemma DerivativeRemainders.aiDeriv_le_chi {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < 2 * π / 3)
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
    rw [hw, mem_slitPlane_iff_arg,
        RotatedExpansions.arg_ofReal_mul_exp hX (by linarith [abs_lt.mp hφlt])
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
    rw [← DerivativeRemainders.stieltjes_remainder hws, hc M, Finset.sum_range_succ]
    simp only [airyRemainder, airyFunction, airyExponentialSum]
    rw [DerivativeRemainders.normalizedU_eq hz harg, ← hwdef, Finset.sum_range_succ']
    simp only [hc]
    simp only [pow_zero, div_one, airyExpansionCoeff, RealRemainders.airyV_zero, ofReal_one,
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
  have hz := (RotatedExpansions.differentiableAt_zeta hw).continuousAt
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
      (pow_ne_zero _ (StieltjesBounds.zeta_ne_zero hw0))
  unfold airyRemainder airyFunction
  exact ((hasDerivAt_airyAiDeriv w).continuousAt.div hp
    (RotatedExpansions.prefactor_ne_zero .aiDeriv hw0)).sub hs

/-- The `χ + 1` bound for `Ai'` on the rays `|arg z| = 2π/3`, by continuity. -/
private lemma DerivativeRemainders.aiDeriv_boundary {z : ℂ} (hz : z ≠ 0)
    (harg : |arg z| = 2 * π / 3)
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
    continuousAt_const.div ((RotatedExpansions.differentiableAt_zeta hzs).continuousAt.pow N)
      (pow_ne_zero _ (StieltjesBounds.zeta_ne_zero hz))
  have hg := ((continuousAt_airyRemainder_aiDeriv (hpz ▸ hzs) N).comp hpc.continuousAt).norm
  have hh := (((hpz ▸ hT).comp hpc.continuousAt).norm).const_mul (airyChi (N + 0) + 1)
  have hb : ∀ φ : ℝ, π / 3 < |φ| → |φ| < 2 * π / 3 →
      ‖airyRemainder .aiDeriv N (p φ)‖ ≤ (airyChi (N + 0) + 1) *
        ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex (p φ) ^ N‖ := by
    intro φ h1 h2
    have hφ : arg (p φ) = φ := RotatedExpansions.arg_ofReal_mul_exp hr (by linarith [neg_abs_le φ])
      (by linarith [le_abs_self φ])
    have hp0 : p φ ≠ 0 := RotatedExpansions.ofReal_mul_exp_ne_zero hr φ
    exact DerivativeRemainders.aiDeriv_le_chi hp0 (by rw [hφ]; exact h2)
      (by rw [hφ]; exact StieltjesBounds.sin_ne_zero h1 h2) hN
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
private lemma DerivativeRemainders.biDeriv_remainder {x : ℝ} (hx : 0 < x) (N : ℕ) :
    airyRemainder .biDeriv N x =
      (airyRemainder .aiDeriv N ((x : ℂ) * exp (((1 * (2 * π / 3)) : ℝ) * I)) +
        airyRemainder .aiDeriv N ((x : ℂ) * exp ((((-1) * (2 * π / 3)) : ℝ) * I))) / 2 := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hz1 := RotatedExpansions.zeta_rotation hx0 harg (Or.inl rfl)
  have hz2 := RotatedExpansions.zeta_rotation hx0 harg (Or.inr rfl)
  have hq1 := RotatedExpansions.quarter_rotation hx0 harg (Or.inl rfl)
  have hq2 := RotatedExpansions.quarter_rotation hx0 harg (Or.inr rfl)
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
    have h2 : airyZetaComplex (x : ℂ) ^ k ≠ 0 := pow_ne_zero _ (StieltjesBounds.zeta_ne_zero hx0)
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
theorem airyBiDeriv_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
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
      RotatedExpansions.ofReal_mul_exp_ne_zero hx _
    have hwa : |arg ((x : ℂ) * exp (((ε * (2 * π / 3)) : ℝ) * I))| = 2 * π / 3 := by
      have hπ := Real.pi_pos
      rcases hε with rfl | rfl
      · rw [RotatedExpansions.arg_ofReal_mul_exp hx (by linarith) (by linarith), one_mul,
            abs_of_pos (by positivity)]
      · rw [RotatedExpansions.arg_ofReal_mul_exp hx (by linarith) (by linarith),
            abs_of_neg (by linarith)]; ring
    have h := DerivativeRemainders.aiDeriv_boundary hw0 hwa hN
    rw [RotatedExpansions.zeta_rotation hx0 harg hε] at h
    convert h using 2
    simp only [airyExpansionCoeff, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
  rw [DerivativeRemainders.biDeriv_remainder hx N]
  calc _ ≤ (‖airyRemainder .aiDeriv N ((x : ℂ) * exp (((1 * (2 * π / 3)) : ℝ) * I))‖ +
        ‖airyRemainder .aiDeriv N ((x : ℂ) * exp ((((-1) * (2 * π / 3)) : ℝ) * I))‖) / 2 := by
        rw [norm_div, Complex.norm_two]; gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith [hT 1 (Or.inl rfl), hT (-1) (Or.inr rfl)]

/-! ### DLMF 9.7.17 for `Ai'`

On `|arg z| < 2π/3` the remainder is `R_N = (2π)⁻¹ (-1)^{N-1} w^{1-N} J_{N-1}(w)`, `w = 2ζ`; a
lower bound `|t + w| ≥ s |w|` on `t > 0` gives `|R_N| ≤ s⁻¹ |T_N|`, with `s = 1` for
`|arg w| ≤ π/2` and `s = |sin(arg w)|` otherwise. In the last sector the derivative of the
connection formula 9.2.12 reduces the bound to the second sector and to
`|F(u)| ≤ 1 + |v₁|/|ζ(u)|`. -/

/-- `w = 2ζ(z)` in polar form, with the expansion coefficients as Stieltjes moments. -/
private lemma DerivativeRemainders.polar {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < 2 * π / 3) :
    2 * airyZetaComplex z = ((Real.exp (log 2 + airyLogZeta z).re : ℝ) : ℂ) *
        exp (((3 / 2 * arg z : ℝ) : ℂ) * I) ∧ 2 * airyZetaComplex z ∈ slitPlane ∧
      ∀ j : ℕ, airyExpansionCoeff .aiDeriv (j + 1) / airyZetaComplex z ^ (j + 1) =
        (1 / (2 * π) : ℂ) * (-1) ^ j * (airyDerMoment j : ℂ) / (2 * airyZetaComplex z) ^ (j + 1)
          := by
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
  have hws : 2 * airyZetaComplex z ∈ slitPlane := by
    rw [hw, mem_slitPlane_iff_arg,
        RotatedExpansions.arg_ofReal_mul_exp hX (by linarith [abs_lt.mp hφlt])
      (by linarith [abs_lt.mp hφlt])]
    exact ⟨fun h => by rw [h, abs_of_pos hπ] at hφlt; linarith,
      mul_ne_zero (ofReal_ne_zero.mpr hX.ne') (exp_ne_zero _)⟩
  refine ⟨hw, hws, fun j => ?_⟩
  have hv := airyV_succ_mul_two_pow j
  have hv' : (airyV (j + 1) : ℂ) = -(1 / (2 * π)) * airyDerMoment j / 2 ^ (j + 1) := by
    rw [eq_div_iff (pow_ne_zero _ two_ne_zero)]
    exact_mod_cast hv
  have hζ : airyZetaComplex z = (2 * airyZetaComplex z) / 2 := by ring
  rw [airyExpansionCoeff, hv', hζ, div_pow]
  have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr hπ.ne'
  have hw0 : 2 * airyZetaComplex z ≠ 0 := slitPlane_ne_zero hws
  field_simp
  ring

/-- `R_N = (2π)⁻¹ (-1)^{N-1} w^{1-N} J_{N-1}(w)` with `w = 2ζ`, on `|arg z| < 2π/3`. -/
private lemma DerivativeRemainders.remainder_eq_J {z : ℂ} (hz : z ≠ 0)
    (harg : |arg z| < 2 * π / 3) (M : ℕ) :
    airyRemainder .aiDeriv (M + 1) z = (1 / (2 * π) : ℂ) * (-1) ^ M /
      (2 * airyZetaComplex z) ^ M * airyDerJ M (2 * airyZetaComplex z) := by
  obtain ⟨-, hws, hc⟩ := DerivativeRemainders.polar hz harg
  rw [← DerivativeRemainders.stieltjes_remainder hws]
  simp only [airyRemainder, airyFunction, airyExponentialSum]
  rw [DerivativeRemainders.normalizedU_eq hz harg, Finset.sum_range_succ']
  simp only [hc]
  simp only [pow_zero, div_one, airyExpansionCoeff, RealRemainders.airyV_zero, ofReal_one, mul_one]
  ring

/-- A lower bound `|t + w| ≥ s |w|` gives `|R_N| ≤ s⁻¹ |T_N|`. -/
private lemma DerivativeRemainders.remainder_le_of_lower {z : ℂ} (hz : z ≠ 0)
    (harg : |arg z| < 2 * π / 3) {N : ℕ}
    (hN : 1 ≤ N) {s : ℝ} (hs : 0 < s)
    (hlow : ∀ t : ℝ, 0 < t → s * ‖2 * airyZetaComplex z‖ ≤ ‖(t : ℂ) + 2 * airyZetaComplex z‖) :
    ‖airyRemainder .aiDeriv N z‖ ≤ s⁻¹ *
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  obtain ⟨-, hws, hc⟩ := DerivativeRemainders.polar hz harg
  set w := 2 * airyZetaComplex z with hwdef
  have hw0 : w ≠ 0 := slitPlane_ne_zero hws
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [DerivativeRemainders.remainder_eq_J hz harg M, hc M, ← hwdef]
  have hJ : ‖airyDerJ M w‖ ≤ airyDerMoment M / (s * ‖w‖) := by
    have hint : IntegrableOn
        (fun t : ℝ => t ^ M * DerivativeRemainders.density t / (s * ‖w‖)) (Ioi 0) :=
      (DerivativeRemainders.density_moment M).1.div_const _
    have h := norm_integral_le_of_norm_le
      (f := fun t : ℝ => (DerivativeRemainders.density t : ℂ) * (t : ℂ) ^ M / ((t : ℂ) + w))
          hint.integrable ?_
    · rw [airyDerJ]
      refine h.trans (le_of_eq ?_)
      rw [integral_div, (DerivativeRemainders.density_moment M).2]
      rfl
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t (ht : 0 < t) => ?_)
      have hρ := DerivativeRemainders.density_nonneg ht
      have hl := hlow t ht
      have hd : 0 < ‖(t : ℂ) + w‖ := lt_of_lt_of_le (by positivity) hl
      rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hρ, Real.norm_of_nonneg ht.le, div_le_div_iff₀ hd (by positivity)]
      have : 0 ≤ DerivativeRemainders.density t * t ^ M := by positivity
      nlinarith
  have hm := airyDerMoment_pos M
  have h2π : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg hπ.le]
  refine le_trans (b := 1 / (2 * π) / ‖w‖ ^ M * (airyDerMoment M / (s * ‖w‖))) ?_ (le_of_eq ?_)
  · rw [norm_mul, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, h2π,
      norm_pow]
    have h0 : (0:ℝ) ≤ 1 / (2 * π) / ‖w‖ ^ M := div_nonneg (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hJ h0
  · simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, mul_one, h2π,
      Complex.norm_real, Real.norm_of_nonneg hm.le]
    field_simp
    ring

/-- `|t + X e^{iφ}|² = (t + X cos φ)² + (X sin φ)²`. -/
private lemma DerivativeRemainders.norm_sq_add (t X φ : ℝ) :
    ‖(t : ℂ) + (X : ℂ) * exp ((φ : ℂ) * I)‖ ^ 2 =
      (t + X * Real.cos φ) ^ 2 + (X * Real.sin φ) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  ring

/-- The bound with multiplier `1` for `|arg z| ≤ π/3`. -/
private lemma DerivativeRemainders.aiDeriv_le_one {z : ℂ} (hz : z ≠ 0)
    (harg : |arg z| ≤ π / 3) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N z‖ ≤ ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  have harg' : |arg z| < 2 * π / 3 := by linarith
  obtain ⟨hw, -, -⟩ := DerivativeRemainders.polar hz harg'
  have h := DerivativeRemainders.remainder_le_of_lower hz harg' hN one_pos (fun t ht => ?_)
  · simpa using h
  rw [hw, one_mul]
  set X : ℝ := Real.exp (log 2 + airyLogZeta z).re
  have hX : 0 < X := Real.exp_pos _
  have hc : 0 ≤ Real.cos (3 / 2 * arg z) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [abs_le.mp harg], by linarith [abs_le.mp harg]⟩
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hX.le]
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [DerivativeRemainders.norm_sq_add]
  have := Real.sin_sq_add_cos_sq (3 / 2 * arg z)
  nlinarith [mul_nonneg (mul_nonneg ht.le hX.le) hc]

/-- The bound with multiplier `|csc(3 arg z / 2)|` for `|arg z| < 2π/3`. -/
private lemma DerivativeRemainders.aiDeriv_le_csc {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < 2 * π / 3)
    (hsin : Real.sin (3 * arg z / 2) ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N z‖ ≤ |(Real.sin (3 * arg z / 2))⁻¹| *
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  obtain ⟨hw, -, -⟩ := DerivativeRemainders.polar hz harg
  have hs : Real.sin (3 / 2 * arg z) ≠ 0 := by
    rwa [show 3 / 2 * arg z = 3 * arg z / 2 by ring]
  have h := DerivativeRemainders.remainder_le_of_lower hz harg hN (abs_pos.mpr hs) (fun t ht => ?_)
  · rwa [abs_inv, show 3 * arg z / 2 = 3 / 2 * arg z by ring]
  rw [hw]
  set X : ℝ := Real.exp (log 2 + airyLogZeta z).re
  have hX : 0 < X := Real.exp_pos _
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hX.le]
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [DerivativeRemainders.norm_sq_add, mul_pow, sq_abs]
  nlinarith [sq_nonneg (t + X * Real.cos (3 / 2 * arg z))]

/-- `Ai'(u) + ω² Ai'(uω) + ω̄² Ai'(uω̄) = 0` with `ω = e^{±2πi/3}`, the derivative of 9.2.12. -/
private lemma DerivativeRemainders.connection (u : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyAiDeriv u + exp (((ε * (2 * π / 3)) : ℝ) * I) ^ 2 *
        airyAiDeriv (u * exp (((ε * (2 * π / 3)) : ℝ) * I)) +
      exp ((((-ε) * (2 * π / 3)) : ℝ) * I) ^ 2 *
        airyAiDeriv (u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I)) = 0 := by
  set a := exp (((ε * (2 * π / 3)) : ℝ) * I)
  set b := exp ((((-ε) * (2 * π / 3)) : ℝ) * I)
  have hg : (fun v => airyAi v + a * airyAi (v * a) + b * airyAi (v * b)) = fun _ => 0 :=
    funext fun v => StieltjesBounds.connection hε
  have h1 := ((hasDerivAt_airyAi (u * a)).comp u ((hasDerivAt_id u).mul_const a)).const_mul a
  have h2 := ((hasDerivAt_airyAi (u * b)).comp u ((hasDerivAt_id u).mul_const b)).const_mul b
  have h := ((hasDerivAt_airyAi u).add h1).add h2
  have h0 : HasDerivAt (fun v => airyAi v + a * airyAi (v * a) + b * airyAi (v * b)) 0 u := by
    rw [hg]; exact hasDerivAt_const _ _
  have := h0.unique (by
    convert h using 1
    funext v
    simp only [Pi.add_apply, Function.comp_apply, id_eq])
  linear_combination -this

/-- The connection formula for the `Ai'` remainder at `z = u e^{±2πi/3}`. -/
private lemma DerivativeRemainders.third_relation {u : ℂ} (hu : u ≠ 0)
    (harg : |arg u| < π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (N : ℕ) :
    airyRemainder .aiDeriv N (u * exp (((ε * (2 * π / 3)) : ℝ) * I)) =
      airyRemainder .aiDeriv N (u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I)) +
        (-(exp (((ε * (π / 6)) : ℝ) * I) ^ 9)⁻¹) * exp (-(2 * airyZetaComplex u)) *
          (airyAiDeriv u / airyPrefactor .aiDeriv u) := by
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> norm_num
  have hz1 := RotatedExpansions.zeta_rotation hu harg hε
  have hz2 := RotatedExpansions.zeta_rotation hu harg hε'
  have hq1 := RotatedExpansions.quarter_rotation hu harg hε
  have hq2 := RotatedExpansions.quarter_rotation hu harg hε'
  have conn := DerivativeRemainders.connection u hε
  set E := exp (((ε * (π / 6)) : ℝ) * I) with hE
  have hE0 : E ≠ 0 := exp_ne_zero _
  have hpow : ∀ (c : ℝ) (n : ℕ), c = n * (ε * (π / 6)) → exp ((c : ℂ) * I) = E ^ n := by
    intro c n hc; rw [hE, ← exp_nat_mul]; congr 1; rw [hc]; push_cast; ring
  have hpowi : ∀ (c : ℝ) (n : ℕ), c = -(n * (ε * (π / 6))) → exp ((c : ℂ) * I) = (E ^ n)⁻¹ := by
    intro c n hc; rw [hE, ← exp_nat_mul, ← exp_neg]; congr 1; rw [hc]; push_cast; ring
  have hE6 : E ^ 6 = -1 := by
    rw [← hpow (ε * π) 6 (by push_cast; ring)]
    rcases hε with rfl | rfl
    · simp
    · rw [show (((-1 : ℝ) * π : ℝ) : ℂ) * I = -(π * I) by push_cast; ring, exp_neg, exp_pi_mul_I]
      norm_num
  simp only [airyRemainder, airyFunction, airyPrefactor, airyExponentialSum, hz1, hz2, hq1, hq2]
  generalize airyAiDeriv u = A0 at conn ⊢
  generalize airyAiDeriv (u * exp (((ε * (2 * π / 3)) : ℝ) * I)) = A1 at conn ⊢
  generalize airyAiDeriv (u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I)) = A2 at conn ⊢
  rw [hpow (ε * (2 * π / 3)) 4 (by push_cast; ring),
    hpowi ((-ε) * (2 * π / 3)) 4 (by push_cast; ring)] at conn
  rw [hpowi ((-ε) * (π / 6)) 1 (by push_cast; ring), pow_one]
  have hX0 : exp (airyZetaComplex u) ≠ 0 := exp_ne_zero _
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : u ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hu)
  rw [neg_neg, show -(2 * airyZetaComplex u) = -airyZetaComplex u + -airyZetaComplex u by ring,
    exp_add, exp_neg]
  generalize exp (airyZetaComplex u) = X at *
  field_simp
  have hF : E ^ 4 * (E ^ 4)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hE0)
  generalize (E ^ 4)⁻¹ = F at conn hF
  linear_combination (-(2 * (Real.sqrt π : ℂ))) * conn +
    (2 * (Real.sqrt π : ℂ) * A2 * F ^ 2 * (E ^ 12 - E ^ 6 + 1)) * hE6 -
    (2 * (Real.sqrt π : ℂ) * A2 * E ^ 10 * (E ^ 4 * F + 1)) * hF


/-- `|v_N| = (6N+1)/(6N-1) u_N` for `N ≥ 1`. -/
private lemma DerivativeRemainders.abs_airyV {N : ℕ} (hN : 1 ≤ N) :
    |airyV N| = (6 * N + 1) / (6 * N - 1) * airyU N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hu := StieltjesBounds.airyU_pos N
  rw [airyV, abs_mul, abs_div, abs_of_pos (by linarith), abs_of_neg (by linarith),
    abs_of_pos hu, neg_sub]

/-- `((N-1)/(2e))^{N-1} ≤ 2/(N-1) (N/(2e))^N` for `N ≥ 2`. -/
private lemma DerivativeRemainders.pow_pred_le {M : ℕ} (hM : 1 ≤ M) :
    ((M : ℝ) / (2 * Real.exp 1)) ^ M ≤
      2 / M * (((M + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^ (M + 1) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have he := Real.exp_pos 1
  have h1 := Real.one_sub_div_pow_le_exp_neg (n := M + 1) (t := 1) (by push_cast; linarith)
  push_cast at h1 ⊢
  have hq : (1 : ℝ) - 1 / (M + 1) = M / (M + 1) := by field_simp; ring
  rw [hq, div_pow, pow_succ, Real.exp_neg] at h1
  have hk : ((M : ℝ) / (2 * Real.exp 1)) ^ M =
      ((M + 1) / (2 * Real.exp 1)) ^ M * (M ^ M / (M + 1) ^ M) := by
    rw [div_pow, div_pow]; field_simp
  rw [hk, pow_succ]
  have hA : 0 < ((M + 1) / (2 * Real.exp 1) : ℝ) ^ M := by positivity
  have h2 : (M : ℝ) ^ M / (M + 1) ^ M ≤ (Real.exp 1)⁻¹ * ((M + 1) / M) := by
    rw [div_le_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by positivity)]
    calc (M : ℝ) ^ M ≤ (Real.exp 1)⁻¹ * ((M + 1) ^ M * (M + 1)) / M := by
          rw [le_div_iff₀ hM0, ← pow_succ]; exact h1
      _ = _ := by field_simp
  calc ((M + 1) / (2 * Real.exp 1) : ℝ) ^ M * (M ^ M / (M + 1) ^ M)
      ≤ ((M + 1) / (2 * Real.exp 1)) ^ M * ((Real.exp 1)⁻¹ * ((M + 1) / M)) :=
        mul_le_mul_of_nonneg_left h2 hA.le
    _ = _ := by field_simp

/-- `e^{-2s}(s + 7/72) ≤ √(2π) |v_1|`. -/
private lemma DerivativeRemainders.tail_one (s : ℝ) :
    Real.exp (-(2 * s)) * (s + 7 / 72) ≤ Real.sqrt (2 * π * 1) * |airyV 1| := by
  rw [RealRemainders.airyV_one, mul_one]
  have h1 := Real.add_one_le_exp (2 * s + 2 * (7 / 72) - 1)
  have h2 : Real.exp (-(2 * s)) * (s + 7 / 72) ≤ Real.exp (-(29 / 36)) / 2 := by
    have : Real.exp (-(29 / 36)) = Real.exp (-(2 * s)) * Real.exp (2 * s + 2 * (7 / 72) - 1) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    have := Real.exp_pos (-(2 * s))
    nlinarith
  have h3 := Real.quadratic_le_exp_of_nonneg (x := 29 / 36) (by norm_num)
  have h4 : Real.exp (-(29 / 36)) ≤ 1 / (1 + 29 / 36 + (29 / 36) ^ 2 / 2) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h3
  have h5 : (5 / 2 : ℝ) ≤ Real.sqrt (2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_d2]
  rw [abs_of_neg (by norm_num : (-7 / 72 : ℝ) < 0)]
  refine h2.trans ?_
  nlinarith

/-- `e^{-2s}(s^N + (7/72) s^{N-1}) ≤ √(2πN) |v_N|` for `N ≥ 1`, `s ≥ 0`: the numerical
inequality behind the last sector of DLMF 9.7.17 for `Ai'`. -/
private lemma DerivativeRemainders.tail_numeric {N : ℕ} (hN : 1 ≤ N) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-(2 * s)) * (s ^ N + 7 / 72 * s ^ (N - 1)) ≤
      Real.sqrt (2 * π * N) * |airyV N| := by
  rcases Nat.lt_or_ge N 2 with h | h2
  · obtain rfl : N = 1 := by omega
    simpa using DerivativeRemainders.tail_one s
  have hA := StieltjesBounds.pow_exp_le hs N
  have hB := StieltjesBounds.pow_exp_le hs (N - 1)
  have hE := Real.exp_pos (-(2 * s))
  have hsplit : Real.exp (-(2 * s)) * (s ^ N + 7 / 72 * s ^ (N - 1)) ≤
      ((N : ℝ) / (2 * Real.exp 1)) ^ N +
        7 / 72 * (((N - 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^ (N - 1) := by
    nlinarith
  refine hsplit.trans ?_
  have hu := StieltjesBounds.airyU_pos N
  rw [DerivativeRemainders.abs_airyV hN]
  rcases Nat.lt_or_ge N 4 with h | h4
  · have he := Real.exp_one_gt_d9
    have hπ := Real.pi_gt_d6
    have hv : 0 < (6 * (N : ℝ) + 1) / (6 * N - 1) * airyU N := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast h2
      exact mul_pos (div_pos (by linarith) (by linarith)) hu
    have hle : ∀ k : ℕ, ((k : ℝ) / (2 * Real.exp 1)) ^ k ≤ ((k : ℝ) / (2 * 2.7182818283)) ^ k :=
      fun k => pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)) k
    have h3 : Real.sqrt (2 * 3.141592 * N) * ((6 * (N : ℝ) + 1) / (6 * N - 1) * airyU N) ≤
        Real.sqrt (2 * π * N) * ((6 * (N : ℝ) + 1) / (6 * N - 1) * airyU N) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by gcongr)) hv.le
    refine le_trans (add_le_add (hle N) (mul_le_mul_of_nonneg_left (hle (N - 1))
      (by norm_num))) (le_trans ?_ h3)
    rw [← Real.sqrt_sq hv.le, ← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    interval_cases N <;> norm_num [airyU, ascPochhammer_succ_eval, Nat.factorial]
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hM : (3 : ℝ) ≤ M := by exact_mod_cast (by omega : 3 ≤ M)
    simp only [Nat.add_sub_cancel] at *
    have hP := DerivativeRemainders.pow_pred_le (M := M) (by omega)
    have hG := StieltjesBounds.gamma_inequality (M + 1)
    set A := (((M + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^ (M + 1)
    have hA0 : 0 ≤ A := by positivity
    push_cast at hG ⊢
    have hstep : A + 7 / 72 * ((M : ℝ) / (2 * Real.exp 1)) ^ M ≤
        A * ((36 * M + 7) / (36 * M)) := by
      have : A * ((36 * M + 7) / (36 * M)) = A + 7 / 72 * (2 / M * A) := by
        field_simp; ring
      rw [this]; linarith
    refine hstep.trans ?_
    have hk : 0 ≤ (36 * (M : ℝ) + 7) / (36 * M) := by positivity
    refine (mul_le_mul_of_nonneg_right hG hk).trans ?_
    have hS : Real.sqrt (2 * π * ((M : ℝ) + 1 + 1 / 6)) * ((36 * M + 7) / (36 * M)) ≤
        Real.sqrt (2 * π * ((M : ℝ) + 1)) * ((6 * ((M : ℝ) + 1) + 1) / (6 * (M + 1) - 1)) := by
      rw [← Real.sqrt_sq hk, ← Real.sqrt_mul (by positivity),
        ← Real.sqrt_sq (show 0 ≤ (6 * ((M : ℝ) + 1) + 1) / (6 * (M + 1) - 1) by
          apply div_nonneg <;> linarith), ← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      rw [div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc,
        div_le_div_iff₀ (by positivity) (by nlinarith)]
      have hπ := Real.pi_pos
      have hpoly : 0 ≤ 5184 * ((M : ℝ) + 1) ^ 3 - 25524 * (M + 1) ^ 2 + 19956 * (M + 1) - 841 := by
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ M - 3)
          (by linarith : (0 : ℝ) ≤ M - 3)) (by linarith : (0 : ℝ) ≤ M - 3)]
      have := mul_nonneg (mul_nonneg hπ.le (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ 2)) hpoly
      nlinarith
    nlinarith

/-- `‖Ai'(u)/(prefactor)‖ ≤ 1 + (7/72)/|ζ(u)|` for `|arg u| ≤ π/3`. -/
private lemma DerivativeRemainders.ratio_norm_le {u : ℂ} (hu : u ≠ 0) (harg : |arg u| ≤ π / 3) :
    ‖airyAiDeriv u / airyPrefactor .aiDeriv u‖ ≤ 1 + 7 / 72 / ‖airyZetaComplex u‖ := by
  have h := DerivativeRemainders.aiDeriv_le_one hu harg le_rfl
  have he : airyAiDeriv u / airyPrefactor .aiDeriv u = 1 + airyRemainder .aiDeriv 1 u := by
    simp only [airyRemainder, airyFunction, airyExponentialSum, Finset.sum_range_one,
      airyExpansionCoeff, pow_zero, RealRemainders.airyV_zero, ofReal_one, mul_one, div_one]
    ring
  rw [he]
  refine (norm_add_le _ _).trans (add_le_add (by simp) (h.trans (le_of_eq ?_)))
  simp only [airyExpansionCoeff, pow_one, RealRemainders.airyV_one, norm_div, norm_mul, norm_neg,
    norm_one, one_mul, Complex.norm_real]
  norm_num

/-- `Re (2ζ(u)) = 2 |ζ(u)| cos ((3/2) arg u)` for `u ≠ 0`. -/
private lemma DerivativeRemainders.re_two_zeta {u : ℂ} (hu0 : u ≠ 0) :
    (2 * airyZetaComplex u).re = 2 * (‖airyZetaComplex u‖ * Real.cos (3 / 2 * arg u)) := by
  have h := RotatedExpansions.re_W u 0
  simp only [ofReal_zero, zero_mul, add_zero] at h
  rw [exp_log_two_add_airyLogZeta hu0] at h
  have hn : Real.exp (log 2 + airyLogZeta u).re = ‖2 * airyZetaComplex u‖ := by
    rw [← Complex.norm_exp, exp_log_two_add_airyLogZeta hu0]
  rw [h, hn, norm_mul]; simp; ring

/-- The last term of 9.7.17 for `Ai'`:
`e^{-2ρc}(1 + (7/72)/ρ) ≤ √(2πN) c^{-N} |v_N| ρ^{-N}` for `0 < c ≤ 1`. -/
private lemma DerivativeRemainders.third_term {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (hc1 : c ≤ 1) {N : ℕ}
    (hN : 1 ≤ N) :
    Real.exp (-(2 * (ρ * c))) * (1 + 7 / 72 / ρ) ≤
      Real.sqrt (2 * π * (N + 0)) / c ^ ((N : ℝ) + 0) * (|airyV N| / ρ ^ N) := by
  simp only [add_zero]
  rw [Real.rpow_natCast, div_mul_div_comm, le_div_iff₀ (by positivity)]
  have key := DerivativeRemainders.tail_numeric hN (mul_pos hρ hc).le
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at key
  have hE := Real.exp_pos (-(2 * (ρ * c)))
  calc Real.exp (-(2 * (ρ * c))) * (1 + 7 / 72 / ρ) * (c ^ (M + 1) * ρ ^ (M + 1))
      = Real.exp (-(2 * (ρ * c))) * ((ρ * c) ^ (M + 1) + 7 / 72 * c * (ρ * c) ^ M) := by
        rw [mul_pow, mul_pow]; field_simp; ring
    _ ≤ Real.exp (-(2 * (ρ * c))) * ((ρ * c) ^ (M + 1) + 7 / 72 * (ρ * c) ^ M) := by
        gcongr
        linarith
    _ ≤ _ := key

/-- **The third sector of 9.7.17 for `Ai'`**, `2π/3 < |arg z| < π`. -/
private lemma DerivativeRemainders.aiDeriv_third {z : ℂ} (hz : z ≠ 0) (h1 : 2 * π / 3 < |arg z|)
    (h2 : |arg z| < π) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N z‖ ≤ (Real.sqrt (2 * π * (N + 0)) /
      |Real.cos (3 * arg z / 2)| ^ ((N : ℝ) + 0) + airyChi (N + 0) + 1) *
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  obtain ⟨ε, hε, hεarg⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ arg z = |arg z| * ε := by
    rcases le_or_gt 0 (arg z) with h | h
    · exact ⟨1, Or.inl rfl, by rw [abs_of_nonneg h, mul_one]⟩
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h]; ring⟩
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> norm_num
  set u := z * exp ((((-ε) * (2 * π / 3)) : ℝ) * I) with hudef
  have hu0 : u ≠ 0 := mul_ne_zero hz (exp_ne_zero _)
  have hargu : arg u = arg z + (-ε) * (2 * π / 3) := by
    rw [hudef]
    apply Complex.arg_mul_exp_ofReal_mul_I hz <;> rcases hε with rfl | rfl <;> rw [hεarg]
        <;> nlinarith
  have hu : |arg u| < π / 3 := by
    rw [hargu, hεarg]; rcases hε with rfl | rfl <;> rw [abs_lt] <;> constructor <;> nlinarith
  have hzu : z = u * exp (((ε * (2 * π / 3)) : ℝ) * I) := by
    rw [hudef, mul_assoc, ← exp_add]
    rw [show (((-ε) * (2 * π / 3) : ℝ) : ℂ) * I + ((ε * (2 * π / 3) : ℝ) : ℂ) * I = 0 by
      push_cast; ring, exp_zero, mul_one]
  set z₂ := u * exp ((((-ε) * (2 * π / 3)) : ℝ) * I) with hz₂
  obtain ⟨b1, b2⟩ := RotatedExpansions.arg_rotation_bounds hu hε'
  have hz₂0 : z₂ ≠ 0 := mul_ne_zero hu0 (exp_ne_zero _)
  have harg₂ : arg z₂ = arg u + (-ε) * (2 * π / 3) := Complex.arg_mul_exp_ofReal_mul_I hu0 b1 b2
  have hc : 0 < Real.cos (3 / 2 * arg u) := by
    have := abs_lt.mp hu
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcz : |Real.cos (3 * arg z / 2)| = Real.cos (3 / 2 * arg u) := by
    have : 3 * arg z / 2 = 3 / 2 * arg u + ε * π := by rw [hargu]; ring
    rw [this]
    rcases hε with rfl | rfl
    · rw [one_mul, Real.cos_add_pi, abs_neg, abs_of_pos hc]
    · rw [neg_one_mul, ← sub_eq_add_neg, Real.cos_sub_pi, abs_neg, abs_of_pos hc]
  have hζ1 := RotatedExpansions.zeta_rotation hu0 hu hε
  have hζ2 := RotatedExpansions.zeta_rotation hu0 hu hε'
  have hT : ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ =
      |airyV N| / ‖airyZetaComplex u‖ ^ N := by
    rw [hzu, hζ1]
    simp only [airyExpansionCoeff, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hR₂ : ‖airyRemainder .aiDeriv N z₂‖ ≤ (airyChi (N + 0) + 1) *
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ := by
    have hz2a : |arg z₂| < 2 * π / 3 := by
      rw [harg₂]; have := abs_lt.mp hu
      rcases hε with rfl | rfl <;> rw [abs_lt] <;> constructor <;> nlinarith
    have hsin : Real.sin (3 * arg z₂ / 2) ≠ 0 := by
      rw [harg₂, show 3 * (arg u + (-ε) * (2 * π / 3)) / 2 = 3 / 2 * arg u - ε * π by ring]
      rcases hε with rfl | rfl
      all_goals
        first
          | rw [one_mul, Real.sin_sub_pi]
          | rw [neg_one_mul, sub_neg_eq_add, Real.sin_add_pi]
        refine neg_ne_zero.mpr fun h0 => ?_
        have := abs_lt.mp hu
        rcases Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith) |>.mp h0 with h'
        have hargu0 : arg u = 0 := by linarith
        have := hargu; rw [hargu0, hεarg] at this
        nlinarith
    have := DerivativeRemainders.aiDeriv_le_chi hz₂0 hz2a hsin hN
    rwa [hz₂, hζ2, ← hζ1, ← hzu] at this
  have hrel := DerivativeRemainders.third_relation hu0 hu hε N
  rw [← hzu, ← hz₂] at hrel
  rw [hrel]
  have hκ : ‖-(exp (((ε * (π / 6)) : ℝ) * I) ^ 9)⁻¹‖ = 1 := by
    rw [norm_neg, norm_inv, norm_pow, norm_exp_ofReal_mul_I, one_pow, inv_one]
  have hF := DerivativeRemainders.ratio_norm_le hu0 hu.le
  have hre := DerivativeRemainders.re_two_zeta hu0
  have hρ : 0 < ‖airyZetaComplex u‖ := norm_pos_iff.mpr (StieltjesBounds.zeta_ne_zero hu0)
  have h3 := DerivativeRemainders.third_term hρ hc (Real.cos_le_one _) hN
  rw [hcz, hT]
  rw [hT] at hR₂
  calc ‖airyRemainder .aiDeriv N z₂ + -(exp (((ε * (π / 6)) : ℝ) * I) ^ 9)⁻¹ *
        exp (-(2 * airyZetaComplex u)) * (airyAiDeriv u / airyPrefactor .aiDeriv u)‖
      ≤ ‖airyRemainder .aiDeriv N z₂‖ + Real.exp (-(2 * (‖airyZetaComplex u‖ *
          Real.cos (3 / 2 * arg u)))) * (1 + 7 / 72 / ‖airyZetaComplex u‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, norm_mul, hκ, one_mul, norm_exp, neg_re, hre]
        exact mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
    _ ≤ _ := by linarith

/-- On the slit plane, for `N ≥ 1`, the remainder of the normalized `Ai'` expansion is bounded
by the error multiplier times the first neglected term (DLMF 9.7.17). -/
@[dlmf 9.7.E17]
theorem airyAiDeriv_complex_error {z : ℂ} (hz : z ∈ slitPlane) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N z‖ ≤ airyErrorMultiplier N (0) z *
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ := by
  have hπ := Real.pi_pos
  have hz0 := slitPlane_ne_zero hz
  have hlt : |arg z| < π := by
    rw [mem_slitPlane_iff_arg] at hz
    exact lt_of_le_of_ne (abs_le.mpr ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩) (fun h => by
      rcases abs_eq hπ.le |>.mp h with h' | h'
      · exact hz.1 h'
      · linarith [neg_pi_lt_arg z])
  unfold airyErrorMultiplier
  split_ifs with h1 h2 h3
  · rw [one_mul]; exact DerivativeRemainders.aiDeriv_le_one hz0 h1 hN
  · rcases lt_or_eq_of_le h2 with h | h
    · exact absurd h3 (StieltjesBounds.sin_ne_zero (lt_of_not_ge h1) h)
    · exact DerivativeRemainders.aiDeriv_boundary hz0 h hN
  · rcases lt_or_eq_of_le h2 with h | h
    · rw [min_mul_of_nonneg _ _ (norm_nonneg _)]
      exact le_min (DerivativeRemainders.aiDeriv_le_csc hz0 h h3 hN)
          (DerivativeRemainders.aiDeriv_le_chi hz0 h h3 hN)
    · exfalso; apply h3
      rcases le_or_gt 0 (arg z) with h0 | h0
      · rw [abs_of_nonneg h0] at h; rw [h, show 3 * (2 * π / 3) / 2 = π by ring, Real.sin_pi]
      · rw [abs_of_neg h0] at h
        rw [show arg z = -(2 * π / 3) by linarith, show 3 * -(2 * π / 3) / 2 = -π by ring,
          Real.sin_neg, Real.sin_pi, neg_zero]
  · exact DerivativeRemainders.aiDeriv_third hz0 (lt_of_not_ge h2) hlt hN
end DLMF.Airy

end
