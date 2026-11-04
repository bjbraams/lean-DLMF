/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Products.InfiniteProducts
public import DLMF.QSeries.RamanujanPsi
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog

/-!
# The mean of `log |θ₁/θ₄|` over a real period

For `ℑτ > 0` and `C ≠ 0`,
`∫₀^{2π} log ‖C θ₁(θ/2|τ)/θ₄(θ/2|τ)‖ dθ = 2π (log ‖C‖ - π ℑτ/4)`.
With `w = e^{iθ}`, the product formulas DLMF 20.5.1 and 20.5.4 write
`‖θ₁/θ₄‖ = |q^{1/4}| ‖w - 1‖ ‖(Qw;Q)_∞ (Q/w;Q)_∞‖ / ‖(qw;Q)_∞ (q/w;Q)_∞‖` (`Q = q²`). The
circle mean of `log ‖w - 1‖` vanishes, and so does the circle mean of `log ‖(cw;Q)_∞‖` for
`‖c‖ < 1` by the mean value property of the harmonic function `log ‖(cw;Q)_∞‖` (Mathlib's
`AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`). This is the theta-function input to
DLMF 22.14.16–22.14.17.

## Main results

* `integral_log_norm_mul_jacobiThetaOneTau_div`: the mean value above, with integrability.
-/

@[expose] public section

open Complex Real MeasureTheory
open DLMF.QSeries DLMF.Elliptic

noncomputable section

namespace DLMF.Theta

/-- Circle average of `log ‖(c w; Q)_∞‖` vanishes for `‖c‖ < 1`. -/
private lemma circleAverage_log_norm_qPochhammerInf {c Q : ℂ} (hc : ‖c‖ < 1) (hQ : ‖Q‖ < 1) :
    circleAverage (fun w => Real.log ‖qPochhammerInf (c * w) Q‖) 0 1 = 0 := by
  have hd : Differentiable ℂ (fun w => qPochhammerInf (c * w) Q) :=
    (differentiable_qPochhammerInf_left hQ).comp (differentiable_id.const_mul c)
  rw [AnalyticOnNhd.circleAverage_log_norm_of_ne_zero (fun w _ => hd.analyticAt w)]
  · simp [qPochhammerInf]
  · intro u hu
    refine qPochhammerInf_ne_zero_of_norm_lt_one ?_ hQ
    rw [norm_mul]
    have : ‖u‖ ≤ 1 := by simpa using hu
    nlinarith [norm_nonneg c, norm_nonneg u]


/-- `e^{iθ} - 1 = e^{iθ/2} · 2i sin(θ/2)`, so `‖e^{iθ} - 1‖ = ‖2 sin(θ/2)‖`. -/
private lemma norm_circleMap_sub_one (θ : ℝ) :
    ‖circleMap 0 1 θ - 1‖ = ‖2 * Complex.sin ((θ / 2 : ℝ) : ℂ)‖ := by
  have h : circleMap 0 1 θ - 1 = cexp (((θ / 2 : ℝ) : ℂ) * I) *
      (2 * Complex.sin ((θ / 2 : ℝ) : ℂ) * I) := by
    rw [circleMap, Complex.sin]
    push_cast
    have h1 : cexp (θ / 2 * I) * cexp (-(θ / 2) * I) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
    have h2 : cexp (θ * I) = cexp (θ / 2 * I) * cexp (θ / 2 * I) := by
      rw [← Complex.exp_add]; ring_nf
    rw [h2]
    linear_combination (-I ^ 2) * h1 + (cexp (θ / 2 * I) ^ 2 - 1) * I_sq
  rw [h, norm_mul, norm_mul, norm_exp_ofReal_mul_I, norm_I, one_mul, mul_one]


/-- The function of `w = e^{2iζ}` whose value is `log ‖θ₁(ζ|τ)/θ₄(ζ|τ)‖` on the unit circle. -/
private noncomputable def logNormThetaOneDivFour (τ w : ℂ) : ℝ :=
  Real.log ‖cexp (π * I * τ / 4)‖ + Real.log ‖w - 1‖ +
    Real.log ‖qPochhammerInf (cexp (π * I * τ) ^ 2 * w) (cexp (π * I * τ) ^ 2)‖ +
    Real.log ‖qPochhammerInf (cexp (π * I * τ) ^ 2 * w⁻¹) (cexp (π * I * τ) ^ 2)‖ -
    Real.log ‖qPochhammerInf (cexp (π * I * τ) * w) (cexp (π * I * τ) ^ 2)‖ -
    Real.log ‖qPochhammerInf (cexp (π * I * τ) * w⁻¹) (cexp (π * I * τ) ^ 2)‖

private lemma log_norm_mul_jacobiThetaOneTau_div {τ : ℂ} (hτ : 0 < τ.im) {C : ℂ} (hC : C ≠ 0)
    (θ : ℝ) (hw : circleMap 0 1 θ ≠ 1) :
    Real.log ‖C * (jacobiThetaOneTau ((θ / 2 : ℝ) : ℂ) τ /
      jacobiThetaFourTau ((θ / 2 : ℝ) : ℂ) τ)‖ =
      Real.log ‖C‖ + logNormThetaOneDivFour τ (circleMap 0 1 θ) := by
  have hQ := norm_nome_sq_lt_one hτ
  have hE := norm_nome_lt_one hτ
  set ζ : ℂ := ((θ / 2 : ℝ) : ℂ) with hζ
  set E := cexp (π * I * τ) with hEdef
  set w := circleMap 0 1 θ with hwdef
  have hw1 : cexp (2 * I * ζ) = w := by
    rw [hwdef, circleMap, hζ]; push_cast; ring_nf
  have hw2 : cexp (2 * I * (ζ + π / 2)) = -w := by
    rw [← hw1, show 2 * I * (ζ + π / 2) = 2 * I * ζ + π * I by ring, Complex.exp_add,
      exp_pi_mul_I]; ring
  have hwn : ‖w‖ = 1 := by simp [hwdef]
  have hw0 : w ≠ 0 := by intro h; simp [h] at hwn
  have hwin : ‖w⁻¹‖ = 1 := by rw [norm_inv, hwn, inv_one]
  have hP : ∀ c : ℂ, ‖c‖ < 1 → ∀ u : ℂ, ‖u‖ = 1 → qPochhammerInf (c * u) (E ^ 2) ≠ 0 :=
    fun c hc u hu => qPochhammerInf_ne_zero_of_norm_lt_one (by rw [norm_mul, hu, mul_one]; exact hc)
      hQ
  have hA : qPochhammerInf (E ^ 2) (E ^ 2) ≠ 0 := by
    simpa using hP _ hQ 1 (by simp)
  have hs : ‖2 * Complex.sin ζ‖ = ‖w - 1‖ := (norm_circleMap_sub_one θ).symm
  have hs0 : ‖w - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw)
  rw [jacobiThetaOneTau_eq_qPochhammerInf ζ hτ, jacobiThetaFourTau,
    jacobiThetaThreeTau_eq_qPochhammerInf _ hτ, hw1, hw2, ← hEdef,
    show -(E * -w) = E * w by ring, show -(E * (-w)⁻¹) = E * w⁻¹ by rw [inv_neg]; ring]
  have key : C * (2 * cexp (π * I * τ / 4) * Complex.sin ζ * (qPochhammerInf (E ^ 2) (E ^ 2) *
      qPochhammerInf (E ^ 2 * w) (E ^ 2) * qPochhammerInf (E ^ 2 * w⁻¹) (E ^ 2)) /
      (qPochhammerInf (E ^ 2) (E ^ 2) * qPochhammerInf (E * w) (E ^ 2) *
        qPochhammerInf (E * w⁻¹) (E ^ 2))) =
      C * cexp (π * I * τ / 4) * (2 * Complex.sin ζ) *
        (qPochhammerInf (E ^ 2 * w) (E ^ 2) * qPochhammerInf (E ^ 2 * w⁻¹) (E ^ 2)) /
        (qPochhammerInf (E * w) (E ^ 2) * qPochhammerInf (E * w⁻¹) (E ^ 2)) := by
    field_simp
  rw [key]
  generalize 2 * Complex.sin ζ = S at hs ⊢
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hs]
  have h1 := norm_ne_zero_iff.mpr hC
  have h2 := norm_ne_zero_iff.mpr (exp_ne_zero (π * I * τ / 4))
  have h3 := norm_ne_zero_iff.mpr (hP _ hQ w hwn)
  have h4 := norm_ne_zero_iff.mpr (hP _ hQ w⁻¹ hwin)
  have h5 := norm_ne_zero_iff.mpr (hP _ hE w hwn)
  have h6 := norm_ne_zero_iff.mpr (hP _ hE w⁻¹ hwin)
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul h5 h6,
    logNormThetaOneDivFour]
  ring


private lemma continuousOn_log_norm_qPochhammerInf_sphere {c Q : ℂ} (hc : ‖c‖ < 1) (hQ : ‖Q‖ < 1)
    {g : ℂ → ℂ} (hg : ContinuousOn g (Metric.sphere 0 1))
    (hgn : ∀ u ∈ Metric.sphere (0 : ℂ) 1, ‖g u‖ = 1) :
    ContinuousOn (fun w => Real.log ‖qPochhammerInf (c * g w) Q‖) (Metric.sphere 0 1) := by
  have hd := (differentiable_qPochhammerInf_left hQ).continuous
  refine ContinuousOn.log ((hd.comp_continuousOn (hg.const_smul c)).norm) fun u hu => ?_
  refine norm_ne_zero_iff.mpr (qPochhammerInf_ne_zero_of_norm_lt_one ?_ hQ)
  rw [norm_mul, hgn u hu, mul_one]; exact hc

private lemma circleIntegrable_logNormThetaOneDivFour {τ : ℂ} (hτ : 0 < τ.im) :
    CircleIntegrable (logNormThetaOneDivFour τ) 0 1 := by
  have hQ := norm_nome_sq_lt_one hτ
  have hE := norm_nome_lt_one hτ
  have hid : ContinuousOn (fun w : ℂ => w) (Metric.sphere 0 1) := continuousOn_id
  have hinv : ContinuousOn (fun w : ℂ => w⁻¹) (Metric.sphere 0 1) :=
    continuousOn_inv₀.mono fun u hu h0 => by
      rw [Set.mem_singleton_iff.mp h0] at hu; simp at hu
  have hn1 : ∀ u ∈ Metric.sphere (0 : ℂ) 1, ‖u‖ = 1 := fun u hu => by simpa using hu
  have hn2 : ∀ u ∈ Metric.sphere (0 : ℂ) 1, ‖u⁻¹‖ = 1 := fun u hu => by
    rw [norm_inv, hn1 u hu, inv_one]
  have c1 := (continuousOn_log_norm_qPochhammerInf_sphere hQ hQ hid hn1).circleIntegrable
    zero_le_one
  have c2 := (continuousOn_log_norm_qPochhammerInf_sphere hQ hQ hinv hn2).circleIntegrable
    zero_le_one
  have c3 := (continuousOn_log_norm_qPochhammerInf_sphere hE hQ hid hn1).circleIntegrable
    zero_le_one
  have c4 := (continuousOn_log_norm_qPochhammerInf_sphere hE hQ hinv hn2).circleIntegrable
    zero_le_one
  have c0 : CircleIntegrable (fun _ : ℂ => Real.log ‖cexp (π * I * τ / 4)‖) 0 1 :=
    continuousOn_const.circleIntegrable zero_le_one
  have cs := circleIntegrable_log_norm_sub_const (c := 0) (a := (1 : ℂ)) 1
  exact ((((c0.add cs).add c1).add c2).sub c3).sub c4

private lemma circleAverage_logNormThetaOneDivFour {τ : ℂ} (hτ : 0 < τ.im) :
    circleAverage (logNormThetaOneDivFour τ) 0 1 = -(π * τ.im / 4) := by
  have hQ := norm_nome_sq_lt_one hτ
  have hE := norm_nome_lt_one hτ
  have hid : ContinuousOn (fun w : ℂ => w) (Metric.sphere 0 1) := continuousOn_id
  have hinv : ContinuousOn (fun w : ℂ => w⁻¹) (Metric.sphere 0 1) :=
    continuousOn_inv₀.mono fun u hu h0 => by
      rw [Set.mem_singleton_iff.mp h0] at hu; simp at hu
  have hn1 : ∀ u ∈ Metric.sphere (0 : ℂ) 1, ‖u‖ = 1 := fun u hu => by simpa using hu
  have hn2 : ∀ u ∈ Metric.sphere (0 : ℂ) 1, ‖u⁻¹‖ = 1 := fun u hu => by
    rw [norm_inv, hn1 u hu, inv_one]
  have c1 := (continuousOn_log_norm_qPochhammerInf_sphere hQ hQ hid hn1).circleIntegrable
    zero_le_one
  have c2 := (continuousOn_log_norm_qPochhammerInf_sphere hQ hQ hinv hn2).circleIntegrable
    zero_le_one
  have c3 := (continuousOn_log_norm_qPochhammerInf_sphere hE hQ hid hn1).circleIntegrable
    zero_le_one
  have c4 := (continuousOn_log_norm_qPochhammerInf_sphere hE hQ hinv hn2).circleIntegrable
    zero_le_one
  have c0 : CircleIntegrable (fun _ : ℂ => Real.log ‖cexp (π * I * τ / 4)‖) 0 1 :=
    continuousOn_const.circleIntegrable zero_le_one
  have cs := circleIntegrable_log_norm_sub_const (c := 0) (a := (1 : ℂ)) 1
  have hfun : logNormThetaOneDivFour τ = ((((((fun _ : ℂ => Real.log ‖cexp (π * I * τ / 4)‖) +
      fun w => Real.log ‖w - 1‖) +
      fun w => Real.log ‖qPochhammerInf (cexp (π * I * τ) ^ 2 * w) (cexp (π * I * τ) ^ 2)‖) +
      fun w => Real.log ‖qPochhammerInf (cexp (π * I * τ) ^ 2 * w⁻¹) (cexp (π * I * τ) ^ 2)‖) -
      fun w => Real.log ‖qPochhammerInf (cexp (π * I * τ) * w) (cexp (π * I * τ) ^ 2)‖) -
      fun w => Real.log ‖qPochhammerInf (cexp (π * I * τ) * w⁻¹) (cexp (π * I * τ) ^ 2)‖) := rfl
  rw [hfun, circleAverage_sub (((c0.add cs).add c1).add c2 |>.sub c3) c4,
    circleAverage_sub (((c0.add cs).add c1).add c2) c3,
    circleAverage_add ((c0.add cs).add c1) c2, circleAverage_add (c0.add cs) c1,
    circleAverage_add c0 cs, circleAverage_const,
    circleAverage_log_norm_sub_const₁ (by simp),
    circleAverage_log_norm_qPochhammerInf hQ hQ, circleAverage_log_norm_qPochhammerInf hE hQ,
    circleAverage_zero_one_congr_inv (f := fun w => Real.log ‖qPochhammerInf
      (cexp (π * I * τ) ^ 2 * w) (cexp (π * I * τ) ^ 2)‖),
    circleAverage_zero_one_congr_inv (f := fun w => Real.log ‖qPochhammerInf
      (cexp (π * I * τ) * w) (cexp (π * I * τ) ^ 2)‖),
    circleAverage_log_norm_qPochhammerInf hQ hQ, circleAverage_log_norm_qPochhammerInf hE hQ,
    Complex.norm_exp, Real.log_exp]
  simp only [div_ofNat_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, zero_sub,
    mul_im, add_zero, sub_zero]
  ring


private lemma circleMap_ne_one_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π)) :
    circleMap 0 1 θ ≠ 1 := by
  intro h
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h' : θ = n * (2 * π) := by
    have := congrArg Complex.im hn
    simpa using this
  obtain ⟨h0, h1⟩ := hθ
  rw [h'] at h0 h1
  have hp := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by nlinarith
  have hn1 : (n : ℝ) < 1 := by nlinarith
  have : (0 : ℤ) < n := by exact_mod_cast hn0
  have : n < (1 : ℤ) := by exact_mod_cast hn1
  omega

/-- `∫₀^{2π} log ‖C θ₁(θ/2|τ)/θ₄(θ/2|τ)‖ dθ = 2π (log ‖C‖ - π ℑτ/4)`, with integrability. -/
theorem integral_log_norm_mul_jacobiThetaOneTau_div {τ : ℂ} (hτ : 0 < τ.im) {C : ℂ}
    (hC : C ≠ 0) :
    IntervalIntegrable (fun θ : ℝ => Real.log ‖C * (jacobiThetaOneTau ((θ / 2 : ℝ) : ℂ) τ /
      jacobiThetaFourTau ((θ / 2 : ℝ) : ℂ) τ)‖) volume 0 (2 * π) ∧
    ∫ θ in (0 : ℝ)..2 * π, Real.log ‖C * (jacobiThetaOneTau ((θ / 2 : ℝ) : ℂ) τ /
      jacobiThetaFourTau ((θ / 2 : ℝ) : ℂ) τ)‖ = 2 * π * (Real.log ‖C‖ - π * τ.im / 4) := by
  have hpi : 0 ≤ 2 * π := by positivity
  have heq : Set.EqOn (fun θ : ℝ => Real.log ‖C‖ + logNormThetaOneDivFour τ (circleMap 0 1 θ))
      (fun θ : ℝ => Real.log ‖C * (jacobiThetaOneTau ((θ / 2 : ℝ) : ℂ) τ /
        jacobiThetaFourTau ((θ / 2 : ℝ) : ℂ) τ)‖) (Set.uIoo 0 (2 * π)) := by
    intro θ hθ
    rw [Set.uIoo_of_le hpi] at hθ
    exact (log_norm_mul_jacobiThetaOneTau_div hτ hC θ (circleMap_ne_one_of_mem_Ioo hθ)).symm
  have hi : IntervalIntegrable (fun θ : ℝ => Real.log ‖C‖ +
      logNormThetaOneDivFour τ (circleMap 0 1 θ)) volume 0 (2 * π) :=
    intervalIntegrable_const.add (circleIntegrable_logNormThetaOneDivFour hτ)
  refine ⟨hi.congr_uIoo heq, ?_⟩
  rw [← intervalIntegral.integral_congr_uIoo heq, intervalIntegral.integral_add
    intervalIntegrable_const (circleIntegrable_logNormThetaOneDivFour hτ),
    intervalIntegral.integral_const]
  have h := circleAverage_logNormThetaOneDivFour hτ
  rw [circleAverage_def, smul_eq_mul] at h
  have hp : (2 * π : ℝ) ≠ 0 := by positivity
  have h' : ∫ θ in (0 : ℝ)..2 * π, logNormThetaOneDivFour τ (circleMap 0 1 θ) =
      2 * π * -(π * τ.im / 4) := by
    rw [← h]; field_simp
  rw [h', smul_eq_mul, sub_zero]
  ring

end DLMF.Theta
