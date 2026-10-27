/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Calculus
public import DLMF.Gamma.QGamma

/-!
# q-beta integrals (DLMF §17.13)

Finite and bilateral Jackson integrals reuse `QSeries.jacksonIntegral` through
the adapters in `Calculus`. Every evaluated integral asserts convergence of its
defining series. The ordinary Mellin integral asserts Bochner integrability.
The Gamma quotient of 17.13.3 is filled by its complex-parameter limit at
removable positive-integer alpha values; the literal totalized `0/0` would be false.
-/

@[expose] public noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- The two-ended Jackson q-beta kernel. -/
def jacksonBetaKernel (a b c d q x : ℂ) : ℂ :=
  qPochhammerInf (-q*x/c) q * qPochhammerInf (q*x/d) q /
    (qPochhammerInf (-a*x/c) q * qPochhammerInf (b*x/d) q)

/-- The complex two-ended q-beta integral, with endpoint-series convergence. -/
@[dlmf 17.13.E1]
theorem jacksonBeta_integral (a b c d q : ℂ) (hq : ‖q‖<1)
    (hc : c≠0) (hd : d≠0) (hcd : c+d≠0)
    (hden : qDenominatorRegular [a,b,-b*c/d,-a*d/c] q) :
    Summable (fun n : ℕ => jacksonBetaKernel a b c d q (d*q^n)*q^n) ∧
    Summable (fun n : ℕ => jacksonBetaKernel a b c d q (-c*q^n)*q^n) ∧
    jacksonBetween q (-c) d (jacksonBetaKernel a b c d q) =
      (1-q) * qPochhammerInf q q * qPochhammerInf (a*b) q * c*d *
        qPochhammerInf (-c/d) q * qPochhammerInf (-d/c) q /
        (qPochhammerInf a q * qPochhammerInf b q * (c+d) *
          qPochhammerInf (-b*c/d) q * qPochhammerInf (-a*d/c) q) := by
  sorry

/-- The q-Gamma normalization of the two-ended Jackson integral. -/
@[dlmf 17.13.E2]
theorem jacksonBeta_integral_qGamma (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (α β c d : ℂ) (hα : 0<α.re) (hβ : 0<β.re)
    (hc : c≠0) (hd : d≠0) (hcd : c+d≠0)
    (hden : qDenominatorRegular [-((q:ℂ)^β)*c/d,-((q:ℂ)^α)*d/c] q) :
    Summable (fun n : ℕ => jacksonBetaKernel ((q:ℂ)^α) ((q:ℂ)^β) c d q (d*q^n)*q^n) ∧
    Summable (fun n : ℕ => jacksonBetaKernel ((q:ℂ)^α) ((q:ℂ)^β) c d q (-c*q^n)*q^n) ∧
    jacksonBetween q (-c) d (jacksonBetaKernel ((q:ℂ)^α) ((q:ℂ)^β) c d q) =
      DLMF.Gamma.qBeta q α β * (c*d/(c+d)) *
        qPochhammerInf (-c/d) q * qPochhammerInf (-d/c) q /
        (qPochhammerInf (-((q:ℂ)^β)*c/d) q * qPochhammerInf (-((q:ℂ)^α)*d/c) q) := by
  sorry

/-- The meromorphically interpreted Gamma quotient in the ordinary q-beta integral. -/
def mellinQBetaValue (q : ℝ) (α β : ℂ) : ℂ :=
  limUnder (𝓝[≠] α) (fun a : ℂ =>
    Complex.Gamma a * Complex.Gamma (1-a) * DLMF.QSeries.qGamma q β /
      (DLMF.QSeries.qGamma q (1-a) * DLMF.QSeries.qGamma q (a+β)))

/-- The q-Gamma function is continuous and nonzero on the right half-plane. -/
lemma qaR4_qGamma_cont_ne (q : ℝ) (hq0 : 0<q) (hq1 : q<1) (x : ℂ) (hx : 0<x.re) :
    ContinuousAt (DLMF.QSeries.qGamma (q:ℂ)) x ∧ DLMF.QSeries.qGamma (q:ℂ) x≠0 := by
  have hqn : ‖(q:ℂ)‖<1 := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq0]; exact hq1
  have hqc : (q:ℂ)≠0 := by exact_mod_cast hq0.ne'
  have hq1c : (1:ℂ)-q≠0 := one_sub_ne_zero_of_norm_lt_one hqn
  have hpow : ∀ y : ℂ, 0<y.re → ∀ n : ℕ, 1-(q:ℂ)^y*(q:ℂ)^n≠0 := by
    intro y hy n
    apply one_sub_ne_zero_of_norm_lt_one
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hq0,norm_pow]
    have h1 : q^y.re<1 := Real.rpow_lt_one hq0.le hq1 hy
    have h2 : ‖(q:ℂ)‖^n≤1 := pow_le_one₀ (norm_nonneg _) hqn.le
    calc q^y.re*‖(q:ℂ)‖^n≤q^y.re*1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ <1 := by simpa using h1
  have hA : qPochhammerInf (q:ℂ) (q:ℂ)≠0 := qPochhammerInf_ne_zero hqn fun n => by
    simpa using hpow 1 (by simp) n
  have hB : qPochhammerInf ((q:ℂ)^x) (q:ℂ)≠0 := qPochhammerInf_ne_zero hqn (hpow x hx)
  have hcB : ContinuousAt (fun y : ℂ => qPochhammerInf ((q:ℂ)^y) (q:ℂ)) x :=
    ((qPochhammerInf_analytic hqn ((q:ℂ)^x) (Set.mem_univ _)).continuousAt).comp
      (continuousAt_const_cpow hqc)
  refine ⟨?_,?_⟩
  · unfold DLMF.QSeries.qGamma
    exact (continuousAt_const.div hcB hB).mul
      ((continuousAt_const_cpow hq1c).comp (continuousAt_const.sub continuousAt_id))
  · unfold DLMF.QSeries.qGamma
    exact mul_ne_zero (div_ne_zero hA hB) fun h => hq1c ((cpow_eq_zero_iff _ _).mp h).1

/-- On its initial regular strip the filled value is the printed Gamma quotient. -/
@[dlmf 17.13.E3]
theorem mellinQBetaValue_eq (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (α β : ℂ) (hα0 : 0<α.re) (hα1 : α.re<1) (hβ : 0<β.re) :
    mellinQBetaValue q α β =
      Complex.Gamma α * Complex.Gamma (1-α) * DLMF.QSeries.qGamma q β /
        (DLMF.QSeries.qGamma q (1-α) * DLMF.QSeries.qGamma q (α+β)) := by
  have h1 := qaR4_qGamma_cont_ne q hq0 hq1 (1-α) (by simp; linarith)
  have h2 := qaR4_qGamma_cont_ne q hq0 hq1 (α+β) (by simp; linarith)
  have hG1 : ∀ m : ℕ, α≠-m := fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0:ℝ)≤m)]
  have hG2 : ∀ m : ℕ, 1-α≠-m := fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0:ℝ)≤m)]
  have hc : ContinuousAt (fun a : ℂ => Complex.Gamma a * Complex.Gamma (1-a) * DLMF.QSeries.qGamma q β /
      (DLMF.QSeries.qGamma q (1-a) * DLMF.QSeries.qGamma q (a+β))) α := by
    refine ((((Complex.differentiableAt_Gamma α hG1).continuousAt).mul
      (((Complex.differentiableAt_Gamma (1-α) hG2).continuousAt).comp
        (continuousAt_const.sub continuousAt_id))).mul continuousAt_const).div
      ((h1.1.comp (continuousAt_const.sub continuousAt_id)).mul
        (ContinuousAt.comp (x:=α) (f:=fun a : ℂ => a+β) h2.1 (continuousAt_id.add continuousAt_const))) (mul_ne_zero h1.2 h2.2)
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

/-- The ordinary Mellin q-beta integral, including the removable integer-alpha cases. -/
@[dlmf 17.13.E3]
theorem mellinQBeta_integral (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (α β : ℂ) (hα : 0<α.re) (hβ : 0<β.re) :
    let f := fun t : ℝ => (t:ℂ)^(α-1) *
      qPochhammerInf (-(t:ℂ)*(q:ℂ)^(α+β)) q / qPochhammerInf (-(t:ℂ)) q
    IntegrableOn f (Ioi 0) ∧ (∫ t in Ioi (0:ℝ), f t) = mellinQBetaValue q α β := by
  sorry

/-- The bilateral Jackson q-beta integral with a general nonzero scale. -/
@[dlmf 17.13.E4]
theorem bilateralJacksonBeta_integral (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (α β c : ℂ) (hα : 0<α.re) (hβ : 0<β.re) (hc : c≠0)
    (hden : ∀ k : ℤ, c≠ -((q:ℂ)^k)) :
    let f := fun t : ℂ => t^(α-1) *
      qPochhammerInf (-c*t*(q:ℂ)^(α+β)) q / qPochhammerInf (-c*t) q
    Summable (fun n : ℤ => (q:ℂ)^n * f ((q:ℂ)^n)) ∧
    jacksonBilateral q f =
      DLMF.Gamma.qBeta q α β * qPochhammerInf (-c*(q:ℂ)^α) q *
        qPochhammerInf (-(q:ℂ)^(1-α)/c) q /
        (qPochhammerInf (-c) q * qPochhammerInf (-(q:ℂ)/c) q) := by
  sorry

/-- The Gamma quotient has a genuine removable limit, including positive integer alpha. -/
@[dlmf 17.13.E3]
theorem tendsto_mellinQBetaValue (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (α β : ℂ) (hα : 0 < α.re) (hβ : 0 < β.re) :
    Tendsto (fun a : ℂ =>
      Complex.Gamma a * Complex.Gamma (1-a) * DLMF.QSeries.qGamma q β /
        (DLMF.QSeries.qGamma q (1-a) * DLMF.QSeries.qGamma q (a+β)))
      (𝓝[≠] α) (𝓝 (mellinQBetaValue q α β)) := by
  sorry


end DLMF.QHypergeometric
