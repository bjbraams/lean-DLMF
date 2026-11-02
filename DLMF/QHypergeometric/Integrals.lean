/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.QGamma
public import DLMF.QHypergeometric.Calculus
public import DLMF.QSeries.RamanujanPsi

/-!
# `q`-beta integrals (DLMF §17.13)

This file evaluates the two-ended and bilateral Jackson `q`-beta integrals and the ordinary
Mellin `q`-beta integral of DLMF §17.13.

## Main definitions

* `jacksonBetaKernel`: the two-ended Jackson `q`-beta kernel.
* `mellinQBetaValue`: the Gamma quotient of DLMF 17.13.3, filled at its removable points.

## Main results

* `jacksonBeta_integral`, `jacksonBeta_integral_qGamma`: the two-ended `q`-beta integral and
  its `q`-Gamma normalization (DLMF 17.13.1–17.13.2).
* `mellinQBeta_integral`: the ordinary Mellin `q`-beta integral (DLMF 17.13.3), with
  `mellinQBetaValue_eq` and `tendsto_mellinQBetaValue` for the filled Gamma quotient.
* `bilateralJacksonBeta_integral`: the bilateral Jackson `q`-beta integral (DLMF 17.13.4).

## Implementation notes

Finite and bilateral Jackson integrals reuse `QSeries.jacksonIntegral` through the adapters
in `DLMF.QHypergeometric.Calculus`. Every evaluated integral asserts convergence of its
defining series, and the ordinary Mellin integral asserts Bochner integrability. The Gamma
quotient of DLMF 17.13.3 is filled by its complex-parameter limit at removable
positive-integer values of `α`; the literal totalized `0/0` would be false.
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
    (hden : QDenominatorRegular [a,b,-b*c/d,-a*d/c] q) :
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
    (hden : QDenominatorRegular [-((q:ℂ)^β)*c/d,-((q:ℂ)^α)*d/c] q) :
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
private lemma continuousAt_qGamma_and_ne_zero (q : ℝ) (hq0 : 0<q) (hq1 : q<1) (x : ℂ)
    (hx : 0<x.re) :
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
  have h1 := continuousAt_qGamma_and_ne_zero q hq0 hq1 (1-α) (by simp; linarith)
  have h2 := continuousAt_qGamma_and_ne_zero q hq0 hq1 (α+β) (by simp; linarith)
  have hG1 : ∀ m : ℕ, α≠-m := fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0:ℝ)≤m)]
  have hG2 : ∀ m : ℕ, 1-α≠-m := fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0:ℝ)≤m)]
  have hc : ContinuousAt
      (fun a : ℂ => Complex.Gamma a * Complex.Gamma (1-a) * DLMF.QSeries.qGamma q β /
      (DLMF.QSeries.qGamma q (1-a) * DLMF.QSeries.qGamma q (a+β))) α := by
    refine ((((Complex.differentiableAt_Gamma α hG1).continuousAt).mul
      (((Complex.differentiableAt_Gamma (1-α) hG2).continuousAt).comp
        (continuousAt_const.sub continuousAt_id))).mul continuousAt_const).div
      ((h1.1.comp (continuousAt_const.sub continuousAt_id)).mul
        (ContinuousAt.comp (x:=α) (f:=fun a : ℂ => a+β) h2.1
            (continuousAt_id.add continuousAt_const))) (mul_ne_zero h1.2 h2.2)
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

/-- The ordinary Mellin q-beta integral, including the removable integer-alpha cases. -/
@[dlmf 17.13.E3]
theorem mellinQBeta_integral (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (α β : ℂ) (hα : 0<α.re) (hβ : 0<β.re) :
    let f := fun t : ℝ => (t:ℂ)^(α-1) *
      qPochhammerInf (-(t:ℂ)*(q:ℂ)^(α+β)) q / qPochhammerInf (-(t:ℂ)) q
    IntegrableOn f (Ioi 0) ∧ (∫ t in Ioi (0:ℝ), f t) = mellinQBetaValue q α β := by
  sorry

/-- `(a q^n;q)_∞ = (a;q)_∞ / (a;q)_n` for every integer `n`, when `(a;q)_∞ ≠ 0`. -/
private lemma qPochhammerInf_mul_zpow {a q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : ∀ k : ℤ, 1 - a * q ^ k ≠ 0) (n : ℤ) :
    qPochhammerInf (a * q ^ n) q = qPochhammerInf a q / qPochhammerInt a q n := by
  rcases n with k | m
  · have hk : qPochhammer a q k ≠ 0 := qPochhammer_ne_zero_of_factors hq
      (fun j => by simpa using ha j) k
    rw [Int.ofNat_eq_natCast, zpow_natCast, qPochhammerInt_natCast,
      qPochhammerInf_mul_qPochhammer hq (a := a) k]
    field_simp
  · have hsplit := qPochhammerInf_mul_qPochhammer hq (a := a * (q ^ (m + 1))⁻¹) (m + 1)
    have hbq : a * (q ^ (m + 1))⁻¹ * q ^ (m + 1) = a := by field_simp
    rw [hbq] at hsplit
    have hqi : q ^ (-((m : ℤ) + 1)) = (q ^ (m + 1))⁻¹ := by rw [zpow_neg]; norm_cast
    rw [zpow_negSucc, qPochhammerInt_negSucc, hqi, hsplit, div_inv_eq_mul]
    ring

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
  intro f
  have hqc0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hqn : ‖(q : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hnpow : ∀ s : ℂ, ‖(q : ℂ) ^ s‖ = q ^ s.re := fun s =>
    Complex.norm_cpow_eq_rpow_re_of_pos hq0 s
  set z : ℂ := (q : ℂ) ^ α with hz
  set b : ℂ := -c * (q : ℂ) ^ (α + β) with hb
  have hz0 : z ≠ 0 := by simp [hz, hqc0]
  have hzn : ‖z‖ < 1 := by rw [hz, hnpow]; exact Real.rpow_lt_one hq0.le hq1 hα
  have ha0 : -c ≠ 0 := neg_ne_zero.mpr hc
  have ha : ∀ n : ℕ, -c ≠ (q : ℂ) ^ (n + 1) := fun n h => hden ((n + 1 : ℕ) : ℤ) (by
    rw [zpow_natCast, ← h, neg_neg])
  have hbaz : ‖b‖ < ‖-c * z‖ := by
    rw [hb, hz, norm_mul, norm_mul, hnpow, hnpow, add_re]
    refine mul_lt_mul_of_pos_left ?_ (norm_pos_iff.mpr ha0)
    rw [Real.rpow_add hq0]
    exact mul_lt_of_lt_one_right (Real.rpow_pos_of_pos hq0 _) (Real.rpow_lt_one hq0.le hq1 hβ)
  have hfac : ∀ k : ℤ, 1 - (-c) * (q : ℂ) ^ k ≠ 0 := fun k h => hden (-k) (by
    have hk : (q : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hqc0
    rw [zpow_neg]; field_simp; linear_combination h)
  have hAinf : qPochhammerInf (-c) q ≠ 0 := qPochhammerInf_ne_zero hqn (fun k => by
    simpa using hfac k)
  -- the summand
  have hterm : ∀ n : ℤ, (q : ℂ) ^ n * f ((q : ℂ) ^ n) =
      RamanujanPsi.term (-c) q z b n / qPochhammerInf (-c) q := by
    intro n
    have hpow : ((q : ℂ) ^ n) ^ (α - 1) = ((q : ℂ) ^ (α - 1)) ^ n := by
      have hqn0 : ((q : ℂ) ^ n) ≠ 0 := zpow_ne_zero _ hqc0
      rw [Complex.cpow_def_of_ne_zero hqn0, Complex.cpow_def_of_ne_zero hqc0,
        ← Complex.exp_int_mul, ← Complex.ofReal_zpow, ← Complex.ofReal_log (zpow_pos hq0 n).le,
        Real.log_zpow, ← Complex.ofReal_log hq0.le]
      push_cast
      ring_nf
    have hinf := qPochhammerInf_mul_zpow hqc0 hqn hfac n
    have hcn : qPochhammerInt (-c) q n ≠ 0 := by
      intro h0
      have hne : qPochhammerInf (-c * (q : ℂ) ^ n) q ≠ 0 := qPochhammerInf_ne_zero hqn
        (fun j => by
          have := hfac (n + j)
          rwa [zpow_add₀ hqc0, zpow_natCast, ← mul_assoc] at this)
      rw [hinf, h0, div_zero] at hne
      exact hne rfl
    have hzq : ((q : ℂ) ^ (α - 1)) ^ n * (q : ℂ) ^ n = z ^ n := by
      have h := Complex.cpow_add (α - 1) 1 hqc0
      rw [Complex.cpow_one, sub_add_cancel] at h
      rw [← mul_zpow, hz, ← h]
    have hbq : -c * (q : ℂ) ^ n * (q : ℂ) ^ (α + β) = b * (q : ℂ) ^ n := by rw [hb]; ring
    simp only [f]
    rw [hpow, hbq, hinf]
    unfold RamanujanPsi.term
    rw [← hzq]
    field_simp
  have hsum := RamanujanPsi.summable_term hqc0 hqn ha0 ha hz0 hzn hbaz
  have hval := RamanujanPsi.tsum_term_eq_prodSide hqc0 hqn ha0 ha hz0 hzn hbaz
  have hS : Summable (fun n : ℤ => (q:ℂ)^n * f ((q:ℂ)^n)) := by
    simpa only [hterm] using hsum.div_const (qPochhammerInf (-c) q)
  refine ⟨hS, ?_⟩
  unfold jacksonBilateral
  rw [tsum_congr hterm, tsum_div_const, hval]
  unfold RamanujanPsi.prodSide DLMF.Gamma.qBeta qGamma
  have e1 : b / -c = (q : ℂ) ^ (α + β) := by rw [hb]; field_simp
  have e2 : (q : ℂ) / (-c * z) = -(q : ℂ) ^ (1 - α) / c := by
    rw [hz, Complex.cpow_sub _ _ hqc0, Complex.cpow_one]; field_simp
  have e3 : b / (-c * z) = (q : ℂ) ^ β := by
    have hqa : (q : ℂ) ^ α ≠ 0 := by simp [hqc0]
    rw [hb, hz, Complex.cpow_add _ _ hqc0]; field_simp
  have e4 : (q : ℂ) / -c = -(q : ℂ) / c := by ring
  rw [e1, e2, e3, e4, hz]
  have h1q : (1 : ℂ) - q ≠ 0 := one_sub_ne_zero_of_norm_lt_one hqn
  have hpw : (1 - (q : ℂ)) ^ (1 - α) * (1 - (q : ℂ)) ^ (1 - β) =
      (1 - (q : ℂ)) ^ (1 - (α + β)) * (1 - q) := by
    rw [← Complex.cpow_add _ _ h1q]
    conv_rhs => rw [show (1 - (q : ℂ)) ^ (1 - (α + β)) * (1 - q) =
      (1 - (q : ℂ)) ^ (1 - (α + β)) * (1 - q) ^ (1 : ℂ) by rw [Complex.cpow_one]]
    rw [← Complex.cpow_add _ _ h1q]
    ring_nf
  have hpos : ∀ s : ℂ, 0 < s.re → qPochhammerInf ((q : ℂ) ^ s) q ≠ 0 := fun s hs =>
    qPochhammerInf_ne_zero_of_norm_lt_one (by rw [hnpow]; exact Real.rpow_lt_one hq0.le hq1 hs) hqn
  have hA := hpos α hα
  have hB := hpos β hβ
  have hAB := hpos (α + β) (by simp; linarith)
  have hQ : qPochhammerInf (q : ℂ) q ≠ 0 := by
    simpa using hpos 1 (by simp)
  have hQA : qPochhammerInf (-(q : ℂ) / c) q ≠ 0 := by
    rw [← e4]; exact RamanujanPsi.qPochhammerInf_q_div_ne_zero hqn ha0 ha
  have hc1 : ∀ s : ℂ, (1 - (q : ℂ)) ^ s ≠ 0 := fun s => by
    simp [h1q]
  have hc2 := hc1 (1 - α)
  have hc3 := hc1 (1 - β)
  have hc4 := hc1 (1 - (α + β))
  generalize qPochhammerInf (q : ℂ) q = Q at *
  generalize qPochhammerInf ((q : ℂ) ^ (α + β)) q = PAB at *
  generalize qPochhammerInf ((q : ℂ) ^ α) q = PA at *
  generalize qPochhammerInf ((q : ℂ) ^ β) q = PB at *
  generalize qPochhammerInf (-c * (q : ℂ) ^ α) q = X at *
  generalize qPochhammerInf (-(q : ℂ) ^ (1 - α) / c) q = Y at *
  generalize qPochhammerInf (-(q : ℂ) / c) q = W at *
  generalize qPochhammerInf (-c) q = V at *
  generalize (1 - (q : ℂ)) ^ (1 - α) = R1 at *
  generalize (1 - (q : ℂ)) ^ (1 - β) = R2 at *
  generalize (1 - (q : ℂ)) ^ (1 - (α + β)) = R3 at *
  field_simp
  linear_combination (-(X * Y)) * hpw

open scoped Real in
/-- The Gamma quotient has a genuine removable limit, including positive integer alpha. -/
@[dlmf 17.13.E3]
theorem tendsto_mellinQBetaValue (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (α β : ℂ) (hα : 0 < α.re) (hβ : 0 < β.re) :
    Tendsto (fun a : ℂ =>
      Complex.Gamma a * Complex.Gamma (1-a) * DLMF.QSeries.qGamma q β /
        (DLMF.QSeries.qGamma q (1-a) * DLMF.QSeries.qGamma q (a+β)))
      (𝓝[≠] α) (𝓝 (mellinQBetaValue q α β)) := by
  have hqc0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hqn : ‖(q : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have h1q : (1 : ℂ) - q ≠ 0 := one_sub_ne_zero_of_norm_lt_one hqn
  have hP := qPochhammerInf_analytic hqn
  have hQ : qPochhammerInf (q : ℂ) q ≠ 0 := qPochhammerInf_ne_zero hqn fun n => by
    simpa [← pow_succ'] using one_sub_ne_zero_of_norm_lt_one (norm_pow (q : ℂ) (n + 1) ▸
      pow_lt_one₀ (norm_nonneg _) hqn (Nat.succ_ne_zero n))
  -- the entire factor
  let E : ℂ → ℂ := fun a => qGamma q β * (qPochhammerInf ((q : ℂ) ^ (1 - a)) q *
    (qPochhammerInf (q : ℂ) q * (1 - (q : ℂ)) ^ (1 - (1 - a)))⁻¹) * (qGamma q (a + β))⁻¹
  have hinv : ∀ x : ℂ, (qGamma q x)⁻¹ =
      qPochhammerInf ((q : ℂ) ^ x) q * (qPochhammerInf (q : ℂ) q * (1 - (q : ℂ)) ^ (1 - x))⁻¹ := by
    intro x; unfold qGamma; rw [mul_inv, inv_div, mul_inv]; ring
  have hg : ∀ a : ℂ, Complex.Gamma a * Complex.Gamma (1-a) * qGamma q β /
      (qGamma q (1-a) * qGamma q (a+β)) = π / Complex.sin (π * a) * E a := by
    intro a
    rw [Complex.Gamma_mul_Gamma_one_sub]
    simp only [E, ← hinv]
    rw [div_eq_mul_inv, mul_inv]
    ring
  have hE : DifferentiableAt ℂ E α := by
    have hpos : qPochhammerInf ((q : ℂ) ^ (α + β)) q ≠ 0 :=
      qPochhammerInf_ne_zero_of_norm_lt_one (by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0]
        exact Real.rpow_lt_one hq0.le hq1 (by simp; linarith)) hqn
    have hG : DifferentiableAt ℂ (fun a => qGamma q (a + β)) α := by
      unfold qGamma
      have h1 : DifferentiableAt ℂ (fun a : ℂ => qPochhammerInf ((q : ℂ) ^ (a + β)) q) α :=
        (hP _ (mem_univ _)).differentiableAt.comp α
          ((differentiableAt_id.add_const β).const_cpow (Or.inl hqc0))
      have h2 : DifferentiableAt ℂ (fun a : ℂ => (1 - (q : ℂ)) ^ (1 - (a + β))) α :=
        (differentiableAt_const _ |>.sub (differentiableAt_id.add_const β)).const_cpow
          (Or.inl h1q)
      exact ((differentiableAt_const _).div h1 hpos).mul h2
    have hGne : qGamma q (α + β) ≠ 0 := by
      unfold qGamma
      exact mul_ne_zero (div_ne_zero hQ hpos) (by simp [h1q])
    refine ((differentiableAt_const _).mul ?_).mul (hG.inv hGne)
    refine DifferentiableAt.mul ?_ (DifferentiableAt.inv ?_ ?_)
    · exact (hP _ (mem_univ _)).differentiableAt.comp α
        ((differentiableAt_const _ |>.sub differentiableAt_id).const_cpow (Or.inl hqc0))
    · exact (differentiableAt_const _).mul ((differentiableAt_const _ |>.sub
        (differentiableAt_const _ |>.sub differentiableAt_id)).const_cpow (Or.inl h1q))
    · exact mul_ne_zero hQ (by simp [h1q])
  suffices h : ∃ L, Tendsto (fun a : ℂ => π / Complex.sin (π * a) * E a) (𝓝[≠] α) (𝓝 L) by
    obtain ⟨L, hL⟩ := h
    have hL' : Tendsto (fun a : ℂ => Complex.Gamma a * Complex.Gamma (1-a) * qGamma q β /
        (qGamma q (1-a) * qGamma q (a+β))) (𝓝[≠] α) (𝓝 L) := by
      simpa only [hg] using hL
    exact tendsto_nhds_limUnder ⟨L, hL'⟩
  let S : ℂ → ℂ := fun a => Complex.sin (π * a)
  have hS : DifferentiableAt ℂ S α :=
    (differentiableAt_id.const_mul (π : ℂ)).csin
  by_cases hs : Complex.sin (π * α) = 0
  · obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have hαk : α = k := by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      apply mul_left_cancel₀ hπ; rw [hk]; ring
    have hk1 : 1 ≤ k := by
      have : (0 : ℝ) < k := by simpa [hαk] using hα
      exact_mod_cast this
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m + 1 : ℕ) := ⟨(k - 1).toNat, by omega⟩
    have hE0 : E α = 0 := by
      have hz : qPochhammerInf ((q : ℂ) ^ (1 - α)) q = 0 := by
        rw [qPochhammerInf_mul_qPochhammer hqn (m + 1), qPochhammer_succ]
        have : (q : ℂ) ^ (1 - α) * (q : ℂ) ^ m = 1 := by
          rw [hαk, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hqc0]
          push_cast; ring_nf; simp
        simp [this]
      simp [E, hz]
    have hdS : deriv S α ≠ 0 := by
      have : deriv S α = π * Complex.cos (π * α) := by
        have h := (((hasDerivAt_id α).const_mul (π : ℂ)).csin).deriv
        simp only [S]
        rw [show (fun a : ℂ => Complex.sin (π * a)) = fun a => Complex.sin (π * id a) from rfl, h]
        simp only [id]; ring
      rw [this]
      refine mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) ?_
      intro h
      have h2 := Complex.sin_sq_add_cos_sq (π * α)
      rw [hs, h] at h2
      norm_num at h2
    refine ⟨π * deriv E α / deriv S α, ?_⟩
    have h1 := (continuousAt_dslope_same.mpr hE).tendsto.mono_left (nhdsWithin_le_nhds (s := {α}ᶜ))
    have h2 := (continuousAt_dslope_same.mpr hS).tendsto.mono_left (nhdsWithin_le_nhds (s := {α}ᶜ))
    rw [dslope_same] at h1 h2
    refine ((h1.const_mul (π : ℂ)).div h2 hdS).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : a ≠ α := ha
    have hsub : a - α ≠ 0 := sub_ne_zero.mpr ha'
    simp only [Pi.div_apply]
    rw [dslope_of_ne _ ha', dslope_of_ne _ ha', slope_def_field, slope_def_field, hE0]
    simp only [S, hs, sub_zero]
    field_simp
  · refine ⟨π / Complex.sin (π * α) * E α, ?_⟩
    exact ((continuousAt_const.div hS.continuousAt hs).mul hE.continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds

end DLMF.QHypergeometric
