/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.SeriesAndZeros
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.PSeriesComplex

/-!
# Theta functions: integrals (DLMF §20.10)

Mellin transforms (20.10.1–20.10.3) and Laplace transforms (20.10.4–20.10.5) with respect to the
lattice parameter. Integrals are Bochner integrals over `(0, ∞)` and are stated together with
integrability, so that Lean's convention `∫ = 0` for non-integrable functions plays no role.
Powers `x^{s-1}`, `2^s`, `π^{-s/2}` and `√s` are principal complex powers.

**Exceptional point (20.10.3).** For `Re s > 0` the right side `(1 - 2^{1-s}) π^{-s/2} Γ(s/2) ζ(s)`
is meant as its analytic continuation, which is removable at `s = 1`, where Mathlib's totalized
`riemannZeta 1` gives the wrong value `0`. We state 20.10.3 for `s ≠ 1` and the value at `s = 1`,
`∫₀^∞ (1 - θ₄(0|ix²)) dx = ln 2`, separately.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic

/-- Integrability of a pointwise sum with summable integrals of norms (helper). -/
lemma p20R1_integrableOn_of_hasSum {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ} {G : ℝ → ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hGm : AEStronglyMeasurable G (volume.restrict S))
    (hF : ∀ i, IntegrableOn (F i) S) (hsum : Summable fun i => ∫ x in S, ‖F i x‖)
    (hpt : ∀ x ∈ S, HasSum (fun i => F i x) (G x)) : IntegrableOn G S := by
  refine ⟨hGm, ?_⟩
  show ∫⁻ x in S, ‖G x‖ₑ < ⊤
  calc ∫⁻ x in S, ‖G x‖ₑ ≤ ∫⁻ x in S, ∑' i, ‖F i x‖ₑ := by
        refine setLIntegral_mono_ae' hS (Eventually.of_forall fun x hx => ?_)
        rw [← (hpt x hx).tsum_eq]; exact enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ x in S, ‖F i x‖ₑ :=
        lintegral_tsum fun i => (hF i).aestronglyMeasurable.enorm
    _ = ∑' i, ENNReal.ofReal (∫ x in S, ‖F i x‖) := by
        congr 1; funext i; exact (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
    _ = ENNReal.ofReal (∑' i, ∫ x in S, ‖F i x‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun _ => norm_nonneg _) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Mellin transform of a Dirichlet-type exponential series, with convergence (helper). -/
lemma p20R1_mellin_series {a : ℕ → ℂ} {q : ℕ → ℝ} {F : ℝ → ℂ} {s : ℂ} (hq : ∀ n, 0 < q n)
    (hs : 0 < s.re) (hFc : ContinuousOn F (Set.Ioi 0))
    (hF : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun n => a n * Real.exp (-π * q n * t)) (F t))
    (h_sum : Summable fun n => ‖a n‖ / q n ^ s.re) :
    MellinConvergent F s ∧
      HasSum (fun n => (π : ℂ) ^ (-s) * Gamma s * a n / q n ^ s) (mellin F s) := by
  refine ⟨?_, hasSum_mellin_pi_mul (fun n => Or.inr (hq n)) hs hF h_sum⟩
  have hint : ∀ n, IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * (a n * Real.exp (-π * q n * t)))
      (Set.Ioi 0) := by
    intro n
    have hb : 0 < π * q n := mul_pos Real.pi_pos (hq n)
    have hr := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s.re - 1) (p := 1) (b := π * q n)
      (by linarith) one_pos hb
    refine (hr.norm.const_mul ‖a n‖).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have ht' : (0 : ℝ) < t := ht
      exact ((continuousAt_ofReal_cpow_const _ _ (Or.inr ht'.ne')).mul
        (by fun_prop)).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht' : (0 : ℝ) < t := ht
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht', norm_real, Real.norm_eq_abs,
        Real.abs_exp, Real.rpow_one, norm_mul, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
      simp only [sub_re, one_re]
      rw [show -π * q n * t = -(π * q n) * t by ring]
      nlinarith [norm_nonneg (a n), Real.rpow_nonneg ht'.le (s.re - 1),
        Real.exp_pos (-(π * q n) * t)]
  refine p20R1_integrableOn_of_hasSum (F := fun n t => (t : ℂ) ^ (s - 1) * (a n *
    Real.exp (-π * q n * t))) measurableSet_Ioi ?_ hint ?_ (fun t ht => (hF t ht).mul_left _)
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht' : (0 : ℝ) < t := ht
    exact ((continuousAt_ofReal_cpow_const _ _ (Or.inr ht'.ne')).continuousWithinAt.smul
      (hFc t ht))
  · have : ∀ n, ∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * (a n * Real.exp (-π * q n * t))‖ =
        Real.Gamma s.re * (‖a n‖ / (π * q n) ^ s.re) := by
      intro n
      have hb : 0 < π * q n := mul_pos Real.pi_pos (hq n)
      rw [← setIntegral_congr_fun measurableSet_Ioi (f := fun t : ℝ =>
        ‖a n‖ * (t ^ (s.re - 1) * Real.exp (-((π * q n) * t)))), integral_const_mul,
        Real.integral_rpow_mul_exp_neg_mul_Ioi hs hb, one_div, Real.inv_rpow hb.le]
      · ring
      · intro t ht
        have ht' : (0 : ℝ) < t := ht
        simp only
        rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht', norm_real, Real.norm_eq_abs,
          Real.abs_exp]
        simp only [sub_re, one_re]
        rw [show -π * q n * t = -(π * q n * t) by ring]
        ring
    simp_rw [this]
    refine Summable.mul_left _ ?_
    convert h_sum.mul_left ((π ^ s.re)⁻¹) using 1
    funext n
    rw [Real.mul_rpow Real.pi_pos.le (hq n).le]
    field_simp

/-- `((n+1)²)^{s/2} = (n+1)^s` (helper). -/
lemma p20R1_sq_cpow_half (x : ℝ) (hx : 0 < x) (s : ℂ) :
    (((x ^ 2 : ℝ)) : ℂ) ^ (s / 2) = (x : ℂ) ^ s := by
  rw [ofReal_pow, ← cpow_nat_mul' (x := (x : ℂ)) (n := 2)]
  · congr 1; push_cast; ring
  all_goals rw [arg_ofReal_of_nonneg hx.le]; linarith [Real.pi_pos]

/-- The Mellin transform in `x²` (helper for 20.10.1–20.10.3): for `g` continuous on `(0,∞)` with
`g t = ∑ aₙ e^{-π qₙ t}`, `∫₀^∞ x^{s-1} g(x²) dx = ½ ∑ π^{-s/2} Γ(s/2) aₙ / qₙ^{s/2}`. -/
lemma p20R1_mellin_sq {a : ℕ → ℂ} {q : ℕ → ℝ} {g : ℝ → ℂ} {s : ℂ} (hq : ∀ n, 0 < q n)
    (hs : 0 < s.re) (hgc : ContinuousOn g (Set.Ioi 0))
    (hg : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun n => a n * Real.exp (-π * q n * t)) (g t))
    (h_sum : Summable fun n => ‖a n‖ / q n ^ (s / 2).re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * g (x ^ 2)) (Set.Ioi 0) ∧
      HasSum (fun n => (π : ℂ) ^ (-(s / 2)) * Gamma (s / 2) * a n / q n ^ (s / 2) / 2)
        (∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * g (x ^ 2)) := by
  have hs2 : 0 < (s / 2).re := by rw [div_ofNat_re]; positivity
  obtain ⟨hM, hS⟩ := p20R1_mellin_series hq hs2 hgc hg h_sum
  have hcongr : Set.EqOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * g (x ^ 2))
      (fun x : ℝ => (x : ℂ) ^ (s - 1) • (fun t => g (t ^ (2 : ℝ))) x) (Set.Ioi 0) := by
    intro x _
    simp only [smul_eq_mul, Real.rpow_two]
  refine ⟨?_, ?_⟩
  · rw [integrableOn_congr_fun hcongr measurableSet_Ioi]
    exact (MellinConvergent.comp_rpow (f := g) (s := s) two_ne_zero).mpr hM
  · rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    have := mellin_comp_rpow g s 2
    simp only [mellin] at this ⊢
    rw [this]
    convert hS.div_const 2 using 1
    simp [mellin]
    ring

/-- Continuity of `t ↦ θ(0|it)`-type functions (helper). -/
lemma p20R1_cont_three (c : ℂ) : ContinuousOn (fun t : ℝ => jacobiThetaThreeTau c (I * t))
    (Set.Ioi 0) := by
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  have h1 : 0 < (I * (t : ℂ)).im := by simpa using ht'
  have := (differentiableAt_jacobiTheta₂_snd (c / π) h1).continuousAt
  have h2 : ContinuousAt (fun t : ℝ => jacobiTheta₂ (c / π) (I * t)) t :=
    ContinuousAt.comp (g := jacobiTheta₂ (c / π)) (f := fun t : ℝ => I * (t : ℂ)) this
      (by fun_prop)
  exact h2.continuousWithinAt

/-- `∑_{n≥0} (2n+1)^{-s} = (1 - 2^{-s}) ζ(s)` (helper). -/
lemma p20R1_odd_zeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => 1 / ((2 * n + 1 : ℕ) : ℂ) ^ s) ((1 - 2 ^ (-s)) * riemannZeta s) := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have hz := zeta_eq_tsum_one_div_nat_cpow hs
  have he : HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℂ) ^ s) (2 ^ (-s) * riemannZeta s) := by
    rw [hz]
    convert (hsum.hasSum.mul_left (2 ^ (-s))) using 1
    funext k
    rw [Nat.cast_mul, natCast_mul_natCast_cpow, Nat.cast_ofNat, cpow_neg, one_div, one_div,
      mul_inv]
  have ho := (hsum.comp_injective (fun a b h => by simpa using h :
    Function.Injective (fun k : ℕ => 2 * k + 1))).hasSum
  have h := tsum_even_add_odd (f := fun n : ℕ => 1 / (n : ℂ) ^ s)
    (hsum.comp_injective (fun a b h => by simpa using h : Function.Injective (fun k : ℕ => 2 * k)))
    (hsum.comp_injective (fun a b h => by simpa using h :
      Function.Injective (fun k : ℕ => 2 * k + 1)))
  rw [he.tsum_eq, ← hz] at h
  rw [show ((1 : ℂ) - 2 ^ (-s)) * riemannZeta s = ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℂ) ^ s by
    linear_combination -h]
  exact ho

/-- DLMF 20.10.1: `∫₀^∞ x^{s-1} θ₂(0|ix²) dx = (2^s - 1) π^{-s/2} Γ(s/2) ζ(s)`, `Re s > 1`. -/
@[dlmf 20.10.E1]
theorem mellin_jacobiThetaTwoNullTau {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * jacobiThetaTwoNullTau (I * x ^ 2))
        (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * jacobiThetaTwoNullTau (I * x ^ 2) =
        (2 ^ s - 1) * (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  have hgc : ContinuousOn (fun t : ℝ => jacobiThetaTwoNullTau (I * t)) (Set.Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : 0 < (I * (t : ℂ)).im := by simpa using ht'
    have hc := continuousAt_jacobiTheta₂ ((0 + π * (I * t) / 2) / π) h1
    have h2 : ContinuousAt (fun t : ℝ => jacobiTheta₂ ((0 + π * (I * t) / 2) / π) (I * t)) t :=
      ContinuousAt.comp (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2)
        (f := fun t : ℝ => (((0 : ℂ) + π * (I * t) / 2) / π, I * (t : ℂ))) hc (by fun_prop)
    have h3 : ContinuousAt (fun t : ℝ => cexp (π * I * (I * t) / 4 + I * 0) *
        jacobiTheta₂ ((0 + π * (I * t) / 2) / π) (I * t)) t := (by fun_prop : ContinuousAt
          (fun t : ℝ => cexp (π * I * (I * t) / 4 + I * 0)) t).mul h2
    exact h3.continuousWithinAt
  have hg : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun n : ℕ => (2 : ℂ) *
      Real.exp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t)) (jacobiThetaTwoNullTau (I * t)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h := jacobiThetaTwoTau_hasSum_cos 0 (τ := I * t) (by simpa using ht')
    convert h using 2 with n
    rw [mul_zero, cos_zero, mul_one, ofReal_exp]
    congr 2
    push_cast; ring_nf; rw [I_sq]; ring
  have hsum : Summable fun n : ℕ => ‖(2 : ℂ)‖ / (((n : ℝ) + 1 / 2) ^ 2) ^ (s / 2).re := by
    have h := (Real.summable_nat_rpow_inv.mpr hs)
    have h' := ((summable_nat_add_iff 1).mpr h).mul_left (2 * 2 ^ s.re)
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) h'
    rw [div_ofNat_re, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    push_cast
    rw [show (2 : ℝ) * (s.re / 2) = s.re by ring, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have h1 : (((n : ℝ) + 1) / 2) ^ s.re ≤ ((n : ℝ) + 1 / 2) ^ s.re :=
      Real.rpow_le_rpow (by positivity) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) hs0.le
    have hp : 0 < (((n : ℝ) + 1) / 2) ^ s.re := by positivity
    calc (2 : ℝ) / ((n : ℝ) + 1 / 2) ^ s.re ≤ 2 / (((n : ℝ) + 1) / 2) ^ s.re :=
          div_le_div_of_nonneg_left (by norm_num) hp h1
      _ = 2 * 2 ^ s.re * (((n : ℝ) + 1) ^ s.re)⁻¹ := by
          rw [Real.div_rpow (by positivity) (by norm_num)]
          field_simp
  obtain ⟨hI, hS⟩ := p20R1_mellin_sq (fun n => by positivity) hs0 hgc hg hsum
  have hfun : (fun x : ℝ => (x : ℂ) ^ (s - 1) * jacobiThetaTwoNullTau (I * x ^ 2)) =
      fun x : ℝ => (x : ℂ) ^ (s - 1) *
        (fun t : ℝ => jacobiThetaTwoNullTau (I * t)) (x ^ 2) := by
    funext x; push_cast; rfl
  rw [hfun]
  refine ⟨hI, ?_⟩
  have h2s : (2 : ℂ) ^ s ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => two_ne_zero h.1
  have hO := (p20R1_odd_zeta hs).mul_left ((π : ℂ) ^ (-(s / 2)) * Gamma (s / 2) * 2 ^ s)
  have heq : (fun n : ℕ => (π : ℂ) ^ (-(s / 2)) * Gamma (s / 2) * 2 /
      ((((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) ^ (s / 2) / 2) = fun n : ℕ =>
      (π : ℂ) ^ (-(s / 2)) * Gamma (s / 2) * 2 ^ s * (1 / ((2 * n + 1 : ℕ) : ℂ) ^ s) := by
    funext n
    rw [p20R1_sq_cpow_half _ (by positivity)]
    have e : (((n : ℝ) + 1 / 2 : ℝ) : ℂ) = ((2 * (n : ℝ) + 1 : ℝ) : ℂ) * (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, mul_cpow_ofReal_nonneg (by positivity) (by norm_num), ofReal_inv,
      inv_cpow _ _ (by rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]; simpa using Real.pi_ne_zero.symm)]
    push_cast
    have h1 : ((2 * (n : ℂ) + 1)) ^ s ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; intro h
      have : (2 * (n : ℂ) + 1) = ((2 * n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this] at h; exact Nat.cast_ne_zero.mpr (by omega) h.1
    field_simp
  rw [heq] at hS
  rw [hS.unique hO, cpow_neg (2 : ℂ) s, neg_div]
  field_simp

/-- DLMF 20.10.2: `∫₀^∞ x^{s-1} (θ₃(0|ix²) - 1) dx = π^{-s/2} Γ(s/2) ζ(s)`, `Re s > 1`. -/
@[dlmf 20.10.E2]
theorem mellin_jacobiThetaThreeNullTau_sub_one {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * (jacobiThetaThreeNullTau (I * x ^ 2) - 1))
        (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * (jacobiThetaThreeNullTau (I * x ^ 2) - 1) =
        (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  have hgc : ContinuousOn (fun t : ℝ => jacobiThetaThreeNullTau (I * t) - 1) (Set.Ioi 0) :=
    (p20R1_cont_three 0).sub continuousOn_const
  have hg : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun n : ℕ => (2 : ℂ) *
      Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t)) (jacobiThetaThreeNullTau (I * t) - 1) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h := jacobiThetaThreeTau_hasSum_cos 0 (τ := I * t) (by simpa using ht')
    convert h using 2 with n
    rw [mul_zero, cos_zero, mul_one, ofReal_exp]
    congr 2
    push_cast; ring_nf; rw [I_sq]; ring
  have hsum : Summable fun n : ℕ => ‖(2 : ℂ)‖ / (((n : ℝ) + 1) ^ 2) ^ (s / 2).re := by
    have h := (Real.summable_nat_rpow_inv.mpr hs)
    have h' := ((summable_nat_add_iff 1).mpr h).mul_left 2
    convert h' using 1
    funext n
    rw [div_ofNat_re, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    push_cast
    rw [show (2 : ℝ) * (s.re / 2) = s.re by ring, div_eq_mul_inv]; norm_num
  obtain ⟨hI, hS⟩ := p20R1_mellin_sq (fun n => by positivity) hs0 hgc hg hsum
  have hfun : (fun x : ℝ => (x : ℂ) ^ (s - 1) * (jacobiThetaThreeNullTau (I * x ^ 2) - 1)) =
      fun x : ℝ => (x : ℂ) ^ (s - 1) *
        (fun t : ℝ => jacobiThetaThreeNullTau (I * t) - 1) (x ^ 2) := by
    funext x; push_cast; rfl
  rw [hfun]
  refine ⟨hI, ?_⟩
  rw [← hS.tsum_eq]
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  rw [hz, ← tsum_mul_left]
  congr 1; funext n
  rw [p20R1_sq_cpow_half _ (by positivity), neg_div]
  push_cast
  field_simp

/-- `1 - θ₄(0|it)` (helper for 20.10.3). -/
noncomputable def p3t_G (t : ℝ) : ℂ := 1 - jacobiThetaFourNullTau (I * t)

/-- `1/2 ≠ 0` in `UnitAddCircle`. -/
lemma p3t_half_ne_zero : (((1 / 2 : ℝ)) : UnitAddCircle) ≠ 0 := by
  rw [Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico (by norm_num)]
  norm_num

/-- `θ₄(0|it)` is Mathlib's `cosKernel (1/2) t`. -/
lemma p3t_four_null_eq_cosKernel (t : ℝ) :
    jacobiThetaFourNullTau (I * t) =
      (HurwitzZeta.cosKernel (((1 / 2 : ℝ)) : UnitAddCircle) t : ℂ) := by
  rw [HurwitzZeta.cosKernel_def]
  simp only [jacobiThetaFourNullTau, jacobiThetaFourTau, jacobiThetaThreeTau, zero_add]
  congr 1
  have := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast; field_simp

/-- `1 - θ₄(0|it)` decays exponentially as `t → ∞`. -/
lemma p3t_G_top : ∃ p : ℝ, 0 < p ∧ p3t_G =O[atTop] fun t => Real.exp (-p * t) := by
  obtain ⟨p, hp, h⟩ := HurwitzZeta.isBigO_atTop_cosKernel_sub (((1 / 2 : ℝ)) : UnitAddCircle)
  refine ⟨p, hp, ?_⟩
  have h2 := (Complex.isBigO_ofReal_left.mpr h).neg_left
  refine h2.congr_left fun t => ?_
  simp only [p3t_G, p3t_four_null_eq_cosKernel, ofReal_sub, ofReal_one, neg_sub]

/-- `θ₄(0|it) → 0` as `t → 0⁺` (functional equation). -/
lemma p3t_cosKernel_tendsto_zero :
    Tendsto (HurwitzZeta.cosKernel (((1 / 2 : ℝ)) : UnitAddCircle)) (𝓝[>] 0) (𝓝 0) := by
  set a : UnitAddCircle := ((1 / 2 : ℝ) : UnitAddCircle)
  obtain ⟨p, hp, h⟩ := HurwitzZeta.isBigO_atTop_evenKernel_sub a
  simp only [a, p3t_half_ne_zero, ite_false, sub_zero] at h
  have hH : Tendsto (fun u : ℝ => u ^ (1 / 2 : ℝ) * HurwitzZeta.evenKernel a u) atTop (𝓝 0) :=
    ((Asymptotics.isBigO_refl (fun u : ℝ => u ^ (1 / 2 : ℝ)) atTop).mul h).trans_tendsto
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ hp)
  refine (hH.comp tendsto_inv_nhdsGT_zero).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) < t := ht
  have hf := HurwitzZeta.evenKernel_functional_equation a t⁻¹
  simp only [Function.comp_apply, hf, one_div, inv_inv]
  have : t⁻¹ ^ (2⁻¹ : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (inv_pos.mpr ht') _).ne'
  rw [mul_inv_cancel_left₀ this]

/-- `1 - θ₄(0|it)` is bounded as `t → 0⁺`. -/
lemma p3t_G_zero : p3t_G =O[𝓝[>] 0] fun t : ℝ => t ^ (-(0 : ℝ)) := by
  have h : Tendsto p3t_G (𝓝[>] 0) (𝓝 1) := by
    have := (continuous_ofReal.tendsto 0).comp p3t_cosKernel_tendsto_zero
    have h2 := tendsto_const_nhds (x := (1 : ℂ)) |>.sub this
    simp only [ofReal_zero, sub_zero] at h2
    refine h2.congr fun t => ?_
    simp [p3t_G, p3t_four_null_eq_cosKernel]
  simp only [neg_zero, Real.rpow_zero]
  exact h.isBigO_one ℝ

/-- Continuity of `1 - θ₄(0|it)` on `(0, ∞)`. -/
lemma p3t_G_cont : ContinuousOn p3t_G (Set.Ioi 0) := by
  have := (HurwitzZeta.continuousOn_cosKernel (((1 / 2 : ℝ)) : UnitAddCircle))
  have h2 := continuousOn_const (c := (1 : ℂ)).sub (continuous_ofReal.comp_continuousOn this)
  refine h2.congr fun t _ => ?_
  simp [p3t_G, p3t_four_null_eq_cosKernel]

/-- The Mellin transform of `1 - θ₄(0|it)` converges for `Re w > 0`. -/
lemma p3t_G_mellinConvergent {w : ℂ} (hw : 0 < w.re) : MellinConvergent p3t_G w := by
  obtain ⟨p, hp, h⟩ := p3t_G_top
  exact mellinConvergent_of_isBigO_rpow_exp hp
    (p3t_G_cont.locallyIntegrableOn measurableSet_Ioi) h p3t_G_zero hw

/-- The Mellin transform of `1 - θ₄(0|it)` is holomorphic on `Re w > 0`. -/
lemma p3t_G_mellin_diff {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ (mellin p3t_G) w := by
  obtain ⟨p, hp, h⟩ := p3t_G_top
  exact mellin_differentiableAt_of_isBigO_rpow_exp hp
    (p3t_G_cont.locallyIntegrableOn measurableSet_Ioi) h p3t_G_zero hw


/-- The `x²`-form of the Mellin transform of `1 - θ₄(0|it)`. -/
lemma p3t_xform {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * p3t_G (x ^ 2)) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * p3t_G (x ^ 2) = mellin p3t_G (s / 2) / 2 := by
  have hs2 : 0 < (s / 2).re := by rw [div_ofNat_re]; positivity
  have hM := p3t_G_mellinConvergent hs2
  have hcongr : Set.EqOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * p3t_G (x ^ 2))
      (fun x : ℝ => (x : ℂ) ^ (s - 1) • (fun t => p3t_G (t ^ (2 : ℝ))) x) (Set.Ioi 0) := by
    intro x _
    simp only [smul_eq_mul, Real.rpow_two]
  refine ⟨?_, ?_⟩
  · rw [integrableOn_congr_fun hcongr measurableSet_Ioi]
    exact (MellinConvergent.comp_rpow (f := p3t_G) (s := s) two_ne_zero).mpr hM
  · rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    have := mellin_comp_rpow p3t_G s 2
    simp only [mellin] at this ⊢
    rw [this]
    norm_num
    ring

/-- Unfolding `p3t_G` at `x²`. -/
lemma p3t_G_eq (x : ℝ) : p3t_G (x ^ 2) = 1 - jacobiThetaFourNullTau (I * x ^ 2) := by
  simp [p3t_G]

/-- `∑ (-1)ⁿ (n+1)^{-s} = (1 - 2^{1-s}) ζ(s)` for `Re s > 1`. -/
lemma p3t_eta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s) ((1 - 2 ^ (1 - s)) * riemannZeta s) := by
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have := (Complex.summable_one_div_nat_cpow.mpr hs)
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hE : HasSum (fun k : ℕ => (-1 : ℂ) ^ (2 * k) / (((2 * k : ℕ) : ℂ) + 1) ^ s)
      ((1 - 2 ^ (-s)) * riemannZeta s) := by
    convert p20R1_odd_zeta hs using 2 with k
    rw [pow_mul, neg_one_sq, one_pow]; push_cast; rfl
  have hO : HasSum (fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1) / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s)
      (-(2 ^ (-s) * riemannZeta s)) := by
    rw [hz]
    have := (hsum.hasSum.mul_left (2 ^ (-s))).neg
    convert this using 1
    funext k
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul,
      show (((2 * k + 1 : ℕ) : ℂ) + 1) = ((2 : ℝ) : ℂ) * (((k + 1 : ℝ)) : ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg (by norm_num) (by positivity), cpow_neg]
    push_cast
    field_simp
  have h := HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s) hE hO
  convert h using 1
  rw [show (1 : ℂ) - s = 1 + -s by ring, cpow_add _ _ two_ne_zero, cpow_one]
  ring


/-- DLMF 20.10.3 in Mellin form for `Re s > 1`. -/
lemma p3t_main_gt_one {s : ℂ} (hs : 1 < s.re) :
    mellin p3t_G (s / 2) / 2 =
      (1 - 2 ^ (1 - s)) * (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  have hg : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum (fun n : ℕ => (2 * (-1 : ℂ) ^ n) *
      Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t)) (p3t_G t) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h := (jacobiThetaFourTau_hasSum_cos 0 (τ := I * t) (by simpa using ht')).neg
    rw [neg_sub] at h
    rw [show p3t_G t = 1 - jacobiThetaFourTau 0 (I * t) from rfl]
    convert h using 1
    funext n
    rw [mul_zero, cos_zero, mul_one, ofReal_exp, pow_succ]
    have : cexp (π * I * (I * t) * ((n : ℂ) + 1) ^ 2) =
        cexp (((-π * ((n : ℝ) + 1) ^ 2 * t : ℝ)) : ℂ) := by
      congr 1; push_cast; linear_combination ((π : ℂ) * t * ((n : ℂ) + 1) ^ 2) * I_sq
    rw [this]; ring_nf
  have hsum : Summable fun n : ℕ => ‖2 * (-1 : ℂ) ^ n‖ / (((n : ℝ) + 1) ^ 2) ^ (s / 2).re := by
    have h := (Real.summable_nat_rpow_inv.mpr hs)
    have h' := ((summable_nat_add_iff 1).mpr h).mul_left 2
    convert h' using 1
    funext n
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, div_ofNat_re,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    push_cast
    rw [show (2 : ℝ) * (s.re / 2) = s.re by ring, div_eq_mul_inv]; norm_num
  obtain ⟨-, hS⟩ := p20R1_mellin_sq (fun n => by positivity) hs0 p3t_G_cont hg hsum
  rw [(p3t_xform hs0).2] at hS
  have hE := (p3t_eta hs).mul_left ((π : ℂ) ^ (-(s / 2)) * Gamma (s / 2))
  have heq : (fun n : ℕ => (π : ℂ) ^ (-(s / 2)) * Gamma (s / 2) * (2 * (-1 : ℂ) ^ n) /
      ((((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (s / 2) / 2) = fun n : ℕ =>
      (π : ℂ) ^ (-(s / 2)) * Gamma (s / 2) * ((-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s) := by
    funext n
    rw [p20R1_sq_cpow_half _ (by positivity)]
    push_cast
    ring
  rw [heq] at hS
  rw [hS.unique hE, neg_div]
  ring


/-- The right side of 20.10.3 is holomorphic on `Re s > 0`, `s ≠ 1`. -/
lemma p3t_R_diff {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s : ℂ =>
      (1 - 2 ^ (1 - s)) * (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s) s := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hG : DifferentiableAt ℂ (fun s : ℂ => Gamma (s / 2)) s := by
    refine (differentiableAt_Gamma _ fun m h => ?_).comp s (by fun_prop)
    have := congrArg re h
    rw [div_ofNat_re] at this
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (1 - s)) s :=
    (differentiableAt_id.const_sub 1).const_cpow (Or.inl two_ne_zero)
  have h3 : DifferentiableAt ℂ (fun s : ℂ => (π : ℂ) ^ (-s / 2)) s :=
    (differentiableAt_id.neg.div_const 2).const_cpow (Or.inl hπ)
  exact (((differentiableAt_const _).sub h2).mul h3 |>.mul hG).mul
    (differentiableAt_riemannZeta hs1)

/-- The left side of 20.10.3 is holomorphic on `Re s > 0`. -/
lemma p3t_F_diff {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun s : ℂ => mellin p3t_G (s / 2) / 2) s := by
  have hs2 : 0 < (s / 2).re := by rw [div_ofNat_re]; positivity
  exact (DifferentiableAt.comp (g := mellin p3t_G) (f := fun s : ℂ => s / 2) s
    (p3t_G_mellin_diff hs2) (by fun_prop)).div_const 2

/-- Analytic continuation of 20.10.3 over a convex open set. -/
lemma p3t_eqOn_convex {V : Set ℂ} (hV : Convex ℝ V) (hVo : IsOpen V)
    (hV0 : ∀ s ∈ V, 0 < s.re ∧ s ≠ 1) {z₀ : ℂ} (hz₀ : z₀ ∈ V) (hz₀' : 1 < z₀.re) :
    Set.EqOn (fun s : ℂ => mellin p3t_G (s / 2) / 2)
      (fun s : ℂ => (1 - 2 ^ (1 - s)) * (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s)
      V := by
  have hF : DifferentiableOn ℂ (fun s : ℂ => mellin p3t_G (s / 2) / 2) V := fun s hs =>
    (p3t_F_diff (hV0 s hs).1).differentiableWithinAt
  have hR : DifferentiableOn ℂ (fun s : ℂ =>
      (1 - 2 ^ (1 - s)) * (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s) V := fun s hs =>
    (p3t_R_diff (hV0 s hs).1 (hV0 s hs).2).differentiableWithinAt
  refine (hF.analyticOnNhd hVo).eqOn_of_preconnected_of_eventuallyEq (hR.analyticOnNhd hVo)
    hV.isPreconnected hz₀ ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀'] with s hs
  exact p3t_main_gt_one hs

/-- DLMF 20.10.3 in Mellin form for `Re s > 0`, `s ≠ 1`. -/
lemma p3t_main {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    mellin p3t_G (s / 2) / 2 =
      (1 - 2 ^ (1 - s)) * (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s := by
  have hlin1 : IsLinearMap ℝ (fun s : ℂ => s.im - s.re) :=
    ⟨fun x y => by simp; ring, fun c x => by simp; ring⟩
  have hlin2 : IsLinearMap ℝ (fun s : ℂ => s.im + s.re) :=
    ⟨fun x y => by simp; ring, fun c x => by simp; ring⟩
  have hc1 : Continuous fun s : ℂ => s.im - s.re := by fun_prop
  have hc2 : Continuous fun s : ℂ => s.im + s.re := by fun_prop
  by_cases h1 : s.re - 1 < s.im
  · refine p3t_eqOn_convex (V := {s : ℂ | 0 < s.re} ∩ {s : ℂ | -1 < s.im - s.re})
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_gt hlin1 (-1)))
      ((isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const hc1))
      (fun w hw => ⟨hw.1, fun h => by subst h; norm_num at hw⟩)
      (z₀ := 2 + 2 * I) ⟨by norm_num, by norm_num⟩ (by norm_num) ⟨hs, by simp; linarith⟩
  by_cases h2 : s.im < 1 - s.re
  · refine p3t_eqOn_convex (V := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im + s.re < 1})
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_lt hlin2 1))
      ((isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt hc2 continuous_const))
      (fun w hw => ⟨hw.1, fun h => by subst h; norm_num at hw⟩)
      (z₀ := 2 - 2 * I) ⟨by norm_num, by norm_num⟩ (by norm_num) ⟨hs, by simp; linarith⟩
  · have h3 : 1 < s.re := by
      rcases lt_or_eq_of_le (show 1 ≤ s.re by linarith) with h | h
      · exact h
      · exfalso; apply hs1
        apply Complex.ext <;> simp <;> linarith
    exact p3t_main_gt_one h3

/-- The right side of 20.10.3 tends to `ln 2` at `s = 1`. -/
lemma p3t_R_tendsto : Tendsto (fun s : ℂ =>
      (1 - 2 ^ (1 - s)) * (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s) (𝓝[≠] 1)
      (𝓝 (Real.log 2 : ℂ)) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hφ : HasDerivAt (fun s : ℂ => (2 : ℂ) ^ (1 - s)) ((2 : ℂ) ^ ((1 : ℂ) - 1) *
      Complex.log 2 * (-1)) 1 :=
    ((hasDerivAt_id (1 : ℂ)).const_sub 1).const_cpow (Or.inl two_ne_zero)
  have hA : Tendsto (fun s : ℂ => (1 - 2 ^ (1 - s)) / (s - 1)) (𝓝[≠] 1) (𝓝 (Real.log 2 : ℂ)) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp hφ).neg
    rw [show (2 : ℂ) ^ ((1 : ℂ) - 1) = 1 by simp, one_mul, mul_neg_one, neg_neg,
      show Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) by
        rw [Complex.ofReal_log (by norm_num)]; norm_num] at h
    refine h.congr fun s => ?_
    rw [slope_def_field, sub_self, cpow_zero]
    ring
  have hC : Tendsto (fun s : ℂ => (π : ℂ) ^ (-s / 2) * Gamma (s / 2)) (𝓝[≠] 1) (𝓝 1) := by
    have hG : ContinuousAt (fun s : ℂ => Gamma (s / 2)) 1 :=
      ((differentiableAt_Gamma _ fun m h => by
        have := congrArg re h; norm_num at this
        linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]).comp 1 (by fun_prop)).continuousAt
    have h3 : ContinuousAt (fun s : ℂ => (π : ℂ) ^ (-s / 2)) 1 :=
      ((differentiableAt_id.neg.div_const 2).const_cpow (Or.inl hπ)).continuousAt
    have h : Tendsto (fun s : ℂ => (π : ℂ) ^ (-s / 2) * Gamma (s / 2)) (𝓝[≠] 1)
        (𝓝 ((π : ℂ) ^ (-1 / 2 : ℂ) * Gamma (1 / 2))) :=
      (h3.mul hG).tendsto.mono_left nhdsWithin_le_nhds
    convert h using 2
    rw [Gamma_one_half_eq, ← cpow_add _ _ hπ]
    norm_num
  have h := (hA.mul riemannZeta_residue_one).mul hC
  rw [mul_one, mul_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp

/-- DLMF 20.10.3: `∫₀^∞ x^{s-1} (1 - θ₄(0|ix²)) dx = (1 - 2^{1-s}) π^{-s/2} Γ(s/2) ζ(s)`,
`Re s > 0`, `s ≠ 1` (see `mellin_one_sub_jacobiThetaFourNullTau_one` for `s = 1`).
Corrected from the printed DLMF formula: `s = 1` is excluded because there the right side is a
removable singularity, whereas Lean's totalized `riemannZeta 1` would make it `0` instead of
the limit `ln 2`. -/
@[dlmf 20.10.E3]
theorem mellin_one_sub_jacobiThetaFourNullTau {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * (1 - jacobiThetaFourNullTau (I * x ^ 2)))
        (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * (1 - jacobiThetaFourNullTau (I * x ^ 2)) =
        (1 - 2 ^ (1 - s)) * (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s := by
  obtain ⟨hI, hE⟩ := p3t_xform hs
  simp only [p3t_G_eq] at hI hE
  exact ⟨hI, hE.trans (p3t_main hs hs1)⟩

/-- DLMF 20.10.3 at the removable point `s = 1`: `∫₀^∞ (1 - θ₄(0|ix²)) dx = ln 2`.
Corrected from the printed DLMF formula: the printed right side `(1 - 2^{1-s}) π^{-s/2} Γ(s/2) ζ(s)`
is `0 · ∞` at `s = 1`; its limit `ln 2` is stated explicitly (checked with mpmath). -/
@[dlmf 20.10.E3 "removable point s = 1 of the right side"]
theorem mellin_one_sub_jacobiThetaFourNullTau_one :
    IntegrableOn (fun x : ℝ => 1 - jacobiThetaFourNullTau (I * x ^ 2)) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), (1 - jacobiThetaFourNullTau (I * x ^ 2)) = Real.log 2 := by
  obtain ⟨hI, hE⟩ := p3t_xform (s := 1) (by norm_num)
  simp only [p3t_G_eq, sub_self, cpow_zero, one_mul] at hI hE
  refine ⟨hI, hE.trans ?_⟩
  have hF : Tendsto (fun s : ℂ => mellin p3t_G (s / 2) / 2) (𝓝[≠] 1)
      (𝓝 (mellin p3t_G (1 / 2) / 2)) :=
    (p3t_F_diff (s := 1) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun s : ℂ => mellin p3t_G (s / 2) / 2) (𝓝[≠] 1) (𝓝 (Real.log 2 : ℂ)) := by
    refine p3t_R_tendsto.congr' ?_
    have hre : ∀ᶠ s : ℂ in 𝓝[≠] 1, 0 < s.re :=
      nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num))
    filter_upwards [hre, self_mem_nhdsWithin] with s h1 h2
    exact (p3t_main h1 h2).symm
  exact tendsto_nhds_unique hF hR

/-- DLMF 20.10.4: for `Re s > 0`, `ℓ > 0`, `|Re β| + |Im β| ≤ ℓ`,
`∫₀^∞ e^{-st} θ₁(βπ/(2ℓ)|iπt/ℓ²) dt = -∫₀^∞ e^{-st} θ₂((ℓ+β)π/(2ℓ)|iπt/ℓ²) dt
  = (ℓ/√s) sinh(β√s) sech(ℓ√s)`. -/
@[dlmf 20.10.E4]
theorem laplace_jacobiThetaOneTau {s β : ℂ} {ℓ : ℝ} (hs : 0 < s.re) (hℓ : 0 < ℓ)
    (hβ : |β.re| + |β.im| ≤ ℓ) :
    IntegrableOn (fun t : ℝ => cexp (-s * t) *
        jacobiThetaOneTau (β * π / (2 * ℓ)) (I * π * t / ℓ ^ 2))
        (Set.Ioi 0) ∧
      IntegrableOn (fun t : ℝ => cexp (-s * t) *
        jacobiThetaTwoTau ((ℓ + β) * π / (2 * ℓ)) (I * π * t / ℓ ^ 2)) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), cexp (-s * t) *
          jacobiThetaOneTau (β * π / (2 * ℓ)) (I * π * t / ℓ ^ 2) =
        ℓ / s ^ (1 / 2 : ℂ) * sinh (β * s ^ (1 / 2 : ℂ)) / cosh (ℓ * s ^ (1 / 2 : ℂ)) ∧
      -∫ t in Set.Ioi (0 : ℝ), cexp (-s * t) *
          jacobiThetaTwoTau ((ℓ + β) * π / (2 * ℓ)) (I * π * t / ℓ ^ 2) =
        ℓ / s ^ (1 / 2 : ℂ) * sinh (β * s ^ (1 / 2 : ℂ)) / cosh (ℓ * s ^ (1 / 2 : ℂ)) := by
  sorry

/-- DLMF 20.10.5: for `Re s > 0`, `ℓ > 0`, `|Re β| + |Im β| ≤ ℓ`,
`∫₀^∞ e^{-st} θ₃((ℓ+β)π/(2ℓ)|iπt/ℓ²) dt = ∫₀^∞ e^{-st} θ₄(βπ/(2ℓ)|iπt/ℓ²) dt
  = (ℓ/√s) cosh(β√s) csch(ℓ√s)`. -/
@[dlmf 20.10.E5]
theorem laplace_jacobiThetaThreeTau {s β : ℂ} {ℓ : ℝ} (hs : 0 < s.re) (hℓ : 0 < ℓ)
    (hβ : |β.re| + |β.im| ≤ ℓ) :
    IntegrableOn (fun t : ℝ => cexp (-s * t) *
        jacobiThetaThreeTau ((ℓ + β) * π / (2 * ℓ)) (I * π * t / ℓ ^ 2)) (Set.Ioi 0) ∧
      IntegrableOn (fun t : ℝ => cexp (-s * t) *
        jacobiThetaFourTau (β * π / (2 * ℓ)) (I * π * t / ℓ ^ 2)) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), cexp (-s * t) *
          jacobiThetaThreeTau ((ℓ + β) * π / (2 * ℓ)) (I * π * t / ℓ ^ 2) =
        ℓ / s ^ (1 / 2 : ℂ) * cosh (β * s ^ (1 / 2 : ℂ)) / sinh (ℓ * s ^ (1 / 2 : ℂ)) ∧
      ∫ t in Set.Ioi (0 : ℝ), cexp (-s * t) *
          jacobiThetaFourTau (β * π / (2 * ℓ)) (I * π * t / ℓ ^ 2) =
        ℓ / s ^ (1 / 2 : ℂ) * cosh (β * s ^ (1 / 2 : ℂ)) / sinh (ℓ * s ^ (1 / 2 : ℂ)) := by
  sorry

end DLMF.Theta

end
