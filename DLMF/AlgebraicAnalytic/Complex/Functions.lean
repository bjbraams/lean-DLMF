/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.AlgebraicAnalytic.Complex.Basic
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import DLMFMathlib.Analysis.Complex.TrigSeriesExtension
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Tactic.CrossRefAttribute
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.Contour.Residue.Theorem
public import DLMFMathlib.Analysis.Complex.RoucheFilledHull
public import DLMFMathlib.Analysis.Complex.LaurentAnnulus
public import DLMFMathlib.Analysis.Complex.LagrangeInversion
public import DLMFMathlib.Analysis.Complex.MittagLeffler
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Subharmonic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.StrongMaximumPrinciple

/-!
# Functions of a complex variable (DLMF §1.10(i)–(viii))

Statements of DLMF §1.10 that are not, in the stated generality, in Mathlib or Tau Ceti; the
upstream items (Taylor's theorem, the identity theorem, the maximum-modulus principle, Schwarz's
lemma on discs, removable singularities, Rouché's theorem on discs, …) are recorded as
`dlmf_upstream` pointers in `DLMF.AlgebraicAnalytic.Complex.MathlibCoverage`.

## Main results

* `hasSum_exp_series`: the exponential series (DLMF 1.10.2).
* `hasSum_laurentSeries`: Laurent's theorem (DLMF 1.10.6–1.10.7).
* `removable_iff_laurentCoeff_neg_eq_zero`, `meromorphicOrderAt_eq_neg_iff_laurentCoeff`,
  `residueAt_eq_residue`, `picard_great`: singularities and residues (§1.10(iii)).
* `IsSimpleClosedContour.residue_theorem`, `IsSimpleClosedContour.argument_principle`,
  `IsSimpleClosedContour.argumentPrinciple_mul_id`, `IsSimpleClosedContour.rouche`:
  DLMF 1.10.8–1.10.10 and Rouché's theorem (§1.10(iv)).
* `harmonic_eqOn_of_isMaxOn`, `harmonic_exists_mem_frontier_isMaxOn`: the maximum principle for
  harmonic functions (§1.10(v)).
* `schwarz_lemma`, `schwarz_lemma_eq_iff`: Schwarz's lemma (DLMF 1.10.11).
* `sqrt_branch_slitPlane`, `sqrt_branch_compl_Ici`, `not_exists_sqrt_branch_punctured`,
  `differentiableOn_one_sub_cpow_mul_one_add_cpow`: branches in cut planes (§1.10(vi)).
* `residueAt_div_sub_pow`, `eventually_hasSum_residueAt_lagrange`: residues of
  `H(z)/(z - z₀)ⁿ⁺¹` and the Lagrange–Bürmann expansion in terms of residues.
* `lagrange_inversion`, `lagrange_burmann`, `lagrange_inversion_extended`,
  `lagrange_burmann_extended`: inversion theorems (DLMF 1.10.12–1.10.17), from
  `Complex.hasSum_lagrangeInversion`.
* `differentiableOn_intervalIntegral_param`, `differentiableOn_improperIntegral_param`,
  `tendstoUniformlyOn_integral_of_norm_le`: analyticity of integrals (DLMF 1.10.18–1.10.19,
  §1.10(viii)).

The infinite products, partial fractions and generating functions of §1.10(ix)–(xi) are in
`DLMF.AlgebraicAnalytic.Complex.InfiniteProducts`.

## Implementation notes

* Contours, interiors and the positive sense are those of `DLMF.AlgebraicAnalytic.Complex.Basic`
  (simple closed piecewise `C¹` contours, Tau Ceti's filled hull and winding number).
* The residue is `residueAt f z₀`, the Laurent coefficient `a_{-1}` defined by a circle integral,
  so that it is meaningful also at essential singularities; at poles it is Tau Ceti's
  `TauCeti.Contour.residue` (`residueAt_eq_residue`).
* Products indexed by `n ≥ 1` in DLMF are indexed by `ℕ` here where the index is a dummy
  (Weierstrass products, Mittag-Leffler series); DLMF's convergence of infinite products is
  `InfiniteProductConverges`.
* Logarithms and powers are principal (`Complex.log`, `cpow`).
-/

@[expose] public noncomputable section

open Complex Filter Set Metric MeasureTheory
open scoped Topology

namespace DLMF.AlgebraicAnalytic

/-! ## §1.10(i) Taylor's theorem -/

/-- DLMF 1.10.2: `e^z = 1 + z/1! + z²/2! + ⋯`, `|z| < ∞`. From Mathlib's
`NormedSpace.expSeries_div_hasSum_exp`. -/
@[dlmf 1.10.E2]
theorem hasSum_exp_series (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / n.factorial) (exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

/-! ## §1.10(iii) Laurent series -/

/-- The open annulus `r₁ < ‖z - z₀‖ < r₂` is open. -/
private lemma isOpen_annulus (z₀ : ℂ) (r₁ r₂ : ℝ) :
    IsOpen {z : ℂ | r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂} :=
  (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)

/-- The closed annulus `ρ ≤ ‖z - z₀‖ ≤ ρ'` lies in the open annulus `r₁ < ‖z - z₀‖ < r₂`. -/
private lemma closedAnnulus_subset {z₀ : ℂ} {r₁ r₂ ρ ρ' : ℝ} (hρ : r₁ < ρ) (hρ' : ρ' < r₂) :
    closedBall z₀ ρ' \ ball z₀ ρ ⊆ {z : ℂ | r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂} := by
  intro z hz
  simp only [Set.mem_sdiff, mem_closedBall, mem_ball, dist_eq_norm, not_lt] at hz
  exact ⟨by linarith [hz.2], by linarith [hz.1]⟩

/-- Radius independence of Laurent coefficients, for radii `ρ ≤ ρ'`. -/
private lemma laurentCoeff_eq_of_le {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ ρ ρ' : ℝ} (hr₁ : 0 ≤ r₁)
    (hf : DifferentiableOn ℂ f {z | r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hρ : ρ ∈ Ioo r₁ r₂)
    (hρ' : ρ' ∈ Ioo r₁ r₂) (hle : ρ ≤ ρ') (n : ℤ) :
    laurentCoeff f z₀ ρ' n = laurentCoeff f z₀ ρ n := by
  unfold laurentCoeff
  congr 1
  have hsub := closedAnnulus_subset (z₀ := z₀) hρ.1 hρ'.2
  have hA := isOpen_annulus z₀ r₁ r₂
  have hdiff : ∀ z ∈ closedBall z₀ ρ' \ ball z₀ ρ,
      DifferentiableAt ℂ (fun z => f z * (z - z₀) ^ (-n - 1)) z := by
    intro z hz
    have hzA := hsub hz
    have hz0 : z - z₀ ≠ 0 := by
      intro h
      have h1 : r₁ < ‖z - z₀‖ := hzA.1
      rw [h, norm_zero] at h1; linarith
    exact (hf.differentiableAt (hA.mem_nhds hzA)).mul
      ((differentiableAt_id.sub_const z₀).zpow (Or.inl hz0))
  refine circleIntegral_eq_of_differentiable_on_annulus_off_countable (hr₁.trans_lt hρ.1) hle
    countable_empty (fun z hz => (hdiff z hz).continuousAt.continuousWithinAt)
    (fun z hz => hdiff z ⟨ball_subset_closedBall hz.1.1, fun h => hz.1.2
      (ball_subset_closedBall h)⟩)

/-- Laurent coefficients do not depend on the radius within the annulus of holomorphy. -/
private lemma laurentCoeff_eq_of_mem {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ ρ ρ' : ℝ} (hr₁ : 0 ≤ r₁)
    (hf : DifferentiableOn ℂ f {z | r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hρ : ρ ∈ Ioo r₁ r₂)
    (hρ' : ρ' ∈ Ioo r₁ r₂) (n : ℤ) :
    laurentCoeff f z₀ ρ' n = laurentCoeff f z₀ ρ n := by
  rcases le_total ρ ρ' with h | h
  · exact laurentCoeff_eq_of_le hr₁ hf hρ hρ' h n
  · exact (laurentCoeff_eq_of_le hr₁ hf hρ' hρ h n).symm

/-- The nonnegative part of the Laurent series sums to the outer Cauchy integral. -/
private lemma hasSum_laurent_outer {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ r ρ : ℝ} (hr₁ : 0 ≤ r₁)
    (hf : DifferentiableOn ℂ f {z | r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hr : r ∈ Ioo r₁ r₂)
    (hρ : ρ ∈ Ioo r₁ r₂) {z : ℂ} (hzρ : ‖z - z₀‖ < ρ) :
    HasSum (fun n : ℕ => laurentCoeff f z₀ r (n : ℤ) * (z - z₀) ^ (n : ℤ))
      ((2 * Real.pi * I)⁻¹ * ∮ w in C(z₀, ρ), (w - z)⁻¹ * f w) := by
  have hρ0 : 0 < ρ := hr₁.trans_lt hρ.1
  have hsph : sphere z₀ ρ ⊆ {z : ℂ | r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂} := fun w hw => by
    rw [mem_sphere, dist_eq_norm] at hw
    change r₁ < ‖w - z₀‖ ∧ ‖w - z₀‖ < r₂
    rw [hw]; exact hρ
  have hint : CircleIntegrable f z₀ ρ := (hf.continuousOn.mono hsph).circleIntegrable hρ0.le
  have hout := hasSum_two_pi_I_cauchyPowerSeries_integral (f := f) (w := z - z₀) hint hzρ
  have := hout.mul_left (2 * Real.pi * I)⁻¹
  simp only [add_sub_cancel, smul_eq_mul] at this
  refine this.congr_fun fun n => ?_
  rw [laurentCoeff_eq_of_mem hr₁ hf hρ hr, laurentCoeff, zpow_natCast, mul_assoc]
  congr 1
  rw [mul_comm _ ((z - z₀) ^ n), ← circleIntegral.integral_const_mul]
  refine circleIntegral.integral_congr hρ0.le fun w hw => ?_
  have hw0 : w - z₀ ≠ 0 := by
    intro h; rw [mem_sphere, dist_eq_norm, h, norm_zero] at hw; linarith
  rw [show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    div_pow, pow_succ]
  field_simp

/-- DLMF 1.10.6–1.10.7 (Laurent's theorem): if `f` is analytic in the annulus
`r₁ < |z - z₀| < r₂` (`0 ≤ r₁ < r₂ ≤ ∞`; here `r₂` finite or the statement is applied for every
finite `r₂`) and `r₁ < r < r₂`, then `f(z) = ∑_{n ∈ ℤ} aₙ (z - z₀)ⁿ` in the annulus, with
`aₙ = laurentCoeff f z₀ r n`; the series converges absolutely (and uniformly on compact
subsets). -/
@[dlmf 1.10.E6]
theorem hasSum_laurentSeries {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ r : ℝ} (hr₁ : 0 ≤ r₁)
    (hf : DifferentiableOn ℂ f {z | r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hr : r ∈ Ioo r₁ r₂)
    {z : ℂ} (hz : r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂) :
    HasSum (fun n : ℤ => laurentCoeff f z₀ r n * (z - z₀) ^ n) (f z) := by
  set d := ‖z - z₀‖
  set ρ₁ := (r₁ + d) / 2
  set ρ₂ := (d + r₂) / 2
  have hρ₁ : ρ₁ ∈ Ioo r₁ r₂ := ⟨by simp only [ρ₁]; linarith, by simp only [ρ₁]; linarith⟩
  have hρ₂ : ρ₂ ∈ Ioo r₁ r₂ := ⟨by simp only [ρ₂]; linarith, by simp only [ρ₂]; linarith⟩
  have hρ₁0 : 0 < ρ₁ := hr₁.trans_lt hρ₁.1
  have hρ₁d : ρ₁ < d := by simp only [ρ₁]; linarith
  have hdρ₂ : d < ρ₂ := by simp only [ρ₂]; linarith
  have hA := isOpen_annulus z₀ r₁ r₂
  have hsub := closedAnnulus_subset (z₀ := z₀) hρ₁.1 hρ₂.2
  have hcont : ContinuousOn f (closedBall z₀ ρ₂ \ ball z₀ ρ₁) :=
    hf.continuousOn.mono hsub
  have hsph : ∀ ρ ∈ Ioo r₁ r₂, sphere z₀ ρ ⊆ {z : ℂ | r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂} :=
    fun ρ hρ w hw => by
      rw [mem_sphere, dist_eq_norm] at hw
      change r₁ < ‖w - z₀‖ ∧ ‖w - z₀‖ < r₂
      rw [hw]; exact hρ
  have hint : ∀ ρ ∈ Ioo r₁ r₂, CircleIntegrable f z₀ ρ := fun ρ hρ =>
    (hf.continuousOn.mono (hsph ρ hρ)).circleIntegrable (hr₁.trans hρ.1.le)
  have hcauchy := Complex.circleIntegral_sub_inv_mul_annulus hρ₁0 hρ₁d hdρ₂ hcont
    (fun w hw => hf.differentiableAt (hA.mem_nhds (hsub ⟨ball_subset_closedBall hw.1,
      fun h => hw.2 (ball_subset_closedBall h)⟩)))
  have hin := Complex.hasSum_circleIntegral_inner (w := z - z₀) hρ₁0 (hint ρ₁ hρ₁) hρ₁d
  have hz0 : z - z₀ ≠ 0 := fun h => by
    have : d = 0 := by simp only [d, h, norm_zero]
    linarith
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hA' := hasSum_laurent_outer hr₁ hf hr hρ₂ hdρ₂
  have hB' : HasSum (fun n : ℕ => laurentCoeff f z₀ r (-((n : ℤ) + 1)) *
      (z - z₀) ^ (-((n : ℤ) + 1)))
      (-((2 * Real.pi * I)⁻¹ * ∮ w in C(z₀, ρ₁), (w - z)⁻¹ * f w)) := by
    have := hin.mul_left (2 * Real.pi * I)⁻¹
    rw [show (∮ w in C(z₀, ρ₁), -((w - (z₀ + (z - z₀)))⁻¹ * f w)) =
        ∮ w in C(z₀, ρ₁), (-1) * ((w - z)⁻¹ * f w) by
          simp only [add_sub_cancel, neg_one_mul],
      circleIntegral.integral_const_mul] at this
    convert this using 1
    · funext n
      rw [laurentCoeff_eq_of_mem hr₁ hf hρ₁ hr, laurentCoeff,
        show -(-((n : ℤ) + 1)) - 1 = (n : ℤ) by ring, mul_assoc]
      congr 1
      rw [mul_comm, ← circleIntegral.integral_const_mul]
      refine circleIntegral.integral_congr hρ₁0.le fun w _ => ?_
      rw [zpow_neg, zpow_natCast, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, div_pow, pow_succ]
      field_simp
    · ring
  have key := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => laurentCoeff f z₀ r n * (z - z₀) ^ n)
    hA' hB'
  rw [← sub_eq_add_neg, ← mul_sub, hcauchy, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul] at key
  exact key

/-- If all negative Laurent coefficients vanish, `f` agrees off `z₀` with the Cauchy integral
over `C(z₀, r)`, which is analytic at `z₀` with value `a₀` there. -/
private lemma exists_analyticAt_of_laurentCoeff_neg {f : ℂ → ℂ} {z₀ : ℂ} {r₂ r : ℝ}
    (hf : DifferentiableOn ℂ f {z | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hr : r ∈ Ioo 0 r₂)
    (h : ∀ n : ℤ, n < 0 → laurentCoeff f z₀ r n = 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G z₀ ∧ G z₀ = laurentCoeff f z₀ r 0 ∧ f =ᶠ[𝓝[≠] z₀] G := by
  have hsph : sphere z₀ r ⊆ {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂} := fun w hw => by
    rw [mem_sphere, dist_eq_norm] at hw
    change 0 < ‖w - z₀‖ ∧ ‖w - z₀‖ < r₂
    rw [hw]; exact hr
  have hint : CircleIntegrable f z₀ r := (hf.continuousOn.mono hsph).circleIntegrable hr.1.le
  refine ⟨fun z => (2 * Real.pi * I)⁻¹ * ∮ w in C(z₀, r), (w - z)⁻¹ * f w, ?_, ?_, ?_⟩
  · have := (hasFPowerSeriesOn_cauchy_integral (R := ⟨r, hr.1.le⟩) hint
      (by exact_mod_cast hr.1)).analyticAt
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul]
    rfl
  · beta_reduce
    rw [laurentCoeff]
    congr 1
    refine circleIntegral.integral_congr hr.1.le fun w _ => ?_
    simp only [neg_zero, zero_sub, zpow_neg_one, mul_comm]
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds z₀ hr.1)] with z hz hb
    rw [mem_ball, dist_eq_norm] at hb
    have hz' : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
    have hL := hasSum_laurentSeries le_rfl hf hr ⟨hz', hb.trans hr.2⟩
    have hA := hasSum_laurent_outer le_rfl hf hr hr hb
    have hB : HasSum (fun n : ℕ => laurentCoeff f z₀ r (-((n : ℤ) + 1)) *
        (z - z₀) ^ (-((n : ℤ) + 1))) 0 := by
      have : (fun n : ℕ => laurentCoeff f z₀ r (-((n : ℤ) + 1)) *
          (z - z₀) ^ (-((n : ℤ) + 1))) = fun _ => 0 := by
        funext n; rw [h _ (by omega), zero_mul]
      rw [this]; exact hasSum_zero
    have := HasSum.of_nat_of_neg_add_one
      (f := fun n : ℤ => laurentCoeff f z₀ r n * (z - z₀) ^ n) hA hB
    rw [add_zero] at this
    exact hL.unique this

/-- Laurent coefficients of an analytic germ at negative indices vanish. -/
private lemma laurentCoeff_neg_eq_zero_of_analyticAt {f g : ℂ → ℂ} {z₀ : ℂ} {r₂ r : ℝ}
    (hf : DifferentiableOn ℂ f {z | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hr : r ∈ Ioo 0 r₂)
    (hg : AnalyticAt ℂ g z₀) (hfg : f =ᶠ[𝓝[≠] z₀] g) {n : ℤ} (hn : n < 0) :
    laurentCoeff f z₀ r n = 0 := by
  obtain ⟨ε₁, hε₁, hg'⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨ε₂, hε₂, hfg'⟩ := Metric.mem_nhdsWithin_iff.mp hfg
  set ρ := min (min (ε₁ / 2) (ε₂ / 2)) (r / 2)
  have hρ0 : 0 < ρ := lt_min (lt_min (by linarith) (by linarith)) (by linarith [hr.1])
  have hρ1 : ρ < ε₁ := by
    have := min_le_left (min (ε₁ / 2) (ε₂ / 2)) (r / 2)
    have := min_le_left (ε₁ / 2) (ε₂ / 2); linarith
  have hρ2 : ρ < ε₂ := by
    have := min_le_left (min (ε₁ / 2) (ε₂ / 2)) (r / 2)
    have := min_le_right (ε₁ / 2) (ε₂ / 2); linarith
  have hρr : ρ < r := by have := min_le_right (min (ε₁ / 2) (ε₂ / 2)) (r / 2); linarith
  rw [laurentCoeff_eq_of_mem le_rfl hf ⟨hρ0, hρr.trans hr.2⟩ hr, laurentCoeff]
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -n - 1 by omega)
  have hgd : DifferentiableOn ℂ (fun w => g w * (w - z₀) ^ k) (closedBall z₀ ρ) := fun w hw =>
    ((hg' w (closedBall_subset_ball hρ1 hw)).differentiableAt.mul
      ((differentiableAt_id.sub_const z₀).pow k)).differentiableWithinAt
  rw [circleIntegral.integral_congr hρ0.le (g := fun w => g w * (w - z₀) ^ k),
    circleIntegral_eq_zero_of_differentiable_on_off_countable hρ0.le countable_empty
      hgd.continuousOn (fun w hw => hgd.differentiableAt (closedBall_mem_nhds_of_mem hw.1)),
    mul_zero]
  intro w hw
  have hw0 : w ≠ z₀ := by
    intro h; rw [h, mem_sphere, dist_self] at hw; linarith
  beta_reduce
  rw [hk, zpow_natCast, hfg' ⟨sphere_subset_closedBall.trans
    (closedBall_subset_ball hρ2) hw, hw0⟩]

/-- DLMF §1.10(iii) (removable singularities): if `f` is analytic in the punctured disc
`0 < |z - z₀| < r₂`, then `z₀` is removable (`f` agrees near `z₀`, off `z₀`, with a function
analytic at `z₀`) iff all Laurent coefficients `aₙ`, `n < 0`, vanish; the Laurent series is
then the Taylor series. -/
@[dlmf 1.10.iii]
theorem removable_iff_laurentCoeff_neg_eq_zero {f : ℂ → ℂ} {z₀ : ℂ} {r₂ r : ℝ}
    (hf : DifferentiableOn ℂ f {z | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hr : r ∈ Ioo 0 r₂) :
    (∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g) ↔
      ∀ n : ℤ, n < 0 → laurentCoeff f z₀ r n = 0 := by
  constructor
  · rintro ⟨g, hg, hfg⟩ n hn
    exact laurentCoeff_neg_eq_zero_of_analyticAt hf hr hg hfg hn
  · intro h
    obtain ⟨G, hG, -, hfG⟩ := exists_analyticAt_of_laurentCoeff_neg hf hr h
    exact ⟨G, hG, hfG⟩

/-- DLMF §1.10(iii) (poles): for `f` analytic in a punctured disc, `z₀` is a pole of order
`m ≥ 1` (`f` is meromorphic at `z₀` of order `-m`) iff `a_{-m} ≠ 0` and `aₙ = 0` for `n < -m`.
An isolated singularity with infinitely many nonzero `aₙ`, `n < 0`, is essential. -/
@[dlmf 1.10.iii]
theorem meromorphicOrderAt_eq_neg_iff_laurentCoeff {f : ℂ → ℂ} {z₀ : ℂ} {r₂ r : ℝ}
    (hf : DifferentiableOn ℂ f {z | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hr : r ∈ Ioo 0 r₂)
    {m : ℕ} (hm : 1 ≤ m) :
    (MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ = (-(m : ℤ) : ℤ)) ↔
      laurentCoeff f z₀ r (-(m : ℤ)) ≠ 0 ∧ ∀ n : ℤ, n < -(m : ℤ) → laurentCoeff f z₀ r n = 0 := by
  set h : ℂ → ℂ := fun z => (z - z₀) ^ m * f z with hh
  have hhd : DifferentiableOn ℂ h {z | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂} :=
    ((differentiableOn_id.sub_const z₀).pow m).mul hf
  have hcoeff : ∀ k : ℤ, laurentCoeff h z₀ r k = laurentCoeff f z₀ r (k - m) := by
    intro k
    rw [laurentCoeff, laurentCoeff]
    congr 1
    refine circleIntegral.integral_congr hr.1.le fun w hw => ?_
    have hw0 : w - z₀ ≠ 0 := by
      intro h0; rw [mem_sphere, dist_eq_norm, h0, norm_zero] at hw; linarith [hr.1]
    rw [show -(k - (m : ℤ)) - 1 = (m : ℤ) + (-k - 1) by ring, zpow_add₀ hw0, zpow_natCast, hh]
    ring
  have hfe : ∀ G : ℂ → ℂ, h =ᶠ[𝓝[≠] z₀] G →
      ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ (-(m : ℤ)) • G z := by
    intro G hG
    filter_upwards [hG, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z - z₀ ≠ 0 := sub_ne_zero.mpr hz0
    rw [← hz, hh, smul_eq_mul, zpow_neg, zpow_natCast, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hz0'), one_mul]
  constructor
  · rintro ⟨hM, hord⟩
    obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hM).mp hord
    have hhg : h =ᶠ[𝓝[≠] z₀] g := by
      filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz0
      have hz0' : z - z₀ ≠ 0 := sub_ne_zero.mpr hz0
      rw [hh]; simp only
      rw [hz, smul_eq_mul, zpow_neg, zpow_natCast, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hz0'), one_mul]
    have hneg : ∀ k : ℤ, k < 0 → laurentCoeff h z₀ r k = 0 := fun k hk =>
      laurentCoeff_neg_eq_zero_of_analyticAt hhd hr hg hhg hk
    obtain ⟨G, hG, hG0, hhG⟩ := exists_analyticAt_of_laurentCoeff_neg hhd hr hneg
    have hGg : G z₀ = g z₀ := by
      have h1 : Tendsto G (𝓝[≠] z₀) (𝓝 (G z₀)) :=
        hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto G (𝓝[≠] z₀) (𝓝 (g z₀)) :=
        (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hhG.symm.trans hhg).symm
      exact tendsto_nhds_unique h1 h2
    refine ⟨?_, fun n hn => ?_⟩
    · rw [show -(m : ℤ) = 0 - m by ring, ← hcoeff 0, ← hG0, hGg]
      exact hg0
    · have := hneg (n + m) (by omega)
      rwa [hcoeff, add_sub_cancel_right] at this
  · rintro ⟨hne, hzero⟩
    have hneg : ∀ k : ℤ, k < 0 → laurentCoeff h z₀ r k = 0 := fun k hk => by
      rw [hcoeff]; exact hzero _ (by omega)
    obtain ⟨G, hG, hG0, hhG⟩ := exists_analyticAt_of_laurentCoeff_neg hhd hr hneg
    have hG0' : G z₀ ≠ 0 := by rwa [hG0, hcoeff, zero_sub]
    have hfe' := hfe G hhG
    have hM : MeromorphicAt f z₀ := by
      have : MeromorphicAt (fun z => (z - z₀) ^ (-(m : ℤ)) • G z) z₀ := by fun_prop
      exact this.congr (hfe'.mono fun z hz => hz.symm)
    exact ⟨hM, (meromorphicOrderAt_eq_int_iff hM).mpr ⟨G, hG, hG0', hfe'⟩⟩

/-- DLMF §1.10(iii) (residue): at a pole, the Laurent residue `residueAt f z₀` (the coefficient
`a_{-1}`) is Tau Ceti's `TauCeti.Contour.residue f z₀`. -/
@[dlmf 1.10.iii]
theorem residueAt_eq_residue {f : ℂ → ℂ} {z₀ : ℂ} {r₂ : ℝ}
    (hf : DifferentiableOn ℂ f {z | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hm : MeromorphicAt f z₀) :
    residueAt f z₀ = TauCeti.Contour.residue f z₀ := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.mp hm.eventually_analyticAt
  have key : ∀ r ∈ Ioo 0 ε, laurentCoeff f z₀ r (-1) = TauCeti.Contour.residue f z₀ := by
    intro r hr
    have han : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → AnalyticAt ℂ f z := fun z hz hzz =>
      hεs ⟨closedBall_subset_ball hr.2 hz, hzz⟩
    have hmo : MeromorphicOn f (closedBall z₀ r) := fun z hz => by
      by_cases h : z = z₀
      · exact h ▸ hm
      · exact (han z hz h).meromorphicAt
    have hres := TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hr.1
      {z₀} hmo (by simp [hr.1]) fun z hz hneg => by
        by_contra h
        rw [Finset.mem_singleton] at h
        exact (not_le.mpr hneg) (han z hz h).meromorphicOrderAt_nonneg
    rw [laurentCoeff, show -(-1 : ℤ) - 1 = 0 by norm_num]
    simp only [zpow_zero, mul_one]
    rw [hres, Finset.sum_singleton]
    field_simp
  unfold residueAt
  exact Tendsto.limUnder_eq (tendsto_nhds_of_eventually_eq (by
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr using key r hr))

/-- DLMF §1.10(iii) (Picard's theorem): in any neighbourhood of an isolated essential
singularity (`f` analytic in a punctured disc of positive radius and not meromorphic at `z₀`),
`f` assumes every
value in `ℂ` with at most one exception. -/
@[dlmf 1.10.iii]
theorem picard_great {f : ℂ → ℂ} {z₀ : ℂ} {r₂ : ℝ} (hr₂ : 0 < r₂)
    (hf : DifferentiableOn ℂ f {z | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}) (hess : ¬ MeromorphicAt f z₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w₀ : ℂ, ∀ w : ℂ, w ≠ w₀ → ∃ z, 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < ε ∧ f z = w := by
  sorry

/-! ## §1.10(iv) Residue theorem -/

/-- DLMF 1.10.8 (residue theorem): if `f` is analytic within a simple closed contour `C` and
continuous within and on `C`, except at finitely many singularities `S` within `C`, and `C` is
described in the positive sense, then `(2πi)⁻¹ ∫_C f(z) dz` is the sum of the residues of `f`
within `C`. (Tau Ceti's `TauCeti.Contour.classicalResidueTheorem_nullHomologous` is the homology
form for meromorphic `f`.) -/
@[dlmf 1.10.E8]
theorem IsSimpleClosedContour.residue_theorem {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ}
    (hγ : IsSimpleClosedContour γ a b) (hpos : IsPositivelyOriented γ a b)
    (hS : ↑S ⊆ contourInterior γ a b)
    (hc : ContinuousOn f ((contourInterior γ a b ∪ γ '' Icc a b) \ ↑S))
    (hd : DifferentiableOn ℂ f (contourInterior γ a b \ ↑S)) :
    (2 * Real.pi * I)⁻¹ * contourIntegral γ a b f = ∑ s ∈ S, residueAt f s := by
  sorry

/-- DLMF 1.10.9 (phase or argument principle): if the singularities of `f` within the simple
closed contour `C` are poles, the zeros and poles within `C` lie in the finite set `S`, `f` is
analytic and nonvanishing on `C` (and elsewhere within `C` off `S`), and `C` is described in the
positive sense, then `N - P = (2πi)⁻¹ ∫_C f'(z)/f(z) dz = (2π)⁻¹ Δ_C(ph f(z))`, where
`N - P = ∑_{s ∈ S} ord_s f` counts zeros and poles with multiplicity and `Δ_C(ph f)` is the
change of any continuous phase `θ(t)` of `f(γ(t))` along `C`. -/
@[dlmf 1.10.E9]
theorem IsSimpleClosedContour.argument_principle {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    {S : Finset ℂ} (hγ : IsSimpleClosedContour γ a b) (hpos : IsPositivelyOriented γ a b)
    (hS : ↑S ⊆ contourInterior γ a b)
    (hf : ∀ z ∈ (contourInterior γ a b ∪ γ '' Icc a b) \ ↑S, AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hm : ∀ s ∈ S, MeromorphicAt f s ∧ meromorphicOrderAt f s ≠ ⊤) :
    (2 * Real.pi * I)⁻¹ * contourIntegral γ a b (logDeriv f) =
        ∑ s ∈ S, ((meromorphicOrderAt f s).untop₀ : ℂ) ∧
      ∀ θ : ℝ → ℝ, ContinuousOn θ (Icc a b) →
        (∀ t ∈ Icc a b, IsPhase (f (γ t)) (θ t)) →
        (θ b - θ a) / (2 * Real.pi) = ∑ s ∈ S, ((meromorphicOrderAt f s).untop₀ : ℝ) := by
  sorry

/-- DLMF 1.10.10: under the hypotheses of 1.10.9,
`(2πi)⁻¹ ∫_C z f'(z)/f(z) dz = (sum of locations of zeros) - (sum of locations of poles)`, each
location counted with multiplicity. -/
@[dlmf 1.10.E10]
theorem IsSimpleClosedContour.argumentPrinciple_mul_id {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    {S : Finset ℂ} (hγ : IsSimpleClosedContour γ a b) (hpos : IsPositivelyOriented γ a b)
    (hS : ↑S ⊆ contourInterior γ a b)
    (hf : ∀ z ∈ (contourInterior γ a b ∪ γ '' Icc a b) \ ↑S, AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hm : ∀ s ∈ S, MeromorphicAt f s ∧ meromorphicOrderAt f s ≠ ⊤) :
    (2 * Real.pi * I)⁻¹ * contourIntegral γ a b (fun z => z * logDeriv f z) =
      ∑ s ∈ S, ((meromorphicOrderAt f s).untop₀ : ℂ) * s := by
  sorry

/-- DLMF §1.10(iv) (Rouché's theorem): if `f` and `g` are analytic on and inside a simple closed
contour `C` and `|g(z)| < |f(z)|` on `C`, then `f` and `f + g` have the same number of zeros
inside `C`, counted with multiplicity. (Tau Ceti's `TauCeti.rouche_add` is the case of a
circle.) -/
@[dlmf 1.10.iv]
theorem IsSimpleClosedContour.rouche {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ}
    (hγ : IsSimpleClosedContour γ a b)
    (hf : AnalyticOnNhd ℂ f (contourInterior γ a b ∪ γ '' Icc a b))
    (hg : AnalyticOnNhd ℂ g (contourInterior γ a b ∪ γ '' Icc a b))
    (hlt : ∀ z ∈ γ '' Icc a b, ‖g z‖ < ‖f z‖) :
    (∑ᶠ z ∈ contourInterior γ a b, analyticOrderNatAt f z) =
      ∑ᶠ z ∈ contourInterior γ a b, analyticOrderNatAt (fun w => f w + g w) z := by
  have hC : IsCompact (γ '' Icc a b) := by
    refine isCompact_Icc.image_of_continuousOn ?_
    have := hγ.2.1.continuousOn
    rwa [uIcc_of_le hγ.1.le] at this
  have hK : contourInterior γ a b ∪ γ '' Icc a b = TauCeti.filledHull (γ '' Icc a b) :=
    sdiff_union_of_subset TauCeti.subset_filledHull
  rw [hK] at hf hg
  exact Complex.rouche_filledHull hC hf hg hlt

/-! ## §1.10(v) Maximum-modulus principle -/

/-- DLMF §1.10(v) (maximum principle for harmonic functions): if `u` is harmonic in a domain
`D` and attains its maximum over `D` at `z₀ ∈ D`, then `u` is constant in `D`. -/
@[dlmf 1.10.v]
theorem harmonic_eqOn_of_isMaxOn {u : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D) (hc : IsConnected D)
    (hu : InnerProductSpace.HarmonicOnNhd u D) {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hmax : IsMaxOn u D z₀) :
    EqOn u (fun _ => u z₀) D := by
  exact TauCeti.eqOn_const_of_harmonicOnNhd_of_isMaxOn_of_isOpen hD hz₀ hc.isPreconnected hu hmax

/-- DLMF §1.10(v) (maximum principle for harmonic functions on bounded domains): if `D` is
bounded and `u` is continuous on `D̄` and harmonic in `D`, then `u` attains its maximum over `D̄`
at some point of `∂D`. -/
@[dlmf 1.10.v]
theorem harmonic_exists_mem_frontier_isMaxOn {u : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D)
    (hb : Bornology.IsBounded D) (hne : D.Nonempty) (hc : ContinuousOn u (closure D))
    (hu : InnerProductSpace.HarmonicOnNhd u D) :
    ∃ z ∈ frontier D, IsMaxOn u (closure D) z := by
  have hcompact : IsCompact (frontier D) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hproper : D ≠ Set.univ := by
    intro h
    have hk : IsCompact (Set.univ : Set ℂ) := by simpa [h] using hb.isCompact_closure
    exact noncompact_univ ℂ hk
  have hfront : (frontier D).Nonempty := nonempty_frontier_iff.mpr ⟨hne, hproper⟩
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn hfront (hc.mono frontier_subset_closure)
  refine ⟨z, hz, ?_⟩
  have hbound := hu.subharmonicOn.le_of_le_frontier hD hb hc
    (InnerProductSpace.harmonicOnNhd_const (u z)) continuousOn_const (fun x hx => hmax hx)
  exact hbound

/-- DLMF 1.10.11 (Schwarz's lemma, inequalities): if `f` is analytic in `|z| < R`,
`|f(z)| ≤ M` there and `f(0) = 0`, then `|f(z)| ≤ M|z|/R` and `|f'(0)| ≤ M/R`. From Mathlib's
`Complex.dist_le_div_mul_dist_of_mapsTo_ball` and `Complex.norm_deriv_le_div_of_mapsTo_ball`. -/
@[dlmf 1.10.E11]
theorem schwarz_lemma {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hM : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) (h0 : f 0 = 0) :
    (∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M * ‖z‖ / R) ∧ ‖deriv f 0‖ ≤ M / R := by
  have hmaps : MapsTo f (ball 0 R) (closedBall (f 0) M) := fun z hz => by
    rw [h0, mem_closedBall, dist_zero_right]; exact hM z hz
  refine ⟨fun z hz => ?_, Complex.norm_deriv_le_div_of_mapsTo_ball hf hmaps hR⟩
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf hmaps hz
  rw [h0, dist_zero_right, dist_zero_right] at h
  calc ‖f z‖ ≤ M / R * ‖z‖ := h
    _ = M * ‖z‖ / R := by ring

/-- DLMF 1.10.11 (Schwarz's lemma, equality case): under the hypotheses of 1.10.11, equality
`|f(z₁)| = M|z₁|/R` at some `z₁ ≠ 0` or `|f'(0)| = M/R` holds iff `f(z) = Az` on `|z| < R`
with `|A| = M/R`. -/
@[dlmf 1.10.E11]
theorem schwarz_lemma_eq_iff {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hM : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) (h0 : f 0 = 0) :
    ((∃ z₁ ∈ ball (0 : ℂ) R, z₁ ≠ 0 ∧ ‖f z₁‖ = M * ‖z₁‖ / R) ∨ ‖deriv f 0‖ = M / R) ↔
      ∃ A : ℂ, ‖A‖ = M / R ∧ EqOn f (fun z => A * z) (ball 0 R) := by
  constructor
  · intro h
    have hmaps : MapsTo f (ball (0 : ℂ) R) (closedBall (f 0) M) := fun z hz => by
      simpa [mem_closedBall, h0, dist_zero_right] using hM z hz
    have hds : ∃ z ∈ ball (0 : ℂ) R, ‖dslope f 0 z‖ = M / R := by
      rcases h with ⟨z, hz, hz0, hzeq⟩ | hd
      · refine ⟨z, hz, ?_⟩
        rw [dslope_of_ne f hz0, slope_def_field, h0, sub_zero, sub_zero, norm_div, hzeq]
        field_simp
      · exact ⟨0, mem_ball_self hR, by simpa [dslope_same] using hd⟩
    obtain ⟨A, hAnorm, hAf⟩ :=
      Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div' hf hmaps hds
    refine ⟨A, hAnorm, ?_⟩
    intro z hz
    simpa [h0, smul_eq_mul, mul_comm] using hAf hz
  · rintro ⟨A, hAnorm, hAf⟩
    right
    have heq : f =ᶠ[𝓝 (0 : ℂ)] (fun z => A * z) :=
      eventually_of_mem (ball_mem_nhds _ hR) hAf
    have hd := ((hasDerivAt_id (0 : ℂ)).const_mul A).congr_of_eventuallyEq heq
    rw [hd.deriv]
    simpa using hAnorm

/-! ## §1.10(vi) Multivalued functions -/

/-- DLMF §1.10(vi), example: in `D = ℂ \ (-∞, 0]` the principal branch `√r e^{iθ/2}`
(`-π < θ < π`), that is `z^{1/2}`, and its negative are analytic branches of `√z`. -/
@[dlmf 1.10.vi]
theorem sqrt_branch_slitPlane :
    DifferentiableOn ℂ (fun z : ℂ => z ^ (1 / 2 : ℂ)) slitPlane ∧
      ∀ z : ℂ, (z ^ (1 / 2 : ℂ)) ^ 2 = z ∧ (-(z ^ (1 / 2 : ℂ))) ^ 2 = z := by
  refine ⟨fun z hz => (differentiableAt_id.cpow_const hz).differentiableWithinAt, fun z => ?_⟩
  have h : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
    rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
    exact cpow_nat_inv_pow z two_ne_zero
  exact ⟨h, by rw [neg_sq, h]⟩

/-- DLMF §1.10(vi), example: in `D = ℂ \ [0, ∞)` the branch `√r e^{iθ/2}` with `0 < θ < 2π`,
that is `i (-z)^{1/2}`, is analytic and squares to `z`. -/
@[dlmf 1.10.vi]
theorem sqrt_branch_compl_Ici :
    DifferentiableOn ℂ (fun z : ℂ => I * (-z) ^ (1 / 2 : ℂ)) {z | -z ∈ slitPlane} ∧
      ∀ z : ℂ, (I * (-z) ^ (1 / 2 : ℂ)) ^ 2 = z := by
  refine ⟨fun z hz => ?_, fun z => ?_⟩
  · exact ((differentiableAt_id.neg.cpow_const hz).const_mul I).differentiableWithinAt
  · rw [mul_pow, I_sq, show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num,
      cpow_nat_inv_pow _ two_ne_zero]
    ring

/-- DLMF §1.10(vi): `z = 0` is a branch point of `√z`: there is no continuous branch of `√z` in
any punctured neighbourhood of `0`. -/
@[dlmf 1.10.vi]
theorem not_exists_sqrt_branch_punctured {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, ContinuousOn g (ball 0 ε \ {0}) ∧ ∀ z ∈ ball (0 : ℂ) ε \ {0}, g z ^ 2 = z := by
  rintro ⟨g, hg, hgsq⟩
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by dsimp [r]; linarith
  let p : ℝ → ℂ := fun t => (r : ℂ) * exp ((2 * t : ℝ) * I)
  have hp (t : ℝ) : p t ∈ ball (0 : ℂ) ε \ {0} := by
    have hnorm : ‖p t‖ = r := by
      dsimp [p]
      rw [norm_mul, norm_exp]
      simp [abs_of_pos hr]
    constructor
    · simpa [mem_ball, dist_zero_right, hnorm] using hrε
    · simpa only [mem_singleton_iff] using
        (norm_pos_iff.mp (hnorm ▸ hr))
  let v : ℝ → ℂ := fun t => g (p t) * exp (-((t : ℂ) * I))
  have hc : Continuous v := by
    have hgp : Continuous (fun t => g (p t)) := by
      rw [← continuousOn_univ]
      exact hg.comp (by dsimp [p]; fun_prop) (fun t ht => hp t)
    exact hgp.mul (by fun_prop)
  have hvsq (t : ℝ) : v t ^ 2 = r := by
    dsimp [v]
    rw [mul_pow, hgsq _ (hp t), ← exp_nat_mul]
    dsimp [p]
    rw [mul_assoc, ← exp_add]
    have he : (2 * t : ℝ) * (I : ℂ) + 2 * -((t : ℂ) * I) = 0 := by
      push_cast
      ring
    rw [he, exp_zero, mul_one]
  have hv0 : v 0 = g r := by simp [v, p]
  have hvend : v Real.pi = -g r := by
    have he : exp ((2 * Real.pi : ℝ) * (I : ℂ)) = 1 := by
      push_cast
      rw [show (2 : ℂ) * Real.pi * I = (2 * Real.pi) * I by ring, exp_two_pi_mul_I]
    have he' : exp (-((Real.pi : ℂ) * I)) = -1 := by rw [exp_neg, exp_pi_mul_I]; norm_num
    simp [v, p, he, he']
  have hmaps : MapsTo v univ ({g r, -g r} : Set ℂ) := by
    intro t ht
    have hs : v t ^ 2 = (g r) ^ 2 := by rw [hvsq, ← hv0, hvsq]
    simpa only [mem_insert_iff, mem_singleton_iff] using sq_eq_sq_iff_eq_or_eq_neg.mp hs
  have hconst := isPreconnected_univ.constant_of_mapsTo
    (Set.toFinite ({g r, -g r} : Set ℂ)).isDiscrete hc.continuousOn hmaps
    (mem_univ (0 : ℝ)) (mem_univ Real.pi)
  rw [hv0, hvend] at hconst
  have hz : g r = 0 := by linear_combination (1 / 2 : ℂ) * hconst
  have hs := hvsq 0
  rw [hv0, hz, zero_pow (by decide)] at hs
  exact hr.ne' (Complex.ofReal_eq_zero.mp hs.symm)


/-- DLMF §1.10(vi), example: for `α`, `β ∈ ℂ`, `F(z) = (1 - z)^α (1 + z)^β` with principal values
is analytic (a branch of `F`) in the plane cut along `[1, ∞)` and `(-∞, -1]`. -/
@[dlmf 1.10.vi]
theorem differentiableOn_one_sub_cpow_mul_one_add_cpow (α β : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z) ^ α * (1 + z) ^ β)
      {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane} := by
  intro z hz
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (1 - z) ^ α) z :=
    ((differentiableAt_const _).sub differentiableAt_id).cpow_const hz.1
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (1 + z) ^ β) z :=
    ((differentiableAt_const _).add differentiableAt_id).cpow_const hz.2
  exact (h1.mul h2).differentiableWithinAt

/-! ## §1.10(vii) Inverse functions -/

/-- The residue at `z₀` of `H(z) / (z - z₀)ⁿ⁺¹`, `H` analytic at `z₀`, is `H⁽ⁿ⁾(z₀) / n!`. -/
theorem residueAt_div_sub_pow {K H : ℂ → ℂ} {z₀ : ℂ} {n : ℕ} (hH : AnalyticAt ℂ H z₀)
    (hK : ∀ᶠ z in 𝓝[≠] z₀, K z = H z / (z - z₀) ^ (n + 1)) :
    residueAt K z₀ = iteratedDeriv n H z₀ / n.factorial := by
  obtain ⟨δ, hδ, hHδ⟩ := hH.exists_ball_analyticOnNhd
  obtain ⟨δ', hδ', hKδ⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hK)
  have key : ∀ r ∈ Ioo 0 (min δ δ'), laurentCoeff K z₀ r (-1) =
      iteratedDeriv n H z₀ / n.factorial := by
    intro r hr
    have hd : DiffContOnCl ℂ H (ball z₀ r) :=
      (hHδ.differentiableOn.mono (closedBall_subset_ball (hr.2.trans_le (min_le_left _ _)))
        ).diffContOnCl_ball le_rfl
    have hc := hd.circleIntegral_one_div_sub_center_pow_smul hr.1 n
    have hcongr : (∮ z in C(z₀, r), K z * (z - z₀) ^ (-(-1 : ℤ) - 1)) =
        ∮ z in C(z₀, r), (1 / (z - z₀) ^ (n + 1)) • H z := by
      refine circleIntegral.integral_congr hr.1.le fun z hz => ?_
      have hzr : dist z z₀ = r := by rw [dist_eq_norm]; simpa using hz
      have hz0 : z ≠ z₀ := by
        rintro rfl
        simp only [dist_self] at hzr
        exact hr.1.ne hzr
      simp only [show -(-1 : ℤ) - 1 = 0 by norm_num, zpow_zero, mul_one, smul_eq_mul]
      rw [hKδ (hzr.trans_lt (hr.2.trans_le (min_le_right _ _))) hz0]
      ring
    rw [laurentCoeff, hcongr, hc, smul_eq_mul]
    field_simp [Real.pi_ne_zero, I_ne_zero]
  unfold residueAt
  exact Tendsto.limUnder_eq (tendsto_nhds_of_eventually_eq (by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hδ')] with r hr using key r hr))

/-- Lagrange–Bürmann expansion in terms of residues: for `φ` analytic at `z₀` with a simple zero
there and `g` analytic at `z₀`, for `z` near `z₀`,
`g(z) - g(z₀) = ∑ₙ Res_{z₀}(g'/φⁿ⁺¹) / (n + 1) · φ(z)ⁿ⁺¹`. -/
theorem eventually_hasSum_residueAt_lagrange {φ g : ℂ → ℂ} {z₀ : ℂ} (hφ : AnalyticAt ℂ φ z₀)
    (hφ₀ : φ z₀ = 0) (hd : deriv φ z₀ ≠ 0) (hg : AnalyticAt ℂ g z₀) :
    ∀ᶠ z in 𝓝 z₀, HasSum (fun n : ℕ =>
      residueAt (fun z => deriv g z / φ z ^ (n + 1)) z₀ / (n + 1) * φ z ^ (n + 1))
      (g z - g z₀) := by
  set h : ℂ → ℂ := fun t => φ (z₀ + t) with hhdef
  set G : ℂ → ℂ := fun t => g (z₀ + t) with hGdef
  have hadd : AnalyticAt ℂ (fun t : ℂ => z₀ + t) 0 := analyticAt_const.add analyticAt_id
  have hh : AnalyticAt ℂ h 0 := hφ.comp_of_eq hadd (add_zero z₀)
  have hG : AnalyticAt ℂ G 0 := hg.comp_of_eq hadd (add_zero z₀)
  have hh0 : h 0 = 0 := by simp [hhdef, hφ₀]
  have hhd : deriv h 0 ≠ 0 := by
    rw [hhdef, deriv_comp_const_add, add_zero]; exact hd
  obtain ⟨ε, hε, hsum⟩ := Complex.hasSum_lagrangeInversion hh hh0 hhd hG
  set Ψ : ℂ → ℂ := fun t => (dslope h 0 t)⁻¹ with hΨdef
  have hΨ : AnalyticAt ℂ Ψ 0 := (hh.dslope 0).inv (by rwa [dslope_same])
  have hsub : AnalyticAt ℂ (fun z : ℂ => z - z₀) z₀ := analyticAt_id.sub analyticAt_const
  have hφeq : ∀ z, φ z = (z - z₀) * dslope h 0 (z - z₀) := by
    intro z
    have := sub_smul_dslope h 0 (z - z₀)
    rw [hh0, sub_zero, sub_zero, smul_eq_mul] at this
    rw [this, hhdef]
    simp
  have hcoef : ∀ n : ℕ, residueAt (fun z => deriv g z / φ z ^ (n + 1)) z₀ / (n + 1) =
      iteratedDeriv n (fun t => deriv G t * Ψ t ^ (n + 1)) 0 / (n + 1).factorial := by
    intro n
    have hH : AnalyticAt ℂ (fun z => deriv g z * Ψ (z - z₀) ^ (n + 1)) z₀ :=
      hg.deriv.mul ((hΨ.comp_of_eq hsub (sub_self z₀)).pow _)
    rw [residueAt_div_sub_pow hH (Eventually.of_forall fun z => by
      rw [hφeq z]
      simp only [hΨdef, div_eq_mul_inv, mul_pow, mul_inv, inv_pow]
      ring)]
    have htr := congrFun (iteratedDeriv_comp_const_add n
      (fun z => deriv g z * Ψ (z - z₀) ^ (n + 1)) z₀) 0
    simp only [add_zero, add_sub_cancel_left] at htr
    rw [← htr]
    have hfun : (fun t => deriv G t * Ψ t ^ (n + 1)) =
        fun t => deriv g (z₀ + t) * Ψ t ^ (n + 1) := by
      funext t
      rw [hGdef, deriv_comp_const_add]
    rw [hfun, Nat.factorial_succ]
    push_cast
    field_simp
  filter_upwards [ball_mem_nhds z₀ hε] with z hz
  have hw : ‖z - z₀‖ < ε := by simpa [dist_eq_norm] using hz
  have := hsum (z - z₀) hw
  simp only [hGdef, hhdef, add_sub_cancel, add_zero] at this
  refine this.congr_fun fun n => ?_
  rw [hcoef n]

/-- The local inverse of an analytic function with nonvanishing derivative, packaged. -/
private theorem exists_analyticAt_localInverse {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hd : deriv f z₀ ≠ 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (f z₀) ∧ F (f z₀) = z₀ ∧
      (∀ᶠ w in 𝓝 (f z₀), f (F w) = w) ∧ (∀ᶠ z in 𝓝 z₀, F (f z) = z) :=
  ⟨hf.hasStrictDerivAt.localInverse _ _ _ hd, hf.analyticAt_localInverse hd,
    HasStrictFDerivAt.localInverse_apply_image .., HasStrictDerivAt.eventually_right_inverse ..,
    HasStrictDerivAt.eventually_left_inverse ..⟩

/-- DLMF 1.10.12–1.10.13 (Lagrange inversion theorem): if `f` is analytic at `z₀`,
`f'(z₀) ≠ 0` and `w₀ = f(z₀)`, then `f(z) = w` has a unique solution `z = F(w)` analytic at `w₀`
with `F(w₀) = z₀`, and `F(w) = z₀ + ∑_{n ≥ 1} Fₙ (w - w₀)ⁿ` near `w₀`, where `n Fₙ` is the
residue of `1/(f(z) - f(z₀))ⁿ` at `z₀`. Uniqueness is local: `F(f(z)) = z` near `z₀`. -/
@[dlmf 1.10.E12, dlmf 1.10.E13]
theorem lagrange_inversion {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (hd : deriv f z₀ ≠ 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (f z₀) ∧ F (f z₀) = z₀ ∧
      (∀ᶠ w in 𝓝 (f z₀), f (F w) = w) ∧ (∀ᶠ z in 𝓝 z₀, F (f z) = z) ∧
      ∀ᶠ w in 𝓝 (f z₀), HasSum (fun n : ℕ =>
        residueAt (fun z => ((f z - f z₀) ^ (n + 1))⁻¹) z₀ / (n + 1) * (w - f z₀) ^ (n + 1))
        (F w - z₀) := by
  obtain ⟨F, hF, hF₀, hR, hL⟩ := exists_analyticAt_localInverse hf hd
  refine ⟨F, hF, hF₀, hR, hL, ?_⟩
  have hφd : deriv (fun z => f z - f z₀) z₀ ≠ 0 := by rwa [deriv_sub_const]
  have hev := eventually_hasSum_residueAt_lagrange (φ := fun z => f z - f z₀) (g := fun z => z)
    (hf.sub analyticAt_const) (sub_self _) hφd analyticAt_id
  have hT : Tendsto F (𝓝 (f z₀)) (𝓝 z₀) := by
    have := hF.continuousAt.tendsto; rwa [hF₀] at this
  filter_upwards [hT.eventually hev, hR] with w h1 h2
  rw [h2] at h1
  simpa only [deriv_id'', one_div] using h1

/-- DLMF 1.10.14: under the hypotheses of 1.10.12, for `g` analytic at `z₀`,
`g(F(w)) = g(z₀) + ∑_{n ≥ 1} Gₙ (w - w₀)ⁿ` near `w₀`, where `n Gₙ` is the residue of
`g'(z)/(f(z) - f(z₀))ⁿ` at `z₀`. -/
@[dlmf 1.10.E14]
theorem lagrange_burmann {f g F : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (hd : deriv f z₀ ≠ 0)
    (hg : AnalyticAt ℂ g z₀) (hF : AnalyticAt ℂ F (f z₀)) (hF₀ : F (f z₀) = z₀)
    (hFinv : ∀ᶠ w in 𝓝 (f z₀), f (F w) = w) :
    ∀ᶠ w in 𝓝 (f z₀), HasSum (fun n : ℕ =>
      residueAt (fun z => deriv g z / (f z - f z₀) ^ (n + 1)) z₀ / (n + 1) * (w - f z₀) ^ (n + 1))
      (g (F w) - g z₀) := by
  have hφd : deriv (fun z => f z - f z₀) z₀ ≠ 0 := by rwa [deriv_sub_const]
  have hev := eventually_hasSum_residueAt_lagrange (φ := fun z => f z - f z₀)
    (hf.sub analyticAt_const) (sub_self _) hφd hg
  have hT : Tendsto F (𝓝 (f z₀)) (𝓝 z₀) := by
    have := hF.continuousAt.tendsto; rwa [hF₀] at this
  filter_upwards [hT.eventually hev, hFinv] with w h1 h2
  rwa [h2] at h1

/-- DLMF 1.10.15–1.10.16, stronger than DLMF, which assumes `μ = m ≥ 1` and `f` analytic at
`z₀`: if `φ` is analytic at `z₀`, `φ(z₀) = 0`, `φ'(z₀) ≠ 0` and `φ(z)^m = f(z) - f(z₀)` near `z₀`
(any `m : ℕ`), then for every `ζ` near `0`, `z = z₀ + ∑_{n ≥ 1} Fₙ ζⁿ` solves
`f(z) = f(z₀) + ζ^m`, where `n Fₙ` is the residue of `1/φ(z)ⁿ` at `z₀`. -/
@[dlmf 1.10.E15, dlmf 1.10.E16]
theorem lagrange_inversion_extended' {f φ : ℂ → ℂ} {z₀ : ℂ} {m : ℕ}
    (hφ : AnalyticAt ℂ φ z₀) (hφ₀ : φ z₀ = 0) (hφd : deriv φ z₀ ≠ 0)
    (hroot : ∀ᶠ z in 𝓝 z₀, φ z ^ m = f z - f z₀) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), ∃ z : ℂ,
      HasSum (fun n : ℕ => residueAt (fun z => (φ z ^ (n + 1))⁻¹) z₀ / (n + 1) * ζ ^ (n + 1))
        (z - z₀) ∧ f z = f z₀ + ζ ^ m := by
  obtain ⟨F, hF, hF₀, hR, -⟩ := exists_analyticAt_localInverse hφ hφd
  rw [hφ₀] at hF hF₀ hR
  have hev := eventually_hasSum_residueAt_lagrange (g := fun z => z) hφ hφ₀ hφd analyticAt_id
  have hT : Tendsto F (𝓝 0) (𝓝 z₀) := by
    have := hF.continuousAt.tendsto; rwa [hF₀] at this
  filter_upwards [hT.eventually (hev.and hroot), hR] with ζ ⟨h1, h2⟩ h3
  refine ⟨F ζ, ?_, ?_⟩
  · rw [h3] at h1
    simpa only [deriv_id'', one_div] using h1
  · rw [h3] at h2
    linear_combination -h2

/-- DLMF 1.10.15–1.10.16 (extended inversion theorem), case of an integer `μ = m ≥ 1`:
suppose `f(z) - f(z₀)` has a zero of order `m` at `z₀` and `φ` is an analytic `m`-th root of it,
`φ(z)^m = f(z) - f(z₀)` near `z₀` with `φ(z₀) = 0`, `φ'(z₀) ≠ 0` (the choice of `φ` is the choice
of branch of `(f(z) - f(z₀))^{1/m}`). Then for every `ζ` near `0`, in particular for every
`m`-th root `ζ = (w - w₀)^{1/m}`, `z = z₀ + ∑_{n ≥ 1} Fₙ ζⁿ` solves `f(z) = w₀ + ζ^m` (1.10.12),
where `n Fₙ` is the residue of `1/φ(z)ⁿ = 1/(f(z) - f(z₀))^{n/m}` at `z₀`. Different roots `ζ`
give the different solutions. DLMF allows real `μ > 0` with a series in `(z - z₀)^{μ + n}`; only
integer `μ` is formalized. -/
@[dlmf 1.10.E15, dlmf 1.10.E16]
theorem lagrange_inversion_extended {f φ : ℂ → ℂ} {z₀ : ℂ} {m : ℕ} (_hm : 1 ≤ m)
    (_hf : AnalyticAt ℂ f z₀)
    (hφ : AnalyticAt ℂ φ z₀) (hφ₀ : φ z₀ = 0) (hφd : deriv φ z₀ ≠ 0)
    (hroot : ∀ᶠ z in 𝓝 z₀, φ z ^ m = f z - f z₀) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), ∃ z : ℂ,
      HasSum (fun n : ℕ => residueAt (fun z => (φ z ^ (n + 1))⁻¹) z₀ / (n + 1) * ζ ^ (n + 1))
        (z - z₀) ∧ f z = f z₀ + ζ ^ m :=
  lagrange_inversion_extended' hφ hφ₀ hφd hroot

/-- DLMF 1.10.17, stronger than DLMF, which assumes `μ = m ≥ 1`, `f` analytic at `z₀` and
`φ(z)^m = f(z) - f(z₀)`: only `φ` (analytic at `z₀` with a simple zero there) and `g` matter.
For `ζ` near `0` and `z = z₀ + ∑ Fₙ ζⁿ`, `g(z) = g(z₀) + ∑_{n ≥ 1} Gₙ ζⁿ`, where `n Gₙ` is the
residue of `g'(z)/φ(z)ⁿ` at `z₀`. -/
@[dlmf 1.10.E17]
theorem lagrange_burmann_extended' {φ g : ℂ → ℂ} {z₀ : ℂ}
    (hφ : AnalyticAt ℂ φ z₀) (hφ₀ : φ z₀ = 0) (hφd : deriv φ z₀ ≠ 0) (hg : AnalyticAt ℂ g z₀) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), ∀ z : ℂ,
      HasSum (fun n : ℕ => residueAt (fun z => (φ z ^ (n + 1))⁻¹) z₀ / (n + 1) * ζ ^ (n + 1))
        (z - z₀) →
      HasSum (fun n : ℕ => residueAt (fun z => deriv g z / φ z ^ (n + 1)) z₀ / (n + 1) *
        ζ ^ (n + 1)) (g z - g z₀) := by
  obtain ⟨F, hF, hF₀, hR, -⟩ := exists_analyticAt_localInverse hφ hφd
  rw [hφ₀] at hF hF₀ hR
  have hev := eventually_hasSum_residueAt_lagrange (g := fun z => z) hφ hφ₀ hφd analyticAt_id
  have hevg := eventually_hasSum_residueAt_lagrange hφ hφ₀ hφd hg
  have hT : Tendsto F (𝓝 0) (𝓝 z₀) := by
    have := hF.continuousAt.tendsto; rwa [hF₀] at this
  filter_upwards [hT.eventually (hev.and hevg), hR] with ζ ⟨h1, h2⟩ h3 z hz
  rw [h3] at h1 h2
  simp only [deriv_id'', one_div] at h1
  have hzF : z = F ζ := sub_left_injective (hz.unique h1)
  rw [hzF]
  exact h2

/-- DLMF 1.10.17: in the setting of 1.10.15–1.10.16 (integer `μ = m`), for `g` analytic at `z₀`
and `z = z₀ + ∑ Fₙ ζⁿ` the solution belonging to `ζ`,
`g(z) = g(z₀) + ∑_{n ≥ 1} Gₙ ζⁿ`, where `n Gₙ` is the residue of
`g'(z)/(f(z) - f(z₀))^{n/m} = g'(z)/φ(z)ⁿ` at `z₀`. -/
@[dlmf 1.10.E17]
theorem lagrange_burmann_extended {f φ g : ℂ → ℂ} {z₀ : ℂ} {m : ℕ} (_hm : 1 ≤ m)
    (_hf : AnalyticAt ℂ f z₀) (hφ : AnalyticAt ℂ φ z₀) (hφ₀ : φ z₀ = 0) (hφd : deriv φ z₀ ≠ 0)
    (_hroot : ∀ᶠ z in 𝓝 z₀, φ z ^ m = f z - f z₀) (hg : AnalyticAt ℂ g z₀) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), ∀ z : ℂ,
      HasSum (fun n : ℕ => residueAt (fun z => (φ z ^ (n + 1))⁻¹) z₀ / (n + 1) * ζ ^ (n + 1))
        (z - z₀) →
      HasSum (fun n : ℕ => residueAt (fun z => deriv g z / φ z ^ (n + 1)) z₀ / (n + 1) *
        ζ ^ (n + 1)) (g z - g z₀) :=
  lagrange_burmann_extended' hφ hφ₀ hφd hg

/-! ## §1.10(viii) Functions defined by contour integrals -/

/-- DLMF 1.10.18: if `f(z, t)` is analytic in `z ∈ D` for each `t ∈ [a, b]` and continuous in
both variables, then `F(z) = ∫_a^b f(z, t) dt` is analytic in `D`, and its derivatives are
obtained by differentiating under the integral sign. -/
@[dlmf 1.10.E18]
theorem differentiableOn_intervalIntegral_param {f : ℂ → ℝ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    {a b : ℝ} (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun z => f z t) D)
    (hc : ContinuousOn (Function.uncurry f) (D ×ˢ Icc a b)) :
    DifferentiableOn ℂ (fun z => ∫ t in a..b, f z t) D ∧
      ∀ n : ℕ, ∀ z ∈ D, iteratedDeriv n (fun z => ∫ t in a..b, f z t) z =
        ∫ t in a..b, iteratedDeriv n (fun z => f z t) z := by
  have hmeas : ∀ z ∈ D, AEStronglyMeasurable (f z) (volume.restrict (uIoc a b)) := by
    intro z hz
    exact ((hc.uncurry_left z hz).aestronglyMeasurable measurableSet_Icc).mono_set
      (by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self)
  have hdiff : ∀ᵐ t ∂(volume.restrict (uIoc a b)),
      DifferentiableOn ℂ (fun z => f z t) D := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    exact hf t (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht)
  have hdom : ∀ z ∈ D, ∃ V ∈ 𝓝 z, ∃ g : ℝ → ℝ,
      Integrable g (volume.restrict (uIoc a b)) ∧
      ∀ᵐ t ∂(volume.restrict (uIoc a b)), ∀ w ∈ V, ‖f w t‖ ≤ g t := by
    intro z hz
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hD z hz
    have hr2 : 0 < r / 2 := half_pos hr
    have hK : IsCompact (closedBall z (r / 2) ×ˢ Icc a b) :=
      (isCompact_closedBall z (r / 2)).prod isCompact_Icc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono fun p hp =>
      ⟨hsub (closedBall_subset_ball (by linarith) hp.1), hp.2⟩)
    refine ⟨ball z (r / 2), ball_mem_nhds z hr2, fun _ => C, (by
      rw [uIoc_of_le hab]
      exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume a b).1), ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht w hw
    refine hC (w, t) ⟨ball_subset_closedBall hw, ?_⟩
    simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht
  exact ⟨Complex.differentiableOn_intervalIntegral_of_locally_dominated hD a b hmeas hdiff hdom,
    fun n z hz => Complex.iteratedDeriv_intervalIntegral_of_locally_dominated
      hD a b hmeas hdiff hdom n hz⟩

/-- DLMF §1.10(viii) and 1.10.19 (improper integrals, `b = ∞`): if `f(z, t)` is analytic in
`z ∈ D` for each `t ≥ a`, continuous in both variables on `D × [a, ∞)`, and
`∫_a^∞ f(z, t) dt = F(z)` converges uniformly on compact subsets of `D` (1.10.19: the tails
`∫_{a₁}^∞` are uniformly small, equivalently the partial integrals `∫_a^c` converge uniformly
as `c → ∞`), then `F` is analytic in `D`. -/
@[dlmf 1.10.E19]
theorem differentiableOn_improperIntegral_param {f : ℂ → ℝ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    {a : ℝ} (hf : ∀ t ∈ Ici a, DifferentiableOn ℂ (fun z => f z t) D)
    (hc : ContinuousOn (Function.uncurry f) (D ×ˢ Ici a)) {F : ℂ → ℂ}
    (hu : ∀ K ⊆ D, IsCompact K →
      TendstoUniformlyOn (fun c z => ∫ t in a..c, f z t) F atTop K) :
    DifferentiableOn ℂ F D := by
  have hl : TendstoLocallyUniformlyOn (fun c z => ∫ t in a..c, f z t) F atTop D :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr hu
  apply hl.differentiableOn ?_ hD
  filter_upwards [eventually_ge_atTop a] with c hc'
  exact (differentiableOn_intervalIntegral_param hD hc'
    (fun t ht => hf t ht.1) (hc.mono fun p hp => ⟨hp.1, hp.2.1⟩)).1

/-- DLMF §1.10(viii) (improper integrals with a singularity at a finite `b`): if `f(z, t)` is
analytic in `z ∈ D` for each `t ∈ [a, b)`, continuous in both variables on `D × [a, b)`, and
`∫_a^b f(z, t) dt = F(z)` converges uniformly on compact subsets of `D` (the partial integrals
`∫_a^c` converge uniformly as `c → b-`), then `F` is analytic in `D`. -/
@[dlmf 1.10.viii]
theorem differentiableOn_improperIntegral_param_of_lt {f : ℂ → ℝ → ℂ} {D : Set ℂ}
    (hD : IsOpen D) {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Ico a b, DifferentiableOn ℂ (fun z => f z t) D)
    (hc : ContinuousOn (Function.uncurry f) (D ×ˢ Ico a b)) {F : ℂ → ℂ}
    (hu : ∀ K ⊆ D, IsCompact K →
      TendstoUniformlyOn (fun c z => ∫ t in a..c, f z t) F (𝓝[<] b) K) :
    DifferentiableOn ℂ F D := by
  have hl : TendstoLocallyUniformlyOn (fun c z => ∫ t in a..c, f z t) F (𝓝[<] b) D :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr hu
  apply hl.differentiableOn ?_ hD
  filter_upwards [Ioo_mem_nhdsLT hab] with c hc'
  exact (differentiableOn_intervalIntegral_param hD hc'.1.le
    (fun t ht => hf t ⟨ht.1, lt_of_le_of_lt ht.2 hc'.2⟩)
    (hc.mono fun p hp => ⟨hp.1, hp.2.1, lt_of_le_of_lt hp.2.2 hc'.2⟩)).1

/-- DLMF §1.10(viii) (`M`-test for integrals): if `|f(z, t)| ≤ M(t)` for `z ∈ S`, `t ≥ a`, and
`∫_a^∞ M(t) dt` converges, then `∫_a^∞ f(z, t) dt` converges absolutely and uniformly on `S`. -/
@[dlmf 1.10.viii]
theorem tendstoUniformlyOn_integral_of_norm_le {f : ℂ → ℝ → ℂ} {S : Set ℂ} {a : ℝ} {M : ℝ → ℝ}
    (hmeas : ∀ z ∈ S, AEStronglyMeasurable (f z) (volume.restrict (Ioi a)))
    (hM : IntegrableOn M (Ioi a)) (hle : ∀ z ∈ S, ∀ t ∈ Ioi a, ‖f z t‖ ≤ M t) :
    (∀ z ∈ S, IntegrableOn (f z) (Ioi a)) ∧
      TendstoUniformlyOn (fun c z => ∫ t in a..c, f z t) (fun z => ∫ t in Ioi a, f z t)
        atTop S := by
  have hi : ∀ z ∈ S, IntegrableOn (f z) (Ioi a) := by
    intro z hz
    apply hM.mono' (hmeas z hz)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hle z hz t ht
  have hMn : IntegrableOn (fun t => ‖M t‖) (Ioi a) := hM.norm
  refine ⟨hi, Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_⟩
  have ht : Tendsto (fun c : ℝ => ∫ t in Ioi c, ‖M t‖) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  filter_upwards [eventually_ge_atTop a, ht.eventually (gt_mem_nhds hε)] with c hc hεc z hz
  have hzi := hi z hz
  have htail : (∫ t in Ioi a, f z t) - (∫ t in a..c, f z t) = ∫ t in Ioi c, f z t := by
    have he := intervalIntegral.integral_interval_add_Ioi hzi (hzi.mono_set (Ioi_subset_Ioi hc))
    linear_combination -he
  rw [dist_eq_norm, htail]
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le
    (hMn.mono_set (Ioi_subset_Ioi hc)) ?_) hεc
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (hle z hz t (lt_of_le_of_lt hc ht)).trans (le_abs_self _)

end DLMF.AlgebraicAnalytic
