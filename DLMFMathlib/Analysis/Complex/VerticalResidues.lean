/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.VerticalLineShift
public import DLMFMathlib.Analysis.Complex.MellinBarnesSeries
public import TauCeti.Analysis.Contour.Residue.Theorem
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Vertical contour shifts with Tau Ceti residues

The vertical-line shift across finitely many isolated singularities is expressed using
`TauCeti.Contour.residue` when the singularities are meromorphic. The single-pole iteration
is likewise expressed as a series of these residues. Line integrals use `dy`, giving a
factor `2π` in the residue formula.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology Real

namespace Complex

/-- For all sufficiently small circles, the integral about a meromorphic point is `2πi`
times its residue. Removable singularities, including exceptional point values, are allowed. -/
theorem eventually_circleIntegral_eq_two_pi_mul_I_residue {f : ℂ → ℂ} {p : ℂ}
    (hm : MeromorphicAt f p) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), circleIntegral f p r =
      2 * (Real.pi : ℂ) * I * TauCeti.Contour.residue f p := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.mp hm.eventually_analyticAt
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  have han : ∀ z ∈ closedBall p r, z ≠ p → AnalyticAt ℂ f z := fun z hz hzp =>
    hεs ⟨closedBall_subset_ball hr.2 hz, hzp⟩
  have hmo : MeromorphicOn f (closedBall p r) := fun z hz => by
    by_cases hzp : z = p
    · exact hzp ▸ hm
    · exact (han z hz hzp).meromorphicAt
  simpa using TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg
    hr.1 {p} hmo (by simp [hr.1]) (by
      intro z hz hneg
      by_contra hzp
      have hne : z ≠ p := by simpa using hzp
      exact (not_le.mpr hneg) (han z hz hne).meromorphicOrderAt_nonneg)

/-- A vertical-line shift across finitely many meromorphic singularities, with the residues
defined by Tau Ceti. The horizontal connector integrals need only tend to zero. -/
theorem integral_vertical_sub_eq_two_pi_mul_sum_residue {f : ℂ → ℂ} {d c : ℝ}
    (hdc : d < c) (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hf : DifferentiableOn ℂ f (re ⁻¹' Icc d c \ P))
    (hm : ∀ p ∈ P, MeromorphicAt f p)
    (hd : Integrable fun y : ℝ => f (d + y * I))
    (hc : Integrable fun y : ℝ => f (c + y * I))
    (htop : Tendsto (fun T : ℝ => ∫ x in d..c, f (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in d..c, f (x + T * I)) atBot (𝓝 0)) :
    (∫ y : ℝ, f (c + y * I)) - ∫ y : ℝ, f (d + y * I) =
      2 * (Real.pi : ℂ) * ∑ p ∈ P, TauCeti.Contour.residue f p := by
  obtain ⟨ρ, hρ, hshift⟩ :=
    integral_vertical_sub_eq_sum_circleIntegral hdc P hP hf hd hc htop hbot
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ p ∈ P, circleIntegral f p r =
      2 * (Real.pi : ℂ) * I * TauCeti.Contour.residue f p :=
    (eventually_all_finset P).mpr fun p hp =>
      eventually_circleIntegral_eq_two_pi_mul_I_residue (hm p hp)
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 ρ := Ioo_mem_nhdsGT hρ
  obtain ⟨r, hr, he⟩ := (hsmall.and he).exists
  have hs := hshift r hr.1 hr.2
  rw [Finset.sum_congr rfl he, ← Finset.mul_sum] at hs
  apply mul_left_cancel₀ I_ne_zero
  calc I * ((∫ y : ℝ, f (c + y * I)) - ∫ y : ℝ, f (d + y * I)) =
      (2 * (Real.pi : ℂ) * I) * ∑ p ∈ P, TauCeti.Contour.residue f p := hs
    _ = _ := by ring

/-- Absolute vertical integrability is preserved by the Mellin inversion weight at a
positive real argument. -/
theorem _root_.integrable_mellinInv_integrand {G : ℂ → ℂ} {σ x : ℝ}
    (hG : VerticalIntegrable G σ) (hx : 0 < x) :
    Integrable fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I)) * G (σ + y * I) := by
  refine (hG.norm.const_mul (x ^ (-σ))).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact ((continuous_iff_continuousAt.mpr fun y =>
      (differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))).continuousAt.comp
        (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)).aestronglyMeasurable).mul
          hG.aestronglyMeasurable
  · rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
    simp

/-- Inverse Mellin transforms are additive on a line of absolute convergence. -/
theorem _root_.mellinInv_add {F G : ℂ → ℂ} {σ x : ℝ}
    (hF : VerticalIntegrable F σ) (hG : VerticalIntegrable G σ) (hx : 0 < x) :
    mellinInv σ (fun z => F z + G z) x = mellinInv σ F x + mellinInv σ G x := by
  unfold mellinInv
  simp only [smul_eq_mul, mul_add]
  rw [integral_add (integrable_mellinInv_integrand hF hx)
    (integrable_mellinInv_integrand hG hx), smul_add]

/-- Mellin inversion shifted to the right across finitely many meromorphic poles, with
Tau Ceti residues and the sign of the clockwise contour. Horizontal connectors are given
for the weighted integrand, and absolute convergence is required only on the two lines. -/
theorem mellinInv_eq_sum_residue_add {G : ℂ → ℂ} {d c x : ℝ}
    (hdc : d < c) (hx : 0 < x) (P : Finset ℂ)
    (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hf : DifferentiableOn ℂ (fun z => (x : ℂ) ^ (-z) * G z) (re ⁻¹' Icc d c \ P))
    (hm : ∀ p ∈ P, MeromorphicAt (fun z => (x : ℂ) ^ (-z) * G z) p)
    (hd : VerticalIntegrable G d) (hc : VerticalIntegrable G c)
    (htop : Tendsto (fun T : ℝ => ∫ σ in d..c,
      (x : ℂ) ^ (-((σ : ℂ) + T * I)) * G (σ + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ σ in d..c,
      (x : ℂ) ^ (-((σ : ℂ) + T * I)) * G (σ + T * I)) atBot (𝓝 0)) :
    mellinInv d G x = ∑ p ∈ P, TauCeti.Contour.residue
      (fun z => -((x : ℂ) ^ (-z) * G z)) p + mellinInv c G x := by
  let f : ℂ → ℂ := fun z => (x : ℂ) ^ (-z) * G z
  have hline (σ : ℝ) (hi : VerticalIntegrable G σ) :
      Integrable fun y : ℝ => f (σ + y * I) := integrable_mellinInv_integrand hi hx
  have hs := integral_vertical_sub_eq_two_pi_mul_sum_residue hdc P hP hf hm
    (hline d hd) (hline c hc) htop hbot
  have hneg : ∀ p : ℂ, TauCeti.Contour.residue (fun z => -f z) p =
      -TauCeti.Contour.residue f p := by
    intro p
    simpa only [neg_one_mul] using TauCeti.Contour.residue_const_mul (f := f) (z₀ := p) (-1)
  change mellinInv d G x = ∑ p ∈ P, TauCeti.Contour.residue (fun z => -f z) p +
    mellinInv c G x
  simp only [hneg, Finset.sum_neg_distrib]
  unfold mellinInv
  simp only [smul_eq_mul]
  change (1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ, f (d + y * I)) =
    -(∑ p ∈ P, TauCeti.Contour.residue f p) +
      (1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ, f (c + y * I))
  rw [real_smul, real_smul]
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  change (∫ y : ℝ, f (c + y * I)) - (∫ y : ℝ, f (d + y * I)) =
    2 * (Real.pi : ℂ) * ∑ p ∈ P, TauCeti.Contour.residue f p at hs
  generalize (∫ y : ℝ, f (c + y * I)) = Ic at hs ⊢
  generalize (∫ y : ℝ, f (d + y * I)) = Id at hs ⊢
  generalize (∑ p ∈ P, TauCeti.Contour.residue f p) = S at hs ⊢
  push_cast
  field_simp
  linear_combination -hs

/-- Uniform decay of the unweighted transform on a strip supplies the vanishing horizontal
connectors for a Mellin contour shift with Tau Ceti residues. -/
theorem mellinInv_eq_sum_residue_add_of_iSup_norm {G : ℂ → ℂ} {d c x : ℝ}
    (hdc : d < c) (hx : 0 < x) (P : Finset ℂ)
    (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hG : DifferentiableOn ℂ G (re ⁻¹' Icc d c \ P))
    (hm : ∀ p ∈ P, MeromorphicAt G p)
    (hd : VerticalIntegrable G d) (hc : VerticalIntegrable G c)
    (hdecay : Tendsto (fun y : ℝ => ⨆ σ : Icc d c, ‖G (σ + y * I)‖)
      (cocompact ℝ) (𝓝 0)) :
    mellinInv d G x = ∑ p ∈ P, TauCeti.Contour.residue
      (fun z => -((x : ℂ) ^ (-z) * G z)) p + mellinInv c G x := by
  have hpow (z : ℂ) : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ (-z)) z :=
    analyticAt_const.cpow analyticAt_id.neg (ofReal_mem_slitPlane.mpr hx)
  have hf : DifferentiableOn ℂ (fun z => (x : ℂ) ^ (-z) * G z)
      (re ⁻¹' Icc d c \ P) := fun z hz =>
    (hpow z).differentiableAt.differentiableWithinAt.mul (hG z hz)
  have hmf : ∀ p ∈ P, MeromorphicAt (fun z => (x : ℂ) ^ (-z) * G z) p :=
    fun p hp => (hpow p).meromorphicAt.mul (hm p hp)
  let X : ℝ := max (x ^ (-d)) (x ^ (-c))
  have hX (σ : ℝ) (hσ : σ ∈ Icc d c) : x ^ (-σ) ≤ X := by
    rcases le_total 1 x with h1 | h1
    · exact (Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hσ.1])).trans
        (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hx h1 (by linarith [hσ.2])).trans
        (le_max_right _ _)
  have hhor : Tendsto (fun T : ℝ => ∫ σ in d..c,
      (x : ℂ) ^ (-((σ : ℂ) + T * I)) * G (σ + T * I)) (cocompact ℝ) (𝓝 0) := by
    have hl : Tendsto (fun T : ℝ => X * (⨆ σ : Icc d c, ‖G (σ + T * I)‖) * |c - d|)
        (cocompact ℝ) (𝓝 0) := by simpa using (hdecay.const_mul X).mul_const |c - d|
    refine squeeze_zero_norm' ?_ hl
    have hev : ∀ᶠ T : ℝ in cocompact ℝ, ∀ p ∈ P, T ≠ p.im :=
      (Filter.eventually_all_finset P).mpr fun p _ =>
        (isCompact_singleton : IsCompact ({p.im} : Set ℝ)).compl_mem_cocompact
    filter_upwards [hev] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    rw [uIoc_of_le hdc.le] at hσ
    have hσ' : σ ∈ Icc d c := Ioc_subset_Icc_self hσ
    have hseg : ∀ τ ∈ Icc d c, ((τ : ℂ) + T * I) ∈ re ⁻¹' Icc d c \ (P : Set ℂ) := by
      intro τ hτ
      refine ⟨by simpa using hτ, fun hp => hT _ hp ?_⟩
      simp
    have hcont : ContinuousOn (fun τ : ℝ => ‖G (τ + T * I)‖) (Icc d c) :=
      (hG.continuousOn.comp (Continuous.continuousOn (by fun_prop)) hseg).norm
    have hbdd : BddAbove (Set.range fun τ : Icc d c => ‖G (τ + T * I)‖) := by
      have h := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
      rwa [Set.image_eq_range] at h
    have hle : ‖G (σ + T * I)‖ ≤ ⨆ τ : Icc d c, ‖G (τ + T * I)‖ :=
      le_ciSup (f := fun τ : Icc d c => ‖G (τ + T * I)‖) hbdd ⟨σ, hσ'⟩
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
    simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]
    exact mul_le_mul (hX σ hσ') hle (norm_nonneg _)
      ((Real.rpow_nonneg hx.le _).trans (hX σ hσ'))
  exact mellinInv_eq_sum_residue_add hdc hx P hP hf hmf hd hc
    (hhor.mono_left atTop_le_cocompact) (hhor.mono_left atBot_le_cocompact)

/-- The residue of a finite sum of simple principal parts is its coefficient at the
chosen pole, provided the pole locations are distinct. -/
theorem residue_sum_div_sub {ι : Type*} [DecidableEq ι] (S : Finset ι) (p c : ι → ℂ)
    (hp : Function.Injective p) {k : ι} (hk : k ∈ S) :
    TauCeti.Contour.residue (fun z => ∑ i ∈ S, c i / (z - p i)) (p k) = c k := by
  have hm (i : ι) : MeromorphicAt (fun z : ℂ => c i / (z - p i)) (p k) :=
    analyticAt_const.meromorphicAt.div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  have hs : TauCeti.Contour.residue (fun z => ∑ i ∈ S, c i / (z - p i)) (p k) =
      ∑ i ∈ S, TauCeti.Contour.residue (fun z => c i / (z - p i)) (p k) := by
    have he : (fun z => ∑ i ∈ S, c i / (z - p i)) =
        ∑ i ∈ S, (fun z => c i / (z - p i)) := by
      funext z
      simp only [Finset.sum_apply]
    rw [he]
    exact TauCeti.Contour.residue_sum S (fun i _ => hm i)
  rw [hs, Finset.sum_eq_single k]
  · simpa using TauCeti.Contour.residue_div_sub_pow_of_analyticAt
      (g := fun _ => c k) (z₀ := p k) analyticAt_const 0
  · intro i _ hik
    apply TauCeti.Contour.residue_eq_zero_of_analyticAt
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr fun he => hik (hp he.symm))
  · exact fun h => (h hk).elim

/-- Holomorphic subtraction of finitely many distinct simple principal parts determines
the residues, including zero coefficients and removable singularities. -/
theorem residue_eq_of_analyticAt_sub_sum_div {ι : Type*} [DecidableEq ι] {F : ℂ → ℂ}
    (S : Finset ι) (p c : ι → ℂ) (hp : Function.Injective p) {k : ι} (hk : k ∈ S)
    (ha : AnalyticAt ℂ (fun z => F z - ∑ i ∈ S, c i / (z - p i)) (p k)) :
    TauCeti.Contour.residue F (p k) = c k := by
  let A : ℂ → ℂ := fun z => F z - ∑ i ∈ S, c i / (z - p i)
  let B : ℂ → ℂ := fun z => ∑ i ∈ S, c i / (z - p i)
  have hmB : MeromorphicAt B (p k) := MeromorphicAt.fun_sum fun i _ =>
    analyticAt_const.meromorphicAt.div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  have he : F = A + B := by funext z; simp [A, B]
  rw [he, TauCeti.Contour.residue_add ha.meromorphicAt hmB,
    TauCeti.Contour.residue_eq_zero_of_analyticAt ha]
  exact (zero_add _).trans (residue_sum_div_sub S p c hp hk)

/-- The numerator value at a simple or removable pole is Tau Ceti's residue. -/
theorem residue_eq_of_eventuallyEq_div_sub {f φ : ℂ → ℂ} {p : ℂ}
    (hφ : AnalyticAt ℂ φ p) (he : f =ᶠ[𝓝[≠] p] fun z => φ z / (z - p)) :
    TauCeti.Contour.residue f p = φ p := by
  rw [TauCeti.Contour.residue_congr_nhdsNE he]
  simpa using TauCeti.Contour.residue_div_sub_pow_of_analyticAt hφ 0

/-- Under the hypotheses for a simple-pole contour iteration, every numerator value is
the corresponding Tau Ceti residue. -/
theorem MellinBarnesSeries.residue_eq {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ}
    {φ : ℕ → ℂ → ℂ} (h : MellinBarnesSeriesData F c p φ) (n : ℕ) :
    TauCeti.Contour.residue F (p n) = φ n (p n) := by
  have hs : re ⁻¹' Icc (c (n + 1)) (c n) ∈ 𝓝 (p n) :=
    continuous_re.continuousAt.preimage_mem_nhds (Icc_mem_nhds (h.lt_re n) (h.re_lt n))
  apply residue_eq_of_eventuallyEq_div_sub ((h.differentiableOn n).analyticAt hs)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hs, self_mem_nhdsWithin] with z hz hzp
  exact h.eq_div n z hz hzp

/-- The finite simple-pole contour iteration, written as a sum of Tau Ceti residues. -/
theorem MellinBarnesSeries.sub_eq_sum_residue {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ}
    {φ : ℕ → ℂ → ℂ} (h : MellinBarnesSeriesData F c p φ) (N : ℕ) :
    (∫ y : ℝ, F (c 0 + y * I)) - ∫ y : ℝ, F (c N + y * I) =
      2 * (Real.pi : ℂ) * ∑ n ∈ Finset.range N, TauCeti.Contour.residue F (p n) := by
  simp_rw [MellinBarnesSeries.residue_eq h]
  simpa [Finset.mul_sum] using MellinBarnesSeries.sub_eq_sum h N

/-- Closing the contour gives convergence of the partial sums of Tau Ceti residues. -/
theorem MellinBarnesSeries.tendsto_sum_residue {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ}
    {φ : ℕ → ℂ → ℂ} (h : MellinBarnesSeriesData F c p φ)
    (hlim : Tendsto (fun N : ℕ => ∫ y : ℝ, F (c N + y * I)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, TauCeti.Contour.residue F (p n)) atTop
      (𝓝 ((2 * (Real.pi : ℂ))⁻¹ * ∫ y : ℝ, F (c 0 + y * I))) := by
  have ht := (MellinBarnesSeries.tendsto h hlim).const_mul (2 * (Real.pi : ℂ))⁻¹
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  simpa [MellinBarnesSeries.residue_eq h, ← Finset.mul_sum, ← mul_assoc,
    inv_mul_cancel₀ hpi] using ht

/-- If the residue series is summable, closing the contour gives its sum. -/
theorem MellinBarnesSeries.hasSum_residue {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ}
    {φ : ℕ → ℂ → ℂ} (h : MellinBarnesSeriesData F c p φ)
    (hlim : Tendsto (fun N : ℕ => ∫ y : ℝ, F (c N + y * I)) atTop (𝓝 0))
    (hs : Summable fun n => TauCeti.Contour.residue F (p n)) :
    HasSum (fun n => TauCeti.Contour.residue F (p n))
      ((2 * (Real.pi : ℂ))⁻¹ * ∫ y : ℝ, F (c 0 + y * I)) := by
  have ht := MellinBarnesSeries.tendsto_sum_residue h hlim
  rw [← tendsto_nhds_unique hs.hasSum.tendsto_sum_nat ht]
  exact hs.hasSum

end Complex
