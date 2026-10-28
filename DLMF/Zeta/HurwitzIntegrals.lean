/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Hurwitz
public import DLMF.Zeta.IntegralReps
public import DLMF.Constants.Catalan

/-!
# The Hurwitz zeta function: integrals, sums and `a`-asymptotics (DLMF §25.11(vii)–(xii))

Statements use DLMF's `ζ(s, a)` in the form `DLMF.Confluent.hurwitzZetaComplex s a` for complex
`a` (see `DLMF.Zeta.Hurwitz`), and Mathlib's `hurwitzZeta` where DLMF's range is `0 < a ≤ 1`.

* Integrals `∫_0^a` with complex `a` are taken along the segment `[0, a]`, written
  `∫_0^1 a f(ta) dt`.
* Conditionally convergent series and improper integrals are stated as limits of partial sums or of
  `∫_0^X` (resp. `∫_{-a}^X`) as `X → ∞`.
* Asymptotic expansions (25.11.43–25.11.45) are stated for each truncation order `K`, with remainder
  `O` of the next power, as `a → ∞` in the sector `|ph a| ≤ π - δ`.
* 25.11.37 involves `ln Γ` of complex arguments. With principal logarithms it holds only modulo
  `2πi` (mpmath, e.g. `n = 2`, `a = 4 - 9i`); it is stated exactly with principal logarithms for
  real `a ≥ 1` (where every logarithm is of a positive real) and in exponentiated form for complex
  `Re a ≥ 1` (the identity with the analytic branch of `ln Γ` is equivalent to it plus a
  continuity statement).
* The removable singularities at `s = 1` in 25.11.31 and 25.11.35 (differences of two Hurwitz
  functions) are excluded by a hypothesis `s ≠ 1`, since Lean's value at the pole is junk.
-/

@[expose] public section

open Complex Filter Set MeasureTheory HurwitzZeta Asymptotics
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

open DLMF.Confluent (hurwitzZetaComplex)
open DLMF.Hypergeometric (poch)

/-! ### §25.11(vii) Integral representations -/

/-- **Laplace-type integral** (DLMF 25.11.25):
`ζ(s,a) = (1/Γ(s)) ∫_0^∞ x^{s-1} e^{-ax}/(1 - e^{-x}) dx` for `Re s > 1`, complex `Re a > 0`.
(Real `0 < a ≤ 1` with Mathlib's function:
`DLMF.Gamma.Gamma_mul_hurwitzZeta_eq_integral`.) -/
@[dlmf 25.11.E25]
theorem hurwitzZetaComplex_eq_integral {s a : ℂ} (hs : 1 < s.re) (ha : 0 < a.re) :
    hurwitzZetaComplex s a = 1 / Gamma s *
      ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * cexp (-(a * x)) / (1 - cexp (-(x : ℂ))) := by
  have ha' : ∀ m : ℕ, a ≠ -m := fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have h := q25b_hasSum_lerchInt (z := 1) (by linarith) ha (Or.inr ⟨by simp, hs⟩)
  simp only [one_pow, q25b_lerchInt, one_mul] at h
  refine (hasSum_hurwitzZetaComplex hs ha').unique ?_
  rw [one_div]
  exact h.congr_fun fun n => by rw [add_comm]

/-- **Sawtooth integral** (DLMF 25.11.26): `ζ(s,a) = -s ∫_{-a}^∞ (x - ⌊x⌋ - 1/2)/(x+a)^{s+1} dx`
for `-1 < Re s < 0`, `0 < a ≤ 1`; the integral converges conditionally at `∞` and is stated as the
limit of `∫_{-a}^X`. -/
@[dlmf 25.11.E26]
theorem tendsto_hurwitzZeta_sawtooth_integral {s : ℂ} (hs1 : -1 < s.re) (hs0 : s.re < 0) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun X : ℝ => -s * ∫ x in (-a)..X,
        ((Int.fract x - 1 / 2 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 1)) atTop
      (𝓝 (hurwitzZeta (a : UnitAddCircle) s)) := by
  sorry

/-- `{Re s > c} \ {1}` is preconnected for `c < 1`. -/
lemma s25b_isPreconnected_re_gt_diff_one {c : ℝ} (hc : c < 1) :
    IsPreconnected ({s : ℂ | c < s.re} \ {1}) := by
  set Q1 : Set ℂ := {s | c < s.re ∧ 0 < s.im}
  set Q2 : Set ℂ := {s | c < s.re ∧ s.im < 0}
  set Q3 : Set ℂ := {s | c < s.re ∧ s.re < 1}
  set Q4 : Set ℂ := {s | 1 < s.re}
  have c1 : Convex ℝ Q1 := (convex_halfSpace_re_gt c).inter (convex_halfSpace_im_gt 0)
  have c2 : Convex ℝ Q2 := (convex_halfSpace_re_gt c).inter (convex_halfSpace_im_lt 0)
  have c3 : Convex ℝ Q3 := (convex_halfSpace_re_gt c).inter (convex_halfSpace_re_lt 1)
  have c4 : Convex ℝ Q4 := convex_halfSpace_re_gt 1
  set m : ℝ := (c + 1) / 2
  have hm1 : c < m := by simp only [m]; linarith
  have hm2 : m < 1 := by simp only [m]; linarith
  have h13 := c1.isPreconnected.union ((m : ℂ) + I) (by simp [Q1, hm1])
    (by simp [Q3, hm1, hm2]) c3.isPreconnected
  have h132 := h13.union ((m : ℂ) - I) (by simp [Q3, hm1, hm2]) (by simp [Q2, hm1])
    c2.isPreconnected
  have h := h132.union (2 + I)
    (show (2 + I) ∈ Q1 ∪ Q3 ∪ Q2 from Or.inl (Or.inl ⟨by simp; linarith, by simp⟩))
    (by norm_num [Q4])
    c4.isPreconnected
  convert h using 1
  ext s
  simp only [Set.mem_sdiff, mem_ofPred_eq, Set.mem_singleton_iff, mem_union, Q1, Q2, Q3, Q4]
  constructor
  · rintro ⟨h0, h1⟩
    rcases lt_trichotomy s.im 0 with hi | hi | hi
    · exact Or.inl (Or.inr ⟨h0, hi⟩)
    · rcases lt_trichotomy s.re 1 with hr | hr | hr
      · exact Or.inl (Or.inl (Or.inr ⟨h0, hr⟩))
      · exact absurd (Complex.ext (by simpa using hr) (by simpa using hi)) h1
      · exact Or.inr hr
    · exact Or.inl (Or.inl (Or.inl ⟨h0, hi⟩))
  · rintro (((⟨h0, h1⟩ | ⟨h0, h1⟩) | ⟨h0, h1⟩) | h0)
    · exact ⟨h0, fun h => by subst h; simp at h1⟩
    · exact ⟨h0, fun h => by subst h; simp at h1⟩
    · exact ⟨h0, fun h => by subst h; simp at h1⟩
    · exact ⟨by linarith, fun h => by subst h; simp at h0⟩

/-- Domination of the 25.11.27 integrand: for `x > 0` and `σ₁ ≤ Re s ≤ σ₂`,
`|β(x) x^{s-1} e^{-ax}| ≤ (x^{σ₁} + x^{σ₂-1}) e^{-Re a x}`. -/
lemma s25b_norm_binet_integrand_le {s a : ℂ} {x σ₁ σ₂ : ℝ} (hx : 0 < x) (h1 : σ₁ ≤ s.re)
    (h2 : s.re ≤ σ₂) :
    ‖((DLMF.Gamma.binetBeta x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) * cexp (-(a * x))‖ ≤
      (x ^ σ₁ + x ^ (σ₂ - 1)) * Real.exp (-(a.re * x)) := by
  rw [mul_assoc, norm_mul, q25b_norm_cpow_mul_cexp hx, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (DLMF.Gamma.binetBeta_nonneg hx), ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have hb0 := DLMF.Gamma.binetBeta_nonneg hx
  have hp1 := Real.rpow_nonneg hx.le σ₁
  have hp2 := Real.rpow_nonneg hx.le (σ₂ - 1)
  have hp := Real.rpow_nonneg hx.le (s.re - 1)
  rcases le_or_gt x 1 with hx1 | hx1
  · have hb := DLMF.Gamma.binetBeta_le hx
    have e : x * x ^ (s.re - 1) = x ^ s.re := by
      conv_rhs => rw [show s.re = 1 + (s.re - 1) by ring]
      rw [Real.rpow_add hx, Real.rpow_one]
    have hle : x ^ s.re ≤ x ^ σ₁ := Real.rpow_le_rpow_of_exponent_ge hx hx1 h1
    nlinarith
  · have hb := DLMF.Gamma.binetBeta_le_half hx
    have hle : x ^ (s.re - 1) ≤ x ^ (σ₂ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    nlinarith

/-- The 25.11.27 integrand. -/
noncomputable def s25b_binetIntegrand (a s : ℂ) (x : ℝ) : ℂ :=
  ((DLMF.Gamma.binetBeta x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) * cexp (-(a * x))

/-- The stated relation follows from the given hypotheses: `AEStronglyMeasurable
(s25b_binetIntegrand a s) (volume.restrict (Ioi 0))`. -/
lemma s25b_aestronglyMeasurable_binetIntegrand (a s : ℂ) :
    AEStronglyMeasurable (s25b_binetIntegrand a s) (volume.restrict (Ioi 0)) := by
  have hb : AEStronglyMeasurable (fun x : ℝ => ((DLMF.Gamma.binetBeta x : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) :=
    (continuous_ofReal.comp_continuousOn DLMF.Gamma.continuousOn_binetBeta).aestronglyMeasurable
      measurableSet_Ioi
  have := hb.mul (q25b_aestronglyMeasurable_cpow_mul_cexp s a)
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [s25b_binetIntegrand, Pi.mul_apply, mul_assoc]

/-- Integrability of the 25.11.27 integrand for `Re s > -1`, `Re a > 0`. -/
lemma s25b_integrableOn_binetIntegrand {a s : ℂ} (ha : 0 < a.re) (hs : -1 < s.re) :
    IntegrableOn (s25b_binetIntegrand a s) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => (x ^ s.re + x ^ ((s.re + 1) - 1)) *
      Real.exp (-(a.re * x))) (Ioi 0) := by
    have h1 := q25b_integrableOn_rpow_mul_exp (σ := s.re + 1) (by linarith) ha
    have h2 := q25b_integrableOn_rpow_mul_exp (σ := s.re + 1) (by linarith) ha
    simp only [add_sub_cancel_right] at h1 h2 ⊢
    exact (h1.add h2).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  refine hg.mono' (s25b_aestronglyMeasurable_binetIntegrand a s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact s25b_norm_binet_integrand_le hx le_rfl (by linarith)

/-- Holomorphy in `s` of the 25.11.27 integral on `Re s > -1`. -/
lemma s25b_differentiableOn_binetIntegral {a : ℂ} (ha : 0 < a.re) :
    DifferentiableOn ℂ (fun s => ∫ x in Ioi (0 : ℝ), s25b_binetIntegrand a s x)
      {s : ℂ | -1 < s.re} := by
  have hU : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const continuous_re
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated hU 0
    (fun s _ => s25b_aestronglyMeasurable_binetIntegrand a s) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s _
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold s25b_binetIntegrand
    exact ((differentiableAt_const _).mul ((differentiableAt_id.sub_const 1).const_cpow
      (Or.inl hx0))).mul (differentiableAt_const _)
  · intro s₀ hs₀
    have hs₀' : -1 < s₀.re := hs₀
    set δ := (s₀.re + 1) / 2
    have hδ : 0 < δ := by simp only [δ]; linarith
    refine ⟨Metric.ball s₀ δ, Metric.ball_mem_nhds _ hδ, fun x =>
      (x ^ (s₀.re - δ) + x ^ ((s₀.re + δ + 1) - 1)) * Real.exp (-(a.re * x)), ?_, ?_⟩
    · have h1 := q25b_integrableOn_rpow_mul_exp (σ := s₀.re - δ + 1)
        (by simp only [δ]; linarith) ha
      have h2 := q25b_integrableOn_rpow_mul_exp (σ := s₀.re + δ + 1)
        (by simp only [δ]; linarith) ha
      simp only [add_sub_cancel_right] at h1
      exact (h1.add h2).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have := abs_re_le_norm (s - s₀)
      simp only [sub_re] at this
      exact s25b_norm_binet_integrand_le hx (by linarith [neg_abs_le (s.re - s₀.re)])
        (by linarith [le_abs_self (s.re - s₀.re)])

/-- 25.11.27 for `Re s > 1`, from 25.11.25 and two Gamma integrals. -/
lemma s25b_binetIntegral_of_one_lt_re {a s : ℂ} (ha : 0 < a.re) (hs : 1 < s.re) :
    ∫ x in Ioi (0 : ℝ), s25b_binetIntegrand a s x =
      Gamma s * (hurwitzZetaComplex s a - a ^ (-s) / 2 - a ^ (1 - s) / (s - 1)) := by
  have ha' : ∀ m : ℕ, a ≠ -m := fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  set P : ℝ → ℂ := fun x => (x : ℂ) ^ ((s - 1) - 1) * cexp (-(a * x))
  set Q : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * cexp (-(a * x))
  have hP : IntegrableOn P (Ioi 0) := q25b_integrableOn_cpow_mul_cexp (by simp; linarith) ha
  have hQ : IntegrableOn Q (Ioi 0) := q25b_integrableOn_cpow_mul_cexp (by linarith) ha
  have hB := s25b_integrableOn_binetIntegrand ha (s := s) (by linarith)
  have heq : EqOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * cexp (-((a + 1) * x)) /
      (1 - cexp (-(x : ℂ)))) (fun x => s25b_binetIntegrand a s x + P x - Q x / 2) (Ioi 0) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0 : ℝ) < x from hx))
    have hex : (Real.exp x : ℂ) - 1 ≠ 0 := by
      have := DLMF.Gamma.exp_sub_one_pos (show (0 : ℝ) < x from hx)
      exact_mod_cast this.ne'
    have h1 : 1 - cexp (-(x : ℂ)) ≠ 0 := by
      rw [Complex.exp_neg, ← Complex.ofReal_exp]
      intro h; apply hex
      have he : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
      field_simp at h; linear_combination h
    simp only [s25b_binetIntegrand, DLMF.Gamma.binetBeta, P, Q]
    rw [cpow_sub (x := (x : ℂ)) (s - 1) 1 hx0, cpow_one]
    push_cast
    rw [show -((a + 1) * (x : ℂ)) = -(a * x) + -(x : ℂ) by ring, Complex.exp_add,
      Complex.exp_neg (x : ℂ), ← Complex.ofReal_exp]
    have he : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
    field_simp
    ring
  have h25 := hurwitzZetaComplex_eq_integral hs (a := a + 1) (by simp; linarith)
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_sub (f := fun x => s25b_binetIntegrand a s x + P x) (g := fun x => Q x / 2)
      (hB.add hP) (hQ.div_const 2), integral_add hB hP, integral_div] at h25
  have hPi : ∫ x in Ioi (0 : ℝ), P x = Gamma (s - 1) * a ^ (-(s - 1)) :=
    DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (by simp; linarith) ha
  have hQi : ∫ x in Ioi (0 : ℝ), Q x = Gamma s * a ^ (-s) :=
    DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (by linarith) ha
  rw [hPi, hQi] at h25
  have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hG1 : Gamma s = (s - 1) * Gamma (s - 1) := by
    rw [← Complex.Gamma_add_one _ hs1']; ring_nf
  rw [hurwitzZetaComplex_eq_add_one hs1 ha', h25, hG1]
  rw [hG1] at hG
  have hG' : Gamma (s - 1) ≠ 0 := right_ne_zero_of_mul hG
  rw [show -(s - 1) = 1 - s by ring]
  field_simp
  ring

/-- **Integral with the Bernoulli generating function** (DLMF 25.11.27): for `Re s > -1`, `s ≠ 1`,
`Re a > 0`, `ζ(s,a) = a^{-s}/2 + a^{1-s}/(s-1) + (1/Γ(s)) ∫_0^∞ (1/(e^x-1) - 1/x + 1/2) x^{s-1}
e^{-ax} dx`. -/
@[dlmf 25.11.E27]
theorem hurwitzZetaComplex_eq_integral_bernoulli {s a : ℂ} (hs : s ≠ 1) (hs0 : -1 < s.re)
    (ha : 0 < a.re) :
    hurwitzZetaComplex s a = a ^ (-s) / 2 + a ^ (1 - s) / (s - 1) + 1 / Gamma s *
      ∫ x in Ioi (0 : ℝ), ((1 / (Real.exp x - 1) - 1 / x + 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) *
        cexp (-(a * x)) := by
  change _ = _ + _ + 1 / Gamma s * ∫ x in Ioi (0 : ℝ), s25b_binetIntegrand a s x
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have han : ∀ n : ℕ, a + n ≠ 0 := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set W : Set ℂ := {t : ℂ | -1 < t.re} \ {1}
  have hW : IsOpen W := (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  set G : ℂ → ℂ := fun t => a ^ (-t) / 2 + a ^ (1 - t) / (t - 1) +
    1 / Gamma t * ∫ x in Ioi (0 : ℝ), s25b_binetIntegrand a t x
  have hF : DifferentiableOn ℂ (fun t => hurwitzZetaComplex t a) W := fun t ht =>
    (r25b_differentiableAt_hurwitzZetaComplex ht.2 han).differentiableWithinAt
  have hG : DifferentiableOn ℂ G W := by
    intro t ht
    have ht1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht.2
    have hI := (s25b_differentiableOn_binetIntegral ha t ht.1).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds ht.1)
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.add (DifferentiableAt.add ?_ ?_) ?_
    · exact ((differentiableAt_id.neg).const_cpow (Or.inl ha0)).div_const _
    · exact (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl ha0)).div
        (differentiableAt_id.sub_const 1) ht1
    · have h1 : DifferentiableAt ℂ (fun t : ℂ => 1 / Gamma t) t := by
        simpa only [one_div] using Complex.differentiable_one_div_Gamma t
      exact h1.mul hI
  have heq : EqOn (fun t => hurwitzZetaComplex t a) G W := by
    refine (hF.analyticOnNhd hW).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hW)
      (s25b_isPreconnected_re_gt_diff_one (by norm_num)) (show (2 : ℂ) ∈ W by norm_num [W]) ?_
    have hopen : IsOpen {t : ℂ | 1 < t.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with t ht
    have hΓ : Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    simp only [G, s25b_binetIntegral_of_one_lt_re ha ht]
    field_simp
    ring
  exact heq ⟨hs0, hs⟩

/-- **Integral with `n` Bernoulli terms removed** (DLMF 25.11.28): for `Re s > -(2n+1)`, `s ≠ 1`,
`Re a > 0`. -/
@[dlmf 25.11.E28]
theorem hurwitzZetaComplex_eq_integral_bernoulli_sub (n : ℕ) {s a : ℂ} (hs : s ≠ 1)
    (hs0 : -(2 * n + 1 : ℝ) < s.re) (ha : 0 < a.re) :
    hurwitzZetaComplex s a = a ^ (-s) / 2 + a ^ (1 - s) / (s - 1) +
      (∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℂ) / (2 * k)! * poch s (2 * k - 1) *
        a ^ (1 - s - 2 * k)) +
      1 / Gamma s * ∫ x in Ioi (0 : ℝ),
        ((1 / (Real.exp x - 1) - 1 / x + 1 / 2 -
          ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℝ) / (2 * k)! * x ^ (2 * k - 1) : ℝ) : ℂ) *
          (x : ℂ) ^ (s - 1) * cexp (-(a * x)) := by
  sorry

/-- **Hermite's formula** (DLMF 25.11.29): for `s ≠ 1` and `Re a > 0`,
`ζ(s,a) = a^{-s}/2 + a^{1-s}/(s-1) + 2 ∫_0^∞ sin(s arctan(x/a))/((a²+x²)^{s/2}(e^{2πx}-1)) dx`,
principal branches of `arctan` and of the power (for `Re a > 0`, `x > 0` the argument `x/a` avoids
the cuts of `arctan` and `a² + x²` avoids `(-∞, 0]`). -/
@[dlmf 25.11.E29]
theorem hurwitzZetaComplex_hermite {s a : ℂ} (hs : s ≠ 1) (ha : 0 < a.re) :
    hurwitzZetaComplex s a = a ^ (-s) / 2 + a ^ (1 - s) / (s - 1) +
      2 * ∫ x in Ioi (0 : ℝ), Complex.sin (s * Complex.arctan (x / a)) /
        ((a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) * (Real.exp (2 * π * x) - 1 : ℝ)) := by
  sorry

/-- **Loop integral** (DLMF 25.11.30): for `s ≠ 1, 2, 3, …` and `Re a > 0`,
`ζ(s, a) = (Γ(1-s)/(2πi)) ∫_{-∞}^{(0+)} e^{az} z^{s-1}/(1 - e^z) dz`, the loop encircling the origin
once positively without enclosing `±2πi, ±4πi, …`. As for 25.5.20 (`riemannZeta_eq_loop_integral`)
the loop is the keyhole `DLMF.Zeta.keyholeLoopIntegral` of radius `0 < δ < 2π` (the independence of
the loop is not formalized). -/
@[dlmf 25.11.E30]
theorem hurwitzZetaComplex_eq_loop_integral {s a : ℂ} (hs : ∀ n : ℕ, s ≠ n + 1) (ha : 0 < a.re)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π) :
    hurwitzZetaComplex s a = Gamma (1 - s) / (2 * π * I) *
      keyholeLoopIntegral (fun z => cexp (a * z) / (1 - cexp z)) (s - 1) δ := by
  sorry

/-! ### §25.11(viii) Further integral representations -/

/-- Holomorphy in `s` of `∫_0^∞ x^{s-1} e^{-ax}/(1 + e^{-x}) dx` on `Re s > 0`. -/
lemma s25b_differentiableOn_altIntegral {a : ℂ} (ha : 0 < a.re) :
    DifferentiableOn ℂ (fun s => q25b_lerchInt s a (-1)) {s : ℂ | 0 < s.re} := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hden : ∀ x : ℝ, ‖1 - (-1) * cexp (-(x : ℂ))‖ ≥ 1 := by
    intro x
    have e : 1 - (-1) * cexp (-(x : ℂ)) = ((1 + Real.exp (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_add, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_one]; ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith [Real.exp_pos (-x)]
  have hden0 : ∀ x : ℝ, 1 - (-1) * cexp (-(x : ℂ)) ≠ 0 := fun x h => by
    have := hden x; rw [h, norm_zero] at this; linarith
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated hU 0 (fun s _ => ?_) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    refine ContinuousAt.continuousWithinAt ?_
    exact ContinuousAt.div (ContinuousAt.mul (continuousAt_ofReal_cpow_const _ _
      (Or.inr (ne_of_gt hx))) (by fun_prop)) (by fun_prop) (hden0 x)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s _
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (((differentiableAt_id.sub_const 1).const_cpow (Or.inl hx0)).mul
      (differentiableAt_const _)).div_const _
  · intro s₀ hs₀
    have hs₀' : 0 < s₀.re := hs₀
    set δ := s₀.re / 2
    have hδ : 0 < δ := by simp only [δ]; linarith
    refine ⟨Metric.ball s₀ δ, Metric.ball_mem_nhds _ hδ, fun x =>
      (x ^ ((s₀.re - δ) - 1) + x ^ ((s₀.re + δ) - 1)) * Real.exp (-(a.re * x)), ?_, ?_⟩
    · have h1 := q25b_integrableOn_rpow_mul_exp (σ := s₀.re - δ) (by simp only [δ]; linarith) ha
      have h2 := q25b_integrableOn_rpow_mul_exp (σ := s₀.re + δ) (by simp only [δ]; linarith) ha
      exact (h1.add h2).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring)
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have := abs_re_le_norm (s - s₀)
      simp only [sub_re] at this
      have h1 : s₀.re - δ ≤ s.re := by linarith [neg_abs_le (s.re - s₀.re)]
      have h2 : s.re ≤ s₀.re + δ := by linarith [le_abs_self (s.re - s₀.re)]
      rw [norm_div, q25b_norm_cpow_mul_cexp hx]
      have hd := hden x
      have hp : 0 ≤ x ^ (s.re - 1) * Real.exp (-(a.re * x)) :=
        mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le
      calc x ^ (s.re - 1) * Real.exp (-(a.re * x)) / ‖1 - (-1) * cexp (-(x : ℂ))‖
          ≤ x ^ (s.re - 1) * Real.exp (-(a.re * x)) := div_le_self hp hd
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have := s25b_rpow_le_add (x := x) (σ := -s.re) (σ₀ := -(s₀.re + δ))
            (R := -(s₀.re - δ)) hx (by linarith) (by linarith)
          simp only [neg_neg] at this
          linarith

/-- The alternating Hurwitz integral (DLMF 25.11.35, integral form) for `Re a > 0`,
`Re s > 0`, `s ≠ 1`:
`(1/Γ(s)) ∫_0^∞ x^{s-1} e^{-ax}/(1+e^{-x}) dx = 2^{-s}(ζ(s,a/2) - ζ(s,(1+a)/2))`. -/
lemma s25b_altIntegral_eq {s a : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (ha : 0 < a.re) :
    1 / Gamma s * q25b_lerchInt s a (-1) =
      2 ^ (-s) * (hurwitzZetaComplex s (a / 2) - hurwitzZetaComplex s ((1 + a) / 2)) := by
  have ha2 : 0 < (a / 2).re := by simp; linarith
  have ha3 : 0 < ((1 + a) / 2).re := by simp; linarith
  set W : Set ℂ := {t : ℂ | 0 < t.re} \ {1}
  have hW : IsOpen W := (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  have hF : DifferentiableOn ℂ (fun t => 1 / Gamma t * q25b_lerchInt t a (-1)) W := by
    intro t ht
    have hI := ((s25b_differentiableOn_altIntegral ha) t ht.1).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds ht.1)
    have h1 : DifferentiableAt ℂ (fun t : ℂ => 1 / Gamma t) t := by
      simpa only [one_div] using Complex.differentiable_one_div_Gamma t
    exact (h1.mul hI).differentiableWithinAt
  have hG : DifferentiableOn ℂ (fun t => (2 : ℂ) ^ (-t) * (hurwitzZetaComplex t (a / 2) -
      hurwitzZetaComplex t ((1 + a) / 2))) W := by
    intro t ht
    exact (((differentiableAt_id.neg).const_cpow (Or.inl two_ne_zero)).mul
      ((r25b_differentiableAt_hurwitzZetaComplex ht.2 (r25b_ne_neg_nat_of_re_pos ha2)).sub
        (r25b_differentiableAt_hurwitzZetaComplex ht.2
          (r25b_ne_neg_nat_of_re_pos ha3)))).differentiableWithinAt
  refine (hF.analyticOnNhd hW).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hW)
    (s25b_isPreconnected_re_gt_diff_one (by norm_num)) (show (2 : ℂ) ∈ W by norm_num [W]) ?_
    ⟨hs0, hs1⟩
  have hopen : IsOpen {t : ℂ | 1 < t.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with t ht
  have hL := q25b_hasSum_lerchInt (z := -1) (by linarith) ha (Or.inr ⟨by simp, ht⟩)
  have hne : ∀ b : ℂ, 0 < b.re → ∀ m : ℕ, b ≠ -m := fun b hb m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have he := (hasSum_hurwitzZetaComplex ht (hne _ ha2)).mul_left ((2 : ℂ) ^ (-t))
  have ho := ((hasSum_hurwitzZetaComplex ht (hne _ ha3)).mul_left ((2 : ℂ) ^ (-t))).neg
  have hsplit : ∀ (m : ℕ) (b : ℂ), 0 < b.re →
      (2 : ℂ) ^ (-t) * (1 / ((m : ℂ) + b) ^ t) = 1 / (2 * (m : ℂ) + 2 * b) ^ t := by
    intro m b hb
    have hw : (m : ℂ) + b ≠ 0 := by rw [add_comm]; exact r25b_ne_neg_nat_of_re_pos hb m
    rw [show 2 * (m : ℂ) + 2 * b = ((2 : ℝ) : ℂ) * ((m : ℂ) + b) by push_cast; ring,
      r25b_ofReal_mul_cpow two_pos hw, cpow_neg]
    push_cast
    have h2 : (2 : ℂ) ^ t ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; simp
    have h3 : ((m : ℂ) + b) ^ t ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; simp [hw]
    field_simp
  have hs := HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ n / (a + n) ^ t)
    (he.congr_fun fun k => ?_) (ho.congr_fun fun k => ?_)
  · rw [← sub_eq_add_neg, ← mul_sub] at hs
    rw [one_div]; exact (hs.unique hL).symm
  · rw [hsplit k _ ha2, show (-1 : ℂ) ^ (2 * k) = 1 by rw [pow_mul]; norm_num]
    push_cast; ring_nf
  · rw [hsplit k _ ha3, show (-1 : ℂ) ^ (2 * k + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
    push_cast; ring_nf

/-- **`cosh` integral** (DLMF 25.11.31): for `Re s > 0`, `Re a > -1` (and `s ≠ 1`, where the
difference on the right has a removable singularity),
`(1/Γ(s)) ∫_0^∞ x^{s-1} e^{-ax}/(2 cosh x) dx = 4^{-s}(ζ(s, 1/4 + a/4) - ζ(s, 3/4 + a/4))`. -/
@[dlmf 25.11.E31]
theorem integral_cosh_eq_hurwitzZetaComplex_sub {s a : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1)
    (ha : -1 < a.re) :
    1 / Gamma s * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * cexp (-(a * x)) / (2 * Real.cosh x) =
      4 ^ (-s) * (hurwitzZetaComplex s (1 / 4 + a / 4) - hurwitzZetaComplex s (3 / 4 + a / 4)) := by
  set a' := (a + 1) / 2
  have ha' : 0 < a'.re := by simp [a']; linarith
  have hsub : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * cexp (-(a * x)) / (2 * Real.cosh x) =
      2 ^ (-s) * q25b_lerchInt s a' (-1) := by
    have hc := integral_comp_mul_left_Ioi (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-(a' * u)) /
      (1 - (-1) * cexp (-(u : ℂ)))) 0 (b := 2) two_pos
    rw [mul_zero] at hc
    rw [q25b_lerchInt, ← smul_eq_mul (a := (2 : ℂ) ^ (-s)), show (2 : ℂ) ^ (-s) =
      ((2 : ℝ) : ℂ) ^ (1 - s) * (((2 : ℝ)⁻¹ : ℝ) : ℂ) by
        rw [show (1 - s) = 1 + (-s) by ring, cpow_add _ _ (by norm_num), cpow_one]
        push_cast; field_simp, mul_smul, Complex.coe_smul, ← hc, ← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    simp only [smul_eq_mul]
    rw [show ((2 * x : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * (x : ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg (by norm_num) hx0.le, Real.cosh_eq]
    have hcx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
    have hd : ((2 * ((Real.exp x + Real.exp (-x)) / 2) : ℝ) : ℂ) ≠ 0 := by
      have : 0 < 2 * ((Real.exp x + Real.exp (-x)) / 2) := by positivity
      exact_mod_cast this.ne'
    have hd2 : 1 - (-1) * cexp (-((((2 : ℝ) : ℂ) * (x : ℂ)))) ≠ 0 := by
      rw [show 1 - (-1) * cexp (-((((2 : ℝ) : ℂ) * (x : ℂ)))) =
        ((1 + Real.exp (-(2 * x)) : ℝ) : ℂ) by push_cast; ring_nf]
      have : 0 < 1 + Real.exp (-(2 * x)) := by positivity
      exact_mod_cast this.ne'
    have h2s : ((2 : ℝ) : ℂ) ^ (s - 1) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; simp
    have h22 : ((2 : ℝ) : ℂ) ^ (1 - s) * ((2 : ℝ) : ℂ) ^ (s - 1) = 1 := by
      rw [← cpow_add _ _ (by norm_num)]; simp
    rw [← mul_div_assoc, ← mul_assoc, ← mul_assoc, h22, one_mul]
    rw [show -(a' * (((2 : ℝ) : ℂ) * (x : ℂ))) = -(a * x) + -(x : ℂ) by simp [a']; ring,
      Complex.exp_add, show -(((2 : ℝ) : ℂ) * (x : ℂ)) = -(x : ℂ) + -(x : ℂ) by push_cast; ring,
      Complex.exp_add]
    push_cast
    simp only [Complex.exp_neg]
    have hE : cexp (x : ℂ) ≠ 0 := Complex.exp_ne_zero _
    have hE2 : cexp (x : ℂ) * cexp (x : ℂ) + 1 ≠ 0 := by
      rw [← Complex.exp_add, ← Complex.ofReal_add, ← Complex.ofReal_exp]
      have : 0 < Real.exp (x + x) + 1 := by positivity
      exact_mod_cast this.ne'
    have hE3 : cexp (x : ℂ) ^ 2 + 1 ≠ 0 := by rw [sq]; exact hE2
    have hE4 : 1 + cexp (x : ℂ) ^ 2 ≠ 0 := by rw [add_comm]; exact hE3
    field_simp
    ring_nf
    field_simp
    ring
  rw [hsub, mul_left_comm, s25b_altIntegral_eq hs0 hs1 ha', ← mul_assoc]
  congr 1
  · rw [show (4 : ℂ) = ((2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) by norm_num,
      mul_cpow_ofReal_nonneg (by norm_num) (by norm_num)]
    push_cast; ring
  · simp only [a']; ring_nf

/-- **Moments of the digamma function** (DLMF 25.11.32): for `n ≥ 1` and `Re a > 0`, with the
harmonic numbers `H_k` (25.11.33) and `ζ'` the `s`-derivative,
`∫_0^a xⁿ ψ(x) dx = (-1)^{n-1} ζ'(-n) + (-1)ⁿ Hₙ B_{n+1}/(n+1)
 - ∑_{k=0}^{n} (-1)^k C(n,k) H_k (B_{k+1}(a)/(k+1)) a^{n-k}
 + ∑_{k=0}^{n} (-1)^k C(n,k) ζ'(-k, a) a^{n-k}`, the integral along `[0, a]`. -/
@[dlmf 25.11.E32]
theorem integral_pow_mul_digamma {n : ℕ} (hn : 1 ≤ n) {a : ℂ} (ha : 0 < a.re) :
    ∫ t in (0 : ℝ)..1, a * (t * a) ^ n * digamma (t * a) =
      (-1) ^ (n - 1) * deriv riemannZeta (-n) +
        (-1) ^ n * (harmonic n : ℂ) * bernoulli (n + 1) / (n + 1) -
        ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (n.choose k : ℂ) * (harmonic k : ℂ) *
          (((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval a / (k + 1)) * a ^ (n - k) +
        ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (n.choose k : ℂ) *
          deriv (fun s => hurwitzZetaComplex s a) (-k) * a ^ (n - k) := by
  sorry

/-- **Integral of `ζ'(1-n, x)`** (DLMF 25.11.34): for `n ≥ 1`, `Re a > 0`, along `[0, a]`,
`n ∫_0^a ζ'(1-n, x) dx = ζ'(-n, a) - ζ'(-n) + (B_{n+1} - B_{n+1}(a))/(n(n+1))`. -/
@[dlmf 25.11.E34]
theorem integral_deriv_hurwitzZetaComplex {n : ℕ} (hn : 1 ≤ n) {a : ℂ} (ha : 0 < a.re) :
    n * ∫ t in (0 : ℝ)..1, a * deriv (fun s => hurwitzZetaComplex s (t * a)) (1 - n) =
      deriv (fun s => hurwitzZetaComplex s a) (-n) - deriv riemannZeta (-n) +
        ((bernoulli (n + 1) : ℂ) - ((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval a) /
          (n * (n + 1)) := by
  sorry

/-! ### §25.11(x) Further series representations -/

/-- **Alternating Hurwitz series** (DLMF 25.11.35), series form: for `Re a > 0`, `Re s > 0`, or
`Re a = 0`, `Im a ≠ 0`, `0 < Re s < 1` (and `s ≠ 1`, a removable singularity of the right side),
`∑_{n≥0} (-1)^n/(n+a)^s = 2^{-s}(ζ(s, a/2) - ζ(s, (1+a)/2))`, as a limit of partial sums. -/
@[dlmf 25.11.E35]
theorem tendsto_alternating_hurwitz {s a : ℂ} (hs1 : s ≠ 1)
    (h : (0 < a.re ∧ 0 < s.re) ∨ (a.re = 0 ∧ a.im ≠ 0 ∧ 0 < s.re ∧ s.re < 1)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n / ((n : ℂ) + a) ^ s) atTop
      (𝓝 (2 ^ (-s) * (hurwitzZetaComplex s (a / 2) - hurwitzZetaComplex s ((1 + a) / 2)))) := by
  sorry

/-- **Alternating Hurwitz series** (DLMF 25.11.35), integral form: under the same conditions,
`(1/Γ(s)) ∫_0^∞ x^{s-1} e^{-ax}/(1 + e^{-x}) dx = 2^{-s}(ζ(s, a/2) - ζ(s, (1+a)/2))`; for
`Re a = 0` the integral converges conditionally and is the limit of `∫_0^X`. -/
@[dlmf 25.11.E35]
theorem tendsto_integral_alternating_hurwitz {s a : ℂ} (hs1 : s ≠ 1)
    (h : (0 < a.re ∧ 0 < s.re) ∨ (a.re = 0 ∧ a.im ≠ 0 ∧ 0 < s.re ∧ s.re < 1)) :
    Tendsto (fun X : ℝ => 1 / Gamma s *
        ∫ x in (0 : ℝ)..X, (x : ℂ) ^ (s - 1) * cexp (-(a * x)) / (1 + cexp (-(x : ℂ)))) atTop
      (𝓝 (2 ^ (-s) * (hurwitzZetaComplex s (a / 2) - hurwitzZetaComplex s ((1 + a) / 2)))) := by
  sorry

/-! ### §25.11(xi) Sums -/

/-- **Logarithmic sum** (DLMF 25.11.37) for real `a ≥ 1`, `n = 2, 3, …`, principal logarithms:
`∑_{k≥1} ((-1)^k/k) ζ(nk, a) = -n ln Γ(a) + ln ∏_{j=0}^{n-1} Γ(a - e^{(2j+1)πi/n})`. -/
@[dlmf 25.11.E37]
theorem hasSum_hurwitzZeta_log_gamma {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 1 ≤ a) :
    HasSum (fun k : ℕ => (-1) ^ (k + 1) / (k + 1 : ℂ) * hurwitzZetaComplex (n * (k + 1)) a)
      (-n * Real.log (Real.Gamma a) +
        Complex.log (∏ j ∈ Finset.range n, Gamma (a - cexp ((2 * j + 1) * π * I / n)))) := by
  sorry

/-- **Logarithmic sum, exponentiated** (DLMF 25.11.37) for complex `Re a ≥ 1`, `n = 2, 3, …`:
`exp(∑_{k≥1} ((-1)^k/k) ζ(nk, a)) = Γ(a)^{-n} ∏_{j=0}^{n-1} Γ(a - e^{(2j+1)πi/n})`
(branch-free form of the printed identity, whose logarithms must be read as the analytic branch of
`ln Γ`). -/
@[dlmf 25.11.E37]
theorem exp_tsum_hurwitzZeta_eq_prod_gamma {n : ℕ} (hn : 2 ≤ n) {a : ℂ} (ha : 1 ≤ a.re) :
    Summable (fun k : ℕ => (-1) ^ (k + 1) / (k + 1 : ℂ) * hurwitzZetaComplex (n * (k + 1)) a) ∧
    cexp (∑' k : ℕ, (-1) ^ (k + 1) / (k + 1 : ℂ) * hurwitzZetaComplex (n * (k + 1)) a) =
      (∏ j ∈ Finset.range n, Gamma (a - cexp ((2 * j + 1) * π * I / n))) / Gamma a ^ n := by
  sorry

/-- `‖a‖ ≤ ‖a + m‖` for `Re a > 0` and `m ≥ 0`. -/
lemma s25b_norm_le_norm_add_nat {a : ℂ} (ha : 0 < a.re) (m : ℕ) : ‖a‖ ≤ ‖a + m‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    normSq_apply, normSq_apply]
  simp only [add_re, natCast_re, add_im, natCast_im, add_zero]
  nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- `iteratedDeriv k ψ^{(n)} = ψ^{(n+k)}`. -/
lemma s25b_iteratedDeriv_polygamma (n k : ℕ) :
    iteratedDeriv k (DLMF.Gamma.polygamma n) = DLMF.Gamma.polygamma (k + n) := by
  funext w
  unfold DLMF.Gamma.polygamma
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply]

/-- **Generating function for polygamma differences** (DLMF 25.11.38): for `n ≥ 1`, `Re a > 0`,
`|z| < |a|`, `∑_{k≥1} C(n+k, k) ζ(n+k+1, a) z^k = ((-1)ⁿ/n!)(ψ⁽ⁿ⁾(a) - ψ⁽ⁿ⁾(a - z))`. -/
@[dlmf 25.11.E38]
theorem hasSum_hurwitzZeta_polygamma_sub {n : ℕ} (hn : 1 ≤ n) {a z : ℂ} (ha : 0 < a.re)
    (hz : ‖z‖ < ‖a‖) :
    HasSum (fun k : ℕ => ((n + (k + 1)).choose (k + 1) : ℂ) *
        hurwitzZetaComplex (n + (k + 1) + 1 : ℕ) a * z ^ (k + 1))
      ((-1) ^ n / n ! * (DLMF.Gamma.polygamma n a - DLMF.Gamma.polygamma n (a - z))) := by
  have hmem : ∀ w ∈ Metric.ball (0 : ℂ) ‖a‖, a - w ∈ DLMF.Gamma.notNegNat := by
    intro w hw m hm
    rw [mem_ball_zero_iff] at hw
    have hw' : w = a + m := by linear_combination -hm
    rw [hw'] at hw
    linarith [s25b_norm_le_norm_add_nat ha m]
  have hd : DifferentiableOn ℂ (fun w => DLMF.Gamma.polygamma n (a - w))
      (Metric.ball 0 ‖a‖) := by
    intro w hw
    have hA : AnalyticOnNhd ℂ Complex.digamma DLMF.Gamma.notNegNat :=
      fun x hx => DLMF.Gamma.analyticAt_digamma hx
    have h1 := (hA.iterated_deriv n) (a - w) (hmem w hw)
    rw [← iteratedDeriv_eq_iterate] at h1
    exact (h1.differentiableAt.comp w ((differentiableAt_const a).sub differentiableAt_id))
      |>.differentiableWithinAt
  have hT := Complex.hasSum_taylorSeries_on_ball hd (mem_ball_zero_iff.mpr hz)
  simp_rw [iteratedDeriv_comp_const_sub] at hT
  simp only [s25b_iteratedDeriv_polygamma, sub_zero, smul_eq_mul] at hT
  have h1 := ((hasSum_nat_add_iff' 1).mpr hT).mul_left (-((-1) ^ n / n ! : ℂ))
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, inv_one, one_mul, zero_add] at h1
  convert h1 using 1
  · funext k
    have hk : 1 ≤ n + (k + 1) := by omega
    have hζ := hurwitzZetaComplex_nat_eq_polygamma hk ha
    rw [show ((n + (k + 1) + 1 : ℕ) : ℂ) = ((n + (k + 1) : ℕ) : ℂ) + 1 by push_cast; ring, hζ,
      show k + 1 + n = n + (k + 1) by ring]
    have hc := Nat.add_choose_mul_factorial_mul_factorial n (k + 1)
    have hc' : ((n + (k + 1)).choose (k + 1) : ℂ) * n ! * (k + 1)! = (n + (k + 1))! := by
      exact_mod_cast (by linarith [hc] : (n + (k + 1)).choose (k + 1) * n ! * (k + 1)! =
        (n + (k + 1))!)
    have hf1 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hf2 : ((k + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (k + 1).factorial_ne_zero
    have hf3 : ((n + (k + 1))! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n + (k + 1)).factorial_ne_zero
    have hch : ((n + (k + 1)).choose (k + 1) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    rw [← hc']
    field_simp
    ring
  · ring

/-- **Catalan's constant from `ζ(·, 3/4)`** (DLMF 25.11.39):
`∑_{k≥2} (k/2^k) ζ(k+1, 3/4) = 8G`, `G` Catalan's constant (25.11.40,
`DLMF.Constants.catalanConstant`). -/
@[dlmf 25.11.E39]
theorem hasSum_hurwitzZeta_three_quarters :
    HasSum (fun k : ℕ => ((k + 2 : ℕ) : ℂ) / 2 ^ (k + 2) *
        hurwitzZeta ((3 / 4 : ℝ) : UnitAddCircle) (k + 3))
      (8 * DLMF.Constants.catalanConstant) := by
  have h := (hasSum_hurwitzZeta_polygamma_sub (n := 1) le_rfl (a := 3 / 4) (z := 1 / 2)
    (by norm_num) (by norm_num)).mul_left (1 / 2)
  rw [show (3 / 4 : ℂ) - 1 / 2 = 1 / 4 by norm_num, DLMF.Constants.trigamma_one_quarter,
    DLMF.Constants.trigamma_three_quarters] at h
  convert h using 1
  · funext k
    have hs : ((1 + (k + 1) + 1 : ℕ) : ℂ) ≠ 1 := by
      norm_cast; omega
    rw [show (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) by push_cast; ring,
      r25b_hurwitzZetaComplex_mathlib (by norm_num) (by norm_num) hs,
      show 1 + (k + 1) = k + 2 by ring, Nat.choose_succ_self_right]
    push_cast
    simp only [one_div, inv_pow]
    ring_nf
  · simp
    ring_nf

/-! ### §25.11(xii) `a`-asymptotic behaviour -/

/-- **Small `a`** (DLMF 25.11.41): as `a → 0` (complex), for fixed `s ≠ 1`,
`ζ(s, a+1) = ζ(s) - s ζ(s+1) a + O(a²)`. We also assume `s ≠ 0` (implicit condition: at `s = 0`
the coefficient `s ζ(s+1)` is to be read as its limit `1`; with Lean's junk `ζ(1)` the literal
statement fails there). -/
@[dlmf 25.11.E41]
theorem hurwitzZetaComplex_add_one_isBigO {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (fun a => hurwitzZetaComplex s (a + 1) - (riemannZeta s - s * riemannZeta (s + 1) * a))
      =O[𝓝 0] (fun a => a ^ 2) := by
  set f : ℂ → ℂ := fun a => hurwitzZetaComplex s (a + 1)
  have hB : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ one_pos
  have hre : ∀ a ∈ Metric.ball (0 : ℂ) 1, 0 < (a + 1).re := fun a ha => by
    rw [Metric.mem_ball, dist_zero_right] at ha
    have := neg_abs_le a.re
    have := abs_re_le_norm a
    simp; linarith
  have hf : DifferentiableOn ℂ f (Metric.ball 0 1) := fun a ha =>
    ((r25b_differentiableOn_hurwitzZetaComplex_param hs1 (a + 1) (hre a ha)).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds (hre a ha))).comp a
      (differentiableAt_id.add_const 1) |>.differentiableWithinAt
  have hd : DifferentiableOn ℂ (dslope f 0) (Metric.ball 0 1) :=
    (differentiableOn_dslope hB).mpr hf
  have hc : ContinuousAt (dslope (dslope f 0) 0) 0 :=
    continuousAt_dslope_same.mpr (hd.differentiableAt hB)
  have hf0 : f 0 = riemannZeta s := by simp [f, hurwitzZetaComplex_one hs1]
  have hs1' : s + 1 ≠ 1 := fun h => hs0 (by linear_combination h)
  have hder : deriv f 0 = -s * riemannZeta (s + 1) := by
    have h1 := r25b_hasDerivAt_hurwitzZetaComplex_param hs0 hs1 (a₀ := 1) (by simp)
    rw [show (1 : ℂ) = 0 + 1 by ring] at h1
    have h := h1.comp_add_const (0 : ℂ) 1
    simp only [zero_add] at h
    rw [h.deriv, hurwitzZetaComplex_one hs1']
  have key : ∀ a, f a - (riemannZeta s - s * riemannZeta (s + 1) * a) =
      a ^ 2 * dslope (dslope f 0) 0 a := by
    intro a
    have h1 := sub_smul_dslope f 0 a
    have h2 := sub_smul_dslope (dslope f 0) 0 a
    rw [dslope_same, hder] at h2
    simp only [sub_zero, smul_eq_mul] at h1 h2
    rw [← hf0]
    linear_combination -h1 - a * h2
  have hO : (fun a => dslope (dslope f 0) 0 a) =O[𝓝 0] (fun _ => (1 : ℂ)) :=
    hc.tendsto.isBigO_one ℂ
  have := (isBigO_refl (fun a : ℂ => a ^ 2) (𝓝 0)).mul hO
  simp only [mul_one] at this
  exact this.congr_left fun a => (key a).symm

/-- **Large imaginary part** (DLMF 25.11.42): for `Re s > 1`, `ζ(s, α + iβ) → 0` as `β → ±∞`,
uniformly for `α` in bounded subsets of `[0, ∞)`. -/
@[dlmf 25.11.E42]
theorem tendstoUniformlyOn_hurwitzZetaComplex_im {s : ℂ} (hs : 1 < s.re) (A : ℝ) :
    TendstoUniformlyOn (fun (β : ℝ) (α : ℝ) => hurwitzZetaComplex s (α + β * I)) 0
      (cocompact ℝ) (Icc 0 A) := by
  sorry

/-- The sector `|ph a| ≤ π - δ` of DLMF §25.11(xii). -/
def z25b_sector (δ : ℝ) : Set ℂ := {a | |arg a| ≤ π - δ}

/-- **Large-`a` expansion** (DLMF 25.11.43): for `s ≠ 1` and `0 < δ < π`, as `a → ∞` in
`|ph a| ≤ π - δ`, `ζ(s,a) - a^{1-s}/(s-1) - a^{-s}/2 ∼ ∑_{k≥1} (B_{2k}/(2k)!) (s)_{2k-1}
a^{1-s-2k}`: for every `K` the remainder after `K` terms is `O(a^{-1-s-2K})`. -/
@[dlmf 25.11.E43]
theorem hurwitzZetaComplex_asymptotic {s : ℂ} (hs : s ≠ 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π)
    (K : ℕ) :
    (fun a => hurwitzZetaComplex s a - a ^ (1 - s) / (s - 1) - a ^ (-s) / 2 -
        ∑ k ∈ Finset.Icc 1 K, (bernoulli (2 * k) : ℂ) / (2 * k)! * poch s (2 * k - 1) *
          a ^ (1 - s - 2 * k))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 (z25b_sector δ)] (fun a => a ^ (-1 - s - 2 * K)) := by
  sorry

/-- **Large-`a` expansion of `ζ'(-1, a)`** (DLMF 25.11.44), `0 < δ < π`, `|ph a| ≤ π - δ`:
`ζ'(-1,a) - 1/12 + a²/4 - (1/12 - a/2 + a²/2) ln a ∼ -∑_{k≥1} B_{2k+2}/((2k+2)(2k+1)2k) a^{-2k}`. -/
@[dlmf 25.11.E44]
theorem deriv_hurwitzZetaComplex_neg_one_asymptotic {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π) (K : ℕ) :
    (fun a : ℂ => deriv (fun s => hurwitzZetaComplex s a) (-1) - 1 / 12 + a ^ 2 / 4 -
        (1 / 12 - a / 2 + a ^ 2 / 2) * Complex.log a +
        ∑ k ∈ Finset.Icc 1 K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2) * (2 * k + 1) * (2 * k)) *
          a ^ (-(2 * k : ℤ)))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 (z25b_sector δ)] (fun a => a ^ (-(2 * K + 2 : ℤ))) := by
  sorry

/-- **Large-`a` expansion of `ζ'(-2, a)`** (DLMF 25.11.45), `0 < δ < π`, `|ph a| ≤ π - δ`:
`ζ'(-2,a) - a/12 + a³/9 - (a/6 - a²/2 + a³/3) ln a ∼
∑_{k≥1} 2B_{2k+2}/((2k+2)(2k+1)2k(2k-1)) a^{-(2k-1)}`. -/
@[dlmf 25.11.E45]
theorem deriv_hurwitzZetaComplex_neg_two_asymptotic {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π) (K : ℕ) :
    (fun a : ℂ => deriv (fun s => hurwitzZetaComplex s a) (-2) - a / 12 + a ^ 3 / 9 -
        (a / 6 - a ^ 2 / 2 + a ^ 3 / 3) * Complex.log a -
        ∑ k ∈ Finset.Icc 1 K, 2 * (bernoulli (2 * k + 2) : ℂ) /
          ((2 * k + 2) * (2 * k + 1) * (2 * k) * (2 * k - 1)) * a ^ (-(2 * k - 1 : ℤ)))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 (z25b_sector δ)] (fun a => a ^ (-(2 * K + 1 : ℤ))) := by
  sorry

end DLMF.Zeta

end
