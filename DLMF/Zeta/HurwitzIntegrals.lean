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
# The Hurwitz zeta function: integrals and sums

Integral representations (DLMF §25.11(vii)), further integrals (§25.11(viii)), further series
(§25.11(ix)–(x)) and sums (§25.11(xi)) of the Hurwitz zeta function; the loop integral 25.11.30 is
in `DLMF.Zeta.HurwitzLoopIntegral` and the asymptotic behaviour in `a` (§25.11(xii)) in
`DLMF.Zeta.HurwitzAsymptotics`.

## Main definitions

* `binetIntegrand`: the integrand of DLMF 25.11.27.

## Main results

* `hurwitzZetaComplex_eq_integral`: the Laplace-type integral DLMF 25.11.25.
* `tendsto_hurwitzZeta_sawtooth_integral`: the sawtooth integral DLMF 25.11.26.
* `hurwitzZetaComplex_eq_integral_bernoulli`, `hurwitzZetaComplex_eq_integral_bernoulli_sub`:
  DLMF 25.11.27–25.11.28.
* `riemannZeta_eq_half_add_bernoulli_integral`: DLMF 25.5.7, the case `a = 1` of 25.11.28.
* `hurwitzZetaComplex_hermite`: Hermite's formula DLMF 25.11.29.
* `integral_cosh_eq_hurwitzZetaComplex_sub`: DLMF 25.11.31.
* `integral_pow_mul_digamma`, `integral_deriv_hurwitzZetaComplex`: DLMF 25.11.32–25.11.34.
* `tendsto_alternating_hurwitz`, `tendsto_integral_alternating_hurwitz`: DLMF 25.11.35.
* `hasSum_hurwitzZeta_log_gamma`, `exp_tsum_hurwitzZeta_eq_prod_gamma`: DLMF 25.11.37.
* `hasSum_hurwitzZeta_polygamma_sub`: DLMF 25.11.38.
* `hasSum_hurwitzZeta_three_quarters`: Catalan's constant, DLMF 25.11.39.

## Implementation notes

Statements use DLMF's `ζ(s, a)` in the form `DLMF.Zeta.hurwitzZetaComplex s a` for complex
`a` (see `DLMF.Zeta.Hurwitz`), and Mathlib's `hurwitzZeta` where DLMF's range is `0 < a ≤ 1`.

* Integrals `∫_0^a` with complex `a` are taken along the segment `[0, a]`, written
  `∫_0^1 a f(ta) dt`.
* Conditionally convergent series and improper integrals are stated as limits of partial sums
  or of `∫_0^X` (resp. `∫_{-a}^X`) as `X → ∞`.
* 25.11.37 involves `ln Γ` of complex arguments. With principal logarithms it holds only modulo
  `2πi` (mpmath, e.g. `n = 2`, `a = 4 - 9i`); it is stated exactly with principal logarithms for
  real `a ≥ 1` (where every logarithm is of a positive real) and in exponentiated form for
  complex `Re a ≥ 1` (the identity with the analytic branch of `ln Γ` is equivalent to it plus a
  continuity statement).
* The removable singularities at `s = 1` in 25.11.31 and 25.11.35 (differences of two Hurwitz
  functions) are excluded by a hypothesis `s ≠ 1`, since Lean's value at the pole is junk.
-/

@[expose] public section

open Complex Filter Set MeasureTheory HurwitzZeta Asymptotics
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

open DLMF.Hypergeometric (pochhammer)

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
  have h := hasSum_lerch_lerchIntegral (z := 1) (by linarith) ha (Or.inr ⟨by simp, hs⟩)
  simp only [one_pow, lerchIntegral, one_mul] at h
  refine (hasSum_hurwitzZetaComplex hs ha').unique ?_
  rw [one_div]
  exact h.congr_fun fun n => by rw [add_comm]

/-- `B̃₂` is continuous. -/
private lemma continuous_periodicBernoulli_two : Continuous (periodicBernoulli 2) := by
  have : periodicBernoulli 2 = periodizedBernoulli 2 ∘ ((↑) : ℝ → UnitAddCircle) := by
    funext x; exact DLMF.BernoulliEuler.periodicBernoulliB_eq_periodizedBernoulli 2 x
  rw [this]; exact (periodizedBernoulli.continuous (by norm_num)).comp continuous_quotient_mk'

/-- `B̃₂' = 2 B̃₁ = 2({x} - 1/2)` off the integers. -/
private lemma hasDerivAt_periodicBernoulli_two {x : ℝ} (hx : x ∉ range (Int.cast : ℤ → ℝ)) :
    HasDerivAt (periodicBernoulli 2) (2 * (Int.fract x - 1 / 2)) x := by
  set m := ⌊x⌋
  have hlt : (m : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (fun h => hx ⟨m, h⟩)
  have hlt2 : x < m + 1 := Int.lt_floor_add_one x
  have heq : periodicBernoulli 2 =ᶠ[𝓝 x] (fun y => bernoulliFun 2 (y - m)) := by
    filter_upwards [Ioo_mem_nhds hlt hlt2] with y hy
    rw [periodicBernoulli, Int.fract, Int.floor_eq_iff.mpr ⟨hy.1.le, hy.2⟩]
  have hd := (hasDerivAt_bernoulliFun 2 (x - m)).comp x ((hasDerivAt_id x).sub_const (m : ℝ))
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  convert hd using 1
  · funext y; simp
  · rw [show Int.fract x = x - m from rfl]; simp [bernoulliFun_one]

/-- A bounded measurable function divided by `(x+a)^w`, `Re w ≥ 0`, `a > 0`, is interval
integrable on `[0, X]`. -/
private lemma intervalIntegrable_bdd_div_add_cpow {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 0 ≤ w.re) {X : ℝ} (hX : 0 ≤ X) :
    IntervalIntegrable (fun x : ℝ => ((g x : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ w) volume 0 X := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  refine Measure.integrableOn_of_bounded (M := C * a ^ (-w.re)) (by simp)
    ((Complex.measurable_ofReal.comp hg).div ((Complex.measurable_ofReal.comp
      (measurable_id.add_const a)).pow_const w)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hxa : 0 < x + a := by linarith [hx.1]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos hxa,
    div_eq_mul_inv, ← Real.rpow_neg hxa.le]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine mul_le_mul (hC x) ?_ (by positivity) hC0
  exact Real.rpow_le_rpow_of_nonpos ha (by linarith [hx.1]) (by linarith)

/-- **Sawtooth integral** (DLMF 25.11.26): `ζ(s,a) = -s ∫_{-a}^∞ (x - ⌊x⌋ - 1/2)/(x+a)^{s+1} dx`
for `-1 < Re s < 0`, `0 < a ≤ 1`; the integral converges conditionally at `∞` and is stated as the
limit of `∫_{-a}^X`. -/
@[dlmf 25.11.E26]
theorem tendsto_hurwitzZeta_sawtooth_integral {s : ℂ} (hs1 : -1 < s.re) (hs0 : s.re < 0) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun X : ℝ => -s * ∫ x in (-a)..X,
        ((Int.fract x - 1 / 2 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 1)) atTop
      (𝓝 (hurwitzZeta (a : UnitAddCircle) s)) := by
  have hs1' : s ≠ 1 := by rintro rfl; norm_num at hs0
  have hsz : s ≠ 0 := by rintro rfl; simp at hs0
  set f : ℝ → ℂ := fun x => ((Int.fract x - 1 / 2 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 1)
  set g : ℝ → ℂ := fun x =>
    ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 2)
  set F : ℝ → ℂ := fun x =>
    ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) / (((x + a : ℝ)) : ℂ) ^ (s + 1)
  obtain ⟨C2, hC2⟩ := exists_abs_periodicBernoulli_le 2
  have hb2 : ∀ x, |periodicBernoulli 2 x - (bernoulli 2 : ℝ)| ≤ C2 + |(bernoulli 2 : ℝ)| :=
    fun x => (abs_sub _ _).trans (by linarith [hC2 x])
  have hb1 : ∀ x : ℝ, |Int.fract x - 1 / 2| ≤ 1 := fun x => by
    rw [abs_le]; constructor <;> linarith [Int.fract_nonneg x, Int.fract_lt_one x]
  have hmf : Measurable fun x : ℝ => Int.fract x - 1 / 2 := measurable_fract.sub_const _
  have hmg : Measurable fun x : ℝ => periodicBernoulli 2 x - (bernoulli 2 : ℝ) :=
    (measurable_periodicBernoulli 2).sub_const _
  -- the piece on `[-a, 0]`
  set h : ℝ → ℂ := fun y => (y : ℂ) ^ (-s) + (1 / 2 - a) * (y : ℂ) ^ (-s - 1)
  have hh1 : IntervalIntegrable (fun y : ℝ => (y : ℂ) ^ (-s)) volume 0 a :=
    intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
  have hh2 : IntervalIntegrable (fun y : ℝ => (y : ℂ) ^ (-s - 1)) volume 0 a :=
    intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
  have hhI : IntervalIntegrable h volume 0 a := hh1.add (hh2.const_mul _)
  have hfh : ∀ᵐ x : ℝ ∂volume, x ∈ Set.uIoc (-a) 0 → f x = h (x + a) := by
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne] with x hx0 hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hx' : x < 0 := lt_of_le_of_ne hx.2 hx0
    have hxa : 0 < x + a := by linarith [hx.1]
    have hfr : Int.fract x = x + 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [hx.1], by linarith, -1, by push_cast; ring⟩
    have hy0 : ((x + a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxa.ne'
    simp only [f, h, hfr]
    rw [show -s = 1 - (s + 1) by ring, show 1 - (s + 1) - 1 = -(s + 1) by ring,
      cpow_sub _ _ hy0, cpow_one, cpow_neg]
    push_cast
    field_simp
    ring
  have hfI0 : IntervalIntegrable f volume (-a) 0 := by
    have := hhI.comp_add_right a
    simp only [zero_sub, sub_self] at this
    refine this.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hfh] with x hx hxm using (hx hxm).symm
  have hint0 : ∫ x in (-a)..0, f x =
      (a : ℂ) ^ (1 - s) / (1 - s) - (1 / 2 - a) * (a : ℂ) ^ (-s) / s := by
    rw [intervalIntegral.integral_congr_ae hfh, intervalIntegral.integral_comp_add_right h a]
    simp only [neg_add_cancel, zero_add]
    rw [intervalIntegral.integral_add hh1 (hh2.const_mul _), intervalIntegral.integral_const_mul,
      integral_cpow (Or.inl (by simp; linarith)), integral_cpow (Or.inl (by simp; linarith))]
    have h1 : -s + 1 ≠ 0 := by
      intro h0; have := congrArg re h0; simp at this; linarith
    have h2 : -s - 1 + 1 ≠ 0 := by rw [sub_add_cancel]; exact neg_ne_zero.mpr hsz
    rw [ofReal_zero, zero_cpow h1, zero_cpow h2, show -s - 1 + 1 = -s by ring,
      show -s + 1 = 1 - s by ring]
    have h3 : (1 : ℂ) - s ≠ 0 := by rw [← show -s + 1 = 1 - s by ring]; exact h1
    field_simp
    ring
  -- integration by parts on `[0, X]`
  have hparts : ∀ X : ℝ, 0 ≤ X → ∫ x in (0 : ℝ)..X, f x =
      F X / 2 + (s + 1) / 2 * ∫ x in (0 : ℝ)..X, g x := by
    intro X hX
    have hfI := intervalIntegrable_bdd_div_add_cpow hmf hb1 ha0 (w := s + 1) (by simp; linarith)
      hX
    have hgI := intervalIntegrable_bdd_div_add_cpow hmg hb2 ha0 (w := s + 2) (by simp; linarith)
      hX
    have hd := integral_eq_of_hasDerivAt_off_countable_of_le F
      (fun x => 2 * f x - (s + 1) * g x) hX (countable_range (Int.cast : ℤ → ℝ)) ?_ ?_
      ((hfI.const_mul 2).sub (hgI.const_mul _))
    · rw [intervalIntegral.integral_sub (hfI.const_mul 2) (hgI.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hd
      have hF0 : F 0 = 0 := by
        simp [F, periodicBernoulli]
      rw [hF0, sub_zero] at hd
      linear_combination hd / 2
    · refine ((Complex.continuous_ofReal.comp
        (continuous_periodicBernoulli_two.sub continuous_const)).continuousOn).div ?_ ?_
      · exact ContinuousOn.cpow_const (Complex.continuous_ofReal.comp
          (continuous_id.add continuous_const)).continuousOn fun x hx =>
            ofReal_mem_slitPlane.mpr (by linarith [hx.1])
      · intro x hx
        exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (by linarith [hx.1] : x + a ≠ 0)))
    · intro x hx
      have hxa : 0 < x + a := by linarith [hx.1.1]
      have h1 := (hasDerivAt_periodicBernoulli_two hx.2).sub_const (bernoulli 2 : ℝ)
      have h1c := h1.ofReal_comp
      have h2 : HasDerivAt (fun y : ℝ => (((y + a : ℝ)) : ℂ) ^ (-(s + 1)))
          (-(s + 1) * (((x + a : ℝ)) : ℂ) ^ (-(s + 1) - 1)) x := by
        have hlin : HasDerivAt (fun y : ℝ => (((y + a : ℝ)) : ℂ)) 1 x := by
          simpa using ((hasDerivAt_id x).add_const a).ofReal_comp
        have hc := (Complex.hasStrictDerivAt_cpow_const (c := -(s + 1))
          (ofReal_mem_slitPlane.mpr hxa)).hasDerivAt.comp x hlin
        rw [mul_one] at hc
        exact hc
      have := h1c.mul h2
      convert this using 1
      · funext y; simp only [F, Pi.mul_apply, div_eq_mul_inv, cpow_neg]
      · simp only [f, g]
        have hy0 : (((x + a : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hxa.ne'
        rw [show -(s + 1) - 1 = -(s + 2) by ring, cpow_neg, cpow_neg]
        push_cast
        ring
  -- limits
  have hgInt : IntegrableOn g (Ioi 0) :=
    integrableOn_bdd_div_add_cpow hmg hb2 (w := s + 2) (by simp; linarith) ha0 le_rfl
  set J := ∫ x in Ioi (0 : ℝ), g x
  have hlimJ : Tendsto (fun X : ℝ => ∫ x in (0 : ℝ)..X, g x) atTop (𝓝 J) :=
    intervalIntegral_tendsto_integral_Ioi 0 hgInt tendsto_id
  have hlimF : Tendsto F atTop (𝓝 0) := by
    have ht : Tendsto (fun X : ℝ => (C2 + |(bernoulli 2 : ℝ)|) * (X + a) ^ (-(s.re + 1))) atTop
        (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (y := s.re + 1) (by linarith)).comp
        (tendsto_atTop_add_const_right _ a tendsto_id)).const_mul (C2 + |(bernoulli 2 : ℝ)|)
      simpa using this
    refine squeeze_zero_norm' ?_ ht
    · filter_upwards [eventually_ge_atTop 0] with X hX
      have hxa : 0 < X + a := by linarith
      simp only [F]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos hxa,
        div_eq_mul_inv, ← Real.rpow_neg hxa.le]
      simp only [add_re, one_re]
      exact mul_le_mul_of_nonneg_right (hb2 X) (by positivity)
  have hlim : Tendsto (fun X : ℝ => -s * ((∫ x in (-a)..0, f x) +
      (F X / 2 + (s + 1) / 2 * ∫ x in (0 : ℝ)..X, g x))) atTop
      (𝓝 (-s * ((∫ x in (-a)..0, f x) + (0 / 2 + (s + 1) / 2 * J)))) :=
    (((hlimF.div_const 2).add (hlimJ.const_mul _)).const_add _).const_mul _
  have hval : -s * ((∫ x in (-a)..0, f x) + (0 / 2 + (s + 1) / 2 * J)) =
      hurwitzZeta (a : UnitAddCircle) s := by
    rw [← hurwitzZetaComplex_eq_hurwitzZeta ha0 ha1 hs1',
      hurwitzZetaComplex_eulerMaclaurin_two hs1' hs1 ha0, hint0]
    have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1')
    have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1'
    have ha0' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    have hpow : (a : ℂ) ^ (1 - s) = a * (a : ℂ) ^ (-s) := by
      rw [sub_eq_add_neg, cpow_add _ _ ha0', cpow_one]
    rw [hpow]
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with X hX
  have hfIX := intervalIntegrable_bdd_div_add_cpow hmf hb1 ha0 (w := s + 1) (by simp; linarith) hX
  rw [← intervalIntegral.integral_add_adjacent_intervals hfI0 hfIX, hparts X hX]

/-- `{Re s > c} \ {1}` is preconnected for `c < 1`. -/
private lemma isPreconnected_re_gt_diff_one {c : ℝ} (hc : c < 1) :
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
private lemma norm_binetBeta_mul_cpow_mul_exp_le {s a : ℂ} {x σ₁ σ₂ : ℝ} (hx : 0 < x)
    (h1 : σ₁ ≤ s.re)
    (h2 : s.re ≤ σ₂) :
    ‖((DLMF.Gamma.binetBeta x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) * cexp (-(a * x))‖ ≤
      (x ^ σ₁ + x ^ (σ₂ - 1)) * Real.exp (-(a.re * x)) := by
  rw [mul_assoc, norm_mul, norm_cpow_mul_exp_neg hx, Complex.norm_real, Real.norm_eq_abs,
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
noncomputable def binetIntegrand (a s : ℂ) (x : ℝ) : ℂ :=
  ((DLMF.Gamma.binetBeta x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) * cexp (-(a * x))

/-- The stated relation follows from the given hypotheses: `AEStronglyMeasurable
(binetIntegrand a s) (volume.restrict (Ioi 0))`. -/
private lemma aestronglyMeasurable_binetIntegrand (a s : ℂ) :
    AEStronglyMeasurable (binetIntegrand a s) (volume.restrict (Ioi 0)) := by
  have hb : AEStronglyMeasurable (fun x : ℝ => ((DLMF.Gamma.binetBeta x : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) :=
    (continuous_ofReal.comp_continuousOn DLMF.Gamma.continuousOn_binetBeta).aestronglyMeasurable
      measurableSet_Ioi
  have := hb.mul (aestronglyMeasurable_cpow_mul_exp_neg s a)
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [binetIntegrand, Pi.mul_apply, mul_assoc]

/-- Integrability of the 25.11.27 integrand for `Re s > -1`, `Re a > 0`. -/
private lemma integrableOn_binetIntegrand {a s : ℂ} (ha : 0 < a.re) (hs : -1 < s.re) :
    IntegrableOn (binetIntegrand a s) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => (x ^ s.re + x ^ ((s.re + 1) - 1)) *
      Real.exp (-(a.re * x))) (Ioi 0) := by
    have h1 := integrableOn_rpow_mul_exp_neg (σ := s.re + 1) (by linarith) ha
    have h2 := integrableOn_rpow_mul_exp_neg (σ := s.re + 1) (by linarith) ha
    simp only [add_sub_cancel_right] at h1 h2 ⊢
    exact (h1.add h2).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  refine hg.mono' (aestronglyMeasurable_binetIntegrand a s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_binetBeta_mul_cpow_mul_exp_le hx le_rfl (by linarith)

/-- Holomorphy in `s` of the 25.11.27 integral on `Re s > -1`. -/
private lemma differentiableOn_integral_binetIntegrand {a : ℂ} (ha : 0 < a.re) :
    DifferentiableOn ℂ (fun s => ∫ x in Ioi (0 : ℝ), binetIntegrand a s x)
      {s : ℂ | -1 < s.re} := by
  have hU : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const continuous_re
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated hU 0
    (fun s _ => aestronglyMeasurable_binetIntegrand a s) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s _
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold binetIntegrand
    exact ((differentiableAt_const _).mul ((differentiableAt_id.sub_const 1).const_cpow
      (Or.inl hx0))).mul (differentiableAt_const _)
  · intro s₀ hs₀
    have hs₀' : -1 < s₀.re := hs₀
    set δ := (s₀.re + 1) / 2
    have hδ : 0 < δ := by simp only [δ]; linarith
    refine ⟨Metric.ball s₀ δ, Metric.ball_mem_nhds _ hδ, fun x =>
      (x ^ (s₀.re - δ) + x ^ ((s₀.re + δ + 1) - 1)) * Real.exp (-(a.re * x)), ?_, ?_⟩
    · have h1 := integrableOn_rpow_mul_exp_neg (σ := s₀.re - δ + 1)
        (by simp only [δ]; linarith) ha
      have h2 := integrableOn_rpow_mul_exp_neg (σ := s₀.re + δ + 1)
        (by simp only [δ]; linarith) ha
      simp only [add_sub_cancel_right] at h1
      exact (h1.add h2).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have := abs_re_le_norm (s - s₀)
      simp only [sub_re] at this
      exact norm_binetBeta_mul_cpow_mul_exp_le hx (by linarith [neg_abs_le (s.re - s₀.re)])
        (by linarith [le_abs_self (s.re - s₀.re)])

/-- 25.11.27 for `Re s > 1`, from 25.11.25 and two Gamma integrals. -/
private lemma integral_binetIntegrand_of_one_lt_re {a s : ℂ} (ha : 0 < a.re) (hs : 1 < s.re) :
    ∫ x in Ioi (0 : ℝ), binetIntegrand a s x =
      Gamma s * (hurwitzZetaComplex s a - a ^ (-s) / 2 - a ^ (1 - s) / (s - 1)) := by
  have ha' : ∀ m : ℕ, a ≠ -m := fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  set P : ℝ → ℂ := fun x => (x : ℂ) ^ ((s - 1) - 1) * cexp (-(a * x))
  set Q : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * cexp (-(a * x))
  have hP : IntegrableOn P (Ioi 0) := integrableOn_cpow_mul_exp_neg (by simp; linarith) ha
  have hQ : IntegrableOn Q (Ioi 0) := integrableOn_cpow_mul_exp_neg (by linarith) ha
  have hB := integrableOn_binetIntegrand ha (s := s) (by linarith)
  have heq : EqOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * cexp (-((a + 1) * x)) /
      (1 - cexp (-(x : ℂ)))) (fun x => binetIntegrand a s x + P x - Q x / 2) (Ioi 0) := by
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
    simp only [binetIntegrand, DLMF.Gamma.binetBeta, P, Q]
    rw [cpow_sub (x := (x : ℂ)) (s - 1) 1 hx0, cpow_one]
    push_cast
    rw [show -((a + 1) * (x : ℂ)) = -(a * x) + -(x : ℂ) by ring, Complex.exp_add,
      Complex.exp_neg (x : ℂ), ← Complex.ofReal_exp]
    have he : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
    field_simp
    ring
  have h25 := hurwitzZetaComplex_eq_integral hs (a := a + 1) (by simp; linarith)
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_sub (f := fun x => binetIntegrand a s x + P x) (g := fun x => Q x / 2)
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
  change _ = _ + _ + 1 / Gamma s * ∫ x in Ioi (0 : ℝ), binetIntegrand a s x
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have han : ∀ n : ℕ, a + n ≠ 0 := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set W : Set ℂ := {t : ℂ | -1 < t.re} \ {1}
  have hW : IsOpen W := (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  set G : ℂ → ℂ := fun t => a ^ (-t) / 2 + a ^ (1 - t) / (t - 1) +
    1 / Gamma t * ∫ x in Ioi (0 : ℝ), binetIntegrand a t x
  have hF : DifferentiableOn ℂ (fun t => hurwitzZetaComplex t a) W := fun t ht =>
    (differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' ht.2 han).differentiableWithinAt
  have hG : DifferentiableOn ℂ G W := by
    intro t ht
    have ht1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht.2
    have hI := (differentiableOn_integral_binetIntegrand ha t ht.1).differentiableAt
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
      (isPreconnected_re_gt_diff_one (by norm_num)) (show (2 : ℂ) ∈ W by norm_num [W]) ?_
    have hopen : IsOpen {t : ℂ | 1 < t.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with t ht
    have hΓ : Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    simp only [G, integral_binetIntegrand_of_one_lt_re ha ht]
    field_simp
    ring
  exact heq ⟨hs0, hs⟩

/-- The bracket of DLMF 25.11.28, `1/(eˣ-1) - 1/x + 1/2 - ∑_{k=1}^n B_{2k}/(2k)! x^{2k-1}`. -/
private def bernoulliRemainder (n : ℕ) (x : ℝ) : ℝ :=
  1 / (Real.exp x - 1) - 1 / x + 1 / 2 -
    ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℝ) / (2 * k)! * x ^ (2 * k - 1)

/-- The bracket of 25.11.28 is `O(x^{2n+1})` uniformly on `x > 0`. -/
private lemma abs_bernoulliRemainder_le (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |bernoulliRemainder n x| ≤ 2 * DLMF.Gamma.binetRemConst n * x ^ (2 * n + 1) := by
  have h := DLMF.Gamma.abs_binetBeta_div_sub_binetPoly_le n hx
  have heq : bernoulliRemainder n x =
      x * (DLMF.Gamma.binetBeta x / x - DLMF.Gamma.binetPoly n x) := by
    simp only [bernoulliRemainder, DLMF.Gamma.binetBeta, DLMF.Gamma.binetPoly, mul_sub,
      Finset.mul_sum]
    rw [mul_div_cancel₀ _ hx.ne']
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [show 2 * k - 1 = (2 * k - 2) + 1 by omega, pow_succ]
    ring
  rw [heq, abs_mul, abs_of_pos hx, pow_succ]
  calc x * |DLMF.Gamma.binetBeta x / x - DLMF.Gamma.binetPoly n x|
      ≤ x * (2 * DLMF.Gamma.binetRemConst n * x ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left h hx.le
    _ = _ := by ring

/-- Domination of the 25.11.28 integrand on `σ₁ ≤ Re s ≤ σ₂`. -/
private lemma norm_bernoulliRemainder_mul_le (n : ℕ) {s a : ℂ} {x σ₁ σ₂ : ℝ} (hx : 0 < x)
    (h1 : σ₁ ≤ s.re) (h2 : s.re ≤ σ₂) :
    ‖((bernoulliRemainder n x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) * cexp (-(a * x))‖ ≤
      2 * DLMF.Gamma.binetRemConst n * ((x ^ (σ₁ + (2 * n + 1) - 1) +
        x ^ (σ₂ + (2 * n + 1) - 1)) * Real.exp (-(a.re * x))) := by
  rw [mul_assoc, norm_mul, norm_cpow_mul_exp_neg hx, Complex.norm_real, Real.norm_eq_abs]
  have hR := abs_bernoulliRemainder_le n hx
  have hC : 0 ≤ 2 * DLMF.Gamma.binetRemConst n * x ^ (2 * n + 1) := (abs_nonneg _).trans hR
  have hp : x ^ (2 * n + 1) * x ^ (s.re - 1) = x ^ (s.re + (2 * n + 1) - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx]; push_cast; ring_nf
  have hmono : x ^ (s.re + (2 * n + 1) - 1) ≤
      x ^ (σ₁ + (2 * n + 1) - 1) + x ^ (σ₂ + (2 * n + 1) - 1) := by
    rcases le_or_gt x 1 with hx1 | hx1
    · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show σ₁ + (2 * n + 1) - 1 ≤
        s.re + (2 * n + 1) - 1 by linarith)
      linarith [Real.rpow_nonneg hx.le (σ₂ + (2 * n + 1) - 1)]
    · have := Real.rpow_le_rpow_of_exponent_le hx1.le (show s.re + (2 * n + 1) - 1 ≤
        σ₂ + (2 * n + 1) - 1 by linarith)
      linarith [Real.rpow_nonneg hx.le (σ₁ + (2 * n + 1) - 1)]
  have hS : 0 ≤ DLMF.Gamma.binetRemConst n := by
    have : 0 ≤ 2 * DLMF.Gamma.binetRemConst n * x ^ (2 * n + 1) := hC
    have hxp : 0 < x ^ (2 * n + 1) := by positivity
    nlinarith
  have he := Real.exp_pos (-(a.re * x))
  calc |bernoulliRemainder n x| * (x ^ (s.re - 1) * Real.exp (-(a.re * x)))
      ≤ 2 * DLMF.Gamma.binetRemConst n * x ^ (2 * n + 1) *
          (x ^ (s.re - 1) * Real.exp (-(a.re * x))) :=
        mul_le_mul_of_nonneg_right hR (by positivity)
    _ = 2 * DLMF.Gamma.binetRemConst n * (x ^ (s.re + (2 * n + 1) - 1) *
          Real.exp (-(a.re * x))) := by rw [← hp]; ring
    _ ≤ _ := by gcongr

/-- The 25.11.28 integrand. -/
private def bernoulliRemainderIntegrand (n : ℕ) (a s : ℂ) (x : ℝ) : ℂ :=
  ((bernoulliRemainder n x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) * cexp (-(a * x))

private lemma aestronglyMeasurable_bernoulliRemainderIntegrand (n : ℕ) (a s : ℂ) :
    AEStronglyMeasurable (bernoulliRemainderIntegrand n a s) (volume.restrict (Ioi 0)) := by
  have hm : Measurable (bernoulliRemainder n) := by
    unfold bernoulliRemainder
    fun_prop
  have := (Complex.measurable_ofReal.comp hm).aestronglyMeasurable.mul
    (aestronglyMeasurable_cpow_mul_exp_neg s a) (μ := volume.restrict (Ioi 0))
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [bernoulliRemainderIntegrand, Pi.mul_apply, Function.comp, mul_assoc]

private lemma integrableOn_bernoulliRemainderIntegrand (n : ℕ) {a s : ℂ} (ha : 0 < a.re)
    (hs : -(2 * n + 1 : ℝ) < s.re) :
    IntegrableOn (bernoulliRemainderIntegrand n a s) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => 2 * DLMF.Gamma.binetRemConst n *
      ((x ^ (s.re + (2 * n + 1) - 1) + x ^ (s.re + (2 * n + 1) - 1)) *
        Real.exp (-(a.re * x)))) (Ioi 0) := by
    have h1 := integrableOn_rpow_mul_exp_neg (σ := s.re + (2 * n + 1)) (by linarith) ha
    refine IntegrableOn.congr_fun ((h1.add h1).const_mul (2 * DLMF.Gamma.binetRemConst n))
      (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  refine hg.mono' (aestronglyMeasurable_bernoulliRemainderIntegrand n a s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_bernoulliRemainder_mul_le n hx le_rfl le_rfl

private lemma differentiableOn_integral_bernoulliRemainderIntegrand (n : ℕ) {a : ℂ}
    (ha : 0 < a.re) :
    DifferentiableOn ℂ (fun s => ∫ x in Ioi (0 : ℝ), bernoulliRemainderIntegrand n a s x)
      {s : ℂ | -(2 * n + 1 : ℝ) < s.re} := by
  have hU : IsOpen {s : ℂ | -(2 * n + 1 : ℝ) < s.re} := isOpen_lt continuous_const continuous_re
  refine Complex.differentiableOn_integral_Ioi_of_locally_dominated hU 0
    (fun s _ => aestronglyMeasurable_bernoulliRemainderIntegrand n a s) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s _
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold bernoulliRemainderIntegrand
    exact ((differentiableAt_const _).mul ((differentiableAt_id.sub_const 1).const_cpow
      (Or.inl hx0))).mul (differentiableAt_const _)
  · intro s₀ hs₀
    have hs₀' : -(2 * n + 1 : ℝ) < s₀.re := hs₀
    set δ := (s₀.re + (2 * n + 1)) / 2
    have hδ : 0 < δ := by simp only [δ]; linarith
    refine ⟨Metric.ball s₀ δ, Metric.ball_mem_nhds _ hδ, fun x =>
      2 * DLMF.Gamma.binetRemConst n * ((x ^ ((s₀.re - δ) + (2 * n + 1) - 1) +
        x ^ ((s₀.re + δ) + (2 * n + 1) - 1)) * Real.exp (-(a.re * x))), ?_, ?_⟩
    · have h1 := integrableOn_rpow_mul_exp_neg (σ := (s₀.re - δ) + (2 * n + 1))
        (by simp only [δ]; linarith) ha
      have h2 := integrableOn_rpow_mul_exp_neg (σ := (s₀.re + δ) + (2 * n + 1))
        (by simp only [δ]; linarith) ha
      refine IntegrableOn.congr_fun ((h1.add h2).const_mul (2 * DLMF.Gamma.binetRemConst n))
        (fun x _ => ?_) measurableSet_Ioi
      simp only [Pi.add_apply]; ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have := abs_re_le_norm (s - s₀)
      simp only [sub_re] at this
      exact norm_bernoulliRemainder_mul_le n hx (by linarith [neg_abs_le (s.re - s₀.re)])
        (by linarith [le_abs_self (s.re - s₀.re)])

/-- 25.11.28 for `Re s > 1`, from 25.11.27 and Gamma integrals. -/
private lemma integral_bernoulliRemainderIntegrand_of_one_lt_re (n : ℕ) {a s : ℂ}
    (ha : 0 < a.re) (hs : 1 < s.re) :
    ∫ x in Ioi (0 : ℝ), bernoulliRemainderIntegrand n a s x =
      Gamma s * (hurwitzZetaComplex s a - a ^ (-s) / 2 - a ^ (1 - s) / (s - 1) -
        ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℂ) / (2 * k)! * pochhammer s (2 * k - 1) *
          a ^ (1 - s - 2 * k)) := by
  set c : ℕ → ℂ := fun k => (bernoulli (2 * k) : ℂ) / (2 * k)!
  set P : ℕ → ℝ → ℂ := fun k x =>
    (x : ℂ) ^ ((s + ((2 * k - 1 : ℕ) : ℂ)) - 1) * cexp (-(a * x))
  have hP : ∀ k ∈ Finset.Icc 1 n, IntegrableOn (P k) (Ioi 0) := fun k _ =>
    integrableOn_cpow_mul_exp_neg (by simp; linarith) ha
  have hB := integrableOn_binetIntegrand ha (s := s) (by linarith)
  have heq : EqOn (bernoulliRemainderIntegrand n a s)
      (fun x => binetIntegrand a s x - ∑ k ∈ Finset.Icc 1 n, c k * P k x) (Ioi 0) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0 : ℝ) < x from hx))
    simp only [bernoulliRemainderIntegrand, bernoulliRemainder, binetIntegrand,
      DLMF.Gamma.binetBeta, P, c]
    push_cast
    rw [sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hpow : (x : ℂ) ^ (s + ((2 * k - 1 : ℕ) : ℂ) - 1) =
        (x : ℂ) ^ (2 * k - 1) * (x : ℂ) ^ (s - 1) := by
      rw [show s + ((2 * k - 1 : ℕ) : ℂ) - 1 = (s - 1) + ((2 * k - 1 : ℕ) : ℂ) by ring,
        cpow_add _ _ hx0, cpow_natCast]
      ring
    rw [hpow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hB
    (integrable_finsetSum _ fun k hk => (hP k hk).const_mul (c k)), integral_finsetSum _
    fun k hk => (hP k hk).const_mul (c k), integral_binetIntegrand_of_one_lt_re ha hs]
  suffices hsum : ∑ k ∈ Finset.Icc 1 n, ∫ x in Ioi (0 : ℝ), c k * P k x =
      Gamma s * ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℂ) / (2 * k)! *
          pochhammer s (2 * k - 1) *
        a ^ (1 - s - 2 * k) by
    rw [hsum]; ring
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [integral_const_mul, DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (by simp; linarith) ha,
    DLMF.Hypergeometric.Gamma_add_nat_eq_pochhammer_mul_Gamma (by linarith)]
  have hcast : ((2 * k - 1 : ℕ) : ℂ) = 2 * k - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast, show -(s + (2 * (k : ℂ) - 1)) = 1 - s - 2 * k by ring]
  ring

/-- **Integral with `n` Bernoulli terms removed** (DLMF 25.11.28): for `Re s > -(2n+1)`, `s ≠ 1`,
`Re a > 0`. -/
@[dlmf 25.11.E28]
theorem hurwitzZetaComplex_eq_integral_bernoulli_sub (n : ℕ) {s a : ℂ} (hs : s ≠ 1)
    (hs0 : -(2 * n + 1 : ℝ) < s.re) (ha : 0 < a.re) :
    hurwitzZetaComplex s a = a ^ (-s) / 2 + a ^ (1 - s) / (s - 1) +
      (∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℂ) / (2 * k)! * pochhammer s (2 * k - 1) *
        a ^ (1 - s - 2 * k)) +
      1 / Gamma s * ∫ x in Ioi (0 : ℝ),
        ((1 / (Real.exp x - 1) - 1 / x + 1 / 2 -
          ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℝ) / (2 * k)! * x ^ (2 * k - 1) : ℝ) : ℂ) *
          (x : ℂ) ^ (s - 1) * cexp (-(a * x)) := by
  change _ = _ + _ + _ + 1 / Gamma s * ∫ x in Ioi (0 : ℝ), bernoulliRemainderIntegrand n a s x
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have han : ∀ m : ℕ, a + m ≠ 0 := fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  set W : Set ℂ := {t : ℂ | -(2 * n + 1 : ℝ) < t.re} \ {1}
  have hW : IsOpen W := (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  set G : ℂ → ℂ := fun t => a ^ (-t) / 2 + a ^ (1 - t) / (t - 1) +
    (∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℂ) / (2 * k)! * pochhammer t (2 * k - 1) *
      a ^ (1 - t - 2 * k)) +
    1 / Gamma t * ∫ x in Ioi (0 : ℝ), bernoulliRemainderIntegrand n a t x
  have hF : DifferentiableOn ℂ (fun t => hurwitzZetaComplex t a) W := fun t ht =>
    (differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' ht.2 han).differentiableWithinAt
  have hG : DifferentiableOn ℂ G W := by
    intro t ht
    have ht1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht.2
    have hI := (differentiableOn_integral_bernoulliRemainderIntegrand n ha t ht.1).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds ht.1)
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add ?_ ?_) ?_) ?_
    · exact ((differentiableAt_id.neg).const_cpow (Or.inl ha0)).div_const _
    · exact (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl ha0)).div
        (differentiableAt_id.sub_const 1) ht1
    · refine DifferentiableAt.fun_sum fun k _ => ?_
      refine ((differentiableAt_const _).mul ?_).mul
        ((((differentiableAt_const _).sub differentiableAt_id).sub_const _).const_cpow
          (Or.inl ha0))
      exact (Polynomial.differentiable _).differentiableAt
    · have h1 : DifferentiableAt ℂ (fun t : ℂ => 1 / Gamma t) t := by
        simpa only [one_div] using Complex.differentiable_one_div_Gamma t
      exact h1.mul hI
  have heq : EqOn (fun t => hurwitzZetaComplex t a) G W := by
    refine (hF.analyticOnNhd hW).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hW)
      (isPreconnected_re_gt_diff_one (by linarith)) (show (2 : ℂ) ∈ W by
        refine ⟨?_, by norm_num⟩
        show -(2 * n + 1 : ℝ) < (2 : ℂ).re
        simp only [re_ofNat]; linarith) ?_
    have hopen : IsOpen {t : ℂ | 1 < t.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with t ht
    have hΓ : Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    simp only [G, integral_bernoulliRemainderIntegrand_of_one_lt_re n ha ht]
    field_simp
    ring
  exact heq ⟨hs0, hs⟩

/-- DLMF 25.5.7 for all `n`, `Re s > -(2n+1)`, `s ≠ 1`: the case `a = 1` of 25.11.28;
stronger than DLMF, which assumes `n ≥ 1`. -/
@[dlmf 25.5.E7 "stronger than DLMF: n = 0 allowed"]
theorem riemannZeta_eq_half_add_bernoulli_integral' {s : ℂ} {n : ℕ}
    (hs : -(2 * n + 1 : ℝ) < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (1 / (cexp x - 1) - 1 / x + 1 / 2 -
        ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
          (x : ℂ) ^ (2 * m - 1)) * (x : ℂ) ^ (s - 1) / cexp x) (Ioi 0) ∧
      riemannZeta s = 1 / 2 + 1 / (s - 1) +
        ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
          (ascPochhammer ℂ (2 * m - 1)).eval s +
        1 / Gamma s * ∫ x in Ioi (0 : ℝ), (1 / (cexp x - 1) - 1 / x + 1 / 2 -
          ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
            (x : ℂ) ^ (2 * m - 1)) * (x : ℂ) ^ (s - 1) / cexp x := by
  have hI := integrableOn_bernoulliRemainderIntegrand n (a := 1) (by norm_num) hs
  have hv := hurwitzZetaComplex_eq_integral_bernoulli_sub n (a := 1) hs1 hs (by norm_num)
  have heq : EqOn (fun x : ℝ => (1 / (cexp x - 1) - 1 / x + 1 / 2 -
      ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
        (x : ℂ) ^ (2 * m - 1)) * (x : ℂ) ^ (s - 1) / cexp x)
      (bernoulliRemainderIntegrand n 1 s) (Ioi 0) := by
    intro x _
    simp only [bernoulliRemainderIntegrand, bernoulliRemainder, one_mul, Complex.exp_neg]
    push_cast
    rw [div_eq_mul_inv]
  refine ⟨hI.congr_fun heq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, ← hurwitzZetaComplex_one hs1]
  change _ = _ + _ + _ + 1 / Gamma s * ∫ x in Ioi (0 : ℝ), ((1 / (Real.exp x - 1) - 1 / x + 1 / 2 -
      ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℝ) / (2 * k)! * x ^ (2 * k - 1) : ℝ) : ℂ) *
      (x : ℂ) ^ (s - 1) * cexp (-(1 * x))
  rw [hv]
  simp only [one_cpow]
  ring_nf

/-- DLMF 25.5.7: for `n ≥ 1`, `Re s > -(2n+1)`, `s ≠ 1`,
`ζ(s) = ½ + 1/(s-1) + ∑_{m=1}^{n} (B_{2m}/(2m)!) (s)_{2m-1}
  + Γ(s)⁻¹ ∫₀^∞ (1/(eˣ-1) - 1/x + ½ - ∑_{m=1}^{n} (B_{2m}/(2m)!) x^{2m-1}) x^{s-1} e^{-x} dx`,
with the Pochhammer symbol `(s)_k = ascPochhammer ℂ k` evaluated at `s`. -/
@[dlmf 25.5.E7]
theorem riemannZeta_eq_half_add_bernoulli_integral {s : ℂ} {n : ℕ} (_hn : 1 ≤ n)
    (hs : -(2 * n + 1 : ℝ) < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (1 / (cexp x - 1) - 1 / x + 1 / 2 -
        ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
          (x : ℂ) ^ (2 * m - 1)) * (x : ℂ) ^ (s - 1) / cexp x) (Ioi 0) ∧
      riemannZeta s = 1 / 2 + 1 / (s - 1) +
        ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
          (ascPochhammer ℂ (2 * m - 1)).eval s +
        1 / Gamma s * ∫ x in Ioi (0 : ℝ), (1 / (cexp x - 1) - 1 / x + 1 / 2 -
          ∑ m ∈ Finset.Icc (1 : ℕ) n, (bernoulli (2 * m) : ℂ) / (2 * m).factorial *
            (x : ℂ) ^ (2 * m - 1)) * (x : ℂ) ^ (s - 1) / cexp x :=
  riemannZeta_eq_half_add_bernoulli_integral' hs hs1

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

/-! ### §25.11(viii) Further integral representations -/

/-- Holomorphy in `s` of `∫_0^∞ x^{s-1} e^{-ax}/(1 + e^{-x}) dx` on `Re s > 0`. -/
private lemma differentiableOn_lerchIntegral_neg_one {a : ℂ} (ha : 0 < a.re) :
    DifferentiableOn ℂ (fun s => lerchIntegral s a (-1)) {s : ℂ | 0 < s.re} := by
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
    · have h1 := integrableOn_rpow_mul_exp_neg (σ := s₀.re - δ) (by simp only [δ]; linarith) ha
      have h2 := integrableOn_rpow_mul_exp_neg (σ := s₀.re + δ) (by simp only [δ]; linarith) ha
      exact (h1.add h2).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring)
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have := abs_re_le_norm (s - s₀)
      simp only [sub_re] at this
      have h1 : s₀.re - δ ≤ s.re := by linarith [neg_abs_le (s.re - s₀.re)]
      have h2 : s.re ≤ s₀.re + δ := by linarith [le_abs_self (s.re - s₀.re)]
      rw [norm_div, norm_cpow_mul_exp_neg hx]
      have hd := hden x
      have hp : 0 ≤ x ^ (s.re - 1) * Real.exp (-(a.re * x)) :=
        mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le
      calc x ^ (s.re - 1) * Real.exp (-(a.re * x)) / ‖1 - (-1) * cexp (-(x : ℂ))‖
          ≤ x ^ (s.re - 1) * Real.exp (-(a.re * x)) := div_le_self hp hd
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have := rpow_neg_sub_one_le_add (x := x) (σ := -s.re) (σ₀ := -(s₀.re + δ))
            (R := -(s₀.re - δ)) hx (by linarith) (by linarith)
          simp only [neg_neg] at this
          linarith

/-- The alternating Hurwitz integral (DLMF 25.11.35, integral form) for `Re a > 0`,
`Re s > 0`, `s ≠ 1`:
`(1/Γ(s)) ∫_0^∞ x^{s-1} e^{-ax}/(1+e^{-x}) dx = 2^{-s}(ζ(s,a/2) - ζ(s,(1+a)/2))`. -/
private lemma one_div_Gamma_mul_lerchIntegral_neg_one {s a : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1)
    (ha : 0 < a.re) :
    1 / Gamma s * lerchIntegral s a (-1) =
      2 ^ (-s) * (hurwitzZetaComplex s (a / 2) - hurwitzZetaComplex s ((1 + a) / 2)) := by
  have ha2 : 0 < (a / 2).re := by simp; linarith
  have ha3 : 0 < ((1 + a) / 2).re := by simp; linarith
  set W : Set ℂ := {t : ℂ | 0 < t.re} \ {1}
  have hW : IsOpen W := (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  have hF : DifferentiableOn ℂ (fun t => 1 / Gamma t * lerchIntegral t a (-1)) W := by
    intro t ht
    have hI := ((differentiableOn_lerchIntegral_neg_one ha) t ht.1).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds ht.1)
    have h1 : DifferentiableAt ℂ (fun t : ℂ => 1 / Gamma t) t := by
      simpa only [one_div] using Complex.differentiable_one_div_Gamma t
    exact (h1.mul hI).differentiableWithinAt
  have hG : DifferentiableOn ℂ (fun t => (2 : ℂ) ^ (-t) * (hurwitzZetaComplex t (a / 2) -
      hurwitzZetaComplex t ((1 + a) / 2))) W := by
    intro t ht
    exact (((differentiableAt_id.neg).const_cpow (Or.inl two_ne_zero)).mul
      ((differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' ht.2
          (Complex.add_natCast_ne_zero_of_re_pos ha2)).sub
        (differentiableAt_hurwitzZetaComplex_of_add_natCast_ne_zero' ht.2
          (Complex.add_natCast_ne_zero_of_re_pos ha3)))).differentiableWithinAt
  refine (hF.analyticOnNhd hW).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hW)
    (isPreconnected_re_gt_diff_one (by norm_num)) (show (2 : ℂ) ∈ W by norm_num [W]) ?_
    ⟨hs0, hs1⟩
  have hopen : IsOpen {t : ℂ | 1 < t.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with t ht
  have hL := hasSum_lerch_lerchIntegral (z := -1) (by linarith) ha (Or.inr ⟨by simp, ht⟩)
  have hne : ∀ b : ℂ, 0 < b.re → ∀ m : ℕ, b ≠ -m := fun b hb m h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have he := (hasSum_hurwitzZetaComplex ht (hne _ ha2)).mul_left ((2 : ℂ) ^ (-t))
  have ho := ((hasSum_hurwitzZetaComplex ht (hne _ ha3)).mul_left ((2 : ℂ) ^ (-t))).neg
  have hsplit : ∀ (m : ℕ) (b : ℂ), 0 < b.re →
      (2 : ℂ) ^ (-t) * (1 / ((m : ℂ) + b) ^ t) = 1 / (2 * (m : ℂ) + 2 * b) ^ t := by
    intro m b hb
    have hw : (m : ℂ) + b ≠ 0 := by rw [add_comm]; exact Complex.add_natCast_ne_zero_of_re_pos hb m
    rw [show 2 * (m : ℂ) + 2 * b = ((2 : ℝ) : ℂ) * ((m : ℂ) + b) by push_cast; ring,
      ofReal_mul_cpow_of_pos two_pos hw, cpow_neg]
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
      2 ^ (-s) * lerchIntegral s a' (-1) := by
    have hc := integral_comp_mul_left_Ioi (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-(a' * u)) /
      (1 - (-1) * cexp (-(u : ℂ)))) 0 (b := 2) two_pos
    rw [mul_zero] at hc
    rw [lerchIntegral, ← smul_eq_mul (a := (2 : ℂ) ^ (-s)), show (2 : ℂ) ^ (-s) =
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
  rw [hsub, mul_left_comm, one_div_Gamma_mul_lerchIntegral_neg_one hs0 hs1 ha', ← mul_assoc]
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

/-- `(2w)^t = 2^t w^t` for `t ≠ 0`. -/
private lemma two_mul_cpow_of_ne_zero (w : ℂ) {t : ℂ} (ht : t ≠ 0) :
    (2 * w) ^ t = 2 ^ t * w ^ t := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [zero_cpow ht]
  · have := ofReal_mul_cpow_of_pos (r := 2) (by norm_num) hw t
    simpa using this

/-- Consecutive differences `(z+N+1)^{1-s} - (z+N)^{1-s} → 0` for `Re s > 0`, `s ≠ 1`. -/
private lemma tendsto_add_natCast_cpow_one_sub_sub {s : ℂ} (hs : s ≠ 1) (hs0 : 0 < s.re)
    (z : ℂ) :
    Tendsto (fun N : ℕ => (z + N + 1) ^ (1 - s) - (z + N) ^ (1 - s)) atTop (𝓝 0) := by
  have hE := tendsto_eulerMaclaurinSeq_hurwitzZetaComplex (M := 0) (z := z) hs
    (by simpa using hs0)
  have hD : Tendsto (fun N : ℕ => eulerMaclaurinSeq 0 s z (N + 1) - eulerMaclaurinSeq 0 s z N)
      atTop (𝓝 0) := by
    simpa using (hE.comp (tendsto_add_atTop_nat 1)).sub hE
  have hneg : (-s).re < 0 := by simpa using hs0
  have h0 := tendsto_add_natCast_cpow_atTop z hneg
  have h1 : Tendsto (fun N : ℕ => (z + N + 1) ^ (-s)) atTop (𝓝 0) := by
    simpa [Function.comp_def, add_assoc] using h0.comp (tendsto_add_atTop_nat 1)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hlim := ((hD.sub (h0.add ((h1.sub h0).div_const 2))).const_mul (s - 1))
  simp only [sub_zero, add_zero, mul_zero, zero_div] at hlim
  refine hlim.congr fun N => ?_
  simp only [eulerMaclaurinSeq, eulerMaclaurinTail, Finset.range_zero, Finset.sum_empty,
    add_zero, Finset.sum_range_succ]
  push_cast
  field_simp
  ring_nf

/-- **Alternating Hurwitz series** (DLMF 25.11.35), series form, for every complex `a` and
`Re s > 0`, `s ≠ 1`: `∑_{n≥0} (-1)^n/(n+a)^s = 2^{-s}(ζ(s, a/2) - ζ(s, (1+a)/2))` as a limit of
partial sums (a term with `n + a = 0` is read as `0`, as in `hurwitzZetaComplex`). Stronger than
DLMF, which assumes `Re a > 0`, or `Re a = 0`, `Im a ≠ 0` and `Re s < 1`. -/
@[dlmf 25.11.E35 "stronger than DLMF: every complex a, Re s > 0"]
theorem tendsto_alternating_hurwitz' {s a : ℂ} (hs1 : s ≠ 1) (hs0 : 0 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n / ((n : ℂ) + a) ^ s) atTop
      (𝓝 (2 ^ (-s) * (hurwitzZetaComplex s (a / 2) - hurwitzZetaComplex s ((1 + a) / 2)))) := by
  have hs : s ≠ 0 := fun h => by simp [h] at hs0
  have hns : -s ≠ 0 := neg_ne_zero.mpr hs
  have hs1' : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  set T : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n / ((n : ℂ) + a) ^ s
  -- the even partial sums
  have hT2 : ∀ N : ℕ, T (2 * N) = ∑ m ∈ Finset.range N,
      (2 ^ (-s) * (a / 2 + m) ^ (-s) - 2 ^ (-s) * ((1 + a) / 2 + m) ^ (-s)) := by
    intro N
    induction N with
    | zero => simp [T]
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring]
      simp only [T] at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have e1 : ((2 * N : ℕ) : ℂ) + a = 2 * (a / 2 + N) := by push_cast; ring
      have e2 : ((2 * N + 1 : ℕ) : ℂ) + a = 2 * ((1 + a) / 2 + N) := by push_cast; ring
      rw [e1, e2, div_eq_mul_inv ((-1 : ℂ) ^ (2 * N)), div_eq_mul_inv ((-1 : ℂ) ^ (2 * N + 1)),
        ← cpow_neg, ← cpow_neg,
        two_mul_cpow_of_ne_zero _ hns, two_mul_cpow_of_ne_zero _ hns, pow_succ, pow_mul]
      norm_num
      ring
  have hns' : (-s).re < 0 := by simpa using hs0
  have hE := ((tendsto_eulerMaclaurinSeq_hurwitzZetaComplex (M := 0) (z := a / 2) hs1
    (by simpa using hs0)).sub (tendsto_eulerMaclaurinSeq_hurwitzZetaComplex (M := 0)
      (z := (1 + a) / 2) hs1 (by simpa using hs0))).const_mul (2 ^ (-s))
  have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  have hA := (tendsto_add_natCast_cpow_one_sub_sub hs1 hs0 a).comp h2N
  have hB1 := tendsto_add_natCast_cpow_atTop (a / 2) hns'
  have hB2 := tendsto_add_natCast_cpow_atTop ((1 + a) / 2) hns'
  have hR : Tendsto (fun N : ℕ => -((((a + ((2 * N : ℕ) : ℂ) + 1) ^ (1 - s) -
      (a + ((2 * N : ℕ) : ℂ)) ^ (1 - s))) / (2 * (s - 1))) + 2 ^ (-s) *
      ((a / 2 + N) ^ (-s) - ((1 + a) / 2 + N) ^ (-s)) / 2) atTop (𝓝 0) := by
    simpa using ((hA.div_const (2 * (s - 1))).neg.add (((hB1.sub hB2).const_mul
      (2 ^ (-s))).div_const 2))
  have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hEven : Tendsto (fun N : ℕ => T (2 * N)) atTop
      (𝓝 (2 ^ (-s) * (hurwitzZetaComplex s (a / 2) - hurwitzZetaComplex s ((1 + a) / 2)))) := by
    have := hE.sub hR
    rw [sub_zero] at this
    refine this.congr fun N => ?_
    rw [hT2 N]
    simp only [eulerMaclaurinSeq, eulerMaclaurinTail, Finset.range_zero,
      Finset.sum_empty, add_zero]
    have e1 : a + ((2 * N : ℕ) : ℂ) = 2 * (a / 2 + N) := by push_cast; ring
    have e2 : a + ((2 * N : ℕ) : ℂ) + 1 = 2 * ((1 + a) / 2 + N) := by push_cast; ring
    have h21 : (2 : ℂ) ^ (1 - s) = 2 * 2 ^ (-s) := by
      rw [sub_eq_add_neg, cpow_add _ _ (by norm_num), cpow_one]
    rw [e2, e1, two_mul_cpow_of_ne_zero _ hs1', two_mul_cpow_of_ne_zero _ hs1', h21,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    field_simp
    ring
  have hsplit : ∀ N : ℕ, T N = T (2 * (N / 2)) +
      (if N % 2 = 1 then (((2 * (N / 2) : ℕ) : ℂ) + a) ^ (-s) else 0) := by
    intro N
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
    · simp
    · have h1 : (2 * k + 1) / 2 = k := by omega
      have h2 : (2 * k + 1) % 2 = 1 := by omega
      simp only [h1, h2, ite_true, T, Finset.sum_range_succ, pow_mul]
      rw [cpow_neg]
      norm_num [div_eq_mul_inv]
  have hhalf : Tendsto (fun N : ℕ => 2 * (N / 2)) atTop atTop :=
    h2N.comp (Nat.tendsto_div_const_atTop (by norm_num))
  have hC : Tendsto (fun N : ℕ => (if N % 2 = 1 then (((2 * (N / 2) : ℕ) : ℂ) + a) ^ (-s)
      else 0)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun N : ℕ => ‖(a + ((2 * (N / 2) : ℕ) : ℂ)) ^ (-s)‖)
      (fun N => ?_) ?_
    · split_ifs
      · rw [add_comm]
      · simp
    · simpa using ((tendsto_add_natCast_cpow_atTop a hns').comp hhalf).norm
  have := (hEven.comp (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))).add hC
  rw [add_zero] at this
  exact this.congr fun N => (hsplit N).symm

/-- **Alternating Hurwitz series** (DLMF 25.11.35), series form: for `Re a > 0`, `Re s > 0`, or
`Re a = 0`, `Im a ≠ 0`, `0 < Re s < 1` (and `s ≠ 1`, a removable singularity of the right side),
`∑_{n≥0} (-1)^n/(n+a)^s = 2^{-s}(ζ(s, a/2) - ζ(s, (1+a)/2))`, as a limit of partial sums. -/
@[dlmf 25.11.E35]
theorem tendsto_alternating_hurwitz {s a : ℂ} (hs1 : s ≠ 1)
    (h : (0 < a.re ∧ 0 < s.re) ∨ (a.re = 0 ∧ a.im ≠ 0 ∧ 0 < s.re ∧ s.re < 1)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n / ((n : ℂ) + a) ^ s) atTop
      (𝓝 (2 ^ (-s) * (hurwitzZetaComplex s (a / 2) - hurwitzZetaComplex s ((1 + a) / 2)))) :=
  tendsto_alternating_hurwitz' hs1 (by rcases h with h | h <;> [exact h.2; exact h.2.2.1])

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

open Finset in
/-- `∏_{j<n} (z - e^{(2j+1)πi/n}) = zⁿ + 1`. -/
private lemma prod_sub_exp_odd_mul_pi_I_div {n : ℕ} (hn : 0 < n) (z : ℂ) :
    ∏ j ∈ range n, (z - cexp ((2 * j + 1) * π * I / n)) = z ^ n + 1 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  have hα : cexp (π * I / n) ^ n = -1 := by
    rw [← Complex.exp_nat_mul, show (n : ℂ) * (π * I / n) = π * I by field_simp,
      Complex.exp_pi_mul_I]
  have h := congrArg (Polynomial.eval z) (X_pow_sub_C_eq_prod hζ hn hα)
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod] at h
  rw [sub_neg_eq_add] at h
  rw [h]
  refine prod_congr rfl fun j _ => ?_
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2
  field_simp

open Finset in
/-- `∑_{j<n} e^{(2j+1)πi/n} = 0` for `n ≥ 2`. -/
private lemma sum_exp_odd_mul_pi_I_div {n : ℕ} (hn : 2 ≤ n) :
    ∑ j ∈ range n, cexp ((2 * j + 1) * π * I / n) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hζ := Complex.isPrimitiveRoot_exp n (by omega)
  have h := hζ.geom_sum_eq_zero (by omega)
  have : ∀ j : ℕ, cexp ((2 * j + 1) * π * I / n) = cexp (2 * π * I / n) ^ j * cexp (π * I / n) := by
    intro j
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    field_simp
  simp only [this, ← sum_mul, h, zero_mul]

open Finset in
/-- **Logarithmic sum, exponentiated** (DLMF 25.11.37) for complex `Re a > 1`, `n = 2, 3, …`:
`exp(∑_{k≥1} ((-1)^k/k) ζ(nk, a)) = Γ(a)^{-n} ∏_{j=0}^{n-1} Γ(a - e^{(2j+1)πi/n})`
(branch-free form of the printed identity, whose logarithms must be read as the analytic branch of
`ln Γ`). -/
@[dlmf 25.11.E37]
theorem exp_tsum_hurwitzZeta_eq_prod_gamma {n : ℕ} (hn : 2 ≤ n) {a : ℂ} (ha : 1 < a.re) :
    Summable (fun k : ℕ => (-1) ^ (k + 1) / (k + 1 : ℂ) * hurwitzZetaComplex (n * (k + 1)) a) ∧
    cexp (∑' k : ℕ, (-1) ^ (k + 1) / (k + 1 : ℂ) * hurwitzZetaComplex (n * (k + 1)) a) =
      (∏ j ∈ Finset.range n, Gamma (a - cexp ((2 * j + 1) * π * I / n))) / Gamma a ^ n := by
  set ω : ℕ → ℂ := fun j => cexp ((2 * j + 1) * π * I / n) with hω
  set x : ℕ → ℂ := fun m => 1 / ((m : ℂ) + a) ^ n with hx
  have hre : ∀ m : ℕ, ((m : ℂ) + a).re = m + a.re := fun m => by simp
  have hnorm : ∀ m : ℕ, (m : ℝ) + a.re ≤ ‖(m : ℂ) + a‖ := fun m =>
    (hre m) ▸ Complex.re_le_norm _
  have hpos : ∀ m : ℕ, (1 : ℝ) < m + a.re := fun m => by linarith [m.cast_nonneg (α := ℝ)]
  have hma0 : ∀ m : ℕ, (m : ℂ) + a ≠ 0 := fun m h => by
    have := hre m; rw [h] at this; simp at this; linarith [hpos m]
  have hxle : ∀ m : ℕ, ‖x m‖ ≤ 1 / ((m : ℝ) + a.re) ^ n := by
    intro m
    simp only [x, norm_div, norm_one, norm_pow]
    exact one_div_le_one_div_of_le (pow_pos (by linarith [hpos m]) n)
      (pow_le_pow_left₀ (by linarith [hpos m]) (hnorm m) n)
  set r : ℝ := 1 / a.re ^ n with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr_def, div_lt_one (by positivity)]
    exact one_lt_pow₀ ha (by omega)
  have hxr : ∀ m : ℕ, ‖x m‖ ≤ r := fun m => (hxle m).trans (by
    rw [hr_def]; gcongr; linarith [m.cast_nonneg (α := ℝ)])
  have hxs : Summable fun m => ‖x m‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => (hxle m).trans ?_)
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < n)))
    push_cast
    gcongr
  -- the double series
  set u : ℕ × ℕ → ℂ := fun p => (-1) ^ (p.2 + 1) / (p.2 + 1 : ℂ) * x p.1 ^ (p.2 + 1) with hu_def
  have hu_norm : ∀ p, ‖u p‖ ≤ ‖x p.1‖ * r ^ p.2 := by
    intro ⟨m, k⟩
    have h1 : ‖(k : ℂ) + 1‖ = k + 1 := by norm_cast
    have e : ‖u (m, k)‖ = 1 / ((k : ℝ) + 1) * (‖x m‖ ^ k * ‖x m‖) := by
      simp only [u, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, h1, pow_succ]
      ring
    rw [e]
    have h2 : ‖x m‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg _) (hxr m) k
    have h3 : (1 : ℝ) / (k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
    calc 1 / ((k : ℝ) + 1) * (‖x m‖ ^ k * ‖x m‖) ≤ 1 * (r ^ k * ‖x m‖) := by
          gcongr
      _ = ‖x m‖ * r ^ k := by ring
  have hus : Summable u := Summable.of_norm_bounded
    (hxs.mul_of_nonneg (summable_geometric_of_lt_one hr0 hr1) (fun _ => norm_nonneg _)
      (fun _ => by positivity)) hu_norm
  have hS := hus.hasSum
  have hzeta : ∀ k : ℕ, HasSum (fun m => u (m, k))
      ((-1) ^ (k + 1) / (k + 1 : ℂ) * hurwitzZetaComplex (n * (k + 1)) a) := by
    intro k
    have hs : 1 < ((n : ℂ) * (k + 1)).re := by
      simp
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [k.cast_nonneg (α := ℝ)]
    refine ((hasSum_hurwitzZetaComplex' hs).mul_left ((-1) ^ (k + 1) / (k + 1 : ℂ))).congr_fun ?_
    intro m
    simp only [u, x]
    rw [show (n : ℂ) * (k + 1) = ((n * (k + 1) : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
      pow_mul, one_div_pow]
  have hlog : ∀ m : ℕ, HasSum (fun k => u (m, k)) (-Complex.log (1 + x m)) := by
    intro m
    have hx1 : ‖x m‖ < 1 := (hxr m).trans_lt hr1
    have h := (hasSum_nat_add_iff' 1).mpr (hasSum_taylorSeries_log hx1)
    simp only [range_one, sum_singleton, pow_zero, Nat.cast_zero, div_zero, sub_zero] at h
    refine h.neg.congr_fun fun k => ?_
    simp only [u]
    push_cast
    ring
  have hv : HasSum (u ∘ Equiv.prodComm ℕ ℕ) (∑' p, u p) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hS
  have hK := hv.prod_fiberwise fun k => hzeta k
  have hM := hS.prod_fiberwise hlog
  refine ⟨hK.summable, ?_⟩
  rw [hK.tsum_eq]
  set T := ∑' p, u p
  -- the exponential of the partial sums
  have hE := ((continuous_exp.tendsto T).comp hM.tendsto_sum_nat)
  have h1x : ∀ m : ℕ, 1 + x m ≠ 0 := fun m h => by
    have := (hxr m).trans_lt hr1
    rw [show x m = -1 by linear_combination h] at this
    simp at this
  have hEq : ∀ N : ℕ, (cexp ∘ fun N => ∑ m ∈ range N, -Complex.log (1 + x m)) N =
      ∏ m ∈ range N, (1 + x m)⁻¹ := by
    intro N
    simp only [Function.comp_apply, Complex.exp_sum, Complex.exp_neg,
      Complex.exp_log (h1x _)]
  simp only [funext hEq] at hE
  -- Euler's limit formula
  have hΓ : Tendsto (fun N => GammaSeq a N ^ n * ∏ m ∈ range (N + 1), (1 + x m)⁻¹) atTop
      (𝓝 (Gamma a ^ n * cexp T)) :=
    ((GammaSeq_tendsto_Gamma a).pow n).mul (hE.comp (tendsto_add_atTop_nat 1))
  have hΓω : Tendsto (fun N => ∏ j ∈ range n, GammaSeq (a - ω j) N) atTop
      (𝓝 (∏ j ∈ range n, Gamma (a - ω j))) :=
    tendsto_finsetProd _ fun j _ => GammaSeq_tendsto_Gamma _
  have hy1 : ∀ m : ℕ, ((m : ℂ) + a) ^ n + 1 ≠ 0 := by
    intro m h
    apply h1x m
    have h2 := pow_ne_zero n (hma0 m)
    simp only [x]
    field_simp
    linear_combination h
  have hid : ∀ N : ℕ, 1 ≤ N → ∏ j ∈ range n, GammaSeq (a - ω j) N =
      GammaSeq a N ^ n * ∏ m ∈ range (N + 1), (1 + x m)⁻¹ := by
    intro N hN
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hcp : ∏ j ∈ range n, (N : ℂ) ^ (a - ω j) = ((N : ℂ) ^ a) ^ n := by
      simp only [cpow_def_of_ne_zero hN0, ← Complex.exp_sum, ← Complex.exp_nat_mul, ← mul_sum,
        sum_sub_distrib, sum_const, card_range, ω, sum_exp_odd_mul_pi_I_div hn]
      congr 1
      simp only [nsmul_eq_mul]
      ring
    have hroot : ∏ j ∈ range n, ∏ m ∈ range (N + 1), (a - ω j + m) =
        ∏ m ∈ range (N + 1), (((m : ℂ) + a) ^ n + 1) := by
      rw [Finset.prod_comm]
      refine prod_congr rfl fun m _ => ?_
      rw [← prod_sub_exp_odd_mul_pi_I_div (by omega)]
      exact prod_congr rfl fun j _ => by simp only [ω]; ring
    have hinv : ∀ m : ℕ, (1 + x m)⁻¹ = ((m : ℂ) + a) ^ n / (((m : ℂ) + a) ^ n + 1) := by
      intro m
      have h2 := pow_ne_zero n (hma0 m)
      have h3 := hy1 m
      simp only [x]
      field_simp
    have hcomm : ∏ m ∈ range (N + 1), ((m : ℂ) + a) = ∏ m ∈ range (N + 1), (a + m) :=
      prod_congr rfl fun _ _ => add_comm _ _
    have hP : ∏ m ∈ range (N + 1), (a + m) ≠ 0 := by
      rw [← hcomm]; exact prod_ne_zero_iff.mpr fun m _ => hma0 m
    have hQ : ∏ m ∈ range (N + 1), (((m : ℂ) + a) ^ n + 1) ≠ 0 :=
      prod_ne_zero_iff.mpr fun m _ => hy1 m
    simp only [GammaSeq, hinv, div_pow, mul_pow, prod_div_distrib, prod_mul_distrib, prod_const,
      card_range, hcp, hroot, Finset.prod_pow, hcomm]
    field_simp
  have hlim := tendsto_nhds_unique (hΓω.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN; exact hid N hN)) hΓ
  have hΓa : Gamma a ^ n ≠ 0 := pow_ne_zero _ (Complex.Gamma_ne_zero fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [m.cast_nonneg (α := ℝ)])
  rw [hlim]
  field_simp

/-- **Logarithmic sum** (DLMF 25.11.37) for real `a > 1`, `n = 2, 3, …`, principal logarithms:
`∑_{k≥1} ((-1)^k/k) ζ(nk, a) = -n ln Γ(a) + ln ∏_{j=0}^{n-1} Γ(a - e^{(2j+1)πi/n})`. -/
@[dlmf 25.11.E37]
theorem hasSum_hurwitzZeta_log_gamma {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 1 < a) :
    HasSum (fun k : ℕ => (-1) ^ (k + 1) / (k + 1 : ℂ) * hurwitzZetaComplex (n * (k + 1)) a)
      (-n * Real.log (Real.Gamma a) +
        Complex.log (∏ j ∈ Finset.range n, Gamma (a - cexp ((2 * j + 1) * π * I / n)))) := by
  obtain ⟨hsum, hexp⟩ := exp_tsum_hurwitzZeta_eq_prod_gamma hn (a := a) (by simpa using ha)
  set T := ∑' k : ℕ, (-1) ^ (k + 1) / (k + 1 : ℂ) * hurwitzZetaComplex (n * (k + 1)) a
  have hzr : ∀ k : ℕ, (hurwitzZetaComplex (n * (k + 1)) a).im = 0 := by
    intro k
    have hs : 1 < ((n : ℂ) * (k + 1)).re := by
      simp
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [k.cast_nonneg (α := ℝ)]
    have h := (hasSum_hurwitzZetaComplex' (a := (a : ℂ)) hs).mapL Complex.imCLM
    have h0 : HasSum (fun m : ℕ => Complex.imCLM (1 / ((m : ℂ) + a) ^ ((n : ℂ) * (k + 1)))) 0 := by
      convert hasSum_zero with m
      simp only [Complex.imCLM_apply]
      rw [show (n : ℂ) * (k + 1) = ((n * (k + 1) : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
        show (m : ℂ) + a = ((m + a : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_pow,
        ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_im]
    simpa using h.unique h0
  have hTim : T.im = 0 := by
    have h := hsum.hasSum.mapL Complex.imCLM
    refine (h.unique ?_)
    convert hasSum_zero with k
    simp only [Complex.imCLM_apply]
    rw [show (-1 : ℂ) ^ (k + 1) / (k + 1 : ℂ) = (((-1) ^ (k + 1) / (k + 1) : ℝ) : ℂ) by
      push_cast; ring, Complex.im_ofReal_mul, hzr, mul_zero]
  have hT : T = (T.re : ℂ) := Complex.ext (by simp) (by simp [hTim])
  have hΓ : Gamma (a : ℂ) = (Real.Gamma a : ℂ) := Complex.Gamma_ofReal a
  have hΓpos : 0 < Real.Gamma a := Real.Gamma_pos_of_pos (by linarith)
  have hprod : ∏ j ∈ Finset.range n, Gamma (a - cexp ((2 * j + 1) * π * I / n)) =
      ((Real.Gamma a ^ n * Real.exp T.re : ℝ) : ℂ) := by
    have hΓ0 : Gamma (a : ℂ) ^ n ≠ 0 := by rw [hΓ]; exact_mod_cast (pow_pos hΓpos n).ne'
    rw [eq_div_iff hΓ0] at hexp
    rw [← hexp, hΓ, show cexp T = ((Real.exp T.re : ℝ) : ℂ) by rw [Complex.ofReal_exp, ← hT]]
    push_cast
    ring
  rw [hprod, ← Complex.ofReal_log (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_pow]
  convert hsum.hasSum using 1
  push_cast
  rw [show ((T.re : ℝ) : ℂ) = T from hT.symm]
  ring

/-- `‖a‖ ≤ ‖a + m‖` for `Re a > 0` and `m ≥ 0`. -/
private lemma norm_le_norm_add_natCast {a : ℂ} (ha : 0 < a.re) (m : ℕ) : ‖a‖ ≤ ‖a + m‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    normSq_apply, normSq_apply]
  simp only [add_re, natCast_re, add_im, natCast_im, add_zero]
  nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- `iteratedDeriv k ψ^{(n)} = ψ^{(n+k)}`. -/
private lemma iteratedDeriv_polygamma (n k : ℕ) :
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
    linarith [norm_le_norm_add_natCast ha m]
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
  simp only [iteratedDeriv_polygamma, sub_zero, smul_eq_mul] at hT
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
      hurwitzZetaComplex_eq_hurwitzZeta (by norm_num) (by norm_num) hs,
      show 1 + (k + 1) = k + 2 by ring, Nat.choose_succ_self_right]
    push_cast
    simp only [one_div, inv_pow]
    ring_nf
  · simp
    ring_nf

end DLMF.Zeta

end
