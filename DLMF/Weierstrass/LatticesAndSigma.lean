/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic.Functions
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Normed.Module.Connected
public import DLMFMathlib.NumberTheory.ModularForms.P3wJSurjective

/-!
# Weierstrass lattices and sigma products

Lattices, half-periods, zeta and sigma definitions and the convergent Weierstrass sigma product.

Source references and common attribution are retained in
`DLMF.Weierstrass.Basic`.
-/

@[expose] public section

open Complex PeriodPair

open scoped Real

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF §23.2(i): `𝕃 = {2mω₁ + 2nω₃ : m, n ∈ ℤ}`. -/
@[dlmf 23.2.i]
theorem mem_lattice_iff {z : ℂ} : z ∈ H.lattice ↔ ∃ m n : ℤ, z = 2 * m * H.ω₁ + 2 * n * H.ω₃ := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by simp; ring⟩
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by simp; ring⟩

/-- Formula under the stated hypotheses: `2 * H.ω₁ ∈ H.lattice`. -/
theorem two_mul_ω₁_mem : 2 * H.ω₁ ∈ H.lattice := H.periodPair.ω₁_mem_lattice
/-- Formula under the stated hypotheses: `2 * H.ω₃ ∈ H.lattice`. -/
theorem two_mul_ω₃_mem : 2 * H.ω₃ ∈ H.lattice := H.periodPair.ω₂_mem_lattice
/-- Formula under the stated hypotheses: `2 * H.ω₂ ∈ H.lattice`. -/
theorem two_mul_ω₂_mem : 2 * H.ω₂ ∈ H.lattice := by
  have : 2 * H.ω₂ = -(2 * H.ω₁) - 2 * H.ω₃ := by simp [ω₂]; ring
  rw [this]
  exact sub_mem (neg_mem H.two_mul_ω₁_mem) H.two_mul_ω₃_mem

/-- DLMF §23.2(i): with `ω₂` as in 23.2.1, `2ω₂, 2ω₃` are also generators of `𝕃`. -/
@[dlmf 23.2.i]
theorem span_two_ω₂_two_ω₃ :
    Submodule.span ℤ {2 * H.ω₂, 2 * H.ω₃} = H.lattice := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by
      rintro x (rfl | rfl)
      exacts [H.two_mul_ω₂_mem, H.two_mul_ω₃_mem])
  · refine Submodule.span_le.mpr ?_
    rintro x (rfl | rfl)
    · have : H.periodPair.ω₁ = -(2 * H.ω₂) - 2 * H.ω₃ := by simp [ω₂]; ring
      rw [this]
      exact sub_mem (neg_mem (Submodule.subset_span (by simp)))
        (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (by simp)

/-- DLMF §23.2(i): `2ω₂, 2ω₁` are also generators of `𝕃`. -/
@[dlmf 23.2.i]
theorem span_two_ω₂_two_ω₁ :
    Submodule.span ℤ {2 * H.ω₂, 2 * H.ω₁} = H.lattice := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by
      rintro x (rfl | rfl)
      exacts [H.two_mul_ω₂_mem, H.two_mul_ω₁_mem])
  · refine Submodule.span_le.mpr ?_
    rintro x (rfl | rfl)
    · exact Submodule.subset_span (by simp)
    · have : H.periodPair.ω₂ = -(2 * H.ω₂) - 2 * H.ω₁ := by simp [ω₂]; ring
      rw [this]
      exact sub_mem (neg_mem (Submodule.subset_span (by simp)))
        (Submodule.subset_span (by simp))

/-- Integer coordinates with respect to `2ω₁, 2ω₃` are unique. -/
lemma p23R1_int_coord_eq_zero {m n : ℤ} (h : (m : ℂ) * (2 * H.ω₁) + n * (2 * H.ω₃) = 0) :
    m = 0 ∧ n = 0 := by
  have := LinearIndependent.pair_iff.mp H.linearIndependent_two_mul (m : ℝ) (n : ℝ)
    (by simpa [Complex.real_smul] using h)
  exact_mod_cast this

/-- `ℑ((cω₁ + dω₃)/(aω₁ + bω₃)) = (ad - bc) ℑτ / |a + bτ|²`. -/
lemma p23R1_im_div (a b c d : ℤ) :
    ((c * H.ω₁ + d * H.ω₃) / (a * H.ω₁ + b * H.ω₃)).im =
      ((a * d - b * c : ℤ) : ℝ) * H.tau.im / normSq (a + b * H.tau) := by
  have h1 := H.ω₁_ne_zero
  have heq : (c * H.ω₁ + d * H.ω₃) / (a * H.ω₁ + b * H.ω₃) =
      (c + d * H.tau) / (a + b * H.tau) := by
    rw [← mul_div_mul_right (c + d * H.tau) (a + b * H.tau) h1]
    simp only [tau]
    congr 1 <;> field_simp
  rw [heq, div_im, ← sub_div]
  congr 1
  simp only [add_re, add_im, mul_re, mul_im, intCast_re, intCast_im, zero_mul, sub_zero,
    add_zero, zero_add]
  push_cast
  ring

/-- DLMF 23.2.2–23.2.3: for integers `a, b, c, d` and `χ₁ = aω₁ + bω₃`, `χ₃ = cω₁ + dω₃`,
the numbers `2χ₁, 2χ₃` are (DLMF-oriented, `ℑ(χ₃/χ₁) > 0`) generators of `𝕃` iff
`ad - bc = 1`. The orientation condition is part of DLMF's notion of generators
(§23.2(i)); without it the condition would be `ad - bc = ±1`. -/
@[dlmf 23.2.E2, dlmf 23.2.E3]
theorem generators_iff (a b c d : ℤ) :
    (Submodule.span ℤ {2 * (a * H.ω₁ + b * H.ω₃), 2 * (c * H.ω₁ + d * H.ω₃)} = H.lattice ∧
      0 < ((c * H.ω₁ + d * H.ω₃) / (a * H.ω₁ + b * H.ω₃)).im) ↔ a * d - b * c = 1 := by
  have hlat : H.lattice = Submodule.span ℤ {2 * H.ω₁, 2 * H.ω₃} := rfl
  have htau := H.tau_im_pos
  rw [H.p23R1_im_div, hlat]
  constructor
  · rintro ⟨hspan, hpos⟩
    have m1 : 2 * H.ω₁ ∈ Submodule.span ℤ {2 * (a * H.ω₁ + b * H.ω₃), 2 * (c * H.ω₁ + d * H.ω₃)} :=
      hspan ▸ Submodule.subset_span (by simp)
    have m3 : 2 * H.ω₃ ∈ Submodule.span ℤ {2 * (a * H.ω₁ + b * H.ω₃), 2 * (c * H.ω₁ + d * H.ω₃)} :=
      hspan ▸ Submodule.subset_span (by simp)
    obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp m1
    obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp m3
    simp only [zsmul_eq_mul] at hpq hrs
    obtain ⟨e1, e2⟩ := H.p23R1_int_coord_eq_zero (m := p * a + q * c - 1) (n := p * b + q * d)
      (by push_cast; linear_combination hpq)
    obtain ⟨e3, e4⟩ := H.p23R1_int_coord_eq_zero (m := r * a + s * c) (n := r * b + s * d - 1)
      (by push_cast; linear_combination hrs)
    have hdet : (p * s - q * r) * (a * d - b * c) = 1 := by
      linear_combination (r * b + s * d) * e1 + e4 - (r * a + s * c) * e2 + 0 * e3
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exfalso
      rw [h] at hpos
      have : ((-1 : ℤ) : ℝ) * H.tau.im / normSq (a + b * H.tau) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by push_cast; linarith) (normSq_nonneg _)
      linarith
  · intro hdet
    refine ⟨le_antisymm ?_ ?_, ?_⟩
    · refine Submodule.span_le.mpr ?_
      rintro x (rfl | rfl)
      · rw [show 2 * (a * H.ω₁ + b * H.ω₃) = a • (2 * H.ω₁) + b • (2 * H.ω₃) by
          simp only [zsmul_eq_mul]; ring]
        exact Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩
      · rw [show 2 * (c * H.ω₁ + d * H.ω₃) = c • (2 * H.ω₁) + d • (2 * H.ω₃) by
          simp only [zsmul_eq_mul]; ring]
        exact Submodule.mem_span_pair.mpr ⟨c, d, rfl⟩
    · refine Submodule.span_le.mpr ?_
      have hdet' : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
      rintro x (rfl | rfl)
      · refine Submodule.mem_span_pair.mpr ⟨d, -b, ?_⟩
        simp only [zsmul_eq_mul]; push_cast
        linear_combination (2 * H.ω₁) * hdet'
      · refine Submodule.mem_span_pair.mpr ⟨-c, a, ?_⟩
        simp only [zsmul_eq_mul]; push_cast
        linear_combination (2 * H.ω₃) * hdet'
    · rw [hdet]
      have hz : (a : ℂ) + b * H.tau ≠ 0 := by
        intro hz
        have hi := congrArg Complex.im hz
        have hr := congrArg Complex.re hz
        simp at hi hr
        rcases hi with hb | hi
        · subst hb; simp at hr; subst hr; simp at hdet
        · linarith
      have := normSq_pos.mpr hz
      push_cast
      positivity

end HalfPeriods

/-! ### The functions `ζ` and `σ` (§23.2(ii)) -/

/-- The summand of the zeta series is `z²/(w²(z - w))`. -/
theorem wp23_zeta_summand (z w : ℂ) (hw : w ≠ 0) (hz : z ≠ w) :
    1 / (z - w) + 1 / w + z / w ^ 2 = z ^ 2 / (w ^ 2 * (z - w)) := by
  have : z - w ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring

/-- Locally uniform bound for the zeta summand: `‖z²/(w²(z-w))‖ ≤ 2r²‖w‖⁻³`. -/
lemma wp23_zeta_bound (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) + 1 / l + s / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl : 0 < ‖l‖ := by linarith
  have hl0 : l ≠ 0 := norm_pos_iff.mp hl
  have hsl : s ≠ l := by rintro rfl; linarith
  have hsl' : ‖l‖ / 2 ≤ ‖s - l‖ := by
    rw [norm_sub_rev]; exact .trans (by linarith) (norm_sub_norm_le l s)
  rw [wp23_zeta_summand s l hl0 hsl, norm_div, norm_mul, norm_pow, norm_pow,
    Real.rpow_neg hl.le]
  have h1 : ‖s‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs.le 2
  calc ‖s‖ ^ 2 / (‖l‖ ^ 2 * ‖s - l‖) ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by
        gcongr
    _ = 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ := by field_simp
    _ = _ := by norm_cast

/-- `ζ` is odd (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem weierstrassZeta_neg (L : PeriodPair) (z : ℂ) :
    weierstrassZeta L (-z) = -weierstrassZeta L z := by
  simp only [weierstrassZeta]
  rw [← (Equiv.neg L.lattice).tsum_eq, ← tsum_neg]
  refine tsum_congr fun l => ?_
  simp only [Equiv.neg_apply, NegMemClass.coe_neg]
  rw [show -z - -(l : ℂ) = -(z - l) by ring, div_neg, div_neg, neg_sq]
  ring

/-- `σ` is odd (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem weierstrassSigma_neg (L : PeriodPair) (z : ℂ) :
    weierstrassSigma L (-z) = -weierstrassSigma L z := by
  simp only [weierstrassSigma]
  rw [← (Equiv.neg L.lattice).tprod_eq, neg_mul]
  congr 2
  refine tprod_congr fun l => ?_
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, neg_div_neg_eq, neg_sq]

/-- `σ` vanishes at every lattice point (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem weierstrassSigma_eq_zero_of_mem (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) :
    weierstrassSigma L z = 0 := by
  by_cases h0 : z = 0
  · simp [weierstrassSigma, h0]
  rw [weierstrassSigma, (hasProd_zero_of_exists_eq_zero ⟨⟨z, hz⟩, by simp [h0]⟩).tprod_eq,
    mul_zero]

/-- The double series for `ζ` converges absolutely and locally uniformly on `ℂ` (with the
totalized summands at lattice points), DLMF §23.2(ii). -/
@[dlmf 23.2.ii]
theorem hasSumLocallyUniformly_weierstrassZeta (L : PeriodPair) :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      (weierstrassZeta L) := by
  refine L.hasSumLocallyUniformly_aux (u := (2 * · ^ 2 * ‖·‖ ^ (-3 : ℝ))) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  exact wp23_zeta_bound r hr s hs l h

section p23R1Sigma

open Filter Topology

/-- The Weierstrass elementary factor bound: `‖(1 - u)e^{u + u²/2} - 1‖ ≤ 2‖u‖³` for
`‖u‖ ≤ 1/2`. -/
lemma p23R1_norm_elementary_factor_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖(1 - u) * cexp (u + u ^ 2 / 2) - 1‖ ≤ 2 * ‖u‖ ^ 3 := by
  have hu1 : ‖-u‖ < 1 := by rw [norm_neg]; linarith
  have h1u : (1 : ℂ) - u ≠ 0 := by
    intro h
    have : u = 1 := by linear_combination -h
    rw [this, norm_one] at hu; linarith
  have hT : logTaylor (2 + 1) (-u) = -u - u ^ 2 / 2 := by
    simp [logTaylor, Finset.sum_range_succ]; ring
  have hb := norm_log_sub_logTaylor_le 2 hu1
  rw [hT, norm_neg, ← sub_eq_add_neg] at hb
  set w := log (1 - u) - (-u - u ^ 2 / 2) with hw
  have hwb : ‖w‖ ≤ 2 / 3 * ‖u‖ ^ 3 := by
    refine hb.trans ?_
    have h0 : 0 ≤ ‖u‖ := norm_nonneg u
    have : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    push_cast
    calc ‖u‖ ^ (2 + 1) * (1 - ‖u‖)⁻¹ / (2 + 1) ≤ ‖u‖ ^ (2 + 1) * 2 / (2 + 1) := by
          gcongr
      _ = 2 / 3 * ‖u‖ ^ 3 := by ring
  have heq : (1 - u) * cexp (u + u ^ 2 / 2) = cexp w := by
    rw [hw, show log (1 - u) - (-u - u ^ 2 / 2) = log (1 - u) + (u + u ^ 2 / 2) by ring,
      Complex.exp_add (log _), Complex.exp_log h1u]
  rw [heq]
  have hw1 : ‖w‖ ≤ 1 := by
    refine hwb.trans ?_
    have : ‖u‖ ^ 3 ≤ (1 / 2) ^ 3 := by gcongr
    linarith
  calc ‖cexp w - 1‖ ≤ 2 * ‖w‖ := norm_exp_sub_one_le hw1
    _ ≤ 2 * (2 / 3 * ‖u‖ ^ 3) := by gcongr
    _ ≤ 2 * ‖u‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg u) 3]

/-- The Weierstrass factor of `σ` at the lattice point `l`. -/
noncomputable def p23R1_sigmaFactor (l z : ℂ) : ℂ := (1 - z / l) * cexp (z / l + z ^ 2 / (2 * l ^ 2))

/-- Bound for the Weierstrass factor of `σ` on `‖z‖ < r` when `‖l‖ ≥ 2r`. -/
lemma p23R1_norm_sigmaFactor_sub_one_le {r : ℝ} {l z : ℂ} (hz : ‖z‖ < r) (hl : 2 * r ≤ ‖l‖) :
    ‖p23R1_sigmaFactor l z - 1‖ ≤ 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hz
  have hl0 : 0 < ‖l‖ := by linarith
  have hu : ‖z / l‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hl0]; linarith
  have h := p23R1_norm_elementary_factor_sub_one_le hu
  have he : p23R1_sigmaFactor l z = (1 - z / l) * cexp (z / l + (z / l) ^ 2 / 2) := by
    simp only [p23R1_sigmaFactor]; congr 3; ring
  rw [he]
  refine h.trans ?_
  rw [norm_div, div_pow, Real.rpow_neg hl0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, div_eq_mul_inv, ← mul_assoc]
  gcongr

/-- All but finitely many lattice points have norm at least `R`. -/
lemma p23R1_eventually_le_norm (L : PeriodPair) (R : ℝ) :
    ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intro l hl
  have hl' : ¬ R ≤ ‖(l : ℂ)‖ := hl
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact (not_le.mp hl').le

/-- The majorant `2r³‖l‖⁻³` is summable over the lattice. -/
lemma p23R1_summable_bound (L : PeriodPair) (r : ℝ) :
    Summable fun l : L.lattice => 2 * r ^ 3 * ‖(l : ℂ)‖ ^ (-3 : ℝ) :=
  (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _

/-- The product for `σ` converges locally uniformly on every ball. -/
lemma p23R1_hasProdLocallyUniformlyOn_sigma (L : PeriodPair) {r : ℝ} :
    HasProdLocallyUniformlyOn (fun (l : L.lattice) z => p23R1_sigmaFactor l z)
      (fun z => ∏' l : L.lattice, p23R1_sigmaFactor l z) (Metric.ball 0 r) := by
  have h := Summable.hasProdLocallyUniformlyOn_one_add (f := fun (l : L.lattice) z =>
      p23R1_sigmaFactor l z - 1) (K := Metric.ball (0 : ℂ) r) Metric.isOpen_ball
    (p23R1_summable_bound L r) ?_ ?_
  · simpa using h
  · filter_upwards [p23R1_eventually_le_norm L (2 * r)] with l hl z hz
    exact p23R1_norm_sigmaFactor_sub_one_le (by simpa using hz) hl
  · intro l
    exact (by unfold p23R1_sigmaFactor; fun_prop : Continuous fun z : ℂ =>
      p23R1_sigmaFactor l z - 1).continuousOn

/-- `∑ ‖E_l(z) - 1‖` converges for the Weierstrass factors `E_l` of `σ`. -/
lemma p23R1_summable_norm_sigmaFactor (L : PeriodPair) (z : ℂ) :
    Summable fun l : L.lattice => ‖p23R1_sigmaFactor l z - 1‖ := by
  refine Summable.of_norm_bounded_eventually (p23R1_summable_bound L (‖z‖ + 1)) ?_
  filter_upwards [p23R1_eventually_le_norm L (2 * (‖z‖ + 1))] with l hl
  rw [norm_norm]
  exact p23R1_norm_sigmaFactor_sub_one_le (by linarith) hl

/-- The Weierstrass factors of `σ` do not vanish off the lattice. -/
lemma p23R1_sigmaFactor_ne_zero (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (l : L.lattice) : p23R1_sigmaFactor l z ≠ 0 := by
  unfold p23R1_sigmaFactor
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  by_cases hl : (l : ℂ) = 0
  · simp [hl]
  · intro h
    have : z = l := by
      have := sub_eq_zero.mp h
      field_simp at this
      exact this.symm
    exact hz (this ▸ l.2)

/-- The logarithmic derivative of a Weierstrass factor of `σ` is a summand of `ζ` (the `l = 0`
summand `1/z` of `ζ` is accounted for separately). -/
lemma p23R1_logDeriv_sigmaFactor (L : PeriodPair) {x : ℂ} (hx : x ∉ L.lattice)
    (l : L.lattice) :
    logDeriv (p23R1_sigmaFactor l) x =
      (1 / (x - l) + 1 / l + x / l ^ 2) - if (l : ℂ) = 0 then 1 / x else 0 := by
  by_cases hl : (l : ℂ) = 0
  · have : p23R1_sigmaFactor l = fun _ => 1 := by
      funext z; simp [p23R1_sigmaFactor, hl]
    rw [this]
    simp [hl, logDeriv]
  · have hxl : x - l ≠ 0 := sub_ne_zero.mpr fun h => hx (h ▸ l.2)
    have h1 : HasDerivAt (fun z : ℂ => 1 - z / l) (-(1 / l)) x := by
      simpa using ((hasDerivAt_id x).div_const (l : ℂ)).const_sub 1
    have h2 : HasDerivAt (fun z : ℂ => z / l + z ^ 2 / (2 * l ^ 2)) (1 / l + 2 * x / (2 * l ^ 2)) x := by
      have := ((hasDerivAt_id' x).div_const (l : ℂ)).fun_add
        ((hasDerivAt_pow 2 x).div_const (2 * (l : ℂ) ^ 2))
      convert this using 1; simp
    have hd := h1.fun_mul h2.cexp
    have hf : p23R1_sigmaFactor l = fun z => (1 - z / l) * cexp (z / l + z ^ 2 / (2 * l ^ 2)) := rfl
    rw [logDeriv_apply, hf, hd.deriv]
    simp only [hl, ite_false, sub_zero]
    have he := Complex.exp_ne_zero (x / l + x ^ 2 / (2 * l ^ 2))
    have h1x : (1 : ℂ) - x / l ≠ 0 := by
      rw [one_sub_div hl]; exact div_ne_zero (by rwa [← neg_sub, neg_ne_zero]) hl
    rw [one_sub_div hl]
    have hlx : (l : ℂ) - x ≠ 0 := by rwa [← neg_sub, neg_ne_zero] at hxl
    field_simp
    ring

end p23R1Sigma

/-- The double product for `σ` converges (unconditionally) for every `z` (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem multipliable_weierstrassSigma (L : PeriodPair) (z : ℂ) :
    Multipliable fun l : L.lattice ↦ (1 - z / l) * cexp (z / l + z ^ 2 / (2 * l ^ 2)) :=
  ((p23R1_hasProdLocallyUniformlyOn_sigma L (r := ‖z‖ + 1)).hasProd
    (by simp)).multipliable

/-- Differentiability throughout the specified domain: `DifferentiableOn ℂ (fun z : ℂ ↦ 1 / (z -
l) + 1 / l + z / l ^ 2) L.latticeᶜ`. -/
lemma wp23_differentiableOn_zeta_summand (L : PeriodPair) (l : L.lattice) :
    DifferentiableOn ℂ (fun z : ℂ ↦ 1 / (z - l) + 1 / l + z / l ^ 2) L.latticeᶜ := by
  intro z hz
  have : z - l ≠ 0 := sub_ne_zero.mpr fun h => hz (h ▸ l.2)
  have h : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / (w - l) + 1 / l + w / l ^ 2) z := by
    fun_prop (disch := exact this)
  exact h.differentiableWithinAt

/-- `ζ` is differentiable off the lattice (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem differentiableOn_weierstrassZeta (L : PeriodPair) :
    DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ :=
  TendstoLocallyUniformlyOn.differentiableOn
    (hasSumLocallyUniformly_weierstrassZeta L).hasSumLocallyUniformlyOn
    (.of_forall fun _ ↦ .fun_sum fun l _ ↦ wp23_differentiableOn_zeta_summand L l)
    L.isClosed_lattice.isOpen_compl

/-- DLMF 23.2.7: `℘(z) = -ζ'(z)` for `z ∉ 𝕃`. -/
@[dlmf 23.2.E7]
theorem hasDerivAt_weierstrassZeta (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (weierstrassZeta L) (-℘[L] z) z := by
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hd := (differentiableOn_weierstrassZeta L).differentiableAt (hU.mem_nhds hz)
  convert hd.hasDerivAt using 1
  have hT : TendstoLocallyUniformlyOn
      (fun (s : Finset L.lattice) (w : ℂ) ↦ ∑ l ∈ s, (1 / (w - l) + 1 / l + w / l ^ 2))
      (weierstrassZeta L) Filter.atTop L.latticeᶜ :=
    (hasSumLocallyUniformly_weierstrassZeta L).hasSumLocallyUniformlyOn
  have hD := (TendstoLocallyUniformlyOn.deriv hT (.of_forall fun s ↦ .fun_sum fun l _ ↦
    wp23_differentiableOn_zeta_summand L l) hU).tendsto_at hz
  have hS : HasSum (fun l : L.lattice ↦ -(1 / (z - l) ^ 2 - 1 / l ^ 2)) (-℘[L] z) :=
    (L.hasSum_weierstrassP z).neg
  refine (tendsto_nhds_unique hD ?_).symm
  have hS' : Filter.Tendsto (fun s : Finset L.lattice ↦ ∑ l ∈ s, -(1 / (z - l) ^ 2 - 1 / l ^ 2))
      Filter.atTop (nhds (-℘[L] z)) := hS
  · refine hS'.congr' (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.comp_apply]
    rw [deriv_fun_sum fun l _ =>
      (wp23_differentiableOn_zeta_summand L l).differentiableAt (hU.mem_nhds hz)]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hzl : z - l ≠ 0 := sub_ne_zero.mpr fun h => hz (h ▸ l.2)
    have : HasDerivAt (fun w : ℂ ↦ 1 / (w - l) + 1 / l + w / l ^ 2)
        (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
      have h1 := ((hasDerivAt_id z).sub_const (l : ℂ)).inv hzl
      have h2 := (hasDerivAt_id z).div_const ((l : ℂ) ^ 2)
      convert (h1.add_const (1 / (l : ℂ))).add h2 using 1
      · ext w; simp [one_div]
      · simp only [id, one_div]; ring
    exact this.deriv.symm

/-- `σ` is entire (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem differentiable_weierstrassSigma (L : PeriodPair) :
    Differentiable ℂ (weierstrassSigma L) := by
  intro z
  have hU : IsOpen (Metric.ball (0 : ℂ) (‖z‖ + 1)) := Metric.isOpen_ball
  have hz : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by simp
  have hd : DifferentiableOn ℂ (fun z => ∏' l : L.lattice, p23R1_sigmaFactor l z)
      (Metric.ball 0 (‖z‖ + 1)) := by
    refine (p23R1_hasProdLocallyUniformlyOn_sigma L).differentiableOn
      (.of_forall fun s => ?_) hU
    refine DifferentiableOn.fun_finsetProd fun l _ => ?_
    exact (by unfold p23R1_sigmaFactor; fun_prop : Differentiable ℂ (p23R1_sigmaFactor l))
      |>.differentiableOn
  exact (differentiableAt_id.mul (hd.differentiableAt (hU.mem_nhds hz)))

/-- The zeros of `σ` are exactly the lattice points (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem weierstrassSigma_eq_zero_iff (L : PeriodPair) {z : ℂ} :
    weierstrassSigma L z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun h => ?_, weierstrassSigma_eq_zero_of_mem L⟩
  by_contra hz
  have hz0 : z ≠ 0 := fun h0 => hz (h0 ▸ zero_mem _)
  have hne := tprod_one_add_ne_zero_of_summable (f := fun l : L.lattice => p23R1_sigmaFactor l z - 1)
    (fun l => by simpa using p23R1_sigmaFactor_ne_zero L hz l)
    (p23R1_summable_norm_sigmaFactor L z)
  simp only [add_sub_cancel] at hne
  exact mul_ne_zero hz0 hne h

/-- DLMF 23.2.8: `ζ(z) = σ'(z)/σ(z)` for `z ∉ 𝕃`. -/
@[dlmf 23.2.E8]
theorem weierstrassZeta_eq_deriv_div (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    weierstrassZeta L z = deriv (weierstrassSigma L) z / weierstrassSigma L z := by
  have hz0 : z ≠ 0 := fun h0 => hz (h0 ▸ zero_mem _)
  set U := Metric.ball (0 : ℂ) (‖z‖ + 1)
  have hU : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by simp [U]
  have hfd : ∀ l : L.lattice, Differentiable ℂ (p23R1_sigmaFactor l) := fun l => by
    unfold p23R1_sigmaFactor; fun_prop
  have hprod := p23R1_hasProdLocallyUniformlyOn_sigma L (r := ‖z‖ + 1)
  have hP0 : ∏' l : L.lattice, p23R1_sigmaFactor l z ≠ 0 := by
    have := tprod_one_add_ne_zero_of_summable
      (f := fun l : L.lattice => p23R1_sigmaFactor l z - 1)
      (fun l => by simpa using p23R1_sigmaFactor_ne_zero L hz l)
      (p23R1_summable_norm_sigmaFactor L z)
    simpa using this
  -- the zeta series and the log-derivative series
  have hζ : HasSum (fun l : L.lattice => 1 / (z - l) + 1 / l + z / l ^ 2) (weierstrassZeta L z) :=
    (hasSumLocallyUniformly_weierstrassZeta L).hasSum
  have hlog : HasSum (fun l : L.lattice => logDeriv (p23R1_sigmaFactor l) z)
      (weierstrassZeta L z - 1 / z) := by
    have h0 := hasSum_ite_eq (0 : L.lattice) (1 / z)
    convert hζ.sub h0 using 1
    funext l
    rw [p23R1_logDeriv_sigmaFactor L hz l]
    congr 1
    by_cases hl : l = 0
    · subst hl; simp
    · have : (l : ℂ) ≠ 0 := by simpa using hl
      simp [hl, this]
  have hPd : DifferentiableOn ℂ (fun x => ∏' l : L.lattice, p23R1_sigmaFactor l x) U :=
    hprod.differentiableOn (.of_forall fun s => DifferentiableOn.fun_finsetProd fun l _ =>
      (hfd l).differentiableOn) hU
  have hLP := logDeriv_tprod_eq_tsum hU hzU (fun l => p23R1_sigmaFactor_ne_zero L hz l)
    (fun l => (hfd l).differentiableOn) hlog.summable ⟨_, hprod⟩ hP0
  have hσ : weierstrassSigma L = fun x => x * ∏' l : L.lattice, p23R1_sigmaFactor l x := rfl
  have hmul : logDeriv (weierstrassSigma L) z = logDeriv id z +
      logDeriv (fun x => ∏' l : L.lattice, p23R1_sigmaFactor l x) z := by
    rw [hσ]
    exact logDeriv_mul (f := id) z hz0 hP0 differentiableAt_id
      (hPd.differentiableAt (hU.mem_nhds hzU))
  rw [← logDeriv_apply, hmul, hLP, hlog.tsum_eq]
  simp [logDeriv]

/-- `ζ` has a simple pole with residue `1` at every lattice point: `ζ(z) - 1/(z - w)` is
analytic at `w ∈ 𝕃` (DLMF §23.2(ii)). With Lean's totalization the value at `z = w` is the
regular part. -/
@[dlmf 23.2.ii]
theorem analyticAt_weierstrassZeta_sub (L : PeriodPair) {w : ℂ} (hw : w ∈ L.lattice) :
    AnalyticAt ℂ (fun z ↦ weierstrassZeta L z - 1 / (z - w)) w := by
  classical
  set g : L.lattice → ℂ → ℂ := fun l z ↦
    if (l : ℂ) = w then 1 / w + z / w ^ 2 else 1 / (z - l) + 1 / l + z / l ^ 2 with hg
  have hsum : ∀ z, HasSum (fun l ↦ g l z) (weierstrassZeta L z - 1 / (z - w)) := by
    intro z
    have h1 := (hasSumLocallyUniformly_weierstrassZeta L).hasSum (x := z)
    have h2 := hasSum_ite_eq (⟨w, hw⟩ : L.lattice) (1 / (z - w))
    convert h1.sub h2 using 1
    funext l
    by_cases hl : (l : ℂ) = w
    · have : l = ⟨w, hw⟩ := Subtype.ext hl
      subst this; simp [hg]; ring
    · have : l ≠ ⟨w, hw⟩ := fun h => hl (by rw [h])
      simp [hg, hl, this]
  have hU : IsOpen ((L.lattice : Set ℂ) \ {w})ᶜ := L.isOpen_compl_lattice_sdiff
  have hloc : HasSumLocallyUniformly g (∑' l, g l ·) := by
    refine L.hasSumLocallyUniformly_aux (u := (2 * · ^ 2 * ‖·‖ ^ (-3 : ℝ))) _
      (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
      Filter.eventually_atTop.mpr ⟨max (2 * r) (‖w‖ + 1), ?_⟩
    rintro _ h s hs l rfl
    have hlw : (l : ℂ) ≠ w := by
      rintro hl; rw [hl] at h; linarith [le_max_right (2 * r) (‖w‖ + 1)]
    simp only [hg, hlw, ite_false]
    exact wp23_zeta_bound r hr s hs l ((le_max_left _ _).trans h)
  have hdiff : DifferentiableOn ℂ (∑' l, g l ·) ((L.lattice : Set ℂ) \ {w})ᶜ := by
    refine TendstoLocallyUniformlyOn.differentiableOn hloc.hasSumLocallyUniformlyOn
      (.of_forall fun _ ↦ .fun_sum fun l _ ↦ ?_) hU
    intro z hz
    by_cases hl : (l : ℂ) = w
    · simp only [hg, hl, ite_true]
      exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ 1 / w + z / w ^ 2) z)
        |>.differentiableWithinAt
    · have hzl : z - l ≠ 0 := sub_ne_zero.mpr fun h => hz ⟨h ▸ l.2, by simpa [h] using hl⟩
      simp only [hg, hl, ite_false]
      exact (by fun_prop (disch := exact hzl) :
        DifferentiableAt ℂ (fun w : ℂ ↦ 1 / (w - l) + 1 / l + w / l ^ 2) z)
        |>.differentiableWithinAt
  have heq : (fun z ↦ weierstrassZeta L z - 1 / (z - w)) = (∑' l, g l ·) :=
    funext fun z => ((hsum z).tsum_eq).symm
  rw [heq]
  exact hdiff.analyticAt (hU.mem_nhds (by simp))

/-- `ζ` is analytic off the lattice (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem analyticOnNhd_weierstrassZeta (L : PeriodPair) :
    AnalyticOnNhd ℂ (weierstrassZeta L) L.latticeᶜ :=
  (differentiableOn_weierstrassZeta L).analyticOnNhd L.isClosed_lattice.isOpen_compl

/-- The poles of `℘` are double with residue `0`: near `w ∈ 𝕃`,
`℘(z) = 1/(z-w)² + h(z)` with `h` analytic at `w` (DLMF §23.2(ii)). With Lean's totalization
the function `℘(z) - 1/(z - w)²` is itself analytic at `w`. -/
@[dlmf 23.2.ii]
theorem analyticAt_weierstrassP_sub (L : PeriodPair) {w : ℂ} (hw : w ∈ L.lattice) :
    AnalyticAt ℂ (fun z ↦ ℘[L] z - 1 / (z - w) ^ 2) w := by
  have heq : (fun z ↦ ℘[L] z - 1 / (z - w) ^ 2) = fun z ↦ ℘[L - w] z - 1 / w ^ 2 := by
    funext z
    rw [L.weierstrassPExcept_def ⟨w, hw⟩ z]
    ring
  rw [heq]
  exact (L.analyticAt_weierstrassPExcept w).sub analyticAt_const

/-- The complement of a period lattice is preconnected. -/
theorem wp23_isPreconnected_compl_lattice (L : PeriodPair) :
    IsPreconnected (L.latticeᶜ : Set ℂ) := by
  have hc : (L.lattice : Set ℂ).Countable := by
    have : Countable L.lattice := L.latticeEquivProd.toEquiv.injective.countable
    exact Set.countable_coe_iff.mp this
  exact (Set.Countable.isConnected_compl_of_one_lt_rank (by simp [rank_real_complex])
    hc).isPreconnected

/-- `ζ(z + w) - ζ(z)` is independent of `z ∉ 𝕃` for `w ∈ 𝕃`. -/
lemma wp23_zeta_add_sub_const (L : PeriodPair) {w : ℂ} (hw : w ∈ L.lattice) {z₁ z₂ : ℂ}
    (h₁ : z₁ ∉ L.lattice) (h₂ : z₂ ∉ L.lattice) :
    weierstrassZeta L (z₁ + w) - weierstrassZeta L z₁ =
      weierstrassZeta L (z₂ + w) - weierstrassZeta L z₂ := by
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hshift : ∀ z, z ∉ L.lattice → z + w ∉ L.lattice := fun z hz h =>
    hz (by simpa using sub_mem h hw)
  have hD : ∀ z ∈ (L.latticeᶜ : Set ℂ), HasDerivAt
      (fun z ↦ weierstrassZeta L (z + w) - weierstrassZeta L z) 0 z := by
    intro z hz
    have h1 := (hasDerivAt_weierstrassZeta L (hshift z hz)).comp_add_const z w
    have h2 := hasDerivAt_weierstrassZeta L hz
    convert h1.sub h2 using 1
    rw [L.weierstrassP_add_coe z ⟨w, hw⟩]; ring
  refine hU.is_const_of_deriv_eq_zero (wp23_isPreconnected_compl_lattice L)
    (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hD z hz).deriv) h₁ h₂

/-- `σ'(0) = 1`. -/
theorem p23R1_hasDerivAt_weierstrassSigma_zero (L : PeriodPair) :
    HasDerivAt (weierstrassSigma L) 1 0 := by
  have hU : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hPd : DifferentiableOn ℂ (fun x => ∏' l : L.lattice, p23R1_sigmaFactor l x)
      (Metric.ball 0 1) :=
    (p23R1_hasProdLocallyUniformlyOn_sigma L).differentiableOn
      (.of_forall fun s => DifferentiableOn.fun_finsetProd fun l _ =>
        (by unfold p23R1_sigmaFactor; fun_prop : Differentiable ℂ (p23R1_sigmaFactor l))
          |>.differentiableOn) hU
  have hP0 : ∏' l : L.lattice, p23R1_sigmaFactor l 0 = 1 := by simp [p23R1_sigmaFactor]
  have h := (hasDerivAt_id (0 : ℂ)).mul
    (hPd.differentiableAt (hU.mem_nhds (by simp))).hasDerivAt
  have hσ : weierstrassSigma L = fun x => id x * ∏' l : L.lattice, p23R1_sigmaFactor l x := rfl
  rw [hσ]
  convert h using 1
  simp [hP0]

/-- `σ'(z) = ζ(z)σ(z)` off the lattice. -/
lemma p23R1_deriv_weierstrassSigma_eq (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (weierstrassSigma L) z = weierstrassZeta L z * weierstrassSigma L z := by
  have h := (weierstrassSigma_eq_zero_iff L).not.mpr hz
  rw [weierstrassZeta_eq_deriv_div L hz, div_mul_cancel₀ _ h]

/-- Quasi-periodicity of `σ` along any lattice vector, with an unspecified nonzero constant. -/
theorem p23R1_weierstrassSigma_add_mem (L : PeriodPair) {w : ℂ} (hw : w ∈ L.lattice) {z₀ : ℂ}
    (hz₀ : z₀ ∉ L.lattice) : ∃ a : ℂ, a ≠ 0 ∧ ∀ z, weierstrassSigma L (z + w) =
      a * cexp ((weierstrassZeta L (z₀ + w) - weierstrassZeta L z₀) * z) * weierstrassSigma L z := by
  set c := weierstrassZeta L (z₀ + w) - weierstrassZeta L z₀ with hc
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hshift : ∀ z, z ∉ L.lattice → z + w ∉ L.lattice := fun z hz h =>
    hz (by simpa using sub_mem h hw)
  have hσd := differentiable_weierstrassSigma L
  have hne : ∀ z, z ∉ L.lattice → weierstrassSigma L z ≠ 0 := fun z hz =>
    (weierstrassSigma_eq_zero_iff L).not.mpr hz
  set h : ℂ → ℂ := fun z => weierstrassSigma L (z + w) * cexp (-(c * z)) / weierstrassSigma L z
  have hD : ∀ z ∈ (L.latticeᶜ : Set ℂ), HasDerivAt h 0 z := by
    intro z hz
    have hzc : weierstrassZeta L (z + w) = weierstrassZeta L z + c := by
      have := wp23_zeta_add_sub_const L hw hz hz₀
      rw [hc]; linear_combination this
    have h1 : HasDerivAt (fun z => weierstrassSigma L (z + w))
        ((weierstrassZeta L z + c) * weierstrassSigma L (z + w)) z := by
      have := (hσd (z + w)).hasDerivAt.comp_add_const z w
      rwa [p23R1_deriv_weierstrassSigma_eq L (hshift z hz), hzc] at this
    have h2 : HasDerivAt (fun z => cexp (-(c * z))) (cexp (-(c * z)) * -c) z := by
      have := ((hasDerivAt_id z).const_mul c).neg.cexp
      simpa using this
    have h3 : HasDerivAt (weierstrassSigma L) (weierstrassZeta L z * weierstrassSigma L z) z := by
      have := (hσd z).hasDerivAt
      rwa [p23R1_deriv_weierstrassSigma_eq L hz] at this
    convert (h1.fun_mul h2).div h3 (hne z hz) using 1
    field_simp
    ring
  have hconst : ∀ z, z ∉ L.lattice → h z = h z₀ := fun z hz =>
    hU.is_const_of_deriv_eq_zero (wp23_isPreconnected_compl_lattice L)
      (fun y hy => (hD y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hD y hy).deriv) hz hz₀
  refine ⟨h z₀, ?_, fun z => ?_⟩
  · exact div_ne_zero (mul_ne_zero (hne _ (hshift z₀ hz₀)) (Complex.exp_ne_zero _))
      (hne z₀ hz₀)
  · by_cases hz : z ∈ L.lattice
    · rw [weierstrassSigma_eq_zero_of_mem L hz, weierstrassSigma_eq_zero_of_mem L (add_mem hz hw),
        mul_zero]
    · rw [← hconst z hz]
      simp only [h]
      have := hne z hz
      have he : cexp (-(z * c)) * cexp (z * c) = 1 := by rw [← Complex.exp_add]; simp
      field_simp
      linear_combination (-weierstrassSigma L (z + w)) * he

/-- The zeros of `σ` are simple (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem deriv_weierstrassSigma_ne_zero (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) :
    deriv (weierstrassSigma L) z ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ ∉ L.lattice := ⟨_, L.ω₁_div_two_notMem_lattice⟩
  obtain ⟨a, ha, hfa⟩ := p23R1_weierstrassSigma_add_mem L hz hz₀
  set c := weierstrassZeta L (z₀ + z) - weierstrassZeta L z₀
  have h1 : HasDerivAt (fun y => weierstrassSigma L (y + z)) (deriv (weierstrassSigma L) z) 0 := by
    have := ((differentiable_weierstrassSigma L) (0 + z)).hasDerivAt.comp_add_const 0 z
    simpa using this
  have h2 : HasDerivAt (fun y => a * cexp (c * y) * weierstrassSigma L y) a 0 := by
    have he : HasDerivAt (fun y => cexp (c * y)) (cexp (c * 0) * c) 0 :=
      ((hasDerivAt_id (0 : ℂ)).const_mul c).cexp.congr_deriv (by simp)
    convert ((he.const_mul a).mul (p23R1_hasDerivAt_weierstrassSigma_zero L)) using 1
    simp [weierstrassSigma_eq_zero_of_mem L (zero_mem _)]
  rw [show (fun y => weierstrassSigma L (y + z)) = fun y => a * cexp (c * y) * weierstrassSigma L y
    from funext hfa] at h1
  rw [h1.unique h2]
  exact ha

end DLMF.Weierstrass
end
end
