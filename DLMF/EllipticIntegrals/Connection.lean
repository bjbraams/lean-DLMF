/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Derivatives

/-!
# Connection formulas for Legendre's integrals (DLMF §19.7)

Statements of DLMF 19.7.1–19.7.10. Legendre's relation (19.7.1) is proved for real `0 < k < 1`
from the existing real `DLMF.Elliptic.legendre_relation`. On the complex domain it follows by the
identity theorem on `Re k > 0`, by evenness in `k` for `Re k < 0`, and on the imaginary axis by a
one-sided limit from `Re k > 0` (dominated convergence across the cut of `K(k')` and `E(k')`).
19.7.2 is proved by the identity theorem from the real substitution `θ ↦ π/2 - θ`.
The modulus transformations 19.7.2–19.7.3 are stated for complex `k`; the transformations
19.7.4–19.7.7 for the real amplitudes on which DLMF states them (19.7.7 with complex `k`); the
parameter changes 19.7.8–19.7.10 for real data, with Cauchy principal values. Here
`k' = jacobiComodulusk k` (principal), `c = csc²φ` and `R_C = symEllIntRC`.

**Convention note.** DLMF prints the second and fourth formulas of 19.7.2,
`K(-ik'/k) = kK(k')` and `E(-ik'/k) = (1/k)E(k')`, without a condition; their left sides are even
in `k` (they depend on `k²` only) and the right sides odd, so they hold for `Re k > 0` (as in
19.7.3, which DLMF states for `Re k > 0`) and change sign for `Re k < 0`; checked numerically
with mpmath at `k = 0.6, 0.5 + 0.3i, 1.3 + 0.5i, 0.3 - 0.9i` (valid) and `k = -0.4 + 0.7i,
-1.3 + 0.5i, -0.3 - 2i` (sign reversed). They are acquired with `0 < Re k`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### §19.7(i) Complete integrals of the first and second kinds -/

/-- DLMF 19.7.1 (Legendre's relation) for real `0 < k < 1`:
`E(k)K'(k) + E'(k)K(k) - K(k)K'(k) = π/2`. -/
@[dlmf 19.7.E1]
theorem legendre_relation_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    compEllIntEk k * cCompEllIntKk k + cCompEllIntEk k * compEllIntKk k -
      compEllIntKk k * cCompEllIntKk k = π / 2 := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  rw [compEllIntEk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk2.le,
    compEllIntKk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk2.le, cCompEllIntKk_ofReal hk0,
    cCompEllIntEk_ofReal hk0]
  have h := DLMF.Elliptic.legendre_relation (m := k ^ 2) (by positivity) hk2
  exact_mod_cast h

/-! ### Helpers for 19.7.1 and 19.7.2 -/

lemma p19lR1_imag_integral {x c : ℝ} (hc : 0 < c) (hxc : c ^ 2 = 1 - x ^ 2) (r : ℂ) :
    ∫ θ in (0 : ℝ)..(π / 2), (1 - (I * x / c) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ r =
      (((c ^ 2)⁻¹ : ℝ) : ℂ) ^ r *
        ∫ θ in (0 : ℝ)..(π / 2), (1 - (x : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ r := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => (1 - (I * x / c) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ r) (a := 0) (b := π / 2) (π / 2)
  simp only [sub_self, sub_zero] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [Real.sin_pi_div_two_sub]
  have hA : 0 ≤ 1 - x ^ 2 * Real.sin θ ^ 2 := by
    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.sin θ), sq_nonneg c, mul_nonneg (sq_nonneg x) (sq_nonneg (Real.sin θ))]
  have e : (1 - (I * x / c) ^ 2 * (Real.cos θ : ℂ) ^ 2) =
      (((c ^ 2)⁻¹ : ℝ) : ℂ) * ((1 - x ^ 2 * Real.sin θ ^ 2 : ℝ) : ℂ) := by
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hxc' : (c : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 := by exact_mod_cast hxc
    push_cast
    field_simp
    rw [I_sq, hxc']
    linear_combination ((x : ℂ) ^ 2) * Complex.cos_sq_add_sin_sq (θ : ℂ)
  rw [e, Complex.mul_cpow_ofReal_nonneg (by positivity) hA]
  push_cast; ring_nf

lemma p19lR1_inv_sq_cpow {c : ℝ} (hc : 0 < c) :
    (((c ^ 2)⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = c ∧ (((c ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (c : ℂ)⁻¹ := by
  have h1 : (((c ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (c : ℂ)⁻¹ := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      Real.inv_rpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hc.le]
    push_cast; rfl
  refine ⟨?_, h1⟩
  rw [cpow_neg, h1, inv_inv]

lemma p19lR1_inv_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) : w⁻¹ ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  have hw0 : w ≠ 0 := slitPlane_ne_zero (mem_slitPlane_iff.2 hw)
  have hn : 0 < normSq w := normSq_pos.2 hw0
  rw [inv_re, inv_im]
  rcases hw with h | h
  · left; exact div_pos h hn
  · right; exact div_ne_zero (neg_ne_zero.2 h) hn.ne'

theorem p19lR1_isOpen_U : IsOpen {k : ℂ | 1 - k ^ 2 ∈ slitPlane} :=
  isOpen_slitPlane.preimage (by fun_prop)

lemma p19lR1_isPreconnected_U : IsPreconnected {k : ℂ | 1 - k ^ 2 ∈ slitPlane} := by
  refine (StarConvex.isPathConnected (a := (0 : ℂ)) ?_ (by simp)).isConnected.isPreconnected
  intro y hy a b ha hb hab
  simp only [smul_zero, zero_add, Set.mem_ofPred_eq, real_smul] at hy ⊢
  have := ei19a_one_sub_mul_mem_slitPlane hy (sq_nonneg b) (by nlinarith)
  convert this using 2; push_cast; ring

theorem p19lR1_comod_differentiableAt {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    DifferentiableAt ℂ jacobiComodulusk k := by
  unfold jacobiComodulusk
  exact (by fun_prop : DifferentiableAt ℂ (fun k : ℂ => 1 - k ^ 2) k).cpow_const hk

lemma p19lR1_comod_ne_zero {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) : jacobiComodulusk k ≠ 0 := by
  intro h
  have := ei19a_jacobiComodulusk_sq k
  rw [h] at this
  exact slitPlane_ne_zero hk (by rw [← this]; ring)

lemma p19lR1_comod_ofReal {x : ℝ} (hx : x ^ 2 ≤ 1) :
    jacobiComodulusk x = (Real.sqrt (1 - x ^ 2) : ℂ) := by
  rw [jacobiComodulusk, Real.sqrt_eq_rpow, ofReal_cpow (by linarith)]
  push_cast; rfl

lemma p19lR1_imag_mem {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    1 - (I * k / jacobiComodulusk k) ^ 2 ∈ slitPlane := by
  have hne := p19lR1_comod_ne_zero hk
  have hne' : 1 - k ^ 2 ≠ 0 := slitPlane_ne_zero hk
  have : 1 - (I * k / jacobiComodulusk k) ^ 2 = (1 - k ^ 2)⁻¹ := by
    rw [div_pow, ei19a_jacobiComodulusk_sq, mul_pow, I_sq]
    field_simp; ring
  rw [this]; exact p19lR1_inv_mem_slitPlane hk

theorem p19lR1_eqOn_U {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f {k : ℂ | 1 - k ^ 2 ∈ slitPlane})
    (hg : DifferentiableOn ℂ g {k : ℂ | 1 - k ^ 2 ∈ slitPlane})
    (h : ∀ x : ℝ, 0 < x → x < 1 → f x = g x) {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) : f k = g k := by
  have h0 : (0 : ℂ) ∈ {k : ℂ | 1 - k ^ 2 ∈ slitPlane} := by simp
  refine (hf.analyticOnNhd p19lR1_isOpen_U).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd p19lR1_isOpen_U) p19lR1_isPreconnected_U h0 ?_ hk
  have := Carlson.TwoVariable.frequently_ofReal_Ioo (a := 0) (ε := 1) one_pos (P := fun z => f z = g z)
    (fun x h1 h2 => h x h1 (by linarith))
  simpa using this

lemma p19lR1_imag_modulus {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    compEllIntKk (I * k / jacobiComodulusk k) = jacobiComodulusk k * compEllIntKk k ∧
      compEllIntEk (I * k / jacobiComodulusk k) = compEllIntEk k / jacobiComodulusk k := by
  have hD := differentiableOn_compEllIntKk_compEllIntEk
  have hcomp : DifferentiableOn ℂ (fun k : ℂ => I * k / jacobiComodulusk k)
      {k : ℂ | 1 - k ^ 2 ∈ slitPlane} := fun k hk =>
    ((differentiableAt_const _).mul differentiableAt_id |>.div (p19lR1_comod_differentiableAt hk)
      (p19lR1_comod_ne_zero hk)).differentiableWithinAt
  have hmaps : MapsTo (fun k : ℂ => I * k / jacobiComodulusk k) {k : ℂ | 1 - k ^ 2 ∈ slitPlane}
      {k : ℂ | 1 - k ^ 2 ∈ slitPlane} := fun k hk => p19lR1_imag_mem hk
  have hc : DifferentiableOn ℂ jacobiComodulusk {k : ℂ | 1 - k ^ 2 ∈ slitPlane} := fun k hk =>
    (p19lR1_comod_differentiableAt hk).differentiableWithinAt
  have hreal : ∀ x : ℝ, 0 < x → x < 1 → 0 < Real.sqrt (1 - x ^ 2) ∧
      Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 ∧ jacobiComodulusk x = (Real.sqrt (1 - x ^ 2) : ℂ) :=
    fun x h0 h1 => ⟨Real.sqrt_pos.2 (by nlinarith), Real.sq_sqrt (by nlinarith),
      p19lR1_comod_ofReal (by nlinarith)⟩
  constructor
  · refine p19lR1_eqOn_U (hD.1.comp hcomp hmaps) (g := fun k => jacobiComodulusk k * compEllIntKk k) (hc.mul hD.1) (fun x h0 h1 => ?_) hk
    obtain ⟨hc0, hc2, hcx⟩ := hreal x h0 h1
    simp only [Function.comp, hcx]
    unfold compEllIntKk
    rw [p19lR1_imag_integral hc0 hc2, (p19lR1_inv_sq_cpow hc0).1]
  · refine p19lR1_eqOn_U (hD.2.comp hcomp hmaps) (g := fun k => compEllIntEk k / jacobiComodulusk k) (hD.2.div hc fun k hk => p19lR1_comod_ne_zero hk)
      (fun x h0 h1 => ?_) hk
    obtain ⟨hc0, hc2, hcx⟩ := hreal x h0 h1
    simp only [Function.comp_def, hcx]
    rw [compEllIntEk_eq_integral, compEllIntEk_eq_integral, p19lR1_imag_integral hc0 hc2,
      (p19lR1_inv_sq_cpow hc0).2]
    ring

lemma p19lR1_comod_comod {k : ℂ} (hk : 0 < k.re) :
    jacobiComodulusk (jacobiComodulusk k) = k := by
  rw [jacobiComodulusk, ei19a_jacobiComodulusk_sq, sub_sub_cancel, one_div]
  have h := abs_arg_lt_pi_div_two_iff.2 (Or.inl hk)
  rw [abs_lt] at h
  exact Complex.pow_cpow_nat_inv (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

lemma p19lR1_imag_comodulus {k : ℂ} (hk : 0 < k.re) (hk2 : k ^ 2 ∈ slitPlane) :
    compEllIntKk (-I * jacobiComodulusk k / k) = k * compEllIntKk (jacobiComodulusk k) ∧
      compEllIntEk (-I * jacobiComodulusk k / k) = compEllIntEk (jacobiComodulusk k) / k := by
  have h1 : 1 - jacobiComodulusk k ^ 2 ∈ slitPlane := by
    rw [ei19a_jacobiComodulusk_sq, sub_sub_cancel]; exact hk2
  have h := p19lR1_imag_modulus h1
  rw [p19lR1_comod_comod hk] at h
  rw [show -I * jacobiComodulusk k / k = -(I * jacobiComodulusk k / k) by ring,
    compEllIntKk_neg, compEllIntEk_neg]
  exact h


/-- The Legendre combination with the literal complementary integrals `K(k')`, `E(k')`. -/
noncomputable def p19lR1_W (k : ℂ) : ℂ :=
  compEllIntEk k * compEllIntKk (jacobiComodulusk k) +
    compEllIntEk (jacobiComodulusk k) * compEllIntKk k -
      compEllIntKk k * compEllIntKk (jacobiComodulusk k)

lemma p19lR1_comod_neg (k : ℂ) : jacobiComodulusk (-k) = jacobiComodulusk k := by
  simp [jacobiComodulusk]

lemma p19lR1_W_neg (k : ℂ) : p19lR1_W (-k) = p19lR1_W k := by
  simp only [p19lR1_W, p19lR1_comod_neg, compEllIntKk_neg, compEllIntEk_neg]

lemma p19lR1_sq_mem_slitPlane {k : ℂ} (hk : 0 < k.re) : k ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases eq_or_ne k.im 0 with h | h
  · left; simp [sq, h]; nlinarith
  · right; simp only [sq, mul_im]; intro h'
    have : k.re * k.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · exact hk.ne' h3
    · exact h h3

lemma p19lR1_one_sub_sq_mem_iff {z : ℂ} : 1 - z ^ 2 ∈ slitPlane ↔ z.im ≠ 0 ∨ z.re ^ 2 < 1 := by
  rw [mem_slitPlane_iff]
  simp only [sub_re, one_re, sub_im, one_im, sq, mul_re, mul_im, zero_sub, ne_eq, neg_eq_zero]
  constructor
  · rintro (h | h)
    · by_cases him : z.im = 0
      · right; simp [him] at h; nlinarith
      · left; exact him
    · left; intro him; apply h; simp [him]
  · rintro (h | h)
    · by_cases hre : z.re = 0
      · left; simp [hre]; nlinarith [sq_nonneg z.im]
      · right; intro h'; rcases mul_eq_zero.1 (by linarith : z.re * z.im * 2 = 0) with h'' | h''
        · rcases mul_eq_zero.1 h'' with h3 | h3
          · exact hre h3
          · exact h h3
        · norm_num at h''
    · left; nlinarith [sq_nonneg z.im]

lemma p19lR1_isOpen_V : IsOpen {k : ℂ | 0 < k.re ∧ 1 - k ^ 2 ∈ slitPlane} :=
  (isOpen_lt continuous_const continuous_re).inter p19lR1_isOpen_U

lemma p19lR1_isPreconnected_V : IsPreconnected {k : ℂ | 0 < k.re ∧ 1 - k ^ 2 ∈ slitPlane} := by
  refine (StarConvex.isPathConnected (a := ((1 / 2 : ℝ) : ℂ)) ?_ ?_).isConnected.isPreconnected
  · intro y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, real_smul, p19lR1_one_sub_sq_mem_iff] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, add_im, mul_im,
      zero_add, mul_zero]
    constructor
    · rcases hb.lt_or_eq with hb' | hb'
      · nlinarith [mul_pos hb' hy1]
      · subst hb'; norm_num at hab ⊢; linarith
    · rcases hy2 with h | h
      · rcases hb.lt_or_eq with hb' | hb'
        · left; simpa using mul_ne_zero hb'.ne' h
        · right; subst hb'; norm_num at hab ⊢; subst hab; norm_num
      · right
        have hr : y.re < 1 := by nlinarith
        have hz : a * (1 / 2) + b * y.re < 1 := by nlinarith
        have hz0 : 0 ≤ a * (1 / 2) + b * y.re := by positivity
        nlinarith
  · simp only [Set.mem_ofPred_eq, p19lR1_one_sub_sq_mem_iff, ofReal_re, ofReal_im]; norm_num

lemma p19lR1_W_of_re_pos {k : ℂ} (hk : 0 < k.re) (hk1 : 1 - k ^ 2 ∈ slitPlane) :
    p19lR1_W k = π / 2 := by
  have hD := differentiableOn_compEllIntKk_compEllIntEk
  have hV : {k : ℂ | 0 < k.re ∧ 1 - k ^ 2 ∈ slitPlane} ⊆ {k : ℂ | 1 - k ^ 2 ∈ slitPlane} :=
    fun k hk => hk.2
  have hc : DifferentiableOn ℂ jacobiComodulusk {k : ℂ | 0 < k.re ∧ 1 - k ^ 2 ∈ slitPlane} :=
    fun k hk => (p19lR1_comod_differentiableAt hk.2).differentiableWithinAt
  have hmaps : MapsTo jacobiComodulusk {k : ℂ | 0 < k.re ∧ 1 - k ^ 2 ∈ slitPlane}
      {k : ℂ | 1 - k ^ 2 ∈ slitPlane} := fun k hk => by
    show 1 - jacobiComodulusk k ^ 2 ∈ slitPlane
    rw [ei19a_jacobiComodulusk_sq, sub_sub_cancel]; exact p19lR1_sq_mem_slitPlane hk.1
  have hW : DifferentiableOn ℂ p19lR1_W {k : ℂ | 0 < k.re ∧ 1 - k ^ 2 ∈ slitPlane} := by
    have h1 := hD.1.mono hV
    have h2 := hD.2.mono hV
    have h3 := hD.1.comp hc hmaps
    have h4 := hD.2.comp hc hmaps
    exact ((h2.mul h3).add (h4.mul h1)).sub (h1.mul h3)
  have h0 : ((1 / 2 : ℝ) : ℂ) ∈ {k : ℂ | 0 < k.re ∧ 1 - k ^ 2 ∈ slitPlane} := by
    simp only [Set.mem_ofPred_eq, p19lR1_one_sub_sq_mem_iff, ofReal_re, ofReal_im]; norm_num
  refine (hW.analyticOnNhd p19lR1_isOpen_V).eqOn_of_preconnected_of_frequently_eq
    (analyticOnNhd_const (v := ((π : ℂ) / 2))) p19lR1_isPreconnected_V h0 ?_ ⟨hk, hk1⟩
  refine Carlson.TwoVariable.frequently_ofReal_Ioo (a := 1 / 2) (ε := 1 / 2) (by norm_num)
    (fun x h1 h2 => ?_)
  have hx0 : 0 < x := by linarith
  have hx1 : x < 1 := by linarith
  have h := legendre_relation_ofReal hx0 hx1
  have hre : 0 < (x : ℂ).re ∨ ((x : ℂ).re = 0 ∧ 0 ≤ (x : ℂ).im) := Or.inl (by simpa using hx0)
  rw [(cCompEllIntKk_of_re_pos hre).1, (cCompEllIntKk_of_re_pos hre).2] at h
  rw [p19lR1_W]; exact h

/-- The Legendre combination with DLMF's continued `K'`, `E'` equals `p19lR1_W` everywhere. -/
lemma p19lR1_legendre_eq_W (k : ℂ) :
    compEllIntEk k * cCompEllIntKk k + cCompEllIntEk k * compEllIntKk k -
      compEllIntKk k * cCompEllIntKk k = p19lR1_W k := by
  unfold cCompEllIntKk cCompEllIntEk p19lR1_W
  rw [compEllIntKk_jacobiComodulusk, compEllIntKk_neg, compEllIntEk_neg]
  split_ifs <;> ring

lemma p19lR1_cpow_cwa_upper {w : ℝ} (hw : w ≠ 0) (r : ℂ) :
    ContinuousWithinAt (fun z : ℂ => z ^ r) {z : ℂ | 0 ≤ z.im} (w : ℂ) := by
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  rcases hw.lt_or_gt with h | h
  · have hlog := continuousWithinAt_log_of_re_neg_of_im_zero (z := (w : ℂ)) (by simpa using h)
      (by simp)
    have hexp : ContinuousWithinAt (fun z => exp (log z * r)) {z : ℂ | 0 ≤ z.im} w :=
      Complex.continuous_exp.continuousAt.comp_continuousWithinAt
        (hlog.mul continuousWithinAt_const)
    refine hexp.congr_of_eventuallyEq ?_ (cpow_def_of_ne_zero hw' r)
    filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hw')] with z hz
    exact cpow_def_of_ne_zero hz r
  · exact (continuousAt_cpow_const (ofReal_mem_slitPlane.2 h)).continuousWithinAt

lemma p19lR1_abs_sin_ge {d : ℝ} (h1 : -(π / 2) ≤ d) (h2 : d ≤ π / 2) :
    2 / π * |d| ≤ |Real.sin d| := by
  rcases le_or_gt 0 d with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith))]
    exact Real.mul_le_sin h h2
  · have h3 := Real.mul_le_sin (x := -d) (by linarith) (by linarith)
    rw [Real.sin_neg] at h3
    have h4 : 0 < 2 / π * -d := mul_pos (by positivity) (by linarith)
    rw [abs_of_neg h, abs_of_neg (by linarith)]
    exact h3

lemma p19lR1_sin_sq_sub_lower {θ₀ : ℝ} (h0 : 0 < θ₀) (h1 : θ₀ < π / 2) :
    ∃ C > 0, ∀ θ ∈ Icc 0 (π / 2), C * |θ - θ₀| ≤ |Real.sin θ₀ ^ 2 - Real.sin θ ^ 2| := by
  set m := 2 / π * min θ₀ (π / 2 - θ₀) with hm
  have hm0 : 0 < m := mul_pos (by positivity) (lt_min h0 (by linarith))
  refine ⟨2 / π * m, by positivity, fun θ hθ => ?_⟩
  have hid : Real.sin θ₀ ^ 2 - Real.sin θ ^ 2 = Real.sin (θ₀ - θ) * Real.sin (θ₀ + θ) := by
    rw [Real.sin_sub, Real.sin_add]
    linear_combination Real.sin θ ^ 2 * Real.sin_sq_add_cos_sq θ₀ -
      Real.sin θ₀ ^ 2 * Real.sin_sq_add_cos_sq θ
  have hs1 : 2 / π * |θ - θ₀| ≤ |Real.sin (θ₀ - θ)| := by
    rw [abs_sub_comm]; exact p19lR1_abs_sin_ge (by linarith [hθ.2]) (by linarith [hθ.1])
  have hs2 : m ≤ |Real.sin (θ₀ + θ)| := by
    have hx0 : 0 ≤ θ₀ + θ := by linarith [hθ.1]
    rcases le_or_gt (θ₀ + θ) (π / 2) with hx | hx
    · rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith))]
      refine le_trans ?_ (Real.mul_le_sin hx0 hx)
      rw [hm]; gcongr; exact (min_le_left _ _).trans (by linarith [hθ.1])
    · rw [← Real.sin_pi_sub, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith [hθ.2]) (by linarith))]
      refine le_trans ?_ (Real.mul_le_sin (by linarith [hθ.2]) (by linarith))
      rw [hm]; gcongr; exact (min_le_right _ _).trans (by linarith [hθ.2])
  rw [hid, abs_mul]
  calc 2 / π * m * |θ - θ₀| = (2 / π * |θ - θ₀|) * m := by ring
    _ ≤ |Real.sin (θ₀ - θ)| * |Real.sin (θ₀ + θ)| :=
      mul_le_mul hs1 hs2 hm0.le (abs_nonneg _)

lemma p19lR1_intervalIntegrable_abs_sub_rpow {θ₀ : ℝ} (h0 : 0 ≤ θ₀) (h1 : θ₀ ≤ π / 2) :
    IntervalIntegrable (fun θ : ℝ => |θ - θ₀| ^ (-(1 / 2) : ℝ)) volume 0 (π / 2) := by
  have hr : (-1 : ℝ) < -(1 / 2) := by norm_num
  refine (?_ : IntervalIntegrable _ volume 0 θ₀).trans (?_ : IntervalIntegrable _ volume θ₀ (π / 2))
  · have h := ((intervalIntegral.intervalIntegrable_rpow' hr (a := 0) (b := θ₀)).comp_sub_left θ₀
      (by simp)).symm
    simp only [sub_zero, sub_self] at h
    refine h.congr fun x hx => ?_
    rw [uIoc_of_le h0] at hx
    rw [abs_of_nonpos (by linarith [hx.2])]; ring_nf
  · have h := (intervalIntegral.intervalIntegrable_rpow' hr (a := 0) (b := π / 2 - θ₀)).comp_sub_right
      θ₀ (by simp)
    simp only [zero_add, sub_add_cancel] at h
    refine h.congr fun x hx => ?_
    rw [uIoc_of_le h1] at hx
    rw [abs_of_nonneg (by linarith [hx.1])]

lemma p19lR1_intervalIntegrable_dom {a : ℝ} (ha : 1 < a) :
    IntervalIntegrable (fun θ : ℝ => |1 - a * Real.sin θ ^ 2| ^ (-(1 / 2) : ℝ)) volume 0 (π / 2) := by
  set θ₀ := Real.arcsin (1 / Real.sqrt a) with hθ₀
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 (by linarith)
  have hsa1 : 1 < Real.sqrt a := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) ha
  have hu0 : 0 < 1 / Real.sqrt a := by positivity
  have hu1 : 1 / Real.sqrt a < 1 := by rw [div_lt_one hsa]; exact hsa1
  have h0 : 0 < θ₀ := Real.arcsin_pos.2 hu0
  have h1 : θ₀ < π / 2 := Real.arcsin_lt_pi_div_two.2 hu1
  have hsin : Real.sin θ₀ ^ 2 = 1 / a := by
    rw [hθ₀, Real.sin_arcsin (by linarith) hu1.le, div_pow, Real.sq_sqrt (by linarith)]; ring
  obtain ⟨C, hC, hCb⟩ := p19lR1_sin_sq_sub_lower h0 h1
  have hint := (p19lR1_intervalIntegrable_abs_sub_rpow h0.le h1.le).const_mul
    ((a * C) ^ (-(1 / 2) : ℝ))
  refine hint.mono_fun ?_ ?_
  · exact ((continuous_const.sub (continuous_const.mul
      (Real.continuous_sin.pow 2))).abs.measurable.pow_const _).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_uIoc fun θ hθ => ?_
    rw [uIoc_of_le (by positivity)] at hθ
    have hθ' : θ ∈ Icc 0 (π / 2) := ⟨hθ.1.le, hθ.2⟩
    dsimp only
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    rcases eq_or_ne θ θ₀ with he | he
    · rw [he, show 1 - a * Real.sin θ₀ ^ 2 = 0 by rw [hsin]; field_simp; ring, abs_zero,
        Real.zero_rpow (by norm_num)]
      positivity
    · have hd : 0 < |θ - θ₀| := abs_pos.2 (sub_ne_zero.2 he)
      have hw : a * C * |θ - θ₀| ≤ |1 - a * Real.sin θ ^ 2| := by
        have : 1 - a * Real.sin θ ^ 2 = a * (Real.sin θ₀ ^ 2 - Real.sin θ ^ 2) := by
          rw [hsin]; field_simp
        rw [this, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < a), mul_assoc]
        exact mul_le_mul_of_nonneg_left (hCb θ hθ') (by linarith)
      calc |1 - a * Real.sin θ ^ 2| ^ (-(1 / 2) : ℝ) ≤ (a * C * |θ - θ₀|) ^ (-(1 / 2) : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hw (by norm_num)
        _ = (a * C) ^ (-(1 / 2) : ℝ) * |θ - θ₀| ^ (-(1 / 2) : ℝ) :=
            Real.mul_rpow (by positivity) (abs_nonneg _)

lemma p19lR1_ae_ne_zero_cut {a : ℝ} (ha : 1 < a) :
    ∀ᵐ θ : ℝ, θ ∈ uIoc (0 : ℝ) (π / 2) → 1 - a * Real.sin θ ^ 2 ≠ 0 := by
  filter_upwards [Measure.ae_ne volume (Real.arcsin (1 / Real.sqrt a))] with θ hne hθ h
  rw [uIoc_of_le (by positivity)] at hθ
  apply hne
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, Real.pi_pos])
  have hsq : Real.sin θ ^ 2 = 1 / a := by field_simp; linarith
  have hs : Real.sin θ = 1 / Real.sqrt a := by
    rw [← Real.sqrt_sq hs0, hsq, Real.sqrt_div' _ (by linarith : (0 : ℝ) ≤ a), Real.sqrt_one]
  rw [← hs, Real.arcsin_sin (by linarith [hθ.1, Real.pi_pos]) hθ.2]

lemma p19lR1_tendsto_integral_cut {a : ℝ} (ha : 1 < a) {ρ : ℝ} (hρ : ρ = -(1 / 2) ∨ ρ = 1 / 2) :
    Tendsto (fun η : ℝ => ∫ θ in (0 : ℝ)..(π / 2),
        (1 - ((a : ℂ) - I * η) * (Real.sin θ : ℂ) ^ 2) ^ (ρ : ℂ)) (𝓝[>] 0)
      (𝓝 (∫ θ in (0 : ℝ)..(π / 2), (1 - (a : ℂ) * (Real.sin θ : ℂ) ^ 2) ^ (ρ : ℂ))) := by
  have hre : ∀ (η θ : ℝ), (1 - ((a : ℂ) - I * η) * (Real.sin θ : ℂ) ^ 2) =
      ((1 - a * Real.sin θ ^ 2 : ℝ) : ℂ) + I * ((η * Real.sin θ ^ 2 : ℝ) : ℂ) := by
    intro η θ; push_cast; ring
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun θ => (a + 3) + |1 - a * Real.sin θ ^ 2| ^ (-(1 / 2) : ℝ)) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun η => ?_
    exact (Measurable.pow_const (by fun_prop) _).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with η hη
    filter_upwards [p19lR1_ae_ne_zero_cut ha] with θ hθw hθ
    have hw := hθw hθ
    rw [hre, norm_cpow_real]
    set z : ℂ := ((1 - a * Real.sin θ ^ 2 : ℝ) : ℂ) + I * ((η * Real.sin θ ^ 2 : ℝ) : ℂ)
    have hzre : z.re = 1 - a * Real.sin θ ^ 2 := by
      simp only [z, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]; ring
    have hzim : z.im = η * Real.sin θ ^ 2 := by
      simp only [z, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]; ring
    have hs1 := Real.sin_sq_le_one θ
    have hs0 := sq_nonneg (Real.sin θ)
    have hlow : |1 - a * Real.sin θ ^ 2| ≤ ‖z‖ := hzre ▸ abs_re_le_norm z
    have hup : ‖z‖ ≤ a + 2 := by
      refine (norm_le_abs_re_add_abs_im z).trans ?_
      rw [hzre, hzim]
      have h1 : |1 - a * Real.sin θ ^ 2| ≤ 1 + a := abs_le.2 ⟨by nlinarith, by nlinarith⟩
      have h2 : |η * Real.sin θ ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (by nlinarith [hη.1])]; nlinarith [hη.2, hη.1]
      linarith
    have hpos : 0 ≤ |1 - a * Real.sin θ ^ 2| ^ (-(1 / 2) : ℝ) := by positivity
    rcases hρ with rfl | rfl
    · have := Real.rpow_le_rpow_of_nonpos (abs_pos.2 hw) hlow (by norm_num : (-(1 / 2) : ℝ) ≤ 0)
      linarith
    · have : ‖z‖ ^ (1 / 2 : ℝ) ≤ ‖z‖ + 1 := by
        rcases le_or_gt ‖z‖ 1 with h | h
        · have := Real.rpow_le_one (norm_nonneg z) h (by norm_num : (0 : ℝ) ≤ 1 / 2)
          linarith [norm_nonneg z]
        · have := Real.rpow_le_rpow_of_exponent_le h.le (by norm_num : (1 / 2 : ℝ) ≤ 1)
          rw [Real.rpow_one] at this; linarith
      linarith
  · exact intervalIntegrable_const.add (p19lR1_intervalIntegrable_dom ha)
  · filter_upwards [p19lR1_ae_ne_zero_cut ha] with θ hθw hθ
    have hw := hθw hθ
    have hf : (1 - (a : ℂ) * (Real.sin θ : ℂ) ^ 2) = ((1 - a * Real.sin θ ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    simp only [hre, hf]
    refine (p19lR1_cpow_cwa_upper hw _).tendsto.comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous fun η : ℝ => ((1 - a * Real.sin θ ^ 2 : ℝ) : ℂ) +
          I * ((η * Real.sin θ ^ 2 : ℝ) : ℂ) := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with η hη
      simp only [add_im, ofReal_im, mul_im, I_re, ofReal_re, zero_mul, I_im,
        one_mul, zero_add]
      exact mul_nonneg (le_of_lt hη) (sq_nonneg _)

lemma p19lR1_W_eq (k : ℂ) : p19lR1_W k =
    compEllIntEk k * (∫ θ in (0 : ℝ)..(π / 2),
      (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ ((-(1 / 2) : ℝ) : ℂ)) +
    (∫ θ in (0 : ℝ)..(π / 2), (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ ((1 / 2 : ℝ) : ℂ)) *
      compEllIntKk k -
    compEllIntKk k * (∫ θ in (0 : ℝ)..(π / 2),
      (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ ((-(1 / 2) : ℝ) : ℂ)) := by
  have hK : compEllIntKk (jacobiComodulusk k) = ∫ θ in (0 : ℝ)..(π / 2),
      (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ ((-(1 / 2) : ℝ) : ℂ) := by
    unfold compEllIntKk; rw [ei19a_jacobiComodulusk_sq]; push_cast; rfl
  have hE : compEllIntEk (jacobiComodulusk k) = ∫ θ in (0 : ℝ)..(π / 2),
      (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ ((1 / 2 : ℝ) : ℂ) := by
    rw [compEllIntEk_eq_integral, ei19a_jacobiComodulusk_sq]; push_cast; rfl
  rw [p19lR1_W, hK, hE]

lemma p19lR1_W_imag {y : ℝ} (hy : 0 < y) : p19lR1_W (I * y) = π / 2 := by
  set kε : ℝ → ℂ := fun ε => (ε : ℂ) + I * (Real.sqrt (y ^ 2 + ε ^ 2) : ℂ) with hkε
  set η : ℝ → ℝ := fun ε => 2 * ε * Real.sqrt (y ^ 2 + ε ^ 2) with hη
  set a : ℝ := 1 + y ^ 2 with ha
  have ha1 : 1 < a := by rw [ha]; nlinarith
  have hsq : ∀ ε : ℝ, Real.sqrt (y ^ 2 + ε ^ 2) ^ 2 = y ^ 2 + ε ^ 2 :=
    fun ε => Real.sq_sqrt (by positivity)
  have hspos : ∀ ε : ℝ, 0 < Real.sqrt (y ^ 2 + ε ^ 2) := fun ε => Real.sqrt_pos.2 (by positivity)
  have h1k : ∀ ε : ℝ, 1 - kε ε ^ 2 = (a : ℂ) - I * (η ε : ℂ) := by
    intro ε
    have h := hsq ε
    have h' : (Real.sqrt (y ^ 2 + ε ^ 2) : ℂ) ^ 2 = (y : ℂ) ^ 2 + (ε : ℂ) ^ 2 := by exact_mod_cast h
    simp only [hkε, hη, ha]; push_cast
    linear_combination (-1 : ℂ) * h' * I ^ 2 + (-(y : ℂ) ^ 2 - (ε : ℂ) ^ 2) * I_sq
  have h1I : 1 - (I * (y : ℂ)) ^ 2 = (a : ℂ) := by
    rw [ha, mul_pow, I_sq]; push_cast; ring
  have hU : 1 - (I * (y : ℂ)) ^ 2 ∈ slitPlane := by
    rw [h1I]; exact ofReal_mem_slitPlane.2 (by linarith)
  have hcont : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f {k : ℂ | 1 - k ^ 2 ∈ slitPlane} →
      Tendsto (fun ε => f (kε ε)) (𝓝[>] 0) (𝓝 (f (I * y))) := by
    intro f hf
    have hfc : ContinuousAt f (I * y) :=
      (hf.differentiableAt (p19lR1_isOpen_U.mem_nhds hU)).continuousAt
    have hk : Tendsto kε (𝓝[>] 0) (𝓝 (I * y)) := by
      have hc : Continuous kε := by rw [hkε]; fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      convert this using 2
      simp only [hkε, ofReal_zero, zero_add]
      rw [show y ^ 2 + (0 : ℝ) ^ 2 = y ^ 2 by ring, Real.sqrt_sq hy.le]
    exact hfc.tendsto.comp hk
  have hηt : Tendsto η (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous η := by rw [hη]; fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa [hη] using this
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos (mul_pos two_pos hε) (hspos ε)
  have hD := differentiableOn_compEllIntKk_compEllIntEk
  have hKc := (p19lR1_tendsto_integral_cut ha1 (ρ := -(1 / 2)) (Or.inl rfl)).comp hηt
  have hEc := (p19lR1_tendsto_integral_cut ha1 (ρ := 1 / 2) (Or.inr rfl)).comp hηt
  have hT : Tendsto (fun ε => p19lR1_W (kε ε)) (𝓝[>] 0) (𝓝 (p19lR1_W (I * y))) := by
    simp only [p19lR1_W_eq, h1k, h1I]
    exact (((hcont _ hD.2).mul hKc).add (hEc.mul (hcont _ hD.1))).sub ((hcont _ hD.1).mul hKc)
  have hconst : ∀ᶠ ε in 𝓝[>] (0 : ℝ), p19lR1_W (kε ε) = π / 2 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    refine p19lR1_W_of_re_pos (by simpa [hkε] using hε) ?_
    rw [p19lR1_one_sub_sq_mem_iff]; left
    simpa [hkε] using (hspos ε).ne'
  exact tendsto_nhds_unique hT (tendsto_const_nhds.congr' (hconst.mono fun ε h => h.symm))

/-- DLMF 19.7.1 (Legendre's relation) for complex `k` with `k ∉ (-∞, 0]` and
`k² ∉ [1, ∞)`: `E(k)K'(k) + E'(k)K(k) - K(k)K'(k) = π/2` (with DLMF's continued `K'`, `E'`). -/
@[dlmf 19.7.E1]
theorem legendre_relation_complex {k : ℂ} (hk : k ∈ slitPlane) (hk1 : 1 - k ^ 2 ∈ slitPlane) :
    compEllIntEk k * cCompEllIntKk k + cCompEllIntEk k * compEllIntKk k -
      compEllIntKk k * cCompEllIntKk k = π / 2 := by
  rw [p19lR1_legendre_eq_W]
  rcases lt_trichotomy k.re 0 with h | h | h
  · rw [← p19lR1_W_neg]
    exact p19lR1_W_of_re_pos (by simpa using h) (by simpa using hk1)
  · have him : k.im ≠ 0 := by
      intro h'; exact slitPlane_ne_zero hk (Complex.ext h h')
    rcases him.lt_or_gt with h' | h'
    · rw [← p19lR1_W_neg]
      have : -k = I * ((-k.im : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [h]
      rw [this]; exact p19lR1_W_imag (by linarith)
    · have : k = I * ((k.im : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [h]
      rw [this]; exact p19lR1_W_imag h'
  · exact p19lR1_W_of_re_pos h hk1

/-- DLMF 19.7.2 (first and third formulas): `K(ik/k') = k'K(k)` and
`E(ik/k') = (1/k')E(k)` in the principal domain `1 - k² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.7.E2]
theorem compEllInt_imaginary_modulus {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    compEllIntKk (I * k / jacobiComodulusk k) = jacobiComodulusk k * compEllIntKk k ∧
      compEllIntEk (I * k / jacobiComodulusk k) = compEllIntEk k / jacobiComodulusk k :=
  p19lR1_imag_modulus hk

/-- DLMF 19.7.2 (second and fourth formulas), with the implicit condition `Re k > 0`
(see the module docstring): `K(-ik'/k) = kK(k')` and `E(-ik'/k) = (1/k)E(k')`, for
`k² ∉ (-∞, 0]`. -/
@[dlmf 19.7.E2]
theorem compEllInt_imaginary_comodulus {k : ℂ} (hk : 0 < k.re) (hk2 : k ^ 2 ∈ slitPlane) :
    compEllIntKk (-I * jacobiComodulusk k / k) = k * compEllIntKk (jacobiComodulusk k) ∧
      compEllIntEk (-I * jacobiComodulusk k / k) = compEllIntEk (jacobiComodulusk k) / k :=
  p19lR1_imag_comodulus hk hk2

/-- **Admitted.** DLMF 19.7.3 (Fettis): for `Re k > 0` and `Im k² ≠ 0`, with `s = 1` if
`Im k² > 0` and `s = -1` if `Im k² < 0` (DLMF's upper/lower signs),
`K(1/k) = k(K(k) - s i K(k'))`, `K(1/k') = k'(K(k') + s i K(k))`,
`E(1/k) = (1/k)(E(k) + s i E(k') - k'²K(k) - s i k² K(k'))`,
`E(1/k') = (1/k')(E(k') - s i E(k) - k²K(k') + s i k'² K(k))`. -/
@[dlmf 19.7.E3]
theorem compEllInt_reciprocal_modulus {k : ℂ} (hk : 0 < k.re) {s : ℂ}
    (hs : (0 < (k ^ 2).im ∧ s = 1) ∨ ((k ^ 2).im < 0 ∧ s = -1)) :
    compEllIntKk (1 / k) = k * (compEllIntKk k - s * I * compEllIntKk (jacobiComodulusk k)) ∧
      compEllIntKk (1 / jacobiComodulusk k) = jacobiComodulusk k *
        (compEllIntKk (jacobiComodulusk k) + s * I * compEllIntKk k) ∧
      compEllIntEk (1 / k) = (1 / k) * (compEllIntEk k + s * I * compEllIntEk (jacobiComodulusk k) -
        (1 - k ^ 2) * compEllIntKk k - s * I * k ^ 2 * compEllIntKk (jacobiComodulusk k)) ∧
      compEllIntEk (1 / jacobiComodulusk k) = (1 / jacobiComodulusk k) *
        (compEllIntEk (jacobiComodulusk k) - s * I * compEllIntEk k -
          k ^ 2 * compEllIntKk (jacobiComodulusk k) + s * I * (1 - k ^ 2) * compEllIntKk k) := by
  sorry

/-! ### §19.7(ii) Change of modulus and amplitude -/

/-! ### Helpers for 19.7.4 (substitution `θ = arcsin (k sin ψ)`) -/

lemma p19lR1_ofReal_cpow_half {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((Real.sqrt x)⁻¹ : ℝ) ∧ (x : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℝ) := by
  constructor
  · rw [show -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx,
      Real.rpow_neg hx, ← Real.sqrt_eq_rpow]
  · rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx,
      ← Real.sqrt_eq_rpow]

lemma p19lR1_sin_sq_le_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π / 2) :
    Real.sin x ^ 2 ≤ Real.sin y ^ 2 := by
  have h1 : Real.sin x ≤ Real.sin y :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hy hxy
  have h0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_pos])
  nlinarith

/-- `Π` for real data with `α² sin²φ < 1` on `0 ≤ φ ≤ π/2` needs no principal value. -/
lemma p19lR1_Pi_ofReal_of_lt {φ α2 : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ π / 2)
    (hα : α2 * Real.sin φ ^ 2 < 1) (k : ℂ) :
    incEllIntPik φ α2 k = ∫ θ in (0 : ℝ)..φ, ((1 - α2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
  rw [incEllIntPik_eq_segmentIntegral (δ := min 1 (1 - α2 * Real.sin φ ^ 2))
    (lt_min one_pos (by linarith)), ei19a_segmentIntegral_ofReal]
  · simp only [← Complex.ofReal_sin]
  · intro t ht
    have hs := p19lR1_sin_sq_le_of_le (x := t * φ) (y := φ) (by nlinarith [ht.1])
      (by nlinarith [ht.2]) hφ1
    have hs0 := sq_nonneg (Real.sin (t * φ))
    have hre : (1 - (α2 : ℂ) * Complex.sin (t * φ) ^ 2) =
        ((1 - α2 * Real.sin (t * φ) ^ 2 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hre, Complex.norm_real, Real.norm_eq_abs]
    have hpos : min 1 (1 - α2 * Real.sin φ ^ 2) ≤ 1 - α2 * Real.sin (t * φ) ^ 2 := by
      rcases le_or_gt α2 0 with h | h
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (min_le_right _ _).trans (by nlinarith)
    exact hpos.trans (le_abs_self _)

/-- The substitution `θ = arcsin (k sin ψ)` on `[0, β]`. -/
lemma p19lR1_arcsin_subst {k β : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ π / 2)
    (g : ℝ → ℂ) :
    ∫ θ in (0 : ℝ)..(Real.arcsin (k * Real.sin β)), g θ =
      ∫ ψ in (0 : ℝ)..β, ((k * Real.cos ψ / Real.sqrt (1 - k ^ 2 * Real.sin ψ ^ 2) : ℝ) : ℂ) *
        g (Real.arcsin (k * Real.sin ψ)) := by
  have hb : ∀ ψ : ℝ, k * Real.sin ψ < 1 := fun ψ => by
    nlinarith [Real.sin_le_one ψ, Real.neg_one_le_sin ψ]
  have hb' : ∀ ψ : ℝ, -1 < k * Real.sin ψ := fun ψ => by
    nlinarith [Real.sin_le_one ψ, Real.neg_one_le_sin ψ]
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (a := 0) (b := β) (g := g)
    (f := fun ψ => Real.arcsin (k * Real.sin ψ))
    (f' := fun ψ => k * Real.cos ψ / Real.sqrt (1 - k ^ 2 * Real.sin ψ ^ 2))
    (by fun_prop)
    (fun ψ _ => by
      have := (Real.hasDerivAt_arcsin (hb' ψ).ne' (hb ψ).ne).comp ψ
        ((Real.hasDerivAt_sin ψ).const_mul k)
      refine this.congr_deriv ?_
      rw [mul_pow]; field_simp)
    (fun ψ hψ => by
      rw [min_eq_left hβ0, max_eq_right hβ0] at hψ
      have := Real.cos_nonneg_of_mem_Icc (x := ψ)
        ⟨by linarith [hψ.1, Real.pi_pos], by linarith [hψ.2]⟩
      exact div_nonneg (mul_nonneg hk0.le this) (Real.sqrt_nonneg _))
  simp only [Real.sin_zero, mul_zero, Real.arcsin_zero, real_smul, Function.comp] at h
  exact h.symm

lemma p19lR1_recip_modulus {k β φ α2 : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ π / 2) (hφ : Real.arcsin (k * Real.sin β) = φ) (hα : α2 * Real.sin φ ^ 2 < 1) :
    incEllIntFk φ (1 / k : ℝ) = k * incEllIntFk β k ∧
      incEllIntEk φ (1 / k : ℝ) = (incEllIntEk β k - (1 - k ^ 2 : ℝ) * incEllIntFk β k) / k ∧
      incEllIntPik φ α2 (1 / k : ℝ) = k * incEllIntPik β (k ^ 2 * α2 : ℝ) k := by
  subst hφ
  have hb : ∀ ψ : ℝ, k * Real.sin ψ ≤ 1 := fun ψ => by
    nlinarith [Real.sin_le_one ψ, Real.neg_one_le_sin ψ]
  have hb' : ∀ ψ : ℝ, -1 ≤ k * Real.sin ψ := fun ψ => by
    nlinarith [Real.sin_le_one ψ, Real.neg_one_le_sin ψ]
  have hsin : ∀ ψ, Real.sin (Real.arcsin (k * Real.sin ψ)) = k * Real.sin ψ :=
    fun ψ => Real.sin_arcsin (hb' ψ) (hb ψ)
  have hk0' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hspos : ∀ ψ : ℝ, 0 < 1 - k ^ 2 * Real.sin ψ ^ 2 := fun ψ => by
    nlinarith [Real.sin_sq_le_one ψ, sq_nonneg (Real.sin ψ), mul_pos hk0 hk0]
  set s : ℝ → ℝ := fun ψ => Real.sqrt (1 - k ^ 2 * Real.sin ψ ^ 2) with hs
  have hs0 : ∀ ψ, 0 < s ψ := fun ψ => Real.sqrt_pos.2 (hspos ψ)
  have hs2 : ∀ ψ, s ψ ^ 2 = 1 - k ^ 2 * Real.sin ψ ^ 2 := fun ψ => Real.sq_sqrt (hspos ψ).le
  have hsc : Continuous s := by rw [hs]; fun_prop
  have hΔ : ∀ ψ : ℝ, (1 - (k : ℂ) ^ 2 * (Real.sin ψ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = ((s ψ)⁻¹ : ℝ) ∧
      (1 - (k : ℂ) ^ 2 * (Real.sin ψ : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (s ψ : ℝ) := by
    intro ψ
    have e : (1 - (k : ℂ) ^ 2 * (Real.sin ψ : ℂ) ^ 2) = ((1 - k ^ 2 * Real.sin ψ ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]; exact p19lR1_ofReal_cpow_half (hspos ψ).le
  -- on `0 < ψ < π/2`, the reciprocal-modulus integrand
  have hcos : ∀ ψ : ℝ, 0 < Real.cos ψ →
      (1 - ((1 / k : ℝ) : ℂ) ^ 2 * (Real.sin (Real.arcsin (k * Real.sin ψ)) : ℂ) ^ 2) ^
        (-(1 / 2 : ℂ)) = ((Real.cos ψ)⁻¹ : ℝ) ∧
      (1 - ((1 / k : ℝ) : ℂ) ^ 2 * (Real.sin (Real.arcsin (k * Real.sin ψ)) : ℂ) ^ 2) ^
        (1 / 2 : ℂ) = (Real.cos ψ : ℝ) := by
    intro ψ hc
    have e : (1 - ((1 / k : ℝ) : ℂ) ^ 2 * (Real.sin (Real.arcsin (k * Real.sin ψ)) : ℂ) ^ 2) =
        ((Real.cos ψ ^ 2 : ℝ) : ℂ) := by
      have er : 1 - (1 / k) ^ 2 * Real.sin (Real.arcsin (k * Real.sin ψ)) ^ 2 = Real.cos ψ ^ 2 := by
        rw [hsin]; field_simp; nlinarith [Real.sin_sq_add_cos_sq ψ]
      rw [← er]; simp only [ofReal_sub, ofReal_one, ofReal_mul, ofReal_pow]
    rw [e, (p19lR1_ofReal_cpow_half (sq_nonneg _)).1, (p19lR1_ofReal_cpow_half (sq_nonneg _)).2,
      Real.sqrt_sq hc.le]
    exact ⟨rfl, rfl⟩
  have hae : ∀ᵐ ψ : ℝ, ψ ∈ uIoc 0 β → 0 < Real.cos ψ := by
    filter_upwards [Measure.ae_ne volume (π / 2)] with ψ hne hψ
    rw [uIoc_of_le hβ0] at hψ
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hψ.1, Real.pi_pos],
      lt_of_le_of_ne (hψ.2.trans hβ1) hne⟩
  have hφ0 : 0 ≤ Real.arcsin (k * Real.sin β) :=
    Real.arcsin_nonneg.2 (mul_nonneg hk0.le (Real.sin_nonneg_of_nonneg_of_le_pi hβ0
      (by linarith [Real.pi_pos])))
  have hφ1 : Real.arcsin (k * Real.sin β) ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hsint : IntervalIntegrable (fun ψ => ((s ψ : ℝ) : ℂ)) volume 0 β :=
    (continuous_ofReal.comp hsc).intervalIntegrable _ _
  have hsiint : IntervalIntegrable (fun ψ => (((s ψ)⁻¹ : ℝ) : ℂ)) volume 0 β :=
    (continuous_ofReal.comp (hsc.inv₀ fun ψ => (hs0 ψ).ne')).intervalIntegrable _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [incEllIntFk_ofReal_eq_integral, p19lR1_arcsin_subst hk0 hk1 hβ0 hβ1,
      incEllIntFk_ofReal_eq_integral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with ψ hψ hmem
    have hc := hψ hmem
    rw [(hcos ψ hc).1, (hΔ ψ).1, ← ofReal_mul, ← ofReal_mul]
    congr 1
    have := (Real.sqrt_pos.2 (hspos ψ)).ne'
    simp only [hs]
    field_simp
  · have hrhs : incEllIntEk β k - (1 - k ^ 2 : ℝ) * incEllIntFk β k =
        ∫ ψ in (0 : ℝ)..β, ((k ^ 2 * Real.cos ψ ^ 2 / s ψ : ℝ) : ℂ) := by
      rw [incEllIntEk_ofReal_eq_integral, incEllIntFk_ofReal_eq_integral]
      simp only [fun ψ => (hΔ ψ).1, fun ψ => (hΔ ψ).2]
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hsint
        (hsiint.const_mul _)]
      refine intervalIntegral.integral_congr fun ψ _ => ?_
      have h0 := (hs0 ψ).ne'
      have h2 := hs2 ψ
      rw [show ((1 - k ^ 2 : ℝ) : ℂ) * (((s ψ)⁻¹ : ℝ) : ℂ) = (((1 - k ^ 2) * (s ψ)⁻¹ : ℝ) : ℂ) by
        push_cast; ring, ← ofReal_sub]
      congr 1
      rw [Real.cos_sq']
      field_simp
      linear_combination h2
    rw [hrhs, incEllIntEk_ofReal_eq_integral, p19lR1_arcsin_subst hk0 hk1 hβ0 hβ1,
      ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with ψ hψ hmem
    have hc := hψ hmem
    rw [(hcos ψ hc).2, ← ofReal_mul, ← ofReal_div]
    congr 1
    have := (Real.sqrt_pos.2 (hspos ψ)).ne'
    simp only [hs]
    field_simp
  · have hαβ : (k ^ 2 * α2) * Real.sin β ^ 2 < 1 := by
      have := hα; rw [hsin] at this; nlinarith
    rw [p19lR1_Pi_ofReal_of_lt hφ0 hφ1 hα, p19lR1_arcsin_subst hk0 hk1 hβ0 hβ1,
      p19lR1_Pi_ofReal_of_lt hβ0 hβ1 hαβ, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with ψ hψ hmem
    have hc := hψ hmem
    rw [(hcos ψ hc).1, (hΔ ψ).1, hsin]
    rw [show (1 - (α2 : ℂ) * ((k * Real.sin ψ : ℝ) : ℂ) ^ 2)⁻¹ =
        (((1 - α2 * (k * Real.sin ψ) ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring,
      show (1 - ((k ^ 2 * α2 : ℝ) : ℂ) * (Real.sin ψ : ℂ) ^ 2)⁻¹ =
        (((1 - k ^ 2 * α2 * Real.sin ψ ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring]
    simp only [← ofReal_mul]
    congr 1
    have := (Real.sqrt_pos.2 (hspos ψ)).ne'
    simp only [hs]
    field_simp

/-- DLMF 19.7.4 (reciprocal-modulus transformation): for real `0 < k < 1`,
`k₁ = 1/k`, real `0 ≤ φ ≤ π/2` with `sin β = k₁ sin φ ≤ 1` (`β = arcsin(k₁ sin φ)`), and real
`α²` with `α² sin²φ < 1`,
`F(φ, k₁) = kF(β, k)`, `E(φ, k₁) = (E(β, k) - k'²F(β, k))/k`, `Π(φ, α², k₁) = kΠ(β, k²α², k)`. -/
@[dlmf 19.7.E4]
theorem incEllInt_reciprocal_modulus {k φ α2 : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) (hφk : Real.sin φ ≤ k) (hα : α2 * Real.sin φ ^ 2 < 1) :
    let β := Real.arcsin (Real.sin φ / k)
    incEllIntFk φ (1 / k : ℝ) = k * incEllIntFk β k ∧
      incEllIntEk φ (1 / k : ℝ) = (incEllIntEk β k - (1 - k ^ 2 : ℝ) * incEllIntFk β k) / k ∧
      incEllIntPik φ α2 (1 / k : ℝ) = k * incEllIntPik β (k ^ 2 * α2 : ℝ) k := by
  intro β
  have hs0 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos])
  have hu0 : 0 ≤ Real.sin φ / k := div_nonneg hs0 hk0.le
  have hu1 : Real.sin φ / k ≤ 1 := (div_le_one hk0).2 hφk
  have hβ0 : 0 ≤ β := Real.arcsin_nonneg.2 hu0
  have hβ1 : β ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hφ : Real.arcsin (k * Real.sin β) = φ := by
    rw [Real.sin_arcsin (by linarith) hu1, mul_div_cancel₀ _ hk0.ne',
      Real.arcsin_sin (by linarith [Real.pi_pos]) hφ1]
  exact p19lR1_recip_modulus hk0 hk1 hβ0 hβ1 hφ hα

/-! ### Helpers for 19.7.5–19.7.6 (substitution `tan θ = √(1+k²) tan u`) -/

/-- The amplitude map of 19.7.5, `T(u) = arcsin (√(1+k²) sin u / √(1 + k² sin²u))`. -/
noncomputable def p19lR1_T (k u : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt (1 + k ^ 2) * Real.sin u / Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2))

lemma p19lR1_w_pos (k u : ℝ) : 0 < 1 + k ^ 2 * Real.sin u ^ 2 := by positivity

lemma p19lR1_T_arg_le (k u : ℝ) :
    (Real.sqrt (1 + k ^ 2) * Real.sin u / Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2)) ^ 2 ≤ 1 := by
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    div_le_one (by positivity)]
  nlinarith [Real.sin_sq_le_one u, sq_nonneg k, sq_nonneg (Real.sin u)]

lemma p19lR1_sin_T (k u : ℝ) :
    Real.sin (p19lR1_T k u) =
      Real.sqrt (1 + k ^ 2) * Real.sin u / Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) := by
  have h := p19lR1_T_arg_le k u
  rw [p19lR1_T, Real.sin_arcsin (by nlinarith [sq_nonneg (Real.sqrt (1 + k ^ 2) * Real.sin u /
    Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) + 1)]) (by nlinarith [sq_nonneg (Real.sqrt (1 + k ^ 2) *
    Real.sin u / Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) - 1)])]

lemma p19lR1_T_eq_arctan (k : ℝ) {u : ℝ} (hu : u ∈ Ioo (-(π / 2)) (π / 2)) :
    p19lR1_T k u = Real.arctan (Real.sqrt (1 + k ^ 2) * Real.tan u) := by
  have hc := Real.cos_pos_of_mem_Ioo hu
  have hw := p19lR1_w_pos k u
  rw [Real.arctan_eq_arcsin, p19lR1_T]
  congr 1
  have h1 : 1 + (Real.sqrt (1 + k ^ 2) * Real.tan u) ^ 2 =
      (Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) / Real.cos u) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hw.le, Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq u]
  rw [h1, Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) hc.le), Real.tan_eq_sin_div_cos]
  have := (Real.sqrt_pos.2 hw).ne'
  field_simp

lemma p19lR1_hasDerivAt_T (k : ℝ) {u : ℝ} (hu : u ∈ Ioo (-(π / 2)) (π / 2)) :
    HasDerivAt (p19lR1_T k) (Real.sqrt (1 + k ^ 2) / (1 + k ^ 2 * Real.sin u ^ 2)) u := by
  have hc := Real.cos_pos_of_mem_Ioo hu
  have h := (Real.hasDerivAt_arctan (Real.sqrt (1 + k ^ 2) * Real.tan u)).comp u
    ((Real.hasDerivAt_tan hc.ne').const_mul (Real.sqrt (1 + k ^ 2)))
  have heq : (fun v => Real.arctan (Real.sqrt (1 + k ^ 2) * Real.tan v)) =ᶠ[𝓝 u] p19lR1_T k := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    exact (p19lR1_T_eq_arctan k hv).symm
  refine (h.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  have hw := p19lR1_w_pos k u
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq u]

lemma p19lR1_continuous_T (k : ℝ) : Continuous (p19lR1_T k) := by
  unfold p19lR1_T
  refine Real.continuous_arcsin.comp ?_
  exact Continuous.div (by fun_prop) (by fun_prop) fun u => (Real.sqrt_pos.2 (p19lR1_w_pos k u)).ne'

lemma p19lR1_T_subst (k : ℝ) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ π / 2) (g : ℝ → ℂ) :
    ∫ θ in (0 : ℝ)..(p19lR1_T k φ), g θ =
      ∫ u in (0 : ℝ)..φ, ((Real.sqrt (1 + k ^ 2) / (1 + k ^ 2 * Real.sin u ^ 2) : ℝ) : ℂ) *
        g (p19lR1_T k u) := by
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (a := 0) (b := φ) (g := g)
    (f := p19lR1_T k) (f' := fun u => Real.sqrt (1 + k ^ 2) / (1 + k ^ 2 * Real.sin u ^ 2))
    (p19lR1_continuous_T k).continuousOn
    (fun u hu => by
      rw [min_eq_left hφ0, max_eq_right hφ0] at hu
      exact p19lR1_hasDerivAt_T k ⟨by linarith [hu.1, Real.pi_pos], by linarith [hu.2]⟩)
    (fun u _ => div_nonneg (Real.sqrt_nonneg _) (p19lR1_w_pos k u).le)
  have h0 : p19lR1_T k 0 = 0 := by simp [p19lR1_T]
  simp only [h0, real_smul, Function.comp] at h
  exact h.symm

lemma p19lR1_imod_pt (k u : ℝ) :
    (1 - (I * k) ^ 2 * (Real.sin u : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
        (((Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2))⁻¹ : ℝ) : ℂ) ∧
      (1 - (I * k) ^ 2 * (Real.sin u : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
        ((Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) : ℝ) : ℂ) ∧
      (1 - ((k / Real.sqrt (1 + k ^ 2) : ℝ) : ℂ) ^ 2 * (Real.sin (p19lR1_T k u) : ℂ) ^ 2) ^
          (-(1 / 2 : ℂ)) = ((Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) : ℝ) : ℂ) ∧
      (1 - ((k / Real.sqrt (1 + k ^ 2) : ℝ) : ℂ) ^ 2 * (Real.sin (p19lR1_T k u) : ℂ) ^ 2) ^
          (1 / 2 : ℂ) = (((Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2))⁻¹ : ℝ) : ℂ) := by
  have hw := p19lR1_w_pos k u
  have hW := Real.sqrt_pos.2 hw
  have hW2 := Real.sq_sqrt hw.le
  have hc := Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 1 + k ^ 2)
  have hc2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + k ^ 2)
  have e1 : (1 - (I * k) ^ 2 * (Real.sin u : ℂ) ^ 2) = ((1 + k ^ 2 * Real.sin u ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]; simp only [ofReal_add, ofReal_one, ofReal_mul, ofReal_pow]; ring
  have er : 1 - (k / Real.sqrt (1 + k ^ 2)) ^ 2 * Real.sin (p19lR1_T k u) ^ 2 =
      (Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) ^ 2)⁻¹ := by
    rw [p19lR1_sin_T, div_pow, div_pow, mul_pow, hc2, hW2]
    field_simp
    ring
  have e2 : (1 - ((k / Real.sqrt (1 + k ^ 2) : ℝ) : ℂ) ^ 2 * (Real.sin (p19lR1_T k u) : ℂ) ^ 2) =
      (((Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [← er]; simp only [ofReal_sub, ofReal_one, ofReal_mul, ofReal_pow]
  rw [e1, e2, (p19lR1_ofReal_cpow_half hw.le).1, (p19lR1_ofReal_cpow_half hw.le).2,
    (p19lR1_inv_sq_cpow hW).1, (p19lR1_inv_sq_cpow hW).2]
  push_cast
  exact ⟨rfl, rfl, rfl, rfl⟩

lemma p19lR1_alg_Pi {k α2 c W s : ℝ} (hc : 0 < c) (hW : 0 < W) (hc2 : c ^ 2 = 1 + k ^ 2)
    (hW2 : W ^ 2 = 1 + k ^ 2 * s ^ 2) (hd : 1 - α2 * s ^ 2 ≠ 0) (hαk : α2 + k ^ 2 ≠ 0) :
    (1 - α2 * s ^ 2)⁻¹ * W⁻¹ = (1 / c) / ((α2 + k ^ 2) / (1 + k ^ 2)) *
      ((k / c) ^ 2 * (c * W⁻¹) + ((1 / c) ^ 2 * α2) * (c * W / (1 - α2 * s ^ 2))) := by
  rw [← hc2]
  field_simp
  linear_combination (-(α2)) * hW2

lemma p19lR1_alg_E {k c J X Wφ sc : ℝ} (hc2 : c ^ 2 = 1 + k ^ 2) (hc : 0 < c) (hW : 0 < Wφ)
    (hX : X = k ^ 2 * sc / (c * Wφ)) :
    (1 + k ^ 2) * J - k ^ 2 * sc / Wφ = (1 / (1 / c)) * (c * J - X) := by
  rw [hX, ← hc2]; field_simp

lemma p19lR1_alg1 {a w : ℝ} (hw : 0 < w) (h : w ^ 2 = a) (c : ℝ) : c / a * w = c * w⁻¹ := by
  rw [← h]; field_simp

lemma p19lR1_alg2 {a w : ℝ} (hw : 0 < w) (h : w ^ 2 = a) (c : ℝ) :
    c / a * w⁻¹ = c * (w ^ 3)⁻¹ := by
  rw [← h]; field_simp

lemma p19lR1_alg_P {k α2 c W s : ℝ} (hc2 : c ^ 2 = 1 + k ^ 2) (hW : 0 < W)
    (hW2 : W ^ 2 = 1 + k ^ 2 * s ^ 2) (hd : 1 - α2 * s ^ 2 ≠ 0) :
    c / (1 + k ^ 2 * s ^ 2) * ((1 - (α2 + k ^ 2) / (1 + k ^ 2) * (c * s / W) ^ 2)⁻¹ * W) =
      c * W / (1 - α2 * s ^ 2) := by
  have h1 : 1 - (α2 + k ^ 2) / (1 + k ^ 2) * (c * s / W) ^ 2 = (1 - α2 * s ^ 2) / W ^ 2 := by
    rw [div_pow, mul_pow, hc2]
    have : (1 + k ^ 2) ≠ 0 := by positivity
    field_simp
    rw [hW2]; ring
  rw [h1, ← hW2]
  field_simp

lemma p19lR1_imod_X (k : ℝ) {φ : ℝ} (hφ1 : φ ≤ π / 2) (hφ0 : 0 ≤ φ) :
    (k / Real.sqrt (1 + k ^ 2)) ^ 2 * Real.sin (p19lR1_T k φ) * Real.cos (p19lR1_T k φ) /
        Real.sqrt (1 - (k / Real.sqrt (1 + k ^ 2)) ^ 2 * Real.sin (p19lR1_T k φ) ^ 2) =
      k ^ 2 * (Real.sin φ * Real.cos φ) /
        (Real.sqrt (1 + k ^ 2) * Real.sqrt (1 + k ^ 2 * Real.sin φ ^ 2)) := by
  set c := Real.sqrt (1 + k ^ 2) with hc
  set w := Real.sqrt (1 + k ^ 2 * Real.sin φ ^ 2) with hw
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 1 + k ^ 2 := Real.sq_sqrt (by positivity)
  have hw0 : 0 < w := Real.sqrt_pos.2 (p19lR1_w_pos k φ)
  have hw2 : w ^ 2 = 1 + k ^ 2 * Real.sin φ ^ 2 := Real.sq_sqrt (p19lR1_w_pos k φ).le
  have hs : Real.sin (p19lR1_T k φ) = c * Real.sin φ / w := p19lR1_sin_T k φ
  have hcφ : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
  have hcos : Real.cos (p19lR1_T k φ) = Real.cos φ / w := by
    have h1 : Real.cos (p19lR1_T k φ) = Real.sqrt (1 - (c * Real.sin φ / w) ^ 2) := by
      rw [p19lR1_T, Real.cos_arcsin]
    have h2 : 1 - (c * Real.sin φ / w) ^ 2 = (Real.cos φ / w) ^ 2 := by
      rw [div_pow, div_pow, mul_pow, hc2]
      field_simp
      rw [hw2]
      nlinarith [Real.sin_sq_add_cos_sq φ]
    rw [h1, h2, Real.sqrt_sq (div_nonneg hcφ hw0.le)]
  have hsq : Real.sqrt (1 - (k / c) ^ 2 * Real.sin (p19lR1_T k φ) ^ 2) = w⁻¹ := by
    have h2 : 1 - (k / c) ^ 2 * Real.sin (p19lR1_T k φ) ^ 2 = (w⁻¹) ^ 2 := by
      rw [hs, div_pow, div_pow, mul_pow, hc2]
      field_simp
      rw [hw2]
      ring
    rw [h2, Real.sqrt_sq (inv_nonneg.2 hw0.le)]
  rw [hsq, hs, hcos]
  field_simp

/-- DLMF 19.7.5–19.7.6 (imaginary-modulus transformation): for real `k`, real
`0 ≤ φ ≤ π/2` and real `α² < 1` with `α² + k² ≠ 0`, with `κ = k/√(1+k²)`, `κ' = 1/√(1+k²)`,
`sin θ = √(1+k²) sin φ/√(1 + k² sin²φ)` and `α₁² = (α² + k²)/(1 + k²)`:
`F(φ, ik) = κ'F(θ, κ)`,
`E(φ, ik) = (1/κ')(E(θ, κ) - κ² sin θ cos θ (1 - κ² sin²θ)^{-1/2})`,
`Π(φ, α², ik) = (κ'/α₁²)(κ²F(θ, κ) + κ'²α²Π(θ, α₁², κ))`. -/
@[dlmf 19.7.E5, dlmf 19.7.E6]
theorem incEllInt_imaginary_modulus {k φ α2 : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ π / 2) (hα : α2 < 1)
    (hαk : α2 + k ^ 2 ≠ 0) :
    let κ := k / Real.sqrt (1 + k ^ 2)
    let κ' := 1 / Real.sqrt (1 + k ^ 2)
    let θ := Real.arcsin (Real.sqrt (1 + k ^ 2) * Real.sin φ /
      Real.sqrt (1 + k ^ 2 * Real.sin φ ^ 2))
    let α12 := (α2 + k ^ 2) / (1 + k ^ 2)
    incEllIntFk φ (I * k) = κ' * incEllIntFk θ κ ∧
      incEllIntEk φ (I * k) = (1 / κ' : ℝ) * (incEllIntEk θ κ -
        (κ ^ 2 * Real.sin θ * Real.cos θ / Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2) : ℝ)) ∧
      incEllIntPik φ α2 (I * k) = (κ' / α12 : ℝ) *
        ((κ ^ 2 : ℝ) * incEllIntFk θ κ + (κ' ^ 2 * α2 : ℝ) * incEllIntPik θ α12 κ) := by
  intro κ κ' θ α12
  set c := Real.sqrt (1 + k ^ 2) with hc
  set W : ℝ → ℝ := fun u => Real.sqrt (1 + k ^ 2 * Real.sin u ^ 2) with hW
  have hθ : θ = p19lR1_T k φ := rfl
  have hκ : κ = k / c := rfl
  have hκ' : κ' = 1 / c := rfl
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 1 + k ^ 2 := Real.sq_sqrt (by positivity)
  have hW0 : ∀ u, 0 < W u := fun u => Real.sqrt_pos.2 (p19lR1_w_pos k u)
  have hW2 : ∀ u, W u ^ 2 = 1 + k ^ 2 * Real.sin u ^ 2 := fun u => Real.sq_sqrt (p19lR1_w_pos k u).le
  have hpt : ∀ u : ℝ, (1 - (I * k) ^ 2 * (Real.sin u : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
        (((W u)⁻¹ : ℝ) : ℂ) ∧
      (1 - (I * k) ^ 2 * (Real.sin u : ℂ) ^ 2) ^ (1 / 2 : ℂ) = ((W u : ℝ) : ℂ) ∧
      (1 - ((κ : ℝ) : ℂ) ^ 2 * (Real.sin (p19lR1_T k u) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
        ((W u : ℝ) : ℂ) ∧
      (1 - ((κ : ℝ) : ℂ) ^ 2 * (Real.sin (p19lR1_T k u) : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
        (((W u)⁻¹ : ℝ) : ℂ) := p19lR1_imod_pt k
  have hsub : ∀ g : ℝ → ℂ, ∫ x in (0 : ℝ)..θ, g x = ∫ u in (0 : ℝ)..φ,
      ((c / (1 + k ^ 2 * Real.sin u ^ 2) : ℝ) : ℂ) * g (p19lR1_T k u) :=
    p19lR1_T_subst k hφ0 hφ1
  have hθ0 : 0 ≤ θ := by
    rw [hθ, p19lR1_T]
    exact Real.arcsin_nonneg.2 (div_nonneg (mul_nonneg hc0.le
      (Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos]))) (hW0 φ).le)
  have hθ1 : θ ≤ π / 2 := Real.arcsin_le_pi_div_two _
  -- the first kind
  have hF1 : incEllIntFk φ (I * k) = ∫ u in (0 : ℝ)..φ, (((W u)⁻¹ : ℝ) : ℂ) := by
    rw [incEllIntFk_ofReal_eq_integral]
    exact intervalIntegral.integral_congr fun u _ => (hpt u).1
  have hF2 : incEllIntFk θ κ = ∫ u in (0 : ℝ)..φ, ((c * (W u)⁻¹ : ℝ) : ℂ) := by
    rw [incEllIntFk_ofReal_eq_integral, hsub]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [(hpt u).2.2.1, ← ofReal_mul]
    exact congrArg ofReal (p19lR1_alg1 (hW0 u) (hW2 u) c)
  refine ⟨?_, ?_, ?_⟩
  · rw [hF1, hF2, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_const_mul, ← ofReal_mul, hκ']
    congr 1
    field_simp
  · have hslit : 1 - (I * (k : ℂ)) ^ 2 ∈ slitPlane := by
      have : (1 - (I * (k : ℂ)) ^ 2) = ((1 + k ^ 2 : ℝ) : ℂ) := by
        rw [mul_pow, I_sq]; push_cast; ring
      rw [this]; exact ofReal_mem_slitPlane.2 (by positivity)
    have hcube := p19lR1_integral_cube hslit φ
    set J := ∫ u in (0 : ℝ)..φ, ((W u ^ 3)⁻¹ : ℝ) with hJ
    have hJ' : (∫ θ in (0 : ℝ)..φ, (1 - (I * (k : ℂ)) ^ 2 * (Real.sin θ : ℂ) ^ 2)⁻¹ *
        (1 - (I * (k : ℂ)) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) = (J : ℂ) := by
      rw [hJ, ← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [(hpt u).1]
      have e : (1 - (I * (k : ℂ)) ^ 2 * (Real.sin u : ℂ) ^ 2) = ((W u ^ 2 : ℝ) : ℂ) := by
        rw [hW2 u, mul_pow, I_sq]; simp only [ofReal_add, ofReal_one, ofReal_mul, ofReal_pow]; ring
      rw [e, ← ofReal_inv, ← ofReal_mul]
      congr 1
      have := (hW0 u).ne'
      field_simp
    have hΔφ : p19lR1_Δ (I * k) φ = (W φ : ℂ) := (hpt φ).2.1
    have hEφ : incEllIntEk φ (I * k) =
        (((1 + k ^ 2) * J - k ^ 2 * (Real.sin φ * Real.cos φ) / W φ : ℝ) : ℂ) := by
      have h1k : (1 : ℂ) - (I * k) ^ 2 = ((1 + k ^ 2 : ℝ) : ℂ) := by
        rw [mul_pow, I_sq]; push_cast; ring
      have h1k0 : ((1 + k ^ 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (0 : ℝ) < 1 + k ^ 2).ne'
      have hW0' : (W φ : ℂ) ≠ 0 := by exact_mod_cast (hW0 φ).ne'
      rw [hJ', hΔφ, h1k, eq_div_iff h1k0] at hcube
      rw [mul_pow, I_sq] at hcube
      push_cast at hcube ⊢
      linear_combination -hcube
    have hEθ : incEllIntEk θ κ = ((c * J : ℝ) : ℂ) := by
      rw [incEllIntEk_ofReal_eq_integral, hsub, hJ, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [(hpt u).2.2.2, ← ofReal_mul]
      exact congrArg ofReal (p19lR1_alg2 (hW0 u) (hW2 u) c)
    have hX : κ ^ 2 * Real.sin θ * Real.cos θ / Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2) =
        k ^ 2 * (Real.sin φ * Real.cos φ) / (c * W φ) := p19lR1_imod_X k hφ1 hφ0
    rw [hEφ, hEθ, hX, hκ']
    have := p19lR1_alg_E (J := J) (X := k ^ 2 * (Real.sin φ * Real.cos φ) / (c * W φ))
      (sc := Real.sin φ * Real.cos φ) hc2 hc0 (hW0 φ) rfl
    rw [this]
    push_cast; ring
  · have hden : ∀ u, 0 < 1 - α2 * Real.sin u ^ 2 := fun u => by
      rcases le_or_gt α2 0 with h | h
      · nlinarith [sq_nonneg (Real.sin u)]
      · nlinarith [Real.sin_sq_le_one u]
    have hα' : α2 * Real.sin φ ^ 2 < 1 := by linarith [hden φ]
    have hα12 : α12 * Real.sin θ ^ 2 < 1 := by
      have h12 : α12 < 1 := by
        show (α2 + k ^ 2) / (1 + k ^ 2) < 1
        rw [div_lt_one (by positivity)]; linarith
      rcases le_or_gt α12 0 with h | h
      · nlinarith [sq_nonneg (Real.sin θ)]
      · nlinarith [Real.sin_sq_le_one θ]
    have hP1 : incEllIntPik φ α2 (I * k) =
        ∫ u in (0 : ℝ)..φ, (((1 - α2 * Real.sin u ^ 2)⁻¹ * (W u)⁻¹ : ℝ) : ℂ) := by
      rw [p19lR1_Pi_ofReal_of_lt hφ0 hφ1 hα']
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [(hpt u).1, show (1 - (α2 : ℂ) * (Real.sin u : ℂ) ^ 2)⁻¹ =
        (((1 - α2 * Real.sin u ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring, ← ofReal_mul]
    have hP2 : incEllIntPik θ α12 κ =
        ∫ u in (0 : ℝ)..φ, ((c * W u / (1 - α2 * Real.sin u ^ 2) : ℝ) : ℂ) := by
      rw [p19lR1_Pi_ofReal_of_lt hθ0 hθ1 hα12, hsub]
      refine intervalIntegral.integral_congr fun u _ => ?_
      have hs : Real.sin (p19lR1_T k u) = c * Real.sin u / W u := p19lR1_sin_T k u
      rw [(hpt u).2.2.1, show (1 - (α12 : ℂ) * (Real.sin (p19lR1_T k u) : ℂ) ^ 2)⁻¹ =
        (((1 - α12 * Real.sin (p19lR1_T k u) ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_mul, ← ofReal_mul, hs]
      exact congrArg ofReal (p19lR1_alg_P hc2 (hW0 u) (hW2 u) (hden u).ne')
    have hBc : Continuous fun u => c * (W u)⁻¹ := by
      refine continuous_const.mul (Continuous.inv₀ ?_ fun u => (hW0 u).ne')
      rw [hW]; fun_prop
    have hCc : Continuous fun u => c * W u / (1 - α2 * Real.sin u ^ 2) := by
      refine Continuous.div (continuous_const.mul ?_) (by fun_prop) fun u => (hden u).ne'
      rw [hW]; fun_prop
    have key : (∫ u in (0 : ℝ)..φ, (1 - α2 * Real.sin u ^ 2)⁻¹ * (W u)⁻¹) =
        κ' / α12 * (κ ^ 2 * (∫ u in (0 : ℝ)..φ, c * (W u)⁻¹) +
          κ' ^ 2 * α2 * ∫ u in (0 : ℝ)..φ, c * W u / (1 - α2 * Real.sin u ^ 2)) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((hBc.intervalIntegrable _ _).const_mul _)
          ((hCc.intervalIntegrable _ _).const_mul _), ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u _ => ?_
      exact p19lR1_alg_Pi hc0 (hW0 u) hc2 (hW2 u) (hden u).ne' hαk
    rw [hP1, hF2, hP2, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal, key]
    push_cast; ring

/-! ### Helpers for 19.7.7 (substitution `θ = arctan (sinh u)`) -/

lemma p19lR1_mul_ofReal_cpow {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rcases eq_or_ne z 0 with rfl | hz
  · rcases eq_or_ne w 0 with rfl | hw
    · simp
    · simp [zero_cpow hw]
  · rw [cpow_def_of_ne_zero (mul_ne_zero hr' hz), cpow_def_of_ne_zero hr', cpow_def_of_ne_zero hz,
      show (r : ℂ) * z = z * r by ring, log_mul_ofReal r hr z hz, ← exp_add, ofReal_log hr.le]
    ring_nf

/-- A segment integral along `[0, iφ]`. -/
lemma p19lR1_segmentIntegral_I (f : ℂ → ℂ) (φ : ℝ) :
    ei19a_segmentIntegral f (I * φ) = I * ∫ u in (0 : ℝ)..φ, f (I * u) := by
  have h := ei19a_segmentIntegral_ofReal (fun z => I * f (I * z)) φ
  rw [intervalIntegral.integral_const_mul] at h
  rw [← h, ei19a_segmentIntegral, ei19a_segmentIntegral]
  congr 1; funext t; ring_nf

lemma p19lR1_sin_I_sq (u : ℝ) : Complex.sin (I * u) ^ 2 = -((Real.sinh u : ℝ) : ℂ) ^ 2 := by
  rw [mul_comm, Complex.sin_mul_I, ofReal_sinh, mul_pow, I_sq]; ring

/-- Substitution `θ = arctan (sinh u)`, `dθ = du / cosh u`. -/
lemma p19lR1_subst_arctan_sinh {G : ℝ → ℂ} (hG : ContinuousOn G (Ioo (-(π / 2)) (π / 2)))
    (φ : ℝ) :
    ∫ u in (0 : ℝ)..φ, ((Real.cosh u)⁻¹ : ℝ) • G (Real.arctan (Real.sinh u)) =
      ∫ θ in (0 : ℝ)..(Real.arctan (Real.sinh φ)), G θ := by
  have h := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := φ)
    (f := fun u => Real.arctan (Real.sinh u)) (f' := fun u => (Real.cosh u)⁻¹) (g := G)
    (fun u _ => by
      have := (Real.hasDerivAt_arctan (Real.sinh u)).comp u (Real.hasDerivAt_sinh u)
      refine this.congr_deriv ?_
      have hc := Real.cosh_pos u
      rw [← Real.cosh_sq']; field_simp)
    (by
      refine Continuous.continuousOn ?_
      exact continuous_iff_continuousAt.2 fun u =>
        (Real.continuous_cosh.continuousAt).inv₀ (Real.cosh_pos u).ne')
    (hG.mono (by
      rintro _ ⟨u, -, rfl⟩
      exact ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩))
  simpa [Real.sinh_zero, Real.arctan_zero] using h

lemma p19lR1_sin_cos_arctan_sinh (u : ℝ) :
    Real.sin (Real.arctan (Real.sinh u)) = Real.sinh u / Real.cosh u ∧
      Real.cos (Real.arctan (Real.sinh u)) = (Real.cosh u)⁻¹ := by
  have hs : Real.sqrt (1 + Real.sinh u ^ 2) = Real.cosh u := by
    rw [← Real.cosh_sq', Real.sqrt_sq (Real.cosh_pos u).le]
  rw [Real.sin_arctan, Real.cos_arctan, hs, one_div]
  exact ⟨rfl, rfl⟩

/-- Along the substitution, `1 - (1 - b) sin²θ = (1 + b sinh²u)/cosh²u`. -/
lemma p19lR1_one_sub_arctan_sinh (b : ℂ) (u : ℝ) :
    1 - (1 - b) * (Real.sin (Real.arctan (Real.sinh u)) : ℂ) ^ 2 =
      ((((Real.cosh u) ^ 2)⁻¹ : ℝ) : ℂ) * (1 + b * ((Real.sinh u : ℝ) : ℂ) ^ 2) := by
  rw [(p19lR1_sin_cos_arctan_sinh u).1]
  have hc : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
  have h2 : (Real.cosh u : ℂ) ^ 2 = 1 + (Real.sinh u : ℂ) ^ 2 := by
    have := Real.cosh_sq' u; exact_mod_cast (by linarith : Real.cosh u ^ 2 = 1 + Real.sinh u ^ 2)
  rw [ofReal_div, div_pow, ofReal_inv, ofReal_pow]
  field_simp
  linear_combination h2


lemma p19lR1_conv_mem {b : ℂ} (hb : b ∈ slitPlane) (θ : ℝ) :
    1 - (1 - b) * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane := by
  have := ei19a_one_sub_mul_mem_slitPlane (z := 1 - b) (by rw [sub_sub_cancel]; exact hb)
    (sq_nonneg (Real.sin θ)) (Real.sin_sq_le_one θ)
  convert this using 2; push_cast; ring

lemma p19lR1_cpow_arctan_sinh (b : ℂ) (u : ℝ) :
    (1 - (1 - b) * (Real.sin (Real.arctan (Real.sinh u)) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      (Real.cosh u : ℂ) * (1 + b * ((Real.sinh u : ℝ) : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) ∧
    (1 - (1 - b) * (Real.sin (Real.arctan (Real.sinh u)) : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
      (Real.cosh u : ℂ)⁻¹ * (1 + b * ((Real.sinh u : ℝ) : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
  have hc := Real.cosh_pos u
  rw [p19lR1_one_sub_arctan_sinh, p19lR1_mul_ofReal_cpow (by positivity),
    p19lR1_mul_ofReal_cpow (by positivity), (p19lR1_inv_sq_cpow hc).1, (p19lR1_inv_sq_cpow hc).2]
  exact ⟨rfl, rfl⟩

lemma p19lR1_imag_arg_F (φ : ℝ) {k : ℂ} (hk : k ^ 2 ∈ slitPlane) :
    incEllIntFk (I * φ) k = I * incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) := by
  rw [incEllIntFk, p19lR1_segmentIntegral_I, incEllIntFk_ofReal_eq_integral,
    ei19a_jacobiComodulusk_sq]
  congr 1
  rw [← p19lR1_subst_arctan_sinh]
  · refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [p19lR1_sin_I_sq, (p19lR1_cpow_arctan_sinh _ u).1, real_smul]
    have hc : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
    rw [ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    ring_nf
  · exact (continuous_iff_continuousAt.2 fun θ =>
      (continuousAt_cpow_const (p19lR1_conv_mem hk θ)).comp
        (f := fun θ : ℝ => 1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) (by fun_prop)).continuousOn

lemma p19lR1_cos_ne_zero_of_mem {θ : ℝ} (h : θ ∈ Ioo (-(π / 2)) (π / 2)) : Real.cos θ ≠ 0 :=
  (Real.cos_pos_of_mem_Ioo h).ne'

lemma p19lR1_uIcc_sub_Ioo {ψ : ℝ} (h : ψ ∈ Ioo (-(π / 2)) (π / 2)) :
    uIcc 0 ψ ⊆ Ioo (-(π / 2)) (π / 2) := by
  intro x hx
  rcases le_total 0 ψ with h0 | h0
  · rw [uIcc_of_le h0] at hx; exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, h.2]⟩
  · rw [uIcc_of_ge h0] at hx; exact ⟨by linarith [hx.1, h.1], by linarith [hx.2, Real.pi_pos]⟩

lemma p19lR1_imag_arg_E (φ : ℝ) {k : ℂ} (hk : k ^ 2 ∈ slitPlane) :
    incEllIntEk (I * φ) k = I * (incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) -
        incEllIntEk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) +
          Real.tan (Real.arctan (Real.sinh φ)) *
            (1 - (1 - k ^ 2) * (Real.sin (Real.arctan (Real.sinh φ)) : ℂ) ^ 2) ^ (1 / 2 : ℂ)) := by
  set ψ := Real.arctan (Real.sinh φ) with hψ
  set k' := jacobiComodulusk k with hk'
  have hk'2 : k' ^ 2 = 1 - k ^ 2 := ei19a_jacobiComodulusk_sq k
  have hk's : 1 - k' ^ 2 ∈ slitPlane := by rw [hk'2, sub_sub_cancel]; exact hk
  have hψI : ψ ∈ Ioo (-(π / 2)) (π / 2) :=
    ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hsub := p19lR1_uIcc_sub_Ioo hψI
  set G : ℝ → ℂ := fun θ => p19lR1_Δ k' θ / (Real.cos θ : ℂ) ^ 2 with hG
  have hΔc := p19lR1_continuous_Δ hk's
  have hGc : ContinuousOn G (Ioo (-(π / 2)) (π / 2)) := by
    refine hΔc.continuousOn.div (by fun_prop) fun θ hθ => ?_
    exact pow_ne_zero _ (by exact_mod_cast p19lR1_cos_ne_zero_of_mem hθ)
  -- the substitution
  have h1 : incEllIntEk (I * φ) k = I * ∫ θ in (0 : ℝ)..ψ, G θ := by
    rw [incEllIntEk, p19lR1_segmentIntegral_I, ← p19lR1_subst_arctan_sinh hGc]
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hG, p19lR1_Δ, hk'2, (p19lR1_cpow_arctan_sinh _ u).2, p19lR1_sin_I_sq, real_smul,
      (p19lR1_sin_cos_arctan_sinh u).2]
    have hc0 : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
    have e : (1 - k ^ 2 * -((Real.sinh u : ℝ) : ℂ) ^ 2) = 1 + k ^ 2 * ((Real.sinh u : ℝ) : ℂ) ^ 2 := by
      ring
    rw [e, ofReal_inv]
    field_simp
  -- the integration by parts identity
  set D : ℝ → ℂ := fun θ => G θ - (p19lR1_Δ k' θ)⁻¹ + p19lR1_Δ k' θ with hD
  have hDc : ContinuousOn D (uIcc 0 ψ) := by
    refine ((hGc.mono hsub).sub ?_).add hΔc.continuousOn
    exact (continuous_iff_continuousAt.2 fun θ =>
      (hΔc.continuousAt).inv₀ (p19lR1_Δ_ne_zero hk's θ)).continuousOn
  have hFTC : ∫ θ in (0 : ℝ)..ψ, D θ = Real.tan ψ * p19lR1_Δ k' ψ := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ : ℝ => (Real.tan θ : ℂ) * p19lR1_Δ k' θ) (f' := D) (a := 0) (b := ψ)
      (fun θ hθ => by
        have hcos := p19lR1_cos_ne_zero_of_mem (hsub hθ)
        have h := ((Real.hasDerivAt_tan hcos).ofReal_comp).mul (p19lR1_hasDerivAt_Δ hk's θ)
        refine h.congr_deriv ?_
        have hΔ := p19lR1_Δ_ne_zero hk's θ
        have hΔ2 := p19lR1_Δ_sq k' θ
        have hc : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hcos
        simp only [hD, hG, Real.tan_eq_sin_div_cos, ofReal_div, ofReal_one, ofReal_pow]
        field_simp
        linear_combination (-(Real.cos θ : ℂ) ^ 2) * hΔ2)
      (hDc.intervalIntegrable)
    rw [this]; simp [Real.tan_zero]
  have hGint : IntervalIntegrable G volume 0 ψ := (hGc.mono hsub).intervalIntegrable
  have hΔint : IntervalIntegrable (p19lR1_Δ k') volume 0 ψ := hΔc.intervalIntegrable _ _
  have hΔiint : IntervalIntegrable (fun θ => (p19lR1_Δ k' θ)⁻¹) volume 0 ψ :=
    (continuous_iff_continuousAt.2 fun θ =>
      (hΔc.continuousAt).inv₀ (p19lR1_Δ_ne_zero hk's θ)).intervalIntegrable _ _
  have hsplit : ∫ θ in (0 : ℝ)..ψ, G θ = (∫ θ in (0 : ℝ)..ψ, D θ) +
      (∫ θ in (0 : ℝ)..ψ, (p19lR1_Δ k' θ)⁻¹) - ∫ θ in (0 : ℝ)..ψ, p19lR1_Δ k' θ := by
    rw [← intervalIntegral.integral_add ((hGint.sub hΔiint).add hΔint) hΔiint,
      ← intervalIntegral.integral_sub (((hGint.sub hΔiint).add hΔint).add hΔiint) hΔint]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring
  rw [h1, hsplit, hFTC, incEllIntFk_ofReal_eq_integral, incEllIntEk_ofReal_eq_integral]
  simp only [p19lR1_Δ, ← cpow_neg, hk'2]
  ring

lemma p19lR1_one_add_mem {b : ℂ} (hb : b ∈ slitPlane) {x : ℝ} (hx : 0 ≤ x) :
    1 + b * x ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hb ⊢
  simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, add_im, one_im,
    mul_im, zero_add]
  rcases hx.lt_or_eq with hx | rfl
  · rcases eq_or_ne b.im 0 with h | h
    · left; have := hb.resolve_right (not_not.2 h); nlinarith
    · right; exact mul_ne_zero h hx.ne'
  · left; simp

lemma p19lR1_path_bound {g : ℂ → ℂ} (hg : Continuous g) (w : ℂ)
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, g (t * w) ≠ 0) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖g (t * w)‖ := by
  obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    (nonempty_Icc.2 zero_le_one) (by fun_prop : Continuous fun t : ℝ => ‖g (t * w)‖).continuousOn
  exact ⟨‖g (t0 * w)‖, norm_pos_iff.2 (hne t0 ht0), fun t ht => hmin ht⟩

lemma p19lR1_incEllIntPik_ofReal_slit (ψ : ℝ) {β : ℂ} (hβ : 1 - β ∈ slitPlane) (k : ℂ) :
    incEllIntPik ψ β k = ∫ θ in (0 : ℝ)..ψ, ((1 - β * (Real.sin θ : ℂ) ^ 2)⁻¹ *
      (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
  obtain ⟨δ, hδ, hb⟩ := p19lR1_exists_norm_lower_gen hβ
  rw [incEllIntPik_eq_segmentIntegral (δ := δ) hδ, ei19a_segmentIntegral_ofReal]
  · simp only [← Complex.ofReal_sin]
  · intro t _
    have := hb (t * ψ)
    push_cast at this; exact this

lemma p19lR1_imag_arg_Pi (φ : ℝ) {k α2 : ℂ} (hk : k ^ 2 ∈ slitPlane) (hα : α2 ∈ slitPlane)
    (hα1 : α2 ≠ 1) :
    incEllIntPik (I * φ) α2 k = I * (incEllIntFk (Real.arctan (Real.sinh φ)) (jacobiComodulusk k) -
        α2 * incEllIntPik (Real.arctan (Real.sinh φ)) (1 - α2) (jacobiComodulusk k)) / (1 - α2) := by
  set ψ := Real.arctan (Real.sinh φ) with hψ
  set k' := jacobiComodulusk k with hk'
  have hk'2 : k' ^ 2 = 1 - k ^ 2 := ei19a_jacobiComodulusk_sq k
  have hα1' : (1 : ℂ) - α2 ≠ 0 := sub_ne_zero.2 (Ne.symm hα1)
  have hpath : ∀ u : ℝ, 1 - α2 * Complex.sin (I * u) ^ 2 =
      1 + α2 * (((Real.sinh u) ^ 2 : ℝ) : ℂ) := by
    intro u; rw [p19lR1_sin_I_sq]; push_cast; ring
  -- remove the principal value on the left
  obtain ⟨δ, hδ, hb⟩ := p19lR1_path_bound (g := fun z => 1 - α2 * Complex.sin z ^ 2)
    (by fun_prop) (I * φ) (fun t _ => by
      have : ((t : ℂ) * (I * φ)) = I * ((t * φ : ℝ) : ℂ) := by push_cast; ring
      simp only [this, hpath]
      exact slitPlane_ne_zero (p19lR1_one_add_mem hα (sq_nonneg _)))
  rw [incEllIntPik_eq_segmentIntegral hδ hb, p19lR1_segmentIntegral_I,
    p19lR1_incEllIntPik_ofReal_slit ψ (by rw [sub_sub_cancel]; exact hα),
    incEllIntFk_ofReal_eq_integral]
  set P : ℝ → ℂ := fun θ => 1 - (1 - α2) * (Real.sin θ : ℂ) ^ 2 with hP
  have hPne : ∀ θ, P θ ≠ 0 := fun θ => slitPlane_ne_zero (p19lR1_conv_mem hα θ)
  set H : ℝ → ℂ := fun θ => (Real.cos θ : ℂ) ^ 2 * (P θ)⁻¹ *
    (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) with hH
  have hQc : Continuous fun θ : ℝ => (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) :=
    continuous_iff_continuousAt.2 fun θ =>
      (continuousAt_cpow_const (p19lR1_conv_mem hk θ)).comp
        (f := fun θ : ℝ => 1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) (by fun_prop)
  have hPic : Continuous fun θ => (P θ)⁻¹ :=
    continuous_iff_continuousAt.2 fun θ => ((by fun_prop : Continuous P).continuousAt).inv₀ (hPne θ)
  have hHc : Continuous H := by
    rw [hH]; exact ((by fun_prop : Continuous fun θ : ℝ => (Real.cos θ : ℂ) ^ 2).mul hPic).mul hQc
  have h1 : (∫ u in (0 : ℝ)..φ, (1 - α2 * Complex.sin (I * u) ^ 2)⁻¹ *
      (1 - k ^ 2 * Complex.sin (I * u) ^ 2) ^ (-(1 / 2 : ℂ))) = ∫ θ in (0 : ℝ)..ψ, H θ := by
    rw [← p19lR1_subst_arctan_sinh hHc.continuousOn]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have hPu : P (Real.arctan (Real.sinh u)) =
        ((((Real.cosh u) ^ 2)⁻¹ : ℝ) : ℂ) * (1 + α2 * ((Real.sinh u : ℝ) : ℂ) ^ 2) :=
      p19lR1_one_sub_arctan_sinh α2 u
    simp only [hH, hPu, (p19lR1_cpow_arctan_sinh _ u).1, (p19lR1_sin_cos_arctan_sinh u).2,
      real_smul, p19lR1_sin_I_sq]
    have hc0 : (Real.cosh u : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos u).ne'
    have hA : (1 + α2 * ((Real.sinh u : ℝ) : ℂ) ^ 2) ≠ 0 :=
      slitPlane_ne_zero (by
        have := p19lR1_one_add_mem hα (sq_nonneg (Real.sinh u)); push_cast at this ⊢; exact this)
    have e : (1 - k ^ 2 * -((Real.sinh u : ℝ) : ℂ) ^ 2) = 1 + k ^ 2 * ((Real.sinh u : ℝ) : ℂ) ^ 2 := by
      ring
    have e2 : (1 - α2 * -((Real.sinh u : ℝ) : ℂ) ^ 2) =
        1 + α2 * ((Real.sinh u : ℝ) : ℂ) ^ 2 := by ring
    rw [e, e2, ofReal_inv, ofReal_inv, ofReal_pow]
    field_simp
  rw [h1]
  have hint1 : IntervalIntegrable (fun θ : ℝ =>
      (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) volume 0 ψ :=
    hQc.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ : ℝ => (P θ)⁻¹ *
      (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) volume 0 ψ :=
    (hPic.mul hQc).intervalIntegrable _ _
  have h2 : ∫ θ in (0 : ℝ)..ψ, H θ = ((∫ θ in (0 : ℝ)..ψ,
      (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) - α2 * ∫ θ in (0 : ℝ)..ψ,
        (P θ)⁻¹ * (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) / (1 - α2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hint1
      (hint2.const_mul _), ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hP' := hPne θ
    simp only [hH]
    have hcs : (Real.cos θ : ℂ) ^ 2 = 1 - (Real.sin θ : ℂ) ^ 2 := by
      have := Real.cos_sq' θ; exact_mod_cast this
    rw [hcs]
    field_simp
    simp only [hP]
    ring
  rw [h2, hk'2]
  ring
/-- DLMF 19.7.7 (imaginary-argument transformation): for real `φ`, `tan ψ = sinh φ`
(`ψ = arctan(sinh φ)`), `k² ∉ (-∞, 0]` and `α² ∉ (-∞, 0]`, `α² ≠ 1`:
`F(iφ, k) = iF(ψ, k')`,
`E(iφ, k) = i(F(ψ, k') - E(ψ, k') + tan ψ √(1 - k'² sin²ψ))`,
`Π(iφ, α², k) = i(F(ψ, k') - α²Π(ψ, 1 - α², k'))/(1 - α²)`. -/
@[dlmf 19.7.E7]
theorem incEllInt_imaginary_argument (φ : ℝ) {k α2 : ℂ} (hk : k ^ 2 ∈ slitPlane)
    (hα : α2 ∈ slitPlane) (hα1 : α2 ≠ 1) :
    let ψ := Real.arctan (Real.sinh φ)
    incEllIntFk (I * φ) k = I * incEllIntFk ψ (jacobiComodulusk k) ∧
      incEllIntEk (I * φ) k = I * (incEllIntFk ψ (jacobiComodulusk k) -
        incEllIntEk ψ (jacobiComodulusk k) +
          Real.tan ψ * (1 - (1 - k ^ 2) * (Real.sin ψ : ℂ) ^ 2) ^ (1 / 2 : ℂ)) ∧
      incEllIntPik (I * φ) α2 k = I * (incEllIntFk ψ (jacobiComodulusk k) -
        α2 * incEllIntPik ψ (1 - α2) (jacobiComodulusk k)) / (1 - α2) :=
  ⟨p19lR1_imag_arg_F φ hk, p19lR1_imag_arg_E φ hk, p19lR1_imag_arg_Pi φ hk hα hα1⟩

/-! ### §19.7(iii) Change of parameter of `Π(φ, α², k)` -/

/-- **Admitted.** DLMF 19.7.8: for real `0 < φ < π/2`, `c = csc²φ`, real `0 < k < 1` and real
`α², ω²` with `α²ω² = k²`, `α² ≠ c`, `ω² ≠ c` (Cauchy principal values when `α²` or `ω²`
exceeds `c`):
`Π(φ, α², k) + Π(φ, ω², k) = F(φ, k) + √c R_C((c-1)(c-k²), (c-α²)(c-ω²))`. -/
@[dlmf 19.7.E8]
theorem incEllIntPik_add_first {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : α2 * ω2 = k ^ 2) (hα : α2 ≠ 1 / Real.sin φ ^ 2)
    (hω : ω2 ≠ 1 / Real.sin φ ^ 2) :
    let c := 1 / Real.sin φ ^ 2
    incEllIntPik φ α2 k + incEllIntPik φ ω2 k = incEllIntFk φ k +
      Real.sqrt c * symEllIntRC ((c - 1) * (c - k ^ 2) : ℝ) ((c - α2) * (c - ω2) : ℝ) := by
  sorry

/-- **Admitted.** DLMF 19.7.9: for real `0 < φ < π/2`, `c = csc²φ`, real `0 < k < 1` and real
`α², ω²` with `(1 - α²)(1 - ω²) = 1 - k²`, `α² ≠ c`, `ω² ≠ c`:
`(k² - α²)Π(φ, α², k) + (k² - ω²)Π(φ, ω², k)
= k²F(φ, k) - α²ω² √(c - 1) R_C(c(c - k²), (c - α²)(c - ω²))`. -/
@[dlmf 19.7.E9]
theorem incEllIntPik_add_second {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : (1 - α2) * (1 - ω2) = 1 - k ^ 2) (hα : α2 ≠ 1 / Real.sin φ ^ 2)
    (hω : ω2 ≠ 1 / Real.sin φ ^ 2) :
    let c := 1 / Real.sin φ ^ 2
    ((k ^ 2 - α2 : ℝ) : ℂ) * incEllIntPik φ α2 k + ((k ^ 2 - ω2 : ℝ) : ℂ) * incEllIntPik φ ω2 k =
      (k ^ 2 : ℝ) * incEllIntFk φ k - (α2 * ω2 * Real.sqrt (c - 1) : ℝ) *
        symEllIntRC (c * (c - k ^ 2) : ℝ) ((c - α2) * (c - ω2) : ℝ) := by
  sorry

/-- **Admitted.** DLMF 19.7.10: for real `0 < φ < π/2`, `c = csc²φ`, real `0 < k < 1` and real
`α², ω²` with `(k² - α²)(k² - ω²) = k²(k² - 1)`, `α² ≠ c`, `ω² ≠ c`:
`(1 - α²)Π(φ, α², k) + (1 - ω²)Π(φ, ω², k)
= F(φ, k) + (1 - α² - ω²) √(c - k²) R_C(c(c - 1), (c - α²)(c - ω²))`. -/
@[dlmf 19.7.E10]
theorem incEllIntPik_add_third {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : (k ^ 2 - α2) * (k ^ 2 - ω2) = k ^ 2 * (k ^ 2 - 1))
    (hα : α2 ≠ 1 / Real.sin φ ^ 2) (hω : ω2 ≠ 1 / Real.sin φ ^ 2) :
    let c := 1 / Real.sin φ ^ 2
    ((1 - α2 : ℝ) : ℂ) * incEllIntPik φ α2 k + ((1 - ω2 : ℝ) : ℂ) * incEllIntPik φ ω2 k =
      incEllIntFk φ k + ((1 - α2 - ω2) * Real.sqrt (c - k ^ 2) : ℝ) *
        symEllIntRC (c * (c - 1) : ℝ) ((c - α2) * (c - ω2) : ℝ) := by
  sorry

/-- DLMF §19.7(iii) (prose): under the relation `α²ω² = k²` of 19.7.8, since `k² ≤ c`, `α² > c`
implies `ω² < 1 ≤ c` (for real `0 < k < 1` and `0 < φ < π/2`). -/
@[dlmf 19.7.iii]
theorem first_relation_omega_lt {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : α2 * ω2 = k ^ 2) (hα : 1 / Real.sin φ ^ 2 < α2) :
    ω2 < 1 ∧ 1 ≤ 1 / Real.sin φ ^ 2 := by
  have hs0 : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hs1 : Real.sin φ ^ 2 ≤ 1 := Real.sin_sq_le_one φ
  have hc : 1 ≤ 1 / Real.sin φ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  refine ⟨?_, hc⟩
  have hα0 : 1 < α2 := lt_of_le_of_lt hc hα
  by_contra h
  push Not at h
  nlinarith

end DLMF.EllipticIntegrals
