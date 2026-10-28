/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Derivatives

/-!
# Connections among complete elliptic integrals

Complementary-modulus and imaginary-modulus connections among the complete elliptic integrals.

Source references and common attribution are retained in
`DLMF.EllipticIntegrals.Connection`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory

open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

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

/-- Identity under the stated parameter and domain assumptions: `∫ θ in (0 : ℝ)..(π / 2), (1 - (I
* x / c) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ r = (((c ^ 2)⁻¹ : ℝ) : ℂ) ^ r * ∫ θ in (0 : ℝ)..(π /
2), (1 - (x : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ r`. -/
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

/-- Identity under the stated parameter and domain assumptions: `(((c ^ 2)⁻¹ : ℝ) : ℂ) ^ (-(1 / 2
: ℂ)) = c ∧ (((c ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (c : ℂ)⁻¹`. -/
lemma p19lR1_inv_sq_cpow {c : ℝ} (hc : 0 < c) :
    (((c ^ 2)⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = c ∧ (((c ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (c : ℂ)⁻¹ := by
  have h1 : (((c ^ 2)⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (c : ℂ)⁻¹ := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      Real.inv_rpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hc.le]
    push_cast; rfl
  refine ⟨?_, h1⟩
  rw [cpow_neg, h1, inv_inv]

/-- Formula under the stated hypotheses: `w⁻¹ ∈ slitPlane`. -/
lemma p19lR1_inv_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) : w⁻¹ ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  have hw0 : w ≠ 0 := slitPlane_ne_zero (mem_slitPlane_iff.2 hw)
  have hn : 0 < normSq w := normSq_pos.2 hw0
  rw [inv_re, inv_im]
  rcases hw with h | h
  · left; exact div_pos h hn
  · right; exact div_ne_zero (neg_ne_zero.2 h) hn.ne'

/-- The indicated domain is open: `IsOpen {k : ℂ | 1 - k ^ 2 ∈ slitPlane}`. -/
theorem p19lR1_isOpen_U : IsOpen {k : ℂ | 1 - k ^ 2 ∈ slitPlane} :=
  isOpen_slitPlane.preimage (by fun_prop)

/-- Formula under the stated hypotheses: `IsPreconnected {k : ℂ | 1 - k ^ 2 ∈ slitPlane}`. -/
lemma p19lR1_isPreconnected_U : IsPreconnected {k : ℂ | 1 - k ^ 2 ∈ slitPlane} := by
  refine (StarConvex.isPathConnected (a := (0 : ℂ)) ?_ (by simp)).isConnected.isPreconnected
  intro y hy a b ha hb hab
  simp only [smul_zero, zero_add, Set.mem_ofPred_eq, real_smul] at hy ⊢
  have := ei19a_one_sub_mul_mem_slitPlane hy (sq_nonneg b) (by nlinarith)
  convert this using 2; push_cast; ring

/-- Differentiability at the specified argument: `DifferentiableAt ℂ jacobiComodulusk k`. -/
theorem p19lR1_comod_differentiableAt {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    DifferentiableAt ℂ jacobiComodulusk k := by
  unfold jacobiComodulusk
  exact (by fun_prop : DifferentiableAt ℂ (fun k : ℂ => 1 - k ^ 2) k).cpow_const hk

/-- Nonvanishing under the stated hypotheses: `jacobiComodulusk k ≠ 0`. -/
lemma p19lR1_comod_ne_zero {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) : jacobiComodulusk k ≠ 0 := by
  intro h
  have := ei19a_jacobiComodulusk_sq k
  rw [h] at this
  exact slitPlane_ne_zero hk (by rw [← this]; ring)

/-- Identity under the stated parameter and domain assumptions: `jacobiComodulusk x = (Real.sqrt
(1 - x ^ 2) : ℂ)`. -/
lemma p19lR1_comod_ofReal {x : ℝ} (hx : x ^ 2 ≤ 1) :
    jacobiComodulusk x = (Real.sqrt (1 - x ^ 2) : ℂ) := by
  rw [jacobiComodulusk, Real.sqrt_eq_rpow, ofReal_cpow (by linarith)]
  push_cast; rfl

/-- Formula under the stated hypotheses: `1 - (I * k / jacobiComodulusk k) ^ 2 ∈ slitPlane`. -/
lemma p19lR1_imag_mem {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    1 - (I * k / jacobiComodulusk k) ^ 2 ∈ slitPlane := by
  have hne := p19lR1_comod_ne_zero hk
  have hne' : 1 - k ^ 2 ≠ 0 := slitPlane_ne_zero hk
  have : 1 - (I * k / jacobiComodulusk k) ^ 2 = (1 - k ^ 2)⁻¹ := by
    rw [div_pow, ei19a_jacobiComodulusk_sq, mul_pow, I_sq]
    field_simp; ring
  rw [this]; exact p19lR1_inv_mem_slitPlane hk

/-- Identity under the stated parameter and domain assumptions: `f k = g k`. -/
theorem p19lR1_eqOn_U {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f {k : ℂ | 1 - k ^ 2 ∈ slitPlane})
    (hg : DifferentiableOn ℂ g {k : ℂ | 1 - k ^ 2 ∈ slitPlane})
    (h : ∀ x : ℝ, 0 < x → x < 1 → f x = g x) {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) : f k = g k := by
  have h0 : (0 : ℂ) ∈ {k : ℂ | 1 - k ^ 2 ∈ slitPlane} := by simp
  refine (hf.analyticOnNhd p19lR1_isOpen_U).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd p19lR1_isOpen_U) p19lR1_isPreconnected_U h0 ?_ hk
  have := Carlson.TwoVariable.frequently_ofReal_Ioo (a := 0) (ε := 1) one_pos (P := fun z => f z = g z)
    (fun x h1 h2 => h x h1 (by linarith))
  simpa using this

/-- Identity under the stated parameter and domain assumptions: `compEllIntKk (I * k /
jacobiComodulusk k) = jacobiComodulusk k * compEllIntKk k ∧ compEllIntEk (I * k /
jacobiComodulusk k) = compEllIntEk k / jacobiComodulusk k`. -/
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

/-- Identity under the stated parameter and domain assumptions: `jacobiComodulusk
(jacobiComodulusk k) = k`. -/
lemma p19lR1_comod_comod {k : ℂ} (hk : 0 < k.re) :
    jacobiComodulusk (jacobiComodulusk k) = k := by
  rw [jacobiComodulusk, ei19a_jacobiComodulusk_sq, sub_sub_cancel, one_div]
  have h := abs_arg_lt_pi_div_two_iff.2 (Or.inl hk)
  rw [abs_lt] at h
  exact Complex.pow_cpow_nat_inv (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

/-- Identity under the stated parameter and domain assumptions: `compEllIntKk (-I *
jacobiComodulusk k / k) = k * compEllIntKk (jacobiComodulusk k) ∧ compEllIntEk (-I *
jacobiComodulusk k / k) = compEllIntEk (jacobiComodulusk k) / k`. -/
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

/-- Identity under the stated parameter and domain assumptions: `jacobiComodulusk (-k) =
jacobiComodulusk k`. -/
lemma p19lR1_comod_neg (k : ℂ) : jacobiComodulusk (-k) = jacobiComodulusk k := by
  simp [jacobiComodulusk]

/-- Identity under the stated parameter and domain assumptions: `p19lR1_W (-k) = p19lR1_W k`. -/
lemma p19lR1_W_neg (k : ℂ) : p19lR1_W (-k) = p19lR1_W k := by
  simp only [p19lR1_W, p19lR1_comod_neg, compEllIntKk_neg, compEllIntEk_neg]

/-- Formula under the stated hypotheses: `k ^ 2 ∈ slitPlane`. -/
lemma p19lR1_sq_mem_slitPlane {k : ℂ} (hk : 0 < k.re) : k ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases eq_or_ne k.im 0 with h | h
  · left; simp [sq, h]; nlinarith
  · right; simp only [sq, mul_im]; intro h'
    have : k.re * k.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · exact hk.ne' h3
    · exact h h3

/-- Estimate under the stated parameter and domain assumptions: `1 - z ^ 2 ∈ slitPlane ↔ z.im ≠ 0
∨ z.re ^ 2 < 1`. -/
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

/-- The indicated domain is open: `IsOpen {k : ℂ | 0 < k.re ∧ 1 - k ^ 2 ∈ slitPlane}`. -/
lemma p19lR1_isOpen_V : IsOpen {k : ℂ | 0 < k.re ∧ 1 - k ^ 2 ∈ slitPlane} :=
  (isOpen_lt continuous_const continuous_re).inter p19lR1_isOpen_U

/-- Estimate under the stated parameter and domain assumptions: `IsPreconnected {k : ℂ | 0 < k.re
∧ 1 - k ^ 2 ∈ slitPlane}`. -/
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

/-- Identity under the stated parameter and domain assumptions: `p19lR1_W k = π / 2`. -/
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

/-- Continuity within the specified domain: `ContinuousWithinAt (fun z : ℂ => z ^ r) {z : ℂ | 0 ≤
z.im} (w : ℂ)`. -/
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

/-- Estimate under the stated parameter and domain assumptions: `2 / π * |d| ≤ |Real.sin d|`. -/
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

/-- Estimate under the stated parameter and domain assumptions: `∃ C > 0, ∀ θ ∈ Icc 0 (π / 2), C *
|θ - θ₀| ≤ |Real.sin θ₀ ^ 2 - Real.sin θ ^ 2|`. -/
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

/-- Integrability between the indicated endpoints: `IntervalIntegrable (fun θ : ℝ => |θ - θ₀| ^
(-(1 / 2) : ℝ)) volume 0 (π / 2)`. -/
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

/-- Integrability between the indicated endpoints: `IntervalIntegrable (fun θ : ℝ => |1 - a *
Real.sin θ ^ 2| ^ (-(1 / 2) : ℝ)) volume 0 (π / 2)`. -/
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

/-- Formula under the stated hypotheses: `∀ᵐ θ : ℝ, θ ∈ uIoc (0 : ℝ) (π / 2) → 1 - a * Real.sin θ
^ 2 ≠ 0`. -/
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

/-- The map `(fun η : ℝ => ∫ θ in (0 : ℝ)..(π / 2), (1 - ((a : ℂ) - I * η) * (Real.sin θ : ℂ) ^ 2)
^ (ρ : ℂ))` tends to `(𝓝 (∫ θ in (0 : ℝ)..(π / 2), (1 - (a : ℂ) * (Real.sin θ : ℂ) ^ 2) ^ (ρ :
ℂ)))` along `(𝓝[>] 0)`. -/
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

/-- Identity under the stated parameter and domain assumptions: `p19lR1_W k = compEllIntEk k * (∫
θ in (0 : ℝ)..(π / 2), (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ ((-(1 / 2) : ℝ) : ℂ)) + (∫ θ
in (0 : ℝ)..(π / 2), (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ ((1 / 2 : ℝ) : ℂ)) *
compEllIntKk k - compEllIntKk k * (∫ θ in (0 : ℝ)..(π / 2), (1 - (1 - k ^ 2) * (Real.sin θ :
ℂ) ^ 2) ^ ((-(1 / 2) : ℝ) : ℂ))`. -/
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

/-- Identity under the stated parameter and domain assumptions: `p19lR1_W (I * y) = π / 2`. -/
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

end DLMF.EllipticIntegrals
end
