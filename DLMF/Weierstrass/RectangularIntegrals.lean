/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.SpecialLattices

/-!
# Inversion of `℘` by real integrals on a rectangular lattice (DLMF 23.6.30–23.6.35)

For a rectangular lattice (`ω₁ = a > 0`, `ω₃ = ib`, `b > 0`) the function `℘` is real on the
boundary of the period rectangle `[0, ω₁] × [0, ω₃]` and maps each of its four sides
monotonically onto a real interval bounded by the roots `e₃ < e₂ < e₁` or by `±∞`. The
differential equation `℘'² = 4(℘ - e₁)(℘ - e₂)(℘ - e₃)` and the one-dimensional change of
variables formula then express the side lengths as elliptic integrals.

## Main results

* `rectangular_integral_one` … `rectangular_integral_four`: DLMF 23.6.30–23.6.33.
* `rectangular_two_ω₁`, `rectangular_two_ω₃`: DLMF 23.6.34–23.6.35.

## Implementation notes

On each side, parametrized by an affine path `γ`, the real function `t ↦ ℜ℘(γ(t))` has
nonvanishing derivative of modulus `2√|∏(℘ - e_j)|` (the zeros of `℘'` are the half-periods), so
it is injective by Rolle's theorem; `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`
turns the integral over its image into the length of the side.
-/

@[expose] public section

open Complex PeriodPair MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

variable (H : HalfPeriods)

/-- `hasDerivAt_re_weierstrassP_comp` when the roots `e_j` are real. -/
private lemma path_facts {γ : ℝ → ℂ} {v : ℂ} (hv : ‖v‖ = 1) (hγ : ∀ t, HasDerivAt γ v t)
    {α β : ℝ} (hL : ∀ t ∈ Ioo α β, γ t ∉ H.lattice ∧ 2 * γ t ∉ H.lattice)
    (hR : ∀ t ∈ Ioo α β, (H.weierstrassP (γ t)).im = 0)
    (he1 : (H.e 1).im = 0) (he2 : (H.e 2).im = 0) (he3 : (H.e 3).im = 0)
    {t : ℝ} (ht : t ∈ Ioo α β) :
    HasDerivAt (fun s => (H.weierstrassP (γ s)).re) (H.derivWeierstrassP (γ t) * v).re t ∧
      (H.derivWeierstrassP (γ t) * v).re ≠ 0 ∧
      |(H.derivWeierstrassP (γ t) * v).re| = 2 * Real.sqrt
        |((H.weierstrassP (γ t)).re - (H.e 1).re) * ((H.weierstrassP (γ t)).re - (H.e 2).re) *
          ((H.weierstrassP (γ t)).re - (H.e 3).re)| := by
  obtain ⟨h1, h2, h3⟩ := H.hasDerivAt_re_weierstrassP_comp hv hγ hL hR ht
  refine ⟨h1, h2, h3.trans ?_⟩
  have hr : ∀ w : ℂ, w.im = 0 → w = (w.re : ℂ) := fun w hw => Complex.ext (by simp) (by simp [hw])
  rw [hr _ (hR t ht), hr _ he1, hr _ he2, hr _ he3, ← ofReal_sub, ← ofReal_sub, ← ofReal_sub,
    ← ofReal_mul, ← ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
  simp only [ofReal_re]

/-- No integer multiple of `c > 0` lies strictly between `0` and `c`. -/
private lemma false_of_eq_int_mul {c t : ℝ} (hc : 0 < c) {m : ℤ} (h : t = m * c)
    (h0 : 0 < t) (h1 : t < c) : False := by
  subst h
  have hm0 : (0 : ℝ) < m := by
    by_contra hh; rw [not_lt] at hh; nlinarith
  have hm1 : (m : ℝ) < 1 := by
    by_contra hh; rw [not_lt] at hh; nlinarith
  have : (0 : ℤ) < m := by exact_mod_cast hm0
  have : m < 1 := by exact_mod_cast hm1
  omega

variable {H}

/-- Coordinates of a point of a rectangular lattice. -/
private lemma rectangular_mem_lattice {a b : ℝ} (hω₁ : H.ω₁ = a) (hω₃ : H.ω₃ = b * I) {z : ℂ}
    (hz : z ∈ H.lattice) : (∃ m : ℤ, z.re = m * (2 * a)) ∧ ∃ n : ℤ, z.im = n * (2 * b) := by
  obtain ⟨m, n, rfl⟩ := H.mem_lattice_iff.mp hz
  rw [hω₁, hω₃]
  exact ⟨⟨m, by simp; ring⟩, ⟨n, by simp; ring⟩⟩

/-- A rectangular lattice is invariant under conjugation. -/
private lemma rectangular_conj_mem {a b : ℝ} (hω₁ : H.ω₁ = a) (hω₃ : H.ω₃ = b * I) :
    ∀ z, z ∈ H.periodPair.lattice → conj z ∈ H.periodPair.lattice := by
  intro z hz
  obtain ⟨m, n, rfl⟩ := H.mem_lattice_iff.mp hz
  refine H.mem_lattice_iff.mpr ⟨m, -n, ?_⟩
  rw [hω₁, hω₃]
  apply Complex.ext <;> simp

/-- The half-periods `ω₁ = a`, `ω₃ = ib` form a rectangular lattice. -/
private lemma isRectangular_of_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) : H.IsRectangular :=
  ⟨by simp [hω₁], by simp [hω₁, ha], by simp [hω₃], by simp [hω₃, hb]⟩

/-- `e₂ = ℘(ω₁ + ω₃)`. -/
private lemma rectangular_e_two {a b : ℝ} (hω₁ : H.ω₁ = a) (hω₃ : H.ω₃ = b * I) :
    H.e 2 = H.weierstrassP (a + b * I) := by
  rw [HalfPeriods.e, halfPeriod_two, HalfPeriods.ω₂, hω₁, hω₃,
    show -(a : ℂ) - b * I = -(a + b * I) by ring]
  exact H.periodPair.weierstrassP_neg _

variable (H)

/-- DLMF 23.6.30: for a rectangular lattice (`ω₁ = a > 0`, `ω₃ = ib`, `b > 0`) and
`z = x ∈ (0, ω₁]`, `t = ℘(z)` is real, `t ≥ e₁` and
`z = ½ ∫_t^∞ du/√((u - e₁)(u - e₂)(u - e₃))`. -/
@[dlmf 23.6.E30]
theorem rectangular_integral_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) {x : ℝ} (hx : x ∈ Set.Ioc 0 a) :
    (H.weierstrassP x).im = 0 ∧ H.eRe 1 ≤ (H.weierstrassP x).re ∧
      x = 1 / 2 * ∫ u in Set.Ioi (H.weierstrassP x).re,
        1 / Real.sqrt ((u - H.eRe 1) * (u - H.eRe 2) * (u - H.eRe 3)) := by
  obtain ⟨he1, he2, he3, h21, h32, -, -⟩ := (isRectangular_of_eq ha hb hω₁ hω₃).roots
  have hinv := rectangular_conj_mem hω₁ hω₃
  set f : ℝ → ℝ := fun s => (H.weierstrassP (s : ℂ)).re with hf
  have hR : ∀ t : ℝ, (H.weierstrassP (t : ℂ)).im = 0 := fun t =>
    weierstrassP_im_eq_zero_of_conj hinv (zero_mem _) (Or.inl (by simp))
  have hnot : ∀ t ∈ Ioc 0 a, (t : ℂ) ∉ H.lattice := by
    intro t ht hm
    obtain ⟨⟨m, hm⟩, -⟩ := rectangular_mem_lattice hω₁ hω₃ hm
    simp only [ofReal_re] at hm
    exact false_of_eq_int_mul (by linarith) hm ht.1 (by linarith [ht.2])
  have hL : ∀ t ∈ Ioo 0 a, (t : ℂ) ∉ H.lattice ∧ 2 * (t : ℂ) ∉ H.lattice := by
    intro t ht
    refine ⟨hnot t ⟨ht.1, ht.2.le⟩, fun hm => ?_⟩
    obtain ⟨⟨m, hm⟩, -⟩ := rectangular_mem_lattice hω₁ hω₃ hm
    simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero] at hm
    exact false_of_eq_int_mul (by linarith) hm (by linarith [ht.1]) (by linarith [ht.2])
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := fun t => by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hPF : ∀ t ∈ Ioo 0 a, HasDerivAt f (H.derivWeierstrassP (t : ℂ) * 1).re t ∧
      (H.derivWeierstrassP (t : ℂ) * 1).re ≠ 0 ∧
      |(H.derivWeierstrassP (t : ℂ) * 1).re| = 2 * Real.sqrt
        |(f t - (H.e 1).re) * (f t - (H.e 2).re) * (f t - (H.e 3).re)| := fun t ht =>
    H.path_facts (by simp) hγ hL (fun t _ => hR t) he1 he2 he3 ht
  have hcont : ∀ t ∈ Ioc 0 a, ContinuousAt f t := fun t ht =>
    H.continuousAt_re_weierstrassP_comp hγ (hnot t ht)
  have hlim : Tendsto f (𝓝[>] 0) atTop := by
    have hg := analyticAt_weierstrassP_sub H.periodPair (zero_mem _)
    have h1 : ContinuousAt (fun t : ℝ => H.weierstrassP t - 1 / ((t : ℂ) - 0) ^ 2) 0 :=
      hg.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
    obtain ⟨C, hgc⟩ : ∃ C, Tendsto (fun t : ℝ => (H.weierstrassP t - 1 / ((t : ℂ) - 0) ^ 2).re)
        (𝓝[>] 0) (𝓝 C) :=
      ⟨_, (Complex.continuous_re.continuousAt.comp h1).tendsto.mono_left nhdsWithin_le_nhds⟩
    have hinf : Tendsto (fun t : ℝ => (t ^ 2)⁻¹) (𝓝[>] 0) atTop := by
      have := (tendsto_pow_atTop (two_ne_zero)).comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
      simpa [Function.comp_def, inv_pow] using this
    refine (hinf.atTop_add hgc).congr' ?_
    filter_upwards with t
    have : (1 / ((t : ℂ) - 0) ^ 2) = (((t ^ 2)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    simp only [hf, this, sub_re, ofReal_re]
    ring
  obtain ⟨hSA, himg⟩ := strictAntiOn_Ioc_of_tendsto_atTop (c := a) hcont
    (fun t ht => (hPF t ht).1) (fun t ht => (hPF t ht).2.1) hlim
  have hfa : f a = H.eRe 1 := by simp [hf, HalfPeriods.eRe, HalfPeriods.e, hω₁]
  have hfx : H.eRe 1 ≤ f x := by
    rcases hx.2.lt_or_eq with h | h
    · exact hfa ▸ (hSA hx ⟨ha, le_rfl⟩ h).le
    · rw [h, hfa]
  refine ⟨hR x, hfx, ?_⟩
  have key := integral_image_one_div_sqrt (s := Ioo 0 x) measurableSet_Ioo (f := f)
    (f' := fun t => (H.derivWeierstrassP (t : ℂ) * 1).re)
    (Q := fun u => (u - H.eRe 1) * (u - H.eRe 2) * (u - H.eRe 3))
    (fun t (ht : t ∈ Ioo 0 x) => ((hPF t ⟨ht.1, ht.2.trans_le hx.2⟩).1).hasDerivWithinAt)
    (hSA.injOn.mono (Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc_right hx.2)))
    (fun t (ht : t ∈ Ioo 0 x) => by
      have := hSA ⟨ht.1, ht.2.le.trans hx.2⟩ hx ht.2
      simp only [HalfPeriods.eRe] at *
      exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
    (fun t (ht : t ∈ Ioo 0 x) => by
      have := hSA ⟨ht.1, ht.2.le.trans hx.2⟩ hx ht.2
      rw [(hPF t ⟨ht.1, ht.2.trans_le hx.2⟩).2.2, abs_of_pos]
      simp only [HalfPeriods.eRe] at *
      exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
  rw [himg x hx, Real.volume_real_Ioo_of_le hx.1.le] at key
  rw [key]; ring

/-- DLMF 23.6.31: rectangular lattice, `z = ω₁ + iy ∈ [ω₁, ω₁ + ω₃]`: `t = ℘(z)` is real,
`e₂ ≤ t ≤ e₁` and `z - ω₁ = (i/2) ∫_t^{e₁} du/√((e₁ - u)(u - e₂)(u - e₃))`. -/
@[dlmf 23.6.E31]
theorem rectangular_integral_two {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) {y : ℝ} (hy : y ∈ Set.Icc 0 b) :
    (H.weierstrassP (a + y * I)).im = 0 ∧ H.eRe 2 ≤ (H.weierstrassP (a + y * I)).re ∧
      (H.weierstrassP (a + y * I)).re ≤ H.eRe 1 ∧
      ((a + y * I : ℂ) - H.ω₁) = I / 2 * ((∫ u in (H.weierstrassP (a + y * I)).re..H.eRe 1,
        1 / Real.sqrt ((H.eRe 1 - u) * (u - H.eRe 2) * (u - H.eRe 3)) : ℝ) : ℂ) := by
  obtain ⟨he1, he2, he3, h21, h32, -, -⟩ := (isRectangular_of_eq ha hb hω₁ hω₃).roots
  have hinv := rectangular_conj_mem hω₁ hω₃
  set f : ℝ → ℝ := fun s => (H.weierstrassP ((a : ℂ) + s * I)).re with hf
  have h2a : (2 * a : ℂ) ∈ H.lattice := H.mem_lattice_iff.mpr ⟨1, 0, by rw [hω₁]; push_cast; ring⟩
  have hR : ∀ t : ℝ, (H.weierstrassP ((a : ℂ) + t * I)).im = 0 := fun t =>
    weierstrassP_im_eq_zero_of_conj hinv h2a (Or.inr (by apply Complex.ext <;> simp; ring))
  have hnot : ∀ t : ℝ, (a : ℂ) + t * I ∉ H.lattice := by
    intro t hm
    obtain ⟨⟨m, hm⟩, -⟩ := rectangular_mem_lattice hω₁ hω₃ hm
    simp at hm
    exact false_of_eq_int_mul (by linarith) hm ha (by linarith)
  have hL : ∀ t ∈ Ioo 0 b, (a : ℂ) + t * I ∉ H.lattice ∧ 2 * ((a : ℂ) + t * I) ∉ H.lattice := by
    intro t ht
    refine ⟨hnot t, fun hm => ?_⟩
    obtain ⟨-, ⟨n, hn⟩⟩ := rectangular_mem_lattice hω₁ hω₃ hm
    simp at hn
    exact false_of_eq_int_mul (by linarith) hn (by linarith [ht.1]) (by linarith [ht.2])
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (a : ℂ) + s * I) I t := fun t => by
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add (a : ℂ)
  have hPF : ∀ t ∈ Ioo 0 b, HasDerivAt f (H.derivWeierstrassP ((a : ℂ) + t * I) * I).re t ∧
      (H.derivWeierstrassP ((a : ℂ) + t * I) * I).re ≠ 0 ∧
      |(H.derivWeierstrassP ((a : ℂ) + t * I) * I).re| = 2 * Real.sqrt
        |(f t - (H.e 1).re) * (f t - (H.e 2).re) * (f t - (H.e 3).re)| := fun t ht =>
    H.path_facts (by simp) hγ hL (fun t _ => hR t) he1 he2 he3 ht
  have hcI : ContinuousOn f (Icc 0 b) := fun t _ =>
    (H.continuousAt_re_weierstrassP_comp hγ (hnot t)).continuousWithinAt
  have hf0 : f 0 = H.eRe 1 := by simp [hf, HalfPeriods.eRe, HalfPeriods.e, hω₁]
  have hfb : f b = H.eRe 2 := by simp [hf, HalfPeriods.eRe, rectangular_e_two hω₁ hω₃]
  have hSA : StrictAntiOn f (Icc 0 b) :=
    hcI.strictAntiOn_of_injOn_Icc hb.le (by rw [hf0, hfb]; exact h21.le)
      (injOn_Icc_of_hasDerivAt_ne_zero hcI (fun t ht => (hPF t ht).1) (fun t ht => (hPF t ht).2.1))
  have hb' : b ∈ Icc 0 b := ⟨hb.le, le_rfl⟩
  have h0' : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hfy1 : f y ≤ H.eRe 1 := hf0 ▸ hSA.antitoneOn h0' hy hy.1
  have hfy2 : H.eRe 2 ≤ f y := hfb ▸ hSA.antitoneOn hy hb' hy.2
  refine ⟨hR y, hfy2, hfy1, ?_⟩
  have himg := image_Ioo_of_strictAntiOn_Icc hcI hSA hy
  have key := integral_image_one_div_sqrt (s := Ioo 0 y) measurableSet_Ioo (f := f)
    (f' := fun t => (H.derivWeierstrassP ((a : ℂ) + t * I) * I).re)
    (Q := fun u => (H.eRe 1 - u) * (u - H.eRe 2) * (u - H.eRe 3))
    (fun t (ht : t ∈ Ioo 0 y) => ((hPF t ⟨ht.1, ht.2.trans_le hy.2⟩).1).hasDerivWithinAt)
    (hSA.injOn.mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hy.2)))
    (fun t (ht : t ∈ Ioo 0 y) => by
      have h1 : f t ∈ Ioo (f y) (f 0) := himg ▸ mem_image_of_mem f ht
      rw [hf0] at h1
      simp only [HalfPeriods.eRe] at *
      exact mul_pos (mul_pos (by linarith [h1.2]) (by linarith [h1.1])) (by linarith [h1.1]))
    (fun t (ht : t ∈ Ioo 0 y) => by
      have h1 : f t ∈ Ioo (f y) (f 0) := himg ▸ mem_image_of_mem f ht
      rw [hf0] at h1
      rw [(hPF t ⟨ht.1, ht.2.trans_le hy.2⟩).2.2, abs_of_neg]
      · ring_nf
      simp only [HalfPeriods.eRe] at *
      have : 0 < (H.e 1).re - f t := by linarith [h1.2]
      have : 0 < f t - (H.e 2).re := by linarith [h1.1]
      have : 0 < f t - (H.e 3).re := by linarith [h1.1]
      nlinarith [mul_pos (mul_pos this ‹0 < f t - (H.e 2).re›) ‹0 < (H.e 1).re - f t›])
  rw [himg, hf0, Real.volume_real_Ioo_of_le hy.1, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hfy1] at key
  rw [key, hω₁]; push_cast; ring

/-- DLMF 23.6.32: rectangular lattice, `z = ω₃ + x ∈ [ω₃, ω₁ + ω₃]`: `t = ℘(z)` is real,
`e₃ ≤ t ≤ e₂` and `z - ω₃ = ½ ∫_{e₃}^t du/√((e₁ - u)(e₂ - u)(u - e₃))`. -/
@[dlmf 23.6.E32]
theorem rectangular_integral_three {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) {x : ℝ} (hx : x ∈ Set.Icc 0 a) :
    (H.weierstrassP (x + b * I)).im = 0 ∧ H.eRe 3 ≤ (H.weierstrassP (x + b * I)).re ∧
      (H.weierstrassP (x + b * I)).re ≤ H.eRe 2 ∧
      ((x + b * I : ℂ) - H.ω₃) = ((1 / 2 * ∫ u in H.eRe 3..(H.weierstrassP (x + b * I)).re,
        1 / Real.sqrt ((H.eRe 1 - u) * (H.eRe 2 - u) * (u - H.eRe 3)) : ℝ) : ℂ) := by
  obtain ⟨he1, he2, he3, h21, h32, -, -⟩ := (isRectangular_of_eq ha hb hω₁ hω₃).roots
  have hinv := rectangular_conj_mem hω₁ hω₃
  set f : ℝ → ℝ := fun s => (H.weierstrassP ((s : ℂ) + b * I)).re with hf
  have h2b : (-(2 * b * I) : ℂ) ∈ H.lattice :=
    H.mem_lattice_iff.mpr ⟨0, -1, by rw [hω₃]; push_cast; ring⟩
  have hR : ∀ t : ℝ, (H.weierstrassP ((t : ℂ) + b * I)).im = 0 := fun t =>
    weierstrassP_im_eq_zero_of_conj hinv h2b (Or.inl (by apply Complex.ext <;> simp; ring))
  have hnot : ∀ t : ℝ, (t : ℂ) + b * I ∉ H.lattice := by
    intro t hm
    obtain ⟨-, ⟨n, hn⟩⟩ := rectangular_mem_lattice hω₁ hω₃ hm
    simp at hn
    exact false_of_eq_int_mul (by linarith) hn hb (by linarith)
  have hL : ∀ t ∈ Ioo 0 a, (t : ℂ) + b * I ∉ H.lattice ∧ 2 * ((t : ℂ) + b * I) ∉ H.lattice := by
    intro t ht
    refine ⟨hnot t, fun hm => ?_⟩
    obtain ⟨⟨m, hm⟩, -⟩ := rectangular_mem_lattice hω₁ hω₃ hm
    simp at hm
    exact false_of_eq_int_mul (by linarith) hm (by linarith [ht.1]) (by linarith [ht.2])
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ) + b * I) 1 t := fun t => by
    simpa using ((hasDerivAt_id t).ofReal_comp).add_const ((b : ℂ) * I)
  have hPF : ∀ t ∈ Ioo 0 a, HasDerivAt f (H.derivWeierstrassP ((t : ℂ) + b * I) * 1).re t ∧
      (H.derivWeierstrassP ((t : ℂ) + b * I) * 1).re ≠ 0 ∧
      |(H.derivWeierstrassP ((t : ℂ) + b * I) * 1).re| = 2 * Real.sqrt
        |(f t - (H.e 1).re) * (f t - (H.e 2).re) * (f t - (H.e 3).re)| := fun t ht =>
    H.path_facts (by simp) hγ hL (fun t _ => hR t) he1 he2 he3 ht
  have hcI : ContinuousOn f (Icc 0 a) := fun t _ =>
    (H.continuousAt_re_weierstrassP_comp hγ (hnot t)).continuousWithinAt
  have hf0 : f 0 = H.eRe 3 := by simp [hf, HalfPeriods.eRe, HalfPeriods.e, hω₃]
  have hfa : f a = H.eRe 2 := by simp [hf, HalfPeriods.eRe, rectangular_e_two hω₁ hω₃]
  have hSM : StrictMonoOn f (Icc 0 a) :=
    hcI.strictMonoOn_of_injOn_Icc ha.le (by rw [hf0, hfa]; exact h32.le)
      (injOn_Icc_of_hasDerivAt_ne_zero hcI (fun t ht => (hPF t ht).1) (fun t ht => (hPF t ht).2.1))
  have ha' : a ∈ Icc 0 a := ⟨ha.le, le_rfl⟩
  have h0' : (0 : ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
  have hfx3 : H.eRe 3 ≤ f x := hf0 ▸ hSM.monotoneOn h0' hx hx.1
  have hfx2 : f x ≤ H.eRe 2 := hfa ▸ hSM.monotoneOn hx ha' hx.2
  refine ⟨hR x, hfx3, hfx2, ?_⟩
  have himg := image_Ioo_of_strictMonoOn_Icc hcI hSM hx
  have key := integral_image_one_div_sqrt (s := Ioo 0 x) measurableSet_Ioo (f := f)
    (f' := fun t => (H.derivWeierstrassP ((t : ℂ) + b * I) * 1).re)
    (Q := fun u => (H.eRe 1 - u) * (H.eRe 2 - u) * (u - H.eRe 3))
    (fun t (ht : t ∈ Ioo 0 x) => ((hPF t ⟨ht.1, ht.2.trans_le hx.2⟩).1).hasDerivWithinAt)
    (hSM.injOn.mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hx.2)))
    (fun t (ht : t ∈ Ioo 0 x) => by
      have h1 : f t ∈ Ioo (f 0) (f x) := himg ▸ mem_image_of_mem f ht
      rw [hf0] at h1
      simp only [HalfPeriods.eRe] at *
      exact mul_pos (mul_pos (by linarith [h1.2]) (by linarith [h1.2])) (by linarith [h1.1]))
    (fun t (ht : t ∈ Ioo 0 x) => by
      have h1 : f t ∈ Ioo (f 0) (f x) := himg ▸ mem_image_of_mem f ht
      rw [hf0] at h1
      rw [(hPF t ⟨ht.1, ht.2.trans_le hx.2⟩).2.2, abs_of_pos]
      · ring_nf
      simp only [HalfPeriods.eRe] at *
      have : 0 < (H.e 1).re - f t := by linarith [h1.2]
      have : 0 < (H.e 2).re - f t := by linarith [h1.2]
      have : 0 < f t - (H.e 3).re := by linarith [h1.1]
      nlinarith [mul_pos (mul_pos ‹0 < (H.e 1).re - f t› ‹0 < (H.e 2).re - f t›) this])
  rw [himg, hf0, Real.volume_real_Ioo_of_le hx.1, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hfx3] at key
  rw [key, hω₃]; push_cast; ring

/-- DLMF 23.6.33: rectangular lattice, `z = iy ∈ (0, ω₃]`: `t = ℘(z)` is real, `t ≤ e₃` and
`z = (i/2) ∫_{-∞}^t du/√((e₁ - u)(e₂ - u)(e₃ - u))`. -/
@[dlmf 23.6.E33]
theorem rectangular_integral_four {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) {y : ℝ} (hy : y ∈ Set.Ioc 0 b) :
    (H.weierstrassP (y * I)).im = 0 ∧ (H.weierstrassP (y * I)).re ≤ H.eRe 3 ∧
      (y * I : ℂ) = I / 2 * ((∫ u in Set.Iio (H.weierstrassP (y * I)).re,
        1 / Real.sqrt ((H.eRe 1 - u) * (H.eRe 2 - u) * (H.eRe 3 - u)) : ℝ) : ℂ) := by
  obtain ⟨he1, he2, he3, h21, h32, -, -⟩ := (isRectangular_of_eq ha hb hω₁ hω₃).roots
  have hinv := rectangular_conj_mem hω₁ hω₃
  set f : ℝ → ℝ := fun s => (H.weierstrassP ((s : ℂ) * I)).re with hf
  have hR : ∀ t : ℝ, (H.weierstrassP ((t : ℂ) * I)).im = 0 := fun t =>
    weierstrassP_im_eq_zero_of_conj hinv (zero_mem _) (Or.inr (by apply Complex.ext <;> simp))
  have hnot : ∀ t ∈ Ioc 0 b, (t : ℂ) * I ∉ H.lattice := by
    intro t ht hm
    obtain ⟨-, ⟨n, hn⟩⟩ := rectangular_mem_lattice hω₁ hω₃ hm
    simp at hn
    exact false_of_eq_int_mul (by linarith) hn ht.1 (by linarith [ht.2])
  have hL : ∀ t ∈ Ioo 0 b, (t : ℂ) * I ∉ H.lattice ∧ 2 * ((t : ℂ) * I) ∉ H.lattice := by
    intro t ht
    refine ⟨hnot t ⟨ht.1, ht.2.le⟩, fun hm => ?_⟩
    obtain ⟨-, ⟨n, hn⟩⟩ := rectangular_mem_lattice hω₁ hω₃ hm
    simp at hn
    exact false_of_eq_int_mul (by linarith) hn (by linarith [ht.1]) (by linarith [ht.2])
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ) * I) I t := fun t => by
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I)
  have hPF : ∀ t ∈ Ioo 0 b, HasDerivAt f (H.derivWeierstrassP ((t : ℂ) * I) * I).re t ∧
      (H.derivWeierstrassP ((t : ℂ) * I) * I).re ≠ 0 ∧
      |(H.derivWeierstrassP ((t : ℂ) * I) * I).re| = 2 * Real.sqrt
        |(f t - (H.e 1).re) * (f t - (H.e 2).re) * (f t - (H.e 3).re)| := fun t ht =>
    H.path_facts (by simp) hγ hL (fun t _ => hR t) he1 he2 he3 ht
  have hcont : ∀ t ∈ Ioc 0 b, ContinuousAt (fun s => -f s) t := fun t ht =>
    (H.continuousAt_re_weierstrassP_comp hγ (hnot t ht)).neg
  have hlim : Tendsto (fun s => -f s) (𝓝[>] 0) atTop := by
    have hg := analyticAt_weierstrassP_sub H.periodPair (zero_mem _)
    have h1 : ContinuousAt (fun t : ℝ => H.weierstrassP (t * I) - 1 / ((t : ℂ) * I - 0) ^ 2) 0 :=
      hg.continuousAt.comp_of_eq ((Complex.continuous_ofReal.mul continuous_const).continuousAt)
        (by simp)
    obtain ⟨C, hgc⟩ : ∃ C, Tendsto
        (fun t : ℝ => -(H.weierstrassP (t * I) - 1 / ((t : ℂ) * I - 0) ^ 2).re) (𝓝[>] 0) (𝓝 C) :=
      ⟨_, (Complex.continuous_re.continuousAt.comp h1).neg.tendsto.mono_left nhdsWithin_le_nhds⟩
    have hinf : Tendsto (fun t : ℝ => (t ^ 2)⁻¹) (𝓝[>] 0) atTop := by
      have := (tendsto_pow_atTop (two_ne_zero)).comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
      simpa [Function.comp_def, inv_pow] using this
    refine (hinf.atTop_add hgc).congr' ?_
    filter_upwards with t
    have : (1 / ((t : ℂ) * I - 0) ^ 2) = ((-(t ^ 2)⁻¹ : ℝ) : ℂ) := by
      push_cast; rw [sub_zero, mul_pow, I_sq]; ring
    simp only [hf, this, sub_re, ofReal_re]
    ring
  obtain ⟨hSA, himg⟩ := strictAntiOn_Ioc_of_tendsto_atTop (c := b) hcont
    (f' := fun t => -(H.derivWeierstrassP ((t : ℂ) * I) * I).re)
    (fun t ht => (hPF t ht).1.neg) (fun t ht => neg_ne_zero.mpr (hPF t ht).2.1) hlim
  have hfb : f b = H.eRe 3 := by simp [hf, HalfPeriods.eRe, HalfPeriods.e, hω₃]
  have hfy : f y ≤ H.eRe 3 := by
    rcases hy.2.lt_or_eq with h | h
    · have := hSA hy ⟨hb, le_rfl⟩ h
      simp only at this
      linarith
    · rw [h, hfb]
  refine ⟨hR y, hfy, ?_⟩
  have himg' : f '' Ioo 0 y = Iio (f y) := by
    ext u
    have := congrArg (fun S => u ∈ (fun w => -w) '' S) (himg y hy)
    simp only [image_image, neg_neg] at this
    rw [this]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact mem_Iio.mpr (neg_lt.mp (mem_Ioi.mp hw))
    · intro hu; exact ⟨-u, by simpa [neg_lt_neg_iff] using hu, neg_neg u⟩
  have hinj : InjOn f (Ioo 0 y) := fun s hs t ht hst =>
    hSA.injOn (Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc_right hy.2) hs)
      (Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc_right hy.2) ht) (by simp [hst])
  have key := integral_image_one_div_sqrt (s := Ioo 0 y) measurableSet_Ioo (f := f)
    (f' := fun t => (H.derivWeierstrassP ((t : ℂ) * I) * I).re)
    (Q := fun u => (H.eRe 1 - u) * (H.eRe 2 - u) * (H.eRe 3 - u))
    (fun t (ht : t ∈ Ioo 0 y) => ((hPF t ⟨ht.1, ht.2.trans_le hy.2⟩).1).hasDerivWithinAt)
    hinj
    (fun t (ht : t ∈ Ioo 0 y) => by
      have h1 : f t ∈ Iio (f y) := himg' ▸ mem_image_of_mem f ht
      simp only [HalfPeriods.eRe, mem_Iio] at *
      exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
    (fun t (ht : t ∈ Ioo 0 y) => by
      have h1 : f t ∈ Iio (f y) := himg' ▸ mem_image_of_mem f ht
      rw [(hPF t ⟨ht.1, ht.2.trans_le hy.2⟩).2.2, abs_of_neg]
      · ring_nf
      simp only [HalfPeriods.eRe, mem_Iio] at *
      have : 0 < (H.e 1).re - f t := by linarith
      have : 0 < (H.e 2).re - f t := by linarith
      have : 0 < (H.e 3).re - f t := by linarith
      nlinarith [mul_pos (mul_pos ‹0 < (H.e 1).re - f t› ‹0 < (H.e 2).re - f t›) this])
  rw [himg', Real.volume_real_Ioo_of_le hy.1.le] at key
  rw [key]; push_cast; ring

/-- DLMF 23.6.34: rectangular lattice,
`2ω₁ = ∫_{e₁}^∞ du/√((u - e₁)(u - e₂)(u - e₃)) = ∫_{e₃}^{e₂} du/√((e₁ - u)(e₂ - u)(u - e₃))`. -/
@[dlmf 23.6.E34]
theorem rectangular_two_ω₁ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) :
    2 * a = ∫ u in Set.Ioi (H.eRe 1),
        1 / Real.sqrt ((u - H.eRe 1) * (u - H.eRe 2) * (u - H.eRe 3)) ∧
      2 * a = ∫ u in H.eRe 3..H.eRe 2,
        1 / Real.sqrt ((H.eRe 1 - u) * (H.eRe 2 - u) * (u - H.eRe 3)) := by
  have h1 : (H.weierstrassP (a : ℂ)).re = H.eRe 1 := by simp [HalfPeriods.eRe, HalfPeriods.e, hω₁]
  have h2 : (H.weierstrassP ((a : ℂ) + b * I)).re = H.eRe 2 := by
    simp [HalfPeriods.eRe, rectangular_e_two hω₁ hω₃]
  obtain ⟨-, -, k1⟩ := H.rectangular_integral_one ha hb hω₁ hω₃ ⟨ha, le_rfl⟩
  obtain ⟨-, -, -, k3⟩ := H.rectangular_integral_three ha hb hω₁ hω₃ ⟨ha.le, le_rfl⟩
  rw [h1] at k1
  rw [h2, hω₃, add_sub_cancel_right] at k3
  refine ⟨by linarith, ?_⟩
  have := congrArg Complex.re k3
  simp only [ofReal_re] at this
  linarith

/-- DLMF 23.6.35: rectangular lattice, `2ω₃ = i ∫_{e₂}^{e₁} du/√((e₁ - u)(u - e₂)(u - e₃))
= i ∫_{-∞}^{e₃} du/√((e₁ - u)(e₂ - u)(e₃ - u))`; with `ω₃ = ib` this says `2b` equals both
integrals. -/
@[dlmf 23.6.E35]
theorem rectangular_two_ω₃ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) :
    2 * b = ∫ u in H.eRe 2..H.eRe 1,
        1 / Real.sqrt ((H.eRe 1 - u) * (u - H.eRe 2) * (u - H.eRe 3)) ∧
      2 * b = ∫ u in Set.Iio (H.eRe 3),
        1 / Real.sqrt ((H.eRe 1 - u) * (H.eRe 2 - u) * (H.eRe 3 - u)) := by
  have h2 : (H.weierstrassP ((a : ℂ) + b * I)).re = H.eRe 2 := by
    simp [HalfPeriods.eRe, rectangular_e_two hω₁ hω₃]
  have h3 : (H.weierstrassP ((b : ℂ) * I)).re = H.eRe 3 := by
    simp [HalfPeriods.eRe, HalfPeriods.e, hω₃]
  obtain ⟨-, -, -, k2⟩ := H.rectangular_integral_two ha hb hω₁ hω₃ ⟨hb.le, le_rfl⟩
  obtain ⟨-, -, k4⟩ := H.rectangular_integral_four ha hb hω₁ hω₃ ⟨hb, le_rfl⟩
  rw [h2, hω₁, add_sub_cancel_left] at k2
  rw [h3] at k4
  constructor
  · have := congrArg Complex.im k2
    simp only [one_div] at this ⊢
    simp at this
    linarith
  · have := congrArg Complex.im k4
    simp only [one_div] at this ⊢
    simp at this
    linarith

end HalfPeriods

end DLMF.Weierstrass
