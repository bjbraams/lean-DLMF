/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.FurtherTransformations

/-!
# Cubic transformations for special values (DLMF §15.4(iii))

Two of Goursat's cubic transformations, proved on cone-shaped convex domains around real
segments, for the special-argument evaluations 15.4.31 and 15.4.32:

* `hypSV_cubic_psi`: `F(3a, 3a+1/2; 2a+5/6; z) = (1-9z)^{-2a} F(a, a+1/2; 2a+5/6; ψ(z))`,
  `ψ(z) = -27z(1-z)²/(1-9z)²`, with `1 - ψ(z) = (1+3z)³/(1-9z)²`;
* `hypSV_cubic_two`: `F(3a, 1/3-a; 2a+5/6; u) = (1-4u)^{-3a} F(a, a+1/3; 2a+5/6; s(u))`,
  `s(u) = 27u/(4u-1)³`, with `1 - s(u) = (1+8u)²(1-u)/(1-4u)³`.

The proofs follow `cubic_transformation` (15.8.31): both sides solve the same Gauss equation
near the origin, and the identity is continued through the cut-plane continuation
`regularizedGaussHG`. The image of the domain lies in the cut plane because `1 - ψ(z)`
(resp. `1 - s(u)`) has positive real part there; this is checked with elementary tangent bounds
for products (`hypSV_tan_mul`, `hypSV_tan_recip`).
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- Tangent bound for a product: if `|Im wᵢ| ≤ tᵢ Re wᵢ` with `Re wᵢ > 0` and `t₁t₂ < 1`, then
`w₁w₂` has positive real part and `|Im(w₁w₂)| ≤ T Re(w₁w₂)` whenever `t₁ + t₂ ≤ T(1 - t₁t₂)`. -/
theorem hypSV_tan_mul {w₁ w₂ : ℂ} {t₁ t₂ T : ℝ} (h₁ : 0 < w₁.re) (h₂ : 0 < w₂.re)
    (ht₁ : |w₁.im| ≤ t₁ * w₁.re) (ht₂ : |w₂.im| ≤ t₂ * w₂.re) (hlt : t₁ * t₂ < 1)
    (hT : t₁ + t₂ ≤ T * (1 - t₁ * t₂)) :
    0 < (w₁ * w₂).re ∧ |(w₁ * w₂).im| ≤ T * (w₁ * w₂).re := by
  simp only [mul_re, mul_im]
  have hp : 0 < w₁.re * w₂.re := mul_pos h₁ h₂
  have ht₁0 : 0 ≤ t₁ := by
    by_contra h; push Not at h; nlinarith [abs_nonneg w₁.im]
  have ht₂0 : 0 ≤ t₂ := by
    by_contra h; push Not at h; nlinarith [abs_nonneg w₂.im]
  have hb : |w₁.im * w₂.im| ≤ t₁ * t₂ * (w₁.re * w₂.re) := by
    rw [abs_mul]
    calc |w₁.im| * |w₂.im| ≤ (t₁ * w₁.re) * (t₂ * w₂.re) :=
          mul_le_mul ht₁ ht₂ (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hre : (1 - t₁ * t₂) * (w₁.re * w₂.re) ≤ w₁.re * w₂.re - w₁.im * w₂.im := by
    have := (abs_le.mp hb).2; nlinarith
  have hpos : 0 < (1 - t₁ * t₂) * (w₁.re * w₂.re) := mul_pos (by linarith) hp
  refine ⟨by linarith, ?_⟩
  have hT0 : 0 ≤ T := by
    by_contra h; push Not at h; nlinarith
  have hi : |w₁.re * w₂.im + w₁.im * w₂.re| ≤ (t₁ + t₂) * (w₁.re * w₂.re) := by
    calc _ ≤ |w₁.re * w₂.im| + |w₁.im * w₂.re| := abs_add_le _ _
      _ = w₁.re * |w₂.im| + |w₁.im| * w₂.re := by
          rw [abs_mul, abs_mul, abs_of_pos h₁, abs_of_pos h₂]
      _ ≤ w₁.re * (t₂ * w₂.re) + (t₁ * w₁.re) * w₂.re := by gcongr
      _ = _ := by ring
  calc _ ≤ (t₁ + t₂) * (w₁.re * w₂.re) := hi
    _ ≤ T * (1 - t₁ * t₂) * (w₁.re * w₂.re) := mul_le_mul_of_nonneg_right hT hp.le
    _ = T * ((1 - t₁ * t₂) * (w₁.re * w₂.re)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hre hT0

/-- Tangent bound for a reciprocal. -/
theorem hypSV_tan_recip {w : ℂ} {t : ℝ} (h : 0 < w.re) (ht : |w.im| ≤ t * w.re) :
    0 < (w⁻¹).re ∧ |(w⁻¹).im| ≤ t * (w⁻¹).re := by
  have hn : 0 < normSq w := normSq_pos.mpr (by rintro rfl; simp at h)
  rw [inv_re, inv_im]
  refine ⟨div_pos h hn, ?_⟩
  rw [neg_div, abs_neg, abs_div, abs_of_pos hn, mul_div_assoc']
  exact div_le_div_of_nonneg_right ht hn.le

/-- On the cone domain of the cubic map `ψ(z) = -27z(1-z)²/(1-9z)²`, `1 - ψ z` has positive
real part. -/
theorem hypSV_psi_one_sub_re_pos {w : ℂ} (h₁ : 30 * |w.im| < 1 + 3 * w.re)
    (h₂ : 30 * |w.im| < 1 - 9 * w.re) :
    0 < (1 - (-27 * w * (1 - w) ^ 2 / (1 - 9 * w) ^ 2)).re := by
  have hq0 : 1 - 9 * w ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith [abs_nonneg w.im]
  have hid : 1 - (-27 * w * (1 - w) ^ 2 / (1 - 9 * w) ^ 2) =
      ((1 + 3 * w) * (1 + 3 * w)) * (1 + 3 * w) * ((1 - 9 * w)⁻¹ * (1 - 9 * w)⁻¹) := by
    obtain ⟨u, hu⟩ : ∃ u, u = 1 - 9 * w := ⟨_, rfl⟩
    have hwu : w = (1 - u) / 9 := by rw [hu]; ring
    have hu0 : u ≠ 0 := by rw [hu]; exact hq0
    subst hwu
    rw [show (1 : ℂ) - 9 * ((1 - u) / 9) = u by ring]
    field_simp
    ring
  rw [hid]
  have hpre : 0 < (1 + 3 * w).re := by simp; linarith [abs_nonneg w.im]
  have hpim : |(1 + 3 * w).im| ≤ 1 / 10 * (1 + 3 * w).re := by
    simp [abs_mul]; linarith
  have hqre : 0 < (1 - 9 * w).re := by simp; linarith [abs_nonneg w.im]
  have hqim : |(1 - 9 * w).im| ≤ 3 / 10 * (1 - 9 * w).re := by
    simp [abs_mul]; linarith
  obtain ⟨hq1, hq2⟩ := hypSV_tan_recip hqre hqim
  obtain ⟨hp2r, hp2i⟩ := hypSV_tan_mul (T := 21 / 100) hpre hpre hpim hpim (by norm_num) (by norm_num)
  obtain ⟨hp3r, hp3i⟩ := hypSV_tan_mul (T := 8 / 25) hp2r hpre hp2i hpim (by norm_num) (by norm_num)
  obtain ⟨hq2r, hq2i⟩ := hypSV_tan_mul (T := 2 / 3) hq1 hq1 hq2 hq2 (by norm_num) (by norm_num)
  exact (hypSV_tan_mul (T := 2) hp3r hq2r hp3i hq2i (by norm_num) (by norm_num)).1

/-- A cubic transformation (Goursat), the `z ↦ 1 - z` image of DLMF 15.8.31:
`F(3a, 3a+1/2; 2a+5/6; z) = (1-9z)^{-2a} F(a, a+1/2; 2a+5/6; -27z(1-z)²/(1-9z)²)` on the cone
domain around `(-1/3, 1/9)` (where the image stays in the unit disk). -/
theorem hypSV_cubic_psi {a z : ℂ} (hc : ∀ k : ℕ, 2 * a + 5 / 6 ≠ -(k : ℂ))
    (h₁ : 30 * |z.im| < 1 + 3 * z.re) (h₂ : 30 * |z.im| < 1 - 9 * z.re)
    (hw : ‖-27 * z * (1 - z) ^ 2 / (1 - 9 * z) ^ 2‖ < 1) :
    ₂F₁ (3 * a) (3 * a + 1 / 2) (2 * a + 5 / 6) z =
      (1 - 9 * z) ^ (-2 * a) *
        ₂F₁ a (a + 1 / 2) (2 * a + 5 / 6) (-27 * z * (1 - z) ^ 2 / (1 - 9 * z) ^ 2) := by
  set H : ℂ → ℂ := ₂F₁ a (a + 1 / 2) (2 * a + 5 / 6) with hH
  set P : ℂ → ℂ := fun w => (1 + (-9) * w) ^ (-2 * a) with hP
  set φ : ℂ → ℂ := fun w => -27 * w * (1 - w) ^ 2 / (1 - 9 * w) ^ 2 with hφdef
  set D : Set ℂ := {w | 30 * |w.im| < 1 + 3 * w.re ∧ 30 * |w.im| < 1 - 9 * w.re} with hD
  have hsmall : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 100), ‖w‖ < 1 / 100 := fun w hw => by simpa using hw
  have hballD : ∀ w : ℂ, ‖w‖ < 1 / 100 → w ∈ D := by
    intro w hw
    have h1 := abs_re_le_norm w
    have h2 := abs_im_le_norm w
    rw [abs_le] at h1
    exact ⟨by linarith, by linarith⟩
  have hq0 : ∀ w ∈ D, 1 - 9 * w ≠ 0 := by
    intro w hw h; have := congrArg re h; simp at this; linarith [abs_nonneg w.im, hw.2]
  have hslit : ∀ w ∈ D, 1 + (-9) * w ∈ slitPlane := by
    intro w hw
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    simp; linarith [abs_nonneg w.im, hw.2]
  have hnorm : ∀ w ∈ D, ‖w‖ < 1 := by
    intro w hw
    have := norm_le_abs_re_add_abs_im w
    have hr : |w.re| < 1 / 3 := by
      rw [abs_lt]; constructor <;> linarith [abs_nonneg w.im, hw.1, hw.2]
    have hi : |w.im| < 1 / 30 := by linarith [hw.1, hw.2]
    linarith
  have hφn : ∀ w : ℂ, ‖w‖ < 1 / 100 → ‖φ w‖ < 1 := by
    intro w hw
    have h1 : 91 / 100 ≤ ‖1 - 9 * w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (9 * w)
      rw [norm_one, norm_mul, show ‖(9 : ℂ)‖ = 9 by norm_num] at this
      linarith
    have h2 : ‖1 - w‖ ≤ 101 / 100 := by
      have := norm_sub_le (1 : ℂ) w; rw [norm_one] at this; linarith
    simp only [hφdef, norm_div, norm_mul, norm_pow, norm_neg, show ‖(27 : ℂ)‖ = 27 by norm_num]
    rw [div_lt_one (by positivity)]
    have hw0 := norm_nonneg w
    calc 27 * ‖w‖ * ‖1 - w‖ ^ 2 ≤ 27 * (1 / 100) * (101 / 100) ^ 2 := by gcongr
      _ < (91 / 100) ^ 2 := by norm_num
      _ ≤ ‖1 - 9 * w‖ ^ 2 := by gcongr
  have hPa : ∀ w ∈ D, AnalyticAt ℂ P w := fun w hw =>
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const (hslit w hw)
  have hφa : ∀ w ∈ D, AnalyticAt ℂ φ w := fun w hw =>
    (((analyticAt_const.mul analyticAt_id).mul ((analyticAt_const.sub analyticAt_id).pow 2)).div
      ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).pow 2)) (pow_ne_zero 2 (hq0 w hw))
  have hDopen : IsOpen D := by
    rw [hD, Set.ofPred_and]
    exact (isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop))
  have hφd : ∀ w ∈ D, HasDerivAt φ (-27 * (1 - w) * (1 + 3 * w) ^ 2 / (1 - 9 * w) ^ 3) w := by
    intro w hw
    have h := ((((hasDerivAt_id w).const_mul (-27 : ℂ))).mul
      (((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).pow 2)).div
      (((hasDerivAt_const w (1 : ℂ)).sub ((hasDerivAt_id w).const_mul (9 : ℂ))).pow 2)
      (pow_ne_zero 2 (hq0 w hw))
    refine h.congr_deriv ?_
    have hq := hq0 w hw
    simp only [id, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Nat.cast_ofNat,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    obtain ⟨u, hu⟩ : ∃ u, u = 1 - 9 * w := ⟨_, rfl⟩
    have hwu : w = (1 - u) / 9 := by rw [hu]; ring
    have hu0 : u ≠ 0 := by rw [hu]; exact hq
    subst hwu
    rw [show (1 : ℂ) - 9 * ((1 - u) / 9) = u by ring]
    field_simp
    ring
  have hφdd : ∀ w ∈ D, deriv (deriv φ) w = -864 * (1 + 3 * w) / (1 - 9 * w) ^ 4 := by
    intro w hw
    have hev : deriv φ =ᶠ[𝓝 w] fun v => -27 * (1 - v) * (1 + 3 * v) ^ 2 / (1 - 9 * v) ^ 3 := by
      filter_upwards [hDopen.mem_nhds hw] with v hv
      exact (hφd v hv).deriv
    rw [hev.deriv_eq]
    have h := ((((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).const_mul (-27 : ℂ)).mul
      ((((hasDerivAt_id w).const_mul (3 : ℂ)).const_add 1).pow 2)).div
      (((hasDerivAt_const w (1 : ℂ)).sub ((hasDerivAt_id w).const_mul (9 : ℂ))).pow 3)
      (pow_ne_zero 3 (hq0 w hw))
    have h' : HasDerivAt (fun v => -27 * (1 - v) * (1 + 3 * v) ^ 2 / (1 - 9 * v) ^ 3) _ w := h
    rw [h'.deriv]
    have hq := hq0 w hw
    simp only [id, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Nat.cast_ofNat,
      show (2 : ℕ) - 1 = 1 from rfl, show (3 : ℕ) - 1 = 2 from rfl, pow_one]
    obtain ⟨u, hu⟩ : ∃ u, u = 1 - 9 * w := ⟨_, rfl⟩
    have hwu : w = (1 - u) / 9 := by rw [hu]; ring
    have hu0 : u ≠ 0 := by rw [hu]; exact hq
    subst hwu
    rw [show (1 : ℂ) - 9 * ((1 - u) / 9) = u by ring]
    field_simp
    ring
  have hG : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 100), (fun v => P v * H (φ v)) w =
      ₂F₁ (3 * a) (3 * a + 1 / 2) (2 * a + 5 / 6) w := by
    refine eq_ordinaryHypergeometric_of_gaussOperator hc (by norm_num) (by norm_num) ?_ ?_ ?_
    · intro w hw
      have hw1 := hsmall w hw
      exact (hPa w (hballD w hw1)).mul ((analyticAt_ordinaryHypergeometric (hφn w hw1)).comp
        (f := φ) (hφa w (hballD w hw1)))
    · intro w hw
      have hw1 := hsmall w hw
      have hwD := hballD w hw1
      have hHa : AnalyticAt ℂ H (φ w) := analyticAt_ordinaryHypergeometric (hφn w hw1)
      rw [gaussOperator_mul_comp (hPa w hwD) (hφa w hwD) hHa,
        show deriv P w = _ from deriv_affine_cpow (hslit w hwD),
        show deriv (deriv P) w = _ from deriv_deriv_affine_cpow (hslit w hwD),
        (hφd w hwD).deriv, hφdd w hwD]
      have hode := gaussOperator_ordinaryHypergeometric (a := a) (b := a + 1 / 2) hc (hφn w hw1)
      simp only [gaussOperator] at hode
      have hq := hq0 w hwD
      linear_combination (norm := skip)
        (-27 * P w * (1 - w) * (1 + 3 * w) / (1 - 9 * w) ^ 2) * hode
      simp only [hP, hφdef, hH]
      generalize ₂F₁ a (a + 1 / 2) (2 * a + 5 / 6) (-27 * w * (1 - w) ^ 2 / (1 - 9 * w) ^ 2) = h0
      generalize deriv (₂F₁ a (a + 1 / 2) (2 * a + 5 / 6))
        (-27 * w * (1 - w) ^ 2 / (1 - 9 * w) ^ 2) = h1
      generalize iteratedDeriv 2 (₂F₁ a (a + 1 / 2) (2 * a + 5 / 6))
        (-27 * w * (1 - w) ^ 2 / (1 - 9 * w) ^ 2) = h2
      rw [show (1 : ℂ) + -9 * w = 1 - 9 * w by ring]
      generalize (1 - 9 * w) ^ (-2 * a) = pw
      obtain ⟨u, hu⟩ : ∃ u, u = 1 - 9 * w := ⟨_, rfl⟩
      have hwu : w = (1 - u) / 9 := by rw [hu]; ring
      have hu0 : u ≠ 0 := by rw [hu]; exact hq
      rw [← hu]
      subst hwu
      field_simp
      ring
    · simp [hP, hφdef, hH, ordinaryHypergeometric_zero]
  -- extension to `D` through the cut-plane continuation
  set c₂ := 2 * a + 5 / 6 with hc₂
  set R : ℂ → ℂ := fun w => P w * (Gamma c₂ * regularizedGaussHG a (a + 1 / 2) c₂ (φ w)) with hR
  have hDc : IsPreconnected D := by
    have hconv : Convex ℝ D := by
      have : D = {w : ℂ | 30 * w.im - 3 * w.re < 1} ∩ {w : ℂ | -30 * w.im - 3 * w.re < 1} ∩
          ({w : ℂ | 30 * w.im + 9 * w.re < 1} ∩ {w : ℂ | -30 * w.im + 9 * w.re < 1}) := by
        ext w
        simp only [hD, Set.mem_ofPred_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨h1, h2⟩
          rcases abs_lt.mp (show |w.im| < 1 / 30 + 0 by linarith [abs_nonneg w.im]) with _
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
            cases abs_cases w.im <;> linarith
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩
          refine ⟨?_, ?_⟩ <;> cases abs_cases w.im <;> linarith
      rw [this]
      refine ((convex_halfSpace_lt ?_ _).inter (convex_halfSpace_lt ?_ _)).inter
        ((convex_halfSpace_lt ?_ _).inter (convex_halfSpace_lt ?_ _)) <;>
        exact ⟨fun x y => by simp; ring, fun r x => by simp; ring⟩
    exact hconv.isPreconnected
  have hRe : ∀ w : ℂ, ‖φ w‖ < 1 → R w = P w * H (φ w) := by
    intro w hw
    simp only [hR, hH]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw, regularizedGaussHGFun_eq_div_Gamma hc,
      mul_div_cancel₀ _ (Gamma_ne_zero hc)]
  have hLan : AnalyticOnNhd ℂ (₂F₁ (3 * a) (3 * a + 1 / 2) (2 * a + 5 / 6) : ℂ → ℂ) D :=
    fun w hw => analyticAt_ordinaryHypergeometric (hnorm w hw)
  have hcut : ∀ w ∈ D, φ w ∈ cutPlane := by
    intro w hw
    rw [mem_cutPlane]
    exact mem_slitPlane_iff.mpr (Or.inl (hypSV_psi_one_sub_re_pos hw.1 hw.2))
  have hRan : AnalyticOnNhd ℂ R D := fun w hw =>
    (hPa w hw).mul (analyticAt_const.mul ((analyticAt_regularizedGaussHG _ _ _
      (hcut w hw)).comp (f := φ) (hφa w hw)))
  have h0D : (0 : ℂ) ∈ D := by simp [hD]
  have hev : (₂F₁ (3 * a) (3 * a + 1 / 2) (2 * a + 5 / 6) : ℂ → ℂ) =ᶠ[𝓝 0] R := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 100)] with w hw
    rw [hRe w (hφn w (hsmall w hw))]
    exact (hG w hw).symm
  have hEq := hLan.eqOn_of_preconnected_of_eventuallyEq hRan hDc h0D hev ⟨h₁, h₂⟩
  rw [hEq, hRe z hw]
  simp only [hP, hφdef, hH]
  rw [show (1 : ℂ) - 9 * z = 1 + -9 * z by ring]

/-- On the cone domain of the cubic map `s(u) = 27u/(4u-1)³`, `1 - s u` has positive real part. -/
theorem hypSV_cubicTwo_one_sub_re_pos {w : ℂ} (h₁ : 80 * |w.im| < 1 + 8 * w.re)
    (h₂ : 80 * |w.im| < 1 - 16 * w.re) :
    0 < (1 - 27 * w / (4 * w - 1) ^ 3).re := by
  have hq0 : 4 * w - 1 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith [abs_nonneg w.im]
  have hid : 1 - 27 * w / (4 * w - 1) ^ 3 =
      ((1 + 8 * w) * (1 + 8 * w)) * (1 - w) *
        (((1 - 4 * w)⁻¹ * (1 - 4 * w)⁻¹) * (1 - 4 * w)⁻¹) := by
    obtain ⟨u, hu⟩ : ∃ u, u = 4 * w - 1 := ⟨_, rfl⟩
    have hwu : w = (u + 1) / 4 := by rw [hu]; ring
    have hu0 : u ≠ 0 := by rw [hu]; exact hq0
    subst hwu
    rw [show (4 : ℂ) * ((u + 1) / 4) - 1 = u by ring,
      show (1 : ℂ) - 4 * ((u + 1) / 4) = -u by ring]
    have hu' : -u ≠ 0 := neg_ne_zero.mpr hu0
    field_simp
    ring
  rw [hid]
  have hab := abs_nonneg w.im
  have hpre : 0 < (1 + 8 * w).re := by simp; linarith
  have hpim : |(1 + 8 * w).im| ≤ 1 / 10 * (1 + 8 * w).re := by
    simp [abs_mul]; linarith
  have hrre : 0 < (1 - w).re := by simp; linarith
  have hrim : |(1 - w).im| ≤ 1 / 50 * (1 - w).re := by
    simp; linarith
  have hqre : 0 < (1 - 4 * w).re := by simp; linarith
  have hqim : |(1 - 4 * w).im| ≤ 1 / 10 * (1 - 4 * w).re := by
    simp [abs_mul]; linarith
  obtain ⟨hq1, hq2⟩ := hypSV_tan_recip hqre hqim
  obtain ⟨hp2r, hp2i⟩ := hypSV_tan_mul (T := 21 / 100) hpre hpre hpim hpim (by norm_num) (by norm_num)
  obtain ⟨hprr, hpri⟩ := hypSV_tan_mul (T := 6 / 25) hp2r hrre hp2i hrim (by norm_num) (by norm_num)
  obtain ⟨hq2r, hq2i⟩ := hypSV_tan_mul (T := 21 / 100) hq1 hq1 hq2 hq2 (by norm_num) (by norm_num)
  obtain ⟨hq3r, hq3i⟩ := hypSV_tan_mul (T := 8 / 25) hq2r hq1 hq2i hq2 (by norm_num) (by norm_num)
  exact (hypSV_tan_mul (T := 1) hprr hq3r hpri hq3i (by norm_num) (by norm_num)).1

/-- A cubic transformation (Goursat; Erdélyi, Higher Transcendental Functions, 2.11(39)):
`F(3a, 1/3-a; 2a+5/6; u) = (1-4u)^{-3a} F(a, a+1/3; 2a+5/6; 27u/(4u-1)³)` on the cone domain
around `(-1/8, 1/16)` (where the image stays in the unit disk). -/
theorem hypSV_cubic_two {a z : ℂ} (hc : ∀ k : ℕ, 2 * a + 5 / 6 ≠ -(k : ℂ))
    (h₁ : 80 * |z.im| < 1 + 8 * z.re) (h₂ : 80 * |z.im| < 1 - 16 * z.re)
    (hw : ‖27 * z / (4 * z - 1) ^ 3‖ < 1) :
    ₂F₁ (3 * a) (1 / 3 - a) (2 * a + 5 / 6) z =
      (1 - 4 * z) ^ (-3 * a) * ₂F₁ a (a + 1 / 3) (2 * a + 5 / 6) (27 * z / (4 * z - 1) ^ 3) := by
  set H : ℂ → ℂ := ₂F₁ a (a + 1 / 3) (2 * a + 5 / 6) with hH
  set P : ℂ → ℂ := fun w => (1 + (-4) * w) ^ (-3 * a) with hP
  set φ : ℂ → ℂ := fun w => 27 * w / (4 * w - 1) ^ 3 with hφdef
  set D : Set ℂ := {w | 80 * |w.im| < 1 + 8 * w.re ∧ 80 * |w.im| < 1 - 16 * w.re} with hD
  have hsmall : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 100), ‖w‖ < 1 / 100 := fun w hw => by simpa using hw
  have hballD : ∀ w : ℂ, ‖w‖ < 1 / 100 → w ∈ D := by
    intro w hw
    have h1 := abs_re_le_norm w
    have h2 := abs_im_le_norm w
    rw [abs_le] at h1
    exact ⟨by linarith, by linarith⟩
  have hq0 : ∀ w ∈ D, 4 * w - 1 ≠ 0 := by
    intro w hw h; have := congrArg re h; simp at this; linarith [abs_nonneg w.im, hw.2]
  have hslit : ∀ w ∈ D, 1 + (-4) * w ∈ slitPlane := by
    intro w hw
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    simp; linarith [abs_nonneg w.im, hw.2]
  have hnorm : ∀ w ∈ D, ‖w‖ < 1 := by
    intro w hw
    have := norm_le_abs_re_add_abs_im w
    have hr : |w.re| < 1 / 8 := by
      rw [abs_lt]; constructor <;> linarith [abs_nonneg w.im, hw.1, hw.2]
    have hi : |w.im| < 1 / 80 := by linarith [hw.1, hw.2]
    linarith
  have hφn : ∀ w : ℂ, ‖w‖ < 1 / 100 → ‖φ w‖ < 1 := by
    intro w hw
    have h1 : 96 / 100 ≤ ‖4 * w - 1‖ := by
      have := norm_sub_norm_le (1 : ℂ) (4 * w)
      rw [norm_one, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num] at this
      rw [norm_sub_rev]
      linarith
    simp only [hφdef, norm_div, norm_mul, norm_pow, show ‖(27 : ℂ)‖ = 27 by norm_num]
    rw [div_lt_one (by positivity)]
    have hw0 := norm_nonneg w
    calc 27 * ‖w‖ ≤ 27 * (1 / 100) := by gcongr
      _ < (96 / 100) ^ 3 := by norm_num
      _ ≤ ‖4 * w - 1‖ ^ 3 := by gcongr
  have hPa : ∀ w ∈ D, AnalyticAt ℂ P w := fun w hw =>
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const (hslit w hw)
  have hφa : ∀ w ∈ D, AnalyticAt ℂ φ w := fun w hw =>
    ((analyticAt_const.mul analyticAt_id).div
      (((analyticAt_const.mul analyticAt_id).sub analyticAt_const).pow 3)) (pow_ne_zero 3 (hq0 w hw))
  have hDopen : IsOpen D := by
    rw [hD, Set.ofPred_and]
    exact (isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop))
  have hφd : ∀ w ∈ D, HasDerivAt φ (-27 * (8 * w + 1) / (4 * w - 1) ^ 4) w := by
    intro w hw
    have h := ((hasDerivAt_id w).const_mul (27 : ℂ)).div
      ((((hasDerivAt_id w).const_mul (4 : ℂ)).sub_const (1 : ℂ)).pow 3) (pow_ne_zero 3 (hq0 w hw))
    refine h.congr_deriv ?_
    have hq := hq0 w hw
    simp only [id, Pi.pow_apply, Nat.cast_ofNat,
      show (3 : ℕ) - 1 = 2 from rfl]
    obtain ⟨u, hu⟩ : ∃ u, u = 4 * w - 1 := ⟨_, rfl⟩
    have hwu : w = (u + 1) / 4 := by rw [hu]; ring
    have hu0 : u ≠ 0 := by rw [hu]; exact hq
    subst hwu
    rw [show (4 : ℂ) * ((u + 1) / 4) - 1 = u by ring]
    field_simp
    ring
  have hφdd : ∀ w ∈ D, deriv (deriv φ) w = 648 * (4 * w + 1) / (4 * w - 1) ^ 5 := by
    intro w hw
    have hev : deriv φ =ᶠ[𝓝 w] fun v => -27 * (8 * v + 1) / (4 * v - 1) ^ 4 := by
      filter_upwards [hDopen.mem_nhds hw] with v hv
      exact (hφd v hv).deriv
    rw [hev.deriv_eq]
    have h := ((((hasDerivAt_id w).const_mul (8 : ℂ)).add_const (1 : ℂ)).const_mul (-27 : ℂ)).div
      ((((hasDerivAt_id w).const_mul (4 : ℂ)).sub_const (1 : ℂ)).pow 4) (pow_ne_zero 4 (hq0 w hw))
    have h' : HasDerivAt (fun v => -27 * (8 * v + 1) / (4 * v - 1) ^ 4) _ w := h
    rw [h'.deriv]
    have hq := hq0 w hw
    simp only [id, Pi.pow_apply, Nat.cast_ofNat,
      show (4 : ℕ) - 1 = 3 from rfl]
    obtain ⟨u, hu⟩ : ∃ u, u = 4 * w - 1 := ⟨_, rfl⟩
    have hwu : w = (u + 1) / 4 := by rw [hu]; ring
    have hu0 : u ≠ 0 := by rw [hu]; exact hq
    subst hwu
    rw [show (4 : ℂ) * ((u + 1) / 4) - 1 = u by ring]
    field_simp
    ring
  have hG : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 100), (fun v => P v * H (φ v)) w =
      ₂F₁ (3 * a) (1 / 3 - a) (2 * a + 5 / 6) w := by
    refine eq_ordinaryHypergeometric_of_gaussOperator hc (by norm_num) (by norm_num) ?_ ?_ ?_
    · intro w hw
      have hw1 := hsmall w hw
      exact (hPa w (hballD w hw1)).mul ((analyticAt_ordinaryHypergeometric (hφn w hw1)).comp
        (f := φ) (hφa w (hballD w hw1)))
    · intro w hw
      have hw1 := hsmall w hw
      have hwD := hballD w hw1
      have hHa : AnalyticAt ℂ H (φ w) := analyticAt_ordinaryHypergeometric (hφn w hw1)
      rw [gaussOperator_mul_comp (hPa w hwD) (hφa w hwD) hHa,
        show deriv P w = _ from deriv_affine_cpow (hslit w hwD),
        show deriv (deriv P) w = _ from deriv_deriv_affine_cpow (hslit w hwD),
        (hφd w hwD).deriv, hφdd w hwD]
      have hode := gaussOperator_ordinaryHypergeometric (a := a) (b := a + 1 / 3) hc (hφn w hw1)
      simp only [gaussOperator] at hode
      have hq := hq0 w hwD
      linear_combination (norm := skip) (-27 * P w / (4 * w - 1) ^ 2) * hode
      simp only [hP, hφdef, hH]
      generalize ₂F₁ a (a + 1 / 3) (2 * a + 5 / 6) (27 * w / (4 * w - 1) ^ 3) = h0
      generalize deriv (₂F₁ a (a + 1 / 3) (2 * a + 5 / 6)) (27 * w / (4 * w - 1) ^ 3) = h1
      generalize iteratedDeriv 2 (₂F₁ a (a + 1 / 3) (2 * a + 5 / 6)) (27 * w / (4 * w - 1) ^ 3) = h2
      generalize (1 + -4 * w) ^ (-3 * a) = pw
      obtain ⟨u, hu⟩ : ∃ u, u = 4 * w - 1 := ⟨_, rfl⟩
      have hwu : w = (u + 1) / 4 := by rw [hu]; ring
      have hu0 : u ≠ 0 := by rw [hu]; exact hq
      subst hwu
      rw [show (4 : ℂ) * ((u + 1) / 4) - 1 = u by ring,
        show (1 : ℂ) + -4 * ((u + 1) / 4) = -u by ring]
      have hu' : -u ≠ 0 := neg_ne_zero.mpr hu0
      field_simp
      ring
    · simp [hP, hφdef, hH, ordinaryHypergeometric_zero]
  set c₂ := 2 * a + 5 / 6 with hc₂
  set R : ℂ → ℂ := fun w => P w * (Gamma c₂ * regularizedGaussHG a (a + 1 / 3) c₂ (φ w)) with hR
  have hDc : IsPreconnected D := by
    have hconv : Convex ℝ D := by
      have : D = {w : ℂ | 80 * w.im - 8 * w.re < 1} ∩ {w : ℂ | -80 * w.im - 8 * w.re < 1} ∩
          ({w : ℂ | 80 * w.im + 16 * w.re < 1} ∩ {w : ℂ | -80 * w.im + 16 * w.re < 1}) := by
        ext w
        simp only [hD, Set.mem_ofPred_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> cases abs_cases w.im <;> linarith
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩
          refine ⟨?_, ?_⟩ <;> cases abs_cases w.im <;> linarith
      rw [this]
      refine ((convex_halfSpace_lt ?_ _).inter (convex_halfSpace_lt ?_ _)).inter
        ((convex_halfSpace_lt ?_ _).inter (convex_halfSpace_lt ?_ _)) <;>
        exact ⟨fun x y => by simp; ring, fun r x => by simp; ring⟩
    exact hconv.isPreconnected
  have hRe : ∀ w : ℂ, ‖φ w‖ < 1 → R w = P w * H (φ w) := by
    intro w hw
    simp only [hR, hH]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw, regularizedGaussHGFun_eq_div_Gamma hc,
      mul_div_cancel₀ _ (Gamma_ne_zero hc)]
  have hLan : AnalyticOnNhd ℂ (₂F₁ (3 * a) (1 / 3 - a) (2 * a + 5 / 6) : ℂ → ℂ) D :=
    fun w hw => analyticAt_ordinaryHypergeometric (hnorm w hw)
  have hcut : ∀ w ∈ D, φ w ∈ cutPlane := by
    intro w hw
    rw [mem_cutPlane]
    exact mem_slitPlane_iff.mpr (Or.inl (hypSV_cubicTwo_one_sub_re_pos hw.1 hw.2))
  have hRan : AnalyticOnNhd ℂ R D := fun w hw =>
    (hPa w hw).mul (analyticAt_const.mul ((analyticAt_regularizedGaussHG _ _ _
      (hcut w hw)).comp (f := φ) (hφa w hw)))
  have h0D : (0 : ℂ) ∈ D := by simp [hD]
  have hev : (₂F₁ (3 * a) (1 / 3 - a) (2 * a + 5 / 6) : ℂ → ℂ) =ᶠ[𝓝 0] R := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 100)] with w hw
    rw [hRe w (hφn w (hsmall w hw))]
    exact (hG w hw).symm
  have hEq := hLan.eqOn_of_preconnected_of_eventuallyEq hRan hDc h0D hev ⟨h₁, h₂⟩
  rw [hEq, hRe z hw]
  simp only [hP, hφdef, hH]
  rw [show (1 : ℂ) - 4 * z = 1 + -4 * z by ring]

/-- The value at `-1/3` of the `ψ`-cubic family, through `hypSV_cubic_psi` and Abel's theorem:
`F(3a, 3a+1/2; 2a+5/6; -1/3) = 4^{-2a} F(a, a+1/2; 2a+5/6; 1)` (the last series converges since
`Re(c - a - b) = 1/3`). -/
theorem hypSV_cubic_psi_neg_one_third {A : ℂ} (hcA : ∀ k : ℕ, 2 * A + 5 / 6 ≠ -(k : ℂ)) :
    ₂F₁ (3 * A) (3 * A + 1 / 2) (2 * A + 5 / 6) (-1 / 3) =
      (4 : ℂ) ^ (-2 * A) * ₂F₁ A (A + 1 / 2) (2 * A + 5 / 6) 1 := by
  have hre : 0 < (2 * A + 5 / 6 - A - (A + 1 / 2)).re := by
    rw [show 2 * A + 5 / 6 - A - (A + 1 / 2) = 1 / 3 by ring]; norm_num
  set G : ℂ → ℂ := ₂F₁ (3 * A) (3 * A + 1 / 2) (2 * A + 5 / 6) with hG
  -- the value `G(-1/3)` through the cubic transformation and Abel's theorem
  set ψr : ℝ → ℝ := fun x => -27 * x * (1 - x) ^ 2 / (1 - 9 * x) ^ 2 with hψr
  have hψc : ∀ x : ℝ, ((ψr x : ℝ) : ℂ) = -27 * (x : ℂ) * (1 - x) ^ 2 / (1 - 9 * x) ^ 2 := by
    intro x; simp only [hψr]; push_cast; ring
  have hψ1 : ∀ x : ℝ, -1 / 3 < x → x ≤ 0 → 0 ≤ ψr x ∧ ψr x < 1 := by
    intro x hx1 hx2
    have hq : 0 < (1 - 9 * x) ^ 2 := by nlinarith
    simp only [hψr]
    constructor
    · apply div_nonneg _ hq.le; nlinarith [sq_nonneg (1 - x)]
    · rw [div_lt_one hq]; nlinarith [sq_nonneg (1 + 3 * x), mul_pos (by linarith : (0:ℝ) < 1 + 3 * x)
        (mul_pos (by linarith : (0:ℝ) < 1 + 3 * x) (by linarith : (0:ℝ) < 1 + 3 * x))]
  have hmap : Tendsto ψr (𝓝[>] (-1 / 3)) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : ContinuousAt ψr (-1 / 3) := by
        simp only [hψr]
        exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
      have := hcont.tendsto
      rw [show ψr (-1 / 3) = 1 by simp only [hψr]; norm_num] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (-1 / 3 : ℝ) < 0 by norm_num)] with x hx
      exact (hψ1 x hx.1 hx.2.le).2
  have hR := (tendsto_ordinaryHypergeometric_left_one hre).comp hmap
  have hP : Tendsto (fun x : ℝ => (1 - 9 * (x : ℂ)) ^ (-2 * A)) (𝓝[>] (-1 / 3)) (𝓝 ((4 : ℂ) ^ (-2 * A))) := by
    have h4 : (1 : ℂ) - 9 * ((-1 / 3 : ℝ) : ℂ) = 4 := by push_cast; norm_num
    have hcont : ContinuousAt (fun x : ℝ => (1 - 9 * (x : ℂ)) ^ (-2 * A)) (-1 / 3) := by
      apply ContinuousAt.cpow (by fun_prop) continuousAt_const
      rw [h4]; exact mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    have := hcont.tendsto
    rw [h4] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hL : Tendsto (fun x : ℝ => G (x : ℂ)) (𝓝[>] (-1 / 3)) (𝓝 (G (-1 / 3))) := by
    have hc0 := (continuous_ofReal.tendsto (-1 / 3 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (-1 / 3 : ℝ)))
    rw [show ((-1 / 3 : ℝ) : ℂ) = -1 / 3 by push_cast; ring] at hc0
    exact (analyticAt_ordinaryHypergeometric (a := 3 * A) (b := 3 * A + 1 / 2) (c := 2 * A + 5 / 6)
      (show ‖(-1 / 3 : ℂ)‖ < 1 by norm_num)).continuousAt.tendsto.comp hc0
  have heq : ∀ᶠ x : ℝ in 𝓝[>] (-1 / 3), G (x : ℂ) =
      (1 - 9 * (x : ℂ)) ^ (-2 * A) * ₂F₁ A (A + 1 / 2) (2 * A + 5 / 6) ((ψr x : ℝ) : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (-1 / 3 : ℝ) < 0 by norm_num)] with x hx
    obtain ⟨h0, h1⟩ := hψ1 x hx.1 hx.2.le
    rw [hψc x]
    refine hypSV_cubic_psi hcA ?_ ?_ ?_
    · simp; linarith [hx.1]
    · simp; linarith [hx.2]
    · rw [← hψc x, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hlim := tendsto_nhds_unique hL ((hP.mul hR).congr' (by
    filter_upwards [heq] with x hx
    simp only [Function.comp_apply]
    rw [hx]))
  exact hlim

/-- `₂F₁` as the tsum of its Gauss coefficients, at every argument (the tsum is totalized). -/
theorem hypSV_ordinaryHypergeometric_eq_tsum (a b c z : ℂ) :
    ₂F₁ a b c z = ∑' n, gaussHGCoeff a b c n * z ^ n := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  congr 1
  funext n
  simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Abel's theorem for `₂F₁` along a radius to a point `ω` of the unit circle, when
`Re(c - a - b) > 0`. -/
theorem hypSV_tendsto_ray {a b c ω : ℂ} (hω : ‖ω‖ = 1) (h : 0 < (c - a - b).re) :
    Tendsto (fun r : ℝ => ₂F₁ a b c ((r : ℂ) * ω)) (𝓝[<] 1) (𝓝 (₂F₁ a b c ω)) := by
  have hs := ordinaryHypergeometric_summable_of_mem_sphere (a := a) (b := b) (c := c) hω h
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hs.hasSum.tendsto_sum_nat
  rw [← hypSV_ordinaryHypergeometric_eq_tsum] at habel
  refine habel.congr fun x => ?_
  rw [hypSV_ordinaryHypergeometric_eq_tsum]
  dsimp only
  congr 1
  funext n
  rw [mul_pow]; ring

/-- `(p³/q²)^{1/3} = p q^{-2/3}` for positive reals. -/
theorem hypSV_rpow_third {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (p ^ 3 / q ^ 2) ^ (1 / 3 : ℝ) = p * q ^ (-(2 / 3) : ℝ) := by
  rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hp.le, ← Real.rpow_mul hq.le, Real.rpow_neg hq.le]
  norm_num
  rw [div_eq_mul_inv]

/-- Near `z = -1/3` the `ψ`-cubic family is given by the connection formula at `ψ = 1`. -/
theorem hypSV_cubic_psi_eventually {A : ℂ} (hcA : ∀ k : ℕ, 2 * A + 5 / 6 ≠ -(k : ℂ)) :
    ₂F₁ (3 * A) (3 * A + 1 / 2) (2 * A + 5 / 6) =ᶠ[𝓝 (-1 / 3)] fun z =>
      Gamma (2 * A + 5 / 6) * (Real.pi / sin (Real.pi * (1 / 3))) *
        ((1 + (-9) * z) ^ (-2 * A) *
          ₂F₁ A (A + 1 / 2) (2 / 3) ((1 + 3 * z) ^ 3 / (1 - 9 * z) ^ 2) *
            (Gamma (2 / 3) * (Gamma (A + 5 / 6) * Gamma (A + 1 / 3)))⁻¹ -
        (1 + (-9) * z) ^ (-2 * A) * ((1 + 3 * z) * (1 + (-9) * z) ^ (-(2 / 3) : ℂ)) *
          ₂F₁ (A + 5 / 6) (A + 1 / 3) (4 / 3) ((1 + 3 * z) ^ 3 / (1 - 9 * z) ^ 2) *
            (Gamma (4 / 3) * (Gamma A * Gamma (A + 1 / 2)))⁻¹) := by
  set c := 2 * A + 5 / 6 with hc
  set u : ℂ → ℂ := fun z => (1 + 3 * z) ^ 3 / (1 - 9 * z) ^ 2 with hu
  set Φ : ℂ → ℂ := fun z => Gamma c * (Real.pi / sin (Real.pi * (1 / 3))) *
        ((1 + (-9) * z) ^ (-2 * A) * ₂F₁ A (A + 1 / 2) (2 / 3) (u z) *
            (Gamma (2 / 3) * (Gamma (A + 5 / 6) * Gamma (A + 1 / 3)))⁻¹ -
        (1 + (-9) * z) ^ (-2 * A) * ((1 + 3 * z) * (1 + (-9) * z) ^ (-(2 / 3) : ℂ)) *
          ₂F₁ (A + 5 / 6) (A + 1 / 3) (4 / 3) (u z) *
            (Gamma (4 / 3) * (Gamma A * Gamma (A + 1 / 2)))⁻¹) with hΦ
  have hs : sin (Real.pi * (1 / 3) : ℂ) ≠ 0 := by
    rw [show (Real.pi : ℂ) * (1 / 3) = ((Real.pi / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
      Real.sin_pi_div_three]
    exact ofReal_ne_zero.mpr (by positivity)
  have hu0 : u (-1 / 3) = 0 := by simp only [hu]; norm_num
  have h9 : (1 : ℂ) + (-9) * (-1 / 3) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  -- analyticity at `-1/3`
  have hua : AnalyticAt ℂ u (-1 / 3) := by
    simp only [hu]
    exact ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).pow 3).div
      ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).pow 2) (by norm_num)
  have hF1 : AnalyticAt ℂ (fun z => ₂F₁ A (A + 1 / 2) (2 / 3) (u z)) (-1 / 3) :=
    (analyticAt_ordinaryHypergeometric (by rw [hu0]; simp)).comp hua
  have hF2 : AnalyticAt ℂ (fun z => ₂F₁ (A + 5 / 6) (A + 1 / 3) (4 / 3) (u z)) (-1 / 3) :=
    (analyticAt_ordinaryHypergeometric (by rw [hu0]; simp)).comp hua
  have hP : ∀ s : ℂ, AnalyticAt ℂ (fun z : ℂ => (1 + (-9) * z) ^ s) (-1 / 3) := fun s =>
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const h9
  have hΦa : AnalyticAt ℂ Φ (-1 / 3) := by
    simp only [hΦ]
    exact analyticAt_const.mul ((((hP _).mul hF1).mul analyticAt_const).sub
      ((((hP _).mul ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).mul (hP _))).mul
        hF2).mul analyticAt_const))
  have hGa : AnalyticAt ℂ (₂F₁ (3 * A) (3 * A + 1 / 2) c : ℂ → ℂ) (-1 / 3 : ℂ) :=
    analyticAt_ordinaryHypergeometric (by norm_num)
  -- equality on a real interval to the right of `-1/3`
  have hreal : ∀ x : ℝ, -1 / 3 < x → x < -1 / 6 →
      ₂F₁ (3 * A) (3 * A + 1 / 2) c (x : ℂ) = Φ x := by
    intro x hx1 hx2
    have hp : 0 < 1 + 3 * x := by linarith
    have hq : 0 < 1 - 9 * x := by linarith
    set ψ : ℂ := -27 * (x : ℂ) * (1 - x) ^ 2 / (1 - 9 * x) ^ 2 with hψ
    have hψr : ψ = ((-27 * x * (1 - x) ^ 2 / (1 - 9 * x) ^ 2 : ℝ) : ℂ) := by rw [hψ]; push_cast; ring
    have h1ψ : 1 - ψ = (((1 + 3 * x) ^ 3 / (1 - 9 * x) ^ 2 : ℝ) : ℂ) := by
      rw [hψr, ← ofReal_one, ← ofReal_sub]
      congr 1
      rw [eq_div_iff (by positivity), sub_mul, div_mul_cancel₀ _ (by positivity)]
      ring
    have hur : 0 < (1 + 3 * x) ^ 3 / (1 - 9 * x) ^ 2 := by positivity
    have hur1 : (1 + 3 * x) ^ 3 / (1 - 9 * x) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]
      have h3 : (1 + 3 * x) ^ 3 < 1 := by
        have : 1 + 3 * x < 1 := by linarith
        calc (1 + 3 * x) ^ 3 < 1 ^ 3 := by gcongr
          _ = 1 := by norm_num
      nlinarith
    have hψ1 : ‖ψ‖ < 1 := by
      rw [show ψ = 1 - (1 - ψ) by ring, h1ψ]
      rw [show (1 : ℂ) - (((1 + 3 * x) ^ 3 / (1 - 9 * x) ^ 2 : ℝ) : ℂ) =
        ((1 - (1 + 3 * x) ^ 3 / (1 - 9 * x) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have h1ψn : ‖1 - ψ‖ < 1 := by
      rw [h1ψ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hur]; exact hur1
    have hcub := hypSV_cubic_psi (a := A) (z := (x : ℂ)) hcA (by simp; linarith) (by simp; linarith)
      (by rw [← hψ]; exact hψ1)
    rw [← hψ] at hcub
    have hcon := regularized_connection_one_sub A (A + 1 / 2) c hψ1 h1ψn
    rw [show c - A - (A + 1 / 2) = 1 / 3 by rw [hc]; ring,
      show A + (A + 1 / 2) - c + 1 = 2 / 3 by rw [hc]; ring,
      show c - A = A + 5 / 6 by rw [hc]; ring, show c - (A + 1 / 2) = A + 1 / 3 by rw [hc]; ring,
      show (1 : ℂ) / 3 + 1 = 4 / 3 by norm_num,
      regularizedGaussHGFun_eq_div_Gamma hcA,
      regularizedGaussHGFun_eq_div_Gamma (c := 2 / 3) (fun k => by
        intro h; have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]),
      regularizedGaussHGFun_eq_div_Gamma (c := 4 / 3) (fun k => by
        intro h; have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])] at hcon
    have hthird : (1 - ψ) ^ (1 / 3 : ℂ) = (1 + 3 * (x : ℂ)) * (1 + (-9) * (x : ℂ)) ^ (-(2 / 3) : ℂ) := by
      rw [h1ψ, show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hur.le,
        hypSV_rpow_third hp hq, ofReal_mul, ofReal_cpow hq.le]
      push_cast; ring_nf
    have hu' : u x = 1 - ψ := by rw [h1ψ, hu]; push_cast; ring
    rw [hcub]
    simp only [hΦ]
    rw [hu', ← hthird, show (1 : ℂ) + (-9) * x = 1 - 9 * x by ring]
    have hG : Gamma c ≠ 0 := Gamma_ne_zero hcA
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hF : ₂F₁ A (A + 1 / 2) c ψ = Gamma c * (Real.pi / sin (Real.pi * (1 / 3))) *
        (₂F₁ A (A + 1 / 2) (2 / 3) (1 - ψ) / Gamma (2 / 3) / (Gamma (A + 5 / 6) * Gamma (A + 1 / 3)) -
          (1 - ψ) ^ (1 / 3 : ℂ) / (Gamma A * Gamma (A + 1 / 2)) *
            (₂F₁ (A + 5 / 6) (A + 1 / 3) (4 / 3) (1 - ψ) / Gamma (4 / 3))) := by
      have hs' : sin ((Real.pi : ℂ) / 3) ≠ 0 := by
        rw [show (Real.pi : ℂ) / 3 = Real.pi * (1 / 3) by ring]; exact hs
      rw [← hcon]
      field_simp
    rw [hF]
    ring
  have hT : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (-1 / 3 : ℝ)) (𝓝[≠] (-1 / 3 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := (continuous_ofReal.tendsto (-1 / 3 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (-1 / 3 : ℝ)))
      rwa [show ((-1 / 3 : ℝ) : ℂ) = -1 / 3 by push_cast; ring] at this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg re h
      simp at this
      exact absurd this (by simp at hx; linarith)
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (-1 / 3), ₂F₁ (3 * A) (3 * A + 1 / 2) c (x : ℂ) = Φ x := by
    filter_upwards [Ioo_mem_nhdsGT (show (-1 / 3 : ℝ) < -1 / 6 by norm_num)] with x hx
    exact hreal x hx.1 hx.2
  exact (hGa.frequently_eq_iff_eventually_eq hΦa).mp (hT.frequently hev.frequently)

/-- The derivative at `-1/3` of the `ψ`-cubic family, from the connection formula at `ψ = 1`. -/
theorem hypSV_cubic_psi_deriv_neg_one_third {A : ℂ} (hcA : ∀ k : ℕ, 2 * A + 5 / 6 ≠ -(k : ℂ)) :
    deriv (₂F₁ (3 * A) (3 * A + 1 / 2) (2 * A + 5 / 6)) (-1 / 3) =
      Gamma (2 * A + 5 / 6) * (Real.pi / sin (Real.pi * (1 / 3))) *
        (18 * A * (4 : ℂ) ^ (-2 * A) / 4 * (Gamma (2 / 3) * (Gamma (A + 5 / 6) * Gamma (A + 1 / 3)))⁻¹ -
          (4 : ℂ) ^ (-2 * A) * (3 * (4 : ℂ) ^ (-(2 / 3) : ℂ)) *
            (Gamma (4 / 3) * (Gamma A * Gamma (A + 1 / 2)))⁻¹) := by
  rw [(hypSV_cubic_psi_eventually hcA).deriv_eq]
  set u : ℂ → ℂ := fun z => (1 + 3 * z) ^ 3 / (1 - 9 * z) ^ 2 with hu
  have hu0 : u (-1 / 3) = 0 := by simp only [hu]; norm_num
  have hud : HasDerivAt u 0 (-1 / 3) := by
    have h := ((((hasDerivAt_id (-1 / 3 : ℂ)).const_mul (3 : ℂ)).const_add (1 : ℂ)).pow 3).div
      (((hasDerivAt_const (-1 / 3 : ℂ) (1 : ℂ)).sub ((hasDerivAt_id (-1 / 3 : ℂ)).const_mul
        (9 : ℂ))).pow 2) (by norm_num)
    have h' : HasDerivAt (fun z : ℂ => (1 + 3 * z) ^ 3 / (1 - 9 * z) ^ 2) _ (-1 / 3) := h
    convert h' using 1
    norm_num
  have hF : ∀ p q r : ℂ, HasDerivAt (fun z => ₂F₁ p q r (u z)) 0 (-1 / 3) := by
    intro p q r
    have ha : AnalyticAt ℂ (₂F₁ p q r : ℂ → ℂ) (u (-1 / 3)) :=
      analyticAt_ordinaryHypergeometric (by rw [hu0]; simp)
    have h2 := ha.differentiableAt.hasDerivAt.comp (-1 / 3 : ℂ) hud
    rw [mul_zero] at h2
    exact h2
  have h9 : (1 : ℂ) + (-9) * (-1 / 3) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  have hP : ∀ s : ℂ, HasDerivAt (fun z : ℂ => (1 + (-9) * z) ^ s)
      (s * (1 + (-9) * (-1 / 3 : ℂ)) ^ (s - 1) * (-9)) (-1 / 3) := by
    intro s
    have h := (((hasDerivAt_id (-1 / 3 : ℂ)).const_mul (-9 : ℂ)).const_add (1 : ℂ)).cpow_const
      (c := s) (by simpa using h9)
    simpa using h
  have hL : HasDerivAt (fun z : ℂ => 1 + 3 * z) 3 (-1 / 3) := by
    simpa using ((hasDerivAt_id (-1 / 3 : ℂ)).const_mul (3 : ℂ)).const_add (1 : ℂ)
  have hΦ := ((((hP (-2 * A)).mul (hF A (A + 1 / 2) (2 / 3))).mul_const
    (Gamma (2 / 3) * (Gamma (A + 5 / 6) * Gamma (A + 1 / 3)))⁻¹).sub
    ((((hP (-2 * A)).mul (hL.mul (hP (-(2 / 3) : ℂ)))).mul (hF (A + 5 / 6) (A + 1 / 3) (4 / 3))).mul_const
      (Gamma (4 / 3) * (Gamma A * Gamma (A + 1 / 2)))⁻¹)).const_mul
    (Gamma (2 * A + 5 / 6) * (Real.pi / sin (Real.pi * (1 / 3))))
  refine Eq.trans hΦ.deriv ?_
  simp only [hu0, ordinaryHypergeometric_zero, Pi.mul_apply]
  have h4 : (1 : ℂ) + (-9) * (-1 / 3) = 4 := by norm_num
  have h0 : (1 : ℂ) + 3 * (-1 / 3) = 0 := by norm_num
  rw [h4, h0, cpow_sub _ _ (by norm_num : (4 : ℂ) ≠ 0), cpow_one]
  ring

end DLMF.Hypergeometric
