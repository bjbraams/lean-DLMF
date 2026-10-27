/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.AdditionTools

/-!
# Tools for the addition theorems of the second kind

The Ferrers addition theorem of the second kind (DLMF 14.18.3) for every regular complex degree,
derived from the first-kind theorem 14.18.1 (`legAdd_fer_coeff_eq`) without a separate integer
case:

* for non-real `ν`, the connection formula 14.9.10 writes `𝖰_ν(x)` as a combination of `𝖯_ν(x)`
  and `𝖯_ν(-x)`; since `-(cos θ₁ cos θ₂ + sin θ₁ sin θ₂ cos φ)` is the addition-theorem argument
  at `(θ₁, π - θ₂)` and angle `φ + π` (`legQAdd_fY_reflect`), 14.18.1 at both angle pairs (the
  second needs `θ₁ < θ₂`) and 14.9.10 at order `m` give the Fourier coefficients
  (`legQAdd_coeff_eq_of_im`);
* the Fourier coefficients are continuous in the degree at every regular `ν`
  (`legQAdd_continuousAt_coeff`: dominated convergence, with a locally uniform bound from the
  joint holomorphy of the Gauss function), so the identity extends to all regular degrees, real
  ones included, by `eq_zero_of_im_ne_zero` (`legQAdd_coeff_eq`);
* the cosine expansion `legAdd_hasSum_cos` of the `C²` function `φ ↦ 𝖰_ν(…)` then gives 14.18.3
  (`legQAdd_ferrersQ_addition`).

The complex addition theorem 14.28.1 for `Re z₁, Re z₂ > 0`, `z₁, z₂ ∉ (0, 1]`:

* `legQAdd_one_add_mem_slitPlane`: the combined argument `z₁z₂ - s₁s₂ cos φ` never meets
  `(-∞, -1]`, for every `φ` and either choice of the square roots `sᵢ = (zᵢ²-1)^{1/2}`. With
  `zᵢ + 1 = bᵢ²`, `zᵢ - 1 = aᵢ²`, `aᵢbᵢ = sᵢ`, one has `1 + z₁z₂ - c s₁s₂ = (1+c)/4 X² + (1-c)/4 Y²`
  for `X, Y = b₁b₂ ∓ a₁a₂`, and `Re (X Ȳ) = |z₁+1||z₂+1| - |z₁-1||z₂-1| > 0`,
  `Re (XY) = 2 Re (z₁ + z₂) > 0` exclude a real nonpositive value;
* `legQAdd_coeff_differentiableOn`, `legQAdd_extend`: the Fourier coefficients in `φ` are
  holomorphic in each `zᵢ` on `D`, and the identity theorem on convex half-plane pieces of `D`
  carries 14.18.4 (`legAdd_hyp_coeff_eq`, at `zᵢ = cosh ξᵢ`) to all of `D × D`
  (`legQAdd_complex_coeff_eq`), with `P^m_ν = (ν-m+1)_{2m} P^{-m}_ν` for every degree
  (`legQAdd_associatedP_nat_eq`);
* `legQAdd_associatedP_complex_addition`: 14.28.1 for every angle.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory DLMF.Hypergeometric DLMF
open scoped Real Topology Nat ComplexConjugate

namespace DLMF.Legendre

/-- Shifting a `2π`-periodic function by `π` multiplies its `m`-th Fourier coefficient by `(-1)^m`. -/
theorem legQAdd_coeff_shift_pi {g : ℝ → ℂ} (hper : Function.Periodic g (2 * π)) (m : ℕ) :
    legAdd_coeff (fun t => g (t + π)) m = (-1) ^ m * legAdd_coeff g m := by
  simp only [legAdd_coeff]
  set h : ℝ → ℂ := fun s => exp (-(((m:ℤ):ℂ) * s * I)) * g s
  have hhper : Function.Periodic h (2 * π) := by
    intro s
    simp only [h, hper s]
    congr 1
    rw [show -(((m:ℤ):ℂ) * ((s + 2 * π : ℝ) : ℂ) * I) =
        -(((m:ℤ):ℂ) * s * I) + ((-(m:ℤ) : ℤ) : ℂ) * (2 * π * I) by push_cast; ring, exp_add,
      exp_int_mul_two_pi_mul_I, mul_one]
  have e1 : (∫ t in (-π)..π, exp (-(((m:ℤ):ℂ) * t * I)) * g (t + π)) =
      exp ((m:ℂ) * π * I) * ∫ s in (-π)..π, h s := by
    calc (∫ t in (-π)..π, exp (-(((m:ℤ):ℂ) * t * I)) * g (t + π))
        = ∫ t in (-π)..π, exp ((m:ℂ) * π * I) * h (t + π) := by
          refine intervalIntegral.integral_congr fun t _ => ?_
          simp only [h]
          rw [← mul_assoc, ← exp_add]
          congr 2
          push_cast; ring
      _ = ∫ x in (-π + π)..(π + π), exp ((m:ℂ) * π * I) * h x :=
          intervalIntegral.integral_comp_add_right (fun x => exp ((m:ℂ) * π * I) * h x) π
      _ = exp ((m:ℂ) * π * I) * ∫ s in (-π)..π, h s := by
          rw [intervalIntegral.integral_const_mul, show -π + π = 0 by ring,
            show π + π = 0 + 2 * π by ring, hhper.intervalIntegral_add_eq 0 (-π),
            show -π + 2 * π = π by ring]
  rw [e1, show exp ((m:ℂ) * π * I) = (-1) ^ m by
    rw [show (m:ℂ) * π * I = m * (π * I) by ring, exp_nat_mul, exp_pi_mul_I]]
  ring

/-- The addition-theorem argument stays below one when `θ₁ < θ₂ < π`. -/
theorem legQAdd_fY_lt_one {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h12 : θ₁ < θ₂) (h2 : θ₂ < π) (t : ℝ) :
    legAdd_fY θ₁ θ₂ t ≤ Real.cos (θ₂ - θ₁) ∧ Real.cos (θ₂ - θ₁) < 1 := by
  have hs1 : 0 ≤ Real.sin θ₁ := Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith)
  have hs2 : 0 ≤ Real.sin θ₂ := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h2.le
  have hc := Real.cos_le_one t
  refine ⟨?_, ?_⟩
  · rw [Real.cos_sub]; unfold legAdd_fY; nlinarith [mul_nonneg hs1 hs2]
  · rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) (by linarith)

/-- Reflection of the addition-theorem argument: replacing `θ₂` by `π - θ₂` and `t` by `t + π`. -/
theorem legQAdd_fY_reflect (θ₁ θ₂ t : ℝ) :
    legAdd_fY θ₁ (π - θ₂) (t + π) = -legAdd_fY θ₁ θ₂ t := by
  simp only [legAdd_fY, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_add_pi]; ring

/-- `𝖰_ν` of order zero in the even/odd basis. -/
theorem legQAdd_ferrersQ_zero_eq (ν : ℂ) (x : ℝ) :
    ferrersQ ν 0 x = π / 2 * (-sin (ν * π / 2) * Gamma ((ν + 1) / 2) * (Gamma ((ν + 2) / 2))⁻¹ *
      regularizedGaussHG (-ν / 2) ((ν + 1) / 2) (1 / 2) ((x:ℂ) ^ 2) +
      cos (ν * π / 2) * Gamma ((ν + 2) / 2) * (Gamma ((ν + 1) / 2))⁻¹ *
      ((x:ℂ) * regularizedGaussHG ((1 - ν) / 2) ((ν + 2) / 2) (3 / 2) ((x:ℂ) ^ 2))) := by
  rw [ferrersQ_even_odd]
  simp only [ferrersEven, ferrersOdd, add_zero, sub_zero, neg_zero, zero_div, cpow_zero, one_mul]

/-- Real `C²` regularity of `t ↦ 𝐅(a, b; c; y(t)²)` along a smooth path in `(-1, 1)`. -/
theorem legQAdd_contDiff_hg_sq (a b c : ℂ) {y : ℝ → ℝ} (hy : ContDiff ℝ 2 y)
    (hy1 : ∀ t, y t ^ 2 < 1) :
    ContDiff ℝ 2 (fun t => regularizedGaussHG a b c ((y t : ℂ) ^ 2)) := by
  have hG : DifferentiableOn ℂ (fun z => regularizedGaussHG a b c z) cutPlane :=
    DifferentiableOn.regularizedGaussHG (differentiableOn_const _) (differentiableOn_const _)
      (differentiableOn_const _) differentiableOn_id fun w hw => hw
  have hG2 : ContDiffOn ℝ 2 (fun z => regularizedGaussHG a b c z) cutPlane :=
    (hG.contDiffOn isOpen_cutPlane).restrict_scalars ℝ
  have hh : ContDiff ℝ 2 (fun t : ℝ => ((y t ^ 2 : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp (hy.pow 2)
  have := hG2.comp_contDiff hh fun t => legAdd_ofReal_mem_cutPlane (hy1 t)
  convert this using 1
  funext t
  simp only [Function.comp]
  push_cast; rfl

/-- `t ↦ 𝖰_ν(y(t))` is `C²` along a smooth path in `(-1, 1)`, for every degree. -/
theorem legQAdd_contDiff_ferrersQ (ν : ℂ) {y : ℝ → ℝ} (hy : ContDiff ℝ 2 y)
    (hy1 : ∀ t, y t ^ 2 < 1) : ContDiff ℝ 2 (fun t => ferrersQ ν 0 (y t)) := by
  simp only [legQAdd_ferrersQ_zero_eq]
  have hY : ContDiff ℝ 2 (fun t => (y t : ℂ)) := ofRealCLM.contDiff.comp hy
  exact contDiff_const.mul ((contDiff_const.mul (legQAdd_contDiff_hg_sq _ _ _ hy hy1)).add
    (contDiff_const.mul (hY.mul (legQAdd_contDiff_hg_sq _ _ _ hy hy1))))


/-- Quadratic Gauss functions are bounded on `closedBall ν₀ 1 × [a, b]`, `-1 < a`, `b < 1`. -/
theorem legQAdd_hg_sq_bound {A B : ℂ → ℂ} (hA : Continuous A) (hB : Continuous B) (c ν₀ : ℂ)
    {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    ∃ C, ∀ ν ∈ Metric.closedBall ν₀ 1, ∀ x ∈ Icc a b,
      ‖regularizedGaussHG (A ν) (B ν) c ((x:ℂ) ^ 2)‖ ≤ C := by
  have hK : IsCompact (Metric.closedBall ν₀ 1 ×ˢ Icc a b) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hc : ContinuousOn (fun p : ℂ × ℝ => regularizedGaussHG (A p.1) (B p.1) c ((p.2:ℂ) ^ 2))
      (Metric.closedBall ν₀ 1 ×ˢ Icc a b) :=
    differentiableOn_regularizedGaussHG_joint.continuousOn.comp
      (f := fun p : ℂ × ℝ => (A p.1, B p.1, c, ((p.2:ℂ) ^ 2)))
      (by fun_prop : Continuous _).continuousOn
      (fun p hp => ferrers_sq_mem_cutPlane ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨C, fun ν hν x hx => hC (ν, x) ⟨hν, hx⟩⟩

/-- A locally uniform bound for `𝖰_ν(x)` near a regular degree, `x ∈ [a, b] ⊂ (-1, 1)`. -/
theorem legQAdd_ferrersQ_bound {ν₀ : ℂ} (hr : LegendreQRegular ν₀ 0) {a b : ℝ} (ha : -1 < a)
    (hb : b < 1) : ∃ C, ∀ᶠ ν in 𝓝 ν₀, ∀ x ∈ Icc a b, ‖ferrersQ ν 0 x‖ ≤ C := by
  obtain ⟨c1, c2⟩ := continuousAt_Gamma_ferrersQ hr
  simp only [add_zero] at c1 c2
  set g1 : ℂ → ℂ := fun ν => -sin (ν * π / 2) * Gamma ((ν + 1) / 2) * (Gamma ((ν + 2) / 2))⁻¹
  set g2 : ℂ → ℂ := fun ν => cos (ν * π / 2) * Gamma ((ν + 2) / 2) * (Gamma ((ν + 1) / 2))⁻¹
  have hg1 : ContinuousAt g1 ν₀ :=
    (((by fun_prop : Continuous fun ν : ℂ => -sin (ν * π / 2)).continuousAt.mul c1).mul
      (continuous_recip_Gamma.comp (by fun_prop : Continuous fun ν : ℂ => (ν + 2) / 2)).continuousAt)
  have hg2 : ContinuousAt g2 ν₀ :=
    (((by fun_prop : Continuous fun ν : ℂ => cos (ν * π / 2)).continuousAt.mul c2).mul
      (continuous_recip_Gamma.comp (by fun_prop : Continuous fun ν : ℂ => (ν + 1) / 2)).continuousAt)
  obtain ⟨E, hE⟩ := legQAdd_hg_sq_bound (A := fun ν => -ν / 2) (B := fun ν => (ν + 1) / 2)
    (by fun_prop) (by fun_prop) (1 / 2) ν₀ ha hb
  obtain ⟨O, hO⟩ := legQAdd_hg_sq_bound (A := fun ν => (1 - ν) / 2) (B := fun ν => (ν + 2) / 2)
    (by fun_prop) (by fun_prop) (3 / 2) ν₀ ha hb
  have e1 : ∀ᶠ ν in 𝓝 ν₀, ‖g1 ν‖ < ‖g1 ν₀‖ + 1 :=
    hg1.norm.eventually (gt_mem_nhds (lt_add_one _))
  have e2 : ∀ᶠ ν in 𝓝 ν₀, ‖g2 ν‖ < ‖g2 ν₀‖ + 1 :=
    hg2.norm.eventually (gt_mem_nhds (lt_add_one _))
  have e3 : ∀ᶠ ν in 𝓝 ν₀, ν ∈ Metric.closedBall ν₀ 1 := Metric.closedBall_mem_nhds _ one_pos
  refine ⟨π / 2 * ((‖g1 ν₀‖ + 1) * E + (‖g2 ν₀‖ + 1) * O), ?_⟩
  filter_upwards [e1, e2, e3] with ν h1 h2 h3 x hx
  have hx1 : ‖(x:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx.1, hx.2]
  rw [legQAdd_ferrersQ_zero_eq]
  have hπ : ‖(π:ℂ) / 2‖ = π / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; simp
  calc ‖(π:ℂ) / 2 * (g1 ν * regularizedGaussHG (-ν / 2) ((ν + 1) / 2) (1 / 2) ((x:ℂ) ^ 2) +
        g2 ν * ((x:ℂ) * regularizedGaussHG ((1 - ν) / 2) ((ν + 2) / 2) (3 / 2) ((x:ℂ) ^ 2)))‖
      ≤ π / 2 * (‖g1 ν‖ * ‖regularizedGaussHG (-ν / 2) ((ν + 1) / 2) (1 / 2) ((x:ℂ) ^ 2)‖ +
        ‖g2 ν‖ * (‖(x:ℂ)‖ * ‖regularizedGaussHG ((1 - ν) / 2) ((ν + 2) / 2) (3 / 2) ((x:ℂ) ^ 2)‖)) := by
        rw [norm_mul, hπ]
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul (g1 ν), norm_mul (g2 ν), norm_mul (x:ℂ)]
    _ ≤ π / 2 * ((‖g1 ν₀‖ + 1) * E + (‖g2 ν₀‖ + 1) * O) := by
        have hO' := hO ν h3 x hx
        have hE' := hE ν h3 x hx
        gcongr
        calc ‖(x:ℂ)‖ * ‖regularizedGaussHG ((1 - ν) / 2) ((ν + 2) / 2) (3 / 2) ((x:ℂ) ^ 2)‖
            ≤ 1 * ‖regularizedGaussHG ((1 - ν) / 2) ((ν + 2) / 2) (3 / 2) ((x:ℂ) ^ 2)‖ := by gcongr
          _ ≤ O := by rw [one_mul]; exact hO'

/-- The Fourier coefficients of `t ↦ 𝖰_ν(y(t))` are continuous in the degree at a regular `ν₀`. -/
theorem legQAdd_continuousAt_coeff {ν₀ : ℂ} (hr : LegendreQRegular ν₀ 0) {y : ℝ → ℝ}
    (hy : ContDiff ℝ 2 y) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : ∀ t, y t ∈ Icc a b)
    (m : ℤ) : ContinuousAt (fun ν => legAdd_coeff (fun t => ferrersQ ν 0 (y t)) m) ν₀ := by
  have hy1 : ∀ t, y t ^ 2 < 1 := fun t => by
    have := hab t; nlinarith [this.1, this.2]
  obtain ⟨C, hC⟩ := legQAdd_ferrersQ_bound hr ha hb
  unfold legAdd_coeff
  refine continuousAt_const.mul ?_
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun ν =>
      ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
        (legQAdd_contDiff_ferrersQ ν hy hy1).continuous).aestronglyMeasurable
  · filter_upwards [hC] with ν hν
    refine ae_of_all _ fun t _ => ?_
    rw [norm_mul, show -((m:ℂ) * t * I) = ((-(m * t) : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, one_mul]
    exact hν _ (hab t)
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun t _ => continuousAt_const.mul (continuousAt_ferrersQ_degree hr ?_)
    exact ⟨by linarith [(hab t).1], by linarith [(hab t).2]⟩


/-- The argument of the addition theorem lies in `[cos (θ₁ + θ₂), cos (θ₂ - θ₁)] ⊂ (-1, 1)`. -/
theorem legQAdd_fY_mem {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h12 : θ₁ < θ₂) (hs : θ₁ + θ₂ < π) (t : ℝ) :
    legAdd_fY θ₁ θ₂ t ∈ Icc (Real.cos (θ₁ + θ₂)) (Real.cos (θ₂ - θ₁)) :=
  ⟨(legAdd_fY_mem h1 (by linarith) hs t).1, (legQAdd_fY_lt_one h1 h12 (by linarith) t).1⟩

/-- The Fourier coefficients of `φ ↦ 𝖰_ν(cos θ₁ cos θ₂ + sin θ₁ sin θ₂ cos φ)` for non-real `ν`,
from 14.18.1 at `(θ₁, θ₂)` and `(θ₁, π - θ₂)` and the connection formula 14.9.10. -/
theorem legQAdd_coeff_eq_of_im {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h12 : θ₁ < θ₂) (hs : θ₁ + θ₂ < π)
    (m : ℕ) {ν : ℂ} (hν : ν.im ≠ 0) :
    legAdd_coeff (fun t => ferrersQ ν 0 (legAdd_fY θ₁ θ₂ t)) m =
      (-1:ℂ) ^ m * ferrersP ν (-(m:ℂ)) (Real.cos θ₁) * ferrersQ ν m (Real.cos θ₂) := by
  have h2 : θ₂ < π := by linarith
  have h2' : 0 ≤ θ₂ := by linarith
  have hreg : ∀ μ : ℂ, μ.im = 0 → LegendreQRegular ν μ := fun μ hμ =>
    legendreQRegular_of_im_ne_zero (by simp [hμ, hν])
  have hsin : sin (ν * π) ≠ 0 := sin_mul_pi_ne_zero_of_im_ne_zero hν
  have hsin' : sin (π * ν) ≠ 0 := by rwa [mul_comm]
  have hY : ∀ t, legAdd_fY θ₁ θ₂ t ∈ Ioo (-1:ℝ) 1 := fun t =>
    ⟨lt_of_lt_of_le (legAdd_neg_one_lt_cos (by linarith) hs) (legQAdd_fY_mem h1 h12 hs t).1,
      lt_of_le_of_lt (legQAdd_fY_mem h1 h12 hs t).2 (legQAdd_fY_lt_one h1 h12 h2 t).2⟩
  have hQ : ∀ x ∈ Ioo (-1:ℝ) 1, ferrersQ ν 0 x =
      π / (2 * sin (ν * π)) * (cos (ν * π) * ferrersP ν 0 x - ferrersP ν 0 (-x)) := by
    intro x hx
    have := ferrers_connection_10 ν 0 (hreg 0 rfl) (hreg _ (by simp)) hx
    simp only [neg_zero, sub_zero] at this
    have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hk : π / (2 * sin (ν * π)) * (2 / π * sin (ν * π)) = 1 := by field_simp
    calc ferrersQ ν 0 x = (π / (2 * sin (ν * π)) * (2 / π * sin (ν * π))) * ferrersQ ν 0 x := by
          rw [hk, one_mul]
      _ = _ := by rw [mul_assoc, this]
  have hs' : θ₁ + (π - θ₂) < π := by linarith
  set F : ℝ → ℂ := fun t => ferrersP ν 0 (legAdd_fY θ₁ (π - θ₂) t) with hFdef
  have hfun : (fun t => ferrersQ ν 0 (legAdd_fY θ₁ θ₂ t)) = fun t =>
      (π / (2 * sin (ν * π)) * cos (ν * π)) * ferrersP ν 0 (legAdd_fY θ₁ θ₂ t) +
        (-(π / (2 * sin (ν * π)))) * F (t + π) := by
    funext t; simp only [F]; rw [legQAdd_fY_reflect, hQ _ (hY t)]; ring
  have hcP : Continuous (fun t => ferrersP ν 0 (legAdd_fY θ₁ θ₂ t)) :=
    (legAdd_fY_contDiff ν h1 h2' hs).continuous
  have hcF : Continuous F := (legAdd_fY_contDiff ν h1 (by linarith) hs').continuous
  have hFper : Function.Periodic F (2 * π) := fun t => by
    simp only [F, legAdd_fY, Real.cos_add_two_pi]
  have hcF' : Continuous fun t : ℝ => -(π / (2 * sin (ν * π))) * F (t + π) := by fun_prop
  have hcP' : Continuous fun t : ℝ => π / (2 * sin (ν * π)) * cos (ν * π) *
      ferrersP ν 0 (legAdd_fY θ₁ θ₂ t) := by fun_prop
  rw [hfun, legAdd_coeff_add hcP' hcF', legAdd_coeff_const_mul,
    legAdd_coeff_const_mul (-(π / (2 * sin (ν * π)))) (fun t => F (t + π)),
    legQAdd_coeff_shift_pi hFper,
    legAdd_fer_coeff_eq h1 h2' hs m (fun n => legAdd_fer_nat h1 h2' hs m n) ν, hFdef,
    legAdd_fer_coeff_eq h1 (by linarith) hs' m (fun n => legAdd_fer_nat h1 (by linarith) hs' m n) ν,
    Real.cos_pi_sub]
  have hx2 : Real.cos θ₂ ∈ Ioo (-1:ℝ) 1 := ⟨legAdd_neg_one_lt_cos h2' h2, by
    rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl h2.le (by linarith)⟩
  have hc := ferrers_connection_10 ν (-(m:ℂ)) (hreg _ (by simp)) (hreg _ (by simp)) hx2
  rw [neg_neg, show (ν - -(m:ℂ)) * π = ν * π + m * π by ring, cos_antiperiodic.add_nat_mul_eq,
    sin_antiperiodic.add_nat_mul_eq] at hc
  have hsq : ((-1:ℂ)) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : π / (2 * sin (ν * π)) * (2 / π * sin (ν * π)) = 1 := by field_simp
  set u : ℂ := (-1) ^ m
  set k : ℂ := π / (2 * sin (ν * π))
  set P1 := ferrersP ν (-(m:ℂ)) (Real.cos θ₁)
  set Pm := ferrersP ν m (Real.cos θ₂)
  set Q := ferrersQ ν m (Real.cos θ₂)
  linear_combination (-k * u ^ 2 * P1) * hc + (-k * cos (ν * π) * u * P1 * Pm + u * P1 * Q) * hsq +
    (u ^ 3 * P1 * Q) * hk


/-- `legAdd_fY θ₁ θ₂` is smooth in the angle. -/
theorem legQAdd_fY_contDiff (θ₁ θ₂ : ℝ) : ContDiff ℝ 2 (legAdd_fY θ₁ θ₂) := by
  unfold legAdd_fY
  exact contDiff_const.add (contDiff_const.mul Real.contDiff_cos)

/-- The Fourier coefficients of `φ ↦ 𝖰_ν(cos θ₁ cos θ₂ + sin θ₁ sin θ₂ cos φ)` for every regular
degree: the non-real case `legQAdd_coeff_eq_of_im` extended by continuity in `ν`. -/
theorem legQAdd_coeff_eq {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h12 : θ₁ < θ₂) (hs : θ₁ + θ₂ < π)
    (m : ℕ) {ν : ℂ} (hr : LegendreQRegular ν 0) :
    legAdd_coeff (fun t => ferrersQ ν 0 (legAdd_fY θ₁ θ₂ t)) m =
      (-1:ℂ) ^ m * ferrersP ν (-(m:ℂ)) (Real.cos θ₁) * ferrersQ ν m (Real.cos θ₂) := by
  have h2 : θ₂ < π := by linarith
  have hrm : ∀ w : ℂ, LegendreQRegular w 0 → LegendreQRegular w m := fun w hw n hn =>
    hw (n + m) (by push_cast; linear_combination hn)
  have hx1 : -1 < Real.cos θ₁ := legAdd_neg_one_lt_cos h1 (by linarith)
  have hx2 : Real.cos θ₂ ∈ Ioo (-1:ℝ) 1 := ⟨legAdd_neg_one_lt_cos (by linarith) h2, by
    rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl h2.le (by linarith)⟩
  have hG : ContinuousAt (fun w => legAdd_coeff (fun t => ferrersQ w 0 (legAdd_fY θ₁ θ₂ t)) m -
      (-1:ℂ) ^ m * ferrersP w (-(m:ℂ)) (Real.cos θ₁) * ferrersQ w m (Real.cos θ₂)) ν :=
    (legQAdd_continuousAt_coeff hr (legQAdd_fY_contDiff θ₁ θ₂)
      (legAdd_neg_one_lt_cos (by linarith) hs) (legQAdd_fY_lt_one h1 h12 h2 0).2
      (legQAdd_fY_mem h1 h12 hs) m).sub
      ((continuousAt_const.mul (legAdd_differentiable_ferrersP _ hx1).continuous.continuousAt).mul
        (continuousAt_ferrersQ_degree (hrm ν hr) hx2))
  have := eq_zero_of_im_ne_zero (μ := 0) hG (fun w hw => by
    rw [add_zero] at hw; exact sub_eq_zero.mpr (legQAdd_coeff_eq_of_im h1 h12 hs m hw))
  exact sub_eq_zero.mp this

/-- **Addition theorem for Ferrers functions of the second kind** (DLMF 14.18.3). -/
theorem legQAdd_ferrersQ_addition (ν : ℂ) {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h12 : θ₁ < θ₂)
    (hs : θ₁ + θ₂ < π) (hr : LegendreQRegular ν 0) (phi : ℝ) :
    HasSum (fun j : ℕ => let m := j + 1; 2 * (-1) ^ m * ferrersP ν (-m) (Real.cos θ₁) *
      ferrersQ ν m (Real.cos θ₂) * Real.cos (m * phi))
      (ferrersQ ν 0 (Real.cos θ₁ * Real.cos θ₂ + Real.sin θ₁ * Real.sin θ₂ * Real.cos phi) -
        ferrersP ν 0 (Real.cos θ₁) * ferrersQ ν 0 (Real.cos θ₂)) := by
  have hper : Function.Periodic (fun t : ℝ => ferrersQ ν 0 (legAdd_fY θ₁ θ₂ t)) (2 * π) :=
    fun t => by simp only [legAdd_fY, Real.cos_add_two_pi]
  have hev : ∀ t, (fun t : ℝ => ferrersQ ν 0 (legAdd_fY θ₁ θ₂ t)) (-t) =
      (fun t : ℝ => ferrersQ ν 0 (legAdd_fY θ₁ θ₂ t)) t :=
    fun t => by simp only [legAdd_fY, Real.cos_neg]
  have hy1 : ∀ t, legAdd_fY θ₁ θ₂ t ^ 2 < 1 := fun t => by
    have h3 := legQAdd_fY_mem h1 h12 hs t
    have h4 := legAdd_neg_one_lt_cos (by linarith) hs
    have h5 := (legQAdd_fY_lt_one h1 h12 (by linarith) t).2
    have h6 : -1 < legAdd_fY θ₁ θ₂ t := by linarith [h3.1]
    have h7 : legAdd_fY θ₁ θ₂ t < 1 := by linarith [h3.2]
    nlinarith
  have hF := legAdd_hasSum_cos (legQAdd_contDiff_ferrersQ ν (legQAdd_fY_contDiff θ₁ θ₂) hy1)
    hper hev phi
  have h0 := legQAdd_coeff_eq h1 h12 hs 0 hr
  simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero] at h0
  convert hF using 1
  · funext j
    rw [legQAdd_coeff_eq h1 h12 hs (j + 1) hr]
    push_cast
    ring
  · rw [h0]; rfl

/-- **The combined argument avoids the cut.** If `Re z₁, Re z₂ > 0`, `sᵢ² = zᵢ² - 1` (any square
roots) and `-1 ≤ c ≤ 1`, then `1 + z₁ z₂ - s₁ s₂ c` lies in the slit plane. Writing
`zᵢ ± 1 = bᵢ², aᵢ²` with `aᵢ bᵢ = sᵢ`, `1 + z₁z₂ - c s₁s₂ = (1+c)/4 X² + (1-c)/4 Y²` with
`X, Y = b₁b₂ ∓ a₁a₂`, and `Re (X Ȳ) = |z₁+1||z₂+1| - |z₁-1||z₂-1| > 0`, `Re (XY) = 2 Re (z₁+z₂) > 0`. -/
theorem legQAdd_one_add_mem_slitPlane {z₁ z₂ s₁ s₂ : ℂ} (hz₁ : 0 < z₁.re) (hz₂ : 0 < z₂.re)
    (hs₁ : s₁ ^ 2 = z₁ ^ 2 - 1) (hs₂ : s₂ ^ 2 = z₂ ^ 2 - 1) {c : ℝ} (hc1 : -1 ≤ c) (hc2 : c ≤ 1) :
    1 + (z₁ * z₂ - s₁ * s₂ * c) ∈ slitPlane := by
  have hb0 : ∀ z : ℂ, 0 < z.re → z + 1 ≠ 0 := fun z hz h => by
    have := congrArg re h; simp at this; linarith
  obtain ⟨b₁, hb₁⟩ : ∃ b : ℂ, b ^ 2 = z₁ + 1 :=
    ⟨_, cpow_nat_inv_pow _ two_ne_zero⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b : ℂ, b ^ 2 = z₂ + 1 :=
    ⟨_, cpow_nat_inv_pow _ two_ne_zero⟩
  have hb₁0 : b₁ ≠ 0 := fun h => hb0 z₁ hz₁ (by rw [← hb₁, h]; ring)
  have hb₂0 : b₂ ≠ 0 := fun h => hb0 z₂ hz₂ (by rw [← hb₂, h]; ring)
  set a₁ := s₁ / b₁
  set a₂ := s₂ / b₂
  have ha₁ : a₁ ^ 2 = z₁ - 1 := by
    simp only [a₁]; rw [div_pow, hs₁, hb₁]; field_simp [hb0 z₁ hz₁]; ring
  have ha₂ : a₂ ^ 2 = z₂ - 1 := by
    simp only [a₂]; rw [div_pow, hs₂, hb₂]; field_simp [hb0 z₂ hz₂]; ring
  have hab₁ : a₁ * b₁ = s₁ := by simp only [a₁]; field_simp
  have hab₂ : a₂ * b₂ = s₂ := by simp only [a₂]; field_simp
  set X := b₁ * b₂ - a₁ * a₂
  set Y := b₁ * b₂ + a₁ * a₂
  have hW : 1 + (z₁ * z₂ - s₁ * s₂ * c) = ((1 + c) / 4 : ℝ) * X ^ 2 + ((1 - c) / 4 : ℝ) * Y ^ 2 := by
    rw [← hab₁, ← hab₂]
    simp only [X, Y]
    push_cast
    linear_combination (-(1:ℂ)/2) * ((b₂ ^ 2) * hb₁ + (z₁ + 1) * hb₂) + (-(1:ℂ)/2) * ((a₂ ^ 2) * ha₁ + (z₁ - 1) * ha₂)
  -- the two real parts
  have hXY : 0 < (X * Y).re := by
    have : X * Y = 2 * (z₁ + z₂) := by
      simp only [X, Y]
      linear_combination (b₂ ^ 2) * hb₁ + (z₁ + 1) * hb₂ - ((a₂ ^ 2) * ha₁ + (z₁ - 1) * ha₂)
    rw [this]; simp; linarith
  have hnorm : ∀ (z b : ℂ), b ^ 2 = z → normSq b ^ 2 = normSq z := fun z b h => by
    rw [← h, map_pow]
  have hlt : ∀ z : ℂ, 0 < z.re → normSq (z - 1) < normSq (z + 1) := fun z hz => by
    simp only [normSq_apply, sub_re, add_re, one_re, sub_im, add_im, one_im]; nlinarith
  have hXcY : 0 < (X * conj Y).re := by
    have e : (X * conj Y).re = normSq b₁ * normSq b₂ - normSq a₁ * normSq a₂ := by
      simp only [X, Y, mul_re, conj_re, conj_im, add_re, add_im, sub_re, sub_im, mul_im, normSq_apply]
      ring
    rw [e]
    have p1 := hnorm _ _ hb₁
    have p2 := hnorm _ _ hb₂
    have q1 := hnorm _ _ ha₁
    have q2 := hnorm _ _ ha₂
    have l1 := hlt z₁ hz₁
    have l2 := hlt z₂ hz₂
    have n1 := normSq_nonneg b₁
    have n2 := normSq_nonneg b₂
    have n3 := normSq_nonneg a₁
    have n4 := normSq_nonneg a₂
    have r1 : normSq a₁ < normSq b₁ := by nlinarith
    have r2 : normSq a₂ < normSq b₂ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left r2.le n3]
  rw [mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  obtain ⟨r, hr⟩ : ∃ r : ℝ, 1 + (z₁ * z₂ - s₁ * s₂ * c) = r :=
    ⟨(1 + (z₁ * z₂ - s₁ * s₂ * c)).re, by apply Complex.ext <;> simp [him]⟩
  have hr0 : r ≤ 0 := by have := congrArg Complex.re hr; simp only [ofReal_re] at this; linarith
  have key : (r : ℂ) * conj (X * Y) = (((1 + c) / 4 * normSq X : ℝ) : ℂ) * (X * conj Y) +
      (((1 - c) / 4 * normSq Y : ℝ) : ℂ) * conj (X * conj Y) := by
    rw [← hr, hW, map_mul, map_mul, Complex.conj_conj]
    push_cast
    rw [← mul_conj X, ← mul_conj Y]
    ring
  have hre_key := congrArg Complex.re key
  rw [re_ofReal_mul, conj_re, add_re, re_ofReal_mul, re_ofReal_mul, conj_re] at hre_key
  have hX0 : X ≠ 0 := fun h => by rw [h, zero_mul] at hXcY; simp at hXcY
  have hY0 : Y ≠ 0 := fun h => by rw [h, map_zero, mul_zero] at hXcY; simp at hXcY
  have nX := normSq_pos.2 hX0
  have nY := normSq_pos.2 hY0
  have hpos : 0 < (1 + c) / 4 * normSq X + (1 - c) / 4 * normSq Y := by
    have e1 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 + c) / 4) nX.le
    have e2 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - c) / 4) nY.le
    rcases le_or_gt c 0 with h | h
    · have := mul_pos (by linarith : (0:ℝ) < (1 - c) / 4) nY; linarith
    · have := mul_pos (by linarith : (0:ℝ) < (1 + c) / 4) nX; linarith
  have h3 := mul_pos hpos hXcY
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hr0 hXY.le]


/-- The square-root branch `(z²-1)^{1/2} = exp ((log (z-1) + log (z+1))/2)` of DLMF 14.28.1. -/
def legQAdd_sq (z : ℂ) : ℂ := exp ((log (z - 1) + log (z + 1)) / 2)

theorem legQAdd_sq_sq {z : ℂ} (h1 : z - 1 ≠ 0) (h2 : z + 1 ≠ 0) : legQAdd_sq z ^ 2 = z ^ 2 - 1 := by
  rw [legQAdd_sq, ← exp_nat_mul, show ((2:ℕ):ℂ) * ((log (z - 1) + log (z + 1)) / 2) =
    log (z - 1) + log (z + 1) by push_cast; ring, exp_add, exp_log h1, exp_log h2]
  ring

/-- The domain `Re z > 0`, `z ∉ (0, 1]` of DLMF 14.28.1. -/
def legQAdd_D : Set ℂ := {z | 0 < z.re ∧ z - 1 ∈ slitPlane}

theorem isOpen_legQAdd_D : IsOpen legQAdd_D :=
  (isOpen_lt continuous_const continuous_re).inter
    (isOpen_slitPlane.preimage (by fun_prop : Continuous fun z : ℂ => z - 1))

theorem legQAdd_add_one_mem {z : ℂ} (hz : 0 < z.re) : z + 1 ∈ slitPlane :=
  Or.inl (by simp; linarith)

theorem legQAdd_differentiableAt_sq {z : ℂ} (hz : z ∈ legQAdd_D) :
    DifferentiableAt ℂ legQAdd_sq z := by
  have h1 : DifferentiableAt ℂ (fun w : ℂ => log (w - 1)) z :=
    (differentiableAt_id.sub_const 1).clog hz.2
  have h2 : DifferentiableAt ℂ (fun w : ℂ => log (w + 1)) z :=
    (differentiableAt_id.add_const 1).clog (legQAdd_add_one_mem hz.1)
  exact ((h1.add h2).div_const 2).cexp

/-- The combined argument `z₁ z₂ - (z₁²-1)^{1/2} (z₂²-1)^{1/2} cos t` of DLMF 14.28.1. -/
def legQAdd_Z (z₁ z₂ : ℂ) (t : ℝ) : ℂ := z₁ * z₂ - legQAdd_sq z₁ * legQAdd_sq z₂ * Real.cos t

theorem legQAdd_Z_comm (z₁ z₂ : ℂ) (t : ℝ) : legQAdd_Z z₁ z₂ t = legQAdd_Z z₂ z₁ t := by
  simp only [legQAdd_Z]; ring

/-- The combined argument stays in the domain of holomorphy of `P_ν`, for every angle. -/
theorem legQAdd_Z_mem {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ legQAdd_D) (hz₂ : z₂ ∈ legQAdd_D) (t : ℝ) :
    (1 - legQAdd_Z z₁ z₂ t) / 2 ∈ cutPlane := by
  have hs : ∀ z ∈ legQAdd_D, legQAdd_sq z ^ 2 = z ^ 2 - 1 := fun z hz =>
    legQAdd_sq_sq (slitPlane_ne_zero hz.2) (slitPlane_ne_zero (legQAdd_add_one_mem hz.1))
  have h := legQAdd_one_add_mem_slitPlane hz₁.1 hz₂.1 (hs z₁ hz₁) (hs z₂ hz₂)
    (Real.neg_one_le_cos t) (Real.cos_le_one t)
  show 1 - (1 - legQAdd_Z z₁ z₂ t) / 2 ∈ slitPlane
  rw [show 1 - (1 - legQAdd_Z z₁ z₂ t) / 2 = (1 + legQAdd_Z z₁ z₂ t) / 2 by ring]
  rw [mem_slitPlane_iff] at h ⊢
  simp only [div_ofNat_re, div_ofNat_im]
  rcases h with h | h
  · left; unfold legQAdd_Z; linarith
  · right; unfold legQAdd_Z; intro h'; apply h; linarith

/-- `(cosh² ξ - 1)^{1/2} = sinh ξ` in the branch of 14.28.1, for `ξ > 0`. -/
theorem legQAdd_sq_cosh {ξ : ℝ} (hξ : 0 < ξ) : legQAdd_sq (Real.cosh ξ) = Real.sinh ξ := by
  have hc : 1 < Real.cosh ξ := Real.one_lt_cosh.2 hξ.ne'
  have e1 : log ((Real.cosh ξ : ℂ) - 1) = (Real.log (Real.cosh ξ - 1) : ℂ) := by
    rw [show (Real.cosh ξ : ℂ) - 1 = ((Real.cosh ξ - 1 : ℝ) : ℂ) by push_cast; ring,
      ofReal_log (by linarith)]
  have e2 : log ((Real.cosh ξ : ℂ) + 1) = (Real.log (Real.cosh ξ + 1) : ℂ) := by
    rw [show (Real.cosh ξ : ℂ) + 1 = ((Real.cosh ξ + 1 : ℝ) : ℂ) by push_cast; ring,
      ofReal_log (by linarith)]
  rw [legQAdd_sq, e1, e2, show ((Real.log (Real.cosh ξ - 1) : ℂ) + Real.log (Real.cosh ξ + 1)) / 2 =
    (((Real.log (Real.cosh ξ - 1) + Real.log (Real.cosh ξ + 1)) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_exp]
  congr 1
  have hpos := Real.exp_pos ((Real.log (Real.cosh ξ - 1) + Real.log (Real.cosh ξ + 1)) / 2)
  have hsh : 0 < Real.sinh ξ := Real.sinh_pos_iff.2 hξ
  have hsq : Real.exp ((Real.log (Real.cosh ξ - 1) + Real.log (Real.cosh ξ + 1)) / 2) ^ 2 =
      Real.sinh ξ ^ 2 := by
    rw [← Real.exp_nat_mul, show ((2:ℕ):ℝ) * ((Real.log (Real.cosh ξ - 1) +
      Real.log (Real.cosh ξ + 1)) / 2) = Real.log (Real.cosh ξ - 1) + Real.log (Real.cosh ξ + 1) by
      push_cast; ring, Real.exp_add, Real.exp_log (by linarith), Real.exp_log (by linarith)]
    rw [Real.sinh_sq]; ring
  exact (pow_left_inj₀ hpos.le hsh.le two_ne_zero).1 hsq

/-- At real points the combined argument is that of 14.18.4. -/
theorem legQAdd_Z_cosh {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (t : ℝ) :
    legQAdd_Z (Real.cosh ξ₁) (Real.cosh ξ₂) t = legAdd_hX ξ₁ ξ₂ t := by
  simp only [legQAdd_Z, legAdd_hX, legQAdd_sq_cosh h1, legQAdd_sq_cosh h2]
  push_cast; ring


theorem legQAdd_continuousOn_sq : ContinuousOn legQAdd_sq legQAdd_D := fun _ hz =>
  (legQAdd_differentiableAt_sq hz).continuousAt.continuousWithinAt

/-- Joint continuity of `(z, t) ↦ P_ν(legQAdd_Z z z₂ t)` on `D × ℝ`. -/
theorem legQAdd_continuousOn_joint (ν : ℂ) {z₂ : ℂ} (hz₂ : z₂ ∈ legQAdd_D) :
    ContinuousOn (fun p : ℂ × ℝ => associatedP ν 0 (legQAdd_Z p.1 z₂ p.2)) (legQAdd_D ×ˢ univ) := by
  have hF : DifferentiableOn ℂ (fun w => regularizedGaussHG (ν + 1) (-ν) 1 w) cutPlane :=
    DifferentiableOn.regularizedGaussHG (differentiableOn_const _) (differentiableOn_const _)
      (differentiableOn_const _) differentiableOn_id fun w hw => hw
  simp only [legAdd_associatedP_zero_eq]
  refine hF.continuousOn.comp (f := fun p : ℂ × ℝ => (1 - legQAdd_Z p.1 z₂ p.2) / 2) ?_
    (fun p hp => legQAdd_Z_mem hp.1 hz₂ p.2)
  have hs : ContinuousOn (fun p : ℂ × ℝ => legQAdd_sq p.1) (legQAdd_D ×ˢ univ) :=
    legQAdd_continuousOn_sq.comp continuous_fst.continuousOn (fun p hp => hp.1)
  unfold legQAdd_Z
  exact (continuousOn_const.sub ((continuous_fst.continuousOn.mul continuousOn_const).sub
    ((hs.mul continuousOn_const).mul
      (by fun_prop : Continuous fun p : ℂ × ℝ => ((Real.cos p.2 : ℝ) : ℂ)).continuousOn))).div_const 2

/-- The Fourier coefficients of `t ↦ P_ν(legQAdd_Z z z₂ t)` are holomorphic in `z ∈ D`. -/
theorem legQAdd_coeff_differentiableOn (ν : ℂ) {z₂ : ℂ} (hz₂ : z₂ ∈ legQAdd_D) (m : ℤ) :
    DifferentiableOn ℂ (fun z => legAdd_coeff (fun t => associatedP ν 0 (legQAdd_Z z z₂ t)) m)
      legQAdd_D := by
  have hj := legQAdd_continuousOn_joint ν hz₂
  have hct : ∀ z ∈ legQAdd_D, Continuous (fun t : ℝ => associatedP ν 0 (legQAdd_Z z z₂ t)) :=
    fun z hz => by
      have hc : Continuous fun t : ℝ => ((z, t) : ℂ × ℝ) := by fun_prop
      have h3 := hj.comp_continuous hc (fun t => Set.mk_mem_prod hz (mem_univ t))
      exact h3
  have key : DifferentiableOn ℂ (fun z => ∫ t in (-π)..π, exp (-((m:ℂ) * t * I)) *
      associatedP ν 0 (legQAdd_Z z z₂ t)) legQAdd_D := by
    apply Complex.differentiableOn_intervalIntegral_of_locally_dominated isOpen_legQAdd_D
    · intro z hz
      exact ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
        (hct z hz)).aestronglyMeasurable
    · refine ae_of_all _ fun t => ?_
      simp only [legAdd_associatedP_zero_eq]
      refine (differentiableOn_const _).mul (DifferentiableOn.regularizedGaussHG
        (differentiableOn_const _) (differentiableOn_const _) (differentiableOn_const _) ?_
        (fun z hz => legQAdd_Z_mem hz hz₂ t))
      have hsd : DifferentiableOn ℂ legQAdd_sq legQAdd_D := fun z hz =>
        (legQAdd_differentiableAt_sq hz).differentiableWithinAt
      unfold legQAdd_Z
      exact ((differentiableOn_const _).sub ((differentiableOn_id.mul (differentiableOn_const _)).sub
        ((hsd.mul (differentiableOn_const _)).mul (differentiableOn_const _)))).div_const 2
    · intro z₀ hz₀
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_legQAdd_D z₀ hz₀
      have hK : IsCompact (Metric.closedBall z₀ (r / 2) ×ˢ Icc (-π) π) :=
        (isCompact_closedBall _ _).prod isCompact_Icc
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hj.mono (prod_mono
        ((Metric.closedBall_subset_ball (by linarith)).trans hball) (subset_univ _)))
      refine ⟨Metric.closedBall z₀ (r / 2), Metric.closedBall_mem_nhds _ (by linarith),
        fun _ => C, integrableOn_const (by rw [uIoc_of_le (by linarith [Real.pi_pos])]; simp), ?_⟩
      refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun t ht y hy => ?_)
      rw [norm_mul, show -((m:ℂ) * t * I) = ((-(m * t) : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I, one_mul]
      rw [uIoc_of_le (by linarith [Real.pi_pos])] at ht
      exact hC (y, t) ⟨hy, ht.1.le, ht.2⟩
  exact (key.const_mul _).congr fun z _ => rfl

/-- Half-plane intersections used to reach any point of `D` from the real axis. -/
theorem legQAdd_U_props {κ σ : ℝ} (hκ : 0 < κ) :
    IsOpen {w : ℂ | 0 < w.re ∧ κ * (1 - w.re) < σ * w.im} ∧
    Convex ℝ {w : ℂ | 0 < w.re ∧ κ * (1 - w.re) < σ * w.im} ∧
    {w : ℂ | 0 < w.re ∧ κ * (1 - w.re) < σ * w.im} ⊆ legQAdd_D ∧
    ((Real.cosh 1 : ℝ) : ℂ) ∈ {w : ℂ | 0 < w.re ∧ κ * (1 - w.re) < σ * w.im} := by
  have hc : 1 < Real.cosh 1 := Real.one_lt_cosh.2 one_ne_zero
  have ho : IsOpen ({w : ℂ | 0 < w.re} ∩ {w : ℂ | κ * (1 - w.re) < σ * w.im}) :=
    (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt (f := fun w : ℂ => κ * (1 - w.re)) (g := fun w : ℂ => σ * w.im)
        (by fun_prop) (by fun_prop))
  refine ⟨ho, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [mem_ofPred_eq, add_re, add_im, Complex.real_smul, re_ofReal_mul, im_ofReal_mul] at hx hy ⊢
    constructor
    · rcases eq_or_lt_of_le ha with h | h
      · subst h; simp at hab; subst hab; simpa using hy.1
      · nlinarith [mul_pos h hx.1, mul_nonneg hb hy.1.le]
    · have e : κ * (1 - (a * x.re + b * y.re)) = a * (κ * (1 - x.re)) + b * (κ * (1 - y.re)) := by
        linear_combination (-κ) * hab
      rw [e]
      rcases eq_or_lt_of_le ha with h | h
      · subst h; simp at hab; subst hab; simpa using hy.2
      · nlinarith [mul_lt_mul_of_pos_left hx.2 h, mul_le_mul_of_nonneg_left hy.2.le hb]
  · intro w hw
    refine ⟨hw.1, ?_⟩
    rw [mem_slitPlane_iff]
    by_cases him : w.im = 0
    · left; simp only [sub_re, one_re]
      have h2 := hw.2; rw [him, mul_zero] at h2; nlinarith
    · right; simpa using him
  · simp only [mem_ofPred_eq, ofReal_re, ofReal_im, mul_zero]
    exact ⟨by linarith, by nlinarith⟩

/-- **Identity theorem on `D`**: holomorphic functions on `D` that agree at the points `cosh ξ`,
`ξ > 0`, agree on `D`. -/
theorem legQAdd_extend {F G : ℂ → ℂ} (hF : DifferentiableOn ℂ F legQAdd_D)
    (hG : DifferentiableOn ℂ G legQAdd_D) (h : ∀ ξ : ℝ, 0 < ξ → F (Real.cosh ξ) = G (Real.cosh ξ))
    {z : ℂ} (hz : z ∈ legQAdd_D) : F z = G z := by
  obtain ⟨κ, σ, hκ, hzU⟩ : ∃ κ σ : ℝ, 0 < κ ∧ z ∈ {w : ℂ | 0 < w.re ∧ κ * (1 - w.re) < σ * w.im} := by
    by_cases him : z.im = 0
    · refine ⟨1, 1, one_pos, hz.1, ?_⟩
      have h2 := hz.2
      rw [mem_slitPlane_iff] at h2
      simp only [sub_re, one_re, sub_im, one_im, sub_zero] at h2
      rcases h2 with h2 | h2
      · rw [him]; linarith
      · exact absurd him h2
    · have hpos : 0 < z.im ^ 2 := by positivity
      refine ⟨z.im ^ 2 / (2 * (|1 - z.re| + 1)), z.im, by positivity, hz.1, ?_⟩
      have hd : 0 < 2 * (|1 - z.re| + 1) := by positivity
      have h1 : z.im ^ 2 / (2 * (|1 - z.re| + 1)) * (1 - z.re) ≤
          z.im ^ 2 / (2 * (|1 - z.re| + 1)) * |1 - z.re| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      have h2 : z.im ^ 2 / (2 * (|1 - z.re| + 1)) * |1 - z.re| < z.im ^ 2 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hd]; nlinarith [abs_nonneg (1 - z.re)]
      nlinarith
  obtain ⟨hUo, hUc, hUD, hxU⟩ := legQAdd_U_props (σ := σ) hκ
  have hFa : AnalyticOnNhd ℂ F _ := (hF.mono hUD).analyticOnNhd hUo
  have hGa : AnalyticOnNhd ℂ G _ := (hG.mono hUD).analyticOnNhd hUo
  refine hFa.eqOn_of_preconnected_of_frequently_eq hGa hUc.isPreconnected hxU ?_ hzU
  have ht : Tendsto (fun ξ : ℝ => ((Real.cosh ξ : ℝ) : ℂ)) (𝓝[≠] 1)
      (𝓝[≠] ((Real.cosh 1 : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((continuous_ofReal.comp Real.continuous_cosh).tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)] with ξ hξ hξ0
      simp only [mem_compl_iff, mem_singleton_iff, ofReal_inj]
      intro he
      apply hξ
      rcases lt_trichotomy ξ 1 with h3 | h3 | h3
      · have := Real.cosh_lt_cosh.2 (show |ξ| < |(1:ℝ)| by
          rw [abs_of_pos (show (0:ℝ) < ξ from hξ0), abs_one]; exact h3)
        linarith
      · exact h3
      · have := Real.cosh_lt_cosh.2 (show |(1:ℝ)| < |ξ| by
          rw [abs_of_pos (show (0:ℝ) < ξ from hξ0), abs_one]; exact h3)
        linarith
  apply ht.frequently
  refine Filter.Eventually.frequently ?_
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)] with ξ hξ
  exact h ξ hξ


/-- `P^m_ν(z) = (ν-m+1)_{2m} P^{-m}_ν(z)` for every complex degree (14.9.13-type relation without
exceptional degrees, by continuation in `ν`). -/
theorem legQAdd_associatedP_nat_eq (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z - 1 ∈ slitPlane)
    (hz' : (1 - z) / 2 ∈ cutPlane) :
    associatedP ν m z = poch (ν - m + 1) (2 * m) * associatedP ν (-(m:ℂ)) z := by
  set D : ℂ → ℂ := fun ν => associatedP ν m z - poch (ν - m + 1) (2 * m) * associatedP ν (-(m:ℂ)) z
  have hD : Differentiable ℂ D := by
    have hp : Differentiable ℂ (fun ν : ℂ => poch (ν - m + 1) (2 * m)) := by
      show Differentiable ℂ (fun ν : ℂ => (ascPochhammer ℂ (2 * m)).eval (ν - m + 1))
      exact ((ascPochhammer ℂ (2 * m)).differentiable).comp (by fun_prop)
    exact (legAdd_differentiable_associatedP _ hz').sub (hp.mul
      (legAdd_differentiable_associatedP _ hz'))
  have hgen : ∀ ν : ℂ, (m:ℝ) < ν.re → D ν = 0 := by
    intro ν hν
    have hh : ∀ n : ℕ, ν - m + 1 ≠ -n := fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hGa : Gamma (ν - m + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hP := DLMF.Gamma.poch_mul_recip_Gamma_add_nat (ν - m + 1) (2 * m)
    rw [show ν - m + 1 + ((2 * m : ℕ) : ℂ) = ν + m + 1 by push_cast; ring] at hP
    simp only [D]
    rw [associatedP_negative_integer_order ν m hh hz]
    have : poch (ν - m + 1) (2 * m) * Gamma (ν - m + 1) / Gamma (ν + m + 1) = 1 := by
      rw [mul_div_assoc, div_eq_mul_inv, mul_comm (Gamma _), ← mul_assoc, hP, inv_mul_cancel₀ hGa]
    rw [show poch (ν - m + 1) (2 * m) * (Gamma (ν - m + 1) / Gamma (ν + m + 1) *
        associatedP ν m z) = (poch (ν - m + 1) (2 * m) * Gamma (ν - m + 1) / Gamma (ν + m + 1)) *
        associatedP ν m z by ring, this]
    ring
  have han : AnalyticOnNhd ℂ D univ := hD.differentiableOn.analyticOnNhd isOpen_univ
  have hev : D =ᶠ[𝓝 ((m:ℂ) + 1)] 0 := by
    have hopen : IsOpen {w : ℂ | (m:ℝ) < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (m:ℝ) < ((m:ℂ) + 1).re)] with w hw
    exact hgen w hw
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _) hev
    (mem_univ ν)
  exact sub_eq_zero.mp this

/-- The coefficient form of 14.18.4 used for 14.28.1: on `(1, ∞)`,
`(-1)^m P^{-m}_ν(x₁) P^m_ν(x₂) = (-1)^m P^m_ν(x₁) P^m_ν(x₂)/(ν-m+1)_{2m}` (both sides vanish
when the Pochhammer symbol does). -/
theorem legQAdd_hyp_coeff_eq' (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (m : ℕ) :
    legAdd_coeff (fun t => associatedP ν 0 (legQAdd_Z (Real.cosh ξ₁) (Real.cosh ξ₂) t)) m =
      (-1:ℂ) ^ m / poch (ν - m + 1) (2 * m) * associatedP ν m (Real.cosh ξ₁) *
        associatedP ν m (Real.cosh ξ₂) := by
  have hfun : (fun t => associatedP ν 0 (legQAdd_Z (Real.cosh ξ₁) (Real.cosh ξ₂) t)) =
      fun t => associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t) := by
    funext t; rw [legQAdd_Z_cosh h1 h2]
  rw [hfun, legAdd_hyp_coeff_eq ν h1 h2 m]
  have hz : ∀ ξ : ℝ, 0 < ξ → (Real.cosh ξ : ℂ) - 1 ∈ slitPlane ∧
      (1 - (Real.cosh ξ : ℂ)) / 2 ∈ cutPlane := fun ξ hξ => by
    have hc : 1 < Real.cosh ξ := Real.one_lt_cosh.2 hξ.ne'
    refine ⟨legInt_one_lt_mem hc, ?_⟩
    rw [show (1 - (Real.cosh ξ : ℂ)) / 2 = (((1 - Real.cosh ξ) / 2 : ℝ) : ℂ) by push_cast; ring]
    exact legAdd_ofReal_mem_cutPlane (by linarith)
  have e1 := legQAdd_associatedP_nat_eq ν m (hz ξ₁ h1).1 (hz ξ₁ h1).2
  have e2 := legQAdd_associatedP_nat_eq ν m (hz ξ₂ h2).1 (hz ξ₂ h2).2
  by_cases hp : poch (ν - m + 1) (2 * m) = 0
  · rw [e2, hp]; simp
  · rw [e1]; field_simp

/-- The Fourier coefficients of `φ ↦ P_ν(z₁z₂ - (z₁²-1)^{1/2}(z₂²-1)^{1/2} cos φ)` on `D × D`:
14.18.4 continued analytically in each variable (`legQAdd_extend`). -/
theorem legQAdd_complex_coeff_eq (ν : ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ legQAdd_D)
    (hz₂ : z₂ ∈ legQAdd_D) (m : ℕ) :
    legAdd_coeff (fun t => associatedP ν 0 (legQAdd_Z z₁ z₂ t)) m =
      (-1:ℂ) ^ m / poch (ν - m + 1) (2 * m) * associatedP ν m z₁ * associatedP ν m z₂ := by
  have hP : DifferentiableOn ℂ (associatedP ν m) legQAdd_D := fun z hz =>
    (associatedP_analytic ν m z hz.2).differentiableAt.differentiableWithinAt
  have hcD : ∀ ξ : ℝ, 0 < ξ → ((Real.cosh ξ : ℝ) : ℂ) ∈ legQAdd_D := fun ξ hξ =>
    ⟨by simp; exact Real.cosh_pos ξ, legInt_one_lt_mem (Real.one_lt_cosh.2 hξ.ne')⟩
  -- first variable, second one real
  have step1 : ∀ ξ₂ : ℝ, 0 < ξ₂ → ∀ z ∈ legQAdd_D,
      legAdd_coeff (fun t => associatedP ν 0 (legQAdd_Z z (Real.cosh ξ₂) t)) m =
        (-1:ℂ) ^ m / poch (ν - m + 1) (2 * m) * associatedP ν m z *
          associatedP ν m (Real.cosh ξ₂) := fun ξ₂ h2 z hz =>
    legQAdd_extend (legQAdd_coeff_differentiableOn ν (hcD ξ₂ h2) m)
      ((hP.const_mul _).mul_const _) (fun ξ₁ h1 => legQAdd_hyp_coeff_eq' ν h1 h2 m) hz
  have hsym : ∀ w : ℂ, (fun t => associatedP ν 0 (legQAdd_Z z₁ w t)) =
      fun t => associatedP ν 0 (legQAdd_Z w z₁ t) := fun w => by
    funext t; rw [legQAdd_Z_comm]
  have := legQAdd_extend (F := fun w => legAdd_coeff (fun t => associatedP ν 0 (legQAdd_Z w z₁ t)) m)
    (G := fun w => (-1:ℂ) ^ m / poch (ν - m + 1) (2 * m) * associatedP ν m z₁ * associatedP ν m w)
    (legQAdd_coeff_differentiableOn ν hz₁ m) ((differentiableOn_const _).mul hP)
    (fun ξ₂ h2 => by
      rw [← hsym]
      exact step1 ξ₂ h2 z₁ hz₁) hz₂
  rw [hsym]
  exact this


/-- `t ↦ P_ν(legQAdd_Z z₁ z₂ t)` is `C²` on `ℝ`. -/
theorem legQAdd_Z_contDiff (ν : ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ legQAdd_D) (hz₂ : z₂ ∈ legQAdd_D) :
    ContDiff ℝ 2 (fun t : ℝ => associatedP ν 0 (legQAdd_Z z₁ z₂ t)) := by
  have hG : DifferentiableOn ℂ (fun z => regularizedGaussHG (ν + 1) (-ν) 1 z) cutPlane :=
    DifferentiableOn.regularizedGaussHG (differentiableOn_const _) (differentiableOn_const _)
      (differentiableOn_const _) differentiableOn_id fun w hw => hw
  have hG2 : ContDiffOn ℝ 2 (fun z => regularizedGaussHG (ν + 1) (-ν) 1 z) cutPlane :=
    (hG.contDiffOn isOpen_cutPlane).restrict_scalars ℝ
  have hh : ContDiff ℝ 2 (fun t : ℝ => (1 - legQAdd_Z z₁ z₂ t) / 2) := by
    unfold legQAdd_Z
    have hc : ContDiff ℝ 2 (fun t : ℝ => ((Real.cos t : ℝ) : ℂ)) :=
      ofRealCLM.contDiff.comp Real.contDiff_cos
    exact (contDiff_const.sub (contDiff_const.sub (contDiff_const.mul hc))).div_const 2
  have := hG2.comp_contDiff hh fun t => legQAdd_Z_mem hz₁ hz₂ t
  convert this using 1
  funext t
  simp only [Function.comp, legAdd_associatedP_zero_eq]

/-- **Addition theorem for `P_ν` in the complex plane** (DLMF 14.28.1), for `Re z₁, Re z₂ > 0`,
`z₁, z₂ ∉ (0, 1]`, every complex degree and every angle. -/
theorem legQAdd_associatedP_complex_addition (ν : ℂ) {z₁ z₂ : ℂ} (h1 : 0 < z₁.re) (h2 : 0 < z₂.re)
    (hz1 : z₁ - 1 ∈ slitPlane) (hz2 : z₂ - 1 ∈ slitPlane) (phi : ℝ) :
    HasSum (fun j : ℕ => let m := j + 1; 2 * (-1) ^ m * 1 / poch (ν - m + 1) (2 * m) *
      associatedP ν m z₁ * associatedP ν m z₂ * Real.cos (m * phi))
      (associatedP ν 0 (z₁ * z₂ - exp ((log (z₁ - 1) + log (z₁ + 1)) / 2) *
        exp ((log (z₂ - 1) + log (z₂ + 1)) / 2) * Real.cos phi) -
        associatedP ν 0 z₁ * associatedP ν 0 z₂) := by
  have hz₁ : z₁ ∈ legQAdd_D := ⟨h1, hz1⟩
  have hz₂ : z₂ ∈ legQAdd_D := ⟨h2, hz2⟩
  have hper : Function.Periodic (fun t : ℝ => associatedP ν 0 (legQAdd_Z z₁ z₂ t)) (2 * π) :=
    fun t => by simp only [legQAdd_Z, Real.cos_add_two_pi]
  have hev : ∀ t, (fun t : ℝ => associatedP ν 0 (legQAdd_Z z₁ z₂ t)) (-t) =
      (fun t : ℝ => associatedP ν 0 (legQAdd_Z z₁ z₂ t)) t :=
    fun t => by simp only [legQAdd_Z, Real.cos_neg]
  have hF := legAdd_hasSum_cos (legQAdd_Z_contDiff ν hz₁ hz₂) hper hev phi
  have h0 := legQAdd_complex_coeff_eq ν hz₁ hz₂ 0
  simp only [pow_zero, Nat.cast_zero, mul_zero, sub_zero] at h0
  rw [show poch (ν + 1) 0 = 1 from by simp [poch], div_one, one_mul] at h0
  convert hF using 1
  · funext j
    rw [legQAdd_complex_coeff_eq ν hz₁ hz₂ (j + 1)]
    push_cast
    ring
  · rw [h0]; rfl

end DLMF.Legendre
