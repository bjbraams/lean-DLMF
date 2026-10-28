/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Integrals.BarnesAndRamanujan

import DLMF.Gamma.RecipGammaDeriv

/-!
# Fourier kernels and trigamma sums

Fourier transforms of trigonometric Gamma kernels, their complex continuation and trigamma
summations.

Source references and common attribution are retained in
`DLMF.Gamma.Integrals`.
-/

@[expose] public section

open Complex MeasureTheory Filter

open scoped Real Topology ComplexConjugate

noncomputable section

namespace DLMF.Gamma

section Ramanujan

open Set FourierTransform

open scoped Interval

namespace RamanujanAux

/-! ### Fourier transforms of the kernels `cos^p φ e^{iζφ}` on `(-π/2, π/2]` -/

/-- The kernel `1_{(-π/2,π/2]}(φ) cos^p φ e^{iζφ}`. -/
def kern (p ζ : ℝ) : ℝ → ℂ := (Ioc (-(π / 2)) (π / 2)).indicator fun φ =>
  ((Real.cos φ ^ p : ℝ) : ℂ) * Complex.exp ((ζ : ℂ) * φ * I)

/-- The Fourier transform of the kernel `cos^p φ e^(iζφ)` on `(-π/2, π/2]` is the corresponding
cosine-power integral. -/
theorem fourier_kern_eq (p ζ w : ℝ) :
    𝓕 (kern p ζ) w = ∫ x in (-(π / 2))..(π / 2),
      ((Real.cos x ^ p : ℝ) : ℂ) * Complex.exp (((ζ : ℂ) - 2 * π * w) * x * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ← integral_indicator measurableSet_Ioc]
  congr 1; funext v
  simp only [kern, smul_eq_mul]
  by_cases hv : v ∈ Ioc (-(π / 2)) (π / 2)
  · rw [indicator_of_mem hv, indicator_of_mem hv, mul_left_comm, ← Complex.exp_add]
    congr 2; push_cast; ring
  · rw [indicator_of_notMem hv, indicator_of_notMem hv, mul_zero]

/-- For `p > -1`, the Fourier transform of `cos^p φ e^(iζφ)` on `(-π/2, π/2]` is `π Γ(p + 1) 2^(-p)
/ (Γ(1 + p/2 + u/2) Γ(1 + p/2 - u/2))` with `u = ζ - 2πw`. -/
theorem fourier_kern {p : ℝ} (hp : -1 < p) (ζ w : ℝ) :
    𝓕 (kern p ζ) w = ((π * Real.Gamma (p + 1) / 2 ^ p : ℝ) : ℂ) *
      ((Complex.Gamma (1 + p / 2 + ((ζ : ℂ) - 2 * π * w) / 2))⁻¹ *
        (Complex.Gamma (1 + p / 2 - ((ζ : ℂ) - 2 * π * w) / 2))⁻¹) := by
  rw [fourier_kern_eq]; exact integral_cos_rpow_mul_cexp hp _

/-- For `p > -1` the kernel `cos^p φ e^(iζφ)` on `(-π/2, π/2]` is integrable. -/
theorem integrable_kern {p : ℝ} (hp : -1 < p) (ζ : ℝ) : Integrable (kern p ζ) := by
  rw [kern, integrable_indicator_iff measurableSet_Ioc]
  have hle : -(π / 2) ≤ π / 2 := by linarith [Real.pi_pos]
  have hii : IntervalIntegrable (fun x : ℝ => ((Real.cos x ^ p : ℝ) : ℂ) *
      Complex.exp ((ζ : ℂ) * x * I)) volume (-(π / 2)) (π / 2) :=
    (intervalIntegrable_ofReal (intervalIntegrable_cos_rpow' hp)).mul_continuousOn
      (by fun_prop : Continuous fun x : ℝ => Complex.exp ((ζ : ℂ) * x * I)).continuousOn
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hii

/-- The kernel `cos^p φ e^(iζφ)` is continuous on `(-π/2, π/2)`. -/
theorem continuousAt_kern (p ζ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    ContinuousAt (kern p ζ) x := by
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hx
  have hc : ContinuousAt (fun φ : ℝ => ((Real.cos φ ^ p : ℝ) : ℂ) *
      Complex.exp ((ζ : ℂ) * φ * I)) x :=
    (Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_rpow_const _ _ (Or.inl hcos.ne')).comp
        Real.continuous_cos.continuousAt)).mul
      (by fun_prop : Continuous fun φ : ℝ => Complex.exp ((ζ : ℂ) * φ * I)).continuousAt
  refine hc.congr ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  simp [kern, indicator_of_mem (Ioo_subset_Ioc_self hy)]

/-- The Fourier transform is linear in scalar multiples. -/
theorem fourier_const_mul (C : ℂ) (F : ℝ → ℂ) (x : ℝ) :
    𝓕 (fun ξ => C * F ξ) x = C * 𝓕 F x := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  congr 1; funext v; simp only [smul_eq_mul]; ring

/-- The Fourier transform at `0` is the integral. -/
theorem fourier_zero_eq_integral (F : ℝ → ℂ) : 𝓕 F 0 = ∫ v, F v := by
  rw [Real.fourier_real_eq_integral_exp_smul]; simp

/-- Fourier inversion for the cosine-power kernel at interior points. -/
theorem fourier_fourier_kern {p : ℝ} (hp : -1 < p) (ζ : ℝ) (h𝓕 : Integrable (𝓕 (kern p ζ)))
    {x : ℝ} (hx : -x ∈ Ioo (-(π / 2)) (π / 2)) :
    𝓕 (𝓕 (kern p ζ)) x = kern p ζ (-x) := by
  have h := (integrable_kern hp ζ).fourierInv_fourier_eq h𝓕 (continuousAt_kern p ζ hx)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h
  exact h

/-- **Ramanujan's integral for real parameters** with `a + c > 1` and `b + d > 2`, by the
multiplication formula `∫ 𝓕h · G = ∫ h · 𝓕G` and Fourier inversion. -/
theorem integral_ramanujanIntegrand_of_real {a b c d : ℝ} (hac : 1 < a + c) (hbd : 2 < b + d) :
    ∫ t : ℝ, ramanujanIntegrand a b c d t =
      Complex.Gamma (a + b + c + d - 3) /
        (Complex.Gamma (a + c - 1) * Complex.Gamma (a + d - 1) *
          Complex.Gamma (b + c - 1) * Complex.Gamma (b + d - 1)) := by
  set p₁ : ℝ := a + c - 2 with hp₁d
  set ζ₁ : ℝ := c - a with hζ₁d
  set p₂ : ℝ := b + d - 2 with hp₂d
  set ζ₂ : ℝ := d - b with hζ₂d
  have hp₁ : -1 < p₁ := by rw [hp₁d]; linarith
  have hp₂ : -1 < p₂ := by rw [hp₂d]; linarith
  have hP : -1 < p₁ + p₂ := by linarith
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  set C₁ : ℂ := ((π * Real.Gamma (p₁ + 1) / 2 ^ p₁ : ℝ) : ℂ) with hC₁
  set C₂ : ℂ := ((π * Real.Gamma (p₂ + 1) / 2 ^ p₂ : ℝ) : ℂ) with hC₂
  set CP : ℂ := ((π * Real.Gamma (p₁ + p₂ + 1) / 2 ^ (p₁ + p₂) : ℝ) : ℂ) with hCP
  have hC₂0 : C₂ ≠ 0 := by
    rw [hC₂]; exact ofReal_ne_zero.2 (by
      have := Real.Gamma_pos_of_pos (show 0 < p₂ + 1 by linarith)
      positivity)
  have hC₁0 : C₁ ≠ 0 := by
    rw [hC₁]; exact ofReal_ne_zero.2 (by
      have := Real.Gamma_pos_of_pos (show 0 < p₁ + 1 by linarith)
      positivity)
  -- the Fourier transforms of the two kernels
  have hF1 : ∀ w : ℝ, 𝓕 (kern p₁ ζ₁) w = C₁ *
      ((Complex.Gamma (c - π * w))⁻¹ * (Complex.Gamma (a + π * w))⁻¹) := by
    intro w; rw [fourier_kern hp₁]
    congr 4 <;> simp only [hp₁d, hζ₁d] <;> push_cast <;> ring
  have hF2 : ∀ w : ℝ, 𝓕 (kern p₂ ζ₂) w = C₂ *
      ((Complex.Gamma (d - π * w))⁻¹ * (Complex.Gamma (b + π * w))⁻¹) := by
    intro w; rw [fourier_kern hp₂]
    congr 4 <;> simp only [hp₂d, hζ₂d] <;> push_cast <;> ring
  set g : ℝ → ℂ := fun x => (Complex.Gamma (b + x))⁻¹ * (Complex.Gamma (d - x))⁻¹ with hgd
  have hg : Integrable g := integrable_recip_Gamma_mul_recip_Gamma (by simp; linarith)
  set G : ℝ → ℂ := fun ξ => g (π * ξ) with hGd
  have hG : Integrable G := hg.comp_mul_left' Real.pi_ne_zero
  have hFG : 𝓕 (kern p₂ ζ₂) = fun ξ => C₂ * G ξ := by
    funext ξ; rw [hF2]; simp only [hGd, hgd]; push_cast; ring
  have hF2i : Integrable (𝓕 (kern p₂ ζ₂)) := by rw [hFG]; exact hG.const_mul C₂
  have hGeq : G = fun ξ => C₂⁻¹ * 𝓕 (kern p₂ ζ₂) ξ := by
    funext ξ; rw [hFG]; field_simp
  -- the multiplication formula
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext; simp
  have hmult := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume)
    (ν := volume) (L := innerₗ ℝ) (e := Real.fourierChar) Real.continuous_fourierChar
    continuous_inner (integrable_kern hp₁ ζ₁) hG
  rw [hflip] at hmult
  change ∫ ξ, 𝓕 (kern p₁ ζ₁) ξ • G ξ = ∫ x, kern p₁ ζ₁ x • 𝓕 G x at hmult
  -- the left side
  have hL : ∫ ξ, 𝓕 (kern p₁ ζ₁) ξ • G ξ =
      C₁ * ((π : ℂ)⁻¹ * ∫ t : ℝ, ramanujanIntegrand a b c d t) := by
    have hpt : ∀ ξ : ℝ, 𝓕 (kern p₁ ζ₁) ξ • G ξ =
        C₁ * ramanujanIntegrand a b c d (π * ξ) := by
      intro ξ
      rw [hF1, smul_eq_mul, ramanujanIntegrand_eq_mul]
      simp only [hGd, hgd, one_div, mul_inv]
      push_cast; ring
    simp_rw [hpt]
    rw [integral_const_mul, Measure.integral_comp_mul_left, abs_inv,
      abs_of_pos Real.pi_pos, Complex.real_smul]
    push_cast; ring
  -- the right side
  have hR : ∫ x, kern p₁ ζ₁ x • 𝓕 G x = C₂⁻¹ * ∫ x, kern (p₁ + p₂) (ζ₁ - ζ₂) x := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_real (π / 2)] with x hx
    rw [hGeq, fourier_const_mul, smul_eq_mul]
    by_cases hxo : x ∈ Ioo (-(π / 2)) (π / 2)
    · have hxo' : -x ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hxo.2], by linarith [hxo.1]⟩
      rw [fourier_fourier_kern hp₂ ζ₂ hF2i hxo']
      have hxc : x ∈ Ioc (-(π / 2)) (π / 2) := Ioo_subset_Ioc_self hxo
      have hxc' : -x ∈ Ioc (-(π / 2)) (π / 2) := Ioo_subset_Ioc_self hxo'
      simp only [kern, indicator_of_mem hxc, indicator_of_mem hxc', Real.cos_neg]
      have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hxo
      rw [Real.rpow_add hcos]
      push_cast
      have he : Complex.exp (((ζ₁ : ℂ) - ζ₂) * x * I) =
          Complex.exp ((ζ₁ : ℂ) * x * I) * Complex.exp ((ζ₂ : ℂ) * -(x : ℂ) * I) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [he]
      ring
    · have hxc : x ∉ Ioc (-(π / 2)) (π / 2) := by
        intro h; exact hxo ⟨h.1, lt_of_le_of_ne h.2 hx⟩
      simp only [kern, indicator_of_notMem hxc, zero_mul, mul_zero]
  -- the remaining kernel integral
  have hI : ∫ x, kern (p₁ + p₂) (ζ₁ - ζ₂) x =
      CP * ((Complex.Gamma (b + c - 1))⁻¹ * (Complex.Gamma (a + d - 1))⁻¹) := by
    rw [← fourier_zero_eq_integral, fourier_kern hP]
    congr 4 <;> simp only [hp₁d, hζ₁d, hp₂d, hζ₂d] <;> push_cast <;> ring
  rw [hL, hR, hI] at hmult
  -- solve for the integral
  have hJ : ∫ t : ℝ, ramanujanIntegrand a b c d t =
      π * C₁⁻¹ * C₂⁻¹ * CP * ((Complex.Gamma (b + c - 1))⁻¹ * (Complex.Gamma (a + d - 1))⁻¹) := by
    have := hmult
    field_simp at this ⊢
    linear_combination this
  rw [hJ]
  have g1 : Complex.Gamma (a + c - 1) = Real.Gamma (p₁ + 1) := by
    rw [← Complex.Gamma_ofReal]; congr 1; simp only [hp₁d]; push_cast; ring
  have g2 : Complex.Gamma (b + d - 1) = Real.Gamma (p₂ + 1) := by
    rw [← Complex.Gamma_ofReal]; congr 1; simp only [hp₂d]; push_cast; ring
  have g3 : Complex.Gamma (a + b + c + d - 3) = Real.Gamma (p₁ + p₂ + 1) := by
    rw [← Complex.Gamma_ofReal]; congr 1; simp only [hp₁d, hp₂d]; push_cast; ring
  have hG1 := Real.Gamma_pos_of_pos (show 0 < p₁ + 1 by linarith)
  have hG2 := Real.Gamma_pos_of_pos (show 0 < p₂ + 1 by linarith)
  have h2 : (2 : ℝ) ^ (p₁ + p₂) = 2 ^ p₁ * 2 ^ p₂ := Real.rpow_add (by norm_num) _ _
  rw [g1, g2, g3, hC₁, hC₂, hCP, h2]
  have h2p₁ : (0 : ℝ) < 2 ^ p₁ := by positivity
  have h2p₂ : (0 : ℝ) < 2 ^ p₂ := by positivity
  have c1 : (((2 : ℝ) ^ p₁ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 h2p₁.ne'
  have c2 : (((2 : ℝ) ^ p₂ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 h2p₂.ne'
  push_cast
  field_simp

/-! ### Continuation to complex parameters -/

/-- The right side of 5.13.4. -/
def ramanujanR (a b c d : ℂ) : ℂ :=
  Complex.Gamma (a + b + c + d - 3) /
    (Complex.Gamma (a + c - 1) * Complex.Gamma (a + d - 1) *
      Complex.Gamma (b + c - 1) * Complex.Gamma (b + d - 1))

/-- The right-hand side of 5.13.4 is symmetric in `a` and `b`. -/
theorem ramanujanR_swap (a b c d : ℂ) : ramanujanR a b c d = ramanujanR b a c d := by
  simp only [ramanujanR]; ring_nf

/-- The right-hand side of 5.13.4 is invariant under swapping `(a, b)` with `(c, d)`. -/
theorem ramanujanR_neg (a b c d : ℂ) : ramanujanR a b c d = ramanujanR c d a b := by
  simp only [ramanujanR]; ring_nf

/-- The integral of Ramanujan's integrand is symmetric in `a` and `b`. -/
theorem integral_ramanujanIntegrand_swap (a b c d : ℂ) :
    ∫ t : ℝ, ramanujanIntegrand a b c d t = ∫ t : ℝ, ramanujanIntegrand b a c d t := by
  simp_rw [ramanujanIntegrand_swap a b c d]

/-- The integral of Ramanujan's integrand is invariant under swapping `(a, b)` with `(c, d)`. -/
theorem integral_ramanujanIntegrand_neg (a b c d : ℂ) :
    ∫ t : ℝ, ramanujanIntegrand a b c d t = ∫ t : ℝ, ramanujanIntegrand c d a b t := by
  rw [← integral_neg_eq_self]; simp_rw [ramanujanIntegrand_neg]

/-- The right-hand side of 5.13.4 is holomorphic in `a` on `Re(a + b + c + d) > 3`. -/
theorem differentiableOn_ramanujanR (b c d : ℂ) :
    DifferentiableOn ℂ (fun a : ℂ => ramanujanR a b c d) {a | 3 < (a + b + c + d).re} := by
  intro a ha
  change 3 < (a + b + c + d).re at ha
  have hg := differentiable_recip_Gamma
  have hΓ : DifferentiableAt ℂ (fun a : ℂ => Complex.Gamma (a + b + c + d - 3)) a := by
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp a (by fun_prop)
    have := congrArg re hm; simp at this
    have : (a + b + c + d).re = a.re + b.re + c.re + d.re := by simp
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have e : (fun a : ℂ => ramanujanR a b c d) = fun a : ℂ => Complex.Gamma (a + b + c + d - 3) *
      ((Complex.Gamma (a + c - 1))⁻¹ * (Complex.Gamma (a + d - 1))⁻¹ *
        (Complex.Gamma (b + c - 1))⁻¹ * (Complex.Gamma (b + d - 1))⁻¹) := by
    funext a; simp only [ramanujanR, div_eq_mul_inv, mul_inv]
  rw [e]
  refine (hΓ.mul ?_).differentiableWithinAt
  exact (((hg.comp (by fun_prop)).mul (hg.comp (by fun_prop))).mul
    (hg.comp (by fun_prop))).mul (hg.comp (by fun_prop)) |>.differentiableAt

/-- Identity theorem on a right half-plane, from agreement on a real half-line. -/
theorem eqOn_of_real_halfline {f g : ℂ → ℂ} {s : ℝ}
    (hf : DifferentiableOn ℂ f {a | s < a.re}) (hg : DifferentiableOn ℂ g {a | s < a.re})
    {x₀ : ℝ} (hx₀ : s ≤ x₀) (hfg : ∀ x : ℝ, x₀ < x → f x = g x) {a : ℂ} (ha : s < a.re) :
    f a = g a := by
  have hU : IsOpen {a : ℂ | s < a.re} := isOpen_lt continuous_const continuous_re
  have hconv : Convex ℝ {a : ℂ | s < a.re} := convex_halfSpace_re_gt s
  have h1 : ((x₀ + 1 : ℝ) : ℂ) ∈ {a : ℂ | s < a.re} := by simp; linarith
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (z₀ := ((x₀ + 1 : ℝ) : ℂ))
    (hf.analyticOnNhd hU) (hg.analyticOnNhd hU) hconv.isPreconnected h1 ?_ ha
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] (x₀ + 1), f x = g x := by
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds (show x₀ < x₀ + 1 by linarith))] with x hx
    exact hfg x hx
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (x₀ + 1)) (𝓝[≠] ((x₀ + 1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx h =>
      hx (Complex.ofReal_injective h)
  exact ht.frequently hev.frequently

/-- `{a | 3 < Re(a + k)} = {a | 3 - Re k < Re a}`. -/
theorem halfplane_eq (k : ℂ) : {a : ℂ | 3 < (a + k).re} = {a : ℂ | 3 - k.re < a.re} := by
  ext a
  change 3 < (a + k).re ↔ 3 - k.re < a.re
  rw [add_re]; constructor <;> intro h <;> linarith

/-- One continuation step in the first parameter. -/
theorem ramanujan_step (b c d : ℂ) {x₀ : ℝ} (hx₀ : 3 - (b + c + d).re ≤ x₀)
    (h : ∀ x : ℝ, x₀ < x →
      ∫ t : ℝ, ramanujanIntegrand x b c d t = ramanujanR x b c d)
    {a : ℂ} (ha : 3 < (a + b + c + d).re) :
    ∫ t : ℝ, ramanujanIntegrand a b c d t = ramanujanR a b c d := by
  have e : ∀ a : ℂ, a + b + c + d = a + (b + c + d) := fun a => by ring
  have hset : {a : ℂ | 3 < (a + b + c + d).re} = {a : ℂ | 3 - (b + c + d).re < a.re} := by
    simp_rw [e]; exact halfplane_eq _
  have hf := differentiableOn_integral_ramanujanIntegrand b c d
  have hg := differentiableOn_ramanujanR b c d
  rw [hset] at hf hg
  refine eqOn_of_real_halfline hf hg hx₀ h ?_
  rw [e, add_re] at ha; linarith

end RamanujanAux

open RamanujanAux

/-- DLMF 5.13.4, Ramanujan's integral: `∫ dt / (Γ(a + t) Γ(b + t) Γ(c - t) Γ(d - t)) = Γ(a + b + c +
d - 3) / (Γ(a + c - 1) Γ(a + d - 1) Γ(b + c - 1) Γ(b + d - 1))` for `Re(a + b + c + d) > 3`. -/
@[dlmf 5.13.E4]
theorem mellin_barnes_recip_four {a b c d : ℂ}
    (h : 3 < (a + b + c + d).re) :
    ∫ t : ℝ, 1 /
        (Complex.Gamma (a + t) * Complex.Gamma (b + t) *
          Complex.Gamma (c - t) * Complex.Gamma (d - t)) =
      Complex.Gamma (a + b + c + d - 3) /
        (Complex.Gamma (a + c - 1) * Complex.Gamma (a + d - 1) *
          Complex.Gamma (b + c - 1) * Complex.Gamma (b + d - 1)) := by
  change ∫ t : ℝ, ramanujanIntegrand a b c d t = ramanujanR a b c d
  -- step 1: complex `a`, real `b, c, d` with `b + d > 2`
  have S1 : ∀ (a : ℂ) (b c d : ℝ), 2 < b + d → 3 < (a + b + c + d).re →
      ∫ t : ℝ, ramanujanIntegrand a b c d t = ramanujanR a b c d := by
    intro a b c d hbd ha
    refine ramanujan_step (b : ℂ) c d (x₀ := max (1 - c) (3 - (b + c + d))) ?_ (fun x hx => ?_) ha
    · simp
    · have hx1 : 1 - c < x := lt_of_le_of_lt (le_max_left _ _) hx
      exact integral_ramanujanIntegrand_of_real (by linarith) hbd
  -- step 2: complex `a, b`, real `c, d`
  have S2 : ∀ (a b : ℂ) (c d : ℝ), 3 < (a + b + c + d).re →
      ∫ t : ℝ, ramanujanIntegrand a b c d t = ramanujanR a b c d := by
    intro a b c d hab
    rw [integral_ramanujanIntegrand_swap, ramanujanR_swap]
    refine ramanujan_step a c d (x₀ := max (2 - d) (3 - (a + c + d).re)) ?_ (fun x hx => ?_)
      (by rw [show b + a + c + d = a + b + c + d by ring]; exact hab)
    · simp
    · rw [integral_ramanujanIntegrand_swap, ramanujanR_swap]
      have hx1 : 2 - d < x := lt_of_le_of_lt (le_max_left _ _) hx
      have hx2 : 3 - (a + c + d).re < x := lt_of_le_of_lt (le_max_right _ _) hx
      exact S1 a x c d (by linarith) (by simp at hx2 ⊢; linarith)
  -- step 3: complex `a, b, c`, real `d`
  have S3 : ∀ (a b c : ℂ) (d : ℝ), 3 < (a + b + c + d).re →
      ∫ t : ℝ, ramanujanIntegrand a b c d t = ramanujanR a b c d := by
    intro a b c d habc
    rw [integral_ramanujanIntegrand_neg, ramanujanR_neg]
    refine ramanujan_step (d : ℂ) a b (x₀ := 3 - (d + a + b).re) le_rfl (fun x hx => ?_)
      (by rw [show c + d + a + b = a + b + c + d by ring]; exact habc)
    rw [← integral_ramanujanIntegrand_neg, ← ramanujanR_neg]
    exact S2 a b x d (by simp at hx ⊢; linarith)
  -- step 4: all complex
  rw [integral_ramanujanIntegrand_neg, integral_ramanujanIntegrand_swap, ramanujanR_neg,
    ramanujanR_swap]
  refine ramanujan_step c a b (x₀ := 3 - (c + a + b).re) le_rfl (fun x hx => ?_)
    (by rw [show d + c + a + b = a + b + c + d by ring]; exact h)
  rw [← integral_ramanujanIntegrand_swap, ← ramanujanR_swap, ← integral_ramanujanIntegrand_neg,
    ← ramanujanR_neg]
  exact S3 a b c x (by simp at hx ⊢; linarith)

end Ramanujan

/-- DLMF 5.13.5, de Branges–Wilson integral: `(1/4π) ∫ ∏ₖ Γ(aₖ ± it) / Γ(±2it) dt = ∏_{j<k} Γ(aⱼ +
aₖ) / Γ(a₁ + a₂ + a₃ + a₄)` for positive real parts. -/
@[dlmf 5.13.E5]
theorem mellin_barnes_selberg {a : Fin 4 → ℂ} (ha : ∀ k, 0 < (a k).re) :
    (1 / (4 * π)) * ∫ t : ℝ,
        (∏ k : Fin 4, Complex.Gamma (a k + I * t) * Complex.Gamma (a k - I * t)) /
          (Complex.Gamma (2 * I * t) * Complex.Gamma (-2 * I * t)) =
      (∏ j : Fin 4, ∏ k : Fin 4, if j.val < k.val then Complex.Gamma (a j + a k) else 1) /
        Complex.Gamma (∑ k : Fin 4, a k) := by
  sorry

/-- `∑ 1/(2j+1)² = π²/8`. -/
theorem hasSum_one_div_odd_sq :
    HasSum (fun j : ℕ => (1 : ℝ) / (2 * j + 1) ^ 2) (π ^ 2 / 8) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hf
  have h : HasSum f (π ^ 2 / 6) := hasSum_zeta_two
  have he : HasSum (fun j : ℕ => f (2 * j)) (π ^ 2 / 24) := by
    have := h.div_const 4
    rw [show π ^ 2 / 6 / 4 = π ^ 2 / 24 by ring] at this
    refine this.congr_fun fun j => ?_
    simp only [hf]; push_cast
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      field_simp; ring
  have hinj : Function.Injective fun j : ℕ => 2 * j + 1 := fun a b h => by
    simp only at h; omega
  have ho : HasSum (fun j : ℕ => f (2 * j + 1)) (∑' j : ℕ, f (2 * j + 1)) :=
    (h.summable.comp_injective hinj).hasSum
  have hval := h.unique (HasSum.even_add_odd (f := f) he ho)
  have ho' : ∑' j : ℕ, f (2 * j + 1) = π ^ 2 / 8 := by linarith
  rw [ho'] at ho
  refine ho.congr_fun fun j => ?_
  simp only [hf]; push_cast; ring

/-- Tail of the trigamma series. -/
theorem tendsto_trigamma_nat_add_one :
    Tendsto (fun k : ℕ => Real.trigamma (k + 1)) atTop (𝓝 0) := by
  have hs : Summable fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [one_div] using this
  refine (tendsto_sum_nat_add fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2).congr fun k => ?_
  rw [Real.trigamma_eq_tsum (by positivity)]
  congr 1; funext n; push_cast; ring_nf

/-- Consecutive trigamma values differ by `1/(k+1)²`. -/
theorem trigamma_succ_sub (k : ℕ) :
    Real.trigamma ((k : ℝ) + 1) - Real.trigamma (((k + 1 : ℕ) : ℝ) + 1) =
      1 / ((k : ℝ) + 1) ^ 2 := by
  have h := trigamma_add_one (x := (k : ℝ) + 1) (by positivity)
  push_cast
  rw [h]; field_simp; ring

/-- Even partial sums of the alternating trigamma series. -/
theorem sum_alternating_trigamma_even (M : ℕ) :
    ∑ k ∈ Finset.range (2 * M), (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1) =
      -∑ j ∈ Finset.range M, (1 : ℝ) / (2 * j + 1) ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have hd := trigamma_succ_sub (2 * M)
    have e1 : (-1 : ℝ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e2 : (-1 : ℝ) ^ (2 * M + 1 + 1) = 1 := by rw [pow_succ, e1]; norm_num
    rw [e1, e2]
    push_cast at hd ⊢
    linear_combination -hd

/-- Odd partial sums of the alternating trigamma series. -/
theorem sum_alternating_trigamma_odd (M : ℕ) :
    ∑ k ∈ Finset.range (2 * M + 1), (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1) =
      -∑ j ∈ Finset.range M, (1 : ℝ) / (2 * j + 1) ^ 2 - Real.trigamma ((2 * M : ℕ) + 1) := by
  rw [Finset.sum_range_succ, sum_alternating_trigamma_even]
  have e1 : (-1 : ℝ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [e1]; push_cast; ring

/-- The alternating trigamma series. It converges only conditionally, so it is stated with
ordered partial sums; Lean's unordered `tsum` of the series would be `0`. -/
@[dlmf 5.16.E1]
theorem sum_alternating_trigamma :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1))
      Filter.atTop (nhds (-π ^ 2 / 8)) := by
  set A : ℕ → ℝ := fun M => ∑ j ∈ Finset.range M, (1 : ℝ) / (2 * j + 1) ^ 2
  set E : ℕ → ℝ := fun N => if Even N then 0 else Real.trigamma (((N - 1 : ℕ) : ℝ) + 1)
  have hform : ∀ N, ∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1) =
      -A (N / 2) - E N := by
    intro N
    obtain ⟨M, rfl | rfl⟩ := Nat.even_or_odd' N
    · rw [sum_alternating_trigamma_even]
      simp [A, E, show 2 * M / 2 = M by omega]
    · rw [sum_alternating_trigamma_odd]
      simp [A, E, show (2 * M + 1) / 2 = M by omega, Nat.not_even_bit1]
  simp_rw [hform]
  have hA : Tendsto (fun N => A (N / 2)) atTop (𝓝 (π ^ 2 / 8)) :=
    hasSum_one_div_odd_sq.tendsto_sum_nat.comp (Nat.tendsto_div_const_atTop two_ne_zero)
  have hT : Tendsto (fun N : ℕ => Real.trigamma (((N - 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_trigamma_nat_add_one.comp (tendsto_sub_atTop_nat 1)
  have hE : Tendsto E atTop (𝓝 0) := by
    refine squeeze_zero (fun N => ?_) (fun N => ?_) hT
    · simp only [E]; split_ifs
      · exact le_rfl
      · rw [Real.trigamma_eq_tsum (by positivity)]; positivity
    · simp only [E]; split_ifs
      · rw [Real.trigamma_eq_tsum (by positivity)]; positivity
      · exact le_rfl
  have := (hA.neg).sub hE
  simpa [neg_div] using this

section SumTrigamma

open Finset
open scoped ENNReal

/-- `ψ'(k+2) ≤ 1/(k+1)`, by comparison with a telescoping series. -/
theorem trigamma_add_two_le (k : ℕ) : Real.trigamma (k + 2) ≤ 1 / (k + 1) := by
  rw [Real.trigamma_eq_tsum (by positivity)]
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun N => ?_
  have h := Real.sum_recip_sub_recip_range ((k : ℝ) + 1) N
  have hle : ∀ n ∈ range N, ((k : ℝ) + 2 + n)⁻¹ ^ 2 ≤
      ((k : ℝ) + 1 + n)⁻¹ - ((k : ℝ) + 1 + n + 1)⁻¹ := by
    intro n _
    have h1 : (0 : ℝ) < k + 1 + n := by positivity
    rw [show (k : ℝ) + 1 + n + 1 = k + 2 + n by ring, inv_pow, inv_sub_inv h1.ne' (by positivity),
      show (k : ℝ) + 2 + n - (k + 1 + n) = 1 by ring]
    rw [one_div]
    exact inv_anti₀ (by positivity) (by nlinarith)
  refine (sum_le_sum hle).trans ?_
  rw [h, one_div]
  have : (0 : ℝ) ≤ ((k : ℝ) + 1 + N)⁻¹ := by positivity
  linarith

/-- Row sums of the double series for 5.16.2: `∑_q 1/((p+1)(p+q+2)²) = ψ'(p+2)/(p+1)`. -/
private lemma sumTrigamma_row (p : ℕ) :
    ∑' q : ℕ, ENNReal.ofReal (1 / ((p + 1 : ℝ) * ((p : ℝ) + q + 2) ^ 2)) =
      ENNReal.ofReal ((1 / (p + 1 : ℝ)) * Real.trigamma (p + 2)) := by
  have hS := Real.summable_trigamma (by positivity : (0 : ℝ) < p + 2)
  rw [show (fun q : ℕ => ENNReal.ofReal (1 / ((p + 1 : ℝ) * ((p : ℝ) + q + 2) ^ 2))) =
      fun q : ℕ => ENNReal.ofReal (1 / (p + 1 : ℝ)) *
      ENNReal.ofReal (((p : ℝ) + 2 + q)⁻¹ ^ 2) by
    funext q; rw [← ENNReal.ofReal_mul (by positivity)]; congr 1
    field_simp; ring_nf,
    ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hS,
    ← ENNReal.ofReal_mul (by positivity), ← Real.trigamma_eq_tsum (by positivity)]

/-- Column sums of the double series for 5.16.2:
`∑_q 1/((p+1)(q+1)(p+q+2)) = ∑_{j≤p} 1/((j+1)(p+1)²)`. -/
private lemma sumTrigamma_col (p : ℕ) :
    ∑' q : ℕ, ENNReal.ofReal (1 / ((p + 1 : ℝ) * (q + 1) * ((p : ℝ) + q + 2))) =
      ∑ j ∈ range (p + 1), ENNReal.ofReal (1 / ((j + 1 : ℝ) * (p + 1) ^ 2)) := by
  have hx : (0 : ℝ) < p + 2 := by positivity
  have hT : ∑' n, Real.digammaSeriesTerm ((p : ℝ) + 2) n =
      ∑ j ∈ range (p + 1), 1 / (j + 1 : ℝ) := by
    have h1 := Real.digamma_eq_tsum hx
    have h2 := Real.digamma_nat_add_one (p + 1)
    rw [show ((p + 1 : ℕ) : ℝ) + 1 = (p : ℝ) + 2 by push_cast; ring, h1] at h2
    rw [show ∑ j ∈ range (p + 1), 1 / (j + 1 : ℝ) = (harmonic (p + 1) : ℝ) by
      simp [harmonic]]
    linarith
  have hD0 : ∀ n, 0 ≤ Real.digammaSeriesTerm ((p : ℝ) + 2) n := fun n => by
    simp only [Real.digammaSeriesTerm]
    rw [sub_nonneg]
    exact inv_anti₀ (by positivity) (by linarith)
  rw [show (fun q : ℕ => ENNReal.ofReal (1 / ((p + 1 : ℝ) * (q + 1) * ((p : ℝ) + q + 2)))) =
      fun q : ℕ => ENNReal.ofReal (1 / (p + 1 : ℝ) ^ 2) *
      ENNReal.ofReal (Real.digammaSeriesTerm ((p : ℝ) + 2) q) by
    funext q; rw [← ENNReal.ofReal_mul (by positivity)]; congr 1
    simp only [Real.digammaSeriesTerm]
    field_simp; ring,
    ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg hD0
      (Real.summable_digammaSeriesTerm hx), hT, ← ENNReal.ofReal_mul (by positivity),
    mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  refine sum_congr rfl fun j _ => ?_
  congr 1; field_simp

/-- After the triangular interchange: `∑_{p≥j} 1/((j+1)(p+1)²) = 1/(j+1)³ + ψ'(j+2)/(j+1)`. -/
private lemma sumTrigamma_tri (j : ℕ) :
    ∑' p : ℕ, (if j ≤ p then ENNReal.ofReal (1 / ((j + 1 : ℝ) * (p + 1) ^ 2)) else 0) =
      ENNReal.ofReal (1 / ((j : ℝ) + 1) ^ 3) +
        ENNReal.ofReal ((1 / (j + 1 : ℝ)) * Real.trigamma (j + 2)) := by
  have ha0 : 0 ≤ (1 / (j + 1 : ℝ)) * Real.trigamma (j + 2) := by
    rw [Real.trigamma_eq_tsum (by positivity)]; positivity
  rw [← Summable.sum_add_tsum_nat_add' (f := fun p : ℕ =>
    if j ≤ p then ENNReal.ofReal (1 / ((j + 1 : ℝ) * (p + 1) ^ 2)) else 0) (k := j)
    ENNReal.summable, sum_eq_zero fun i hi => by simp [show ¬ j ≤ i by simpa using hi],
    zero_add]
  simp only [le_add_iff_nonneg_left, zero_le, ite_true]
  rw [show (fun i : ℕ => ENNReal.ofReal (1 / ((j + 1 : ℝ) * (((i + j : ℕ) : ℝ) + 1) ^ 2))) =
      fun i : ℕ => ENNReal.ofReal (1 / (j + 1 : ℝ)) *
      ENNReal.ofReal (((j : ℝ) + 1 + i)⁻¹ ^ 2) by
    funext i; rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; push_cast
    field_simp; ring,
    ENNReal.tsum_mul_left, tsum_eq_zero_add' ENNReal.summable]
  have hS := Real.summable_trigamma (by positivity : (0 : ℝ) < j + 2)
  rw [show (fun i : ℕ => ENNReal.ofReal (((j : ℝ) + 1 + ((i + 1 : ℕ) : ℝ))⁻¹ ^ 2)) =
      fun i : ℕ => ENNReal.ofReal (((j : ℝ) + 2 + i)⁻¹ ^ 2) by
    funext i; push_cast; ring_nf,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hS,
    ← Real.trigamma_eq_tsum (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by rw [Real.trigamma_eq_tsum (by positivity)]; positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) ha0]
  congr 1
  push_cast
  field_simp
  ring

/-- DLMF 5.16.2: `∑_{k≥1} ψ'(k + 1)/k = ζ(3)`. -/
@[dlmf 5.16.E2]
theorem sum_trigamma_div :
    ∑' k : ℕ, (1 / (k + 1 : ℝ)) * Real.trigamma (k + 2) = (riemannZeta 3).re := by
  -- the summand and its ENNReal sum `L`
  set a : ℕ → ℝ := fun k => (1 / (k + 1 : ℝ)) * Real.trigamma (k + 2) with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    simp only [ha]; rw [Real.trigamma_eq_tsum (by positivity)]; positivity
  have haS : Summable a := by
    refine Summable.of_nonneg_of_le ha0 (fun k => ?_)
      ((Real.summable_one_div_nat_add_rpow 1 2).mpr one_lt_two)
    simp only [ha]
    calc (1 / (k + 1 : ℝ)) * Real.trigamma (k + 2) ≤ (1 / (k + 1)) * (1 / (k + 1)) :=
          mul_le_mul_of_nonneg_left (trigamma_add_two_le k) (by positivity)
      _ = 1 / |(k : ℝ) + 1| ^ (2 : ℝ) := by
          rw [abs_of_pos (by positivity), Real.rpow_two]; field_simp
  set L : ℝ≥0∞ := ∑' k, ENNReal.ofReal (a k) with hL
  -- ζ(3) as a real series
  set z : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) ^ 3 with hz
  have hzS : Summable z := by
    refine ((Real.summable_one_div_nat_add_rpow 1 3).mpr (by norm_num)).congr fun j => ?_
    simp only [hz]; rw [abs_of_pos (by positivity)]; norm_cast
  have hzeta : (riemannZeta 3).re = ∑' j, z j := by
    rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num,
      zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num)]
    simp only [cpow_natCast]
    rw [show (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ 3) = fun n => ((z n : ℝ) : ℂ) by
      funext n; simp [hz], ← ofReal_tsum, ofReal_re]
  -- the double series over `(p, q)` of `f p q = 1/((p+1)(q+1)(p+q+2))`
  set g : ℕ → ℕ → ℝ := fun p q => 1 / ((p + 1 : ℝ) * ((p : ℝ) + q + 2) ^ 2) with hg
  set f : ℕ → ℕ → ℝ := fun p q => 1 / ((p + 1 : ℝ) * (q + 1) * ((p : ℝ) + q + 2)) with hf
  have hfg : ∀ p q, ENNReal.ofReal (f p q) = ENNReal.ofReal (g p q) + ENNReal.ofReal (g q p) := by
    intro p q
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp only [hf, hg]
    field_simp
    ring
  -- symmetry: the double sum is `2 L`
  have hrow : ∀ p : ℕ, ∑' q, ENNReal.ofReal (g p q) = ENNReal.ofReal (a p) :=
    sumTrigamma_row
  have hsym : ∑' p, ∑' q, ENNReal.ofReal (f p q) = 2 * L := by
    simp_rw [hfg, ENNReal.tsum_add]
    rw [ENNReal.tsum_comm (f := fun p q => ENNReal.ofReal (g q p))]
    simp_rw [hrow]
    rw [hL, two_mul]
  -- summing over `q` first gives harmonic numbers
  set c : ℕ → ℕ → ℝ≥0∞ := fun j p => ENNReal.ofReal (1 / ((j + 1 : ℝ) * (p + 1) ^ 2)) with hc
  have hcol : ∀ p : ℕ, ∑' q, ENNReal.ofReal (f p q) = ∑ j ∈ range (p + 1), c j p :=
    sumTrigamma_col
  -- the triangular interchange gives `ζ(3) + L`
  have hrow2 : ∀ j : ℕ, ∑' p, (if j ≤ p then c j p else 0) =
      ENNReal.ofReal (z j) + ENNReal.ofReal (a j) :=
    sumTrigamma_tri
  have htri : ∑' p, ∑' q, ENNReal.ofReal (f p q) = ENNReal.ofReal (∑' j, z j) + L := by
    have h1 : ∀ p, ∑ j ∈ range (p + 1), c j p = ∑' j, (if j ≤ p then c j p else 0) := by
      intro p
      rw [tsum_eq_sum (s := range (p + 1)) fun j hj => by
        simp only [mem_range, not_lt] at hj; simp [show ¬ j ≤ p by omega]]
      exact sum_congr rfl fun j hj => by
        simp only [mem_range] at hj; simp [show j ≤ p by omega]
    simp_rw [hcol, h1]
    rw [ENNReal.tsum_comm]
    simp_rw [hrow2]
    rw [ENNReal.tsum_add, ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hzS]
  -- conclude
  have hLfin : L = ENNReal.ofReal (∑' k, a k) := (ENNReal.ofReal_tsum_of_nonneg ha0 haS).symm
  have hLne : L ≠ ∞ := by rw [hLfin]; exact ENNReal.ofReal_ne_top
  have hEq : L = ENNReal.ofReal (∑' j, z j) := by
    have := hsym.symm.trans htri
    rw [two_mul] at this
    exact (ENNReal.add_left_inj hLne).mp this
  rw [hzeta]
  have hz0 : 0 ≤ ∑' j, z j := tsum_nonneg fun j => by positivity
  rw [hLfin] at hEq
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg ha0) hz0).mp hEq

end SumTrigamma

end DLMF.Gamma

end
end
