/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric

/-!
# Integral identities among `R_F`, `R_D`, `R_G` (DLMF §19.21(ii)), at the integral level

Round-1 helpers (prefix `p19sR1_`). The relations (19.21.7)–(19.21.11) between the defining
integrals (19.16.1), (19.16.5), (19.16.2_5) follow from exact antiderivatives of the form
`(α t + β)/s(t)`, `s(t) = √(t + x) √(t + y) √(t + z)` (`p19sR1_integral_eq_of_lin`), or from
pointwise identities of the integrands. Where possible one variable may be `0` (DLMF's boundary
case), which gives the complete cases (19.21.2), (19.21.3).
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- **FTC for `(α t + β)/s(t)`.** If `f` is integrable on `(0, ∞)` and is, for `t > 0`, the
derivative of `h(t) = (α t + β) s(t)⁻¹` (written out with `u = √(t + x)` etc.), then
`∫₀^∞ f = -β/s(0)`. Here `x` is admissible, `y, z` lie in the slit plane, and `β = 0` if
`x = 0`. -/
lemma p19sR1_integral_eq_of_lin {x y z α β : ℂ} (hx : x ∈ slitPlane ∨ x = 0)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hβ : x = 0 → β = 0) {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ioi 0))
    (hfe : ∀ t : ℝ, 0 < t → f t =
      α * (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
          ((t : ℂ) + z) ^ (1 / 2 : ℂ))⁻¹ +
        ((t : ℂ) * α + β) *
          (-((((t : ℂ) + x) ^ (1 / 2 : ℂ) / (2 * ((t : ℂ) + x)) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) +
                ((t : ℂ) + x) ^ (1 / 2 : ℂ) * (((t : ℂ) + y) ^ (1 / 2 : ℂ) / (2 * ((t : ℂ) + y)))) *
              ((t : ℂ) + z) ^ (1 / 2 : ℂ) +
            ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
              (((t : ℂ) + z) ^ (1 / 2 : ℂ) / (2 * ((t : ℂ) + z)))) /
          (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
            ((t : ℂ) + z) ^ (1 / 2 : ℂ)) ^ 2)) :
    ∫ t in Ioi (0 : ℝ), f t = -(β * (x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ))⁻¹) := by
  set S : ℝ → ℂ := fun t => ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
    ((t : ℂ) + z) ^ (1 / 2 : ℂ) with hS
  set h : ℝ → ℂ := fun t => ((t : ℂ) * α + β) * (S t)⁻¹ with hh
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt h (f t) t := by
    intro t ht
    have hx' := p19sR1_add_mem_slitPlane ht hx
    have hy' := p19sR1_add_mem_slitPlane ht (Or.inl hy)
    have hz' := p19sR1_add_mem_slitPlane ht (Or.inl hz)
    have hs := ((p19sR1_hasDerivAt_cpow_half hx').mul (p19sR1_hasDerivAt_cpow_half hy')).mul
      (p19sR1_hasDerivAt_cpow_half hz')
    have hu0 := p19sR1_cpow_half_ne_zero ht hx
    have hv0 := p19sR1_cpow_half_ne_zero ht (Or.inl hy)
    have hw0 := p19sR1_cpow_half_ne_zero ht (Or.inl hz)
    have hinv := hs.inv (mul_ne_zero (mul_ne_zero hu0 hv0) hw0)
    have hp : HasDerivAt (fun s : ℝ => (s : ℂ) * α + β) (1 * α) t :=
      ((hasDerivAt_id (t : ℂ)).comp_ofReal.mul_const α).add_const β
    have := hp.mul hinv
    rw [one_mul] at this
    convert this using 1
    rw [hfe t ht]
    simp only [Pi.mul_apply, Pi.inv_apply]
  obtain ⟨C, hC⟩ := p19sR1_norm_inv_s_le hx hy hz
  have hC0 : 0 ≤ C := by
    have := hC 1 one_pos
    have h2 : 0 < (Real.sqrt 1 * (1 + 1))⁻¹ := by positivity
    by_contra hneg; push Not at hneg
    have : C * (Real.sqrt 1 * (1 + 1))⁻¹ < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [norm_nonneg (S 1)⁻¹]
  have hbound : ∀ t : ℝ, 0 < t → ‖h t‖ ≤ (‖α‖ + ‖β‖) * C * (Real.sqrt t)⁻¹ := by
    intro t ht
    have h1 := hC t ht
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hpoly : ‖(t : ℂ) * α + β‖ ≤ (‖α‖ + ‖β‖) * (t + 1) := by
      calc _ ≤ ‖(t : ℂ) * α‖ + ‖β‖ := norm_add_le _ _
        _ = t * ‖α‖ + ‖β‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
        _ ≤ _ := by nlinarith [norm_nonneg α, norm_nonneg β]
    simp only [hh]
    rw [norm_mul]
    calc _ ≤ (‖α‖ + ‖β‖) * (t + 1) * (C * (Real.sqrt t * (t + 1))⁻¹) :=
          mul_le_mul hpoly h1 (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hlim : Tendsto h atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t => (‖α‖ + ‖β‖) * C * (Real.sqrt t)⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with t ht using hbound t ht
    · simpa using (Real.tendsto_sqrt_atTop.inv_tendsto_atTop).const_mul ((‖α‖ + ‖β‖) * C)
  have hcont : ContinuousWithinAt h (Ici 0) 0 := by
    rcases hx with hx | rfl
    · refine ContinuousAt.continuousWithinAt ?_
      have h0 : ∀ w : ℂ, w ∈ slitPlane → ((0 : ℝ) : ℂ) + w ∈ slitPlane := fun w hw => by simpa
      refine ((((continuous_ofReal.mul continuous_const).add continuous_const).continuousAt).mul
        ((((p19sR1_continuousAt_cpow_half (h0 x hx)).mul
          (p19sR1_continuousAt_cpow_half (h0 y hy))).mul
          (p19sR1_continuousAt_cpow_half (h0 z hz))).inv₀ ?_))
      exact mul_ne_zero (mul_ne_zero (p19sR1_cpow_half_ne_zero_of_mem (h0 x hx))
        (p19sR1_cpow_half_ne_zero_of_mem (h0 y hy))) (p19sR1_cpow_half_ne_zero_of_mem (h0 z hz))
    · obtain rfl := hβ rfl
      have h00 : h 0 = 0 := by simp [hh]
      rw [ContinuousWithinAt, h00]
      have hb0 : ∀ t ∈ Ici (0 : ℝ), ‖h t‖ ≤ ‖α‖ * C * Real.sqrt t := by
        intro t ht
        rcases (mem_Ici.mp ht).eq_or_lt with rfl | ht
        · rw [h00, norm_zero]; positivity
        · have h1 := hC t ht
          have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
          simp only [hh, add_zero]
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
          calc _ ≤ t * ‖α‖ * (C * (Real.sqrt t * (t + 1))⁻¹) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = ‖α‖ * C * (t / Real.sqrt t) * (t + 1)⁻¹ := by rw [mul_inv]; ring
            _ = ‖α‖ * C * Real.sqrt t * (t + 1)⁻¹ := by rw [Real.div_sqrt]
            _ ≤ _ := by
                have : (t + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
                have : 0 ≤ ‖α‖ * C * Real.sqrt t := by positivity
                nlinarith
      refine squeeze_zero_norm' (a := fun t => ‖α‖ * C * Real.sqrt t) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with t ht using hb0 t ht
      · have : Tendsto (fun t : ℝ => ‖α‖ * C * Real.sqrt t) (𝓝 0) (𝓝 (‖α‖ * C * Real.sqrt 0)) :=
          (Real.continuous_sqrt.tendsto 0).const_mul _
        rw [Real.sqrt_zero, mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hf hlim]
  simp [hh, hS]

/-- The derivative of `(α t + β)/s` in terms of `u = √(t + x)` etc. (as in
`p19sR1_integral_eq_of_lin`). -/
abbrev p19sR1_linDeriv (t u v w x y z α β : ℂ) : ℂ :=
  α * (u * v * w)⁻¹ + (t * α + β) *
      (-((u / (2 * (t + x)) * v + u * (v / (2 * (t + y)))) * w + u * v * (w / (2 * (t + z)))) /
        (u * v * w) ^ 2)

/-- Identity under the stated parameter and domain assumptions: `(3 / 2) * (x * (u * v * w * (t +
x))⁻¹ + y * (u * v * w * (t + y))⁻¹ + z * (u * v * w * (t + z))⁻¹ - (u * v * w)⁻¹) =
p19sR1_linDeriv t u v w x y z 3 0`. -/
lemma p19sR1_alg9 (t u v w x y z : ℂ) (hu : u ^ 2 = t + x) (hv : v ^ 2 = t + y)
    (hw : w ^ 2 = t + z) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    (3 / 2) * (x * (u * v * w * (t + x))⁻¹ + y * (u * v * w * (t + y))⁻¹ +
      z * (u * v * w * (t + z))⁻¹ - (u * v * w)⁻¹) = p19sR1_linDeriv t u v w x y z 3 0 := by
  obtain rfl : x = u ^ 2 - t := by linear_combination -hu
  obtain rfl : y = v ^ 2 - t := by linear_combination -hv
  obtain rfl : z = w ^ 2 - t := by linear_combination -hw
  simp only [add_sub_cancel, p19sR1_linDeriv]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `(3 / 2) * ((u * v * w * (t +
x))⁻¹ + (u * v * w * (t + y))⁻¹ + (u * v * w * (t + z))⁻¹) = p19sR1_linDeriv t u v w x y z 0
(-3)`. -/
lemma p19sR1_alg8 (t u v w x y z : ℂ) (hu : u ^ 2 = t + x) (hv : v ^ 2 = t + y)
    (hw : w ^ 2 = t + z) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    (3 / 2) * ((u * v * w * (t + x))⁻¹ + (u * v * w * (t + y))⁻¹ +
      (u * v * w * (t + z))⁻¹) = p19sR1_linDeriv t u v w x y z 0 (-3) := by
  obtain rfl : x = u ^ 2 - t := by linear_combination -hu
  obtain rfl : y = v ^ 2 - t := by linear_combination -hv
  obtain rfl : z = w ^ 2 - t := by linear_combination -hw
  simp only [add_sub_cancel, p19sR1_linDeriv]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `(3 / 2) * ((x - y) * (u * v * w *
(t + x))⁻¹ + (z - y) * (u * v * w * (t + z))⁻¹ - (u * v * w)⁻¹) = p19sR1_linDeriv t u v w x y
z 3 (3 * y)`. -/
lemma p19sR1_alg7 (t u v w x y z : ℂ) (hu : u ^ 2 = t + x) (hv : v ^ 2 = t + y)
    (hw : w ^ 2 = t + z) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    (3 / 2) * ((x - y) * (u * v * w * (t + x))⁻¹ + (z - y) * (u * v * w * (t + z))⁻¹ -
      (u * v * w)⁻¹) = p19sR1_linDeriv t u v w x y z 3 (3 * y) := by
  obtain rfl : x = u ^ 2 - t := by linear_combination -hu
  obtain rfl : y = v ^ 2 - t := by linear_combination -hv
  obtain rfl : z = w ^ 2 - t := by linear_combination -hw
  simp only [add_sub_cancel, p19sR1_linDeriv]
  field_simp
  ring

/-- An admissible argument is not a negative real. -/
lemma p19sR1_not_isNegReal {x : ℂ} (hx : SymEllIntArg x) : ¬ IsNegReal x := by
  rcases hx with hx | rfl
  · exact ei19c_not_isNegReal_of_mem_slitPlane hx
  · simp [IsNegReal]

/-- `R_D(y, z, x)` as `(3/2) ∫ (s(t) (t + x))⁻¹` with `s` written in the order `x, y, z`. -/
lemma p19sR1_symEllIntRD_perm1 (x y z : ℂ) (hx : SymEllIntArg x) :
    symEllIntRD y z x = (3 / 2) * ∫ t in Ioi (0 : ℝ), (((t : ℂ) + x) ^ (1 / 2 : ℂ) *
      ((t : ℂ) + y) ^ (1 / 2 : ℂ) * ((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + x))⁻¹ := by
  rw [symEllIntRD_eq_integral (p19sR1_not_isNegReal hx)]
  congr 2; funext t; simp only [symEllIntS]; ring_nf

/-- `R_D(z, x, y)` as `(3/2) ∫ (s(t) (t + y))⁻¹` with `s` written in the order `x, y, z`. -/
lemma p19sR1_symEllIntRD_perm2 (x y z : ℂ) (hy : SymEllIntArg y) :
    symEllIntRD z x y = (3 / 2) * ∫ t in Ioi (0 : ℝ), (((t : ℂ) + x) ^ (1 / 2 : ℂ) *
      ((t : ℂ) + y) ^ (1 / 2 : ℂ) * ((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹ := by
  rw [symEllIntRD_eq_integral (p19sR1_not_isNegReal hy)]
  congr 2; funext t; simp only [symEllIntS]; ring_nf

/-- DLMF 19.21.9, **stronger than DLMF** in allowing `x = 0`:
`x R_D(y, z, x) + y R_D(z, x, y) + z R_D(x, y, z) = 3 R_F(x, y, z)` for admissible `x` and
`y, z ∈ ℂ \ (-∞, 0]` (at `x = 0` the first term is `0`). -/
@[dlmf 19.21.E9]
theorem p19sR1_symEllIntRD_cyclic_mul_sum {x y z : ℂ} (hx : SymEllIntArg x) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    x * symEllIntRD y z x + y * symEllIntRD z x y + z * symEllIntRD x y z =
      3 * symEllIntRF x y z := by
  set S : ℝ → ℂ := fun t => ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
    ((t : ℂ) + z) ^ (1 / 2 : ℂ) with hS
  have iF : IntegrableOn (fun t : ℝ => (S t)⁻¹) (Ioi 0) := p19sR1_integrableOn_RF hx hy hz
  have iDy : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + y))⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RJ hx hy hz hy
  have iDz : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + z))⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RJ hx hy hz hz
  have iDx : IntegrableOn (fun t : ℝ => x * (S t * ((t : ℂ) + x))⁻¹) (Ioi 0) := by
    rcases hx with hx' | rfl
    · exact (p19sR1_integrableOn_RJ (Or.inl hx') hy hz hx').const_mul x
    · simp
  have i1 : IntegrableOn (fun t : ℝ => x * (S t * ((t : ℂ) + x))⁻¹ +
      y * (S t * ((t : ℂ) + y))⁻¹) (Ioi 0) := iDx.add (iDy.const_mul y)
  have i2 : IntegrableOn (fun t : ℝ => x * (S t * ((t : ℂ) + x))⁻¹ +
      y * (S t * ((t : ℂ) + y))⁻¹ + z * (S t * ((t : ℂ) + z))⁻¹) (Ioi 0) :=
    i1.add (iDz.const_mul z)
  have i3 : IntegrableOn (fun t : ℝ => x * (S t * ((t : ℂ) + x))⁻¹ +
      y * (S t * ((t : ℂ) + y))⁻¹ + z * (S t * ((t : ℂ) + z))⁻¹ - (S t)⁻¹) (Ioi 0) :=
    i2.sub iF
  have key := p19sR1_integral_eq_of_lin (α := 3) (β := 0) hx hy hz (fun _ => rfl)
    (i3.const_mul (3 / 2 : ℂ)) fun t ht => by
      have := p19sR1_alg9 (t : ℂ) _ _ _ x y z (p19sR1_cpow_half_sq _) (p19sR1_cpow_half_sq _)
        (p19sR1_cpow_half_sq _) (p19sR1_cpow_half_ne_zero ht hx)
        (p19sR1_cpow_half_ne_zero ht (Or.inl hy)) (p19sR1_cpow_half_ne_zero ht (Or.inl hz))
      simp only [p19sR1_linDeriv] at this
      simp only [hS]
      rw [← this]
  rw [zero_mul, neg_zero, integral_const_mul, integral_sub i2 iF,
    integral_add i1 (iDz.const_mul z), integral_add iDx (iDy.const_mul y),
    integral_const_mul, integral_const_mul, integral_const_mul] at key
  rw [p19sR1_symEllIntRD_perm1 x y z hx, p19sR1_symEllIntRD_perm2 x y z (Or.inl hy),
    symEllIntRD_eq_integral (ei19c_not_isNegReal_of_mem_slitPlane hz), symEllIntRF]
  simp only [symEllIntS]
  linear_combination key

/-- DLMF 19.21.8: `R_D(y, z, x) + R_D(z, x, y) + R_D(x, y, z) = 3 x^{-1/2} y^{-1/2} z^{-1/2}`. -/
theorem p19sR1_symEllIntRD_cyclic_sum {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    symEllIntRD y z x + symEllIntRD z x y + symEllIntRD x y z =
      3 * x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ) := by
  set S : ℝ → ℂ := fun t => ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
    ((t : ℂ) + z) ^ (1 / 2 : ℂ) with hS
  have iDx : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + x))⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RJ (Or.inl hx) hy hz hx
  have iDy : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + y))⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RJ (Or.inl hx) hy hz hy
  have iDz : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + z))⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RJ (Or.inl hx) hy hz hz
  have i1 : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + x))⁻¹ +
      (S t * ((t : ℂ) + y))⁻¹) (Ioi 0) := iDx.add iDy
  have i2 : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + x))⁻¹ +
      (S t * ((t : ℂ) + y))⁻¹ + (S t * ((t : ℂ) + z))⁻¹) (Ioi 0) := i1.add iDz
  have key := p19sR1_integral_eq_of_lin (α := 0) (β := -3) (Or.inl hx) hy hz
    (fun h => absurd h (slitPlane_ne_zero hx))
    (i2.const_mul (3 / 2 : ℂ)) fun t ht => by
      have := p19sR1_alg8 (t : ℂ) _ _ _ x y z (p19sR1_cpow_half_sq _) (p19sR1_cpow_half_sq _)
        (p19sR1_cpow_half_sq _) (p19sR1_cpow_half_ne_zero ht (Or.inl hx))
        (p19sR1_cpow_half_ne_zero ht (Or.inl hy)) (p19sR1_cpow_half_ne_zero ht (Or.inl hz))
      simp only [p19sR1_linDeriv] at this
      simp only [hS]
      rw [← this]
  rw [integral_const_mul, integral_add i1 iDz, integral_add iDx iDy] at key
  rw [p19sR1_symEllIntRD_perm1 x y z (Or.inl hx), p19sR1_symEllIntRD_perm2 x y z (Or.inl hy),
    symEllIntRD_eq_integral (ei19c_not_isNegReal_of_mem_slitPlane hz)]
  simp only [symEllIntS]
  have e : ∀ w : ℂ, w ^ (-1 / 2 : ℂ) = (w ^ (1 / 2 : ℂ))⁻¹ := fun w => by
    rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  rw [e x, e y, e z]
  rw [mul_inv, mul_inv] at key
  linear_combination key

/-- DLMF 19.21.7: `(x - y) R_D(y, z, x) + (z - y) R_D(x, y, z) = 3R_F(x, y, z)
- 3 y^{1/2} x^{-1/2} z^{-1/2}`, slit-plane variables. -/
theorem p19sR1_symEllIntRD_move {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    (x - y) * symEllIntRD y z x + (z - y) * symEllIntRD x y z =
      3 * symEllIntRF x y z - 3 * y ^ (1 / 2 : ℂ) * x ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ) := by
  set S : ℝ → ℂ := fun t => ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
    ((t : ℂ) + z) ^ (1 / 2 : ℂ) with hS
  have iF : IntegrableOn (fun t : ℝ => (S t)⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RF (Or.inl hx) hy hz
  have iDx : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + x))⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RJ (Or.inl hx) hy hz hx
  have iDz : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + z))⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RJ (Or.inl hx) hy hz hz
  have i1 : IntegrableOn (fun t : ℝ => (x - y) * (S t * ((t : ℂ) + x))⁻¹ +
      (z - y) * (S t * ((t : ℂ) + z))⁻¹) (Ioi 0) :=
    (iDx.const_mul (x - y)).add (iDz.const_mul (z - y))
  have i2 : IntegrableOn (fun t : ℝ => (x - y) * (S t * ((t : ℂ) + x))⁻¹ +
      (z - y) * (S t * ((t : ℂ) + z))⁻¹ - (S t)⁻¹) (Ioi 0) := i1.sub iF
  have key := p19sR1_integral_eq_of_lin (α := 3) (β := 3 * y) (Or.inl hx) hy hz
    (fun h => absurd h (slitPlane_ne_zero hx))
    (i2.const_mul (3 / 2 : ℂ)) fun t ht => by
      have := p19sR1_alg7 (t : ℂ) _ _ _ x y z (p19sR1_cpow_half_sq _) (p19sR1_cpow_half_sq _)
        (p19sR1_cpow_half_sq _) (p19sR1_cpow_half_ne_zero ht (Or.inl hx))
        (p19sR1_cpow_half_ne_zero ht (Or.inl hy)) (p19sR1_cpow_half_ne_zero ht (Or.inl hz))
      simp only [p19sR1_linDeriv] at this
      simp only [hS]
      rw [← this]
  rw [integral_const_mul, integral_sub i1 iF, integral_add (iDx.const_mul (x - y))
    (iDz.const_mul (z - y)), integral_const_mul, integral_const_mul] at key
  rw [p19sR1_symEllIntRD_perm1 x y z (Or.inl hx),
    symEllIntRD_eq_integral (ei19c_not_isNegReal_of_mem_slitPlane hz), symEllIntRF]
  simp only [symEllIntS]
  have e : ∀ w : ℂ, w ^ (-1 / 2 : ℂ) = (w ^ (1 / 2 : ℂ))⁻¹ := fun w => by
    rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  have hy2 : y ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) = y := ei19c_cpow_half_sq y
  have hy0 := p19sR1_cpow_half_ne_zero_of_mem hy
  rw [e x, e z]
  rw [mul_inv, mul_inv] at key
  have : y * (y ^ (1 / 2 : ℂ))⁻¹ = y ^ (1 / 2 : ℂ) := by
    rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hy0]; exact hy2
  linear_combination key - 3 * (x ^ (1 / 2 : ℂ))⁻¹ * (z ^ (1 / 2 : ℂ))⁻¹ * this

/-- DLMF 19.21.11 (first form): `6R_G(x, y, z) = 3(x + y + z) R_F(x, y, z) - ∑ x² R_D(y, z, x)`
(cyclic sum), slit-plane variables. The integrands agree pointwise
(`t x/(t + x) = x - x²/(t + x)`). -/
theorem p19sR1_six_mul_symEllIntRG {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    6 * symEllIntRG x y z = 3 * (x + y + z) * symEllIntRF x y z -
      (x ^ 2 * symEllIntRD y z x + y ^ 2 * symEllIntRD z x y + z ^ 2 * symEllIntRD x y z) := by
  set S : ℝ → ℂ := fun t => ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
    ((t : ℂ) + z) ^ (1 / 2 : ℂ) with hS
  have iF : IntegrableOn (fun t : ℝ => (S t)⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RF (Or.inl hx) hy hz
  have iDx : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + x))⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RJ (Or.inl hx) hy hz hx
  have iDy : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + y))⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RJ (Or.inl hx) hy hz hy
  have iDz : IntegrableOn (fun t : ℝ => (S t * ((t : ℂ) + z))⁻¹) (Ioi 0) :=
    p19sR1_integrableOn_RJ (Or.inl hx) hy hz hz
  have i1 : IntegrableOn (fun t : ℝ => x ^ 2 * (S t * ((t : ℂ) + x))⁻¹ +
      y ^ 2 * (S t * ((t : ℂ) + y))⁻¹) (Ioi 0) := (iDx.const_mul _).add (iDy.const_mul _)
  have i2 : IntegrableOn (fun t : ℝ => x ^ 2 * (S t * ((t : ℂ) + x))⁻¹ +
      y ^ 2 * (S t * ((t : ℂ) + y))⁻¹ + z ^ 2 * (S t * ((t : ℂ) + z))⁻¹) (Ioi 0) :=
    i1.add (iDz.const_mul _)
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (symEllIntS x y z t)⁻¹ *
      (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t =
      (x + y + z) * (S t)⁻¹ - (x ^ 2 * (S t * ((t : ℂ) + x))⁻¹ +
        y ^ 2 * (S t * ((t : ℂ) + y))⁻¹ + z ^ 2 * (S t * ((t : ℂ) + z))⁻¹) := by
    intro t ht
    have h1 := slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht (Or.inl hx))
    have h2 := slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht (Or.inl hy))
    have h3 := slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht (Or.inl hz))
    simp only [symEllIntS, hS]
    field_simp
    ring
  have hG : symEllIntRG x y z = (1 / 4) * ((x + y + z) * (∫ t in Ioi (0 : ℝ), (S t)⁻¹) -
      (x ^ 2 * (∫ t in Ioi (0 : ℝ), (S t * ((t : ℂ) + x))⁻¹) +
        y ^ 2 * (∫ t in Ioi (0 : ℝ), (S t * ((t : ℂ) + y))⁻¹) +
        z ^ 2 * (∫ t in Ioi (0 : ℝ), (S t * ((t : ℂ) + z))⁻¹))) := by
    rw [symEllIntRG, setIntegral_congr_fun measurableSet_Ioi hpt,
      integral_sub (iF.const_mul _) i2, integral_add i1 (iDz.const_mul _),
      integral_add (iDx.const_mul _) (iDy.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul]
  rw [hG, p19sR1_symEllIntRD_perm1 x y z (Or.inl hx), p19sR1_symEllIntRD_perm2 x y z (Or.inl hy),
    symEllIntRD_eq_integral (ei19c_not_isNegReal_of_mem_slitPlane hz), symEllIntRF]
  simp only [symEllIntS, hS]
  ring

/-- Integrability of `R_C`'s integrand `((t + x)^{1/2} (t + y))⁻¹`: `x` admissible, `y` in the
slit plane. -/
lemma p19sR1_integrableOn_RC {x y : ℂ} (hx : SymEllIntArg x) (hy : y ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹) (Ioi 0) := by
  obtain ⟨c1, hc1, h1⟩ := p19sR1_norm_cpow_half_ge' hx
  obtain ⟨c2, hc2, h2⟩ := p19sR1_norm_add_ge hy
  refine p19sR1_integrableOn_of_le (C := (c1 * c2)⁻¹) ?_ fun t ht => ?_
  · refine ((p19sR1_continuousOn_cpow_half hx).mul
      (continuous_ofReal.add continuous_const).continuousOn).inv₀ fun t ht => ?_
    exact mul_ne_zero (p19sR1_cpow_half_ne_zero ht hx)
      (slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht (Or.inl hy)))
  · have a1 := h1 t ht
    have a2 := h2 t ht.le
    rw [norm_inv, norm_mul, ← mul_inv]
    have hp : 0 < ‖((t : ℂ) + x) ^ (1 / 2 : ℂ)‖ * ‖(t : ℂ) + y‖ :=
      mul_pos (lt_of_lt_of_le (by positivity) a1) (lt_of_lt_of_le (by positivity) a2)
    rw [inv_le_inv₀ hp (by positivity)]
    calc c1 * c2 * (Real.sqrt t * (t + 1)) = (c1 * Real.sqrt t) * (c2 * (t + 1)) := by ring
      _ ≤ _ := mul_le_mul a1 a2 (by positivity) (norm_nonneg _)

/-- DLMF 19.20.8 (third), **stronger than DLMF** in allowing `x = 0`:
`R_J(x, y, y, p) = 3/(p - y) (R_C(x, y) - R_C(x, p))`, `p ≠ y`, `x` admissible,
`y, p ∈ ℂ \ (-∞, 0]`. Partial fractions in the integrand. -/
theorem p19sR1_symEllIntRJ_self_right_eq {x y p : ℂ} (hx : SymEllIntArg x) (hy : y ∈ slitPlane)
    (hp : p ∈ slitPlane) (hpy : p ≠ y) :
    symEllIntRJ x y y p = 3 / (p - y) * (symEllIntRC x y - symEllIntRC x p) := by
  have iy := p19sR1_integrableOn_RC hx hy
  have ip := p19sR1_integrableOn_RC hx hp
  have hpy' : p - y ≠ 0 := sub_ne_zero.mpr hpy
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (symEllIntS x y y t * ((t : ℂ) + p))⁻¹ =
      (p - y)⁻¹ * ((((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹ -
        (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + p))⁻¹) := by
    intro t ht
    have h1 := p19sR1_cpow_half_ne_zero ht hx
    have h2 := slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht (Or.inl hy))
    have h3 := slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht (Or.inl hp))
    simp only [symEllIntS, mul_assoc, ei19c_cpow_half_sq]
    field_simp
    ring
  simp only [symEllIntRJ, symEllIntRC, ei19c_not_isNegReal_of_mem_slitPlane hp,
    ei19c_not_isNegReal_of_mem_slitPlane hy, ↓reduceIte]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_sub iy ip]
  field_simp

/-- DLMF 19.20.20 on the slit plane: `R_D(x, y, y) = 3/(2(y - x)) (R_C(x, y) - √x/y)`, `x ≠ y`.
From (19.21.7) with `(x, y, z) ↦ (y, x, y)`. -/
theorem p19sR1_symEllIntRD_self_right {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hxy : x ≠ y) :
    symEllIntRD x y y = 3 / (2 * (y - x)) * (symEllIntRC x y - x ^ (1 / 2 : ℂ) / y) := by
  have h := p19sR1_symEllIntRD_move hy hx hy
  rw [symEllIntRD_comm x y y, symEllIntRF_comm_left,
    ← symEllIntRC_eq_symEllIntRF x (ei19c_not_isNegReal_of_mem_slitPlane hy)] at h
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hy0 := p19sR1_cpow_half_ne_zero_of_mem hy
  have hy2 := ei19c_cpow_half_sq y
  have e : y ^ (-1 / 2 : ℂ) = (y ^ (1 / 2 : ℂ))⁻¹ := by
    rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  have hinv : (y ^ (1 / 2 : ℂ))⁻¹ * (y ^ (1 / 2 : ℂ))⁻¹ = y⁻¹ := by rw [← mul_inv, hy2]
  have hyne := slitPlane_ne_zero hy
  have h' : 2 * (y - x) * symEllIntRD x y y = 3 * symEllIntRC x y - 3 * x ^ (1 / 2 : ℂ) * y⁻¹ := by
    rw [← hinv, ← e]; linear_combination h
  calc symEllIntRD x y y = (2 * (y - x) * symEllIntRD x y y) / (2 * (y - x)) := by field_simp
    _ = (3 * symEllIntRC x y - 3 * x ^ (1 / 2 : ℂ) * y⁻¹) / (2 * (y - x)) := by rw [h']
    _ = _ := by ring

/-- DLMF 19.20.21: `R_D(x, x, z) = 3/(z - x) (R_C(z, x) - 1/√z)`, `x ≠ z`, slit plane. From
(19.21.8) and (19.20.20). -/
theorem p19sR1_symEllIntRD_self_left {x z : ℂ} (hx : x ∈ slitPlane) (hz : z ∈ slitPlane)
    (hxz : x ≠ z) :
    symEllIntRD x x z = 3 / (z - x) * (symEllIntRC z x - 1 / z ^ (1 / 2 : ℂ)) := by
  have h8 := p19sR1_symEllIntRD_cyclic_sum hx hx hz
  have h20 := p19sR1_symEllIntRD_self_right hz hx (Ne.symm hxz)
  rw [← symEllIntRD_comm x z x] at h8
  have hxz' : x - z ≠ 0 := sub_ne_zero.mpr hxz
  have hzx' : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
  have hx0 := p19sR1_cpow_half_ne_zero_of_mem hx
  have hz0 := p19sR1_cpow_half_ne_zero_of_mem hz
  have hx2 := ei19c_cpow_half_sq x
  have hz2 := ei19c_cpow_half_sq z
  have e : ∀ w : ℂ, w ^ (-1 / 2 : ℂ) = (w ^ (1 / 2 : ℂ))⁻¹ := fun w => by
    rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  rw [e, e, h20] at h8
  have hxne := slitPlane_ne_zero hx
  have hzne := slitPlane_ne_zero hz
  have hinv : (x ^ (1 / 2 : ℂ))⁻¹ * (x ^ (1 / 2 : ℂ))⁻¹ = x⁻¹ := by rw [← mul_inv, hx2]
  have h8' : 2 * (3 / (2 * (x - z)) * (symEllIntRC z x - z ^ (1 / 2 : ℂ) / x)) +
      symEllIntRD x x z = 3 * x⁻¹ * (z ^ (1 / 2 : ℂ))⁻¹ := by
    rw [← hinv]; linear_combination h8
  have hzz : z ^ (1 / 2 : ℂ) / x = z / (x * z ^ (1 / 2 : ℂ)) := by
    rw [div_eq_div_iff hxne (mul_ne_zero hxne hz0)]; linear_combination x * hz2
  rw [hzz] at h8'
  calc symEllIntRD x x z = 3 * x⁻¹ * (z ^ (1 / 2 : ℂ))⁻¹ -
      2 * (3 / (2 * (x - z)) * (symEllIntRC z x - z / (x * z ^ (1 / 2 : ℂ)))) := by
        linear_combination h8'
    _ = _ := by field_simp; ring

/-- A function with `‖f t‖ ≥ M/t` on `(0, 1)`, `M > 0`, is not integrable on `(0, ∞)`. -/
lemma p19sR1_not_integrableOn_of_ge {f : ℝ → ℂ} {M : ℝ} (hM : 0 < M)
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, M * t⁻¹ ≤ ‖f t‖) : ¬ IntegrableOn f (Ioi 0) := by
  intro hf
  have h1 : IntegrableOn f (Ioo 0 1) := hf.mono_set Ioo_subset_Ioi_self
  have h2 : IntegrableOn (fun t : ℝ => M * t ^ (-1 : ℝ)) (Ioo 0 1) := by
    refine Integrable.mono' (Integrable.norm h1) ?_ ?_
    · have hc : ContinuousOn (fun t : ℝ => M * t ^ (-1 : ℝ)) (Ioo 0 1) := fun t ht =>
        (continuousAt_const.mul (Real.continuousAt_rpow_const _ _
          (Or.inl (ne_of_gt (mem_Ioo.mp ht).1)))).continuousWithinAt
      exact hc.aestronglyMeasurable measurableSet_Ioo
    · refine (ae_restrict_mem measurableSet_Ioo).mono fun t ht => ?_
      rw [Real.rpow_neg_one, Real.norm_of_nonneg (by have := ht.1; positivity)]
      exact h t ht
  have h3 : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 1) := by
    have h4 : IntegrableOn (fun t : ℝ => M⁻¹ * (M * t ^ (-1 : ℝ))) (Ioo 0 1) := h2.const_mul M⁻¹
    refine h4.congr_fun (fun t _ => ?_) measurableSet_Ioo
    field_simp
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff one_pos] at h3
  norm_num at h3

/-- `‖(t + w)^{1/2}‖ ≤ √(1 + ‖w‖)` for `0 ≤ t ≤ 1`. -/
lemma p19sR1_norm_cpow_half_le {w : ℂ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((t : ℂ) + w) ^ (1 / 2 : ℂ)‖ ≤ Real.sqrt (1 + ‖w‖) := by
  rw [p19sR1_norm_cpow_half]
  refine Real.sqrt_le_sqrt ?_
  calc ‖(t : ℂ) + w‖ ≤ ‖(t : ℂ)‖ + ‖w‖ := norm_add_le _ _
    _ ≤ 1 + ‖w‖ := by rw [Complex.norm_real, Real.norm_of_nonneg ht]; linarith

/-- `‖t + w‖ ≤ 1 + ‖w‖` for `0 ≤ t ≤ 1`. -/
lemma p19sR1_norm_add_le {w : ℂ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(t : ℂ) + w‖ ≤ 1 + ‖w‖ := by
  calc ‖(t : ℂ) + w‖ ≤ ‖(t : ℂ)‖ + ‖w‖ := norm_add_le _ _
    _ ≤ 1 + ‖w‖ := by rw [Complex.norm_real, Real.norm_of_nonneg ht]; linarith

/-- The integrand `(s(t) (t + p))⁻¹` with two zero variables is not integrable at `0`. -/
theorem p19sR1_not_integrableOn_zero_zero {z p : ℂ} (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    ¬ IntegrableOn (fun t => (symEllIntS 0 0 z t * ((t : ℂ) + p))⁻¹) (Ioi 0) := by
  have hA : 0 < Real.sqrt (1 + ‖z‖) := Real.sqrt_pos.mpr (by positivity)
  refine p19sR1_not_integrableOn_of_ge (M := (Real.sqrt (1 + ‖z‖) * (1 + ‖p‖))⁻¹)
    (by positivity) fun t ht => ?_
  have ht0 := ht.1
  have h1 := p19sR1_norm_cpow_half_le (w := z) ht0.le ht.2.le
  have h2 := p19sR1_norm_add_le (w := p) ht0.le ht.2.le
  have q1 : 0 < ‖((t : ℂ) + z) ^ (1 / 2 : ℂ)‖ :=
    norm_pos_iff.mpr (p19sR1_cpow_half_ne_zero ht0 (Or.inl hz))
  have q2 : 0 < ‖(t : ℂ) + p‖ :=
    norm_pos_iff.mpr (slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht0 (Or.inl hp)))
  simp only [symEllIntS, add_zero]
  rw [ei19c_cpow_half_sq, norm_inv, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ht0.le, ← mul_inv, inv_le_inv₀ (by positivity) (by positivity)]
  calc t * ‖((t : ℂ) + z) ^ (1 / 2 : ℂ)‖ * ‖(t : ℂ) + p‖
      ≤ t * Real.sqrt (1 + ‖z‖) * (1 + ‖p‖) := by gcongr
    _ = _ := by ring

/-- The integrand `s(t)⁻¹` with two zero variables is not integrable at `0`. -/
theorem p19sR1_not_integrableOn_zero_zero' {z : ℂ} (hz : z ∈ slitPlane) :
    ¬ IntegrableOn (fun t => (symEllIntS 0 0 z t)⁻¹) (Ioi 0) := by
  have hA : 0 < Real.sqrt (1 + ‖z‖) := Real.sqrt_pos.mpr (by positivity)
  refine p19sR1_not_integrableOn_of_ge (M := (Real.sqrt (1 + ‖z‖))⁻¹)
    (by positivity) fun t ht => ?_
  have ht0 := ht.1
  have h1 := p19sR1_norm_cpow_half_le (w := z) ht0.le ht.2.le
  have q1 : 0 < ‖((t : ℂ) + z) ^ (1 / 2 : ℂ)‖ :=
    norm_pos_iff.mpr (p19sR1_cpow_half_ne_zero ht0 (Or.inl hz))
  simp only [symEllIntS, add_zero]
  rw [ei19c_cpow_half_sq, norm_inv, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ht0.le, ← mul_inv, inv_le_inv₀ (by positivity) (by positivity)]
  calc t * ‖((t : ℂ) + z) ^ (1 / 2 : ℂ)‖ ≤ t * Real.sqrt (1 + ‖z‖) := by gcongr
    _ = _ := by ring

end DLMF.EllipticIntegrals
