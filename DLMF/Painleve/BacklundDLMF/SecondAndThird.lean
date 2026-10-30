/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Backlund
public import DLMF.Painleve.Equations

/-!
# Backlund transformations for Painleve II and III

Parameter-changing transformations of Painleve II and III, including denominator and domain
conditions.

Source references and common attribution are retained in
`DLMF.Painleve.BacklundDLMF`.
-/

@[expose] public noncomputable section

open Set Filter

open scoped Topology

namespace DLMF.Painleve

/-- DLMF 32.7.1, the transformation `S`: `w(z; -α) = -w(z; α)`. -/
@[dlmf 32.7.E1]
theorem IsPainleveIIOn.neg {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (h : IsPainleveIIOn α w U) :
    IsPainleveIIOn (-α) (fun z => -w z) U := by
  rw [isPainleveIIOn_iff_isPIIOn, neg_neg]
  simpa using (isPainleveIIOn_iff_isPIIOn.mp h).neg

/-- DLMF 32.7.2, the transformation `T⁺`: `w(z; α+1) = -w - (2α+1)/(2w² + 2w' + z)` is a
solution of `PII` with parameter `α + 1` on every open set where the denominator does not
vanish. Stronger than DLMF: no restriction `α ≠ -1/2` is needed on such a set (at
`α = -1/2` the map is `w ↦ -w`). -/
@[dlmf 32.7.E2]
theorem IsPainleveIIOn.tPlus {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (h : IsPainleveIIOn α w U)
    (hU : IsOpen U) (hD : ∀ z ∈ U, 2 * w z ^ 2 + 2 * deriv w z + z ≠ 0) :
    IsPainleveIIOn (α + 1) (painleveIITPlus α w) U := by
  have h1 := (isPainleveIIOn_iff_isPIIOn.mp h).shiftDown hU (fun z hz => by
    simpa [backlundDenom, add_comm, add_left_comm, add_assoc] using hD z hz)
  rw [isPainleveIIOn_iff_isPIIOn]
  have he : backlundDown (-α) w = painleveIITPlus α w := by
    funext z
    simp only [backlundDown, backlundReflect, backlundCorrection, backlundDenom,
      painleveIITPlus]
    rw [show z + 2 * w z ^ 2 + 2 * deriv w z = 2 * w z ^ 2 + 2 * deriv w z + z by ring]
    ring
  rw [← he, show -(α + 1) = -α - 1 by ring]
  exact h1

/-- DLMF 32.7.2, the transformation `T⁻`: `w(z; α-1) = -w - (2α-1)/(2w² - 2w' + z)` is a
solution of `PII` with parameter `α - 1` where the denominator does not vanish. -/
@[dlmf 32.7.E2]
theorem IsPainleveIIOn.tMinus {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (h : IsPainleveIIOn α w U)
    (hU : IsOpen U) (hD : ∀ z ∈ U, 2 * w z ^ 2 - 2 * deriv w z + z ≠ 0) :
    IsPainleveIIOn (α - 1) (painleveIITMinus α w) U := by
  have hneg (z : ℂ) : deriv (fun x => -w x) z = -deriv w z := deriv.neg
  have h1 := (isPainleveIIOn_iff_isPIIOn.mp h).shiftUp hU (fun z hz => by
    simp only [backlundDenom, hneg]
    convert hD z hz using 1; ring)
  rw [isPainleveIIOn_iff_isPIIOn]
  have he : backlundUp (-α) w = painleveIITMinus α w := by
    funext z
    rw [backlundUp_eq]
    simp only [painleveIITMinus]
    rw [show z + 2 * w z ^ 2 - 2 * deriv w z = 2 * w z ^ 2 - 2 * deriv w z + z by ring]
    ring
  rw [← he, show -(α - 1) = -α + 1 by ring]
  exact h1

/-- The explicit derivative of the special transformation 32.7.3. -/
private lemma a32_special_hasDerivAt {w : ℂ → ℂ} {U : Set ℂ} (h : IsPainleveIIOn 0 w U)
    (hw0 : ∀ z ∈ U, w z ≠ 0) {t ε : ℂ} (ht : t ≠ 0) {ζ : ℂ} (hζ : -ζ / t ∈ U) :
    HasDerivAt (fun ζ => ε / t * deriv w (-ζ / t) / w (-ζ / t))
      (-(ε / t ^ 2) * (2 * w (-ζ / t) ^ 2 + -ζ / t - deriv w (-ζ / t) ^ 2 / w (-ζ / t) ^ 2))
      ζ := by
  have hφ : HasDerivAt (fun ζ : ℂ => -ζ / t) (-1 / t) ζ := by
    simpa using ((hasDerivAt_id ζ).neg).div_const t
  have hw := (IsODE2SolutionOn.hasDerivAt h hζ).comp (h := fun ζ : ℂ => -ζ / t) ζ hφ
  have hv := (h.hasDerivAt_deriv _ hζ).comp (h := fun ζ : ℂ => -ζ / t) ζ hφ
  have h0 := hw0 _ hζ
  refine ((hv.const_mul (ε / t)).div hw h0).congr_deriv ?_
  simp only [Function.comp, painleveIIRhs]
  generalize w (-ζ / t) = a at h0 ⊢
  generalize deriv w (-ζ / t) = b
  field_simp
  ring

/-- DLMF 32.7.3: the special transformation `W(ζ; ε/2) = 2^{-1/3} ε w'(z; 0)/w(z; 0)`,
`ζ = -2^{1/3} z`, `ε = ±1`, takes a solution of `PII` with `α = 0` to a solution with
`α = ε/2`. Stated for every `t` with `t³ = 2` in place of `2^{1/3}` (stronger than DLMF),
on the open set of `ζ` with `z = -ζ/t ∈ U`, where `w ≠ 0`. -/
@[dlmf 32.7.E3]
theorem IsPainleveIIOn.special {w : ℂ → ℂ} {U : Set ℂ} (h : IsPainleveIIOn 0 w U)
    (hU : IsOpen U) (hw0 : ∀ z ∈ U, w z ≠ 0) {t ε : ℂ} (ht : t ^ 3 = 2)
    (hε : ε = 1 ∨ ε = -1) :
    IsPainleveIIOn (ε / 2) (fun ζ => ε / t * deriv w (-ζ / t) / w (-ζ / t))
      ((fun ζ : ℂ => -ζ / t) ⁻¹' U) := by
  have ht0 : t ≠ 0 := by rintro rfl; norm_num at ht
  have hV : IsOpen ((fun ζ : ℂ => -ζ / t) ⁻¹' U) :=
    hU.preimage (continuous_neg.div_const t)
  refine isODE2SolutionOn_of_hasDerivAt hV (fun ζ hζ => a32_special_hasDerivAt h hw0 ht0 hζ)
    (fun ζ hζ => ?_)
  have hζ : -ζ / t ∈ U := hζ
  have hφ : HasDerivAt (fun ζ : ℂ => -ζ / t) (-1 / t) ζ := by
    simpa using ((hasDerivAt_id ζ).neg).div_const t
  have hw := (IsODE2SolutionOn.hasDerivAt h hζ).comp (h := fun ζ : ℂ => -ζ / t) ζ hφ
  have hv := (h.hasDerivAt_deriv _ hζ).comp (h := fun ζ : ℂ => -ζ / t) ζ hφ
  have h0 := hw0 _ hζ
  refine ((((hw.pow 2).const_mul 2).add hφ).sub ((hv.pow 2).div (hw.pow 2)
    (pow_ne_zero 2 h0))).const_mul (-(ε / t ^ 2)) |>.congr_deriv ?_
  simp only [Function.comp, painleveIIRhs, Pi.pow_apply]
  have ht' (n : ℕ) : t ^ (n + 3) = 2 * t ^ n := by rw [pow_add, ht]; ring
  generalize w (-ζ / t) = a at h0 ⊢
  generalize deriv w (-ζ / t) = b
  rcases hε with rfl | rfl <;>
  · field_simp
    ring_nf
    simp only [ht, show t ^ 4 = 2 * t by simpa using ht' 1, show t ^ 5 = 2 * t ^ 2 by
      simpa using ht' 2, show t ^ 6 = 4 by rw [ht' 3, ht]; norm_num]
    ring

/-- DLMF 32.7.4, the equivalent form of the special transformation:
`w²(z; 0) = 2^{-1/3}(W² - εW' + ζ/2)` with `W = W(ζ; ε/2)` from 32.7.3 and `ζ = -2^{1/3}z`
(any `t` with `t³ = 2` in place of `2^{1/3}`). -/
@[dlmf 32.7.E4]
theorem IsPainleveIIOn.special_sq {w : ℂ → ℂ} {U : Set ℂ} (h : IsPainleveIIOn 0 w U)
    (hw0 : ∀ z ∈ U, w z ≠ 0) {t ε : ℂ} (ht : t ^ 3 = 2)
    (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (hζ : -ζ / t ∈ U) :
    let W := fun ζ => ε / t * deriv w (-ζ / t) / w (-ζ / t)
    w (-ζ / t) ^ 2 = 1 / t * (W ζ ^ 2 - ε * deriv W ζ + ζ / 2) := by
  have ht0 : t ≠ 0 := by rintro rfl; norm_num at ht
  intro W
  rw [(a32_special_hasDerivAt (ε := ε) h hw0 ht0 hζ).deriv]
  have h0 := hw0 _ hζ
  simp only [W]
  generalize w (-ζ / t) = a at h0 ⊢
  generalize deriv w (-ζ / t) = b
  rcases hε with rfl | rfl <;>
  · field_simp
    ring_nf
    rw [show t ^ 4 = t * t ^ 3 by ring, ht]
    ring

/-- DLMF 32.7.5: the solutions `w_{α±1} = T^± w_α` satisfy the nonlinear recurrence
`(α + 1/2)/(w_{α+1} + w_α) + (α - 1/2)/(w_α + w_{α-1}) + 2w_α² + z = 0`, wherever
`α ≠ ±1/2` (an algebraic identity; with the totalized maps `painleveIITPlus`,
`painleveIITMinus` it holds even where the denominators of 32.7.2 vanish). -/
@[dlmf 32.7.E5]
theorem painleveII_recurrence {α : ℂ} (w : ℂ → ℂ) (z : ℂ) (hα₁ : 2 * α + 1 ≠ 0)
    (hα₂ : 2 * α - 1 ≠ 0) :
    (α + 1 / 2) / (painleveIITPlus α w z + w z) +
        (α - 1 / 2) / (w z + painleveIITMinus α w z) + 2 * w z ^ 2 + z = 0 := by
  simp only [painleveIITPlus, painleveIITMinus]
  rw [show -w z - (2 * α + 1) / (2 * w z ^ 2 + 2 * deriv w z + z) + w z =
      -((2 * α + 1) / (2 * w z ^ 2 + 2 * deriv w z + z)) by ring,
    show w z + (-w z - (2 * α - 1) / (2 * w z ^ 2 - 2 * deriv w z + z)) =
      -((2 * α - 1) / (2 * w z ^ 2 - 2 * deriv w z + z)) by ring]
  have e1 : (α + 1 / 2) / -((2 * α + 1) / (2 * w z ^ 2 + 2 * deriv w z + z)) =
      -(2 * w z ^ 2 + 2 * deriv w z + z) / 2 := by
    rw [show α + 1 / 2 = (2 * α + 1) / 2 by ring]; field_simp
  have e2 : (α - 1 / 2) / -((2 * α - 1) / (2 * w z ^ 2 - 2 * deriv w z + z)) =
      -(2 * w z ^ 2 - 2 * deriv w z + z) / 2 := by
    rw [show α - 1 / 2 = (2 * α - 1) / 2 by ring]; field_simp
  rw [e1, e2]
  ring

/-! ## `PIII` (§32.7(iii)) -/

/-- DLMF 32.7.6 and 32.7.8, the transformation `S₁`: `w₁ = -w₀` solves `PIII` with
`(α₁, β₁, γ₁, δ₁) = (-α₀, -β₀, γ₀, δ₀)`. -/
@[dlmf 32.7.E6, dlmf 32.7.E8]
theorem IsPainleveIIIOn.neg {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn α β γ δ w U) (hU : IsOpen U) :
    IsPainleveIIIOn (-α) (-β) γ δ (fun z => -w z) U := by
  refine ⟨?_, h.ne_zero, fun z hz => neg_ne_zero.mpr (h.w_ne_zero z hz)⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => -deriv w z)
    (fun z hz => (h.ode.hasDerivAt hz).neg) (fun z hz => ?_)
  refine (h.ode.hasDerivAt_deriv z hz).neg.congr_deriv ?_
  have := h.w_ne_zero z hz
  have := h.ne_zero z hz
  simp only [painleveIIIRhs]
  field_simp
  ring

/-- DLMF 32.7.7 and 32.7.9, the transformation `S₂`: `w₂ = 1/w₀` solves `PIII` with
`(α₂, β₂, γ₂, δ₂) = (-β₀, -α₀, -δ₀, -γ₀)`. -/
@[dlmf 32.7.E7, dlmf 32.7.E9]
theorem IsPainleveIIIOn.inv {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn α β γ δ w U) (hU : IsOpen U) :
    IsPainleveIIIOn (-β) (-α) (-δ) (-γ) (fun z => (w z)⁻¹) U := by
  refine ⟨?_, h.ne_zero, fun z hz => inv_ne_zero (h.w_ne_zero z hz)⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => -deriv w z / w z ^ 2)
    (fun z hz => ?_) (fun z hz => ?_)
  · exact ((h.ode.hasDerivAt hz).inv (h.w_ne_zero z hz)).congr_deriv (by ring)
  · have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    refine ((h.ode.hasDerivAt_deriv z hz).neg.div ((h.ode.hasDerivAt hz).pow 2)
      (pow_ne_zero 2 h0)).congr_deriv ?_
    simp only [painleveIIIRhs, Pi.pow_apply, Pi.neg_apply]
    field_simp
    ring

/-- DLMF 32.7.10–32.7.11, the transformation `T₁` of `PIII` with `γ = 1`, `δ = -1`:
`W₁ = (zW₀' + zW₀² - βW₀ - W₀ + z)/(W₀(zW₀' + zW₀² + αW₀ + W₀ + z))` solves `PIII` with
`(α₁, β₁) = (α₀ + 2, β₀ + 2)`, where the denominator and numerator do not vanish. -/
@[dlmf 32.7.E10, dlmf 32.7.E11]
theorem IsPainleveIIIOn.t₁ {α β : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn α β 1 (-1) w U) (hU : IsOpen U)
    (hN : ∀ z ∈ U, z * deriv w z + z * w z ^ 2 - β * w z - w z + z ≠ 0)
    (hD : ∀ z ∈ U, z * deriv w z + z * w z ^ 2 + α * w z + w z + z ≠ 0) :
    IsPainleveIIIOn (α + 2) (β + 2) 1 (-1) (fun z =>
      (z * deriv w z + z * w z ^ 2 - β * w z - w z + z) /
        (w z * (z * deriv w z + z * w z ^ 2 + α * w z + w z + z))) U := by
  refine ⟨?_, h.ne_zero, fun z hz => div_ne_zero (hN z hz) (mul_ne_zero (h.w_ne_zero z hz) (hD z
      hz))⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => ((((((-((((((z * deriv w z) + (z * (w z ^
      2))) + (α * w z)) + w z) + z))) * ((((((z * deriv w z) + (z * (w z ^ 2))) - (β * w z)) - w z)
      + z))) * deriv w z) + (((((((z * deriv w z) + (z * (w z ^ 2))) + (α * w z)) + w z) + z)) *
      ((((((((deriv w z ^ 2) * z) + ((deriv w z * w z) * (((-β) + ((2 * w z) * z)) - 1))) + ((w z ^
      4) * z)) + (w z ^ 3)) + (w z * ((α * (w z ^ 2)) + β))) + w z) - z))) - (((((((z * deriv w z)
      + (z * (w z ^ 2))) - (β * w z)) - w z) + z)) * ((((((((deriv w z ^ 2) * z) + ((deriv w z * w
      z) * ((α + ((2 * w z) * z)) + 1))) + ((w z ^ 4) * z)) + (w z ^ 3)) + (w z * ((α * (w z ^ 2))
      + β))) + w z) - z))) / ((((((((z * deriv w z) + (z * (w z ^ 2))) + (α * w z)) + w z) + z)) ^
      2) * (w z ^ 2)))) (fun z hz => ?_) (fun z hz => ?_)
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((((hid).mul (hv)).add ((hid).mul ((hw).pow 2))).sub ((hw).const_mul β)).sub
        (hw)).add (hid)
    have hX1 := (((((hid).mul (hv)).add ((hid).mul ((hw).pow 2))).add ((hw).const_mul α)).add
        (hw)).add (hid)
    have hc := ((hX0).div ((hw).mul (hX1)) (mul_ne_zero h0 hd))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, painleveIIIRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eN : z * b + z * a ^ 2 - β * a - a + z = NN at hn ⊢
      generalize eD : z * b + z * a ^ 2 + α * a + a + z = DD at hd ⊢
      field_simp
      subst eN eD
      ring
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((((hid).mul (hv)).add ((hid).mul ((hw).pow 2))).sub ((hw).const_mul β)).sub
        (hw)).add (hid)
    have hX1 := (((((hid).mul (hv)).add ((hid).mul ((hw).pow 2))).add ((hw).const_mul α)).add
        (hw)).add (hid)
    have hc := (((((((hX1).neg).mul (hX0)).mul (hv)).add ((hX1).mul (((((((((hv).pow 2).mul
        (hid)).add (((hv).mul (hw)).mul (((((hw).const_mul 2).mul (hid)).const_add (-β)).sub_const
        1))).add (((hw).pow 4).mul (hid))).add ((hw).pow 3)).add ((hw).mul ((((hw).pow 2).const_mul
        α).add_const β))).add (hw)).sub (hid)))).sub ((hX0).mul (((((((((hv).pow 2).mul (hid)).add
        (((hv).mul (hw)).mul (((((hw).const_mul 2).mul (hid)).const_add α).add_const 1))).add
        (((hw).pow 4).mul (hid))).add ((hw).pow 3)).add ((hw).mul ((((hw).pow 2).const_mul
        α).add_const β))).add (hw)).sub (hid)))).div (((hX1).pow 2).mul ((hw).pow 2)) (mul_ne_zero
        (pow_ne_zero 2 hd) (pow_ne_zero 2 h0)))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, painleveIIIRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eN : z * b + z * a ^ 2 - β * a - a + z = NN at hn ⊢
      generalize eD : z * b + z * a ^ 2 + α * a + a + z = DD at hd ⊢
      field_simp
      subst eN eD
      ring

/-- DLMF 32.7.10 and 32.7.12, the transformation `T₂`:
`W₂ = -(zW₀' - zW₀² - βW₀ - W₀ + z)/(W₀(zW₀' - zW₀² - αW₀ + W₀ + z))` solves `PIII(1, -1)`
with `(α₂, β₂) = (α₀ - 2, β₀ + 2)`. -/
@[dlmf 32.7.E10, dlmf 32.7.E12]
theorem IsPainleveIIIOn.t₂ {α β : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn α β 1 (-1) w U) (hU : IsOpen U)
    (hN : ∀ z ∈ U, z * deriv w z - z * w z ^ 2 - β * w z - w z + z ≠ 0)
    (hD : ∀ z ∈ U, z * deriv w z - z * w z ^ 2 - α * w z + w z + z ≠ 0) :
    IsPainleveIIIOn (α - 2) (β + 2) 1 (-1) (fun z =>
      -(z * deriv w z - z * w z ^ 2 - β * w z - w z + z) /
        (w z * (z * deriv w z - z * w z ^ 2 - α * w z + w z + z))) U := by
  refine ⟨?_, h.ne_zero, fun z hz => div_ne_zero (neg_ne_zero.mpr (hN z hz)) (mul_ne_zero
      (h.w_ne_zero z hz) (hD z hz))⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => (((((((((((z * deriv w z) - (z * (w z ^
      2))) - (α * w z)) + w z) + z)) * ((((((z * deriv w z) - (z * (w z ^ 2))) - (β * w z)) - w z)
      + z))) * deriv w z) - (((((((z * deriv w z) - (z * (w z ^ 2))) - (α * w z)) + w z) + z)) *
      ((((((((deriv w z ^ 2) * z) + ((deriv w z * w z) * (((-β) - ((2 * w z) * z)) - 1))) + ((w z ^
      4) * z)) - (w z ^ 3)) + (w z * ((α * (w z ^ 2)) + β))) + w z) - z))) + (((((((z * deriv w z)
      - (z * (w z ^ 2))) - (β * w z)) - w z) + z)) * ((((((((deriv w z ^ 2) * z) + ((deriv w z * w
      z) * (((-α) - ((2 * w z) * z)) + 1))) + ((w z ^ 4) * z)) - (w z ^ 3)) + (w z * ((α * (w z ^
      2)) + β))) + w z) - z))) / ((((((((z * deriv w z) - (z * (w z ^ 2))) - (α * w z)) + w z) +
      z)) ^ 2) * (w z ^ 2)))) (fun z hz => ?_) (fun z hz => ?_)
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((((hid).mul (hv)).sub ((hid).mul ((hw).pow 2))).sub ((hw).const_mul β)).sub
        (hw)).add (hid)
    have hX1 := (((((hid).mul (hv)).sub ((hid).mul ((hw).pow 2))).sub ((hw).const_mul α)).add
        (hw)).add (hid)
    have hc := (((hX0).neg).div ((hw).mul (hX1)) (mul_ne_zero h0 hd))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, painleveIIIRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eN : z * b - z * a ^ 2 - β * a - a + z = NN at hn ⊢
      generalize eD : z * b - z * a ^ 2 - α * a + a + z = DD at hd ⊢
      field_simp
      subst eN eD
      ring
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((((hid).mul (hv)).sub ((hid).mul ((hw).pow 2))).sub ((hw).const_mul β)).sub
        (hw)).add (hid)
    have hX1 := (((((hid).mul (hv)).sub ((hid).mul ((hw).pow 2))).sub ((hw).const_mul α)).add
        (hw)).add (hid)
    have hc := ((((((hX1).mul (hX0)).mul (hv)).sub ((hX1).mul (((((((((hv).pow 2).mul (hid)).add
        (((hv).mul (hw)).mul (((((hw).const_mul 2).mul (hid)).const_sub (-β)).sub_const 1))).add
        (((hw).pow 4).mul (hid))).sub ((hw).pow 3)).add ((hw).mul ((((hw).pow 2).const_mul
        α).add_const β))).add (hw)).sub (hid)))).add ((hX0).mul (((((((((hv).pow 2).mul (hid)).add
        (((hv).mul (hw)).mul (((((hw).const_mul 2).mul (hid)).const_sub (-α)).add_const 1))).add
        (((hw).pow 4).mul (hid))).sub ((hw).pow 3)).add ((hw).mul ((((hw).pow 2).const_mul
        α).add_const β))).add (hw)).sub (hid)))).div (((hX1).pow 2).mul ((hw).pow 2)) (mul_ne_zero
        (pow_ne_zero 2 hd) (pow_ne_zero 2 h0)))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, painleveIIIRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eN : z * b - z * a ^ 2 - β * a - a + z = NN at hn ⊢
      generalize eD : z * b - z * a ^ 2 - α * a + a + z = DD at hd ⊢
      field_simp
      subst eN eD
      ring

/-- DLMF 32.7.10 and 32.7.13, the transformation `T₃`:
`W₃ = -(zW₀' + zW₀² + βW₀ - W₀ - z)/(W₀(zW₀' + zW₀² + αW₀ + W₀ - z))` solves `PIII(1, -1)`
with `(α₃, β₃) = (α₀ + 2, β₀ - 2)`. -/
@[dlmf 32.7.E10, dlmf 32.7.E13]
theorem IsPainleveIIIOn.t₃ {α β : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn α β 1 (-1) w U) (hU : IsOpen U)
    (hN : ∀ z ∈ U, z * deriv w z + z * w z ^ 2 + β * w z - w z - z ≠ 0)
    (hD : ∀ z ∈ U, z * deriv w z + z * w z ^ 2 + α * w z + w z - z ≠ 0) :
    IsPainleveIIIOn (α + 2) (β - 2) 1 (-1) (fun z =>
      -(z * deriv w z + z * w z ^ 2 + β * w z - w z - z) /
        (w z * (z * deriv w z + z * w z ^ 2 + α * w z + w z - z))) U := by
  refine ⟨?_, h.ne_zero, fun z hz => div_ne_zero (neg_ne_zero.mpr (hN z hz)) (mul_ne_zero
      (h.w_ne_zero z hz) (hD z hz))⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => (((((((((((z * deriv w z) + (z * (w z ^
      2))) + (α * w z)) + w z) - z)) * ((((((z * deriv w z) + (z * (w z ^ 2))) + (β * w z)) - w z)
      - z))) * deriv w z) - (((((((z * deriv w z) + (z * (w z ^ 2))) + (α * w z)) + w z) - z)) *
      ((((((((deriv w z ^ 2) * z) + ((deriv w z * w z) * ((β + ((2 * w z) * z)) - 1))) + ((w z ^ 4)
      * z)) + (w z ^ 3)) + (w z * ((α * (w z ^ 2)) + β))) - w z) - z))) + (((((((z * deriv w z) +
      (z * (w z ^ 2))) + (β * w z)) - w z) - z)) * ((((((((deriv w z ^ 2) * z) + ((deriv w z * w z)
      * ((α + ((2 * w z) * z)) + 1))) + ((w z ^ 4) * z)) + (w z ^ 3)) + (w z * ((α * (w z ^ 2)) +
      β))) - w z) - z))) / ((((((((z * deriv w z) + (z * (w z ^ 2))) + (α * w z)) + w z) - z)) ^ 2)
      * (w z ^ 2)))) (fun z hz => ?_) (fun z hz => ?_)
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((((hid).mul (hv)).add ((hid).mul ((hw).pow 2))).add ((hw).const_mul β)).sub
        (hw)).sub (hid)
    have hX1 := (((((hid).mul (hv)).add ((hid).mul ((hw).pow 2))).add ((hw).const_mul α)).add
        (hw)).sub (hid)
    have hc := (((hX0).neg).div ((hw).mul (hX1)) (mul_ne_zero h0 hd))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, painleveIIIRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eN : z * b + z * a ^ 2 + β * a - a - z = NN at hn ⊢
      generalize eD : z * b + z * a ^ 2 + α * a + a - z = DD at hd ⊢
      field_simp
      subst eN eD
      ring
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((((hid).mul (hv)).add ((hid).mul ((hw).pow 2))).add ((hw).const_mul β)).sub
        (hw)).sub (hid)
    have hX1 := (((((hid).mul (hv)).add ((hid).mul ((hw).pow 2))).add ((hw).const_mul α)).add
        (hw)).sub (hid)
    have hc := ((((((hX1).mul (hX0)).mul (hv)).sub ((hX1).mul (((((((((hv).pow 2).mul (hid)).add
        (((hv).mul (hw)).mul (((((hw).const_mul 2).mul (hid)).const_add β).sub_const 1))).add
        (((hw).pow 4).mul (hid))).add ((hw).pow 3)).add ((hw).mul ((((hw).pow 2).const_mul
        α).add_const β))).sub (hw)).sub (hid)))).add ((hX0).mul (((((((((hv).pow 2).mul (hid)).add
        (((hv).mul (hw)).mul (((((hw).const_mul 2).mul (hid)).const_add α).add_const 1))).add
        (((hw).pow 4).mul (hid))).add ((hw).pow 3)).add ((hw).mul ((((hw).pow 2).const_mul
        α).add_const β))).sub (hw)).sub (hid)))).div (((hX1).pow 2).mul ((hw).pow 2)) (mul_ne_zero
        (pow_ne_zero 2 hd) (pow_ne_zero 2 h0)))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, painleveIIIRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eN : z * b + z * a ^ 2 + β * a - a - z = NN at hn ⊢
      generalize eD : z * b + z * a ^ 2 + α * a + a - z = DD at hd ⊢
      field_simp
      subst eN eD
      ring

/-- DLMF 32.7.10 and 32.7.14, the transformation `T₄`:
`W₄ = (zW₀' - zW₀² + βW₀ - W₀ - z)/(W₀(zW₀' - zW₀² - αW₀ + W₀ - z))` solves `PIII(1, -1)`
with `(α₄, β₄) = (α₀ - 2, β₀ - 2)`. -/
@[dlmf 32.7.E10, dlmf 32.7.E14]
theorem IsPainleveIIIOn.t₄ {α β : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn α β 1 (-1) w U) (hU : IsOpen U)
    (hN : ∀ z ∈ U, z * deriv w z - z * w z ^ 2 + β * w z - w z - z ≠ 0)
    (hD : ∀ z ∈ U, z * deriv w z - z * w z ^ 2 - α * w z + w z - z ≠ 0) :
    IsPainleveIIIOn (α - 2) (β - 2) 1 (-1) (fun z =>
      (z * deriv w z - z * w z ^ 2 + β * w z - w z - z) /
        (w z * (z * deriv w z - z * w z ^ 2 - α * w z + w z - z))) U := by
  refine ⟨?_, h.ne_zero, fun z hz => div_ne_zero (hN z hz) (mul_ne_zero (h.w_ne_zero z hz) (hD z
      hz))⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => ((((((-((((((z * deriv w z) - (z * (w z ^
      2))) - (α * w z)) + w z) - z))) * ((((((z * deriv w z) - (z * (w z ^ 2))) + (β * w z)) - w z)
      - z))) * deriv w z) + (((((((z * deriv w z) - (z * (w z ^ 2))) - (α * w z)) + w z) - z)) *
      ((((((((deriv w z ^ 2) * z) + ((deriv w z * w z) * ((β - ((2 * w z) * z)) - 1))) + ((w z ^ 4)
      * z)) - (w z ^ 3)) + (w z * ((α * (w z ^ 2)) + β))) - w z) - z))) - (((((((z * deriv w z) -
      (z * (w z ^ 2))) + (β * w z)) - w z) - z)) * ((((((((deriv w z ^ 2) * z) + ((deriv w z * w z)
      * (((-α) - ((2 * w z) * z)) + 1))) + ((w z ^ 4) * z)) - (w z ^ 3)) + (w z * ((α * (w z ^ 2))
      + β))) - w z) - z))) / ((((((((z * deriv w z) - (z * (w z ^ 2))) - (α * w z)) + w z) - z)) ^
      2) * (w z ^ 2)))) (fun z hz => ?_) (fun z hz => ?_)
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((((hid).mul (hv)).sub ((hid).mul ((hw).pow 2))).add ((hw).const_mul β)).sub
        (hw)).sub (hid)
    have hX1 := (((((hid).mul (hv)).sub ((hid).mul ((hw).pow 2))).sub ((hw).const_mul α)).add
        (hw)).sub (hid)
    have hc := ((hX0).div ((hw).mul (hX1)) (mul_ne_zero h0 hd))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, painleveIIIRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eN : z * b - z * a ^ 2 + β * a - a - z = NN at hn ⊢
      generalize eD : z * b - z * a ^ 2 - α * a + a - z = DD at hd ⊢
      field_simp
      subst eN eD
      ring
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((((hid).mul (hv)).sub ((hid).mul ((hw).pow 2))).add ((hw).const_mul β)).sub
        (hw)).sub (hid)
    have hX1 := (((((hid).mul (hv)).sub ((hid).mul ((hw).pow 2))).sub ((hw).const_mul α)).add
        (hw)).sub (hid)
    have hc := (((((((hX1).neg).mul (hX0)).mul (hv)).add ((hX1).mul (((((((((hv).pow 2).mul
        (hid)).add (((hv).mul (hw)).mul (((((hw).const_mul 2).mul (hid)).const_sub β).sub_const
        1))).add (((hw).pow 4).mul (hid))).sub ((hw).pow 3)).add ((hw).mul ((((hw).pow 2).const_mul
        α).add_const β))).sub (hw)).sub (hid)))).sub ((hX0).mul (((((((((hv).pow 2).mul (hid)).add
        (((hv).mul (hw)).mul (((((hw).const_mul 2).mul (hid)).const_sub (-α)).add_const 1))).add
        (((hw).pow 4).mul (hid))).sub ((hw).pow 3)).add ((hw).mul ((((hw).pow 2).const_mul
        α).add_const β))).sub (hw)).sub (hid)))).div (((hX1).pow 2).mul ((hw).pow 2)) (mul_ne_zero
        (pow_ne_zero 2 hd) (pow_ne_zero 2 h0)))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, painleveIIIRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eN : z * b - z * a ^ 2 + β * a - a - z = NN at hn ⊢
      generalize eD : z * b - z * a ^ 2 - α * a + a - z = DD at hd ⊢
      field_simp
      subst eN eD
      ring

/-- DLMF 32.7.15–32.7.16, the transformation `T₅` of `PIII` with `γ = 0`, `α = 1`,
`δ = -1`: `u₅ = (zu₀' + z - (β₀ + 1)u₀)/u₀²` solves `PIII(1, β₀ + 2, 0, -1)` where its
numerator does not vanish. -/
@[dlmf 32.7.E15, dlmf 32.7.E16]
theorem IsPainleveIIIOn.t₅ {β : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn 1 β 0 (-1) w U) (hU : IsOpen U)
    (hN : ∀ z ∈ U, z * deriv w z + z - (β + 1) * w z ≠ 0) :
    IsPainleveIIIOn 1 (β + 2) 0 (-1)
      (fun z => (z * deriv w z + z - (β + 1) * w z) / w z ^ 2) U := by
  refine ⟨?_, h.ne_zero, fun z hz => div_ne_zero (hN z hz) (pow_ne_zero 2 (h.w_ne_zero z hz))⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => -(deriv w z ^ 2 * z -
      deriv w z * w z * β - deriv w z * w z + 2 * deriv w z * z - w z ^ 3 - w z * β - w z + z) /
      w z ^ 3) (fun z hz => ?_) (fun z hz => ?_)
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hd := ((((hasDerivAt_id z).mul hv).add (hasDerivAt_id z)).sub
      (hw.const_mul (β + 1))).div (hw.pow 2) (pow_ne_zero 2 h0)
    convert hd using 1
    · funext x
      try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      simp only [painleveIIIRhs]
      field_simp
      ring
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hu0 := hN z hz
    have P := ((((((((hv.pow 2).mul hid).sub ((hv.mul hw).const_mul β)).sub (hv.mul hw)).add
      ((hv.const_mul 2).mul hid)).sub (hw.pow 3)).sub (hw.const_mul β)).sub hw).add hid
    have hd := P.neg.div (hw.pow 3) (pow_ne_zero 3 h0)
    convert hd using 1
    · funext x
      try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      simp only [painleveIIIRhs]
      generalize hn : z * deriv w z + z - (β + 1) * w z = n at hu0 ⊢
      field_simp
      rw [← hn]
      ring

/-- DLMF 32.7.15 and 32.7.17, the transformation `T₆`:
`u₆ = -(zu₀' - z + (β₀ - 1)u₀)/u₀²` solves `PIII(1, β₀ - 2, 0, -1)`. -/
@[dlmf 32.7.E15, dlmf 32.7.E17]
theorem IsPainleveIIIOn.t₆ {β : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn 1 β 0 (-1) w U) (hU : IsOpen U)
    (hN : ∀ z ∈ U, z * deriv w z - z + (β - 1) * w z ≠ 0) :
    IsPainleveIIIOn 1 (β - 2) 0 (-1)
      (fun z => -(z * deriv w z - z + (β - 1) * w z) / w z ^ 2) U := by
  refine ⟨?_, h.ne_zero, fun z hz => div_ne_zero (neg_ne_zero.mpr (hN z hz))
    (pow_ne_zero 2 (h.w_ne_zero z hz))⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => (deriv w z ^ 2 * z +
      deriv w z * w z * β - deriv w z * w z - 2 * deriv w z * z - w z ^ 3 - w z * β + w z + z) /
      w z ^ 3) (fun z hz => ?_) (fun z hz => ?_)
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hd := ((((hasDerivAt_id z).mul hv).sub (hasDerivAt_id z)).add
      (hw.const_mul (β - 1))).neg.div (hw.pow 2) (pow_ne_zero 2 h0)
    convert hd using 1
    · funext x
      try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      simp only [painleveIIIRhs]
      field_simp
      ring
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hz0 := h.ne_zero z hz
    have hu0 := hN z hz
    have P := ((((((((hv.pow 2).mul hid).add ((hv.mul hw).const_mul β)).sub (hv.mul hw)).sub
      ((hv.const_mul 2).mul hid)).sub (hw.pow 3)).sub (hw.const_mul β)).add hw).add hid
    have hd := P.div (hw.pow 3) (pow_ne_zero 3 h0)
    convert hd using 1
    · funext x
      try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      simp only [painleveIIIRhs]
      generalize hn : z * deriv w z - z + (β - 1) * w z = n at hu0 ⊢
      field_simp
      rw [← hn]
      ring

/-- DLMF 32.7.18: `w(z; a, b, 0, 0) = W²(ζ; 0, 0, a, b)` with `z = ζ²/2`. Branch-free: `ζ` is
any function `s` on `U` with `s² = 2z` and `s' = 1/s` (so `s = ±√(2z)`), and `W` solves
`PIII(0, 0, a, b)` near `s(z)`. -/
@[dlmf 32.7.E18]
theorem isPainleveIIIOn_sq_of_isPainleveIIIOn {a b : ℂ} {W s : ℂ → ℂ} {U V : Set ℂ}
    (hW : IsPainleveIIIOn 0 0 a b W V) (hU : IsOpen U)
    (hs : ∀ z ∈ U, s z ^ 2 = 2 * z) (hs' : ∀ z ∈ U, HasDerivAt s (1 / s z) z)
    (hsV : ∀ z ∈ U, s z ∈ V) :
    IsPainleveIIIOn a b 0 0 (fun z => W (s z) ^ 2) U := by
  have hz0' (z : ℂ) (hz : z ∈ U) : z ≠ 0 := by
    intro h0
    have : s z ^ 2 = 0 := by rw [hs z hz, h0, mul_zero]
    exact hW.ne_zero _ (hsV z hz) (pow_eq_zero_iff two_ne_zero |>.mp this)
  refine ⟨?_, hz0', fun z hz => pow_ne_zero 2 (hW.w_ne_zero _ (hsV z hz))⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => (((2 * W (s z)) * deriv W (s z)) / s z))
      (fun z hz => ?_) (fun z hz => ?_)
  · have hm := hsV z hz
    have hS := hs' z hz
    have hX := (hW.ode.hasDerivAt hm).comp z hS
    have hY := (hW.ode.hasDerivAt_deriv _ hm).comp z hS
    have hid := hasDerivAt_id z
    have hS0 := hW.ne_zero _ hm
    have hX0 := hW.w_ne_zero _ hm
    have hz0 := hz0' z hz
    have hs2 : z = s z ^ 2 / 2 := by linear_combination -(hs z hz) / 2
    have hc := (hX).pow 2
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveIIIRhs, Function.comp]
      generalize deriv W (s z) = Y
      generalize W (s z) = X at hX0 ⊢
      generalize s z = S at hS0 hs2 ⊢
      subst hs2
      field_simp
      all_goals set_option maxRecDepth 100000 in ring
  · have hm := hsV z hz
    have hS := hs' z hz
    have hX := (hW.ode.hasDerivAt hm).comp z hS
    have hY := (hW.ode.hasDerivAt_deriv _ hm).comp z hS
    have hid := hasDerivAt_id z
    have hS0 := hW.ne_zero _ hm
    have hX0 := hW.w_ne_zero _ hm
    have hz0 := hz0' z hz
    have hs2 : z = s z ^ 2 / 2 := by linear_combination -(hs z hz) / 2
    have hc := ((((hX).const_mul 2).mul (hY)).div (hS) hS0)
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveIIIRhs, Function.comp]
      generalize deriv W (s z) = Y
      generalize W (s z) = X at hX0 ⊢
      generalize s z = S at hS0 hs2 ⊢
      subst hs2
      field_simp
      all_goals set_option maxRecDepth 100000 in ring

end DLMF.Painleve
end
