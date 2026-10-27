/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Equations
public import DLMF.Painleve.Backlund

/-!
# Bäcklund transformations: DLMF §32.7

The transformations of `PII`–`PVI` in the DLMF normalization. The `PII` transformations come
from the Beals–Wong development (`DLMF.Painleve.Backlund`) through the bridge
`isPainleveIIOn_iff_isPIIOn`. All maps are stated on open sets where their denominators do
not vanish; square roots of parameters (`√(-2β)`, `√(2α)`, …) are replaced by arbitrary
numbers with the right square, so both branches are covered at once.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace DLMF.Painleve

/-! ## `PII` (§32.7(ii)) -/

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
    (hW : IsPainleveIIIOn 0 0 a b W V) (hV : IsOpen V) (hU : IsOpen U)
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

/-! ## `PIV` (§32.7(iv)) -/

/-- DLMF 32.7.19–32.7.20, the transformation `T₁^±` of `PIV`: with `r² = -2β₀`
(`r = ±√(-2β₀)`, the upper sign being `r = √(-2β₀)`),
`w₁ = (w₀' - w₀² - 2zw₀ - r)/(2w₀)` solves `PIV` with
`α₁ = (2 - 2α₀ + 3r)/4`, `β₁ = -(1 + α₀ + r/2)²/2`, where `w₁ ≠ 0`. -/
@[dlmf 32.7.E19, dlmf 32.7.E20]
theorem IsPainleveIVOn.t₁ {α β r : ℂ} (hr : r ^ 2 = -2 * β) {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIVOn α β w U) (hU : IsOpen U)
    (hN : ∀ z ∈ U, deriv w z - w z ^ 2 - 2 * z * w z - r ≠ 0) :
    IsPainleveIVOn ((2 - 2 * α + 3 * r) / 4) (-(1 + α + r / 2) ^ 2 / 2)
      (fun z => (deriv w z - w z ^ 2 - 2 * z * w z - r) / (2 * w z)) U := by
  have hβ : β = -r ^ 2 / 2 := by linear_combination hr / 2
  subst hβ
  refine ⟨?_, fun z hz => div_ne_zero (hN z hz) (mul_ne_zero two_ne_zero (h.w_ne_zero z hz))⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => (-deriv w z ^ 2 -
      2 * deriv w z * w z ^ 2 + 2 * deriv w z * r + 3 * w z ^ 4 + 8 * w z ^ 3 * z -
      4 * w z ^ 2 * α + 4 * w z ^ 2 * z ^ 2 - 4 * w z ^ 2 - r ^ 2) / (4 * w z ^ 2))
    (fun z hz => ?_) (fun z hz => ?_)
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have h0 := h.w_ne_zero z hz
    have hd := (((hv.sub (hw.pow 2)).sub (((hasDerivAt_id z).const_mul 2).mul hw)).sub_const
      r).div (hw.const_mul 2) (mul_ne_zero two_ne_zero h0)
    convert hd using 1
    · funext x
      try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      simp only [painleveIVRhs]
      field_simp
      ring
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hu0 := hN z hz
    have P := ((((((((hv.pow 2).neg.sub ((hv.mul (hw.pow 2)).const_mul 2)).add
      (hv.const_mul (2 * r))).add ((hw.pow 4).const_mul 3)).add
      (((hw.pow 3).mul hid).const_mul 8)).sub ((hw.pow 2).const_mul (4 * α))).add
      (((hw.pow 2).mul (hid.pow 2)).const_mul 4)).sub ((hw.pow 2).const_mul 4)).sub_const (r ^ 2)
    have hd := P.div ((hw.pow 2).const_mul 4)
      (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 2 h0))
    convert hd using 1
    · funext x
      try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      simp only [painleveIVRhs]
      generalize hn : deriv w z - w z ^ 2 - 2 * z * w z - r = n at hu0 ⊢
      field_simp
      rw [← hn]
      ring

/-- DLMF 32.7.19 and 32.7.21, the transformation `T₂^±` of `PIV`: with `r² = -2β₀`,
`w₂ = -(w₀' + w₀² + 2zw₀ - r)/(2w₀)` solves `PIV` with `α₂ = -(2 + 2α₀ + 3r)/4`,
`β₂ = -(1 - α₀ + r/2)²/2`, where `w₂ ≠ 0`. -/
@[dlmf 32.7.E19, dlmf 32.7.E21]
theorem IsPainleveIVOn.t₂ {α β r : ℂ} (hr : r ^ 2 = -2 * β) {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIVOn α β w U) (hU : IsOpen U)
    (hN : ∀ z ∈ U, deriv w z + w z ^ 2 + 2 * z * w z - r ≠ 0) :
    IsPainleveIVOn (-(2 + 2 * α + 3 * r) / 4) (-(1 - α + r / 2) ^ 2 / 2)
      (fun z => -(deriv w z + w z ^ 2 + 2 * z * w z - r) / (2 * w z)) U := by
  have hβ : β = -r ^ 2 / 2 := by linear_combination hr / 2
  subst hβ
  refine ⟨?_, fun z hz => div_ne_zero (neg_ne_zero.mpr (hN z hz))
    (mul_ne_zero two_ne_zero (h.w_ne_zero z hz))⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => -(-deriv w z ^ 2 +
      2 * deriv w z * w z ^ 2 + 2 * deriv w z * r + 3 * w z ^ 4 + 8 * w z ^ 3 * z -
      4 * w z ^ 2 * α + 4 * w z ^ 2 * z ^ 2 + 4 * w z ^ 2 - r ^ 2) / (4 * w z ^ 2))
    (fun z hz => ?_) (fun z hz => ?_)
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have h0 := h.w_ne_zero z hz
    have hd := (((hv.add (hw.pow 2)).add (((hasDerivAt_id z).const_mul 2).mul hw)).sub_const
      r).neg.div (hw.const_mul 2) (mul_ne_zero two_ne_zero h0)
    convert hd using 1
    · funext x
      try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      simp only [painleveIVRhs]
      field_simp
      ring
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hu0 := hN z hz
    have P := ((((((((hv.pow 2).neg.add ((hv.mul (hw.pow 2)).const_mul 2)).add
      (hv.const_mul (2 * r))).add ((hw.pow 4).const_mul 3)).add
      (((hw.pow 3).mul hid).const_mul 8)).sub ((hw.pow 2).const_mul (4 * α))).add
      (((hw.pow 2).mul (hid.pow 2)).const_mul 4)).add ((hw.pow 2).const_mul 4)).sub_const (r ^ 2)
    have hd := P.neg.div ((hw.pow 2).const_mul 4)
      (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 2 h0))
    convert hd using 1
    · funext x
      try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      simp only [painleveIVRhs]
      generalize hn : deriv w z + w z ^ 2 + 2 * z * w z - r = n at hu0 ⊢
      field_simp
      rw [← hn]
      ring

/-- DLMF 32.7.19 and 32.7.22, the transformation `T₃^±` of `PIV`: with `r² = -2β₀`,
`w₃ = w₀ + 2(1 - α₀ - r/2)w₀/(w₀' + r + 2zw₀ + w₀²)` solves `PIV` with
`α₃ = 3/2 - α₀/2 - 3r/4`, `β₃ = -(1 - α₀ + r/2)²/2`, where the denominator and `w₃` do not
vanish. -/
@[dlmf 32.7.E19, dlmf 32.7.E22]
theorem IsPainleveIVOn.t₃ {α β r : ℂ} (hr : r ^ 2 = -2 * β) {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIVOn α β w U) (hU : IsOpen U)
    (hD : ∀ z ∈ U, deriv w z + r + 2 * z * w z + w z ^ 2 ≠ 0)
    (hN : ∀ z ∈ U, w z + 2 * (1 - α - r / 2) * w z /
      (deriv w z + r + 2 * z * w z + w z ^ 2) ≠ 0) :
    IsPainleveIVOn (3 / 2 - α / 2 - 3 * r / 4) (-(1 - α + r / 2) ^ 2 / 2)
      (fun z => w z + 2 * (1 - α - r / 2) * w z / (deriv w z + r + 2 * z * w z + w z ^ 2)) U := by
  have hβ : β = -r ^ 2 / 2 := by linear_combination hr / 2
  subst hβ
  refine ⟨?_, hN⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => (((((2 * ((((deriv w z + r) + ((2 * z) *
      w z)) + (w z ^ 2)))) * deriv w z) * (((((((deriv w z + r) + ((2 * z) * w z)) + (w z ^ 2))) -
      (2 * α)) - r) + 2)) - (((((-2) * α) - r) + 2) * (((((((-(r ^ 2)) + (deriv w z ^ 2)) + (((4 *
      deriv w z) * w z) * (w z + z))) + (3 * (w z ^ 4))) + ((8 * (w z ^ 3)) * z)) + ((4 * (w z ^
      2)) * ((-α) + (z ^ 2)))) + (4 * (w z ^ 2))))) / (2 * (((((deriv w z + r) + ((2 * z) * w z)) +
      (w z ^ 2))) ^ 2)))) (fun z hz => ?_) (fun z hz => ?_)
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((hv).add_const r).add (((hid).const_mul 2).mul (hw))).add ((hw).pow 2)
    have hc := (hw).add ((((hw).const_mul (2 * ((1 - α) - (r / 2)))).div (hX0) hd))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveIVRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eD : b + r + 2 * z * a + a ^ 2 = DD at hn hd ⊢
      have hn' : DD + 2 * (1 - α - r / 2) ≠ 0 := by
        intro hc; apply hn; field_simp; linear_combination a * hc
      try rw [show a + 2 * (1 - α - r / 2) * a / DD = a * (DD + 2 * (1 - α - r / 2)) / DD by
          field_simp]
      generalize eM : DD + 2 * (1 - α - r / 2) = MM at hn' ⊢
      field_simp
      subst eM eD
      set_option maxRecDepth 100000 in ring
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((hv).add_const r).add (((hid).const_mul 2).mul (hw))).add ((hw).pow 2)
    have hc := ((((((hX0).const_mul 2).mul (hv)).mul ((((hX0).sub_const (2 * α)).sub_const
        r).add_const 2)).sub (((((((((hv).pow 2).const_add (-(r ^ 2))).add ((((hv).const_mul 4).mul
        (hw)).mul ((hw).add (hid)))).add (((hw).pow 4).const_mul 3)).add ((((hw).pow 3).const_mul
        8).mul (hid))).add ((((hw).pow 2).const_mul 4).mul (((hid).pow 2).const_add (-α)))).add
        (((hw).pow 2).const_mul 4)).const_mul ((((-2) * α) - r) + 2))).div (((hX0).pow 2).const_mul
        2) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hd)))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveIVRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eD : b + r + 2 * z * a + a ^ 2 = DD at hn hd ⊢
      have hn' : DD + 2 * (1 - α - r / 2) ≠ 0 := by
        intro hc; apply hn; field_simp; linear_combination a * hc
      try rw [show a + 2 * (1 - α - r / 2) * a / DD = a * (DD + 2 * (1 - α - r / 2)) / DD by
          field_simp]
      generalize eM : DD + 2 * (1 - α - r / 2) = MM at hn' ⊢
      field_simp
      subst eM eD
      set_option maxRecDepth 100000 in ring

/-- DLMF 32.7.19 and 32.7.23, the transformation `T₄^±` of `PIV`: with `r² = -2β₀`,
`w₄ = w₀ + 2(1 + α₀ + r/2)w₀/(w₀' - r - 2zw₀ - w₀²)` solves `PIV` with
`α₄ = -3/2 - α₀/2 - 3r/4`, `β₄ = -(-1 - α₀ + r/2)²/2`. -/
@[dlmf 32.7.E19, dlmf 32.7.E23]
theorem IsPainleveIVOn.t₄ {α β r : ℂ} (hr : r ^ 2 = -2 * β) {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIVOn α β w U) (hU : IsOpen U)
    (hD : ∀ z ∈ U, deriv w z - r - 2 * z * w z - w z ^ 2 ≠ 0)
    (hN : ∀ z ∈ U, w z + 2 * (1 + α + r / 2) * w z /
      (deriv w z - r - 2 * z * w z - w z ^ 2) ≠ 0) :
    IsPainleveIVOn (-3 / 2 - α / 2 - 3 * r / 4) (-(-1 - α + r / 2) ^ 2 / 2)
      (fun z => w z + 2 * (1 + α + r / 2) * w z / (deriv w z - r - 2 * z * w z - w z ^ 2)) U := by
  have hβ : β = -r ^ 2 / 2 := by linear_combination hr / 2
  subst hβ
  refine ⟨?_, hN⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => (((((2 * ((((deriv w z - r) - ((2 * z) *
      w z)) - (w z ^ 2)))) * deriv w z) * (((((((deriv w z - r) - ((2 * z) * w z)) - (w z ^ 2))) +
      (2 * α)) + r) + 2)) - ((((2 * α) + r) + 2) * (((((((-(r ^ 2)) + (deriv w z ^ 2)) + (((4 *
      deriv w z) * w z) * ((-w z) - z))) + (3 * (w z ^ 4))) + ((8 * (w z ^ 3)) * z)) + ((4 * (w z ^
      2)) * ((-α) + (z ^ 2)))) - (4 * (w z ^ 2))))) / (2 * (((((deriv w z - r) - ((2 * z) * w z)) -
      (w z ^ 2))) ^ 2)))) (fun z hz => ?_) (fun z hz => ?_)
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((hv).sub_const r).sub (((hid).const_mul 2).mul (hw))).sub ((hw).pow 2)
    have hc := (hw).add ((((hw).const_mul (2 * ((1 + α) + (r / 2)))).div (hX0) hd))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveIVRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eD : b - r - 2 * z * a - a ^ 2 = DD at hn hd ⊢
      have hn' : DD + 2 * (1 + α + r / 2) ≠ 0 := by
        intro hc; apply hn; field_simp; linear_combination a * hc
      try rw [show a + 2 * (1 + α + r / 2) * a / DD = a * (DD + 2 * (1 + α + r / 2)) / DD by
          field_simp]
      generalize eM : DD + 2 * (1 + α + r / 2) = MM at hn' ⊢
      field_simp
      subst eM eD
      set_option maxRecDepth 100000 in ring
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have hn := hN z hz
    have hd := hD z hz
    have hX0 := (((hv).sub_const r).sub (((hid).const_mul 2).mul (hw))).sub ((hw).pow 2)
    have hc := ((((((hX0).const_mul 2).mul (hv)).mul ((((hX0).add_const (2 * α)).add_const
        r).add_const 2)).sub (((((((((hv).pow 2).const_add (-(r ^ 2))).add ((((hv).const_mul 4).mul
        (hw)).mul (((hw).neg).sub (hid)))).add (((hw).pow 4).const_mul 3)).add ((((hw).pow
        3).const_mul 8).mul (hid))).add ((((hw).pow 2).const_mul 4).mul (((hid).pow 2).const_add
        (-α)))).sub (((hw).pow 2).const_mul 4)).const_mul (((2 * α) + r) + 2))).div (((hX0).pow
        2).const_mul 2) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hd)))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveIVRhs]
      generalize deriv w z = b at hn hd ⊢
      generalize w z = a at h0 hn hd ⊢
      generalize eD : b - r - 2 * z * a - a ^ 2 = DD at hn hd ⊢
      have hn' : DD + 2 * (1 + α + r / 2) ≠ 0 := by
        intro hc; apply hn; field_simp; linear_combination a * hc
      try rw [show a + 2 * (1 + α + r / 2) * a / DD = a * (DD + 2 * (1 + α + r / 2)) / DD by
          field_simp]
      generalize eM : DD + 2 * (1 + α + r / 2) = MM at hn' ⊢
      field_simp
      subst eM eD
      set_option maxRecDepth 100000 in ring

/-! ## `PV` (§32.7(v)) -/

/-- DLMF 32.7.24–32.7.25, the transformation `S₁` of `PV`: `w₁(z₁) = w(z₀)` with
`z₁ = -z₀`, that is `w₁(ζ) = w(-ζ)`, solves `PV(α₀, β₀, -γ₀, δ₀)`. -/
@[dlmf 32.7.E24, dlmf 32.7.E25]
theorem IsPainleveVOn.comp_neg {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVOn α β γ δ w U) (hU : IsOpen U) :
    IsPainleveVOn α β (-γ) δ (fun ζ => w (-ζ)) ((fun ζ : ℂ => -ζ) ⁻¹' U) := by
  have hV : IsOpen ((fun ζ : ℂ => -ζ) ⁻¹' U) := hU.preimage continuous_neg
  have hW := h.ode.affine hV (a := 0) (b := 1) (c := 0) (d := -1) one_ne_zero
    (neg_ne_zero.mpr one_ne_zero) (fun ζ hζ => by simpa using hζ)
  refine ⟨?_, fun ζ hζ => by simpa using h.ne_zero _ hζ, fun ζ hζ => h.w_ne_zero _ hζ,
    fun ζ hζ => h.w_ne_one _ hζ⟩
  have he : (fun ζ => (w (0 + -1 * ζ) - 0) / 1) = fun ζ => w (-ζ) := by funext ζ; simp
  rw [he] at hW
  refine hW.congr_rhs fun ζ hζ => ?_
  have h0 := h.w_ne_zero _ hζ
  have h1 : w (-ζ) - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one _ hζ)
  have hz : -ζ ≠ 0 := h.ne_zero _ hζ
  have hz' : ζ ≠ 0 := by simpa using hz
  simp only [painleveVRhs, zero_add, one_mul, neg_mul, one_mul]
  field_simp

/-- DLMF 32.7.24 and 32.7.26, the transformation `S₂` of `PV`: `w₂ = 1/w` solves
`PV(-β₀, -α₀, -γ₀, δ₀)`. -/
@[dlmf 32.7.E24, dlmf 32.7.E26]
theorem IsPainleveVOn.inv {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVOn α β γ δ w U) (hU : IsOpen U) :
    IsPainleveVOn (-β) (-α) (-γ) δ (fun z => (w z)⁻¹) U := by
  refine ⟨?_, h.ne_zero, fun z hz => inv_ne_zero (h.w_ne_zero z hz), fun z hz => ?_⟩
  · refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => -deriv w z / w z ^ 2)
      (fun z hz => ?_) (fun z hz => ?_)
    · exact ((h.ode.hasDerivAt hz).inv (h.w_ne_zero z hz)).congr_deriv (by ring)
    · have h0 := h.w_ne_zero z hz
      have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
      have h1' : 1 - w z ≠ 0 := by intro h2; exact h1 (by linear_combination -h2)
      have hz0 := h.ne_zero z hz
      refine ((h.ode.hasDerivAt_deriv z hz).neg.div ((h.ode.hasDerivAt hz).pow 2)
        (pow_ne_zero 2 h0)).congr_deriv ?_
      simp only [painleveVRhs, Pi.pow_apply, Pi.neg_apply]
      field_simp
      ring
  · intro h2
    exact h.w_ne_one z hz (by rw [← inv_inv (w z), h2, inv_one])

/-- DLMF 32.7.27–32.7.29, the transformations `T_{ε₁,ε₂,ε₃}` of `PV` with `δ = -1/2`.
Branch-free: `A` and `B` are any numbers with `A² = 2α₀`, `B² = -2β₀` (in place of `√(2α₀)`,
`√(-2β₀)`), and `ε_j² = 1`. With
`Φ = zW₀' - ε₂AW₀² + ε₃B + (ε₂A - ε₃B + ε₁z)W₀ ≠ 0`, the function `W₁ = (Φ - 2ε₁zW₀)/Φ`
solves `PV` with `α₁ = (γ₀ + ε₁(1 - ε₃B - ε₂A))²/8`, `β₁ = -(γ₀ - ε₁(1 - ε₃B - ε₂A))²/8`,
`γ₁ = ε₁(ε₃B - ε₂A)`, `δ₁ = -1/2`, where the numerator does not vanish. -/
@[dlmf 32.7.E27, dlmf 32.7.E28, dlmf 32.7.E29]
theorem IsPainleveVOn.t_eps {α β γ A B ε₁ ε₂ ε₃ : ℂ} (hA : A ^ 2 = 2 * α) (hB : B ^ 2 = -2 * β)
    (h₁ : ε₁ ^ 2 = 1) (h₂ : ε₂ ^ 2 = 1) (h₃ : ε₃ ^ 2 = 1) {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVOn α β γ (-1 / 2) w U) (hU : IsOpen U)
    (hΦ : ∀ z ∈ U, z * deriv w z - ε₂ * A * w z ^ 2 + ε₃ * B +
      (ε₂ * A - ε₃ * B + ε₁ * z) * w z ≠ 0)
    (hN : ∀ z ∈ U, z * deriv w z - ε₂ * A * w z ^ 2 + ε₃ * B +
      (ε₂ * A - ε₃ * B + ε₁ * z) * w z - 2 * ε₁ * z * w z ≠ 0) :
    IsPainleveVOn ((γ + ε₁ * (1 - ε₃ * B - ε₂ * A)) ^ 2 / 8)
      (-(γ - ε₁ * (1 - ε₃ * B - ε₂ * A)) ^ 2 / 8) (ε₁ * (ε₃ * B - ε₂ * A)) (-1 / 2)
      (fun z => (z * deriv w z - ε₂ * A * w z ^ 2 + ε₃ * B + (ε₂ * A - ε₃ * B + ε₁ * z) * w z -
        2 * ε₁ * z * w z) / (z * deriv w z - ε₂ * A * w z ^ 2 + ε₃ * B +
          (ε₂ * A - ε₃ * B + ε₁ * z) * w z)) U := by
  have hA' : (ε₂ * A) ^ 2 = 2 * α := by rw [mul_pow, h₂, one_mul, hA]
  have hB' : (ε₃ * B) ^ 2 = -2 * β := by rw [mul_pow, h₃, one_mul, hB]
  generalize ε₂ * A = A' at hA' hΦ hN ⊢
  generalize ε₃ * B = B' at hB' hΦ hN ⊢
  have hα : α = A' ^ 2 / 2 := by linear_combination -hA' / 2
  have hβ : β = -B' ^ 2 / 2 := by linear_combination hB' / 2
  subst hα hβ
  rcases mul_self_eq_one_iff.mp (show ε₁ * ε₁ = 1 by rw [← sq]; exact h₁) with rfl | rfl
  · refine ⟨?_, h.ne_zero, fun z hz => div_ne_zero (hN z hz) (hΦ z hz), fun z hz h1 => ?_⟩
    swap
    · have := (div_eq_one_iff_eq (hΦ z hz)).mp h1
      exact mul_ne_zero (h.ne_zero z hz) (h.w_ne_zero z hz) (by linear_combination - this / 2)
    refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => ((((-(((((((z * deriv w z) - (A' * (w z
        ^ 2))) + B') + (((A' - B') + (1 * z)) * w z))) - (((2 * 1) * z) * w z)))) * (((((((((2 * γ)
        * (w z ^ 2)) * z) * (w z - 1)) + (((deriv w z ^ 2) * (z ^ 2)) * ((3 * w z) - 1))) + (((((2
        * deriv w z) * w z) * z) * (w z - 1)) * ((((((-2) * A') * w z) + A') - B') + z))) - (((w z
        ^ 2) * (z ^ 2)) * (w z + 1))) + (((2 * (w z ^ 2)) * z) * (w z - 1))) + (((w z - 1) ^ 3) *
        (((A' ^ 2) * (w z ^ 2)) - (B' ^ 2))))) + ((((((z * deriv w z) - (A' * (w z ^ 2))) + B') +
        (((A' - B') + (1 * z)) * w z))) * ((((((((((2 * γ) * (w z ^ 2)) * z) * (w z - 1)) +
        (((deriv w z ^ 2) * (z ^ 2)) * ((3 * w z) - 1))) - ((((4 * deriv w z) * w z) * (z ^ 2)) *
        (w z - 1))) + (((((2 * deriv w z) * w z) * z) * (w z - 1)) * ((((((-2) * A') * w z) + A') -
        B') + z))) - (((w z ^ 2) * (z ^ 2)) * (w z + 1))) - (((2 * (w z ^ 2)) * z) * (w z - 1))) +
        (((w z - 1) ^ 3) * (((A' ^ 2) * (w z ^ 2)) - (B' ^ 2)))))) / ((((2 * ((((((z * deriv w z) -
        (A' * (w z ^ 2))) + B') + (((A' - B') + (1 * z)) * w z))) ^ 2)) * w z) * z) * (w z - 1))))
        (fun z hz => ?_) (fun z hz => ?_)
    · have hw := h.ode.hasDerivAt hz
      have hv := h.ode.hasDerivAt_deriv z hz
      have hid := hasDerivAt_id z
      have h0 := h.w_ne_zero z hz
      have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
      have hz0 := h.ne_zero z hz
      have hn := hN z hz
      have hp := hΦ z hz
      have hX0 := ((((hid).mul (hv)).sub (((hw).pow 2).const_mul A')).add_const B').add
          ((((hid).const_mul 1).const_add (A' - B')).mul (hw))
      have hX1 := (hX0).sub (((hid).const_mul (2 * 1)).mul (hw))
      have hc := ((hX1).div (hX0) hp)
      convert hc using 1
      · funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
            Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
        try ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs]
        generalize deriv w z = b at hn hp ⊢
        generalize w z = a at h0 h1 hn hp ⊢
        generalize eP : z * b - A' * a ^ 2 + B' + (A' - B' + 1 * z) * a = PP at hn hp ⊢
        try rw [show (PP - 2 * 1 * z * a) / PP - 1 = -(2 * 1 * z * a) / PP by field_simp; ring]
        generalize eN : PP - 2 * 1 * z * a = NN at hn ⊢
        field_simp
        subst eN eP
        set_option maxRecDepth 100000 in ring
    · have hw := h.ode.hasDerivAt hz
      have hv := h.ode.hasDerivAt_deriv z hz
      have hid := hasDerivAt_id z
      have h0 := h.w_ne_zero z hz
      have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
      have hz0 := h.ne_zero z hz
      have hn := hN z hz
      have hp := hΦ z hz
      have hX0 := ((((hid).mul (hv)).sub (((hw).pow 2).const_mul A')).add_const B').add
          ((((hid).const_mul 1).const_add (A' - B')).mul (hw))
      have hX1 := (hX0).sub (((hid).const_mul (2 * 1)).mul (hw))
      have hc := (((((hX1).neg).mul ((((((((((hw).pow 2).const_mul (2 * γ)).mul (hid)).mul
          ((hw).sub_const 1)).add ((((hv).pow 2).mul ((hid).pow 2)).mul (((hw).const_mul
          3).sub_const 1))).add ((((((hv).const_mul 2).mul (hw)).mul (hid)).mul ((hw).sub_const
          1)).mul (((((hw).const_mul ((-2) * A')).add_const A').sub_const B').add (hid)))).sub
          ((((hw).pow 2).mul ((hid).pow 2)).mul ((hw).add_const 1))).add (((((hw).pow 2).const_mul
          2).mul (hid)).mul ((hw).sub_const 1))).add ((((hw).sub_const 1).pow 3).mul ((((hw).pow
          2).const_mul (A' ^ 2)).sub_const (B' ^ 2))))).add ((hX0).mul (((((((((((hw).pow
          2).const_mul (2 * γ)).mul (hid)).mul ((hw).sub_const 1)).add ((((hv).pow 2).mul
          ((hid).pow 2)).mul (((hw).const_mul 3).sub_const 1))).sub (((((hv).const_mul 4).mul
          (hw)).mul ((hid).pow 2)).mul ((hw).sub_const 1))).add ((((((hv).const_mul 2).mul
          (hw)).mul (hid)).mul ((hw).sub_const 1)).mul (((((hw).const_mul ((-2) * A')).add_const
          A').sub_const B').add (hid)))).sub ((((hw).pow 2).mul ((hid).pow 2)).mul ((hw).add_const
          1))).sub (((((hw).pow 2).const_mul 2).mul (hid)).mul ((hw).sub_const 1))).add
          ((((hw).sub_const 1).pow 3).mul ((((hw).pow 2).const_mul (A' ^ 2)).sub_const (B' ^
          2)))))).div ((((((hX0).pow 2).const_mul 2).mul (hw)).mul (hid)).mul ((hw).sub_const 1))
          (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp)) h0)
          hz0) (by assumption)))
      convert hc using 1
      · funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
            Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
        try ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs]
        generalize deriv w z = b at hn hp ⊢
        generalize w z = a at h0 h1 hn hp ⊢
        generalize eP : z * b - A' * a ^ 2 + B' + (A' - B' + 1 * z) * a = PP at hn hp ⊢
        try rw [show (PP - 2 * 1 * z * a) / PP - 1 = -(2 * 1 * z * a) / PP by field_simp; ring]
        generalize eN : PP - 2 * 1 * z * a = NN at hn ⊢
        field_simp
        subst eN eP
        set_option maxRecDepth 100000 in ring

  · refine ⟨?_, h.ne_zero, fun z hz => div_ne_zero (hN z hz) (hΦ z hz), fun z hz h1 => ?_⟩
    swap
    · have := (div_eq_one_iff_eq (hΦ z hz)).mp h1
      exact mul_ne_zero (h.ne_zero z hz) (h.w_ne_zero z hz) (by linear_combination  this / 2)
    refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => ((((-(((((((z * deriv w z) - (A' * (w z
        ^ 2))) + B') + (((A' - B') + ((-1) * z)) * w z))) - (((2 * (-1)) * z) * w z)))) *
        (((((((((2 * γ) * (w z ^ 2)) * z) * (w z - 1)) + (((deriv w z ^ 2) * (z ^ 2)) * ((3 * w z)
        - 1))) + (((((2 * deriv w z) * w z) * z) * (w z - 1)) * ((((((-2) * A') * w z) + A') - B')
        - z))) - (((w z ^ 2) * (z ^ 2)) * (w z + 1))) - (((2 * (w z ^ 2)) * z) * (w z - 1))) + (((w
        z - 1) ^ 3) * (((A' ^ 2) * (w z ^ 2)) - (B' ^ 2))))) + ((((((z * deriv w z) - (A' * (w z ^
        2))) + B') + (((A' - B') + ((-1) * z)) * w z))) * ((((((((((2 * γ) * (w z ^ 2)) * z) * (w z
        - 1)) + (((deriv w z ^ 2) * (z ^ 2)) * ((3 * w z) - 1))) + ((((4 * deriv w z) * w z) * (z ^
        2)) * (w z - 1))) + (((((2 * deriv w z) * w z) * z) * (w z - 1)) * ((((((-2) * A') * w z) +
        A') - B') - z))) - (((w z ^ 2) * (z ^ 2)) * (w z + 1))) + (((2 * (w z ^ 2)) * z) * (w z -
        1))) + (((w z - 1) ^ 3) * (((A' ^ 2) * (w z ^ 2)) - (B' ^ 2)))))) / ((((2 * ((((((z * deriv
        w z) - (A' * (w z ^ 2))) + B') + (((A' - B') + ((-1) * z)) * w z))) ^ 2)) * w z) * z) * (w
        z - 1)))) (fun z hz => ?_) (fun z hz => ?_)
    · have hw := h.ode.hasDerivAt hz
      have hv := h.ode.hasDerivAt_deriv z hz
      have hid := hasDerivAt_id z
      have h0 := h.w_ne_zero z hz
      have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
      have hz0 := h.ne_zero z hz
      have hn := hN z hz
      have hp := hΦ z hz
      have hX0 := ((((hid).mul (hv)).sub (((hw).pow 2).const_mul A')).add_const B').add
          ((((hid).const_mul (-1)).const_add (A' - B')).mul (hw))
      have hX1 := (hX0).sub (((hid).const_mul (2 * (-1))).mul (hw))
      have hc := ((hX1).div (hX0) hp)
      convert hc using 1
      · funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
            Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
        try ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs]
        generalize deriv w z = b at hn hp ⊢
        generalize w z = a at h0 h1 hn hp ⊢
        generalize eP : z * b - A' * a ^ 2 + B' + (A' - B' + -1 * z) * a = PP at hn hp ⊢
        try rw [show (PP - 2 * -1 * z * a) / PP - 1 = -(2 * -1 * z * a) / PP by field_simp; ring]
        generalize eN : PP - 2 * -1 * z * a = NN at hn ⊢
        field_simp
        subst eN eP
        set_option maxRecDepth 100000 in ring
    · have hw := h.ode.hasDerivAt hz
      have hv := h.ode.hasDerivAt_deriv z hz
      have hid := hasDerivAt_id z
      have h0 := h.w_ne_zero z hz
      have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
      have hz0 := h.ne_zero z hz
      have hn := hN z hz
      have hp := hΦ z hz
      have hX0 := ((((hid).mul (hv)).sub (((hw).pow 2).const_mul A')).add_const B').add
          ((((hid).const_mul (-1)).const_add (A' - B')).mul (hw))
      have hX1 := (hX0).sub (((hid).const_mul (2 * (-1))).mul (hw))
      have hc := (((((hX1).neg).mul ((((((((((hw).pow 2).const_mul (2 * γ)).mul (hid)).mul
          ((hw).sub_const 1)).add ((((hv).pow 2).mul ((hid).pow 2)).mul (((hw).const_mul
          3).sub_const 1))).add ((((((hv).const_mul 2).mul (hw)).mul (hid)).mul ((hw).sub_const
          1)).mul (((((hw).const_mul ((-2) * A')).add_const A').sub_const B').sub (hid)))).sub
          ((((hw).pow 2).mul ((hid).pow 2)).mul ((hw).add_const 1))).sub (((((hw).pow 2).const_mul
          2).mul (hid)).mul ((hw).sub_const 1))).add ((((hw).sub_const 1).pow 3).mul ((((hw).pow
          2).const_mul (A' ^ 2)).sub_const (B' ^ 2))))).add ((hX0).mul (((((((((((hw).pow
          2).const_mul (2 * γ)).mul (hid)).mul ((hw).sub_const 1)).add ((((hv).pow 2).mul
          ((hid).pow 2)).mul (((hw).const_mul 3).sub_const 1))).add (((((hv).const_mul 4).mul
          (hw)).mul ((hid).pow 2)).mul ((hw).sub_const 1))).add ((((((hv).const_mul 2).mul
          (hw)).mul (hid)).mul ((hw).sub_const 1)).mul (((((hw).const_mul ((-2) * A')).add_const
          A').sub_const B').sub (hid)))).sub ((((hw).pow 2).mul ((hid).pow 2)).mul ((hw).add_const
          1))).add (((((hw).pow 2).const_mul 2).mul (hid)).mul ((hw).sub_const 1))).add
          ((((hw).sub_const 1).pow 3).mul ((((hw).pow 2).const_mul (A' ^ 2)).sub_const (B' ^
          2)))))).div ((((((hX0).pow 2).const_mul 2).mul (hw)).mul (hid)).mul ((hw).sub_const 1))
          (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp)) h0)
          hz0) (by assumption)))
      convert hc using 1
      · funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
            Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
        try ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs]
        generalize deriv w z = b at hn hp ⊢
        generalize w z = a at h0 h1 hn hp ⊢
        generalize eP : z * b - A' * a ^ 2 + B' + (A' - B' + -1 * z) * a = PP at hn hp ⊢
        try rw [show (PP - 2 * -1 * z * a) / PP - 1 = -(2 * -1 * z * a) / PP by field_simp; ring]
        generalize eN : PP - 2 * -1 * z * a = NN at hn ⊢
        field_simp
        subst eN eP
        set_option maxRecDepth 100000 in ring

/-! ## `PIII` and `PV` (§32.7(vi)) -/

/-- DLMF 32.7.30–32.7.32: for a solution `w` of `PIII(α, β, 1, -1)` and `ε = ±1`, put
`v = w' - εw² + (1 - εα)w/z`. Then `W(ζ) = (v - 1)/(v + 1)` with `z = √(2ζ)` solves `PV` with
`(α₀, β₀, γ₀, δ₀) = ((β - εα + 2)²/32, -(β + εα - 2)²/32, -ε, 0)`. Branch-free: `√(2ζ)` is
any function `s` on `V` with `s² = 2ζ`, `s' = 1/s`, mapping `V` into `U`, and
`W(ζ) = (v(s ζ) - 1)/(v(s ζ) + 1)`. -/
@[dlmf 32.7.E30, dlmf 32.7.E31, dlmf 32.7.E32]
theorem IsPainleveIIIOn.toPainleveV {α β ε : ℂ} (hε : ε ^ 2 = 1) {w s : ℂ → ℂ} {U V : Set ℂ}
    (h : IsPainleveIIIOn α β 1 (-1) w U) (hU : IsOpen U) (hV : IsOpen V)
    (hs : ∀ ζ ∈ V, s ζ ^ 2 = 2 * ζ) (hs' : ∀ ζ ∈ V, HasDerivAt s (1 / s ζ) ζ)
    (hsU : ∀ ζ ∈ V, s ζ ∈ U)
    (hv1 : ∀ ζ ∈ V, deriv w (s ζ) - ε * w (s ζ) ^ 2 + (1 - ε * α) * w (s ζ) / s ζ ≠ 1)
    (hv2 : ∀ ζ ∈ V, deriv w (s ζ) - ε * w (s ζ) ^ 2 + (1 - ε * α) * w (s ζ) / s ζ ≠ -1) :
    IsPainleveVOn ((β - ε * α + 2) ^ 2 / 32) (-(β + ε * α - 2) ^ 2 / 32) (-ε) 0
      (fun ζ => (deriv w (s ζ) - ε * w (s ζ) ^ 2 + (1 - ε * α) * w (s ζ) / s ζ - 1) /
        (deriv w (s ζ) - ε * w (s ζ) ^ 2 + (1 - ε * α) * w (s ζ) / s ζ + 1)) V := by
  have hz0' (z : ℂ) (hz : z ∈ V) : z ≠ 0 := by
    intro h0
    have : s z ^ 2 = 0 := by rw [hs z hz, h0, mul_zero]
    exact h.ne_zero _ (hsU z hz) (pow_eq_zero_iff two_ne_zero |>.mp this)
  refine ⟨?_, hz0', fun z hz => div_ne_zero (sub_ne_zero.mpr (hv1 z hz))
    (fun h' => hv2 z hz (by linear_combination h')), fun z hz h' => ?_⟩
  swap
  · rw [div_eq_one_iff_eq (fun h' => hv2 z hz (by linear_combination h'))] at h'
    exact two_ne_zero (by linear_combination -h' : (2 : ℂ) = 0)
  rcases mul_self_eq_one_iff.mp (show ε * ε = 1 by rw [← sq]; exact hε) with rfl | rfl
  · refine isODE2SolutionOn_of_hasDerivAt hV (v := fun z => ((2 * (((((s z * w (s z)) * deriv w (s
      z)) * (((((-2) * s z) * w (s z)) - α) + 1)) + (s z * (((((s z * (w (s z) ^ 4)) + (s z *
      (deriv w (s z) ^ 2))) - s z) - (w (s z) * deriv w (s z))) + (w (s z) * (((w (s z) ^ 2) * α) +
      β))))) - ((w (s z) ^ 2) * (1 - α)))) / (((s z ^ 3) * w (s z)) * (((((deriv w (s z) - (1 * (w
      (s z) ^ 2))) + (((1 - (1 * α)) * w (s z)) / s z))) + 1) ^ 2)))) (fun z hz => ?_) (fun z hz =>
      ?_)
    · have hm := hsU z hz
      have hS := hs' z hz
      have hX := (h.ode.hasDerivAt hm).comp z hS
      have hY := (h.ode.hasDerivAt_deriv _ hm).comp z hS
      have hid := hasDerivAt_id z
      have hS0 := h.ne_zero _ hm
      have hX0 := h.w_ne_zero _ hm
      have hz0 := hz0' z hz
      have hv1 : deriv w (s z) - 1 * w (s z) ^ 2 + (1 - 1 * α) * w (s z) / s z - 1 ≠ 0 :=
          sub_ne_zero.mpr (hv1 z hz)
      have hv2 : deriv w (s z) - 1 * w (s z) ^ 2 + (1 - 1 * α) * w (s z) / s z + 1 ≠ 0 := fun h' =>
          hv2 z hz (by linear_combination h')
      have hs2 : z = s z ^ 2 / 2 := by linear_combination -(hs z hz) / 2
      have hE0 := ((hY).sub (((hX).pow 2).const_mul 1)).add ((((hX).const_mul (1 - (1 * α))).div
          (hS) hS0))
      have hc := (((hE0).sub_const 1).div ((hE0).add_const 1) hv2)
      convert hc using 1
      · funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
            Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp]
        try ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs, painleveIIIRhs,
          Function.comp]
        generalize deriv w (s z) = Y at hv1 hv2 ⊢
        generalize w (s z) = X at hX0 hv1 hv2 ⊢
        generalize s z = S at hS0 hs2 hv1 hv2 ⊢
        subst hs2
        generalize eV : Y - 1 * X ^ 2 + (1 - 1 * α) * X / S = VV at hv1 hv2 ⊢
        try rw [show (VV - 1) / (VV + 1) - 1 = -2 / (VV + 1) by field_simp; ring]
        field_simp
        subst eV
        field_simp
        all_goals set_option maxRecDepth 100000 in ring
    · have hm := hsU z hz
      have hS := hs' z hz
      have hX := (h.ode.hasDerivAt hm).comp z hS
      have hY := (h.ode.hasDerivAt_deriv _ hm).comp z hS
      have hid := hasDerivAt_id z
      have hS0 := h.ne_zero _ hm
      have hX0 := h.w_ne_zero _ hm
      have hz0 := hz0' z hz
      have hv1 : deriv w (s z) - 1 * w (s z) ^ 2 + (1 - 1 * α) * w (s z) / s z - 1 ≠ 0 :=
          sub_ne_zero.mpr (hv1 z hz)
      have hv2 : deriv w (s z) - 1 * w (s z) ^ 2 + (1 - 1 * α) * w (s z) / s z + 1 ≠ 0 := fun h' =>
          hv2 z hz (by linear_combination h')
      have hs2 : z = s z ^ 2 / 2 := by linear_combination -(hs z hz) / 2
      have hE0 := ((hY).sub (((hX).pow 2).const_mul 1)).add ((((hX).const_mul (1 - (1 * α))).div
          (hS) hS0))
      have hc := ((((((((hS).mul (hX)).mul (hY)).mul (((((hS).const_mul (-2)).mul (hX)).sub_const
          α).add_const 1)).add ((hS).mul ((((((hS).mul ((hX).pow 4)).add ((hS).mul ((hY).pow
          2))).sub (hS)).sub ((hX).mul (hY))).add ((hX).mul ((((hX).pow 2).mul_const α).add_const
          β))))).sub (((hX).pow 2).mul_const (1 - α))).const_mul 2).div ((((hS).pow 3).mul
          (hX)).mul (((hE0).add_const 1).pow 2)) (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hS0) hX0)
          (pow_ne_zero 2 hv2)))
      convert hc using 1
      · funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
            Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp]
        try ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs, painleveIIIRhs,
          Function.comp]
        generalize deriv w (s z) = Y at hv1 hv2 ⊢
        generalize w (s z) = X at hX0 hv1 hv2 ⊢
        generalize s z = S at hS0 hs2 hv1 hv2 ⊢
        subst hs2
        generalize eV : Y - 1 * X ^ 2 + (1 - 1 * α) * X / S = VV at hv1 hv2 ⊢
        try rw [show (VV - 1) / (VV + 1) - 1 = -2 / (VV + 1) by field_simp; ring]
        field_simp
        subst eV
        field_simp
        all_goals set_option maxRecDepth 100000 in ring

  · refine isODE2SolutionOn_of_hasDerivAt hV (v := fun z => ((2 * (((((s z * w (s z)) * deriv w (s
      z)) * ((((2 * s z) * w (s z)) + α) + 1)) + (s z * (((((s z * (w (s z) ^ 4)) + (s z * (deriv w
      (s z) ^ 2))) - s z) - (w (s z) * deriv w (s z))) + (w (s z) * (((w (s z) ^ 2) * α) + β))))) -
      ((w (s z) ^ 2) * (α + 1)))) / (((s z ^ 3) * w (s z)) * (((((deriv w (s z) - ((-1) * (w (s z)
      ^ 2))) + (((1 - ((-1) * α)) * w (s z)) / s z))) + 1) ^ 2)))) (fun z hz => ?_) (fun z hz => ?_)
    · have hm := hsU z hz
      have hS := hs' z hz
      have hX := (h.ode.hasDerivAt hm).comp z hS
      have hY := (h.ode.hasDerivAt_deriv _ hm).comp z hS
      have hid := hasDerivAt_id z
      have hS0 := h.ne_zero _ hm
      have hX0 := h.w_ne_zero _ hm
      have hz0 := hz0' z hz
      have hv1 : deriv w (s z) - -1 * w (s z) ^ 2 + (1 - -1 * α) * w (s z) / s z - 1 ≠ 0 :=
          sub_ne_zero.mpr (hv1 z hz)
      have hv2 : deriv w (s z) - -1 * w (s z) ^ 2 + (1 - -1 * α) * w (s z) / s z + 1 ≠ 0 := fun h'
          => hv2 z hz (by linear_combination h')
      have hs2 : z = s z ^ 2 / 2 := by linear_combination -(hs z hz) / 2
      have hE0 := ((hY).sub (((hX).pow 2).const_mul (-1))).add ((((hX).const_mul (1 - ((-1) *
          α))).div (hS) hS0))
      have hc := (((hE0).sub_const 1).div ((hE0).add_const 1) hv2)
      convert hc using 1
      · funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
            Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp]
        try ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs, painleveIIIRhs,
          Function.comp]
        generalize deriv w (s z) = Y at hv1 hv2 ⊢
        generalize w (s z) = X at hX0 hv1 hv2 ⊢
        generalize s z = S at hS0 hs2 hv1 hv2 ⊢
        subst hs2
        generalize eV : Y - -1 * X ^ 2 + (1 - -1 * α) * X / S = VV at hv1 hv2 ⊢
        try rw [show (VV - 1) / (VV + 1) - 1 = -2 / (VV + 1) by field_simp; ring]
        field_simp
        subst eV
        field_simp
        all_goals set_option maxRecDepth 100000 in ring
    · have hm := hsU z hz
      have hS := hs' z hz
      have hX := (h.ode.hasDerivAt hm).comp z hS
      have hY := (h.ode.hasDerivAt_deriv _ hm).comp z hS
      have hid := hasDerivAt_id z
      have hS0 := h.ne_zero _ hm
      have hX0 := h.w_ne_zero _ hm
      have hz0 := hz0' z hz
      have hv1 : deriv w (s z) - -1 * w (s z) ^ 2 + (1 - -1 * α) * w (s z) / s z - 1 ≠ 0 :=
          sub_ne_zero.mpr (hv1 z hz)
      have hv2 : deriv w (s z) - -1 * w (s z) ^ 2 + (1 - -1 * α) * w (s z) / s z + 1 ≠ 0 := fun h'
          => hv2 z hz (by linear_combination h')
      have hs2 : z = s z ^ 2 / 2 := by linear_combination -(hs z hz) / 2
      have hE0 := ((hY).sub (((hX).pow 2).const_mul (-1))).add ((((hX).const_mul (1 - ((-1) *
          α))).div (hS) hS0))
      have hc := ((((((((hS).mul (hX)).mul (hY)).mul (((((hS).const_mul 2).mul (hX)).add_const
          α).add_const 1)).add ((hS).mul ((((((hS).mul ((hX).pow 4)).add ((hS).mul ((hY).pow
          2))).sub (hS)).sub ((hX).mul (hY))).add ((hX).mul ((((hX).pow 2).mul_const α).add_const
          β))))).sub (((hX).pow 2).mul_const (α + 1))).const_mul 2).div ((((hS).pow 3).mul
          (hX)).mul (((hE0).add_const 1).pow 2)) (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hS0) hX0)
          (pow_ne_zero 2 hv2)))
      convert hc using 1
      · funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
            Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp]
        try ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs, painleveIIIRhs,
          Function.comp]
        generalize deriv w (s z) = Y at hv1 hv2 ⊢
        generalize w (s z) = X at hX0 hv1 hv2 ⊢
        generalize s z = S at hS0 hs2 hv1 hv2 ⊢
        subst hs2
        generalize eV : Y - -1 * X ^ 2 + (1 - -1 * α) * X / S = VV at hv1 hv2 ⊢
        try rw [show (VV - 1) / (VV + 1) - 1 = -2 / (VV + 1) by field_simp; ring]
        field_simp
        subst eV
        field_simp
        all_goals set_option maxRecDepth 100000 in ring

/-! ## `PVI` (§32.7(vii)) -/

/-- DLMF 32.7.33, 32.7.36 and 32.7.39, the transformation `S₁` of `PVI`:
`w₁(z₁) = w₀(z₀)/z₀` with `z₁ = 1/z₀`, i.e. `w₁(ζ) = ζ w₀(1/ζ)`, solves `PVI` with
`(α₁, β₁, γ₁, δ₁) = (α₀, β₀, 1/2 - δ₀, 1/2 - γ₀)`. -/
@[dlmf 32.7.E33, dlmf 32.7.E36, dlmf 32.7.E39]
theorem IsPainleveVIOn.s₁ {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVIOn α β γ δ w U) (hU : IsOpen U) :
    IsPainleveVIOn α β (-δ + 1 / 2) (-γ + 1 / 2) (fun ζ => ζ * w ζ⁻¹)
      ((fun ζ : ℂ => ζ⁻¹) ⁻¹' U) := by
  have hsub : (fun ζ : ℂ => ζ⁻¹) ⁻¹' U ⊆ {0}ᶜ := fun ζ hζ (h0 : ζ = 0) =>
    h.ne_zero _ hζ (by simp [h0])
  have hV : IsOpen ((fun ζ : ℂ => ζ⁻¹) ⁻¹' U) := by
    have := ContinuousOn.isOpen_preimage continuousOn_inv₀ isOpen_compl_singleton hsub hU
    exact this
  have hmem (ζ : ℂ) (hζ : ζ ∈ (fun ζ : ℂ => ζ⁻¹) ⁻¹' U) : ζ⁻¹ ∈ U := hζ
  have hz0' (ζ : ℂ) (hζ : ζ ∈ (fun ζ : ℂ => ζ⁻¹) ⁻¹' U) : ζ ≠ 0 := hsub hζ
  refine ⟨?_, hz0', fun ζ hζ h1 => h.ne_one _ (hmem ζ hζ) (by simp [h1]),
    fun ζ hζ => mul_ne_zero (hz0' ζ hζ) (h.w_ne_zero _ (hmem ζ hζ)), fun ζ hζ h' => ?_,
    fun ζ hζ h' => ?_⟩
  rotate_left
  · exact h.w_ne_self _ (hmem ζ hζ) (inv_eq_of_mul_eq_one_right h').symm
  · exact h.w_ne_one _ (hmem ζ hζ) (mul_left_cancel₀ (hz0' ζ hζ) (h'.trans (mul_one ζ).symm))
  refine isODE2SolutionOn_of_hasDerivAt hV (v := fun z => (((-deriv w z⁻¹) + (w z⁻¹ * z)) / z))
      (fun z hz => ?_) (fun z hz => ?_)
  · have hm := hmem z hz
    have hz0 := hz0' z hz
    have hi := hasDerivAt_inv hz0
    have hw := (h.ode.hasDerivAt hm).comp z hi
    have hv := (h.ode.hasDerivAt_deriv _ hm).comp z hi
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero _ hm
    have h1 : w z⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one _ hm)
    have h2 : w z⁻¹ - z⁻¹ ≠ 0 := sub_ne_zero.mpr (h.w_ne_self _ hm)
    have hz1 : z⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one _ hm)
    have hc := (hid).mul (hw)
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs, Function.comp]
      generalize deriv w z⁻¹ = b
      generalize w z⁻¹ = a at h0 h1 h2 ⊢
      have h3 : z * a - 1 ≠ 0 := fun h' => h2 (by field_simp; linear_combination h')
      have h4 : z - 1 ≠ 0 := fun h' => hz1 (by field_simp; linear_combination -h')
      have h5 : 1 - z ≠ 0 := fun h' => h4 (by linear_combination -h')
      have h6 : z * a - z ≠ 0 := mul_ne_zero hz0 h1 ∘ (by intro h'; linear_combination h')
      have h7 : 1 - a ≠ 0 := fun h' => h1 (by linear_combination -h')
      have h8 : 1 - z * a ≠ 0 := fun h' => h3 (by linear_combination -h')
      have h9 : 1 - a * z ≠ 0 := fun h' => h3 (by linear_combination -h')
      have h10 : a * z - 1 ≠ 0 := fun h' => h3 (by linear_combination h')
      field_simp
      set_option maxRecDepth 100000 in ring
  · have hm := hmem z hz
    have hz0 := hz0' z hz
    have hi := hasDerivAt_inv hz0
    have hw := (h.ode.hasDerivAt hm).comp z hi
    have hv := (h.ode.hasDerivAt_deriv _ hm).comp z hi
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero _ hm
    have h1 : w z⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one _ hm)
    have h2 : w z⁻¹ - z⁻¹ ≠ 0 := sub_ne_zero.mpr (h.w_ne_self _ hm)
    have hz1 : z⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one _ hm)
    have hc := ((((hv).neg).add ((hw).mul (hid))).div (hid) hz0)
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs, Function.comp]
      generalize deriv w z⁻¹ = b
      generalize w z⁻¹ = a at h0 h1 h2 ⊢
      have h3 : z * a - 1 ≠ 0 := fun h' => h2 (by field_simp; linear_combination h')
      have h4 : z - 1 ≠ 0 := fun h' => hz1 (by field_simp; linear_combination -h')
      have h5 : 1 - z ≠ 0 := fun h' => h4 (by linear_combination -h')
      have h6 : z * a - z ≠ 0 := mul_ne_zero hz0 h1 ∘ (by intro h'; linear_combination h')
      have h7 : 1 - a ≠ 0 := fun h' => h1 (by linear_combination -h')
      have h8 : 1 - z * a ≠ 0 := fun h' => h3 (by linear_combination -h')
      have h9 : 1 - a * z ≠ 0 := fun h' => h3 (by linear_combination -h')
      have h10 : a * z - 1 ≠ 0 := fun h' => h3 (by linear_combination h')
      field_simp
      set_option maxRecDepth 100000 in ring

/-- DLMF 32.7.34, 32.7.37 and 32.7.40, the transformation `S₂` of `PVI`:
`w₂(z₂) = 1 - w₀(z₀)` with `z₂ = 1 - z₀`, i.e. `w₂(ζ) = 1 - w₀(1 - ζ)`, solves `PVI` with
`(α₂, β₂, γ₂, δ₂) = (α₀, -γ₀, -β₀, δ₀)`. -/
@[dlmf 32.7.E34, dlmf 32.7.E37, dlmf 32.7.E40]
theorem IsPainleveVIOn.s₂ {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVIOn α β γ δ w U) (hU : IsOpen U) :
    IsPainleveVIOn α (-γ) (-β) δ (fun ζ => 1 - w (1 - ζ)) ((fun ζ : ℂ => 1 - ζ) ⁻¹' U) := by
  have hV : IsOpen ((fun ζ : ℂ => 1 - ζ) ⁻¹' U) := hU.preimage (continuous_const.sub continuous_id)
  have hW := h.ode.affine hV (a := 1) (b := -1) (c := 1) (d := -1) (neg_ne_zero.mpr one_ne_zero)
    (neg_ne_zero.mpr one_ne_zero) (fun ζ hζ => by simpa [sub_eq_add_neg] using hζ)
  have hmem (ζ : ℂ) (hζ : ζ ∈ (fun ζ : ℂ => 1 - ζ) ⁻¹' U) : 1 - ζ ∈ U := hζ
  refine ⟨?_, fun ζ hζ => ?_, fun ζ hζ => ?_, fun ζ hζ => ?_, fun ζ hζ => ?_, fun ζ hζ => ?_⟩
  · have he : (fun ζ => (w (1 + -1 * ζ) - 1) / -1) = fun ζ => 1 - w (1 - ζ) := by
      funext ζ; rw [show 1 + -1 * ζ = 1 - ζ by ring]; ring
    rw [he] at hW
    refine hW.congr_rhs fun ζ hζ => ?_
    have hm := hmem ζ hζ
    have h0 := h.w_ne_zero _ hm
    have h1 : w (1 - ζ) - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one _ hm)
    have h2 : w (1 - ζ) - (1 - ζ) ≠ 0 := sub_ne_zero.mpr (h.w_ne_self _ hm)
    have hz0 : 1 - ζ ≠ 0 := h.ne_zero _ hm
    have hz1 : 1 - ζ - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one _ hm)
    have hz0' : ζ ≠ 0 := by intro h'; apply hz1; rw [h']; ring
    have hz1' : ζ - 1 ≠ 0 := by intro h'; apply hz0; linear_combination -h'
    have hφ : HasDerivAt (fun ζ : ℂ => 1 - ζ) (-1) ζ := by
      simpa using (hasDerivAt_id ζ).const_sub 1
    have hd : deriv (fun ζ => 1 - w (1 - ζ)) ζ = deriv w (1 - ζ) := by
      have := (((h.ode.hasDerivAt hm).comp (h := fun ζ : ℂ => 1 - ζ) ζ hφ).const_sub 1).deriv
      simp only [Function.comp] at this
      rw [this]; ring
    rw [hd]
    simp only [painleveVIRhs]
    rw [show 1 + -1 * (1 - w (1 - ζ)) = w (1 - ζ) by ring]
    generalize w (1 - ζ) = a at h0 h1 h2 ⊢
    generalize deriv w (1 - ζ) = b
    have h2' : 1 - a - ζ ≠ 0 := by intro h'; apply h2; linear_combination -h'
    have h1' : 1 - a ≠ 0 := by intro h'; apply h1; linear_combination -h'
    have h2'' : a + ζ - 1 ≠ 0 := by intro h'; apply h2; linear_combination h'
    simp only [show (1 : ℂ) + -1 * ζ = 1 - ζ by ring, show (1 : ℂ) - ζ - 1 = -ζ by ring,
      show a - (1 - ζ) = a + ζ - 1 by ring, show (1 : ℂ) - a - 1 = -a by ring]
    field_simp
    ring
  · intro h'; exact h.ne_one _ (hmem ζ hζ) (by rw [h']; ring)
  · intro h'; exact h.ne_zero _ (hmem ζ hζ) (by rw [h']; ring)
  · intro h'; exact h.w_ne_one _ (hmem ζ hζ) (by linear_combination -h')
  · intro h'; exact h.w_ne_zero _ (hmem ζ hζ) (by linear_combination -h')
  · intro h'; exact h.w_ne_self _ (hmem ζ hζ) (by linear_combination -h')

/-- DLMF 32.7.35, 32.7.38 and 32.7.41, the transformation `S₃` of `PVI`:
`w₃(z₃) = 1/w₀(z₀)` with `z₃ = 1/z₀`, i.e. `w₃(ζ) = 1/w₀(1/ζ)`, solves `PVI` with
`(α₃, β₃, γ₃, δ₃) = (-β₀, -α₀, γ₀, δ₀)`. -/
@[dlmf 32.7.E35, dlmf 32.7.E38, dlmf 32.7.E41]
theorem IsPainleveVIOn.s₃ {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVIOn α β γ δ w U) (hU : IsOpen U) :
    IsPainleveVIOn (-β) (-α) γ δ (fun ζ => (w ζ⁻¹)⁻¹) ((fun ζ : ℂ => ζ⁻¹) ⁻¹' U) := by
  have hsub : (fun ζ : ℂ => ζ⁻¹) ⁻¹' U ⊆ {0}ᶜ := fun ζ hζ (h0 : ζ = 0) =>
    h.ne_zero _ hζ (by simp [h0])
  have hV : IsOpen ((fun ζ : ℂ => ζ⁻¹) ⁻¹' U) := by
    have := ContinuousOn.isOpen_preimage continuousOn_inv₀ isOpen_compl_singleton hsub hU
    exact this
  have hmem (ζ : ℂ) (hζ : ζ ∈ (fun ζ : ℂ => ζ⁻¹) ⁻¹' U) : ζ⁻¹ ∈ U := hζ
  have hz0' (ζ : ℂ) (hζ : ζ ∈ (fun ζ : ℂ => ζ⁻¹) ⁻¹' U) : ζ ≠ 0 := hsub hζ
  refine ⟨?_, hz0', fun ζ hζ h1 => h.ne_one _ (hmem ζ hζ) (by simp [h1]),
    fun ζ hζ => inv_ne_zero (h.w_ne_zero _ (hmem ζ hζ)), fun ζ hζ h' => ?_,
    fun ζ hζ h' => ?_⟩
  rotate_left
  · exact h.w_ne_one _ (hmem ζ hζ) (by rw [← inv_inv (w ζ⁻¹), h', inv_one])
  · exact h.w_ne_self _ (hmem ζ hζ) (by rw [← inv_inv (w ζ⁻¹), h'])
  refine isODE2SolutionOn_of_hasDerivAt hV (v := fun z => (deriv w z⁻¹ / ((w z⁻¹ ^ 2) * (z ^ 2))))
      (fun z hz => ?_) (fun z hz => ?_)
  · have hm := hmem z hz
    have hz0 := hz0' z hz
    have hi := hasDerivAt_inv hz0
    have hw := (h.ode.hasDerivAt hm).comp z hi
    have hv := (h.ode.hasDerivAt_deriv _ hm).comp z hi
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero _ hm
    have h1 : w z⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one _ hm)
    have h2 : w z⁻¹ - z⁻¹ ≠ 0 := sub_ne_zero.mpr (h.w_ne_self _ hm)
    have hz1 : z⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one _ hm)
    have hc := ((hasDerivAt_const _ 1).div (hw) h0)
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs, Function.comp]
      generalize deriv w z⁻¹ = b
      generalize w z⁻¹ = a at h0 h1 h2 ⊢
      have h3 : z * a - 1 ≠ 0 := fun h' => h2 (by field_simp; linear_combination h')
      have h4 : z - 1 ≠ 0 := fun h' => hz1 (by field_simp; linear_combination -h')
      have h5 : 1 - z ≠ 0 := fun h' => h4 (by linear_combination -h')
      have h6 : z * a - z ≠ 0 := mul_ne_zero hz0 h1 ∘ (by intro h'; linear_combination h')
      have h7 : 1 - a ≠ 0 := fun h' => h1 (by linear_combination -h')
      have h8 : 1 - z * a ≠ 0 := fun h' => h3 (by linear_combination -h')
      have h9 : 1 - a * z ≠ 0 := fun h' => h3 (by linear_combination -h')
      have h10 : a * z - 1 ≠ 0 := fun h' => h3 (by linear_combination h')
      field_simp
      set_option maxRecDepth 100000 in ring
  · have hm := hmem z hz
    have hz0 := hz0' z hz
    have hi := hasDerivAt_inv hz0
    have hw := (h.ode.hasDerivAt hm).comp z hi
    have hv := (h.ode.hasDerivAt_deriv _ hm).comp z hi
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero _ hm
    have h1 : w z⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one _ hm)
    have h2 : w z⁻¹ - z⁻¹ ≠ 0 := sub_ne_zero.mpr (h.w_ne_self _ hm)
    have hz1 : z⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one _ hm)
    have hc := ((hv).div (((hw).pow 2).mul ((hid).pow 2)) (mul_ne_zero (pow_ne_zero 2 h0)
        (pow_ne_zero 2 hz0)))
    convert hc using 1
    · funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp]
      try ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs, Function.comp]
      generalize deriv w z⁻¹ = b
      generalize w z⁻¹ = a at h0 h1 h2 ⊢
      have h3 : z * a - 1 ≠ 0 := fun h' => h2 (by field_simp; linear_combination h')
      have h4 : z - 1 ≠ 0 := fun h' => hz1 (by field_simp; linear_combination -h')
      have h5 : 1 - z ≠ 0 := fun h' => h4 (by linear_combination -h')
      have h6 : z * a - z ≠ 0 := mul_ne_zero hz0 h1 ∘ (by intro h'; linear_combination h')
      have h7 : 1 - a ≠ 0 := fun h' => h1 (by linear_combination -h')
      have h8 : 1 - z * a ≠ 0 := fun h' => h3 (by linear_combination -h')
      have h9 : 1 - a * z ≠ 0 := fun h' => h3 (by linear_combination -h')
      have h10 : a * z - 1 ≠ 0 := fun h' => h3 (by linear_combination h')
      field_simp
      set_option maxRecDepth 100000 in ring

/-- DLMF 32.7.42–32.7.46, the Okamoto-type transformation of `PVI`, **as corrected**: DLMF
prints `α = (θ∞ - 1)²/2` and `A = (Θ∞ - 1)²/2` in 32.7.42–32.7.43; with those values the
transformation fails (numerical and symbolic checks), while `α = θ∞²/2`, `A = Θ∞²/2` make
32.7.46 correct, with `σ` and `θ_j = Θ_j + σ/2` as in 32.7.44–32.7.45. If `W` solves
`PVI(A, B, C, D)`, `A = Θ∞²/2`, `B = -Θ₀²/2`, `C = Θ₁²/2`, `D = (1 - Θ₂²)/2`, and
`σ = 1 - (Θ₀ + Θ₁ + Θ₂ + Θ∞)`, then `w = W + σ/R`,
`R = z(z-1)W'/(W(W-1)(W-z)) + Θ₀/W + Θ₁/(W-1) + (Θ₂-1)/(W-z)`, solves `PVI` with the
parameters built from `θ_j = Θ_j + σ/2` (where `R ≠ 0` and `w ∉ {0, 1, z}`), and
`σ/(w - W)` also equals the corresponding expression in `w` and the `θ_j`. -/
@[dlmf 32.7.E42, dlmf 32.7.E43, dlmf 32.7.E44, dlmf 32.7.E45, dlmf 32.7.E46]
theorem IsPainleveVIOn.okamoto {Θ₀ Θ₁ Θ₂ Θinf : ℂ} {W : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVIOn (Θinf ^ 2 / 2) (-Θ₀ ^ 2 / 2) (Θ₁ ^ 2 / 2) ((1 - Θ₂ ^ 2) / 2) W U)
    (hU : IsOpen U)
    (hR : ∀ z ∈ U, z * (z - 1) * deriv W z / (W z * (W z - 1) * (W z - z)) + Θ₀ / W z +
      Θ₁ / (W z - 1) + (Θ₂ - 1) / (W z - z) ≠ 0)
    (hσ : 1 - (Θ₀ + Θ₁ + Θ₂ + Θinf) ≠ 0) :
    let σ := 1 - (Θ₀ + Θ₁ + Θ₂ + Θinf)
    let R := fun z => z * (z - 1) * deriv W z / (W z * (W z - 1) * (W z - z)) + Θ₀ / W z +
      Θ₁ / (W z - 1) + (Θ₂ - 1) / (W z - z)
    let w := fun z => W z + σ / R z
    let θ₀ := Θ₀ + σ / 2
    let θ₁ := Θ₁ + σ / 2
    let θ₂ := Θ₂ + σ / 2
    let θinf := Θinf + σ / 2
    (∀ z ∈ U, w z ≠ 0 → w z ≠ 1 → w z ≠ z →
      σ / (w z - W z) = z * (z - 1) * deriv w z / (w z * (w z - 1) * (w z - z)) + θ₀ / w z +
        θ₁ / (w z - 1) + (θ₂ - 1) / (w z - z)) ∧
    ∀ V : Set ℂ, IsOpen V → V ⊆ U → (∀ z ∈ V, w z ≠ 0 ∧ w z ≠ 1 ∧ w z ≠ z) →
      IsPainleveVIOn (θinf ^ 2 / 2) (-θ₀ ^ 2 / 2) (θ₁ ^ 2 / 2) ((1 - θ₂ ^ 2) / 2) w V := by
  intro σ R w θ₀ θ₁ θ₂ θinf
  have hσ' : σ ≠ 0 := hσ
  have hRd' : ∀ z ∈ U, HasDerivAt R ((((((((((((((((((((((((((((-3) * (R z ^ 2)) * (W z ^ 2)) +
      (((2 * (R z ^ 2)) * W z) * z)) + ((2 * (R z ^ 2)) * W z)) - ((R z ^ 2) * z)) + (((4 * R z) *
      Θ₀) * W z)) - (((2 * R z) * Θ₀) * z)) - ((2 * R z) * Θ₀)) + (((4 * R z) * Θ₁) * W z)) - (((2
      * R z) * Θ₁) * z)) + (((4 * R z) * Θ₂) * W z)) - ((2 * R z) * Θ₂)) - ((4 * R z) * W z)) + (2
      * R z)) - (Θ₀ ^ 2)) - ((2 * Θ₀) * Θ₁)) - ((2 * Θ₀) * Θ₂)) + (2 * Θ₀)) - (Θ₁ ^ 2)) - ((2 * Θ₁)
      * Θ₂)) + (2 * Θ₁)) - (Θ₂ ^ 2)) + (2 * Θ₂)) + (Θinf ^ 2)) - 1) / ((2 * z) * (z - 1)))) z := by
    intro z hz
    have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have h0 := h.w_ne_zero z hz
    have h1 : W z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : W z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have hz0 := h.ne_zero z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hid := hasDerivAt_id z
    have hc := (((((((hid).mul ((hid).sub_const 1)).mul (hv)).div (((hw).mul ((hw).sub_const
        1)).mul ((hw).sub (hid))) (mul_ne_zero (mul_ne_zero h0 h1) h2))).add (((hasDerivAt_const _
        Θ₀).div (hw) h0))).add (((hasDerivAt_const _ Θ₁).div ((hw).sub_const 1) h1))).add
        (((hasDerivAt_const _ (Θ₂ - 1)).div ((hw).sub (hid)) h2))
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, R]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, R]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs]
    simp only [R]
    generalize deriv W z = b
    generalize W z = a at h0 h1 h2 ⊢
    field_simp
    all_goals set_option maxRecDepth 100000 in ring
  have hWd : ∀ z ∈ U, HasDerivAt W ((((((((((((((((R z * (W z ^ 3)) - ((R z * (W z ^ 2)) * z)) - (R
      z * (W z ^ 2))) + ((R z * W z) * z)) - (Θ₀ * (W z ^ 2))) + ((Θ₀ * W z) * z)) + (Θ₀ * W z)) -
      (Θ₀ * z)) - (Θ₁ * (W z ^ 2))) + ((Θ₁ * W z) * z)) - (Θ₂ * (W z ^ 2))) + (Θ₂ * W z)) + (W z ^
      2)) - W z) / (z * (z - 1)))) z := by
    intro z hz
    have h0 := h.w_ne_zero z hz
    have h1 : W z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : W z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have hz0 := h.ne_zero z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hid := hasDerivAt_id z
    refine (h.ode.hasDerivAt hz).congr_deriv ?_
    simp only [R]
    field_simp
    ring
  have hXd : ∀ z ∈ U, HasDerivAt w (((-((((((((((((((((((((-2) * R z) * (w z ^ 3)) + (((2 * R z) *
      (w z ^ 2)) * z)) + ((2 * R z) * (w z ^ 2))) - (((2 * R z) * w z) * z)) + ((2 * Θ₀) * (w z ^
      2))) - (((2 * Θ₀) * w z) * z)) - ((2 * Θ₀) * w z)) + ((2 * Θ₀) * z)) + ((2 * Θ₁) * (w z ^
      2))) - (((2 * Θ₁) * w z) * z)) + ((2 * Θ₂) * (w z ^ 2))) - ((2 * Θ₂) * w z)) + ((3 * (w z ^
      2)) * σ)) - (2 * (w z ^ 2))) - (((2 * w z) * σ) * z)) - ((2 * w z) * σ)) + (2 * w z)) + (σ *
      z))) / ((2 * z) * (z - 1)))) z := by
    intro z hz
    have h0 := h.w_ne_zero z hz
    have h1 : W z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : W z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have hz0 := h.ne_zero z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hid := hasDerivAt_id z
    have hR0 : R z ≠ 0 := hR z hz
    have hc := (hWd z hz).add ((hasDerivAt_const z σ).div (hRd' z hz) hR0)
    refine hc.congr_deriv ?_
    simp only [w, σ]
    generalize R z = Rs at hR0 ⊢
    generalize W z = a at h0 ⊢
    field_simp
    ring
  have hRX : ∀ z ∈ U, HasDerivAt R (((((((((((((((((((((((((-3) * (R z ^ 2)) * (w z ^ 2)) + (((2 *
      (R z ^ 2)) * w z) * z)) + ((2 * (R z ^ 2)) * w z)) - ((R z ^ 2) * z)) + (((4 * R z) * Θ₀) * w
      z)) - (((2 * R z) * Θ₀) * z)) - ((2 * R z) * Θ₀)) + (((4 * R z) * Θ₁) * w z)) - (((2 * R z) *
      Θ₁) * z)) + (((4 * R z) * Θ₂) * w z)) - ((2 * R z) * Θ₂)) + (((6 * R z) * w z) * σ)) - ((4 *
      R z) * w z)) - (((2 * R z) * σ) * z)) - ((2 * R z) * σ)) + (2 * R z)) - ((2 * Θ₀) * σ)) - ((2
      * Θ₁) * σ)) - ((2 * Θ₂) * σ)) - (2 * (σ ^ 2))) + (2 * σ)) / ((2 * z) * (z - 1)))) z := by
    intro z hz
    have h0 := h.w_ne_zero z hz
    have h1 : W z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : W z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have hz0 := h.ne_zero z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hid := hasDerivAt_id z
    have hR0 : R z ≠ 0 := hR z hz
    refine (hRd' z hz).congr_deriv ?_
    simp only [w, σ]
    generalize R z = Rs at hR0 ⊢
    generalize W z = a at h0 ⊢
    field_simp
    ring
  refine ⟨fun z hz hw0 hw1 hwz => ?_, fun V hV hVU hV0 => ?_⟩
  · rw [(hXd z hz).deriv]
    have hR0 : R z ≠ 0 := hR z hz
    have hz0 := h.ne_zero z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hX1 : w z - 1 ≠ 0 := sub_ne_zero.mpr hw1
    have hXz : w z - z ≠ 0 := sub_ne_zero.mpr hwz
    have hd : w z - W z = σ / R z := by
      simp only [w]
      ring
    rw [hd]
    generalize R z = Rs at hR0 ⊢
    generalize w z = X at hw0 hX1 hXz ⊢
    field_simp
    simp only [θ₀, θ₁, θ₂, θinf, σ]
    ring
  · refine ⟨isODE2SolutionOn_of_hasDerivAt hV (v := fun z => ((-((((((((((((((((((((-2) * R z) * (w
      z ^ 3)) + (((2 * R z) * (w z ^ 2)) * z)) + ((2 * R z) * (w z ^ 2))) - (((2 * R z) * w z) *
      z)) + ((2 * Θ₀) * (w z ^ 2))) - (((2 * Θ₀) * w z) * z)) - ((2 * Θ₀) * w z)) + ((2 * Θ₀) * z))
      + ((2 * Θ₁) * (w z ^ 2))) - (((2 * Θ₁) * w z) * z)) + ((2 * Θ₂) * (w z ^ 2))) - ((2 * Θ₂) * w
      z)) + ((3 * (w z ^ 2)) * σ)) - (2 * (w z ^ 2))) - (((2 * w z) * σ) * z)) - ((2 * w z) * σ)) +
      (2 * w z)) + (σ * z))) / ((2 * z) * (z - 1)))) (fun z hz => hXd z (hVU hz))
      (fun z hz => ?_), fun z hz => h.ne_zero z (hVU hz), fun z hz => h.ne_one z (hVU hz),
      fun z hz => (hV0 z hz).1, fun z hz => (hV0 z hz).2.1, fun z hz => (hV0 z hz).2.2⟩
    have hz' := hVU hz
    have hX := hXd z hz'
    have hRX := hRX z hz'
    have hR0 : R z ≠ 0 := hR z hz'
    have hz0 := h.ne_zero z hz'
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz')
    have hid := hasDerivAt_id z
    have hX0 : w z ≠ 0 := (hV0 z hz).1
    have hX1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (hV0 z hz).2.1
    have hXz : w z - z ≠ 0 := sub_ne_zero.mpr (hV0 z hz).2.2
    have hc := ((((((((((((((((((((((hRX).const_mul (-2)).mul ((hX).pow 3)).add ((((hRX).const_mul
        2).mul ((hX).pow 2)).mul (hid))).add (((hRX).const_mul 2).mul ((hX).pow 2))).sub
        ((((hRX).const_mul 2).mul (hX)).mul (hid))).add (((hX).pow 2).const_mul (2 * Θ₀))).sub
        (((hX).const_mul (2 * Θ₀)).mul (hid))).sub ((hX).const_mul (2 * Θ₀))).add ((hid).const_mul
        (2 * Θ₀))).add (((hX).pow 2).const_mul (2 * Θ₁))).sub (((hX).const_mul (2 * Θ₁)).mul
        (hid))).add (((hX).pow 2).const_mul (2 * Θ₂))).sub ((hX).const_mul (2 * Θ₂))).add
        ((((hX).pow 2).const_mul 3).mul_const σ)).sub (((hX).pow 2).const_mul 2)).sub
        ((((hX).const_mul 2).mul_const σ).mul (hid))).sub (((hX).const_mul 2).mul_const σ)).add
        ((hX).const_mul 2)).add ((hid).const_mul σ)).neg).div (((hid).const_mul 2).mul
        ((hid).sub_const 1)) (mul_ne_zero (mul_ne_zero (by norm_num) hz0) hz1))
    refine (hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      try ring
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs]
    generalize R z = Rs at hR0 ⊢
    generalize w z = X at hX0 hX1 hXz ⊢
    field_simp
    simp only [θ₀, θ₁, θ₂, θinf, σ]
    all_goals set_option maxRecDepth 100000 in ring

/-- Transfer of a derivative through a holomorphic change of variables `φ` with nonzero
derivative: if `u (φ x) = g x` on the open set `U`, then `u' (φ z) = g'(z) / φ'(z)`. -/
lemma p3a_hasDerivAt_of_comp {φ φ' g u : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hφ : ∀ x ∈ U, HasDerivAt φ (φ' x) x) (hφ0 : ∀ x ∈ U, φ' x ≠ 0) {g' z : ℂ} (hz : z ∈ U)
    (hg : HasDerivAt g g' z) (hug : ∀ x ∈ U, u (φ x) = g x) :
    HasDerivAt u (g' / φ' z) (φ z) := by
  have hdiff : DifferentiableOn ℂ φ U := fun x hx =>
    (hφ x hx).differentiableAt.differentiableWithinAt
  have hs : HasStrictDerivAt φ (φ' z) z := by
    have := (hdiff.analyticAt (hU.mem_nhds hz)).hasStrictDerivAt
    rwa [(hφ z hz).deriv] at this
  have hψ := hs.to_localInverse (hφ0 z hz)
  have hψz : HasStrictDerivAt.localInverse φ (φ' z) z hs (hφ0 z hz) (φ z) = z :=
    (hs.eventually_left_inverse (hφ0 z hz)).self_of_nhds
  have hev : ∀ᶠ y in 𝓝 (φ z),
      u y = g (HasStrictDerivAt.localInverse φ (φ' z) z hs (hφ0 z hz) y) := by
    have h2 : ∀ᶠ y in 𝓝 (φ z), HasStrictDerivAt.localInverse φ (φ' z) z hs (hφ0 z hz) y ∈ U :=
      hψ.hasDerivAt.continuousAt.preimage_mem_nhds (by rw [hψz]; exact hU.mem_nhds hz)
    filter_upwards [hs.eventually_right_inverse (hφ0 z hz), h2] with y hy1 hy2
    rw [← hug _ hy2, hy1]
  have hc := (show HasDerivAt g g' (HasStrictDerivAt.localInverse φ (φ' z) z hs (hφ0 z hz) (φ z))
    by rwa [hψz]).comp (φ z) hψ.hasDerivAt
  exact (hc.congr_of_eventuallyEq hev).congr_deriv (div_eq_mul_inv _ _).symm

/-- A second-order ODE transferred through a holomorphic change of variables `ζ = φ(x)` with
nonzero derivative: if `u (φ x) = g x` on `U`, `g' = g₁`, `(g₁/φ')' = g₂` and
`g₂/φ' = F(φ, g, g₁/φ')` on `U`, then `u` solves `u'' = F(ζ, u, u')` on any `V ⊆ φ(U)`. -/
lemma p3a_isODE2SolutionOn_of_comp {F : ℂ → ℂ → ℂ → ℂ} {φ φ' g g₁ g₂ u : ℂ → ℂ}
    {U V : Set ℂ} (hU : IsOpen U) (hφ : ∀ x ∈ U, HasDerivAt φ (φ' x) x)
    (hφ0 : ∀ x ∈ U, φ' x ≠ 0) (hg : ∀ x ∈ U, HasDerivAt g (g₁ x) x)
    (hg₁ : ∀ x ∈ U, HasDerivAt (fun y => g₁ y / φ' y) (g₂ x) x)
    (hug : ∀ x ∈ U, u (φ x) = g x) (hcover : V ⊆ φ '' U)
    (hF : ∀ x ∈ U, g₂ x / φ' x = F (φ x) (g x) (g₁ x / φ' x)) :
    IsODE2SolutionOn F u V := by
  have h1 : ∀ x ∈ U, HasDerivAt u (g₁ x / φ' x) (φ x) := fun x hx =>
    p3a_hasDerivAt_of_comp hU hφ hφ0 hx (hg x hx) hug
  have h2 : ∀ x ∈ U, deriv u (φ x) = g₁ x / φ' x := fun x hx => (h1 x hx).deriv
  refine ⟨fun ζ hζ => ?_, fun ζ hζ => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hcover hζ
    exact (h1 x hx).differentiableAt
  · obtain ⟨x, hx, rfl⟩ := hcover hζ
    rw [hug x hx, h2 x hx, ← hF x hx]
    exact p3a_hasDerivAt_of_comp hU hφ hφ0 hx (hg₁ x hx) h2

/-- DLMF 32.7.47, the quadratic transformation of `PVI`: for a solution `w` of `PVI` with
`α = -β`, `γ = 1/2 - δ`, and with `s = √z` (any function on `U` with `s² = z`,
`s' = 1/(2s)`, `s ≠ -1`), the function `u₁` of `ζ₁ = ((1-s)/(1+s))²` given by
`u₁(ζ₁) = (1-w)(w-z)/((1+s)²w)` solves `PVI(4α, -4γ, 0, 1/2)`. Formulated for any `u₁`
on an open `V` with these values, where every point of `V` is `ζ₁(z)` for some `z ∈ U` at
which `ζ₁` has nonzero derivative. -/
@[dlmf 32.7.E47]
theorem IsPainleveVIOn.quadratic {α γ : ℂ} {w s u : ℂ → ℂ} {U V : Set ℂ}
    (h : IsPainleveVIOn α (-α) γ (1 / 2 - γ) w U) (hU : IsOpen U) (hV : IsOpen V)
    (hs : ∀ z ∈ U, s z ^ 2 = z) (hs' : ∀ z ∈ U, HasDerivAt s (1 / (2 * s z)) z)
    (hs1 : ∀ z ∈ U, s z ≠ -1) (hs1' : ∀ z ∈ U, s z ≠ 1)
    (hmaps : ∀ z ∈ U, ((1 - s z) / (1 + s z)) ^ 2 ∈ V)
    (hu : ∀ z ∈ U, u (((1 - s z) / (1 + s z)) ^ 2) =
      (1 - w z) * (w z - z) / ((1 + s z) ^ 2 * w z))
    (hcover : V ⊆ (fun z => ((1 - s z) / (1 + s z)) ^ 2) '' U)
    (hu0 : ∀ ζ ∈ V, u ζ ≠ 0 ∧ u ζ ≠ 1 ∧ u ζ ≠ ζ) :
    IsPainleveVIOn (4 * α) (-4 * γ) 0 (1 / 2) u V := by
  have hh : ∀ z ∈ U, HasDerivAt (fun z => ((1 - s z) / (1 + s z)) ^ 2) (((-(2 * (1 - s z))) / (s z
      * ((1 + s z) ^ 3)))) z := by
    intro z hz
    have hS := hs' z hz
    have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have hS0 : s z ≠ 0 := fun h' => h.ne_zero z hz (by rw [← hs z hz, h', zero_pow two_ne_zero])
    have h1s : 1 + s z ≠ 0 := fun h' => hs1 z hz (by linear_combination h')
    have h1s' : s z + 1 ≠ 0 := fun h' => hs1 z hz (by linear_combination h')
    have h1ms : 1 - s z ≠ 0 := fun h' => hs1' z hz (by linear_combination -h')
    have hSm1 : s z - 1 ≠ 0 := fun h' => hs1' z hz (by linear_combination h')
    have h0 := h.w_ne_zero z hz
    have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : w z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have h2' : -w z + z ≠ 0 := fun h' => h2 (by linear_combination -h')
    have hD : (1 + s z) ^ 2 * w z ≠ 0 := mul_ne_zero (pow_ne_zero 2 h1s) h0
    have hz0 := h.ne_zero z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hsq : z = s z ^ 2 := (hs z hz).symm
    have hc := ((((hS).const_sub 1).div ((hS).const_add 1) h1s)).pow 2
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs]
    generalize deriv w z = b
    generalize w z = a at h0 h1 h2 h2' hD ⊢
    generalize s z = S at hS0 h1s h1s' h1ms hSm1 hsq hD ⊢
    subst hsq
    field_simp
    all_goals set_option maxRecDepth 100000 in ring
  refine ⟨p3a_isODE2SolutionOn_of_comp hU (φ := fun z => ((1 - s z) / (1 + s z)) ^ 2)
      (φ' := fun z => ((-(2 * (1 - s z))) / (s z * ((1 + s z) ^ 3))))
      (g := fun z => (1 - w z) * (w z - z) / ((1 + s z) ^ 2 * w z))
      (g₁ := fun z => ((((((s z * deriv w z) * (s z + 1)) * (((w z * (1 - w z)) - (w z * (w z -
          z))) - ((1 - w z) * (w z - z)))) - (((s z * w z) * (1 - w z)) * (s z + 1))) - ((w z * (1
          - w z)) * (w z - z))) / ((s z * (w z ^ 2)) * ((s z + 1) ^ 3)))) (g₂ := fun z =>
          (((((((((s z ^ 2) * (s z - 1)) * (s z + 1)) * (((w z * (1 - w z)) - (w z * (w z - z))) -
          ((1 - w z) * (w z - z)))) * (((((((((2 * α) * (w z ^ 2)) * ((w z - 1) ^ 2)) * ((w z - z)
          ^ 2)) - ((((2 * α) * z) * ((w z - 1) ^ 2)) * ((w z - z) ^ 2))) + ((((2 * γ) * (w z ^ 2))
          * ((w z - z) ^ 2)) * (z - 1))) + ((((deriv w z ^ 2) * (z ^ 2)) * ((z - 1) ^ 2)) * (((w z
          * (w z - 1)) + (w z * (w z - z))) + ((w z - 1) * (w z - z))))) - ((((((2 * deriv w z) * w
          z) * z) * (w z - 1)) * (z - 1)) * (((z * (w z - z)) + (z * (z - 1))) + ((w z - z) * (z -
          1))))) + (((((w z ^ 2) * z) * (1 - (2 * γ))) * ((w z - 1) ^ 2)) * (z - 1)))) + ((((((((2
          * s z) * deriv w z) * (z ^ 2)) * (s z - 1)) * (w z - 1)) * (w z - z)) * ((z - 1) ^ 2)) *
          ((((((((-2) * s z) * deriv w z) * (s z + 1)) * (((w z * (1 - w z)) - (w z * (w z - z))) -
          ((1 - w z) * (w z - z)))) + ((((2 * s z) * w z) * (1 - w z)) * (s z + 1))) + (((2 * w z)
          * (1 - w z)) * (w z - z))) + (w z * ((((((((((-2) * s z) * deriv w z) * w z) * (s z + 1))
          + ((s z * w z) * (s z + 1))) - ((s z * (1 - w z)) * (s z + 1))) - (w z * (1 - w z))) + (w
          z * (w z - z))) - ((1 - w z) * (w z - z))))))) + ((((((((2 * s z) * w z) * (z ^ 2)) * (s
          z - 1)) * (w z - 1)) * (w z - z)) * ((z - 1) ^ 2)) * (((s z * deriv w z) * (s z + 1)) +
          (w z * (1 - w z))))) + (((((w z * (z ^ 2)) * (w z - 1)) * (w z - z)) * ((z - 1) ^ 2)) *
          (((((((-s z) * deriv w z) * (s z + 1)) * (((w z * (1 - w z)) - (w z * (w z - z))) - ((1 -
          w z) * (w z - z)))) + (((s z * w z) * (1 - w z)) * (s z + 1))) + ((w z * (1 - w z)) * (w
          z - z))) + ((s z - 1) * (((((s z * deriv w z) * (((w z * (1 - w z)) - (w z * (w z - z)))
          - ((1 - w z) * (w z - z)))) - ((s z * w z) * (1 - w z))) + ((deriv w z * (s z + 1)) *
          (((w z * (1 - w z)) - (w z * (w z - z))) - ((1 - w z) * (w z - z))))) - ((w z * (1 - w
          z)) * (s z + 1))))))) / ((((((((-4) * s z) * (w z ^ 3)) * (z ^ 2)) * ((s z - 1) ^ 2)) *
          ((-w z) + z)) * (w z - 1)) * ((z - 1) ^ 2)))) hh (fun z hz => ?_) (fun z hz => ?_)
      (fun z hz => ?_) hu hcover (fun z hz => ?_), fun ζ hζ => ?_, fun ζ hζ => ?_,
      fun ζ hζ => (hu0 ζ hζ).1, fun ζ hζ => (hu0 ζ hζ).2.1, fun ζ hζ => (hu0 ζ hζ).2.2⟩
  · have hS0 : s z ≠ 0 := fun h' => h.ne_zero z hz (by rw [← hs z hz, h', zero_pow two_ne_zero])
    have h1s : 1 + s z ≠ 0 := fun h' => hs1 z hz (by linear_combination h')
    have h1ms : 1 - s z ≠ 0 := fun h' => hs1' z hz (by linear_combination -h')
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero two_ne_zero h1ms))
      (mul_ne_zero hS0 (pow_ne_zero 3 h1s))
  · have hS := hs' z hz
    have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have hS0 : s z ≠ 0 := fun h' => h.ne_zero z hz (by rw [← hs z hz, h', zero_pow two_ne_zero])
    have h1s : 1 + s z ≠ 0 := fun h' => hs1 z hz (by linear_combination h')
    have h1s' : s z + 1 ≠ 0 := fun h' => hs1 z hz (by linear_combination h')
    have h1ms : 1 - s z ≠ 0 := fun h' => hs1' z hz (by linear_combination -h')
    have hSm1 : s z - 1 ≠ 0 := fun h' => hs1' z hz (by linear_combination h')
    have h0 := h.w_ne_zero z hz
    have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : w z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have h2' : -w z + z ≠ 0 := fun h' => h2 (by linear_combination -h')
    have hD : (1 + s z) ^ 2 * w z ≠ 0 := mul_ne_zero (pow_ne_zero 2 h1s) h0
    have hz0 := h.ne_zero z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hsq : z = s z ^ 2 := (hs z hz).symm
    have hc := ((((hw).const_sub 1).mul ((hw).sub (hid))).div ((((hS).const_add 1).pow 2).mul (hw))
        (mul_ne_zero (pow_ne_zero 2 h1s) h0))
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs]
    generalize deriv w z = b
    generalize w z = a at h0 h1 h2 h2' hD ⊢
    generalize s z = S at hS0 h1s h1s' h1ms hSm1 hsq hD ⊢
    subst hsq
    field_simp
    all_goals set_option maxRecDepth 100000 in ring
  · have hS := hs' z hz
    have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have hS0 : s z ≠ 0 := fun h' => h.ne_zero z hz (by rw [← hs z hz, h', zero_pow two_ne_zero])
    have h1s : 1 + s z ≠ 0 := fun h' => hs1 z hz (by linear_combination h')
    have h1s' : s z + 1 ≠ 0 := fun h' => hs1 z hz (by linear_combination h')
    have h1ms : 1 - s z ≠ 0 := fun h' => hs1' z hz (by linear_combination -h')
    have hSm1 : s z - 1 ≠ 0 := fun h' => hs1' z hz (by linear_combination h')
    have h0 := h.w_ne_zero z hz
    have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : w z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have h2' : -w z + z ≠ 0 := fun h' => h2 (by linear_combination -h')
    have hD : (1 + s z) ^ 2 * w z ≠ 0 := mul_ne_zero (pow_ne_zero 2 h1s) h0
    have hz0 := h.ne_zero z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hsq : z = s z ^ 2 := (hs z hz).symm
    have hc := (((((((((hS).mul (hv)).mul ((hS).add_const 1)).mul ((((hw).mul ((hw).const_sub
        1)).sub ((hw).mul ((hw).sub (hid)))).sub (((hw).const_sub 1).mul ((hw).sub (hid))))).sub
        ((((hS).mul (hw)).mul ((hw).const_sub 1)).mul ((hS).add_const 1))).sub (((hw).mul
        ((hw).const_sub 1)).mul ((hw).sub (hid)))).div (((hS).mul ((hw).pow 2)).mul
        (((hS).add_const 1).pow 3)) (mul_ne_zero (mul_ne_zero hS0 (pow_ne_zero 2 h0)) (pow_ne_zero
        3 h1s')))).div ((((((hS).const_sub 1).const_mul 2).neg).div ((hS).mul (((hS).const_add
        1).pow 3)) (mul_ne_zero hS0 (pow_ne_zero 3 h1s)))) (div_ne_zero (neg_ne_zero.mpr
        (mul_ne_zero (by norm_num) h1ms)) (mul_ne_zero hS0 (pow_ne_zero 3 h1s))))
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs]
    generalize deriv w z = b
    generalize w z = a at h0 h1 h2 h2' hD ⊢
    generalize s z = S at hS0 h1s h1s' h1ms hSm1 hsq hD ⊢
    subst hsq
    field_simp
    all_goals set_option maxRecDepth 100000 in ring
  · have hS := hs' z hz
    have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have hS0 : s z ≠ 0 := fun h' => h.ne_zero z hz (by rw [← hs z hz, h', zero_pow two_ne_zero])
    have h1s : 1 + s z ≠ 0 := fun h' => hs1 z hz (by linear_combination h')
    have h1s' : s z + 1 ≠ 0 := fun h' => hs1 z hz (by linear_combination h')
    have h1ms : 1 - s z ≠ 0 := fun h' => hs1' z hz (by linear_combination -h')
    have hSm1 : s z - 1 ≠ 0 := fun h' => hs1' z hz (by linear_combination h')
    have h0 := h.w_ne_zero z hz
    have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : w z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have h2' : -w z + z ≠ 0 := fun h' => h2 (by linear_combination -h')
    have hD : (1 + s z) ^ 2 * w z ≠ 0 := mul_ne_zero (pow_ne_zero 2 h1s) h0
    have hz0 := h.ne_zero z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hsq : z = s z ^ 2 := (hs z hz).symm
    have hu' := hu0 _ (hmaps z hz)
    rw [hu z hz] at hu'
    have hU0 := hu'.1
    have hU1 := sub_ne_zero.mpr hu'.2.1
    have hUz := sub_ne_zero.mpr hu'.2.2
    have hZ0 : ((1 - s z) / (1 + s z)) ^ 2 ≠ 0 := pow_ne_zero 2 (div_ne_zero h1ms h1s)
    have hZ1 : ((1 - s z) / (1 + s z)) ^ 2 - 1 ≠ 0 := by
      rw [div_pow, div_sub_one (pow_ne_zero 2 h1s)]
      refine div_ne_zero ?_ (pow_ne_zero 2 h1s)
      intro h'
      apply hS0
      linear_combination (-1 / 4) * h'
    simp only [painleveVIRhs]
    generalize eZ : ((1 - s z) / (1 + s z)) ^ 2 = Z at hZ0 hZ1 hUz ⊢
    generalize eU : (1 - w z) * (w z - z) / ((1 + s z) ^ 2 * w z) = U0 at hU0 hU1 hUz ⊢
    generalize deriv w z = b
    generalize w z = a at h0 h1 h2 h2' hD eU ⊢
    generalize s z = S at hS0 h1s h1s' h1ms hSm1 hsq hD eU eZ ⊢
    subst hsq
    field_simp
    subst eU eZ
    field_simp
    ring
  · obtain ⟨z, hz, rfl⟩ := hcover hζ
    have h1s : 1 + s z ≠ 0 := fun h' => hs1 z hz (by linear_combination h')
    have h1ms : 1 - s z ≠ 0 := fun h' => hs1' z hz (by linear_combination -h')
    exact pow_ne_zero 2 (div_ne_zero h1ms h1s)
  · obtain ⟨z, hz, rfl⟩ := hcover hζ
    have h1s : 1 + s z ≠ 0 := fun h' => hs1 z hz (by linear_combination h')
    intro h'
    beta_reduce at h'
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 2 h1s)] at h'
    have : s z = 0 := by linear_combination (-1 / 4) * h'
    exact h.ne_zero z hz (by rw [← hs z hz, this]; ring)

/-- DLMF 32.7.48, the quartic transformation of `PVI`: for a solution `w` of `PVI` with
`α = -β = γ = 1/2 - δ`, the function `u₂(z) = (w² - z)²/(4w(w-1)(w-z))` solves
`PVI(16α, 0, 0, 1/2)` (with `ζ₂ = z`), where `u₂ ∉ {0, 1, z}`. -/
@[dlmf 32.7.E48]
theorem IsPainleveVIOn.quartic {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVIOn α (-α) α (1 / 2 - α) w U) (hU : IsOpen U)
    (hu : ∀ z ∈ U, (w z ^ 2 - z) ^ 2 / (4 * w z * (w z - 1) * (w z - z)) ≠ 0 ∧
      (w z ^ 2 - z) ^ 2 / (4 * w z * (w z - 1) * (w z - z)) ≠ 1 ∧
      (w z ^ 2 - z) ^ 2 / (4 * w z * (w z - 1) * (w z - z)) ≠ z) :
    IsPainleveVIOn (16 * α) 0 0 (1 / 2)
      (fun z => (w z ^ 2 - z) ^ 2 / (4 * w z * (w z - 1) * (w z - z))) U := by
  refine ⟨?_, h.ne_zero, h.ne_one, fun z hz => (hu z hz).1, fun z hz => (hu z hz).2.1,
    fun z hz => (hu z hz).2.2⟩
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => ((2 * ((((((4 * w z) * (w z - 1)) * (w z
      - z))) * (((((2 * deriv w z) * w z) * ((w z ^ 2) - z)) - (w z ^ 2)) + z)) - ((2 * ((((w z ^
      2) - z) ^ 2))) * ((deriv w z * (((w z * (w z - 1)) + (w z * (w z - z))) + ((w z - 1) * (w z -
      z)))) - (w z * (w z - 1)))))) / (((((4 * w z) * (w z - 1)) * (w z - z))) ^ 2))) (fun z hz =>
      ?_) (fun z hz => ?_)
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : w z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have hz0 := h.ne_zero z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hD : 4 * w z * (w z - 1) * (w z - z) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h0) h1) h2
    have hn : (w z ^ 2 - z) ^ 2 ≠ 0 := fun h' => (hu z hz).1 (by rw [h', zero_div])
    have hm1 : (w z ^ 2 - z) ^ 2 - 4 * w z * (w z - 1) * (w z - z) ≠ 0 := fun h' =>
      (hu z hz).2.1 (by rw [div_eq_one_iff_eq hD]; linear_combination h')
    have hm2 : (w z ^ 2 - z) ^ 2 - z * (4 * w z * (w z - 1) * (w z - z)) ≠ 0 := fun h' =>
      (hu z hz).2.2 (by rw [div_eq_iff hD]; linear_combination h')
    have hE0 := (((hw).pow 2).sub (hid)).pow 2
    have hE1 := (((hw).const_mul 4).mul ((hw).sub_const 1)).mul ((hw).sub (hid))
    have hc := ((hE0).div (hE1) hD)
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs]
    generalize deriv w z = b
    generalize w z = a at h0 h1 h2 hD hn hm1 hm2 ⊢
    try rw [show (a ^ 2 - z) ^ 2 / (4 * a * (a - 1) * (a - z)) - 1 = ((a ^ 2 - z) ^ 2 - 4 * a * (a
        - 1) * (a - z)) / (4 * a * (a - 1) * (a - z)) by field_simp]
    try rw [show (a ^ 2 - z) ^ 2 / (4 * a * (a - 1) * (a - z)) - z = ((a ^ 2 - z) ^ 2 - z * (4 * a
        * (a - 1) * (a - z))) / (4 * a * (a - 1) * (a - z)) by field_simp]
    generalize eM1 : (a ^ 2 - z) ^ 2 - 4 * a * (a - 1) * (a - z) = M1 at hm1 ⊢
    generalize eM2 : (a ^ 2 - z) ^ 2 - z * (4 * a * (a - 1) * (a - z)) = M2 at hm2 ⊢
    generalize eN : (a ^ 2 - z) ^ 2 = NN at hn ⊢
    generalize eD : 4 * a * (a - 1) * (a - z) = DD at hD ⊢
    field_simp
    subst eM1 eM2 eN eD
    all_goals set_option maxRecDepth 100000 in ring
  · have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have h0 := h.w_ne_zero z hz
    have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : w z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have hz0 := h.ne_zero z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hD : 4 * w z * (w z - 1) * (w z - z) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h0) h1) h2
    have hn : (w z ^ 2 - z) ^ 2 ≠ 0 := fun h' => (hu z hz).1 (by rw [h', zero_div])
    have hm1 : (w z ^ 2 - z) ^ 2 - 4 * w z * (w z - 1) * (w z - z) ≠ 0 := fun h' =>
      (hu z hz).2.1 (by rw [div_eq_one_iff_eq hD]; linear_combination h')
    have hm2 : (w z ^ 2 - z) ^ 2 - z * (4 * w z * (w z - 1) * (w z - z)) ≠ 0 := fun h' =>
      (hu z hz).2.2 (by rw [div_eq_iff hD]; linear_combination h')
    have hE0 := (((hw).pow 2).sub (hid)).pow 2
    have hE1 := (((hw).const_mul 4).mul ((hw).sub_const 1)).mul ((hw).sub (hid))
    have hc := (((((hE1).mul ((((((hv).const_mul 2).mul (hw)).mul (((hw).pow 2).sub (hid))).sub
        ((hw).pow 2)).add (hid))).sub (((hE0).const_mul 2).mul (((hv).mul ((((hw).mul
        ((hw).sub_const 1)).add ((hw).mul ((hw).sub (hid)))).add (((hw).sub_const 1).mul ((hw).sub
        (hid))))).sub ((hw).mul ((hw).sub_const 1))))).const_mul 2).div ((hE1).pow 2) (pow_ne_zero
        2 hD))
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs]
    generalize deriv w z = b
    generalize w z = a at h0 h1 h2 hD hn hm1 hm2 ⊢
    try rw [show (a ^ 2 - z) ^ 2 / (4 * a * (a - 1) * (a - z)) - 1 = ((a ^ 2 - z) ^ 2 - 4 * a * (a
        - 1) * (a - z)) / (4 * a * (a - 1) * (a - z)) by field_simp]
    try rw [show (a ^ 2 - z) ^ 2 / (4 * a * (a - 1) * (a - z)) - z = ((a ^ 2 - z) ^ 2 - z * (4 * a
        * (a - 1) * (a - z))) / (4 * a * (a - 1) * (a - z)) by field_simp]
    generalize eM1 : (a ^ 2 - z) ^ 2 - 4 * a * (a - 1) * (a - z) = M1 at hm1 ⊢
    generalize eM2 : (a ^ 2 - z) ^ 2 - z * (4 * a * (a - 1) * (a - z)) = M2 at hm2 ⊢
    generalize eN : (a ^ 2 - z) ^ 2 = NN at hn ⊢
    generalize eD : 4 * a * (a - 1) * (a - z) = DD at hD ⊢
    field_simp
    subst eM1 eM2 eN eD
    all_goals set_option maxRecDepth 100000 in ring

/-- DLMF 32.7.49–32.7.50: for a solution `w` of `PVI` with `α = β = 0`, `γ = 1/2 - δ`,
with `q = z^{1/4}` and `p = √w` (any functions with `q⁴ = z`, `q' = q/(4z)`, `p² = w`,
`p' = w'/(2p)`), the function `u₃` of `ζ₃ = ((1-q)/(1+q))⁴` with
`u₃(ζ₃) = ((1-q)/(1+q))²((p+q)/(p-q))²` solves `PVI` with `α₃ = β₃`, `γ₃ = 1/2 - δ₃`.
Stronger than DLMF: the numerical check gives the parameters exactly,
`(α₃, β₃, γ₃, δ₃) = (0, 0, γ, 1/2 - γ)`. Formulated like `IsPainleveVIOn.quadratic`. -/
@[dlmf 32.7.E49, dlmf 32.7.E50]
theorem IsPainleveVIOn.quartic_root {γ : ℂ} {w q p u : ℂ → ℂ} {U V : Set ℂ}
    (h : IsPainleveVIOn 0 0 γ (1 / 2 - γ) w U) (hU : IsOpen U) (hV : IsOpen V)
    (hq : ∀ z ∈ U, q z ^ 4 = z) (hq' : ∀ z ∈ U, HasDerivAt q (q z / (4 * z)) z)
    (hp : ∀ z ∈ U, p z ^ 2 = w z) (hp' : ∀ z ∈ U, HasDerivAt p (deriv w z / (2 * p z)) z)
    (hq1 : ∀ z ∈ U, q z ≠ -1) (hpq : ∀ z ∈ U, p z ≠ q z)
    (hmaps : ∀ z ∈ U, ((1 - q z) / (1 + q z)) ^ 4 ∈ V)
    (hu : ∀ z ∈ U, u (((1 - q z) / (1 + q z)) ^ 4) =
      ((1 - q z) / (1 + q z)) ^ 2 * ((p z + q z) / (p z - q z)) ^ 2)
    (hcover : V ⊆ (fun z => ((1 - q z) / (1 + q z)) ^ 4) '' U)
    (hderiv : ∀ z ∈ U, (1 - q z) ^ 3 * q z / ((1 + q z) ^ 5 * z) ≠ 0)
    (hu0 : ∀ ζ ∈ V, u ζ ≠ 0 ∧ u ζ ≠ 1 ∧ u ζ ≠ ζ) :
    IsPainleveVIOn 0 0 γ (1 / 2 - γ) u V := by
  have hh : ∀ z ∈ U, HasDerivAt (fun z => ((1 - q z) / (1 + q z)) ^ 4) (((-((2 * ((1 - q z) ^ 3)) *
      q z)) / (((1 + q z) ^ 5) * z))) z := by
    intro z hz
    have hz0 := h.ne_zero z hz
    have hQ0 : q z ≠ 0 := fun h' => hz0 (by rw [← hq z hz, h']; ring)
    have h1q : 1 + q z ≠ 0 := fun h' => hq1 z hz (by linear_combination h')
    have h1mq : 1 - q z ≠ 0 := fun h' => hderiv z hz (by rw [h']; simp)
    have hQ := hq' z hz
    have hP := hp' z hz
    have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have hq1' : q z + 1 ≠ 0 := fun h' => hq1 z hz (by linear_combination h')
    have hqm1 : q z - 1 ≠ 0 := fun h' => h1mq (by linear_combination -h')
    have hP0 : p z ≠ 0 := fun h' => h.w_ne_zero z hz (by rw [← hp z hz, h']; ring)
    have hPQ : p z - q z ≠ 0 := sub_ne_zero.mpr (hpq z hz)
    have h0 := h.w_ne_zero z hz
    have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : w z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have h2' : -w z + z ≠ 0 := fun h' => h2 (by linear_combination -h')
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hpw := hp z hz
    have hsq : z = q z ^ 4 := (hq z hz).symm
    have hc := ((((hQ).const_sub 1).div ((hQ).const_add 1) h1q)).pow 4
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs]
    generalize deriv w z = b
    generalize w z = a at h0 h1 h2 h2' hpw ⊢
    generalize p z = P at hP0 hPQ hpw ⊢
    generalize q z = Q at hQ0 h1q hq1' h1mq hqm1 hPQ hsq ⊢
    subst hpw
    subst hsq
    field_simp
    all_goals set_option maxRecDepth 100000 in ring
  refine ⟨p3a_isODE2SolutionOn_of_comp hU (φ := fun z => ((1 - q z) / (1 + q z)) ^ 4)
      (φ' := fun z => ((-((2 * ((1 - q z) ^ 3)) * q z)) / (((1 + q z) ^ 5) * z)))
      (g := fun z => ((1 - q z) / (1 + q z)) ^ 2 * ((p z + q z) / (p z - q z)) ^ 2)
      (g₁ := fun z => (((q z * (p z + q z)) * ((p z * ((((((-((1 - q z) ^ 2)) * (p z - q z)) * (p z
          + q z)) + ((((1 - q z) ^ 2) * (p z - q z)) * (q z + 1))) + ((((1 - q z) ^ 2) * (p z + q
          z)) * (q z + 1))) + ((((p z - q z) * (p z + q z)) * (q z - 1)) * (q z + 1)))) - ((((4 *
          deriv w z) * z) * ((1 - q z) ^ 2)) * (q z + 1)))) / ((((2 * p z) * z) * ((p z - q z) ^
          3)) * ((q z + 1) ^ 3)))) (g₂ := fun z => (((q z + 1) * ((((((((((p z ^ 2) * q z) * w z) *
          (w z - 1)) * (w z - z)) * (z - 1)) * (((((((((-(1 - q z)) * (p z - q z)) * (p z + q z)) *
          (q z + 1)) * (((p z * ((((((2 * ((1 - q z) ^ 2)) * (p z + q z)) - (((p z - q z) * (p z +
          q z)) * (q z - 1))) + (((p z - q z) * (p z + q z)) * (q z + 1))) + (((3 * (p z - q z)) *
          (q z - 1)) * (q z + 1))) + (((p z + q z) * (q z - 1)) * (q z + 1)))) - (((4 * deriv w z)
          * z) * ((1 - q z) ^ 2))) - ((((8 * deriv w z) * z) * (q z - 1)) * (q z + 1)))) - ((((2 *
          (1 - q z)) * (p z - q z)) * (p z + q z)) * ((p z * ((((((-((1 - q z) ^ 2)) * (p z - q z))
          * (p z + q z)) + ((((1 - q z) ^ 2) * (p z - q z)) * (q z + 1))) + ((((1 - q z) ^ 2) * (p
          z + q z)) * (q z + 1))) + ((((p z - q z) * (p z + q z)) * (q z - 1)) * (q z + 1)))) -
          ((((4 * deriv w z) * z) * ((1 - q z) ^ 2)) * (q z + 1))))) - ((((1 - q z) * (p z - q z))
          * (q z + 1)) * ((p z * ((((((-((1 - q z) ^ 2)) * (p z - q z)) * (p z + q z)) + ((((1 - q
          z) ^ 2) * (p z - q z)) * (q z + 1))) + ((((1 - q z) ^ 2) * (p z + q z)) * (q z + 1))) +
          ((((p z - q z) * (p z + q z)) * (q z - 1)) * (q z + 1)))) - ((((4 * deriv w z) * z) * ((1
          - q z) ^ 2)) * (q z + 1))))) - ((((3 * (1 - q z)) * (p z + q z)) * (q z + 1)) * ((p z *
          ((((((-((1 - q z) ^ 2)) * (p z - q z)) * (p z + q z)) + ((((1 - q z) ^ 2) * (p z - q z))
          * (q z + 1))) + ((((1 - q z) ^ 2) * (p z + q z)) * (q z + 1))) + ((((p z - q z) * (p z +
          q z)) * (q z - 1)) * (q z + 1)))) - ((((4 * deriv w z) * z) * ((1 - q z) ^ 2)) * (q z +
          1))))) - ((((3 * (p z - q z)) * (p z + q z)) * (q z + 1)) * ((p z * ((((((-((1 - q z) ^
          2)) * (p z - q z)) * (p z + q z)) + ((((1 - q z) ^ 2) * (p z - q z)) * (q z + 1))) +
          ((((1 - q z) ^ 2) * (p z + q z)) * (q z + 1))) + ((((p z - q z) * (p z + q z)) * (q z -
          1)) * (q z + 1)))) - ((((4 * deriv w z) * z) * ((1 - q z) ^ 2)) * (q z + 1)))))) +
          (((((((((((16 * (p z ^ 2)) * deriv w z) * w z) * z) * ((1 - q z) ^ 3)) * (p z - q z)) *
          (p z + q z)) * ((q z + 1) ^ 2)) * (w z - 1)) * (w z - z)) * (z - 1))) + ((((((8 * (p z ^
          2)) * ((1 - q z) ^ 3)) * (p z - q z)) * (p z + q z)) * ((q z + 1) ^ 2)) * ((((((deriv w z
          ^ 2) * (z ^ 2)) * (z - 1)) * (((w z * (w z - 1)) + (w z * (w z - z))) + ((w z - 1) * (w z
          - z)))) - (((((2 * deriv w z) * w z) * z) * (w z - 1)) * (((z * (w z - z)) + (z * (z -
          1))) + ((w z - z) * (z - 1))))) + ((w z ^ 2) * (((2 * γ) * ((w z - z) ^ 2)) + ((z * (1 -
          (2 * γ))) * ((w z - 1) ^ 2))))))) + (((((((((2 * deriv w z) * w z) * z) * (1 - q z)) * (q
          z + 1)) * (w z - 1)) * (w z - z)) * (z - 1)) * (((((((-p z) * (p z - q z)) * (p z + q z))
          * (((((p z * ((((((-((1 - q z) ^ 2)) * (p z - q z)) - (((1 - q z) ^ 2) * (p z + q z))) +
          ((2 * ((1 - q z) ^ 2)) * (q z + 1))) + (((p z - q z) * (q z - 1)) * (q z + 1))) + (((p z
          + q z) * (q z - 1)) * (q z + 1)))) - ((((1 - q z) ^ 2) * (p z - q z)) * (p z + q z))) +
          ((((1 - q z) ^ 2) * (p z - q z)) * (q z + 1))) + ((((1 - q z) ^ 2) * (p z + q z)) * (q z
          + 1))) + ((((p z - q z) * (p z + q z)) * (q z - 1)) * (q z + 1)))) - ((p z * (p z - q z))
          * ((p z * ((((((-((1 - q z) ^ 2)) * (p z - q z)) * (p z + q z)) + ((((1 - q z) ^ 2) * (p
          z - q z)) * (q z + 1))) + ((((1 - q z) ^ 2) * (p z + q z)) * (q z + 1))) + ((((p z - q z)
          * (p z + q z)) * (q z - 1)) * (q z + 1)))) - ((((4 * deriv w z) * z) * ((1 - q z) ^ 2)) *
          (q z + 1))))) + (((3 * p z) * (p z + q z)) * ((p z * ((((((-((1 - q z) ^ 2)) * (p z - q
          z)) * (p z + q z)) + ((((1 - q z) ^ 2) * (p z - q z)) * (q z + 1))) + ((((1 - q z) ^ 2) *
          (p z + q z)) * (q z + 1))) + ((((p z - q z) * (p z + q z)) * (q z - 1)) * (q z + 1)))) -
          ((((4 * deriv w z) * z) * ((1 - q z) ^ 2)) * (q z + 1))))) + (((p z - q z) * (p z + q z))
          * ((p z * ((((((-((1 - q z) ^ 2)) * (p z - q z)) * (p z + q z)) + ((((1 - q z) ^ 2) * (p
          z - q z)) * (q z + 1))) + ((((1 - q z) ^ 2) * (p z + q z)) * (q z + 1))) + ((((p z - q z)
          * (p z + q z)) * (q z - 1)) * (q z + 1)))) - ((((4 * deriv w z) * z) * ((1 - q z) ^ 2)) *
          (q z + 1)))))))) / (((((((((-16) * (p z ^ 3)) * w z) * z) * ((p z - q z) ^ 4)) * ((q z -
          1) ^ 4)) * ((-w z) + z)) * (w z - 1)) * (z - 1)))) hh (fun z hz => ?_) (fun z hz => ?_)
      (fun z hz => ?_) hu hcover (fun z hz => ?_), fun ζ hζ => ?_, fun ζ hζ => ?_,
      fun ζ hζ => (hu0 ζ hζ).1, fun ζ hζ => (hu0 ζ hζ).2.1, fun ζ hζ => (hu0 ζ hζ).2.2⟩
  · have hz0 := h.ne_zero z hz
    have hQ0 : q z ≠ 0 := fun h' => hz0 (by rw [← hq z hz, h']; ring)
    have h1q : 1 + q z ≠ 0 := fun h' => hq1 z hz (by linear_combination h')
    have h1mq : 1 - q z ≠ 0 := fun h' => hderiv z hz (by rw [h']; simp)
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 3 h1mq))
      hQ0)) (mul_ne_zero (pow_ne_zero 5 h1q) hz0)
  · have hz0 := h.ne_zero z hz
    have hQ0 : q z ≠ 0 := fun h' => hz0 (by rw [← hq z hz, h']; ring)
    have h1q : 1 + q z ≠ 0 := fun h' => hq1 z hz (by linear_combination h')
    have h1mq : 1 - q z ≠ 0 := fun h' => hderiv z hz (by rw [h']; simp)
    have hQ := hq' z hz
    have hP := hp' z hz
    have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have hq1' : q z + 1 ≠ 0 := fun h' => hq1 z hz (by linear_combination h')
    have hqm1 : q z - 1 ≠ 0 := fun h' => h1mq (by linear_combination -h')
    have hP0 : p z ≠ 0 := fun h' => h.w_ne_zero z hz (by rw [← hp z hz, h']; ring)
    have hPQ : p z - q z ≠ 0 := sub_ne_zero.mpr (hpq z hz)
    have h0 := h.w_ne_zero z hz
    have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : w z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have h2' : -w z + z ≠ 0 := fun h' => h2 (by linear_combination -h')
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hpw := hp z hz
    have hsq : z = q z ^ 4 := (hq z hz).symm
    have hc := (((((hQ).const_sub 1).div ((hQ).const_add 1) h1q)).pow 2).mul (((((hP).add (hQ)).div
        ((hP).sub (hQ)) hPQ)).pow 2)
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs]
    generalize deriv w z = b
    generalize w z = a at h0 h1 h2 h2' hpw ⊢
    generalize p z = P at hP0 hPQ hpw ⊢
    generalize q z = Q at hQ0 h1q hq1' h1mq hqm1 hPQ hsq ⊢
    subst hpw
    subst hsq
    field_simp
    all_goals set_option maxRecDepth 100000 in ring
  · have hz0 := h.ne_zero z hz
    have hQ0 : q z ≠ 0 := fun h' => hz0 (by rw [← hq z hz, h']; ring)
    have h1q : 1 + q z ≠ 0 := fun h' => hq1 z hz (by linear_combination h')
    have h1mq : 1 - q z ≠ 0 := fun h' => hderiv z hz (by rw [h']; simp)
    have hQ := hq' z hz
    have hP := hp' z hz
    have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have hq1' : q z + 1 ≠ 0 := fun h' => hq1 z hz (by linear_combination h')
    have hqm1 : q z - 1 ≠ 0 := fun h' => h1mq (by linear_combination -h')
    have hP0 : p z ≠ 0 := fun h' => h.w_ne_zero z hz (by rw [← hp z hz, h']; ring)
    have hPQ : p z - q z ≠ 0 := sub_ne_zero.mpr (hpq z hz)
    have h0 := h.w_ne_zero z hz
    have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : w z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have h2' : -w z + z ≠ 0 := fun h' => h2 (by linear_combination -h')
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hpw := hp z hz
    have hsq : z = q z ^ 4 := (hq z hz).symm
    have hc := ((((((hQ).mul ((hP).add (hQ))).mul (((hP).mul (((((((((hQ).const_sub 1).pow
        2).neg).mul ((hP).sub (hQ))).mul ((hP).add (hQ))).add (((((hQ).const_sub 1).pow 2).mul
        ((hP).sub (hQ))).mul ((hQ).add_const 1))).add (((((hQ).const_sub 1).pow 2).mul ((hP).add
        (hQ))).mul ((hQ).add_const 1))).add (((((hP).sub (hQ)).mul ((hP).add (hQ))).mul
        ((hQ).sub_const 1)).mul ((hQ).add_const 1)))).sub (((((hv).const_mul 4).mul (hid)).mul
        (((hQ).const_sub 1).pow 2)).mul ((hQ).add_const 1)))).div (((((hP).const_mul 2).mul
        (hid)).mul (((hP).sub (hQ)).pow 3)).mul (((hQ).add_const 1).pow 3)) (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hP0) hz0) (pow_ne_zero 3 hPQ))
        (pow_ne_zero 3 hq1')))).div ((((((((hQ).const_sub 1).pow 3).const_mul 2).mul (hQ)).neg).div
        ((((hQ).const_add 1).pow 5).mul (hid)) (mul_ne_zero (pow_ne_zero 5 h1q) hz0))) (div_ne_zero
        (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 h1mq)) hQ0))
        (mul_ne_zero (pow_ne_zero 5 h1q) hz0)))
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVIRhs]
    generalize deriv w z = b
    generalize w z = a at h0 h1 h2 h2' hpw ⊢
    generalize p z = P at hP0 hPQ hpw ⊢
    generalize q z = Q at hQ0 h1q hq1' h1mq hqm1 hPQ hsq ⊢
    subst hpw
    subst hsq
    field_simp
    all_goals set_option maxRecDepth 100000 in ring
  · have hz0 := h.ne_zero z hz
    have hQ0 : q z ≠ 0 := fun h' => hz0 (by rw [← hq z hz, h']; ring)
    have h1q : 1 + q z ≠ 0 := fun h' => hq1 z hz (by linear_combination h')
    have h1mq : 1 - q z ≠ 0 := fun h' => hderiv z hz (by rw [h']; simp)
    have hQ := hq' z hz
    have hP := hp' z hz
    have hw := h.ode.hasDerivAt hz
    have hv := h.ode.hasDerivAt_deriv z hz
    have hid := hasDerivAt_id z
    have hq1' : q z + 1 ≠ 0 := fun h' => hq1 z hz (by linear_combination h')
    have hqm1 : q z - 1 ≠ 0 := fun h' => h1mq (by linear_combination -h')
    have hP0 : p z ≠ 0 := fun h' => h.w_ne_zero z hz (by rw [← hp z hz, h']; ring)
    have hPQ : p z - q z ≠ 0 := sub_ne_zero.mpr (hpq z hz)
    have h0 := h.w_ne_zero z hz
    have h1 : w z - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one z hz)
    have h2 : w z - z ≠ 0 := sub_ne_zero.mpr (h.w_ne_self z hz)
    have h2' : -w z + z ≠ 0 := fun h' => h2 (by linear_combination -h')
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (h.ne_one z hz)
    have hpw := hp z hz
    have hsq : z = q z ^ 4 := (hq z hz).symm
    have hu' := hu0 _ (hmaps z hz)
    rw [hu z hz] at hu'
    have hU0 := hu'.1
    have hU1 := sub_ne_zero.mpr hu'.2.1
    have hUz := sub_ne_zero.mpr hu'.2.2
    have hZ0 : ((1 - q z) / (1 + q z)) ^ 4 ≠ 0 := pow_ne_zero 4 (div_ne_zero h1mq h1q)
    have hZ1 : ((1 - q z) / (1 + q z)) ^ 4 - 1 ≠ 0 := by
      rw [div_pow, div_sub_one (pow_ne_zero 4 h1q)]
      refine div_ne_zero ?_ (pow_ne_zero 4 h1q)
      have hq2 : 1 + q z ^ 2 ≠ 0 := fun h' => h.ne_one z hz (by
        rw [← hq z hz]
        linear_combination (q z ^ 2 - 1) * h')
      rw [show (1 - q z) ^ 4 - (1 + q z) ^ 4 = -8 * q z * (1 + q z ^ 2) by ring]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hQ0) hq2
    simp only [painleveVIRhs]
    generalize eZ : ((1 - q z) / (1 + q z)) ^ 4 = Z at hZ0 hZ1 hUz ⊢
    generalize eU : ((1 - q z) / (1 + q z)) ^ 2 * ((p z + q z) / (p z - q z)) ^ 2 =
        U0 at hU0 hU1 hUz ⊢
    generalize deriv w z = b
    generalize w z = a at h0 h1 h2 h2' hpw ⊢
    generalize p z = P at hP0 hPQ hpw eU ⊢
    generalize q z = Q at hQ0 h1q hq1' h1mq hqm1 hPQ hsq eU eZ ⊢
    subst hpw
    subst hsq
    field_simp
    subst eU eZ
    field_simp
    ring
  · obtain ⟨z, hz, rfl⟩ := hcover hζ
    have hz0 := h.ne_zero z hz
    have hQ0 : q z ≠ 0 := fun h' => hz0 (by rw [← hq z hz, h']; ring)
    have h1q : 1 + q z ≠ 0 := fun h' => hq1 z hz (by linear_combination h')
    have h1mq : 1 - q z ≠ 0 := fun h' => hderiv z hz (by rw [h']; simp)
    exact pow_ne_zero 4 (div_ne_zero h1mq h1q)
  · obtain ⟨z, hz, rfl⟩ := hcover hζ
    have hz0 := h.ne_zero z hz
    have hQ0 : q z ≠ 0 := fun h' => hz0 (by rw [← hq z hz, h']; ring)
    have h1q : 1 + q z ≠ 0 := fun h' => hq1 z hz (by linear_combination h')
    have h1mq : 1 - q z ≠ 0 := fun h' => hderiv z hz (by rw [h']; simp)
    have hZ1 : ((1 - q z) / (1 + q z)) ^ 4 - 1 ≠ 0 := by
      rw [div_pow, div_sub_one (pow_ne_zero 4 h1q)]
      refine div_ne_zero ?_ (pow_ne_zero 4 h1q)
      have hq2 : 1 + q z ^ 2 ≠ 0 := fun h' => h.ne_one z hz (by
        rw [← hq z hz]
        linear_combination (q z ^ 2 - 1) * h')
      rw [show (1 - q z) ^ 4 - (1 + q z) ^ 4 = -8 * q z * (1 + q z ^ 2) by ring]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hQ0) hq2
    beta_reduce
    exact fun h' => hZ1 (by rw [h', sub_self])

end DLMF.Painleve
