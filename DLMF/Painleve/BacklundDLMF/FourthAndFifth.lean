/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.BacklundDLMF.SecondAndThird

/-!
# Backlund transformations for Painleve IV and V

Transformations of Painleve IV and V and the connection between Painleve III and V.

Source references and common attribution are retained in
`DLMF.Painleve.BacklundDLMF`.
-/

@[expose] public noncomputable section

open Set Filter

open scoped Topology

namespace DLMF.Painleve

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

end DLMF.Painleve
end
