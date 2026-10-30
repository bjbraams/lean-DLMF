/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.BacklundDLMF.FourthAndFifth

/-!
# Backlund transformations for Painleve VI

Painleve VI parameter symmetries, Okamoto transformations and quadratic and quartic changes of
variables.

Source references and common attribution are retained in
`DLMF.Painleve.BacklundDLMF`.
-/

@[expose] public noncomputable section

open Set Filter

open scoped Topology

namespace DLMF.Painleve

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
    (h : IsPainleveVIOn 0 0 γ (1 / 2 - γ) w U) (hU : IsOpen U)
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

end
