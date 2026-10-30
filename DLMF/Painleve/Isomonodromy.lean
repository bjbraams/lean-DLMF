/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic
public import DLMF.Airy.Properties
public import DLMF.Painleve.Basic

/-!
# Isomonodromy problems and the integral equation: DLMF §§32.4–32.5

The Lax pairs of §32.4 are stated in jet form, as the existing Beals–Wong file
`DLMF.Painleve.LaxPair` does: the `z`-derivative of `A(z, λ)` along a function `w` is written
out explicitly in terms of `w, w', w''` (for `PIII` in terms of the four unknowns and their
derivatives), and the zero-curvature condition 32.4.3 is shown to be the Painlevé equation.
The integral equation of §32.5 (Ablowitz–Segur) is acquired as an admitted statement.
-/

@[expose] public noncomputable section

open Set Filter Matrix MeasureTheory
open scoped Topology

namespace DLMF.Painleve

/-! ## The compatibility condition (§32.4(i)) -/

/-- DLMF 32.4.1–32.4.3: if `Ψ_λ = AΨ` and `Ψ_z = BΨ` (32.4.1), the two mixed second
derivatives `∂_z(AΨ) = A_zΨ + A(BΨ)` and `∂_λ(BΨ) = B_λΨ + B(AΨ)` differ by
`(A_z - B_λ + AB - BA)Ψ`; so 32.4.2 holds when the compatibility condition 32.4.3 holds.
Here `Az`, `Bl` stand for `∂A/∂z`, `∂B/∂λ`. -/
@[dlmf 32.4.E1, dlmf 32.4.E2, dlmf 32.4.E3]
theorem lax_mixed_derivatives {n : ℕ} (A B Az Bl Ψ : Matrix (Fin n) (Fin n) ℂ) :
    (Az * Ψ + A * (B * Ψ)) - (Bl * Ψ + B * (A * Ψ)) = (Az - Bl + A * B - B * A) * Ψ := by
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- DLMF 32.4.3 ⇒ 32.4.2: under the compatibility condition the mixed derivatives agree. -/
@[dlmf 32.4.E2, dlmf 32.4.E3]
theorem lax_mixed_derivatives_eq {n : ℕ} {A B Az Bl : Matrix (Fin n) (Fin n) ℂ}
    (h : Az - Bl + A * B - B * A = 0) (Ψ : Matrix (Fin n) (Fin n) ℂ) :
    Az * Ψ + A * (B * Ψ) = Bl * Ψ + B * (A * Ψ) := by
  have := lax_mixed_derivatives A B Az Bl Ψ
  rw [h, Matrix.zero_mul] at this
  exact sub_eq_zero.mp this

/-! ## `PI` (§32.4(ii)) -/

/-- The curvature of the `PI` Lax pair 32.4.4–32.4.5, along a function with `w' = v`,
`w'' = w₂`: `∂A/∂z - ∂B/∂λ + AB - BA = 2λ(6w² + z - w₂)σ₁`. Here
`∂A/∂z = (4wv + 1)σ₃ - i(4λ²v + 4wv + 1)σ₂ - 2λw₂σ₁` and
`∂B/∂λ = (1 - w/λ²)σ₃ + (iw/λ²)σ₂`. -/
theorem painleveI_lax_curvature (z w v w₂ l : ℂ) (hl : l ≠ 0) :
    ((4 * w * v + 1) • laxSigma3 - (Complex.I * (4 * l ^ 2 * v + 4 * w * v + 1)) • laxSigma2 -
        (2 * l * w₂) • laxSigma1) -
      ((1 - w / l ^ 2) • laxSigma3 + (Complex.I * w / l ^ 2) • laxSigma2) +
      painleveILaxA z w v l * painleveILaxB w l - painleveILaxB w l * painleveILaxA z w v l =
      (2 * l * (6 * w ^ 2 + z - w₂)) • laxSigma1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [painleveILaxA, painleveILaxB, laxSigma1, laxSigma2, laxSigma3, Matrix.mul_apply,
      Fin.sum_univ_two]
    try field_simp
    try ring_nf
    try simp only [Complex.I_sq]
    try ring

/-- DLMF 32.4.4–32.4.5: `PI` is the compatibility condition 32.4.3 of the linear system
32.4.1 with the matrices 32.4.4–32.4.5 (at any `λ ≠ 0`; jet form, see
`painleveI_lax_curvature`). -/
@[dlmf 32.4.E4, dlmf 32.4.E5]
theorem painleveI_lax_compatibility_iff (z w v w₂ l : ℂ) (hl : l ≠ 0) :
    ((4 * w * v + 1) • laxSigma3 - (Complex.I * (4 * l ^ 2 * v + 4 * w * v + 1)) • laxSigma2 -
        (2 * l * w₂) • laxSigma1) -
      ((1 - w / l ^ 2) • laxSigma3 + (Complex.I * w / l ^ 2) • laxSigma2) +
      painleveILaxA z w v l * painleveILaxB w l - painleveILaxB w l * painleveILaxA z w v l = 0 ↔
      w₂ = painleveIRhs z w v := by
  rw [painleveI_lax_curvature z w v w₂ l hl, painleveIRhs]
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    simp [laxSigma1] at h01
    rcases h01 with h01 | h01
    · exact absurd h01 hl
    · linear_combination -h01
  · intro h
    rw [h, sub_self, mul_zero, zero_smul]

/-! ## `PII` (§32.4(iii)) -/

/-- The curvature of the `PII` Lax pair 32.4.6–32.4.7, along a function with `w' = v`,
`w'' = w₂`: `∂A/∂z - ∂B/∂λ + AB - BA = 2(2w³ + zw + α - w₂)σ₂`. Here
`∂A/∂z = -i(4wv + 1)σ₃ - 2w₂σ₂ + 4λvσ₁` and `∂B/∂λ = -iσ₃`. -/
theorem painleveII_lax_curvature (α z w v w₂ l : ℂ) (hl : l ≠ 0) :
    ((-Complex.I * (4 * w * v + 1)) • laxSigma3 - (2 * w₂) • laxSigma2 + (4 * l * v) • laxSigma1) -
      (-Complex.I) • laxSigma3 +
      painleveIILaxA α z w v l * painleveIILaxB w l -
        painleveIILaxB w l * painleveIILaxA α z w v l =
      (2 * (2 * w ^ 3 + z * w + α - w₂)) • laxSigma2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [painleveIILaxA, painleveIILaxB, laxSigma1, laxSigma2, laxSigma3, Matrix.mul_apply,
      Fin.sum_univ_two]
    try field_simp
    try ring_nf
    try simp only [Complex.I_sq]
    try ring

/-- DLMF 32.4.6–32.4.7: `PII` is the compatibility condition of 32.4.1 with the matrices
32.4.6–32.4.7 (at any `λ ≠ 0`; jet form). -/
@[dlmf 32.4.E6, dlmf 32.4.E7]
theorem painleveII_lax_compatibility_iff (α z w v w₂ l : ℂ) (hl : l ≠ 0) :
    ((-Complex.I * (4 * w * v + 1)) • laxSigma3 - (2 * w₂) • laxSigma2 + (4 * l * v) • laxSigma1) -
      (-Complex.I) • laxSigma3 +
      painleveIILaxA α z w v l * painleveIILaxB w l -
        painleveIILaxB w l * painleveIILaxA α z w v l = 0 ↔
      w₂ = painleveIIRhs α z w v := by
  rw [painleveII_lax_curvature α z w v w₂ l hl, painleveIIRhs]
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
    simp [laxSigma2] at h01
    linear_combination -h01
  · intro h
    rw [h, sub_self, mul_zero, zero_smul]

/-! ## `PIII` (§32.4(iv)) -/

/-- DLMF 32.4.8–32.4.13 (the system implies compatibility): along functions satisfying
32.4.10–32.4.13 (derivatives `painleveIIISystemRhs`), the `PIII` Lax pair 32.4.8–32.4.9 satisfies
the zero-curvature condition 32.4.3 at every `λ ≠ 0`, `z ≠ 0` (with `v₁ ≠ 0`). Jet form:
`∂A/∂z = diag(1/4, -1/4) + [[0, u₀'],[u₁', 0]]/λ + M_z/λ²` and
`∂B/∂λ = diag(1/4, -1/4) + M/(zλ²)`. -/
@[dlmf 32.4.E8, dlmf 32.4.E9, dlmf 32.4.E10, dlmf 32.4.E11, dlmf 32.4.E12, dlmf 32.4.E13]
theorem painleveIII_lax_compatibility (θinf z u₀ u₁ v₀ v₁ l : ℂ) (hl : l ≠ 0) (hz : z ≠ 0)
    (hv : v₁ ≠ 0) :
    let d := painleveIIISystemRhs θinf z u₀ u₁ v₀ v₁
    (!![1 / 4, 0; 0, -1 / 4] + (1 / l) • !![0, d.1; d.2.1, 0] +
        (1 / l ^ 2) • painleveIIILaxMDeriv z v₀ v₁ d.2.2.1 d.2.2.2) -
      (!![1 / 4, 0; 0, -1 / 4] + (1 / (z * l ^ 2)) • painleveIIILaxM z v₀ v₁) +
      painleveIIILaxA θinf z u₀ u₁ v₀ v₁ l * painleveIIILaxB z u₀ u₁ v₀ v₁ l -
      painleveIIILaxB z u₀ u₁ v₀ v₁ l * painleveIIILaxA θinf z u₀ u₁ v₀ v₁ l = 0 := by
  intro d
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [d, painleveIIISystemRhs, painleveIIILaxMDeriv, painleveIIILaxA, painleveIIILaxB,
      painleveIIILaxM, Matrix.mul_apply, Fin.sum_univ_two]
    try field_simp
    try ring

/-- DLMF 32.4.8–32.4.13 (compatibility implies the system): if the zero-curvature
condition holds for all `λ ≠ 0` with some derivative values `(du₀, du₁, dv₀, dv₁)`, these are
the values 32.4.10–32.4.13. -/
@[dlmf 32.4.E10, dlmf 32.4.E11, dlmf 32.4.E12, dlmf 32.4.E13]
theorem painleveIII_lax_system_of_compatibility (θinf z u₀ u₁ v₀ v₁ du₀ du₁ dv₀ dv₁ : ℂ)
    (hz : z ≠ 0) (hv : v₁ ≠ 0)
    (h : ∀ l : ℂ, l ≠ 0 →
      (!![1 / 4, 0; 0, -1 / 4] + (1 / l) • !![0, du₀; du₁, 0] +
          (1 / l ^ 2) • painleveIIILaxMDeriv z v₀ v₁ dv₀ dv₁) -
        (!![1 / 4, 0; 0, -1 / 4] + (1 / (z * l ^ 2)) • painleveIIILaxM z v₀ v₁) +
        painleveIIILaxA θinf z u₀ u₁ v₀ v₁ l * painleveIIILaxB z u₀ u₁ v₀ v₁ l -
        painleveIIILaxB z u₀ u₁ v₀ v₁ l * painleveIIILaxA θinf z u₀ u₁ v₀ v₁ l = 0) :
    (du₀, du₁, dv₀, dv₁) = painleveIIISystemRhs θinf z u₀ u₁ v₀ v₁ := by
  have E (l : ℂ) (hl : l ≠ 0) (i j : Fin 2) := congrFun (congrFun (h l hl) i) j
  have a00 := E 1 one_ne_zero 0 0
  have a01 := E 1 one_ne_zero 0 1
  have b01 := E 2 two_ne_zero 0 1
  have a10 := E 1 one_ne_zero 1 0
  have b10 := E 2 two_ne_zero 1 0
  simp [painleveIIILaxMDeriv, painleveIIILaxA, painleveIIILaxB,
      painleveIIILaxM] at a00 a01 b01 a10 b10
  field_simp at a00 a01 b01 a10 b10
  have g0 : du₀ * z - (θinf * u₀ - v₀ * v₁ * z) = 0 := by
    linear_combination (-1 / 8 : ℂ) * a01 + (1 / 8 : ℂ) * b01
  have g1 : v₁ * (du₁ * 2 * v₁ * z - (-2 * θinf * u₁ * v₁ - 2 * v₀ * z + z ^ 2)) = 0 := by
    linear_combination (-1 / 8 : ℂ) * a10 + (1 / 8 : ℂ) * b10
  have g2 : dv₀ * v₁ * z - (2 * u₀ * v₀ - u₀ * z + 2 * u₁ * v₀ * v₁ ^ 2 + v₀ * v₁) = 0 := by
    linear_combination (1 / 32 : ℂ) * a00
  have g3 : z * (dv₁ * z - (-θinf * v₁ + 2 * u₀ - 2 * u₁ * v₁ ^ 2)) = 0 := by
    linear_combination (-1 / 8 : ℂ) * a00 + (-1 / 2 : ℂ) * a01 + (1 / 4 : ℂ) * b01 +
      (1 / 4 : ℂ) * a10 + (-1 / 8 : ℂ) * b10
  have g1' := (mul_eq_zero.mp g1).resolve_left hv
  have g3' := (mul_eq_zero.mp g3).resolve_left hz
  simp only [painleveIIISystemRhs, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp; linear_combination g0
  · field_simp; linear_combination g1'
  · field_simp; linear_combination g2
  · field_simp; linear_combination g3'

/-- DLMF 32.4.14: along a solution of 32.4.10–32.4.13 on an open set (with `z, v₀, v₁ ≠ 0`),
`w = -u₀/(v₀v₁)` satisfies `zw' = (4v₀ - z)w² + (2θ∞ - 1)w + z`. -/
@[dlmf 32.4.E14]
theorem painleveIII_lax_riccati {θinf : ℂ} {u₀ u₁ v₀ v₁ : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hv₀ : v₀ z ≠ 0) (hv₁ : v₁ z ≠ 0)
    (hu₀' : HasDerivAt u₀ (painleveIIISystemRhs θinf z (u₀ z) (u₁ z) (v₀ z) (v₁ z)).1 z)
    (hv₀' : HasDerivAt v₀ (painleveIIISystemRhs θinf z (u₀ z) (u₁ z) (v₀ z) (v₁ z)).2.2.1 z)
    (hv₁' : HasDerivAt v₁ (painleveIIISystemRhs θinf z (u₀ z) (u₁ z) (v₀ z) (v₁ z)).2.2.2 z) :
    HasDerivAt (fun z => -u₀ z / (v₀ z * v₁ z))
      (((4 * v₀ z - z) * (-u₀ z / (v₀ z * v₁ z)) ^ 2 +
        (2 * θinf - 1) * (-u₀ z / (v₀ z * v₁ z)) + z) / z) z := by
  have hd := hu₀'.neg.div (hv₀'.mul hv₁') (mul_ne_zero hv₀ hv₁)
  convert hd using 1
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
      Pi.div_apply, id,
      Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  simp only [painleveIIISystemRhs]
  field_simp
  ring

/-- DLMF 32.4.16: `θ₀ = (4v₀/z)(θ∞(1 - z/(4v₀)) + (z - 2v₀)u₀/(2v₀v₁) + u₁v₁)` is a first
integral of 32.4.10–32.4.13: its derivative along a solution vanishes. -/
@[dlmf 32.4.E16]
theorem painleveIII_lax_firstIntegral {θinf : ℂ} {u₀ u₁ v₀ v₁ : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hv₀ : v₀ z ≠ 0) (hv₁ : v₁ z ≠ 0)
    (hu₀' : HasDerivAt u₀ (painleveIIISystemRhs θinf z (u₀ z) (u₁ z) (v₀ z) (v₁ z)).1 z)
    (hu₁' : HasDerivAt u₁ (painleveIIISystemRhs θinf z (u₀ z) (u₁ z) (v₀ z) (v₁ z)).2.1 z)
    (hv₀' : HasDerivAt v₀ (painleveIIISystemRhs θinf z (u₀ z) (u₁ z) (v₀ z) (v₁ z)).2.2.1 z)
    (hv₁' : HasDerivAt v₁ (painleveIIISystemRhs θinf z (u₀ z) (u₁ z) (v₀ z) (v₁ z)).2.2.2 z) :
    HasDerivAt (fun z => 4 * v₀ z / z * (θinf * (1 - z / (4 * v₀ z)) +
      (z - 2 * v₀ z) / (2 * v₀ z * v₁ z) * u₀ z + u₁ z * v₁ z)) 0 z := by
  have hid := hasDerivAt_id z
  have h1 := (hv₀'.const_mul 4).div hid hz
  have h2 := ((hid.div (hv₀'.const_mul 4)
    (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hv₀)).const_sub 1).const_mul θinf
  have h3 := ((hid.sub (hv₀'.const_mul 2)).div ((hv₀'.const_mul 2).mul hv₁')
    (mul_ne_zero (mul_ne_zero two_ne_zero hv₀) hv₁)).mul hu₀'
  have hd := h1.mul ((h2.add h3).add (hu₁'.mul hv₁'))
  convert hd using 1
  · funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, id]
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, id]
    simp only [painleveIIISystemRhs]
    field_simp
    ring

/-- DLMF 32.4.15: along a solution of 32.4.10–32.4.13 on an open set `U` (with `z, u₀, v₀, v₁`
nonzero) on which the first integral 32.4.16 has the constant value `θ₀`, the function
`w = -u₀/(v₀v₁)` solves `PIII` with `(α, β, γ, δ) = (2θ₀, 2(1 - θ∞), 1, -1)`. -/
@[dlmf 32.4.E15, dlmf 32.4.E16]
theorem painleveIII_lax_isPainleveIIIOn {θinf θ₀ : ℂ} {u₀ u₁ v₀ v₁ : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hz : ∀ z ∈ U, z ≠ 0) (hu₀ : ∀ z ∈ U, u₀ z ≠ 0) (hv₀ : ∀ z ∈ U, v₀ z ≠ 0)
    (hv₁ : ∀ z ∈ U, v₁ z ≠ 0)
    (hu₀' : ∀ z ∈ U, HasDerivAt u₀ (painleveIIISystemRhs θinf z (u₀ z) (u₁ z) (v₀ z) (v₁ z)).1 z)
    (hu₁' : ∀ z ∈ U, HasDerivAt u₁ (painleveIIISystemRhs θinf z (u₀ z) (u₁ z) (v₀ z) (v₁ z)).2.1 z)
    (hv₀' : ∀ z ∈ U,
      HasDerivAt v₀ (painleveIIISystemRhs θinf z (u₀ z) (u₁ z) (v₀ z) (v₁ z)).2.2.1 z)
    (hv₁' : ∀ z ∈ U,
      HasDerivAt v₁ (painleveIIISystemRhs θinf z (u₀ z) (u₁ z) (v₀ z) (v₁ z)).2.2.2 z)
    (hθ : ∀ z ∈ U, 4 * v₀ z / z * (θinf * (1 - z / (4 * v₀ z)) +
      (z - 2 * v₀ z) / (2 * v₀ z * v₁ z) * u₀ z + u₁ z * v₁ z) = θ₀) :
    IsPainleveIIIOn (2 * θ₀) (2 * (1 - θinf)) 1 (-1) (fun z => -u₀ z / (v₀ z * v₁ z)) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => ((4 * v₀ z - z) *
      (-u₀ z / (v₀ z * v₁ z)) ^ 2 + (2 * θinf - 1) * (-u₀ z / (v₀ z * v₁ z)) + z) / z)
    (fun z hz' => painleveIII_lax_riccati (hz z hz') (hv₀ z hz') (hv₁ z hz') (hu₀' z hz')
      (hv₀' z hz') (hv₁' z hz')) (fun z hz' => ?_), hz,
    fun z hz' => div_ne_zero (neg_ne_zero.mpr (hu₀ z hz')) (mul_ne_zero (hv₀ z hz') (hv₁ z hz'))⟩
  have hid := hasDerivAt_id z
  have h0 := hz z hz'
  have a0 := hu₀ z hz'
  have b0 := hv₀ z hz'
  have b1 := hv₁ z hz'
  have hw := (hu₀' z hz').neg.div ((hv₀' z hz').mul (hv₁' z hz')) (mul_ne_zero b0 b1)
  have hd := (((((hv₀' z hz').const_mul 4).sub hid).mul (hw.pow 2)).add
    (hw.const_mul (2 * θinf - 1))).add hid |>.div hid h0
  convert hd using 1
  · funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
      Pi.div_apply, id]
  · rw [← hθ z hz']
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
      Pi.div_apply, id, painleveIIIRhs, painleveIIISystemRhs]
    generalize u₀ z = a at a0 ⊢
    generalize v₀ z = b at b0 ⊢
    generalize v₁ z = c at b1 ⊢
    generalize u₁ z = d
    field_simp
    ring_nf
    field_simp
    ring

/-! ## The integral equation (§32.5) -/

/-- DLMF 32.5.1–32.5.3 (Ablowitz–Segur): let `K(z, ζ)` (real variables) be a continuous
solution of `K(z, ζ) = k Ai((z+ζ)/2) + (k²/4) ∫_z^∞ ∫_z^∞ K(z, s) Ai((s+t)/2) Ai((t+ζ)/2) ds dt`.
Then `w(z) = K(z, z)` solves `PII` with `α = 0` on `ℝ` (Beals–Wong form `IsPIIOn 0`, which is
DLMF's `α = 0`) and `w(z) ~ k Ai(z)` as `z → +∞`. The hypothesis `|k| ≤ 1` is added: for
`|k| > 1` the corresponding solution of `PII` has real poles and the integral equation is not
uniquely solvable for every `z`. -/
@[dlmf 32.5.E1, dlmf 32.5.E2, dlmf 32.5.E3]
theorem painleveII_integralEquation {k : ℝ} (hk : |k| ≤ 1) {K : ℝ → ℝ → ℝ}
    (hKc : Continuous (Function.uncurry K))
    (hK : ∀ z ζ : ℝ, K z ζ = k * (DLMF.Airy.airyAi (((z + ζ) / 2 : ℝ) : ℂ)).re +
      k ^ 2 / 4 * ∫ t in Ioi z, ∫ s in Ioi z,
        K z s * (DLMF.Airy.airyAi (((s + t) / 2 : ℝ) : ℂ)).re *
        (DLMF.Airy.airyAi (((t + ζ) / 2 : ℝ) : ℂ)).re) :
    IsPIIOn (0 : ℝ) (fun z => K z z) univ ∧
      Asymptotics.IsEquivalent atTop (fun z => K z z)
        (fun z => k * (DLMF.Airy.airyAi (z : ℂ)).re) := by
  sorry

end DLMF.Painleve
