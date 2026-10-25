/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.LegendreIdentities

/-!
# Connection formulas for Legendre's integrals (DLMF §19.7)

Statements of DLMF 19.7.1–19.7.10. Legendre's relation (19.7.1) is proved for real `0 < k < 1`
from the existing real `DLMF.Elliptic.legendre_relation` and admitted on the complex domain.
The modulus transformations 19.7.2–19.7.3 are stated for complex `k`; the transformations
19.7.4–19.7.7 for the real amplitudes on which DLMF states them (19.7.7 with complex `k`); the
parameter changes 19.7.8–19.7.10 for real data, with Cauchy principal values. Here
`k' = jacobiComodulusk k` (principal), `c = csc²φ` and `R_C = symEllIntRC`.

**Convention note.** DLMF prints the second and fourth formulas of 19.7.2,
`K(-ik'/k) = kK(k')` and `E(-ik'/k) = (1/k)E(k')`, without a condition; their left sides are even
in `k` (they depend on `k²` only) and the right sides odd, so they hold for `Re k > 0` (as in
19.7.3, which DLMF states for `Re k > 0`) and change sign for `Re k < 0`; checked numerically
with mpmath at `k = 0.6, 0.5 + 0.3i, 1.3 + 0.5i, 0.3 - 0.9i` (valid) and `k = -0.4 + 0.7i,
-1.3 + 0.5i, -0.3 - 2i` (sign reversed). They are acquired with `0 < Re k`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-! ### §19.7(i) Complete integrals of the first and second kinds -/

/-- DLMF 19.7.1 (Legendre's relation) for real `0 < k < 1`:
`E(k)K'(k) + E'(k)K(k) - K(k)K'(k) = π/2`. -/
@[dlmf 19.7.E1]
theorem legendre_relation_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    compEllIntEk k * cCompEllIntKk k + cCompEllIntEk k * compEllIntKk k -
      compEllIntKk k * cCompEllIntKk k = π / 2 := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  rw [compEllIntEk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk2.le,
    compEllIntKk_eq_ofReal (m := k ^ 2) (by push_cast; ring) hk2.le, cCompEllIntKk_ofReal hk0,
    cCompEllIntEk_ofReal hk0]
  have h := DLMF.Elliptic.legendre_relation (m := k ^ 2) (by positivity) hk2
  exact_mod_cast h

/-- **Admitted.** DLMF 19.7.1 (Legendre's relation) for complex `k` with `k ∉ (-∞, 0]` and
`k² ∉ [1, ∞)`: `E(k)K'(k) + E'(k)K(k) - K(k)K'(k) = π/2` (with DLMF's continued `K'`, `E'`). -/
@[dlmf 19.7.E1]
theorem legendre_relation_complex {k : ℂ} (hk : k ∈ slitPlane) (hk1 : 1 - k ^ 2 ∈ slitPlane) :
    compEllIntEk k * cCompEllIntKk k + cCompEllIntEk k * compEllIntKk k -
      compEllIntKk k * cCompEllIntKk k = π / 2 := by
  sorry

/-- **Admitted.** DLMF 19.7.2 (first and third formulas): `K(ik/k') = k'K(k)` and
`E(ik/k') = (1/k')E(k)` in the principal domain `1 - k² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.7.E2]
theorem compEllInt_imaginary_modulus {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    compEllIntKk (I * k / jacobiComodulusk k) = jacobiComodulusk k * compEllIntKk k ∧
      compEllIntEk (I * k / jacobiComodulusk k) = compEllIntEk k / jacobiComodulusk k := by
  sorry

/-- **Admitted.** DLMF 19.7.2 (second and fourth formulas), with the implicit condition `Re k > 0`
(see the module docstring): `K(-ik'/k) = kK(k')` and `E(-ik'/k) = (1/k)E(k')`, for
`k² ∉ (-∞, 0]`. -/
@[dlmf 19.7.E2]
theorem compEllInt_imaginary_comodulus {k : ℂ} (hk : 0 < k.re) (hk2 : k ^ 2 ∈ slitPlane) :
    compEllIntKk (-I * jacobiComodulusk k / k) = k * compEllIntKk (jacobiComodulusk k) ∧
      compEllIntEk (-I * jacobiComodulusk k / k) = compEllIntEk (jacobiComodulusk k) / k := by
  sorry

/-- **Admitted.** DLMF 19.7.3 (Fettis): for `Re k > 0` and `Im k² ≠ 0`, with `s = 1` if
`Im k² > 0` and `s = -1` if `Im k² < 0` (DLMF's upper/lower signs),
`K(1/k) = k(K(k) - s i K(k'))`, `K(1/k') = k'(K(k') + s i K(k))`,
`E(1/k) = (1/k)(E(k) + s i E(k') - k'²K(k) - s i k² K(k'))`,
`E(1/k') = (1/k')(E(k') - s i E(k) - k²K(k') + s i k'² K(k))`. -/
@[dlmf 19.7.E3]
theorem compEllInt_reciprocal_modulus {k : ℂ} (hk : 0 < k.re) {s : ℂ}
    (hs : (0 < (k ^ 2).im ∧ s = 1) ∨ ((k ^ 2).im < 0 ∧ s = -1)) :
    compEllIntKk (1 / k) = k * (compEllIntKk k - s * I * compEllIntKk (jacobiComodulusk k)) ∧
      compEllIntKk (1 / jacobiComodulusk k) = jacobiComodulusk k *
        (compEllIntKk (jacobiComodulusk k) + s * I * compEllIntKk k) ∧
      compEllIntEk (1 / k) = (1 / k) * (compEllIntEk k + s * I * compEllIntEk (jacobiComodulusk k) -
        (1 - k ^ 2) * compEllIntKk k - s * I * k ^ 2 * compEllIntKk (jacobiComodulusk k)) ∧
      compEllIntEk (1 / jacobiComodulusk k) = (1 / jacobiComodulusk k) *
        (compEllIntEk (jacobiComodulusk k) - s * I * compEllIntEk k -
          k ^ 2 * compEllIntKk (jacobiComodulusk k) + s * I * (1 - k ^ 2) * compEllIntKk k) := by
  sorry

/-! ### §19.7(ii) Change of modulus and amplitude -/

/-- **Admitted.** DLMF 19.7.4 (reciprocal-modulus transformation): for real `0 < k < 1`,
`k₁ = 1/k`, real `0 ≤ φ ≤ π/2` with `sin β = k₁ sin φ ≤ 1` (`β = arcsin(k₁ sin φ)`), and real
`α²` with `α² sin²φ < 1`,
`F(φ, k₁) = kF(β, k)`, `E(φ, k₁) = (E(β, k) - k'²F(β, k))/k`, `Π(φ, α², k₁) = kΠ(β, k²α², k)`. -/
@[dlmf 19.7.E4]
theorem incEllInt_reciprocal_modulus {k φ α2 : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ π / 2) (hφk : Real.sin φ ≤ k) (hα : α2 * Real.sin φ ^ 2 < 1) :
    let β := Real.arcsin (Real.sin φ / k)
    incEllIntFk φ (1 / k : ℝ) = k * incEllIntFk β k ∧
      incEllIntEk φ (1 / k : ℝ) = (incEllIntEk β k - (1 - k ^ 2 : ℝ) * incEllIntFk β k) / k ∧
      incEllIntPik φ α2 (1 / k : ℝ) = k * incEllIntPik β (k ^ 2 * α2 : ℝ) k := by
  sorry

/-- **Admitted.** DLMF 19.7.5–19.7.6 (imaginary-modulus transformation): for real `k`, real
`0 ≤ φ ≤ π/2` and real `α² < 1` with `α² + k² ≠ 0`, with `κ = k/√(1+k²)`, `κ' = 1/√(1+k²)`,
`sin θ = √(1+k²) sin φ/√(1 + k² sin²φ)` and `α₁² = (α² + k²)/(1 + k²)`:
`F(φ, ik) = κ'F(θ, κ)`,
`E(φ, ik) = (1/κ')(E(θ, κ) - κ² sin θ cos θ (1 - κ² sin²θ)^{-1/2})`,
`Π(φ, α², ik) = (κ'/α₁²)(κ²F(θ, κ) + κ'²α²Π(θ, α₁², κ))`. -/
@[dlmf 19.7.E5, dlmf 19.7.E6]
theorem incEllInt_imaginary_modulus {k φ α2 : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ π / 2) (hα : α2 < 1)
    (hαk : α2 + k ^ 2 ≠ 0) :
    let κ := k / Real.sqrt (1 + k ^ 2)
    let κ' := 1 / Real.sqrt (1 + k ^ 2)
    let θ := Real.arcsin (Real.sqrt (1 + k ^ 2) * Real.sin φ /
      Real.sqrt (1 + k ^ 2 * Real.sin φ ^ 2))
    let α12 := (α2 + k ^ 2) / (1 + k ^ 2)
    incEllIntFk φ (I * k) = κ' * incEllIntFk θ κ ∧
      incEllIntEk φ (I * k) = (1 / κ' : ℝ) * (incEllIntEk θ κ -
        (κ ^ 2 * Real.sin θ * Real.cos θ / Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2) : ℝ)) ∧
      incEllIntPik φ α2 (I * k) = (κ' / α12 : ℝ) *
        ((κ ^ 2 : ℝ) * incEllIntFk θ κ + (κ' ^ 2 * α2 : ℝ) * incEllIntPik θ α12 κ) := by
  sorry

/-- **Admitted.** DLMF 19.7.7 (imaginary-argument transformation): for real `φ`, `tan ψ = sinh φ`
(`ψ = arctan(sinh φ)`), `k² ∉ (-∞, 0]` and `α² ∉ (-∞, 0]`, `α² ≠ 1`:
`F(iφ, k) = iF(ψ, k')`,
`E(iφ, k) = i(F(ψ, k') - E(ψ, k') + tan ψ √(1 - k'² sin²ψ))`,
`Π(iφ, α², k) = i(F(ψ, k') - α²Π(ψ, 1 - α², k'))/(1 - α²)`. -/
@[dlmf 19.7.E7]
theorem incEllInt_imaginary_argument (φ : ℝ) {k α2 : ℂ} (hk : k ^ 2 ∈ slitPlane)
    (hα : α2 ∈ slitPlane) (hα1 : α2 ≠ 1) :
    let ψ := Real.arctan (Real.sinh φ)
    incEllIntFk (I * φ) k = I * incEllIntFk ψ (jacobiComodulusk k) ∧
      incEllIntEk (I * φ) k = I * (incEllIntFk ψ (jacobiComodulusk k) -
        incEllIntEk ψ (jacobiComodulusk k) +
          Real.tan ψ * (1 - (1 - k ^ 2) * (Real.sin ψ : ℂ) ^ 2) ^ (1 / 2 : ℂ)) ∧
      incEllIntPik (I * φ) α2 k = I * (incEllIntFk ψ (jacobiComodulusk k) -
        α2 * incEllIntPik ψ (1 - α2) (jacobiComodulusk k)) / (1 - α2) := by
  sorry

/-! ### §19.7(iii) Change of parameter of `Π(φ, α², k)` -/

/-- **Admitted.** DLMF 19.7.8: for real `0 < φ < π/2`, `c = csc²φ`, real `0 < k < 1` and real
`α², ω²` with `α²ω² = k²`, `α² ≠ c`, `ω² ≠ c` (Cauchy principal values when `α²` or `ω²`
exceeds `c`):
`Π(φ, α², k) + Π(φ, ω², k) = F(φ, k) + √c R_C((c-1)(c-k²), (c-α²)(c-ω²))`. -/
@[dlmf 19.7.E8]
theorem incEllIntPik_add_first {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : α2 * ω2 = k ^ 2) (hα : α2 ≠ 1 / Real.sin φ ^ 2)
    (hω : ω2 ≠ 1 / Real.sin φ ^ 2) :
    let c := 1 / Real.sin φ ^ 2
    incEllIntPik φ α2 k + incEllIntPik φ ω2 k = incEllIntFk φ k +
      Real.sqrt c * symEllIntRC ((c - 1) * (c - k ^ 2) : ℝ) ((c - α2) * (c - ω2) : ℝ) := by
  sorry

/-- **Admitted.** DLMF 19.7.9: for real `0 < φ < π/2`, `c = csc²φ`, real `0 < k < 1` and real
`α², ω²` with `(1 - α²)(1 - ω²) = 1 - k²`, `α² ≠ c`, `ω² ≠ c`:
`(k² - α²)Π(φ, α², k) + (k² - ω²)Π(φ, ω², k)
= k²F(φ, k) - α²ω² √(c - 1) R_C(c(c - k²), (c - α²)(c - ω²))`. -/
@[dlmf 19.7.E9]
theorem incEllIntPik_add_second {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : (1 - α2) * (1 - ω2) = 1 - k ^ 2) (hα : α2 ≠ 1 / Real.sin φ ^ 2)
    (hω : ω2 ≠ 1 / Real.sin φ ^ 2) :
    let c := 1 / Real.sin φ ^ 2
    ((k ^ 2 - α2 : ℝ) : ℂ) * incEllIntPik φ α2 k + ((k ^ 2 - ω2 : ℝ) : ℂ) * incEllIntPik φ ω2 k =
      (k ^ 2 : ℝ) * incEllIntFk φ k - (α2 * ω2 * Real.sqrt (c - 1) : ℝ) *
        symEllIntRC (c * (c - k ^ 2) : ℝ) ((c - α2) * (c - ω2) : ℝ) := by
  sorry

/-- **Admitted.** DLMF 19.7.10: for real `0 < φ < π/2`, `c = csc²φ`, real `0 < k < 1` and real
`α², ω²` with `(k² - α²)(k² - ω²) = k²(k² - 1)`, `α² ≠ c`, `ω² ≠ c`:
`(1 - α²)Π(φ, α², k) + (1 - ω²)Π(φ, ω², k)
= F(φ, k) + (1 - α² - ω²) √(c - k²) R_C(c(c - 1), (c - α²)(c - ω²))`. -/
@[dlmf 19.7.E10]
theorem incEllIntPik_add_third {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : (k ^ 2 - α2) * (k ^ 2 - ω2) = k ^ 2 * (k ^ 2 - 1))
    (hα : α2 ≠ 1 / Real.sin φ ^ 2) (hω : ω2 ≠ 1 / Real.sin φ ^ 2) :
    let c := 1 / Real.sin φ ^ 2
    ((1 - α2 : ℝ) : ℂ) * incEllIntPik φ α2 k + ((1 - ω2 : ℝ) : ℂ) * incEllIntPik φ ω2 k =
      incEllIntFk φ k + ((1 - α2 - ω2) * Real.sqrt (c - k ^ 2) : ℝ) *
        symEllIntRC (c * (c - 1) : ℝ) ((c - α2) * (c - ω2) : ℝ) := by
  sorry

/-- DLMF §19.7(iii) (prose): under the relation `α²ω² = k²` of 19.7.8, since `k² ≤ c`, `α² > c`
implies `ω² < 1 ≤ c` (for real `0 < k < 1` and `0 < φ < π/2`). -/
@[dlmf 19.7.iii]
theorem first_relation_omega_lt {φ k α2 ω2 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (hk0 : 0 < k)
    (hk1 : k < 1) (hαω : α2 * ω2 = k ^ 2) (hα : 1 / Real.sin φ ^ 2 < α2) :
    ω2 < 1 ∧ 1 ≤ 1 / Real.sin φ ^ 2 := by
  have hs0 : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hs1 : Real.sin φ ^ 2 ≤ 1 := Real.sin_sq_le_one φ
  have hc : 1 ≤ 1 / Real.sin φ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  refine ⟨?_, hc⟩
  have hα0 : 1 < α2 := lt_of_le_of_lt hc hα
  by_contra h
  push Not at h
  nlinarith

end DLMF.EllipticIntegrals
