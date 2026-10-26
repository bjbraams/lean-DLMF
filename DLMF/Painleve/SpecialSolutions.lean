/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.RationalDLMF
public import DLMF.Painleve.Airy
public import DLMF.Bessel.Basic
public import DLMF.Confluent.ParabolicCylinder
public import DLMF.Confluent.Whittaker
public import DLMF.ErrorFunctions.Basic
public import DLMF.OrthogonalPolynomials.Differential
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# Special function solutions of the Painlevé equations (DLMF §32.10)

DLMF normalization (`DLMF.Painleve.Defs`). For each of `PII`–`PVI`, the Riccati equation of
§32.10 (the case `n = 0` of the parameter conditions 32.10.11, 32.10.15, 32.10.23, 32.10.28)
is proved to imply the Painlevé equation. The Airy solutions 32.10.4–32.10.6 of `PII` are
proved, bridging to the Beals–Wong construction of `DLMF.Painleve.Airy` (`airyPII`, with the
cube-root scale `k = -2^{-1/3}`, `k³ = -1/2`); existence for every `α = n + 1/2` (32.10.2) is
the Airy hierarchy `airyPIIHierarchy`. The `α = 5/2` member 32.10.7 and the Wronskian formula
32.10.8–32.10.9 are admitted. The Hermite solutions 32.10.20–32.10.21 and the error-function
solutions 32.10.16, 32.10.22 of `PIV` are proved. The Bessel, parabolic cylinder, Whittaker and
hypergeometric solutions of the Riccati equations (32.10.13–32.10.14, 32.10.18–32.10.19,
32.10.26–32.10.27, 32.10.30–32.10.31) and Picard's solution 32.10.32–32.10.34 are admitted
(the special-function solutions were verified numerically with mpmath, residuals about
`10⁻³⁰`).

**Source correction.** DLMF introduces the Riccati equation 32.10.29 of `PVI` with "If `n = 1`";
it is the case `n = 0` of 32.10.28, i.e. `a + b + c + d = 1` (verified symbolically: the
Riccati equation implies `PVI` exactly when `(1 - a - b - c)² = d² = 1 - 2δ`). The statement
`painleveVI_of_riccati` uses `δ = (1 - (1 - a - b - c)²)/2`.

The phrase "expressible in terms of special functions" (32.10.1 and the "iff" of 32.10.2,
32.10.11, 32.10.15–32.10.16, 32.10.23–32.10.24, 32.10.28) is not formalized; the existence
directions are covered for the Riccati cases.
-/

@[expose] public noncomputable section

open Set Filter Complex Polynomial
open scoped Topology
open DLMF.Airy DLMF.Confluent DLMF.OrthogonalPolynomials

namespace DLMF.Painleve

/-- The logarithmic derivative `φ₁/φ` of a solution of `φ'' = Pφ' + Qφ` satisfies the
Riccati equation `(φ₁/φ)' = P (φ₁/φ) + Q - (φ₁/φ)²`. -/
private lemma b32_hasDerivAt_logDeriv {φ φ1 P Q : ℂ → ℂ} {z : ℂ} (hφ : HasDerivAt φ (φ1 z) z)
    (hφ1 : HasDerivAt φ1 (P z * φ1 z + Q z * φ z) z) (h0 : φ z ≠ 0) :
    HasDerivAt (fun z => φ1 z / φ z) (P z * (φ1 z / φ z) + Q z - (φ1 z / φ z) ^ 2) z :=
  (hφ1.div hφ h0).congr_deriv (by field_simp)

private lemma b32_sq_eq_one {ε : ℂ} (hε : ε = 1 ∨ ε = -1) : ε ^ 2 = 1 := by
  rcases hε with h | h <;> simp [h]

/-! ## `PII` (§32.10(ii)) -/

/-- DLMF 32.10.3: if `εw' = w² + z/2` (`ε = ±1`; equivalently `w' = ε(w² + z/2)`) on an open
set, then `w` solves `PII` with `α = ε/2`. -/
@[dlmf 32.10.E3]
theorem painleveII_of_riccati {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {w : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hw : ∀ z ∈ U, HasDerivAt w (ε * (w z ^ 2 + z / 2)) z) :
    IsPainleveIIOn (ε / 2) w U := by
  have hε2 := b32_sq_eq_one hε
  refine isODE2SolutionOn_of_hasDerivAt hU hw fun z hz => ?_
  refine ((((hw z hz).pow 2).add ((hasDerivAt_id z).div_const 2)).const_mul ε).congr_deriv ?_
  simp only [painleveIIRhs, Nat.cast_ofNat]
  linear_combination (2 * w z ^ 3 + z * w z) * hε2

/-- The DLMF cube-root scale `k = -2^{-1/3}` of 32.10.5 satisfies `k³ = -1/2`. -/
private lemma b32_airy_scale : (-(2 : ℂ) ^ (-1 / 3 : ℂ)) ^ 3 = -1 / 2 := by
  have h : ((2 : ℂ) ^ (-1 / 3 : ℂ)) ^ 3 = 2 ^ (-1 : ℂ) := by
    rw [← cpow_nat_mul]; norm_num
  rw [neg_pow, h, cpow_neg_one]
  norm_num

/-- DLMF 32.10.4–32.10.5: with `φ(z) = C₁Ai(-2^{-1/3}z) + C₂Bi(-2^{-1/3}z)` and `ε = ±1`,
`w(z; ε/2) = -εφ'(z)/φ(z)` solves `PII` with `α = ε/2` wherever `φ ≠ 0`. -/
@[dlmf 32.10.E4, dlmf 32.10.E5]
theorem painleveII_airy {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (C₁ C₂ : ℂ) :
    IsPainleveIIOn (ε / 2)
      (fun z => -ε * deriv (fun z => C₁ * airyAi (-(2 : ℂ) ^ (-1 / 3 : ℂ) * z) +
          C₂ * airyBi (-(2 : ℂ) ^ (-1 / 3 : ℂ) * z)) z /
        (C₁ * airyAi (-(2 : ℂ) ^ (-1 / 3 : ℂ) * z) + C₂ * airyBi (-(2 : ℂ) ^ (-1 / 3 : ℂ) * z)))
      {z | C₁ * airyAi (-(2 : ℂ) ^ (-1 / 3 : ℂ) * z) +
          C₂ * airyBi (-(2 : ℂ) ^ (-1 / 3 : ℂ) * z) ≠ 0} := by
  set k : ℂ := -(2 : ℂ) ^ (-1 / 3 : ℂ)
  have hk : k ^ 3 = -1 / 2 := b32_airy_scale
  have h := isPIIOn_airyPII hk C₁ C₂
  have hS : IsOpen {z | airySeed k C₁ C₂ z ≠ 0} :=
    isOpen_ne_fun (continuous_iff_continuousAt.mpr fun z =>
      (hasDerivAt_airySeed k C₁ C₂ z).continuousAt) continuous_const
  have hd : ∀ z, deriv (fun z => C₁ * airyAi (k * z) + C₂ * airyBi (k * z)) z =
      airySeedDeriv k C₁ C₂ z := fun z => (hasDerivAt_airySeed k C₁ C₂ z).deriv
  rcases hε with rfl | rfl
  · have h0 : IsPainleveIIOn (-1 / 2) (airyPII k C₁ C₂) {z | airySeed k C₁ C₂ z ≠ 0} :=
      b32_isPainleveIIOn_iff.mpr (by convert h using 1; norm_num)
    have h' := b32_isPainleveIIOn_neg h0
    rw [show (1 : ℂ) / 2 = -(-1 / 2) by norm_num]
    refine b32_congr h' hS fun z _ => ?_
    simp only [hd, airyPII, airySeed]
    ring
  · have h0 : IsPainleveIIOn (-1 / 2) (airyPII k C₁ C₂) {z | airySeed k C₁ C₂ z ≠ 0} :=
      b32_isPainleveIIOn_iff.mpr (by convert h using 1; norm_num)
    refine b32_congr h0 hS fun z _ => ?_
    simp only [hd, airyPII, airySeed]
    ring

/-- DLMF 32.10.2 (existence direction): `PII` has Airy-type solutions for every `α = n + 1/2`,
`n ∈ ℤ`: the hierarchy `airyPIIHierarchy` (Beals–Wong Proposition 15.4.6), a finite rational
expression in `z`, `Ai`, `Bi` and their derivatives, obtained from 32.10.4 by the Bäcklund
transformations, solves `PII` on a nonempty open set. The converse ("only if") involves the
notion of a solution expressible in terms of Airy functions and is not formalized. -/
@[dlmf 32.10.E2]
theorem painleveII_exists_airy (n : ℤ) :
    ∃ (w : ℂ → ℂ) (U : Set ℂ), IsOpen U ∧ U.Nonempty ∧ IsPainleveIIOn ((n : ℂ) + 1 / 2) w U := by
  obtain ⟨s, hs, hne, h⟩ := exists_open_isPIIOn_airyPIIHierarchy b32_airy_scale (-n - 1)
  refine ⟨airyPIIHierarchy (-(2 : ℂ) ^ (-1 / 3 : ℂ)) 1 0 (-n - 1), s, hs, hne,
      b32_isPainleveIIOn_iff.mpr ?_⟩
  convert h using 2
  push_cast
  ring

/-- The Riccati equation `Φ' = -Φ² - z/2` of `Φ = φ'/φ` for the Airy combination of 32.10.5. -/
private lemma b32_hasDerivAt_airyPhi (C₁ C₂ : ℂ) {z : ℂ}
    (hz : airySeed (-(2 : ℂ) ^ (-1 / 3 : ℂ)) C₁ C₂ z ≠ 0) :
    HasDerivAt (airyPII (-(2 : ℂ) ^ (-1 / 3 : ℂ)) C₁ C₂)
      (-airyPII (-(2 : ℂ) ^ (-1 / 3 : ℂ)) C₁ C₂ z ^ 2 - z / 2) z :=
  hasDerivAt_airyPII b32_airy_scale C₁ C₂ hz

/-- DLMF 32.10.6 in Riccati form: if `Φ' = -Φ² - z/2` on an open set (as for `Φ = φ'/φ` with
`φ` from 32.10.5), then `w = Φ - 1/(2Φ² + z)` solves `PII` with `α = 3/2` where
`2Φ² + z ≠ 0`. -/
@[dlmf 32.10.E6]
theorem painleveII_three_halves {Φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΦ : ∀ z ∈ U, HasDerivAt Φ (-Φ z ^ 2 - z / 2) z) (hD : ∀ z ∈ U, 2 * Φ z ^ 2 + z ≠ 0) :
    IsPainleveIIOn (3 / 2) (fun z => Φ z - 1 / (2 * Φ z ^ 2 + z)) U := by
  have hDd : ∀ z ∈ U, HasDerivAt (fun z => 2 * Φ z ^ 2 + z)
      (4 * Φ z * (-Φ z ^ 2 - z / 2) + 1) z := fun z hz =>
    ((((hΦ z hz).pow 2).const_mul 2).add (hasDerivAt_id z)).congr_deriv (by
      push_cast; ring)
  refine isODE2SolutionOn_of_hasDerivAt hU
    (v := fun z => (-Φ z ^ 2 - z / 2) + (4 * Φ z * (-Φ z ^ 2 - z / 2) + 1) /
      (2 * Φ z ^ 2 + z) ^ 2) (fun z hz => ?_) (fun z hz => ?_)
  · refine ((hΦ z hz).sub ((hasDerivAt_const z (1 : ℂ)).div (hDd z hz) (hD z hz))).congr_deriv ?_
    have := hD z hz
    field_simp
    ring
  · have hP := hΦ z hz
    have hQ := hDd z hz
    have hd := hD z hz
    have hR : HasDerivAt (fun z => -Φ z ^ 2 - z / 2) (-(2 * Φ z * (-Φ z ^ 2 - z / 2)) - 1 / 2) z :=
      ((hP.pow 2).neg.sub ((hasDerivAt_id z).div_const 2)).congr_deriv (by
        push_cast; ring)
    have hN : HasDerivAt (fun z => 4 * Φ z * (-Φ z ^ 2 - z / 2) + 1)
        (4 * (-Φ z ^ 2 - z / 2) * (-Φ z ^ 2 - z / 2) +
          4 * Φ z * (-(2 * Φ z * (-Φ z ^ 2 - z / 2)) - 1 / 2)) z :=
      (((hP.const_mul 4).mul hR).add_const 1).congr_deriv (by ring)
    refine (hR.add (hN.div (hQ.pow 2) (pow_ne_zero 2 hd))).congr_deriv ?_
    simp only [painleveIIRhs, Pi.pow_apply]
    field_simp
    ring

/-- DLMF 32.10.7 in Riccati form: if `Φ' = -Φ² - z/2` on an open set, then
`w = 1/(2Φ² + z) + (2zΦ² + Φ + z²)/(4Φ³ + 2zΦ - 1)` solves `PII` with `α = 5/2` where both
denominators are nonzero. -/
@[dlmf 32.10.E7]
theorem painleveII_five_halves {Φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΦ : ∀ z ∈ U, HasDerivAt Φ (-Φ z ^ 2 - z / 2) z) (hD : ∀ z ∈ U, 2 * Φ z ^ 2 + z ≠ 0)
    (hE : ∀ z ∈ U, 4 * Φ z ^ 3 + 2 * z * Φ z - 1 ≠ 0) :
    IsPainleveIIOn (5 / 2)
      (fun z => 1 / (2 * Φ z ^ 2 + z) + (2 * z * Φ z ^ 2 + Φ z + z ^ 2) /
        (4 * Φ z ^ 3 + 2 * z * Φ z - 1)) U := by
  sorry

/-- DLMF 32.10.6 for the Airy function: with `Φ = φ'/φ`, `φ` as in 32.10.5,
`w(z; 3/2) = Φ - 1/(2Φ² + z)` solves `PII` with `α = 3/2` where `φ ≠ 0` and `2Φ² + z ≠ 0`. -/
@[dlmf 32.10.E6]
theorem painleveII_airy_three_halves (C₁ C₂ : ℂ) :
    IsPainleveIIOn (3 / 2)
      (fun z => airyPII (-(2 : ℂ) ^ (-1 / 3 : ℂ)) C₁ C₂ z -
        1 / (2 * airyPII (-(2 : ℂ) ^ (-1 / 3 : ℂ)) C₁ C₂ z ^ 2 + z))
      {z | airySeed (-(2 : ℂ) ^ (-1 / 3 : ℂ)) C₁ C₂ z ≠ 0 ∧
        2 * airyPII (-(2 : ℂ) ^ (-1 / 3 : ℂ)) C₁ C₂ z ^ 2 + z ≠ 0} := by
  set k : ℂ := -(2 : ℂ) ^ (-1 / 3 : ℂ)
  have hF : Continuous (airySeed k C₁ C₂) := continuous_iff_continuousAt.mpr fun z =>
    (hasDerivAt_airySeed k C₁ C₂ z).continuousAt
  have hS : IsOpen {z | airySeed k C₁ C₂ z ≠ 0} := isOpen_ne_fun hF continuous_const
  have hc : ContinuousOn (fun z => 2 * airyPII k C₁ C₂ z ^ 2 + z) {z | airySeed k C₁ C₂ z ≠ 0} :=
    fun z hz => ((((b32_hasDerivAt_airyPhi C₁ C₂ hz).pow 2).const_mul 2).add
      (hasDerivAt_id z)).continuousAt.continuousWithinAt
  have hU := hc.isOpen_inter_preimage hS (isOpen_compl_singleton (x := (0 : ℂ)))
  exact painleveII_three_halves hU (fun z hz => b32_hasDerivAt_airyPhi C₁ C₂ hz.1)
    fun z hz => hz.2

/-- DLMF 32.10.8–32.10.9: for `n = 1, 2, …` and `φ` as in 32.10.5, with the Wronskians
`τ_n = 𝒲{φ, φ', …, φ^{(n-1)}}`, `w(z; n + 1/2) = d/dz ln(τ_n(z)/τ_{n+1}(z))` solves `PII`
with `α = n + 1/2` where `τ_nτ_{n+1} ≠ 0` (the logarithmic derivative is written as
`τ_n'/τ_n - τ_{n+1}'/τ_{n+1}`). -/
@[dlmf 32.10.E8]
theorem painleveII_airy_wronskian (C₁ C₂ : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    let φ := fun z => C₁ * airyAi (-(2 : ℂ) ^ (-1 / 3 : ℂ) * z) +
      C₂ * airyBi (-(2 : ℂ) ^ (-1 / 3 : ℂ) * z)
    IsPainleveIIOn ((n : ℂ) + 1 / 2)
      (fun z => deriv (wronskianTau φ n) z / wronskianTau φ n z -
        deriv (wronskianTau φ (n + 1)) z / wronskianTau φ (n + 1) z)
      {z | wronskianTau φ n z ≠ 0 ∧ wronskianTau φ (n + 1) z ≠ 0} := by
  sorry

/-- DLMF 32.10.10: `w(z; -n - 1/2) = -w(z; n + 1/2)`; more generally `w ↦ -w` maps solutions
of `PII` with parameter `α` to solutions with parameter `-α`. -/
@[dlmf 32.10.E10]
theorem painleveII_neg {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (h : IsPainleveIIOn α w U) :
    IsPainleveIIOn (-α) (fun z => -w z) U :=
  b32_isPainleveIIOn_neg h

/-! ## `PIII` (§32.10(iii)) -/

/-- DLMF 32.10.11–32.10.12 (the case `ε₁α + ε₂β = 2` of 32.10.11): with `γ = 1`, `δ = -1`, if
`zw' = ε₁zw² + (αε₁ - 1)w + ε₂z` (`ε₁, ε₂ = ±1`) on an open set avoiding `z = 0` and the zeros
of `w`, then `w` solves `PIII` with parameters `(α, β, 1, -1)`. -/
@[dlmf 32.10.E11, dlmf 32.10.E12]
theorem painleveIII_of_riccati {ε₁ ε₂ α β : ℂ} (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hαβ : ε₁ * α + ε₂ * β = 2) {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (hw0 : ∀ z ∈ U, w z ≠ 0)
    (hw : ∀ z ∈ U, HasDerivAt w ((ε₁ * z * w z ^ 2 + (α * ε₁ - 1) * w z + ε₂ * z) / z) z) :
    IsPainleveIIIOn α β 1 (-1) w U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU hw fun z hz => ?_, h0, hw0⟩
  have hz0 := h0 z hz
  have hw' := hw z hz
  have hw0' := hw0 z hz
  refine ((((((hasDerivAt_id z).const_mul ε₁).mul (hw'.pow 2)).add
    (hw'.const_mul (α * ε₁ - 1))).add ((hasDerivAt_id z).const_mul ε₂)).div (hasDerivAt_id z)
      hz0).congr_deriv ?_
  simp only [painleveIIIRhs, id_eq, Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  all_goals
    first
    | (have hβ : β = 2 - α := by linear_combination hαβ)
    | (have hβ : β = α - 2 := by linear_combination -hαβ)
    | (have hβ : β = -2 - α := by linear_combination -hαβ)
    | (have hβ : β = α + 2 := by linear_combination hαβ)
  all_goals (subst hβ; field_simp; ring)

/-- DLMF 32.10.13–32.10.14: if `α ≠ ε₁`, then `w = -ε₁φ'/φ` with
`φ(z) = z^ν(C₁J_ν(ζ) + C₂Y_ν(ζ))`, `ζ = (ε₁ε₂)^{1/2} z`, `ν = αε₁/2`, solves the Riccati
equation 32.10.12 wherever `φ ≠ 0` (principal branches; `U` in the slit plane and `ζ(U)` in the
slit plane). -/
@[dlmf 32.10.E13, dlmf 32.10.E14]
theorem painleveIII_bessel_riccati {ε₁ ε₂ α C₁ C₂ : ℂ} (h₁ : ε₁ = 1 ∨ ε₁ = -1)
    (h₂ : ε₂ = 1 ∨ ε₂ = -1) (hα : α ≠ ε₁) {U : Set ℂ} (hU : IsOpen U) (hUs : U ⊆ slitPlane)
    (hζ : ∀ z ∈ U, (ε₁ * ε₂) ^ (1 / 2 : ℂ) * z ∈ slitPlane) :
    let φ := fun z : ℂ => z ^ (α * ε₁ / 2) *
      (C₁ * besselJ (α * ε₁ / 2) ((ε₁ * ε₂) ^ (1 / 2 : ℂ) * z) +
        C₂ * DLMF.Bessel.besselY (α * ε₁ / 2) ((ε₁ * ε₂) ^ (1 / 2 : ℂ) * z))
    ∀ z ∈ U, φ z ≠ 0 →
      HasDerivAt (fun z => -ε₁ * deriv φ z / φ z)
        ((ε₁ * z * (-ε₁ * deriv φ z / φ z) ^ 2 + (α * ε₁ - 1) * (-ε₁ * deriv φ z / φ z) +
          ε₂ * z) / z) z := by
  sorry

/-! ## `PIV` (§32.10(iv)) -/

/-- DLMF 32.10.15, 32.10.17 (the case `n = 0` of 32.10.15): if
`w' = ε(w² + 2zw) - 2(1 + εα)` (`ε = ±1`) on an open set avoiding the zeros of `w`, then `w`
solves `PIV` with parameters `(α, -2(1 + εα)²)`. -/
@[dlmf 32.10.E15, dlmf 32.10.E17]
theorem painleveIV_of_riccati {ε α : ℂ} (hε : ε = 1 ∨ ε = -1) {w : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hw0 : ∀ z ∈ U, w z ≠ 0)
    (hw : ∀ z ∈ U, HasDerivAt w (ε * (w z ^ 2 + 2 * z * w z) - 2 * (1 + ε * α)) z) :
    IsPainleveIVOn α (-2 * (1 + ε * α) ^ 2) w U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU hw fun z hz => ?_, hw0⟩
  have hw' := hw z hz
  have hw0' := hw0 z hz
  refine ((((hw'.pow 2).add (((hasDerivAt_id z).const_mul 2).mul hw')).const_mul ε).sub_const
    (2 * (1 + ε * α))).congr_deriv ?_
  simp only [painleveIVRhs, id_eq]
  rcases hε with rfl | rfl <;> (field_simp; ring)

/-- DLMF 32.10.18–32.10.19: with `a = α + ε/2` and
`φ(z) = (C₁U(a, √2 z) + C₂V(a, √2 z)) exp(εz²/2)`, the function `w = -εφ'/φ` solves the
Riccati equation 32.10.17 wherever `φ ≠ 0`. -/
@[dlmf 32.10.E18, dlmf 32.10.E19]
theorem painleveIV_pcf_riccati {ε α C₁ C₂ : ℂ} (hε : ε = 1 ∨ ε = -1) :
    let φ := fun z : ℂ => (C₁ * pcfU (α + ε / 2) (Real.sqrt 2 * z) +
      C₂ * pcfV (α + ε / 2) (Real.sqrt 2 * z)) * exp (ε * z ^ 2 / 2)
    ∀ z, φ z ≠ 0 →
      HasDerivAt (fun z => -ε * deriv φ z / φ z)
        (ε * ((-ε * deriv φ z / φ z) ^ 2 + 2 * z * (-ε * deriv φ z / φ z)) -
          2 * (1 + ε * α)) z := by
  sorry

/-- The Hermite differential equation `H_n'' = 2zH_n' - 2nH_n` over `ℂ`. -/
private lemma b32_hermite_ode (n : ℕ) :
    let H : ℂ[X] := (hermitePolyH n).map (Int.castRingHom ℂ)
    derivative (derivative H) = 2 * X * derivative H - C (2 * n : ℂ) * H := by
  intro H
  have h := congrArg (Polynomial.map (Int.castRingHom ℂ)) (hermitePolyH_differential_equation n)
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_C, Polynomial.map_zero] at h
  rw [← sub_eq_zero, ← h]
  simp [H]
  ring

/-- DLMF 32.10.20: for `m = 1, 2, …`, `w(z; -m, -2(m - 1)²) = -H_{m-1}'(z)/H_{m-1}(z)` solves
`PIV` with `(α, β) = (-m, -2(m - 1)²)` wherever `H_{m-1}(z) ≠ 0` and `H_{m-1}'(z) ≠ 0`
(`PIV` divides by `w`; for `m = 1` the solution `w ≡ 0` is excluded and the set is empty).
`H_n` is the physicists' Hermite polynomial `hermitePolyH n`, mapped to `ℂ[X]`. -/
@[dlmf 32.10.E20]
theorem painleveIV_hermite (m : ℕ) (hm : 1 ≤ m) :
    let H : ℂ[X] := (hermitePolyH (m - 1)).map (Int.castRingHom ℂ)
    IsPainleveIVOn (-(m : ℂ)) (-2 * ((m : ℂ) - 1) ^ 2)
      (fun z => -(derivative H).eval z / H.eval z)
      {z | H.eval z ≠ 0 ∧ (derivative H).eval z ≠ 0} := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  intro H
  have hU : IsOpen {z | H.eval z ≠ 0 ∧ (derivative H).eval z ≠ 0} :=
    (isOpen_ne_fun (Polynomial.continuous _) continuous_const).inter
      (isOpen_ne_fun (Polynomial.continuous _) continuous_const)
  have h := painleveIV_of_riccati (ε := 1) (α := -((k + 1 : ℕ) : ℂ)) (Or.inl rfl) hU
    (w := fun z => -(derivative H).eval z / H.eval z)
    (fun z hz => div_ne_zero (neg_ne_zero.mpr hz.2) hz.1) (fun z hz => ?_)
  · convert h using 1
    push_cast; ring
  · have hode := congrArg (eval z) (b32_hermite_ode k)
    simp only [eval_sub, eval_mul, eval_X, eval_C, eval_ofNat] at hode
    change (derivative (derivative H)).eval z =
      2 * z * (derivative H).eval z - 2 * (k : ℂ) * H.eval z at hode
    have h1 := (derivative H).hasDerivAt z
    have h2 := H.hasDerivAt z
    refine (h1.neg.div h2 hz.1).congr_deriv ?_
    rw [hode]
    have := hz.1
    simp only [Pi.neg_apply]
    field_simp
    push_cast
    ring

/-- DLMF 32.10.21: for `m = 0, 1, 2, …`, `w(z; -m, -2(m + 1)²) = -2z + H_m'(z)/H_m(z)` solves
`PIV` with `(α, β) = (-m, -2(m + 1)²)` wherever `H_m(z) ≠ 0` and `w(z) ≠ 0`. -/
@[dlmf 32.10.E21]
theorem painleveIV_hermite' (m : ℕ) :
    let H : ℂ[X] := (hermitePolyH m).map (Int.castRingHom ℂ)
    IsPainleveIVOn (-(m : ℂ)) (-2 * ((m : ℂ) + 1) ^ 2)
      (fun z => -2 * z + (derivative H).eval z / H.eval z)
      {z | H.eval z ≠ 0 ∧ -2 * z + (derivative H).eval z / H.eval z ≠ 0} := by
  intro H
  have hc : ContinuousOn (fun z => -2 * z + (derivative H).eval z / H.eval z)
      {z | H.eval z ≠ 0} := by
    intro z hz
    exact (((continuous_const.mul continuous_id).continuousAt).add
      ((Polynomial.continuous _).continuousAt.div (Polynomial.continuous _).continuousAt
        hz)).continuousWithinAt
  have hU := hc.isOpen_inter_preimage (isOpen_ne_fun (Polynomial.continuous _) continuous_const)
    (isOpen_compl_singleton (x := (0 : ℂ)))
  have h := painleveIV_of_riccati (ε := -1) (α := -(m : ℂ)) (Or.inr rfl) hU
    (w := fun z => -2 * z + (derivative H).eval z / H.eval z)
    (fun z hz => hz.2) (fun z hz => ?_)
  · convert h using 1 <;> first | rfl | ring
  · have hode := congrArg (eval z) (b32_hermite_ode m)
    simp only [eval_sub, eval_mul, eval_X, eval_C, eval_ofNat] at hode
    change (derivative (derivative H)).eval z =
      2 * z * (derivative H).eval z - 2 * (m : ℂ) * H.eval z at hode
    have h1 := (derivative H).hasDerivAt z
    have h2 := H.hasDerivAt z
    refine (((hasDerivAt_id z).const_mul (-2)).add (h1.div h2 hz.1)).congr_deriv ?_
    rw [hode]
    have : H.eval z ≠ 0 := hz.1
    field_simp
    ring

/-- DLMF 32.10.16, 32.10.22 (the case `1 + εα = 0` of 32.10.17, `β = 0 = -2·0²` in 32.10.16):
for `ε = 1` (`α = -1`), `w = 2e^{z²}/(√π(C - i erfc(iz)))` solves `PIV` with `(α, β) = (-1, 0)`
wherever the denominator does not vanish. -/
@[dlmf 32.10.E16, dlmf 32.10.E22]
theorem painleveIV_erfc_plus (C : ℂ) :
    IsPainleveIVOn (-1) 0
      (fun z => 2 * exp (z ^ 2) / ((Real.sqrt Real.pi : ℂ) * (C - I * erfc (I * z))))
      {z | C - I * erfc (I * z) ≠ 0} := by
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hD : ∀ z : ℂ, HasDerivAt (fun z => C - I * erfc (I * z))
      (-(2 / (Real.sqrt Real.pi : ℂ) * exp (z ^ 2))) z := by
    intro z
    have h := (hasDerivAt_erf_complex (I * z)).comp z ((hasDerivAt_id z).const_mul I)
    have h' := ((h.const_sub 1).const_mul I).const_sub C
    refine h'.congr_deriv ?_
    have he : -(I * z) ^ 2 = z ^ 2 := by rw [mul_pow, I_sq]; ring
    rw [he]
    linear_combination (2 / (Real.sqrt Real.pi : ℂ) * exp (z ^ 2)) * I_sq
  have hc : Continuous (fun z => C - I * erfc (I * z)) :=
    continuous_iff_continuousAt.mpr fun z => (hD z).continuousAt
  have hU : IsOpen {z | C - I * erfc (I * z) ≠ 0} := isOpen_ne_fun hc continuous_const
  have h := painleveIV_of_riccati (ε := 1) (α := -1) (Or.inl rfl) hU
    (w := fun z => 2 * exp (z ^ 2) / ((Real.sqrt Real.pi : ℂ) * (C - I * erfc (I * z))))
    (fun z hz => div_ne_zero (mul_ne_zero two_ne_zero (exp_ne_zero _)) (mul_ne_zero hπ hz))
    (fun z hz => ?_)
  · convert h using 1
    norm_num
  · have hz' : C - I * erfc (I * z) ≠ 0 := hz
    have hE := (hasDerivAt_pow 2 z).cexp
    refine ((hE.const_mul 2).div ((hD z).const_mul (Real.sqrt Real.pi : ℂ))
      (mul_ne_zero hπ hz')).congr_deriv ?_
    field_simp
    push_cast
    ring

/-- DLMF 32.10.22 for `ε = -1` (`α = 1`): `w = 2e^{-z²}/(√π(C - erfc z))` solves `PIV` with
`(α, β) = (1, 0)` wherever the denominator does not vanish. -/
@[dlmf 32.10.E22]
theorem painleveIV_erfc_minus (C : ℂ) :
    IsPainleveIVOn 1 0 (fun z => 2 * exp (-z ^ 2) / ((Real.sqrt Real.pi : ℂ) * (C - erfc z)))
      {z | C - erfc z ≠ 0} := by
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hD : ∀ z : ℂ, HasDerivAt (fun z => C - erfc z)
      (2 / (Real.sqrt Real.pi : ℂ) * exp (-z ^ 2)) z := fun z =>
    (((hasDerivAt_erf_complex z).const_sub 1).const_sub C).congr_deriv (by ring)
  have hc : Continuous (fun z => C - erfc z) :=
    continuous_iff_continuousAt.mpr fun z => (hD z).continuousAt
  have hU : IsOpen {z | C - erfc z ≠ 0} := isOpen_ne_fun hc continuous_const
  have h := painleveIV_of_riccati (ε := -1) (α := 1) (Or.inr rfl) hU
    (w := fun z => 2 * exp (-z ^ 2) / ((Real.sqrt Real.pi : ℂ) * (C - erfc z)))
    (fun z hz => div_ne_zero (mul_ne_zero two_ne_zero (exp_ne_zero _)) (mul_ne_zero hπ hz))
    (fun z hz => ?_)
  · convert h using 1
    norm_num
  · have hz' : C - erfc z ≠ 0 := hz
    have hE := (hasDerivAt_pow 2 z).neg.cexp
    refine ((hE.const_mul 2).div ((hD z).const_mul (Real.sqrt Real.pi : ℂ))
      (mul_ne_zero hπ hz')).congr_deriv ?_
    simp only [Pi.neg_apply]
    field_simp
    push_cast
    ring

/-! ## `PV` (§32.10(v)) -/

/-- DLMF 32.10.23, 32.10.25 (the case `n = 0` of 32.10.23): with `δ = -1/2`, if
`zw' = aw² + (b - a + ε₃z)w - b` (`ε₃ = ±1`) on an open set avoiding `z = 0` and the points
where `w ∈ {0, 1}`, then `w` solves `PV` with `α = a²/2`, `β = -b²/2` and `γ` given by
`a + b + ε₃γ = 1`. -/
@[dlmf 32.10.E23, dlmf 32.10.E25]
theorem painleveV_of_riccati {a b ε₃ : ℂ} (hε : ε₃ = 1 ∨ ε₃ = -1) {w : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (h0 : ∀ z ∈ U, z ≠ 0) (hw0 : ∀ z ∈ U, w z ≠ 0) (hw1 : ∀ z ∈ U, w z ≠ 1)
    (hw : ∀ z ∈ U, HasDerivAt w ((a * w z ^ 2 + (b - a + ε₃ * z) * w z - b) / z) z) :
    IsPainleveVOn (a ^ 2 / 2) (-b ^ 2 / 2) (ε₃ * (1 - a - b)) (-1 / 2) w U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU hw fun z hz => ?_, h0, hw0, hw1⟩
  have hz0 := h0 z hz
  have hw' := hw z hz
  have hw0' := hw0 z hz
  have hw1' := sub_ne_zero.mpr (hw1 z hz)
  refine (((((hw'.pow 2).const_mul a).add ((((hasDerivAt_id z).const_mul ε₃).const_add
    (b - a)).mul hw')).sub_const b).div (hasDerivAt_id z) hz0).congr_deriv ?_
  simp only [painleveVRhs, id_eq, Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
  rcases hε with rfl | rfl <;> (field_simp; ring)

/-- DLMF 32.10.26–32.10.27: if `a ≠ 0`, then `w = -zφ'/(aφ)` with
`φ(z) = ζ^{-(a-b+1)/2}(C₁M_{κ,μ}(ζ) + C₂W_{κ,μ}(ζ)) e^{ζ/2}`, `ζ = ε₃z`, `κ = (a - b + 1)/2`,
`μ = (a + b)/2`, solves the Riccati equation 32.10.25 wherever `φ ≠ 0` (principal branches, `ζ`
in the slit plane, `1 + 2μ ∉ -ℕ`). -/
@[dlmf 32.10.E26, dlmf 32.10.E27]
theorem painleveV_whittaker_riccati {a b ε₃ C₁ C₂ : ℂ} (hε : ε₃ = 1 ∨ ε₃ = -1) (ha : a ≠ 0)
    (hμ : ∀ k : ℕ, 1 + (a + b) ≠ -k) :
    let φ := fun z : ℂ => (C₁ * whittakerM ((a - b + 1) / 2) ((a + b) / 2) (ε₃ * z) +
        C₂ * whittakerW ((a - b + 1) / 2) ((a + b) / 2) (ε₃ * z)) /
      (ε₃ * z) ^ ((a - b + 1) / 2) * exp (ε₃ * z / 2)
    ∀ z, ε₃ * z ∈ slitPlane → φ z ≠ 0 →
      HasDerivAt (fun z => -z * deriv φ z / (a * φ z))
        ((a * (-z * deriv φ z / (a * φ z)) ^ 2 +
          (b - a + ε₃ * z) * (-z * deriv φ z / (a * φ z)) - b) / z) z := by
  sorry

/-! ## `PVI` (§32.10(vi)) -/

/-- DLMF 32.10.28–32.10.29 (the case `a + b + c + d = 1` of 32.10.28; DLMF writes "if `n = 1`",
which should read `n = 0`): if
`w' = aw²/(z(z-1)) + ((b + c)z - a - c)w/(z(z-1)) - b/(z-1)` on an open set avoiding
`z ∈ {0, 1}` and the points where `w ∈ {0, 1, z}`, then `w` solves `PVI` with `α = a²/2`,
`β = -b²/2`, `γ = c²/2` and `δ = (1 - d²)/2`, `d = 1 - a - b - c`. -/
@[dlmf 32.10.E28, dlmf 32.10.E29]
theorem painleveVI_of_riccati {a b c : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1) (hw0 : ∀ z ∈ U, w z ≠ 0)
    (hw1 : ∀ z ∈ U, w z ≠ 1) (hwz : ∀ z ∈ U, w z ≠ z)
    (hw : ∀ z ∈ U, HasDerivAt w (a * w z ^ 2 / (z * (z - 1)) +
      ((b + c) * z - a - c) / (z * (z - 1)) * w z - b / (z - 1)) z) :
    IsPainleveVIOn (a ^ 2 / 2) (-b ^ 2 / 2) (c ^ 2 / 2) ((1 - (1 - a - b - c) ^ 2) / 2) w U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU hw fun z hz => ?_, h0, h1, hw0, hw1, hwz⟩
  have hz0 := h0 z hz
  have hz1 := sub_ne_zero.mpr (h1 z hz)
  have hw' := hw z hz
  have hw0' := hw0 z hz
  have hw1' := sub_ne_zero.mpr (hw1 z hz)
  have hwz' := sub_ne_zero.mpr (hwz z hz)
  have hzz : z * (z - 1) ≠ 0 := mul_ne_zero hz0 hz1
  have hq : HasDerivAt (fun z : ℂ => z * (z - 1)) (2 * z - 1) z :=
    ((hasDerivAt_id z).mul ((hasDerivAt_id z).sub_const 1)).congr_deriv (by simp; ring)
  have hA := ((hw'.pow 2).const_mul a).div hq hzz
  have hB := (((((hasDerivAt_id z).const_mul (b + c)).sub_const a).sub_const c).div hq
    hzz).mul hw'
  have hC := (hasDerivAt_const z b).div ((hasDerivAt_id z).sub_const 1) hz1
  refine ((hA.add hB).sub hC).congr_deriv ?_
  simp only [painleveVIRhs, id_eq, Pi.pow_apply, Pi.div_apply,
    ]
  field_simp
  ring

/-- DLMF 32.10.30–32.10.31: if `a ≠ 0`, then `w(z) = (ζ - 1)φ'(ζ)/(aφ(ζ))`, `ζ = 1/(1 - z)`,
with `φ(ζ) = C₁F(b, -a; b + c; ζ) + C₂ζ^{1-b-c}F(1 - a - b - c, 1 - c; 2 - b - c; ζ)`, solves the
Riccati equation 32.10.29 wherever `φ(ζ) ≠ 0`. Here `F` is Gauss's series
`ordinaryHypergeometric`, so the statement is made for `|ζ| < 1` (with `ζ` in the slit plane
for the principal power and `b + c`, `2 - b - c` not nonpositive integers). -/
@[dlmf 32.10.E30, dlmf 32.10.E31]
theorem painleveVI_hypergeometric_riccati {a b c C₁ C₂ : ℂ} (ha : a ≠ 0)
    (hbc : ∀ k : ℕ, b + c ≠ -k) (hbc' : ∀ k : ℕ, 2 - b - c ≠ -k) :
    let φ := fun ζ : ℂ => C₁ * ordinaryHypergeometric b (-a) (b + c) ζ +
      C₂ * ζ ^ (1 - b - c) * ordinaryHypergeometric (1 - a - b - c) (1 - c) (2 - b - c) ζ
    let w := fun z : ℂ => (1 / (1 - z) - 1) * deriv φ (1 / (1 - z)) / (a * φ (1 / (1 - z)))
    ∀ z, z ≠ 1 → ‖1 / (1 - z)‖ < 1 → 1 / (1 - z) ∈ slitPlane → φ (1 / (1 - z)) ≠ 0 →
      HasDerivAt w (a * w z ^ 2 / (z * (z - 1)) + ((b + c) * z - a - c) / (z * (z - 1)) * w z -
        b / (z - 1)) z := by
  sorry

/-- DLMF 32.10.32–32.10.34 (Picard's solution): let `Λ(u, z)` be the elliptic function defined
by `u = ∫_0^Λ dt/√(t(t-1)(t-z))`, i.e. `(∂Λ/∂u)² = Λ(Λ-1)(Λ-z)`, `Λ(0, z) = 0`, with periods
`2φ₁(z)`, `2φ₂(z)` that are linearly independent solutions of the hypergeometric equation
`z(1-z)φ'' + (1-2z)φ' - φ/4 = 0` (32.10.33). Then `w(z) = Λ(C₁φ₁(z) + C₂φ₂(z), z)` solves `PVI`
with `(α, β, γ, δ) = (0, 0, 0, 1/2)` on every open set where it is defined and avoids
`w ∈ {0, 1, z}`, `z ∈ {0, 1}`. (DLMF adds that this solution is essentially transcendental in
both constants: no algebraic first integral exists; that statement is not formalized.) -/
@[dlmf 32.10.E32, dlmf 32.10.E33, dlmf 32.10.E34]
theorem painleveVI_picard {Λ : ℂ → ℂ → ℂ} {φ₁ φ₂ : ℂ → ℂ} {C₁ C₂ : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hΛ : ∀ z ∈ U, ∀ u, DifferentiableAt ℂ (Function.uncurry Λ) (u, z))
    (hΛu : ∀ z ∈ U, ∀ u, deriv (fun u => Λ u z) u ^ 2 = Λ u z * (Λ u z - 1) * (Λ u z - z))
    (hΛ0 : ∀ z ∈ U, Λ 0 z = 0)
    (hper : ∀ z ∈ U, ∀ u, Λ (u + 2 * φ₁ z) z = Λ u z ∧ Λ (u + 2 * φ₂ z) z = Λ u z)
    (hφ : ∀ z ∈ U, ∀ φ ∈ ({φ₁, φ₂} : Set (ℂ → ℂ)), ContDiffAt ℂ 2 φ z ∧
      z * (1 - z) * iteratedDeriv 2 φ z + (1 - 2 * z) * deriv φ z - φ z / 4 = 0)
    (hind : ∀ z ∈ U, φ₁ z * deriv φ₂ z - φ₂ z * deriv φ₁ z ≠ 0)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1)
    (hw : ∀ z ∈ U, Λ (C₁ * φ₁ z + C₂ * φ₂ z) z ∉ ({0, 1, z} : Set ℂ)) :
    IsPainleveVIOn 0 0 0 (1 / 2) (fun z => Λ (C₁ * φ₁ z + C₂ * φ₂ z) z) U := by
  sorry

end DLMF.Painleve
