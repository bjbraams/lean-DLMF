/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Basic solutions of Heun's equation (DLMF §31.3)

`heunLocal a q α β γ δ z = ∑ c_j z^j` is DLMF's `Hl(a, q; α, β, γ, δ; z)` (31.3.1), with the
coefficients `c_j` of the three-term recurrence 31.3.2–31.3.4 (`heunLocalCoeff`). This file
states

* the recurrence (31.3.2, 31.3.3, proved from the definition), `Hl(0) = 1` (proved), the
  convergence of the series in `|z| < min(1, |a|)` and the characterization of `Hl` as the
  solution with exponent `0` and value `1` at the origin (§31.3(i), admitted);
* the second solution at `0` (31.3.5) and the Fuchs–Frobenius solutions at `1`, `a`, `∞`
  (31.3.6–31.3.11), each as a solution of Heun's equation on the disk of convergence of the `Hl`
  involved (admitted);
* the equivalent expressions 31.3.12 (proved, for all `z`: the two series agree term by term)
  and 31.3.13 (admitted).

Domains: the principal powers `z^{1-γ}`, `(1-z)^{1-δ}`, `((a-z)/(a-1))^{1-ε}`, `z^{-α}` are used
where their bases lie in `slitPlane`. Exceptional parameters: DLMF requires
`γ ∉ {0, -1, -2, …}` for 31.3.1 and `γ ∉ {1, 2, 3, …}` for 31.3.5; at the other singularities
the corresponding restrictions on `δ`, `ε` and `α - β` are imposed. For `γ ∈ ℤ` DLMF only remarks
(§31.3(i), last paragraph) that a second solution can be constructed as in §2.7(i), in general
with a logarithmic singularity; that remark is not acquired. The remarks of §31.3(iii) on the
192 = 8 · 24 equivalent local solutions are informal (not acquired beyond 31.3.12–31.3.13).

Every formula was checked numerically (mpmath, coefficients from the recurrence, ODE residuals
below `10⁻²⁹` at sample points for complex parameters).
-/

@[expose] public section

open Complex Filter Set
open scoped Topology Real

noncomputable section

namespace DLMF.Heun

variable {a q α β γ δ ε : ℂ}

/-! ### The recurrence -/

@[simp] theorem heunLocalCoeff_zero : heunLocalCoeff a q α β γ δ 0 = 1 := rfl

@[simp] theorem heunLocalCoeff_one : heunLocalCoeff a q α β γ δ 1 = q / (a * γ) := rfl

/-- DLMF 31.3.2: `aγc₁ - qc₀ = 0` (for `aγ ≠ 0`). -/
@[dlmf 31.3.E2]
theorem heunLocalCoeff_rec_zero (ha : a ≠ 0) (hγ : γ ≠ 0) :
    a * γ * heunLocalCoeff a q α β γ δ 1 - q * heunLocalCoeff a q α β γ δ 0 = 0 := by
  simp only [heunLocalCoeff_one, heunLocalCoeff_zero]
  field_simp
  ring

/-- DLMF 31.3.3: `R_j c_{j+1} - (Q_j + q) c_j + P_j c_{j-1} = 0` for `j ≥ 1` (for `R_j ≠ 0`, that
is `a ≠ 0` and `γ ≠ -j`). -/
@[dlmf 31.3.E3]
theorem heunLocalCoeff_rec {j : ℕ} (hj : 1 ≤ j) (hR : heunRecR a γ j ≠ 0) :
    heunRecR a γ j * heunLocalCoeff a q α β γ δ (j + 1) -
      (heunRecQ a α β γ δ j + q) * heunLocalCoeff a q α β γ δ j +
      heunRecP α β j * heunLocalCoeff a q α β γ δ (j - 1) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show k + 1 + 1 = k + 2 from rfl, heunLocalCoeff, mul_div_cancel₀ _ hR]
  ring

/-- `Hl(a, q; α, β, γ, δ; 0) = 1` (DLMF §31.3(i): the solution "assumes the value 1" at `0`). -/
@[dlmf 31.3.i]
theorem heunLocal_zero : heunLocal a q α β γ δ 0 = 1 := by
  rw [heunLocal, tsum_eq_single 0]
  · simp
  · intro j hj
    simp [zero_pow hj]

/-- DLMF 31.3.1: for `a ≠ 0` and `γ ∉ {0, -1, -2, …}` the Maclaurin series `∑ c_j z^j`
converges to `Hl(a, q; α, β, γ, δ; z)` for `|z| < min(1, |a|)` (the radius given by the nearest
singularity; the ratio `c_{j+1}/c_j` tends to `1` or `1/a`). -/
@[dlmf 31.3.E1]
theorem hasSum_heunLocal (ha : a ≠ 0) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) {z : ℂ}
    (hz : ‖z‖ < heunLocalRadius a) :
    HasSum (fun j => heunLocalCoeff a q α β γ δ j * z ^ j) (heunLocal a q α β γ δ z) := by
  sorry

/-- DLMF §31.3(i): `Hl` is analytic in the disk `|z| < min(1, |a|)` and solves Heun's equation
(with `ε = α + β + 1 - γ - δ`) there, away from the regular singular point `z = 0`. -/
@[dlmf 31.3.i, dlmf 31.3.E1]
theorem heunLocal_isHeunSolOn (ha : a ≠ 0) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) :
    AnalyticOnNhd ℂ (heunLocal a q α β γ δ) (Metric.ball 0 (heunLocalRadius a)) ∧
    IsHeunSolOn a q α β γ δ (heunEps α β γ δ) (heunLocal a q α β γ δ)
      (Metric.ball 0 (heunLocalRadius a) \ {0}) := by
  sorry

/-- DLMF §31.3(i), characterization of `Hl`: for `γ ∉ {0, -1, -2, …}`, every solution of Heun's
equation near `0` (punctured) that is analytic at `0` is `w(0) · Hl(z)` near `0`. -/
@[dlmf 31.3.i]
theorem eventuallyEq_heunLocal_of_analyticAt (ha : a ≠ 0) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    {w : ℂ → ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 (0 : ℂ)) (hw : AnalyticAt ℂ w 0)
    (hsol : IsHeunSolOn a q α β γ δ (heunEps α β γ δ) w (U \ {0})) :
    w =ᶠ[𝓝 0] fun z => w 0 * heunLocal a q α β γ δ z := by
  sorry

/-! ### The other local solutions (31.3.5–31.3.11) -/

/-- DLMF 31.3.5: for `γ ∉ {1, 2, 3, …}` the solution with exponent `1 - γ` at `z = 0` is
`z^{1-γ} Hl(a, (aδ + ε)(1 - γ) + q; α + 1 - γ, β + 1 - γ, 2 - γ, δ; z)`. -/
@[dlmf 31.3.E5]
theorem heunLocal_second_isHeunSolOn (ha : a ≠ 0) (hγ : ∀ n : ℕ, γ ≠ (n : ℂ) + 1)
    (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => z ^ (1 - γ) * heunLocal a ((a * δ + ε) * (1 - γ) + q) (α + 1 - γ) (β + 1 - γ)
        (2 - γ) δ z)
      {z | ‖z‖ < heunLocalRadius a ∧ z ∈ slitPlane} := by
  sorry

/-- DLMF 31.3.6: for `δ ∉ {0, -1, -2, …}` the solution with exponent `0` at `z = 1` is
`Hl(1 - a, αβ - q; α, β, δ, γ; 1 - z)`. -/
@[dlmf 31.3.E6]
theorem heunLocal_at_one_isHeunSolOn (ha : a ≠ 1) (hδ : ∀ n : ℕ, δ ≠ -(n : ℂ))
    (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε (fun z => heunLocal (1 - a) (α * β - q) α β δ γ (1 - z))
      ({z | ‖1 - z‖ < heunLocalRadius (1 - a)} \ {1}) := by
  sorry

/-- DLMF 31.3.7: for `δ ∉ {1, 2, 3, …}` the solution with exponent `1 - δ` at `z = 1` is
`(1-z)^{1-δ} Hl(1 - a, ((1-a)γ + ε)(1 - δ) + αβ - q; α + 1 - δ, β + 1 - δ, 2 - δ, γ; 1 - z)`. -/
@[dlmf 31.3.E7]
theorem heunLocal_second_at_one_isHeunSolOn (ha : a ≠ 1) (hδ : ∀ n : ℕ, δ ≠ (n : ℂ) + 1)
    (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => (1 - z) ^ (1 - δ) * heunLocal (1 - a) (((1 - a) * γ + ε) * (1 - δ) + α * β - q)
        (α + 1 - δ) (β + 1 - δ) (2 - δ) γ (1 - z))
      {z | ‖1 - z‖ < heunLocalRadius (1 - a) ∧ 1 - z ∈ slitPlane} := by
  sorry

/-- DLMF 31.3.8: for `ε ∉ {0, -1, -2, …}` the solution with exponent `0` at `z = a` is
`Hl(a/(a-1), (αβa - q)/(a-1); α, β, ε, δ; (a-z)/(a-1))`. -/
@[dlmf 31.3.E8]
theorem heunLocal_at_a_isHeunSolOn (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hε' : ∀ n : ℕ, ε ≠ -(n : ℂ))
    (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => heunLocal (a / (a - 1)) ((α * β * a - q) / (a - 1)) α β ε δ ((a - z) / (a - 1)))
      ({z | ‖(a - z) / (a - 1)‖ < heunLocalRadius (a / (a - 1))} \ {a}) := by
  sorry

/-- DLMF 31.3.9: for `ε ∉ {1, 2, 3, …}` the solution with exponent `1 - ε` at `z = a` is
`((a-z)/(a-1))^{1-ε} Hl(a/(a-1), (a(δ+γ) - γ)(1-ε)/(a-1) + (αβa - q)/(a-1);
α + 1 - ε, β + 1 - ε, 2 - ε, δ; (a-z)/(a-1))`. -/
@[dlmf 31.3.E9]
theorem heunLocal_second_at_a_isHeunSolOn (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hε' : ∀ n : ℕ, ε ≠ (n : ℂ) + 1) (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => ((a - z) / (a - 1)) ^ (1 - ε) *
        heunLocal (a / (a - 1)) ((a * (δ + γ) - γ) * (1 - ε) / (a - 1) + (α * β * a - q) / (a - 1))
          (α + 1 - ε) (β + 1 - ε) (2 - ε) δ ((a - z) / (a - 1)))
      {z | ‖(a - z) / (a - 1)‖ < heunLocalRadius (a / (a - 1)) ∧
        (a - z) / (a - 1) ∈ slitPlane} := by
  sorry

/-- DLMF 31.3.10 (as corrected in DLMF 1.1.7): for `α - β ∉ {-1, -2, …}` the solution with
exponent `α` at `∞` is
`z^{-α} Hl(1/a, q/a - α(β - ε) - (α/a)(β - δ); α, α - γ + 1, α - β + 1, δ; 1/z)`,
valid for `|z| > max(1, |a|)` off the branch cut of `z^{-α}`. -/
@[dlmf 31.3.E10]
theorem heunLocal_at_infinity_isHeunSolOn (ha0 : a ≠ 0)
    (hαβ : ∀ n : ℕ, α - β + 1 ≠ -(n : ℂ)) (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => z ^ (-α) * heunLocal (1 / a) (q / a - α * (β - ε) - α / a * (β - δ)) α
        (α - γ + 1) (α - β + 1) δ (1 / z))
      {z | ‖1 / z‖ < heunLocalRadius (1 / a) ∧ z ∈ slitPlane} := by
  sorry

/-- DLMF 31.3.11 (as corrected in DLMF 1.1.7): for `β - α ∉ {-1, -2, …}` the solution with
exponent `β` at `∞` is
`z^{-β} Hl(1/a, q/a - β(α - ε) - (β/a)(α - δ); β, β - γ + 1, β - α + 1, δ; 1/z)`. -/
@[dlmf 31.3.E11]
theorem heunLocal_second_at_infinity_isHeunSolOn (ha0 : a ≠ 0)
    (hαβ : ∀ n : ℕ, β - α + 1 ≠ -(n : ℂ)) (hε : ε = heunEps α β γ δ) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => z ^ (-β) * heunLocal (1 / a) (q / a - β * (α - ε) - β / a * (α - δ)) β
        (β - γ + 1) (β - α + 1) δ (1 / z))
      {z | ‖1 / z‖ < heunLocalRadius (1 / a) ∧ z ∈ slitPlane} := by
  sorry

/-! ### Equivalent expressions (§31.3(iii)) -/

/-- The coefficients of `Hl(1/a, q/a; α, β, γ, ε; ·)` are `a^j` times those of
`Hl(a, q; α, β, γ, δ; ·)`, where `ε = α + β + 1 - γ - δ`. -/
theorem h31_heunLocalCoeff_inv (ha : a ≠ 0) (j : ℕ) :
    heunLocalCoeff (1 / a) (q / a) α β γ (heunEps α β γ δ) j =
      a ^ j * heunLocalCoeff a q α β γ δ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => simp
    | 1, _ =>
      simp only [heunLocalCoeff_one, pow_one]
      rcases eq_or_ne γ 0 with rfl | hγ
      · simp
      · field_simp
    | k + 2, ih =>
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have hQ : heunRecQ (1 / a) α β γ (heunEps α β γ δ) (k + 1) =
          heunRecQ a α β γ δ (k + 1) / a := by
        unfold heunRecQ heunEps
        field_simp
        ring
      have hR : heunRecR (1 / a) γ (k + 1) = heunRecR a γ (k + 1) / a ^ 2 := by
        unfold heunRecR
        field_simp
      rw [heunLocalCoeff, heunLocalCoeff, h1, h0, hQ, hR, div_div_eq_mul_div, mul_div_assoc']
      congr 1
      field_simp
      ring

/-- DLMF 31.3.12: `Hl(a, q; α, β, γ, δ; z) = Hl(1/a, q/a; α, β, γ, α + β + 1 - γ - δ; z/a)`,
from the homography `z̃ = z/a`. Stronger than DLMF: proved for every `z` and all parameters with
`a ≠ 0`, since the two series agree term by term (including the junk values outside the disk of
convergence). -/
@[dlmf 31.3.E12]
theorem heunLocal_eq_heunLocal_inv (ha : a ≠ 0) (z : ℂ) :
    heunLocal a q α β γ δ z =
      heunLocal (1 / a) (q / a) α β γ (α + β + 1 - γ - δ) (z / a) := by
  rw [heunLocal, heunLocal]
  refine tsum_congr fun j => ?_
  rw [show α + β + 1 - γ - δ = heunEps α β γ δ from rfl, h31_heunLocalCoeff_inv ha, div_pow]
  field_simp

/-- DLMF 31.3.13: `Hl(a, q; α, β, γ, δ; z)
= (1-z)^{-α} Hl(a/(a-1), -(q - aαγ)/(a-1); α, α + 1 - δ, γ, α + 1 - β; z/(z-1))`, from the
homography `z̃ = z/(z-1)`, where both series converge. -/
@[dlmf 31.3.E13]
theorem heunLocal_eq_pfaff (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) {z : ℂ}
    (hz : ‖z‖ < heunLocalRadius a) (hz' : ‖z / (z - 1)‖ < heunLocalRadius (a / (a - 1))) :
    heunLocal a q α β γ δ z =
      (1 - z) ^ (-α) * heunLocal (a / (a - 1)) (-(q - a * α * γ) / (a - 1)) α (α + 1 - δ) γ
        (α + 1 - β) (z / (z - 1)) := by
  sorry

end DLMF.Heun
