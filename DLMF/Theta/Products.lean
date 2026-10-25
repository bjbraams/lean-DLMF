/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic
public import DLMF.QSeries.Identities
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# Theta functions: infinite products and related results (DLMF §20.5)

Single products (20.5.1–20.5.8), Jacobi's triple product in theta form (20.5.9), the
logarithmic derivatives (20.5.10–20.5.13) and the Eisenstein-ordered double products
(20.5.14–20.5.17). Throughout `q = e^{iπτ}`, `q^{1/4} = e^{iπτ/4}` and `Im τ > 0`.
Products over `n ≥ 1` are `HasProd` statements over `k : ℕ` with `n = k + 1`.

The triple product `DLMF.QSeries.jacobi_triple_product` (DLMF 17.8.1) is the source of the
product formulas.

In 20.5.10 and 20.5.11 the left-hand sides are meromorphic with removable singularities at the
real zeros of `θ₁`, resp. `θ₂`; with Lean's conventions `x / 0 = 0` both sides vanish there, so
the statements hold on the whole strip.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic DLMF.QSeries

/-! ### Helpers -/

/-- `HasProd` form of `(a;Q)_∞` for `‖Q‖ < 1`. -/
lemma th20_hasProd_qPochhammerInf (a : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun k : ℕ => 1 - a * q ^ k) (qPochhammerInf a q) :=
  (multipliable_one_sub_mul_pow hq).hasProd

/-- The triple product for `θ₃` as one `HasProd` over `k : ℕ`. -/
lemma th20_three_hasProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasProd (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + cexp (π * I * τ) ^ (2 * k + 1) * cexp (2 * I * z)) *
        (1 + cexp (π * I * τ) ^ (2 * k + 1) * (cexp (2 * I * z))⁻¹))
      (jacobiThetaThreeTau z τ) := by
  have hQn : ‖cexp (π * I * τ) ^ 2‖ < 1 := by
    rw [norm_pow]
    have h := th20_norm_nome_lt_one hτ
    nlinarith [norm_nonneg (cexp (π * I * τ))]
  rw [th20_three_eq_qPochhammer z hτ]
  convert ((th20_hasProd_qPochhammerInf _ hQn).mul (th20_hasProd_qPochhammerInf _ hQn)).mul
    (th20_hasProd_qPochhammerInf _ hQn) using 1
  funext k
  ring

/-! ### §20.5(i) Single products -/

/-- DLMF 20.5.2: `θ₂(z,q) = 2q^{1/4} cos z ∏_{n≥1} (1 - q^{2n})(1 + 2q^{2n} cos 2z + q^{4n})`. -/
@[dlmf 20.5.E2]
theorem jacobiThetaTwoTau_hasProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))) ∧
      jacobiThetaTwoTau z τ = 2 * cexp (π * I * τ / 4) * cos z *
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))) := by
  have hQn := th20_norm_nome_sq_lt_one hτ
  have hw1 : cexp (2 * I * z) * (cexp (2 * I * z))⁻¹ = 1 := mul_inv_cancel₀ (exp_ne_zero _)
  have hcos := th20_exp_add_inv z
  set E := cexp (π * I * τ) with hE
  set w := cexp (2 * I * z) with hw
  have hP := ((th20_hasProd_qPochhammerInf (E ^ 2) hQn).mul
    (th20_hasProd_qPochhammerInf (-(E ^ 2 * w)) hQn)).mul
    (th20_hasProd_qPochhammerInf (-(w⁻¹ * E ^ 2)) hQn)
  have key : ∀ k : ℕ, (1 - E ^ 2 * (E ^ 2) ^ k) * (1 - -(E ^ 2 * w) * (E ^ 2) ^ k) *
      (1 - -(w⁻¹ * E ^ 2) * (E ^ 2) ^ k) =
      (1 - E ^ (2 * (k + 1))) * (1 + 2 * E ^ (2 * (k + 1)) * cos (2 * z) + E ^ (4 * (k + 1))) :=
    fun k => by
      linear_combination (1 - E ^ (2 * (k + 1))) * E ^ (2 * (k + 1)) * hcos +
        (1 - E ^ (2 * (k + 1))) * (E ^ (2 * (k + 1))) ^ 2 * hw1
  have hP' := th20_hasProd_congr hP key
  have hw' : cexp (2 * I * (z + π * τ / 2)) = E * w := by
    rw [hE, hw, ← exp_add]; congr 1; ring
  have hEw : E * (E * w)⁻¹ = w⁻¹ := by
    have hE0 : E ≠ 0 := exp_ne_zero _
    field_simp
  have h3 : jacobiThetaThreeTau (z + π * τ / 2) τ = (1 + w⁻¹) * (qPochhammerInf (E ^ 2) (E ^ 2) *
      qPochhammerInf (-(E ^ 2 * w)) (E ^ 2) * qPochhammerInf (-(w⁻¹ * E ^ 2)) (E ^ 2)) := by
    rw [th20_three_eq_qPochhammer _ hτ, ← hE, hw', qPochhammerInf_shift (a := -(E * (E * w)⁻¹)) hQn,
      hEw, show -(E * (E * w)) = -(E ^ 2 * w) by ring, show -w⁻¹ * E ^ 2 = -(w⁻¹ * E ^ 2) by ring]
    ring
  have hcz : cexp (I * z) * (1 + w⁻¹) = 2 * cos z := by
    rw [hw, ← exp_neg, mul_add, mul_one, ← exp_add, cos, show I * z + -(2 * I * z) = -z * I by ring,
      show I * z = z * I by ring]
    ring
  refine ⟨hP'.multipliable, ?_⟩
  rw [jacobiThetaTwoTau, exp_add, h3, hP'.tprod_eq,
    show ∀ a b c d : ℂ, a * b * (c * d) = a * (b * c) * d from fun a b c d => by ring, hcz]
  ring

/-- DLMF 20.5.1: `θ₁(z,q) = 2q^{1/4} sin z ∏_{n≥1} (1 - q^{2n})(1 - 2q^{2n} cos 2z + q^{4n})`. -/
@[dlmf 20.5.E1]
theorem jacobiThetaOneTau_hasProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))) ∧
      jacobiThetaOneTau z τ = 2 * cexp (π * I * τ / 4) * sin z *
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))) := by
  obtain ⟨hm, he⟩ := jacobiThetaTwoTau_hasProd (z + π / 2) hτ
  have hc : cos (2 * (z + π / 2)) = -cos (2 * z) := by
    rw [show 2 * (z + π / 2) = 2 * z + π by ring, cos_add_pi]
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * (z + π / 2)) +
        cexp (π * I * τ) ^ (4 * (k + 1))) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1))) := fun k => by rw [hc]; ring
  refine ⟨hm.congr key, ?_⟩
  rw [jacobiThetaOneTau, he, cos_add_pi_div_two, tprod_congr key]
  ring

/-- DLMF 20.5.3: `θ₃(z,q) = ∏_{n≥1} (1 - q^{2n})(1 + 2q^{2n-1} cos 2z + q^{4n-2})`. -/
@[dlmf 20.5.E3]
theorem jacobiThetaThreeTau_hasProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))) ∧
      jacobiThetaThreeTau z τ =
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))) := by
  have h := th20_three_hasProd z hτ
  have hw1 : cexp (2 * I * z) * (cexp (2 * I * z))⁻¹ = 1 := mul_inv_cancel₀ (exp_ne_zero _)
  have hcos := th20_exp_add_inv z
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 + cexp (π * I * τ) ^ (2 * k + 1) * cexp (2 * I * z)) *
      (1 + cexp (π * I * τ) ^ (2 * k + 1) * (cexp (2 * I * z))⁻¹) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2)) := fun k => by
    linear_combination (1 - cexp (π * I * τ) ^ (2 * (k + 1))) * cexp (π * I * τ) ^ (2 * k + 1) *
      hcos + (1 - cexp (π * I * τ) ^ (2 * (k + 1))) * (cexp (π * I * τ) ^ (2 * k + 1)) ^ 2 * hw1
  have h' := th20_hasProd_congr h key
  exact ⟨h'.multipliable, h'.tprod_eq.symm⟩

/-- DLMF 20.5.4: `θ₄(z,q) = ∏_{n≥1} (1 - q^{2n})(1 - 2q^{2n-1} cos 2z + q^{4n-2})`. -/
@[dlmf 20.5.E4]
theorem jacobiThetaFourTau_hasProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))) ∧
      jacobiThetaFourTau z τ =
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))) := by
  obtain ⟨hm, he⟩ := jacobiThetaThreeTau_hasProd (z + π / 2) hτ
  have hc : cos (2 * (z + π / 2)) = -cos (2 * z) := by
    rw [show 2 * (z + π / 2) = 2 * z + π by ring, cos_add_pi]
  have key : ∀ k : ℕ, (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
      (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * (z + π / 2)) +
        cexp (π * I * τ) ^ (4 * k + 2)) =
      (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2)) := fun k => by rw [hc]; ring
  exact ⟨hm.congr key, by rw [jacobiThetaFourTau, he]; exact tprod_congr key⟩

/-- DLMF 20.5.5: `θ₁(z|τ) = θ₁'(0|τ) sin z ∏_{n≥1} sin(nπτ + z) sin(nπτ - z)/sin²(nπτ)`. -/
@[dlmf 20.5.E5]
theorem jacobiThetaOneTau_hasProd_sin (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => sin ((k + 1) * π * τ + z) * sin ((k + 1) * π * τ - z) /
        sin ((k + 1) * π * τ) ^ 2) ∧
      jacobiThetaOneTau z τ = jacobiThetaOneDerivNullTau τ * sin z *
        ∏' k : ℕ, (sin ((k + 1) * π * τ + z) * sin ((k + 1) * π * τ - z) /
        sin ((k + 1) * π * τ) ^ 2) := by
  sorry

/-- DLMF 20.5.6: `θ₂(z|τ) = θ₂(0|τ) cos z ∏_{n≥1} cos(nπτ + z) cos(nπτ - z)/cos²(nπτ)`. -/
@[dlmf 20.5.E6]
theorem jacobiThetaTwoTau_hasProd_cos (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => cos ((k + 1) * π * τ + z) * cos ((k + 1) * π * τ - z) /
        cos ((k + 1) * π * τ) ^ 2) ∧
      jacobiThetaTwoTau z τ = jacobiThetaTwoNullTau τ * cos z *
        ∏' k : ℕ, (cos ((k + 1) * π * τ + z) * cos ((k + 1) * π * τ - z) /
        cos ((k + 1) * π * τ) ^ 2) := by
  sorry

/-- DLMF 20.5.7: `θ₃(z|τ) = θ₃(0|τ) ∏_{n≥1} cos((n-½)πτ + z) cos((n-½)πτ - z)/cos²((n-½)πτ)`. -/
@[dlmf 20.5.E7]
theorem jacobiThetaThreeTau_hasProd_cos (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => cos ((k + 1 / 2) * π * τ + z) * cos ((k + 1 / 2) * π * τ - z) /
        cos ((k + 1 / 2) * π * τ) ^ 2) ∧
      jacobiThetaThreeTau z τ = jacobiThetaThreeNullTau τ *
        ∏' k : ℕ, (cos ((k + 1 / 2) * π * τ + z) * cos ((k + 1 / 2) * π * τ - z) /
        cos ((k + 1 / 2) * π * τ) ^ 2) := by
  sorry

/-- DLMF 20.5.8: `θ₄(z|τ) = θ₄(0|τ) ∏_{n≥1} sin((n-½)πτ + z) sin((n-½)πτ - z)/sin²((n-½)πτ)`. -/
@[dlmf 20.5.E8]
theorem jacobiThetaFourTau_hasProd_sin (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Multipliable (fun k : ℕ => sin ((k + 1 / 2) * π * τ + z) * sin ((k + 1 / 2) * π * τ - z) /
        sin ((k + 1 / 2) * π * τ) ^ 2) ∧
      jacobiThetaFourTau z τ = jacobiThetaFourNullTau τ *
        ∏' k : ℕ, (sin ((k + 1 / 2) * π * τ + z) * sin ((k + 1 / 2) * π * τ - z) /
        sin ((k + 1 / 2) * π * τ) ^ 2) := by
  sorry

/-- DLMF 20.5.9 (Jacobi's triple product): with `p = e^{iπz}`, `q = e^{iπτ}`,
`θ₃(πz|τ) = ∑_{n∈ℤ} p^{2n} q^{n²} = ∏_{n≥1} (1 - q^{2n})(1 + q^{2n-1}p²)(1 + q^{2n-1}p^{-2})`. -/
@[dlmf 20.5.E9]
theorem jacobiThetaThreeTau_triple_product (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => cexp (π * I * z) ^ (2 * n) * cexp (π * I * τ) ^ (n ^ 2))
        (jacobiThetaThreeTau (π * z) τ) ∧
      Multipliable (fun k : ℕ => (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
          (1 + cexp (π * I * τ) ^ (2 * k + 1) * cexp (π * I * z) ^ 2) *
          (1 + cexp (π * I * τ) ^ (2 * k + 1) * (cexp (π * I * z) ^ 2)⁻¹)) ∧
      jacobiThetaThreeTau (π * z) τ =
        ∏' k : ℕ, ((1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
          (1 + cexp (π * I * τ) ^ (2 * k + 1) * cexp (π * I * z) ^ 2) *
          (1 + cexp (π * I * τ) ^ (2 * k + 1) * (cexp (π * I * z) ^ 2)⁻¹)) := by
  have hp : cexp (π * I * z) ^ 2 = cexp (2 * I * (π * z)) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have hP := th20_three_hasProd (π * z) hτ
  rw [← hp] at hP
  refine ⟨?_, hP.multipliable, hP.tprod_eq.symm⟩
  convert th20_hasSum_three (π * z) hτ using 1
  funext n
  rw [th20_exp_zpow, th20_exp_zpow, ← exp_add]
  congr 1; push_cast; ring

/-! ### §20.5(ii) Logarithmic derivatives -/

/-- DLMF 20.5.10: for `|Im z| < π Im τ`,
`θ₁'/θ₁ - cot z = 4 sin 2z ∑ q^{2n}/(1 - 2q^{2n} cos 2z + q^{4n})
  = 4 ∑ q^{2n}/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E10]
theorem jacobiThetaOneTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im) :
    HasSum (fun k : ℕ => 4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))))
      (deriv (fun w => jacobiThetaOneTau w τ) z / jacobiThetaOneTau z τ - cot z) ∧
    HasSum (fun k : ℕ => 4 * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaOneTau w τ) z / jacobiThetaOneTau z τ - cot z) := by
  sorry

/-- DLMF 20.5.11: for `|Im z| < π Im τ`,
`θ₂'/θ₂ + tan z = -4 sin 2z ∑ q^{2n}/(1 + 2q^{2n} cos 2z + q^{4n})
  = 4 ∑ (-1)ⁿ q^{2n}/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E11]
theorem jacobiThetaTwoTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im) :
    HasSum (fun k : ℕ => -4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))))
      (deriv (fun w => jacobiThetaTwoTau w τ) z / jacobiThetaTwoTau z τ + tan z) ∧
    HasSum (fun k : ℕ => 4 * (-1 : ℂ) ^ (k + 1) * (cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaTwoTau w τ) z / jacobiThetaTwoTau z τ + tan z) := by
  sorry

/-- DLMF 20.5.12: for `|Im z| < π Im τ / 2`,
`θ₃'/θ₃ = -4 sin 2z ∑ q^{2n-1}/(1 + 2q^{2n-1} cos 2z + q^{4n-2})
  = 4 ∑ (-1)ⁿ qⁿ/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E12]
theorem jacobiThetaThreeTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im / 2) :
    HasSum (fun k : ℕ => -4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * k + 1) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))))
      (deriv (fun w => jacobiThetaThreeTau w τ) z / jacobiThetaThreeTau z τ) ∧
    HasSum (fun k : ℕ => 4 * (-1 : ℂ) ^ (k + 1) * (cexp (π * I * τ) ^ (k + 1) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaThreeTau w τ) z / jacobiThetaThreeTau z τ) := by
  sorry

/-- DLMF 20.5.13: for `|Im z| < π Im τ / 2`,
`θ₄'/θ₄ = 4 sin 2z ∑ q^{2n-1}/(1 - 2q^{2n-1} cos 2z + q^{4n-2}) = 4 ∑ qⁿ/(1 - q^{2n}) sin 2nz`. -/
@[dlmf 20.5.E13]
theorem jacobiThetaFourTau_logDeriv {z τ : ℂ} (hτ : 0 < τ.im) (hz : |z.im| < π * τ.im / 2) :
    HasSum (fun k : ℕ => 4 * sin (2 * z) * (cexp (π * I * τ) ^ (2 * k + 1) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))))
      (deriv (fun w => jacobiThetaFourTau w τ) z / jacobiThetaFourTau z τ) ∧
    HasSum (fun k : ℕ => 4 * (cexp (π * I * τ) ^ (k + 1) /
        (1 - cexp (π * I * τ) ^ (2 * (k + 1)))) * sin (2 * (k + 1) * z))
      (deriv (fun w => jacobiThetaFourTau w τ) z / jacobiThetaFourTau z τ) := by
  sorry

/-- DLMF §20.5(ii): under the conditions of 20.5.10–20.5.13 the series converge absolutely and
uniformly on compact subsets. Stated for the Fourier series of 20.5.10/20.5.11 on compact subsets
of the strip `|Im z| < π Im τ` and of 20.5.12/20.5.13 on compact subsets of `|Im z| < π Im τ/2`,
in Weierstrass M-test form: there is a summable majorant. -/
@[dlmf 20.5.ii]
theorem jacobiTheta_logDeriv_series_uniform {τ : ℂ} (hτ : 0 < τ.im) (K : Set ℂ)
    (hK : IsCompact K) :
    ((∀ z ∈ K, |z.im| < π * τ.im) → ∃ u : ℕ → ℝ, Summable u ∧ ∀ k : ℕ, ∀ z ∈ K,
      ‖cexp (π * I * τ) ^ (2 * (k + 1)) / (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        sin (2 * (k + 1) * z)‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * (k + 1)) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * (k + 1)) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * (k + 1)))‖ ≤ u k) ∧
    ((∀ z ∈ K, |z.im| < π * τ.im / 2) → ∃ u : ℕ → ℝ, Summable u ∧ ∀ k : ℕ, ∀ z ∈ K,
      ‖cexp (π * I * τ) ^ (k + 1) / (1 - cexp (π * I * τ) ^ (2 * (k + 1))) *
        sin (2 * (k + 1) * z)‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * k + 1) /
        (1 - 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))‖ ≤ u k ∧
      ‖cexp (π * I * τ) ^ (2 * k + 1) /
        (1 + 2 * cexp (π * I * τ) ^ (2 * k + 1) * cos (2 * z) +
          cexp (π * I * τ) ^ (4 * k + 2))‖ ≤ u k) := by
  sorry

/-! ### §20.5(iii) Double products -/

/-- DLMF 20.5.14: `θ₁(z|τ) = z θ₁'(0|τ) lim_{N→∞} ∏_{n=-N}^{N} lim_{M→∞} ∏_{m=-M, |m|+|n|≠0}^{M}
(1 + z/((m + nτ)π))`, in this (Eisenstein) order of limits. -/
@[dlmf 20.5.E14]
theorem jacobiThetaOneTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (-(M : ℤ)) M,
          if m = 0 ∧ n = 0 then (1 : ℂ) else 1 + z / ((m + n * τ) * π)) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => z * jacobiThetaOneDerivNullTau τ * ∏ n ∈ Finset.Icc (-(N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaOneTau z τ)) := by
  sorry

/-- DLMF 20.5.15: `θ₂(z|τ) = θ₂(0|τ) lim_{N→∞} ∏_{n=-N}^{N} lim_{M→∞} ∏_{m=1-M}^{M}
(1 + z/((m - 1/2 + nτ)π))`. -/
@[dlmf 20.5.E15]
theorem jacobiThetaTwoTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (1 - (M : ℤ)) M,
          (1 + z / ((m - 1 / 2 + n * τ) * π))) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => jacobiThetaTwoNullTau τ * ∏ n ∈ Finset.Icc (-(N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaTwoTau z τ)) := by
  sorry

/-- DLMF 20.5.16: `θ₃(z|τ) = θ₃(0|τ) lim_{N→∞} ∏_{n=1-N}^{N} lim_{M→∞} ∏_{m=1-M}^{M}
(1 + z/((m - 1/2 + (n - 1/2)τ)π))`. -/
@[dlmf 20.5.E16]
theorem jacobiThetaThreeTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (1 - (M : ℤ)) M,
          (1 + z / ((m - 1 / 2 + (n - 1 / 2) * τ) * π))) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => jacobiThetaThreeNullTau τ * ∏ n ∈ Finset.Icc (1 - (N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaThreeTau z τ)) := by
  sorry

/-- DLMF 20.5.17: `θ₄(z|τ) = θ₄(0|τ) lim_{N→∞} ∏_{n=1-N}^{N} lim_{M→∞} ∏_{m=-M}^{M}
(1 + z/((m + (n - 1/2)τ)π))`. -/
@[dlmf 20.5.E17]
theorem jacobiThetaFourTau_doubleProd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ L : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (-(M : ℤ)) M,
          (1 + z / ((m + (n - 1 / 2) * τ) * π))) atTop (𝓝 (L n))) ∧
      Tendsto (fun N : ℕ => jacobiThetaFourNullTau τ * ∏ n ∈ Finset.Icc (1 - (N : ℤ)) N, L n)
        atTop (𝓝 (jacobiThetaFourTau z τ)) := by
  sorry

/-- DLMF §20.5(iii): the double products are not absolutely convergent: for `z ≠ 0` the terms
`z/((m + nτ)π)` are not absolutely summable over the lattice. -/
@[dlmf 20.5.iii]
theorem jacobiTheta_doubleProd_not_absolutely_convergent {z τ : ℂ} (hz : z ≠ 0) (hτ : 0 < τ.im) :
    ¬ Summable (fun p : ℤ × ℤ => ‖z / ((p.1 + p.2 * τ) * π)‖) := by
  sorry

end DLMF.Theta

end
