/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.RationalDLMF
public import DLMF.Painleve.Airy
public import DLMF.Confluent.ParabolicCylinder
public import DLMF.ErrorFunctions.AnalyticProperties
public import DLMF.OrthogonalPolynomials.Differential
public import DLMF.Weierstrass.EllipticFunctionsAndInvariants

/-!
# Special function solutions of the Painlevé equations (DLMF §32.10)

DLMF normalization (`DLMF.Painleve.Basic`). For each of `PII`–`PVI`, the Riccati equation of
§32.10 (the case `n = 0` of the parameter conditions 32.10.11, 32.10.15, 32.10.23, 32.10.28)
is proved to imply the Painlevé equation. The Airy solutions 32.10.4–32.10.6 of `PII` are
proved, bridging to the Beals–Wong construction of `DLMF.Painleve.Airy` (`airyPII`, with the
cube-root scale `k = -2^{-1/3}`, `k³ = -1/2`); existence for every `α = n + 1/2` (32.10.2) is
the Airy hierarchy `airyPIIHierarchy`. The `α = 5/2` member 32.10.7 and the Wronskian formula
32.10.8–32.10.9 are admitted. The Hermite solutions 32.10.20–32.10.21 and the error-function
solutions 32.10.16, 32.10.22 of `PIV` are proved. The Bessel, parabolic cylinder and
hypergeometric solutions of the Riccati equations (32.10.13–32.10.14, 32.10.18–32.10.19,
32.10.30–32.10.31) are proved from the linear ODEs of `J_ν`, `Y_ν`, `U`, `V` and `₂F₁`; the
Whittaker solution 32.10.26–32.10.27 and Picard's solution 32.10.32–32.10.34 are admitted
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

/-- Identity under the stated parameter and domain assumptions: `ε ^ 2 = 1`. -/
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
      isPainleveIIOn_iff_isPIIOn.mpr (by convert h using 1; norm_num)
    have h' := b32_isPainleveIIOn_neg h0
    rw [show (1 : ℂ) / 2 = -(-1 / 2) by norm_num]
    refine b32_congr h' hS fun z _ => ?_
    simp only [hd, airyPII, airySeed]
    ring
  · have h0 : IsPainleveIIOn (-1 / 2) (airyPII k C₁ C₂) {z | airySeed k C₁ C₂ z ≠ 0} :=
      isPainleveIIOn_iff_isPIIOn.mpr (by convert h using 1; norm_num)
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
      isPainleveIIOn_iff_isPIIOn.mpr ?_⟩
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
  have hfun : (fun z => 1 / (2 * Φ z ^ 2 + z) + (2 * z * Φ z ^ 2 + Φ z + z ^ 2) /
      (4 * Φ z ^ 3 + 2 * z * Φ z - 1)) = fun x => 1 / ((1 : ℂ) * x + (2 : ℂ) * Φ x ^ 2) + ((1 : ℂ)
          * x ^ 2 + (2 : ℂ) * x * Φ x ^ 2 + (1 : ℂ) * Φ x) / ((2 : ℂ) * x * Φ x + (4 : ℂ) * Φ x ^ 3
          + (-1 : ℂ)) :=
    funext fun x => by ring
  rw [hfun]
  have hD0 : ∀ x ∈ U, ((1 : ℂ) * x + (2 : ℂ) * Φ x ^ 2) ≠ 0 := fun x hx => by
    convert hD x hx using 1; ring
  have hE0 : ∀ x ∈ U, ((2 : ℂ) * x * Φ x + (4 : ℂ) * Φ x ^ 3 + (-1 : ℂ)) ≠ 0 := fun x hx => by
    convert hE x hx using 1; ring
  have hD : ∀ x ∈ U, HasDerivAt (fun x => ((1 : ℂ) * x + (2 : ℂ) * Φ x ^ 2)) _ x := fun x hx =>
    (((hasDerivAt_const x (1 : ℂ)).mul (hasDerivAt_id' x)).add ((hasDerivAt_const x (2 : ℂ)).mul
        ((hΦ x hx).pow 2)))
  have hE : ∀ x ∈ U, HasDerivAt (fun x => ((2 : ℂ) * x * Φ x + (4 : ℂ) * Φ x ^ 3 +
      (-1 : ℂ))) _ x := fun x hx =>
    (((((hasDerivAt_const x (2 : ℂ)).mul (hasDerivAt_id' x)).mul (hΦ x hx)).add
        ((hasDerivAt_const x (4 : ℂ)).mul ((hΦ x hx).pow 3))).add (hasDerivAt_const x (-1 : ℂ)))
  have hN : ∀ x ∈ U, HasDerivAt (fun x => ((1 : ℂ) * x ^ 2 + (2 : ℂ) * x * Φ x ^ 2 + (1 : ℂ)
      * Φ x)) _ x := fun x hx =>
    ((((hasDerivAt_const x (1 : ℂ)).mul ((hasDerivAt_id' x).pow 2)).add (((hasDerivAt_const x
        (2 : ℂ)).mul (hasDerivAt_id' x)).mul ((hΦ x hx).pow 2))).add ((hasDerivAt_const x
        (1 : ℂ)).mul (hΦ x hx)))
  have hD1 : ∀ x ∈ U, HasDerivAt (fun x => ((-2 : ℂ) * x * Φ x + (-4 : ℂ) * Φ x ^ 3 +
      (1 : ℂ))) _ x := fun x hx =>
    (((((hasDerivAt_const x (-2 : ℂ)).mul (hasDerivAt_id' x)).mul (hΦ x hx)).add
        ((hasDerivAt_const x (-4 : ℂ)).mul ((hΦ x hx).pow 3))).add (hasDerivAt_const x (1 : ℂ)))
  have hE1 : ∀ x ∈ U, HasDerivAt (fun x => ((-1 : ℂ) * x ^ 2 + (-8 : ℂ) * x * Φ x ^ 2 + (-12 : ℂ)
      * Φ x ^ 4 + (2 : ℂ) * Φ x)) _ x := fun x hx =>
    (((((hasDerivAt_const x (-1 : ℂ)).mul ((hasDerivAt_id' x).pow 2)).add (((hasDerivAt_const x
        (-8 : ℂ)).mul (hasDerivAt_id' x)).mul ((hΦ x hx).pow 2))).add ((hasDerivAt_const x
        (-12 : ℂ)).mul ((hΦ x hx).pow 4))).add ((hasDerivAt_const x (2 : ℂ)).mul (hΦ x hx)))
  have hN1 : ∀ x ∈ U, HasDerivAt (fun x => ((-2 : ℂ) * x ^ 2 * Φ x + (-4 : ℂ) * x * Φ x ^ 3 +
      (3 / 2 : ℂ) * x + (1 : ℂ) * Φ x ^ 2)) _ x := fun x hx =>
    ((((((hasDerivAt_const x (-2 : ℂ)).mul ((hasDerivAt_id' x).pow 2)).mul (hΦ x hx)).add
        (((hasDerivAt_const x (-4 : ℂ)).mul (hasDerivAt_id' x)).mul ((hΦ x hx).pow 3))).add
        ((hasDerivAt_const x (3 / 2 : ℂ)).mul (hasDerivAt_id' x))).add ((hasDerivAt_const x
        (1 : ℂ)).mul ((hΦ x hx).pow 2)))
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun x => -((-2 : ℂ) * x * Φ x + (-4 : ℂ) * Φ x ^ 3
      + (1 : ℂ)) / ((1 : ℂ) * x + (2 : ℂ) * Φ x ^ 2) ^ 2 + (((-2 : ℂ) * x ^ 2 * Φ x + (-4 : ℂ) * x
      * Φ x ^ 3 + (3 / 2 : ℂ) * x + (1 : ℂ) * Φ x ^ 2) * ((2 : ℂ) * x * Φ x + (4 : ℂ) * Φ x ^ 3 +
      (-1 : ℂ)) - ((1 : ℂ) * x ^ 2 + (2 : ℂ) * x * Φ x ^ 2 + (1 : ℂ) * Φ x) * ((-1 : ℂ) * x ^ 2 +
      (-8 : ℂ) * x * Φ x ^ 2 + (-12 : ℂ) * Φ x ^ 4 + (2 : ℂ) * Φ x)) / ((2 : ℂ) * x * Φ x + (4 : ℂ)
      * Φ x ^ 3 + (-1 : ℂ)) ^ 2) (fun x hx => ?_) (fun x hx => ?_)
  · refine (((hasDerivAt_const x (1 : ℂ)).div (hD x hx) (hD0 x hx)).add
      ((hN x hx).div (hE x hx) (hE0 x hx))).congr_deriv ?_
    have := hD0 x hx
    have := hE0 x hx
    simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    ring
  · refine (((hD1 x hx).neg.div ((hD x hx).pow 2) (pow_ne_zero 2 (hD0 x hx))).add
      ((((hN1 x hx).mul (hE x hx)).sub ((hN x hx).mul (hE1 x hx))).div ((hE x hx).pow 2)
        (pow_ne_zero 2 (hE0 x hx)))).congr_deriv ?_
    have hd := hD0 x hx
    have he := hE0 x hx
    simp only [painleveIIRhs, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.neg_apply]
    generalize Φ x = p at hd he ⊢
    generalize hdd : 1 * x + 2 * p ^ 2 = d at hd ⊢
    generalize hee : 2 * x * p + 4 * p ^ 3 + -1 = e at he ⊢
    field_simp
    subst hdd hee
    ring

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

/-- At `z`, the function `(fun z : ℂ => z ^ a)` has derivative `(a * z ^ a / z)`. -/
private lemma p3b_hasDerivAt_cpow {a z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z ^ a) (a * z ^ a / z) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  refine (hasDerivAt_id z |>.cpow_const (c := a) (by simpa using hz)).congr_deriv ?_
  simp only [id_eq, mul_one]
  rw [cpow_sub _ _ hz0, cpow_one]
  ring

/-- A function differentiable on the slit plane has `deriv f` with derivative
`deriv (deriv f)` there. -/
private lemma p3b_hasDerivAt_deriv_slit {f : ℂ → ℂ}
    (hf : ∀ ζ ∈ slitPlane, DifferentiableAt ℂ f ζ) {ζ : ℂ} (hζ : ζ ∈ slitPlane) :
    HasDerivAt (deriv f) (deriv (deriv f) ζ) ζ :=
  (((DifferentiableOn.deriv (fun x hx => (hf x hx).differentiableWithinAt)
    isOpen_slitPlane) ζ hζ).differentiableAt (isOpen_slitPlane.mem_nhds hζ)).hasDerivAt

/-- A function differentiable on an open set has a differentiable `deriv` there. -/
private lemma p3b_hasDerivAt_deriv_open {f : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hf : ∀ ζ ∈ V, DifferentiableAt ℂ f ζ) {ζ : ℂ} (hζ : ζ ∈ V) :
    HasDerivAt (deriv f) (deriv (deriv f) ζ) ζ :=
  (((DifferentiableOn.deriv (fun x hx => (hf x hx).differentiableWithinAt) hV) ζ
    hζ).differentiableAt (hV.mem_nhds hζ)).hasDerivAt

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
  intro φ z hz hφ0
  have e1 : ε₁ ^ 2 = 1 := by rcases h₁ with h | h <;> simp [h]
  have e2 : ε₂ ^ 2 = 1 := by rcases h₂ with h | h <;> simp [h]
  set ν := α * ε₁ / 2 with hν
  set c := (ε₁ * ε₂) ^ (1 / 2 : ℂ) with hc
  have hc2 : c ^ 2 = ε₁ * ε₂ := by
    rw [hc, ← cpow_nat_mul]; norm_num
  set J := besselJ ν with hJ
  set Y := DLMF.Bessel.besselY ν with hY
  have hJd : ∀ ζ ∈ slitPlane, DifferentiableAt ℂ J ζ := fun ζ hζ =>
    (DLMF.Bessel.hasDerivAt_besselJ hζ).differentiableAt
  have hYd : ∀ ζ ∈ slitPlane, DifferentiableAt ℂ Y ζ := fun ζ hζ =>
    (DLMF.Bessel.hasDerivAt_besselY ν hζ).differentiableAt
  set B : ℂ → ℂ := fun ζ => C₁ * J ζ + C₂ * Y ζ with hB
  set B1 : ℂ → ℂ := fun ζ => C₁ * deriv J ζ + C₂ * deriv Y ζ with hB1
  have hBd : ∀ ζ ∈ slitPlane, HasDerivAt B (B1 ζ) ζ := fun ζ hζ =>
    ((hJd ζ hζ).hasDerivAt.const_mul C₁).add ((hYd ζ hζ).hasDerivAt.const_mul C₂)
  have hB1d : ∀ ζ ∈ slitPlane, HasDerivAt B1
      (C₁ * deriv (deriv J) ζ + C₂ * deriv (deriv Y) ζ) ζ := fun ζ hζ =>
    ((p3b_hasDerivAt_deriv_slit hJd hζ).const_mul C₁).add
      ((p3b_hasDerivAt_deriv_slit hYd hζ).const_mul C₂)
  have hode : ∀ ζ ∈ slitPlane, ζ ^ 2 * (C₁ * deriv (deriv J) ζ + C₂ * deriv (deriv Y) ζ) +
      ζ * B1 ζ + (ζ ^ 2 - ν ^ 2) * B ζ = 0 := fun ζ hζ => by
    have hj := DLMF.Bessel.besselJ_ode (ν := ν) hζ
    have hy := DLMF.Bessel.besselY_ode_all ν hζ
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hj hy
    simp only [hB, hB1]
    linear_combination C₁ * hj + C₂ * hy
  have hlin : ∀ x : ℂ, HasDerivAt (fun x => c * x) c x := fun x => by
    simpa using (hasDerivAt_id x).const_mul c
  set V := {x : ℂ | x ∈ slitPlane ∧ c * x ∈ slitPlane} with hV
  have hVo : IsOpen V := isOpen_slitPlane.inter
    (isOpen_slitPlane.preimage (continuous_const.mul continuous_id))
  have hzV : z ∈ V := ⟨hUs hz, hζ z hz⟩
  set φ1 : ℂ → ℂ := fun x => ν * x ^ ν / x * B (c * x) + x ^ ν * (B1 (c * x) * c) with hφ1
  have hφd : ∀ x ∈ V, HasDerivAt φ (φ1 x) x := fun x hx => by
    have := (p3b_hasDerivAt_cpow (a := ν) hx.1).mul ((hBd _ hx.2).comp x (hlin x))
    exact this.congr_deriv (by simp only [hφ1, Function.comp])
  have hev : (fun x => -ε₁ * deriv φ x / φ x) =ᶠ[𝓝 z] fun x => -ε₁ * φ1 x / φ x := by
    filter_upwards [hVo.mem_nhds hzV] with x hx
    rw [(hφd x hx).deriv]
  have hz0 : z ≠ 0 := slitPlane_ne_zero (hUs hz)
  have hs0 : z ^ ν ≠ 0 := by rw [cpow_def_of_ne_zero hz0]; exact exp_ne_zero _
  have hφ1d := (((p3b_hasDerivAt_cpow (a := ν) (hUs hz)).const_mul ν).div (hasDerivAt_id z)
    hz0).mul ((hBd _ (hζ z hz)).comp z (hlin z)) |>.add
    ((p3b_hasDerivAt_cpow (a := ν) (hUs hz)).mul (((hB1d _ (hζ z hz)).comp z (hlin z)).mul_const c))
  refine ((((hφ1d.const_mul (-ε₁)).div (hφd z hzV) hφ0)).congr_of_eventuallyEq hev).congr_deriv ?_
  rw [(hφd z hzV).deriv]
  have hO := hode _ (hζ z hz)
  have hφz : φ z = z ^ ν * B (c * z) := rfl
  simp only [hφz, hφ1, Function.comp_apply, id, Pi.mul_apply, Pi.div_apply, Pi.add_apply] at hφ0 ⊢
  generalize z ^ ν = S at hs0 hφ0 ⊢
  generalize B (c * z) = b at hφ0 hO ⊢
  generalize B1 (c * z) = b1 at hO ⊢
  generalize C₁ * deriv (deriv J) (c * z) + C₂ * deriv (deriv Y) (c * z) = b2 at hO ⊢
  have hb : b ≠ 0 := right_ne_zero_of_mul hφ0
  field_simp
  simp only [hν] at hO ⊢
  linear_combination (-b*ε₁) * hO + (b^2*ε₁*z^2 - b1^2*ε₁^3*z^2 + b1^2*ε₁*z^2) * hc2 +
    (-α^2*b^2*ε₁^3/4 - α*b*b1*c*ε₁^2*z + b^2*ε₂*z^2 - b1^2*ε₁^2*ε₂*z^2) * e1

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
  intro φ z hz
  have he2 : ε ^ 2 = 1 := by rcases hε with h | h <;> simp [h]
  set a := α + ε / 2 with ha
  set r : ℂ := (Real.sqrt 2 : ℂ) with hr
  have hr2 : r ^ 2 = 2 := by
    rw [hr, ← ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  set Y : ℂ → ℂ := fun x => C₁ * pcfU a x + C₂ * pcfV a x with hY
  set Y1 : ℂ → ℂ := fun x => C₁ * pcfUDeriv a x + C₂ * pcfVDeriv a x with hY1
  have hYd : ∀ x, HasDerivAt Y (Y1 x) x := fun x =>
    ((hasDerivAt_pcfU a x).const_mul C₁).add ((hasDerivAt_pcfV a x).const_mul C₂)
  have hY1d : ∀ x, HasDerivAt Y1 ((x ^ 2 / 4 + a) * Y x) x := fun x => by
    have := ((hasDerivAt_pcfUDeriv a x).const_mul C₁).add ((hasDerivAt_pcfVDeriv a x).const_mul C₂)
    exact this.congr_deriv (by simp only [hY]; ring)
  have hlin : ∀ x, HasDerivAt (fun x => r * x) r x := fun x => by
    simpa using (hasDerivAt_id x).const_mul r
  have hE : ∀ x, HasDerivAt (fun x => exp (ε * x ^ 2 / 2)) (ε * x * exp (ε * x ^ 2 / 2)) x :=
    fun x => by
      have := ((((hasDerivAt_id x).pow 2).const_mul ε).div_const 2).cexp
      exact this.congr_deriv (by simp; ring)
  set φ1 : ℂ → ℂ := fun x => (r * Y1 (r * x) + ε * x * Y (r * x)) * exp (ε * x ^ 2 / 2) with hφ1
  have hφd : ∀ x, HasDerivAt φ (φ1 x) x := fun x => by
    have := ((hYd (r * x)).comp x (hlin x)).mul (hE x)
    exact this.congr_deriv (by simp only [hφ1, Function.comp]; ring)
  have hdφ : deriv φ = φ1 := funext fun x => (hφd x).deriv
  have hφ1d : HasDerivAt φ1 ((r * (((r * z) ^ 2 / 4 + a) * Y (r * z) * r) +
      (ε * Y (r * z) + ε * z * (Y1 (r * z) * r))) * exp (ε * z ^ 2 / 2) +
      (r * Y1 (r * z) + ε * z * Y (r * z)) * (ε * z * exp (ε * z ^ 2 / 2))) z := by
    have h1 := ((hY1d (r * z)).comp z (hlin z)).const_mul r
    have h2 := ((hasDerivAt_id z).const_mul ε).mul ((hYd (r * z)).comp z (hlin z))
    have := (h1.add h2).mul (hE z)
    exact this.congr_deriv (by simp only [Function.comp, id, Pi.add_apply, Pi.mul_apply]; ring)
  rw [hdφ]
  have hφz : φ z = Y (r * z) * exp (ε * z ^ 2 / 2) := rfl
  have hexp : exp (ε * z ^ 2 / 2) ≠ 0 := exp_ne_zero _
  have hYz : Y (r * z) ≠ 0 := by
    intro h; apply hz; rw [hφz, h, zero_mul]
  refine (((hφ1d.const_mul (-ε)).div (hφd z) hz)).congr_deriv ?_
  rw [hφz]
  simp only [hφ1]
  rw [ha]
  field_simp
  linear_combination (-8 * Y (r * z) ^ 2 * α * ε - 4 * Y (r * z) ^ 2 * ε ^ 2 -
      2 * Y (r * z) ^ 2 * ε * r ^ 2 * z ^ 2 - 4 * Y (r * z) ^ 2 * ε * z ^ 2 -
      8 * Y1 (r * z) ^ 2 * ε ^ 3 + 8 * Y1 (r * z) ^ 2 * ε) * hr2 +
    (-8 * Y (r * z) ^ 2 * ε ^ 3 * z ^ 2 + 8 * Y (r * z) ^ 2 * ε * z ^ 2 - 16 * Y (r * z) ^ 2 -
      16 * Y (r * z) * Y1 (r * z) * ε ^ 2 * r * z - 16 * Y1 (r * z) ^ 2 * ε) * he2

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
  intro φ z hz hφ0
  have e1 : ε₃ ^ 2 = 1 := by rcases hε with h | h <;> simp [h]
  set B := 1 + (a + b) with hBdef
  have hB : ∀ k : ℕ, B ≠ -k := hμ
  have hB1 : ∀ k : ℕ, B + 1 ≠ -k := fun k hk => hB (k + 1) (by push_cast; linear_combination hk)
  have hB0 : B ≠ 0 := by simpa using hB 0
  have hB10 : B + 1 ≠ 0 := by simpa using hB1 0
  set K : ℂ → ℂ := fun ζ => C₁ * kummerM b B ζ + C₂ * kummerU b B ζ with hK
  set K1 : ℂ → ℂ := fun ζ => C₁ * (b / B * kummerM (b + 1) (B + 1) ζ) +
    C₂ * (-b * kummerU (b + 1) (B + 1) ζ) with hK1
  set K2 : ℂ → ℂ := fun ζ =>
    C₁ * (b / B * ((b + 1) / (B + 1) * kummerM (b + 1 + 1) (B + 1 + 1) ζ)) +
    C₂ * (-b * (-(b + 1) * kummerU (b + 1 + 1) (B + 1 + 1) ζ)) with hK2
  have hKd : ∀ ζ ∈ slitPlane, HasDerivAt K (K1 ζ) ζ := fun ζ hζ =>
    ((hasDerivAt_kummerM_shift hB ζ).const_mul C₁).add
      ((hasDerivAt_kummerU b B hζ).const_mul C₂)
  have hK1d : ∀ ζ ∈ slitPlane, HasDerivAt K1 (K2 ζ) ζ := fun ζ hζ =>
    ((((hasDerivAt_kummerM_shift hB1 ζ).const_mul (b / B))).const_mul C₁).add
      ((((hasDerivAt_kummerU (b + 1) (B + 1) hζ).const_mul (-b))).const_mul C₂)
  have hode : ∀ ζ ∈ slitPlane, ζ * K2 ζ + (B - ζ) * K1 ζ - b * K ζ = 0 := fun ζ hζ => by
    have hm := kummerM_ode_contiguous (a := b) (z := ζ) hB
    have hu := kummerU_ode_contiguous b B ζ (slitPlane_ne_zero hζ)
    have hM : ζ * (b / B * ((b + 1) / (B + 1) * kummerM (b + 2) (B + 2) ζ)) +
        (B - ζ) * (b / B * kummerM (b + 1) (B + 1) ζ) - b * kummerM b B ζ = 0 := by
      field_simp
      linear_combination b * hm
    simp only [hK, hK1, hK2]
    rw [show b + 1 + 1 = b + 2 by ring, show B + 1 + 1 = B + 2 by ring]
    linear_combination C₁ * hM + (C₂ * b) * hu
  have hrep : ∀ x, ε₃ * x ∈ slitPlane → φ x = (ε₃ * x) ^ b * K (ε₃ * x) := by
    intro x hx
    have h0 := slitPlane_ne_zero hx
    simp only [φ, hK, whittakerM, whittakerW]
    rw [show (a + b) / 2 - (a - b + 1) / 2 + 1 / 2 = b by ring,
      show 1 / 2 + (a + b) / 2 - (a - b + 1) / 2 = b by ring,
      show 1 + 2 * ((a + b) / 2) = B by rw [hBdef]; ring,
      show (a + b) / 2 + 1 / 2 = b + (a - b + 1) / 2 by ring,
      show 1 / 2 + (a + b) / 2 = b + (a - b + 1) / 2 by ring, cpow_add _ _ h0]
    have hk0 : (ε₃ * x) ^ ((a - b + 1) / 2) ≠ 0 := by
      rw [cpow_def_of_ne_zero h0]; exact exp_ne_zero _
    have hexp : exp (-(ε₃ * x / 2)) * exp (ε₃ * x / 2) = 1 := by
      rw [← exp_add]; ring_nf; simp
    generalize (ε₃ * x) ^ ((a - b + 1) / 2) = P at hk0 ⊢
    field_simp
    linear_combination ((ε₃ * x) ^ b * (C₁ * kummerM b B (ε₃ * x) +
      C₂ * kummerU b B (ε₃ * x))) * hexp
  have hlin : ∀ x : ℂ, HasDerivAt (fun x => ε₃ * x) ε₃ x := fun x => by
    simpa using (hasDerivAt_id x).const_mul ε₃
  set V := {x : ℂ | ε₃ * x ∈ slitPlane} with hV
  have hVo : IsOpen V := isOpen_slitPlane.preimage (continuous_const.mul continuous_id)
  have hzV : z ∈ V := hz
  set T : ℂ → ℂ := fun x => (ε₃ * x) ^ b with hT
  set ψ1 : ℂ → ℂ := fun x => b * T x / (ε₃ * x) * ε₃ * K (ε₃ * x) +
    T x * (K1 (ε₃ * x) * ε₃) with hψ1
  have hTd : ∀ x ∈ V, HasDerivAt T (b * T x / (ε₃ * x) * ε₃) x := fun x hx =>
    (p3b_hasDerivAt_cpow (a := b) hx).comp x (hlin x)
  have hφd : ∀ x ∈ V, HasDerivAt φ (ψ1 x) x := fun x hx => by
    have h1 : HasDerivAt (fun x => T x * K (ε₃ * x)) (ψ1 x) x :=
      ((hTd x hx).mul ((hKd _ hx).comp x (hlin x))).congr_deriv
        (by simp only [hψ1, Function.comp_apply])
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hVo.mem_nhds hx] with y hy
    exact hrep y hy
  have hev : (fun x => -x * deriv φ x / (a * φ x)) =ᶠ[𝓝 z]
      fun x => -x * ψ1 x / (a * φ x) := by
    filter_upwards [hVo.mem_nhds hzV] with x hx
    rw [(hφd x hx).deriv]
  have hζ0 : ε₃ * z ≠ 0 := slitPlane_ne_zero hz
  have hψ1d : HasDerivAt ψ1 ((((b * (b * T z / (ε₃ * z) * ε₃)) * (ε₃ * z) - b * T z * ε₃) /
      (ε₃ * z) ^ 2 * ε₃) * K (ε₃ * z) + b * T z / (ε₃ * z) * ε₃ * (K1 (ε₃ * z) * ε₃) +
      ((b * T z / (ε₃ * z) * ε₃) * (K1 (ε₃ * z) * ε₃) + T z * (K2 (ε₃ * z) * ε₃ * ε₃))) z := by
    have := ((((hTd z hzV).const_mul b).div (hlin z) hζ0).mul_const ε₃).mul
      ((hKd _ hz).comp z (hlin z)) |>.add
      ((hTd z hzV).mul (((hK1d _ hz).comp z (hlin z)).mul_const ε₃))
    exact this.congr_deriv (by simp only [Function.comp_apply, Pi.div_apply])
  refine ((((hasDerivAt_id z).neg.mul hψ1d).div ((hφd z hzV).const_mul a)
    (mul_ne_zero ha hφ0)).congr_of_eventuallyEq hev).congr_deriv ?_
  rw [(hφd z hzV).deriv, hrep z hz]
  rw [hrep z hz] at hφ0
  have hO := hode _ hz
  simp only [hψ1, hT, Pi.mul_apply, Pi.neg_apply, id_eq] at hφ0 ⊢
  have hs0 : (ε₃ * z) ^ b ≠ 0 := left_ne_zero_of_mul hφ0
  generalize (ε₃ * z) ^ b = t at hs0 hφ0 ⊢
  generalize K (ε₃ * z) = k at hφ0 hO ⊢
  generalize K1 (ε₃ * z) = k1 at hO ⊢
  generalize K2 (ε₃ * z) = k2 at hO ⊢
  have hk : k ≠ 0 := right_ne_zero_of_mul hφ0
  have hz0 : z ≠ 0 := right_ne_zero_of_mul hζ0
  have he0 : ε₃ ≠ 0 := left_ne_zero_of_mul hζ0
  field_simp
  rw [hBdef] at hO
  linear_combination (-ε₃ * k * z) * hO

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
  intro φ w z hz1 hzn hzs hφ0
  set F : ℂ → ℂ := ordinaryHypergeometric b (-a) (b + c) with hF
  set G : ℂ → ℂ := ordinaryHypergeometric (1 - a - b - c) (1 - c) (2 - b - c) with hG
  set Ω := {ζ : ℂ | ‖ζ‖ < 1} ∩ slitPlane with hΩ
  have hΩo : IsOpen Ω := (isOpen_lt continuous_norm continuous_const).inter isOpen_slitPlane
  have hne1 : ∀ ζ ∈ Ω, ζ ≠ 1 := fun ζ hζ h => by
    have h' : ‖ζ‖ < 1 := hζ.1
    simp [h] at h'
  have hFd : ∀ ζ ∈ Ω, DifferentiableAt ℂ F ζ := fun ζ hζ =>
    (DLMF.Hypergeometric.hasDerivAt_ordinaryHypergeometric hbc hζ.1).differentiableAt
  have hGd : ∀ ζ ∈ Ω, DifferentiableAt ℂ G ζ := fun ζ hζ =>
    (DLMF.Hypergeometric.hasDerivAt_ordinaryHypergeometric hbc' hζ.1).differentiableAt
  set ζ0 := 1 / (1 - z) with hζ0
  have hζΩ : ζ0 ∈ Ω := ⟨hzn, hzs⟩
  set φ1 : ℂ → ℂ := fun ζ => C₁ * deriv F ζ + C₂ * ((1 - b - c) * ζ ^ (1 - b - c) / ζ * G ζ +
    ζ ^ (1 - b - c) * deriv G ζ) with hφ1
  have hφd : ∀ ζ ∈ Ω, HasDerivAt φ (φ1 ζ) ζ := fun ζ hζ => by
    have := ((hFd ζ hζ).hasDerivAt.const_mul C₁).add
      (((p3b_hasDerivAt_cpow (a := 1 - b - c) hζ.2).const_mul C₂).mul (hGd ζ hζ).hasDerivAt)
    exact this.congr_deriv (by simp only [hφ1]; ring)
  have hζ00 : ζ0 ≠ 0 := slitPlane_ne_zero hzs
  have hζ01 : ζ0 ≠ 1 := hne1 _ hζΩ
  have hoF := DLMF.Hypergeometric.ordinaryHypergeometric_ode (a := b) (b := -a) hbc hzn hζ00 hζ01
  have hoG := DLMF.Hypergeometric.ordinaryHypergeometric_ode (a := 1 - a - b - c) (b := 1 - c)
    hbc' hzn hζ00 hζ01
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hoF hoG
  have hsd := p3b_hasDerivAt_cpow (a := 1 - b - c) hzs
  have hA := ((hsd.const_mul (1 - b - c)).div (hasDerivAt_id ζ0) hζ00).mul (hGd ζ0 hζΩ).hasDerivAt
  have hB := hsd.mul (p3b_hasDerivAt_deriv_open hΩo hGd hζΩ)
  have hφ1raw := ((p3b_hasDerivAt_deriv_open hΩo hFd hζΩ).const_mul C₁).add
    ((hA.add hB).const_mul C₂)
  have hφ1d : HasDerivAt φ1 (-((b + c) - (b - a + 1) * ζ0) / (ζ0 * (1 - ζ0)) * φ1 ζ0 +
      (-a * b) / (ζ0 * (1 - ζ0)) * φ ζ0) ζ0 := by
    refine hφ1raw.congr_deriv ?_
    have hs0 : ζ0 ^ (1 - b - c) ≠ 0 := by
      rw [cpow_def_of_ne_zero hζ00]; exact exp_ne_zero _
    have h1 : (1 : ℂ) - ζ0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ01)
    simp only [hφ1, φ, id, Pi.div_apply]
    rw [← hF, ← hG]
    generalize ζ0 ^ (1 - b - c) = S at hs0 ⊢
    generalize deriv (deriv F) ζ0 = F2 at hoF ⊢
    generalize deriv (deriv G) ζ0 = G2 at hoG ⊢
    generalize deriv F ζ0 = F1 at hoF ⊢
    generalize deriv G ζ0 = G1 at hoG ⊢
    rw [← hF] at hoF; rw [← hG] at hoG
    generalize F ζ0 = F0 at hoF ⊢
    generalize G ζ0 = G0 at hoG ⊢
    field_simp
    linear_combination (C₁ * ζ0) * hoF + (C₂ * S * ζ0) * hoG
  have hL : HasDerivAt (fun ζ => φ1 ζ / φ ζ)
      (-((b + c) - (b - a + 1) * ζ0) / (ζ0 * (1 - ζ0)) * (φ1 ζ0 / φ ζ0) +
        (-a * b) / (ζ0 * (1 - ζ0)) - (φ1 ζ0 / φ ζ0) ^ 2) ζ0 :=
    (hφ1d.div (hφd ζ0 hζΩ) hφ0).congr_deriv (by field_simp)
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hζd : HasDerivAt (fun z : ℂ => 1 / (1 - z)) (1 / (1 - z) ^ 2) z := by
    have := (hasDerivAt_const z (1 : ℂ)).div ((hasDerivAt_id z).const_sub 1) h1z
    exact this.congr_deriv (by simp)
  have hcont : ContinuousAt (fun z : ℂ => 1 / (1 - z)) z := hζd.continuousAt
  have hev : w =ᶠ[𝓝 z] fun z => (1 / (1 - z) - 1) * (φ1 (1 / (1 - z)) / φ (1 / (1 - z))) / a := by
    filter_upwards [hcont.preimage_mem_nhds (hΩo.mem_nhds hζΩ)] with x hx
    simp only [w]
    rw [(hφd _ hx).deriv]
    ring_nf
  have hwz : w z = (ζ0 - 1) * (φ1 ζ0 / φ ζ0) / a := by
    change (ζ0 - 1) * deriv φ ζ0 / (a * φ ζ0) = _
    rw [(hφd _ hζΩ).deriv]; ring_nf
  refine ((((hζd.sub_const 1).mul (hL.comp z hζd)).div_const a).congr_of_eventuallyEq
    hev).congr_deriv ?_
  rw [hwz]
  simp only [Function.comp_apply]
  rw [← hζ0]
  generalize φ1 ζ0 / φ ζ0 = L
  have hz0 : z ≠ 0 := by
    intro h; apply hζ01; rw [hζ0, h]; norm_num
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [hζ0]
  have e : (1 : ℂ) / (1 - z) - 1 = z / (1 - z) := by field_simp; ring_nf
  have e2 : (1 : ℂ) - 1 / (1 - z) = -z / (1 - z) := by field_simp; ring_nf
  rw [e, e2]
  field_simp
  ring

/-- A holomorphic function that is real-valued near a point has zero derivative there. -/
lemma p3b_deriv_eq_zero_of_im_eq_zero {r : ℂ → ℂ} {d z₀ : ℂ} (hr : HasDerivAt r d z₀)
    (him : ∀ᶠ z in 𝓝 z₀, (r z).im = 0) : d = 0 := by
  have key : ∀ c : ℂ, c ≠ 0 → (d * c).im = 0 := by
    intro c hc
    have h1 : HasDerivAt (fun t : ℝ => r (z₀ + (t : ℂ) * c)) (d * c) 0 := by
      have hl : HasDerivAt (fun t : ℝ => z₀ + (t : ℂ) * c) c 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const c
        simpa using this.const_add z₀
      have hr' : HasDerivAt r d (z₀ + ((0 : ℝ) : ℂ) * c) := by simpa using hr
      exact hr'.comp (0 : ℝ) hl
    have h2 : HasDerivAt (fun t : ℝ => (r (z₀ + (t : ℂ) * c)).im) (d * c).im 0 := by
      have := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt (0 : ℝ) h1
      convert this using 1 <;> rfl
    have hcont : Tendsto (fun t : ℝ => z₀ + (t : ℂ) * c) (𝓝 0) (𝓝 z₀) := by
      have : Continuous (fun t : ℝ => z₀ + (t : ℂ) * c) := by fun_prop
      simpa using this.tendsto 0
    have hev : (fun t : ℝ => (r (z₀ + (t : ℂ) * c)).im) =ᶠ[𝓝 0] fun _ => (0 : ℝ) :=
      hcont.eventually him
    exact h2.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev)
  have h1 := key 1 one_ne_zero
  have h2 := key I I_ne_zero
  simp at h1 h2
  exact Complex.ext h2 h1

/-- The stated relation follows from the given hypotheses: `False`. -/
lemma p3b_ratio_not_real {ψ₁ ψ₂ : ℂ → ℂ} {z₀ : ℂ} (h₁ : DifferentiableAt ℂ ψ₁ z₀)
    (h₂ : DifferentiableAt ℂ ψ₂ z₀) (hne : ψ₂ z₀ ≠ 0)
    (hW : ψ₁ z₀ * deriv ψ₂ z₀ - ψ₂ z₀ * deriv ψ₁ z₀ ≠ 0)
    (him : ∀ᶠ z in 𝓝 z₀, (ψ₁ z * (starRingEnd ℂ) (ψ₂ z)).im = 0) : False := by
  have hd : HasDerivAt (fun z => ψ₁ z / ψ₂ z)
      ((deriv ψ₁ z₀ * ψ₂ z₀ - ψ₁ z₀ * deriv ψ₂ z₀) / ψ₂ z₀ ^ 2) z₀ :=
    h₁.hasDerivAt.div h₂.hasDerivAt hne
  have hev : ∀ᶠ z in 𝓝 z₀, ψ₂ z ≠ 0 := h₂.continuousAt.eventually_ne hne
  have h0 := p3b_deriv_eq_zero_of_im_eq_zero hd (by
    filter_upwards [him, hev] with z hz hz2
    have hn : (Complex.normSq (ψ₂ z) : ℂ) ≠ 0 := by
      exact_mod_cast (Complex.normSq_pos.2 hz2).ne'
    have : ψ₁ z / ψ₂ z = ψ₁ z * (starRingEnd ℂ) (ψ₂ z) / (Complex.normSq (ψ₂ z) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      field_simp [hz2, (map_ne_zero (starRingEnd ℂ)).2 hz2]
    rw [this, Complex.div_ofReal_im, hz, zero_div])
  rw [div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact hW (by linear_combination -h0)
  · exact hne (pow_eq_zero_iff two_ne_zero |>.1 h0)

/-- An entire function with two `ℝ`-independent periods is bounded. -/
lemma p3b_bounded_of_periods {f : ℂ → ℂ} {ω₁ ω₂ : ℂ} (hf : Continuous f)
    (hD : (ω₁ * (starRingEnd ℂ) ω₂).im ≠ 0)
    (h1 : Function.Periodic f ω₁) (h2 : Function.Periodic f ω₂) :
    Bornology.IsBounded (range f) := by
  set K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) * ω₁ + (p.2 : ℂ) * ω₂) '' (Icc 0 1 ×ˢ Icc 0 1)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  refine (hK.image hf).isBounded.subset ?_
  rintro _ ⟨u, rfl⟩
  set D := (ω₁ * (starRingEnd ℂ) ω₂).im
  set a : ℝ := (u * (starRingEnd ℂ) ω₂).im / D
  set b : ℝ := (ω₁ * (starRingEnd ℂ) u).im / D
  have hu : u = (a : ℂ) * ω₁ + (b : ℂ) * ω₂ := by
    have hD' : -(ω₂.im * ω₁.re) + ω₂.re * ω₁.im ≠ 0 := by
      intro h; apply hD; simp only [D, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      linarith
    apply Complex.ext <;>
      simp only [a, b, D, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im] <;>
      field_simp <;> ring
  refine ⟨_, ⟨(Int.fract a, Int.fract b), ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩,
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩, rfl⟩, ?_⟩
  simp only
  rw [hu, Int.fract, Int.fract]
  push_cast
  have : ((a : ℂ) - (⌊a⌋ : ℂ)) * ω₁ + ((b : ℂ) - (⌊b⌋ : ℂ)) * ω₂ =
      (a : ℂ) * ω₁ + (b : ℂ) * ω₂ - (⌊a⌋ : ℤ) * ω₁ - (⌊b⌋ : ℤ) * ω₂ := by ring
  rw [this, h2.sub_int_mul_eq, h1.sub_int_mul_eq]

/-- The hypotheses of the first formulation of `painleveVI_picard` (before its restatement on
2026-10-27) cannot hold at any point of `U`: they make `Λ(·, z)`
entire, while its periods `2φ₁(z)`, `2φ₂(z)` are `ℝ`-independent at some `z ∈ U` (their ratio
is holomorphic with nonzero derivative, so it is not real-valued on an open set). By
Liouville `Λ(·, z)` is then constant, equal to `Λ(0, z) = 0`, contradicting `w(z) ≠ 0`. -/
lemma p3b_painleveVI_picard_hyp_false {Λ : ℂ → ℂ → ℂ} {φ₁ φ₂ : ℂ → ℂ} {C₁ C₂ : ℂ}
    {U : Set ℂ}
    (hU : IsOpen U) (hΛ : ∀ z ∈ U, ∀ u, DifferentiableAt ℂ (Function.uncurry Λ) (u, z))
    (hΛ0 : ∀ z ∈ U, Λ 0 z = 0)
    (hper : ∀ z ∈ U, ∀ u, Λ (u + 2 * φ₁ z) z = Λ u z ∧ Λ (u + 2 * φ₂ z) z = Λ u z)
    (hφ : ∀ z ∈ U, ∀ φ ∈ ({φ₁, φ₂} : Set (ℂ → ℂ)), ContDiffAt ℂ 2 φ z ∧
      z * (1 - z) * iteratedDeriv 2 φ z + (1 - 2 * z) * deriv φ z - φ z / 4 = 0)
    (hind : ∀ z ∈ U, φ₁ z * deriv φ₂ z - φ₂ z * deriv φ₁ z ≠ 0)
    (hw : ∀ z ∈ U, Λ (C₁ * φ₁ z + C₂ * φ₂ z) z ∉ ({0, 1, z} : Set ℂ))
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) : False := by
  have hdiff : ∀ z ∈ U, DifferentiableAt ℂ φ₁ z ∧ DifferentiableAt ℂ φ₂ z := fun z hz =>
    ⟨(hφ z hz φ₁ (by simp)).1.differentiableAt (by norm_num),
      (hφ z hz φ₂ (by simp)).1.differentiableAt (by norm_num)⟩
  obtain ⟨z, hz, hD⟩ : ∃ z ∈ U, (φ₁ z * (starRingEnd ℂ) (φ₂ z)).im ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hev : ∀ᶠ z in 𝓝 z₀, (φ₁ z * (starRingEnd ℂ) (φ₂ z)).im = 0 := by
      filter_upwards [hU.mem_nhds hz₀] with z hz using hcon z hz
    by_cases h2 : φ₂ z₀ = 0
    · have h1 : φ₁ z₀ ≠ 0 := by
        intro h1; apply hind z₀ hz₀; simp [h1, h2]
      refine p3b_ratio_not_real (ψ₁ := φ₂) (ψ₂ := φ₁) (hdiff z₀ hz₀).2 (hdiff z₀ hz₀).1 h1
        ?_ ?_
      · intro h; apply hind z₀ hz₀; linear_combination -h
      · filter_upwards [hev] with z hz
        have : φ₂ z * (starRingEnd ℂ) (φ₁ z) =
            (starRingEnd ℂ) (φ₁ z * (starRingEnd ℂ) (φ₂ z)) := by simp [mul_comm]
        rw [this, Complex.conj_im, hz, neg_zero]
    · exact p3b_ratio_not_real (hdiff z₀ hz₀).1 (hdiff z₀ hz₀).2 h2 (hind z₀ hz₀) hev
  have hfd : Differentiable ℂ (fun u => Λ u z) := fun u => by
    have h : DifferentiableAt ℂ (fun u : ℂ => (u, z)) u :=
      differentiableAt_id.prodMk (differentiableAt_const z)
    have := DifferentiableAt.comp (g := Function.uncurry Λ) u (hΛ z hz u) h
    exact this
  have hD2 : ((2 * φ₁ z) * (starRingEnd ℂ) (2 * φ₂ z)).im ≠ 0 := by
    have : (2 * φ₁ z) * (starRingEnd ℂ) (2 * φ₂ z) =
        ((4 : ℝ) : ℂ) * (φ₁ z * (starRingEnd ℂ) (φ₂ z)) := by
      simp only [map_mul, map_ofNat]; push_cast; ring
    rw [this, Complex.im_ofReal_mul]
    exact mul_ne_zero (by norm_num) hD
  have hb := p3b_bounded_of_periods hfd.continuous hD2 (fun u => (hper z hz u).1)
    (fun u => (hper z hz u).2)
  have hc := hfd.apply_eq_apply_of_bounded hb (C₁ * φ₁ z + C₂ * φ₂ z) 0
  apply hw z hz
  rw [hc, hΛ0 z hz]
  simp

/-- The lattice hypotheses `hL` and `he₁` of `painleveVI_picard` can be met at every
`z ∉ {0, 1}` (pointwise, with `C₁ = C₂ = 0`): a period pair with Picard's invariants
`g₂(z)`, `g₃(z)` exists (their discriminant is `z²(z-1)²/256`), and one of its half-periods `ω₀`
has `℘(ω₀) = -(1 + z)/12`, the root of `4x³ - g₂x - g₃` that corresponds to `Λ = 0`. -/
theorem picard_hypotheses_nonempty {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    ∃ L : PeriodPair, ∃ ω₀ : ℂ, L.g₂ = picardG₂ z ∧ L.g₃ = picardG₃ z ∧ ω₀ ∉ L.lattice ∧
      2 * ω₀ ∈ L.lattice ∧
      DLMF.Weierstrass.weierstrassPInvariants (picardG₂ z) (picardG₃ z) ω₀ = -(1 + z) / 12 := by
  have hΔ : picardG₂ z ^ 3 - 27 * picardG₃ z ^ 2 ≠ 0 := by
    have e : picardG₂ z ^ 3 - 27 * picardG₃ z ^ 2 = z ^ 2 * (z - 1) ^ 2 / 256 := by
      simp only [picardG₂, picardG₃]; ring
    rw [e]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ (sub_ne_zero.2 h1)))
      (by norm_num)
  obtain ⟨L, h2, h3⟩ := DLMF.Weierstrass.exists_periodPair_invariants _ _ hΔ
  set H := DLMF.Weierstrass.halfPeriodsOf L with hH
  have hHL : H.periodPair.lattice = L.lattice := DLMF.Weierstrass.halfPeriodsOf_lattice L
  have hG : ∀ n, H.periodPair.G n = L.G n := by
    intro n
    simp only [PeriodPair.G]
    rw [← (Equiv.subtypeEquivRight (fun x => by rw [hHL]) :
      H.periodPair.lattice ≃ L.lattice).tsum_eq]
    rfl
  have hg2 : H.g₂ = picardG₂ z := by
    simp only [DLMF.Weierstrass.HalfPeriods.g₂, PeriodPair.g₂, hG]; exact h2
  have hg3 : H.g₃ = picardG₃ z := by
    simp only [DLMF.Weierstrass.HalfPeriods.g₃, PeriodPair.g₃, hG]; exact h3
  have hroot :
      (-(1 + z) / 12 - H.e 1) * (-(1 + z) / 12 - H.e 2) * (-(1 + z) / 12 - H.e 3) = 0 := by
    have hc := H.cubic_eq_mul (-(1 + z) / 12)
    rw [hg2, hg3] at hc
    have : 4 * (-(1 + z) / 12) ^ 3 - picardG₂ z * (-(1 + z) / 12) - picardG₃ z = 0 := by
      simp only [picardG₂, picardG₃]; ring
    rw [this] at hc
    linear_combination -hc / 4
  have key : ∃ j ∈ ({1, 2, 3} : Finset ℕ), H.e j = -(1 + z) / 12 := by
    rcases mul_eq_zero.1 hroot with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact ⟨1, by simp, (sub_eq_zero.1 h).symm⟩
      · exact ⟨2, by simp, (sub_eq_zero.1 h).symm⟩
    · exact ⟨3, by simp, (sub_eq_zero.1 h).symm⟩
  obtain ⟨j, hj, hej⟩ := key
  refine ⟨L, H.halfPeriod j, h2, h3, ?_, ?_, ?_⟩
  · rw [← hHL]; exact H.halfPeriod_notMem hj
  · rw [← hHL]; exact H.two_mul_halfPeriod_mem hj
  · rw [← h2, ← h3, DLMF.Weierstrass.weierstrassPInvariants_eq,
      DLMF.Weierstrass.wp23_weierstrassP_eq_of_lattice_eq L H.periodPair hHL.symm]
    exact hej

/-- **Picard's solution of `PVI`** (DLMF 32.10.32–32.10.34). For `z ∉ {0, 1}` let
`Λ(u, z) = 4℘(u + ω₀(z); g₂(z), g₃(z)) + (1 + z)/3` (`picardLambda`), the elliptic function
inverse to `u = ∫_0^Λ dt/√(t(t-1)(t-z))` (32.10.32): `(∂Λ/∂u)² = Λ(Λ-1)(Λ-z)`, `Λ(0, z) = 0`,
where `ω₀(z)` is the half-period with `℘(ω₀) = -(1 + z)/12`. Let `2φ₁(z)`, `2φ₂(z)` be a basis of
the period lattice of `Λ(·, z)` (`hL`), depending on `z` with `φ₁`, `φ₂` solutions of the
hypergeometric equation `z(1-z)φ'' + (1-2z)φ' - φ/4 = 0` (32.10.33, `hφ`). Then
`w(z) = Λ(C₁φ₁(z) + C₂φ₂(z), z)` (32.10.34) solves `PVI` with `(α, β, γ, δ) = (0, 0, 0, 1/2)` on
the open set `U`, provided `w` stays away from the poles of `Λ` and from `{0, 1, z}`.
(DLMF adds that the solution is essentially transcendental in both constants; that statement is
not formalized.)

Restated on 2026-10-27 with user approval: the earlier formulation required `Λ(·, z)` to be
entire, which made its hypotheses contradictory (`p3b_painleveVI_picard_hyp_false`). -/
@[dlmf 32.10.E32, dlmf 32.10.E33, dlmf 32.10.E34]
theorem painleveVI_picard {φ₁ φ₂ ω₀ : ℂ → ℂ} {C₁ C₂ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1)
    (hL : ∀ z ∈ U, ∃ L : PeriodPair, L.ω₁ = 2 * φ₁ z ∧ L.ω₂ = 2 * φ₂ z ∧
      L.g₂ = picardG₂ z ∧ L.g₃ = picardG₃ z ∧ ω₀ z ∉ L.lattice ∧ 2 * ω₀ z ∈ L.lattice ∧
      C₁ * φ₁ z + C₂ * φ₂ z + ω₀ z ∉ L.lattice)
    (he₁ : ∀ z ∈ U, DLMF.Weierstrass.weierstrassPInvariants (picardG₂ z) (picardG₃ z) (ω₀ z) =
      -(1 + z) / 12)
    (hφ : ∀ z ∈ U, ∀ φ ∈ ({φ₁, φ₂} : Set (ℂ → ℂ)), ContDiffAt ℂ 2 φ z ∧
      z * (1 - z) * iteratedDeriv 2 φ z + (1 - 2 * z) * deriv φ z - φ z / 4 = 0)
    (hw : ∀ z ∈ U, picardLambda (ω₀ z) (C₁ * φ₁ z + C₂ * φ₂ z) z ∉ ({0, 1, z} : Set ℂ)) :
    IsPainleveVIOn 0 0 0 (1 / 2)
      (fun z => picardLambda (ω₀ z) (C₁ * φ₁ z + C₂ * φ₂ z) z) U := by
  sorry

end DLMF.Painleve
