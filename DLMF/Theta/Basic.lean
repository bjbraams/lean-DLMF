/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Theta
public import DLMF.QSeries.Identities
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Theta functions: definitions and periodic properties (DLMF §§20.1–20.2)

The project's theta functions are `DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`
(`θⱼ(z|τ)` in DLMF normalization, defined from Mathlib's `jacobiTheta₂`; `q = e^{iπτ}`,
period `π` in `z`). As in Mathlib, they are totalized: for `Im τ ≤ 0` they vanish.

This module adds

* the nome forms `jacobiThetaOneQ … jacobiThetaFourQ` (`θⱼ(z,q)`, DLMF §20.1), defined by their
  Fourier series in `q`. DLMF's convention `q^α = e^{iαπτ}` presupposes a known `τ`; for `θ₁, θ₂`
  we use the principal `q^{1/4}`, so `θⱼ(z, e^{iπτ}) = θⱼ(z|τ)` holds for `-1 < Re τ ≤ 1`
  (`jacobiThetaTwoQ_cexp`), while for `θ₃, θ₄` it holds for every `τ`;
* the theta constants `θⱼ(0|τ)`, `θ₁'(0|τ)` (`…NullTau`, `…DerivNullTau`) and their nome forms;
* the Fourier series 20.2.1–20.2.4 in DLMF's sine/cosine form, the lattice quasi-periodicity
  20.2.6–20.2.9, the half-period translations 20.2.10–20.2.14 and the `z`-zeros of §20.2(iv).

Statements are given in the lattice-parameter form `θⱼ(z|τ)`, which avoids the branch of `q^{1/4}`;
results with `q²`, `iq`, … are stated with `2τ`, `τ + 1/2`, … accordingly.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic DLMF.QSeries Filter Topology

/-! ### Nome forms and theta constants -/

/-- Nome form `θ₃(z,q) = ∑_{n∈ℤ} q^{n²} e^{2inz}` (DLMF 20.2.3, §20.1). For `‖q‖ < 1`. -/
def jacobiThetaThreeQ (z q : ℂ) : ℂ := ∑' n : ℤ, q ^ (n ^ 2) * cexp (2 * I * n * z)

/-- Nome form `θ₄(z,q) = ∑_{n∈ℤ} (-1)ⁿ q^{n²} e^{2inz}` (DLMF 20.2.4, §20.1). For `‖q‖ < 1`. -/
def jacobiThetaFourQ (z q : ℂ) : ℂ :=
  ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n ^ 2) * cexp (2 * I * n * z)

/-- Nome form `θ₂(z,q) = q^{1/4} ∑_{n∈ℤ} q^{n(n+1)} e^{(2n+1)iz}` (DLMF 20.2.2, §20.1), i.e.
`∑ q^{(n+1/2)²} e^{(2n+1)iz}` with the principal fourth root `q^{1/4}`. For `‖q‖ < 1`. -/
def jacobiThetaTwoQ (z q : ℂ) : ℂ :=
  q ^ (1 / 4 : ℂ) * ∑' n : ℤ, q ^ (n * (n + 1)) * cexp ((2 * n + 1) * I * z)

/-- Nome form `θ₁(z,q) = -i q^{1/4} ∑_{n∈ℤ} (-1)ⁿ q^{n(n+1)} e^{(2n+1)iz}` (DLMF 20.2.1, §20.1),
with the principal fourth root `q^{1/4}`. For `‖q‖ < 1`. -/
def jacobiThetaOneQ (z q : ℂ) : ℂ :=
  -I * q ^ (1 / 4 : ℂ) * ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (n + 1)) * cexp ((2 * n + 1) * I * z)

/-- The theta constant `θ₂(0|τ)` (DLMF §20.4). -/
abbrev jacobiThetaTwoNullTau (τ : ℂ) : ℂ := jacobiThetaTwoTau 0 τ

/-- The theta constant `θ₃(0|τ)` (DLMF §20.4); Mathlib's `jacobiTheta τ`. -/
abbrev jacobiThetaThreeNullTau (τ : ℂ) : ℂ := jacobiThetaThreeTau 0 τ

/-- The theta constant `θ₄(0|τ)` (DLMF §20.4). -/
abbrev jacobiThetaFourNullTau (τ : ℂ) : ℂ := jacobiThetaFourTau 0 τ

/-- `θ₁'(0|τ)`, the `z`-derivative of `θ₁(z|τ)` at `z = 0` (DLMF §20.1, §20.4). -/
def jacobiThetaOneDerivNullTau (τ : ℂ) : ℂ := deriv (fun z => jacobiThetaOneTau z τ) 0

/-- The theta constant `θ₂(0,q)` (principal `q^{1/4}`). -/
abbrev jacobiThetaTwoNullQ (q : ℂ) : ℂ := jacobiThetaTwoQ 0 q

/-- The theta constant `θ₃(0,q) = ∑ q^{n²}`. -/
abbrev jacobiThetaThreeNullQ (q : ℂ) : ℂ := jacobiThetaThreeQ 0 q

/-- The theta constant `θ₄(0,q) = ∑ (-1)ⁿ q^{n²}`. -/
abbrev jacobiThetaFourNullQ (q : ℂ) : ℂ := jacobiThetaFourQ 0 q

/-- `θ₁'(0,q)`, the `z`-derivative of `θ₁(z,q)` at `z = 0`. -/
def jacobiThetaOneDerivNullQ (q : ℂ) : ℂ := deriv (fun z => jacobiThetaOneQ z q) 0

/-- Theta functions indexed by `j = 1, 2, 3, 4` (`θⱼ(z|τ)`; other indices give `0`). -/
def jacobiThetaTau (j : ℕ) (z τ : ℂ) : ℂ :=
  match j with
  | 1 => jacobiThetaOneTau z τ
  | 2 => jacobiThetaTwoTau z τ
  | 3 => jacobiThetaThreeTau z τ
  | 4 => jacobiThetaFourTau z τ
  | _ => 0

/-! ### Elementary helpers -/

/-- `(-1)^k = e^{iπk}` for integer `k`. -/
lemma th20_neg_one_zpow (k : ℤ) : (-1 : ℂ) ^ k = cexp (π * I * k) := by
  rw [← exp_pi_mul_I, ← exp_int_mul]; ring_nf

/-- `(e^w)^k = e^{kw}` for integer `k`. -/
lemma th20_exp_zpow (w : ℂ) (k : ℤ) : cexp w ^ k = cexp (k * w) := by
  rw [← exp_int_mul]

/-- The exponential is unchanged by adding `2πi` times an integer. -/
lemma th20_exp_add_int (w : ℂ) (k : ℤ) : cexp (w + k * (2 * π * I)) = cexp w := by
  rw [exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- `e^{iπ/2} = i`. -/
lemma th20_exp_pi_div_two_mul_I : cexp (π / 2 * I) = I := by
  rw [exp_mul_I, cos_pi_div_two, sin_pi_div_two]; ring

/-- `cos(x + nπ) = (-1)ⁿ cos x` for complex `x`. -/
lemma th20_cos_add_nat_mul_pi (x : ℂ) (n : ℕ) : cos (x + n * π) = (-1) ^ n * cos x := by
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, cos_add_pi, ih]; ring

/-! ### Bridges between the lattice and nome forms -/

/-- `θ₃(z, e^{iπτ}) = θ₃(z|τ)` for every `τ`. -/
theorem jacobiThetaThreeQ_cexp (z τ : ℂ) :
    jacobiThetaThreeQ z (cexp (π * I * τ)) = jacobiThetaThreeTau z τ := by
  rw [jacobiThetaThreeQ, jacobiThetaThreeTau_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [th20_exp_zpow, ← exp_add]
  congr 1; push_cast; ring

/-- `θ₄(z, e^{iπτ}) = θ₄(z|τ)` for every `τ`. -/
theorem jacobiThetaFourQ_cexp (z τ : ℂ) :
    jacobiThetaFourQ z (cexp (π * I * τ)) = jacobiThetaFourTau z τ := by
  rw [jacobiThetaFourQ, jacobiThetaFourTau_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [th20_exp_zpow, mul_assoc, ← exp_add]
  congr 2; push_cast; ring

/-- `θ₂(z|τ) = e^{iπτ/4} ∑_{n∈ℤ} q^{n(n+1)} e^{(2n+1)iz}`, `q = e^{iπτ}`, for every `τ`. -/
theorem jacobiThetaTwoTau_eq_tsum (z τ : ℂ) :
    jacobiThetaTwoTau z τ = cexp (π * I * τ / 4) *
      ∑' n : ℤ, cexp (π * I * τ) ^ (n * (n + 1)) * cexp ((2 * n + 1) * I * z) := by
  rw [jacobiThetaTwoTau, jacobiThetaThreeTau_eq_tsum, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [th20_exp_zpow, ← exp_add, ← exp_add, ← exp_add]
  congr 1; push_cast; ring

/-- `θ₁(z|τ) = -i e^{iπτ/4} ∑_{n∈ℤ} (-1)ⁿ q^{n(n+1)} e^{(2n+1)iz}`, `q = e^{iπτ}`, for every `τ`. -/
theorem jacobiThetaOneTau_eq_tsum (z τ : ℂ) :
    jacobiThetaOneTau z τ = -I * cexp (π * I * τ / 4) *
      ∑' n : ℤ, (-1 : ℂ) ^ n * cexp (π * I * τ) ^ (n * (n + 1)) * cexp ((2 * n + 1) * I * z) := by
  rw [jacobiThetaOneTau, jacobiThetaTwoTau_eq_tsum, mul_assoc, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_neg]
  refine tsum_congr fun n => ?_
  rw [th20_neg_one_zpow]
  have key : cexp ((2 * n + 1) * I * (z + π / 2)) =
      cexp (π / 2 * I) * cexp (π * I * n) * cexp ((2 * n + 1) * I * z) := by
    simp only [← exp_add]; congr 1; ring
  rw [key, th20_exp_pi_div_two_mul_I]
  ring

/-- The principal fourth root of the nome: `(e^{iπτ})^{1/4} = e^{iπτ/4}` when `-1 < Re τ ≤ 1`. -/
lemma th20_cexp_cpow_quarter {τ : ℂ} (h1 : -1 < τ.re) (h2 : τ.re ≤ 1) :
    cexp (π * I * τ) ^ (1 / 4 : ℂ) = cexp (π * I * τ / 4) := by
  have him : (π * I * τ).im = π * τ.re := by simp
  rw [cpow_def_of_ne_zero (exp_ne_zero _), log_exp]
  · congr 1; ring
  · rw [him]; nlinarith [Real.pi_pos]
  · rw [him]; nlinarith [Real.pi_pos]

/-- `θ₂(z, e^{iπτ}) = θ₂(z|τ)` when `-1 < Re τ ≤ 1` (principal `q^{1/4}`). -/
theorem jacobiThetaTwoQ_cexp (z : ℂ) {τ : ℂ} (h1 : -1 < τ.re) (h2 : τ.re ≤ 1) :
    jacobiThetaTwoQ z (cexp (π * I * τ)) = jacobiThetaTwoTau z τ := by
  rw [jacobiThetaTwoQ, jacobiThetaTwoTau_eq_tsum, th20_cexp_cpow_quarter h1 h2]

/-- `θ₁(z, e^{iπτ}) = θ₁(z|τ)` when `-1 < Re τ ≤ 1` (principal `q^{1/4}`). -/
theorem jacobiThetaOneQ_cexp (z : ℂ) {τ : ℂ} (h1 : -1 < τ.re) (h2 : τ.re ≤ 1) :
    jacobiThetaOneQ z (cexp (π * I * τ)) = jacobiThetaOneTau z τ := by
  rw [jacobiThetaOneQ, jacobiThetaOneTau_eq_tsum, th20_cexp_cpow_quarter h1 h2]

/-! ### §20.2(i) Fourier series -/

/-- Summability of the `θ₃` series for `Im τ > 0`. -/
lemma th20_hasSum_three (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => cexp (π * I * n ^ 2 * τ + 2 * I * n * z)) (jacobiThetaThreeTau z τ) := by
  have h := hasSum_jacobiTheta₂_term (z / π) hτ
  rw [jacobiThetaThreeTau]
  convert h using 2 with n
  rw [jacobiTheta₂_term]
  congr 1
  field_simp [pi_ne_zero']
  ring

/-- DLMF 20.2.3: `θ₃(z|τ) = 1 + 2∑_{n≥1} q^{n²} cos(2nz)`, `q = e^{iπτ}`, `Im τ > 0`. -/
@[dlmf 20.2.E3]
theorem jacobiThetaThreeTau_hasSum_cos (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => 2 * cexp (π * I * τ * ((n : ℂ) + 1) ^ 2) * cos (2 * ((n : ℂ) + 1) * z))
      (jacobiThetaThreeTau z τ - 1) := by
  have h := (th20_hasSum_three z hτ).nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.sum_range_one, Int.cast_natCast, Int.cast_neg, Nat.cast_zero, Int.cast_zero]
    at h
  convert h using 1
  · funext n
    rw [cos, show 2 * I * ((n + 1 : ℕ) : ℂ) * z = 2 * ((n : ℂ) + 1) * z * I by push_cast; ring,
      show 2 * I * -((n + 1 : ℕ) : ℂ) * z = -(2 * ((n : ℂ) + 1) * z * I) by push_cast; ring]
    simp only [exp_add, neg_sq]
    push_cast
    ring_nf
  · simp

/-- DLMF 20.2.4: `θ₄(z|τ) = 1 + 2∑_{n≥1} (-1)ⁿ q^{n²} cos(2nz)`, `Im τ > 0`. -/
@[dlmf 20.2.E4]
theorem jacobiThetaFourTau_hasSum_cos (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ (n + 1) * cexp (π * I * τ * ((n : ℂ) + 1) ^ 2) *
      cos (2 * ((n : ℂ) + 1) * z)) (jacobiThetaFourTau z τ - 1) := by
  have h := jacobiThetaThreeTau_hasSum_cos (z + π / 2) hτ
  rw [jacobiThetaFourTau]
  convert h using 2 with n
  rw [show 2 * ((n : ℂ) + 1) * (z + π / 2) = 2 * ((n : ℂ) + 1) * z + (n + 1 : ℕ) * π by
    push_cast; ring, th20_cos_add_nat_mul_pi]
  ring

/-- DLMF 20.2.2: `θ₂(z|τ) = 2∑_{n≥0} q^{(n+1/2)²} cos((2n+1)z)`, `q^{(n+1/2)²} = e^{iπτ(n+1/2)²}`,
`Im τ > 0`. -/
@[dlmf 20.2.E2]
theorem jacobiThetaTwoTau_hasSum_cos (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => 2 * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) * cos ((2 * n + 1) * z))
      (jacobiThetaTwoTau z τ) := by
  have h := (th20_hasSum_three (z + π * τ / 2) hτ).mul_left (cexp (π * I * τ / 4 + I * z))
  have h2 := h.nat_add_neg_add_one
  rw [jacobiThetaTwoTau]
  convert h2 using 1
  funext n
  have e1 : cexp (π * I * τ / 4 + I * z) *
      cexp (π * I * ((n : ℤ) : ℂ) ^ 2 * τ + 2 * I * ((n : ℤ) : ℂ) * (z + π * τ / 2)) =
      cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) * cexp ((2 * n + 1) * z * I) := by
    simp only [← exp_add]; congr 1; push_cast; ring
  have e2 : cexp (π * I * τ / 4 + I * z) *
      cexp (π * I * ((-(n + 1) : ℤ) : ℂ) ^ 2 * τ +
        2 * I * ((-(n + 1) : ℤ) : ℂ) * (z + π * τ / 2)) =
      cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) * cexp (-((2 * n + 1) * z) * I) := by
    simp only [← exp_add]; congr 1; push_cast; ring
  rw [e1, e2, cos]
  ring

/-- DLMF 20.2.1: `θ₁(z|τ) = 2∑_{n≥0} (-1)ⁿ q^{(n+1/2)²} sin((2n+1)z)`, `Im τ > 0`. -/
@[dlmf 20.2.E1]
theorem jacobiThetaOneTau_hasSum_sin (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ n * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
      sin ((2 * n + 1) * z)) (jacobiThetaOneTau z τ) := by
  have h := (jacobiThetaTwoTau_hasSum_cos (z + π / 2) hτ).neg
  rw [jacobiThetaOneTau]
  convert h using 2 with n
  rw [show (2 * (n : ℂ) + 1) * (z + π / 2) = (2 * n + 1) * z + π / 2 + n * π by ring,
    th20_cos_add_nat_mul_pi, cos_add_pi_div_two]
  ring

/-! ### §20.2(ii) Periodicity and quasi-periodicity -/

/-- Lattice quasi-periodicity of `θ₃` in exponential form. -/
theorem th20_three_add_lattice (z τ : ℂ) (m n : ℤ) :
    jacobiThetaThreeTau (z + (m + n * τ) * π) τ =
      cexp (-(π * I * τ * n ^ 2)) * cexp (-2 * I * n * z) * jacobiThetaThreeTau z τ := by
  rw [jacobiThetaThreeTau_eq_tsum, jacobiThetaThreeTau_eq_tsum, ← tsum_mul_left,
    ← (Equiv.subRight n).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [Equiv.subRight_apply, ← exp_add]
  rw [exp_eq_exp_iff_exists_int]
  exact ⟨k * m - n * m, by push_cast; ring⟩

/-- DLMF 20.2.8: `θ₃(z + (m + nτ)π|τ) = q^{-n²} e^{-2inz} θ₃(z|τ)`. -/
@[dlmf 20.2.E8]
theorem jacobiThetaThreeTau_add_lattice (z τ : ℂ) (m n : ℤ) :
    jacobiThetaThreeTau (z + (m + n * τ) * π) τ =
      cexp (-(π * I * τ * n ^ 2)) * cexp (-2 * I * n * z) * jacobiThetaThreeTau z τ :=
  th20_three_add_lattice z τ m n

/-- DLMF 20.2.9: `θ₄(z + (m + nτ)π|τ) = (-1)ⁿ q^{-n²} e^{-2inz} θ₄(z|τ)`. -/
@[dlmf 20.2.E9]
theorem jacobiThetaFourTau_add_lattice (z τ : ℂ) (m n : ℤ) :
    jacobiThetaFourTau (z + (m + n * τ) * π) τ =
      (-1 : ℂ) ^ n * cexp (-(π * I * τ * n ^ 2)) * cexp (-2 * I * n * z) *
        jacobiThetaFourTau z τ := by
  rw [jacobiThetaFourTau, jacobiThetaFourTau, show z + (m + n * τ) * π + π / 2 =
    (z + π / 2) + (m + n * τ) * π by ring, th20_three_add_lattice, th20_neg_one_zpow]
  simp only [← exp_add]
  congr 1
  rw [exp_eq_exp_iff_exists_int]
  exact ⟨-n, by push_cast; ring⟩

/-- DLMF 20.2.7: `θ₂(z + (m + nτ)π|τ) = (-1)^m q^{-n²} e^{-2inz} θ₂(z|τ)`. -/
@[dlmf 20.2.E7]
theorem jacobiThetaTwoTau_add_lattice (z τ : ℂ) (m n : ℤ) :
    jacobiThetaTwoTau (z + (m + n * τ) * π) τ =
      (-1 : ℂ) ^ m * cexp (-(π * I * τ * n ^ 2)) * cexp (-2 * I * n * z) *
        jacobiThetaTwoTau z τ := by
  rw [jacobiThetaTwoTau, jacobiThetaTwoTau, show z + (m + n * τ) * π + π * τ / 2 =
    (z + π * τ / 2) + (m + n * τ) * π by ring, th20_three_add_lattice, th20_neg_one_zpow]
  simp only [← mul_assoc, ← exp_add]
  congr 2
  ring

/-- DLMF 20.2.6: `θ₁(z + (m + nτ)π|τ) = (-1)^{m+n} q^{-n²} e^{-2inz} θ₁(z|τ)`. -/
@[dlmf 20.2.E6]
theorem jacobiThetaOneTau_add_lattice (z τ : ℂ) (m n : ℤ) :
    jacobiThetaOneTau (z + (m + n * τ) * π) τ =
      (-1 : ℂ) ^ (m + n) * cexp (-(π * I * τ * n ^ 2)) * cexp (-2 * I * n * z) *
        jacobiThetaOneTau z τ := by
  rw [jacobiThetaOneTau, jacobiThetaOneTau, show z + (m + n * τ) * π + π / 2 =
    (z + π / 2) + (m + n * τ) * π by ring, jacobiThetaTwoTau_add_lattice, th20_neg_one_zpow,
    th20_neg_one_zpow]
  have : cexp (-2 * I * n * (z + π / 2)) = cexp (π * I * n) * cexp (-2 * I * n * z) := by
    rw [← exp_add, exp_eq_exp_iff_exists_int]; exact ⟨-n, by push_cast; ring⟩
  rw [this]
  have e : cexp (π * I * m) * cexp (-(π * I * τ * n ^ 2)) * (cexp (π * I * n) *
      cexp (-2 * I * n * z)) = cexp (π * I * (m + n : ℤ)) * cexp (-(π * I * τ * n ^ 2)) *
      cexp (-2 * I * n * z) := by
    simp only [← exp_add]; congr 1; push_cast; ring
  rw [← e]; ring

/-- DLMF 20.2.5: the lattice points `z_{m,n} = (m + nτ)π`. -/
@[dlmf 20.2.E5]
def latticePoint (m n : ℤ) (τ : ℂ) : ℂ := (m + n * τ) * π

/-- DLMF §20.2(ii): `θ₁` and `θ₂` have period `2π` in `z` (`θ₃`, `θ₄` even have period `π`). -/
@[dlmf 20.2.ii]
theorem jacobiThetaTau_add_two_pi (j : ℕ) (z τ : ℂ) :
    jacobiThetaTau j (z + 2 * π) τ = jacobiThetaTau j z τ := by
  rcases j with _ | _ | _ | _ | _ | j
  · rfl
  · simp only [jacobiThetaTau]
    rw [show z + 2 * π = z + π + π by ring, jacobiThetaOneTau_add_pi, jacobiThetaOneTau_add_pi,
      neg_neg]
  · simp only [jacobiThetaTau]
    rw [show z + 2 * π = z + π + π by ring, jacobiThetaTwoTau_add_pi, jacobiThetaTwoTau_add_pi,
      neg_neg]
  · simp only [jacobiThetaTau]
    rw [show z + 2 * π = z + π + π by ring, jacobiThetaThreeTau_add_pi,
      jacobiThetaThreeTau_add_pi]
  · simp only [jacobiThetaTau]
    rw [show z + 2 * π = z + π + π by ring, jacobiThetaFourTau_add_pi, jacobiThetaFourTau_add_pi]
  · rfl

/-- DLMF §20.2(ii): `θ₃(·|τ)` is entire in `z` for `Im τ > 0`. -/
theorem differentiable_jacobiThetaThreeTau {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (fun z => jacobiThetaThreeTau z τ) := fun z => by
  have := (differentiableAt_jacobiTheta₂_fst (z / π) hτ).comp z
    (differentiableAt_id.div_const (π : ℂ))
  exact this

/-- DLMF §20.2(ii): each `θⱼ(·|τ)` is an entire function of `z` for `Im τ > 0`. -/
@[dlmf 20.2.ii]
theorem differentiable_jacobiThetaTau (j : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (fun z => jacobiThetaTau j z τ) := by
  have h3 := differentiable_jacobiThetaThreeTau hτ
  have h2 : Differentiable ℂ (fun z => jacobiThetaTwoTau z τ) := by
    unfold jacobiThetaTwoTau
    exact ((differentiable_const _).add (differentiable_const _ |>.mul differentiable_id)).cexp.mul
      (h3.comp (differentiable_id.add_const _))
  rcases j with _ | _ | _ | _ | _ | j
  · exact differentiable_const _
  · show Differentiable ℂ (fun z => jacobiThetaOneTau z τ)
    unfold jacobiThetaOneTau
    exact (h2.comp (differentiable_id.add_const _)).neg
  · exact h2
  · exact h3
  · show Differentiable ℂ (fun z => jacobiThetaFourTau z τ)
    unfold jacobiThetaFourTau
    exact h3.comp (differentiable_id.add_const _)
  · exact differentiable_const _

/-- DLMF §20.2(ii): for fixed `z`, `θ₃(z|τ)` and `θ₄(z|τ)` are analytic in `τ` on `Im τ > 0`. -/
@[dlmf 20.2.ii]
theorem differentiableAt_jacobiThetaThreeTau_tau (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (jacobiThetaThreeTau z) τ :=
  differentiableAt_jacobiTheta₂_snd (z / π) hτ

/-- DLMF §20.2(ii): `θ₄(z|·)` is analytic on the upper half-plane. -/
@[dlmf 20.2.ii]
theorem differentiableAt_jacobiThetaFourTau_tau (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (jacobiThetaFourTau z) τ :=
  differentiableAt_jacobiThetaThreeTau_tau (z + π / 2) hτ

/-- `θ₂(z|·)` is analytic on the upper half-plane (used for DLMF §20.2(ii)). -/
theorem differentiableAt_jacobiThetaTwoTau_tau (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (jacobiThetaTwoTau z) τ := by
  have hθ : DifferentiableAt ℂ (fun σ : ℂ => jacobiThetaThreeTau (z + π * σ / 2) σ) τ := by
    have h := (hasFDerivAt_jacobiTheta₂ ((z + π * τ / 2) / π) hτ).differentiableAt
    have hp : DifferentiableAt ℂ (fun σ : ℂ => ((z + π * σ / 2) / π, σ)) τ :=
      (((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id
        |>.div_const _)).div_const _).prodMk differentiableAt_id
    exact DifferentiableAt.comp (𝕜 := ℂ) τ (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2)
      (f := fun σ : ℂ => ((z + π * σ / 2) / π, σ)) h hp
  exact ((((differentiableAt_const _).mul differentiableAt_id).div_const _).add
    (differentiableAt_const _)).cexp.mul hθ

/-- `θ₁(z|·)` is analytic on the upper half-plane (used for DLMF §20.2(ii)). -/
theorem differentiableAt_jacobiThetaOneTau_tau (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (jacobiThetaOneTau z) τ :=
  (differentiableAt_jacobiThetaTwoTau_tau (z + π / 2) hτ).neg

/-! ### Helpers for the quotients `θ₁(z|τ)/sin z`, `θ₂(z|τ)/cos z` -/

/-- Dirichlet kernel `Uₙ(z) = ∑_{k=0}^{2n} e^{2i(k-n)z}`. -/
def thR2_U (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (2 * n + 1), cexp (2 * I * ((k : ℂ) - n) * z)

/-- `sin z · Uₙ(z) = sin((2n+1)z)`. -/
lemma thR2_sin_mul_U (n : ℕ) (z : ℂ) : sin z * thR2_U n z = sin ((2 * n + 1) * z) := by
  set f : ℕ → ℂ := fun k => cexp (I * (2 * k - 2 * n - 1) * z) with hf
  have hterm : ∀ k : ℕ, sin z * cexp (2 * I * ((k : ℂ) - n) * z) = (f (k + 1) - f k) / (2 * I) := by
    intro k
    rw [Complex.sin, hf]
    simp only
    field_simp
    simp only [I_sq, neg_mul, one_mul]
    push_cast
    ring_nf
    simp only [exp_add, exp_sub]
    ring
  rw [thR2_U, Finset.mul_sum]
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_range_sub, Complex.sin, hf]
  simp only
  field_simp
  simp only [I_sq, neg_mul, one_mul]
  push_cast
  ring_nf

/-- `‖Uₙ(z)‖ ≤ (2n+1) e^{2n|Im z|}`. -/
lemma thR2_norm_U_le (n : ℕ) (z : ℂ) :
    ‖thR2_U n z‖ ≤ (2 * n + 1) * Real.exp (2 * n * |z.im|) := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k ∈ Finset.range (2 * n + 1), ‖cexp (2 * I * ((k : ℂ) - n) * z)‖ ≤
      Real.exp (2 * n * |z.im|) := by
    intro k hk
    rw [Complex.norm_exp, Real.exp_le_exp]
    have hk' : (k : ℝ) ≤ 2 * n := by
      have := Finset.mem_range.mp hk; exact_mod_cast Nat.lt_succ_iff.mp this
    have hre : (2 * I * ((k : ℂ) - n) * z).re = -(2 * ((k : ℝ) - n) * z.im) := by
      simp [mul_re, mul_im]
    rw [hre]
    have h1 : |(k : ℝ) - n| ≤ n := by rw [abs_le]; constructor <;> linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    have h2 : -(2 * ((k : ℝ) - n) * z.im) ≤ 2 * |(k : ℝ) - n| * |z.im| := by
      have := neg_abs_le (((k : ℝ) - n) * z.im)
      rw [abs_mul] at this; nlinarith
    nlinarith [abs_nonneg z.im]
  refine (Finset.sum_le_sum this).trans ?_
  simp

/-- Differentiability of `Uₙ`. -/
lemma thR2_differentiable_U (n : ℕ) : Differentiable ℂ (thR2_U n) := by
  unfold thR2_U
  fun_prop

/-- The terms of the series for `θ₁(z|τ)/sin z`. -/
def thR2_term (n : ℕ) (z τ : ℂ) : ℂ :=
  2 * (-1 : ℂ) ^ n * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) * thR2_U n z

/-- Termwise bound. -/
lemma thR2_norm_term_le (n : ℕ) {z τ : ℂ} {R T : ℝ} (hT : 0 ≤ T) (hz : |z.im| ≤ R)
    (hτ : T ≤ τ.im) :
    ‖thR2_term n z τ‖ ≤ 2 * ((2 * n + 1) * Real.exp (-π * T * n ^ 2 + 2 * R * n)) := by
  have he : ‖cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2)‖ = Real.exp (-π * τ.im * (n + 1 / 2) ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    have : ((n : ℂ) + 1 / 2) = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← ofReal_pow, Complex.re_mul_ofReal]
    simp [mul_re, mul_im]
  rw [thR2_term, norm_mul, norm_mul, norm_mul, he]
  simp only [norm_pow, norm_neg, norm_one, one_pow, mul_one, Complex.norm_ofNat]
  have hU := thR2_norm_U_le n z
  have hexp : Real.exp (-π * τ.im * (n + 1 / 2) ^ 2) * Real.exp (2 * n * |z.im|) ≤
      Real.exp (-π * T * n ^ 2 + 2 * R * n) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have h1 : π * T * n ^ 2 ≤ π * τ.im * (n + 1 / 2) ^ 2 := by
      have : (n : ℝ) ^ 2 ≤ (n + 1 / 2) ^ 2 := by nlinarith
      have := mul_le_mul hτ this (sq_nonneg _) (hT.trans hτ)
      nlinarith [Real.pi_pos]
    nlinarith
  calc 2 * Real.exp (-π * τ.im * (n + 1 / 2) ^ 2) * ‖thR2_U n z‖
      ≤ 2 * Real.exp (-π * τ.im * (n + 1 / 2) ^ 2) *
        ((2 * n + 1) * Real.exp (2 * n * |z.im|)) := by gcongr
    _ = 2 * ((2 * n + 1) * (Real.exp (-π * τ.im * (n + 1 / 2) ^ 2) *
        Real.exp (2 * n * |z.im|))) := by ring
    _ ≤ _ := by gcongr

/-- Summability of the majorant. -/
lemma thR2_summable_bound (R : ℝ) {T : ℝ} (hT : 0 < T) :
    Summable (fun n : ℕ => 2 * ((2 * n + 1) * Real.exp (-π * T * n ^ 2 + 2 * R * n))) := by
  have h1 := (summable_pow_mul_jacobiTheta₂_term_bound (R / π) hT 1).comp_injective
    Nat.cast_injective
  have h0 := (summable_pow_mul_jacobiTheta₂_term_bound (R / π) hT 0).comp_injective
    Nat.cast_injective
  refine ((h1.mul_left 2).add h0).mul_left 2 |>.congr fun n => ?_
  simp only [Function.comp_apply, Int.cast_natCast, Nat.abs_cast, pow_one, pow_zero, one_mul]
  have : -π * (T * (n : ℝ) ^ 2 - 2 * (R / π) * n) = -π * T * n ^ 2 + 2 * R * n := by
    field_simp; ring
  rw [this]; ring

/-- Summability of the series for `θ₁(z|τ)/sin z`. -/
lemma thR2_summable_term (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℕ => thR2_term n z τ) :=
  (thR2_summable_bound |z.im| hτ).of_norm_bounded fun n => thR2_norm_term_le n hτ.le le_rfl le_rfl

/-- `sin z · ∑ₙ (2(-1)ⁿ q^{(n+1/2)²} Uₙ(z)) = θ₁(z|τ)`. -/
lemma thR2_sin_mul_tsum (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    sin z * ∑' n : ℕ, thR2_term n z τ = jacobiThetaOneTau z τ := by
  refine ((thR2_summable_term z hτ).hasSum.mul_left (sin z)).unique ?_
  convert jacobiThetaOneTau_hasSum_sin z hτ using 2 with n
  rw [thR2_term, ← thR2_sin_mul_U]
  ring

/-- For `Im τ > 0`, `z ↦ ∑ₙ 2(-1)ⁿ q^{(n+1/2)²} Uₙ(z)` is entire. -/
lemma thR2_differentiable_tsum_z {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (fun z => ∑' n : ℕ, thR2_term n z τ) := by
  intro z₀
  have hU : IsOpen {z : ℂ | |z.im| < |z₀.im| + 1} :=
    isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have h := Complex.differentiableOn_tsum_of_summable_norm (thR2_summable_bound (|z₀.im| + 1) hτ)
    (fun n => by
      simp only [thR2_term]
      exact ((thR2_differentiable_U n).const_mul _).differentiableOn) hU
    (fun n w hw => thR2_norm_term_le n hτ.le (le_of_lt hw) le_rfl)
  exact h.differentiableAt (hU.mem_nhds (by simp))

/-- For fixed `z`, `τ ↦ ∑ₙ 2(-1)ⁿ q^{(n+1/2)²} Uₙ(z)` is analytic on the upper half-plane. -/
lemma thR2_differentiableOn_tsum_tau (z : ℂ) :
    DifferentiableOn ℂ (fun τ => ∑' n : ℕ, thR2_term n z τ) {τ | 0 < τ.im} := by
  intro τ₀ hτ₀
  have hT : 0 < τ₀.im / 2 := half_pos hτ₀
  have hU : IsOpen {τ : ℂ | τ₀.im / 2 < τ.im} := isOpen_lt continuous_const continuous_im
  have h := Complex.differentiableOn_tsum_of_summable_norm (thR2_summable_bound |z.im| hT)
    (fun n => by
      simp only [thR2_term]
      exact Differentiable.differentiableOn (by fun_prop)) hU
    (fun n w hw => thR2_norm_term_le n hT.le le_rfl (le_of_lt hw))
  exact (h.differentiableAt (hU.mem_nhds (by simp only [Set.mem_ofPred_eq]; linarith))
    ).differentiableWithinAt

/-- `θ₁(π/2 - z|τ) = θ₂(z|τ)`. -/
lemma thR2_one_pi_div_two_sub (z τ : ℂ) :
    jacobiThetaOneTau (π / 2 - z) τ = jacobiThetaTwoTau z τ := by
  rw [jacobiThetaOneTau, show (π : ℂ) / 2 - z + π / 2 = -z + π by ring, jacobiThetaTwoTau_add_pi,
    neg_neg, jacobiThetaTwoTau_neg]

/-- DLMF §20.2(ii): `θ₁(z|τ)/sin z` and `θ₂(z|τ)/cos z` are analytic functions of `τ` in the
upper half-plane for every fixed `z`, including the zeros of `sin z`, `cos z`, where the quotients
are understood as their limits. Formally: there is a function `F(z, τ)` that is entire in `z` for
each `τ` with `Im τ > 0`, analytic in `τ` on the upper half-plane for each `z`, and equal to
`θ₁(z|τ)/sin z` wherever `sin z ≠ 0`; continuity in `z` makes `F` unique, so at the zeros of
`sin z` it is the removable-singularity value. Likewise `G` for `θ₂(z|τ)/cos z`.
Restated 2026-10-25 (user decision): the earlier form only asked for some analytic function of
`τ` agreeing with the quotient where `sin z ≠ 0`, which is trivially true at the zeros. -/
@[dlmf 20.2.ii]
theorem jacobiThetaOneTau_div_sin_analytic :
    (∃ F : ℂ → ℂ → ℂ, (∀ τ : ℂ, 0 < τ.im → Differentiable ℂ (fun z => F z τ)) ∧
      (∀ z : ℂ, DifferentiableOn ℂ (F z) {τ | 0 < τ.im}) ∧
      ∀ z τ : ℂ, 0 < τ.im → sin z ≠ 0 → F z τ = jacobiThetaOneTau z τ / sin z) ∧
    (∃ G : ℂ → ℂ → ℂ, (∀ τ : ℂ, 0 < τ.im → Differentiable ℂ (fun z => G z τ)) ∧
      (∀ z : ℂ, DifferentiableOn ℂ (G z) {τ | 0 < τ.im}) ∧
      ∀ z τ : ℂ, 0 < τ.im → cos z ≠ 0 → G z τ = jacobiThetaTwoTau z τ / cos z) := by
  refine ⟨⟨fun z τ => ∑' n : ℕ, thR2_term n z τ, fun τ hτ => thR2_differentiable_tsum_z hτ,
    thR2_differentiableOn_tsum_tau, fun z τ hτ hz => ?_⟩,
    ⟨fun z τ => ∑' n : ℕ, thR2_term n (π / 2 - z) τ, fun τ hτ => ?_,
    fun z => thR2_differentiableOn_tsum_tau (π / 2 - z), fun z τ hτ hz => ?_⟩⟩
  · rw [eq_div_iff hz, mul_comm, thR2_sin_mul_tsum z hτ]
  · exact (thR2_differentiable_tsum_z hτ).comp ((differentiable_const _).sub differentiable_id)
  · rw [← sin_pi_div_two_sub] at hz
    rw [eq_div_iff (by rwa [← sin_pi_div_two_sub]), ← sin_pi_div_two_sub, mul_comm,
      thR2_sin_mul_tsum _ hτ, thR2_one_pi_div_two_sub]

/-- DLMF §20.2(ii): `Im τ = 0` is a natural boundary of `θ₃(z|·)`: no real point has a
neighbourhood on which an analytic function agrees with `θ₃(z|τ)` for `Im τ > 0`. -/
@[dlmf 20.2.ii]
theorem jacobiThetaThreeTau_natural_boundary (z : ℂ) (x : ℝ) :
    ¬ ∃ U : Set ℂ, IsOpen U ∧ (x : ℂ) ∈ U ∧ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      ∀ τ ∈ U, 0 < τ.im → f τ = jacobiThetaThreeTau z τ := by
  sorry

/-- `sin(x + nπ) = (-1)ⁿ sin x` (helper). -/
lemma p20R1_sin_add_nat_mul_pi (x : ℂ) (n : ℕ) : sin (x + n * π) = (-1) ^ n * sin x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show x + ((n + 1 : ℕ) : ℂ) * π = (x + n * π) + π by push_cast; ring, sin_add_pi, ih]
    ring

/-- The derivative of `θ₃(·|τ)` and its sine series (helper). -/
theorem p20R1_three_deriv (u : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun w => jacobiThetaThreeTau w τ) ((1 / π) * jacobiTheta₂' (u / π) τ) u ∧
    HasSum (fun k : ℕ => -(2 * cexp (π * I * τ * ((k : ℂ) + 1) ^ 2) *
        (2 * ((k : ℂ) + 1) * sin (2 * ((k : ℂ) + 1) * u)))) ((1 / π) * jacobiTheta₂' (u / π) τ) := by
  refine ⟨?_, ?_⟩
  · have h := (hasDerivAt_jacobiTheta₂_fst (u / π) hτ).comp u ((hasDerivAt_id u).div_const (π : ℂ))
    exact h.congr_deriv (by ring)
  · have h := ((hasSum_jacobiTheta₂'_term (u / π) hτ).mul_left (1 / (π : ℂ))).nat_add_neg
    have h0 : (1 / (π : ℂ)) * jacobiTheta₂'_term 0 (u / π) τ = 0 := by
      simp [jacobiTheta₂'_term]
    rw [h0, add_zero] at h
    have h' := (hasSum_nat_add_iff' 1).mpr h
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero, h0, add_zero,
      sub_zero] at h'
    convert h' using 1
    funext k
    simp only [jacobiTheta₂'_term, jacobiTheta₂_term, sin]
    push_cast
    have e1 : cexp (2 * π * I * ((k : ℂ) + 1) * (u / π) + π * I * ((k : ℂ) + 1) ^ 2 * τ) =
        cexp (π * I * τ * ((k : ℂ) + 1) ^ 2) * cexp (2 * ((k : ℂ) + 1) * u * I) := by
      rw [← exp_add]; congr 1; field_simp [pi_ne_zero']; ring
    have e2 : cexp (2 * π * I * -((k : ℂ) + 1) * (u / π) + π * I * (-((k : ℂ) + 1)) ^ 2 * τ) =
        cexp (π * I * τ * ((k : ℂ) + 1) ^ 2) * cexp (-(2 * ((k : ℂ) + 1) * u) * I) := by
      rw [← exp_add]; congr 1; field_simp [pi_ne_zero']; ring
    rw [e1, e2]
    field_simp [pi_ne_zero']
    ring


/-- The derivative of `θ₂(·|τ)` and its sine series (helper). -/
theorem p20R1_two_deriv (u : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ D : ℂ, HasDerivAt (fun w => jacobiThetaTwoTau w τ) D u ∧
    HasSum (fun n : ℕ => -(2 * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
        ((2 * n + 1) * sin ((2 * n + 1) * u)))) D := by
  set c := cexp (π * I * τ / 4 + I * u) with hc
  set v := (u + π * τ / 2) / π with hv
  have hE : HasDerivAt (fun w : ℂ => cexp (π * I * τ / 4 + I * w)) (I * c) u := by
    have := (((hasDerivAt_id u).const_mul I).const_add (π * I * τ / 4)).cexp
    simpa [hc, mul_comm] using this
  have hJ : HasDerivAt (fun w : ℂ => jacobiTheta₂ ((w + π * τ / 2) / π) τ)
      (jacobiTheta₂' v τ * (1 / π)) u := by
    have := (hasDerivAt_jacobiTheta₂_fst v hτ).comp u
      (((hasDerivAt_id u).add_const (π * τ / 2)).div_const (π : ℂ))
    simpa [hv, Function.comp_def] using this
  refine ⟨I * c * jacobiTheta₂ v τ + c * (jacobiTheta₂' v τ * (1 / π)), hE.mul hJ, ?_⟩
  have hS := (((hasSum_jacobiTheta₂_term v hτ).mul_left (I * c)).add
    ((hasSum_jacobiTheta₂'_term v hτ).mul_left (c * (1 / (π : ℂ))))).nat_add_neg_add_one
  convert hS using 1
  · funext n
    have hm : ∀ m : ℤ, I * c * jacobiTheta₂_term m v τ + c * (1 / π) * jacobiTheta₂'_term m v τ =
        I * (2 * m + 1) * (c * jacobiTheta₂_term m v τ) := fun m => by
      simp only [jacobiTheta₂'_term]; field_simp [pi_ne_zero']; ring
    rw [hm, hm]
    simp only [jacobiTheta₂_term, sin, hc, hv]
    push_cast
    set A := cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2)
    have e1 : cexp (π * I * τ / 4 + I * u) *
        cexp (2 * π * I * n * ((u + π * τ / 2) / π) + π * I * n ^ 2 * τ) =
        A * cexp ((2 * n + 1) * u * I) := by
      simp only [A, ← exp_add]; congr 1; field_simp [pi_ne_zero']; ring
    have e2 : cexp (π * I * τ / 4 + I * u) *
        cexp (2 * π * I * -((n : ℂ) + 1) * ((u + π * τ / 2) / π) + π * I * (-((n : ℂ) + 1)) ^ 2 * τ) =
        A * cexp (-((2 * n + 1) * u) * I) := by
      simp only [A, ← exp_add]; congr 1; field_simp [pi_ne_zero']; ring
    linear_combination (-(I * (2 * n + 1))) * e1 + (I * (2 * n + 1)) * e2
  · ring


/-- DLMF §20.2(i): the expansions of `θⱼ'(z|τ)` obtained by termwise differentiation of
20.2.1–20.2.4 (`Im τ > 0`). -/
@[dlmf 20.2.i]
theorem jacobiThetaTau_deriv_hasSum (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ n * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
        ((2 * n + 1) * cos ((2 * n + 1) * z))) (deriv (fun w => jacobiThetaOneTau w τ) z) ∧
    HasSum (fun n : ℕ => -(2 * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) *
        ((2 * n + 1) * sin ((2 * n + 1) * z)))) (deriv (fun w => jacobiThetaTwoTau w τ) z) ∧
    HasSum (fun n : ℕ => -(2 * cexp (π * I * τ * ((n : ℂ) + 1) ^ 2) *
        (2 * ((n : ℂ) + 1) * sin (2 * ((n : ℂ) + 1) * z))))
      (deriv (fun w => jacobiThetaThreeTau w τ) z) ∧
    HasSum (fun n : ℕ => -(2 * (-1 : ℂ) ^ (n + 1) * cexp (π * I * τ * ((n : ℂ) + 1) ^ 2) *
        (2 * ((n : ℂ) + 1) * sin (2 * ((n : ℂ) + 1) * z))))
      (deriv (fun w => jacobiThetaFourTau w τ) z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨D, hD, hS⟩ := p20R1_two_deriv (z + π / 2) hτ
    have hD1 : HasDerivAt (fun w => jacobiThetaOneTau w τ) (-D) z :=
      (hD.comp_add_const z (π / 2)).neg
    rw [hD1.deriv]
    convert hS.neg using 1
    funext n
    rw [neg_neg, show (2 * (n : ℂ) + 1) * (z + π / 2) = ((2 * n + 1) * z + π / 2) + n * π by ring,
      p20R1_sin_add_nat_mul_pi, sin_add_pi_div_two]
    ring
  · obtain ⟨D, hD, hS⟩ := p20R1_two_deriv z hτ
    rw [hD.deriv]; exact hS
  · obtain ⟨hD, hS⟩ := p20R1_three_deriv z hτ
    rw [hD.deriv]; exact hS
  · obtain ⟨hD, hS⟩ := p20R1_three_deriv (z + π / 2) hτ
    have hD4 : HasDerivAt (fun w => jacobiThetaFourTau w τ) ((1 / π) * jacobiTheta₂' ((z + π / 2) / π) τ) z :=
      hD.comp_add_const z (π / 2)
    rw [hD4.deriv]
    convert hS using 1
    funext n
    rw [show 2 * ((n : ℂ) + 1) * (z + π / 2) = 2 * ((n : ℂ) + 1) * z + ((n + 1 : ℕ) : ℂ) * π by
      push_cast; ring, p20R1_sin_add_nat_mul_pi]
    ring

/-! ### §20.2(iii) Translation of the argument by half-periods -/

/-- DLMF 20.2.10: the multiplier `M(z|τ) = e^{iz + iπτ/4}`. -/
@[dlmf 20.2.E10]
def thetaMultiplierM (z τ : ℂ) : ℂ := cexp (I * z + π * I * τ / 4)

/-- DLMF 20.2.11: `θ₁(z|τ) = -θ₂(z + π/2|τ) = -iMθ₄(z + πτ/2|τ) = -iMθ₃(z + π/2 + πτ/2|τ)`. -/
@[dlmf 20.2.E11]
theorem jacobiThetaOneTau_half_periods (z τ : ℂ) :
    jacobiThetaOneTau z τ = -jacobiThetaTwoTau (z + π / 2) τ ∧
    jacobiThetaOneTau z τ = -I * thetaMultiplierM z τ * jacobiThetaFourTau (z + π * τ / 2) τ ∧
    jacobiThetaOneTau z τ =
      -I * thetaMultiplierM z τ * jacobiThetaThreeTau (z + π / 2 + π * τ / 2) τ := by
  have h3 : jacobiThetaOneTau z τ =
      -I * thetaMultiplierM z τ * jacobiThetaThreeTau (z + π / 2 + π * τ / 2) τ := by
    rw [jacobiThetaOneTau, jacobiThetaTwoTau, thetaMultiplierM,
      show z + π / 2 + π * τ / 2 = z + π * τ / 2 + π / 2 by ring]
    have : cexp (π * I * τ / 4 + I * (z + π / 2)) = I * cexp (I * z + π * I * τ / 4) := by
      rw [show π * I * τ / 4 + I * (z + π / 2) = (I * z + π * I * τ / 4) + π / 2 * I by ring,
        exp_add, show (π / 2 : ℂ) * I = (π / 2 : ℂ) * I from rfl, exp_mul_I]
      simp [cos_pi_div_two, sin_pi_div_two]; ring
    rw [this]
    ring_nf
  refine ⟨rfl, ?_, h3⟩
  rw [h3, jacobiThetaFourTau, show z + π * τ / 2 + π / 2 = z + π / 2 + π * τ / 2 by ring]

/-- DLMF 20.2.12: `θ₂(z|τ) = θ₁(z + π/2|τ) = Mθ₃(z + πτ/2|τ) = Mθ₄(z + π/2 + πτ/2|τ)`. -/
@[dlmf 20.2.E12]
theorem jacobiThetaTwoTau_half_periods (z τ : ℂ) :
    jacobiThetaTwoTau z τ = jacobiThetaOneTau (z + π / 2) τ ∧
    jacobiThetaTwoTau z τ = thetaMultiplierM z τ * jacobiThetaThreeTau (z + π * τ / 2) τ ∧
    jacobiThetaTwoTau z τ =
      thetaMultiplierM z τ * jacobiThetaFourTau (z + π / 2 + π * τ / 2) τ := by
  have h2 : jacobiThetaTwoTau z τ =
      thetaMultiplierM z τ * jacobiThetaThreeTau (z + π * τ / 2) τ := by
    rw [jacobiThetaTwoTau, thetaMultiplierM]; congr 2; ring
  refine ⟨?_, h2, ?_⟩
  · rw [jacobiThetaOneTau, show z + π / 2 + π / 2 = z + π by ring, jacobiThetaTwoTau_add_pi,
      neg_neg]
  · rw [h2, jacobiThetaFourTau, show z + π / 2 + π * τ / 2 + π / 2 = z + π * τ / 2 + π by ring,
      jacobiThetaThreeTau_add_pi]

/-- DLMF 20.2.13: `θ₃(z|τ) = θ₄(z + π/2|τ) = Mθ₂(z + πτ/2|τ) = Mθ₁(z + π/2 + πτ/2|τ)`. -/
@[dlmf 20.2.E13]
theorem jacobiThetaThreeTau_half_periods (z τ : ℂ) :
    jacobiThetaThreeTau z τ = jacobiThetaFourTau (z + π / 2) τ ∧
    jacobiThetaThreeTau z τ = thetaMultiplierM z τ * jacobiThetaTwoTau (z + π * τ / 2) τ ∧
    jacobiThetaThreeTau z τ =
      thetaMultiplierM z τ * jacobiThetaOneTau (z + π / 2 + π * τ / 2) τ := by
  have h2 : jacobiThetaThreeTau z τ =
      thetaMultiplierM z τ * jacobiThetaTwoTau (z + π * τ / 2) τ := by
    rw [jacobiThetaTwoTau, thetaMultiplierM, show z + π * τ / 2 + π * τ / 2 =
      z + (((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * τ) * π by
      push_cast; ring, th20_three_add_lattice]
    have e : cexp (I * z + π * I * τ / 4) * cexp (π * I * τ / 4 + I * (z + π * τ / 2)) *
        cexp (-(π * I * τ * ((1 : ℤ) : ℂ) ^ 2)) * cexp (-2 * I * ((1 : ℤ) : ℂ) * z) = 1 := by
      simp only [← exp_add]; rw [← exp_zero]; congr 1; push_cast; ring
    linear_combination (-jacobiThetaThreeTau z τ) * e
  refine ⟨?_, h2, ?_⟩
  · rw [jacobiThetaFourTau, show z + π / 2 + π / 2 = z + π by ring, jacobiThetaThreeTau_add_pi]
  · rw [h2, jacobiThetaOneTau, show z + π / 2 + π * τ / 2 + π / 2 = z + π * τ / 2 + π by ring,
      jacobiThetaTwoTau_add_pi, neg_neg]

/-- DLMF 20.2.14: `θ₄(z|τ) = θ₃(z + π/2|τ) = -iMθ₁(z + πτ/2|τ) = iMθ₂(z + π/2 + πτ/2|τ)`. -/
@[dlmf 20.2.E14]
theorem jacobiThetaFourTau_half_periods (z τ : ℂ) :
    jacobiThetaFourTau z τ = jacobiThetaThreeTau (z + π / 2) τ ∧
    jacobiThetaFourTau z τ = -I * thetaMultiplierM z τ * jacobiThetaOneTau (z + π * τ / 2) τ ∧
    jacobiThetaFourTau z τ =
      I * thetaMultiplierM z τ * jacobiThetaTwoTau (z + π / 2 + π * τ / 2) τ := by
  have h2 : jacobiThetaFourTau z τ =
      I * thetaMultiplierM z τ * jacobiThetaTwoTau (z + π / 2 + π * τ / 2) τ := by
    have h := (jacobiThetaThreeTau_half_periods (z + π / 2) τ).2.1
    rw [jacobiThetaFourTau, h, thetaMultiplierM, thetaMultiplierM,
      show z + π / 2 + π * τ / 2 = z + π * τ / 2 + π / 2 by ring]
    have : cexp (I * (z + π / 2) + π * I * τ / 4) = I * cexp (I * z + π * I * τ / 4) := by
      rw [show I * (z + π / 2) + π * I * τ / 4 = (I * z + π * I * τ / 4) + π / 2 * I by ring,
        exp_add, exp_mul_I]
      simp [cos_pi_div_two, sin_pi_div_two]; ring
    rw [this]
  refine ⟨rfl, ?_, h2⟩
  rw [h2, jacobiThetaOneTau, show z + π * τ / 2 + π / 2 = z + π / 2 + π * τ / 2 by ring]
  ring_nf

/-! ### Helpers: the triple product in theta form -/

/-- `‖e^{iπτ}‖ < 1` for `Im τ > 0`. -/
lemma th20_norm_nome_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖cexp (π * I * τ)‖ < 1 := by
  rw [norm_exp]
  have : (π * I * τ).re = -(π * τ.im) := by simp
  rw [this]
  calc Real.exp (-(π * τ.im)) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    _ = 1 := Real.exp_zero

/-- Jacobi's triple product for `θ₃`: with `E = e^{iπτ}`, `Q = E²`, `w = e^{2iz}`,
`θ₃(z|τ) = (Q;Q)_∞ (-Ew;Q)_∞ (-E/w;Q)_∞`. -/
lemma th20_three_eq_qPochhammer (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaThreeTau z τ =
      qPochhammerInf (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) *
        qPochhammerInf (-(cexp (π * I * τ) * cexp (2 * I * z))) (cexp (π * I * τ) ^ 2) *
        qPochhammerInf (-(cexp (π * I * τ) * (cexp (2 * I * z))⁻¹)) (cexp (π * I * τ) ^ 2) := by
  set E := cexp (π * I * τ) with hE
  set w := cexp (2 * I * z) with hw
  have hEne : E ≠ 0 := exp_ne_zero _
  have hwne : w ≠ 0 := exp_ne_zero _
  have hQn : ‖E ^ 2‖ < 1 := by
    rw [norm_pow]
    have h := th20_norm_nome_lt_one hτ
    nlinarith [norm_nonneg E]
  have hZ : -(E * w) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hEne hwne)
  have hdiv : E ^ 2 / -(E * w) = -(E * w⁻¹) := by field_simp
  have h := DLMF.QSeries.jacobi_triple_product hQn hZ
  rw [hdiv] at h
  rw [h, jacobiThetaThreeTau_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [TripleProduct.cpow_tri, neg_eq_neg_one_mul (E * w), mul_zpow, mul_zpow,
    show (-1 : ℂ) ^ n * (E ^ 2) ^ TripleProduct.tri n * ((-1) ^ n * (E ^ n * w ^ n)) =
      ((-1) * (-1) : ℂ) ^ n * ((E ^ 2) ^ TripleProduct.tri n * E ^ n * w ^ n) by
        rw [mul_zpow]; ring,
    show ((-1 : ℂ) * -1) = 1 by norm_num, one_zpow, one_mul]
  have ht : ((TripleProduct.tri n : ℤ) : ℂ) * 2 = n * (n - 1) := by
    exact_mod_cast TripleProduct.tri_mul_two n
  have hsq : cexp (π * I * τ) ^ 2 = cexp (2 * (π * I * τ)) := by
    rw [← exp_nat_mul]; norm_num
  rw [hE, hw, hsq, th20_exp_zpow, th20_exp_zpow, th20_exp_zpow, ← exp_add, ← exp_add]
  congr 1
  linear_combination (-(π * I * τ)) * ht

/-- A `q`-Pochhammer product with a vanishing factor vanishes. -/
lemma th20_qPochhammerInf_eq_zero {a q : ℂ} (hq : ‖q‖ < 1) {k : ℕ} (hk : 1 - a * q ^ k = 0) :
    qPochhammerInf a q = 0 := by
  have ht := tendsto_qPochhammer (w := a) hq
  have hev : ∀ᶠ n in atTop, qPochhammer a q n = 0 := by
    filter_upwards [eventually_gt_atTop k] with n hn
    rw [qPochhammer_eq_prod]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hn) hk
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))

/-- The `q`-Pochhammer product vanishes exactly when one of its factors does (`|q| < 1`). -/
lemma th20_qPochhammerInf_eq_zero_iff {a q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf a q = 0 ↔ ∃ k : ℕ, 1 - a * q ^ k = 0 := by
  constructor
  · intro h
    by_contra hne
    exact qPochhammerInf_ne_zero hq (fun n hn => hne ⟨n, hn⟩) h
  · rintro ⟨k, hk⟩
    exact th20_qPochhammerInf_eq_zero hq hk

/-- Transport of `HasProd` along a pointwise equality of factors. -/
lemma th20_hasProd_congr {f g : ℕ → ℂ} {a : ℂ} (h : HasProd f a) (hfg : ∀ k, f k = g k) :
    HasProd g a := by
  have : f = g := funext hfg
  exact this ▸ h

/-- `e^{2iz} + e^{-2iz} = 2 cos 2z`. -/
lemma th20_exp_add_inv (z : ℂ) : cexp (2 * I * z) + (cexp (2 * I * z))⁻¹ = 2 * cos (2 * z) := by
  rw [← exp_neg, cos, show 2 * z * I = 2 * I * z by ring, show -(2 * z) * I = -(2 * I * z) by ring]
  ring

/-- `‖e^{2πiτ}‖ < 1` in the form `‖(e^{iπτ})²‖ < 1`. -/
lemma th20_norm_nome_sq_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖cexp (π * I * τ) ^ 2‖ < 1 := by
  rw [norm_pow]
  have h := th20_norm_nome_lt_one hτ
  nlinarith [norm_nonneg (cexp (π * I * τ))]

/-! ### §20.2(iv) `z`-zeros -/

/-- DLMF §20.2(iv): the lattice points `(m + nτ)π` are zeros of `θ₁(z|τ)` (for every `τ`). -/
theorem jacobiThetaOneTau_lattice_eq_zero (τ : ℂ) (m n : ℤ) :
    jacobiThetaOneTau ((m + n * τ) * π) τ = 0 := by
  have h0 : jacobiThetaOneTau 0 τ = 0 := by
    have := jacobiThetaOneTau_neg 0 τ
    rw [neg_zero] at this
    exact CharZero.eq_neg_self_iff.mp this
  have := jacobiThetaOneTau_add_lattice 0 τ m n
  rw [zero_add, h0, mul_zero] at this
  exact this

/-- `1 + e^x = 0` iff `x = iπ + 2πim` for some integer `m`. -/
lemma th20_one_add_exp_eq_zero_iff (x : ℂ) :
    1 + cexp x = 0 ↔ ∃ m : ℤ, x = π * I + m * (2 * π * I) := by
  rw [add_eq_zero_iff_eq_neg', ← exp_pi_mul_I, exp_eq_exp_iff_exists_int]

/-- `2i ≠ 0`. -/
lemma th20_two_mul_I_ne_zero : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero

/-- The zeros of `θ₃(z|τ)` (DLMF §20.2(iv)), from the triple product. -/
lemma th20_three_eq_zero_iff {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiThetaThreeTau z τ = 0 ↔ ∃ m n : ℤ, z = (m + 1 / 2 + (n + 1 / 2) * τ) * π := by
  have hQn := th20_norm_nome_sq_lt_one hτ
  have hA : qPochhammerInf (cexp (π * I * τ) ^ 2) (cexp (π * I * τ) ^ 2) ≠ 0 :=
    qPochhammerInf_ne_zero_of_norm_lt_one hQn hQn
  have hQk : ∀ k : ℕ, (cexp (π * I * τ) ^ 2) ^ k = cexp (k * (2 * (π * I * τ))) := fun k => by
    rw [← exp_nat_mul, ← exp_nat_mul]; push_cast; ring_nf
  rw [th20_three_eq_qPochhammer z hτ]
  simp only [mul_eq_zero, hA, false_or]
  rw [th20_qPochhammerInf_eq_zero_iff hQn, th20_qPochhammerInf_eq_zero_iff hQn]
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · rw [hQk, sub_eq_add_neg, neg_mul, neg_neg, ← exp_add, ← exp_add,
        th20_one_add_exp_eq_zero_iff] at hk
      obtain ⟨m, hm⟩ := hk
      refine ⟨m, -((k : ℤ) + 1), ?_⟩
      apply mul_left_cancel₀ th20_two_mul_I_ne_zero
      push_cast
      linear_combination hm
    · rw [hQk, sub_eq_add_neg, neg_mul, neg_neg, ← exp_neg, ← exp_add, ← exp_add,
        th20_one_add_exp_eq_zero_iff] at hk
      obtain ⟨m, hm⟩ := hk
      refine ⟨-m - 1, k, ?_⟩
      apply mul_left_cancel₀ th20_two_mul_I_ne_zero
      push_cast
      linear_combination -hm
  · rintro ⟨m, n, rfl⟩
    rcases le_or_gt 0 n with hn | hn
    · right
      lift n to ℕ using hn
      refine ⟨n, ?_⟩
      rw [hQk, sub_eq_add_neg, neg_mul, neg_neg, ← exp_neg, ← exp_add, ← exp_add,
        th20_one_add_exp_eq_zero_iff]
      refine ⟨-m - 1, ?_⟩
      push_cast
      ring
    · left
      obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -((k : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
      subst hk
      refine ⟨k, ?_⟩
      rw [hQk, sub_eq_add_neg, neg_mul, neg_neg, ← exp_add, ← exp_add,
        th20_one_add_exp_eq_zero_iff]
      refine ⟨m, ?_⟩
      push_cast
      ring

/-- DLMF §20.2(iv): for `Im τ > 0` the `z`-zeros of `θ₁, θ₂, θ₃, θ₄` are exactly
`(m + nτ)π`, `(m + 1/2 + nτ)π`, `(m + 1/2 + (n + 1/2)τ)π`, `(m + (n + 1/2)τ)π`. -/
@[dlmf 20.2.iv]
theorem jacobiThetaTau_eq_zero_iff {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    (jacobiThetaOneTau z τ = 0 ↔ ∃ m n : ℤ, z = (m + n * τ) * π) ∧
    (jacobiThetaTwoTau z τ = 0 ↔ ∃ m n : ℤ, z = (m + 1 / 2 + n * τ) * π) ∧
    (jacobiThetaThreeTau z τ = 0 ↔ ∃ m n : ℤ, z = (m + 1 / 2 + (n + 1 / 2) * τ) * π) ∧
    (jacobiThetaFourTau z τ = 0 ↔ ∃ m n : ℤ, z = (m + (n + 1 / 2) * τ) * π) := by
  have h3 : ∀ z : ℂ, jacobiThetaThreeTau z τ = 0 ↔
      ∃ m n : ℤ, z = (m + 1 / 2 + (n + 1 / 2) * τ) * π := fun z => th20_three_eq_zero_iff hτ z
  refine ⟨?_, ?_, h3 z, ?_⟩
  · rw [jacobiThetaOneTau, neg_eq_zero, jacobiThetaTwoTau, mul_eq_zero, h3]
    simp only [exp_ne_zero, false_or]
    refine exists₂_congr fun m n => ?_
    constructor <;> intro h <;> linear_combination h
  · rw [jacobiThetaTwoTau, mul_eq_zero, h3]
    simp only [exp_ne_zero, false_or]
    refine exists₂_congr fun m n => ?_
    constructor <;> intro h <;> linear_combination h
  · rw [jacobiThetaFourTau, h3]
    refine exists₂_congr fun m n => ?_
    constructor <;> intro h <;> linear_combination h

/-- A lattice-type point `(a + bτ)π` with real `a, b` vanishes only if `a = b = 0` (`Im τ > 0`). -/
lemma th20_lattice_eq_zero {τ : ℂ} (hτ : 0 < τ.im) {a b : ℝ} (h : 0 = ((a : ℂ) + b * τ) * π) :
    a = 0 ∧ b = 0 := by
  have h' : (a : ℂ) + b * τ = 0 := by
    rcases mul_eq_zero.mp h.symm with h | h
    · exact h
    · exact absurd h pi_ne_zero'
  have him := congrArg Complex.im h'
  have hre := congrArg Complex.re h'
  simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_add, zero_im, add_re, mul_re,
    zero_mul, sub_zero, zero_re] at him hre
  have hb : b = 0 := by
    rw [add_zero] at him
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h hτ.ne'
  subst hb
  simp at hre
  exact ⟨hre, rfl⟩

/-- `θ₂(0|τ), θ₃(0|τ), θ₄(0|τ) ≠ 0` for `Im τ > 0` (from the zeros of §20.2(iv)). -/
theorem jacobiThetaNullTau_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau τ ≠ 0 ∧ jacobiThetaThreeNullTau τ ≠ 0 ∧ jacobiThetaFourNullTau τ ≠ 0 := by
  have hz := jacobiThetaTau_eq_zero_iff hτ 0
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨m, n, hmn⟩ := hz.2.1.mp h
    have := th20_lattice_eq_zero hτ (a := m + 1 / 2) (b := n) (by push_cast; exact hmn)
    have h2 : (2 * m + 1 : ℝ) = 0 := by linarith [this.1]
    exact absurd (by exact_mod_cast h2 : (2 * m + 1 : ℤ) = 0) (by omega)
  · obtain ⟨m, n, hmn⟩ := hz.2.2.1.mp h
    have := th20_lattice_eq_zero hτ (a := m + 1 / 2) (b := n + 1 / 2) (by push_cast; exact hmn)
    have h2 : (2 * m + 1 : ℝ) = 0 := by linarith [this.1]
    exact absurd (by exact_mod_cast h2 : (2 * m + 1 : ℤ) = 0) (by omega)
  · obtain ⟨m, n, hmn⟩ := hz.2.2.2.mp h
    have := th20_lattice_eq_zero hτ (a := m) (b := n + 1 / 2) (by push_cast; exact hmn)
    have h2 : (2 * n + 1 : ℝ) = 0 := by linarith [this.2]
    exact absurd (by exact_mod_cast h2 : (2 * n + 1 : ℤ) = 0) (by omega)

end DLMF.Theta

end
