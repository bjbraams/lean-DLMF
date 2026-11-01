/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic.Definitions
public import DLMF.Elliptic.Basic.ThetaPeriodicity

/-!
# Theta functions: nome forms and Fourier series (DLMF §20.2(i))

The relation between the nome forms `θⱼ(z,q)` and the lattice forms `θⱼ(z|τ)`, and the Fourier
series DLMF 20.2.1–20.2.4 in DLMF's sine/cosine form.

## Main results

* `jacobiThetaThreeQ_cexp`, `jacobiThetaFourQ_cexp`: `θⱼ(z, e^{iπτ}) = θⱼ(z|τ)` for every `τ`.
* `jacobiThetaOneQ_cexp`, `jacobiThetaTwoQ_cexp`: the same for `-1 < Re τ ≤ 1`.
* `jacobiThetaOneTau_eq_tsum`, `jacobiThetaTwoTau_eq_tsum`: the exponential series of `θ₁`,
  `θ₂`.
* `jacobiThetaOneTau_hasSum_sin`, `jacobiThetaTwoTau_hasSum_cos`,
  `jacobiThetaThreeTau_hasSum_cos`, `jacobiThetaFourTau_hasSum_cos`: DLMF 20.2.1–20.2.4.
* `norm_nome_lt_one`, `norm_nome_sq_lt_one`: `|q| < 1` and `|q²| < 1` for `Im τ > 0`.

## Implementation notes

The theta functions are totalized as in Mathlib: for `Im τ ≤ 0` they vanish. Statements are
given in the lattice-parameter form `θⱼ(z|τ)`, which avoids the branch of `q^{1/4}`.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic Filter Topology

/-! ### Elementary helpers -/

/-- `(-1)^k = e^{iπk}` for integer `k`. -/
theorem neg_one_zpow_eq_exp (k : ℤ) : (-1 : ℂ) ^ k = cexp (π * I * k) := by
  rw [← exp_pi_mul_I, ← exp_int_mul]; ring_nf

/-- `(e^w)^k = e^{kw}` for integer `k`. -/
theorem exp_zpow_eq_exp_intCast_mul (w : ℂ) (k : ℤ) : cexp w ^ k = cexp (k * w) := by
  rw [← exp_int_mul]

/-- The exponential is unchanged by adding `2πi` times an integer. -/
private lemma exp_add_int_mul_two_pi_I (w : ℂ) (k : ℤ) : cexp (w + k * (2 * π * I)) = cexp w := by
  rw [exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- `cos(x + nπ) = (-1)ⁿ cos x` for complex `x`. -/
private lemma complex_cos_add_nat_mul_pi (x : ℂ) (n : ℕ) : cos (x + n * π) = (-1) ^ n * cos x := by
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, cos_add_pi, ih]; ring

/-! ### Bridges between the lattice and nome forms -/

/-- `θ₃(z, e^{iπτ}) = θ₃(z|τ)` for every `τ`. -/
theorem jacobiThetaThreeQ_cexp (z τ : ℂ) :
    jacobiThetaThreeQ z (cexp (π * I * τ)) = jacobiThetaThreeTau z τ := by
  rw [jacobiThetaThreeQ, jacobiThetaThreeTau_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [exp_zpow_eq_exp_intCast_mul, ← exp_add]
  congr 1; push_cast; ring

/-- `θ₄(z, e^{iπτ}) = θ₄(z|τ)` for every `τ`. -/
theorem jacobiThetaFourQ_cexp (z τ : ℂ) :
    jacobiThetaFourQ z (cexp (π * I * τ)) = jacobiThetaFourTau z τ := by
  rw [jacobiThetaFourQ, jacobiThetaFourTau_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [exp_zpow_eq_exp_intCast_mul, mul_assoc, ← exp_add]
  congr 2; push_cast; ring

/-- `θ₂(z|τ) = e^{iπτ/4} ∑_{n∈ℤ} q^{n(n+1)} e^{(2n+1)iz}`, `q = e^{iπτ}`, for every `τ`. -/
theorem jacobiThetaTwoTau_eq_tsum (z τ : ℂ) :
    jacobiThetaTwoTau z τ = cexp (π * I * τ / 4) *
      ∑' n : ℤ, cexp (π * I * τ) ^ (n * (n + 1)) * cexp ((2 * n + 1) * I * z) := by
  rw [jacobiThetaTwoTau, jacobiThetaThreeTau_eq_tsum, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [exp_zpow_eq_exp_intCast_mul, ← exp_add, ← exp_add, ← exp_add]
  congr 1; push_cast; ring

/-- `θ₁(z|τ) = -i e^{iπτ/4} ∑_{n∈ℤ} (-1)ⁿ q^{n(n+1)} e^{(2n+1)iz}`, `q = e^{iπτ}`, for every `τ`. -/
theorem jacobiThetaOneTau_eq_tsum (z τ : ℂ) :
    jacobiThetaOneTau z τ = -I * cexp (π * I * τ / 4) *
      ∑' n : ℤ, (-1 : ℂ) ^ n * cexp (π * I * τ) ^ (n * (n + 1)) * cexp ((2 * n + 1) * I * z) := by
  rw [jacobiThetaOneTau, jacobiThetaTwoTau_eq_tsum, mul_assoc, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_neg]
  refine tsum_congr fun n => ?_
  rw [neg_one_zpow_eq_exp]
  have key : cexp ((2 * n + 1) * I * (z + π / 2)) =
      cexp (π / 2 * I) * cexp (π * I * n) * cexp ((2 * n + 1) * I * z) := by
    simp only [← exp_add]; congr 1; ring
  rw [key, Complex.exp_pi_div_two_mul_I]
  ring

/-- The principal fourth root of the nome: `(e^{iπτ})^{1/4} = e^{iπτ/4}` when `-1 < Re τ ≤ 1`. -/
private lemma exp_pi_I_mul_cpow_quarter {τ : ℂ} (h1 : -1 < τ.re) (h2 : τ.re ≤ 1) :
    cexp (π * I * τ) ^ (1 / 4 : ℂ) = cexp (π * I * τ / 4) := by
  have him : (π * I * τ).im = π * τ.re := by simp
  rw [cpow_def_of_ne_zero (exp_ne_zero _), log_exp]
  · congr 1; ring
  · rw [him]; nlinarith [Real.pi_pos]
  · rw [him]; nlinarith [Real.pi_pos]

/-- `θ₂(z, e^{iπτ}) = θ₂(z|τ)` when `-1 < Re τ ≤ 1` (principal `q^{1/4}`). -/
theorem jacobiThetaTwoQ_cexp (z : ℂ) {τ : ℂ} (h1 : -1 < τ.re) (h2 : τ.re ≤ 1) :
    jacobiThetaTwoQ z (cexp (π * I * τ)) = jacobiThetaTwoTau z τ := by
  rw [jacobiThetaTwoQ, jacobiThetaTwoTau_eq_tsum, exp_pi_I_mul_cpow_quarter h1 h2]

/-- `θ₁(z, e^{iπτ}) = θ₁(z|τ)` when `-1 < Re τ ≤ 1` (principal `q^{1/4}`). -/
theorem jacobiThetaOneQ_cexp (z : ℂ) {τ : ℂ} (h1 : -1 < τ.re) (h2 : τ.re ≤ 1) :
    jacobiThetaOneQ z (cexp (π * I * τ)) = jacobiThetaOneTau z τ := by
  rw [jacobiThetaOneQ, jacobiThetaOneTau_eq_tsum, exp_pi_I_mul_cpow_quarter h1 h2]

/-! ### §20.2(i) Fourier series -/

/-- Summability of the `θ₃` series for `Im τ > 0`. -/
theorem hasSum_jacobiThetaThreeTau (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
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
  have h := (hasSum_jacobiThetaThreeTau z hτ).nat_add_neg
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
    push_cast; ring, complex_cos_add_nat_mul_pi]
  ring

/-- DLMF 20.2.2: `θ₂(z|τ) = 2∑_{n≥0} q^{(n+1/2)²} cos((2n+1)z)`, `q^{(n+1/2)²} = e^{iπτ(n+1/2)²}`,
`Im τ > 0`. -/
@[dlmf 20.2.E2]
theorem jacobiThetaTwoTau_hasSum_cos (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => 2 * cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2) * cos ((2 * n + 1) * z))
      (jacobiThetaTwoTau z τ) := by
  have h := (hasSum_jacobiThetaThreeTau (z + π * τ / 2) hτ).mul_left (cexp (π * I * τ / 4 + I * z))
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
    complex_cos_add_nat_mul_pi, cos_add_pi_div_two]
  ring

/-! ### Norms of the nome -/

/-- `‖e^{iπτ}‖ < 1` for `Im τ > 0`. -/
theorem norm_nome_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖cexp (π * I * τ)‖ < 1 := by
  rw [norm_exp]
  have : (π * I * τ).re = -(π * τ.im) := by simp
  rw [this]
  calc Real.exp (-(π * τ.im)) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    _ = 1 := Real.exp_zero

/-- `‖e^{2πiτ}‖ < 1` in the form `‖(e^{iπτ})²‖ < 1`. -/
theorem norm_nome_sq_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖cexp (π * I * τ) ^ 2‖ < 1 := by
  rw [norm_pow]
  have h := norm_nome_lt_one hτ
  nlinarith [norm_nonneg (cexp (π * I * τ))]

end DLMF.Theta

end
