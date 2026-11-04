/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.AnalyticProperties

/-!
# Jacobian elliptic functions: periods, poles and zeros (DLMF §22.4)

The quarter-period shifts of Table 22.4.3, the periods of Tables 22.4.1–22.4.2, and the zeros
and poles of the twelve Jacobian elliptic functions, in lattice form and in modulus form.

## Main definitions

* `JacobiLetter.swapK`, `JacobiLetter.swapKp`: the letter permutations `s ↔ c, d ↔ n` and
  `s ↔ n, c ↔ d` induced by `z ↦ z + K` and `z ↦ z + iK'`.
* `jacobiLetterMultiplierK`, `jacobiLetterMultiplierKp`: the constant multipliers of the
  normalized theta functions under these shifts.
* `jacobiLetterPointk`: the corner `0, K, K + iK', iK'` of the fundamental cell labelled by a
  letter (DLMF §22.4(ii)).
* `jacobiCongruentk`: the points congruent to `a` modulo the lattice `2mK + 2niK'`.

## Main results

* `jacobiPQOfTau_add_K`, `jacobiPQOfTau_add_iKp`: the quarter-period shifts in the lattice form.
* `jacobiSnOfTau_shift`, …, `jacobiCsOfTau_shift`: Table 22.4.3 in the lattice form.
* `jacobiSn_shift`, `jacobiCn_shift`, `jacobiDn_shift`, …, `jacobiCs_shift`: Table 22.4.3
  for `k ∈ jacobiModulusDomain`.
* `mem_jacobiCongruentk_iff_jacobiThetaOneTau_eq_zero`: the corners of a letter are the zeros
  of its theta function.
* `jacobiPQ_zeros_poles`: the zeros and poles, Tables 22.4.1–22.4.2 and DLMF §22.4(ii).
* `jacobiSn_periodic`, `jacobiCn_periodic`, `jacobiDn_periodic` and the nine companions:
  the periods of Tables 22.4.1–22.4.2.

## Implementation notes

The shifts `z ↦ z + K`, `z ↦ z + iK'` move the theta argument `ζ = πz/(2K)` by `π/2` and
`πτ/2`; on the normalized theta functions `θ_s, θ_c, θ_d, θ_n` they act by letter permutations
with explicit constant multipliers. The modulus form follows from the lattice form through the
inversion 22.2.2. The location and simplicity of the poles and zeros follow from the zeros of
`θ₁` (§20.2(iv)), Jacobi's `θ₁'(0) = θ₂θ₃θ₄(0)` and the half-period shifts, which write each
`θ_p` as a unit times a translate of `θ₁`.
-/

@[expose] public section

open Complex DLMF.Elliptic
open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

/-- The letter permutation `s ↔ c`, `d ↔ n` induced by `z ↦ z + K`. -/
def JacobiLetter.swapK : JacobiLetter → JacobiLetter
  | .s => .c
  | .c => .s
  | .d => .n
  | .n => .d

/-- The letter permutation `s ↔ n`, `c ↔ d` induced by `z ↦ z + iK'`. -/
def JacobiLetter.swapKp : JacobiLetter → JacobiLetter
  | .s => .n
  | .c => .d
  | .d => .c
  | .n => .s

/-- Injectivity of the indicated map: `Function.Injective JacobiLetter.swapK`. -/
theorem JacobiLetter.swapK_injective : Function.Injective JacobiLetter.swapK := by
  intro a b h; cases a <;> cases b <;> simp_all [JacobiLetter.swapK]

/-- Injectivity of the indicated map: `Function.Injective JacobiLetter.swapKp`. -/
theorem JacobiLetter.swapKp_injective : Function.Injective JacobiLetter.swapKp := by
  intro a b h; cases a <;> cases b <;> simp_all [JacobiLetter.swapKp]

/-- `r' = θ₄(0|τ)/θ₃(0|τ)`, a square root of `k'`. -/
def jacobiComodulusRootTau (τ : ℂ) : ℂ := jacobiThetaFourTau 0 τ / jacobiThetaThreeTau 0 τ

/-- `r = θ₂(0|τ)/θ₃(0|τ)`, a square root of `k`. -/
def jacobiModulusRootTau (τ : ℂ) : ℂ := jacobiThetaTwoTau 0 τ / jacobiThetaThreeTau 0 τ

/-- Multipliers of the normalized theta functions under `ζ ↦ ζ + π/2`. -/
def jacobiLetterMultiplierK (τ : ℂ) : JacobiLetter → ℂ
  | .s => (jacobiComodulusRootTau τ)⁻¹
  | .c => -jacobiComodulusRootTau τ
  | .d => jacobiComodulusRootTau τ
  | .n => (jacobiComodulusRootTau τ)⁻¹

/-- Multipliers (up to the common factor `jacobiThetaShiftFactor`) under `ζ ↦ ζ + πτ/2`. -/
def jacobiLetterMultiplierKp (τ : ℂ) : JacobiLetter → ℂ
  | .s => I * (jacobiModulusRootTau τ)⁻¹
  | .c => (jacobiModulusRootTau τ)⁻¹
  | .d => jacobiModulusRootTau τ
  | .n => I * jacobiModulusRootTau τ

/-- Nonvanishing under the stated hypotheses: `jacobiModulusRootTau τ ≠ 0`. -/
private lemma jacobiModulusRootTau_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiModulusRootTau τ ≠ 0 :=
  div_ne_zero (jacobiThetaTwoTau_zero_ne_zero hτ) (jacobiThetaThreeTau_zero_ne_zero hτ)

/-- Nonvanishing under the stated hypotheses: `jacobiComodulusRootTau τ ≠ 0`. -/
private lemma jacobiComodulusRootTau_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiComodulusRootTau τ ≠ 0 :=
  div_ne_zero (jacobiThetaFourTau_zero_ne_zero hτ) (jacobiThetaThreeTau_zero_ne_zero hτ)

/-- Nonvanishing under the stated hypotheses: `jacobiLetterMultiplierK τ p ≠ 0`. -/
theorem jacobiLetterMultiplierK_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) :
    jacobiLetterMultiplierK τ p ≠ 0 := by
  have := jacobiComodulusRootTau_ne_zero hτ
  cases p <;> simp [jacobiLetterMultiplierK, this]

/-- Nonvanishing under the stated hypotheses: `jacobiLetterMultiplierKp τ p ≠ 0`. -/
private lemma jacobiLetterMultiplierKp_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) :
    jacobiLetterMultiplierKp τ p ≠ 0 := by
  have := jacobiModulusRootTau_ne_zero hτ
  cases p <;> simp [jacobiLetterMultiplierKp, this, I_ne_zero]

/-- Identity under the stated parameter and domain assumptions:
`jacobiModulusOfTau τ = jacobiModulusRootTau τ ^ 2`. -/
private lemma jacobiModulusOfTau_eq_sq (τ : ℂ) : jacobiModulusOfTau τ =
    jacobiModulusRootTau τ ^ 2 := by
  rw [jacobiModulusOfTau, jacobiModulusRootTau, div_pow]

/-- Identity under the stated parameter and domain assumptions:
`jacobiComodulusOfTau τ = jacobiComodulusRootTau τ ^ 2`. -/
private lemma jacobiComodulusOfTau_eq_sq (τ : ℂ) : jacobiComodulusOfTau τ =
    jacobiComodulusRootTau τ ^ 2 := by
  rw [jacobiComodulusOfTau, jacobiComodulusRootTau, div_pow]

/-- The normalized theta functions under `ζ ↦ ζ + π/2`. -/
theorem jacobiLetterTheta_add_pi_div_two {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) (ζ : ℂ) :
    jacobiLetterTheta p (ζ + π / 2) τ = jacobiLetterMultiplierK τ p *
        jacobiLetterTheta p.swapK ζ τ := by
  have h2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have h3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have h4 := jacobiThetaFourTau_zero_ne_zero hτ
  cases p <;>
    simp only [jacobiLetterTheta, jacobiLetterMultiplierK, JacobiLetter.swapK,
        jacobiComodulusRootTau,
      jacobiThetaOneTau_add_pi_div_two, jacobiThetaTwoTau_add_pi_div_two,
          jacobiThetaThreeTau_add_pi_div_two,
      jacobiThetaFourTau_add_pi_div_two] <;> field_simp

/-- The normalized theta functions under `ζ ↦ ζ + πτ/2`. -/
private lemma jacobiLetterTheta_add_pi_mul_div_two {τ : ℂ} (hτ : 0 < τ.im)
    (p : JacobiLetter) (ζ : ℂ) :
    jacobiLetterTheta p (ζ + π * τ / 2) τ =
      jacobiThetaShiftFactor ζ τ * jacobiLetterMultiplierKp τ p *
          jacobiLetterTheta p.swapKp ζ τ := by
  have h2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have h3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have h4 := jacobiThetaFourTau_zero_ne_zero hτ
  cases p <;>
    simp only [jacobiLetterTheta, jacobiLetterMultiplierKp, JacobiLetter.swapKp,
        jacobiModulusRootTau,
      jacobiThetaOneTau_add_pi_mul_div_two, jacobiThetaTwoTau_add_pi_mul_div_two,
          jacobiThetaThreeTau_add_pi_mul_div_two,
      jacobiThetaFourTau_add_pi_mul_div_two] <;> field_simp

/-- Glaisher quotients under `ζ ↦ ζ + π/2`. -/
private lemma jacobiGlaisher_add_pi_div_two {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (ζ : ℂ) :
    jacobiGlaisher p q (ζ + π / 2) τ =
      jacobiLetterMultiplierK τ p / jacobiLetterMultiplierK τ q *
          jacobiGlaisher p.swapK q.swapK ζ τ := by
  unfold jacobiGlaisher
  by_cases hpq : p = q
  · subst hpq; simp [div_self (jacobiLetterMultiplierK_ne_zero hτ p)]
  · have : p.swapK ≠ q.swapK := fun h => hpq (JacobiLetter.swapK_injective h)
    simp only [hpq, this, ↓reduceIte]
    rw [jacobiLetterTheta_add_pi_div_two hτ, jacobiLetterTheta_add_pi_div_two hτ, mul_div_mul_comm]

/-- Glaisher quotients under `ζ ↦ ζ + πτ/2`. -/
private lemma jacobiGlaisher_add_pi_mul_div_two {τ : ℂ} (hτ : 0 < τ.im)
    (p q : JacobiLetter) (ζ : ℂ) :
    jacobiGlaisher p q (ζ + π * τ / 2) τ =
      jacobiLetterMultiplierKp τ p / jacobiLetterMultiplierKp τ q *
          jacobiGlaisher p.swapKp q.swapKp ζ τ := by
  unfold jacobiGlaisher
  by_cases hpq : p = q
  · subst hpq; simp [div_self (jacobiLetterMultiplierKp_ne_zero hτ p)]
  · have : p.swapKp ≠ q.swapKp := fun h => hpq (JacobiLetter.swapKp_injective h)
    simp only [hpq, this, ↓reduceIte]
    rw [jacobiLetterTheta_add_pi_mul_div_two hτ, jacobiLetterTheta_add_pi_mul_div_two hτ, mul_assoc,
      mul_assoc, mul_div_mul_left _ _ (jacobiThetaShiftFactor_ne_zero ζ τ), mul_div_mul_comm]

/-- Nonvanishing under the stated hypotheses: `completeEllipticKOfTau τ ≠ 0`. -/
private lemma completeEllipticKOfTau_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    completeEllipticKOfTau τ ≠ 0 := by
  rw [completeEllipticKOfTau]
  exact mul_ne_zero (div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero)
    (pow_ne_zero _ (jacobiThetaThreeTau_zero_ne_zero hτ))

/-- Identity under the stated parameter and domain assumptions:
`jacobiThetaArgumentOfTau (z + completeEllipticKOfTau τ) τ = jacobiThetaArgumentOfTau z τ + π / 2`.
-/
private lemma jacobiThetaArgumentOfTau_add_completeEllipticKOfTau {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiThetaArgumentOfTau (z + completeEllipticKOfTau τ) τ =
        jacobiThetaArgumentOfTau z τ + π / 2 := by
  have := completeEllipticKOfTau_ne_zero hτ
  rw [jacobiThetaArgumentOfTau, jacobiThetaArgumentOfTau]; field_simp

/-- Identity under the stated parameter and domain assumptions: `jacobiThetaArgumentOfTau (z + I *
completeEllipticKPrimeOfTau τ) τ = jacobiThetaArgumentOfTau z τ + π * τ / 2`. -/
private lemma jacobiThetaArgumentOfTau_add_I_mul_completeEllipticKPrimeOfTau {τ : ℂ}
    (hτ : 0 < τ.im) (z : ℂ) :
    jacobiThetaArgumentOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
        jacobiThetaArgumentOfTau z τ + π * τ / 2 := by
  have := completeEllipticKOfTau_ne_zero hτ
  rw [jacobiThetaArgumentOfTau, jacobiThetaArgumentOfTau, completeEllipticKPrimeOfTau]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- `pq(z + K) = (β_p/β_q) · (σp)(σq)(z)` in the lattice form. -/
theorem jacobiPQOfTau_add_K {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQOfTau p q (z + completeEllipticKOfTau τ) τ =
      jacobiLetterMultiplierK τ p / jacobiLetterMultiplierK τ q *
          jacobiPQOfTau p.swapK q.swapK z τ := by
  rw [jacobiPQOfTau, jacobiThetaArgumentOfTau_add_completeEllipticKOfTau hτ,
      jacobiGlaisher_add_pi_div_two hτ, jacobiPQOfTau]

/-- `pq(z + iK') = (β'_p/β'_q) · (σ'p)(σ'q)(z)` in the lattice form. -/
theorem jacobiPQOfTau_add_iKp {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQOfTau p q (z + I * completeEllipticKPrimeOfTau τ) τ =
      jacobiLetterMultiplierKp τ p / jacobiLetterMultiplierKp τ q *
          jacobiPQOfTau p.swapKp q.swapKp z τ := by
  rw [jacobiPQOfTau, jacobiThetaArgumentOfTau_add_I_mul_completeEllipticKPrimeOfTau hτ,
      jacobiGlaisher_add_pi_mul_div_two hτ, jacobiPQOfTau]

/-- Composing the real and imaginary quarter-period shifts of a Glaisher quotient. -/
theorem jacobiPQOfTau_add_K_add_iKp {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQOfTau p q (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      (jacobiLetterMultiplierK τ p / jacobiLetterMultiplierK τ q) *
        (jacobiLetterMultiplierKp τ p.swapK / jacobiLetterMultiplierKp τ q.swapK *
          jacobiPQOfTau p.swapK.swapKp q.swapK.swapKp z τ) := by
  rw [show z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ =
    z + I * completeEllipticKPrimeOfTau τ + completeEllipticKOfTau τ by ring,
    jacobiPQOfTau_add_K hτ, jacobiPQOfTau_add_iKp hτ]

/-- Composing two real quarter-period shifts of a Glaisher quotient. -/
theorem jacobiPQOfTau_add_two_K {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQOfTau p q (z + 2 * completeEllipticKOfTau τ) τ =
      (jacobiLetterMultiplierK τ p / jacobiLetterMultiplierK τ q) *
        (jacobiLetterMultiplierK τ p.swapK / jacobiLetterMultiplierK τ q.swapK *
          jacobiPQOfTau p.swapK.swapK q.swapK.swapK z τ) := by
  rw [show z + 2 * completeEllipticKOfTau τ =
    z + completeEllipticKOfTau τ + completeEllipticKOfTau τ by ring,
    jacobiPQOfTau_add_K hτ, jacobiPQOfTau_add_K hτ]

/-- Composing two imaginary quarter-period shifts of a Glaisher quotient. -/
theorem jacobiPQOfTau_add_two_iKp {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQOfTau p q (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      (jacobiLetterMultiplierKp τ p / jacobiLetterMultiplierKp τ q) *
        (jacobiLetterMultiplierKp τ p.swapKp / jacobiLetterMultiplierKp τ q.swapKp *
          jacobiPQOfTau p.swapKp.swapKp q.swapKp.swapKp z τ) := by
  rw [show z + 2 * (I * completeEllipticKPrimeOfTau τ) =
    z + I * completeEllipticKPrimeOfTau τ + I * completeEllipticKPrimeOfTau τ by ring,
    jacobiPQOfTau_add_iKp hτ, jacobiPQOfTau_add_iKp hτ]

/-- Composing the two full-period translations of a Glaisher quotient. -/
theorem jacobiPQOfTau_add_two_K_add_two_iKp {τ : ℂ} (hτ : 0 < τ.im)
    (p q : JacobiLetter) (z : ℂ) :
    jacobiPQOfTau p q (z + 2 * completeEllipticKOfTau τ + 2 *
        (I * completeEllipticKPrimeOfTau τ)) τ =
      (jacobiLetterMultiplierK τ p / jacobiLetterMultiplierK τ q) *
        (jacobiLetterMultiplierK τ p.swapK / jacobiLetterMultiplierK τ q.swapK *
          ((jacobiLetterMultiplierKp τ p.swapK.swapK / jacobiLetterMultiplierKp τ q.swapK.swapK) *
            (jacobiLetterMultiplierKp τ p.swapK.swapK.swapKp /
              jacobiLetterMultiplierKp τ q.swapK.swapK.swapKp *
              jacobiPQOfTau p.swapK.swapK.swapKp.swapKp q.swapK.swapK.swapKp.swapKp z τ))) := by
  rw [show z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ) =
    z + 2 * (I * completeEllipticKPrimeOfTau τ) + 2 * completeEllipticKOfTau τ by ring,
    jacobiPQOfTau_add_two_K hτ, jacobiPQOfTau_add_two_iKp hτ]

/-- Unfold the twelve lattice-form functions and apply the quarter-period shifts. -/
macro "jacobi_shift_simp " h:term : tactic => `(tactic|
  simp only [jacobiSnOfTau, jacobiCnOfTau, jacobiDnOfTau, jacobiSdOfTau,
      jacobiCdOfTau, jacobiScOfTau,
    jacobiNsOfTau, jacobiNcOfTau, jacobiNdOfTau, jacobiDsOfTau, jacobiDcOfTau, jacobiCsOfTau,
    jacobiPQOfTau_add_K $h, jacobiPQOfTau_add_iKp $h,
    jacobiPQOfTau_add_K_add_iKp $h, jacobiPQOfTau_add_two_K $h,
    jacobiPQOfTau_add_two_iKp $h, jacobiPQOfTau_add_two_K_add_two_iKp $h,
    JacobiLetter.swapK, JacobiLetter.swapKp,
    jacobiLetterMultiplierK, jacobiLetterMultiplierKp, jacobiModulusOfTau_eq_sq,
        jacobiComodulusOfTau_eq_sq])

/-- Close a coefficient identity `a * X = b * X` produced by `jacobi_shift_simp`. -/
macro "jacobi_coef_tac" : tactic => `(tactic|
  ((try field_simp) <;> (try ring_nf) <;> (try simp only [I_sq, I_pow_four]) <;> (try ring_nf)))

/-- Apply the quarter-period shifts and close the resulting coefficient identity. -/
macro "jacobi_shift_close " h:term : tactic => `(tactic|
  (jacobi_shift_simp $h <;> jacobi_coef_tac))

/-- Table 22.4.3, row `sn`, in the lattice form: the shifts of `sn` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiSnOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiSnOfTau (z + completeEllipticKOfTau τ) τ =
      jacobiCdOfTau z τ ∧
    jacobiSnOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      (jacobiModulusOfTau τ)⁻¹ * jacobiDcOfTau z τ ∧
    jacobiSnOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      (jacobiModulusOfTau τ)⁻¹ * jacobiNsOfTau z τ ∧
    jacobiSnOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      -jacobiSnOfTau z τ ∧
    jacobiSnOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiSnOfTau z τ ∧
    jacobiSnOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      jacobiSnOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `cn`, in the lattice form: the shifts of `cn` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiCnOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiCnOfTau (z + completeEllipticKOfTau τ) τ =
      -jacobiComodulusOfTau τ * jacobiSdOfTau z τ ∧
    jacobiCnOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      -(I * jacobiComodulusOfTau τ / jacobiModulusOfTau τ) * jacobiNcOfTau z τ ∧
    jacobiCnOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      -(I / jacobiModulusOfTau τ) * jacobiDsOfTau z τ ∧
    jacobiCnOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      -jacobiCnOfTau z τ ∧
    jacobiCnOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      jacobiCnOfTau z τ ∧
    jacobiCnOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiCnOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `dn`, in the lattice form: the shifts of `dn` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiDnOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiDnOfTau (z + completeEllipticKOfTau τ) τ =
      jacobiComodulusOfTau τ * jacobiNdOfTau z τ ∧
    jacobiDnOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      I * jacobiComodulusOfTau τ * jacobiScOfTau z τ ∧
    jacobiDnOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      -I * jacobiCsOfTau z τ ∧
    jacobiDnOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      jacobiDnOfTau z τ ∧
    jacobiDnOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiDnOfTau z τ ∧
    jacobiDnOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiDnOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `cd`, in the lattice form: the shifts of `cd` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiCdOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiCdOfTau (z + completeEllipticKOfTau τ) τ =
      -jacobiSnOfTau z τ ∧
    jacobiCdOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      -(jacobiModulusOfTau τ)⁻¹ * jacobiNsOfTau z τ ∧
    jacobiCdOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      (jacobiModulusOfTau τ)⁻¹ * jacobiDcOfTau z τ ∧
    jacobiCdOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      -jacobiCdOfTau z τ ∧
    jacobiCdOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiCdOfTau z τ ∧
    jacobiCdOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      jacobiCdOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `sd`, in the lattice form: the shifts of `sd` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiSdOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiSdOfTau (z + completeEllipticKOfTau τ) τ =
      (jacobiComodulusOfTau τ)⁻¹ * jacobiCnOfTau z τ ∧
    jacobiSdOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      -(I / (jacobiModulusOfTau τ * jacobiComodulusOfTau τ)) * jacobiDsOfTau z τ ∧
    jacobiSdOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      (I / jacobiModulusOfTau τ) * jacobiNcOfTau z τ ∧
    jacobiSdOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      -jacobiSdOfTau z τ ∧
    jacobiSdOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      jacobiSdOfTau z τ ∧
    jacobiSdOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiSdOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `nd`, in the lattice form: the shifts of `nd` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiNdOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiNdOfTau (z + completeEllipticKOfTau τ) τ =
      (jacobiComodulusOfTau τ)⁻¹ * jacobiDnOfTau z τ ∧
    jacobiNdOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      -(I / jacobiComodulusOfTau τ) * jacobiCsOfTau z τ ∧
    jacobiNdOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      I * jacobiScOfTau z τ ∧
    jacobiNdOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      jacobiNdOfTau z τ ∧
    jacobiNdOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiNdOfTau z τ ∧
    jacobiNdOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiNdOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `dc`, in the lattice form: the shifts of `dc` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiDcOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiDcOfTau (z + completeEllipticKOfTau τ) τ =
      -jacobiNsOfTau z τ ∧
    jacobiDcOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      -jacobiModulusOfTau τ * jacobiSnOfTau z τ ∧
    jacobiDcOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      jacobiModulusOfTau τ * jacobiCdOfTau z τ ∧
    jacobiDcOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      -jacobiDcOfTau z τ ∧
    jacobiDcOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiDcOfTau z τ ∧
    jacobiDcOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      jacobiDcOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `nc`, in the lattice form: the shifts of `nc` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiNcOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiNcOfTau (z + completeEllipticKOfTau τ) τ =
      -(jacobiComodulusOfTau τ)⁻¹ * jacobiDsOfTau z τ ∧
    jacobiNcOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      (I * jacobiModulusOfTau τ / jacobiComodulusOfTau τ) * jacobiCnOfTau z τ ∧
    jacobiNcOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      I * jacobiModulusOfTau τ * jacobiSdOfTau z τ ∧
    jacobiNcOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      -jacobiNcOfTau z τ ∧
    jacobiNcOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      jacobiNcOfTau z τ ∧
    jacobiNcOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiNcOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `sc`, in the lattice form: the shifts of `sc` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiScOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiScOfTau (z + completeEllipticKOfTau τ) τ =
      -(jacobiComodulusOfTau τ)⁻¹ * jacobiCsOfTau z τ ∧
    jacobiScOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      (I / jacobiComodulusOfTau τ) * jacobiDnOfTau z τ ∧
    jacobiScOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      I * jacobiNdOfTau z τ ∧
    jacobiScOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      jacobiScOfTau z τ ∧
    jacobiScOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiScOfTau z τ ∧
    jacobiScOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiScOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `ns`, in the lattice form: the shifts of `ns` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiNsOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiNsOfTau (z + completeEllipticKOfTau τ) τ =
      jacobiDcOfTau z τ ∧
    jacobiNsOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      jacobiModulusOfTau τ * jacobiCdOfTau z τ ∧
    jacobiNsOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      jacobiModulusOfTau τ * jacobiSnOfTau z τ ∧
    jacobiNsOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      -jacobiNsOfTau z τ ∧
    jacobiNsOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiNsOfTau z τ ∧
    jacobiNsOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      jacobiNsOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `ds`, in the lattice form: the shifts of `ds` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiDsOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiDsOfTau (z + completeEllipticKOfTau τ) τ =
      jacobiComodulusOfTau τ * jacobiNcOfTau z τ ∧
    jacobiDsOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      I * jacobiModulusOfTau τ * jacobiComodulusOfTau τ * jacobiSdOfTau z τ ∧
    jacobiDsOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      -(I * jacobiModulusOfTau τ) * jacobiCnOfTau z τ ∧
    jacobiDsOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      -jacobiDsOfTau z τ ∧
    jacobiDsOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      jacobiDsOfTau z τ ∧
    jacobiDsOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiDsOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `cs`, in the lattice form: the shifts of `cs` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiCsOfTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiCsOfTau (z + completeEllipticKOfTau τ) τ =
      -jacobiComodulusOfTau τ * jacobiScOfTau z τ ∧
    jacobiCsOfTau (z + completeEllipticKOfTau τ + I * completeEllipticKPrimeOfTau τ) τ =
      -(I * jacobiComodulusOfTau τ) * jacobiNdOfTau z τ ∧
    jacobiCsOfTau (z + I * completeEllipticKPrimeOfTau τ) τ =
      -I * jacobiDnOfTau z τ ∧
    jacobiCsOfTau (z + 2 * completeEllipticKOfTau τ) τ =
      jacobiCsOfTau z τ ∧
    jacobiCsOfTau (z + 2 * completeEllipticKOfTau τ + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiCsOfTau z τ ∧
    jacobiCsOfTau (z + 2 * (I * completeEllipticKPrimeOfTau τ)) τ =
      -jacobiCsOfTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- `K(k) ≠ 0` on `jacobiModulusDomain` (from the admitted inversion). -/
theorem completeEllipticK_ne_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    completeEllipticK k ≠ 0 := by
  rw [← (jacobi_inversion_k hk).2.2]
  exact completeEllipticKOfTau_ne_zero (jacobiTau_im_pos hk)

/-- `K'` of the lattice form at `τ = iK'/K` is `K'(k)`. -/
theorem completeEllipticKPrimeOfTau_jacobiTau {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    completeEllipticKPrimeOfTau (jacobiTau k) = completeEllipticKPrime k := by
  have hK := completeEllipticK_ne_zero hk
  rw [completeEllipticKPrimeOfTau, (jacobi_inversion_k hk).2.2, jacobiTau]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- Transfer a lattice-form identity `h` at `τ = jacobiTau k` to the modulus form. -/
macro "jacobi_to_k " hk:term:max h:ident : tactic => `(tactic| (
  obtain ⟨h1, h2, h3⟩ := jacobi_inversion_k $hk
  have hKp := completeEllipticKPrimeOfTau_jacobiTau $hk
  simp only [jacobiSnOfTau, jacobiCnOfTau, jacobiDnOfTau, jacobiSdOfTau,
      jacobiCdOfTau, jacobiScOfTau,
    jacobiNsOfTau, jacobiNcOfTau, jacobiNdOfTau, jacobiDsOfTau, jacobiDcOfTau,
        jacobiCsOfTau] at $h:ident
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiSd, jacobiCd, jacobiSc,
    jacobiNs, jacobiNc, jacobiNd, jacobiDs, jacobiDc, jacobiCs, jacobiPQ_eq_jacobiPQOfTau $hk]
  simp only [h1, h2, h3, hKp] at $h:ident
  exact $h))

/-- Table 22.4.3, row `sn`: the shifts of `sn(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiSn_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSn (z + completeEllipticK k) k =
      jacobiCd z k ∧
    jacobiSn (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      (k)⁻¹ * jacobiDc z k ∧
    jacobiSn (z + I * completeEllipticKPrime k) k =
      (k)⁻¹ * jacobiNs z k ∧
    jacobiSn (z + 2 * completeEllipticK k) k =
      -jacobiSn z k ∧
    jacobiSn (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiSn z k ∧
    jacobiSn (z + 2 * (I * completeEllipticKPrime k)) k =
      jacobiSn z k := by
  have h := jacobiSnOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `cn`: the shifts of `cn(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiCn_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCn (z + completeEllipticK k) k =
      -jacobiComodulus k * jacobiSd z k ∧
    jacobiCn (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      -(I * jacobiComodulus k / k) * jacobiNc z k ∧
    jacobiCn (z + I * completeEllipticKPrime k) k =
      -(I / k) * jacobiDs z k ∧
    jacobiCn (z + 2 * completeEllipticK k) k =
      -jacobiCn z k ∧
    jacobiCn (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      jacobiCn z k ∧
    jacobiCn (z + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiCn z k := by
  have h := jacobiCnOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `dn`: the shifts of `dn(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiDn_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDn (z + completeEllipticK k) k =
      jacobiComodulus k * jacobiNd z k ∧
    jacobiDn (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      I * jacobiComodulus k * jacobiSc z k ∧
    jacobiDn (z + I * completeEllipticKPrime k) k =
      -I * jacobiCs z k ∧
    jacobiDn (z + 2 * completeEllipticK k) k =
      jacobiDn z k ∧
    jacobiDn (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiDn z k ∧
    jacobiDn (z + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiDn z k := by
  have h := jacobiDnOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `cd`: the shifts of `cd(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiCd_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCd (z + completeEllipticK k) k =
      -jacobiSn z k ∧
    jacobiCd (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      -(k)⁻¹ * jacobiNs z k ∧
    jacobiCd (z + I * completeEllipticKPrime k) k =
      (k)⁻¹ * jacobiDc z k ∧
    jacobiCd (z + 2 * completeEllipticK k) k =
      -jacobiCd z k ∧
    jacobiCd (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiCd z k ∧
    jacobiCd (z + 2 * (I * completeEllipticKPrime k)) k =
      jacobiCd z k := by
  have h := jacobiCdOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `sd`: the shifts of `sd(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiSd_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSd (z + completeEllipticK k) k =
      (jacobiComodulus k)⁻¹ * jacobiCn z k ∧
    jacobiSd (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      -(I / (k * jacobiComodulus k)) * jacobiDs z k ∧
    jacobiSd (z + I * completeEllipticKPrime k) k =
      (I / k) * jacobiNc z k ∧
    jacobiSd (z + 2 * completeEllipticK k) k =
      -jacobiSd z k ∧
    jacobiSd (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      jacobiSd z k ∧
    jacobiSd (z + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiSd z k := by
  have h := jacobiSdOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `nd`: the shifts of `nd(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiNd_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNd (z + completeEllipticK k) k =
      (jacobiComodulus k)⁻¹ * jacobiDn z k ∧
    jacobiNd (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      -(I / jacobiComodulus k) * jacobiCs z k ∧
    jacobiNd (z + I * completeEllipticKPrime k) k =
      I * jacobiSc z k ∧
    jacobiNd (z + 2 * completeEllipticK k) k =
      jacobiNd z k ∧
    jacobiNd (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiNd z k ∧
    jacobiNd (z + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiNd z k := by
  have h := jacobiNdOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `dc`: the shifts of `dc(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiDc_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDc (z + completeEllipticK k) k =
      -jacobiNs z k ∧
    jacobiDc (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      -k * jacobiSn z k ∧
    jacobiDc (z + I * completeEllipticKPrime k) k =
      k * jacobiCd z k ∧
    jacobiDc (z + 2 * completeEllipticK k) k =
      -jacobiDc z k ∧
    jacobiDc (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiDc z k ∧
    jacobiDc (z + 2 * (I * completeEllipticKPrime k)) k =
      jacobiDc z k := by
  have h := jacobiDcOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `nc`: the shifts of `nc(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiNc_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNc (z + completeEllipticK k) k =
      -(jacobiComodulus k)⁻¹ * jacobiDs z k ∧
    jacobiNc (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      (I * k / jacobiComodulus k) * jacobiCn z k ∧
    jacobiNc (z + I * completeEllipticKPrime k) k =
      I * k * jacobiSd z k ∧
    jacobiNc (z + 2 * completeEllipticK k) k =
      -jacobiNc z k ∧
    jacobiNc (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      jacobiNc z k ∧
    jacobiNc (z + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiNc z k := by
  have h := jacobiNcOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `sc`: the shifts of `sc(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiSc_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSc (z + completeEllipticK k) k =
      -(jacobiComodulus k)⁻¹ * jacobiCs z k ∧
    jacobiSc (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      (I / jacobiComodulus k) * jacobiDn z k ∧
    jacobiSc (z + I * completeEllipticKPrime k) k =
      I * jacobiNd z k ∧
    jacobiSc (z + 2 * completeEllipticK k) k =
      jacobiSc z k ∧
    jacobiSc (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiSc z k ∧
    jacobiSc (z + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiSc z k := by
  have h := jacobiScOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `ns`: the shifts of `ns(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiNs_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNs (z + completeEllipticK k) k =
      jacobiDc z k ∧
    jacobiNs (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      k * jacobiCd z k ∧
    jacobiNs (z + I * completeEllipticKPrime k) k =
      k * jacobiSn z k ∧
    jacobiNs (z + 2 * completeEllipticK k) k =
      -jacobiNs z k ∧
    jacobiNs (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiNs z k ∧
    jacobiNs (z + 2 * (I * completeEllipticKPrime k)) k =
      jacobiNs z k := by
  have h := jacobiNsOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `ds`: the shifts of `ds(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiDs_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDs (z + completeEllipticK k) k =
      jacobiComodulus k * jacobiNc z k ∧
    jacobiDs (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      I * k * jacobiComodulus k * jacobiSd z k ∧
    jacobiDs (z + I * completeEllipticKPrime k) k =
      -(I * k) * jacobiCn z k ∧
    jacobiDs (z + 2 * completeEllipticK k) k =
      -jacobiDs z k ∧
    jacobiDs (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      jacobiDs z k ∧
    jacobiDs (z + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiDs z k := by
  have h := jacobiDsOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `cs`: the shifts of `cs(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiCs_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCs (z + completeEllipticK k) k =
      -jacobiComodulus k * jacobiSc z k ∧
    jacobiCs (z + completeEllipticK k + I * completeEllipticKPrime k) k =
      -(I * jacobiComodulus k) * jacobiNd z k ∧
    jacobiCs (z + I * completeEllipticKPrime k) k =
      -I * jacobiDn z k ∧
    jacobiCs (z + 2 * completeEllipticK k) k =
      jacobiCs z k ∧
    jacobiCs (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiCs z k ∧
    jacobiCs (z + 2 * (I * completeEllipticKPrime k)) k =
      -jacobiCs z k := by
  have h := jacobiCsOfTau_shift (jacobiTau_im_pos hk) z
  jacobi_to_k hk h

/-! ### Tables 22.4.1–22.4.2: periods, poles and zeros -/

/-- The corner of the fundamental unit cell labelled by a Glaisher letter (DLMF §22.4(ii),
Figure 22.4.2): `s = 0`, `c = K`, `d = K + iK'`, `n = iK'`. -/
def jacobiLetterPointk (p : JacobiLetter) (k : ℂ) : ℂ :=
  match p with
  | .s => 0
  | .c => completeEllipticK k
  | .d => completeEllipticK k + I * completeEllipticKPrime k
  | .n => I * completeEllipticKPrime k

/-- The points congruent to `a` modulo the lattice `2mK + 2niK'` (DLMF §22.4(i)). -/
def jacobiCongruentk (a k : ℂ) : Set ℂ :=
  {z | ∃ m n : ℤ, z = a + 2 * m * completeEllipticK k + 2 * n * (I * completeEllipticKPrime k)}

/-! ### Simple zeros of the letter theta functions -/

/-- Real part of the corner of a letter, in units of `2K`. -/
def jacobiLetterCornerRe : JacobiLetter → ℝ
  | .s => 0
  | .c => 1 / 2
  | .d => 1 / 2
  | .n => 0

/-- Imaginary part of the corner of a letter, in units of `2iK'`. -/
def jacobiLetterCornerIm : JacobiLetter → ℝ
  | .s => 0
  | .c => 0
  | .d => 1 / 2
  | .n => 1 / 2

/-- The theta shift of a letter: `θ_p(ζ)` is a unit times `θ₁(ζ - jacobiLetterThetaShift p τ)`. -/
def jacobiLetterThetaShift (p : JacobiLetter) (τ : ℂ) : ℂ :=
    (jacobiLetterCornerRe p + jacobiLetterCornerIm p * τ) * π

/-- The (nonvanishing, entire) amplitude with `θ_p(ζ) = amp · θ₁(ζ - shift)`. -/
def jacobiLetterThetaAmplitude (p : JacobiLetter) (ζ τ : ℂ) : ℂ :=
  match p with
  | .s => jacobiThetaThreeTau 0 τ / (jacobiThetaTwoTau 0 τ * jacobiThetaFourTau 0 τ)
  | .c => -1 / jacobiThetaTwoTau 0 τ
  | .d => I * jacobiThetaShiftFactor (ζ - π / 2 - π * τ / 2) τ / jacobiThetaThreeTau 0 τ
  | .n => I * jacobiThetaShiftFactor (ζ - π * τ / 2) τ / jacobiThetaFourTau 0 τ

/-- Identity under the stated parameter and domain assumptions:
`jacobiLetterTheta p ζ τ = jacobiLetterThetaAmplitude p ζ τ * jacobiThetaOneTau (ζ -
jacobiLetterThetaShift p τ) τ`. -/
theorem jacobiLetterTheta_eq_amplitude_mul (p : JacobiLetter) (ζ τ : ℂ) :
    jacobiLetterTheta p ζ τ = jacobiLetterThetaAmplitude p ζ τ *
        jacobiThetaOneTau (ζ - jacobiLetterThetaShift p τ) τ := by
  cases p
  · simp [jacobiLetterTheta, jacobiLetterThetaAmplitude, jacobiLetterThetaShift,
        jacobiLetterCornerRe, jacobiLetterCornerIm]
  · simp only [jacobiLetterTheta, jacobiLetterThetaAmplitude, jacobiLetterThetaShift,
        jacobiLetterCornerRe, jacobiLetterCornerIm]
    rw [jacobiThetaOneTau]
    push_cast
    rw [show ζ - (1 / 2 + 0 * τ) * π + π / 2 = ζ by ring]
    ring
  · simp only [jacobiLetterTheta, jacobiLetterThetaAmplitude, jacobiLetterThetaShift,
        jacobiLetterCornerRe, jacobiLetterCornerIm]
    have h1 := jacobiThetaThreeTau_add_pi_div_two (ζ - π / 2) τ
    have h2 := jacobiThetaFourTau_add_pi_mul_div_two (ζ - π / 2 - π * τ / 2) τ
    rw [show ζ - π / 2 + π / 2 = ζ by ring] at h1
    rw [show ζ - π / 2 - π * τ / 2 + π * τ / 2 = ζ - π / 2 by ring] at h2
    push_cast
    rw [show ζ - (1 / 2 + 1 / 2 * τ) * π = ζ - π / 2 - π * τ / 2 by ring, h1, h2]
    ring
  · simp only [jacobiLetterTheta, jacobiLetterThetaAmplitude, jacobiLetterThetaShift,
        jacobiLetterCornerRe, jacobiLetterCornerIm]
    have h2 := jacobiThetaFourTau_add_pi_mul_div_two (ζ - π * τ / 2) τ
    rw [show ζ - π * τ / 2 + π * τ / 2 = ζ by ring] at h2
    push_cast
    rw [show ζ - (0 + 1 / 2 * τ) * π = ζ - π * τ / 2 by ring, h2]
    ring

/-- Nonvanishing under the stated hypotheses: `jacobiLetterThetaAmplitude p ζ τ ≠ 0`. -/
theorem jacobiLetterThetaAmplitude_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) (ζ : ℂ) :
    jacobiLetterThetaAmplitude p ζ τ ≠ 0 := by
  have h2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have h3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have h4 := jacobiThetaFourTau_zero_ne_zero hτ
  cases p <;> simp [jacobiLetterThetaAmplitude, h2, h3, h4, jacobiThetaShiftFactor_ne_zero]

/-- Differentiability of the indicated parameterized function:
`Differentiable ℂ (fun ζ => jacobiLetterThetaAmplitude p ζ τ)`. -/
private lemma differentiable_jacobiLetterThetaAmplitude (p : JacobiLetter) (τ : ℂ) :
    Differentiable ℂ (fun ζ => jacobiLetterThetaAmplitude p ζ τ) := by
  cases p <;> simp only [jacobiLetterThetaAmplitude, jacobiThetaShiftFactor] <;> fun_prop

/-- The derivative of `θ₁` does not vanish at its zeros. -/
private lemma deriv_jacobiThetaOneTau_ne_zero_of_eq_zero {τ : ℂ} (hτ : 0 < τ.im) {y : ℂ}
    (hy : jacobiThetaOneTau y τ = 0) :
    deriv (fun w => jacobiThetaOneTau w τ) y ≠ 0 := by
  obtain ⟨m, n, rfl⟩ := ((DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ y).1).mp hy
  have hd : Differentiable ℂ (fun w => jacobiThetaOneTau w τ) :=
    DLMF.Theta.differentiable_jacobiThetaTau 1 hτ
  set c : ℂ := (-1 : ℂ) ^ (m + n) * cexp (-(π * I * τ * n ^ 2)) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (zpow_ne_zero _ (by norm_num)) (exp_ne_zero _)
  have hL : HasDerivAt (fun z => jacobiThetaOneTau (z + (m + n * τ) * π) τ)
      (deriv (fun w => jacobiThetaOneTau w τ) ((m + n * τ) * π)) 0 := by
    have := (hd ((0 : ℂ) + (m + n * τ) * π)).hasDerivAt.comp_add_const (0 : ℂ) ((m + n * τ) * π)
    simpa using this
  have hR : HasDerivAt (fun z => c * cexp (-2 * I * n * z) * jacobiThetaOneTau z τ)
      (c * (cexp (-2 * I * n * 0) * (-2 * I * n)) * jacobiThetaOneTau 0 τ +
        c * cexp (-2 * I * n * 0) * deriv (fun w => jacobiThetaOneTau w τ) 0) 0 := by
    have he : HasDerivAt (fun z : ℂ => cexp (-2 * I * n * z)) (cexp (-2 * I * n * 0) * (-2 * I * n))
        0 := by
      have := ((hasDerivAt_id (0 : ℂ)).const_mul (-2 * I * n)).cexp
      simpa using this
    exact (he.const_mul c).mul (hd 0).hasDerivAt
  have heq : (fun z => jacobiThetaOneTau (z + (m + n * τ) * π) τ) =
      fun z => c * cexp (-2 * I * n * z) * jacobiThetaOneTau z τ := by
    funext z; rw [DLMF.Theta.jacobiThetaOneTau_add_lattice]
  rw [heq] at hL
  rw [hL.unique hR, jacobiThetaOneTau_zero]
  have h1 : deriv (fun w => jacobiThetaOneTau w τ) 0 ≠ 0 := by
    have := DLMF.Theta.jacobiThetaOneDerivNullTau_eq_mul hτ
    rw [DLMF.Theta.jacobiThetaOneDerivNullTau] at this
    rw [this]
    obtain ⟨a, b, c⟩ := DLMF.Theta.jacobiThetaNullTau_ne_zero hτ
    exact mul_ne_zero (mul_ne_zero a b) c
  simpa [hc0] using h1

/-- Identity under the stated parameter and domain assumptions: `jacobiLetterPointk p k = 2 *
jacobiLetterCornerRe p * completeEllipticK k + 2 * jacobiLetterCornerIm p * (I *
completeEllipticKPrime k)`. -/
private lemma jacobiLetterPointk_eq_corner (p : JacobiLetter) (k : ℂ) :
    jacobiLetterPointk p k = 2 * jacobiLetterCornerRe p * completeEllipticK k +
      2 * jacobiLetterCornerIm p * (I * completeEllipticKPrime k) := by
  cases p <;> simp [jacobiLetterPointk, jacobiLetterCornerRe, jacobiLetterCornerIm]

/-- The corners of a letter are the zeros of its theta function. -/
theorem mem_jacobiCongruentk_iff_jacobiThetaOneTau_eq_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    (p : JacobiLetter) (z : ℂ) :
    z ∈ jacobiCongruentk (jacobiLetterPointk p k) k ↔
      jacobiThetaOneTau (jacobiThetaArgument z k - jacobiLetterThetaShift p (jacobiTau k))
          (jacobiTau k) = 0 := by
  have hτ := jacobiTau_im_pos hk
  have hK := completeEllipticK_ne_zero hk
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [((DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ _).1), jacobiCongruentk, Set.mem_ofPred_eq,
    jacobiLetterPointk_eq_corner]
  simp only [jacobiThetaArgument, jacobiLetterThetaShift, jacobiTau]
  refine exists₂_congr fun m n => ?_
  constructor
  · intro h
    rw [h]; field_simp; ring
  · intro h
    field_simp at h
    linear_combination h

/-- The theta function of a letter as a function of `w`. -/
private lemma jacobiLetterTheta_comp_eq_amplitude_mul {k : ℂ} (p : JacobiLetter) :
    (fun w => jacobiLetterTheta p (jacobiThetaArgument w k) (jacobiTau k)) =
      (fun w => jacobiLetterThetaAmplitude p (jacobiThetaArgument w k) (jacobiTau k)) *
        ((fun y => jacobiThetaOneTau y (jacobiTau k)) ∘
          fun w => jacobiThetaArgument w k - jacobiLetterThetaShift p (jacobiTau k)) := by
  funext w; simp [jacobiLetterTheta_eq_amplitude_mul]

/-- Differentiability of the indicated parameterized function: `Differentiable ℂ (fun w =>
jacobiLetterTheta p (jacobiThetaArgument w k) (jacobiTau k))`. -/
theorem differentiable_jacobiLetterTheta_comp_jacobiThetaArgument {k : ℂ}
    (hk : k ∈ jacobiModulusDomain)
    (p : JacobiLetter) :
    Differentiable ℂ (fun w => jacobiLetterTheta p (jacobiThetaArgument w k) (jacobiTau k)) := by
  rw [jacobiLetterTheta_comp_eq_amplitude_mul]
  have h1 : Differentiable ℂ (fun y => jacobiThetaOneTau y (jacobiTau k)) :=
    DLMF.Theta.differentiable_jacobiThetaTau 1 (jacobiTau_im_pos hk)
  have h2 : Differentiable ℂ fun w => jacobiThetaArgument w k -
      jacobiLetterThetaShift p (jacobiTau k) := by
    unfold jacobiThetaArgument; fun_prop
  exact ((differentiable_jacobiLetterThetaAmplitude p _).comp
      (by unfold jacobiThetaArgument; fun_prop)).mul (h1.comp h2)

/-- The zeros of the letter theta functions are simple. -/
private lemma meromorphicOrderAt_jacobiLetterTheta_comp_eq_one {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) (p : JacobiLetter) {z : ℂ}
    (hz : jacobiLetterTheta p (jacobiThetaArgument z k) (jacobiTau k) = 0) :
    meromorphicOrderAt (fun w =>
        jacobiLetterTheta p (jacobiThetaArgument w k) (jacobiTau k)) z = 1 := by
  have hτ := jacobiTau_im_pos hk
  have hK := completeEllipticK_ne_zero hk
  have h1 : Differentiable ℂ (fun y => jacobiThetaOneTau y (jacobiTau k)) :=
    DLMF.Theta.differentiable_jacobiThetaTau 1 hτ
  set g : ℂ → ℂ := fun w => jacobiThetaArgument w k - jacobiLetterThetaShift p (jacobiTau k) with hg
  have hgd : HasDerivAt g (π / (2 * completeEllipticK k)) z := by
    have := ((hasDerivAt_id z).const_mul (π / (2 * completeEllipticK k))).sub_const
      (jacobiLetterThetaShift p (jacobiTau k))
    convert this using 1
    · funext w; simp [hg, jacobiThetaArgument]; ring
    · simp
  have hg0 : jacobiThetaOneTau (g z) (jacobiTau k) = 0 := by
    rw [jacobiLetterTheta_eq_amplitude_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (jacobiLetterThetaAmplitude_ne_zero hτ _ _)
  have hamp : AnalyticAt ℂ
      (fun w => jacobiLetterThetaAmplitude p (jacobiThetaArgument w k) (jacobiTau k)) z :=
    Differentiable.analyticAt
        ((differentiable_jacobiLetterThetaAmplitude p _).comp
            (by unfold jacobiThetaArgument; fun_prop :
      Differentiable ℂ fun w => jacobiThetaArgument w k)) z
  rw [jacobiLetterTheta_comp_eq_amplitude_mul,
      meromorphicOrderAt_mul_of_ne_zero hamp (jacobiLetterThetaAmplitude_ne_zero hτ _ _)]
  have hga : AnalyticAt ℂ g z :=
    Differentiable.analyticAt (by rw [hg]; unfold jacobiThetaArgument; fun_prop) z
  rw [show (fun w => jacobiThetaArgument w k - jacobiLetterThetaShift p (jacobiTau k)) = g from rfl,
    meromorphicOrderAt_comp_of_deriv_ne_zero hga ?_]
  · have ha : AnalyticAt ℂ (fun y => jacobiThetaOneTau y (jacobiTau k)) (g z) :=
      h1.analyticAt (g z)
    have := ha.analyticOrderAt_sub_eq_one_of_deriv_ne_zero
        (deriv_jacobiThetaOneTau_ne_zero_of_eq_zero hτ hg0)
    simp only [hg0, sub_zero] at this
    rw [ha.meromorphicOrderAt_eq, this]
    rfl
  · rw [hgd.deriv]
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) (mul_ne_zero two_ne_zero hK)

/-- Nonvanishing under the stated hypotheses: `(1 / 2 : ℝ) - j ≠ 0`. -/
private lemma one_half_sub_intCast_ne_zero (j : ℤ) : (1 / 2 : ℝ) - j ≠ 0 := by
  intro h
  have : (2 * j : ℝ) = 1 := by linarith
  have : (2 * j : ℤ) = 1 := by exact_mod_cast this
  omega

/-- Distinct letters have disjoint zero sets. -/
private lemma jacobiLetterThetaShift_zeros_disjoint {τ : ℂ} (hτ : 0 < τ.im) {p q : JacobiLetter}
    (hpq : p ≠ q) (ζ : ℂ)
    (hp : jacobiThetaOneTau (ζ - jacobiLetterThetaShift p τ) τ = 0)
    (hq : jacobiThetaOneTau (ζ - jacobiLetterThetaShift q τ) τ = 0) : False := by
  obtain ⟨m, n, hmn⟩ := ((DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ _).1).mp hp
  obtain ⟨m', n', hmn'⟩ := ((DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ _).1).mp hq
  have h := DLMF.Theta.eq_zero_of_lattice_point_eq_zero hτ
    (a := jacobiLetterCornerRe q - jacobiLetterCornerRe p - (m - m'))
        (b := jacobiLetterCornerIm q - jacobiLetterCornerIm p - (n - n'))
    (by simp only [jacobiLetterThetaShift] at hmn hmn'; push_cast; linear_combination hmn' - hmn)
  obtain ⟨ha, hb⟩ := h
  have e1 := one_half_sub_intCast_ne_zero (m - m')
  have e2 := one_half_sub_intCast_ne_zero (n - n')
  have e3 := one_half_sub_intCast_ne_zero (m' - m)
  have e4 := one_half_sub_intCast_ne_zero (n' - n)
  push_cast at e1 e2 e3 e4
  cases p <;> cases q <;> simp only [jacobiLetterCornerRe, jacobiLetterCornerIm] at ha hb <;>
    first | exact hpq rfl | (apply e1; linarith) | (apply e2; linarith) |
      (apply e3; linarith) | (apply e4; linarith)

/-- Zeros and poles of the Jacobian elliptic functions (Tables 22.4.1–22.4.2 and
the mnemonic of §22.4(ii)(a)): for distinct letters `p ≠ q`, `pq(z, k)` has simple zeros exactly at
the points congruent to the `p`-corner, simple poles exactly at the points congruent to the
`q`-corner, and is analytic and nonzero elsewhere. -/
@[dlmf 22.4.T1, dlmf 22.4.T2, dlmf 22.4.ii]
theorem jacobiPQ_zeros_poles {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q : JacobiLetter}
    (hpq : p ≠ q) (z : ℂ) :
    (meromorphicOrderAt (fun w => jacobiPQ p q w k) z = 1 ↔
        z ∈ jacobiCongruentk (jacobiLetterPointk p k) k) ∧
      (meromorphicOrderAt (fun w => jacobiPQ p q w k) z = -1 ↔
        z ∈ jacobiCongruentk (jacobiLetterPointk q k) k) ∧
      (z ∉ jacobiCongruentk (jacobiLetterPointk p k) k →
        z ∉ jacobiCongruentk (jacobiLetterPointk q k) k →
        AnalyticAt ℂ (fun w => jacobiPQ p q w k) z ∧ jacobiPQ p q z k ≠ 0) := by
  have hτ := jacobiTau_im_pos hk
  set F : JacobiLetter → ℂ → ℂ := fun r w =>
      jacobiLetterTheta r (jacobiThetaArgument w k) (jacobiTau k)
    with hF
  have hFd : ∀ r, Differentiable ℂ (F r) := fun r =>
      differentiable_jacobiLetterTheta_comp_jacobiThetaArgument hk r
  have hzero : ∀ r, F r z = 0 ↔ z ∈ jacobiCongruentk (jacobiLetterPointk r k) k := by
    intro r
    rw [mem_jacobiCongruentk_iff_jacobiThetaOneTau_eq_zero hk, hF]
    simp only [jacobiLetterTheta_eq_amplitude_mul, mul_eq_zero,
        jacobiLetterThetaAmplitude_ne_zero hτ, false_or]
  have hord : ∀ r, meromorphicOrderAt (F r) z = if F r z = 0 then 1 else 0 := by
    intro r
    split_ifs with h
    · exact meromorphicOrderAt_jacobiLetterTheta_comp_eq_one hk r h
    · rw [((hFd r).analyticAt z).meromorphicOrderAt_eq,
        ((hFd r).analyticAt z).analyticOrderAt_eq_zero.mpr h]
      rfl
  have heq : (fun w => jacobiPQ p q w k) = fun w => F p w / F q w := by
    funext w; simp [hF, jacobiPQ, jacobiGlaisher, hpq]
  have hdiv : meromorphicOrderAt (fun w => jacobiPQ p q w k) z =
      meromorphicOrderAt (F p) z - meromorphicOrderAt (F q) z := by
    rw [heq, show (fun w => F p w / F q w) = F p / F q from rfl]
    exact meromorphicOrderAt_div ((hFd p).analyticAt z).meromorphicAt
      ((hFd q).analyticAt z).meromorphicAt
  have hdisj : ¬ (F p z = 0 ∧ F q z = 0) := by
    rintro ⟨h1, h2⟩
    rw [hzero, mem_jacobiCongruentk_iff_jacobiThetaOneTau_eq_zero hk] at h1 h2
    exact jacobiLetterThetaShift_zeros_disjoint hτ hpq _ h1 h2
  rw [hdiv, hord p, hord q, ← hzero p, ← hzero q]
  refine ⟨?_, ?_, fun h1 h2 => ?_⟩
  · by_cases h1 : F p z = 0 <;> by_cases h2 : F q z = 0 <;> simp_all <;> decide
  · by_cases h1 : F p z = 0 <;> by_cases h2 : F q z = 0 <;> simp_all <;> decide
  · rw [heq, show jacobiPQ p q z k = F p z / F q z from congrFun heq z]
    exact ⟨((hFd p).analyticAt z).div ((hFd q).analyticAt z) h2, div_ne_zero h1 h2⟩

/-- Periods of `sn` (Tables 22.4.1 and 22.4.2): `4K`, `2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiSn_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSn (z + 4 * completeEllipticK k) k = jacobiSn z k ∧
      jacobiSn (z + 2 * (I * completeEllipticKPrime k)) k = jacobiSn z k :=
  ⟨by rw [show z + 4 * completeEllipticK k = z + 2 * completeEllipticK k + 2 *
        completeEllipticK k by ring,
      (jacobiSn_shift hk _).2.2.2.1, (jacobiSn_shift hk z).2.2.2.1, neg_neg], (jacobiSn_shift hk
          z).2.2.2.2.2⟩

/-- Periods of `cd` (Tables 22.4.1 and 22.4.2): `4K`, `2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiCd_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCd (z + 4 * completeEllipticK k) k = jacobiCd z k ∧
      jacobiCd (z + 2 * (I * completeEllipticKPrime k)) k = jacobiCd z k :=
  ⟨by rw [show z + 4 * completeEllipticK k = z + 2 * completeEllipticK k + 2 *
        completeEllipticK k by ring,
      (jacobiCd_shift hk _).2.2.2.1, (jacobiCd_shift hk z).2.2.2.1, neg_neg], (jacobiCd_shift hk
          z).2.2.2.2.2⟩

/-- Periods of `dc` (Tables 22.4.1 and 22.4.2): `4K`, `2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiDc_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDc (z + 4 * completeEllipticK k) k = jacobiDc z k ∧
      jacobiDc (z + 2 * (I * completeEllipticKPrime k)) k = jacobiDc z k :=
  ⟨by rw [show z + 4 * completeEllipticK k = z + 2 * completeEllipticK k + 2 *
        completeEllipticK k by ring,
      (jacobiDc_shift hk _).2.2.2.1, (jacobiDc_shift hk z).2.2.2.1, neg_neg], (jacobiDc_shift hk
          z).2.2.2.2.2⟩

/-- Periods of `ns` (Tables 22.4.1 and 22.4.2): `4K`, `2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiNs_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNs (z + 4 * completeEllipticK k) k = jacobiNs z k ∧
      jacobiNs (z + 2 * (I * completeEllipticKPrime k)) k = jacobiNs z k :=
  ⟨by rw [show z + 4 * completeEllipticK k = z + 2 * completeEllipticK k + 2 *
        completeEllipticK k by ring,
      (jacobiNs_shift hk _).2.2.2.1, (jacobiNs_shift hk z).2.2.2.1, neg_neg], (jacobiNs_shift hk
          z).2.2.2.2.2⟩

/-- Periods of `cn` (Tables 22.4.1 and 22.4.2): `4K`, `2K + 2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiCn_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCn (z + 4 * completeEllipticK k) k = jacobiCn z k ∧
      jacobiCn (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
          jacobiCn z k :=
  ⟨by rw [show z + 4 * completeEllipticK k = z + 2 * completeEllipticK k + 2 *
        completeEllipticK k by ring,
      (jacobiCn_shift hk _).2.2.2.1, (jacobiCn_shift hk z).2.2.2.1, neg_neg], (jacobiCn_shift hk
          z).2.2.2.2.1⟩

/-- Periods of `sd` (Tables 22.4.1 and 22.4.2): `4K`, `2K + 2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiSd_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSd (z + 4 * completeEllipticK k) k = jacobiSd z k ∧
      jacobiSd (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
          jacobiSd z k :=
  ⟨by rw [show z + 4 * completeEllipticK k = z + 2 * completeEllipticK k + 2 *
        completeEllipticK k by ring,
      (jacobiSd_shift hk _).2.2.2.1, (jacobiSd_shift hk z).2.2.2.1, neg_neg], (jacobiSd_shift hk
          z).2.2.2.2.1⟩

/-- Periods of `nc` (Tables 22.4.1 and 22.4.2): `4K`, `2K + 2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiNc_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNc (z + 4 * completeEllipticK k) k = jacobiNc z k ∧
      jacobiNc (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
          jacobiNc z k :=
  ⟨by rw [show z + 4 * completeEllipticK k = z + 2 * completeEllipticK k + 2 *
        completeEllipticK k by ring,
      (jacobiNc_shift hk _).2.2.2.1, (jacobiNc_shift hk z).2.2.2.1, neg_neg], (jacobiNc_shift hk
          z).2.2.2.2.1⟩

/-- Periods of `ds` (Tables 22.4.1 and 22.4.2): `4K`, `2K + 2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiDs_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDs (z + 4 * completeEllipticK k) k = jacobiDs z k ∧
      jacobiDs (z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k =
          jacobiDs z k :=
  ⟨by rw [show z + 4 * completeEllipticK k = z + 2 * completeEllipticK k + 2 *
        completeEllipticK k by ring,
      (jacobiDs_shift hk _).2.2.2.1, (jacobiDs_shift hk z).2.2.2.1, neg_neg], (jacobiDs_shift hk
          z).2.2.2.2.1⟩

/-- Periods of `dn` (Tables 22.4.1 and 22.4.2): `2K`, `4iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiDn_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDn (z + 2 * completeEllipticK k) k = jacobiDn z k ∧
      jacobiDn (z + 4 * (I * completeEllipticKPrime k)) k = jacobiDn z k :=
  ⟨(jacobiDn_shift hk z).2.2.2.1, by
    rw [show z + 4 * (I * completeEllipticKPrime k) =
        z + 2 * (I * completeEllipticKPrime k) + 2 * (I * completeEllipticKPrime k) by ring,
      (jacobiDn_shift hk _).2.2.2.2.2, (jacobiDn_shift hk z).2.2.2.2.2, neg_neg]⟩

/-- Periods of `nd` (Tables 22.4.1 and 22.4.2): `2K`, `4iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiNd_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNd (z + 2 * completeEllipticK k) k = jacobiNd z k ∧
      jacobiNd (z + 4 * (I * completeEllipticKPrime k)) k = jacobiNd z k :=
  ⟨(jacobiNd_shift hk z).2.2.2.1, by
    rw [show z + 4 * (I * completeEllipticKPrime k) =
        z + 2 * (I * completeEllipticKPrime k) + 2 * (I * completeEllipticKPrime k) by ring,
      (jacobiNd_shift hk _).2.2.2.2.2, (jacobiNd_shift hk z).2.2.2.2.2, neg_neg]⟩

/-- Periods of `sc` (Tables 22.4.1 and 22.4.2): `2K`, `4iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiSc_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSc (z + 2 * completeEllipticK k) k = jacobiSc z k ∧
      jacobiSc (z + 4 * (I * completeEllipticKPrime k)) k = jacobiSc z k :=
  ⟨(jacobiSc_shift hk z).2.2.2.1, by
    rw [show z + 4 * (I * completeEllipticKPrime k) =
        z + 2 * (I * completeEllipticKPrime k) + 2 * (I * completeEllipticKPrime k) by ring,
      (jacobiSc_shift hk _).2.2.2.2.2, (jacobiSc_shift hk z).2.2.2.2.2, neg_neg]⟩

/-- Periods of `cs` (Tables 22.4.1 and 22.4.2): `2K`, `4iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiCs_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCs (z + 2 * completeEllipticK k) k = jacobiCs z k ∧
      jacobiCs (z + 4 * (I * completeEllipticKPrime k)) k = jacobiCs z k :=
  ⟨(jacobiCs_shift hk z).2.2.2.1, by
    rw [show z + 4 * (I * completeEllipticKPrime k) =
        z + 2 * (I * completeEllipticKPrime k) + 2 * (I * completeEllipticKPrime k) by ring,
      (jacobiCs_shift hk _).2.2.2.2.2, (jacobiCs_shift hk z).2.2.2.2.2, neg_neg]⟩

end DLMF.JacobiElliptic
