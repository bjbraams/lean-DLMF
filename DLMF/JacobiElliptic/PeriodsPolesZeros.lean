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

* `jacobiPQTau_add_K`, `jacobiPQTau_add_iKp`: the quarter-period shifts in the lattice form.
* `jacobiSnTau_shift`, …, `jacobiCsTau_shift`: Table 22.4.3 in the lattice form.
* `jacobiSnk_shift`, `jacobiCnk_shift`, `jacobiDnk_shift`, …, `jacobiCsk_shift`: Table 22.4.3
  for `k ∈ jacobiModulusDomain`.
* `mem_jacobiCongruentk_iff_jacobiThetaOneTau_eq_zero`: the corners of a letter are the zeros
  of its theta function.
* `jacobiPQk_zeros_poles`: the zeros and poles, Tables 22.4.1–22.4.2 and DLMF §22.4(ii).
* `jacobiSnk_periodic`, `jacobiCnk_periodic`, `jacobiDnk_periodic` and the nine companions:
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

open DLMF.EllipticIntegrals (compEllIntKk compEllIntKpk)

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
`jacobiModulusTau τ = jacobiModulusRootTau τ ^ 2`. -/
private lemma jacobiModulusTau_eq_sq (τ : ℂ) : jacobiModulusTau τ = jacobiModulusRootTau τ ^ 2 := by
  rw [jacobiModulusTau, jacobiModulusRootTau, div_pow]

/-- Identity under the stated parameter and domain assumptions:
`jacobiComodulusTau τ = jacobiComodulusRootTau τ ^ 2`. -/
private lemma jacobiComodulusTau_eq_sq (τ : ℂ) : jacobiComodulusTau τ =
    jacobiComodulusRootTau τ ^ 2 := by
  rw [jacobiComodulusTau, jacobiComodulusRootTau, div_pow]

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

/-- Nonvanishing under the stated hypotheses: `compEllIntKTau τ ≠ 0`. -/
private lemma compEllIntKTau_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : compEllIntKTau τ ≠ 0 := by
  rw [compEllIntKTau]
  exact mul_ne_zero (div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero)
    (pow_ne_zero _ (jacobiThetaThreeTau_zero_ne_zero hτ))

/-- Identity under the stated parameter and domain assumptions: `jacobiZetaTau (z + compEllIntKTau
τ) τ = jacobiZetaTau z τ + π / 2`. -/
private lemma jacobiZetaTau_add_compEllIntKTau {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiZetaTau (z + compEllIntKTau τ) τ = jacobiZetaTau z τ + π / 2 := by
  have := compEllIntKTau_ne_zero hτ
  rw [jacobiZetaTau, jacobiZetaTau]; field_simp

/-- Identity under the stated parameter and domain assumptions: `jacobiZetaTau (z + I *
compEllIntKpTau τ) τ = jacobiZetaTau z τ + π * τ / 2`. -/
private lemma jacobiZetaTau_add_I_mul_compEllIntKpTau {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiZetaTau (z + I * compEllIntKpTau τ) τ = jacobiZetaTau z τ + π * τ / 2 := by
  have := compEllIntKTau_ne_zero hτ
  rw [jacobiZetaTau, jacobiZetaTau, compEllIntKpTau]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- `pq(z + K) = (β_p/β_q) · (σp)(σq)(z)` in the lattice form. -/
theorem jacobiPQTau_add_K {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQTau p q (z + compEllIntKTau τ) τ =
      jacobiLetterMultiplierK τ p / jacobiLetterMultiplierK τ q *
          jacobiPQTau p.swapK q.swapK z τ := by
  rw [jacobiPQTau, jacobiZetaTau_add_compEllIntKTau hτ,
      jacobiGlaisher_add_pi_div_two hτ, jacobiPQTau]

/-- `pq(z + iK') = (β'_p/β'_q) · (σ'p)(σ'q)(z)` in the lattice form. -/
theorem jacobiPQTau_add_iKp {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQTau p q (z + I * compEllIntKpTau τ) τ =
      jacobiLetterMultiplierKp τ p / jacobiLetterMultiplierKp τ q *
          jacobiPQTau p.swapKp q.swapKp z τ := by
  rw [jacobiPQTau, jacobiZetaTau_add_I_mul_compEllIntKpTau hτ,
      jacobiGlaisher_add_pi_mul_div_two hτ, jacobiPQTau]

/-- Composing the real and imaginary quarter-period shifts of a Glaisher quotient. -/
theorem jacobiPQTau_add_K_add_iKp {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQTau p q (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      (jacobiLetterMultiplierK τ p / jacobiLetterMultiplierK τ q) *
        (jacobiLetterMultiplierKp τ p.swapK / jacobiLetterMultiplierKp τ q.swapK *
          jacobiPQTau p.swapK.swapKp q.swapK.swapKp z τ) := by
  rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
    z + I * compEllIntKpTau τ + compEllIntKTau τ by ring,
    jacobiPQTau_add_K hτ, jacobiPQTau_add_iKp hτ]

/-- Composing two real quarter-period shifts of a Glaisher quotient. -/
theorem jacobiPQTau_add_two_K {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQTau p q (z + 2 * compEllIntKTau τ) τ =
      (jacobiLetterMultiplierK τ p / jacobiLetterMultiplierK τ q) *
        (jacobiLetterMultiplierK τ p.swapK / jacobiLetterMultiplierK τ q.swapK *
          jacobiPQTau p.swapK.swapK q.swapK.swapK z τ) := by
  rw [show z + 2 * compEllIntKTau τ =
    z + compEllIntKTau τ + compEllIntKTau τ by ring,
    jacobiPQTau_add_K hτ, jacobiPQTau_add_K hτ]

/-- Composing two imaginary quarter-period shifts of a Glaisher quotient. -/
theorem jacobiPQTau_add_two_iKp {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQTau p q (z + 2 * (I * compEllIntKpTau τ)) τ =
      (jacobiLetterMultiplierKp τ p / jacobiLetterMultiplierKp τ q) *
        (jacobiLetterMultiplierKp τ p.swapKp / jacobiLetterMultiplierKp τ q.swapKp *
          jacobiPQTau p.swapKp.swapKp q.swapKp.swapKp z τ) := by
  rw [show z + 2 * (I * compEllIntKpTau τ) =
    z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring,
    jacobiPQTau_add_iKp hτ, jacobiPQTau_add_iKp hτ]

/-- Composing the two full-period translations of a Glaisher quotient. -/
theorem jacobiPQTau_add_two_K_add_two_iKp {τ : ℂ} (hτ : 0 < τ.im)
    (p q : JacobiLetter) (z : ℂ) :
    jacobiPQTau p q (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      (jacobiLetterMultiplierK τ p / jacobiLetterMultiplierK τ q) *
        (jacobiLetterMultiplierK τ p.swapK / jacobiLetterMultiplierK τ q.swapK *
          ((jacobiLetterMultiplierKp τ p.swapK.swapK / jacobiLetterMultiplierKp τ q.swapK.swapK) *
            (jacobiLetterMultiplierKp τ p.swapK.swapK.swapKp /
              jacobiLetterMultiplierKp τ q.swapK.swapK.swapKp *
              jacobiPQTau p.swapK.swapK.swapKp.swapKp q.swapK.swapK.swapKp.swapKp z τ))) := by
  rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
    z + 2 * (I * compEllIntKpTau τ) + 2 * compEllIntKTau τ by ring,
    jacobiPQTau_add_two_K hτ, jacobiPQTau_add_two_iKp hτ]

/-- Unfold the twelve lattice-form functions and apply the quarter-period shifts. -/
macro "jacobi_shift_simp " h:term : tactic => `(tactic|
  simp only [jacobiSnTau, jacobiCnTau, jacobiDnTau, jacobiSdTau, jacobiCdTau, jacobiScTau,
    jacobiNsTau, jacobiNcTau, jacobiNdTau, jacobiDsTau, jacobiDcTau, jacobiCsTau,
    jacobiPQTau_add_K $h, jacobiPQTau_add_iKp $h,
    jacobiPQTau_add_K_add_iKp $h, jacobiPQTau_add_two_K $h,
    jacobiPQTau_add_two_iKp $h, jacobiPQTau_add_two_K_add_two_iKp $h,
    JacobiLetter.swapK, JacobiLetter.swapKp,
    jacobiLetterMultiplierK, jacobiLetterMultiplierKp, jacobiModulusTau_eq_sq,
        jacobiComodulusTau_eq_sq])

/-- Close a coefficient identity `a * X = b * X` produced by `jacobi_shift_simp`. -/
macro "jacobi_coef_tac" : tactic => `(tactic|
  ((try field_simp) <;> (try ring_nf) <;> (try simp only [I_sq, I_pow_four]) <;> (try ring_nf)))

/-- Apply the quarter-period shifts and close the resulting coefficient identity. -/
macro "jacobi_shift_close " h:term : tactic => `(tactic|
  (jacobi_shift_simp $h <;> jacobi_coef_tac))

/-- Table 22.4.3, row `sn`, in the lattice form: the shifts of `sn` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiSnTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiSnTau (z + compEllIntKTau τ) τ =
      jacobiCdTau z τ ∧
    jacobiSnTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      (jacobiModulusTau τ)⁻¹ * jacobiDcTau z τ ∧
    jacobiSnTau (z + I * compEllIntKpTau τ) τ =
      (jacobiModulusTau τ)⁻¹ * jacobiNsTau z τ ∧
    jacobiSnTau (z + 2 * compEllIntKTau τ) τ =
      -jacobiSnTau z τ ∧
    jacobiSnTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiSnTau z τ ∧
    jacobiSnTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      jacobiSnTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `cn`, in the lattice form: the shifts of `cn` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiCnTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiCnTau (z + compEllIntKTau τ) τ =
      -jacobiComodulusTau τ * jacobiSdTau z τ ∧
    jacobiCnTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      -(I * jacobiComodulusTau τ / jacobiModulusTau τ) * jacobiNcTau z τ ∧
    jacobiCnTau (z + I * compEllIntKpTau τ) τ =
      -(I / jacobiModulusTau τ) * jacobiDsTau z τ ∧
    jacobiCnTau (z + 2 * compEllIntKTau τ) τ =
      -jacobiCnTau z τ ∧
    jacobiCnTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      jacobiCnTau z τ ∧
    jacobiCnTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiCnTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `dn`, in the lattice form: the shifts of `dn` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiDnTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiDnTau (z + compEllIntKTau τ) τ =
      jacobiComodulusTau τ * jacobiNdTau z τ ∧
    jacobiDnTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      I * jacobiComodulusTau τ * jacobiScTau z τ ∧
    jacobiDnTau (z + I * compEllIntKpTau τ) τ =
      -I * jacobiCsTau z τ ∧
    jacobiDnTau (z + 2 * compEllIntKTau τ) τ =
      jacobiDnTau z τ ∧
    jacobiDnTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiDnTau z τ ∧
    jacobiDnTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiDnTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `cd`, in the lattice form: the shifts of `cd` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiCdTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiCdTau (z + compEllIntKTau τ) τ =
      -jacobiSnTau z τ ∧
    jacobiCdTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      -(jacobiModulusTau τ)⁻¹ * jacobiNsTau z τ ∧
    jacobiCdTau (z + I * compEllIntKpTau τ) τ =
      (jacobiModulusTau τ)⁻¹ * jacobiDcTau z τ ∧
    jacobiCdTau (z + 2 * compEllIntKTau τ) τ =
      -jacobiCdTau z τ ∧
    jacobiCdTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiCdTau z τ ∧
    jacobiCdTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      jacobiCdTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `sd`, in the lattice form: the shifts of `sd` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiSdTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiSdTau (z + compEllIntKTau τ) τ =
      (jacobiComodulusTau τ)⁻¹ * jacobiCnTau z τ ∧
    jacobiSdTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      -(I / (jacobiModulusTau τ * jacobiComodulusTau τ)) * jacobiDsTau z τ ∧
    jacobiSdTau (z + I * compEllIntKpTau τ) τ =
      (I / jacobiModulusTau τ) * jacobiNcTau z τ ∧
    jacobiSdTau (z + 2 * compEllIntKTau τ) τ =
      -jacobiSdTau z τ ∧
    jacobiSdTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      jacobiSdTau z τ ∧
    jacobiSdTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiSdTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `nd`, in the lattice form: the shifts of `nd` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiNdTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiNdTau (z + compEllIntKTau τ) τ =
      (jacobiComodulusTau τ)⁻¹ * jacobiDnTau z τ ∧
    jacobiNdTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      -(I / jacobiComodulusTau τ) * jacobiCsTau z τ ∧
    jacobiNdTau (z + I * compEllIntKpTau τ) τ =
      I * jacobiScTau z τ ∧
    jacobiNdTau (z + 2 * compEllIntKTau τ) τ =
      jacobiNdTau z τ ∧
    jacobiNdTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiNdTau z τ ∧
    jacobiNdTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiNdTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `dc`, in the lattice form: the shifts of `dc` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiDcTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiDcTau (z + compEllIntKTau τ) τ =
      -jacobiNsTau z τ ∧
    jacobiDcTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      -jacobiModulusTau τ * jacobiSnTau z τ ∧
    jacobiDcTau (z + I * compEllIntKpTau τ) τ =
      jacobiModulusTau τ * jacobiCdTau z τ ∧
    jacobiDcTau (z + 2 * compEllIntKTau τ) τ =
      -jacobiDcTau z τ ∧
    jacobiDcTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiDcTau z τ ∧
    jacobiDcTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      jacobiDcTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `nc`, in the lattice form: the shifts of `nc` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiNcTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiNcTau (z + compEllIntKTau τ) τ =
      -(jacobiComodulusTau τ)⁻¹ * jacobiDsTau z τ ∧
    jacobiNcTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      (I * jacobiModulusTau τ / jacobiComodulusTau τ) * jacobiCnTau z τ ∧
    jacobiNcTau (z + I * compEllIntKpTau τ) τ =
      I * jacobiModulusTau τ * jacobiSdTau z τ ∧
    jacobiNcTau (z + 2 * compEllIntKTau τ) τ =
      -jacobiNcTau z τ ∧
    jacobiNcTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      jacobiNcTau z τ ∧
    jacobiNcTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiNcTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `sc`, in the lattice form: the shifts of `sc` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiScTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiScTau (z + compEllIntKTau τ) τ =
      -(jacobiComodulusTau τ)⁻¹ * jacobiCsTau z τ ∧
    jacobiScTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      (I / jacobiComodulusTau τ) * jacobiDnTau z τ ∧
    jacobiScTau (z + I * compEllIntKpTau τ) τ =
      I * jacobiNdTau z τ ∧
    jacobiScTau (z + 2 * compEllIntKTau τ) τ =
      jacobiScTau z τ ∧
    jacobiScTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiScTau z τ ∧
    jacobiScTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiScTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `ns`, in the lattice form: the shifts of `ns` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiNsTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiNsTau (z + compEllIntKTau τ) τ =
      jacobiDcTau z τ ∧
    jacobiNsTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      jacobiModulusTau τ * jacobiCdTau z τ ∧
    jacobiNsTau (z + I * compEllIntKpTau τ) τ =
      jacobiModulusTau τ * jacobiSnTau z τ ∧
    jacobiNsTau (z + 2 * compEllIntKTau τ) τ =
      -jacobiNsTau z τ ∧
    jacobiNsTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiNsTau z τ ∧
    jacobiNsTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      jacobiNsTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `ds`, in the lattice form: the shifts of `ds` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiDsTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiDsTau (z + compEllIntKTau τ) τ =
      jacobiComodulusTau τ * jacobiNcTau z τ ∧
    jacobiDsTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      I * jacobiModulusTau τ * jacobiComodulusTau τ * jacobiSdTau z τ ∧
    jacobiDsTau (z + I * compEllIntKpTau τ) τ =
      -(I * jacobiModulusTau τ) * jacobiCnTau z τ ∧
    jacobiDsTau (z + 2 * compEllIntKTau τ) τ =
      -jacobiDsTau z τ ∧
    jacobiDsTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      jacobiDsTau z τ ∧
    jacobiDsTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiDsTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- Table 22.4.3, row `cs`, in the lattice form: the shifts of `cs` by `K`, `K + iK'`,
`iK'`, `2K`, `2K + 2iK'`, `2iK'`, with `k = θ₂²/θ₃²`, `k' = θ₄²/θ₃²`. -/
theorem jacobiCsTau_shift {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiCsTau (z + compEllIntKTau τ) τ =
      -jacobiComodulusTau τ * jacobiScTau z τ ∧
    jacobiCsTau (z + compEllIntKTau τ + I * compEllIntKpTau τ) τ =
      -(I * jacobiComodulusTau τ) * jacobiNdTau z τ ∧
    jacobiCsTau (z + I * compEllIntKpTau τ) τ =
      -I * jacobiDnTau z τ ∧
    jacobiCsTau (z + 2 * compEllIntKTau τ) τ =
      jacobiCsTau z τ ∧
    jacobiCsTau (z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiCsTau z τ ∧
    jacobiCsTau (z + 2 * (I * compEllIntKpTau τ)) τ =
      -jacobiCsTau z τ := by
  have hr := jacobiModulusRootTau_ne_zero hτ
  have hrp := jacobiComodulusRootTau_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> jacobi_shift_close hτ

/-- `K(k) ≠ 0` on `jacobiModulusDomain` (from the admitted inversion). -/
theorem compEllIntKk_ne_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : compEllIntKk k ≠ 0 := by
  rw [← (jacobi_inversion_k hk).2.2]
  exact compEllIntKTau_ne_zero (jacobiTauk_im_pos hk)

/-- `K'` of the lattice form at `τ = iK'/K` is `K'(k)`. -/
theorem compEllIntKpTau_jacobiTauk {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    compEllIntKpTau (jacobiTauk k) = compEllIntKpk k := by
  have hK := compEllIntKk_ne_zero hk
  rw [compEllIntKpTau, (jacobi_inversion_k hk).2.2, jacobiTauk]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- Transfer a lattice-form identity `h` at `τ = jacobiTauk k` to the modulus form. -/
macro "jacobi_to_k " hk:term:max h:ident : tactic => `(tactic| (
  obtain ⟨h1, h2, h3⟩ := jacobi_inversion_k $hk
  have hKp := compEllIntKpTau_jacobiTauk $hk
  simp only [jacobiSnTau, jacobiCnTau, jacobiDnTau, jacobiSdTau, jacobiCdTau, jacobiScTau,
    jacobiNsTau, jacobiNcTau, jacobiNdTau, jacobiDsTau, jacobiDcTau, jacobiCsTau] at $h:ident
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiSdk, jacobiCdk, jacobiSck,
    jacobiNsk, jacobiNck, jacobiNdk, jacobiDsk, jacobiDck, jacobiCsk, jacobiPQk_eq_jacobiPQTau $hk]
  simp only [h1, h2, h3, hKp] at $h:ident
  exact $h))

/-- Table 22.4.3, row `sn`: the shifts of `sn(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiSnk_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSnk (z + compEllIntKk k) k =
      jacobiCdk z k ∧
    jacobiSnk (z + compEllIntKk k + I * compEllIntKpk k) k =
      (k)⁻¹ * jacobiDck z k ∧
    jacobiSnk (z + I * compEllIntKpk k) k =
      (k)⁻¹ * jacobiNsk z k ∧
    jacobiSnk (z + 2 * compEllIntKk k) k =
      -jacobiSnk z k ∧
    jacobiSnk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      -jacobiSnk z k ∧
    jacobiSnk (z + 2 * (I * compEllIntKpk k)) k =
      jacobiSnk z k := by
  have h := jacobiSnTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `cn`: the shifts of `cn(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiCnk_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCnk (z + compEllIntKk k) k =
      -jacobiComodulusk k * jacobiSdk z k ∧
    jacobiCnk (z + compEllIntKk k + I * compEllIntKpk k) k =
      -(I * jacobiComodulusk k / k) * jacobiNck z k ∧
    jacobiCnk (z + I * compEllIntKpk k) k =
      -(I / k) * jacobiDsk z k ∧
    jacobiCnk (z + 2 * compEllIntKk k) k =
      -jacobiCnk z k ∧
    jacobiCnk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      jacobiCnk z k ∧
    jacobiCnk (z + 2 * (I * compEllIntKpk k)) k =
      -jacobiCnk z k := by
  have h := jacobiCnTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `dn`: the shifts of `dn(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiDnk_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDnk (z + compEllIntKk k) k =
      jacobiComodulusk k * jacobiNdk z k ∧
    jacobiDnk (z + compEllIntKk k + I * compEllIntKpk k) k =
      I * jacobiComodulusk k * jacobiSck z k ∧
    jacobiDnk (z + I * compEllIntKpk k) k =
      -I * jacobiCsk z k ∧
    jacobiDnk (z + 2 * compEllIntKk k) k =
      jacobiDnk z k ∧
    jacobiDnk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      -jacobiDnk z k ∧
    jacobiDnk (z + 2 * (I * compEllIntKpk k)) k =
      -jacobiDnk z k := by
  have h := jacobiDnTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `cd`: the shifts of `cd(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiCdk_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCdk (z + compEllIntKk k) k =
      -jacobiSnk z k ∧
    jacobiCdk (z + compEllIntKk k + I * compEllIntKpk k) k =
      -(k)⁻¹ * jacobiNsk z k ∧
    jacobiCdk (z + I * compEllIntKpk k) k =
      (k)⁻¹ * jacobiDck z k ∧
    jacobiCdk (z + 2 * compEllIntKk k) k =
      -jacobiCdk z k ∧
    jacobiCdk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      -jacobiCdk z k ∧
    jacobiCdk (z + 2 * (I * compEllIntKpk k)) k =
      jacobiCdk z k := by
  have h := jacobiCdTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `sd`: the shifts of `sd(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiSdk_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSdk (z + compEllIntKk k) k =
      (jacobiComodulusk k)⁻¹ * jacobiCnk z k ∧
    jacobiSdk (z + compEllIntKk k + I * compEllIntKpk k) k =
      -(I / (k * jacobiComodulusk k)) * jacobiDsk z k ∧
    jacobiSdk (z + I * compEllIntKpk k) k =
      (I / k) * jacobiNck z k ∧
    jacobiSdk (z + 2 * compEllIntKk k) k =
      -jacobiSdk z k ∧
    jacobiSdk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      jacobiSdk z k ∧
    jacobiSdk (z + 2 * (I * compEllIntKpk k)) k =
      -jacobiSdk z k := by
  have h := jacobiSdTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `nd`: the shifts of `nd(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiNdk_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNdk (z + compEllIntKk k) k =
      (jacobiComodulusk k)⁻¹ * jacobiDnk z k ∧
    jacobiNdk (z + compEllIntKk k + I * compEllIntKpk k) k =
      -(I / jacobiComodulusk k) * jacobiCsk z k ∧
    jacobiNdk (z + I * compEllIntKpk k) k =
      I * jacobiSck z k ∧
    jacobiNdk (z + 2 * compEllIntKk k) k =
      jacobiNdk z k ∧
    jacobiNdk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      -jacobiNdk z k ∧
    jacobiNdk (z + 2 * (I * compEllIntKpk k)) k =
      -jacobiNdk z k := by
  have h := jacobiNdTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `dc`: the shifts of `dc(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiDck_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDck (z + compEllIntKk k) k =
      -jacobiNsk z k ∧
    jacobiDck (z + compEllIntKk k + I * compEllIntKpk k) k =
      -k * jacobiSnk z k ∧
    jacobiDck (z + I * compEllIntKpk k) k =
      k * jacobiCdk z k ∧
    jacobiDck (z + 2 * compEllIntKk k) k =
      -jacobiDck z k ∧
    jacobiDck (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      -jacobiDck z k ∧
    jacobiDck (z + 2 * (I * compEllIntKpk k)) k =
      jacobiDck z k := by
  have h := jacobiDcTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `nc`: the shifts of `nc(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiNck_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNck (z + compEllIntKk k) k =
      -(jacobiComodulusk k)⁻¹ * jacobiDsk z k ∧
    jacobiNck (z + compEllIntKk k + I * compEllIntKpk k) k =
      (I * k / jacobiComodulusk k) * jacobiCnk z k ∧
    jacobiNck (z + I * compEllIntKpk k) k =
      I * k * jacobiSdk z k ∧
    jacobiNck (z + 2 * compEllIntKk k) k =
      -jacobiNck z k ∧
    jacobiNck (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      jacobiNck z k ∧
    jacobiNck (z + 2 * (I * compEllIntKpk k)) k =
      -jacobiNck z k := by
  have h := jacobiNcTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `sc`: the shifts of `sc(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiSck_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSck (z + compEllIntKk k) k =
      -(jacobiComodulusk k)⁻¹ * jacobiCsk z k ∧
    jacobiSck (z + compEllIntKk k + I * compEllIntKpk k) k =
      (I / jacobiComodulusk k) * jacobiDnk z k ∧
    jacobiSck (z + I * compEllIntKpk k) k =
      I * jacobiNdk z k ∧
    jacobiSck (z + 2 * compEllIntKk k) k =
      jacobiSck z k ∧
    jacobiSck (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      -jacobiSck z k ∧
    jacobiSck (z + 2 * (I * compEllIntKpk k)) k =
      -jacobiSck z k := by
  have h := jacobiScTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `ns`: the shifts of `ns(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiNsk_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNsk (z + compEllIntKk k) k =
      jacobiDck z k ∧
    jacobiNsk (z + compEllIntKk k + I * compEllIntKpk k) k =
      k * jacobiCdk z k ∧
    jacobiNsk (z + I * compEllIntKpk k) k =
      k * jacobiSnk z k ∧
    jacobiNsk (z + 2 * compEllIntKk k) k =
      -jacobiNsk z k ∧
    jacobiNsk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      -jacobiNsk z k ∧
    jacobiNsk (z + 2 * (I * compEllIntKpk k)) k =
      jacobiNsk z k := by
  have h := jacobiNsTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `ds`: the shifts of `ds(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiDsk_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDsk (z + compEllIntKk k) k =
      jacobiComodulusk k * jacobiNck z k ∧
    jacobiDsk (z + compEllIntKk k + I * compEllIntKpk k) k =
      I * k * jacobiComodulusk k * jacobiSdk z k ∧
    jacobiDsk (z + I * compEllIntKpk k) k =
      -(I * k) * jacobiCnk z k ∧
    jacobiDsk (z + 2 * compEllIntKk k) k =
      -jacobiDsk z k ∧
    jacobiDsk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      jacobiDsk z k ∧
    jacobiDsk (z + 2 * (I * compEllIntKpk k)) k =
      -jacobiDsk z k := by
  have h := jacobiDsTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-- Table 22.4.3, row `cs`: the shifts of `cs(z, k)` by `K`, `K + iK'`, `iK'`, `2K`,
`2K + 2iK'`, `2iK'`, for `k` in `jacobiModulusDomain` (from the admitted inversion 22.2.2). -/
@[dlmf 22.4.T3]
theorem jacobiCsk_shift {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCsk (z + compEllIntKk k) k =
      -jacobiComodulusk k * jacobiSck z k ∧
    jacobiCsk (z + compEllIntKk k + I * compEllIntKpk k) k =
      -(I * jacobiComodulusk k) * jacobiNdk z k ∧
    jacobiCsk (z + I * compEllIntKpk k) k =
      -I * jacobiDnk z k ∧
    jacobiCsk (z + 2 * compEllIntKk k) k =
      jacobiCsk z k ∧
    jacobiCsk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k =
      -jacobiCsk z k ∧
    jacobiCsk (z + 2 * (I * compEllIntKpk k)) k =
      -jacobiCsk z k := by
  have h := jacobiCsTau_shift (jacobiTauk_im_pos hk) z
  jacobi_to_k hk h

/-! ### Tables 22.4.1–22.4.2: periods, poles and zeros -/

/-- The corner of the fundamental unit cell labelled by a Glaisher letter (DLMF §22.4(ii),
Figure 22.4.2): `s = 0`, `c = K`, `d = K + iK'`, `n = iK'`. -/
def jacobiLetterPointk (p : JacobiLetter) (k : ℂ) : ℂ :=
  match p with
  | .s => 0
  | .c => compEllIntKk k
  | .d => compEllIntKk k + I * compEllIntKpk k
  | .n => I * compEllIntKpk k

/-- The points congruent to `a` modulo the lattice `2mK + 2niK'` (DLMF §22.4(i)). -/
def jacobiCongruentk (a k : ℂ) : Set ℂ :=
  {z | ∃ m n : ℤ, z = a + 2 * m * compEllIntKk k + 2 * n * (I * compEllIntKpk k)}

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
jacobiLetterCornerRe p * compEllIntKk k + 2 * jacobiLetterCornerIm p * (I * compEllIntKpk k)`. -/
private lemma jacobiLetterPointk_eq_corner (p : JacobiLetter) (k : ℂ) :
    jacobiLetterPointk p k = 2 * jacobiLetterCornerRe p * compEllIntKk k +
      2 * jacobiLetterCornerIm p * (I * compEllIntKpk k) := by
  cases p <;> simp [jacobiLetterPointk, jacobiLetterCornerRe, jacobiLetterCornerIm]

/-- The corners of a letter are the zeros of its theta function. -/
theorem mem_jacobiCongruentk_iff_jacobiThetaOneTau_eq_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    (p : JacobiLetter) (z : ℂ) :
    z ∈ jacobiCongruentk (jacobiLetterPointk p k) k ↔
      jacobiThetaOneTau (jacobiZetak z k - jacobiLetterThetaShift p (jacobiTauk k))
          (jacobiTauk k) = 0 := by
  have hτ := jacobiTauk_im_pos hk
  have hK := compEllIntKk_ne_zero hk
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [((DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ _).1), jacobiCongruentk, Set.mem_ofPred_eq,
    jacobiLetterPointk_eq_corner]
  simp only [jacobiZetak, jacobiLetterThetaShift, jacobiTauk]
  refine exists₂_congr fun m n => ?_
  constructor
  · intro h
    rw [h]; field_simp; ring
  · intro h
    field_simp at h
    linear_combination h

/-- The theta function of a letter as a function of `w`. -/
private lemma jacobiLetterTheta_comp_eq_amplitude_mul {k : ℂ} (p : JacobiLetter) :
    (fun w => jacobiLetterTheta p (jacobiZetak w k) (jacobiTauk k)) =
      (fun w => jacobiLetterThetaAmplitude p (jacobiZetak w k) (jacobiTauk k)) *
        ((fun y => jacobiThetaOneTau y (jacobiTauk k)) ∘
          fun w => jacobiZetak w k - jacobiLetterThetaShift p (jacobiTauk k)) := by
  funext w; simp [jacobiLetterTheta_eq_amplitude_mul]

/-- Differentiability of the indicated parameterized function: `Differentiable ℂ (fun w =>
jacobiLetterTheta p (jacobiZetak w k) (jacobiTauk k))`. -/
theorem differentiable_jacobiLetterTheta_comp_jacobiZetak {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    (p : JacobiLetter) :
    Differentiable ℂ (fun w => jacobiLetterTheta p (jacobiZetak w k) (jacobiTauk k)) := by
  rw [jacobiLetterTheta_comp_eq_amplitude_mul]
  have h1 : Differentiable ℂ (fun y => jacobiThetaOneTau y (jacobiTauk k)) :=
    DLMF.Theta.differentiable_jacobiThetaTau 1 (jacobiTauk_im_pos hk)
  have h2 : Differentiable ℂ fun w => jacobiZetak w k -
      jacobiLetterThetaShift p (jacobiTauk k) := by
    unfold jacobiZetak; fun_prop
  exact ((differentiable_jacobiLetterThetaAmplitude p _).comp
      (by unfold jacobiZetak; fun_prop)).mul (h1.comp h2)

/-- The zeros of the letter theta functions are simple. -/
private lemma meromorphicOrderAt_jacobiLetterTheta_comp_eq_one {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) (p : JacobiLetter) {z : ℂ}
    (hz : jacobiLetterTheta p (jacobiZetak z k) (jacobiTauk k) = 0) :
    meromorphicOrderAt (fun w => jacobiLetterTheta p (jacobiZetak w k) (jacobiTauk k)) z = 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hK := compEllIntKk_ne_zero hk
  have h1 : Differentiable ℂ (fun y => jacobiThetaOneTau y (jacobiTauk k)) :=
    DLMF.Theta.differentiable_jacobiThetaTau 1 hτ
  set g : ℂ → ℂ := fun w => jacobiZetak w k - jacobiLetterThetaShift p (jacobiTauk k) with hg
  have hgd : HasDerivAt g (π / (2 * compEllIntKk k)) z := by
    have := ((hasDerivAt_id z).const_mul (π / (2 * compEllIntKk k))).sub_const
      (jacobiLetterThetaShift p (jacobiTauk k))
    convert this using 1
    · funext w; simp [hg, jacobiZetak]; ring
    · simp
  have hg0 : jacobiThetaOneTau (g z) (jacobiTauk k) = 0 := by
    rw [jacobiLetterTheta_eq_amplitude_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (jacobiLetterThetaAmplitude_ne_zero hτ _ _)
  have hamp : AnalyticAt ℂ
      (fun w => jacobiLetterThetaAmplitude p (jacobiZetak w k) (jacobiTauk k)) z :=
    Differentiable.analyticAt
        ((differentiable_jacobiLetterThetaAmplitude p _).comp (by unfold jacobiZetak; fun_prop :
      Differentiable ℂ fun w => jacobiZetak w k)) z
  rw [jacobiLetterTheta_comp_eq_amplitude_mul,
      meromorphicOrderAt_mul_of_ne_zero hamp (jacobiLetterThetaAmplitude_ne_zero hτ _ _)]
  have hga : AnalyticAt ℂ g z :=
    Differentiable.analyticAt (by rw [hg]; unfold jacobiZetak; fun_prop) z
  rw [show (fun w => jacobiZetak w k - jacobiLetterThetaShift p (jacobiTauk k)) = g from rfl,
    meromorphicOrderAt_comp_of_deriv_ne_zero hga ?_]
  · have ha : AnalyticAt ℂ (fun y => jacobiThetaOneTau y (jacobiTauk k)) (g z) :=
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
theorem jacobiPQk_zeros_poles {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q : JacobiLetter}
    (hpq : p ≠ q) (z : ℂ) :
    (meromorphicOrderAt (fun w => jacobiPQk p q w k) z = 1 ↔
        z ∈ jacobiCongruentk (jacobiLetterPointk p k) k) ∧
      (meromorphicOrderAt (fun w => jacobiPQk p q w k) z = -1 ↔
        z ∈ jacobiCongruentk (jacobiLetterPointk q k) k) ∧
      (z ∉ jacobiCongruentk (jacobiLetterPointk p k) k →
        z ∉ jacobiCongruentk (jacobiLetterPointk q k) k →
        AnalyticAt ℂ (fun w => jacobiPQk p q w k) z ∧ jacobiPQk p q z k ≠ 0) := by
  have hτ := jacobiTauk_im_pos hk
  set F : JacobiLetter → ℂ → ℂ := fun r w => jacobiLetterTheta r (jacobiZetak w k) (jacobiTauk k)
    with hF
  have hFd : ∀ r, Differentiable ℂ (F r) := fun r =>
      differentiable_jacobiLetterTheta_comp_jacobiZetak hk r
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
  have heq : (fun w => jacobiPQk p q w k) = fun w => F p w / F q w := by
    funext w; simp [hF, jacobiPQk, jacobiGlaisher, hpq]
  have hdiv : meromorphicOrderAt (fun w => jacobiPQk p q w k) z =
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
  · rw [heq, show jacobiPQk p q z k = F p z / F q z from congrFun heq z]
    exact ⟨((hFd p).analyticAt z).div ((hFd q).analyticAt z) h2, div_ne_zero h1 h2⟩

/-- Periods of `sn` (Tables 22.4.1 and 22.4.2): `4K`, `2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiSnk_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSnk (z + 4 * compEllIntKk k) k = jacobiSnk z k ∧
      jacobiSnk (z + 2 * (I * compEllIntKpk k)) k = jacobiSnk z k :=
  ⟨by rw [show z + 4 * compEllIntKk k = z + 2 * compEllIntKk k + 2 * compEllIntKk k by ring,
      (jacobiSnk_shift hk _).2.2.2.1, (jacobiSnk_shift hk z).2.2.2.1, neg_neg], (jacobiSnk_shift hk
          z).2.2.2.2.2⟩

/-- Periods of `cd` (Tables 22.4.1 and 22.4.2): `4K`, `2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiCdk_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCdk (z + 4 * compEllIntKk k) k = jacobiCdk z k ∧
      jacobiCdk (z + 2 * (I * compEllIntKpk k)) k = jacobiCdk z k :=
  ⟨by rw [show z + 4 * compEllIntKk k = z + 2 * compEllIntKk k + 2 * compEllIntKk k by ring,
      (jacobiCdk_shift hk _).2.2.2.1, (jacobiCdk_shift hk z).2.2.2.1, neg_neg], (jacobiCdk_shift hk
          z).2.2.2.2.2⟩

/-- Periods of `dc` (Tables 22.4.1 and 22.4.2): `4K`, `2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiDck_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDck (z + 4 * compEllIntKk k) k = jacobiDck z k ∧
      jacobiDck (z + 2 * (I * compEllIntKpk k)) k = jacobiDck z k :=
  ⟨by rw [show z + 4 * compEllIntKk k = z + 2 * compEllIntKk k + 2 * compEllIntKk k by ring,
      (jacobiDck_shift hk _).2.2.2.1, (jacobiDck_shift hk z).2.2.2.1, neg_neg], (jacobiDck_shift hk
          z).2.2.2.2.2⟩

/-- Periods of `ns` (Tables 22.4.1 and 22.4.2): `4K`, `2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiNsk_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNsk (z + 4 * compEllIntKk k) k = jacobiNsk z k ∧
      jacobiNsk (z + 2 * (I * compEllIntKpk k)) k = jacobiNsk z k :=
  ⟨by rw [show z + 4 * compEllIntKk k = z + 2 * compEllIntKk k + 2 * compEllIntKk k by ring,
      (jacobiNsk_shift hk _).2.2.2.1, (jacobiNsk_shift hk z).2.2.2.1, neg_neg], (jacobiNsk_shift hk
          z).2.2.2.2.2⟩

/-- Periods of `cn` (Tables 22.4.1 and 22.4.2): `4K`, `2K + 2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiCnk_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCnk (z + 4 * compEllIntKk k) k = jacobiCnk z k ∧
      jacobiCnk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = jacobiCnk z k :=
  ⟨by rw [show z + 4 * compEllIntKk k = z + 2 * compEllIntKk k + 2 * compEllIntKk k by ring,
      (jacobiCnk_shift hk _).2.2.2.1, (jacobiCnk_shift hk z).2.2.2.1, neg_neg], (jacobiCnk_shift hk
          z).2.2.2.2.1⟩

/-- Periods of `sd` (Tables 22.4.1 and 22.4.2): `4K`, `2K + 2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiSdk_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSdk (z + 4 * compEllIntKk k) k = jacobiSdk z k ∧
      jacobiSdk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = jacobiSdk z k :=
  ⟨by rw [show z + 4 * compEllIntKk k = z + 2 * compEllIntKk k + 2 * compEllIntKk k by ring,
      (jacobiSdk_shift hk _).2.2.2.1, (jacobiSdk_shift hk z).2.2.2.1, neg_neg], (jacobiSdk_shift hk
          z).2.2.2.2.1⟩

/-- Periods of `nc` (Tables 22.4.1 and 22.4.2): `4K`, `2K + 2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiNck_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNck (z + 4 * compEllIntKk k) k = jacobiNck z k ∧
      jacobiNck (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = jacobiNck z k :=
  ⟨by rw [show z + 4 * compEllIntKk k = z + 2 * compEllIntKk k + 2 * compEllIntKk k by ring,
      (jacobiNck_shift hk _).2.2.2.1, (jacobiNck_shift hk z).2.2.2.1, neg_neg], (jacobiNck_shift hk
          z).2.2.2.2.1⟩

/-- Periods of `ds` (Tables 22.4.1 and 22.4.2): `4K`, `2K + 2iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiDsk_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDsk (z + 4 * compEllIntKk k) k = jacobiDsk z k ∧
      jacobiDsk (z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = jacobiDsk z k :=
  ⟨by rw [show z + 4 * compEllIntKk k = z + 2 * compEllIntKk k + 2 * compEllIntKk k by ring,
      (jacobiDsk_shift hk _).2.2.2.1, (jacobiDsk_shift hk z).2.2.2.1, neg_neg], (jacobiDsk_shift hk
          z).2.2.2.2.1⟩

/-- Periods of `dn` (Tables 22.4.1 and 22.4.2): `2K`, `4iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiDnk_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDnk (z + 2 * compEllIntKk k) k = jacobiDnk z k ∧
      jacobiDnk (z + 4 * (I * compEllIntKpk k)) k = jacobiDnk z k :=
  ⟨(jacobiDnk_shift hk z).2.2.2.1, by
    rw [show z + 4 * (I * compEllIntKpk k) =
        z + 2 * (I * compEllIntKpk k) + 2 * (I * compEllIntKpk k) by ring,
      (jacobiDnk_shift hk _).2.2.2.2.2, (jacobiDnk_shift hk z).2.2.2.2.2, neg_neg]⟩

/-- Periods of `nd` (Tables 22.4.1 and 22.4.2): `2K`, `4iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiNdk_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiNdk (z + 2 * compEllIntKk k) k = jacobiNdk z k ∧
      jacobiNdk (z + 4 * (I * compEllIntKpk k)) k = jacobiNdk z k :=
  ⟨(jacobiNdk_shift hk z).2.2.2.1, by
    rw [show z + 4 * (I * compEllIntKpk k) =
        z + 2 * (I * compEllIntKpk k) + 2 * (I * compEllIntKpk k) by ring,
      (jacobiNdk_shift hk _).2.2.2.2.2, (jacobiNdk_shift hk z).2.2.2.2.2, neg_neg]⟩

/-- Periods of `sc` (Tables 22.4.1 and 22.4.2): `2K`, `4iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiSck_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSck (z + 2 * compEllIntKk k) k = jacobiSck z k ∧
      jacobiSck (z + 4 * (I * compEllIntKpk k)) k = jacobiSck z k :=
  ⟨(jacobiSck_shift hk z).2.2.2.1, by
    rw [show z + 4 * (I * compEllIntKpk k) =
        z + 2 * (I * compEllIntKpk k) + 2 * (I * compEllIntKpk k) by ring,
      (jacobiSck_shift hk _).2.2.2.2.2, (jacobiSck_shift hk z).2.2.2.2.2, neg_neg]⟩

/-- Periods of `cs` (Tables 22.4.1 and 22.4.2): `2K`, `4iK'`. -/
@[dlmf 22.4.T1, dlmf 22.4.T2]
theorem jacobiCsk_periodic {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCsk (z + 2 * compEllIntKk k) k = jacobiCsk z k ∧
      jacobiCsk (z + 4 * (I * compEllIntKpk k)) k = jacobiCsk z k :=
  ⟨(jacobiCsk_shift hk z).2.2.2.1, by
    rw [show z + 4 * (I * compEllIntKpk k) =
        z + 2 * (I * compEllIntKpk k) + 2 * (I * compEllIntKpk k) by ring,
      (jacobiCsk_shift hk _).2.2.2.2.2, (jacobiCsk_shift hk z).2.2.2.2.2, neg_neg]⟩

end DLMF.JacobiElliptic
