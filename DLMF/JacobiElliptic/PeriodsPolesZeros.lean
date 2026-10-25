/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic

/-!
# Jacobian elliptic functions: periods, poles and zeros (DLMF §22.4)

The quarter-period shifts `z ↦ z + K`, `z ↦ z + iK'` move the theta argument `ζ = πz/(2K)` by
`π/2` and `πτ/2`. On the normalized theta functions `θ_s, θ_c, θ_d, θ_n` these act by the letter
permutations `s ↔ c, d ↔ n` and `s ↔ n, c ↔ d`, with explicit constant multipliers; this gives
the whole of Table 22.4.3 (proved in the lattice form, and in the modulus form from the admitted
inversion 22.2.2), and the periods of Tables 22.4.1–22.4.2. The location and simplicity of the
poles and zeros (the zeros of `θ_j`) are admitted.
-/

@[expose] public section

open Complex DLMF.Elliptic
open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

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

lemma JacobiLetter.swapK_injective : Function.Injective JacobiLetter.swapK := by
  intro a b h; cases a <;> cases b <;> simp_all [JacobiLetter.swapK]

lemma JacobiLetter.swapKp_injective : Function.Injective JacobiLetter.swapKp := by
  intro a b h; cases a <;> cases b <;> simp_all [JacobiLetter.swapKp]

/-- `r' = θ₄(0|τ)/θ₃(0|τ)`, a square root of `k'`. -/
def je22a_rp (τ : ℂ) : ℂ := jacobiThetaFourTau 0 τ / jacobiThetaThreeTau 0 τ

/-- `r = θ₂(0|τ)/θ₃(0|τ)`, a square root of `k`. -/
def je22a_r (τ : ℂ) : ℂ := jacobiThetaTwoTau 0 τ / jacobiThetaThreeTau 0 τ

/-- Multipliers of the normalized theta functions under `ζ ↦ ζ + π/2`. -/
def je22a_betaK (τ : ℂ) : JacobiLetter → ℂ
  | .s => (je22a_rp τ)⁻¹
  | .c => -je22a_rp τ
  | .d => je22a_rp τ
  | .n => (je22a_rp τ)⁻¹

/-- Multipliers (up to the common factor `je22a_shiftFactor`) under `ζ ↦ ζ + πτ/2`. -/
def je22a_betaKp (τ : ℂ) : JacobiLetter → ℂ
  | .s => I * (je22a_r τ)⁻¹
  | .c => (je22a_r τ)⁻¹
  | .d => je22a_r τ
  | .n => I * je22a_r τ

lemma je22a_r_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : je22a_r τ ≠ 0 :=
  div_ne_zero (je22a_thetaTwo_zero_ne_zero hτ) (je22a_thetaThree_zero_ne_zero hτ)

lemma je22a_rp_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : je22a_rp τ ≠ 0 :=
  div_ne_zero (je22a_thetaFour_zero_ne_zero hτ) (je22a_thetaThree_zero_ne_zero hτ)

lemma je22a_betaK_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) : je22a_betaK τ p ≠ 0 := by
  have := je22a_rp_ne_zero hτ
  cases p <;> simp [je22a_betaK, this]

lemma je22a_betaKp_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) :
    je22a_betaKp τ p ≠ 0 := by
  have := je22a_r_ne_zero hτ
  cases p <;> simp [je22a_betaKp, this, I_ne_zero]

lemma je22a_modulusTau_eq (τ : ℂ) : jacobiModulusTau τ = je22a_r τ ^ 2 := by
  rw [jacobiModulusTau, je22a_r, div_pow]

lemma je22a_comodulusTau_eq (τ : ℂ) : jacobiComodulusTau τ = je22a_rp τ ^ 2 := by
  rw [jacobiComodulusTau, je22a_rp, div_pow]

/-- The normalized theta functions under `ζ ↦ ζ + π/2`. -/
theorem je22a_letterTheta_add_half_pi {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) (ζ : ℂ) :
    jacobiLetterTheta p (ζ + π / 2) τ = je22a_betaK τ p * jacobiLetterTheta p.swapK ζ τ := by
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  cases p <;>
    simp only [jacobiLetterTheta, je22a_betaK, JacobiLetter.swapK, je22a_rp,
      je22a_thetaOne_add_half_pi, je22a_thetaTwo_add_half_pi, je22a_thetaThree_add_half_pi,
      je22a_thetaFour_add_half_pi] <;> field_simp

/-- The normalized theta functions under `ζ ↦ ζ + πτ/2`. -/
theorem je22a_letterTheta_add_half_tau {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) (ζ : ℂ) :
    jacobiLetterTheta p (ζ + π * τ / 2) τ =
      je22a_shiftFactor ζ τ * je22a_betaKp τ p * jacobiLetterTheta p.swapKp ζ τ := by
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  cases p <;>
    simp only [jacobiLetterTheta, je22a_betaKp, JacobiLetter.swapKp, je22a_r,
      je22a_thetaOne_add_half_tau, je22a_thetaTwo_add_half_tau, je22a_thetaThree_add_half_tau,
      je22a_thetaFour_add_half_tau] <;> field_simp

/-- Glaisher quotients under `ζ ↦ ζ + π/2`. -/
theorem je22a_glaisher_add_half_pi {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (ζ : ℂ) :
    jacobiGlaisher p q (ζ + π / 2) τ =
      je22a_betaK τ p / je22a_betaK τ q * jacobiGlaisher p.swapK q.swapK ζ τ := by
  unfold jacobiGlaisher
  by_cases hpq : p = q
  · subst hpq; simp [div_self (je22a_betaK_ne_zero hτ p)]
  · have : p.swapK ≠ q.swapK := fun h => hpq (JacobiLetter.swapK_injective h)
    simp only [hpq, this, ↓reduceIte]
    rw [je22a_letterTheta_add_half_pi hτ, je22a_letterTheta_add_half_pi hτ, mul_div_mul_comm]

/-- Glaisher quotients under `ζ ↦ ζ + πτ/2`. -/
theorem je22a_glaisher_add_half_tau {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (ζ : ℂ) :
    jacobiGlaisher p q (ζ + π * τ / 2) τ =
      je22a_betaKp τ p / je22a_betaKp τ q * jacobiGlaisher p.swapKp q.swapKp ζ τ := by
  unfold jacobiGlaisher
  by_cases hpq : p = q
  · subst hpq; simp [div_self (je22a_betaKp_ne_zero hτ p)]
  · have : p.swapKp ≠ q.swapKp := fun h => hpq (JacobiLetter.swapKp_injective h)
    simp only [hpq, this, ↓reduceIte]
    rw [je22a_letterTheta_add_half_tau hτ, je22a_letterTheta_add_half_tau hτ, mul_assoc,
      mul_assoc, mul_div_mul_left _ _ (je22a_shiftFactor_ne_zero ζ τ), mul_div_mul_comm]

lemma je22a_compEllIntKTau_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : compEllIntKTau τ ≠ 0 := by
  rw [compEllIntKTau]
  exact mul_ne_zero (div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero)
    (pow_ne_zero _ (je22a_thetaThree_zero_ne_zero hτ))

lemma je22a_zetaTau_add_K {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiZetaTau (z + compEllIntKTau τ) τ = jacobiZetaTau z τ + π / 2 := by
  have := je22a_compEllIntKTau_ne_zero hτ
  rw [jacobiZetaTau, jacobiZetaTau]; field_simp

lemma je22a_zetaTau_add_iKp {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    jacobiZetaTau (z + I * compEllIntKpTau τ) τ = jacobiZetaTau z τ + π * τ / 2 := by
  have := je22a_compEllIntKTau_ne_zero hτ
  rw [jacobiZetaTau, jacobiZetaTau, compEllIntKpTau]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- `pq(z + K) = (β_p/β_q) · (σp)(σq)(z)` in the lattice form. -/
theorem jacobiPQTau_add_K {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQTau p q (z + compEllIntKTau τ) τ =
      je22a_betaK τ p / je22a_betaK τ q * jacobiPQTau p.swapK q.swapK z τ := by
  rw [jacobiPQTau, je22a_zetaTau_add_K hτ, je22a_glaisher_add_half_pi hτ, jacobiPQTau]

/-- `pq(z + iK') = (β'_p/β'_q) · (σ'p)(σ'q)(z)` in the lattice form. -/
theorem jacobiPQTau_add_iKp {τ : ℂ} (hτ : 0 < τ.im) (p q : JacobiLetter) (z : ℂ) :
    jacobiPQTau p q (z + I * compEllIntKpTau τ) τ =
      je22a_betaKp τ p / je22a_betaKp τ q * jacobiPQTau p.swapKp q.swapKp z τ := by
  rw [jacobiPQTau, je22a_zetaTau_add_iKp hτ, je22a_glaisher_add_half_tau hτ, jacobiPQTau]

/-- Unfold the twelve lattice-form functions and apply the quarter-period shifts. -/
macro "je22a_shift_simp " h:term : tactic => `(tactic|
  simp only [jacobiSnTau, jacobiCnTau, jacobiDnTau, jacobiSdTau, jacobiCdTau, jacobiScTau,
    jacobiNsTau, jacobiNcTau, jacobiNdTau, jacobiDsTau, jacobiDcTau, jacobiCsTau,
    jacobiPQTau_add_K $h, jacobiPQTau_add_iKp $h, JacobiLetter.swapK, JacobiLetter.swapKp,
    je22a_betaK, je22a_betaKp, je22a_modulusTau_eq, je22a_comodulusTau_eq])

/-- Close a coefficient identity `a * X = b * X` produced by `je22a_shift_simp`. -/
macro "je22a_coef_tac" : tactic => `(tactic|
  ((try field_simp) <;> (try ring_nf) <;> (try simp only [I_sq, I_pow_four]) <;> (try ring_nf)))

/-- Apply the quarter-period shifts and close the resulting coefficient identity. -/
macro "je22a_shift_close " h:term : tactic => `(tactic|
  (je22a_shift_simp $h <;> je22a_coef_tac))

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

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
  have hr := je22a_r_ne_zero hτ
  have hrp := je22a_rp_ne_zero hτ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · je22a_shift_close hτ
  · rw [show z + compEllIntKTau τ + I * compEllIntKpTau τ =
        z + I * compEllIntKpTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ =
        z + compEllIntKTau τ + compEllIntKTau τ by ring]
    je22a_shift_close hτ
  · rw [show z + 2 * compEllIntKTau τ + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ + compEllIntKTau τ + compEllIntKTau τ by
            ring]
    je22a_shift_close hτ
  · rw [show z + 2 * (I * compEllIntKpTau τ) =
        z + I * compEllIntKpTau τ + I * compEllIntKpTau τ by ring]
    je22a_shift_close hτ

/-! ### Transfer to the modulus form -/

/-- `K(k) ≠ 0` on `jacobiModulusDomain` (from the admitted inversion). -/
theorem compEllIntKk_ne_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : compEllIntKk k ≠ 0 := by
  rw [← (jacobi_inversion_k hk).2.2]
  exact je22a_compEllIntKTau_ne_zero (jacobiTauk_im_pos hk)

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
macro "je22a_to_k " hk:term:max h:ident : tactic => `(tactic| (
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
  je22a_to_k hk h

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
  je22a_to_k hk h

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
  je22a_to_k hk h

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
  je22a_to_k hk h

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
  je22a_to_k hk h

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
  je22a_to_k hk h

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
  je22a_to_k hk h

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
  je22a_to_k hk h

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
  je22a_to_k hk h

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
  je22a_to_k hk h

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
  je22a_to_k hk h

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
  je22a_to_k hk h


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

/-- **Admitted.** Zeros and poles of the Jacobian elliptic functions (Tables 22.4.1–22.4.2 and
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
  sorry

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
