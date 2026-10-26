/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.SolutionsDefs
public import DLMF.Painleve.Rational

/-!
# Rational solutions of the Painlevé equations (DLMF §32.8)

DLMF normalization (`DLMF.Painleve.Defs`). The rational solutions of `PII` are bridged to the
Beals–Wong construction of `DLMF.Painleve.Rational` (`rationalPIIPair`), whose `PII(c)` is DLMF's
`PII` with `α = -c`. The explicit solutions 32.8.1–32.8.4 and the Yablonskii–Vorob'ev
polynomials 32.8.7 are proved by polynomial identities; the general statements 32.8.5–32.8.6
and 32.8.9 are admitted for general `n` and proved for small `n`. The special rational
solutions of `PIII`–`PVI` (32.8.11–32.8.13, 32.8.16–32.8.18, 32.8.24–32.8.26,
32.8.28–32.8.32) are proved on every open set avoiding the singular points; the
classification statements ("rational solutions exist iff …") are admitted.
-/

@[expose] public noncomputable section

open Polynomial Set Filter
open scoped Topology

namespace DLMF.Painleve

/-! ## Bridge to Beals–Wong -/

/-- DLMF's `PII` with parameter `α` is Beals–Wong's `PII(-α)`. -/
lemma b32_isPainleveIIOn_iff {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ} :
    IsPainleveIIOn α w U ↔ IsPIIOn (-α) w U := by
  constructor
  · intro h
    exact ⟨h.differentiableAt, fun z hz => by
      simpa [painleveIIRhs, sub_neg_eq_add] using h.hasDerivAt_deriv z hz⟩
  · intro h
    exact ⟨h.differentiableAt, fun z hz => by
      simpa [painleveIIRhs, sub_neg_eq_add] using h.hasDerivAt_deriv z hz⟩

/-- The symmetry `w ↦ -w`, `α ↦ -α` of DLMF's `PII`. -/
lemma b32_isPainleveIIOn_neg {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIOn α w U) : IsPainleveIIOn (-α) (fun z => -w z) U := by
  rw [b32_isPainleveIIOn_iff] at h ⊢
  simpa using h.neg

/-- A polynomial quotient `p/q` solves `PII` with parameter `α` on the regular set of `q`
when the polynomial identity obtained by clearing `q³` holds. -/
private lemma b32_isPainleveIIOn_rationalFn {p q : ℂ[X]} {α : ℂ}
    (H : (derivative (derivative p) * q - p * derivative (derivative q)) * q -
        2 * derivative q * (derivative p * q - p * derivative q) =
      2 * p ^ 3 + X * p * q ^ 2 + C α * q ^ 3) :
    IsPainleveIIOn α (rationalFn p q) (polynomialDomain q) := by
  apply isODE2SolutionOn_of_hasDerivAt (isOpen_polynomialDomain q)
    (v := rationalFn (derivative p * q - p * derivative q) (q ^ 2))
  · intro z hz
    have h := hasDerivAt_rationalFn p q hz
    simpa [rationalFn, eval_sub, eval_mul, eval_pow] using h
  · intro z hz
    have hz' : (q ^ 2).eval z ≠ 0 := by simpa [eval_pow] using pow_ne_zero 2 hz
    refine (hasDerivAt_rationalFn _ _ hz').congr_deriv ?_
    have He := congrArg (eval z) H
    simp only [eval_sub, eval_mul, eval_add, eval_pow, eval_X, eval_C, eval_ofNat] at He
    simp only [painleveIIRhs, rationalFn, eval_sub, eval_mul, eval_add, eval_pow,
      derivative_mul, derivative_sub, derivative_pow, eval_C, Nat.cast_ofNat]
    change q.eval z ≠ 0 at hz
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp
    linear_combination He

/-! ## `PII`: existence for integral parameters (§32.8(ii)) -/

/-- DLMF §32.8(ii): `PII` has rational solutions for every integral `α = n`, generated from the
seed `w(z; 0) = 0` by the Bäcklund transformations 32.7.1–32.7.2. The solution is a polynomial
quotient `p/q` with `q ≠ 0`, on the full regular set of `q`. Proved from the Beals–Wong
construction `exists_rational_solution_int`. -/
@[dlmf 32.8.ii]
theorem painleveII_exists_rational_int (n : ℤ) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ IsPainleveIIOn (n : ℂ) (rationalFn p q) (polynomialDomain q) := by
  obtain ⟨p, q, hq, h⟩ := exists_rational_solution_int (-n)
  exact ⟨p, q, hq, b32_isPainleveIIOn_iff.mpr (by simpa using h)⟩

/-- DLMF 32.8.1: `w(z; 1) = -1/z` solves `PII` with `α = 1` for `z ≠ 0`. -/
@[dlmf 32.8.E1]
theorem painleveII_rational_one :
    IsPainleveIIOn 1 (fun z => -1 / z) {z | z ≠ 0} := by
  have h := isPIIOn_recip (𝕜 := ℂ)
  have h' : IsPainleveIIOn (-1) (fun z : ℂ => z⁻¹) {z | z ≠ 0} :=
    b32_isPainleveIIOn_iff.mpr (by simpa using h)
  simpa [neg_div, one_div] using b32_isPainleveIIOn_neg h'

/-! ## The Yablonskii–Vorob'ev polynomials (32.8.5–32.8.7) -/

/-- Polynomial differentiation of explicit polynomials. -/
local macro "b32_pd" : tactic =>
  `(tactic| (simp only [derivative_add, derivative_sub, derivative_mul, derivative_X_pow,
      derivative_X, derivative_ofNat, derivative_one, derivative_zero, derivative_neg, map_natCast,
      mul_one, zero_mul, mul_zero, add_zero, zero_add, sub_zero]) <;>
    first | (norm_num; done) | (norm_num; ring) | ring)

/-- One step of the recurrence 32.8.6: if `Q_{n+1} Q_{n-1}` equals the right-hand side then
`yablonskiiVorobievQ (n + 2)` is that polynomial. -/
private lemma b32_Q_step {n : ℕ} {R : ℂ[X]} (hn : yablonskiiVorobievQ n ≠ 0)
    (h : X * yablonskiiVorobievQ (n + 1) ^ 2 +
        C 4 * (derivative (yablonskiiVorobievQ (n + 1))) ^ 2 -
        C 4 * yablonskiiVorobievQ (n + 1) * derivative (derivative (yablonskiiVorobievQ (n + 1))) =
      R * yablonskiiVorobievQ n) :
    yablonskiiVorobievQ (n + 2) = R := by
  rw [yablonskiiVorobievQ, h, mul_div_cancel_right₀ _ hn]

private lemma b32_C4 : (C 4 : ℂ[X]) = 4 := rfl

/-- DLMF 32.8.7: `Q₂(z) = z³ + 4`. -/
@[dlmf 32.8.E7]
theorem yablonskiiVorobievQ_two : yablonskiiVorobievQ 2 = X ^ 3 + 4 := by
  apply b32_Q_step (n := 0) one_ne_zero
  simp only [yablonskiiVorobievQ, derivative_X, derivative_one, b32_C4]
  ring

/-- DLMF 32.8.7: `Q₃(z) = z⁶ + 20z³ - 80`. -/
@[dlmf 32.8.E7]
theorem yablonskiiVorobievQ_three : yablonskiiVorobievQ 3 = X ^ 6 + 20 * X ^ 3 - 80 := by
  apply b32_Q_step (n := 1) X_ne_zero
  have h1 : derivative (X ^ 3 + 4 : ℂ[X]) = 3 * X ^ 2 := by b32_pd
  have h2 : derivative (3 * X ^ 2 : ℂ[X]) = 6 * X := by b32_pd
  rw [yablonskiiVorobievQ_two, h1, h2, b32_C4]
  simp only [yablonskiiVorobievQ]
  ring

private lemma b32_Q2_ne : (X ^ 3 + 4 : ℂ[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  simp at this

private lemma b32_Q3_ne : (X ^ 6 + 20 * X ^ 3 - 80 : ℂ[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  norm_num at this

private lemma b32_Q4_ne : (X ^ 10 + 60 * X ^ 7 + 11200 * X : ℂ[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 1) h
  norm_num at this

private lemma b32_Q5_ne : (X ^ 15 + 140 * X ^ 12 + 2800 * X ^ 9 + 78400 * X ^ 6 - 3136000 * X ^ 3 -
    6272000 : ℂ[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  norm_num at this

/-- DLMF 32.8.7: `Q₄(z) = z¹⁰ + 60z⁷ + 11200z`. -/
@[dlmf 32.8.E7]
theorem yablonskiiVorobievQ_four :
    yablonskiiVorobievQ 4 = X ^ 10 + 60 * X ^ 7 + 11200 * X := by
  apply b32_Q_step (n := 2) (by rw [yablonskiiVorobievQ_two]; exact b32_Q2_ne)
  have h1 : derivative (X ^ 6 + 20 * X ^ 3 - 80 : ℂ[X]) = 6 * X ^ 5 + 60 * X ^ 2 := by b32_pd
  have h2 : derivative (6 * X ^ 5 + 60 * X ^ 2 : ℂ[X]) = 30 * X ^ 4 + 120 * X := by b32_pd
  rw [yablonskiiVorobievQ_three, yablonskiiVorobievQ_two, h1, h2, b32_C4]
  ring

/-- DLMF 32.8.7: `Q₅(z) = z¹⁵ + 140z¹² + 2800z⁹ + 78400z⁶ - 3136000z³ - 6272000`. -/
@[dlmf 32.8.E7]
theorem yablonskiiVorobievQ_five :
    yablonskiiVorobievQ 5 = X ^ 15 + 140 * X ^ 12 + 2800 * X ^ 9 + 78400 * X ^ 6 -
      3136000 * X ^ 3 - 6272000 := by
  apply b32_Q_step (n := 3) (by rw [yablonskiiVorobievQ_three]; exact b32_Q3_ne)
  have h1 : derivative (X ^ 10 + 60 * X ^ 7 + 11200 * X : ℂ[X]) =
      10 * X ^ 9 + 420 * X ^ 6 + 11200 := by b32_pd
  have h2 : derivative (10 * X ^ 9 + 420 * X ^ 6 + 11200 : ℂ[X]) =
      90 * X ^ 8 + 2520 * X ^ 5 := by b32_pd
  rw [yablonskiiVorobievQ_four, yablonskiiVorobievQ_three, h1, h2, b32_C4]
  ring

/-- DLMF 32.8.7: `Q₆(z) = z²¹ + 280z¹⁸ + 18480z¹⁵ + 627200z¹² - 17248000z⁹ + 1448832000z⁶ +
19317760000z³ - 38635520000`. -/
@[dlmf 32.8.E7]
theorem yablonskiiVorobievQ_six :
    yablonskiiVorobievQ 6 = X ^ 21 + 280 * X ^ 18 + 18480 * X ^ 15 + 627200 * X ^ 12 -
      17248000 * X ^ 9 + 1448832000 * X ^ 6 + 19317760000 * X ^ 3 - 38635520000 := by
  apply b32_Q_step (n := 4) (by rw [yablonskiiVorobievQ_four]; exact b32_Q4_ne)
  have h1 : derivative (X ^ 15 + 140 * X ^ 12 + 2800 * X ^ 9 + 78400 * X ^ 6 -
      3136000 * X ^ 3 - 6272000 : ℂ[X]) =
      15 * X ^ 14 + 1680 * X ^ 11 + 25200 * X ^ 8 + 470400 * X ^ 5 - 9408000 * X ^ 2 := by
    b32_pd
  have h2 : derivative (15 * X ^ 14 + 1680 * X ^ 11 + 25200 * X ^ 8 + 470400 * X ^ 5 -
      9408000 * X ^ 2 : ℂ[X]) =
      210 * X ^ 13 + 18480 * X ^ 10 + 201600 * X ^ 7 + 2352000 * X ^ 4 - 18816000 * X := by
    b32_pd
  rw [yablonskiiVorobievQ_five, yablonskiiVorobievQ_four, h1, h2, b32_C4]
  ring

/-! ## Explicit rational solutions of `PII` (32.8.1–32.8.4) -/

/-- Equality on an open set transports DLMF's `PII`. -/
lemma b32_congr {α : ℂ} {w w' : ℂ → ℂ} {U : Set ℂ} (h : IsPainleveIIOn α w U)
    (hU : IsOpen U) (he : EqOn w w' U) : IsPainleveIIOn α w' U :=
  b32_isPainleveIIOn_iff.mpr ((b32_isPainleveIIOn_iff.mp h).congr hU he)

/-- A difference of logarithmic derivatives `A₁/A - B₁/B` of polynomials (with `A₁` the
derivative of `A`, `A₂` that of `A₁`, `A₃` that of `A₂`, similarly for `B`) solves `PII` where
`AB ≠ 0`, given the polynomial identity obtained after clearing denominators. -/
private lemma b32_isPainleveIIOn_logDeriv {A B A1 A2 A3 B1 B2 B3 : ℂ[X]} {α : ℂ}
    (hA1 : derivative A = A1) (hA2 : derivative A1 = A2) (hA3 : derivative A2 = A3)
    (hB1 : derivative B = B1) (hB2 : derivative B1 = B2) (hB3 : derivative B2 = B3)
    (H : ((A3 * B + A2 * B1 - A1 * B2 - A * B3) * (A * B) -
          (A1 * B - A * B1) * (A2 * B + 2 * A1 * B1 + A * B2)) * (A * B) -
        2 * (A1 * B + A * B1) *
          ((A2 * B - A * B2) * (A * B) - (A1 * B - A * B1) * (A1 * B + A * B1)) =
      2 * (A1 * B - A * B1) ^ 3 + X * (A1 * B - A * B1) * (A * B) ^ 2 + C α * (A * B) ^ 3) :
    IsPainleveIIOn α (fun z => A1.eval z / A.eval z - B1.eval z / B.eval z)
      {z | A.eval z ≠ 0 ∧ B.eval z ≠ 0} := by
  set p := derivative A * B - A * derivative B
  set q := A * B
  have e1 : derivative p = A2 * B - A * B2 := by
    simp only [p, derivative_mul, derivative_sub, hA1, hA2, hB1, hB2]; ring
  have e2 : derivative (derivative p) = A3 * B + A2 * B1 - A1 * B2 - A * B3 := by
    rw [e1]; simp only [derivative_mul, derivative_sub, hA1, hA3, hB1, hB3]; ring
  have e3 : derivative q = A1 * B + A * B1 := by
    simp only [q, derivative_mul, hA1, hB1]
  have e4 : derivative (derivative q) = A2 * B + 2 * A1 * B1 + A * B2 := by
    rw [e3]; simp only [derivative_mul, derivative_add, hA1, hA2, hB1, hB2]; ring
  have hp : p = A1 * B - A * B1 := by simp only [p, hA1, hB1]
  have h := b32_isPainleveIIOn_rationalFn (p := p) (q := q) (α := α) (by
    rw [e2, e4, e1, e3, hp]; exact H)
  have hdom : polynomialDomain q = {z | A.eval z ≠ 0 ∧ B.eval z ≠ 0} := by
    ext z; simp [polynomialDomain, q, eval_mul]
  rw [hdom] at h
  refine b32_congr h (hdom ▸ isOpen_polynomialDomain q) fun z hz => ?_
  obtain ⟨ha, hb⟩ := hz
  simp only [rationalFn, hp, q, eval_sub, eval_mul]
  field_simp

private lemma b32_isOpen_ne_poly (P : ℂ[X]) : IsOpen {z : ℂ | P.eval z ≠ 0} :=
  isOpen_ne_fun P.continuous continuous_const

/-- DLMF 32.8.2: `w(z; 2) = 1/z - 3z²/(z³ + 4)` solves `PII` with `α = 2` where
`z(z³ + 4) ≠ 0`. -/
@[dlmf 32.8.E2]
theorem painleveII_rational_two :
    IsPainleveIIOn 2 (fun z => 1 / z - 3 * z ^ 2 / (z ^ 3 + 4)) {z | z ≠ 0 ∧ z ^ 3 + 4 ≠ 0} := by
  have h := b32_isPainleveIIOn_logDeriv (α := 2) (A := X) (B := X ^ 3 + 4) (A1 := 1) (A2 := 0)
    (A3 := 0) (B1 := 3 * X ^ 2) (B2 := 6 * X) (B3 := 6) (by b32_pd) (by b32_pd) (by b32_pd)
    (by b32_pd) (by b32_pd) (by b32_pd) (by rw [show (C 2 : ℂ[X]) = 2 from rfl]; ring)
  have hs : {z : ℂ | (X : ℂ[X]).eval z ≠ 0 ∧ (X ^ 3 + 4 : ℂ[X]).eval z ≠ 0} =
      {z | z ≠ 0 ∧ z ^ 3 + 4 ≠ 0} := by ext z; simp
  rw [hs] at h
  refine b32_congr h ?_ fun z _ => ?_
  · rw [← hs]; exact (b32_isOpen_ne_poly _).inter (b32_isOpen_ne_poly _)
  · simp

/-- DLMF 32.8.3: `w(z; 3) = 3z²/(z³ + 4) - 6z²(z³ + 10)/(z⁶ + 20z³ - 80)` solves `PII` with
`α = 3` where the denominators do not vanish. -/
@[dlmf 32.8.E3]
theorem painleveII_rational_three :
    IsPainleveIIOn 3 (fun z => 3 * z ^ 2 / (z ^ 3 + 4) -
        6 * z ^ 2 * (z ^ 3 + 10) / (z ^ 6 + 20 * z ^ 3 - 80))
      {z | z ^ 3 + 4 ≠ 0 ∧ z ^ 6 + 20 * z ^ 3 - 80 ≠ 0} := by
  have h := b32_isPainleveIIOn_logDeriv (α := 3) (A := X ^ 3 + 4) (B := X ^ 6 + 20 * X ^ 3 - 80)
    (A1 := 3 * X ^ 2) (A2 := 6 * X) (A3 := 6) (B1 := 6 * X ^ 5 + 60 * X ^ 2)
    (B2 := 30 * X ^ 4 + 120 * X) (B3 := 120 * X ^ 3 + 120) (by b32_pd) (by b32_pd) (by b32_pd)
    (by b32_pd) (by b32_pd) (by b32_pd) (by rw [show (C 3 : ℂ[X]) = 3 from rfl]; ring)
  have hs : {z : ℂ | (X ^ 3 + 4 : ℂ[X]).eval z ≠ 0 ∧
      (X ^ 6 + 20 * X ^ 3 - 80 : ℂ[X]).eval z ≠ 0} =
      {z | z ^ 3 + 4 ≠ 0 ∧ z ^ 6 + 20 * z ^ 3 - 80 ≠ 0} := by ext z; simp
  rw [hs] at h
  refine b32_congr h ?_ fun z _ => ?_
  · rw [← hs]; exact (b32_isOpen_ne_poly _).inter (b32_isOpen_ne_poly _)
  · simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_sub]
    ring

/-- DLMF 32.8.4: `w(z; 4) = -1/z + 6z²(z³ + 10)/(z⁶ + 20z³ - 80) - 9z⁵(z³ + 40)/(z⁹ + 60z⁶ +
11200)` solves `PII` with `α = 4` where the denominators do not vanish. -/
@[dlmf 32.8.E4]
theorem painleveII_rational_four :
    IsPainleveIIOn 4 (fun z => -1 / z + 6 * z ^ 2 * (z ^ 3 + 10) / (z ^ 6 + 20 * z ^ 3 - 80) -
        9 * z ^ 5 * (z ^ 3 + 40) / (z ^ 9 + 60 * z ^ 6 + 11200))
      {z | z ≠ 0 ∧ z ^ 6 + 20 * z ^ 3 - 80 ≠ 0 ∧ z ^ 9 + 60 * z ^ 6 + 11200 ≠ 0} := by
  have h := b32_isPainleveIIOn_logDeriv (α := 4) (A := X ^ 6 + 20 * X ^ 3 - 80)
    (B := X ^ 10 + 60 * X ^ 7 + 11200 * X)
    (A1 := 6 * X ^ 5 + 60 * X ^ 2) (A2 := 30 * X ^ 4 + 120 * X) (A3 := 120 * X ^ 3 + 120)
    (B1 := 10 * X ^ 9 + 420 * X ^ 6 + 11200) (B2 := 90 * X ^ 8 + 2520 * X ^ 5)
    (B3 := 720 * X ^ 7 + 12600 * X ^ 4) (by b32_pd) (by b32_pd) (by b32_pd)
    (by b32_pd) (by b32_pd) (by b32_pd) (by rw [show (C 4 : ℂ[X]) = 4 from rfl]; ring)
  have hs : {z : ℂ | (X ^ 6 + 20 * X ^ 3 - 80 : ℂ[X]).eval z ≠ 0 ∧
      (X ^ 10 + 60 * X ^ 7 + 11200 * X : ℂ[X]).eval z ≠ 0} =
      {z | z ≠ 0 ∧ z ^ 6 + 20 * z ^ 3 - 80 ≠ 0 ∧ z ^ 9 + 60 * z ^ 6 + 11200 ≠ 0} := by
    ext z
    simp only [mem_ofPred_eq, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_sub]
    have : z ^ 10 + 60 * z ^ 7 + 11200 * z = z * (z ^ 9 + 60 * z ^ 6 + 11200) := by ring
    rw [this, mul_ne_zero_iff]
    tauto
  rw [hs] at h
  refine b32_congr h ?_ fun z hz => ?_
  · rw [← hs]; exact (b32_isOpen_ne_poly _).inter (b32_isOpen_ne_poly _)
  · obtain ⟨h0, h1, h2⟩ := hz
    have h3 : z ^ 10 + 60 * z ^ 7 + 11200 * z ≠ 0 := by
      rw [show z ^ 10 + 60 * z ^ 7 + 11200 * z = z * (z ^ 9 + 60 * z ^ 6 + 11200) by ring]
      exact mul_ne_zero h0 h2
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_sub]
    rw [div_sub_div _ _ h1 h3, div_add_div _ _ h0 h1, div_sub_div _ _ (mul_ne_zero h0 h1) h2,
      div_eq_div_iff (mul_ne_zero h1 h3) (mul_ne_zero (mul_ne_zero h0 h1) h2)]
    ring

/-! ## General statements on the Yablonskii–Vorob'ev polynomials (32.8.5–32.8.10) -/

/-- DLMF 32.8.6: the division in the recurrence is exact, `Q_{n+1}Q_{n-1} = zQ_n² + 4(Q_n')² -
4Q_nQ_n''` for `n ≥ 1` (here with `n + 1` in place of `n`), and every `Q_n` is monic.
Verified for `n ≤ 5` by `yablonskiiVorobievQ_two` … `yablonskiiVorobievQ_six`. -/
@[dlmf 32.8.E6]
theorem yablonskiiVorobievQ_recurrence (n : ℕ) :
    yablonskiiVorobievQ (n + 2) * yablonskiiVorobievQ n =
        X * yablonskiiVorobievQ (n + 1) ^ 2 +
          C 4 * (derivative (yablonskiiVorobievQ (n + 1))) ^ 2 -
          C 4 * yablonskiiVorobievQ (n + 1) *
            derivative (derivative (yablonskiiVorobievQ (n + 1))) ∧
      (yablonskiiVorobievQ (n + 2)).Monic := by
  sorry

/-- DLMF 32.8.5: for `n ≥ 1`, `w(z; n) = d/dz ln(Q_{n-1}(z)/Q_n(z))` solves `PII` with `α = n`
on the set where `Q_{n-1}Q_n ≠ 0` (the logarithmic derivative is taken as
`Q_{n-1}'/Q_{n-1} - Q_n'/Q_n`, so no branch of `ln` enters). Proved for `n ≤ 4` in the explicit
forms `painleveII_rational_one` … `painleveII_rational_four`. -/
@[dlmf 32.8.E5]
theorem rationalPainleveII_isPainleveIIOn (n : ℕ) (hn : 1 ≤ n) :
    IsPainleveIIOn (n : ℂ) (rationalPainleveII n)
      {z | (yablonskiiVorobievQ (n - 1)).eval z ≠ 0 ∧ (yablonskiiVorobievQ n).eval z ≠ 0} := by
  sorry

/-- DLMF 32.8.5 for every integer `n`, including the seed `n = 0` and, for `n < 0`, the
symmetric solutions `w(z; n) = -w(z; -n)`. Proved from `rationalPainleveII_isPainleveIIOn`. -/
@[dlmf 32.8.E5]
theorem rationalPainleveII_isPainleveIIOn_int (n : ℤ) :
    IsPainleveIIOn (n : ℂ) (rationalPainleveII n)
      {z | (yablonskiiVorobievQ (n.natAbs - 1)).eval z ≠ 0 ∧
        (yablonskiiVorobievQ n.natAbs).eval z ≠ 0} := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
    have h := b32_isPainleveIIOn_neg (rationalPainleveII_isPainleveIIOn (m + 1) (by omega))
    have habs : (-((m : ℤ) + 1)).natAbs = m + 1 := by omega
    rw [habs]
    convert h using 1
    · push_cast; ring
    · funext z
      have h1 : ¬ (0 : ℤ) < -((m : ℤ) + 1) := by omega
      have h2 : -((m : ℤ) + 1) ≠ 0 := by omega
      have h3 : (-(-((m : ℤ) + 1))).toNat = m + 1 := by omega
      have h4 : (0 : ℤ) < ((m + 1 : ℕ) : ℤ) := by omega
      have h5 : ((m + 1 : ℕ) : ℤ).toNat = m + 1 := by omega
      simp only [rationalPainleveII, h1, h2, h3, h4, h5, ite_false, ite_true]
  · have he : rationalPainleveII 0 = fun _ => 0 := by
      funext z; simp [rationalPainleveII]
    rw [he]
    refine ⟨fun _ _ => differentiableAt_const _, fun z _ => ?_⟩
    simpa [painleveIIRhs] using hasDerivAt_const z (0 : ℂ)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
    simpa using rationalPainleveII_isPainleveIIOn m (by omega)

/-- DLMF 32.8.8: the generating function `∑_{m ≥ 0} p_m(z) λ^m = exp(zλ - (4/3)λ³)`, for all
complex `z` and `λ`. -/
@[dlmf 32.8.E8]
theorem hasSum_yablonskiiVorobievP (z l : ℂ) :
    HasSum (fun m : ℕ => (yablonskiiVorobievP m).eval z * l ^ m)
      (Complex.exp (z * l - 4 / 3 * l ^ 3)) := by
  sorry

/-- DLMF 32.8.9–32.8.10: for `n ≥ 2` (in fact `n ≥ 1`) the Wronskians `τ_n` of
`p₁, p₃, …, p_{2n-1}` give `w(z; n) = d/dz ln(τ_{n-1}(z)/τ_n(z))`, a solution of `PII` with
`α = n` where `τ_{n-1}τ_n ≠ 0`. (In fact `τ_n` is a nonzero constant multiple of `Q_n`.) -/
@[dlmf 32.8.E9]
theorem yablonskiiVorobievTau_isPainleveIIOn (n : ℕ) (hn : 2 ≤ n) :
    IsPainleveIIOn (n : ℂ)
      (fun z => (derivative (yablonskiiVorobievTau (n - 1))).eval z /
          (yablonskiiVorobievTau (n - 1)).eval z -
        (derivative (yablonskiiVorobievTau n)).eval z / (yablonskiiVorobievTau n).eval z)
      {z | (yablonskiiVorobievTau (n - 1)).eval z ≠ 0 ∧ (yablonskiiVorobievTau n).eval z ≠ 0} := by
  sorry

/-! ## Special rational solutions of `PIII` (32.8.11–32.8.15) -/

/-- DLMF 32.8.11: the constant `w = κ` solves `PIII` with parameters `(μ, -μκ², λ, -λκ⁴)` on
every open set avoiding `z = 0`, for `κ ≠ 0` (`PIII` divides by `w`). -/
@[dlmf 32.8.E11]
theorem painleveIII_rational_const {μ κ l : ℂ} {U : Set ℂ} (hU : IsOpen U) (hκ : κ ≠ 0)
    (h0 : ∀ z ∈ U, z ≠ 0) :
    IsPainleveIIIOn μ (-μ * κ ^ 2) l (-l * κ ^ 4) (fun _ => κ) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun _ => 0)
    (fun z _ => hasDerivAt_const z κ) (fun z hz => ?_), h0, fun _ _ => hκ⟩
  have hz' := h0 z hz
  convert hasDerivAt_const z (0 : ℂ) using 1
  simp only [painleveIIIRhs]
  field_simp
  ring

/-- DLMF 32.8.12: `w = κz` solves `PIII` with parameters `(0, -μ, 0, μκ)` on every open set
avoiding `z = 0`, for `κ ≠ 0`. -/
@[dlmf 32.8.E12]
theorem painleveIII_rational_linear {μ κ : ℂ} {U : Set ℂ} (hU : IsOpen U) (hκ : κ ≠ 0)
    (h0 : ∀ z ∈ U, z ≠ 0) :
    IsPainleveIIIOn 0 (-μ) 0 (μ * κ) (fun z => κ * z) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun _ => κ)
    (fun z _ => by simpa using (hasDerivAt_id z).const_mul κ) (fun z hz => ?_), h0,
    fun z hz => mul_ne_zero hκ (h0 z hz)⟩
  have hz' := h0 z hz
  convert hasDerivAt_const z κ using 1
  simp only [painleveIIIRhs]
  field_simp
  ring

/-- DLMF 32.8.13: `w = (z + κ)/(z + κ + 1)` solves `PIII` with parameters
`(2κ + 3, -2κ + 1, 1, -1)` on every open set avoiding `z = 0`, `z = -κ` and `z = -κ - 1`. -/
@[dlmf 32.8.E13]
theorem painleveIII_rational_mobius {κ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z + κ ≠ 0) (h2 : ∀ z ∈ U, z + κ + 1 ≠ 0) :
    IsPainleveIIIOn (2 * κ + 3) (-2 * κ + 1) 1 (-1) (fun z => (z + κ) / (z + κ + 1)) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => 1 / (z + κ + 1) ^ 2)
    (fun z hz => ?_) (fun z hz => ?_), h0, fun z hz => div_ne_zero (h1 z hz) (h2 z hz)⟩
  · have h := ((hasDerivAt_id z).add_const κ).div (((hasDerivAt_id z).add_const κ).add_const 1)
      (h2 z hz)
    refine h.congr_deriv ?_
    have := h2 z hz
    simp only [id_eq]
    field_simp
    ring
  · have h := (hasDerivAt_const z (1 : ℂ)).div
      ((((hasDerivAt_id z).add_const κ).add_const 1).pow 2) (pow_ne_zero 2 (h2 z hz))
    refine h.congr_deriv ?_
    have := h2 z hz; have := h1 z hz; have := h0 z hz
    simp only [painleveIIIRhs, id_eq, Pi.pow_apply]
    field_simp
    ring

/-- DLMF 32.8.14: with `γ = 1`, `δ = -1` (the normalization of §32.2(ii) when `γδ ≠ 0`),
`PIII` has a rational solution (on some nonempty open set) iff `α + β = 4n` or `α - β = 4n` for
some `n ∈ ℤ`. -/
@[dlmf 32.8.E14]
theorem painleveIII_exists_rational_iff (α β : ℂ) :
    (∃ (w : ℂ → ℂ) (U : Set ℂ), IsOpen U ∧ U.Nonempty ∧ IsRationalOn w U ∧
        IsPainleveIIIOn α β 1 (-1) w U) ↔
      ∃ n : ℤ, α + β = 4 * n ∨ α - β = 4 * n := by
  sorry

/-- DLMF 32.8.15: with `γ = 1`, `δ = -1`, every rational solution of `PIII` is `P_m/Q_m` with
polynomials `P_m`, `Q_m` of the same degree `m` and without common zeros. -/
@[dlmf 32.8.E15]
theorem painleveIII_rational_form {α β : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hne : U.Nonempty) (hrat : IsRationalOn w U) (h : IsPainleveIIIOn α β 1 (-1) w U) :
    ∃ (m : ℕ) (P Q : ℂ[X]), P.natDegree = m ∧ Q.natDegree = m ∧ IsCoprime P Q ∧
      ∀ z ∈ U, Q.eval z ≠ 0 ∧ w z = P.eval z / Q.eval z := by
  sorry

/-! ## Special rational solutions of `PIV` (32.8.16–32.8.23) -/

/-- DLMF 32.8.16: `w₁ = 1/z` solves `PIV` with `(α, β) = (2, -2)` for `z ≠ 0`. -/
@[dlmf 32.8.E16]
theorem painleveIV_rational_inv {U : Set ℂ} (hU : IsOpen U) (h0 : ∀ z ∈ U, z ≠ 0) :
    IsPainleveIVOn 2 (-2) (fun z => 1 / z) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => -1 / z ^ 2) (fun z hz => ?_)
    (fun z hz => ?_), fun z hz => one_div_ne_zero (h0 z hz)⟩
  · have := h0 z hz
    exact ((hasDerivAt_inv this).congr_deriv (by field_simp)).congr_of_eventuallyEq
      (Eventually.of_forall fun y => one_div y)
  · have := h0 z hz
    refine ((hasDerivAt_const z (-1 : ℂ)).div ((hasDerivAt_id z).pow 2)
      (pow_ne_zero 2 this)).congr_deriv ?_
    simp only [painleveIVRhs, id_eq, Pi.pow_apply]
    field_simp
    ring

/-- DLMF 32.8.16: `w₁ = -1/z` solves `PIV` with `(α, β) = (-2, -2)` for `z ≠ 0`. -/
@[dlmf 32.8.E16]
theorem painleveIV_rational_neg_inv {U : Set ℂ} (hU : IsOpen U) (h0 : ∀ z ∈ U, z ≠ 0) :
    IsPainleveIVOn (-2) (-2) (fun z => -1 / z) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => 1 / z ^ 2) (fun z hz => ?_)
    (fun z hz => ?_), fun z hz => div_ne_zero (neg_ne_zero.mpr one_ne_zero) (h0 z hz)⟩
  · have := h0 z hz
    exact ((hasDerivAt_inv this).neg.congr_deriv (by field_simp)).congr_of_eventuallyEq
      (Eventually.of_forall fun y => by simp [neg_div])
  · have := h0 z hz
    refine ((hasDerivAt_const z (1 : ℂ)).div ((hasDerivAt_id z).pow 2)
      (pow_ne_zero 2 this)).congr_deriv ?_
    simp only [painleveIVRhs, id_eq, Pi.pow_apply]
    field_simp
    ring

/-- A linear function `w = cz` solves `PIV` with `α = 0` and `β = -2c²(1 + c)(2 + 3c)/…`;
we only need the two cases of DLMF 32.8.17–32.8.18. -/
private lemma b32_painleveIV_linear {c α β : ℂ} {U : Set ℂ} (hU : IsOpen U) (hc : c ≠ 0)
    (h0 : ∀ z ∈ U, z ≠ 0)
    (H : ∀ z : ℂ, z ≠ 0 → (0 : ℂ) = painleveIVRhs α β z (c * z) c) :
    IsPainleveIVOn α β (fun z => c * z) U :=
  ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun _ => c)
    (fun z _ => by simpa using (hasDerivAt_id z).const_mul c)
    (fun z hz => (H z (h0 z hz)) ▸ hasDerivAt_const z c),
    fun z hz => mul_ne_zero hc (h0 z hz)⟩

/-- DLMF 32.8.17: `w₂ = -2z` solves `PIV` with `(α, β) = (0, -2)` for `z ≠ 0`. -/
@[dlmf 32.8.E17]
theorem painleveIV_rational_neg_two_mul {U : Set ℂ} (hU : IsOpen U) (h0 : ∀ z ∈ U, z ≠ 0) :
    IsPainleveIVOn 0 (-2) (fun z => -2 * z) U :=
  b32_painleveIV_linear hU (by norm_num) h0 fun z hz => by
    simp only [painleveIVRhs]; field_simp; ring

/-- DLMF 32.8.18: `w₃ = -(2/3)z` solves `PIV` with `(α, β) = (0, -2/9)` for `z ≠ 0`. -/
@[dlmf 32.8.E18]
theorem painleveIV_rational_neg_two_thirds_mul {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) :
    IsPainleveIVOn 0 (-2 / 9) (fun z => -2 / 3 * z) U :=
  b32_painleveIV_linear hU (by norm_num) h0 fun z hz => by
    simp only [painleveIVRhs]; field_simp; ring

/-- DLMF 32.8.19–32.8.21: every rational solution of `PIV` belongs to one of three families,
`w₁ = P_{1,n-1}/Q_{1,n}`, `w₂ = -2z + P_{2,n-1}/Q_{2,n}`, `w₃ = -(2/3)z + P_{3,n-1}/Q_{3,n}`,
with `deg Q = n`, `deg P = n - 1` (`P = 0` when `n = 0`) and no common zeros. (DLMF states the
existence of three such families; the precise statement is the classification of the rational
solutions, due to Murata (1985).) -/
@[dlmf 32.8.E19, dlmf 32.8.E20, dlmf 32.8.E21]
theorem painleveIV_rational_form {α β : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hne : U.Nonempty) (hrat : IsRationalOn w U) (h : IsPainleveIVOn α β w U) :
    ∃ (n : ℕ) (P Q : ℂ[X]) (c : ℂ), (c = 0 ∨ c = -2 ∨ c = -2 / 3) ∧ Q.natDegree = n ∧
      ((n = 0 ∧ P = 0) ∨ P.natDegree + 1 = n) ∧ IsCoprime P Q ∧
      ∀ z ∈ U, Q.eval z ≠ 0 ∧ w z = c * z + P.eval z / Q.eval z := by
  sorry

/-- DLMF 32.8.22–32.8.23: `PIV` has a rational solution iff `α = m`, `β = -2(1 + 2n - m)²` or
`α = m`, `β = -2(1/3 + 2n - m)²`, with `m, n ∈ ℤ`. -/
@[dlmf 32.8.E22, dlmf 32.8.E23]
theorem painleveIV_exists_rational_iff (α β : ℂ) :
    (∃ (w : ℂ → ℂ) (U : Set ℂ), IsOpen U ∧ U.Nonempty ∧ IsRationalOn w U ∧
        IsPainleveIVOn α β w U) ↔
      ∃ m n : ℤ, α = m ∧ (β = -2 * (1 + 2 * n - m) ^ 2 ∨ β = -2 * (1 / 3 + 2 * n - m) ^ 2) := by
  sorry

/-! ## Special rational solutions of `PV` (32.8.24–32.8.27) -/

/-- DLMF 32.8.24: `w = κz + μ` solves `PV` with parameters `(1/2, -μ²/2, κ(2 - μ), -κ²/2)` on
every open set avoiding `z = 0` and the points where `w ∈ {0, 1}`. -/
@[dlmf 32.8.E24]
theorem painleveV_rational_linear {κ μ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, κ * z + μ ≠ 0) (h2 : ∀ z ∈ U, κ * z + μ ≠ 1) :
    IsPainleveVOn (1 / 2) (-μ ^ 2 / 2) (κ * (2 - μ)) (-κ ^ 2 / 2) (fun z => κ * z + μ) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun _ => κ)
    (fun z _ => by simpa using ((hasDerivAt_id z).const_mul κ).add_const μ)
    (fun z hz => ?_), h0, h1, h2⟩
  have hz' := h0 z hz; have hw := h1 z hz; have hw1 := sub_ne_zero.mpr (h2 z hz)
  convert hasDerivAt_const z κ using 1
  simp only [painleveVRhs]
  field_simp
  ring

/-- DLMF 32.8.25: `w = κ/(z + κ)` solves `PV` with parameters `(1/2, κ²μ, 2κμ, μ)` on every open
set avoiding `z = 0`, `z = -κ` and `z = 0` of `w - 1` (i.e. `z ≠ 0` again), for `κ ≠ 0`. -/
@[dlmf 32.8.E25]
theorem painleveV_rational_mobius {κ μ : ℂ} {U : Set ℂ} (hU : IsOpen U) (hκ : κ ≠ 0)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z + κ ≠ 0) :
    IsPainleveVOn (1 / 2) (κ ^ 2 * μ) (2 * κ * μ) μ (fun z => κ / (z + κ)) U := by
  have hw1 : ∀ z ∈ U, κ / (z + κ) ≠ 1 := by
    intro z hz h
    rw [div_eq_one_iff_eq (h1 z hz)] at h
    exact h0 z hz (by linear_combination -h)
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => -κ / (z + κ) ^ 2)
    (fun z hz => ?_) (fun z hz => ?_), h0, fun z hz => div_ne_zero hκ (h1 z hz), hw1⟩
  · refine ((hasDerivAt_const z κ).div ((hasDerivAt_id z).add_const κ) (h1 z hz)).congr_deriv ?_
    have := h1 z hz
    simp only [id_eq]
    field_simp
    ring
  · refine ((hasDerivAt_const z (-κ)).div (((hasDerivAt_id z).add_const κ).pow 2)
      (pow_ne_zero 2 (h1 z hz))).congr_deriv ?_
    have := h1 z hz; have hz' := h0 z hz
    have h3 : κ - (z + κ) ≠ 0 := by
      rw [show κ - (z + κ) = -z by ring]; exact neg_ne_zero.mpr hz'
    simp only [painleveVRhs, id_eq, Pi.pow_apply]
    field_simp
    ring

/-- DLMF 32.8.26: `w = (κ + z)/(κ - z)` solves `PV` with parameters `(1/8, -1/8, -κμ, μ)` on
every open set avoiding `z = 0`, `z = κ` and `z = -κ`. -/
@[dlmf 32.8.E26]
theorem painleveV_rational_mobius' {κ μ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, κ - z ≠ 0) (h2 : ∀ z ∈ U, κ + z ≠ 0) :
    IsPainleveVOn (1 / 8) (-1 / 8) (-κ * μ) μ (fun z => (κ + z) / (κ - z)) U := by
  have hw1 : ∀ z ∈ U, (κ + z) / (κ - z) ≠ 1 := by
    intro z hz h
    rw [div_eq_one_iff_eq (h1 z hz)] at h
    exact h0 z hz (by linear_combination h / 2)
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => 2 * κ / (κ - z) ^ 2)
    (fun z hz => ?_) (fun z hz => ?_), h0, fun z hz => div_ne_zero (h2 z hz) (h1 z hz), hw1⟩
  · refine (((hasDerivAt_id z).const_add κ).div ((hasDerivAt_id z).const_sub κ)
      (h1 z hz)).congr_deriv ?_
    have := h1 z hz
    simp only [id_eq]
    field_simp
    ring
  · refine ((hasDerivAt_const z (2 * κ)).div (((hasDerivAt_id z).const_sub κ).pow 2)
      (pow_ne_zero 2 (h1 z hz))).congr_deriv ?_
    have := h1 z hz; have hz' := h0 z hz; have := h2 z hz
    have h3 : κ + z - (κ - z) ≠ 0 := by
      rw [show κ + z - (κ - z) = 2 * z by ring]; exact mul_ne_zero two_ne_zero hz'
    simp only [painleveVRhs, id_eq, Pi.pow_apply]
    field_simp
    ring

/-- DLMF §32.8(v), conditions (a)–(e): with `δ = -1/2` (the normalization of §32.2(ii) when
`δ ≠ 0`), `PV` has a rational solution iff, for some `m, n ∈ ℤ` and `ε = ±1`, one of
(a) `α = (m + εγ)²/2`, `β = -n²/2`, `n > 0`, `m + n` odd, and `α ≠ 0` when `|m| < n`;
(b) `α = n²/2`, `β = -(m + εγ)²/2`, `n > 0`, `m + n` odd, and `β ≠ 0` when `|m| < n`;
(c) `α = a²/2`, `β = -(a + n)²/2`, `γ = m`, `m + n` even (some `a ∈ ℂ`);
(d) `α = (b + n)²/2`, `β = -b²/2`, `γ = m`, `m + n` even (some `b ∈ ℂ`);
(e) `α = (2m + 1)²/8`, `β = -(2n + 1)²/8`, `γ ∉ ℤ`. -/
@[dlmf 32.8.v]
theorem painleveV_exists_rational_iff (α β γ : ℂ) :
    (∃ (w : ℂ → ℂ) (U : Set ℂ), IsOpen U ∧ U.Nonempty ∧ IsRationalOn w U ∧
        IsPainleveVOn α β γ (-1 / 2) w U) ↔
      ∃ (m n : ℤ) (ε : ℂ), (ε = 1 ∨ ε = -1) ∧
        ((α = (m + ε * γ) ^ 2 / 2 ∧ β = -(n : ℂ) ^ 2 / 2 ∧ 0 < n ∧ Odd (m + n) ∧
            (|m| < n → α ≠ 0)) ∨
          (α = (n : ℂ) ^ 2 / 2 ∧ β = -(m + ε * γ) ^ 2 / 2 ∧ 0 < n ∧ Odd (m + n) ∧
            (|m| < n → β ≠ 0)) ∨
          (∃ a : ℂ, α = a ^ 2 / 2 ∧ β = -(a + n) ^ 2 / 2 ∧ γ = m ∧ Even (m + n)) ∨
          (∃ b : ℂ, α = (b + n) ^ 2 / 2 ∧ β = -b ^ 2 / 2 ∧ γ = m ∧ Even (m + n)) ∨
          (α = (2 * m + 1) ^ 2 / 8 ∧ β = -(2 * n + 1) ^ 2 / 8 ∧ ∀ k : ℤ, γ ≠ k)) := by
  sorry

/-- DLMF 32.8.27: with `δ = -1/2`, every rational solution of `PV` has the form
`w = λz + μ + P_{n-1}/Q_n` with constants `λ, μ` and polynomials of degrees `n - 1` and `n`
(`P = 0` when `n = 0`) without common zeros. -/
@[dlmf 32.8.E27]
theorem painleveV_rational_form {α β γ : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hne : U.Nonempty) (hrat : IsRationalOn w U) (h : IsPainleveVOn α β γ (-1 / 2) w U) :
    ∃ (n : ℕ) (P Q : ℂ[X]) (l μ : ℂ), Q.natDegree = n ∧
      ((n = 0 ∧ P = 0) ∨ P.natDegree + 1 = n) ∧ IsCoprime P Q ∧
      ∀ z ∈ U, Q.eval z ≠ 0 ∧ w z = l * z + μ + P.eval z / Q.eval z := by
  sorry

/-! ## Special rational solutions of `PVI` (32.8.28–32.8.33) -/

/-- DLMF 32.8.28: `w = κz` solves `PVI` with parameters `(μ, -μκ², 1/2, 1/2 - μ(κ - 1)²)` on
every open set avoiding `z ∈ {0, 1}` and the points where `κz ∈ {0, 1, z}`. -/
@[dlmf 32.8.E28]
theorem painleveVI_rational_linear {κ μ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1) (hκ : κ ≠ 0) (hκ1 : κ ≠ 1)
    (hw1 : ∀ z ∈ U, κ * z ≠ 1) :
    IsPainleveVIOn μ (-μ * κ ^ 2) (1 / 2) (1 / 2 - μ * (κ - 1) ^ 2) (fun z => κ * z) U := by
  have hwz : ∀ z ∈ U, κ * z ≠ z := fun z hz h =>
    hκ1 (mul_right_cancel₀ (h0 z hz) (by rw [h, one_mul]))
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun _ => κ)
    (fun z _ => by simpa using (hasDerivAt_id z).const_mul κ) (fun z hz => ?_), h0, h1,
    fun z hz => mul_ne_zero hκ (h0 z hz), hw1, hwz⟩
  have hz' := h0 z hz; have hz1 := sub_ne_zero.mpr (h1 z hz)
  have ha := sub_ne_zero.mpr (hw1 z hz); have hb := sub_ne_zero.mpr (hwz z hz)
  have hk1 := sub_ne_zero.mpr hκ1
  convert hasDerivAt_const z κ using 1
  simp only [painleveVIRhs]
  field_simp
  ring

/-- DLMF 32.8.29: `w = κz²` solves `PVI` with parameters `(0, 0, 2, 0)` on every open set
avoiding `z ∈ {0, 1}` and the points where `κz² ∈ {0, 1, z}`. -/
@[dlmf 32.8.E29]
theorem painleveVI_rational_sq {κ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1) (hκ : κ ≠ 0)
    (hw1 : ∀ z ∈ U, κ * z ^ 2 ≠ 1) (hwz : ∀ z ∈ U, κ * z ^ 2 ≠ z) :
    IsPainleveVIOn 0 0 2 0 (fun z => κ * z ^ 2) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => 2 * κ * z)
    (fun z _ => ?_) (fun z hz => ?_), h0, h1,
    fun z hz => mul_ne_zero hκ (pow_ne_zero 2 (h0 z hz)), hw1, hwz⟩
  · exact ((hasDerivAt_pow 2 z).const_mul κ).congr_deriv (by push_cast; ring)
  · have hz' := h0 z hz; have hz1 := sub_ne_zero.mpr (h1 z hz)
    have ha := sub_ne_zero.mpr (hw1 z hz); have hb := sub_ne_zero.mpr (hwz z hz)
    have hc : κ * z - 1 ≠ 0 := fun h => hb (by linear_combination z * h)
    refine ((hasDerivAt_id z).const_mul (2 * κ)).congr_deriv ?_
    simp only [painleveVIRhs]
    field_simp
    ring

/-- DLMF 32.8.30: `w = κ/z` solves `PVI` with parameters `(0, 0, 1/2, -3/2)` on every open set
avoiding `z ∈ {0, 1}` and the points where `κ/z ∈ {0, 1, z}`. -/
@[dlmf 32.8.E30]
theorem painleveVI_rational_inv {κ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1) (hκ : κ ≠ 0)
    (hw1 : ∀ z ∈ U, κ / z ≠ 1) (hwz : ∀ z ∈ U, κ / z ≠ z) :
    IsPainleveVIOn 0 0 (1 / 2) (-3 / 2) (fun z => κ / z) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => -κ / z ^ 2)
    (fun z hz => ?_) (fun z hz => ?_), h0, h1,
    fun z hz => div_ne_zero hκ (h0 z hz), hw1, hwz⟩
  · refine ((hasDerivAt_const z κ).div (hasDerivAt_id z) (h0 z hz)).congr_deriv ?_
    simp only [id_eq]; ring
  · have hz' := h0 z hz; have hz1 := sub_ne_zero.mpr (h1 z hz)
    have ha : κ - z ≠ 0 := by
      intro h; apply hw1 z hz; rw [sub_eq_zero.mp h, div_self hz']
    have hb : κ - z ^ 2 ≠ 0 := by
      intro h; apply hwz z hz; rw [sub_eq_zero.mp h]; field_simp
    refine ((hasDerivAt_const z (-κ)).div ((hasDerivAt_id z).pow 2)
      (pow_ne_zero 2 hz')).congr_deriv ?_
    simp only [painleveVIRhs, id_eq, Pi.pow_apply]
    field_simp
    ring

/-- DLMF 32.8.31: `w = κ/z²` solves `PVI` with parameters `(0, 0, 2, -4)` on every open set
avoiding `z ∈ {0, 1}` and the points where `κ/z² ∈ {0, 1, z}`. -/
@[dlmf 32.8.E31]
theorem painleveVI_rational_inv_sq {κ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1) (hκ : κ ≠ 0)
    (hw1 : ∀ z ∈ U, κ / z ^ 2 ≠ 1) (hwz : ∀ z ∈ U, κ / z ^ 2 ≠ z) :
    IsPainleveVIOn 0 0 2 (-4) (fun z => κ / z ^ 2) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => -2 * κ / z ^ 3)
    (fun z hz => ?_) (fun z hz => ?_), h0, h1,
    fun z hz => div_ne_zero hκ (pow_ne_zero 2 (h0 z hz)), hw1, hwz⟩
  · have hz' := h0 z hz
    refine ((hasDerivAt_const z κ).div ((hasDerivAt_id z).pow 2)
      (pow_ne_zero 2 hz')).congr_deriv ?_
    simp only [id_eq, Pi.pow_apply]; field_simp; ring
  · have hz' := h0 z hz; have hz1 := sub_ne_zero.mpr (h1 z hz)
    have ha : κ - z ^ 2 ≠ 0 := by
      intro h; apply hw1 z hz; rw [sub_eq_zero.mp h, div_self (pow_ne_zero 2 hz')]
    have hb : κ - z ^ 3 ≠ 0 := by
      intro h; apply hwz z hz; rw [sub_eq_zero.mp h]; field_simp
    refine ((hasDerivAt_const z (-2 * κ)).div ((hasDerivAt_id z).pow 3)
      (pow_ne_zero 3 hz')).congr_deriv ?_
    simp only [painleveVIRhs, id_eq, Pi.pow_apply]
    field_simp
    ring

/-- DLMF 32.8.32: `w = z/(κ + μz)` solves `PVI` with parameters
`((κ + μ)²/2, -1/2, (μ - 1)²/2, κ(2 - κ)/2)` on every open set avoiding `z ∈ {0, 1}`,
`κ + μz = 0` and the points where `w ∈ {1, z}`. -/
@[dlmf 32.8.E32]
theorem painleveVI_rational_mobius {κ μ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (h1 : ∀ z ∈ U, z ≠ 1) (hd : ∀ z ∈ U, κ + μ * z ≠ 0)
    (hw1 : ∀ z ∈ U, z / (κ + μ * z) ≠ 1) (hwz : ∀ z ∈ U, z / (κ + μ * z) ≠ z) :
    IsPainleveVIOn ((κ + μ) ^ 2 / 2) (-1 / 2) ((μ - 1) ^ 2 / 2) (κ * (2 - κ) / 2)
      (fun z => z / (κ + μ * z)) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (v := fun z => κ / (κ + μ * z) ^ 2)
    (fun z hz => ?_) (fun z hz => ?_), h0, h1,
    fun z hz => div_ne_zero (h0 z hz) (hd z hz), hw1, hwz⟩
  · refine ((hasDerivAt_id z).div (((hasDerivAt_id z).const_mul μ).const_add κ)
      (hd z hz)).congr_deriv ?_
    have := hd z hz
    simp only [id_eq]; field_simp; ring
  · have hz' := h0 z hz; have hz1 := sub_ne_zero.mpr (h1 z hz); have hdz := hd z hz
    have ha : z - (κ + μ * z) ≠ 0 := by
      intro h; apply hw1 z hz; rw [div_eq_one_iff_eq hdz]; linear_combination h
    have hb : 1 - (κ + μ * z) ≠ 0 := by
      intro h; apply hwz z hz; rw [div_eq_iff hdz]; linear_combination z * h
    refine ((hasDerivAt_const z κ).div ((((hasDerivAt_id z).const_mul μ).const_add κ).pow 2)
      (pow_ne_zero 2 hdz)).congr_deriv ?_
    simp only [painleveVIRhs, id_eq, Pi.pow_apply]
    field_simp
    ring

/-- DLMF 32.8.33: `PVI` has rational solutions if `a + b + c + d = 2n + 1` for some `n ∈ ℤ`,
where `a² = 2α`, `b² = -2β`, `c² = 2γ`, `d² = 1 - 2δ` (independent choices of signs) and at
least one of `a, b, c, d` is an integer. -/
@[dlmf 32.8.E33]
theorem painleveVI_exists_rational {α β γ δ a b c d : ℂ} (ha : a ^ 2 = 2 * α)
    (hb : b ^ 2 = -2 * β) (hc : c ^ 2 = 2 * γ) (hd : d ^ 2 = 1 - 2 * δ) {n : ℤ}
    (hn : a + b + c + d = 2 * n + 1)
    (hint : ∃ k : ℤ, a = k ∨ b = k ∨ c = k ∨ d = k) :
    ∃ (w : ℂ → ℂ) (U : Set ℂ), IsOpen U ∧ U.Nonempty ∧ IsRationalOn w U ∧
      IsPainleveVIOn α β γ δ w U := by
  sorry

end DLMF.Painleve
