/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.SolutionsDefs
public import DLMF.Painleve.Equations
public import DLMF.Painleve.Rational

/-!
# Rational solutions of the Painlevé equations (DLMF §32.8)

DLMF normalization (`DLMF.Painleve.Defs`). The rational solutions of `PII` are bridged to the
Beals–Wong construction of `DLMF.Painleve.Rational` (`rationalPIIPair`), whose `PII(c)` is DLMF's
`PII` with `α = -c`. The explicit solutions 32.8.1–32.8.4 and the Yablonskii–Vorob'ev
polynomials 32.8.7 are proved by polynomial identities. The general statements 32.8.5–32.8.6
(exactness of the recurrence, monicity, the rational solutions for every `n`) are proved from a
bilinear invariant: `Q_n` and `Q_{n+1}` are monic with simple zeros and satisfy the Hirota
equations `D_z²(Q_{n+1}·Q_n) = 0` and `(D_z³ - zD_z)(Q_n·Q_{n+1}) = (n+1)Q_nQ_{n+1}`
(`p3b_YV`); divisibility follows by checking the numerator at the simple zeros of `Q_n`. The
generating function 32.8.8 is a Cauchy product; the Wronskian form 32.8.9 is admitted. The
special rational solutions of `PIII`–`PVI` (32.8.11–32.8.13, 32.8.16–32.8.18, 32.8.24–32.8.26,
32.8.28–32.8.32) are proved on every open set avoiding the singular points; the
classification statements ("rational solutions exist iff …") are admitted.
-/

@[expose] public noncomputable section

open Polynomial Set Filter
open scoped Topology

namespace DLMF.Painleve

/-! ## Bridge to Beals–Wong -/

/-- The symmetry `w ↦ -w`, `α ↦ -α` of DLMF's `PII`. -/
theorem b32_isPainleveIIOn_neg {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIOn α w U) : IsPainleveIIOn (-α) (fun z => -w z) U := by
  rw [isPainleveIIOn_iff_isPIIOn] at h ⊢
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
  exact ⟨p, q, hq, isPainleveIIOn_iff_isPIIOn.mpr (by simpa using h)⟩

/-- DLMF 32.8.1: `w(z; 1) = -1/z` solves `PII` with `α = 1` for `z ≠ 0`. -/
@[dlmf 32.8.E1]
theorem painleveII_rational_one :
    IsPainleveIIOn 1 (fun z => -1 / z) {z | z ≠ 0} := by
  have h := isPIIOn_recip (𝕜 := ℂ)
  have h' : IsPainleveIIOn (-1) (fun z : ℂ => z⁻¹) {z | z ≠ 0} :=
    isPainleveIIOn_iff_isPIIOn.mpr (by simpa using h)
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

/-- Identity under the stated parameter and domain assumptions: `(C 4 : ℂ[X]) = 4`. -/
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

/-- Nonvanishing under the stated hypotheses: `(X ^ 3 + 4 : ℂ[X]) ≠ 0`. -/
private lemma b32_Q2_ne : (X ^ 3 + 4 : ℂ[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  simp at this

/-- Nonvanishing under the stated hypotheses: `(X ^ 6 + 20 * X ^ 3 - 80 : ℂ[X]) ≠ 0`. -/
private lemma b32_Q3_ne : (X ^ 6 + 20 * X ^ 3 - 80 : ℂ[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  norm_num at this

/-- Nonvanishing under the stated hypotheses: `(X ^ 10 + 60 * X ^ 7 + 11200 * X : ℂ[X]) ≠ 0`. -/
private lemma b32_Q4_ne : (X ^ 10 + 60 * X ^ 7 + 11200 * X : ℂ[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 1) h
  norm_num at this

/-- Nonvanishing under the stated hypotheses: `(X ^ 15 + 140 * X ^ 12 + 2800 * X ^ 9 + 78400 * X ^
6 - 3136000 * X ^ 3 - 6272000 : ℂ[X]) ≠ 0`. -/
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
theorem b32_congr {α : ℂ} {w w' : ℂ → ℂ} {U : Set ℂ} (h : IsPainleveIIOn α w U)
    (hU : IsOpen U) (he : EqOn w w' U) : IsPainleveIIOn α w' U :=
  isPainleveIIOn_iff_isPIIOn.mpr ((isPainleveIIOn_iff_isPIIOn.mp h).congr hU he)

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

/-- The indicated domain is open: `IsOpen {z : ℂ | P.eval z ≠ 0}`. -/
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

/-! ## Bilinear invariant of the Yablonskii–Vorob'ev polynomials -/

/-- A nonzero polynomial with only simple zeros divides every nonzero polynomial vanishing at
its zeros. -/
lemma p3b_dvd_of_simple {v N : ℂ[X]} (hv : v ≠ 0)
    (hs : ∀ c, v.eval c = 0 → (derivative v).eval c ≠ 0) (hN0 : N ≠ 0)
    (h : ∀ c, v.eval c = 0 → N.eval c = 0) : v ∣ N := by
  classical
  refine (IsAlgClosed.splits v).dvd_of_roots_le_roots hv ?_
  have hnd : v.roots.Nodup := Multiset.nodup_iff_count_le_one.mpr fun c => by
    rw [count_roots]
    by_contra hc
    push Not at hc
    obtain ⟨h0, h1⟩ := (one_lt_rootMultiplicity_iff_isRoot hv).mp hc
    exact hs c h0 h1
  rw [Multiset.le_iff_subset hnd]
  intro c hc
  rw [mem_roots hv] at hc
  exact (mem_roots hN0).mpr (h c hc)

/-- A nonzero solution `f` of the bilinear equation `D²(f·g) = 0` has only simple zeros
away from the zeros of `g`. -/
lemma p3b_simple_of_D2 {f g : ℂ[X]} (hf : f ≠ 0) {c : ℂ} (hg : g.eval c ≠ 0)
    (hD : derivative (derivative f) * g - 2 * derivative f * derivative g +
      f * derivative (derivative g) = 0) (h0 : f.eval c = 0) :
    (derivative f).eval c ≠ 0 := by
  intro h1
  set k := f.rootMultiplicity c with hk
  have hk2 : 1 < k := (one_lt_rootMultiplicity_iff_isRoot hf).mpr ⟨h0, h1⟩
  have hm1 : (derivative f).rootMultiplicity c = k - 1 := derivative_rootMultiplicity_of_root h0
  have hm2 : (derivative (derivative f)).rootMultiplicity c = k - 2 := by
    rw [derivative_rootMultiplicity_of_root h1, hm1]; omega
  have hf2 : derivative (derivative f) ≠ 0 := by
    intro h2
    have e1 := derivative_eq_zero.mp h2
    rw [eq_C_of_natDegree_eq_zero e1] at h1
    have hf1 : derivative f = 0 := by
      rw [eq_C_of_natDegree_eq_zero e1]; simpa using h1
    have e0 := derivative_eq_zero.mp hf1
    rw [eq_C_of_natDegree_eq_zero e0] at h0
    exact hf (by rw [eq_C_of_natDegree_eq_zero e0]; simpa using h0)
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have hdvd : (X - C c) ^ (k - 1) ∣ derivative (derivative f) * g := by
    have e : derivative (derivative f) * g =
        2 * derivative f * derivative g - f * derivative (derivative g) := by
      linear_combination hD
    rw [e]
    refine dvd_sub (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ?_ _) _)
      (dvd_mul_of_dvd_left ?_ _)
    · rw [← hm1]; exact pow_rootMultiplicity_dvd _ _
    · exact (pow_dvd_pow _ (Nat.sub_le k 1)).trans (pow_rootMultiplicity_dvd _ _)
  have hne := mul_ne_zero hf2 hg0
  have := (le_rootMultiplicity_iff hne).mpr hdvd
  rw [rootMultiplicity_mul hne, hm2, rootMultiplicity_eq_zero (by simpa using hg)] at this
  omega
/-- The bilinear equations propagate through one step of the Yablonskii–Vorob'ev recurrence:
with jets of `u`, `v`, `s` and `s v = z u² - 4 u u'' + 4 u'²`. -/
lemma p3b_step {u u1 u2 u3 u4 u5 v v1 v2 v3 v4 s s1 s2 s3 : ℂ[X]} {α : ℂ}
    (hu1 : derivative u = u1) (hu2 : derivative u1 = u2) (hu3 : derivative u2 = u3)
    (hu4 : derivative u3 = u4) (hu5 : derivative u4 = u5)
    (hv1 : derivative v = v1) (hv2 : derivative v1 = v2) (hv3 : derivative v2 = v3)
    (hv4 : derivative v3 = v4)
    (hs1 : derivative s = s1) (hs2 : derivative s1 = s2) (hs3 : derivative s2 = s3)
    (hv : v ≠ 0)
    (hR : s * v = X * u ^ 2 - 4 * u * u2 + 4 * u1 ^ 2)
    (hD : u2 * v - 2 * u1 * v1 + u * v2 = 0)
    (hE : v3 * u - 3 * v2 * u1 + 3 * v1 * u2 - v * u3 - X * (v1 * u - v * u1) = C α * v * u) :
    s2 * u - 2 * s1 * u1 + s * u2 = 0 ∧
      u3 * s - 3 * u2 * s1 + 3 * u1 * s2 - u * s3 - X * (u1 * s - u * s1) =
        C (α + 1) * u * s := by
  set a := C α with ha
  have hda : derivative a = 0 := derivative_C
  have hR0 : s * v - (X * u * u - 4 * u * u2 + 4 * u1 * u1) = 0 := by
    rw [hR]; ring
  have hD0 := hD
  have hE0 : v3 * u - 3 * v2 * u1 + 3 * v1 * u2 - v * u3 - X * (v1 * u - v * u1) - a * v * u = 0 :=
    sub_eq_zero.mpr hE
  have hR1 := congrArg derivative hR0
  have hR2 := congrArg derivative hR1
  have hR3 := congrArg derivative hR2
  have hD1 := congrArg derivative hD0
  have hD2 := congrArg derivative hD1
  have hD3 := congrArg derivative hD2
  have hE1 := congrArg derivative hE0
  have hE2 := congrArg derivative hE1
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X,
    derivative_ofNat, derivative_zero, derivative_one, hda, hu1, hu2, hu3, hu4, hu5, hv1, hv2, hv3,
    hv4, hs1, hs2, hs3] at hR1 hR2 hR3 hD1 hD2 hD3 hE1 hE2
  constructor
  · have h : v ^ 3 * (s2 * u - 2 * s1 * u1 + s * u2) = 0 := by
      linear_combination (u*v^2) * hR2 + (- 2*u1*v^2 - 2*u*v*v1) * hR1 + (u2*v^2 + 2*u*v1^2 - u*v*v2
          + 2*u1*v*v1) * hR0 + (- 2*v*u^2) * hD2 + (2*v1*u^2 + 6*u*u1*v) * hD1 + (- 4*v*u1^2 +
          v*X*u^2 - 4*u*u1*v1) * hD0 + (2*v*u^2) * hE1 + (- 2*v1*u^2 - 2*u*u1*v) * hE0
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 hv)
  · have h : v ^ 4 * (u3 * s - 3 * u2 * s1 + 3 * u1 * s2 - u * s3 - X * (u1 * s - u * s1) -
        (a + 1) * u * s) = 0 := by
      linear_combination (- u*v^3) * hR3 + (3*u1*v^3 + 3*u*v1*v^2) * hR2 + (- 3*u2*v^3 + u*X*v^3 -
          6*u*v*v1^2 - 6*u1*v1*v^2 + 3*u*v2*v^2) * hR1 + (u3*v^3 - u*v^3 + 6*u*v1^3 + u*v3*v^2 -
          a*u*v^3 - u1*X*v^3 - 3*u1*v2*v^2 + 3*u2*v1*v^2 + 6*u1*v*v1^2 - u*v1*X*v^2 - 6*u*v*v1*v2) *
          hR0 + (2*u^2*v^2) * hD3 + (- 6*u*u1*v^2 - 6*v*v1*u^2) * hD2 + (6*u^2*v1^2 + 6*u1^2*v^2 -
          2*X*u^2*v^2 + 12*u*u1*v*v1) * hD1 + (- u^2*v^2 - 12*u*u1*v1^2 - 12*v*v1*u1^2 - 4*v*v3*u^2
          + 2*a*u^2*v^2 + 4*v*v1*X*u^2 + 12*u*u1*v*v2) * hD0 + (- 2*u^2*v^2) * hE2 + (2*u*u1*v^2 +
          6*v*v1*u^2) * hE1 + (- 6*u^2*v1^2 + 2*u1^2*v^2 + X*u^2*v^2 + 4*v*v2*u^2 - 8*u*u1*v*v1) *
          hE0
    rw [C_add, C_1, ← ha]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 4 hv))

/-- One step of the Yablonskii–Vorob'ev recurrence on the bilinear invariant. -/
lemma p3b_step_full {u v : ℂ[X]} {α : ℂ} (hv : v.Monic) (hu : u.Monic)
    (hsv : ∀ c, v.eval c = 0 → (derivative v).eval c ≠ 0)
    (hsu : ∀ c, u.eval c = 0 → (derivative u).eval c ≠ 0)
    (hD : derivative (derivative u) * v - 2 * derivative u * derivative v +
      u * derivative (derivative v) = 0)
    (hE : derivative (derivative (derivative v)) * u -
        3 * derivative (derivative v) * derivative u +
        3 * derivative v * derivative (derivative u) - v * derivative (derivative (derivative u)) -
        X * (derivative v * u - v * derivative u) = C α * v * u) :
    let N := X * u ^ 2 + C 4 * (derivative u) ^ 2 - C 4 * u * derivative (derivative u)
    N / v * v = N ∧ (N / v).Monic ∧
      (∀ c, (N / v).eval c = 0 → (derivative (N / v)).eval c ≠ 0) ∧
      derivative (derivative (N / v)) * u - 2 * derivative (N / v) * derivative u +
        (N / v) * derivative (derivative u) = 0 ∧
      derivative (derivative (derivative u)) * (N / v) -
        3 * derivative (derivative u) * derivative (N / v) +
        3 * derivative u * derivative (derivative (N / v)) -
        u * derivative (derivative (derivative (N / v))) -
        X * (derivative u * (N / v) - u * derivative (N / v)) = C (α + 1) * u * (N / v) := by
  intro N
  have h4 : (C 4 : ℂ[X]) = 4 := rfl
  -- `N` is monic
  have hNm : N.Monic := by
    have e : N = X * u ^ 2 + (C 4 * (derivative u) ^ 2 - C 4 * u * derivative (derivative u)) := by
      simp only [N]; ring
    rw [e]
    have hp : (X * u ^ 2).Monic := monic_X.mul (hu.pow 2)
    refine hp.add_of_left (degree_lt_degree ?_)
    have hpd : (X * u ^ 2).natDegree = 2 * u.natDegree + 1 := by
      rw [natDegree_mul X_ne_zero (pow_ne_zero 2 hu.ne_zero), natDegree_X, natDegree_pow]; ring
    have h1 := natDegree_derivative_le u
    have h2 := natDegree_derivative_le (derivative u)
    have hq : (C 4 * (derivative u) ^ 2 - C 4 * u * derivative (derivative u)).natDegree ≤
        2 * u.natDegree := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans ?_)
        omega
      · rw [mul_assoc]
        refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
        omega
    omega
  -- exactness: `v ∣ N`
  have hdvd : v ∣ N := by
    refine p3b_dvd_of_simple hv.ne_zero hsv hNm.ne_zero fun c hc => ?_
    have hD1 := congrArg derivative hD
    simp only [derivative_mul, derivative_add, derivative_sub, derivative_ofNat, derivative_zero,
      zero_mul, zero_add] at hD1
    have e0 := congrArg (eval c) hD
    have e1 := congrArg (eval c) hD1
    have e2 := congrArg (eval c) hE
    simp only [eval_mul, eval_add, eval_sub, eval_ofNat, eval_X, eval_C, eval_zero, hc] at e0 e1 e2
    have hA := hsv c hc
    simp only [N, eval_mul, eval_add, eval_sub, eval_pow, eval_X, eval_C]
    have : (derivative v).eval c * (c * u.eval c ^ 2 + 4 * (derivative u).eval c ^ 2 -
        4 * u.eval c * (derivative (derivative u)).eval c) = 0 := by
      linear_combination (-2 * (derivative u).eval c) * e0 + (u.eval c) * e1 - (u.eval c) * e2
    exact (mul_eq_zero.mp this).resolve_left hA
  obtain ⟨s, hs⟩ := hdvd
  have hsN : N / v = s := by rw [hs]; exact mul_div_cancel_left₀ s hv.ne_zero
  rw [hsN]
  have hsm : s.Monic := hv.of_mul_monic_left (hs ▸ hNm)
  have hR : s * v = X * u ^ 2 - 4 * u * derivative (derivative u) + 4 * (derivative u) ^ 2 := by
    have : N = v * s := hs
    simp only [N, h4] at this
    linear_combination -this
  obtain ⟨hD', hE'⟩ := p3b_step (u := u) (v := v) (s := s) rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl hv.ne_zero hR hD hE
  refine ⟨by rw [mul_comm]; exact hs.symm, hsm, fun c hc => ?_, hD', hE'⟩
  by_cases huc : u.eval c = 0
  · have e := congrArg (eval c) hR
    simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_X, eval_ofNat, hc, huc] at e
    have : (derivative u).eval c ^ 2 = 0 := by linear_combination -e / 4
    exact absurd (pow_eq_zero_iff two_ne_zero |>.mp this) (hsu c huc)
  · exact p3b_simple_of_D2 hsm.ne_zero huc hD' hc

/-- The bilinear invariant of the Yablonskii–Vorob'ev polynomials. -/
lemma p3b_YV (n : ℕ) :
    (yablonskiiVorobievQ n).Monic ∧ (yablonskiiVorobievQ (n + 1)).Monic ∧
      (∀ c, (yablonskiiVorobievQ n).eval c = 0 →
        (derivative (yablonskiiVorobievQ n)).eval c ≠ 0) ∧
      (∀ c, (yablonskiiVorobievQ (n + 1)).eval c = 0 →
        (derivative (yablonskiiVorobievQ (n + 1))).eval c ≠ 0) ∧
      derivative (derivative (yablonskiiVorobievQ (n + 1))) * yablonskiiVorobievQ n -
          2 * derivative (yablonskiiVorobievQ (n + 1)) * derivative (yablonskiiVorobievQ n) +
          yablonskiiVorobievQ (n + 1) * derivative (derivative (yablonskiiVorobievQ n)) = 0 ∧
      derivative (derivative (derivative (yablonskiiVorobievQ n))) *
            yablonskiiVorobievQ (n + 1) -
          3 * derivative (derivative (yablonskiiVorobievQ n)) *
            derivative (yablonskiiVorobievQ (n + 1)) +
          3 * derivative (yablonskiiVorobievQ n) *
            derivative (derivative (yablonskiiVorobievQ (n + 1))) -
          yablonskiiVorobievQ n *
            derivative (derivative (derivative (yablonskiiVorobievQ (n + 1)))) -
          X * (derivative (yablonskiiVorobievQ n) * yablonskiiVorobievQ (n + 1) -
            yablonskiiVorobievQ n * derivative (yablonskiiVorobievQ (n + 1))) =
        C ((n : ℂ) + 1) * yablonskiiVorobievQ n * yablonskiiVorobievQ (n + 1) := by
  induction n with
  | zero =>
    simp only [yablonskiiVorobievQ]
    refine ⟨monic_one, monic_X, fun c hc => by simp at hc, fun c _ => by simp, by simp, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨hv, hu, hsv, hsu, hD, hE⟩ := ih
    obtain ⟨-, hm, hs, hD', hE'⟩ := p3b_step_full hv hu hsv hsu hD hE
    have hQ : yablonskiiVorobievQ (n + 1 + 1) = (X * yablonskiiVorobievQ (n + 1) ^ 2 +
        C 4 * (derivative (yablonskiiVorobievQ (n + 1))) ^ 2 -
        C 4 * yablonskiiVorobievQ (n + 1) *
          derivative (derivative (yablonskiiVorobievQ (n + 1)))) / yablonskiiVorobievQ n := by
      rw [yablonskiiVorobievQ]
    rw [hQ]
    refine ⟨hu, hm, hsu, hs, hD', ?_⟩
    convert hE' using 3
    push_cast; ring

/-! ## General statements on the Yablonskii–Vorob'ev polynomials (32.8.5–32.8.10) -/

/-- DLMF 32.8.6: the division in the recurrence is exact, `Q_{n+1}Q_{n-1} = zQ_n² + 4(Q_n')² -
4Q_nQ_n''` for `n ≥ 1` (here with `n + 1` in place of `n`), and every `Q_n` is monic.
Proved from the bilinear invariant `p3b_YV`. -/
@[dlmf 32.8.E6]
theorem yablonskiiVorobievQ_recurrence (n : ℕ) :
    yablonskiiVorobievQ (n + 2) * yablonskiiVorobievQ n =
        X * yablonskiiVorobievQ (n + 1) ^ 2 +
          C 4 * (derivative (yablonskiiVorobievQ (n + 1))) ^ 2 -
          C 4 * yablonskiiVorobievQ (n + 1) *
            derivative (derivative (yablonskiiVorobievQ (n + 1))) ∧
      (yablonskiiVorobievQ (n + 2)).Monic := by
  obtain ⟨hv, hu, hsv, hsu, hD, hE⟩ := p3b_YV n
  obtain ⟨h1, hm, -⟩ := p3b_step_full hv hu hsv hsu hD hE
  have hQ : yablonskiiVorobievQ (n + 2) = (X * yablonskiiVorobievQ (n + 1) ^ 2 +
      C 4 * (derivative (yablonskiiVorobievQ (n + 1))) ^ 2 -
      C 4 * yablonskiiVorobievQ (n + 1) *
        derivative (derivative (yablonskiiVorobievQ (n + 1)))) / yablonskiiVorobievQ n := by
    rw [yablonskiiVorobievQ]
  rw [hQ]
  exact ⟨h1, hm⟩

/-- DLMF 32.8.5: for `n ≥ 1`, `w(z; n) = d/dz ln(Q_{n-1}(z)/Q_n(z))` solves `PII` with `α = n`
on the set where `Q_{n-1}Q_n ≠ 0` (the logarithmic derivative is taken as
`Q_{n-1}'/Q_{n-1} - Q_n'/Q_n`, so no branch of `ln` enters). Proved for `n ≤ 4` in the explicit
forms `painleveII_rational_one` … `painleveII_rational_four`. -/
@[dlmf 32.8.E5]
theorem rationalPainleveII_isPainleveIIOn (n : ℕ) (hn : 1 ≤ n) :
    IsPainleveIIOn (n : ℂ) (rationalPainleveII n)
      {z | (yablonskiiVorobievQ (n - 1)).eval z ≠ 0 ∧ (yablonskiiVorobievQ n).eval z ≠ 0} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨-, -, -, -, hD, hE⟩ := p3b_YV m
  set v := yablonskiiVorobievQ m
  set u := yablonskiiVorobievQ (m + 1)
  have h := b32_isPainleveIIOn_logDeriv (α := (m : ℂ) + 1) (A := v) (B := u) rfl rfl rfl rfl rfl
    rfl (by
      linear_combination (-3 * v * derivative v * u ^ 2 + 3 * u * derivative u * v ^ 2) * hD +
        (u ^ 2 * v ^ 2) * hE)
  have hm : m + 1 - 1 = m := by omega
  rw [hm]
  push_cast
  convert h using 2 with z
  have h1 : (0 : ℤ) < ((m + 1 : ℕ) : ℤ) := by omega
  have h2 : ((m + 1 : ℕ) : ℤ).toNat = m + 1 := by omega
  rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring]
  simp only [rationalPainleveII, h1, h2, ite_true, hm, v, u]

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

open Nat in
/-- DLMF 32.8.8: the generating function `∑_{m ≥ 0} p_m(z) λ^m = exp(zλ - (4/3)λ³)`, for all
complex `z` and `λ`. -/
@[dlmf 32.8.E8]
theorem hasSum_yablonskiiVorobievP (z l : ℂ) :
    HasSum (fun m : ℕ => (yablonskiiVorobievP m).eval z * l ^ m)
      (Complex.exp (z * l - 4 / 3 * l ^ 3)) := by
  set a : ℕ → ℂ := fun k => if 3 ∣ k then (-4 / 3 * l ^ 3) ^ (k / 3) / ((k / 3)! : ℂ) else 0
    with ha_def
  set b : ℕ → ℂ := fun k => (z * l) ^ k / (k ! : ℂ) with hb_def
  have hinj : Function.Injective (fun j : ℕ => 3 * j) := fun i j h => by simpa using h
  have hcomp : a ∘ (fun j => 3 * j) = fun j => (-4 / 3 * l ^ 3) ^ j / (j ! : ℂ) := by
    funext j; simp [a]
  have hzero : ∀ k ∉ Set.range (fun j : ℕ => 3 * j), a k = 0 := by
    intro k hk
    simp only [a, ite_eq_right_iff]
    intro h; exact absurd ⟨k / 3, Nat.mul_div_cancel' h⟩ hk
  have ha : HasSum a (Complex.exp (-4 / 3 * l ^ 3)) := by
    rw [← hinj.hasSum_iff hzero, hcomp, Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hna : Summable fun k => ‖a k‖ := by
    rw [← hinj.summable_iff (f := fun k => ‖a k‖) (fun k hk => by simp [hzero k hk])]
    have := NormedSpace.norm_expSeries_div_summable (𝔸 := ℂ) (-4 / 3 * l ^ 3)
    convert this using 2 with j
    simp [a]
  have hb : HasSum b (Complex.exp (z * l)) := by
    rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hnb : Summable fun k => ‖b k‖ := NormedSpace.norm_expSeries_div_summable (𝔸 := ℂ) _
  have H := hasSum_sum_range_mul_of_summable_norm hna hnb
  rw [ha.tsum_eq, hb.tsum_eq, ← Complex.exp_add] at H
  convert H using 1
  · funext m
    have hfil : (Finset.range (m + 1)).filter (fun k => 3 ∣ k) =
        (Finset.range (m / 3 + 1)).image (3 * ·) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hk, j, rfl⟩; exact ⟨j, by omega, rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact ⟨by omega, dvd_mul_right 3 j⟩
    have e1 : ∑ k ∈ Finset.range (m + 1), a k * b (m - k) =
        ∑ k ∈ Finset.range (m + 1), if 3 ∣ k then
          (-4 / 3 * l ^ 3) ^ (k / 3) / ((k / 3)! : ℂ) * b (m - k) else 0 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [a]; split_ifs <;> simp
    rw [e1, ← Finset.sum_filter, hfil, Finset.sum_image (fun i _ j _ h => hinj h)]
    simp only [yablonskiiVorobievP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : 3 * j ≤ m := by simp at hj; omega
    rw [Nat.mul_div_cancel_left j (by norm_num : 0 < 3)]
    have hl : l ^ m = (l ^ 3) ^ j * l ^ (m - 3 * j) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    simp only [b, hl, mul_pow]
    field_simp
  · congr 1; ring

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
