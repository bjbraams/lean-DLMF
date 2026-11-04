/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.SixJ

/-!
# The recursion relation of the `6j` symbol

The three-term recursion relation DLMF 34.5.11 of the `6j` symbol in its first argument, with
the coefficients 34.5.12 and 34.5.13.

## Main results

* `wigner6j_recursion`: DLMF 34.5.11–34.5.13.

## Implementation notes

The recursion is proved on Racah's single sum 34.4.2 (`racahTerm6j`). The combination
`K S(j₁) + c₊ S(j₁+1) + c₋ S(j₁-1)` of the three Racah sums telescopes: its summand is
`H(s+1) - H(s)`, where `H(s)` is a shifted Racah term times a polynomial in `s` of degree two
(`sixJRecursionCertificate`), found by Gosper's algorithm. The square-root factors
`E(j₁+1)` and `E(j₁)` combine with the triangle coefficients of the shifted symbols into
those of `{j₁ j₂ j₃; l₁ l₂ l₃}` times polynomials. When a shifted symbol violates a triangle
condition, its Racah sum vanishes term by term.
-/

@[expose] public noncomputable section

open Finset

namespace DLMF.WignerSymbols

/-! ## §34.5(iii) Recursion relations -/

/-- Three-term relation of the Racah sum of 34.4.2 in the shift `j₁ ↦ j₁ ± 1`, from a
polynomial telescoping certificate. -/
private theorem sum_racahTerm6j_three_term {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} {n₁ n₂ n₃ n₄ m₁ m₂ m₃ : ℤ}
    (h₁ : j₁ + j₂ + j₃ = n₁) (h₂ : j₁ + l₂ + l₃ = n₂) (h₃ : l₁ + j₂ + l₃ = n₃)
    (h₄ : l₁ + l₂ + j₃ = n₄) (g₁ : j₁ + j₂ + l₁ + l₂ = m₁) (g₂ : j₂ + j₃ + l₂ + l₃ = m₂)
    (g₃ : j₃ + j₁ + l₃ + l₁ = m₃) (h₃0 : 0 ≤ l₁ + j₂ + l₃) (N : ℕ) (hN : j₂ + j₃ + l₂ + l₃ < N)
    (K cp cm : ℝ) (q : ℝ → ℝ)
    (hpoly : ∀ x : ℝ,
      K * ((x - (j₁ + j₂ + j₃) + 1) * (x - (j₁ + l₂ + l₃) + 1) * (j₁ + j₂ + l₁ + l₂ - x + 1) *
          (j₃ + j₁ + l₃ + l₁ - x + 1)) +
        cp * ((x - (j₁ + j₂ + j₃)) * (x - (j₁ + j₂ + j₃) + 1) * ((x - (j₁ + l₂ + l₃)) *
          (x - (j₁ + l₂ + l₃) + 1))) +
        cm * ((j₁ + j₂ + l₁ + l₂ - x) * (j₁ + j₂ + l₁ + l₂ - x + 1) *
          ((j₃ + j₁ + l₃ + l₁ - x) * (j₃ + j₁ + l₃ + l₁ - x + 1))) =
      -((x + 2) * (j₁ + j₂ + l₁ + l₂ - x + 1) * (j₂ + j₃ + l₂ + l₃ - x) *
          (j₃ + j₁ + l₃ + l₁ - x + 1)) * q (x + 1) -
        (x - (j₁ + j₂ + j₃) + 1) * (x - (j₁ + l₂ + l₃) + 1) * (x - (l₁ + j₂ + l₃)) *
          (x - (l₁ + l₂ + j₃)) * q x) :
    K * ∑ s ∈ range N, racahTerm6j j₁ j₂ j₃ l₁ l₂ l₃ s +
      cp * ∑ s ∈ range N, racahTerm6j (j₁ + 1) j₂ j₃ l₁ l₂ l₃ s +
      cm * ∑ s ∈ range N, racahTerm6j (j₁ - 1) j₂ j₃ l₁ l₂ l₃ s = 0 := by
  set H : ℕ → ℝ := fun s => (-1 : ℝ) ^ s * ((s + 1).factorial : ℝ) *
    ratInvFactorial (s - j₁ - j₂ - j₃) * ratInvFactorial (s - j₁ - l₂ - l₃) *
    ratInvFactorial (s - l₁ - j₂ - l₃ - 1) * ratInvFactorial (s - l₁ - l₂ - j₃ - 1) *
    ratInvFactorial (j₁ + j₂ + l₁ + l₂ + 1 - s) * ratInvFactorial (j₂ + j₃ + l₂ + l₃ - s) *
    ratInvFactorial (j₃ + j₁ + l₃ + l₁ + 1 - s) * q s with hHdef
  have hH0 : H 0 = 0 := by
    simp only [hHdef]
    rw [ratInvFactorial_of_neg (x := ((0 : ℕ) : ℚ) - l₁ - j₂ - l₃ - 1) (by push_cast; linarith)]
    ring
  have hHN : H N = 0 := by
    simp only [hHdef]
    rw [ratInvFactorial_of_neg (x := j₂ + j₃ + l₂ + l₃ - N) (by linarith)]
    ring
  have hT := sum_range_sub H N
  rw [hHN, hH0, sub_zero] at hT
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← hT]
  refine sum_congr rfl fun s _ => ?_
  have R : ∀ (t : ℚ) (n : ℤ), t = n → ratInvFactorial (t - 1) = (t : ℝ) * ratInvFactorial t :=
    fun t n h => ratInvFactorial_sub_one_of_eq_intCast h
  -- the base factors
  have u1 : ratInvFactorial ((s : ℚ) - j₁ - j₂ - j₃) =
      (((s : ℚ) - j₁ - j₂ - j₃ + 1 : ℚ) : ℝ) * ratInvFactorial ((s : ℚ) - j₁ - j₂ - j₃ + 1) := by
    rw [← R _ (s - n₁ + 1) (by push_cast; linarith)]; congr 1; ring
  have u2 : ratInvFactorial ((s : ℚ) - j₁ - l₂ - l₃) =
      (((s : ℚ) - j₁ - l₂ - l₃ + 1 : ℚ) : ℝ) * ratInvFactorial ((s : ℚ) - j₁ - l₂ - l₃ + 1) := by
    rw [← R _ (s - n₂ + 1) (by push_cast; linarith)]; congr 1; ring
  have v1 : ratInvFactorial (j₁ + j₂ + l₁ + l₂ - s) =
      ((j₁ + j₂ + l₁ + l₂ + 1 - s : ℚ) : ℝ) * ratInvFactorial (j₁ + j₂ + l₁ + l₂ + 1 - s) := by
    rw [← R _ (m₁ + 1 - s) (by push_cast; linarith)]; congr 1; ring
  have v3 : ratInvFactorial (j₃ + j₁ + l₃ + l₁ - s) =
      ((j₃ + j₁ + l₃ + l₁ + 1 - s : ℚ) : ℝ) * ratInvFactorial (j₃ + j₁ + l₃ + l₁ + 1 - s) := by
    rw [← R _ (m₃ + 1 - s) (by push_cast; linarith)]; congr 1; ring
  -- shifted symbol `j₁ + 1`
  have p1 : ratInvFactorial ((s : ℚ) - (j₁ + 1) - j₂ - j₃) =
      (((s : ℚ) - j₁ - j₂ - j₃ : ℚ) : ℝ) * ratInvFactorial ((s : ℚ) - j₁ - j₂ - j₃) := by
    rw [← R _ (s - n₁) (by push_cast; linarith)]; congr 1; ring
  have p2 : ratInvFactorial ((s : ℚ) - (j₁ + 1) - l₂ - l₃) =
      (((s : ℚ) - j₁ - l₂ - l₃ : ℚ) : ℝ) * ratInvFactorial ((s : ℚ) - j₁ - l₂ - l₃) := by
    rw [← R _ (s - n₂) (by push_cast; linarith)]; congr 1; ring
  have p3 : ratInvFactorial (j₁ + 1 + j₂ + l₁ + l₂ - s) =
      ratInvFactorial (j₁ + j₂ + l₁ + l₂ + 1 - s) := by
    congr 1; ring
  have p4 : ratInvFactorial (j₃ + (j₁ + 1) + l₃ + l₁ - s) =
      ratInvFactorial (j₃ + j₁ + l₃ + l₁ + 1 - s) := by
    congr 1; ring
  -- shifted symbol `j₁ - 1`
  have m1 : ratInvFactorial ((s : ℚ) - (j₁ - 1) - j₂ - j₃) =
      ratInvFactorial ((s : ℚ) - j₁ - j₂ - j₃ + 1) := by
    congr 1; ring
  have m2 : ratInvFactorial ((s : ℚ) - (j₁ - 1) - l₂ - l₃) =
      ratInvFactorial ((s : ℚ) - j₁ - l₂ - l₃ + 1) := by
    congr 1; ring
  have m3 : ratInvFactorial (j₁ - 1 + j₂ + l₁ + l₂ - s) =
      ((j₁ + j₂ + l₁ + l₂ - s : ℚ) : ℝ) * ratInvFactorial (j₁ + j₂ + l₁ + l₂ - s) := by
    rw [← R _ (m₁ - s) (by push_cast; linarith)]; congr 1; ring
  have m4 : ratInvFactorial (j₃ + (j₁ - 1) + l₃ + l₁ - s) =
      ((j₃ + j₁ + l₃ + l₁ - s : ℚ) : ℝ) * ratInvFactorial (j₃ + j₁ + l₃ + l₁ - s) := by
    rw [← R _ (m₃ - s) (by push_cast; linarith)]; congr 1; ring
  -- `H s`
  have w3 : ratInvFactorial ((s : ℚ) - l₁ - j₂ - l₃ - 1) =
      (((s : ℚ) - l₁ - j₂ - l₃ : ℚ) : ℝ) * ratInvFactorial ((s : ℚ) - l₁ - j₂ - l₃) :=
    R _ (s - n₃) (by push_cast; linarith)
  have w4 : ratInvFactorial ((s : ℚ) - l₁ - l₂ - j₃ - 1) =
      (((s : ℚ) - l₁ - l₂ - j₃ : ℚ) : ℝ) * ratInvFactorial ((s : ℚ) - l₁ - l₂ - j₃) :=
    R _ (s - n₄) (by push_cast; linarith)
  -- `H (s + 1)`
  have z1 : ratInvFactorial (((s + 1 : ℕ) : ℚ) - j₁ - j₂ - j₃) =
      ratInvFactorial ((s : ℚ) - j₁ - j₂ - j₃ + 1) := by congr 1; push_cast; ring
  have z2 : ratInvFactorial (((s + 1 : ℕ) : ℚ) - j₁ - l₂ - l₃) =
      ratInvFactorial ((s : ℚ) - j₁ - l₂ - l₃ + 1) := by congr 1; push_cast; ring
  have z3 : ratInvFactorial (((s + 1 : ℕ) : ℚ) - l₁ - j₂ - l₃ - 1) =
      ratInvFactorial ((s : ℚ) - l₁ - j₂ - l₃) := by congr 1; push_cast; ring
  have z4 : ratInvFactorial (((s + 1 : ℕ) : ℚ) - l₁ - l₂ - j₃ - 1) =
      ratInvFactorial ((s : ℚ) - l₁ - l₂ - j₃) := by congr 1; push_cast; ring
  have z5 : ratInvFactorial (j₁ + j₂ + l₁ + l₂ + 1 - ((s + 1 : ℕ) : ℚ)) =
      ratInvFactorial (j₁ + j₂ + l₁ + l₂ - s) := by congr 1; push_cast; ring
  have z6 : ratInvFactorial (j₂ + j₃ + l₂ + l₃ - ((s + 1 : ℕ) : ℚ)) =
      ((j₂ + j₃ + l₂ + l₃ - s : ℚ) : ℝ) * ratInvFactorial (j₂ + j₃ + l₂ + l₃ - s) := by
    rw [← R _ (m₂ - s) (by push_cast; linarith)]; congr 1; push_cast; ring
  have z7 : ratInvFactorial (j₃ + j₁ + l₃ + l₁ + 1 - ((s + 1 : ℕ) : ℚ)) =
      ratInvFactorial (j₃ + j₁ + l₃ + l₁ - s) := by congr 1; push_cast; ring
  simp only [hHdef, racahTerm6j]
  rw [z1, z2, z3, z4, z5, z6, z7, w3, w4, p1, p2, p3, p4, m1, m2, m3, m4, u1, u2, v1, v3,
    Nat.factorial_succ (s + 1), pow_succ]
  have hp := hpoly s
  push_cast at hp ⊢
  linear_combination ((-1 : ℝ) ^ s * ((s + 1).factorial : ℝ) *
    ratInvFactorial ((s : ℚ) - j₁ - j₂ - j₃ + 1) * ratInvFactorial ((s : ℚ) - j₁ - l₂ - l₃ + 1) *
    ratInvFactorial ((s : ℚ) - l₁ - j₂ - l₃) * ratInvFactorial ((s : ℚ) - l₁ - l₂ - j₃) *
    ratInvFactorial (j₁ + j₂ + l₁ + l₂ + 1 - s) * ratInvFactorial (j₂ + j₃ + l₂ + l₃ - s) *
    ratInvFactorial (j₃ + j₁ + l₃ + l₁ + 1 - s)) * hp

/-- The polynomial factor of the telescoping certificate of the `6j` recursion, in the
variables `Xᵢ = s - aᵢ` and `Yₖ = bₖ - s` (the factorial arguments of 34.4.2). -/
private def sixJRecursionCertificate (X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ : ℝ) : ℝ :=
  (-X₁ * X₂ * X₃ ^ (2 : ℕ) * X₄ - X₁ * X₂ * X₃ ^ (2 : ℕ) * Y₁ - X₁ * X₂ * X₃ ^ (2 : ℕ) * Y₃
    - 2 * X₁ * X₂ * X₃ ^ (2 : ℕ) - X₁ * X₂ * X₃ * X₄ ^ (2 : ℕ) - 3 * X₁ * X₂ * X₃ * X₄ * Y₁
    - 3 * X₁ * X₂ * X₃ * X₄ * Y₃ - 4 * X₁ * X₂ * X₃ * X₄ - 2 * X₁ * X₂ * X₃ * Y₁ ^ (2 : ℕ)
    - 4 * X₁ * X₂ * X₃ * Y₁ * Y₃ - 6 * X₁ * X₂ * X₃ * Y₁ - 2 * X₁ * X₂ * X₃ * Y₃ ^ (2 : ℕ)
    - 6 * X₁ * X₂ * X₃ * Y₃ - 4 * X₁ * X₂ * X₃ - X₁ * X₂ * X₄ ^ (2 : ℕ) * Y₁
    - X₁ * X₂ * X₄ ^ (2 : ℕ) * Y₃ - 2 * X₁ * X₂ * X₄ ^ (2 : ℕ) - 2 * X₁ * X₂ * X₄ * Y₁ ^ (2 : ℕ)
    - 4 * X₁ * X₂ * X₄ * Y₁ * Y₃ - 6 * X₁ * X₂ * X₄ * Y₁ - 2 * X₁ * X₂ * X₄ * Y₃ ^ (2 : ℕ)
    - 6 * X₁ * X₂ * X₄ * Y₃ - 4 * X₁ * X₂ * X₄ - X₁ * X₂ * Y₁ ^ (3 : ℕ)
    - 3 * X₁ * X₂ * Y₁ ^ (2 : ℕ) * Y₃ - 4 * X₁ * X₂ * Y₁ ^ (2 : ℕ)
    - 3 * X₁ * X₂ * Y₁ * Y₃ ^ (2 : ℕ) - 10 * X₁ * X₂ * Y₁ * Y₃ - 6 * X₁ * X₂ * Y₁
    - X₁ * X₂ * Y₃ ^ (3 : ℕ) - 4 * X₁ * X₂ * Y₃ ^ (2 : ℕ) - 6 * X₁ * X₂ * Y₃ - 2 * X₁ * X₂
    - X₁ * X₃ ^ (2 : ℕ) * Y₁ * Y₃ - X₁ * X₃ ^ (2 : ℕ) * Y₁ - X₁ * X₃ ^ (2 : ℕ) * Y₃
    - X₁ * X₃ ^ (2 : ℕ) - 2 * X₁ * X₃ * X₄ * Y₁ * Y₃ - 2 * X₁ * X₃ * X₄ * Y₁
    - 2 * X₁ * X₃ * X₄ * Y₃ - 2 * X₁ * X₃ * X₄ - 2 * X₁ * X₃ * Y₁ ^ (2 : ℕ) * Y₃
    - 2 * X₁ * X₃ * Y₁ ^ (2 : ℕ) - X₁ * X₃ * Y₁ * Y₂ * Y₃ - X₁ * X₃ * Y₁ * Y₂
    - 2 * X₁ * X₃ * Y₁ * Y₃ ^ (2 : ℕ) - 7 * X₁ * X₃ * Y₁ * Y₃ - 5 * X₁ * X₃ * Y₁
    - X₁ * X₃ * Y₂ * Y₃ - X₁ * X₃ * Y₂ - 2 * X₁ * X₃ * Y₃ ^ (2 : ℕ) - 5 * X₁ * X₃ * Y₃
    - 3 * X₁ * X₃ - X₁ * X₄ ^ (2 : ℕ) * Y₁ * Y₃ - X₁ * X₄ ^ (2 : ℕ) * Y₁ - X₁ * X₄ ^ (2 : ℕ) * Y₃
    - X₁ * X₄ ^ (2 : ℕ) - 2 * X₁ * X₄ * Y₁ ^ (2 : ℕ) * Y₃ - 2 * X₁ * X₄ * Y₁ ^ (2 : ℕ)
    - X₁ * X₄ * Y₁ * Y₂ * Y₃ - X₁ * X₄ * Y₁ * Y₂ - 2 * X₁ * X₄ * Y₁ * Y₃ ^ (2 : ℕ)
    - 7 * X₁ * X₄ * Y₁ * Y₃ - 5 * X₁ * X₄ * Y₁ - X₁ * X₄ * Y₂ * Y₃ - X₁ * X₄ * Y₂
    - 2 * X₁ * X₄ * Y₃ ^ (2 : ℕ) - 5 * X₁ * X₄ * Y₃ - 3 * X₁ * X₄ - X₁ * Y₁ ^ (3 : ℕ) * Y₃
    - X₁ * Y₁ ^ (3 : ℕ) - X₁ * Y₁ ^ (2 : ℕ) * Y₂ * Y₃ - X₁ * Y₁ ^ (2 : ℕ) * Y₂
    - 2 * X₁ * Y₁ ^ (2 : ℕ) * Y₃ ^ (2 : ℕ) - 6 * X₁ * Y₁ ^ (2 : ℕ) * Y₃ - 4 * X₁ * Y₁ ^ (2 : ℕ)
    - X₁ * Y₁ * Y₂ * Y₃ ^ (2 : ℕ) - 4 * X₁ * Y₁ * Y₂ * Y₃ - 3 * X₁ * Y₁ * Y₂
    - X₁ * Y₁ * Y₃ ^ (3 : ℕ) - 6 * X₁ * Y₁ * Y₃ ^ (2 : ℕ) - 10 * X₁ * Y₁ * Y₃ - 5 * X₁ * Y₁
    - X₁ * Y₂ * Y₃ ^ (2 : ℕ) - 3 * X₁ * Y₂ * Y₃ - 2 * X₁ * Y₂ - X₁ * Y₃ ^ (3 : ℕ)
    - 4 * X₁ * Y₃ ^ (2 : ℕ) - 5 * X₁ * Y₃ - 2 * X₁ - X₂ * X₃ ^ (2 : ℕ) * Y₁ * Y₃
    - X₂ * X₃ ^ (2 : ℕ) * Y₁ - X₂ * X₃ ^ (2 : ℕ) * Y₃ - X₂ * X₃ ^ (2 : ℕ)
    - 2 * X₂ * X₃ * X₄ * Y₁ * Y₃ - 2 * X₂ * X₃ * X₄ * Y₁ - 2 * X₂ * X₃ * X₄ * Y₃
    - 2 * X₂ * X₃ * X₄ - 2 * X₂ * X₃ * Y₁ ^ (2 : ℕ) * Y₃ - 2 * X₂ * X₃ * Y₁ ^ (2 : ℕ)
    - X₂ * X₃ * Y₁ * Y₂ * Y₃ - X₂ * X₃ * Y₁ * Y₂ - 2 * X₂ * X₃ * Y₁ * Y₃ ^ (2 : ℕ)
    - 7 * X₂ * X₃ * Y₁ * Y₃ - 5 * X₂ * X₃ * Y₁ - X₂ * X₃ * Y₂ * Y₃ - X₂ * X₃ * Y₂
    - 2 * X₂ * X₃ * Y₃ ^ (2 : ℕ) - 5 * X₂ * X₃ * Y₃ - 3 * X₂ * X₃ - X₂ * X₄ ^ (2 : ℕ) * Y₁ * Y₃
    - X₂ * X₄ ^ (2 : ℕ) * Y₁ - X₂ * X₄ ^ (2 : ℕ) * Y₃ - X₂ * X₄ ^ (2 : ℕ)
    - 2 * X₂ * X₄ * Y₁ ^ (2 : ℕ) * Y₃ - 2 * X₂ * X₄ * Y₁ ^ (2 : ℕ) - X₂ * X₄ * Y₁ * Y₂ * Y₃
    - X₂ * X₄ * Y₁ * Y₂ - 2 * X₂ * X₄ * Y₁ * Y₃ ^ (2 : ℕ) - 7 * X₂ * X₄ * Y₁ * Y₃
    - 5 * X₂ * X₄ * Y₁ - X₂ * X₄ * Y₂ * Y₃ - X₂ * X₄ * Y₂ - 2 * X₂ * X₄ * Y₃ ^ (2 : ℕ)
    - 5 * X₂ * X₄ * Y₃ - 3 * X₂ * X₄ - X₂ * Y₁ ^ (3 : ℕ) * Y₃ - X₂ * Y₁ ^ (3 : ℕ)
    - X₂ * Y₁ ^ (2 : ℕ) * Y₂ * Y₃ - X₂ * Y₁ ^ (2 : ℕ) * Y₂ - 2 * X₂ * Y₁ ^ (2 : ℕ) * Y₃ ^ (2 : ℕ)
    - 6 * X₂ * Y₁ ^ (2 : ℕ) * Y₃ - 4 * X₂ * Y₁ ^ (2 : ℕ) - X₂ * Y₁ * Y₂ * Y₃ ^ (2 : ℕ)
    - 4 * X₂ * Y₁ * Y₂ * Y₃ - 3 * X₂ * Y₁ * Y₂ - X₂ * Y₁ * Y₃ ^ (3 : ℕ)
    - 6 * X₂ * Y₁ * Y₃ ^ (2 : ℕ) - 10 * X₂ * Y₁ * Y₃ - 5 * X₂ * Y₁ - X₂ * Y₂ * Y₃ ^ (2 : ℕ)
    - 3 * X₂ * Y₂ * Y₃ - 2 * X₂ * Y₂ - X₂ * Y₃ ^ (3 : ℕ) - 4 * X₂ * Y₃ ^ (2 : ℕ) - 5 * X₂ * Y₃
    - 2 * X₂ - X₃ ^ (2 : ℕ) * Y₁ * Y₂ * Y₃ - X₃ ^ (2 : ℕ) * Y₁ * Y₂ - X₃ ^ (2 : ℕ) * Y₁ * Y₃
    - X₃ ^ (2 : ℕ) * Y₁ - X₃ ^ (2 : ℕ) * Y₂ * Y₃ - X₃ ^ (2 : ℕ) * Y₂ - X₃ ^ (2 : ℕ) * Y₃
    - X₃ ^ (2 : ℕ) - 2 * X₃ * X₄ * Y₁ * Y₂ * Y₃ - 2 * X₃ * X₄ * Y₁ * Y₂ - 2 * X₃ * X₄ * Y₁ * Y₃
    - 2 * X₃ * X₄ * Y₁ - 2 * X₃ * X₄ * Y₂ * Y₃ - 2 * X₃ * X₄ * Y₂ - 2 * X₃ * X₄ * Y₃ - 2 * X₃ * X₄
    - 2 * X₃ * Y₁ ^ (2 : ℕ) * Y₂ * Y₃ - 2 * X₃ * Y₁ ^ (2 : ℕ) * Y₂ - 2 * X₃ * Y₁ ^ (2 : ℕ) * Y₃
    - 2 * X₃ * Y₁ ^ (2 : ℕ) - X₃ * Y₁ * Y₂ ^ (2 : ℕ) * Y₃ - X₃ * Y₁ * Y₂ ^ (2 : ℕ)
    - 2 * X₃ * Y₁ * Y₂ * Y₃ ^ (2 : ℕ) - 8 * X₃ * Y₁ * Y₂ * Y₃ - 6 * X₃ * Y₁ * Y₂
    - 2 * X₃ * Y₁ * Y₃ ^ (2 : ℕ) - 7 * X₃ * Y₁ * Y₃ - 5 * X₃ * Y₁ - X₃ * Y₂ ^ (2 : ℕ) * Y₃
    - X₃ * Y₂ ^ (2 : ℕ) - 2 * X₃ * Y₂ * Y₃ ^ (2 : ℕ) - 6 * X₃ * Y₂ * Y₃ - 4 * X₃ * Y₂
    - 2 * X₃ * Y₃ ^ (2 : ℕ) - 5 * X₃ * Y₃ - 3 * X₃ - X₄ ^ (2 : ℕ) * Y₁ * Y₂ * Y₃
    - X₄ ^ (2 : ℕ) * Y₁ * Y₂ - X₄ ^ (2 : ℕ) * Y₁ * Y₃ - X₄ ^ (2 : ℕ) * Y₁ - X₄ ^ (2 : ℕ) * Y₂ * Y₃
    - X₄ ^ (2 : ℕ) * Y₂ - X₄ ^ (2 : ℕ) * Y₃ - X₄ ^ (2 : ℕ) - 2 * X₄ * Y₁ ^ (2 : ℕ) * Y₂ * Y₃
    - 2 * X₄ * Y₁ ^ (2 : ℕ) * Y₂ - 2 * X₄ * Y₁ ^ (2 : ℕ) * Y₃ - 2 * X₄ * Y₁ ^ (2 : ℕ)
    - X₄ * Y₁ * Y₂ ^ (2 : ℕ) * Y₃ - X₄ * Y₁ * Y₂ ^ (2 : ℕ) - 2 * X₄ * Y₁ * Y₂ * Y₃ ^ (2 : ℕ)
    - 8 * X₄ * Y₁ * Y₂ * Y₃ - 6 * X₄ * Y₁ * Y₂ - 2 * X₄ * Y₁ * Y₃ ^ (2 : ℕ) - 7 * X₄ * Y₁ * Y₃
    - 5 * X₄ * Y₁ - X₄ * Y₂ ^ (2 : ℕ) * Y₃ - X₄ * Y₂ ^ (2 : ℕ) - 2 * X₄ * Y₂ * Y₃ ^ (2 : ℕ)
    - 6 * X₄ * Y₂ * Y₃ - 4 * X₄ * Y₂ - 2 * X₄ * Y₃ ^ (2 : ℕ) - 5 * X₄ * Y₃ - 3 * X₄
    - Y₁ ^ (3 : ℕ) * Y₂ * Y₃ - Y₁ ^ (3 : ℕ) * Y₂ - Y₁ ^ (3 : ℕ) * Y₃ - Y₁ ^ (3 : ℕ)
    - Y₁ ^ (2 : ℕ) * Y₂ ^ (2 : ℕ) * Y₃ - Y₁ ^ (2 : ℕ) * Y₂ ^ (2 : ℕ)
    - 2 * Y₁ ^ (2 : ℕ) * Y₂ * Y₃ ^ (2 : ℕ) - 7 * Y₁ ^ (2 : ℕ) * Y₂ * Y₃ - 5 * Y₁ ^ (2 : ℕ) * Y₂
    - 2 * Y₁ ^ (2 : ℕ) * Y₃ ^ (2 : ℕ) - 6 * Y₁ ^ (2 : ℕ) * Y₃ - 4 * Y₁ ^ (2 : ℕ)
    - Y₁ * Y₂ ^ (2 : ℕ) * Y₃ ^ (2 : ℕ) - 4 * Y₁ * Y₂ ^ (2 : ℕ) * Y₃ - 3 * Y₁ * Y₂ ^ (2 : ℕ)
    - Y₁ * Y₂ * Y₃ ^ (3 : ℕ) - 7 * Y₁ * Y₂ * Y₃ ^ (2 : ℕ) - 14 * Y₁ * Y₂ * Y₃ - 8 * Y₁ * Y₂
    - Y₁ * Y₃ ^ (3 : ℕ) - 6 * Y₁ * Y₃ ^ (2 : ℕ) - 10 * Y₁ * Y₃ - 5 * Y₁
    - Y₂ ^ (2 : ℕ) * Y₃ ^ (2 : ℕ) - 3 * Y₂ ^ (2 : ℕ) * Y₃ - 2 * Y₂ ^ (2 : ℕ) - Y₂ * Y₃ ^ (3 : ℕ)
    - 5 * Y₂ * Y₃ ^ (2 : ℕ) - 8 * Y₂ * Y₃ - 4 * Y₂ - Y₃ ^ (3 : ℕ) - 4 * Y₃ ^ (2 : ℕ) - 5 * Y₃
    - 2) / 2

set_option maxHeartbeats 1000000 in
/-- The telescoping certificate of the `6j` recursion, as a polynomial identity. -/
private theorem sixJ_recursion_certificate {j₁ j₂ j₃ l₁ l₂ l₃ x X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ X₁' X₂' X₃'
    X₄' Y₁' Y₂' Y₃' : ℝ} (hj₁ : j₁ = (X₃ + X₄ + Y₁ + Y₃) / 2)
    (hj₂ : j₂ = (X₂ + X₄ + Y₁ + Y₂) / 2) (hj₃ : j₃ = (X₂ + X₃ + Y₂ + Y₃) / 2)
    (hl₁ : l₁ = (X₁ + X₂ + Y₁ + Y₃) / 2) (hl₂ : l₂ = (X₁ + X₃ + Y₁ + Y₂) / 2)
    (hl₃ : l₃ = (X₁ + X₄ + Y₂ + Y₃) / 2) (hx : x = X₁ + X₂ + X₃ + X₄ + Y₁ + Y₂ + Y₃)
    (h₁ : X₁' = X₁ + 1) (h₂ : X₂' = X₂ + 1) (h₃ : X₃' = X₃ + 1) (h₄ : X₄' = X₄ + 1)
    (h₅ : Y₁' = Y₁ - 1) (h₆ : Y₂' = Y₂ - 1) (h₇ : Y₃' = Y₃ - 1) :
    -((2 * j₁ + 1) * ((j₃ * (j₃ + 1) + j₂ * (j₂ + 1) - j₁ * (j₁ + 1)) *
        (l₃ * (l₃ + 1) + l₂ * (l₂ + 1) - j₁ * (j₁ + 1)) -
        2 * (j₃ * (j₃ + 1) * (l₃ * (l₃ + 1)) + j₂ * (j₂ + 1) * (l₂ * (l₂ + 1)) -
          j₁ * (j₁ + 1) * (l₁ * (l₁ + 1))))) * ((X₁ + 1) * (X₂ + 1) * (Y₁ + 1) * (Y₃ + 1)) +
      j₁ * ((j₁ + j₂ - j₃ + 1) * (j₁ - j₂ + j₃ + 1) * (j₁ + l₂ - l₃ + 1) * (j₁ - l₂ + l₃ + 1)) *
        (X₁ * (X₁ + 1) * (X₂ * (X₂ + 1))) +
      (j₁ + 1) * ((-j₁ + j₂ + j₃ + 1) * (j₁ + j₂ + j₃ + 1) * (-j₁ + l₂ + l₃ + 1) *
          (j₁ + l₂ + l₃ + 1)) * (Y₁ * (Y₁ + 1) * (Y₃ * (Y₃ + 1))) =
      -((x + 2) * (Y₁ + 1) * Y₂ * (Y₃ + 1)) *
          sixJRecursionCertificate X₁' X₂' X₃' X₄' Y₁' Y₂' Y₃' -
        (X₁ + 1) * (X₂ + 1) * X₃ * X₄ * sixJRecursionCertificate X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ := by
  subst hj₁ hj₂ hj₃ hl₁ hl₂ hl₃ hx h₁ h₂ h₃ h₄ h₅ h₆ h₇
  unfold sixJRecursionCertificate
  ring

/-- `(x + 1)! = (x + 1) x!` for a natural number `x`. -/
private lemma ratFactorial_add_one {x : ℚ} (hx : IsNatQ x) : ratFactorial (x + 1) = ((x : ℝ) + 1) *
    ratFactorial x := by
  obtain ⟨n, rfl⟩ := hx
  rw [show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by push_cast; ring, ratFactorial_natCast,
                                                ratFactorial_natCast,
    Nat.factorial_succ]
  push_cast
  ring

private lemma ratFactorial_pos (x : ℚ) : 0 < ratFactorial x := by unfold ratFactorial; positivity

/-- Combining square roots: `√x (√y √z) = √w √u v` from `x y z = w u v²`. -/
private lemma sqrt_mul_sqrt_mul_sqrt_eq {x y z w u v : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hw : 0 ≤ w) (hu : 0 ≤ u) (hv : 0 ≤ v) (h : x * (y * z) = w * u * v ^ 2) :
    Real.sqrt x * (Real.sqrt y * Real.sqrt z) = Real.sqrt w * Real.sqrt u * v := by
  rw [← Real.sqrt_mul hy, ← Real.sqrt_mul hx, h, Real.sqrt_mul (mul_nonneg hw hu),
    Real.sqrt_mul hw, Real.sqrt_sq hv]

set_option maxHeartbeats 1000000 in
/-- The square-root factors of the `6j` recursion for the raised symbol. -/
private lemma sixJRecursionE_mul_triangleDelta_add_one {j₁ j₂ j₃ l₂ l₃ : ℚ}
    (hA : IsNatQ (j₁ + j₂ - j₃)) (hB : IsNatQ (j₁ - j₂ + j₃)) (hC : IsNatQ (-(j₁ + 1) + j₂ + j₃))
    (hA' : IsNatQ (j₁ + l₂ - l₃)) (hB' : IsNatQ (j₁ - l₂ + l₃))
    (hC' : IsNatQ (-(j₁ + 1) + l₂ + l₃)) :
    sixJRecursionE j₂ j₃ l₂ l₃ (j₁ + 1) * (triangleDelta (j₁ + 1) j₂ j₃ *
      triangleDelta (j₁ + 1) l₂ l₃) =
      triangleDelta j₁ j₂ j₃ * triangleDelta j₁ l₂ l₃ *
        (((j₁ : ℝ) + j₂ - j₃ + 1) * ((j₁ : ℝ) - j₂ + j₃ + 1) * ((j₁ : ℝ) + l₂ - l₃ + 1) *
          ((j₁ : ℝ) - l₂ + l₃ + 1)) := by
  have hA0 := hA.nonneg; have hB0 := hB.nonneg; have hC0 := hC.nonneg
  have hA0' := hA'.nonneg; have hB0' := hB'.nonneg; have hC0' := hC'.nonneg
  have qA : (0 : ℝ) ≤ (j₁ : ℝ) + j₂ - j₃ := by exact_mod_cast hA0
  have qB : (0 : ℝ) ≤ (j₁ : ℝ) - j₂ + j₃ := by exact_mod_cast hB0
  have qC : (0 : ℝ) ≤ -((j₁ : ℝ) + 1) + j₂ + j₃ := by exact_mod_cast hC0
  have qA' : (0 : ℝ) ≤ (j₁ : ℝ) + l₂ - l₃ := by exact_mod_cast hA0'
  have qB' : (0 : ℝ) ≤ (j₁ : ℝ) - l₂ + l₃ := by exact_mod_cast hB0'
  have qC' : (0 : ℝ) ≤ -((j₁ : ℝ) + 1) + l₂ + l₃ := by exact_mod_cast hC0'
  have hY : (0 : ℝ) ≤ ((j₁ : ℝ) + j₂ - j₃ + 1) * ((j₁ : ℝ) - j₂ + j₃ + 1) *
      ((j₁ : ℝ) + l₂ - l₃ + 1) * ((j₁ : ℝ) - l₂ + l₃ + 1) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (j₁ : ℝ) + j₂ - j₃ + 1)
      (by linarith : (0 : ℝ) ≤ (j₁ : ℝ) - j₂ + j₃ + 1))
      (by linarith : (0 : ℝ) ≤ (j₁ : ℝ) + l₂ - l₃ + 1))
      (by linarith : (0 : ℝ) ≤ (j₁ : ℝ) - l₂ + l₃ + 1)
    exact this
  have hZ : (0 : ℝ) ≤ (-((j₁ : ℝ) + 1) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 2) *
      ((-((j₁ : ℝ) + 1) + l₂ + l₃ + 1) * ((j₁ : ℝ) + l₂ + l₃ + 2)) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
  have hE : ((((j₁ + 1) ^ 2 - (j₂ - j₃) ^ 2) * ((j₂ + j₃ + 1) ^ 2 - (j₁ + 1) ^ 2) *
      ((j₁ + 1) ^ 2 - (l₂ - l₃) ^ 2) * ((l₂ + l₃ + 1) ^ 2 - (j₁ + 1) ^ 2) : ℚ) : ℝ) =
      (((j₁ : ℝ) + j₂ - j₃ + 1) * ((j₁ : ℝ) - j₂ + j₃ + 1) *
        ((j₁ : ℝ) + l₂ - l₃ + 1) * ((j₁ : ℝ) - l₂ + l₃ + 1)) *
      ((-((j₁ : ℝ) + 1) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 2) *
        ((-((j₁ : ℝ) + 1) + l₂ + l₃ + 1) * ((j₁ : ℝ) + l₂ + l₃ + 2))) := by
    push_cast; ring
  unfold sixJRecursionE triangleDelta
  rw [hE]
  refine sqrt_mul_sqrt_mul_sqrt_eq (mul_nonneg hY hZ) (by unfold ratFactorial; positivity)
    (by unfold ratFactorial; positivity) (by unfold ratFactorial; positivity) hY ?_
  have f1 := ratFactorial_add_one hA
  have f2 := ratFactorial_add_one hB
  have f3 := ratFactorial_add_one hC
  have f4 := ratFactorial_add_one hA'
  have f5 := ratFactorial_add_one hB'
  have f6 := ratFactorial_add_one hC'
  have f7 := ratFactorial_add_one (x := j₁ + j₂ + j₃ + 1) (((hA.add hB).add hC).add
    (isNatQ_natCast 2) |>.of_eq (by push_cast; ring))
  have f8 := ratFactorial_add_one (x := j₁ + l₂ + l₃ + 1) (((hA'.add hB').add hC').add
    (isNatQ_natCast 2) |>.of_eq (by push_cast; ring))
  rw [show j₁ + 1 + j₂ - j₃ = j₁ + j₂ - j₃ + 1 by ring, show j₁ + 1 - j₂ + j₃ = j₁ - j₂ + j₃ + 1 by
      ring, show -j₁ + j₂ + j₃ = -(j₁ + 1) + j₂ + j₃ + 1 by ring,
    show j₁ + 1 + j₂ + j₃ + 1 = j₁ + j₂ + j₃ + 1 + 1 by ring,
    show j₁ + 1 + l₂ - l₃ = j₁ + l₂ - l₃ + 1 by ring, show j₁ + 1 - l₂ + l₃ = j₁ - l₂ + l₃ + 1 by
      ring, show -j₁ + l₂ + l₃ = -(j₁ + 1) + l₂ + l₃ + 1 by ring,
    show j₁ + 1 + l₂ + l₃ + 1 = j₁ + l₂ + l₃ + 1 + 1 by ring, f1, f2, f3, f4, f5, f6, f7, f8]
  have p1 := ratFactorial_pos (j₁ + j₂ + j₃ + 1)
  have p2 := ratFactorial_pos (j₁ + l₂ + l₃ + 1)
  have p3 : (0 : ℝ) < (j₁ : ℝ) + j₂ + j₃ + 1 + 1 := by linarith
  have p4 : (0 : ℝ) < (j₁ : ℝ) + l₂ + l₃ + 1 + 1 := by linarith
  push_cast
  have p5 : (0 : ℝ) < (j₁ : ℝ) + j₂ + j₃ + 2 := by linarith
  have p6 : (0 : ℝ) < (j₁ : ℝ) + l₂ + l₃ + 2 := by linarith
  rw [show (j₁ : ℝ) + j₂ + j₃ + 1 + 1 = (j₁ : ℝ) + j₂ + j₃ + 2 by ring,
    show (j₁ : ℝ) + l₂ + l₃ + 1 + 1 = (j₁ : ℝ) + l₂ + l₃ + 2 by ring]
  field_simp

set_option maxHeartbeats 1000000 in
/-- The square-root factors of the `6j` recursion for the lowered symbol. -/
private lemma sixJRecursionE_mul_triangleDelta_sub_one {j₁ j₂ j₃ l₂ l₃ : ℚ}
    (hA : IsNatQ (j₁ - 1 + j₂ - j₃)) (hB : IsNatQ (j₁ - 1 - j₂ + j₃)) (hC : IsNatQ (-j₁ + j₂ + j₃))
    (hA' : IsNatQ (j₁ - 1 + l₂ - l₃)) (hB' : IsNatQ (j₁ - 1 - l₂ + l₃))
    (hC' : IsNatQ (-j₁ + l₂ + l₃)) :
    sixJRecursionE j₂ j₃ l₂ l₃ j₁ * (triangleDelta (j₁ - 1) j₂ j₃ *
      triangleDelta (j₁ - 1) l₂ l₃) =
      triangleDelta j₁ j₂ j₃ * triangleDelta j₁ l₂ l₃ *
        ((-(j₁ : ℝ) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 1) * (-(j₁ : ℝ) + l₂ + l₃ + 1) *
          ((j₁ : ℝ) + l₂ + l₃ + 1)) := by
  have qA : (0 : ℝ) ≤ (j₁ : ℝ) - 1 + j₂ - j₃ := by exact_mod_cast hA.nonneg
  have qB : (0 : ℝ) ≤ (j₁ : ℝ) - 1 - j₂ + j₃ := by exact_mod_cast hB.nonneg
  have qC : (0 : ℝ) ≤ -(j₁ : ℝ) + j₂ + j₃ := by exact_mod_cast hC.nonneg
  have qA' : (0 : ℝ) ≤ (j₁ : ℝ) - 1 + l₂ - l₃ := by exact_mod_cast hA'.nonneg
  have qB' : (0 : ℝ) ≤ (j₁ : ℝ) - 1 - l₂ + l₃ := by exact_mod_cast hB'.nonneg
  have qC' : (0 : ℝ) ≤ -(j₁ : ℝ) + l₂ + l₃ := by exact_mod_cast hC'.nonneg
  have hY : (0 : ℝ) ≤ (-(j₁ : ℝ) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 1) *
      (-(j₁ : ℝ) + l₂ + l₃ + 1) * ((j₁ : ℝ) + l₂ + l₃ + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
      (by linarith)
  have hZ : (0 : ℝ) ≤ ((j₁ : ℝ) + j₂ - j₃) * ((j₁ : ℝ) - j₂ + j₃) *
      (((j₁ : ℝ) + l₂ - l₃) * ((j₁ : ℝ) - l₂ + l₃)) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
  have hE : (((j₁ ^ 2 - (j₂ - j₃) ^ 2) * ((j₂ + j₃ + 1) ^ 2 - j₁ ^ 2) *
      (j₁ ^ 2 - (l₂ - l₃) ^ 2) * ((l₂ + l₃ + 1) ^ 2 - j₁ ^ 2) : ℚ) : ℝ) =
      ((-(j₁ : ℝ) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 1) * (-(j₁ : ℝ) + l₂ + l₃ + 1) *
        ((j₁ : ℝ) + l₂ + l₃ + 1)) *
      (((j₁ : ℝ) + j₂ - j₃) * ((j₁ : ℝ) - j₂ + j₃) *
        (((j₁ : ℝ) + l₂ - l₃) * ((j₁ : ℝ) - l₂ + l₃))) := by
    push_cast; ring
  unfold sixJRecursionE triangleDelta
  rw [hE]
  refine sqrt_mul_sqrt_mul_sqrt_eq (mul_nonneg hY hZ) (by unfold ratFactorial; positivity)
    (by unfold ratFactorial; positivity) (by unfold ratFactorial; positivity) hY ?_
  have f1 := ratFactorial_add_one hA
  have f2 := ratFactorial_add_one hB
  have f3 := ratFactorial_add_one hC
  have f4 := ratFactorial_add_one hA'
  have f5 := ratFactorial_add_one hB'
  have f6 := ratFactorial_add_one hC'
  have f7 := ratFactorial_add_one (x := j₁ - 1 + j₂ + j₃ + 1) (((hA.add hB).add hC).add
    (isNatQ_natCast 2) |>.of_eq (by push_cast; ring))
  have f8 := ratFactorial_add_one (x := j₁ - 1 + l₂ + l₃ + 1) (((hA'.add hB').add hC').add
    (isNatQ_natCast 2) |>.of_eq (by push_cast; ring))
  rw [show j₁ + j₂ - j₃ = j₁ - 1 + j₂ - j₃ + 1 by ring, show j₁ - j₂ + j₃ = j₁ - 1 - j₂ + j₃ + 1 by
      ring, show -(j₁ - 1) + j₂ + j₃ = -j₁ + j₂ + j₃ + 1 by ring,
    show j₁ + j₂ + j₃ + 1 = j₁ - 1 + j₂ + j₃ + 1 + 1 by ring,
    show j₁ + l₂ - l₃ = j₁ - 1 + l₂ - l₃ + 1 by ring, show j₁ - l₂ + l₃ = j₁ - 1 - l₂ + l₃ + 1 by
      ring, show -(j₁ - 1) + l₂ + l₃ = -j₁ + l₂ + l₃ + 1 by ring,
    show j₁ + l₂ + l₃ + 1 = j₁ - 1 + l₂ + l₃ + 1 + 1 by ring, f1, f2, f3, f4, f5, f6, f7, f8]
  have p1 := ratFactorial_pos (j₁ - 1 + j₂ + j₃ + 1)
  have p2 := ratFactorial_pos (j₁ - 1 + l₂ + l₃ + 1)
  have p5 : (0 : ℝ) < (j₁ : ℝ) + j₂ + j₃ + 1 := by linarith
  have p6 : (0 : ℝ) < (j₁ : ℝ) + l₂ + l₃ + 1 := by linarith
  push_cast
  rw [show (j₁ : ℝ) - 1 + j₂ + j₃ + 1 + 1 = (j₁ : ℝ) + j₂ + j₃ + 1 by ring,
    show (j₁ : ℝ) - 1 + l₂ + l₃ + 1 + 1 = (j₁ : ℝ) + l₂ + l₃ + 1 by ring]
  field_simp
  ring


/-- A nonzero natural number minus one is natural. -/
private lemma IsNatQ.sub_one_of_ne_zero {x : ℚ} (hx : IsNatQ x) (h0 : x ≠ 0) :
    IsNatQ (x - 1) := by
  obtain ⟨n, rfl⟩ := hx
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at h0)
  exact ⟨k, by push_cast; ring⟩

/-- A natural number is an integer. -/
private lemma IsNatQ.exists_intCast {x : ℚ} (hx : IsNatQ x) : ∃ n : ℤ, x = n := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨n, by simp⟩

/-- A Racah term of 34.4.2 vanishes when one of its factorial arguments is negative. -/
private lemma racahTerm6j_eq_zero_of_or {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} {s : ℕ}
    (h : (s : ℚ) - j₁ - j₂ - j₃ < 0 ∨ (s : ℚ) - j₁ - l₂ - l₃ < 0 ∨
      (s : ℚ) - l₁ - j₂ - l₃ < 0 ∨ (s : ℚ) - l₁ - l₂ - j₃ < 0 ∨ j₁ + j₂ + l₁ + l₂ - s < 0 ∨
      j₂ + j₃ + l₂ + l₃ - s < 0 ∨ j₃ + j₁ + l₃ + l₁ - s < 0) :
    racahTerm6j j₁ j₂ j₃ l₁ l₂ l₃ s = 0 := by
  unfold racahTerm6j
  rcases h with h | h | h | h | h | h | h <;> simp [ratInvFactorial_of_neg h]

/-- DLMF 34.5.11–34.5.13: with `Jᵣ = jᵣ(jᵣ+1)`, `Lᵣ = lᵣ(lᵣ+1)` (34.5.12) and `E(j)` of
34.5.13 (`sixJRecursionE`),
`(2j₁+1)((J₃+J₂-J₁)(L₃+L₂-J₁) - 2(J₃L₃+J₂L₂-J₁L₁)) {j₁ j₂ j₃; l₁ l₂ l₃}`
`= j₁ E(j₁+1) {j₁+1 j₂ j₃; l₁ l₂ l₃} + (j₁+1) E(j₁) {j₁-1 j₂ j₃; l₁ l₂ l₃}`,
assuming the triangle conditions of `{j₁ j₂ j₃; l₁ l₂ l₃}`. -/
@[dlmf 34.5.E11, dlmf 34.5.E12]
theorem wigner6j_recursion {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : IsAdmissible6j j₁ j₂ j₃ l₁ l₂ l₃) :
    (((2 * j₁ + 1) * ((j₃ * (j₃ + 1) + j₂ * (j₂ + 1) - j₁ * (j₁ + 1)) *
        (l₃ * (l₃ + 1) + l₂ * (l₂ + 1) - j₁ * (j₁ + 1)) -
        2 * (j₃ * (j₃ + 1) * (l₃ * (l₃ + 1)) + j₂ * (j₂ + 1) * (l₂ * (l₂ + 1)) -
          j₁ * (j₁ + 1) * (l₁ * (l₁ + 1)))) : ℚ) : ℝ) * wigner6j j₁ j₂ j₃ l₁ l₂ l₃ =
      (j₁ : ℝ) * sixJRecursionE j₂ j₃ l₂ l₃ (j₁ + 1) * wigner6j (j₁ + 1) j₂ j₃ l₁ l₂ l₃ +
        ((j₁ + 1 : ℚ) : ℝ) * sixJRecursionE j₂ j₃ l₂ l₃ j₁ * wigner6j (j₁ - 1) j₂ j₃ l₁ l₂ l₃ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := isAdmissible6j_iff.mp h
  obtain ⟨n₁, e₁⟩ := (((h1.add h2).add h3).of_eq (by ring) :
    IsNatQ (j₁ + j₂ + j₃)).exists_intCast
  obtain ⟨n₂, e₂⟩ := (((h4.add h5).add h6).of_eq (by ring) :
    IsNatQ (j₁ + l₂ + l₃)).exists_intCast
  obtain ⟨n₃, e₃⟩ := (((h7.add h8).add h9).of_eq (by ring) :
    IsNatQ (l₁ + j₂ + l₃)).exists_intCast
  obtain ⟨n₄, e₄⟩ := (((h10.add h11).add h12).of_eq (by ring) :
    IsNatQ (l₁ + l₂ + j₃)).exists_intCast
  have hb₁ : IsNatQ (j₁ + j₂ + l₁ + l₂) :=
    (h1.add ((h10.add h11).add h12)).of_eq (by ring)
  have hb₂ : IsNatQ (j₂ + j₃ + l₂ + l₃) :=
    (h3.add ((h4.add h5).add h6)).of_eq (by ring)
  have hb₃ : IsNatQ (j₃ + j₁ + l₃ + l₁) :=
    (h2.add ((h7.add h8).add h9)).of_eq (by ring)
  obtain ⟨m₁, g₁⟩ := hb₁.exists_intCast
  obtain ⟨m₂, g₂⟩ := hb₂.exists_intCast
  obtain ⟨m₃, g₃⟩ := hb₃.exists_intCast
  have h30 : 0 ≤ l₁ + j₂ + l₃ := (((h7.add h8).add h9).of_eq (by ring) :
    IsNatQ (l₁ + j₂ + l₃)).nonneg
  set M := ⌊j₁ + j₂ + l₁ + l₂⌋.toNat + ⌊j₂ + j₃ + l₂ + l₃⌋.toNat + 1 with hM
  have hN : j₂ + j₃ + l₂ + l₃ < ((M + 1 : ℕ) : ℚ) := by
    have := hb₂.floor_toNat
    have := hb₁.nonneg
    rw [hM]; push_cast; linarith
  set Δ := triangleDelta j₁ j₂ j₃ * triangleDelta j₁ l₂ l₃ * triangleDelta l₁ j₂ l₃ *
    triangleDelta l₁ l₂ j₃ with hΔ
  set S := ∑ s ∈ range (M + 1), racahTerm6j j₁ j₂ j₃ l₁ l₂ l₃ s with hS
  set Sp := ∑ s ∈ range (M + 1), racahTerm6j (j₁ + 1) j₂ j₃ l₁ l₂ l₃ s with hSp
  set Sm := ∑ s ∈ range (M + 1), racahTerm6j (j₁ - 1) j₂ j₃ l₁ l₂ l₃ s with hSm
  have cert := sum_racahTerm6j_three_term e₁ e₂ e₃ e₄ g₁ g₂ g₃ h30 (M + 1) hN _ _ _
    (fun y => sixJRecursionCertificate (y - (j₁ + j₂ + j₃)) (y - (j₁ + l₂ + l₃))
      (y - (l₁ + j₂ + l₃)) (y - (l₁ + l₂ + j₃)) (j₁ + j₂ + l₁ + l₂ - y) (j₂ + j₃ + l₂ + l₃ - y)
      (j₃ + j₁ + l₃ + l₁ - y))
    (fun x => by
      refine sixJ_recursion_certificate (j₁ := (j₁ : ℝ)) (j₂ := j₂) (j₃ := j₃) (l₁ := l₁)
        (l₂ := l₂) (l₃ := l₃) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> ring)
  rw [← hS, ← hSp, ← hSm] at cert
  have hW : wigner6j j₁ j₂ j₃ l₁ l₂ l₃ = Δ * S := by
    unfold wigner6j
    simp only [h, ↓reduceIte]
    rw [sum_racahTerm6j_extend h M (by omega)]
  have hWp : (j₁ : ℝ) * sixJRecursionE j₂ j₃ l₂ l₃ (j₁ + 1) * wigner6j (j₁ + 1) j₂ j₃ l₁ l₂ l₃ =
      (j₁ : ℝ) * (((j₁ : ℝ) + j₂ - j₃ + 1) * ((j₁ : ℝ) - j₂ + j₃ + 1) *
        ((j₁ : ℝ) + l₂ - l₃ + 1) * ((j₁ : ℝ) - l₂ + l₃ + 1)) * Δ * Sp := by
    by_cases hp : IsAdmissible6j (j₁ + 1) j₂ j₃ l₁ l₂ l₃
    · obtain ⟨-, -, p3, -, -, p6, -⟩ := isAdmissible6j_iff.mp hp
      have key := sixJRecursionE_mul_triangleDelta_add_one h1 h2 p3 h4 h5 p6
      have hfl : ⌊j₁ + 1 + j₂ + l₁ + l₂⌋.toNat ≤ M := by
        rw [show j₁ + 1 + j₂ + l₁ + l₂ = j₁ + j₂ + l₁ + l₂ + 1 by ring, Int.floor_add_one]
        omega
      unfold wigner6j
      simp only [hp, ↓reduceIte]
      rw [sum_racahTerm6j_extend hp M hfl, ← hSp]
      linear_combination ((j₁ : ℝ) * triangleDelta l₁ j₂ l₃ * triangleDelta l₁ l₂ j₃ * Sp) * key
    · have hC : -j₁ + j₂ + j₃ = 0 ∨ -j₁ + l₂ + l₃ = 0 := by
        by_contra hc
        push Not at hc
        apply hp
        rw [isAdmissible6j_iff]
        exact ⟨h1.add (isNatQ_natCast 1) |>.of_eq (by push_cast; ring),
          h2.add (isNatQ_natCast 1) |>.of_eq (by push_cast; ring),
          (h3.sub_one_of_ne_zero hc.1).of_eq (by ring),
          h4.add (isNatQ_natCast 1) |>.of_eq (by push_cast; ring),
          h5.add (isNatQ_natCast 1) |>.of_eq (by push_cast; ring),
          (h6.sub_one_of_ne_zero hc.2).of_eq (by ring), h7, h8, h9, h10, h11, h12⟩
      have hSp0 : Sp = 0 := by
        refine sum_eq_zero fun s _ => racahTerm6j_eq_zero_of_or ?_
        rcases hC with hC | hC
        · rcases lt_or_ge (s : ℚ) (j₁ + 1 + l₂ + l₃) with hs | hs
          · exact Or.inr (Or.inl (by linarith))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
        · rcases lt_or_ge (s : ℚ) (j₁ + 1 + j₂ + j₃) with hs | hs
          · exact Or.inl (by linarith)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
      unfold wigner6j
      simp only [hp, ↓reduceIte]
      rw [hSp0]
      ring
  have hWm : ((j₁ : ℝ) + 1) * sixJRecursionE j₂ j₃ l₂ l₃ j₁ * wigner6j (j₁ - 1) j₂ j₃ l₁ l₂ l₃ =
      ((j₁ : ℝ) + 1) * ((-(j₁ : ℝ) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 1) *
        (-(j₁ : ℝ) + l₂ + l₃ + 1) * ((j₁ : ℝ) + l₂ + l₃ + 1)) * Δ * Sm := by
    by_cases hm : IsAdmissible6j (j₁ - 1) j₂ j₃ l₁ l₂ l₃
    · obtain ⟨p1, p2, -, p4, p5, -, -⟩ := isAdmissible6j_iff.mp hm
      have key := sixJRecursionE_mul_triangleDelta_sub_one p1 p2 h3 p4 p5 h6
      have hfl : ⌊j₁ - 1 + j₂ + l₁ + l₂⌋.toNat ≤ M := by
        have : ⌊j₁ - 1 + j₂ + l₁ + l₂⌋ ≤ ⌊j₁ + j₂ + l₁ + l₂⌋ := Int.floor_mono (by linarith)
        omega
      unfold wigner6j
      simp only [hm, ↓reduceIte]
      rw [sum_racahTerm6j_extend hm M hfl, ← hSm]
      linear_combination
        (((j₁ : ℝ) + 1) * triangleDelta l₁ j₂ l₃ * triangleDelta l₁ l₂ j₃ * Sm) * key
    · have hA : j₁ + j₂ - j₃ = 0 ∨ j₁ - j₂ + j₃ = 0 ∨ j₁ + l₂ - l₃ = 0 ∨ j₁ - l₂ + l₃ = 0 := by
        by_contra hc
        push Not at hc
        apply hm
        rw [isAdmissible6j_iff]
        exact ⟨(h1.sub_one_of_ne_zero hc.1).of_eq (by ring),
          (h2.sub_one_of_ne_zero hc.2.1).of_eq (by ring),
          h3.add (isNatQ_natCast 1) |>.of_eq (by push_cast; ring),
          (h4.sub_one_of_ne_zero hc.2.2.1).of_eq (by ring),
          (h5.sub_one_of_ne_zero hc.2.2.2).of_eq (by ring),
          h6.add (isNatQ_natCast 1) |>.of_eq (by push_cast; ring), h7, h8, h9, h10, h11, h12⟩
      have hSm0 : Sm = 0 := by
        refine sum_eq_zero fun s _ => racahTerm6j_eq_zero_of_or ?_
        rcases hA with hA | hA | hA | hA
        · rcases lt_or_ge (s : ℚ) (l₁ + l₂ + j₃) with hs | hs
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
        · rcases lt_or_ge (s : ℚ) (l₁ + j₂ + l₃) with hs | hs
          · exact Or.inr (Or.inr (Or.inl (by linarith)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))
        · rcases lt_or_ge (s : ℚ) (l₁ + j₂ + l₃) with hs | hs
          · exact Or.inr (Or.inr (Or.inl (by linarith)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
        · rcases lt_or_ge (s : ℚ) (l₁ + l₂ + j₃) with hs | hs
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))
      unfold wigner6j
      simp only [hm, ↓reduceIte]
      rw [hSm0]
      ring
  push_cast at hWm ⊢
  rw [hW]
  linear_combination -hWp - hWm - Δ * cert

end DLMF.WignerSymbols
