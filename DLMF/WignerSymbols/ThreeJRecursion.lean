/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.ThreeJ

/-!
# Recursion relations of the `3j` symbol

The recursion relations DLMF 34.3.13–34.3.15 of §34.3(iii) for `wigner3j`, stated for all
rational arguments.

## Main results

* `wigner3j_recursion_half`: DLMF 34.3.13.
* `wigner3j_recursion_m`: DLMF 34.3.14.
* `wigner3j_recursion_j`: DLMF 34.3.15.

## Implementation notes

Since `wigner3j` is `0` outside the admissible range (34.2.1–34.2.3), the recursions are stated
for all rational arguments; this is stronger than DLMF, which assumes the triangle conditions
for every symbol. Square roots are `Real.sqrt`, which is `0` at negative arguments; the
coefficients of the recursions vanish exactly where a symbol leaves the admissible range.

On the admissible range the three symbols share the prefactor of Racah's formula 34.2.4 up to
explicit polynomial factors, and each recursion reduces to a three-term contiguous relation of
Racah's sum in symmetric form (`symmetricRacahSum`). These are proved by telescoping: the
combination of the three summands is `H(s + 1) - H(s)` for an explicit hypergeometric term
`H` (a Gosper certificate), and a finitely supported telescoping sum over `ℤ` vanishes.
-/

@[expose] public noncomputable section

open Finset

namespace DLMF.WignerSymbols

/-! ## §34.3(iii) Recursion relations -/

/-- The summand of `symmetricRacahSum` has finite support. -/
private lemma finite_support_symmetricRacahSum_summand (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    (Function.support fun s : ℤ => (-1 : ℝ) ^ s *
        (ratInvFactorial (x₁ - s) * ratInvFactorial (x₂ - s) *
      ratInvFactorial (x₃ - s) *
          (ratInvFactorial (s - y₁) * ratInvFactorial (s - y₂) *
          ratInvFactorial (s - y₃)))).Finite := by
  apply (Set.finite_Icc (⌈y₁⌉) (⌊x₁⌋)).subset
  intro s hs
  simp only [Function.mem_support] at hs
  simp only [Set.mem_Icc]
  constructor
  · by_contra h
    apply hs
    rw [ratInvFactorial_of_neg (x := (s : ℚ) - y₁) (by
      have : (s : ℚ) < y₁ := by
        rw [not_le, Int.lt_ceil] at h; exact h
      linarith)]
    ring
  · by_contra h
    apply hs
    rw [ratInvFactorial_of_neg (x := x₁ - s) (by
      have : x₁ < (s : ℚ) := by
        rw [not_le, Int.floor_lt] at h; exact h
      linarith)]
    ring

/-- Contiguity of the symmetric Racah sum: lowering `x₃` and raising `y₃` by one. -/
private lemma symmetricRacahSum_contiguous (x₁ x₂ y₁ y₂ : ℚ) {x₃ y₃ : ℚ} {n k : ℤ} (hx : x₃ = n)
    (hy : y₃ = k) :
    symmetricRacahSum x₁ x₂ (x₃ - 1) y₁ y₂ y₃ + symmetricRacahSum x₁ x₂ x₃ y₁ y₂ (y₃ + 1) =
      ((x₃ - y₃ : ℚ) : ℝ) * symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ := by
  unfold symmetricRacahSum
  rw [← finsum_add_distrib (finite_support_symmetricRacahSum_summand _ _ _ _ _ _)
      (finite_support_symmetricRacahSum_summand _ _ _ _ _ _),
    mul_finsum]
  refine finsum_congr fun s => ?_
  rw [show x₃ - 1 - s = (x₃ - s) - 1 by ring, show (s : ℚ) - (y₃ + 1) = (s - y₃) - 1 by ring,
    ratInvFactorial_sub_one_of_eq_intCast (n := n - s) (by rw [hx]; push_cast; ring),
    ratInvFactorial_sub_one_of_eq_intCast (n := s - k) (by rw [hy]; push_cast; ring)]
  push_cast
  ring

/-- The symmetric Racah sum vanishes when `x₃ < y₂`. -/
private lemma symmetricRacahSum_eq_zero_of_lt (x₁ x₂ y₁ y₃ : ℚ) {x₃ y₂ : ℚ} (h : x₃ < y₂) :
    symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ = 0 := by
  unfold symmetricRacahSum
  convert finsum_zero with s
  rcases lt_or_ge (x₃ - s) 0 with h' | h'
  · rw [ratInvFactorial_of_neg h']; ring
  · rw [ratInvFactorial_of_neg (x := (s : ℚ) - y₂) (by linarith)]; ring


/-- DLMF 34.3.13. Stated for all arguments (stronger than DLMF, which assumes the triangle
conditions for each symbol). -/
@[dlmf 34.3.E13]
theorem wigner3j_recursion_half (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    Real.sqrt ((j₁ + j₂ + j₃ + 1) * (-j₁ + j₂ + j₃)) * wigner3j j₁ j₂ j₃ m₁ m₂ m₃ =
      Real.sqrt ((j₂ + m₂) * (j₃ - m₃)) *
          wigner3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ - 1 / 2) (m₃ + 1 / 2) -
        Real.sqrt ((j₂ - m₂) * (j₃ + m₃)) *
          wigner3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ + 1 / 2) (m₃ - 1 / 2) := by
  have one : IsNatQ 1 := ⟨1, by simp⟩
  by_cases hL : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ m₃
  swap
  · have h1 : ¬ IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ - 1 / 2) (m₃ + 1 / 2) := by
      rintro ⟨⟨t1, t2, t3⟩, p1, ⟨p2a, p2b⟩, ⟨p3a, p3b⟩, hs⟩
      exact hL ⟨⟨t1.of_eq (by ring), t2.of_eq (by ring), (t3.add one).of_eq (by ring)⟩, p1,
        ⟨p2a.of_eq (by ring), (p2b.add one).of_eq (by ring)⟩,
        ⟨(p3a.add one).of_eq (by ring), p3b.of_eq (by ring)⟩, by linarith⟩
    have h2 : ¬ IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ + 1 / 2) (m₃ - 1 / 2) := by
      rintro ⟨⟨t1, t2, t3⟩, p1, ⟨p2a, p2b⟩, ⟨p3a, p3b⟩, hs⟩
      exact hL ⟨⟨t1.of_eq (by ring), t2.of_eq (by ring), (t3.add one).of_eq (by ring)⟩, p1,
        ⟨(p2a.add one).of_eq (by ring), p2b.of_eq (by ring)⟩,
        ⟨p3a.of_eq (by ring), (p3b.add one).of_eq (by ring)⟩, by linarith⟩
    rw [wigner3j_of_not hL, wigner3j_of_not h1, wigner3j_of_not h2]; ring
  have hL' := hL
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩,
    ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, hm⟩ := hL'
  rcases c with _ | w
  · have h1 : ¬ IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ - 1 / 2) (m₃ + 1 / 2) := by
      rintro ⟨⟨-, -, t3⟩, -⟩
      have := t3.nonneg; push_cast at hc; linarith
    have h2 : ¬ IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ + 1 / 2) (m₃ - 1 / 2) := by
      rintro ⟨⟨-, -, t3⟩, -⟩
      have := t3.nonneg; push_cast at hc; linarith
    rw [wigner3j_of_not h1, wigner3j_of_not h2,
      show (-(j₁ : ℝ) + j₂ + j₃) = 0 by
        have := congrArg (Rat.cast : ℚ → ℝ) hc; push_cast at this; linarith]
    simp
  have hR : ∀ {x : ℚ} {n : ℕ}, x = n → (x : ℝ) = n := fun h => by rw [h]; simp
  have hJ : j₁ + j₂ + j₃ + 1 = ((a + b + w + 2 : ℕ) : ℚ) := by push_cast at hc ⊢; linarith
  set PL : ℝ := ratFactorial (j₁ + j₂ - j₃) * ratFactorial (j₁ - j₂ + j₃) *
      ratFactorial (-j₁ + j₂ + j₃) /
          ratFactorial (j₁ + j₂ + j₃ + 1) *
              (ratFactorial (j₁ + m₁) * ratFactorial (j₁ - m₁) * ratFactorial (j₂ + m₂) *
          ratFactorial (j₂ - m₂) * ratFactorial (j₃ + m₃) * ratFactorial (j₃ - m₃)) with hPL
  set K : ℝ := signPow (j₁ - j₂ - m₃) * Real.sqrt PL *
    Real.sqrt (((a + b + w + 2 : ℕ) : ℝ) / ((w + 1 : ℕ) : ℝ)) with hK
  have e1 : Real.sqrt ((j₂ + m₂) * (j₃ - m₃)) *
      wigner3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ - 1 / 2) (m₃ + 1 / 2) =
      K * symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) ((j₂ + m₂) - 1) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + m₂) := by
    rcases q₂ with _ | u
    · rw [symmetricRacahSum_swap_y12,
          symmetricRacahSum_eq_zero_of_lt _ _ _ _ (by push_cast at hq₂; linarith),
        show ((j₂ : ℝ) + m₂) = 0 by have := hR hq₂; push_cast at this; linarith]
      simp
    rcases p₃ with _ | v
    · rw [symmetricRacahSum_eq_zero_of_lt _ _ _ _ (by push_cast at hq₂ hp₃; linarith),
        show ((j₃ : ℝ) - m₃) = 0 by have := hR hp₃; push_cast at this; linarith]
      simp
    have hR1 : IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ - 1 / 2) (m₃ + 1 / 2) :=
      ⟨⟨⟨a, by linarith⟩, ⟨b, by linarith⟩, ⟨w, by push_cast at hc ⊢; linarith⟩⟩,
        ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, by linarith⟩, ⟨u, by push_cast at hq₂ ⊢; linarith⟩⟩,
        ⟨⟨v, by push_cast at hp₃ ⊢; linarith⟩, ⟨q₃, by linarith⟩⟩, by linarith⟩
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hR1, show j₁ - (j₂ - 1 / 2) - (m₃ + 1 / 2) = j₁ -
        j₂ - m₃ by ring,
      show symmetricRacahSum (j₁ + (j₂ - 1 / 2) - (j₃ - 1 / 2)) (j₁ - m₁)
          (j₂ - 1 / 2 + (m₂ - 1 / 2)) 0
        (j₂ - 1 / 2 - (j₃ - 1 / 2) - m₁) (j₁ - (j₃ - 1 / 2) + (m₂ - 1 / 2)) =
        symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) ((j₂ + m₂) - 1) 0 (j₂ - j₃ - m₁)
            (j₁ - j₃ + m₂) by
          congr 1 <;> ring, hK,
      show ∀ c s Q S : ℝ, c * (s * Q * S) = s * (c * Q) * S from fun _ _ _ _ => by ring]
    congr 1
    rw [mul_assoc (signPow (j₁ - j₂ - m₃))]
    congr 1
    have hu : (j₂ : ℝ) + m₂ = (u : ℝ) + 1 := by have := hR hq₂; push_cast at this; linarith
    have hv : (j₃ : ℝ) - m₃ = (v : ℝ) + 1 := by have := hR hp₃; push_cast at this; linarith
    have hPL0 : 0 ≤ PL := by rw [hPL]; wigner_cast_nonneg
    rw [hu, hv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul hPL0, hPL]
    congr 1
    rw [ratFactorial_of_eq (n := a) (show j₁ + (j₂ - 1 / 2) - (j₃ - 1 / 2) = (a : ℚ) by linarith),
      ratFactorial_of_eq (n := b) (show j₁ - (j₂ - 1 / 2) + (j₃ - 1 / 2) = (b : ℚ) by linarith),
      ratFactorial_of_eq (n := w) (show -j₁ + (j₂ - 1 / 2) + (j₃ - 1 / 2) = (w : ℚ) by
        push_cast at hc; linarith),
      ratFactorial_of_eq (n := a + b + w + 1) (show j₁ + (j₂ - 1 / 2) + (j₃ - 1 / 2) + 1 =
        ((a + b + w + 1 : ℕ) : ℚ) by push_cast at hJ ⊢; linarith),
      ratFactorial_of_eq (n := u) (show j₂ - 1 / 2 + (m₂ - 1 / 2) = (u : ℚ) by
        push_cast at hq₂; linarith),
      ratFactorial_of_eq (n := p₂) (show j₂ - 1 / 2 - (m₂ - 1 / 2) = (p₂ : ℚ) by linarith),
      ratFactorial_of_eq (n := q₃) (show j₃ - 1 / 2 + (m₃ + 1 / 2) = (q₃ : ℚ) by linarith),
      ratFactorial_of_eq (n := v) (show j₃ - 1 / 2 - (m₃ + 1 / 2) = (v : ℚ) by
        push_cast at hp₃; linarith),
      ha, hb, hc, hJ, hq₁, hp₁, hq₂, hp₂, hq₃, hp₃]
    simp only [ratFactorial_natCast, Nat.factorial_succ, show a + b + w + 2 =
        (a + b + w + 1) + 1 from rfl]
    push_cast
    field_simp
  have e2 : Real.sqrt ((j₂ - m₂) * (j₃ + m₃)) *
      wigner3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ + 1 / 2) (m₃ - 1 / 2) =
      -K * symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂) 0 (j₂ - j₃ - m₁)
          ((j₁ - j₃ + m₂) + 1) := by
    rcases p₂ with _ | u
    · rw [symmetricRacahSum_swap_x12, symmetricRacahSum_swap_x23, symmetricRacahSum_swap_y23,
        symmetricRacahSum_eq_zero_of_lt _ _ _ _ (by push_cast at hp₂; linarith),
        show ((j₂ : ℝ) - m₂) = 0 by have := hR hp₂; push_cast at this; linarith]
      simp
    rcases q₃ with _ | v
    · rw [symmetricRacahSum_swap_x23, symmetricRacahSum_swap_y23,
        symmetricRacahSum_eq_zero_of_lt _ _ _ _ (by push_cast at hq₃; linarith),
        show ((j₃ : ℝ) + m₃) = 0 by have := hR hq₃; push_cast at this; linarith]
      simp
    have hR2 : IsAdmissible3j j₁ (j₂ - 1 / 2) (j₃ - 1 / 2) m₁ (m₂ + 1 / 2) (m₃ - 1 / 2) :=
      ⟨⟨⟨a, by linarith⟩, ⟨b, by linarith⟩, ⟨w, by push_cast at hc ⊢; linarith⟩⟩,
        ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨u, by push_cast at hp₂ ⊢; linarith⟩, ⟨q₂, by linarith⟩⟩,
        ⟨⟨p₃, by linarith⟩, ⟨v, by push_cast at hq₃ ⊢; linarith⟩⟩, by linarith⟩
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hR2,
      show j₁ - (j₂ - 1 / 2) - (m₃ - 1 / 2) = j₁ - j₂ - m₃ + ((1 : ℤ) : ℚ) by push_cast; ring,
      signPow_add_intCast, zpow_one,
      show symmetricRacahSum (j₁ + (j₂ - 1 / 2) - (j₃ - 1 / 2)) (j₁ - m₁)
          (j₂ - 1 / 2 + (m₂ + 1 / 2)) 0
        (j₂ - 1 / 2 - (j₃ - 1 / 2) - m₁) (j₁ - (j₃ - 1 / 2) + (m₂ + 1 / 2)) =
        symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂) 0 (j₂ - j₃ - m₁)
            ((j₁ - j₃ + m₂) + 1) by
          congr 1 <;> ring, hK, neg_mul,
      show ∀ c s Q S : ℝ, c * (s * (-1) * Q * S) = -(s * (c * Q) * S) from
        fun _ _ _ _ => by ring]
    congr 2
    rw [mul_assoc (signPow (j₁ - j₂ - m₃))]
    congr 1
    have hu : (j₂ : ℝ) - m₂ = (u : ℝ) + 1 := by have := hR hp₂; push_cast at this; linarith
    have hv : (j₃ : ℝ) + m₃ = (v : ℝ) + 1 := by have := hR hq₃; push_cast at this; linarith
    have hPL0 : 0 ≤ PL := by rw [hPL]; wigner_cast_nonneg
    rw [hu, hv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul hPL0, hPL]
    congr 1
    rw [ratFactorial_of_eq (n := a) (show j₁ + (j₂ - 1 / 2) - (j₃ - 1 / 2) = (a : ℚ) by linarith),
      ratFactorial_of_eq (n := b) (show j₁ - (j₂ - 1 / 2) + (j₃ - 1 / 2) = (b : ℚ) by linarith),
      ratFactorial_of_eq (n := w) (show -j₁ + (j₂ - 1 / 2) + (j₃ - 1 / 2) = (w : ℚ) by
        push_cast at hc; linarith),
      ratFactorial_of_eq (n := a + b + w + 1) (show j₁ + (j₂ - 1 / 2) + (j₃ - 1 / 2) + 1 =
        ((a + b + w + 1 : ℕ) : ℚ) by push_cast at hJ ⊢; linarith),
      ratFactorial_of_eq (n := q₂) (show j₂ - 1 / 2 + (m₂ + 1 / 2) = (q₂ : ℚ) by linarith),
      ratFactorial_of_eq (n := u) (show j₂ - 1 / 2 - (m₂ + 1 / 2) = (u : ℚ) by
        push_cast at hp₂; linarith),
      ratFactorial_of_eq (n := v) (show j₃ - 1 / 2 + (m₃ - 1 / 2) = (v : ℚ) by
        push_cast at hq₃; linarith),
      ratFactorial_of_eq (n := p₃) (show j₃ - 1 / 2 - (m₃ - 1 / 2) = (p₃ : ℚ) by linarith),
      ha, hb, hc, hJ, hq₁, hp₁, hq₂, hp₂, hq₃, hp₃]
    simp only [ratFactorial_natCast, Nat.factorial_succ, show a + b + w + 2 =
        (a + b + w + 1) + 1 from rfl]
    push_cast
    field_simp
  rw [e1, e2, wigner3j_eq_sqrt_mul_symmetricRacahSum hL, ← hPL, show ∀ x y : ℝ, K * x - -K * y =
      K * (x + y) from
    fun x y => by ring, symmetricRacahSum_contiguous _ _ _ _ hq₂ (n := q₂) (k := (a : ℤ) - p₂) (by
      push_cast; linarith), hK]
  have hcR : (-(j₁ : ℝ) + j₂ + j₃) = ((w + 1 : ℕ) : ℝ) := by
    have := hR hc; push_cast at this ⊢; linarith
  have hJR : ((j₁ : ℝ) + j₂ + j₃ + 1) = ((a + b + w + 2 : ℕ) : ℝ) := by
    have := hR hJ; push_cast at this ⊢; linarith
  rw [hcR, hJR, show (((j₂ + m₂) - (j₁ - j₃ + m₂) : ℚ) : ℝ) = ((w + 1 : ℕ) : ℝ) by
    rw [show (j₂ + m₂) - (j₁ - j₃ + m₂) = -j₁ + j₂ + j₃ by ring, hR hc]]
  have hw : (0 : ℝ) < ((w + 1 : ℕ) : ℝ) := by positivity
  rw [Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity)]
  have hs : Real.sqrt ((w + 1 : ℕ) : ℝ) ^ 2 = ((w + 1 : ℕ) : ℝ) := Real.sq_sqrt hw.le
  have hs0 : Real.sqrt ((w + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  rw [hs]
  ring

/-- A multiple of the summand of `symmetricRacahSum` has finite support. -/
private lemma finite_support_mul_racahSummand (r : ℝ) (x₁ x₂ x₃ y₁ y₂ y₃ : ℚ) :
    (Function.support fun s : ℤ => r *
        ((-1 : ℝ) ^ s * (ratInvFactorial (x₁ - s) * ratInvFactorial (x₂ - s) *
      ratInvFactorial (x₃ - s) * (ratInvFactorial (s - y₁) * ratInvFactorial (s - y₂) *
        ratInvFactorial (s - y₃))))).Finite :=
  (finite_support_symmetricRacahSum_summand _ _ _ _ _ _).subset
    (Function.support_mul_subset_right _ _)

/-- A telescoping finite sum over `ℤ` vanishes. -/
private lemma finsum_sub_shift_eq_zero {H : ℤ → ℝ} (hH : (Function.support H).Finite) :
    ∑ᶠ s : ℤ, (H (s + 1) - H s) = 0 := by
  have h1 : (Function.support fun s : ℤ => H (s + 1)).Finite := by
    have : (Function.support fun s : ℤ => H (s + 1)) = (fun s => s + 1) ⁻¹' Function.support H :=
      rfl
    rw [this]
    exact hH.preimage (add_left_injective 1).injOn
  rw [finsum_sub_distrib h1 hH, sub_eq_zero]
  exact finsum_comp_equiv (Equiv.addRight 1)

/-- The three-term contiguous relation of the symmetric Racah sum in `(x₃, y₃)`. -/
private theorem symmetricRacahSum_three_term_x₃_y₃ {x₁ x₂ x₃ y₁ y₂ y₃ : ℚ} {n₁ n₂ n₃ k₁ k₂ k₃ : ℤ}
    (h₁ : x₁ = n₁) (h₂ : x₂ = n₂) (h₃ : x₃ = n₃) (g₁ : y₁ = k₁) (g₂ : y₂ = k₂) (g₃ : y₃ = k₃) :
    ((x₁ * x₂ - x₁ * x₃ - x₂ * x₃ + 2 * x₃ * y₃ - x₃ + y₁ * y₂ - y₁ * y₃ - y₂ * y₃ + y₃ : ℚ) : ℝ) *
        symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ +
      (((x₃ - y₁ + 1) * (x₃ - y₂ + 1) : ℚ) : ℝ) *
        symmetricRacahSum x₁ x₂ (x₃ + 1) y₁ y₂ (y₃ + 1) +
      (((x₁ - y₃ + 1) * (x₂ - y₃ + 1) : ℚ) : ℝ) *
        symmetricRacahSum x₁ x₂ (x₃ - 1) y₁ y₂ (y₃ - 1) = 0 := by
  set H : ℤ → ℝ := fun s => (-1 : ℝ) ^ s * (ratInvFactorial (x₁ - s) * ratInvFactorial (x₂ - s) *
      ratInvFactorial ((x₃ + 1) - s) *
          (ratInvFactorial (s - (y₁ + 1)) * ratInvFactorial (s - (y₂ + 1)) *
        ratInvFactorial (s - y₃))) with hHdef
  have hH : (Function.support H).Finite := finite_support_symmetricRacahSum_summand _ _ _ _ _ _
  unfold symmetricRacahSum
  rw [mul_finsum, mul_finsum, mul_finsum,
    ← finsum_add_distrib ((finite_support_mul_racahSummand _ _ _ _ _ _ _))
      ((finite_support_mul_racahSummand _ _ _ _ _ _ _)),
    ← finsum_add_distrib (((finite_support_mul_racahSummand _ _ _ _ _ _ _)).union
      ((finite_support_mul_racahSummand _ _ _ _ _ _ _)) |>.subset (Function.support_add _ _))
      ((finite_support_mul_racahSummand _ _ _ _ _ _ _))]
  rw [← mul_zero (-(((x₃ - y₃ + 1 : ℚ)) : ℝ)), ← finsum_sub_shift_eq_zero hH, mul_finsum]
  · refine finsum_congr fun s => ?_
    -- relation `1/(t-1)! = t/t!`
    have R : ∀ (t : ℚ) (n : ℤ), t = n → ratInvFactorial (t - 1) = (t : ℝ) * ratInvFactorial t :=
      fun t n h => ratInvFactorial_sub_one_of_eq_intCast h
    have a3 : ratInvFactorial (x₃ - s) = ((x₃ + 1 - s : ℚ) : ℝ) * ratInvFactorial (x₃ + 1 - s) := by
      rw [← R _ (n₃ + 1 - s) (by rw [h₃]; push_cast; ring)]; congr 1; ring
    have a3m : ratInvFactorial (x₃ - 1 - s) =
        ((x₃ - s : ℚ) : ℝ) * ((x₃ + 1 - s : ℚ) : ℝ) * ratInvFactorial (x₃ + 1 - s) := by
      rw [show x₃ - 1 - s = (x₃ - s) - 1 by ring, R _ (n₃ - s) (by rw [h₃]; push_cast; ring),
        a3, mul_assoc]
    have b3 : ratInvFactorial (s - y₃) = ((s - y₃ + 1 : ℚ) : ℝ) *
        ratInvFactorial (s - (y₃ - 1)) := by
      rw [show (s : ℚ) - (y₃ - 1) = s - y₃ + 1 by ring,
        ← R _ (s - k₃ + 1) (by rw [g₃]; push_cast; ring)]; congr 1; ring
    have b3p : ratInvFactorial (s - (y₃ + 1)) =
        ((s - y₃ : ℚ) : ℝ) * ((s - y₃ + 1 : ℚ) : ℝ) * ratInvFactorial (s - (y₃ - 1)) := by
      rw [show (s : ℚ) - (y₃ + 1) = (s - y₃) - 1 by ring,
        R _ (s - k₃) (by rw [g₃]; push_cast; ring), b3, mul_assoc]
    have c1 : ratInvFactorial (s - (y₁ + 1)) = ((s - y₁ : ℚ) : ℝ) * ratInvFactorial (s - y₁) := by
      rw [show (s : ℚ) - (y₁ + 1) = (s - y₁) - 1 by ring,
        R _ (s - k₁) (by rw [g₁]; push_cast; ring)]
    have c2 : ratInvFactorial (s - (y₂ + 1)) = ((s - y₂ : ℚ) : ℝ) * ratInvFactorial (s - y₂) := by
      rw [show (s : ℚ) - (y₂ + 1) = (s - y₂) - 1 by ring,
        R _ (s - k₂) (by rw [g₂]; push_cast; ring)]
    have d1 : ratInvFactorial (x₁ - ((s + 1 : ℤ) : ℚ)) = ((x₁ - s : ℚ) : ℝ) *
        ratInvFactorial (x₁ - s) := by
      rw [show x₁ - ((s + 1 : ℤ) : ℚ) = (x₁ - s) - 1 by push_cast; ring,
        R _ (n₁ - s) (by rw [h₁]; push_cast; ring)]
    have d2 : ratInvFactorial (x₂ - ((s + 1 : ℤ) : ℚ)) = ((x₂ - s : ℚ) : ℝ) *
        ratInvFactorial (x₂ - s) := by
      rw [show x₂ - ((s + 1 : ℤ) : ℚ) = (x₂ - s) - 1 by push_cast; ring,
        R _ (n₂ - s) (by rw [h₂]; push_cast; ring)]
    have d3 : ratInvFactorial (x₃ + 1 - ((s + 1 : ℤ) : ℚ)) = ratInvFactorial (x₃ - s) := by
      congr 1; push_cast; ring
    have e1 : ratInvFactorial (((s + 1 : ℤ) : ℚ) - (y₁ + 1)) = ratInvFactorial (s - y₁) := by
      congr 1; push_cast; ring
    have e2 : ratInvFactorial (((s + 1 : ℤ) : ℚ) - (y₂ + 1)) = ratInvFactorial (s - y₂) := by
      congr 1; push_cast; ring
    have e3 : ratInvFactorial (((s + 1 : ℤ) : ℚ) - y₃) = ratInvFactorial (s - (y₃ - 1)) := by
      congr 1; push_cast; ring
    simp only [hHdef]
    rw [a3m, a3, b3p, b3, c1, c2, d1, d2, d3, e1, e2, e3, a3, zpow_add_one₀ (by norm_num)]
    push_cast
    ring

/-- The symmetric Racah sum vanishes when for every `s` one factorial argument is negative. -/
private lemma symmetricRacahSum_eq_zero_of_forall_neg {x₁ x₂ x₃ y₁ y₂ y₃ : ℚ}
    (h : ∀ s : ℚ, x₁ - s < 0 ∨ x₂ - s < 0 ∨ x₃ - s < 0 ∨ s - y₁ < 0 ∨ s - y₂ < 0 ∨ s - y₃ < 0) :
    symmetricRacahSum x₁ x₂ x₃ y₁ y₂ y₃ = 0 := by
  unfold symmetricRacahSum
  convert finsum_zero with s
  rcases h s with h' | h' | h' | h' | h' | h' <;> rw [ratInvFactorial_of_neg h'] <;> ring

/-- The three-term contiguous relation of the symmetric Racah sum with `y₁ = 0` in the
simultaneous shifts of `(x₁, x₂, y₃)`. -/
private theorem symmetricRacahSum_three_term_x₁_x₂_y₃ {x₁ x₂ x₃ y₂ y₃ : ℚ} {n₁ n₂ n₃ k₂ k₃ : ℤ}
    (h₁ : x₁ = n₁) (h₂ : x₂ = n₂) (h₃ : x₃ = n₃) (g₂ : y₂ = k₂) (g₃ : y₃ = k₃) :
    ((-(x₁ + x₂ - y₂ + 1) * (x₁ ^ 2 * x₂ - x₁ ^ 2 * x₃ + x₁ * x₂ ^ 2 - x₁ * x₂ * y₂ -
        2 * x₁ * x₂ * y₃ + 2 * x₁ * x₂ + x₁ * x₃ * y₂ - x₁ * x₃ + x₁ * y₂ * y₃ - x₁ * y₃ -
        x₂ ^ 2 * x₃ + x₂ * x₃ * y₂ - x₂ * x₃ + x₂ * y₂ * y₃ - x₂ * y₃ + x₃ * y₂ - y₂ ^ 2 * y₃ +
        y₂ * y₃) : ℚ) : ℝ) * symmetricRacahSum x₁ x₂ x₃ 0 y₂ y₃ +
      (((x₁ + 1) * (x₁ - y₂ + 1) * (x₂ + 1) * (x₂ - y₂ + 1) * (x₁ + x₂ - y₂) : ℚ) : ℝ) *
        symmetricRacahSum (x₁ + 1) (x₂ + 1) x₃ 0 y₂ (y₃ + 1) +
      (((x₃ - y₃ + 1) * (x₁ + x₂ - y₂ + 2) * (x₁ + x₂ + x₃ - y₂ - y₃ + 1) : ℚ) : ℝ) *
        symmetricRacahSum (x₁ - 1) (x₂ - 1) x₃ 0 y₂ (y₃ - 1) = 0 := by
  set q₀ : ℚ :=
      -x₁^3 * x₂ + x₁^3 * y₃ - x₁^3 - 2 * x₁^2 * x₂^2 - x₁^2 * x₂ * x₃ + 2 * x₁^2 * x₂ * y₂
      + 3 * x₁^2 * x₂ * y₃ - 6 * x₁^2 * x₂ - x₁^2 * x₃ - 2 * x₁^2 * y₂ * y₃ + 2 * x₁^2 * y₂
      + 4 * x₁^2 * y₃ - 4 * x₁^2 - x₁ * x₂^3 - x₁ * x₂^2 * x₃ + 2 * x₁ * x₂^2 * y₂
      + 3 * x₁ * x₂^2 * y₃ - 6 * x₁ * x₂^2 + x₁ * x₂ * x₃ * y₂ - 4 * x₁ * x₂ * x₃ - x₁ * x₂ * y₂^2
      - 4 * x₁ * x₂ * y₂ * y₃ + 7 * x₁ * x₂ * y₂ + 10 * x₁ * x₂ * y₃ - 10 * x₁ * x₂ + x₁ * x₃ * y₂
      - 3 * x₁ * x₃ + x₁ * y₂^2 * y₃ - x₁ * y₂^2 - 6 * x₁ * y₂ * y₃ + 5 * x₁ * y₂ + 6 * x₁ * y₃
      - 5 * x₁ + x₂^3 * y₃ - x₂^3 - x₂^2 * x₃ - 2 * x₂^2 * y₂ * y₃ + 2 * x₂^2 * y₂ + 4 * x₂^2 * y₃
      - 4 * x₂^2 + x₂ * x₃ * y₂ - 3 * x₂ * x₃ + x₂ * y₂^2 * y₃ - x₂ * y₂^2 - 6 * x₂ * y₂ * y₃
      + 5 * x₂ * y₂ + 6 * x₂ * y₃ - 5 * x₂ + x₃ * y₂ - 2 * x₃ + 2 * y₂^2 * y₃ - y₂^2 - 4 * y₂ * y₃
      + 3 * y₂ + 2 * y₃ - 2 with hq₀
  set q₁ : ℚ :=
      x₁^2 * x₂ + x₁^2 * x₃ - 2 * x₁^2 * y₃ + 2 * x₁^2 + x₁ * x₂^2 + 2 * x₁ * x₂ * x₃
      - x₁ * x₂ * y₂ - 4 * x₁ * x₂ * y₃ + 4 * x₁ * x₂ - x₁ * x₃ * y₂ + 4 * x₁ * x₃
      + 3 * x₁ * y₂ * y₃ - 2 * x₁ * y₂ - 6 * x₁ * y₃ + 5 * x₁ + x₂^2 * x₃ - 2 * x₂^2 * y₃
      + 2 * x₂^2 - x₂ * x₃ * y₂ + 4 * x₂ * x₃ + 3 * x₂ * y₂ * y₃ - 2 * x₂ * y₂ - 6 * x₂ * y₃
      + 5 * x₂ - 2 * x₃ * y₂ + 4 * x₃ - y₂^2 * y₃ + 4 * y₂ * y₃ - 3 * y₂ - 4 * y₃ + 4 with hq₁
  set q₂ : ℚ :=
      -x₁ * x₃ + x₁ * y₃ - x₁ - x₂ * x₃ + x₂ * y₃ - x₂ + x₃ * y₂ - 2 * x₃ - y₂ * y₃ + y₂ + 2 * y₃
      - 2 with hq₂
  set H : ℤ → ℝ := fun s => (-1 : ℝ) ^ s *
      (ratInvFactorial ((x₁ + 1) - s) * ratInvFactorial ((x₂ + 1) - s) *
      ratInvFactorial (x₃ - s) * (ratInvFactorial (s - 1) * ratInvFactorial (s - (y₂ + 1)) *
        ratInvFactorial (s - y₃))) * ((q₀ + q₁ * s + q₂ * s ^ 2 : ℚ) : ℝ) with hHdef
  have hH : (Function.support H).Finite :=
    (finite_support_symmetricRacahSum_summand (x₁ + 1) (x₂ + 1) x₃ 1 (y₂ + 1) y₃).subset
      (Function.support_mul_subset_left _ _)
  unfold symmetricRacahSum
  rw [mul_finsum, mul_finsum, mul_finsum,
    ← finsum_add_distrib ((finite_support_mul_racahSummand _ _ _ _ _ _ _))
      ((finite_support_mul_racahSummand _ _ _ _ _ _ _)),
    ← finsum_add_distrib (((finite_support_mul_racahSummand _ _ _ _ _ _ _)).union
      ((finite_support_mul_racahSummand _ _ _ _ _ _ _)) |>.subset (Function.support_add _ _))
      ((finite_support_mul_racahSummand _ _ _ _ _ _ _)),
    ← finsum_sub_shift_eq_zero hH]
  refine finsum_congr fun s => ?_
  have R : ∀ (t : ℚ) (n : ℤ), t = n → ratInvFactorial (t - 1) = (t : ℝ) * ratInvFactorial t :=
    fun t n h => ratInvFactorial_sub_one_of_eq_intCast h
  have a1 : ratInvFactorial (x₁ - s) = ((x₁ + 1 - s : ℚ) : ℝ) * ratInvFactorial (x₁ + 1 - s) := by
    rw [← R _ (n₁ + 1 - s) (by rw [h₁]; push_cast; ring)]; congr 1; ring
  have a2 : ratInvFactorial (x₂ - s) = ((x₂ + 1 - s : ℚ) : ℝ) * ratInvFactorial (x₂ + 1 - s) := by
    rw [← R _ (n₂ + 1 - s) (by rw [h₂]; push_cast; ring)]; congr 1; ring
  have a1m : ratInvFactorial (x₁ - 1 - s) = ((x₁ - s : ℚ) : ℝ) * ratInvFactorial (x₁ - s) := by
    rw [show x₁ - 1 - s = (x₁ - s) - 1 by ring, R _ (n₁ - s) (by rw [h₁]; push_cast; ring)]
  have a2m : ratInvFactorial (x₂ - 1 - s) = ((x₂ - s : ℚ) : ℝ) * ratInvFactorial (x₂ - s) := by
    rw [show x₂ - 1 - s = (x₂ - s) - 1 by ring, R _ (n₂ - s) (by rw [h₂]; push_cast; ring)]
  have b3 : ratInvFactorial (s - y₃) = ((s - y₃ + 1 : ℚ) : ℝ) * ratInvFactorial (s - (y₃ - 1)) := by
    rw [show (s : ℚ) - (y₃ - 1) = s - y₃ + 1 by ring,
      ← R _ (s - k₃ + 1) (by rw [g₃]; push_cast; ring)]; congr 1; ring
  have b3p : ratInvFactorial (s - (y₃ + 1)) = ((s - y₃ : ℚ) : ℝ) * ratInvFactorial (s - y₃) := by
    rw [show (s : ℚ) - (y₃ + 1) = (s - y₃) - 1 by ring, R _ (s - k₃) (by rw [g₃]; push_cast; ring)]
  have c0 : ratInvFactorial ((s : ℚ) - 1) = (s : ℝ) * ratInvFactorial ((s : ℚ) - 0) := by
    rw [sub_zero, R _ s rfl]; push_cast; ring
  have c2 : ratInvFactorial (s - (y₂ + 1)) = ((s - y₂ : ℚ) : ℝ) * ratInvFactorial (s - y₂) := by
    rw [show (s : ℚ) - (y₂ + 1) = (s - y₂) - 1 by ring, R _ (s - k₂) (by rw [g₂]; push_cast; ring)]
  have d1 : ratInvFactorial (x₁ + 1 - ((s + 1 : ℤ) : ℚ)) = ratInvFactorial (x₁ - s) := by
    congr 1; push_cast; ring
  have d2 : ratInvFactorial (x₂ + 1 - ((s + 1 : ℤ) : ℚ)) = ratInvFactorial (x₂ - s) := by
    congr 1; push_cast; ring
  have d3 : ratInvFactorial (x₃ - ((s + 1 : ℤ) : ℚ)) = ((x₃ - s : ℚ) : ℝ) *
      ratInvFactorial (x₃ - s) := by
    rw [show x₃ - ((s + 1 : ℤ) : ℚ) = (x₃ - s) - 1 by push_cast; ring,
      R _ (n₃ - s) (by rw [h₃]; push_cast; ring)]
  have e0 : ratInvFactorial (((s + 1 : ℤ) : ℚ) - 1) = ratInvFactorial ((s : ℚ) - 0) := by
    congr 1; push_cast; ring
  have e2 : ratInvFactorial (((s + 1 : ℤ) : ℚ) - (y₂ + 1)) = ratInvFactorial (s - y₂) := by
    congr 1; push_cast; ring
  have e3 : ratInvFactorial (((s + 1 : ℤ) : ℚ) - y₃) = ratInvFactorial (s - (y₃ - 1)) := by
    congr 1; push_cast; ring
  simp only [hHdef]
  rw [d1, d2, d3, e0, e2, e3, c0, c2, a1m, a2m, a1, a2, b3p, b3, zpow_add_one₀ (by norm_num)]
  rw [hq₀, hq₁, hq₂]
  push_cast
  ring

set_option maxHeartbeats 800000 in
/-- DLMF 34.3.14. Stated for all arguments (stronger than DLMF). -/
@[dlmf 34.3.E14]
theorem wigner3j_recursion_m (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    ((j₁ * (j₁ + 1) - j₂ * (j₂ + 1) - j₃ * (j₃ + 1) - 2 * m₂ * m₃ : ℚ) : ℝ) *
        wigner3j j₁ j₂ j₃ m₁ m₂ m₃ =
      Real.sqrt ((j₂ - m₂) * (j₂ + m₂ + 1) * (j₃ - m₃ + 1) * (j₃ + m₃)) *
          wigner3j j₁ j₂ j₃ m₁ (m₂ + 1) (m₃ - 1) +
        Real.sqrt ((j₂ - m₂ + 1) * (j₂ + m₂) * (j₃ - m₃) * (j₃ + m₃ + 1)) *
          wigner3j j₁ j₂ j₃ m₁ (m₂ - 1) (m₃ + 1) := by
  have one : IsNatQ 1 := ⟨1, by simp⟩
  by_cases hL : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ m₃
  swap
  · have t1 : Real.sqrt ((j₂ - m₂) * (j₂ + m₂ + 1) * (j₃ - m₃ + 1) * (j₃ + m₃)) *
        wigner3j j₁ j₂ j₃ m₁ (m₂ + 1) (m₃ - 1) = 0 := by
      by_cases h1 : IsAdmissible3j j₁ j₂ j₃ m₁ (m₂ + 1) (m₃ - 1)
      · obtain ⟨t, p1, ⟨⟨u, hu⟩, ⟨w, hw⟩⟩, ⟨⟨u', hu'⟩, ⟨w', hw'⟩⟩, hs⟩ := h1
        rcases w with _ | w
        · rw [show ((j₂ : ℝ) + m₂ + 1) = 0 by
            have := congrArg (Rat.cast : ℚ → ℝ) hw; push_cast at this; linarith]
          simp
        rcases u' with _ | u'
        · rw [show ((j₃ : ℝ) - m₃ + 1) = 0 by
            have := congrArg (Rat.cast : ℚ → ℝ) hu'; push_cast at this; linarith]
          simp
        exfalso
        exact hL ⟨t, p1, ⟨⟨u + 1, by push_cast; linarith⟩, ⟨w, by push_cast at hw ⊢; linarith⟩⟩,
          ⟨⟨u', by push_cast at hu' ⊢; linarith⟩, ⟨w' + 1, by push_cast; linarith⟩⟩, by linarith⟩
      · rw [wigner3j_of_not h1, mul_zero]
    have t2 : Real.sqrt ((j₂ - m₂ + 1) * (j₂ + m₂) * (j₃ - m₃) * (j₃ + m₃ + 1)) *
        wigner3j j₁ j₂ j₃ m₁ (m₂ - 1) (m₃ + 1) = 0 := by
      by_cases h1 : IsAdmissible3j j₁ j₂ j₃ m₁ (m₂ - 1) (m₃ + 1)
      · obtain ⟨t, p1, ⟨⟨u, hu⟩, ⟨w, hw⟩⟩, ⟨⟨u', hu'⟩, ⟨w', hw'⟩⟩, hs⟩ := h1
        rcases u with _ | u
        · rw [show ((j₂ : ℝ) - m₂ + 1) = 0 by
            have := congrArg (Rat.cast : ℚ → ℝ) hu; push_cast at this; linarith]
          simp
        rcases w' with _ | w'
        · rw [show ((j₃ : ℝ) + m₃ + 1) = 0 by
            have := congrArg (Rat.cast : ℚ → ℝ) hw'; push_cast at this; linarith]
          simp
        exfalso
        exact hL ⟨t, p1, ⟨⟨u, by push_cast at hu ⊢; linarith⟩, ⟨w + 1, by push_cast; linarith⟩⟩,
          ⟨⟨u' + 1, by push_cast; linarith⟩, ⟨w', by push_cast at hw' ⊢; linarith⟩⟩, by linarith⟩
      · rw [wigner3j_of_not h1, mul_zero]
    rw [wigner3j_of_not hL, t1, t2]; ring
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩,
    ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, hm⟩ := id hL
  have hJ : j₁ + j₂ + j₃ + 1 = ((a + b + c + 1 : ℕ) : ℚ) := by push_cast; linarith
  set PL : ℝ := ratFactorial (j₁ + j₂ - j₃) * ratFactorial (j₁ - j₂ + j₃) *
      ratFactorial (-j₁ + j₂ + j₃) /
          ratFactorial (j₁ + j₂ + j₃ + 1) *
              (ratFactorial (j₁ + m₁) * ratFactorial (j₁ - m₁) * ratFactorial (j₂ + m₂) *
          ratFactorial (j₂ - m₂) * ratFactorial (j₃ + m₃) * ratFactorial (j₃ - m₃)) with hPL
  have hPL0 : 0 ≤ PL := by rw [hPL]; wigner_cast_nonneg
  set σ : ℝ := signPow (j₁ - j₂ - m₃) with hσ
  have hR : ∀ {x : ℚ} {n : ℕ}, x = n → (x : ℝ) = n := fun h => by rw [h]; simp
  have e1 : Real.sqrt ((j₂ - m₂) * (j₂ + m₂ + 1) * (j₃ - m₃ + 1) * (j₃ + m₃)) *
      wigner3j j₁ j₂ j₃ m₁ (m₂ + 1) (m₃ - 1) =
      -(σ * Real.sqrt PL) * (((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1)) *
        symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂ + 1) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + m₂ + 1) := by
    rcases p₂ with _ | u
    · rw [symmetricRacahSum_eq_zero_of_forall_neg (fun s => by
        by_contra! H; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H; push_cast at hp₂; linarith),
        show ((j₂ : ℝ) - m₂) = 0 by have := hR hp₂; push_cast at this; linarith]
      simp
    rcases q₃ with _ | v
    · rw [symmetricRacahSum_eq_zero_of_forall_neg (fun s => by
        by_contra! H; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H; push_cast at hq₃; linarith),
        show ((j₃ : ℝ) + m₃) = 0 by have := hR hq₃; push_cast at this; linarith]
      simp
    have hR1 : IsAdmissible3j j₁ j₂ j₃ m₁ (m₂ + 1) (m₃ - 1) :=
      ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩,
        ⟨⟨u, by push_cast at hp₂ ⊢; linarith⟩, ⟨q₂ + 1, by push_cast; linarith⟩⟩,
        ⟨⟨p₃ + 1, by push_cast; linarith⟩, ⟨v, by push_cast at hq₃ ⊢; linarith⟩⟩, by linarith⟩
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hR1,
      show j₁ - j₂ - (m₃ - 1) = j₁ - j₂ - m₃ + ((1 : ℤ) : ℚ) by push_cast; ring,
      signPow_add_intCast, zpow_one, ← hσ,
      show symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + (m₂ + 1)) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + (m₂ + 1)) =
        symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂ + 1) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + m₂ + 1) by congr 1 <;> ring]
    have hX : (0 : ℝ) ≤ ((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1) := by
      have h1 := hR hq₂; have h2 := hR hp₃; push_cast at h1 h2
      rw [show ((j₂ : ℝ) + m₂ + 1) = (q₂ : ℝ) + 1 by linarith,
        show ((j₃ : ℝ) - m₃ + 1) = (p₃ : ℝ) + 1 by linarith]
      positivity
    have hQ : Real.sqrt ((j₂ - m₂) * (j₂ + m₂ + 1) * (j₃ - m₃ + 1) * (j₃ + m₃)) *
        Real.sqrt (ratFactorial (j₁ + j₂ - j₃) * ratFactorial (j₁ - j₂ + j₃) *
            ratFactorial (-j₁ + j₂ + j₃) /
          ratFactorial (j₁ + j₂ + j₃ + 1) *
              (ratFactorial (j₁ + m₁) * ratFactorial (j₁ - m₁) * ratFactorial (j₂ + (m₂ + 1)) *
            ratFactorial (j₂ - (m₂ + 1)) * ratFactorial (j₃ + (m₃ - 1)) *
                ratFactorial (j₃ - (m₃ - 1)))) =
        Real.sqrt PL * (((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1)) := by
      rw [← Real.sqrt_mul' _ (by wigner_cast_nonneg), ← Real.sqrt_sq hX,
        ← Real.sqrt_mul hPL0]
      congr 1
      have h1 := hR hp₂; have h2 := hR hq₂; have h3 := hR hp₃; have h4 := hR hq₃
      push_cast at h1 h2 h3 h4
      rw [show ((j₂ : ℝ) - m₂) = (u : ℝ) + 1 by linarith,
        show ((j₂ : ℝ) + m₂ + 1) = (q₂ : ℝ) + 1 by linarith,
        show ((j₃ : ℝ) - m₃ + 1) = (p₃ : ℝ) + 1 by linarith,
        show ((j₃ : ℝ) + m₃) = (v : ℝ) + 1 by linarith, hPL,
        ratFactorial_of_eq (n := q₂ + 1) (show j₂ + (m₂ + 1) = ((q₂ + 1 : ℕ) : ℚ) by
          push_cast; linarith),
        ratFactorial_of_eq (n := u) (show j₂ - (m₂ + 1) = (u : ℚ) by push_cast at hp₂; linarith),
        ratFactorial_of_eq (n := v) (show j₃ + (m₃ - 1) = (v : ℚ) by push_cast at hq₃; linarith),
        ratFactorial_of_eq (n := p₃ + 1) (show j₃ - (m₃ - 1) = ((p₃ + 1 : ℕ) : ℚ) by
          push_cast; linarith),
        ha, hb, hc, hJ, hq₁, hp₁, hq₂, hp₂, hq₃, hp₃]
      simp only [ratFactorial_natCast, Nat.factorial_succ]
      push_cast
      field_simp
    linear_combination (-(σ * symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂ + 1) 0
      (j₂ - j₃ - m₁) (j₁ - j₃ + m₂ + 1))) * hQ
  have e2 : Real.sqrt ((j₂ - m₂ + 1) * (j₂ + m₂) * (j₃ - m₃) * (j₃ + m₃ + 1)) *
      wigner3j j₁ j₂ j₃ m₁ (m₂ - 1) (m₃ + 1) =
      -(σ * Real.sqrt PL) * (((j₂ : ℝ) - m₂ + 1) * ((j₃ : ℝ) + m₃ + 1)) *
        symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂ - 1) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + m₂ - 1) := by
    rcases q₂ with _ | u
    · rw [symmetricRacahSum_eq_zero_of_forall_neg (fun s => by
        by_contra! H; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H; push_cast at hq₂; linarith),
        show ((j₂ : ℝ) + m₂) = 0 by have := hR hq₂; push_cast at this; linarith]
      simp
    rcases p₃ with _ | v
    · rw [symmetricRacahSum_eq_zero_of_forall_neg (fun s => by
        by_contra! H; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H; push_cast at hp₃; linarith),
        show ((j₃ : ℝ) - m₃) = 0 by have := hR hp₃; push_cast at this; linarith]
      simp
    have hR1 : IsAdmissible3j j₁ j₂ j₃ m₁ (m₂ - 1) (m₃ + 1) :=
      ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩,
        ⟨⟨p₂ + 1, by push_cast; linarith⟩, ⟨u, by push_cast at hq₂ ⊢; linarith⟩⟩,
        ⟨⟨v, by push_cast at hp₃ ⊢; linarith⟩, ⟨q₃ + 1, by push_cast; linarith⟩⟩, by linarith⟩
    have hm1 : (-1 : ℝ) ^ (-1 : ℤ) = -1 := by norm_num
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hR1,
      show j₁ - j₂ - (m₃ + 1) = j₁ - j₂ - m₃ + ((-1 : ℤ) : ℚ) by push_cast; ring,
      signPow_add_intCast, hm1, ← hσ,
      show symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + (m₂ - 1)) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + (m₂ - 1)) =
        symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂ - 1) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + m₂ - 1) by congr 1 <;> ring]
    have h1 := hR hp₂; have h2 := hR hq₂; have h3 := hR hp₃; have h4 := hR hq₃
    push_cast at h1 h2 h3 h4
    have hX : (0 : ℝ) ≤ ((j₂ : ℝ) - m₂ + 1) * ((j₃ : ℝ) + m₃ + 1) := by
      rw [show ((j₂ : ℝ) - m₂ + 1) = (p₂ : ℝ) + 1 by linarith,
        show ((j₃ : ℝ) + m₃ + 1) = (q₃ : ℝ) + 1 by linarith]
      positivity
    have hQ : Real.sqrt ((j₂ - m₂ + 1) * (j₂ + m₂) * (j₃ - m₃) * (j₃ + m₃ + 1)) *
        Real.sqrt (ratFactorial (j₁ + j₂ - j₃) * ratFactorial (j₁ - j₂ + j₃) *
            ratFactorial (-j₁ + j₂ + j₃) /
          ratFactorial (j₁ + j₂ + j₃ + 1) *
              (ratFactorial (j₁ + m₁) * ratFactorial (j₁ - m₁) * ratFactorial (j₂ + (m₂ - 1)) *
            ratFactorial (j₂ - (m₂ - 1)) * ratFactorial (j₃ + (m₃ + 1)) *
                ratFactorial (j₃ - (m₃ + 1)))) =
        Real.sqrt PL * (((j₂ : ℝ) - m₂ + 1) * ((j₃ : ℝ) + m₃ + 1)) := by
      rw [← Real.sqrt_mul' _ (by wigner_cast_nonneg), ← Real.sqrt_sq hX,
        ← Real.sqrt_mul hPL0]
      congr 1
      rw [show ((j₂ : ℝ) - m₂ + 1) = (p₂ : ℝ) + 1 by linarith,
        show ((j₂ : ℝ) + m₂) = (u : ℝ) + 1 by linarith,
        show ((j₃ : ℝ) - m₃) = (v : ℝ) + 1 by linarith,
        show ((j₃ : ℝ) + m₃ + 1) = (q₃ : ℝ) + 1 by linarith, hPL,
        ratFactorial_of_eq (n := u) (show j₂ + (m₂ - 1) = (u : ℚ) by push_cast at hq₂; linarith),
        ratFactorial_of_eq (n := p₂ + 1) (show j₂ - (m₂ - 1) = ((p₂ + 1 : ℕ) : ℚ) by
          push_cast; linarith),
        ratFactorial_of_eq (n := q₃ + 1) (show j₃ + (m₃ + 1) = ((q₃ + 1 : ℕ) : ℚ) by
          push_cast; linarith),
        ratFactorial_of_eq (n := v) (show j₃ - (m₃ + 1) = (v : ℚ) by push_cast at hp₃; linarith),
        ha, hb, hc, hJ, hq₁, hp₁, hq₂, hp₂, hq₃, hp₃]
      simp only [ratFactorial_natCast, Nat.factorial_succ]
      push_cast
      field_simp
    linear_combination (-(σ * symmetricRacahSum (j₁ + j₂ - j₃) (j₁ - m₁) (j₂ + m₂ - 1) 0
      (j₂ - j₃ - m₁) (j₁ - j₃ + m₂ - 1))) * hQ
  have key := symmetricRacahSum_three_term_x₃_y₃ (x₁ := j₁ + j₂ - j₃) (x₂ := j₁ - m₁)
    (x₃ := j₂ + m₂) (y₁ := 0) (y₂ := j₂ - j₃ - m₁) (y₃ := j₁ - j₃ + m₂) (n₁ := a) (n₂ := p₁)
    (n₃ := q₂) (k₁ := 0) (k₂ := (q₂ : ℤ) - p₃) (k₃ := (a : ℤ) - p₂) (by simp [ha])
    (by simp [hp₁]) (by simp [hq₂]) (by simp) (by push_cast; linarith) (by push_cast; linarith)
  rw [e1, e2, wigner3j_eq_sqrt_mul_symmetricRacahSum hL, ← hPL, ← hσ]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  push_cast at key ⊢
  linear_combination (σ * Real.sqrt PL) * key

set_option maxHeartbeats 1600000 in
/-- DLMF 34.3.15. Stated for all arguments (stronger than DLMF). -/
@[dlmf 34.3.E15]
theorem wigner3j_recursion_j (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    ((2 * j₁ + 1) * ((j₂ * (j₂ + 1) - j₃ * (j₃ + 1)) * m₁ - j₁ * (j₁ + 1) * (m₃ - m₂)) : ℚ) *
        wigner3j j₁ j₂ j₃ m₁ m₂ m₃ =
      ((j₁ + 1 : ℚ) : ℝ) * Real.sqrt (j₁ ^ 2 - (j₂ - j₃) ^ 2) *
          Real.sqrt ((j₂ + j₃ + 1) ^ 2 - j₁ ^ 2) * Real.sqrt (j₁ ^ 2 - m₁ ^ 2) *
          wigner3j (j₁ - 1) j₂ j₃ m₁ m₂ m₃ +
        (j₁ : ℝ) * Real.sqrt ((j₁ + 1) ^ 2 - (j₂ - j₃) ^ 2) *
          Real.sqrt ((j₂ + j₃ + 1) ^ 2 - (j₁ + 1) ^ 2) * Real.sqrt ((j₁ + 1) ^ 2 - m₁ ^ 2) *
          wigner3j (j₁ + 1) j₂ j₃ m₁ m₂ m₃ := by
  have hR : ∀ {x : ℚ} {n : ℕ}, x = n → (x : ℝ) = n := fun h => by rw [h]; simp
  by_cases hL : IsAdmissible3j j₁ j₂ j₃ m₁ m₂ m₃
  swap
  · have t1 : ((j₁ + 1 : ℚ) : ℝ) * Real.sqrt (j₁ ^ 2 - (j₂ - j₃) ^ 2) *
          Real.sqrt ((j₂ + j₃ + 1) ^ 2 - j₁ ^ 2) * Real.sqrt (j₁ ^ 2 - m₁ ^ 2) *
          wigner3j (j₁ - 1) j₂ j₃ m₁ m₂ m₃ = 0 := by
      by_cases h1 : IsAdmissible3j (j₁ - 1) j₂ j₃ m₁ m₂ m₃
      · obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, ⟨⟨p, hp⟩, ⟨q, hq⟩⟩, p2, p3, hs⟩ := h1
        rcases c with _ | c
        · rw [show ((j₂ : ℝ) + j₃ + 1) ^ 2 - (j₁ : ℝ) ^ 2 = 0 by
            have := hR hc; push_cast at this
            rw [show ((j₂ : ℝ) + j₃ + 1) ^ 2 - (j₁ : ℝ) ^ 2 =
              (-(j₁ : ℝ) + j₂ + j₃ + 1) * (j₁ + j₂ + j₃ + 1) by ring]
            rw [show -(j₁ : ℝ) + j₂ + j₃ + 1 = 0 by linarith]; ring]
          simp
        exfalso
        exact hL ⟨⟨⟨a + 1, by push_cast; linarith⟩, ⟨b + 1, by push_cast; linarith⟩,
          ⟨c, by push_cast at hc ⊢; linarith⟩⟩,
          ⟨⟨p + 1, by push_cast; linarith⟩, ⟨q + 1, by push_cast; linarith⟩⟩, p2, p3, hs⟩
      · rw [wigner3j_of_not h1, mul_zero]
    have t2 : (j₁ : ℝ) * Real.sqrt ((j₁ + 1) ^ 2 - (j₂ - j₃) ^ 2) *
          Real.sqrt ((j₂ + j₃ + 1) ^ 2 - (j₁ + 1) ^ 2) * Real.sqrt ((j₁ + 1) ^ 2 - m₁ ^ 2) *
          wigner3j (j₁ + 1) j₂ j₃ m₁ m₂ m₃ = 0 := by
      by_cases h1 : IsAdmissible3j (j₁ + 1) j₂ j₃ m₁ m₂ m₃
      · obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, ⟨⟨p, hp⟩, ⟨q, hq⟩⟩, p2, p3, hs⟩ := h1
        have hA : ((j₁ : ℝ) + 1) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2 =
            ((j₁ : ℝ) + 1 + j₂ - j₃) * ((j₁ : ℝ) + 1 - j₂ + j₃) := by ring
        have hM : ((j₁ : ℝ) + 1) ^ 2 - (m₁ : ℝ) ^ 2 =
            ((j₁ : ℝ) + 1 - m₁) * ((j₁ : ℝ) + 1 + m₁) := by ring
        have h1 := hR ha; have h2 := hR hb; have h3 := hR hp; have h4 := hR hq
        push_cast at h1 h2 h3 h4
        rcases a with _ | a
        · rw [hA, show (j₁ : ℝ) + 1 + j₂ - j₃ = 0 by push_cast at h1; linarith]; simp
        rcases b with _ | b
        · rw [hA, show (j₁ : ℝ) + 1 - j₂ + j₃ = 0 by push_cast at h2; linarith]; simp
        rcases p with _ | p
        · rw [hM, show (j₁ : ℝ) + 1 - m₁ = 0 by push_cast at h3; linarith]; simp
        rcases q with _ | q
        · rw [hM, show (j₁ : ℝ) + 1 + m₁ = 0 by push_cast at h4; linarith]; simp
        exfalso
        exact hL ⟨⟨⟨a, by push_cast at ha; linarith⟩, ⟨b, by push_cast at hb; linarith⟩,
          ⟨c + 1, by push_cast; linarith⟩⟩,
          ⟨⟨p, by push_cast at hp; linarith⟩, ⟨q, by push_cast at hq; linarith⟩⟩, p2, p3, hs⟩
      · rw [wigner3j_of_not h1, mul_zero]
    rw [wigner3j_of_not hL, t1, t2]; ring
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, ⟨⟨p₁, hp₁⟩, ⟨q₁, hq₁⟩⟩, ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩,
    ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, hm⟩ := id hL
  set PL : ℝ := ratFactorial (j₁ + j₂ - j₃) * ratFactorial (j₁ - j₂ + j₃) *
      ratFactorial (-j₁ + j₂ + j₃) /
          ratFactorial (j₁ + j₂ + j₃ + 1) *
              (ratFactorial (j₁ + m₁) * ratFactorial (j₁ - m₁) * ratFactorial (j₂ + m₂) *
          ratFactorial (j₂ - m₂) * ratFactorial (j₃ + m₃) * ratFactorial (j₃ - m₃)) with hPL
  have hPL0 : 0 ≤ PL := by rw [hPL]; wigner_cast_nonneg
  set σ : ℝ := signPow (j₁ - j₂ - m₃) with hσ
  have hm1 : (-1 : ℝ) ^ (-1 : ℤ) = -1 := by norm_num
  have r1 := hR ha; have r2 := hR hb; have r3 := hR hc; have r4 := hR hp₁; have r5 := hR hq₁
  push_cast at r1 r2 r3 r4 r5
  have eM : ((j₁ + 1 : ℚ) : ℝ) * Real.sqrt (j₁ ^ 2 - (j₂ - j₃) ^ 2) *
      Real.sqrt ((j₂ + j₃ + 1) ^ 2 - j₁ ^ 2) * Real.sqrt (j₁ ^ 2 - m₁ ^ 2) *
      wigner3j (j₁ - 1) j₂ j₃ m₁ m₂ m₃ =
      -(σ * Real.sqrt PL) * (((j₁ : ℝ) + 1) * ((-(j₁ : ℝ) + j₂ + j₃ + 1) *
        ((j₁ : ℝ) + j₂ + j₃ + 1))) *
        symmetricRacahSum (j₁ + j₂ - j₃ - 1) (j₁ - m₁ - 1) (j₂ + m₂) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + m₂ - 1) := by
    have hA : (j₁ : ℝ) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2 =
        ((j₁ : ℝ) + j₂ - j₃) * ((j₁ : ℝ) - j₂ + j₃) := by ring
    have hM : (j₁ : ℝ) ^ 2 - (m₁ : ℝ) ^ 2 = ((j₁ : ℝ) - m₁) * ((j₁ : ℝ) + m₁) := by ring
    rcases a with _ | a
    · rw [hA, show (j₁ : ℝ) + j₂ - j₃ = 0 by push_cast at r1; linarith,
        symmetricRacahSum_eq_zero_of_forall_neg (fun s => by
          by_contra! H; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H; push_cast at ha hq₂ hp₃; linarith)]
      simp
    rcases b with _ | b
    · rw [hA, show (j₁ : ℝ) - j₂ + j₃ = 0 by push_cast at r2; linarith,
        symmetricRacahSum_eq_zero_of_forall_neg (fun s => by
          by_contra! H; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H; push_cast at hb hq₂ hp₃; linarith)]
      simp
    rcases p₁ with _ | p
    · rw [hM, show (j₁ : ℝ) - m₁ = 0 by push_cast at r4; linarith,
        symmetricRacahSum_eq_zero_of_forall_neg (fun s => by
          by_contra! H; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H; push_cast at hp₁ hq₂ hp₃; linarith)]
      simp
    rcases q₁ with _ | q
    · rw [hM, show (j₁ : ℝ) + m₁ = 0 by push_cast at r5; linarith,
        symmetricRacahSum_eq_zero_of_forall_neg (fun s => by
          by_contra! H; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H; push_cast at hq₁ hq₂ hp₃; linarith)]
      simp
    push_cast at r1 r2 r4 r5
    have hR1 : IsAdmissible3j (j₁ - 1) j₂ j₃ m₁ m₂ m₃ :=
      ⟨⟨⟨a, by push_cast at ha; linarith⟩, ⟨b, by push_cast at hb; linarith⟩,
        ⟨c + 1, by push_cast; linarith⟩⟩,
        ⟨⟨p, by push_cast at hp₁; linarith⟩, ⟨q, by push_cast at hq₁; linarith⟩⟩,
        ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩, ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, hm⟩
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hR1,
      show j₁ - 1 - j₂ - m₃ = j₁ - j₂ - m₃ + ((-1 : ℤ) : ℚ) by push_cast; ring,
      signPow_add_intCast, hm1, ← hσ,
      show symmetricRacahSum (j₁ - 1 + j₂ - j₃) (j₁ - 1 - m₁) (j₂ + m₂) 0 (j₂ - j₃ - m₁)
          (j₁ - 1 - j₃ + m₂) =
        symmetricRacahSum (j₁ + j₂ - j₃ - 1) (j₁ - m₁ - 1) (j₂ + m₂) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + m₂ - 1) by congr 1 <;> ring,
      hA, hM, show ((j₂ : ℝ) + j₃ + 1) ^ 2 - (j₁ : ℝ) ^ 2 =
        (-(j₁ : ℝ) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 1) by ring]
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have hX : (0 : ℝ) ≤ (-(j₁ : ℝ) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hQ : Real.sqrt (((j₁ : ℝ) + j₂ - j₃) * ((j₁ : ℝ) - j₂ + j₃)) *
        Real.sqrt ((-(j₁ : ℝ) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 1)) *
        Real.sqrt (((j₁ : ℝ) - m₁) * ((j₁ : ℝ) + m₁)) *
        Real.sqrt (ratFactorial (j₁ - 1 + j₂ - j₃) * ratFactorial (j₁ - 1 - j₂ + j₃) *
          ratFactorial (-(j₁ - 1) + j₂ + j₃) / ratFactorial (j₁ - 1 + j₂ + j₃ + 1) *
          (ratFactorial (j₁ - 1 + m₁) * ratFactorial (j₁ - 1 - m₁) * ratFactorial (j₂ + m₂) *
            ratFactorial (j₂ - m₂) * ratFactorial (j₃ + m₃) * ratFactorial (j₃ - m₃))) =
        Real.sqrt PL * ((-(j₁ : ℝ) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 1)) := by
      rw [show Real.sqrt PL * ((-(j₁ : ℝ) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 1)) =
          Real.sqrt (PL * ((-(j₁ : ℝ) + j₂ + j₃ + 1) * ((j₁ : ℝ) + j₂ + j₃ + 1)) ^ 2) by
        rw [Real.sqrt_mul hPL0, Real.sqrt_sq hX]]
      rw [show (j₁ : ℝ) + j₂ - j₃ = (a : ℝ) + 1 by linarith,
        show (j₁ : ℝ) - j₂ + j₃ = (b : ℝ) + 1 by linarith,
        show -(j₁ : ℝ) + j₂ + j₃ + 1 = (c : ℝ) + 1 by linarith,
        show (j₁ : ℝ) + j₂ + j₃ + 1 = (a : ℝ) + b + c + 3 by linarith,
        show (j₁ : ℝ) - m₁ = (p : ℝ) + 1 by linarith,
        show (j₁ : ℝ) + m₁ = (q : ℝ) + 1 by linarith,
        ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((a : ℝ) + 1) * ((b : ℝ) + 1)),
        ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((a : ℝ) + 1) * ((b : ℝ) + 1) *
          (((c : ℝ) + 1) * ((a : ℝ) + b + c + 3))),
        ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((a : ℝ) + 1) * ((b : ℝ) + 1) *
          (((c : ℝ) + 1) * ((a : ℝ) + b + c + 3)) * (((p : ℝ) + 1) * ((q : ℝ) + 1)))]
      congr 1
      rw [hPL,
        ratFactorial_of_eq (n := a) (show j₁ - 1 + j₂ - j₃ = (a : ℚ) by push_cast at ha; linarith),
        ratFactorial_of_eq (n := b) (show j₁ - 1 - j₂ + j₃ = (b : ℚ) by push_cast at hb; linarith),
        ratFactorial_of_eq (n := c + 1) (show -(j₁ - 1) + j₂ + j₃ = ((c + 1 : ℕ) : ℚ) by
          push_cast; linarith),
        ratFactorial_of_eq (n := a + b + c + 2)
            (show j₁ - 1 + j₂ + j₃ + 1 = ((a + b + c + 2 : ℕ) : ℚ) by
          push_cast at ha hb ⊢; linarith),
        ratFactorial_of_eq (n := q) (show j₁ - 1 + m₁ = (q : ℚ) by push_cast at hq₁; linarith),
        ratFactorial_of_eq (n := p) (show j₁ - 1 - m₁ = (p : ℚ) by push_cast at hp₁; linarith),
        ratFactorial_of_eq (n := a + b + c + 3)
            (show j₁ + j₂ + j₃ + 1 = ((a + b + c + 3 : ℕ) : ℚ) by
          push_cast at ha hb ⊢; linarith),
        ha, hb, hc, hq₁, hp₁]
      simp only [ratFactorial_natCast, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    rw [show ((j₁ + 1 : ℚ) : ℝ) = (j₁ : ℝ) + 1 by push_cast; ring]
    linear_combination (-(σ * ((j₁ : ℝ) + 1) *
      symmetricRacahSum (j₁ + j₂ - j₃ - 1) (j₁ - m₁ - 1) (j₂ + m₂) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + m₂ - 1))) * hQ
  have eP : (j₁ : ℝ) * Real.sqrt ((j₁ + 1) ^ 2 - (j₂ - j₃) ^ 2) *
      Real.sqrt ((j₂ + j₃ + 1) ^ 2 - (j₁ + 1) ^ 2) * Real.sqrt ((j₁ + 1) ^ 2 - m₁ ^ 2) *
      wigner3j (j₁ + 1) j₂ j₃ m₁ m₂ m₃ =
      -(σ * Real.sqrt PL) * ((j₁ : ℝ) * (((j₁ : ℝ) + j₂ - j₃ + 1) * ((j₁ : ℝ) - j₂ + j₃ + 1) *
        (((j₁ : ℝ) - m₁ + 1) * ((j₁ : ℝ) + m₁ + 1)))) *
        symmetricRacahSum (j₁ + j₂ - j₃ + 1) (j₁ - m₁ + 1) (j₂ + m₂) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + m₂ + 1) := by
    have hA : ((j₁ : ℝ) + 1) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2 =
        ((j₁ : ℝ) + j₂ - j₃ + 1) * ((j₁ : ℝ) - j₂ + j₃ + 1) := by ring
    have hC : ((j₂ : ℝ) + j₃ + 1) ^ 2 - ((j₁ : ℝ) + 1) ^ 2 =
        (-(j₁ : ℝ) + j₂ + j₃) * ((j₁ : ℝ) + j₂ + j₃ + 2) := by ring
    have hM : ((j₁ : ℝ) + 1) ^ 2 - (m₁ : ℝ) ^ 2 =
        ((j₁ : ℝ) - m₁ + 1) * ((j₁ : ℝ) + m₁ + 1) := by ring
    rcases c with _ | c
    · rw [hC, show -(j₁ : ℝ) + j₂ + j₃ = 0 by push_cast at r3; linarith,
        symmetricRacahSum_eq_zero_of_forall_neg (fun s => by
          by_contra! H; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H; push_cast at hc hq₂ hp₂; linarith)]
      simp
    push_cast at r3
    have hR1 : IsAdmissible3j (j₁ + 1) j₂ j₃ m₁ m₂ m₃ :=
      ⟨⟨⟨a + 1, by push_cast; linarith⟩, ⟨b + 1, by push_cast; linarith⟩,
        ⟨c, by push_cast at hc; linarith⟩⟩,
        ⟨⟨p₁ + 1, by push_cast; linarith⟩, ⟨q₁ + 1, by push_cast; linarith⟩⟩,
        ⟨⟨p₂, hp₂⟩, ⟨q₂, hq₂⟩⟩, ⟨⟨p₃, hp₃⟩, ⟨q₃, hq₃⟩⟩, hm⟩
    rw [wigner3j_eq_sqrt_mul_symmetricRacahSum hR1,
      show j₁ + 1 - j₂ - m₃ = j₁ - j₂ - m₃ + ((1 : ℤ) : ℚ) by push_cast; ring,
      signPow_add_intCast, zpow_one, ← hσ,
      show symmetricRacahSum (j₁ + 1 + j₂ - j₃) (j₁ + 1 - m₁) (j₂ + m₂) 0 (j₂ - j₃ - m₁)
          (j₁ + 1 - j₃ + m₂) =
        symmetricRacahSum (j₁ + j₂ - j₃ + 1) (j₁ - m₁ + 1) (j₂ + m₂) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + m₂ + 1) by congr 1 <;> ring, hA, hC, hM]
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have hp0 : (0 : ℝ) ≤ p₁ := Nat.cast_nonneg p₁
    have hq0 : (0 : ℝ) ≤ q₁ := Nat.cast_nonneg q₁
    have hX : (0 : ℝ) ≤ ((j₁ : ℝ) + j₂ - j₃ + 1) * ((j₁ : ℝ) - j₂ + j₃ + 1) *
        (((j₁ : ℝ) - m₁ + 1) * ((j₁ : ℝ) + m₁ + 1)) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith))
        (mul_nonneg (by linarith) (by linarith))
    have hQ : Real.sqrt (((j₁ : ℝ) + j₂ - j₃ + 1) * ((j₁ : ℝ) - j₂ + j₃ + 1)) *
        Real.sqrt ((-(j₁ : ℝ) + j₂ + j₃) * ((j₁ : ℝ) + j₂ + j₃ + 2)) *
        Real.sqrt (((j₁ : ℝ) - m₁ + 1) * ((j₁ : ℝ) + m₁ + 1)) *
        Real.sqrt (ratFactorial (j₁ + 1 + j₂ - j₃) * ratFactorial (j₁ + 1 - j₂ + j₃) *
          ratFactorial (-(j₁ + 1) + j₂ + j₃) / ratFactorial (j₁ + 1 + j₂ + j₃ + 1) *
          (ratFactorial (j₁ + 1 + m₁) * ratFactorial (j₁ + 1 - m₁) * ratFactorial (j₂ + m₂) *
            ratFactorial (j₂ - m₂) * ratFactorial (j₃ + m₃) * ratFactorial (j₃ - m₃))) =
        Real.sqrt PL * (((j₁ : ℝ) + j₂ - j₃ + 1) * ((j₁ : ℝ) - j₂ + j₃ + 1) *
          (((j₁ : ℝ) - m₁ + 1) * ((j₁ : ℝ) + m₁ + 1))) := by
      rw [show Real.sqrt PL * (((j₁ : ℝ) + j₂ - j₃ + 1) * ((j₁ : ℝ) - j₂ + j₃ + 1) *
          (((j₁ : ℝ) - m₁ + 1) * ((j₁ : ℝ) + m₁ + 1))) =
          Real.sqrt (PL * (((j₁ : ℝ) + j₂ - j₃ + 1) * ((j₁ : ℝ) - j₂ + j₃ + 1) *
            (((j₁ : ℝ) - m₁ + 1) * ((j₁ : ℝ) + m₁ + 1))) ^ 2) by
        rw [Real.sqrt_mul hPL0, Real.sqrt_sq hX]]
      rw [show (j₁ : ℝ) + j₂ - j₃ + 1 = (a : ℝ) + 1 by linarith,
        show (j₁ : ℝ) - j₂ + j₃ + 1 = (b : ℝ) + 1 by linarith,
        show -(j₁ : ℝ) + j₂ + j₃ = (c : ℝ) + 1 by linarith,
        show (j₁ : ℝ) + j₂ + j₃ + 2 = (a : ℝ) + b + c + 3 by linarith,
        show (j₁ : ℝ) - m₁ + 1 = (p₁ : ℝ) + 1 by linarith,
        show (j₁ : ℝ) + m₁ + 1 = (q₁ : ℝ) + 1 by linarith,
        ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((a : ℝ) + 1) * ((b : ℝ) + 1)),
        ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((a : ℝ) + 1) * ((b : ℝ) + 1) *
          (((c : ℝ) + 1) * ((a : ℝ) + b + c + 3))),
        ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((a : ℝ) + 1) * ((b : ℝ) + 1) *
          (((c : ℝ) + 1) * ((a : ℝ) + b + c + 3)) * (((p₁ : ℝ) + 1) * ((q₁ : ℝ) + 1)))]
      congr 1
      rw [hPL,
        ratFactorial_of_eq (n := a + 1) (show j₁ + 1 + j₂ - j₃ = ((a + 1 : ℕ) : ℚ) by
          push_cast; linarith),
        ratFactorial_of_eq (n := b + 1) (show j₁ + 1 - j₂ + j₃ = ((b + 1 : ℕ) : ℚ) by
          push_cast; linarith),
        ratFactorial_of_eq (n := c)
            (show -(j₁ + 1) + j₂ + j₃ = (c : ℚ) by push_cast at hc; linarith),
        ratFactorial_of_eq (n := a + b + c + 3) (show j₁ + 1 + j₂ + j₃ + 1 =
          ((a + b + c + 3 : ℕ) : ℚ) by push_cast at hc ⊢; linarith),
        ratFactorial_of_eq (n := q₁ + 1)
            (show j₁ + 1 + m₁ = ((q₁ + 1 : ℕ) : ℚ) by push_cast; linarith),
        ratFactorial_of_eq (n := p₁ + 1)
            (show j₁ + 1 - m₁ = ((p₁ + 1 : ℕ) : ℚ) by push_cast; linarith),
        ratFactorial_of_eq (n := a + b + c + 2)
            (show j₁ + j₂ + j₃ + 1 = ((a + b + c + 2 : ℕ) : ℚ) by
          push_cast at hc ⊢; linarith),
        ha, hb, hc, hq₁, hp₁]
      simp only [ratFactorial_natCast, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    linear_combination (-(σ * (j₁ : ℝ) *
      symmetricRacahSum (j₁ + j₂ - j₃ + 1) (j₁ - m₁ + 1) (j₂ + m₂) 0 (j₂ - j₃ - m₁)
          (j₁ - j₃ + m₂ + 1))) * hQ
  have key := symmetricRacahSum_three_term_x₁_x₂_y₃ (x₁ := j₁ + j₂ - j₃) (x₂ := j₁ - m₁)
    (x₃ := j₂ + m₂) (y₂ := j₂ - j₃ - m₁) (y₃ := j₁ - j₃ + m₂) (n₁ := a) (n₂ := p₁)
    (n₃ := q₂) (k₂ := (q₂ : ℤ) - p₃) (k₃ := (a : ℤ) - p₂) (by simp [ha])
    (by simp [hp₁]) (by simp [hq₂]) (by push_cast; linarith) (by push_cast; linarith)
  rw [eM, eP, wigner3j_eq_sqrt_mul_symmetricRacahSum hL, ← hPL, ← hσ]
  obtain rfl : m₃ = -m₁ - m₂ := by linarith
  push_cast at key ⊢
  linear_combination (σ * Real.sqrt PL / 2) * key

end DLMF.WignerSymbols
