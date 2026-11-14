/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Hyperbolic.Integrals
import Mathlib.Tactic

/-!
# Coefficient evidence for the DLMF 4.39.2 transcription

One quotient in the uncorrected continued-fraction numerator is evaluated in `ℂ` instead of
`ℕ`. These exact coefficient identities distinguish the two expressions. The finite
convergent calculation is coefficient evidence, not a nonconvergence theorem for the
infinite fraction. The corrected production theorem is
`DLMF.Elementary.arcsinh_continued_fraction`.
-/

public noncomputable section

open Complex
namespace DLMFStatementCorrections

-- At index two, Lean elaborates the second quotient in ℂ in the uncorrected statement.
/-- The transcribed second numerator coefficient evaluates to three. -/
lemma arcsinh_coefficient_two_as_written :
    (((2 * ((2 + 1) / 2) - 1 : ℕ) : ℂ) * (2 * ((2 + 1) / 2) : ℂ)) = 3 := by
  norm_num
/-- Natural-number division gives the intended coefficient two. -/
lemma arcsinh_coefficient_two_with_nat_division :
    (((2 * ((2 + 1) / 2) - 1 : ℕ) : ℂ) * ((2 * ((2 + 1) / 2) : ℕ) : ℂ)) = 2 := by
  norm_num

-- The erroneous third finite convergent has z ^ 5 coefficient 26 / 45.
-- Its remainder after this polynomial begins at z ^ 7, as this exact identity shows.
/-- The erroneous third convergent has the stated exact polynomial remainder. -/
lemma arcsinh_third_convergent_remainder (z : ℂ) (hz : 1 + (13 / 15 : ℂ) * z ^ 2 ≠ 0) :
    z * (1 + z ^ 2 / 5) / (1 + (13 / 15 : ℂ) * z ^ 2) -
        (z - (2 / 3 : ℂ) * z ^ 3 + (26 / 45 : ℂ) * z ^ 5) =
      -(338 / 675 : ℂ) * z ^ 7 / (1 + (13 / 15 : ℂ) * z ^ 2) := by
  have hz' : (15 : ℂ) + 13 * z ^ 2 ≠ 0 := by
    have he : (15 : ℂ) + 13 * z ^ 2 = 15 * (1 + (13 / 15 : ℂ) * z ^ 2) := by ring
    rw [he]
    exact mul_ne_zero (by norm_num) hz
  have hz'' : (15 : ℂ) + z ^ 2*13 ≠ 0 := by
    rw [mul_comm (z ^ 2) 13]
    exact hz'
  field_simp [hz', hz'']
  ring

-- The correct arcsinh quotient's z ^ 5 Gauss coefficient is 8/15 = 24 / 45.
/-- The matching Gauss series has fifth-order coefficient `24 / 45`. -/
lemma arcsinh_gauss_coefficient_two : DLMF.Hypergeometric.pochhammer (1 : ℂ) 2 *
      DLMF.Hypergeometric.pochhammer (1 : ℂ) 2 /
      (DLMF.Hypergeometric.pochhammer (3 / 2 : ℂ) 2 * (2 : ℂ)) = (24 / 45 : ℂ) := by
  norm_num [DLMF.Hypergeometric.pochhammer_succ, DLMF.Hypergeometric.pochhammer_zero]

/-- The two fifth-order coefficients are distinct. -/
lemma arcsinh_coefficients_ne : (26 / 45 : ℂ) ≠ 24 / 45 := by norm_num

#print axioms arcsinh_coefficient_two_as_written
#print axioms arcsinh_coefficient_two_with_nat_division
#print axioms arcsinh_third_convergent_remainder
#print axioms arcsinh_gauss_coefficient_two
#print axioms arcsinh_coefficients_ne
end DLMFStatementCorrections

#print axioms DLMF.Elementary.arcsinh_continued_fraction
