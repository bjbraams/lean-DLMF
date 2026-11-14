/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.NineJ

/-!
# A doubly stretched nine-j evaluation

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018),
§7.3, (7.63)–(7.72), synopsis RL-7.10. The closed value is stated
for the canonical nine-j function, independently of a proposed triple-sum phase.
-/

@[expose] public noncomputable section
namespace DLMF.WignerSymbols.StretchedNineJ

/-- The factorial triangle factor in the stretched formulas,
Rao–Lakshminarayanan (7.44) and (7.72), synopsis RL-7.10. -/
def triangleFactor (u v w : ℚ) : ℝ :=
  Real.sqrt (ratFactorial (u - v + w) * ratFactorial (u + v - w) *
    ratFactorial (u + v + w + 1) / ratFactorial (-u + v + w))

/-- The defining factorial formula for the triangle factor, RL-7.10. -/
theorem triangleFactor_def (u v w : ℚ) : triangleFactor u v w =
    Real.sqrt (ratFactorial (u - v + w) * ratFactorial (u + v - w) *
      ratFactorial (u + v + w + 1) / ratFactorial (-u + v + w)) := rfl

/-- The type-III doubly stretched nine-j symbol has a single-term value,
Rao–Lakshminarayanan (7.63)–(7.72), synopsis RL-7.10.
All factorial arguments are nonnegative integers on these four triangle domains. -/
theorem wigner9j_type_three (a b c d e f i : ℚ)
    (h₁ : IsTriad a b c) (h₂ : IsTriad d e f)
    (h₃ : IsTriad (a + d + i) b e) (h₄ : IsTriad i c f) :
    wigner9j (a + d) (a + d + i) i a b c d e f =
      signPow (d - e + f) * triangleFactor (a + d + i) b e /
        (triangleFactor a b c * triangleFactor d e f * triangleFactor i c f) *
      Real.sqrt (ratFactorial (2 * a) * ratFactorial (2 * d) * ratFactorial (2 * i) /
        ((2 * a + 2 * d + 1 : ℚ) * ratFactorial (2 * a + 2 * d + 2 * i + 1))) := by
  sorry

end DLMF.WignerSymbols.StretchedNineJ
