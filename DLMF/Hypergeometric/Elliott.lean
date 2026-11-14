/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic

/-!
# Elliott's generalization of Legendre's relation

The product identity in Andrews, Askey and Roy, *Special Functions*, Theorem 3.2.8.
The parameter shifts follow the printed theorem on p. 138.
-/

@[expose] public section

namespace DLMF.Hypergeometric

/-- Elliott's relation on the real interval between the two regular singularities.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.2.8, p. 138
(synopsis AAR-3.2.3–3.2.11). The two lower parameters are regular; the inverse
Gamma factors on the right include their zeros. -/
theorem elliott_relation (a b c : ℂ) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hu : ∀ k : ℕ, a + b + 1 ≠ -(k : ℂ))
    (hv : ∀ k : ℕ, b + c + 1 ≠ -(k : ℂ)) :
    ordinaryHypergeometric (a + 1 / 2) (-1 / 2 - c) (a + b + 1) (x : ℂ) *
        ordinaryHypergeometric (1 / 2 - a) (c + 1 / 2) (b + c + 1) (1 - (x : ℂ)) +
      ordinaryHypergeometric (a + 1 / 2) (1 / 2 - c) (a + b + 1) (x : ℂ) *
        ordinaryHypergeometric (-(a + 1 / 2)) (c + 1 / 2) (b + c + 1) (1 - (x : ℂ)) -
      ordinaryHypergeometric (a + 1 / 2) (1 / 2 - c) (a + b + 1) (x : ℂ) *
        ordinaryHypergeometric (1 / 2 - a) (c + 1 / 2) (b + c + 1) (1 - (x : ℂ)) =
      Complex.Gamma (a + b + 1) * Complex.Gamma (b + c + 1) /
        (Complex.Gamma (a + b + c + 3 / 2) * Complex.Gamma (b + 1 / 2)) := by
  sorry

end DLMF.Hypergeometric
