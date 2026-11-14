/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.AskeyScheme
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Wilson and continuous Hahn squared norms

Andrews, Askey and Roy, *Special Functions*, Theorem 3.8.2 and §6.10.
The Wilson constant polynomial gives Wilson's beta integral. The degree-zero
continuous Hahn norm cancels the removable factor `(A−1)Γ(A−1)` first.
-/

@[expose] public section

open MeasureTheory DLMF.Hypergeometric

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- Wilson's full orthogonality norm on the positive real axis.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.8.2
(synopsis AAR-3.6.1–3.8.2); degree zero is Theorem 3.6.2. -/
theorem wilson_integral_mul {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (m n : ℕ) :
    (∫ x : ℝ in Set.Ioi 0,
      wilson a b c d m ((x : ℂ) ^ 2) * wilson a b c d n ((x : ℂ) ^ 2) *
        (‖Complex.Gamma (a + Complex.I * x) * Complex.Gamma (b + Complex.I * x) *
          Complex.Gamma (c + Complex.I * x) * Complex.Gamma (d + Complex.I * x) /
          Complex.Gamma (2 * Complex.I * x)‖ ^ 2 : ℝ)) =
      if m = n then
        2 * Real.pi * n.factorial * pochhammer (n + (a : ℂ) + b + c + d - 1) n *
          Complex.Gamma (n + (a : ℂ) + b) * Complex.Gamma (n + (a : ℂ) + c) *
          Complex.Gamma (n + (a : ℂ) + d) * Complex.Gamma (n + (b : ℂ) + c) *
          Complex.Gamma (n + (b : ℂ) + d) * Complex.Gamma (n + (c : ℂ) + d) /
          Complex.Gamma ((a : ℂ) + b + c + d + 2 * n)
      else 0 := by
  sorry

/-- Wilson polynomials are invariant under every parameter permutation on the finite
regular domain. Andrews–Askey–Roy, *Special Functions*, Definition 3.8.1
(synopsis AAR-3.6.1–3.8.2). -/
theorem wilson_parameter_permutation (u : Fin 4 → ℂ) (σ : Equiv.Perm (Fin 4))
    (n : ℕ) (x : ℂ)
    (hreg : ∀ i j : Fin 4, i ≠ j → ∀ k ≤ n, pochhammer (u i + u j) k ≠ 0) :
    wilson (u (σ 0)) (u (σ 1)) (u (σ 2)) (u (σ 3)) n x =
      wilson (u 0) (u 1) (u 2) (u 3) n x := by
  sorry

/-- The full continuous Hahn orthogonality norm, with its degree-zero Gamma quotient
canceled at the exceptional value A=1. Andrews–Askey–Roy, *Special Functions*,
§6.10 (synopsis AAR-6.10–6.11). -/
theorem continuousHahn_integral_mul {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (m n : ℕ) :
    (∫ x : ℝ, continuousHahn a b (star a) (star b) m x *
      continuousHahn a b (star a) (star b) n x * continuousHahnWeight a b x) =
      if m = n then
        2 * Real.pi * Complex.Gamma (n + a + star a) *
          Complex.Gamma (n + a + star b) * Complex.Gamma (n + b + star a) *
          Complex.Gamma (n + b + star b) /
          (if n = 0 then Complex.Gamma (a + b + star a + star b) else
            (2 * n + a + b + star a + star b - 1) * n.factorial *
              Complex.Gamma (n + a + b + star a + star b - 1))
      else 0 := by
  sorry

end DLMF.OrthogonalPolynomials
