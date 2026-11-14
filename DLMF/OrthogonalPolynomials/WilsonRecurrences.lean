/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.AskeyScheme

/-!
# Wilson and continuous Hahn three-term and imaginary-step equations

Andrews, Askey and Roy, *Special Functions*, §§3.8 and 6.10, pp. 155–160,
330–338. Cleared forms retain the identities at removable recurrence singularities.
Finite lower-parameter regularity is imposed only through the degrees occurring.
-/

@[expose] public section

open DLMF.Hypergeometric

namespace DLMF.OrthogonalPolynomials

/-- The Wilson three-term recurrence with its coefficient denominators cleared.
Andrews–Askey–Roy, *Special Functions*, §3.8, pp. 155–160
(synopses AAR-3.6.1–3.8.2 and AAR-6.10–6.11). The normalized `R` is the
terminating hypergeometric polynomial, and no restriction on the coefficient sum is added. -/
theorem wilson_normalized_recurrence (a b c d x : ℂ) (n : ℕ)
    (hregular : ∀ k ≤ n + 2,
      pochhammer (a + b) k ≠ 0 ∧ pochhammer (a + c) k ≠ 0 ∧ pochhammer (a + d) k ≠ 0) :
    let R := fun m : ℕ => wilson a b c d m (x ^ 2) /
      (pochhammer (a + b) m * pochhammer (a + c) m * pochhammer (a + d) m)
    let k : ℂ := n + 1
    let A := a + b + c + d
    let da := (2 * k + A - 1) * (2 * k + A)
    let dc := (2 * k + A - 2) * (2 * k + A - 1)
    (-(a ^ 2 + x ^ 2) * R (n + 1) * da * dc) =
      (k + A - 1) * (k + a + b) * (k + a + c) * (k + a + d) * dc *
          (R (n + 2) - R (n + 1)) +
        k * (k + b + c - 1) * (k + b + d - 1) * (k + c + d - 1) * da *
          (R n - R (n + 1)) := by
  sorry

/-- The continuous dual Hahn three-term recurrence in normalized form.
Andrews–Askey–Roy, *Special Functions*, §6.10, pp. 330–338
(synopsis AAR-6.10–6.11). -/
theorem continuousDualHahn_normalized_recurrence (a b c x : ℂ) (n : ℕ)
    (hregular : ∀ k ≤ n + 2, pochhammer (a + b) k ≠ 0 ∧ pochhammer (a + c) k ≠ 0) :
    let R := fun m : ℕ => continuousDualHahn a b c m (x ^ 2) /
      (pochhammer (a + b) m * pochhammer (a + c) m)
    let k : ℂ := n + 1
    (-(a ^ 2 + x ^ 2) * R (n + 1)) =
      (k + a + b) * (k + a + c) * (R (n + 2) - R (n + 1)) +
        k * (k + b + c - 1) * (R n - R (n + 1)) := by
  sorry

/-- The continuous Hahn recurrence with all coefficient denominators cleared.
Andrews–Askey–Roy, *Special Functions*, §6.10, pp. 330–338
(synopsis AAR-6.10–6.11). The negative sign in the forward coefficient matches
the source's `i^n/n!` normalization. -/
theorem continuousHahn_normalized_recurrence (a b c d x : ℂ) (n : ℕ)
    (hregular : ∀ k ≤ n + 2, pochhammer (a + c) k ≠ 0 ∧ pochhammer (a + d) k ≠ 0) :
    let R := fun m : ℕ => m.factorial * continuousHahn a b c d m x /
      (Complex.I ^ m * pochhammer (a + c) m * pochhammer (a + d) m)
    let k : ℂ := n + 1
    let A := a + b + c + d
    let da := (2 * k + A - 1) * (2 * k + A)
    let dc := (2 * k + A - 2) * (2 * k + A - 1)
    (a + Complex.I * x) * R (n + 1) * da * dc =
      -(k + A - 1) * (k + a + c) * (k + a + d) * dc * (R (n + 2) - R (n + 1)) +
        k * (k + b + c - 1) * (k + b + d - 1) * da * (R n - R (n + 1)) := by
  sorry

/-- The Wilson imaginary-step eigen-equation, cleared at `x = 0, ±i/2`.
Andrews–Askey–Roy, *Special Functions*, §6.10, pp. 330–338
(synopsis AAR-6.10–6.11). These exceptional arguments require no arbitrary square root. -/
theorem wilson_imaginary_step_equation (a b c d : ℂ) (n : ℕ)
    (hregular : ∀ k ≤ n,
      pochhammer (a + b) k ≠ 0 ∧ pochhammer (a + c) k ≠ 0 ∧ pochhammer (a + d) k ≠ 0)
    (x : ℂ) :
    let y := fun z : ℂ => wilson a b c d n (z ^ 2)
    let t := 2 * Complex.I * x
    n * (n + a + b + c + d - 1) * y x * t * (t - 1) * (t + 1) =
      (a - Complex.I * x) * (b - Complex.I * x) *
          (c - Complex.I * x) * (d - Complex.I * x) * (t + 1) *
          (y (x + Complex.I) - y x) +
        (a + Complex.I * x) * (b + Complex.I * x) *
          (c + Complex.I * x) * (d + Complex.I * x) * (t - 1) *
          (y (x - Complex.I) - y x) := by
  sorry

/-- The continuous dual Hahn imaginary-step eigen-equation, with its rational
coefficient poles cleared. Andrews–Askey–Roy, *Special Functions*, §6.10,
pp. 330–338 (synopsis AAR-6.10–6.11). -/
theorem continuousDualHahn_imaginary_step_equation (a b c : ℂ) (n : ℕ)
    (hregular : ∀ k ≤ n, pochhammer (a + b) k ≠ 0 ∧ pochhammer (a + c) k ≠ 0) (x : ℂ) :
    let y := fun z : ℂ => continuousDualHahn a b c n (z ^ 2)
    let t := 2 * Complex.I * x
    n * y x * t * (t - 1) * (t + 1) =
      (a - Complex.I * x) * (b - Complex.I * x) * (c - Complex.I * x) * (t + 1) *
          (y (x + Complex.I) - y x) +
        (a + Complex.I * x) * (b + Complex.I * x) * (c + Complex.I * x) * (t - 1) *
          (y (x - Complex.I) - y x) := by
  sorry

end DLMF.OrthogonalPolynomials
