/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Calculus.WeightedRayPrimitive
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Coefficients of the Bessel comparison equation at a simple pole

The differential recurrences retain the removable value at zero. The weighted
radial primitive fixes every `B` coefficient, leaving exactly one arbitrary
integration constant for each subsequent `A` coefficient. Real smooth and complex
analytic data use the same equations. Source: Olver, *Asymptotics and Special
Functions*, Chapter 12, §2, (2.05)–(2.10), pp. 439–440.
-/

@[expose] public noncomputable section

open Set Finset
open scoped Topology

namespace ODE

variable {𝕜 : Type*} [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ]

/-- The simple-pole coefficient differential equations, including the removable
value at zero. The parameter `nu` may be complex for the formal construction.
Olver, Chapter 12, (2.07)–(2.10), pp. 439–440. -/
def IsSimplePoleCoefficientSequence (ψ : 𝕜 → ℂ) (ν : ℂ)
    (A B : ℕ → 𝕜 → ℂ) (D : Set 𝕜) : Prop :=
  ContDiffOn 𝕜 ⊤ ψ D ∧ (∀ n, ContDiffOn 𝕜 ⊤ (A n) D) ∧
    (∀ n, ContDiffOn 𝕜 ⊤ (B n) D) ∧ (∀ z ∈ D, A 0 z = 1) ∧
    (∀ n z, z ∈ D →
      (algebraMap 𝕜 ℂ z) * deriv (deriv (A n)) z + (ν + 1) * deriv (A n) z -
        ψ z * A n z + (algebraMap 𝕜 ℂ z) * deriv (B n) z + B n z / 2 = 0) ∧
    ∀ n z, z ∈ D →
      deriv (A (n + 1)) z + (algebraMap 𝕜 ℂ z) * deriv (deriv (B n)) z +
        (1 - ν) * deriv (B n) z - ψ z * B n z = 0

/-- The smoothness, leading normalization, and two differential recurrences. -/
theorem isSimplePoleCoefficientSequence_iff (ψ : 𝕜 → ℂ) (ν : ℂ)
    (A B : ℕ → 𝕜 → ℂ) (D : Set 𝕜) :
    IsSimplePoleCoefficientSequence ψ ν A B D ↔
      ContDiffOn 𝕜 ⊤ ψ D ∧ (∀ n, ContDiffOn 𝕜 ⊤ (A n) D) ∧
        (∀ n, ContDiffOn 𝕜 ⊤ (B n) D) ∧ (∀ z ∈ D, A 0 z = 1) ∧
        (∀ n z, z ∈ D →
          (algebraMap 𝕜 ℂ z) * deriv (deriv (A n)) z + (ν + 1) * deriv (A n) z -
            ψ z * A n z + (algebraMap 𝕜 ℂ z) * deriv (B n) z + B n z / 2 = 0) ∧
        ∀ n z, z ∈ D →
          deriv (A (n + 1)) z + (algebraMap 𝕜 ℂ z) * deriv (deriv (B n)) z +
            (1 - ν) * deriv (B n) z - ψ z * B n z = 0 := Iff.rfl

/-- Constructor for the simple-pole coefficient sequence. -/
theorem IsSimplePoleCoefficientSequence.mk
    {ψ : 𝕜 → ℂ} {ν : ℂ} {A B : ℕ → 𝕜 → ℂ} {D : Set 𝕜}
    (hψ : ContDiffOn 𝕜 ⊤ ψ D) (hA : ∀ n, ContDiffOn 𝕜 ⊤ (A n) D)
    (hB : ∀ n, ContDiffOn 𝕜 ⊤ (B n) D) (hzero : ∀ z ∈ D, A 0 z = 1)
    (hfirst : ∀ n z, z ∈ D →
      (algebraMap 𝕜 ℂ z) * deriv (deriv (A n)) z + (ν + 1) * deriv (A n) z -
        ψ z * A n z + (algebraMap 𝕜 ℂ z) * deriv (B n) z + B n z / 2 = 0)
    (hsecond : ∀ n z, z ∈ D →
      deriv (A (n + 1)) z + (algebraMap 𝕜 ℂ z) * deriv (deriv (B n)) z +
        (1 - ν) * deriv (B n) z - ψ z * B n z = 0) :
    IsSimplePoleCoefficientSequence ψ ν A B D := ⟨hψ, hA, hB, hzero, hfirst, hsecond⟩

/-- The first recurrence determines the value of every `B_n` at zero without
any division by the independent variable. Olver, Chapter 12, §2, p. 440. -/
theorem IsSimplePoleCoefficientSequence.B_zero
    {ψ : 𝕜 → ℂ} {ν : ℂ} {A B : ℕ → 𝕜 → ℂ} {D : Set 𝕜}
    (h : IsSimplePoleCoefficientSequence ψ ν A B D) (hzero : 0 ∈ D) (n : ℕ) :
    B n 0 = 2 * (ψ 0 * A n 0 - (ν + 1) * deriv (A n) 0) := by
  have heq := h.2.2.2.2.1 n 0 hzero
  simp only [map_zero, zero_mul, zero_add, add_zero] at heq
  linear_combination 2 * heq

variable [IsScalarTower ℝ 𝕜 ℂ]

/-- The weighted primitive specifies `B_n` completely, with no free integration
constant. Olver, Chapter 12, (2.07), p. 440. -/
theorem IsSimplePoleCoefficientSequence.B_eq_weightedRayPrimitive
    {ψ : 𝕜 → ℂ} {ν : ℂ} {A B : ℕ → 𝕜 → ℂ} {D : Set 𝕜}
    (hD : IsOpen D) (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D)
    (h : IsSimplePoleCoefficientSequence ψ ν A B D) (n : ℕ) {z : 𝕜} (hz : z ∈ D) :
    B n z = -deriv (A n) z + MeasureTheory.weightedRayPrimitive (-1 / 2)
      (fun w => ψ w * A n w - (ν + 1 / 2) * deriv (A n) w) z := by
  sorry

/-- Smooth real perturbations have smooth coefficient sequences with arbitrary
prescribed constants in `A_{n+1}`. Olver, Chapter 12, §2, pp. 439–440. -/
theorem exists_simplePoleCoefficientSequence_real {D : Set ℝ}
    (hD : IsOpen D) (hstar : StarConvex ℝ 0 D) (hzero : 0 ∈ D)
    {ψ : ℝ → ℂ} (hψ : ContDiffOn ℝ ⊤ ψ D) (ν : ℂ)
    (c : ℕ → ℂ) (hc : c 0 = 1) :
    ∃ A B : ℕ → ℝ → ℂ, IsSimplePoleCoefficientSequence ψ ν A B D ∧
      ∀ n, A n 0 = c n := by
  sorry

/-- Analytic perturbations on a simply connected domain containing zero have
analytic coefficient sequences with all `A_n(0)` prescribed. The `B` equation
has a removable regular singularity at zero. Olver, Chapter 12, §2, p. 440. -/
theorem exists_simplePoleCoefficientSequence_complex {D : Set ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) (hzero : 0 ∈ D)
    {ψ : ℂ → ℂ} (hψ : AnalyticOnNhd ℂ ψ D) (ν : ℂ)
    (c : ℕ → ℂ) (hc : c 0 = 1) :
    ∃ A B : ℕ → ℂ → ℂ, IsSimplePoleCoefficientSequence ψ ν A B D ∧
      (∀ n, AnalyticOnNhd ℂ (A n) D ∧ AnalyticOnNhd ℂ (B n) D) ∧
      ∀ n, A n 0 = c n := by
  sorry

omit [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ] [IsScalarTower ℝ 𝕜 ℂ]

/-- The actual finite compound Bessel sum. Its comparison pair is
`P=sqrt(z)*I_nu(u*sqrt(z))`, `Q=z*I_(nu+1)(u*sqrt(z))/u`, or the
corresponding pair with `K_nu,-K_(nu+1)`. Olver, Chapter 12, §2, p. 440. -/
def simplePolePartialSum (A B : ℕ → 𝕜 → ℂ) (P Q : 𝕜 → ℂ)
    (u : ℂ) (n : ℕ) (z : 𝕜) : ℂ :=
  P z * ∑ s ∈ range (n + 1), A s z / u ^ (2 * s) +
    Q z * ∑ s ∈ range n, B s z / u ^ (2 * s)

/-- The defining compound finite sum. -/
theorem simplePolePartialSum_def (A B : ℕ → 𝕜 → ℂ) (P Q : 𝕜 → ℂ)
    (u : ℂ) (n : ℕ) (z : 𝕜) : simplePolePartialSum A B P Q u n z =
    P z * ∑ s ∈ range (n + 1), A s z / u ^ (2 * s) +
      Q z * ∑ s ∈ range n, B s z / u ^ (2 * s) := rfl

/-- The leading compound sum is its leading `A` term. -/
@[simp] theorem simplePolePartialSum_zero (A B : ℕ → 𝕜 → ℂ) (P Q : 𝕜 → ℂ)
    (u : ℂ) (z : 𝕜) : simplePolePartialSum A B P Q u 0 z = P z * A 0 z := by
  simp [simplePolePartialSum]

/-- The exact finite residual of the compound Bessel expansion. The identities
for `P,Q` are the two consecutive-order Bessel derivative identities in the
simple-pole variable. Olver, Chapter 12, §2 and Theorem 3.1, pp. 440–442. -/
theorem simplePolePartialSum_residual {D : Set ℂ} (hD : IsOpen D)
    {ψ : ℂ → ℂ} {ν u : ℂ} {A B : ℕ → ℂ → ℂ} {P Q : ℂ → ℂ}
    (hseq : IsSimplePoleCoefficientSequence ψ ν A B D)
    (hP : AnalyticOnNhd ℂ P D) (hQ : AnalyticOnNhd ℂ Q D)
    (hPderiv : ∀ z ∈ D, deriv P z = (ν + 1) / (2 * z) * P z + u ^ 2 / (2 * z) * Q z)
    (hQderiv : ∀ z ∈ D, deriv Q z = P z / 2 - (ν - 1) / (2 * z) * Q z)
    (hu : u ≠ 0) {z : ℂ} (hz : z ∈ D) (hz_ne : z ≠ 0) (n : ℕ) :
    deriv (deriv (simplePolePartialSum A B P Q u n)) z -
      (u ^ 2 / (4 * z) + (ν ^ 2 - 1) / (4 * z ^ 2) + ψ z / z) *
        simplePolePartialSum A B P Q u n z =
      -P z * (2 * z * deriv (B n) z + B n z) / (2 * z * u ^ (2 * n)) := by
  sorry

end ODE
