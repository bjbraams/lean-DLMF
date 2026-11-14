/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Fourier endpoint expansions with an integrable highest derivative

Olver, *Asymptotics and Special Functions*, Chapter 3, §5,
pp. 74–76, synopsis O-3.04. Lower derivatives have finite endpoint limits,
while the highest derivative is only integrable and piecewise continuous.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Complex Asymptotics
open scoped Topology

namespace Asymptotics

/-- Exact finite-endpoint expansion and little-oh remainder under an integrable highest
piecewise continuous derivative. Olver, Chapter 3, §5, synopsis O-3.04. -/
theorem fourier_endpoint_expansion_of_integrable_highestDerivative
    {a b : ℝ} (hab : a < b) (D : ℕ → ℝ → ℂ) (N : ℕ)
    (singular : Finset ℝ)
    (hc : ∀ k < N, ContinuousOn (D k) (Ioo a b))
    (hcN : ContinuousOn (D N) (Ioo a b \ (singular : Set ℝ)))
    (hd : ∀ k < N, ∀ t ∈ Ioo a b \ (singular : Set ℝ),
      HasDerivAt (D k) (D (k + 1) t) t)
    (hi : IntegrableOn (D N) (Ioo a b)) (A B : ℕ → ℂ)
    (hA : ∀ k < N, Tendsto (D k) (𝓝[>] a) (𝓝 (A k)))
    (hB : ∀ k < N, Tendsto (D k) (𝓝[<] b) (𝓝 (B k))) :
    (∀ x : ℝ, x ≠ 0 → (∫ t in a..b, exp (I * x * t) * D 0 t) =
      (∑ k ∈ Finset.range N, (-1 : ℂ) ^ k / (I * x) ^ (k + 1) *
        (exp (I * x * b) * B k - exp (I * x * a) * A k)) +
      (-1 : ℂ) ^ N / (I * x) ^ N * ∫ t in a..b, exp (I * x * t) * D N t) ∧
    (fun x : ℝ => (∫ t in a..b, exp (I * x * t) * D 0 t) -
      ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k / (I * x) ^ (k + 1) *
        (exp (I * x * b) * B k - exp (I * x * a) * A k))
      =o[atTop] (fun x : ℝ => x⁻¹ ^ N) := by
  sorry

/-- The half-line endpoint expansion preserves an ordinary conditional cutoff integral.
Olver, Chapter 3, §5, synopsis O-3.04. No absolute integrability of lower derivatives is
assumed. Their endpoint contributions at infinity vanish by explicit hypotheses. -/
theorem exists_fourier_halfLine_expansion_of_integrable_highestDerivative
    (a : ℝ) (D : ℕ → ℝ → ℂ) (N : ℕ) (singular : Finset ℝ)
    (hc : ∀ k < N, ContinuousOn (D k) (Ioi a))
    (hcN : ContinuousOn (D N) (Ioi a \ (singular : Set ℝ)))
    (hd : ∀ k < N, ∀ t ∈ Ioi a \ (singular : Set ℝ),
      HasDerivAt (D k) (D (k + 1) t) t)
    (hi : IntegrableOn (D N) (Ioi a)) (A : ℕ → ℂ)
    (hA : ∀ k < N, Tendsto (D k) (𝓝[>] a) (𝓝 (A k)))
    (hinfty : ∀ k < N, Tendsto (D k) atTop (𝓝 0)) :
    ∃ F : ℝ → ℂ,
      (∀ x : ℝ, 0 < x → Tendsto (fun T : ℝ =>
        ∫ t in a..T, exp (I * x * t) * D 0 t) atTop (𝓝 (F x))) ∧
      (fun x : ℝ => F x + ∑ k ∈ Finset.range N,
        (-1 : ℂ) ^ k / (I * x) ^ (k + 1) * exp (I * x * a) * A k)
        =o[atTop] (fun x : ℝ => x⁻¹ ^ N) := by
  sorry

end Asymptotics
