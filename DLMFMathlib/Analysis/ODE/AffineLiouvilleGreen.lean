/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.ComplexLiouvilleGreenExpansion

/-!
# Liouville–Green expansions with an affine parameter term

The equation is `W''=(u^2+u*phi+psi)W`. The actual finite remainder functions
and the exact truncation residual distinguish the three source variations.
The comparison solutions have constant Wronskian `-2`, and the quantitative error
retains both the lower bound for `|u+phi/2|` and the derivative weight.
Source: Olver, *Asymptotics and Special Functions*, Chapter 10,
Theorem 9.1, pp. 382–386.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Real BigOperators Topology

namespace Complex

/-- The analytic coefficient recursion for an affine-parameter LG equation.
Prescribing values at one point fixes all integration constants. Olver,
Chapter 10, §9, pp. 382–383. -/
def IsAffineLiouvilleGreenCoefficientSequence (φ : ℂ → ℂ)
    (ψ A : ℕ → ℂ → ℂ) (D : Set ℂ) : Prop :=
  AnalyticOnNhd ℂ φ D ∧ (∀ n, AnalyticOnNhd ℂ (ψ n) D) ∧
    (∀ n, AnalyticOnNhd ℂ (A n) D) ∧ (∀ z ∈ D, A 0 z = 1) ∧
    ∀ s z, z ∈ D → 2 * deriv (A (s + 1)) z =
      (∑ j ∈ Finset.range (s + 1), ψ j z * A (s - j) z) -
        deriv (deriv (A s)) z - φ z * deriv (A s) z -
          (deriv φ z / 2 + φ z ^ 2 / 4) * A s z

/-- The explicit analytic hypotheses and coefficient recurrence. -/
theorem isAffineLiouvilleGreenCoefficientSequence_iff (φ : ℂ → ℂ)
    (ψ A : ℕ → ℂ → ℂ) (D : Set ℂ) :
    IsAffineLiouvilleGreenCoefficientSequence φ ψ A D ↔
      AnalyticOnNhd ℂ φ D ∧ (∀ n, AnalyticOnNhd ℂ (ψ n) D) ∧
        (∀ n, AnalyticOnNhd ℂ (A n) D) ∧ (∀ z ∈ D, A 0 z = 1) ∧
        ∀ s z, z ∈ D → 2 * deriv (A (s + 1)) z =
          (∑ j ∈ Finset.range (s + 1), ψ j z * A (s - j) z) -
            deriv (deriv (A s)) z - φ z * deriv (A s) z -
              (deriv φ z / 2 + φ z ^ 2 / 4) * A s z := Iff.rfl

/-- Construct affine coefficient data from the displayed analytic recursion. -/
theorem IsAffineLiouvilleGreenCoefficientSequence.mk
    {φ : ℂ → ℂ} {ψ A : ℕ → ℂ → ℂ} {D : Set ℂ}
    (hφ : AnalyticOnNhd ℂ φ D) (hψ : ∀ n, AnalyticOnNhd ℂ (ψ n) D)
    (hA : ∀ n, AnalyticOnNhd ℂ (A n) D) (hzero : ∀ z ∈ D, A 0 z = 1)
    (hrec : ∀ s z, z ∈ D → 2 * deriv (A (s + 1)) z =
      (∑ j ∈ Finset.range (s + 1), ψ j z * A (s - j) z) -
        deriv (deriv (A s)) z - φ z * deriv (A s) z -
          (deriv φ z / 2 + φ z ^ 2 / 4) * A s z) :
    IsAffineLiouvilleGreenCoefficientSequence φ ψ A D := ⟨hφ, hψ, hA, hzero, hrec⟩

/-- Every prescribed sequence of integration constants produces analytic affine
LG coefficients on a simply connected domain. Olver, Chapter 10, §9, p. 383. -/
theorem exists_affineLiouvilleGreenCoefficientSequence {D : Set ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) {b : ℂ} (hb : b ∈ D)
    {φ : ℂ → ℂ} {ψ : ℕ → ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ D)
    (hψ : ∀ n, AnalyticOnNhd ℂ (ψ n) D) (initial : ℕ → ℂ) :
    ∃ A : ℕ → ℂ → ℂ, IsAffineLiouvilleGreenCoefficientSequence φ ψ A D ∧
      ∀ n, A (n + 1) b = initial n := by
  sorry

/-- The exact coefficient remainder `Psi_n=u^n*(psi-sum_(j<n)psi_j/u^j)`.
Olver, Chapter 10, Theorem 9.1, pp. 383–384. -/
def affineLiouvilleGreenRemainder (ψ : ℂ → ℂ) (coeff : ℕ → ℂ → ℂ)
    (u : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  u ^ n * (ψ z - ∑ j ∈ Finset.range n, coeff j z / u ^ j)

/-- The defining finite remainder. -/
theorem affineLiouvilleGreenRemainder_def (ψ : ℂ → ℂ) (coeff : ℕ → ℂ → ℂ)
    (u : ℂ) (n : ℕ) (z : ℂ) : affineLiouvilleGreenRemainder ψ coeff u n z =
      u ^ n * (ψ z - ∑ j ∈ Finset.range n, coeff j z / u ^ j) := rfl

/-- The order-zero remainder is the original perturbation. -/
@[simp] theorem affineLiouvilleGreenRemainder_zero (ψ : ℂ → ℂ)
    (coeff : ℕ → ℂ → ℂ) (u z : ℂ) :
    affineLiouvilleGreenRemainder ψ coeff u 0 z = ψ z := by
  simp [affineLiouvilleGreenRemainder]

/-- The finite affine LG approximation, with `F'=phi/2` supplying the exponential
prefactor `X=exp(F)`. Olver, Chapter 10, §9, pp. 382–384. -/
def affineLiouvilleGreenPartialSum (A : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (u : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  exp (u * z + F z) * ∑ s ∈ Finset.range N, A s z / u ^ s

/-- The defining exponential finite sum. -/
theorem affineLiouvilleGreenPartialSum_def (A : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (u : ℂ) (N : ℕ) (z : ℂ) : affineLiouvilleGreenPartialSum A F u N z =
      exp (u * z + F z) * ∑ s ∈ Finset.range N, A s z / u ^ s := rfl

/-- The zero-term affine approximation vanishes. -/
@[simp] theorem affineLiouvilleGreenPartialSum_zero (A : ℕ → ℂ → ℂ)
    (F : ℂ → ℂ) (u z : ℂ) : affineLiouvilleGreenPartialSum A F u 0 z = 0 := by
  simp [affineLiouvilleGreenPartialSum]

/-- The comparison pair `K*exp(+-S)`, where `K^2*h=1` and `S'=h`, has Wronskian
`-2` and the exact comparison coefficient `h^2-h''/(2h)+3h'^2/(4h^2)`.
Olver, Chapter 10, Theorem 9.1, pp. 383–384. -/
theorem liouvilleGreen_comparison_pair {D : Set ℂ} (hD : IsOpen D)
    {h K S : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h D) (hK : AnalyticOnNhd ℂ K D)
    (hS : AnalyticOnNhd ℂ S D) (hroot : ∀ z ∈ D, K z ^ 2 * h z = 1)
    (hprimitive : ∀ z ∈ D, deriv S z = h z) :
    let Z₁ := fun z => K z * exp (S z)
    let Z₂ := fun z => K z * exp (-S z)
    ∀ z ∈ D,
      Z₁ z * deriv Z₂ z - deriv Z₁ z * Z₂ z = -2 ∧
      deriv (deriv Z₁) z =
        (h z ^ 2 - deriv (deriv h) z / (2 * h z) +
          3 * deriv h z ^ 2 / (4 * h z ^ 2)) * Z₁ z ∧
      deriv (deriv Z₂) z =
        (h z ^ 2 - deriv (deriv h) z / (2 * h z) +
          3 * deriv h z ^ 2 / (4 * h z ^ 2)) * Z₂ z := by
  sorry

/-- The exact residual involves both `A_N'` and the distinct primitive `T_N'`.
Olver, Chapter 10, Theorem 9.1, pp. 383–384. -/
theorem affineLiouvilleGreenPartialSum_residual {D : Set ℂ} (hD : IsOpen D)
    {φ ψ F T : ℂ → ℂ} {coeff A : ℕ → ℂ → ℂ}
    (hcoeff : IsAffineLiouvilleGreenCoefficientSequence φ coeff A D)
    (hψ : AnalyticOnNhd ℂ ψ D) (hF : AnalyticOnNhd ℂ F D) (hT : AnalyticOnNhd ℂ T D)
    (hFderiv : ∀ z ∈ D, deriv F z = φ z / 2) {u : ℂ} (hu : u ≠ 0)
    {N : ℕ} (hN : 1 ≤ N)
    (hTderiv : ∀ z ∈ D, deriv T z =
      ∑ s ∈ Finset.range N, A s z * affineLiouvilleGreenRemainder ψ coeff u (N - s) z)
    {z : ℂ} (hz : z ∈ D) :
    deriv (deriv (affineLiouvilleGreenPartialSum A F u N)) z -
      (u ^ 2 + u * φ z + ψ z) * affineLiouvilleGreenPartialSum A F u N z =
        -exp (u * z + F z) * (2 * deriv (A N) z / u ^ (N - 1) + deriv T z / u ^ N) := by
  sorry

/-- The finite-reference source bound, with the separate variations of `A_N`,
`T_N` and `H`, a positive pathwise lower bound `lambda` for `|u+phi/2|`, and
its exact derivative weight. Olver, Chapter 10, Theorem 9.1, pp. 384–386. -/
theorem exists_affineLiouvilleGreen_finite_reference {D : Set ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) {b u : ℂ} (hb : b ∈ D) (hu : u ≠ 0)
    {φ ψ F T H : ℂ → ℂ} {coeff A : ℕ → ℂ → ℂ}
    (hcoeff : IsAffineLiouvilleGreenCoefficientSequence φ coeff A D)
    (hψ : AnalyticOnNhd ℂ ψ D) (hF : AnalyticOnNhd ℂ F D)
    (hT : AnalyticOnNhd ℂ T D) (hH : AnalyticOnNhd ℂ H D)
    (hFderiv : ∀ z ∈ D, deriv F z = φ z / 2)
    (hne : ∀ z ∈ D, u + φ z / 2 ≠ 0) {N : ℕ} (hN : 1 ≤ N)
    (hTderiv : ∀ z ∈ D, deriv T z =
      ∑ s ∈ Finset.range N, A s z * affineLiouvilleGreenRemainder ψ coeff u (N - s) z)
    (hHderiv : ∀ z ∈ D, deriv H z = ψ z - φ z ^ 2 / 4 +
      deriv (deriv φ) z / (4 * u + 2 * φ z) -
        3 * deriv φ z ^ 2 / (4 * u + 2 * φ z) ^ 2) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε D ∧ ε b = 0 ∧ deriv ε b = 0 ∧
      (∀ z ∈ D,
        let W := fun t => affineLiouvilleGreenPartialSum A F u N t + ε t
        deriv (deriv W) z = (u ^ 2 + u * φ z + ψ z) * W z) ∧
      ∀ γ : ℝ → ℂ, TauCeti.IsPiecewiseC1On γ 0 1 → γ 0 = b →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ D) →
        MonotoneOn (fun t => (u * γ t + F (γ t)).re) (Icc 0 1) →
        BoundedVariationOn (A N ∘ γ) (Icc 0 1) →
        BoundedVariationOn (T ∘ γ) (Icc 0 1) →
        BoundedVariationOn (H ∘ γ) (Icc 0 1) →
        ∀ lam : ℝ, 0 < lam →
          (∀ t ∈ Icc (0 : ℝ) 1, lam ≤ ‖u + φ (γ t) / 2‖) →
          let mu := Real.sqrt lam * (‖u + φ (γ 1) / 2‖ ^ (1 / 2 : ℝ) +
            ‖deriv φ (γ 1)‖ / (4 * ‖u + φ (γ 1) / 2‖ ^ (3 / 2 : ℝ)))
          let B := ‖exp (u * γ 1 + F (γ 1))‖ / lam *
            (2 * (eVariationOn (A N ∘ γ) (Icc 0 1)).toReal / ‖u‖ ^ (N - 1) +
              (eVariationOn (T ∘ γ) (Icc 0 1)).toReal / ‖u‖ ^ N) *
                Real.exp ((eVariationOn (H ∘ γ) (Icc 0 1)).toReal / lam)
          ‖ε (γ 1)‖ ≤ B ∧ ‖deriv ε (γ 1)‖ / mu ≤ B := by
  sorry

/-- The affine-parameter error theorem with a prescribed recessive boundary or
infinite initial tail. All three coefficient/control variations and the positive
lower bound for the comparison frequency are retained when a finite progressive
path is appended. Olver, Chapter 10, Theorem 9.1, pp. 384–386. -/
theorem exists_affineLiouvilleGreen_endpoint_reference {D : Set ℂ}
    (hD : IsOpen D) (hsc : IsSimplyConnected D) {u : ℂ} (hu : u ≠ 0)
    {φ ψ F T H : ℂ → ℂ} {coeff A : ℕ → ℂ → ℂ}
    (hcoeff : IsAffineLiouvilleGreenCoefficientSequence φ coeff A D)
    (hψ : AnalyticOnNhd ℂ ψ D) (hF : AnalyticOnNhd ℂ F D)
    (hT : AnalyticOnNhd ℂ T D) (hH : AnalyticOnNhd ℂ H D)
    (hFderiv : ∀ z ∈ D, deriv F z = φ z / 2)
    (hne : ∀ z ∈ D, u + φ z / 2 ≠ 0) {N : ℕ} (hN : 1 ≤ N)
    (hTderiv : ∀ z ∈ D, deriv T z =
      ∑ s ∈ Finset.range N, A s z * affineLiouvilleGreenRemainder ψ coeff u (N - s) z)
    (hHderiv : ∀ z ∈ D, deriv H z = ψ z - φ z ^ 2 / 4 +
      deriv (deriv φ) z / (4 * u + 2 * φ z) -
        3 * deriv φ z ^ 2 / (4 * u + 2 * φ z) ^ 2)
    {γ₀ : ℝ → ℂ} (hγ₀ : ContinuousOn γ₀ (Ioc 0 1))
    (hregular : ∀ s : ℝ, 0 < s → s < 1 → TauCeti.IsPiecewiseC1On γ₀ s 1)
    (himage : ∀ t ∈ Ioc (0 : ℝ) 1, γ₀ t ∈ D)
    (hprogressive : MonotoneOn (fun t => (u * γ₀ t + F (γ₀ t)).re) (Ioc 0 1))
    (hend : Tendsto (fun t => (u * γ₀ t + F (γ₀ t)).re) (𝓝[>] 0) atBot)
    (hvariationA : BoundedVariationOn (A N ∘ γ₀) (Ioc 0 1))
    (hvariationT : BoundedVariationOn (T ∘ γ₀) (Ioc 0 1))
    (hvariationH : BoundedVariationOn (H ∘ γ₀) (Ioc 0 1))
    {tailLowerBound : ℝ} (htailLowerBound : 0 < tailLowerBound)
    (htail : ∀ t ∈ Ioc (0 : ℝ) 1, tailLowerBound ≤ ‖u + φ (γ₀ t) / 2‖) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε D ∧
      (∀ z ∈ D,
        let W := fun t => affineLiouvilleGreenPartialSum A F u N t + ε t
        deriv (deriv W) z = (u ^ 2 + u * φ z + ψ z) * W z) ∧
      Tendsto (fun t => ε (γ₀ t) / exp (u * γ₀ t + F (γ₀ t))) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t =>
        let mu := Real.sqrt tailLowerBound * (‖u + φ (γ₀ t) / 2‖ ^ (1 / 2 : ℝ) +
          ‖deriv φ (γ₀ t)‖ / (4 * ‖u + φ (γ₀ t) / 2‖ ^ (3 / 2 : ℝ)))
        deriv ε (γ₀ t) / (mu * exp (u * γ₀ t + F (γ₀ t)))) (𝓝[>] 0) (𝓝 0) ∧
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ γ : ℝ → ℂ,
        TauCeti.IsPiecewiseC1On γ 0 1 → γ 0 = γ₀ s →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ D) →
        MonotoneOn (fun t => (u * γ t + F (γ t)).re) (Icc 0 1) →
        BoundedVariationOn (A N ∘ γ) (Icc 0 1) →
        BoundedVariationOn (T ∘ γ) (Icc 0 1) →
        BoundedVariationOn (H ∘ γ) (Icc 0 1) →
        ∀ lam : ℝ, 0 < lam →
          (∀ t ∈ Ioc (0 : ℝ) s, lam ≤ ‖u + φ (γ₀ t) / 2‖) →
          (∀ t ∈ Icc (0 : ℝ) 1, lam ≤ ‖u + φ (γ t) / 2‖) →
          let VA := (eVariationOn (A N ∘ γ₀) (Ioc 0 s)).toReal +
            (eVariationOn (A N ∘ γ) (Icc 0 1)).toReal
          let VT := (eVariationOn (T ∘ γ₀) (Ioc 0 s)).toReal +
            (eVariationOn (T ∘ γ) (Icc 0 1)).toReal
          let VH := (eVariationOn (H ∘ γ₀) (Ioc 0 s)).toReal +
            (eVariationOn (H ∘ γ) (Icc 0 1)).toReal
          let mu := Real.sqrt lam * (‖u + φ (γ 1) / 2‖ ^ (1 / 2 : ℝ) +
            ‖deriv φ (γ 1)‖ / (4 * ‖u + φ (γ 1) / 2‖ ^ (3 / 2 : ℝ)))
          let B := ‖exp (u * γ 1 + F (γ 1))‖ / lam *
            (2 * VA / ‖u‖ ^ (N - 1) + VT / ‖u‖ ^ N) * Real.exp (VH / lam)
          ‖ε (γ 1)‖ ≤ B ∧ ‖deriv ε (γ 1)‖ / mu ≤ B := by
  sorry

end Complex
