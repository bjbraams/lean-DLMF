/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Calculus.WeightedRayPrimitive
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Data.Set.Function

/-!
# Liouville coordinates at simple zeros and poles

The real simple-zero coordinate is an actual weighted integral of the positive
factor `F=f/(x-x0)`, including its removable ratio at the turning point. Analytic
local coordinates also retain the simple-pole normalization and transformed
double-pole coefficient. Source: Olver, *Asymptotics and Special Functions*,
Chapter 10, §1, pp. 362–363; Chapter 11, Lemma 3.1, p. 399;
Chapter 12, §2, pp. 438–440.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace ODE.RealTurningPoint

/-- The removable ratio `zeta(x)/(x-x0)` for `f(x)=(x-x0)*F(x)`, with the
positive real branch when `F>0`. Olver, Chapter 11, Lemma 3.1, p. 399. -/
def ratio (F : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  ((3 / 2 : ℝ) * ∫ t : ℝ in 0..1,
    Real.sqrt t * Real.sqrt (F (x₀ + t * (x - x₀)))) ^ (2 / 3 : ℝ)

/-- The defining weighted integral of the removable ratio. -/
theorem ratio_def (F : ℝ → ℝ) (x₀ x : ℝ) : ratio F x₀ x =
    ((3 / 2 : ℝ) * ∫ t : ℝ in 0..1,
      Real.sqrt t * Real.sqrt (F (x₀ + t * (x - x₀)))) ^ (2 / 3 : ℝ) := rfl

/-- The increasing real turning-point coordinate. Olver, Chapter 11,
Lemma 3.1, p. 399. -/
def coordinate (F : ℝ → ℝ) (x₀ x : ℝ) : ℝ := (x - x₀) * ratio F x₀ x

/-- The coordinate is the linear factor times its removable positive ratio. -/
theorem coordinate_def (F : ℝ → ℝ) (x₀ x : ℝ) :
    coordinate F x₀ x = (x - x₀) * ratio F x₀ x := rfl

/-- The turning point maps to zero. -/
@[simp] theorem coordinate_self (F : ℝ → ℝ) (x₀ : ℝ) : coordinate F x₀ x₀ = 0 := by
  simp [coordinate]

/-- The positive scale `h=f/zeta`, extended through the turning point.
Olver, Chapter 11, Lemma 3.1, p. 399. -/
def scale (F : ℝ → ℝ) (x₀ x : ℝ) : ℝ := F x / ratio F x₀ x

/-- The defining removable scale. -/
theorem scale_def (F : ℝ → ℝ) (x₀ x : ℝ) : scale F x₀ x = F x / ratio F x₀ x := rfl

/-- The Liouville amplitude `h^(-1/4)` with positive real branch.
Olver, Chapter 11, Lemma 3.1, p. 399. -/
def amplitude (F : ℝ → ℝ) (x₀ x : ℝ) : ℝ := scale F x₀ x ^ (-1 / 4 : ℝ)

/-- The defining positive-branch amplitude. -/
theorem amplitude_def (F : ℝ → ℝ) (x₀ x : ℝ) :
    amplitude F x₀ x = scale F x₀ x ^ (-1 / 4 : ℝ) := rfl

/-- The transformed perturbation evaluated at `zeta(x)`, using the nonsingular
amplitude formula rather than cancellation of apparent poles.
Olver, Chapter 11, Lemma 3.1, p. 399. -/
def perturbation (F : ℝ → ℝ) (g : ℝ → ℂ) (x₀ x : ℝ) : ℂ :=
  (g x - (deriv (deriv (amplitude F x₀)) x / amplitude F x₀ x : ℝ)) / scale F x₀ x

/-- The defining nonsingular transformed perturbation. -/
theorem perturbation_def (F : ℝ → ℝ) (g : ℝ → ℂ) (x₀ x : ℝ) :
    perturbation F g x₀ x =
      (g x - (deriv (deriv (amplitude F x₀)) x / amplitude F x₀ x : ℝ)) / scale F x₀ x := rfl

/-- The exact coordinate normalization at the turning point.
Olver, Chapter 11, Lemma 3.1, p. 399. -/
theorem values_at_turningPoint {F : ℝ → ℝ} {x₀ : ℝ} (hF : 0 < F x₀) :
    ratio F x₀ x₀ = F x₀ ^ (1 / 3 : ℝ) ∧
    scale F x₀ x₀ = F x₀ ^ (2 / 3 : ℝ) ∧
    amplitude F x₀ x₀ = F x₀ ^ (-1 / 6 : ℝ) := by
  sorry

/-- The ratio, scale and amplitude have two continuous derivatives through the
turning point, and the coordinate has positive derivative `sqrt(h)`.
Olver, Chapter 11, Lemma 3.1, p. 399. -/
theorem regularity {D : Set ℝ} (hD : IsOpen D) (hconvex : Convex ℝ D)
    {F : ℝ → ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ D) (hF : ContDiffOn ℝ 2 F D)
    (hpositive : ∀ x ∈ D, 0 < F x) :
    ContDiffOn ℝ 2 (ratio F x₀) D ∧ ContDiffOn ℝ 2 (scale F x₀) D ∧
    ContDiffOn ℝ 2 (amplitude F x₀) D ∧ ContDiffOn ℝ 3 (coordinate F x₀) D ∧
    ∀ x ∈ D, 0 < ratio F x₀ x ∧ 0 < scale F x₀ x ∧ 0 < amplitude F x₀ x ∧
      deriv (coordinate F x₀) x = Real.sqrt (scale F x₀ x) ∧
      coordinate F x₀ x * scale F x₀ x = (x - x₀) * F x := by
  sorry

/-- Both signed integral definitions agree with the single removable coordinate.
Olver, Chapter 11, Lemma 3.1, p. 399. -/
theorem coordinate_integrals {D : Set ℝ} (hD : IsOpen D) (hconvex : Convex ℝ D)
    {F : ℝ → ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ D) (hF : ContDiffOn ℝ 2 F D)
    (hpositive : ∀ x ∈ D, 0 < F x) {x : ℝ} (hx : x ∈ D) :
    (x₀ ≤ x → (2 / 3 : ℝ) * coordinate F x₀ x ^ (3 / 2 : ℝ) =
      ∫ t in x₀..x, Real.sqrt ((t - x₀) * F t)) ∧
    (x ≤ x₀ → (2 / 3 : ℝ) * (-coordinate F x₀ x) ^ (3 / 2 : ℝ) =
      ∫ t in x..x₀, Real.sqrt (-(t - x₀) * F t)) := by
  sorry

/-- The coordinate has a differentiable inverse on its open image, with positive
inverse derivative. Olver, Chapter 11, Lemma 3.1, p. 399. -/
theorem inverse_properties {D : Set ℝ} (hD : IsOpen D) (hconvex : Convex ℝ D)
    {F : ℝ → ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ D) (hF : ContDiffOn ℝ 2 F D)
    (hpositive : ∀ x ∈ D, 0 < F x) :
    let zeta := coordinate F x₀
    let X := Function.invFunOn zeta D
    StrictMonoOn zeta D ∧ (∀ x ∈ D, X (zeta x) = x) ∧
      (∀ y ∈ zeta '' D, X y ∈ D ∧ zeta (X y) = y) ∧ ContDiffOn ℝ 2 X (zeta '' D) ∧
      ∀ y ∈ zeta '' D, deriv X y = (Real.sqrt (scale F x₀ (X y)))⁻¹ := by
  sorry

/-- The transformed perturbation is continuous both in the original variable and
in the turning-point variable, including zero. Olver, Chapter 11,
Lemma 3.1, p. 399. -/
theorem continuousOn_perturbation {D : Set ℝ} (hD : IsOpen D) (hconvex : Convex ℝ D)
    {F : ℝ → ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ D) (hF : ContDiffOn ℝ 2 F D)
    (hpositive : ∀ x ∈ D, 0 < F x) {g : ℝ → ℂ} (hg : ContinuousOn g D) :
    ContinuousOn (perturbation F g x₀) D ∧
      ContinuousOn (fun y => perturbation F g x₀ (Function.invFunOn (coordinate F x₀) D y))
        (coordinate F x₀ '' D) := by
  sorry

/-- Away from the turning point the nonsingular perturbation is the displayed
formula with its apparent double poles. Olver, Chapter 11,
Lemma 3.1, p. 399. -/
theorem perturbation_eq_away {D : Set ℝ} (hD : IsOpen D) (hconvex : Convex ℝ D)
    {F : ℝ → ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ D) (hF : ContDiffOn ℝ 2 F D)
    (hpositive : ∀ x ∈ D, 0 < F x) (g : ℝ → ℂ) {x : ℝ} (hx : x ∈ D) (hxx₀ : x ≠ x₀) :
    let f := fun t => (t - x₀) * F t
    let zeta := coordinate F x₀ x
    perturbation F g x₀ x = (zeta / f x : ℝ) * g x +
      (5 / (16 * zeta ^ 2) + zeta *
        (4 * f x * deriv (deriv f) x - 5 * deriv f x ^ 2) / (16 * f x ^ 3) : ℝ) := by
  sorry

/-- The exact Liouville transformation through the real turning point.
It retains the continuous perturbation at zero without cancelling singular
fractions there. Olver, Chapter 11, Lemma 3.1, p. 399. -/
theorem transformed_equation {D : Set ℝ} (hD : IsOpen D) (hconvex : Convex ℝ D)
    {F : ℝ → ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ D) (hF : ContDiffOn ℝ 2 F D)
    (hpositive : ∀ x ∈ D, 0 < F x) (g : ℝ → ℂ) (u : ℂ) {x : ℝ} (hx : x ∈ D)
    {W : ℝ → ℂ} (hW : ContDiffAt ℝ 2 W (coordinate F x₀ x)) :
    let w := fun t => (amplitude F x₀ t : ℂ) * W (coordinate F x₀ t)
    deriv (deriv w) x - (u ^ 2 * ((x - x₀) * F x : ℝ) + g x) * w x =
      (amplitude F x₀ x * scale F x₀ x : ℝ) *
        (deriv (deriv W) (coordinate F x₀ x) -
          (u ^ 2 * coordinate F x₀ x + perturbation F g x₀ x) * W (coordinate F x₀ x)) := by
  sorry

end ODE.RealTurningPoint

namespace Complex

/-- A simple analytic zero admits an analytic Liouville coordinate with any
chosen cube root of the derivative, and an analytic local inverse.
Olver, Chapter 10, §1, pp. 362–363. -/
theorem exists_analytic_simpleZero_liouville_coordinate {f : ℂ → ℂ} {z₀ d : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hzero : f z₀ = 0) (hne : deriv f z₀ ≠ 0)
    (hd : d ^ 3 = deriv f z₀) :
    ∃ zeta X : ℂ → ℂ, AnalyticAt ℂ zeta z₀ ∧ AnalyticAt ℂ X 0 ∧
      zeta z₀ = 0 ∧ deriv zeta z₀ = d ∧ X 0 = z₀ ∧
      (fun z => zeta z * deriv zeta z ^ 2) =ᶠ[𝓝 z₀] f ∧
      (fun y => zeta (X y)) =ᶠ[𝓝 0] id ∧ (fun z => X (zeta z)) =ᶠ[𝓝 z₀] id := by
  sorry

/-- A simple analytic pole admits the analytic CaseIII coordinate and inverse.
Taking `c=1` gives `2sqrt(zeta)=integral sqrt(f)`; taking `c=4` gives the
Chapter12 normalization `sqrt(zeta)=integral sqrt(f)`.
Olver, Chapter 10, §1, pp. 362–363; Chapter 12, §2, pp. 438–440. -/
theorem exists_analytic_simplePole_liouville_coordinate {F : ℂ → ℂ} {z₀ c : ℂ}
    (hF : AnalyticAt ℂ F z₀) (hFzero : F z₀ ≠ 0) (hc : c ≠ 0) :
    ∃ zeta X : ℂ → ℂ, AnalyticAt ℂ zeta z₀ ∧ AnalyticAt ℂ X 0 ∧
      zeta z₀ = 0 ∧ deriv zeta z₀ = c * F z₀ ∧ X 0 = z₀ ∧
      (fun z => (z - z₀) * deriv zeta z ^ 2) =ᶠ[𝓝 z₀] (fun z => c * F z * zeta z) ∧
      (fun y => zeta (X y)) =ᶠ[𝓝 0] id ∧ (fun z => X (zeta z)) =ᶠ[𝓝 z₀] id := by
  sorry

/-- The nonzero coordinate derivative has an analytic inverse-square-root
amplitude with its branch fixed at the reference point. Olver,
Chapter 10, §1, pp. 362–363. -/
theorem exists_analytic_liouville_coordinate_amplitude {zeta : ℂ → ℂ} {z₀ a₀ : ℂ}
    (hzeta : AnalyticAt ℂ zeta z₀) (hne : deriv zeta z₀ ≠ 0)
    (ha₀ : a₀ ^ 2 * deriv zeta z₀ = 1) :
    ∃ amplitude : ℂ → ℂ, AnalyticAt ℂ amplitude z₀ ∧ amplitude z₀ = a₀ ∧
      (fun z => amplitude z ^ 2 * deriv zeta z) =ᶠ[𝓝 z₀] 1 := by
  sorry

/-- The transformed simple-pole equation retains the double-pole coefficient
`G(z0)` and has an analytic remaining numerator `Psi`. Thus the canonical
potential is `u^2/(c*zeta)+G(z0)/zeta^2+Psi(zeta)/zeta`; taking
`G(z0)=(nu^2-1)/4,c=4` is the Chapter12 normalization.
Olver, Chapter 12, §2, pp. 438–440. -/
theorem exists_analytic_simplePole_liouville_perturbation
    {G zeta X amplitude : ℂ → ℂ} {z₀ : ℂ}
    (hG : AnalyticAt ℂ G z₀) (hzeta : AnalyticAt ℂ zeta z₀)
    (hX : AnalyticAt ℂ X 0) (hzero : zeta z₀ = 0) (hne : deriv zeta z₀ ≠ 0)
    (hinverse : (fun y => zeta (X y)) =ᶠ[𝓝 0] id) (hXzero : X 0 = z₀)
    (hamp : AnalyticAt ℂ amplitude z₀)
    (hroot : (fun z => amplitude z ^ 2 * deriv zeta z) =ᶠ[𝓝 z₀] 1) :
    ∃ Ψ : ℂ → ℂ, AnalyticAt ℂ Ψ 0 ∧
      (fun z => zeta z * ((G z / (z - z₀) ^ 2 -
        deriv (deriv amplitude) z / amplitude z) / deriv zeta z ^ 2 - G z₀ / zeta z ^ 2))
        =ᶠ[𝓝[≠] z₀] fun z => Ψ (zeta z) := by
  sorry

end Complex

namespace Real

/-- Real analytic simple-pole data admit the increasing real coordinate and a
real analytic inverse. The normalized derivative is `c*F(x0)>0`.
Olver, Chapter 12, §2, pp. 438–440; `c=4` is its Bessel normalization. -/
theorem exists_analytic_simplePole_liouville_coordinate {F : ℝ → ℝ} {x₀ c : ℝ}
    (hF : AnalyticAt ℝ F x₀) (hFpositive : 0 < F x₀) (hc : 0 < c) :
    ∃ zeta X : ℝ → ℝ, AnalyticAt ℝ zeta x₀ ∧ AnalyticAt ℝ X 0 ∧
      zeta x₀ = 0 ∧ deriv zeta x₀ = c * F x₀ ∧ X 0 = x₀ ∧
      (fun x => (x - x₀) * deriv zeta x ^ 2) =ᶠ[𝓝 x₀] (fun x => c * F x * zeta x) ∧
      (fun y => zeta (X y)) =ᶠ[𝓝 0] id ∧ (fun x => X (zeta x)) =ᶠ[𝓝 x₀] id ∧
      ∀ᶠ x in 𝓝 x₀, 0 < deriv zeta x := by
  sorry

/-- The real simple-pole coordinate retains the exponent coefficient and an
analytic complex-valued perturbation through zero. Taking `c=4` and
`G(x0)=(nu^2-1)/4` gives the canonical simple-pole Bessel equation.
Olver, Chapter 12, §2, pp. 438–440. -/
theorem exists_analytic_simplePole_liouville_data {F : ℝ → ℝ} {G : ℝ → ℂ} {x₀ c : ℝ}
    (hF : AnalyticAt ℝ F x₀) (hFpositive : 0 < F x₀) (hG : AnalyticAt ℝ G x₀)
    (hc : 0 < c) :
    ∃ zeta X : ℝ → ℝ, ∃ Ψ : ℝ → ℂ,
      AnalyticAt ℝ zeta x₀ ∧ AnalyticAt ℝ X 0 ∧ AnalyticAt ℝ Ψ 0 ∧
      zeta x₀ = 0 ∧ deriv zeta x₀ = c * F x₀ ∧ X 0 = x₀ ∧
      (fun x => (x - x₀) * deriv zeta x ^ 2) =ᶠ[𝓝 x₀] (fun x => c * F x * zeta x) ∧
      (fun y => zeta (X y)) =ᶠ[𝓝 0] id ∧ (fun x => X (zeta x)) =ᶠ[𝓝 x₀] id ∧
      let amplitude := fun x => deriv zeta x ^ (-1 / 2 : ℝ)
      (fun x => (zeta x : ℂ) * ((G x / (x - x₀ : ℝ) ^ 2 -
        (deriv (deriv amplitude) x / amplitude x : ℝ)) / (deriv zeta x : ℝ) ^ 2 -
          G x₀ / (zeta x : ℝ) ^ 2)) =ᶠ[𝓝[≠] x₀] fun x => Ψ (zeta x) := by
  sorry

end Real
