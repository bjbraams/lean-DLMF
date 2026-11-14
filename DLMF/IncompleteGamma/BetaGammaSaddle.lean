/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.BetaAsymptotics
public import DLMFMathlib.Analysis.Analytic.QuadraticInverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The beta-to-gamma saddle contour and complete coefficient algorithm

Temme, *Special Functions* (1996), Chapter 11, equations (11.47)–(11.58),
pages 295–297. The inverse branch is fixed at the saddle and continued along the
explicit Hankel deformation. The coefficients are its actual Taylor derivatives;
the exact finite-truncation remainder retains the contour integral and its norm bound.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Finset Polynomial
open scoped Topology Real

namespace DLMF.Statistical

/-- The constant matching the beta and gamma saddle phases, Temme (11.48), TEM-11-15. -/
def Real.betaGammaPhaseConstant (μ : ℝ) : ℝ :=
  (1 + μ) * _root_.Real.log (1 + μ) - μ

/-- The principal beta saddle phase, Temme (11.47), synopsis TEM-11-15. -/
def betaGammaBetaPhase (μ : ℝ) (t : ℂ) : ℂ := -log t - μ * log (1 - t)

/-- The principal gamma saddle phase, Temme (11.47), synopsis TEM-11-15. -/
def betaGammaGammaPhase (μ : ℝ) (s : ℂ) : ℂ := s - μ * log s

/-- The branch of the inverse phase map whose real derivative is negative at the saddle.
Temme (11.47)–(11.49), synopsis TEM-11-15. -/
def betaGammaLocalInverse (μ : ℝ) : ℂ → ℂ :=
  analyticSaddleMap (betaGammaBetaPhase μ) (betaGammaGammaPhase μ)
    μ (1 / (1 + μ)) (-((1 + μ) ^ (-(3 / 2 : ℝ)) : ℝ))

/-- The upward Hankel deformation through `μ`, with the removable value at zero
provided by `sinc 0 = 1`. Temme (11.50)–(11.51), synopsis TEM-11-15. -/
def betaGammaHankelPoint (μ θ : ℝ) : ℂ :=
  (μ / _root_.Real.sinc θ : ℝ) * exp (I * θ)

/-- A continuation of the normalized inverse germ along the specified Hankel contour
and positive axis. The principal phase equation and the germ fix its branch.
Temme (11.47)–(11.51), synopsis TEM-11-15. -/
def IsBetaGammaContinuation (μ : ℝ) (t : ℂ → ℂ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧
    (∀ θ ∈ Ioo (-π) π, betaGammaHankelPoint μ θ ∈ U) ∧
    (∀ s : ℝ, 0 < s → (s : ℂ) ∈ U) ∧ AnalyticOnNhd ℂ t U ∧
    (∀ s ∈ U, t s ∈ slitPlane ∧ 1 - t s ∈ slitPlane ∧
      betaGammaBetaPhase μ (t s) = betaGammaGammaPhase μ s +
        Real.betaGammaPhaseConstant μ) ∧
    t =ᶠ[𝓝 (μ : ℂ)] betaGammaLocalInverse μ

/-- The analytic continuation of the normalized saddle inverse.
Only its values and derivatives on the prescribed continuation domain are used.
Temme (11.47)–(11.51), synopsis TEM-11-15. -/
def betaGammaContinuation (μ : ℝ) : ℂ → ℂ :=
  Classical.epsilon (IsBetaGammaContinuation μ)

/-- The pole-subtracted amplitude of the beta-to-gamma contour, filled by its
removable limit at `s=η`. Temme (11.50)–(11.53), synopsis TEM-11-15. -/
def betaGammaAmplitude (μ x : ℝ) (s : ℂ) : ℂ :=
  let η := Real.betaZeta μ x
  let raw := fun z : ℂ => z * (deriv (betaGammaContinuation μ) z /
    (betaGammaContinuation μ z - x) - (z - η)⁻¹)
  if s = η then limUnder (𝓝[≠] s) raw else raw s

/-- The actual Taylor coefficient `h_n=h⁽ⁿ⁾(μ)/n!`.
Temme (11.53), synopsis TEM-11-15. -/
def betaGammaContourCoefficient (n : ℕ) (μ x : ℝ) : ℂ :=
  iteratedDeriv n (betaGammaAmplitude μ x) μ / n.factorial

/-- The explicit falling-factorial polynomial `Φ_n(q)`.
Temme (11.54)–(11.58), synopsis TEM-11-15; the corrected value is `Φ₂=-q`. -/
def betaGammaMomentCoefficient (n : ℕ) (q : ℂ) : ℂ :=
  ∑ j ∈ range (n + 1), (n.choose j : ℂ) * (-q) ^ (n - j) *
    (descPochhammer ℂ j).eval q

/-- The pullback of `e^(ps)s^(-q-1)` times an amplitude along the actual Hankel curve.
Temme (11.50)–(11.58), synopsis TEM-11-15. -/
def betaGammaContourKernel (p q μ : ℝ) (h : ℂ → ℂ) (θ : ℝ) : ℂ :=
  let s := betaGammaHankelPoint μ θ
  exp (p * s) * s ^ (-(q : ℂ) - 1) * h s * deriv (betaGammaHankelPoint μ) θ

/-- The exact transformed prefactor, Temme (11.50), synopsis TEM-11-15. -/
def betaGammaContourPrefactor (p q x : ℝ) : ℂ :=
  (x : ℂ) ^ (p : ℂ) * (1 - x : ℂ) ^ (q : ℂ) *
    exp (p * Real.betaGammaPhaseConstant (q / p))

/-- The defining phase-matching constant. -/
theorem Real.betaGammaPhaseConstant_def (μ : ℝ) :
    Real.betaGammaPhaseConstant μ = (1 + μ) * _root_.Real.log (1 + μ) - μ := rfl

/-- The defining pair of principal saddle phases. -/
theorem betaGammaBetaPhase_def (μ : ℝ) (t : ℂ) :
    betaGammaBetaPhase μ t = -log t - μ * log (1 - t) := rfl

/-- The defining gamma phase. -/
theorem betaGammaGammaPhase_def (μ : ℝ) (s : ℂ) :
    betaGammaGammaPhase μ s = s - μ * log s := rfl

/-- The defining normalized inverse germ. -/
theorem betaGammaLocalInverse_def (μ : ℝ) :
    betaGammaLocalInverse μ = analyticSaddleMap (betaGammaBetaPhase μ)
      (betaGammaGammaPhase μ) μ (1 / (1 + μ))
        (-((1 + μ) ^ (-(3 / 2 : ℝ)) : ℝ)) := rfl

/-- The defining Hankel parametrization, including its removable central value. -/
theorem betaGammaHankelPoint_def (μ θ : ℝ) :
    betaGammaHankelPoint μ θ = (μ / _root_.Real.sinc θ : ℝ) * exp (I * θ) := rfl

/-- Introduction and elimination conditions for the normalized continuation. -/
theorem isBetaGammaContinuation_iff (μ : ℝ) (t : ℂ → ℂ) :
    IsBetaGammaContinuation μ t ↔
      ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧
        (∀ θ ∈ Ioo (-π) π, betaGammaHankelPoint μ θ ∈ U) ∧
        (∀ s : ℝ, 0 < s → (s : ℂ) ∈ U) ∧ AnalyticOnNhd ℂ t U ∧
        (∀ s ∈ U, t s ∈ slitPlane ∧ 1 - t s ∈ slitPlane ∧
          betaGammaBetaPhase μ (t s) = betaGammaGammaPhase μ s +
            Real.betaGammaPhaseConstant μ) ∧
        t =ᶠ[𝓝 (μ : ℂ)] betaGammaLocalInverse μ := Iff.rfl

/-- The defining choice of the normalized analytic continuation. -/
theorem betaGammaContinuation_def (μ : ℝ) :
    betaGammaContinuation μ = Classical.epsilon (IsBetaGammaContinuation μ) := rfl

/-- The defining pole-subtracted amplitude. -/
theorem betaGammaAmplitude_def (μ x : ℝ) (s : ℂ) :
    betaGammaAmplitude μ x s =
      let η := Real.betaZeta μ x
      let raw := fun z : ℂ => z * (deriv (betaGammaContinuation μ) z /
        (betaGammaContinuation μ z - x) - (z - η)⁻¹)
      if s = η then limUnder (𝓝[≠] s) raw else raw s := rfl

/-- The defining Taylor-derivative algorithm. -/
theorem betaGammaContourCoefficient_def (n : ℕ) (μ x : ℝ) :
    betaGammaContourCoefficient n μ x =
      iteratedDeriv n (betaGammaAmplitude μ x) μ / n.factorial := rfl

/-- The defining finite falling-factorial expression. -/
theorem betaGammaMomentCoefficient_def (n : ℕ) (q : ℂ) :
    betaGammaMomentCoefficient n q =
      ∑ j ∈ range (n + 1), (n.choose j : ℂ) * (-q) ^ (n - j) *
        (descPochhammer ℂ j).eval q := rfl

/-- The defining pullback of the Hankel integrand. -/
theorem betaGammaContourKernel_def (p q μ : ℝ) (h : ℂ → ℂ) (θ : ℝ) :
    betaGammaContourKernel p q μ h θ =
      let s := betaGammaHankelPoint μ θ
      exp (p * s) * s ^ (-(q : ℂ) - 1) * h s *
        deriv (betaGammaHankelPoint μ) θ := rfl

/-- The defining transformed prefactor. -/
theorem betaGammaContourPrefactor_def (p q x : ℝ) :
    betaGammaContourPrefactor p q x =
      (x : ℂ) ^ (p : ℂ) * (1 - x : ℂ) ^ (q : ℂ) *
        exp (p * Real.betaGammaPhaseConstant (q / p)) := rfl

/-- The normalized local phase map exists with its prescribed decreasing branch.
Temme (11.47)–(11.49), synopsis TEM-11-15. -/
theorem betaGammaLocalInverse_spec {μ : ℝ} (hμ : 0 < μ) :
    IsAnalyticSaddleMap (betaGammaBetaPhase μ) (betaGammaGammaPhase μ)
      μ (1 / (1 + μ)) (-((1 + μ) ^ (-(3 / 2 : ℝ)) : ℝ))
      (betaGammaLocalInverse μ) := by
  sorry

/-- The normalized saddle germ continues along the specified Hankel deformation.
Temme (11.47)–(11.51), synopsis TEM-11-15. -/
theorem exists_isBetaGammaContinuation {μ : ℝ} (hμ : 0 < μ) :
    ∃ t : ℂ → ℂ, IsBetaGammaContinuation μ t := by
  sorry

/-- The canonical continuation has its defining branch, phase and analytic domain.
Temme (11.47)–(11.51), synopsis TEM-11-15. -/
theorem betaGammaContinuation_spec {μ : ℝ} (hμ : 0 < μ) :
    IsBetaGammaContinuation μ (betaGammaContinuation μ) := by
  exact Classical.epsilon_spec (exists_isBetaGammaContinuation hμ)

/-- The complex continuation restricts to the canonical decreasing real inverse.
Temme (11.47)–(11.49), synopsis TEM-11-15. -/
theorem betaGammaContinuation_ofReal {μ s : ℝ} (hμ : 0 < μ) (hs : 0 < s) :
    betaGammaContinuation μ s = (Real.betaGeneralX μ s : ℂ) := by
  sorry

/-- The real phase coordinate decreases bijectively from `(0,1)` onto `(0,∞)`.
Temme (11.47)–(11.49), synopsis TEM-11-15. -/
theorem Real.betaZeta_strictAntiOn_bijOn {μ : ℝ} (hμ : 0 < μ) :
    StrictAntiOn (Real.betaZeta μ) (Ioo 0 1) ∧
      BijOn (Real.betaZeta μ) (Ioo 0 1) (Ioi 0) := by
  sorry

/-- The derivative at the removable real saddle has the stated negative value.
Temme (11.49), synopsis TEM-11-15. -/
theorem Real.hasDerivAt_betaZeta_saddle {μ : ℝ} (hμ : 0 < μ) :
    HasDerivAt (Real.betaZeta μ) (-((1 + μ) ^ (3 / 2 : ℝ))) (1 / (1 + μ)) := by
  sorry

/-- The derivative away from the saddle follows the explicit phase equation.
Temme (11.49), synopsis TEM-11-15. -/
theorem Real.hasDerivAt_betaZeta {μ x : ℝ} (hμ : 0 < μ)
    (hx : 0 < x) (hx1 : x < 1) (hxs : x ≠ 1 / (1 + μ)) :
    HasDerivAt (Real.betaZeta μ)
      (((1 + μ) * x - 1) * Real.betaZeta μ x /
        (x * (1 - x) * (Real.betaZeta μ x - μ))) x := by
  sorry

/-- The continued amplitude is analytic at the saddle, including the transition.
Temme (11.50)–(11.53), synopsis TEM-11-15. -/
theorem analyticAt_betaGammaAmplitude {μ x : ℝ} (hμ : 0 < μ)
    (hx : 0 < x) (hx1 : x < 1) : AnalyticAt ℂ (betaGammaAmplitude μ x) μ := by
  sorry

/-- The first two moment-polynomial initial conditions.
Temme (11.54)–(11.58), synopsis TEM-11-15. -/
theorem betaGammaMomentCoefficient_initial (q : ℂ) :
    betaGammaMomentCoefficient 0 q = 1 ∧ betaGammaMomentCoefficient 1 q = 0 := by
  simp [betaGammaMomentCoefficient, sum_range_succ]

/-- The complete moment-polynomial recursion, including the corrected sign of `Φ₂`.
Temme (11.54)–(11.58), synopsis TEM-11-15. -/
theorem betaGammaMomentCoefficient_recurrence (n : ℕ) (q : ℂ) :
    betaGammaMomentCoefficient (n + 2) q = -((n : ℂ) + 1) *
      (betaGammaMomentCoefficient (n + 1) q + q * betaGammaMomentCoefficient n q) := by
  sorry

/-- The second moment polynomial is `-q`, correcting the printed value `2q`.
Temme (11.58), synopsis TEM-11-15 and erratum TEM-E11. -/
@[simp] theorem betaGammaMomentCoefficient_two (q : ℂ) :
    betaGammaMomentCoefficient 2 q = -q := by
  norm_num [betaGammaMomentCoefficient, sum_range_succ, descPochhammer_succ_right]
  ring

/-- Each polynomial-weighted Hankel moment is absolutely integrable.
Temme (11.54)–(11.58), synopsis TEM-11-15. -/
theorem integrableOn_betaGammaContour_monomial {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (n : ℕ) :
    IntegrableOn (betaGammaContourKernel p q (q / p)
      (fun s => (s - q / p) ^ n)) (Ioo (-π) π) := by
  sorry

/-- Exact evaluation of every centered Hankel moment.
Temme (11.54)–(11.58), synopsis TEM-11-15. -/
theorem integral_betaGammaContour_monomial {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (n : ℕ) :
    (2 * π * I : ℂ)⁻¹ * (∫ θ in Ioo (-π) π,
      betaGammaContourKernel p q (q / p) (fun s => (s - q / p) ^ n) θ) =
        (p : ℂ) ^ (q : ℂ) / (Gamma (q + 1) * (p : ℂ) ^ n) *
          betaGammaMomentCoefficient n q := by
  sorry

/-- The exact finite Taylor remainder of the continued amplitude is contour-integrable.
Temme (11.50)–(11.58), synopsis TEM-11-15. -/
theorem integrableOn_betaGammaContour_taylor_remainder {p q x : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) (hx1 : x < 1) (N : ℕ) :
    IntegrableOn (betaGammaContourKernel p q (q / p) (fun s =>
      betaGammaAmplitude (q / p) x s - ∑ n ∈ range N,
        betaGammaContourCoefficient n (q / p) x * (s - q / p) ^ n)) (Ioo (-π) π) := by
  sorry

/-- The gamma term and exact finite Taylor-remainder contour represent the beta ratio.
Temme (11.50)–(11.58), synopsis TEM-11-15. No variable-parameter asymptotic scale is assumed. -/
theorem regularizedIncompleteBeta_eq_gamma_sub_finite_contour {p q x : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) (hx1 : x < 1) (N : ℕ) :
    regularizedIncompleteBeta p q x =
      DLMF.Confluent.regularizedIncompleteGammaQ q (p * Real.betaZeta (q / p) x) -
        betaGammaContourPrefactor p q x * (p : ℂ) ^ (q : ℂ) / Gamma (q + 1) *
          (∑ n ∈ range N, betaGammaContourCoefficient n (q / p) x *
            betaGammaMomentCoefficient n q / (p : ℂ) ^ n) -
        betaGammaContourPrefactor p q x / (2 * π * I) *
          ∫ θ in Ioo (-π) π, betaGammaContourKernel p q (q / p) (fun s =>
            betaGammaAmplitude (q / p) x s - ∑ n ∈ range N,
              betaGammaContourCoefficient n (q / p) x * (s - q / p) ^ n) θ := by
  sorry

/-- The finite-truncation error is bounded by the integral of the actual contour
remainder's norm, uniformly as an exact identity for every positive pair `p,q`.
Temme (11.50)–(11.58), synopsis TEM-11-15. -/
theorem norm_regularizedIncompleteBeta_sub_gamma_sum_le_contour {p q x : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) (hx1 : x < 1) (N : ℕ) :
    ‖regularizedIncompleteBeta p q x -
      DLMF.Confluent.regularizedIncompleteGammaQ q (p * Real.betaZeta (q / p) x) +
        betaGammaContourPrefactor p q x * (p : ℂ) ^ (q : ℂ) / Gamma (q + 1) *
          (∑ n ∈ range N, betaGammaContourCoefficient n (q / p) x *
            betaGammaMomentCoefficient n q / (p : ℂ) ^ n)‖ ≤
      ‖betaGammaContourPrefactor p q x‖ / (2 * π) *
        ∫ θ in Ioo (-π) π, ‖betaGammaContourKernel p q (q / p) (fun s =>
          betaGammaAmplitude (q / p) x s - ∑ n ∈ range N,
            betaGammaContourCoefficient n (q / p) x * (s - q / p) ^ n) θ‖ := by
  sorry

end DLMF.Statistical
