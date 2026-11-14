/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import DLMF.Airy.Basic
public import DLMFMathlib.Analysis.ODE.TurningPointCoefficients
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Data.Set.Function

/-!
# Large-order Bessel expansions through the turning point

The action coordinate is an actual weighted integral on the principal slit plane.
Its removable ratio at one fixes every branch without taking a fractional power
of an action on the wrong sheet. The four cylinder functions are identified
separately, preserving the recessive Hankel error. Source: Olver,
*Asymptotics and Special Functions*, Chapter 11, §10, pp. 419–426.
-/

@[expose] public noncomputable section

open Complex ODE Set Filter Finset
open scoped Real Topology

namespace DLMF.Bessel.TurningPoint

/-- The analytic weighted action ratio before its `2/3` power.
Olver, Chapter 11, (10.03)–(10.05), pp. 420–421. -/
def actionRatio (z : ℂ) : ℂ :=
  (3 / 2 : ℂ) * ∫ t : ℝ in 0..1,
    (Real.sqrt t : ℂ) * sqrt (2 + t * (z - 1)) / (1 + t * (z - 1))

/-- The defining weighted action integral. -/
theorem actionRatio_def (z : ℂ) : actionRatio z =
    (3 / 2 : ℂ) * ∫ t : ℝ in 0..1,
      (Real.sqrt t : ℂ) * sqrt (2 + t * (z - 1)) / (1 + t * (z - 1)) := rfl

/-- The principal Bessel turning-point coordinate, positive for `0<z<1` and
negative for `z>1`, with the analytic removable value zero at one.
Olver, Chapter 11, (10.03), (10.07), pp. 420–421. -/
def coordinate (z : ℂ) : ℂ := (1 - z) * actionRatio z ^ (2 / 3 : ℂ)

/-- The defining removable action ratio. -/
theorem coordinate_def (z : ℂ) : coordinate z = (1 - z) * actionRatio z ^ (2 / 3 : ℂ) := rfl

/-- The cylinder-function prefactor `(4*zeta/(1-z^2))^(1/4)`, expressed without
a zero denominator at one. All powers have their principal analytic branches.
Olver, Chapter 11, (10.17)–(10.20), pp. 422–423. -/
def prefactor (z : ℂ) : ℂ :=
  (Real.sqrt 2 : ℂ) * actionRatio z ^ (1 / 6 : ℂ) / (1 + z) ^ (1 / 4 : ℂ)

/-- The defining removable prefactor. -/
theorem prefactor_def (z : ℂ) : prefactor z =
    (Real.sqrt 2 : ℂ) * actionRatio z ^ (1 / 6 : ℂ) / (1 + z) ^ (1 / 4 : ℂ) := rfl

/-- The Liouville amplitude for the normal equation satisfied by `sqrt(z)*C_nu`.
Olver, Chapter 11, §10, p. 420. -/
def amplitude (z : ℂ) : ℂ := sqrt z * prefactor z / (Real.sqrt 2 : ℂ)

/-- The defining amplitude branch. -/
theorem amplitude_def (z : ℂ) : amplitude z = sqrt z * prefactor z / (Real.sqrt 2 : ℂ) := rfl

/-- The analytic transformed perturbation, evaluated with the actual inverse
coordinate and nonsingular amplitude formula. Olver, Chapter 11, (10.06), p. 420. -/
def perturbation (ζ : ℂ) : ℂ :=
  let z := Function.invFunOn coordinate slitPlane ζ
  (-1 / (4 * z ^ 2) - deriv (deriv amplitude) z / amplitude z) / deriv coordinate z ^ 2

/-- The defining nonsingular transformed perturbation. -/
theorem perturbation_def (ζ : ℂ) : perturbation ζ =
    let z := Function.invFunOn coordinate slitPlane ζ
    (-1 / (4 * z ^ 2) - deriv (deriv amplitude) z / amplitude z) / deriv coordinate z ^ 2 := rfl

/-- The coordinate and prefactor are analytic on the full slit plane, with
nonzero removable ratios, analytic inverse and exact action identities on both
positive real regimes. Olver, Chapter 11, §10, pp. 420–421. -/
theorem coordinate_properties :
    AnalyticOnNhd ℂ coordinate slitPlane ∧ AnalyticOnNhd ℂ prefactor slitPlane ∧
      AnalyticOnNhd ℂ perturbation (coordinate '' slitPlane) ∧
      InjOn coordinate slitPlane ∧ IsOpen (coordinate '' slitPlane) ∧
      IsSimplyConnected (coordinate '' slitPlane) ∧
      AnalyticOnNhd ℂ (Function.invFunOn coordinate slitPlane) (coordinate '' slitPlane) ∧
      coordinate 1 = 0 ∧ deriv coordinate 1 = -(2 : ℂ) ^ (1 / 3 : ℂ) ∧
      prefactor 1 = (2 : ℂ) ^ (1 / 3 : ℂ) ∧
      (∀ z ∈ slitPlane, actionRatio z ∈ slitPlane ∧ prefactor z ≠ 0 ∧
        deriv coordinate z ≠ 0 ∧
        coordinate z * deriv coordinate z ^ 2 = (1 - z ^ 2) / z ^ 2) ∧
      (∀ x : ℝ, 0 < x → x < 1 → 0 < (coordinate x).re ∧ (coordinate x).im = 0 ∧
        (2 / 3 : ℝ) * (coordinate x).re ^ (3 / 2 : ℝ) =
          Real.log ((1 + Real.sqrt (1 - x ^ 2)) / x) - Real.sqrt (1 - x ^ 2)) ∧
      (∀ x : ℝ, 1 < x → (coordinate x).re < 0 ∧ (coordinate x).im = 0 ∧
        (2 / 3 : ℝ) * (-(coordinate x).re) ^ (3 / 2 : ℝ) =
          Real.sqrt (x ^ 2 - 1) - Real.arccos x⁻¹) := by
  sorry

/-- The apparent poles at the turning point cancel in the analytic perturbation.
Olver, Chapter 11, (10.06), p. 420. -/
theorem perturbation_coordinate_eq {z : ℂ} (hz : z ∈ slitPlane) (hz_one : z ≠ 1) :
    perturbation (coordinate z) = 5 / (16 * coordinate z ^ 2) +
      coordinate z * z ^ 2 * (z ^ 2 + 4) / (4 * (z ^ 2 - 1) ^ 3) := by
  sorry

/-- The four separately normalized Airy comparison functions for `J,Y,H1,H2`.
Olver, Chapter 11, (10.17)–(10.20), pp. 422–423. -/
def airyComparison (k : Fin 4) (ζ : ℂ) : ℂ :=
  if k = 0 then DLMF.Airy.airyAi ζ else if k = 1 then -DLMF.Airy.airyBi ζ else
    let σ : ℂ := if k = 2 then 1 else -1
    2 * exp (-σ * Real.pi * I / 3) * DLMF.Airy.airyAi (exp (σ * 2 * Real.pi * I / 3) * ζ)

/-- The defining four comparison branches. -/
theorem airyComparison_def (k : Fin 4) (ζ : ℂ) : airyComparison k ζ =
    if k = 0 then DLMF.Airy.airyAi ζ else if k = 1 then -DLMF.Airy.airyBi ζ else
      let σ : ℂ := if k = 2 then 1 else -1
      2 * exp (-σ * Real.pi * I / 3) * DLMF.Airy.airyAi (exp (σ * 2 * Real.pi * I / 3) * ζ) := rfl

/-- The corresponding four canonical cylinder functions. -/
def cylinder (k : Fin 4) (ν z : ℂ) : ℂ :=
  if k = 0 then besselJ ν z else if k = 1 then besselY ν z else
    if k = 2 then hankelH1 ν z else hankelH2 ν z

/-- The defining cylinder-function selection. -/
theorem cylinder_def (k : Fin 4) (ν z : ℂ) : cylinder k ν z =
    if k = 0 then besselJ ν z else if k = 1 then besselY ν z else
      if k = 2 then hankelH1 ν z else hankelH2 ν z := rfl

/-- The actual two-series finite Airy approximation, with both series truncated
before index `N`. Olver, Chapter 11, (10.17)–(10.20), pp. 422–423. -/
def approximation (A B : ℕ → ℂ → ℂ) (k : Fin 4) (ν : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  let ζ := coordinate z
  let x := (ν ^ (2 / 3 : ℝ) : ℝ) * ζ
  prefactor z * (ν ^ (-1 / 3 : ℝ) : ℝ) *
    (airyComparison k x * ∑ s ∈ range N, A s ζ / (ν : ℂ) ^ (2 * s) +
      (ν ^ (-4 / 3 : ℝ) : ℝ) * deriv (airyComparison k) x *
        ∑ s ∈ range N, B s ζ / (ν : ℂ) ^ (2 * s))

/-- The defining finite compound approximation. -/
theorem approximation_def (A B : ℕ → ℂ → ℂ) (k : Fin 4) (ν : ℝ) (N : ℕ) (z : ℂ) :
    approximation A B k ν N z =
      let ζ := coordinate z
      let x := (ν ^ (2 / 3 : ℝ) : ℝ) * ζ
      prefactor z * (ν ^ (-1 / 3 : ℝ) : ℝ) *
        (airyComparison k x * ∑ s ∈ range N, A s ζ / (ν : ℂ) ^ (2 * s) +
          (ν ^ (-4 / 3 : ℝ) : ℝ) * deriv (airyComparison k) x *
            ∑ s ∈ range N, B s ζ / (ν : ℂ) ^ (2 * s)) := rfl

/-- One common normalized coefficient pair gives all four full expansions and
their derivatives uniformly in every unbounded proper sector of the slit plane.
The majorants include both Airy value and derivative, retaining control at zeros;
each Hankel function has its own recessive comparison rather than a difference
of separately bounded dominant errors. Olver, Chapter 11, §10, pp. 421–426. -/
theorem exists_uniform_cylinder_turningPoint_coefficients :
    ∃ A B : ℕ → ℂ → ℂ,
      IsTurningPointCoefficientSequence perturbation A B (coordinate '' slitPlane) ∧
      (∀ s : ℕ, 0 < s → Tendsto (fun x : ℝ => A s x) atBot (𝓝 0)) ∧
      ∀ (δ : ℝ), 0 < δ → δ < Real.pi → ∀ N : ℕ,
        ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ (ν : ℝ) (z : ℂ) (k : Fin 4),
          R ≤ ν → z ∈ slitPlane → |arg z| ≤ Real.pi - δ →
          let x := (ν ^ (2 / 3 : ℝ) : ℝ) * coordinate z
          let M := ‖airyComparison k x‖ + ‖deriv (airyComparison k) x‖ /
            (1 + Real.sqrt ‖x‖)
          let D := ‖deriv (airyComparison k) x‖ + (1 + Real.sqrt ‖x‖) * ‖airyComparison k x‖
          ‖cylinder k ν (ν * z) - approximation A B k ν N z‖ ≤
            C * ‖prefactor z‖ * M / ν ^ (2 * N + 1 / 3 : ℝ) ∧
          ‖deriv (cylinder k ν) (ν * z) - deriv (approximation A B k ν N) z / ν‖ ≤
            C * (‖deriv prefactor z‖ * M +
              ν ^ (2 / 3 : ℝ) * ‖prefactor z * deriv coordinate z‖ * D) /
                ν ^ (2 * N + 4 / 3 : ℝ) := by
  sorry

end DLMF.Bessel.TurningPoint
