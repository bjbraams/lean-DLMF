/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Weighted derivative-coupled Volterra equations on oriented paths

Olver, *Asymptotics and Special Functions*, Chapter 6, §10.2 and Theorems
10.1–10.2, pp. 218–220, synopsis O-6.14–O-6.16. Extended-real parameter
endpoints allow finite and improper paths. The kernel jet is differentiated with
respect to the path coordinate, so its weights retain the source's normalizations
under reparametrization. Finitely many corners or improper coefficient points
are allowed; integration hypotheses retain their actual absolute arc-length weights.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace ODE.WeightedVolterra

/-- The real parameter interval between finite or infinite endpoints. -/
def interval (a b : EReal) : Set ℝ := {t | a < (t : EReal) ∧ (t : EReal) < b}

/-- The initial part of an oriented path parameter interval, excluding its initial end. -/
def initialSegment (a : EReal) (t : ℝ) : Set ℝ := {s | a < (s : EReal) ∧ s ≤ t}

/-- Membership in the extended-endpoint interval. -/
theorem mem_interval_iff (a b : EReal) (t : ℝ) :
    t ∈ interval a b ↔ a < (t : EReal) ∧ (t : EReal) < b := Iff.rfl

/-- Membership in the initial integration segment. -/
theorem mem_initialSegment_iff (a : EReal) (t s : ℝ) :
    s ∈ initialSegment a t ↔ a < (s : EReal) ∧ s ≤ t := Iff.rfl

/-- The actual source kernel, derivative weights and integrable forcing data.
Olver, Chapter 6, §10.2, p. 218, synopsis O-6.14. -/
structure Data (a b : EReal) where
  lower_lt_upper : a < b
  path : ℝ → ℂ
  exceptionalPoints : Finset ℝ
  continuousOn_path : ContinuousOn path (interval a b)
  contDiffOn_path : ContDiffOn ℝ 2 path (interval a b \ exceptionalPoints)
  deriv_path_ne_zero : ∀ t ∈ interval a b \ exceptionalPoints, deriv path t ≠ 0
  kernel : Fin 3 → ℝ → ℝ → ℂ
  weight : Fin 3 → ℝ → ℝ
  inputWeight : ℝ → ℝ
  forcingCoefficient : ℝ → ℂ
  valueCoefficient : ℝ → ℂ
  derivativeCoefficient : ℝ → ℂ
  forcingFunction : ℝ → ℂ
  forcingBound : ℝ
  zeroWeightBound : ℝ
  firstWeightBound : ℝ
  continuousOn_weight : ∀ j, ContinuousOn (weight j) (interval a b)
  weight_pos : ∀ j t, t ∈ interval a b → 0 < weight j t
  continuousOn_inputWeight : ContinuousOn inputWeight (interval a b)
  inputWeight_pos : ∀ t ∈ interval a b, 0 < inputWeight t
  continuousOn_kernel : ∀ j, ContinuousOn (Function.uncurry (kernel j))
    {p | p.1 ∈ interval a b ∧ p.2 ∈ interval a b ∧ p.2 ≤ p.1}
  hasDerivWithinAt_kernel : ∀ (j : Fin 2) t s,
    t ∈ interval a b \ exceptionalPoints → s ∈ interval a b → s ≤ t →
    HasDerivWithinAt (fun u => kernel j.castSucc u s)
      (deriv path t * kernel j.succ t s) (Ici s ∩ interval a b) t
  kernel_diagonal : ∀ t ∈ interval a b, kernel 0 t t = 0
  kernel_bound : ∀ j t s, t ∈ interval a b → s ∈ interval a b → s ≤ t →
    ‖kernel j t s‖ ≤ weight j t * inputWeight s
  forcingBound_nonneg : 0 ≤ forcingBound
  zeroWeightBound_nonneg : 0 ≤ zeroWeightBound
  firstWeightBound_nonneg : 0 ≤ firstWeightBound
  forcing_bound : ∀ t ∈ interval a b, inputWeight t * ‖forcingFunction t‖ ≤ forcingBound
  zeroWeight_bound : ∀ t ∈ interval a b, weight 0 t * inputWeight t ≤ zeroWeightBound
  firstWeight_bound : ∀ t ∈ interval a b, weight 1 t * inputWeight t ≤ firstWeightBound
  continuousOn_coefficients : ∀ f ∈
    ({forcingCoefficient, valueCoefficient, derivativeCoefficient, forcingFunction} :
      Set (ℝ → ℂ)), ContinuousOn f (interval a b \ exceptionalPoints)
  integrableOn_coefficients : ∀ f ∈
    ({forcingCoefficient, valueCoefficient, derivativeCoefficient} : Set (ℝ → ℂ)),
    ∀ t ∈ interval a b,
      IntegrableOn (fun s => ‖f s‖ * ‖deriv path s‖) (initialSegment a t)

namespace Data

variable {a b : EReal}

/-- The absolute arc-length primitive of one coefficient. -/
def variation (D : Data a b) (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  ∫ s : ℝ in initialSegment a t, ‖f s‖ * ‖deriv D.path s‖

/-- The defining arc-length primitive. -/
theorem variation_def (D : Data a b) (f : ℝ → ℂ) (t : ℝ) :
    D.variation f t = ∫ s : ℝ in initialSegment a t, ‖f s‖ * ‖deriv D.path s‖ := rfl

/-- The two integral components of the Volterra value and path-derivative jet. -/
def transform (D : Data a b) (H : ℝ → ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  (∫ s : ℝ in initialSegment a t, D.kernel 0 t s *
      (D.forcingCoefficient s * D.forcingFunction s +
        D.valueCoefficient s * (H s).1 + D.derivativeCoefficient s * (H s).2) * deriv D.path s,
    ∫ s : ℝ in initialSegment a t, D.kernel 1 t s *
      (D.forcingCoefficient s * D.forcingFunction s +
        D.valueCoefficient s * (H s).1 + D.derivativeCoefficient s * (H s).2) * deriv D.path s)

/-- The actual two integral equations defining the transform. -/
theorem transform_def (D : Data a b) (H : ℝ → ℂ × ℂ) (t : ℝ) :
    D.transform H t =
      (∫ s : ℝ in initialSegment a t, D.kernel 0 t s *
        (D.forcingCoefficient s * D.forcingFunction s +
          D.valueCoefficient s * (H s).1 + D.derivativeCoefficient s * (H s).2) * deriv D.path s,
      ∫ s : ℝ in initialSegment a t, D.kernel 1 t s *
        (D.forcingCoefficient s * D.forcingFunction s +
          D.valueCoefficient s * (H s).1 + D.derivativeCoefficient s * (H s).2) *
            deriv D.path s) := rfl

/-- Successive Volterra approximations, starting with zero errors.
Olver, Chapter 6, Theorem 10.1, synopsis O-6.15. -/
def iterate (D : Data a b) : ℕ → ℝ → ℂ × ℂ
  | 0 => fun _ => 0
  | n + 1 => D.transform (D.iterate n)

/-- Initial zero approximation. -/
@[simp] theorem iterate_zero (D : Data a b) : D.iterate 0 = fun _ => 0 := rfl

/-- The Volterra iteration recurrence. -/
theorem iterate_succ (D : Data a b) (n : ℕ) :
    D.iterate (n + 1) = D.transform (D.iterate n) := rfl

/-- The exact normalized solution-jet conditions, including both endpoint limits.
Olver, Chapter 6, Theorem 10.1, synopsis O-6.15. -/
def IsSolution (D : Data a b) (H : ℝ → ℂ × ℂ) : Prop :=
  ContinuousOn H (interval a b) ∧
  (∀ t ∈ interval a b, H t = D.transform H t) ∧
  (∀ t ∈ interval a b \ D.exceptionalPoints,
    HasDerivAt (fun s => (H s).1) (deriv D.path t * (H t).2) t) ∧
  DifferentiableOn ℝ (fun t => (H t).2) (interval a b \ D.exceptionalPoints) ∧
  Tendsto (fun t => (H t).1 / D.weight 0 t)
    (comap (fun t : ℝ => (t : EReal)) (𝓝 a) ⊓ 𝓟 (interval a b)) (𝓝 0) ∧
  Tendsto (fun t => (H t).2 / D.weight 1 t)
    (comap (fun t : ℝ => (t : EReal)) (𝓝 a) ⊓ 𝓟 (interval a b)) (𝓝 0)

/-- The defining fixed-point, path-derivative and endpoint conditions. -/
theorem isSolution_iff (D : Data a b) (H : ℝ → ℂ × ℂ) : D.IsSolution H ↔
    ContinuousOn H (interval a b) ∧
    (∀ t ∈ interval a b, H t = D.transform H t) ∧
    (∀ t ∈ interval a b \ D.exceptionalPoints,
      HasDerivAt (fun s => (H s).1) (deriv D.path t * (H t).2) t) ∧
    DifferentiableOn ℝ (fun t => (H t).2) (interval a b \ D.exceptionalPoints) ∧
    Tendsto (fun t => (H t).1 / D.weight 0 t)
      (comap (fun t : ℝ => (t : EReal)) (𝓝 a) ⊓ 𝓟 (interval a b)) (𝓝 0) ∧
    Tendsto (fun t => (H t).2 / D.weight 1 t)
      (comap (fun t : ℝ => (t : EReal)) (𝓝 a) ⊓ 𝓟 (interval a b)) (𝓝 0) := Iff.rfl

/-- The exact Neumann factorial estimate for both value and path-derivative iterates.
Olver, Chapter 6, Theorem 10.1, (10.06), pp. 219–220, synopsis O-6.15. -/
theorem norm_iterate_succ_sub_le (D : Data a b) (n : ℕ) {t : ℝ}
    (ht : t ∈ interval a b) :
    let B := D.zeroWeightBound * D.variation D.valueCoefficient t +
      D.firstWeightBound * D.variation D.derivativeCoefficient t
    ‖(D.iterate (n + 1) t).1 - (D.iterate n t).1‖ / D.weight 0 t ≤
      D.forcingBound * D.variation D.forcingCoefficient t * B ^ n / n.factorial ∧
    ‖(D.iterate (n + 1) t).2 - (D.iterate n t).2‖ / D.weight 1 t ≤
      D.forcingBound * D.variation D.forcingCoefficient t * B ^ n / n.factorial := by
  sorry

/-- The unique normalized Volterra solution, its explicit two-component error bound,
and compact-uniform convergence of the actual successive approximations. Uniqueness
is equality on the interval, since values outside it are immaterial.
Olver, Chapter 6, Theorem 10.1, pp. 219–220, synopsis O-6.15. -/
theorem existsUnique_isSolution (D : Data a b) :
    ∃ H : ℝ → ℂ × ℂ, D.IsSolution H ∧
      (∀ G : ℝ → ℂ × ℂ, D.IsSolution G → EqOn G H (interval a b)) ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ interval a b →
        TendstoUniformlyOn D.iterate H atTop K) ∧
      ∀ t ∈ interval a b,
        let B := D.zeroWeightBound * D.variation D.valueCoefficient t +
          D.firstWeightBound * D.variation D.derivativeCoefficient t
        ‖(H t).1‖ / D.weight 0 t ≤
          D.forcingBound * D.variation D.forcingCoefficient t * Real.exp B ∧
        ‖(H t).2‖ / D.weight 1 t ≤
          D.forcingBound * D.variation D.forcingCoefficient t * Real.exp B := by
  sorry

end Data

/-- The removable self-forcing majorant, including its zero coefficient value.
Olver, Chapter 6, Theorem 10.2, p. 220, synopsis O-6.16. -/
def selfForcingBound (κ κ₀ Φ : ℝ) : ℝ :=
  if κ₀ = 0 then κ * Φ else κ / κ₀ * (Real.exp (κ₀ * Φ) - 1)

/-- The two cases defining the self-forcing estimate. -/
theorem selfForcingBound_def (κ κ₀ Φ : ℝ) : selfForcingBound κ κ₀ Φ =
    if κ₀ = 0 then κ * Φ else κ / κ₀ * (Real.exp (κ₀ * Φ) - 1) := rfl

/-- The explicitly retained continuous value when the zero-weight coefficient vanishes. -/
@[simp] theorem selfForcingBound_zero (κ Φ : ℝ) : selfForcingBound κ 0 Φ = κ * Φ := by
  simp only [selfForcingBound, ↓reduceIte]

/-- The zero-coefficient interpretation is the limit of the full quotient.
Olver, Chapter 6, Theorem 10.2, synopsis O-6.16. -/
theorem tendsto_selfForcingBound_zero (κ Φ : ℝ) :
    Tendsto (fun κ₀ => selfForcingBound κ κ₀ Φ) (𝓝 0) (𝓝 (κ * Φ)) := by
  sorry

/-- The sharper bound for arbitrary derivative-free self-forcing kernels, not only
Green kernels arising from a fundamental solution pair.
Olver, Chapter 6, Theorem 10.2, p. 220, synopsis O-6.16. -/
theorem Data.norm_isSolution_le_selfForcingBound {a b : EReal} (D : Data a b)
    (hself : D.forcingCoefficient = D.valueCoefficient)
    (hderiv : D.derivativeCoefficient = fun _ => 0) {H : ℝ → ℂ × ℂ}
    (hH : D.IsSolution H) {t : ℝ} (ht : t ∈ interval a b) :
    ‖(H t).1‖ / D.weight 0 t ≤
        selfForcingBound D.forcingBound D.zeroWeightBound (D.variation D.forcingCoefficient t) ∧
      ‖(H t).2‖ / D.weight 1 t ≤
        selfForcingBound D.forcingBound D.zeroWeightBound
          (D.variation D.forcingCoefficient t) := by
  sorry

end ODE.WeightedVolterra
