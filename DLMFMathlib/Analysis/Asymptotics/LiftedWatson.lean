/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Watson's lemma on a full lifted sector

Temme, *Special Functions* (1996), Theorem 2.5, pp. 33–34, synopsis TEM-02-07.
The kernel is given on a logarithmic strip, so sectors wider than a single argument
branch are retained. The transform is an actual rotated-ray integral with a specified
ray. Exponential growth is allowed separately on each closed kernel subsector.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set
open scoped Real Topology

namespace Asymptotics.LiftedWatson

/-- The source assumptions for a logarithmic kernel with endpoint exponent `lam`.
The argument of the original variable is the imaginary part of its logarithm.
Temme, Theorem 2.5, synopsis TEM-02-07. -/
structure IsKernel (f : ℂ → ℂ) (a : ℕ → ℂ) (lam : ℂ) (α₁ α₂ : ℝ) : Prop where
  analytic : AnalyticOnNhd ℂ f {v | α₁ < v.im ∧ v.im < α₂}
  expansion : ∀ β₁ β₂ : ℝ, α₁ < β₁ → β₁ ≤ β₂ → β₂ < α₂ →
    HasAsymptoticExpansion
      (comap (fun v : ℂ => v.re) atBot ⊓ 𝓟 {v : ℂ | β₁ ≤ v.im ∧ v.im ≤ β₂})
      (fun (n : ℕ) (v : ℂ) => exp ((lam - 1 + n) * v)) a f
  growth : ∀ β₁ β₂ : ℝ, α₁ < β₁ → β₁ ≤ β₂ → β₂ < α₂ →
    ∃ C : ℝ, 0 < C ∧ ∃ σ R : ℝ, ∀ v : ℂ,
      β₁ ≤ v.im → v.im ≤ β₂ → R ≤ v.re →
        ‖f v‖ ≤ C * _root_.Real.exp (σ * _root_.Real.exp v.re)

/-- The midpoint of the permissible ray-angle interval. This interval is nonempty
exactly on the full continued Laplace sector in the logarithmic argument.
Temme, Theorem 2.5, synopsis TEM-02-07. -/
def rayAngle (α₁ α₂ : ℝ) (w : ℂ) : ℝ :=
  (max α₁ (-_root_.Real.pi / 2 - w.im) +
    min α₂ (_root_.Real.pi / 2 - w.im)) / 2

/-- The actual rotated-ray transform, on the logarithmic argument plane. The ray tangent
is included; outside the convergence domain the Bochner integral is totalized.
Temme, Theorem 2.5, synopsis TEM-02-07. -/
def transform (f : ℂ → ℂ) (α₁ α₂ : ℝ) (w : ℂ) : ℂ :=
  let θ := rayAngle α₁ α₂ w
  exp (I * θ) * ∫ r : ℝ in Ioi 0,
    exp (-exp w * exp (I * θ) * r) * f (log (r : ℂ) + I * θ)

/-- The specified midpoint ray angle. -/
theorem rayAngle_def (α₁ α₂ : ℝ) (w : ℂ) :
    rayAngle α₁ α₂ w =
      (max α₁ (-_root_.Real.pi / 2 - w.im) +
        min α₂ (_root_.Real.pi / 2 - w.im)) / 2 := rfl

/-- The actual defining ray integral, including its tangent. -/
theorem transform_def (f : ℂ → ℂ) (α₁ α₂ : ℝ) (w : ℂ) :
    transform f α₁ α₂ w = exp (I * rayAngle α₁ α₂ w) *
      ∫ r : ℝ in Ioi 0,
        exp (-exp w * exp (I * rayAngle α₁ α₂ w) * r) *
          f (log (r : ℂ) + I * rayAngle α₁ α₂ w) := rfl

/-- The selected ray genuinely lies inside both the kernel sector and the decaying
Laplace half-plane. Temme, Theorem 2.5, synopsis TEM-02-07. -/
theorem rayAngle_mem {α₁ α₂ : ℝ} (hα : α₁ < α₂) {w : ℂ}
    (h₁ : -α₂ - _root_.Real.pi / 2 < w.im)
    (h₂ : w.im < -α₁ + _root_.Real.pi / 2) :
    α₁ < rayAngle α₁ α₂ w ∧ rayAngle α₁ α₂ w < α₂ ∧
      |w.im + rayAngle α₁ α₂ w| < _root_.Real.pi / 2 := by
  unfold rayAngle
  have hπ := _root_.Real.pi_pos
  constructor
  · have := le_max_left α₁ (-_root_.Real.pi / 2 - w.im)
    have hh : α₁ < min α₂ (_root_.Real.pi / 2 - w.im) := lt_min hα (by linarith)
    linarith
  constructor
  · have := min_le_left α₂ (_root_.Real.pi / 2 - w.im)
    have hh : max α₁ (-_root_.Real.pi / 2 - w.im) < α₂ :=
      max_lt hα (by linarith)
    linarith
  · rw [abs_lt]
    have hlo : max α₁ (-_root_.Real.pi / 2 - w.im) <
        min α₂ (_root_.Real.pi / 2 - w.im) := by
      apply max_lt
      · exact lt_min hα (by linarith)
      · exact lt_min (by linarith) (by linarith)
    have hl := le_max_right α₁ (-_root_.Real.pi / 2 - w.im)
    have hu := min_le_right α₂ (_root_.Real.pi / 2 - w.im)
    constructor <;> linarith

/-- On each closed continued subsector the chosen ray integrals are absolutely
convergent and define an analytic continuation sufficiently far from the origin.
Temme, Theorem 2.5, synopsis TEM-02-07. -/
theorem exists_analyticOnNhd_transform {f : ℂ → ℂ} {a : ℕ → ℂ} {lam : ℂ}
    {α₁ α₂ β₁ β₂ : ℝ} (hα₁ : α₁ < 0) (hα₂ : 0 < α₂)
    (hlam : 0 < lam.re) (hf : IsKernel f a lam α₁ α₂)
    (hβ₁ : -α₂ - _root_.Real.pi / 2 < β₁) (hβ : β₁ ≤ β₂)
    (hβ₂ : β₂ < -α₁ + _root_.Real.pi / 2) :
    ∃ R : ℝ, AnalyticOnNhd ℂ (transform f α₁ α₂)
      {w | R < w.re ∧ β₁ ≤ w.im ∧ w.im ≤ β₂} ∧
      ∀ w : ℂ, R < w.re → β₁ ≤ w.im → w.im ≤ β₂ →
        IntegrableOn (fun r : ℝ =>
          exp (-exp w * exp (I * rayAngle α₁ α₂ w) * r) *
            f (log (r : ℂ) + I * rayAngle α₁ α₂ w)) (Ioi 0) := by
  sorry

/-- The continuation agrees with the original positive-ray Laplace integral when
its positive real argument is sufficiently large.
Temme, Theorem 2.5, synopsis TEM-02-07. -/
theorem exists_transform_ofReal {f : ℂ → ℂ} {a : ℕ → ℂ} {lam : ℂ}
    {α₁ α₂ : ℝ} (hα₁ : α₁ < 0) (hα₂ : 0 < α₂)
    (hlam : 0 < lam.re) (hf : IsKernel f a lam α₁ α₂) :
    ∃ R : ℝ, ∀ u : ℝ, R < u →
      transform f α₁ α₂ u =
        ∫ r : ℝ in Ioi 0, exp (-exp (u : ℂ) * r) * f (log (r : ℂ)) := by
  sorry

/-- The full lifted-sector Watson expansion under analytic-sector and exponential-growth
hypotheses. The expansion uses the same powers continued from the positive ray.
Temme, Theorem 2.5, synopsis TEM-02-07. -/
theorem hasAsymptoticExpansion_transform {f : ℂ → ℂ} {a : ℕ → ℂ} {lam : ℂ}
    {α₁ α₂ β₁ β₂ : ℝ} (hα₁ : α₁ < 0) (hα₂ : 0 < α₂)
    (hlam : 0 < lam.re) (hf : IsKernel f a lam α₁ α₂)
    (hβ₁ : -α₂ - _root_.Real.pi / 2 < β₁) (hβ : β₁ ≤ β₂)
    (hβ₂ : β₂ < -α₁ + _root_.Real.pi / 2) :
    HasAsymptoticExpansion
      (comap (fun w : ℂ => w.re) atTop ⊓ 𝓟 {w : ℂ | β₁ ≤ w.im ∧ w.im ≤ β₂})
      (fun (n : ℕ) (w : ℂ) => exp (-((n : ℂ) + lam) * w))
      (fun n => a n * Gamma (n + lam)) (transform f α₁ α₂) := by
  sorry

end Asymptotics.LiftedWatson
