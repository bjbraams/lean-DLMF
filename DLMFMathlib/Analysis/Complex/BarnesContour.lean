/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Barnes contours with finite deformations and vertical tails

A finite central path is completed by upward vertical tails. Its relative Cauchy
index against a fixed vertical baseline records precisely which Gamma poles were
moved to its left. Unlike a graph contour, this can separate interlaced real pole
families. Sources: Kristensson, *Second Order Differential Equations*, Chapter 5,
§§5.4–5.5, pp. 80–88; Olver, *Asymptotics and Special Functions*, Chapter 8,
§6, pp. 299–302. The integral definition is totalized; application theorems assert
absolute convergence of the two tails separately.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace Complex

/-- The relative Cauchy index of the central path and the oppositely oriented
vertical closing segment. Equal endpoints make their union a closed cycle. -/
def barnesRelativeIndex (γ : ℝ → ℂ) (σ T : ℝ) (z : ℂ) : ℂ :=
  (1 / (2 * Real.pi * I)) *
    ((∫ t in (0 : ℝ)..1, (γ t - z)⁻¹ * deriv γ t) -
      ∫ t in -T..T, ((σ : ℂ) + I * t - z)⁻¹ * I)

/-- The defining Cauchy-integral difference for a Barnes contour index. -/
theorem barnesRelativeIndex_def (γ : ℝ → ℂ) (σ T : ℝ) (z : ℂ) :
    barnesRelativeIndex γ σ T z = (1 / (2 * Real.pi * I)) *
      ((∫ t in (0 : ℝ)..1, (γ t - z)⁻¹ * deriv γ t) -
        ∫ t in -T..T, ((σ : ℂ) + I * t - z)⁻¹ * I) := rfl

/-- A Barnes contour separates the poles `-left i-k` from `right j+k`,
for natural `k`. Relative indices encode the finite deformations from a vertical
baseline lying to the left of all right pole families. -/
structure BarnesContour {m n : ℕ} (left : Fin m → ℂ) (right : Fin n → ℂ) where
  /-- The common real part of the two vertical tails. -/
  baseline : ℝ
  /-- The positive height beyond every horizontal pole line. -/
  height : ℝ
  /-- The finite central path, parametrized on `[0,1]`. -/
  curve : ℝ → ℂ
  /-- The tail endpoints have distinct heights. -/
  height_pos : 0 < height
  /-- All left poles lie between the two tail heights. -/
  left_height : ∀ i, |(left i).im| < height
  /-- All right poles lie between the two tail heights. -/
  right_height : ∀ j, |(right j).im| < height
  /-- The straight baseline is left of every right family. -/
  baseline_lt_right : ∀ j, baseline < (right j).re
  /-- No left pole lies on the comparison baseline. -/
  baseline_ne_left : ∀ i (k : ℕ), baseline ≠ (-left i - k).re
  /-- The central path has the regularity required for its ordinary contour integral. -/
  piecewiseC1 : TauCeti.IsPiecewiseC1On curve 0 1
  /-- The path starts at the lower tail. -/
  lower_endpoint : curve 0 = (baseline : ℂ) - I * height
  /-- The path ends at the upper tail. -/
  upper_endpoint : curve 1 = (baseline : ℂ) + I * height
  /-- Left poles never lie on the central path. -/
  avoids_left : ∀ i (k : ℕ), ∀ t ∈ Icc (0 : ℝ) 1, curve t ≠ -left i - k
  /-- Right poles never lie on the central path. -/
  avoids_right : ∀ j (k : ℕ), ∀ t ∈ Icc (0 : ℝ) 1, curve t ≠ right j + k
  /-- Every left pole to the right of the original baseline is enclosed once positively. -/
  separates_left : ∀ i (k : ℕ),
    barnesRelativeIndex curve baseline height (-left i - k) =
      if baseline < (-left i - k).re then 1 else 0
  /-- No right pole is moved to the left of the contour. -/
  separates_right : ∀ j (k : ℕ),
    barnesRelativeIndex curve baseline height (right j + k) = 0

namespace BarnesContour

/-- Absolute integrability of the two vertical tails and the ordinary central
curve integral. This predicate supplies the convergence meaning of the completed
Barnes integral. -/
def IsIntegrable {m n : ℕ} {left : Fin m → ℂ} {right : Fin n → ℂ}
    (C : BarnesContour left right) (H : ℂ → ℂ) : Prop :=
  IntegrableOn (fun t : ℝ => I * H ((C.baseline : ℂ) + I * t)) (Iio (-C.height)) ∧
    IntervalIntegrable (fun t : ℝ => H (C.curve t) * deriv C.curve t) volume 0 1 ∧
    IntegrableOn (fun t : ℝ => I * H ((C.baseline : ℂ) + I * t)) (Ioi C.height)

/-- The three explicit integrability requirements for a Barnes contour. -/
theorem isIntegrable_iff {m n : ℕ} {left : Fin m → ℂ} {right : Fin n → ℂ}
    (C : BarnesContour left right) (H : ℂ → ℂ) :
    C.IsIntegrable H ↔
      IntegrableOn (fun t : ℝ => I * H ((C.baseline : ℂ) + I * t)) (Iio (-C.height)) ∧
        IntervalIntegrable (fun t : ℝ => H (C.curve t) * deriv C.curve t) volume 0 1 ∧
        IntegrableOn (fun t : ℝ => I * H ((C.baseline : ℂ) + I * t)) (Ioi C.height) := Iff.rfl

/-- Construct integrable Barnes data from its lower, central and upper pieces.
The contour of Kristensson, Chapter 5, §§5.4–5.5, pp. 80–88. -/
theorem IsIntegrable.mk {m n : ℕ} {left : Fin m → ℂ} {right : Fin n → ℂ}
    {C : BarnesContour left right} {H : ℂ → ℂ}
    (hl : IntegrableOn (fun t : ℝ => I * H ((C.baseline : ℂ) + I * t)) (Iio (-C.height)))
    (hc : IntervalIntegrable (fun t : ℝ => H (C.curve t) * deriv C.curve t) volume 0 1)
    (hu : IntegrableOn (fun t : ℝ => I * H ((C.baseline : ℂ) + I * t)) (Ioi C.height)) :
    C.IsIntegrable H := ⟨hl, hc, hu⟩

/-- The lower tail of integrable Barnes data is absolutely integrable.
The contour of Kristensson, Chapter 5, §§5.4–5.5, pp. 80–88. -/
theorem IsIntegrable.lower {m n : ℕ} {left : Fin m → ℂ} {right : Fin n → ℂ}
    {C : BarnesContour left right} {H : ℂ → ℂ} (h : C.IsIntegrable H) :
    IntegrableOn (fun t : ℝ => I * H ((C.baseline : ℂ) + I * t)) (Iio (-C.height)) := h.1

/-- The upper tail of integrable Barnes data is absolutely integrable.
The contour of Kristensson, Chapter 5, §§5.4–5.5, pp. 80–88. -/
theorem IsIntegrable.upper {m n : ℕ} {left : Fin m → ℂ} {right : Fin n → ℂ}
    {C : BarnesContour left right} {H : ℂ → ℂ} (h : C.IsIntegrable H) :
    IntegrableOn (fun t : ℝ => I * H ((C.baseline : ℂ) + I * t)) (Ioi C.height) := h.2.2


/-- The complete upward Barnes integral: lower vertical tail, central deformation,
and upper vertical tail. Each tail is an actual half-line integral. -/
def integral {m n : ℕ} {left : Fin m → ℂ} {right : Fin n → ℂ}
    (C : BarnesContour left right) (H : ℂ → ℂ) : ℂ :=
  (∫ t in Iio (-C.height), I * H ((C.baseline : ℂ) + I * t)) +
    (∫ t in (0 : ℝ)..1, H (C.curve t) * deriv C.curve t) +
      ∫ t in Ioi C.height, I * H ((C.baseline : ℂ) + I * t)

/-- The defining three pieces of the completed Barnes integral. -/
theorem integral_def {m n : ℕ} {left : Fin m → ℂ} {right : Fin n → ℂ}
    (C : BarnesContour left right) (H : ℂ → ℂ) :
    C.integral H =
      (∫ t in Iio (-C.height), I * H ((C.baseline : ℂ) + I * t)) +
        (∫ t in (0 : ℝ)..1, H (C.curve t) * deriv C.curve t) +
          ∫ t in Ioi C.height, I * H ((C.baseline : ℂ) + I * t) := rfl


/-- Truncate the two vertical tails at heights `-T` and `T`, retaining the same
central deformation. The ordinary truncation has `T >= C.height`. -/
def partialIntegral {m n : ℕ} {left : Fin m → ℂ} {right : Fin n → ℂ}
    (C : BarnesContour left right) (H : ℂ → ℂ) (T : ℝ) : ℂ :=
  (∫ t in -T..(-C.height), I * H ((C.baseline : ℂ) + I * t)) +
    (∫ t in (0 : ℝ)..1, H (C.curve t) * deriv C.curve t) +
      ∫ t in C.height..T, I * H ((C.baseline : ℂ) + I * t)

/-- The three finite intervals in a truncated Barnes integral. -/
theorem partialIntegral_def {m n : ℕ} {left : Fin m → ℂ} {right : Fin n → ℂ}
    (C : BarnesContour left right) (H : ℂ → ℂ) (T : ℝ) :
    C.partialIntegral H T =
      (∫ t in -T..(-C.height), I * H ((C.baseline : ℂ) + I * t)) +
        (∫ t in (0 : ℝ)..1, H (C.curve t) * deriv C.curve t) +
          ∫ t in C.height..T, I * H ((C.baseline : ℂ) + I * t) := rfl


end BarnesContour

/-- Disjoint opposite Gamma pole families admit a contour with finite deformations
and vertical tails. Kristensson, Chapter 5, §§5.4–5.5, pp. 80–88; Olver,
Chapter 8, §6, pp. 299–302. Coinciding poles within one family are permitted. -/
theorem nonempty_barnesContour {m n : ℕ} (left : Fin m → ℂ) (right : Fin n → ℂ)
    (hdisjoint : ∀ i j (k l : ℕ), -left i - k ≠ right j + l) :
    Nonempty (BarnesContour left right) := by
  sorry

end Complex
