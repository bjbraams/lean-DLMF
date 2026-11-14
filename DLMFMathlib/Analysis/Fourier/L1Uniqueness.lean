/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Uniqueness of the Fourier transform on L1

Andrews, Askey and Roy, *Special Functions*, Theorem 6.5.1, pp. 306–307
(synopsis AAR-6.5.1–6.6.2). Equality is almost everywhere; no continuity
hypothesis is imposed on the original integrable functions. The scalar theorem
extends to complex Banach-valued functions on finite-dimensional real inner-product spaces.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Integrable

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Two integrable functions with equal Fourier transforms agree almost everywhere.
Andrews–Askey–Roy, *Special Functions*, Theorem 6.5.1, pp. 306–307
(synopsis AAR-6.5.1–6.6.2). The measure is the canonical Euclidean volume. -/
theorem ae_eq_of_fourier_eq {f g : V → F} (hf : Integrable f) (hg : Integrable g)
    (hFourier : FourierTransform.fourier f = FourierTransform.fourier g) :
    f =ᵐ[volume] g := by
  sorry

/-- An integrable function with identically zero Fourier transform vanishes almost
everywhere. Andrews–Askey–Roy, *Special Functions*, Theorem 6.5.1, pp. 306–307
(synopsis AAR-6.5.1–6.6.2). -/
theorem ae_eq_zero_of_fourier_eq_zero {f : V → F} (hf : Integrable f)
    (hFourier : FourierTransform.fourier f = 0) : f =ᵐ[volume] 0 := by
  apply hf.ae_eq_of_fourier_eq (integrable_zero V F volume)
  rw [hFourier]
  ext x
  simp [Real.fourier_eq]

end MeasureTheory.Integrable
