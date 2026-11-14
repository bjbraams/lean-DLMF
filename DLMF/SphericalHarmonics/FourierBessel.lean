/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.SphericalHarmonics.Basic
public import DLMF.Bessel.Basic
public import DLMF.Hypergeometric.Basic
public import TauCeti.RingTheory.MvPolynomial.Harmonic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Fourier–Bessel reduction in arbitrary dimension

Andrews, Askey and Roy, *Special Functions*, §9.10. Fourier integrals have the
positive `2πi` sign, implemented by Mathlib's inverse Fourier transform. Sphere
integrals use unnormalized surface measure; the factor `ωₙ` of the normalized
book convention is therefore absent. Harmonic polynomials have arbitrary complex coefficients.
-/

@[expose] public section

open MeasureTheory MvPolynomial
open scoped Real SchwartzMap

noncomputable section

namespace DLMF.SphericalHarmonics

/-- The spherical exponential transform of a harmonic polynomial.
Andrews–Askey–Roy, *Special Functions*, Lemma 9.10.2
(synopsis AAR-9.10.2–9.10.6), with unnormalized surface measure. The entire
normalized Bessel form includes every complex frequency, including zero. -/
theorem integral_sphere_exp_mul_harmonic {n k : ℕ} (hn : 2 ≤ n)
    {P : MvPolynomial (Fin n) ℂ} (hP : P ∈ harmonicSubmodule (Fin n) ℂ k)
    (η : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (r : ℂ) :
    (∫ ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      Complex.exp (2 * Real.pi * Complex.I * r * (∑ i, ξ.val i * η.val i)) *
        eval (fun i => (ξ.val i : ℂ)) P
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) =
      2 * (Real.pi : ℂ) ^ ((n : ℂ) / 2) * (Real.pi * Complex.I * r) ^ k *
        Complex.regularizedHGFun ∅ {k + (n : ℂ) / 2} (-(Real.pi * r) ^ 2) *
        eval (fun i => (η.val i : ℂ)) P := by
  sorry

/-- Radial harmonic Fourier–Bessel reduction with the positive Fourier sign.
Andrews–Askey–Roy, *Special Functions*, Theorem 9.10.3
(synopsis AAR-9.10.2–9.10.6). A nonzero harmonic makes the assumed full-space
integrability equivalent to weighted radial integrability. -/
theorem fourierInv_radial_mul_surface_harmonic {n k : ℕ} (hn : 2 ≤ n)
    {P : MvPolynomial (Fin n) ℂ} (hP : P ∈ harmonicSubmodule (Fin n) ℂ k) (hP₀ : P ≠ 0)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      f ‖x‖ * eval (fun i => (x i / ‖x‖ : ℂ)) P))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ 0) :
    FourierTransform.fourierInv
      (fun x : EuclideanSpace ℝ (Fin n) =>
        f ‖x‖ * eval (fun i => (x i / ‖x‖ : ℂ)) P) y =
      2 * Real.pi * Complex.I ^ k * (‖y‖ : ℂ) ^ (1 - (n : ℂ) / 2) *
        eval (fun i => (y i / ‖y‖ : ℂ)) P *
        ∫ s : ℝ in Set.Ioi 0, f s *
          Complex.besselJ (k + (n : ℂ) / 2 - 1) (2 * Real.pi * s * ‖y‖) *
          (s : ℂ) ^ ((n : ℂ) / 2) := by
  sorry

/-- Solid harmonic Fourier–Bessel reduction. Andrews–Askey–Roy, *Special Functions*,
Theorem 9.10.5 (synopsis AAR-9.10.2–9.10.6). -/
theorem fourierInv_radial_mul_solid_harmonic {n k : ℕ} (hn : 2 ≤ n)
    {P : MvPolynomial (Fin n) ℂ} (hP : P ∈ harmonicSubmodule (Fin n) ℂ k) (hP₀ : P ≠ 0)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      f ‖x‖ * eval (fun i => (x i : ℂ)) P))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ 0) :
    FourierTransform.fourierInv
      (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖ * eval (fun i => (x i : ℂ)) P) y =
      2 * Real.pi * Complex.I ^ k * (‖y‖ : ℂ) ^ (1 - (n : ℂ) / 2 - k) *
        eval (fun i => (y i : ℂ)) P *
        ∫ s : ℝ in Set.Ioi 0, f s *
          Complex.besselJ (k + (n : ℂ) / 2 - 1) (2 * Real.pi * s * ‖y‖) *
          (s : ℂ) ^ ((n : ℂ) / 2 + k) := by
  sorry

/-- The Gaussian times a solid harmonic is a Fourier eigenfunction.
Andrews–Askey–Roy, *Special Functions*, Theorem 9.10.6
(synopsis AAR-9.10.2–9.10.6), with the positive Fourier sign. -/
theorem fourierInv_gaussian_mul_harmonic {n k : ℕ} (hn : 1 ≤ n)
    {P : MvPolynomial (Fin n) ℂ} (hP : P ∈ harmonicSubmodule (Fin n) ℂ k)
    (y : EuclideanSpace ℝ (Fin n)) :
    FourierTransform.fourierInv (fun x : EuclideanSpace ℝ (Fin n) =>
      (Real.exp (-Real.pi * ‖x‖ ^ 2) : ℂ) * eval (fun i => (x i : ℂ)) P) y =
      Complex.I ^ k * (Real.exp (-Real.pi * ‖y‖ ^ 2) : ℂ) *
        eval (fun i => (y i : ℂ)) P := by
  sorry

/-- The homogeneous harmonic Fourier identity as equality against every Schwartz test
function, hence as tempered distributions. Andrews–Askey–Roy, *Special Functions*,
Corollary 9.10.4 (synopsis AAR-9.10.2–9.10.6). Both tested integrals converge absolutely. -/
theorem integral_homogeneous_harmonic_fourierInv {n k : ℕ} (hn : 2 ≤ n)
    {P : MvPolynomial (Fin n) ℂ} (hP : P ∈ harmonicSubmodule (Fin n) ℂ k)
    {lam : ℂ} (hlam : 0 < lam.re) (hlam₁ : lam.re < n)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    (∫ x : EuclideanSpace ℝ (Fin n), (‖x‖ : ℂ) ^ (-lam) *
      eval (fun i => (x i / ‖x‖ : ℂ)) P * FourierTransform.fourierInv φ x) =
      Complex.I ^ k * (Real.pi : ℂ) ^ (lam - (n : ℂ) / 2) *
        Complex.Gamma (((n + k : ℕ) : ℂ) / 2 - lam / 2) /
        Complex.Gamma ((k + lam) / 2) *
        ∫ y : EuclideanSpace ℝ (Fin n), (‖y‖ : ℂ) ^ (lam - n) *
          eval (fun i => (y i / ‖y‖ : ℂ)) P * φ y := by
  sorry


/-- The zero-frequency value of the radial surface-harmonic transform.
Andrews–Askey–Roy, *Special Functions*, Theorems 9.10.3–9.10.5
(synopsis AAR-9.10.2–9.10.6). It is zero in positive harmonic degree;
in degree zero it is the radial mass times the constant harmonic. -/
theorem fourierInv_radial_mul_surface_harmonic_zero {n k : ℕ} (hn : 2 ≤ n)
    {P : MvPolynomial (Fin n) ℂ} (hP : P ∈ harmonicSubmodule (Fin n) ℂ k)
    (hP₀ : P ≠ 0) (f : ℝ → ℂ) (hf : Measurable f)
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      f ‖x‖ * eval (fun i => (x i / ‖x‖ : ℂ)) P)) :
    FourierTransform.fourierInv
      (fun x : EuclideanSpace ℝ (Fin n) =>
        f ‖x‖ * eval (fun i => (x i / ‖x‖ : ℂ)) P) 0 =
      if k = 0 then
        2 * (Real.pi : ℂ) ^ ((n : ℂ) / 2) / Complex.Gamma ((n : ℂ) / 2) *
          eval (fun _ => (0 : ℂ)) P *
          ∫ s : ℝ in Set.Ioi 0, f s * (s : ℂ) ^ ((n : ℂ) - 1)
      else 0 := by
  sorry

end DLMF.SphericalHarmonics
