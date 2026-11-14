/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Legendre
public import DLMF.Bessel.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Stieltjes, Hilb and Fourier–Legendre expansions

Temme, *Special Functions* (1996), §§6.8.4–6.9, pp. 158–164,
synopses TEM-06-13–TEM-06-16. The least-squares statements retain the full
`L²` domain, and angular asymptotic bounds specify their uniformity sets.
-/

@[expose] public noncomputable section
open Complex MeasureTheory Filter Finset DLMF.Hypergeometric
open scoped Topology Real Nat
namespace DLMF.OrthogonalPolynomials

/-- The complete Stieltjes summand, including the Gamma prefactor,
Temme §6.8.4, pp. 158–160, synopsis TEM-06-13. -/
def legendreStieltjesTerm (n : ℕ) (θ : ℝ) (k : ℕ) : ℂ :=
  Real.sqrt (2 / (Real.pi * Real.sin θ)) *
    (Real.Gamma (n + 1) / Real.Gamma (n + 3 / 2)) *
    pochhammer (1 / 2) k ^ 2 /
    (k.factorial * pochhammer (n + 3 / 2) k * (2 * Real.sin θ : ℂ) ^ k) *
    Real.cos (((n : ℝ) + k + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * Real.pi / 2)

/-- The removable Hilb amplitude at the pole, Temme §6.8.4, synopsis TEM-06-13. -/
def Real.legendreHilbAmplitude (θ : ℝ) : ℝ :=
  if θ = 0 then 1 else Real.sqrt (θ / Real.sin θ)

/-- The full Stieltjes summand formula, Temme §6.8.4, synopsis TEM-06-13. -/
theorem legendreStieltjesTerm_def (n : ℕ) (θ : ℝ) (k : ℕ) :
    legendreStieltjesTerm n θ k =
      Real.sqrt (2 / (Real.pi * Real.sin θ)) *
        (Real.Gamma (n + 1) / Real.Gamma (n + 3 / 2)) * pochhammer (1 / 2) k ^ 2 /
        (k.factorial * pochhammer (n + 3 / 2) k * (2 * Real.sin θ : ℂ) ^ k) *
        Real.cos (((n : ℝ) + k + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * Real.pi / 2) := rfl

/-- The amplitude formula with its limiting value, Temme §6.8.4. -/
theorem Real.legendreHilbAmplitude_def (θ : ℝ) : Real.legendreHilbAmplitude θ =
    if θ = 0 then 1 else Real.sqrt (θ / Real.sin θ) := rfl

/-- Uniform finite Stieltjes expansion, Temme §6.8.4, synopsis TEM-06-13. -/
theorem legendrePolynomialP_stieltjes_uniform {δ : ℝ} (hδ : 0 < δ)
    (hδπ : δ < Real.pi / 2) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℕ, 1 ≤ A ∧ ∀ n ≥ A,
      ∀ θ ∈ Set.Icc δ (Real.pi - δ),
        ‖legendrePolynomialP n (Real.cos θ) - ∑ k ∈ range N, legendreStieltjesTerm n θ k‖ ≤
          C * (n : ℝ) ^ (-(N : ℝ) - 1 / 2) := by
  sorry

/-- The Stieltjes expansion also converges in its overlap region,
Temme §6.8.4, synopsis TEM-06-13. -/
theorem hasSum_legendreStieltjesTerm (n : ℕ) {θ : ℝ}
    (hθ : 0 < θ) (hθπ : θ < Real.pi) (hconv : 1 < 2 * Real.sin θ) :
    HasSum (legendreStieltjesTerm n θ) (legendrePolynomialP n (Real.cos θ)) := by
  sorry

/-- Uniform Hilb approximation including the removable endpoint,
Temme §6.8.4, synopsis TEM-06-13. -/
theorem legendrePolynomialP_hilb_uniform {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℕ, 1 ≤ A ∧ ∀ n ≥ A,
      ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi - δ),
        ‖legendrePolynomialP n (Real.cos θ) -
          Real.legendreHilbAmplitude θ * Complex.besselJ 0 (((n : ℝ) + 1 / 2) * θ)‖ ≤
            C * Real.sqrt θ * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  sorry

/-- The exact least-squares error for any square-integrable function,
Temme (6.58)–(6.62), synopsis TEM-06-14. -/
theorem integral_norm_sub_sum_legendrePolynomialP_sq_of_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (-1 : ℝ) 1))) (a : ℕ → ℂ) (N : ℕ) :
    (∫ x : ℝ in (-1 : ℝ)..1,
      ‖f x - ∑ n ∈ range N, a n * legendrePolynomialP n x‖ ^ 2) =
      (∫ x : ℝ in (-1 : ℝ)..1, ‖f x‖ ^ 2) -
      (∑ n ∈ range N, 2 / (2 * (n : ℝ) + 1) * ‖legendreCoeff f n‖ ^ 2) +
      ∑ n ∈ range N, 2 / (2 * (n : ℝ) + 1) * ‖a n - legendreCoeff f n‖ ^ 2 := by
  sorry

/-- Bessel's infinite inequality on the full `L²` domain,
Temme (6.62), synopsis TEM-06-14. -/
theorem summable_legendreCoeff_sq_of_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (-1 : ℝ) 1))) :
    Summable (fun n : ℕ => 2 / (2 * (n : ℝ) + 1) * ‖legendreCoeff f n‖ ^ 2) ∧
      (∑' n : ℕ, 2 / (2 * (n : ℝ) + 1) * ‖legendreCoeff f n‖ ^ 2) ≤
        ∫ x : ℝ in (-1 : ℝ)..1, ‖f x‖ ^ 2 := by
  sorry

/-- Dirichlet convergence of Fourier–Legendre sums under local one-sided
linear bounds. Finite one-sided derivatives in Temme Theorem 6.6 imply these
bounds; global piecewise continuity implies the integral hypothesis.
Temme p. 162, synopsis TEM-06-15. -/
theorem tendsto_sum_legendreCoeff_of_one_sided_bound {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-1) 1) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (fm fp : ℂ) (hlocal : ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ δ < min (x + 1) (1 - x) ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) δ, ‖f (x - t) - fm‖ ≤ C * t ∧ ‖f (x + t) - fp‖ ≤ C * t) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, legendreCoeff f n * legendrePolynomialP n x)
      atTop (𝓝 ((fm + fp) / 2)) := by
  sorry

/-- The coefficient formula from repeated integration by parts, with actual
one-sided endpoint derivatives, Temme §6.9.1, synopsis TEM-06-15. -/
theorem legendreCoeff_eq_integral_derivative (F : ℕ → ℝ → ℂ) (n : ℕ)
    (hcont : ∀ k ≤ n, ContinuousOn (F k) (Set.Icc (-1) 1))
    (hderiv : ∀ k < n, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc (-1) 1) x) :
    legendreCoeff (F 0) n = (2 * n + 1 : ℂ) / (2 ^ (n + 1) * n.factorial) *
      ∫ x : ℝ in (-1 : ℝ)..1, F n x * (1 - (x : ℂ) ^ 2) ^ n := by
  sorry

/-- Uniform plane-wave expansion on the full orthogonality interval,
Temme (6.64), synopsis TEM-06-16; the spherical Bessel definition includes zero. -/
theorem tendstoUniformlyOn_legendre_plane_wave (a : ℝ) :
    TendstoUniformlyOn
      (fun N : ℕ => fun x : ℝ => ∑ n ∈ range N,
        (2 * n + 1 : ℂ) * I ^ n * DLMF.Bessel.sphericalJ n a * legendrePolynomialP n x)
      (fun x : ℝ => exp (I * a * x)) atTop (Set.Icc (-1) 1) := by
  sorry

/-- The Fourier–Legendre truncation is the unique least-squares polynomial of degree
at most `N`, with a full `L²` datum, Temme (6.58)–(6.62), synopsis TEM-06-14. -/
theorem legendre_partialSum_unique_leastSquares {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (-1 : ℝ) 1))) (N : ℕ) :
    let S := fun x : ℝ => ∑ n ∈ range (N + 1), legendreCoeff f n * legendrePolynomialP n x
    ∀ P : Polynomial ℂ, P.natDegree ≤ N →
      (∫ x : ℝ in (-1 : ℝ)..1, ‖f x - S x‖ ^ 2) ≤
        (∫ x : ℝ in (-1 : ℝ)..1, ‖f x - P.eval (x : ℂ)‖ ^ 2) ∧
      ((∫ x : ℝ in (-1 : ℝ)..1, ‖f x - P.eval (x : ℂ)‖ ^ 2) =
        (∫ x : ℝ in (-1 : ℝ)..1, ‖f x - S x‖ ^ 2) ↔ ∀ x : ℝ, P.eval (x : ℂ) = S x) := by
  sorry

end DLMF.OrthogonalPolynomials
