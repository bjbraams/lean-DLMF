/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import DLMF.OrthogonalPolynomials.LegendreSeries
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Outgoing Dirichlet scattering by a unit sphere

Temme, *Special Functions* (1996), §10.3.2, (10.10)–(10.12), pp. 270–271,
synopsis TEM-10-07. The field uses the canonical entire spherical Bessel
function and the outgoing principal spherical Hankel function on positive radii.
-/

@[expose] public noncomputable section
open Complex Filter Set Laplacian
open scoped Topology
namespace DLMF.WaveEquation

/-- The `n`th outgoing spherical partial wave, with cosine of polar angle as argument,
Temme (10.10)–(10.12), synopsis TEM-10-07. -/
def sphereScatteringTerm (k r μ : ℝ) (n : ℕ) : ℂ :=
  -(2 * n + 1 : ℂ) * I ^ n *
    DLMF.Bessel.sphericalJ n k / DLMF.Bessel.sphericalH1 n k *
      DLMF.Bessel.sphericalH1 n (k * r) * DLMF.OrthogonalPolynomials.legendrePolynomialP n μ

/-- The outgoing sphere field as a sum of partial waves,
Temme (10.10)–(10.12), synopsis TEM-10-07. -/
def sphereScatteredField (k r μ : ℝ) : ℂ := ∑' n : ℕ, sphereScatteringTerm k r μ n

/-- The exact partial-wave normalization, Temme (10.10)–(10.12). -/
theorem sphereScatteringTerm_def (k r μ : ℝ) (n : ℕ) :
    sphereScatteringTerm k r μ n = -(2 * n + 1 : ℂ) * I ^ n *
      DLMF.Bessel.sphericalJ n k / DLMF.Bessel.sphericalH1 n k *
        DLMF.Bessel.sphericalH1 n (k * r) *
          DLMF.OrthogonalPolynomials.legendrePolynomialP n μ := rfl

/-- The defining partial-wave series, Temme (10.10)–(10.12). -/
theorem sphereScatteredField_def (k r μ : ℝ) :
    sphereScatteredField k r μ = ∑' n : ℕ, sphereScatteringTerm k r μ n := rfl

/-- The outgoing denominators are nonzero for positive frequency,
Temme §10.3.2, synopsis TEM-10-07. -/
theorem sphericalH1_ne_zero {k : ℝ} (hk : 0 < k) (n : ℕ) :
    DLMF.Bessel.sphericalH1 n k ≠ 0 := by
  sorry

/-- Absolute convergence of the exterior partial waves, including the boundary sphere,
Temme §10.3.2, synopsis TEM-10-07. -/
theorem summable_sphereScatteringTerm {k r μ : ℝ} (hk : 0 < k)
    (hr : 1 ≤ r) (hμ : μ ∈ Icc (-1 : ℝ) 1) :
    Summable (sphereScatteringTerm k r μ) := by
  sorry

/-- The scattered field cancels the incident plane wave on the sphere,
Temme (10.12), synopsis TEM-10-07. -/
theorem sphereScatteredField_boundary {k μ : ℝ} (hk : 0 < k)
    (hμ : μ ∈ Icc (-1 : ℝ) 1) :
    sphereScatteredField k 1 μ = -exp (I * k * μ) := by
  sorry

/-- The Cartesian exterior field solves Helmholtz's equation,
Temme §10.3.2, synopsis TEM-10-07. -/
theorem helmholtz_sphereScatteredField {k : ℝ} (hk : 0 < k)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : 1 < ‖p‖) :
    laplacian (fun q : EuclideanSpace ℝ (Fin 3) => sphereScatteredField k ‖q‖ (q 2 / ‖q‖)) p +
      k ^ 2 * sphereScatteredField k ‖p‖ (p 2 / ‖p‖) = 0 := by
  sorry

/-- Termwise differentiation of every order is locally uniform in the strict exterior,
Temme §10.3.2, synopsis TEM-10-07. -/
theorem tendstoLocallyUniformlyOn_sphereScattering_derivatives {k : ℝ}
    (hk : 0 < k) (j : ℕ) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => iteratedFDeriv ℝ j (fun q : EuclideanSpace ℝ (Fin 3) =>
        ∑ n ∈ Finset.range N, sphereScatteringTerm k ‖q‖ (q 2 / ‖q‖) n))
      (iteratedFDeriv ℝ j (fun q : EuclideanSpace ℝ (Fin 3) =>
        sphereScatteredField k ‖q‖ (q 2 / ‖q‖)))
      atTop {q : EuclideanSpace ℝ (Fin 3) | 1 < ‖q‖} := by
  sorry

/-- The outgoing Sommerfeld condition holds uniformly in the polar direction,
Temme §10.3.2, synopsis TEM-10-07. -/
theorem sphereScatteredField_radiation {k : ℝ} (hk : 0 < k) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 < R ∧ ∀ r ≥ R, ∀ μ ∈ Icc (-1 : ℝ) 1,
      ‖r * (deriv (fun s : ℝ => sphereScatteredField k s μ) r -
        I * k * sphereScatteredField k r μ)‖ < ε := by
  sorry

end DLMF.WaveEquation
