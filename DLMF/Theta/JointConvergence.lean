/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic.Analytic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Joint theta convergence and the angular heat equation

Temme, *Special Functions* (1996), Chapter 12, equation (12.29), pages 324–325,
synopsis TEM-12-11. The joint domain is the amplitude plane times the upper half-plane.
The angular normalization gives the heat coefficient `-i*pi/4`.
-/

@[expose] public noncomputable section

open Complex Filter Set DLMF.Elliptic
open scoped Real Topology

namespace DLMF.Theta

/-- All four Fourier series converge locally uniformly in the amplitude and lattice
parameter together. Powers of the nome are represented by their specified tau exponential.
Temme (12.29), synopsis TEM-12-11. -/
theorem tendstoLocallyUniformlyOn_jacobiThetaTau_series :
    TendstoLocallyUniformlyOn (fun N : ℕ => fun p : ℂ × ℂ =>
      ∑ n ∈ Finset.range N, 2 * (-1 : ℂ) ^ n *
        exp (π * I * p.2 * ((n : ℂ) + 1 / 2) ^ 2) * sin ((2 * n + 1) * p.1))
      (fun p : ℂ × ℂ => jacobiThetaOneTau p.1 p.2) atTop {p | 0 < p.2.im} ∧
    TendstoLocallyUniformlyOn (fun N : ℕ => fun p : ℂ × ℂ =>
      ∑ n ∈ Finset.range N, 2 * exp (π * I * p.2 * ((n : ℂ) + 1 / 2) ^ 2) *
        cos ((2 * n + 1) * p.1))
      (fun p : ℂ × ℂ => jacobiThetaTwoTau p.1 p.2) atTop {p | 0 < p.2.im} ∧
    TendstoLocallyUniformlyOn (fun N : ℕ => fun p : ℂ × ℂ =>
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        exp (π * I * p.2 * (n : ℂ) ^ 2 + 2 * I * n * p.1))
      (fun p : ℂ × ℂ => jacobiThetaThreeTau p.1 p.2) atTop {p | 0 < p.2.im} ∧
    TendstoLocallyUniformlyOn (fun N : ℕ => fun p : ℂ × ℂ =>
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (-1 : ℂ) ^ n *
        exp (π * I * p.2 * (n : ℂ) ^ 2 + 2 * I * n * p.1))
      (fun p : ℂ × ℂ => jacobiThetaFourTau p.1 p.2) atTop {p | 0 < p.2.im} := by
  sorry

/-- The theta functions are jointly analytic on the amplitude plane times the upper
half-plane. Temme (12.29), synopsis TEM-12-11. -/
theorem analyticOnNhd_jacobiThetaTau_joint (j : ℕ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => jacobiThetaTau j p.1 p.2) {p | 0 < p.2.im} := by
  sorry

/-- The tau derivative and the second angular-amplitude derivative satisfy the theta
heat equation. Temme (12.29), synopsis TEM-12-11. -/
theorem deriv_jacobiThetaTau_tau (j : ℕ) (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (jacobiThetaTau j z) τ =
      -I * π / 4 * iteratedDeriv 2 (fun w => jacobiThetaTau j w τ) z := by
  sorry

end DLMF.Theta
