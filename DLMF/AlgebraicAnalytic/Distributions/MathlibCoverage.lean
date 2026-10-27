/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# DLMF §§1.16–1.17 results already in Mathlib

Checked pointers to Mathlib declarations for DLMF §1.16 (distributions) and §1.17 (the Dirac
delta). Mathlib's distributions `𝓓'(Ω, F)` are continuous `ℝ`-linear maps on the real test
functions `𝓓(Ω, ℝ)` (complex distributions take `F = ℂ`; testing only real test functions is
equivalent), with the topology of compact convergence; its tempered distributions `𝓢'(E, F)` are
continuous `ℂ`-linear maps on `𝓢(E, ℂ)` with the topology of pointwise convergence. Mathlib's
Fourier transform is `𝓕 f ξ = ∫ e^{-2πi⟪x, ξ⟫} f x dx`, not DLMF's 1.14.1; DLMF's transform is
`DLMF.AlgebraicAnalytic.dlmfFourierSchwartz`.
-/

/- §1.16(i): test functions and distributions. -/
dlmf_upstream 1.16.i TestFunction
  "exact: 𝓓(Ω, F), smooth compactly supported functions with the inductive-limit topology"
dlmf_upstream 1.16.E1 Distribution
  "exact: distributions are continuous linear maps 𝓓(Ω, ℝ) →L[ℝ] F"
dlmf_upstream 1.16.E2 Distribution
  "exact: continuity on 𝓓(Ω, ℝ); the topology is the inductive limit topology"
dlmf_upstream 1.16.E3 Distribution.ofFun_apply
  "exact: ⟨Λ_f, φ⟩ = ∫ φ x • f x for locally integrable f"
dlmf_upstream 1.16.E4 ContinuousLinearMap.add_apply
  "exact: (Λ₁ + Λ₂) φ = Λ₁ φ + Λ₂ φ"
dlmf_upstream 1.16.E5 ContinuousLinearMap.map_smul
  "exact: Λ (c φ) = c Λ φ (real c on real test functions); (c Λ) φ = c (Λ φ) by definition"

/- §1.16(ii)–(iii): derivatives and the Dirac delta. -/
dlmf_upstream 1.16.E8 Distribution.lineDerivOp_apply_apply
  "exact: ⟨∂_v Λ, φ⟩ = ⟨Λ, -∂_v φ⟩"
dlmf_upstream 1.16.E10 Distribution.delta_apply
  "exact: ⟨δ_x, φ⟩ = φ(x) (real valued)"
dlmf_upstream 1.16.E11 Distribution.delta_apply
  "exact: ⟨δ_{x₀}, φ⟩ = φ(x₀)"

/- §1.16(v)–(vi): tempered distributions, several variables. -/
dlmf_upstream 1.16.v SchwartzMap
  "exact: the Schwartz space 𝓣 = 𝓢(E, F) of rapidly decreasing smooth functions"
dlmf_upstream 1.16.E24 schwartz_withSeminorms
  "stronger: the topology of 𝓢 is given by the seminorms sup |x|^k |φ^{(n)}(x)|"
dlmf_upstream 1.16.v TemperedDistribution
  "exact: 𝓢'(E, F) = 𝓢(E, ℂ) →Lₚₜ[ℂ] F"
dlmf_upstream 1.16.E25 PointwiseConvergenceCLM.tendsto_iff_forall_tendsto
  "exact: convergence in 𝓢' is pointwise convergence on 𝓢"
dlmf_upstream 1.16.v TemperedDistribution.derivCLM_apply_apply
  "exact: the derivative of a tempered distribution, ⟨u', φ⟩ = ⟨u, -φ'⟩"
dlmf_upstream 1.16.vi Distribution
  "exact: distributions on an open set of any finite-dimensional real normed space"
dlmf_upstream 1.16.E26 Distribution.ofFun_apply
  "exact: ⟨Λ_f, φ⟩ = ∫_{ℝⁿ} φ x • f x"
dlmf_upstream 1.16.E28 SchwartzMap.decay
  "exact: |x|^k ‖D^n φ(x)‖ ≤ C, the defining bounds of 𝓣ₙ"

/- §1.16(vii)–(viii): Fourier transforms (Mathlib's normalization). -/
dlmf_upstream 1.16.E29 SchwartzMap.fourier_coe
  "different convention: Mathlib's 𝓕 on 𝓢 uses e^{-2πi⟪x, ξ⟫}; DLMF's is dlmfFourierSchwartz"
dlmf_upstream 1.16.E35 TemperedDistribution.fourier_apply
  "different convention: ⟨𝓕 u, φ⟩ = ⟨u, 𝓕 φ⟩ with Mathlib's 𝓕"
dlmf_upstream 1.16.E36 TemperedDistribution.fourier_lineDerivOp_eq
  "different convention: Fourier transform of a directional derivative, Mathlib's 𝓕"
dlmf_upstream 1.16.E39 TemperedDistribution.fourier_delta_zero
  "different convention: 𝓕 δ = 1 in Mathlib's normalization (DLMF: 1/√(2π))"

/- §1.17: the Dirac delta. -/
dlmf_upstream 1.17.E2 Distribution.delta_apply
  "exact: ⟨δ_a, φ⟩ = φ(a), the meaning of ∫ δ(x - a) φ(x) dx = φ(a)"
dlmf_upstream 1.17.E2 TemperedDistribution.delta_apply
  "exact: the tempered delta, δ_a φ = φ(a)"
dlmf_upstream 1.17.E8 Continuous.fourierInv_fourier_eq
  "different convention: Fourier inversion 𝓕⁻(𝓕 f) = f in Mathlib's normalization"
dlmf_upstream 1.17.E17 hasSum_fourier_series_of_summable
  "partial: a function on the circle with summable Fourier coefficients is the sum of its series"
