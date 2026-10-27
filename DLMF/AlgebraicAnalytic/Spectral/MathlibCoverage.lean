/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# DLMF §1.18 results already in Mathlib

Checked pointers to Mathlib declarations for the Hilbert-space material of DLMF §1.18(i)–(iii)
and §1.18(ix). Mathlib's inner product `⟪u, v⟫` is conjugate linear in `u` and linear in `v`;
DLMF's `⟨u, v⟩` is linear in `u`, so DLMF's `⟨u, v⟩` is Mathlib's `⟪v, u⟫` (for instance DLMF's
`cₙ = ⟨v, vₙ⟩` (1.18.3) is `⟪vₙ, v⟫ = b.repr v n`).
-/

/- §1.18(i): Hilbert spaces. -/
dlmf_upstream 1.18.i InnerProductSpace
  "exact: inner product spaces (Mathlib's inner product is linear in the second argument)"
dlmf_upstream 1.18.E1 norm_eq_sqrt_re_inner
  "exact: ‖v‖ = √⟨v, v⟩"
dlmf_upstream 1.18.E2 Orthonormal.tsum_inner_products_le
  "exact: Bessel's inequality Σ |⟨v, vₙ⟩|² ≤ ‖v‖²"
dlmf_upstream 1.18.E3 HilbertBasis.repr_apply_apply
  "exact: the coefficients b.repr v n = ⟪b n, v⟫ (DLMF's ⟨v, vₙ⟩)"
dlmf_upstream 1.18.E4 HilbertBasis.tsum_inner_mul_inner
  "exact: Parseval Σ ⟪v, bₙ⟫⟪bₙ, w⟫ = ⟪v, w⟫, with w = v"
dlmf_upstream 1.18.i exists_hilbertBasis
  "stronger: every Hilbert space has a Hilbert basis (complete orthonormal set)"
dlmf_upstream 1.18.E5 HilbertBasis.summable_inner_mul_inner
  "exact: Σ |cₙ|² < ∞"
dlmf_upstream 1.18.E6 HilbertBasis.hasSum_repr_symm
  "exact: for c ∈ ℓ², Σ cₙ bₙ converges to the unique v with coefficients c"
dlmf_upstream 1.18.E7 HilbertBasis.hasSum_repr_symm
  "stronger: unconditional convergence in norm"
dlmf_upstream 1.18.E8 lp.norm_rpow_eq_tsum
  "exact: ‖v‖² = Σ |cₙ|² in ℓ²"
dlmf_upstream 1.18.E9 lp.inner_eq_tsum
  "exact: ⟨v, w⟩ = Σ cₙ conj(dₙ) (Mathlib: Σ ⟪cₙ, dₙ⟫)"
dlmf_upstream 1.18.E10 HilbertBasis.repr
  "exact: the isometric isomorphism E ≃ₗᵢ ℓ² given by a Hilbert basis"

/- §1.18(ii): L² spaces. -/
dlmf_upstream 1.18.E11 MeasureTheory.MemLp
  "exact: MemLp f 2 μ, square integrability for a measure μ (Lebesgue–Stieltjes included)"
dlmf_upstream 1.18.E12 MeasureTheory.L2.inner_def
  "exact: ⟨f, g⟩ = ∫ conj(f) g dμ in Mathlib's convention"
dlmf_upstream 1.18.E14 HilbertBasis.tsum_inner_mul_inner
  "exact: ∫ |f|² = Σ |cₙ|² (Parseval in L²(X))"
dlmf_upstream 1.18.E17 HilbertBasis.hasSum_repr
  "exact: f = Σ ⟨f, φₙ⟩ φₙ in L²"
dlmf_upstream 1.18.E18 HilbertBasis.tsum_inner_mul_inner
  "partial: the kernel K(x, y) = Σ φₙ(x) conj(φₙ(y)) acts weakly as the identity"
dlmf_upstream 1.18.E19 HilbertBasis.tsum_inner_mul_inner
  "partial: completeness relation, weakly: Σ ⟨g, φₙ⟩⟨φₙ, f⟩ = ⟨g, f⟩"
dlmf_upstream 1.18.E20 HilbertBasis.orthonormal
  "exact: orthonormality of the basis"

/- §1.18(iii), §1.18(ix): operators. -/
dlmf_upstream 1.18.E21 LinearMap
  "exact: linear maps"
dlmf_upstream 1.18.E22 ContinuousLinearMap.sSup_sphere_eq_norm
  "exact: ‖T‖ = sup_{‖v‖ = 1} ‖Tv‖"
dlmf_upstream 1.18.iii ContinuousLinearMap.extend
  "exact: a bounded densely defined operator extends uniquely to a bounded operator"
dlmf_upstream 1.18.E23 ContinuousLinearMap.adjoint_inner_right
  "exact: ⟨Tv, w⟩ = ⟨v, T* w⟩ for bounded T"
dlmf_upstream 1.18.iii LinearPMap
  "exact: unbounded operators T : 𝓓(T) → V with linear domain"
dlmf_upstream 1.18.E68 LinearPMap.mem_adjoint_domain_iff
  "exact: w ∈ 𝓓(T*) iff v ↦ ⟨Tv, w⟩ is continuous (equivalently bounded on the unit sphere)"
dlmf_upstream 1.18.E69 LinearPMap.adjoint_isFormalAdjoint
  "exact: ⟨Tv, w⟩ = ⟨v, T* w⟩, v ∈ 𝓓(T), w ∈ 𝓓(T*), for densely defined T"
dlmf_upstream 1.18.E70 LinearPMap.IsFormalAdjoint
  "exact: T.IsFormalAdjoint T is ⟨Tv, w⟩ = ⟨v, Tw⟩ on 𝓓(T)"
dlmf_upstream 1.18.ix LinearPMap.IsFormalAdjoint.le_adjoint
  "exact: a symmetric operator satisfies T ⊂ T*"
dlmf_upstream 1.18.ix LinearPMap.isSelfAdjoint_def
  "exact: T is self-adjoint iff T* = T"
dlmf_upstream 1.18.ix spectrum.isCompact
  "exact: the spectrum of a bounded operator is compact"

/- §1.18(v): point spectra (abstract part) and the Fourier basis. -/
dlmf_upstream 1.18.E30 HilbertBasis.tsum_inner_mul_inner
  "partial: completeness relation of an eigenbasis, weakly"
dlmf_upstream 1.18.E31 HilbertBasis.hasSum_repr
  "exact: f = Σ f̂(λₙ) φ_{λₙ} in L²"
dlmf_upstream 1.18.E33 HilbertBasis.tsum_inner_mul_inner
  "exact: Parseval ∫ |f|² = Σ |f̂(λₙ)|²"
dlmf_upstream 1.18.E40 hasSum_fourier_series_L2
  "different setting: Fourier series in L² of the circle ℝ/Tℤ with Haar measure"
