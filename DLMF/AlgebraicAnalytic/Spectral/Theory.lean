/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Spectral.Basic
public import DLMF.Bessel.Basic.Equation
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.MeasureTheory.Function.L2Space
public import DLMFMathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Oscillator
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.HilbertBasis
public import Mathlib.Analysis.Complex.RealDeriv
public import DLMFMathlib.Analysis.Fourier.DirichletKernel
public import DLMFMathlib.Analysis.Fourier.PoissonKernel

/-!
# Linear second-order differential operators and eigenfunction expansions (DLMF §1.18)

DLMF §1.18 surveys the spectral theory of `𝓛 = -d²/dx² + q(x)` (1.18.28). The Hilbert-space
facts of §1.18(i)–(ii) are Mathlib's (`HilbertBasis`, `lp`, `MeasureTheory.L2`; pointers in
`DLMF.AlgebraicAnalytic.Spectral.MathlibCoverage`).

## Main results

* `tendsto_integral_sq_sub_partialSum`: `L²` mean convergence (DLMF 1.18.13–1.18.16).
* `IsSymmetricOperator.eigenvalue_real`, `IsSymmetricOperator.inner_eq_zero`: reality of eigenvalues
  and orthogonality of eigenvectors of symmetric operators (DLMF 1.18.24).
* `integral_deriv2_mul_eq`, `integral_deriv2_mul_eq_of_dirichlet`: integration by parts and
  formal self-adjointness (DLMF 1.18.25–1.18.27).
* `hasSum_eigen_expansion`, `hasSum_resolvent_expansion`: eigenfunction expansions for a
  self-adjoint operator with an orthonormal basis of eigenvectors (DLMF 1.18.29–1.18.35).
* `sinEigenfunction_hilbertBasis`, `cosEigenfunction_hilbertBasis`,
  `expEigenfunction_hilbertBasis`, `hermiteFunction_eigen`, `hermiteFunction_hilbertBasis`:
  the examples 1.18.36–1.18.43.
* `IsEigenfunctionTransform.integral_norm_sq`, `IsEigenfunctionTransform.ae_eq_integral`,
  `IsDiagonalizedBy.inner_apply`, `IsDiagonalizedBy.inner_resolvent`: expansions over
  continuous and mixed spectra (DLMF 1.18.46–1.18.52, 1.18.64–1.18.66).
* `tendsto_stieltjes_inversion`, `tendsto_sokhotski_plemelj`: DLMF 1.18.53, 1.18.54.
* `besselOperator_sqrt_mul_besselJ`, `tendsto_hankel_kernel`, `tendsto_fourier_cos_sin`: the Hankel
  and Fourier integral theorems (DLMF 1.18.55–1.18.59).
* `exists_bound_state_of_integral_nonpos`: Simon's bound-state theorem (§1.18(viii)).
* `operatorSpectrum_eq_union`, `IsSelfAdjoint.operatorSpectrum_real`,
  `IsSymmetricOperator.exists_selfAdjoint_extension_iff`, `IsSymmetricOperator.adjoint_domain_eq`:
  spectra, deficiency indices and von Neumann's theory (§1.18(ix)).
* `allSolutionsL2Left_of_exists`, `rank_l2SolutionSpace_left`, `rank_l2SolutionSpace_add_two`,
  `limitPoint_iff_wronskian_tendsto_zero`: Weyl's alternative (§1.18(ix), 1.18.71).

## Implementation notes

The Hermite results use the TauCeti Hermite-function API; `ofReal_hermiteFunction`
identifies the DLMF normalization.

DLMF's `⟨u, v⟩` is linear in `u`, Mathlib's `⟪u, v⟫` in `v`: DLMF's `⟨f, φₙ⟩` is `⟪φₙ, f⟫`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Complex intervalIntegral
open scoped Topology InnerProductSpace ComplexConjugate

namespace DLMF.AlgebraicAnalytic

/-! ## §1.18(ii): `L²` convergence in the mean -/

/-- DLMF 1.18.13–1.18.16: for an orthonormal basis `φₙ` of `L²(X)` and `f ∈ L²(X)`, with
`cₙ = ⟨f, φₙ⟩ = ∫ f conj(φₙ)` (1.18.13), `lim_m ∫_X |f - Σ_{n≤m} cₙ φₙ|² = 0` (1.18.16, the
sense of 1.18.15). -/
@[dlmf 1.18.E13, dlmf 1.18.E15, dlmf 1.18.E16]
theorem tendsto_integral_sq_sub_partialSum {X : Set ℝ}
    (b : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict X))) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict X)) :
    Tendsto (fun m : ℕ => ∫ x in X, ‖f x - ∑ n ∈ Finset.range (m + 1),
        (∫ y in X, f y * conj ((b n : ℝ → ℂ) y)) * (b n : ℝ → ℂ) x‖ ^ 2) atTop (𝓝 0) := by
  let v := hf.toLp f
  let S : ℕ → Lp ℂ 2 (volume.restrict X) :=
    fun m => ∑ n ∈ Finset.range (m + 1), b.repr v n • b n
  have hcoef (n : ℕ) : b.repr v n = ∫ y in X, f y * conj ((b n : ℝ → ℂ) y) := by
    rw [b.repr_apply_apply, L2.inner_def]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with y hy
    rw [show v y = f y from hy, RCLike.inner_apply]
  have hS : Tendsto S atTop (𝓝 v) :=
    (b.hasSum_repr v).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun m => ‖v - S m‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (𝓝 v)).sub hS).norm.pow 2
  convert ht using 1
  funext m
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  apply MeasureTheory.integral_congr_ae
  have hsum := (Lp.coeFn_finsetSum (Finset.range (m + 1))
    (fun n => b.repr v n • b n)).trans
      (eventuallyEq_sum fun n _ => Lp.coeFn_smul (b.repr v n) (b n))
  filter_upwards [hf.coeFn_toLp, Lp.coeFn_sub v (S m), hsum] with x hfx hsub hsumx
  have hsx : (S m : ℝ → ℂ) x = ∑ n ∈ Finset.range (m + 1),
      (∫ y in X, f y * conj ((b n : ℝ → ℂ) y)) * (b n : ℝ → ℂ) x := by
    simpa only [S, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcoef] using hsumx
  rw [hsub, Pi.sub_apply, show v x = f x from hfx, hsx]

/-! ## §1.18(iii): symmetric operators and integration by parts -/

section Symmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- DLMF 1.18.24: the eigenvalues of a symmetric operator are real. -/
@[dlmf 1.18.E24]
theorem IsSymmetricOperator.eigenvalue_real {T : E →ₗ.[ℂ] E} (hT : IsSymmetricOperator T) {z : ℂ}
    (u : T.domain) (hu : (u : E) ≠ 0) (h : T u = z • (u : E)) : conj z = z := by
  have h1 := hT.2 u u
  rw [h, inner_smul_left, inner_smul_right] at h1
  have h2 : (⟪(u : E), (u : E)⟫_ℂ) ≠ 0 := inner_self_ne_zero.mpr hu
  exact mul_right_cancel₀ h2 h1

omit [CompleteSpace E] in
/-- DLMF 1.18.24: eigenvectors of a symmetric operator for distinct eigenvalues are
orthogonal, `⟨u_λ, u_t⟩ = 0` for `λ ≠ t`. -/
@[dlmf 1.18.E24]
theorem IsSymmetricOperator.inner_eq_zero {T : E →ₗ.[ℂ] E} (hT : IsSymmetricOperator T) {z w : ℂ}
    (u v : T.domain) (hu : (u : E) ≠ 0) (hTu : T u = z • (u : E)) (hTv : T v = w • (v : E))
    (hzw : z ≠ w) : ⟪(u : E), (v : E)⟫_ℂ = 0 := by
  have hz := hT.eigenvalue_real u hu hTu
  have h1 := hT.2 u v
  rw [hTu, hTv, inner_smul_left, inner_smul_right, hz] at h1
  have : (z - w) * ⟪(u : E), (v : E)⟫_ℂ = 0 := by linear_combination h1
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hzw)

end Symmetric

/-- DLMF 1.18.25–1.18.26: for `T = d²/dx²` on `[a, b]`,
`∫_a^b f'' g = [f' g]_a^b - [f g']_a^b + ∫_a^b f g''` (here for complex `f, g` with continuous
second derivatives on a neighbourhood of `[a, b]`). -/
@[dlmf 1.18.E25, dlmf 1.18.E26]
theorem integral_deriv2_mul_eq {a b : ℝ} {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) :
    ∫ x in a..b, deriv (deriv f) x * g x =
      (deriv f b * g b - deriv f a * g a) - (f b * deriv g b - f a * deriv g a) +
        ∫ x in a..b, f x * deriv (deriv g) x := by
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.iterate_deriv' 1 1
  have hg1 : ContDiff ℝ 1 (deriv g) := hg.iterate_deriv' 1 1
  have hdf : ∀ x, HasDerivAt f (deriv f x) x :=
    fun x => ((hf.differentiable (by norm_num)) x).hasDerivAt
  have hdg : ∀ x, HasDerivAt g (deriv g x) x :=
    fun x => ((hg.differentiable (by norm_num)) x).hasDerivAt
  have hdf' : ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    fun x => ((hf1.differentiable (by norm_num)) x).hasDerivAt
  have hdg' : ∀ x, HasDerivAt (deriv g) (deriv (deriv g) x) x :=
    fun x => ((hg1.differentiable (by norm_num)) x).hasDerivAt
  have hF : ∀ x ∈ uIcc a b, HasDerivAt (fun x => deriv f x * g x - f x * deriv g x)
      (deriv (deriv f) x * g x - f x * deriv (deriv g) x) x := by
    intro x _
    have := ((hdf' x).mul (hdg x)).sub ((hdf x).mul (hdg' x))
    convert this using 1
    ring
  have hcont1 : Continuous fun x => deriv (deriv f) x * g x :=
    (hf1.continuous_deriv le_rfl).mul hg.continuous
  have hcont2 : Continuous fun x => f x * deriv (deriv g) x :=
    hf.continuous.mul (hg1.continuous_deriv le_rfl)
  have hint := integral_eq_sub_of_hasDerivAt hF
    ((hcont1.sub hcont2).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub (hcont1.intervalIntegrable a b)
    (hcont2.intervalIntegrable a b)] at hint
  linear_combination hint

/-- DLMF 1.18.27 and §1.18(iii): with the boundary conditions `f(a) = f(b) = 0`,
`g(a) = g(b) = 0` the boundary terms of 1.18.26 vanish and `T = d²/dx²` is symmetric:
`∫_a^b f'' g = ∫_a^b f g''`. -/
@[dlmf 1.18.E27, dlmf 1.18.iii]
theorem integral_deriv2_mul_eq_of_dirichlet {a b : ℝ} {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hfa : f a = 0) (hfb : f b = 0) (hga : g a = 0) (hgb : g b = 0) :
    ∫ x in a..b, deriv (deriv f) x * g x = ∫ x in a..b, f x * deriv (deriv g) x := by
  rw [integral_deriv2_mul_eq hf hg, hfa, hfb, hga, hgb]
  ring

/-! ## §1.18(v): point spectra and eigenfunction expansions -/

section PointSpectrum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ι : Type*}

/-- A self-adjoint operator is symmetric. -/
private lemma isFormalAdjoint_self_of_isSelfAdjoint {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T) :
    T.IsFormalAdjoint T := by
  have h := LinearPMap.adjoint_isFormalAdjoint (T := T) hT.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hT] at h
  exact h

/-- DLMF 1.18.29–1.18.34: let `T` be self-adjoint with an orthonormal basis of eigenvectors
`φₙ`, `T φₙ = lam φₙ` (1.18.29, completeness 1.18.30). Then for `f ∈ 𝓓(T)`
`Tf = Σ lam f̂(lam) φₙ` with `f̂(lam) = ⟨f, φₙ⟩` (1.18.32, 1.18.34); the expansion of `f` itself
(1.18.31) and Parseval (1.18.33) are Mathlib's `HilbertBasis.hasSum_repr` and
`HilbertBasis.tsum_inner_mul_inner`. -/
@[dlmf 1.18.E29, dlmf 1.18.E30, dlmf 1.18.E31, dlmf 1.18.E34]
theorem hasSum_eigen_expansion {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T)
    (b : HilbertBasis ι ℂ E) (lam : ι → ℝ) (hmem : ∀ i, b i ∈ T.domain)
    (hb : ∀ i, T ⟨b i, hmem i⟩ = (lam i : ℂ) • b i) (f : T.domain) :
    HasSum (fun i => ((lam i : ℂ) * ⟪b i, (f : E)⟫_ℂ) • b i) (T f) := by
  have hs := b.hasSum_repr (T f)
  refine hs.congr_fun fun i => ?_
  rw [b.repr_apply_apply]
  congr 1
  have h := isFormalAdjoint_self_of_isSelfAdjoint hT ⟨b i, hmem i⟩ f
  simp only at h
  rw [← h, hb, inner_smul_left, conj_ofReal]

/-- DLMF 1.18.35 for the resolvent `F(λ) = (z - λ)⁻¹`: if `(z - T)u = f` with `z` not an
eigenvalue, then `u = Σ (z - lam)⁻¹ f̂(lam) φₙ`. -/
@[dlmf 1.18.E35]
theorem hasSum_resolvent_expansion {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T)
    (b : HilbertBasis ι ℂ E) (lam : ι → ℝ) (hmem : ∀ i, b i ∈ T.domain)
    (hb : ∀ i, T ⟨b i, hmem i⟩ = (lam i : ℂ) • b i) {z : ℂ} (hz : ∀ i, z ≠ lam i)
    (u : T.domain) (f : E) (hf : z • (u : E) - T u = f) :
    HasSum (fun i => ((z - lam i)⁻¹ * ⟪b i, f⟫_ℂ) • b i) (u : E) := by
  have hs := b.hasSum_repr (u : E)
  refine hs.congr_fun fun i => ?_
  rw [b.repr_apply_apply]
  congr 1
  have h := isFormalAdjoint_self_of_isSelfAdjoint hT ⟨b i, hmem i⟩ u
  simp only at h
  have hne : z - lam i ≠ 0 := sub_ne_zero.mpr (hz i)
  rw [← hf, inner_sub_right, inner_smul_right, ← h, hb, inner_smul_left, conj_ofReal]
  field_simp

end PointSpectrum

/-! ### Example 1: `q = 0` on `[0, π]` -/

/-- Identity under the stated parameter and domain assumptions: `deriv (fun x : ℝ => cexp (c * x))
= fun x : ℝ => c * cexp (c * x)`. -/
private lemma deriv_cexp_mul_ofReal (c : ℂ) :
    deriv (fun x : ℝ => cexp (c * x)) = fun x : ℝ => c * cexp (c * x) := by
  ext x
  have h : HasDerivAt (fun x : ℝ => c * (x : ℂ)) (c * 1) x :=
    ((hasDerivAt_id x).ofReal_comp).const_mul c
  have := h.cexp
  rw [this.deriv]; ring

/-- Identity under the stated parameter and domain assumptions: `deriv (fun x : ℝ => Complex.sin
(c * x)) = fun x : ℝ => c * Complex.cos (c * x)`. -/
private lemma deriv_csin_mul_ofReal (c : ℂ) :
    deriv (fun x : ℝ => Complex.sin (c * x)) = fun x : ℝ => c * Complex.cos (c * x) := by
  ext x
  have h : HasDerivAt (fun x : ℝ => c * (x : ℂ)) (c * 1) x :=
    ((hasDerivAt_id x).ofReal_comp).const_mul c
  rw [show (fun x : ℝ => Complex.sin (c * x)) = Complex.sin ∘ fun x : ℝ => c * (x : ℂ)
    from rfl, ((Complex.hasDerivAt_sin (c * x)).comp x h).deriv]
  ring

/-- Identity under the stated parameter and domain assumptions: `deriv (fun x : ℝ => Complex.cos
(c * x)) = fun x : ℝ => -(c * Complex.sin (c * x))`. -/
private lemma deriv_ccos_mul_ofReal (c : ℂ) :
    deriv (fun x : ℝ => Complex.cos (c * x)) = fun x : ℝ => -(c * Complex.sin (c * x)) := by
  ext x
  have h : HasDerivAt (fun x : ℝ => c * (x : ℂ)) (c * 1) x :=
    ((hasDerivAt_id x).ofReal_comp).const_mul c
  rw [show (fun x : ℝ => Complex.cos (c * x)) = Complex.cos ∘ fun x : ℝ => c * (x : ℂ)
    from rfl, ((Complex.hasDerivAt_cos (c * x)).comp x h).deriv]
  ring

/-- DLMF 1.18.36 (Case 1): `√(2/π) sin(nx)` satisfies `-φ'' = n² φ` with `φ(0) = φ(π) = 0`. -/
@[dlmf 1.18.E36]
theorem sinEigenfunction_spec (n : ℕ) :
    (∀ x, schrodingerOperator 0 (sinEigenfunction n) x = (n : ℂ) ^ 2 * sinEigenfunction n x) ∧
      sinEigenfunction n 0 = 0 ∧ sinEigenfunction n Real.pi = 0 := by
  have hf : sinEigenfunction n = fun x : ℝ =>
      (Real.sqrt (2 / Real.pi) : ℂ) * Complex.sin ((n : ℂ) * x) := by
    ext x; simp [sinEigenfunction]
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [schrodingerOperator, hf]
    simp only [deriv_const_mul_field', deriv_csin_mul_ofReal, deriv_ccos_mul_ofReal]
    simp
    ring
  · simp [sinEigenfunction]
  · simp only [sinEigenfunction, Complex.ofReal_eq_zero, mul_eq_zero]
    right
    exact_mod_cast Real.sin_nat_mul_pi n

/-- DLMF 1.18.36: the functions `√(2/π) sin(nx)`, `n ≥ 1`, are an orthonormal basis of
`L²(0, π)`. -/
@[dlmf 1.18.E36]
theorem sinEigenfunction_hilbertBasis :
    ∃ b : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 Real.pi))),
      ∀ n, (b n : ℝ → ℂ) =ᵐ[volume.restrict (Ioo 0 Real.pi)] sinEigenfunction (n + 1) := by
  sorry

/-- DLMF 1.18.37 (Case 2): `1/√π` and `√(2/π) cos(nx)` satisfy `-φ'' = n² φ` with
`φ'(0) = φ'(π) = 0`. -/
@[dlmf 1.18.E37]
theorem cosEigenfunction_spec (n : ℕ) :
    (∀ x, schrodingerOperator 0 (cosEigenfunction n) x = (n : ℂ) ^ 2 * cosEigenfunction n x) ∧
      deriv (cosEigenfunction n) 0 = 0 ∧ deriv (cosEigenfunction n) Real.pi = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : cosEigenfunction 0 = fun _ => ((1 / Real.sqrt Real.pi : ℝ) : ℂ) := by
      ext x; simp [cosEigenfunction]
    simp [h0, schrodingerOperator]
  have hf : cosEigenfunction n = fun x : ℝ =>
      (Real.sqrt (2 / Real.pi) : ℂ) * Complex.cos ((n : ℂ) * x) := by
    ext x; simp [cosEigenfunction, hn.ne']
  have hd : deriv (cosEigenfunction n) = fun x : ℝ =>
      (Real.sqrt (2 / Real.pi) : ℂ) * -((n : ℂ) * Complex.sin ((n : ℂ) * x)) := by
    rw [hf]; ext x; simp only [deriv_const_mul_field', deriv_ccos_mul_ofReal]
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [schrodingerOperator, hd, hf]
    simp
    rw [deriv_csin_mul_ofReal]
    ring
  · simp [hd]
  · rw [hd]
    have : Complex.sin ((n : ℂ) * (Real.pi : ℝ)) = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_sin]
      exact_mod_cast Real.sin_nat_mul_pi n
    simp [this]

/-- DLMF 1.18.37: the functions `1/√π`, `√(2/π) cos(nx)` (`n ≥ 1`) are an orthonormal basis
of `L²(0, π)`. -/
@[dlmf 1.18.E37]
theorem cosEigenfunction_hilbertBasis :
    ∃ b : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 Real.pi))),
      ∀ n, (b n : ℝ → ℂ) =ᵐ[volume.restrict (Ioo 0 Real.pi)] cosEigenfunction n := by
  sorry

/-- DLMF 1.18.38 (Case 3, periodic boundary conditions): `e^{±2inx}/√π` satisfies
`-φ'' = (2n)² φ` with `φ(0) = φ(π)`, `φ'(0) = φ'(π)`; each eigenvalue `4n²` with `n ≠ 0` has
multiplicity two. (DLMF does not print the eigenvalue of Case 3; it is `(2n)²`.) -/
@[dlmf 1.18.E38]
theorem expEigenfunction_spec (n : ℤ) :
    (∀ x, schrodingerOperator 0 (expEigenfunction n) x = (2 * n : ℂ) ^ 2 * expEigenfunction n x) ∧
      expEigenfunction n 0 = expEigenfunction n Real.pi ∧
      deriv (expEigenfunction n) 0 = deriv (expEigenfunction n) Real.pi := by
  have hf : expEigenfunction n = fun x : ℝ =>
      (1 / Real.sqrt Real.pi : ℂ) * cexp ((2 * I * n) * x) := by
    ext x; simp only [expEigenfunction]; ring_nf
  have hd : deriv (expEigenfunction n) = fun x : ℝ =>
      (1 / Real.sqrt Real.pi : ℂ) * ((2 * I * n) * cexp ((2 * I * n) * x)) := by
    rw [hf]; ext x
    rw [deriv_const_mul _ (by fun_prop), deriv_cexp_mul_ofReal]
  have hpi : cexp ((2 * I * n) * (Real.pi : ℝ)) = 1 := by
    rw [show (2 * I * n) * ((Real.pi : ℝ) : ℂ) = n * (2 * Real.pi * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  refine ⟨fun x => ?_, ?_, ?_⟩
  · have hdd : deriv (deriv (expEigenfunction n)) x =
        (1 / Real.sqrt Real.pi : ℂ) * ((2 * I * n) * ((2 * I * n) * cexp ((2 * I * n) * x))) := by
      rw [hd, deriv_const_mul _ (by fun_prop), deriv_const_mul _ (by fun_prop),
        deriv_cexp_mul_ofReal]
    rw [schrodingerOperator, hdd, hf]
    simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero]
    ring_nf; rw [I_sq]; ring
  · rw [hf]; simp [hpi]
  · rw [hd]; simp [hpi]

/-- DLMF 1.18.38–1.18.40: the functions `e^{2inx}/√π`, `n ∈ ℤ`, are an orthonormal basis of
`L²(0, π)`; hence `f = Σ f̂(lam) e^{2inx}/√π` in `L²` with
`f̂(lam) = π^{-1/2} ∫_0^π f(y) e^{-2iny} dy` (1.18.40), the meaning of the completeness relation
`δ(x - y) = π⁻¹ Σ e^{2in(x-y)}` (1.18.39). On the circle `ℝ/πℤ` this is Mathlib's
`fourierBasis`. -/
@[dlmf 1.18.E38, dlmf 1.18.E39, dlmf 1.18.E40]
theorem expEigenfunction_hilbertBasis :
    ∃ b : HilbertBasis ℤ ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 Real.pi))),
      ∀ n, (b n : ℝ → ℂ) =ᵐ[volume.restrict (Ioo 0 Real.pi)] expEigenfunction n := by
  sorry

/-! ### Hermite's equation on `ℝ` -/

/-- DLMF 1.18.41–1.18.42: the Hermite functions satisfy
`-φₙ'' + x² φₙ = (2n + 1) φₙ`. -/
@[dlmf 1.18.E41, dlmf 1.18.E42]
theorem hermiteFunction_eigen (n : ℕ) (x : ℝ) :
    hermiteOperator (fun x : ℝ => (TauCeti.hermiteFunction n x : ℂ)) x =
      (2 * n + 1 : ℂ) * TauCeti.hermiteFunction n x := by
  have hd : deriv (fun x : ℝ => (TauCeti.hermiteFunction n x : ℂ)) =
      fun x : ℝ => ((deriv (TauCeti.hermiteFunction n) x : ℝ) : ℂ) := by
    funext y
    exact ((TauCeti.hasDerivAt_hermiteFunction n y).differentiableAt.hasDerivAt.ofReal_comp).deriv
  rw [hermiteOperator, schrodingerOperator, hd,
    (TauCeti.hasDerivAt_deriv_hermiteFunction n x).ofReal_comp.deriv]
  push_cast
  ring

/-- DLMF 1.18.42–1.18.43: the Hermite functions are an orthonormal basis of `L²(ℝ)`; hence
`f = Σₙ (∫ φₙ(y) f(y) dy) φₙ` in `L²` for `f ∈ L²(ℝ)` (1.18.43, convergence as in §1.18(ii)). -/
@[dlmf 1.18.E42, dlmf 1.18.E43]
theorem hermiteFunction_hilbertBasis :
    ∃ b : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)),
      ∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => (TauCeti.hermiteFunction n x : ℂ) := by
  refine ⟨TauCeti.hermiteHilbertBasis ℂ, fun n => ?_⟩
  rw [congrFun (TauCeti.coe_hermiteHilbertBasis ℂ) n]
  simpa using TauCeti.coeFn_hermiteFunctionLp (𝕜 := ℂ) n

/-! ## §1.18(vi), §1.18(viii): continuous and mixed spectra -/

section Transform

variable {X : Set ℝ} {ν : Measure ℝ} {φ : ℝ → ℝ → ℂ}
  {U : Lp ℂ 2 (volume.restrict X) ≃ₗᵢ[ℂ] Lp ℂ 2 ν}

/-- DLMF 1.18.48 and 1.18.65 (Plancherel): `∫_X |f|² = ∫ |f̂(λ)|² dν(λ)`, that is
`∫_X |f|² = ∫_{σ_c} |f̂(λ)|² dλ + Σ_{σ_p} |f̂(lam)|²` for the spectral measure `ν` of
`IsEigenfunctionTransform`, for compactly supported continuous `f`. -/
@[dlmf 1.18.E48, dlmf 1.18.E65]
theorem IsEigenfunctionTransform.integral_norm_sq (hU : IsEigenfunctionTransform X ν φ U)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict X)) (hc : Continuous f)
    (hcs : HasCompactSupport f) (hX : tsupport f ⊆ X) :
    ∫ x in X, ‖f x‖ ^ 2 = ∫ μ, ‖eigenCoeff X φ f μ‖ ^ 2 ∂ν := by
  rw [hf.integral_norm_sq_eq_norm_toLp_sq, ← U.norm_map (hf.toLp f),
    ← Lp.integral_norm_sq_eq_norm_sq (U (hf.toLp f))]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hU f hf hc hcs hX] with t ht
  rw [ht]

/-- DLMF 1.18.46 and 1.18.64 (eigenfunction expansion):
`f(x) = ∫_{σ_c} f̂(λ) φ_λ(x) dλ + Σ_{σ_p} f̂(lam) φ_{lam}(x)` for almost every `x ∈ X`, for
compactly supported continuous `f` whose coefficient `f̂` is `ν`-integrable against the
(locally bounded) eigenfunctions. -/
@[dlmf 1.18.E46, dlmf 1.18.E64]
theorem IsEigenfunctionTransform.ae_eq_integral (hU : IsEigenfunctionTransform X ν φ U)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict X)) (hc : Continuous f)
    (hcs : HasCompactSupport f) (hX : tsupport f ⊆ X)
    (hint : ∀ᵐ x ∂(volume.restrict X),
      Integrable (fun μ => eigenCoeff X φ f μ * φ μ x) ν) :
    ∀ᵐ x ∂(volume.restrict X), f x = ∫ μ, eigenCoeff X φ f μ * φ μ x ∂ν := by
  sorry

/-- DLMF 1.18.49 and 1.18.51 with `F(λ) = λ`: if `U` diagonalizes `T`, then
`⟨Tf, f⟩ = ∫ λ |f̂(λ)|² dν(λ)` for `f ∈ 𝓓(T)` (in Mathlib's convention
`⟨Tf, f⟩ = ⟪f, Tf⟫`). -/
@[dlmf 1.18.E49, dlmf 1.18.E51]
theorem IsDiagonalizedBy.inner_apply
    {T : Lp ℂ 2 (volume.restrict X) →ₗ.[ℂ] Lp ℂ 2 (volume.restrict X)}
    (hT : IsDiagonalizedBy T U) (f : T.domain) :
    ⟪(f : Lp ℂ 2 (volume.restrict X)), T f⟫_ℂ =
      ∫ μ, (μ : ℂ) * ‖(U f : ℝ → ℂ) μ‖ ^ 2 ∂ν := by
  rw [← U.inner_map_map, L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hT f] with t ht
  rw [ht, ← smul_eq_mul, inner_smul_right, inner_self_eq_norm_sq_to_K]
  rfl

/-- DLMF 1.18.52 and 1.18.66 (matrix elements of the resolvent): if `U` diagonalizes `T`,
`z ∉ σ` and `(z - T)u = f`, then `⟨(z - T)⁻¹ f, f⟩ = ⟨u, f⟩ = ∫ |f̂(λ)|² dν(λ)/(z - λ)`, which
for the mixed spectral measure is
`Σ_{σ_p} |f̂(lam)|²/(z - lam) + ∫_{σ_c} |f̂(λ)|² dλ/(z - λ)`. -/
@[dlmf 1.18.E52, dlmf 1.18.E66]
theorem IsDiagonalizedBy.inner_resolvent
    {T : Lp ℂ 2 (volume.restrict X) →ₗ.[ℂ] Lp ℂ 2 (volume.restrict X)}
    (hT : IsDiagonalizedBy T U) {z : ℂ} (hz : ∀ᵐ t ∂ν, z ≠ ((t : ℝ) : ℂ)) (u : T.domain)
    (f : Lp ℂ 2 (volume.restrict X)) (hf : z • (u : Lp ℂ 2 (volume.restrict X)) - T u = f) :
    ⟪f, (u : Lp ℂ 2 (volume.restrict X))⟫_ℂ =
      ∫ μ, ‖(U f : ℝ → ℂ) μ‖ ^ 2 / (z - μ) ∂ν := by
  have hUf : U f = z • U (u : Lp ℂ 2 (volume.restrict X)) - U (T u) := by
    rw [← hf]
    simp only [map_sub, map_smul]
  rw [← U.inner_map_map, L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hz, hT u,
    Lp.coeFn_sub (z • U (u : Lp ℂ 2 (volume.restrict X))) (U (T u)),
    Lp.coeFn_smul z (U (u : Lp ℂ 2 (volume.restrict X)))] with t hzt hTu hsub hsmul
  have hval : (U f : ℝ → ℂ) t = (z - t) * (U u : ℝ → ℂ) t := by
    rw [hUf, hsub, Pi.sub_apply, hsmul, hTu]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hu : (U u : ℝ → ℂ) t = (U f : ℝ → ℂ) t / (z - t) := by
    rw [hval]
    exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr hzt)).symm
  rw [hu, div_eq_inv_mul, ← smul_eq_mul, inner_smul_right, inner_self_eq_norm_sq_to_K]
  rw [mul_comm]
  rfl

end Transform

/-- DLMF 1.18.53 (Stieltjes inversion): for `h ∈ L¹(ℝ)` continuous at `μ` and
`G(z) = ∫ h(λ) dλ/(z - λ)` (the right side of 1.18.52 with `h = |f̂|²`),
`lim_{ν→0+} (2πi)⁻¹ (G(μ - iν) - G(μ + iν)) = h(μ)`; in particular it is `0` when `h`
vanishes near `μ` (`μ ∉ σ_c`). -/
@[dlmf 1.18.E53]
theorem tendsto_stieltjes_inversion {h : ℝ → ℝ} (hh : Integrable h) {μ : ℝ}
    (hc : ContinuousAt h μ) :
    Tendsto (fun ν : ℝ => (1 / (2 * Real.pi * I)) *
      ((∫ t : ℝ, (h t : ℂ) / ((μ : ℂ) - ν * I - t)) -
        ∫ t : ℝ, (h t : ℂ) / ((μ : ℂ) + ν * I - t))) (𝓝[>] 0) (𝓝 (h μ)) := by
  have hg : Integrable fun t => (h t : ℂ) := hh.ofReal
  have hcc : Tendsto (fun t => (h t : ℂ)) (𝓝 μ) (𝓝 (h μ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hc.tendsto
  have hP := Real.tendsto_integral_poissonKernelLine_mul hg (hcc.mono_left nhdsWithin_le_nhds)
    (hcc.mono_left nhdsWithin_le_nhds)
  rw [← two_mul, mul_div_cancel_left₀ _ two_ne_zero] at hP
  refine hP.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ν (hν : 0 < ν)
  have hint : ∀ c : ℂ, c.im ≠ 0 → Integrable fun t : ℝ => (h t : ℂ) / (c - t) := by
    intro c hc0
    have hne : ∀ t : ℝ, c - t ≠ 0 := fun t ht => hc0 (by simpa using congrArg Complex.im ht)
    have hb := hg.bdd_mul (c := 1 / |c.im|)
      (f := fun t : ℝ => (c - t)⁻¹) (Continuous.inv₀ (by fun_prop) hne).aestronglyMeasurable
      (Eventually.of_forall fun t => by
        rw [norm_inv, ← one_div]
        gcongr
        simpa using Complex.abs_im_le_norm (c - t))
    refine hb.congr (Eventually.of_forall fun t => ?_)
    simp only; rw [div_eq_inv_mul]
  have h1 : ((μ : ℂ) - ν * I).im ≠ 0 := by simp; exact hν.ne'
  have h2 : ((μ : ℂ) + ν * I).im ≠ 0 := by simp; exact hν.ne'
  rw [← MeasureTheory.integral_sub (hint _ h1) (hint _ h2), ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have d1 : (μ : ℂ) - ν * I - t ≠ 0 := fun ht => h1 (by simpa using congrArg Complex.im ht)
  have d2 : (μ : ℂ) + ν * I - t ≠ 0 := fun ht => h2 (by simpa using congrArg Complex.im ht)
  have hprod : ((μ : ℂ) - ν * I - t) * ((μ : ℂ) + ν * I - t) = ((t - μ) ^ 2 + ν ^ 2 : ℝ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have hpos : (((t - μ) ^ 2 + ν ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; positivity
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [Real.poissonKernelLine]
  rw [div_sub_div _ _ d1 d2, hprod]
  push_cast
  field_simp
  ring_nf


/-- The integral of an odd function vanishes. -/
private lemma integral_eq_zero_of_odd {F : ℝ → ℂ} (hF : ∀ u, F (-u) = -F u) :
    ∫ u, F u = 0 := by
  have h := integral_neg_eq_self F volume
  simp only [hF, MeasureTheory.integral_neg] at h
  linear_combination -h / 2

/-- The integral of an odd function over a symmetric set vanishes. -/
private lemma integral_indicator_eq_zero_of_odd {T : Set ℝ} (hT : ∀ u, -u ∈ T ↔ u ∈ T)
    {k : ℝ → ℂ} (hk : ∀ u, k (-u) = -k u) : ∫ u, T.indicator k u = 0 :=
  integral_eq_zero_of_odd fun u => by
    by_cases hu : u ∈ T
    · rw [indicator_of_mem ((hT u).2 hu), indicator_of_mem hu, hk]
    · rw [indicator_of_notMem (mt (hT u).1 hu), indicator_of_notMem hu, neg_zero]

/-- DLMF 1.18.54 (Sokhotski–Plemelj):
`lim_{ε→0+} ∫ f(y)/(x ± iε - y) dy = ⨍ f(y)/(x - y) dy ∓ iπ f(x)`.

DLMF assumes only `f ∈ C(X)`; continuity alone does not make the principal value exist, and
the statement is made for continuously differentiable `f` with compact support on `X = ℝ`
(Hölder continuity at `x` and integrability suffice). The principal value is the limit of
the integrals over `|x - y| > δ`. -/
@[dlmf 1.18.E54]
theorem tendsto_sokhotski_plemelj {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f)
    (x : ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∃ pv : ℂ, Tendsto (fun δ : ℝ => ∫ y in {y : ℝ | δ < |x - y|}, f y / (x - y)) (𝓝[>] 0)
        (𝓝 pv) ∧
      Tendsto (fun ε : ℝ => ∫ y : ℝ, f y / ((x : ℂ) + s * ε * I - y)) (𝓝[>] 0)
        (𝓝 (pv - s * Real.pi * I * f x)) := by
  have hfc : Continuous f := hf.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hf one_ne_zero
  obtain ⟨R, hR0, hRs⟩ : ∃ R : ℝ, 0 < R ∧ ∀ u : ℝ, R < |u| → f (x - u) = 0 := by
    obtain ⟨r, hr⟩ := hcs.isCompact.isBounded.subset_closedBall x
    refine ⟨max r 1, by positivity, fun u hu => ?_⟩
    by_contra hne
    have h1 := hr (subset_tsupport f hne)
    rw [Metric.mem_closedBall, Real.dist_eq, show x - u - x = -u by ring, abs_neg] at h1
    linarith [le_max_left r 1]
  set G : ℝ → ℂ := fun u => (f (x - u) - f x) / u with hG
  have hGb : ∀ u, ‖G u‖ ≤ L := by
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · simp [hG]
    have h := hL.dist_le_mul (x - u) x
    rw [dist_eq_norm, dist_eq_norm, show x - u - x = -u by ring, norm_neg,
      Real.norm_eq_abs] at h
    simp only [hG, norm_div, Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_iff₀ (abs_pos.2 hu)]
    exact h
  have hGm : Measurable G := by simp only [hG]; fun_prop
  set B : Set ℝ := Icc (-R) R with hB
  have hBm : MeasurableSet B := measurableSet_Icc
  have hBi : ∀ c : ℝ, Integrable (B.indicator fun _ : ℝ => c) :=
    fun c => (integrable_indicator_iff hBm).2 (integrableOn_const measure_Icc_lt_top.ne)
  have hBG : ∀ (S : Set ℝ), MeasurableSet S → ∀ k : ℝ → ℂ, Measurable k → (∀ u, ‖k u‖ ≤ 1) →
      Integrable ((S ∩ B).indicator fun u => G u * k u) := by
    intro S hS k hk hk1
    refine (hBi L).mono' ((hGm.mul hk).indicator (hS.inter hBm)).aestronglyMeasurable ?_
    · refine Eventually.of_forall fun u => ?_
      by_cases hu : u ∈ S ∩ B
      · rw [indicator_of_mem hu, indicator_of_mem hu.2, norm_mul]
        simpa using mul_le_mul (hGb u) (hk1 u) (norm_nonneg _) (by
          have := hGb u; exact (norm_nonneg _).trans this)
      · rw [indicator_of_notMem hu, norm_zero]
        by_cases hb : u ∈ B
        · rw [indicator_of_mem hb]
          exact L.2
        · rw [indicator_of_notMem hb]
  set pv : ℂ := ∫ u, B.indicator G u with hpv
  have hBsymm : ∀ u, -u ∈ B ↔ u ∈ B := fun u => by
    simp only [hB, mem_Icc]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hlimG : ∀ (k : ℝ → ℝ → ℂ), (∀ δ, 0 < δ → Measurable (k δ)) →
      (∀ δ, 0 < δ → ∀ u, ‖k δ u‖ ≤ 1) →
      (∀ u, u ≠ 0 → Tendsto (fun δ => k δ u) (𝓝[>] 0) (𝓝 1)) →
      ∀ (T : ℝ → Set ℝ), (∀ δ, 0 < δ → MeasurableSet (T δ)) →
      (∀ u, u ≠ 0 → ∀ᶠ δ in 𝓝[>] 0, u ∈ T δ) →
      Tendsto (fun δ => ∫ u, (T δ ∩ B).indicator (fun u => G u * k δ u) u) (𝓝[>] 0)
        (𝓝 pv) := by
    intro k hkm hk1 hk T hTm hT
    refine tendsto_integral_filter_of_dominated_convergence (B.indicator fun _ => (L : ℝ))
      ?_ ?_ (hBi L) ?_
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      exact (hBG _ (hTm δ hδ) _ (hkm δ hδ) (hk1 δ hδ)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      refine Eventually.of_forall fun u => ?_
      by_cases hu : u ∈ T δ ∩ B
      · rw [indicator_of_mem hu, indicator_of_mem hu.2, norm_mul]
        calc ‖G u‖ * ‖k δ u‖ ≤ L * 1 :=
              mul_le_mul (hGb u) (hk1 δ hδ u) (norm_nonneg _) L.2
          _ = L := mul_one _
      · rw [indicator_of_notMem hu, norm_zero]
        by_cases hb : u ∈ B
        · rw [indicator_of_mem hb]; exact L.2
        · rw [indicator_of_notMem hb]
    · filter_upwards [Measure.ae_ne volume 0] with u hu
      by_cases hb : u ∈ B
      · have h := (hk u hu).const_mul (G u)
        rw [mul_one] at h
        rw [indicator_of_mem hb]
        refine h.congr' ?_
        filter_upwards [hT u hu] with δ hδ
        rw [indicator_of_mem (show u ∈ T δ ∩ B from ⟨hδ, hb⟩)]
      · rw [indicator_of_notMem hb]
        exact tendsto_const_nhds.congr fun δ =>
          (indicator_of_notMem (fun (h : u ∈ T δ ∩ B) => hb h.2) _).symm
  refine ⟨pv, ?_, ?_⟩
  · set T : ℝ → Set ℝ := fun δ => {u : ℝ | δ < |u|} with hT
    have hTm : ∀ δ, MeasurableSet (T δ) := fun δ =>
      measurableSet_lt measurable_const continuous_abs.measurable
    have h := hlimG (fun _ _ => 1) (fun _ _ => measurable_const) (fun _ _ _ => by simp)
      (fun _ _ => tendsto_const_nhds) T (fun δ _ => hTm δ) (fun u hu => by
        filter_upwards [Ioo_mem_nhdsGT (abs_pos.2 hu)] with δ hδ
        exact hδ.2)
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hR0] with δ hδ
    have hS : MeasurableSet {y : ℝ | δ < |x - y|} :=
      measurableSet_lt measurable_const (by fun_prop)
    rw [← MeasureTheory.integral_indicator hS, ← integral_sub_left_eq_self
      ({y : ℝ | δ < |x - y|}.indicator fun y => f y / ((x : ℂ) - y)) volume x]
    have hi2 : Integrable ((T δ ∩ B).indicator fun u => f x / u) := by
      refine (hBi (‖f x‖ / δ)).mono'
        ((by fun_prop : Measurable fun u : ℝ => f x / u).indicator
          ((hTm δ).inter hBm)).aestronglyMeasurable ?_
      refine Eventually.of_forall fun u => ?_
      by_cases hu : u ∈ T δ ∩ B
      · rw [indicator_of_mem hu, indicator_of_mem hu.2, norm_div, Complex.norm_real,
          Real.norm_eq_abs]
        have h1 : δ < |u| := hu.1
        exact div_le_div_of_nonneg_left (norm_nonneg _) hδ.1 h1.le
      · rw [indicator_of_notMem hu, norm_zero]
        by_cases hb : u ∈ B
        · rw [indicator_of_mem hb]; exact div_nonneg (norm_nonneg _) hδ.1.le
        · rw [indicator_of_notMem hb]
    have hodd := integral_indicator_eq_zero_of_odd (T := T δ ∩ B)
      (fun u => by simp only [mem_inter_iff, hT, mem_ofPred_eq, abs_neg, hBsymm])
      (k := fun u => f x / u) (fun u => by push_cast; ring)
    rw [← add_zero (∫ u, (T δ ∩ B).indicator (fun u => G u * 1) u), ← hodd,
      ← MeasureTheory.integral_add (hBG _ (hTm δ) _ measurable_const (fun _ => by simp)) hi2]
    congr 1; funext u
    simp only [mul_one]
    by_cases hu : u ∈ T δ
    · have hu' : δ < |u| := hu
      have hu0 : u ≠ 0 := fun h => by rw [h, abs_zero] at hu'; linarith [hδ.1]
      have hmem : x - u ∈ {y : ℝ | δ < |x - y|} := by simpa using hu'
      rw [indicator_of_mem hmem]
      by_cases hb : u ∈ B
      · rw [indicator_of_mem (show u ∈ T δ ∩ B from ⟨hu, hb⟩),
          indicator_of_mem (show u ∈ T δ ∩ B from ⟨hu, hb⟩)]
        have : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu0
        simp only [hG]
        rw [← add_div, sub_add_cancel]
        push_cast
        ring
      · rw [indicator_of_notMem (fun (h : u ∈ T δ ∩ B) => hb h.2),
          indicator_of_notMem (fun (h : u ∈ T δ ∩ B) => hb h.2)]
        have hbu : R < |u| := by
          simp only [hB, mem_Icc, not_and_or, not_le] at hb
          rcases hb with hb | hb
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        rw [hRs u hbu, zero_div, add_zero]
    · have hu' : ¬ δ < |u| := hu
      have hmem : x - u ∉ {y : ℝ | δ < |x - y|} := by simpa using hu'
      rw [indicator_of_notMem hmem, indicator_of_notMem (fun (h : u ∈ T δ ∩ B) => hu h.1),
        indicator_of_notMem (fun (h : u ∈ T δ ∩ B) => hu h.1), add_zero]
  · have hs2 : (s : ℂ) ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    set k : ℝ → ℝ → ℂ := fun ε u => ((u ^ 2 / (u ^ 2 + ε ^ 2) : ℝ) : ℂ) with hk
    have hkm : ∀ ε, 0 < ε → Measurable (k ε) := fun ε _ => by simp only [hk]; fun_prop
    have hk1 : ∀ ε, 0 < ε → ∀ u, ‖k ε u‖ ≤ 1 := by
      intro ε hε u
      simp only [hk, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
      nlinarith [sq_nonneg ε]
    have hk0 : ∀ u, u ≠ 0 → Tendsto (fun ε => k ε u) (𝓝[>] 0) (𝓝 1) := by
      intro u hu
      have hpos : 0 < u ^ 2 := by positivity
      have hc : ContinuousAt (fun ε : ℝ => ((u ^ 2 / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) 0 :=
        (Complex.continuous_ofReal.comp (continuous_const.div (by fun_prop)
          fun ε => by positivity)).continuousAt
      have h := hc.tendsto
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
        div_self hpos.ne', ofReal_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h1 := hlimG k hkm hk1 hk0 (fun _ => univ) (fun _ _ => MeasurableSet.univ)
      (fun _ _ => Eventually.of_forall fun _ => mem_univ _)
    simp only [univ_inter] at h1
    -- the Poisson part
    have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hcs
    have hgi : Integrable fun u => f (x - u) := hfi.comp_sub_left x
    have hgc : Tendsto (fun u => f (x - u)) (𝓝 0) (𝓝 (f x)) := by
      have := ((by fun_prop : Continuous fun u : ℝ => f (x - u)).tendsto 0)
      simpa using this
    have h3 := Real.tendsto_integral_poissonKernelLine_mul hgi
      (hgc.mono_left nhdsWithin_le_nhds) (hgc.mono_left nhdsWithin_le_nhds)
    rw [← two_mul, mul_div_cancel_left₀ _ two_ne_zero] at h3
    have hlim := h1.sub (h3.const_mul ((s : ℂ) * Real.pi * I))
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    -- the odd part
    have hi2 : Integrable (B.indicator fun u => f x * ((u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) := by
      refine (hBi (‖f x‖ / ε)).mono'
        ((by fun_prop : Measurable fun u : ℝ => f x * ((u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)).indicator
          hBm).aestronglyMeasurable ?_
      refine Eventually.of_forall fun u => ?_
      by_cases hb : u ∈ B
      · rw [indicator_of_mem hb, indicator_of_mem hb, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < u ^ 2 + ε ^ 2),
          div_eq_mul_inv (‖f x‖)]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hε]
        nlinarith [sq_nonneg (|u| - ε), sq_abs u]
      · rw [indicator_of_notMem hb, indicator_of_notMem hb, norm_zero]
    have hodd := integral_indicator_eq_zero_of_odd (T := B) hBsymm
      (k := fun u => f x * ((u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) (fun u => by push_cast; ring)
    have hi3 : Integrable fun u => (Real.poissonKernelLine 0 ε u : ℂ) * f (x - u) :=
      hgi.bdd_mul (c := 1 / (Real.pi * ε))
        (Complex.continuous_ofReal.comp
          (Real.continuous_poissonKernelLine 0 hε)).aestronglyMeasurable
        (Eventually.of_forall fun t => by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.poissonKernelLine_nonneg 0 hε t)]
          exact Real.poissonKernelLine_le 0 hε t)
    have hi1 := hBG univ MeasurableSet.univ (k ε) (hkm ε hε) (hk1 ε hε)
    simp only [univ_inter] at hi1
    have hi12 : Integrable fun u => B.indicator (fun u => G u * k ε u) u +
        B.indicator (fun u => f x * ((u / (u ^ 2 + ε ^ 2) : ℝ) : ℂ)) u := hi1.add hi2
    rw [← add_zero (∫ u, B.indicator (fun u => G u * k ε u) u), ← hodd,
      ← MeasureTheory.integral_add hi1 hi2, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub hi12
        (hi3.const_mul _), ← integral_sub_left_eq_self
        (fun y => f y / ((x : ℂ) + s * ε * I - y)) volume x]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    have hD : ((u ^ 2 + ε ^ 2 : ℝ) : ℂ) ≠ 0 := by
      rw [ofReal_ne_zero]; positivity
    have hden : (x : ℂ) + s * ε * I - ((x - u : ℝ) : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rcases hs with rfl | rfl <;> simp at this <;> linarith
    have hinv : 1 / ((x : ℂ) + s * ε * I - ((x - u : ℝ) : ℂ)) =
        (u - s * ε * I) / ((u ^ 2 + ε ^ 2 : ℝ) : ℂ) := by
      rw [div_eq_div_iff hden hD]
      push_cast
      ring_nf
      rw [I_sq, hs2]
      ring
    have hGu : G u * (u : ℂ) ^ 2 = (f (x - u) - f x) * u := by
      rcases eq_or_ne u 0 with rfl | hu
      · simp
      have : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu
      simp only [hG]
      field_simp
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    rw [div_eq_mul_one_div, hinv]
    by_cases hb : u ∈ B
    · rw [indicator_of_mem hb, indicator_of_mem hb]
      clear_value G
      generalize G u = g at hGu ⊢
      simp only [hk, Real.poissonKernelLine, sub_zero]
      push_cast at hD ⊢
      field_simp
      linear_combination hGu
    · rw [indicator_of_notMem hb, indicator_of_notMem hb]
      have hbu : R < |u| := by
        simp only [hB, mem_Icc, not_and_or, not_le] at hb
        rcases hb with hb | hb
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [hRs u hbu]
      ring


/-- DLMF 1.18.55: `√x J_ν(x√λ)` is an eigenfunction of the Bessel operator with eigenvalue
`λ ≥ 0` on `(0, ∞)` (real `ν`, Mathlib's `Complex.besselJ`, principal powers). -/
@[dlmf 1.18.E55]
theorem besselOperator_sqrt_mul_besselJ (ν : ℝ) {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx : 0 < x) :
    besselOperator ν (fun y => (Real.sqrt y : ℂ) * Complex.besselJ ν (y * Real.sqrt t)) x =
      (t : ℂ) * ((Real.sqrt x : ℂ) * Complex.besselJ ν (x * Real.sqrt t)) := by
  set s := Real.sqrt t with hs
  set J := Complex.besselJ (ν : ℂ) with hJ
  have hs0 : 0 ≤ s := Real.sqrt_nonneg t
  have hst : (s : ℂ) ^ 2 = t := by
    rw [← Complex.ofReal_pow, hs, Real.sq_sqrt ht]
  -- derivatives of `y ↦ J(ys)` and `y ↦ J'(ys)`, also valid for `s = 0`
  have hcomp : ∀ (G : ℂ → ℂ), (∀ w ∈ slitPlane, AnalyticAt ℂ G w) → ∀ y : ℝ, 0 < y →
      HasDerivAt (fun y : ℝ => G (y * s)) (deriv G (y * s) * s) y := by
    intro G hG y hy
    rcases hs0.eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [Complex.ofReal_zero, mul_zero]
      exact hasDerivAt_const _ _
    · have hw : (y : ℂ) * s ∈ slitPlane := by
        rw [← Complex.ofReal_mul]; exact Complex.ofReal_mem_slitPlane.mpr (mul_pos hy hpos)
      have h := (hG _ hw).differentiableAt.hasDerivAt.comp (y : ℂ)
        ((hasDerivAt_id (y : ℂ)).mul_const (s : ℂ))
      simp only [id, one_mul] at h
      exact h.comp_ofReal
  have hJa : ∀ w ∈ slitPlane, AnalyticAt ℂ J w := fun w hw => analyticAt_besselJ _ hw
  have hJ'a : ∀ w ∈ slitPlane, AnalyticAt ℂ (deriv J) w := fun w hw => (hJa w hw).deriv
  have hsq : ∀ y : ℝ, 0 < y →
      HasDerivAt (fun y : ℝ => (Real.sqrt y : ℂ)) (((1 / (2 * Real.sqrt y) : ℝ)) : ℂ) y :=
    fun y hy => (Real.hasDerivAt_sqrt hy.ne').ofReal_comp
  set g1 : ℝ → ℂ := fun y => ((1 / (2 * Real.sqrt y) : ℝ) : ℂ) * J (y * s) +
    (Real.sqrt y : ℂ) * (deriv J (y * s) * s) with hg1
  have hfirst : ∀ y : ℝ, 0 < y →
      HasDerivAt (fun y => (Real.sqrt y : ℂ) * J (y * s)) (g1 y) y :=
    fun y hy => (hsq y hy).mul (hcomp J hJa y hy)
  have hderiv : deriv (fun y => (Real.sqrt y : ℂ) * J (y * s)) =ᶠ[𝓝 x] g1 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (hfirst y hy).deriv
  have hr : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hinv : HasDerivAt (fun y : ℝ => ((1 / (2 * Real.sqrt y) : ℝ) : ℂ))
      (((0 * (2 * Real.sqrt x) - 1 * (2 * (1 / (2 * Real.sqrt x)))) /
        (2 * Real.sqrt x) ^ 2 : ℝ) : ℂ) x :=
    ((hasDerivAt_const x (1 : ℝ)).div ((Real.hasDerivAt_sqrt hx.ne').const_mul 2)
      (by positivity)).ofReal_comp
  have hsecond : HasDerivAt g1 _ x := (hinv.mul (hcomp J hJa x hx)).add
    ((hsq x hx).mul ((hcomp (deriv J) hJ'a x hx).mul_const (s : ℂ)))
  have hode : ((x : ℂ) * s) ^ 2 * deriv (deriv J) (x * s) + (x * s) * deriv J (x * s) +
      (((x : ℂ) * s) ^ 2 - (ν : ℂ) ^ 2) * J (x * s) = 0 := by
    rcases hs0.eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [Complex.ofReal_zero, mul_zero, hJ, Complex.besselJ_zero]
      split_ifs with h <;> simp [h]
    · have hw : (x : ℂ) * s ∈ slitPlane := by
        rw [← Complex.ofReal_mul]; exact Complex.ofReal_mem_slitPlane.mpr (mul_pos hx hpos)
      have := DLMF.Bessel.besselJ_ode (ν := (ν : ℂ)) hw
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using this
  unfold besselOperator schrodingerOperator
  rw [hderiv.deriv_eq, hsecond.deriv]
  have hxr : ((Real.sqrt x : ℝ) : ℂ) ^ 2 = x := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hx.le]
  have hr0 : ((Real.sqrt x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [← hst]
  push_cast
  rw [← hxr] at hode ⊢
  field_simp
  linear_combination (-16 : ℂ) * hode

/-- DLMF 1.18.56–1.18.58 (Hankel transform): for `ν > -1`, `x > 0` and `f` piecewise
continuously differentiable on `(0, ∞)` (here: `C¹` on each side of `x` near `x`, with one-sided
limits `f(x±)`, locally integrable) satisfying 1.18.58,
`lim_{R→∞} ∫_0^∞ f(y) (∫_0^R √(xt) J_ν(xt) √(yt) J_ν(yt) dt) dy = ½(f(x+) + f(x-))`
(Li and Wong 2008, §3, Thm. 1); this is the meaning of the completeness relation 1.18.56. -/
@[dlmf 1.18.E56, dlmf 1.18.E57, dlmf 1.18.E58]
theorem tendsto_hankel_kernel {ν : ℝ} (hν : -1 < ν) {f : ℝ → ℂ} {x : ℝ} (hx : 0 < x)
    {fm fp : ℂ} (hloc : LocallyIntegrableOn f (Ioi 0))
    (h1 : IntegrableOn (fun y => ‖f y‖ / y) (Ioi 1))
    (h2 : IntegrableOn (fun y => (1 + y ^ (ν + 1 / 2)) * ‖f y‖) (Ioc 0 1))
    (hpw : ∃ δ > 0, ContDiffOn ℝ 1 f (Ioo (x - δ) x) ∧ ContDiffOn ℝ 1 f (Ioo x (x + δ)) ∧
      BddAbove ((fun y => ‖deriv f y‖) '' (Ioo (x - δ) x ∪ Ioo x (x + δ))))
    (hm : Tendsto f (𝓝[<] x) (𝓝 fm)) (hp : Tendsto f (𝓝[>] x) (𝓝 fp)) :
    Tendsto (fun R : ℝ => ∫ y in Ioi 0, f y * ∫ t in (0 : ℝ)..R,
      (Real.sqrt (x * t) : ℂ) * Complex.besselJ ν (x * t) * (Real.sqrt (y * t) : ℂ) *
        Complex.besselJ ν (y * t)) atTop (𝓝 ((1 / 2 : ℂ) * (fp + fm))) := by
  sorry

/-- `∫₀^R (cos(xt) cos(yt) + sin(xt) sin(yt)) dt = sin(R(x - y))/(x - y)` for `x ≠ y`. -/
private lemma integral_cos_mul_cos_add_sin_mul_sin {x y : ℝ} (h : x - y ≠ 0) (R : ℝ) :
    ∫ t in (0 : ℝ)..R, (Real.cos (x * t) * Real.cos (y * t) + Real.sin (x * t) *
      Real.sin (y * t)) = Real.sin (R * (x - y)) / (x - y) := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) R, HasDerivAt (fun t => Real.sin ((x - y) * t) / (x - y))
      (Real.cos (x * t) * Real.cos (y * t) + Real.sin (x * t) * Real.sin (y * t)) t := by
    intro t _
    convert ((hasDerivAt_id t).const_mul (x - y)).sin.div_const (x - y) using 1
    simp only [id]
    rw [sub_mul, Real.cos_sub]
    field_simp
    simp only [id, mul_comm t y]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    exact (by fun_prop : Continuous fun t => Real.cos (x * t) * Real.cos (y * t) +
      Real.sin (x * t) * Real.sin (y * t)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.sin_zero, zero_div, sub_zero]
  rw [mul_comm R]

/-- DLMF 1.18.59 (Fourier integral theorem in cosine–sine form, Titchmarsh 1962a, pp. 71–72):
`f(x) = π⁻¹ ∫ (∫_0^∞ cos(xt) cos(yt) dt) f(y) dy + π⁻¹ ∫ (∫_0^∞ sin(xt) sin(yt) dt) f(y) dy`,
with the inner integrals over `[0, R]` and `R → ∞`, for `f ∈ L¹(ℝ)` differentiable at `x`. -/
@[dlmf 1.18.E59]
theorem tendsto_fourier_cos_sin {f : ℝ → ℂ} (hf : Integrable f) {x : ℝ}
    (hx : DifferentiableAt ℝ f x) :
    Tendsto (fun R : ℝ => (1 / Real.pi : ℂ) * ∫ y, ((∫ t in (0 : ℝ)..R,
        Real.cos (x * t) * Real.cos (y * t) + Real.sin (x * t) * Real.sin (y * t) : ℝ) : ℂ) *
          f y) atTop (𝓝 (f x)) := by
  refine (Real.tendsto_integral_mul_sin_div_of_differentiableAt hf hx).congr fun R => ?_
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume x] with y hy
  rw [integral_cos_mul_cos_add_sin_mul_sin (sub_ne_zero.2 (Ne.symm hy))]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : (x : ℂ) - y ≠ 0 := by exact_mod_cast sub_ne_zero.2 (Ne.symm hy)
  push_cast
  field_simp

/-- §1.18(viii), Example 1 (Simon 1976, Thm. 2.5): in one dimension a potential with
`∫ (1 + x²)|q| < ∞`, `q ≢ 0` and `∫ q ≤ 0` has a bound state: there are `λ < 0` and a nonzero
`f ∈ L²(ℝ)` with `-f'' + q f = λ f`. -/
@[dlmf 1.18.viii]
theorem exists_bound_state_of_integral_nonpos {q : ℝ → ℝ} (hq : Continuous q)
    (hint : Integrable fun x => (1 + x ^ 2) * q x) (hne : q ≠ 0) (hle : ∫ x, q x ≤ 0) :
    ∃ t : ℝ, t < 0 ∧ ∃ f : ℝ → ℂ, f ≠ 0 ∧ MemLp f 2 ∧ IsSchrodingerSolutionOn q t f univ := by
  sorry

/-! ## §1.18(ix): mathematical background -/

section Background

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- §1.18(ix): the spectrum is the disjoint union of the point, continuous and residual
spectra. -/
@[dlmf 1.18.ix]
theorem operatorSpectrum_eq_union (T : E →ₗ.[ℂ] E) :
    operatorSpectrum T =
        operatorPointSpectrum T ∪ operatorContinuousSpectrum T ∪ operatorResidualSpectrum T ∧
      Disjoint (operatorPointSpectrum T) (operatorContinuousSpectrum T) ∧
      Disjoint (operatorPointSpectrum T) (operatorResidualSpectrum T) ∧
      Disjoint (operatorContinuousSpectrum T) (operatorResidualSpectrum T) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext z
    simp only [operatorSpectrum, operatorResolventSet, operatorPointSpectrum,
        operatorContinuousSpectrum,
      operatorResidualSpectrum, mem_compl_iff, mem_ofPred_eq, mem_union]
    tauto
  · exact Set.disjoint_left.mpr fun z h1 h2 => h1 h2.1
  · exact Set.disjoint_left.mpr fun z h1 h2 => h1 h2.1
  · exact Set.disjoint_left.mpr fun z h1 h2 => h2.2 h1.2.1

/-- §1.18(ix): the spectrum of a self-adjoint operator is a closed subset of `ℝ` and its
residual spectrum is empty. -/
@[dlmf 1.18.ix]
theorem IsSelfAdjoint.operatorSpectrum_real {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T) :
    IsClosed (operatorSpectrum T) ∧ (∀ z ∈ operatorSpectrum T, z.im = 0) ∧
        operatorResidualSpectrum T = ∅ := by
  sorry

/-- §1.18(ix): eigenvectors of a self-adjoint operator for distinct eigenvalues are
orthogonal. -/
@[dlmf 1.18.ix]
theorem IsSelfAdjoint.inner_eigenvectors_eq_zero {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T)
    {z w : ℂ} (u v : T.domain) (hu : (u : E) ≠ 0) (hTu : T u = z • (u : E))
    (hTv : T v = w • (v : E)) (hzw : z ≠ w) : ⟪(u : E), (v : E)⟫_ℂ = 0 :=
  IsSymmetricOperator.inner_eq_zero ⟨hT.dense_domain, isFormalAdjoint_self_of_isSelfAdjoint hT⟩ u
      v hu hTu hTv hzw

/-- §1.18(ix): for a symmetric operator, `dim N_z` is constant on the upper and on the lower
half-plane, so the deficiency indices `n₊ = dim N_i`, `n₋ = dim N_{-i}` describe all `N_z`. -/
@[dlmf 1.18.ix]
theorem IsSymmetricOperator.rank_deficiencySubspace {T : E →ₗ.[ℂ] E} (hT : IsSymmetricOperator T)
    {z : ℂ} (hz : z.im ≠ 0) :
    Module.rank ℂ (deficiencySubspace T z) =
      if 0 < z.im then (deficiencyIndices T).1 else (deficiencyIndices T).2 := by
  sorry

/-- §1.18(ix) (von Neumann): a symmetric operator has a self-adjoint extension if and only if
its deficiency indices are equal. -/
@[dlmf 1.18.ix]
theorem IsSymmetricOperator.exists_selfAdjoint_extension_iff {T : E →ₗ.[ℂ] E}
    (hT : IsSymmetricOperator T) :
    (∃ S : E →ₗ.[ℂ] E, T ≤ S ∧ IsSelfAdjoint S) ↔
      (deficiencyIndices T).1 = (deficiencyIndices T).2 := by
  sorry

/-- §1.18(ix) (von Neumann's formula): `𝓓(T*) = 𝓓(T**) + N_i + N_{-i}`, a direct sum. -/
@[dlmf 1.18.ix]
theorem IsSymmetricOperator.adjoint_domain_eq {T : E →ₗ.[ℂ] E} (hT : IsSymmetricOperator T) :
    T.adjoint.domain = T.adjoint.adjoint.domain ⊔ deficiencySubspace T I ⊔
        deficiencySubspace T (-I) ∧
      Disjoint T.adjoint.adjoint.domain (deficiencySubspace T I ⊔ deficiencySubspace T (-I)) ∧
      Disjoint (deficiencySubspace T I) (deficiencySubspace T (-I)) := by
  sorry

/-- §1.18(ix): with equal deficiency indices, the self-adjoint extensions of a symmetric `T`
are the restrictions of `T*` to `{v + w + Uw : v ∈ 𝓓(T**), w ∈ N_i}` for the linear
isometries `U : N_i → N_{-i}` onto `N_{-i}`. -/
@[dlmf 1.18.ix]
theorem IsSymmetricOperator.selfAdjoint_extension_iff {T : E →ₗ.[ℂ] E} (hT : IsSymmetricOperator T)
    (S : E →ₗ.[ℂ] E) :
    (T ≤ S ∧ IsSelfAdjoint S) ↔
      ∃ U : deficiencySubspace T I ≃ₗᵢ[ℂ] deficiencySubspace T (-I),
        S ≤ T.adjoint ∧ ∀ x : E, x ∈ S.domain ↔
          ∃ v ∈ T.adjoint.adjoint.domain, ∃ w : deficiencySubspace T I,
            x = v + (w : E) + (U w : E) := by
  sorry

end Background

/-- §1.18(ix), Weyl's alternative (part 1): if all solutions of `-f'' + q f = z f` are square
integrable near the end point `a` for one `z ∈ ℂ`, then so for every `z ∈ ℂ` (limit circle
case). Here `q` is real and continuous on `(a, c]`. -/
@[dlmf 1.18.ix]
theorem allSolutionsL2Left_of_exists {q : ℝ → ℝ} {a c : ℝ} (hac : a < c)
    (hq : ContinuousOn q (Ioc a c)) {z₀ : ℂ} (h : AllSolutionsL2Left q z₀ a c) :
    IsLimitCircleLeft q a c := by
  sorry

open Classical in
/-- §1.18(ix), Weyl's alternative (part 2): for `ℑz ≠ 0` there is always a nonzero solution
square integrable near `a`; so `dim N_z = 1` on `(a, c)` (limit point) or `2` (limit
circle). -/
@[dlmf 1.18.ix]
theorem rank_l2SolutionSpace_left {q : ℝ → ℝ} {a c : ℝ} (hac : a < c)
    (hq : ContinuousOn q (Ioc a c)) {z : ℂ} (hz : z.im ≠ 0) :
    Module.rank ℂ (l2SolutionSpace q z (Ioo a c)) =
      if IsLimitCircleLeft q a c then 2 else 1 := by
  sorry

/-- §1.18(ix): the deficiency indices of `𝓛` on `(a, b)` are `n₁ + n₂ - 2`, where `n₁, n₂`
are the dimensions of the `L²` solution spaces on `(a, c)` and `(c, b)` (independent of `c`):
`dim N_z(a, b) + 2 = dim N_z(a, c) + dim N_z(c, b)` for `ℑz ≠ 0`. -/
@[dlmf 1.18.ix]
theorem rank_l2SolutionSpace_add_two {q : ℝ → ℝ} {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hq : ContinuousOn q (Ioo a b)) {z : ℂ} (hz : z.im ≠ 0) :
    Module.rank ℂ (l2SolutionSpace q z (Ioo a b)) + 2 =
      Module.rank ℂ (l2SolutionSpace q z (Ioo a c)) +
        Module.rank ℂ (l2SolutionSpace q z (Ioo c b)) := by
  sorry

/-- §1.18(ix): in the limit point case at `a` the Lagrange bracket of any two elements of the
maximal domain vanishes at `a` (so there are no nonzero boundary values 1.18.71 at `a`); in the
limit circle case there are elements with nonzero bracket. -/
@[dlmf 1.18.ix, dlmf 1.18.E71]
theorem limitPoint_iff_wronskian_tendsto_zero {q : ℝ → ℝ} {a b c : ℝ} (hac : a < c)
    (hcb : c < b) (hq : ContinuousOn q (Ioo a b)) :
    ¬ IsLimitCircleLeft q a c ↔ ∀ f ∈ schrodingerMaxDomainC2 q a b,
      ∀ g ∈ schrodingerMaxDomainC2 q a b,
        Tendsto (wronskianC f (fun x => conj (g x))) (𝓝[>] a) (𝓝 0) := by
  sorry

end DLMF.AlgebraicAnalytic
