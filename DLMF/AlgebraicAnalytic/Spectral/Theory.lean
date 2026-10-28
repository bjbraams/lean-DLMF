/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Spectral.Defs
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Linear second-order differential operators and eigenfunction expansions (DLMF §1.18)

DLMF §1.18 surveys the spectral theory of `𝓛 = -d²/dx² + q(x)` (1.18.28). The Hilbert-space
facts of §1.18(i)–(ii) are Mathlib's (`HilbertBasis`, `lp`, `MeasureTheory.L2`; pointers in
`DLMF.AlgebraicAnalytic.Spectral.MathlibCoverage`). This file states:

* §1.18(ii): the `L²` mean convergence 1.18.16;
* §1.18(iii): reality of eigenvalues and orthogonality of eigenvectors of symmetric operators
  (1.18.24), the integration by parts 1.18.26 and formal self-adjointness 1.18.27;
* §1.18(v): eigenfunction expansions for a self-adjoint operator with an orthonormal basis of
  eigenvectors (1.18.29–1.18.35), the examples 1.18.36–1.18.43;
* §1.18(vi), §1.18(viii): expansions over continuous and mixed spectra in the form of
  `IsEigenfunctionTransform` (1.18.46–1.18.52, 1.18.64–1.18.66), Stieltjes inversion 1.18.53,
  the Sokhotski–Plemelj formula 1.18.54, the Hankel and Fourier integral theorems
  1.18.56–1.18.59, and Simon's bound-state theorem (§1.18(viii));
* §1.18(ix): spectra of self-adjoint operators, deficiency indices, Weyl's alternative.

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
  sorry

/-! ## §1.18(iii): symmetric operators and integration by parts -/

section Symmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- DLMF 1.18.24: the eigenvalues of a symmetric operator are real. -/
@[dlmf 1.18.E24]
theorem IsSymmetricOp.eigenvalue_real {T : E →ₗ.[ℂ] E} (hT : IsSymmetricOp T) {z : ℂ}
    (u : T.domain) (hu : (u : E) ≠ 0) (h : T u = z • (u : E)) : conj z = z := by
  have h1 := hT.2 u u
  rw [h, inner_smul_left, inner_smul_right] at h1
  have h2 : (⟪(u : E), (u : E)⟫_ℂ) ≠ 0 := inner_self_ne_zero.mpr hu
  exact mul_right_cancel₀ h2 h1

omit [CompleteSpace E] in
/-- DLMF 1.18.24: eigenvectors of a symmetric operator for distinct eigenvalues are
orthogonal, `⟨u_λ, u_t⟩ = 0` for `λ ≠ t`. -/
@[dlmf 1.18.E24]
theorem IsSymmetricOp.inner_eq_zero {T : E →ₗ.[ℂ] E} (hT : IsSymmetricOp T) {z w : ℂ}
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
lemma g1f_isFormalAdjoint_self {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T) :
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
  have h := g1f_isFormalAdjoint_self hT ⟨b i, hmem i⟩ f
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
  have h := g1f_isFormalAdjoint_self hT ⟨b i, hmem i⟩ u
  simp only at h
  have hne : z - lam i ≠ 0 := sub_ne_zero.mpr (hz i)
  rw [← hf, inner_sub_right, inner_smul_right, ← h, hb, inner_smul_left, conj_ofReal]
  field_simp

end PointSpectrum

/-! ### Example 1: `q = 0` on `[0, π]` -/

/-- Identity under the stated parameter and domain assumptions: `deriv (fun x : ℝ => cexp (c * x))
= fun x : ℝ => c * cexp (c * x)`. -/
private lemma g1f_deriv_cexp_mul (c : ℂ) :
    deriv (fun x : ℝ => cexp (c * x)) = fun x : ℝ => c * cexp (c * x) := by
  ext x
  have h : HasDerivAt (fun x : ℝ => c * (x : ℂ)) (c * 1) x :=
    ((hasDerivAt_id x).ofReal_comp).const_mul c
  have := h.cexp
  rw [this.deriv]; ring

/-- Identity under the stated parameter and domain assumptions: `deriv (fun x : ℝ => Complex.sin
(c * x)) = fun x : ℝ => c * Complex.cos (c * x)`. -/
private lemma g1f_deriv_csin_mul (c : ℂ) :
    deriv (fun x : ℝ => Complex.sin (c * x)) = fun x : ℝ => c * Complex.cos (c * x) := by
  ext x
  have h : HasDerivAt (fun x : ℝ => c * (x : ℂ)) (c * 1) x :=
    ((hasDerivAt_id x).ofReal_comp).const_mul c
  rw [show (fun x : ℝ => Complex.sin (c * x)) = Complex.sin ∘ fun x : ℝ => c * (x : ℂ)
    from rfl, ((Complex.hasDerivAt_sin (c * x)).comp x h).deriv]
  ring

/-- Identity under the stated parameter and domain assumptions: `deriv (fun x : ℝ => Complex.cos
(c * x)) = fun x : ℝ => -(c * Complex.sin (c * x))`. -/
private lemma g1f_deriv_ccos_mul (c : ℂ) :
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
    (∀ x, schrodingerOp 0 (sinEigenfunction n) x = (n : ℂ) ^ 2 * sinEigenfunction n x) ∧
      sinEigenfunction n 0 = 0 ∧ sinEigenfunction n Real.pi = 0 := by
  have hf : sinEigenfunction n = fun x : ℝ =>
      (Real.sqrt (2 / Real.pi) : ℂ) * Complex.sin ((n : ℂ) * x) := by
    ext x; simp [sinEigenfunction]
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [schrodingerOp, hf]
    simp only [deriv_const_mul_field', g1f_deriv_csin_mul, g1f_deriv_ccos_mul]
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
    (∀ x, schrodingerOp 0 (cosEigenfunction n) x = (n : ℂ) ^ 2 * cosEigenfunction n x) ∧
      deriv (cosEigenfunction n) 0 = 0 ∧ deriv (cosEigenfunction n) Real.pi = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : cosEigenfunction 0 = fun _ => ((1 / Real.sqrt Real.pi : ℝ) : ℂ) := by
      ext x; simp [cosEigenfunction]
    simp [h0, schrodingerOp]
  have hf : cosEigenfunction n = fun x : ℝ =>
      (Real.sqrt (2 / Real.pi) : ℂ) * Complex.cos ((n : ℂ) * x) := by
    ext x; simp [cosEigenfunction, hn.ne']
  have hd : deriv (cosEigenfunction n) = fun x : ℝ =>
      (Real.sqrt (2 / Real.pi) : ℂ) * -((n : ℂ) * Complex.sin ((n : ℂ) * x)) := by
    rw [hf]; ext x; simp only [deriv_const_mul_field', g1f_deriv_ccos_mul]
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [schrodingerOp, hd, hf]
    simp
    rw [g1f_deriv_csin_mul]
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
    (∀ x, schrodingerOp 0 (expEigenfunction n) x = (2 * n : ℂ) ^ 2 * expEigenfunction n x) ∧
      expEigenfunction n 0 = expEigenfunction n Real.pi ∧
      deriv (expEigenfunction n) 0 = deriv (expEigenfunction n) Real.pi := by
  have hf : expEigenfunction n = fun x : ℝ =>
      (1 / Real.sqrt Real.pi : ℂ) * cexp ((2 * I * n) * x) := by
    ext x; simp only [expEigenfunction]; ring_nf
  have hd : deriv (expEigenfunction n) = fun x : ℝ =>
      (1 / Real.sqrt Real.pi : ℂ) * ((2 * I * n) * cexp ((2 * I * n) * x)) := by
    rw [hf]; ext x
    rw [deriv_const_mul _ (by fun_prop), g1f_deriv_cexp_mul]
  have hpi : cexp ((2 * I * n) * (Real.pi : ℝ)) = 1 := by
    rw [show (2 * I * n) * ((Real.pi : ℝ) : ℂ) = n * (2 * Real.pi * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  refine ⟨fun x => ?_, ?_, ?_⟩
  · have hdd : deriv (deriv (expEigenfunction n)) x =
        (1 / Real.sqrt Real.pi : ℂ) * ((2 * I * n) * ((2 * I * n) * cexp ((2 * I * n) * x))) := by
      rw [hd, deriv_const_mul _ (by fun_prop), deriv_const_mul _ (by fun_prop),
        g1f_deriv_cexp_mul]
    rw [schrodingerOp, hdd, hf]
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
    hermiteOp (hermiteFunction n) x = (2 * n + 1 : ℂ) * hermiteFunction n x := by
  sorry

/-- DLMF 1.18.42–1.18.43: the Hermite functions are an orthonormal basis of `L²(ℝ)`; hence
`f = Σₙ (∫ φₙ(y) f(y) dy) φₙ` in `L²` for `f ∈ L²(ℝ)` (1.18.43, convergence as in §1.18(ii)). -/
@[dlmf 1.18.E42, dlmf 1.18.E43]
theorem hermiteFunction_hilbertBasis :
    ∃ b : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)),
      ∀ n, (b n : ℝ → ℂ) =ᵐ[volume] hermiteFunction n := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- DLMF 1.18.55: `√x J_ν(x√λ)` is an eigenfunction of the Bessel operator with eigenvalue
`λ ≥ 0` on `(0, ∞)` (real `ν`, Mathlib's `Complex.besselJ`, principal powers). -/
@[dlmf 1.18.E55]
theorem besselOp_sqrt_mul_besselJ (ν : ℝ) {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx : 0 < x) :
    besselOp ν (fun y => (Real.sqrt y : ℂ) * Complex.besselJ ν (y * Real.sqrt t)) x =
      (t : ℂ) * ((Real.sqrt x : ℂ) * Complex.besselJ ν (x * Real.sqrt t)) := by
  sorry

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

/-- DLMF 1.18.59 (Fourier integral theorem in cosine–sine form, Titchmarsh 1962a, pp. 71–72):
`f(x) = π⁻¹ ∫ (∫_0^∞ cos(xt) cos(yt) dt) f(y) dy + π⁻¹ ∫ (∫_0^∞ sin(xt) sin(yt) dt) f(y) dy`,
with the inner integrals over `[0, R]` and `R → ∞`, for `f ∈ L¹(ℝ)` differentiable at `x`. -/
@[dlmf 1.18.E59]
theorem tendsto_fourier_cos_sin {f : ℝ → ℂ} (hf : Integrable f) {x : ℝ}
    (hx : DifferentiableAt ℝ f x) :
    Tendsto (fun R : ℝ => (1 / Real.pi : ℂ) * ∫ y, ((∫ t in (0 : ℝ)..R,
        Real.cos (x * t) * Real.cos (y * t) + Real.sin (x * t) * Real.sin (y * t) : ℝ) : ℂ) *
          f y) atTop (𝓝 (f x)) := by
  sorry

/-- §1.18(viii), Example 1 (Simon 1976, Thm. 2.5): in one dimension a potential with
`∫ (1 + x²)|q| < ∞`, `q ≢ 0` and `∫ q ≤ 0` has a bound state: there are `λ < 0` and a nonzero
`f ∈ L²(ℝ)` with `-f'' + q f = λ f`. -/
@[dlmf 1.18.viii]
theorem exists_bound_state_of_integral_nonpos {q : ℝ → ℝ} (hq : Continuous q)
    (hint : Integrable fun x => (1 + x ^ 2) * q x) (hne : q ≠ 0) (hle : ∫ x, q x ≤ 0) :
    ∃ t : ℝ, t < 0 ∧ ∃ f : ℝ → ℂ, f ≠ 0 ∧ MemLp f 2 ∧ IsSchrodingerSolOn q t f univ := by
  sorry

/-! ## §1.18(ix): mathematical background -/

section Background

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- §1.18(ix): the spectrum is the disjoint union of the point, continuous and residual
spectra. -/
@[dlmf 1.18.ix]
theorem opSpectrum_eq_union (T : E →ₗ.[ℂ] E) :
    opSpectrum T = opPointSpectrum T ∪ opContinuousSpectrum T ∪ opResidualSpectrum T ∧
      Disjoint (opPointSpectrum T) (opContinuousSpectrum T) ∧
      Disjoint (opPointSpectrum T) (opResidualSpectrum T) ∧
      Disjoint (opContinuousSpectrum T) (opResidualSpectrum T) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext z
    simp only [opSpectrum, opResolventSet, opPointSpectrum, opContinuousSpectrum,
      opResidualSpectrum, mem_compl_iff, mem_ofPred_eq, mem_union]
    tauto
  · exact Set.disjoint_left.mpr fun z h1 h2 => h1 h2.1
  · exact Set.disjoint_left.mpr fun z h1 h2 => h1 h2.1
  · exact Set.disjoint_left.mpr fun z h1 h2 => h2.2 h1.2.1

/-- §1.18(ix): the spectrum of a self-adjoint operator is a closed subset of `ℝ` and its
residual spectrum is empty. -/
@[dlmf 1.18.ix]
theorem IsSelfAdjoint.opSpectrum_real {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T) :
    IsClosed (opSpectrum T) ∧ (∀ z ∈ opSpectrum T, z.im = 0) ∧ opResidualSpectrum T = ∅ := by
  sorry

/-- §1.18(ix): eigenvectors of a self-adjoint operator for distinct eigenvalues are
orthogonal. -/
@[dlmf 1.18.ix]
theorem IsSelfAdjoint.inner_eigenvectors_eq_zero {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T)
    {z w : ℂ} (u v : T.domain) (hu : (u : E) ≠ 0) (hTu : T u = z • (u : E))
    (hTv : T v = w • (v : E)) (hzw : z ≠ w) : ⟪(u : E), (v : E)⟫_ℂ = 0 :=
  IsSymmetricOp.inner_eq_zero ⟨hT.dense_domain, g1f_isFormalAdjoint_self hT⟩ u v hu hTu hTv hzw

/-- §1.18(ix): for a symmetric operator, `dim N_z` is constant on the upper and on the lower
half-plane, so the deficiency indices `n₊ = dim N_i`, `n₋ = dim N_{-i}` describe all `N_z`. -/
@[dlmf 1.18.ix]
theorem IsSymmetricOp.rank_deficiencySubspace {T : E →ₗ.[ℂ] E} (hT : IsSymmetricOp T)
    {z : ℂ} (hz : z.im ≠ 0) :
    Module.rank ℂ (deficiencySubspace T z) =
      if 0 < z.im then (deficiencyIndices T).1 else (deficiencyIndices T).2 := by
  sorry

/-- §1.18(ix) (von Neumann): a symmetric operator has a self-adjoint extension if and only if
its deficiency indices are equal. -/
@[dlmf 1.18.ix]
theorem IsSymmetricOp.exists_selfAdjoint_extension_iff {T : E →ₗ.[ℂ] E}
    (hT : IsSymmetricOp T) :
    (∃ S : E →ₗ.[ℂ] E, T ≤ S ∧ IsSelfAdjoint S) ↔
      (deficiencyIndices T).1 = (deficiencyIndices T).2 := by
  sorry

/-- §1.18(ix) (von Neumann's formula): `𝓓(T*) = 𝓓(T**) + N_i + N_{-i}`, a direct sum. -/
@[dlmf 1.18.ix]
theorem IsSymmetricOp.adjoint_domain_eq {T : E →ₗ.[ℂ] E} (hT : IsSymmetricOp T) :
    T.adjoint.domain = T.adjoint.adjoint.domain ⊔ deficiencySubspace T I ⊔
        deficiencySubspace T (-I) ∧
      Disjoint T.adjoint.adjoint.domain (deficiencySubspace T I ⊔ deficiencySubspace T (-I)) ∧
      Disjoint (deficiencySubspace T I) (deficiencySubspace T (-I)) := by
  sorry

/-- §1.18(ix): with equal deficiency indices, the self-adjoint extensions of a symmetric `T`
are the restrictions of `T*` to `{v + w + Uw : v ∈ 𝓓(T**), w ∈ N_i}` for the linear
isometries `U : N_i → N_{-i}` onto `N_{-i}`. -/
@[dlmf 1.18.ix]
theorem IsSymmetricOp.selfAdjoint_extension_iff {T : E →ₗ.[ℂ] E} (hT : IsSymmetricOp T)
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
