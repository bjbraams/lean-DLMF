/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Algebra.Means
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Matrices, vectors, scalar products and norms (DLMF §1.2(v)–(vi))

DLMF's matrices are Mathlib's `Matrix m n ℂ` (transpose `Aᵀ`, Hermitian conjugate `Aᴴ`, trace
`Matrix.trace`, determinant `Matrix.det`, inverse `A⁻¹`); vectors are functions `n → ℂ` (or
`EuclideanSpace ℂ n` when the Euclidean norm is meant). The definitions and the algebraic rules
1.2.27–1.2.39, 1.2.53–1.2.56 and 1.2.62–1.2.69 are upstream; the pointers are in
`DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean`.

**Convention for the scalar product.** DLMF's `⟨u, v⟩ = ∑ u_i \overline{v_i} = v^H u` (1.2.40)
is linear in the first argument, Mathlib's inner product `⟪x, y⟫_ℂ = ∑ \overline{x_i} y_i` in
the second. Here `⟨u, v⟩` is written `u ⬝ᵥ star v` for plain vectors, and it equals Mathlib's
`⟪v, u⟫_ℂ` on `EuclideanSpace ℂ n` (`dotProduct_star_eq_inner`).

This file proves the DLMF forms of the scalar-product rules 1.2.40–1.2.42, the complex Hölder
inequality 1.2.50, the equality case of the Cauchy–Schwarz inequality 1.2.51, the limit
`‖v‖_p → ‖v‖_∞` of 1.2.48, the Leibniz formula 1.2.59 in DLMF's index order, the statements on
inverses and linear systems in §1.2(vi) (1.2.60–1.2.61), the attained maximum in the matrix
norm 1.2.67, the characterization 1.2.71–1.2.72 of
eigenvalues, the characterization 1.2.73 of non-defective matrices, 1.2.74–1.2.75, and the
convergence of the exponential series 1.2.76.

The equality case of 1.2.51 as printed ("iff `v` is a scalar multiple of `u`") fails for
`u = 0 ≠ v`; it is stated with the alternative `u = 0`.
-/

@[expose] public noncomputable section

open Finset Filter Topology Matrix ComplexConjugate

namespace DLMF.AlgebraicAnalytic

variable {n : Type*} [Fintype n]

/-! ### Scalar products and norms (§1.2(v)) -/

/-- DLMF 1.2.40: the scalar product `⟨u, v⟩ = ∑ u_i \overline{v_i} = v^H u` of complex column
vectors, written `u ⬝ᵥ star v`; `v^H u` is `star v ⬝ᵥ u`. -/
@[dlmf 1.2.E40]
theorem dotProduct_star_eq_sum (u v : n → ℂ) :
    u ⬝ᵥ star v = ∑ i, u i * conj (v i) ∧ u ⬝ᵥ star v = star v ⬝ᵥ u :=
  ⟨rfl, dotProduct_comm _ _⟩

/-- DLMF 1.2.40: on `EuclideanSpace ℂ n`, DLMF's `⟨u, v⟩` is Mathlib's `⟪v, u⟫_ℂ` (the order of
the arguments is reversed, see the module docstring). -/
@[dlmf 1.2.E40]
theorem dotProduct_star_eq_inner (u v : EuclideanSpace ℂ n) :
    ∑ i, u i * conj (v i) = inner ℂ v u := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rfl

/-- DLMF 1.2.41: `⟨u, v⟩ = \overline{⟨v, u⟩}`. -/
@[dlmf 1.2.E41]
theorem dotProduct_star_conj_symm (u v : n → ℂ) :
    u ⬝ᵥ star v = conj (v ⬝ᵥ star u) := by
  simp only [dotProduct, map_sum, map_mul, Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  exact sum_congr rfl fun i _ => mul_comm _ _

/-- DLMF 1.2.42: `⟨αu, βv⟩ = α \overline{β} ⟨u, v⟩` for `α, β ∈ ℂ`. -/
@[dlmf 1.2.E42]
theorem smul_dotProduct_star_smul (α β : ℂ) (u v : n → ℂ) :
    (α • u) ⬝ᵥ star (β • v) = α * conj β * (u ⬝ᵥ star v) := by
  simp only [dotProduct, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul', mul_sum,
    RCLike.star_def]
  exact sum_congr rfl fun i _ => by ring

/-- DLMF 1.2.50: Hölder's inequality `|⟨u, v⟩| ≤ ‖u‖_p ‖v‖_q` for complex vectors and
`1/p + 1/q = 1` (1.2.49, `p.HolderConjugate q`), derived from Mathlib's real form
`Real.inner_le_Lp_mul_Lq_of_nonneg`. -/
@[dlmf 1.2.E50]
theorem norm_dotProduct_star_le_Lp_mul_Lq {p q : ℝ} (hpq : p.HolderConjugate q)
    (u v : n → ℂ) :
    ‖u ⬝ᵥ star v‖ ≤ (∑ i, ‖u i‖ ^ p) ^ (1 / p) * (∑ i, ‖v i‖ ^ q) ^ (1 / q) := by
  refine (norm_sum_le _ _).trans ?_
  simp only [Pi.star_apply, norm_mul, norm_star]
  exact Real.inner_le_Lp_mul_Lq_of_nonneg univ hpq (fun i _ => norm_nonneg _)
    (fun i _ => norm_nonneg _)

/-- DLMF 1.2.51 (equality case of the Cauchy–Schwarz inequality, corrected): in a real or complex
inner product space, `|⟨u, v⟩| = ‖u‖ ‖v‖` iff `u = 0` or `v` is a scalar multiple of `u`. DLMF
omits the case `u = 0`, in which equality holds for every `v`. The inequality itself is Mathlib's
`norm_inner_le_norm`. -/
@[dlmf 1.2.E51]
theorem norm_inner_eq_norm_mul_iff {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (u v : E) :
    ‖inner 𝕜 u v‖ = ‖u‖ * ‖v‖ ↔ u = 0 ∨ ∃ c : 𝕜, v = c • u := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp only [hv, inner_zero_right, norm_zero, mul_zero, true_iff]
    exact Or.inr ⟨0, by simp⟩
  rw [norm_inner_eq_norm_iff hu hv]
  constructor
  · rintro ⟨r, -, hr⟩
    exact Or.inr ⟨r, hr⟩
  · rintro (h | ⟨c, hc⟩)
    · exact absurd h hu
    · refine ⟨c, ?_, hc⟩
      rintro rfl
      exact hv (by simpa using hc)

/-- DLMF 1.2.48: the `l^p` norm tends to the maximum norm as `p → ∞`:
`(∑ |v_i|^p)^{1/p} → max(|v₁|, …, |vₙ|)`. -/
@[dlmf 1.2.E48]
theorem tendsto_lpNorm_atTop [Nonempty n] (v : n → ℂ) :
    Tendsto (fun p : ℝ => (∑ i, ‖v i‖ ^ p) ^ (1 / p)) atTop (𝓝 (⨆ i, ‖v i‖)) := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ‖v i‖
  have hsup : (⨆ i, ‖v i‖) = ‖v i₀‖ :=
    le_antisymm (ciSup_le hi₀) (le_ciSup (Set.finite_range fun i => ‖v i‖).bddAbove i₀)
  rw [hsup]
  simpa using g1a_tendsto_sum_rpow_atTop (w := fun _ => (1 : ℝ)) (c := fun i => ‖v i‖)
    (fun _ => one_pos) (fun i => norm_nonneg _) hi₀

/-! ### Square matrices (§1.2(vi)) -/

variable [DecidableEq n]

/-- DLMF 1.2.59: the Leibniz formula `det A = ∑_{σ ∈ 𝔖ₙ} sign σ ∏_i a_{i,σ(i)}` (Mathlib's
`Matrix.det_apply'` has the factors `a_{σ(i),i}`). -/
@[dlmf 1.2.E59]
theorem det_eq_sum_sign_mul_prod {R : Type*} [CommRing R] (A : Matrix n n R) :
    A.det = ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : R) * ∏ i, A i (σ i) := by
  rw [← det_transpose, det_apply']
  rfl

/-- DLMF 1.2.60: if `det A ≠ 0`, then `A` has an inverse with `A A⁻¹ = A⁻¹ A = I`, and it is
unique: any `B` with `A B = I` is `A⁻¹`. -/
@[dlmf 1.2.E60]
theorem mul_inv_eq_one_of_det_ne_zero {K : Type*} [Field K] {A : Matrix n n K}
    (h : A.det ≠ 0) :
    A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 ∧ ∀ B : Matrix n n K, A * B = 1 → B = A⁻¹ := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 h
  exact ⟨mul_nonsing_inv A hu, nonsing_inv_mul A hu, fun B hB => (inv_eq_right_inv hB).symm⟩

/-- DLMF §1.2(vi), after 1.2.60: if `det A ≠ 0`, then `A B = A C` implies `B = C`. -/
@[dlmf 1.2.E60]
theorem eq_of_mul_eq_mul_of_det_ne_zero {K : Type*} [Field K] {m : Type*} {A : Matrix n n K}
    (h : A.det ≠ 0) {B C : Matrix n m K} (hBC : A * B = A * C) : B = C := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 h
  rw [← nonsing_inv_mul_cancel_left A B hu, hBC, nonsing_inv_mul_cancel_left A C hu]

/-- DLMF §1.2(vi), after 1.2.60: if `det A = 0` (and the order is positive), then `A B = A C`
does not imply `B = C`. -/
@[dlmf 1.2.E60]
theorem exists_mul_eq_mul_ne_of_det_eq_zero {K : Type*} [Field K] {A : Matrix n n K}
    (h : A.det = 0) : ∃ B C : Matrix n n K, A * B = A * C ∧ B ≠ C := by
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 h
  refine ⟨0, Matrix.of fun i _ => v i, ?_, ?_⟩
  · ext i j
    have := congrFun hv i
    simp only [mulVec, dotProduct] at this
    simp [Matrix.mul_apply, this]
  · intro h0
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
    exact hi (by simpa using (congrFun (congrFun h0 i) i).symm)

/-- DLMF 1.2.61: if `det A ≠ 0`, the linear system `A b = c` has the unique solution
`b = A⁻¹ c`. -/
@[dlmf 1.2.E61]
theorem existsUnique_mulVec_eq {K : Type*} [Field K] {A : Matrix n n K} (h : A.det ≠ 0)
    (c : n → K) : ∃! b, A *ᵥ b = c ∧ b = A⁻¹ *ᵥ c := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 h
  refine ⟨A⁻¹ *ᵥ c, ⟨by rw [mulVec_mulVec, mul_nonsing_inv A hu, one_mulVec], rfl⟩, ?_⟩
  rintro b ⟨-, rfl⟩
  rfl

/-- DLMF 1.2.61: if `det A ≠ 0`, every solution of `A b = c` is `A⁻¹ c`. -/
@[dlmf 1.2.E61]
theorem eq_inv_mulVec_of_mulVec_eq {K : Type*} [Field K] {A : Matrix n n K} (h : A.det ≠ 0)
    {b c : n → K} (hb : A *ᵥ b = c) : b = A⁻¹ *ᵥ c := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 h
  rw [← hb, mulVec_mulVec, nonsing_inv_mul A hu, one_mulVec]

omit [DecidableEq n] in
/-- DLMF §1.2(vi), after 1.2.61: the solutions of `A b = c` are a particular solution plus the
solutions of `A b = 0`. -/
@[dlmf 1.2.E61]
theorem mulVec_eq_iff_of_mulVec_eq {K : Type*} [Field K] {A : Matrix n n K} {b₀ c : n → K}
    (hb₀ : A *ᵥ b₀ = c) (b : n → K) : A *ᵥ b = c ↔ A *ᵥ (b - b₀) = 0 := by
  rw [mulVec_sub, hb₀, sub_eq_zero]

/-- DLMF §1.2(vi), after 1.2.61: if `det A = 0`, then over an infinite field the system
`A b = c` has either no solution or infinitely many. -/
@[dlmf 1.2.E61]
theorem not_exists_or_infinite_of_det_eq_zero {K : Type*} [Field K] [Infinite K]
    {A : Matrix n n K} (h : A.det = 0) (c : n → K) :
    (¬∃ b, A *ᵥ b = c) ∨ {b | A *ᵥ b = c}.Infinite := by
  by_cases hc : ∃ b, A *ᵥ b = c
  · right
    obtain ⟨b₀, hb₀⟩ := hc
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 h
    have hinj : Function.Injective fun t : K => b₀ + t • v := by
      intro s t hst
      have : (s - t) • v = 0 := by
        rw [sub_smul]; exact sub_eq_zero.2 (add_left_cancel hst)
      exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hv0)
    refine Set.infinite_of_injective_forall_mem hinj fun t => ?_
    simp [mulVec_add, mulVec_smul, hv, hb₀]
  · exact Or.inl hc

open scoped Matrix.Norms.L2Operator in
/-- DLMF 1.2.67: the matrix norm `‖A‖ = max_{‖x‖ = 1} ‖A x‖` induced by the `l²` norm is
Mathlib's `l²` operator norm (the scoped instance `Matrix.Norms.L2Operator`), and the maximum
over the unit sphere is attained (for a nonempty index type). `toEuclideanCLM A` is `x ↦ A x` on
`EuclideanSpace ℂ n`. -/
@[dlmf 1.2.E67]
theorem l2_opNorm_isGreatest [Nonempty n] (A : Matrix n n ℂ) :
    IsGreatest ((fun x : EuclideanSpace ℂ n => ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖) ''
      Metric.sphere 0 1) ‖A‖ := by
  have hc : IsCompact ((fun x : EuclideanSpace ℂ n => ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖) ''
      Metric.sphere 0 1) :=
    (isCompact_sphere 0 1).image (by fun_prop)
  have hne : ((fun x : EuclideanSpace ℂ n => ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖) ''
      Metric.sphere 0 1).Nonempty :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).image _
  have := hc.isGreatest_sSup hne
  rwa [ContinuousLinearMap.sSup_sphere_eq_norm, ← cstar_norm_def] at this

/-- DLMF 1.2.71 and 1.2.72: `λ` is an eigenvalue of `A`, with an eigenvector `a ≠ 0` such that
`A a = λ a` (1.2.70), iff `det(A - λI) = 0`; the eigenvectors are the nonzero solutions of
`(A - λI) a = 0`. -/
@[dlmf 1.2.E70, dlmf 1.2.E71, dlmf 1.2.E72]
theorem exists_eigenvector_iff_det_sub_eq_zero {K : Type*} [Field K] (A : Matrix n n K)
    (μ : K) : (∃ a, a ≠ 0 ∧ A *ᵥ a = μ • a) ↔ (A - μ • (1 : Matrix n n K)).det = 0 := by
  rw [← exists_mulVec_eq_zero_iff]
  refine exists_congr fun a => and_congr_right fun _ => ?_
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]

/-- DLMF 1.2.73: for invertible `S`, `S⁻¹ A S` is the diagonal matrix `Λ = diag(λ_j)` iff the
`j`th column of `S` is an eigenvector of `A` with eigenvalue `λ_j`, for every `j`. -/
@[dlmf 1.2.E73]
theorem inv_mul_mul_eq_diagonal_iff {K : Type*} [Field K] {A S : Matrix n n K}
    (hS : IsUnit S.det) (μ : n → K) :
    S⁻¹ * A * S = diagonal μ ↔ ∀ j, A *ᵥ (fun i => S i j) = μ j • fun i => S i j := by
  have hS' : IsUnit S := (isUnit_iff_isUnit_det S).2 hS
  have key : S⁻¹ * A * S = diagonal μ ↔ A * S = S * diagonal μ := by
    constructor
    · intro h
      rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv S hS, Matrix.one_mul]
    · intro h
      rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, nonsing_inv_mul S hS, Matrix.one_mul]
  rw [key]
  constructor
  · intro h j
    ext i
    have := congrFun (congrFun h i) j
    rw [mul_diagonal] at this
    simpa [mulVec, dotProduct, Matrix.mul_apply, mul_comm] using this
  · intro h
    ext i j
    have := congrFun (h j) i
    rw [mul_diagonal]
    simpa [mulVec, dotProduct, Matrix.mul_apply, mul_comm] using this

/-- DLMF 1.2.73: a matrix is non-defective (it has `n` linearly independent eigenvectors) iff it
is diagonalizable by a similarity transformation `Λ = S⁻¹ A S`. -/
@[dlmf 1.2.E73]
theorem nonDefective_iff_exists_diagonal {K : Type*} [Field K] (A : Matrix n n K) :
    (∃ v : n → n → K, LinearIndependent K v ∧ ∀ j, ∃ μ : K, A *ᵥ v j = μ • v j) ↔
      ∃ (S : Matrix n n K) (μ : n → K), IsUnit S.det ∧ S⁻¹ * A * S = diagonal μ := by
  constructor
  · rintro ⟨v, hv, hev⟩
    choose μ hμ using hev
    set S : Matrix n n K := Matrix.of fun i j => v j i with hSdef
    have hcol : S.col = v := by ext j i; rfl
    have hS : IsUnit S.det := by
      rw [← isUnit_iff_isUnit_det, ← linearIndependent_col_iff_isUnit, hcol]
      exact hv
    exact ⟨S, μ, hS, (inv_mul_mul_eq_diagonal_iff hS μ).2 fun j => hμ j⟩
  · rintro ⟨S, μ, hS, h⟩
    refine ⟨S.col, ?_, fun j => ⟨μ j, ?_⟩⟩
    · rw [linearIndependent_col_iff_isUnit, isUnit_iff_isUnit_det]
      exact hS
    · exact (inv_mul_mul_eq_diagonal_iff hS μ).1 h j

/-- DLMF 1.2.74: if `S⁻¹ A S = diag(λ₁, …, λₙ)`, then `det A = ∏ λ_i`. Mathlib's
`Matrix.det_eq_prod_roots_charpoly` gives `det A` as the product of the roots of the
characteristic polynomial for every matrix over an algebraically closed field. -/
@[dlmf 1.2.E74]
theorem det_eq_prod_of_inv_mul_mul_eq_diagonal {K : Type*} [Field K] {A S : Matrix n n K}
    (hS : IsUnit S.det) {μ : n → K} (h : S⁻¹ * A * S = diagonal μ) : A.det = ∏ i, μ i := by
  rw [← det_diagonal, ← h, det_conj' ((isUnit_iff_isUnit_det S).2 hS)]

/-- DLMF 1.2.75: if `S⁻¹ A S = diag(λ₁, …, λₙ)`, then `tr A = ∑ λ_i`. Mathlib's
`Matrix.trace_eq_sum_roots_charpoly` is the general form. -/
@[dlmf 1.2.E75]
theorem trace_eq_sum_of_inv_mul_mul_eq_diagonal {K : Type*} [Field K] {A S : Matrix n n K}
    (hS : IsUnit S.det) {μ : n → K} (h : S⁻¹ * A * S = diagonal μ) : A.trace = ∑ i, μ i := by
  rw [← trace_diagonal, ← h, trace_conj' ((isUnit_iff_isUnit_det S).2 hS)]

/-- DLMF 1.2.76: the exponential series `∑ Aⁿ/n!` of a complex square matrix converges to
`exp A` (Mathlib's `NormedSpace.exp`), both in norm (the topology of `Matrix n n ℂ`) and entry
by entry. -/
@[dlmf 1.2.E76]
theorem hasSum_exp_matrix (A : Matrix n n ℂ) :
    HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • A ^ k) (NormedSpace.exp A) ∧
      ∀ i j, HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (A ^ k) i j) (NormedSpace.exp A i j) := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  refine ⟨h, fun i j => ?_⟩
  have h1 := Pi.hasSum.1 h i
  exact Pi.hasSum.1 h1 j

end DLMF.AlgebraicAnalytic
