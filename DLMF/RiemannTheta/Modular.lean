/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Symmetry
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Modular transformations of Riemann theta functions (DLMF §21.5)

Integer symplectic matrices `Γ = [[A, B], [C, D]]` with `Γ J Γᵀ = J`,
`J = [[0, I], [-I, 0]]` (DLMF 21.5.1–21.5.2), are related to Mathlib's
`Matrix.symplecticGroup` (whose `J` is the negative of DLMF's). Their determinant is `1`
(DLMF 21.5.3, Mathlib's `SymplecticGroup.det_eq_one`).

The elementary transformations 21.5.5–21.5.7 are proved by reindexing and a parity
argument; the `g = 1` case of the inversion 21.5.8 is proved from Mathlib's
`jacobiTheta₂_functional_equation`.

## Corrections and branch conventions

* **21.5.4 as printed is false for general symplectic `Γ`.** For `Γ = [[I, B], [0, I]]` with
  `B` of odd diagonal, 21.5.7 gives `θ(z|Ω+B) = θ(z + ½ diag B|Ω)`, which is not a constant
  multiple of `θ(z|Ω)` (numerically, for `g = 2`, `B = [[1,3],[3,-1]]`, the ratio
  `θ(z|Ω+B)/θ(z|Ω)` changes with `z`). The general formula is 21.5.9 with `α = β = 0`, which
  shifts the characteristics by `½ diag(CDᵀ)`, `½ diag(ABᵀ)`; 21.5.4 holds when both diagonals
  are even (the theta group). That corrected form is acquired.
* The square root `√det(CΩ+D)` in 21.5.4 and 21.5.9 is a continuous branch on the Siegel
  space (any such branch, the constant `ξ` or `κ` absorbing its sign).
* **21.5.8 with the principal square root fails for `g ≥ 3`.** For `Ω = τ I₃`,
  `τ = -1.1√3 + i`, `det(-iΩ) = (1 + 1.1√3 i)³` has argument beyond `π`, and the principal value
  of the root has the wrong sign (verified numerically). The correct factor is the continuous
  branch with value `1` at `Ω = iI`, i.e. the product of the principal roots of the
  eigenvalues of `-iΩ`. For `g ≤ 2` the principal value is that branch. Both the general
  branch form and the principal-value form for `g ≤ 2` are acquired; `g = 1` is proved.
-/

@[expose] public noncomputable section

open Complex Matrix Finset
open scoped Real

namespace DLMF.RiemannTheta

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Symplectic matrices (DLMF 21.5.1–21.5.3) -/

/-- DLMF's `J_{2g} = [[0, I], [-I, 0]]` (DLMF §21.1). It is `-Matrix.J` in Mathlib. -/
@[dlmf 21.1 "J_{2g}"]
def symplecticJ (ι : Type*) [DecidableEq ι] (R : Type*) [CommRing R] :
    Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks 0 1 (-1) 0

/-- The symplectic condition `Γ J_{2g} Γᵀ = J_{2g}` (DLMF 21.5.2). -/
@[dlmf 21.5.E2]
def IsSymplectic {R : Type*} [CommRing R] (Γ : Matrix (ι ⊕ ι) (ι ⊕ ι) R) : Prop :=
  Γ * symplecticJ ι R * Γᵀ = symplecticJ ι R

/-- The block matrix `Γ = [[A, B], [C, D]]` of integer `g × g` matrices is symplectic
(DLMF 21.5.1–21.5.2). -/
@[dlmf 21.5.E1]
def IsSymplecticBlocks (A B C D : Matrix ι ι ℤ) : Prop :=
  IsSymplectic (Matrix.fromBlocks A B C D)

omit [Fintype ι] in
theorem symplecticJ_eq_neg {R : Type*} [CommRing R] : symplecticJ ι R = -Matrix.J ι R := by
  simp [symplecticJ, Matrix.J, Matrix.fromBlocks_neg]

/-- DLMF's symplectic condition agrees with membership in Mathlib's `Matrix.symplecticGroup`
(whose `J` is `-J_{2g}`). -/
@[dlmf 21.5.E2 "bridge to Matrix.symplecticGroup"]
theorem isSymplectic_iff_mem_symplecticGroup {R : Type*} [CommRing R]
    (Γ : Matrix (ι ⊕ ι) (ι ⊕ ι) R) : IsSymplectic Γ ↔ Γ ∈ Matrix.symplecticGroup ι R := by
  rw [IsSymplectic, SymplecticGroup.mem_iff, symplecticJ_eq_neg, Matrix.mul_neg, Matrix.neg_mul,
    neg_inj]

/-- `det Γ = 1` for a symplectic matrix (DLMF 21.5.3). -/
@[dlmf 21.5.E3]
theorem det_eq_one_of_isSymplectic {R : Type*} [CommRing R] {Γ : Matrix (ι ⊕ ι) (ι ⊕ ι) R}
    (hΓ : IsSymplectic Γ) : Γ.det = 1 :=
  SymplecticGroup.det_eq_one ((isSymplectic_iff_mem_symplecticGroup Γ).mp hΓ)

/-- The integer matrix `A` viewed as a complex matrix. -/
abbrev rth21_cplx (A : Matrix ι ι ℤ) : Matrix ι ι ℂ := A.map (Int.cast)

/-- The real matrix of an integer matrix. -/
abbrev rth21_real (A : Matrix ι ι ℤ) : Matrix ι ι ℝ := A.map (Int.cast)

omit [DecidableEq ι] in
/-- For a real symmetric `Y`, `u* Y u = x·Yx + y·Yy` with `u = x + iy`. -/
lemma p3t_star_quad {Y : Matrix ι ι ℝ} (hY : Yᵀ = Y) (u : ι → ℂ) :
    star u ⬝ᵥ (Y.map ofReal *ᵥ u) =
      (((fun i => (u i).re) ⬝ᵥ (Y *ᵥ fun i => (u i).re) +
        (fun i => (u i).im) ⬝ᵥ (Y *ᵥ fun i => (u i).im) : ℝ) : ℂ) := by
  set x : ι → ℝ := fun i => (u i).re
  set y : ι → ℝ := fun i => (u i).im
  have hc : ∀ v w : ι → ℝ, (fun i => (v i : ℂ)) ⬝ᵥ (Y.map ofReal *ᵥ fun i => (w i : ℂ)) =
      ((v ⬝ᵥ (Y *ᵥ w) : ℝ) : ℂ) := by
    intro v w
    simp [dotProduct, mulVec, ofReal_sum, ofReal_mul]
  have hs : x ⬝ᵥ (Y *ᵥ y) = y ⬝ᵥ (Y *ᵥ x) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hY, dotProduct_comm]
  have hu : u = (fun i => (x i : ℂ)) + I • (fun i => (y i : ℂ)) := by
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, x, y]
    rw [mul_comm, Complex.re_add_im]
  have hsu : star u = (fun i => (x i : ℂ)) - I • (fun i => (y i : ℂ)) := by
    ext i; simp [x, y]
    apply Complex.ext <;> simp
  rw [hsu, show Y.map ofReal *ᵥ u = Y.map ofReal *ᵥ ((fun i => (x i : ℂ)) +
    I • (fun i => (y i : ℂ))) by rw [← hu]]
  rw [mulVec_add, mulVec_smul, sub_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, hc, hc, hc, hc, hs]
  simp only [smul_eq_mul]
  push_cast
  ring_nf
  rw [I_sq]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- `Ω - Ωᴴ = 2i Im Ω` for symmetric `Ω`. -/
lemma p3t_sub_conjTranspose {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω) :
    Ω - Ωᴴ = (2 * I) • (Ω.map Complex.im).map ofReal := by
  ext i j
  have h := congrFun (congrFun hΩ i) j
  simp only [transpose_apply] at h
  simp only [Matrix.sub_apply, conjTranspose_apply, h, Matrix.smul_apply, map_apply, smul_eq_mul]
  apply Complex.ext
  · simp
  · simp; ring


omit [Fintype ι] [DecidableEq ι] in
/-- Integer matrices are fixed by `ᴴ` up to transposition. -/
lemma p3t_cplx_conjTranspose (A : Matrix ι ι ℤ) : (rth21_cplx A)ᴴ = (rth21_cplx A)ᵀ := by
  ext i j; simp [conjTranspose_apply]

/-- The block relations of an integer symplectic matrix, over `ℂ`. -/
lemma p3t_blocks {A B C D : Matrix ι ι ℤ} (hΓ : IsSymplecticBlocks A B C D) :
    (rth21_cplx A)ᵀ * rth21_cplx C = (rth21_cplx C)ᵀ * rth21_cplx A ∧
      (rth21_cplx B)ᵀ * rth21_cplx D = (rth21_cplx D)ᵀ * rth21_cplx B ∧
      (rth21_cplx A)ᵀ * rth21_cplx D - (rth21_cplx C)ᵀ * rth21_cplx B = 1 := by
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.mp
    ((isSymplectic_iff_mem_symplecticGroup _).mp hΓ)
  have e : ∀ X : Matrix ι ι ℤ, rth21_cplx X = X.map (Int.castRingHom ℂ) := fun X => by
    ext; simp
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun X => X.map (Int.castRingHom ℂ)) h1
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    simpa only [e] using this
  · have := congrArg (fun X => X.map (Int.castRingHom ℂ)) h2
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    simpa only [e] using this
  · have := congrArg (Int.castRingHom ℂ).mapMatrix h3
    rw [map_sub, map_mul, map_mul, map_one] at this
    simp only [RingHom.mapMatrix_apply, Matrix.transpose_map] at this
    simpa only [e] using this

/-- A symplectic `Γ` maps the Siegel space to itself, `Ω ↦ (AΩ+B)(CΩ+D)⁻¹`, and `CΩ+D` is
invertible there (DLMF §21.5(i), implicit in 21.5.4). -/
@[dlmf 21.5.i "the modular action preserves the Siegel space and CΩ+D is invertible"]
theorem modular_mem_siegel {A B C D : Matrix ι ι ℤ} (hΓ : IsSymplecticBlocks A B C D)
    {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    IsUnit (rth21_cplx C * Ω + rth21_cplx D).det ∧
      (rth21_cplx A * Ω + rth21_cplx B) * (rth21_cplx C * Ω + rth21_cplx D)⁻¹ ∈
        siegelUpperHalfSpace ι := by
  obtain ⟨m1, m2, m3⟩ := p3t_blocks hΓ
  set a := rth21_cplx A
  set b := rth21_cplx B
  set c := rth21_cplx C
  set d := rth21_cplx D
  set M := c * Ω + d with hM
  set N := a * Ω + b with hN
  set Y := Ω.map Complex.im with hYdef
  have hYs : Yᵀ = Y := by
    have := hΩ.2.1.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have key : ∀ P : Matrix ι ι ℂ, (P * cᵀ + dᵀ) * N - (P * aᵀ + bᵀ) * M = Ω - P := by
    intro P
    have m4 : dᵀ * a - bᵀ * c = 1 := by
      have := congrArg transpose m3
      simpa [transpose_sub, transpose_mul] using this
    calc (P * cᵀ + dᵀ) * N - (P * aᵀ + bᵀ) * M =
        P * (cᵀ * a - aᵀ * c) * Ω - P * (aᵀ * d - cᵀ * b) + (dᵀ * a - bᵀ * c) * Ω +
          (dᵀ * b - bᵀ * d) := by rw [hN, hM]; noncomm_ring
      _ = Ω - P := by rw [m1, m3, m4, m2]; noncomm_ring
  have hMt : Mᵀ = Ω * cᵀ + dᵀ := by rw [hM, transpose_add, transpose_mul, hΩ.1]
  have hNt : Nᵀ = Ω * aᵀ + bᵀ := by rw [hN, transpose_add, transpose_mul, hΩ.1]
  have hMh : Mᴴ = Ωᴴ * cᵀ + dᵀ := by
    rw [hM, conjTranspose_add, conjTranspose_mul, p3t_cplx_conjTranspose, p3t_cplx_conjTranspose]
  have hNh : Nᴴ = Ωᴴ * aᵀ + bᵀ := by
    rw [hN, conjTranspose_add, conjTranspose_mul, p3t_cplx_conjTranspose, p3t_cplx_conjTranspose]
  have hT : Mᵀ * N = Nᵀ * M := by
    have := key Ω; rw [sub_self, ← hMt, ← hNt] at this; exact sub_eq_zero.mp this
  have hH : Mᴴ * N - Nᴴ * M = (2 * I) • Y.map ofReal := by
    rw [hMh, hNh, key, p3t_sub_conjTranspose hΩ.1]
  -- the quadratic form
  have hq : ∀ u : ι → ℂ, star (M *ᵥ u) ⬝ᵥ (N *ᵥ u) - star (N *ᵥ u) ⬝ᵥ (M *ᵥ u) =
      2 * I * (((fun i => (u i).re) ⬝ᵥ (Y *ᵥ fun i => (u i).re) +
        (fun i => (u i).im) ⬝ᵥ (Y *ᵥ fun i => (u i).im) : ℝ) : ℂ) := by
    intro u
    rw [← p3t_star_quad hYs, ← smul_eq_mul, ← dotProduct_smul, ← smul_mulVec, ← hH,
      sub_mulVec, dotProduct_sub, star_mulVec, star_mulVec, dotProduct_mulVec, dotProduct_mulVec,
      vecMul_vecMul, vecMul_vecMul, ← dotProduct_mulVec, ← dotProduct_mulVec]
  have hpos : ∀ u : ι → ℂ, u ≠ 0 → 0 < (fun i => (u i).re) ⬝ᵥ (Y *ᵥ fun i => (u i).re) +
      (fun i => (u i).im) ⬝ᵥ (Y *ᵥ fun i => (u i).im) := by
    intro u hu
    have h0 := rth21_posIm_of_mem hΩ
    have hnn : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (Y *ᵥ x) := fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · exact (h0 x hx).le
    by_cases hre : (fun i => (u i).re) = 0
    · have him : (fun i => (u i).im) ≠ 0 := by
        intro him; apply hu; funext i
        apply Complex.ext
        · exact congrFun hre i
        · exact congrFun him i
      exact add_pos_of_nonneg_of_pos (hnn _) (h0 _ him)
    · exact add_pos_of_pos_of_nonneg (h0 _ hre) (hnn _)
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hMv⟩ := (exists_mulVec_eq_zero_iff (M := M)).mpr h0
    have h1 := hq v
    rw [hMv, star_zero, zero_dotProduct, dotProduct_zero, sub_zero] at h1
    have hp := hpos v hv
    have : (2 * I) * (((fun i => (v i).re) ⬝ᵥ (Y *ᵥ fun i => (v i).re) +
        (fun i => (v i).im) ⬝ᵥ (Y *ᵥ fun i => (v i).im) : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (ofReal_ne_zero.mpr hp.ne')
    exact this h1.symm
  have hsymm : (N * M⁻¹)ᵀ = N * M⁻¹ := by
    rw [transpose_mul, transpose_nonsing_inv]
    have hMtu : IsUnit Mᵀ.det := by rwa [det_transpose]
    calc (Mᵀ)⁻¹ * Nᵀ = (Mᵀ)⁻¹ * (Nᵀ * M) * M⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = N * M⁻¹ := by
          rw [← hT, ← Matrix.mul_assoc, nonsing_inv_mul _ hMtu, Matrix.one_mul]
  refine ⟨hdet, hsymm, PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, ← Matrix.transpose_map, hsymm]
  · rw [star_trivial, ← rth21_im_quad_ofReal]
    set xc : ι → ℂ := fun i => (x i : ℂ) with hxc
    set u := M⁻¹ *ᵥ xc with hu_def
    have hMu : M *ᵥ u = xc := by
      rw [hu_def, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have hu : u ≠ 0 := by
      intro h
      apply hx
      funext i
      have := congrFun hMu i
      rw [h, mulVec_zero, hxc] at this
      simpa using this.symm
    have hsx : star xc = xc := by ext i; simp [hxc]
    have hw : xc ⬝ᵥ ((N * M⁻¹) *ᵥ xc) = star (M *ᵥ u) ⬝ᵥ (N *ᵥ u) := by
      rw [hMu, hsx, ← mulVec_mulVec]
    have hc : starRingEnd ℂ (star (M *ᵥ u) ⬝ᵥ (N *ᵥ u)) = star (N *ᵥ u) ⬝ᵥ (M *ᵥ u) := by
      simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [mul_comm]
    have h2 := hq u
    rw [← hc] at h2
    rw [hw]
    have h3 := congrArg Complex.im h2
    rw [Complex.sub_conj] at h3
    simp at h3
    linarith [hpos u hu]

omit [DecidableEq ι] in
/-- The Siegel upper half-space is convex. -/
lemma p3t_siegel_convex : Convex ℝ (siegelUpperHalfSpace ι) := by
  refine convex_iff_forall_pos.mpr fun Ω₁ h₁ Ω₂ h₂ a b ha hb hab => ⟨?_, ?_⟩
  · rw [transpose_add, transpose_smul, transpose_smul, h₁.1, h₂.1]
  · have e : (a • Ω₁ + b • Ω₂).map Complex.im = a • Ω₁.map Complex.im + b • Ω₂.map Complex.im := by
      ext i j; simp
    rw [e]
    exact (h₁.2.smul ha).add (h₂.2.smul hb)

/-- `iI` lies in the Siegel upper half-space. -/
lemma p3t_siegel_nonempty : (I • (1 : Matrix ι ι ℂ)) ∈ siegelUpperHalfSpace ι := by
  refine ⟨by simp, ?_⟩
  have e : (I • (1 : Matrix ι ι ℂ)).map Complex.im = 1 := by
    ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
  rw [e]; exact PosDef.one

/-- A continuous square root of `det(CΩ+D)` exists on the Siegel space (DLMF §21.5(i): the
branch of `√det[CΩ+D]` in 21.5.4 and 21.5.9). -/
@[dlmf 21.5.i "existence of a continuous branch of the square root of det(CΩ+D)"]
theorem exists_continuous_sqrt_det {C D : Matrix ι ι ℤ}
    (hdet : ∀ Ω ∈ siegelUpperHalfSpace ι, (rth21_cplx C * Ω + rth21_cplx D).det ≠ 0) :
    ∃ s : Matrix ι ι ℂ → ℂ, ContinuousOn s (siegelUpperHalfSpace ι) ∧
      ∀ Ω ∈ siegelUpperHalfSpace ι, s Ω ^ 2 = (rth21_cplx C * Ω + rth21_cplx D).det := by
  classical
  set S := siegelUpperHalfSpace ι
  have : LocallyConvexSpace ℝ (Matrix ι ι ℂ) :=
    inferInstanceAs (LocallyConvexSpace ℝ (ι → ι → ℂ))
  have hne : S.Nonempty := ⟨_, p3t_siegel_nonempty⟩
  have : ContractibleSpace S := p3t_siegel_convex.contractibleSpace hne
  have : LocallyPathConnectedSpace S := p3t_siegel_convex.locallyPathConnectedSpace
  let f : C(S, {z : ℂ // z ≠ 0}) := ⟨fun Ω => ⟨(rth21_cplx C * Ω.1 + rth21_cplx D).det,
    hdet Ω.1 Ω.2⟩, by
      refine Continuous.subtype_mk ?_ _
      exact (Continuous.matrix_det ((continuous_const.matrix_mul continuous_subtype_val).add
        continuous_const))⟩
  let a₀ : S := ⟨_, p3t_siegel_nonempty⟩
  set w := ((f a₀ : ℂ)) ^ ((2 : ℕ)⁻¹ : ℂ) with hw
  have hw0 : w ≠ 0 := by
    rw [hw, Ne, cpow_eq_zero_iff]; exact fun h => (f a₀).2 h.1
  have hw2 : w ^ 2 = f a₀ := by
    rw [hw]; exact cpow_nat_inv_pow _ two_ne_zero
  obtain ⟨F, ⟨-, hF⟩, -⟩ :=
    (isCoveringMap_npow (𝕜 := ℂ) 2 (by norm_num)).existsUnique_continuousMap_lifts
    f a₀ ⟨w, hw0⟩ (Subtype.ext hw2)
  refine ⟨fun Ω => if h : Ω ∈ S then (F ⟨Ω, h⟩ : ℂ) else 0, ?_, fun Ω hΩ => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : S.domRestrict (fun Ω => if h : Ω ∈ S then (F ⟨Ω, h⟩ : ℂ) else 0) =
        fun Ω : S => (F Ω : ℂ) := by
      funext Ω; simp [Set.domRestrict, Ω.2]
    rw [this]
    exact continuous_subtype_val.comp F.continuous
  · simp only [hΩ, dite_true]
    have := congrArg Subtype.val (congrFun hF ⟨Ω, hΩ⟩)
    exact this

/-- **Corrected 21.5.4.** For an integer symplectic `Γ = [[A,B],[C,D]]` with `diag(CDᵀ)` and
`diag(ABᵀ)` even (the theta group) and any continuous branch `s` of `√det(CΩ+D)` on the
Siegel space, there is an eighth root of unity `ξ` with
`θ([(CΩ+D)⁻¹]ᵀ z | (AΩ+B)(CΩ+D)⁻¹) = ξ s(Ω) exp(πi z·[(CΩ+D)⁻¹C]·z) θ(z|Ω)`.
Corrected from the printed DLMF formula: DLMF states this for all symplectic `Γ`, which is false
(for `Γ = [[I, B], [0, I]]`, `B = [[1, 3], [3, -1]]`, the ratio depends on `z`, `g = 2`), so the
theta-group condition is added and the square root is a continuous branch; the general case is
21.5.9. -/
@[dlmf 21.5.E4 "corrected: requires even diag(CDᵀ) and diag(ABᵀ); continuous square-root branch"]
theorem riemannTheta_modular {A B C D : Matrix ι ι ℤ} (hΓ : IsSymplecticBlocks A B C D)
    (hCD : ∀ i, Even ((C * Dᵀ) i i)) (hAB : ∀ i, Even ((A * Bᵀ) i i))
    {s : Matrix ι ι ℂ → ℂ} (hs : ContinuousOn s (siegelUpperHalfSpace ι))
    (hs2 : ∀ Ω ∈ siegelUpperHalfSpace ι, s Ω ^ 2 = (rth21_cplx C * Ω + rth21_cplx D).det) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ ∀ Ω ∈ siegelUpperHalfSpace ι, ∀ z : ι → ℂ,
      riemannTheta ((rth21_cplx C * Ω + rth21_cplx D)⁻¹ᵀ *ᵥ z)
          ((rth21_cplx A * Ω + rth21_cplx B) * (rth21_cplx C * Ω + rth21_cplx D)⁻¹) =
        ξ * s Ω * cexp (π * I * (z ⬝ᵥ (((rth21_cplx C * Ω + rth21_cplx D)⁻¹ * rth21_cplx C) *ᵥ
          z))) * riemannTheta z Ω := by
  sorry

/-! ## The generators (DLMF 21.5.5–21.5.8) -/

/-- `θ(Az|AΩAᵀ) = θ(z|Ω)` for an integer matrix `A` invertible over `ℤ` (DLMF 21.5.5,
`Γ = [[A, 0], [0, (A⁻¹)ᵀ]]`). Holds for every complex `Ω`.
Corrected from the printed DLMF formula: `A` must be invertible over `ℤ` (`A ∈ GL_g(ℤ)`, so that
`Γ` is an integer symplectic matrix), not merely `det A ≠ 0`. -/
@[dlmf 21.5.E5]
theorem riemannTheta_unimodular {A : Matrix ι ι ℤ} (hA : IsUnit A) (z : ι → ℂ)
    (Ω : Matrix ι ι ℂ) :
    riemannTheta (rth21_cplx A *ᵥ z) (rth21_cplx A * Ω * (rth21_cplx A)ᵀ) = riemannTheta z Ω := by
  obtain ⟨u, rfl⟩ := hA
  let e : (ι → ℤ) ≃ (ι → ℤ) :=
    { toFun := fun n => (u : Matrix ι ι ℤ)ᵀ *ᵥ n
      invFun := fun n => (↑u⁻¹ : Matrix ι ι ℤ)ᵀ *ᵥ n
      left_inv := fun n => by
        dsimp only
        rw [mulVec_mulVec, ← transpose_mul, Units.mul_inv, transpose_one, one_mulVec]
      right_inv := fun n => by
        dsimp only
        rw [mulVec_mulVec, ← transpose_mul, Units.inv_mul, transpose_one, one_mulVec] }
  rw [riemannTheta, riemannTheta]
  conv_rhs => rw [← e.tsum_eq]
  refine tsum_congr fun n => ?_
  have hcast : (fun i => ((e n i : ℤ) : ℂ)) =
      (rth21_cplx (u : Matrix ι ι ℤ))ᵀ *ᵥ fun i => (n i : ℂ) := by
    funext i
    simp [e, mulVec, dotProduct]
  rw [riemannThetaTerm, riemannThetaTerm, hcast]
  congr 3
  · rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  · rw [dotProduct_mulVec, ← mulVec_transpose]

lemma rth21_quad_mod_two (B : Matrix ι ι ℤ) (hB : Bᵀ = B) (n : ι → ℤ) :
    ((n ⬝ᵥ (B *ᵥ n) : ℤ) : ZMod 2) = ((∑ i, B i i * n i : ℤ) : ZMod 2) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  push_cast
  rw [← Finset.sum_product' (f := fun i j => ((n i : ℤ) : ZMod 2) * ((B i j : ZMod 2) *
    (n j : ZMod 2)))]
  have hsplit : ∀ p : ι × ι, ((n p.1 : ℤ) : ZMod 2) * ((B p.1 p.2 : ZMod 2) * (n p.2 : ZMod 2)) =
      (if p.1 = p.2 then ((n p.1 : ℤ) : ZMod 2) * ((B p.1 p.2 : ZMod 2) * (n p.2 : ZMod 2))
        else 0) +
      (if p.1 = p.2 then 0
        else ((n p.1 : ℤ) : ZMod 2) * ((B p.1 p.2 : ZMod 2) * (n p.2 : ZMod 2))) := by
    intro p; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun p _ => hsplit p, Finset.sum_add_distrib]
  have hoff : ∑ p ∈ (univ : Finset ι) ×ˢ univ, (if p.1 = p.2 then 0
      else ((n p.1 : ℤ) : ZMod 2) * ((B p.1 p.2 : ZMod 2) * (n p.2 : ZMod 2))) = 0 := by
    refine Finset.sum_ninvolution Prod.swap (fun p => ?_) (fun p hp => ?_) (fun p => by simp)
      (fun p => Prod.swap_swap p)
    · rcases p with ⟨i, j⟩
      by_cases h : i = j
      · subst h; simp
      · have hji : B j i = B i j := by
          simpa using congrFun (congrFun hB i) j
        simp only [Prod.swap_prod_mk, h, Ne.symm h, ite_false, hji]
        have h2 : (2 : ZMod 2) = 0 := rfl
        linear_combination ((n i : ZMod 2) * ((B i j : ZMod 2) * (n j : ZMod 2))) * h2
    · rcases p with ⟨i, j⟩
      intro hsw
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hsw
      simp [hsw.1] at hp
  rw [hoff, add_zero, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq univ i]
  simp only [Finset.mem_univ, ite_true]
  have hsq : ((n i : ℤ) : ZMod 2) * (n i : ZMod 2) = (n i : ZMod 2) := by
    have := ZMod.pow_card (p := 2) ((n i : ℤ) : ZMod 2)
    rw [sq] at this
    exact this
  rw [mul_left_comm, hsq, mul_comm]

/-- `θ(z|Ω + B) = θ(z + ½ diag B|Ω)` for a symmetric integer matrix `B` (DLMF 21.5.7,
`Γ = [[I, B], [0, I]]`). Holds for every complex `Ω`. -/
@[dlmf 21.5.E7]
theorem riemannTheta_add_symm_int {B : Matrix ι ι ℤ} (hB : Bᵀ = B) (z : ι → ℂ)
    (Ω : Matrix ι ι ℂ) :
    riemannTheta z (Ω + rth21_cplx B) = riemannTheta (z + fun i => (B i i : ℂ) / 2) Ω := by
  rw [riemannTheta, riemannTheta]
  refine tsum_congr fun n => ?_
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ n ⬝ᵥ (B *ᵥ n) - ∑ i, B i i * n i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).mp (rth21_quad_mod_two B hB n).symm
  have hq : (fun i => (n i : ℂ)) ⬝ᵥ (rth21_cplx B *ᵥ fun i => (n i : ℂ)) =
      ((n ⬝ᵥ (B *ᵥ n) : ℤ) : ℂ) := by
    simp [dotProduct, mulVec]
  have hd : (fun i => (n i : ℂ)) ⬝ᵥ (fun i => (B i i : ℂ) / 2) =
      ((∑ i, B i i * n i : ℤ) : ℂ) / 2 := by
    simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [riemannThetaTerm, riemannThetaTerm, add_mulVec, dotProduct_add, dotProduct_add, hq, hd]
  have hk' : ((n ⬝ᵥ (B *ᵥ n) : ℤ) : ℂ) = ((∑ i, B i i * n i : ℤ) : ℂ) + 2 * (k : ℂ) := by
    rw [← sub_eq_iff_eq_add']
    exact_mod_cast hk
  rw [hk', show ∀ a b c : ℂ, 2 * π * I * ((1 / 2 : ℂ) * (a + (b + 2 * k)) + c) =
      2 * π * I * ((1 / 2 : ℂ) * a + (c + b / 2)) + 2 * π * I * k by intros; ring,
    Complex.exp_add, rth21_exp_int, mul_one]

/-- `θ(z|Ω + B) = θ(z|Ω)` for a symmetric integer matrix `B` with even diagonal
(DLMF 21.5.6, `Γ = [[I, B], [0, I]]`). -/
@[dlmf 21.5.E6]
theorem riemannTheta_add_symm_int_even {B : Matrix ι ι ℤ} (hB : Bᵀ = B)
    (heven : ∀ i, Even (B i i)) (z : ι → ℂ) (Ω : Matrix ι ι ℂ) :
    riemannTheta z (Ω + rth21_cplx B) = riemannTheta z Ω := by
  choose m hm using heven
  rw [riemannTheta_add_symm_int hB]
  have : (fun i => (B i i : ℂ) / 2) = fun i => (m i : ℂ) := by
    funext i
    rw [hm i]
    push_cast
    ring
  rw [this, riemannTheta_add_int]

/-- The inversion `θ(Ω⁻¹z | -Ω⁻¹) = s(Ω) exp(πi z·Ω⁻¹·z) θ(z|Ω)` (DLMF 21.5.8,
`Γ = [[0, -I], [I, 0]]`), where `s` is the continuous branch of `√det(-iΩ)` on the Siegel
space with `s(iI) = 1`. Corrected from the printed DLMF formula: DLMF prescribes the principal
value of `√det(-iΩ)`, which is this branch only for `g ≤ 2` (`riemannTheta_inversion_principal`);
for `g = 3`, `Ω = τI₃`, `τ = -1.1√3 + i`, the ratio is minus the principal root. -/
@[dlmf 21.5.E8 "corrected branch: continuous square root with value 1 at Ω = iI"]
theorem riemannTheta_inversion {s : Matrix ι ι ℂ → ℂ}
    (hs : ContinuousOn s (siegelUpperHalfSpace ι))
    (hs2 : ∀ Ω ∈ siegelUpperHalfSpace ι, s Ω ^ 2 = (-I • Ω).det)
    (hs1 : s (I • 1) = 1) {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) (z : ι → ℂ) :
    riemannTheta (Ω⁻¹ *ᵥ z) (-Ω⁻¹) =
      s Ω * cexp (π * I * (z ⬝ᵥ (Ω⁻¹ *ᵥ z))) * riemannTheta z Ω := by
  sorry

/-- DLMF 21.5.8 with the principal square root, valid for genus `g ≤ 2`.
Corrected from the printed DLMF formula: the principal root is restricted to `g ≤ 2`, where the
eigenvalues of `-iΩ` (in the right half-plane) multiply without crossing the cut; it fails for
`g ≥ 3` (see `riemannTheta_inversion`). -/
@[dlmf 21.5.E8 "principal square root; valid for g ≤ 2 (false for g ≥ 3)"]
theorem riemannTheta_inversion_principal (hg : Fintype.card ι ≤ 2) {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) (z : ι → ℂ) :
    riemannTheta (Ω⁻¹ *ᵥ z) (-Ω⁻¹) =
      (-I • Ω).det ^ (1 / 2 : ℂ) * cexp (π * I * (z ⬝ᵥ (Ω⁻¹ *ᵥ z))) * riemannTheta z Ω := by
  sorry

lemma rth21_inv_fin_one {τ : ℂ} (hτ : τ ≠ 0) : (!![τ] : Matrix (Fin 1) (Fin 1) ℂ)⁻¹ = !![τ⁻¹] := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i; fin_cases j
  simp [hτ]

lemma rth21_riemannTheta_fin_one' (w σ : ℂ) : riemannTheta ![w] !![σ] = jacobiTheta₂ w σ := by
  rw [riemannTheta_fin_one, DLMF.Elliptic.jacobiThetaThreeTau,
    mul_div_cancel_left₀ _ DLMF.Elliptic.pi_ne_zero']

/-- DLMF 21.5.8 for `g = 1`: `θ(z/τ | -1/τ) = √(-iτ) exp(πi z²/τ) θ(z|τ)` with the principal
square root, from Mathlib's `jacobiTheta₂_functional_equation`. -/
@[dlmf 21.5.E8 "g = 1, principal square root"]
theorem riemannTheta_inversion_fin_one {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    riemannTheta ((!![τ] : Matrix (Fin 1) (Fin 1) ℂ)⁻¹ *ᵥ ![z]) (-(!![τ])⁻¹) =
      (-I • (!![τ] : Matrix (Fin 1) (Fin 1) ℂ)).det ^ (1 / 2 : ℂ) *
        cexp (π * I * (![z] ⬝ᵥ ((!![τ] : Matrix (Fin 1) (Fin 1) ℂ)⁻¹ *ᵥ ![z]))) *
          riemannTheta ![z] !![τ] := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hv : (!![τ⁻¹] : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ ![z] = ![z / τ] := by
    ext i; fin_cases i; simp [mulVec, dotProduct, div_eq_inv_mul]
  have hm : -(!![τ⁻¹] : Matrix (Fin 1) (Fin 1) ℂ) = !![-1 / τ] := by
    ext i j; fin_cases i; fin_cases j; simp [neg_div]
  have hdet : (-I • (!![τ] : Matrix (Fin 1) (Fin 1) ℂ)).det = -I * τ := by
    simp
  have hdot : ![z] ⬝ᵥ ![z / τ] = z ^ 2 / τ := by
    simp [dotProduct, sq, mul_div_assoc]
  rw [rth21_inv_fin_one hτ0, hv, hm, hdet, hdot, rth21_riemannTheta_fin_one',
    rth21_riemannTheta_fin_one', jacobiTheta₂_functional_equation z τ]
  have hne : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [hτ0, I_ne_zero]
  have hexp : cexp (π * I * (z ^ 2 / τ)) * cexp (-π * I * z ^ 2 / τ) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  rw [show ∀ a b c e : ℂ, a * b * (1 / a * c * e) = (a * (1 / a)) * (b * c) * e by
      intros; ring, mul_one_div_cancel hne, hexp, one_mul, one_mul]

/-! ## Characteristics (DLMF 21.5.9) -/

/-- The modular transformation of theta functions with characteristics (DLMF 21.5.9): for an
integer symplectic `Γ = [[A,B],[C,D]]` and a continuous branch `s` of `√det(CΩ+D)` there is a
constant `κ(α, β, Γ)`, independent of `z` and `Ω`, with
`θ[Dα - Cβ + ½diag(CDᵀ); -Bα + Aβ + ½diag(ABᵀ)]([(CΩ+D)⁻¹]ᵀ z | (AΩ+B)(CΩ+D)⁻¹)
  = κ s(Ω) exp(πi z·[(CΩ+D)⁻¹C]·z) θ[α;β](z|Ω)`. -/
@[dlmf 21.5.E9 "continuous square-root branch; κ independent of z and Ω"]
theorem riemannThetaChar_modular {A B C D : Matrix ι ι ℤ} (hΓ : IsSymplecticBlocks A B C D)
    (α β : ι → ℝ) {s : Matrix ι ι ℂ → ℂ} (hs : ContinuousOn s (siegelUpperHalfSpace ι))
    (hs2 : ∀ Ω ∈ siegelUpperHalfSpace ι, s Ω ^ 2 = (rth21_cplx C * Ω + rth21_cplx D).det) :
    ∃ κ : ℂ, ∀ Ω ∈ siegelUpperHalfSpace ι, ∀ z : ι → ℂ,
      riemannThetaChar
          (rth21_real D *ᵥ α - rth21_real C *ᵥ β + fun i => ((C * Dᵀ) i i : ℝ) / 2)
          (-(rth21_real B *ᵥ α) + rth21_real A *ᵥ β + fun i => ((A * Bᵀ) i i : ℝ) / 2)
          ((rth21_cplx C * Ω + rth21_cplx D)⁻¹ᵀ *ᵥ z)
          ((rth21_cplx A * Ω + rth21_cplx B) * (rth21_cplx C * Ω + rth21_cplx D)⁻¹) =
        κ * s Ω * cexp (π * I * (z ⬝ᵥ (((rth21_cplx C * Ω + rth21_cplx D)⁻¹ * rth21_cplx C) *ᵥ
          z))) * riemannThetaChar α β z Ω := by
  sorry

end DLMF.RiemannTheta
