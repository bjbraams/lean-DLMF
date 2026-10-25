/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Symmetry
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

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
lemma symplecticJ_eq_neg {R : Type*} [CommRing R] : symplecticJ ι R = -Matrix.J ι R := by
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

/-- A symplectic `Γ` maps the Siegel space to itself, `Ω ↦ (AΩ+B)(CΩ+D)⁻¹`, and `CΩ+D` is
invertible there (DLMF §21.5(i), implicit in 21.5.4). -/
@[dlmf 21.5.i "the modular action preserves the Siegel space and CΩ+D is invertible"]
theorem modular_mem_siegel {A B C D : Matrix ι ι ℤ} (hΓ : IsSymplecticBlocks A B C D)
    {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    IsUnit (rth21_cplx C * Ω + rth21_cplx D).det ∧
      (rth21_cplx A * Ω + rth21_cplx B) * (rth21_cplx C * Ω + rth21_cplx D)⁻¹ ∈
        siegelUpperHalfSpace ι := by
  sorry

/-- A continuous square root of `det(CΩ+D)` exists on the Siegel space (DLMF §21.5(i): the
branch of `√det[CΩ+D]` in 21.5.4 and 21.5.9). -/
@[dlmf 21.5.i "existence of a continuous branch of the square root of det(CΩ+D)"]
theorem exists_continuous_sqrt_det {C D : Matrix ι ι ℤ}
    (hdet : ∀ Ω ∈ siegelUpperHalfSpace ι, (rth21_cplx C * Ω + rth21_cplx D).det ≠ 0) :
    ∃ s : Matrix ι ι ℂ → ℂ, ContinuousOn s (siegelUpperHalfSpace ι) ∧
      ∀ Ω ∈ siegelUpperHalfSpace ι, s Ω ^ 2 = (rth21_cplx C * Ω + rth21_cplx D).det := by
  sorry

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
