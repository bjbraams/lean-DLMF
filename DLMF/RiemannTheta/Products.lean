/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Symmetry

/-!
# Products of Riemann theta functions (DLMF §21.6)

This file proves the Riemann identity (DLMF 21.6.1–21.6.4) for a rational orthogonal `h × h`
matrix `T`, its `h = 4` example (DLMF 21.6.5–21.6.7) and the addition formula DLMF 21.6.8.

## Main definitions

* `riemannK`: the set `𝒦 = ℤ^{g×h}T / (ℤ^{g×h}T ∩ ℤ^{g×h})` (DLMF 21.6.1), as a quotient type.
* `riemannD`: the number `𝒟 = |Tᵀℤ^h / (Tᵀℤ^h ∩ ℤ^h)|` (DLMF 21.6.2).
* `IsRiemannKRepresentatives`: a finite set of representatives of `𝒦` in `ℤ^{g×h}T`.
* `riemannTExample`: the rational orthogonal matrix of DLMF 21.6.5.

## Main results

* `riemann_identity`: the Riemann identity (DLMF 21.6.3).
* `riemann_identity_char`: the Riemann identity with characteristics (DLMF 21.6.4).
* `riemannTExample_mul_transpose`, `riemannTExample_rat`: the matrix of DLMF 21.6.5 is
  orthogonal and rational.
* `riemannTheta_four_product`, `riemannThetaChar_four_product`: DLMF 21.6.6–21.6.7.
* `riemannThetaChar_mul_addition`: the addition formula (DLMF 21.6.8).

## Implementation notes

The sums over `𝒦` in 21.6.3–21.6.4 are taken over a finite set of representatives
`R ⊆ ℤ^{g×h}T` mapping bijectively onto `𝒦`. The summand of 21.6.3 depends on the
representatives only through their class provided the representatives lie in `ℤ^{g×h}T`: with
arbitrary real representatives modulo integer matrices the identity fails (numerically, for
`g = 1` and `T = [[3/5, 4/5], [4/5, -3/5]]`), since the factor `exp(2πi tr AᵀB)` is not
invariant under integer shifts of `B` outside `ℤ^{g×h}T`.

In 21.6.4 DLMF calls the characteristic vectors `c_j, d_j` "h-dimensional"; they are the
`g`-dimensional columns of `g × h` matrices, as the formula requires.
-/

@[expose] public noncomputable section

open Complex Matrix Finset
open scoped Real

namespace DLMF.RiemannTheta

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ## The sets `𝒦` and the number `𝒟` (DLMF 21.6.1–21.6.2) -/

/-- A real matrix with integer entries. -/
def IsIntegerMatrix {m n : Type*} (A : Matrix m n ℝ) : Prop := ∃ M : Matrix m n ℤ,
    A = M.map Int.cast

/-- Identity under the stated parameter and domain assumptions: `Equivalence fun (A A' : Matrix m
n ℝ) => IsIntegerMatrix (A - A')`. -/
lemma equivalence_isInt_sub {m n : Type*} :
    Equivalence fun (A A' : Matrix m n ℝ) => IsIntegerMatrix (A - A') where
  refl A := ⟨0, by ext; simp⟩
  symm := fun {A A'} ⟨M, h⟩ => ⟨-M, by rw [← neg_sub, h]; ext; simp⟩
  trans := fun {A B C} ⟨M₁, h₁⟩ ⟨M₂, h₂⟩ =>
    ⟨M₁ + M₂, by rw [show A - C = (A - B) + (B - C) by abel, h₁, h₂]; ext; simp⟩

/-- The set `ℤ^{g×h} T` of `g × h` matrices `N T` with `N` an integer matrix. -/
def riemannKSet (ι : Type*) (T : Matrix κ κ ℝ) : Set (Matrix ι κ ℝ) :=
  {A | ∃ N : Matrix ι κ ℤ, A = N.map Int.cast * T}

/-- Equivalence modulo integer matrices on `ℤ^{g×h} T`. -/
def riemannKSetoid (ι : Type*) (T : Matrix κ κ ℝ) : Setoid (riemannKSet ι T) where
  r A A' := IsIntegerMatrix (A.1 - A'.1)
  iseqv := ⟨fun A => equivalence_isInt_sub.refl A.1, fun h => equivalence_isInt_sub.symm h,
    fun h h' => equivalence_isInt_sub.trans h h'⟩

/-- `𝒦 = ℤ^{g×h}T / (ℤ^{g×h}T ∩ ℤ^{g×h})` (DLMF 21.6.1). -/
@[dlmf 21.6.E1]
def riemannK (ι : Type*) (T : Matrix κ κ ℝ) : Type _ := Quotient (riemannKSetoid ι T)

/-- The set `Tᵀ ℤ^h` of vectors `Tᵀ m`, `m ∈ ℤ^h`. -/
def riemannDSet (T : Matrix κ κ ℝ) : Set (κ → ℝ) :=
  {v | ∃ m : κ → ℤ, v = Tᵀ *ᵥ fun k => (m k : ℝ)}

/-- Equivalence modulo integer vectors on `Tᵀ ℤ^h`. -/
def riemannDSetoid (T : Matrix κ κ ℝ) : Setoid (riemannDSet T) where
  r v v' := ∃ m : κ → ℤ, v.1 - v'.1 = fun k => (m k : ℝ)
  iseqv := ⟨fun v => ⟨0, by ext; simp⟩,
    fun {v v'} ⟨m, h⟩ => ⟨-m, by rw [← neg_sub, h]; ext; simp⟩,
    fun {u v w} ⟨m₁, h₁⟩ ⟨m₂, h₂⟩ =>
      ⟨m₁ + m₂, by rw [show u.1 - w.1 = (u.1 - v.1) + (v.1 - w.1) by abel, h₁, h₂]; ext; simp⟩⟩

/-- `𝒟 = |Tᵀ ℤ^h / (Tᵀ ℤ^h ∩ ℤ^h)|` (DLMF 21.6.2); `Nat.card` of the quotient. -/
@[dlmf 21.6.E2]
def riemannD (T : Matrix κ κ ℝ) : ℕ := Nat.card (Quotient (riemannDSetoid T))

/-- A finite set `R ⊆ ℤ^{g×h}T` of representatives of `𝒦`: the map `R → 𝒦` is bijective. -/
def IsRiemannKRepresentatives (T : Matrix κ κ ℝ) (R : Finset (Matrix ι κ ℝ)) : Prop :=
  ∃ hR : ∀ A ∈ R, A ∈ riemannKSet ι T,
    Function.Bijective fun A : R =>
      (Quotient.mk (riemannKSetoid ι T) ⟨A.1, hR A.1 A.2⟩ : riemannK ι T)

/-- The complex matrix of a real matrix. -/
abbrev realMatrixToComplex {m n : Type*} (A : Matrix m n ℝ) : Matrix m n ℂ := A.map Complex.ofReal

/-! ## The Riemann identity (DLMF 21.6.3–21.6.4) -/

/-- The Riemann identity (DLMF 21.6.3): for a rational orthogonal `h × h` matrix `T`, any
`g × h` matrix `Z` with columns `z_j`, and representatives `R ⊆ ℤ^{g×h}T` of `𝒦`,
`∏ⱼ θ(∑ₖ Tⱼₖ zₖ|Ω) = 𝒟^{-g} ∑_{A,B ∈ R} exp(2πi tr[½ AᵀΩA + Aᵀ(Z + B)])
  ∏ⱼ θ(zⱼ + Ω aⱼ + bⱼ|Ω)`. -/
@[dlmf 21.6.E3 "representatives of 𝒦 taken in ℤ^{g×h}T"]
theorem riemann_identity [DecidableEq κ] {T : Matrix κ κ ℝ}
    (hTrat : ∀ j k, ∃ q : ℚ, T j k = q) (hT : T * Tᵀ = 1)
    {R : Finset (Matrix ι κ ℝ)} (hR : IsRiemannKRepresentatives T R)
    {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) (Z : Matrix ι κ ℂ) :
    ∏ j, riemannTheta (fun i => ∑ k, (T j k : ℂ) * Z i k) Ω =
      ((riemannD T : ℂ)⁻¹) ^ Fintype.card ι * ∑ A ∈ R, ∑ B ∈ R,
        cexp (2 * π * I * Matrix.trace
            ((1 / 2 : ℂ) • ((realMatrixToComplex A)ᵀ * Ω * realMatrixToComplex A) +
          (realMatrixToComplex A)ᵀ * (Z + realMatrixToComplex B))) *
        ∏ j, riemannTheta ((fun i => Z i j) + (Ω *ᵥ fun i => (A i j : ℂ)) +
          fun i => (B i j : ℂ)) Ω := by
  sorry

/-- The Riemann identity with characteristics (DLMF 21.6.4): for real `g × h` matrices `C`,
`D` with columns `c_j`, `d_j`,
`∏ⱼ θ[∑ₖ Tⱼₖ cₖ; ∑ₖ Tⱼₖ dₖ](∑ₖ Tⱼₖ zₖ|Ω) = 𝒟^{-g} ∑_{A,B ∈ R} exp(-2πi ∑ⱼ bⱼ·cⱼ)
  ∏ⱼ θ[aⱼ + cⱼ; bⱼ + dⱼ](zⱼ|Ω)`.
Corrected from the printed DLMF formula: `c_j`, `d_j` are `g`-dimensional (characteristics of a
genus-`g` theta function), not `h`-dimensional as printed. Taking the representatives of `𝒦` in
`ℤ^{g×h}T` (`IsRiemannKRepresentatives`) follows DLMF's own definition 21.6.1. -/
@[dlmf 21.6.E4 "c_j, d_j are g-dimensional columns; representatives in ℤ^{g×h}T"]
theorem riemann_identity_char [DecidableEq κ] {T : Matrix κ κ ℝ}
    (hTrat : ∀ j k, ∃ q : ℚ, T j k = q) (hT : T * Tᵀ = 1)
    {R : Finset (Matrix ι κ ℝ)} (hR : IsRiemannKRepresentatives T R)
    {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) (Z : Matrix ι κ ℂ)
    (C D : Matrix ι κ ℝ) :
    ∏ j, riemannThetaChar (fun i => ∑ k, T j k * C i k) (fun i => ∑ k, T j k * D i k)
        (fun i => ∑ k, (T j k : ℂ) * Z i k) Ω =
      ((riemannD T : ℂ)⁻¹) ^ Fintype.card ι * ∑ A ∈ R, ∑ B ∈ R,
        cexp (-2 * π * I * ∑ j, ∑ i, (B i j * C i j : ℝ)) *
        ∏ j, riemannThetaChar (fun i => A i j + C i j) (fun i => B i j + D i j)
          (fun i => Z i j) Ω := by
  sorry

/-! ## The example `h = 4` (DLMF 21.6.5–21.6.7) -/

/-- The rational orthogonal matrix `T = ½[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]`
(DLMF 21.6.5). -/
@[dlmf 21.6.E5]
def riemannTExample : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 2, 1 / 2, 1 / 2, 1 / 2; 1 / 2, 1 / 2, -1 / 2, -1 / 2;
     1 / 2, -1 / 2, 1 / 2, -1 / 2; 1 / 2, -1 / 2, -1 / 2, 1 / 2]

/-- The matrix of 21.6.5 is orthogonal. -/
@[dlmf 21.6.E5 "T is orthogonal"]
theorem riemannTExample_mul_transpose : riemannTExample * riemannTExampleᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [riemannTExample, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.transpose_apply] <;> norm_num

/-- The matrix of 21.6.5 has rational entries. -/
@[dlmf 21.6.E5 "T has rational entries"]
theorem riemannTExample_rat (j k : Fin 4) : ∃ q : ℚ, riemannTExample j k = q := by
  refine ⟨(!![1 / 2, 1 / 2, 1 / 2, 1 / 2; 1 / 2, 1 / 2, -1 / 2, -1 / 2;
     1 / 2, -1 / 2, 1 / 2, -1 / 2; 1 / 2, -1 / 2, -1 / 2, 1 / 2] : Matrix (Fin 4) (Fin 4) ℚ) j k,
    ?_⟩
  fin_cases j <;> fin_cases k <;> simp [riemannTExample]

/-- The half-integer vector `a/2` for `a ∈ {0,1}^g`, a representative of `½ℤ^g/ℤ^g`. -/
abbrev halfBinaryVector (a : ι → Fin 2) : ι → ℝ := fun i => ((a i : ℕ) : ℝ) / 2

/-! ## Addition formula (DLMF 21.6.8) -/

/-- Formula under the stated hypotheses: `(2 • Ω) ∈ siegelUpperHalfSpace ι`. -/
private lemma two_smul_mem_siegelUpperHalfSpace {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    (2 • Ω) ∈ siegelUpperHalfSpace ι := by
  refine ⟨by rw [transpose_smul, hΩ.1], ?_⟩
  have : (2 • Ω).map Complex.im = Ω.map Complex.im + Ω.map Complex.im := by
    ext i j; simp [two_smul]
  rw [this]
  exact hΩ.2.add hΩ.2

/-- The residue class `t mod 2` in `Fin 2`. -/
def intModTwo (t : ℤ) : Fin 2 :=
  ⟨(t % 2).toNat, by omega⟩

/-- Identity under the stated parameter and domain assumptions: `(((intModTwo t : ℕ)) : ℤ) = t
% 2`. -/
private lemma val_intModTwo (t : ℤ) : (((intModTwo t : ℕ)) : ℤ) = t % 2 := by
  simp only [intModTwo]
  omega

/-- Identity under the stated parameter and domain assumptions: `intModTwo (2 * l + (ν : ℕ)) =
ν`. -/
private lemma intModTwo_two_mul_add (l : ℤ) (ν : Fin 2) : intModTwo (2 * l + (ν : ℕ)) = ν := by
  ext
  simp only [intModTwo]
  have := ν.2
  omega

/-- The bijection `(ν, k, l) ↦ (k + l + ν, k - l)` from `{0,1}^g × ℤ^g × ℤ^g` onto
`ℤ^g × ℤ^g` used in the addition formula. -/
def additionIndexEquiv (ι : Type*) :
    (ι → Fin 2) × (ι → ℤ) × (ι → ℤ) ≃ (ι → ℤ) × (ι → ℤ) where
  toFun q := (fun i => q.2.1 i + q.2.2 i + ((q.1 i : ℕ) : ℤ), fun i => q.2.1 i - q.2.2 i)
  invFun p := (fun i => intModTwo (p.1 i - p.2 i),
    fun i => (p.1 i + p.2 i - ((intModTwo (p.1 i - p.2 i) : ℕ) : ℤ)) / 2,
    fun i => (p.1 i - p.2 i - ((intModTwo (p.1 i - p.2 i) : ℕ) : ℤ)) / 2)
  left_inv q := by
    rcases q with ⟨ν, k, l⟩
    have h : ∀ i, k i + l i + ((ν i : ℕ) : ℤ) - (k i - l i) = 2 * l i + ((ν i : ℕ) : ℤ) := by
      intro i; ring
    simp only [h, intModTwo_two_mul_add]
    refine Prod.ext (funext fun i => rfl) (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
    · simp only; omega
    · simp only; omega
  right_inv p := by
    rcases p with ⟨n, m⟩
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp only
      have := val_intModTwo (n i - m i)
      omega
    · simp only
      have := val_intModTwo (n i - m i)
      omega

/-- Identity under the stated parameter and domain assumptions: `riemannThetaCharTerm ((1 / 2 : ℝ)
• (α + β + fun i => ((ν i : ℕ) : ℝ))) (γ + δ) (z₁ + z₂) (2 • Ω) k * riemannThetaCharTerm ((1 /
2 : ℝ) • (α - β + fun i => ((ν i : ℕ) : ℝ))) (γ - δ) (z₁ - z₂) (2 • Ω) l =
riemannThetaCharTerm α γ z₁ Ω (additionIndexEquiv ι (ν, k, l)).1 * riemannThetaCharTerm β δ z₂ Ω
(additionIndexEquiv ι (ν, k, l)).2`. -/
private lemma riemannThetaCharTerm_two_smul_mul (α β γ δ : ι → ℝ) (z₁ z₂ : ι → ℂ) (Ω : Matrix ι ι ℂ)
    (ν : ι → Fin 2) (k l : ι → ℤ) :
    riemannThetaCharTerm ((1 / 2 : ℝ) • (α + β + fun i => ((ν i : ℕ) : ℝ))) (γ + δ)
        (z₁ + z₂) (2 • Ω) k *
      riemannThetaCharTerm ((1 / 2 : ℝ) • (α - β + fun i => ((ν i : ℕ) : ℝ))) (γ - δ)
        (z₁ - z₂) (2 • Ω) l =
    riemannThetaCharTerm α γ z₁ Ω (additionIndexEquiv ι (ν, k, l)).1 *
      riemannThetaCharTerm β δ z₂ Ω (additionIndexEquiv ι (ν, k, l)).2 := by
  simp only [riemannThetaCharTerm, additionIndexEquiv, Equiv.coe_fn_mk, ← Complex.exp_add]
  congr 1
  set U : ι → ℂ := fun i => ((k i + l i + ((ν i : ℕ) : ℤ) : ℤ) : ℂ) + (α i : ℂ)
  set W : ι → ℂ := fun i => ((k i - l i : ℤ) : ℂ) + (β i : ℂ)
  have hP : (fun i => (k i : ℂ) + ((((1 / 2 : ℝ) • (α + β + fun i => ((ν i : ℕ) : ℝ))) i : ℝ) :
      ℂ)) = (1 / 2 : ℂ) • (U + W) := by
    funext i; simp [U, W]; ring
  have hQ : (fun i => (l i : ℂ) + ((((1 / 2 : ℝ) • (α - β + fun i => ((ν i : ℕ) : ℝ))) i : ℝ) :
      ℂ)) = (1 / 2 : ℂ) • (U - W) := by
    funext i; simp [U, W]; ring
  have h1 : (fun i => (z₁ + z₂) i + (((γ + δ) i : ℝ) : ℂ)) =
      (fun i => z₁ i + (γ i : ℂ)) + fun i => z₂ i + (δ i : ℂ) := by
    funext i; simp; ring
  have h2 : (fun i => (z₁ - z₂) i + (((γ - δ) i : ℝ) : ℂ)) =
      (fun i => z₁ i + (γ i : ℂ)) - fun i => z₂ i + (δ i : ℂ) := by
    funext i; simp; ring
  rw [hP, hQ, h1, h2]
  set Z₁ : ι → ℂ := fun i => z₁ i + (γ i : ℂ)
  set Z₂ : ι → ℂ := fun i => z₂ i + (δ i : ℂ)
  have hΩ2 : (2 • Ω : Matrix ι ι ℂ) = (2 : ℂ) • Ω := by rw [two_smul, two_smul]
  rw [hΩ2]
  simp only [smul_mulVec, mulVec_smul, mulVec_add, mulVec_sub, smul_dotProduct, dotProduct_smul,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub, smul_eq_mul]
  ring

/-- The addition formula (DLMF 21.6.8): for `α, β, γ, δ ∈ ℝ^g`,
`θ[α;γ](z₁|Ω) θ[β;δ](z₂|Ω) = ∑_{ν ∈ ℤ^g/2ℤ^g} θ[½(α+β+ν); γ+δ](z₁+z₂|2Ω)
  θ[½(α-β+ν); γ-δ](z₁-z₂|2Ω)`, with `ν` running over `{0,1}^g`. -/
@[dlmf 21.6.E8]
theorem riemannThetaChar_mul_addition [DecidableEq ι] {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) (α β γ δ : ι → ℝ) (z₁ z₂ : ι → ℂ) :
    riemannThetaChar α γ z₁ Ω * riemannThetaChar β δ z₂ Ω =
      ∑ ν : ι → Fin 2,
        riemannThetaChar ((1 / 2 : ℝ) • (α + β + fun i => ((ν i : ℕ) : ℝ))) (γ + δ)
            (z₁ + z₂) (2 • Ω) *
          riemannThetaChar ((1 / 2 : ℝ) • (α - β + fun i => ((ν i : ℕ) : ℝ))) (γ - δ)
            (z₁ - z₂) (2 • Ω) := by
  have h2Ω := two_smul_mem_siegelUpperHalfSpace hΩ
  rw [riemannThetaChar, riemannThetaChar,
    tsum_mul_tsum_of_summable_norm (summable_norm_riemannThetaCharTerm α γ z₁ hΩ)
      (summable_norm_riemannThetaCharTerm β δ z₂ hΩ)]
  have hsum := summable_mul_of_summable_norm (summable_norm_riemannThetaCharTerm α γ z₁ hΩ)
    (summable_norm_riemannThetaCharTerm β δ z₂ hΩ)
  rw [← (additionIndexEquiv ι).tsum_eq]
  have hsum' := (additionIndexEquiv ι).summable_iff.mpr hsum
  simp only [Function.comp_def] at hsum' ⊢
  rw [hsum'.tsum_prod, tsum_fintype]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [riemannThetaChar, riemannThetaChar,
    tsum_mul_tsum_of_summable_norm (summable_norm_riemannThetaCharTerm _ _ _ h2Ω)
      (summable_norm_riemannThetaCharTerm _ _ _ h2Ω)]
  exact tsum_congr fun c => (riemannThetaCharTerm_two_smul_mul α β γ δ z₁ z₂ Ω ν c.1 c.2).symm

/-! ## Proof of the example 21.6.6 from the addition formula -/

/-- The characteristic vector `(a + ν)/2`. -/
abbrev halfBinarySum (a ν : ι → Fin 2) : ι → ℝ := fun i => (((a i : ℕ) + (ν i : ℕ) : ℕ) : ℝ) / 2

/-- Identity under the stated parameter and domain assumptions: `riemannTheta w₁ Ω * riemannTheta
w₂ Ω = ∑ ν : ι → Fin 2, riemannThetaChar (halfBinaryVector ν) 0 (w₁ + w₂) (2 • Ω) * riemannThetaChar
(halfBinaryVector ν) 0 (w₁ - w₂) (2 • Ω)`. -/
private lemma riemannTheta_mul_riemannTheta_eq_sum [DecidableEq ι] {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι)
    (w₁ w₂ : ι → ℂ) :
    riemannTheta w₁ Ω * riemannTheta w₂ Ω =
      ∑ ν : ι → Fin 2, riemannThetaChar (halfBinaryVector ν) 0 (w₁ + w₂) (2 • Ω) *
        riemannThetaChar (halfBinaryVector ν) 0 (w₁ - w₂) (2 • Ω) := by
  rw [← riemannThetaChar_zero w₁, ← riemannThetaChar_zero w₂,
    riemannThetaChar_mul_addition hΩ]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have h1 : (1 / 2 : ℝ) • ((0 : ι → ℝ) + 0 + fun i => ((ν i : ℕ) : ℝ)) = halfBinaryVector ν := by
    funext i; simp [halfBinaryVector]; ring
  have h2 : (1 / 2 : ℝ) • ((0 : ι → ℝ) - 0 + fun i => ((ν i : ℕ) : ℝ)) = halfBinaryVector ν := by
    funext i; simp [halfBinaryVector]; ring
  rw [h1, h2, add_zero, sub_zero]

/-- Identity under the stated parameter and domain assumptions: `riemannThetaChar (c + fun i => (m
i : ℝ)) 0 z Ω = riemannThetaChar c 0 z Ω`. -/
private lemma riemannThetaChar_add_natCast_zero (c : ι → ℝ) (m : ι → ℕ) (z : ι → ℂ)
    (Ω : Matrix ι ι ℂ) :
    riemannThetaChar (c + fun i => (m i : ℝ)) 0 z Ω = riemannThetaChar c 0 z Ω := by
  have h := riemannThetaChar_add_int c 0 z Ω (fun i => (m i : ℤ)) 0
  have e1 : (c + fun i => (((m i : ℤ) : ℝ))) = c + fun i => (m i : ℝ) := by
    funext i; simp
  have e2 : ((0 : ι → ℝ) + fun i => (((0 : ι → ℤ) i : ℤ) : ℝ)) = 0 := by
    funext i; simp
  rw [e1, e2] at h
  rw [h]
  simp [dotProduct]

/-- Identity under the stated parameter and domain assumptions: `riemannThetaChar c (fun i => ((b
i : ℕ) : ℝ)) z Ω = cexp (2 * π * I * ((fun i => (c i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) *
riemannThetaChar c 0 z Ω`. -/
private lemma riemannThetaChar_binary_eq_exp_mul (c : ι → ℝ) (b : ι → Fin 2) (z : ι → ℂ)
    (Ω : Matrix ι ι ℂ) :
    riemannThetaChar c (fun i => ((b i : ℕ) : ℝ)) z Ω =
      cexp (2 * π * I * ((fun i => (c i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) *
        riemannThetaChar c 0 z Ω := by
  have h := riemannThetaChar_add_int c 0 z Ω 0 (fun i => ((b i : ℕ) : ℤ))
  have e1 : (c + fun i => (((0 : ι → ℤ) i : ℤ) : ℝ)) = c := by funext i; simp
  have e2 : ((0 : ι → ℝ) + fun i => ((((b i : ℕ) : ℤ)) : ℝ)) = fun i => ((b i : ℕ) : ℝ) := by
    funext i; simp
  rw [e1, e2] at h
  rw [h]
  congr 3

/-- Identity under the stated parameter and domain assumptions:
`riemannThetaChar (halfBinaryVector a) (halfBinaryVector b) x Ω * riemannThetaChar (halfBinaryVector
a) (halfBinaryVector b) y Ω = ∑ ν : ι → Fin 2, cexp (2 * π * I * ((fun i => (halfBinarySum a ν i :
ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) * (riemannThetaChar (halfBinarySum a ν) 0 (x + y) (2 • Ω) *
riemannThetaChar (halfBinaryVector ν) 0 (x
- y) (2 • Ω))`. -/
private lemma riemannThetaChar_half_mul_eq_sum [DecidableEq ι] {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι)
    (a b : ι → Fin 2) (x y : ι → ℂ) :
    riemannThetaChar (halfBinaryVector a) (halfBinaryVector b) x Ω *
        riemannThetaChar (halfBinaryVector a) (halfBinaryVector b) y Ω =
      ∑ ν : ι → Fin 2,
        cexp (2 * π * I * ((fun i => (halfBinarySum a ν i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) *
          (riemannThetaChar (halfBinarySum a ν) 0 (x + y) (2 • Ω) *
            riemannThetaChar (halfBinaryVector ν) 0 (x - y) (2 • Ω)) := by
  rw [riemannThetaChar_mul_addition hΩ]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have h1 : (1 / 2 : ℝ) • (halfBinaryVector a + halfBinaryVector a + fun i => ((ν i : ℕ) : ℝ)) =
      halfBinarySum a ν := by
    funext i; simp [halfBinaryVector, halfBinarySum]; ring
  have h2 : (1 / 2 : ℝ) • (halfBinaryVector a - halfBinaryVector a + fun i => ((ν i : ℕ) : ℝ)) =
      halfBinaryVector ν := by
    funext i; simp [halfBinaryVector]; ring
  have h3 : halfBinaryVector b + halfBinaryVector b = fun i => ((b i : ℕ) : ℝ) := by
    funext i; simp [halfBinaryVector]
  rw [h1, h2, h3, sub_self, riemannThetaChar_binary_eq_exp_mul, mul_assoc]

/-- Identity under the stated parameter and domain assumptions: `∑ b : ι → Fin 2, cexp (2 * π * I
* ((fun i => (halfBinarySum a ν i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) * cexp (2 * π * I *
((fun i => (halfBinarySum a μ i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) = if ν = μ then (2 : ℂ) ^
Fintype.card ι else 0`. -/
private lemma sum_exp_halfBinarySum_mul_exp [DecidableEq ι] (a ν μ : ι → Fin 2) :
    ∑ b : ι → Fin 2,
      cexp (2 * π * I * ((fun i => (halfBinarySum a ν i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) *
        cexp (2 * π * I * ((fun i => (halfBinarySum a μ i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) =
      if ν = μ then (2 : ℂ) ^ Fintype.card ι else 0 := by
  have hfac : ∀ b : ι → Fin 2,
      cexp (2 * π * I * ((fun i => (halfBinarySum a ν i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) *
        cexp (2 * π * I * ((fun i => (halfBinarySum a μ i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) =
      ∏ i, cexp (π * I * ((((a i : ℕ) + (a i : ℕ) + (ν i : ℕ) + (μ i : ℕ) : ℕ) : ℂ) *
        ((b i : ℕ) : ℂ))) := by
    intro b
    rw [← Complex.exp_add, ← Complex.exp_sum]
    congr 1
    simp only [dotProduct, halfBinarySum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [Finset.sum_congr rfl fun b _ => hfac b]
  rw [show (Finset.univ : Finset (ι → Fin 2)) = Fintype.piFinset fun _ => Finset.univ from
    Fintype.piFinset_univ.symm, ← Finset.prod_univ_sum (fun _ => Finset.univ)
      (fun i (t : Fin 2) => cexp (π * I * ((((a i : ℕ) + (a i : ℕ) + (ν i : ℕ) + (μ i : ℕ) :
        ℕ) : ℂ) * ((t : ℕ) : ℂ))))]
  have hone : ∀ i, ∑ t : Fin 2, cexp (π * I * ((((a i : ℕ) + (a i : ℕ) + (ν i : ℕ) + (μ i : ℕ) :
      ℕ) : ℂ) * ((t : ℕ) : ℂ))) = if ν i = μ i then 2 else 0 := by
    intro i
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, Complex.exp_zero, Fin.val_one,
      Nat.cast_one, mul_one]
    have hν := (ν i).2
    have hμ := (μ i).2
    by_cases h : ν i = μ i
    · rw [h]
      simp only [ite_true]
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (a i : ℕ) + (a i : ℕ) + (μ i : ℕ) + (μ i : ℕ) = 2 * k :=
        ⟨(a i : ℕ) + (μ i : ℕ), by ring⟩
      rw [hk, show π * I * (((2 * k : ℕ) : ℂ)) = 2 * π * I * ((k : ℤ) : ℂ) by push_cast; ring,
        exp_two_pi_I_intCast]
      norm_num
    · simp only [h, ite_false]
      have hne : (ν i : ℕ) ≠ (μ i : ℕ) := fun h' => h (Fin.ext h')
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (a i : ℕ) + (a i : ℕ) + (ν i : ℕ) + (μ i : ℕ) = 2 * k + 1 :=
        ⟨(a i : ℕ), by omega⟩
      rw [hk, show π * I * (((2 * k + 1 : ℕ) : ℂ)) = 2 * π * I * ((k : ℤ) : ℂ) + π * I by
        push_cast; ring, Complex.exp_add, exp_two_pi_I_intCast, Complex.exp_pi_mul_I]
      ring
  simp_rw [hone]
  by_cases h : ν = μ
  · subst h; simp
  · simp only [h, ite_false]
    obtain ⟨i, hi⟩ : ∃ i, ν i ≠ μ i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Identity under the stated parameter and domain assumptions: `∑ a : ι → Fin 2, F (halfBinarySum
a ν) = ∑ a : ι → Fin 2, F (halfBinaryVector a)`. -/
private lemma sum_halfBinarySum_eq_sum_halfBinaryVector [DecidableEq ι] (ν : ι → Fin 2)
    (F : (ι → ℝ) → ℂ)
    (hF : ∀ (c : ι → ℝ) (m : ι → ℕ), F (c + fun i => (m i : ℝ)) = F c) :
    ∑ a : ι → Fin 2, F (halfBinarySum a ν) = ∑ a : ι → Fin 2, F (halfBinaryVector a) := by
  rw [← Equiv.sum_comp (Equiv.addRight ν) (fun a => F (halfBinaryVector a))]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsplit : halfBinarySum a ν =
      halfBinaryVector (a + ν) + fun i => ((((a i : ℕ) + (ν i : ℕ)) / 2 : ℕ) : ℝ) := by
    funext i
    simp only [halfBinarySum, halfBinaryVector, Pi.add_apply, Fin.val_add]
    have := Nat.mod_add_div ((a i : ℕ) + (ν i : ℕ)) 2
    have h2 : (((a i : ℕ) + (ν i : ℕ) : ℕ) : ℝ) =
        ((((a i : ℕ) + (ν i : ℕ)) % 2 : ℕ) : ℝ) + 2 * ((((a i : ℕ) + (ν i : ℕ)) / 2 : ℕ) : ℝ) := by
      exact_mod_cast this.symm
    rw [h2]
    ring
  rw [hsplit, hF, Equiv.coe_addRight]

/-- Identity under the stated parameter and domain assumptions: `∑ b : ι → Fin 2, (∑ ν, e ν b * U
ν) * (∑ μ, e μ b * V μ) = ∑ ν, K * (U ν * V ν)`. -/
private lemma sum_mul_sum_of_orthogonal [DecidableEq ι] {K : ℂ} (e : (ι → Fin 2) → (ι → Fin 2) → ℂ)
    (U V : (ι → Fin 2) → ℂ)
    (hchar : ∀ ν μ, ∑ b : ι → Fin 2, e ν b * e μ b = if ν = μ then K else 0) :
    ∑ b : ι → Fin 2, (∑ ν, e ν b * U ν) * (∑ μ, e μ b * V μ) = ∑ ν, K * (U ν * V ν) := by
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]
  have : ∀ μ, ∑ b : ι → Fin 2, e ν b * U ν * (e μ b * V μ) =
      (if ν = μ then K else 0) * (U ν * V μ) := by
    intro μ
    rw [← hchar ν μ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp_rw [this, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The four-theta summand transforms under the binary half-characteristic shift by the displayed
quadratic phase factor. -/
private lemma exp_mul_riemannTheta_four_shift {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω) (a b : ι → Fin 2)
    (x y u v : ι → ℂ) :
    cexp (2 * π * I * (2 * ((fun i => (halfBinaryVector a i : ℂ)) ⬝ᵥ
          (Ω *ᵥ fun i => (halfBinaryVector a i : ℂ))) +
          (fun i => (halfBinaryVector a i : ℂ)) ⬝ᵥ (x + y + u + v))) *
        riemannTheta (x + (Ω *ᵥ fun i => (halfBinaryVector a i : ℂ)) + fun i =>
            (halfBinaryVector b i : ℂ)) Ω *
        riemannTheta (y + (Ω *ᵥ fun i => (halfBinaryVector a i : ℂ)) + fun i =>
            (halfBinaryVector b i : ℂ)) Ω *
        riemannTheta (u + (Ω *ᵥ fun i => (halfBinaryVector a i : ℂ)) + fun i =>
            (halfBinaryVector b i : ℂ)) Ω *
        riemannTheta (v + (Ω *ᵥ fun i => (halfBinaryVector a i : ℂ)) + fun i =>
            (halfBinaryVector b i : ℂ)) Ω =
      (riemannThetaChar (halfBinaryVector a) (halfBinaryVector b) x Ω *
          riemannThetaChar (halfBinaryVector a) (halfBinaryVector b) y Ω) *
        (riemannThetaChar (halfBinaryVector a) (halfBinaryVector b) u Ω *
          riemannThetaChar (halfBinaryVector a) (halfBinaryVector b) v Ω) := by
  simp only [riemannThetaChar_eq _ _ _ hΩ]
  set A : ι → ℂ := fun i => (halfBinaryVector a i : ℂ)
  set B : ι → ℂ := fun i => (halfBinaryVector b i : ℂ)
  have hab : 4 * (A ⬝ᵥ B) = ((∑ i, ((a i : ℕ) * (b i : ℕ) : ℕ) : ℤ) : ℂ) := by
    simp only [A, B, halfBinaryVector, dotProduct, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have key : 2 * π * I * (2 * (A ⬝ᵥ (Ω *ᵥ A)) + A ⬝ᵥ (x + y + u + v)) =
      (2 * π * I * ((1 / 2 : ℂ) * (A ⬝ᵥ (Ω *ᵥ A)) + A ⬝ᵥ (x + B)) +
        2 * π * I * ((1 / 2 : ℂ) * (A ⬝ᵥ (Ω *ᵥ A)) + A ⬝ᵥ (y + B)) +
        2 * π * I * ((1 / 2 : ℂ) * (A ⬝ᵥ (Ω *ᵥ A)) + A ⬝ᵥ (u + B)) +
        2 * π * I * ((1 / 2 : ℂ) * (A ⬝ᵥ (Ω *ᵥ A)) + A ⬝ᵥ (v + B))) +
      2 * π * I * ((-(∑ i, ((a i : ℕ) * (b i : ℕ) : ℕ) : ℤ) : ℤ) : ℂ) := by
    push_cast at hab ⊢
    rw [← hab]
    simp only [dotProduct_add]
    ring
  rw [key, Complex.exp_add, exp_two_pi_I_intCast, mul_one, Complex.exp_add, Complex.exp_add,
    Complex.exp_add]
  ring

/-- DLMF 21.6.6: with `α, β` running over `½ℤ^g/ℤ^g` (representatives `a/2`, `a ∈ {0,1}^g`),
`θ((x+y+u+v)/2)θ((x+y-u-v)/2)θ((x-y+u-v)/2)θ((x-y-u+v)/2)
  = 2^{-g} ∑_{α,β} exp(2πi(2α·Ω·α + α·[x+y+u+v])) θ(x+Ωα+β)θ(y+Ωα+β)θ(u+Ωα+β)θ(v+Ωα+β)`. -/
@[dlmf 21.6.E6]
theorem riemannTheta_four_product [DecidableEq ι] {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι)
    (x y u v : ι → ℂ) :
    riemannTheta ((1 / 2 : ℂ) • (x + y + u + v)) Ω *
      riemannTheta ((1 / 2 : ℂ) • (x + y - u - v)) Ω *
        riemannTheta ((1 / 2 : ℂ) • (x - y + u - v)) Ω *
        riemannTheta ((1 / 2 : ℂ) • (x - y - u + v)) Ω =
      ((2 : ℂ) ^ Fintype.card ι)⁻¹ * ∑ a : ι → Fin 2, ∑ b : ι → Fin 2,
        cexp (2 * π * I * (2 * ((fun i => (halfBinaryVector a i : ℂ)) ⬝ᵥ
          (Ω *ᵥ fun i => (halfBinaryVector a i : ℂ))) +
          (fun i => (halfBinaryVector a i : ℂ)) ⬝ᵥ (x + y + u + v))) *
        riemannTheta (x + (Ω *ᵥ fun i => (halfBinaryVector a i : ℂ)) + fun i =>
            (halfBinaryVector b i : ℂ)) Ω *
        riemannTheta (y + (Ω *ᵥ fun i => (halfBinaryVector a i : ℂ)) + fun i =>
            (halfBinaryVector b i : ℂ)) Ω *
        riemannTheta (u + (Ω *ᵥ fun i => (halfBinaryVector a i : ℂ)) + fun i =>
            (halfBinaryVector b i : ℂ)) Ω *
        riemannTheta (v + (Ω *ᵥ fun i => (halfBinaryVector a i : ℂ)) +
          fun i => (halfBinaryVector b i : ℂ)) Ω := by
  rw [mul_assoc (riemannTheta _ Ω * riemannTheta _ Ω), riemannTheta_mul_riemannTheta_eq_sum hΩ,
      riemannTheta_mul_riemannTheta_eq_sum hΩ]
  have hw1 : (1 / 2 : ℂ) • (x + y + u + v) + (1 / 2 : ℂ) • (x + y - u - v) = x + y := by
    funext i; simp; ring
  have hw2 : (1 / 2 : ℂ) • (x + y + u + v) - (1 / 2 : ℂ) • (x + y - u - v) = u + v := by
    funext i; simp; ring
  have hw3 : (1 / 2 : ℂ) • (x - y + u - v) + (1 / 2 : ℂ) • (x - y - u + v) = x - y := by
    funext i; simp; ring
  have hw4 : (1 / 2 : ℂ) • (x - y + u - v) - (1 / 2 : ℂ) • (x - y - u + v) = u - v := by
    funext i; simp; ring
  rw [hw1, hw2, hw3, hw4, Finset.sum_mul_sum]
  symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    exp_mul_riemannTheta_four_shift hΩ.1 a b x y u v]
  simp_rw [riemannThetaChar_half_mul_eq_sum hΩ]
  rw [Finset.sum_congr rfl fun a _ => sum_mul_sum_of_orthogonal
    (fun ν b => cexp (2 * π * I * ((fun i => (halfBinarySum a ν i : ℂ)) ⬝ᵥ
      fun i => ((b i : ℕ) : ℂ)))) _ _ (sum_exp_halfBinarySum_mul_exp a)]
  conv_lhs => simp only [← Finset.mul_sum]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hF := sum_halfBinarySum_eq_sum_halfBinaryVector ν
      (fun c => riemannThetaChar c 0 (x + y) (2 • Ω) *
    riemannThetaChar c 0 (u + v) (2 • Ω)) (fun c m => by
      simp only [riemannThetaChar_add_natCast_zero])
  calc ∑ a : ι → Fin 2, riemannThetaChar (halfBinarySum a ν) 0 (x + y) (2 • Ω) *
        riemannThetaChar (halfBinaryVector ν) 0 (x - y) (2 • Ω) *
          (riemannThetaChar (halfBinarySum a ν) 0 (u + v) (2 • Ω) *
            riemannThetaChar (halfBinaryVector ν) 0 (u - v) (2 • Ω))
      = (∑ a : ι → Fin 2, riemannThetaChar (halfBinarySum a ν) 0 (x + y) (2 • Ω) *
          riemannThetaChar (halfBinarySum a ν) 0 (u + v) (2 • Ω)) *
          (riemannThetaChar (halfBinaryVector ν) 0 (x - y) (2 • Ω) *
            riemannThetaChar (halfBinaryVector ν) 0 (u - v) (2 • Ω)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = (∑ a : ι → Fin 2, riemannThetaChar (halfBinaryVector a) 0 (x + y) (2 • Ω) *
          riemannThetaChar (halfBinaryVector a) 0 (u + v) (2 • Ω)) *
          (riemannThetaChar (halfBinaryVector ν) 0 (x - y) (2 • Ω) *
            riemannThetaChar (halfBinaryVector ν) 0 (u - v) (2 • Ω)) := by rw [hF]
    _ = _ := by rw [Finset.sum_mul]

/-! ## Proof of 21.6.7 from the addition formula -/

/-- Identity under the stated parameter and domain assumptions: `riemannThetaChar (c + fun i => (m
i : ℝ)) q z Ω = riemannThetaChar c q z Ω`. -/
private lemma riemannThetaChar_add_natCast (c q : ι → ℝ) (m : ι → ℕ) (z : ι → ℂ)
    (Ω : Matrix ι ι ℂ) :
    riemannThetaChar (c + fun i => (m i : ℝ)) q z Ω = riemannThetaChar c q z Ω := by
  have h := riemannThetaChar_add_int c q z Ω (fun i => (m i : ℤ)) 0
  have e1 : (c + fun i => (((m i : ℤ) : ℝ))) = c + fun i => (m i : ℝ) := by
    funext i; simp
  have e2 : (q + fun i => (((0 : ι → ℤ) i : ℤ) : ℝ)) = q := by
    funext i; simp
  rw [e1, e2] at h
  rw [h]
  simp [dotProduct]

/-- Identity under the stated parameter and domain assumptions: `riemannThetaChar c (q + fun i =>
((b i : ℕ) : ℝ)) z Ω = cexp (2 * π * I * ((fun i => (c i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) *
riemannThetaChar c q z Ω`. -/
private lemma riemannThetaChar_add_binary_eq_exp_mul (c q : ι → ℝ) (b : ι → Fin 2) (z : ι → ℂ)
    (Ω : Matrix ι ι ℂ) :
    riemannThetaChar c (q + fun i => ((b i : ℕ) : ℝ)) z Ω =
      cexp (2 * π * I * ((fun i => (c i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) *
        riemannThetaChar c q z Ω := by
  have h := riemannThetaChar_add_int c q z Ω 0 (fun i => ((b i : ℕ) : ℤ))
  have e1 : (c + fun i => (((0 : ι → ℤ) i : ℤ) : ℝ)) = c := by funext i; simp
  have e2 : (q + fun i => ((((b i : ℕ) : ℤ)) : ℝ)) = q + fun i => ((b i : ℕ) : ℝ) := by
    funext i; simp
  rw [e1, e2] at h
  rw [h]
  congr 3

/-- The product of two theta functions with half-characteristics is the finite sum of
doubled-period theta products with the indicated shifted characteristics. -/
private lemma riemannThetaChar_shift_half_mul_eq_sum [DecidableEq ι] {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι)
    (c₁ c₂ d₁ d₂ : ι → ℝ) (a b : ι → Fin 2) (x y : ι → ℂ) :
    riemannThetaChar (c₁ + halfBinaryVector a) (d₁ + halfBinaryVector b) x Ω *
        riemannThetaChar (c₂ + halfBinaryVector a) (d₂ + halfBinaryVector b) y Ω =
      ∑ ν : ι → Fin 2,
        cexp (2 * π * I * ((fun i => (((1 / 2 : ℝ) • (c₁ + c₂) + halfBinarySum a ν) i : ℂ)) ⬝ᵥ
          fun i => ((b i : ℕ) : ℂ))) *
          (riemannThetaChar ((1 / 2 : ℝ) • (c₁ + c₂) + halfBinarySum a ν) (d₁ + d₂) (x + y)
            (2 • Ω) *
            riemannThetaChar ((1 / 2 : ℝ) • (c₁ - c₂) + halfBinaryVector ν) (d₁ - d₂) (x - y)
              (2 • Ω)) := by
  rw [riemannThetaChar_mul_addition hΩ]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have h1 : (1 / 2 : ℝ) •
      (c₁ + halfBinaryVector a + (c₂ + halfBinaryVector a) + fun i => ((ν i : ℕ) : ℝ)) =
      (1 / 2 : ℝ) • (c₁ + c₂) + halfBinarySum a ν := by
    funext i; simp [halfBinaryVector, halfBinarySum]; ring
  have h2 : (1 / 2 : ℝ) •
      (c₁ + halfBinaryVector a - (c₂ + halfBinaryVector a) + fun i => ((ν i : ℕ) : ℝ)) =
      (1 / 2 : ℝ) • (c₁ - c₂) + halfBinaryVector ν := by
    funext i; simp [halfBinaryVector]; ring
  have h3 : d₁ + halfBinaryVector b + (d₂ + halfBinaryVector b) = (d₁ + d₂) + fun i =>
      ((b i : ℕ) : ℝ) := by
    funext i; simp [halfBinaryVector]; ring
  have h4 : d₁ + halfBinaryVector b - (d₂ + halfBinaryVector b) = d₁ - d₂ := by
    funext i; simp
  rw [h1, h2, h3, h4, riemannThetaChar_add_binary_eq_exp_mul, mul_assoc]

/-- Identity under the stated parameter and domain assumptions: `∑ b : ι → Fin 2, k b * ((∑ ν, e ν
b * U ν) * (∑ μ, e' μ b * V μ)) = ∑ ν, K * (U ν * V ν)`. -/
private lemma sum_weighted_mul_sum_of_orthogonal [DecidableEq ι] {K : ℂ} (k : (ι → Fin 2) → ℂ)
    (e e' : (ι → Fin 2) → (ι → Fin 2) → ℂ) (U V : (ι → Fin 2) → ℂ)
    (hchar : ∀ ν μ, ∑ b : ι → Fin 2, k b * e ν b * e' μ b = if ν = μ then K else 0) :
    ∑ b : ι → Fin 2, k b * ((∑ ν, e ν b * U ν) * (∑ μ, e' μ b * V μ)) =
      ∑ ν, K * (U ν * V ν) := by
  simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]
  have : ∀ μ, ∑ b : ι → Fin 2, k b * (e ν b * U ν * (e' μ b * V μ)) =
      (if ν = μ then K else 0) * (U ν * V μ) := by
    intro μ
    rw [← hchar ν μ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp_rw [this, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Identity under the stated parameter and domain assumptions: `∑ b : ι → Fin 2, cexp (-2 * π * I
* ((fun i => (halfBinaryVector b i : ℂ)) ⬝ᵥ fun i => ((s₁ + s₂) i : ℂ))) * cexp (2 * π * I * ((fun i
=> (((1 / 2 : ℝ) • s₁ + halfBinarySum a ν) i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) * cexp (2 * π
* I * ((fun i => (((1 / 2 : ℝ) • s₂ + halfBinarySum a μ) i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ)))
= if ν = μ then (2 : ℂ) ^ Fintype.card ι else 0`. -/
private lemma sum_exp_halfBinaryVector_mul_exp_mul_exp [DecidableEq ι] (a ν μ : ι → Fin 2)
    (s₁ s₂ : ι → ℝ) :
    ∑ b : ι → Fin 2,
      cexp (-2 * π * I * ((fun i => (halfBinaryVector b i : ℂ)) ⬝ᵥ fun i => ((s₁ + s₂) i : ℂ))) *
        cexp (2 * π * I * ((fun i => (((1 / 2 : ℝ) • s₁ + halfBinarySum a ν) i : ℂ)) ⬝ᵥ
          fun i => ((b i : ℕ) : ℂ))) *
        cexp (2 * π * I * ((fun i => (((1 / 2 : ℝ) • s₂ + halfBinarySum a μ) i : ℂ)) ⬝ᵥ
          fun i => ((b i : ℕ) : ℂ))) =
      if ν = μ then (2 : ℂ) ^ Fintype.card ι else 0 := by
  rw [← sum_exp_halfBinarySum_mul_exp a ν μ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [dotProduct, halfBinaryVector, halfBinarySum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- DLMF 21.6.7, the characteristic form of 21.6.6, for real characteristic vectors
`c₁, …, c₄, d₁, …, d₄ ∈ ℝ^g`. -/
@[dlmf 21.6.E7]
theorem riemannThetaChar_four_product [DecidableEq ι] {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι)
    (x y u v : ι → ℂ) (c₁ c₂ c₃ c₄ d₁ d₂ d₃ d₄ : ι → ℝ) :
    riemannThetaChar ((1 / 2 : ℝ) • (c₁ + c₂ + c₃ + c₄)) ((1 / 2 : ℝ) • (d₁ + d₂ + d₃ + d₄))
          ((1 / 2 : ℂ) • (x + y + u + v)) Ω *
        riemannThetaChar ((1 / 2 : ℝ) • (c₁ + c₂ - c₃ - c₄)) ((1 / 2 : ℝ) • (d₁ + d₂ - d₃ - d₄))
          ((1 / 2 : ℂ) • (x + y - u - v)) Ω *
        riemannThetaChar ((1 / 2 : ℝ) • (c₁ - c₂ + c₃ - c₄)) ((1 / 2 : ℝ) • (d₁ - d₂ + d₃ - d₄))
          ((1 / 2 : ℂ) • (x - y + u - v)) Ω *
        riemannThetaChar ((1 / 2 : ℝ) • (c₁ - c₂ - c₃ + c₄)) ((1 / 2 : ℝ) • (d₁ - d₂ - d₃ + d₄))
          ((1 / 2 : ℂ) • (x - y - u + v)) Ω =
      ((2 : ℂ) ^ Fintype.card ι)⁻¹ * ∑ a : ι → Fin 2, ∑ b : ι → Fin 2,
        cexp (-2 * π * I * ((fun i => (halfBinaryVector b i : ℂ)) ⬝ᵥ
          fun i => ((c₁ + c₂ + c₃ + c₄) i : ℂ))) *
        riemannThetaChar (c₁ + halfBinaryVector a) (d₁ + halfBinaryVector b) x Ω *
        riemannThetaChar (c₂ + halfBinaryVector a) (d₂ + halfBinaryVector b) y Ω *
        riemannThetaChar (c₃ + halfBinaryVector a) (d₃ + halfBinaryVector b) u Ω *
        riemannThetaChar (c₄ + halfBinaryVector a) (d₄ + halfBinaryVector b) v Ω := by
  rw [mul_assoc (riemannThetaChar _ _ _ Ω * riemannThetaChar _ _ _ Ω)]
  rw [riemannThetaChar_mul_addition hΩ, riemannThetaChar_mul_addition hΩ]
  have hw1 : (1 / 2 : ℂ) • (x + y + u + v) + (1 / 2 : ℂ) • (x + y - u - v) = x + y := by
    funext i; simp; ring
  have hw2 : (1 / 2 : ℂ) • (x + y + u + v) - (1 / 2 : ℂ) • (x + y - u - v) = u + v := by
    funext i; simp; ring
  have hw3 : (1 / 2 : ℂ) • (x - y + u - v) + (1 / 2 : ℂ) • (x - y - u + v) = x - y := by
    funext i; simp; ring
  have hw4 : (1 / 2 : ℂ) • (x - y + u - v) - (1 / 2 : ℂ) • (x - y - u + v) = u - v := by
    funext i; simp; ring
  have hA : ∀ ν : ι → Fin 2, (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (c₁ + c₂ + c₃ + c₄) +
      (1 / 2 : ℝ) • (c₁ + c₂ - c₃ - c₄) + fun i => ((ν i : ℕ) : ℝ)) =
      (1 / 2 : ℝ) • (c₁ + c₂) + halfBinaryVector ν := by
    intro ν; funext i; simp [halfBinaryVector]; ring
  have hB : ∀ ν : ι → Fin 2, (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (c₁ + c₂ + c₃ + c₄) -
      (1 / 2 : ℝ) • (c₁ + c₂ - c₃ - c₄) + fun i => ((ν i : ℕ) : ℝ)) =
      (1 / 2 : ℝ) • (c₃ + c₄) + halfBinaryVector ν := by
    intro ν; funext i; simp [halfBinaryVector]; ring
  have hC : ∀ ν : ι → Fin 2, (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (c₁ - c₂ + c₃ - c₄) +
      (1 / 2 : ℝ) • (c₁ - c₂ - c₃ + c₄) + fun i => ((ν i : ℕ) : ℝ)) =
      (1 / 2 : ℝ) • (c₁ - c₂) + halfBinaryVector ν := by
    intro ν; funext i; simp [halfBinaryVector]; ring
  have hD : ∀ ν : ι → Fin 2, (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (c₁ - c₂ + c₃ - c₄) -
      (1 / 2 : ℝ) • (c₁ - c₂ - c₃ + c₄) + fun i => ((ν i : ℕ) : ℝ)) =
      (1 / 2 : ℝ) • (c₃ - c₄) + halfBinaryVector ν := by
    intro ν; funext i; simp [halfBinaryVector]; ring
  have hd1 : (1 / 2 : ℝ) • (d₁ + d₂ + d₃ + d₄) + (1 / 2 : ℝ) • (d₁ + d₂ - d₃ - d₄) = d₁ + d₂ := by
    funext i; simp; ring
  have hd2 : (1 / 2 : ℝ) • (d₁ + d₂ + d₃ + d₄) - (1 / 2 : ℝ) • (d₁ + d₂ - d₃ - d₄) = d₃ + d₄ := by
    funext i; simp; ring
  have hd3 : (1 / 2 : ℝ) • (d₁ - d₂ + d₃ - d₄) + (1 / 2 : ℝ) • (d₁ - d₂ - d₃ + d₄) = d₁ - d₂ := by
    funext i; simp; ring
  have hd4 : (1 / 2 : ℝ) • (d₁ - d₂ + d₃ - d₄) - (1 / 2 : ℝ) • (d₁ - d₂ - d₃ + d₄) = d₃ - d₄ := by
    funext i; simp; ring
  simp only [hA, hB, hC, hD, hd1, hd2, hd3, hd4, hw1, hw2, hw3, hw4]
  rw [Finset.sum_mul_sum]
  symm
  have hsummand : ∀ a b : ι → Fin 2,
      cexp (-2 * π * I * ((fun i => (halfBinaryVector b i : ℂ)) ⬝ᵥ
          fun i => ((c₁ + c₂ + c₃ + c₄) i : ℂ))) *
        riemannThetaChar (c₁ + halfBinaryVector a) (d₁ + halfBinaryVector b) x Ω *
        riemannThetaChar (c₂ + halfBinaryVector a) (d₂ + halfBinaryVector b) y Ω *
        riemannThetaChar (c₃ + halfBinaryVector a) (d₃ + halfBinaryVector b) u Ω *
        riemannThetaChar (c₄ + halfBinaryVector a) (d₄ + halfBinaryVector b) v Ω =
      cexp (-2 * π * I * ((fun i => (halfBinaryVector b i : ℂ)) ⬝ᵥ
          fun i => (((c₁ + c₂) + (c₃ + c₄)) i : ℂ))) *
        ((riemannThetaChar (c₁ + halfBinaryVector a) (d₁ + halfBinaryVector b) x Ω *
          riemannThetaChar (c₂ + halfBinaryVector a) (d₂ + halfBinaryVector b) y Ω) *
        (riemannThetaChar (c₃ + halfBinaryVector a) (d₃ + halfBinaryVector b) u Ω *
          riemannThetaChar (c₄ + halfBinaryVector a) (d₄ + halfBinaryVector b) v Ω)) := by
    intro a b
    have : c₁ + c₂ + c₃ + c₄ = (c₁ + c₂) + (c₃ + c₄) := by abel
    rw [this]
    ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsummand a b]
  simp_rw [riemannThetaChar_shift_half_mul_eq_sum hΩ]
  rw [Finset.mul_sum]
  have hcol : ∀ a : ι → Fin 2, ∑ b : ι → Fin 2,
      cexp (-2 * π * I * ((fun i => (halfBinaryVector b i : ℂ)) ⬝ᵥ
        fun i => (((c₁ + c₂) + (c₃ + c₄)) i : ℂ))) *
      ((∑ ν, cexp (2 * π * I * ((fun i => (((1 / 2 : ℝ) • (c₁ + c₂) +
          halfBinarySum a ν) i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) *
        (riemannThetaChar ((1 / 2 : ℝ) • (c₁ + c₂) + halfBinarySum a ν) (d₁ + d₂) (x + y) (2 • Ω) *
          riemannThetaChar ((1 / 2 : ℝ) • (c₁ - c₂) + halfBinaryVector ν) (d₁ - d₂)
              (x - y) (2 • Ω))) *
       (∑ μ, cexp (2 * π * I * ((fun i => (((1 / 2 : ℝ) • (c₃ + c₄) +
          halfBinarySum a μ) i : ℂ)) ⬝ᵥ fun i => ((b i : ℕ) : ℂ))) *
        (riemannThetaChar ((1 / 2 : ℝ) • (c₃ + c₄) + halfBinarySum a μ) (d₃ + d₄) (u + v) (2 • Ω) *
          riemannThetaChar ((1 / 2 : ℝ) • (c₃ - c₄) + halfBinaryVector μ) (d₃ - d₄)
              (u - v) (2 • Ω)))) =
      ∑ ν, (2 : ℂ) ^ Fintype.card ι *
        ((riemannThetaChar ((1 / 2 : ℝ) • (c₁ + c₂) + halfBinarySum a ν) (d₁ + d₂) (x + y) (2 • Ω) *
          riemannThetaChar ((1 / 2 : ℝ) • (c₁ - c₂) + halfBinaryVector ν) (d₁ - d₂)
              (x - y) (2 • Ω)) *
         (riemannThetaChar ((1 / 2 : ℝ) • (c₃ + c₄) + halfBinarySum a ν) (d₃ + d₄) (u + v) (2 • Ω) *
          riemannThetaChar ((1 / 2 : ℝ) • (c₃ - c₄) + halfBinaryVector ν) (d₃ - d₄)
              (u - v) (2 • Ω))) :=
    fun a => sum_weighted_mul_sum_of_orthogonal _ _ _ _ _
      (fun ν μ => sum_exp_halfBinaryVector_mul_exp_mul_exp a ν μ (c₁ + c₂) (c₃ + c₄))
  simp only [hcol]
  conv_lhs => simp only [← Finset.mul_sum]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hF := sum_halfBinarySum_eq_sum_halfBinaryVector ν (fun c =>
    riemannThetaChar ((1 / 2 : ℝ) • (c₁ + c₂) + c) (d₁ + d₂) (x + y) (2 • Ω) *
      riemannThetaChar ((1 / 2 : ℝ) • (c₃ + c₄) + c) (d₃ + d₄) (u + v) (2 • Ω))
    (fun c m => by simp only [← add_assoc, riemannThetaChar_add_natCast])
  rw [← Finset.sum_mul, ← hF, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

end DLMF.RiemannTheta
