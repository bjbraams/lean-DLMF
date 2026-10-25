/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Basic

/-!
# Symmetry and quasi-periodicity of Riemann theta functions (DLMF §21.3)

Parity, periodicity and quasi-periodicity of `θ(z|Ω)` (DLMF 21.3.1–21.3.3), the
characteristic shifts and quasi-periodicity of `θ[α;β](z|Ω)` (DLMF 21.3.4–21.3.5), and the
parity of theta functions with half-period characteristics (DLMF 21.3.6).

All identities are proved by reindexing the lattice sum with an equivalence of `ℤ^g`; this
needs no summability, so they hold for every matrix `Ω` (symmetry `Ωᵀ = Ω` is assumed where the
quadratic form is shifted). The parity 21.3.6 is proved in the stronger form
`θ[a/2; b/2](-z|Ω) = (-1)^{a·b} θ[a/2; b/2](z|Ω)` for all integer vectors `a, b`; DLMF states
it for half-period characteristics `aᵢ, bᵢ ∈ {0, 1}`.
-/

@[expose] public noncomputable section

open Complex Matrix Finset
open scoped Real

namespace DLMF.RiemannTheta

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma rth21_cast_neg (n : ι → ℤ) :
    (fun i => (((-n) i : ℤ) : ℂ)) = -fun i => (n i : ℂ) := by
  funext i; simp

omit [Fintype ι] in
lemma rth21_cast_sub (n m : ι → ℤ) :
    (fun i => (((n - m) i : ℤ) : ℂ)) = (fun i => (n i : ℂ)) - fun i => (m i : ℂ) := by
  funext i; simp

lemma rth21_intDot (n m : ι → ℤ) :
    (fun i => (n i : ℂ)) ⬝ᵥ (fun i => (m i : ℂ)) = ((n ⬝ᵥ m : ℤ) : ℂ) := by
  simp [dotProduct]

lemma rth21_exp_int (k : ℤ) : cexp (2 * π * I * k) = 1 := by
  rw [show 2 * π * I * (k : ℂ) = k * (2 * π * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- `θ(-z|Ω) = θ(z|Ω)` (DLMF 21.3.1). -/
@[dlmf 21.3.E1]
theorem riemannTheta_neg (z : ι → ℂ) (Ω : Matrix ι ι ℂ) :
    riemannTheta (-z) Ω = riemannTheta z Ω := by
  rw [riemannTheta, ← (Equiv.neg (ι → ℤ)).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply, riemannThetaTerm, rth21_cast_neg, mulVec_neg, neg_dotProduct,
    dotProduct_neg, neg_neg]

/-- `θ(z + m₁|Ω) = θ(z|Ω)` for `m₁ ∈ ℤ^g` (DLMF 21.3.2). -/
@[dlmf 21.3.E2]
theorem riemannTheta_add_int (z : ι → ℂ) (Ω : Matrix ι ι ℂ) (m₁ : ι → ℤ) :
    riemannTheta (z + fun i => (m₁ i : ℂ)) Ω = riemannTheta z Ω := by
  rw [riemannTheta, riemannTheta]
  refine tsum_congr fun n => ?_
  rw [riemannThetaTerm, riemannThetaTerm, dotProduct_add, rth21_intDot,
    show ∀ a b : ℂ, 2 * π * I * ((1 / 2 : ℂ) * a + (b + ((n ⬝ᵥ m₁ : ℤ) : ℂ))) =
      2 * π * I * ((1 / 2 : ℂ) * a + b) + 2 * π * I * ((n ⬝ᵥ m₁ : ℤ) : ℂ) by intros; ring,
    Complex.exp_add, rth21_exp_int, mul_one]

/-- Quasi-periodicity `θ(z + m₁ + Ωm₂|Ω) = exp(-2πi(½ m₂·Ω·m₂ + m₂·z)) θ(z|Ω)` for
`m₁, m₂ ∈ ℤ^g` and symmetric `Ω` (DLMF 21.3.3). -/
@[dlmf 21.3.E3]
theorem riemannTheta_add_lattice (z : ι → ℂ) {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω)
    (m₁ m₂ : ι → ℤ) :
    riemannTheta (z + (fun i => (m₁ i : ℂ)) + Ω *ᵥ fun i => (m₂ i : ℂ)) Ω =
      cexp (-2 * π * I * ((1 / 2 : ℂ) * ((fun i => (m₂ i : ℂ)) ⬝ᵥ
        (Ω *ᵥ fun i => (m₂ i : ℂ))) + (fun i => (m₂ i : ℂ)) ⬝ᵥ z)) * riemannTheta z Ω := by
  rw [riemannTheta, riemannTheta, ← (Equiv.subRight m₂).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [Equiv.subRight_apply, riemannThetaTerm, riemannThetaTerm, ← Complex.exp_add,
    rth21_cast_sub]
  set N : ι → ℂ := fun i => (n i : ℂ)
  set M₁ : ι → ℂ := fun i => (m₁ i : ℂ)
  set M₂ : ι → ℂ := fun i => (m₂ i : ℂ)
  have hk : (N - M₂) ⬝ᵥ M₁ = (((n - m₂) ⬝ᵥ m₁ : ℤ) : ℂ) := by
    rw [← rth21_cast_sub, rth21_intDot]
  have hsym := rth21_dot_mulVec_comm hΩ M₂ N
  have key : 2 * π * I * ((1 / 2 : ℂ) * ((N - M₂) ⬝ᵥ (Ω *ᵥ (N - M₂))) +
      (N - M₂) ⬝ᵥ (z + M₁ + Ω *ᵥ M₂)) =
      (-2 * π * I * ((1 / 2 : ℂ) * (M₂ ⬝ᵥ (Ω *ᵥ M₂)) + M₂ ⬝ᵥ z) +
        2 * π * I * ((1 / 2 : ℂ) * (N ⬝ᵥ (Ω *ᵥ N)) + N ⬝ᵥ z)) +
      2 * π * I * (((n - m₂) ⬝ᵥ m₁ : ℤ) : ℂ) := by
    rw [← hk]
    simp only [mulVec_sub, dotProduct_add, dotProduct_sub, sub_dotProduct]
    rw [hsym]
    ring
  rw [key, Complex.exp_add, rth21_exp_int, mul_one]

/-- The period lattice `{m₁ + Ωm₂ : m₁, m₂ ∈ ℤ^g}` of the Riemann theta function
(DLMF §21.3(i)). -/
@[dlmf 21.3.i "the period lattice of the Riemann theta function"]
def riemannThetaPeriodLattice (Ω : Matrix ι ι ℂ) : Set (ι → ℂ) :=
  {w | ∃ m₁ m₂ : ι → ℤ, w = (fun i => (m₁ i : ℂ)) + Ω *ᵥ fun i => (m₂ i : ℂ)}

/-- The quasi-periodicity 21.3.3 determines the Riemann theta function up to a constant factor:
every entire function with the same multipliers is a constant multiple of `θ(·|Ω)`
(DLMF §21.3(i)). -/
@[dlmf 21.3.i "quasi-periodicity determines θ up to a constant factor"]
theorem eq_const_mul_riemannTheta_of_quasiPeriodic {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (hper : ∀ (m₁ m₂ : ι → ℤ) (z : ι → ℂ),
      f (z + (fun i => (m₁ i : ℂ)) + Ω *ᵥ fun i => (m₂ i : ℂ)) =
        cexp (-2 * π * I * ((1 / 2 : ℂ) * ((fun i => (m₂ i : ℂ)) ⬝ᵥ
          (Ω *ᵥ fun i => (m₂ i : ℂ))) + (fun i => (m₂ i : ℂ)) ⬝ᵥ z)) * f z) :
    ∃ c : ℂ, ∀ z, f z = c * riemannTheta z Ω := by
  sorry

/-- Shifting the characteristics by integer vectors:
`θ[α + m₁; β + m₂](z|Ω) = exp(2πi α·m₂) θ[α; β](z|Ω)` (DLMF 21.3.4). -/
@[dlmf 21.3.E4]
theorem riemannThetaChar_add_int (α β : ι → ℝ) (z : ι → ℂ) (Ω : Matrix ι ι ℂ)
    (m₁ m₂ : ι → ℤ) :
    riemannThetaChar (α + fun i => (m₁ i : ℝ)) (β + fun i => (m₂ i : ℝ)) z Ω =
      cexp (2 * π * I * ((fun i => (α i : ℂ)) ⬝ᵥ fun i => (m₂ i : ℂ))) *
        riemannThetaChar α β z Ω := by
  rw [riemannThetaChar, riemannThetaChar, ← (Equiv.subRight m₁).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [Equiv.subRight_apply, riemannThetaCharTerm, riemannThetaCharTerm, ← Complex.exp_add]
  have hv : (fun i => (((n - m₁) i : ℤ) : ℂ) + (((α + fun i => (m₁ i : ℝ)) i : ℝ) : ℂ)) =
      fun i => (n i : ℂ) + (α i : ℂ) := by
    funext i; simp
  have hw : (fun i => z i + (((β + fun i => (m₂ i : ℝ)) i : ℝ) : ℂ)) =
      (fun i => z i + (β i : ℂ)) + fun i => (m₂ i : ℂ) := by
    funext i; simp [add_assoc]
  rw [hv, hw, dotProduct_add]
  have hsplit : (fun i => (n i : ℂ) + (α i : ℂ)) ⬝ᵥ (fun i => (m₂ i : ℂ)) =
      (fun i => (α i : ℂ)) ⬝ᵥ (fun i => (m₂ i : ℂ)) + ((n ⬝ᵥ m₂ : ℤ) : ℂ) := by
    rw [show (fun i => (n i : ℂ) + (α i : ℂ)) = (fun i => (n i : ℂ)) + fun i => (α i : ℂ)
      from rfl, add_dotProduct, rth21_intDot, add_comm]
  rw [hsplit]
  rw [show ∀ a b c d : ℂ, 2 * π * I * ((1 / 2 : ℂ) * a + (b + (c + d))) =
      (2 * π * I * c + 2 * π * I * ((1 / 2 : ℂ) * a + b)) + 2 * π * I * d by intros; ring,
    Complex.exp_add, rth21_exp_int, mul_one]

/-- Quasi-periodicity with characteristics:
`θ[α;β](z + m₁ + Ωm₂|Ω) = exp(2πi(α·m₁ - β·m₂ - ½ m₂·Ω·m₂ - m₂·z)) θ[α;β](z|Ω)`
(DLMF 21.3.5), for symmetric `Ω`. -/
@[dlmf 21.3.E5]
theorem riemannThetaChar_add_lattice (α β : ι → ℝ) (z : ι → ℂ) {Ω : Matrix ι ι ℂ}
    (hΩ : Ωᵀ = Ω) (m₁ m₂ : ι → ℤ) :
    riemannThetaChar α β (z + (fun i => (m₁ i : ℂ)) + Ω *ᵥ fun i => (m₂ i : ℂ)) Ω =
      cexp (2 * π * I * ((fun i => (α i : ℂ)) ⬝ᵥ (fun i => (m₁ i : ℂ)) -
        (fun i => (β i : ℂ)) ⬝ᵥ (fun i => (m₂ i : ℂ)) -
        (1 / 2 : ℂ) * ((fun i => (m₂ i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (m₂ i : ℂ))) -
        (fun i => (m₂ i : ℂ)) ⬝ᵥ z)) * riemannThetaChar α β z Ω := by
  rw [riemannThetaChar, riemannThetaChar, ← (Equiv.subRight m₂).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [Equiv.subRight_apply, riemannThetaCharTerm, riemannThetaCharTerm, ← Complex.exp_add]
  set N : ι → ℂ := fun i => (n i : ℂ)
  set A : ι → ℂ := fun i => (α i : ℂ)
  set B : ι → ℂ := fun i => (β i : ℂ)
  set M₁ : ι → ℂ := fun i => (m₁ i : ℂ)
  set M₂ : ι → ℂ := fun i => (m₂ i : ℂ)
  have hv : (fun i => (((n - m₂) i : ℤ) : ℂ) + (α i : ℂ)) = N - M₂ + A := by
    funext i; simp [N, M₂, A]
  have hv' : (fun i => (n i : ℂ) + (α i : ℂ)) = N + A := rfl
  have hw : (fun i => (z + M₁ + Ω *ᵥ M₂) i + (β i : ℂ)) = z + M₁ + Ω *ᵥ M₂ + B := rfl
  have hw' : (fun i => z i + (β i : ℂ)) = z + B := rfl
  rw [hv, hv', hw, hw']
  have hk : N ⬝ᵥ M₁ - M₂ ⬝ᵥ M₁ = (((n - m₂) ⬝ᵥ m₁ : ℤ) : ℂ) := by
    rw [← rth21_intDot, rth21_cast_sub, sub_dotProduct]
  have key : 2 * π * I * ((1 / 2 : ℂ) * ((N - M₂ + A) ⬝ᵥ (Ω *ᵥ (N - M₂ + A))) +
      (N - M₂ + A) ⬝ᵥ (z + M₁ + Ω *ᵥ M₂ + B)) =
      (2 * π * I * (A ⬝ᵥ M₁ - B ⬝ᵥ M₂ - (1 / 2 : ℂ) * (M₂ ⬝ᵥ (Ω *ᵥ M₂)) - M₂ ⬝ᵥ z) +
        2 * π * I * ((1 / 2 : ℂ) * ((N + A) ⬝ᵥ (Ω *ᵥ (N + A))) + (N + A) ⬝ᵥ (z + B))) +
      2 * π * I * (((n - m₂) ⬝ᵥ m₁ : ℤ) : ℂ) := by
    rw [← hk]
    simp only [mulVec_sub, mulVec_add, dotProduct_add, dotProduct_sub, sub_dotProduct,
      add_dotProduct]
    rw [rth21_dot_mulVec_comm hΩ M₂ N, rth21_dot_mulVec_comm hΩ M₂ A,
      dotProduct_comm B M₂]
    ring
  rw [key, Complex.exp_add, rth21_exp_int, mul_one]

/-- Parity with half-period characteristics, in the stronger form valid for all integer
vectors `a, b`: `θ[a/2; b/2](-z|Ω) = (-1)^{a·b} θ[a/2; b/2](z|Ω)`. DLMF 21.3.6 is the case
`aᵢ, bᵢ ∈ {0, 1}`, where `4α·β = a·b` (stronger than DLMF). -/
@[dlmf 21.3.E6 "stronger than DLMF: all integer a, b with α = a/2, β = b/2"]
theorem riemannThetaChar_neg_half (a b : ι → ℤ) (z : ι → ℂ) (Ω : Matrix ι ι ℂ) :
    riemannThetaChar (fun i => (a i : ℝ) / 2) (fun i => (b i : ℝ) / 2) (-z) Ω =
      (-1 : ℂ) ^ (a ⬝ᵥ b) *
        riemannThetaChar (fun i => (a i : ℝ) / 2) (fun i => (b i : ℝ) / 2) z Ω := by
  rw [riemannThetaChar, riemannThetaChar,
    ← ((Equiv.neg (ι → ℤ)).trans (Equiv.subRight a)).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [Equiv.trans_apply, Equiv.neg_apply, Equiv.subRight_apply, riemannThetaCharTerm,
    riemannThetaCharTerm]
  set U : ι → ℂ := fun i => (n i : ℂ) + (((a i : ℝ) / 2 : ℝ) : ℂ)
  set Bv : ι → ℂ := fun i => (((b i : ℝ) / 2 : ℝ) : ℂ)
  have hv : (fun i => (((-n - a) i : ℤ) : ℂ) + (((a i : ℝ) / 2 : ℝ) : ℂ)) = -U := by
    funext i; simp [U]; ring
  have hw : (fun i => (-z) i + (((b i : ℝ) / 2 : ℝ) : ℂ)) = -z + Bv := rfl
  have hw' : (fun i => z i + (((b i : ℝ) / 2 : ℝ) : ℂ)) = z + Bv := rfl
  rw [hv, hw, hw']
  have hUB : 2 * (U ⬝ᵥ Bv) = ((n ⬝ᵥ b : ℤ) : ℂ) + ((a ⬝ᵥ b : ℤ) : ℂ) / 2 := by
    simp only [U, Bv, dotProduct, Finset.mul_sum, Int.cast_sum, Int.cast_mul]
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have key : 2 * π * I * ((1 / 2 : ℂ) * ((-U) ⬝ᵥ (Ω *ᵥ -U)) + (-U) ⬝ᵥ (-z + Bv)) =
      (π * I * ((a ⬝ᵥ b : ℤ) : ℂ) +
        2 * π * I * ((1 / 2 : ℂ) * (U ⬝ᵥ (Ω *ᵥ U)) + U ⬝ᵥ (z + Bv))) +
      2 * π * I * ((-(n ⬝ᵥ b) - a ⬝ᵥ b : ℤ) : ℂ) := by
    have : (-U) ⬝ᵥ (-z + Bv) = U ⬝ᵥ (z + Bv) - 2 * (U ⬝ᵥ Bv) := by
      simp only [neg_dotProduct, dotProduct_add, dotProduct_neg]
      ring
    rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, this, hUB]
    push_cast
    ring
  rw [key, Complex.exp_add, Complex.exp_add, rth21_exp_int, mul_one,
    show π * I * ((a ⬝ᵥ b : ℤ) : ℂ) = ((a ⬝ᵥ b : ℤ) : ℂ) * (π * I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

end DLMF.RiemannTheta
