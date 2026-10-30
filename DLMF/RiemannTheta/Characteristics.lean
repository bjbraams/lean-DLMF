/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Scaled

/-!
# Riemann theta characteristics, examples and classical theta identities
-/

@[expose] public noncomputable section

open Complex Matrix Finset Filter Topology
open scoped Real

variable {ι : Type*} [Fintype ι]

namespace DLMF.RiemannTheta

/-! ## The example of DLMF 21.2.3–21.2.4 and the Riemann matrices of §21.4 -/

/-- `Ω₁ = [[i, -1/2], [-1/2, i]]` of DLMF 21.4.2 (graphics section; exact matrix retained). -/
@[dlmf 21.4.E2]
theorem riemannMatrixExample_eq_omegaOne :
    riemannMatrixExample = !![I, -1 / 2; -1 / 2, I] := rfl

/-- Identity under the stated parameter and domain assumptions: `riemannMatrixExample.map
Complex.im = 1`. -/
theorem riemannMatrixExample_map_im : riemannMatrixExample.map Complex.im = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [riemannMatrixExample]

/-- The example matrix is a Riemann matrix. -/
@[dlmf 21.2.E3 "the example matrix lies in the Siegel upper half-space"]
theorem riemannMatrixExample_mem : riemannMatrixExample ∈ siegelUpperHalfSpace (Fin 2) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [riemannMatrixExample]
  · rw [riemannMatrixExample_map_im]
    exact Matrix.PosDef.one

/-- Identity under the stated parameter and domain assumptions: `riemannThetaTerm z
riemannMatrixExample n = cexp (-π * ((n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2)) * cexp (-I * π * (n 0 * n
1 : ℂ)) * cexp (2 * π * I * (n 0 * z 0 + n 1 * z 1))`. -/
lemma rth21_example_term (z : Fin 2 → ℂ) (n : Fin 2 → ℤ) :
    riemannThetaTerm z riemannMatrixExample n =
      cexp (-π * ((n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2)) * cexp (-I * π * (n 0 * n 1 : ℂ)) *
        cexp (2 * π * I * (n 0 * z 0 + n 1 * z 1)) := by
  rw [riemannThetaTerm, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp [riemannMatrixExample, dotProduct, mulVec, Fin.sum_univ_two]
  ring_nf
  rw [I_sq]
  ring

/-- The double series for the example (DLMF 21.2.3). -/
@[dlmf 21.2.E3]
theorem riemannTheta_example (z₁ z₂ : ℂ) :
    riemannTheta ![z₁, z₂] riemannMatrixExample =
      ∑' n₁ : ℤ, ∑' n₂ : ℤ, cexp (-π * ((n₁ : ℂ) ^ 2 + (n₂ : ℂ) ^ 2)) *
        cexp (-I * π * (n₁ * n₂ : ℂ)) * cexp (2 * π * I * (n₁ * z₁ + n₂ * z₂)) := by
  have hs := (summable_norm_riemannThetaTerm ![z₁, z₂] riemannMatrixExample_mem).of_norm
  rw [riemannTheta, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  have hs' := (finTwoArrowEquiv ℤ).symm.summable_iff.mpr hs
  refine (hs'.tsum_prod).trans ?_
  refine tsum_congr fun n₁ => tsum_congr fun n₂ => ?_
  rw [Function.comp_apply, rth21_example_term]
  simp

/-- The scaled double series for the example (DLMF 21.2.4), `z_j = x_j + i y_j`. -/
@[dlmf 21.2.E4]
theorem riemannThetaScaled_example (x₁ y₁ x₂ y₂ : ℝ) :
    riemannThetaScaled ![x₁ + y₁ * I, x₂ + y₂ * I] riemannMatrixExample =
      ∑' n₁ : ℤ, ∑' n₂ : ℤ, cexp (-π * ((n₁ + y₁ : ℂ) ^ 2) - π * ((n₂ + y₂ : ℂ) ^ 2)) *
        cexp (π * I * (2 * n₁ * x₁ + 2 * n₂ * x₂ - n₁ * n₂)) := by
  rw [riemannThetaScaled, riemannTheta_example, riemannMatrixExample_map_im, inv_one,
    one_mulVec, ← tsum_mul_left]
  refine tsum_congr fun n₁ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun n₂ => ?_
  have hy : ((fun i => ((![x₁ + y₁ * I, x₂ + y₂ * I] : Fin 2 → ℂ) i).im) ⬝ᵥ
      fun i => ((![x₁ + y₁ * I, x₂ + y₂ * I] : Fin 2 → ℂ) i).im) = y₁ ^ 2 + y₂ ^ 2 := by
    simp [dotProduct, Fin.sum_univ_two, sq]
  rw [hy, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- `Ω₂` of DLMF 21.4.3 is a Riemann matrix. -/
@[dlmf 21.4.E3 "Ω₂ lies in the Siegel upper half-space"]
theorem riemannMatrixOmegaTwo_mem : riemannMatrixOmegaTwo ∈ siegelUpperHalfSpace (Fin 3) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [riemannMatrixOmegaTwo]
  · refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [riemannMatrixOmegaTwo]
    · have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (by ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2])
      simp [riemannMatrixOmegaTwo, dotProduct, mulVec, Fin.sum_univ_three]
      rcases hx' with h | h | h
      · have := pow_pos (abs_pos.mpr h) 2
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1),
          sq_nonneg (x 2), sq_abs (x 0)]
      · have := pow_pos (abs_pos.mpr h) 2
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1),
          sq_nonneg (x 2), sq_abs (x 1)]
      · have := pow_pos (abs_pos.mpr h) 2
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1),
          sq_nonneg (x 2), sq_abs (x 2)]

/-! ## Characteristics (DLMF §21.2(ii)) -/

/-- Identity under the stated parameter and domain assumptions: `a ⬝ᵥ (Ω *ᵥ b) = b ⬝ᵥ (Ω *ᵥ a)`. -/
theorem rth21_dot_mulVec_comm {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω) (a b : ι → ℂ) :
    a ⬝ᵥ (Ω *ᵥ b) = b ⬝ᵥ (Ω *ᵥ a) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hΩ, dotProduct_comm]

/-- The characteristic term as a multiple of a shifted theta term (DLMF 21.2.6, termwise). -/
theorem riemannThetaCharTerm_eq (α β : ι → ℝ) (z : ι → ℂ) {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω)
    (n : ι → ℤ) :
    riemannThetaCharTerm α β z Ω n =
      cexp (2 * π * I * ((1 / 2 : ℂ) * ((fun i => (α i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (α i : ℂ))) +
        (fun i => (α i : ℂ)) ⬝ᵥ (z + fun i => (β i : ℂ)))) *
      riemannThetaTerm (z + Ω *ᵥ (fun i => (α i : ℂ)) + fun i => (β i : ℂ)) Ω n := by
  rw [riemannThetaCharTerm, riemannThetaTerm, ← Complex.exp_add]
  congr 1
  have hv : (fun i => (n i : ℂ) + (α i : ℂ)) = (fun i => (n i : ℂ)) + fun i => (α i : ℂ) := rfl
  have hz : (fun i => z i + (β i : ℂ)) = z + fun i => (β i : ℂ) := rfl
  rw [hv, hz]
  simp only [mulVec_add, dotProduct_add, add_dotProduct]
  rw [rth21_dot_mulVec_comm hΩ (fun i => (α i : ℂ)) (fun i => (n i : ℂ))]
  ring

/-- `θ[α;β](z|Ω) = exp(2πi(½ α·Ω·α + α·[z+β])) θ(z + Ωα + β|Ω)` (DLMF 21.2.6).
Corrected from the printed DLMF formula: the hypothesis `Ωᵀ = Ω` is stated, since the identity
uses `n·Ω·α = α·Ω·n` (DLMF assumes it implicitly through the Siegel space). -/
@[dlmf 21.2.E6]
theorem riemannThetaChar_eq (α β : ι → ℝ) (z : ι → ℂ) {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω) :
    riemannThetaChar α β z Ω =
      cexp (2 * π * I * ((1 / 2 : ℂ) * ((fun i => (α i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (α i : ℂ))) +
        (fun i => (α i : ℂ)) ⬝ᵥ (z + fun i => (β i : ℂ)))) *
      riemannTheta (z + Ω *ᵥ (fun i => (α i : ℂ)) + fun i => (β i : ℂ)) Ω := by
  rw [riemannThetaChar, riemannTheta, ← tsum_mul_left]
  exact tsum_congr fun n => riemannThetaCharTerm_eq α β z hΩ n

/-- `θ[0;0](z|Ω) = θ(z|Ω)` (DLMF 21.2.7). -/
@[dlmf 21.2.E7]
theorem riemannThetaChar_zero (z : ι → ℂ) (Ω : Matrix ι ι ℂ) :
    riemannThetaChar 0 0 z Ω = riemannTheta z Ω := by
  rw [riemannThetaChar, riemannTheta]
  refine tsum_congr fun n => ?_
  simp [riemannThetaCharTerm, riemannThetaTerm]

/-- The theta series with characteristics converges absolutely for `Ω` in the Siegel space. -/
@[dlmf 21.2.ii "absolute convergence of the series with characteristics"]
theorem summable_norm_riemannThetaCharTerm (α β : ι → ℝ) (z : ι → ℂ) {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    Summable fun n => ‖riemannThetaCharTerm α β z Ω n‖ := by
  simp_rw [riemannThetaCharTerm_eq α β z hΩ.1, norm_mul]
  exact (summable_norm_riemannThetaTerm _ hΩ).mul_left _

/-- There are `2^{2g}` half-period characteristics (DLMF §21.2(ii)). -/
@[dlmf 21.2.ii "there are 2^(2g) half-period characteristics"]
theorem ncard_halfPeriodCharacteristics [DecidableEq ι] :
    (halfPeriodCharacteristics ι).ncard = 2 ^ (2 * Fintype.card ι) := by
  let e : (ι → Bool) × (ι → Bool) → (ι → ℝ) × (ι → ℝ) := fun b =>
    (fun i => if b.1 i then 1 / 2 else 0, fun i => if b.2 i then 1 / 2 else 0)
  have he : Function.Injective e := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [e, Prod.mk.injEq] at h
    have h1 := h.1
    have h2 := h.2
    ext i
    · have := congrFun h1 i
      rcases Bool.eq_false_or_eq_true (a i) with ha | ha <;>
        rcases Bool.eq_false_or_eq_true (c i) with hc | hc <;> simp [ha, hc] at this ⊢
    · have := congrFun h2 i
      rcases Bool.eq_false_or_eq_true (b i) with ha | ha <;>
        rcases Bool.eq_false_or_eq_true (d i) with hc | hc <;> simp [ha, hc] at this ⊢
  have hrange : halfPeriodCharacteristics ι = Set.range e := by
    ext ⟨α, β⟩
    constructor
    · intro h
      refine ⟨(fun i => decide (α i = 1 / 2), fun i => decide (β i = 1 / 2)), ?_⟩
      simp only [e, Prod.mk.injEq]
      constructor <;> funext i
      · rcases (h i).1 with h' | h' <;> simp only at h' <;> simp [h']
      · rcases (h i).2 with h' | h' <;> simp only at h' <;> simp [h']
    · rintro ⟨⟨a, b⟩, hab⟩
      simp only [e, Prod.mk.injEq] at hab
      intro i
      rw [← hab.1, ← hab.2]
      constructor
      · cases a i <;> simp
      · cases b i <;> simp
  rw [hrange, ← Set.image_univ, Set.ncard_image_of_injective _ he, Set.ncard_univ,
    Nat.card_eq_fintype_card]
  simp [Fintype.card_prod, Fintype.card_bool, pow_mul, sq, ← mul_pow]

/-! ## Relation to the classical theta functions (DLMF §21.2(iii)) -/

open DLMF.Elliptic

/-- Identity under the stated parameter and domain assumptions: `∑' n, f n = ∑' k : ℤ, f fun _ =>
k`. -/
lemma rth21_tsum_fin_one (f : (Fin 1 → ℤ) → ℂ) : ∑' n, f n = ∑' k : ℤ, f fun _ => k := by
  rw [← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
  rfl

/-- `θ(z|Ω) = θ₃(πz|Ω)` for `g = 1` (DLMF 21.2.8). -/
@[dlmf 21.2.E8]
theorem riemannTheta_fin_one (z τ : ℂ) :
    riemannTheta ![z] !![τ] = jacobiThetaThreeTau (π * z) τ := by
  rw [riemannTheta, rth21_tsum_fin_one, jacobiThetaThreeTau_eq_tsum]
  refine tsum_congr fun k => ?_
  simp only [riemannThetaTerm]
  congr 1
  simp [dotProduct, mulVec]
  ring

/-- Characteristics in genus one reduce to a shifted `θ₃`. -/
lemma rth21_char_fin_one (a b : ℝ) (z τ : ℂ) :
    riemannThetaChar ![a] ![b] ![z] !![τ] =
      cexp (2 * π * I * ((1 / 2 : ℂ) * (a * (τ * a)) + a * (z + b))) *
        jacobiThetaThreeTau (π * (z + τ * a + b)) τ := by
  rw [riemannThetaChar_eq _ _ _ (by ext i j; fin_cases i; fin_cases j; rfl),
    ← riemannTheta_fin_one]
  congr 2
  · simp [dotProduct]
  · ext i
    fin_cases i
    simp [dotProduct]

/-- `θ₁(πz|Ω) = -θ[½;½](z|Ω)` for `g = 1` (DLMF 21.2.9). -/
@[dlmf 21.2.E9]
theorem jacobiThetaOneTau_eq_riemannThetaChar (z τ : ℂ) :
    jacobiThetaOneTau (π * z) τ = -riemannThetaChar ![1 / 2] ![1 / 2] ![z] !![τ] := by
  rw [rth21_char_fin_one, jacobiThetaOneTau, jacobiThetaTwoTau]
  push_cast
  congr 2
  · congr 1
    ring
  · congr 1
    ring

/-- `θ₂(πz|Ω) = θ[½;0](z|Ω)` for `g = 1` (DLMF 21.2.10). -/
@[dlmf 21.2.E10]
theorem jacobiThetaTwoTau_eq_riemannThetaChar (z τ : ℂ) :
    jacobiThetaTwoTau (π * z) τ = riemannThetaChar ![1 / 2] ![0] ![z] !![τ] := by
  rw [rth21_char_fin_one, jacobiThetaTwoTau]
  push_cast
  congr 1
  · congr 1
    ring
  · congr 1
    ring

/-- `θ₃(πz|Ω) = θ[0;0](z|Ω)` for `g = 1` (DLMF 21.2.11). -/
@[dlmf 21.2.E11]
theorem jacobiThetaThreeTau_eq_riemannThetaChar (z τ : ℂ) :
    jacobiThetaThreeTau (π * z) τ = riemannThetaChar ![0] ![0] ![z] !![τ] := by
  rw [rth21_char_fin_one]
  simp

/-- `θ₄(πz|Ω) = θ[0;½](z|Ω)` for `g = 1` (DLMF 21.2.12). -/
@[dlmf 21.2.E12]
theorem jacobiThetaFourTau_eq_riemannThetaChar (z τ : ℂ) :
    jacobiThetaFourTau (π * z) τ = riemannThetaChar ![0] ![1 / 2] ![z] !![τ] := by
  rw [rth21_char_fin_one, jacobiThetaFourTau]
  push_cast
  simp only [mul_zero, zero_mul, add_zero, Complex.exp_zero, one_mul]
  congr 1
  ring

end DLMF.RiemannTheta
