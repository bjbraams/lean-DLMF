/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Appell.Basic.EulerBranches
public import Dirichlet.Beta.Complex.Integral

/-!
# Dirichlet's integral on Euler's triangle

The two-dimensional Dirichlet integral over `appellTriangle`, the integration domain of the
Euler integral of Appell's `F₃` (DLMF 16.15.3), obtained from the solid-simplex multivariate
Beta integral of lean-codes (`Complex.mvBetaIntegral_eq_mvBeta`, DLMF 5.14.2).

## Main definitions

* `appellTriangleKernel`: the kernel `u^(β-1) v^(β'-1) (1-u-v)^(γ-1)`.

## Main results

* `setIntegral_appellTriangleKernel`: `∫ = Γ(β) Γ(β') Γ(γ) / Γ(β + β' + γ)`.
* `integrableOn_appellTriangleKernel`: integrability for positive real parts.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set

namespace DLMF.Hypergeometric

/-- The Dirichlet kernel `u^(β-1) v^(β'-1) (1-u-v)^(γ-1)` on Euler's triangle `appellTriangle`,
with principal powers. -/
def appellTriangleKernel (β β' γ : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (β - 1) * (p.2 : ℂ) ^ (β' - 1) * ((1 - p.1 - p.2 : ℝ) : ℂ) ^ (γ - 1)

/-- The triangle in `ℝ × ℝ` is the solid simplex in `Fin 2 → ℝ`. -/
private lemma preimage_finTwoArrow_appellTriangle :
    (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹' appellTriangle =
      Complex.mvBetaSimplex 2 := by
  ext x
  simp [appellTriangle, Complex.mvBetaSimplex, Fin.forall_fin_two, Fin.sum_univ_two,
    MeasurableEquiv.finTwoArrow, and_assoc]

/-- The triangle integral as the multivariate Beta integral of lean-codes. -/
private lemma setIntegral_appellTriangleKernel_eq_mvBetaIntegral (β β' γ : ℂ) :
    ∫ p in appellTriangle, appellTriangleKernel β β' γ p =
      Complex.mvBetaIntegral γ ![β, β'] := by
  rw [← (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding, preimage_finTwoArrow_appellTriangle,
    Complex.mvBetaIntegral]
  refine setIntegral_congr_fun (Complex.measurableSet_mvBetaSimplex 2) fun x _ => ?_
  simp [appellTriangleKernel, MeasurableEquiv.finTwoArrow, Fin.sum_univ_two, Fin.prod_univ_two,
    sub_sub]
  ring

/-- Dirichlet's integral over the triangle (DLMF 5.14.2 with `n = 2`). -/
theorem setIntegral_appellTriangleKernel {β β' γ : ℂ} (hβ : 0 < β.re) (hβ' : 0 < β'.re)
    (hγ : 0 < γ.re) :
    ∫ p in appellTriangle, appellTriangleKernel β β' γ p =
      Gamma β * Gamma β' * Gamma γ / Gamma (β + β' + γ) := by
  rw [setIntegral_appellTriangleKernel_eq_mvBetaIntegral,
    Complex.mvBetaIntegral_eq_mvBeta hγ (by simp [Fin.forall_fin_two, hβ, hβ']),
    Complex.mvBeta]
  simp [Fin.prod_univ_succ, Fin.sum_univ_succ]
  ring_nf

/-- The Dirichlet kernel is integrable on the triangle. -/
theorem integrableOn_appellTriangleKernel {β β' γ : ℂ} (hβ : 0 < β.re) (hβ' : 0 < β'.re)
    (hγ : 0 < γ.re) : IntegrableOn (appellTriangleKernel β β' γ) appellTriangle := by
  by_contra h
  have h0 := integral_undef h
  rw [setIntegral_appellTriangleKernel hβ hβ' hγ] at h0
  have hs : 0 < (β + β' + γ).re := by simp; linarith
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (Gamma_ne_zero_of_re_pos hβ)
    (Gamma_ne_zero_of_re_pos hβ')) (Gamma_ne_zero_of_re_pos hγ))
    (Gamma_ne_zero_of_re_pos hs) h0

end DLMF.Hypergeometric
