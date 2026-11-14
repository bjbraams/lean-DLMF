/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Basic.Analytic
public import DLMF.RiemannTheta.Basic.Periodicity
import Mathlib.Tactic

/-!
# Theta functions in the negative-real-part normalization

The alternative theta function `Θ(φ|B) = θ(φ/(2πi)|B/(2πi))` has periods `2πim`
and multiplier `exp(-nBn/2 - nφ)` under translation by `Bn`. Symmetry and negative
definiteness of `Re B` give the usual domain, and `Θ` is entire in its vector argument.

References: Beals–Wong, *More Explorations in Complex Functions*, §11.3;
Mumford, *Tata Lectures on Theta II*, Chapter IIIb, §2. The normalization is the
existing DLMF alternative notation from Chapter 21.
-/

public noncomputable section

open Complex Matrix Set
open scoped Real

namespace DLMF.RiemannTheta

variable {ι : Type*} [Fintype ι]

/-- Symmetric matrices with negative definite real part give Riemann matrices after
division by `2πi`. -/
theorem inv_two_pi_I_smul_mem_siegelUpperHalfSpace {B : Matrix ι ι ℂ}
    (hB : Bᵀ = B) (hRe : (-(B.map Complex.re)).PosDef) :
    (2 * π * I)⁻¹ • B ∈ siegelUpperHalfSpace ι := by
  refine ⟨by rw [transpose_smul, hB], ?_⟩
  have hc : (2 * (π : ℂ) * I)⁻¹ = -I / (2 * π) := by
    rw [_root_.mul_inv_rev, Complex.inv_I]
    rfl
  have him : ((2 * π * I)⁻¹ • B).map Complex.im =
      ((2 * (π : ℝ))⁻¹) • -(B.map Complex.re) := by
    rw [hc]
    ext i j
    simp [smul_eq_mul, div_eq_mul_inv, Complex.mul_im, Complex.mul_re]
  rw [him]
  exact hRe.smul (inv_pos.mpr (by positivity))

/-- The alternative theta function is even for every matrix parameter. -/
theorem riemannThetaBig_neg (φ : ι → ℂ) (B : Matrix ι ι ℂ) :
    riemannThetaBig (-φ) B = riemannThetaBig φ B := by
  have hv : (fun i => (-φ) i / (2 * π * I)) =
      -(fun i => φ i / (2 * π * I)) := by
    ext i
    simp only [Pi.neg_apply, neg_div]
  rw [riemannThetaBig, riemannThetaBig, hv, riemannTheta_neg]

/-- The full lattice translation law in the alternative normalization. The linear term
uses the period-matrix vector `n`, as does the quadratic term. -/
theorem riemannThetaBig_add_lattice (φ : ι → ℂ) {B : Matrix ι ι ℂ} (hB : Bᵀ = B)
    (m n : ι → ℤ) :
    riemannThetaBig (φ + (2 * π * I) • (fun i => (m i : ℂ)) +
        B *ᵥ fun i => (n i : ℂ)) B =
      exp (-(1 / 2 : ℂ) * ((fun i => (n i : ℂ)) ⬝ᵥ (B *ᵥ fun i => (n i : ℂ))) -
        (fun i => (n i : ℂ)) ⬝ᵥ φ) * riemannThetaBig φ B := by
  have harg : (fun i => (φ + (2 * π * I) • (fun i => (m i : ℂ)) +
      B *ᵥ fun i => (n i : ℂ)) i / (2 * π * I)) =
      (fun i => φ i / (2 * π * I)) + (fun i => (m i : ℂ)) +
        ((2 * π * I)⁻¹ • B) *ᵥ fun i => (n i : ℂ) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_mulVec]
    field_simp [Complex.two_pi_I_ne_zero]
  have hnorm : (fun i => φ i / (2 * π * I)) = (2 * π * I)⁻¹ • φ := by
    ext i
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [riemannThetaBig, riemannThetaBig, harg,
    riemannTheta_add_lattice _ (by rw [transpose_smul, hB])]
  congr 1
  simp only [hnorm, smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  field_simp [Complex.two_pi_I_ne_zero]
  ring

/-- The vector periods `2πim` of the alternative theta function. -/
theorem riemannThetaBig_add_int (φ : ι → ℂ) (B : Matrix ι ι ℂ) (m : ι → ℤ) :
    riemannThetaBig (φ + (2 * π * I) • fun i => (m i : ℂ)) B = riemannThetaBig φ B := by
  have harg : (fun i => (φ + (2 * π * I) • fun i => (m i : ℂ)) i / (2 * π * I)) =
      (fun i => φ i / (2 * π * I)) + fun i => (m i : ℂ) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [Complex.two_pi_I_ne_zero]
  rw [riemannThetaBig, riemannThetaBig, harg, riemannTheta_add_int]

/-- The alternative theta function is entire when the normalized matrix is a Riemann matrix. -/
theorem differentiable_riemannThetaBig {B : Matrix ι ι ℂ}
    (hB : (2 * π * I)⁻¹ • B ∈ siegelUpperHalfSpace ι) :
    Differentiable ℂ (fun φ => riemannThetaBig φ B) := by
  have hd := (differentiable_riemannTheta hB).comp
    (differentiable_id.const_smul ((2 * π * I)⁻¹ : ℂ))
  convert hd using 1
  funext φ
  rw [riemannThetaBig]
  congr 1
  ext i
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

end DLMF.RiemannTheta
