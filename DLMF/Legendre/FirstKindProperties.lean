/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Basic

public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.OrthogonalPolynomials.Classical

/-!
# Legendre functions of the first kind (Temme §§8.1–8.2, DLMF §14.3)

Canonical definitions are in `DLMF.Legendre.Basic`; this module develops their properties.

`P_ν(z) = F(-ν, ν+1; 1; (1-z)/2)` is defined through the continuation `regularizedGaussHG` of `₂F₁`
to the cut plane, so it is analytic on `ℂ ∖ (-∞, -1]` for every complex `ν`. This file proves
`P_ν(1) = 1`, the symmetry `P_{-ν-1} = P_ν`, agreement with the Legendre polynomials at integer
degree, and Legendre's differential equation. The latter comes from the hypergeometric equation
for `regularizedGaussHG` on the cut plane, which is the diagonal contiguous relation times `ab`.
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Topology
open DLMF.OrthogonalPolynomials

noncomputable section

namespace DLMF.Hypergeometric

/-- The hypergeometric equation (DLMF 15.10.1) for the continuation `𝐅` on the cut plane, with
`𝐅'` and `𝐅''` written through 15.5.1–15.5.2. -/
@[dlmf 15.10.E1]
theorem regularizedGaussHG_ode (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    z * (1 - z) * (poch a 2 * poch b 2 * regularizedGaussHG (a + 2) (b + 2) (c + 2) z) +
      (c - (a + b + 1) * z) * (a * b * regularizedGaussHG (a + 1) (b + 1) (c + 1) z) -
      a * b * regularizedGaussHG a b c z = 0 := by
  have h := regularizedGaussHG_contiguous_diagonal a b c hz
  simp only [poch, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one]
  push_cast
  linear_combination (a * b) * h

end DLMF.Hypergeometric

namespace DLMF.Legendre





/-- For `z ∉ (-∞, -1]`, the argument `(1-z)/2` lies in the cut plane. -/
theorem mem_cutPlane_of_one_add {z : ℂ} (hz : 1 + z ∈ slitPlane) : (1 - z) / 2 ∈ cutPlane := by
  rw [mem_cutPlane, show 1 - (1 - z) / 2 = (1 + z) / 2 by ring]
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp at h ⊢; linarith
  · right; simpa using h

/-- `P_ν(1) = 1`. -/
theorem legendreP_one (ν : ℂ) : legendreP ν 1 = 1 := by
  rw [legendreP, sub_self, zero_div, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by simp),
    regularizedGaussHGFun_eq_div_Gamma (fun k h => by
      have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])]
  simp

/-- `P_{-ν-1} = P_ν` (DLMF 14.9.5, Temme (8.6)). -/
@[dlmf 14.9.E5]
theorem legendreP_neg_sub_one (ν : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    legendreP (-ν - 1) z = legendreP ν z := by
  rw [legendreP, legendreP, regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hz)]
  congr 1 <;> ring


/-- The domain `ℂ ∖ (-∞, -1]` is open. -/
theorem isOpen_one_add_mem_slitPlane : IsOpen {z : ℂ | 1 + z ∈ slitPlane} :=
  isOpen_slitPlane.preimage (by fun_prop)

/-- Chain rule for `z ↦ 𝐅(a,b;c;(1-z)/2)`. -/
theorem hasDerivAt_regularizedGaussHG_half (a b c : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    HasDerivAt (fun z => regularizedGaussHG a b c ((1 - z) / 2))
      (-(1 / 2) * (a * b * regularizedGaussHG (a + 1) (b + 1) (c + 1) ((1 - z) / 2))) z := by
  have hw := mem_cutPlane_of_one_add hz
  have h := (differentiableAt_regularizedGaussHG a b c hw).hasDerivAt
  rw [deriv_regularizedGaussHG _ _ _ hw] at h
  have hl : HasDerivAt (fun z : ℂ => (1 - z) / 2) (-1 / 2) z := by
    simpa using ((hasDerivAt_id z).const_sub 1).div_const 2
  exact (h.comp z hl).congr_deriv (by ring)

/-- `P_ν'` through `𝐅(1-ν, ν+2; 2; (1-z)/2)`. -/
theorem deriv_legendreP (ν : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    deriv (legendreP ν) z =
      -(1 / 2) * (-ν * (ν + 1) * regularizedGaussHG (-ν + 1) (ν + 1 + 1) 2 ((1 - z) / 2)) := by
  have h := (hasDerivAt_regularizedGaussHG_half (-ν) (ν + 1) 1 hz).deriv
  rw [show (1 : ℂ) + 1 = 2 by norm_num] at h
  exact h

/-- `P_ν''` through `𝐅(2-ν, ν+3; 3; (1-z)/2)`. -/
theorem iteratedDeriv_two_legendreP (ν : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    iteratedDeriv 2 (legendreP ν) z =
      (1 / 4) * (-ν * (-ν + 1) * ((ν + 1) * (ν + 2)) *
        regularizedGaussHG (-ν + 2) (ν + 3) 3 ((1 - z) / 2)) := by
  have hev : deriv (legendreP ν) =ᶠ[𝓝 z] fun z =>
      -(1 / 2) * (-ν * (ν + 1) * regularizedGaussHG (-ν + 1) (ν + 1 + 1) 2 ((1 - z) / 2)) := by
    filter_upwards [isOpen_one_add_mem_slitPlane.mem_nhds hz] with w hw
    exact deriv_legendreP ν hw
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
  have h := ((hasDerivAt_regularizedGaussHG_half (-ν + 1) (ν + 1 + 1) 2 hz).const_mul
    (-ν * (ν + 1))).const_mul (-(1 / 2) : ℂ)
  rw [h.deriv]
  rw [show -ν + 1 + 1 = -ν + 2 by ring, show ν + 1 + 1 + 1 = ν + 3 by ring,
    show (2 : ℂ) + 1 = 3 by norm_num]
  ring

/-- Legendre's equation `(1-z²) w'' - 2z w' + ν(ν+1) w = 0` (DLMF 14.2.2 with `μ = 0`). -/
@[dlmf 14.2.E2]
theorem legendreP_ode (ν : ℂ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    (1 - z ^ 2) * iteratedDeriv 2 (legendreP ν) z - 2 * z * deriv (legendreP ν) z +
      ν * (ν + 1) * legendreP ν z = 0 := by
  have h := regularizedGaussHG_ode (-ν) (ν + 1) 1 (mem_cutPlane_of_one_add hz)
  rw [iteratedDeriv_two_legendreP ν hz, deriv_legendreP ν hz, legendreP]
  simp only [poch, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one] at h
  rw [show (1 : ℂ) + 1 = 2 by norm_num, show (1 : ℂ) + 2 = 3 by norm_num,
    show ν + 1 + 2 = ν + 3 by ring] at h
  push_cast at h
  linear_combination h


/-- For `n ∈ ℕ`, `P_n` is the Legendre polynomial (DLMF 14.7.1 with `μ = 0`). -/
theorem legendreP_nat (n : ℕ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    legendreP n z = legendrePolyP n z := by
  have h1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hpoly : AnalyticOnNhd ℂ (fun w => ₂F₁ (-(n : ℂ)) ((n : ℂ) + 1) 1 w) cutPlane := by
    intro w _
    simp_rw [ordinaryHypergeometric_eq_sum_neg_nat]
    fun_prop
  have heq := regularizedGaussHG_unique hpoly (fun w hw => by
    rw [regularizedGaussHGFun_eq_div_Gamma h1, Gamma_one, div_one])
  rw [legendreP, ← heq (mem_cutPlane_of_one_add hz), legendrePolyP, jacobiPolyP]
  simp only [zero_add, add_zero, poch_nat_one]
  rw [div_self (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_mul]

end DLMF.Legendre

end
