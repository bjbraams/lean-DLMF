/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Recurrences
public import DLMF.Legendre.Basic.Properties
public import DLMF.Hypergeometric.AnalyticProperties

/-!
# Ferrers functions (Temme §8.7; DLMF §§14.2, 14.3, 14.6)

The Ferrers function `𝖯^μ_ν(x) = ((1+x)/(1-x))^{μ/2} 𝐅(ν+1, -ν; 1-μ; (1-x)/2)` on `(-1, 1)`
(DLMF 14.3.1): the integer-order formula. The associated Legendre equation `ferrersP_ode`, the
value `ferrersP_zero` at `μ = 0` and DLMF 15.2.3_5 on the cut plane (`regularizedGaussHG_neg_nat`)
are in `DLMF.Legendre.Basic.Properties` and `DLMF.Hypergeometric.Basic.CutPlane`.

## Main results

* `ferrersP_nat`: `𝖯^m_ν(x) = (-1)ᵐ (1-x²)^{m/2} P_ν⁽ᵐ⁾(x)` (DLMF 14.6.1).
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Topology Real

noncomputable section

namespace DLMF.Legendre

/-- For integer order, `𝖯^m_ν(x) = (-1)ᵐ (1-x²)^{m/2} dᵐP_ν(x)/dxᵐ` (DLMF 14.6.1). -/
@[dlmf 14.6.E1]
theorem ferrersP_nat (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ferrersP ν m x = (-1) ^ m * (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
      iteratedDeriv m (legendreP ν) x := by
  have hs : 1 + (x : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  have hw := mem_cutPlane_of_one_add hs
  rw [iteratedDeriv_legendreP ν m hs]
  rcases m with _ | m
  · simp [ferrersP_zero ν hx.1, legendreP, poch_zero]
  have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
  have h2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
  set k : ℕ := m + 1 with hk
  have hreal : ((1 + x) / (1 - x)) ^ ((k : ℝ) / 2) * ((1 - x) / 2) ^ k =
      (1 - x ^ 2) ^ ((k : ℝ) / 2) / 2 ^ k := by
    rw [Real.div_rpow h1.le h2.le, show 1 - x ^ 2 = (1 + x) * (1 - x) by ring,
      Real.mul_rpow h1.le h2.le, div_pow]
    have hsq : (1 - x) ^ k = (1 - x) ^ ((k : ℝ) / 2) * (1 - x) ^ ((k : ℝ) / 2) := by
      rw [← Real.rpow_add h2, add_halves, Real.rpow_natCast]
    have hpos : 0 < (1 - x) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos h2 _
    rw [hsq]
    field_simp
  have hwc : ((((1 - x) / 2 : ℝ)) : ℂ) ∈ cutPlane := by push_cast; exact hw
  rw [ferrersP, show (1 : ℂ) - (k : ℕ) = -(m : ℂ) by rw [hk]; push_cast; ring,
    regularizedGaussHG_neg_nat _ _ _ hw, regularizedGaussHG_symm (-ν + (k : ℕ)) _ _ hw]
  have hc : (((1 + x) / (1 - x) : ℝ) : ℂ) ^ (((k : ℕ) : ℂ) / 2) =
      (((1 + x) / (1 - x)) ^ ((k : ℝ) / 2) : ℝ) := by
    rw [ofReal_cpow (by positivity)]; push_cast; ring_nf
  have hreal' := congrArg (fun r : ℝ => (r : ℂ)) hreal
  push_cast at hreal'
  rw [hc]
  have hkc : ((k : ℕ) : ℂ) = (m : ℂ) + 1 := by rw [hk]; push_cast; ring
  rw [hkc, show ν + 1 + ((m : ℂ) + 1) = ν + 1 + m + 1 by ring,
    show -ν + ((m : ℂ) + 1) = -ν + m + 1 by ring, show (1 : ℂ) + ((m : ℂ) + 1) = m + 2 by ring]
  rw [← hk]
  have hneg : ((-1 : ℂ)) ^ k * (-1 / 2) ^ k = 1 / 2 ^ k := by
    rw [← mul_pow, one_div, ← inv_pow]; norm_num
  linear_combination (poch (ν + 1) k * poch (-ν) k *
    regularizedGaussHG (ν + 1 + m + 1) (-ν + m + 1) (m + 2) ((1 - (x : ℂ)) / 2)) * hreal' -
    (((1 - x ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * poch (ν + 1) k * poch (-ν) k *
    regularizedGaussHG (ν + 1 + m + 1) (-ν + m + 1) (m + 2) ((1 - (x : ℂ)) / 2) * hneg

end DLMF.Legendre

end
