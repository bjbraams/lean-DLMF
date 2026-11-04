/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Derivatives
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import DLMF.Elliptic.JacobiIdentities

/-!
# Theta-quotient values at elliptic special points

The values of the twelve Jacobian elliptic functions at `z = 0` and at the lattice points
`K, K + iK', iK', 2K, 2K + 2iK', 2iK'` (Table 22.5.1), for `k ∈ jacobiModulusDomain`.

## Main results

* `jacobiLetterTheta_zero`: `θ_s(0) = 0` and `θ_c(0) = θ_d(0) = θ_n(0) = 1`.
* `jacobiPQ_zero`: `pq(0, k) = 0` for `p = s` and `= 1` otherwise (`q ≠ s`), with the named
  cases `jacobiSn_zero`, `jacobiCn_zero`, `jacobiDn_zero` and companions.
* `jacobiSn_specialValues`, `jacobiCn_specialValues`, `jacobiDn_specialValues` and the nine
  companions such as `jacobiCs_specialValues`: the finite values in Table 22.5.1.

## Implementation notes

The values follow from the values at `z = 0` (`θ₁(0) = 0`, nonvanishing theta constants) and
the shift Table 22.4.3, in the modulus form via the inversion 22.2.2.
-/

@[expose] public section

open Complex DLMF.Elliptic Filter

open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

/-- The normalized theta functions at `ζ = 0`: `θ_s(0) = 0`, `θ_c(0) = θ_d(0) = θ_n(0) = 1`. -/
theorem jacobiLetterTheta_zero {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) :
    jacobiLetterTheta p 0 τ = if p = .s then 0 else 1 := by
  have h2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have h3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have h4 := jacobiThetaFourTau_zero_ne_zero hτ
  cases p <;> simp [jacobiLetterTheta, jacobiThetaOneTau_zero, h2, h3, h4]

/-- Values at `z = 0` of the functions without a pole there: `pq(0, k) = 0` for `p = s` and
`= 1` otherwise (`q ≠ s`). -/
theorem jacobiPQ_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) (p q : JacobiLetter)
    (hq : q ≠ .s) : jacobiPQ p q 0 k = if p = .s then 0 else 1 := by
  have hτ := jacobiTau_im_pos hk
  have hz : jacobiThetaArgument 0 k = 0 := by simp [jacobiThetaArgument]
  rw [jacobiPQ, hz, jacobiGlaisher]
  by_cases hpq : p = q
  · subst hpq; simp [hq]
  · simp only [hpq, ↓reduceIte, jacobiLetterTheta_zero hτ, hq, div_one]

/-- `sn(0, k) = 0` (Table 22.5.1). -/
theorem jacobiSn_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiSn 0 k = 0 := by
  rw [jacobiSn, jacobiPQ_zero hk _ _ (by decide)]
  rfl

/-- `cn(0, k) = 1` (Table 22.5.1). -/
theorem jacobiCn_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiCn 0 k = 1 := by
  rw [jacobiCn, jacobiPQ_zero hk _ _ (by decide)]
  rfl

/-- `dn(0, k) = 1` (Table 22.5.1). -/
theorem jacobiDn_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiDn 0 k = 1 := by
  rw [jacobiDn, jacobiPQ_zero hk _ _ (by decide)]
  rfl

/-- `cd(0, k) = 1` (Table 22.5.1). -/
theorem jacobiCd_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiCd 0 k = 1 := by
  rw [jacobiCd, jacobiPQ_zero hk _ _ (by decide)]
  rfl

/-- `sd(0, k) = 0` (Table 22.5.1). -/
theorem jacobiSd_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiSd 0 k = 0 := by
  rw [jacobiSd, jacobiPQ_zero hk _ _ (by decide)]
  rfl

/-- `nd(0, k) = 1` (Table 22.5.1). -/
theorem jacobiNd_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiNd 0 k = 1 := by
  rw [jacobiNd, jacobiPQ_zero hk _ _ (by decide)]
  rfl

/-- `dc(0, k) = 1` (Table 22.5.1). -/
theorem jacobiDc_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiDc 0 k = 1 := by
  rw [jacobiDc, jacobiPQ_zero hk _ _ (by decide)]
  rfl

/-- `nc(0, k) = 1` (Table 22.5.1). -/
theorem jacobiNc_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiNc 0 k = 1 := by
  rw [jacobiNc, jacobiPQ_zero hk _ _ (by decide)]
  rfl

/-- `sc(0, k) = 0` (Table 22.5.1). -/
theorem jacobiSc_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiSc 0 k = 0 := by
  rw [jacobiSc, jacobiPQ_zero hk _ _ (by decide)]
  rfl

/-- Evaluate a coefficient times a value at `0`. -/
macro "jacobi_value_tac " hk:term:max : tactic => `(tactic|
  (simp only [jacobiSn_zero $hk, jacobiCn_zero $hk, jacobiDn_zero $hk, jacobiCd_zero $hk,
    jacobiSd_zero $hk, jacobiNd_zero $hk, jacobiDc_zero $hk, jacobiNc_zero $hk,
    jacobiSc_zero $hk, mul_one, mul_zero, neg_zero] <;> try ring))

/-- Table 22.5.1, row `sn`: the finite values of `sn(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiSn_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSn 0 k = 0 ∧
    jacobiSn (completeEllipticK k) k = 1 ∧
    jacobiSn (completeEllipticK k + I * completeEllipticKPrime k) k = k⁻¹ ∧
    jacobiSn (2 * completeEllipticK k) k = 0 ∧
    jacobiSn (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k = 0 ∧
    jacobiSn (2 * (I * completeEllipticKPrime k)) k = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiSn_zero hk
  · have h := (jacobiSn_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSn_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSn_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSn_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSn_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

/-- Table 22.5.1, row `cn`: the finite values of `cn(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiCn_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiCn 0 k = 1 ∧
    jacobiCn (completeEllipticK k) k = 0 ∧
    jacobiCn (completeEllipticK k + I * completeEllipticKPrime k) k = -I * jacobiComodulus k / k ∧
    jacobiCn (2 * completeEllipticK k) k = -1 ∧
    jacobiCn (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k = 1 ∧
    jacobiCn (2 * (I * completeEllipticKPrime k)) k = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiCn_zero hk
  · have h := (jacobiCn_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiCn_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiCn_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiCn_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiCn_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

/-- Table 22.5.1, row `dn`: the finite values of `dn(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiDn_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiDn 0 k = 1 ∧
    jacobiDn (completeEllipticK k) k = jacobiComodulus k ∧
    jacobiDn (completeEllipticK k + I * completeEllipticKPrime k) k = 0 ∧
    jacobiDn (2 * completeEllipticK k) k = 1 ∧
    jacobiDn (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k = -1 ∧
    jacobiDn (2 * (I * completeEllipticKPrime k)) k = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiDn_zero hk
  · have h := (jacobiDn_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiDn_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiDn_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiDn_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiDn_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

/-- Table 22.5.1, row `cd`: the finite values of `cd(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiCd_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiCd 0 k = 1 ∧
    jacobiCd (completeEllipticK k) k = 0 ∧
    jacobiCd (I * completeEllipticKPrime k) k = k⁻¹ ∧
    jacobiCd (2 * completeEllipticK k) k = -1 ∧
    jacobiCd (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k = -1 ∧
    jacobiCd (2 * (I * completeEllipticKPrime k)) k = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiCd_zero hk
  · have h := (jacobiCd_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiCd_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiCd_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiCd_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiCd_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

/-- Table 22.5.1, row `sd`: the finite values of `sd(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiSd_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSd 0 k = 0 ∧
    jacobiSd (completeEllipticK k) k = 1 / jacobiComodulus k ∧
    jacobiSd (I * completeEllipticKPrime k) k = I / k ∧
    jacobiSd (2 * completeEllipticK k) k = 0 ∧
    jacobiSd (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k = 0 ∧
    jacobiSd (2 * (I * completeEllipticKPrime k)) k = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiSd_zero hk
  · have h := (jacobiSd_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSd_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSd_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSd_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSd_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

/-- Table 22.5.1, row `nd`: the finite values of `nd(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiNd_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiNd 0 k = 1 ∧
    jacobiNd (completeEllipticK k) k = 1 / jacobiComodulus k ∧
    jacobiNd (I * completeEllipticKPrime k) k = 0 ∧
    jacobiNd (2 * completeEllipticK k) k = 1 ∧
    jacobiNd (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k = -1 ∧
    jacobiNd (2 * (I * completeEllipticKPrime k)) k = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiNd_zero hk
  · have h := (jacobiNd_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiNd_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiNd_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiNd_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiNd_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

/-- Table 22.5.1, row `dc`: the finite values of `dc(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiDc_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiDc 0 k = 1 ∧
    jacobiDc (completeEllipticK k + I * completeEllipticKPrime k) k = 0 ∧
    jacobiDc (I * completeEllipticKPrime k) k = k ∧
    jacobiDc (2 * completeEllipticK k) k = -1 ∧
    jacobiDc (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k = -1 ∧
    jacobiDc (2 * (I * completeEllipticKPrime k)) k = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiDc_zero hk
  · have h := (jacobiDc_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiDc_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiDc_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiDc_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiDc_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

/-- Table 22.5.1, row `nc`: the finite values of `nc(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiNc_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiNc 0 k = 1 ∧
    jacobiNc (completeEllipticK k + I * completeEllipticKPrime k) k = I * k / jacobiComodulus k ∧
    jacobiNc (I * completeEllipticKPrime k) k = 0 ∧
    jacobiNc (2 * completeEllipticK k) k = -1 ∧
    jacobiNc (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k = 1 ∧
    jacobiNc (2 * (I * completeEllipticKPrime k)) k = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiNc_zero hk
  · have h := (jacobiNc_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiNc_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiNc_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiNc_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiNc_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

/-- Table 22.5.1, row `sc`: the finite values of `sc(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiSc_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSc 0 k = 0 ∧
    jacobiSc (completeEllipticK k + I * completeEllipticKPrime k) k = I / jacobiComodulus k ∧
    jacobiSc (I * completeEllipticKPrime k) k = I ∧
    jacobiSc (2 * completeEllipticK k) k = 0 ∧
    jacobiSc (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) k = 0 ∧
    jacobiSc (2 * (I * completeEllipticKPrime k)) k = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiSc_zero hk
  · have h := (jacobiSc_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSc_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSc_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSc_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiSc_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

/-- Table 22.5.1, row `ns`: the finite values of `ns(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiNs_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiNs (completeEllipticK k) k = 1 ∧
    jacobiNs (completeEllipticK k + I * completeEllipticKPrime k) k = k ∧
    jacobiNs (I * completeEllipticKPrime k) k = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (jacobiNs_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiNs_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiNs_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

/-- Table 22.5.1, row `ds`: the finite values of `ds(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiDs_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiDs (completeEllipticK k) k = jacobiComodulus k ∧
    jacobiDs (completeEllipticK k + I * completeEllipticKPrime k) k = 0 ∧
    jacobiDs (I * completeEllipticKPrime k) k = -I * k := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (jacobiDs_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiDs_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiDs_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

/-- Table 22.5.1, row `cs`: the finite values of `cs(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiCs_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiCs (completeEllipticK k) k = 0 ∧
    jacobiCs (completeEllipticK k + I * completeEllipticKPrime k) k = -I * jacobiComodulus k ∧
    jacobiCs (I * completeEllipticKPrime k) k = -I := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (jacobiCs_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiCs_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk
  · have h := (jacobiCs_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    jacobi_value_tac hk

end DLMF.JacobiElliptic
end
end
