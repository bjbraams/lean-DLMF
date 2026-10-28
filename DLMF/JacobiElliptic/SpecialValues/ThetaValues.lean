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

Exact Jacobian elliptic values at the distinguished lattice and half-period points.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.SpecialValues`.
-/

@[expose] public section

open Complex DLMF.Elliptic Filter

open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

/-- The normalized theta functions at `ζ = 0`: `θ_s(0) = 0`, `θ_c(0) = θ_d(0) = θ_n(0) = 1`. -/
theorem je22a_letterTheta_zero {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) :
    jacobiLetterTheta p 0 τ = if p = .s then 0 else 1 := by
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  cases p <;> simp [jacobiLetterTheta, je22a_thetaOne_zero, h2, h3, h4]

/-- Values at `z = 0` of the functions without a pole there: `pq(0, k) = 0` for `p = s` and
`= 1` otherwise (`q ≠ s`). -/
theorem jacobiPQk_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) (p q : JacobiLetter)
    (hq : q ≠ .s) : jacobiPQk p q 0 k = if p = .s then 0 else 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hz : jacobiZetak 0 k = 0 := by simp [jacobiZetak]
  rw [jacobiPQk, hz, jacobiGlaisher]
  by_cases hpq : p = q
  · subst hpq; simp [hq]
  · simp only [hpq, ↓reduceIte, je22a_letterTheta_zero hτ, hq, div_one]

/-- `sn(0, k) = 0` (Table 22.5.1). -/
theorem jacobiSnk_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiSnk 0 k = 0 := by
  rw [jacobiSnk, jacobiPQk_zero hk _ _ (by decide)]
  rfl

/-- `cn(0, k) = 1` (Table 22.5.1). -/
theorem jacobiCnk_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiCnk 0 k = 1 := by
  rw [jacobiCnk, jacobiPQk_zero hk _ _ (by decide)]
  rfl

/-- `dn(0, k) = 1` (Table 22.5.1). -/
theorem jacobiDnk_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiDnk 0 k = 1 := by
  rw [jacobiDnk, jacobiPQk_zero hk _ _ (by decide)]
  rfl

/-- `cd(0, k) = 1` (Table 22.5.1). -/
theorem jacobiCdk_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiCdk 0 k = 1 := by
  rw [jacobiCdk, jacobiPQk_zero hk _ _ (by decide)]
  rfl

/-- `sd(0, k) = 0` (Table 22.5.1). -/
theorem jacobiSdk_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiSdk 0 k = 0 := by
  rw [jacobiSdk, jacobiPQk_zero hk _ _ (by decide)]
  rfl

/-- `nd(0, k) = 1` (Table 22.5.1). -/
theorem jacobiNdk_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiNdk 0 k = 1 := by
  rw [jacobiNdk, jacobiPQk_zero hk _ _ (by decide)]
  rfl

/-- `dc(0, k) = 1` (Table 22.5.1). -/
theorem jacobiDck_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiDck 0 k = 1 := by
  rw [jacobiDck, jacobiPQk_zero hk _ _ (by decide)]
  rfl

/-- `nc(0, k) = 1` (Table 22.5.1). -/
theorem jacobiNck_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiNck 0 k = 1 := by
  rw [jacobiNck, jacobiPQk_zero hk _ _ (by decide)]
  rfl

/-- `sc(0, k) = 0` (Table 22.5.1). -/
theorem jacobiSck_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : jacobiSck 0 k = 0 := by
  rw [jacobiSck, jacobiPQk_zero hk _ _ (by decide)]
  rfl

/-- Evaluate a coefficient times a value at `0`. -/
macro "je22a_value_tac " hk:term:max : tactic => `(tactic|
  (simp only [jacobiSnk_zero $hk, jacobiCnk_zero $hk, jacobiDnk_zero $hk, jacobiCdk_zero $hk,
    jacobiSdk_zero $hk, jacobiNdk_zero $hk, jacobiDck_zero $hk, jacobiNck_zero $hk,
    jacobiSck_zero $hk, mul_one, mul_zero, neg_zero] <;> try ring))

/-- Table 22.5.1, row `sn`: the finite values of `sn(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiSnk_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk 0 k = 0 ∧
    jacobiSnk (compEllIntKk k) k = 1 ∧
    jacobiSnk (compEllIntKk k + I * compEllIntKpk k) k = k⁻¹ ∧
    jacobiSnk (2 * compEllIntKk k) k = 0 ∧
    jacobiSnk (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = 0 ∧
    jacobiSnk (2 * (I * compEllIntKpk k)) k = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiSnk_zero hk
  · have h := (jacobiSnk_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSnk_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSnk_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSnk_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSnk_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

/-- Table 22.5.1, row `cn`: the finite values of `cn(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiCnk_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiCnk 0 k = 1 ∧
    jacobiCnk (compEllIntKk k) k = 0 ∧
    jacobiCnk (compEllIntKk k + I * compEllIntKpk k) k = -I * jacobiComodulusk k / k ∧
    jacobiCnk (2 * compEllIntKk k) k = -1 ∧
    jacobiCnk (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = 1 ∧
    jacobiCnk (2 * (I * compEllIntKpk k)) k = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiCnk_zero hk
  · have h := (jacobiCnk_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiCnk_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiCnk_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiCnk_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiCnk_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

/-- Table 22.5.1, row `dn`: the finite values of `dn(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiDnk_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiDnk 0 k = 1 ∧
    jacobiDnk (compEllIntKk k) k = jacobiComodulusk k ∧
    jacobiDnk (compEllIntKk k + I * compEllIntKpk k) k = 0 ∧
    jacobiDnk (2 * compEllIntKk k) k = 1 ∧
    jacobiDnk (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = -1 ∧
    jacobiDnk (2 * (I * compEllIntKpk k)) k = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiDnk_zero hk
  · have h := (jacobiDnk_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiDnk_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiDnk_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiDnk_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiDnk_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

/-- Table 22.5.1, row `cd`: the finite values of `cd(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiCdk_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiCdk 0 k = 1 ∧
    jacobiCdk (compEllIntKk k) k = 0 ∧
    jacobiCdk (I * compEllIntKpk k) k = k⁻¹ ∧
    jacobiCdk (2 * compEllIntKk k) k = -1 ∧
    jacobiCdk (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = -1 ∧
    jacobiCdk (2 * (I * compEllIntKpk k)) k = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiCdk_zero hk
  · have h := (jacobiCdk_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiCdk_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiCdk_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiCdk_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiCdk_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

/-- Table 22.5.1, row `sd`: the finite values of `sd(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiSdk_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSdk 0 k = 0 ∧
    jacobiSdk (compEllIntKk k) k = 1 / jacobiComodulusk k ∧
    jacobiSdk (I * compEllIntKpk k) k = I / k ∧
    jacobiSdk (2 * compEllIntKk k) k = 0 ∧
    jacobiSdk (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = 0 ∧
    jacobiSdk (2 * (I * compEllIntKpk k)) k = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiSdk_zero hk
  · have h := (jacobiSdk_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSdk_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSdk_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSdk_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSdk_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

/-- Table 22.5.1, row `nd`: the finite values of `nd(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiNdk_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiNdk 0 k = 1 ∧
    jacobiNdk (compEllIntKk k) k = 1 / jacobiComodulusk k ∧
    jacobiNdk (I * compEllIntKpk k) k = 0 ∧
    jacobiNdk (2 * compEllIntKk k) k = 1 ∧
    jacobiNdk (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = -1 ∧
    jacobiNdk (2 * (I * compEllIntKpk k)) k = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiNdk_zero hk
  · have h := (jacobiNdk_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiNdk_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiNdk_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiNdk_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiNdk_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

/-- Table 22.5.1, row `dc`: the finite values of `dc(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiDck_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiDck 0 k = 1 ∧
    jacobiDck (compEllIntKk k + I * compEllIntKpk k) k = 0 ∧
    jacobiDck (I * compEllIntKpk k) k = k ∧
    jacobiDck (2 * compEllIntKk k) k = -1 ∧
    jacobiDck (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = -1 ∧
    jacobiDck (2 * (I * compEllIntKpk k)) k = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiDck_zero hk
  · have h := (jacobiDck_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiDck_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiDck_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiDck_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiDck_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

/-- Table 22.5.1, row `nc`: the finite values of `nc(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiNck_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiNck 0 k = 1 ∧
    jacobiNck (compEllIntKk k + I * compEllIntKpk k) k = I * k / jacobiComodulusk k ∧
    jacobiNck (I * compEllIntKpk k) k = 0 ∧
    jacobiNck (2 * compEllIntKk k) k = -1 ∧
    jacobiNck (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = 1 ∧
    jacobiNck (2 * (I * compEllIntKpk k)) k = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiNck_zero hk
  · have h := (jacobiNck_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiNck_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiNck_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiNck_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiNck_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

/-- Table 22.5.1, row `sc`: the finite values of `sc(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiSck_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSck 0 k = 0 ∧
    jacobiSck (compEllIntKk k + I * compEllIntKpk k) k = I / jacobiComodulusk k ∧
    jacobiSck (I * compEllIntKpk k) k = I ∧
    jacobiSck (2 * compEllIntKk k) k = 0 ∧
    jacobiSck (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) k = 0 ∧
    jacobiSck (2 * (I * compEllIntKpk k)) k = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jacobiSck_zero hk
  · have h := (jacobiSck_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSck_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSck_shift hk 0).2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSck_shift hk 0).2.2.2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiSck_shift hk 0).2.2.2.2.2
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

/-- Table 22.5.1, row `ns`: the finite values of `ns(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiNsk_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiNsk (compEllIntKk k) k = 1 ∧
    jacobiNsk (compEllIntKk k + I * compEllIntKpk k) k = k ∧
    jacobiNsk (I * compEllIntKpk k) k = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (jacobiNsk_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiNsk_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiNsk_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

/-- Table 22.5.1, row `ds`: the finite values of `ds(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiDsk_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiDsk (compEllIntKk k) k = jacobiComodulusk k ∧
    jacobiDsk (compEllIntKk k + I * compEllIntKpk k) k = 0 ∧
    jacobiDsk (I * compEllIntKpk k) k = -I * k := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (jacobiDsk_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiDsk_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiDsk_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

/-- Table 22.5.1, row `cs`: the finite values of `cs(z, k)` at `z = 0, K, K + iK', iK', 2K,
2K + 2iK', 2iK'` (proved from Table 22.4.3 and the values at `0`). -/
@[dlmf 22.5.T1]
theorem jacobiCsk_specialValues {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiCsk (compEllIntKk k) k = 0 ∧
    jacobiCsk (compEllIntKk k + I * compEllIntKpk k) k = -I * jacobiComodulusk k ∧
    jacobiCsk (I * compEllIntKpk k) k = -I := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (jacobiCsk_shift hk 0).1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiCsk_shift hk 0).2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk
  · have h := (jacobiCsk_shift hk 0).2.2.1
    simp only [zero_add] at h
    rw [h]
    je22a_value_tac hk

end DLMF.JacobiElliptic
end
end
