/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.PeriodsPolesZeros

/-!
# Jacobian elliptic functions: special values (DLMF §22.5)

The values in Table 22.5.1 follow from the values at `z = 0` (`θ₁(0) = 0`, nonvanishing theta
constants) and the shift Table 22.4.3; they are proved (in the modulus form from the admitted
inversion 22.2.2). The derivatives and residues of Table 22.5.1 (which need `θ₁'(0)`), the
values at quarter- and three-quarter-periods of Table 22.5.2 and the limiting forms of
Tables 22.5.3–22.5.4 are admitted.

**Correction.** Table 22.5.1 prints `0, k` for `dc` at `z = K + iK'`; the derivative is `-k`
(from `dc(z) = ns(z + K)`, `ns(z + 2K) = -ns z` and `ns'(iK') = k`, and numerically).
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

/-- **Admitted.** Table 22.5.1, row `sn`: the `z`-derivative of `sn(z, k)` at the regular
special points and the residue at the poles. -/
@[dlmf 22.5.T1]
theorem jacobiSnk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiSnk w k) (1) (0) ∧
    HasDerivAt (fun w => jacobiSnk w k) (0) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiSnk w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (I * compEllIntKpk k)) * jacobiSnk w k) (𝓝[≠] (I * compEllIntKpk k))
        (𝓝 (k⁻¹)) ∧
    HasDerivAt (fun w => jacobiSnk w k) (-1) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiSnk w k) (-1) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiSnk w k) (1) (2 * (I * compEllIntKpk k)) := by
  sorry

/-- **Admitted.** Table 22.5.1, row `cn`: the `z`-derivative of `cn(z, k)` at the regular
special points and the residue at the poles. -/
@[dlmf 22.5.T1]
theorem jacobiCnk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiCnk w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiCnk w k) (-jacobiComodulusk k) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiCnk w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (I * compEllIntKpk k)) * jacobiCnk w k) (𝓝[≠] (I * compEllIntKpk k))
        (𝓝 (-I / k)) ∧
    HasDerivAt (fun w => jacobiCnk w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiCnk w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiCnk w k) (0) (2 * (I * compEllIntKpk k)) := by
  sorry

/-- **Admitted.** Table 22.5.1, row `dn`: the `z`-derivative of `dn(z, k)` at the regular
special points and the residue at the poles. -/
@[dlmf 22.5.T1]
theorem jacobiDnk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiDnk w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiDnk w k) (0) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiDnk w k) (I * jacobiComodulusk k)
        (compEllIntKk k + I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (I * compEllIntKpk k)) * jacobiDnk w k) (𝓝[≠] (I * compEllIntKpk k))
        (𝓝 (-I)) ∧
    HasDerivAt (fun w => jacobiDnk w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiDnk w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiDnk w k) (0) (2 * (I * compEllIntKpk k)) := by
  sorry

/-- **Admitted.** Table 22.5.1, row `cd`: the `z`-derivative of `cd(z, k)` at the regular
special points and the residue at the poles. -/
@[dlmf 22.5.T1]
theorem jacobiCdk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiCdk w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiCdk w k) (-1) (compEllIntKk k) ∧
    Tendsto (fun w => (w - (compEllIntKk k + I * compEllIntKpk k)) * jacobiCdk w k)
        (𝓝[≠] (compEllIntKk k + I * compEllIntKpk k))
        (𝓝 (-k⁻¹)) ∧
    HasDerivAt (fun w => jacobiCdk w k) (0) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiCdk w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiCdk w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiCdk w k) (0) (2 * (I * compEllIntKpk k)) := by
  sorry

/-- **Admitted.** Table 22.5.1, row `sd`: the `z`-derivative of `sd(z, k)` at the regular
special points and the residue at the poles. -/
@[dlmf 22.5.T1]
theorem jacobiSdk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiSdk w k) (1) (0) ∧
    HasDerivAt (fun w => jacobiSdk w k) (0) (compEllIntKk k) ∧
    Tendsto (fun w => (w - (compEllIntKk k + I * compEllIntKpk k)) * jacobiSdk w k)
        (𝓝[≠] (compEllIntKk k + I * compEllIntKpk k))
        (𝓝 (-I / (k * jacobiComodulusk k))) ∧
    HasDerivAt (fun w => jacobiSdk w k) (0) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiSdk w k) (-1) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiSdk w k) (1) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiSdk w k) (-1) (2 * (I * compEllIntKpk k)) := by
  sorry

/-- **Admitted.** Table 22.5.1, row `nd`: the `z`-derivative of `nd(z, k)` at the regular
special points and the residue at the poles. -/
@[dlmf 22.5.T1]
theorem jacobiNdk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiNdk w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiNdk w k) (0) (compEllIntKk k) ∧
    Tendsto (fun w => (w - (compEllIntKk k + I * compEllIntKpk k)) * jacobiNdk w k)
        (𝓝[≠] (compEllIntKk k + I * compEllIntKpk k))
        (𝓝 (-I / jacobiComodulusk k)) ∧
    HasDerivAt (fun w => jacobiNdk w k) (I) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiNdk w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiNdk w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiNdk w k) (0) (2 * (I * compEllIntKpk k)) := by
  sorry

/-- **Admitted.** Table 22.5.1, row `dc`: the `z`-derivative of `dc(z, k)` at the regular
special points and the residue at the poles. Corrected from the printed DLMF formula: the
printed derivative `k` of `dc` at `K + iK'` has the wrong sign; it is `-k` (numerical
differentiation and `dc' = (1 - k²) sc nc`, see the ledger). -/
@[dlmf 22.5.T1 "corrected: d dc/dz = -k at K + iK'"]
theorem jacobiDck_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiDck w k) (0) (0) ∧
    Tendsto (fun w => (w - (compEllIntKk k)) * jacobiDck w k) (𝓝[≠] (compEllIntKk k))
        (𝓝 (-1)) ∧
    HasDerivAt (fun w => jacobiDck w k) (-k) (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiDck w k) (0) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiDck w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiDck w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiDck w k) (0) (2 * (I * compEllIntKpk k)) := by
  sorry

/-- **Admitted.** Table 22.5.1, row `nc`: the `z`-derivative of `nc(z, k)` at the regular
special points and the residue at the poles. -/
@[dlmf 22.5.T1]
theorem jacobiNck_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiNck w k) (0) (0) ∧
    Tendsto (fun w => (w - (compEllIntKk k)) * jacobiNck w k) (𝓝[≠] (compEllIntKk k))
        (𝓝 (-1 / jacobiComodulusk k)) ∧
    HasDerivAt (fun w => jacobiNck w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiNck w k) (I * k) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiNck w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiNck w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiNck w k) (0) (2 * (I * compEllIntKpk k)) := by
  sorry

/-- **Admitted.** Table 22.5.1, row `sc`: the `z`-derivative of `sc(z, k)` at the regular
special points and the residue at the poles. -/
@[dlmf 22.5.T1]
theorem jacobiSck_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiSck w k) (1) (0) ∧
    Tendsto (fun w => (w - (compEllIntKk k)) * jacobiSck w k) (𝓝[≠] (compEllIntKk k))
        (𝓝 (-1 / jacobiComodulusk k)) ∧
    HasDerivAt (fun w => jacobiSck w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiSck w k) (0) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiSck w k) (1) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiSck w k) (-1) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiSck w k) (-1) (2 * (I * compEllIntKpk k)) := by
  sorry

/-- **Admitted.** Table 22.5.1, row `ns`: the `z`-derivative of `ns(z, k)` at the regular
special points and the residue at the poles. -/
@[dlmf 22.5.T1]
theorem jacobiNsk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    Tendsto (fun w => (w - (0)) * jacobiNsk w k) (𝓝[≠] (0))
        (𝓝 (1)) ∧
    HasDerivAt (fun w => jacobiNsk w k) (0) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiNsk w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiNsk w k) (k) (I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k)) * jacobiNsk w k) (𝓝[≠] (2 * compEllIntKk k))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) * jacobiNsk w k)
        (𝓝[≠] (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * (I * compEllIntKpk k))) * jacobiNsk w k)
        (𝓝[≠] (2 * (I * compEllIntKpk k)))
        (𝓝 (1)) := by
  sorry

/-- **Admitted.** Table 22.5.1, row `ds`: the `z`-derivative of `ds(z, k)` at the regular
special points and the residue at the poles. -/
@[dlmf 22.5.T1]
theorem jacobiDsk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    Tendsto (fun w => (w - (0)) * jacobiDsk w k) (𝓝[≠] (0))
        (𝓝 (1)) ∧
    HasDerivAt (fun w => jacobiDsk w k) (0) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiDsk w k) (I * k * jacobiComodulusk k)
        (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiDsk w k) (0) (I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k)) * jacobiDsk w k) (𝓝[≠] (2 * compEllIntKk k))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) * jacobiDsk w k)
        (𝓝[≠] (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)))
        (𝓝 (1)) ∧
    Tendsto (fun w => (w - (2 * (I * compEllIntKpk k))) * jacobiDsk w k)
        (𝓝[≠] (2 * (I * compEllIntKpk k)))
        (𝓝 (-1)) := by
  sorry

/-- **Admitted.** Table 22.5.1, row `cs`: the `z`-derivative of `cs(z, k)` at the regular
special points and the residue at the poles. -/
@[dlmf 22.5.T1]
theorem jacobiCsk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    Tendsto (fun w => (w - (0)) * jacobiCsk w k) (𝓝[≠] (0))
        (𝓝 (1)) ∧
    HasDerivAt (fun w => jacobiCsk w k) (-jacobiComodulusk k) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiCsk w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiCsk w k) (0) (I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k)) * jacobiCsk w k) (𝓝[≠] (2 * compEllIntKk k))
        (𝓝 (1)) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) * jacobiCsk w k)
        (𝓝[≠] (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * (I * compEllIntKpk k))) * jacobiCsk w k)
        (𝓝[≠] (2 * (I * compEllIntKpk k)))
        (𝓝 (-1)) := by
  sorry

/-- **Admitted.** Table 22.5.2: `sn`, `cn`, `dn` at `z = K/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (compEllIntKk k / 2) k = (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) ∧
      jacobiCnk (compEllIntKk k / 2) k = (jacobiComodulusk k / (1 + jacobiComodulusk k)) ^
          (1 / 2 : ℂ) ∧
      jacobiDnk (compEllIntKk k / 2) k = jacobiComodulusk k ^ (1 / 2 : ℂ) := by
  sorry

/-- **Admitted.** Table 22.5.2: `sn`, `cn`, `dn` at `z = (K + iK')/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfKKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k =
        ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiCnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k = (1 - I) * jacobiComodulusk k ^
          (1 / 2 : ℂ) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiDnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k = (1 - I) / 2 * jacobiComodulusk k ^
          (1 / 2 : ℂ) * ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) := by
  sorry

/-- **Admitted.** Table 22.5.2: `sn`, `cn`, `dn` at `z = iK'/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (I * compEllIntKpk k / 2) k = I * k ^ (-(1 / 2) : ℂ) ∧
      jacobiCnk (I * compEllIntKpk k / 2) k = (1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ) ∧
      jacobiDnk (I * compEllIntKpk k / 2) k = (1 + k) ^ (1 / 2 : ℂ) := by
  sorry

/-- **Admitted.** Table 22.5.2: `sn`, `cn`, `dn` at `z = 3K/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (3 * compEllIntKk k / 2) k = (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) ∧
      jacobiCnk (3 * compEllIntKk k / 2) k = -(jacobiComodulusk k / (1 + jacobiComodulusk k)) ^
          (1 / 2 : ℂ) ∧
      jacobiDnk (3 * compEllIntKk k / 2) k = jacobiComodulusk k ^ (1 / 2 : ℂ) := by
  sorry

/-- **Admitted.** Table 22.5.2: `sn`, `cn`, `dn` at `z = 3(K + iK')/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfKKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (3 * (compEllIntKk k + I * compEllIntKpk k) / 2) k =
        ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiCnk (3 * (compEllIntKk k + I * compEllIntKpk k) / 2) k = (1 - I) * jacobiComodulusk k ^
          (1 / 2 : ℂ) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiDnk (3 * (compEllIntKk k + I * compEllIntKpk k) / 2) k = (I - 1) / 2 * jacobiComodulusk
          k ^ (1 / 2 : ℂ) * ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) := by
  sorry

/-- **Admitted.** Table 22.5.2: `sn`, `cn`, `dn` at `z = 3iK'/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (3 * (I * compEllIntKpk k) / 2) k = -(I * k ^ (-(1 / 2) : ℂ)) ∧
      jacobiCnk (3 * (I * compEllIntKpk k) / 2) k = -((1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ)) ∧
      jacobiDnk (3 * (I * compEllIntKpk k) / 2) k = -(1 + k) ^ (1 / 2 : ℂ) := by
  sorry

/-- **Admitted.** Table T3: `sn(z, k) → Complex.sin z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiSnk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiSnk z k) (𝓝[>] 0) (𝓝 (Complex.sin z)) := by
  sorry

/-- **Admitted.** Table T3: `cd(z, k) → Complex.cos z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiCdk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiCdk z k) (𝓝[>] 0) (𝓝 (Complex.cos z)) := by
  sorry

/-- **Admitted.** Table T3: `dc(z, k) → (Complex.cos z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiDck_zero (z : ℂ) (hz : Complex.cos z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDck z k) (𝓝[>] 0) (𝓝 ((Complex.cos z)⁻¹)) := by
  sorry

/-- **Admitted.** Table T3: `ns(z, k) → (Complex.sin z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiNsk_zero (z : ℂ) (hz : Complex.sin z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNsk z k) (𝓝[>] 0) (𝓝 ((Complex.sin z)⁻¹)) := by
  sorry

/-- **Admitted.** Table T3: `cn(z, k) → Complex.cos z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiCnk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiCnk z k) (𝓝[>] 0) (𝓝 (Complex.cos z)) := by
  sorry

/-- **Admitted.** Table T3: `sd(z, k) → Complex.sin z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiSdk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiSdk z k) (𝓝[>] 0) (𝓝 (Complex.sin z)) := by
  sorry

/-- **Admitted.** Table T3: `nc(z, k) → (Complex.cos z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiNck_zero (z : ℂ) (hz : Complex.cos z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNck z k) (𝓝[>] 0) (𝓝 ((Complex.cos z)⁻¹)) := by
  sorry

/-- **Admitted.** Table T3: `ds(z, k) → (Complex.sin z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiDsk_zero (z : ℂ) (hz : Complex.sin z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDsk z k) (𝓝[>] 0) (𝓝 ((Complex.sin z)⁻¹)) := by
  sorry

/-- **Admitted.** Table T3: `dn(z, k) → 1` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiDnk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiDnk z k) (𝓝[>] 0) (𝓝 (1)) := by
  sorry

/-- **Admitted.** Table T3: `nd(z, k) → 1` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiNdk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiNdk z k) (𝓝[>] 0) (𝓝 (1)) := by
  sorry

/-- **Admitted.** Table T3: `sc(z, k) → Complex.tan z` as real `k → 0+`, away from the poles of the
limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiSck_zero (z : ℂ) (hz : Complex.cos z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiSck z k) (𝓝[>] 0) (𝓝 (Complex.tan z)) := by
  sorry

/-- **Admitted.** Table T3: `cs(z, k) → Complex.cot z` as real `k → 0+`, away from the poles of the
limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiCsk_zero (z : ℂ) (hz : Complex.sin z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiCsk z k) (𝓝[>] 0) (𝓝 (Complex.cot z)) := by
  sorry

/-- **Admitted.** Table T4: `sn(z, k) → Complex.tanh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiSnk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiSnk z k) (𝓝[<] 1) (𝓝 (Complex.tanh z)) := by
  sorry

/-- **Admitted.** Table T4: `cd(z, k) → 1` as real `k → 1-`, away from the poles of the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiCdk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiCdk z k) (𝓝[<] 1) (𝓝 (1)) := by
  sorry

/-- **Admitted.** Table T4: `dc(z, k) → 1` as real `k → 1-`, away from the poles of the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiDck_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDck z k) (𝓝[<] 1) (𝓝 (1)) := by
  sorry

/-- **Admitted.** Table T4: `ns(z, k) → (Complex.tanh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiNsk_one (z : ℂ) (hz : Complex.sinh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNsk z k) (𝓝[<] 1) (𝓝 ((Complex.tanh z)⁻¹)) := by
  sorry

/-- **Admitted.** Table T4: `cn(z, k) → (Complex.cosh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiCnk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiCnk z k) (𝓝[<] 1) (𝓝 ((Complex.cosh z)⁻¹)) := by
  sorry

/-- **Admitted.** Table T4: `sd(z, k) → Complex.sinh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiSdk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiSdk z k) (𝓝[<] 1) (𝓝 (Complex.sinh z)) := by
  sorry

/-- **Admitted.** Table T4: `nc(z, k) → Complex.cosh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiNck_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNck z k) (𝓝[<] 1) (𝓝 (Complex.cosh z)) := by
  sorry

/-- **Admitted.** Table T4: `ds(z, k) → (Complex.sinh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiDsk_one (z : ℂ) (hz : Complex.sinh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDsk z k) (𝓝[<] 1) (𝓝 ((Complex.sinh z)⁻¹)) := by
  sorry

/-- **Admitted.** Table T4: `dn(z, k) → (Complex.cosh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiDnk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDnk z k) (𝓝[<] 1) (𝓝 ((Complex.cosh z)⁻¹)) := by
  sorry

/-- **Admitted.** Table T4: `nd(z, k) → Complex.cosh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiNdk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNdk z k) (𝓝[<] 1) (𝓝 (Complex.cosh z)) := by
  sorry

/-- **Admitted.** Table T4: `sc(z, k) → Complex.sinh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiSck_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiSck z k) (𝓝[<] 1) (𝓝 (Complex.sinh z)) := by
  sorry

/-- **Admitted.** Table T4: `cs(z, k) → (Complex.sinh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiCsk_one (z : ℂ) (hz : Complex.sinh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiCsk z k) (𝓝[<] 1) (𝓝 ((Complex.sinh z)⁻¹)) := by
  sorry

/-- §22.5(ii): `K(k) → π/2` as real `k → 0+`. -/
@[dlmf 22.5.ii]
theorem tendsto_compEllIntKk_zero :
    Tendsto (fun k : ℝ => compEllIntKk k) (𝓝[>] 0) (𝓝 (π / 2)) := by
  have hc : ContinuousAt (fun k : ℝ => (Real.compEllIntKm (k ^ 2) : ℂ)) 0 := by
    refine Complex.continuous_ofReal.continuousAt.comp ?_
    have h1 : ContinuousAt Real.compEllIntKm ((0 : ℝ) ^ 2) :=
      Real.continuousAt_compEllIntKm (by norm_num)
    exact h1.comp (f := fun k : ℝ => k ^ 2) (continuous_pow 2).continuousAt
  have h := hc.tendsto
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Real.compEllIntKm_zero,
    ofReal_div, ofReal_ofNat] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
  rw [compEllIntKk_ofReal (by nlinarith [hk.1, hk.2])]

/-- §22.5(ii): `K'(k) → π/2` as real `k → 1-`. -/
@[dlmf 22.5.ii]
theorem tendsto_compEllIntKpk_one :
    Tendsto (fun k : ℝ => compEllIntKpk k) (𝓝[<] 1) (𝓝 (π / 2)) := by
  have hc : ContinuousAt (fun k : ℝ => (Real.compEllIntKm (1 - k ^ 2) : ℂ)) 1 := by
    refine Complex.continuous_ofReal.continuousAt.comp ?_
    have h1 : ContinuousAt Real.compEllIntKm (1 - (1 : ℝ) ^ 2) :=
      Real.continuousAt_compEllIntKm (by norm_num)
    exact h1.comp (f := fun k : ℝ => 1 - k ^ 2)
        (continuous_const.sub (continuous_pow 2)).continuousAt
  have h := hc.tendsto
  simp only [one_pow, sub_self, Real.compEllIntKm_zero, ofReal_div, ofReal_ofNat] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
  rw [compEllIntKpk_ofReal (by nlinarith [hk.1, hk.2])]

/-- **Admitted.** §22.5(ii): `K'(k) → ∞` as real `k → 0+`. -/
@[dlmf 22.5.ii]
theorem tendsto_norm_compEllIntKpk_zero :
    Tendsto (fun k : ℝ => ‖compEllIntKpk k‖) (𝓝[>] 0) Filter.atTop := by
  sorry

/-- **Admitted.** §22.5(ii): `K(k) → ∞` as real `k → 1-`. -/
@[dlmf 22.5.ii]
theorem tendsto_norm_compEllIntKk_one :
    Tendsto (fun k : ℝ => ‖compEllIntKk k‖) (𝓝[<] 1) Filter.atTop := by
  sorry


end DLMF.JacobiElliptic
