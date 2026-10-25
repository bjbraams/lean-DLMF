/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.PeriodsPolesZeros
public import DLMF.JacobiElliptic.Derivatives
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Jacobian elliptic functions: special values (DLMF §22.5)

The values in Table 22.5.1 follow from the values at `z = 0` (`θ₁(0) = 0`, nonvanishing theta
constants) and the shift Table 22.4.3; they are proved (in the modulus form, via the inversion
22.2.2). The derivatives and residues of Table 22.5.1 are proved from the derivatives of
Table 22.13.1 at `z = 0` and the shift Table 22.4.3. The values at quarter- and
three-quarter-periods of Table 22.5.2 are proved: their squares follow from Table 22.4.3 and
the addition theorem, and the principal square roots are selected by the identity theorem in
`k` from the real case `0 < k < 1` (via the real bridges `jacobiSnk_ofReal` etc., proved here
by ODE uniqueness); the `iK'/2` values use Jacobi's imaginary transformation. The limits
`K(k) → ∞`, `K'(k) → ∞` (§22.5(ii)) are proved from `K(1 - δ²) ≥ log(π/(2δ))/√2`. The limiting
forms of Table 22.5.3 (`k → 0+`) are proved from `Im τ(k) → ∞`, `πz/(2K) → z` and the
limits of the normalized theta functions (dominated convergence of the theta series); those of
Table 22.5.4 (`k → 1-`) follow from them by Jacobi's imaginary transformation.

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

/-! ### Derivatives and residues at the special points (helpers) -/

lemma p22R1_hasDerivAt_shift {f g : ℂ → ℂ} {c p g' : ℂ} (hfg : ∀ z, f (z + p) = c * g z)
    (hg : HasDerivAt g g' 0) : HasDerivAt f (c * g') p := by
  have hf : f = fun w => c * g (w - p) := funext fun w => by rw [← hfg, sub_add_cancel]
  rw [hf]
  have hg' : HasDerivAt g g' (p - p) := by rwa [sub_self]
  exact (hg'.comp_sub_const p p).const_mul c

lemma p22R1_residue_shift {f s : ℂ → ℂ} {c p : ℂ} (hfs : ∀ z, f (z + p) = c * (1 / s z))
    (hs : HasDerivAt s 1 0) (hs0 : s 0 = 0) :
    Tendsto (fun w => (w - p) * f w) (𝓝[≠] p) (𝓝 c) := by
  have h1 := hs.tendsto_slope_zero
  simp only [zero_add, hs0, sub_zero, smul_eq_mul] at h1
  have h2 : Tendsto (fun t => t * (1 / s t)) (𝓝[≠] 0) (𝓝 1) := by
    have := h1.inv₀ one_ne_zero
    simp only [inv_one] at this
    refine this.congr fun t => ?_
    rw [mul_inv, inv_inv, one_div]
  have h3 : Tendsto (fun w => w - p) (𝓝[≠] p) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_sub_right p).tendsto p)
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw using sub_ne_zero.mpr hw
  have h4 := (h2.comp h3).const_mul c
  rw [mul_one] at h4
  refine h4.congr fun w => ?_
  have := hfs (w - p)
  rw [sub_add_cancel] at this
  simp only [Function.comp_apply, this]
  ring

lemma p22R1_reg0 {k : ℂ} (hk : k ∈ jacobiModulusDomain) {q : JacobiLetter} (hq : q ≠ .s) :
    jacobiLetterTheta q (jacobiZetak 0 k) (jacobiTauk k) ≠ 0 := by
  have : jacobiZetak 0 k = 0 := by simp [jacobiZetak]
  rw [this, je22a_letterTheta_zero (jacobiTauk_im_pos hk)]
  simp [hq]

/-- Table 22.5.1, row `sn`: the `z`-derivative of `sn(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiSnk (z + (0)) k = 1 * jacobiSnk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiSnk (z + (compEllIntKk k)) k = 1 * jacobiCdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiSnk_shift hk z).1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiSnk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        ((k)⁻¹) * jacobiDck z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiSnk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiSnk (z + (I * compEllIntKpk k)) k = ((k)⁻¹) * jacobiNsk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiSnk_shift hk z).2.2.1]
    have hfs : ∀ z, jacobiSnk (z + (I * compEllIntKpk k)) k = ((k)⁻¹) * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiSnk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiSnk (z + (2 * compEllIntKk k)) k = -1 * jacobiSnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiSnk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiSnk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiSnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiSnk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiSnk (z + (2 * (I * compEllIntKpk k))) k = 1 * jacobiSnk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiSnk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])

/-- Table 22.5.1, row `cn`: the `z`-derivative of `cn(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiCnk (z + (0)) k = 1 * jacobiCnk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiCnk (z + (compEllIntKk k)) k = (-jacobiComodulusk k) * jacobiSdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiCnk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiCnk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I * jacobiComodulusk k / k)) * jacobiNck z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiCnk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiCnk (z + (I * compEllIntKpk k)) k = (-(I / k)) * jacobiDsk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiCnk_shift hk z).2.2.1]
    have hfs : ∀ z, jacobiCnk (z + (I * compEllIntKpk k)) k = (-(I / k)) * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCnk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiCnk (z + (2 * compEllIntKk k)) k = -1 * jacobiCnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiCnk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiCnk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        1 * jacobiCnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiCnk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiCnk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiCnk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiCnk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])

/-- Table 22.5.1, row `dn`: the `z`-derivative of `dn(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiDnk (z + (0)) k = 1 * jacobiDnk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiDnk (z + (compEllIntKk k)) k = (jacobiComodulusk k) * jacobiNdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiDnk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiDnk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (I * jacobiComodulusk k) * jacobiSck z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiDnk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiDnk (z + (I * compEllIntKpk k)) k = (-I) * jacobiCsk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiDnk_shift hk z).2.2.1]
    have hfs : ∀ z, jacobiDnk (z + (I * compEllIntKpk k)) k = (-I) * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDnk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDnk (z + (2 * compEllIntKk k)) k = 1 * jacobiDnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiDnk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiDnk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiDnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiDnk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiDnk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiDnk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiDnk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])

/-- Table 22.5.1, row `cd`: the `z`-derivative of `cd(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiCdk (z + (0)) k = 1 * jacobiCdk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiCdk (z + (compEllIntKk k)) k = -1 * jacobiSnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiCdk_shift hk z).1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiCdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(k)⁻¹) * jacobiNsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiCdk_shift hk z).2.1]
    have hfs : ∀ z, jacobiCdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(k)⁻¹) * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCdk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCdk (z + (I * compEllIntKpk k)) k = ((k)⁻¹) * jacobiDck z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiCdk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiCdk (z + (2 * compEllIntKk k)) k = -1 * jacobiCdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiCdk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiCdk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiCdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiCdk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiCdk (z + (2 * (I * compEllIntKpk k))) k = 1 * jacobiCdk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiCdk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])

/-- Table 22.5.1, row `sd`: the `z`-derivative of `sd(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiSdk (z + (0)) k = 1 * jacobiSdk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiSdk (z + (compEllIntKk k)) k = ((jacobiComodulusk k)⁻¹) * jacobiCnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiSdk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiSdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I / (k * jacobiComodulusk k))) * jacobiDsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiSdk_shift hk z).2.1]
    have hfs : ∀ z, jacobiSdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I / (k * jacobiComodulusk k))) * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiSdk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiSdk (z + (I * compEllIntKpk k)) k = ((I / k)) * jacobiNck z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiSdk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiSdk (z + (2 * compEllIntKk k)) k = -1 * jacobiSdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiSdk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiSdk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        1 * jacobiSdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiSdk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiSdk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiSdk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiSdk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])

/-- Table 22.5.1, row `nd`: the `z`-derivative of `nd(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiNdk (z + (0)) k = 1 * jacobiNdk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiNdk (z + (compEllIntKk k)) k = ((jacobiComodulusk k)⁻¹) * jacobiDnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiNdk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiNdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I / jacobiComodulusk k)) * jacobiCsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiNdk_shift hk z).2.1]
    have hfs : ∀ z, jacobiNdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I / jacobiComodulusk k)) * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNdk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiNdk (z + (I * compEllIntKpk k)) k = (I) * jacobiSck z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiNdk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiNdk (z + (2 * compEllIntKk k)) k = 1 * jacobiNdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiNdk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiNdk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiNdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiNdk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiNdk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiNdk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiNdk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])

/-- Table 22.5.1, row `dc`: the `z`-derivative of `dc(z, k)` at the regular
special points and the residue at the poles (proved). Corrected from the printed DLMF formula: the
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiDck (z + (0)) k = 1 * jacobiDck z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiDck (z + (compEllIntKk k)) k = -1 * jacobiNsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiDck_shift hk z).1]
        try ring
    have hfs : ∀ z, jacobiDck (z + (compEllIntKk k)) k = -1 * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDck w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDck (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-k) * jacobiSnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiDck_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiDck (z + (I * compEllIntKpk k)) k = (k) * jacobiCdk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiDck_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiDck (z + (2 * compEllIntKk k)) k = -1 * jacobiDck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiDck_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiDck (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiDck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiDck_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiDck (z + (2 * (I * compEllIntKpk k))) k = 1 * jacobiDck z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiDck_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])

/-- Table 22.5.1, row `nc`: the `z`-derivative of `nc(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiNck (z + (0)) k = 1 * jacobiNck z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiNck (z + (compEllIntKk k)) k =
        (-(jacobiComodulusk k)⁻¹) * jacobiDsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiNck_shift hk z).1]
    have hfs : ∀ z, jacobiNck (z + (compEllIntKk k)) k =
        (-(jacobiComodulusk k)⁻¹) * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNck w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiNck (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        ((I * k / jacobiComodulusk k)) * jacobiCnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiNck_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiNck (z + (I * compEllIntKpk k)) k = (I * k) * jacobiSdk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiNck_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiNck (z + (2 * compEllIntKk k)) k = -1 * jacobiNck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiNck_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiNck (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        1 * jacobiNck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiNck_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiNck (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiNck z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiNck_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])

/-- Table 22.5.1, row `sc`: the `z`-derivative of `sc(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiSck (z + (0)) k = 1 * jacobiSck z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiSck (z + (compEllIntKk k)) k =
        (-(jacobiComodulusk k)⁻¹) * jacobiCsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiSck_shift hk z).1]
    have hfs : ∀ z, jacobiSck (z + (compEllIntKk k)) k =
        (-(jacobiComodulusk k)⁻¹) * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiSck w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiSck (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        ((I / jacobiComodulusk k)) * jacobiDnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiSck_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiSck (z + (I * compEllIntKpk k)) k = (I) * jacobiNdk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiSck_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiSck (z + (2 * compEllIntKk k)) k = 1 * jacobiSck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiSck_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiSck (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiSck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiSck_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiSck (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiSck z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiSck_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])

/-- Table 22.5.1, row `ns`: the `z`-derivative of `ns(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiNsk (z + (0)) k = 1 * jacobiNsk z k :=
      fun z => by rw [add_zero, one_mul]
    have hfs : ∀ z, jacobiNsk (z + (0)) k = 1 * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNsk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiNsk (z + (compEllIntKk k)) k = 1 * jacobiDck z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiNsk_shift hk z).1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNsk w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiNsk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (k) * jacobiCdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiNsk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNsk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiNsk (z + (I * compEllIntKpk k)) k = (k) * jacobiSnk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiNsk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNsk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiNsk (z + (2 * compEllIntKk k)) k = -1 * jacobiNsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiNsk_shift hk z).2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiNsk (z + (2 * compEllIntKk k)) k = -1 * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNsk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiNsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiNsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiNsk_shift hk z).2.2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiNsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNsk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiNsk (z + (2 * (I * compEllIntKpk k))) k = 1 * jacobiNsk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiNsk_shift hk z).2.2.2.2.2]
        try ring
    have hfs : ∀ z, jacobiNsk (z + (2 * (I * compEllIntKpk k))) k = 1 * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNsk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2

/-- Table 22.5.1, row `ds`: the `z`-derivative of `ds(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiDsk (z + (0)) k = 1 * jacobiDsk z k :=
      fun z => by rw [add_zero, one_mul]
    have hfs : ∀ z, jacobiDsk (z + (0)) k = 1 * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDsk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDsk (z + (compEllIntKk k)) k = (jacobiComodulusk k) * jacobiNck z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiDsk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDsk w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiDsk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (I * k * jacobiComodulusk k) * jacobiSdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiDsk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDsk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiDsk (z + (I * compEllIntKpk k)) k = (-(I * k)) * jacobiCnk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiDsk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDsk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiDsk (z + (2 * compEllIntKk k)) k = -1 * jacobiDsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiDsk_shift hk z).2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiDsk (z + (2 * compEllIntKk k)) k = -1 * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDsk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        1 * jacobiDsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiDsk_shift hk z).2.2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiDsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        1 * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDsk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDsk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiDsk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiDsk_shift hk z).2.2.2.2.2]
        try ring
    have hfs : ∀ z, jacobiDsk (z + (2 * (I * compEllIntKpk k))) k = -1 * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDsk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2

/-- Table 22.5.1, row `cs`: the `z`-derivative of `cs(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiCsk (z + (0)) k = 1 * jacobiCsk z k :=
      fun z => by rw [add_zero, one_mul]
    have hfs : ∀ z, jacobiCsk (z + (0)) k = 1 * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCsk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCsk (z + (compEllIntKk k)) k = (-jacobiComodulusk k) * jacobiSck z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiCsk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCsk w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiCsk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I * jacobiComodulusk k)) * jacobiNdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiCsk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCsk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiCsk (z + (I * compEllIntKpk k)) k = (-I) * jacobiDnk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiCsk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCsk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiCsk (z + (2 * compEllIntKk k)) k = 1 * jacobiCsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiCsk_shift hk z).2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiCsk (z + (2 * compEllIntKk k)) k = 1 * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCsk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiCsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiCsk_shift hk z).2.2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiCsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCsk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCsk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiCsk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiCsk_shift hk z).2.2.2.2.2]
        try ring
    have hfs : ∀ z, jacobiCsk (z + (2 * (I * compEllIntKpk k))) k = -1 * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCsk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2

/-! ### Real bridges (DLMF 22.2.4–22.2.6 on the real line)

For `0 < k < 1` and real `u`, the theta-quotient `sn, cn, dn` agree with the amplitude-based
`Real.jacobiSnm, Real.jacobiCnm, Real.jacobiDnm` of parameter `m = k²`: both triples solve
`s' = cd, c' = -sd, d' = -k²sc` with `(s, c, d)(0) = (0, 1, 1)`, so they agree by ODE
uniqueness (`ODE_solution_unique_of_mem_Ioo`). (Moved here from `Basic`.) -/

/-- For real `0 < k < 1`, the complex `sn, cn, dn` have no pole on the real line. -/
lemma p22R1_reg_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiLetterTheta .n (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
  have hk := p22R1_ofReal_mem hk0 hk1
  have hτ := jacobiTauk_im_pos hk
  have hK := compEllIntKk_ofReal (k := k) (by nlinarith)
  have hKpos : 0 < Real.compEllIntKm (k ^ 2) := Real.compEllIntKm_pos (by nlinarith)
  have hz : jacobiZetak u k = ((u / (2 * Real.compEllIntKm (k ^ 2)) : ℝ) : ℂ) * π := by
    rw [jacobiZetak, hK]; push_cast; field_simp
  rw [hz, jacobiLetterTheta]
  exact div_ne_zero (p22R1_theta_real_ne hτ _).1 (by simpa using (p22R1_theta_real_ne hτ 0).1)

open Set in
/-- Joint real-line identification of the complex and real `sn, cn, dn` (ODE uniqueness). -/
theorem p22R1_ofReal_all {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiSnk u k = (Real.jacobiSnm u (k ^ 2) : ℂ) ∧
      jacobiCnk u k = (Real.jacobiCnm u (k ^ 2) : ℂ) ∧
      jacobiDnk u k = (Real.jacobiDnm u (k ^ 2) : ℂ) := by
  have hk := p22R1_ofReal_mem hk0 hk1
  have hm : k ^ 2 < 1 := by nlinarith
  set f : ℝ → ℂ × ℂ × ℂ := fun t => (jacobiSnk t k, jacobiCnk t k, jacobiDnk t k) with hf
  set g : ℝ → ℂ × ℂ × ℂ := fun t =>
    ((Real.jacobiSnm t (k ^ 2) : ℂ), (Real.jacobiCnm t (k ^ 2) : ℂ),
      (Real.jacobiDnm t (k ^ 2) : ℂ)) with hg
  set v : ℝ → ℂ × ℂ × ℂ → ℂ × ℂ × ℂ := fun _ x =>
    (x.2.1 * x.2.2, -(x.1 * x.2.2), -((k : ℂ) ^ 2 * x.1 * x.2.1)) with hv
  have hf' : ∀ t : ℝ, HasDerivAt f (v t (f t)) t := fun t => by
    have hz := p22R1_reg_real hk0 hk1 t
    exact ((hasDerivAt_jacobiSnk hk hz).comp_ofReal).prodMk
      (((hasDerivAt_jacobiCnk hk hz).comp_ofReal).prodMk
        ((hasDerivAt_jacobiDnk hk hz).comp_ofReal))
  have hg' : ∀ t : ℝ, HasDerivAt g (v t (g t)) t := fun t => by
    have h1 := (Real.hasDerivAt_jacobiSnm hm t).ofReal_comp
    have h2 := (Real.hasDerivAt_jacobiCnm hm t).ofReal_comp
    have h3 := (Real.hasDerivAt_jacobiDnm hm t).ofReal_comp
    refine (HasDerivAt.prodMk h1 (HasDerivAt.prodMk h2 h3)).congr_deriv ?_
    simp only [hv, hg]; push_cast; rfl
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf' t).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg' t).continuousAt
  set a : ℝ := -(|u| + 1)
  set b : ℝ := |u| + 1
  obtain ⟨Rf, hRf⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hfc.continuousOn
  obtain ⟨Rg, hRg⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hgc.continuousOn
  set R := max Rf Rg
  have hvL : LocallyLipschitz (v 0) := by
    apply ContDiff.locallyLipschitz (𝕂 := ℝ)
    simp only [hv]; fun_prop
  obtain ⟨L, hL⟩ := (hvL.locallyLipschitzOn (s := Metric.closedBall 0 R)).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall 0 R)
  have h0 : f 0 = g 0 := by
    simp only [hf, hg, ofReal_zero, jacobiSnk_zero hk, jacobiCnk_zero hk, jacobiDnk_zero hk,
      Real.jacobiSnm, Real.jacobiCnm, Real.jacobiDnm, Real.jacobiAmm_zero hm]
    norm_num
  have hu : u ∈ Ioo a b := ⟨by simp only [a]; linarith [neg_abs_le u], by
    simp only [b]; linarith [le_abs_self u]⟩
  have key := ODE_solution_unique_of_mem_Ioo (v := v) (s := fun _ => Metric.closedBall 0 R)
    (K := L) (a := a) (b := b) (t₀ := 0) (fun t _ => hL)
    ⟨by simp only [a]; linarith [abs_nonneg u], by simp only [b]; linarith [abs_nonneg u]⟩
    (fun t ht => ⟨hf' t, mem_closedBall_zero_iff.mpr ((hRf t (Ioo_subset_Icc_self ht)).trans
      (le_max_left _ _))⟩)
    (fun t ht => ⟨hg' t, mem_closedBall_zero_iff.mpr ((hRg t (Ioo_subset_Icc_self ht)).trans
      (le_max_right _ _))⟩) h0 hu
  simp only [hf, hg, Prod.mk.injEq] at key
  exact key

/-- Bridge to the real-variable `sn` (defined through the amplitude):
for `0 < k < 1` and real `u`, `sn(u, k) = Real.jacobiSnm u (k²)`. -/
@[dlmf 22.2.E4 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiSnk_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiSnk u k = (Real.jacobiSnm u (k ^ 2) : ℂ) :=
  (p22R1_ofReal_all hk0 hk1 u).1

/-- Bridge to the real-variable `cn`: for `0 < k < 1` and real `u`,
`cn(u, k) = Real.jacobiCnm u (k²)`. -/
@[dlmf 22.2.E5 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiCnk_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiCnk u k = (Real.jacobiCnm u (k ^ 2) : ℂ) :=
  (p22R1_ofReal_all hk0 hk1 u).2.1

/-- Bridge to the real-variable `dn`: for `0 < k < 1` and real `u`,
`dn(u, k) = Real.jacobiDnm u (k²)`. -/
@[dlmf 22.2.E6 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiDnk_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiDnk u k = (Real.jacobiDnm u (k ^ 2) : ℂ) :=
  (p22R1_ofReal_all hk0 hk1 u).2.2

lemma p22R1_re_cpow_half_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w ^ (1 / 2 : ℂ)).re :=
  p22R1_re_sqrt_pos (Or.inl hw)

lemma p22R1_re_cpow_neg_half_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w ^ (-(1 / 2) : ℂ)).re := by
  rw [cpow_neg, inv_re]
  have h := p22R1_re_cpow_half_pos hw
  exact div_pos h (normSq_pos.mpr fun h0 => by rw [h0] at h; simp at h)

lemma p22R1_re_div_one_add_pos {a : ℂ} (ha : 0 < a.re) : 0 < (a / (1 + a)).re := by
  have h1 : (1 + a) ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  rw [div_re]
  have hn : 0 < normSq (1 + a) := normSq_pos.mpr h1
  have : a.re * (1 + a).re / normSq (1 + a) + a.im * (1 + a).im / normSq (1 + a) =
      (a.re * (1 + a.re) + a.im * a.im) / normSq (1 + a) := by
    simp only [add_re, one_re, add_im, one_im, zero_add]; ring
  rw [this]
  exact div_pos (by nlinarith [mul_self_nonneg a.im]) hn

lemma p22R1_cpow_neg_half_sq (w : ℂ) : (w ^ (-(1 / 2) : ℂ)) ^ 2 = w⁻¹ := by
  rw [cpow_neg, inv_pow, p22R1_sqrt_sq]

lemma p22R1_comodulus_re_pos {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    0 < (jacobiComodulusk k).re := (p22R1_comodulus_mem hk).1

lemma p22R1_differentiableAt_comodulus {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    DifferentiableAt ℂ jacobiComodulusk k := by
  have hk' := hk
  rw [p22R1_domain_eq] at hk'
  exact (by fun_prop : DifferentiableAt ℂ (fun k : ℂ => 1 - k ^ 2) k).cpow_const hk'.2

/-- Square-root branch selection by the identity theorem. -/
lemma p22R1_branch {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f jacobiModulusDomain)
    (hg : DifferentiableOn ℂ g jacobiModulusDomain)
    (hsq : ∀ x : ℝ, 0 < x → x < 1 → f x ^ 2 = g x ^ 2)
    (hfr : ∀ x : ℝ, 0 < x → x < 1 → 0 < (f x).re)
    (hgr : ∀ x : ℝ, 0 < x → x < 1 → 0 < (g x).re) : Set.EqOn f g jacobiModulusDomain := by
  refine p22R1_eqOn_of_real hf hg fun x h0 h1 => ?_
  have h : (f x - g x) * (f x + g x) = 0 := by linear_combination hsq x h0 h1
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg re h
    simp only [add_re, zero_re] at this
    linarith [hfr x h0 h1, hgr x h0 h1]

/-- Composition of Glaisher's quotient at a constant real theta argument with `τ(k)`. -/
lemma p22R1_differentiableOn_glaisher_const (p q : JacobiLetter) (c : ℂ)
    (hq : ∀ τ : ℂ, 0 < τ.im → jacobiLetterTheta q c τ ≠ 0) :
    DifferentiableOn ℂ (fun k => jacobiGlaisher p q c (jacobiTauk k)) jacobiModulusDomain := by
  refine p22R1_differentiableOn_comp fun τ hτ => ?_
  have hl : ∀ r : JacobiLetter, DifferentiableAt ℂ (fun σ => jacobiLetterTheta r c σ) τ :=
    fun r => (p22R1_differentiableAt_letterTheta r (x := (c, τ)) hτ).comp τ
      (f := fun σ : ℂ => (c, σ)) (by fun_prop)
  unfold jacobiGlaisher
  by_cases hpq : p = q
  · simp only [hpq, ↓reduceIte]; exact differentiableAt_const _
  · simp only [hpq, ↓reduceIte]; exact (hl p).div (hl q) (hq τ hτ)

lemma p22R1_zeta_halfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiZetak (compEllIntKk k / 2) k = ((1 / 4 : ℝ) : ℂ) * π := by
  have := compEllIntKk_ne_zero hk
  rw [jacobiZetak]; push_cast; field_simp; ring

lemma p22R1_theta_quarter_ne {τ : ℂ} (hτ : 0 < τ.im) (r : JacobiLetter) :
    jacobiLetterTheta r (((1 / 4 : ℝ) : ℂ) * π) τ ≠ 0 := by
  obtain ⟨h4, h3, h1⟩ := p22R1_theta_real_ne hτ (1 / 4)
  have n2 := je22a_thetaTwo_zero_ne_zero hτ
  have n3 := je22a_thetaThree_zero_ne_zero hτ
  have n4 := je22a_thetaFour_zero_ne_zero hτ
  have hnz : ∀ m : ℤ, (1 / 4 : ℝ) ≠ m := by
    intro m hm
    have h1 : (0 : ℝ) < m := by rw [← hm]; norm_num
    have h2 : (m : ℝ) < 1 := by rw [← hm]; norm_num
    have : (0 : ℤ) < m := by exact_mod_cast h1
    have : m < 1 := by exact_mod_cast h2
    omega
  have hnz' : ∀ m : ℤ, (-(1 / 4) : ℝ) ≠ m := by
    intro m hm
    have h1 : (-1 : ℝ) < m := by rw [← hm]; norm_num
    have h2 : (m : ℝ) < 0 := by rw [← hm]; norm_num
    have : (-1 : ℤ) < m := by exact_mod_cast h1
    have : m < 0 := by exact_mod_cast h2
    omega
  cases r <;> simp only [jacobiLetterTheta]
  · exact mul_ne_zero (div_ne_zero n3 (mul_ne_zero n2 n4)) (h1 hnz)
  · refine div_ne_zero ?_ n2
    have h := (p22R1_theta_real_ne hτ (-(1 / 4))).2.2 hnz'
    have e : jacobiThetaOneTau (((-(1 / 4) : ℝ) : ℂ) * π) τ =
        -jacobiThetaTwoTau (((1 / 4 : ℝ) : ℂ) * π) τ := by
      rw [jacobiThetaOneTau]; congr 2; push_cast; ring
    rw [e] at h; exact fun h' => h (by rw [h', neg_zero])
  · exact div_ne_zero h3 n3
  · exact div_ne_zero h4 n4

lemma p22R1_amm_strictMono {m : ℝ} (hm : m < 1) : StrictMono fun u => Real.jacobiAmm u m := by
  simp only [Real.jacobiAmm, hm, ↓reduceDIte]
  exact (Real.incEllIntFmOrderIso hm).symm.strictMono

/-- The values at `K/2` up to the choice of square roots. -/
lemma p22R1_halfK_alg {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiDnk (compEllIntKk k / 2) k ^ 2 = jacobiComodulusk k ∧
      jacobiSnk (compEllIntKk k / 2) k ^ 2 * (1 + jacobiComodulusk k) = 1 ∧
      jacobiCnk (compEllIntKk k / 2) k =
        jacobiSnk (compEllIntKk k / 2) k * jacobiDnk (compEllIntKk k / 2) k := by
  have hτ := jacobiTauk_im_pos hk
  set u := compEllIntKk k / 2 with hu
  have hreg : ∀ r, jacobiRegulark r u k := fun r => by
    unfold jacobiRegulark; rw [hu, p22R1_zeta_halfK hk]; exact p22R1_theta_quarter_ne hτ r
  have hd : jacobiDnk u k ≠ 0 := jacobiPQk_ne_zero (by decide) (hreg .d) (hreg .n)
  have hm : -u + compEllIntKk k = u := by rw [hu]; ring
  have e1 := (jacobiSnk_shift hk (-u)).1
  have e3 := (jacobiDnk_shift hk (-u)).1
  rw [hm] at e1 e3
  rw [jacobiCdk, jacobiPQk_neg, ← jacobiCdk] at e1
  rw [jacobiNdk, jacobiPQk_neg, ← jacobiNdk] at e3
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, decide_true, not_true_eq_false,
    ↓reduceIte, Bool.not_eq_true, eq_self_iff_true] at e1 e3
  obtain ⟨-, -, -, -, -, -, hsd, hcd, hnd⟩ := je22a_glaisher_via_n (hreg .n)
  rw [hcd] at e1; rw [hnd] at e3
  obtain ⟨hsc, -⟩ := jacobi_sq_sum hk (hreg .n)
  have hdd : jacobiDnk u k ^ 2 = jacobiComodulusk k := by
    field_simp at e3; linear_combination e3
  refine ⟨hdd, ?_, ?_⟩
  · field_simp at e1
    have hc : jacobiCnk u k = jacobiSnk u k * jacobiDnk u k := by linear_combination -e1
    rw [hc] at hsc
    linear_combination hsc - jacobiSnk u k ^ 2 * hdd
  · field_simp at e1; linear_combination -e1

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = K/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (compEllIntKk k / 2) k = (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) ∧
      jacobiCnk (compEllIntKk k / 2) k = (jacobiComodulusk k / (1 + jacobiComodulusk k)) ^
          (1 / 2 : ℂ) ∧
      jacobiDnk (compEllIntKk k / 2) k = jacobiComodulusk k ^ (1 / 2 : ℂ) := by
  -- holomorphy of the three left-hand sides
  have hL : ∀ p q : JacobiLetter, q ≠ .s → DifferentiableOn ℂ
      (fun k => jacobiPQk p q (compEllIntKk k / 2) k) jacobiModulusDomain := by
    intro p q _
    refine (p22R1_differentiableOn_glaisher_const p q _
      fun τ hτ => p22R1_theta_quarter_ne hτ q).congr fun k hk => ?_
    simp only [jacobiPQk, p22R1_zeta_halfK hk]
  have hkd : DifferentiableOn ℂ jacobiComodulusk jacobiModulusDomain := fun k hk =>
    (p22R1_differentiableAt_comodulus hk).differentiableWithinAt
  have hslit : ∀ {w : ℂ}, 0 < w.re → w ∈ slitPlane := fun h => Or.inl h
  have h1re : ∀ k ∈ jacobiModulusDomain, 0 < (1 + jacobiComodulusk k).re := fun k hk => by
    simp only [add_re, one_re]; linarith [p22R1_comodulus_re_pos hk]
  -- real positivity of the left-hand sides
  have hreal : ∀ x : ℝ, 0 < x → x < 1 → ∀ p : JacobiLetter, p ≠ .s → ∀ q : JacobiLetter,
      jacobiPQk q .n (compEllIntKk x / 2) x = jacobiPQk q .n
        ((Real.compEllIntKm (x ^ 2) / 2 : ℝ) : ℂ) x := by
    intro x h0 h1 _ _ q
    rw [compEllIntKk_ofReal (by nlinarith)]; push_cast; rfl
  have hm : ∀ x : ℝ, 0 < x → x < 1 → x ^ 2 < 1 := fun x h0 h1 => by nlinarith
  have hamm : ∀ x : ℝ, 0 < x → x < 1 →
      0 < Real.jacobiAmm (Real.compEllIntKm (x ^ 2) / 2) (x ^ 2) ∧
        Real.jacobiAmm (Real.compEllIntKm (x ^ 2) / 2) (x ^ 2) < π / 2 := by
    intro x h0 h1
    have hK := Real.compEllIntKm_pos (hm x h0 h1)
    have a := p22R1_amm_strictMono (hm x h0 h1) (show 0 < Real.compEllIntKm (x ^ 2) / 2 by
      positivity)
    have b := p22R1_amm_strictMono (hm x h0 h1)
      (show Real.compEllIntKm (x ^ 2) / 2 < Real.compEllIntKm (x ^ 2) by linarith)
    simp only [Real.jacobiAmm_zero (hm x h0 h1), Real.jacobiAmm_compEllIntKm (hm x h0 h1)] at a b
    exact ⟨a, b⟩
  refine ⟨?_, ?_, ?_⟩
  · refine p22R1_branch (f := fun k => jacobiSnk (compEllIntKk k / 2) k)
      (g := fun k => (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ)) (hL .s .n (by decide))
      ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · intro k hk
      exact ((hkd k hk).const_add 1).cpow_const (hslit (h1re k hk))
        |>.differentiableAt (p22R1_isOpen_domain.mem_nhds hk) |>.differentiableWithinAt
    · have h := (p22R1_halfK_alg (p22R1_ofReal_mem h0 h1)).2.1
      have hne : (1 + jacobiComodulusk x) ≠ 0 := fun h' => by
        have := h1re x (p22R1_ofReal_mem h0 h1); rw [h'] at this; simp at this
      rw [p22R1_cpow_neg_half_sq]
      field_simp
      linear_combination h
    · simp only [jacobiSnk]
      rw [hreal x h0 h1 .c (by decide) .s, ← jacobiSnk, jacobiSnk_ofReal h0 h1, ofReal_re,
        Real.jacobiSnm]
      exact Real.sin_pos_of_pos_of_lt_pi (hamm x h0 h1).1 (by linarith [(hamm x h0 h1).2,
        Real.pi_pos])
    · exact p22R1_re_cpow_neg_half_pos (h1re x (p22R1_ofReal_mem h0 h1))
  · have hne : ∀ k ∈ jacobiModulusDomain, (1 + jacobiComodulusk k) ≠ 0 := fun k hk h' => by
      have := h1re k hk; rw [h'] at this; simp at this
    refine p22R1_branch (f := fun k => jacobiCnk (compEllIntKk k / 2) k)
      (g := fun k => (jacobiComodulusk k / (1 + jacobiComodulusk k)) ^ (1 / 2 : ℂ))
      (hL .c .n (by decide)) ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · intro k hk
      exact ((hkd k hk).div ((hkd k hk).const_add 1) (hne k hk)).cpow_const
        (hslit (p22R1_re_div_one_add_pos (p22R1_comodulus_re_pos hk)))
        |>.differentiableAt (p22R1_isOpen_domain.mem_nhds hk) |>.differentiableWithinAt
    · obtain ⟨hd, hs, hc⟩ := p22R1_halfK_alg (p22R1_ofReal_mem h0 h1)
      have hn := hne x (p22R1_ofReal_mem h0 h1)
      rw [p22R1_sqrt_sq, hc, mul_pow, hd]
      field_simp
      linear_combination jacobiComodulusk x * hs
    · simp only [jacobiCnk]
      rw [hreal x h0 h1 .c (by decide) .c, ← jacobiCnk, jacobiCnk_ofReal h0 h1, ofReal_re,
        Real.jacobiCnm]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [(hamm x h0 h1).1, Real.pi_pos],
        (hamm x h0 h1).2⟩
    · exact p22R1_re_cpow_half_pos (p22R1_re_div_one_add_pos
        (p22R1_comodulus_re_pos (p22R1_ofReal_mem h0 h1)))
  · refine p22R1_branch (f := fun k => jacobiDnk (compEllIntKk k / 2) k)
      (g := fun k => jacobiComodulusk k ^ (1 / 2 : ℂ))
      (hL .d .n (by decide)) ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · intro k hk
      exact (hkd k hk).cpow_const (hslit (p22R1_comodulus_re_pos hk))
        |>.differentiableAt (p22R1_isOpen_domain.mem_nhds hk) |>.differentiableWithinAt
    · rw [p22R1_sqrt_sq]; exact (p22R1_halfK_alg (p22R1_ofReal_mem h0 h1)).1
    · simp only [jacobiDnk]
      rw [hreal x h0 h1 .c (by decide) .d, ← jacobiDnk, jacobiDnk_ofReal h0 h1, ofReal_re]
      exact Real.jacobiDnm_pos (hm x h0 h1) _
    · exact p22R1_re_cpow_half_pos (p22R1_comodulus_re_pos (p22R1_ofReal_mem h0 h1))

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = 3K/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (3 * compEllIntKk k / 2) k = (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) ∧
      jacobiCnk (3 * compEllIntKk k / 2) k = -(jacobiComodulusk k / (1 + jacobiComodulusk k)) ^
          (1 / 2 : ℂ) ∧
      jacobiDnk (3 * compEllIntKk k / 2) k = jacobiComodulusk k ^ (1 / 2 : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := jacobi_specialValues_HalfK hk
  have e : 3 * compEllIntKk k / 2 = -(compEllIntKk k / 2) + 2 * compEllIntKk k := by ring
  rw [e, (jacobiSnk_shift hk _).2.2.2.1, (jacobiCnk_shift hk _).2.2.2.1,
    (jacobiDnk_shift hk _).2.2.2.1, jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk_neg,
    jacobiPQk_neg, jacobiPQk_neg, ← jacobiSnk, ← jacobiCnk, ← jacobiDnk, h1, h2, h3]
  simp

/-- `|Im a| < Re a` (argument in `(-π/4, π/4)`). -/
def p22R1_Good (a : ℂ) : Prop := |a.im| < a.re

lemma p22R1_good_sqrt {w : ℂ} (hw : 0 < w.re) : p22R1_Good (w ^ (1 / 2 : ℂ)) := by
  have h := p22R1_sqrt_sq w
  have hr := p22R1_re_cpow_half_pos hw
  set a := w ^ (1 / 2 : ℂ)
  have : w.re = a.re ^ 2 - a.im ^ 2 := by rw [← h]; simp [pow_two]
  unfold p22R1_Good
  rw [abs_lt]; constructor <;> nlinarith

lemma p22R1_good_inv {a : ℂ} (ha : p22R1_Good a) : p22R1_Good a⁻¹ := by
  unfold p22R1_Good at *
  have h0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hn := normSq_pos.mpr h0
  rw [inv_re, inv_im, neg_div, abs_neg, abs_div, abs_of_pos hn]
  exact div_lt_div_of_pos_right ha hn

lemma p22R1_good_re {a : ℂ} (ha : p22R1_Good a) : 0 < a.re :=
  lt_of_le_of_lt (abs_nonneg _) ha

lemma p22R1_good_mul_re {a b : ℂ} (ha : p22R1_Good a) (hb : p22R1_Good b) : 0 < (a * b).re := by
  unfold p22R1_Good at ha hb
  rw [mul_re]
  have := abs_mul a.im b.im
  have h1 : a.im * b.im ≤ |a.im| * |b.im| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : |a.im| * |b.im| < a.re * b.re := mul_lt_mul'' ha hb (abs_nonneg _) (abs_nonneg _)
  linarith

/-- Uniqueness of a square root with positive real part. -/
lemma p22R1_sq_eq_of_re {a b : ℂ} (h : a ^ 2 = b ^ 2) (ha : 0 < a.re) (hb : 0 < b.re) :
    a = b := by
  have h' : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h' | h'
  · exact sub_eq_zero.mp h'
  · have := congrArg re h'; simp only [add_re, zero_re] at this; linarith

lemma p22R1_comodulus_comodulus {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiComodulusk (jacobiComodulusk k) = k := by
  have hsl : k ^ 2 ∈ slitPlane := by
    rcases p22R1_sq_of_mem_domain hk with h | ⟨-, h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  rw [jacobiComodulusk, jacobiComodulusk_sq, sub_sub_cancel]
  exact p22R1_sq_eq_of_re (p22R1_sqrt_sq _) (p22R1_re_sqrt_pos hsl) hk.1

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = iK'/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (I * compEllIntKpk k / 2) k = I * k ^ (-(1 / 2) : ℂ) ∧
      jacobiCnk (I * compEllIntKpk k / 2) k = (1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ) ∧
      jacobiDnk (I * compEllIntKpk k / 2) k = (1 + k) ^ (1 / 2 : ℂ) := by
  have hk' := p22R1_comodulus_mem hk
  have hkk := p22R1_comodulus_comodulus hk
  obtain ⟨s1, c1, d1⟩ := jacobi_specialValues_HalfK hk'
  rw [hkk] at s1 c1 d1
  have hτ' := jacobiTauk_im_pos hk'
  have hreg : jacobiRegulark .n (compEllIntKk (jacobiComodulusk k) / 2) (jacobiComodulusk k) := by
    unfold jacobiRegulark; rw [p22R1_zeta_halfK hk']; exact p22R1_theta_quarter_ne hτ' _
  obtain ⟨-, -, -, hsc, hdc, hnc, -, -, -⟩ := je22a_glaisher_via_n hreg
  obtain ⟨t1, t2, t3, -⟩ := jacobi_imaginary_transformation hk
    (compEllIntKk (jacobiComodulusk k) / 2)
  have e : I * compEllIntKpk k / 2 = I * (compEllIntKk (jacobiComodulusk k) / 2) := by
    rw [p22R1_K_comodulus]; ring
  rw [e, t1, t2, t3, hsc, hdc, hnc, s1, c1, d1]
  have hk0 : k ≠ 0 := fun h => by have := hk.1; rw [h] at this; simp at this
  have hre1 : 0 < (1 + k).re := by simp only [add_re, one_re]; linarith [hk.1]
  have h1k : 1 + k ≠ 0 := fun h => by rw [h] at hre1; simp at hre1
  have hq := p22R1_re_div_one_add_pos hk.1
  have gS : p22R1_Good ((1 + k) ^ (-(1 / 2) : ℂ)) := by
    rw [cpow_neg]; exact p22R1_good_inv (p22R1_good_sqrt hre1)
  have gC := p22R1_good_sqrt hq
  have gCi := p22R1_good_inv gC
  have gK : p22R1_Good (k ^ (-(1 / 2) : ℂ)) := by
    rw [cpow_neg]; exact p22R1_good_inv (p22R1_good_sqrt hk.1)
  refine ⟨?_, ?_, ?_⟩
  · congr 1
    refine p22R1_sq_eq_of_re ?_ (by rw [div_eq_mul_inv]; exact p22R1_good_mul_re gS gCi)
      (p22R1_good_re gK)
    rw [div_pow, p22R1_cpow_neg_half_sq, p22R1_sqrt_sq, p22R1_cpow_neg_half_sq]
    field_simp
  · refine p22R1_sq_eq_of_re ?_ (by rw [one_div]; exact p22R1_good_re gCi)
      (p22R1_good_mul_re (p22R1_good_sqrt hre1) gK)
    rw [div_pow, mul_pow, p22R1_cpow_neg_half_sq, p22R1_sqrt_sq, p22R1_sqrt_sq]
    field_simp
  · have hr : 0 < (k ^ (1 / 2 : ℂ) / (k / (1 + k)) ^ (1 / 2 : ℂ)).re := by
      rw [div_eq_mul_inv]; exact p22R1_good_mul_re (p22R1_good_sqrt hk.1) gCi
    refine p22R1_sq_eq_of_re ?_ hr (p22R1_re_cpow_half_pos hre1)
    rw [div_pow, p22R1_sqrt_sq, p22R1_sqrt_sq, p22R1_sqrt_sq]
    field_simp

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = 3iK'/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (3 * (I * compEllIntKpk k) / 2) k = -(I * k ^ (-(1 / 2) : ℂ)) ∧
      jacobiCnk (3 * (I * compEllIntKpk k) / 2) k = -((1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ)) ∧
      jacobiDnk (3 * (I * compEllIntKpk k) / 2) k = -(1 + k) ^ (1 / 2 : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := jacobi_specialValues_HalfKp hk
  have e : 3 * (I * compEllIntKpk k) / 2 = -(I * compEllIntKpk k / 2) +
      2 * (I * compEllIntKpk k) := by ring
  rw [e, (jacobiSnk_shift hk _).2.2.2.2.2, (jacobiCnk_shift hk _).2.2.2.2.2,
    (jacobiDnk_shift hk _).2.2.2.2.2, jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk_neg,
    jacobiPQk_neg, jacobiPQk_neg, ← jacobiSnk, ← jacobiCnk, ← jacobiDnk, h1, h2, h3]
  simp

lemma p22R1_theta4_ne {τ : ℂ} (hτ : 0 < τ.im) (a b : ℝ) (hb : ∀ n : ℤ, b ≠ n + 1 / 2) :
    jacobiThetaFourTau (((a : ℂ) + b * τ) * π) τ ≠ 0 := by
  rw [Ne, (DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ _).2.2.2]
  rintro ⟨m, n, h⟩
  have h' : ((a - m : ℝ) : ℂ) + ((b - (n + 1 / 2) : ℝ) : ℂ) * τ = 0 := by
    have := mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) h
    push_cast; linear_combination this
  have := DLMF.Theta.th20_lattice_eq_zero hτ (a := a - m) (b := b - (n + 1 / 2))
    (by rw [h', zero_mul])
  exact hb n (by linarith [this.2])

lemma p22R1_reg_halfKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiRegulark .n (I * compEllIntKpk k / 2) k := by
  have hτ := jacobiTauk_im_pos hk
  have hK := compEllIntKk_ne_zero hk
  unfold jacobiRegulark
  have hz : jacobiZetak (I * compEllIntKpk k / 2) k =
      (((0 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * jacobiTauk k) * π := by
    rw [jacobiZetak, jacobiTauk]; push_cast; field_simp; ring
  rw [hz, jacobiLetterTheta]
  refine div_ne_zero (p22R1_theta4_ne hτ 0 (1 / 4) fun n h => ?_)
    (je22a_thetaFour_zero_ne_zero hτ)
  have h1 : (4 * n + 1 : ℝ) = 0 := by linarith
  have h2 : (4 * n + 1 : ℤ) = 0 := by exact_mod_cast h1
  omega

lemma p22R1_reg_halfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) (r : JacobiLetter) :
    jacobiRegulark r (compEllIntKk k / 2) k := by
  unfold jacobiRegulark; rw [p22R1_zeta_halfK hk]
  exact p22R1_theta_quarter_ne (jacobiTauk_im_pos hk) r

/-- `k + k' ≠ -1`, so `1 + k + k' ≠ 0`. -/
lemma p22R1_one_add_add_ne {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    1 + k + jacobiComodulusk k ≠ 0 := fun h => by
  have := congrArg re h
  simp only [add_re, one_re, zero_re] at this
  linarith [hk.1, p22R1_comodulus_re_pos hk]

/-- Positive reals. -/
def p22R1_PR (a : ℂ) : Prop := a.im = 0 ∧ 0 < a.re

lemma p22R1_PR_mul {a b : ℂ} (ha : p22R1_PR a) (hb : p22R1_PR b) : p22R1_PR (a * b) := by
  unfold p22R1_PR at *; simp [mul_re, mul_im, ha.1, hb.1, mul_pos ha.2 hb.2]

lemma p22R1_PR_add {a b : ℂ} (ha : p22R1_PR a) (hb : p22R1_PR b) : p22R1_PR (a + b) := by
  unfold p22R1_PR at *; simp [ha.1, hb.1]; linarith [ha.2, hb.2]

lemma p22R1_PR_inv {a : ℂ} (ha : p22R1_PR a) : p22R1_PR a⁻¹ := by
  unfold p22R1_PR at *
  have h0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  refine ⟨by simp [inv_im, ha.1], ?_⟩
  rw [inv_re]; exact div_pos ha.2 (normSq_pos.mpr h0)

lemma p22R1_PR_div {a b : ℂ} (ha : p22R1_PR a) (hb : p22R1_PR b) : p22R1_PR (a / b) := by
  rw [div_eq_mul_inv]; exact p22R1_PR_mul ha (p22R1_PR_inv hb)

lemma p22R1_PR_cpow {a : ℂ} (ha : p22R1_PR a) (c : ℝ) : p22R1_PR (a ^ (c : ℂ)) := by
  have e : a = (a.re : ℂ) := by apply Complex.ext <;> simp [ha.1]
  rw [e, ← ofReal_cpow ha.2.le]
  exact ⟨ofReal_im _, by rw [ofReal_re]; exact Real.rpow_pos_of_pos ha.2 _⟩

lemma p22R1_PR_one : p22R1_PR 1 := ⟨by simp, by simp⟩

lemma p22R1_PR_ofReal {x : ℝ} (hx : 0 < x) : p22R1_PR (x : ℂ) := ⟨ofReal_im _, by simpa⟩

lemma p22R1_PR_comodulus {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    p22R1_PR (jacobiComodulusk x) := by
  have : (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [jacobiComodulusk, this, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
  exact p22R1_PR_cpow (p22R1_PR_ofReal (by nlinarith)) _

lemma p22R1_PR_re_add_I_mul {a b : ℂ} (ha : p22R1_PR a) (hb : p22R1_PR b) :
    (a + I * b).re = a.re := by
  simp [hb.1]

/-- The values at `(K + iK')/2` from the addition theorem, in terms of the half-period values. -/
lemma p22R1_halfKKp_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    let κ := jacobiComodulusk k
    let S := (1 + κ) ^ (-(1 / 2) : ℂ)
    let Q := k ^ (-(1 / 2) : ℂ)
    let A := (1 + k) ^ (1 / 2 : ℂ)
    let D := κ ^ (1 / 2 : ℂ)
    jacobiSnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k =
        S * Q * (1 + k) * (1 + κ) / (1 + k + κ) + I * (S * Q * κ * (1 + κ) / (1 + k + κ)) ∧
      jacobiCnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k =
        S * D * A * Q * (1 + κ) / (1 + k + κ) - I * (S * D * A * Q * (1 + κ) / (1 + k + κ)) ∧
      jacobiDnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k =
        D * A * (1 + κ) / (1 + k + κ) - I * (D * A * k / (1 + k + κ)) := by
  intro κ S Q A D
  obtain ⟨s1, -, d1⟩ := jacobi_specialValues_HalfK hk
  obtain ⟨-, -, hc1⟩ := p22R1_halfK_alg hk
  obtain ⟨s2, c2, d2⟩ := jacobi_specialValues_HalfKp hk
  have hu := p22R1_reg_halfK hk .n
  have hv := p22R1_reg_halfKp hk
  have e : (compEllIntKk k + I * compEllIntKpk k) / 2 =
      compEllIntKk k / 2 + I * compEllIntKpk k / 2 := by ring
  have hk0 : k ≠ 0 := fun h => by have := hk.1; rw [h] at this; simp at this
  have hre1 : 0 < (1 + κ).re := by simp only [add_re, one_re]; linarith [p22R1_comodulus_re_pos hk]
  have h1κ : 1 + κ ≠ 0 := fun h => by rw [h] at hre1; simp at hre1
  have hSS : S ^ 2 * (1 + κ) = 1 := by
    simp only [S]; rw [p22R1_cpow_neg_half_sq]; field_simp
  have hQQ : Q ^ 2 * k = 1 := by simp only [Q]; rw [p22R1_cpow_neg_half_sq]; field_simp
  have hAA : A ^ 2 = 1 + k := p22R1_sqrt_sq _
  have hDD : D ^ 2 = κ := p22R1_sqrt_sq _
  have hκκ : κ ^ 2 = 1 - k ^ 2 := jacobiComodulusk_sq k
  have hI : I ^ 2 = -1 := I_sq
  have h3 := p22R1_one_add_add_ne hk
  have s1' : jacobiSnk (compEllIntKk k / 2) k = S := s1
  have d1' : jacobiDnk (compEllIntKk k / 2) k = D := d1
  have s2' : jacobiSnk (I * compEllIntKpk k / 2) k = I * Q := s2
  have c2' : jacobiCnk (I * compEllIntKpk k / 2) k = A * Q := c2
  have d2' : jacobiDnk (I * compEllIntKpk k / 2) k = A := d2
  rw [s1', d1'] at hc1
  have hden0 : (1 - k ^ 2 * S ^ 2 * (I * Q) ^ 2) * (1 + κ) = 1 + k + κ := by
    linear_combination (-k ^ 2 * Q ^ 2 * I ^ 2) * hSS - k ^ 2 * Q ^ 2 * hI + k * hQQ
  have hden : 1 - k ^ 2 * jacobiSnk (compEllIntKk k / 2) k ^ 2 *
      jacobiSnk (I * compEllIntKpk k / 2) k ^ 2 ≠ 0 := by
    rw [s1', s2']; intro h; rw [h, zero_mul] at hden0; exact h3 hden0.symm
  rw [e, jacobiSnk_add hk hu hv hden, jacobiCnk_add hk hu hv hden, jacobiDnk_add hk hu hv hden,
    s1', d1', hc1, s2', c2', d2']
  have hd2 : 1 - k ^ 2 * S ^ 2 * (I * Q) ^ 2 = (1 + k + κ) / (1 + κ) := by
    rw [← hden0]; field_simp
  rw [hd2]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    rw [hAA, hDD]
  · field_simp
  · field_simp
    rw [div_left_inj' h3]
    linear_combination (-D * A * k ^ 2 * I * Q ^ 2) * hSS - D * A * k * I * hQQ

lemma p22R1_PR_half {a : ℂ} (ha : p22R1_PR a) :
    p22R1_PR (a ^ (1 / 2 : ℂ)) ∧ p22R1_PR (a ^ (-(1 / 2) : ℂ)) := by
  constructor
  · rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]; exact p22R1_PR_cpow ha _
  · rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring]; exact p22R1_PR_cpow ha _

/-- Real data at a real modulus `0 < x < 1`. -/
lemma p22R1_real_atoms {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    let κ := jacobiComodulusk x
    p22R1_PR (x : ℂ) ∧ p22R1_PR κ ∧ p22R1_PR ((1 + κ) ^ (-(1 / 2) : ℂ)) ∧
      p22R1_PR ((x : ℂ) ^ (-(1 / 2) : ℂ)) ∧ p22R1_PR ((1 + (x : ℂ)) ^ (1 / 2 : ℂ)) ∧
      p22R1_PR (κ ^ (1 / 2 : ℂ)) ∧ p22R1_PR ((1 - (x : ℂ)) ^ (1 / 2 : ℂ)) ∧
      p22R1_PR ((2 * (x : ℂ)) ^ (1 / 2 : ℂ)) ∧
      (1 + (x : ℂ)) ^ (1 / 2 : ℂ) * (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = κ := by
  intro κ
  have hx := p22R1_PR_ofReal h0
  have hκ := p22R1_PR_comodulus h0 h1
  have h1x : p22R1_PR (1 + (x : ℂ)) := p22R1_PR_add p22R1_PR_one hx
  have h1mx : p22R1_PR (1 - (x : ℂ)) := by
    rw [show (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
    exact p22R1_PR_ofReal (by linarith)
  have h2x : p22R1_PR (2 * (x : ℂ)) := by
    rw [show (2 * (x : ℂ)) = ((2 * x : ℝ) : ℂ) by push_cast; ring]
    exact p22R1_PR_ofReal (by linarith)
  refine ⟨hx, hκ, (p22R1_PR_half (p22R1_PR_add p22R1_PR_one hκ)).2, (p22R1_PR_half hx).2,
    (p22R1_PR_half h1x).1, (p22R1_PR_half hκ).1, (p22R1_PR_half h1mx).1,
    (p22R1_PR_half h2x).1, ?_⟩
  refine p22R1_sq_eq_of_re ?_ (p22R1_PR_mul (p22R1_PR_half h1x).1 (p22R1_PR_half h1mx).1).2 hκ.2
  rw [mul_pow, p22R1_sqrt_sq, p22R1_sqrt_sq, jacobiComodulusk_sq]; ring

lemma p22R1_re_add_I_mul' {a b : ℂ} (hb : b.im = 0) : (a + I * b).re = a.re := by simp [hb]

lemma p22R1_re_sub_I_mul' {a b : ℂ} (hb : b.im = 0) : (a - I * b).re = a.re := by simp [hb]

lemma p22R1_diffOn_cpow {h : ℂ → ℂ} (c : ℂ)
    (hd : ∀ k ∈ jacobiModulusDomain, DifferentiableAt ℂ h k)
    (hs : ∀ k ∈ jacobiModulusDomain, h k ∈ slitPlane) :
    DifferentiableOn ℂ (fun k => h k ^ c) jacobiModulusDomain := fun k hk =>
  ((hd k hk).cpow_const (hs k hk)).differentiableWithinAt

lemma p22R1_one_sub_slit {k : ℂ} (hk : k ∈ jacobiModulusDomain) : 1 - k ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : k.im = 0
  · left; simp only [sub_re, one_re]; linarith [hk.2 h]
  · right; simpa using h

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = (K + iK')/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfKKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k =
        ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiCnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k = (1 - I) * jacobiComodulusk k ^
          (1 / 2 : ℂ) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiDnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k = (1 - I) / 2 * jacobiComodulusk k ^
          (1 / 2 : ℂ) * ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) := by
  obtain ⟨e1, e2, e3⟩ := p22R1_halfKKp_add hk
  rw [e1, e2, e3]
  have Dom := jacobiModulusDomain
  -- differentiability of the building blocks
  have dκ : ∀ k ∈ jacobiModulusDomain, DifferentiableAt ℂ jacobiComodulusk k :=
    fun k hk => p22R1_differentiableAt_comodulus hk
  have slit_re : ∀ {w : ℂ}, 0 < w.re → w ∈ slitPlane := fun h => Or.inl h
  have re1κ : ∀ k ∈ jacobiModulusDomain, 0 < (1 + jacobiComodulusk k).re := fun k hk => by
    simp only [add_re, one_re]; linarith [p22R1_comodulus_re_pos hk]
  have re1k : ∀ k ∈ jacobiModulusDomain, 0 < (1 + k).re := fun k hk => by
    simp only [add_re, one_re]; linarith [hk.1]
  have re2k : ∀ k ∈ jacobiModulusDomain, 0 < (2 * k).re := fun k hk => by
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith [hk.1]
  have dS := p22R1_diffOn_cpow (h := fun k => 1 + jacobiComodulusk k) (-(1 / 2))
    (fun k hk => (dκ k hk).const_add 1) fun k hk => slit_re (re1κ k hk)
  have dQ := p22R1_diffOn_cpow (h := fun k => k) (-(1 / 2))
    (fun k _ => differentiableAt_id) fun k hk => slit_re hk.1
  have dA := p22R1_diffOn_cpow (h := fun k => 1 + k) (1 / 2)
    (fun k _ => differentiableAt_id.const_add 1) fun k hk => slit_re (re1k k hk)
  have dD := p22R1_diffOn_cpow (h := jacobiComodulusk) (1 / 2) dκ
    fun k hk => slit_re (p22R1_comodulus_re_pos hk)
  have dB := p22R1_diffOn_cpow (h := fun k => 1 - k) (1 / 2)
    (fun k _ => (differentiableAt_const _).sub differentiableAt_id) fun k hk => p22R1_one_sub_slit hk
  have dC := p22R1_diffOn_cpow (h := fun k => 2 * k) (1 / 2)
    (fun k _ => differentiableAt_id.const_mul 2) fun k hk => slit_re (re2k k hk)
  have dK : DifferentiableOn ℂ jacobiComodulusk jacobiModulusDomain :=
    fun k hk => (dκ k hk).differentiableWithinAt
  have dId : DifferentiableOn ℂ (fun k : ℂ => k) jacobiModulusDomain := differentiableOn_id
  have dN : DifferentiableOn ℂ (fun k => 1 + k + jacobiComodulusk k) jacobiModulusDomain :=
    (dId.const_add 1).add dK
  have hN := fun k (hk : k ∈ jacobiModulusDomain) => p22R1_one_add_add_ne hk
  have hC0 : ∀ k ∈ jacobiModulusDomain, (2 * k) ^ (1 / 2 : ℂ) ≠ 0 := fun k hk h => by
    have := p22R1_re_cpow_half_pos (re2k k hk); rw [h] at this; simp at this
  refine ⟨?_, ?_, ?_⟩
  · refine p22R1_branch
      (f := fun k => (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) * k ^ (-(1 / 2) : ℂ) * (1 + k) *
        (1 + jacobiComodulusk k) / (1 + k + jacobiComodulusk k) +
        I * ((1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) * k ^ (-(1 / 2) : ℂ) * jacobiComodulusk k *
        (1 + jacobiComodulusk k) / (1 + k + jacobiComodulusk k)))
      (g := fun k => ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) / (2 * k) ^ (1 / 2 : ℂ))
      ?_ ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · exact ((((dS.mul dQ).mul (dId.const_add 1)).mul (dK.const_add 1)).div dN hN).add
        (((((dS.mul dQ).mul dK).mul (dK.const_add 1)).div dN hN).const_mul I)
    · exact (dA.add (dB.const_mul I)).div dC hC0
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have hN0 := hN x (p22R1_ofReal_mem h0 h1)
      have hC00 := hC0 x (p22R1_ofReal_mem h0 h1)
      have hSS : ((1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ)) ^ 2 * (1 + jacobiComodulusk x) = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (fun h => by
          have := (p22R1_PR_add p22R1_PR_one hκ).2; rw [h] at this; simp at this)
      have hQQ : ((x : ℂ) ^ (-(1 / 2) : ℂ)) ^ 2 * x = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (by exact_mod_cast h0.ne')
      have hBB := p22R1_sqrt_sq (1 - (x : ℂ))
      have hCC := p22R1_sqrt_sq (2 * (x : ℂ))
      have hAA := p22R1_sqrt_sq (1 + (x : ℂ))
      have hκκ := jacobiComodulusk_sq (x : ℂ)
      have hI : I ^ 2 = -1 := I_sq
      generalize (1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ) = S at *
      generalize (x : ℂ) ^ (-(1 / 2) : ℂ) = Q at *
      generalize (1 + (x : ℂ)) ^ (1 / 2 : ℂ) = A at *
      generalize (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = B at *
      generalize (2 * (x : ℂ)) ^ (1 / 2 : ℂ) = C at *
      generalize jacobiComodulusk x = κ at *
      generalize (x : ℂ) = k at *
      field_simp
      linear_combination (-4*k^3*I+4*κ*k^2+4*κ*k*I-4*k^2*I+4*κ*k+4*k^2+4*κ*I+4*k*I+4*k+4*I) * hSS +
          (4*S^2*κ^3*k*I-2*S^2*κ^4+2*S^2*κ^2*k^2+4*S^2*κ^3*I+8*S^2*κ^2*k*I-4*S^2*κ^3+4*S^2*κ^2*k
            +4*S^2*κ*k^2+8*S^2*κ^2*I+4*S^2*κ*k*I+8*S^2*κ*k+2*S^2*k^2+4*S^2*κ*I+4*S^2*κ+4*S^2*k
              +2*S^2) * hQQ +
          (-2*κ*k-2*κ-2*k-2) * hAA +
          (2*κ*k+2*κ+2*k+2) * hBB +
          (2*S^2*Q^2*κ^3*k*I-S^2*Q^2*κ^4+S^2*Q^2*κ^2*k^2+2*S^2*Q^2*κ^3*I+4*S^2*Q^2*κ^2*k*I
            -2*S^2*Q^2*κ^3+2*S^2*Q^2*κ^2*k+2*S^2*Q^2*κ*k^2+4*S^2*Q^2*κ^2*I+2*S^2*Q^2*κ*k*I
              +4*S^2*Q^2*κ*k+S^2*Q^2*k^2+2*S^2*Q^2*κ*I+2*S^2*Q^2*κ+2*S^2*Q^2*k+S^2*Q^2) * hCC +
          (4*S^2*κ*k*I-2*S^2*κ^2+4*S^2*κ*I+4*S^2*k*I-4*S^2*κ+4*S^2*I-2*S^2-A^2+B^2-2*κ*I-4*k*I
            -4*I) * hκκ +
          (S^2*Q^2*C^2*κ^4+2*S^2*Q^2*C^2*κ^3+S^2*Q^2*C^2*κ^2-B^2*κ^2-2*B^2*κ*k-B^2*k^2-2*B^2*κ
            -2*B^2*k-B^2) * hI +
          (-2*κ^2*I-4*κ*k*I-2*k^2*I-4*κ*I-4*k*I-2*I) * hAB
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      rw [p22R1_re_add_I_mul' (p22R1_PR_div (p22R1_PR_mul (p22R1_PR_mul (p22R1_PR_mul hS hQ) hκ)
        (p22R1_PR_add p22R1_PR_one hκ)) (p22R1_PR_add (p22R1_PR_add p22R1_PR_one hx) hκ)).1]
      exact (p22R1_PR_div (p22R1_PR_mul (p22R1_PR_mul (p22R1_PR_mul hS hQ)
        (p22R1_PR_add p22R1_PR_one hx)) (p22R1_PR_add p22R1_PR_one hκ))
        (p22R1_PR_add (p22R1_PR_add p22R1_PR_one hx) hκ)).2
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      rw [add_div, mul_div_assoc, p22R1_re_add_I_mul' (p22R1_PR_div hB hC).1]
      exact (p22R1_PR_div hA hC).2
  · refine p22R1_branch
      (f := fun k => (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) * jacobiComodulusk k ^ (1 / 2 : ℂ) *
        (1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ) * (1 + jacobiComodulusk k) /
        (1 + k + jacobiComodulusk k) - I * ((1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) *
        jacobiComodulusk k ^ (1 / 2 : ℂ) * (1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ) *
        (1 + jacobiComodulusk k) / (1 + k + jacobiComodulusk k)))
      (g := fun k => (1 - I) * jacobiComodulusk k ^ (1 / 2 : ℂ) / (2 * k) ^ (1 / 2 : ℂ))
      ?_ ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · have h := (((((dS.mul dD).mul dA).mul dQ).mul (dK.const_add 1)).div dN hN)
      exact h.sub (h.const_mul I)
    · exact (dD.const_mul (1 - I)).div dC hC0
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have hN0 := hN x (p22R1_ofReal_mem h0 h1)
      have hC00 := hC0 x (p22R1_ofReal_mem h0 h1)
      have hSS : ((1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ)) ^ 2 * (1 + jacobiComodulusk x) = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (fun h => by
          have := (p22R1_PR_add p22R1_PR_one hκ).2; rw [h] at this; simp at this)
      have hQQ : ((x : ℂ) ^ (-(1 / 2) : ℂ)) ^ 2 * x = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (by exact_mod_cast h0.ne')
      have hBB := p22R1_sqrt_sq (1 - (x : ℂ))
      have hCC := p22R1_sqrt_sq (2 * (x : ℂ))
      have hAA := p22R1_sqrt_sq (1 + (x : ℂ))
      have hDD := p22R1_sqrt_sq (jacobiComodulusk x)
      have hκκ := jacobiComodulusk_sq (x : ℂ)
      have hI : I ^ 2 = -1 := I_sq
      generalize (1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ) = S at *
      generalize (x : ℂ) ^ (-(1 / 2) : ℂ) = Q at *
      generalize (1 + (x : ℂ)) ^ (1 / 2 : ℂ) = A at *
      generalize (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = B at *
      generalize (2 * (x : ℂ)) ^ (1 / 2 : ℂ) = C at *
      generalize jacobiComodulusk x ^ (1 / 2 : ℂ) = D at *
      generalize jacobiComodulusk x = κ at *
      generalize (x : ℂ) = k at *
      field_simp
      linear_combination (4*k^3*I-4*κ*k*I+4*k^2*I-4*κ*I-4*k*I-4*I) * hSS +
          (-4*S^2*A^2*κ^3*I-8*S^2*A^2*κ^2*I-4*S^2*A^2*κ*I) * hQQ +
          (4*S^2*κ*k^2*I+8*S^2*k^2*I-8*S^2*κ*I-8*S^2*I) * hAA +
          (-2*S^2*Q^2*A^2*κ^3*I-4*S^2*Q^2*A^2*κ^2*I-2*S^2*Q^2*A^2*κ*I) * hCC +
          (-2*S^2*Q^2*A^2*C^2*κ^2*I-4*S^2*Q^2*A^2*C^2*κ*I-2*S^2*Q^2*A^2*C^2*I+2*κ^2*I+4*κ*k*I
            +2*k^2*I+4*κ*I+4*k*I+2*I) * hDD +
          (-4*S^2*A^2*κ*I-8*S^2*A^2*I+4*S^2*k*I+4*S^2*I+2*κ*I+4*k*I+4*I) * hκκ +
          (S^2*Q^2*A^2*C^2*D^2*κ^2+2*S^2*Q^2*A^2*C^2*D^2*κ+S^2*Q^2*A^2*C^2*D^2-D^2*κ^2-2*D^2*κ*k
            -D^2*k^2-2*D^2*κ-2*D^2*k-D^2) * hI
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have h := p22R1_PR_div (p22R1_PR_mul (p22R1_PR_mul (p22R1_PR_mul (p22R1_PR_mul hS hD) hA) hQ)
        (p22R1_PR_add p22R1_PR_one hκ)) (p22R1_PR_add (p22R1_PR_add p22R1_PR_one hx) hκ)
      rw [p22R1_re_sub_I_mul' h.1]; exact h.2
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      rw [show ∀ a b : ℂ, (1 - I) * a / b = a / b - I * (a / b) from fun a b => by ring,
        p22R1_re_sub_I_mul' (p22R1_PR_div hD hC).1]
      exact (p22R1_PR_div hD hC).2
  · refine p22R1_branch
      (f := fun k => jacobiComodulusk k ^ (1 / 2 : ℂ) * (1 + k) ^ (1 / 2 : ℂ) *
        (1 + jacobiComodulusk k) / (1 + k + jacobiComodulusk k) -
        I * (jacobiComodulusk k ^ (1 / 2 : ℂ) * (1 + k) ^ (1 / 2 : ℂ) * k /
        (1 + k + jacobiComodulusk k)))
      (g := fun k => (1 - I) / 2 * jacobiComodulusk k ^ (1 / 2 : ℂ) *
        ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)))
      ?_ ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · exact ((((dD.mul dA).mul (dK.const_add 1)).div dN hN)).sub
        ((((dD.mul dA).mul dId).div dN hN).const_mul I)
    · exact (dD.const_mul ((1 - I) / 2)).mul (dA.add (dB.const_mul I))
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have hN0 := hN x (p22R1_ofReal_mem h0 h1)
      have hC00 := hC0 x (p22R1_ofReal_mem h0 h1)
      have hSS : ((1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ)) ^ 2 * (1 + jacobiComodulusk x) = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (fun h => by
          have := (p22R1_PR_add p22R1_PR_one hκ).2; rw [h] at this; simp at this)
      have hQQ : ((x : ℂ) ^ (-(1 / 2) : ℂ)) ^ 2 * x = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (by exact_mod_cast h0.ne')
      have hBB := p22R1_sqrt_sq (1 - (x : ℂ))
      have hCC := p22R1_sqrt_sq (2 * (x : ℂ))
      have hAA := p22R1_sqrt_sq (1 + (x : ℂ))
      have hDD := p22R1_sqrt_sq (jacobiComodulusk x)
      have hκκ := jacobiComodulusk_sq (x : ℂ)
      have hI : I ^ 2 = -1 := I_sq
      generalize (1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ) = S at *
      generalize (x : ℂ) ^ (-(1 / 2) : ℂ) = Q at *
      generalize (1 + (x : ℂ)) ^ (1 / 2 : ℂ) = A at *
      generalize (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = B at *
      generalize (2 * (x : ℂ)) ^ (1 / 2 : ℂ) = C at *
      generalize jacobiComodulusk x ^ (1 / 2 : ℂ) = D at *
      generalize jacobiComodulusk x = κ at *
      generalize (x : ℂ) = k at *
      field_simp
      linear_combination (4*k^3*I-8*κ*k^2-4*κ*k*I-4*k^2*I-8*k^2+4*κ*I-4*k*I+8*κ+4*I+8) * hAA +
          (4*k^3*I-4*κ*k*I+4*k^2*I-4*κ*I-4*k*I-4*I) * hBB +
          (2*A^2*κ^2*I-2*B^2*κ^2*I-4*A^2*κ*k*I-4*B^2*κ*k*I+2*A^2*k^2*I-2*B^2*k^2*I+4*A^2*κ^2
            -4*A*B*κ^2-8*A*B*κ*k-4*A^2*k^2-4*A*B*k^2+4*A^2*κ*I-4*B^2*κ*I-4*A^2*k*I-4*B^2*k*I
              +8*A^2*κ-8*A*B*κ-8*A*B*k+2*A^2*I-2*B^2*I+4*A^2-4*A*B) * hDD +
          (2*A^2*κ*I-2*B^2*κ*I-4*A^2*k*I-4*B^2*k*I+4*A^2*κ+4*A^2*I-4*B^2*I+8*A^2-4*κ^2-8*κ*k-8*κ
            -8*k-8) * hκκ +
          (-B^2*D^2*κ^2*I^2-2*B^2*D^2*κ*k*I^2-B^2*D^2*k^2*I^2-2*A*B*D^2*κ^2*I+2*B^2*D^2*κ^2*I
            -4*A*B*D^2*κ*k*I+4*B^2*D^2*κ*k*I-2*A*B*D^2*k^2*I+2*B^2*D^2*k^2*I-2*B^2*D^2*κ*I^2
              -2*B^2*D^2*k*I^2-A^2*D^2*κ^2+4*A*B*D^2*κ^2-2*A^2*D^2*κ*k+8*A*B*D^2*κ*k+3*A^2*D^2*k^2
                +4*A*B*D^2*k^2-4*A*B*D^2*κ*I+4*B^2*D^2*κ*I-4*A*B*D^2*k*I+4*B^2*D^2*k*I-B^2*D^2*I^2
                  -2*A^2*D^2*κ+8*A*B*D^2*κ-2*A^2*D^2*k+8*A*B*D^2*k-2*A*B*D^2*I+2*B^2*D^2*I-A^2*D^2
                    +4*A*B*D^2) * hI +
          (-4*κ^3-8*κ^2*k-4*κ*k^2-8*κ^2-8*κ*k-4*κ) * hAB
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have h := p22R1_PR_div (p22R1_PR_mul (p22R1_PR_mul hD hA) (p22R1_PR_add p22R1_PR_one hκ))
        (p22R1_PR_add (p22R1_PR_add p22R1_PR_one hx) hκ)
      have h' := p22R1_PR_div (p22R1_PR_mul (p22R1_PR_mul hD hA) hx)
        (p22R1_PR_add (p22R1_PR_add p22R1_PR_one hx) hκ)
      rw [p22R1_re_sub_I_mul' h'.1]; exact h.2
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have e : ∀ D A B : ℂ, (1 - I) / 2 * D * (A + I * B) = D * (A + B) / 2 + I * (D * (B - A) / 2) :=
        fun D A B => by linear_combination (-(D * B) / 2) * I_sq
      have h2 : p22R1_PR (2 : ℂ) := ⟨by simp, by norm_num⟩
      rw [e, p22R1_re_add_I_mul' (by simp only [div_ofNat_im, mul_im, sub_im, sub_re, hD.1, hA.1, hB.1]; ring)]
      exact (p22R1_PR_div (p22R1_PR_mul hD (p22R1_PR_add hA hB)) h2).2

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = 3(K + iK')/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfKKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (3 * (compEllIntKk k + I * compEllIntKpk k) / 2) k =
        ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiCnk (3 * (compEllIntKk k + I * compEllIntKpk k) / 2) k = (1 - I) * jacobiComodulusk k ^
          (1 / 2 : ℂ) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiDnk (3 * (compEllIntKk k + I * compEllIntKpk k) / 2) k = (I - 1) / 2 * jacobiComodulusk
          k ^ (1 / 2 : ℂ) * ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := jacobi_specialValues_HalfKKp hk
  have e : 3 * (compEllIntKk k + I * compEllIntKpk k) / 2 =
      -((compEllIntKk k + I * compEllIntKpk k) / 2) + 2 * compEllIntKk k +
        2 * (I * compEllIntKpk k) := by ring
  rw [e, (jacobiSnk_shift hk _).2.2.2.2.1, (jacobiCnk_shift hk _).2.2.2.2.1,
    (jacobiDnk_shift hk _).2.2.2.2.1, jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk_neg,
    jacobiPQk_neg, jacobiPQk_neg, ← jacobiSnk, ← jacobiCnk, ← jacobiDnk, h1, h2, h3]
  refine ⟨by simp, by simp, ?_⟩
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false, ↓reduceIte]
  ring































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

/-- Logarithmic lower bound `K(1 - δ²) ≥ log(π/(2δ))/√2` for `0 < δ < π/2`. -/
lemma p22R1_K_ge {δ : ℝ} (h0 : 0 < δ) (h1 : δ < π / 2) :
    Real.log (π / 2 / δ) / √2 ≤ Real.compEllIntKm (1 - δ ^ 2) := by
  have hm : 1 - δ ^ 2 < 1 := by nlinarith
  set f : ℝ → ℝ := fun θ => (1 - (1 - δ ^ 2) * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ) with hf
  have hfc : Continuous f := continuous_one_sub_mul_sin_sq_rpow hm _
  have hfpos : ∀ θ, 0 ≤ f θ := fun θ => Real.rpow_nonneg (one_sub_mul_sin_sq_pos hm θ).le _
  have hs2 : 0 < √2 := by positivity
  -- restrict to `[0, π/2 - δ]`
  have hsub : ∫ θ in (0 : ℝ)..(π / 2 - δ), f θ ≤ Real.compEllIntKm (1 - δ ^ 2) := by
    rw [Real.compEllIntKm]
    have := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hfc.intervalIntegrable 0 (π / 2 - δ)) (hfc.intervalIntegrable (π / 2 - δ) (π / 2))
    rw [← this]
    have : 0 ≤ ∫ θ in (π / 2 - δ)..(π / 2), f θ :=
      intervalIntegral.integral_nonneg (by linarith) fun θ _ => hfpos θ
    linarith
  have hlow : ∫ θ in (0 : ℝ)..(π / 2 - δ), 1 / (√2 * (π / 2 - θ)) ≤
      ∫ θ in (0 : ℝ)..(π / 2 - δ), f θ := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ (hfc.intervalIntegrable _ _) ?_
    · refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.div (by fun_prop) fun θ hθ => ?_
      rw [Set.uIcc_of_le (by linarith)] at hθ
      have : 0 < π / 2 - θ := by linarith [hθ.2]
      positivity
    · intro θ hθ
      have hx : δ ≤ π / 2 - θ := by linarith [hθ.2]
      have hxpos : 0 < π / 2 - θ := by linarith
      have hc : Real.cos θ ≤ π / 2 - θ := by
        rw [← Real.sin_pi_div_two_sub]; exact Real.sin_le hxpos.le
      have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2]⟩
      have hp := one_sub_mul_sin_sq_pos hm θ
      have hle : 1 - (1 - δ ^ 2) * Real.sin θ ^ 2 ≤ 2 * (π / 2 - θ) ^ 2 := by
        have h := Real.sin_sq_add_cos_sq θ
        have : Real.cos θ ^ 2 ≤ (π / 2 - θ) ^ 2 := pow_le_pow_left₀ hc0 hc 2
        have : δ ^ 2 ≤ (π / 2 - θ) ^ 2 := pow_le_pow_left₀ h0.le hx 2
        nlinarith [Real.sin_sq_le_one θ, sq_nonneg δ]
      simp only [hf]
      rw [Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow, one_div]
      apply inv_anti₀ (Real.sqrt_pos.mpr hp)
      calc √(1 - (1 - δ ^ 2) * Real.sin θ ^ 2) ≤ √(2 * (π / 2 - θ) ^ 2) := Real.sqrt_le_sqrt hle
        _ = √2 * (π / 2 - θ) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hxpos.le]
  have hcalc : ∫ θ in (0 : ℝ)..(π / 2 - δ), 1 / (√2 * (π / 2 - θ)) = Real.log (π / 2 / δ) / √2 := by
    have : ∀ θ, 1 / (√2 * (π / 2 - θ)) = (1 / √2) * (π / 2 - θ)⁻¹ := fun θ => by
      field_simp
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left
      (fun x => x⁻¹) (π / 2)]
    rw [show π / 2 - (π / 2 - δ) = δ by ring, sub_zero, integral_inv_of_pos h0 (by positivity)]
    ring
  linarith

/-- `log(π/(2δ))/√2 → ∞` as `δ → 0+`. -/
lemma p22R1_log_tendsto :
    Tendsto (fun δ : ℝ => Real.log (π / 2 / δ) / √2) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun δ : ℝ => π / 2 / δ) (𝓝[>] 0) atTop := by
    simp_rw [div_eq_mul_inv (π / 2)]
    exact tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
  exact (Real.tendsto_log_atTop.comp h1).atTop_div_const (by positivity)

/-- §22.5(ii): `K'(k) → ∞` as real `k → 0+`. -/
@[dlmf 22.5.ii]
theorem tendsto_norm_compEllIntKpk_zero :
    Tendsto (fun k : ℝ => ‖compEllIntKpk k‖) (𝓝[>] 0) Filter.atTop := by
  refine tendsto_atTop_mono' _ ?_ p22R1_log_tendsto
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
  have hk2 : 0 < k ^ 2 := by nlinarith [hk.1]
  rw [compEllIntKpk_ofReal hk2, Complex.norm_real, Real.norm_eq_abs]
  exact (p22R1_K_ge hk.1 (by linarith [hk.2, Real.pi_gt_three])).trans (le_abs_self _)

/-- §22.5(ii): `K(k) → ∞` as real `k → 1-`. -/
@[dlmf 22.5.ii]
theorem tendsto_norm_compEllIntKk_one :
    Tendsto (fun k : ℝ => ‖compEllIntKk k‖) (𝓝[<] 1) Filter.atTop := by
  have hδ : Tendsto (fun k : ℝ => √(1 - k ^ 2)) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun k : ℝ => √(1 - k ^ 2)) (𝓝 1) (𝓝 (√(1 - 1 ^ 2))) :=
        ((continuous_const.sub (continuous_pow 2)).sqrt).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
      exact Real.sqrt_pos.mpr (by nlinarith [hk.1, hk.2])
  refine tendsto_atTop_mono' _ ?_ (p22R1_log_tendsto.comp hδ)
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  have hpos : 0 < 1 - k ^ 2 := by linarith
  have hd0 : 0 < √(1 - k ^ 2) := Real.sqrt_pos.mpr hpos
  have hd1 : √(1 - k ^ 2) < π / 2 := by
    have : √(1 - k ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
    linarith [Real.pi_gt_three]
  have h := p22R1_K_ge hd0 hd1
  rw [Real.sq_sqrt hpos.le, show 1 - (1 - k ^ 2) = k ^ 2 by ring] at h
  rw [compEllIntKk_ofReal hk2, Complex.norm_real, Real.norm_eq_abs]
  exact h.trans (le_abs_self _)


section p22R1Limits
variable {α : Type*} {l : Filter α} {w τ : α → ℂ} {w0 : ℂ}

lemma p22R1_term_tendsto_zero (hw : Tendsto w l (𝓝 w0))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun i => Real.exp (-π * a * (τ i).im - 2 * π * b * (w i).im)) l (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have h1 : Tendsto (fun i => -π * a * (τ i).im) l atBot :=
    hτ.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos])
  have h2 : Tendsto (fun i => 2 * π * b * (w i).im) l (𝓝 (2 * π * b * w0.im)) :=
    ((continuous_im.tendsto w0).comp hw).const_mul _
  exact h1.atBot_add (h2.neg) |>.congr fun i => by ring

lemma p22R1_bound_ev (hw : Tendsto w l (𝓝 w0)) (hτ : Tendsto (fun i => (τ i).im) l atTop) :
    ∀ᶠ i in l, |(w i).im| ≤ |w0.im| + 1 ∧ 1 ≤ (τ i).im := by
  have h1 : ∀ᶠ i in l, |(w i).im - w0.im| < 1 := by
    have := ((continuous_im.tendsto w0).comp hw)
    exact (Metric.tendsto_nhds.mp this) 1 one_pos |>.mono fun i hi => by
      simpa [Real.dist_eq] using hi
  filter_upwards [h1, hτ.eventually_ge_atTop 1] with i hi h2
  refine ⟨?_, h2⟩
  have := abs_sub_abs_le_abs_sub (w i).im w0.im
  linarith

/-- `θ(w | τ) → 1` as `Im τ → ∞`, locally uniformly in `w`. -/
lemma p22R1_theta2_tendsto_one (hw : Tendsto w l (𝓝 w0))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) :
    Tendsto (fun i => jacobiTheta₂ (w i) (τ i)) l (𝓝 1) := by
  have key : Tendsto (fun i => ∑' n : ℤ, jacobiTheta₂_term n (w i) (τ i)) l
      (𝓝 (∑' n : ℤ, if n = 0 then (1 : ℂ) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n : ℤ => Real.exp (-π * (1 * n ^ 2 - 2 * (|w0.im| + 1) * |n|)))
      (by simpa using summable_pow_mul_jacobiTheta₂_term_bound (|w0.im| + 1) one_pos 0)
      (fun n => ?_) ?_
    · by_cases hn : n = 0
      · subst hn; simpa [jacobiTheta₂_term] using tendsto_const_nhds
      · simp only [hn, ↓reduceIte]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simp_rw [norm_jacobiTheta₂_term]
        have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
        refine (p22R1_term_tendsto_zero hw hτ hn2 n).congr fun i => by ring_nf
    · filter_upwards [p22R1_bound_ev hw hτ] with i hi n
      exact norm_jacobiTheta₂_term_le one_pos hi.1 hi.2 n
  rw [tsum_ite_eq] at key
  exact key

lemma p22R1_term_shift (n : ℤ) (z τ : ℂ) :
    jacobiTheta₂_term n (z + τ / 2) τ = cexp (2 * π * I * n * z + π * I * (n ^ 2 + n) * τ) := by
  rw [jacobiTheta₂_term]; congr 1; ring

/-- `θ(w + τ/2 | τ) → 1 + e^{-2πiw}` as `Im τ → ∞`. -/
lemma p22R1_theta2_shift_tendsto (hw : Tendsto w l (𝓝 w0))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) :
    Tendsto (fun i => jacobiTheta₂ (w i + τ i / 2) (τ i)) l
      (𝓝 (1 + cexp (-(2 * π * I * w0)))) := by
  set S := |w0.im| + 1 + 1 / 2
  have key : Tendsto (fun i => ∑' n : ℤ, jacobiTheta₂_term n (w i + τ i / 2) (τ i)) l
      (𝓝 (∑' n : ℤ, ((if n = 0 then (1 : ℂ) else 0) +
        (if n = -1 then cexp (-(2 * π * I * w0)) else 0)))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n : ℤ => Real.exp (-π * (1 * n ^ 2 - 2 * S * |n|)))
      (by simpa using summable_pow_mul_jacobiTheta₂_term_bound S one_pos 0)
      (fun n => ?_) ?_
    · simp_rw [p22R1_term_shift]
      by_cases h0 : n = 0
      · subst h0; simpa using tendsto_const_nhds
      by_cases h1 : n = -1
      · subst h1; simp only [Int.reduceNeg, ↓reduceIte, zero_add, Int.cast_neg, Int.cast_one]
        have : ∀ i, cexp (2 * π * I * -1 * w i + π * I * ((-1) ^ 2 + -1) * τ i) =
            cexp (-(2 * π * I * w i)) := fun i => by congr 1; ring
        simp_rw [this]
        rw [show (if (-1 : ℤ) = 0 then (1 : ℂ) else 0) = 0 by norm_num, zero_add]
        exact (Complex.continuous_exp.tendsto _).comp ((tendsto_const_nhds.mul hw).neg)
      · simp only [h0, h1, ↓reduceIte, add_zero]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hn : (0 : ℝ) < (n : ℝ) ^ 2 + n := by
          have : n ≥ 1 ∨ n ≤ -2 := by omega
          rcases this with h | h
          · have : (1 : ℝ) ≤ n := by exact_mod_cast h
            nlinarith
          · have : (n : ℝ) ≤ -2 := by exact_mod_cast h
            nlinarith
        refine (p22R1_term_tendsto_zero hw hτ hn n).congr fun i => ?_
        rw [Complex.norm_exp]; congr 1
        simp only [add_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, intCast_re,
          intCast_im, add_im, pow_two, re_ofNat, im_ofNat]
        ring
    · filter_upwards [p22R1_bound_ev hw hτ] with i hi n
      rw [p22R1_term_shift, Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : (2 * π * I * n * w i + π * I * (n ^ 2 + n) * τ i).re =
          -π * ((n : ℝ) ^ 2 + n) * (τ i).im - 2 * π * n * (w i).im := by
        simp only [add_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, intCast_re,
          intCast_im, add_im, pow_two, re_ofNat, im_ofNat]
        ring
      rw [hre]
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 + n := by
        have : n ≥ 0 ∨ n ≤ -1 := by omega
        rcases this with h | h
        · have : (0 : ℝ) ≤ n := by exact_mod_cast h
          nlinarith
        · have : (n : ℝ) ≤ -1 := by exact_mod_cast h
          nlinarith
      have h1 : -π * ((n : ℝ) ^ 2 + n) * (τ i).im ≤ -π * ((n : ℝ) ^ 2 + n) := by
        have := mul_le_mul_of_nonneg_left hi.2 hnn
        nlinarith [Real.pi_pos]
      have h2 : -(2 * π * n * (w i).im) ≤ 2 * π * |(n : ℝ)| * (|w0.im| + 1) := by
        have := abs_mul (n : ℝ) (w i).im
        have h3 : -((n : ℝ) * (w i).im) ≤ |(n : ℝ)| * |(w i).im| := by
          rw [← abs_mul]; exact neg_le_abs _
        have h4 : |(n : ℝ)| * |(w i).im| ≤ |(n : ℝ)| * (|w0.im| + 1) :=
          mul_le_mul_of_nonneg_left hi.1 (abs_nonneg _)
        nlinarith [Real.pi_pos]
      have h5 : -(n : ℝ) ≤ |(n : ℝ)| := neg_le_abs _
      have h6 := mul_le_mul_of_nonneg_left h5 Real.pi_pos.le
      simp only [S, Int.cast_abs]
      nlinarith [Real.pi_pos]
  have hs1 : Summable fun n : ℤ => if n = 0 then (1 : ℂ) else 0 :=
    summable_of_ne_finset_zero (s := {0}) (by intro n hn; simp_all)
  have hs2 : Summable fun n : ℤ => if n = -1 then cexp (-(2 * π * I * w0)) else 0 :=
    summable_of_ne_finset_zero (s := {-1}) (by intro n hn; simp_all)
  rw [Summable.tsum_add hs1 hs2, tsum_ite_eq, tsum_ite_eq] at key
  exact key

/-- Limits of the normalized theta functions as `Im τ → ∞`. -/
noncomputable def p22R1_L (p : JacobiLetter) (z : ℂ) : ℂ :=
  match p with
  | .s => Complex.sin z
  | .c => Complex.cos z
  | .d => 1
  | .n => 1

lemma p22R1_theta3_tendsto {ζ : α → ℂ} {z : ℂ} (hζ : Tendsto ζ l (𝓝 z))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) :
    Tendsto (fun i => jacobiThetaThreeTau (ζ i) (τ i)) l (𝓝 1) :=
  p22R1_theta2_tendsto_one (hζ.div_const _) hτ

lemma p22R1_thetaC_tendsto {ζ : α → ℂ} {z : ℂ} (hζ : Tendsto ζ l (𝓝 z))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) :
    Tendsto (fun i => jacobiThetaTwoTau (ζ i) (τ i) / jacobiThetaTwoTau 0 (τ i)) l
      (𝓝 (Complex.cos z)) := by
  have e : ∀ i, jacobiThetaTwoTau (ζ i) (τ i) / jacobiThetaTwoTau 0 (τ i) =
      cexp (I * ζ i) * jacobiTheta₂ (ζ i / π + τ i / 2) (τ i) /
        jacobiTheta₂ (0 / π + τ i / 2) (τ i) := fun i => by
    simp only [jacobiThetaTwoTau, jacobiThetaThreeTau]
    rw [show (ζ i + π * τ i / 2) / π = ζ i / π + τ i / 2 by field_simp,
      show (0 + π * τ i / 2) / π = 0 / π + τ i / 2 by field_simp, Complex.exp_add,
      mul_zero, add_zero, mul_assoc, mul_div_mul_left _ _ (exp_ne_zero _)]
  simp_rw [e]
  have h1 := p22R1_theta2_shift_tendsto (hζ.div_const (π : ℂ)) hτ
  have h0 := p22R1_theta2_shift_tendsto (w := fun _ => (0 : ℂ) / π) tendsto_const_nhds hτ
  have h2 : Tendsto (fun i => cexp (I * ζ i)) l (𝓝 (cexp (I * z))) :=
    (Complex.continuous_exp.tendsto _).comp (hζ.const_mul I)
  have hne : (1 + cexp (-(2 * π * I * (0 / π)))) ≠ 0 := by norm_num
  have H : Tendsto (fun i => cexp (I * ζ i) * jacobiTheta₂ (ζ i / π + τ i / 2) (τ i) /
      jacobiTheta₂ (0 / π + τ i / 2) (τ i)) l
      (𝓝 (cexp (I * z) * (1 + cexp (-(2 * π * I * (z / π)))) /
        (1 + cexp (-(2 * π * I * (0 / π)))))) := (h2.mul h1).div h0 hne
  convert H using 2
  rw [Complex.cos]
  have : cexp (-(2 * π * I * (z / π))) = cexp (-z * I) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; field_simp; ring
  rw [this, show cexp (I * z) = cexp (z * I) by ring_nf]
  simp only [zero_div, mul_zero, neg_zero, Complex.exp_zero]
  have hm : cexp (z * I) * cexp (-z * I) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  simp only [neg_mul] at hm this ⊢
  field_simp
  linear_combination (-2 * cexp (-(z * I))) * hm

lemma p22R1_letter_tendsto {ζ : α → ℂ} {z : ℂ} (hζ : Tendsto ζ l (𝓝 z))
    (hτ : Tendsto (fun i => (τ i).im) l atTop) (p : JacobiLetter) :
    Tendsto (fun i => jacobiLetterTheta p (ζ i) (τ i)) l (𝓝 (p22R1_L p z)) := by
  have t30 := p22R1_theta3_tendsto (ζ := fun _ => (0 : ℂ)) tendsto_const_nhds hτ
  have t40 := p22R1_theta3_tendsto (ζ := fun _ => (0 : ℂ) + π / 2) tendsto_const_nhds hτ
  cases p
  · simp only [jacobiLetterTheta, p22R1_L, jacobiThetaOneTau]
    have h := p22R1_thetaC_tendsto (hζ.add_const (π / 2 : ℂ)) hτ
    have e : ∀ i, jacobiThetaThreeTau 0 (τ i) / (jacobiThetaTwoTau 0 (τ i) *
        jacobiThetaFourTau 0 (τ i)) * -jacobiThetaTwoTau (ζ i + π / 2) (τ i) =
        -(jacobiThetaThreeTau 0 (τ i) / jacobiThetaThreeTau (0 + π / 2) (τ i)) *
          (jacobiThetaTwoTau (ζ i + π / 2) (τ i) / jacobiThetaTwoTau 0 (τ i)) := fun i => by
      rw [jacobiThetaFourTau]; ring
    simp_rw [e]
    have hq : Tendsto (fun i => jacobiThetaThreeTau 0 (τ i) / jacobiThetaThreeTau (0 + π / 2) (τ i))
        l (𝓝 1) := by
      have := t30.div t40 one_ne_zero
      simpa only [Pi.div_def, div_one] using this
    convert (hq.neg.mul h) using 1
    rw [Complex.cos_add_pi_div_two]; ring
  · simpa [jacobiLetterTheta, p22R1_L] using p22R1_thetaC_tendsto hζ hτ
  · have := (p22R1_theta3_tendsto hζ hτ).div t30 one_ne_zero
    simpa only [Pi.div_def, div_one, jacobiLetterTheta, p22R1_L] using this
  · simp only [jacobiLetterTheta, p22R1_L, jacobiThetaFourTau]
    have := (p22R1_theta3_tendsto (hζ.add_const (π / 2 : ℂ)) hτ).div t40 one_ne_zero
    simpa only [Pi.div_def, div_one, zero_add] using this

end p22R1Limits

lemma p22R1_tau_im_tendsto :
    Tendsto (fun k : ℝ => (jacobiTauk (k : ℂ)).im) (𝓝[>] 0) atTop := by
  have hc : Tendsto (fun k : ℝ => Real.compEllIntKm (k ^ 2)) (𝓝 0) (𝓝 (π / 2)) := by
    have h1 : ContinuousAt Real.compEllIntKm ((0 : ℝ) ^ 2) :=
      Real.continuousAt_compEllIntKm (by norm_num)
    have := (h1.comp (f := fun k : ℝ => k ^ 2) (continuous_pow 2).continuousAt).tendsto
    simpa [Real.compEllIntKm_zero, Function.comp_def] using this
  have hev : ∀ᶠ k : ℝ in 𝓝[>] 0, Real.compEllIntKm (k ^ 2) < 2 :=
    nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds (by linarith [Real.pi_lt_four])))
  have hlog : Tendsto (fun k : ℝ => Real.log (π / 2 / k) / √2 / 2) (𝓝[>] 0) atTop :=
    p22R1_log_tendsto.atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hK hk
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  have hKpos := Real.compEllIntKm_pos hk2
  have hτ : jacobiTauk (k : ℂ) = I * ((Real.compEllIntKm (1 - k ^ 2) /
      Real.compEllIntKm (k ^ 2) : ℝ) : ℂ) := by
    rw [jacobiTauk, compEllIntKk_ofReal hk2, compEllIntKpk_ofReal (by nlinarith [hk.1])]
    push_cast; ring
  rw [hτ, Complex.mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]
  have hge := p22R1_K_ge hk.1 (by linarith [hk.2, Real.pi_gt_three])
  have hKp : 0 ≤ Real.compEllIntKm (1 - k ^ 2) := by
    rw [Real.compEllIntKm]
    exact intervalIntegral.integral_nonneg (by positivity) fun θ _ =>
      Real.rpow_nonneg (one_sub_mul_sin_sq_pos (by nlinarith [hk.1]) θ).le _
  rw [le_div_iff₀ hKpos]
  calc Real.log (π / 2 / k) / √2 / 2 * Real.compEllIntKm (k ^ 2)
      ≤ Real.compEllIntKm (1 - k ^ 2) / 2 * Real.compEllIntKm (k ^ 2) := by
        gcongr
    _ ≤ Real.compEllIntKm (1 - k ^ 2) := by nlinarith

lemma p22R1_zeta_tendsto (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiZetak z k) (𝓝[>] 0) (𝓝 z) := by
  have h := (tendsto_compEllIntKk_zero.const_mul (2 : ℂ))
  have hne : (2 : ℂ) * (π / 2 : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have := (tendsto_const_nhds (x := (π : ℂ) * z)).div h hne
  convert this using 2
  · rfl
  · field_simp

lemma p22R1_pq_tendsto_zero {p q : JacobiLetter} (hpq : p ≠ q) (z : ℂ)
    (hq : p22R1_L q z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiPQk p q z k) (𝓝[>] 0) (𝓝 (p22R1_L p z / p22R1_L q z)) := by
  unfold jacobiPQk jacobiGlaisher
  simp only [hpq, ↓reduceIte]
  exact (p22R1_letter_tendsto (p22R1_zeta_tendsto z) p22R1_tau_im_tendsto p).div
    (p22R1_letter_tendsto (p22R1_zeta_tendsto z) p22R1_tau_im_tendsto q) hq

/-- Table T3: `sn(z, k) → Complex.sin z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiSnk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiSnk z k) (𝓝[>] 0) (𝓝 (Complex.sin z)) := by
  simpa [p22R1_L, jacobiSnk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .s) (q := .n) (by decide) z (by simp [p22R1_L])

/-- Table T3: `cd(z, k) → Complex.cos z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiCdk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiCdk z k) (𝓝[>] 0) (𝓝 (Complex.cos z)) := by
  simpa [p22R1_L, jacobiCdk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .c) (q := .d) (by decide) z (by simp [p22R1_L])

/-- Table T3: `dc(z, k) → (Complex.cos z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiDck_zero (z : ℂ) (hz : Complex.cos z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDck z k) (𝓝[>] 0) (𝓝 ((Complex.cos z)⁻¹)) := by
  simpa [p22R1_L, jacobiDck, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .d) (q := .c) (by decide) z (by simpa [p22R1_L] using hz)

/-- Table T3: `ns(z, k) → (Complex.sin z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiNsk_zero (z : ℂ) (hz : Complex.sin z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNsk z k) (𝓝[>] 0) (𝓝 ((Complex.sin z)⁻¹)) := by
  simpa [p22R1_L, jacobiNsk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .n) (q := .s) (by decide) z (by simpa [p22R1_L] using hz)

/-- Table T3: `cn(z, k) → Complex.cos z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiCnk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiCnk z k) (𝓝[>] 0) (𝓝 (Complex.cos z)) := by
  simpa [p22R1_L, jacobiCnk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .c) (q := .n) (by decide) z (by simp [p22R1_L])

/-- Table T3: `sd(z, k) → Complex.sin z` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiSdk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiSdk z k) (𝓝[>] 0) (𝓝 (Complex.sin z)) := by
  simpa [p22R1_L, jacobiSdk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .s) (q := .d) (by decide) z (by simp [p22R1_L])

/-- Table T3: `nc(z, k) → (Complex.cos z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiNck_zero (z : ℂ) (hz : Complex.cos z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNck z k) (𝓝[>] 0) (𝓝 ((Complex.cos z)⁻¹)) := by
  simpa [p22R1_L, jacobiNck, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .n) (q := .c) (by decide) z (by simpa [p22R1_L] using hz)

/-- Table T3: `ds(z, k) → (Complex.sin z)⁻¹` as real `k → 0+`, away from the poles of
the limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiDsk_zero (z : ℂ) (hz : Complex.sin z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDsk z k) (𝓝[>] 0) (𝓝 ((Complex.sin z)⁻¹)) := by
  simpa [p22R1_L, jacobiDsk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .d) (q := .s) (by decide) z (by simpa [p22R1_L] using hz)

/-- Table T3: `dn(z, k) → 1` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiDnk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiDnk z k) (𝓝[>] 0) (𝓝 (1)) := by
  simpa [p22R1_L, jacobiDnk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .d) (q := .n) (by decide) z (by simp [p22R1_L])

/-- Table T3: `nd(z, k) → 1` as real `k → 0+`. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiNdk_zero (z : ℂ) :
    Tendsto (fun k : ℝ => jacobiNdk z k) (𝓝[>] 0) (𝓝 (1)) := by
  simpa [p22R1_L, jacobiNdk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .n) (q := .d) (by decide) z (by simp [p22R1_L])

/-- Table T3: `sc(z, k) → Complex.tan z` as real `k → 0+`, away from the poles of the
limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiSck_zero (z : ℂ) (hz : Complex.cos z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiSck z k) (𝓝[>] 0) (𝓝 (Complex.tan z)) := by
  simpa [p22R1_L, jacobiSck, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .s) (q := .c) (by decide) z (by simpa [p22R1_L] using hz)

/-- Table T3: `cs(z, k) → Complex.cot z` as real `k → 0+`, away from the poles of the
limit. -/
@[dlmf 22.5.T3]
theorem tendsto_jacobiCsk_zero (z : ℂ) (hz : Complex.sin z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiCsk z k) (𝓝[>] 0) (𝓝 (Complex.cot z)) := by
  simpa [p22R1_L, jacobiCsk, one_div, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin] using
    p22R1_pq_tendsto_zero (p := .c) (q := .s) (by decide) z (by simpa [p22R1_L] using hz)

lemma p22R1_comodulus_ofReal {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    jacobiComodulusk (x : ℂ) = ((√(1 - x ^ 2) : ℝ) : ℂ) := by
  rw [jacobiComodulusk, Real.sqrt_eq_rpow, ofReal_cpow (by nlinarith)]
  push_cast; ring_nf

lemma p22R1_sqrt_tendsto :
    Tendsto (fun k : ℝ => √(1 - k ^ 2)) (𝓝[<] 1) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun k : ℝ => √(1 - k ^ 2)) (𝓝 1) (𝓝 (√(1 - 1 ^ 2))) :=
      ((continuous_const.sub (continuous_pow 2)).sqrt).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
    exact Real.sqrt_pos.mpr (by nlinarith [hk.1, hk.2])

lemma p22R1_pq_tendsto_one {p q : JacobiLetter} (hpq : p ≠ q) (z : ℂ)
    (hq : p22R1_L (p22R1_sig q) (-I * z) ≠ 0) :
    Tendsto (fun k : ℝ => jacobiPQk p q z k) (𝓝[<] 1)
      (𝓝 ((if p = .s then -I else 1) / (if q = .s then -I else 1) *
        ((if p = .s then -1 else 1) * (if q = .s then -1 else 1)) *
        (p22R1_L (p22R1_sig p) (-I * z) / p22R1_L (p22R1_sig q) (-I * z)))) := by
  have hσ : p22R1_sig p ≠ p22R1_sig q := by
    cases p <;> cases q <;> simp_all [p22R1_sig]
  have h := ((p22R1_pq_tendsto_zero hσ (-I * z) hq).comp p22R1_sqrt_tendsto).const_mul
    ((if p = .s then -I else 1) / (if q = .s then -I else 1) *
        ((if p = .s then -1 else 1) * (if q = .s then -1 else 1)))
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
  have hk' := p22R1_ofReal_mem hk.1 hk.2
  simp only [Function.comp_apply]
  rw [← p22R1_comodulus_ofReal hk.1 hk.2, ← p22R1_imag_PQ hk' p q hpq,
    show I * (-I * z) = z by ring_nf; rw [I_sq]; ring]

lemma p22R1_sin_I (z : ℂ) : Complex.sin (I * z) = Complex.sinh z * I := by
  rw [mul_comm, Complex.sin_mul_I]

lemma p22R1_cos_I (z : ℂ) : Complex.cos (I * z) = Complex.cosh z := by
  rw [mul_comm, Complex.cos_mul_I]

lemma p22R1_sin_negI (z : ℂ) : Complex.sin (-I * z) = -(Complex.sinh z * I) := by
  rw [show -I * z = (-z) * I by ring, Complex.sin_mul_I, Complex.sinh_neg]; ring

lemma p22R1_cos_negI (z : ℂ) : Complex.cos (-I * z) = Complex.cosh z := by
  rw [show -I * z = (-z) * I by ring, Complex.cos_mul_I, Complex.cosh_neg]

/-- Table T4: `sn(z, k) → Complex.tanh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiSnk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiSnk z k) (𝓝[<] 1) (𝓝 (Complex.tanh z)) := by
  have h := p22R1_pq_tendsto_one (p := .s) (q := .n) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `cd(z, k) → 1` as real `k → 1-`, away from the poles of the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiCdk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiCdk z k) (𝓝[<] 1) (𝓝 (1)) := by
  have h := p22R1_pq_tendsto_one (p := .c) (q := .d) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `dc(z, k) → 1` as real `k → 1-`, away from the poles of the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiDck_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDck z k) (𝓝[<] 1) (𝓝 (1)) := by
  have h := p22R1_pq_tendsto_one (p := .d) (q := .c) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `ns(z, k) → (Complex.tanh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiNsk_one (z : ℂ) (hz : Complex.sinh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNsk z k) (𝓝[<] 1) (𝓝 ((Complex.tanh z)⁻¹)) := by
  have h := p22R1_pq_tendsto_one (p := .n) (q := .s) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `cn(z, k) → (Complex.cosh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiCnk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiCnk z k) (𝓝[<] 1) (𝓝 ((Complex.cosh z)⁻¹)) := by
  have h := p22R1_pq_tendsto_one (p := .c) (q := .n) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `sd(z, k) → Complex.sinh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiSdk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiSdk z k) (𝓝[<] 1) (𝓝 (Complex.sinh z)) := by
  have h := p22R1_pq_tendsto_one (p := .s) (q := .d) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `nc(z, k) → Complex.cosh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiNck_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNck z k) (𝓝[<] 1) (𝓝 (Complex.cosh z)) := by
  have h := p22R1_pq_tendsto_one (p := .n) (q := .c) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `ds(z, k) → (Complex.sinh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiDsk_one (z : ℂ) (hz : Complex.sinh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDsk z k) (𝓝[<] 1) (𝓝 ((Complex.sinh z)⁻¹)) := by
  have h := p22R1_pq_tendsto_one (p := .d) (q := .s) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `dn(z, k) → (Complex.cosh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiDnk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiDnk z k) (𝓝[<] 1) (𝓝 ((Complex.cosh z)⁻¹)) := by
  have h := p22R1_pq_tendsto_one (p := .d) (q := .n) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `nd(z, k) → Complex.cosh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiNdk_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiNdk z k) (𝓝[<] 1) (𝓝 (Complex.cosh z)) := by
  have h := p22R1_pq_tendsto_one (p := .n) (q := .d) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `sc(z, k) → Complex.sinh z` as real `k → 1-`, away from the poles of the
limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiSck_one (z : ℂ) (hz : Complex.cosh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiSck z k) (𝓝[<] 1) (𝓝 (Complex.sinh z)) := by
  have h := p22R1_pq_tendsto_one (p := .s) (q := .c) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

/-- Table T4: `cs(z, k) → (Complex.sinh z)⁻¹` as real `k → 1-`, away from the poles of
the limit. -/
@[dlmf 22.5.T4]
theorem tendsto_jacobiCsk_one (z : ℂ) (hz : Complex.sinh z ≠ 0) :
    Tendsto (fun k : ℝ => jacobiCsk z k) (𝓝[<] 1) (𝓝 ((Complex.sinh z)⁻¹)) := by
  have h := p22R1_pq_tendsto_one (p := .c) (q := .s) (by decide) z
    (by simp [p22R1_L, p22R1_sig, p22R1_sin_I, p22R1_cos_I, hz, I_ne_zero])
  convert h using 2
  · rfl
  · simp only [p22R1_L, p22R1_sig, reduceCtorEq, ↓reduceIte, p22R1_sin_negI, p22R1_cos_negI,
      Complex.tanh_eq_sinh_div_cosh]
    field_simp
    try ring_nf
    try simp only [I_sq]
    try ring_nf

end DLMF.JacobiElliptic
