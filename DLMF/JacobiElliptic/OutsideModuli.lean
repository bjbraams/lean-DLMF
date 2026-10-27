/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.P3jJacobiODE

/-!
# Moduli outside the interval `[0, 1]` (DLMF §22.17)

* 22.17.1 `pq(z, -k) = pq(z, k)` is proved for all twelve functions and all complex `z, k`:
  the definition `jacobiPQk` depends on `k` only through `k²`.
* The reciprocal-modulus transformation 22.17.2–22.17.4 and the imaginary-modulus
  transformation 22.17.6–22.17.8 are stated for complex moduli with both moduli involved in
  `jacobiModulusDomain` (DLMF §22.17(ii): the functions are meromorphic in `k²`, so the
  identities persist for complex `k`). The real moduli `1/k > 1` and `ik` lie on the cut
  `[1, ∞)` or on the imaginary axis, where the literal definition `jacobiPQk` uses principal
  branches of `K'(k)` that are not the analytic continuation, so they are not covered here.
  These six statements are proved by ODE uniqueness: both sides solve the Jacobi system
  `s' = cd, c' = -sd, d' = -k²sc` for the same modulus with the same initial values, so they
  agree near `0` (`p3j_ode_unique`) and then everywhere by the identity principle
  `p3j_eq_of_eventuallyEq` (poles included, from Tables 22.4.1–22.4.2).
* 22.17.5: `k₁ = k/√(1 + k²)`, `k₁k₁' = k/(1 + k²)`, proved for real `k`.
-/

@[expose] public section

open Complex Filter
open scoped Topology

noncomputable section

namespace DLMF.JacobiElliptic

/-- DLMF 22.17.1: `pq(z, -k) = pq(z, k)` for all twelve Glaisher functions (all letters
`p, q`), all complex `z` and `k`. -/
@[dlmf 22.17.E1 "stronger than DLMF: all complex z and k"]
theorem jacobiPQk_neg_modulus (p q : JacobiLetter) (z k : ℂ) :
    jacobiPQk p q z (-k) = jacobiPQk p q z k := by
  simp only [jacobiPQk, jacobiZetak, jacobiTauk, compEllIntKk, compEllIntKpk, neg_sq]

/-- DLMF 22.17.2–22.17.4 jointly (reciprocal modulus). -/
lemma p3j_inv_all {k : ℂ} (hk : k ∈ jacobiModulusDomain) (hk' : k⁻¹ ∈ jacobiModulusDomain) :
    (fun z => jacobiSnk z k⁻¹) = (fun z => k * jacobiSnk (z / k) k) ∧
      (fun z => jacobiCnk z k⁻¹) = (fun z => 1 * jacobiDnk (z / k) k) ∧
      (fun z => jacobiDnk z k⁻¹) = (fun z => 1 * jacobiCnk (z / k) k) := by
  have hk0 : k ≠ 0 := by rintro rfl; simp [jacobiModulusDomain] at hk
  have r1 := p22R1_eventually_ne hk' (p22R1_reg0 hk' (q := .n) (by decide))
  have r2 := p3j_reg_near hk (q := .n) (by decide) k
  have hdiv : ∀ w : ℂ, HasDerivAt (fun w : ℂ => w / k) (1 / k) w := fun w =>
    (hasDerivAt_id w).div_const k
  have chain : ∀ {f : ℂ → ℂ} {f' : ℂ} (z : ℂ), HasDerivAt f f' (z / k) →
      HasDerivAt (fun w => f (w / k)) (f' * (1 / k)) z := fun z h => h.comp z (hdiv z)
  have E := p3j_ode_unique (κ := k⁻¹ ^ 2)
    (s := fun z => jacobiSnk z k⁻¹) (c := fun z => jacobiCnk z k⁻¹)
    (d := fun z => jacobiDnk z k⁻¹)
    (s₂ := fun z => k * jacobiSnk (z / k) k) (c₂ := fun z => 1 * jacobiDnk (z / k) k)
    (d₂ := fun z => 1 * jacobiCnk (z / k) k)
    (r1.mono fun z hz => hasDerivAt_jacobiSnk hk' hz)
    (r1.mono fun z hz => hasDerivAt_jacobiCnk hk' hz)
    (r1.mono fun z hz => hasDerivAt_jacobiDnk hk' hz)
    (r2.mono fun z hz => ((chain z (hasDerivAt_jacobiSnk hk hz)).const_mul k).congr_deriv
      (by field_simp))
    (r2.mono fun z hz => ((chain z (hasDerivAt_jacobiDnk hk hz)).const_mul 1).congr_deriv
      (by field_simp))
    (r2.mono fun z hz => ((chain z (hasDerivAt_jacobiCnk hk hz)).const_mul 1).congr_deriv
      (by field_simp))
    (by simp [jacobiSnk_zero hk, jacobiSnk_zero hk'])
    (by simp [jacobiCnk_zero hk', jacobiDnk_zero hk])
    (by simp [jacobiDnk_zero hk', jacobiCnk_zero hk])
  refine ⟨p3j_eq_of_eventuallyEq (p3j_dich_pq hk' (by decide))
      ((p3j_dich_pq hk (p := .s) (q := .n) (by decide)).comp hk0 hk0) E.1,
    p3j_eq_of_eventuallyEq (p3j_dich_pq hk' (by decide))
      ((p3j_dich_pq hk (p := .d) (q := .n) (by decide)).comp hk0 one_ne_zero) E.2.1,
    p3j_eq_of_eventuallyEq (p3j_dich_pq hk' (by decide))
      ((p3j_dich_pq hk (p := .c) (q := .n) (by decide)).comp hk0 one_ne_zero) E.2.2⟩

/-- DLMF 22.17.2: `sn(z, 1/k) = k sn(z/k, k)`, for complex `k` with `k, 1/k ∈ jacobiModulusDomain`.
-/
@[dlmf 22.17.E2 "special case: k and 1/k in jacobiModulusDomain (non-real k)"]
theorem jacobiSnk_inv {k : ℂ} (hk : k ∈ jacobiModulusDomain) (hk' : k⁻¹ ∈ jacobiModulusDomain)
    (z : ℂ) : jacobiSnk z k⁻¹ = k * jacobiSnk (z / k) k := by
  exact congrFun (p3j_inv_all hk hk').1 z

/-- DLMF 22.17.3: `cn(z, 1/k) = dn(z/k, k)`, for `k, 1/k ∈ jacobiModulusDomain`-/
@[dlmf 22.17.E3 "special case: k and 1/k in jacobiModulusDomain (non-real k)"]
theorem jacobiCnk_inv {k : ℂ} (hk : k ∈ jacobiModulusDomain) (hk' : k⁻¹ ∈ jacobiModulusDomain)
    (z : ℂ) : jacobiCnk z k⁻¹ = jacobiDnk (z / k) k := by
  simpa using congrFun (p3j_inv_all hk hk').2.1 z

/-- DLMF 22.17.4: `dn(z, 1/k) = cn(z/k, k)`, for `k, 1/k ∈ jacobiModulusDomain`-/
@[dlmf 22.17.E4 "special case: k and 1/k in jacobiModulusDomain (non-real k)"]
theorem jacobiDnk_inv {k : ℂ} (hk : k ∈ jacobiModulusDomain) (hk' : k⁻¹ ∈ jacobiModulusDomain)
    (z : ℂ) : jacobiDnk z k⁻¹ = jacobiCnk (z / k) k := by
  simpa using congrFun (p3j_inv_all hk hk').2.2 z

/-- DLMF 22.17.5: for real `k`, `k₁ = k/√(1 + k²)` satisfies `k₁ k₁' = k/(1 + k²)` with
`k₁' = √(1 - k₁²)`. -/
@[dlmf 22.17.E5 "special case: real k"]
theorem mul_sqrt_one_sub_sq_imagModulus (k : ℝ) :
    k / √(1 + k ^ 2) * √(1 - (k / √(1 + k ^ 2)) ^ 2) = k / (1 + k ^ 2) := by
  have hp : 0 < 1 + k ^ 2 := by positivity
  have hs : 0 < √(1 + k ^ 2) := Real.sqrt_pos.mpr hp
  have h1 : 1 - (k / √(1 + k ^ 2)) ^ 2 = (1 / √(1 + k ^ 2)) ^ 2 := by
    rw [div_pow, div_pow, Real.sq_sqrt hp.le]
    field_simp
    ring
  rw [h1, Real.sqrt_sq (by positivity)]
  field_simp
  rw [Real.sq_sqrt hp.le]

/-- The modulus `k₁ = k/√(1 + k²)` of DLMF 22.17.5 for complex `k` (principal square root;
DLMF 22.17(i): either value of the square root can be chosen). -/
@[dlmf 22.17.E5]
def jacobiImagModulusk (k : ℂ) : ℂ := k / (1 + k ^ 2) ^ (1 / 2 : ℂ)

/-- DLMF 22.17.6–22.17.8 jointly (imaginary modulus). -/
lemma p3j_I_mul_all {k : ℂ} (hk : I * k ∈ jacobiModulusDomain)
    (hk₁ : jacobiImagModulusk k ∈ jacobiModulusDomain) :
    (fun z => jacobiSnk z (I * k)) = (fun z => jacobiComodulusk (jacobiImagModulusk k) *
        jacobiSdk (z / jacobiComodulusk (jacobiImagModulusk k)) (jacobiImagModulusk k)) ∧
      (fun z => jacobiCnk z (I * k)) = (fun z => 1 *
        jacobiCdk (z / jacobiComodulusk (jacobiImagModulusk k)) (jacobiImagModulusk k)) ∧
      (fun z => jacobiDnk z (I * k)) = (fun z => 1 *
        jacobiNdk (z / jacobiComodulusk (jacobiImagModulusk k)) (jacobiImagModulusk k)) := by
  set k₁ := jacobiImagModulusk k with hk₁def
  set k₁' := jacobiComodulusk k₁ with hk₁'def
  have hk1 : 1 + k ^ 2 ≠ 0 := by
    intro h
    have h1 := hk
    have : k ^ 2 = -1 := by linear_combination h
    have hk' : k = I ∨ k = -I := by
      have : (k - I) * (k + I) = 0 := by linear_combination this - I_sq
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases hk' with rfl | rfl
    · simp [jacobiModulusDomain] at h1; linarith
    · simp [jacobiModulusDomain] at h1
  have hs1 : k₁ ^ 2 = k ^ 2 / (1 + k ^ 2) := by
    simp only [k₁, jacobiImagModulusk, div_pow, p22R1_sqrt_sq]
  have hs2 : k₁' ^ 2 = 1 / (1 + k ^ 2) := by
    simp only [k₁', jacobiComodulusk, p22R1_sqrt_sq, hs1]
    field_simp; ring
  have hk₁'0 : k₁' ≠ 0 := by
    intro h; rw [h] at hs2; simp at hs2; exact hk1 (by simpa using hs2.symm)
  have r1 := p22R1_eventually_ne hk (p22R1_reg0 hk (q := .n) (by decide))
  have r2 := p3j_reg_near hk₁ (q := .d) (by decide) k₁'
  have hdiv : ∀ w : ℂ, HasDerivAt (fun w : ℂ => w / k₁') (1 / k₁') w := fun w =>
    (hasDerivAt_id w).div_const k₁'
  have chain : ∀ {f : ℂ → ℂ} {f' : ℂ} (z : ℂ), HasDerivAt f f' (z / k₁') →
      HasDerivAt (fun w => f (w / k₁')) (f' * (1 / k₁')) z := fun z h => h.comp z (hdiv z)
  have hratio : k₁ ^ 2 = (I * k) ^ 2 * (-1) * k₁' ^ 2 := by
    rw [hs1, hs2, mul_pow, I_sq]; field_simp
  have E := p3j_ode_unique (κ := (I * k) ^ 2)
    (s := fun z => jacobiSnk z (I * k)) (c := fun z => jacobiCnk z (I * k))
    (d := fun z => jacobiDnk z (I * k))
    (s₂ := fun z => k₁' * jacobiSdk (z / k₁') k₁) (c₂ := fun z => 1 * jacobiCdk (z / k₁') k₁)
    (d₂ := fun z => 1 * jacobiNdk (z / k₁') k₁)
    (r1.mono fun z hz => hasDerivAt_jacobiSnk hk hz)
    (r1.mono fun z hz => hasDerivAt_jacobiCnk hk hz)
    (r1.mono fun z hz => hasDerivAt_jacobiDnk hk hz)
    (r2.mono fun z hz => ((chain z (hasDerivAt_jacobiSdk hk₁ hz)).const_mul k₁').congr_deriv
      (by field_simp))
    (r2.mono fun z hz => ((chain z (hasDerivAt_jacobiCdk hk₁ hz)).const_mul 1).congr_deriv
      (by rw [← hk₁'def]; field_simp))
    (r2.mono fun z hz => ((chain z (hasDerivAt_jacobiNdk hk₁ hz)).const_mul 1).congr_deriv
      (by rw [hratio]; field_simp))
    (by simp [jacobiSnk_zero hk, jacobiSdk_zero hk₁])
    (by simp [jacobiCnk_zero hk, jacobiCdk_zero hk₁])
    (by simp [jacobiDnk_zero hk, jacobiNdk_zero hk₁])
  refine ⟨p3j_eq_of_eventuallyEq (p3j_dich_pq hk (by decide))
      ((p3j_dich_pq hk₁ (p := .s) (q := .d) (by decide)).comp hk₁'0 hk₁'0) E.1,
    p3j_eq_of_eventuallyEq (p3j_dich_pq hk (by decide))
      ((p3j_dich_pq hk₁ (p := .c) (q := .d) (by decide)).comp hk₁'0 one_ne_zero) E.2.1,
    p3j_eq_of_eventuallyEq (p3j_dich_pq hk (by decide))
      ((p3j_dich_pq hk₁ (p := .n) (q := .d) (by decide)).comp hk₁'0 one_ne_zero) E.2.2⟩

/-- DLMF 22.17.6: `sn(z, ik) = k₁' sd(z/k₁', k₁)`, `k₁ = k/√(1 + k²)`, `k₁' = √(1 - k₁²)`, for
complex `k` with `ik, k₁ ∈ jacobiModulusDomain`-/
@[dlmf 22.17.E6 "special case: ik and k₁ in jacobiModulusDomain"]
theorem jacobiSnk_I_mul {k : ℂ} (hk : I * k ∈ jacobiModulusDomain)
    (hk₁ : jacobiImagModulusk k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSnk z (I * k) = jacobiComodulusk (jacobiImagModulusk k) *
      jacobiSdk (z / jacobiComodulusk (jacobiImagModulusk k)) (jacobiImagModulusk k) := by
  exact congrFun (p3j_I_mul_all hk hk₁).1 z

/-- DLMF 22.17.7: `cn(z, ik) = cd(z/k₁', k₁)`, for `ik, k₁ ∈ jacobiModulusDomain`-/
@[dlmf 22.17.E7 "special case: ik and k₁ in jacobiModulusDomain"]
theorem jacobiCnk_I_mul {k : ℂ} (hk : I * k ∈ jacobiModulusDomain)
    (hk₁ : jacobiImagModulusk k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiCnk z (I * k) =
      jacobiCdk (z / jacobiComodulusk (jacobiImagModulusk k)) (jacobiImagModulusk k) := by
  simpa using congrFun (p3j_I_mul_all hk hk₁).2.1 z

/-- DLMF 22.17.8: `dn(z, ik) = nd(z/k₁', k₁)`, for `ik, k₁ ∈ jacobiModulusDomain`-/
@[dlmf 22.17.E8 "special case: ik and k₁ in jacobiModulusDomain"]
theorem jacobiDnk_I_mul {k : ℂ} (hk : I * k ∈ jacobiModulusDomain)
    (hk₁ : jacobiImagModulusk k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiDnk z (I * k) =
      jacobiNdk (z / jacobiComodulusk (jacobiImagModulusk k)) (jacobiImagModulusk k) := by
  simpa using congrFun (p3j_I_mul_all hk hk₁).2.2 z

end DLMF.JacobiElliptic
