/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Jacobi

/-!
# Identities for Jacobi's elliptic functions (Duverney Ch. 5; DLMF §§22.6, 22.8, 22.13)

For `m < 1`:
* `dn² - m cn² = 1 - m` and the first- and second-order equations of `sn`, `cn`, `dn`
  (DLMF 22.13.13–22.13.18, Duverney Ex. 5.12).
* The addition formulas for `sn`, `cn`, `dn` (DLMF 22.8.1–22.8.3, Duverney Ex. 5.14). Following
  Duverney, `Ψ(u) = N(u, w-u)/(1 - m sn²u sn²(w-u))` has zero derivative, so it equals `Ψ(0)`.
  The identity `N'D - ND' = 0` is a polynomial identity modulo `sn² + cn² = 1` and
  `m sn² + dn² = 1` at both points.
* The quarter-period shift `u ↦ u + K` and the values at `K/2` (Duverney Ex. 5.15).
* The simple pendulum: `y = 2 arcsin(√m sn(ωt + φ))` solves `y'' + ω² sin y = 0` and has period
  `4K/ω` (Duverney Thm 5.6, Temme §12.1.1).
-/

@[expose] public section

open Real Set Filter
open scoped Topology

noncomputable section

namespace DLMF.Elliptic

/-- `dn² - m cn² = 1 - m` (DLMF 22.6.1). -/
@[dlmf 22.6.E1 "consequence dn² - m cn² = 1 - m of 22.6.1, real m < 1"]
theorem Real.jacobiDnm_sq_sub_mul_jacobiCnm_sq {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiDnm u m ^ 2 - m * Real.jacobiCnm u m ^ 2 = 1 - m := by
  have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq u m
  have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm u
  linear_combination h2 - m * h1

/-- `(sn')² = (1 - sn²)(1 - m sn²)`: the first-order equation of `sn` (DLMF 22.13.1). -/
@[dlmf 22.13.E1]
theorem Real.jacobiSnm_deriv_sq {m : ℝ} (hm : m < 1) (u : ℝ) :
    deriv (fun u => Real.jacobiSnm u m) u ^ 2 =
      (1 - Real.jacobiSnm u m ^ 2) * (1 - m * Real.jacobiSnm u m ^ 2) := by
  rw [(Real.hasDerivAt_jacobiSnm hm u).deriv]
  have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq u m
  have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm u
  linear_combination (1 - m * Real.jacobiSnm u m ^ 2) * h1 + Real.jacobiCnm u m ^ 2 * h2

/-- `(cn')² = (1 - cn²)(1 - m + m cn²)` (DLMF 22.13.2). -/
@[dlmf 22.13.E2]
theorem Real.jacobiCnm_deriv_sq {m : ℝ} (hm : m < 1) (u : ℝ) :
    deriv (fun u => Real.jacobiCnm u m) u ^ 2 =
      (1 - Real.jacobiCnm u m ^ 2) * (1 - m + m * Real.jacobiCnm u m ^ 2) := by
  rw [(Real.hasDerivAt_jacobiCnm hm u).deriv]
  have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq u m
  have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm u
  linear_combination (1 - m + m * Real.jacobiCnm u m ^ 2 - m * Real.jacobiSnm u m ^ 2) * h1 +
    Real.jacobiSnm u m ^ 2 * h2

/-- `(dn')² = (1 - dn²)(dn² - (1 - m))` (DLMF 22.13.3). -/
@[dlmf 22.13.E3]
theorem Real.jacobiDnm_deriv_sq {m : ℝ} (hm : m < 1) (u : ℝ) :
    deriv (fun u => Real.jacobiDnm u m) u ^ 2 =
      (1 - Real.jacobiDnm u m ^ 2) * (Real.jacobiDnm u m ^ 2 - (1 - m)) := by
  rw [(Real.hasDerivAt_jacobiDnm hm u).deriv]
  have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq u m
  have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm u
  linear_combination m ^ 2 * Real.jacobiSnm u m ^ 2 * h1 +
    (Real.jacobiDnm u m ^ 2 - m * Real.jacobiSnm u m ^ 2 + m - 1) * h2

/-- The denominator of the addition formulas is positive. -/
lemma Real.one_sub_mul_jacobiSnm_sq_mul_sq_pos {m : ℝ} (hm : m < 1) (u v : ℝ) :
    0 < 1 - m * Real.jacobiSnm u m ^ 2 * Real.jacobiSnm v m ^ 2 := by
  have h1 : Real.jacobiSnm u m ^ 2 ≤ 1 := by
    have := Real.jacobiSnm_sq_add_jacobiCnm_sq u m; nlinarith [sq_nonneg (Real.jacobiCnm u m)]
  have h2 : Real.jacobiSnm v m ^ 2 ≤ 1 := by
    have := Real.jacobiSnm_sq_add_jacobiCnm_sq v m; nlinarith [sq_nonneg (Real.jacobiCnm v m)]
  have hp : Real.jacobiSnm u m ^ 2 * Real.jacobiSnm v m ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.jacobiSnm u m), sq_nonneg (Real.jacobiSnm v m)]
  have hp0 : 0 ≤ Real.jacobiSnm u m ^ 2 * Real.jacobiSnm v m ^ 2 := by positivity
  rcases le_or_gt m 0 with h | h
  · nlinarith
  · nlinarith

/-- Derivatives of `u ↦ sn(w-u)`, `cn(w-u)`, `dn(w-u)`. -/
lemma hasDerivAt_jacobi_sub {m : ℝ} (hm : m < 1) (w u : ℝ) :
    HasDerivAt (fun u => Real.jacobiSnm (w - u) m)
        (-(Real.jacobiCnm (w - u) m * Real.jacobiDnm (w - u) m)) u ∧
    HasDerivAt (fun u => Real.jacobiCnm (w - u) m)
        (Real.jacobiSnm (w - u) m * Real.jacobiDnm (w - u) m) u ∧
    HasDerivAt (fun u => Real.jacobiDnm (w - u) m)
        (m * Real.jacobiSnm (w - u) m * Real.jacobiCnm (w - u) m) u := by
  have hl : HasDerivAt (fun u : ℝ => w - u) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub w
  refine ⟨?_, ?_, ?_⟩
  · exact ((Real.hasDerivAt_jacobiSnm hm (w - u)).comp u hl).congr_deriv (by ring)
  · exact ((Real.hasDerivAt_jacobiCnm hm (w - u)).comp u hl).congr_deriv (by ring)
  · exact ((Real.hasDerivAt_jacobiDnm hm (w - u)).comp u hl).congr_deriv (by ring)

/-- A function with zero derivative everywhere is constant. -/
lemma eq_of_hasDerivAt_zero {Ψ : ℝ → ℝ} (h : ∀ u, HasDerivAt Ψ 0 u) (u : ℝ) : Ψ u = Ψ 0 :=
  is_const_of_deriv_eq_zero (fun x => (h x).differentiableAt) (fun x => (h x).deriv) u 0

/-- **Addition formula for `sn`** (DLMF 22.8.1, Duverney (5.69)). -/
@[dlmf 22.8.E1]
theorem Real.jacobiSnm_add {m : ℝ} (hm : m < 1) (u v : ℝ) :
    Real.jacobiSnm (u + v) m = (Real.jacobiSnm u m * Real.jacobiCnm v m * Real.jacobiDnm v m +
      Real.jacobiSnm v m * Real.jacobiCnm u m * Real.jacobiDnm u m) /
        (1 - m * Real.jacobiSnm u m ^ 2 * Real.jacobiSnm v m ^ 2) := by
  set w := u + v
  set Ψ : ℝ → ℝ := fun x =>
      (Real.jacobiSnm x m * Real.jacobiCnm (w - x) m * Real.jacobiDnm (w - x) m +
      Real.jacobiSnm (w - x) m * Real.jacobiCnm x m * Real.jacobiDnm x m) /
        (1 - m * Real.jacobiSnm x m ^ 2 * Real.jacobiSnm (w - x) m ^ 2) with hΨ
  have hd (x : ℝ) : HasDerivAt Ψ 0 x := by
    obtain ⟨hs2, hc2, hd2⟩ := hasDerivAt_jacobi_sub hm w x
    have hs1 := Real.hasDerivAt_jacobiSnm hm x
    have hc1 := Real.hasDerivAt_jacobiCnm hm x
    have hd1 := Real.hasDerivAt_jacobiDnm hm x
    have hD := Real.one_sub_mul_jacobiSnm_sq_mul_sq_pos hm x (w - x)
    have h := (((hs1.mul hc2).mul hd2).add ((hs2.mul hc1).mul hd1)).div
      (((hs1.pow 2).const_mul m |>.mul (hs2.pow 2)).const_sub 1) hD.ne'
    refine h.congr_deriv ?_
    rw [div_eq_zero_iff]; left
    have r1a := Real.jacobiSnm_sq_add_jacobiCnm_sq x m
    have r2a := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm x
    have r1b := Real.jacobiSnm_sq_add_jacobiCnm_sq (w - x) m
    have r2b := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm (w - x)
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply]
    generalize Real.jacobiSnm x m = s1 at *
    generalize Real.jacobiCnm x m = c1 at *
    generalize Real.jacobiDnm x m = d1 at *
    generalize Real.jacobiSnm (w - x) m = s2 at *
    generalize Real.jacobiCnm (w - x) m = c2 at *
    generalize Real.jacobiDnm (w - x) m = d2 at *
    linear_combination (m * s1 * s2 * (2 * d1 ^ 2 * s2 ^ 2 + m * s1 ^ 2 * s2 ^ 2 - 1)) * r1a +
      (-s1 * s2 * (m * s1 ^ 2 * s2 ^ 2 - 2 * m * s2 ^ 2 + 1)) * r2a +
      (-m * s1 * s2 * (2 * d2 ^ 2 * s1 ^ 2 + m * s1 ^ 2 * s2 ^ 2 - 1)) * r1b +
      (s1 * s2 * (m * s1 ^ 2 * s2 ^ 2 - 2 * m * s1 ^ 2 + 1)) * r2b
  have h := eq_of_hasDerivAt_zero hd u
  obtain ⟨z1, z2, z3⟩ := jacobi_zero hm
  simp only [hΨ, sub_zero, z1, z2, z3, show w - u = v by simp [w]] at h
  rw [h]; simp

/-- **Addition formula for `cn`** (DLMF 22.8.2, Duverney (5.70)). -/
@[dlmf 22.8.E2]
theorem Real.jacobiCnm_add {m : ℝ} (hm : m < 1) (u v : ℝ) :
    Real.jacobiCnm (u + v) m = (Real.jacobiCnm u m * Real.jacobiCnm v m -
      Real.jacobiSnm u m * Real.jacobiSnm v m * Real.jacobiDnm u m * Real.jacobiDnm v m) /
        (1 - m * Real.jacobiSnm u m ^ 2 * Real.jacobiSnm v m ^ 2) := by
  set w := u + v
  set Ψ : ℝ → ℝ := fun x => (Real.jacobiCnm x m * Real.jacobiCnm (w - x) m -
      Real.jacobiSnm x m * Real.jacobiSnm (w - x) m * Real.jacobiDnm x m *
        Real.jacobiDnm (w - x) m) /
        (1 - m * Real.jacobiSnm x m ^ 2 * Real.jacobiSnm (w - x) m ^ 2) with hΨ
  have hd (x : ℝ) : HasDerivAt Ψ 0 x := by
    obtain ⟨hs2, hc2, hd2⟩ := hasDerivAt_jacobi_sub hm w x
    have hs1 := Real.hasDerivAt_jacobiSnm hm x
    have hc1 := Real.hasDerivAt_jacobiCnm hm x
    have hd1 := Real.hasDerivAt_jacobiDnm hm x
    have hD := Real.one_sub_mul_jacobiSnm_sq_mul_sq_pos hm x (w - x)
    have h := ((hc1.mul hc2).sub (((hs1.mul hs2).mul hd1).mul hd2)).div
      (((hs1.pow 2).const_mul m |>.mul (hs2.pow 2)).const_sub 1) hD.ne'
    refine h.congr_deriv ?_
    rw [div_eq_zero_iff]; left
    have r1a := Real.jacobiSnm_sq_add_jacobiCnm_sq x m
    have r2a := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm x
    have r1b := Real.jacobiSnm_sq_add_jacobiCnm_sq (w - x) m
    have r2b := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm (w - x)
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
    generalize Real.jacobiSnm x m = s1 at *
    generalize Real.jacobiCnm x m = c1 at *
    generalize Real.jacobiDnm x m = d1 at *
    generalize Real.jacobiSnm (w - x) m = s2 at *
    generalize Real.jacobiCnm (w - x) m = c2 at *
    generalize Real.jacobiDnm (w - x) m = d2 at *
    linear_combination (2 * c2 * d1 * m * s1 * s2 ^ 2) * r1a +
      (-c1 * d2 * s2 * (m * s1 ^ 2 * s2 ^ 2 + 1)) * r2a +
      (-2 * c1 * d2 * m * s1 ^ 2 * s2) * r1b + (c2 * d1 * s1 * (m * s1 ^ 2 * s2 ^ 2 + 1)) * r2b
  have h := eq_of_hasDerivAt_zero hd u
  obtain ⟨z1, z2, z3⟩ := jacobi_zero hm
  simp only [hΨ, sub_zero, z1, z2, z3, show w - u = v by simp [w]] at h
  rw [h]; simp

/-- **Addition formula for `dn`** (DLMF 22.8.3, Duverney (5.71)). -/
@[dlmf 22.8.E3]
theorem Real.jacobiDnm_add {m : ℝ} (hm : m < 1) (u v : ℝ) :
    Real.jacobiDnm (u + v) m = (Real.jacobiDnm u m * Real.jacobiDnm v m -
      m * Real.jacobiSnm u m * Real.jacobiSnm v m * Real.jacobiCnm u m * Real.jacobiCnm v m) /
        (1 - m * Real.jacobiSnm u m ^ 2 * Real.jacobiSnm v m ^ 2) := by
  set w := u + v
  set Ψ : ℝ → ℝ := fun x => (Real.jacobiDnm x m * Real.jacobiDnm (w - x) m -
      m * Real.jacobiSnm x m * Real.jacobiSnm (w - x) m * Real.jacobiCnm x m *
          Real.jacobiCnm (w - x) m) /
        (1 - m * Real.jacobiSnm x m ^ 2 * Real.jacobiSnm (w - x) m ^ 2) with hΨ
  have hd (x : ℝ) : HasDerivAt Ψ 0 x := by
    obtain ⟨hs2, hc2, hd2⟩ := hasDerivAt_jacobi_sub hm w x
    have hs1 := Real.hasDerivAt_jacobiSnm hm x
    have hc1 := Real.hasDerivAt_jacobiCnm hm x
    have hd1 := Real.hasDerivAt_jacobiDnm hm x
    have hD := Real.one_sub_mul_jacobiSnm_sq_mul_sq_pos hm x (w - x)
    have h := ((hd1.mul hd2).sub ((((hs1.const_mul m).mul hs2).mul hc1).mul hc2)).div
      (((hs1.pow 2).const_mul m |>.mul (hs2.pow 2)).const_sub 1) hD.ne'
    refine h.congr_deriv ?_
    rw [div_eq_zero_iff]; left
    have r1a := Real.jacobiSnm_sq_add_jacobiCnm_sq x m
    have r2a := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm x
    have r1b := Real.jacobiSnm_sq_add_jacobiCnm_sq (w - x) m
    have r2b := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm (w - x)
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
    generalize Real.jacobiSnm x m = s1 at *
    generalize Real.jacobiCnm x m = c1 at *
    generalize Real.jacobiDnm x m = d1 at *
    generalize Real.jacobiSnm (w - x) m = s2 at *
    generalize Real.jacobiCnm (w - x) m = c2 at *
    generalize Real.jacobiDnm (w - x) m = d2 at *
    linear_combination (-c2 * d1 * m * s2 * (m * s1 ^ 2 * s2 ^ 2 + 1)) * r1a +
      (2 * c1 * d2 * m * s1 * s2 ^ 2) * r2a +
      (c1 * d2 * m * s1 * (m * s1 ^ 2 * s2 ^ 2 + 1)) * r1b + (-2 * c2 * d1 * m * s1 ^ 2 * s2) * r2b
  have h := eq_of_hasDerivAt_zero hd u
  obtain ⟨z1, z2, z3⟩ := jacobi_zero hm
  simp only [hΨ, sub_zero, z1, z2, z3, show w - u = v by simp [w]] at h
  rw [h]; simp

/-- `K(m) > 0` for `m < 1`. -/
lemma Real.compEllIntKm_pos {m : ℝ} (hm : m < 1) : 0 < Real.compEllIntKm m := by
  have h := Real.strictMono_incEllIntFm hm (show (0 : ℝ) < π / 2 by positivity)
  have h0 : Real.incEllIntFm 0 m = 0 := by simp [Real.incEllIntFm]
  simp only at h
  rwa [h0, Real.incEllIntFm_pi_div_two] at h

/-- Shift by a quarter period (DLMF Table 22.4.3, Duverney Ex. 5.15):
`sn(u+K) = cn u/dn u`, `cn(u+K) = -k' sn u/dn u`, `dn(u+K) = k'/dn u`, `k' = (1-m)^{1/2}`. -/
@[dlmf 22.4.T3 "real parameter m < 1: the K column for sn, cn, dn"]
theorem Real.jacobi_add_compEllIntKm {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiSnm (u + Real.compEllIntKm m) m = Real.jacobiCnm u m / Real.jacobiDnm u m ∧
      Real.jacobiCnm (u + Real.compEllIntKm m) m =
          -((1 - m) ^ (1 / 2 : ℝ) * Real.jacobiSnm u m / Real.jacobiDnm u m) ∧
      Real.jacobiDnm (u + Real.compEllIntKm m) m = (1 - m) ^ (1 / 2 : ℝ) / Real.jacobiDnm u m := by
  obtain ⟨k1, k2, k3⟩ := Real.jacobi_compEllIntKm hm
  have hd := Real.jacobiDnm_pos hm u
  have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm u
  have hden : 1 - m * Real.jacobiSnm u m ^ 2 * Real.jacobiSnm (Real.compEllIntKm m) m ^ 2 =
      Real.jacobiDnm u m ^ 2 := by
    rw [k1]; linear_combination -h2
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.jacobiSnm_add hm, hden, k1, k2, k3]; field_simp; ring
  · rw [Real.jacobiCnm_add hm, hden, k1, k2, k3]; field_simp; ring
  · rw [Real.jacobiDnm_add hm, hden, k1, k2, k3]; field_simp; ring

/-- Values at the half quarter-period (DLMF Table 22.5.2, Duverney Ex. 5.15):
`dn(K/2) = k'^{1/2}`, `sn(K/2) = (1+k')^{-1/2}`, `cn(K/2) = k'^{1/2}(1+k')^{-1/2}`. -/
@[dlmf 22.5.T2 "real parameter m < 1: values of sn, cn, dn at K/2"]
theorem Real.jacobi_half_compEllIntKm {m : ℝ} (hm : m < 1) :
    Real.jacobiDnm (Real.compEllIntKm m / 2) m = Real.sqrt (Real.sqrt (1 - m)) ∧
      Real.jacobiSnm (Real.compEllIntKm m / 2) m = 1 / Real.sqrt (1 + Real.sqrt (1 - m)) ∧
      Real.jacobiCnm (Real.compEllIntKm m / 2) m =
        Real.sqrt (Real.sqrt (1 - m)) / Real.sqrt (1 + Real.sqrt (1 - m)) := by
  set K := Real.compEllIntKm m
  have hK := Real.compEllIntKm_pos hm
  have hk' : (1 - m) ^ (1 / 2 : ℝ) = Real.sqrt (1 - m) := (Real.sqrt_eq_rpow _).symm
  obtain ⟨hs, hc, hdd⟩ := Real.jacobi_add_compEllIntKm hm (-(K / 2))
  obtain ⟨ns, nc, nd⟩ := jacobi_neg hm (K / 2)
  rw [show -(K / 2) + K = K / 2 by ring] at hs hc hdd
  simp only [ns, nc, nd, hk'] at hs hc hdd
  set s := Real.jacobiSnm (K / 2) m
  set c := Real.jacobiCnm (K / 2) m
  set d := Real.jacobiDnm (K / 2) m
  have hd : 0 < d := Real.jacobiDnm_pos hm _
  have hq : 0 < Real.sqrt (1 - m) := Real.sqrt_pos.mpr (by linarith)
  have hdsq : d ^ 2 = Real.sqrt (1 - m) := by
    field_simp at hdd; linear_combination hdd
  have hd' : d = Real.sqrt (Real.sqrt (1 - m)) := by
    rw [← hdsq, Real.sqrt_sq hd.le]
  -- `0 < am(K/2) < π/2`
  have ham : 0 < Real.jacobiAmm (K / 2) m ∧ Real.jacobiAmm (K / 2) m < π / 2 := by
    have hmono : StrictMono fun u => Real.jacobiAmm u m := by
      simp only [Real.jacobiAmm, hm, ↓reduceDIte]
      exact (Real.incEllIntFmOrderIso hm).symm.strictMono
    constructor
    · have := hmono (show (0 : ℝ) < K / 2 by positivity)
      simpa [Real.jacobiAmm_zero hm] using this
    · have := hmono (show K / 2 < K by linarith)
      simp only at this
      rwa [Real.jacobiAmm_compEllIntKm hm] at this
  have hs0 : 0 < s := sin_pos_of_pos_of_lt_pi ham.1 (by linarith [ham.2, pi_pos])
  have hcs : c = s * d := by field_simp at hs; linarith
  have h1 : s ^ 2 + c ^ 2 = 1 := Real.jacobiSnm_sq_add_jacobiCnm_sq _ _
  have hs2 : s ^ 2 * (1 + Real.sqrt (1 - m)) = 1 := by
    rw [← hdsq]; rw [hcs] at h1; linear_combination h1
  have hsq : s = 1 / Real.sqrt (1 + Real.sqrt (1 - m)) := by
    have hp : 0 < 1 + Real.sqrt (1 - m) := by positivity
    rw [eq_div_iff (Real.sqrt_pos.mpr hp).ne', ← Real.sqrt_sq hs0.le, ← Real.sqrt_mul (sq_nonneg _),
      hs2, Real.sqrt_one]
  refine ⟨hd', hsq, ?_⟩
  rw [hcs, hsq, hd']; ring

/-- `sn'' = -(1+m) sn + 2m sn³` (DLMF 22.13.13, Duverney Ex. 5.12). -/
@[dlmf 22.13.E13]
theorem Real.iteratedDeriv_two_jacobiSnm {m : ℝ} (hm : m < 1) (u : ℝ) :
    iteratedDeriv 2 (fun u => Real.jacobiSnm u m) u =
      -(1 + m) * Real.jacobiSnm u m + 2 * m * Real.jacobiSnm u m ^ 3 := by
  have hd : deriv (fun u => Real.jacobiSnm u m) =
      fun u => Real.jacobiCnm u m * Real.jacobiDnm u m :=
    funext fun x => (Real.hasDerivAt_jacobiSnm hm x).deriv
  have h' : HasDerivAt (fun u => Real.jacobiCnm u m * Real.jacobiDnm u m) _ u :=
    (Real.hasDerivAt_jacobiCnm hm u).mul (Real.hasDerivAt_jacobiDnm hm u)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, h'.deriv]
  have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq u m
  have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm u
  linear_combination (-(m * Real.jacobiSnm u m)) * h1 + (-Real.jacobiSnm u m) * h2

/-- `cn'' = (2m-1) cn - 2m cn³` (DLMF 22.13.14). -/
@[dlmf 22.13.E14]
theorem Real.iteratedDeriv_two_jacobiCnm {m : ℝ} (hm : m < 1) (u : ℝ) :
    iteratedDeriv 2 (fun u => Real.jacobiCnm u m) u =
      (2 * m - 1) * Real.jacobiCnm u m - 2 * m * Real.jacobiCnm u m ^ 3 := by
  have hd : deriv (fun u => Real.jacobiCnm u m) =
      fun u => -(Real.jacobiSnm u m * Real.jacobiDnm u m) :=
    funext fun x => (Real.hasDerivAt_jacobiCnm hm x).deriv
  have h' : HasDerivAt (fun u => -(Real.jacobiSnm u m * Real.jacobiDnm u m)) _ u :=
    ((Real.hasDerivAt_jacobiSnm hm u).mul (Real.hasDerivAt_jacobiDnm hm u)).neg
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, h'.deriv]
  have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq u m
  have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm u
  linear_combination (2 * m * Real.jacobiCnm u m) * h1 + (-Real.jacobiCnm u m) * h2

/-- `dn'' = (2-m) dn - 2 dn³` (DLMF 22.13.15). -/
@[dlmf 22.13.E15]
theorem Real.iteratedDeriv_two_jacobiDnm {m : ℝ} (hm : m < 1) (u : ℝ) :
    iteratedDeriv 2 (fun u => Real.jacobiDnm u m) u =
      (2 - m) * Real.jacobiDnm u m - 2 * Real.jacobiDnm u m ^ 3 := by
  have hd : deriv (fun u => Real.jacobiDnm u m) =
      fun u => -(m * Real.jacobiSnm u m * Real.jacobiCnm u m) :=
    funext fun x => (Real.hasDerivAt_jacobiDnm hm x).deriv
  have h' : HasDerivAt (fun u => -(m * Real.jacobiSnm u m * Real.jacobiCnm u m)) _ u :=
    (((Real.hasDerivAt_jacobiSnm hm u).const_mul m).mul (Real.hasDerivAt_jacobiCnm hm u)).neg
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, h'.deriv]
  have h1 := Real.jacobiSnm_sq_add_jacobiCnm_sq u m
  have h2 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm u
  linear_combination (-(m * Real.jacobiDnm u m)) * h1 + (2 * Real.jacobiDnm u m) * h2

/-- The pendulum solution `y(t) = 2 arcsin(k sn(ωt + φ))`, `k = √m`. -/
def pendulumAngle (m ω φ t : ℝ) : ℝ := 2 * arcsin (Real.sqrt m * Real.jacobiSnm (ω * t + φ) m)

/-- **The simple pendulum** (Duverney Thm 5.6, Temme §12.1.1): for `0 ≤ m < 1`, the angle
`y(t) = 2 arcsin(√m sn(ωt + φ))` solves `y'' + ω² sin y = 0`, with `y' = 2√m ω cn(ωt + φ)`. -/
theorem pendulumAngle_ode {m : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) (ω φ t : ℝ) :
    HasDerivAt (pendulumAngle m ω φ) (2 * Real.sqrt m * ω * Real.jacobiCnm (ω * t + φ) m) t ∧
      iteratedDeriv 2 (pendulumAngle m ω φ) t + ω ^ 2 * sin (pendulumAngle m ω φ t) = 0 := by
  have hk : Real.sqrt m < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt hm0 hm
  have hk0 := Real.sqrt_nonneg m
  have hsq := Real.sq_sqrt hm0
  have hd (x : ℝ) : HasDerivAt (pendulumAngle m ω φ)
      (2 * Real.sqrt m * ω * Real.jacobiCnm (ω * x + φ) m) x := by
    set w := ω * x + φ
    have hs1 : Real.jacobiSnm w m ^ 2 ≤ 1 := by
      have := Real.jacobiSnm_sq_add_jacobiCnm_sq w m; nlinarith [sq_nonneg (Real.jacobiCnm w m)]
    have habs : |Real.sqrt m * Real.jacobiSnm w m| < 1 := by
      rw [abs_mul, abs_of_nonneg hk0]
      have : |Real.jacobiSnm w m| ≤ 1 := by rw [← sq_le_one_iff_abs_le_one]; exact hs1
      nlinarith [abs_nonneg (Real.jacobiSnm w m)]
    have hlin : HasDerivAt (fun t : ℝ => ω * t + φ) ω x := by
      simpa using ((hasDerivAt_id x).const_mul ω).add_const φ
    have hsn := ((Real.hasDerivAt_jacobiSnm hm w).comp x hlin).const_mul (Real.sqrt m)
    have hlt := abs_lt.mp habs
    have hne1 : Real.sqrt m * Real.jacobiSnm w m ≠ -1 := by linarith [hlt.1]
    have hne2 : Real.sqrt m * Real.jacobiSnm w m ≠ 1 := by linarith [hlt.2]
    have ha := (Real.hasDerivAt_arcsin hne1 hne2).comp x hsn
    have hdn : Real.sqrt (1 - (Real.sqrt m * Real.jacobiSnm w m) ^ 2) = Real.jacobiDnm w m := by
      rw [mul_pow, hsq, Real.jacobiDnm, Real.sqrt_eq_rpow]
    refine (ha.const_mul 2).congr_deriv ?_
    rw [hdn]
    have := Real.jacobiDnm_pos hm w
    field_simp
  refine ⟨hd t, ?_⟩
  have hdd : deriv (pendulumAngle m ω φ) =
      fun x => 2 * Real.sqrt m * ω * Real.jacobiCnm (ω * x + φ) m :=
    funext fun x => (hd x).deriv
  have hlin : HasDerivAt (fun t : ℝ => ω * t + φ) ω t := by
    simpa using ((hasDerivAt_id t).const_mul ω).add_const φ
  have h' : HasDerivAt (fun x => 2 * Real.sqrt m * ω * Real.jacobiCnm (ω * x + φ) m) _ t :=
    ((Real.hasDerivAt_jacobiCnm hm (ω * t + φ)).comp t hlin).const_mul (2 * Real.sqrt m * ω)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hdd, h'.deriv]
  set w := ω * t + φ
  have hs1 : Real.jacobiSnm w m ^ 2 ≤ 1 := by
    have := Real.jacobiSnm_sq_add_jacobiCnm_sq w m; nlinarith [sq_nonneg (Real.jacobiCnm w m)]
  have hx : |Real.sqrt m * Real.jacobiSnm w m| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hk0]
    have : |Real.jacobiSnm w m| ≤ 1 := by rw [← sq_le_one_iff_abs_le_one]; exact hs1
    nlinarith [abs_nonneg (Real.jacobiSnm w m)]
  have hsin : sin (pendulumAngle m ω φ t) =
      2 * (Real.sqrt m * Real.jacobiSnm w m) * Real.jacobiDnm w m := by
    rw [pendulumAngle, sin_two_mul, sin_arcsin (by linarith [neg_abs_le (Real.sqrt m *
      Real.jacobiSnm w m)]) (by linarith [le_abs_self (Real.sqrt m * Real.jacobiSnm w m)]),
          cos_arcsin,
      mul_pow, hsq, Real.jacobiDnm, ← Real.sqrt_eq_rpow]
  rw [hsin]
  ring

/-- The pendulum has period `4K/ω` (Duverney Rem. 5.7). -/
theorem pendulumAngle_periodic {m : ℝ} (hm : m < 1) {ω : ℝ} (hω : ω ≠ 0) (φ t : ℝ) :
    pendulumAngle m ω φ (t + 4 * Real.compEllIntKm m / ω) = pendulumAngle m ω φ t := by
  have h : ω * (t + 4 * Real.compEllIntKm m / ω) + φ = ω * t + φ + 4 * Real.compEllIntKm m := by
    field_simp; ring
  simp only [pendulumAngle]
  rw [h, (Real.jacobiSnm_add_four_compEllIntKm hm _).1]

end DLMF.Elliptic

end
