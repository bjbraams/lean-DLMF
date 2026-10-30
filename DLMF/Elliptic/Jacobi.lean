/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Amplitude
public import DLMF.Elliptic.Complete

/-!
# Incomplete elliptic integrals and Jacobi's elliptic functions (Temme §§12.2–12.3)

For a real parameter `m < 1` (`m = k²`), Legendre's incomplete integrals
`F(φ|m) = ∫₀^φ (1 - m sin²θ)^{-1/2} dθ` and `E(φ|m) = ∫₀^φ (1 - m sin²θ)^{1/2} dθ` are odd
and quasi-periodic, `F(φ + π|m) = F(φ|m) + 2K(m)`. Since `∂F/∂φ > 0` and `F(nπ|m) = 2nK(m)`,
`φ ↦ F(φ|m)` is an order isomorphism of `ℝ`; its inverse is Jacobi's amplitude `am(u|m)`
(Temme (12.21)–(12.22)), and `sn = sin ∘ am`, `cn = cos ∘ am`, `dn = (1 - m sn²)^{1/2}`. The
inverse function theorem gives `am' = dn` and the derivatives of DLMF 22.13.1–22.13.3.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

noncomputable section

namespace DLMF.Elliptic

/-- `F(am(u|m)|m) = u`. -/
@[dlmf 22.16.E11]
theorem Real.incEllIntFm_jacobiAmm {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.incEllIntFm (Real.jacobiAmm u m) m = u := by
  simp only [Real.jacobiAmm, hm, ↓reduceDIte]
  exact (Real.incEllIntFmOrderIso hm).apply_symm_apply u

/-- `am(F(φ|m)|m) = φ`. -/
theorem Real.jacobiAmm_incEllIntFm {m : ℝ} (hm : m < 1) (φ : ℝ) :
    Real.jacobiAmm (Real.incEllIntFm φ m) m = φ := by
  simp only [Real.jacobiAmm, hm, ↓reduceDIte]
  exact (Real.incEllIntFmOrderIso hm).symm_apply_apply φ

/-- The amplitude is continuous. -/
theorem Real.continuous_jacobiAmm {m : ℝ} (hm : m < 1) : Continuous fun u => Real.jacobiAmm u m := by
  simp only [Real.jacobiAmm, hm, ↓reduceDIte]
  exact (Real.incEllIntFmOrderIso hm).symm.continuous

/-- `d am/du = dn(u|m) = (1 - m sin² am)^{1/2}`. -/
@[dlmf 22.16.i]
theorem Real.hasDerivAt_jacobiAmm {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiAmm u m)
      ((1 - m * sin (Real.jacobiAmm u m) ^ 2) ^ (1 / 2 : ℝ)) u := by
  have hpos := one_sub_mul_sin_sq_pos hm (Real.jacobiAmm u m)
  have h := HasDerivAt.of_local_left_inverse (f := fun φ => Real.incEllIntFm φ m)
    (Real.continuous_jacobiAmm hm).continuousAt
    (Real.hasDerivAt_incEllIntFm hm (Real.jacobiAmm u m))
    (rpow_pos_of_pos hpos _).ne' (Eventually.of_forall fun y => Real.incEllIntFm_jacobiAmm hm y)
  rwa [rpow_neg hpos.le, inv_inv] at h

/-- `am(0|m) = 0`. -/
theorem Real.jacobiAmm_zero {m : ℝ} (hm : m < 1) : Real.jacobiAmm 0 m = 0 := by
  simpa [Real.incEllIntFm] using Real.jacobiAmm_incEllIntFm hm 0

/-- `am(K|m) = π/2`. -/
theorem Real.jacobiAmm_compEllIntKm {m : ℝ} (hm : m < 1) :
    Real.jacobiAmm (Real.compEllIntKm m) m = π / 2 := by
  rw [← Real.incEllIntFm_pi_div_two, Real.jacobiAmm_incEllIntFm hm]

/-- `am(u + 2K|m) = am(u|m) + π`. -/
@[dlmf 22.16.E2]
theorem Real.jacobiAmm_add_two_compEllIntKm {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiAmm (u + 2 * Real.compEllIntKm m) m = Real.jacobiAmm u m + π := by
  conv_lhs => rw [← Real.incEllIntFm_jacobiAmm hm u, ← Real.incEllIntFm_add_pi hm]
  exact Real.jacobiAmm_incEllIntFm hm _

/-- `am(-u|m) = -am(u|m)`. -/
theorem Real.jacobiAmm_neg {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiAmm (-u) m = -Real.jacobiAmm u m := by
  conv_lhs => rw [← Real.incEllIntFm_jacobiAmm hm u, ← Real.incEllIntFm_neg]
  exact Real.jacobiAmm_incEllIntFm hm _

/-- `am(u|0) = u`. -/
@[dlmf 22.16.E4]
theorem Real.jacobiAmm_zero_param (u : ℝ) : Real.jacobiAmm u 0 = u := by
  simpa [Real.incEllIntFm_zero_param] using Real.jacobiAmm_incEllIntFm (m := 0) (by norm_num) u

/-- `sn² + cn² = 1` (DLMF 22.6.1). -/
@[dlmf 22.6.E1]
theorem Real.jacobiSnm_sq_add_jacobiCnm_sq (u m : ℝ) :
    Real.jacobiSnm u m ^ 2 + Real.jacobiCnm u m ^ 2 = 1 :=
  sin_sq_add_cos_sq _

/-- `m sn² + dn² = 1` (DLMF 22.6.1). -/
@[dlmf 22.6.E1]
theorem Real.mul_jacobiSnm_sq_add_jacobiDnm_sq {m : ℝ} (hm : m < 1) (u : ℝ) :
    m * Real.jacobiSnm u m ^ 2 + Real.jacobiDnm u m ^ 2 = 1 := by
  have hx : 0 < 1 - m * Real.jacobiSnm u m ^ 2 := one_sub_mul_sin_sq_pos hm (Real.jacobiAmm u m)
  rw [Real.jacobiDnm, ← rpow_natCast ((1 - m * Real.jacobiSnm u m ^ 2) ^ (1 / 2 : ℝ)) 2,
      ← rpow_mul hx.le]
  norm_num

/-- `dn > 0` for `m < 1`. -/
theorem Real.jacobiDnm_pos {m : ℝ} (hm : m < 1) (u : ℝ) : 0 < Real.jacobiDnm u m :=
  rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm _) _

/-- `d sn/du = cn dn` (DLMF Table 22.13.1). -/
@[dlmf 22.13.T1]
theorem Real.hasDerivAt_jacobiSnm {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiSnm u m) (Real.jacobiCnm u m * Real.jacobiDnm u m) u :=
  (hasDerivAt_sin _).comp u (Real.hasDerivAt_jacobiAmm hm u)

/-- `d cn/du = -sn dn` (DLMF Table 22.13.1). -/
@[dlmf 22.13.T1]
theorem Real.hasDerivAt_jacobiCnm {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiCnm u m) (-(Real.jacobiSnm u m * Real.jacobiDnm u m)) u := by
  have h := (hasDerivAt_cos _).comp u (Real.hasDerivAt_jacobiAmm hm u)
  exact h.congr_deriv (by simp [Real.jacobiSnm, Real.jacobiDnm])

/-- `d dn/du = -m sn cn` (DLMF Table 22.13.1). -/
@[dlmf 22.13.T1]
theorem Real.hasDerivAt_jacobiDnm {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiDnm u m)
      (-(m * Real.jacobiSnm u m * Real.jacobiCnm u m)) u := by
  have hx : 0 < 1 - m * Real.jacobiSnm u m ^ 2 := one_sub_mul_sin_sq_pos hm (Real.jacobiAmm u m)
  have h1 := (((Real.hasDerivAt_jacobiSnm hm u).pow 2).const_mul m).const_sub 1
  have h := h1.rpow_const (p := 1 / 2) (Or.inl hx.ne')
  have hdpos := Real.jacobiDnm_pos hm u
  have hr : (1 - m * Real.jacobiSnm u m ^ 2) ^ (1 / 2 - 1 : ℝ) = (Real.jacobiDnm u m)⁻¹ := by
    rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, rpow_neg hx.le]
    rfl
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  rw [hr]
  field_simp
  ring

/-- `sn(u + 2K) = -sn u`, `cn(u + 2K) = -cn u`, `dn(u + 2K) = dn u` (DLMF Table 22.4.3). -/
@[dlmf 22.4.T3 "real parameter m < 1 and real argument: the 2K column for sn, cn, dn"]
theorem Real.jacobi_add_two_compEllIntKm {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiSnm (u + 2 * Real.compEllIntKm m) m = -Real.jacobiSnm u m ∧
      Real.jacobiCnm (u + 2 * Real.compEllIntKm m) m = -Real.jacobiCnm u m ∧
      Real.jacobiDnm (u + 2 * Real.compEllIntKm m) m = Real.jacobiDnm u m := by
  simp only [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiCnm, Real.jacobiAmm_add_two_compEllIntKm hm,
      sin_add_pi,
    cos_add_pi, neg_sq, and_self]

/-- `sn` and `cn` have period `4K` (DLMF §22.4). -/
@[dlmf 22.4.T1 "real parameter m < 1 and real argument: the period 4K of sn and cn"]
theorem Real.jacobiSnm_add_four_compEllIntKm {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiSnm (u + 4 * Real.compEllIntKm m) m = Real.jacobiSnm u m ∧
      Real.jacobiCnm (u + 4 * Real.compEllIntKm m) m = Real.jacobiCnm u m := by
  have h := Real.jacobi_add_two_compEllIntKm hm (u + 2 * Real.compEllIntKm m)
  have h' := Real.jacobi_add_two_compEllIntKm hm u
  rw [show u + 2 * Real.compEllIntKm m + 2 * Real.compEllIntKm m =
      u + 4 * Real.compEllIntKm m by ring] at h
  exact ⟨by rw [h.1, h'.1, neg_neg], by rw [h.2.1, h'.2.1, neg_neg]⟩

/-- Special values at `u = K` (DLMF Table 22.5.1): `sn K = 1`, `cn K = 0`, `dn K = (1-m)^{1/2}`. -/
@[dlmf 22.5.T1 "real parameter m < 1: values of sn, cn, dn at K"]
theorem Real.jacobi_compEllIntKm {m : ℝ} (hm : m < 1) :
    Real.jacobiSnm (Real.compEllIntKm m) m = 1 ∧ Real.jacobiCnm (Real.compEllIntKm m) m = 0 ∧
      Real.jacobiDnm (Real.compEllIntKm m) m = (1 - m) ^ (1 / 2 : ℝ) := by
  simp [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiCnm, Real.jacobiAmm_compEllIntKm hm]

/-- Values at `u = 0`: `sn 0 = 0`, `cn 0 = 1`, `dn 0 = 1`. -/
@[dlmf 22.5.T1 "real parameter m < 1: values of sn, cn, dn at 0"]
theorem jacobi_zero {m : ℝ} (hm : m < 1) :
    Real.jacobiSnm 0 m = 0 ∧ Real.jacobiCnm 0 m = 1 ∧ Real.jacobiDnm 0 m = 1 := by
  simp [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiCnm, Real.jacobiAmm_zero hm]

/-- `sn` is odd and `cn`, `dn` are even. -/
@[dlmf 22.2 "real parameter m < 1: sn odd, cn and dn even"]
theorem jacobi_neg {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiSnm (-u) m = -Real.jacobiSnm u m ∧ Real.jacobiCnm (-u) m = Real.jacobiCnm u m ∧
      Real.jacobiDnm (-u) m = Real.jacobiDnm u m := by
  simp [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiCnm, Real.jacobiAmm_neg hm]

/-- For `m = 0` the Jacobi functions reduce to `sin`, `cos`, `1` (DLMF §22.5(ii)). -/
@[dlmf 22.5.T3 "exact at m = 0 for real argument"]
theorem jacobi_zero_param (u : ℝ) :
    Real.jacobiSnm u 0 = sin u ∧ Real.jacobiCnm u 0 = cos u ∧ Real.jacobiDnm u 0 = 1 := by
  simp [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiCnm, Real.jacobiAmm_zero_param]

end DLMF.Elliptic
