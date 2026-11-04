/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Amplitude
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Jacobi's amplitude and elliptic functions: basic properties

For a real parameter `m < 1` (`m = k²`), `φ ↦ F(φ|m)` is an order isomorphism of `ℝ` whose inverse
is Jacobi's amplitude `am(u|m)` (Temme §§12.2–12.3, (12.21)–(12.22)); `sn = sin ∘ am`,
`cn = cos ∘ am` and `dn = (1 - m sn²)^{1/2}`. This file proves the inverse relations,
derivatives, periodicity and special values, and defines the inverse function `arcsn`.

## Main definitions

* `Real.jacobiArcsnOfParameter`: Jacobi's inverse function `arcsn(x|m) = F(arcsin x|m)` (DLMF
  22.15.4).

## Main results

* `Real.incompleteEllipticFOfParameter_jacobiAmOfParameter`,
  `Real.jacobiAmOfParameter_incompleteEllipticFOfParameter`: `F(am(u|m)|m) = u` and
  `am(F(φ|m)|m) = φ` (DLMF 22.16.11).
* `Real.hasDerivAt_jacobiAmOfParameter`: `am' = dn` (DLMF §22.16(i)).
* `Real.jacobiAmOfParameter_add_two_completeEllipticKOfParameter`,
  `Real.jacobiAmOfParameter_zero_param`: `am(u + 2K|m) = am(u|m) + π` and `am(u|0) = u` (DLMF
  22.16.2, 22.16.4).
* `Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq`,
  `Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq`: DLMF 22.6.1.
* `Real.hasDerivAt_jacobiSnOfParameter`, `Real.hasDerivAt_jacobiCnOfParameter`,
  `Real.hasDerivAt_jacobiDnOfParameter`: derivatives (DLMF Table 22.13.1).
* `Real.continuous_jacobiSnOfParameter`, `Real.continuous_jacobiCnOfParameter`,
  `Real.continuous_jacobiDnOfParameter`: continuity for `m < 1`.
* `Real.jacobi_add_two_completeEllipticKOfParameter`,
  `Real.jacobiSnOfParameter_add_four_completeEllipticKOfParameter`: half-period shifts and periods
  (DLMF Tables 22.4.1, 22.4.3).
* `Real.jacobi_completeEllipticKOfParameter`, `jacobi_zero`: values at `u = K` and `u = 0` (DLMF
  Table 22.5.1).
* `jacobi_neg`: `sn` is odd and `cn`, `dn` are even.
* `jacobi_zero_param`: for `m = 0` the functions reduce to `sin`, `cos`, `1` (DLMF §22.5(ii)).
* `Real.jacobiSnOfParameter_jacobiArcsnOfParameter`,
  `Real.jacobiArcsnOfParameter_jacobiSnOfParameter`, `Real.hasDerivAt_jacobiArcsnOfParameter`:
  `arcsn` inverts `sn` on `[-K, K]`, with derivative `((1 - x²)(1 - m x²))^{-1/2}`.

## Implementation notes

The derivatives follow from the inverse function theorem applied to `F(·|m)`, whose derivative
is positive.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

noncomputable section

namespace DLMF.Elliptic

/-- `F(am(u|m)|m) = u`. -/
@[dlmf 22.16.E11]
theorem Real.incompleteEllipticFOfParameter_jacobiAmOfParameter {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.incompleteEllipticFOfParameter (Real.jacobiAmOfParameter u m) m = u := by
  simp only [Real.jacobiAmOfParameter, hm, ↓reduceDIte]
  exact (Real.incompleteEllipticFOfParameterOrderIso hm).apply_symm_apply u

/-- `am(F(φ|m)|m) = φ`. -/
theorem Real.jacobiAmOfParameter_incompleteEllipticFOfParameter {m : ℝ} (hm : m < 1) (φ : ℝ) :
    Real.jacobiAmOfParameter (Real.incompleteEllipticFOfParameter φ m) m = φ := by
  simp only [Real.jacobiAmOfParameter, hm, ↓reduceDIte]
  exact (Real.incompleteEllipticFOfParameterOrderIso hm).symm_apply_apply φ

/-- The amplitude is continuous. -/
theorem Real.continuous_jacobiAmOfParameter {m : ℝ} (hm : m < 1) :
    Continuous fun u => Real.jacobiAmOfParameter u m := by
  simp only [Real.jacobiAmOfParameter, hm, ↓reduceDIte]
  exact (Real.incompleteEllipticFOfParameterOrderIso hm).symm.continuous

/-- `d am/du = dn(u|m) = (1 - m sin² am)^{1/2}`. -/
@[dlmf 22.16.i]
theorem Real.hasDerivAt_jacobiAmOfParameter {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiAmOfParameter u m)
      ((1 - m * sin (Real.jacobiAmOfParameter u m) ^ 2) ^ (1 / 2 : ℝ)) u := by
  have hpos := one_sub_mul_sin_sq_pos hm (Real.jacobiAmOfParameter u m)
  have h := HasDerivAt.of_local_left_inverse (f := fun φ => Real.incompleteEllipticFOfParameter φ m)
    (Real.continuous_jacobiAmOfParameter hm).continuousAt
    (Real.hasDerivAt_incompleteEllipticFOfParameter hm (Real.jacobiAmOfParameter u m))
    (rpow_pos_of_pos hpos _).ne'
        (Eventually.of_forall fun y => Real.incompleteEllipticFOfParameter_jacobiAmOfParameter hm y)
  rwa [rpow_neg hpos.le, inv_inv] at h

/-- `am(0|m) = 0`. -/
theorem Real.jacobiAmOfParameter_zero {m : ℝ} (hm : m < 1) : Real.jacobiAmOfParameter 0 m = 0 := by
  simpa [Real.incompleteEllipticFOfParameter] using
      Real.jacobiAmOfParameter_incompleteEllipticFOfParameter hm 0

/-- `am(K|m) = π/2`. -/
theorem Real.jacobiAmOfParameter_completeEllipticKOfParameter {m : ℝ} (hm : m < 1) :
    Real.jacobiAmOfParameter (Real.completeEllipticKOfParameter m) m = π / 2 := by
  rw [← Real.incompleteEllipticFOfParameter_pi_div_two,
      Real.jacobiAmOfParameter_incompleteEllipticFOfParameter hm]

/-- `am(u + 2K|m) = am(u|m) + π`. -/
@[dlmf 22.16.E2]
theorem Real.jacobiAmOfParameter_add_two_completeEllipticKOfParameter {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiAmOfParameter (u + 2 * Real.completeEllipticKOfParameter m) m =
        Real.jacobiAmOfParameter u m + π := by
  conv_lhs => rw [← Real.incompleteEllipticFOfParameter_jacobiAmOfParameter hm u,
                ← Real.incompleteEllipticFOfParameter_add_pi hm]
  exact Real.jacobiAmOfParameter_incompleteEllipticFOfParameter hm _

/-- `am(-u|m) = -am(u|m)`. -/
theorem Real.jacobiAmOfParameter_neg {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiAmOfParameter (-u) m = -Real.jacobiAmOfParameter u m := by
  conv_lhs => rw [← Real.incompleteEllipticFOfParameter_jacobiAmOfParameter hm u,
                ← Real.incompleteEllipticFOfParameter_neg]
  exact Real.jacobiAmOfParameter_incompleteEllipticFOfParameter hm _

/-- `am(u|0) = u`. -/
@[dlmf 22.16.E4]
theorem Real.jacobiAmOfParameter_zero_param (u : ℝ) : Real.jacobiAmOfParameter u 0 = u := by
  simpa [Real.incompleteEllipticFOfParameter_zero_param] using
      Real.jacobiAmOfParameter_incompleteEllipticFOfParameter (m := 0) (by norm_num) u

/-- `sn² + cn² = 1` (DLMF 22.6.1). -/
@[dlmf 22.6.E1]
theorem Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq (u m : ℝ) :
    Real.jacobiSnOfParameter u m ^ 2 + Real.jacobiCnOfParameter u m ^ 2 = 1 :=
  sin_sq_add_cos_sq _

/-- `m sn² + dn² = 1` (DLMF 22.6.1). -/
@[dlmf 22.6.E1]
theorem Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq {m : ℝ} (hm : m < 1) (u : ℝ) :
    m * Real.jacobiSnOfParameter u m ^ 2 + Real.jacobiDnOfParameter u m ^ 2 = 1 := by
  have hx : 0 < 1 - m * Real.jacobiSnOfParameter u m ^ 2 :=
      one_sub_mul_sin_sq_pos hm (Real.jacobiAmOfParameter u m)
  rw [Real.jacobiDnOfParameter,
      ← rpow_natCast ((1 - m * Real.jacobiSnOfParameter u m ^ 2) ^ (1 / 2 : ℝ)) 2,
      ← rpow_mul hx.le]
  norm_num

/-- `dn > 0` for `m < 1`. -/
theorem Real.jacobiDnOfParameter_pos {m : ℝ} (hm : m < 1) (u : ℝ) : 0 <
    Real.jacobiDnOfParameter u m :=
  rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm _) _

/-- `d sn/du = cn dn` (DLMF Table 22.13.1). -/
@[dlmf 22.13.T1]
theorem Real.hasDerivAt_jacobiSnOfParameter {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiSnOfParameter u m)
        (Real.jacobiCnOfParameter u m * Real.jacobiDnOfParameter u m) u :=
  (hasDerivAt_sin _).comp u (Real.hasDerivAt_jacobiAmOfParameter hm u)

/-- `d cn/du = -sn dn` (DLMF Table 22.13.1). -/
@[dlmf 22.13.T1]
theorem Real.hasDerivAt_jacobiCnOfParameter {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiCnOfParameter u m)
        (-(Real.jacobiSnOfParameter u m * Real.jacobiDnOfParameter u m)) u := by
  have h := (hasDerivAt_cos _).comp u (Real.hasDerivAt_jacobiAmOfParameter hm u)
  exact h.congr_deriv (by simp [Real.jacobiSnOfParameter, Real.jacobiDnOfParameter])

/-- `d dn/du = -m sn cn` (DLMF Table 22.13.1). -/
@[dlmf 22.13.T1]
theorem Real.hasDerivAt_jacobiDnOfParameter {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiDnOfParameter u m)
      (-(m * Real.jacobiSnOfParameter u m * Real.jacobiCnOfParameter u m)) u := by
  have hx : 0 < 1 - m * Real.jacobiSnOfParameter u m ^ 2 :=
      one_sub_mul_sin_sq_pos hm (Real.jacobiAmOfParameter u m)
  have h1 := (((Real.hasDerivAt_jacobiSnOfParameter hm u).pow 2).const_mul m).const_sub 1
  have h := h1.rpow_const (p := 1 / 2) (Or.inl hx.ne')
  have hdpos := Real.jacobiDnOfParameter_pos hm u
  have hr : (1 - m * Real.jacobiSnOfParameter u m ^ 2) ^ (1 / 2 - 1 : ℝ) =
      (Real.jacobiDnOfParameter u m)⁻¹ := by
    rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, rpow_neg hx.le]
    rfl
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  rw [hr]
  field_simp
  ring

/-- `sn(·|m)` is continuous for `m < 1`. -/
theorem Real.continuous_jacobiSnOfParameter {m : ℝ} (hm : m < 1) :
    Continuous fun u => Real.jacobiSnOfParameter u m :=
  continuous_iff_continuousAt.mpr fun u => (Real.hasDerivAt_jacobiSnOfParameter hm u).continuousAt

/-- `cn(·|m)` is continuous for `m < 1`. -/
theorem Real.continuous_jacobiCnOfParameter {m : ℝ} (hm : m < 1) :
    Continuous fun u => Real.jacobiCnOfParameter u m :=
  continuous_iff_continuousAt.mpr fun u => (Real.hasDerivAt_jacobiCnOfParameter hm u).continuousAt

/-- `dn(·|m)` is continuous for `m < 1`. -/
theorem Real.continuous_jacobiDnOfParameter {m : ℝ} (hm : m < 1) :
    Continuous fun u => Real.jacobiDnOfParameter u m :=
  continuous_iff_continuousAt.mpr fun u => (Real.hasDerivAt_jacobiDnOfParameter hm u).continuousAt

/-- `sn(0|m) = 0` for `m < 1`. -/
theorem Real.jacobiSnOfParameter_zero {m : ℝ} (hm : m < 1) : Real.jacobiSnOfParameter 0 m = 0 := by
  simp [Real.jacobiSnOfParameter, Real.jacobiAmOfParameter_zero hm]

/-- `sn(u + 2K) = -sn u`, `cn(u + 2K) = -cn u`, `dn(u + 2K) = dn u` (DLMF Table 22.4.3). -/
@[dlmf 22.4.T3 "real parameter m < 1 and real argument: the 2K column for sn, cn, dn"]
theorem Real.jacobi_add_two_completeEllipticKOfParameter {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiSnOfParameter (u + 2 * Real.completeEllipticKOfParameter m) m =
        -Real.jacobiSnOfParameter u m ∧
      Real.jacobiCnOfParameter (u + 2 * Real.completeEllipticKOfParameter m) m =
          -Real.jacobiCnOfParameter u m ∧
      Real.jacobiDnOfParameter (u + 2 * Real.completeEllipticKOfParameter m) m =
          Real.jacobiDnOfParameter u m := by
  simp only [Real.jacobiDnOfParameter, Real.jacobiSnOfParameter, Real.jacobiCnOfParameter,
      Real.jacobiAmOfParameter_add_two_completeEllipticKOfParameter hm,
      sin_add_pi,
    cos_add_pi, neg_sq, and_self]

/-- `sn` and `cn` have period `4K` (DLMF §22.4). -/
@[dlmf 22.4.T1 "real parameter m < 1 and real argument: the period 4K of sn and cn"]
theorem Real.jacobiSnOfParameter_add_four_completeEllipticKOfParameter {m : ℝ}
    (hm : m < 1) (u : ℝ) :
    Real.jacobiSnOfParameter (u + 4 * Real.completeEllipticKOfParameter m) m =
        Real.jacobiSnOfParameter u m ∧
      Real.jacobiCnOfParameter (u + 4 * Real.completeEllipticKOfParameter m) m =
          Real.jacobiCnOfParameter u m := by
  have h := Real.jacobi_add_two_completeEllipticKOfParameter hm
      (u + 2 * Real.completeEllipticKOfParameter m)
  have h' := Real.jacobi_add_two_completeEllipticKOfParameter hm u
  rw [show u + 2 * Real.completeEllipticKOfParameter m + 2 * Real.completeEllipticKOfParameter m =
      u + 4 * Real.completeEllipticKOfParameter m by ring] at h
  exact ⟨by rw [h.1, h'.1, neg_neg], by rw [h.2.1, h'.2.1, neg_neg]⟩

/-- Special values at `u = K` (DLMF Table 22.5.1): `sn K = 1`, `cn K = 0`, `dn K = (1-m)^{1/2}`. -/
@[dlmf 22.5.T1 "real parameter m < 1: values of sn, cn, dn at K"]
theorem Real.jacobi_completeEllipticKOfParameter {m : ℝ} (hm : m < 1) :
    Real.jacobiSnOfParameter (Real.completeEllipticKOfParameter m) m = 1 ∧
        Real.jacobiCnOfParameter (Real.completeEllipticKOfParameter m) m = 0 ∧
      Real.jacobiDnOfParameter (Real.completeEllipticKOfParameter m) m = (1 - m) ^ (1 / 2 : ℝ) := by
  simp [Real.jacobiDnOfParameter, Real.jacobiSnOfParameter, Real.jacobiCnOfParameter,
      Real.jacobiAmOfParameter_completeEllipticKOfParameter hm]

/-- Values at `u = 0`: `sn 0 = 0`, `cn 0 = 1`, `dn 0 = 1`. -/
@[dlmf 22.5.T1 "real parameter m < 1: values of sn, cn, dn at 0"]
theorem jacobi_zero {m : ℝ} (hm : m < 1) :
    Real.jacobiSnOfParameter 0 m = 0 ∧ Real.jacobiCnOfParameter 0 m = 1 ∧
        Real.jacobiDnOfParameter 0 m = 1 := by
  simp [Real.jacobiDnOfParameter, Real.jacobiSnOfParameter, Real.jacobiCnOfParameter,
      Real.jacobiAmOfParameter_zero hm]

/-- `sn` is odd and `cn`, `dn` are even. -/
@[dlmf 22.2 "real parameter m < 1: sn odd, cn and dn even"]
theorem jacobi_neg {m : ℝ} (hm : m < 1) (u : ℝ) :
    Real.jacobiSnOfParameter (-u) m = -Real.jacobiSnOfParameter u m ∧
        Real.jacobiCnOfParameter (-u) m = Real.jacobiCnOfParameter u m ∧
      Real.jacobiDnOfParameter (-u) m = Real.jacobiDnOfParameter u m := by
  simp [Real.jacobiDnOfParameter, Real.jacobiSnOfParameter, Real.jacobiCnOfParameter,
      Real.jacobiAmOfParameter_neg hm]

/-- For `m = 0` the Jacobi functions reduce to `sin`, `cos`, `1` (DLMF §22.5(ii)). -/
@[dlmf 22.5.T3 "exact at m = 0 for real argument"]
theorem jacobi_zero_param (u : ℝ) :
    Real.jacobiSnOfParameter u 0 = sin u ∧ Real.jacobiCnOfParameter u 0 = cos u ∧
        Real.jacobiDnOfParameter u 0 = 1 := by
  simp [Real.jacobiDnOfParameter, Real.jacobiSnOfParameter, Real.jacobiCnOfParameter,
      Real.jacobiAmOfParameter_zero_param]

/-- Jacobi's inverse function `arcsn(x|m) = F(arcsin x|m)` (Duverney (5.56)). -/
@[dlmf 22.15.E4]
def Real.jacobiArcsnOfParameter (x m : ℝ) : ℝ := Real.incompleteEllipticFOfParameter (arcsin x) m

/-- `sn(arcsn x) = x` for `|x| ≤ 1`. -/
@[dlmf 22.15.E1]
theorem Real.jacobiSnOfParameter_jacobiArcsnOfParameter {m : ℝ} (hm : m < 1) {x : ℝ} (hx : -1 ≤ x)
    (hx1 : x ≤ 1) :
    Real.jacobiSnOfParameter (Real.jacobiArcsnOfParameter x m) m = x := by
  rw [Real.jacobiSnOfParameter, Real.jacobiArcsnOfParameter,
      Real.jacobiAmOfParameter_incompleteEllipticFOfParameter hm, sin_arcsin hx hx1]

/-- `arcsn(sn u) = u` for `|u| ≤ K`. -/
theorem Real.jacobiArcsnOfParameter_jacobiSnOfParameter {m : ℝ} (hm : m < 1) {u : ℝ}
    (hu : |u| ≤ Real.completeEllipticKOfParameter m) :
    Real.jacobiArcsnOfParameter (Real.jacobiSnOfParameter u m) m = u := by
  have hmono : StrictMono fun u => Real.jacobiAmOfParameter u m := by
    simp only [Real.jacobiAmOfParameter, hm, ↓reduceDIte];
        exact (Real.incompleteEllipticFOfParameterOrderIso hm).symm.strictMono
  have h1 : Real.jacobiAmOfParameter u m ≤ π / 2 := by
    rw [← Real.jacobiAmOfParameter_completeEllipticKOfParameter hm];
        exact hmono.monotone (le_of_abs_le hu)
  have h2 : -(π / 2) ≤ Real.jacobiAmOfParameter u m := by
    rw [← Real.jacobiAmOfParameter_completeEllipticKOfParameter hm,
        ← Real.jacobiAmOfParameter_neg hm]
    exact hmono.monotone (neg_le_of_abs_le hu)
  rw [Real.jacobiArcsnOfParameter, Real.jacobiSnOfParameter, arcsin_sin h2 h1,
      Real.incompleteEllipticFOfParameter_jacobiAmOfParameter hm]

/-- `d arcsn/dx = ((1-x²)(1-mx²))^{-1/2}` for `|x| < 1` (Duverney (5.57)). -/
theorem Real.hasDerivAt_jacobiArcsnOfParameter {m : ℝ} (hm : m < 1) {x : ℝ} (hx : -1 < x)
    (hx1 : x < 1) :
    HasDerivAt (fun x => Real.jacobiArcsnOfParameter x m)
      (1 / Real.sqrt ((1 - x ^ 2) * (1 - m * x ^ 2))) x := by
  have ha := hasDerivAt_arcsin hx.ne' hx1.ne
  have h := (Real.hasDerivAt_incompleteEllipticFOfParameter hm (arcsin x)).comp x ha
  refine h.congr_deriv ?_
  have hp : 0 < 1 - m * x ^ 2 := by
    have := one_sub_mul_sin_sq_pos hm (arcsin x); rwa [sin_arcsin hx.le hx1.le] at this
  have hq : 0 < 1 - x ^ 2 := by nlinarith
  rw [sin_arcsin hx.le hx1.le, rpow_neg hp.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul hq.le]
  field_simp

end DLMF.Elliptic
