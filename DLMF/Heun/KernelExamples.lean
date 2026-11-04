/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMFMathlib.Analysis.Calculus.Deriv.MulComp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Heun's operator on the kernels of Examples 1 and 2 of DLMF §31.10

The kernels of DLMF 31.10.10 and 31.10.11 are products `P(z) F(u(z)) G(v(z))` of a power factor
and two hypergeometric functions of rational arguments. This file computes Heun's operator
`𝒟_z` (`heunOperator`) on such products in closed form, with `F` and `G` arbitrary analytic
functions; the kernel equations themselves are proved in `DLMF.Heun.Integral`.

## Main results

* `heunOperator_mul_comp_mul_comp`: `𝒟_z (P · F ∘ u · G ∘ v)` in terms of the derivatives of the
  factors (`heunOperatorProductValue`).
* `heunOperator_kernelExample₁`, `heunOperator_kernelExample₂`: the closed forms for the kernels
  of 31.10.10 and 31.10.11.
-/

@[expose] public noncomputable section

open Filter Complex
open scoped Topology

namespace DLMF.Heun

/-- The value of `heunOperator` on `x ↦ P x * F (u x) * G (v x)` in terms of the derivatives
of the factors. -/
def heunOperatorProductValue (a α β γ δ ε z P P1 P2 u1 u2 v1 v2 F0 F1 F2 G0 G1 G2 : ℂ) : ℂ :=
  z * (z - 1) * (z - a) * (P2 * F0 * G0 + 2 * P1 * u1 * F1 * G0 + 2 * P1 * F0 * v1 * G1 +
      P * (u2 * F1 + u1 ^ 2 * F2) * G0 + 2 * P * u1 * v1 * F1 * G1 +
      P * F0 * (v2 * G1 + v1 ^ 2 * G2)) +
    (γ * (z - 1) * (z - a) + δ * z * (z - a) + ε * z * (z - 1)) *
      (P1 * F0 * G0 + P * u1 * F1 * G0 + P * F0 * v1 * G1) + α * β * z * (P * F0 * G0)

/-- `heunOperator` applied to `x ↦ P x * F (u x) * G (v x)`, for `F` and `G` analytic. -/
theorem heunOperator_mul_comp_mul_comp {a α β γ δ ε : ℂ} {P u v F G P1 u1 v1 : ℂ → ℂ}
    {P2 u2 v2 z : ℂ}
    (hP : ∀ᶠ x in 𝓝 z, HasDerivAt P (P1 x) x) (hP1 : HasDerivAt P1 P2 z)
    (hu : ∀ᶠ x in 𝓝 z, HasDerivAt u (u1 x) x) (hu1 : HasDerivAt u1 u2 z)
    (hv : ∀ᶠ x in 𝓝 z, HasDerivAt v (v1 x) x) (hv1 : HasDerivAt v1 v2 z)
    (hF : AnalyticAt ℂ F (u z)) (hG : AnalyticAt ℂ G (v z)) :
    heunOperator a α β γ δ ε (fun x => P x * F (u x) * G (v x)) z =
      heunOperatorProductValue a α β γ δ ε z (P z) (P1 z) P2 (u1 z) u2 (v1 z) v2 (F (u z))
        (deriv F (u z)) (deriv (deriv F) (u z)) (G (v z)) (deriv G (v z))
        (deriv (deriv G) (v z)) := by
  obtain ⟨h1, h2⟩ := deriv_deriv_mul_comp_mul_comp hP hP1 hu hu1 hv hv1 hF hG
  rw [heunOperator, h1, h2, heunOperatorProductValue]

/-- The operator `𝒟_z` applied to a kernel of the form of DLMF 31.10.10,
`(zt - a)^p F(zt/a) G(a(z-1)(t-1)/((a-1)(zt-a)))`, for `F`, `G` analytic. -/
theorem heunOperator_kernelExample₁ {a α β γ δ ε p z t : ℂ} {F G : ℂ → ℂ} (ha1 : a ≠ 1)
    (hF : AnalyticAt ℂ F (z * t / a))
    (hG : AnalyticAt ℂ G (a * (z - 1) * (t - 1) / ((a - 1) * (z * t - a))))
    (hD : z * t - a ∈ slitPlane) :
    heunOperator a α β γ δ ε (fun x => (x * t - a) ^ p * F (x * t / a) *
        G (a * (x - 1) * (t - 1) / ((a - 1) * (x * t - a)))) z =
      heunOperatorProductValue a α β γ δ ε z ((z * t - a) ^ p)
        (p * t * (z * t - a) ^ p / (z * t - a))
        (p * (p - 1) * t ^ 2 * (z * t - a) ^ p / (z * t - a) ^ 2) (t / a) 0
        (a * (t - 1) * (t - a) / ((a - 1) * (z * t - a) ^ 2))
        (-2 * t * a * (t - 1) * (t - a) / ((a - 1) * (z * t - a) ^ 3)) (F (z * t / a))
        (deriv F (z * t / a)) (deriv (deriv F) (z * t / a))
        (G (a * (z - 1) * (t - 1) / ((a - 1) * (z * t - a))))
        (deriv G (a * (z - 1) * (t - 1) / ((a - 1) * (z * t - a))))
        (deriv (deriv G) (a * (z - 1) * (t - 1) / ((a - 1) * (z * t - a)))) := by
  have hD0 : z * t - a ≠ 0 := slitPlane_ne_zero hD
  have ha1' : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hcont : Continuous fun x : ℂ => x * t - a := by fun_prop
  have hev : ∀ᶠ x in 𝓝 z, x * t - a ∈ slitPlane :=
    hcont.continuousAt.eventually_mem (isOpen_slitPlane.mem_nhds hD)
  have hlin : ∀ x, HasDerivAt (fun x : ℂ => x * t - a) t x := fun x => by
    simpa using ((hasDerivAt_id x).mul_const t).sub_const a
  have hP : ∀ᶠ x in 𝓝 z, HasDerivAt (fun x : ℂ => (x * t - a) ^ p)
      (p * (x * t - a) ^ (p - 1) * t) x := by
    filter_upwards [hev] with x hx
    exact (hlin x).cpow_const hx
  have hP1 : HasDerivAt (fun x : ℂ => p * (x * t - a) ^ (p - 1) * t)
      (p * ((p - 1) * (z * t - a) ^ (p - 1 - 1) * t) * t) z :=
    (((hlin z).cpow_const hD).const_mul p).mul_const t
  have hu' : ∀ᶠ x in 𝓝 z, HasDerivAt (fun x : ℂ => x * t / a) (t / a) x :=
    Eventually.of_forall fun x => by simpa using ((hasDerivAt_id x).mul_const t).div_const a
  have hu1 : HasDerivAt (fun _ : ℂ => t / a) 0 z := hasDerivAt_const _ _
  have hv' : ∀ᶠ x in 𝓝 z, HasDerivAt
      (fun x : ℂ => a * (x - 1) * (t - 1) / ((a - 1) * (x * t - a)))
      (a * (t - 1) * (t - a) / ((a - 1) * (x * t - a) ^ 2)) x := by
    filter_upwards [hev] with x hx
    have hx0 : x * t - a ≠ 0 := slitPlane_ne_zero hx
    have h1 : HasDerivAt (fun x : ℂ => a * (x - 1) * (t - 1)) (a * (t - 1)) x := by
      simpa using (((hasDerivAt_id x).sub_const 1).const_mul a).mul_const (t - 1)
    have h2 : HasDerivAt (fun x : ℂ => (a - 1) * (x * t - a)) ((a - 1) * t) x :=
      (hlin x).const_mul _
    convert h1.div h2 (mul_ne_zero ha1' hx0) using 1
    field_simp
    ring
  have hv1 : HasDerivAt (fun x : ℂ => a * (t - 1) * (t - a) / ((a - 1) * (x * t - a) ^ 2))
      (-2 * t * a * (t - 1) * (t - a) / ((a - 1) * (z * t - a) ^ 3)) z := by
    have h2 : HasDerivAt (fun x : ℂ => (a - 1) * (x * t - a) ^ 2)
        ((a - 1) * ((2 : ℕ) * (z * t - a) ^ (2 - 1) * t)) z :=
      ((hlin z).pow 2).const_mul _
    convert (hasDerivAt_const z (a * (t - 1) * (t - a))).div h2
      (mul_ne_zero ha1' (pow_ne_zero 2 hD0)) using 1
    norm_num
    field_simp
  rw [heunOperator_mul_comp_mul_comp hP hP1 hu' hu1 hv' hv1 hF hG]
  have e1 : (z * t - a) ^ (p - 1) = (z * t - a) ^ p / (z * t - a) := by
    rw [cpow_sub _ _ hD0, cpow_one]
  have e2 : (z * t - a) ^ (p - 1 - 1) = (z * t - a) ^ p / (z * t - a) ^ 2 := by
    rw [cpow_sub _ _ hD0, cpow_sub _ _ hD0, cpow_one, div_div, ← sq]
  simp only [e1, e2]
  congr 1 <;> ring


/-- The operator `𝒟_z` applied to a kernel of the form of DLMF 31.10.11,
`(zt - a)^p (zt/a)^q F(a/(zt)) G((z-a)(t-a)/((1-a)(zt-a)))`, for `F`, `G` analytic. -/
theorem heunOperator_kernelExample₂ {a α β γ δ ε p q z t : ℂ} {F G : ℂ → ℂ} (ha1 : a ≠ 1)
    (hF : AnalyticAt ℂ F (a / (z * t)))
    (hG : AnalyticAt ℂ G ((z - a) * (t - a) / ((1 - a) * (z * t - a))))
    (hD : z * t - a ∈ slitPlane) (hE : z * t / a ∈ slitPlane) :
    heunOperator a α β γ δ ε (fun x => (x * t - a) ^ p * (x * t / a) ^ q * F (a / (x * t)) *
        G ((x - a) * (t - a) / ((1 - a) * (x * t - a)))) z =
      heunOperatorProductValue a α β γ δ ε z ((z * t - a) ^ p * (z * t / a) ^ q)
        ((z * t - a) ^ p * (z * t / a) ^ q * (p * t / (z * t - a) + q / z))
        ((z * t - a) ^ p * (z * t / a) ^ q *
          ((p * t / (z * t - a) + q / z) ^ 2 - p * t ^ 2 / (z * t - a) ^ 2 - q / z ^ 2))
        (-(a / (z ^ 2 * t))) (2 * a / (z ^ 3 * t))
        (a * (t - a) * (t - 1) / ((1 - a) * (z * t - a) ^ 2))
        (-2 * t * a * (t - a) * (t - 1) / ((1 - a) * (z * t - a) ^ 3))
        (F (a / (z * t))) (deriv F (a / (z * t))) (deriv (deriv F) (a / (z * t)))
        (G ((z - a) * (t - a) / ((1 - a) * (z * t - a))))
        (deriv G ((z - a) * (t - a) / ((1 - a) * (z * t - a))))
        (deriv (deriv G) ((z - a) * (t - a) / ((1 - a) * (z * t - a)))) := by
  have hD0 : z * t - a ≠ 0 := slitPlane_ne_zero hD
  have hE0 : z * t / a ≠ 0 := slitPlane_ne_zero hE
  have ha0 : a ≠ 0 := by rintro rfl; simp at hE0
  have hz0 : z ≠ 0 := by rintro rfl; simp at hE0
  have ht0 : t ≠ 0 := by rintro rfl; simp at hE0
  have ha1' : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have hev1 : ∀ᶠ x in 𝓝 z, x * t - a ∈ slitPlane :=
    (show Continuous fun x : ℂ => x * t - a by fun_prop).continuousAt.eventually_mem
      (isOpen_slitPlane.mem_nhds hD)
  have hev2 : ∀ᶠ x in 𝓝 z, x * t / a ∈ slitPlane :=
    (show Continuous fun x : ℂ => x * t / a by fun_prop).continuousAt.eventually_mem
      (isOpen_slitPlane.mem_nhds hE)
  have hlin : ∀ x, HasDerivAt (fun x : ℂ => x * t - a) t x := fun x => by
    simpa using ((hasDerivAt_id x).mul_const t).sub_const a
  have hlin2 : ∀ x, HasDerivAt (fun x : ℂ => x * t / a) (t / a) x := fun x => by
    simpa using ((hasDerivAt_id x).mul_const t).div_const a
  have hP : ∀ᶠ x in 𝓝 z, HasDerivAt (fun x : ℂ => (x * t - a) ^ p * (x * t / a) ^ q)
      (p * (x * t - a) ^ (p - 1) * t * (x * t / a) ^ q +
        (x * t - a) ^ p * (q * (x * t / a) ^ (q - 1) * (t / a))) x := by
    filter_upwards [hev1, hev2] with x hx1 hx2
    exact ((hlin x).cpow_const hx1).mul ((hlin2 x).cpow_const hx2)
  have hP1 := (((((hlin z).cpow_const (c := p - 1) hD).const_mul p).mul_const t).mul
    ((hlin2 z).cpow_const (c := q) hE)).add (((hlin z).cpow_const (c := p) hD).mul
      ((((hlin2 z).cpow_const (c := q - 1) hE).const_mul q).mul_const (t / a)))
  have hu : ∀ᶠ x in 𝓝 z, HasDerivAt (fun x : ℂ => a / (x * t)) (-(a / (x ^ 2 * t))) x := by
    filter_upwards [hev2] with x hx2
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx2
    exact ((hasDerivAt_const x a).div ((hasDerivAt_id' x).mul_const t)
      (mul_ne_zero hx0 ht0)).congr_deriv (by field_simp; simp)
  have hu1 : HasDerivAt (fun x : ℂ => -(a / (x ^ 2 * t))) (2 * a / (z ^ 3 * t)) z := by
    convert ((hasDerivAt_const z a).div ((hasDerivAt_pow 2 z).mul_const t)
      (mul_ne_zero (pow_ne_zero 2 hz0) ht0)).neg using 1
    norm_num
    field_simp
  have hv : ∀ᶠ x in 𝓝 z, HasDerivAt
      (fun x : ℂ => (x - a) * (t - a) / ((1 - a) * (x * t - a)))
      (a * (t - a) * (t - 1) / ((1 - a) * (x * t - a) ^ 2)) x := by
    filter_upwards [hev1] with x hx
    have hx0 : x * t - a ≠ 0 := slitPlane_ne_zero hx
    have h1 : HasDerivAt (fun x : ℂ => (x - a) * (t - a)) (t - a) x := by
      simpa using ((hasDerivAt_id x).sub_const a).mul_const (t - a)
    convert h1.div ((hlin x).const_mul (1 - a)) (mul_ne_zero ha1' hx0) using 1
    field_simp
    ring
  have hv1 : HasDerivAt (fun x : ℂ => a * (t - a) * (t - 1) / ((1 - a) * (x * t - a) ^ 2))
      (-2 * t * a * (t - a) * (t - 1) / ((1 - a) * (z * t - a) ^ 3)) z := by
    convert (hasDerivAt_const z (a * (t - a) * (t - 1))).div
      (((hlin z).pow 2).const_mul (1 - a)) (mul_ne_zero ha1' (pow_ne_zero 2 hD0)) using 1
    norm_num
    field_simp
  rw [heunOperator_mul_comp_mul_comp hP hP1 hu hu1 hv hv1 hF hG]
  have e1 : (z * t - a) ^ (p - 1) = (z * t - a) ^ p / (z * t - a) := by
    rw [cpow_sub _ _ hD0, cpow_one]
  have e2 : (z * t - a) ^ (p - 1 - 1) = (z * t - a) ^ p / (z * t - a) ^ 2 := by
    rw [cpow_sub _ _ hD0, cpow_sub _ _ hD0, cpow_one, div_div, ← sq]
  have e3 : (z * t / a) ^ (q - 1) = (z * t / a) ^ q / (z * t / a) := by
    rw [cpow_sub _ _ hE0, cpow_one]
  have e4 : (z * t / a) ^ (q - 1 - 1) = (z * t / a) ^ q / (z * t / a) ^ 2 := by
    rw [cpow_sub _ _ hE0, cpow_sub _ _ hE0, cpow_one, div_div, ← sq]
  simp only [e1, e2, e3, e4]
  congr 1
  · field_simp
  · field_simp
    ring

end DLMF.Heun
