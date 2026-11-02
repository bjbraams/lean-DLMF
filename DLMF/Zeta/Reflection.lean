/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.RiemannProperties

/-!
# Reflection formulas for the Riemann zeta function (DLMF §25.4)

The functional equation 25.4.1 is Mathlib's `riemannZeta_one_sub`, and 25.4.3 in the
normalization `Λ(s) = π^{-s/2} Γ(s/2) ζ(s)` is `completedRiemannZeta_one_sub` (pointers in
`DLMF.Core.UpstreamElementary`). This file covers the rest of DLMF §25.4: the functional equation
solved for `ζ(s)` and the derivative reflection formulas. Riemann's `ξ`-function
`riemannXi` (DLMF 25.4.4) and the constant `reflectionConst` (DLMF 25.4.6) are defined in
`DLMF.Zeta.Basic.Riemann`; the basic properties of `ξ` (it is entire, the product formula 25.4.4
and the symmetry 25.4.3) are in `DLMF.Zeta.Basic.RiemannProperties`.

## Main results

* `riemannZeta_eq_reflection`: `ζ(s) = 2 (2π)^{s-1} sin(πs/2) Γ(1-s) ζ(1-s)` (DLMF 25.4.2).
* `iteratedDeriv_riemannZeta_one_sub`: the derivative reflection formula (DLMF 25.4.5).

## Implementation notes

The printed product `½ s(s-1) Γ(s/2) π^{-s/2} ζ(s)` has removable singularities at `s = 0, 1`
and at the trivial zeros, where Lean's totalized `Γ` and `ζ` give wrong values; `riemannXi` is
therefore defined through Mathlib's entire function `completedRiemannZeta₀` as
`½ s(s-1) Λ₀(s) + ½`.

As for Mathlib's 25.4.1, the Lean statements of 25.4.2 and 25.4.5 exclude, besides DLMF's
`s ≠ 0, 1`, the points where a Gamma factor has a pole (`s = 2, 3, …` in 25.4.2 and
`s = -1, -2, …` in 25.4.5): there the printed right sides are limits of `0 · ∞` forms and Lean's
value `Γ = 0` at the poles would make the statements false. The formula 25.4.5 is also stated
for `k = 0`, where it is 25.4.1.
-/

@[expose] public noncomputable section

open Complex Filter Topology Finset
open scoped Real

namespace DLMF.Zeta

/-- DLMF 25.4.2: `ζ(s) = 2 (2π)^{s-1} sin(πs/2) Γ(1-s) ζ(1-s)` for `s ≠ 0` and
`s ∉ {1, 2, 3, …}` (DLMF: `s ≠ 0, 1`; at `s = 2, 3, …` the printed right side is a removable
`0 · ∞` form). Proved from Mathlib's `riemannZeta_one_sub`. -/
@[dlmf 25.4.E2]
theorem riemannZeta_eq_reflection {s : ℂ} (hs0 : s ≠ 0) (hs : ∀ n : ℕ, s ≠ n + 1) :
    riemannZeta s =
      2 * (2 * π) ^ (s - 1) * sin (π * s / 2) * Gamma (1 - s) * riemannZeta (1 - s) := by
  have h1 : ∀ n : ℕ, 1 - s ≠ -n := fun n h => hs n (by linear_combination -h)
  have h2 : 1 - s ≠ 1 := fun h => hs0 (by linear_combination -h)
  have h := riemannZeta_one_sub h1 h2
  rw [sub_sub_cancel] at h
  rw [h, show -(1 - s) = s - 1 by ring,
    show π * (1 - s) / 2 = π / 2 - π * s / 2 by ring, cos_pi_div_two_sub]
  ring

/-- `2 (2π)^{-z} cos(πz/2) = e^{cz} + e^{c̄z}` with `c = reflectionConst`. -/
private lemma two_mul_cpow_mul_cos_eq_exp_add_exp (z : ℂ) :
    2 * (2 * π : ℂ) ^ (-z) * cos (π * z / 2) =
      cexp (reflectionConst * z) + cexp ((starRingEnd ℂ) reflectionConst * z) := by
  have hL : Complex.log (2 * π) = (Real.log (2 * π) : ℂ) := by
    rw [← ofReal_ofNat, ← ofReal_mul, ofReal_log (by positivity)]
  have hπ : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [cpow_def_of_ne_zero hπ, hL, Complex.cos, reflectionConst]
  simp only [map_sub, map_neg, map_div₀, map_mul, conj_ofReal, conj_I, map_ofNat]
  rw [show (Real.log (2 * π) : ℂ) * -z = -(Real.log (2 * π) : ℂ) * z by ring]
  have e1 : (-(Real.log (2 * π) : ℂ) - π * I / 2) * z =
      -(Real.log (2 * π) : ℂ) * z + -(π * z / 2 * I) := by ring1
  have e2 : (-(Real.log (2 * π) : ℂ) - π * -I / 2) * z =
      -(Real.log (2 * π) : ℂ) * z + π * z / 2 * I := by ring1
  rw [e1, e2, Complex.exp_add, Complex.exp_add]
  rw [show -(↑π * z / 2) * I = -(↑π * z / 2 * I) by ring]; ring1

/-- `c^j e^{cs} + c̄^j e^{c̄s} = 2 (2π)^{-s} (Re(c^j) cos(πs/2) + Im(c^j) sin(πs/2))`. -/
private lemma reflectionConst_pow_mul_exp_add_conj (j : ℕ) (s : ℂ) :
    reflectionConst ^ j * cexp (reflectionConst * s) +
        (starRingEnd ℂ) reflectionConst ^ j * cexp ((starRingEnd ℂ) reflectionConst * s) =
      2 / (2 * π) ^ s * (((reflectionConst ^ j).re : ℂ) * cos (π * s / 2) +
        ((reflectionConst ^ j).im : ℂ) * sin (π * s / 2)) := by
  have hL : Complex.log (2 * π) = (Real.log (2 * π) : ℂ) := by
    rw [← ofReal_ofNat, ← ofReal_mul, ofReal_log (by positivity)]
  have hπ : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hc : (starRingEnd ℂ) reflectionConst ^ j = (starRingEnd ℂ) (reflectionConst ^ j) :=
    (map_pow _ _ _).symm
  rw [hc]
  set w := reflectionConst ^ j with hw
  have hwe : w = (w.re : ℂ) + (w.im : ℂ) * I := (re_add_im w).symm
  have hwc : (starRingEnd ℂ) w = (w.re : ℂ) - (w.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have hcs : (2 * π : ℂ) ^ s = cexp ((Real.log (2 * π) : ℂ) * s) := by
    rw [cpow_def_of_ne_zero hπ, hL]
  have e1 : reflectionConst * s = -((Real.log (2 * π) : ℂ) * s) + -(π * s / 2) * I := by
    rw [reflectionConst]; ring1
  have e2 : (starRingEnd ℂ) reflectionConst * s =
      -((Real.log (2 * π) : ℂ) * s) + (π * s / 2) * I := by
    rw [reflectionConst]
    simp only [map_sub, map_neg, map_div₀, map_mul, conj_ofReal, conj_I, map_ofNat]
    ring1
  rw [e1, e2, Complex.exp_add, Complex.exp_add, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.exp_neg, hcs, cos_neg, sin_neg]
  rw [hwc]
  set E := cexp ((Real.log (2 * π) : ℂ) * s)
  linear_combination E⁻¹ * (cos (π * s / 2) - sin (π * s / 2) * I) * hwe +
    E⁻¹ * (-2 * (w.im : ℂ) * sin (π * s / 2)) * I_sq

/-- DLMF 25.4.5: for `k ≥ 0` (DLMF: `k ≥ 1`; `k = 0` is 25.4.1),
`(-1)^k ζ^{(k)}(1-s) = 2 (2π)^{-s} ∑_{m=0}^{k} ∑_{r=0}^{m} binom(k,m) binom(m,r)
  (Re(c^{k-m}) cos(πs/2) + Im(c^{k-m}) sin(πs/2)) Γ^{(r)}(s) ζ^{(m-r)}(s)`,
with `c = reflectionConst`. DLMF states it for `s ≠ 0, 1`; the Lean statement also excludes the
poles `s = -1, -2, …` of `Γ`, where the right side is a limit. Here `Re`, `Im` are applied to
the constants `c^{k-m}` only; `s` is complex. -/
@[dlmf 25.4.E5]
theorem iteratedDeriv_riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1)
    (k : ℕ) :
    (-1 : ℂ) ^ k * iteratedDeriv k riemannZeta (1 - s) =
      2 / (2 * π) ^ s * ∑ m ∈ range (k + 1), ∑ r ∈ range (m + 1),
        (k.choose m : ℂ) * (m.choose r : ℂ) *
          (((reflectionConst ^ (k - m)).re : ℂ) * cos (π * s / 2) +
            ((reflectionConst ^ (k - m)).im : ℂ) * sin (π * s / 2)) *
          iteratedDeriv r Gamma s * iteratedDeriv (m - r) riemannZeta s := by
  -- the open set where the functional equation holds
  set U : Set ℂ := {z | (Gamma z)⁻¹ ≠ 0} ∩ {z | z ≠ 1} with hU
  have hUo : IsOpen U :=
    (isOpen_ne_fun differentiable_one_div_Gamma.continuous continuous_const).inter
      isOpen_ne
  have hmemU : ∀ {z}, z ∈ U ↔ (∀ n : ℕ, z ≠ -n) ∧ z ≠ 1 := by
    intro z
    simp only [hU, Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, inv_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun n hn => h1 (by rw [hn, Gamma_neg_nat_eq_zero]), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Gamma_ne_zero h1, h2⟩
  have hsU : s ∈ U := hmemU.mpr ⟨hs, hs1⟩
  have hGd : DifferentiableOn ℂ Gamma U := fun z hz =>
    (differentiableAt_Gamma z (hmemU.mp hz).1).differentiableWithinAt
  have hZd : DifferentiableOn ℂ riemannZeta U := fun z hz =>
    (differentiableAt_riemannZeta (hmemU.mp hz).2).differentiableWithinAt
  have hGc : ContDiffAt ℂ k Gamma s := (hGd.contDiffOn hUo).contDiffAt (hUo.mem_nhds hsU)
  have hZc : ContDiffAt ℂ k riemannZeta s := (hZd.contDiffOn hUo).contDiffAt (hUo.mem_nhds hsU)
  set A : ℂ → ℂ := fun z => cexp (reflectionConst * z) +
    cexp ((starRingEnd ℂ) reflectionConst * z) with hA
  have hAc : ContDiffAt ℂ k A s := by fun_prop
  have heq : (fun z => riemannZeta (1 - z)) =ᶠ[𝓝 s] A * (Gamma * riemannZeta) := by
    filter_upwards [hUo.mem_nhds hsU] with z hz
    obtain ⟨h1, h2⟩ := hmemU.mp hz
    rw [riemannZeta_one_sub h1 h2]
    show _ = (cexp (reflectionConst * z) + cexp ((starRingEnd ℂ) reflectionConst * z)) *
      (Gamma z * riemannZeta z)
    rw [← two_mul_cpow_mul_cos_eq_exp_add_exp]
    ring1
  have hlhs : (-1 : ℂ) ^ k * iteratedDeriv k riemannZeta (1 - s) =
      iteratedDeriv k (fun z => riemannZeta (1 - z)) s := by
    simp only [iteratedDeriv_comp_const_sub, smul_eq_mul]
  have hAder : ∀ j : ℕ, iteratedDeriv j A s =
      reflectionConst ^ j * cexp (reflectionConst * s) +
        (starRingEnd ℂ) reflectionConst ^ j * cexp ((starRingEnd ℂ) reflectionConst * s) := by
    intro j
    rw [hA, iteratedDeriv_fun_add (by fun_prop) (by fun_prop), iteratedDeriv_cexp_const_mul,
      iteratedDeriv_cexp_const_mul]
  rw [hlhs, heq.iteratedDeriv_eq, iteratedDeriv_mul (f := A) (g := Gamma * riemannZeta) hAc
    (hGc.mul hZc : ContDiffAt ℂ k (Gamma * riemannZeta) s)]
  rw [← sum_range_reflect, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hm' : m ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [show k + 1 - 1 - m = k - m by omega,
    iteratedDeriv_mul (f := Gamma) (g := riemannZeta) (hGc.of_le ?_) (hZc.of_le ?_), hAder,
    reflectionConst_pow_mul_exp_add_conj, show k - (k - m) = m by omega, Nat.choose_symm hm',
                                                                    mul_sum, mul_sum]
  · refine sum_congr rfl fun r _ => ?_
    ring1
  all_goals exact_mod_cast (by omega : k - (k - m) ≤ k)

end DLMF.Zeta
