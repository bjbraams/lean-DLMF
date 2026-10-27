/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.P2mConnection

/-!
# Modified Mathieu functions: connection formulas (DLMF §28.22)

The radial functions of the first and second kinds in terms of `Ce_m`, `Se_m`, `Fe_m`, `Ge_m`
with the joining factors `g_{e,m}`, `g_{o,m}`, `f_{e,m}`, `f_{o,m}` (defined in
`DLMF.Mathieu.Modified.Defs` by 28.22.5–28.22.10), and, for noninteger `ν`, `M^{(1)}_ν` in
terms of `Me_ν` and `M^{(2)}_ν` in terms of `M^{(1)}_{±ν}`. All formulas were checked
numerically (`h = 1.2`, `m ≤ 4`, `ν = 0.3`). Real `h > 0` throughout (DLMF's joining factors
are defined for real `h`); `q = h²`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

/-- **Connection formula** (DLMF 28.22.1), `h > 0`, `m = 0, 1, …`:
`Mc^{(1)}_m(z, h) = √(2/π) (g_{e,m}(h) ce_m(0, h²))⁻¹ Ce_m(z, h²)`. -/
@[dlmf 28.22.E1]
theorem radialMathieuMc_one_eq (m : ℕ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMc 1 m z h = Real.sqrt (2 / π) / (mathieuJoinGe m h * mathieuCe m 0 (h ^ 2)) *
      modMathieuCe m z ((h ^ 2 : ℝ) : ℂ) :=
  p2m_radialMathieuMc_one_eq m hh z

/-- **Connection formula** (DLMF 28.22.2), `h > 0`, `m = 1, 2, …`:
`Ms^{(1)}_m(z, h) = √(2/π) (g_{o,m}(h) se'_m(0, h²))⁻¹ Se_m(z, h²)`. -/
@[dlmf 28.22.E2]
theorem radialMathieuMs_one_eq {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMs 1 m z h = Real.sqrt (2 / π) /
      (mathieuJoinGo m h * deriv (fun x => mathieuSe m x (h ^ 2)) 0) *
      modMathieuSe m z ((h ^ 2 : ℝ) : ℂ) :=
  p2m_radialMathieuMs_one_eq hm hh z

/-- **Connection formula** (DLMF 28.22.3), `h > 0`, `m = 0, 1, …`:
`Mc^{(2)}_m(z, h) = √(2/π) (g_{e,m} ce_m(0, h²))⁻¹
(-f_{e,m} Ce_m(z, h²) + 2/(π C_m(h²)) Fe_m(z, h²))`. -/
@[dlmf 28.22.E3]
theorem radialMathieuMc_two_eq (m : ℕ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMc 2 m z h = Real.sqrt (2 / π) / (mathieuJoinGe m h * mathieuCe m 0 (h ^ 2)) *
      (-mathieuJoinFe m h * modMathieuCe m z ((h ^ 2 : ℝ) : ℂ) +
        2 / (π * mathieuFeC m (h ^ 2)) * modMathieuFe m z (h ^ 2)) :=
  p2m_radialMathieuMc_two_eq m hh z

/-- **Connection formula** (DLMF 28.22.4), `h > 0`, `m = 1, 2, …`:
`Ms^{(2)}_m(z, h) = √(2/π) (g_{o,m} se'_m(0, h²))⁻¹
(-f_{o,m} Se_m(z, h²) - 2/(π S_m(h²)) Ge_m(z, h²))`. -/
@[dlmf 28.22.E4]
theorem radialMathieuMs_two_eq {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMs 2 m z h = Real.sqrt (2 / π) /
      (mathieuJoinGo m h * deriv (fun x => mathieuSe m x (h ^ 2)) 0) *
      (-mathieuJoinFo m h * modMathieuSe m z ((h ^ 2 : ℝ) : ℂ) -
        2 / (π * mathieuGeS m (h ^ 2)) * modMathieuGe m z (h ^ 2)) :=
  p2m_radialMathieuMs_two_eq hm hh z

/-- An even function differentiable at `0` has derivative `0` there. -/
lemma p1c_deriv_zero_of_even {f : ℂ → ℂ} (hf : DifferentiableAt ℂ f 0)
    (he : ∀ z, f (-z) = f z) : deriv f 0 = 0 := by
  have h1 : HasDerivAt (fun z => f (-z)) (deriv f (-0) * -1) 0 :=
    (by simpa using hf.hasDerivAt : HasDerivAt f (deriv f (-0)) (-0)).comp (0 : ℂ)
      (hasDerivAt_neg (0 : ℂ))
  have h2 : (fun z => f (-z)) = f := funext he
  rw [h2] at h1
  have := h1.unique hf.hasDerivAt
  simp at this
  linear_combination -this / 2

/-- `(√(2/π))² = 2/π` in `ℂ`. -/
lemma p1c_sqrt_two_div_pi_sq : ((Real.sqrt (2 / π) : ℝ) : ℂ) ^ 2 = 2 / π := by
  rw [← ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring

/-- **Values at `z = 0`** (DLMF 28.22.11), `h > 0`:
`Mc^{(2)'}_m(0, h) = √(2/π) g_{e,m}(h)` and `Ms^{(2)}_m(0, h) = -√(2/π) g_{o,m}(h)` (`m ≥ 1`
for the second). -/
@[dlmf 28.22.E11]
theorem radialMathieu_two_zero (m : ℕ) {h : ℝ} (hh : 0 < h) :
    deriv (fun z => radialMathieuMc 2 m z h) 0 = Real.sqrt (2 / π) * mathieuJoinGe m h ∧
      (m ≠ 0 → radialMathieuMs 2 m 0 h = -(Real.sqrt (2 / π) * mathieuJoinGo m h)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs := p1c_sqrt_two_div_pi_sq
  have hs0 : (Real.sqrt (2 / π) : ℂ) ≠ 0 := by
    intro h0; rw [h0] at hs; simp at hs; exact div_ne_zero two_ne_zero hπ hs.symm
  constructor
  · have hW := (modMathieuM_wronskian_two (ν := (m : ℝ)) hh 0).1
    simp only [Complex.ofReal_natCast] at hW
    set A := (Real.sqrt (2 / π) : ℂ) / (mathieuJoinGe m h * mathieuCe m 0 (h ^ 2))
    have e1 : (fun z => modMathieuM 1 (m : ℂ) z h) = fun z =>
        A * mathieuCe m (I * z) (h ^ 2) := by
      funext z
      rw [← radialMathieuMc, radialMathieuMc_one_eq m hh z, modMathieuCe_natCast]
    have hce := (isMathieuSolution_mathieuCe m (h ^ 2)).differentiable
    have dce : deriv (fun z => mathieuCe m z (h ^ 2)) 0 = 0 :=
      p1c_deriv_zero_of_even (hce 0) (fun z => mathieuCe_neg m z (h ^ 2))
    have hCe : HasDerivAt (fun z => mathieuCe m (I * z) (h ^ 2)) 0 0 := by
      have := ((hce (I * 0)).hasDerivAt).comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul I)
      simp only [mul_zero, dce, zero_mul, mul_one] at this
      exact this
    have d1 := hCe.const_mul A
    have v1 := congrFun e1 0
    simp only [mul_zero] at v1
    rw [m28c_wronskian, e1, d1.deriv, v1] at hW
    simp only [mul_zero, zero_mul, sub_zero] at hW
    change deriv (fun z => modMathieuM 2 (m : ℂ) z h) 0 = _
    have hc : mathieuCe m 0 (h ^ 2) ≠ 0 := by
      rintro hc; rw [hc] at hW; simp at hW; exact div_ne_zero two_ne_zero hπ hW.symm
    have hg : mathieuJoinGe m h ≠ 0 := by
      rintro hg; simp [A, hg] at hW; exact div_ne_zero two_ne_zero hπ hW.symm
    simp only [A] at hW
    field_simp at hW
    have hs' : (Real.sqrt (2 / π) : ℂ) ^ 2 * π = 2 := by rw [hs]; field_simp
    apply mul_left_cancel₀ (mul_ne_zero hs0 hπ)
    linear_combination hW - mathieuJoinGe m h * hs'
  · intro hm
    have hW := (modMathieuM_wronskian_two (ν := -(m : ℝ)) hh 0).1
    push_cast at hW
    have hP : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    set B := (Real.sqrt (2 / π) : ℂ) /
      (mathieuJoinGo m h * deriv (fun x => mathieuSe m x (h ^ 2)) 0)
    have e1 : (fun z => modMathieuM 1 (-(m : ℂ)) z h) = fun z =>
        (-1 : ℂ) ^ m * (B * (-I * mathieuSe m (I * z) (h ^ 2))) := by
      funext z
      have := radialMathieuMs_one_eq hm hh z
      rw [radialMathieuMs, modMathieuSe_natCast hm] at this
      rw [← this]; linear_combination (-modMathieuM 1 (-(m : ℂ)) z h) * hP
    have e2 : modMathieuM 2 (-(m : ℂ)) 0 h = (-1 : ℂ) ^ m * radialMathieuMs 2 m 0 h := by
      rw [radialMathieuMs]; linear_combination (-modMathieuM 2 (-(m : ℂ)) 0 h) * hP
    have hse := (isMathieuSolution_mathieuSe m (h ^ 2)).differentiable
    have hSe : HasDerivAt (fun z => -I * mathieuSe m (I * z) (h ^ 2))
        (deriv (fun z => mathieuSe m z (h ^ 2)) 0) 0 := by
      have := (((hse (I * 0)).hasDerivAt).comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_mul I)).const_mul (-I)
      simp only [mul_zero, mul_one] at this
      refine this.congr_deriv ?_
      linear_combination (-(deriv (fun z => mathieuSe m z (h ^ 2)) 0)) * I_sq
    have d1 := (hSe.const_mul B).const_mul ((-1 : ℂ) ^ m)
    have v1 := congrFun e1 0
    simp only [mul_zero] at v1
    have hse0 : mathieuSe m 0 (h ^ 2) = 0 := by
      have := mathieuSe_neg m 0 (h ^ 2); rw [neg_zero] at this; linear_combination this / 2
    rw [m28c_wronskian, e1, d1.deriv, v1, e2, hse0] at hW
    simp only [mul_zero, zero_mul, zero_sub] at hW
    have hc : deriv (fun x => mathieuSe m x (h ^ 2)) 0 ≠ 0 := by
      rintro hc; rw [hc] at hW; simp at hW; exact div_ne_zero two_ne_zero hπ hW.symm
    have hg : mathieuJoinGo m h ≠ 0 := by
      rintro hg; simp [B, hg] at hW; exact div_ne_zero two_ne_zero hπ hW.symm
    simp only [B] at hW
    field_simp at hW
    have hs' : (Real.sqrt (2 / π) : ℂ) ^ 2 * π = 2 := by rw [hs]; field_simp
    have hP2 : ((-1 : ℂ) ^ m) ^ 2 = 1 := by rw [sq]; exact hP
    rw [hP2, one_mul] at hW
    apply mul_left_cancel₀ (mul_ne_zero hs0 hπ)
    linear_combination -hW + mathieuJoinGo m h * hs'

/-- **Initial values of the second solutions** (DLMF 28.22.12), `h > 0`:
`fe'_m(0, h²) = ½π C_m(h²) g_{e,m}(h)² ce_m(0, h²)` and
`ge_m(0, h²) = ½π S_m(h²) g_{o,m}(h)² se'_m(0, h²)` (`m ≥ 1` for the second). -/
@[dlmf 28.22.E12]
theorem mathieuFe_ge_zero_eq_joinG (m : ℕ) {h : ℝ} (hh : 0 < h) :
    deriv (fun z => mathieuFe m z (h ^ 2)) 0 =
        π / 2 * mathieuFeC m (h ^ 2) * mathieuJoinGe m h ^ 2 * mathieuCe m 0 (h ^ 2) ∧
      (m ≠ 0 → mathieuGe m 0 (h ^ 2) = π / 2 * mathieuGeS m (h ^ 2) * mathieuJoinGo m h ^ 2 *
        deriv (fun z => mathieuSe m z (h ^ 2)) 0) := by
  have hq : h ^ 2 ≠ 0 := by positivity
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs := p1c_sqrt_two_div_pi_sq
  constructor
  · -- the Wronskian `𝒲{Mc^{(1)}_m, Mc^{(2)}_m}(0) = 2/π`
    have hW := (modMathieuM_wronskian_two (ν := (m : ℝ)) hh 0).1
    simp only [Complex.ofReal_natCast] at hW
    have e1 : (fun z => modMathieuM 1 (m : ℂ) z h) = fun z =>
        Real.sqrt (2 / π) / (mathieuJoinGe m h * mathieuCe m 0 (h ^ 2)) *
          mathieuCe m (I * z) (h ^ 2) := by
      funext z
      rw [← radialMathieuMc, radialMathieuMc_one_eq m hh z, modMathieuCe_natCast]
    have e2 : (fun z => modMathieuM 2 (m : ℂ) z h) = fun z =>
        Real.sqrt (2 / π) / (mathieuJoinGe m h * mathieuCe m 0 (h ^ 2)) *
          (-mathieuJoinFe m h * mathieuCe m (I * z) (h ^ 2) +
            2 / (π * mathieuFeC m (h ^ 2)) * (-I * mathieuFe m (I * z) (h ^ 2))) := by
      funext z
      rw [← radialMathieuMc, radialMathieuMc_two_eq m hh z, modMathieuCe_natCast]; rfl
    have hce := (isMathieuSolution_mathieuCe m (h ^ 2)).differentiable
    have hfe := (isMathieuSolution_mathieuFe (n := m) (q := h ^ 2) (by tauto)).differentiable
    have dce : deriv (fun z => mathieuCe m z (h ^ 2)) 0 = 0 :=
      p1c_deriv_zero_of_even (hce 0) (fun z => mathieuCe_neg m z (h ^ 2))
    have hCe : HasDerivAt (fun z => mathieuCe m (I * z) (h ^ 2)) 0 0 := by
      have := ((hce (I * 0)).hasDerivAt).comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul I)
      simp only [mul_zero, dce, zero_mul, mul_one] at this
      exact this
    have hFe : HasDerivAt (fun z => -I * mathieuFe m (I * z) (h ^ 2))
        (deriv (fun z => mathieuFe m z (h ^ 2)) 0) 0 := by
      have := (((hfe (I * 0)).hasDerivAt).comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_mul I)).const_mul (-I)
      simp only [mul_zero, mul_one] at this
      refine this.congr_deriv ?_
      linear_combination (-(deriv (fun z => mathieuFe m z (h ^ 2)) 0)) * I_sq
    set A := (Real.sqrt (2 / π) : ℂ) / (mathieuJoinGe m h * mathieuCe m 0 (h ^ 2))
    set K := 2 / (π * mathieuFeC m (h ^ 2))
    have d1 := hCe.const_mul A
    have d2 : HasDerivAt (fun z => A * (-mathieuJoinFe m h * mathieuCe m (I * z) (h ^ 2) +
        K * (-I * mathieuFe m (I * z) (h ^ 2))))
        (A * (-mathieuJoinFe m h * 0 + K * deriv (fun z => mathieuFe m z (h ^ 2)) 0)) 0 :=
      ((hCe.const_mul (-mathieuJoinFe m h)).add (hFe.const_mul K)).const_mul A
    have v1 := congrFun e1 0
    simp only [mul_zero] at v1
    rw [m28c_wronskian, e1, e2, d1.deriv, d2.deriv, v1] at hW
    simp only [mul_zero, zero_mul, sub_zero, zero_add] at hW
    have hA : A ≠ 0 := by
      rintro hA; rw [hA] at hW; simp at hW; exact div_ne_zero two_ne_zero hπ hW.symm
    have hK : K ≠ 0 := by
      rintro hK; rw [hK] at hW; simp at hW; exact div_ne_zero two_ne_zero hπ hW.symm
    have hg : mathieuJoinGe m h ≠ 0 := by rintro hg; apply hA; simp [A, hg]
    have hc : mathieuCe m 0 (h ^ 2) ≠ 0 := by rintro hc; apply hA; simp [A, hc]
    have hC : mathieuFeC m (h ^ 2) ≠ 0 := by rintro hC; apply hK; simp [K, hC]
    simp only [A, K] at hW
    field_simp at hW
    rw [hs] at hW
    field_simp at hW
    linear_combination hW / 2
  · intro hm
    have hW := (modMathieuM_wronskian_two (ν := -(m : ℝ)) hh 0).1
    push_cast at hW
    have hP : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    set B := (Real.sqrt (2 / π) : ℂ) /
      (mathieuJoinGo m h * deriv (fun x => mathieuSe m x (h ^ 2)) 0)
    set L := 2 / (π * mathieuGeS m (h ^ 2))
    have e1 : (fun z => modMathieuM 1 (-(m : ℂ)) z h) = fun z =>
        (-1 : ℂ) ^ m * (B * (-I * mathieuSe m (I * z) (h ^ 2))) := by
      funext z
      have := radialMathieuMs_one_eq hm hh z
      rw [radialMathieuMs, modMathieuSe_natCast hm] at this
      rw [← this]; linear_combination (-modMathieuM 1 (-(m : ℂ)) z h) * hP
    have e2 : (fun z => modMathieuM 2 (-(m : ℂ)) z h) = fun z =>
        (-1 : ℂ) ^ m * (B * (-mathieuJoinFo m h * (-I * mathieuSe m (I * z) (h ^ 2)) -
          L * mathieuGe m (I * z) (h ^ 2))) := by
      funext z
      have := radialMathieuMs_two_eq hm hh z
      rw [radialMathieuMs, modMathieuSe_natCast hm, modMathieuGe] at this
      rw [← this]; linear_combination (-modMathieuM 2 (-(m : ℂ)) z h) * hP
    have hse := (isMathieuSolution_mathieuSe m (h ^ 2)).differentiable
    have hge := (isMathieuSolution_mathieuGe m (h ^ 2)).differentiable
    have hSe : HasDerivAt (fun z => -I * mathieuSe m (I * z) (h ^ 2))
        (deriv (fun z => mathieuSe m z (h ^ 2)) 0) 0 := by
      have := (((hse (I * 0)).hasDerivAt).comp (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_mul I)).const_mul (-I)
      simp only [mul_zero, mul_one] at this
      refine this.congr_deriv ?_
      linear_combination (-(deriv (fun z => mathieuSe m z (h ^ 2)) 0)) * I_sq
    have hGe : HasDerivAt (fun z => mathieuGe m (I * z) (h ^ 2))
        (deriv (fun z => mathieuGe m z (h ^ 2)) (I * 0) * I) 0 := by
      have := ((hge (I * 0)).hasDerivAt).comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul I)
      simp only [mul_one] at this
      exact this
    have d1 := (hSe.const_mul B).const_mul ((-1 : ℂ) ^ m)
    have d2 : HasDerivAt (fun z => (-1 : ℂ) ^ m * (B * (-mathieuJoinFo m h *
        (-I * mathieuSe m (I * z) (h ^ 2)) - L * mathieuGe m (I * z) (h ^ 2))))
        ((-1 : ℂ) ^ m * (B * (-mathieuJoinFo m h * deriv (fun z => mathieuSe m z (h ^ 2)) 0 -
          L * (deriv (fun z => mathieuGe m z (h ^ 2)) (I * 0) * I)))) 0 :=
      (((hSe.const_mul (-mathieuJoinFo m h)).sub (hGe.const_mul L)).const_mul B).const_mul _
    have v1 := congrFun e1 0
    have v2 := congrFun e2 0
    simp only [mul_zero] at v1 v2
    rw [m28c_wronskian, e1, e2, d1.deriv, d2.deriv, v1, v2] at hW
    have hse0 : mathieuSe m 0 (h ^ 2) = 0 := by
      have := mathieuSe_neg m 0 (h ^ 2); rw [neg_zero] at this; linear_combination this / 2
    rw [hse0] at hW
    simp only [mul_zero, zero_mul, zero_sub] at hW
    have hB : B ≠ 0 := by
      rintro hB; rw [hB] at hW; simp at hW; exact div_ne_zero two_ne_zero hπ hW.symm
    have hL : L ≠ 0 := by
      rintro hL; rw [hL] at hW; simp at hW; exact div_ne_zero two_ne_zero hπ hW.symm
    have hg : mathieuJoinGo m h ≠ 0 := by rintro hg; apply hB; simp [B, hg]
    have hc : deriv (fun x => mathieuSe m x (h ^ 2)) 0 ≠ 0 := by
      rintro hc; apply hB; simp [B, hc]
    have hS : mathieuGeS m (h ^ 2) ≠ 0 := by rintro hS; apply hL; simp [L, hS]
    simp only [B, L] at hW
    field_simp at hW
    rw [hs] at hW
    field_simp at hW
    linear_combination hW / 2 - mathieuGe m 0 (h ^ 2) * hP

/-- Mathieu's equation is invariant under `t ↦ -t`. -/
lemma p1c_isMathieuSolution_neg {a q : ℂ} {w : ℂ → ℂ} (hw : IsMathieuSolution a q w) :
    IsMathieuSolution a q (fun t => w (-t)) := by
  have hd : ∀ t, HasDerivAt (fun t => w (-t)) (-deriv w (-t)) t := fun t => by
    have := ((hw.differentiable (-t)).hasDerivAt).comp t (hasDerivAt_neg t)
    convert this using 1 <;> first | rfl | ring
  refine ⟨fun t => (hd t).differentiableAt, fun t => ?_⟩
  have he : deriv (fun t => w (-t)) = fun t => -deriv w (-t) := funext fun t => (hd t).deriv
  rw [he]
  have h2 := (((hw.hasDerivAt_deriv (-t)).comp t (hasDerivAt_neg t))).neg
  convert h2 using 1
  · funext t; rfl
  rw [show 2 * -t = -(2 * t) by ring, Complex.cos_neg]; ring

/-- A Floquet solution with multiplier `ρ`, `ρ² ≠ 1`, vanishing at `0` is identically zero. -/
lemma p1c_floquet_eq_zero {a q ρ : ℂ} {w : ℂ → ℂ} (hw : IsMathieuSolution a q w)
    (h0 : w 0 = 0) (hρ : ∀ t, w (t + π) = ρ * w t) (hρ0 : ρ ≠ 0) (hρ1 : ρ ^ 2 ≠ 1) :
    w = 0 := by
  have hneg := p1c_isMathieuSolution_neg hw
  have hm := hw.const_mul (-1)
  have hd : deriv (fun t => w (-t)) 0 = deriv (fun t => -1 * w t) 0 := by
    have h1 : HasDerivAt (fun t => w (-t)) (-deriv w (-0)) 0 := by
      have := ((hw.differentiable (-0)).hasDerivAt).comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
      convert this using 1 <;> first | rfl | ring
    rw [h1.deriv, ((hw.differentiable 0).hasDerivAt.const_mul (-1)).deriv]
    simp
  have heq := hneg.eq_of_initial hm (z₀ := 0) (by simp [h0]) hd
  funext t
  have e1 := congrFun heq (t + π)
  have e2 : w (-(t + π)) = ρ⁻¹ * w (-t) := by
    have := hρ (-(t + π)); rw [show -(t + π) + π = -t by ring] at this
    rw [this]; field_simp
  have e3 := congrFun heq t
  rw [e2, e3, hρ t] at e1
  have : (ρ ^ 2 - 1) * w t = 0 := by
    have := congrArg (fun x => ρ * x) e1; field_simp at this
    linear_combination this
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hρ1
  · simpa using h

/-- **Noninteger order** (DLMF 28.22.13), `ν` real, `ν ∉ ℤ`, `h > 0`, `me_ν(0, h²) ≠ 0`:
`M^{(1)}_ν(z, h) = (M^{(1)}_ν(0, h) / me_ν(0, h²)) Me_ν(z, h²)`. (DLMF's further remark, that
`M^{(1)}_ν(0, h)` is best computed from 28.24.1 with an index of maximal `|c^ν_{2n}|`, is
computational advice; cf. `modMathieuIndex`.) -/
@[dlmf 28.22.E13]
theorem modMathieuM_one_eq_modMathieuMe {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ}
    (hh : 0 < h) (hme : mathieuMe ν 0 ((h : ℂ) ^ 2) ≠ 0) (z : ℂ) :
    modMathieuM 1 ν z h =
      modMathieuM 1 ν 0 h / mathieuMe ν 0 ((h : ℂ) ^ 2) * modMathieuMe ν z ((h : ℂ) ^ 2) := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hM := p1c_isMathieuSolution_comp
    (isModMathieuSolution_modMathieuM 1 le_rfl (by norm_num) (p1c_admissible_real hν h) hh')
    (c := I) I_sq
  have hF := (isFloquetSolution_mathieuMe (p1c_not_int_cast hν) (p1c_normal_real hν h)).1
  set K := modMathieuM 1 ν 0 h / mathieuMe ν 0 ((h : ℂ) ^ 2)
  have hW := hM.add (hF.1.const_mul (-K))
  have hW0 := p1c_floquet_eq_zero hW (ρ := Complex.exp (π * I * ν))
    (by simp only [mul_zero, K]; field_simp; ring)
    (fun t => by
      have h1 := modMathieuM_one_add_int_mul_pi_I (ν : ℂ) (I * t) h 1
      simp only [Int.cast_one, one_mul, mul_one] at h1
      have h2 : mathieuMe ν (t + π) ((h : ℂ) ^ 2) =
          Complex.exp (π * I * ν) * mathieuMe ν t ((h : ℂ) ^ 2) := hF.2.2 t
      rw [show I * (t + π) = I * t + π * I by ring, h1, h2]
      rw [show I * π * ν = π * I * ν by ring]; ring)
    (Complex.exp_ne_zero _)
    (by
      rw [← Complex.exp_nat_mul, Ne, Complex.exp_eq_one_iff]
      rintro ⟨k, hk⟩
      apply hν k
      have hπ : (π : ℂ) * I ≠ 0 := by simp [Real.pi_ne_zero]
      have : ((ν : ℂ)) = k := by
        apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hπ)
        push_cast at hk; linear_combination hk
      exact_mod_cast this.symm)
  have := congrFun hW0 (-I * z)
  simp only [Pi.zero_apply] at this
  rw [show I * (-I * z) = z by ring_nf; rw [I_sq]; ring] at this
  rw [modMathieuMe]
  linear_combination this

/-- Term-wise form of 28.22.14 (with the `-ν` series reindexed by `ℓ ↦ -ℓ`). -/
lemma p1c_modMathieuTerm_two_eq {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) (z h : ℂ) (n ℓ : ℤ) :
    modMathieuTerm 2 ν z h n ℓ = Complex.cot (ν * π) * modMathieuTerm 1 ν z h n ℓ -
      modMathieuTerm 1 (-(ν : ℂ)) z h (-n) (-ℓ) / Complex.sin (ν * π) := by
  have hk := p1c_not_int_add hν (n + ℓ)
  have hk' : ¬ ∃ j : ℤ, (ν : ℂ) + n + ℓ = j := by
    rw [show (ν : ℂ) + n + ℓ = ν + ((n + ℓ : ℤ) : ℂ) by push_cast; ring]; exact hk
  have hs0 := p1c_sin_ne_zero hν 0
  simp only [Int.cast_zero, add_zero] at hs0
  have ecos := p1c_cos_add_int ν (n + ℓ)
  have esin := p1c_sin_add_int ν (n + ℓ)
  push_cast at ecos esin
  rw [← add_assoc] at ecos esin
  simp only [modMathieuTerm, mathieuCylExp]
  rw [p1c_besselYExp_of_not_int hk', ecos, esin, Complex.cot_eq_cos_div_sin,
    mathieuMeCoeff_neg (p1c_not_int_cast hν),
    show (-ℓ - -n : ℤ) = -(ℓ - n) by ring, p1c_besselJExp_neg_intCast,
    show -(ν : ℂ) + ((-n : ℤ) : ℂ) + ((-ℓ : ℤ) : ℂ) = -(ν + n + ℓ) by push_cast; ring]
  have hP : (-1 : ℂ) ^ (n + ℓ) * (-1 : ℂ) ^ (ℓ - n) = 1 := by
    rw [← zpow_add₀ (by norm_num), show n + ℓ + (ℓ - n) = 2 * ℓ by ring, zpow_mul]; simp
  have hm : (-1 : ℂ) ^ (-ℓ) = (-1 : ℂ) ^ ℓ := by
    rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]
  rw [hm]
  have hPne : (-1 : ℂ) ^ (n + ℓ) ≠ 0 := zpow_ne_zero _ (by norm_num)
  field_simp
  linear_combination mathieuMeCoeff ν (h ^ 2) ℓ *
    besselJExp ((ℓ - n : ℤ) : ℂ) h (-z) * besselJExp (-(ν + n + ℓ)) h z * hP

/-- **Noninteger order** (DLMF 28.22.14), `ν` real, `ν ∉ ℤ`, `h > 0`:
`M^{(2)}_ν(z, h) = cot(νπ) M^{(1)}_ν(z, h) - M^{(1)}_{-ν}(z, h) / sin(νπ)`. -/
@[dlmf 28.22.E14]
theorem modMathieuM_two_eq {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ} (hh : 0 < h)
    (z : ℂ) :
    modMathieuM 2 ν z h = Complex.cot (ν * π) * modMathieuM 1 ν z h -
      modMathieuM 1 (-(ν : ℂ)) z h / Complex.sin (ν * π) := by
  have hadm := p1c_admissible_real hν h
  have hadm' : ModMathieuAdmissible (-(ν : ℂ)) h := by
    have := p1c_admissible_real (p1c_neg_not_int hν) h; push_cast at this; exact this
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hc := p1c_coeff_index_ne_zero hν h
  set n := modMathieuIndex ν h
  have h1 := summable_modMathieuTerm 1 le_rfl (by norm_num) hadm hh' n z
  have hneg := hasSum_modMathieuTerm 1 le_rfl (by norm_num) hadm' hh' (-n) z
  rw [← (Equiv.neg ℤ).hasSum_iff] at hneg
  rw [mathieuMeCoeff_neg (p1c_not_int_cast hν)] at hneg
  have hsum := ((h1.hasSum.mul_left (Complex.cot (ν * π))).sub (hneg.div_const
    (Complex.sin (ν * π))))
  have e : (fun ℓ => Complex.cot (ν * π) * modMathieuTerm 1 ν z h n ℓ -
      ((modMathieuTerm 1 (-(ν : ℂ)) z h (-n)) ∘ (Equiv.neg ℤ)) ℓ / Complex.sin (ν * π)) =
      modMathieuTerm 2 ν z h n := by
    funext ℓ; rw [p1c_modMathieuTerm_two_eq hν]; rfl
  rw [e] at hsum
  have e2 : modMathieuM 2 ν z h = (mathieuMeCoeff ν ((h : ℂ) ^ 2) n)⁻¹ *
      ∑' ℓ, modMathieuTerm 2 ν z h n ℓ := rfl
  have e1 : modMathieuM 1 ν z h = (mathieuMeCoeff ν ((h : ℂ) ^ 2) n)⁻¹ *
      ∑' ℓ, modMathieuTerm 1 ν z h n ℓ := rfl
  rw [e2, hsum.tsum_eq, e1]
  field_simp

end DLMF.Mathieu
