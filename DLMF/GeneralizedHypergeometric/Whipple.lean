/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.GeneralizedHypergeometric.Basic
import DLMF.GeneralizedHypergeometric.Thomae
import DLMF.Hypergeometric.Identities.Dixon
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic
/-!
# Whipple summation at unit argument

Whipple’s sum, DLMF 16.4.7, follows from the Thomae transformation and Dixon’s sum.
Analytic continuation removes the auxiliary Gamma exclusions first in the complementary
upper parameters, then in the remaining parameter for terminating series. In particular,
the formula retains all integer complementary upper parameters outside the convergence
half - space.

* `WhippleSummation.generalizedHypergeometric_eq`: the complete Whipple formula.

The proof reuses `dixon_sum` and the endpoint beta - integral proof of the Thomae
transformation in `DLMF.GeneralizedHypergeometric.Thomae`.
-/
public noncomputable section
open Complex Filter Set Finset
open scoped Topology Real
namespace DLMF.Hypergeometric.WhippleSummation

/-- Dixon’s sum expressed using the native generalized hypergeometric function. -/
lemma generalizedHypergeometric_dixon {a b c : ℂ} (h : 0 < (1 + a / 2 - b - c).re)
    (ha : ∀ n : ℕ, 1 + a / 2 ≠ -(n: ℂ))
    (hb : ∀ n : ℕ, 1 + a - b ≠ -(n: ℂ)) (hc : ∀ n : ℕ, 1 + a - c ≠ -(n: ℂ)) :
    generalizedHypergeometric {a, b, c} {1 + a - b, 1 + a - c} 1 =
      Gamma (1 + a / 2) * Gamma (1 + a - b) * Gamma (1 + a - c) * Gamma (1 + a / 2 - b - c) /
        (Gamma (1 + a) * Gamma (1 + a / 2 - b) * Gamma (1 + a / 2 - c) *
          Gamma (1 + a - b - c)) := by
  have hden : LowerParametersRegular {1 + a - b, 1 + a - c} := by
    intro u hu n
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hu
    rcases hu with rfl|rfl
    · exact hb n
    · exact hc n
  have hex : 0 < (parameterExcess {a, b, c} {1 + a - b, 1 + a - c}).re := by
    simp only [parameterExcess, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton,
      add_re, sub_re, one_re, div_ofNat_re] at h ⊢
    linarith
  have hsum := generalizedHypergeometric_one_hasSum (a := {a, b, c})
    (b := {1 + a - b, 1 + a - c}) (by simp) hden hex
  rw [← hsum.tsum_eq]
  convert dixon_sum h ha hb hc using 1
  apply tsum_congr
  intro n
  simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  ring

/-- Whipple’s formula where the auxiliary Gamma factors are regular. -/
lemma generalizedHypergeometric_eq_of_regular_parameters {a c d : ℂ} (hc : 0 < c.re)
    (hd : LowerParametersRegular {d, 2 * c - d + 1}) (hgap : 0 < (2 * c - d + 1 - a).re)
    (hpar : LowerParametersRegular
      {a + c, (a + d + 1) / 2, a + d, (a + d) / 2, (d - a + 1) / 2, c + (a - d + 1) / 2}) :
    generalizedHypergeometric {a, 1 - a, c} {d, 2 * c - d + 1} 1 =
      (Real.pi : ℂ) * Gamma d * Gamma (2 * c - d + 1) * (2: ℂ) ^ (1 - 2 * c) /
        (Gamma (c + (a - d + 1) / 2) * Gamma (c + 1 - (a + d) / 2)*
          Gamma ((a + d) / 2) * Gamma ((d - a + 1) / 2)) := by
  have hlow : LowerParametersRegular {d, 2 * c - d + 1, d + (2 * c - d + 1) - (1 - a) - c} := by
    intro u hu n
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hu
    rcases hu with rfl|rfl|rfl
    · exact hd _ (by simp) n
    · exact hd _ (by simp) n
    · rw [show d + (2 * c - d + 1) - (1 - a) - c = a + c by ring]
      exact hpar _ (by simp) n
  have H := ThomaeTransformation.generalizedHypergeometric_eq (a := a) (b := 1 - a)
    (c := c) hlow (by convert hc using 1; congr 1; ring) hgap
  rw [show d + (2 * c - d + 1) - a - (1 - a) - c = c by ring,
    show d + (2 * c - d + 1) - (1 - a) - c = a + c by ring,
    show d - (1 - a) = a + d - 1 by ring] at H
  have hdc : 0 < (1 + (a + d - 1) / 2 - a - (d - c)).re := by
    rw [show 1 + (a + d - 1) / 2 - a - (d - c) = (2 * c - d + 1 - a) / 2 by ring, div_ofNat_re]
    exact div_pos hgap (by norm_num)
  have hD := generalizedHypergeometric_dixon (a := a + d - 1) (b := a) (c := d - c) hdc
    (by intro n; rw [show 1 + (a + d - 1) / 2 = (a + d + 1) / 2 by ring]; exact hpar _ (by simp) n)
    (by intro n; rw [show 1 + (a + d - 1) - a = d by ring]; exact hd _ (by simp) n)
    (by intro n; rw [show 1 + (a + d - 1) - (d - c) = a + c by ring]; exact hpar _ (by simp) n)
  rw [show 1 + (a + d - 1) / 2 - a - (d - c) = c + (1 - a - d) / 2 by ring,
    show 1 + (a + d - 1) / 2 - a = (d - a + 1) / 2 by ring,
    show 1 + (a + d - 1) / 2 - (d - c) = c + (a - d + 1) / 2 by ring,
    show 1 + (a + d - 1) - a - (d - c) = c by ring,
    show 1 + (a + d - 1) - a = d by ring, show 1 + (a + d - 1) - (d - c) = a + c by ring,
    show 1 + (a + d - 1) = a + d by ring,
    show 1 + (a + d - 1) / 2 = (a + d + 1) / 2 by ring] at hD
  have hperm : ({a, a + d - 1, d - c}:Multiset ℂ)={a + d - 1, a, d - c} := by
    simp only [Multiset.insert_eq_cons]
    rw [Multiset.cons_swap a (a + d - 1)]
  rw [hperm, hD] at H
  have hGc := Gamma_ne_zero_of_re_pos hc
  have hGaC := Gamma_ne_zero (hpar (a + c) (by simp))
  have hGy := Gamma_ne_zero (hpar ((a + d) / 2) (by simp))
  have hG2y := Gamma_ne_zero (hpar (a + d) (by simp))
  have hGv := Gamma_ne_zero (hpar ((d - a + 1) / 2) (by simp))
  have hu : 0 < (c + (1 - a - d) / 2).re := by
    rw [show c + (1 - a - d) / 2 = (2 * c - d + 1 - a) / 2 by ring, div_ofNat_re]
    exact div_pos hgap (by norm_num)
  have huv : 0 < (c + 1 - (a + d) / 2).re := by
    rw [show c + 1 - (a + d) / 2 = (c + (1 - a - d) / 2) + (1 / 2: ℂ) by ring,
      add_re, div_ofNat_re, one_re]
    linarith
  have hG2u := Gamma_ne_zero_of_re_pos hgap
  have hGuh := Gamma_ne_zero_of_re_pos huv
  have hdupY : Gamma ((a + d + 1) / 2) / Gamma (a + d) =
      (2: ℂ) ^ (1 - a - d) * (Real.sqrt Real.pi : ℂ) / Gamma ((a + d) / 2) := by
    have hY := Gamma_mul_Gamma_add_half ((a + d) / 2)
    rw [show (a + d) / 2 + 1 / 2 = (a + d + 1) / 2 by ring,
      show 2 * ((a + d) / 2) = a + d by ring, show 1 - (a + d) = 1 - a - d by ring] at hY
    apply (div_eq_div_iff hG2y hGy).mpr
    linear_combination hY
  have hdupU : Gamma (c + (1 - a - d) / 2) / Gamma (2 * c - d + 1 - a) =
      (2: ℂ) ^ (a + d - 2 * c) * (Real.sqrt Real.pi : ℂ) / Gamma (c + 1 - (a + d) / 2) := by
    have hU := Gamma_mul_Gamma_add_half (c + (1 - a - d) / 2)
    rw [show c + (1 - a - d) / 2 + 1 / 2 = c + 1 - (a + d) / 2 by ring,
      show 2 * (c + (1 - a - d) / 2) = 2 * c - d + 1 - a by ring,
      show 1 - (2 * c - d + 1 - a) = a + d - 2 * c by ring] at hU
    apply (div_eq_div_iff hG2u hGuh).mpr
    linear_combination hU
  have hPow : (2: ℂ) ^ (1 - a - d) * (2: ℂ) ^ (a + d - 2 * c) = (2: ℂ) ^ (1 - 2 * c) := by
    rw [← cpow_add _ _ (by norm_num : (2: ℂ)≠0)]
    congr 1
    ring
  have hπ : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi: ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  calc generalizedHypergeometric {a, 1 - a, c} {d, 2 * c - d + 1} 1 =
      Gamma (2 * c - d + 1) * Gamma d *
        (Gamma ((a + d + 1) / 2) / Gamma (a + d)) *
        (Gamma (c + (1 - a - d) / 2) / Gamma (2 * c - d + 1 - a)) /
        (Gamma ((d - a + 1) / 2) * Gamma (c + (a - d + 1) / 2)) := by rw [H]; field_simp
    _ = Gamma (2 * c - d + 1) * Gamma d *
        ((2: ℂ) ^ (1 - a - d) * (2: ℂ) ^ (a + d - 2 * c)) * (Real.sqrt Real.pi : ℂ) ^ 2 /
        (Gamma (c + (a - d + 1) / 2) * Gamma (c + 1 - (a + d) / 2)*
          Gamma ((a + d) / 2) * Gamma ((d - a + 1) / 2)) := by
      rw [hdupY, hdupU]
      ring
    _ = _ := by rw [hPow, hπ]; ring

/-- Whipple’s formula throughout the absolute convergence half - space. -/
lemma generalizedHypergeometric_eq_of_re_pos {a c d : ℂ} (hc : 0 < c.re)
    (hd : LowerParametersRegular {d, 2 * c - d + 1}) :
    generalizedHypergeometric {a, 1 - a, c} {d, 2 * c - d + 1} 1 =
      (Real.pi : ℂ) * Gamma d * Gamma (2 * c - d + 1) * (2: ℂ) ^ (1 - 2 * c) /
        (Gamma (c + (a - d + 1) / 2) * Gamma (c + 1 - (a + d) / 2)*
          Gamma ((a + d) / 2) * Gamma ((d - a + 1) / 2)) := by
  let L (z : ℂ) := generalizedHypergeometric {z, 1 - z, c} {d, 2 * c - d + 1} 1
  let R (z : ℂ) := (Real.pi : ℂ) * Gamma d * Gamma (2 * c - d + 1) * (2: ℂ) ^ (1 - 2 * c) /
        (Gamma (c + (z - d + 1) / 2) * Gamma (c + 1 - (z + d) / 2)*
          Gamma ((z + d) / 2) * Gamma ((d - z + 1) / 2))
  have hL : AnalyticOnNhd ℂ L univ := by
    intro z _
    let T (w : ℂ) : Fin 5 → ℂ := ![w, 1 - w, c, d, 2 * c - d + 1]
    have hT : AnalyticAt ℂ T z := by
      apply analyticAt_pi_iff.mpr
      intro i
      fin_cases i
      · exact analyticAt_id
      · exact analyticAt_const.sub analyticAt_id
      · exact analyticAt_const
      · exact analyticAt_const
      · exact analyticAt_const
    have hTr : T z ∈ UnitParameterSeries.convergenceRegion := by
      rw [UnitParameterSeries.convergenceRegion_def]
      dsimp [T]
      constructor
      · exact hd
      · norm_num [mul_re]
        linarith
    exact (UnitParameterSeries.analyticOnNhd_generalizedHypergeometric_one _ hTr).comp hT
  have hInv (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => (Gamma w)⁻¹) z :=
    differentiable_one_div_Gamma.analyticAt z
  have hR : AnalyticOnNhd ℂ R univ := by
    intro z _
    have h₁ := (hInv (c + (z - d + 1) / 2)).comp (x := z)
      (analyticAt_const.add
        (((analyticAt_id.sub analyticAt_const).add analyticAt_const).div_const (c := 2)))
    have h₂ := (hInv (c + 1 - (z + d) / 2)).comp (x := z)
      (analyticAt_const.sub ((analyticAt_id.add analyticAt_const).div_const (c := 2)))
    have h₃ := (hInv ((z + d) / 2)).comp (x := z)
      ((analyticAt_id.add analyticAt_const).div_const (c := 2))
    have h₄ := (hInv ((d - z + 1) / 2)).comp (x := z)
      (((analyticAt_const.sub analyticAt_id).add analyticAt_const).div_const (c := 2))
    simpa [R, div_eq_mul_inv, mul_inv_rev, Pi.mul_def, Pi.add_def, Pi.sub_def,
      Function.comp_def] using
      (analyticAt_const.mul (h₄.mul (h₃.mul (h₂.mul h₁))))
  let a₀ : ℂ := (((2 * c - d + 1).re - 1 : ℝ) : ℂ) +
    ((2 * |c.im| + 2 * |d.im| + 2 : ℝ) : ℂ) * I
  have hgap₀ : 0 < (2 * c - d + 1 - a₀).re := by
    dsimp [a₀]
    simp only [mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    linarith
  have hpar₀ : LowerParametersRegular
      {a₀ + c, (a₀ + d + 1) / 2, a₀ + d, (a₀ + d) / 2, (d - a₀ + 1) / 2, c + (a₀ - d + 1) / 2} := by
    intro u hu n hn
    have him := congrArg im hn
    simp only [neg_im, natCast_im, neg_zero] at him
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;>
      dsimp [a₀] at him <;>
      simp only [add_im, sub_im, div_ofNat_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_one, mul_zero, zero_add, one_im] at him <;>
      nlinarith [le_abs_self c.im, neg_le_abs c.im, le_abs_self d.im, neg_le_abs d.im]
  have hEq : L =ᶠ[𝓝 a₀] R := by
    have hreg (f : ℂ → ℂ) (hf : Continuous f) (h : ∀ n : ℕ, f a₀ ≠ -(n: ℂ)) :
        ∀ᶠ z in 𝓝 a₀, ∀ n : ℕ, f z ≠ -(n: ℂ) :=
      hf.continuousAt.eventually (isOpen_not_neg_nat.mem_nhds h)
    have h₁ := hreg (fun z => z + c) (by fun_prop) (hpar₀ _ (by simp))
    have h₂ := hreg (fun z => (z + d + 1) / 2) (by fun_prop) (hpar₀ _ (by simp))
    have h₃ := hreg (fun z => z + d) (by fun_prop) (hpar₀ _ (by simp))
    have h₄ := hreg (fun z => (z + d) / 2) (by fun_prop) (hpar₀ _ (by simp))
    have h₅ := hreg (fun z => (d - z + 1) / 2) (by fun_prop) (hpar₀ _ (by simp))
    have h₆ := hreg (fun z => c + (z - d + 1) / 2) (by fun_prop) (hpar₀ _ (by simp))
    have hg : ∀ᶠ z in 𝓝 a₀, 0 < (2 * c - d + 1 - z).re :=
      (by fun_prop : Continuous (fun z : ℂ => (2 * c - d + 1 - z).re)).continuousAt.eventually
        (Ioi_mem_nhds hgap₀)
    filter_upwards [h₁, h₂, h₃, h₄, h₅, h₆, hg] with z hz₁ hz₂ hz₃ hz₄ hz₅ hz₆ hzg
    exact generalizedHypergeometric_eq_of_regular_parameters hc hd hzg (by
      intro u hu n
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hu
      rcases hu with rfl|rfl|rfl|rfl|rfl|rfl
      · exact hz₁ n
      · exact hz₂ n
      · exact hz₃ n
      · exact hz₄ n
      · exact hz₅ n
      · exact hz₆ n)
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR isPreconnected_univ (mem_univ a₀)
    hEq (mem_univ a)

/-- Whipple’s formula for every terminating complementary upper parameter. -/
lemma generalizedHypergeometric_eq_of_terminates {a c d : ℂ} {N : ℕ}
    (hN : -(N: ℂ) ∈ ({a, 1 - a}:Multiset ℂ))
    (hd : LowerParametersRegular {d, 2 * c - d + 1}) :
    generalizedHypergeometric {a, 1 - a, c} {d, 2 * c - d + 1} 1 =
      (Real.pi : ℂ) * Gamma d * Gamma (2 * c - d + 1) * (2: ℂ) ^ (1 - 2 * c) /
        (Gamma (c + (a - d + 1) / 2) * Gamma (c + 1 - (a + d) / 2)*
          Gamma ((a + d) / 2) * Gamma ((d - a + 1) / 2)) := by
  have hd₀ : ∀ n : ℕ, d ≠ -(n: ℂ) := hd _ (by simp)
  let U : Set ℂ := {z | ∀ n : ℕ, 2 * z - d + 1 ≠ -(n: ℂ)}
  have hUeq : U = (range (fun n : ℕ => (-(n: ℂ) + d - 1) / 2))ᶜ := by
    ext z
    constructor
    · intro hz hzbad
      rcases hzbad with ⟨n, hn⟩
      apply hz n
      linear_combination -2 * hn
    · intro hz n hn
      apply hz
      exact ⟨n, by linear_combination -hn / 2⟩
  have hUc : IsPreconnected U := by
    rw [hUeq]
    exact (Set.Countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) (countable_range _)).isConnected.isPreconnected
  have hlow {z : ℂ} (hz : z ∈ U) : LowerParametersRegular {d, 2 * z - d + 1} := by
    intro u hu n
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hu
    rcases hu with rfl|rfl
    · exact hd₀ n
    · exact hz n
  have hNt (z : ℂ) : -(N: ℂ) ∈ ({a, 1 - a, z}:Multiset ℂ) := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hN ⊢
    exact hN.elim Or.inl (fun h => Or.inr (Or.inl h))
  let L (z : ℂ) := generalizedHypergeometricTruncated N {a, 1 - a, z} {d, 2 * z - d + 1} 1
  let R (z : ℂ) := (Real.pi : ℂ) * Gamma d * Gamma (2 * z - d + 1) * (2: ℂ) ^ (1 - 2 * z) /
        (Gamma (z + (a - d + 1) / 2) * Gamma (z + 1 - (a + d) / 2)*
          Gamma ((a + d) / 2) * Gamma ((d - a + 1) / 2))
  have hL : AnalyticOnNhd ℂ L U := by
    intro z hz
    let T (w : ℂ) : Fin 5 → ℂ := ![a, 1 - a, w, d, 2 * w - d + 1]
    have hT : AnalyticAt ℂ T z := by
      apply analyticAt_pi_iff.mpr
      intro i
      fin_cases i
      · exact analyticAt_const
      · exact analyticAt_const
      · exact analyticAt_id
      · exact analyticAt_const
      · exact ((analyticAt_const.mul analyticAt_id).sub analyticAt_const).add analyticAt_const
    have hpar : LowerParametersRegular {(T z) 3, (T z) 4} := by
      dsimp [T]
      exact hlow hz
    have hn (n : ℕ) := (UnitParameterSeries.analyticAt_coefficient hpar n).comp hT
    simpa [L, generalizedHypergeometricTruncated, UnitParameterSeries.coefficient_def,
      T, Function.comp_def, Finset.sum_apply] using
      (Finset.analyticAt_fun_sum (range (N + 1)) (fun n _ => hn n))
  have hInv (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => (Gamma w)⁻¹) z :=
    differentiable_one_div_Gamma.analyticAt z
  have hR : AnalyticOnNhd ℂ R U := by
    intro z hz
    have hΓall : AnalyticOnNhd ℂ Gamma {w : ℂ | ∀ n : ℕ, w ≠ -(n: ℂ)} := by
      apply DifferentiableOn.analyticOnNhd _ isOpen_not_neg_nat
      intro w hw
      exact (differentiableAt_Gamma w hw).differentiableWithinAt
    have hΓ := hΓall (2 * z - d + 1) hz
    have h₀ := hΓ.comp (x := z)
      (((analyticAt_const.mul analyticAt_id).sub analyticAt_const).add analyticAt_const)
    have hP : AnalyticAt ℂ (fun w : ℂ => (2: ℂ) ^ (1 - 2 * w)) z :=
      (((differentiable_const (1: ℂ)).sub
        ((differentiable_const (2: ℂ)).mul differentiable_id)).const_cpow
        (Or.inl (by norm_num : (2: ℂ)≠0))).analyticAt z
    have h₁ := (hInv (z + (a - d + 1) / 2)).comp (x := z) (analyticAt_id.add analyticAt_const)
    have h₂ := (hInv (z + 1 - (a + d) / 2)).comp (x := z)
      ((analyticAt_id.add analyticAt_const).sub analyticAt_const)
    simpa [R, div_eq_mul_inv, mul_inv_rev, Pi.mul_def, Pi.add_def, Pi.sub_def,
      Function.comp_def] using
      (((analyticAt_const.mul h₀).mul hP).mul
        (analyticAt_const.mul (analyticAt_const.mul (h₂.mul h₁))))
  let c₀ : ℂ := ((|d.re| + 2 : ℝ): ℂ) + ((d.im / 2: ℝ): ℂ) * I
  have hc₀ : 0 < c₀.re := by
    dsimp [c₀]
    simp only [mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
    positivity
  have he₀ : 0 < (2 * c₀ - d + 1).re := by
    dsimp [c₀]
    norm_num [mul_re]
    nlinarith [le_abs_self d.re, abs_nonneg d.re]
  have hc₀U : c₀ ∈ U := not_neg_nat_of_re_pos he₀
  have hEq : L =ᶠ[𝓝 c₀] R := by
    have hp : ∀ᶠ z : ℂ in 𝓝 c₀, 0 < z.re :=
      continuous_re.continuousAt.eventually (Ioi_mem_nhds hc₀)
    have he : ∀ᶠ z : ℂ in 𝓝 c₀, 0 < (2 * z - d + 1).re :=
      (by fun_prop : Continuous (fun z : ℂ => (2 * z - d + 1).re)).continuousAt.eventually
        (Ioi_mem_nhds he₀)
    filter_upwards [hp, he] with z hz hze
    have hdz : LowerParametersRegular {d, 2 * z - d + 1} :=
      hlow (not_neg_nat_of_re_pos hze)
    have H := generalizedHypergeometric_eq_of_re_pos (a := a) hz hdz
    rw [generalizedHypergeometric_eq_finite hdz (hNt z) 1] at H
    exact H
  have hcU : c ∈ U := hd _ (by simp)
  have H := hL.eqOn_of_preconnected_of_eventuallyEq hR hUc hc₀U hEq hcU
  rw [generalizedHypergeometric_eq_finite hd (hNt c) 1]
  exact H

/-- Whipple’s formula in its convergence half - space and at every integer upper parameter. -/
lemma generalizedHypergeometric_eq {a c d : ℂ} (hd : LowerParametersRegular {d, 2 * c - d + 1})
    (h : 0 < c.re ∨ ∃ n : ℤ, a = n) :
    generalizedHypergeometric {a, 1 - a, c} {d, 2 * c - d + 1} 1 =
      (Real.pi : ℂ) * Gamma d * Gamma (2 * c - d + 1) * (2: ℂ) ^ (1 - 2 * c) /
        (Gamma (c + (a - d + 1) / 2) * Gamma (c + 1 - (a + d) / 2)*
          Gamma ((a + d) / 2) * Gamma ((d - a + 1) / 2)) := by
  rcases h with hc|⟨n, rfl⟩
  · exact generalizedHypergeometric_eq_of_re_pos hc hd
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, -(N: ℂ) ∈ ({(n: ℂ), 1 - (n: ℂ)}:Multiset ℂ) := by
      cases n with
      | ofNat k =>
        cases k with
        | zero => exact ⟨0, by simp⟩
        | succ k =>
          refine ⟨k, ?_⟩
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
          right
          rw [show ((Int.ofNat (k + 1): ℤ): ℂ) = ((k + 1: ℕ): ℂ) from rfl]
          push_cast
          ring
      | negSucc k =>
        refine ⟨k + 1, ?_⟩
        simp
    exact generalizedHypergeometric_eq_of_terminates hN hd

end DLMF.Hypergeometric.WhippleSummation
