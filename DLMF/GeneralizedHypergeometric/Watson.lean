/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.GeneralizedHypergeometric.Basic
import DLMF.GeneralizedHypergeometric.Whipple
import DLMF.GeneralizedHypergeometric.Thomae
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic
/-!
# Watson summation at unit argument

Watson’s formula, DLMF 16.4.6, follows from the Thomae transformation and Whipple’s sum.
Fixing the positive parameter excess while varying the remaining parameter continues the
identity on a plane minus two discrete lattices. The resulting formula holds on the full
absolute convergence half-space, including exceptional upper parameters and zeros of
reciprocal Gamma factors.

* `WatsonSummation.generalizedHypergeometric_eq`: Watson’s complete unit-argument sum.

The proof reuses the native Thomae and Whipple transformations and Mathlib’s Gamma duplication
formula and countable-complement path-connectedness theorem.
-/
public noncomputable section
open Complex Filter Set Finset
open scoped Topology
namespace DLMF.Hypergeometric.WatsonSummation

 /-- Watson’s formula when the third upper parameter has positive real part. -/
lemma generalizedHypergeometric_eq_of_re_pos {a b c : ℂ} (hc : 0 < c.re)
    (hd : LowerParametersRegular {(a + b + 1) / 2, 2 * c})
    (hs : 0 < (c + (1 - a - b) / 2).re) :
    generalizedHypergeometric {a, b, c} {(a + b + 1) / 2, 2 * c} 1 =
      Gamma (1 / 2) * Gamma (c + 1 / 2) * Gamma ((a + b + 1) / 2) * Gamma (c + (1 - a - b) / 2) /
        (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2) * Gamma (c + (1 - a) / 2) *
          Gamma (c + (1 - b) / 2)) := by
  have hcs : 0 < (2 * c + (1 - a - b) / 2).re := by
    rw [show 2 * c + (1 - a - b) / 2 = c + (c + (1 - a - b) / 2) by ring, add_re]
    linarith
  have hlow : LowerParametersRegular {(a + b + 1) / 2, 2 * c, (a + b + 1) / 2 + 2 * c - a - b} := by
    intro u hu n
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hu
    rcases hu with rfl|rfl|rfl
    · exact hd _ (by simp) n
    · exact hd _ (by simp) n
    · apply not_neg_nat_of_re_pos (k := n)
      convert hcs using 1
      congr 1
      ring
  have H := ThomaeTransformation.generalizedHypergeometric_eq (a := c) (b := a) (c := b)
    hlow (by convert hs using 1;congr 1;ring)
    (by simpa only [show 2 * c - c = c by ring] using hc)
  rw [show (a + b + 1) / 2 + 2 * c - c - a - b = c + (1 - a - b) / 2 by ring,
    show (a + b + 1) / 2 + 2 * c - a - b = 2 * c + (1 - a - b) / 2 by ring,
    show 2 * c - c = c by ring] at H
  have hW := WhippleSummation.generalizedHypergeometric_eq_of_re_pos
    (a := (a + b + 1) / 2 - a) (c := c) (d := (a + b + 1) / 2) hc (by
      intro u hu n
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hu
      rcases hu with rfl|rfl
      · exact hd _ (by simp) n
      · apply not_neg_nat_of_re_pos (k := n)
        convert hcs using 1
        congr 1
        ring)
  rw [show 1 - ((a + b + 1) / 2 - a) = (a + b + 1) / 2 - b by ring,
    show 2 * c - (a + b + 1) / 2 + 1 = 2 * c + (1 - a - b) / 2 by ring,
    show c + ((a + b + 1) / 2 - a - (a + b + 1) / 2 + 1) / 2 = c + (1 - a) / 2 by ring,
    show c + 1 - (((a + b + 1) / 2 - a) + (a + b + 1) / 2) / 2 = c + (1 - b) / 2 by ring,
    show (((a + b + 1) / 2 - a) + (a + b + 1) / 2) / 2 = (b + 1) / 2 by ring,
    show ((a + b + 1) / 2 - ((a + b + 1) / 2 - a) + 1) / 2 = (a + 1) / 2 by ring] at hW
  have hperm : ({c, (a + b + 1) / 2 - a, (a + b + 1) / 2 - b}:Multiset ℂ)=
      {(a + b + 1) / 2 - a, (a + b + 1) / 2 - b, c} := by
    simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero]
    rw [Multiset.cons_swap c ((a + b + 1) / 2 - a), Multiset.cons_swap c ((a + b + 1) / 2 - b)]
  rw [hperm, hW] at H
  have hperm₀ : ({c, a, b}:Multiset ℂ)={a, b, c} := by
    simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero]
    rw [Multiset.cons_swap c a, Multiset.cons_swap c b]
  rw [hperm₀] at H
  have hGc := Gamma_ne_zero_of_re_pos hc
  have hGcs := Gamma_ne_zero_of_re_pos hcs
  have hdup := Gamma_mul_Gamma_add_half c
  have hπ : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi: ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hπn : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hG : Gamma (2 * c) * (2: ℂ) ^ (1 - 2 * c) / Gamma c =
      Gamma (c + 1 / 2) / (Real.sqrt Real.pi : ℂ) := by
    apply (div_eq_div_iff hGc hπn).mpr
    linear_combination - hdup
  calc
    generalizedHypergeometric {a, b, c} {(a + b + 1) / 2, 2 * c} 1 =
      (Real.pi : ℂ) * Gamma ((a + b + 1) / 2) * Gamma (c + (1 - a - b) / 2) *
        (Gamma (2 * c) * (2: ℂ) ^ (1 - 2 * c) / Gamma c) /
        (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2) * Gamma (c + (1 - a) / 2) *
          Gamma (c + (1 - b) / 2)) := by
      rw [H]
      generalize Gamma (2 * c + (1 - a - b) / 2) = Y at hGcs ⊢
      field_simp
    _ = ((Real.pi : ℂ) / (Real.sqrt Real.pi : ℂ)) * Gamma (c + 1 / 2) *
        Gamma ((a + b + 1) / 2) * Gamma (c + (1 - a - b) / 2) /
        (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2) * Gamma (c + (1 - a) / 2) *
          Gamma (c + (1 - b) / 2)) := by
      rw [hG]
      ring
    _ = _ := by
      have hr : (Real.pi : ℂ) / (Real.sqrt Real.pi : ℂ) = (Real.sqrt Real.pi : ℂ) :=
        (div_eq_iff hπn).mpr (by linear_combination - hπ)
      have hh : Gamma (1 / 2) = (Real.sqrt Real.pi : ℂ) := by
        rw [show (1 / 2: ℂ) = ((1 / 2: ℝ): ℂ) by norm_num, Gamma_ofReal, Real.Gamma_one_half_eq]
      rw [hr, hh]

 /-- Watson’s formula throughout its absolute convergence half-space. -/
lemma generalizedHypergeometric_eq {a b c : ℂ}
    (hd : LowerParametersRegular {(a + b + 1) / 2, 2 * c})
    (hs₀ : -1 < (2 * c - a - b).re) :
    generalizedHypergeometric {a, b, c} {(a + b + 1) / 2, 2 * c} 1 =
      Gamma (1 / 2) * Gamma (c + 1 / 2) * Gamma ((a + b + 1) / 2) * Gamma (c + (1 - a - b) / 2) /
        (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2) * Gamma (c + (1 - a) / 2) *
          Gamma (c + (1 - b) / 2)) := by
  let s := c + (1 - a - b) / 2
  let x := 1 - s
  let A (z : ℂ) := 2 * z + 1 - b - 2 * s
  have hs : 0 < s.re := by
    dsimp [s]
    norm_num [mul_re] at hs₀
    simp only [sub_re, div_ofNat_re, one_re]
    linarith
  let U : Set ℂ := {z | (∀ n : ℕ, z + x ≠ -(n: ℂ)) ∧ (∀ n : ℕ, 2 * z ≠ -(n: ℂ))}
  have hUeq : U = (range (fun n : ℕ => -(n: ℂ) - x) ∪ range (fun n : ℕ => -(n: ℂ) / 2))ᶜ := by
    ext z
    constructor
    · rintro ⟨h₁, h₂⟩ (⟨n, hn⟩|⟨n, hn⟩)
      · apply h₁ n
        linear_combination - hn
      · apply h₂ n
        linear_combination - 2 * hn
    · intro hz
      constructor
      · intro n hn
        apply hz
        exact Or.inl ⟨n, by linear_combination - hn⟩
      · intro n hn
        apply hz
        exact Or.inr ⟨n, by linear_combination - hn / 2⟩
  have hUc : IsPreconnected U := by
    rw [hUeq]
    exact (Set.Countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex];norm_num)
      ((countable_range _).union (countable_range _))).isConnected.isPreconnected
  let L (z : ℂ) := generalizedHypergeometric {A z, b, z} {z + x, 2 * z} 1
  let R (z : ℂ) := Gamma (1 / 2) * Gamma (z + 1 / 2) * Gamma (z + x) * Gamma s /
    (Gamma ((A z + 1) / 2) * Gamma ((b + 1) / 2) * Gamma (z + (1 - A z) / 2) *
      Gamma (z + (1 - b) / 2))
  have hlow {z : ℂ} (hz : z ∈ U) : LowerParametersRegular {z + x, 2 * z} := by
    intro u hu n
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hu
    rcases hu with rfl|rfl
    · exact hz.1 n
    · exact hz.2 n
  have hL : AnalyticOnNhd ℂ L U := by
    intro z hz
    let T (w : ℂ) : Fin 5 → ℂ := ![A w, b, w, w + x, 2 * w]
    have hT : AnalyticAt ℂ T z := by
      apply analyticAt_pi_iff.mpr
      intro i
      fin_cases i
      · exact (((analyticAt_const.mul analyticAt_id).add analyticAt_const).sub
          analyticAt_const).sub analyticAt_const
      · exact analyticAt_const
      · exact analyticAt_id
      · exact analyticAt_id.add analyticAt_const
      · exact analyticAt_const.mul analyticAt_id
    have hTr : T z ∈ UnitParameterSeries.convergenceRegion := by
      rw [UnitParameterSeries.convergenceRegion_def]
      have he : (T z) 3 + (T z) 4 - (T z) 0 - (T z) 1 - (T z) 2 = s := by
        dsimp [T, A, x]
        ring
      constructor
      · dsimp [T]
        exact hlow hz
      · rw [he]
        exact hs
    exact (UnitParameterSeries.analyticOnNhd_generalizedHypergeometric_one _ hTr).comp hT
  have hΓ : AnalyticOnNhd ℂ Gamma {w : ℂ | ∀ n : ℕ, w ≠ -(n: ℂ)} := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_not_neg_nat
    intro w hw
    exact (differentiableAt_Gamma w hw).differentiableWithinAt
  have hInv (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => (Gamma w)⁻¹) z :=
    differentiable_one_div_Gamma.analyticAt z
  have hR : AnalyticOnNhd ℂ R U := by
    intro z hz
    have hzh : ∀ n : ℕ, z + 1 / 2 ≠ -(n: ℂ) := by
      intro n hn
      apply hz.2 (2 * n + 1)
      push_cast
      linear_combination 2 * hn
    have h₁ := (hΓ _ hzh).comp (x := z) (analyticAt_id.add analyticAt_const)
    have h₂ := (hΓ _ hz.1).comp (x := z) (analyticAt_id.add analyticAt_const)
    have h₃ := (hInv ((A z + 1) / 2)).comp (x := z)
      ((((((analyticAt_const.mul analyticAt_id).add analyticAt_const).sub
        analyticAt_const).sub analyticAt_const).add analyticAt_const).div_const (c := 2))
    have h₄ := (hInv (z + (1 - A z) / 2)).comp (x := z)
      (analyticAt_id.add ((analyticAt_const.sub
        ((((analyticAt_const.mul analyticAt_id).add analyticAt_const).sub
          analyticAt_const).sub analyticAt_const)).div_const (c := 2)))
    have h₅ := (hInv (z + (1 - b) / 2)).comp (x := z) (analyticAt_id.add analyticAt_const)
    simpa [R, A, div_eq_mul_inv, mul_inv_rev, Pi.mul_def, Pi.add_def, Pi.sub_def,
      Function.comp_def] using
      ((((analyticAt_const.mul h₁).mul h₂).mul analyticAt_const).mul
        (h₅.mul (h₄.mul (analyticAt_const.mul h₃))))
  let z₀ : ℂ := ((|x.re| + 2 : ℝ): ℂ)
  have hz₀ : 0 < z₀.re := by
    dsimp [z₀]
    positivity
  have hzx : 0 < (z₀ + x).re := by
    dsimp [z₀]
    nlinarith [neg_le_abs x.re, abs_nonneg x.re]
  have hz₀U : z₀ ∈ U := ⟨not_neg_nat_of_re_pos hzx,
    not_neg_nat_of_re_pos (by rw [show 2 * z₀ = z₀ + z₀ by ring, add_re];linarith)⟩
  have hEq : L =ᶠ[𝓝 z₀] R := by
    have hpos : ∀ᶠ z : ℂ in 𝓝 z₀, 0 < z.re :=
      continuous_re.continuousAt.eventually (Ioi_mem_nhds hz₀)
    have hreg : ∀ᶠ z : ℂ in 𝓝 z₀, 0 < (z + x).re :=
      (by fun_prop : Continuous (fun z : ℂ => (z + x).re)).continuousAt.eventually
        (Ioi_mem_nhds hzx)
    filter_upwards [hpos, hreg] with z hz hzx
    have hAz : (A z + b + 1) / 2 = z + x := by dsimp [A, x];ring
    have hsz : z + (1 - A z - b) / 2 = s := by dsimp [A];ring
    have hdz : LowerParametersRegular {(A z + b + 1) / 2, 2 * z} := by
      rw [hAz]
      exact hlow ⟨not_neg_nat_of_re_pos hzx,
        not_neg_nat_of_re_pos (by rw [show 2 * z = z + z by ring, add_re];linarith)⟩
    have H := generalizedHypergeometric_eq_of_re_pos hz hdz (by rwa [hsz])
    rw [hAz, hsz] at H
    exact H
  have hAc : A c = a := by dsimp [A, s];ring
  have hcx : c + x = (a + b + 1) / 2 := by dsimp [x, s];ring
  have hcU : c ∈ U := by
    constructor
    · rw [hcx]
      exact hd _ (by simp)
    · exact hd _ (by simp)
  have H := hL.eqOn_of_preconnected_of_eventuallyEq hR hUc hz₀U hEq hcU
  dsimp only [L, R] at H
  rw [hAc, hcx] at H
  exact H

end DLMF.Hypergeometric.WatsonSummation
