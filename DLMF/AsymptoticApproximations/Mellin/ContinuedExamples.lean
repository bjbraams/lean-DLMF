/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Mellin.ContinuationResidues
public import DLMF.AsymptoticApproximations.Mellin.SmallParameter
public import DLMF.AsymptoticApproximations.Mellin.BesselExample
public import DLMFMathlib.Analysis.Asymptotics.ElementaryPowerSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Continued Mellin transforms of elementary kernels

The exponential continues to the Gamma function and the reciprocal-linear kernel to
`π/sin(πz)`. Their finite-subtraction principal parts determine the residues with the
signs in DLMF 2.5.25 and 2.5.27.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- The negative exponential is locally integrable on the positive real axis. -/
private theorem locallyIntegrableOn_exp_neg :
    LocallyIntegrableOn (fun t : ℝ => exp (-(t : ℂ))) (Ioi 0) :=
  (by fun_prop : ContinuousOn (fun t : ℝ => exp (-(t : ℂ))) (Ioi 0)).locallyIntegrableOn
    measurableSet_Ioi

/-- The negative exponential decays faster than every real power at positive infinity. -/
private theorem exp_neg_isBigO_rpow (b : ℝ) :
    (fun t : ℝ => exp (-(t : ℂ))) =O[atTop] fun t => t ^ (-b) := by
  rw [← isBigO_norm_left]
  simpa only [norm_exp, neg_re, ofReal_re, neg_one_mul] using
    (isLittleO_exp_neg_mul_rpow_atTop one_pos (-b)).isBigO

/-- The real parts of the natural complex exponents strictly increase. -/
private theorem strictMono_natCast_re : StrictMono fun k : ℕ => ((k : ℂ)).re := by
  intro i j hij
  simp only [natCast_re]
  exact_mod_cast hij

/-- The finite continuation of the negative exponential agrees with Gamma away from its
first `N` poles on `-N < Re z`. -/
theorem mellinContinuationAtZero_exp_neg {N : ℕ} {z : ℂ} (hz : -(N : ℝ) < z.re)
    (hne : ∀ k ∈ range N, z + (k : ℂ) ≠ 0) :
    mellinContinuationAtZero (fun t : ℝ => exp (-(t : ℂ)))
      (fun k => (-1 : ℂ) ^ k / (k.factorial : ℂ)) (fun k => k) N z = Gamma z := by
  let B : ℝ := max z.re 1 + 1
  have hBz : z.re < B := by dsimp [B]; linarith [le_max_left z.re 1]
  have hB1 : (1 : ℝ) < B := by dsimp [B]; linarith [le_max_right z.re 1]
  have hf := Asymptotics.hasAsymptoticExpansion_exp_neg_ofReal
  obtain ⟨G, hGm, hG⟩ := exists_meromorphic_mellinContinuationAtZero
    locallyIntegrableOn_exp_neg strictMono_natCast_re tendsto_natCast_atTop_atTop hf
    (exp_neg_isBigO_rpow B)
  have he : G =ᶠ[𝓝 (1 : ℂ)] Gamma := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num :
      (0 : ℝ) < (1 : ℂ).re),
      (isOpen_lt continuous_re continuous_const).mem_nhds hB1] with w hw0 hwB
    rw [hG 0 w (by simpa using hw0) hwB,
      mellinContinuationAtZero_eq_mellin locallyIntegrableOn_exp_neg strictMono_natCast_re hf
        (exp_neg_isBigO_rpow B) 0 (by simpa using hw0) hwB]
    simpa only [← ofReal_neg, ← ofReal_exp] using mellin_exp_neg hw0
  have hGamma (k : ℕ) : z ≠ -(k : ℂ) := by
    intro heq
    have hk : k < N := by
      have hr := congrArg Complex.re heq
      simp only [neg_re, natCast_re] at hr
      exact_mod_cast (show (k : ℝ) < N by linarith)
    exact hne k (mem_range.mpr hk) (by rw [heq]; ring)
  have hd := differentiableAt_mellinContinuationAtZero locallyIntegrableOn_exp_neg hf
    (exp_neg_isBigO_rpow B) N (by simpa using hz) hBz hne
  have hGc : ContinuousAt G z := hd.continuousAt.congr (by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz,
      (isOpen_lt continuous_re continuous_const).mem_nhds hBz] with w hw hwB
    exact (hG N w (by simpa using hw) hwB).symm)
  have heq := hGm.eq_of_isConnected_of_eventuallyEq
    (fun w _ => Meromorphic.Gamma w)
    ⟨⟨1, hB1⟩, (convex_halfSpace_re_lt B).isPreconnected⟩ hB1 he hBz hGc
    (continuousAt_Gamma z hGamma)
  rw [hG N z (by simpa using hz) hBz] at heq
  exact heq

/-- The residue of the exponential's finite continuation at `-k` is `(-1)^k/k!`. -/
theorem residue_mellinContinuationAtZero_exp_neg (N k : ℕ) (hk : k < N) :
    TauCeti.Contour.residue
      (mellinContinuationAtZero (fun t : ℝ => exp (-(t : ℂ)))
        (fun k => (-1 : ℂ) ^ k / (k.factorial : ℂ)) (fun k => k) N) (-(k : ℂ)) =
          (-1 : ℂ) ^ k / (k.factorial : ℂ) := by
  exact residue_mellinContinuationAtZero locallyIntegrableOn_exp_neg strictMono_natCast_re
    Asymptotics.hasAsymptoticExpansion_exp_neg_ofReal (exp_neg_isBigO_rpow 1) N k hk
      (by simp only [natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) k])

/-- The reciprocal-linear kernel is locally integrable on the positive real axis. -/
private theorem locallyIntegrableOn_inv_one_add :
    LocallyIntegrableOn (fun t : ℝ => (1 + (t : ℂ))⁻¹) (Ioi 0) := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  intro t ht
  exact ((continuousAt_const.add continuous_ofReal.continuousAt).inv₀
    (ne_zero_of_re_pos (by simp; linarith [show 0 < t from ht]))).continuousWithinAt

/-- The reciprocal-linear kernel is bounded at the positive side of zero. -/
private theorem inv_one_add_isBigO_atZero :
    (fun t : ℝ => (1 + (t : ℂ))⁻¹) =O[𝓝[>] 0] fun t => t ^ (0 : ℝ) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [norm_inv, ← ofReal_one, ← ofReal_add, norm_real,
    Real.norm_of_nonneg (by linarith [show 0 < t from ht] : 0 ≤ 1 + t)]
  simp only [Real.rpow_zero, norm_one, one_mul]
  exact inv_le_one_of_one_le₀ (by linarith [show 0 < t from ht])

/-- The positive integer exponents have strictly increasing real parts. -/
private theorem strictMono_natCast_add_one_re :
    StrictMono fun k : ℕ => ((k : ℂ) + 1).re := by
  simpa only [add_re, natCast_re, one_re] using strictMono_natCast_re.add_const 1

/-- The Mellin transform of `1/(1+t)` on its initial strip. -/
theorem mellin_inv_one_add {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    mellin (fun t : ℝ => (1 + (t : ℂ))⁻¹) z = (Real.pi : ℂ) / sin (Real.pi * z) := by
  have h := mellin_inv_one_add_one_sub (z := 1 - z)
    (by simp; linarith) (by simp; linarith)
  simpa only [sub_sub_cancel, ofReal_add, ofReal_one, mul_sub, mul_one, sin_pi_sub] using h

/-- The finite infinity-endpoint continuation of `1/(1+t)` agrees with `π/sin(πz)` on
`0 < Re z < N+1`, away from its displayed poles. -/
theorem mellinContinuationAtTop_inv_one_add {N : ℕ} {z : ℂ} (hz0 : 0 < z.re)
    (hzN : z.re < N + 1) (hne : ∀ k ∈ range N, z - ((k : ℂ) + 1) ≠ 0) :
    mellinContinuationAtTop (fun t : ℝ => (1 + (t : ℂ))⁻¹)
      (fun k => (-1 : ℂ) ^ k) (fun k => (k : ℂ) + 1) N z =
        (Real.pi : ℂ) / sin (Real.pi * z) := by
  have hf := Asymptotics.hasAsymptoticExpansion_inv_one_add_atTop
  obtain ⟨G, hGm, hG⟩ := exists_meromorphic_mellinContinuationAtTop
    locallyIntegrableOn_inv_one_add strictMono_natCast_add_one_re
    (by simpa only [add_re, natCast_re, one_re] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)))
    hf inv_one_add_isBigO_atZero
  simp only [neg_zero] at hGm hG
  have hgm : MeromorphicOn (fun w : ℂ => (Real.pi : ℂ) / sin (Real.pi * w))
      {w | (0 : ℝ) < w.re} := fun w _ => analyticAt_const.meromorphicAt.div
        ((Complex.analyticAt_sin.comp (analyticAt_const.mul analyticAt_id)).meromorphicAt)
  have he : G =ᶠ[𝓝 (1 / 2 : ℂ)] (fun w => (Real.pi : ℂ) / sin (Real.pi * w)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re),
      (isOpen_lt continuous_re continuous_const).mem_nhds
        (by norm_num : (1 / 2 : ℂ).re < (1 : ℝ))] with w hw0 hw1
    rw [hG 0 w (by simpa using hw0) (by simpa using hw1),
      mellinContinuationAtTop_eq_mellin locallyIntegrableOn_inv_one_add
        strictMono_natCast_add_one_re hf inv_one_add_isBigO_atZero 0
          (by simpa using hw0) (by simpa using hw1), mellin_inv_one_add hw0 hw1]
  have hsin : sin (Real.pi * z) ≠ 0 := by
    intro hs
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hzk : z = (k : ℂ) := by apply mul_left_cancel₀ hπ; rw [hk]; ring
    have hk0 : 0 < k := by rw [hzk] at hz0; exact_mod_cast hz0
    have hkN : k ≤ N := by rw [hzk] at hzN; norm_cast at hzN; omega
    let j := k.toNat - 1
    have hj : j < N := by omega
    have heq : (j : ℂ) + 1 = (k : ℂ) := by
      have hn : j + 1 = k.toNat := by omega
      exact_mod_cast (show (j : ℤ) + 1 = k by omega)
    exact hne j (mem_range.mpr hj) (by rw [hzk, heq, sub_self])
  have hd := differentiableAt_mellinContinuationAtTop locallyIntegrableOn_inv_one_add hf
    inv_one_add_isBigO_atZero N (by simpa using hz0) (by simpa using hzN) hne
  have hGc : ContinuousAt G z := hd.continuousAt.congr (by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz0,
      (isOpen_lt continuous_re continuous_const).mem_nhds hzN] with w hw0 hwN
    exact (hG N w (by simpa using hw0) (by simpa using hwN)).symm)
  have heq := hGm.eq_of_isConnected_of_eventuallyEq hgm
    ⟨⟨1, by norm_num⟩, (convex_halfSpace_re_gt 0).isPreconnected⟩
    (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re) he hz0 hGc
    ((continuousAt_const.div (Complex.continuous_sin.continuousAt.comp
      (continuousAt_const.mul continuousAt_id)) hsin))
  rw [hG N z (by simpa using hz0) (by simpa using hzN)] at heq
  exact heq

/-- The residue at the positive integer `k+1` is `-(-1)^k = (-1)^(k+1)`. -/
theorem residue_mellinContinuationAtTop_inv_one_add (N k : ℕ) (hk : k < N) :
    TauCeti.Contour.residue
      (mellinContinuationAtTop (fun t : ℝ => (1 + (t : ℂ))⁻¹)
        (fun k => (-1 : ℂ) ^ k) (fun k => (k : ℂ) + 1) N) ((k : ℂ) + 1) =
          (-1 : ℂ) ^ (k + 1) := by
  rw [residue_mellinContinuationAtTop locallyIntegrableOn_inv_one_add
    strictMono_natCast_add_one_re Asymptotics.hasAsymptoticExpansion_inv_one_add_atTop
    inv_one_add_isBigO_atZero N k hk (by simp; positivity)]
  simp [pow_succ]

end DLMF.AsymptoticApproximations
