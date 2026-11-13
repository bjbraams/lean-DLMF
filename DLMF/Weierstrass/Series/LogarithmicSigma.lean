/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic.Functions
import DLMF.Weierstrass.Basic.LatticesAndSigma
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# A logarithmic expansion of the Weierstrass sigma function

Inside the disk bounded by the nearest nonzero lattice point, the regularized logarithms of
the sigma product converge absolutely. Expanding each factor and pairing opposite lattice
points expresses sigma as `z` times the exponential of a series of even lattice sums.
-/

public section

set_option maxHeartbeats 0

open Complex PeriodPair Filter
open scoped Topology

namespace DLMF.Weierstrass

/-- Sigma is `z` times the exponential of its regularized logarithmic lattice series. -/
lemma weierstrassSigma_eq_exp_sum (L : PeriodPair) {z : ℂ}
    (hz : ∀ w ∈ L.lattice, w ≠ 0 → ‖z‖ < ‖w‖) :
    ∃ S : ℂ, HasSum (fun n : ℕ => L.G (2 * (n + 2)) * z ^ (2 * (n + 2)) /
        (2 * (n + 2))) S ∧ weierstrassSigma L z = z * cexp (-S) := by
  let T : ℕ → L.lattice → ℂ := fun k l =>
    z ^ (k + 3) / ((k + 3 : ℕ) * (l : ℂ) ^ (k + 3))
  have hW := L.summable_weierstrassPExceptSummand 0 z 0 (fun l hl => by
    simpa using hz l l.2 hl)
  have hinj : Function.Injective (fun p : ℕ × L.lattice => (p.1 + 1, p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq, add_left_inj] at h
    exact Prod.ext h.1 h.2
  have hW' := (summable_norm_iff.mpr (hW.comp_injective hinj)).mul_left (‖z‖ ^ 2)
  have hT : Summable (Function.uncurry T) := by
    refine Summable.of_norm_bounded hW' fun p => ?_
    obtain ⟨k, l⟩ := p
    dsimp only [Function.uncurry, Function.comp_def, T]
    by_cases hl : (l : ℂ) = 0
    · simp [hl, weierstrassPExceptSummand]
    · simp only [weierstrassPExceptSummand, hl, ite_false, Pi.zero_apply, sub_zero,
        norm_div, norm_mul, norm_pow, norm_natCast]
      rw [zpow_neg, zpow_natCast]
      have hden : (1 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by norm_cast; omega
      have hnum : (1 : ℝ) ≤ ‖((k + 1 : ℕ) : ℂ) + 1‖ := by
        rw [show ((k + 1 : ℕ) : ℂ) + 1 = ((k + 2 : ℕ) : ℂ) by push_cast; ring_nf,
          norm_natCast]
        norm_cast
        omega
      have hp : 0 ≤ ‖z‖ ^ (k + 3) * (‖(l : ℂ)‖ ^ (k + 3))⁻¹ := by positivity
      calc
        _ = (‖z‖ ^ (k + 3) * (‖(l : ℂ)‖ ^ (k + 3))⁻¹) /
            ((k + 3 : ℕ) : ℝ) := by rw [div_mul_eq_div_div]; ring_nf
        _ ≤ ‖z‖ ^ (k + 3) * (‖(l : ℂ)‖ ^ (k + 3))⁻¹ := div_le_self hp hden
        _ ≤ ‖((k + 1 : ℕ) : ℂ) + 1‖ *
            (‖z‖ ^ (k + 3) * (‖(l : ℂ)‖ ^ (k + 3))⁻¹) :=
          le_mul_of_one_le_left hp hnum
        _ = _ := by
          rw [show k + 1 + 2 = k + 3 by omega]
          simp only [norm_pow, norm_inv]
          ring_nf
  let F : L.lattice → ℂ := fun l => -log (1 - z / l) - z / l - (z / l) ^ 2 / 2
  have hfib (l : L.lattice) : HasSum (fun k => T k l) (F l) := by
    by_cases hl : (l : ℂ) = 0
    · simp [T, F, hl]
    · have hq : ‖z / l‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.mpr hl)]
        exact hz l l.2 hl
      have h := (hasSum_nat_add_iff' 3).mpr (Complex.hasSum_taylorSeries_neg_log hq)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, div_zero,
        zero_add, Nat.cast_zero, pow_one, Nat.cast_one, div_one, Nat.cast_ofNat] at h
      convert h using 1
      · funext k
        dsimp only [T]
        rw [div_pow]
        field_simp [hl]
      · dsimp only [F]
        ring_nf
  let S : ℂ := ∑' p : ℕ × L.lattice, Function.uncurry T p
  have hcoeff : HasSum (fun k : ℕ => z ^ (k + 3) / (k + 3) * L.G (k + 3)) S := by
    have h := hT.hasSum.prod_fiberwise (fun k => (hT.prod_factor k).hasSum)
    convert h using 1
    funext k
    simp only [T, PeriodPair.G, Function.uncurry_apply_pair]
    rw [← tsum_mul_left]
    congr 1
    funext l
    simp only [div_eq_mul_inv, mul_inv_rev]
    push_cast
    ring_nf
  have htswap : HasSum (fun q : L.lattice × ℕ => T q.2 q.1) S :=
    (Equiv.prodComm L.lattice ℕ).hasSum_iff.mpr hT.hasSum
  have hF : HasSum F S := htswap.prod_fiberwise hfib
  have hp : HasProd (fun l : L.lattice => cexp (-F l)) (cexp (-S)) := by
    simpa only [Complex.exp_eq_exp_ℂ, Function.comp_def] using hF.neg.exp
  have hfactor (l : L.lattice) : cexp (-F l) =
      (1 - z / l) * cexp (z / l + z ^ 2 / (2 * (l : ℂ) ^ 2)) := by
    have hn : 1 - z / l ≠ 0 := by
      by_cases hl : (l : ℂ) = 0
      · simp [hl]
      · intro he
        have hq : ‖z / l‖ < 1 := by
          rw [norm_div, div_lt_one (norm_pos_iff.mpr hl)]
          exact hz l l.2 hl
        rw [← sub_eq_zero.mp he, norm_one] at hq
        exact lt_irrefl _ hq
    dsimp only [F]
    rw [show -(-log (1 - z / l) - z / l - (z / l) ^ 2 / 2) =
        log (1 - z / l) + (z / l + z ^ 2 / (2 * (l : ℂ) ^ 2)) by
      rw [div_pow]; ring_nf, Complex.exp_add, Complex.exp_log hn]
  have hσ : weierstrassSigma L z = z * cexp (-S) := by
    rw [weierstrassSigma, ← hp.tprod_eq]
    congr 1
    exact tprod_congr fun l => (hfactor l).symm
  refine ⟨S, ?_, hσ⟩
  have hinj2 : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b hab
    dsimp only at hab
    omega
  have hzero (k : ℕ) (hk : ¬ ∃ n, (fun n : ℕ => 2 * n + 1) n = k) :
      z ^ (k + 3) / (k + 3) * L.G (k + 3) = 0 := by
    have hkEven : Even k := by
      rcases Nat.even_or_odd k with he | ⟨a, ha⟩
      · exact he
      · exact absurd ⟨a, by dsimp only; omega⟩ hk
    rw [L.G_eq_zero_of_odd _ (by rcases hkEven with ⟨a, ha⟩; exact ⟨a + 1, by omega⟩)]
    simp
  have heven := (hinj2.hasSum_iff hzero).mpr hcoeff
  refine heven.congr_fun fun n => ?_
  simp only [Function.comp_apply]
  rw [show 2 * n + 1 + 3 = 2 * (n + 2) by omega]
  push_cast
  ring_nf

/-- The shifted logarithmic lattice series converges inside the nearest-pole disk. -/
lemma summable_logarithmicLatticeSeries (L : PeriodPair) (x : ℂ) {z : ℂ}
    (hz : ∀ l : L.lattice, ‖z‖ < ‖(l : ℂ) - x‖) :
    Summable (fun n : ℕ => L.sumInvPow x (n + 3) * z ^ (n + 3) / (n + 3)) := by
  let T : ℕ → L.lattice → ℂ := fun k l =>
    z ^ (k + 3) / ((k + 3 : ℕ) * ((l : ℂ) - x) ^ (k + 3))
  have hW := L.summable_weierstrassPSummand (x + z) x (fun l => by
    simpa only [add_sub_cancel_left] using hz l)
  have hinj : Function.Injective (fun p : ℕ × L.lattice => (p.1 + 1, p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq, add_left_inj] at h
    exact Prod.ext h.1 h.2
  have hW' := (summable_norm_iff.mpr (hW.comp_injective hinj)).mul_left (‖z‖ ^ 2)
  have hT : Summable (Function.uncurry T) := by
    refine Summable.of_norm_bounded hW' fun p => ?_
    obtain ⟨k, l⟩ := p
    dsimp only [Function.uncurry, Function.comp_def, T]
    simp only [weierstrassPSummand, Nat.add_one, Pi.zero_apply, sub_zero,
      add_sub_cancel_left, norm_div, norm_mul, norm_pow, norm_natCast, norm_zpow]
    rw [zpow_neg, zpow_natCast]
    have hden : (1 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by norm_cast; omega
    have hnum : (1 : ℝ) ≤ ‖((k + 1 : ℕ) : ℂ) + 1‖ := by
      rw [show ((k + 1 : ℕ) : ℂ) + 1 = ((k + 2 : ℕ) : ℂ) by push_cast; ring_nf,
        norm_natCast]
      norm_cast
      omega
    have hp : 0 ≤ ‖z‖ ^ (k + 3) * (‖(l : ℂ) - x‖ ^ (k + 3))⁻¹ := by positivity
    calc
      _ = (‖z‖ ^ (k + 3) * (‖(l : ℂ) - x‖ ^ (k + 3))⁻¹) /
          ((k + 3 : ℕ) : ℝ) := by rw [div_mul_eq_div_div]; ring_nf
      _ ≤ ‖z‖ ^ (k + 3) * (‖(l : ℂ) - x‖ ^ (k + 3))⁻¹ := div_le_self hp hden
      _ ≤ ‖((k + 1 : ℕ) : ℂ) + 1‖ *
          (‖z‖ ^ (k + 3) * (‖(l : ℂ) - x‖ ^ (k + 3))⁻¹) :=
        le_mul_of_one_le_left hp hnum
      _ = _ := by
        rw [show k + 1 + 2 = k + 3 by omega]
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
        ring_nf
  have h := hT.hasSum.prod_fiberwise (fun k => (hT.prod_factor k).hasSum)
  have hc : Summable (fun n : ℕ => L.sumInvPow x (n + 3) * z ^ (n + 3) / (n + 3)) := by
    convert h.summable using 1
    funext k
    simp only [T, PeriodPair.sumInvPow, Function.uncurry_apply_pair]
    rw [← tsum_mul_right, ← tsum_div_const]
    congr 1
    funext l
    simp only [div_eq_mul_inv, mul_inv_rev]
    push_cast
    ring_nf
  exact hc

end DLMF.Weierstrass
