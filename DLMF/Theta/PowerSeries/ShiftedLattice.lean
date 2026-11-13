/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic.PowerSeries
import DLMF.Theta.PowerSeries.LatticeCoefficients
import DLMF.Weierstrass.Series.LogarithmicSigma
import DLMF.Weierstrass.Basic.LatticesAndSigma
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# Convergence of logarithmic theta series on shifted lattice disks

The distance to the shifted zero lattice controls absolute convergence and analyticity
of the logarithmic power series in DLMF 20.6.3–20.6.5.
-/

public section

set_option maxHeartbeats 0
open Complex PeriodPair Filter DLMF.Weierstrass
open scoped Real Topology
namespace DLMF.Theta.LogarithmicTheta

/-- A nondegenerate theta lattice has positive distance from zero to its nonzero points. -/
lemma thetaLatticeMinNorm_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < thetaLatticeMinNorm τ := by
  let : Nonempty {p : ℤ × ℤ // p ≠ 0} := ⟨⟨(1, 0), by decide⟩⟩
  let σ : UpperHalfPlane := ⟨τ, hτ⟩
  refine lt_of_lt_of_le (mul_pos (EisensteinSeries.r_pos σ) Real.pi_pos)
    (le_ciInf fun p => ?_)
  let v : Fin 2 → ℤ := ![p.1.2, p.1.1]
  have hv : v ≠ 0 := by
    intro h
    apply p.2
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
    exact Prod.ext h1 h0
  have hn : (1 : ℝ) ≤ ‖v‖ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have hvi : (1 : ℝ) ≤ ‖v i‖ := by
      rw [Int.norm_eq_abs]
      exact_mod_cast Int.one_le_abs hi
    exact hvi.trans (norm_le_pi_norm v i)
  have hb := EisensteinSeries.r_mul_max_le σ hv
  have hle : EisensteinSeries.r σ ≤ ‖(p.1.1 : ℂ) + p.1.2 * τ‖ := by
    calc
      _ ≤ EisensteinSeries.r σ * ‖v‖ :=
        le_mul_of_one_le_right (EisensteinSeries.r_pos σ).le hn
      _ ≤ _ := by simpa [v, σ, add_comm] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact mul_le_mul_of_nonneg_right hle Real.pi_pos.le

/-- The shifted logarithmic lattice series converges absolutely inside its zero-free disk. -/
lemma summable_norm_shiftedLatticeLogSeries {τ z : ℂ} (hτ : 0 < τ.im) (a b : ℝ)
    (hz : ‖π * z‖ < thetaShiftedLatticeMinNorm a b τ) :
    Summable (fun j : ℕ => ‖(∑' n : ℤ, ∑' m : ℤ,
        (((m : ℂ) - a + ((n : ℂ) - b) * τ) ^ (2 * (j + 1)))⁻¹) *
      z ^ (2 * (j + 1)) / (2 * (j + 1))‖) := by
  let H := HalfPeriods.ofTau (1 / 2 : ℂ) (by norm_num) ⟨τ, hτ⟩
  have h1 : H.ω₁ = 1 / 2 := rfl
  have h3 : H.ω₃ = τ / 2 := by dsimp only [H, HalfPeriods.ofTau]; ring_nf
  let x : ℂ := a + b * τ
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hbound (l : H.periodPair.lattice) : ‖z‖ < ‖(l : ℂ) - x‖ := by
    obtain ⟨m, n, he⟩ := H.mem_lattice_iff.mp l.2
    rw [h1, h3] at he
    have he' : (l : ℂ) - x = (m : ℂ) - a + ((n : ℂ) - b) * τ := by
      dsimp only [x]
      linear_combination he
    have hh := hz.trans_le (thetaShiftedLatticeMinNorm_le a b τ (m, n))
    rw [← he'] at hh
    have hh' : ‖(π : ℂ)‖ * ‖z‖ < ‖(π : ℂ)‖ * ‖(l : ℂ) - x‖ := by
      simpa only [norm_mul, mul_comm] using hh
    exact (mul_lt_mul_iff_of_pos_left (norm_pos_iff.mpr hπ)).mp hh'
  have hs := summable_logarithmicLatticeSeries H.periodPair x hbound
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro c d h
    dsimp only at h
    omega
  have ht := hs.comp_injective hinj
  apply (summable_nat_add_iff 1).mp
  apply summable_norm_iff.mpr
  convert ht using 1
  funext n
  simp only [Function.comp_apply]
  rw [show 2 * n + 1 + 3 = 2 * (n + 2) by omega]
  rw [sumInvPow_eq_shifted_lattice H h1 h3 a b (by omega : 2 < 2 * (n + 2))]
  rw [show n + 1 + 1 = n + 2 by omega]
  push_cast
  congr 1
  ring_nf

/-- The shifted logarithmic lattice series is analytic inside its zero-free disk. -/
lemma analyticOnNhd_shiftedLatticeLogSeries {τ : ℂ} (hτ : 0 < τ.im) (a b : ℝ) :
    AnalyticOnNhd ℂ (fun z => ∑' j : ℕ, (∑' n : ℤ, ∑' m : ℤ,
        (((m : ℂ) - a + ((n : ℂ) - b) * τ) ^ (2 * (j + 1)))⁻¹) *
      z ^ (2 * (j + 1)) / (2 * (j + 1)))
      {z | ‖π * z‖ < thetaShiftedLatticeMinNorm a b τ} := by
  intro z hz
  change ‖π * z‖ < thetaShiftedLatticeMinNorm a b τ at hz
  have hπ : 0 < ‖(π : ℂ)‖ := norm_pos_iff.mpr (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hz' : ‖z‖ < thetaShiftedLatticeMinNorm a b τ / ‖(π : ℂ)‖ := by
    rw [lt_div_iff₀ hπ]
    simpa only [norm_mul, mul_comm] using hz
  obtain ⟨R, hzR, hRρ⟩ := exists_between hz'
  have hR : 0 < R := (norm_nonneg z).trans_lt hzR
  have hRbound : ‖π * (R : ℂ)‖ < thetaShiftedLatticeMinNorm a b τ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le, mul_comm] using
      (lt_div_iff₀ hπ).mp hRρ
  let c : ℕ → ℂ := fun j => ∑' n : ℤ, ∑' m : ℤ,
    (((m : ℂ) - a + ((n : ℂ) - b) * τ) ^ (2 * (j + 1)))⁻¹
  let F : ℕ → ℂ → ℂ := fun j w => c j * w ^ (2 * (j + 1)) / (2 * (j + 1))
  have hs : Summable (fun j => ‖F j (R : ℂ)‖) :=
    summable_norm_shiftedLatticeLogSeries hτ a b hRbound
  have hb (j : ℕ) (w : ℂ) (hw : w ∈ Metric.ball 0 R) : ‖F j w‖ ≤ ‖F j (R : ℂ)‖ := by
    dsimp only [F]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
    gcongr
    exact (show ‖w‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hw).le
  have hd := differentiableOn_tsum_of_summable_norm hs (F := F)
    (fun j => by dsimp only [F]; fun_prop) Metric.isOpen_ball hb
  exact (hd.analyticOnNhd Metric.isOpen_ball) z (by simpa using hzR)

end DLMF.Theta.LogarithmicTheta
