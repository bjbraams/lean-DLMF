/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.GeneralizedCalculus
public import DLMF.Confluent.Regularized
public import ToMathlib.Analysis.SpecialFunctions.GammaShiftBounds

/-!
# Joint continuity of the regularized generalized hypergeometric series

Uniform reciprocal-Gamma bounds from lean-codes control the regularized `₁F₂(1;b,c;z)` series
jointly in both lower parameters and the argument, including exceptional lower parameters.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology Nat

namespace DLMF.Hypergeometric

/-- The regularized `₁F₂(1;b,c;q)` is jointly continuous in its lower parameters and argument. -/
theorem continuous_regularized1F2_one :
    Continuous (fun p : ℂ × ℂ × ℂ => regularizedHGFun {1} {p.1,p.2.1} p.2.2) := by
  have heq : (fun p : ℂ × ℂ × ℂ => regularizedHGFun {1} {p.1,p.2.1} p.2.2)=
      fun p => ∑' n : ℕ, p.2.2^n*(Gamma (p.1+n))⁻¹*(Gamma (p.2.1+n))⁻¹ := by
    funext p
    rw [(hasSum_regularized1F2 1 p.1 p.2.1 p.2.2).tsum_eq.symm]
    congr 1
    funext n
    rw [regularized1F2_one_coeff]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [heq]
  apply DLMF.Confluent.continuous_tsum_of_eventually_dominated
  · intro n
    exact ((by fun_prop : Continuous fun p : ℂ × ℂ × ℂ => p.2.2^n).mul
      (differentiable_one_div_Gamma.continuous.comp (by fun_prop))).mul
      (differentiable_one_div_Gamma.continuous.comp (by fun_prop))
  · intro p
    have hs := (hasSum_regularized1F2 1 p.1 p.2.1 p.2.2).summable
    refine hs.congr fun n => ?_
    rw [regularized1F2_one_coeff]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · intro p₀
    let K : Set ℂ := Metric.closedBall p₀.1 1 ∪ Metric.closedBall p₀.2.1 1
    have hK : IsCompact K := (isCompact_closedBall _ _).union (isCompact_closedBall _ _)
    obtain ⟨m,C,hC,hbound⟩ := Complex.exists_uniform_norm_inv_Gamma_add_nat hK
    let R := ‖p₀.2.2‖+1
    let u : ℕ → ℝ := fun n => C^2*R^n/((n-m)!)
    have hu : Summable u := by
      rw [← summable_nat_add_iff m]
      convert (Real.summable_pow_div_factorial R).mul_left (C^2*R^m) using 1
      funext n
      simp only [u,Nat.add_sub_cancel,pow_add]
      ring
    refine ⟨Metric.ball p₀ 1,Metric.isOpen_ball,Metric.mem_ball_self (by norm_num),m,u,hu,?_⟩
    intro n hn p hp
    have hp₁ : p.1 ∈ K := Or.inl (show dist p.1 p₀.1 ≤ 1 from
      (le_max_left _ _).trans hp.le)
    have hp₂ : p.2.1 ∈ K := Or.inr (show dist p.2.1 p₀.2.1 ≤ 1 from
      ((le_max_left _ _).trans (le_max_right _ _)).trans hp.le)
    have hp₃ : ‖p.2.2‖ ≤ R := by
      have hd : dist p.2.2 p₀.2.2 ≤ 1 :=
        ((le_max_right _ _).trans (le_max_right _ _)).trans hp.le
      have ht : ‖p.2.2‖ ≤ ‖p.2.2-p₀.2.2‖+‖p₀.2.2‖ := by
        calc ‖p.2.2‖=‖(p.2.2-p₀.2.2)+p₀.2.2‖ := by congr 1; ring
             _ ≤ _ := norm_add_le _ _
      rw [dist_eq_norm] at hd
      dsimp only [R]
      linarith
    have h₁ := hbound p.1 hp₁ (n-m)
    have h₂ := hbound p.2.1 hp₂ (n-m)
    rw [← Nat.cast_add,Nat.sub_add_cancel hn] at h₁ h₂
    have hf : (1:ℝ) ≤ ((n-m)! : ℕ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero (n-m))
    have hc : C/(((n-m)! : ℕ):ℝ) ≤ C := div_le_self hC hf
    simp only [norm_mul,norm_pow]
    calc ‖p.2.2‖^n*‖(Gamma (p.1+n))⁻¹‖*‖(Gamma (p.2.1+n))⁻¹‖
        ≤ R^n*C*(C/(((n-m)! : ℕ):ℝ)) := by gcongr; exact h₁.trans hc
      _ = u n := by dsimp only [u]; ring


end DLMF.Hypergeometric
