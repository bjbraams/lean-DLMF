/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.GeneralizedHypergeometric.AnalyticProperties
import DLMF.Hypergeometric.Basic.ParameterAnalyticity
import DLMFMathlib.Analysis.Complex.ShiftedNorm
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Joint parameter analyticity of convergent `₃F₂(1)`

Uniform coefficient bounds compare parameters near a regular tuple with a fixed nearby
reference tuple. Slightly larger upper real parts and smaller lower real parts preserve
positive excess and dominate every sufficiently late recurrence factor. The resulting normal
convergence includes terminating upper parameters.

* `UnitParameterSeries.analyticOnNhd_generalizedHypergeometric_one`: joint analyticity on the
  complete regular positive-excess domain.

Several-variable analyticity uses the pinned TauCeti Osgood theorem
`ContinuousOn.analyticOnNhd_of_differentiableAt_update`, from
`TauCeti.Analysis.Complex.CauchyIntegralPolydisc`.
-/

public noncomputable section
open Complex Filter Set Finset
open scoped Topology Nat
namespace DLMF.Hypergeometric.UnitParameterSeries

/-- The coefficient of `₃F₂(P₀,P₁,P₂;P₃,P₄;1)` as a function of its five parameters. -/
def coefficient (P : Fin 5 → ℂ) (n : ℕ) : ℂ :=
  generalizedHypergeometricCoeff {P 0,P 1,P 2} {P 3,P 4} n

/-- Regular lower parameters and strictly positive real parameter excess. -/
def convergenceRegion : Set (Fin 5 → ℂ) :=
  {P | LowerParametersRegular {P 3,P 4} ∧ 0 < (P 3+P 4-P 0-P 1-P 2).re}

/-- The defining generalized hypergeometric coefficient. -/
lemma coefficient_def (P : Fin 5 → ℂ) (n : ℕ) : coefficient P n =
    generalizedHypergeometricCoeff {P 0,P 1,P 2} {P 3,P 4} n := by rfl

/-- The defining regularity and excess conditions. -/
lemma convergenceRegion_def : convergenceRegion =
    {P | LowerParametersRegular {P 3,P 4} ∧ 0 < (P 3+P 4-P 0-P 1-P 2).re} := by rfl

/-- Every fixed coefficient is jointly analytic at regular lower parameters. -/
lemma analyticAt_coefficient {P : Fin 5 → ℂ} (hP : LowerParametersRegular {P 3,P 4}) (n : ℕ) :
    AnalyticAt ℂ (fun Q => coefficient Q n) P := by
  have hp (i : Fin 5) (k : ℕ) : AnalyticAt ℂ (fun Q : Fin 5 → ℂ => pochhammer (Q i) k) P := by
    induction k with
    | zero => simpa only [pochhammer_zero] using (analyticAt_const (E := Fin 5 → ℂ) (v := (1 : ℂ)))
    | succ k ih =>
      simp only [pochhammer_succ]
      have hi : AnalyticAt ℂ (fun Q : Fin 5 → ℂ => Q i) P :=
        (ContinuousLinearMap.proj i : (Fin 5 → ℂ) →L[ℂ] ℂ).analyticAt P
      exact ih.mul (hi.add analyticAt_const)
  have hden : pochhammer (P 3) n * pochhammer (P 4) n * (n.factorial : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero
      (pochhammer_ne_zero_of_not_neg_nat (hP _ (by simp)) n)
      (pochhammer_ne_zero_of_not_neg_nat (hP _ (by simp)) n))
      (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  simp only [coefficient,generalizedHypergeometricCoeff,pochhammerProduct,Multiset.insert_eq_cons,
    Multiset.map_cons,Multiset.map_singleton,Multiset.prod_cons,Multiset.prod_singleton]
  exact ((hp 0 n).mul ((hp 1 n).mul (hp 2 n))).div
    (((hp 3 n).mul (hp 4 n)).mul analyticAt_const) hden

/-- The norm recurrence compares consecutive coefficients without excluding zero upper factors. -/
lemma norm_coefficient_succ {P : Fin 5 → ℂ} (hP : LowerParametersRegular {P 3,P 4}) (n : ℕ) :
    ‖coefficient P (n+1)‖ = ‖coefficient P n‖ *
      (‖P 0+(n:ℂ)‖*‖P 1+(n:ℂ)‖*‖P 2+(n:ℂ)‖) /
      (‖P 3+(n:ℂ)‖*‖P 4+(n:ℂ)‖*((n:ℝ)+1)) := by
  have h3 : P 3+(n:ℂ) ≠ 0 := fun h => hP _ (by simp) n (eq_neg_of_add_eq_zero_left h)
  have h4 : P 4+(n:ℂ) ≠ 0 := fun h => hP _ (by simp) n (eq_neg_of_add_eq_zero_left h)
  have hnorm : ‖(n:ℂ)+1‖ = (n:ℝ)+1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using (Complex.norm_natCast (n+1))
  have hr := congrArg norm (generalizedHypergeometricCoeff_succ_mul (a := {P 0,P 1,P 2}) hP n)
  simp only [Multiset.insert_eq_cons,Multiset.map_cons,Multiset.map_singleton,
    Multiset.prod_cons,Multiset.prod_singleton,norm_mul,hnorm] at hr
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (norm_ne_zero_iff.mpr h3)
    (norm_ne_zero_iff.mpr h4)) (by positivity : (n:ℝ)+1 ≠ 0))).mpr
  dsimp only [coefficient]
  simp only [Multiset.insert_eq_cons]
  linear_combination hr

/-- All coefficients are nonzero when every parameter avoids the nonpositive integers. -/
lemma coefficient_ne_zero {P : Fin 5 → ℂ} (hP : ∀ i, ∀ n : ℕ, P i ≠ -(n:ℂ)) (n : ℕ) :
    coefficient P n ≠ 0 := by
  simp only [coefficient,generalizedHypergeometricCoeff,pochhammerProduct,Multiset.insert_eq_cons,
    Multiset.map_cons,Multiset.map_singleton,Multiset.prod_cons,Multiset.prod_singleton]
  exact div_ne_zero (mul_ne_zero (pochhammer_ne_zero_of_not_neg_nat (hP 0) n)
    (mul_ne_zero (pochhammer_ne_zero_of_not_neg_nat (hP 1) n)
      (pochhammer_ne_zero_of_not_neg_nat (hP 2) n)))
    (mul_ne_zero (mul_ne_zero (pochhammer_ne_zero_of_not_neg_nat (hP 3) n)
      (pochhammer_ne_zero_of_not_neg_nat (hP 4) n)) (Nat.cast_ne_zero.mpr n.factorial_ne_zero))

/-- Near a regular positive-excess tuple, a fixed convergent reference series uniformly
dominates every coefficient, including terminating upper parameters. -/
lemma exists_coefficient_majorant {P₀ : Fin 5 → ℂ} (hP₀ : P₀ ∈ convergenceRegion) :
    ∃ Q : Fin 5 → ℂ, Q ∈ convergenceRegion ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ V ∈ 𝓝 P₀, IsOpen V ∧ ∀ P ∈ V, P ∈ convergenceRegion ∧
        ∀ n, ‖coefficient P n‖ ≤ C*‖coefficient Q n‖ := by
  let d : ℝ := (P₀ 3+P₀ 4-P₀ 0-P₀ 1-P₀ 2).re
  have hd : 0 < d := hP₀.2
  let δ := d/10
  have hδ : 0 < δ := by dsimp [δ];positivity
  let ε := min (δ/4) 1
  have hε : 0 < ε := lt_min (by positivity) one_pos
  have hεδ : ε ≤ δ/4 := min_le_left _ _
  have hε1 : ε ≤ 1 := min_le_right _ _
  let Q : Fin 5 → ℂ := fun i => ((P₀ i).re : ℂ) + (if i.val<3 then (δ:ℂ) else -(δ:ℂ)) + I
  have hQall (i : Fin 5) (n : ℕ) : Q i ≠ -(n:ℂ) := by
    intro he
    have H := congrArg Complex.im he
    dsimp only [Q] at H
    split_ifs at H <;> norm_num at H
  have hQreg : LowerParametersRegular {Q 3,Q 4} := by
    intro u hu n
    simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] at hu
    rcases hu with rfl|rfl <;> exact hQall _ n
  have hQex : (Q 3+Q 4-Q 0-Q 1-Q 2).re=d-5*δ := by
    dsimp [Q,d]
    norm_num
    ring
  have hQr : Q ∈ convergenceRegion := ⟨hQreg,by rw [hQex];dsimp [δ];linarith⟩
  let M := ‖P₀‖+δ+2
  have hNormQ (i : Fin 5) : ‖Q i‖ ≤ M := by
    have he : ‖(if i.val<3 then (δ:ℂ) else -(δ:ℂ))‖=δ := by
      split_ifs <;> simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
    have hr : ‖((P₀ i).re : ℂ)‖ ≤ ‖P₀‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs]
      exact (abs_re_le_norm _).trans (norm_le_pi_norm P₀ i)
    calc ‖Q i‖ ≤ ‖((P₀ i).re : ℂ)‖ + ‖(if i.val<3 then (δ:ℂ) else -(δ:ℂ))‖ + ‖I‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ M := by rw [he,norm_I];dsimp [M];linarith
  obtain ⟨N,hN⟩ := exists_nat_gt (M^2/δ)
  have hNbound (n : ℕ) (hn : N ≤ n) : M^2 ≤ (n:ℝ)*δ := by
    have hN' := (div_lt_iff₀ hδ).mp hN
    have hnn : (N:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have eReg : ∀ᶠ P : Fin 5 → ℂ in 𝓝 P₀, LowerParametersRegular {P 3,P 4} := by
    have e3 := ((continuous_apply 3).tendsto P₀).eventually
      (isOpen_not_neg_nat.mem_nhds (hP₀.1 (P₀ 3) (by simp)))
    have e4 := ((continuous_apply 4).tendsto P₀).eventually
      (isOpen_not_neg_nat.mem_nhds (hP₀.1 (P₀ 4) (by simp)))
    filter_upwards [e3,e4] with P h3 h4
    intro u hu n
    simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] at hu
    rcases hu with rfl|rfl
    · exact h3 n
    · exact h4 n
  have eEx : ∀ᶠ P : Fin 5 → ℂ in 𝓝 P₀, 0 < (P 3+P 4-P 0-P 1-P 2).re := by
    exact ((by fun_prop : Continuous (fun P : Fin 5 → ℂ =>
      (P 3+P 4-P 0-P 1-P 2).re)).tendsto P₀).eventually (Ioi_mem_nhds hd)
  have eClose : ∀ᶠ P : Fin 5 → ℂ in 𝓝 P₀, ‖P-P₀‖<ε := by
    filter_upwards [Metric.ball_mem_nhds P₀ hε] with P hP
    simpa only [Metric.mem_ball,dist_eq_norm] using hP
  have eCoeff : ∀ᶠ P : Fin 5 → ℂ in 𝓝 P₀, ∀ n ∈ range (N+1),
      ‖coefficient P n‖ < ‖coefficient P₀ n‖+1 := by
    rw [eventually_all_finset]
    intro n _
    exact (analyticAt_coefficient hP₀.1 n).continuousAt.norm.eventually_lt_const (by linarith)
  obtain ⟨V,hVsub,hVo,hP₀V⟩ := mem_nhds_iff.mp (eReg.and (eEx.and (eClose.and eCoeff)))
  have hV : V ∈ 𝓝 P₀ := hVo.mem_nhds hP₀V
  let C := ∑ n ∈ range (N+1), (‖coefficient P₀ n‖+1)/‖coefficient Q n‖
  have hC : 0 ≤ C := sum_nonneg fun _ _ => by positivity
  refine ⟨Q,hQr,C,hC,V,hV,hVo,?_⟩
  intro P hPV
  obtain ⟨hPreg,hPex,hClose,hSmall⟩ := hVsub hPV
  refine ⟨⟨hPreg,hPex⟩,?_⟩
  have hcoord (i : Fin 5) : ‖P i-P₀ i‖ < ε :=
    (norm_le_pi_norm (P-P₀) i).trans_lt hClose
  have hNormP (i : Fin 5) : ‖P i‖ ≤ M := by
    have hh := norm_add_le (P i-P₀ i) (P₀ i)
    rw [sub_add_cancel] at hh
    have hp := norm_le_pi_norm P₀ i
    dsimp [M]
    linarith [hcoord i,hε1,hδ]
  have hReUpper (i : Fin 5) : (P i).re ≤ (P₀ i).re+ε := by
    have hh := (le_abs_self ((P i-P₀ i).re)).trans_lt ((abs_re_le_norm _).trans_lt (hcoord i))
    simp only [sub_re] at hh
    linarith
  have hReLower (i : Fin 5) : (P₀ i).re-ε ≤ (P i).re := by
    have hh := (neg_abs_le ((P i-P₀ i).re))
    have hh' := (abs_re_le_norm (P i-P₀ i)).trans_lt (hcoord i)
    simp only [sub_re] at hh hh'
    linarith
  have hupper (i : Fin 5) (hi : i.val<3) (n : ℕ) (hn : N ≤ n) :
      ‖P i+(n:ℂ)‖ ≤ ‖Q i+(n:ℂ)‖ := by
    have hre : (P i).re+δ/2 ≤ (Q i).re := by
      simp only [Q,hi,↓reduceIte,add_re,ofReal_re,I_re,add_zero]
      linarith [hReUpper i]
    simpa only [ofReal_natCast] using norm_add_ofReal_le_of_re_gap (hNormP i) hre
      (Nat.cast_nonneg n) (by nlinarith [hNbound n hn])
  have hlower (i : Fin 5) (hi : 3 ≤ i.val) (n : ℕ) (hn : N ≤ n) :
      ‖Q i+(n:ℂ)‖ ≤ ‖P i+(n:ℂ)‖ := by
    have hre : (Q i).re+δ/2 ≤ (P i).re := by
      simp only [Q,show ¬ i.val<3 by omega,↓reduceIte,add_re,ofReal_re,neg_re,I_re,add_zero]
      linarith [hReLower i]
    simpa only [ofReal_natCast] using norm_add_ofReal_le_of_re_gap (hNormQ i) hre
      (Nat.cast_nonneg n) (by nlinarith [hNbound n hn])
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n ≤ N
    · have hnR : n ∈ range (N+1) := mem_range.mpr (by omega)
      have hnQ : ‖coefficient Q n‖ ≠ 0 := norm_ne_zero_iff.mpr (coefficient_ne_zero hQall n)
      have hCn : (‖coefficient P₀ n‖+1)/‖coefficient Q n‖ ≤ C :=
        single_le_sum (f := fun m : ℕ => (‖coefficient P₀ m‖+1)/‖coefficient Q m‖)
          (fun _ _ => by positivity) hnR
      calc ‖coefficient P n‖ ≤ ‖coefficient P₀ n‖+1 := (hSmall n hnR).le
        _ = ((‖coefficient P₀ n‖+1)/‖coefficient Q n‖)*‖coefficient Q n‖ :=
          (div_mul_cancel₀ _ hnQ).symm
        _ ≤ C*‖coefficient Q n‖ := mul_le_mul_of_nonneg_right hCn (norm_nonneg _)
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
      have hkN : N ≤ k := by omega
      have hk := ih k (by omega)
      rw [norm_coefficient_succ hPreg,norm_coefficient_succ hQreg]
      have hD : 0 < ‖Q 3+(k:ℂ)‖*‖Q 4+(k:ℂ)‖*((k:ℝ)+1) := by
        apply mul_pos (mul_pos (norm_pos_iff.mpr ?_) (norm_pos_iff.mpr ?_)) (by positivity)
        · exact fun he => hQall 3 k (eq_neg_of_add_eq_zero_left he)
        · exact fun he => hQall 4 k (eq_neg_of_add_eq_zero_left he)
      calc _ ≤ (C*‖coefficient Q k‖)*
          (‖Q 0+(k:ℂ)‖*‖Q 1+(k:ℂ)‖*‖Q 2+(k:ℂ)‖) /
          (‖Q 3+(k:ℂ)‖*‖Q 4+(k:ℂ)‖*((k:ℝ)+1)) := by
            gcongr
            · exact hupper 0 (by decide) k hkN
            · exact hupper 1 (by decide) k hkN
            · exact hupper 2 (by decide) k hkN
            · exact hlower 3 (by decide) k hkN
            · exact hlower 4 (by decide) k hkN
        _ = _ := by ring

/-- The absolutely convergent unit series sums to the principal generalized function. -/
lemma hasSum_coefficient {P : Fin 5 → ℂ} (hP : P ∈ convergenceRegion) :
    HasSum (coefficient P) (generalizedHypergeometric {P 0,P 1,P 2} {P 3,P 4} 1) := by
  have he : 0 < (parameterExcess {P 0,P 1,P 2} {P 3,P 4}).re := by
    have h := hP.2
    simp only [parameterExcess,Multiset.insert_eq_cons,Multiset.sum_cons,Multiset.sum_singleton,
      add_re,sub_re] at h ⊢
    linarith
  convert (generalizedHypergeometric_one_hasSum (a := {P 0,P 1,P 2}) (b := {P 3,P 4})
      (by simp) hP.1 he) using 1
  funext n
  simp only [coefficient]

/-- The convergent unit `₃F₂` is jointly analytic throughout its regular positive-excess region. -/
lemma analyticOnNhd_generalizedHypergeometric_one :
    AnalyticOnNhd ℂ (fun P : Fin 5 → ℂ => generalizedHypergeometric {P 0,P 1,P 2} {P 3,P 4} 1)
      convergenceRegion := by
  intro P hP
  obtain ⟨Q,hQ,C,_,V,hV,hVo,hbound⟩ := exists_coefficient_majorant hP
  have hsum : Summable (fun n => ‖coefficient Q n‖) := (hasSum_coefficient hQ).summable.norm
  have hc : ContinuousOn (fun R => ∑' n, coefficient R n) V := by
    exact continuousOn_tsum (fun n R hR =>
      (analyticAt_coefficient (hbound R hR).1.1 n).continuousAt.continuousWithinAt)
      (hsum.mul_left C) (fun n R hR => (hbound R hR).2 n)
  have hA : AnalyticOnNhd ℂ (fun R => ∑' n, coefficient R n) V := by
    apply hc.analyticOnNhd_of_differentiableAt_update hVo
    intro R hR i
    let W : Set ℂ := (fun z => Function.update R i z) ⁻¹' V
    have hWo : IsOpen W := hVo.preimage (continuous_const.update i continuous_id)
    have hW : R i ∈ W := by simpa [W] using hR
    have hD : DifferentiableOn ℂ (fun z => ∑' n, coefficient (Function.update R i z) n) W := by
      apply differentiableOn_tsum_of_summable_norm (u := fun n => C*‖coefficient Q n‖)
        (hsum.mul_left C)
      · intro n z hz
        exact ((analyticAt_coefficient (hbound _ hz).1.1 n).differentiableAt.comp z
          (hasDerivAt_update R i z).differentiableAt).differentiableWithinAt
      · exact hWo
      · intro n z hz
        exact (hbound _ hz).2 n
    exact hD.differentiableAt (hWo.mem_nhds hW)
  apply (hA P (mem_of_mem_nhds hV)).congr
  filter_upwards [hV] with R hR
  exact (hasSum_coefficient (hbound R hR).1).tsum_eq

end DLMF.Hypergeometric.UnitParameterSeries
