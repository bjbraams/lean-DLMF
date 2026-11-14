/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.GeneralizedHypergeometric.UnitParameterAnalyticity
public import Carlson.TwoVariable.ThreeFTwoExercises
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Thomae transformation at unit argument

The transformation of DLMF 16.4.11 follows from Euler’s transformation under beta integration.
Fixing the two positive excesses then continues the identity in the remaining parameter on
the plane minus two translated nonpositive-integer lattices. This retains every exceptional
upper parameter and the full printed convergence half-space.

* `ThomaeTransformation.generalizedHypergeometric_eq`: the full convergent transformation.

Endpoint beta integration reuses `Carlson.TwoVariable.betaIntegral_mul_threeFTwo` from the
`lean-codes` dependency. Joint parameter analyticity comes from
`DLMF.GeneralizedHypergeometric.UnitParameterAnalyticity`; connectedness of the punctured
parameter plane uses Mathlib’s countable-complement path-connectedness theorem.
-/

public noncomputable section
open Complex Filter Set Finset MeasureTheory
open scoped Topology
namespace DLMF.Hypergeometric.ThomaeTransformation

/-- Carlson’s ordinary unit `₃F₂` series agrees with the principal generalized function
throughout its regular absolute-convergence region. -/
lemma threeFTwo_eq_generalizedHypergeometric {a b c d e : ℂ} (hd : ∀ n : ℕ, d ≠ -(n:ℂ))
    (he : ∀ n : ℕ, e ≠ -(n:ℂ)) (hs : 0 < (d+e-a-b-c).re) :
    Carlson.TwoVariable.threeFTwo a b c d e 1 =
      generalizedHypergeometric {a,b,c} {d,e} 1 := by
  have hden : LowerParametersRegular {d,e} := by
    intro u hu n
    simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] at hu
    rcases hu with rfl|rfl
    · exact hd n
    · exact he n
  have hsum := generalizedHypergeometric_one_hasSum (a := {a,b,c}) (b := {d,e}) (by simp) hden (by
    simp only [parameterExcess,Multiset.insert_eq_cons,Multiset.sum_cons,Multiset.sum_singleton,
      add_re,sub_re] at hs ⊢
    linarith)
  rw [← hsum.tsum_eq,Carlson.TwoVariable.threeFTwo]
  apply tsum_congr
  intro n
  simp only [Carlson.TwoVariable.threeFTwoCoeff,generalizedHypergeometricCoeff,pochhammerProduct,
    Multiset.insert_eq_cons,Multiset.map_cons,Multiset.map_singleton,Multiset.prod_cons,
    Multiset.prod_singleton,one_pow,mul_one,pochhammer]
  ring

/-- Euler transformation under beta integration exchanges the two positive endpoint excesses. -/
lemma betaIntegral_mul_threeFTwo_eq {a b c d e : ℂ} (hd : ∀ n : ℕ, d ≠ -(n:ℂ))
    (ha : 0 < a.re) (hea : 0 < (e-a).re) (hs : 0 < (d+e-a-b-c).re) :
    betaIntegral a (e-a) * Carlson.TwoVariable.threeFTwo b c a d e 1 =
      betaIntegral a (d+e-a-b-c) *
        Carlson.TwoVariable.threeFTwo (d-b) (d-c) a d (d+e-b-c) 1 := by
  have hs' : 0 < (d+e-b-c-a).re := by convert hs using 1;congr 1;ring
  have H1 := Carlson.TwoVariable.betaIntegral_mul_threeFTwo
    (a := b) (b := c) (c := a) (d := d) (e := e) (x := 1) hd ha hea hs' (by simp)
  have H2 := Carlson.TwoVariable.betaIntegral_mul_threeFTwo
    (a := d-b) (b := d-c) (c := a) (d := d) (e := d+e-b-c) (x := 1) hd ha
    (by convert hs using 1;congr 1;ring)
    (by convert hea using 1;congr 1;ring) (by simp)
  rw [show d+e-b-c-a=d+e-a-b-c by ring] at H2
  rw [H1,H2]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hu1 : ‖(u:ℂ)‖ < 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu.1]
    exact hu.2
  have h0 : 1-(u:ℂ) ≠ 0 := by
    have hu' : (u:ℂ) ≠ 1 := by exact_mod_cast (ne_of_lt hu.2)
    exact sub_ne_zero.mpr hu'.symm
  simp only [mul_one]
  rw [euler_transformation_of_ne_neg_nat hd hu1]
  rw [show d+e-a-b-c-1=(e-a-1)+(d-b-c) by ring,cpow_add _ _ h0]
  ring

/-- The unit Thomae transformation when the integrated upper parameter has positive real part. -/
lemma generalizedHypergeometric_eq_of_re_pos {a b c d e : ℂ} (hd : ∀ n : ℕ, d ≠ -(n:ℂ))
    (ha : 0 < a.re) (hea : 0 < (e-a).re) (hs : 0 < (d+e-a-b-c).re) :
    generalizedHypergeometric {a,b,c} {d,e} 1 =
      Gamma e * Gamma (d+e-a-b-c) /
        (Gamma (e-a)*Gamma (d+e-b-c)) *
        generalizedHypergeometric {a,d-b,d-c} {d,d+e-b-c} 1 := by
  have heR : 0 < e.re := by simp only [sub_re] at hea;linarith
  have hDR : 0 < (d+e-b-c).re := by
    have hs' := hs
    simp only [sub_re,add_re] at hs' ha ⊢
    linarith
  have hsumL : 0 < (d+e-b-c-a).re := by convert hs using 1;congr 1;ring
  have hsumR : 0 < (d+(d+e-b-c)-(d-b)-(d-c)-a).re := by
    convert hea using 1;congr 1;ring
  have H := betaIntegral_mul_threeFTwo_eq hd ha hea hs
  rw [threeFTwo_eq_generalizedHypergeometric hd (not_neg_nat_of_re_pos heR) hsumL,
    threeFTwo_eq_generalizedHypergeometric hd (not_neg_nat_of_re_pos hDR) hsumR] at H
  have hleft : ({b,c,a}:Multiset ℂ)={a,b,c} := by
    simp only [Multiset.insert_eq_cons,← Multiset.cons_zero]
    rw [Multiset.cons_swap c a,Multiset.cons_swap b a]
  have hright : ({d-b,d-c,a}:Multiset ℂ)={a,d-b,d-c} := by
    simp only [Multiset.insert_eq_cons,← Multiset.cons_zero]
    rw [Multiset.cons_swap (d-c) a,Multiset.cons_swap (d-b) a]
  rw [hleft,hright] at H
  have hbeta {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
      betaIntegral u v = Gamma u * Gamma v / Gamma (u+v) := by
    rw [Gamma_mul_Gamma_eq_betaIntegral hu hv,
      mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos (by simp;linarith))]
  rw [hbeta ha hea,hbeta ha hs,
    show a+(e-a)=e by ring,show a+(d+e-a-b-c)=d+e-b-c by ring] at H
  have hA := Gamma_ne_zero_of_re_pos ha
  have hE := Gamma_ne_zero_of_re_pos hea
  have heG := Gamma_ne_zero_of_re_pos heR
  have hD := Gamma_ne_zero_of_re_pos hDR
  have hFactor : Gamma a*Gamma (e-a)/Gamma e ≠ 0 := div_ne_zero (mul_ne_zero hA hE) heG
  calc generalizedHypergeometric {a,b,c} {d,e} 1 =
        ((Gamma a*Gamma (d+e-a-b-c)/Gamma (d+e-b-c)) *
          generalizedHypergeometric {a,d-b,d-c} {d,d+e-b-c} 1) /
            (Gamma a*Gamma (e-a)/Gamma e) := by
          apply (eq_div_iff hFactor).mpr
          simpa only [mul_comm] using H
    _ = _ := by field_simp

/-- Thomae’s unit transformation for regular lower parameters and both positive excesses. -/
lemma generalizedHypergeometric_eq {a b c d e : ℂ} (hb : LowerParametersRegular {d,e,d+e-b-c})
    (hs0 : 0 < (d+e-a-b-c).re) (hx0 : 0 < (e-a).re) :
    generalizedHypergeometric {a,b,c} {d,e} 1 =
      Gamma e * Gamma (d+e-a-b-c) /
        (Gamma (e-a)*Gamma (d+e-b-c)) *
        generalizedHypergeometric {a,d-b,d-c} {d,d+e-b-c} 1 := by
  let x := e-a
  let s := d+x-b-c
  have hx : 0 < x.re := hx0
  have hs : 0 < s.re := by
    convert hs0 using 1
    congr 1
    dsimp [s,x]
    ring
  have hd : ∀ n : ℕ, d ≠ -(n:ℂ) := hb _ (by simp)
  let U : Set ℂ := {z | (∀ n : ℕ, z+x ≠ -(n:ℂ)) ∧ (∀ n : ℕ, z+s ≠ -(n:ℂ))}
  have hUeq : U = (range (fun n : ℕ => -(n:ℂ)-x) ∪ range (fun n : ℕ => -(n:ℂ)-s))ᶜ := by
    ext z
    constructor
    · rintro ⟨hzx,hzs⟩ hzbad
      rcases hzbad with hzbad|hzbad
      · rcases hzbad with ⟨n,hn⟩
        apply hzx n
        linear_combination -hn
      · rcases hzbad with ⟨n,hn⟩
        apply hzs n
        linear_combination -hn
    · intro hz
      constructor
      · intro n hn
        apply hz
        left
        exact ⟨n,by linear_combination -hn⟩
      · intro n hn
        apply hz
        right
        exact ⟨n,by linear_combination -hn⟩
  have hUc : IsPreconnected U := by
    rw [hUeq]
    exact (Set.Countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex];norm_num)
      ((countable_range _).union (countable_range _))).isConnected.isPreconnected
  let L (z : ℂ) := generalizedHypergeometric {z,b,c} {d,z+x} 1
  let R (z : ℂ) := Gamma (z+x)*Gamma s/(Gamma x*Gamma (z+s)) *
    generalizedHypergeometric {z,d-b,d-c} {d,z+s} 1
  have hΓ : AnalyticOnNhd ℂ Gamma {z : ℂ | ∀ n : ℕ, z ≠ -(n:ℂ)} := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_not_neg_nat
    intro z hz
    exact (differentiableAt_Gamma z hz).differentiableWithinAt
  have hL : AnalyticOnNhd ℂ L U := by
    intro z hz
    let T (w : ℂ) : Fin 5 → ℂ := ![w,b,c,d,w+x]
    have hT : AnalyticAt ℂ T z := by
      apply analyticAt_pi_iff.mpr
      intro i
      fin_cases i
      · exact analyticAt_id
      · exact analyticAt_const
      · exact analyticAt_const
      · exact analyticAt_const
      · exact analyticAt_id.add (analyticAt_const (v := x))
    have hTr : T z ∈ UnitParameterSeries.convergenceRegion := by
      rw [UnitParameterSeries.convergenceRegion_def]
      constructor
      · intro v hv n
        dsimp [T] at hv
        simp only [Multiset.mem_cons,Multiset.mem_singleton] at hv
        rcases hv with rfl|rfl
        · exact hd n
        · exact hz.1 n
      · convert hs using 1
        congr 1
        dsimp [T,s]
        ring
    exact (UnitParameterSeries.analyticOnNhd_generalizedHypergeometric_one _ hTr).comp hT
  have hR : AnalyticOnNhd ℂ R U := by
    intro z hz
    let T (w : ℂ) : Fin 5 → ℂ := ![w,d-b,d-c,d,w+s]
    have hT : AnalyticAt ℂ T z := by
      apply analyticAt_pi_iff.mpr
      intro i
      fin_cases i
      · exact analyticAt_id
      · exact analyticAt_const
      · exact analyticAt_const
      · exact analyticAt_const
      · exact analyticAt_id.add (analyticAt_const (v := s))
    have hTr : T z ∈ UnitParameterSeries.convergenceRegion := by
      rw [UnitParameterSeries.convergenceRegion_def]
      constructor
      · intro v hv n
        dsimp [T] at hv
        simp only [Multiset.mem_cons,Multiset.mem_singleton] at hv
        rcases hv with rfl|rfl
        · exact hd n
        · exact hz.2 n
      · convert hx using 1
        congr 1
        dsimp [T,s]
        ring
    have hF := (UnitParameterSeries.analyticOnNhd_generalizedHypergeometric_one _ hTr).comp hT
    exact ((((hΓ _ hz.1).comp (x := z)
      (analyticAt_id.add (analyticAt_const (v := x)))).mul analyticAt_const).div
      (analyticAt_const.mul ((hΓ _ hz.2).comp (x := z)
        (analyticAt_id.add (analyticAt_const (v := s)))))
      (mul_ne_zero (Gamma_ne_zero_of_re_pos hx) (Gamma_ne_zero hz.2))).mul hF
  have hone : (1:ℂ) ∈ U := by
    constructor
    · apply not_neg_nat_of_re_pos
      simp only [add_re,one_re]
      linarith
    · apply not_neg_nat_of_re_pos
      simp only [add_re,one_re]
      linarith
  have hEq : L =ᶠ[𝓝 (1:ℂ)] R := by
    have hpos : ∀ᶠ z : ℂ in 𝓝 1, 0 < z.re :=
      continuous_re.continuousAt.eventually (Ioi_mem_nhds (by norm_num : (0:ℝ)<(1:ℂ).re))
    filter_upwards [hpos] with z hz
    have heS : d+(z+x)-z-b-c=s := by dsimp [s];ring
    have heD : d+(z+x)-b-c=z+s := by dsimp [s];ring
    have H := generalizedHypergeometric_eq_of_re_pos (b := b) (c := c) (d := d) (e := z+x) hd hz
      (by simpa only [add_sub_cancel_left] using hx) (by rwa [heS])
    rw [heS,heD,add_sub_cancel_left] at H
    exact H
  have hax : a+x=e := by dsimp [x];ring
  have has : a+s=d+e-b-c := by dsimp [s,x];ring
  have haU : a ∈ U := by
    constructor
    · rw [hax];exact hb _ (by simp)
    · rw [has];exact hb _ (by simp)
  have H := hL.eqOn_of_preconnected_of_eventuallyEq hR hUc hone hEq haU
  dsimp only [L,R] at H
  rw [hax,has] at H
  have hsEq : s=d+e-a-b-c := by dsimp [s,x];ring
  simpa only [hsEq] using H

end DLMF.Hypergeometric.ThomaeTransformation
