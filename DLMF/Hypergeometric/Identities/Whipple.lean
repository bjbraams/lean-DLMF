/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Identities.Dixon

/-!
# Whipple transformations and related finite sums

Terminating Whipple transformations and the related finite hypergeometric identities.

Source references and common attribution are retained in
`DLMF.Hypergeometric.Identities`.
-/

@[expose] public section

open Complex

open scoped Real

noncomputable section

namespace DLMF.Hypergeometric

section Whipple

open Filter Finset DLMF.QSeries
open scoped Topology Nat

/-- The exponential difference quotient tends to its complex exponent. -/
private lemma whipple_exp_ratio (a : ℂ) :
    Tendsto (fun t : ℂ => (1-exp (a*t))/(1-exp t)) (𝓝[≠] 0) (𝓝 a) := by
  have h (a : ℂ) : Tendsto (fun t : ℂ => (exp (a*t)-1)/t) (𝓝[≠] 0) (𝓝 a) := by
    have hd : HasDerivAt (fun t : ℂ => exp (a*t)) a 0 := by
      convert ((hasDerivAt_id' (0:ℂ)).const_mul a).cexp using 1; simp
    simpa only [zero_add,mul_zero,exp_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]
      using hd.tendsto_slope_zero
  have hh := (h a).div (h 1) (by norm_num : (1:ℂ) ≠ 0)
  simp only [one_mul,div_one] at hh
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ ht]
  rw [show 1-exp (a*t)=-(exp (a*t)-1) by ring,
    show 1-exp t=-(exp t-1) by ring,neg_div_neg_eq]

/-- The exponential base is different from one on a punctured neighborhood of zero. -/
private lemma whipple_exp_base_ne : ∀ᶠ t : ℂ in 𝓝[≠] 0, 1-exp t ≠ 0 := by
  have h : Tendsto (fun t : ℂ => (exp t-1)/t) (𝓝[≠] 0) (𝓝 (1:ℂ)) := by
    simpa only [zero_add,exp_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]
      using (Complex.hasDerivAt_exp 0).tendsto_slope_zero
  filter_upwards [h.eventually_ne (by norm_num : (1:ℂ) ≠ 0)] with t ht
  intro he
  apply ht
  rw [sub_eq_zero.mp he,sub_self,zero_div]

/-- Finite q-Pochhammer symbols have the classical Pochhammer limit for complex exponents. -/
private lemma whipple_exp_qpoch (a : ℂ) (k : ℕ) :
    Tendsto (fun t : ℂ => qPochhammer (exp (a*t)) (exp t) k/(1-exp t)^k)
      (𝓝[≠] 0) (𝓝 (poch a k)) := by
  induction k with
  | zero => simp [qPochhammer_zero,poch_zero]
  | succ k ih =>
    have h := ih.mul (whipple_exp_ratio (a+k))
    rw [poch_succ]
    refine h.congr' ?_
    filter_upwards [whipple_exp_base_ne] with t ht
    rw [qPochhammer_succ,pow_succ]
    have he : exp (a*t)*exp t^k=exp ((a+k)*t) := by
      rw [←exp_nat_mul,←exp_add];congr 1;ring
    rw [he]
    field_simp

/-- The very-well-poised classical numerator after cancelling its half-parameter ratio. -/
private noncomputable def whippleUnit (a : ℂ) : ℕ → ℂ
  | 0 => 1
  | k+1 => poch (a+1) k*(a+2*(k+1))

/-- The cancelled very-well-poised factor has its classical limit. -/
private lemma whipple_unit_limit (a : ℂ) (k : ℕ) :
    Tendsto (fun t : ℂ => DLMF.Bailey.unitD (exp (a*t)) (exp t) k/(1-exp t)^k)
      (𝓝[≠] 0) (𝓝 (whippleUnit a k)) := by
  cases k with
  | zero => simp [DLMF.Bailey.unitD,whippleUnit]
  | succ k =>
    have h := (whipple_exp_qpoch (a+1) k).mul (whipple_exp_ratio (a+2*(k+1)))
    refine h.congr' ?_
    filter_upwards [whipple_exp_base_ne] with t ht
    rw [DLMF.Bailey.unitD]
    have he : exp (a*t)*exp t=exp ((a+1)*t) := by rw [←exp_add];congr 1;ring
    have he' : exp (a*t)*exp t^(2*(k+1))=exp ((a+2*(k+1))*t) := by
      rw [←exp_nat_mul,←exp_add];congr 1;push_cast;ring
    rw [he,he',pow_succ]
    field_simp

/-- The cancelled numerator equals the standard half-parameter Pochhammer ratio. -/
private lemma whippleUnit_eq (a : ℂ) (ha : ∀ j : ℕ, a/2 ≠ -j) (k : ℕ) :
    whippleUnit a k=poch a k*poch (a/2+1) k/poch (a/2) k := by
  cases k with
  | zero => simp [whippleUnit,poch_zero]
  | succ k =>
    have ha0 : a ≠ 0 := by intro h;simpa [h] using ha 0
    have hP := poch_ne_zero_of_not_neg_nat ha (k+1)
    have hs : (a/2)*poch (a/2+1) (k+1)=poch (a/2) (k+1)*(a/2+(k+1)) := by
      rw [←poch_succ_left,poch_succ]
      push_cast
      ring
    rw [whippleUnit,poch_succ_left a k]
    generalize poch (a/2+1) (k+1)=X at hs ⊢
    generalize poch (a/2) (k+1)=Y at hP hs ⊢
    field_simp
    linear_combination -2*poch (a+1) k*hs

/-- A finite product of normalized q-Pochhammer factors has its termwise limit. -/
private lemma whipple_qprod_limit (xs : List ℂ) (k : ℕ) :
    Tendsto (fun t : ℂ => (xs.map (fun a => qPochhammer (exp (a*t)) (exp t) k/(1-exp t)^k)).prod)
      (𝓝[≠] 0) (𝓝 ((xs.map (fun a => poch a k)).prod)) := by
  induction xs with
  | nil => simp
  | cons a xs ih => simpa only [List.map_cons,List.prod_cons] using (whipple_exp_qpoch a k).mul ih

/-- Collect the common normalization power in a finite q-Pochhammer product. -/
private lemma whipple_qprod_normalize (xs : List ℂ) (k : ℕ) (t : ℂ) :
    (xs.map (fun a => qPochhammer (exp (a*t)) (exp t) k/(1-exp t)^k)).prod =
      (xs.map (fun a => qPochhammer (exp (a*t)) (exp t) k)).prod/(1-exp t)^(xs.length*k) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,ih,Nat.add_mul,pow_add]
    rw [mul_comm ((1-exp t)^(xs.length*k)) ((1-exp t)^(1*k))]
    simp only [one_mul]
    ring

/-- Ratios with equally many finite q-Pochhammer factors have classical limits. -/
private lemma whipple_qratio_limit (xs ys : List ℂ) (hlen : xs.length=ys.length) (k : ℕ)
    (hy : ∀ a ∈ ys, poch a k ≠ 0) :
    Tendsto (fun t : ℂ => (xs.map (fun a => qPochhammer (exp (a*t)) (exp t) k)).prod /
      (ys.map (fun a => qPochhammer (exp (a*t)) (exp t) k)).prod)
      (𝓝[≠] 0) (𝓝 ((xs.map (fun a => poch a k)).prod/(ys.map (fun a => poch a k)).prod)) := by
  have hY : (ys.map (fun a => poch a k)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hx
    obtain ⟨a,ha,h0⟩ := List.mem_map.mp hx
    exact hy a ha h0
  have h := (whipple_qprod_limit xs k).div (whipple_qprod_limit ys k) hY
  refine h.congr' ?_
  filter_upwards [whipple_exp_base_ne] with t ht
  simp only [Pi.div_apply,whipple_qprod_normalize,hlen]
  exact div_div_div_cancel_right₀ (pow_ne_zero _ ht) _ _

/-- Include the cancelled very-well-poised factor in the finite product limit. -/
private lemma whipple_unit_ratio_limit (a : ℂ) (xs ys : List ℂ) (hlen : xs.length+1=ys.length) (k : ℕ)
    (hy : ∀ b ∈ ys, poch b k ≠ 0) :
    Tendsto (fun t : ℂ => DLMF.Bailey.unitD (exp (a*t)) (exp t) k *
      (xs.map (fun b => qPochhammer (exp (b*t)) (exp t) k)).prod /
      (ys.map (fun b => qPochhammer (exp (b*t)) (exp t) k)).prod)
      (𝓝[≠] 0) (𝓝 (whippleUnit a k*(xs.map (fun b => poch b k)).prod/
        (ys.map (fun b => poch b k)).prod)) := by
  have hY : (ys.map (fun b => poch b k)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hx
    obtain ⟨b,hb,h0⟩ := List.mem_map.mp hx
    exact hy b hb h0
  have h := ((whipple_unit_limit a k).mul (whipple_qprod_limit xs k)).div
    (whipple_qprod_limit ys k) hY
  refine h.congr' ?_
  filter_upwards [whipple_exp_base_ne] with t ht
  simp only [Pi.div_apply,whipple_qprod_normalize,←hlen,Nat.add_mul,pow_add,one_mul]
  field_simp

/-- The shifted denominator parameter in exponential coordinates. -/
private lemma whipple_exp_param (a b t : ℂ) :
    exp (a*t)*exp t/exp (b*t)=exp ((a-b+1)*t) := by
  rw [←exp_add,←exp_sub];congr 1;ring

/-- A negative integer base power in exponential coordinates. -/
private lemma whipple_exp_neg_pow (t : ℂ) (n : ℕ) : (exp t)⁻¹^n=exp (-(n:ℂ)*t) := by
  rw [←exp_neg,←exp_nat_mul];congr 1;ring

/-- The terminating denominator parameter in exponential coordinates. -/
private lemma whipple_exp_nparam (a t : ℂ) (n : ℕ) :
    exp (a*t)*exp t*exp t^n=exp ((a+n+1)*t) := by
  rw [←exp_nat_mul,←exp_add,←exp_add];congr 1;ring

/-- The balanced denominator parameter in exponential coordinates. -/
private lemma whipple_exp_yparam (a d e t : ℂ) (n : ℕ) :
    exp (d*t)*exp (e*t)*(exp t)⁻¹^n/exp (a*t)=exp ((d+e-a-n)*t) := by
  rw [whipple_exp_neg_pow,←exp_add,←exp_add,←exp_sub];congr 1;ring

/-- The transformed numerator parameter in exponential coordinates. -/
private lemma whipple_exp_xparam (a b c t : ℂ) :
    exp (a*t)*exp t/(exp (b*t)*exp (c*t))=exp ((a-b-c+1)*t) := by
  rw [←exp_add,←exp_add,←exp_sub];congr 1;ring

/-- Every exponential parameter tends to one with the base. -/
private lemma whipple_exp_tendsto (a : ℂ) : Tendsto (fun t : ℂ => exp (a*t)) (𝓝[≠] 0) (𝓝 1) := by
  have h : ContinuousAt (fun t : ℂ => exp (a*t)) 0 := by fun_prop
  simpa using h.tendsto.mono_left nhdsWithin_le_nhds

/-- The finite Watson summand tends to the very-well-poised classical summand. -/
private lemma whipple_watson8_limit (a b c d e : ℂ) (n k : ℕ)
    (hden : ∀ p ∈ [a-b+1,a-c+1,a-d+1,a-e+1,a+n+1,1], ∀ j : ℕ, p ≠ -j) :
    Tendsto (fun t : ℂ => DLMF.Bailey.watsonR8 (exp (a*t)) (exp (b*t))
      (exp (c*t)) (exp (d*t)) (exp (e*t)) (exp t) n k) (𝓝[≠] 0)
      (𝓝 (whippleUnit a k*poch b k*poch c k*poch d k*poch e k*poch (-(n:ℂ)) k/
        (poch (a-b+1) k*poch (a-c+1) k*poch (a-d+1) k*poch (a-e+1) k*
          poch (a+n+1) k*poch 1 k))) := by
  have hscale := (((((whipple_exp_tendsto a).pow 2).mul
    ((whipple_exp_tendsto 1).pow 2)).mul ((whipple_exp_tendsto 1).pow n)).div
    ((((whipple_exp_tendsto b).mul (whipple_exp_tendsto c)).mul
      (whipple_exp_tendsto d)).mul (whipple_exp_tendsto e)) (by norm_num)).pow k
  simp only [one_mul,one_pow,one_div,inv_one] at hscale
  have h := (whipple_unit_ratio_limit a [b,c,d,e,-(n:ℂ)]
    [a-b+1,a-c+1,a-d+1,a-e+1,a+n+1,1] rfl k
    (fun p hp => poch_ne_zero_of_not_neg_nat (hden p hp) k)).mul hscale
  convert h using 1
  · funext t
    simp only [Pi.div_apply,neg_mul,DLMF.Bailey.watsonR8,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,mul_one,one_mul,whipple_exp_neg_pow,whipple_exp_param,whipple_exp_nparam]
    ring
  · simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    ring

/-- The transformed Watson summand tends to its classical terminating summand. -/
private lemma whipple_watson4_limit (a b c d e : ℂ) (n k : ℕ)
    (hden : ∀ p ∈ [a-b+1,a-c+1,d+e-a-n,1], ∀ j : ℕ, p ≠ -j) :
    Tendsto (fun t : ℂ => DLMF.Bailey.watsonR4 (exp (a*t)) (exp (b*t))
      (exp (c*t)) (exp (d*t)) (exp (e*t)) (exp t) n k) (𝓝[≠] 0)
      (𝓝 (poch (a-b-c+1) k*poch d k*poch e k*poch (-(n:ℂ)) k/
        (poch (a-b+1) k*poch (a-c+1) k*poch (d+e-a-n) k*poch 1 k))) := by
  have h := (whipple_qratio_limit [-(n:ℂ),d,e,a-b-c+1]
    [a-b+1,a-c+1,d+e-a-n,1] rfl k
    (fun p hp => poch_ne_zero_of_not_neg_nat (hden p hp) k)).mul
      ((whipple_exp_tendsto 1).pow k)
  convert h using 1
  · funext t
    simp only [DLMF.Bailey.watsonR4]
    rw [whipple_exp_yparam]
    simp only [neg_mul,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,mul_one,one_mul,whipple_exp_neg_pow,whipple_exp_param,whipple_exp_xparam]
    ring
  · simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_pow]
    ring

/-- The shifted numerator parameter in exponential coordinates. -/
private lemma whipple_exp_oneparam (a t : ℂ) : exp (a*t)*exp t=exp ((a+1)*t) := by
  rw [←exp_add];congr 1;ring

/-- A nonzero classical Pochhammer limit ensures nonzero nearby q-Pochhammer factors. -/
private lemma whipple_qpoch_eventually_ne (a : ℂ) (k : ℕ) (ha : poch a k ≠ 0) :
    ∀ᶠ t : ℂ in 𝓝[≠] 0,qPochhammer (exp (a*t)) (exp t) k ≠ 0 := by
  filter_upwards [(whipple_exp_qpoch a k).eventually_ne ha] with t ht
  intro h0
  apply ht
  rw [h0,zero_div]

/-- Whipple's terminating very well-poised `₇F₆(1)` transformation into a balanced
`₄F₃(1)`, AAR Theorem 3.4.4 and the terminating case of DLMF 16.4.15.
The proof takes the complex-parameter exponential-base limit of the proved rational
Watson transformation `DLMF.Bailey.watsonR`. -/
@[dlmf 16.4.E15]
theorem whipple_7F6 {a b c d e : ℂ} (m : ℕ)
    (hden : ∀ z ∈ [a / 2, a - b + 1, a - c + 1, a - d + 1,
      a - e + 1, a + m + 1, d + e - a - m], ∀ k : ℕ, z ≠ -k) :
    (∑ n ∈ Finset.range (m + 1),
      poch a n * poch (a / 2 + 1) n * poch b n * poch c n * poch d n * poch e n *
        poch (-m : ℂ) n /
        (poch (a / 2) n * poch (a - b + 1) n * poch (a - c + 1) n *
          poch (a - d + 1) n * poch (a - e + 1) n * poch (a + m + 1) n * n.factorial)) =
      poch (a + 1) m * poch (a - d - e + 1) m /
        (poch (a - d + 1) m * poch (a - e + 1) m) *
      (∑ n ∈ Finset.range (m + 1),
        poch (a - b - c + 1) n * poch d n * poch e n * poch (-m : ℂ) n /
          (poch (a - b + 1) n * poch (a - c + 1) n *
            poch (d + e - a - m) n * n.factorial)) := by
  have hA := hden (a/2) (by simp)
  have hB := hden (a-b+1) (by simp)
  have hC := hden (a-c+1) (by simp)
  have hD := hden (a-d+1) (by simp)
  have hE := hden (a-e+1) (by simp)
  have hN := hden (a+m+1) (by simp)
  have hY := hden (d+e-a-m) (by simp)
  have h1 : ∀ j : ℕ,(1:ℂ) ≠ -j := not_neg_nat_of_re_pos (by norm_num)
  have hden8 : ∀ p ∈ [a-b+1,a-c+1,a-d+1,a-e+1,a+m+1,1], ∀ j : ℕ,p ≠ -j := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hden4 : ∀ p ∈ [a-b+1,a-c+1,d+e-a-m,1], ∀ j : ℕ,p ≠ -j := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  have hL := tendsto_finsetSum (Finset.range (m+1)) fun k _ =>
    whipple_watson8_limit a b c d e m k hden8
  have hPref0 := whipple_qratio_limit [a+1,a-d-e+1] [a-d+1,a-e+1] rfl m (by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact poch_ne_zero_of_not_neg_nat hD m
    · exact poch_ne_zero_of_not_neg_nat hE m)
  have hPref : Tendsto (fun t : ℂ =>
      qPochhammer (exp (a*t)*exp t) (exp t) m*
        qPochhammer (exp (a*t)*exp t/(exp (d*t)*exp (e*t))) (exp t) m/
      (qPochhammer (exp (a*t)*exp t/exp (d*t)) (exp t) m*
        qPochhammer (exp (a*t)*exp t/exp (e*t)) (exp t) m)) (𝓝[≠] 0)
      (𝓝 (poch (a+1) m*poch (a-d-e+1) m/(poch (a-d+1) m*poch (a-e+1) m))) := by
    convert hPref0 using 1
    · funext t
      rw [whipple_exp_xparam,whipple_exp_param,whipple_exp_param,whipple_exp_oneparam]
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    · simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  have hR := hPref.mul (tendsto_finsetSum (Finset.range (m+1)) fun k _ =>
    whipple_watson4_limit a b c d e m k hden4)
  have hQB := whipple_qpoch_eventually_ne (a-b+1) m (poch_ne_zero_of_not_neg_nat hB m)
  have hQC := whipple_qpoch_eventually_ne (a-c+1) m (poch_ne_zero_of_not_neg_nat hC m)
  have hQD := whipple_qpoch_eventually_ne (a-d+1) m (poch_ne_zero_of_not_neg_nat hD m)
  have hQE := whipple_qpoch_eventually_ne (a-e+1) m (poch_ne_zero_of_not_neg_nat hE m)
  have hQN := whipple_qpoch_eventually_ne (a+m+1) m (poch_ne_zero_of_not_neg_nat hN m)
  have hQY := whipple_qpoch_eventually_ne (d+e-a-m) m (poch_ne_zero_of_not_neg_nat hY m)
  have hQQ : ∀ᶠ t : ℂ in 𝓝[≠] 0,∀ k ∈ Finset.range (m+1),
      qPochhammer (exp t) (exp t) k ≠ 0 := by
    refine (Filter.eventually_all_finset _).mpr fun k _ => ?_
    simpa only [one_mul] using
      whipple_qpoch_eventually_ne 1 k (poch_ne_zero_of_not_neg_nat h1 k)
  have heq : (fun t : ℂ => ∑ k ∈ Finset.range (m+1),DLMF.Bailey.watsonR8
      (exp (a*t)) (exp (b*t)) (exp (c*t)) (exp (d*t)) (exp (e*t)) (exp t) m k) =ᶠ[𝓝[≠] 0]
      (fun t : ℂ =>
      qPochhammer (exp (a*t)*exp t) (exp t) m*
        qPochhammer (exp (a*t)*exp t/(exp (d*t)*exp (e*t))) (exp t) m/
      (qPochhammer (exp (a*t)*exp t/exp (d*t)) (exp t) m*
        qPochhammer (exp (a*t)*exp t/exp (e*t)) (exp t) m)*
      ∑ k ∈ Finset.range (m+1),DLMF.Bailey.watsonR4
        (exp (a*t)) (exp (b*t)) (exp (c*t)) (exp (d*t)) (exp (e*t)) (exp t) m k) := by
    filter_upwards [hQB,hQC,hQD,hQE,hQN,hQY,hQQ] with t hB hC hD hE hN hY hQ
    refine DLMF.Bailey.watsonR m (exp_ne_zero _) (exp_ne_zero _) (exp_ne_zero _)
      (exp_ne_zero _) (exp_ne_zero _) (exp_ne_zero _) (fun k hk => hQ k (by simpa using hk))
      ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [whipple_exp_param] using hB
    · simpa only [whipple_exp_param] using hC
    · simpa only [whipple_exp_param] using hD
    · simpa only [whipple_exp_param] using hE
    · simpa only [whipple_exp_yparam] using hY
    · simpa only [whipple_exp_nparam] using hN
  have h := tendsto_nhds_unique hL (hR.congr' heq.symm)
  simp only [poch_nat_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [whippleUnit_eq a hA]
  ring

end Whipple

open DougallAux in
/-- Dougall's bilateral `₂H₂` sum, in Gamma form (AAR Theorem 2.8.2). -/
@[dlmf 15.4.E25, dlmf 16.4.E17]
theorem dougall_bilateral {a b c d : ℂ}
    (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k)
    (hconv : 1 + (a + b).re < (c + d).re) :
    (∑' n : ℤ, Gamma (a + n) * Gamma (b + n) /
      (Gamma (c + n) * Gamma (d + n))) =
      π ^ 2 * Gamma (c + d - a - b - 1) /
        (sin (π * a) * sin (π * b) * Gamma (c - a) * Gamma (d - a) *
          Gamma (c - b) * Gamma (d - b)) := by
  change ∑' n : ℤ, term a b c d n = _
  by_cases hc : ∀ k : ℤ, c ≠ k
  · exact tsum_eq_of_not_int ha hb hc hconv
  by_cases hd : ∀ k : ℤ, d ≠ k
  · rw [← rhs_comm]
    simp_rw [term_comm a b c d]
    exact tsum_eq_of_not_int ha hb hd (by rwa [add_comm d c])
  push Not at hc hd
  obtain ⟨j, rfl⟩ := hc
  obtain ⟨m, rfl⟩ := hd
  rcases le_total m j with hjm | hjm
  · exact tsum_at_int_int ha hb hjm hconv
  · rw [← rhs_comm]
    simp_rw [term_comm a b (j : ℂ) (m : ℂ)]
    exact tsum_at_int_int ha hb hjm (by rwa [add_comm (m : ℂ) (j : ℂ)])

/-- The complete elliptic integral of the first kind as the hypergeometric series of AAR §3.2,
in the modulus `k`: `K = (π/2) ₂F₁(1/2, 1/2; 1; k²)`, meaningful for `‖k‖ < 1`. The real integral
form in the parameter `m = k²` is `DLMF.Elliptic.Real.compEllIntKm`. -/
@[dlmf 19.5.E1]
def compEllIntKkSeries (k : ℂ) : ℂ :=
  (π / 2) * ₂F₁ (1 / 2 : ℂ) (1 / 2) 1 (k ^ 2)

/-- The reciprocal square root of the square of a positive real number. -/
theorem cpow_sq_neg_half {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = (x : ℂ)⁻¹ := by
  have hh : ((x : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (x : ℂ) := by
    rw [← ofReal_pow, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← ofReal_cpow (sq_nonneg x), ← Real.sqrt_eq_rpow, Real.sqrt_sq hx.le]
  rw [cpow_neg, hh]

/-- The substitution `t = sin² θ` for the beta weight with parameters `1/2, 1/2`. -/
theorem integral_beta_half_weight (f : ℝ → ℂ) :
    (∫ t : ℝ in (0 : ℝ)..1,
      (t : ℂ) ^ (-(1 / 2 : ℂ)) * (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) * f t) =
      2 * ∫ θ : ℝ in (0 : ℝ)..(π / 2), f (Real.sin θ ^ 2) := by
  let g : ℝ → ℂ := fun t =>
    (t : ℂ) ^ (-(1 / 2 : ℂ)) * (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) * f t
  have hd (θ : ℝ) : HasDerivAt (fun u : ℝ => Real.sin u ^ 2)
      (2 * Real.sin θ * Real.cos θ) θ := by
    convert! (Real.hasDerivAt_sin θ).pow 2 using 1
    simp
  have hnonneg {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
      0 ≤ 2 * Real.sin θ * Real.cos θ := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := (0 : ℝ)) (b := π / 2) (g := g)
    (show ContinuousOn (fun θ : ℝ => Real.sin θ ^ 2) (Set.uIcc 0 (π / 2)) by fun_prop)
    (fun θ _ => hd θ) (fun θ hθ => hnonneg (by
      simpa [min_eq_left Real.pi_div_two_pos.le, max_eq_right Real.pi_div_two_pos.le] using hθ))
  simp only [Real.sin_zero, zero_pow (by decide : 2 ≠ 0), Real.sin_pi_div_two,
    one_pow] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_div_two_pos.le
  intro θ hθ
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsq : 1 - (Real.sin θ : ℂ) ^ 2 = (Real.cos θ : ℂ) ^ 2 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq θ] :
      1 - Real.sin θ ^ 2 = Real.cos θ ^ 2)
  simp only [Function.comp_apply, g, real_smul, ofReal_mul, ofReal_ofNat, ofReal_pow]
  rw [hsq, cpow_sq_neg_half hs, cpow_sq_neg_half hc]
  field_simp [ofReal_ne_zero.mpr hs.ne', ofReal_ne_zero.mpr hc.ne']
  apply (div_eq_iff (mul_ne_zero (ofReal_ne_zero.mpr hs.ne')
    (ofReal_ne_zero.mpr hc.ne'))).2
  ring

/-- AAR §3.2: `K(k) = (π/2) ₂F₁(1/2,1/2;1;k²)` is the definition above; the equivalent
integral `∫_0^{π/2} (1-k² sin²θ)^{-1/2} dθ` follows by `t = sin² θ` in Euler's integral. -/
@[dlmf 19.2.E4]
theorem compEllIntKkSeries_eq_integral {k : ℝ} (hk : |k| < 1) :
    compEllIntKkSeries k =
      ∫ θ : ℝ in (0 : ℝ)..(π / 2), (1 - (k : ℂ) ^ 2 * sin θ ^ 2) ^ (-(1 / 2 : ℂ)) := by
  have hhalf : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hsub : (1 : ℂ) - 1 / 2 = 1 / 2 := by ring
  have hz : ‖(k : ℂ) ^ 2‖ < 1 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_lt_one₀ (abs_nonneg k) hk (by decide)
  have hgamma : Gamma (1 / 2 : ℂ) * Gamma (1 / 2) = (π : ℂ) := by
    have h := Gamma_mul_Gamma_one_sub (1 / 2)
    rw [hsub, show (π : ℂ) * (1 / 2) = π / 2 by ring, sin_pi_div_two, div_one] at h
    exact h
  unfold compEllIntKkSeries
  rw [ordinaryHypergeometric_eq_integral hhalf (by rwa [hsub]) hz,
    hsub, Gamma_one, hgamma]
  have hexp : (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) := by ring
  simp only [hexp]
  rw [integral_beta_half_weight]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hi : (∫ θ : ℝ in (0 : ℝ)..(π / 2),
      (1 - (k : ℂ) ^ 2 * ((Real.sin θ ^ 2 : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ))) =
      ∫ θ : ℝ in (0 : ℝ)..(π / 2),
        (1 - (k : ℂ) ^ 2 * sin θ ^ 2) ^ (-(1 / 2 : ℂ)) := by
    simp only [ofReal_pow, ofReal_sin]
  rw [hi]
  field [hpi]

end DLMF.Hypergeometric

end
end
