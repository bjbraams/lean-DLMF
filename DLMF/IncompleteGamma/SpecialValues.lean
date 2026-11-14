/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.AnalyticProperties
public import DLMF.IncompleteGamma.ContinuedProperties
public import DLMF.Elementary.LogExpIntegrals

/-!
# Special values and confluent representations, DLMF §§8.4–8.5

Special values of the incomplete Gamma functions at half-integral, integral and zero
parameters (DLMF §8.4), their representations through Kummer and Whittaker functions
(DLMF §8.5), and the error-function relations of DLMF §7.11 on the logarithmic plane.

## Main results

* `lowerIncompleteGamma_half_square`, `upperIncompleteGamma_half_square`,
  `tricomiIncompleteGamma_half_negative_square`: the half-order values DLMF 8.4.1, 8.4.6 and 8.4.3.
* `tricomiIncompleteGamma_zero`, `upperIncompleteGamma_zero_E1`: DLMF 8.4.2 and 8.4.4.
* `lowerIncompleteGamma_nat_succ_expPartialSum`, `upperIncompleteGamma_nat_succ_expPartialSum`,
  `regularizedGamma_nat_succ_expPartialSum`,
  `regularizedIncompleteGammaQ_nat_succ_expPartialSum`: integral parameters, DLMF 8.4.7–8.4.10.
* `upperIncompleteGamma_one_minus_nat`, `regularizedIncompleteGammaQ_half_nat`: DLMF 8.4.13
  and 8.4.14.
* `upperIncompleteGamma_neg_nat_finite`, `upperIncompleteGamma_neg_nat_hasSum`: DLMF 8.4.15.
* `lowerIncompleteGamma_kummerM_pair`, `tricomiIncompleteGamma_regularized_pair`,
  `upperIncompleteGamma_kummerU_pair`, `lowerIncompleteGamma_whittakerM`,
  `upperIncompleteGamma_whittakerW`: the confluent representations DLMF 8.5.1–8.5.5.
* `erf_lowerIncompleteGammaOnLog_square`, `erfc_upperIncompleteGammaOnLog_square`,
  `erfc_kummerUConnectionOnLog_square`: DLMF 7.11.1, 7.11.2 and 7.11.5.

## Implementation notes

In DLMF 7.11.1 the square argument keeps its inherited logarithm on the full punctured
plane, so the relations are stated for the logarithmic-plane functions.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Confluent

open DLMF.Statistical

/-- Identity under the stated parameter and domain assumptions: `lowerIncompleteGamma (1/2)
(z^2)=2*primitive (fun t => exp (-t^2)) z ∧ lowerIncompleteGamma (1/2) (z^2)=Real.sqrt π*erf z`. -/
@[dlmf 8.4.E1]
theorem lowerIncompleteGamma_half_square {z : ℂ} (hz : 0 < z.re) :
    lowerIncompleteGamma (1/2) (z^2)=2*primitive (fun t => exp (-t^2)) z ∧
        lowerIncompleteGamma (1/2) (z^2)=Real.sqrt π*erf z := by
  have hz0 := ne_zero_of_re_pos hz
  have he : lowerIncompleteGamma (1/2) (z^2)=(Real.sqrt π:ℂ)*erf z := by
    rw [lowerIncompleteGamma, sq_cpow_of_re_pos hz]
    norm_num only [show (2:ℂ)*(1/2)=1 by norm_num, cpow_one,
      show (1/2:ℂ)+1=3/2 by norm_num]
    rw [kummerM_erf hz0]
    field_simp
  refine ⟨?_,he⟩
  rw [he,erf_complex_segment_integral]
  field_simp

/-- Identity under the stated parameter and domain assumptions:
`tricomiIncompleteGamma a 0=1/Gamma (a+1)`. -/
@[dlmf 8.4.E2]
theorem tricomiIncompleteGamma_zero (a : ℂ) :
    tricomiIncompleteGamma a 0=1/Gamma (a+1) := by
  simp [tricomiIncompleteGamma, Complex.regularizedHGFun_zero, regularizedHGFunCoeff]

/-- Identity under the stated parameter and domain assumptions:
`tricomiIncompleteGamma (1/2) (-z^2)=2*exp (z^2)/(z*Real.sqrt π)*dawsonF z`. -/
@[dlmf 8.4.E3]
theorem tricomiIncompleteGamma_half_negative_square {z : ℂ} (hz : z ≠ 0) :
    tricomiIncompleteGamma (1/2) (-z^2)=2*exp (z^2)/(z*Real.sqrt π)*dawsonF z := by
  rw [tricomiIncompleteGamma, dawsonF_eq_kummerM,
    show (1/2:ℂ)+1=3/2 by norm_num,
    kummerM_eq_mul_regularizedHGFun Complex.three_div_two_ne_neg_natCast]
  rw [DLMF.Bessel.Gamma_three_halves,Complex.Gamma_one_half_eq_sqrt]
  field_simp [hz]

/-- Identity under the stated parameter and domain assumptions:
`upperIncompleteGamma 0 z=expIntegralE 1 z`. -/
@[dlmf 8.4.E4]
theorem upperIncompleteGamma_zero_E1 {z : ℂ} :
    upperIncompleteGamma 0 z=expIntegralE 1 z := by
  simp [expIntegralE]

/-- Identity under the stated parameter and domain assumptions: `upperIncompleteGamma (1/2)
(z^2)=Real.sqrt π*erfc z`. -/
@[dlmf 8.4.E6]
theorem upperIncompleteGamma_half_square {z : ℂ} (hz : 0 < z.re) :
    upperIncompleteGamma (1/2) (z^2)=Real.sqrt π*erfc z := by
  rw [upperIncompleteGamma,show (1:ℂ)-1/2=1/2 by norm_num,
    kummerU_erfc (Or.inl hz) hz]
  have he : exp (-z^2)*exp (z^2)=1 := by rw [← Complex.exp_add]; simp
  linear_combination (Real.sqrt π:ℂ)*erfc z*he

/-- Identity under the stated parameter and domain assumptions: `lowerIncompleteGamma (n+1)
z=(n.factorial : ℂ)*(1-exp (-z)*Elementary.expPartialSum n z)`. -/
@[dlmf 8.4.E7]
theorem lowerIncompleteGamma_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    lowerIncompleteGamma (n+1) z=(n.factorial : ℂ)*(1-exp (-z)*Elementary.expPartialSum n z) := by
  have h := regularizedGamma_nat_succ n hz
  rw [regularizedGamma_eq (natCast_add_one_ne_neg_nat n), show (n:ℂ)+1=((n:ℂ)+1) by rfl,
                                                                       Gamma_nat_eq_factorial] at h
  have hn : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply (div_eq_iff hn).mp at h
  simpa [Elementary.expPartialSum, mul_comm] using h

/-- Identity under the stated parameter and domain assumptions: `upperIncompleteGamma (n+1)
z=(n.factorial : ℂ)*exp (-z)*Elementary.expPartialSum n z`. -/
@[dlmf 8.4.E8]
theorem upperIncompleteGamma_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    upperIncompleteGamma (n+1) z=(n.factorial : ℂ)*exp (-z)*Elementary.expPartialSum n z := by
  have h := regularizedIncompleteGammaQ_nat_succ n hz
  rw [regularizedIncompleteGammaQ_eq' _ hz, Gamma_nat_eq_factorial] at h
  have hn : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply (div_eq_iff hn).mp at h
  simpa [Elementary.expPartialSum, mul_assoc, mul_comm, mul_left_comm] using h

/-- Identity under the stated parameter and domain assumptions: `regularizedGamma (n+1)
z=1-exp (-z)*Elementary.expPartialSum n z`. -/
@[dlmf 8.4.E9]
theorem regularizedGamma_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    regularizedGamma (n+1) z=1-exp (-z)*Elementary.expPartialSum n z := by
  rw [regularizedGamma_nat_succ n hz]
  rfl

/-- Identity under the stated parameter and domain assumptions: `regularizedIncompleteGammaQ (n+1)
z=exp (-z)*Elementary.expPartialSum n z`. -/
@[dlmf 8.4.E10]
theorem regularizedIncompleteGammaQ_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    regularizedIncompleteGammaQ (n+1) z=exp (-z)*Elementary.expPartialSum n z := by
  rw [regularizedIncompleteGammaQ_nat_succ n hz]
  rfl

/-- Identity under the stated parameter and domain assumptions:
`upperIncompleteGamma (1-n) z=z^(1-(n : ℂ))*expIntegralE n z`. -/
@[dlmf 8.4.E13]
theorem upperIncompleteGamma_one_minus_nat (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    upperIncompleteGamma (1-n) z=z^(1-(n : ℂ))*expIntegralE n z := by
  rw [expIntegralE, ← mul_assoc, ← cpow_add _ _ hz]
  simp

/-- Formula under the stated hypotheses: `regularizedIncompleteGammaQ (n+1/2) (z^2)=erfc z+exp
(-z^2)/Real.sqrt π*(∑ k ∈ Finset.range n, z^(2*k+1)/pochhammer (1/2) (k+1))`. -/
@[dlmf 8.4.E14]
theorem regularizedIncompleteGammaQ_half_nat (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    regularizedIncompleteGammaQ (n+1/2) (z^2)=erfc z+exp (-z^2)/Real.sqrt
        π*(∑ k ∈ Finset.range n, z^(2*k+1)/pochhammer (1/2) (k+1)) := by
  have hz0 := ne_zero_of_re_pos hz
  have hp0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have he := regularizedIncompleteGammaQ_shift_up n (1/2) (pow_ne_zero 2 hz0)
  rw [show (1/2:ℂ)+n=n+1/2 by ring,
    regularizedIncompleteGammaQ_eq Complex.one_div_two_ne_neg_natCast (pow_ne_zero 2 hz0),
    upperIncompleteGamma_half_square hz,Complex.Gamma_one_half_eq_sqrt,
    sq_cpow_of_re_pos hz,show (2:ℂ)*(1/2)=1 by norm_num,cpow_one] at he
  rw [he]
  have hc (k : ℕ) : Gamma ((1/2:ℂ)+k+1)=(Real.sqrt π:ℂ)*pochhammer (1/2) (k+1) := by
    have h := Gamma_add_nat_div_Gamma_eq (n:=k+1) (1/2:ℂ) Complex.one_div_two_ne_neg_natCast
    rw [← pochhammer,div_eq_iff (Gamma_ne_zero Complex.one_div_two_ne_neg_natCast)] at h
    rw [Complex.Gamma_one_half_eq_sqrt] at h
    convert h using 1 <;> push_cast <;> ring
  simp_rw [hc]
  rw [show (Real.sqrt π:ℂ)*erfc z/(Real.sqrt π:ℂ)=erfc z by field_simp]

  rw [Finset.mul_sum,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [← pow_mul,pow_succ]
  ring

/-- Formula under the stated hypotheses:
`upperIncompleteGamma (-n) z=(-1 : ℂ)^n/n.factorial*(expIntegralE 1 z-exp (-z)*∑ k ∈ Finset.range n,
(-1 : ℂ)^k*(k.factorial : ℂ)/z^(k+1))`. -/
@[dlmf 8.4.E15]
theorem upperIncompleteGamma_neg_nat_finite (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    upperIncompleteGamma (-n)
        z=(-1 : ℂ)^n/n.factorial*(expIntegralE 1 z-exp (-z)*∑ k ∈ Finset.range n,
        (-1 : ℂ)^k*(k.factorial : ℂ)/z^(k+1)) := by
  induction n with
  | zero => simp [expIntegralE]
  | succ n ih =>
    have he := upperIncompleteGamma_add_one (-(n:ℂ)-1) hz
    rw [show -(n:ℂ)-1+1= -n by ring,ih] at he
    rw [Finset.sum_range_succ,Nat.factorial_succ,pow_succ]
    push_cast at he ⊢
    rw [cpow_sub (-(n:ℂ)) 1 hz,cpow_one,cpow_neg,cpow_natCast] at he
    have hn : (n:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [show -(n+1:ℂ)=-(n:ℂ)-1 by ring]
    have hs : (-1:ℂ)^(n*2)=1 := by rw [Nat.mul_comm,pow_mul]; norm_num
    field_simp [hz,hf,hn] at he ⊢
    linear_combination (norm := ring_nf) he
    rw [hs]
    ring

/-- The series with terms `(fun k : ℕ => if k=n then 0 else (-z)^k/((k.factorial : ℂ)*((k :
ℂ)-n)))` converges to `(z^(n : ℤ)*((-1 : ℂ)^n/n.factorial*(digamma (n+1)-log z)-upperIncompleteGamma
(-n) z))`. -/
@[dlmf 8.4.E15]
theorem upperIncompleteGamma_neg_nat_hasSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => if k=n then 0 else (-z)^k/((k.factorial : ℂ)*((k : ℂ)-n)))
        (z^(n : ℤ)*((-1 : ℂ)^n/n.factorial*(digamma (n+1)-log z)-upperIncompleteGamma (-n) z)) := by
  induction n with
  | zero =>
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, ↓reduceIte, sub_zero, Nat.cast_zero, zpow_zero, one_mul,
      pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, neg_zero,
      upperIncompleteGamma_zero_E1, expIntE1_eq_Ein_complex hz, digamma_one]
    have h := (hasSum_Ein_complex z).neg
    convert h using 1
    · funext k
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [neg_pow, pow_succ]
      push_cast
      ring
    · ring
  | succ n ih =>
    have hexp : HasSum (fun j : ℕ => (-z)^(j+1)/((j+1).factorial : ℂ)) (exp (-z) - 1) := by
      have h : HasSum (fun j : ℕ => (-z)^j/(j.factorial : ℂ)) (exp (-z)) := by
        simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (-z)
      rw [← hasSum_nat_add_iff' 1] at h
      simpa using h
    have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hsum := (((ih.mul_left (-z)).sub (hexp.update n 0)).mul_left (1/((n:ℂ)+1)))
    rw [← hasSum_nat_add_iff' 1]
    convert hsum using 1
    · funext j
      simp only [Function.update_apply]
      by_cases hj : j = n
      · subst hj; simp
      · have hj1 : j + 1 ≠ n + 1 := by omega
        have hjn : (j:ℂ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
        have hj0 : (j:ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
        have hf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
        simp only [hj1, hj, ↓reduceIte]
        rw [Nat.factorial_succ]
        push_cast
        rw [show (j:ℂ)+1-(n+1) = j - n by ring]
        field_simp
        ring
    · have he := upperIncompleteGamma_add_one (-(n:ℂ)-1) hz
      rw [show -(n:ℂ)-1+1= -n by ring] at he
      rw [cpow_sub (-(n:ℂ)) 1 hz,cpow_one,cpow_neg,cpow_natCast] at he
      have hd := digamma_apply_add_one ((n:ℂ)+1) (fun m hm => by
        have : ((n+1 : ℕ) : ℂ) = -m := by push_cast; exact hm
        have h2 := congrArg Complex.re this
        simp at h2; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
      have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      simp only [Finset.sum_range_one, Nat.factorial_succ, zpow_natCast, Nat.cast_zero,
          Nat.factorial_zero]
      push_cast
      rw [show -((n:ℂ)+1) = -(n:ℂ)-1 by ring, hd, he]
      have hzn : z ^ n ≠ 0 := pow_ne_zero _ hz
      rw [pow_succ, pow_succ, pow_succ]
      field_simp
      ring

/-- Identity under the stated parameter and domain assumptions: `lowerIncompleteGamma a z=z^a/a*exp
(-z)*kummerM 1 (1+a) z ∧ lowerIncompleteGamma a z=z^a/a*kummerM a (1+a) (-z)`. -/
@[dlmf 8.5.E1]
theorem lowerIncompleteGamma_kummerM_pair {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    lowerIncompleteGamma a z=z^a/a*exp (-z)*kummerM 1 (1+a) z ∧
        lowerIncompleteGamma a z=z^a/a*kummerM a (1+a) (-z) := by
  have ha1 := add_one_ne_neg_nat ha
  constructor
  · rw [lowerIncompleteGamma, kummerM_kummer_transform ha1]
    simp only [show a+1-a=1 by ring, neg_neg]
    rw [show 1+a=a+1 by ring]
    ring
  · simp [lowerIncompleteGamma, add_comm, mul_div_assoc]

/-- Identity under the stated parameter and domain assumptions: `tricomiIncompleteGamma a z=exp
(-z)*regularizedHGFun {1} {1+a} z ∧ tricomiIncompleteGamma a z=regularizedHGFun {a} {1+a} (-z)`. -/
@[dlmf 8.5.E2]
theorem tricomiIncompleteGamma_regularized_pair (a z : ℂ) :
    tricomiIncompleteGamma a z=exp (-z)*regularizedHGFun {1} {1+a} z ∧
        tricomiIncompleteGamma a z=regularizedHGFun {a} {1+a} (-z) := by
  constructor
  · simp [tricomiIncompleteGamma, add_comm]
  · have h := regularizedConfluent_kummer_transform a (1+a) (-z)
    simpa [tricomiIncompleteGamma, show (1:ℂ)+a-a=1 by ring, add_comm] using h.symm

/-- Identity under the stated parameter and domain assumptions: `upperIncompleteGamma a z=exp
(-z)*kummerU (1-a) (1-a) z ∧ upperIncompleteGamma a z=z^a*exp (-z)*kummerU 1 (1+a) z`. -/
@[dlmf 8.5.E3]
theorem upperIncompleteGamma_kummerU_pair (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    upperIncompleteGamma a z=exp (-z)*kummerU (1-a) (1-a) z ∧
        upperIncompleteGamma a z=z^a*exp (-z)*kummerU 1 (1+a) z := by
  constructor
  · rfl
  · simpa [add_comm] using upperIncompleteGamma_eq_cpow_mul_kummerU a hz

/-- Identity under the stated parameter and domain assumptions:
`lowerIncompleteGamma a z=z^(a/2-1/2)*exp (-z/2)/a*whittakerM (a/2-1/2) (a/2) z`. -/
@[dlmf 8.5.E4]
theorem lowerIncompleteGamma_whittakerM {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    lowerIncompleteGamma a z=z^(a/2-1/2)*exp (-z/2)/a*whittakerM (a/2-1/2) (a/2) z := by
  rw [(lowerIncompleteGamma_kummerM_pair ha z).1, whittakerM]
  rw [show a/2-(a/2-1/2)+1/2=(1:ℂ) by ring,
    show (1:ℂ)+2*(a/2)=1+a by ring]
  have hp : z^(a/2-1/2)*z^(a/2+1/2)=z^a := by
    rw [← cpow_add _ _ hz]; congr 1; ring
  have he : exp (-z/2)*exp (-z/2)=exp (-z) := by rw [← Complex.exp_add]; congr 1; ring
  calc
    z^a/a*exp (-z)*kummerM 1 (1+a) z =
        (exp (-z/2)*exp (-z/2))*(z^(a/2-1/2)*z^(a/2+1/2))/a*kummerM 1 (1+a) z := by rw [hp,he]; ring
    _ = _ := by ring

/-- Identity under the stated parameter and domain assumptions: `upperIncompleteGamma a z=exp
(-z/2)*z^(a/2-1/2)*whittakerW (a/2-1/2) (a/2) z`. -/
@[dlmf 8.5.E5]
theorem upperIncompleteGamma_whittakerW (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    upperIncompleteGamma a z=exp (-z/2)*z^(a/2-1/2)*whittakerW (a/2-1/2) (a/2) z := by
  rw [(upperIncompleteGamma_kummerU_pair a hz).2, whittakerW]
  rw [show (1/2:ℂ)+a/2-(a/2-1/2)=1 by ring,
    show (1:ℂ)+2*(a/2)=1+a by ring]
  have hp : z^(a/2-1/2)*z^(1/2+a/2)=z^a := by
    rw [← cpow_add _ _ hz]; congr 1; ring
  have he : exp (-z/2)*exp (-z/2)=exp (-z) := by rw [← Complex.exp_add]; congr 1; ring
  calc
    z^a*exp (-z)*kummerU 1 (1+a) z =
        (exp (-z/2)*exp (-z/2))*(z^(a/2-1/2)*z^(1/2+a/2))*kummerU 1 (1+a) z := by rw [hp,he]; ring
    _ = _ := by ring

/-- The lower Gamma function on the logarithmic plane at half order has an entire erf primitive. -/
theorem lowerIncompleteGammaOnLog_half (w : ℂ) :
    lowerIncompleteGammaOnLog (1/2) w=(Real.sqrt π:ℂ)*erf (exp (w/2)) := by
  have hu : exp (w/2)≠0 := Complex.exp_ne_zero _
  have hs : exp (w/2)^2=exp w := by rw [← Complex.exp_nat_mul]; congr 1; ring
  have he := kummerM_erf hu
  rw [hs] at he
  rw [kummerM_eq_mul_regularizedHGFun Complex.three_div_two_ne_neg_natCast] at he
  rw [lowerIncompleteGammaOnLog,(tricomiIncompleteGamma_regularized_pair _ _).2,
    show (1:ℂ)+1/2=3/2 by ring,Complex.Gamma_one_half_eq_sqrt,
    show (1/2:ℂ)*w=w/2 by ring]
  rw [DLMF.Bessel.Gamma_three_halves,Complex.Gamma_one_half_eq_sqrt] at he
  field_simp [hu] at he
  linear_combination (Real.sqrt π:ℂ)*he

/-- The upper Gamma continuation is the complementary entire Gaussian primitive at half order. -/
theorem upperIncompleteGammaOnLog_half (w : ℂ) :
    upperIncompleteGammaOnLog (1/2) w=(Real.sqrt π:ℂ)*erfc (exp (w/2)) := by
  have hp0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hd (u : ℂ) : HasDerivAt (fun v => (Real.sqrt π:ℂ)*erf (exp (v/2)))
      (exp ((1/2:ℂ)*u-exp u)) u := by
    have he := ((hasDerivAt_erf_complex (exp (u/2))).comp u
      (((hasDerivAt_id u).div_const 2).cexp)).const_mul (Real.sqrt π:ℂ)
    refine he.congr_deriv ?_
    have hs : exp (u/2)^2=exp u := by rw [← Complex.exp_nat_mul]; congr 1; ring
    simp only [id_eq,one_div,hs]
    rw [show (2:ℂ)⁻¹*u-exp u=u/2+(-exp u) by ring,Complex.exp_add]
    field_simp
  have hi := segmentIntegral_eq_sub hd (log (exp w)) w
  have hl : lowerIncompleteGammaOnLog (1/2) (log (exp w))=lowerIncompleteGamma (1/2) (exp w) := by
    rw [lowerIncompleteGammaOnLog,Complex.exp_log (Complex.exp_ne_zero _)]
    rw [show exp ((1/2:ℂ)*log (exp w))=(exp w)^(1/2:ℂ) by
      rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _)]; congr 1; ring]
    rw [mul_assoc, ← regularizedGamma,
        regularizedGamma_eq Complex.one_div_two_ne_neg_natCast]
    rw [Complex.Gamma_one_half_eq_sqrt]
    field_simp
  rw [lowerIncompleteGammaOnLog_half] at hl
  have hc := lowerIncompleteGamma_add_upperIncompleteGamma Complex.one_div_two_ne_neg_natCast
      (Complex.exp_ne_zero w)
  rw [Complex.Gamma_one_half_eq_sqrt] at hc
  rw [upperIncompleteGammaOnLog,hi]
  simp only [erfc]
  linear_combination hc+hl

/-- The square argument retains its inherited logarithm in the full punctured plane. -/
@[dlmf 7.11.E1, dlmf 8.4.E1]
theorem erf_lowerIncompleteGammaOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erf z=lowerIncompleteGammaOnLog (1/2) (2*log z)/Real.sqrt π := by
  rw [lowerIncompleteGammaOnLog_half,show 2*log z/2=log z by ring,Complex.exp_log hz]
  have hp : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

/-- Identity under the stated parameter and domain assumptions:
`erfc z=upperIncompleteGammaOnLog (1/2) (2*log z)/Real.sqrt π`. -/
@[dlmf 7.11.E2, dlmf 8.4.E6]
theorem erfc_upperIncompleteGammaOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erfc z=upperIncompleteGammaOnLog (1/2) (2*log z)/Real.sqrt π := by
  rw [upperIncompleteGammaOnLog_half,show 2*log z/2=log z by ring,Complex.exp_log hz]
  have hp : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

/-- Identity under the stated parameter and domain assumptions: `erfc z=exp (-z^2)/Real.sqrt
π*kummerUConnectionOnLog (1/2) (1/2) (2*log z) ∧
erfc z=z/Real.sqrt π*exp (-z^2)*kummerUConnectionOnLog 1 (3/2) (2*log z)`. -/
@[dlmf 7.11.E5]
theorem erfc_kummerUConnectionOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erfc z=exp (-z^2)/Real.sqrt π*kummerUConnectionOnLog (1/2) (1/2) (2*log z) ∧
        erfc z=z/Real.sqrt π*exp (-z^2)*kummerUConnectionOnLog 1 (3/2) (2*log z) := by
  have hp0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hGm : Gamma (-(1/2):ℂ)= -2*(Real.sqrt π:ℂ) := by
    have h := Gamma_add_one (-(1/2):ℂ) (by norm_num)
    rw [show (-(1/2):ℂ)+1=1/2 by ring,Complex.Gamma_one_half_eq_sqrt] at h
    linear_combination 2*h
  have he : exp (2*log z)=z^2 := by
    rw [show (2:ℂ)*log z=((2:ℕ):ℂ)*log z by norm_num,Complex.exp_nat_mul,Complex.exp_log hz]
  have hp : exp ((1/2:ℂ)*(2*log z))=z := by
                                           rw [show (1/2:ℂ)*(2*log z)=log z
                                             by ring, Complex.exp_log hz]
  have hm : exp ((-(1/2):ℂ)*(2*log z))=z⁻¹ := by
    rw [show (-(1/2):ℂ)*(2*log z)= -log z by ring,Complex.exp_neg,Complex.exp_log hz]
  have hhalf : kummerUConnectionOnLog (1/2) (1/2) (2*log z)=
      (Real.sqrt π:ℂ)*exp (z^2)*erfc z := by
    unfold kummerUConnectionOnLog
    norm_num only
    rw [he, hp, kummerM_self Complex.one_div_two_ne_neg_natCast, Gamma_one, hGm,
        Complex.Gamma_one_half_eq_sqrt,
      kummerM_kummer_transform Complex.three_div_two_ne_neg_natCast]
    norm_num only
    rw [kummerM_erf hz]
    simp only [erfc]
    field_simp
    ring
  have hrel : kummerUConnectionOnLog 1 (3/2) (2*log z)=
      kummerUConnectionOnLog (1/2) (1/2) (2*log z)/z := by
    unfold kummerUConnectionOnLog
    norm_num only
    rw [he, hp, hm, Gamma_one, hGm, Complex.Gamma_one_half_eq_sqrt,
        kummerM_self Complex.one_div_two_ne_neg_natCast]
    field_simp
    ring
  have hexp : exp (-z^2)*exp (z^2)=1 := by rw [← Complex.exp_add]; simp
  constructor
  · rw [hhalf]
    field_simp
    linear_combination -erfc z*hexp
  · rw [hrel,hhalf]
    field_simp
    linear_combination -erfc z*hexp

/-- Compatibility spelling for the noninteger logarithmic connection expression. -/
@[deprecated erfc_kummerUConnectionOnLog_square (since := "2026-11-14")]
alias erfc_kummerUOnLog_square := erfc_kummerUConnectionOnLog_square

end DLMF.Confluent
