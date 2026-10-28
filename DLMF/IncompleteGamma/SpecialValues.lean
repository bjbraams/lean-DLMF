/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.Basic
public import DLMF.ErrorFunctions.Basic

/-!
# Special values and confluent representations, DLMF §§8.4–8.5

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Statistical

/-- The finite exponential sum e_n. -/
@[dlmf 8.4.E11]
def expPartialSum (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), z^k/(k.factorial : ℂ)

/-- Identity under the stated parameter and domain assumptions: `lowerIncGamma (1/2)
(z^2)=2*primitive (fun t => exp (-t^2)) z ∧ lowerIncGamma (1/2) (z^2)=Real.sqrt π*erf z`. -/
@[dlmf 8.4.E1]
theorem lowerIncGamma_half_square {z : ℂ} (hz : 0 < z.re) :
    lowerIncGamma (1/2) (z^2)=2*primitive (fun t => exp (-t^2)) z ∧ lowerIncGamma (1/2) (z^2)=Real.sqrt π*erf z := by
  have hz0 := ne_zero_of_re_pos hz
  have he : lowerIncGamma (1/2) (z^2)=(Real.sqrt π:ℂ)*erf z := by
    rw [lowerIncGamma, sq_cpow_of_re_pos hz]
    norm_num only [show (2:ℂ)*(1/2)=1 by norm_num, cpow_one,
      show (1/2:ℂ)+1=3/2 by norm_num]
    rw [kummerM_erf hz0]
    field_simp
  refine ⟨?_,he⟩
  rw [he,erf_complex_segment_integral]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `scIncGamma a 0=1/Gamma (a+1)`. -/
@[dlmf 8.4.E2]
theorem scIncGamma_zero (a : ℂ) :
    scIncGamma a 0=1/Gamma (a+1) := by
  simp [scIncGamma, Complex.regularizedHGFun_zero, regularizedHGFunCoeff]

/-- Identity under the stated parameter and domain assumptions: `scIncGamma (1/2) (-z^2)=2*exp
(z^2)/(z*Real.sqrt π)*dawsonF z`. -/
@[dlmf 8.4.E3]
theorem scIncGamma_half_negative_square {z : ℂ} (hz : z ≠ 0) :
    scIncGamma (1/2) (-z^2)=2*exp (z^2)/(z*Real.sqrt π)*dawsonF z := by
  rw [scIncGamma, dawsonF_eq_kummerM,
    show (1/2:ℂ)+1=3/2 by norm_num,
    kummerM_eq_mul_regularizedHGFun three_half_ne_neg_nat]
  rw [DLMF.Bessel.Gamma_three_halves,Gamma_one_half_eq_sqrt]
  field_simp [hz]

/-- Identity under the stated parameter and domain assumptions: `upperIncGamma 0 z=genExpIntE 1
z`. -/
@[dlmf 8.4.E4]
theorem upperIncGamma_zero_E1 {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma 0 z=genExpIntE 1 z := by
  simp [genExpIntE]

/-- Identity under the stated parameter and domain assumptions: `upperIncGamma (1/2)
(z^2)=Real.sqrt π*erfc z`. -/
@[dlmf 8.4.E6]
theorem upperIncGamma_half_square {z : ℂ} (hz : 0 < z.re) :
    upperIncGamma (1/2) (z^2)=Real.sqrt π*erfc z := by
  rw [upperIncGamma,show (1:ℂ)-1/2=1/2 by norm_num,
    kummerU_erfc (Or.inl hz) hz]
  have he : exp (-z^2)*exp (z^2)=1 := by rw [← Complex.exp_add]; simp
  linear_combination (Real.sqrt π:ℂ)*erfc z*he

/-- Identity under the stated parameter and domain assumptions: `lowerIncGamma (n+1)
z=(n.factorial : ℂ)*(1-exp (-z)*expPartialSum n z)`. -/
@[dlmf 8.4.E7]
theorem lowerIncGamma_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma (n+1) z=(n.factorial : ℂ)*(1-exp (-z)*expPartialSum n z) := by
  have h := normIncGammaP_nat_succ n hz
  rw [normIncGammaP, show (n:ℂ)+1=((n:ℂ)+1) by rfl, Gamma_nat_eq_factorial] at h
  have hn : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply (div_eq_iff hn).mp at h
  simpa [expPartialSum, mul_comm] using h

/-- Identity under the stated parameter and domain assumptions: `upperIncGamma (n+1)
z=(n.factorial : ℂ)*exp (-z)*expPartialSum n z`. -/
@[dlmf 8.4.E8]
theorem upperIncGamma_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma (n+1) z=(n.factorial : ℂ)*exp (-z)*expPartialSum n z := by
  have h := normIncGammaQ_nat_succ n hz
  rw [normIncGammaQ, Gamma_nat_eq_factorial] at h
  have hn : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply (div_eq_iff hn).mp at h
  simpa [expPartialSum, mul_assoc, mul_comm, mul_left_comm] using h

/-- Identity under the stated parameter and domain assumptions: `normIncGammaPContinued (n+1)
z=1-exp (-z)*expPartialSum n z`. -/
@[dlmf 8.4.E9]
theorem normIncGammaPContinued_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaPContinued (n+1) z=1-exp (-z)*expPartialSum n z := by
  rw [normIncGammaPContinued_eq (natCast_add_one_ne_neg_nat n), normIncGammaP_nat_succ n hz]
  rfl

/-- Identity under the stated parameter and domain assumptions: `normIncGammaQContinued (n+1)
z=exp (-z)*expPartialSum n z`. -/
@[dlmf 8.4.E10]
theorem normIncGammaQContinued_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaQContinued (n+1) z=exp (-z)*expPartialSum n z := by
  rw [normIncGammaQContinued_eq (natCast_add_one_ne_neg_nat n) hz, normIncGammaQ_nat_succ n hz]
  rfl

/-- Identity under the stated parameter and domain assumptions: `upperIncGamma (1-n) z=z^(1-(n :
ℂ))*genExpIntE n z`. -/
@[dlmf 8.4.E13]
theorem upperIncGamma_one_minus_nat (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma (1-n) z=z^(1-(n : ℂ))*genExpIntE n z := by
  rw [genExpIntE, ← mul_assoc, ← cpow_add _ _ hz]
  simp

/-- Formula under the stated hypotheses: `normIncGammaQContinued (n+1/2) (z^2)=erfc z+exp
(-z^2)/Real.sqrt π*(∑ k ∈ Finset.range n, z^(2*k+1)/poch (1/2) (k+1))`. -/
@[dlmf 8.4.E14]
theorem normIncGammaQ_half_nat (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    normIncGammaQContinued (n+1/2) (z^2)=erfc z+exp (-z^2)/Real.sqrt π*(∑ k ∈ Finset.range n, z^(2*k+1)/poch (1/2) (k+1)) := by
  have hz0 := ne_zero_of_re_pos hz
  have hp0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have he := normIncGammaQContinued_shift_up n (1/2) (pow_ne_zero 2 hz0)
  rw [show (1/2:ℂ)+n=n+1/2 by ring,
    normIncGammaQContinued_eq half_ne_neg_nat (pow_ne_zero 2 hz0),normIncGammaQ,
    upperIncGamma_half_square hz,Gamma_one_half_eq_sqrt,
    sq_cpow_of_re_pos hz,show (2:ℂ)*(1/2)=1 by norm_num,cpow_one] at he
  rw [he]
  have hc (k : ℕ) : Gamma ((1/2:ℂ)+k+1)=(Real.sqrt π:ℂ)*poch (1/2) (k+1) := by
    have h := Gamma_add_nat_div_Gamma_eq (n:=k+1) (1/2:ℂ) half_ne_neg_nat
    rw [← poch,div_eq_iff (Gamma_ne_zero half_ne_neg_nat)] at h
    rw [Gamma_one_half_eq_sqrt] at h
    convert h using 1 <;> push_cast <;> ring
  simp_rw [hc]
  rw [show (Real.sqrt π:ℂ)*erfc z/(Real.sqrt π:ℂ)=erfc z by field_simp]

  rw [Finset.mul_sum,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [← pow_mul,pow_succ]
  ring

/-- Formula under the stated hypotheses: `upperIncGamma (-n) z=(-1 : ℂ)^n/n.factorial*(genExpIntE
1 z-exp (-z)*∑ k ∈ Finset.range n, (-1 : ℂ)^k*(k.factorial : ℂ)/z^(k+1))`. -/
@[dlmf 8.4.E15]
theorem upperIncGamma_neg_nat_finite (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma (-n) z=(-1 : ℂ)^n/n.factorial*(genExpIntE 1 z-exp (-z)*∑ k ∈ Finset.range n, (-1 : ℂ)^k*(k.factorial : ℂ)/z^(k+1)) := by
  induction n with
  | zero => simp [genExpIntE]
  | succ n ih =>
    have he := upperIncGamma_add_one (-(n:ℂ)-1) hz
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
ℂ)-n)))` converges to `(z^(n : ℤ)*((-1 : ℂ)^n/n.factorial*(digamma (n+1)-log z)-upperIncGamma
(-n) z))`. -/
@[dlmf 8.4.E15]
theorem upperIncGamma_neg_nat_hasSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => if k=n then 0 else (-z)^k/((k.factorial : ℂ)*((k : ℂ)-n))) (z^(n : ℤ)*((-1 : ℂ)^n/n.factorial*(digamma (n+1)-log z)-upperIncGamma (-n) z)) := by
  induction n with
  | zero =>
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, ↓reduceIte, sub_zero, Nat.cast_zero, zpow_zero, one_mul,
      pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, neg_zero,
      upperIncGamma_zero_E1 hz, expIntE1_eq_Ein_complex hz, digamma_one]
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
    · have he := upperIncGamma_add_one (-(n:ℂ)-1) hz
      rw [show -(n:ℂ)-1+1= -n by ring] at he
      rw [cpow_sub (-(n:ℂ)) 1 hz,cpow_one,cpow_neg,cpow_natCast] at he
      have hd := digamma_apply_add_one ((n:ℂ)+1) (fun m hm => by
        have : ((n+1 : ℕ) : ℂ) = -m := by push_cast; exact hm
        have h2 := congrArg Complex.re this
        simp at h2; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
      have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      simp only [Finset.sum_range_one, Nat.factorial_succ, zpow_natCast, Nat.cast_zero, Nat.factorial_zero]
      push_cast
      rw [show -((n:ℂ)+1) = -(n:ℂ)-1 by ring, hd, he]
      have hzn : z ^ n ≠ 0 := pow_ne_zero _ hz
      rw [pow_succ, pow_succ, pow_succ]
      field_simp
      ring

/-- Identity under the stated parameter and domain assumptions: `lowerIncGamma a z=z^a/a*exp
(-z)*kummerM 1 (1+a) z ∧ lowerIncGamma a z=z^a/a*kummerM a (1+a) (-z)`. -/
@[dlmf 8.5.E1]
theorem lowerIncGamma_kummerM_pair {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    lowerIncGamma a z=z^a/a*exp (-z)*kummerM 1 (1+a) z ∧ lowerIncGamma a z=z^a/a*kummerM a (1+a) (-z) := by
  have ha1 := add_one_ne_neg_nat ha
  constructor
  · rw [lowerIncGamma, kummerM_kummer_transform ha1]
    simp only [show a+1-a=1 by ring, neg_neg]
    rw [show 1+a=a+1 by ring]
    ring
  · simp [lowerIncGamma, add_comm, mul_div_assoc]

/-- Identity under the stated parameter and domain assumptions: `scIncGamma a z=exp
(-z)*regularizedHGFun {1} {1+a} z ∧ scIncGamma a z=regularizedHGFun {a} {1+a} (-z)`. -/
@[dlmf 8.5.E2]
theorem scIncGamma_regularized_pair (a z : ℂ) :
    scIncGamma a z=exp (-z)*regularizedHGFun {1} {1+a} z ∧ scIncGamma a z=regularizedHGFun {a} {1+a} (-z) := by
  constructor
  · simp [scIncGamma, add_comm]
  · have h := regularizedConfluent_kummer_transform a (1+a) (-z)
    simpa [scIncGamma, show (1:ℂ)+a-a=1 by ring, add_comm] using h.symm

/-- Identity under the stated parameter and domain assumptions: `upperIncGamma a z=exp
(-z)*kummerU (1-a) (1-a) z ∧ upperIncGamma a z=z^a*exp (-z)*kummerU 1 (1+a) z`. -/
@[dlmf 8.5.E3]
theorem upperIncGamma_kummerU_pair (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma a z=exp (-z)*kummerU (1-a) (1-a) z ∧ upperIncGamma a z=z^a*exp (-z)*kummerU 1 (1+a) z := by
  constructor
  · rfl
  · simpa [add_comm] using upperIncGamma_eq_cpow_mul_kummerU a hz

/-- Identity under the stated parameter and domain assumptions: `lowerIncGamma a z=z^(a/2-1/2)*exp
(-z/2)/a*whittakerM (a/2-1/2) (a/2) z`. -/
@[dlmf 8.5.E4]
theorem lowerIncGamma_whittakerM {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma a z=z^(a/2-1/2)*exp (-z/2)/a*whittakerM (a/2-1/2) (a/2) z := by
  rw [(lowerIncGamma_kummerM_pair ha z).1, whittakerM]
  rw [show a/2-(a/2-1/2)+1/2=(1:ℂ) by ring,
    show (1:ℂ)+2*(a/2)=1+a by ring]
  have hp : z^(a/2-1/2)*z^(a/2+1/2)=z^a := by
    rw [← cpow_add _ _ hz]; congr 1; ring
  have he : exp (-z/2)*exp (-z/2)=exp (-z) := by rw [← Complex.exp_add]; congr 1; ring
  calc
    z^a/a*exp (-z)*kummerM 1 (1+a) z =
        (exp (-z/2)*exp (-z/2))*(z^(a/2-1/2)*z^(a/2+1/2))/a*kummerM 1 (1+a) z := by rw [hp,he]; ring
    _ = _ := by ring

/-- Identity under the stated parameter and domain assumptions: `upperIncGamma a z=exp
(-z/2)*z^(a/2-1/2)*whittakerW (a/2-1/2) (a/2) z`. -/
@[dlmf 8.5.E5]
theorem upperIncGamma_whittakerW (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma a z=exp (-z/2)*z^(a/2-1/2)*whittakerW (a/2-1/2) (a/2) z := by
  rw [(upperIncGamma_kummerU_pair a hz).2, whittakerW]
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
theorem lowerIncGammaOnLog_half (w : ℂ) :
    lowerIncGammaOnLog (1/2) w=(Real.sqrt π:ℂ)*erf (exp (w/2)) := by
  have hu : exp (w/2)≠0 := Complex.exp_ne_zero _
  have hs : exp (w/2)^2=exp w := by rw [← Complex.exp_nat_mul]; congr 1; ring
  have he := kummerM_erf hu
  rw [hs] at he
  rw [kummerM_eq_mul_regularizedHGFun three_half_ne_neg_nat] at he
  rw [lowerIncGammaOnLog,(scIncGamma_regularized_pair _ _).2,
    show (1:ℂ)+1/2=3/2 by ring,Gamma_one_half_eq_sqrt,
    show (1/2:ℂ)*w=w/2 by ring]
  rw [DLMF.Bessel.Gamma_three_halves,Gamma_one_half_eq_sqrt] at he
  field_simp [hu] at he
  linear_combination (Real.sqrt π:ℂ)*he

/-- The upper Gamma continuation is the complementary entire Gaussian primitive at half order. -/
theorem upperIncGammaOnLog_half (w : ℂ) :
    upperIncGammaOnLog (1/2) w=(Real.sqrt π:ℂ)*erfc (exp (w/2)) := by
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
  have hi := segmentIntegral_eq_sub (by fun_prop : Continuous (fun u : ℂ => exp ((1/2:ℂ)*u-exp u))) hd (log (exp w)) w
  have hl : lowerIncGammaOnLog (1/2) (log (exp w))=lowerIncGamma (1/2) (exp w) := by
    rw [lowerIncGammaOnLog,Complex.exp_log (Complex.exp_ne_zero _)]
    rw [show exp ((1/2:ℂ)*log (exp w))=(exp w)^(1/2:ℂ) by
      rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _)]; congr 1; ring]
    rw [mul_assoc,← normIncGammaPContinued,normIncGammaPContinued_eq half_ne_neg_nat,normIncGammaP]
    rw [Gamma_one_half_eq_sqrt]
    field_simp
  rw [lowerIncGammaOnLog_half] at hl
  have hc := lowerIncGamma_add_upperIncGamma half_ne_neg_nat (Complex.exp_ne_zero w)
  rw [Gamma_one_half_eq_sqrt] at hc
  rw [upperIncGammaOnLog,hi]
  simp only [erfc]
  linear_combination hc+hl

/-- The square argument retains its inherited logarithm in the full punctured plane. -/
@[dlmf 7.11.E1, dlmf 8.4.E1]
theorem erf_lowerIncGammaOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erf z=lowerIncGammaOnLog (1/2) (2*log z)/Real.sqrt π := by
  rw [lowerIncGammaOnLog_half,show 2*log z/2=log z by ring,Complex.exp_log hz]
  have hp : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

/-- Identity under the stated parameter and domain assumptions: `erfc z=upperIncGammaOnLog (1/2)
(2*log z)/Real.sqrt π`. -/
@[dlmf 7.11.E2, dlmf 8.4.E6]
theorem erfc_upperIncGammaOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erfc z=upperIncGammaOnLog (1/2) (2*log z)/Real.sqrt π := by
  rw [upperIncGammaOnLog_half,show 2*log z/2=log z by ring,Complex.exp_log hz]
  have hp : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

/-- Identity under the stated parameter and domain assumptions: `erfc z=exp (-z^2)/Real.sqrt
π*kummerUOnLog (1/2) (1/2) (2*log z) ∧ erfc z=z/Real.sqrt π*exp (-z^2)*kummerUOnLog 1 (3/2)
(2*log z)`. -/
@[dlmf 7.11.E5]
theorem erfc_kummerUOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erfc z=exp (-z^2)/Real.sqrt π*kummerUOnLog (1/2) (1/2) (2*log z) ∧ erfc z=z/Real.sqrt π*exp (-z^2)*kummerUOnLog 1 (3/2) (2*log z) := by
  have hp0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hGm : Gamma (-(1/2):ℂ)= -2*(Real.sqrt π:ℂ) := by
    have h := Gamma_add_one (-(1/2):ℂ) (by norm_num)
    rw [show (-(1/2):ℂ)+1=1/2 by ring,Gamma_one_half_eq_sqrt] at h
    linear_combination 2*h
  have he : exp (2*log z)=z^2 := by
    rw [show (2:ℂ)*log z=((2:ℕ):ℂ)*log z by norm_num,Complex.exp_nat_mul,Complex.exp_log hz]
  have hp : exp ((1/2:ℂ)*(2*log z))=z := by rw [show (1/2:ℂ)*(2*log z)=log z by ring,Complex.exp_log hz]
  have hm : exp ((-(1/2):ℂ)*(2*log z))=z⁻¹ := by
    rw [show (-(1/2):ℂ)*(2*log z)= -log z by ring,Complex.exp_neg,Complex.exp_log hz]
  have hhalf : kummerUOnLog (1/2) (1/2) (2*log z)=
      (Real.sqrt π:ℂ)*exp (z^2)*erfc z := by
    unfold kummerUOnLog
    norm_num only
    rw [he,hp,kummerM_self half_ne_neg_nat,Gamma_one,hGm,Gamma_one_half_eq_sqrt,
      kummerM_kummer_transform three_half_ne_neg_nat]
    norm_num only
    rw [kummerM_erf hz]
    simp only [erfc]
    field_simp
    ring
  have hrel : kummerUOnLog 1 (3/2) (2*log z)=
      kummerUOnLog (1/2) (1/2) (2*log z)/z := by
    unfold kummerUOnLog
    norm_num only
    rw [he,hp,hm,Gamma_one,hGm,Gamma_one_half_eq_sqrt,kummerM_self half_ne_neg_nat]
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

end DLMF.Confluent
