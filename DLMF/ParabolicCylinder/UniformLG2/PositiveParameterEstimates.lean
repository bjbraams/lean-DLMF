/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.UniformLG2.NegativeParameterEstimates

/-!
# Uniform cylinder estimates for positive parameters

Whole-line comparison solutions, coefficient bounds and normalizing functions for positive
cylinder parameters.

Source references and common attribution are retained in
`DLMF.ParabolicCylinder.UniformLG2`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

open Polynomial

/-! ### Positive parameter: the whole-line expansion and the normalizer identity -/

/-- The barred polynomial `t ↦ Re(i^e P(-it))`, as a real polynomial. -/
noncomputable def pcfLG2_bar (e : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  ∑ n ∈ Finset.range (P.natDegree + 1), C (P.coeff n * (I^e * (-I)^n).re) * X^n

/-- Evaluation of the barred polynomial. -/
lemma pcfLG2_bar_eval (e : ℕ) (P : Polynomial ℝ) (t : ℝ) :
    (pcfLG2_bar e P).eval t = (I^e * aeval (-I * t) P).re := by
  rw [pcfLG2_bar, eval_finsetSum, aeval_eq_sum_range, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [Complex.real_smul, show I^e * ((P.coeff n : ℂ) * (-I * t)^n) =
    ((P.coeff n * t^n : ℝ) : ℂ) * (I^e * (-I)^n) by push_cast; ring, Complex.re_ofReal_mul]
  ring

/-- `i^e (-i)^n` is real when `n + e` is even. -/
lemma pcfLG2_im_I_pow {e n : ℕ} (h : Even (n + e)) : (I^e * (-I)^n).im = 0 := by
  obtain ⟨k, hk⟩ := h
  have : I^e * (-I)^n = (((-1)^n * (-1)^k : ℝ) : ℂ) := by
    rw [neg_pow, show I^e * ((-1)^n * I^n) = (-1)^n * I^(n+e) by ring, hk, ← two_mul,
      pow_mul, I_sq]
    push_cast; ring
  rw [this, Complex.ofReal_im]

/-- For a polynomial of parity `e`, `i^e P(-it)` is real. -/
lemma pcfLG2_bar_real {e D : ℕ} {P : Polynomial ℝ} (hP : pcfLG_good e D P) (t : ℝ) :
    I^e * aeval (-I * t) P = (((pcfLG2_bar e P).eval t : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · rw [pcfLG2_bar_eval, Complex.ofReal_re]
  · rw [Complex.ofReal_im, aeval_eq_sum_range, Finset.mul_sum, Complex.im_sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [Complex.real_smul, show I^e * ((P.coeff n : ℂ) * (-I * t)^n) =
      ((P.coeff n * t^n : ℝ) : ℂ) * (I^e * (-I)^n) by push_cast; ring, Complex.im_ofReal_mul]
    by_cases hc : P.coeff n = 0
    · simp [hc]
    · rw [pcfLG2_im_I_pow (hP n hc).1, mul_zero]

/-- The barred polynomial has degree at most that of `P`. -/
lemma pcfLG2_natDegree_bar (e : ℕ) (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d) :
    (pcfLG2_bar e P).natDegree ≤ d := by
  refine (natDegree_sum_le_of_forall_le _ _ fun n hn => ?_)
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := Finset.mem_range.1 hn; omega

/-- Coefficients of the barred polynomial. -/
lemma pcfLG2_bar_coeff (e : ℕ) (P : Polynomial ℝ) (n : ℕ) :
    (pcfLG2_bar e P).coeff n = P.coeff n * (I^e * (-I)^n).re := by
  rw [pcfLG2_bar, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hn
    have : P.natDegree < n := by simpa using hn
    simp [coeff_eq_zero_of_natDegree_lt this]

/-- The barred polynomial keeps the parity class. -/
lemma pcfLG2_bar_good {e D : ℕ} {P : Polynomial ℝ} (hP : pcfLG_good e D P) (e' : ℕ) :
    pcfLG_good e D (pcfLG2_bar e' P) := fun n hn => by
  rw [pcfLG2_bar_coeff] at hn
  exact hP n (left_ne_zero_of_mul hn)

/-- Parity: `P(-t) = (-1)^e P(t)` for `P` of parity `e`. -/
lemma pcfLG2_eval_neg {e D : ℕ} {P : Polynomial ℝ} (hP : pcfLG_good e D P) (t : ℝ) :
    P.eval (-t) = (-1)^e * P.eval t := by
  rw [eval_eq_sum_range, eval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hc : P.coeff n = 0
  · simp [hc]
  · have h2 : (-1:ℝ)^(n+e) = 1 := (hP n hc).1.neg_one_pow
    have : (-1:ℝ)^n = (-1)^e := by
      calc (-1:ℝ)^n = (-1)^n * ((-1)^e)^2 := by
            rw [← pow_mul, mul_comm e 2, pow_mul]; norm_num
        _ = (-1)^(n+e) * (-1)^e := by ring
        _ = (-1)^e := by rw [h2, one_mul]
    rw [neg_pow, this]; ring

/-- Derivative of `t ↦ i^e P(-it)` (complex-valued). -/
lemma pcfLG2_hasDerivAt_aeval (e : ℕ) (P : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => I^e * aeval (-I * t) P)
      (I^(e+3) * aeval (-I * t) (derivative P)) t := by
  have h1 : HasDerivAt (fun t : ℝ => -I * (t:ℂ)) (-I) t := by
    simpa using ((hasDerivAt_id (t:ℂ)).const_mul (-I)).comp_ofReal
  have := ((P.hasDerivAt_aeval (-I * (t:ℂ))).comp t h1).const_mul (I^e)
  refine this.congr_deriv ?_
  rw [pow_add, show I^3 = -I by rw [pow_succ, I_sq]; ring]; ring

/-- Derivative of the barred polynomial. -/
lemma pcfLG2_hasDerivAt_bar (e : ℕ) (P : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (fun t => (pcfLG2_bar e P).eval t) ((pcfLG2_bar (e+3) (derivative P)).eval t) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (pcfLG2_hasDerivAt_aeval e P t)
  simp only [Function.comp_def, Complex.reCLM_apply] at h
  rw [pcfLG2_bar_eval]
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun x => pcfLG2_bar_eval e P x)

/-- `Q_s(t) = Re(i^s u_s(-it))` (DLMF 12.10.27). -/
noncomputable def pcfLG2_Q (s : ℕ) : Polynomial ℝ := pcfLG2_bar s (pcfOlverU s)
/-- `R_s(t) = Re(i^{s+1} r_{s-1}(-it))`. -/
noncomputable def pcfLG2_R (s : ℕ) : Polynomial ℝ := pcfLG2_bar (s+1) (pcfOlverPair s).2

/-- The barred form of DLMF 12.10.11: `(t²+1)Q_s' - 3stQ_s = R_s`. -/
lemma pcfLG2_QR_eq (s : ℕ) (t : ℝ) :
    (t^2+1) * (pcfLG2_bar (s+3) (derivative (pcfOlverU s))).eval t -
      3*s*t*(pcfLG2_Q s).eval t = (pcfLG2_R s).eval t := by
  have h := congrArg (aeval (-I * (t:ℂ))) (pcfLG_olverU_eq s)
  simp only [map_sub, map_mul, map_pow, aeval_X, map_one, aeval_C] at h
  simp only [pcfLG2_Q, pcfLG2_R, pcfLG2_bar_eval]
  set U' := aeval (-I * (t:ℂ)) (derivative (pcfOlverU s))
  set U := aeval (-I * (t:ℂ)) (pcfOlverU s)
  set ρ := aeval (-I * (t:ℂ)) (pcfOlverPair s).2
  have hI2 : I^2 = -1 := I_sq
  have hc : ((t^2+1 : ℝ) : ℂ) * (I^(s+3) * U') - ((3*s*t : ℝ) : ℂ) * (I^s * U) =
      I^(s+1) * ρ := by
    rw [← h]
    push_cast
    rw [pow_add, pow_add]
    linear_combination (-(3*(t:ℂ)*(s:ℂ)*I^s*U) + I*I^s*U') * hI2
  have := congrArg Complex.re hc
  simp only [Complex.sub_re, Complex.re_ofReal_mul] at this
  linarith

/-- The barred form of DLMF 12.10.12. -/
lemma pcfLG2_R_succ (s : ℕ) (t : ℝ) :
    (pcfLG2_R (s+1)).eval t = 1/8*(3*t^2-2)*(pcfLG2_Q s).eval t -
      3/2*(s+1)*t*(pcfLG2_R s).eval t +
      1/2*(t^2+1)*(pcfLG2_bar (s+1+3) (derivative (pcfOlverPair s).2)).eval t := by
  have h := congrArg (aeval (-I * (t:ℂ))) (pcfLG_olverPair_snd_succ s)
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, map_one, aeval_C] at h
  simp only [pcfLG2_Q, pcfLG2_R, pcfLG2_bar_eval]
  have hU : pcfOlverU s = (pcfOlverPair s).1 := rfl
  rw [hU]
  set U := aeval (-I * (t:ℂ)) (pcfOlverPair s).1
  set ρ := aeval (-I * (t:ℂ)) (pcfOlverPair s).2
  set ρ' := aeval (-I * (t:ℂ)) (derivative (pcfOlverPair s).2)
  set ρ1 := aeval (-I * (t:ℂ)) (pcfOlverPair (s+1)).2
  have hI2 : I^2 = -1 := I_sq
  have hc : I^(s+1+1) * ρ1 = ((1/8*(3*t^2-2) : ℝ) : ℂ) * (I^s * U) -
      ((3/2*(s+1)*t : ℝ) : ℂ) * (I^(s+1) * ρ) + ((1/2*(t^2+1) : ℝ) : ℂ) * (I^(s+1+3) * ρ') := by
    rw [h]
    push_cast
    simp only [pow_add, pow_one]
    linear_combination (3/2*(t:ℂ)*(s:ℂ)*I^s*ρ*I + 3/2*(t:ℂ)*I^s*ρ*I + 1/4*I^s*U -
      1/2*I^s*ρ'*I^2 + 3/8*(t:ℂ)^2*I^s*U*(I^2-1)) * hI2
  have := congrArg Complex.re hc
  simp only [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul] at this
  linarith

/-- Derivative of `q(t) (t²+1)^c`. -/
lemma pcfLG2_hasDerivAt_mul_rpow {q : ℝ → ℝ} {d t : ℝ} (hq : HasDerivAt q d t) (c : ℝ) :
    HasDerivAt (fun t => q t * (t^2+1) ^ c) ((d * (t^2+1) + 2*c*t*q t) * (t^2+1) ^ (c-1)) t := by
  have hy : 0 < t^2+1 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => t^2+1) (2*t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const 1
  have h2 := h1.rpow_const (p := c) (Or.inl hy.ne')
  have := hq.mul h2
  convert this using 1
  have e : (t^2+1) ^ c = (t^2+1) * (t^2+1) ^ (c-1) := by
    conv_lhs => rw [show c = 1 + (c-1) by ring]
    rw [Real.rpow_add hy, Real.rpow_one]
  rw [e]; ring

/-- The amplitude `A = (t²+1)^{-1/4}` for positive parameter. -/
noncomputable def pcfLG2_PA (t : ℝ) : ℝ := (t^2+1) ^ (-1/4:ℝ)
/-- `A'`. -/
noncomputable def pcfLG2_PA1 (t : ℝ) : ℝ := -(t/2) * (t^2+1) ^ (-5/4:ℝ)
/-- `A''`. -/
noncomputable def pcfLG2_PA2 (t : ℝ) : ℝ := (3*t^2-2)/4 * (t^2+1) ^ (-9/4:ℝ)

/-- `A' = -(t/2)(t²+1)^{-5/4}`. -/
lemma pcfLG2_hasDerivAt_PA (t : ℝ) : HasDerivAt pcfLG2_PA (pcfLG2_PA1 t) t := by
  have := pcfLG2_hasDerivAt_mul_rpow (hasDerivAt_const t (1:ℝ)) (-1/4) (t := t)
  simp only [one_mul] at this
  unfold pcfLG2_PA pcfLG2_PA1
  convert this using 1
  rw [show (-1/4:ℝ) - 1 = -5/4 by norm_num]; ring

/-- `A'' = (3t²-2)/4 · (t²+1)^{-9/4}`. -/
lemma pcfLG2_hasDerivAt_PA1 (t : ℝ) : HasDerivAt pcfLG2_PA1 (pcfLG2_PA2 t) t := by
  have := pcfLG2_hasDerivAt_mul_rpow ((hasDerivAt_id' t).const_mul (-1/2:ℝ)) (-5/4) (t := t)
  unfold pcfLG2_PA1 pcfLG2_PA2
  convert this using 1
  · funext t; ring
  · rw [show (-5/4:ℝ) - 1 = -9/4 by norm_num]; ring

/-- `A > 0`. -/
lemma pcfLG2_PA_pos (t : ℝ) : 0 < pcfLG2_PA t := Real.rpow_pos_of_pos (by positivity) _

/-- `A⁻² = √(t²+1)`. -/
lemma pcfLG2_PA_sq_recip (t : ℝ) : (pcfLG2_PA t ^ 2)⁻¹ = Real.sqrt (t^2+1) := by
  have hy : 0 < t^2+1 := by positivity
  rw [pcfLG2_PA, ← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_neg hy.le,
    Real.sqrt_eq_rpow]
  norm_num

/-- `A⁻⁴ = t²+1`. -/
lemma pcfLG2_PA_pow_four_recip (t : ℝ) : (pcfLG2_PA t ^ 4)⁻¹ = t^2+1 := by
  have hy : 0 < t^2+1 := by positivity
  rw [pcfLG2_PA, ← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_neg hy.le]
  norm_num

/-- `ξ̄' = √(t²+1)` (DLMF 12.10.26). -/
lemma pcfLG2_hasDerivAt_xiBar (t : ℝ) : HasDerivAt pcfXiBar (Real.sqrt (t^2+1)) t := by
  have hy : 0 < t^2+1 := by positivity
  set r := Real.sqrt (t^2+1) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hy
  have hr2 : r^2 = t^2+1 := Real.sq_sqrt hy.le
  have h1 : HasDerivAt (fun t : ℝ => t^2+1) (2*t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const 1
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (t^2+1)) (2*t / (2 * r)) t := h1.sqrt hy.ne'
  have htr : 0 < t + r := by
    have : |t| < r := by
      rw [hr, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
    linarith [neg_abs_le t]
  have hl : HasDerivAt (fun t : ℝ => Real.log (t + Real.sqrt (t^2+1))) ((1 + 2*t/(2*r)) / (t + r)) t :=
    ((hasDerivAt_id t).add hs).log htr.ne'
  have := (((hasDerivAt_id t).mul hs).add hl).div_const 2
  have e : pcfXiBar = fun x => ((((id : ℝ → ℝ) * fun t : ℝ => Real.sqrt (t^2+1)) +
      fun t : ℝ => Real.log (t + Real.sqrt (t^2+1))) : ℝ → ℝ) x / 2 := by
    funext x; simp [pcfXiBar]
  rw [e]
  convert this using 1
  simp only [id]
  field_simp
  rw [← hr]
  nlinarith [hr2]

/-- Coefficient `Ā_s(t) = Q_s(t)/(t²+1)^{3s/2}`. -/
noncomputable def pcfLG2_Pa (s : ℕ) (t : ℝ) : ℝ := (pcfLG2_Q s).eval t * (t^2+1) ^ (-(3*s/2:ℝ))
/-- `Ā_s' = R_s(t)/(t²+1)^{(3s+2)/2}`. -/
noncomputable def pcfLG2_Pad (s : ℕ) (t : ℝ) : ℝ :=
  (pcfLG2_R s).eval t * (t^2+1) ^ (-((3*s+2)/2:ℝ))
/-- `Ā_s''`. -/
noncomputable def pcfLG2_Pad2 (s : ℕ) (t : ℝ) : ℝ :=
  ((pcfLG2_bar (s+1+3) (derivative (pcfOlverPair s).2)).eval t * (t^2+1) -
    (3*s+2)*t*(pcfLG2_R s).eval t) * (t^2+1) ^ (-((3*s+4)/2):ℝ)

/-- `Ā_s'`. -/
lemma pcfLG2_hasDerivAt_Pa (s : ℕ) (t : ℝ) : HasDerivAt (pcfLG2_Pa s) (pcfLG2_Pad s t) t := by
  have := pcfLG2_hasDerivAt_mul_rpow (pcfLG2_hasDerivAt_bar s (pcfOlverU s) t) (-(3*s/2))
  unfold pcfLG2_Pa pcfLG2_Pad
  refine this.congr_deriv ?_
  rw [← pcfLG2_QR_eq s t, show -(3*(s:ℝ)/2) - 1 = -((3*s+2)/2) by ring, pcfLG2_Q]; ring

/-- `Ā_s''`. -/
lemma pcfLG2_hasDerivAt_Pad (s : ℕ) (t : ℝ) : HasDerivAt (pcfLG2_Pad s) (pcfLG2_Pad2 s t) t := by
  have := pcfLG2_hasDerivAt_mul_rpow (pcfLG2_hasDerivAt_bar (s+1) (pcfOlverPair s).2 t)
    (-((3*s+2)/2))
  unfold pcfLG2_Pad pcfLG2_Pad2
  refine this.congr_deriv ?_
  rw [show -((3*(s:ℝ)+2)/2) - 1 = -((3*s+4)/2) by ring, pcfLG2_R]; ring

/-- Continuity of `Ā_s''`. -/
lemma pcfLG2_continuous_Pad2 (s : ℕ) : Continuous (pcfLG2_Pad2 s) := by
  unfold pcfLG2_Pad2
  refine Continuous.mul (by fun_prop) ?_
  exact Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity)

/-- **The Liouville–Green recursion for the barred coefficients** with `A = (t²+1)^{-1/4}`. -/
lemma pcfLG2_P_recursion (s : ℕ) (t : ℝ) :
    pcfLG2_PA t ^ 2 * pcfLG2_Pad2 s t + 2 * pcfLG2_PA t * pcfLG2_PA1 t * pcfLG2_Pad s t +
      pcfLG2_PA t * pcfLG2_PA2 t * pcfLG2_Pa s t = 2 * pcfLG2_Pad (s+1) t := by
  have hy : 0 < t^2+1 := by positivity
  set y := t^2+1
  set Z := y ^ (-((3*(s:ℝ)+5)/2))
  have e1 : pcfLG2_PA t ^ 2 * y ^ (-((3*(s:ℝ)+4)/2)) = Z := by
    rw [pcfLG2_PA, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    exact pcfLG_rpow_mul hy (by push_cast; ring)
  have e2 : pcfLG2_PA t * y ^ (-5/4:ℝ) * y ^ (-((3*(s:ℝ)+2)/2)) = Z := by
    rw [pcfLG2_PA, pcfLG_rpow_mul hy (c := -3/2) (by norm_num)]
    exact pcfLG_rpow_mul hy (by ring)
  have e3 : pcfLG2_PA t * y ^ (-9/4:ℝ) * y ^ (-(3*(s:ℝ)/2)) = Z := by
    rw [pcfLG2_PA, pcfLG_rpow_mul hy (c := -5/2) (by norm_num)]
    exact pcfLG_rpow_mul hy (by ring)
  have e4 : y ^ (-((3*((s+1:ℕ):ℝ)+2)/2)) = Z := by simp only [Z]; congr 1; push_cast; ring
  have hp := pcfLG2_R_succ s t
  simp only [pcfLG2_Pad2, pcfLG2_Pad, pcfLG2_Pa, pcfLG2_PA1, pcfLG2_PA2]
  rw [e4, hp]
  linear_combination
    ((pcfLG2_bar (s+1+3) (derivative (pcfOlverPair s).2)).eval t * y -
      (3*s+2)*t*(pcfLG2_R s).eval t) * e1 +
    (-t * (pcfLG2_R s).eval t) * e2 + ((3*t^2-2)/4 * (pcfLG2_Q s).eval t) * e3

/-- `|P(t)| ≤ (∑|coeff|)·(t²+1)^{d/2}` for `deg P ≤ d`. -/
lemma pcfLG2_abs_eval_le (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d) (t : ℝ) :
    |P.eval t| ≤ (∑ i ∈ Finset.range (d+1), |P.coeff i|) * (t^2+1) ^ ((d:ℝ)/2) := by
  have hy : 1 ≤ t^2+1 := by nlinarith [sq_nonneg t]
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hi : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 : |t| ≤ (t^2+1) ^ (1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  calc |t|^i ≤ ((t^2+1) ^ (1/2:ℝ))^i := pow_le_pow_left₀ (abs_nonneg _) h1 i
    _ = (t^2+1) ^ ((i:ℝ)/2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; ring_nf
    _ ≤ (t^2+1) ^ ((d:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le hy (by
        have : (i:ℝ) ≤ d := by exact_mod_cast hi
        linarith)

/-- `(t²+1)^{-3/2} ≤ (1+t²)⁻¹`. -/
lemma pcfLG2_rpow_le_recip (t : ℝ) : (t^2+1) ^ (-(3/2):ℝ) ≤ (1+t^2)⁻¹ := by
  have hy : 1 ≤ t^2+1 := by nlinarith [sq_nonneg t]
  calc (t^2+1) ^ (-(3/2):ℝ) ≤ (t^2+1) ^ (-1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
    _ = (1+t^2)⁻¹ := by rw [Real.rpow_neg_one, add_comm]

/-- Domination by `K (1+t²)⁻¹` gives integrability. -/
lemma pcfLG2_integrable_of_le {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ}
    (hK : ∀ t, |f t| ≤ K * (1 + t^2)⁻¹) : Integrable (fun t => |f t|) :=
  (integrable_inv_one_add_sq.const_mul K).mono' hf.abs.aestronglyMeasurable
    (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, abs_abs]; exact hK t)

/-- Domination by `K (1+t²)⁻¹` gives the tail bound `K π`. -/
lemma pcfLG2_tail_le {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ}
    (hK : ∀ t, |f t| ≤ K * (1 + t^2)⁻¹) (t : ℝ) : ∫ x in Ioi t, |f x| ≤ K * π := by
  refine (setIntegral_le_integral (pcfLG2_integrable_of_le hf hK)
    (Eventually.of_forall fun _ => abs_nonneg _)).trans ?_
  calc ∫ x, |f x| ≤ ∫ x, K * (1 + x^2)⁻¹ :=
        integral_mono (pcfLG2_integrable_of_le hf hK) (integrable_inv_one_add_sq.const_mul K) hK
    _ = K * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- Parity and degree of `Q_s`. -/
lemma pcfLG2_Q_good (s : ℕ) : pcfLG_good s (3*s) (pcfLG2_Q s) :=
  pcfLG2_bar_good (pcfLG_olverPair_inv s).1 s

/-- `|Ā_s(t)| ≤ K_s` on `ℝ`. -/
lemma pcfLG2_abs_Pa_le (s : ℕ) (t : ℝ) :
    |pcfLG2_Pa s t| ≤ ∑ i ∈ Finset.range (3*s+1), |(pcfLG2_Q s).coeff i| := by
  have hy : 0 < t^2+1 := by positivity
  have h := pcfLG2_abs_eval_le (pcfLG2_Q s) (pcfLG_good_natDegree (pcfLG2_Q_good s)) t
  rw [pcfLG2_Pa, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _)]
  have e : (t^2+1) ^ (((3*s:ℕ):ℝ)/2) * (t^2+1) ^ (-(3*s/2:ℝ)) = 1 := by
    rw [← Real.rpow_add hy]; push_cast; ring_nf; exact Real.rpow_zero _
  calc |(pcfLG2_Q s).eval t| * (t^2+1) ^ (-(3*s/2:ℝ))
      ≤ (∑ i ∈ Finset.range (3*s+1), |(pcfLG2_Q s).coeff i|) * (t^2+1) ^ (((3*s:ℕ):ℝ)/2) *
          (t^2+1) ^ (-(3*s/2:ℝ)) := by gcongr
    _ = _ := by rw [mul_assoc, e, mul_one]

/-- `|Ā_N'(t)| ≤ K (1+t²)⁻¹` on `ℝ`. -/
lemma pcfLG2_abs_Pad_le (N : ℕ) : ∃ K, ∀ t, |pcfLG2_Pad N t| ≤ K * (1 + t^2)⁻¹ := by
  rcases N with _ | m
  · refine ⟨0, fun t => ?_⟩
    simp [pcfLG2_Pad, pcfLG2_R, pcfLG2_bar, pcfOlverPair]
  · have hd : (pcfLG2_R (m+1)).natDegree ≤ 3*m+2 :=
      pcfLG2_natDegree_bar _ _ (pcfLG_natDegree_olverPair_snd m)
    refine ⟨∑ i ∈ Finset.range (3*m+2+1), |(pcfLG2_R (m+1)).coeff i|, fun t => ?_⟩
    have hy : 0 < t^2+1 := by positivity
    have h := pcfLG2_abs_eval_le (pcfLG2_R (m+1)) hd t
    rw [pcfLG2_Pad, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _)]
    have e : (t^2+1) ^ (((3*m+2:ℕ):ℝ)/2) * (t^2+1) ^ (-((3*((m+1:ℕ):ℝ)+2)/2)) =
        (t^2+1) ^ (-(3/2):ℝ) := by
      rw [← Real.rpow_add hy]; push_cast; ring_nf
    have hS : 0 ≤ ∑ i ∈ Finset.range (3*m+2+1), |(pcfLG2_R (m+1)).coeff i| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc |(pcfLG2_R (m+1)).eval t| * (t^2+1) ^ (-((3*((m+1:ℕ):ℝ)+2)/2))
        ≤ (∑ i ∈ Finset.range (3*m+2+1), |(pcfLG2_R (m+1)).coeff i|) *
            (t^2+1) ^ (((3*m+2:ℕ):ℝ)/2) * (t^2+1) ^ (-((3*((m+1:ℕ):ℝ)+2)/2)) := by gcongr
      _ = (∑ i ∈ Finset.range (3*m+2+1), |(pcfLG2_R (m+1)).coeff i|) * (t^2+1) ^ (-(3/2):ℝ) := by
          rw [mul_assoc, e]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pcfLG2_rpow_le_recip t) hS

/-- `A A'' = (3t²-2)/4 · (t²+1)^{-5/2}`. -/
lemma pcfLG2_PA_mul_PA2 (t : ℝ) :
    pcfLG2_PA t * pcfLG2_PA2 t = (3*t^2-2)/4 * (t^2+1) ^ (-(5/2):ℝ) := by
  have hy : 0 < t^2+1 := by positivity
  unfold pcfLG2_PA pcfLG2_PA2
  rw [mul_left_comm, pcfLG_rpow_mul hy (c := -(5/2)) (by norm_num)]

/-- The error-control integrand is dominated by `(3/4)(1+t²)⁻¹`. -/
lemma pcfLG2_abs_V_le (t : ℝ) :
    |pcfLG2_PA t * pcfLG2_PA2 t - (fun _ => (0:ℝ)) t * pcfLG2_PA t ^ 2| ≤ 3/4 * (1 + t^2)⁻¹ := by
  have hy : 0 < t^2+1 := by positivity
  simp only [zero_mul, sub_zero]
  rw [pcfLG2_PA_mul_PA2, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _)]
  have h1 : |(3*t^2-2)/4| ≤ 3/4 * (t^2+1) := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg t]
  have e : (t^2+1) * (t^2+1) ^ (-(5/2):ℝ) = (t^2+1) ^ (-(3/2):ℝ) := by
    conv_lhs => arg 1; rw [← Real.rpow_one (t^2+1)]
    rw [← Real.rpow_add hy]; norm_num
  calc |(3*t^2-2)/4| * (t^2+1) ^ (-(5/2):ℝ) ≤ 3/4 * (t^2+1) * (t^2+1) ^ (-(5/2):ℝ) := by
        gcongr
    _ = 3/4 * (t^2+1) ^ (-(3/2):ℝ) := by rw [mul_assoc, e]
    _ ≤ _ := by gcongr; exact pcfLG2_rpow_le_recip t

/-- Continuity of the error-control integrand. -/
lemma pcfLG2_continuous_V :
    Continuous (fun t => pcfLG2_PA t * pcfLG2_PA2 t - (fun _ => (0:ℝ)) t * pcfLG2_PA t ^ 2) := by
  have h1 : Continuous pcfLG2_PA := continuous_iff_continuousAt.2 fun t =>
    (pcfLG2_hasDerivAt_PA t).continuousAt
  have h2 : Continuous pcfLG2_PA2 := by
    unfold pcfLG2_PA2
    exact Continuous.mul (by fun_prop)
      (Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity))
  exact (h1.mul h2).sub (continuous_const.mul (h1.pow 2))

/-- `A(t) → 0` as `t → ∞`. -/
lemma pcfLG2_tendsto_PA : Tendsto pcfLG2_PA atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => t^2+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
  have := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/4)).comp h
  refine this.congr fun t => ?_
  simp only [Function.comp, pcfLG2_PA]; norm_num

/-- `t²/(t²+1) → 1`. -/
lemma pcfLG2_tendsto_sq_div : Tendsto (fun t : ℝ => t^2/(t^2+1)) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => 1/(1 + (t^2)⁻¹)) atTop (𝓝 (1/(1+0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add
      ((tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop)) (by norm_num)
  rw [show (1:ℝ)/(1+0) = 1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have : t^2 ≠ 0 := by positivity
  field_simp

/-- `Ā_s(t) → c̄_s` as `t → ∞`. -/
lemma pcfLG2_tendsto_Pa (s : ℕ) :
    Tendsto (pcfLG2_Pa s) atTop (𝓝 ((pcfLG2_Q s).coeff (3*s))) := by
  have h1 := pcfLG_tendsto_eval_div_pow (pcfLG2_Q s) (pcfLG_good_natDegree (pcfLG2_Q_good s))
  have h2 : Tendsto (fun t : ℝ => (t^2/(t^2+1)) ^ (3*s/2:ℝ)) atTop (𝓝 1) := by
    have := pcfLG2_tendsto_sq_div.rpow_const (p := 3*s/2) (Or.inl one_ne_zero)
    simpa using this
  have := h1.mul h2
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht0
  have hy : 0 < t^2+1 := by positivity
  rw [pcfLG2_Pa, Real.div_rpow (by positivity) hy.le, Real.rpow_neg hy.le,
    show (t^2) ^ (3*(s:ℝ)/2) = t ^ (3*s) by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le, ← Real.rpow_natCast]; push_cast; ring_nf]
  have : t ^ (3*s) ≠ 0 := by positivity
  field_simp

/-- Parity of `Ā_s`. -/
lemma pcfLG2_Pa_neg (s : ℕ) (t : ℝ) : pcfLG2_Pa s (-t) = (-1)^s * pcfLG2_Pa s t := by
  rw [pcfLG2_Pa, pcfLG2_Pa, pcfLG2_eval_neg (pcfLG2_Q_good s), neg_sq]; ring

/-- `Ā_s(t) → (-1)^s c̄_s` as `t → -∞`. -/
lemma pcfLG2_tendsto_Pa_atBot (s : ℕ) :
    Tendsto (pcfLG2_Pa s) atBot (𝓝 ((-1)^s * (pcfLG2_Q s).coeff (3*s))) := by
  have := ((pcfLG2_tendsto_Pa s).const_mul ((-1:ℝ)^s)).comp tendsto_neg_atBot_atTop
  refine this.congr fun t => ?_
  simp only [Function.comp, pcfLG2_Pa_neg]
  rw [← mul_assoc, ← mul_pow]; norm_num

/-- `c̄_s = (-1)^s c_s`. -/
lemma pcfLG2_Q_coeff (s : ℕ) : (pcfLG2_Q s).coeff (3*s) = (-1)^s * pcfLG_c s := by
  rw [pcfLG2_Q, pcfLG2_bar_coeff, pcfLG_c, pcfOlverU]
  have : I^s * (-I)^(3*s) = (((-1)^s : ℝ) : ℂ) := by
    have h3 : (-I)^3 = I := by rw [show (-I)^3 = -(I^2*I) by ring, I_sq]; ring
    rw [pow_mul, h3, ← mul_pow, I_mul_I]
    push_cast; ring
  rw [this, Complex.ofReal_re]; ring

/-- `U(μ²/2, μt√2)` as a function of `t`: first derivative. -/
lemma pcfLG2_hasDerivAt_PU (μ t : ℝ) :
    HasDerivAt (fun t : ℝ => pcfU (μ^2/2) (μ*t*Real.sqrt 2))
      ((μ:ℂ) * Real.sqrt 2 * pcfUDeriv (μ^2/2) (μ*t*Real.sqrt 2)) t := by
  have h1 : HasDerivAt (fun w : ℂ => (μ:ℂ) * w * Real.sqrt 2) ((μ:ℂ) * Real.sqrt 2) (t:ℂ) := by
    simpa using ((hasDerivAt_id (t:ℂ)).const_mul (μ:ℂ)).mul_const ((Real.sqrt 2 : ℝ) : ℂ)
  have := ((hasDerivAt_pcfU ((μ:ℂ)^2/2) ((μ:ℂ) * t * Real.sqrt 2)).comp (t:ℂ) h1).comp_ofReal
  exact this.congr_deriv (by ring)

/-- `U(μ²/2, μt√2)` as a function of `t`: Weber's equation `w'' = μ⁴(t²+1) w`. -/
lemma pcfLG2_hasDerivAt_PU' (μ t : ℝ) :
    HasDerivAt (fun t : ℝ => (μ:ℂ) * Real.sqrt 2 * pcfUDeriv (μ^2/2) (μ*t*Real.sqrt 2))
      (((μ^4*(t^2+1) : ℝ) : ℂ) * pcfU (μ^2/2) (μ*t*Real.sqrt 2)) t := by
  have h1 : HasDerivAt (fun w : ℂ => (μ:ℂ) * w * Real.sqrt 2) ((μ:ℂ) * Real.sqrt 2) (t:ℂ) := by
    simpa using ((hasDerivAt_id (t:ℂ)).const_mul (μ:ℂ)).mul_const ((Real.sqrt 2 : ℝ) : ℂ)
  have := (((hasDerivAt_pcfUDeriv ((μ:ℂ)^2/2) ((μ:ℂ) * t * Real.sqrt 2)).comp (t:ℂ)
    h1).comp_ofReal).const_mul ((μ:ℂ) * Real.sqrt 2)
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  refine this.congr_deriv ?_
  push_cast
  linear_combination (((μ:ℂ)^4*(t:ℂ)^2/4) * (((Real.sqrt 2 : ℝ) : ℂ)^2 + 2) + (μ:ℂ)^4/2) *
    pcfU ((μ:ℂ)^2/2) ((μ:ℂ) * t * Real.sqrt 2) * hs2

/-- `√(t²+1)/t → 1`. -/
lemma pcfLG2_tendsto_sqrt_div : Tendsto (fun t : ℝ => Real.sqrt (t^2+1) / t) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => Real.sqrt (1 + (t^2)⁻¹)) atTop (𝓝 (Real.sqrt (1 + 0))) :=
    (tendsto_const_nhds.add ((tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop)).sqrt
  rw [add_zero, Real.sqrt_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht0
  rw [show 1 + (t^2)⁻¹ = (t^2+1)/t^2 by field_simp, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq ht0.le]

/-- `(t²+1)/t² → 1`. -/
lemma pcfLG2_tendsto_sq_div' : Tendsto (fun t : ℝ => (t^2+1)/t^2) atTop (𝓝 1) := by
  have := pcfLG2_tendsto_sq_div.inv₀ one_ne_zero
  rw [inv_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp

/-- **The normalization at `+∞` for positive parameter**: with `z = μ t √2`, `a = μ²/2`,
`e^{z²/4} z^{a+1/2} A(t) e^{-μ²ξ̄(t)} → μ√2 h(μ)` as `t → ∞`. -/
lemma pcfLG2_tendsto_PR {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => Real.exp ((μ*t*Real.sqrt 2)^2/4) * (μ*t*Real.sqrt 2) ^ (1/2+μ^2/2) *
      pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t))) atTop
      (𝓝 (μ * Real.sqrt 2 * pcfLG_h μ)) := by
  set p : ℝ := 1/2+μ^2/2
  set C₀ : ℝ := p * Real.log μ + p/2 * Real.log 2
  set r : ℝ → ℝ := fun t => Real.sqrt (t^2+1)
  set E : ℝ → ℝ := fun t => C₀ - 1/4 * Real.log ((t^2+1)/t^2) - μ^2/2 * (1 / (1 + r t / t)) -
    μ^2/2 * Real.log (1 + r t / t)
  have hlim : Tendsto E atTop (𝓝 (C₀ - 1/4 * Real.log 1 - μ^2/2 * (1/(1+1)) -
      μ^2/2 * Real.log (1+1))) := by
    have hq := pcfLG2_tendsto_sqrt_div
    exact ((tendsto_const_nhds.sub (tendsto_const_nhds.mul
      (pcfLG2_tendsto_sq_div'.log one_ne_zero))).sub (tendsto_const_nhds.mul
      (tendsto_const_nhds.div (tendsto_const_nhds.add hq) (by norm_num)))).sub
      (tendsto_const_nhds.mul ((tendsto_const_nhds.add hq).log (by norm_num)))
  have hval : C₀ - 1/4 * Real.log 1 - μ^2/2 * (1/(1+1)) - μ^2/2 * Real.log (1+1) =
      Real.log (μ * Real.sqrt 2 * pcfLG_h μ) := by
    rw [pcfLG_h, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow hμ, Real.log_exp, Real.log_sqrt (by norm_num)]
    simp only [C₀, p]; norm_num; ring
  rw [hval] at hlim
  have := (Real.continuous_exp.tendsto _).comp hlim
  rw [Real.exp_log (by have := pcfLG_h_pos hμ; positivity)] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht0
  have hy : 0 < t^2+1 := by positivity
  have hr0 : 0 < r t := Real.sqrt_pos.2 hy
  have hr2 : r t ^ 2 = t^2+1 := Real.sq_sqrt hy.le
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : 0 < μ*t*Real.sqrt 2 := by positivity
  simp only [Function.comp, pcfLG2_PA]
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hy, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  simp only [E, C₀, pcfXiBar]
  have e1 : 1 / (1 + r t / t) = t * r t - t^2 := by
    have : r t + t ≠ 0 := by positivity
    field_simp
    nlinarith [hr2]
  have e2 : Real.log (1 + r t / t) = Real.log (t + r t) - Real.log t := by
    rw [show 1 + r t / t = (t + r t)/t by field_simp, Real.log_div (by positivity) ht0.ne']
  have e3 : Real.log ((t^2+1)/t^2) = Real.log (t^2+1) - 2 * Real.log t := by
    rw [Real.log_div hy.ne' (by positivity), Real.log_pow]; push_cast; ring
  have e4 : Real.log (μ*t*Real.sqrt 2) = Real.log μ + Real.log t + 1/2 * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hμ.ne' ht0.ne',
      Real.log_sqrt (by norm_num)]; ring
  rw [e1, e2, e3, e4]
  have : (μ*t*Real.sqrt 2)^2 = 2*μ^2*t^2 := by rw [mul_pow, mul_pow, hs2]; ring
  rw [this]
  simp only [r]
  ring

/-- **The normalization of `U` at `+∞` for positive parameter** (from DLMF 12.9.1):
`U(μ²/2, μ t √2) / (A(t) e^{-μ² ξ̄(t)}) → 1/(μ√2 h(μ))` as `t → ∞`. -/
lemma pcfLG2_tendsto_PU_div {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => pcfU (μ^2/2) (μ*t*Real.sqrt 2) /
      ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ)) atTop
      (𝓝 (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ)) := by
  set a : ℂ := (μ:ℂ)^2/2
  have hO := pcfU_sector_asymptotic a (δ := π/4) (by positivity) (by linarith [Real.pi_pos]) 1
  have hz2 : Tendsto (fun z : ℂ => z ^ (-(2*(1:ℕ):ℤ))) (sector (3*π/4-π/4)) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => ‖z‖) (sector (3*π/4-π/4)) atTop :=
      tendsto_comap.mono_left inf_le_left
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    have h2 := (tendsto_pow_atTop (two_ne_zero)).comp this |>.inv_tendsto_atTop
    refine h2.congr fun z => ?_
    simp
  have hE := (hO.trans_tendsto hz2).add_const 1
  simp only [zero_add, Finset.sum_range_one] at hE
  have hE' : Tendsto (fun z : ℂ => cexp (z^2/4) * z^(a+1/2) * pcfU a z) (sector (3*π/4-π/4))
      (𝓝 1) := by
    refine hE.congr fun z => ?_
    simp [pcfUTerm, poch_zero]
  have hT := hE'.comp (pcfLG_tendsto_sector (α := 3*π/4-π/4) (by linarith [Real.pi_pos]) hμ)
  have hR := (Complex.continuous_ofReal.tendsto _).comp (pcfLG2_tendsto_PR hμ)
  have hRne : (μ * Real.sqrt 2 * pcfLG_h μ : ℝ) ≠ 0 := by
    have := pcfLG_h_pos hμ; positivity
  have := hT.div hR (by exact_mod_cast hRne)
  rw [show (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) =
    1 / ((μ * Real.sqrt 2 * pcfLG_h μ : ℝ) : ℂ) by push_cast; field_simp]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hx : 0 < μ*t*Real.sqrt 2 := by positivity
  have hcp : ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(a+1/2) = (((μ*t*Real.sqrt 2)^(1/2+μ^2/2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx.le]; congr 1; simp only [a]; push_cast; ring
  have hp : 0 < (μ*t*Real.sqrt 2)^(1/2+μ^2/2) := Real.rpow_pos_of_pos hx _
  have hA : 0 < pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) :=
    mul_pos (pcfLG2_PA_pos t) (Real.exp_pos _)
  have hden : ((Real.exp ((μ*t*Real.sqrt 2)^2/4) * (μ*t*Real.sqrt 2)^(1/2+μ^2/2) * pcfLG2_PA t *
      Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) = cexp (((μ*t*Real.sqrt 2 : ℝ) : ℂ)^2/4) *
      ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(a+1/2) *
      ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) := by
    rw [hcp]; push_cast; ring
  have hp' : ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(a+1/2) ≠ 0 := by rw [hcp]; exact_mod_cast hp.ne'
  have hA' : ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hA.ne'
  have he : cexp (((μ*t*Real.sqrt 2 : ℝ) : ℂ)^2/4) ≠ 0 := Complex.exp_ne_zero _
  simp only [Function.comp, Pi.div_apply]
  rw [hden, mul_div_mul_left _ _ (mul_ne_zero he hp')]
  push_cast; ring

/-- `ξ̄` is odd. -/
lemma pcfLG2_xiBar_neg (s : ℝ) : pcfXiBar (-s) = -pcfXiBar s := by
  have hy : 0 < s^2+1 := by positivity
  set r := Real.sqrt (s^2+1) with hr
  have hr2 : r^2 = s^2+1 := Real.sq_sqrt hy.le
  have h1 : |s| < r := by
    rw [hr, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have hp : 0 < s + r := by linarith [neg_abs_le s]
  have hm : 0 < -s + r := by linarith [le_abs_self s]
  have e : -s + r = (s + r)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by nlinarith [hr2])
  unfold pcfXiBar
  rw [neg_sq, ← hr, e, Real.log_inv]; ring

/-- `A` is even. -/
lemma pcfLG2_PA_neg (s : ℝ) : pcfLG2_PA (-s) = pcfLG2_PA s := by simp [pcfLG2_PA]

/-- `ξ̄(t) → ∞`. -/
lemma pcfLG2_tendsto_xiBar : Tendsto pcfXiBar atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ ((tendsto_pow_atTop two_ne_zero).atTop_div_const
    (by norm_num : (0:ℝ) < 2))
  filter_upwards [eventually_ge_atTop 0] with s hs
  have hy : 0 < s^2+1 := by positivity
  have h1 : s ≤ Real.sqrt (s^2+1) := by
    have := Real.sqrt_le_sqrt (show s^2 ≤ s^2+1 by linarith); rwa [Real.sqrt_sq hs] at this
  have h2 : 0 ≤ Real.log (s + Real.sqrt (s^2+1)) := by
    apply Real.log_nonneg
    have : 1 ≤ Real.sqrt (s^2+1) := by
      have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ s^2+1 by nlinarith); rwa [Real.sqrt_one] at this
    linarith
  unfold pcfXiBar
  nlinarith

/-- With `z = μ s √2`, `a = μ²/2`: `e^{-z²/4} z^{1/2-a} A(s) e^{μ²ξ̄(s)} → 1/h(μ)` as `s → ∞`. -/
lemma pcfLG2_tendsto_PRV {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => Real.exp (-((μ*t*Real.sqrt 2)^2/4)) * (μ*t*Real.sqrt 2) ^ (1/2-μ^2/2) *
      pcfLG2_PA t * Real.exp (μ^2 * pcfXiBar t)) atTop (𝓝 (pcfLG_h μ)⁻¹) := by
  set p : ℝ := 1/2-μ^2/2
  set C₀ : ℝ := p * Real.log μ + p/2 * Real.log 2
  set r : ℝ → ℝ := fun t => Real.sqrt (t^2+1)
  set E : ℝ → ℝ := fun t => C₀ - 1/4 * Real.log ((t^2+1)/t^2) + μ^2/2 * (1 / (1 + r t / t)) +
    μ^2/2 * Real.log (1 + r t / t)
  have hlim : Tendsto E atTop (𝓝 (C₀ - 1/4 * Real.log 1 + μ^2/2 * (1/(1+1)) +
      μ^2/2 * Real.log (1+1))) := by
    have hq := pcfLG2_tendsto_sqrt_div
    exact ((tendsto_const_nhds.sub (tendsto_const_nhds.mul
      (pcfLG2_tendsto_sq_div'.log one_ne_zero))).add (tendsto_const_nhds.mul
      (tendsto_const_nhds.div (tendsto_const_nhds.add hq) (by norm_num)))).add
      (tendsto_const_nhds.mul ((tendsto_const_nhds.add hq).log (by norm_num)))
  have hval : C₀ - 1/4 * Real.log 1 + μ^2/2 * (1/(1+1)) + μ^2/2 * Real.log (1+1) =
      Real.log (pcfLG_h μ)⁻¹ := by
    rw [Real.log_inv, pcfLG_h, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow hμ, Real.log_exp]
    simp only [C₀, p]; norm_num; ring
  rw [hval] at hlim
  have := (Real.continuous_exp.tendsto _).comp hlim
  rw [Real.exp_log (inv_pos.2 (pcfLG_h_pos hμ))] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht0
  have hy : 0 < t^2+1 := by positivity
  have hr0 : 0 < r t := Real.sqrt_pos.2 hy
  have hr2 : r t ^ 2 = t^2+1 := Real.sq_sqrt hy.le
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : 0 < μ*t*Real.sqrt 2 := by positivity
  simp only [Function.comp, pcfLG2_PA]
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hy, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  simp only [E, C₀, pcfXiBar]
  have e1 : 1 / (1 + r t / t) = t * r t - t^2 := by
    have : r t + t ≠ 0 := by positivity
    field_simp
    nlinarith [hr2]
  have e2 : Real.log (1 + r t / t) = Real.log (t + r t) - Real.log t := by
    rw [show 1 + r t / t = (t + r t)/t by field_simp, Real.log_div (by positivity) ht0.ne']
  have e3 : Real.log ((t^2+1)/t^2) = Real.log (t^2+1) - 2 * Real.log t := by
    rw [Real.log_div hy.ne' (by positivity), Real.log_pow]; push_cast; ring
  have e4 : Real.log (μ*t*Real.sqrt 2) = Real.log μ + Real.log t + 1/2 * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hμ.ne' ht0.ne',
      Real.log_sqrt (by norm_num)]; ring
  rw [e1, e2, e3, e4]
  have : (μ*t*Real.sqrt 2)^2 = 2*μ^2*t^2 := by rw [mul_pow, mul_pow, hs2]; ring
  rw [this]
  simp only [r]
  ring

/-- `V(μ²/2, μ s √2) / (A(s) e^{μ²ξ̄(s)}) → h(μ)/√(π/2)` as `s → ∞` (from DLMF 12.9.2). -/
lemma pcfLG2_tendsto_PV_div {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => pcfV (μ^2/2) (μ*t*Real.sqrt 2) /
      ((pcfLG2_PA t * Real.exp (μ^2 * pcfXiBar t)) : ℝ)) atTop
      (𝓝 ((pcfLG_h μ / Real.sqrt (π/2) : ℝ) : ℂ)) := by
  set a : ℂ := (μ:ℂ)^2/2
  have hO := pcfV_sector_asymptotic a (δ := π/8) (by positivity) (by linarith [Real.pi_pos]) 1
  have hz2 : Tendsto (fun z : ℂ => z ^ (-(2*(1:ℕ):ℤ))) (sector (π/4-π/8)) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => ‖z‖) (sector (π/4-π/8)) atTop :=
      tendsto_comap.mono_left inf_le_left
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    have h2 := (tendsto_pow_atTop (two_ne_zero)).comp this |>.inv_tendsto_atTop
    refine h2.congr fun z => ?_
    simp
  have hE := (hO.trans_tendsto hz2).add_const 1
  simp only [zero_add, Finset.sum_range_one] at hE
  have hE' : Tendsto (fun z : ℂ => (Real.sqrt (π/2):ℂ) * cexp (-z^2/4) * z^(-a+1/2) * pcfV a z)
      (sector (π/4-π/8)) (𝓝 1) := by
    refine hE.congr fun z => ?_
    simp [pcfVTerm, poch_zero]
  have hT := hE'.comp (pcfLG_tendsto_sector (α := π/4-π/8) (by linarith [Real.pi_pos]) hμ)
  have hR := (Complex.continuous_ofReal.tendsto _).comp
    ((pcfLG2_tendsto_PRV hμ).const_mul (Real.sqrt (π/2)))
  have hs : 0 < Real.sqrt (π/2) := Real.sqrt_pos.2 (by positivity)
  have hRne : (Real.sqrt (π/2) * (pcfLG_h μ)⁻¹ : ℝ) ≠ 0 := by
    have := pcfLG_h_pos hμ; positivity
  have := hT.div hR (by exact_mod_cast hRne)
  rw [show ((pcfLG_h μ / Real.sqrt (π/2) : ℝ) : ℂ) =
    1 / ((Real.sqrt (π/2) * (pcfLG_h μ)⁻¹ : ℝ) : ℂ) by
      have := (pcfLG_h_pos hμ).ne'
      push_cast; field_simp]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hx : 0 < μ*t*Real.sqrt 2 := by positivity
  have hcp : ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(-a+1/2) = (((μ*t*Real.sqrt 2)^(1/2-μ^2/2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx.le]; congr 1; simp only [a]; push_cast; ring
  have hp : 0 < (μ*t*Real.sqrt 2)^(1/2-μ^2/2) := Real.rpow_pos_of_pos hx _
  have hA : 0 < pcfLG2_PA t * Real.exp (μ^2 * pcfXiBar t) :=
    mul_pos (pcfLG2_PA_pos t) (Real.exp_pos _)
  have hden : ((Real.sqrt (π/2) * (Real.exp (-((μ*t*Real.sqrt 2)^2/4)) *
      (μ*t*Real.sqrt 2)^(1/2-μ^2/2) * pcfLG2_PA t * Real.exp (μ^2 * pcfXiBar t)) : ℝ) : ℂ) =
      (Real.sqrt (π/2):ℂ) * cexp (-((μ*t*Real.sqrt 2 : ℝ) : ℂ)^2/4) *
      ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(-a+1/2) *
      ((pcfLG2_PA t * Real.exp (μ^2 * pcfXiBar t) : ℝ) : ℂ) := by
    rw [hcp]; push_cast; ring_nf
  have hp' : ((μ*t*Real.sqrt 2 : ℝ):ℂ)^(-a+1/2) ≠ 0 := by rw [hcp]; exact_mod_cast hp.ne'
  have he : cexp (-((μ*t*Real.sqrt 2 : ℝ) : ℂ)^2/4) ≠ 0 := Complex.exp_ne_zero _
  have hs' : (Real.sqrt (π/2):ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [Function.comp, Pi.div_apply]
  rw [hden, mul_div_mul_left _ _ (mul_ne_zero (mul_ne_zero hs' he) hp')]
  push_cast; ring

/-- **The behaviour of `U(μ²/2, μt√2)` at `-∞`** (from DLMF 12.2.15 and 12.9.1–12.9.2):
`U / (A e^{-μ²ξ̄}) → √(2π) h(μ)/Γ(1/2+μ²/2)` as `t → -∞`. -/
lemma pcfLG2_tendsto_PU_div_atBot {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun t : ℝ => pcfU (μ^2/2) (μ*t*Real.sqrt 2) /
      ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) : ℝ) : ℂ)) atBot
      (𝓝 (((Real.sqrt (2*π) * pcfLG_h μ : ℝ) : ℂ) / Gamma (1/2 + (μ:ℂ)^2/2))) := by
  set a : ℂ := (μ:ℂ)^2/2 with ha
  have hU := pcfLG2_tendsto_PU_div hμ
  have hV := pcfLG2_tendsto_PV_div hμ
  have he : Tendsto (fun s => ((Real.exp (-(2*μ^2 * pcfXiBar s)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s => -(2*μ^2 * pcfXiBar s)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (pcfLG2_tendsto_xiBar.const_mul_atTop (by positivity))
    have h2 := (Real.tendsto_exp_atBot.comp h1).ofReal
    rw [Complex.ofReal_zero] at h2
    exact h2
  have hsum := ((hU.mul he).const_mul (-Complex.sin (π*a))).add (hV.const_mul (π / Gamma (1/2+a)))
  have hval : -Complex.sin (π*a) * ((((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) * 0) +
      π / Gamma (1/2+a) * ((pcfLG_h μ / Real.sqrt (π/2) : ℝ) : ℂ) =
      ((Real.sqrt (2*π) * pcfLG_h μ : ℝ) : ℂ) / Gamma (1/2 + (μ:ℂ)^2/2) := by
    have hs : Real.sqrt (π/2) * Real.sqrt (2*π) = π := by
      rw [← Real.sqrt_mul (by positivity), show π/2*(2*π) = π^2 by ring,
        Real.sqrt_sq Real.pi_pos.le]
    have hs0 : Real.sqrt (π/2) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    have hs' : (Real.sqrt (π/2) : ℂ) * (Real.sqrt (2*π) : ℂ) = (π : ℂ) := by exact_mod_cast hs
    have hs0' : (Real.sqrt (π/2) : ℂ) ≠ 0 := by exact_mod_cast hs0
    rw [mul_zero, mul_zero, zero_add, ← hs', ha]
    push_cast
    field_simp
  rw [hval] at hsum
  have key : Tendsto (fun s : ℝ => pcfU a (-((μ*s*Real.sqrt 2 : ℝ) : ℂ)) /
      ((pcfLG2_PA s * Real.exp (μ^2 * pcfXiBar s) : ℝ) : ℂ)) atTop
      (𝓝 (((Real.sqrt (2*π) * pcfLG_h μ : ℝ) : ℂ) / Gamma (1/2 + (μ:ℂ)^2/2))) := by
    refine hsum.congr' (Eventually.of_forall fun s => ?_)
    have hA1 : ((pcfLG2_PA s * Real.exp (μ^2 * pcfXiBar s) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (pcfLG2_PA_pos s) (Real.exp_pos _)).ne'
    have hA2 : ((pcfLG2_PA s * Real.exp (-(μ^2 * pcfXiBar s)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (pcfLG2_PA_pos s) (Real.exp_pos _)).ne'
    beta_reduce
    rw [pcfU_neg_eq]
    have hx : ((μ*s*Real.sqrt 2 : ℝ) : ℂ) = (μ:ℂ) * s * Real.sqrt 2 := by push_cast; ring
    rw [hx]
    have hexp : Real.exp (-(2*μ^2 * pcfXiBar s)) =
        Real.exp (-(μ^2 * pcfXiBar s)) / Real.exp (μ^2 * pcfXiBar s) := by
      rw [← Real.exp_sub]; ring_nf
    rw [hexp]
    have h1 : (Real.exp (μ^2 * pcfXiBar s) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    have h2 : (Real.exp (-(μ^2 * pcfXiBar s)) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    have h3 : (pcfLG2_PA s : ℂ) ≠ 0 := by exact_mod_cast (pcfLG2_PA_pos s).ne'
    push_cast
    field_simp
    ring
  refine (key.comp tendsto_neg_atBot_atTop).congr fun t => ?_
  simp only [Function.comp, pcfLG2_PA_neg, pcfLG2_xiBar_neg]
  have : -(((μ*(-t)*Real.sqrt 2 : ℝ)) : ℂ) = (μ:ℂ) * t * Real.sqrt 2 := by push_cast; ring
  rw [this, ha]
  congr 2
  ring_nf

/-- The limits `c̄_s` of the barred coefficients at `+∞`. -/
noncomputable def pcfLG2_cbar (s : ℕ) : ℝ := (pcfLG2_Q s).coeff (3*s)

/-- **Whole-line Liouville–Green core for positive parameter**: for `μ ≥ μ₀` and every real `t`,
`U(μ²/2, μt√2) = H₊/L₊ · A e^{-μ²ξ̄}(S + e)` with `|e| ≤ C μ^{-2N}`, and the corresponding
formula for the derivative. -/
lemma pcfLG2_pos_core {N : ℕ} (hN : 1 ≤ N) : ∃ C μ₀ : ℝ, 0 ≤ C ∧ 1 ≤ μ₀ ∧ ∀ μ, μ₀ ≤ μ →
    |pcfLG2_ser (fun s _ => pcfLG2_cbar s) N (μ^2) 0 - 1| ≤ 1/2 ∧ ∀ t : ℝ,
      |pcfLG2_ser pcfLG2_Pa N (μ^2) t - 1| ≤ 1/2 ∧ ∃ e e' : ℝ,
      |e| ≤ C / (μ^2)^N ∧ |pcfLG2_PA t ^ 2 * e'| ≤ 2 * C / (μ^2)^(N-1) ∧
      pcfU (μ^2/2) (μ*t*Real.sqrt 2) = (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) /
        (pcfLG2_ser (fun s _ => pcfLG2_cbar s) N (μ^2) 0 : ℂ) *
        ((pcfLG2_PA t * Real.exp (-(μ^2 * pcfXiBar t)) * (pcfLG2_ser pcfLG2_Pa N (μ^2) t + e) : ℝ) : ℂ) ∧
      (μ:ℂ) * Real.sqrt 2 * pcfUDeriv (μ^2/2) (μ*t*Real.sqrt 2) =
        (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ) /
        (pcfLG2_ser (fun s _ => pcfLG2_cbar s) N (μ^2) 0 : ℂ) *
        ((Real.exp (-(μ^2 * pcfXiBar t)) * ((pcfLG2_PA1 t - μ^2 * (pcfLG2_PA t)⁻¹) *
          (pcfLG2_ser pcfLG2_Pa N (μ^2) t + e) +
          pcfLG2_PA t * (pcfLG2_ser pcfLG2_Pad N (μ^2) t + e')) : ℝ) : ℂ) := by
  set K : ℕ → ℝ := fun s => ∑ i ∈ Finset.range (3*s+1), |(pcfLG2_Q s).coeff i|
  have hK0 : ∀ s, 0 ≤ K s := fun s => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨Kd, hKd⟩ := pcfLG2_abs_Pad_le N
  have hcPad : Continuous (pcfLG2_Pad N) := continuous_iff_continuousAt.2 fun t =>
    (pcfLG2_hasDerivAt_Pa N t).continuousAt |> fun _ => (pcfLG2_hasDerivAt_Pad N t).continuousAt
  set I := Kd * π
  set V0 := 3/4 * π
  set C := I * Real.exp (V0/2) with hCdef
  set KS := ∑ s ∈ Finset.range N, K s
  have hKS : 0 ≤ KS := Finset.sum_nonneg fun s _ => hK0 s
  have hKd0 : 0 ≤ Kd := by
    have := (abs_nonneg _).trans (hKd 0)
    have h1 : 0 < (1 + (0:ℝ)^2)⁻¹ := by norm_num
    nlinarith
  have hC0 : 0 ≤ C := by positivity
  set μ₀ := max 1 (2*(KS+C)+1)
  have hμ₀ : 1 ≤ μ₀ := le_max_left _ _
  have hμ₀C : 2*((∑ s ∈ Finset.range N, K s) + C) ≤ μ₀^2 := by
    have := le_max_right 1 (2*(KS+C)+1); nlinarith
  refine ⟨C, μ₀, hC0, hμ₀, fun μ hμ => ?_⟩
  have hμ0 : 0 < μ := by linarith
  have hcore : ∀ b : ℝ, _ := fun b => pcfLG2_core (b := b) (A := pcfLG2_PA) (A1 := pcfLG2_PA1)
    (A2 := pcfLG2_PA2) (ξ := pcfXiBar) (fun t _ => pcfLG2_PA_pos t)
    (fun t _ => pcfLG2_hasDerivAt_PA t) (fun t _ => pcfLG2_hasDerivAt_PA1 t)
    (continuous_iff_continuousAt.2 fun t => (pcfLG2_hasDerivAt_PA1 t).continuousAt |>
      fun _ => by
        unfold pcfLG2_PA2
        exact (Continuous.mul (by fun_prop)
          (Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity))).continuousAt).continuousOn
    (fun t _ => by rw [pcfLG2_PA_sq_recip]; exact pcfLG2_hasDerivAt_xiBar t)
    (fun c _ => (pcfLG2_integrable_of_le pcfLG2_continuous_V pcfLG2_abs_V_le).integrableOn)
    (fun t _ => pcfLG2_tail_le pcfLG2_continuous_V pcfLG2_abs_V_le t)
    pcfLG2_tendsto_PA hN (a := pcfLG2_Pa) (ad := pcfLG2_Pad) (ad2 := pcfLG2_Pad2)
    (l := pcfLG2_cbar)
    (fun s _ t _ => pcfLG2_hasDerivAt_Pa s t)
    (fun s _ t _ => pcfLG2_hasDerivAt_Pad s t)
    (fun s _ => (pcfLG2_continuous_Pad2 s).continuousOn)
    (fun t => by simp [pcfLG2_Pa, pcfLG2_Q, pcfLG2_bar, pcfOlverU, pcfOlverPair])
    (fun t _ => by simp [pcfLG2_Pad, pcfLG2_R, pcfLG2_bar, pcfOlverPair])
    (fun s _ t _ => pcfLG2_P_recursion s t)
    (fun c _ => (pcfLG2_integrable_of_le hcPad hKd).integrableOn)
    (fun t _ => pcfLG2_tail_le hcPad hKd t) (K := K)
    (fun s _ t _ => pcfLG2_abs_Pa_le s t)
    (fun s _ => pcfLG2_tendsto_Pa s)
    (U := fun μ t => pcfU (μ^2/2) (μ*t*Real.sqrt 2))
    (U' := fun μ t => (μ:ℂ) * Real.sqrt 2 * pcfUDeriv (μ^2/2) (μ*t*Real.sqrt 2))
    (H := fun μ => (((μ * Real.sqrt 2 * pcfLG_h μ)⁻¹ : ℝ) : ℂ)) (fun μ t _ => pcfLG2_hasDerivAt_PU μ t)
    (fun μ t _ => (pcfLG2_hasDerivAt_PU' μ t).congr_deriv (by rw [pcfLG2_PA_pow_four_recip]))
    (fun μ hμ => pcfLG2_tendsto_PU_div (by linarith)) le_rfl hμ₀ hμ₀C
  refine ⟨((hcore 0) μ hμ).1, fun t => ?_⟩
  obtain ⟨-, ε, ε', hε⟩ := (hcore (t-1)) μ hμ
  obtain ⟨h1, h2, h3, h4⟩ := hε t (by linarith)
  refine ⟨?_, ε t, ε' t, h1, h2, h3, h4⟩
  have hu1 : 1 ≤ μ^2 := by nlinarith
  have hser := pcfLG2_abs_sum_sub_one_le hN (f := fun s => pcfLG2_Pa s t)
    (by simp [pcfLG2_Pa, pcfLG2_Q, pcfLG2_bar, pcfOlverU, pcfOlverPair])
    (fun s _ => pcfLG2_abs_Pa_le s t) hu1
  refine hser.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have : μ₀^2 ≤ μ^2 := by nlinarith
  nlinarith

end DLMF.Confluent
end
