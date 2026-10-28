/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Weber.Solutions

/-!
# Representations and transformations of Weber functions

Further representations and transformations of the real Weber functions, including their
normalization and parameter restrictions.

Source references and common attribution are retained in
`DLMF.ParabolicCylinder.Weber`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat ComplexConjugate

namespace DLMF.Confluent

open DLMF.Bessel

/-- Two entire solutions of `w'' = (a - z²/4) w` with the same data at `0` coincide. -/
theorem weberOsc_eq_of_initial {a : ℂ} {f f1 g g1 : ℂ → ℂ}
    (hf : ∀ z, HasDerivAt f (f1 z) z ∧ HasDerivAt f1 ((a - z^2/4) * f z) z)
    (hg : ∀ z, HasDerivAt g (g1 z) z ∧ HasDerivAt g1 ((a - z^2/4) * g z) z)
    (h0 : f 0 = g 0) (h1 : f1 0 = g1 0) : f = g := by
  have df : deriv f = f1 := funext fun z => (hf z).1.deriv
  have dg : deriv g = g1 := funext fun z => (hg z).1.deriv
  have hfd : Differentiable ℂ f := fun z => (hf z).1.differentiableAt
  have hgd : Differentiable ℂ g := fun z => (hg z).1.differentiableAt
  have h := ODE.eqOn_of_ode (p := fun _ => (0:ℂ)) (q := fun z => a - z^2/4) isOpen_univ
    isPreconnected_univ (fun z _ => hfd.analyticAt z) (fun z _ => hgd.analyticAt z) (mem_univ 0)
    (by fun_prop) (by fun_prop)
    (fun z _ => by rw [df, (hf z).2.deriv]; ring) (fun z _ => by rw [dg, (hg z).2.deriv]; ring)
    h0 (by rw [df, dg, h1])
  exact funext fun z => h (mem_univ z)

/-- `e^{-iπ/4}² = -i`. -/
theorem exp_neg_pi_I_quarter_sq : exp (-π*I/4)^2 = -I := by
  have h1 := exp_neg_pi_I_quarter_mul
  have h2 := exp_pi_I_quarter_sq
  linear_combination I * exp (-π*I/4)^2 * h2 - I * (exp (-π*I/4) * exp (π*I/4) + 1) * h1 +
    exp (-π*I/4)^2 * I_sq

/-- `U(± i a, c z)` for `c = e^{∓iπ/4}` solves `w'' = (a - z²/4) w`. -/
theorem pcfU_rot_weberOsc (a : ℝ) (z : ℂ) :
    (HasDerivAt (fun w => pcfU (I*a) (exp (-π*I/4) * w))
      (exp (-π*I/4) * pcfUDeriv (I*a) (exp (-π*I/4) * z)) z ∧
    HasDerivAt (fun w => exp (-π*I/4) * pcfUDeriv (I*a) (exp (-π*I/4) * w))
      ((a - z^2/4) * pcfU (I*a) (exp (-π*I/4) * z)) z) ∧
    (HasDerivAt (fun w => pcfU (-I*a) (exp (π*I/4) * w))
      (exp (π*I/4) * pcfUDeriv (-I*a) (exp (π*I/4) * z)) z ∧
    HasDerivAt (fun w => exp (π*I/4) * pcfUDeriv (-I*a) (exp (π*I/4) * w))
      ((a - z^2/4) * pcfU (-I*a) (exp (π*I/4) * z)) z) := by
  obtain ⟨h1, h2⟩ := (isWeberSol_pcfU (I*a)).hasDerivAt_rot (exp (-π*I/4)) z
  obtain ⟨h3, h4⟩ := (isWeberSol_pcfU (-I*a)).hasDerivAt_rot (exp (π*I/4)) z
  refine ⟨⟨h1, h2.congr_deriv ?_⟩, ⟨h3, h4.congr_deriv ?_⟩⟩
  · rw [mul_pow, exp_neg_pi_I_quarter_sq]
    linear_combination (z^2/4 - a) * pcfU (I*a) (exp (-π*I/4) * z) * I_sq
  · rw [mul_pow, exp_pi_I_quarter_sq]
    linear_combination (z^2/4 - a) * pcfU (-I*a) (exp (π*I/4) * z) * I_sq

/-- `conj (e^{ix}) = e^{-ix}` for real `x`. -/
theorem conj_exp_I_ofReal (x : ℝ) : conj (exp (I*x)) = exp (-I*x) := by
  rw [← Complex.exp_conj]; congr 1; simp

/-- `conj (e^{-iπ/4}) = e^{iπ/4}`. -/
theorem conj_exp_neg_pi_I_quarter : conj (exp (-π*I/4)) = exp (π*I/4) := by
  rw [← Complex.exp_conj]; congr 1; simp [map_div₀, map_ofNat]

/-- Identity under the stated parameter and domain assumptions: `pcfW a z=(Real.sqrt (pcfWK
a/2):ℂ)*exp (π*a/4)*(exp (I*pcfWRho a)*pcfU (I*a) (z*exp (-π*I/4))+exp (-I*pcfWRho a)*pcfU
(-I*a) (z*exp (π*I/4)))`. -/
@[dlmf 12.14.E4]
theorem pcfW_connection (a : ℝ) (z : ℂ) :
    pcfW a z=(Real.sqrt (pcfWK a/2):ℂ)*exp (π*a/4)*(exp (I*pcfWRho a)*pcfU (I*a) (z*exp (-π*I/4))+exp (-I*pcfWRho a)*pcfU (-I*a) (z*exp (π*I/4))) := by
  set K : ℂ := (Real.sqrt (pcfWK a/2):ℂ)*exp (π*a/4)
  set eρ := exp (I*pcfWRho a)
  set eρ' := exp (-I*pcfWRho a)
  set R : ℂ → ℂ := fun w => K * (eρ * pcfU (I*a) (exp (-π*I/4) * w) +
    eρ' * pcfU (-I*a) (exp (π*I/4) * w))
  set R1 : ℂ → ℂ := fun w => K * (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) (exp (-π*I/4) * w)) +
    eρ' * (exp (π*I/4) * pcfUDeriv (-I*a) (exp (π*I/4) * w)))
  have hR : ∀ w, HasDerivAt R (R1 w) w ∧ HasDerivAt R1 ((a - w^2/4) * R w) w := fun w => by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := pcfU_rot_weberOsc a w
    exact ⟨((h1.const_mul eρ).add (h3.const_mul eρ')).const_mul K,
      (((h2.const_mul eρ).add (h4.const_mul eρ')).const_mul K).congr_deriv (by ring)⟩
  have hW : ∀ w, HasDerivAt (pcfW a) (pcfWDeriv a w) w ∧
      HasDerivAt (pcfWDeriv a) ((a - w^2/4) * pcfW a w) w :=
    fun w => ⟨hasDerivAt_pcfW a w, hasDerivAt_pcfWDeriv a w⟩
  obtain ⟨s1, s2, -, -⟩ := pcfW_aux_scalar a
  have hK : K = ((Real.sqrt (pcfWK a/2) * Real.exp (π*a/4) : ℝ) : ℂ) := by
    simp only [K]; push_cast; rfl
  have hc1 : eρ' * pcfU (-I*a) 0 = conj (eρ * pcfU (I*a) 0) := by
    rw [map_mul, conj_exp_I_ofReal, conj_pcfU]; congr 2 <;> simp
  have hc2 : eρ' * (exp (π*I/4) * pcfUDeriv (-I*a) 0) =
      conj (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) 0)) := by
    rw [map_mul, map_mul, conj_exp_I_ofReal, conj_exp_neg_pi_I_quarter, conj_pcfUDeriv]
    congr 3 <;> simp
  have h0 : pcfW a 0 = R 0 := by
    rw [(pcfW_initial a).1]
    simp only [R, mul_zero]
    rw [hc1, Complex.add_conj, hK, s1]; push_cast; ring
  have h1 : pcfWDeriv a 0 = R1 0 := by
    have : pcfWDeriv a 0 = pcfWDerivZero a := by
      simp [pcfWDeriv, pcfEvenDeriv_zero, pcfOddDeriv_zero]
    rw [this]
    simp only [R1, mul_zero]
    rw [hc2, Complex.add_conj, hK]
    have s2' : pcfWDerivZero a = Real.sqrt (pcfWK a/2) * Real.exp (π*a/4) *
        (2 * (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).re) := by linarith
    rw [s2']; push_cast; ring
  have := congrFun (weberOsc_eq_of_initial hW hR h0 h1) z
  rw [this]; simp only [R, mul_comm _ z]

/-- Unnumbered companion connection formula in DLMF 12.14(iv). -/
theorem pcfW_connection_neg (a : ℝ) (z : ℂ) :
    pcfW a (-z)=-I/Real.sqrt (2*pcfWK a)*exp (π*a/4)*(exp (I*pcfWRho a)*pcfU (I*a) (z*exp (-π*I/4))-exp (-I*pcfWRho a)*pcfU (-I*a) (z*exp (π*I/4))) := by
  obtain ⟨-, -, s3, s4⟩ := pcfW_aux_scalar a
  set K : ℂ := -I/Real.sqrt (2*pcfWK a)*exp (π*a/4)
  set eρ := exp (I*pcfWRho a)
  set eρ' := exp (-I*pcfWRho a)
  set R : ℂ → ℂ := fun w => K * (eρ * pcfU (I*a) (exp (-π*I/4) * w) -
    eρ' * pcfU (-I*a) (exp (π*I/4) * w))
  set R1 : ℂ → ℂ := fun w => K * (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) (exp (-π*I/4) * w)) -
    eρ' * (exp (π*I/4) * pcfUDeriv (-I*a) (exp (π*I/4) * w)))
  have hR : ∀ w, HasDerivAt R (R1 w) w ∧ HasDerivAt R1 ((a - w^2/4) * R w) w := fun w => by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := pcfU_rot_weberOsc a w
    exact ⟨((h1.const_mul eρ).sub (h3.const_mul eρ')).const_mul K,
      (((h2.const_mul eρ).sub (h4.const_mul eρ')).const_mul K).congr_deriv (by ring)⟩
  have hW : ∀ w, HasDerivAt (fun w => pcfW a (-w)) (-pcfWDeriv a (-w)) w ∧
      HasDerivAt (fun w => -pcfWDeriv a (-w)) ((a - w^2/4) * pcfW a (-w)) w := fun w =>
    ⟨((hasDerivAt_pcfW a (-w)).comp w (hasDerivAt_neg w)).congr_deriv (by ring),
      ((hasDerivAt_pcfWDeriv a (-w)).comp w (hasDerivAt_neg w)).neg.congr_deriv (by ring)⟩
  have hsp : (Real.sqrt (2*pcfWK a) : ℂ) ≠ 0 := by
    have := (pcfWK_recip a).1
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  have hc1 : eρ' * pcfU (-I*a) 0 = conj (eρ * pcfU (I*a) 0) := by
    rw [map_mul, conj_exp_I_ofReal, conj_pcfU]; congr 2 <;> simp
  have hc2 : eρ' * (exp (π*I/4) * pcfUDeriv (-I*a) 0) =
      conj (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) 0)) := by
    rw [map_mul, map_mul, conj_exp_I_ofReal, conj_exp_neg_pi_I_quarter, conj_pcfUDeriv]
    congr 3 <;> simp
  have hE : exp (π*a/4) = ((Real.exp (π*a/4) : ℝ) : ℂ) := by push_cast; rfl
  have h0 : pcfW a (-0) = R 0 := by
    rw [neg_zero, (pcfW_initial a).1]
    simp only [R, mul_zero]
    rw [hc1, Complex.sub_conj, s3]
    simp only [K, hE]
    generalize (eρ * pcfU (I*a) 0).im = y
    push_cast
    field_simp
    linear_combination (y : ℂ) * I_sq
  have h1 : -pcfWDeriv a (-0) = R1 0 := by
    have : pcfWDeriv a 0 = pcfWDerivZero a := by
      simp [pcfWDeriv, pcfEvenDeriv_zero, pcfOddDeriv_zero]
    rw [neg_zero, this]
    simp only [R1, mul_zero]
    rw [hc2, Complex.sub_conj]
    have s4' : -(pcfWDerivZero a : ℂ) = ((2 * (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).im *
        Real.exp (π*a/4) / Real.sqrt (2*pcfWK a) : ℝ) : ℂ) := by rw [← s4]; push_cast; ring
    rw [s4']
    simp only [K, hE]
    generalize (eρ * (exp (-π*I/4) * pcfUDeriv (I*a) 0)).im = y
    push_cast
    field_simp
    linear_combination (y : ℂ) * I_sq
  have := congrFun (weberOsc_eq_of_initial hW hR h0 h1) z
  rw [this]; simp only [R, mul_comm _ z]

/-- Maclaurin recurrence for the pcfWAlpha coefficients. -/
def pcfWAlpha (a : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => a
  | n+2 => a*pcfWAlpha a (n+1)-1/2*(n+1)*(2*n+1)*pcfWAlpha a n

/-- Maclaurin recurrence for the pcfWBeta coefficients. -/
def pcfWBeta (a : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => a
  | n+2 => a*pcfWBeta a (n+1)-1/2*(n+1)*(2*n+3)*pcfWBeta a n

open scoped ContDiff in
/-- Taylor recurrence at `0` for solutions of `w'' = (a - z²/4) w`. -/
theorem weberOsc_iteratedDeriv_add_two {F F1 : ℂ → ℂ} {a : ℂ}
    (h : ∀ z, HasDerivAt F (F1 z) z ∧ HasDerivAt F1 ((a - z^2/4) * F z) z) (n : ℕ) :
    iteratedDeriv (n+2) F 0 =
      a * iteratedDeriv n F 0 - 1/4 * ((n.descFactorial 2 : ℕ) * iteratedDeriv (n-2) F 0) := by
  have hF : Differentiable ℂ F := fun z => (h z).1.differentiableAt
  have hc : ContDiff ℂ ∞ F := hF.contDiff
  have h1 : deriv F = F1 := funext fun z => (h z).1.deriv
  have h2 : deriv (deriv F) = fun z => a * F z - 1/4 * (z^2 * F z) := by
    rw [h1]; funext z; rw [(h z).2.deriv]; ring
  have hcn : ContDiffAt ℂ n F 0 := (hc.of_le (by exact_mod_cast le_top)).contDiffAt
  have hq : ContDiffAt ℂ n (fun z : ℂ => z^2 * F z) 0 := by fun_prop
  have hA : ContDiffAt ℂ n (fun z : ℂ => a * F z) 0 := by fun_prop
  have hB : ContDiffAt ℂ n (fun z : ℂ => 1/4 * (z^2 * F z)) 0 := by fun_prop
  rw [iteratedDeriv_succ', iteratedDeriv_succ', h2, iteratedDeriv_fun_sub hA hB,
    iteratedDeriv_const_mul a hcn, iteratedDeriv_const_mul _ hq, ODE.iteratedDeriv_pow_mul_zero hcn]

/-- First and second derivatives of `pcfWEven`: Weber's equation `w'' = (a - z²/4) w`. -/
theorem pcfWEven_hasDerivAt_two (a z : ℂ) :
    HasDerivAt (pcfWEven a) (exp (π*I/4) * pcfEvenDeriv (-I*a) (exp (π*I/4)*z)) z ∧
      HasDerivAt (fun w => exp (π*I/4) * pcfEvenDeriv (-I*a) (exp (π*I/4)*w))
        ((a - z^2/4) * pcfWEven a z) z := by
  obtain ⟨h1, h2⟩ := (isWeberSol_pcfEven (-I*a)).hasDerivAt_rot (exp (π*I/4)) z
  refine ⟨h1, h2.congr_deriv ?_⟩
  rw [pcfWEven, mul_pow, exp_pi_I_quarter_sq]
  linear_combination (z^2/4 - a) * pcfEven (-I * a) (exp (↑π * I / 4) * z) * I_sq

/-- First and second derivatives of `pcfWOdd`: Weber's equation `w'' = (a - z²/4) w`. -/
theorem pcfWOdd_hasDerivAt_two (a z : ℂ) :
    HasDerivAt (pcfWOdd a) (exp (-π*I/4) * (exp (π*I/4) * pcfOddDeriv (-I*a) (exp (π*I/4)*z))) z ∧
      HasDerivAt (fun w => exp (-π*I/4) * (exp (π*I/4) * pcfOddDeriv (-I*a) (exp (π*I/4)*w)))
        ((a - z^2/4) * pcfWOdd a z) z := by
  obtain ⟨h1, h2⟩ := (isWeberSol_pcfOdd (-I*a)).hasDerivAt_rot (exp (π*I/4)) z
  refine ⟨h1.const_mul _, (h2.const_mul _).congr_deriv ?_⟩
  rw [pcfWOdd, mul_pow, exp_pi_I_quarter_sq]
  linear_combination (exp (-π*I/4)) * (z^2/4 - a) * pcfOdd (-I * a) (exp (↑π * I / 4) * z) * I_sq

/-- Derivatives of `pcfWEven` at `0`: the `pcfWAlpha` recurrence and vanishing odd orders. -/
theorem pcfWEven_iteratedDeriv (a : ℂ) (n : ℕ) :
    (iteratedDeriv (2*n) (pcfWEven a) 0 = pcfWAlpha a n ∧
      iteratedDeriv (2*n+2) (pcfWEven a) 0 = pcfWAlpha a (n+1)) ∧
    (iteratedDeriv (2*n+1) (pcfWEven a) 0 = 0 ∧ iteratedDeriv (2*n+3) (pcfWEven a) 0 = 0) := by
  have hr := weberOsc_iteratedDeriv_add_two (fun z => pcfWEven_hasDerivAt_two a z)
  have d0 : iteratedDeriv 0 (pcfWEven a) 0 = 1 := by simp [pcfWEven, pcfEven]
  have d1 : iteratedDeriv 1 (pcfWEven a) 0 = 0 := by
    rw [iteratedDeriv_one, (pcfWEven_hasDerivAt_two a 0).1.deriv]; simp [pcfEvenDeriv_zero]
  induction n with
  | zero =>
    refine ⟨⟨by simpa [pcfWAlpha] using d0, ?_⟩, ⟨by simpa using d1, ?_⟩⟩
    · rw [hr 0, d0]; simp [pcfWAlpha]
    · rw [hr 1, d1]; simp
  | succ n ih =>
    refine ⟨⟨by rw [show 2*(n+1) = 2*n+2 by ring]; exact ih.1.2, ?_⟩,
      ⟨by rw [show 2*(n+1)+1 = 2*n+3 by ring]; exact ih.2.2, ?_⟩⟩
    · rw [show 2*(n+1)+2 = (2*n+2)+2 by ring, hr, ih.1.2, show 2*n+2-2 = 2*n by omega, ih.1.1,
        pcfWAlpha]
      simp only [Nat.descFactorial, Nat.succ_sub_one]
      push_cast; ring
    · rw [show 2*(n+1)+3 = (2*n+3)+2 by ring, hr, ih.2.2, show 2*n+3-2 = 2*n+1 by omega, ih.2.1]
      simp

/-- Derivatives of `pcfWOdd` at `0`: the `pcfWBeta` recurrence and vanishing even orders. -/
theorem pcfWOdd_iteratedDeriv (a : ℂ) (n : ℕ) :
    (iteratedDeriv (2*n+1) (pcfWOdd a) 0 = pcfWBeta a n ∧
      iteratedDeriv (2*n+3) (pcfWOdd a) 0 = pcfWBeta a (n+1)) ∧
    (iteratedDeriv (2*n) (pcfWOdd a) 0 = 0 ∧ iteratedDeriv (2*n+2) (pcfWOdd a) 0 = 0) := by
  have hr := weberOsc_iteratedDeriv_add_two (fun z => pcfWOdd_hasDerivAt_two a z)
  have d0 : iteratedDeriv 0 (pcfWOdd a) 0 = 0 := by simp [pcfWOdd, pcfOdd]
  have d1 : iteratedDeriv 1 (pcfWOdd a) 0 = 1 := by
    rw [iteratedDeriv_one, (pcfWOdd_hasDerivAt_two a 0).1.deriv, ← mul_assoc,
      exp_neg_pi_I_quarter_mul]; simp [pcfOddDeriv_zero]
  induction n with
  | zero =>
    refine ⟨⟨by simpa [pcfWBeta] using d1, ?_⟩, ⟨by simpa using d0, ?_⟩⟩
    · rw [hr 1, d1]; simp [pcfWBeta]
    · rw [hr 0, d0]; simp
  | succ n ih =>
    refine ⟨⟨by rw [show 2*(n+1)+1 = 2*n+3 by ring]; exact ih.1.2, ?_⟩,
      ⟨by rw [show 2*(n+1) = 2*n+2 by ring]; exact ih.2.2, ?_⟩⟩
    · rw [show 2*(n+1)+3 = (2*n+3)+2 by ring, hr, ih.1.2, show 2*n+3-2 = 2*n+1 by omega, ih.1.1,
        pcfWBeta]
      simp only [Nat.descFactorial, Nat.succ_sub_one]
      push_cast; ring
    · rw [show 2*(n+1)+2 = (2*n+2)+2 by ring, hr, ih.2.2, show 2*n+2-2 = 2*n by omega, ih.2.1]
      simp

/-- The series with terms `(fun n : ℕ => pcfWAlpha a n*z^(2*n)/((2*n).factorial:ℂ))` converges to
`(pcfWEven a z)`. -/
@[dlmf 12.14.E9, dlmf 12.14.E11, dlmf 12.14.E12]
theorem pcfWEven_series (a z : ℂ) :
    HasSum (fun n : ℕ => pcfWAlpha a n*z^(2*n)/((2*n).factorial:ℂ)) (pcfWEven a z) := by
  have hd : Differentiable ℂ (pcfWEven a) := fun w => (pcfWEven_hasDerivAt_two a w).1.differentiableAt
  have hT := Complex.hasSum_taylorSeries_of_entire hd 0 z
  have hinj : Function.Injective (fun n : ℕ => 2*n) := fun m n h => by simpa using h
  rw [← hinj.hasSum_iff] at hT
  · convert hT using 1
    funext n
    simp only [Function.comp_apply, sub_zero, smul_eq_mul, (pcfWEven_iteratedDeriv a n).1.1]
    field_simp
  · intro x hx
    obtain ⟨k, rfl⟩ : Odd x := by
      rcases Nat.even_or_odd x with ⟨k, hk⟩ | h
      · exact absurd ⟨k, by simp [hk]; ring⟩ hx
      · exact h
    simp [(pcfWEven_iteratedDeriv a k).2.1]

/-- The series with terms `(fun n : ℕ => pcfWBeta a n*z^(2*n+1)/((2*n+1).factorial:ℂ))` converges
to `(pcfWOdd a z)`. -/
@[dlmf 12.14.E10, dlmf 12.14.E11, dlmf 12.14.E12]
theorem pcfWOdd_series (a z : ℂ) :
    HasSum (fun n : ℕ => pcfWBeta a n*z^(2*n+1)/((2*n+1).factorial:ℂ)) (pcfWOdd a z) := by
  have hd : Differentiable ℂ (pcfWOdd a) := fun w => (pcfWOdd_hasDerivAt_two a w).1.differentiableAt
  have hT := Complex.hasSum_taylorSeries_of_entire hd 0 z
  have hinj : Function.Injective (fun n : ℕ => 2*n+1) := fun m n h => by simpa using h
  rw [← hinj.hasSum_iff] at hT
  · convert hT using 1
    funext n
    simp only [Function.comp_apply, sub_zero, smul_eq_mul, (pcfWOdd_iteratedDeriv a n).1.1]
    field_simp
  · intro x hx
    obtain ⟨k, rfl⟩ : Even x := by
      rcases Nat.even_or_odd x with h | ⟨k, hk⟩
      · exact h
      · exact absurd ⟨k, hk.symm⟩ hx
    simp [← two_mul, (pcfWOdd_iteratedDeriv a k).2.1]

/-- `Γ(1/4) Γ(3/4) = π √2`. -/
theorem real_Gamma_quarter_mul : Real.Gamma (1/4) * Real.Gamma (3/4) = π * Real.sqrt 2 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1/4)
  rw [show (1:ℝ) - 1/4 = 3/4 by norm_num, show π * (1/4) = π/4 by ring, Real.sin_pi_div_four] at h
  rw [h]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

/-- `W(0,0) = 2^{-3/4} √(Γ(1/4)/Γ(3/4))`. -/
theorem pcfWZero_zero : pcfWZero 0 = 2^(-3/4:ℝ) * Real.sqrt (Real.Gamma (1/4) / Real.Gamma (3/4)) := by
  rw [pcfWZero]
  congr 2
  simp only [Complex.ofReal_zero, mul_zero, zero_div, add_zero]
  rw [show (1/4:ℂ) = ((1/4:ℝ):ℂ) by push_cast; ring, show (3/4:ℂ) = ((3/4:ℝ):ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_div, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le (Real.Gamma_pos_of_pos (by norm_num)).le)]

/-- `W'(0,0) = -2^{-1/4} √(Γ(3/4)/Γ(1/4))`. -/
theorem pcfWDerivZero_zero : pcfWDerivZero 0 = -2^(-1/4:ℝ) * Real.sqrt (Real.Gamma (3/4) / Real.Gamma (1/4)) := by
  rw [pcfWDerivZero]
  congr 2
  simp only [Complex.ofReal_zero, mul_zero, zero_div, add_zero]
  rw [show (1/4:ℂ) = ((1/4:ℝ):ℂ) by push_cast; ring, show (3/4:ℂ) = ((3/4:ℝ):ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_div, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le (Real.Gamma_pos_of_pos (by norm_num)).le)]

/-- Identity under the stated parameter and domain assumptions: `(y^(r/4))^4 = y^r`. -/
theorem rpow_quarter_pow_four {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y^(r/4))^4 = y^r := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num

/-- Equality of positive reals from equality of fourth powers. -/
theorem eq_of_pow_four_eq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u^4 = v^4) : u = v :=
  (pow_left_inj₀ hu hv (by norm_num : (4:ℕ) ≠ 0)).mp h

/-- The real coefficient of `J_{-1/4}` in `W(0,x)`. -/
theorem pcfW_zero_coeffA {x : ℝ} (hx : 0 < x) :
    pcfWZero 0 * Real.Gamma (3/4) * (x^2/8)^(1/4:ℝ) = 2^(-5/4:ℝ) * (π*x)^(1/2:ℝ) := by
  have g1 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/4)
  have g3 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3/4)
  rw [pcfWZero_zero]
  apply eq_of_pow_four_eq (by positivity) (by positivity)
  rw [mul_pow, mul_pow, mul_pow, mul_pow, show (-3/4:ℝ) = -3/4 by ring, show (1/4:ℝ) = 1/4 by ring,
    show (-3/4:ℝ) = (-3)/4 by ring, rpow_quarter_pow_four (by norm_num), show (1/4:ℝ) = 1/4 from rfl,
    rpow_quarter_pow_four (by positivity) 1, show (-5/4:ℝ) = (-5)/4 by ring, rpow_quarter_pow_four (by norm_num),
    show (1/2:ℝ) = 2/4 by norm_num, rpow_quarter_pow_four (by positivity),
    show (Real.sqrt (Real.Gamma (1/4) / Real.Gamma (3/4)))^4 = (Real.Gamma (1/4) / Real.Gamma (3/4))^2 by
      rw [show 4 = 2*2 by rfl, pow_mul, Real.sq_sqrt (by positivity)]]
  have hq := real_Gamma_quarter_mul
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  simp only [Real.rpow_one, Real.rpow_two, Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num)]
  field_simp
  linear_combination 32*(Real.Gamma (1/4) * Real.Gamma (3/4) + π*Real.sqrt 2) * hq + 32*π^2 * hs

/-- The real coefficient of `J_{1/4}` in `W(0,x)`. -/
theorem pcfW_zero_coeffB {x : ℝ} (hx : 0 < x) :
    -pcfWDerivZero 0 * x * Real.Gamma (5/4) * (x^2/8)^(-1/4:ℝ) = 2^(-5/4:ℝ) * (π*x)^(1/2:ℝ) := by
  have g1 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/4)
  have g3 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3/4)
  have g5 : Real.Gamma (5/4) = Real.Gamma (1/4) / 4 := by
    rw [show (5/4:ℝ) = 1/4 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]; ring
  rw [pcfWDerivZero_zero, g5]
  simp only [neg_mul, neg_neg]
  apply eq_of_pow_four_eq (by positivity) (by positivity)
  rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
    show (-1/4:ℝ) = (-1)/4 by ring, rpow_quarter_pow_four (by norm_num),
    rpow_quarter_pow_four (by positivity) (-1), show (-5/4:ℝ) = (-5)/4 by ring, rpow_quarter_pow_four (by norm_num),
    show (1/2:ℝ) = 2/4 by norm_num, rpow_quarter_pow_four (by positivity),
    show (Real.sqrt (Real.Gamma (3/4) / Real.Gamma (1/4)))^4 = (Real.Gamma (3/4) / Real.Gamma (1/4))^2 by
      rw [show 4 = 2*2 by rfl, pow_mul, Real.sq_sqrt (by positivity)]]
  have hq := real_Gamma_quarter_mul
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  simp only [Real.rpow_one, Real.rpow_two, Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num),
    Real.rpow_neg (show (0:ℝ) ≤ x^2/8 by positivity)]
  field_simp
  linear_combination 256*(Real.Gamma (1/4) * Real.Gamma (3/4) + π*Real.sqrt 2) * hq + 256*π^2 * hs

/-- Real `cpow` of a nonnegative real is real. -/
theorem ofReal_cpow_real {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y:ℂ)^(r:ℂ) = ((y^r : ℝ) : ℂ) :=
  (Complex.ofReal_cpow hy r).symm

/-- `W`'s even solution at `a = 0` through `J_{-1/4}`. -/
theorem pcfWEven_zero_besselJ {t : ℝ} (ht : 0 < t) :
    pcfWEven 0 t = Gamma (3/4) * (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * besselJ (-1/4) ((t:ℂ)^2/4) := by
  have hν : ∀ k : ℕ, (-1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have h2ν : ∀ k : ℕ, 2*(-1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hy : (0:ℝ) < t^2/8 := by positivity
  rw [besselJ_eq_kummerM hν h2ν, (pcfWEven_kummer _ _).1,
    show (t:ℂ)^2/4/2 = ((t^2/8 : ℝ) : ℂ) by push_cast; ring, show (-1/4:ℂ) = ((-1/4:ℝ):ℂ) by push_cast; ring,
    ofReal_cpow_real hy.le]
  have hG : Gamma (3/4:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hm : ((t^2/8)^(1/4:ℝ) : ℝ) * (t^2/8)^(-1/4:ℝ) = 1 := by
    rw [← Real.rpow_add hy]; norm_num
  have hm' : (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) = 1 := by exact_mod_cast hm
  rw [show ((-1/4:ℝ):ℂ) + 1 = 3/4 by push_cast; ring, show ((-1/4:ℝ):ℂ) + 1/2 = 1/4 by push_cast; ring,
    show 2*((-1/4:ℝ):ℂ) + 1 = 1/2 by push_cast; ring, show 2*I*((t:ℂ)^2/4) = I*(t:ℂ)^2/2 by ring,
    show -I*((t:ℂ)^2/4) = -I*(t:ℂ)^2/4 by ring]
  simp only [mul_zero, zero_div, sub_zero]
  have hg := mul_inv_cancel₀ hG
  linear_combination (-(exp (-I*(t:ℂ)^2/4) * kummerM (1/4) (1/2) (I*(t:ℂ)^2/2))) * hm'
    - ((((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) *
      exp (-I*(t:ℂ)^2/4) * kummerM (1/4) (1/2) (I*(t:ℂ)^2/2)) * hg

/-- `W`'s odd solution at `a = 0` through `J_{1/4}`. -/
theorem pcfWOdd_zero_besselJ {t : ℝ} (ht : 0 < t) :
    pcfWOdd 0 t = t * Gamma (5/4) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) * besselJ (1/4) ((t:ℂ)^2/4) := by
  have hν : ∀ k : ℕ, (1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have h2ν : ∀ k : ℕ, 2*(1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hy : (0:ℝ) < t^2/8 := by positivity
  rw [besselJ_eq_kummerM hν h2ν, (pcfWOdd_kummer _ _).1,
    show (t:ℂ)^2/4/2 = ((t^2/8 : ℝ) : ℂ) by push_cast; ring, show (1/4:ℂ) = ((1/4:ℝ):ℂ) by push_cast; ring,
    ofReal_cpow_real hy.le]
  have hG : Gamma (5/4:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hm : ((t^2/8)^(1/4:ℝ) : ℝ) * (t^2/8)^(-1/4:ℝ) = 1 := by
    rw [← Real.rpow_add hy]; norm_num
  have hm' : (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) = 1 := by exact_mod_cast hm
  rw [show ((1/4:ℝ):ℂ) + 1 = 5/4 by push_cast; ring, show ((1/4:ℝ):ℂ) + 1/2 = 3/4 by push_cast; ring,
    show 2*((1/4:ℝ):ℂ) + 1 = 3/2 by push_cast; ring, show 2*I*((t:ℂ)^2/4) = I*(t:ℂ)^2/2 by ring,
    show -I*((t:ℂ)^2/4) = -I*(t:ℂ)^2/4 by ring]
  simp only [mul_zero, zero_div, sub_zero]
  have hg := mul_inv_cancel₀ hG
  linear_combination (-(t * exp (-I*(t:ℂ)^2/4) * kummerM (3/4) (3/2) (I*(t:ℂ)^2/2))) * hm'
    - (t * (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) *
      exp (-I*(t:ℂ)^2/4) * kummerM (3/4) (3/2) (I*(t:ℂ)^2/2)) * hg

/-- `pcfWEven` is even. -/
theorem pcfWEven_neg (a z : ℂ) : pcfWEven a (-z) = pcfWEven a z := by
  simp [pcfWEven, pcfEven, mul_neg]

/-- `pcfWOdd` is odd. -/
theorem pcfWOdd_neg (a z : ℂ) : pcfWOdd a (-z) = -pcfWOdd a z := by
  simp [pcfWOdd, pcfOdd, mul_neg]

/-- Complex form of the `J_{-1/4}` coefficient. -/
theorem pcfW_zero_coeffA' {x : ℝ} (hx : 0 < x) :
    (pcfWZero 0 : ℂ) * Gamma (3/4) * (((x^2/8)^(1/4:ℝ) : ℝ) : ℂ) = 2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ) := by
  have h := congrArg (fun r : ℝ => (r:ℂ)) (pcfW_zero_coeffA hx)
  simp only [Complex.ofReal_mul] at h
  rw [show (3/4:ℂ) = ((3/4:ℝ):ℂ) by push_cast; ring, Complex.Gamma_ofReal, h,
    Complex.ofReal_cpow (by norm_num), Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

/-- Complex form of the `J_{1/4}` coefficient. -/
theorem pcfW_zero_coeffB' {x : ℝ} (hx : 0 < x) :
    -(pcfWDerivZero 0 : ℂ) * x * Gamma (5/4) * (((x^2/8)^(-1/4:ℝ) : ℝ) : ℂ) = 2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ) := by
  have h := congrArg (fun r : ℝ => (r:ℂ)) (pcfW_zero_coeffB hx)
  simp only [Complex.ofReal_mul, Complex.ofReal_neg] at h
  rw [show (5/4:ℂ) = ((5/4:ℝ):ℂ) by push_cast; ring, Complex.Gamma_ofReal, h,
    Complex.ofReal_cpow (by norm_num), Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

/-- Derivative of the complex Bessel form of `W(0, ±w)`. -/
lemma pcfW_zero_bessel_hasDerivAt_aux (ε : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun w : ℂ => 2^(-5/4:ℂ)*(π*w)^(1/2:ℂ)*(besselJ (-1/4) (w^2/4)-ε*besselJ (1/4) (w^2/4)))
      (-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+ε*besselJ (-3/4) (x^2/4))) (x:ℂ) := by
  have hz : ((x:ℂ)^2/4) ∈ slitPlane := by
    rw [show (x:ℂ)^2/4 = ((x^2/4:ℝ):ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.2 (by positivity)
  have hp : (π*(x:ℂ)) ∈ slitPlane := by
    rw [show (π:ℂ)*(x:ℂ) = ((π*x:ℝ):ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.2 (by positivity)
  have hsq : HasDerivAt (fun w : ℂ => w^2/4) ((x:ℂ)/2) x := by
    exact ((hasDerivAt_pow 2 (x:ℂ)).div_const 4).congr_deriv (by simp; ring)
  have h1 := (hasDerivAt_besselJ (ν := -1/4) hz).comp (x:ℂ) hsq
  have h2 := (hasDerivAt_besselJ' (ν := 1/4) hz).comp (x:ℂ) hsq
  have hc := ((hasDerivAt_id (x:ℂ)).const_mul (π:ℂ)).cpow_const (c := 1/2) (by simpa using hp)
  have := (hc.const_mul (2^(-5/4:ℂ))).mul (h1.sub (h2.const_mul ε))
  convert this using 1
  · ext w; simp
  simp only [id, Function.comp, Pi.sub_apply]
  have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpx : (π:ℂ)*x ≠ 0 := mul_ne_zero hπ hx0
  rw [Complex.cpow_sub _ _ hpx, Complex.cpow_one, show (-9/4:ℂ) = -5/4 - 1 by norm_num,
    Complex.cpow_sub _ _ two_ne_zero, Complex.cpow_one,
    show (-1/4:ℂ) + 1 = 3/4 by norm_num, show (1/4:ℂ) - 1 = -3/4 by norm_num]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `pcfW 0
(1*x)=2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ)*(besselJ (-1/4) (x^2/4)-(1:ℂ)*besselJ (1/4) (x^2/4))`. -/
@[dlmf 12.14.E13]
theorem pcfW_zero_bessel_1 {x : ℝ} (hx : 0 < x) :
    pcfW 0 (1*x)=2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ)*(besselJ (-1/4) (x^2/4)-(1:ℂ)*besselJ (1/4) (x^2/4)) := by
  rw [one_mul, pcfW, Complex.ofReal_zero, pcfWEven_zero_besselJ hx, pcfWOdd_zero_besselJ hx]
  linear_combination besselJ (-1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffA' hx
    - besselJ (1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffB' hx

/-- At `x`, the function `(fun t : ℝ => pcfW 0 (1*t))` has derivative
`(-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+(1:ℂ)*besselJ (-3/4) (x^2/4)))`. -/
@[dlmf 12.14.E14]
theorem pcfW_zero_bessel_deriv_1 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => pcfW 0 (1*t)) (-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+(1:ℂ)*besselJ (-3/4) (x^2/4))) x := by
  refine (pcfW_zero_bessel_hasDerivAt_aux 1 hx).comp_ofReal.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with t ht
  exact pcfW_zero_bessel_1 ht

/-- Identity under the stated parameter and domain assumptions: `pcfW 0
(-1*x)=2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ)*(besselJ (-1/4) (x^2/4)-(-1:ℂ)*besselJ (1/4) (x^2/4))`. -/
@[dlmf 12.14.E13]
theorem pcfW_zero_bessel_2 {x : ℝ} (hx : 0 < x) :
    pcfW 0 (-1*x)=2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ)*(besselJ (-1/4) (x^2/4)-(-1:ℂ)*besselJ (1/4) (x^2/4)) := by
  rw [neg_one_mul, pcfW, Complex.ofReal_zero, pcfWEven_neg, pcfWOdd_neg, pcfWEven_zero_besselJ hx,
    pcfWOdd_zero_besselJ hx]
  linear_combination besselJ (-1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffA' hx
    + besselJ (1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffB' hx

/-- At `x`, the function `(fun t : ℝ => pcfW 0 (-1*t))` has derivative
`(-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+(-1:ℂ)*besselJ (-3/4) (x^2/4)))`. -/
@[dlmf 12.14.E14]
theorem pcfW_zero_bessel_deriv_2 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => pcfW 0 (-1*t)) (-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+(-1:ℂ)*besselJ (-3/4) (x^2/4))) x := by
  refine (pcfW_zero_bessel_hasDerivAt_aux (-1) hx).comp_ofReal.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with t ht
  exact pcfW_zero_bessel_2 ht

/-- The large-real-argument phase `x²/4 - a log x + π/4` plus half the Gamma phase. -/
@[dlmf 12.14.E19]
def pcfWOmega (a x : ℝ) : ℝ :=
  x^2/4-a*Real.log x+π/4+pcfGammaPhase a/2

/-- `W(a,x)` is real. -/
theorem pcfW_ofReal_im (a x : ℝ) : (pcfW a x).im = 0 := by
  rw [← Complex.conj_eq_iff_im]; simpa using conj_pcfW_conj a x

/-- `W(a,z)` and `W(a,-z)` do not vanish together. -/
theorem pcfW_one_ne (a : ℝ) (z : ℂ) (h1 : pcfW a z = 0) (h2 : pcfW a (-z) = 0) : False := by
  have hw := pcfW_wronskian_aux a z
  have := pcfWZero_mul_pcfWDerivZero a
  have : (pcfWZero a : ℂ) * pcfWDerivZero a = -1/2 := by exact_mod_cast this
  rw [h1, h2] at hw
  have : (0:ℂ) = 1 := by linear_combination hw - 2 * this
  exact zero_ne_one this

/-- `W'(a,z)` and `W'(a,-z)` do not vanish together. -/
theorem pcfWDeriv_one_ne (a : ℝ) (z : ℂ) (h1 : pcfWDeriv a z = 0) (h2 : pcfWDeriv a (-z) = 0) : False := by
  have hw := pcfW_wronskian_aux a z
  have := pcfWZero_mul_pcfWDerivZero a
  have : (pcfWZero a : ℂ) * pcfWDerivZero a = -1/2 := by exact_mod_cast this
  rw [h1, h2] at hw
  have : (0:ℂ) = 1 := by linear_combination hw - 2 * this
  exact zero_ne_one this

/-- Combined exact amplitude s1+i s2, recovered from the two real W solutions. -/
@[dlmf 12.14.E17, dlmf 12.14.E18]
def pcfWS (a x : ℝ) : ℂ :=
  exp (-I*pcfWOmega a x)*(Real.sqrt (x/(2*pcfWK a))*pcfW a x+I*Real.sqrt (pcfWK a*x/2)*pcfW a (-x))

/-- Identity under the stated parameter and domain assumptions: `pcfW a x=Real.sqrt (2*pcfWK
a/x)*((pcfWS a x).re*Real.cos (pcfWOmega a x)-(pcfWS a x).im*Real.sin (pcfWOmega a x)) ∧ pcfW
a (-x)=Real.sqrt (2/(pcfWK a*x))*((pcfWS a x).re*Real.sin (pcfWOmega a x)+(pcfWS a
x).im*Real.cos (pcfWOmega a x))`. -/
@[dlmf 12.14.E17, dlmf 12.14.E18]
theorem pcfW_amplitude (a : ℝ) {x : ℝ} (hx : 0 < x) :
    pcfW a x=Real.sqrt (2*pcfWK a/x)*((pcfWS a x).re*Real.cos (pcfWOmega a x)-(pcfWS a x).im*Real.sin (pcfWOmega a x)) ∧ pcfW a (-x)=Real.sqrt (2/(pcfWK a*x))*((pcfWS a x).re*Real.sin (pcfWOmega a x)+(pcfWS a x).im*Real.cos (pcfWOmega a x)) := by
  have h1r := pcfW_ofReal_im a x
  have h2r := pcfW_ofReal_im a (-x)
  push_cast at h2r
  have hk := (pcfWK_recip a).1
  set ω := pcfWOmega a x
  set k := pcfWK a
  set p := Real.sqrt (x/(2*k))
  set q := Real.sqrt (k*x/2)
  have hT : exp (I*ω) * pcfWS a x = p * pcfW a x + I * (q * pcfW a (-x)) := by
    rw [pcfWS, ← mul_assoc, ← Complex.exp_add, show I*ω + -I*ω = 0 by ring, Complex.exp_zero, one_mul]
    ring
  have hre := congrArg Complex.re hT
  have him := congrArg Complex.im hT
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    h1r, h2r, mul_comm I] at hre him
  have hp : Real.sqrt (2*k/x) * p = 1 := by
    rw [← Real.sqrt_mul (by positivity)]; field_simp; simp
  have hq : Real.sqrt (2/(k*x)) * q = 1 := by
    rw [← Real.sqrt_mul (by positivity)]; field_simp; simp
  have e1 : pcfW a x = ((pcfW a x).re : ℂ) := (Complex.ext (by simp) (by simp [h1r]))
  have e2 : pcfW a (-x) = ((pcfW a (-x)).re : ℂ) := (Complex.ext (by simp) (by simp [h2r]))
  constructor
  · rw [e1]
    have : (pcfW a x).re = Real.sqrt (2*k/x) * ((pcfWS a x).re * Real.cos ω - (pcfWS a x).im * Real.sin ω) := by
      linear_combination (-Real.sqrt (2*k/x)) * hre - (pcfW a x).re * hp
    rw [this]; push_cast; ring
  · rw [e2]
    have : (pcfW a (-x)).re = Real.sqrt (2/(k*x)) * ((pcfWS a x).re * Real.sin ω + (pcfWS a x).im * Real.cos ω) := by
      linear_combination (-Real.sqrt (2/(k*x))) * him - (pcfW a (-x)).re * hq
    rw [this]; push_cast; ring

/-- The rising-factorial coefficient `(1/2+ia)_{2r}` in the large-argument Weber expansion. -/
@[dlmf 12.14.E22]
def pcfWCoeff (a : ℝ) (r : ℕ) : ℂ :=
  poch (1/2+I*a) (2*r)

/- DLMF 12.14.22 is Mathlib's `Complex.Gamma_add_nat_div_Gamma_eq`,
with z=1/2+i*a and n=2*r. The real part of z is positive, so its regularity
hypothesis holds. `pcfWCoeff` uses the equivalent Pochhammer definition.
This upstream gamma-ratio identity is not reproved here. -/

/-- `s₁ + i s₂` of DLMF 12.14.17–18 is the normalized `e^{ζ²/4} ζ^{ia+1/2} U(ia, ζ)` at
`ζ = x e^{-iπ/4}` (from the connection formula DLMF 12.14.4). -/
theorem pcfSect_pcfWS_eq (a : ℝ) {x : ℝ} (hx : 0 < x) :
    pcfWS a x = pcfSect_G (I * a) (exp ((Real.log x : ℂ) + ((-(π/4) : ℝ) : ℂ) * I)) := by
  set v : ℂ := (Real.log x : ℂ) + ((-(π/4) : ℝ) : ℂ) * I
  have hv1 : -π < v.im := by simp [v]; linarith [Real.pi_pos]
  have hv2 : v.im ≤ π := by simp [v]; linarith [Real.pi_pos]
  have hζ : (x : ℂ) * exp (-π * I / 4) = exp v := by
    simp only [v]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hx]
    congr 1; push_cast; ring_nf
  have hk := (pcfWK_recip a).1
  have hs1 : (Real.sqrt (x / (2 * pcfWK a)) : ℂ) * (Real.sqrt (pcfWK a / 2) : ℂ) =
      (Real.sqrt x : ℂ) / 2 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity),
      show x / (2 * pcfWK a) * (pcfWK a / 2) = x / 4 by field_simp; ring,
      Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    push_cast; ring
  have hs2 : (Real.sqrt (pcfWK a * x / 2) : ℂ) / (Real.sqrt (2 * pcfWK a) : ℂ) =
      (Real.sqrt x : ℂ) / 2 := by
    rw [← Complex.ofReal_div, ← Real.sqrt_div' _ (by positivity),
      show pcfWK a * x / 2 / (2 * pcfWK a) = x / 4 by field_simp; ring,
      Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    push_cast; ring
  have hsq : (Real.sqrt x : ℂ) = exp ((Real.log x : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, Complex.ofReal_exp]; push_cast; ring_nf
  have hW1 := pcfW_connection a x
  have hW2 := pcfW_connection_neg a x
  rw [hζ, pcfSect_pcfU_exp (I * a) hv1 hv2] at hW1 hW2
  set P := exp (-exp (2 * v) / 4 - (I * a + 1 / 2) * v)
  set G := pcfSect_G (I * a) (exp v)
  set U2 := pcfU (-I * a) (x * exp (π * I / 4))
  set eA := exp (π * (a:ℂ) / 4)
  set eρ := exp (I * (pcfWRho a : ℂ))
  set eρ' := exp (-I * (pcfWRho a : ℂ))
  have hW2' : I * (Real.sqrt (pcfWK a * x / 2) : ℂ) * pcfW a (-x) =
      ((Real.sqrt (pcfWK a * x / 2) : ℂ) / (Real.sqrt (2 * pcfWK a) : ℂ)) * eA *
        (eρ * (P * G) - eρ' * U2) := by
    rw [hW2]
    linear_combination (-((Real.sqrt (pcfWK a * x / 2) : ℂ) / (Real.sqrt (2 * pcfWK a) : ℂ)) *
      eA * (eρ * (P * G) - eρ' * U2)) * I_sq
  have h2v : exp (2 * v) = -I * (x : ℂ) ^ 2 := by
    rw [show (2:ℂ) * v = ((2:ℕ):ℂ) * v by norm_num, Complex.exp_nat_mul, ← hζ, mul_pow,
      exp_neg_pi_I_quarter_sq]; ring
  have key : exp (-I * (pcfWOmega a x : ℂ)) * (Real.sqrt x : ℂ) * eA * eρ * P = 1 := by
    simp only [P, eA, eρ]
    rw [hsq, h2v, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    refine (congrArg exp ?_).trans Complex.exp_zero
    simp only [v, pcfWOmega, pcfWRho]
    push_cast
    linear_combination (π * a / 4) * I_sq
  unfold pcfWS
  rw [hW2', hW1]
  linear_combination (exp (-I * (pcfWOmega a x : ℂ)) * eA * (eρ * (P * G) + eρ' * U2)) * hs1 +
    (exp (-I * (pcfWOmega a x : ℂ)) * eA * (eρ * (P * G) - eρ' * U2)) * hs2 + G * key

/-- Asymptotic bound with the indicated comparison function: `(fun x : ℝ => pcfWS a x-∑ r ∈
Finset.range N, (-I)^r*pcfWCoeff a r/(2^r*(r.factorial:ℂ)*(x:ℂ)^(2*r))) =O[atTop] (fun x : ℝ
=> (x:ℂ)^(-(2*N:ℤ)))`. -/
@[dlmf 12.14.E20, dlmf 12.14.E21, dlmf 12.14.E23]
theorem pcfWS_asymptotic (a : ℝ) (N : ℕ) :
    (fun x : ℝ => pcfWS a x-∑ r ∈ Finset.range N, (-I)^r*pcfWCoeff a r/(2^r*(r.factorial:ℂ)*(x:ℂ)^(2*r))) =O[atTop] (fun x : ℝ => (x:ℂ)^(-(2*N:ℤ))) := by
  have hT : Tendsto (fun x : ℝ => (Real.log x : ℂ)) atTop (pcfSect_logWedge 0 0) := by
    refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr
      (Eventually.of_forall fun x => by simp)⟩
    refine tendsto_id.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [Real.exp_log hx]
  have hS := (pcfSect_tendsto_exp_logWedge (δ := π/4) (by positivity) (-(π/4)) (lo := 0) (hi := 0)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).comp hT
  have h := (pcfSect_U_sector (I * a) (δ := π/4) (by positivity) N).comp_tendsto hS
  refine IsBigO.trans (h.congr' ?_ EventuallyEq.rfl) ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply]
    rw [pcfSect_pcfWS_eq a hx]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    have hsq : (exp ((Real.log x : ℂ) + ((-(π/4) : ℝ) : ℂ) * I)) ^ 2 = -I * (x : ℂ) ^ 2 := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hx, mul_pow,
        show ((-(π/4) : ℝ) : ℂ) * I = -π * I / 4 by push_cast; ring, exp_neg_pi_I_quarter_sq]
      ring
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hII : (-I) ^ r * (-I) ^ r = (-1) ^ r := by rw [← mul_pow]; simp
    have hf : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
    rw [pcfSect_uTerm, hsq, pcfWCoeff, mul_pow, mul_pow, ← pow_mul, ← hII]
    have hI : (-I) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)
    field_simp
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply, norm_zpow, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx]
    simp [Real.exp_log hx]

/-- The modulus of the normalized complex pair formed by `W(a,x)` and `W(a,-x)`. -/
@[dlmf 12.14.E37]
def pcfWF (a x : ℝ) : ℝ :=
  ‖1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)‖

/-- The principal argument of the normalized complex Weber solution pair used to define its
real-axis phase. -/
@[dlmf 12.14.E37]
def pcfWTheta (a x : ℝ) : ℝ :=
  arg ((1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)))

/-- Estimate under the stated parameter and domain assumptions: `0 < pcfWF a x ∧ 1/Real.sqrt
(pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)=(pcfWF a x*exp (I*pcfWTheta a x))`. -/
@[dlmf 12.14.E37]
theorem pcfWF_phase (a x : ℝ) :
    0 < pcfWF a x ∧ 1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)=(pcfWF a x*exp (I*pcfWTheta a x)) := by
  have hk := (pcfWK_recip a).1
  have hs : (Real.sqrt (pcfWK a) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hk).ne'
  have hne : 1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x) ≠ 0 := by
    rw [mul_assoc I]
    refine add_I_mul_ne_zero_of_real ?_ ?_ ?_
    · rw [map_mul, Complex.conj_eq_iff_im.mpr (pcfW_ofReal_im a x)]; simp
    · have := pcfW_ofReal_im a (-x); push_cast at this
      rw [map_mul, Complex.conj_eq_iff_im.mpr this, Complex.conj_ofReal]
    · rintro ⟨h1, h2⟩
      exact pcfW_one_ne a x (by simpa [hs] using h1) (by simpa [hs] using h2)
  refine ⟨norm_pos_iff.mpr hne, ?_⟩
  have h := norm_mul_exp_arg_mul_I (1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x))
  rw [mul_comm ((arg _ : ℝ) : ℂ) I] at h
  exact h.symm

/-- The modulus of the normalized pair of derivatives of `W(a,x)` and `W(a,-x)`. -/
@[dlmf 12.14.E38]
def pcfWG (a x : ℝ) : ℝ :=
  ‖1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)‖

/-- The principal argument of the negated normalized derivative pair in the Weber modulus-phase
representation. -/
@[dlmf 12.14.E38]
def pcfWPsi (a x : ℝ) : ℝ :=
  arg (-(1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)))

/-- Estimate under the stated parameter and domain assumptions: `0 < pcfWG a x ∧ 1/Real.sqrt
(pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)=-(pcfWG a x*exp
(I*pcfWPsi a x))`. -/
@[dlmf 12.14.E38]
theorem pcfWG_phase (a x : ℝ) :
    0 < pcfWG a x ∧ 1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)=-(pcfWG a x*exp (I*pcfWPsi a x)) := by
  have hk := (pcfWK_recip a).1
  have hs : (Real.sqrt (pcfWK a) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hk).ne'
  have hne : 1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x) ≠ 0 := by
    rw [mul_assoc I, deriv_pcfW]
    refine add_I_mul_ne_zero_of_real ?_ ?_ ?_
    · rw [map_mul, conj_pcfWDeriv_ofReal]; simp
    · have := conj_pcfWDeriv_ofReal a (-x); push_cast at this
      rw [map_mul, this, Complex.conj_ofReal]
    · rintro ⟨h1, h2⟩
      exact pcfWDeriv_one_ne a x (by simpa [hs] using h1) (by simpa [hs] using h2)
  refine ⟨norm_pos_iff.mpr hne, ?_⟩
  have h := norm_mul_exp_arg_mul_I (-(1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)))
  rw [mul_comm ((arg _ : ℝ) : ℂ) I, norm_neg] at h
  rw [pcfWG, pcfWPsi, h, neg_neg]

end DLMF.Confluent

end
