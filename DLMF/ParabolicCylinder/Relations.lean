/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Repeated

/-!
# Parabolic cylinder special functions and addition formulas

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Bessel

/-- Identity under the stated parameter and domain assumptions: `pcfV (n+1/2) z=(Real.sqrt
(2/π):ℂ)*exp (z^2/4)*(-I)^n*Polynomial.aeval (I*z) (Polynomial.hermite n)`. -/
@[dlmf 12.7.E3]
theorem pcfV_nat_add_half (n : ℕ) (z : ℂ) :
    pcfV (n+1/2) z=(Real.sqrt (2/π):ℂ)*exp (z^2/4)*(-I)^n*Polynomial.aeval (I*z) (Polynomial.hermite n) := by
  rw [pcfV_eq_mul_I]
  rw [show (1/2:ℂ)-(n+1/2)=-(n:ℂ) by ring, Gamma_neg_nat_eq_zero]
  simp only [div_zero, zero_mul, zero_add]
  have hu := pcfD_nat n (I*z)
  simp only [pcfD] at hu
  rw [show -(n+1/2:ℂ)=-(n:ℂ)-1/2 by ring, hu]
  have he : exp (-I*π*((n+1/2:ℂ)/2-1/4))=(-I)^n := by
    rw [show -I*π*((n+1/2:ℂ)/2-1/4)=(n:ℂ)*(-π/2*I) by ring,
      Complex.exp_nat_mul, Complex.exp_neg_pi_div_two_mul_I]
  rw [he]
  have hz : -(I*z)^2/4=z^2/4 := by rw [mul_pow, I_sq]; ring
  rw [hz]
  ring

/-- Identity under the stated parameter and domain assumptions: `pcfV (-1/2) z=2/Real.sqrt π*exp
(z^2/4)*dawsonF (z/Real.sqrt 2)`. -/
@[dlmf 12.7.E4]
theorem pcfV_neg_half (z : ℂ) :
    pcfV (-1/2) z=2/Real.sqrt π*exp (z^2/4)*dawsonF (z/Real.sqrt 2) := by
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs0 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpp : (Real.sqrt π:ℂ)^2 = π := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have h2 : (2:ℂ)^((-1/2:ℂ)/2 + 3/4) = Real.sqrt 2 := by
    rw [show (-1/2:ℂ)/2 + 3/4 = 1/2 by norm_num, two_cpow_half]
  rw [pcfV, pcfVZero, pcfVDerivZero, pcfOdd_kummer_alternative, dawsonF_eq_kummerM, h2,
    show (1/4:ℂ) + (-1/2)/2 = 0 by norm_num, Complex.Gamma_zero, inv_zero, mul_zero, zero_mul,
    zero_add, show (1/4:ℂ) - (-1/2)/2 = 1/2 by norm_num, show (3/4:ℂ) + (-1/2)/2 = 1/2 by norm_num,
    show -(-1/2:ℂ)/2 + 3/4 = 1 by norm_num, Gamma_one_half_eq_sqrt, div_pow, hs]
  rw [← hpp]
  field_simp
  rw [hs]; ring

/-- Identity under the stated parameter and domain assumptions: `pcfU (n+1/2) z=(Real.sqrt
(π/2):ℂ)*(-1)^n/(n.factorial:ℂ)*exp (-z^2/4)*iteratedDeriv n (fun z : ℂ => exp (z^2/2)*erfc
(z/Real.sqrt 2)) z`. -/
@[dlmf 12.7.E6]
theorem pcfU_nat_add_half_deriv (n : ℕ) (z : ℂ) :
    pcfU (n+1/2) z=(Real.sqrt (π/2):ℂ)*(-1)^n/(n.factorial:ℂ)*exp (-z^2/4)*iteratedDeriv n (fun z : ℂ => exp (z^2/2)*erfc (z/Real.sqrt 2)) z := by
  have h := pcfU_iterated_deriv_9 (1/2) z n
  have hf : (fun w : ℂ => exp (1*w^2/4)*pcfU (1/2) w)=
      (fun w => (Real.sqrt (π/2):ℂ)*(exp (w^2/2)*erfc (w/Real.sqrt 2))) := by
    funext w
    rw [pcfU_half]
    have he : exp (w^2/4)*exp (w^2/4)=exp (w^2/2) := by rw [← Complex.exp_add]; congr 1; ring
    simp only [one_mul]
    linear_combination (Real.sqrt (π/2):ℂ)*erfc (w/Real.sqrt 2)*he
  rw [hf,iteratedDeriv_const_mul_field,show (1/2:ℂ)+1/2=1 by norm_num,
    poch_nat_one,show (1/2:ℂ)+n=n+1/2 by ring] at h
  simp only [one_mul] at h
  have he : exp (-z^2/4)*exp (z^2/4)=1 := by rw [← Complex.exp_add,show -z^2/4+z^2/4=(0:ℂ) by ring,Complex.exp_zero]
  have hn : ((-1:ℂ)^n)^2=1 := by rw [← pow_mul,mul_comm n 2,pow_mul]; simp
  have hn0 : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  calc
    pcfU (n+1/2) z = ((-1:ℂ)^n/(n.factorial:ℂ)*exp (-z^2/4))*
        ((-1:ℂ)^n*(n.factorial:ℂ)*exp (z^2/4)*pcfU (n+1/2) z) := by
      rw [show ((-1:ℂ)^n/(n.factorial:ℂ)*exp (-z^2/4))*
          ((-1:ℂ)^n*(n.factorial:ℂ)*exp (z^2/4)*pcfU (n+1/2) z)=
          ((-1:ℂ)^n)^2*(exp (-z^2/4)*exp (z^2/4))*pcfU (n+1/2) z by field_simp,
        he,hn]
      ring
    _ = _ := by rw [←h]; ring

/-- The repeated Gaussian tail integral `∫₀∞ tⁿ/n! exp (-(z+t)²/2) dt`; the index `-1` denotes the
Gaussian itself. -/
@[dlmf 12.7.E7]
def hhFunction (n : ℤ) (z : ℂ) : ℂ :=
  if n = -1 then exp (-z^2/2) else (∫ t : ℝ in Ioi 0, (t:ℂ)^n.toNat/(n.toNat.factorial:ℂ)*exp (-(z+t)^2/2))

/-- Identity under the stated parameter and domain assumptions: `pcfU (n+1/2) z=exp
(z^2/4)*hhFunction n z ∧ pcfU (n+1/2) z=Real.sqrt π*2^(((n:ℂ)-1)/2)*exp (z^2/4)*iteratedErfc n
(z/Real.sqrt 2)`. -/
@[dlmf 12.7.E7]
theorem pcfU_hh (n : ℤ) (hn : -1 ≤ n) (z : ℂ) :
    pcfU (n+1/2) z=exp (z^2/4)*hhFunction n z ∧ pcfU (n+1/2) z=Real.sqrt π*2^(((n:ℂ)-1)/2)*exp (z^2/4)*iteratedErfc n (z/Real.sqrt 2) := by
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs0 : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hπ0 : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  constructor
  · by_cases h : n= -1
    · subst n
      norm_num only [Int.cast_neg,Int.cast_one]
      rw [show -(1/2:ℂ)= -1/2 by ring,pcfU_neg_half,hhFunction,if_pos rfl,← Complex.exp_add]
      congr 1
      ring
    · have hn0 : 0≤n := by omega
      lift n to ℕ using hn0 with m
      rw [hhFunction,if_neg (by omega)]
      simp only [Int.toNat_natCast,Int.cast_natCast]
      change pcfU (m+1/2) z=exp (z^2/4)*gaussianProbabilityHh m z
      rw [gaussianProbabilityHh_eq_pcfU,←mul_assoc,←Complex.exp_add,show z^2/4 + -z^2/4=(0:ℂ) by ring]
      simp
  · rw [show ((n:ℂ)-1)/2=((n-1:ℤ):ℂ)/2 by push_cast; ring,two_cpow_int_half,
      iteratedErfc_eq_pcfU_int n hn]
    rw [show (Real.sqrt 2:ℂ)*(z/(Real.sqrt 2:ℂ))=z by field_simp]
    have hc : (Real.sqrt π:ℂ)*(Real.sqrt 2:ℂ)^(n-1)*(2/((Real.sqrt π:ℂ)*(Real.sqrt 2:ℂ)^(n+1)))=1 := by
      rw [show n+1=(n-1)+2 by ring,zpow_add₀ hs0,zpow_ofNat,hs]
      field_simp
    have he : exp (z^2/4)*exp (-(z/(Real.sqrt 2:ℂ))^2/2)=1 := by
      rw [←Complex.exp_add,div_pow,hs]
      convert Complex.exp_zero using 1 <;> ring
    symm
    calc
      _ = ((Real.sqrt π:ℂ)*(Real.sqrt 2:ℂ)^(n-1)*(2/((Real.sqrt π:ℂ)*(Real.sqrt 2:ℂ)^(n+1))))*
          (exp (z^2/4)*exp (-(z/(Real.sqrt 2:ℂ))^2/2))*pcfU ((n:ℂ)+1/2) z := by ring
      _ = _ := by rw [hc,he]; ring

/-- On the right half-plane, `log (z² / 2) = 2 log z - log 2`. -/
theorem log_sq_div_two {z : ℂ} (hz : 0 < z.re) : log (z^2/2) = 2*log z - Real.log 2 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have ha := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have hsq : log (z^2) = 2*log z := by
    have : z^2 = exp (2*log z) := by
      rw [show 2*log z = log z + log z by ring, Complex.exp_add, Complex.exp_log hz0, sq]
    rw [this, Complex.log_exp] <;> simp [Complex.log_im] <;> linarith [ha.1, ha.2, Real.pi_pos]
  rw [div_eq_inv_mul, show (2:ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.log_ofReal_mul (by norm_num) (pow_ne_zero 2 hz0), hsq, Real.log_inv]
  push_cast; ring

/-- Powers of `z² / 2` on the right half-plane. -/
theorem sq_div_two_cpow {z : ℂ} (hz : 0 < z.re) (s : ℂ) :
    (z^2/2)^s = exp (s*(2*log z - Real.log 2)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [Complex.cpow_def_of_ne_zero (div_ne_zero (pow_ne_zero 2 hz0) two_ne_zero),
    log_sq_div_two hz, mul_comm]

/-- Powers of two through the real logarithm. -/
theorem two_cpow_eq_exp (s : ℂ) : (2:ℂ)^s = exp (s * Real.log 2) := by
  rw [Complex.cpow_def_of_ne_zero two_ne_zero, mul_comm,
    show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]

/-- On the right half-plane, `z²/4` lies in the slit plane. -/
theorem sq_div_four_mem_slitPlane {z : ℂ} (hz : 0 < z.re) : z^2/4 ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hy : z.im = 0
  · left; simp [sq, hy]; positivity
  · right; simp only [sq, div_im, mul_im, mul_re]; norm_num
    intro h
    have : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hz.ne' h'
    · exact hy h'

/-- `(z/(2π))^{1/2} = z^{1/2}/√(2π)`. -/
theorem div_two_pi_cpow_half {z : ℂ} (hz : z ≠ 0) :
    (z/(2*π))^(1/2:ℂ) = z^(1/2:ℂ) / Real.sqrt (2*π) := by
  have hpos : (0:ℝ) < 2*π := by positivity
  have hsq : (Real.sqrt (2*π):ℂ) = exp (Real.log (2*π) * (1/2:ℂ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]; push_cast; ring_nf
  rw [show z/(2*π) = (((2*π)⁻¹:ℝ):ℂ) * z by push_cast; ring,
    Complex.cpow_def_of_ne_zero (mul_ne_zero (by simp [Real.pi_ne_zero]) hz),
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul (by positivity) hz, hsq, Real.log_inv,
    ← Complex.exp_sub]
  congr 1; push_cast; ring

/-- `U(0,z) = z^{1/2} K_{1/4}(z²/4)/√(2π)` on the right half-plane. -/
theorem pcfU_zero_eq_besselK {z : ℂ} (hz : 0 < z.re) :
    pcfU 0 z = z^(1/2:ℂ) / Real.sqrt (2*π) * besselK (1/4) (z^2/4) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hw := sq_div_four_mem_slitPlane hz
  have hK := kummerU_besselK (-1/4) (z^2/4) hw
  rw [show (-1/4:ℂ) + 1/2 = 0/2 + 1/4 by ring, show 2*(-1/4:ℂ)+1 = 1/2 by ring,
    show 2*(z^2/4) = z^2/2 by ring, show (-1/4:ℂ) = -(1/4) by ring, besselK_neg _ hw, neg_neg] at hK
  have hsq : (Real.sqrt (2*π):ℂ) = (Real.sqrt 2:ℂ) * Real.sqrt π := by
    rw [Real.sqrt_mul (by norm_num)]; push_cast; ring
  have h2 : (Real.sqrt 2:ℂ) = exp (Real.log 2 * (1/2:ℂ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num)]; push_cast; ring_nf
  have he : exp (-z^2/4) * exp (z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have key : (2:ℂ)^(-(1/4)-0/2:ℂ) * (z^2/2)^(1/4:ℂ) * Real.sqrt 2 = z^(1/2:ℂ) := by
    rw [sq_div_two_cpow hz, two_cpow_eq_exp, Complex.cpow_def_of_ne_zero hz0, h2,
      ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs0 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  rw [pcfU_eq_kummerU 0 hz, hK, ← key, hsq]
  calc _ = ((2:ℂ)^(-(1/4)-0/2:ℂ) * (z^2/2)^(1/4:ℂ) * Real.sqrt 2) * (exp (-z^2/4) * exp (z^2/4)) *
        besselK (1/4) (z^2/4) / (Real.sqrt 2 * Real.sqrt π) := by field_simp
    _ = _ := by rw [he]; ring

/-- `U'(0,z) = -z^{3/2} K_{3/4}(z²/4)/(2√(2π))` on the right half-plane. -/
theorem deriv_pcfU_zero_eq_besselK {z : ℂ} (hz : 0 < z.re) :
    deriv (pcfU 0) z = -(z * z^(1/2:ℂ)) / (2 * Real.sqrt (2*π)) * besselK (3/4) (z^2/4) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hw := sq_div_four_mem_slitPlane hz
  have hzs : z ∈ slitPlane := Or.inl hz
  have hev : pcfU 0 =ᶠ[nhds z] fun w => w^(1/2:ℂ) / Real.sqrt (2*π) * besselK (1/4) (w^2/4) :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
      fun w hw => pcfU_zero_eq_besselK hw
  have hd1 := (Complex.hasStrictDerivAt_cpow_const (c := (1/2:ℂ)) hzs).hasDerivAt
  have hd2 : HasDerivAt (fun w : ℂ => w^2/4) (z/2) z := by
    convert (hasDerivAt_pow 2 z).div_const 4 using 1; ring
  have hd := (hd1.div_const (Real.sqrt (2*π):ℂ)).mul ((hasDerivAt_besselK (1/4) hw).comp z hd2)
  have hd' : HasDerivAt (fun w : ℂ => w^(1/2:ℂ) / Real.sqrt (2*π) * besselK (1/4) (w^2/4)) _ z := hd
  rw [hev.deriv_eq, hd'.deriv, Function.comp_apply]
  have hrec := besselK_add_sub (1/4) hw
  rw [show (1/4:ℂ) - 1 = -(3/4) by ring, besselK_neg _ hw, show (1/4:ℂ) + 1 = 5/4 by ring] at hrec
  rw [show (1/4:ℂ) + 1 = 5/4 by ring, Complex.cpow_sub _ _ hz0, Complex.cpow_one]
  have hp0 : (Real.sqrt (2*π):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*π)).ne'
  field_simp at hrec ⊢
  linear_combination z^(1/2:ℂ) * hrec

/-- Principal branches in the right half-plane; continuation elsewhere inherits the logarithm of z squared. -/
@[dlmf 12.7.E8]
theorem pcfU_bessel_8 {z : ℂ} (hz : 0 < z.re) :
    pcfU (-2) z=z^(5/2:ℂ)/(4*Real.sqrt (2*π))*(2*besselK (1/4) (z^2/4)+3*besselK (3/4) (z^2/4)-besselK (5/4) (z^2/4)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hw := sq_div_four_mem_slitPlane hz
  have hrec := besselK_add_sub (1/4) hw
  rw [show (1/4:ℂ) - 1 = -(3/4) by ring, besselK_neg _ hw, show (1/4:ℂ) + 1 = 5/4 by ring] at hrec
  have h1 := pcfU_recurrence_sub 0 z
  rw [deriv_pcfU_zero_eq_besselK hz, pcfU_zero_eq_besselK hz, show (0:ℂ) - 1 = -1 by ring] at h1
  have h := pcfU_three_term (-1) z
  rw [show (-1:ℂ) - 1 = -2 by ring, show (-1:ℂ) + 1 = 0 by ring, pcfU_zero_eq_besselK hz] at h
  rw [show (5/2:ℂ) = 2 + 1/2 by norm_num, Complex.cpow_add _ _ hz0, Complex.cpow_two]
  have hp0 : (Real.sqrt (2*π):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*π)).ne'
  field_simp at hrec
  linear_combination -h + z*h1 - (z^(1/2:ℂ)/(4*Real.sqrt (2*π))) * hrec

/-- Principal branches in the right half-plane; continuation elsewhere inherits the logarithm of z squared. -/
@[dlmf 12.7.E9]
theorem pcfU_bessel_9 {z : ℂ} (hz : 0 < z.re) :
    pcfU (-1) z=z^(3/2:ℂ)/(2*Real.sqrt (2*π))*(besselK (1/4) (z^2/4)+besselK (3/4) (z^2/4)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h := pcfU_recurrence_sub 0 z
  rw [deriv_pcfU_zero_eq_besselK hz, pcfU_zero_eq_besselK hz, show (0:ℂ) - 1 = -1 by ring] at h
  rw [show (3/2:ℂ) = 1 + 1/2 by norm_num, Complex.cpow_add _ _ hz0, Complex.cpow_one]
  have hp0 : (Real.sqrt (2*π):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*π)).ne'
  field_simp at h ⊢
  linear_combination h

/-- Principal branches in the right half-plane; continuation elsewhere inherits the logarithm of z squared. -/
@[dlmf 12.7.E10]
theorem pcfU_bessel_10 {z : ℂ} (hz : 0 < z.re) :
    pcfU (0) z=(z/(2*π))^(1/2:ℂ)*besselK (1/4) (z^2/4) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [pcfU_zero_eq_besselK hz, div_two_pi_cpow_half hz0]

/-- Principal branches in the right half-plane; continuation elsewhere inherits the logarithm of z squared. -/
@[dlmf 12.7.E11]
theorem pcfU_bessel_11 {z : ℂ} (hz : 0 < z.re) :
    pcfU (1) z=z^(3/2:ℂ)/Real.sqrt (2*π)*(besselK (3/4) (z^2/4)-besselK (1/4) (z^2/4)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h := pcfU_recurrence_add 0 z
  rw [deriv_pcfU_zero_eq_besselK hz, pcfU_zero_eq_besselK hz, show (0:ℂ) + 1 = 1 by ring] at h
  rw [show (3/2:ℂ) = 1 + 1/2 by norm_num, Complex.cpow_add _ _ hz0, Complex.cpow_one]
  have hp0 : (Real.sqrt (2*π):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*π)).ne'
  field_simp at h ⊢
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `pcfU a z=2^(-3/4-a/2)*z*exp
(-z^2/4)*kummerU (a/2+3/4) (3/2) (z^2/2)`. -/
@[dlmf 12.7.E14]
theorem pcfU_kummerU_odd (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    pcfU a z=2^(-3/4-a/2)*z*exp (-z^2/4)*kummerU (a/2+3/4) (3/2) (z^2/2) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have key : (2:ℂ)^(-(1/4)-a/2) * (z^2/2)^(1-1/2:ℂ) = 2^(-3/4-a/2) * z := by
    rw [sq_div_two_cpow hz, two_cpow_eq_exp, two_cpow_eq_exp]
    conv_rhs => rw [← Complex.exp_log hz0]
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [pcfU_eq_kummerU a hz, kummerU_kummer_transform_all _ _ (div_ne_zero (pow_ne_zero 2 hz0) two_ne_zero),
    show a/2+1/4-1/2+1 = a/2+3/4 by ring, show (2:ℂ)-1/2 = 3/2 by norm_num]
  linear_combination (exp (-z^2/4) * kummerU (a/2+3/4) (3/2) (z^2/2)) * key

/-- Identity under the stated parameter and domain assumptions: `pcfU a
z=2^(-a/2)*z^(-1/2:ℂ)*whittakerW (-a/2) (1/4) (z^2/2) ∧ pcfU a
z=2^(-a/2)*z^(-1/2:ℂ)*whittakerW (-a/2) (-1/4) (z^2/2)`. -/
@[dlmf 12.7.E14]
theorem pcfU_whittaker (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    pcfU a z=2^(-a/2)*z^(-1/2:ℂ)*whittakerW (-a/2) (1/4) (z^2/2) ∧ pcfU a z=2^(-a/2)*z^(-1/2:ℂ)*whittakerW (-a/2) (-1/4) (z^2/2) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have key1 : (2:ℂ)^(-a/2) * z^(-1/2:ℂ) * (z^2/2)^(1/2 + 1/4:ℂ) = 2^(-3/4-a/2) * z := by
    rw [sq_div_two_cpow hz, two_cpow_eq_exp, two_cpow_eq_exp, Complex.cpow_def_of_ne_zero hz0]
    conv_rhs => rw [← Complex.exp_log hz0]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have key2 : (2:ℂ)^(-a/2) * z^(-1/2:ℂ) * (z^2/2)^(1/2 + -1/4:ℂ) = 2^(-(1/4)-a/2) := by
    rw [sq_div_two_cpow hz, two_cpow_eq_exp, two_cpow_eq_exp, Complex.cpow_def_of_ne_zero hz0]
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  constructor
  · rw [pcfU_kummerU_odd a hz, whittakerW, show (1:ℂ)/2 + 1/4 - -a/2 = a/2+3/4 by ring,
      show (1:ℂ) + 2*(1/4) = 3/2 by ring, show -(z^2/2)/2 = -z^2/4 by ring]
    linear_combination (-(exp (-z^2/4) * kummerU (a/2+3/4) (3/2) (z^2/2))) * key1
  · rw [pcfU_eq_kummerU a hz, whittakerW, show (1:ℂ)/2 + -1/4 - -a/2 = a/2+1/4 by ring,
      show (1:ℂ) + 2*(-1/4) = 1/2 by ring, show -(z^2/2)/2 = -z^2/4 by ring]
    linear_combination (-(exp (-z^2/4) * kummerU (a/2+1/4) (1/2) (z^2/2))) * key2

/-- The series with terms `(fun m : ℕ => exp (1*(x*y/2+y^2/4))*((-y)^m/(m.factorial:ℂ))*pcfU (a-m)
x)` converges to `(pcfU a (x+y))`. -/
@[dlmf 12.13.E1]
theorem pcfU_addition_1 (a x y : ℂ) :
    HasSum (fun m : ℕ => exp (1*(x*y/2+y^2/4))*((-y)^m/(m.factorial:ℂ))*pcfU (a-m) x) (pcfU a (x+y)) := by
  have hf : Differentiable ℂ (fun w => exp (-1*w^2/4) * pcfU a w) :=
    (by fun_prop : Differentiable ℂ (fun w : ℂ => exp (-1*w^2/4))).mul (pcfU_entire a)
  have h := (Complex.hasSum_taylorSeries_of_entire hf x (x+y)).mul_left (exp ((x+y)^2/4))
  simp only [smul_eq_mul, add_sub_cancel_left, pcfU_iterated_deriv_10] at h
  have he : exp ((x+y)^2/4) * exp (-1*(x+y)^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have he2 : exp (1*(x*y/2+y^2/4)) = exp ((x+y)^2/4) * exp (-1*x^2/4) := by
    rw [← Complex.exp_add]; ring_nf
  convert h using 1
  · funext m; rw [he2, neg_pow]; ring
  · rw [← mul_assoc, he, one_mul]

/-- The series with terms `(fun m : ℕ => exp (-1*(x*y/2+y^2/4))*((-1)^m*poch (a+1/2)
m*y^m/(m.factorial:ℂ))*pcfU (a+m) x)` converges to `(pcfU a (x+y))`. -/
@[dlmf 12.13.E2]
theorem pcfU_addition_2 (a x y : ℂ) :
    HasSum (fun m : ℕ => exp (-1*(x*y/2+y^2/4))*((-1)^m*poch (a+1/2) m*y^m/(m.factorial:ℂ))*pcfU (a+m) x) (pcfU a (x+y)) := by
  have hf : Differentiable ℂ (fun w => exp (1*w^2/4) * pcfU a w) :=
    (by fun_prop : Differentiable ℂ (fun w : ℂ => exp (1*w^2/4))).mul (pcfU_entire a)
  have h := (Complex.hasSum_taylorSeries_of_entire hf x (x+y)).mul_left (exp (-1*(x+y)^2/4))
  simp only [smul_eq_mul, add_sub_cancel_left, pcfU_iterated_deriv_9] at h
  have he : exp (-1*(x+y)^2/4) * exp (1*(x+y)^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have he2 : exp (-1*(x*y/2+y^2/4)) = exp (-1*(x+y)^2/4) * exp (1*x^2/4) := by
    rw [← Complex.exp_add]; ring_nf
  convert h using 1
  · funext m; rw [he2, show (1/2:ℂ)+a = a+1/2 by ring]; ring
  · rw [← mul_assoc, he, one_mul]

/-- The series with terms `(fun m : ℕ => exp (1*(x*y/2+y^2/4))*((-1)^m*poch (1/2-a)
m*y^m/(m.factorial:ℂ))*pcfV (a-m) x)` converges to `(pcfV a (x+y))`. -/
@[dlmf 12.13.E3]
theorem pcfV_addition_3 (a x y : ℂ) :
    HasSum (fun m : ℕ => exp (1*(x*y/2+y^2/4))*((-1)^m*poch (1/2-a) m*y^m/(m.factorial:ℂ))*pcfV (a-m) x) (pcfV a (x+y)) := by
  have hf : Differentiable ℂ (fun w => exp (-1*w^2/4) * pcfV a w) :=
    (by fun_prop : Differentiable ℂ (fun w : ℂ => exp (-1*w^2/4))).mul (pcfV_entire a)
  have h := (Complex.hasSum_taylorSeries_of_entire hf x (x+y)).mul_left (exp ((x+y)^2/4))
  simp only [smul_eq_mul, add_sub_cancel_left, pcfV_iterated_deriv_12] at h
  have he : exp ((x+y)^2/4) * exp (-1*(x+y)^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have he2 : exp (1*(x*y/2+y^2/4)) = exp ((x+y)^2/4) * exp (-1*x^2/4) := by
    rw [← Complex.exp_add]; ring_nf
  convert h using 1
  · funext m; rw [he2]; ring
  · rw [← mul_assoc, he, one_mul]

/-- The series with terms `(fun m : ℕ => exp (-1*(x*y/2+y^2/4))*(y^m/(m.factorial:ℂ))*pcfV (a+m)
x)` converges to `(pcfV a (x+y))`. -/
@[dlmf 12.13.E4]
theorem pcfV_addition_4 (a x y : ℂ) :
    HasSum (fun m : ℕ => exp (-1*(x*y/2+y^2/4))*(y^m/(m.factorial:ℂ))*pcfV (a+m) x) (pcfV a (x+y)) := by
  have hf : Differentiable ℂ (fun w => exp (1*w^2/4) * pcfV a w) :=
    (by fun_prop : Differentiable ℂ (fun w : ℂ => exp (1*w^2/4))).mul (pcfV_entire a)
  have h := (Complex.hasSum_taylorSeries_of_entire hf x (x+y)).mul_left (exp (-1*(x+y)^2/4))
  simp only [smul_eq_mul, add_sub_cancel_left, pcfV_iterated_deriv_11] at h
  have he : exp (-1*(x+y)^2/4) * exp (1*(x+y)^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have he2 : exp (-1*(x*y/2+y^2/4)) = exp (-1*(x+y)^2/4) * exp (1*x^2/4) := by
    rw [← Complex.exp_add]; ring_nf
  convert h using 1
  · funext m; rw [he2]; ring
  · rw [← mul_assoc, he, one_mul]

/-- The series with terms `(fun m : ℕ => exp ((x*Real.sin t-y*Real.cos t)^2/4)*(-1)^m*poch (a+1/2)
m/(m.factorial:ℂ)*(Real.tan t:ℂ)^m*pcfU (m+a) x*pcfU (-m-1/2) y)` converges to `(pcfU a
(x*Real.cos t+y*Real.sin t))`. -/
@[dlmf 12.13.E5]
theorem pcfU_rotational_addition {a : ℂ} (ha : a.re ≤ -1/2) (x y : ℂ) {t : ℝ} (ht : 0 ≤ t) (htπ : t ≤ π/4) (hend : t = π/4 → |y.im| ≤ x.re) :
    HasSum (fun m : ℕ => exp ((x*Real.sin t-y*Real.cos t)^2/4)*(-1)^m*poch (a+1/2) m/(m.factorial:ℂ)*(Real.tan t:ℂ)^m*pcfU (m+a) x*pcfU (-m-1/2) y) (pcfU a (x*Real.cos t+y*Real.sin t)) := by
  sorry

/- DLMF 12.13.6 as printed fails at n = 0, z = 0: the left side is
√(π/2), the right side 1. It is intentionally not admitted. See
`DLMF111214Acquisition.md` for the checked counterexample and source status. -/

end DLMF.Confluent
