/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Basic

public import DLMF.Confluent.Coulomb
public import DLMF.Confluent.ParabolicCylinder

/-!
# Elementary properties of parabolic cylinder functions

This file develops the elementary properties of the parabolic cylinder functions defined in
`DLMF.ParabolicCylinder.Basic`: entire dependence on the argument and on the parameter,
behavior under complex conjugation and reality, the modulus–phase representations, the
rotated connection formulas, power series, the special value `a = 1/2` and derivative
formulas (DLMF §§12.2, 12.4, 12.7, 12.8).

## Main results

* `quadraticCylinder_transform`, `parabolicCylinderD_ode`: the cylinder equations DLMF 12.2.1 and
  12.2.4.
* `parabolicCylinderU_entire`, `parabolicCylinderU_entire_order`, `parabolicCylinderV_entire`,
  `parabolicCylinderV_entire_order`: entire dependence on the argument and on the parameter.
* `conj_parabolicCylinderU`, `conj_parabolicCylinderV`, `parabolicCylinderU_real`,
  `parabolicCylinderV_real`: complex conjugation and reality.
* `parabolicCylinderF_phase`, `parabolicCylinderG_phase`: the modulus–phase representations DLMF
  12.2.22–12.2.23.
* `parabolicCylinderU_rotated_connection_pos`, `parabolicCylinderU_rotated_connection_neg`: DLMF
  12.2.18.
* `parabolicCylinderU_rotated_connection_entire_pos`,
  `parabolicCylinderU_rotated_connection_entire_neg`: DLMF 12.2.19.
* `parabolicCylinderEven_kummer_alternative`, `parabolicCylinderOdd_kummer_alternative`: the
  Kummer-transformed forms of DLMF 12.7.12–12.7.13.
* `parabolicCylinderEven_series_3`, `parabolicCylinderOdd_series_4`,
  `parabolicCylinderEven_series_5`, `parabolicCylinderOdd_series_6`: the power series DLMF
  12.4.3–12.4.6.
* `parabolicCylinderU_half`: `U(1/2, z)` in terms of `erfc` (DLMF 12.7.5).
* `parabolicCylinderU_iterated_deriv_9`, `parabolicCylinderU_iterated_deriv_10`,
  `parabolicCylinderV_iterated_deriv_11`, `parabolicCylinderV_iterated_deriv_12`: the derivative
  formulas DLMF 12.8.9–12.8.12.
* `parabolicCylinderUBar_recurrences`: `Ū(a,z)` satisfies the recurrences of `U` on its parameter
  domain.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat ComplexConjugate
namespace DLMF.Confluent

/-- Identity under the stated parameter and domain assumptions: `IsQuadraticCylinderSolution a b c
(fun z => f (s*(z+b/(2*a))))`. -/
@[dlmf 12.2.E1]
theorem quadraticCylinder_transform {a b c s : ℂ} (ha : a ≠ 0) (hs : s^4 = -4*a) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf2 : Differentiable ℂ (deriv f))
    (hode : ∀ z, iteratedDeriv 2 f z-(z^2/4+(b^2/(4*a)-c)/s^2)*f z=0) :
    IsQuadraticCylinderSolution a b c (fun z => f (s*(z+b/(2*a)))) := by
  intro z
  have hs0 : s ≠ 0 := by
    rintro rfl; apply ha; linear_combination hs/4
  have hin : ∀ w : ℂ, HasDerivAt (fun z : ℂ => s*(z+b/(2*a))) s w := fun w => by
    simpa using ((hasDerivAt_id w).add_const (b/(2*a))).const_mul s
  have d1 : deriv (fun z => f (s*(z+b/(2*a)))) = fun z => deriv f (s*(z+b/(2*a))) * s := by
    funext w; exact ((hf _).hasDerivAt.comp w (hin w)).deriv
  have d2 : deriv (fun z => deriv f (s*(z+b/(2*a))) * s) z =
      deriv (deriv f) (s*(z+b/(2*a))) * s * s :=
    (((hf2 _).hasDerivAt.comp z (hin z)).mul_const s).deriv
  have e2 : ∀ g : ℂ → ℂ, iteratedDeriv 2 g = deriv (deriv g) := fun g => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [e2, d1, d2]
  have h := hode (s*(z+b/(2*a)))
  rw [e2] at h
  have : deriv (deriv f) (s*(z+b/(2*a))) = ((s*(z+b/(2*a)))^2/4+(b^2/(4*a)-c)/s^2) *
      f (s*(z+b/(2*a))) := by
    linear_combination h
  rw [this]
  simp only []
  generalize f (s*(z+b/(2*a))) = F
  set t := b/(2*a) with ht
  have hb : b = 2*a*t := by rw [ht]; field_simp
  have hq : b^2/(4*a) = a*t^2 := by rw [hb]; field_simp; ring
  have hq' : (a*t^2-c)/s^2*s*s = a*t^2-c := by field_simp
  rw [hq]
  rw [hb]
  linear_combination (z+t)^2*F/4 * hs + F * hq'

/-- Identity under the stated parameter and domain assumptions:
`iteratedDeriv 2 (parabolicCylinderD ν) z+(ν+1/2-z^2/4)*parabolicCylinderD ν z=0`. -/
@[dlmf 12.2.E4]
theorem parabolicCylinderD_ode (ν z : ℂ) :
    iteratedDeriv 2 (parabolicCylinderD ν) z+(ν+1/2-z^2/4)*parabolicCylinderD ν z=0 := by
  unfold parabolicCylinderD
  rw [show iteratedDeriv 2 (parabolicCylinderU (-ν-1/2)) z =
      deriv (deriv (parabolicCylinderU (-ν-1/2))) z by
                                        rw [show 2=1+1 by rfl, iteratedDeriv_succ,
                                                            iteratedDeriv_one],
    deriv_deriv_parabolicCylinderU]
  ring

/-- Entire dependence on the argument. -/
theorem parabolicCylinderU_entire (a : ℂ) :
    Differentiable ℂ (parabolicCylinderU a) := by
  intro z
  exact (hasDerivAt_parabolicCylinderU a z).differentiableAt

/-- The even Kummer basis is entire in the cylinder parameter. -/
theorem differentiable_parabolicCylinderEven_order (z : ℂ) :
    Differentiable ℂ (fun a => parabolicCylinderEven a z) := by
  unfold parabolicCylinderEven
  simp_rw [kummerM_eq_mul_regularizedHGFun Complex.one_div_two_ne_neg_natCast]
  fun_prop

/-- The odd Kummer basis is entire in the cylinder parameter. -/
theorem differentiable_parabolicCylinderOdd_order (z : ℂ) :
    Differentiable ℂ (fun a => parabolicCylinderOdd a z) := by
  unfold parabolicCylinderOdd
  simp_rw [kummerM_eq_mul_regularizedHGFun Complex.three_div_two_ne_neg_natCast]
  fun_prop

/-- Entire dependence on the parameter. -/
theorem parabolicCylinderU_entire_order (z : ℂ) :
    Differentiable ℂ (fun a => parabolicCylinderU a z) := by
  have he := differentiable_parabolicCylinderEven_order z
  have ho := differentiable_parabolicCylinderOdd_order z
  have hG1 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG2 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG3 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG4 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  unfold parabolicCylinderU
  fun_prop

/-- Powers of two commute with complex conjugation of the exponent. -/
theorem conj_two_cpow (w : ℂ) : conj ((2:ℂ) ^ w) = (2:ℂ) ^ (conj w) := by
  rw [Complex.cpow_conj _ _
      (by rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)];
          exact Real.pi_ne_zero.symm),
    map_ofNat]

/-- The even Kummer basis commutes with complex conjugation. -/
theorem conj_parabolicCylinderEven (a z : ℂ) : conj (parabolicCylinderEven a z) =
    parabolicCylinderEven (conj a) (conj z) := by
  simp [parabolicCylinderEven, conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]

/-- The odd Kummer basis commutes with complex conjugation. -/
theorem conj_parabolicCylinderOdd (a z : ℂ) : conj (parabolicCylinderOdd a z) =
    parabolicCylinderOdd (conj a) (conj z) := by
  simp [parabolicCylinderOdd, conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]

/-- `U(a,z)` commutes with complex conjugation. -/
theorem conj_parabolicCylinderU (a z : ℂ) : conj (parabolicCylinderU a z) =
    parabolicCylinderU (conj a) (conj z) := by
  simp [parabolicCylinderU, conj_parabolicCylinderEven, conj_parabolicCylinderOdd, conj_two_cpow,
      ← Complex.Gamma_conj, map_div₀, map_ofNat]

/-- `V(a,z)` commutes with complex conjugation. -/
theorem conj_parabolicCylinderV (a z : ℂ) : conj (parabolicCylinderV a z) =
    parabolicCylinderV (conj a) (conj z) := by
  simp [parabolicCylinderV, parabolicCylinderVZero, parabolicCylinderVDerivZero,
      conj_parabolicCylinderEven, conj_parabolicCylinderOdd, conj_two_cpow,
    ← Complex.Gamma_conj, map_div₀, map_ofNat]

/-- Reality on real parameters and arguments. -/
theorem parabolicCylinderU_real (a x : ℝ) :
    (parabolicCylinderU a x).im=0 := by
  rw [← Complex.conj_eq_iff_im, conj_parabolicCylinderU, Complex.conj_ofReal, Complex.conj_ofReal]

/-- Entire dependence on the argument. -/
theorem parabolicCylinderV_entire (a : ℂ) :
    Differentiable ℂ (parabolicCylinderV a) := by
  intro z
  exact (hasDerivAt_parabolicCylinderV a z).differentiableAt

/-- Entire dependence on the parameter. -/
theorem parabolicCylinderV_entire_order (z : ℂ) :
    Differentiable ℂ (fun a => parabolicCylinderV a z) := by
  have he := differentiable_parabolicCylinderEven_order z
  have ho := differentiable_parabolicCylinderOdd_order z
  have hG1 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG2 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG3 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG4 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  unfold parabolicCylinderV parabolicCylinderVZero parabolicCylinderVDerivZero
  fun_prop

/-- Reality on real parameters and arguments. -/
theorem parabolicCylinderV_real (a x : ℝ) :
    (parabolicCylinderV a x).im=0 := by
  rw [← Complex.conj_eq_iff_im, conj_parabolicCylinderV, Complex.conj_ofReal, Complex.conj_ofReal]

/-- The derivative of the even Kummer basis commuteswith complex conjugation. -/
theorem conj_parabolicCylinderEvenDeriv (a z : ℂ) : conj (parabolicCylinderEvenDeriv a z) =
    parabolicCylinderEvenDeriv (conj a) (conj z) := by
  simp [parabolicCylinderEvenDeriv, conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]

/-- The derivative of the odd Kummer basis commutes with complex conjugation. -/
theorem conj_parabolicCylinderOddDeriv (a z : ℂ) : conj (parabolicCylinderOddDeriv a z) =
    parabolicCylinderOddDeriv (conj a) (conj z) := by
  simp [parabolicCylinderOddDeriv, conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]

/-- `U'(a,z)` commutes with complex conjugation. -/
theorem conj_parabolicCylinderUDeriv (a z : ℂ) : conj (parabolicCylinderUDeriv a z) =
    parabolicCylinderUDeriv (conj a) (conj z) := by
  simp [parabolicCylinderUDeriv, conj_parabolicCylinderEvenDeriv, conj_parabolicCylinderOddDeriv,
      conj_two_cpow, ← Complex.Gamma_conj,
    map_div₀, map_ofNat]

/-- `V'(a,z)` commutes with complex conjugation. -/
theorem conj_parabolicCylinderVDeriv (a z : ℂ) : conj (parabolicCylinderVDeriv a z) =
    parabolicCylinderVDeriv (conj a) (conj z) := by
  simp [parabolicCylinderVDeriv, parabolicCylinderVZero, parabolicCylinderVDerivZero,
      conj_parabolicCylinderEvenDeriv, conj_parabolicCylinderOddDeriv, conj_two_cpow,
    ← Complex.Gamma_conj, map_div₀, map_ofNat]

/-- `u + i v` with real `u`, `v` vanishes only if `u = v = 0`. -/
theorem add_I_mul_ne_zero_of_real {u v : ℂ} (hu : conj u = u) (hv : conj v = v)
    (h : ¬ (u = 0 ∧ v = 0)) : u + I * v ≠ 0 := by
  rw [Complex.conj_eq_iff_im] at hu hv
  intro h0
  apply h
  have hr := congrArg Complex.re h0
  have hi := congrArg Complex.im h0
  simp [hu, hv] at hr hi
  exact ⟨Complex.ext hr hu, Complex.ext hi hv⟩

/-- `Γ(1/2 - a)` is real for real `a`. -/
theorem conj_Gamma_half_sub_ofReal (a : ℝ) : conj (Gamma (1/2 - a)) = Gamma (1/2 - a) := by
  rw [← Complex.Gamma_conj]; simp [map_ofNat]

/-- Estimate under the stated parameter and domain assumptions:
`0 < parabolicCylinderF a x ∧ parabolicCylinderU a x+I*parabolicCylinderUBar a x=(parabolicCylinderF
a x*exp (I*parabolicCylinderTheta a x))`. -/
@[dlmf 12.2.E22]
theorem parabolicCylinderF_phase {a : ℝ} (ha : ∀ n : ℕ, a ≠ n+1/2) (x : ℝ) :
    0 < parabolicCylinderF a x ∧
        parabolicCylinderU a x+I*parabolicCylinderUBar a
        x=(parabolicCylinderF a x*exp (I*parabolicCylinderTheta a x)) := by
  have hΓ : Gamma (1/2 - (a:ℂ)) ≠ 0 := Complex.Gamma_ne_zero fun n h =>
    ha n (Complex.ofReal_injective (by push_cast; linear_combination -h))
  have hne : parabolicCylinderU a x + I*parabolicCylinderUBar a x ≠ 0 := by
    refine add_I_mul_ne_zero_of_real (by simp [conj_parabolicCylinderU])
      (by simp only [parabolicCylinderUBar, map_mul, conj_Gamma_half_sub_ofReal,
            conj_parabolicCylinderV,
            Complex.conj_ofReal]) ?_
    rintro ⟨hu, hv⟩
    have hV : parabolicCylinderV a x = 0 := (mul_eq_zero.mp hv).resolve_left hΓ
    have hW := parabolicCylinderV_wronskian a x
    rw [hu, hV] at hW
    rw [zero_mul, mul_zero, sub_zero] at hW
    exact (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos two_pos Real.pi_pos)).ne') hW.symm
  refine ⟨norm_pos_iff.mpr hne, ?_⟩
  have h := norm_mul_exp_arg_mul_I (parabolicCylinderU a x + I*parabolicCylinderUBar a x)
  rw [mul_comm ((arg _ : ℝ) : ℂ) I] at h
  exact h.symm

/-- Estimate under the stated parameter and domain assumptions:
`0 < parabolicCylinderG a x ∧ parabolicCylinderUDeriv a x+I*parabolicCylinderUBarDeriv a
x=-(parabolicCylinderG a x*exp (I*parabolicCylinderPsi a x))`. -/
@[dlmf 12.2.E23]
theorem parabolicCylinderG_phase {a : ℝ} (ha : ∀ n : ℕ, a ≠ n+1/2) (x : ℝ) :
    0 < parabolicCylinderG a x ∧
        parabolicCylinderUDeriv a x+I*parabolicCylinderUBarDeriv a
        x=-(parabolicCylinderG a x*exp (I*parabolicCylinderPsi a x)) := by
  have hΓ : Gamma (1/2 - (a:ℂ)) ≠ 0 := Complex.Gamma_ne_zero fun n h =>
    ha n (Complex.ofReal_injective (by push_cast; linear_combination -h))
  have hne : parabolicCylinderUDeriv a x + I*parabolicCylinderUBarDeriv a x ≠ 0 := by
    refine add_I_mul_ne_zero_of_real (by simp [conj_parabolicCylinderUDeriv])
      (by simp only [parabolicCylinderUBarDeriv, map_mul, conj_Gamma_half_sub_ofReal,
            conj_parabolicCylinderVDeriv,
            Complex.conj_ofReal]) ?_
    rintro ⟨hu, hv⟩
    have hV : parabolicCylinderVDeriv a x = 0 := (mul_eq_zero.mp hv).resolve_left hΓ
    have hW := parabolicCylinderV_wronskian a x
    rw [deriv_parabolicCylinderV, deriv_parabolicCylinderU, hu, hV] at hW
    rw [zero_mul, mul_zero, sub_zero] at hW
    exact (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos two_pos Real.pi_pos)).ne') hW.symm
  refine ⟨norm_pos_iff.mpr hne, ?_⟩
  have h := norm_mul_exp_arg_mul_I
      (-(parabolicCylinderUDeriv a x + I*parabolicCylinderUBarDeriv a x))
  rw [mul_comm ((arg _ : ℝ) : ℂ) I, norm_neg] at h
  rw [parabolicCylinderG, parabolicCylinderPsi, h, neg_neg]

/-- Identity under the stated parameter and domain assumptions:
`(Real.sqrt (2*π):ℂ)*parabolicCylinderU a z=Gamma (1/2-a)*(exp
(-(1:ℂ)*I*π*(a/2+1/4))*parabolicCylinderU (-a) ((1:ℂ)*I*z)+exp
((1:ℂ)*I*π*(a/2+1/4))*parabolicCylinderU (-a) (-(1:ℂ)*I*z))`. -/
@[dlmf 12.2.E18]
theorem parabolicCylinderU_rotated_connection_pos {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1/2) (z : ℂ) :
    (Real.sqrt (2*π):ℂ)*parabolicCylinderU a z=Gamma
        (1/2-a)*(exp (-(1:ℂ)*I*π*(a/2+1/4))*parabolicCylinderU (-a) ((1:ℂ)*I*z)+exp
            ((1:ℂ)*I*π*(a/2+1/4))*parabolicCylinderU
        (-a) (-(1:ℂ)*I*z)) := by
  have ha' : ∀ n : ℕ, 1/2 + -a ≠ -n := fun n h => ha n (by linear_combination -h)
  have h := parabolicCylinderU_connection_mul_I ha' (-I*z)
  rw [neg_neg, show I*(-I*z) = z by rw [← mul_assoc, mul_neg, I_mul_I]; ring,
                                      show (1/2 + -a) = 1/2-a by ring,
    show -I*π*(-a/2-1/4) = (1:ℂ)*I*π*(a/2+1/4) by ring, show I*π*(-a/2-1/4) =
                                                    -(1:ℂ)*I*π*(a/2+1/4) by ring,
    show -(-I*z) = (1:ℂ)*I*z by ring, show -I*z = -(1:ℂ)*I*z by ring] at h
  rw [h, add_comm]

/-- Identity under the stated parameter and domain assumptions: `parabolicCylinderU a z=(1:ℂ)*I*exp
((1:ℂ)*I*π*a)*parabolicCylinderU a (-z)+(Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp
((1:ℂ)*I*π*(a/2-1/4))*parabolicCylinderU (-a) ((1:ℂ)*I*z)`. -/
@[dlmf 12.2.E19]
theorem parabolicCylinderU_rotated_connection_entire_pos (a z : ℂ) :
    parabolicCylinderU a z=(1:ℂ)*I*exp ((1:ℂ)*I*π*a)*parabolicCylinderU a
        (-z)+(Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp
        ((1:ℂ)*I*π*(a/2-1/4))*parabolicCylinderU (-a) ((1:ℂ)*I*z) := by
  by_cases hp : ∃ n : ℕ, 1/2 + a = -n
  · obtain ⟨n, hn⟩ := hp
    have ha : a = -n - 1/2 := by linear_combination hn
    rw [hn, Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul, zero_mul, add_zero, ha,
      parabolicCylinderU_neg_nat_sub_half_neg, ← mul_assoc]
    have : (1:ℂ)*I*exp ((1:ℂ)*I*π*(-n-1/2)) * (-1)^n = 1 := by
      rw [show (1:ℂ)*I*π*(-n-1/2) = n * (-(π*I)) + (-(π/2))*I by ring, Complex.exp_add,
        Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I, Complex.exp_mul_I,
        Complex.cos_neg, Complex.sin_neg]
      simp
      rw [show -(I*((-1)^n*I)*(-1)^n) = -(I*I)*((-1:ℂ)^n*(-1)^n) by ring, ← mul_pow]; norm_num
    rw [this, one_mul]
  · push Not at hp
    have hΓ := Complex.Gamma_ne_zero hp
    have h := parabolicCylinderU_connection_mul_I hp z
    have h2 : exp (I*π*(a/2-1/4)) ^ 2 = -I*exp (I*π*a) := by
      rw [sq, ← Complex.exp_add, show I*π*(a/2-1/4) + I*π*(a/2-1/4) = I*π*a + (-(π/2))*I by ring,
        Complex.exp_add, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      simp; ring
    have h3 : exp (I*π*(a/2-1/4)) * exp (-I*π*(a/2-1/4)) = 1 := by
      rw [← Complex.exp_add]; ring_nf; simp
    have hk : (Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp (I*π*(a/2-1/4))*parabolicCylinderU (-a) (I*z) =
        exp (I*π*(a/2-1/4)) * (exp (-I * π * (a / 2 - 1 / 4)) * parabolicCylinderU a z +
        exp (I * π * (a / 2 - 1 / 4)) * parabolicCylinderU a (-z)) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hΓ];
          linear_combination exp (I*π*(a/2-1/4)) * h
    simp only [one_mul]
    rw [hk]
    linear_combination (-(parabolicCylinderU a (-z))) * h2 - parabolicCylinderU a z * h3

/-- Identity under the stated parameter and domain assumptions:
`(Real.sqrt (2*π):ℂ)*parabolicCylinderU a z=Gamma (1/2-a)*(exp
(-(-1:ℂ)*I*π*(a/2+1/4))*parabolicCylinderU (-a) ((-1:ℂ)*I*z)+exp
((-1:ℂ)*I*π*(a/2+1/4))*parabolicCylinderU (-a) (-(-1:ℂ)*I*z))`. -/
@[dlmf 12.2.E18]
theorem parabolicCylinderU_rotated_connection_neg {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1/2) (z : ℂ) :
    (Real.sqrt (2*π):ℂ)*parabolicCylinderU a z=Gamma
        (1/2-a)*(exp (-(-1:ℂ)*I*π*(a/2+1/4))*parabolicCylinderU (-a) ((-1:ℂ)*I*z)+exp
            ((-1:ℂ)*I*π*(a/2+1/4))*parabolicCylinderU
        (-a) (-(-1:ℂ)*I*z)) := by
  have ha' : ∀ n : ℕ, 1/2 + -a ≠ -n := fun n h => ha n (by linear_combination -h)
  have h := parabolicCylinderU_connection_mul_I ha' (-I*z)
  rw [neg_neg, show I*(-I*z) = z by rw [← mul_assoc, mul_neg, I_mul_I]; ring,
                                      show (1/2 + -a) = 1/2-a by ring,
    show -I*π*(-a/2-1/4) = -(-1:ℂ)*I*π*(a/2+1/4) by ring, show I*π*(-a/2-1/4) =
                                                      (-1:ℂ)*I*π*(a/2+1/4) by ring,
    show -(-I*z) = -(-1:ℂ)*I*z by ring, show -I*z = (-1:ℂ)*I*z by ring] at h
  exact h

/-- Identity under the stated parameter and domain assumptions: `parabolicCylinderU a z=(-1:ℂ)*I*exp
((-1:ℂ)*I*π*a)*parabolicCylinderU a (-z)+(Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp
((-1:ℂ)*I*π*(a/2-1/4))*parabolicCylinderU (-a) ((-1:ℂ)*I*z)`. -/
@[dlmf 12.2.E19]
theorem parabolicCylinderU_rotated_connection_entire_neg (a z : ℂ) :
    parabolicCylinderU a z=(-1:ℂ)*I*exp ((-1:ℂ)*I*π*a)*parabolicCylinderU a
        (-z)+(Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp
        ((-1:ℂ)*I*π*(a/2-1/4))*parabolicCylinderU (-a) ((-1:ℂ)*I*z) := by
  by_cases hp : ∃ n : ℕ, 1/2 + a = -n
  · obtain ⟨n, hn⟩ := hp
    have ha : a = -n - 1/2 := by linear_combination hn
    rw [hn, Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul, zero_mul, add_zero, ha,
      parabolicCylinderU_neg_nat_sub_half_neg, ← mul_assoc]
    have : (-1:ℂ)*I*exp ((-1:ℂ)*I*π*(-n-1/2)) * (-1)^n = 1 := by
      rw [show (-1:ℂ)*I*π*(-n-1/2) = n * (π*I) + (π/2)*I by ring, Complex.exp_add,
        Complex.exp_nat_mul, Complex.exp_pi_mul_I, Complex.exp_mul_I]
      simp
      rw [show -(I*((-1)^n*I)*(-1)^n) = -(I*I)*((-1:ℂ)^n*(-1)^n) by ring, ← mul_pow]; norm_num
    rw [this, one_mul]
  · push Not at hp
    have hΓ := Complex.Gamma_ne_zero hp
    have h := parabolicCylinderU_connection_mul_neg_I hp z
    have h2 : exp (-I*π*(a/2-1/4)) ^ 2 = I*exp (-I*π*a) := by
      rw [sq, ← Complex.exp_add, show -I*π*(a/2-1/4) + -I*π*(a/2-1/4) = -I*π*a + (π/2)*I by ring,
        Complex.exp_add, Complex.exp_mul_I]
      simp; ring
    have h3 : exp (-I*π*(a/2-1/4)) * exp (I*π*(a/2-1/4)) = 1 := by
      rw [← Complex.exp_add]; ring_nf; simp
    have hk : (Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp
        (-I*π*(a/2-1/4))*parabolicCylinderU (-a) (-I*z) =
        exp (-I*π*(a/2-1/4)) * (exp (-I * π * (a / 2 - 1 / 4)) * parabolicCylinderU a (-z) +
        exp (I * π * (a / 2 - 1 / 4)) * parabolicCylinderU a z) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hΓ];
          linear_combination exp (-I*π*(a/2-1/4)) * h
    simp only [neg_mul, one_mul] at hk h2 h3 ⊢
    rw [hk]
    linear_combination (-(parabolicCylinderU a (-z))) * h2 - parabolicCylinderU a z * h3

/-- Identity under the stated parameter and domain assumptions:
`parabolicCylinderEven a z = exp (z^2/4)*kummerM (-a/2+1/4) (1/2) (-z^2/2)`. -/
@[dlmf 12.7.E12]
theorem parabolicCylinderEven_kummer_alternative (a z : ℂ) :
    parabolicCylinderEven a z = exp (z^2/4)*kummerM (-a/2+1/4) (1/2) (-z^2/2) := by
  have hb : ∀ k : ℕ, (1/2:ℂ) ≠ -k := by
    intro k hk
    have h := congrArg Complex.re hk
    norm_num at h
    linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  rw [parabolicCylinderEven, kummerM_kummer_transform hb, ← mul_assoc, ← Complex.exp_add]
  congr 2 <;> ring

/-- Identity under the stated parameter and domain assumptions: `parabolicCylinderOdd a z = z*exp
(z^2/4)*kummerM (-a/2+3/4) (3/2) (-z^2/2)`. -/
@[dlmf 12.7.E13]
theorem parabolicCylinderOdd_kummer_alternative (a z : ℂ) :
    parabolicCylinderOdd a z = z*exp (z^2/4)*kummerM (-a/2+3/4) (3/2) (-z^2/2) := by
  have hb : ∀ k : ℕ, (3/2:ℂ) ≠ -k := by
    intro k hk
    have h := congrArg Complex.re hk
    norm_num at h
    linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  rw [parabolicCylinderOdd, kummerM_kummer_transform hb]
  rw [show (3/2:ℂ)-(a/2+3/4) = -a/2+3/4 by ring,
    ← mul_assoc, mul_assoc z (exp (-z^2/4)) (exp (z^2/2)), ← Complex.exp_add]
  congr 2 <;> ring

/-- A product of scaled shifted factors is a scaled Pochhammer symbol. -/
theorem prod_range_mul_add_eq_pochhammer (c α : ℂ) (k : ℕ) :
    ∏ r ∈ Finset.range k, (c * (α + r)) = c ^ k * pochhammer α k := by
  induction k with
  | zero => simp [pochhammer_zero]
  | succ k ih => rw [Finset.prod_range_succ, ih, pochhammer_succ, pow_succ]; ring

/-- `(2k)! = 4^k k! (1/2)_k`. -/
theorem factorial_two_mul_eq_pochhammer (k : ℕ) :
    (((2 * k)! : ℕ) : ℂ) = 4 ^ k * (k ! : ℂ) * pochhammer (1 / 2) k := by
  have h := pochhammer_two_mul (1 / 2) k
  rw [show (2:ℂ) * (1/2) = 1 by norm_num, show (1/2:ℂ) + 1/2 = 1 by norm_num,
    pochhammer_nat_one, pochhammer_nat_one] at h
  rw [h]; ring

/-- `(2k+1)! = 4^k k! (3/2)_k`. -/
theorem factorial_two_mul_add_one_eq_pochhammer (k : ℕ) :
    (((2 * k + 1)! : ℕ) : ℂ) = 4 ^ k * (k ! : ℂ) * pochhammer (3 / 2) k := by
  have h := pochhammer_two_mul 1 k
  rw [show (2:ℂ) * 1 = 2 by norm_num, show (1:ℂ) + 1/2 = 3/2 by norm_num,
    pochhammer_nat_two, pochhammer_nat_one] at h
  rw [h]

/-- The series with terms `(fun k : ℕ => exp (-1*z^2/4)*(∏ r ∈ Finset.range k,
(a+1/2+2*r))*z^(2*k)/((2*k).factorial:ℂ))` converges to `(parabolicCylinderEven a z)`. -/
@[dlmf 12.4.E3]
theorem parabolicCylinderEven_series_3 (a z : ℂ) :
    HasSum (fun k : ℕ =>
        exp (-1*z^2/4)*(∏ r ∈ Finset.range k, (a+1/2+2*r))*z^(2*k)/((2*k).factorial:ℂ))
        (parabolicCylinderEven a z) := by
  rw [parabolicCylinderEven]
  convert (hasSum_kummerM Complex.one_div_two_ne_neg_natCast (z^2/2)).mul_left
      (exp (-z^2/4)) using 2 with k
  have hp := pochhammer_ne_zero_of_not_neg_nat Complex.one_div_two_ne_neg_natCast k
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [show (fun r : ℕ => a+1/2+2*(r:ℂ)) = fun r : ℕ => 2 * ((a/2+1/4) + r) by funext r; ring,
    prod_range_mul_add_eq_pochhammer, factorial_two_mul_eq_pochhammer, kummerMCoeff,
        pow_mul, div_pow,
    show (4:ℂ)^k = 2^k*2^k by rw [← mul_pow]; norm_num]
  field_simp

/-- The series with terms `(fun k : ℕ => exp (1*z^2/4)*(∏ r ∈ Finset.range k,
(a-1/2-2*r))*z^(2*k)/((2*k).factorial:ℂ))` converges to `(parabolicCylinderEven a z)`. -/
@[dlmf 12.4.E5]
theorem parabolicCylinderEven_series_5 (a z : ℂ) :
    HasSum (fun k : ℕ =>
        exp (1*z^2/4)*(∏ r ∈ Finset.range k, (a-1/2-2*r))*z^(2*k)/((2*k).factorial:ℂ))
        (parabolicCylinderEven a z) := by
  rw [parabolicCylinderEven_kummer_alternative]
  convert (hasSum_kummerM Complex.one_div_two_ne_neg_natCast (-z^2/2)).mul_left
      (exp (z^2/4)) using 2 with k
  have hp := pochhammer_ne_zero_of_not_neg_nat Complex.one_div_two_ne_neg_natCast k
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [show (fun r : ℕ => a-1/2-2*(r:ℂ)) = fun r : ℕ => (-2) * ((-a/2+1/4) + r) by funext r; ring,
    prod_range_mul_add_eq_pochhammer, factorial_two_mul_eq_pochhammer, kummerMCoeff, pow_mul,
        div_pow, neg_pow (z^2),
    show (4:ℂ)^k = 2^k*2^k by rw [← mul_pow]; norm_num, neg_pow (2:ℂ)]
  field_simp

/-- The series with terms `(fun k : ℕ => exp (-1*z^2/4)*(∏ r ∈ Finset.range k,
(a+3/2+2*r))*z^(2*k+1)/((2*k+1).factorial:ℂ))` converges to `(parabolicCylinderOdd a z)`. -/
@[dlmf 12.4.E4]
theorem parabolicCylinderOdd_series_4 (a z : ℂ) :
    HasSum (fun k : ℕ =>
        exp (-1*z^2/4)*(∏ r ∈ Finset.range k, (a+3/2+2*r))*z^(2*k+1)/((2*k+1).factorial:ℂ))
        (parabolicCylinderOdd a z) := by
  rw [parabolicCylinderOdd]
  convert (hasSum_kummerM Complex.three_div_two_ne_neg_natCast (z^2/2)).mul_left
      (z * exp (-z^2/4)) using 2 with k
  have hp := pochhammer_ne_zero_of_not_neg_nat Complex.three_div_two_ne_neg_natCast k
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [show (fun r : ℕ => a+3/2+2*(r:ℂ)) = fun r : ℕ => 2 * ((a/2+3/4) + r) by funext r; ring,
    prod_range_mul_add_eq_pochhammer, factorial_two_mul_add_one_eq_pochhammer, kummerMCoeff,
        show z^(2*k+1) =
        z * (z^2)^k by rw [pow_succ, pow_mul]; ring, div_pow,
    show (4:ℂ)^k = 2^k*2^k by rw [← mul_pow]; norm_num]
  field_simp

/-- The series with terms `(fun k : ℕ => exp (1*z^2/4)*(∏ r ∈ Finset.range k,
(a-3/2-2*r))*z^(2*k+1)/((2*k+1).factorial:ℂ))` converges to `(parabolicCylinderOdd a z)`. -/
@[dlmf 12.4.E6]
theorem parabolicCylinderOdd_series_6 (a z : ℂ) :
    HasSum (fun k : ℕ =>
        exp (1*z^2/4)*(∏ r ∈ Finset.range k, (a-3/2-2*r))*z^(2*k+1)/((2*k+1).factorial:ℂ))
        (parabolicCylinderOdd a z) := by
  rw [parabolicCylinderOdd_kummer_alternative]
  convert (hasSum_kummerM Complex.three_div_two_ne_neg_natCast (-z^2/2)).mul_left
      (z * exp (z^2/4)) using 2 with k
  have hp := pochhammer_ne_zero_of_not_neg_nat Complex.three_div_two_ne_neg_natCast k
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [show (fun r : ℕ => a-3/2-2*(r:ℂ)) = fun r : ℕ => (-2) * ((-a/2+3/4) + r) by funext r; ring,
    prod_range_mul_add_eq_pochhammer, factorial_two_mul_add_one_eq_pochhammer, kummerMCoeff,
        show z^(2*k+1) =
        z * (z^2)^k by rw [pow_succ, pow_mul]; ring, div_pow, neg_pow (z^2),
    show (4:ℂ)^k = 2^k*2^k by rw [← mul_pow]; norm_num, neg_pow (2:ℂ)]
  field_simp

/-- Identity under the stated parameter and domain assumptions:
`parabolicCylinderU (1/2) z=(Real.sqrt (π/2):ℂ)*exp (z^2/4)*erfc (z/Real.sqrt 2)`. -/
@[dlmf 12.7.E5]
theorem parabolicCylinderU_half (z : ℂ) :
    parabolicCylinderU (1/2) z=(Real.sqrt (π/2):ℂ)*exp (z^2/4)*erfc (z/Real.sqrt 2) := by
  have hs : (Real.sqrt 2:ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs0 : (Real.sqrt 2:ℂ) ≠ 0 := by
                                      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hc : (Real.sqrt (π/2):ℂ)=(Real.sqrt π:ℂ)/(Real.sqrt 2:ℂ) := by
    exact_mod_cast Real.sqrt_div Real.pi_pos.le 2
  have hE : parabolicCylinderEven (1/2) z=exp (z^2/4) := by
    rw [parabolicCylinderEven]
    norm_num
    rw [kummerM_self Complex.one_div_two_ne_neg_natCast, ← Complex.exp_add]
    congr 1
    ring
  have hO : parabolicCylinderOdd (1/2) z=z*exp (z^2/4)*kummerM (1/2) (3/2)
      (-(z/Real.sqrt 2)^2) := by
    rw [parabolicCylinderOdd_kummer_alternative]
    norm_num
    have hz2 : -z^2/2=-(z/(Real.sqrt 2:ℂ))^2 := by rw [div_pow, hs]; ring
    simp [hz2]
  unfold parabolicCylinderU
  norm_num
  rw [hE, hO, Complex.Gamma_one_half_eq_sqrt]
  have hp : (2:ℂ)^(-(1/2:ℂ))=(Real.sqrt 2:ℂ)⁻¹ := by
    rw [Complex.cpow_neg, two_cpow_half]
  rw [hp,erfc,erf]
  field_simp [hs0, hp0]
  ring_nf
  simp only [hs]
  ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv m (fun z : ℂ => exp
(1*z^2/4)*parabolicCylinderU a z) z = (-1)^m*pochhammer (1/2+a) m*exp (1*z^2/4)*parabolicCylinderU
(a+m) z`. -/
@[dlmf 12.8.E9]
theorem parabolicCylinderU_iterated_deriv_9 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (1*z^2/4)*parabolicCylinderU a z) z =
        (-1)^m*pochhammer (1/2+a) m*exp (1*z^2/4)*parabolicCylinderU (a+m) z := by
  induction m generalizing a with
  | zero => simp [pochhammer_zero]
  | succ m ih =>
    have hd : deriv (fun w : ℂ => exp (1*w^2/4)*parabolicCylinderU a w) =
        fun w => (-(a+1/2))*(exp (1*w^2/4)*parabolicCylinderU (a+(1)) w) := by
      funext w
      have he : HasDerivAt (fun w : ℂ => exp (1*w^2/4))
          ((1*w/2)*exp (1*w^2/4)) w := by
        convert (((hasDerivAt_pow 2 w).const_mul (1:ℂ)).div_const 4).cexp using 1 <;> ring
      change deriv ((fun w : ℂ => exp (1*w^2/4))*parabolicCylinderU a) w = _
      rw [(he.mul (hasDerivAt_parabolicCylinderU a w)).deriv]
      have hr := parabolicCylinderU_recurrence_add a w
      rw [deriv_parabolicCylinderU] at hr
      linear_combination exp (1*w^2/4)*hr
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih, pochhammer_succ_left]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    rw [show (1/2:ℂ)+(a+1)=(1/2+a)+1 by ring, show a+1+m=a+(m+1) by ring]
    ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv m (fun z : ℂ => exp
(-1*z^2/4)*parabolicCylinderU a z) z = (-1)^m*exp (-1*z^2/4)*parabolicCylinderU (a-m) z`. -/
@[dlmf 12.8.E10]
theorem parabolicCylinderU_iterated_deriv_10 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (-1*z^2/4)*parabolicCylinderU a z) z =
        (-1)^m*exp (-1*z^2/4)*parabolicCylinderU (a-m) z := by
  induction m generalizing a with
  | zero => simp [pochhammer_zero]
  | succ m ih =>
    have hd : deriv (fun w : ℂ => exp (-1*w^2/4)*parabolicCylinderU a w) =
        fun w => (-1:ℂ)*(exp (-1*w^2/4)*parabolicCylinderU (a+(-1)) w) := by
      funext w
      have he : HasDerivAt (fun w : ℂ => exp (-1*w^2/4))
          ((-1*w/2)*exp (-1*w^2/4)) w := by
        convert (((hasDerivAt_pow 2 w).const_mul (-1:ℂ)).div_const 4).cexp using 1 <;> ring
      change deriv ((fun w : ℂ => exp (-1*w^2/4))*parabolicCylinderU a) w = _
      rw [(he.mul (hasDerivAt_parabolicCylinderU a w)).deriv]
      have hr := parabolicCylinderU_recurrence_sub a w
      rw [deriv_parabolicCylinderU] at hr
      linear_combination exp (-1*w^2/4)*hr
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    rw [show a + (-1:ℂ) - m = a - (m+1) by ring]
    ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv m (fun z : ℂ => exp
(1*z^2/4)*parabolicCylinderV a z) z = 1*exp (1*z^2/4)*parabolicCylinderV (a+m) z`. -/
@[dlmf 12.8.E11]
theorem parabolicCylinderV_iterated_deriv_11 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (1*z^2/4)*parabolicCylinderV a z) z =
        1*exp (1*z^2/4)*parabolicCylinderV (a+m) z := by
  induction m generalizing a with
  | zero => simp [pochhammer_zero]
  | succ m ih =>
    have hd : deriv (fun w : ℂ => exp (1*w^2/4)*parabolicCylinderV a w) =
        fun w => (1:ℂ)*(exp (1*w^2/4)*parabolicCylinderV (a+(1)) w) := by
      funext w
      have he : HasDerivAt (fun w : ℂ => exp (1*w^2/4))
          ((1*w/2)*exp (1*w^2/4)) w := by
        convert (((hasDerivAt_pow 2 w).const_mul (1:ℂ)).div_const 4).cexp using 1 <;> ring
      change deriv ((fun w : ℂ => exp (1*w^2/4))*parabolicCylinderV a) w = _
      rw [(he.mul (hasDerivAt_parabolicCylinderV a w)).deriv]
      have hr := parabolicCylinderV_recurrence_add a w
      rw [deriv_parabolicCylinderV] at hr
      linear_combination exp (1*w^2/4)*hr
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    rw [show a + (1:ℂ) + m = a + (m+1) by ring]
    ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv m (fun z : ℂ => exp
(-1*z^2/4)*parabolicCylinderV a z) z = (-1)^m*pochhammer (1/2-a) m*exp (-1*z^2/4)*parabolicCylinderV
(a-m) z`. -/
@[dlmf 12.8.E12]
theorem parabolicCylinderV_iterated_deriv_12 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (-1*z^2/4)*parabolicCylinderV a z) z =
        (-1)^m*pochhammer (1/2-a) m*exp (-1*z^2/4)*parabolicCylinderV (a-m) z := by
  induction m generalizing a with
  | zero => simp [pochhammer_zero]
  | succ m ih =>
    have hd : deriv (fun w : ℂ => exp (-1*w^2/4)*parabolicCylinderV a w) =
        fun w => (a-1/2)*(exp (-1*w^2/4)*parabolicCylinderV (a+(-1)) w) := by
      funext w
      have he : HasDerivAt (fun w : ℂ => exp (-1*w^2/4))
          ((-1*w/2)*exp (-1*w^2/4)) w := by
        convert (((hasDerivAt_pow 2 w).const_mul (-1:ℂ)).div_const 4).cexp using 1 <;> ring
      change deriv ((fun w : ℂ => exp (-1*w^2/4))*parabolicCylinderV a) w = _
      rw [(he.mul (hasDerivAt_parabolicCylinderV a w)).deriv]
      have hr := parabolicCylinderV_recurrence_sub a w
      rw [deriv_parabolicCylinderV] at hr
      linear_combination exp (-1*w^2/4)*hr
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih, pochhammer_succ_left]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    rw [show (1/2:ℂ)-(a+(-1))=(1/2-a)+1 by ring, show a+(-1)-m=a-(m+1) by ring]
    ring

/-- The barred solution satisfies the U recurrences on its parameter domain. -/
theorem parabolicCylinderUBar_recurrences {a : ℂ} (ha : ∀ n : ℤ, a ≠ n+1/2) (z : ℂ) :
    z*parabolicCylinderUBar a z-parabolicCylinderUBar (a-1)
        z+(a+1/2)*parabolicCylinderUBar (a+1) z=0 ∧
        parabolicCylinderUBarDeriv a z+z/2*parabolicCylinderUBar a
            z+(a+1/2)*parabolicCylinderUBar (a+1) z=0 ∧
        parabolicCylinderUBarDeriv a z-z/2*parabolicCylinderUBar a
            z+parabolicCylinderUBar (a-1) z=0 ∧
        2*parabolicCylinderUBarDeriv a z+parabolicCylinderUBar (a-1) z+(a+1/2)*parabolicCylinderUBar
            (a+1) z=0 := by
  have h0 : (1/2:ℂ) - a ≠ 0 := fun h => ha 0 (by push_cast; linear_combination -h)
  have h1 : (-1/2:ℂ) - a ≠ 0 := fun h => ha (-1) (by push_cast; linear_combination -h)
  have gA : Gamma (1/2-a) = (-1/2-a) * Gamma (1/2-(a+1)) := by
    rw [show (1/2:ℂ)-a = (1/2-(a+1)) + 1 by ring, Complex.Gamma_add_one _ (by
      rw [show (1/2:ℂ)-(a+1) = -1/2-a by ring]; exact h1)]; ring
  have gB : Gamma (1/2-(a-1)) = (1/2-a) * Gamma (1/2-a) := by
    rw [show (1/2:ℂ)-(a-1) = (1/2-a) + 1 by ring, Complex.Gamma_add_one _ h0]
  have r1 := parabolicCylinderV_three_term a z
  have r2 := parabolicCylinderV_recurrence_add a z
  have r3 := parabolicCylinderV_recurrence_sub a z
  rw [deriv_parabolicCylinderV] at r2 r3
  simp only [parabolicCylinderUBar, parabolicCylinderUBarDeriv, gB]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination Gamma (1/2-a) * r1 + parabolicCylinderV (a+1) z * gA
  · linear_combination Gamma (1/2-a) * r2 + parabolicCylinderV (a+1) z * gA
  · linear_combination Gamma (1/2-a) * r3
  · linear_combination Gamma (1/2-a) * (r2 + r3) + parabolicCylinderV (a+1) z * gA

end DLMF.Confluent
