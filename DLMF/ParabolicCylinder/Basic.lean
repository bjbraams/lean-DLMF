/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.ParabolicCylinder
public import DLMF.Confluent.Coulomb

/-!
# Additional parabolic cylinder definitions and entire dependence

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat ComplexConjugate
namespace DLMF.Confluent

/-- The scalar quadratic-potential equation `f″(z) + (az²+bz+c)f(z) = 0`, written using totalized
iterated derivatives. -/
@[dlmf 12.2.E1]
def IsQuadraticCylinderSolution (a b c : ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z, iteratedDeriv 2 f z+(a*z^2+b*z+c)*f z=0

/-- The oscillatory Weber equation `f″(z) + (z²/4-a)f(z) = 0`, written using totalized iterated
derivatives. -/
@[dlmf 12.2.E3]
def IsOscillatoryCylinderSolution (a : ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z, iteratedDeriv 2 f z+(z^2/4-a)*f z=0

/-- Identity under the stated parameter and domain assumptions: `IsQuadraticCylinderSolution a b c
(fun z => f (s*(z+b/(2*a))))`. -/
@[dlmf 12.2.E1]
theorem quadraticCylinder_transform {a b c s : ℂ} (ha : a ≠ 0) (hs : s^4 = -4*a) (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf2 : Differentiable ℂ (deriv f)) (hode : ∀ z, iteratedDeriv 2 f z-(z^2/4+(b^2/(4*a)-c)/s^2)*f z=0) :
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
  have : deriv (deriv f) (s*(z+b/(2*a))) = ((s*(z+b/(2*a)))^2/4+(b^2/(4*a)-c)/s^2) * f (s*(z+b/(2*a))) := by
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

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv 2 (pcfD ν)
z+(ν+1/2-z^2/4)*pcfD ν z=0`. -/
@[dlmf 12.2.E4]
theorem pcfD_ode (ν z : ℂ) :
    iteratedDeriv 2 (pcfD ν) z+(ν+1/2-z^2/4)*pcfD ν z=0 := by
  unfold pcfD
  rw [show iteratedDeriv 2 (pcfU (-ν-1/2)) z = deriv (deriv (pcfU (-ν-1/2))) z by rw [show 2=1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one],
    deriv_deriv_pcfU]
  ring

/-- Entire dependence on the argument. -/
theorem pcfU_entire (a : ℂ) :
    Differentiable ℂ (pcfU a) := by
  intro z
  exact (hasDerivAt_pcfU a z).differentiableAt

/-- The even Kummer basis is entire in the cylinder parameter. -/
theorem differentiable_pcfEven_order (z : ℂ) :
    Differentiable ℂ (fun a => pcfEven a z) := by
  unfold pcfEven
  simp_rw [kummerM_eq_mul_regularizedHGFun half_ne_neg_nat]
  fun_prop

/-- The odd Kummer basis is entire in the cylinder parameter. -/
theorem differentiable_pcfOdd_order (z : ℂ) :
    Differentiable ℂ (fun a => pcfOdd a z) := by
  unfold pcfOdd
  simp_rw [kummerM_eq_mul_regularizedHGFun three_half_ne_neg_nat]
  fun_prop

/-- Entire dependence on the parameter. -/
theorem pcfU_entire_order (z : ℂ) :
    Differentiable ℂ (fun a => pcfU a z) := by
  have he := differentiable_pcfEven_order z
  have ho := differentiable_pcfOdd_order z
  have hG1 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG2 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG3 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG4 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  unfold pcfU
  fun_prop

/-- Powers of two commute with complex conjugation of the exponent. -/
theorem conj_two_cpow (w : ℂ) : conj ((2:ℂ) ^ w) = (2:ℂ) ^ (conj w) := by
  rw [Complex.cpow_conj _ _ (by rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]; exact Real.pi_ne_zero.symm),
    map_ofNat]

/-- The even Kummer basis commutes with complex conjugation. -/
theorem conj_pcfEven (a z : ℂ) : conj (pcfEven a z) = pcfEven (conj a) (conj z) := by
  simp [pcfEven, conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]

/-- The odd Kummer basis commutes with complex conjugation. -/
theorem conj_pcfOdd (a z : ℂ) : conj (pcfOdd a z) = pcfOdd (conj a) (conj z) := by
  simp [pcfOdd, conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]

/-- `U(a,z)` commutes with complex conjugation. -/
theorem conj_pcfU (a z : ℂ) : conj (pcfU a z) = pcfU (conj a) (conj z) := by
  simp [pcfU, conj_pcfEven, conj_pcfOdd, conj_two_cpow, ← Complex.Gamma_conj, map_div₀, map_ofNat]

/-- `V(a,z)` commutes with complex conjugation. -/
theorem conj_pcfV (a z : ℂ) : conj (pcfV a z) = pcfV (conj a) (conj z) := by
  simp [pcfV, pcfVZero, pcfVDerivZero, conj_pcfEven, conj_pcfOdd, conj_two_cpow,
    ← Complex.Gamma_conj, map_div₀, map_ofNat]

/-- Reality on real parameters and arguments. -/
theorem pcfU_real (a x : ℝ) :
    (pcfU a x).im=0 := by
  rw [← Complex.conj_eq_iff_im, conj_pcfU, Complex.conj_ofReal, Complex.conj_ofReal]

/-- Entire dependence on the argument. -/
theorem pcfV_entire (a : ℂ) :
    Differentiable ℂ (pcfV a) := by
  intro z
  exact (hasDerivAt_pcfV a z).differentiableAt

/-- Entire dependence on the parameter. -/
theorem pcfV_entire_order (z : ℂ) :
    Differentiable ℂ (fun a => pcfV a z) := by
  have he := differentiable_pcfEven_order z
  have ho := differentiable_pcfOdd_order z
  have hG1 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG2 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG3 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG4 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  unfold pcfV pcfVZero pcfVDerivZero
  fun_prop

/-- Reality on real parameters and arguments. -/
theorem pcfV_real (a x : ℝ) :
    (pcfV a x).im=0 := by
  rw [← Complex.conj_eq_iff_im, conj_pcfV, Complex.conj_ofReal, Complex.conj_ofReal]

/-- The barred U solution; meaningful only away from positive half-integral parameters, not complex conjugation. -/
@[dlmf 12.2.E21]
def pcfUBar (a z : ℂ) : ℂ :=
  Gamma (1/2-a)*pcfV a z

/-- The derivative of the Gamma-normalized second cylinder solution: `Γ(1/2-a) V′(a,z)`. -/
def pcfUBarDeriv (a z : ℂ) : ℂ :=
  Gamma (1/2-a)*pcfVDeriv a z

/-- The modulus of the complex pair `U(a,x) + i UBar(a,x)` on the real axis. -/
@[dlmf 12.2.E22]
def pcfF (a x : ℝ) : ℝ :=
  ‖pcfU a x+I*pcfUBar a x‖

/-- Principal phase representative; a continuous lift differs by integral multiples of two pi. -/
@[dlmf 12.2.E22]
def pcfTheta (a x : ℝ) : ℝ :=
  arg ((pcfU a x+I*pcfUBar a x))

/-- The derivative of the even Kummer basis commuteswith complex conjugation. -/
theorem conj_pcfEvenDeriv (a z : ℂ) : conj (pcfEvenDeriv a z) = pcfEvenDeriv (conj a) (conj z) := by
  simp [pcfEvenDeriv, conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]

/-- The derivative of the odd Kummer basis commutes with complex conjugation. -/
theorem conj_pcfOddDeriv (a z : ℂ) : conj (pcfOddDeriv a z) = pcfOddDeriv (conj a) (conj z) := by
  simp [pcfOddDeriv, conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]

/-- `U'(a,z)` commutes with complex conjugation. -/
theorem conj_pcfUDeriv (a z : ℂ) : conj (pcfUDeriv a z) = pcfUDeriv (conj a) (conj z) := by
  simp [pcfUDeriv, conj_pcfEvenDeriv, conj_pcfOddDeriv, conj_two_cpow, ← Complex.Gamma_conj,
    map_div₀, map_ofNat]

/-- `V'(a,z)` commutes with complex conjugation. -/
theorem conj_pcfVDeriv (a z : ℂ) : conj (pcfVDeriv a z) = pcfVDeriv (conj a) (conj z) := by
  simp [pcfVDeriv, pcfVZero, pcfVDerivZero, conj_pcfEvenDeriv, conj_pcfOddDeriv, conj_two_cpow,
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

/-- Estimate under the stated parameter and domain assumptions: `0 < pcfF a x ∧ pcfU a x+I*pcfUBar
a x=(pcfF a x*exp (I*pcfTheta a x))`. -/
@[dlmf 12.2.E22]
theorem pcfF_phase {a : ℝ} (ha : ∀ n : ℕ, a ≠ n+1/2) (x : ℝ) :
    0 < pcfF a x ∧ pcfU a x+I*pcfUBar a x=(pcfF a x*exp (I*pcfTheta a x)) := by
  have hΓ : Gamma (1/2 - (a:ℂ)) ≠ 0 := Complex.Gamma_ne_zero fun n h =>
    ha n (Complex.ofReal_injective (by push_cast; linear_combination -h))
  have hne : pcfU a x + I*pcfUBar a x ≠ 0 := by
    refine add_I_mul_ne_zero_of_real (by simp [conj_pcfU])
      (by simp only [pcfUBar, map_mul, conj_Gamma_half_sub_ofReal, conj_pcfV, Complex.conj_ofReal]) ?_
    rintro ⟨hu, hv⟩
    have hV : pcfV a x = 0 := (mul_eq_zero.mp hv).resolve_left hΓ
    have hW := pcfV_wronskian a x
    rw [hu, hV] at hW
    rw [zero_mul, mul_zero, sub_zero] at hW
    exact (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos two_pos Real.pi_pos)).ne') hW.symm
  refine ⟨norm_pos_iff.mpr hne, ?_⟩
  have h := norm_mul_exp_arg_mul_I (pcfU a x + I*pcfUBar a x)
  rw [mul_comm ((arg _ : ℝ) : ℂ) I] at h
  exact h.symm

/-- The modulus of the derivative pair `U′(a,x) + i UBar′(a,x)` on the real axis. -/
@[dlmf 12.2.E23]
def pcfG (a x : ℝ) : ℝ :=
  ‖pcfUDeriv a x+I*pcfUBarDeriv a x‖

/-- Principal phase representative; a continuous lift differs by integral multiples of two pi. -/
@[dlmf 12.2.E23]
def pcfPsi (a x : ℝ) : ℝ :=
  arg (-(pcfUDeriv a x+I*pcfUBarDeriv a x))

/-- Estimate under the stated parameter and domain assumptions: `0 < pcfG a x ∧ pcfUDeriv a
x+I*pcfUBarDeriv a x=-(pcfG a x*exp (I*pcfPsi a x))`. -/
@[dlmf 12.2.E23]
theorem pcfG_phase {a : ℝ} (ha : ∀ n : ℕ, a ≠ n+1/2) (x : ℝ) :
    0 < pcfG a x ∧ pcfUDeriv a x+I*pcfUBarDeriv a x=-(pcfG a x*exp (I*pcfPsi a x)) := by
  have hΓ : Gamma (1/2 - (a:ℂ)) ≠ 0 := Complex.Gamma_ne_zero fun n h =>
    ha n (Complex.ofReal_injective (by push_cast; linear_combination -h))
  have hne : pcfUDeriv a x + I*pcfUBarDeriv a x ≠ 0 := by
    refine add_I_mul_ne_zero_of_real (by simp [conj_pcfUDeriv])
      (by simp only [pcfUBarDeriv, map_mul, conj_Gamma_half_sub_ofReal, conj_pcfVDeriv, Complex.conj_ofReal]) ?_
    rintro ⟨hu, hv⟩
    have hV : pcfVDeriv a x = 0 := (mul_eq_zero.mp hv).resolve_left hΓ
    have hW := pcfV_wronskian a x
    rw [deriv_pcfV, deriv_pcfU, hu, hV] at hW
    rw [zero_mul, mul_zero, sub_zero] at hW
    exact (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos two_pos Real.pi_pos)).ne') hW.symm
  refine ⟨norm_pos_iff.mpr hne, ?_⟩
  have h := norm_mul_exp_arg_mul_I (-(pcfUDeriv a x + I*pcfUBarDeriv a x))
  rw [mul_comm ((arg _ : ℝ) : ℂ) I, norm_neg] at h
  rw [pcfG, pcfPsi, h, neg_neg]

/-- Identity under the stated parameter and domain assumptions: `(Real.sqrt (2*π):ℂ)*pcfU a
z=Gamma (1/2-a)*(exp (-(1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) ((1:ℂ)*I*z)+exp
((1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) (-(1:ℂ)*I*z))`. -/
@[dlmf 12.2.E18]
theorem pcfU_rotated_connection_pos {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1/2) (z : ℂ) :
    (Real.sqrt (2*π):ℂ)*pcfU a z=Gamma (1/2-a)*(exp (-(1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) ((1:ℂ)*I*z)+exp ((1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) (-(1:ℂ)*I*z)) := by
  have ha' : ∀ n : ℕ, 1/2 + -a ≠ -n := fun n h => ha n (by linear_combination -h)
  have h := pcfU_connection_mul_I ha' (-I*z)
  rw [neg_neg, show I*(-I*z) = z by rw [← mul_assoc, mul_neg, I_mul_I]; ring, show (1/2 + -a) = 1/2-a by ring,
    show -I*π*(-a/2-1/4) = (1:ℂ)*I*π*(a/2+1/4) by ring, show I*π*(-a/2-1/4) = -(1:ℂ)*I*π*(a/2+1/4) by ring,
    show -(-I*z) = (1:ℂ)*I*z by ring, show -I*z = -(1:ℂ)*I*z by ring] at h
  rw [h, add_comm]

/-- Identity under the stated parameter and domain assumptions: `pcfU a z=(1:ℂ)*I*exp
((1:ℂ)*I*π*a)*pcfU a (-z)+(Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp ((1:ℂ)*I*π*(a/2-1/4))*pcfU
(-a) ((1:ℂ)*I*z)`. -/
@[dlmf 12.2.E19]
theorem pcfU_rotated_connection_entire_pos (a z : ℂ) :
    pcfU a z=(1:ℂ)*I*exp ((1:ℂ)*I*π*a)*pcfU a (-z)+(Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp ((1:ℂ)*I*π*(a/2-1/4))*pcfU (-a) ((1:ℂ)*I*z) := by
  by_cases hp : ∃ n : ℕ, 1/2 + a = -n
  · obtain ⟨n, hn⟩ := hp
    have ha : a = -n - 1/2 := by linear_combination hn
    rw [hn, Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul, zero_mul, add_zero, ha,
      pcfU_neg_nat_sub_half_neg, ← mul_assoc]
    have : (1:ℂ)*I*exp ((1:ℂ)*I*π*(-n-1/2)) * (-1)^n = 1 := by
      rw [show (1:ℂ)*I*π*(-n-1/2) = n * (-(π*I)) + (-(π/2))*I by ring, Complex.exp_add,
        Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I, Complex.exp_mul_I,
        Complex.cos_neg, Complex.sin_neg]
      simp
      rw [show -(I*((-1)^n*I)*(-1)^n) = -(I*I)*((-1:ℂ)^n*(-1)^n) by ring, ← mul_pow]; norm_num
    rw [this, one_mul]
  · push Not at hp
    have hΓ := Complex.Gamma_ne_zero hp
    have h := pcfU_connection_mul_I hp z
    have h2 : exp (I*π*(a/2-1/4)) ^ 2 = -I*exp (I*π*a) := by
      rw [sq, ← Complex.exp_add, show I*π*(a/2-1/4) + I*π*(a/2-1/4) = I*π*a + (-(π/2))*I by ring,
        Complex.exp_add, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      simp; ring
    have h3 : exp (I*π*(a/2-1/4)) * exp (-I*π*(a/2-1/4)) = 1 := by
      rw [← Complex.exp_add]; ring_nf; simp
    have hk : (Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp (I*π*(a/2-1/4))*pcfU (-a) (I*z) =
        exp (I*π*(a/2-1/4)) * (exp (-I * π * (a / 2 - 1 / 4)) * pcfU a z +
        exp (I * π * (a / 2 - 1 / 4)) * pcfU a (-z)) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hΓ]; linear_combination exp (I*π*(a/2-1/4)) * h
    simp only [one_mul]
    rw [hk]
    linear_combination (-(pcfU a (-z))) * h2 - pcfU a z * h3

/-- Identity under the stated parameter and domain assumptions: `(Real.sqrt (2*π):ℂ)*pcfU a
z=Gamma (1/2-a)*(exp (-(-1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) ((-1:ℂ)*I*z)+exp
((-1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) (-(-1:ℂ)*I*z))`. -/
@[dlmf 12.2.E18]
theorem pcfU_rotated_connection_neg {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1/2) (z : ℂ) :
    (Real.sqrt (2*π):ℂ)*pcfU a z=Gamma (1/2-a)*(exp (-(-1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) ((-1:ℂ)*I*z)+exp ((-1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) (-(-1:ℂ)*I*z)) := by
  have ha' : ∀ n : ℕ, 1/2 + -a ≠ -n := fun n h => ha n (by linear_combination -h)
  have h := pcfU_connection_mul_I ha' (-I*z)
  rw [neg_neg, show I*(-I*z) = z by rw [← mul_assoc, mul_neg, I_mul_I]; ring, show (1/2 + -a) = 1/2-a by ring,
    show -I*π*(-a/2-1/4) = -(-1:ℂ)*I*π*(a/2+1/4) by ring, show I*π*(-a/2-1/4) = (-1:ℂ)*I*π*(a/2+1/4) by ring,
    show -(-I*z) = -(-1:ℂ)*I*z by ring, show -I*z = (-1:ℂ)*I*z by ring] at h
  exact h

/-- Identity under the stated parameter and domain assumptions: `pcfU a z=(-1:ℂ)*I*exp
((-1:ℂ)*I*π*a)*pcfU a (-z)+(Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp ((-1:ℂ)*I*π*(a/2-1/4))*pcfU
(-a) ((-1:ℂ)*I*z)`. -/
@[dlmf 12.2.E19]
theorem pcfU_rotated_connection_entire_neg (a z : ℂ) :
    pcfU a z=(-1:ℂ)*I*exp ((-1:ℂ)*I*π*a)*pcfU a (-z)+(Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp ((-1:ℂ)*I*π*(a/2-1/4))*pcfU (-a) ((-1:ℂ)*I*z) := by
  by_cases hp : ∃ n : ℕ, 1/2 + a = -n
  · obtain ⟨n, hn⟩ := hp
    have ha : a = -n - 1/2 := by linear_combination hn
    rw [hn, Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul, zero_mul, add_zero, ha,
      pcfU_neg_nat_sub_half_neg, ← mul_assoc]
    have : (-1:ℂ)*I*exp ((-1:ℂ)*I*π*(-n-1/2)) * (-1)^n = 1 := by
      rw [show (-1:ℂ)*I*π*(-n-1/2) = n * (π*I) + (π/2)*I by ring, Complex.exp_add,
        Complex.exp_nat_mul, Complex.exp_pi_mul_I, Complex.exp_mul_I]
      simp
      rw [show -(I*((-1)^n*I)*(-1)^n) = -(I*I)*((-1:ℂ)^n*(-1)^n) by ring, ← mul_pow]; norm_num
    rw [this, one_mul]
  · push Not at hp
    have hΓ := Complex.Gamma_ne_zero hp
    have h := pcfU_connection_mul_neg_I hp z
    have h2 : exp (-I*π*(a/2-1/4)) ^ 2 = I*exp (-I*π*a) := by
      rw [sq, ← Complex.exp_add, show -I*π*(a/2-1/4) + -I*π*(a/2-1/4) = -I*π*a + (π/2)*I by ring,
        Complex.exp_add, Complex.exp_mul_I]
      simp; ring
    have h3 : exp (-I*π*(a/2-1/4)) * exp (I*π*(a/2-1/4)) = 1 := by
      rw [← Complex.exp_add]; ring_nf; simp
    have hk : (Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp (-I*π*(a/2-1/4))*pcfU (-a) (-I*z) =
        exp (-I*π*(a/2-1/4)) * (exp (-I * π * (a / 2 - 1 / 4)) * pcfU a (-z) +
        exp (I * π * (a / 2 - 1 / 4)) * pcfU a z) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hΓ]; linear_combination exp (-I*π*(a/2-1/4)) * h
    simp only [neg_mul, one_mul] at hk h2 h3 ⊢
    rw [hk]
    linear_combination (-(pcfU a (-z))) * h2 - pcfU a z * h3

/-- Identity under the stated parameter and domain assumptions: `pcfEven a z = exp (z^2/4)*kummerM
(-a/2+1/4) (1/2) (-z^2/2)`. -/
@[dlmf 12.7.E12]
theorem pcfEven_kummer_alternative (a z : ℂ) :
    pcfEven a z = exp (z^2/4)*kummerM (-a/2+1/4) (1/2) (-z^2/2) := by
  have hb : ∀ k : ℕ, (1/2:ℂ) ≠ -k := by
    intro k hk
    have h := congrArg Complex.re hk
    norm_num at h
    linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  rw [pcfEven, kummerM_kummer_transform hb, ← mul_assoc, ← Complex.exp_add]
  congr 2 <;> ring

/-- Identity under the stated parameter and domain assumptions: `pcfOdd a z = z*exp
(z^2/4)*kummerM (-a/2+3/4) (3/2) (-z^2/2)`. -/
@[dlmf 12.7.E13]
theorem pcfOdd_kummer_alternative (a z : ℂ) :
    pcfOdd a z = z*exp (z^2/4)*kummerM (-a/2+3/4) (3/2) (-z^2/2) := by
  have hb : ∀ k : ℕ, (3/2:ℂ) ≠ -k := by
    intro k hk
    have h := congrArg Complex.re hk
    norm_num at h
    linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  rw [pcfOdd, kummerM_kummer_transform hb]
  rw [show (3/2:ℂ)-(a/2+3/4) = -a/2+3/4 by ring,
    ← mul_assoc, mul_assoc z (exp (-z^2/4)) (exp (z^2/2)), ← Complex.exp_add]
  congr 2 <;> ring

/-- A product of scaled shifted factors is a scaled Pochhammer symbol. -/
theorem prod_range_mul_add_eq_poch (c α : ℂ) (k : ℕ) :
    ∏ r ∈ Finset.range k, (c * (α + r)) = c ^ k * poch α k := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih => rw [Finset.prod_range_succ, ih, poch_succ, pow_succ]; ring

/-- `(2k)! = 4^k k! (1/2)_k`. -/
theorem factorial_two_mul_eq_poch (k : ℕ) :
    (((2 * k)! : ℕ) : ℂ) = 4 ^ k * (k ! : ℂ) * poch (1 / 2) k := by
  have h := poch_two_mul (1 / 2) k
  rw [show (2:ℂ) * (1/2) = 1 by norm_num, show (1/2:ℂ) + 1/2 = 1 by norm_num,
    poch_nat_one, poch_nat_one] at h
  rw [h]; ring

/-- `(2k+1)! = 4^k k! (3/2)_k`. -/
theorem factorial_two_mul_add_one_eq_poch (k : ℕ) :
    (((2 * k + 1)! : ℕ) : ℂ) = 4 ^ k * (k ! : ℂ) * poch (3 / 2) k := by
  have h := poch_two_mul 1 k
  rw [show (2:ℂ) * 1 = 2 by norm_num, show (1:ℂ) + 1/2 = 3/2 by norm_num,
    poch_nat_two, poch_nat_one] at h
  rw [h]

/-- The series with terms `(fun k : ℕ => exp (-1*z^2/4)*(∏ r ∈ Finset.range k,
(a+1/2+2*r))*z^(2*k)/((2*k).factorial:ℂ))` converges to `(pcfEven a z)`. -/
@[dlmf 12.4.E3]
theorem pcfEven_series_3 (a z : ℂ) :
    HasSum (fun k : ℕ => exp (-1*z^2/4)*(∏ r ∈ Finset.range k, (a+1/2+2*r))*z^(2*k)/((2*k).factorial:ℂ)) (pcfEven a z) := by
  rw [pcfEven]
  convert (hasSum_kummerM half_ne_neg_nat (z^2/2)).mul_left (exp (-z^2/4)) using 2 with k
  have hp := poch_ne_zero_of_not_neg_nat half_ne_neg_nat k
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [show (fun r : ℕ => a+1/2+2*(r:ℂ)) = fun r : ℕ => 2 * ((a/2+1/4) + r) by funext r; ring,
    prod_range_mul_add_eq_poch, factorial_two_mul_eq_poch, kummerMCoeff, pow_mul, div_pow,
    show (4:ℂ)^k = 2^k*2^k by rw [← mul_pow]; norm_num]
  field_simp

/-- The series with terms `(fun k : ℕ => exp (1*z^2/4)*(∏ r ∈ Finset.range k,
(a-1/2-2*r))*z^(2*k)/((2*k).factorial:ℂ))` converges to `(pcfEven a z)`. -/
@[dlmf 12.4.E5]
theorem pcfEven_series_5 (a z : ℂ) :
    HasSum (fun k : ℕ => exp (1*z^2/4)*(∏ r ∈ Finset.range k, (a-1/2-2*r))*z^(2*k)/((2*k).factorial:ℂ)) (pcfEven a z) := by
  rw [pcfEven_kummer_alternative]
  convert (hasSum_kummerM half_ne_neg_nat (-z^2/2)).mul_left (exp (z^2/4)) using 2 with k
  have hp := poch_ne_zero_of_not_neg_nat half_ne_neg_nat k
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [show (fun r : ℕ => a-1/2-2*(r:ℂ)) = fun r : ℕ => (-2) * ((-a/2+1/4) + r) by funext r; ring,
    prod_range_mul_add_eq_poch, factorial_two_mul_eq_poch, kummerMCoeff, pow_mul, div_pow, neg_pow (z^2),
    show (4:ℂ)^k = 2^k*2^k by rw [← mul_pow]; norm_num, neg_pow (2:ℂ)]
  field_simp

/-- The series with terms `(fun k : ℕ => exp (-1*z^2/4)*(∏ r ∈ Finset.range k,
(a+3/2+2*r))*z^(2*k+1)/((2*k+1).factorial:ℂ))` converges to `(pcfOdd a z)`. -/
@[dlmf 12.4.E4]
theorem pcfOdd_series_4 (a z : ℂ) :
    HasSum (fun k : ℕ => exp (-1*z^2/4)*(∏ r ∈ Finset.range k, (a+3/2+2*r))*z^(2*k+1)/((2*k+1).factorial:ℂ)) (pcfOdd a z) := by
  rw [pcfOdd]
  convert (hasSum_kummerM three_half_ne_neg_nat (z^2/2)).mul_left (z * exp (-z^2/4)) using 2 with k
  have hp := poch_ne_zero_of_not_neg_nat three_half_ne_neg_nat k
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [show (fun r : ℕ => a+3/2+2*(r:ℂ)) = fun r : ℕ => 2 * ((a/2+3/4) + r) by funext r; ring,
    prod_range_mul_add_eq_poch, factorial_two_mul_add_one_eq_poch, kummerMCoeff, show z^(2*k+1) = z * (z^2)^k by rw [pow_succ, pow_mul]; ring, div_pow,
    show (4:ℂ)^k = 2^k*2^k by rw [← mul_pow]; norm_num]
  field_simp

/-- The series with terms `(fun k : ℕ => exp (1*z^2/4)*(∏ r ∈ Finset.range k,
(a-3/2-2*r))*z^(2*k+1)/((2*k+1).factorial:ℂ))` converges to `(pcfOdd a z)`. -/
@[dlmf 12.4.E6]
theorem pcfOdd_series_6 (a z : ℂ) :
    HasSum (fun k : ℕ => exp (1*z^2/4)*(∏ r ∈ Finset.range k, (a-3/2-2*r))*z^(2*k+1)/((2*k+1).factorial:ℂ)) (pcfOdd a z) := by
  rw [pcfOdd_kummer_alternative]
  convert (hasSum_kummerM three_half_ne_neg_nat (-z^2/2)).mul_left (z * exp (z^2/4)) using 2 with k
  have hp := poch_ne_zero_of_not_neg_nat three_half_ne_neg_nat k
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [show (fun r : ℕ => a-3/2-2*(r:ℂ)) = fun r : ℕ => (-2) * ((-a/2+3/4) + r) by funext r; ring,
    prod_range_mul_add_eq_poch, factorial_two_mul_add_one_eq_poch, kummerMCoeff, show z^(2*k+1) = z * (z^2)^k by rw [pow_succ, pow_mul]; ring, div_pow, neg_pow (z^2),
    show (4:ℂ)^k = 2^k*2^k by rw [← mul_pow]; norm_num, neg_pow (2:ℂ)]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `pcfU (1/2) z=(Real.sqrt
(π/2):ℂ)*exp (z^2/4)*erfc (z/Real.sqrt 2)`. -/
@[dlmf 12.7.E5]
theorem pcfU_half (z : ℂ) :
    pcfU (1/2) z=(Real.sqrt (π/2):ℂ)*exp (z^2/4)*erfc (z/Real.sqrt 2) := by
  have hs : (Real.sqrt 2:ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs0 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hc : (Real.sqrt (π/2):ℂ)=(Real.sqrt π:ℂ)/(Real.sqrt 2:ℂ) := by
    exact_mod_cast Real.sqrt_div Real.pi_pos.le 2
  have hE : pcfEven (1/2) z=exp (z^2/4) := by
    rw [pcfEven]
    norm_num
    rw [kummerM_self half_ne_neg_nat, ← Complex.exp_add]
    congr 1
    ring
  have hO : pcfOdd (1/2) z=z*exp (z^2/4)*kummerM (1/2) (3/2) (-(z/Real.sqrt 2)^2) := by
    rw [pcfOdd_kummer_alternative]
    norm_num
    have hz2 : -z^2/2=-(z/(Real.sqrt 2:ℂ))^2 := by rw [div_pow, hs]; ring
    simp [hz2]
  unfold pcfU
  norm_num
  rw [hE, hO, Gamma_one_half_eq_sqrt]
  have hp : (2:ℂ)^(-(1/2:ℂ))=(Real.sqrt 2:ℂ)⁻¹ := by
    rw [Complex.cpow_neg, two_cpow_half]
  rw [hp,erfc,erf]
  field_simp [hs0, hp0]
  ring_nf
  simp only [hs]
  ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv m (fun z : ℂ => exp
(1*z^2/4)*pcfU a z) z = (-1)^m*poch (1/2+a) m*exp (1*z^2/4)*pcfU (a+m) z`. -/
@[dlmf 12.8.E9]
theorem pcfU_iterated_deriv_9 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (1*z^2/4)*pcfU a z) z = (-1)^m*poch (1/2+a) m*exp (1*z^2/4)*pcfU (a+m) z := by
  induction m generalizing a with
  | zero => simp [poch_zero]
  | succ m ih =>
    have hd : deriv (fun w : ℂ => exp (1*w^2/4)*pcfU a w) =
        fun w => (-(a+1/2))*(exp (1*w^2/4)*pcfU (a+(1)) w) := by
      funext w
      have he : HasDerivAt (fun w : ℂ => exp (1*w^2/4))
          ((1*w/2)*exp (1*w^2/4)) w := by
        convert (((hasDerivAt_pow 2 w).const_mul (1:ℂ)).div_const 4).cexp using 1 <;> ring
      change deriv ((fun w : ℂ => exp (1*w^2/4))*pcfU a) w = _
      rw [(he.mul (hasDerivAt_pcfU a w)).deriv]
      have hr := pcfU_recurrence_add a w
      rw [deriv_pcfU] at hr
      linear_combination exp (1*w^2/4)*hr
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih, poch_succ_left]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    rw [show (1/2:ℂ)+(a+1)=(1/2+a)+1 by ring, show a+1+m=a+(m+1) by ring]
    ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv m (fun z : ℂ => exp
(-1*z^2/4)*pcfU a z) z = (-1)^m*exp (-1*z^2/4)*pcfU (a-m) z`. -/
@[dlmf 12.8.E10]
theorem pcfU_iterated_deriv_10 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (-1*z^2/4)*pcfU a z) z = (-1)^m*exp (-1*z^2/4)*pcfU (a-m) z := by
  induction m generalizing a with
  | zero => simp [poch_zero]
  | succ m ih =>
    have hd : deriv (fun w : ℂ => exp (-1*w^2/4)*pcfU a w) =
        fun w => (-1:ℂ)*(exp (-1*w^2/4)*pcfU (a+(-1)) w) := by
      funext w
      have he : HasDerivAt (fun w : ℂ => exp (-1*w^2/4))
          ((-1*w/2)*exp (-1*w^2/4)) w := by
        convert (((hasDerivAt_pow 2 w).const_mul (-1:ℂ)).div_const 4).cexp using 1 <;> ring
      change deriv ((fun w : ℂ => exp (-1*w^2/4))*pcfU a) w = _
      rw [(he.mul (hasDerivAt_pcfU a w)).deriv]
      have hr := pcfU_recurrence_sub a w
      rw [deriv_pcfU] at hr
      linear_combination exp (-1*w^2/4)*hr
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    rw [show a + (-1:ℂ) - m = a - (m+1) by ring]
    ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv m (fun z : ℂ => exp
(1*z^2/4)*pcfV a z) z = 1*exp (1*z^2/4)*pcfV (a+m) z`. -/
@[dlmf 12.8.E11]
theorem pcfV_iterated_deriv_11 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (1*z^2/4)*pcfV a z) z = 1*exp (1*z^2/4)*pcfV (a+m) z := by
  induction m generalizing a with
  | zero => simp [poch_zero]
  | succ m ih =>
    have hd : deriv (fun w : ℂ => exp (1*w^2/4)*pcfV a w) =
        fun w => (1:ℂ)*(exp (1*w^2/4)*pcfV (a+(1)) w) := by
      funext w
      have he : HasDerivAt (fun w : ℂ => exp (1*w^2/4))
          ((1*w/2)*exp (1*w^2/4)) w := by
        convert (((hasDerivAt_pow 2 w).const_mul (1:ℂ)).div_const 4).cexp using 1 <;> ring
      change deriv ((fun w : ℂ => exp (1*w^2/4))*pcfV a) w = _
      rw [(he.mul (hasDerivAt_pcfV a w)).deriv]
      have hr := pcfV_recurrence_add a w
      rw [deriv_pcfV] at hr
      linear_combination exp (1*w^2/4)*hr
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    rw [show a + (1:ℂ) + m = a + (m+1) by ring]
    ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv m (fun z : ℂ => exp
(-1*z^2/4)*pcfV a z) z = (-1)^m*poch (1/2-a) m*exp (-1*z^2/4)*pcfV (a-m) z`. -/
@[dlmf 12.8.E12]
theorem pcfV_iterated_deriv_12 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (-1*z^2/4)*pcfV a z) z = (-1)^m*poch (1/2-a) m*exp (-1*z^2/4)*pcfV (a-m) z := by
  induction m generalizing a with
  | zero => simp [poch_zero]
  | succ m ih =>
    have hd : deriv (fun w : ℂ => exp (-1*w^2/4)*pcfV a w) =
        fun w => (a-1/2)*(exp (-1*w^2/4)*pcfV (a+(-1)) w) := by
      funext w
      have he : HasDerivAt (fun w : ℂ => exp (-1*w^2/4))
          ((-1*w/2)*exp (-1*w^2/4)) w := by
        convert (((hasDerivAt_pow 2 w).const_mul (-1:ℂ)).div_const 4).cexp using 1 <;> ring
      change deriv ((fun w : ℂ => exp (-1*w^2/4))*pcfV a) w = _
      rw [(he.mul (hasDerivAt_pcfV a w)).deriv]
      have hr := pcfV_recurrence_sub a w
      rw [deriv_pcfV] at hr
      linear_combination exp (-1*w^2/4)*hr
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih, poch_succ_left]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    rw [show (1/2:ℂ)-(a+(-1))=(1/2-a)+1 by ring, show a+(-1)-m=a-(m+1) by ring]
    ring

/-- The barred solution satisfies the U recurrences on its parameter domain. -/
theorem pcfUBar_recurrences {a : ℂ} (ha : ∀ n : ℤ, a ≠ n+1/2) (z : ℂ) :
    z*pcfUBar a z-pcfUBar (a-1) z+(a+1/2)*pcfUBar (a+1) z=0 ∧ pcfUBarDeriv a z+z/2*pcfUBar a z+(a+1/2)*pcfUBar (a+1) z=0 ∧ pcfUBarDeriv a z-z/2*pcfUBar a z+pcfUBar (a-1) z=0 ∧ 2*pcfUBarDeriv a z+pcfUBar (a-1) z+(a+1/2)*pcfUBar (a+1) z=0 := by
  have h0 : (1/2:ℂ) - a ≠ 0 := fun h => ha 0 (by push_cast; linear_combination -h)
  have h1 : (-1/2:ℂ) - a ≠ 0 := fun h => ha (-1) (by push_cast; linear_combination -h)
  have gA : Gamma (1/2-a) = (-1/2-a) * Gamma (1/2-(a+1)) := by
    rw [show (1/2:ℂ)-a = (1/2-(a+1)) + 1 by ring, Complex.Gamma_add_one _ (by
      rw [show (1/2:ℂ)-(a+1) = -1/2-a by ring]; exact h1)]; ring
  have gB : Gamma (1/2-(a-1)) = (1/2-a) * Gamma (1/2-a) := by
    rw [show (1/2:ℂ)-(a-1) = (1/2-a) + 1 by ring, Complex.Gamma_add_one _ h0]
  have r1 := pcfV_three_term a z
  have r2 := pcfV_recurrence_add a z
  have r3 := pcfV_recurrence_sub a z
  rw [deriv_pcfV] at r2 r3
  simp only [pcfUBar, pcfUBarDeriv, gB]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination Gamma (1/2-a) * r1 + pcfV (a+1) z * gA
  · linear_combination Gamma (1/2-a) * r2 + pcfV (a+1) z * gA
  · linear_combination Gamma (1/2-a) * r3
  · linear_combination Gamma (1/2-a) * (r2 + r3) + pcfV (a+1) z * gA

/-- The generalized cylinder equation with nonzero exponent parameter `lam`, evaluated at the
specified argument. -/
@[dlmf 12.15.E1]
def IsGeneralizedCylinderSolution (ν lam : ℂ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  lam ≠ 0 ∧ iteratedDeriv 2 f z+(ν+1/lam-z^lam/lam^2)*f z=0

end DLMF.Confluent
