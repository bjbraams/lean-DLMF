/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Trigonometric
public import DLMF.Elementary.LogExpAnalysis
public import TauCeti.Analysis.SpecialFunctions.Artanh
public import DLMFMathlib.NumberTheory.BernoulliTaylor

/-!
# Hyperbolic and inverse hyperbolic functions (DLMF §§4.28–4.41)

This acquisition retains complex arguments, principal branches, the two sides of cuts,
convergence of series/products/continued fractions, exact algebraic tables, and prose results.
Upstream coverage is recorded separately in `DLMF.Elementary.MathlibCoverage`.

Reciprocals have Lean's totalized values at poles; every meromorphic identity requiring a
finite value has its pole exclusions stated. The inverse functions below choose one value on
each cut; the other cut value is represented by a one-sided limit. Multivalued inverses are
sets of solutions, with poles excluded from the inverse equations.

The inverse-sinh and mixed inverse-sinh/inverse-cosh sums and differences use paired sinh/cosh
equations to retain branch parity. These correct our full-set acquisition interpretation;
the printed DLMF branch formulas are not claimed to be false.
The former unrestricted full-set acquisition failed at critical parameters; explicit counterexamples
and complete compatible-branch characterizations are proved below using Mathlib log/exp calculus.

The Mathlib real inverse functions `Real.arsinh`, `Real.arcosh`, `Real.artanh` are reused for
real antiderivatives. TauCeti's real tanh/artanh additions and derivative declarations are
credited in the separate upstream coverage fragment; no upstream proofs are copied here.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory
open scoped Real Topology
namespace DLMF.Elementary

/-- The hyperbolic cosecant, totalized at its poles. -/
@[dlmf 4.28.E5]
def csch (z : ℂ) : ℂ := (Complex.sinh z)⁻¹
/-- The hyperbolic secant, totalized at its poles. -/
@[dlmf 4.28.E6]
def sech (z : ℂ) : ℂ := (Complex.cosh z)⁻¹
/-- The hyperbolic cotangent, totalized at its poles. -/
@[dlmf 4.28.E7]
def coth (z : ℂ) : ℂ := Complex.cosh z/Complex.sinh z
/-- The open principal domain of arcsinh (the imaginary rays beyond ±i are cut). -/
def arcsinhDomain : Set ℂ := {z | z.re ≠ 0 ∨ |z.im| < 1}
/-- The open principal domain of arccosh, with the real ray up to 1 removed. -/
def arccoshDomain : Set ℂ := {z | z.im ≠ 0 ∨ 1 < z.re}
/-- The open principal domain of arctanh (the real rays beyond ±1 are cut). -/
def arctanhDomain : Set ℂ := {z | z.im ≠ 0 ∨ |z.re| < 1}
/-- The open principal domain of arccsch, obtained by inversion of the arcsinh domain. -/
def arccschDomain : Set ℂ := {z | z ≠ 0 ∧ z⁻¹ ∈ arcsinhDomain}
/-- The open principal domain of arcsech, obtained by inversion of the arccosh domain. -/
def arcsechDomain : Set ℂ := {z | z ≠ 0 ∧ z⁻¹ ∈ arccoshDomain}
/-- The open principal domain of arccoth, with the segment [-1,1] removed. -/
def arccothDomain : Set ℂ := {z | z.im ≠ 0 ∨ 1 < |z.re|}
/-- Principal inverse sinh; cut-side statements below remove the tie at the square-root cut. -/
@[dlmf 4.37.E16]
def arcsinh (z : ℂ) : ℂ := Complex.log (Complex.sqrt (z^2+1)+z)
/-- Principal inverse cosh, with the square roots factored to preserve the negative half-plane. -/
def arccosh (z : ℂ) : ℂ := Complex.log (z+Complex.sqrt (z-1)*Complex.sqrt (z+1))
/-- Principal inverse tanh off its poles, with the principal logarithm's cut convention. -/
@[dlmf 4.37.E24]
def arctanh (z : ℂ) : ℂ := Complex.log ((1+z)/(1-z))/2
/-- Principal inverse hyperbolic cosecant. -/
@[dlmf 4.37.E7]
def arccsch (z : ℂ) : ℂ := arcsinh z⁻¹
/-- Principal inverse hyperbolic secant. -/
@[dlmf 4.37.E8]
def arcsech (z : ℂ) : ℂ := arccosh z⁻¹
/-- Principal inverse hyperbolic cotangent; the value at zero is a cut-side value. -/
def arccoth (z : ℂ) : ℂ := if z=0 then π*I/2 else arctanh z⁻¹
/-- All finite inverse-sinh values. -/
def arcsinhValues (z : ℂ) : Set ℂ := {w | Complex.sinh w=z}
/-- All finite inverse-cosh values. -/
def arccoshValues (z : ℂ) : Set ℂ := {w | Complex.cosh w=z}
/-- All finite inverse-tanh values; totalized pole values are excluded. -/
def arctanhValues (z : ℂ) : Set ℂ := {w | Complex.cosh w ≠ 0 ∧ Complex.tanh w=z}
/-- All finite inverse-csch values. -/
def arccschValues (z : ℂ) : Set ℂ := {w | Complex.sinh w ≠ 0 ∧ csch w=z}
/-- All finite inverse-sech values. -/
def arcsechValues (z : ℂ) : Set ℂ := {w | Complex.cosh w ≠ 0 ∧ sech w=z}
/-- All finite inverse-coth values. -/
def arccothValues (z : ℂ) : Set ℂ := {w | Complex.sinh w ≠ 0 ∧ coth w=z}
/-- Analytic logarithm normalized at the origin, used when the principal logarithm can wrap. -/
def HyperbolicNormalizedLog (U : Set ℂ) (f L : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ L U ∧ L 0=0 ∧ ∀ z ∈ U, Complex.exp (L z)=f z
/-- The removable sinh quotient at the origin. -/
def sinhc (z : ℂ) : ℂ := if z=0 then 1 else Complex.sinh z/z
/-- The removable tanh quotient at the origin. -/
def tanhc (z : ℂ) : ℂ := if z=0 then 1 else Complex.tanh z/z
/-- Real nonnegative finite values, fixing the square-root convention in Table4.30.1. -/
def HyperbolicPositive (z : ℂ) : Prop :=
  Complex.sinh z ≠ 0 ∧ Complex.cosh z ≠ 0 ∧
  0 ≤ (Complex.sinh z).re ∧ (Complex.sinh z).im=0 ∧
  0 ≤ (Complex.cosh z).re ∧ (Complex.cosh z).im=0
/-- The six hyperbolic functions in the row order of Table4.30.1. -/
def hyperbolicSix (z : ℂ) : Fin 6 → ℂ := ![Complex.sinh z,Complex.cosh z,Complex.tanh z,csch z,sech z,coth z]
/-- coth eq inv tanh. -/
@[dlmf 4.28.E7]
theorem coth_eq_inv_tanh (z : ℂ) : coth z=(Complex.tanh z)⁻¹ := by
  simp [coth, Complex.tanh_eq_sinh_div_cosh, inv_div]

/-- csc mul I. -/
@[dlmf 4.28.E11]
theorem csc_mul_I (z : ℂ) : (Complex.sin (I*z))⁻¹= -I*csch z := by
  simp [mul_comm I z, Complex.sin_mul_I, csch, mul_inv_rev, Complex.inv_I, mul_comm]

/-- sec mul I. -/
@[dlmf 4.28.E12]
theorem sec_mul_I (z : ℂ) : (Complex.cos (I*z))⁻¹=sech z := by
  rw [mul_comm I z, Complex.cos_mul_I]; rfl

/-- cot mul I. -/
@[dlmf 4.28.E13]
theorem cot_mul_I (z : ℂ) : (Complex.tan (I*z))⁻¹= -I*coth z := by
  simp [mul_comm I z, Complex.tan_mul_I, coth_eq_inv_tanh, mul_inv_rev, Complex.inv_I, mul_comm]

/-- sinh zeros. -/
theorem sinh_zeros (z : ℂ) : Complex.sinh z=0 ↔ ∃ k : ℤ, z=(k:ℂ)*π*I := by
  constructor
  · intro h
    have hs:Complex.sin (z*I)=0 := by rw [Complex.sin_mul_I,h,zero_mul]
    obtain ⟨k,hk⟩:=Complex.sin_eq_zero_iff.mp hs
    refine ⟨-k,?_⟩
    have hh:=congrArg (fun w:ℂ=>w*(-I)) hk
    simp [mul_assoc] at hh
    convert hh using 1 <;> push_cast <;> ring
  · rintro ⟨k,rfl⟩
    have hs:Complex.sin (((k:ℂ)*π*I)*I)=0 := by
      rw [mul_assoc,Complex.I_mul_I,mul_neg_one]
      exact Complex.sin_eq_zero_iff.mpr ⟨-k,by push_cast;ring⟩
    rw [Complex.sin_mul_I] at hs
    exact (mul_eq_zero.mp hs).resolve_right Complex.I_ne_zero


/-- cosh zeros. -/
theorem cosh_zeros (z : ℂ) : Complex.cosh z=0 ↔ ∃ k : ℤ, z=((k:ℂ)+1/2)*π*I := by
  constructor
  · intro h
    have hs:Complex.cos (z*I)=0 := by rwa [Complex.cos_mul_I]
    obtain ⟨k,hk⟩:=Complex.cos_eq_zero_iff.mp hs
    refine ⟨-k-1,?_⟩
    have hh:=congrArg (fun w:ℂ=>w*(-I)) hk
    simp [mul_assoc] at hh
    convert hh using 1 <;> push_cast <;> ring
  · rintro ⟨k,rfl⟩
    rw [← Complex.cos_mul_I]
    apply Complex.cos_eq_zero_iff.mpr
    refine ⟨-k-1,?_⟩
    simp [mul_assoc]
    push_cast
    ring


/-- The principal square root of the square of a nonnegative real number. -/
private lemma hypR4_sqrt_sq_ofReal {x : ℝ} (hx : 0 ≤ x) : Complex.sqrt ((x:ℂ)^2) = x := by
  have h : Complex.sqrt ((x^2:ℝ):ℂ) = (Real.sqrt (x^2):ℂ) :=
    Complex.sqrt_of_nonneg (by exact_mod_cast sq_nonneg x)
  rw [← Complex.ofReal_pow, h, Real.sqrt_sq hx]

/-- Under `HyperbolicPositive`, `sinh z` and `cosh z` are positive reals with `γ² = 1 + σ²`. -/
private lemma hypR4_pos_data {z : ℂ} (hz : HyperbolicPositive z) :
    ∃ σ γ : ℝ, 0 < σ ∧ 0 < γ ∧ γ^2 = 1+σ^2 ∧ Complex.sinh z = σ ∧ Complex.cosh z = γ := by
  obtain ⟨hs0, hc0, hsr, hsi, hcr, hci⟩ := hz
  have hs : Complex.sinh z = ((Complex.sinh z).re:ℂ) := Complex.ext (by simp) (by simp [hsi])
  have hc : Complex.cosh z = ((Complex.cosh z).re:ℂ) := Complex.ext (by simp) (by simp [hci])
  refine ⟨(Complex.sinh z).re, (Complex.cosh z).re, ?_, ?_, ?_, hs, hc⟩
  · refine lt_of_le_of_ne hsr ?_
    intro h; apply hs0; rw [hs, ← h]; simp
  · refine lt_of_le_of_ne hcr ?_
    intro h; apply hc0; rw [hc, ← h]; simp
  · have h := Complex.cosh_sq_sub_sinh_sq z
    rw [hs, hc] at h
    have h' : (((Complex.cosh z).re^2 - (Complex.sinh z).re^2 : ℝ):ℂ) = 1 := by push_cast; exact h
    have := Complex.ofReal_injective (h'.trans Complex.ofReal_one.symm)
    linarith

/-- Table4.30.1, column1: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_0 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 0=a) :
    hyperbolicSix z = ![a,Complex.sqrt (1+a^2),a/Complex.sqrt (1+a^2),a⁻¹,1/Complex.sqrt (1+a^2),Complex.sqrt (1+a^2)/a] := by
  obtain ⟨σ, γ, hσ, hγ, hγσ, hs, hc⟩ := hypR4_pos_data hz
  have hγσ' : (γ:ℂ)^2 = 1+(σ:ℂ)^2 := by exact_mod_cast hγσ
  have ha' : a = (σ:ℂ) := by
    rw [← ha]; simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc]
  subst ha'
  have hσ0 : (σ:ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hγ0 : (γ:ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hr : Complex.sqrt (1+(σ:ℂ)^2) = ((γ:ℝ):ℂ) := by
    rw [← hypR4_sqrt_sq_ofReal (by positivity : (0:ℝ) ≤ γ)]
    congr 1
    push_cast
    field_simp
    first | linear_combination hγσ' | linear_combination -hγσ' | linear_combination 2*hγσ' |
      linear_combination -2*hγσ'
  rw [hr]
  push_cast
  funext j
  fin_cases j <;> simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc] <;>
    field_simp

/-- Table4.30.1, column2: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_1 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 1=a) :
    hyperbolicSix z = ![Complex.sqrt (a^2-1),a,Complex.sqrt (a^2-1)/a,1/Complex.sqrt (a^2-1),a⁻¹,a/Complex.sqrt (a^2-1)] := by
  obtain ⟨σ, γ, hσ, hγ, hγσ, hs, hc⟩ := hypR4_pos_data hz
  have hγσ' : (γ:ℂ)^2 = 1+(σ:ℂ)^2 := by exact_mod_cast hγσ
  have ha' : a = (γ:ℂ) := by
    rw [← ha]; simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc]
  subst ha'
  have hσ0 : (σ:ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hγ0 : (γ:ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hr : Complex.sqrt ((γ:ℂ)^2-1) = ((σ:ℝ):ℂ) := by
    rw [← hypR4_sqrt_sq_ofReal (by positivity : (0:ℝ) ≤ σ)]
    congr 1
    push_cast
    field_simp
    first | linear_combination hγσ' | linear_combination -hγσ' | linear_combination 2*hγσ' |
      linear_combination -2*hγσ'
  rw [hr]
  push_cast
  funext j
  fin_cases j <;> simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc] <;>
    field_simp

/-- Table4.30.1, column3: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_2 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 2=a) :
    hyperbolicSix z = ![a/Complex.sqrt (1-a^2),1/Complex.sqrt (1-a^2),a,Complex.sqrt (1-a^2)/a,Complex.sqrt (1-a^2),a⁻¹] := by
  obtain ⟨σ, γ, hσ, hγ, hγσ, hs, hc⟩ := hypR4_pos_data hz
  have hγσ' : (γ:ℂ)^2 = 1+(σ:ℂ)^2 := by exact_mod_cast hγσ
  have ha' : a = (σ:ℂ)/γ := by
    rw [← ha]; simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc]
  subst ha'
  have hσ0 : (σ:ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hγ0 : (γ:ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hr : Complex.sqrt (1-((σ:ℂ)/γ)^2) = ((1/γ:ℝ):ℂ) := by
    rw [← hypR4_sqrt_sq_ofReal (by positivity : (0:ℝ) ≤ 1/γ)]
    congr 1
    push_cast
    field_simp
    first | linear_combination hγσ' | linear_combination -hγσ' | linear_combination 2*hγσ' |
      linear_combination -2*hγσ'
  rw [hr]
  push_cast
  funext j
  fin_cases j <;> simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc] <;>
    field_simp

/-- Table4.30.1, column4: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_3 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 3=a) :
    hyperbolicSix z = ![a⁻¹,Complex.sqrt (1+a^2)/a,1/Complex.sqrt (1+a^2),a,a/Complex.sqrt (1+a^2),Complex.sqrt (1+a^2)] := by
  obtain ⟨σ, γ, hσ, hγ, hγσ, hs, hc⟩ := hypR4_pos_data hz
  have hγσ' : (γ:ℂ)^2 = 1+(σ:ℂ)^2 := by exact_mod_cast hγσ
  have ha' : a = (σ:ℂ)⁻¹ := by
    rw [← ha]; simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc]
  subst ha'
  have hσ0 : (σ:ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hγ0 : (γ:ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hr : Complex.sqrt (1+((σ:ℂ)⁻¹)^2) = ((γ/σ:ℝ):ℂ) := by
    rw [← hypR4_sqrt_sq_ofReal (by positivity : (0:ℝ) ≤ γ/σ)]
    congr 1
    push_cast
    field_simp
    first | linear_combination hγσ' | linear_combination -hγσ' | linear_combination 2*hγσ' |
      linear_combination -2*hγσ'
  rw [hr]
  push_cast
  funext j
  fin_cases j <;> simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc] <;>
    field_simp

/-- Table4.30.1, column5: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_4 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 4=a) :
    hyperbolicSix z = ![Complex.sqrt (1-a^2)/a,a⁻¹,Complex.sqrt (1-a^2),a/Complex.sqrt (1-a^2),a,1/Complex.sqrt (1-a^2)] := by
  obtain ⟨σ, γ, hσ, hγ, hγσ, hs, hc⟩ := hypR4_pos_data hz
  have hγσ' : (γ:ℂ)^2 = 1+(σ:ℂ)^2 := by exact_mod_cast hγσ
  have ha' : a = (γ:ℂ)⁻¹ := by
    rw [← ha]; simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc]
  subst ha'
  have hσ0 : (σ:ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hγ0 : (γ:ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hr : Complex.sqrt (1-((γ:ℂ)⁻¹)^2) = ((σ/γ:ℝ):ℂ) := by
    rw [← hypR4_sqrt_sq_ofReal (by positivity : (0:ℝ) ≤ σ/γ)]
    congr 1
    push_cast
    field_simp
    first | linear_combination hγσ' | linear_combination -hγσ' | linear_combination 2*hγσ' |
      linear_combination -2*hγσ'
  rw [hr]
  push_cast
  funext j
  fin_cases j <;> simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc] <;>
    field_simp

/-- Table4.30.1, column6: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_5 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 5=a) :
    hyperbolicSix z = ![1/Complex.sqrt (a^2-1),a/Complex.sqrt (a^2-1),a⁻¹,Complex.sqrt (a^2-1),Complex.sqrt (a^2-1)/a,a] := by
  obtain ⟨σ, γ, hσ, hγ, hγσ, hs, hc⟩ := hypR4_pos_data hz
  have hγσ' : (γ:ℂ)^2 = 1+(σ:ℂ)^2 := by exact_mod_cast hγσ
  have ha' : a = (γ:ℂ)/σ := by
    rw [← ha]; simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc]
  subst ha'
  have hσ0 : (σ:ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hγ0 : (γ:ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hr : Complex.sqrt (((γ:ℂ)/σ)^2-1) = ((1/σ:ℝ):ℂ) := by
    rw [← hypR4_sqrt_sq_ofReal (by positivity : (0:ℝ) ≤ 1/σ)]
    congr 1
    push_cast
    field_simp
    first | linear_combination hγσ' | linear_combination -hγσ' | linear_combination 2*hγσ' |
      linear_combination -2*hγσ'
  rw [hr]
  push_cast
  funext j
  fin_cases j <;> simp [hyperbolicSix, csch, sech, coth, Complex.tanh_eq_sinh_div_cosh, hs, hc] <;>
    field_simp

/-- sinh div limit. -/
@[dlmf 4.31.E1]
theorem sinh_div_limit  : Tendsto (fun z : ℂ => Complex.sinh z/z) (𝓝[≠] 0) (𝓝 1) := by
  simpa [slope_fun_def_field] using (Complex.hasDerivAt_sinh (0:ℂ)).tendsto_slope

/-- tanh div limit. -/
@[dlmf 4.31.E2]
theorem tanh_div_limit  : Tendsto (fun z : ℂ => Complex.tanh z/z) (𝓝[≠] 0) (𝓝 1) := by
  have hd:HasDerivAt Complex.tanh (1:ℂ) 0 := by
    convert (Complex.hasDerivAt_sinh (0:ℂ)).div (Complex.hasDerivAt_cosh (0:ℂ)) (by simp) using 1
    · ext w; exact Complex.tanh_eq_sinh_div_cosh w
    · simp
  simpa [slope_fun_def_field,Complex.tanh] using hd.tendsto_slope


/-- cosh sub one div sq limit. -/
@[dlmf 4.31.E3]
theorem cosh_sub_one_div_sq_limit  : Tendsto (fun z : ℂ => (Complex.cosh z-1)/z^2) (𝓝[≠] 0) (𝓝 (1/2)) := by
  have hd:HasDerivAt (fun z:ℂ=>Complex.sinh (z/2)) ((1:ℂ)/2) 0 := by
    simpa only [zero_div,Complex.cosh_zero,one_mul,Function.comp_def,id_eq] using
      (Complex.hasDerivAt_sinh ((0:ℂ)/2)).comp (0:ℂ) ((hasDerivAt_id (0:ℂ)).div_const (2:ℂ))
  have hh:Tendsto (fun z:ℂ=>Complex.sinh (z/2)/z) (𝓝[≠] 0) (𝓝 ((1:ℂ)/2)) := by
    simpa [slope_fun_def_field] using hd.tendsto_slope
  have hlim:=(hh.pow 2).const_mul 2
  convert hlim using 1
  · ext z
    have hc:Complex.cosh z-1=2*Complex.sinh (z/2)^2 := by
      have h:=Complex.cosh_two_mul (z/2)
      rw [show (2:ℂ)*(z/2)=z by ring] at h
      linear_combination h+Complex.cosh_sq_sub_sinh_sq (z/2)
    rw [hc,div_pow]
    ring
  · norm_num


/-- Every finite entry of Table4.31.1; zeros at excluded pole entries are Lean totalizations, whose meromorphic poles are asserted separately below. -/
@[dlmf 4.31.T1]
theorem hyperbolic_special_values  :
    hyperbolicSix 0 = ![0,1,0,0,1,0] ∧
    hyperbolicSix (π*I/2) = ![I,0,0,-I,0,0] ∧
    hyperbolicSix (π*I) = ![0,-1,0,0,-1,0] ∧
    hyperbolicSix (3*π*I/2) = ![-I,0,0,I,0,0] := by
  refine ⟨?_,?_,?_,?_⟩ <;> ext j <;> fin_cases j <;>
    norm_num [hyperbolicSix,csch,sech,coth,Complex.tanh_eq_sinh_div_cosh,
      show (π:ℂ)*I/2=(π/2)*I by ring,
      show (3:ℂ)*π*I/2=(π+π/2)*I by ring,
      Complex.sinh_mul_I,Complex.cosh_mul_I,Complex.sin_add,Complex.cos_add]


/-- A function with nonzero derivative at a point does not vanish on a punctured
neighbourhood of that point (isolated zeros of analytic functions). -/
private lemma hypR4_eventually_ne_zero {f : ℂ → ℂ} {p c : ℂ} (ha : AnalyticAt ℂ f p)
    (hd : HasDerivAt f c p) (hc : c ≠ 0) : ∀ᶠ z in 𝓝[≠] p, f z ≠ 0 := by
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have h0 : HasDerivAt f 0 p := (hasDerivAt_const p (0:ℂ)).congr_of_eventuallyEq h
    exact hc (hd.unique h0)
  · exact h

/-- The norm of the reciprocal of a function tends to infinity at a zero, provided the function
is continuous there and does not vanish nearby. -/
private lemma hypR4_norm_inv_tendsto {f : ℂ → ℂ} {p : ℂ} (hf : ContinuousAt f p) (h0 : f p = 0)
    (hne : ∀ᶠ z in 𝓝[≠] p, f z ≠ 0) : Tendsto (fun z => ‖(f z)⁻¹‖) (𝓝[≠] p) atTop := by
  have hn : Tendsto (fun z => ‖f z‖) (𝓝[≠] p) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := (hf.norm.tendsto).mono_left (nhdsWithin_le_nhds (s := {p}ᶜ))
      simpa [h0] using this
    · filter_upwards [hne] with z hz
      exact norm_pos_iff.mpr hz
  exact (tendsto_inv_nhdsGT_zero.comp hn).congr (fun z => by simp [norm_inv])

/-- hyperbolic real infinity. -/
@[dlmf 4.31.T1]
theorem hyperbolic_real_infinity  :
    Tendsto Real.sinh atTop atTop ∧ Tendsto Real.cosh atTop atTop ∧
    Tendsto Real.tanh atTop (𝓝 1) ∧
    Tendsto (fun x : ℝ => (Real.sinh x)⁻¹) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => (Real.cosh x)⁻¹) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => Real.cosh x/Real.sinh x) atTop (𝓝 1) := by
  have hs : Tendsto Real.sinh atTop atTop :=
    tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono fun x hx => Real.self_le_sinh_iff.mpr hx)
      tendsto_id
  have hc : Tendsto Real.cosh atTop atTop :=
    tendsto_atTop_mono (fun x => (Real.sinh_lt_cosh x).le) hs
  have he : Tendsto (fun x:ℝ => Real.exp (-(2*x))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop two_pos)
  have key : ∀ x, Real.tanh x = (1 - Real.exp (-(2*x)))/(1+Real.exp (-(2*x))) := by
    intro x
    rw [Real.tanh_eq]
    have h1 : Real.exp (-(2*x)) = Real.exp (-x) * Real.exp (-x) := by rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [h1, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (2*Real.exp (-x)) * h2
  have ht : Tendsto Real.tanh atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1:ℝ))).sub he |>.div (tendsto_const_nhds.add he) (by norm_num : (1:ℝ)+0 ≠ 0)
    simp only [sub_zero, add_zero, div_one] at this
    exact this.congr (fun x => (key x).symm)
  refine ⟨hs, hc, ht, hs.inv_tendsto_atTop, hc.inv_tendsto_atTop, ?_⟩
  have := ht.inv₀ one_ne_zero
  simp only [inv_one] at this
  exact this.congr (fun x => by simp [Real.tanh_eq_sinh_div_cosh, inv_div])

/-- hyperbolic table sinh poles. -/
@[dlmf 4.31.T1]
theorem hyperbolic_table_sinh_poles (k : ℤ) :
    Tendsto (fun z : ℂ => ‖csch z‖) (𝓝[≠] ((k:ℂ)*π*I)) atTop ∧
    Tendsto (fun z : ℂ => ‖coth z‖) (𝓝[≠] ((k:ℂ)*π*I)) atTop := by
  have hp : Complex.sinh ((k:ℂ)*π*I) = 0 := (sinh_zeros _).mpr ⟨k, rfl⟩
  have hne := hypR4_eventually_ne_zero (Complex.differentiable_sinh.analyticAt _)
    (Complex.hasDerivAt_sinh ((k:ℂ)*π*I))
    (by intro h; have := Complex.cosh_sq_sub_sinh_sq ((k:ℂ)*π*I); rw [h, hp] at this; norm_num at this)
  have hinv := hypR4_norm_inv_tendsto Complex.continuous_sinh.continuousAt hp hne
  refine ⟨hinv, ?_⟩
  have hC : 0 < ‖Complex.cosh ((k:ℂ)*π*I)‖ := by
    rw [norm_pos_iff]; intro h
    have := Complex.cosh_sq_sub_sinh_sq ((k:ℂ)*π*I); rw [h, hp] at this; norm_num at this
  have hcl : Tendsto (fun z => ‖Complex.cosh z‖) (𝓝[≠] ((k:ℂ)*π*I)) (𝓝 ‖Complex.cosh ((k:ℂ)*π*I)‖) :=
    (Complex.continuous_cosh.continuousAt.norm.tendsto).mono_left nhdsWithin_le_nhds
  exact (hcl.pos_mul_atTop hC hinv).congr (fun z => by simp [coth, div_eq_mul_inv])

/-- hyperbolic table cosh poles. -/
@[dlmf 4.31.T1]
theorem hyperbolic_table_cosh_poles (k : ℤ) :
    Tendsto (fun z : ℂ => ‖Complex.tanh z‖) (𝓝[≠] (((k:ℂ)+1/2)*π*I)) atTop ∧
    Tendsto (fun z : ℂ => ‖sech z‖) (𝓝[≠] (((k:ℂ)+1/2)*π*I)) atTop := by
  have hp : Complex.cosh (((k:ℂ)+1/2)*π*I) = 0 := (cosh_zeros _).mpr ⟨k, rfl⟩
  have hS : Complex.sinh (((k:ℂ)+1/2)*π*I) ≠ 0 := by
    intro h; have := Complex.cosh_sq_sub_sinh_sq (((k:ℂ)+1/2)*π*I); rw [h, hp] at this; norm_num at this
  have hne := hypR4_eventually_ne_zero (Complex.differentiable_cosh.analyticAt _)
    (Complex.hasDerivAt_cosh (((k:ℂ)+1/2)*π*I)) hS
  have hinv := hypR4_norm_inv_tendsto Complex.continuous_cosh.continuousAt hp hne
  refine ⟨?_, hinv⟩
  have hC : 0 < ‖Complex.sinh (((k:ℂ)+1/2)*π*I)‖ := norm_pos_iff.mpr hS
  have hcl : Tendsto (fun z => ‖Complex.sinh z‖) (𝓝[≠] (((k:ℂ)+1/2)*π*I))
      (𝓝 ‖Complex.sinh (((k:ℂ)+1/2)*π*I)‖) :=
    (Complex.continuous_sinh.continuousAt.norm.tendsto).mono_left nhdsWithin_le_nhds
  exact (hcl.pos_mul_atTop hC hinv).congr
    (fun z => by simp [Complex.tanh_eq_sinh_div_cosh, div_eq_mul_inv])

/-- cosh le sinhc cube. -/
@[dlmf 4.32.E1]
theorem cosh_le_sinhc_cube (x : ℝ) : Real.cosh x ≤ (if x=0 then 1 else Real.sinh x/x)^3 := by
  sorry

/-- A function vanishing at `0` with positive derivative on `(0,∞)` is positive there. -/
private lemma hypR4_pos_of_deriv_pos {f f' : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0)
    (hd : ∀ x, 0 < x → HasDerivAt f (f' x) x) (hp : ∀ x, 0 < x → 0 < f' x) {x : ℝ}
    (hx : 0 < x) : 0 < f x := by
  have hm : StrictMonoOn f (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) hf.continuousOn fun y hy => ?_
    rw [interior_Ici] at hy
    rw [(hd y hy).deriv]; exact hp y hy
  have := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx.le) hx
  rwa [h0] at this

/-- `tanh x < x` and `x - x³/3 < tanh x` for `x > 0`. -/
private lemma hypR4_tanh_bounds {x : ℝ} (hx : 0 < x) :
    x - x^3/3 < Real.tanh x ∧ Real.tanh x < x := by
  have hc := Real.cosh_pos x
  -- sinh x < x cosh x
  have g := hypR4_pos_of_deriv_pos (f := fun t => t*Real.cosh t - Real.sinh t)
    (f' := fun t => t*Real.sinh t) (by fun_prop) (by simp)
    (fun t _ => by
      have := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
      exact this.congr_deriv (by
        simp only [id_eq, Pi.sub_apply, Pi.mul_apply, Nat.cast_ofNat]
        first | ring | (norm_num; ring) | norm_num))
    (fun t ht => mul_pos ht (Real.sinh_pos_iff.mpr ht)) hx
  have k := fun {y : ℝ} (hy : 0 < y) => hypR4_pos_of_deriv_pos
    (f := fun t => t*Real.cosh t - (1-t^2/3)*Real.sinh t)
    (f' := fun t => t^2/3*Real.cosh t + 5*t/3*Real.sinh t) (by fun_prop) (by simp)
    (fun t _ => by
      have := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub
        ((((hasDerivAt_pow 2 t).div_const 3).const_sub 1).mul (Real.hasDerivAt_sinh t))
      exact this.congr_deriv (by
        simp only [id_eq, Pi.sub_apply, Pi.mul_apply, Nat.cast_ofNat]
        first | ring | (norm_num; ring) | norm_num))
    (fun t ht => by
      have := Real.cosh_pos t
      have := Real.sinh_pos_iff.mpr ht
      positivity) hy
  have h := hypR4_pos_of_deriv_pos (f := fun t => Real.sinh t - (t-t^3/3)*Real.cosh t)
    (f' := fun t => t*(t*Real.cosh t - (1-t^2/3)*Real.sinh t)) (by fun_prop) (by simp)
    (fun t _ => by
      have := (Real.hasDerivAt_sinh t).sub
        ((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 3))).mul (Real.hasDerivAt_cosh t))
      exact this.congr_deriv (by
        simp only [id_eq, Pi.sub_apply, Pi.mul_apply, Nat.cast_ofNat]
        first | ring | (norm_num; ring) | norm_num))
    (fun t ht => mul_pos ht (k ht)) hx
  rw [Real.tanh_eq_sinh_div_cosh]
  constructor
  · rw [lt_div_iff₀ hc]; linarith
  · rw [div_lt_iff₀ hc]; linarith

/-- sin cos lt tanh lt. -/
@[dlmf 4.32.E2]
theorem sin_cos_lt_tanh_lt {x : ℝ} (hx : 0<x) : Real.sin x*Real.cos x < Real.tanh x ∧ Real.tanh x<x := by
  obtain ⟨h1, h2⟩ := hypR4_tanh_bounds hx
  refine ⟨?_, h2⟩
  rcases le_or_gt x 1 with hx1 | hx1
  · have hcos := Real.cos_bound (x := x) (by rw [abs_of_pos hx]; exact hx1)
    rw [abs_of_pos hx] at hcos
    have hc0 : 0 ≤ Real.cos x :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
    have hs := (Real.sin_lt hx).le
    have hcub : Real.cos x ≤ 1 - x^2/2 + x^4*(5/96) := by
      have := (abs_le.mp hcos).2; linarith
    calc Real.sin x*Real.cos x ≤ x*Real.cos x := mul_le_mul_of_nonneg_right hs hc0
      _ ≤ x*(1 - x^2/2 + x^4*(5/96)) := mul_le_mul_of_nonneg_left hcub hx.le
      _ ≤ x - x^3/3 := by
          have e : x - x^3/3 - x*(1 - x^2/2 + x^4*(5/96)) = x^3*(1/6 - 5*x^2/96) := by ring
          have : 0 ≤ x^3*(1/6 - 5*x^2/96) := mul_nonneg (pow_pos hx 3).le (by nlinarith)
          linarith
      _ < Real.tanh x := h1
  · have hsc : Real.sin x*Real.cos x ≤ 1/2 := by
      nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x - Real.cos x)]
    have ht : 1/2 < Real.tanh x := by
      rw [Real.tanh_eq_sinh_div_cosh, lt_div_iff₀ (Real.cosh_pos x), Real.sinh_eq, Real.cosh_eq]
      have he : 3 < Real.exp (2*x) := by
        have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2*x by linarith); nlinarith
      have hpos := Real.exp_pos (-x)
      have hmul : Real.exp x * Real.exp x = Real.exp (2*x) := by rw [← Real.exp_add]; ring_nf
      have hinv : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    linarith

/-- cosh sub lower. -/
@[dlmf 4.32.E3]
theorem cosh_sub_lower {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    |Real.cosh x-Real.cosh y| ≥ |x-y| *Real.sqrt (Real.sinh x*Real.sinh y) := by
  have hd : Real.cosh x - Real.cosh y = 2*Real.sinh ((x+y)/2)*Real.sinh ((x-y)/2) := by
    have h1 := Real.cosh_add ((x+y)/2) ((x-y)/2)
    have h2 := Real.cosh_sub ((x+y)/2) ((x-y)/2)
    rw [show (x+y)/2+(x-y)/2 = x by ring] at h1
    rw [show (x+y)/2-(x-y)/2 = y by ring] at h2
    rw [h1, h2]; ring
  have hsp : 0 < Real.sinh ((x+y)/2) := Real.sinh_pos_iff.mpr (by linarith)
  have hsd : |x-y|/2 ≤ |Real.sinh ((x-y)/2)| := by
    rw [Real.abs_sinh, show |(x-y)/2| = |x-y|/2 by rw [abs_div, abs_two]]
    exact Real.self_le_sinh_iff.mpr (by positivity)
  have hprod : Real.sinh x*Real.sinh y ≤ Real.sinh ((x+y)/2)^2 := by
    have e1 : Real.sinh x*Real.sinh y = (Real.cosh (x+y) - Real.cosh (x-y))/2 := by
      rw [Real.cosh_add, Real.cosh_sub]; ring
    have e2 : Real.sinh ((x+y)/2)^2 = (Real.cosh (x+y) - 1)/2 := by
      have := Real.cosh_two_mul ((x+y)/2)
      rw [show 2*((x+y)/2) = x+y by ring] at this
      nlinarith [Real.cosh_sq ((x+y)/2)]
    rw [e1, e2]; linarith [Real.one_le_cosh (x-y)]
  have hsq : Real.sqrt (Real.sinh x*Real.sinh y) ≤ Real.sinh ((x+y)/2) := by
    rw [Real.sqrt_le_left hsp.le]
    exact hprod
  rw [hd, abs_mul, abs_mul, abs_two, abs_of_pos hsp, ge_iff_le]
  calc (|x-y|)*Real.sqrt (Real.sinh x*Real.sinh y) ≤ (|x-y|)*Real.sinh ((x+y)/2) :=
        mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
    _ = 2*Real.sinh ((x+y)/2)*(|x-y|/2) := by ring
    _ ≤ 2*Real.sinh ((x+y)/2)*|Real.sinh ((x-y)/2)| := by gcongr

/-- arctan le tanh. -/
@[dlmf 4.32.E4]
theorem arctan_le_tanh {x : ℝ} (hx : 0≤x) : Real.arctan x ≤ π/2*Real.tanh x := by
  sorry

/-- Powers of the rotated argument `iz` produce the alternating sign `(-1)^k`. -/
private lemma hypR4_rot_pow (z c : ℂ) (k : ℕ) : (c*(I*z))^(2*k) = (-1:ℂ)^k*(c*z)^(2*k) := by
  rw [show c*(I*z) = I*(c*z) by ring, mul_pow, pow_mul, Complex.I_sq]

/-- The square of the alternating sign is one. -/
private lemma hypR4_neg_one_sq (k : ℕ) : (-1:ℂ)^k*(-1:ℂ)^k = 1 := by
  rw [← mul_pow]; norm_num

/-- The rotated point `iz/π` has norm `‖z‖/π`. -/
private lemma hypR4_norm_rot (z : ℂ) : ‖I*z/π‖ = ‖z‖/π := by
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

/-- hasSum tanh. -/
@[dlmf 4.33.E3]
theorem hasSum_tanh {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*(n+1))*((2:ℂ)^(2*(n+1))-1)*
      (bernoulli (2*(n+1)):ℂ)/((2*(n+1)).factorial:ℂ)*z^(2*n+1)) (Complex.tanh z) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hz0 : z = 0
  · subst hz0; simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0:ℂ)) 0)
  have hw : ‖I*z/π‖ < 1/2 := by
    rw [hypR4_norm_rot, div_lt_iff₀ Real.pi_pos]; linarith
  have hw0 : I*z/π ≠ 0 := by simp [hz0, hπ, Complex.I_ne_zero]
  have h := Complex.hasSum_pi_mul_tan_bernoulli hw hw0
  have h2 : HasSum (fun k : ℕ => (bernoulli (2*k):ℂ)*(1-4^k)*(2*z)^(2*k)/((2*k).factorial:ℂ))
      (-z*Complex.tanh z) := by
    convert h using 1
    · funext k
      rw [show (2:ℂ)*π*(I*z/π) = 2*(I*z) by field_simp, hypR4_rot_pow]
      linear_combination (-(bernoulli (2*k):ℂ)*(1-4^k)*(2*z)^(2*k)/((2*k).factorial:ℂ))*
        hypR4_neg_one_sq k
    · rw [show (π:ℂ)*(I*z/π) = z*I by field_simp, Complex.tan_mul_I]
      linear_combination (-z*Complex.tanh z)*Complex.I_sq
  have h3 := ((hasSum_nat_add_iff' 1).mpr h2).div_const (-z)
  convert h3 using 1
  · funext n
    have e : 2*(n+1) = 2*n+2 := by ring
    have e4 : (4:ℂ)^(n+1) = 2^(2*n+2) := by
      rw [show 2*n+2 = 2*(n+1) by ring, pow_mul]; norm_num
    rw [e, e4]
    field_simp
    ring
  · simp
    field_simp

/-- hasSum csch. -/
theorem hasSum_csch {z : ℂ} (hz0 : z≠0) (hz : ‖z‖<π) :
    HasSum (fun n : ℕ => 2*(1-(2:ℂ)^(2*n+1))*(bernoulli (2*n+2):ℂ)/
      ((2*n+2).factorial:ℂ)*z^(2*n+1)) (csch z-z⁻¹) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw : ‖I*z/π‖ < 1 := by rw [hypR4_norm_rot, div_lt_one Real.pi_pos]; exact hz
  have hw0 : I*z/π ≠ 0 := by simp [hz0, hπ, Complex.I_ne_zero]
  have hs : Complex.sinh z ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := (sinh_zeros z).mp h
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hz0 hk
    have : ‖z‖ = (|(k:ℝ)|)*π := by
      rw [hk, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast]
    have h1 : (1:ℝ) ≤ |(k:ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    nlinarith [Real.pi_pos]
  have h := Complex.hasSum_pi_mul_div_sin_bernoulli hw hw0
  have h2 : HasSum (fun k : ℕ => (bernoulli (2*k):ℂ)*(2-4^k)*z^(2*k)/((2*k).factorial:ℂ))
      (z*csch z) := by
    convert h using 1
    · funext k
      rw [show (π:ℂ)*(I*z/π) = 1*(I*z) by field_simp, hypR4_rot_pow, one_mul]
      linear_combination (-(bernoulli (2*k):ℂ)*(2-4^k)*z^(2*k)/((2*k).factorial:ℂ))*
        hypR4_neg_one_sq k
    · rw [show (π:ℂ)*(I*z/π) = z*I by field_simp, Complex.sin_mul_I, csch]
      field_simp
  have h3 := ((hasSum_nat_add_iff' 1).mpr h2).div_const z
  convert h3 using 1
  · funext n
    have e : 2*(n+1) = 2*n+2 := by ring
    have e4 : (4:ℂ)^(n+1) = 2*2^(2*n+1) := by
      rw [show 2*2^(2*n+1) = (2:ℂ)^(2*(n+1)) by ring, pow_mul]; norm_num
    rw [e, e4]
    field_simp
    ring
  · simp [bernoulli_zero]
    field_simp
    ring

/-- hasSum sech. -/
theorem hasSum_sech {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (eulerNumber (2*n):ℂ)/((2*n).factorial:ℂ)*z^(2*n)) (sech z) := by
  have hw : ‖1*(I*z)‖ < π/2 := by rw [one_mul, norm_mul, Complex.norm_I, one_mul]; exact hz
  have h := hasSum_sec_euler hw
  convert h using 1
  · funext n
    rw [hypR4_rot_pow, one_mul]
    linear_combination (-(eulerNumber (2*n):ℂ)*z^(2*n)/((2*n).factorial:ℂ))*hypR4_neg_one_sq n
  · rw [sec, one_mul, mul_comm, Complex.cos_mul_I, sech]

/-- hasSum coth. -/
theorem hasSum_coth {z : ℂ} (hz0 : z≠0) (hz : ‖z‖<π) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*n+2)*(bernoulli (2*n+2):ℂ)/
      ((2*n+2).factorial:ℂ)*z^(2*n+1)) (coth z-z⁻¹) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw : ‖I*z/π‖ < 1 := by rw [hypR4_norm_rot, div_lt_one Real.pi_pos]; exact hz
  have hw0 : I*z/π ≠ 0 := by simp [hz0, hπ, Complex.I_ne_zero]
  have hs : Complex.sinh z ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := (sinh_zeros z).mp h
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hz0 hk
    have : ‖z‖ = (|(k:ℝ)|)*π := by
      rw [hk, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast]
    have h1 : (1:ℝ) ≤ |(k:ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    nlinarith [Real.pi_pos]
  have h := Complex.hasSum_pi_mul_cot_bernoulli hw hw0
  have h2 : HasSum (fun k : ℕ => (bernoulli (2*k):ℂ)*(2*z)^(2*k)/((2*k).factorial:ℂ))
      (z*coth z) := by
    convert h using 1
    · funext k
      rw [show (2:ℂ)*π*(I*z/π) = 2*(I*z) by field_simp, hypR4_rot_pow]
      linear_combination (-(bernoulli (2*k):ℂ)*(2*z)^(2*k)/((2*k).factorial:ℂ))*hypR4_neg_one_sq k
    · rw [show (π:ℂ)*(I*z/π) = z*I by field_simp, Complex.cot, Complex.cos_mul_I,
        Complex.sin_mul_I, coth]
      field_simp
  have h3 := ((hasSum_nat_add_iff' 1).mpr h2).div_const z
  convert h3 using 1
  · funext n
    have : 2*(n+1) = 2*n+2 := by ring
    rw [this]
    field_simp
    ring
  · simp [bernoulli_zero]
    field_simp

/-- hasSum log sinhc. -/
theorem hasSum_log_sinhc {L : ℂ → ℂ} (hL : HyperbolicNormalizedLog (Metric.ball 0 π) sinhc L)
    {z : ℂ} (hz : ‖z‖<π) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*n+1)*(bernoulli (2*n+2):ℂ)/
      ((n+1:ℂ)*((2*n+2).factorial:ℂ))*z^(2*n+2)) (L z) := by
  sorry

/-- hasSum log cosh. -/
theorem hasSum_log_cosh {L : ℂ → ℂ} (hL : HyperbolicNormalizedLog (Metric.ball 0 (π/2)) Complex.cosh L)
    {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*n+1)*((2:ℂ)^(2*n+2)-1)*(bernoulli (2*n+2):ℂ)/
      ((n+1:ℂ)*((2*n+2).factorial:ℂ))*z^(2*n+2)) (L z) := by
  sorry

/-- hasSum log tanhc. -/
theorem hasSum_log_tanhc {L : ℂ → ℂ} (hL : HyperbolicNormalizedLog (Metric.ball 0 (π/2)) tanhc L)
    {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*n+2)*(1-(2:ℂ)^(2*n+1))*(bernoulli (2*n+2):ℂ)/
      ((n+1:ℂ)*((2*n+2).factorial:ℂ))*z^(2*n+2)) (L z) := by
  sorry

/-- hasDerivAt tanh. -/
@[dlmf 4.34.E3]
theorem hasDerivAt_tanh {z : ℂ} (hz : Complex.cosh z≠0) : HasDerivAt Complex.tanh (sech z^2) z := by
  convert (Complex.hasDerivAt_sinh z).div (Complex.hasDerivAt_cosh z) hz using 1
  · ext w; exact Complex.tanh_eq_sinh_div_cosh w
  · simp only [sech]
    field_simp
    linear_combination -(Complex.cosh_sq_sub_sinh_sq z)

/-- hasDerivAt csch. -/
@[dlmf 4.34.E4]
theorem hasDerivAt_csch {z : ℂ} (hz : Complex.sinh z≠0) : HasDerivAt csch (-csch z*coth z) z := by
  convert (Complex.hasDerivAt_sinh z).inv hz using 1
  · rfl
  · simp only [csch, coth]
    field_simp <;> ring

/-- hasDerivAt sech. -/
@[dlmf 4.34.E5]
theorem hasDerivAt_sech {z : ℂ} (hz : Complex.cosh z≠0) : HasDerivAt sech (-sech z*Complex.tanh z) z := by
  convert (Complex.hasDerivAt_cosh z).inv hz using 1
  · rfl
  · simp only [sech, Complex.tanh_eq_sinh_div_cosh]
    field_simp <;> ring

/-- hasDerivAt coth. -/
@[dlmf 4.34.E6]
theorem hasDerivAt_coth {z : ℂ} (hz : Complex.sinh z≠0) : HasDerivAt coth (-csch z^2) z := by
  convert (Complex.hasDerivAt_cosh z).div (Complex.hasDerivAt_sinh z) hz using 1
  · rfl
  · simp only [coth, csch]
    field_simp
    linear_combination (Complex.cosh_sq_sub_sinh_sq z)

/-- hyperbolic linear ode. -/
@[dlmf 4.34.E7, dlmf 4.34.E11]
theorem hyperbolic_linear_ode {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {a : ℂ} (ha : a≠0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf' : DifferentiableOn ℂ (deriv f) U) :
    (∀ z ∈ U, deriv (deriv f) z-a^2*f z=0) ↔
      ∃ A B : ℂ, ∀ z ∈ U, f z=A*Complex.cosh (a*z)+B*Complex.sinh (a*z) := by
  have hd1 : ∀ z ∈ U, HasDerivAt f (deriv f z) z := fun z hz =>
    (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hd2 : ∀ z ∈ U, HasDerivAt (deriv f) (deriv (deriv f) z) z := fun z hz =>
    (hf'.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hcF : ∀ A B : ℂ, ∀ w : ℂ, HasDerivAt (fun w => A*Complex.cosh (a*w)+B*Complex.sinh (a*w))
      (a*(A*Complex.sinh (a*w)+B*Complex.cosh (a*w))) w := by
    intro A B w
    have h1 := ((Complex.hasDerivAt_cosh (a*w)).comp w ((hasDerivAt_id w).const_mul a)).const_mul A
    have h2 := ((Complex.hasDerivAt_sinh (a*w)).comp w ((hasDerivAt_id w).const_mul a)).const_mul B
    exact (h1.add h2).congr_deriv (by ring)
  constructor
  · intro hode
    have hconst : ∀ s : ℂ, (∀ z ∈ U, deriv (deriv f) z - s*deriv f z = -s*(deriv f z - s*f z)) →
        ∃ C, ∀ z ∈ U, (deriv f z - s*f z)*Complex.exp (s*z) = C := by
      intro s hs
      have hD : ∀ z ∈ U, HasDerivAt (fun w => (deriv f w - s*f w)*Complex.exp (s*w)) 0 z := by
        intro z hz
        have he : HasDerivAt (fun w => Complex.exp (s*w)) (Complex.exp (s*z)*s) z := by
          simpa using ((hasDerivAt_id z).const_mul s).cexp
        have := ((hd2 z hz).sub ((hd1 z hz).const_mul s)).mul he
        convert this using 1
        simp only [Pi.sub_apply]
        linear_combination (-Complex.exp (s*z))*hs z hz
      exact hU.exists_is_const_of_deriv_eq_zero hc.isPreconnected
        (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => (hD z hz).deriv)
    obtain ⟨C1, hC1⟩ := hconst a (fun z hz => by linear_combination hode z hz)
    obtain ⟨C2, hC2⟩ := hconst (-a) (fun z hz => by linear_combination hode z hz)
    refine ⟨(C2 - C1)/(2*a), (C1 + C2)/(2*a), fun z hz => ?_⟩
    have e1 := hC1 z hz
    have e2 := hC2 z hz
    have hep : Complex.exp (a*z) = Complex.cosh (a*z) + Complex.sinh (a*z) :=
      (Complex.cosh_add_sinh _).symm
    have hem : Complex.exp (-a*z) = Complex.cosh (a*z) - Complex.sinh (a*z) := by
      rw [neg_mul]; exact (Complex.cosh_sub_sinh _).symm
    have hinv : Complex.exp (a*z)*Complex.exp (-a*z) = 1 := by rw [← Complex.exp_add]; simp
    have hcs : Complex.cosh (a*z)^2 - Complex.sinh (a*z)^2 = 1 := Complex.cosh_sq_sub_sinh_sq _
    field_simp
    rw [hep] at e1; rw [hem] at e2
    linear_combination (Complex.sinh (a*z) - Complex.cosh (a*z))*e1 +
      (Complex.cosh (a*z) + Complex.sinh (a*z))*e2 - 2*a*f z*hcs
  · rintro ⟨A, B, hAB⟩ z hz
    have hev : f =ᶠ[𝓝 z] fun w => A*Complex.cosh (a*w)+B*Complex.sinh (a*w) :=
      Filter.eventually_of_mem (hU.mem_nhds hz) hAB
    have hdF : deriv (fun w => A*Complex.cosh (a*w)+B*Complex.sinh (a*w)) =
        fun w => a*(A*Complex.sinh (a*w)+B*Complex.cosh (a*w)) := by
      funext w; exact (hcF A B w).deriv
    have hev' : deriv f =ᶠ[𝓝 z] fun w => a*(A*Complex.sinh (a*w)+B*Complex.cosh (a*w)) := by
      rw [← hdF]; exact hev.deriv
    have h2 : HasDerivAt (fun w => a*(A*Complex.sinh (a*w)+B*Complex.cosh (a*w)))
        (a*(a*(A*Complex.cosh (a*z)+B*Complex.sinh (a*z)))) z := by
      have := (hcF B A z).const_mul a
      convert this using 1
      · funext w; ring
      · ring
    rw [hev'.deriv_eq, h2.deriv, hAB z hz]
    ring

/-- General squared first-order equation, including the equilibrium solutions omitted in the source shorthand. -/
@[dlmf 4.34.E8, dlmf 4.34.E12]
theorem hyperbolic_squared_ode_plus {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {a : ℂ} (ha : a≠0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (∀ z ∈ U, (deriv f z)^2-a^2*(f z)^2=1) ↔
      (∃ c : ℂ, ∀ z ∈ U, f z=a⁻¹*Complex.sinh (a*z+c)) ∨
      (∃ w : ℂ, -a^2*w^2=1 ∧ ∀ z ∈ U, f z=w) := by
  sorry

/-- General squared first-order equation, including the equilibrium solutions omitted in the source shorthand. -/
@[dlmf 4.34.E9, dlmf 4.34.E13]
theorem hyperbolic_squared_ode_minus {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {a : ℂ} (ha : a≠0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (∀ z ∈ U, (deriv f z)^2-a^2*(f z)^2=-1) ↔
      (∃ c : ℂ, ∀ z ∈ U, f z=a⁻¹*Complex.cosh (a*z+c)) ∨
      (∃ w : ℂ, -a^2*w^2=-1 ∧ ∀ z ∈ U, f z=w) := by
  sorry

/-- The Riccati general solution, with both constant equilibria and all pole exclusions. -/
@[dlmf 4.34.E10, dlmf 4.34.E14]
theorem hyperbolic_riccati_ode {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {a : ℂ} (ha : a≠0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (∀ z ∈ U, deriv f z+a^2*(f z)^2=1) ↔
      (∃ c : ℂ, (∀ z ∈ U, Complex.sinh (a*z+c)≠0) ∧ ∀ z ∈ U, f z=a⁻¹*coth (a*z+c)) ∨
      (∀ z ∈ U, f z=a⁻¹) ∨ (∀ z ∈ U, f z= -a⁻¹) := by
  sorry

/-- tanh add. -/
@[dlmf 4.35.E3]
theorem tanh_add {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh (u+v)=(Complex.tanh u+Complex.tanh v)/(1+Complex.tanh u*Complex.tanh v) := by
  unfold Complex.tanh
  rw [Complex.sinh_add,Complex.cosh_add]
  field_simp <;> ring


/-- tanh sub. -/
@[dlmf 4.35.E3]
theorem tanh_sub {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh (u-v)=(Complex.tanh u-Complex.tanh v)/(1-Complex.tanh u*Complex.tanh v) := by
  simpa [sub_eq_add_neg,Complex.tanh_neg] using tanh_add hu (show Complex.cosh (-v)≠0 by simpa using hv)


/-- coth add. -/
@[dlmf 4.35.E4]
theorem coth_add {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth (u+v)=(coth u*coth v+1)/(coth u+coth v) := by
  unfold coth
  rw [Complex.sinh_add,Complex.cosh_add]
  field_simp <;> ring


/-- coth sub. -/
@[dlmf 4.35.E4]
theorem coth_sub {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth (u-v)=(-coth u*coth v+1)/(coth u-coth v) := by
  have hn:Complex.sinh (-v)≠0 := by simpa using hv
  have hh:=coth_add hu hn
  simpa [coth,sub_eq_add_neg,Complex.sinh_neg,Complex.cosh_neg,div_neg] using hh


/-- sinh add sinh. -/
@[dlmf 4.35.E5]
theorem sinh_add_sinh (u v : ℂ) : Complex.sinh u+Complex.sinh v=2*Complex.sinh ((u+v)/2)*Complex.cosh ((u-v)/2) := by
  have h1 := Complex.sinh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.sinh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1+h2

/-- sinh sub sinh. -/
@[dlmf 4.35.E6]
theorem sinh_sub_sinh (u v : ℂ) : Complex.sinh u-Complex.sinh v=2*Complex.cosh ((u+v)/2)*Complex.sinh ((u-v)/2) := by
  have h1 := Complex.sinh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.sinh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1-h2

/-- cosh add cosh. -/
@[dlmf 4.35.E7]
theorem cosh_add_cosh (u v : ℂ) : Complex.cosh u+Complex.cosh v=2*Complex.cosh ((u+v)/2)*Complex.cosh ((u-v)/2) := by
  have h1 := Complex.cosh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.cosh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1+h2

/-- cosh sub cosh. -/
@[dlmf 4.35.E8]
theorem cosh_sub_cosh (u v : ℂ) : Complex.cosh u-Complex.cosh v=2*Complex.sinh ((u+v)/2)*Complex.sinh ((u-v)/2) := by
  have h1 := Complex.cosh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.cosh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1-h2

/-- tanh add tanh. -/
@[dlmf 4.35.E9]
theorem tanh_add_tanh {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh u+Complex.tanh v=Complex.sinh (u+v)/(Complex.cosh u*Complex.cosh v) := by
  simp only [Complex.tanh_eq_sinh_div_cosh, Complex.sinh_add]
  field_simp <;> ring

/-- tanh sub tanh. -/
@[dlmf 4.35.E9]
theorem tanh_sub_tanh {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh u-Complex.tanh v=Complex.sinh (u-v)/(Complex.cosh u*Complex.cosh v) := by
  simp only [Complex.tanh_eq_sinh_div_cosh, Complex.sinh_sub]
  field_simp <;> ring

/-- coth add coth. -/
@[dlmf 4.35.E10]
theorem coth_add_coth {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth u+coth v=Complex.sinh (v+u)/(Complex.sinh u*Complex.sinh v) := by
  simp only [coth, Complex.sinh_add]
  field_simp <;> ring

/-- coth sub coth. -/
@[dlmf 4.35.E10]
theorem coth_sub_coth {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth u-coth v=Complex.sinh (v-u)/(Complex.sinh u*Complex.sinh v) := by
  simp only [coth, Complex.sinh_sub]
  field_simp <;> ring

/-- sech sq. -/
@[dlmf 4.35.E12]
theorem sech_sq {z : ℂ} (hz : Complex.cosh z≠0) : sech z^2=1-Complex.tanh z^2 := by
  simp only [sech, Complex.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination -(Complex.cosh_sq_sub_sinh_sq z)

/-- csch sq. -/
@[dlmf 4.35.E13]
theorem csch_sq {z : ℂ} (hz : Complex.sinh z≠0) : csch z^2=coth z^2-1 := by
  simp only [csch, coth]
  field_simp
  linear_combination -(Complex.cosh_sq_sub_sinh_sq z)

/-- two sinh mul sinh. -/
@[dlmf 4.35.E14]
theorem two_sinh_mul_sinh (u v : ℂ) : 2*Complex.sinh u*Complex.sinh v=Complex.cosh (u+v)-Complex.cosh (u-v) := by
  rw [Complex.cosh_add, Complex.cosh_sub]
  ring

/-- two cosh mul cosh. -/
@[dlmf 4.35.E15]
theorem two_cosh_mul_cosh (u v : ℂ) : 2*Complex.cosh u*Complex.cosh v=Complex.cosh (u+v)+Complex.cosh (u-v) := by
  rw [Complex.cosh_add, Complex.cosh_sub]
  ring

/-- two sinh mul cosh. -/
@[dlmf 4.35.E16]
theorem two_sinh_mul_cosh (u v : ℂ) : 2*Complex.sinh u*Complex.cosh v=Complex.sinh (u+v)+Complex.sinh (u-v) := by
  rw [Complex.sinh_add, Complex.sinh_sub]
  ring

/-- sinh sq sub sinh sq. -/
@[dlmf 4.35.E17]
theorem sinh_sq_sub_sinh_sq (u v : ℂ) : Complex.sinh u^2-Complex.sinh v^2=Complex.sinh (u+v)*Complex.sinh (u-v) := by
  rw [Complex.sinh_add, Complex.sinh_sub]
  linear_combination -(Complex.sinh u)^2*(Complex.cosh_sq_sub_sinh_sq v) +
    (Complex.sinh v)^2*(Complex.cosh_sq_sub_sinh_sq u)

/-- cosh sq sub cosh sq. -/
@[dlmf 4.35.E18]
theorem cosh_sq_sub_cosh_sq (u v : ℂ) : Complex.cosh u^2-Complex.cosh v^2=Complex.sinh (u+v)*Complex.sinh (u-v) := by
  linear_combination (Complex.cosh_sq_sub_sinh_sq u) -
    (Complex.cosh_sq_sub_sinh_sq v) + (sinh_sq_sub_sinh_sq u v)

/-- sinh sq add cosh sq. -/
@[dlmf 4.35.E19]
theorem sinh_sq_add_cosh_sq (u v : ℂ) : Complex.sinh u^2+Complex.cosh v^2=Complex.cosh (u+v)*Complex.cosh (u-v) := by
  rw [Complex.cosh_add, Complex.cosh_sub]
  linear_combination -(Complex.cosh v)^2*(Complex.cosh_sq_sub_sinh_sq u) -
    (Complex.sinh u)^2*(Complex.cosh_sq_sub_sinh_sq v)

/-- sinh half sq. -/
@[dlmf 4.35.E20]
theorem sinh_half_sq (z : ℂ) : Complex.sinh (z/2)^2=(Complex.cosh z-1)/2 := by
  have h := Complex.cosh_two_mul (z/2)
  rw [show 2*(z/2)=z by ring] at h
  linear_combination -h/2-(Complex.cosh_sq_sub_sinh_sq (z/2))/2

/-- cosh half sq. -/
@[dlmf 4.35.E21]
theorem cosh_half_sq (z : ℂ) : Complex.cosh (z/2)^2=(Complex.cosh z+1)/2 := by
  have h := Complex.cosh_two_mul (z/2)
  rw [show 2*(z/2)=z by ring] at h
  linear_combination -h/2+(Complex.cosh_sq_sub_sinh_sq (z/2))/2

/-- tanh half sq. -/
@[dlmf 4.35.E22]
theorem tanh_half_sq {z : ℂ} (hz : Complex.cosh (z/2)≠0) : Complex.tanh (z/2)^2=(Complex.cosh z-1)/(Complex.cosh z+1) := by
  have hs:Complex.cosh z-1=2*Complex.sinh (z/2)^2 := by linear_combination -2*sinh_half_sq z
  have hc:Complex.cosh z+1=2*Complex.cosh (z/2)^2 := by linear_combination -2*cosh_half_sq z
  rw [hs,hc,Complex.tanh,div_pow]
  field_simp


/-- tanh half ratios. -/
@[dlmf 4.35.E22]
theorem tanh_half_ratios {z : ℂ} (hz : Complex.sinh z≠0) : Complex.tanh (z/2)=(Complex.cosh z-1)/Complex.sinh z ∧ Complex.tanh (z/2)=Complex.sinh z/(Complex.cosh z+1) := by
  have h2 : Complex.sinh z = 2*Complex.sinh (z/2)*Complex.cosh (z/2) := by
    rw [← Complex.sinh_two_mul]; ring_nf
  have hc : Complex.cosh z - 1 = 2*Complex.sinh (z/2)^2 := by linear_combination -2*sinh_half_sq z
  have hc' : Complex.cosh z + 1 = 2*Complex.cosh (z/2)^2 := by linear_combination -2*cosh_half_sq z
  have hch : Complex.cosh (z/2) ≠ 0 := by intro h; apply hz; rw [h2,h]; ring
  have hsh : Complex.sinh (z/2) ≠ 0 := by intro h; apply hz; rw [h2,h]; ring
  rw [Complex.tanh_eq_sinh_div_cosh, hc, hc', h2]
  constructor <;> field_simp <;> ring

/-- sinh two mul tanh. -/
@[dlmf 4.35.E26]
theorem sinh_two_mul_tanh {z : ℂ} (hz : Complex.cosh z≠0) : Complex.sinh (2*z)=2*Complex.tanh z/(1-Complex.tanh z^2) := by
  rw [Complex.tanh,Complex.sinh_two_mul]
  field_simp
  rw [Complex.cosh_sq]
  ring


/-- cosh two mul forms. -/
@[dlmf 4.35.E27]
theorem cosh_two_mul_forms (z : ℂ) : Complex.cosh (2*z)=2*Complex.cosh z^2-1 ∧ Complex.cosh (2*z)=2*Complex.sinh z^2+1 := by
  rw [Complex.cosh_two_mul]
  constructor
  · linear_combination -(Complex.cosh_sq_sub_sinh_sq z)
  · linear_combination (Complex.cosh_sq_sub_sinh_sq z)

/-- tanh two mul. -/
@[dlmf 4.35.E28]
theorem tanh_two_mul {z : ℂ} (hz : Complex.cosh z≠0) : Complex.tanh (2*z)=2*Complex.tanh z/(1+Complex.tanh z^2) := by
  have hh:=tanh_add hz hz
  simpa only [← two_mul,pow_two] using hh


/-- sinh four mul. -/
@[dlmf 4.35.E31]
theorem sinh_four_mul (z : ℂ) : Complex.sinh (4*z)=4*Complex.sinh z^3*Complex.cosh z+4*Complex.cosh z^3*Complex.sinh z := by
  rw [show 4*z=2*(2*z) by ring, Complex.sinh_two_mul,
    Complex.sinh_two_mul, Complex.cosh_two_mul]
  ring

/-- cosh four mul. -/
@[dlmf 4.35.E32]
theorem cosh_four_mul (z : ℂ) : Complex.cosh (4*z)=Complex.cosh z^4+6*Complex.sinh z^2*Complex.cosh z^2+Complex.sinh z^4 := by
  rw [show 4*z=2*(2*z) by ring, Complex.cosh_two_mul,
    Complex.cosh_two_mul, Complex.sinh_two_mul]
  ring

/-- cosh add sinh int mul. -/
@[dlmf 4.35.E33]
theorem cosh_add_sinh_int_mul (n : ℤ) (z : ℂ) : Complex.cosh ((n:ℂ)*z)+Complex.sinh ((n:ℂ)*z)=(Complex.cosh z+Complex.sinh z)^n ∧ Complex.cosh ((n:ℂ)*z)-Complex.sinh ((n:ℂ)*z)=(Complex.cosh z-Complex.sinh z)^n := by
  constructor
  · rw [Complex.cosh_add_sinh, Complex.cosh_add_sinh, Complex.exp_int_mul]
  · rw [Complex.cosh_sub_sinh, Complex.cosh_sub_sinh, show -((n:ℂ)*z)=(n:ℂ)*(-z) by ring, Complex.exp_int_mul]

/-- sinh cartesian. -/
@[dlmf 4.35.E34]
theorem sinh_cartesian (z : ℂ) : Complex.sinh z=Real.sinh z.re*Real.cos z.im+I*(Real.cosh z.re*Real.sin z.im) := by
  conv_lhs => rw [← Complex.re_add_im z,Complex.sinh_add,Complex.sinh_mul_I,Complex.cosh_mul_I]
  simp only [← Complex.ofReal_sinh,← Complex.ofReal_cosh,← Complex.ofReal_sin,← Complex.ofReal_cos]
  push_cast
  ring


/-- cosh cartesian. -/
@[dlmf 4.35.E35]
theorem cosh_cartesian (z : ℂ) : Complex.cosh z=Real.cosh z.re*Real.cos z.im+I*(Real.sinh z.re*Real.sin z.im) := by
  conv_lhs => rw [← Complex.re_add_im z,Complex.cosh_add,Complex.sinh_mul_I,Complex.cosh_mul_I]
  simp only [← Complex.ofReal_sinh,← Complex.ofReal_cosh,← Complex.ofReal_sin,← Complex.ofReal_cos]
  push_cast
  ring


/-- tanh cartesian. -/
@[dlmf 4.35.E36]
theorem tanh_cartesian (z : ℂ) : Complex.tanh z=((Real.sinh (2*z.re):ℂ)+I*Real.sin (2*z.im))/(Real.cosh (2*z.re)+Real.cos (2*z.im)) := by
  have hDr : Real.cosh (2*z.re)+Real.cos (2*z.im) = 2*((Real.sinh z.re)^2+(Real.cos z.im)^2) := by
    rw [Real.cosh_two_mul, Real.cos_two_mul]
    nlinarith [Real.cosh_sq z.re]
  have hq : 0 ≤ (Real.sinh z.re)^2+(Real.cos z.im)^2 := by positivity
  rw [Complex.tanh_eq_sinh_div_cosh]
  by_cases h0 : (Real.sinh z.re)^2+(Real.cos z.im)^2 = 0
  · have hc : Complex.cosh z = 0 := by
      have hs : Real.sinh z.re = 0 := by nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.cos z.im)]
      have hc0 : Real.cos z.im = 0 := by nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.cos z.im)]
      rw [cosh_cartesian, hs, hc0]; simp
    have : ((Real.cosh (2*z.re):ℂ)+Real.cos (2*z.im)) = 0 := by
      rw [← Complex.ofReal_add, hDr, h0]; simp
    rw [this, hc]; simp
  · have hD0 : ((Real.cosh (2*z.re):ℂ)+Real.cos (2*z.im)) ≠ 0 := by
      rw [← Complex.ofReal_add, hDr]
      exact_mod_cast mul_ne_zero two_ne_zero h0
    have hC0 : Complex.cosh z ≠ 0 := by
      intro h
      rw [cosh_cartesian] at h
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im] at h1 h2
      ring_nf at h1 h2
      have hcy : Real.cos z.im = 0 := by
        rcases mul_eq_zero.mp h1 with h|h
        · exact absurd h (Real.cosh_pos _).ne'
        · exact h
      have hsy : Real.sin z.im ≠ 0 := by
        intro h; have := Real.sin_sq_add_cos_sq z.im; rw [h, hcy] at this; norm_num at this
      have hsx : Real.sinh z.re = 0 := (mul_eq_zero.mp h2).resolve_right hsy
      apply h0; rw [hsx, hcy]; ring
    rw [div_eq_div_iff hC0 hD0, sinh_cartesian, cosh_cartesian]
    rw [Real.cosh_two_mul, Real.cos_two_mul, Real.sinh_two_mul, Real.sin_two_mul]
    have e1 := Real.cosh_sq z.re
    have e2 := Real.sin_sq_add_cos_sq z.im
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    have e1' : ((Real.cosh z.re:ℂ))^2 = (Real.sinh z.re:ℂ)^2+1 := by exact_mod_cast e1
    have e2' : ((Real.sin z.im:ℂ))^2 + (Real.cos z.im:ℂ)^2 = 1 := by exact_mod_cast e2
    generalize (Real.sinh z.re:ℂ) = a at *
    generalize (Real.cosh z.re:ℂ) = b at *
    generalize (Real.cos z.im:ℂ) = c at *
    generalize (Real.sin z.im:ℂ) = s at *
    linear_combination (I*b*s - a*c)*e1' + (-2*I^2*a*c)*e2' + (2*a*c^3 - 2*a*c)*Complex.I_sq

/-- coth cartesian. -/
@[dlmf 4.35.E37]
theorem coth_cartesian (z : ℂ) : coth z=((Real.sinh (2*z.re):ℂ)-I*Real.sin (2*z.im))/(Real.cosh (2*z.re)-Real.cos (2*z.im)) := by
  have hDr : Real.cosh (2*z.re)-Real.cos (2*z.im) = 2*((Real.sinh z.re)^2+(Real.sin z.im)^2) := by
    rw [Real.cosh_two_mul, Real.cos_two_mul]
    nlinarith [Real.cosh_sq z.re, Real.sin_sq_add_cos_sq z.im]
  have hq : 0 ≤ (Real.sinh z.re)^2+(Real.sin z.im)^2 := by positivity
  rw [coth]
  by_cases h0 : (Real.sinh z.re)^2+(Real.sin z.im)^2 = 0
  · have hc : Complex.sinh z = 0 := by
      have hs : Real.sinh z.re = 0 := by nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.sin z.im)]
      have hc0 : Real.sin z.im = 0 := by nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.sin z.im)]
      rw [sinh_cartesian, hs, hc0]; simp
    have : ((Real.cosh (2*z.re):ℂ)-Real.cos (2*z.im)) = 0 := by
      rw [← Complex.ofReal_sub, hDr, h0]; simp
    rw [this, hc]; simp
  · have hD0 : ((Real.cosh (2*z.re):ℂ)-Real.cos (2*z.im)) ≠ 0 := by
      rw [← Complex.ofReal_sub, hDr]
      exact_mod_cast mul_ne_zero two_ne_zero h0
    have hC0 : Complex.sinh z ≠ 0 := by
      intro h
      rw [sinh_cartesian] at h
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im] at h1 h2
      ring_nf at h1 h2
      have hsy : Real.sin z.im = 0 := by
        rcases mul_eq_zero.mp h2 with h|h
        · exact absurd h (Real.cosh_pos _).ne'
        · exact h
      have hcy : Real.cos z.im ≠ 0 := by
        intro h; have := Real.sin_sq_add_cos_sq z.im; rw [h, hsy] at this; norm_num at this
      have hsx : Real.sinh z.re = 0 := (mul_eq_zero.mp h1).resolve_right hcy
      apply h0; rw [hsx, hsy]; ring
    rw [div_eq_div_iff hC0 hD0, sinh_cartesian, cosh_cartesian]
    rw [Real.cosh_two_mul, Real.cos_two_mul, Real.sinh_two_mul, Real.sin_two_mul]
    have e1 := Real.cosh_sq z.re
    have e2 := Real.sin_sq_add_cos_sq z.im
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    have e1' : ((Real.cosh z.re:ℂ))^2 = (Real.sinh z.re:ℂ)^2+1 := by exact_mod_cast e1
    have e2' : ((Real.sin z.im:ℂ))^2 + (Real.cos z.im:ℂ)^2 = 1 := by exact_mod_cast e2
    generalize (Real.sinh z.re:ℂ) = a at *
    generalize (Real.cosh z.re:ℂ) = b at *
    generalize (Real.cos z.im:ℂ) = c at *
    generalize (Real.sin z.im:ℂ) = s at *
    linear_combination (-I*a*s + b*c)*e1' + (2*I^2*b*c)*e2' + (-2*b*c^3 + 2*b*c)*Complex.I_sq

/-- norm sinh cartesian. -/
@[dlmf 4.35.E38]
theorem norm_sinh_cartesian (z : ℂ) : ‖Complex.sinh z‖=Real.sqrt (Real.sinh z.re^2+Real.sin z.im^2) ∧ ‖Complex.sinh z‖=Real.sqrt ((Real.cosh (2*z.re)-Real.cos (2*z.im))/2) := by
  have hn:‖Complex.sin (I*z)‖=‖Complex.sinh z‖ := by
    rw [mul_comm I z,Complex.sin_mul_I,norm_mul,Complex.norm_I,mul_one]
  simpa [hn,Complex.I_mul_re,Complex.I_mul_im,Real.sin_neg,Real.cos_neg,add_comm] using norm_sin_explicit (I*z)


/-- norm cosh cartesian. -/
@[dlmf 4.35.E39]
theorem norm_cosh_cartesian (z : ℂ) : ‖Complex.cosh z‖=Real.sqrt (Real.sinh z.re^2+Real.cos z.im^2) ∧ ‖Complex.cosh z‖=Real.sqrt ((Real.cosh (2*z.re)+Real.cos (2*z.im))/2) := by
  have hn:Complex.cos (I*z)=Complex.cosh z := by rw [mul_comm I z,Complex.cos_mul_I]
  simpa [hn,Complex.I_mul_re,Complex.I_mul_im,Real.cos_neg,add_comm] using norm_cos_explicit (I*z)


/-- norm tanh cartesian. -/
@[dlmf 4.35.E40]
theorem norm_tanh_cartesian (z : ℂ) : ‖Complex.tanh z‖=Real.sqrt ((Real.cosh (2*z.re)-Real.cos (2*z.im))/(Real.cosh (2*z.re)+Real.cos (2*z.im))) := by
  have hp:0≤(Real.cosh (2*z.re)-Real.cos (2*z.im))/2 := by
    rw [Real.cosh_two_mul,Real.cos_two_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq z.re,Real.sin_sq_add_cos_sq z.im,
      sq_nonneg (Real.sin z.im),sq_nonneg (Real.sinh z.re)]
  rw [Complex.tanh_eq_sinh_div_cosh,norm_div,(norm_sinh_cartesian z).2,(norm_cosh_cartesian z).2,← Real.sqrt_div hp]
  congr 1
  exact div_div_div_cancel_right₀ (two_ne_zero : (2:ℝ)≠0) _ _


/-- Two analytic functions on a preconnected open set with equal squares agree everywhere once
they agree at one point where they do not vanish. -/
private lemma hypR4_sq_eq_continuation {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {r s : ℂ → ℂ} (hr : AnalyticOnNhd ℂ r U) (hs : AnalyticOnNhd ℂ s U)
    (hsq : ∀ z ∈ U, r z^2 = s z^2) {x : ℂ} (hx : x ∈ U) (hrx : r x = s x) (hsx : s x ≠ 0) :
    ∀ z ∈ U, r z = s z := by
  have hev : r =ᶠ[𝓝 x] s := by
    have hcont : ContinuousAt (fun z => r z + s z) x := ((hr x hx).add (hs x hx)).continuousAt
    have hne : ∀ᶠ z in 𝓝 x, r z + s z ≠ 0 :=
      hcont.eventually_ne (by rw [hrx, ← two_mul]; exact mul_ne_zero two_ne_zero hsx)
    filter_upwards [hne, hU.mem_nhds hx] with z hz hzU
    have h : (r z - s z)*(r z + s z) = 0 := by linear_combination hsq z hzU
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hz)
  exact fun z hz => hr.eqOn_of_preconnected_of_eventuallyEq hs hc hx hev hz

/-- The half-angle square root selected on the positive real axis and continued analytically. -/
@[dlmf 4.35.E20]
theorem sinh_half_continued_root {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {r : ℂ → ℂ}
    (hr : AnalyticOnNhd ℂ r U) (hsq : ∀ z ∈ U, r z^2=(Complex.cosh z-1)/2)
    {x : ℝ} (hx : 0<x) (hxU : (x:ℂ) ∈ U) (hanchor : r x=Complex.sinh ((x:ℂ)/2))
     :
    ∀ z ∈ U, r z=Complex.sinh (z/2) := by
  have hs : AnalyticOnNhd ℂ (fun z => Complex.sinh (z/2)) U := fun z _ =>
    (Complex.differentiable_sinh.comp (differentiable_id.div_const 2)).analyticAt z
  refine hypR4_sq_eq_continuation hU hc.isPreconnected hr hs
    (fun z hz => by rw [hsq z hz, sinh_half_sq]) hxU hanchor ?_
  rw [show (x:ℂ)/2 = ((x/2:ℝ):ℂ) by push_cast; ring, ← Complex.ofReal_sinh]
  exact_mod_cast (Real.sinh_pos_iff.mpr (by linarith)).ne'

/-- The half-angle square root selected on the positive real axis and continued analytically. -/
@[dlmf 4.35.E21]
theorem cosh_half_continued_root {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {r : ℂ → ℂ}
    (hr : AnalyticOnNhd ℂ r U) (hsq : ∀ z ∈ U, r z^2=(Complex.cosh z+1)/2)
    {x : ℝ} (hx : 0<x) (hxU : (x:ℂ) ∈ U) (hanchor : r x=Complex.cosh ((x:ℂ)/2))
     :
    ∀ z ∈ U, r z=Complex.cosh (z/2) := by
  have hs : AnalyticOnNhd ℂ (fun z => Complex.cosh (z/2)) U := fun z _ =>
    (Complex.differentiable_cosh.comp (differentiable_id.div_const 2)).analyticAt z
  refine hypR4_sq_eq_continuation hU hc.isPreconnected hr hs
    (fun z hz => by rw [hsq z hz, cosh_half_sq]) hxU hanchor ?_
  rw [show (x:ℂ)/2 = ((x/2:ℝ):ℂ) by push_cast; ring, ← Complex.ofReal_cosh]
  exact_mod_cast (Real.cosh_pos _).ne'

/-- The half-angle square root selected on the positive real axis and continued analytically. -/
@[dlmf 4.35.E22]
theorem tanh_half_continued_root {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {r : ℂ → ℂ}
    (hr : AnalyticOnNhd ℂ r U) (hsq : ∀ z ∈ U, r z^2=(Complex.cosh z-1)/(Complex.cosh z+1))
    {x : ℝ} (hx : 0<x) (hxU : (x:ℂ) ∈ U) (hanchor : r x=Complex.tanh ((x:ℂ)/2))
    (hpole : ∀ z ∈ U, Complex.cosh (z/2)≠0) :
    ∀ z ∈ U, r z=Complex.tanh (z/2) := by
  have hs : AnalyticOnNhd ℂ (fun z => Complex.tanh (z/2)) U := by
    intro z hz
    have h1 := (Complex.differentiable_sinh.comp (differentiable_id.div_const 2)).analyticAt z
    have h2 := (Complex.differentiable_cosh.comp (differentiable_id.div_const 2)).analyticAt z
    have hf : (fun z => Complex.tanh (z/2)) =
        (fun z => Complex.sinh (z/2)) / (fun z => Complex.cosh (z/2)) := by
      funext w; simp [Complex.tanh_eq_sinh_div_cosh]
    rw [hf]
    exact h1.div h2 (hpole z hz)
  refine hypR4_sq_eq_continuation hU hc.isPreconnected hr hs
    (fun z hz => by rw [hsq z hz, tanh_half_sq (hpole z hz)]) hxU hanchor ?_
  rw [show (x:ℂ)/2 = ((x/2:ℝ):ℂ) by push_cast; ring, ← Complex.ofReal_tanh]
  have : 0 < Real.tanh (x/2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  exact_mod_cast this.ne'

/-- hasProd sinh. -/
@[dlmf 4.36.E1]
theorem hasProd_sinh (z : ℂ) : HasProd (fun n : ℕ => 1+z^2/(((n+1:ℂ)^2)*π^2)) (sinhc z) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hz0 : z = 0
  · subst hz0; simp [sinhc]
  have hx0 : I*z/π ≠ 0 := by simp [hz0, hπ, Complex.I_ne_zero]
  have hf : (fun n : ℕ => 1+z^2/(((n+1:ℂ)^2)*π^2)) = fun n => 1 + sineTerm (I*z/π) n := by
    funext n; simp only [sineTerm]; congr 1
    have : ((n:ℂ)+1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    linear_combination Complex.I_sq
  rw [hf, (multipliable_sineTerm _).hasProd_iff_tendsto_nat]
  convert tendsto_euler_sin_prod' hx0 using 2
  rw [show (π:ℂ)*(I*z/π) = z*I by field_simp, Complex.sin_mul_I]
  simp only [sinhc, hz0, ↓reduceIte]
  field_simp

/-- hasProd cosh. -/
@[dlmf 4.36.E2]
theorem hasProd_cosh (z : ℂ) : HasProd (fun n : ℕ => 1+4*z^2/(((2*n+1:ℂ)^2)*π^2)) (Complex.cosh z) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  set R : ℝ := ‖z‖+1 with hR
  have hR0 : 0 ≤ R := by positivity
  set K : Set ℂ := Metric.closedBall (0:ℂ) R with hK
  have hzK : z ∈ Metric.ball (0:ℂ) R := by simp [hR]
  have hu : Summable (fun n : ℕ => 4*R^2/(((2*n+1:ℝ))^2*π^2)) := by
    have hs : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using this
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hs.mul_left (4*R^2/π^2))
    have h1 : ((n:ℝ)+1)^2 ≤ (2*n+1)^2 := by nlinarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hp : 0 < π^2 := by positivity
    rw [div_mul_div_comm, mul_one, mul_comm (π^2)]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 hp.le
  have hb : ∀ᶠ n : ℕ in atTop, ∀ x ∈ K,
      ‖4*x^2/(((2*n+1:ℂ)^2)*π^2)‖ ≤ 4*R^2/(((2*n+1:ℝ))^2*π^2) := by
    refine Filter.Eventually.of_forall fun (n : ℕ) (x : ℂ) hx => ?_
    have hx' : ‖x‖ ≤ R := by simpa [hK] using hx
    have e : ‖4*x^2/(((2*n+1:ℂ)^2)*π^2)‖ = 4*‖x‖^2/(((2*n+1:ℝ))^2*π^2) := by
      rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
      have h1 : ‖(2*n+1:ℂ)‖ = 2*n+1 := by
        rw [show (2*n+1:ℂ) = ((2*n+1:ℝ):ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [h1, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
    rw [e]
    gcongr
  have hcts : ∀ n : ℕ, ContinuousOn (fun x : ℂ => 4*x^2/(((2*n+1:ℂ)^2)*π^2)) K :=
    fun n => (by fun_prop : Continuous (fun x : ℂ => 4*x^2/(((2*n+1:ℂ)^2)*π^2))).continuousOn
  have H := Summable.hasProdUniformlyOn_nat_one_add (isCompact_closedBall (0:ℂ) R) hu hb hcts
  set F : ℂ → ℂ := fun x => ∏' i : ℕ, (1+4*x^2/(((2*i+1:ℂ)^2)*π^2)) with hF
  have hFc : ContinuousOn F K := by
    refine H.tendstoUniformlyOn_finsetRange.continuousOn (Filter.Frequently.of_forall fun n => ?_)
    exact continuousOn_finsetProd _ fun i _ => continuousOn_const.add (hcts i)
  have hsinhc2 : ∀ x : ℂ, sinhc (2*x) = sinhc x * Complex.cosh x := by
    intro x
    by_cases hx : x = 0
    · simp [sinhc, hx]
    · have h2 : 2*x ≠ 0 := mul_ne_zero two_ne_zero hx
      simp only [sinhc, hx, h2, ↓reduceIte, Complex.sinh_two_mul]
      field_simp
  have hgood : ∀ x ∈ K, sinhc x ≠ 0 → F x = Complex.cosh x := by
    intro x hx hs
    have h1 := H.hasProd hx
    have h2 := hasProd_sinh x
    have h3 := hasProd_sinh (2*x)
    have h4 : HasProd (fun k : ℕ => 1+(2*x)^2/(((k+1:ℂ)^2)*π^2)) (F x * sinhc x) := by
      refine HasProd.even_mul_odd ?_ ?_
      · convert h1 using 2 with k
        push_cast; ring
      · convert h2 using 2 with k
        have : (k:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        rw [show (((2*k+1:ℕ):ℂ)+1) = 2*((k:ℂ)+1) by push_cast; ring]
        field_simp
    have := h4.unique h3
    rw [hsinhc2, mul_comm] at this
    exact mul_left_cancel₀ hs this
  have hFz : F z = Complex.cosh z := by
    by_cases hs : sinhc z ≠ 0
    · exact hgood z (Metric.ball_subset_closedBall hzK) hs
    push Not at hs
    have hz0 : z ≠ 0 := by intro h; simp [sinhc, h] at hs
    have hsh : Complex.sinh z = 0 := by
      simp only [sinhc, hz0, ↓reduceIte] at hs
      exact (div_eq_zero_iff.mp hs).resolve_right hz0
    have hch : Complex.cosh z ≠ 0 := by
      intro h
      have := Complex.cosh_sq_sub_sinh_sq z
      rw [h, hsh] at this; norm_num at this
    have hlim : Tendsto (fun t : ℝ => z+t) (𝓝[≠] 0) (𝓝 z) := by
      have : Tendsto (fun t : ℝ => z+t) (𝓝 0) (𝓝 (z+((0:ℝ):ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hK : K ∈ 𝓝 z := Metric.closedBall_mem_nhds_of_mem hzK
    have hA := ((hFc.continuousAt hK).tendsto).comp hlim
    have hB := ((Complex.continuous_cosh.continuousAt (x := z)).tendsto).comp hlim
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0, F (z+t) = Complex.cosh (z+t) := by
      have hin : ∀ᶠ t : ℝ in 𝓝[≠] 0, z+(t:ℂ) ∈ K := hlim.eventually (Filter.mem_of_superset hK
        (fun w hw => hw)) |>.mono fun t ht => ht
      filter_upwards [hin, self_mem_nhdsWithin] with t ht ht0
      apply hgood _ ht
      have hsh' : Complex.sinh (z+t) ≠ 0 := by
        rw [Complex.sinh_add, hsh, zero_mul, zero_add]
        refine mul_ne_zero hch ?_
        rw [← Complex.ofReal_sinh]
        exact_mod_cast fun h => ht0 (Real.sinh_eq_zero.mp h)
      by_cases h0 : z+(t:ℂ) = 0
      · simp [sinhc, h0]
      · simp only [sinhc, h0, ↓reduceIte]
        exact div_ne_zero hsh' h0
    exact tendsto_nhds_unique (hA.congr' (hev.mono fun t ht => by simp [Function.comp, ht])) hB
  have := H.hasProd (Metric.ball_subset_closedBall hzK)
  rw [hFz] at this
  exact this

/-- Off the imaginary lattice `πiℤ`, the rotated point `iz/π` avoids the integers. -/
private lemma hypR4_rot_mem {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) :
    I*z/π ∈ Complex.integerComplement := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rintro ⟨n, hn⟩
  apply hz (-n)
  have h : I*z = (n:ℂ)*π := by rw [hn]; field_simp
  push_cast
  linear_combination (-I)*h + z*Complex.I_sq

/-- The Mittag-Leffler cotangent term at the rotated point `iz/π`. -/
private lemma hypR4_cotTerm_rot {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) (n : ℕ) :
    cotTerm (I*z/π) n = (-2*I*z*π)*(1/(z^2+(n+1:ℂ)^2*π^2)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : I*z - (n+1)*π ≠ 0 := by
    intro h; apply hz (-(n+1:ℤ)); push_cast
    linear_combination (-I)*h + z*Complex.I_sq
  have h2 : I*z + (n+1)*π ≠ 0 := by
    intro h; apply hz ((n+1:ℤ)); push_cast
    linear_combination (-I)*h + z*Complex.I_sq
  have h3 : z^2+(n+1:ℂ)^2*π^2 ≠ 0 := by
    intro h; apply mul_ne_zero h1 h2
    linear_combination -h + z^2*Complex.I_sq
  have e1 : I*z/π - (n+1) = (I*z - (n+1)*π)/π := by field_simp
  have e2 : I*z/π + (n+1) = (I*z + (n+1)*π)/π := by field_simp
  simp only [cotTerm]
  rw [e1, e2]
  field_simp
  linear_combination 2*I*z^3 * Complex.I_sq

/-- hasSum coth. -/
@[dlmf 4.36.E3]
theorem hasSum_coth_partialFractions {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) : HasSum (fun n : ℕ => 1/(z^2+(n+1:ℂ)^2*π^2)) ((coth z-z⁻¹)/(2*z)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz0 : z ≠ 0 := by simpa using hz 0
  have hs : Complex.sinh z ≠ 0 := fun h => by
    obtain ⟨k, hk⟩ := (sinh_zeros z).mp h; exact hz k hk
  have hc := (Complex.hasSum_cotTerm (hypR4_rot_mem hz)).div_const (-2*I*z*π)
  have hk : (-2*I*z*π) ≠ 0 := by simp [hz0, hπ, Complex.I_ne_zero]
  convert hc using 1
  · funext n; rw [hypR4_cotTerm_rot hz n]; field_simp
  · rw [show (π:ℂ)*(I*z/π) = z*I by field_simp, Complex.cot, Complex.cos_mul_I,
      Complex.sin_mul_I, coth]
    field_simp
    linear_combination (Complex.cosh z*z - Complex.sinh z) * Complex.I_sq

/-- hasSum csch sq. -/
@[dlmf 4.36.E4]
theorem hasSum_csch_sq {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) : HasSum (fun n : ℤ => 1/(z-(n:ℂ)*π*I)^2) (csch z^2) := by
  sorry

/-- hasSum csch. -/
@[dlmf 4.36.E5]
theorem hasSum_csch_partialFractions {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) : HasSum (fun n : ℕ => (-1:ℂ)^(n+1)/(z^2+(n+1:ℂ)^2*π^2)) ((csch z-z⁻¹)/(2*z)) := by
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz0 : z ≠ 0 := by simpa using hz 0
  have hs : Complex.sinh z ≠ 0 := fun h => by
    obtain ⟨k, hk⟩ := (sinh_zeros z).mp h; exact hz k hk
  have hc := (Complex.hasSum_csc_partial_fraction (hypR4_rot_mem hz)).div_const (-2*I*z*π)
  have hk : (-2*I*z*π) ≠ 0 := by simp [hz0, hπ, Complex.I_ne_zero]
  convert hc using 1
  · funext n; rw [hypR4_cotTerm_rot hz n]; field_simp
  · rw [show (π:ℂ)*(I*z/π) = z*I by field_simp, Complex.sin_mul_I, csch]
    field_simp
    linear_combination (z - Complex.sinh z) * Complex.I_sq

/-- A path integral with the square root continued from its value 1 at the origin. -/
def IsArcsinhPathValue (z w : ℂ) : Prop := ∃ γ r : ℝ → ℂ,
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧ ContinuousOn r (Icc 0 1) ∧ r 0=1 ∧
  (∀ s ∈ Icc (0:ℝ) 1, γ s≠I ∧ γ s≠ -I ∧ r s^2=1+γ s^2) ∧
  IntervalIntegrable (fun s => deriv γ s/r s) volume 0 1 ∧
  (∫ s : ℝ in 0..1, deriv γ s/r s)=w
/-- A path integral with the square root selected on an initial positive-real segment. -/
def IsArccoshPathValue (z w : ℂ) : Prop := ∃ γ r : ℝ → ℂ,
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=1 ∧ γ 1=z ∧ ContinuousOn r (Icc 0 1) ∧ r 0=0 ∧
  (∀ s ∈ Ioc (0:ℝ) 1, γ s≠1 ∧ γ s≠ -1 ∧ r s^2=γ s^2-1) ∧
  (∃ ε ∈ Ioc (0:ℝ) 1, ∀ s ∈ Ioo (0:ℝ) ε,
    (γ s).im=0 ∧ 1<(γ s).re ∧ r s=Complex.sqrt (γ s^2-1)) ∧
  IntervalIntegrable (fun s => deriv γ s/r s) volume 0 1 ∧
  (∫ s : ℝ in 0..1, deriv γ s/r s)=w
/-- The inverse-tanh path integral, avoiding the two logarithmic branch points. -/
def IsArctanhPathValue (z w : ℂ) : Prop := ∃ γ : ℝ → ℂ,
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧
  (∀ s ∈ Icc (0:ℝ) 1, γ s≠1 ∧ γ s≠ -1) ∧
  IntervalIntegrable (fun s => deriv γ s/(1-γ s^2)) volume 0 1 ∧
  (∫ s : ℝ in 0..1, deriv γ s/(1-γ s^2))=w
/-- The multivalued inverse defined by all admissible continued-branch path integrals. -/
@[dlmf 4.37.E1]
theorem arcsinh_path_values {z : ℂ} (hz : z≠I ∧ z≠ -I) : {w | IsArcsinhPathValue z w}=arcsinhValues z := by
  sorry

/-- The multivalued inverse defined by all admissible continued-branch path integrals. -/
@[dlmf 4.37.E2]
theorem arccosh_path_values {z : ℂ} (hz : z≠1 ∧ z≠ -1) : {w | IsArccoshPathValue z w}=arccoshValues z := by
  sorry

/-- The multivalued inverse defined by all admissible continued-branch path integrals. -/
@[dlmf 4.37.E3]
theorem arctanh_path_values {z : ℂ} (hz : z≠1 ∧ z≠ -1) : {w | IsArctanhPathValue z w}=arctanhValues z := by
  sorry

/-- arccsch values inv. -/
@[dlmf 4.37.E4]
theorem arccsch_values_inv {z : ℂ} (hz : z≠0) : arccschValues z=arcsinhValues z⁻¹ := by
  ext w
  change (Complex.sinh w≠0 ∧ (Complex.sinh w)⁻¹=z) ↔ Complex.sinh w=z⁻¹
  constructor
  · intro h
    simpa only [inv_inv] using congrArg Inv.inv h.2
  · intro h
    exact ⟨by simpa only [h] using inv_ne_zero hz,by simp only [h,inv_inv]⟩


/-- arcsech values inv. -/
@[dlmf 4.37.E5]
theorem arcsech_values_inv {z : ℂ} (hz : z≠0) : arcsechValues z=arccoshValues z⁻¹ := by
  ext w
  change (Complex.cosh w≠0 ∧ (Complex.cosh w)⁻¹=z) ↔ Complex.cosh w=z⁻¹
  constructor
  · intro h
    simpa only [inv_inv] using congrArg Inv.inv h.2
  · intro h
    exact ⟨by simpa only [h] using inv_ne_zero hz,by simp only [h,inv_inv]⟩


/-- arccoth values inv. -/
@[dlmf 4.37.E6]
theorem arccoth_values_inv {z : ℂ} (hz : z≠0) : arccothValues z=arctanhValues z⁻¹ := by
  ext w
  change (Complex.sinh w≠0 ∧ coth w=z) ↔ Complex.cosh w≠0 ∧ Complex.tanh w=z⁻¹
  rw [coth_eq_inv_tanh]
  constructor
  · rintro ⟨hs,ht⟩
    have ht0:Complex.tanh w≠0 := by
      intro h
      apply hz
      simpa [h] using ht.symm
    refine ⟨?_,?_⟩
    · intro h; exact ht0 (by simp [Complex.tanh,h])
    · simpa only [inv_inv] using congrArg Inv.inv ht
  · rintro ⟨hc,ht⟩
    refine ⟨?_,by simp only [ht,inv_inv]⟩
    intro h
    have hh:(z⁻¹:ℂ)=0 := by simpa [Complex.tanh,h] using ht.symm
    exact inv_ne_zero hz hh


/-- arccoth eq inv. -/
@[dlmf 4.37.E9]
theorem arccoth_eq_inv {z : ℂ} (hz : z≠0) : arccoth z=arctanh z⁻¹ := by
  simp [arccoth,hz]

/-- A chosen hyperbolic cosine value lifts a sine value to a compatible logarithm branch.
This uses Mathlib's principal logarithm and hyperbolic exponential definitions. -/
private lemma hyper_sinh_cosh_log_lift (u s : ℂ) (hs : s^2=1+u^2) :
    Complex.sinh (Complex.log (s+u))=u ∧ Complex.cosh (Complex.log (s+u))=s := by
  have hprod:(s+u)*(s-u)=1 := by linear_combination hs
  have hne:s+u≠0 := by
    intro h
    rw [h,zero_mul] at hprod
    exact zero_ne_one hprod
  have hinv:(s+u)⁻¹=s-u := by
    apply mul_left_cancel₀ hne
    rw [mul_inv_cancel₀ hne,hprod]
  rw [Complex.sinh,Complex.cosh,Complex.exp_log hne,Complex.exp_neg,Complex.exp_log hne,hinv]
  constructor <;> ring

/-- The factored principal square root in inverse cosh has its prescribed square. -/
private lemma hyper_arccosh_root_sq (z : ℂ) :
    (Complex.sqrt (z-1)*Complex.sqrt (z+1))^2=z^2-1 := by
  rw [mul_pow,trig_sqrt_sq,trig_sqrt_sq]
  ring

/-- The logarithmic inverse-cosh definition is a right inverse even at its cut values. -/
private lemma hyper_cosh_arccosh (z : ℂ) : Complex.cosh (arccosh z)=z := by
  have hs:z^2=1+(Complex.sqrt (z-1)*Complex.sqrt (z+1))^2 := by
    rw [hyper_arccosh_root_sq]
    ring
  exact (hyper_sinh_cosh_log_lift _ z hs).2

/-- Compatible inverse-sinh/cosh branches are characterized by their two shared roots. -/
private lemma hyper_mixed_inverse_fiber (u v σ : ℂ) (hσ : σ=1 ∨ σ= -1) :
    Set.image2 (fun a b : ℂ=>a+σ*b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
        Complex.sinh w=u*v+σ*(r*s) ∧ Complex.cosh w=v*r+σ*(u*s)} := by
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change Complex.sinh a=u at ha
    change Complex.cosh b=v at hb
    refine ⟨Complex.cosh a,Complex.sinh b,?_,?_,?_,?_⟩
    · rw [Complex.cosh_sq,ha] <;> ring
    · rw [Complex.sinh_sq,hb]
    · rcases hσ with rfl|rfl <;>
        simp [Complex.sinh_add,Complex.sinh_neg,Complex.cosh_neg,ha,hb] <;> ring
    · rcases hσ with rfl|rfl <;>
        simp [Complex.cosh_add,Complex.sinh_neg,Complex.cosh_neg,ha,hb] <;> ring
  · rintro ⟨r,s,hr,hs,hw,hc⟩
    have ha:=hyper_sinh_cosh_log_lift u r hr
    let a:=Complex.log (r+u)
    refine ⟨a,ha.1,σ*(w-a),?_,?_⟩
    · change Complex.cosh (σ*(w-a))=v
      rcases hσ with rfl|rfl <;> simp only [one_mul,neg_one_mul,Complex.cosh_neg] <;>
        rw [Complex.cosh_sub,ha.1,ha.2,hw,hc] <;> linear_combination v*hr
    · rcases hσ with rfl|rfl <;> ring

/-- The logarithmic inverse sinh is a right inverse also at the cut and branch points. -/
private lemma hyper_sinh_arcsinh (z:ℂ) : Complex.sinh (arcsinh z)=z := by
  exact (hyper_sinh_cosh_log_lift z (Complex.sqrt (z^2+1))
    (by rw [trig_sqrt_sq];ring)).1

/-- Rotation of Mathlib's two sine fibers preserves the integer branch parity. -/
private lemma hyper_sinh_fiber_forms (A w:ℂ) :
    Complex.sinh w=Complex.sinh A ↔
      ∃ k:ℤ,w=(-1:ℂ)^k*A+(k:ℂ)*π*I := by
  have hrot : Complex.sinh w=Complex.sinh A ↔
      Complex.sin (A*I)=Complex.sin (w*I) := by
    rw [Complex.sin_mul_I,Complex.sin_mul_I]
    constructor
    · intro h;rw [h]
    · intro h
      exact (mul_right_cancel₀ Complex.I_ne_zero h).symm
  rw [hrot,Complex.sin_eq_sin_iff]
  constructor
  · rintro ⟨k,hk|hk⟩
    · have he:Even (-2*k:ℤ) := ⟨-k,by ring⟩
      refine ⟨-2*k,?_⟩
      rw [he.neg_one_zpow]
      push_cast
      linear_combination -I*hk+(w-A)*Complex.I_sq
    · have ho:Odd (-(2*k+1):ℤ) := ⟨-k-1,by ring⟩
      refine ⟨-(2*k+1),?_⟩
      rw [ho.neg_one_zpow]
      push_cast
      linear_combination -I*hk+(w+A)*Complex.I_sq
  · rintro ⟨n,hn⟩
    obtain ⟨k,hk|hk⟩:=Int.even_or_odd' n
    · have he:Even (2*k:ℤ) := ⟨k,by ring⟩
      rw [hk,he.neg_one_zpow] at hn
      refine ⟨-k,Or.inl ?_⟩
      push_cast at hn ⊢
      linear_combination I*hn+(2*k*π)*Complex.I_sq
    · have ho:Odd (2*k+1:ℤ) := ⟨k,by ring⟩
      rw [hk,ho.neg_one_zpow] at hn
      refine ⟨-k-1,Or.inr ?_⟩
      push_cast at hn ⊢
      linear_combination I*hn+((2*k+1)*π)*Complex.I_sq

/-- Rotation identifies the chosen logarithm/square-root inverse with the trigonometric one. -/
private lemma hyper_arcsinh_rotation (z:ℂ) : arcsinh z=I*arcsinPrincipal (-I*z) := by
  have hq:1-(-I*z)^2=z^2+1 := by linear_combination -z^2*Complex.I_sq
  have hi:I*(-I*z)=z := by linear_combination -z*Complex.I_sq
  unfold arcsinh arcsinPrincipal
  rw [hq,hi]
  linear_combination Complex.log (Complex.sqrt (z^2+1)+z)*Complex.I_sq

/-- Rotation maps the inverse-sinh cut plane to the inverse-sine cut plane. -/
private lemma hyper_asinh_coord {z:ℂ} (hz:z∈arcsinhDomain) : -I*z∈arcsinCutPlane := by
  simpa [arcsinhDomain,arcsinCutPlane,Complex.mul_re,Complex.mul_im] using hz

/-- The inverse-sinh derivative follows from the proved rotated inverse-sine derivative. -/
private lemma hyper_hasDerivAt_arcsinh {z:ℂ} (hz:z∈arcsinhDomain) :
    HasDerivAt arcsinh (Complex.sqrt (1+z^2))⁻¹ z := by
  have hd:=((hasDerivAt_arcsin_principal (hyper_asinh_coord hz)).comp z
    ((hasDerivAt_id z).const_mul (-I))).const_mul I
  convert hd using 1
  · ext w
    exact hyper_arcsinh_rotation w
  · have hq:1-(-I*z)^2=1+z^2 := by linear_combination -z^2*Complex.I_sq
    rw [hq]
    linear_combination (Complex.sqrt (1+z^2))⁻¹*Complex.I_sq

/-- The two logarithm factors multiply to one, including the square-root cut. -/
private lemma hyper_asinh_product (z:ℂ) :
    (Complex.sqrt (z^2+1)+z)*(Complex.sqrt (z^2+1)-z)=1 := by
  linear_combination trig_sqrt_sq (z^2+1)

/-- The inverse-sinh logarithm argument is nonzero. -/
private lemma hyper_asinh_log_ne (z:ℂ) : Complex.sqrt (z^2+1)+z≠0 := by
  intro h
  have hp:=hyper_asinh_product z
  rw [h,zero_mul] at hp
  exact zero_ne_one hp

/-- The inverse-sinh logarithm argument avoids the negative real axis. -/
private lemma hyper_asinh_log_slit (z:ℂ) : Complex.sqrt (z^2+1)+z∈Complex.slitPlane := by
  let r:=Complex.sqrt (z^2+1)
  change r+z∈Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  by_cases hi:(r+z).im≠0
  · exact Or.inr hi
  · left
    have him:r.im= -z.im := by
      have hi0:(r+z).im=0 := not_ne_iff.mp hi
      simp only [Complex.add_im] at hi0
      linarith
    have hr:0≤r.re := by
      dsimp [r]
      rw [Complex.sqrt,Complex.cpow_inv_two_re]
      positivity
    have hp:=congrArg Complex.re (hyper_asinh_product z)
    change ((r+z)*(r-z)).re=1 at hp
    simp only [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.add_im,Complex.sub_im,him] at hp
    simp only [Complex.add_re]
    nlinarith

/-- The inverse-tanh Möbius argument lies in the principal logarithm cut plane. -/
private lemma hyper_atanh_slit {z:ℂ} (hz:z∈arctanhDomain) : (1+z)/(1-z)∈Complex.slitPlane := by
  have hre:((1+z)/(1-z)).re=(1-z.re^2-z.im^2)/((1-z.re)^2+z.im^2) := by
    simp [Complex.div_re,Complex.normSq]
    ring
  have him:((1+z)/(1-z)).im=(2*z.im)/((1-z.re)^2+z.im^2) := by
    simp [Complex.div_im,Complex.normSq]
    ring
  rw [Complex.mem_slitPlane_iff]
  by_cases hi:z.im≠0
  · right
    rw [him]
    have hD:0<(1-z.re)^2+z.im^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hi)
    exact div_ne_zero (mul_ne_zero two_ne_zero hi) hD.ne'
  · left
    have hi0:z.im=0 := not_ne_iff.mp hi
    have hx:|z.re|<1 := hz.resolve_left hi
    rw [hre,hi0]
    have hp:0<1-z.re := by linarith [(abs_lt.mp hx).2]
    apply div_pos
    · nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
    · positivity

/-- Neither linear factor vanishes on the inverse-tanh cut plane. -/
private lemma hyper_atanh_nonzero {z:ℂ} (hz:z∈arctanhDomain) : 1+z≠0 ∧ 1-z≠0 := by
  constructor
  · intro h
    have he:z= -1 := by linear_combination h
    rw [he] at hz
    norm_num [arctanhDomain] at hz
  · intro h
    have he:z=1 := by linear_combination -h
    rw [he] at hz
    norm_num [arctanhDomain] at hz

/-- Differentiate the principal inverse-tanh logarithm on its full cut plane. -/
private lemma hyper_hasDerivAt_arctanh {z:ℂ} (hz:z∈arctanhDomain) :
    HasDerivAt arctanh (1/(1-z^2)) z := by
  obtain ⟨hp,hm⟩:=hyper_atanh_nonzero hz
  have hd0:=((hasDerivAt_id z).const_add 1).div ((hasDerivAt_id z).const_sub 1) hm
  have hd:=((Complex.hasDerivAt_log (hyper_atanh_slit hz)).comp z hd0).div_const 2
  convert hd using 1
  · rfl
  · dsimp only [id]
    have hfac:(1+z)*(1-z)=1-z^2 := by ring
    rw [← hfac]
    field_simp [hp,hm]
    ring

/-- Inversion maps the inverse-coth cut plane into the inverse-tanh cut plane. -/
private lemma hyper_acoth_inv_mem {z:ℂ} (hz:z∈arccothDomain) : z≠0 ∧ z⁻¹∈arctanhDomain := by
  have hz0:z≠0 := by intro h;rw [h] at hz;norm_num [arccothDomain] at hz
  refine ⟨hz0,?_⟩
  by_cases hi:z.im≠0
  · left
    rw [Complex.inv_im]
    have hn:Complex.normSq z≠0 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz0)
    exact div_ne_zero (neg_ne_zero.mpr hi) hn
  · right
    have hi0:z.im=0 := not_ne_iff.mp hi
    have hx:1 < |z.re| := hz.resolve_left hi
    have he:z=(z.re:ℂ) := by apply Complex.ext <;> simp [hi0]
    rw [he,← Complex.ofReal_inv,Complex.ofReal_re,abs_inv]
    exact inv_lt_one_of_one_lt₀ hx

/-- The principal complex square root agrees with the nonnegative real square root. -/
private lemma hyper_sqrt_ofReal (x:ℝ) (hx:0≤x) : Complex.sqrt (x:ℂ)=(Real.sqrt x:ℂ) := by
  exact Complex.sqrt_of_nonneg (by exact_mod_cast hx)

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arcsinh_analytic  : AnalyticOnNhd ℂ arcsinh arcsinhDomain := by
  have hU:IsOpen arcsinhDomain := by
    change IsOpen ({z:ℂ | z.re≠0}∪{z:ℂ | |z.im|<1})
    exact (isOpen_ne.preimage Complex.continuous_re).union
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  exact (show DifferentiableOn ℂ arcsinh arcsinhDomain from fun z hz=>
    (hyper_hasDerivAt_arcsinh hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU


/-- Both linear factors of the factored inverse-cosh root lie in the principal slit plane. -/
private lemma hypR4_acosh_slit {z : ℂ} (hz : z ∈ arccoshDomain) :
    z-1 ∈ Complex.slitPlane ∧ z+1 ∈ Complex.slitPlane := by
  rcases hz with hi | hr
  · exact ⟨Or.inr (by simpa using hi), Or.inr (by simpa using hi)⟩
  · exact ⟨Or.inl (by simp; linarith), Or.inl (by simp; linarith)⟩

/-- The factored inverse-cosh root does not vanish on the open domain. -/
private lemma hypR4_acosh_root_ne {z : ℂ} (hz : z ∈ arccoshDomain) :
    Complex.sqrt (z-1)*Complex.sqrt (z+1) ≠ 0 := by
  intro h
  have hs := hyper_arccosh_root_sq z
  rw [h, zero_pow two_ne_zero] at hs
  have h1 : (z-1)*(z+1) = 0 := by linear_combination -hs
  rcases mul_eq_zero.mp h1 with h1 | h1
  · have : z = 1 := by linear_combination h1
    subst this; rcases hz with h | h <;> simp at h
  · have : z = -1 := by linear_combination h1
    subst this; rcases hz with h | h <;> norm_num at h

/-- The inverse-cosh logarithm argument lies in the principal slit plane on the open domain. -/
private lemma hypR4_acosh_log_slit {z : ℂ} (hz : z ∈ arccoshDomain) :
    z+Complex.sqrt (z-1)*Complex.sqrt (z+1) ∈ Complex.slitPlane := by
  set s := Complex.sqrt (z-1)*Complex.sqrt (z+1)
  have hprod : (z+s)*(z-s) = 1 := by
    have := hyper_arccosh_root_sq z; linear_combination -this
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  have hre' := congrArg Complex.re hprod
  have him' := congrArg Complex.im hprod
  simp only [Complex.mul_re, Complex.mul_im, him, Complex.one_re, Complex.one_im] at hre' him'
  simp only [sub_zero, zero_mul, add_zero] at hre' him'
  have hg0 : (z+s).re ≠ 0 := by intro h; rw [h, zero_mul] at hre'; exact zero_ne_one hre'
  have hh_im : (z-s).im = 0 := by
    rcases mul_eq_zero.mp him' with h | h
    · exact absurd h hg0
    · exact h
  have hgneg : (z+s).re < 0 := lt_of_le_of_ne hre hg0
  have hh_re : (z-s).re < 0 := by
    by_contra hc; push Not at hc; nlinarith
  have hzre : z.re = ((z+s).re + (z-s).re)/2 := by simp
  have hzim : z.im = ((z+s).im + (z-s).im)/2 := by simp
  rcases hz with hi | hr
  · apply hi; rw [hzim, him, hh_im]; ring
  · linarith

/-- The derivative of the principal inverse cosh on its open domain. -/
private lemma hypR4_hasDerivAt_arccosh {z : ℂ} (hz : z ∈ arccoshDomain) :
    HasDerivAt arccosh ((Complex.sqrt (z-1)*Complex.sqrt (z+1))⁻¹) z := by
  obtain ⟨h1, h2⟩ := hypR4_acosh_slit hz
  have hs := hypR4_acosh_root_ne hz
  have hg := hypR4_acosh_log_slit hz
  have hA : Complex.sqrt (z-1) ≠ 0 := fun h => hs (by rw [h, zero_mul])
  have hB : Complex.sqrt (z+1) ≠ 0 := fun h => hs (by rw [h, mul_zero])
  have dA : HasDerivAt (fun w => Complex.sqrt (w-1)) ((Complex.sqrt (z-1))⁻¹/2) z := by
    have := (Complex.hasDerivAt_sqrt h1).comp z ((hasDerivAt_id z).sub_const 1)
    simpa only [Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹:ℂ) by norm_num, Complex.cpow_neg, mul_one,
      Function.comp_def, id] using this
  have dB : HasDerivAt (fun w => Complex.sqrt (w+1)) ((Complex.sqrt (z+1))⁻¹/2) z := by
    have := (Complex.hasDerivAt_sqrt h2).comp z ((hasDerivAt_id z).add_const 1)
    simpa only [Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹:ℂ) by norm_num, Complex.cpow_neg, mul_one,
      Function.comp_def, id] using this
  have hd := (Complex.hasDerivAt_log hg).comp z ((hasDerivAt_id z).add (dA.mul dB))
  have hg0 : z+Complex.sqrt (z-1)*Complex.sqrt (z+1) ≠ 0 := Complex.slitPlane_ne_zero hg
  have key : (z+Complex.sqrt (z-1)*Complex.sqrt (z+1))⁻¹ *
      (1 + ((Complex.sqrt (z-1))⁻¹/2*Complex.sqrt (z+1) + Complex.sqrt (z-1)*((Complex.sqrt (z+1))⁻¹/2)))
      = (Complex.sqrt (z-1)*Complex.sqrt (z+1))⁻¹ := by
    have eA := trig_sqrt_sq (z-1)
    have eB := trig_sqrt_sq (z+1)
    generalize Complex.sqrt (z-1) = A at *
    generalize Complex.sqrt (z+1) = B at *
    field_simp
    linear_combination eA + eB
  rw [← key]
  exact hd

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arccosh_analytic  : AnalyticOnNhd ℂ arccosh arccoshDomain := by
  have hU : IsOpen arccoshDomain := by
    change IsOpen ({z:ℂ | z.im≠0}∪{z:ℂ | 1<z.re})
    exact (isOpen_ne.preimage Complex.continuous_im).union
      (isOpen_lt continuous_const Complex.continuous_re)
  exact (show DifferentiableOn ℂ arccosh arccoshDomain from fun z hz =>
    (hypR4_hasDerivAt_arccosh hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arctanh_analytic  : AnalyticOnNhd ℂ arctanh arctanhDomain := by
  have hU:IsOpen arctanhDomain := by
    change IsOpen ({z:ℂ | z.im≠0}∪{z:ℂ | |z.re|<1})
    exact (isOpen_ne.preimage Complex.continuous_im).union
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const)
  exact (show DifferentiableOn ℂ arctanh arctanhDomain from fun z hz=>
    (hyper_hasDerivAt_arctanh hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU


/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arccsch_analytic  : AnalyticOnNhd ℂ arccsch arccschDomain := by
  intro z hz
  exact (arcsinh_analytic _ hz.2).comp (analyticAt_id.inv hz.1)


/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arcsech_analytic  : AnalyticOnNhd ℂ arcsech arcsechDomain := by
  intro z hz
  exact (arccosh_analytic _ hz.2).comp (analyticAt_id.inv hz.1)

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arccoth_analytic  : AnalyticOnNhd ℂ arccoth arccothDomain := by
  intro z hz
  obtain ⟨hz0,hi⟩:=hyper_acoth_inv_mem hz
  have hh:AnalyticAt ℂ (fun w=>arctanh w⁻¹) z :=
    (arctanh_analytic _ hi).comp (analyticAt_id.inv hz0)
  apply hh.congr
  filter_upwards [eventually_ne_nhds hz0] with w hw
  exact (arccoth_eq_inv hw).symm


/-- A right inverse `g (f z) = z` of an entire `g` cannot be analytic at a point where `g'` vanishes. -/
private lemma hypR4_not_analytic_of_right_inv {f g g' : ℂ → ℂ} {p : ℂ}
    (hinv : ∀ z, g (f z) = z) (hg : ∀ w, HasDerivAt g (g' w) w) (h0 : g' (f p) = 0) :
    ¬AnalyticAt ℂ f p := by
  intro ha
  have hd := (hg (f p)).comp p ha.differentiableAt.hasDerivAt
  have hid : HasDerivAt (g ∘ f) 1 p := by
    have : g ∘ f = id := funext hinv
    rw [this]; exact hasDerivAt_id p
  have := hd.unique hid
  rw [h0, zero_mul] at this
  exact zero_ne_one this

/-- The principal inverse tanh is not continuous at `±1`, where `exp (2 arctanh z)` has a pole
or a zero. -/
private lemma hypR4_arctanh_exp (z : ℂ) (h1 : z ≠ 1) (h2 : z ≠ -1) :
    Complex.exp (2*arctanh z)*(1-z) = 1+z := by
  have hm : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hp : 1+z ≠ 0 := by intro h; apply h2; linear_combination h
  rw [arctanh, show 2*(Complex.log ((1+z)/(1-z))/2) = Complex.log ((1+z)/(1-z)) by ring,
    Complex.exp_log (div_ne_zero hp hm)]
  field_simp

/-- The two inverse branch points stated in the definition prose. -/
theorem arcsinh_branch_points  : ¬AnalyticAt ℂ arcsinh I ∧ ¬AnalyticAt ℂ arcsinh (-I) := by
  have hc : ∀ w, Complex.cosh (arcsinh w)^2 = 1+w^2 := fun w => by
    rw [Complex.cosh_sq, hyper_sinh_arcsinh]; ring
  constructor
  · refine hypR4_not_analytic_of_right_inv hyper_sinh_arcsinh Complex.hasDerivAt_sinh ?_
    have := hc I; rw [Complex.I_sq] at this
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [this]; ring)
  · refine hypR4_not_analytic_of_right_inv hyper_sinh_arcsinh Complex.hasDerivAt_sinh ?_
    have := hc (-I); rw [neg_sq, Complex.I_sq] at this
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [this]; ring)

/-- The two inverse branch points stated in the definition prose. -/
theorem arccosh_branch_points  : ¬AnalyticAt ℂ arccosh (1:ℂ) ∧ ¬AnalyticAt ℂ arccosh (-(1:ℂ)) := by
  have hc : ∀ w, Complex.sinh (arccosh w)^2 = w^2-1 := fun w => by
    rw [Complex.sinh_sq, hyper_cosh_arccosh]
  constructor
  · refine hypR4_not_analytic_of_right_inv hyper_cosh_arccosh Complex.hasDerivAt_cosh ?_
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [hc]; ring)
  · refine hypR4_not_analytic_of_right_inv hyper_cosh_arccosh Complex.hasDerivAt_cosh ?_
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [hc]; ring)

/-- The two inverse branch points stated in the definition prose. -/
theorem arctanh_branch_points  : ¬AnalyticAt ℂ arctanh (1:ℂ) ∧ ¬AnalyticAt ℂ arctanh (-(1:ℂ)) := by
  constructor
  · intro ha
    have hcont : ContinuousAt (fun z => Complex.exp (2*arctanh z)*(1-z)) 1 :=
      ((ha.continuousAt.const_mul 2).cexp).mul (continuousAt_const.sub continuousAt_id)
    have hlim : Tendsto (fun z => Complex.exp (2*arctanh z)*(1-z)) (𝓝[≠] 1) (𝓝 0) := by
      have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(1:ℂ)}ᶜ))
      simpa using this
    have hlim2 : Tendsto (fun z => Complex.exp (2*arctanh z)*(1-z)) (𝓝[≠] 1) (𝓝 2) := by
      have h : Tendsto (fun z : ℂ => 1+z) (𝓝[≠] 1) (𝓝 2) := by
        have : Tendsto (fun z:ℂ => 1+z) (𝓝 1) (𝓝 (1+1)) := tendsto_const_nhds.add tendsto_id
        norm_num at this
        exact this.mono_left nhdsWithin_le_nhds
      refine h.congr' ?_
      have hne : ∀ᶠ z in 𝓝[≠] (1:ℂ), z ≠ -1 := by
        apply eventually_nhdsWithin_of_eventually_nhds
        exact eventually_ne_nhds (by norm_num)
      filter_upwards [self_mem_nhdsWithin, hne] with z hz hz'
      exact (hypR4_arctanh_exp z hz hz').symm
    have := tendsto_nhds_unique hlim hlim2
    norm_num at this
  · intro ha
    have hcont : ContinuousAt (fun z => Complex.exp (-(2*arctanh z))*(1+z)) (-1) :=
      ((ha.continuousAt.const_mul 2).neg.cexp).mul (continuousAt_const.add continuousAt_id)
    have hlim : Tendsto (fun z => Complex.exp (-(2*arctanh z))*(1+z)) (𝓝[≠] (-1)) (𝓝 0) := by
      have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(-1:ℂ)}ᶜ))
      simpa using this
    have hlim2 : Tendsto (fun z => Complex.exp (-(2*arctanh z))*(1+z)) (𝓝[≠] (-1)) (𝓝 2) := by
      have h : Tendsto (fun z : ℂ => 1-z) (𝓝[≠] (-1)) (𝓝 2) := by
        have : Tendsto (fun z:ℂ => 1-z) (𝓝 (-1)) (𝓝 (1-(-1))) := tendsto_const_nhds.sub tendsto_id
        norm_num at this
        exact this.mono_left nhdsWithin_le_nhds
      refine h.congr' ?_
      have hne : ∀ᶠ z in 𝓝[≠] (-1:ℂ), z ≠ 1 := by
        apply eventually_nhdsWithin_of_eventually_nhds
        exact eventually_ne_nhds (by norm_num)
      filter_upwards [self_mem_nhdsWithin, hne] with z hz hz'
      have e := hypR4_arctanh_exp z hz' hz
      have hm : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz')
      rw [Complex.exp_neg]
      have hE : Complex.exp (2*arctanh z) ≠ 0 := Complex.exp_ne_zero _
      field_simp
      linear_combination e
    have := tendsto_nhds_unique hlim hlim2
    norm_num at this

/-- The two inverse branch points stated in the definition prose. -/
theorem arccsch_branch_points  : ¬AnalyticAt ℂ arccsch I ∧ ¬AnalyticAt ℂ arccsch (-I) := by
  have hrel : ∀ w : ℂ, arcsinh w = arccsch w⁻¹ := fun w => by simp [arccsch]
  have key : ∀ p : ℂ, p ≠ 0 → AnalyticAt ℂ arccsch p⁻¹ → AnalyticAt ℂ arcsinh p := by
    intro p hp ha
    have := ha.comp (analyticAt_id.inv hp)
    simpa [Function.comp_def, ← hrel] using this
  constructor
  · intro ha
    exact arcsinh_branch_points.2 (key (-I) (by simp) (by simpa using ha))
  · intro ha
    exact arcsinh_branch_points.1 (key I Complex.I_ne_zero (by simpa using ha))

/-- The two inverse branch points stated in the definition prose. -/
theorem arcsech_branch_points  : ¬AnalyticAt ℂ arcsech (1:ℂ) ∧ ¬AnalyticAt ℂ arcsech (-(1:ℂ)) := by
  have hrel : ∀ w : ℂ, arccosh w = arcsech w⁻¹ := fun w => by simp [arcsech]
  have key : ∀ p : ℂ, p ≠ 0 → AnalyticAt ℂ arcsech p⁻¹ → AnalyticAt ℂ arccosh p := by
    intro p hp ha
    have := ha.comp (analyticAt_id.inv hp)
    simpa [Function.comp_def, ← hrel] using this
  constructor
  · intro ha
    exact arccosh_branch_points.1 (key 1 one_ne_zero (by simpa using ha))
  · intro ha
    exact arccosh_branch_points.2 (key (-1) (by norm_num) (by simpa using ha))

/-- The two inverse branch points stated in the definition prose. -/
theorem arccoth_branch_points  : ¬AnalyticAt ℂ arccoth (1:ℂ) ∧ ¬AnalyticAt ℂ arccoth (-(1:ℂ)) := by
  have key : ∀ p : ℂ, p ≠ 0 → AnalyticAt ℂ arccoth p⁻¹ → AnalyticAt ℂ arctanh p := by
    intro p hp ha
    have h := ha.comp (analyticAt_id.inv hp)
    apply h.congr
    filter_upwards [eventually_ne_nhds hp] with w hw
    simp [arccoth_eq_inv (inv_ne_zero hw)]
  constructor
  · intro ha
    exact arctanh_branch_points.1 (key 1 one_ne_zero (by simpa using ha))
  · intro ha
    exact arctanh_branch_points.2 (key (-1) (by norm_num) (by simpa using ha))

/-- Reality and agreement with the existing real inverse on the uncut real interval. -/
theorem arcsinh_ofReal (x : ℝ)  : arcsinh x=(Real.arsinh x:ℂ) := by
  have hq:Complex.sqrt ((x:ℂ)^2+1)=(Real.sqrt (1+x^2):ℂ) := by
    rw [show (x:ℂ)^2+1=((1+x^2:ℝ):ℂ) by push_cast;ring]
    exact hyper_sqrt_ofReal _ (by positivity)
  have hp:0≤x+Real.sqrt (1+x^2) := by
    apply le_of_lt
    rw [← neg_lt_iff_pos_add']
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  rw [arcsinh,hq,Real.arsinh]
  rw [← Complex.ofReal_add,add_comm (Real.sqrt (1+x^2)) x,← Complex.ofReal_log hp]


/-- Reality and agreement with the existing real inverse on the uncut real interval. -/
theorem arccosh_ofReal (x : ℝ) (hx : 1≤x) : arccosh x=(Real.arcosh x:ℂ) := by
  have h1 : Complex.sqrt ((x:ℂ)-1) = (Real.sqrt (x-1):ℂ) := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring]; exact hyper_sqrt_ofReal _ (by linarith)
  have h2 : Complex.sqrt ((x:ℂ)+1) = (Real.sqrt (x+1):ℂ) := by
    rw [show (x:ℂ)+1 = ((x+1:ℝ):ℂ) by push_cast; ring]; exact hyper_sqrt_ofReal _ (by linarith)
  rw [arccosh, h1, h2, ← Complex.ofReal_mul, ← Real.sqrt_mul (by linarith),
    show (x-1)*(x+1) = x^2-1 by ring, ← Complex.ofReal_add,
    ← Complex.ofReal_log (by positivity), Real.arcosh]

/-- Reality and agreement with the existing real inverse on the uncut real interval. -/
theorem arctanh_ofReal (x : ℝ) (hx : |x|<1) : arctanh x=(Real.artanh x:ℂ) := by
  have hxp:0<1+x := by linarith [(abs_lt.mp hx).1]
  have hxm:0<1-x := by linarith [(abs_lt.mp hx).2]
  have hp:0≤(1+x)/(1-x) := (div_pos hxp hxm).le
  have harg:(1+(x:ℂ))/(1-(x:ℂ))=(((1+x)/(1-x):ℝ):ℂ) := by push_cast;rfl
  rw [arctanh,harg,← Complex.ofReal_log hp,Real.artanh_eq_half_log (mem_Icc_of_Ioo (abs_lt.mp hx))]
  push_cast
  ring


/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E10]
theorem arcsinh_neg (z : ℂ) : arcsinh (-z)= -arcsinh z := by
  have hn:Complex.sqrt ((-z)^2+1)+(-z)=(Complex.sqrt (z^2+1)+z)⁻¹ := by
    apply mul_left_cancel₀ (hyper_asinh_log_ne z)
    rw [mul_inv_cancel₀ (hyper_asinh_log_ne z)]
    convert hyper_asinh_product z using 1 <;> ring
  unfold arcsinh
  rw [hn,Complex.log_inv _ (Complex.mem_slitPlane_iff_arg.mp (hyper_asinh_log_slit z)).1]


/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E12]
theorem arctanh_neg {z : ℂ} (hz : z ∈ arctanhDomain) : arctanh (-z)= -arctanh z := by
  have hn:(1+(-z))/(1-(-z))=((1+z)/(1-z))⁻¹ := by
    simp only [sub_eq_add_neg,inv_div,neg_neg]
  unfold arctanh
  rw [hn,Complex.log_inv _ (Complex.mem_slitPlane_iff_arg.mp (hyper_atanh_slit hz)).1]
  ring


/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E13]
theorem arccsch_neg (z : ℂ) : arccsch (-z)= -arccsch z := by
  unfold arccsch
  rw [inv_neg,arcsinh_neg]


/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E15]
theorem arccoth_neg {z : ℂ} (hz : z ∈ arccothDomain) : arccoth (-z)= -arccoth z := by
  obtain ⟨hz0,hi⟩:=hyper_acoth_inv_mem hz
  rw [arccoth_eq_inv (neg_ne_zero.mpr hz0),arccoth_eq_inv hz0,inv_neg,arctanh_neg hi]


/-- Characterization of the principal square root by a root with positive real part. -/
private lemma hypR4_sqrt_eq_of_sq {a w : ℂ} (hw : w^2 = a) (hre : 0 < w.re) :
    Complex.sqrt a = w := by
  have h1 := trig_sqrt_sq a
  have h : (Complex.sqrt a - w)*(Complex.sqrt a + w) = 0 := by linear_combination h1 - hw
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hr : 0 ≤ (Complex.sqrt a).re := by
      rw [Complex.sqrt, Complex.cpow_inv_two_re]; positivity
    have : (Complex.sqrt a).re = -w.re := by
      have := congrArg Complex.re h; simp at this; linarith
    linarith

/-- The principal square root of `-w` for `w` in the upper half-plane. -/
private lemma hypR4_sqrt_neg_of_im_pos {w : ℂ} (h : 0 < w.im) :
    Complex.sqrt (-w) = -I*Complex.sqrt w := by
  apply hypR4_sqrt_eq_of_sq
  · rw [mul_pow, trig_sqrt_sq]; simp
  · have him : (Complex.sqrt w).im = Real.sqrt ((‖w‖ - w.re)/2) := by
      rw [Complex.sqrt]; exact Complex.cpow_inv_two_im_eq_sqrt h.le
    have hlt : w.re < ‖w‖ := lt_of_le_of_lt (le_abs_self _) (Complex.abs_re_lt_norm.mpr h.ne')
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub, neg_neg, him]
    exact Real.sqrt_pos.mpr (by linarith)

/-- The principal square root of `-w` for `w` in the lower half-plane. -/
private lemma hypR4_sqrt_neg_of_im_neg {w : ℂ} (h : w.im < 0) :
    Complex.sqrt (-w) = I*Complex.sqrt w := by
  apply hypR4_sqrt_eq_of_sq
  · rw [mul_pow, trig_sqrt_sq]; simp
  · have him : (Complex.sqrt w).im = -Real.sqrt ((‖w‖ - w.re)/2) := by
      rw [Complex.sqrt]; exact Complex.cpow_inv_two_im_eq_neg_sqrt h
    have hlt : w.re < ‖w‖ := lt_of_le_of_lt (le_abs_self _) (Complex.abs_re_lt_norm.mpr h.ne)
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, him, neg_neg]
    exact Real.sqrt_pos.mpr (by linarith)

/-- The principal logarithm of `-u` for `u` in the upper half-plane. -/
private lemma hypR4_log_neg_of_im_pos {u : ℂ} (h : 0 < u.im) :
    Complex.log (-u) = Complex.log u - π*I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]

/-- The principal logarithm of `-u` for `u` in the lower half-plane. -/
private lemma hypR4_log_neg_of_im_neg {u : ℂ} (h : u.im < 0) :
    Complex.log (-u) = Complex.log u + π*I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg h]

/-- Imaginary part of a principal square root has the sign of the imaginary part. -/
private lemma hypR4_sqrt_im_nonneg {w : ℂ} (h : 0 ≤ w.im) : 0 ≤ (Complex.sqrt w).im := by
  rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_sqrt h]; exact Real.sqrt_nonneg _

/-- Imaginary part of a principal square root in the lower half-plane. -/
private lemma hypR4_sqrt_im_nonpos {w : ℂ} (h : w.im < 0) : (Complex.sqrt w).im ≤ 0 := by
  rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_neg_sqrt h]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)

/-- Real part of a principal square root is nonnegative. -/
private lemma hypR4_sqrt_re_nonneg (w : ℂ) : 0 ≤ (Complex.sqrt w).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]; exact Real.sqrt_nonneg _

/-- Corrected principal-branch sign: E20 at z=±i contradicts the printed E11 sign pairing. -/
@[dlmf 4.37.E11]
theorem arccosh_neg {z : ℂ} (hz : z.im≠0) :
    arccosh (-z)=arccosh z-(if 0<z.im then 1 else -1)*π*I := by
  have hI : (I:ℂ)^2 = -1 := by simp
  have e1 : -z-1 = -(z+1) := by ring
  have e2 : -z+1 = -(z-1) := by ring
  unfold arccosh
  rw [e1, e2]
  rcases lt_or_gt_of_ne hz with hn | hp
  · have h1 : (z+1).im < 0 := by simpa using hn
    have h2 : (z-1).im < 0 := by simpa using hn
    rw [hypR4_sqrt_neg_of_im_neg h1, hypR4_sqrt_neg_of_im_neg h2]
    simp only [not_lt.mpr hn.le, ↓reduceIte]
    have hu : (z + Complex.sqrt (z-1)*Complex.sqrt (z+1)).im < 0 := by
      have a1 := hypR4_sqrt_re_nonneg (z-1)
      have a2 := hypR4_sqrt_re_nonneg (z+1)
      have b1 := hypR4_sqrt_im_nonpos h2
      have b2 := hypR4_sqrt_im_nonpos h1
      simp only [Complex.add_im, Complex.mul_im]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos a1 b2, mul_nonpos_of_nonneg_of_nonpos a2 b1]
    have hx : -z + I*Complex.sqrt (z+1)*(I*Complex.sqrt (z-1)) =
        -(z + Complex.sqrt (z-1)*Complex.sqrt (z+1)) := by
      linear_combination Complex.sqrt (z+1)*Complex.sqrt (z-1)*hI
    rw [hx, hypR4_log_neg_of_im_neg hu]
    ring
  · have h1 : 0 < (z+1).im := by simpa using hp
    have h2 : 0 < (z-1).im := by simpa using hp
    rw [hypR4_sqrt_neg_of_im_pos h1, hypR4_sqrt_neg_of_im_pos h2]
    simp only [hp, ↓reduceIte]
    have hu : 0 < (z + Complex.sqrt (z-1)*Complex.sqrt (z+1)).im := by
      have a1 := hypR4_sqrt_re_nonneg (z-1)
      have a2 := hypR4_sqrt_re_nonneg (z+1)
      have b1 := hypR4_sqrt_im_nonneg h2.le
      have b2 := hypR4_sqrt_im_nonneg h1.le
      simp only [Complex.add_im, Complex.mul_im]
      nlinarith [mul_nonneg a1 b2, mul_nonneg a2 b1]
    have hx : -z + -I*Complex.sqrt (z+1)*(-I*Complex.sqrt (z-1)) =
        -(z + Complex.sqrt (z-1)*Complex.sqrt (z+1)) := by
      linear_combination Complex.sqrt (z+1)*Complex.sqrt (z-1)*hI
    rw [hx, hypR4_log_neg_of_im_pos hu]
    ring

/-- The reciprocal version of the corrected principal arccosh sign relation. -/
@[dlmf 4.37.E14]
theorem arcsech_neg {z : ℂ} (hz : z.im≠0) :
    arcsech (-z)=arcsech z+(if 0<z.im then 1 else -1)*π*I := by
  have hz0 : z ≠ 0 := fun h => hz (by simp [h])
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  have him : (z⁻¹).im = -z.im / Complex.normSq z := by rw [Complex.inv_im]
  have hi : (z⁻¹).im ≠ 0 := by rw [him]; exact div_ne_zero (neg_ne_zero.mpr hz) hn.ne'
  rw [arcsech, arcsech, inv_neg, arccosh_neg hi]
  rcases lt_or_gt_of_ne hz with h | h
  · have : 0 < (z⁻¹).im := by rw [him]; exact div_pos (by linarith) hn
    simp only [this, not_lt.mpr h.le, ↓reduceIte]; ring
  · have : ¬ 0 < (z⁻¹).im := by rw [him]; exact not_lt.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hn.le)
    simp only [this, h, ↓reduceIte]; ring

/-- arcsinh log. -/
@[dlmf 4.37.E16]
theorem arcsinh_log {z : ℂ} (hz : z ∈ arcsinhDomain) : arcsinh z=Complex.log (Complex.sqrt (z^2+1)+z) := by
  rfl

/-- The principal square root is continuous off the open negative real axis. -/
private lemma hypR4_sqrt_continuousAt {w : ℂ} (h : 0 ≤ w.re ∨ w.im ≠ 0) :
    ContinuousAt Complex.sqrt w := by
  have := Complex.continuousAt_cpow_const_of_re_pos (w := (2⁻¹:ℂ)) h (by norm_num)
  exact this

/-- One-sided limit of the principal square root at the cut, from the upper half-plane. -/
private lemma hypR4_sqrt_tendsto_upper {f : ℝ → ℂ} {l : Filter ℝ} {w₀ : ℂ}
    (hf : Tendsto f l (𝓝 w₀)) (hre : w₀.re ≤ 0) (him : ∀ᶠ ε in l, 0 < (f ε).im) :
    Tendsto (fun ε => Complex.sqrt (f ε)) l (𝓝 (I*Complex.sqrt (-w₀))) := by
  have hc := ((hypR4_sqrt_continuousAt (w := -w₀) (Or.inl (by simp; linarith))).tendsto.comp
    hf.neg).const_mul I
  refine hc.congr' (him.mono fun ε hε => ?_)
  simp only [Function.comp_apply]
  rw [hypR4_sqrt_neg_of_im_pos hε]
  linear_combination (-(Complex.sqrt (f ε))) * (by simp : (I:ℂ)^2 = -1)

/-- One-sided limit of the principal square root at the cut, from the lower half-plane. -/
private lemma hypR4_sqrt_tendsto_lower {f : ℝ → ℂ} {l : Filter ℝ} {w₀ : ℂ}
    (hf : Tendsto f l (𝓝 w₀)) (hre : w₀.re ≤ 0) (him : ∀ᶠ ε in l, (f ε).im < 0) :
    Tendsto (fun ε => Complex.sqrt (f ε)) l (𝓝 (-I*Complex.sqrt (-w₀))) := by
  have hc := ((hypR4_sqrt_continuousAt (w := -w₀) (Or.inl (by simp; linarith))).tendsto.comp
    hf.neg).const_mul (-I)
  refine hc.congr' (him.mono fun ε hε => ?_)
  simp only [Function.comp_apply]
  rw [hypR4_sqrt_neg_of_im_neg hε]
  linear_combination (-(Complex.sqrt (f ε))) * (by simp : (I:ℂ)^2 = -1)

/-- Limits of the principal logarithm at a point `i t` of the positive imaginary axis. -/
private lemma hypR4_tendsto_log_I {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : 0 < t)
    (hg : Tendsto g l (𝓝 (I*t))) :
    Tendsto (fun ε => Complex.log (g ε)) l (𝓝 (Real.log t + π/2*I)) := by
  have hs : I*(t:ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simp [ht.ne']
  have h := (continuousAt_clog hs).tendsto.comp hg
  rw [Complex.log_mul_ofReal _ ht _ Complex.I_ne_zero, Complex.log_I] at h
  exact h

/-- Limits of the principal logarithm at a point `-i t` of the negative imaginary axis. -/
private lemma hypR4_tendsto_log_negI {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : 0 < t)
    (hg : Tendsto g l (𝓝 (-I*t))) :
    Tendsto (fun ε => Complex.log (g ε)) l (𝓝 (Real.log t - π/2*I)) := by
  have hs : -I*(t:ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simp [ht.ne']
  have h := (continuousAt_clog hs).tendsto.comp hg
  rw [Complex.log_mul_ofReal _ ht _ (neg_ne_zero.mpr Complex.I_ne_zero), Complex.log_neg_I] at h
  have e : (Real.log t:ℂ) - π/2*I = Real.log t + -(π/2)*I := by ring
  rw [e]; exact h

/-- The quantity `ε + i y` tends to `i y` along any filter tending to zero. -/
private lemma hypR4_tendsto_line {l : Filter ℝ} (hl : l ≤ 𝓝 0) (c : ℂ) :
    Tendsto (fun ε : ℝ => (ε:ℂ)+c) l (𝓝 c) := by
  have : Tendsto (fun ε : ℝ => (ε:ℂ)+c) (𝓝 0) (𝓝 (((0:ℝ):ℂ)+c)) :=
    ((Complex.continuous_ofReal.add continuous_const).tendsto 0)
  simpa using this.mono_left hl

/-- arcsinh upper cut. -/
@[dlmf 4.37.E17]
theorem arcsinh_upper_cut {y : ℝ} (hy : 1≤y) :
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[>] 0)
      (𝓝 (π*I/2+(Real.log (Real.sqrt (y^2-1)+y):ℂ))) ∧
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[<] 0)
      (𝓝 (π*I/2-(Real.log (Real.sqrt (y^2-1)+y):ℂ))) := by
  set r := Real.sqrt (y^2-1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = y^2-1 := Real.sq_sqrt (by nlinarith)
  have hry : r < y := by nlinarith
  have hw : -((I*(y:ℂ))^2+1) = ((y^2-1:ℝ):ℂ) := by
    push_cast; linear_combination -(y:ℂ)^2*(by simp : (I:ℂ)^2 = -1)
  have hsq : Complex.sqrt (-((I*(y:ℂ))^2+1)) = r := by rw [hw, hyper_sqrt_ofReal _ (by nlinarith)]
  have hinv : y - r = (r+y)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -hr2)
  have hz : ∀ {l : Filter ℝ}, l ≤ 𝓝 0 →
      Tendsto (fun ε : ℝ => ((ε:ℂ)+I*y)^2+1) l (𝓝 ((I*(y:ℂ))^2+1)) := fun hl =>
    ((hypR4_tendsto_line hl (I*y)).pow 2).add_const 1
  have hw0 : ((I*(y:ℂ))^2+1).re ≤ 0 := by simp [pow_two]; nlinarith
  constructor
  · have him : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < (((ε:ℂ)+I*y)^2+1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by
        simp [pow_two]; nlinarith
    have hs := hypR4_sqrt_tendsto_upper (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (hypR4_tendsto_line nhdsWithin_le_nhds (I*y))
    have := hypR4_tendsto_log_I (t := r+y) (by linarith) (by convert hg using 2; push_cast; ring)
    have e : (π*I/2+((Real.log (Real.sqrt (y^2-1)+y)):ℂ)) = (Real.log (r+y) + π/2*I) := by
      rw [← hr]; ring
    rw [e]; exact this
  · have him : ∀ᶠ ε in 𝓝[<] (0:ℝ), (((ε:ℂ)+I*y)^2+1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by
        simp [pow_two]; nlinarith
    have hs := hypR4_sqrt_tendsto_lower (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (hypR4_tendsto_line nhdsWithin_le_nhds (I*y))
    have := hypR4_tendsto_log_I (t := y-r) (by linarith) (by convert hg using 2; push_cast; ring)
    have e : (π*I/2-((Real.log (Real.sqrt (y^2-1)+y)):ℂ)) = (Real.log (y-r) + π/2*I) := by
      rw [← hr, hinv, Real.log_inv]; push_cast; ring
    rw [e]; exact this

/-- arcsinh lower cut. -/
@[dlmf 4.37.E18]
theorem arcsinh_lower_cut {y : ℝ} (hy : y≤ -1) :
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[>] 0)
      (𝓝 (-π*I/2+(Real.log (Real.sqrt (y^2-1)-y):ℂ))) ∧
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[<] 0)
      (𝓝 (-π*I/2-(Real.log (Real.sqrt (y^2-1)-y):ℂ))) := by
  set r := Real.sqrt (y^2-1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = y^2-1 := Real.sq_sqrt (by nlinarith)
  have hry : r < -y := by nlinarith
  have hw : -((I*(y:ℂ))^2+1) = ((y^2-1:ℝ):ℂ) := by
    push_cast; linear_combination -(y:ℂ)^2*(by simp : (I:ℂ)^2 = -1)
  have hsq : Complex.sqrt (-((I*(y:ℂ))^2+1)) = r := by rw [hw, hyper_sqrt_ofReal _ (by nlinarith)]
  have hinv : -y - r = (r-y)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -hr2)
  have hz : ∀ {l : Filter ℝ}, l ≤ 𝓝 0 →
      Tendsto (fun ε : ℝ => ((ε:ℂ)+I*y)^2+1) l (𝓝 ((I*(y:ℂ))^2+1)) := fun hl =>
    ((hypR4_tendsto_line hl (I*y)).pow 2).add_const 1
  have hw0 : ((I*(y:ℂ))^2+1).re ≤ 0 := by simp [pow_two]; nlinarith
  constructor
  · have him : ∀ᶠ ε in 𝓝[>] (0:ℝ), (((ε:ℂ)+I*y)^2+1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by
        simp [pow_two]; nlinarith
    have hs := hypR4_sqrt_tendsto_lower (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (hypR4_tendsto_line nhdsWithin_le_nhds (I*y))
    have := hypR4_tendsto_log_negI (t := r-y) (by linarith) (by convert hg using 2; push_cast; ring)
    have e : (-π*I/2+((Real.log (Real.sqrt (y^2-1)-y)):ℂ)) = (Real.log (r-y) - π/2*I) := by
      rw [← hr]; ring
    rw [e]; exact this
  · have him : ∀ᶠ ε in 𝓝[<] (0:ℝ), 0 < (((ε:ℂ)+I*y)^2+1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by
        simp [pow_two]; nlinarith
    have hs := hypR4_sqrt_tendsto_upper (hz nhdsWithin_le_nhds) hw0 him
    rw [hsq] at hs
    have hg := hs.add (hypR4_tendsto_line nhdsWithin_le_nhds (I*y))
    have := hypR4_tendsto_log_negI (t := -y-r) (by linarith) (by convert hg using 2; push_cast; ring)
    have e : (-π*I/2-((Real.log (Real.sqrt (y^2-1)-y)):ℂ)) = (Real.log (-y-r) - π/2*I) := by
      rw [← hr, hinv, Real.log_inv]; push_cast; ring
    rw [e]; exact this

/-- The right half of the inverse-cosh domain is star-convex about `2`. -/
private lemma hypR4_acosh_right_starConvex :
    StarConvex ℝ (2:ℂ) {z : ℂ | z ∈ arccoshDomain ∧ 0 < z.re} := by
  intro y hy a b ha hb hab
  obtain ⟨hyd, hyr⟩ := hy
  have hre : (a • (2:ℂ) + b • y).re = 2*a + b*y.re := by simp; ring
  have him : (a • (2:ℂ) + b • y).im = b*y.im := by simp
  have hpos : 0 < 2*a + b*y.re := by
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · rw [← hb0]; linarith
    · nlinarith
  refine ⟨?_, by rw [hre]; exact hpos⟩
  rcases hyd with hi | hr
  · rcases eq_or_lt_of_le hb with hb0 | hb0
    · right; rw [hre, ← hb0]; linarith
    · left; rw [him]; exact mul_ne_zero hb0.ne' hi
  · right; rw [hre]
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · rw [← hb0]; linarith
    · nlinarith [mul_pos hb0 (sub_pos.mpr hr)]

/-- On the right half of its domain the factored inverse-cosh root is the principal `√(z²-1)`. -/
private lemma hypR4_acosh_root_pos {z : ℂ} (hz : z ∈ arccoshDomain) (hre : 0 < z.re) :
    Complex.sqrt (z-1)*Complex.sqrt (z+1) = Complex.sqrt (z^2-1) := by
  set V := {z : ℂ | z ∈ arccoshDomain ∧ 0 < z.re}
  have hVo : IsOpen V := by
    have : IsOpen arccoshDomain := by
      change IsOpen ({z:ℂ | z.im≠0}∪{z:ℂ | 1<z.re})
      exact (isOpen_ne.preimage Complex.continuous_im).union
        (isOpen_lt continuous_const Complex.continuous_re)
    exact this.inter (isOpen_lt continuous_const Complex.continuous_re)
  have h2V : (2:ℂ) ∈ V := ⟨Or.inr (by norm_num), by norm_num⟩
  have hVc : IsPreconnected V :=
    (hypR4_acosh_right_starConvex.isPathConnected h2V).isConnected.isPreconnected
  have hslit : ∀ w ∈ V, w^2-1 ∈ Complex.slitPlane := by
    rintro w ⟨hw, hwr⟩
    rw [Complex.mem_slitPlane_iff]
    by_cases hy : w.im = 0
    · left
      have : 1 < w.re := hw.resolve_left (not_not.mpr hy)
      simp [pow_two, Complex.mul_re, hy]; nlinarith
    · right; simp [pow_two, Complex.mul_im]
      intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hwr.ne') hy; linear_combination h
  have hr : AnalyticOnNhd ℂ (fun w => Complex.sqrt (w-1)*Complex.sqrt (w+1)) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    obtain ⟨h1, h2⟩ := hypR4_acosh_slit hw.1
    exact (((Complex.differentiableAt_sqrt h1).comp w (differentiableAt_id.sub_const 1)).mul
      ((Complex.differentiableAt_sqrt h2).comp w (differentiableAt_id.add_const 1))).differentiableWithinAt
  have hs : AnalyticOnNhd ℂ (fun w => Complex.sqrt (w^2-1)) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    exact ((Complex.differentiableAt_sqrt (hslit w hw)).comp w
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w^2-1) w)).differentiableWithinAt
  have h1 : Complex.sqrt 1 = 1 := by simp [Complex.sqrt]
  refine hypR4_sq_eq_continuation hVo hVc hr hs ?_ h2V ?_ ?_ z ⟨hz, hre⟩
  · intro w _; rw [mul_pow, trig_sqrt_sq, trig_sqrt_sq, trig_sqrt_sq]; ring
  · norm_num [h1]
  · intro h
    have := trig_sqrt_sq ((2:ℂ)^2-1)
    rw [h] at this; norm_num at this

/-- The factored inverse-cosh root is `±√(z²-1)` according to the sign of `Re z`. -/
private lemma hypR4_acosh_root_signed {z : ℂ} (hz : z ∈ arccoshDomain) (hre : z.re ≠ 0) :
    Complex.sqrt (z-1)*Complex.sqrt (z+1) = (if 0<z.re then 1 else -1)*Complex.sqrt (z^2-1) := by
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · simp only [show ¬ (0 < z.re) from not_lt.mpr hneg.le, ↓reduceIte]
    have him : z.im ≠ 0 := by
      rcases hz with h | h
      · exact h
      · linarith
    have hz' : -z ∈ arccoshDomain := Or.inl (by simpa using him)
    have h := hypR4_acosh_root_pos hz' (by simpa using hneg)
    rw [show (-z)^2-1 = z^2-1 by ring, show -z-1 = -(z+1) by ring,
      show -z+1 = -(z-1) by ring] at h
    rcases lt_or_gt_of_ne him with hi | hi
    · rw [hypR4_sqrt_neg_of_im_neg (by simpa using hi), hypR4_sqrt_neg_of_im_neg (by simpa using hi)] at h
      rw [← h]; linear_combination (Complex.sqrt (z-1)*Complex.sqrt (z+1))*Complex.I_sq
    · rw [hypR4_sqrt_neg_of_im_pos (by simpa using hi), hypR4_sqrt_neg_of_im_pos (by simpa using hi)] at h
      rw [← h]; linear_combination (Complex.sqrt (z-1)*Complex.sqrt (z+1))*Complex.I_sq
  · simp only [hpos, ↓reduceIte, one_mul]; exact hypR4_acosh_root_pos hz hpos

/-- arccosh log. -/
@[dlmf 4.37.E19]
theorem arccosh_log {z : ℂ} (hz : z ∈ arccoshDomain) (hre : z.re≠0) :
    arccosh z=Complex.log ((if 0<z.re then 1 else -1)*Complex.sqrt (z^2-1)+z) := by
  rw [arccosh, hypR4_acosh_root_signed hz hre, add_comm]

/-- arccosh imaginary. -/
@[dlmf 4.37.E20]
theorem arccosh_imaginary {y : ℝ} (hy : y≠0) :
    arccosh (I*y)=(if 0<y then 1 else -1)*π*I/2+
      (Real.log (Real.sqrt (y^2+1)+(if 0<y then y else -y)):ℂ) := by
  have hI : (I:ℂ)^2 = -1 := by simp
  set r := Real.sqrt (y^2+1) with hr
  have hr2 : r^2 = y^2+1 := Real.sq_sqrt (by positivity)
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hry : |y| < r := by
    rw [hr, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  set S := Complex.sqrt (I*y-1)*Complex.sqrt (I*y+1) with hSdef
  have hS2 : S^2 = -((r:ℂ)^2) := by
    rw [hSdef, mul_pow, trig_sqrt_sq, trig_sqrt_sq]
    have : ((r:ℂ))^2 = ((y^2+1:ℝ):ℂ) := by rw [← Complex.ofReal_pow, hr2]
    rw [this]; push_cast; linear_combination (y:ℂ)^2*hI
  have hfac : (S - I*r)*(S + I*r) = 0 := by linear_combination hS2 - (r:ℂ)^2*hI
  unfold arccosh
  rw [← hSdef]
  have a1 := hypR4_sqrt_re_nonneg (I*y-1)
  have a2 := hypR4_sqrt_re_nonneg (I*y+1)
  rcases lt_or_gt_of_ne hy with hn | hp
  · have h1 : (I*y+1).im < 0 := by simpa using hn
    have h2 : (I*y-1).im < 0 := by simpa using hn
    have b1 := hypR4_sqrt_im_nonpos h2
    have b2 := hypR4_sqrt_im_nonpos h1
    have hSim : S.im ≤ 0 := by
      rw [hSdef, Complex.mul_im]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos a1 b2, mul_nonpos_of_nonneg_of_nonpos a2 b1]
    have hS : S = -(I*r) := by
      rcases mul_eq_zero.mp hfac with h | h
      · have : S = I*r := by linear_combination h
        rw [this] at hSim; simp at hSim; linarith
      · linear_combination h
    simp only [not_lt.mpr hn.le, ↓reduceIte]
    rw [hS, show I*(y:ℂ) + -(I*r) = -I*((r-y:ℝ):ℂ) by push_cast; ring,
      Complex.log_mul_ofReal _ (by linarith [neg_abs_le y, le_abs_self y]) _ (by simp)]
    rw [Complex.log_neg_I]; ring
  · have h1 : 0 < (I*y+1).im := by simpa using hp
    have h2 : 0 < (I*y-1).im := by simpa using hp
    have b1 := hypR4_sqrt_im_nonneg h2.le
    have b2 := hypR4_sqrt_im_nonneg h1.le
    have hSim : 0 ≤ S.im := by
      rw [hSdef, Complex.mul_im]
      nlinarith [mul_nonneg a1 b2, mul_nonneg a2 b1]
    have hS : S = I*r := by
      rcases mul_eq_zero.mp hfac with h | h
      · linear_combination h
      · have : S = -(I*r) := by linear_combination h
        rw [this] at hSim; simp at hSim; linarith
    simp only [hp, ↓reduceIte]
    rw [hS, show I*(y:ℂ) + I*r = I*((r+y:ℝ):ℂ) by push_cast; ring,
      Complex.log_mul_ofReal _ (by linarith [neg_abs_le y]) _ (by simp)]
    rw [Complex.log_I]; ring

/-- The principal square root has positive real part off the closed negative real axis. -/
private lemma hypR4_sqrt_re_pos {w : ℂ} (h : w.im ≠ 0 ∨ 0 < w.re) : 0 < (Complex.sqrt w).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  rcases h with h | h
  · have := Complex.abs_re_lt_norm.mpr h
    linarith [neg_abs_le w.re]
  · linarith [Complex.re_le_norm w]

/-- Halving under the principal square root. -/
private lemma hypR4_sqrt_half {w : ℂ} (h : w.im ≠ 0 ∨ 0 < w.re) :
    Complex.sqrt (w/2) = Complex.sqrt w*((Real.sqrt 2)⁻¹:ℝ) := by
  apply hypR4_sqrt_eq_of_sq
  · rw [mul_pow, trig_sqrt_sq, ← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num)]
    push_cast; ring
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos (hypR4_sqrt_re_pos h) (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num)))

/-- `log (u²) = 2 log u` in the open right half-plane. -/
private lemma hypR4_log_sq_of_re_pos {u : ℂ} (h : 0 < u.re) :
    Complex.log (u^2) = 2*Complex.log u := by
  have hu0 : u ≠ 0 := fun e => by rw [e] at h; simp at h
  have harg : |Complex.arg u| < π/2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h)
  rw [show u^2 = Complex.exp (2*Complex.log u) by
    rw [two_mul, Complex.exp_add, Complex.exp_log hu0]; ring, Complex.log_exp]
  · rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.im_ofReal_mul, Complex.log_im]
    linarith [(abs_lt.mp harg).1]
  · rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.im_ofReal_mul, Complex.log_im]
    linarith [(abs_lt.mp harg).2]

/-- arccosh log half. -/
@[dlmf 4.37.E21]
theorem arccosh_log_half {z : ℂ} (hz : z ∈ arccoshDomain) :
    arccosh z=2*Complex.log (Complex.sqrt ((z+1)/2)+Complex.sqrt ((z-1)/2)) := by
  have hp : (z+1).im ≠ 0 ∨ 0 < (z+1).re := by
    rcases hz with h | h
    · left; simpa using h
    · right; simp; linarith
  have hm : (z-1).im ≠ 0 ∨ 0 < (z-1).re := by
    rcases hz with h | h
    · left; simpa using h
    · right; simp; linarith
  have h2 : ((Real.sqrt 2)⁻¹:ℝ)^2 = (1/2:ℂ) := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  have hsum : Complex.sqrt ((z+1)/2)+Complex.sqrt ((z-1)/2) =
      (Complex.sqrt (z+1)+Complex.sqrt (z-1))*((Real.sqrt 2)⁻¹:ℝ) := by
    rw [hypR4_sqrt_half hp, hypR4_sqrt_half hm]; ring
  have hre : 0 < (Complex.sqrt ((z+1)/2)+Complex.sqrt ((z-1)/2)).re := by
    rw [Complex.add_re]
    have := hypR4_sqrt_re_pos (show ((z+1)/2).im ≠ 0 ∨ 0 < ((z+1)/2).re by
      rcases hp with h | h
      · left; simpa using h
      · right; simp; linarith [show 0 < (z+1).re from h, show (z+1).re = z.re+1 by simp])
    linarith [hypR4_sqrt_re_nonneg ((z-1)/2)]
  rw [← hypR4_log_sq_of_re_pos hre, hsum, mul_pow, h2, add_sq, trig_sqrt_sq, trig_sqrt_sq]
  unfold arccosh
  congr 1
  ring

/-- arccosh inner cut. -/
@[dlmf 4.37.E22]
theorem arccosh_inner_cut {x : ℝ} (hx : -1<x ∧ x≤1) :
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[>] 0)
      (𝓝 (Complex.log (I*Real.sqrt (1-x^2)+x))) ∧
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[<] 0)
      (𝓝 (-Complex.log (I*Real.sqrt (1-x^2)+x))) := by
  obtain ⟨hx1, hx2⟩ := hx
  set s := Real.sqrt (1-x^2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = 1-x^2 := Real.sq_sqrt (by nlinarith)
  have hprod : Real.sqrt (1-x)*Real.sqrt (x+1) = s := by
    rw [← Real.sqrt_mul (by linarith), hs]; congr 1; ring
  have hp : Tendsto (fun ε : ℝ => Complex.sqrt ((x:ℂ)+I*ε+1)) (𝓝 0) (𝓝 (Real.sqrt (x+1):ℂ)) := by
    have hc : Tendsto (fun ε : ℝ => (x:ℂ)+I*ε+1) (𝓝 0) (𝓝 ((x+1:ℝ):ℂ)) := by
      have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε+1) := by fun_prop
      simpa using this.tendsto 0
    have := (hypR4_sqrt_continuousAt (w := ((x+1:ℝ):ℂ)) (Or.inl (by simp; linarith))).tendsto.comp hc
    rwa [hyper_sqrt_ofReal _ (by linarith)] at this
  have hm : Tendsto (fun ε : ℝ => (x:ℂ)+I*ε-1) (𝓝 0) (𝓝 ((x:ℂ)-1)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε-1) := by fun_prop
    simpa using this.tendsto 0
  have hlin : Tendsto (fun ε : ℝ => (x:ℂ)+I*ε) (𝓝 0) (𝓝 (x:ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε) := by fun_prop
    simpa using this.tendsto 0
  have hmre : ((x:ℂ)-1).re ≤ 0 := by simp; linarith
  have hneg : Complex.sqrt (-((x:ℂ)-1)) = (Real.sqrt (1-x):ℂ) := by
    rw [show -((x:ℂ)-1) = ((1-x:ℝ):ℂ) by push_cast; ring, hyper_sqrt_ofReal _ (by linarith)]
  have hslit : I*(s:ℂ)+x ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases h0 : s = 0
    · left
      have : x^2 = 1 := by nlinarith
      have : x = 1 := by nlinarith
      simp [h0, this]
    · right; simp; exact h0
  constructor
  · have him : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ((x:ℂ)+I*(ε:ℂ)-1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by simpa using hε
    have h1 := hypR4_sqrt_tendsto_upper (hm.mono_left nhdsWithin_le_nhds) hmre him
    rw [hneg] at h1
    have hg := (hlin.mono_left nhdsWithin_le_nhds).add (h1.mul (hp.mono_left nhdsWithin_le_nhds))
    have := (continuousAt_clog hslit).tendsto.comp
      (show Tendsto _ _ (𝓝 (I*(s:ℂ)+x)) by
        convert hg using 2; rw [← hprod]; push_cast; ring)
    exact this
  · have him : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ)-1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by simpa using hε
    have h1 := hypR4_sqrt_tendsto_lower (hm.mono_left nhdsWithin_le_nhds) hmre him
    rw [hneg] at h1
    have hg := (hlin.mono_left nhdsWithin_le_nhds).add (h1.mul (hp.mono_left nhdsWithin_le_nhds))
    have hconj : -I*(s:ℂ)+x = (I*(s:ℂ)+x)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      have : ((s:ℂ))^2 = 1-(x:ℂ)^2 := by rw [← Complex.ofReal_pow, hs2]; push_cast; ring
      linear_combination this - (s:ℂ)^2*(by simp : (I:ℂ)^2 = -1)
    have harg : Complex.arg (I*(s:ℂ)+x) ≠ π := by
      intro h
      rw [Complex.arg_eq_pi_iff] at h
      simp at h
      obtain ⟨h1, h2⟩ := h
      rw [h2] at hs2; nlinarith
    have hslit' : -I*(s:ℂ)+x ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_cases h0 : s = 0
      · left
        have : x^2 = 1 := by nlinarith
        have : x = 1 := by nlinarith
        simp [h0, this]
      · right; simp; exact h0
    have := (continuousAt_clog hslit').tendsto.comp
      (show Tendsto _ _ (𝓝 (-I*(s:ℂ)+x)) by
        convert hg using 2; rw [← hprod]; push_cast; ring)
    rw [hconj, Complex.log_inv _ harg] at this
    exact this

/-- One-sided limit of the principal logarithm at the negative real axis, from above. -/
private lemma hypR4_tendsto_log_cut_upper {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : t < 0)
    (hg : Tendsto g l (𝓝 (t:ℂ))) (him : ∀ᶠ ε in l, 0 ≤ (g ε).im) :
    Tendsto (fun ε => Complex.log (g ε)) l (𝓝 (Real.log (-t) + π*I)) := by
  have h := (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := (t:ℂ)) (by simpa using ht) (by simp)).comp (tendsto_nhdsWithin_iff.mpr ⟨hg, him⟩)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht] at h
  exact h

/-- One-sided limit of the principal logarithm at the negative real axis, from below. -/
private lemma hypR4_tendsto_log_cut_lower {g : ℝ → ℂ} {l : Filter ℝ} {t : ℝ} (ht : t < 0)
    (hg : Tendsto g l (𝓝 (t:ℂ))) (him : ∀ᶠ ε in l, (g ε).im < 0) :
    Tendsto (fun ε => Complex.log (g ε)) l (𝓝 (Real.log (-t) - π*I)) := by
  have h := (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (z := (t:ℂ)) (by simpa using ht) (by simp)).comp (tendsto_nhdsWithin_iff.mpr ⟨hg, him⟩)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht] at h
  exact h

/-- arccosh outer cut. -/
@[dlmf 4.37.E23]
theorem arccosh_outer_cut {x : ℝ} (hx : x≤ -1) :
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[>] 0)
      (𝓝 (π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ))) ∧
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[<] 0)
      (𝓝 (-π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ))) := by
  set r := Real.sqrt (x^2-1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have hprod : Real.sqrt (1-x)*Real.sqrt (-1-x) = r := by
    rw [← Real.sqrt_mul (by linarith), hr]; congr 1; ring
  have hcont : ∀ c : ℂ, Tendsto (fun ε : ℝ => (x:ℂ)+I*ε+c) (𝓝 0) (𝓝 ((x:ℂ)+c)) := fun c => by
    have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε+c) := by fun_prop
    simpa using this.tendsto 0
  have hm := hcont (-1)
  have hp := hcont 1
  simp only [← sub_eq_add_neg] at hm
  have hlin : Tendsto (fun ε : ℝ => (x:ℂ)+I*ε) (𝓝 0) (𝓝 (x:ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ)+I*ε) := by fun_prop
    simpa using this.tendsto 0
  have hmre : ((x:ℂ)-1).re ≤ 0 := by simp; linarith
  have hpre : ((x:ℂ)+1).re ≤ 0 := by simp; linarith
  have hneg1 : Complex.sqrt (-((x:ℂ)-1)) = (Real.sqrt (1-x):ℂ) := by
    rw [show -((x:ℂ)-1) = ((1-x:ℝ):ℂ) by push_cast; ring, hyper_sqrt_ofReal _ (by linarith)]
  have hneg2 : Complex.sqrt (-((x:ℂ)+1)) = (Real.sqrt (-1-x):ℂ) := by
    rw [show -((x:ℂ)+1) = ((-1-x:ℝ):ℂ) by push_cast; ring, hyper_sqrt_ofReal _ (by linarith)]
  have hxr : x - r < 0 := by linarith
  have hI : (I:ℂ)^2 = -1 := by simp
  constructor
  · have him1 : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ((x:ℂ)+I*(ε:ℂ)-1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by simpa using hε
    have him2 : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ((x:ℂ)+I*(ε:ℂ)+1).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by simpa using hε
    have h1 := hypR4_sqrt_tendsto_upper (hm.mono_left nhdsWithin_le_nhds) hmre him1
    have h2 := hypR4_sqrt_tendsto_upper (hp.mono_left nhdsWithin_le_nhds) hpre him2
    rw [hneg1] at h1; rw [hneg2] at h2
    have hg := (hlin.mono_left nhdsWithin_le_nhds).add (h1.mul h2)
    have hgim : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 ≤ ((x:ℂ)+I*(ε:ℂ) +
        Complex.sqrt ((x:ℂ)+I*(ε:ℂ)-1)*Complex.sqrt ((x:ℂ)+I*(ε:ℂ)+1)).im :=
      (him1.and him2).mono fun ε ⟨e1, e2⟩ => by
        have a1 := hypR4_sqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)-1)
        have a2 := hypR4_sqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)+1)
        have b1 := hypR4_sqrt_im_nonneg e1.le
        have b2 := hypR4_sqrt_im_nonneg e2.le
        have hε : 0 < ε := by
          simpa using e1
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
        nlinarith [mul_nonneg a1 b2, mul_nonneg a2 b1]
    have hg' : Tendsto (fun ε : ℝ => (x:ℂ)+I*(ε:ℂ) +
        Complex.sqrt ((x:ℂ)+I*(ε:ℂ)-1)*Complex.sqrt ((x:ℂ)+I*(ε:ℂ)+1)) (𝓝[>] (0:ℝ))
        (𝓝 ((x-r:ℝ):ℂ)) := by
      convert hg using 2
      rw [← hprod]; push_cast
      linear_combination (-(Real.sqrt (1-x):ℂ)*(Real.sqrt (-1-x):ℂ))*hI
    have := hypR4_tendsto_log_cut_upper hxr hg' hgim
    have e : (π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ)) = Real.log (-(x-r)) + π*I := by
      rw [← hr]; ring_nf
    rw [e]; exact this
  · have him1 : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ)-1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by simpa using hε
    have him2 : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ)+1).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by simpa using hε
    have h1 := hypR4_sqrt_tendsto_lower (hm.mono_left nhdsWithin_le_nhds) hmre him1
    have h2 := hypR4_sqrt_tendsto_lower (hp.mono_left nhdsWithin_le_nhds) hpre him2
    rw [hneg1] at h1; rw [hneg2] at h2
    have hg := (hlin.mono_left nhdsWithin_le_nhds).add (h1.mul h2)
    have hgim : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((x:ℂ)+I*(ε:ℂ) +
        Complex.sqrt ((x:ℂ)+I*(ε:ℂ)-1)*Complex.sqrt ((x:ℂ)+I*(ε:ℂ)+1)).im < 0 :=
      (him1.and him2).mono fun ε ⟨e1, e2⟩ => by
        have a1 := hypR4_sqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)-1)
        have a2 := hypR4_sqrt_re_nonneg ((x:ℂ)+I*(ε:ℂ)+1)
        have b1 := hypR4_sqrt_im_nonpos e1
        have b2 := hypR4_sqrt_im_nonpos e2
        have hε : ε < 0 := by
          simpa using e1
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos a1 b2, mul_nonpos_of_nonneg_of_nonpos a2 b1]
    have hg' : Tendsto (fun ε : ℝ => (x:ℂ)+I*(ε:ℂ) +
        Complex.sqrt ((x:ℂ)+I*(ε:ℂ)-1)*Complex.sqrt ((x:ℂ)+I*(ε:ℂ)+1)) (𝓝[<] (0:ℝ))
        (𝓝 ((x-r:ℝ):ℂ)) := by
      convert hg using 2
      rw [← hprod]; push_cast
      linear_combination (-(Real.sqrt (1-x):ℂ)*(Real.sqrt (-1-x):ℂ))*hI
    have := hypR4_tendsto_log_cut_lower hxr hg' hgim
    have e : (-π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ)) = Real.log (-(x-r)) - π*I := by
      rw [← hr]; ring_nf
    rw [e]; exact this

/-- arctanh log. -/
@[dlmf 4.37.E24]
theorem arctanh_log {z : ℂ} (hz : z ∈ arctanhDomain) : arctanh z=Complex.log ((1+z)/(1-z))/2 := by
  rfl

/-- arctanh cut. -/
@[dlmf 4.37.E25]
theorem arctanh_cut {x : ℝ} (hx : 1< |x|) :
    Tendsto (fun ε : ℝ => arctanh ((x:ℂ)+I*ε)) (𝓝[>] 0)
      (𝓝 (π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2)) ∧
    Tendsto (fun ε : ℝ => arctanh ((x:ℂ)+I*ε)) (𝓝[<] 0)
      (𝓝 (-π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2)) := by
  have hx1 : 1-x ≠ 0 := by
    intro h; have : x = 1 := by linarith
    rw [this] at hx; norm_num at hx
  have hx2 : x+1 ≠ 0 := by
    intro h; have : x = -1 := by linarith
    rw [this] at hx; norm_num at hx
  have ht : (1+x)/(1-x) < 0 := by
    rcases lt_abs.mp hx with h | h
    · exact div_neg_of_pos_of_neg (by linarith) (by linarith)
    · exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hcont : Tendsto (fun ε : ℝ => (1+((x:ℂ)+I*ε))/(1-((x:ℂ)+I*ε))) (𝓝 0)
      (𝓝 (((1+x)/(1-x):ℝ):ℂ)) := by
    have hn : Tendsto (fun ε : ℝ => 1+((x:ℂ)+I*ε)) (𝓝 0) (𝓝 (1+(x:ℂ))) := by
      have : Continuous (fun ε : ℝ => 1+((x:ℂ)+I*ε)) := by fun_prop
      simpa using this.tendsto 0
    have hd : Tendsto (fun ε : ℝ => 1-((x:ℂ)+I*ε)) (𝓝 0) (𝓝 (1-(x:ℂ))) := by
      have : Continuous (fun ε : ℝ => 1-((x:ℂ)+I*ε)) := by fun_prop
      simpa using this.tendsto 0
    have := hn.div hd (by exact_mod_cast hx1)
    rw [show (((1+x)/(1-x):ℝ):ℂ) = (1+(x:ℂ))/(1-(x:ℂ)) by push_cast; ring]
    exact this
  have him : ∀ ε : ℝ, ((1+((x:ℂ)+I*ε))/(1-((x:ℂ)+I*ε))).im =
      2*ε/Complex.normSq (1-((x:ℂ)+I*ε)) := by
    intro ε
    rw [Complex.div_im]
    simp only [Complex.add_im, Complex.sub_im, Complex.add_re, Complex.sub_re, Complex.mul_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im]
    ring
  have hnsq : ∀ ε : ℝ, 0 < Complex.normSq (1-((x:ℂ)+I*ε)) := fun ε =>
    Complex.normSq_pos.mpr fun h => hx1 (by
      have := congrArg Complex.re h; simpa using this)
  have e : Real.log (-((1+x)/(1-x))) = Real.log ((x+1)/(x-1)) := by
    have hx1' : x-1 ≠ 0 := fun h => hx1 (by linarith)
    congr 1; rw [← neg_div, div_eq_div_iff hx1 hx1']; ring
  constructor
  · have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 ≤ ((1+((x:ℂ)+I*ε))/(1-((x:ℂ)+I*ε))).im :=
      eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => by
        rw [him]; exact (div_pos (by linarith) (hnsq ε)).le
    have h := hypR4_tendsto_log_cut_upper ht (hcont.mono_left nhdsWithin_le_nhds) hev
    have := h.div_const 2
    rw [e] at this
    have e2 : (π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2) = ((Real.log ((x+1)/(x-1)):ℂ) + π*I)/2 := by
      ring
    rw [e2]; exact this
  · have hev : ∀ᶠ ε : ℝ in 𝓝[<] (0:ℝ), ((1+((x:ℂ)+I*ε))/(1-((x:ℂ)+I*ε))).im < 0 :=
      eventually_mem_nhdsWithin.mono fun ε (hε : ε < 0) => by
        rw [him]; exact div_neg_of_neg_of_pos (by linarith) (hnsq ε)
    have h := hypR4_tendsto_log_cut_lower ht (hcont.mono_left nhdsWithin_le_nhds) hev
    have := h.div_const 2
    rw [e] at this
    have e2 : (-π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2) = ((Real.log ((x+1)/(x-1)):ℂ) - π*I)/2 := by
      ring
    rw [e2]; exact this

/-- sinh inverse family. -/
@[dlmf 4.37.E26, dlmf 4.37.E29]
theorem sinh_inverse_family (z w : ℂ) :
    Complex.sinh w=z ↔ ∃ k : ℤ, w=(-1:ℂ)^k*arcsinh z+(k:ℂ)*π*I := by
  simpa only [hyper_sinh_arcsinh] using hyper_sinh_fiber_forms (arcsinh z) w


/-- cosh inverse family. -/
@[dlmf 4.37.E27, dlmf 4.37.E30]
theorem cosh_inverse_family (z w : ℂ) :
    Complex.cosh w=z ↔ ∃ k : ℤ, w=arccosh z+2*(k:ℂ)*π*I ∨ w= -arccosh z+2*(k:ℂ)*π*I := by
  have hrot:Complex.cosh w=z ↔ Complex.cos (arccosh z*I)=Complex.cos (w*I) := by
    rw [Complex.cos_mul_I,Complex.cos_mul_I,hyper_cosh_arccosh]
    exact eq_comm
  rw [hrot,Complex.cos_eq_cos_iff]
  constructor
  · rintro ⟨k,hk|hk⟩
    · refine ⟨-k,Or.inl ?_⟩
      push_cast
      linear_combination -I*hk+(w-arccosh z)*Complex.I_sq
    · refine ⟨-k,Or.inr ?_⟩
      push_cast
      linear_combination -I*hk+(w+arccosh z)*Complex.I_sq
  · rintro ⟨k,hk|hk⟩
    · refine ⟨-k,Or.inl ?_⟩
      push_cast
      linear_combination I*hk+(2*k*π)*Complex.I_sq
    · refine ⟨-k,Or.inr ?_⟩
      push_cast
      linear_combination I*hk+(2*k*π)*Complex.I_sq


/-- `cosh` and `sinh` in terms of `exp (2w)`, after multiplying by `2 exp w`. -/
private lemma hypR4_cosh_sinh_exp (w : ℂ) :
    2*Complex.exp w*Complex.cosh w = Complex.exp (2*w)+1 ∧
      2*Complex.exp w*Complex.sinh w = Complex.exp (2*w)-1 := by
  have h2 : Complex.exp (2*w) = Complex.exp w*Complex.exp w := by
    rw [← Complex.exp_add]; ring_nf
  have h1 : Complex.exp w*Complex.exp (-w) = 1 := by rw [← Complex.exp_add]; simp
  rw [Complex.cosh, Complex.sinh, h2]
  constructor
  · linear_combination h1
  · linear_combination -h1

/-- tanh inverse family. -/
@[dlmf 4.37.E28, dlmf 4.37.E31]
theorem tanh_inverse_family {z w : ℂ} (hz : z≠1 ∧ z≠ -1) :
    w ∈ arctanhValues z ↔ ∃ k : ℤ, w=arctanh z+(k:ℂ)*π*I := by
  have hm : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.1)
  have hA := hypR4_arctanh_exp z hz.1 hz.2
  have key : w ∈ arctanhValues z ↔ Complex.exp (2*w) = Complex.exp (2*arctanh z) := by
    obtain ⟨hc, hs⟩ := hypR4_cosh_sinh_exp w
    have hE : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
    constructor
    · rintro ⟨hc0, ht⟩
      rw [Complex.tanh_eq_sinh_div_cosh, div_eq_iff hc0] at ht
      apply mul_right_cancel₀ hm
      rw [hA]
      linear_combination -hs + (z)*hc + 2*Complex.exp w*ht
    · intro h
      have h' : Complex.exp (2*w)*(1-z) = 1+z := by rw [h, hA]
      have hc0 : Complex.cosh w ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hc
        have : (2:ℂ) = 0 := by linear_combination -h' - (1-z)*hc
        norm_num at this
      refine ⟨hc0, ?_⟩
      rw [Complex.tanh_eq_sinh_div_cosh, div_eq_iff hc0]
      apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hE)
      linear_combination hs - z*hc + h'
  rw [key, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by linear_combination hn/2⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by linear_combination 2*hn⟩

/-- The open inverse-cosh domain is star-convex about `2`. -/
private lemma hypR4_acosh_starConvex : StarConvex ℝ (2:ℂ) arccoshDomain := by
  intro y hy a b ha hb hab
  have hre : (a • (2:ℂ) + b • y).re = 2*a + b*y.re := by simp; ring
  have him : (a • (2:ℂ) + b • y).im = b*y.im := by simp
  rcases hy with hi | hr
  · rcases eq_or_lt_of_le hb with hb0 | hb0
    · right; rw [hre, ← hb0]; linarith
    · left; rw [him]; exact mul_ne_zero hb0.ne' hi
  · right; rw [hre]
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · rw [← hb0]; linarith
    · nlinarith [mul_pos hb0 (sub_pos.mpr hr)]

/-- A real point of the inverse-sech domain lies in `(0,1)`. -/
private lemma hypR4_asech_real {z : ℂ} (hz : z ∈ arcsechDomain) (hy : z.im = 0) :
    0 < z.re ∧ z.re < 1 := by
  obtain ⟨hz0, hi⟩ := hz
  have he : z = (z.re:ℂ) := Complex.ext (by simp) (by simp [hy])
  have hx0 : z.re ≠ 0 := fun h => hz0 (by rw [he, h]; simp)
  rw [he, ← Complex.ofReal_inv] at hi
  rcases hi with hi | hi
  · simp at hi
  · rw [Complex.ofReal_re] at hi
    have hxpos : 0 < z.re := by
      by_contra hc; replace hc := not_lt.mp hc
      have : z.re⁻¹ ≤ 0 := inv_nonpos.mpr hc
      linarith
    exact ⟨hxpos, by rwa [one_lt_inv₀ hxpos] at hi⟩

/-- `z √(z⁻¹-1) √(z⁻¹+1)` is the principal `√(1-z²)` on the whole inverse-sech domain. -/
private lemma hypR4_asech_root {z : ℂ} (hz : z ∈ arcsechDomain) :
    z*(Complex.sqrt (z⁻¹-1)*Complex.sqrt (z⁻¹+1)) = Complex.sqrt (1-z^2) := by
  have hVo : IsOpen arcsechDomain := by
    have hA : IsOpen arccoshDomain := by
      change IsOpen ({z:ℂ | z.im≠0}∪{z:ℂ | 1<z.re})
      exact (isOpen_ne.preimage Complex.continuous_im).union
        (isOpen_lt continuous_const Complex.continuous_re)
    have : arcsechDomain = {z : ℂ | z ≠ 0} ∩ (fun z : ℂ => z⁻¹) ⁻¹' arccoshDomain := rfl
    rw [this]
    exact continuousOn_inv₀.isOpen_inter_preimage isOpen_ne hA
  have h0A : (0:ℂ) ∉ arccoshDomain := by
    rintro (h | h)
    · simp at h
    · norm_num at h
  have hVc : IsPreconnected arcsechDomain := by
    have h2 : (2:ℂ) ∈ arccoshDomain := Or.inr (by norm_num)
    have hc := (hypR4_acosh_starConvex.isPathConnected h2).isConnected.isPreconnected
    have himg : arcsechDomain = (fun z : ℂ => z⁻¹) '' arccoshDomain := by
      ext z
      constructor
      · rintro ⟨hz0, hz⟩; exact ⟨z⁻¹, hz, inv_inv z⟩
      · rintro ⟨w, hw, rfl⟩
        have hw0 : w ≠ 0 := fun h => h0A (h ▸ hw)
        exact ⟨inv_ne_zero hw0, by rwa [inv_inv]⟩
    rw [himg]
    exact hc.image _ (continuousOn_inv₀.mono fun w hw => fun h => h0A (h ▸ hw))
  have hslit : ∀ w ∈ arcsechDomain, 1-w^2 ∈ Complex.slitPlane := by
    intro w hw
    rw [Complex.mem_slitPlane_iff]
    by_cases hy : w.im = 0
    · left
      obtain ⟨h1, h2⟩ := hypR4_asech_real hw hy
      simp [pow_two, Complex.mul_re, hy]; nlinarith
    · by_cases hx : w.re = 0
      · left; simp [pow_two, Complex.mul_re, hx]; nlinarith [sq_nonneg w.im]
      · right; simp [pow_two, Complex.mul_im]
        intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hx) hy; linear_combination -h
  have hr : AnalyticOnNhd ℂ (fun w => w*(Complex.sqrt (w⁻¹-1)*Complex.sqrt (w⁻¹+1))) arcsechDomain := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    obtain ⟨h1, h2⟩ := hypR4_acosh_slit hw.2
    have hw0 := hw.1
    exact (differentiableAt_id.mul
      (((Complex.differentiableAt_sqrt h1).comp w
        (by fun_prop (disch := exact hw0) : DifferentiableAt ℂ (fun w : ℂ => w⁻¹-1) w)).mul
      ((Complex.differentiableAt_sqrt h2).comp w
        (by fun_prop (disch := exact hw0) : DifferentiableAt ℂ (fun w : ℂ => w⁻¹+1) w)))).differentiableWithinAt
  have hs : AnalyticOnNhd ℂ (fun w => Complex.sqrt (1-w^2)) arcsechDomain := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    exact ((Complex.differentiableAt_sqrt (hslit w hw)).comp w
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1-w^2) w)).differentiableWithinAt
  have hhalf : (1/2:ℂ) ∈ arcsechDomain := ⟨by norm_num, Or.inr (by norm_num)⟩
  have h1 : Complex.sqrt 1 = 1 := by simp [Complex.sqrt]
  have hanchor : (1/2:ℂ)*(Complex.sqrt ((1/2:ℂ)⁻¹-1)*Complex.sqrt ((1/2:ℂ)⁻¹+1)) =
      Complex.sqrt (1-(1/2:ℂ)^2) := by
    rw [show (1/2:ℂ)⁻¹-1 = 1 by norm_num, show (1/2:ℂ)⁻¹+1 = 3 by norm_num, h1, one_mul]
    symm
    apply hypR4_sqrt_eq_of_sq
    · rw [mul_pow, trig_sqrt_sq]; norm_num
    · have : 0 < (Complex.sqrt 3).re := by
        rw [Complex.sqrt, Complex.cpow_inv_two_re]
        apply Real.sqrt_pos.mpr; norm_num
      simpa using this
  refine hypR4_sq_eq_continuation hVo hVc hr hs ?_ hhalf hanchor ?_ z hz
  · intro w hw
    have hw0 := hw.1
    rw [mul_pow, mul_pow, trig_sqrt_sq, trig_sqrt_sq, trig_sqrt_sq]; field_simp; ring
  · intro h
    have := trig_sqrt_sq (1-(1/2:ℂ)^2)
    rw [h] at this; norm_num at this

/-- On the inverse-sech domain, `1-z²` lies in the slit plane. -/
private lemma hypR4_asech_slit {w : ℂ} (hw : w ∈ arcsechDomain) :
    1-w^2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hy : w.im = 0
  · left
    obtain ⟨h1, h2⟩ := hypR4_asech_real hw hy
    simp [pow_two, Complex.mul_re, hy]; nlinarith
  · by_cases hx : w.re = 0
    · left; simp [pow_two, Complex.mul_re, hx]; nlinarith [sq_nonneg w.im]
    · right; simp [pow_two, Complex.mul_im]
      intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hx) hy; linear_combination -h

/-- The interrelation example in §4.37(vi), with compatible principal branches. -/
theorem arcsech_arccoth_interrelation {a : ℂ} (hre : 0<a.re) (ha : a∈arcsechDomain)
    (hr : (Complex.sqrt (1-a^2))⁻¹∈arccothDomain) :
    arcsech a=arccoth ((Complex.sqrt (1-a^2))⁻¹) := by
  have ha0 : a ≠ 0 := ha.1
  set q := Complex.sqrt (1-a^2) with hqdef
  have hq2 : q^2 = 1-a^2 := trig_sqrt_sq _
  have hqre : 0 ≤ q.re := by
    rw [hqdef, Complex.sqrt, Complex.cpow_inv_two_re]; exact Real.sqrt_nonneg _
  have hq0 : q ≠ 0 := by
    intro h; rw [h] at hq2
    exact Complex.slitPlane_ne_zero (hypR4_asech_slit ha) (by rw [← hq2]; ring)
  have hq1 : 1+q ≠ 0 := by
    intro h; have : q = -1 := by linear_combination h
    rw [this] at hqre; norm_num at hqre
  have hqm : 1-q ≠ 0 := by
    intro h; have : q = 1 := by linear_combination -h
    rw [this] at hq2
    exact ha0 (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination hq2))
  set u := (1+q)/a with hu
  have hu0 : u ≠ 0 := div_ne_zero hq1 ha0
  have huinv : u + u⁻¹ = 2/a := by
    rw [hu, inv_div]; field_simp; linear_combination hq2
  have hure : 0 < u.re := by
    by_contra hc; replace hc := not_lt.mp hc
    have h1 : u⁻¹.re ≤ 0 := by
      rw [Complex.inv_re]; exact div_nonpos_of_nonpos_of_nonneg hc (Complex.normSq_nonneg _)
    have h2 : 0 < (2/a).re := by
      rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im]
      simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      have : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
      positivity
    rw [← huinv, Complex.add_re] at h2
    linarith
  have hS : a⁻¹ + Complex.sqrt (a⁻¹-1)*Complex.sqrt (a⁻¹+1) = u := by
    have e := hypR4_asech_root ha
    rw [← hqdef] at e
    rw [hu, eq_div_iff ha0]
    linear_combination e + mul_inv_cancel₀ ha0
  have hL : arcsech a = Complex.log u := by
    rw [arcsech, arccosh, hS]
  have hR : arccoth q⁻¹ = Complex.log (u^2)/2 := by
    rw [arccoth_eq_inv (inv_ne_zero hq0), inv_inv, arctanh]
    congr 2
    rw [hu, div_pow]
    field_simp
    linear_combination hq2
  rw [hL, hR]
  have harg : |Complex.arg u| < π/2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hure)
  have hpow : u^2 = Complex.exp (2*Complex.log u) := by
    rw [two_mul, Complex.exp_add, Complex.exp_log hu0]; ring
  rw [hpow, Complex.log_exp]
  · ring
  · rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.im_ofReal_mul, Complex.log_im]
    linarith [(abs_lt.mp harg).1]
  · rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.im_ofReal_mul, Complex.log_im]
    linarith [(abs_lt.mp harg).2]

/-- Central-binomial coefficient divided by 4^n, used in the inverse expansions. -/
def hyperbolicCentral (n : ℕ) : ℂ := (Nat.choose (2*n) n:ℂ)/(4:ℂ)^n
/-- hasSum arcsinh. -/
@[dlmf 4.38.E1]
theorem hasSum_arcsinh {z : ℂ} (hz : ‖z‖<1) : HasSum (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral n/(2*n+1:ℂ)*z^(2*n+1)) (arcsinh z) := by
  sorry

/-- hasSum arcsinh large. -/
@[dlmf 4.38.E2]
theorem hasSum_arcsinh_large {z : ℂ} (hz : 0<z.re) (hn : 1<‖z‖) : HasSum (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2))) (arcsinh z-Complex.log (2*z)) := by
  sorry

/-- hasSum arccosh large. -/
@[dlmf 4.38.E3]
theorem hasSum_arccosh_large {z : ℂ} (hn : 1<‖z‖) : HasSum (fun n : ℕ => hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2))) (Complex.log (2*z)-arccosh z) := by
  sorry

/-- hasSum arccosh near one. -/
@[dlmf 4.38.E4]
theorem hasSum_arccosh_near_one {z : ℂ} (hz : 0<z.re) (hn : ‖z-1‖≤2) : HasSum (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral n/((2:ℂ)^n*(2*n+1:ℂ))*(z-1)^n) (if z=1 then 1 else arccosh z/Complex.sqrt (2*(z-1))) := by
  sorry

/-- Natural-order odd series for the principal `arctanh` on the closed disk minus `±1`. -/
theorem errC_tendsto_arctanh {z : ℂ} (hn : ‖z‖ ≤ 1) (hz : z ≠ 1 ∧ z ≠ -1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (2*n+1) / (2*n+1 : ℂ))
      atTop (𝓝 (arctanh z)) := by
  have h := (logBoundary_odd hn hz.1 hz.2).div_const 2
  rw [arctanh]
  refine h.congr (fun N => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

/-- Absolute summability of the odd power series strictly inside the unit disk. -/
theorem errC_summable_odd {w : ℂ} (hn : ‖w‖ < 1) :
    Summable (fun n : ℕ => w ^ (2*n+1) / (2*n+1 : ℂ)) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖w‖ ^ (2*n+1)) ?_ (fun n => ?_)
  · have hg : Summable (fun n : ℕ => ‖w‖ * (‖w‖ ^ 2) ^ n) :=
      (summable_geometric_of_lt_one (by positivity)
        (by nlinarith [norm_nonneg w])).mul_left _
    refine hg.congr (fun n => ?_)
    ring
  · rw [norm_div, norm_pow]
    have h1 : (1 : ℝ) ≤ ‖(2*n+1 : ℂ)‖ := by
      have : (2*n+1 : ℂ) = ((2*n+1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    exact div_le_self (by positivity) h1

/-- The odd principal-logarithm correction outside the unit disk. -/
theorem errC_arctanh_large_eq {z : ℂ} (hz : z.im ≠ 0) :
    arctanh z - (if 0 < z.im then 1 else -1) * I * π / 2 =
      Complex.log ((1 + z⁻¹) / (1 - z⁻¹)) / 2 := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have h1 : 1 - z ≠ 0 := by
    intro h; apply hz; have := congrArg Complex.im h; simp at this; linarith
  have hz1 : z - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
  set v := (1 + z) / (1 - z) with hv
  have hu : (1 + z⁻¹) / (1 - z⁻¹) = -v := by
    rw [hv]; field_simp; ring
  rw [hu, arctanh, ← hv]
  have hvim : v.im = 2 * z.im / Complex.normSq (1 - z) := by
    rw [hv, Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp
    ring
  have hns : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr h1
  have hu0 : -v ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [hvim] at this
    rcases this with h | h
    · exact hz h
    · exact h1 h
  split_ifs with hpos
  · -- Im v > 0, so Im(-v) < 0 and log v = log(-v) + iπ
    have him : (-v).im < 0 := by simp [hvim]; positivity
    have harg := Complex.arg_neg_iff.mpr him
    have hl : Complex.log v = Complex.log (-v) + π * I := by
      have he : Complex.exp (Complex.log (-v) + π * I) = v := by
        rw [Complex.exp_add, Complex.exp_log hu0, Complex.exp_pi_mul_I]; ring
      conv_lhs => rw [← he]
      rw [Complex.log_exp]
      all_goals try simp only [Complex.add_im, Complex.log_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      all_goals nlinarith [Complex.neg_pi_lt_arg (-v), Complex.arg_le_pi (-v), Real.pi_pos]
    rw [hl]; ring
  · have hneg : z.im < 0 := lt_of_le_of_ne (not_lt.mp hpos) hz
    have him : 0 < (-v).im := by
      simp [hvim]; exact div_neg_of_neg_of_pos (by linarith) hns
    have harg : 0 < (-v).arg := by
      refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him.le) (fun h => ?_)
      have := (Complex.arg_eq_zero_iff.mp h.symm).2
      linarith
    have hl : Complex.log v = Complex.log (-v) - π * I := by
      have he : Complex.exp (Complex.log (-v) - π * I) = v := by
        rw [Complex.exp_sub, Complex.exp_log hu0, Complex.exp_pi_mul_I]; field_simp
      conv_lhs => rw [← he]
      rw [Complex.log_exp]
      all_goals try simp only [Complex.sub_im, Complex.log_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      all_goals nlinarith [Complex.neg_pi_lt_arg (-v), Complex.arg_le_pi (-v), Real.pi_pos]
    rw [hl]; ring

/-- Maclaurin series of the principal `arctanh` on the full DLMF domain `|z| ≤ 1`, `z ≠ ±1`,
as a limit of natural-order partial sums (the boundary series converge only conditionally). -/
@[dlmf 4.38.E5]
theorem tendsto_arctanh_series {z : ℂ} (hn : ‖z‖ ≤ 1) (hz : z ≠ 1 ∧ z ≠ -1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (2*n+1) / (2*n+1 : ℂ))
      atTop (𝓝 (arctanh z)) :=
  errC_tendsto_arctanh hn hz

/-- Maclaurin series of the principal `arctanh`, unordered sum strictly inside the unit disk.
Corrected from the earlier transcription: it asserted unordered `HasSum` on the closed disk,
which is false on the unit circle (at `z = i` the term norms are `1/(2n+1)`); the boundary
points are covered by `tendsto_arctanh_series` in natural order. -/
@[dlmf 4.38.E5]
theorem hasSum_arctanh {z : ℂ} (hn : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (2*n+1) / (2*n+1 : ℂ)) (arctanh z) := by
  have hs := errC_summable_odd hn
  have hz : z ≠ 1 ∧ z ≠ -1 := by
    constructor <;> rintro rfl <;> simp at hn
  rw [← tendsto_nhds_unique hs.hasSum.tendsto_sum_nat (errC_tendsto_arctanh hn.le hz)]
  exact hs.hasSum

/-- Reciprocal series of the principal `arctanh` on the full DLMF domain `|z| ≥ 1`, `Im z ≷ 0`,
as a limit of natural-order partial sums. -/
@[dlmf 4.38.E6]
theorem tendsto_arctanh_large_series {z : ℂ} (hn : 1 ≤ ‖z‖) (hz : z.im ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / ((2*n+1 : ℂ) * z ^ (2*n+1)))
      atTop (𝓝 (arctanh z - (if 0 < z.im then 1 else -1) * I * π / 2)) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hw : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact (inv_le_one₀ (norm_pos_iff.mpr hz0)).2 hn
  have hp : z⁻¹ ≠ 1 := by
    intro h; apply hz; rw [inv_eq_one.mp h]; simp
  have hm : z⁻¹ ≠ -1 := by
    intro h; apply hz; rw [show z = -1 by simpa using congrArg (fun w : ℂ => w⁻¹) h]; simp
  have h := (logBoundary_odd hw hp hm).div_const 2
  rw [errC_arctanh_large_eq hz]
  refine h.congr (fun N => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [inv_pow]
  field_simp

/-- Reciprocal series of the principal `arctanh`, unordered sum strictly outside the unit disk.
Corrected from the earlier transcription: it asserted unordered `HasSum` for `|z| ≥ 1`, which is
false on the unit circle (at `z = i` the term norms are `1/(2n+1)`); the boundary points are
covered by `tendsto_arctanh_large_series` in natural order. -/
@[dlmf 4.38.E6]
theorem hasSum_arctanh_large {z : ℂ} (hn : 1 < ‖z‖) (hz : z.im ≠ 0) :
    HasSum (fun n : ℕ => 1 / ((2*n+1 : ℂ) * z ^ (2*n+1)))
      (arctanh z - (if 0 < z.im then 1 else -1) * I * π / 2) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hn; linarith
  have hw : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hn
  have hs : Summable (fun n : ℕ => 1 / ((2*n+1 : ℂ) * z ^ (2*n+1))) :=
    (errC_summable_odd hw).congr (fun n => by rw [inv_pow]; field_simp)
  rw [← tendsto_nhds_unique hs.hasSum.tendsto_sum_nat
    (tendsto_arctanh_large_series hn.le hz)]
  exact hs.hasSum

/-- hasSum arctanh transformed. -/
@[dlmf 4.38.E7]
theorem hasSum_arctanh_transformed {z : ℂ} (hz : (z^2).re<1/2) : HasSum (fun n : ℕ => (4:ℂ)^n*(n.factorial:ℂ)^2/((2*n+1).factorial:ℂ)*(z^2/(z^2-1))^n) (if z=0 then 1 else (1-z^2)/z*arctanh z) := by
  sorry

/-- arctanh transformed region. -/
@[dlmf 4.38.E8]
theorem arctanh_transformed_region (z : ℂ) : (z^2).re<1/2 ↔ z.re^2-z.im^2<1/2 := by
  simp [Complex.mul_re,pow_two]


/-- hasDerivAt arcsinh. -/
@[dlmf 4.38.E9]
theorem hasDerivAt_arcsinh {z : ℂ} (hz : z∈arcsinhDomain) : HasDerivAt arcsinh ((Complex.sqrt (1+z^2))⁻¹) z := by
  exact hyper_hasDerivAt_arcsinh hz


/-- hasDerivAt arccosh. -/
@[dlmf 4.38.E10]
theorem hasDerivAt_arccosh {z : ℂ} (hz : z∈arccoshDomain) : HasDerivAt arccosh ((Complex.sqrt (z-1)*Complex.sqrt (z+1))⁻¹) z := by
  exact hypR4_hasDerivAt_arccosh hz

/-- hasDerivAt arccosh signed. -/
@[dlmf 4.38.E10]
theorem hasDerivAt_arccosh_signed {z : ℂ} (hz : z∈arccoshDomain) (hre : z.re≠0) : HasDerivAt arccosh ((if 0<z.re then 1 else -1)*(Complex.sqrt (z^2-1))⁻¹) z := by
  have h := hypR4_hasDerivAt_arccosh hz
  rw [hypR4_acosh_root_signed hz hre] at h
  convert h using 1
  split_ifs <;> simp

/-- hasDerivAt arctanh. -/
@[dlmf 4.38.E11]
theorem hasDerivAt_arctanh {z : ℂ} (hz : z∈arctanhDomain) : HasDerivAt arctanh (1/(1-z^2)) z := by
  exact hyper_hasDerivAt_arctanh hz


/-- hasDerivAt arccsch. -/
@[dlmf 4.38.E12]
theorem hasDerivAt_arccsch {z : ℂ} (hz : z∈arccschDomain) : HasDerivAt arccsch (-1/(z^2*Complex.sqrt (1+z⁻¹^2))) z := by
  have hd:=(hyper_hasDerivAt_arcsinh hz.2).comp z ((hasDerivAt_id z).inv hz.1)
  convert hd using 1
  · rfl
  · dsimp only [id]
    field_simp <;> ring


/-- `1 + w²` lies in the principal slit plane on the open inverse-sinh domain. -/
private lemma hypR4_one_add_sq_slit {w : ℂ} (hw : w.re ≠ 0 ∨ |w.im| < 1) :
    1+w^2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases hw with hr | hi
  · by_cases hy : w.im = 0
    · left; simp [pow_two, Complex.mul_re, hy]; nlinarith [sq_nonneg w.re]
    · right; simp [pow_two, Complex.mul_im]
      intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hr) hy; linear_combination h
  · left
    simp [pow_two, Complex.mul_re]
    nlinarith [abs_lt.mp hi, sq_nonneg w.re]

/-- On the right half-plane `z √(1+z⁻²)` is the principal `√(1+z²)`. -/
private lemma hypR4_acsch_root_pos {z : ℂ} (hre : 0 < z.re) :
    z*Complex.sqrt (1+z⁻¹^2) = Complex.sqrt (1+z^2) := by
  set V := {z : ℂ | 0 < z.re}
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVc : IsPreconnected V := (convex_halfSpace_re_gt 0).isPreconnected
  have h1V : (1:ℂ) ∈ V := by show (0:ℝ) < (1:ℂ).re; norm_num
  have hinvre : ∀ w ∈ V, 0 < (w⁻¹).re := fun w hw => by
    rw [Complex.inv_re]
    have : w ≠ 0 := fun h => by subst h; exact absurd (show (0:ℝ) < (0:ℂ).re from hw) (by simp)
    exact div_pos hw (Complex.normSq_pos.mpr this)
  have hr : AnalyticOnNhd ℂ (fun w => w*Complex.sqrt (1+w⁻¹^2)) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    have hw0 : w ≠ 0 := fun h => by subst h; exact absurd (show (0:ℝ) < (0:ℂ).re from hw) (by simp)
    have hsl := hypR4_one_add_sq_slit (Or.inl (hinvre w hw).ne')
    exact (differentiableAt_id.mul ((Complex.differentiableAt_sqrt hsl).comp w
      (by fun_prop (disch := exact hw0) : DifferentiableAt ℂ (fun w : ℂ => 1+w⁻¹^2) w))).differentiableWithinAt
  have hs : AnalyticOnNhd ℂ (fun w => Complex.sqrt (1+w^2)) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    have hsl := hypR4_one_add_sq_slit (Or.inl (ne_of_gt hw))
    exact ((Complex.differentiableAt_sqrt hsl).comp w
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1+w^2) w)).differentiableWithinAt
  refine hypR4_sq_eq_continuation hVo hVc hr hs ?_ h1V ?_ ?_ z hre
  · intro w hw
    have hw0 : w ≠ 0 := fun h => by subst h; exact absurd (show (0:ℝ) < (0:ℂ).re from hw) (by simp)
    rw [mul_pow, trig_sqrt_sq, trig_sqrt_sq]; field_simp; ring
  · norm_num
  · intro h
    have := trig_sqrt_sq (1+(1:ℂ)^2)
    rw [h] at this; norm_num at this

/-- `z √(1+z⁻²) = ±√(1+z²)` according to the sign of `Re z`. -/
private lemma hypR4_acsch_root_signed {z : ℂ} (hre : z.re ≠ 0) :
    z*Complex.sqrt (1+z⁻¹^2) = (if 0<z.re then 1 else -1)*Complex.sqrt (1+z^2) := by
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · simp only [show ¬ (0 < z.re) from not_lt.mpr hneg.le, ↓reduceIte]
    have h := hypR4_acsch_root_pos (z := -z) (by simpa using hneg)
    rw [inv_neg, neg_sq, neg_sq] at h
    linear_combination -h
  · simp only [hpos, ↓reduceIte, one_mul]; exact hypR4_acsch_root_pos hpos

/-- hasDerivAt arccsch signed. -/
@[dlmf 4.38.E12]
theorem hasDerivAt_arccsch_signed {z : ℂ} (hz : z∈arccschDomain) (hre : z.re≠0) : HasDerivAt arccsch (-(if 0<z.re then 1 else -1)/(z*Complex.sqrt (1+z^2))) z := by
  have h := hasDerivAt_arccsch hz
  have hz0 : z ≠ 0 := hz.1
  have e := hypR4_acsch_root_signed hre
  convert h using 1
  rw [show z^2*Complex.sqrt (1+z⁻¹^2) = z*(z*Complex.sqrt (1+z⁻¹^2)) by ring, e]
  split_ifs <;> field_simp

/-- hasDerivAt arcsech. -/
@[dlmf 4.38.E13]
theorem hasDerivAt_arcsech {z : ℂ} (hz : z∈arcsechDomain) : HasDerivAt arcsech (-1/(z*Complex.sqrt (1-z^2))) z := by
  have hz0 : z ≠ 0 := hz.1
  have h := (hypR4_hasDerivAt_arccosh hz.2).comp z (hasDerivAt_inv hz0)
  have e := hypR4_asech_root hz
  have hS : Complex.sqrt (z⁻¹-1)*Complex.sqrt (z⁻¹+1) ≠ 0 := hypR4_acosh_root_ne hz.2
  have hf : arcsech = arccosh ∘ (fun w : ℂ => w⁻¹) := rfl
  rw [hf]
  convert h using 1
  rw [← e]
  field_simp

/-- hasDerivAt arccoth. -/
@[dlmf 4.38.E14]
theorem hasDerivAt_arccoth {z : ℂ} (hz : z∈arccothDomain) : HasDerivAt arccoth (1/(1-z^2)) z := by
  obtain ⟨hz0,hi⟩:=hyper_acoth_inv_mem hz
  have hd:=(hyper_hasDerivAt_arctanh hi).comp z ((hasDerivAt_id z).inv hz0)
  have hd':HasDerivAt (fun w:ℂ=>arctanh w⁻¹) (1/(1-z^2)) z := by
    convert hd using 1
    · rfl
    · dsimp only [id]
      field_simp [hz0]
      have heq:(1-z^2)⁻¹= -(-1+z^2)⁻¹ := by
        rw [show (1-z^2)= -(-1+z^2) by ring,inv_neg]
      convert heq using 1 <;> ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz0] with w hw
  exact arccoth_eq_inv hw


/-- The former unrestricted full-set acquisition of 4.38.15 loses branch compatibility:
at u=v=i it includes zero on the right, whereas the actual sum cannot contain zero.
This diagnoses the acquisition, not the branch-qualified DLMF formula. -/
theorem arcsinh_values_add_unrestricted_counterexample :
    (0:ℂ)∈{w | ∃ r s : ℂ,r^2=1+I^2 ∧ s^2=1+I^2 ∧ w∈arcsinhValues (I*r+I*s)} ∧
    (0:ℂ)∉Set.image2 (fun a b : ℂ=>a+b) (arcsinhValues I) (arcsinhValues I) := by
  constructor
  · refine ⟨0,0,?_,?_,?_⟩ <;> simp [arcsinhValues]
  · rintro ⟨a,ha,b,hb,hab⟩
    change Complex.sinh a=I at ha
    change Complex.sinh b=I at hb
    have hba:b= -a := by linear_combination hab
    rw [hba,Complex.sinh_neg,ha] at hb
    have hc:(I:ℂ)=0 := by linear_combination -hb/2
    exact Complex.I_ne_zero hc

/-- DLMF4.38.15 with compatible branches: the same two square-root witnesses determine
both sinh and cosh of the sum. The cosh condition retains the missing parity information,
including u=v=i; every pair of complex parameters and every inverse branch is retained. -/
@[dlmf 4.38.E15]
theorem arcsinh_values_add (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a+b) (arcsinhValues u) (arcsinhValues v)=
      {w | ∃ r s : ℂ,r^2=1+v^2 ∧ s^2=1+u^2 ∧
        w∈arcsinhValues (u*r+v*s) ∧ Complex.cosh w=s*r+u*v} := by
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change Complex.sinh a=u at ha
    change Complex.sinh b=v at hb
    refine ⟨Complex.cosh b,Complex.cosh a,?_,?_,?_,?_⟩
    · rw [Complex.cosh_sq,hb];ring
    · rw [Complex.cosh_sq,ha];ring
    · change Complex.sinh (a+b)=u*Complex.cosh b+v*Complex.cosh a
      rw [Complex.sinh_add,ha,hb]
      ring
    · rw [Complex.cosh_add,ha,hb] <;> ring
  · rintro ⟨r,s,hr,hs,hw,hc⟩
    have ha:=hyper_sinh_cosh_log_lift u s hs
    let a:=Complex.log (s+u)
    refine ⟨a,ha.1,w-a,?_,by ring⟩
    change Complex.sinh (w-a)=v
    change Complex.sinh w=u*r+v*s at hw
    rw [Complex.sinh_sub,ha.1,ha.2,hw,hc]
    linear_combination v*hs


/-- arccosh values add. -/
@[dlmf 4.38.E16]
theorem arccosh_values_add (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a+b) (arccoshValues u) (arccoshValues v)=
      {w | ∃ r : ℂ, r^2=(u^2-1)*(v^2-1) ∧ w ∈ arccoshValues (u*v+r)} := by
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change Complex.cosh a=u at ha
    change Complex.cosh b=v at hb
    refine ⟨Complex.sinh a*Complex.sinh b,?_,?_⟩
    · simp only [mul_pow,Complex.sinh_sq,ha,hb]
    · change Complex.cosh (a+b)=u*v+Complex.sinh a*Complex.sinh b
      rw [Complex.cosh_add,ha,hb]
  · rintro ⟨r,hr,hc⟩
    change Complex.cosh w=u*v+r at hc
    have hs:(v-u*Complex.cosh w)^2=(Complex.sinh w*Complex.sinh (arccosh u))^2 := by
      simp only [mul_pow,Complex.sinh_sq,hyper_cosh_arccosh,hc]
      linear_combination hr
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs|hs
    · refine ⟨-arccosh u,?_,w+arccosh u,?_,by ring⟩
      · change Complex.cosh (-arccosh u)=u
        rw [Complex.cosh_neg,hyper_cosh_arccosh]
      · change Complex.cosh (w+arccosh u)=v
        rw [Complex.cosh_add,hyper_cosh_arccosh]
        linear_combination -hs
    · refine ⟨arccosh u,hyper_cosh_arccosh u,w-arccosh u,?_,by ring⟩
      change Complex.cosh (w-arccosh u)=v
      rw [Complex.cosh_sub,hyper_cosh_arccosh]
      linear_combination -hs


/-- Off `±1`, the finite inverse-tanh values are the solutions of `exp (2w) (1-z) = 1+z`. -/
private lemma hypR4_mem_arctanhValues_iff {z w : ℂ} (h1 : z ≠ 1) (h2 : z ≠ -1) :
    w ∈ arctanhValues z ↔ Complex.exp (2*w)*(1-z) = 1+z := by
  obtain ⟨hc, hs⟩ := hypR4_cosh_sinh_exp w
  have hE : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  constructor
  · rintro ⟨hc0, ht⟩
    rw [Complex.tanh_eq_sinh_div_cosh, div_eq_iff hc0] at ht
    linear_combination -hs + z*hc + 2*Complex.exp w*ht
  · intro h'
    have hc0 : Complex.cosh w ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hc
      have : (2:ℂ) = 0 := by linear_combination -h' - (1-z)*hc
      norm_num at this
    refine ⟨hc0, ?_⟩
    rw [Complex.tanh_eq_sinh_div_cosh, div_eq_iff hc0]
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hE)
    linear_combination hs - z*hc + h'

/-- Off `±1`, the finite inverse-coth values are the solutions of `exp (2w) (z-1) = z+1`. -/
private lemma hypR4_mem_arccothValues_iff {z w : ℂ} (h1 : z ≠ 1) (h2 : z ≠ -1) :
    w ∈ arccothValues z ↔ Complex.exp (2*w)*(z-1) = z+1 := by
  obtain ⟨hc, hs⟩ := hypR4_cosh_sinh_exp w
  have hE : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  constructor
  · rintro ⟨hs0, ht⟩
    rw [coth, div_eq_iff hs0] at ht
    linear_combination hc - z*hs - 2*Complex.exp w*ht
  · intro h'
    have hs0 : Complex.sinh w ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hs
      have : (2:ℂ) = 0 := by linear_combination -h' + (1-z)*hs
      norm_num at this
    refine ⟨hs0, ?_⟩
    rw [coth, div_eq_iff hs0]
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hE)
    linear_combination hc - z*hs - h'

/-- Solution sets of `exp (2w) c = d` add (Minkowski sum) by multiplying the coefficients. -/
private lemma hypR4_expSet_add {c₁ d₁ c₂ d₂ : ℂ} (hc₁ : c₁ ≠ 0) (hd₁ : d₁ ≠ 0) :
    Set.image2 (fun a b : ℂ => a+b) {w | Complex.exp (2*w)*c₁ = d₁} {w | Complex.exp (2*w)*c₂ = d₂} =
      {w | Complex.exp (2*w)*(c₁*c₂) = d₁*d₂} := by
  ext w
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [mul_add, Complex.exp_add, ← ha, ← hb]; ring
  · intro hw
    simp only [Set.mem_ofPred_eq] at hw
    set a := Complex.log (d₁/c₁)/2
    have ha : Complex.exp (2*a)*c₁ = d₁ := by
      rw [show 2*a = Complex.log (d₁/c₁) by simp [a]; ring, Complex.exp_log (div_ne_zero hd₁ hc₁)]
      field_simp
    refine ⟨a, ha, w-a, ?_, by ring⟩
    simp only [Set.mem_ofPred_eq]
    have hEa : Complex.exp (2*a) ≠ 0 := Complex.exp_ne_zero _
    have e : Complex.exp (2*(w-a)) = Complex.exp (2*w)/Complex.exp (2*a) := by
      rw [← Complex.exp_sub]; ring_nf
    rw [e, div_mul_eq_mul_div, div_eq_iff hEa]
    apply mul_left_cancel₀ hc₁
    linear_combination hw - d₂*ha

/-- Solution sets of `exp (2w) c = d` subtract by cross-multiplying the coefficients. -/
private lemma hypR4_expSet_sub {c₁ d₁ c₂ d₂ : ℂ} (hc₁ : c₁ ≠ 0) (hd₁ : d₁ ≠ 0) :
    Set.image2 (fun a b : ℂ => a-b) {w | Complex.exp (2*w)*c₁ = d₁} {w | Complex.exp (2*w)*c₂ = d₂} =
      {w | Complex.exp (2*w)*(c₁*d₂) = d₁*c₂} := by
  have hneg : {w : ℂ | Complex.exp (2*w)*c₂ = d₂} = (fun w => -w) '' {w | Complex.exp (2*w)*d₂ = c₂} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro h; refine ⟨-w, ?_, neg_neg w⟩
      have hE : Complex.exp (2*w) ≠ 0 := Complex.exp_ne_zero _
      rw [show 2*(-w) = -(2*w) by ring, Complex.exp_neg, ← h]; field_simp
    · rintro ⟨b, hb, rfl⟩
      have hE : Complex.exp (2*b) ≠ 0 := Complex.exp_ne_zero _
      rw [show 2*(-b) = -(2*b) by ring, Complex.exp_neg, ← hb]; field_simp
  rw [hneg, Set.image2_image_right, ← hypR4_expSet_add hc₁ hd₁]
  simp only [sub_neg_eq_add]

/-- Two solution sets of `exp (2w) c = d` coincide when the ratios `d/c` agree. -/
private lemma hypR4_expSet_congr {c d c' d' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : c*d' = c'*d) : {w : ℂ | Complex.exp (2*w)*c = d} = {w | Complex.exp (2*w)*c' = d'} := by
  ext w
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hw; apply mul_left_cancel₀ hc; linear_combination c'*hw - h
  · intro hw; apply mul_left_cancel₀ hc'; linear_combination c*hw + h

/-- arctanh values add. -/
@[dlmf 4.38.E17]
theorem arctanh_values_add {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1) (hp : 1+u*v≠0) :
    Set.image2 (fun a b : ℂ => a+b) (arctanhValues u) (arctanhValues v)=arctanhValues ((u+v)/(1+u*v)) := by
  have hu1 : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu.1)
  have hu2 : 1+u ≠ 0 := fun h => hu.2 (by first | linear_combination h | linear_combination -h)
  have hv1 : 1-v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv.1)
  have hv2 : 1+v ≠ 0 := fun h => hv.2 (by first | linear_combination h | linear_combination -h)
  have ht1 : (u+v)/(1+u*v) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hp]; intro h
    exact mul_ne_zero hu1 hv1 (by first | linear_combination h | linear_combination -h)
  have ht2 : (u+v)/(1+u*v) ≠ -1 := by
    rw [Ne, div_eq_iff hp]; intro h
    exact mul_ne_zero hu2 hv2 (by first | linear_combination h | linear_combination -h)
  have ht3 : 1-(u+v)/(1+u*v) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have e0 : arctanhValues (u) = {w : ℂ | Complex.exp (2*w)*(1-(u)) = 1+(u)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hu.1 hu.2
  have e1 : arctanhValues (v) = {w : ℂ | Complex.exp (2*w)*(1-(v)) = 1+(v)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hv.1 hv.2
  have e2 : arctanhValues ((u+v)/(1+u*v)) = {w : ℂ | Complex.exp (2*w)*(1-((u+v)/(1+u*v))) = 1+((u+v)/(1+u*v))} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff ht1 ht2
  rw [e0, e1, e2, hypR4_expSet_add hu1 hu2]
  apply hypR4_expSet_congr (mul_ne_zero hu1 hv1) ht3
  field_simp
  ring

/-- The former mixed full-set acquisitions also discarded branch parity. At u=i,v=1,
their inverse-cosh side admits -pi*i/2, whereas every actual sum or difference has sinh=i. -/
theorem arcsinh_arccosh_values_unrestricted_counterexample :
    (-(π*I/2):ℂ)∈{w | ∃ r s : ℂ,r^2=1+I^2 ∧ s^2=(1:ℂ)^2-1 ∧
      w∈arccoshValues (r+I*s)} ∧
    (-(π*I/2):ℂ)∈{w | ∃ r s : ℂ,r^2=1+I^2 ∧ s^2=(1:ℂ)^2-1 ∧
      w∈arccoshValues (r-I*s)} ∧
    (-(π*I/2):ℂ)∉Set.image2 (fun a b : ℂ=>a+b) (arcsinhValues I) (arccoshValues 1) ∧
    (-(π*I/2):ℂ)∉Set.image2 (fun a b : ℂ=>a-b) (arcsinhValues I) (arccoshValues 1) := by
  have hw:-(π*I/2:ℂ)=(-π/2)*I := by ring
  have hcos:Complex.cosh (-(π*I/2):ℂ)=0 := by
    rw [hw,Complex.cosh_mul_I]
    simp [neg_div]
  have hsin:Complex.sinh (-(π*I/2):ℂ)= -I := by
    rw [hw,Complex.sinh_mul_I]
    simp [neg_div]
  have hnot (σ : ℂ) (hσ : σ=1 ∨ σ= -1) :
      (-(π*I/2):ℂ)∉Set.image2 (fun a b : ℂ=>a+σ*b) (arcsinhValues I) (arccoshValues 1) := by
    rintro ⟨a,ha,b,hb,hab⟩
    change Complex.sinh a=I at ha
    change Complex.cosh b=1 at hb
    have hsb:Complex.sinh b=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.sinh_sq,hb]
      ring
    have hval:Complex.sinh (a+σ*b)=I := by
      rcases hσ with rfl|rfl <;> simp [Complex.sinh_add,Complex.sinh_neg,Complex.cosh_neg,ha,hb,hsb]
    change a+σ*b= -(π*I/2:ℂ) at hab
    rw [hab,hsin] at hval
    have hc:(I:ℂ)=0 := by linear_combination -hval/2
    exact Complex.I_ne_zero hc
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨0,0,?_,?_,?_⟩ <;> simp [arccoshValues,hcos]
  · refine ⟨0,0,?_,?_,?_⟩ <;> simp [arccoshValues,hcos]
  · simpa only [one_mul] using hnot 1 (Or.inl rfl)
  · simpa only [neg_one_mul,sub_eq_add_neg] using hnot (-1) (Or.inr rfl)

/-- DLMF4.38.18 interpreted with shared inverse branches. Both inverse descriptions
retain the paired sinh/cosh equations, including all critical parameter values. -/
@[dlmf 4.38.E18]
theorem arcsinh_arccosh_values_add (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a + b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
        w∈arcsinhValues (u*v + r*s) ∧ Complex.cosh w=v*r + u*s} ∧
    Set.image2 (fun a b : ℂ => a + b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
        w∈arccoshValues (v*r + u*s) ∧ Complex.sinh w=u*v + r*s} := by
  have hfirst :
      Set.image2 (fun a b : ℂ => a + b) (arcsinhValues u) (arccoshValues v)=
        {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
          w∈arcsinhValues (u*v + r*s) ∧ Complex.cosh w=v*r + u*s} := by
    simpa only [one_mul,neg_one_mul,sub_eq_add_neg,arcsinhValues,Set.mem_setOf_eq] using
      hyper_mixed_inverse_fiber u v 1 (Or.inl rfl)
  refine ⟨hfirst,?_⟩
  rw [hfirst]
  ext w
  constructor
  · rintro ⟨r,s,hr,hs,hw,hc⟩
    exact ⟨r,s,hr,hs,hc,hw⟩
  · rintro ⟨r,s,hr,hs,hc,hw⟩
    exact ⟨r,s,hr,hs,hw,hc⟩

/-- arctanh arccoth values add. -/
@[dlmf 4.38.E19]
theorem arctanh_arccoth_values_add {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1)
    (hp : v+u≠0) (hq : u*v+1≠0) :
    Set.image2 (fun a b : ℂ => a+b) (arctanhValues u) (arccothValues v)=arctanhValues ((u*v+1)/(v+u)) ∧
    Set.image2 (fun a b : ℂ => a+b) (arctanhValues u) (arccothValues v)=arccothValues ((v+u)/(u*v+1)) := by
  have hu1 : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu.1)
  have hu2 : 1+u ≠ 0 := fun h => hu.2 (by first | linear_combination h | linear_combination -h)
  have hv1 : v-1 ≠ 0 := sub_ne_zero.mpr hv.1
  have hv2 : v+1 ≠ 0 := fun h => hv.2 (by first | linear_combination h | linear_combination -h)
  have ht1 : (u*v+1)/(v+u) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hp]; intro h
    exact mul_ne_zero hu1 hv1 (by first | linear_combination h | linear_combination -h)
  have ht2 : (u*v+1)/(v+u) ≠ -1 := by
    rw [Ne, div_eq_iff hp]; intro h
    exact mul_ne_zero hu2 hv2 (by first | linear_combination h | linear_combination -h)
  have hs1 : (v+u)/(u*v+1) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hq]; intro h
    exact mul_ne_zero hu1 hv1 (by first | linear_combination h | linear_combination -h)
  have hs2 : (v+u)/(u*v+1) ≠ -1 := by
    rw [Ne, div_eq_iff hq]; intro h
    exact mul_ne_zero hu2 hv2 (by first | linear_combination h | linear_combination -h)
  have ht3 : 1-(u*v+1)/(v+u) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hs3 : (v+u)/(u*v+1)-1 ≠ 0 := sub_ne_zero.mpr hs1
  have e0 : arctanhValues (u) = {w : ℂ | Complex.exp (2*w)*(1-(u)) = 1+(u)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hu.1 hu.2
  have e1 : arccothValues (v) = {w : ℂ | Complex.exp (2*w)*((v)-1) = (v)+1} :=
    Set.ext fun w => hypR4_mem_arccothValues_iff hv.1 hv.2
  have e2 : arctanhValues ((u*v+1)/(v+u)) = {w : ℂ | Complex.exp (2*w)*(1-((u*v+1)/(v+u))) = 1+((u*v+1)/(v+u))} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff ht1 ht2
  have e3 : arccothValues ((v+u)/(u*v+1)) = {w : ℂ | Complex.exp (2*w)*(((v+u)/(u*v+1))-1) = ((v+u)/(u*v+1))+1} :=
    Set.ext fun w => hypR4_mem_arccothValues_iff hs1 hs2
  rw [e0, e1, e2, e3, hypR4_expSet_add hu1 hu2]
  constructor
  · apply hypR4_expSet_congr (mul_ne_zero hu1 hv1) ht3
    field_simp
    ring
  · apply hypR4_expSet_congr (mul_ne_zero hu1 hv1) hs3
    field_simp
    ring

/-- The former unrestricted subtraction acquisition loses the same parity information:
at u=v=i the right side includes pi*i, which is not a difference of two inverse values. -/
theorem arcsinh_values_sub_unrestricted_counterexample :
    (π*I:ℂ)∈{w | ∃ r s : ℂ,r^2=1+I^2 ∧ s^2=1+I^2 ∧ w∈arcsinhValues (I*r-I*s)} ∧
    (π*I:ℂ)∉Set.image2 (fun a b : ℂ=>a-b) (arcsinhValues I) (arcsinhValues I) := by
  constructor
  · refine ⟨0,0,?_,?_,?_⟩ <;> simp [arcsinhValues,Complex.sinh_mul_I]
  · rintro ⟨a,ha,b,hb,hab⟩
    change Complex.sinh a=I at ha
    change Complex.sinh b=I at hb
    have hab':a=b+π*I := by linear_combination hab
    rw [hab',Complex.sinh_add_pi_mul_I,hb] at ha
    have hc:(I:ℂ)=0 := by linear_combination -ha/2
    exact Complex.I_ne_zero hc

/-- DLMF4.38.15 with compatible subtraction branches. The paired cosh equation fixes
parity without excluding parameters, including the critical values ±i. -/
@[dlmf 4.38.E15]
theorem arcsinh_values_sub (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a-b) (arcsinhValues u) (arcsinhValues v)=
      {w | ∃ r s : ℂ,r^2=1+v^2 ∧ s^2=1+u^2 ∧
        w∈arcsinhValues (u*r-v*s) ∧ Complex.cosh w=s*r-u*v} := by
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change Complex.sinh a=u at ha
    change Complex.sinh b=v at hb
    refine ⟨Complex.cosh b,Complex.cosh a,?_,?_,?_,?_⟩
    · rw [Complex.cosh_sq,hb];ring
    · rw [Complex.cosh_sq,ha];ring
    · change Complex.sinh (a-b)=u*Complex.cosh b-v*Complex.cosh a
      rw [Complex.sinh_sub,ha,hb]
      ring
    · rw [Complex.cosh_sub,ha,hb] <;> ring
  · rintro ⟨r,s,hr,hs,hw,hc⟩
    have ha:=hyper_sinh_cosh_log_lift u s hs
    let a:=Complex.log (s+u)
    refine ⟨a,ha.1,a-w,?_,by ring⟩
    change Complex.sinh (a-w)=v
    change Complex.sinh w=u*r-v*s at hw
    rw [Complex.sinh_sub,ha.1,ha.2,hw,hc]
    linear_combination v*hs


/-- arccosh values sub. -/
@[dlmf 4.38.E16]
theorem arccosh_values_sub (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a-b) (arccoshValues u) (arccoshValues v)=
      {w | ∃ r : ℂ, r^2=(u^2-1)*(v^2-1) ∧ w ∈ arccoshValues (u*v-r)} := by
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change Complex.cosh a=u at ha
    change Complex.cosh b=v at hb
    refine ⟨Complex.sinh a*Complex.sinh b,?_,?_⟩
    · simp only [mul_pow,neg_sq,Complex.sinh_sq,ha,hb]
    · change Complex.cosh (a-b)=u*v-Complex.sinh a*Complex.sinh b
      rw [Complex.cosh_sub,ha,hb]
  · rintro ⟨r,hr,hc⟩
    change Complex.cosh w=u*v-r at hc
    have hs:(v-u*Complex.cosh w)^2=(Complex.sinh w*Complex.sinh (arccosh u))^2 := by
      simp only [mul_pow,Complex.sinh_sq,hyper_cosh_arccosh,hc]
      linear_combination hr
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs|hs
    · refine ⟨-arccosh u,?_, -w-arccosh u,?_,by ring⟩
      · change Complex.cosh (-arccosh u)=u
        rw [Complex.cosh_neg,hyper_cosh_arccosh]
      · change Complex.cosh (-w-arccosh u)=v
        rw [show -w-arccosh u= -(w+arccosh u) by ring,Complex.cosh_neg,
          Complex.cosh_add,hyper_cosh_arccosh]
        linear_combination -hs
    · refine ⟨arccosh u,hyper_cosh_arccosh u,arccosh u-w,?_,by ring⟩
      change Complex.cosh (arccosh u-w)=v
      rw [Complex.cosh_sub,hyper_cosh_arccosh]
      linear_combination -hs


/-- arctanh values sub. -/
@[dlmf 4.38.E17]
theorem arctanh_values_sub {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1) (hp : 1-u*v≠0) :
    Set.image2 (fun a b : ℂ => a-b) (arctanhValues u) (arctanhValues v)=arctanhValues ((u-v)/(1-u*v)) := by
  have hu1 : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu.1)
  have hu2 : 1+u ≠ 0 := fun h => hu.2 (by first | linear_combination h | linear_combination -h)
  have hv1 : 1-v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv.1)
  have hv2 : 1+v ≠ 0 := fun h => hv.2 (by first | linear_combination h | linear_combination -h)
  have ht1 : (u-v)/(1-u*v) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hp]; intro h
    exact mul_ne_zero hu1 hv2 (by first | linear_combination h | linear_combination -h)
  have ht2 : (u-v)/(1-u*v) ≠ -1 := by
    rw [Ne, div_eq_iff hp]; intro h
    exact mul_ne_zero hu2 hv1 (by first | linear_combination h | linear_combination -h)
  have ht3 : 1-(u-v)/(1-u*v) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have e0 : arctanhValues (u) = {w : ℂ | Complex.exp (2*w)*(1-(u)) = 1+(u)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hu.1 hu.2
  have e1 : arctanhValues (v) = {w : ℂ | Complex.exp (2*w)*(1-(v)) = 1+(v)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hv.1 hv.2
  have e2 : arctanhValues ((u-v)/(1-u*v)) = {w : ℂ | Complex.exp (2*w)*(1-((u-v)/(1-u*v))) = 1+((u-v)/(1-u*v))} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff ht1 ht2
  rw [e0, e1, e2, hypR4_expSet_sub hu1 hu2]
  apply hypR4_expSet_congr (mul_ne_zero hu1 hv2) ht3
  field_simp
  ring

/-- DLMF4.38.18 interpreted with shared inverse branches. Both inverse descriptions
retain the paired sinh/cosh equations, including all critical parameter values. -/
@[dlmf 4.38.E18]
theorem arcsinh_arccosh_values_sub (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a - b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
        w∈arcsinhValues (u*v - r*s) ∧ Complex.cosh w=v*r - u*s} ∧
    Set.image2 (fun a b : ℂ => a - b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
        w∈arccoshValues (v*r - u*s) ∧ Complex.sinh w=u*v - r*s} := by
  have hfirst :
      Set.image2 (fun a b : ℂ => a - b) (arcsinhValues u) (arccoshValues v)=
        {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
          w∈arcsinhValues (u*v - r*s) ∧ Complex.cosh w=v*r - u*s} := by
    simpa only [one_mul,neg_one_mul,sub_eq_add_neg,arcsinhValues,Set.mem_setOf_eq] using
      hyper_mixed_inverse_fiber u v (-1) (Or.inr rfl)
  refine ⟨hfirst,?_⟩
  rw [hfirst]
  ext w
  constructor
  · rintro ⟨r,s,hr,hs,hw,hc⟩
    exact ⟨r,s,hr,hs,hc,hw⟩
  · rintro ⟨r,s,hr,hs,hc,hw⟩
    exact ⟨r,s,hr,hs,hw,hc⟩

/-- arctanh arccoth values sub. -/
@[dlmf 4.38.E19]
theorem arctanh_arccoth_values_sub {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1)
    (hp : v-u≠0) (hq : u*v-1≠0) :
    Set.image2 (fun a b : ℂ => a-b) (arctanhValues u) (arccothValues v)=arctanhValues ((u*v-1)/(v-u)) ∧
    Set.image2 (fun a b : ℂ => a-b) (arctanhValues u) (arccothValues v)=arccothValues ((v-u)/(u*v-1)) := by
  have hu1 : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu.1)
  have hu2 : 1+u ≠ 0 := fun h => hu.2 (by first | linear_combination h | linear_combination -h)
  have hv1 : v-1 ≠ 0 := sub_ne_zero.mpr hv.1
  have hv2 : v+1 ≠ 0 := fun h => hv.2 (by first | linear_combination h | linear_combination -h)
  have ht1 : (u*v-1)/(v-u) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hp]; intro h
    exact mul_ne_zero hu1 hv2 (by first | linear_combination h | linear_combination -h)
  have ht2 : (u*v-1)/(v-u) ≠ -1 := by
    rw [Ne, div_eq_iff hp]; intro h
    exact mul_ne_zero hu2 hv1 (by first | linear_combination h | linear_combination -h)
  have hs1 : (v-u)/(u*v-1) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hq]; intro h
    exact mul_ne_zero hu1 hv2 (by first | linear_combination h | linear_combination -h)
  have hs2 : (v-u)/(u*v-1) ≠ -1 := by
    rw [Ne, div_eq_iff hq]; intro h
    exact mul_ne_zero hu2 hv1 (by first | linear_combination h | linear_combination -h)
  have ht3 : 1-(u*v-1)/(v-u) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hs3 : (v-u)/(u*v-1)-1 ≠ 0 := sub_ne_zero.mpr hs1
  have e0 : arctanhValues (u) = {w : ℂ | Complex.exp (2*w)*(1-(u)) = 1+(u)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hu.1 hu.2
  have e1 : arccothValues (v) = {w : ℂ | Complex.exp (2*w)*((v)-1) = (v)+1} :=
    Set.ext fun w => hypR4_mem_arccothValues_iff hv.1 hv.2
  have e2 : arctanhValues ((u*v-1)/(v-u)) = {w : ℂ | Complex.exp (2*w)*(1-((u*v-1)/(v-u))) = 1+((u*v-1)/(v-u))} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff ht1 ht2
  have e3 : arccothValues ((v-u)/(u*v-1)) = {w : ℂ | Complex.exp (2*w)*(((v-u)/(u*v-1))-1) = ((v-u)/(u*v-1))+1} :=
    Set.ext fun w => hypR4_mem_arccothValues_iff hs1 hs2
  rw [e0, e1, e2, e3, hypR4_expSet_sub hu1 hu2]
  constructor
  · apply hypR4_expSet_congr (mul_ne_zero hu1 hv2) ht3
    field_simp
    ring
  · apply hypR4_expSet_congr (mul_ne_zero hu1 hv2) hs3
    field_simp
    ring

/-- tanh continued fraction. -/
@[dlmf 4.39.E1]
theorem tanh_continued_fraction {z : ℂ} (hz : Complex.cosh z≠0) :
    DLMF.HasContinuedFraction (fun n => if n=0 then z else z^2) (fun n => (2*n+1:ℂ)) (Complex.tanh z) := by
  sorry

/-- arcsinh continued fraction. -/
@[dlmf 4.39.E2]
theorem arcsinh_continued_fraction {z : ℂ} (hz : z∈arcsinhDomain) :
    DLMF.HasContinuedFraction
      (fun n => if n=0 then z else ((2*((n+1)/2)-1:ℕ):ℂ)*(2*((n+1)/2):ℂ)*z^2)
      (fun n => (2*n+1:ℂ)) (arcsinh z/Complex.sqrt (1+z^2)) := by
  sorry

/-- arctanh continued fraction. -/
@[dlmf 4.39.E3]
theorem arctanh_continued_fraction {z : ℂ} (hz : z∈arctanhDomain) :
    DLMF.HasContinuedFraction (fun n => if n=0 then z else -(n:ℂ)^2*z^2)
      (fun n => (2*n+1:ℂ)) (arctanh z) := by
  sorry

/-- antiderivative tanh. -/
@[dlmf 4.40.E3]
theorem antiderivative_tanh (x : ℝ) : HasDerivAt (fun t : ℝ => Real.log (Real.cosh t)) (Real.tanh x) x := by
  simpa only [Real.tanh_eq_sinh_div_cosh] using (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'


/-- antiderivative csch. -/
@[dlmf 4.40.E4]
theorem antiderivative_csch {x : ℝ} (hx : 0<x) : HasDerivAt (fun t : ℝ => Real.log (Real.tanh (t/2))) (Real.sinh x)⁻¹ x := by
  have hs : 0 < Real.sinh (x/2) := Real.sinh_pos_iff.mpr (by linarith)
  have hc : 0 < Real.cosh (x/2) := Real.cosh_pos _
  have hf : (fun t : ℝ => Real.log (Real.tanh (t/2))) =
      fun t => Real.log (Real.sinh (t/2)/Real.cosh (t/2)) := by
    funext t; rw [Real.tanh_eq_sinh_div_cosh]
  rw [hf]
  have h1 := ((hasDerivAt_id x).div_const 2).sinh
  have h2 := ((hasDerivAt_id x).div_const 2).cosh
  have hd := (h1.div h2 hc.ne').log (div_pos hs hc).ne'
  convert hd using 1
  · rfl
  · dsimp only [id, Pi.div_apply]
    have h2x : Real.sinh x = 2*Real.sinh (x/2)*Real.cosh (x/2) := by
      rw [← Real.sinh_two_mul]; ring_nf
    rw [h2x]
    field_simp
    nlinarith [Real.cosh_sq (x/2)]

/-- antiderivative sech. -/
@[dlmf 4.40.E5]
theorem antiderivative_sech (x : ℝ) : HasDerivAt (fun t : ℝ => 2*Real.arctan (Real.exp t)-π/2) (Real.cosh x)⁻¹ x := by
  have hd:=((Real.hasDerivAt_exp x).arctan.const_mul 2).sub_const (π/2)
  convert hd using 1
  rw [Real.cosh_eq,Real.exp_neg]
  field_simp <;> ring


/-- antiderivative coth. -/
@[dlmf 4.40.E6]
theorem antiderivative_coth {x : ℝ} (hx : 0<x) : HasDerivAt (fun t : ℝ => Real.log (Real.sinh t)) (Real.cosh x/Real.sinh x) x := by
  exact (Real.hasDerivAt_sinh x).log (Real.sinh_pos_iff.mpr hx).ne'


/-- integral exp sin div sinh. -/
@[dlmf 4.40.E7]
theorem integral_exp_sin_div_sinh {a : ℝ} (ha : a≠0) : IntegrableOn (fun x : ℝ => Real.exp (-x)*Real.sin (a*x)/Real.sinh x) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, Real.exp (-x)*Real.sin (a*x)/Real.sinh x)=π/2*(Real.cosh (π*a/2)/Real.sinh (π*a/2))-1/a := by
  sorry

/-- integral sinh div sinh. -/
@[dlmf 4.40.E8]
theorem integral_sinh_div_sinh {a : ℝ} (ha : -π<a ∧ a<π) : IntegrableOn (fun x : ℝ => Real.sinh (a*x)/Real.sinh (π*x)) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, Real.sinh (a*x)/Real.sinh (π*x))=Real.tan (a/2)/2 := by
  sorry

/-- integral exp div cosh sq. -/
@[dlmf 4.40.E9]
theorem integral_exp_div_cosh_sq {a : ℝ} (ha : -1<a ∧ a<1) : Integrable (fun x : ℝ => Real.exp (a*x)/(Real.cosh (x/2))^2) ∧ (∫ x : ℝ, Real.exp (a*x)/(Real.cosh (x/2))^2)=(if a=0 then 4 else 4*π*a/Real.sin (π*a)) := by
  sorry

/-- integral tanh difference. -/
@[dlmf 4.40.E10]
theorem integral_tanh_difference {a b : ℝ} (ha : 0<a) (hb : 0<b) : IntegrableOn (fun x : ℝ => (Real.tanh (a*x)-Real.tanh (b*x))/x) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, (Real.tanh (a*x)-Real.tanh (b*x))/x)=Real.log (a/b) := by
  sorry

/-- antiderivative arcsinh. -/
@[dlmf 4.40.E11]
theorem antiderivative_arcsinh (x : ℝ) : HasDerivAt (fun t : ℝ => t*Real.arsinh t-Real.sqrt (1+t^2)) (Real.arsinh x) x := by
  have hp:0<1+x^2 := by positivity
  have hd:=((hasDerivAt_id x).mul (Real.hasDerivAt_arsinh x)).sub
    ((((hasDerivAt_id x).pow 2).const_add 1).sqrt hp.ne')
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
    field_simp
    ring


/-- antiderivative arccosh. -/
@[dlmf 4.40.E12]
theorem antiderivative_arccosh {x : ℝ} (hx : 1<x) : HasDerivAt (fun t : ℝ => t*Real.arcosh t-Real.sqrt (t^2-1)) (Real.arcosh x) x := by
  have hp:0<x^2-1 := by nlinarith
  have hd:=((hasDerivAt_id x).mul (Real.hasDerivAt_arcosh hx)).sub
    ((((hasDerivAt_id x).pow 2).sub_const 1).sqrt hp.ne')
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
    field_simp
    ring


/-- antiderivative arctanh. -/
@[dlmf 4.40.E13]
theorem antiderivative_arctanh {x : ℝ} (hx : |x|<1) : HasDerivAt (fun t : ℝ => t*Real.artanh t+Real.log (1-t^2)/2) (Real.artanh x) x := by
  have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨(abs_lt.mp hx).1, (abs_lt.mp hx).2⟩
  have hp : 0 < 1-x^2 := by nlinarith [(abs_lt.mp hx).1, (abs_lt.mp hx).2]
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_artanh hx')).add
    ((((hasDerivAt_id x).pow 2).const_sub 1).log hp.ne' |>.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id, Pi.pow_apply]
    field_simp
    ring

/-- antiderivative arccsch. -/
@[dlmf 4.40.E14]
theorem antiderivative_arccsch {x : ℝ} (hx : 0<x) : HasDerivAt (fun t : ℝ => t*Real.arsinh t⁻¹+Real.arsinh t) (Real.arsinh x⁻¹) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have hd := ((hasDerivAt_id x).mul ((hasDerivAt_inv hx.ne').arsinh)).add (Real.hasDerivAt_arsinh x)
  convert hd using 1
  · rfl
  · dsimp only [id]
    have hq : Real.sqrt (1+(x⁻¹)^2) = Real.sqrt (1+x^2)/x := by
      rw [show 1+(x⁻¹)^2 = (1+x^2)/x^2 by field_simp; ring, Real.sqrt_div (by positivity),
        Real.sqrt_sq hx.le]
    rw [hq, smul_eq_mul]
    have : 0 < Real.sqrt (1+x^2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
    ring

/-- antiderivative arcsech. -/
@[dlmf 4.40.E15]
theorem antiderivative_arcsech {x : ℝ} (hx : 0<x ∧ x<1) : HasDerivAt (fun t : ℝ => t*Real.arcosh t⁻¹+Real.arcsin t) (Real.arcosh x⁻¹) x := by
  obtain ⟨h0,h1⟩ := hx
  have hx0 : x ≠ 0 := h0.ne'
  have hi : x⁻¹ ∈ Ioi (1:ℝ) := by
    show 1 < x⁻¹
    exact one_lt_inv₀ h0 |>.mpr h1
  have hd := ((hasDerivAt_id x).mul ((Real.hasDerivAt_arcosh hi).comp x (hasDerivAt_inv h0.ne'))).add
    (Real.hasDerivAt_arcsin (by linarith) (by linarith : x ≠ 1))
  convert hd using 1
  · rfl
  · dsimp only [id, Function.comp]
    have hq : Real.sqrt ((x⁻¹)^2-1) = Real.sqrt (1-x^2)/x := by
      rw [show (x⁻¹)^2-1 = (1-x^2)/x^2 by field_simp, Real.sqrt_div (by nlinarith),
        Real.sqrt_sq h0.le]
    rw [hq]
    have : 0 < Real.sqrt (1-x^2) := Real.sqrt_pos.mpr (by nlinarith)
    field_simp
    ring

/-- antiderivative arccoth. -/
@[dlmf 4.40.E16]
theorem antiderivative_arccoth {x : ℝ} (hx : 1<x) : HasDerivAt (fun t : ℝ => t*Real.artanh t⁻¹+Real.log (t^2-1)/2) (Real.artanh x⁻¹) x := by
  have hi : x⁻¹ ∈ Ioo (-1:ℝ) 1 := ⟨by have := inv_pos.mpr (by linarith : (0:ℝ)<x); linarith,
    inv_lt_one_of_one_lt₀ hx⟩
  have hp : 0 < x^2-1 := by nlinarith
  have hd := ((hasDerivAt_id x).mul ((Real.hasDerivAt_artanh hi).comp x
    (hasDerivAt_inv (by linarith : x ≠ 0)))).add
    ((((hasDerivAt_id x).pow 2).sub_const 1).log hp.ne' |>.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id, Function.comp, Pi.pow_apply]
    have hx0 : x ≠ 0 := by linarith
    have : 1-(x⁻¹)^2 = (x^2-1)/x^2 := by field_simp
    rw [this]
    field_simp
    ring

/-- Two functions that agree on an open neighbourhood have the same derivative there. -/
private lemma hypR4_deriv_eq {f g : ℂ → ℂ} {f' g' z : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hz : z ∈ U) (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) (h : ∀ w ∈ U, f w = g w) :
    f' = g' :=
  hf.unique (hg.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h))

/-- Local logarithmic branches give complex primitives without imposing principal-log cuts. -/
theorem complex_antiderivatives_hyperbolic {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hz : z∈U) (hc : Complex.cosh z≠0) (hs : Complex.sinh z≠0)
    {Lcosh Lsinh Ltanh : ℂ → ℂ}
    (hLc : AnalyticOnNhd ℂ Lcosh U) (hLs : AnalyticOnNhd ℂ Lsinh U)
    (hLt : AnalyticOnNhd ℂ Ltanh U)
    (hEc : ∀ w∈U, Complex.exp (Lcosh w)=Complex.cosh w)
    (hEs : ∀ w∈U, Complex.exp (Lsinh w)=Complex.sinh w)
    (hEt : ∀ w∈U, Complex.exp (Ltanh w)=Complex.tanh (w/2)) :
    HasDerivAt Lcosh (Complex.tanh z) z ∧ HasDerivAt Lsinh (coth z) z ∧
      HasDerivAt Ltanh (csch z) z := by
  have dc := (hLc z hz).differentiableAt.hasDerivAt
  have ds := (hLs z hz).differentiableAt.hasDerivAt
  have dt := (hLt z hz).differentiableAt.hasDerivAt
  have ec := hypR4_deriv_eq hU hz dc.cexp (Complex.hasDerivAt_cosh z) hEc
  have es := hypR4_deriv_eq hU hz ds.cexp (Complex.hasDerivAt_sinh z) hEs
  have h2 : Complex.sinh z = 2*Complex.sinh (z/2)*Complex.cosh (z/2) := by
    rw [← Complex.sinh_two_mul]; ring_nf
  have hc2 : Complex.cosh (z/2) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  have hs2 : Complex.sinh (z/2) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  have dth : HasDerivAt (fun w => Complex.tanh (w/2)) (sech (z/2)^2*(1/2)) z := by
    have := (hasDerivAt_tanh hc2).comp z ((hasDerivAt_id z).div_const 2)
    simpa [Function.comp_def] using this
  have et := hypR4_deriv_eq hU hz dt.cexp dth hEt
  rw [hEc z hz] at ec
  rw [hEs z hz] at es
  rw [hEt z hz] at et
  refine ⟨?_, ?_, ?_⟩
  · convert dc using 1
    rw [Complex.tanh_eq_sinh_div_cosh, div_eq_iff hc]; linear_combination -ec
  · convert ds using 1
    rw [coth, div_eq_iff hs]; linear_combination -es
  · convert dt using 1
    have ht0 : Complex.tanh (z/2) ≠ 0 := by
      rw [Complex.tanh_eq_sinh_div_cosh]; exact div_ne_zero hs2 hc2
    have hd : deriv Ltanh z = sech (z/2)^2*(1/2)/Complex.tanh (z/2) := by
      rw [eq_div_iff ht0]; linear_combination et
    rw [hd, csch, h2, sech, Complex.tanh_eq_sinh_div_cosh]
    field_simp

/-- The principal complex arcsinh primitive on its complete open cut domain. -/
theorem complex_antiderivative_arcsinh {z : ℂ} (hz : z∈arcsinhDomain) :
    HasDerivAt (fun w => w*arcsinh w-Complex.sqrt (1+w^2)) (arcsinh z) z := by
  have hq : 1+z^2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    rcases hz with hr | hi
    · by_cases hy : z.im = 0
      · left; simp [pow_two, Complex.mul_re, hy]; nlinarith [sq_nonneg z.re]
      · right; simp [pow_two, Complex.mul_im]
        intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hr) hy; linear_combination h
    · left
      simp [pow_two, Complex.mul_re]
      nlinarith [abs_lt.mp hi, sq_nonneg z.re]
  have hr : Complex.sqrt (1+z^2) ≠ 0 := by
    intro h
    have hs := trig_sqrt_sq (1+z^2)
    rw [h, zero_pow two_ne_zero] at hs
    exact Complex.slitPlane_ne_zero hq hs.symm
  have hp : HasDerivAt (fun w : ℂ => 1+w^2) (2*z) z := by
    simpa using (hasDerivAt_pow 2 z).const_add 1
  have dS := (Complex.hasDerivAt_sqrt hq).comp z hp
  have hv : (1+z^2)^(-1/2:ℂ) = (Complex.sqrt (1+z^2))⁻¹ := by
    rw [Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹) by norm_num, Complex.cpow_neg]
  have hd := ((hasDerivAt_id z).mul (hyper_hasDerivAt_arcsinh hz)).sub dS
  rw [hv] at hd
  convert hd using 1
  · funext w; simp [Function.comp_def]
  · simp only [id_eq]
    field_simp
    ring

/-- The principal complex arccosh primitive on its complete open cut domain. -/
theorem complex_antiderivative_arccosh {z : ℂ} (hz : z∈arccoshDomain) :
    HasDerivAt (fun w => w*arccosh w-Complex.sqrt (w-1)*Complex.sqrt (w+1)) (arccosh z) z := by
  obtain ⟨h1, h2⟩ := hypR4_acosh_slit hz
  have hs := hypR4_acosh_root_ne hz
  have hA : Complex.sqrt (z-1) ≠ 0 := fun h => hs (by rw [h, zero_mul])
  have hB : Complex.sqrt (z+1) ≠ 0 := fun h => hs (by rw [h, mul_zero])
  have dA : HasDerivAt (fun w => Complex.sqrt (w-1)) ((Complex.sqrt (z-1))⁻¹/2) z := by
    have := (Complex.hasDerivAt_sqrt h1).comp z ((hasDerivAt_id z).sub_const 1)
    simpa only [Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹:ℂ) by norm_num, Complex.cpow_neg, mul_one,
      Function.comp_def, id] using this
  have dB : HasDerivAt (fun w => Complex.sqrt (w+1)) ((Complex.sqrt (z+1))⁻¹/2) z := by
    have := (Complex.hasDerivAt_sqrt h2).comp z ((hasDerivAt_id z).add_const 1)
    simpa only [Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹:ℂ) by norm_num, Complex.cpow_neg, mul_one,
      Function.comp_def, id] using this
  have hd := ((hasDerivAt_id z).mul (hypR4_hasDerivAt_arccosh hz)).sub (dA.mul dB)
  convert hd using 1
  · rfl
  have eA := trig_sqrt_sq (z-1)
  have eB := trig_sqrt_sq (z+1)
  simp only [id_eq]
  generalize Complex.sqrt (z-1) = A at *
  generalize Complex.sqrt (z+1) = B at *
  field_simp
  linear_combination eA + eB

/-- The principal complex arctanh primitive on its complete open cut domain. -/
theorem complex_antiderivative_arctanh {z : ℂ} (hz : z∈arctanhDomain) :
    HasDerivAt (fun w => w*arctanh w+Complex.log (1-w^2)/2) (arctanh z) z := by
  have hq : 1-z^2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    rcases hz with hi | hr
    · by_cases hx : z.re = 0
      · left; simp [pow_two, Complex.mul_re, hx]; nlinarith [sq_nonneg z.im]
      · right; simp [pow_two, Complex.mul_im]
        intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hx) hi; linear_combination -h
    · left
      simp [pow_two, Complex.mul_re]
      nlinarith [abs_lt.mp hr, sq_nonneg z.im]
  have hq0 : 1-z^2 ≠ 0 := Complex.slitPlane_ne_zero hq
  have dL := ((Complex.hasDerivAt_log hq).comp z (((hasDerivAt_id z).pow 2).const_sub 1)).div_const 2
  have hd := ((hasDerivAt_id z).mul (hyper_hasDerivAt_arctanh hz)).add dL
  convert hd using 1
  · funext w; simp [Function.comp_def]
  · simp only [id_eq, Pi.pow_apply]
    field_simp
    ring

/-- The remaining inverse functions are real on their uncut real intervals. -/
theorem reciprocal_inverses_ofReal {x : ℝ} :
    (x≠0 → arccsch x=(Real.arsinh x⁻¹:ℂ)) ∧
    (0<x ∧ x≤1 → arcsech x=(Real.arcosh x⁻¹:ℂ)) ∧
    (1< |x| → arccoth x=(Real.artanh x⁻¹:ℂ)) := by
  refine ⟨fun _ => ?_, fun hx => ?_, fun hx => ?_⟩
  · rw [arccsch, ← Complex.ofReal_inv, arcsinh_ofReal]
  · have h1 : 1 ≤ x⁻¹ := one_le_inv₀ hx.1 |>.mpr hx.2
    rw [arcsech, ← Complex.ofReal_inv, arccosh_ofReal _ h1]
  · have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
    have h1 : |x⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hx
    rw [arccoth_eq_inv (by exact_mod_cast hx0), ← Complex.ofReal_inv, arctanh_ofReal _ h1]

/-- A nonvanishing holomorphic function on a disc about the origin, equal to `1` at the origin,
has a holomorphic logarithm vanishing at the origin. -/
private lemma hypR4_exists_log_ball {r : ℝ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r)) (hne : ∀ z ∈ Metric.ball (0:ℂ) r, g z ≠ 0)
    (h0 : g 0 = 1) (hr : 0 < r) : ∃ L, HyperbolicNormalizedLog (Metric.ball 0 r) g L := by
  have hB : IsOpen (Metric.ball (0:ℂ) r) := Metric.isOpen_ball
  have h0B : (0:ℂ) ∈ Metric.ball (0:ℂ) r := Metric.mem_ball_self hr
  have hd : DifferentiableOn ℂ (fun z => deriv g z / g z) (Metric.ball 0 r) :=
    (hg.deriv hB).div hg hne
  obtain ⟨P, hP0, hP⟩ := hd.isExactOn_ball.with_val_at 0 0
  have hPd : DifferentiableOn ℂ P (Metric.ball 0 r) :=
    fun z hz => (hP z hz).differentiableAt.differentiableWithinAt
  have hQd : ∀ z ∈ Metric.ball (0:ℂ) r,
      HasDerivAt (fun w => g w * Complex.exp (-P w)) 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z :=
      (hg.differentiableAt (hB.mem_nhds hz)).hasDerivAt
    have := hgz.mul ((hP z hz).neg.cexp)
    convert this using 1
    field_simp [hne z hz]
    ring
  have hQc : Set.EqOn (fun w => g w * Complex.exp (-P w)) (fun _ => (1:ℂ)) (Metric.ball 0 r) := by
    refine hB.eqOn_of_deriv_eq (convex_ball (0:ℂ) r).isPreconnected
      (fun z hz => (hQd z hz).differentiableAt.differentiableWithinAt)
      (differentiableOn_const 1) (fun z hz => ?_) h0B (by simp [h0, hP0])
    simp only [(hQd z hz).deriv, deriv_const]
  refine ⟨P, hPd.analyticOnNhd hB, hP0, fun z hz => ?_⟩
  have h := hQc hz
  simp only at h
  have he : Complex.exp (-P z) * Complex.exp (P z) = 1 := by rw [← Complex.exp_add]; simp
  linear_combination -(Complex.exp (P z))*h + g z*he

/-- `sinh` has no zeros other than the origin in the open disc of radius `π`. -/
private lemma hypR4_sinh_ne_zero_ball {z : ℂ} (hz : ‖z‖ < π) (hz0 : z ≠ 0) :
    Complex.sinh z ≠ 0 := by
  intro h
  have hs : Complex.sin (z*I) = 0 := by rw [Complex.sin_mul_I, h, zero_mul]
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
  have hn : ‖z‖ = |(k:ℝ)| * π := by
    have := congrArg norm hk
    rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_intCast, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le] at this
    exact this
  rcases eq_or_ne k 0 with rfl | hk0
  · simp at hk; exact hz0 hk
  · have : (1:ℝ) ≤ |(k:ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    nlinarith [Real.pi_pos]

/-- `cosh` has no zeros in the open disc of radius `π/2`. -/
private lemma hypR4_cosh_ne_zero_ball {z : ℂ} (hz : ‖z‖ < π/2) : Complex.cosh z ≠ 0 := by
  intro h
  have hs : Complex.cos (z*I) = 0 := by rw [Complex.cos_mul_I, h]
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hs
  have hn : ‖z‖ = |2*(k:ℝ)+1| * π / 2 := by
    have := congrArg norm hk
    rw [norm_mul, Complex.norm_I, mul_one, norm_div, norm_mul,
      show (2*(k:ℂ)+1) = ((2*(k:ℝ)+1:ℝ):ℂ) by push_cast; ring, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] at this
    simpa using this
  have : (1:ℝ) ≤ |2*(k:ℝ)+1| := by
    rcases le_or_gt 0 k with hk0 | hk0
    · rw [abs_of_nonneg (by positivity)]
      have : (0:ℝ) ≤ k := by exact_mod_cast hk0
      linarith
    · have : (k:ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk0
      rw [abs_of_neg (by linarith)]; linarith
  nlinarith [Real.pi_pos]

/-- Existence of the three normalized analytic logarithms used in the prose series. -/
theorem exists_hyperbolic_logarithms :
    (∃ L, HyperbolicNormalizedLog (Metric.ball 0 π) sinhc L) ∧
    (∃ L, HyperbolicNormalizedLog (Metric.ball 0 (π/2)) Complex.cosh L) ∧
    (∃ L, HyperbolicNormalizedLog (Metric.ball 0 (π/2)) tanhc L) := by
  have hπ := Real.pi_pos
  refine ⟨?_, ?_, ?_⟩
  · have he : sinhc = dslope Complex.sinh 0 := by
      funext z
      by_cases hz : z = 0
      · subst hz; simp [sinhc, dslope_same, Complex.deriv_sinh]
      · rw [dslope_of_ne _ hz, slope_def_field]; simp [sinhc, hz]
    refine hypR4_exists_log_ball ?_ (fun z hz => ?_) (by simp [sinhc]) hπ
    · rw [he, differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hπ))]
      exact Complex.differentiable_sinh.differentiableOn
    · have hz' : ‖z‖ < π := by simpa using hz
      by_cases hz0 : z = 0
      · simp [sinhc, hz0]
      · simp only [sinhc, hz0, ↓reduceIte]
        exact div_ne_zero (hypR4_sinh_ne_zero_ball hz' hz0) hz0
  · exact hypR4_exists_log_ball Complex.differentiable_cosh.differentiableOn
      (fun z hz => hypR4_cosh_ne_zero_ball (by simpa using hz)) (by simp) (by positivity)
  · have hc : ∀ z ∈ Metric.ball (0:ℂ) (π/2), Complex.cosh z ≠ 0 :=
      fun z hz => hypR4_cosh_ne_zero_ball (by simpa using hz)
    have hT : DifferentiableOn ℂ Complex.tanh (Metric.ball 0 (π/2)) := by
      intro z hz
      have : Complex.tanh = fun w => Complex.sinh w / Complex.cosh w := by
        funext w; exact Complex.tanh_eq_sinh_div_cosh w
      rw [this]
      exact (Complex.differentiable_sinh.differentiableAt.div
        Complex.differentiable_cosh.differentiableAt (hc z hz)).differentiableWithinAt
    have hd0 : deriv Complex.tanh 0 = 1 := by
      have hh : HasDerivAt (fun w => Complex.sinh w / Complex.cosh w)
          ((Complex.cosh 0*Complex.cosh 0 - Complex.sinh 0*Complex.sinh 0)/(Complex.cosh 0)^2) 0 :=
        (Complex.hasDerivAt_sinh 0).div (Complex.hasDerivAt_cosh 0) (by simp)
      have : Complex.tanh = fun w => Complex.sinh w / Complex.cosh w := by
        funext w; exact Complex.tanh_eq_sinh_div_cosh w
      rw [this, hh.deriv]; simp
    have he : tanhc = dslope Complex.tanh 0 := by
      funext z
      by_cases hz : z = 0
      · subst hz; simp [tanhc, dslope_same, hd0]
      · rw [dslope_of_ne _ hz, slope_def_field]; simp [tanhc, hz]
    refine hypR4_exists_log_ball ?_ (fun z hz => ?_) (by simp [tanhc]) (by positivity)
    · rw [he, differentiableOn_dslope (Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (by positivity)))]
      exact hT
    · have hz' : ‖z‖ < π/2 := by simpa using hz
      by_cases hz0 : z = 0
      · simp [tanhc, hz0]
      · simp only [tanhc, hz0, ↓reduceIte]
        rw [Complex.tanh_eq_sinh_div_cosh]
        exact div_ne_zero (div_ne_zero (hypR4_sinh_ne_zero_ball (by linarith) hz0) (hc z hz)) hz0

/-- `√(1-z²)+iz` never lies on the closed negative real axis. -/
private lemma hypR4_sqrt_add_I_mul_slit (z : ℂ) :
    Complex.sqrt (1-z^2)+I*z ∈ Complex.slitPlane := by
  set q := Complex.sqrt (1-z^2) with hq
  have hq2 : q^2 = 1-z^2 := trig_sqrt_sq _
  have hqre : 0 ≤ q.re := by
    rw [hq, Complex.sqrt, Complex.cpow_inv_two_re]; exact Real.sqrt_nonneg _
  rw [Complex.mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  obtain ⟨hre, him⟩ := hc
  set t := q+I*z with ht
  have hprod : t*(q-I*z) = 1 := by
    rw [ht]; linear_combination (by simp : (I:ℂ)^2 = -1) * (-z^2) + hq2
  have ht_real : t = (t.re:ℂ) := Complex.ext (by simp) (by simp [him])
  have ht0 : t ≠ 0 := by rintro h; rw [h, zero_mul] at hprod; exact zero_ne_one hprod
  have htre0 : t.re < 0 := lt_of_le_of_ne hre (fun h => ht0 (by rw [ht_real, h]; simp))
  have hsum : 2*q = t + t⁻¹ := by
    have : q - I*z = t⁻¹ := (eq_inv_of_mul_eq_one_right hprod)
    rw [← this, ht]; ring
  have : (2*q).re < 0 := by
    rw [hsum, ht_real, ← Complex.ofReal_inv, ← Complex.ofReal_add, Complex.ofReal_re]
    have : t.re⁻¹ < 0 := inv_lt_zero.mpr htre0
    linarith
  simp at this; linarith

/-- The complex extension of the reciprocal-inverse antiderivatives on compatible branches. -/
theorem complex_antiderivatives_reciprocal_inverse {z : ℂ}
    (hre : 0<z.re) (hs : z∈arccschDomain) (hc : z∈arcsechDomain)
    (ha : z.im≠0 ∨ |z.re|<1) :
    HasDerivAt (fun w => w*arccsch w+arcsinh w) (arccsch z) z ∧
    HasDerivAt (fun w => w*arcsech w-I*Complex.log (Complex.sqrt (1-w^2)+I*w))
      (arcsech z) z := by
  have hz0 : z ≠ 0 := hs.1
  have hzs : z ∈ arcsinhDomain := Or.inl hre.ne'
  constructor
  · have hd := ((hasDerivAt_id z).mul (hasDerivAt_arccsch_signed hs hre.ne')).add
      (hyper_hasDerivAt_arcsinh hzs)
    have hq : Complex.sqrt (1+z^2) ≠ 0 := by
      intro h
      have hsq := trig_sqrt_sq (1+z^2)
      rw [h, zero_pow two_ne_zero] at hsq
      have hzs' := hzs
      rcases hzs' with h1 | h1
      · have e : z^2 = -1 := by linear_combination -hsq
        have : z = I ∨ z = -I := by
          have : (z-I)*(z+I) = 0 := by
            linear_combination e - (by simp : (I:ℂ)^2 = -1)
          rcases mul_eq_zero.mp this with h | h
          · left; linear_combination h
          · right; linear_combination h
        rcases this with rfl | rfl <;> simp at h1
      · have e : z^2 = -1 := by linear_combination -hsq
        have : (z-I)*(z+I) = 0 := by
          linear_combination e - (by simp : (I:ℂ)^2 = -1)
        rcases mul_eq_zero.mp this with h | h
        · have : z = I := by linear_combination h
          subst this; simp at h1
        · have : z = -I := by linear_combination h
          subst this; simp at h1
    convert hd using 1
    · rfl
    simp only [hre, ↓reduceIte]
    simp only [id_eq]
    field_simp
    ring
  · have hsl := hypR4_asech_slit hc
    set q := Complex.sqrt (1-z^2) with hqdef
    have hq0 : q ≠ 0 := by
      intro h
      have hs2 := trig_sqrt_sq (1-z^2)
      rw [← hqdef, h, zero_pow two_ne_zero] at hs2
      exact Complex.slitPlane_ne_zero hsl hs2.symm
    have hp : HasDerivAt (fun w : ℂ => 1-w^2) (-(2*z)) z := by
      simpa using (hasDerivAt_pow 2 z).const_sub 1
    have dS := (Complex.hasDerivAt_sqrt hsl).comp z hp
    have hv : (1-z^2)^(-1/2:ℂ) = q⁻¹ := by
      rw [hqdef, Complex.sqrt, show (-1/2:ℂ) = -(2⁻¹) by norm_num, Complex.cpow_neg]
    rw [hv] at dS
    have hL := hypR4_sqrt_add_I_mul_slit z
    have hA : HasDerivAt (fun w : ℂ => Complex.sqrt (1-w^2)+I*w) (2⁻¹*q⁻¹*(-(2*z)) + I) z := by
      convert dS.add ((hasDerivAt_id z).const_mul I) using 1
      · funext w; simp [Function.comp_def]
      · ring
    have dL := (Complex.hasDerivAt_log hL).comp z hA
    have hd := ((hasDerivAt_id z).mul (hasDerivAt_arcsech hc)).sub (dL.const_mul I)
    have hne : q + I*z ≠ 0 := Complex.slitPlane_ne_zero hL
    have hI : (I:ℂ)^2 = -1 := by simp
    rw [← hqdef] at hd
    convert hd using 1
    · funext w; simp
    · simp only [id_eq]
      field_simp
      have hne' : q + z*I ≠ 0 := by rwa [mul_comm z I]
      rw [show I*(-z+q*I) = -(q+z*I) by linear_combination q*hI, neg_div, div_self hne']
      ring

/-- The complex inverse-cotangent primitive with a locally consistent logarithm. -/
theorem complex_antiderivative_arccoth {z : ℂ} (hz : z∈arccothDomain)
    (hlog : z^2-1∈slitPlane) :
    HasDerivAt (fun w => w*arccoth w+Complex.log (w^2-1)/2) (arccoth z) z := by
  have hq0 : z^2-1 ≠ 0 := Complex.slitPlane_ne_zero hlog
  have h1 : 1-z^2 ≠ 0 := fun h => hq0 (by linear_combination -h)
  have dL := ((Complex.hasDerivAt_log hlog).comp z (((hasDerivAt_id z).pow 2).sub_const 1)).div_const 2
  have hd := ((hasDerivAt_id z).mul (hasDerivAt_arccoth hz)).add dL
  convert hd using 1
  · funext w; simp [Function.comp_def]
  · simp only [id_eq, Pi.pow_apply]
    field_simp
    ring

/-- One-sided imaginary pole directions in the exact-value table, without an assigned infinite complex value. -/
@[dlmf 4.31.T1]
theorem hyperbolic_table_imaginary_pole_sides :
    Tendsto (fun y : ℝ => (Complex.tanh (I*y)).im) (𝓝[<] (π/2)) atTop ∧
    Tendsto (fun y : ℝ => (Complex.tanh (I*y)).im) (𝓝[>] (3*π/2)) atBot ∧
    Tendsto (fun y : ℝ => (sech (I*y)).re) (𝓝[<] (π/2)) atTop ∧
    Tendsto (fun y : ℝ => (sech (I*y)).re) (𝓝[>] (3*π/2)) atTop := by
  have ht : ∀ y : ℝ, (Complex.tanh (I*y)).im = Real.tan y := fun y => by
    rw [mul_comm, Complex.tanh_mul_I, Complex.mul_I_im, ← Complex.ofReal_tan, Complex.ofReal_re]
  have hs : ∀ y : ℝ, (sech (I*y)).re = (Real.cos y)⁻¹ := fun y => by
    rw [sech, mul_comm, Complex.cosh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_inv,
      Complex.ofReal_re]
  have hcos1 : Tendsto Real.cos (𝓝[<] (π/2)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := Real.continuous_cos.continuousAt (x := π/2) |>.tendsto
      rw [Real.cos_pi_div_two] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : -(π/2) < π/2)] with y hy
      exact Real.cos_pos_of_mem_Ioo hy
  have hcos2 : Tendsto Real.cos (𝓝[>] (3*π/2)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := Real.continuous_cos.continuousAt (x := 3*π/2) |>.tendsto
      have e : Real.cos (3*π/2) = 0 := by
        rw [show 3*π/2 = π/2+π by ring, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
      rw [e] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : 3*π/2 < 5*π/2)] with y hy
      rw [← Real.cos_sub_two_pi]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hshift : Tendsto (fun y : ℝ => y - 2*π) (𝓝[>] (3*π/2)) (𝓝[>] (-(π/2))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun y : ℝ => y - 2*π) (𝓝 (3*π/2)) (𝓝 (3*π/2 - 2*π)) :=
        tendsto_id.sub tendsto_const_nhds
      rw [show 3*π/2 - 2*π = -(π/2) by ring] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      show -(π/2) < y - 2*π
      have : 3*π/2 < y := hy
      linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ht]; exact Real.tendsto_tan_pi_div_two
  · simp only [ht]
    refine (Real.tendsto_tan_neg_pi_div_two.comp hshift).congr (fun y => ?_)
    simp only [Function.comp]
    rw [show y - 2*π = (y-π)-π by ring, Real.tan_periodic.sub_eq, Real.tan_periodic.sub_eq]
  · simp only [hs]; exact tendsto_inv_nhdsGT_zero.comp hcos1
  · simp only [hs]; exact tendsto_inv_nhdsGT_zero.comp hcos2

/-- A local continued Gudermannian, extending the sech antiderivative to the complex plane. -/
theorem complex_antiderivative_sech {z : ℂ} (hz : Complex.cosh z≠0) :
    ∃ U : Set ℂ, IsOpen U ∧ z∈U ∧ ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G U ∧
      (∀ w∈U, HasDerivAt G (sech w) w) ∧
      (∀ w∈U, Complex.tan (G w/2+π/4)=Complex.exp w) := by
  have hI : (I:ℂ)^2 = -1 := by simp
  have h2cosh : ∀ w : ℂ, 2*Complex.cosh w*Complex.exp w = Complex.exp w^2+1 := by
    intro w
    have h1 := Complex.cosh_add_sinh w
    have h2 := Complex.cosh_sub_sinh w
    have h3 : Complex.exp (-w)*Complex.exp w = 1 := by rw [← Complex.exp_add]; simp
    linear_combination (Complex.exp w)*h1 + (Complex.exp w)*h2 + h3
  have hfac : ∀ w : ℂ, Complex.exp w^2+1 = (1-I*Complex.exp w)*(1+I*Complex.exp w) := by
    intro w; linear_combination (Complex.exp w)^2*hI
  have hnz : ∀ w : ℂ, Complex.cosh w ≠ 0 → 1-I*Complex.exp w ≠ 0 ∧ 1+I*Complex.exp w ≠ 0 := by
    intro w hw
    have h := h2cosh w
    rw [hfac] at h
    have : (1-I*Complex.exp w)*(1+I*Complex.exp w) ≠ 0 := by
      rw [← h]; exact mul_ne_zero (mul_ne_zero two_ne_zero hw) (Complex.exp_ne_zero w)
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  set f : ℂ → ℂ := fun w => (1+I*Complex.exp w)/(1-I*Complex.exp w) with hfdef
  obtain ⟨hz1, hz2⟩ := hnz z hz
  set c := f z with hc
  have hc0 : c ≠ 0 := div_ne_zero hz2 hz1
  set V : Set ℂ := {w | 1-I*Complex.exp w ≠ 0} with hV
  have hVo : IsOpen V := isOpen_ne_fun (by fun_prop) continuous_const
  have hfc : ContinuousOn (fun w => f w / c) V := by
    intro w hw
    exact (((by fun_prop : Continuous (fun w : ℂ => 1+I*Complex.exp w)).continuousAt.div
      (by fun_prop : Continuous (fun w : ℂ => 1-I*Complex.exp w)).continuousAt hw).div_const
      c).continuousWithinAt
  set U : Set ℂ := V ∩ (fun w => f w / c) ⁻¹' Complex.slitPlane with hU
  have hUo : IsOpen U := hfc.isOpen_inter_preimage hVo Complex.isOpen_slitPlane
  have hzU : z ∈ U := ⟨hz1, by
    show f z / c ∈ Complex.slitPlane
    rw [← hc, div_self hc0]; exact Complex.one_mem_slitPlane⟩
  set G : ℂ → ℂ := fun w => -I*(Complex.log (f w / c) + Complex.log c) - π/2 with hG
  have hderiv : ∀ w ∈ U, HasDerivAt G (sech w) w := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw2 : f w / c ∈ Complex.slitPlane := hw2
    have hw1' : 1-I*Complex.exp w ≠ 0 := hw1
    have hfw : f w / c ≠ 0 := Complex.slitPlane_ne_zero hw2
    have hfw0 : f w ≠ 0 := fun h => hfw (by rw [h, zero_div])
    have hw3 : 1+I*Complex.exp w ≠ 0 := fun h => hfw0 (by simp [hfdef, h])
    have hcw : Complex.cosh w ≠ 0 := by
      intro h
      have := h2cosh w
      rw [h, hfac, mul_zero, zero_mul] at this
      exact mul_ne_zero hw1' hw3 this.symm
    have hN : HasDerivAt (fun w : ℂ => 1+I*Complex.exp w) (I*Complex.exp w) w :=
      ((Complex.hasDerivAt_exp w).const_mul I).const_add 1
    have hD : HasDerivAt (fun w : ℂ => 1-I*Complex.exp w) (-(I*Complex.exp w)) w :=
      ((Complex.hasDerivAt_exp w).const_mul I).const_sub 1
    have hf := (hN.div hD hw1').div_const c
    have hl := ((hf.clog hw2).add_const (Complex.log c)).const_mul (-I) |>.sub_const (π/2:ℂ)
    convert hl using 1
    simp only [sech]
    have he := Complex.exp_ne_zero w
    have h2 := h2cosh w
    simp only [Pi.div_apply]
    field_simp
    linear_combination (-(Complex.exp w)^2 + 2*Complex.cosh w*Complex.exp w)*hI - h2
  refine ⟨U, hUo, hzU, G, ?_, hderiv, ?_⟩
  · exact DifferentiableOn.analyticOnNhd
      (fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt) hUo
  · intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw2 : f w / c ∈ Complex.slitPlane := hw2
    have hw1' : 1-I*Complex.exp w ≠ 0 := hw1
    have hfw : f w / c ≠ 0 := Complex.slitPlane_ne_zero hw2
    set L := Complex.log (f w / c) + Complex.log c with hL
    have hexpL : Complex.exp L = f w := by
      rw [hL, Complex.exp_add, Complex.exp_log hfw, Complex.exp_log hc0]; field_simp
    set θ := G w/2+π/4 with hθ
    have hθI : θ*I = L/2 := by
      rw [hθ, hG]; simp only; linear_combination (-L/2)*hI
    set E := Complex.exp (L/2) with hE
    have hE2 : E^2 = f w := by rw [hE, ← Complex.exp_nat_mul]; push_cast; rw [← hexpL]; ring_nf
    have h1 : Complex.cos θ + Complex.sin θ*I = E := by rw [Complex.cos_add_sin_I, hθI]
    have h2 : (Complex.cos θ - Complex.sin θ*I)*E = 1 := by
      rw [Complex.cos_sub_sin_I, hE, ← Complex.exp_add, show -θ*I + L/2 = 0 by
        linear_combination -hθI]
      simp
    have hff : f w*(1-I*Complex.exp w) = 1+I*Complex.exp w := div_mul_cancel₀ _ hw1'
    set u := Complex.exp w
    set s := Complex.sin θ
    set k := Complex.cos θ
    have e1 : 2*E*(s*I) = E^2-1 := by linear_combination E*h1 - h2
    have e2 : 2*E*k = E^2+1 := by linear_combination E*h1 + h2
    have key : 2*E*(s*I - I*u*k) = 0 := by
      linear_combination e1 - I*u*e2 + (1-I*u)*hE2 + hff
    have hE0 : E ≠ 0 := Complex.exp_ne_zero _
    have hsk : s = u*k := by
      have := (mul_eq_zero.mp key).resolve_left (mul_ne_zero two_ne_zero hE0)
      have : I*(s-u*k) = 0 := by linear_combination this
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left Complex.I_ne_zero)
    have hk : k ≠ 0 := by
      intro h0
      rw [h0, mul_zero, hE2] at e2
      have hf1 : f w = -1 := by linear_combination -e2
      rw [hf1] at hff
      have : (2:ℂ) = 0 := by linear_combination -hff
      norm_num at this
    rw [Complex.tan_eq_sin_div_cos]
    change s / k = u
    rw [hsk, mul_div_assoc, div_self hk, mul_one]

/-- Oddness of all inverse-tanh branches includes the two values on each cut. -/
@[dlmf 4.37.E12]
theorem arctanh_values_neg (z : ℂ) :
    (fun w : ℂ => -w) '' arctanhValues z=arctanhValues (-z) := by
  ext w
  constructor
  · rintro ⟨a, ⟨hc, ht⟩, rfl⟩
    exact ⟨by rwa [Complex.cosh_neg], by rw [Complex.tanh_neg, ht]⟩
  · rintro ⟨hc, ht⟩
    refine ⟨-w, ⟨by rwa [Complex.cosh_neg], by rw [Complex.tanh_neg, ht, neg_neg]⟩, neg_neg w⟩

/-- Oddness of all inverse-coth branches includes the two cut values at zero. -/
@[dlmf 4.37.E15]
theorem arccoth_values_neg (z : ℂ) :
    (fun w : ℂ => -w) '' arccothValues z=arccothValues (-z) := by
  have hneg : ∀ w, coth (-w) = -coth w := fun w => by
    simp [coth, Complex.cosh_neg, Complex.sinh_neg, div_neg]
  ext w
  constructor
  · rintro ⟨a, ⟨hs, ht⟩, rfl⟩
    exact ⟨by rwa [Complex.sinh_neg, neg_ne_zero], by rw [hneg, ht]⟩
  · rintro ⟨hs, ht⟩
    refine ⟨-w, ⟨by rwa [Complex.sinh_neg, neg_ne_zero], by rw [hneg, ht, neg_neg]⟩, neg_neg w⟩

/-- The rectangular-hyperbola equation delimiting the transformed inverse-tanh series. -/
@[dlmf 4.38.E8]
theorem arctanh_transformed_boundary (z : ℂ) :
    (z^2).re=1/2 ↔ z.re^2-z.im^2=1/2 := by
  simp only [pow_two, Complex.mul_re]

/-- The regular endpoint of the principal inverse cosh is included in its logarithmic formulas. -/
@[dlmf 4.37.E19, dlmf 4.37.E21]
theorem arccosh_one : arccosh 1=0 := by
  simp [arccosh]

/-- At zero inverse coth has the finite half-period family; reciprocal zero is not totalized inside the inverse. -/
@[dlmf 4.37.E6, dlmf 4.37.E9]
theorem arccoth_zero_values :
    arccothValues 0=Set.range (fun k : ℤ => ((k:ℂ)+1/2)*π*I) := by
  ext w
  simp only [Set.mem_range]
  constructor
  · rintro ⟨hs, ht⟩
    rw [coth, div_eq_zero_iff] at ht
    obtain ⟨k, hk⟩ := (cosh_zeros w).mp (ht.resolve_right hs)
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    have hc : Complex.cosh (((k:ℂ)+1/2)*π*I) = 0 := (cosh_zeros _).mpr ⟨k, rfl⟩
    refine ⟨?_, by rw [coth, hc, zero_div]⟩
    intro hs
    have := Complex.cosh_sq_sub_sinh_sq (((k:ℂ)+1/2)*π*I)
    rw [hc, hs] at this; norm_num at this

/-- Continued inverse-sinh branches have the corresponding continued primitive. -/
theorem continued_antiderivative_arcsinh {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U)
    (hinv : ∀ w∈U, Complex.sinh (A w)=w) (hcrit : z≠I ∧ z≠ -I) :
    HasDerivAt (fun w => w*A w-Complex.cosh (A w)) (A z) z := by
  have hdA:=(hA z hz).differentiableAt.hasDerivAt
  have hd:=((hasDerivAt_id z).mul hdA).sub hdA.ccosh
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply]
    rw [hinv z hz]
    ring


/-- Continued inverse-cosh branches have the corresponding continued primitive. -/
theorem continued_antiderivative_arccosh {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U)
    (hinv : ∀ w∈U, Complex.cosh (A w)=w) (hcrit : z≠1 ∧ z≠ -1) :
    HasDerivAt (fun w => w*A w-Complex.sinh (A w)) (A z) z := by
  have hdA:=(hA z hz).differentiableAt.hasDerivAt
  have hd:=((hasDerivAt_id z).mul hdA).sub hdA.csinh
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply]
    rw [hinv z hz]
    ring


/-- Continued inverse-tanh and logarithm branches have the corresponding primitive. -/
theorem continued_antiderivative_arctanh {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A L : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hL : AnalyticOnNhd ℂ L U)
    (hinv : ∀ w∈U, Complex.tanh (A w)=w) (hpole : ∀ w∈U, Complex.cosh (A w)≠0)
    (hlog : ∀ w∈U, Complex.exp (L w)=Complex.cosh (A w)) :
    HasDerivAt (fun w => w*A w-L w) (A z) z := by
  have dA := (hA z hz).differentiableAt.hasDerivAt
  have dL := (hL z hz).differentiableAt.hasDerivAt
  have e := hypR4_deriv_eq hU hz dL.cexp dA.ccosh hlog
  rw [hlog z hz] at e
  have hc := hpole z hz
  have hlz : deriv L z = z*deriv A z := by
    calc deriv L z = Complex.sinh (A z)/Complex.cosh (A z)*deriv A z := by
          field_simp; linear_combination e
      _ = z*deriv A z := by rw [← Complex.tanh_eq_sinh_div_cosh, hinv z hz]
  have hd := ((hasDerivAt_id z).mul dA).sub dL
  convert hd using 1
  · rfl
  · dsimp only [id]
    rw [hlz]; ring

/-- Continued inverse-csch branches use a matching inverse-sinh square-root branch. -/
theorem continued_antiderivative_arccsch {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A B : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (hinv : ∀ w∈U, csch (A w)=w) (hpole : ∀ w∈U, Complex.sinh (A w)≠0)
    (hbinv : ∀ w∈U, Complex.sinh (B w)=w)
    (hbranch : ∀ w∈U, Complex.cosh (B w)=w*Complex.cosh (A w))
    (hcrit : z≠0 ∧ z≠I ∧ z≠ -I) :
    HasDerivAt (fun w => w*A w+B w) (A z) z := by
  have dA := (hA z hz).differentiableAt.hasDerivAt
  have dB := (hB z hz).differentiableAt.hasDerivAt
  have hs := hpole z hz
  have e1 := hypR4_deriv_eq hU hz ((hasDerivAt_csch hs).comp z dA) (hasDerivAt_id z) hinv
  have e2 := hypR4_deriv_eq hU hz dB.csinh (hasDerivAt_id z) hbinv
  rw [hbranch z hz] at e2
  have hcz := hinv z hz
  rw [csch] at hcz
  have hc0 : Complex.cosh (A z) ≠ 0 := by
    intro h; rw [h, mul_zero, zero_mul] at e2; exact zero_ne_one e2
  have hsz : Complex.sinh (A z) = z⁻¹ := by
    have := congrArg Inv.inv hcz; rwa [inv_inv] at this
  have hz0 : z ≠ 0 := hcrit.1
  have key : z*deriv A z + deriv B z = 0 := by
    rw [csch, coth, hsz, inv_inv, div_inv_eq_mul] at e1
    apply mul_left_cancel₀ (mul_ne_zero hz0 hc0)
    linear_combination -e1 + e2
  have hd := ((hasDerivAt_id z).mul dA).add dB
  convert hd using 1
  · rfl
  · dsimp only [id]
    linear_combination -key

/-- Continued inverse-sech branches use a matching inverse-sine square-root branch. -/
theorem continued_antiderivative_arcsech {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A B : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (hinv : ∀ w∈U, sech (A w)=w) (hpole : ∀ w∈U, Complex.cosh (A w)≠0)
    (hbinv : ∀ w∈U, Complex.sin (B w)=w)
    (hbranch : ∀ w∈U, Complex.cos (B w)=w*Complex.sinh (A w))
    (hcrit : z≠0 ∧ z≠1 ∧ z≠ -1) :
    HasDerivAt (fun w => w*A w+B w) (A z) z := by
  have dA := (hA z hz).differentiableAt.hasDerivAt
  have dB := (hB z hz).differentiableAt.hasDerivAt
  have hc := hpole z hz
  have e1 := hypR4_deriv_eq hU hz ((hasDerivAt_sech hc).comp z dA) (hasDerivAt_id z) hinv
  have e2 := hypR4_deriv_eq hU hz dB.csin (hasDerivAt_id z) hbinv
  rw [hbranch z hz] at e2
  have hcz := hinv z hz
  rw [sech] at hcz
  have hs0 : Complex.sinh (A z) ≠ 0 := by
    intro h; rw [h, mul_zero, zero_mul] at e2; exact zero_ne_one e2
  have hcz' : Complex.cosh (A z) = z⁻¹ := by
    have := congrArg Inv.inv hcz; rwa [inv_inv] at this
  have hz0 : z ≠ 0 := hcrit.1
  have key : z*deriv A z + deriv B z = 0 := by
    rw [sech, Complex.tanh_eq_sinh_div_cosh, hcz', inv_inv, div_inv_eq_mul] at e1
    apply mul_left_cancel₀ (mul_ne_zero hz0 hs0)
    linear_combination -e1 + e2
  have hd := ((hasDerivAt_id z).mul dA).add dB
  convert hd using 1
  · rfl
  · dsimp only [id]
    linear_combination -key

/-- Continued inverse-coth branches and a continued logarithm give the full complex primitive. -/
theorem continued_antiderivative_arccoth {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A L : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hL : AnalyticOnNhd ℂ L U)
    (hinv : ∀ w∈U, coth (A w)=w) (hpole : ∀ w∈U, Complex.sinh (A w)≠0)
    (hlog : ∀ w∈U, Complex.exp (2*L w)=w^2-1) :
    HasDerivAt (fun w => w*A w+L w) (A z) z := by
  have dA := (hA z hz).differentiableAt.hasDerivAt
  have dL := (hL z hz).differentiableAt.hasDerivAt
  have hs := hpole z hz
  have e1 := hypR4_deriv_eq hU hz ((hasDerivAt_coth hs).comp z dA) (hasDerivAt_id z) hinv
  have e2 := hypR4_deriv_eq hU hz (dL.const_mul 2).cexp ((hasDerivAt_id z).pow 2 |>.sub_const 1) hlog
  rw [hlog z hz] at e2
  have hcz := hinv z hz
  have hq : z^2-1 ≠ 0 := by rw [← hlog z hz]; exact Complex.exp_ne_zero _
  have hcs : csch (A z)^2 = z^2-1 := by
    have h : csch (A z)^2 = coth (A z)^2-1 := by
      rw [csch, coth]
      field_simp
      first | linear_combination Complex.cosh_sq_sub_sinh_sq (A z) |
        linear_combination -Complex.cosh_sq_sub_sinh_sq (A z)
    rw [h, hcz]
  have key : z*deriv A z + deriv L z = 0 := by
    rw [hcs] at e1
    apply mul_left_cancel₀ hq
    norm_num at e2
    linear_combination (-z)*e1 + e2/2
  have hd := ((hasDerivAt_id z).mul dA).add dL
  convert hd using 1
  · rfl
  · dsimp only [id]
    linear_combination -key

end DLMF.Elementary
