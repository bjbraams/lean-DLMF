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

public import DLMFMathlib.Analysis.Complex.TrigR4SeriesExtension

/-!
# Hyperbolic functions and their series

Direct hyperbolic functions, elementary inequalities, power series and parameter identities.

Source references and common attribution are retained in
`DLMF.Elementary.Hyperbolic`.
This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
The normalized logarithmic series integrate the Bernoulli expansions of their logarithmic
derivatives, using Cauchy–Taylor uniqueness and the removable values at the origin.
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
/-- Identity under the stated parameter and domain assumptions: `coth z=(Complex.tanh z)⁻¹`. -/
@[dlmf 4.28.E7]
theorem coth_eq_inv_tanh (z : ℂ) : coth z=(Complex.tanh z)⁻¹ := by
  simp [coth, Complex.tanh_eq_sinh_div_cosh, inv_div]

/-- Identity under the stated parameter and domain assumptions: `(Complex.sin (I*z))⁻¹= -I*csch
z`. -/
@[dlmf 4.28.E11]
theorem csc_mul_I (z : ℂ) : (Complex.sin (I*z))⁻¹= -I*csch z := by
  simp [mul_comm I z, Complex.sin_mul_I, csch, mul_inv_rev, Complex.inv_I, mul_comm]

/-- Identity under the stated parameter and domain assumptions: `(Complex.cos (I*z))⁻¹=sech z`. -/
@[dlmf 4.28.E12]
theorem sec_mul_I (z : ℂ) : (Complex.cos (I*z))⁻¹=sech z := by
  rw [mul_comm I z, Complex.cos_mul_I]; rfl

/-- Identity under the stated parameter and domain assumptions: `(Complex.tan (I*z))⁻¹= -I*coth
z`. -/
@[dlmf 4.28.E13]
theorem cot_mul_I (z : ℂ) : (Complex.tan (I*z))⁻¹= -I*coth z := by
  simp [mul_comm I z, Complex.tan_mul_I, coth_eq_inv_tanh, mul_inv_rev, Complex.inv_I, mul_comm]

/-- Identity under the stated parameter and domain assumptions: `Complex.sinh z=0 ↔ ∃ k : ℤ,
z=(k:ℂ)*π*I`. -/
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

/-- Identity under the stated parameter and domain assumptions: `Complex.cosh z=0 ↔ ∃ k : ℤ,
z=((k:ℂ)+1/2)*π*I`. -/
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

/-- The map `(fun z : ℂ => Complex.sinh z/z)` tends to `(𝓝 1)` along `(𝓝[≠] 0)`. -/
@[dlmf 4.31.E1]
theorem sinh_div_limit  : Tendsto (fun z : ℂ => Complex.sinh z/z) (𝓝[≠] 0) (𝓝 1) := by
  simpa [slope_fun_def_field] using (Complex.hasDerivAt_sinh (0:ℂ)).tendsto_slope

/-- The map `(fun z : ℂ => Complex.tanh z/z)` tends to `(𝓝 1)` along `(𝓝[≠] 0)`. -/
@[dlmf 4.31.E2]
theorem tanh_div_limit  : Tendsto (fun z : ℂ => Complex.tanh z/z) (𝓝[≠] 0) (𝓝 1) := by
  have hd:HasDerivAt Complex.tanh (1:ℂ) 0 := by
    convert (Complex.hasDerivAt_sinh (0:ℂ)).div (Complex.hasDerivAt_cosh (0:ℂ)) (by simp) using 1
    · ext w; exact Complex.tanh_eq_sinh_div_cosh w
    · simp
  simpa [slope_fun_def_field,Complex.tanh] using hd.tendsto_slope

/-- The map `(fun z : ℂ => (Complex.cosh z-1)/z^2)` tends to `(𝓝 (1/2))` along `(𝓝[≠] 0)`. -/
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

/-- Limit formula in the specified filter: `Tendsto Real.sinh atTop atTop ∧ Tendsto Real.cosh
atTop atTop ∧ Tendsto Real.tanh atTop (𝓝 1) ∧ Tendsto (fun x : ℝ => (Real.sinh x)⁻¹) atTop (𝓝
0) ∧ Tendsto (fun x : ℝ => (Real.cosh x)⁻¹) atTop (𝓝 0) ∧ Tendsto (fun x : ℝ => Real.cosh
x/Real.sinh x) atTop (𝓝 1)`. -/
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

/-- Limit formula in the specified filter: `Tendsto (fun z : ℂ => ‖csch z‖) (𝓝[≠] ((k:ℂ)*π*I))
atTop ∧ Tendsto (fun z : ℂ => ‖coth z‖) (𝓝[≠] ((k:ℂ)*π*I)) atTop`. -/
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

/-- Limit formula in the specified filter: `Tendsto (fun z : ℂ => ‖Complex.tanh z‖) (𝓝[≠]
(((k:ℂ)+1/2)*π*I)) atTop ∧ Tendsto (fun z : ℂ => ‖sech z‖) (𝓝[≠] (((k:ℂ)+1/2)*π*I)) atTop`. -/
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

/-- The auxiliary numerator for the derivative of the Lazarević ratio is positive. -/
private lemma hypR4_sinh_aux {x : ℝ} (hx : 0 < x) :
    0 < x * (3 + 2 * Real.sinh x ^ 2) - 3 * Real.sinh x * Real.cosh x := by
  have hg : ∀ t : ℝ, 0 < t → 0 < t * Real.cosh t - Real.sinh t := by
    intro t ht
    exact hypR4_pos_of_deriv_pos (f := fun u => u * Real.cosh u - Real.sinh u)
      (f' := fun u => u * Real.sinh u) (by fun_prop) (by simp)
      (fun u _ => by
        have h := ((hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)).sub (Real.hasDerivAt_sinh u)
        exact h.congr_deriv (by simp only [id_eq]; ring))
      (fun u hu => mul_pos hu (Real.sinh_pos_iff.mpr hu)) ht
  exact hypR4_pos_of_deriv_pos (f := fun u => u * (3 + 2 * Real.sinh u ^ 2) - 3 * Real.sinh u * Real.cosh u)
    (f' := fun u => 4 * Real.sinh u * (u * Real.cosh u - Real.sinh u))
    (by fun_prop) (by simp)
    (fun u _ => by
      have h := ((hasDerivAt_id u).mul ((Real.hasDerivAt_sinh u).pow 2 |>.const_mul 2 |>.const_add 3)).sub
        (((Real.hasDerivAt_sinh u).mul (Real.hasDerivAt_cosh u)).const_mul 3)
      have hh : 1 * (3 + 2 * Real.sinh u ^ 2) + u * (2 * (2 * Real.sinh u * Real.cosh u)) -
          3 * (Real.cosh u * Real.cosh u + Real.sinh u * Real.sinh u) =
          4 * Real.sinh u * (u * Real.cosh u - Real.sinh u) := by
        nlinarith [Real.cosh_sq_sub_sinh_sq u]
      simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by omega,
        pow_one] at h
      convert h.congr_deriv hh using 1
      funext t
      simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
      ring)
    (fun u hu => by have := hg u hu; have := Real.sinh_pos_iff.mpr hu; positivity) hx

/-- Estimate under the stated parameter and domain assumptions: `Real.cosh x ≤ (if x=0 then 1 else
Real.sinh x/x)^3`. -/
@[dlmf 4.32.E1]
theorem cosh_le_sinhc_cube (x : ℝ) : Real.cosh x ≤ (if x=0 then 1 else Real.sinh x/x)^3 := by
  let s : ℝ → ℝ := dslope Real.sinh 0
  have hs0 : s 0 = 1 := by simp [s, dslope_same, Real.deriv_sinh]
  have hseq : ∀ t : ℝ, t ≠ 0 → s t = Real.sinh t / t := by
    intro t ht
    simp [s, dslope_of_ne _ ht, slope_def_field]
  have hscont : Continuous s := by
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases ht : t = 0
    · subst t
      exact continuousAt_dslope_same.mpr (Real.differentiable_sinh.differentiableAt)
    · exact (continuousAt_dslope_of_ne ht).mpr Real.continuous_sinh.continuousAt
  have hsne : ∀ t, s t ≠ 0 := by
    intro t
    by_cases ht : t = 0
    · simp [ht, hs0]
    · rw [hseq t ht]
      exact div_ne_zero (Real.sinh_ne_zero.mpr ht) ht
  let g : ℝ → ℝ := fun t => Real.cosh t / s t ^ 3
  have hgcont : Continuous g := by
    exact Real.continuous_cosh.div (hscont.pow 3) (fun t => pow_ne_zero 3 (hsne t))
  have hgzero : g 0 = 1 := by simp [g, hs0]
  have hgformula : ∀ t, t ≠ 0 → g t = t ^ 3 * Real.cosh t / Real.sinh t ^ 3 := by
    intro t ht
    dsimp only [g]
    rw [hseq t ht]
    field_simp
  have hgderiv : ∀ t, 0 < t → HasDerivAt g
      (-(t ^ 2 * (t * (3 + 2 * Real.sinh t ^ 2) - 3 * Real.sinh t * Real.cosh t)) /
        Real.sinh t ^ 4) t := by
    intro t ht
    have hn : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
    have hd := (((hasDerivAt_pow 3 t).mul (Real.hasDerivAt_cosh t)).div
      ((Real.hasDerivAt_sinh t).pow 3) (pow_ne_zero 3 hn))
    have he : (3 * t ^ 2 * Real.cosh t + t ^ 3 * Real.sinh t) * Real.sinh t ^ 3 -
        t ^ 3 * Real.cosh t * (3 * Real.sinh t ^ 2 * Real.cosh t) =
        -t ^ 2 * (t * (3 + 2 * Real.sinh t ^ 2) - 3 * Real.sinh t * Real.cosh t) *
          Real.sinh t ^ 2 := by
      linear_combination (-3 * t ^ 3 * Real.sinh t ^ 2) * (Real.cosh_sq_sub_sinh_sq t)
    have hd' : HasDerivAt (fun t => t ^ 3 * Real.cosh t / Real.sinh t ^ 3)
        (-(t ^ 2 * (t * (3 + 2 * Real.sinh t ^ 2) - 3 * Real.sinh t * Real.cosh t)) /
          Real.sinh t ^ 4) t := by
      simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat,
        show 3 - 1 = (2 : ℕ) by omega] at hd
      apply hd.congr_deriv
      rw [he]
      field_simp
    refine hd'.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds (show t ∈ {y : ℝ | y ≠ 0} from ht.ne')] with u hu
    exact hgformula u hu
  have hmono : AntitoneOn g (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hgcont.continuousOn ?_ ?_
    · intro t ht
      rw [interior_Ici] at ht
      exact (hgderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hgderiv t ht).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (sq_nonneg t) (hypR4_sinh_aux ht).le)) (pow_nonneg (Real.sinh_pos_iff.mpr ht).le _)
  have hpos : ∀ x : ℝ, 0 ≤ x → Real.cosh x ≤ (if x=0 then 1 else Real.sinh x/x)^3 := by
    intro x hx
    have h := hmono (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hx) hx
    rw [hgzero] at h
    have heq : (if x=0 then 1 else Real.sinh x/x) = s x := by
      by_cases hx : x = 0 <;> simp [hx, hs0, hseq]
    rw [heq]
    have hdpos : 0 < s x ^ 3 := pow_pos (by
      by_cases h : x = 0
      · simp [h, hs0]
      · rw [hseq x h]; exact div_pos (Real.sinh_pos_iff.mpr (lt_of_le_of_ne hx (Ne.symm h))) (lt_of_le_of_ne hx (Ne.symm h))) _
    dsimp only [g] at h
    rw [div_le_iff₀ hdpos] at h
    linarith
  rcases le_total 0 x with hx | hx
  · exact hpos x hx
  · have h := hpos (-x) (neg_nonneg.mpr hx)
    simpa [Real.cosh_neg, Real.sinh_neg] using h

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

/-- Estimate under the stated parameter and domain assumptions: `Real.sin x*Real.cos x < Real.tanh
x ∧ Real.tanh x<x`. -/
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

/-- The stated relation follows from the given hypotheses: `|Real.cosh x-Real.cosh y| ≥ |x-y|
*Real.sqrt (Real.sinh x*Real.sinh y)`. -/
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

/-- Estimate under the stated parameter and domain assumptions: `Real.arctan x ≤ π/2*Real.tanh x`. -/
@[dlmf 4.32.E4]
theorem arctan_le_tanh {x : ℝ} (hx : 0≤x) : Real.arctan x ≤ π/2*Real.tanh x := by
  have hs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx
  have hm := Real.sin_arctan_strictMono.monotone hs
  have hc : Real.sqrt (1 + Real.sinh x ^ 2) = Real.cosh x := by
    have he : 1 + Real.sinh x ^ 2 = Real.cosh x ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
    rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.cosh_pos x)]
  rw [Real.sin_arctan (Real.sinh x), hc, ← Real.tanh_eq_sinh_div_cosh] at hm
  have h := Real.mul_le_sin (Real.arctan_nonneg.mpr hx) (Real.arctan_lt_pi_div_two x).le
  have hh := mul_le_mul_of_nonneg_left (h.trans hm) (show 0 ≤ π / 2 by positivity)
  have he : π / 2 * (2 / π * Real.arctan x) = Real.arctan x := by
    field_simp
  rwa [he] at hh

/-- Powers of the rotated argument `iz` produce the alternating sign `(-1)^k`. -/
private lemma hypR4_rot_pow (z c : ℂ) (k : ℕ) : (c*(I*z))^(2*k) = (-1:ℂ)^k*(c*z)^(2*k) := by
  rw [show c*(I*z) = I*(c*z) by ring, mul_pow, pow_mul, Complex.I_sq]

/-- The square of the alternating sign is one. -/
private lemma hypR4_neg_one_sq (k : ℕ) : (-1:ℂ)^k*(-1:ℂ)^k = 1 := by
  rw [← mul_pow]; norm_num

/-- The rotated point `iz/π` has norm `‖z‖/π`. -/
private lemma hypR4_norm_rot (z : ℂ) : ‖I*z/π‖ = ‖z‖/π := by
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

/-- The series with terms `(fun n : ℕ => (2:ℂ)^(2*(n+1))*((2:ℂ)^(2*(n+1))-1)* (bernoulli
(2*(n+1)):ℂ)/((2*(n+1)).factorial:ℂ)*z^(2*n+1))` converges to `(Complex.tanh z)`. -/
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

/-- The series with terms `(fun n : ℕ => 2*(1-(2:ℂ)^(2*n+1))*(bernoulli (2*n+2):ℂ)/
((2*n+2).factorial:ℂ)*z^(2*n+1))` converges to `(csch z-z⁻¹)`. -/
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

/-- The series with terms `(fun n : ℕ => (eulerNumber (2*n):ℂ)/((2*n).factorial:ℂ)*z^(2*n))`
converges to `(sech z)`. -/
theorem hasSum_sech {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (eulerNumber (2*n):ℂ)/((2*n).factorial:ℂ)*z^(2*n)) (sech z) := by
  have hw : ‖1*(I*z)‖ < π/2 := by rw [one_mul, norm_mul, Complex.norm_I, one_mul]; exact hz
  have h := hasSum_sec_euler hw
  convert h using 1
  · funext n
    rw [hypR4_rot_pow, one_mul]
    linear_combination (-(eulerNumber (2*n):ℂ)*z^(2*n)/((2*n).factorial:ℂ))*hypR4_neg_one_sq n
  · rw [sec, one_mul, mul_comm, Complex.cos_mul_I, sech]

/-- The series with terms `(fun n : ℕ => (2:ℂ)^(2*n+2)*(bernoulli (2*n+2):ℂ)/
((2*n+2).factorial:ℂ)*z^(2*n+1))` converges to `(coth z-z⁻¹)`. -/
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

/-- The derivative of a normalized analytic logarithm is the logarithmic derivative of its
exponential; equality on the open domain supplies differentiability of the exponential. -/
private lemma hypR4_deriv_normalizedLog {U : Set ℂ} (hU : IsOpen U) {f L : ℂ → ℂ}
    (hL : HyperbolicNormalizedLog U f L) {z : ℂ} (hz : z ∈ U) :
    deriv L z = deriv f z / f z := by
  have hd : HasDerivAt L (deriv L z) z := (hL.1 z hz).differentiableAt.hasDerivAt
  have he : (fun w => Complex.exp (L w)) =ᶠ[𝓝 z] f :=
    eventually_of_mem (hU.mem_nhds hz) hL.2.2
  have hh := (hd.cexp).congr_of_eventuallyEq he.symm
  have hne : f z ≠ 0 := by rw [← hL.2.2 z hz]; exact Complex.exp_ne_zero _
  apply (eq_div_iff hne).mpr
  have hval := hh.deriv
  rw [hL.2.2 z hz] at hval
  simpa [mul_comm] using hval.symm

/-- A normalized analytic logarithm of an even function has zero derivative at the origin. -/
private lemma hypR4_deriv_normalizedLog_zero {R : ℝ} (hR : 0 < R) {f L : ℂ → ℂ}
    (hL : HyperbolicNormalizedLog (Metric.ball 0 R) f L) (heven : ∀ z, f (-z) = f z) :
    deriv L 0 = 0 := by
  have h0 : (0 : ℂ) ∈ Metric.ball 0 R := by simpa using hR
  have hd : HasDerivAt L (deriv L 0) 0 := (hL.1 0 h0).differentiableAt.hasDerivAt
  have he : (fun w => Complex.exp (L w)) =ᶠ[𝓝 (0 : ℂ)] f :=
    eventually_of_mem (Metric.isOpen_ball.mem_nhds h0) hL.2.2
  have hh := (hd.cexp).congr_of_eventuallyEq he.symm
  have hn := hh.comp_of_eq (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).neg) (by simp)
  have hh' : HasDerivAt f (-(Complex.exp (L 0) * deriv L 0)) 0 := by
    simpa only [Function.comp_def, Pi.neg_apply, id_eq, heven, mul_neg, mul_one] using hn
  have h := hh.unique hh'
  simp only [hL.2.1, Complex.exp_zero, one_mul] at h
  linear_combination (1 / 2 : ℂ) * h

/-- The Bernoulli expansion of an analytic logarithm of the removable quotient `sinh z / z`,
normalized to vanish at zero, on the disk `‖z‖ < π`. -/
theorem hasSum_log_sinhc {L : ℂ → ℂ} (hL : HyperbolicNormalizedLog (Metric.ball 0 π) sinhc L)
    {z : ℂ} (hz : ‖z‖<π) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*n+1)*(bernoulli (2*n+2):ℂ)/
      ((n+1:ℂ)*((2*n+2).factorial:ℂ))*z^(2*n+2)) (L z) := by
  let b : ℕ → ℂ := fun n => (2:ℂ)^(2*n+2)*(bernoulli (2*n+2):ℂ)/
      ((2*n+2).factorial:ℂ)
  have hb : ∀ w : ℂ, ‖w‖ < π → HasSum (fun n => b n * w ^ (2*n+1)) (deriv L w) := by
    intro w hw
    by_cases hw0 : w = 0
    · subst w
      have hd := hypR4_deriv_normalizedLog_zero Real.pi_pos hL (by
        intro w
        simp [sinhc])
      rw [hd]
      convert hasSum_zero using 1
      ext n
      simp
    · have hd := hypR4_deriv_normalizedLog Metric.isOpen_ball hL (by simpa using hw)
      have he : sinhc =ᶠ[𝓝 w] (fun v => Complex.sinh v / v) := by
        filter_upwards [eventually_ne_nhds hw0] with v hv
        simp [sinhc, hv]
      have hdq := ((Complex.hasDerivAt_sinh w).div (hasDerivAt_id w) hw0).congr_of_eventuallyEq he
      rw [hdq.deriv, sinhc, ite_eq_right hw0] at hd
      have hs : Complex.sinh w ≠ 0 := by
        have hne : sinhc w ≠ 0 := by rw [← hL.2.2 w (by simpa using hw)]; exact Complex.exp_ne_zero _
        rw [sinhc, ite_eq_right hw0] at hne
        exact (div_ne_zero_iff.mp hne).1
      have hd' : deriv L w = coth w - w⁻¹ := by
        rw [hd, coth]
        simp only [id_eq, mul_one]
        field_simp
      rw [hd']
      exact hasSum_coth hw0 hw
  have hs := Complex.hasSum_odd_primitive_on_ball Real.pi_pos hL.1.differentiableOn hL.2.1 hb hz
  convert hs using 1
  ext n
  dsimp only [b]
  rw [show 2*n+2 = (2*n+1)+1 by omega, pow_succ (2:ℂ)]
  have hn0 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : ((2*n+1+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  ring

/-- The Bernoulli expansion of an analytic logarithm of `cosh`, normalized to vanish at zero,
on the disk `‖z‖ < π / 2`. -/
theorem hasSum_log_cosh {L : ℂ → ℂ} (hL : HyperbolicNormalizedLog (Metric.ball 0 (π/2)) Complex.cosh L)
    {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*n+1)*((2:ℂ)^(2*n+2)-1)*(bernoulli (2*n+2):ℂ)/
      ((n+1:ℂ)*((2*n+2).factorial:ℂ))*z^(2*n+2)) (L z) := by
  let b : ℕ → ℂ := fun n => (2:ℂ)^(2*(n+1))*((2:ℂ)^(2*(n+1))-1)*
      (bernoulli (2*(n+1)):ℂ)/((2*(n+1)).factorial:ℂ)
  have hb : ∀ w : ℂ, ‖w‖ < π/2 → HasSum (fun n => b n * w^(2*n+1)) (deriv L w) := by
    intro w hw
    have hd := hypR4_deriv_normalizedLog Metric.isOpen_ball hL (by simpa using hw)
    rw [Complex.deriv_cosh, ←Complex.tanh_eq_sinh_div_cosh] at hd
    rw [hd]
    exact hasSum_tanh hw
  have hs := Complex.hasSum_odd_primitive_on_ball (by positivity : 0 < π/2)
    hL.1.differentiableOn hL.2.1 hb hz
  convert hs using 1
  ext n
  dsimp only [b]
  rw [show 2*(n+1) = 2*n+2 by omega,
    show 2*n+2 = (2*n+1)+1 by omega, pow_succ (2:ℂ)]
  have hn0 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : ((2*n+1+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  ring

/-- At `z`, the function `Complex.tanh` has derivative `(sech z^2)`. -/
@[dlmf 4.34.E3]
theorem hasDerivAt_tanh {z : ℂ} (hz : Complex.cosh z≠0) : HasDerivAt Complex.tanh (sech z^2) z := by
  convert (Complex.hasDerivAt_sinh z).div (Complex.hasDerivAt_cosh z) hz using 1
  · ext w; exact Complex.tanh_eq_sinh_div_cosh w
  · simp only [sech]
    field_simp
    linear_combination -(Complex.cosh_sq_sub_sinh_sq z)

/-- The Bernoulli expansion of an analytic logarithm of the removable quotient `tanh z / z`,
normalized to vanish at zero, on the disk `‖z‖ < π / 2`. -/
theorem hasSum_log_tanhc {L : ℂ → ℂ} (hL : HyperbolicNormalizedLog (Metric.ball 0 (π/2)) tanhc L)
    {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*n+2)*(1-(2:ℂ)^(2*n+1))*(bernoulli (2*n+2):ℂ)/
      ((n+1:ℂ)*((2*n+2).factorial:ℂ))*z^(2*n+2)) (L z) := by
  let b : ℕ → ℂ := fun n => (2:ℂ)^(2*n+2)*(bernoulli (2*n+2):ℂ)/
      ((2*n+2).factorial:ℂ) -
      (2:ℂ)^(2*(n+1))*((2:ℂ)^(2*(n+1))-1)*(bernoulli (2*(n+1)):ℂ)/
        ((2*(n+1)).factorial:ℂ)
  have hb : ∀ w : ℂ, ‖w‖ < π/2 → HasSum (fun n => b n * w ^ (2*n+1)) (deriv L w) := by
    intro w hw
    by_cases hw0 : w = 0
    · subst w
      have hd := hypR4_deriv_normalizedLog_zero (by positivity : 0 < π/2) hL (by
        intro w
        simp only [tanhc, neg_eq_zero, Complex.tanh_eq_sinh_div_cosh,
          Complex.sinh_neg, Complex.cosh_neg]
        split_ifs <;> ring)
      rw [hd]
      convert hasSum_zero using 1
      ext n
      simp
    · have hne : Complex.tanh w ≠ 0 := by
        have hne : tanhc w ≠ 0 := by
          rw [← hL.2.2 w (by simpa using hw)]
          exact Complex.exp_ne_zero _
        rw [tanhc, ite_eq_right hw0] at hne
        exact (div_ne_zero_iff.mp hne).1
      have hs : Complex.sinh w ≠ 0 := by
        rw [Complex.tanh_eq_sinh_div_cosh] at hne
        exact (div_ne_zero_iff.mp hne).1
      have hc : Complex.cosh w ≠ 0 := by
        rw [Complex.tanh_eq_sinh_div_cosh] at hne
        exact (div_ne_zero_iff.mp hne).2
      have hd := hypR4_deriv_normalizedLog Metric.isOpen_ball hL (by simpa using hw)
      have he : tanhc =ᶠ[𝓝 w] (fun v => Complex.tanh v / v) := by
        filter_upwards [eventually_ne_nhds hw0] with v hv
        simp [tanhc, hv]
      have hdq := ((hasDerivAt_tanh hc).div (hasDerivAt_id w) hw0).congr_of_eventuallyEq he
      rw [hdq.deriv, tanhc, ite_eq_right hw0] at hd
      have hd' : deriv L w = (coth w - w⁻¹) - Complex.tanh w := by
        rw [hd, coth, sech, Complex.tanh_eq_sinh_div_cosh]
        simp only [id_eq, mul_one]
        field_simp
        linear_combination -w * (Complex.cosh_sq_sub_sinh_sq w)
      rw [hd']
      have hp : ‖w‖ < π := lt_trans hw (by linarith [Real.pi_pos])
      convert (hasSum_coth hw0 hp).sub (hasSum_tanh hw) using 1
      ext n
      dsimp only [b]
      ring
  have ht := Complex.hasSum_odd_primitive_on_ball (by positivity : 0 < π/2)
    hL.1.differentiableOn hL.2.1 hb hz
  convert ht using 1
  ext n
  dsimp only [b]
  rw [show 2*(n+1) = 2*n+2 by omega,
    show 2*n+2 = (2*n+1)+1 by omega, pow_succ (2:ℂ)]
  have hn0 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : ((2*n+1+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  ring

/-- At `z`, the function `csch` has derivative `(-csch z*coth z)`. -/
@[dlmf 4.34.E4]
theorem hasDerivAt_csch {z : ℂ} (hz : Complex.sinh z≠0) : HasDerivAt csch (-csch z*coth z) z := by
  convert (Complex.hasDerivAt_sinh z).inv hz using 1
  · rfl
  · simp only [csch, coth]
    field_simp <;> ring

/-- At `z`, the function `sech` has derivative `(-sech z*Complex.tanh z)`. -/
@[dlmf 4.34.E5]
theorem hasDerivAt_sech {z : ℂ} (hz : Complex.cosh z≠0) : HasDerivAt sech (-sech z*Complex.tanh z) z := by
  convert (Complex.hasDerivAt_cosh z).inv hz using 1
  · rfl
  · simp only [sech, Complex.tanh_eq_sinh_div_cosh]
    field_simp <;> ring

/-- At `z`, the function `coth` has derivative `(-csch z^2)`. -/
@[dlmf 4.34.E6]
theorem hasDerivAt_coth {z : ℂ} (hz : Complex.sinh z≠0) : HasDerivAt coth (-csch z^2) z := by
  convert (Complex.hasDerivAt_cosh z).div (Complex.hasDerivAt_sinh z) hz using 1
  · rfl
  · simp only [coth, csch]
    field_simp
    linear_combination (Complex.cosh_sq_sub_sinh_sq z)

/-- Formula under the stated hypotheses: `(∀ z ∈ U, deriv (deriv f) z-a^2*f z=0) ↔ ∃ A B : ℂ, ∀ z
∈ U, f z=A*Complex.cosh (a*z)+B*Complex.sinh (a*z)`. -/
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

end DLMF.Elementary
end
