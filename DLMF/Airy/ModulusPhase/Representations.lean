/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Framework
public import DLMF.Airy.ModulusTools
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticInversion

/-!
# Airy modulus and phase representations

Real-axis calculus, complex modulus-phase representations and their Bessel-function forms.

Source references and common attribution are retained in
`DLMF.Airy.ModulusPhase`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology

namespace DLMF.Airy

/-- Airy modulus M. -/
@[dlmf 9.8.E3]
def airyModulus (x : ℝ) : ℝ := Real.sqrt (airyAiReal x ^ 2 + airyBiReal x ^ 2)
/-- Derivative modulus N. -/
@[dlmf 9.8.E7]
def airyDerivModulus (x : ℝ) : ℝ := Real.sqrt (airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2)
/-- The unwrapped phase θ, normalized to θ(0)=π/6. -/
def airyPhase (x : ℝ) : ℝ := π / 6 - ∫ t in (0 : ℝ)..x, 1 / (π * airyModulus t ^ 2)
/-- The unwrapped derivative phase φ, normalized to φ(0)=-π/6. -/
def airyDerivPhase (x : ℝ) : ℝ := -π / 6 + ∫ t in (0 : ℝ)..x, t / (π * airyDerivModulus t ^ 2)
/-- Coefficients of M² at negative infinity. -/
def airyModulusCoeff (k : ℕ) : ℝ :=
  (∏ j ∈ Finset.range (3 * k), (2 * (j : ℝ) + 1)) / (k.factorial * 96 ^ k)
/-- Coefficients of N² at negative infinity. -/
def airyDerivModulusCoeff (k : ℕ) : ℝ :=
  airyModulusCoeff k * (1 + 6 * (k : ℝ)) / (1 - 6 * (k : ℝ))
/-- Formal reciprocal coefficients, with unit constant term. -/
def airyReciprocalCoeff (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => -∑ j ∈ Finset.range (n + 1), c (j + 1) * airyReciprocalCoeff c (n - j)
termination_by n => n
/-- The all-order θ expansion coefficients, obtained by integrating 1/M². -/
def airyPhaseCoeff (k : ℕ) : ℝ := airyReciprocalCoeff airyModulusCoeff k / (1 - 2 * (k : ℝ))
/-- The all-order φ expansion coefficients, obtained by integrating x/N². -/
def airyDerivPhaseCoeff (k : ℕ) : ℝ := airyReciprocalCoeff airyDerivModulusCoeff k / (1 - 2 * (k : ℝ))
/-- Modulus-square truncation, before its algebraic prefactor. -/
def airyModulusSum (derivative : Bool) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, (if derivative then airyDerivModulusCoeff k else airyModulusCoeff k) * x ^ (-(3 * k : ℤ))
/-- Phase truncation, before its leading algebraic prefactor. -/
def airyPhaseSum (derivative : Bool) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, (if derivative then airyDerivPhaseCoeff k else airyPhaseCoeff k) * x ^ (-(3 * k : ℤ))

/-! ### Real-axis calculus for `Ai`, `Bi` -/

/-- `Ai(x)` as the cast of its real part. -/
theorem airyAi_ofReal_eq (x : ℝ) : airyAi x = (airyAiReal x : ℂ) :=
  Complex.ext (by simp [airyAiReal]) (by simp [airyAi_ofReal_im])

/-- `Bi(x)` as the cast of its real part. -/
theorem airyBi_ofReal_eq (x : ℝ) : airyBi x = (airyBiReal x : ℂ) :=
  Complex.ext (by simp [airyBiReal]) (by simp [airyBi_ofReal_im])

/-- `Ai'(x)` as the cast of its real part. -/
theorem airyAiDeriv_ofReal_eq (x : ℝ) : airyAiDeriv x = (airyAiDerivReal x : ℂ) :=
  Complex.ext (by simp [airyAiDerivReal]) (by simp [airyDer_aiDeriv_ofReal_im])

/-- `Bi'(x)` as the cast of its real part. -/
theorem airyBiDeriv_ofReal_eq (x : ℝ) : airyBiDeriv x = (airyBiDerivReal x : ℂ) :=
  Complex.ext (by simp [airyBiDerivReal]) (by simp [airyDer_biDeriv_ofReal_im])

/-- The real derivative of `Ai` on the real axis. -/
theorem hasDerivAt_airyAiReal (x : ℝ) : HasDerivAt airyAiReal (airyAiDerivReal x) x :=
  (hasDerivAt_airyAi x).real_of_complex

/-- The real derivative of `Bi` on the real axis. -/
theorem hasDerivAt_airyBiReal (x : ℝ) : HasDerivAt airyBiReal (airyBiDerivReal x) x :=
  (hasDerivAt_airyBi x).real_of_complex

/-- Airy's equation for `Ai` on the real axis. -/
theorem hasDerivAt_airyAiDerivReal (x : ℝ) :
    HasDerivAt airyAiDerivReal (x * airyAiReal x) x := by
  have h := (hasDerivAt_airyAiDeriv x).real_of_complex
  exact h.congr_deriv (by simp [airyAiReal])

/-- Airy's equation for `Bi` on the real axis. -/
theorem hasDerivAt_airyBiDerivReal (x : ℝ) :
    HasDerivAt airyBiDerivReal (x * airyBiReal x) x := by
  have h := (hasDerivAt_airyBiDeriv x).real_of_complex
  exact h.congr_deriv (by simp [airyBiReal])

/-- The real Wronskian `Ai Bi' - Ai' Bi = 1/π`. -/
theorem wronskian_airyReal (x : ℝ) :
    airyAiReal x * airyBiDerivReal x - airyAiDerivReal x * airyBiReal x = 1 / π := by
  have h := wronskian_airyAi_airyBi x
  rw [airyAi_ofReal_eq, airyBi_ofReal_eq, airyAiDeriv_ofReal_eq, airyBiDeriv_ofReal_eq] at h
  exact_mod_cast h

/-- `Ai² + Bi² > 0` on the real axis. -/
theorem airyModulusSq_pos (x : ℝ) : 0 < airyAiReal x ^ 2 + airyBiReal x ^ 2 := by
  by_contra h
  have ha : airyAiReal x = 0 := by nlinarith [sq_nonneg (airyAiReal x), sq_nonneg (airyBiReal x)]
  have hb : airyBiReal x = 0 := by nlinarith [sq_nonneg (airyAiReal x), sq_nonneg (airyBiReal x)]
  have hw := wronskian_airyReal x
  rw [ha, hb] at hw
  have : (1 / π : ℝ) ≠ 0 := by have := Real.pi_pos; positivity
  exact this (by linarith)

/-- `Ai'² + Bi'² > 0` on the real axis. -/
theorem airyDerivModulusSq_pos (x : ℝ) : 0 < airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2 := by
  by_contra h
  have ha : airyAiDerivReal x = 0 := by
    nlinarith [sq_nonneg (airyAiDerivReal x), sq_nonneg (airyBiDerivReal x)]
  have hb : airyBiDerivReal x = 0 := by
    nlinarith [sq_nonneg (airyAiDerivReal x), sq_nonneg (airyBiDerivReal x)]
  have hw := wronskian_airyReal x
  rw [ha, hb] at hw
  have : (1 / π : ℝ) ≠ 0 := by have := Real.pi_pos; positivity
  exact this (by linarith)

/-- `M² = Ai² + Bi²`. -/
theorem airyModulus_sq (x : ℝ) : airyModulus x ^ 2 = airyAiReal x ^ 2 + airyBiReal x ^ 2 :=
  Real.sq_sqrt (airyModulusSq_pos x).le

/-- `N² = Ai'² + Bi'²`. -/
theorem airyDerivModulus_sq (x : ℝ) :
    airyDerivModulus x ^ 2 = airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2 :=
  Real.sq_sqrt (airyDerivModulusSq_pos x).le

/-- `M > 0`. -/
theorem airyModulus_pos (x : ℝ) : 0 < airyModulus x := Real.sqrt_pos.mpr (airyModulusSq_pos x)

/-- `N > 0`. -/
theorem airyDerivModulus_pos (x : ℝ) : 0 < airyDerivModulus x :=
  Real.sqrt_pos.mpr (airyDerivModulusSq_pos x)

/-- `M' = (Ai Ai' + Bi Bi')/M`. -/
theorem hasDerivAt_airyModulus (x : ℝ) :
    HasDerivAt airyModulus
      ((airyAiReal x * airyAiDerivReal x + airyBiReal x * airyBiDerivReal x) / airyModulus x) x := by
  have h := (((hasDerivAt_airyAiReal x).pow 2).add ((hasDerivAt_airyBiReal x).pow 2)).sqrt
    (airyModulusSq_pos x).ne'
  refine h.congr_deriv ?_
  simp only [airyModulus, Pi.add_apply, Pi.pow_apply]
  have := airyModulus_pos x
  simp only [airyModulus] at this
  field_simp
  push_cast
  ring

/-- `N' = x (Ai Ai' + Bi Bi')/N`. -/
theorem hasDerivAt_airyDerivModulus (x : ℝ) :
    HasDerivAt airyDerivModulus
      (x * (airyAiReal x * airyAiDerivReal x + airyBiReal x * airyBiDerivReal x) /
        airyDerivModulus x) x := by
  have h := (((hasDerivAt_airyAiDerivReal x).pow 2).add ((hasDerivAt_airyBiDerivReal x).pow 2)).sqrt
    (airyDerivModulusSq_pos x).ne'
  refine h.congr_deriv ?_
  simp only [airyDerivModulus, Pi.add_apply, Pi.pow_apply]
  have := airyDerivModulus_pos x
  simp only [airyDerivModulus] at this
  field_simp
  push_cast
  ring

/-- `M` is continuous. -/
theorem continuous_airyModulus : Continuous airyModulus :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyModulus x).continuousAt

/-- `N` is continuous. -/
theorem continuous_airyDerivModulus : Continuous airyDerivModulus :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyDerivModulus x).continuousAt

/-- `θ' = -1/(π M²)`. -/
theorem hasDerivAt_airyPhase (x : ℝ) : HasDerivAt airyPhase (-(1 / (π * airyModulus x ^ 2))) x := by
  have hc : Continuous fun t => 1 / (π * airyModulus t ^ 2) := by
    refine continuous_const.div (continuous_const.mul (continuous_airyModulus.pow 2)) fun t => ?_
    have := airyModulus_pos t; have := Real.pi_pos; positivity
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact h.const_sub _

/-- `φ' = x/(π N²)`. -/
theorem hasDerivAt_airyDerivPhase (x : ℝ) :
    HasDerivAt airyDerivPhase (x / (π * airyDerivModulus x ^ 2)) x := by
  have hc : Continuous fun t => t / (π * airyDerivModulus t ^ 2) := by
    refine continuous_id.div (continuous_const.mul (continuous_airyDerivModulus.pow 2)) fun t => ?_
    have := airyDerivModulus_pos t; have := Real.pi_pos; positivity
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  exact h.const_add _

/-- The derivative of `M` as a function. -/
theorem deriv_airyModulus : deriv airyModulus = fun x =>
    (airyAiReal x * airyAiDerivReal x + airyBiReal x * airyBiDerivReal x) / airyModulus x :=
  funext fun x => (hasDerivAt_airyModulus x).deriv

/-- The derivative of `N` as a function. -/
theorem deriv_airyDerivModulus : deriv airyDerivModulus = fun x =>
    x * (airyAiReal x * airyAiDerivReal x + airyBiReal x * airyBiDerivReal x) /
      airyDerivModulus x :=
  funext fun x => (hasDerivAt_airyDerivModulus x).deriv

/-- The derivative of `θ` as a function. -/
theorem deriv_airyPhase : deriv airyPhase = fun x => -(1 / (π * airyModulus x ^ 2)) :=
  funext fun x => (hasDerivAt_airyPhase x).deriv

/-- The derivative of `φ` as a function. -/
theorem deriv_airyDerivPhase : deriv airyDerivPhase = fun x => x / (π * airyDerivModulus x ^ 2) :=
  funext fun x => (hasDerivAt_airyDerivPhase x).deriv

/-- The Lagrange identity combined with the Wronskian: `N² M² = (AA' + BB')² + π⁻²`. -/
theorem airy_lagrange (x : ℝ) :
    (airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2) * (airyAiReal x ^ 2 + airyBiReal x ^ 2) * π ^ 2
      = (airyAiReal x * airyAiDerivReal x + airyBiReal x * airyBiDerivReal x) ^ 2 * π ^ 2 + 1 := by
  have hW := wronskian_airyReal x
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hW' : (airyAiReal x * airyBiDerivReal x - airyAiDerivReal x * airyBiReal x) * π = 1 := by
    rw [hW]; field_simp
  linear_combination ((airyAiReal x * airyBiDerivReal x - airyAiDerivReal x * airyBiReal x) * π
    + 1) * hW'

/-- `S = AA' + BB'`, half the derivative of `M²`. -/
theorem hasDerivAt_airyCross (x : ℝ) :
    HasDerivAt (fun t => airyAiReal t * airyAiDerivReal t + airyBiReal t * airyBiDerivReal t)
      (airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2 +
        x * (airyAiReal x ^ 2 + airyBiReal x ^ 2)) x := by
  have h := ((hasDerivAt_airyAiReal x).mul (hasDerivAt_airyAiDerivReal x)).add
    ((hasDerivAt_airyBiReal x).mul (hasDerivAt_airyBiDerivReal x))
  exact h.congr_deriv (by ring)

/-- `M²` as a function. -/
theorem airyModulus_sq_fun : (fun t => airyModulus t ^ 2) =
    fun t => airyAiReal t ^ 2 + airyBiReal t ^ 2 := funext airyModulus_sq

/-! ### The complex form of the modulus–phase representation -/

/-- `Bi(0) = √3 Ai(0)`. -/
theorem airyBiReal_zero_eq : airyBiReal 0 = Real.sqrt 3 * airyAiReal 0 := by
  have hA := airyAi_zero
  have hB := airyBi_zero
  rw [Gamma_two_thirds_eq] at hA hB
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_div] at hA hB
  simp only [airyAiReal, airyBiReal, Complex.ofReal_zero, hA, hB, Complex.ofReal_re]
  have h : (3 : ℝ) ^ (2 / 3 : ℝ) = Real.sqrt 3 * 3 ^ (1 / 6 : ℝ) := by
    rw [sqrt_three_eq_rpow, three_rpow_add]; norm_num
  rw [h]
  have : 0 < (3 : ℝ) ^ (1 / 6 : ℝ) := by positivity
  have : 0 < Real.sqrt 3 := by positivity
  have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)
  field_simp

/-- `Ai(0) > 0`. -/
theorem airyAiReal_zero_pos : 0 < airyAiReal 0 := by
  obtain ⟨r, hr, he⟩ := airyAi_ofReal_pos (le_refl 0)
  rw [Complex.ofReal_zero] at he
  simp [airyAiReal, he, hr]

/-- The complex combination `Bi + i Ai` on the real axis. -/
theorem hasDerivAt_airyBiAiComplex (t : ℝ) :
    HasDerivAt (fun s : ℝ => (airyBiReal s : ℂ) + I * airyAiReal s)
      ((airyBiDerivReal t : ℂ) + I * airyAiDerivReal t) t :=
  (hasDerivAt_airyBiReal t).ofReal_comp.add ((hasDerivAt_airyAiReal t).ofReal_comp.const_mul I)

/-- `Bi + i Ai = M e^{iθ}` on the whole real axis (DLMF 9.8.1–9.8.2 in complex form). -/
theorem airyBi_add_I_airyAi (x : ℝ) :
    (airyBiReal x : ℂ) + I * airyAiReal x = airyModulus x * exp (I * airyPhase x) := by
  set g : ℝ → ℂ := fun s => ((airyBiReal s : ℂ) + I * airyAiReal s) *
    exp (-(I * airyPhase s)) / airyModulus s with hg
  have hd : ∀ t, HasDerivAt g 0 t := by
    intro t
    have hE : HasDerivAt (fun s : ℝ => exp (-(I * airyPhase s)))
        (exp (-(I * airyPhase t)) * (-(I * ((-(1 / (π * airyModulus t ^ 2)) : ℝ) : ℂ)))) t :=
      (((hasDerivAt_airyPhase t).ofReal_comp.const_mul I).neg).cexp
    have hM := (hasDerivAt_airyModulus t).ofReal_comp
    have hM0 : (airyModulus t : ℂ) ≠ 0 := by exact_mod_cast (airyModulus_pos t).ne'
    have h := ((hasDerivAt_airyBiAiComplex t).mul hE).div hM hM0
    refine h.congr_deriv ?_
    have hW := wronskian_airyReal t
    have hM2 := airyModulus_sq t
    have hMr := (airyModulus_pos t).ne'
    have hπ := Real.pi_ne_zero
    simp only [Pi.mul_apply]
    rw [div_eq_zero_iff]; left
    generalize exp (-(I * airyPhase t)) = e
    push_cast
    generalize airyAiReal t = a at *
    generalize airyBiReal t = b at *
    generalize airyAiDerivReal t = a' at *
    generalize airyBiDerivReal t = b' at *
    generalize airyModulus t = m at *
    have hW' : ((a : ℂ) * b' - a' * b) * π = 1 := by
      have : (a * b' - a' * b) * π = 1 := by rw [hW]; field_simp
      exact_mod_cast this
    have hM2' : (m : ℂ) ^ 2 = a ^ 2 + b ^ 2 := by exact_mod_cast hM2
    have hπ' : (π : ℂ) ≠ 0 := by exact_mod_cast hπ
    field_simp
    linear_combination (e * a - e * I * b) * hW' + (e * π * (b' + I * a')) * hM2' + (e * a) * I_sq
  have hconst : g x = g 0 := is_const_of_deriv_eq_zero
    (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) x 0
  have hg0 : g 0 = 1 := by
    have hθ0 : airyPhase 0 = π / 6 := by simp [airyPhase]
    simp only [hg, hθ0]
    rw [airyBiReal_zero_eq, show -(I * ((π / 6 : ℝ) : ℂ)) = -(π * I / 6) by push_cast; ring,
      exp_neg_pi_I_div_six]
    have hM0 : airyModulus 0 = 2 * airyAiReal 0 := by
      rw [airyModulus, airyBiReal_zero_eq, mul_pow, Real.sq_sqrt (by norm_num)]
      rw [show airyAiReal 0 ^ 2 + 3 * airyAiReal 0 ^ 2 = (2 * airyAiReal 0) ^ 2 by ring]
      exact Real.sqrt_sq (by linarith [airyAiReal_zero_pos])
    rw [hM0]
    have h0 : (airyAiReal 0 : ℂ) ≠ 0 := by exact_mod_cast airyAiReal_zero_pos.ne'
    have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := sqrt_three_sq
    push_cast
    field_simp
    linear_combination h3 - I_sq
  have hMx : (airyModulus x : ℂ) ≠ 0 := by exact_mod_cast (airyModulus_pos x).ne'
  rw [hg0] at hconst
  simp only [hg] at hconst
  rw [div_eq_one_iff_eq hMx] at hconst
  rw [← hconst, mul_assoc, ← exp_add]
  simp

/-- `Γ(1/3)` is real. -/
theorem Gamma_one_third_eq : Complex.Gamma (1 / 3) = ((Real.Gamma (1 / 3) : ℝ) : ℂ) := by
  rw [show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]

/-- `Bi'(0) = -√3 Ai'(0)`. -/
theorem airyBiDerivReal_zero_eq : airyBiDerivReal 0 = -(Real.sqrt 3 * airyAiDerivReal 0) := by
  have hA := airyAiDeriv_zero
  have hB := airyBiDeriv_zero
  rw [Gamma_one_third_eq] at hA hB
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_div,
    ← Complex.ofReal_neg] at hA hB
  simp only [airyAiDerivReal, airyBiDerivReal, Complex.ofReal_zero, hA, hB, Complex.ofReal_re]
  have h : (3 : ℝ) ^ (1 / 6 : ℝ) * 3 ^ (1 / 3 : ℝ) = Real.sqrt 3 := by
    rw [sqrt_three_eq_rpow, three_rpow_add]; norm_num
  rw [← h]
  have : 0 < (3 : ℝ) ^ (1 / 6 : ℝ) := by positivity
  have : 0 < (3 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)
  field_simp

/-- `Ai'(0) < 0`. -/
theorem airyAiDerivReal_zero_lt : airyAiDerivReal 0 < 0 := by
  have h := airyAiDeriv_zero
  rw [Gamma_one_third_eq] at h
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_div,
    ← Complex.ofReal_neg] at h
  simp only [airyAiDerivReal, Complex.ofReal_zero, h, Complex.ofReal_re]
  have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)
  have : 0 < (3 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

/-- `Bi' + i Ai' = N e^{iφ}` on the whole real axis (DLMF 9.8.5–9.8.6 in complex form). -/
theorem airyBiDeriv_add_I_airyAiDeriv (x : ℝ) :
    (airyBiDerivReal x : ℂ) + I * airyAiDerivReal x =
      airyDerivModulus x * exp (I * airyDerivPhase x) := by
  set g : ℝ → ℂ := fun s => ((airyBiDerivReal s : ℂ) + I * airyAiDerivReal s) *
    exp (-(I * airyDerivPhase s)) / airyDerivModulus s with hg
  have hd : ∀ t, HasDerivAt g 0 t := by
    intro t
    have hE : HasDerivAt (fun s : ℝ => exp (-(I * airyDerivPhase s)))
        (exp (-(I * airyDerivPhase t)) * (-(I * ((t / (π * airyDerivModulus t ^ 2) : ℝ) : ℂ)))) t :=
      (((hasDerivAt_airyDerivPhase t).ofReal_comp.const_mul I).neg).cexp
    have hM := (hasDerivAt_airyDerivModulus t).ofReal_comp
    have hM0 : (airyDerivModulus t : ℂ) ≠ 0 := by exact_mod_cast (airyDerivModulus_pos t).ne'
    have hF : HasDerivAt (fun s : ℝ => (airyBiDerivReal s : ℂ) + I * airyAiDerivReal s)
        (((t * airyBiReal t : ℝ) : ℂ) + I * ((t * airyAiReal t : ℝ) : ℂ)) t :=
      (hasDerivAt_airyBiDerivReal t).ofReal_comp.add
        ((hasDerivAt_airyAiDerivReal t).ofReal_comp.const_mul I)
    have h := (hF.mul hE).div hM hM0
    refine h.congr_deriv ?_
    have hW := wronskian_airyReal t
    have hM2 := airyDerivModulus_sq t
    have hMr := (airyDerivModulus_pos t).ne'
    have hπ := Real.pi_ne_zero
    simp only [Pi.mul_apply]
    rw [div_eq_zero_iff]; left
    generalize exp (-(I * airyDerivPhase t)) = e
    push_cast
    generalize airyAiReal t = a at *
    generalize airyBiReal t = b at *
    generalize airyAiDerivReal t = a' at *
    generalize airyBiDerivReal t = b' at *
    generalize airyDerivModulus t = m at *
    have hW' : ((a : ℂ) * b' - a' * b) * π = 1 := by
      have : (a * b' - a' * b) * π = 1 := by rw [hW]; field_simp
      exact_mod_cast this
    have hM2' : (m : ℂ) ^ 2 = a' ^ 2 + b' ^ 2 := by exact_mod_cast hM2
    have hπ' : (π : ℂ) ≠ 0 := by exact_mod_cast hπ
    have key : ((t : ℂ) * b + I * (t * a)) * m ^ 2 - I * t * (b' + I * a') / π -
        t * (b' + I * a') * (a * a' + b * b') = 0 := by
      field_simp
      linear_combination (t : ℂ) * π * (b + I * a) * hM2' + t * (I * b' - a') * hW' -
        t * a' * I_sq
    linear_combination (norm := skip) (e / m) * key
    field_simp
    ring
  have hconst : g x = g 0 := is_const_of_deriv_eq_zero
    (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) x 0
  have hg0 : g 0 = 1 := by
    have hφ0 : airyDerivPhase 0 = -π / 6 := by simp [airyDerivPhase]
    simp only [hg, hφ0]
    rw [airyBiDerivReal_zero_eq, show -(I * ((-π / 6 : ℝ) : ℂ)) = π * I / 6 by push_cast; ring,
      exp_pi_I_div_six]
    have hM0 : airyDerivModulus 0 = -(2 * airyAiDerivReal 0) := by
      rw [airyDerivModulus, airyBiDerivReal_zero_eq, neg_sq, mul_pow, Real.sq_sqrt (by norm_num)]
      rw [show airyAiDerivReal 0 ^ 2 + 3 * airyAiDerivReal 0 ^ 2 =
        (-(2 * airyAiDerivReal 0)) ^ 2 by ring]
      exact Real.sqrt_sq (by linarith [airyAiDerivReal_zero_lt])
    rw [hM0]
    have h0 : (airyAiDerivReal 0 : ℂ) ≠ 0 := by exact_mod_cast airyAiDerivReal_zero_lt.ne
    have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := sqrt_three_sq
    push_cast
    field_simp
    linear_combination h3 - I_sq
  have hMx : (airyDerivModulus x : ℂ) ≠ 0 := by exact_mod_cast (airyDerivModulus_pos x).ne'
  rw [hg0] at hconst
  simp only [hg] at hconst
  rw [div_eq_one_iff_eq hMx] at hconst
  rw [← hconst, mul_assoc, ← exp_add]
  simp

/-- `Ai = M sin θ` on the whole real axis. -/
theorem airyAiReal_eq_modulus_sin (x : ℝ) : airyAiReal x = airyModulus x * Real.sin (airyPhase x) := by
  have h := congrArg Complex.im (airyBi_add_I_airyAi x)
  rw [show I * (airyPhase x : ℂ) = (airyPhase x : ℂ) * I by ring, exp_mul_I,
] at h
  simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_re] using h

/-- `Bi = M cos θ` on the whole real axis. -/
theorem airyBiReal_eq_modulus_cos (x : ℝ) : airyBiReal x = airyModulus x * Real.cos (airyPhase x) := by
  have h := congrArg Complex.re (airyBi_add_I_airyAi x)
  rw [show I * (airyPhase x : ℂ) = (airyPhase x : ℂ) * I by ring, exp_mul_I,
] at h
  simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_re] using h

/-- `Ai' = N sin φ` on the whole real axis. -/
theorem airyAiDerivReal_eq_modulus_sin (x : ℝ) :
    airyAiDerivReal x = airyDerivModulus x * Real.sin (airyDerivPhase x) := by
  have h := congrArg Complex.im (airyBiDeriv_add_I_airyAiDeriv x)
  rw [show I * (airyDerivPhase x : ℂ) = (airyDerivPhase x : ℂ) * I by ring, exp_mul_I,
] at h
  simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_re] using h

/-- `Bi' = N cos φ` on the whole real axis. -/
theorem airyBiDerivReal_eq_modulus_cos (x : ℝ) :
    airyBiDerivReal x = airyDerivModulus x * Real.cos (airyDerivPhase x) := by
  have h := congrArg Complex.re (airyBiDeriv_add_I_airyAiDeriv x)
  rw [show I * (airyDerivPhase x : ℂ) = (airyDerivPhase x : ℂ) * I by ring, exp_mul_I,
] at h
  simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_re] using h

/-- A real number differs from the arctangent of its tangent by a multiple of `π`,
when its cosine does not vanish. -/
theorem exists_int_eq_arctan_tan {t : ℝ} (h : Real.cos t ≠ 0) :
    ∃ k : ℤ, t = Real.arctan (Real.tan t) + k * π := by
  set k : ℤ := ⌊t / π + 1 / 2⌋ with hk
  have hπ := Real.pi_pos
  have h1 := Int.floor_le (t / π + 1 / 2)
  have h2 := Int.lt_floor_add_one (t / π + 1 / 2)
  rw [← hk] at h1 h2
  have hlo : -(π / 2) ≤ t - k * π := by
    have := mul_le_mul_of_nonneg_right h1 hπ.le
    rw [add_mul, div_mul_cancel₀ _ hπ.ne'] at this; linarith
  have hhi : t - k * π < π / 2 := by
    have := mul_lt_mul_of_pos_right h2 hπ
    rw [add_mul, add_mul, div_mul_cancel₀ _ hπ.ne'] at this; linarith
  have hne : -(π / 2) ≠ t - k * π := by
    intro he
    apply h
    have : t = -(π / 2) + k * π := by linarith
    rw [this, Real.cos_add_int_mul_pi, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  refine ⟨k, ?_⟩
  rw [show Real.tan t = Real.tan (t - k * π) from (Real.tan_periodic.sub_int_mul_eq k).symm,
    Real.arctan_tan (lt_of_le_of_ne hlo hne) hhi]
  ring

/-- `M N sin(θ - φ) = 1/π` on the whole real axis. -/
theorem airy_modulus_phase_wronskian' (x : ℝ) :
    airyModulus x * airyDerivModulus x * Real.sin (airyPhase x - airyDerivPhase x) = 1 / π := by
  rw [Real.sin_sub, ← wronskian_airyReal x, airyAiReal_eq_modulus_sin, airyBiReal_eq_modulus_cos,
    airyAiDerivReal_eq_modulus_sin, airyBiDerivReal_eq_modulus_cos]
  ring

/-- `M N cos(θ - φ) = Ai Ai' + Bi Bi'` on the whole real axis. -/
theorem airy_modulus_phase_cos (x : ℝ) :
    airyModulus x * airyDerivModulus x * Real.cos (airyPhase x - airyDerivPhase x) =
      airyAiReal x * airyAiDerivReal x + airyBiReal x * airyBiDerivReal x := by
  rw [Real.cos_sub, airyAiReal_eq_modulus_sin, airyBiReal_eq_modulus_cos,
    airyAiDerivReal_eq_modulus_sin, airyBiDerivReal_eq_modulus_cos]
  ring

/-- The energy `w'²/(-x) + w²` of a real solution of Airy's equation is monotone on `(-∞, 0)`. -/
theorem airy_energy_monotoneOn {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (t * f t) t) :
    MonotoneOn (fun t => f' t ^ 2 * (-t)⁻¹ + f t ^ 2) (Iio 0) := by
  have hd : ∀ t ∈ Iio (0 : ℝ), HasDerivAt (fun t => f' t ^ 2 * (-t)⁻¹ + f t ^ 2)
      (f' t ^ 2 * (t ^ 2)⁻¹) t := by
    intro t ht
    have ht0 : -t ≠ 0 := by rw [mem_Iio] at ht; linarith
    have h := (((hf' t).pow 2).mul ((hasDerivAt_id t).neg.inv ht0)).add ((hf t).pow 2)
    refine h.congr_deriv ?_
    simp only [Pi.pow_apply, Pi.inv_apply, Pi.neg_apply, id]
    have ht1 : t ≠ 0 := fun h => ht0 (by rw [h, neg_zero])
    field_simp
    ring
  refine monotoneOn_of_deriv_nonneg (convex_Iio 0) (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt) fun t ht => ?_
  rw [interior_Iio] at ht
  rw [(hd t ht).deriv]
  positivity

/-- A uniform bound for `M²` on `(-∞, -1]`. -/
theorem exists_airyModulus_sq_le :
    ∃ C > 0, ∀ x ≤ -1, airyModulus x ^ 2 ≤ C ∧ airyDerivModulus x ^ 2 ≤ -x * C := by
  have hA := airy_energy_monotoneOn hasDerivAt_airyAiReal hasDerivAt_airyAiDerivReal
  have hB := airy_energy_monotoneOn hasDerivAt_airyBiReal hasDerivAt_airyBiDerivReal
  set C := (airyAiDerivReal (-1) ^ 2 * (-(-1 : ℝ))⁻¹ + airyAiReal (-1) ^ 2) +
    (airyBiDerivReal (-1) ^ 2 * (-(-1 : ℝ))⁻¹ + airyBiReal (-1) ^ 2) with hC
  have hC0 : 0 < C := by
    have := airyModulusSq_pos (-1)
    have e : (-(-1 : ℝ))⁻¹ = 1 := by norm_num
    rw [hC, e]
    nlinarith [sq_nonneg (airyAiDerivReal (-1)), sq_nonneg (airyBiDerivReal (-1))]
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hx0 : x ∈ Iio (0 : ℝ) := by rw [mem_Iio]; linarith
  have h1 : (-1 : ℝ) ∈ Iio (0 : ℝ) := by norm_num
  have ha := hA hx0 h1 hx
  have hb := hB hx0 h1 hx
  simp only at ha hb
  have hpos : 0 < -x := by linarith
  have hi : 0 ≤ (-x)⁻¹ := by positivity
  have e1 : 0 ≤ airyAiDerivReal x ^ 2 * (-x)⁻¹ := by positivity
  have e2 : 0 ≤ airyBiDerivReal x ^ 2 * (-x)⁻¹ := by positivity
  constructor
  · rw [airyModulus_sq]; linarith
  · rw [airyDerivModulus_sq]
    have : airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2 =
        -x * (airyAiDerivReal x ^ 2 * (-x)⁻¹ + airyBiDerivReal x ^ 2 * (-x)⁻¹) := by
      rw [← add_mul, mul_comm, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hpos.le
    nlinarith [sq_nonneg (airyAiReal x), sq_nonneg (airyBiReal x)]

/-- The phase `θ` tends to `+∞` at `-∞`. -/
theorem tendsto_airyPhase_atBot : Tendsto airyPhase atBot atTop := by
  obtain ⟨C, hC, hb⟩ := exists_airyModulus_sq_le
  have hπ := Real.pi_pos
  set h : ℝ → ℝ := fun x => airyPhase x + x / (π * C) with hh
  have hanti : AntitoneOn h (Iic (-1)) := by
    have hd : ∀ x, HasDerivAt h (-(1 / (π * airyModulus x ^ 2)) + 1 / (π * C)) x := fun x =>
      (hasDerivAt_airyPhase x).add ((hasDerivAt_id x).div_const _) |>.congr_deriv (by simp)
    refine antitoneOn_of_deriv_nonpos (convex_Iic _) (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Iic, mem_Iio] at hx
    rw [(hd x).deriv]
    have hM := airyModulus_pos x
    have := (hb x hx.le).1
    have : 1 / (π * C) ≤ 1 / (π * airyModulus x ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left this hπ.le)
    linarith
  have hlow : ∀ x ≤ -1, h (-1) - x / (π * C) ≤ airyPhase x := fun x hx => by
    have := hanti (mem_Iic.mpr hx) (mem_Iic.mpr le_rfl) hx
    simp only [hh] at this ⊢; linarith
  refine tendsto_atTop_mono' atBot (eventually_le_atBot (-1) |>.mono fun x hx => hlow x hx) ?_
  refine tendsto_atTop_add_const_left _ _ ?_
  have : Tendsto (fun x : ℝ => -x) atBot atTop := tendsto_neg_atBot_atTop
  have := this.atTop_div_const (show 0 < π * C by positivity)
  refine this.congr fun x => ?_
  ring

/-- The derivative phase `φ` tends to `+∞` at `-∞`. -/
theorem tendsto_airyDerivPhase_atBot : Tendsto airyDerivPhase atBot atTop := by
  obtain ⟨C, hC, hb⟩ := exists_airyModulus_sq_le
  have hπ := Real.pi_pos
  set h : ℝ → ℝ := fun x => airyDerivPhase x + x / (π * C) with hh
  have hanti : AntitoneOn h (Iic (-1)) := by
    have hd : ∀ x, HasDerivAt h (x / (π * airyDerivModulus x ^ 2) + 1 / (π * C)) x := fun x =>
      (hasDerivAt_airyDerivPhase x).add ((hasDerivAt_id x).div_const _) |>.congr_deriv
        (by simp)
    refine antitoneOn_of_deriv_nonpos (convex_Iic _) (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Iic, mem_Iio] at hx
    rw [(hd x).deriv]
    have hN := airyDerivModulus_pos x
    have h2 := (hb x hx.le).2
    have hx0 : 0 < -x := by linarith
    have : x / (π * airyDerivModulus x ^ 2) ≤ -(1 / (π * C)) := by
      rw [div_le_iff₀ (by positivity)]
      have : -(1 / (π * C)) * (π * airyDerivModulus x ^ 2) = -(airyDerivModulus x ^ 2 / C) := by
        field_simp
      rw [this, le_neg, div_le_iff₀ hC]
      linarith
    linarith
  have hlow : ∀ x ≤ -1, h (-1) - x / (π * C) ≤ airyDerivPhase x := fun x hx => by
    have := hanti (mem_Iic.mpr hx) (mem_Iic.mpr le_rfl) hx
    simp only [hh] at this ⊢; linarith
  refine tendsto_atTop_mono' atBot (eventually_le_atBot (-1) |>.mono fun x hx => hlow x hx) ?_
  refine tendsto_atTop_add_const_left _ _ ?_
  have : Tendsto (fun x : ℝ => -x) atBot atTop := tendsto_neg_atBot_atTop
  have := this.atTop_div_const (show 0 < π * C by positivity)
  refine this.congr fun x => ?_
  ring

/-- For `x ≤ 0`, `Ai(x) = M(x) sin θ(x)` (DLMF 9.8.1). -/
@[dlmf 9.8.E1]
theorem airyAiReal_modulus_phase {x : ℝ} :
    airyAiReal x = airyModulus x * Real.sin (airyPhase x) :=
  airyAiReal_eq_modulus_sin x

/-- For `x ≤ 0`, `Bi(x) = M(x) cos θ(x)` (DLMF 9.8.2). -/
@[dlmf 9.8.E2]
theorem airyBiReal_modulus_phase {x : ℝ} :
    airyBiReal x = airyModulus x * Real.cos (airyPhase x) :=
  airyBiReal_eq_modulus_cos x

/-- For `x ≤ 0`, `Ai'(x) = N(x) sin φ(x)` (DLMF 9.8.5). -/
@[dlmf 9.8.E5]
theorem airyAiDerivReal_modulus_phase {x : ℝ} :
    airyAiDerivReal x = airyDerivModulus x * Real.sin (airyDerivPhase x) :=
  airyAiDerivReal_eq_modulus_sin x

/-- For `x ≤ 0`, `Bi'(x) = N(x) cos φ(x)` (DLMF 9.8.6). -/
@[dlmf 9.8.E6]
theorem airyBiDerivReal_modulus_phase {x : ℝ} :
    airyBiDerivReal x = airyDerivModulus x * Real.cos (airyDerivPhase x) :=
  airyBiDerivReal_eq_modulus_cos x

/-- The arctangent formula with its continuous branch retained (DLMF 9.8.4). -/
@[dlmf 9.8.E4]
theorem airyPhase_atan_branch {x : ℝ} (hb : airyBiReal x ≠ 0) :
    ∃ k : ℤ, airyPhase x = Real.arctan (airyAiReal x / airyBiReal x) + k * π := by
  have hc : Real.cos (airyPhase x) ≠ 0 := fun h => hb (by rw [airyBiReal_eq_modulus_cos, h, mul_zero])
  have hM := (airyModulus_pos x).ne'
  rw [airyAiReal_eq_modulus_sin, airyBiReal_eq_modulus_cos, mul_div_mul_left _ _ hM,
    ← Real.tan_eq_sin_div_cos]
  exact exists_int_eq_arctan_tan hc

/-- The phase is continuous, DLMF §9.8(i). -/
theorem airyPhase_continuous :
    Continuous airyPhase := by
  exact continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyPhase x).continuousAt

/-- Phase normalization in DLMF §9.8(i). -/
theorem airyPhase_zero :
    airyPhase 0 = π / 6 := by
  simp [airyPhase]

/-- The arctangent formula with its continuous branch retained (DLMF 9.8.8). -/
@[dlmf 9.8.E8]
theorem airyDerivPhase_atan_branch {x : ℝ} (hb : airyBiDerivReal x ≠ 0) :
    ∃ k : ℤ, airyDerivPhase x = Real.arctan (airyAiDerivReal x / airyBiDerivReal x) + k * π := by
  have hc : Real.cos (airyDerivPhase x) ≠ 0 := fun h =>
    hb (by rw [airyBiDerivReal_eq_modulus_cos, h, mul_zero])
  have hM := (airyDerivModulus_pos x).ne'
  rw [airyAiDerivReal_eq_modulus_sin, airyBiDerivReal_eq_modulus_cos, mul_div_mul_left _ _ hM,
    ← Real.tan_eq_sin_div_cos]
  exact exists_int_eq_arctan_tan hc

/-- The phase is continuous, DLMF §9.8(i). -/
theorem airyDerivPhase_continuous :
    Continuous airyDerivPhase := by
  exact continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyDerivPhase x).continuousAt

/-- Phase normalization in DLMF §9.8(i). -/
theorem airyDerivPhase_zero :
    airyDerivPhase 0 = -π / 6 := by
  simp [airyDerivPhase]

/-- For `x < 0`, `|x|^{1/2} M²(x) = (ζ/2)(J_{1/3}²(ζ) + Y_{1/3}²(ζ))` with
`ζ = (2/3)|x|^{3/2}` (DLMF 9.8.9). -/
@[dlmf 9.8.E9]
theorem airyModulus_bessel {x : ℝ} (hx : x < 0) :
    ((|x| ^ (1 / 2 : ℝ) * airyModulus x ^ 2 : ℝ) : ℂ) =
      airyZeta |x| / 2 * (Complex.besselJ (1 / 3) (airyZeta |x|) ^ 2 +
        DLMF.Bessel.besselY (1 / 3) (airyZeta |x|) ^ 2) := by
  set y := |x| with hy
  have hy0 : 0 < y := abs_pos.mpr hx.ne
  have hxy : x = -y := by rw [hy, abs_of_neg hx]; ring
  have hA := airyAi_neg_eq_besselJ hy0
  have hB := airyBi_neg_eq_besselJ hy0
  rw [show (-(y : ℂ)) = ((-y : ℝ) : ℂ) by push_cast; ring, ← hxy, airyAi_ofReal_eq] at hA
  rw [show (-(y : ℂ)) = ((-y : ℝ) : ℂ) by push_cast; ring, ← hxy, airyBi_ofReal_eq] at hB
  have hY : DLMF.Bessel.besselY (1 / 3) (airyZeta y) =
      (Complex.besselJ (1 / 3) (airyZeta y) * (1 / 2) - Complex.besselJ (-1 / 3) (airyZeta y)) /
        ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
    rw [DLMF.Bessel.besselY_eq_of_not_int third_ne_int, DLMF.Bessel.besselD]
    have hc : Complex.cos (1 / 3 * π) = 1 / 2 := by
      rw [show (1 / 3 * π : ℂ) = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
        Real.cos_pi_div_three]; push_cast; ring
    have hs : Complex.sin (1 / 3 * π) = ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
      rw [show (1 / 3 * π : ℂ) = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin,
        Real.sin_pi_div_three]
    rw [hc, hs, show (-(1 / 3 : ℂ)) = -1 / 3 by ring]
  rw [hY, airyModulus_sq]
  have hz : airyZeta y = 2 / 3 * (Real.sqrt y * y) := by
    rw [airyZeta_eq hy0.le, show Real.sqrt y ^ 3 = Real.sqrt y * (Real.sqrt y * Real.sqrt y) by
      ring, Real.mul_self_sqrt hy0.le]
  have hsq : y ^ (1 / 2 : ℝ) = Real.sqrt y := (Real.sqrt_eq_rpow y).symm
  have h3 : Real.sqrt (y / 3) = Real.sqrt 3 * (Real.sqrt y / 3) := sqrt_div_three hy0.le
  have hs3 := sqrt_three_mul_self
  have hsy := Real.mul_self_sqrt hy0.le
  have hs3' : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by exact_mod_cast hs3
  have hsy' : ((Real.sqrt y : ℝ) : ℂ) * ((Real.sqrt y : ℝ) : ℂ) = y := by exact_mod_cast hsy
  have hr0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  push_cast
  rw [hsq, hA, hB, h3]
  generalize Complex.besselJ (1 / 3) (airyZeta y) = a
  generalize Complex.besselJ (-1 / 3) (airyZeta y) = b
  rw [hz]
  push_cast
  rw [← hsy']
  field_simp
  linear_combination ((Real.sqrt y : ℂ) ^ 3 * ((2 * a * b - 2 * a ^ 2 + b ^ 2) +
    ((Real.sqrt 3 : ℂ) ^ 2 + 3) * (a ^ 2 + b ^ 2 - 2 * a * b))) * hs3'

/-- If `M > 0`, `M cos(ψ - α) = cJ` and `M sin(ψ - α) = cY` with `c, J ≠ 0`, then
`ψ = α + arctan(Y/J)` modulo `π`. -/
private lemma airyMod_eq_add_arctan {M ψ α c J Y : ℝ} (hM : 0 < M) (hc0 : c ≠ 0) (hJ : J ≠ 0)
    (hc : M * Real.cos (ψ - α) = c * J) (hs : M * Real.sin (ψ - α) = c * Y) :
    ∃ k : ℤ, ψ = α + Real.arctan (Y / J) + k * π := by
  have hcos : Real.cos (ψ - α) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hc
    exact mul_ne_zero hc0 hJ hc.symm
  obtain ⟨k, hk⟩ := exists_int_eq_arctan_tan hcos
  refine ⟨k, ?_⟩
  have ht : Real.tan (ψ - α) = Y / J := by
    rw [Real.tan_eq_sin_div_cos, ← mul_div_mul_left _ _ hM.ne', hs, hc,
      mul_div_mul_left _ _ hc0]
  rw [ht] at hk
  linarith

/-- For `x < 0`, `θ(x) = 2π/3 + arctan(Y_{1/3}(ζ)/J_{1/3}(ζ))` modulo `π`, with
`ζ = (2/3)|x|^{3/2}` (DLMF 9.8.11). -/
@[dlmf 9.8.E11]
theorem airyPhase_bessel_atan {x : ℝ} (hx : x < 0)
    (hJ : (Complex.besselJ (1 / 3) (airyZeta |x|)).re ≠ 0) :
    ∃ k : ℤ, airyPhase x = 2 * π / 3 +
      Real.arctan ((DLMF.Bessel.besselY (1 / 3) (airyZeta |x|)).re /
        (Complex.besselJ (1 / 3) (airyZeta |x|)).re) + k * π := by
  set y := |x| with hy
  have hy0 : 0 < y := abs_pos.mpr hx.ne
  have hxy : x = -y := by rw [hy, abs_of_neg hx]; ring
  have hA := airyAi_neg_eq_besselJ hy0
  have hB := airyBi_neg_eq_besselJ hy0
  rw [show (-(y : ℂ)) = ((-y : ℝ) : ℂ) by push_cast; ring, ← hxy, airyAi_ofReal_eq] at hA
  rw [show (-(y : ℂ)) = ((-y : ℝ) : ℂ) by push_cast; ring, ← hxy, airyBi_ofReal_eq] at hB
  have hY : DLMF.Bessel.besselY (1 / 3) (airyZeta y) =
      (Complex.besselJ (1 / 3) (airyZeta y) * (1 / 2) - Complex.besselJ (-1 / 3) (airyZeta y)) /
        ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
    rw [DLMF.Bessel.besselY_eq_of_not_int third_ne_int, DLMF.Bessel.besselD]
    have hc : Complex.cos (1 / 3 * π) = 1 / 2 := by
      rw [show (1 / 3 * π : ℂ) = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
        Real.cos_pi_div_three]; push_cast; ring
    have hs : Complex.sin (1 / 3 * π) = ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
      rw [show (1 / 3 * π : ℂ) = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin,
        Real.sin_pi_div_three]
    rw [hc, hs, show (-(1 / 3 : ℂ)) = -1 / 3 by ring]
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  have hYr : (DLMF.Bessel.besselY (1 / 3) (airyZeta y)).re =
      ((Complex.besselJ (1 / 3) (airyZeta y)).re - 2 * (Complex.besselJ (-1 / 3) (airyZeta y)).re) /
        Real.sqrt 3 := by
    rw [hY, show ((Real.sqrt 3 / 2 : ℝ) : ℂ) = ((Real.sqrt 3 / 2 : ℝ) : ℂ) from rfl,
      Complex.div_ofReal_re]
    simp only [Complex.sub_re, Complex.mul_re]
    norm_num
    field_simp
  have hAr := congrArg Complex.re hA
  have hBr := congrArg Complex.re hB
  simp only [Complex.ofReal_re, Complex.re_ofReal_mul, Complex.add_re, Complex.sub_re] at hAr hBr
  rw [hYr]
  generalize (Complex.besselJ (1 / 3) (airyZeta y)).re = J at *
  generalize (Complex.besselJ (-1 / 3) (airyZeta y)).re = K at *
  have c23 : Real.cos (2 * π / 3) = -1 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have s23 : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have h3 : Real.sqrt (y / 3) = Real.sqrt 3 * (Real.sqrt y / 3) := sqrt_div_three hy0.le
  have h33 := sqrt_three_mul_self
  have hM := airyModulus_pos x
  have hc : airyModulus x * Real.cos (airyPhase x - 2 * π / 3) = Real.sqrt y * J / Real.sqrt 3 := by
    rw [Real.cos_sub, c23, s23, mul_add, ← mul_assoc, ← mul_assoc, ← airyBiReal_eq_modulus_cos,
      ← airyAiReal_eq_modulus_sin, hAr, hBr, h3]
    field_simp
    linear_combination (2 * J) * h33
  have hs : airyModulus x * Real.sin (airyPhase x - 2 * π / 3) =
      Real.sqrt y * ((J - 2 * K) / Real.sqrt 3) / Real.sqrt 3 := by
    rw [Real.sin_sub, c23, s23, mul_sub, ← mul_assoc, ← mul_assoc, ← airyBiReal_eq_modulus_cos,
      ← airyAiReal_eq_modulus_sin, hAr, hBr, h3]
    field_simp
    linear_combination ((J - K) * (Real.sqrt 3 ^ 2 + 3) - (J + K)) * h33
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  exact airyMod_eq_add_arctan (c := Real.sqrt y / Real.sqrt 3) hM (div_ne_zero hsy.ne' hs3) hJ
    (by rw [hc]; ring) (by rw [hs]; ring)

/-- On the positive real axis the log-plane `J` is the principal `J` at `ζ = (2/3)x^{3/2}`. -/
theorem airyBesselJOnLog_airyLogZeta_ofReal (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    airyBesselJOnLog ν (airyLogZeta x) = Complex.besselJ ν (airyZeta x) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [airyBesselJOnLog_airyLogZeta ν hx0, DLMF.Bessel.besselJ_eq_regularized,
    airyZeta_sq_div_four hx.le]
  congr 1
  have hz : 0 < airyZeta x / 2 := by have := airyZeta_pos hx; positivity
  rw [show ((airyZeta x : ℝ) : ℂ) / 2 = ((airyZeta x / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hz.ne'), ← Complex.ofReal_log hz.le,
    ← Complex.exp_add]
  congr 1
  have hl : Real.log (airyZeta x / 2) = 3 / 2 * Real.log x - Real.log 3 := by
    rw [airyZeta, show 2 / 3 * x ^ (3 / 2 : ℝ) / 2 = x ^ (3 / 2 : ℝ) / 3 by ring,
      Real.log_div (by positivity) (by norm_num), Real.log_rpow hx]
  rw [hl, ← Complex.ofReal_log hx.le]
  push_cast
  rw [← Complex.ofReal_ofNat 3, ← Complex.ofReal_log (by norm_num)]
  ring

/-- `Ai'(-x) = (x/3)(J_{2/3}(ζ) - J_{-2/3}(ζ))` for `x > 0` (DLMF 9.6.7). -/
theorem airyAiDeriv_neg_eq_besselJ_real {x : ℝ} (hx : 0 < x) :
    airyAiDeriv (-x) = (x / 3 : ℂ) *
      (Complex.besselJ (2 / 3) (airyZeta x) - Complex.besselJ (-2 / 3) (airyZeta x)) := by
  rw [airyAiDeriv_neg_eq_besselJ_complex (by exact_mod_cast hx.ne'),
    airyBesselJOnLog_airyLogZeta_ofReal _ hx, airyBesselJOnLog_airyLogZeta_ofReal _ hx]

/-- `Bi'(-x) = (x/√3)(J_{-2/3}(ζ) + J_{2/3}(ζ))` for `x > 0` (DLMF 9.6.9). -/
theorem airyBiDeriv_neg_eq_besselJ_real {x : ℝ} (hx : 0 < x) :
    airyBiDeriv (-x) = (x / Real.sqrt 3 : ℂ) *
      (Complex.besselJ (-2 / 3) (airyZeta x) + Complex.besselJ (2 / 3) (airyZeta x)) := by
  rw [airyBiDeriv_neg_eq_besselJ_complex (by exact_mod_cast hx.ne'),
    airyBesselJOnLog_airyLogZeta_ofReal _ hx, airyBesselJOnLog_airyLogZeta_ofReal _ hx,
    show (-(2 / 3 : ℂ)) = -2 / 3 by ring]

/-- `2/3` is not an integer. -/
theorem two_thirds_ne_int : ∀ k : ℤ, (2 / 3 : ℂ) ≠ k := by
  intro k hk
  have h := congrArg Complex.re hk
  norm_num [Complex.div_re, Complex.normSq] at h
  have h3 : ((3 * k : ℤ) : ℝ) = 2 := by push_cast; linarith
  have : 3 * k = 2 := by exact_mod_cast h3
  omega

/-- `Y_{2/3} = (-J_{2/3}/2 - J_{-2/3})/(√3/2)`. -/
theorem besselY_two_thirds_eq (z : ℂ) :
    DLMF.Bessel.besselY (2 / 3) z =
      (Complex.besselJ (2 / 3) z * (-1 / 2) - Complex.besselJ (-2 / 3) z) /
        ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
  rw [DLMF.Bessel.besselY_eq_of_not_int two_thirds_ne_int, DLMF.Bessel.besselD]
  have hc : Complex.cos (2 / 3 * π) = -1 / 2 := by
    rw [mul_comm]; exact cos_pi_mul_two_thirds
  have hs : Complex.sin (2 / 3 * π) = ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
    rw [mul_comm]; exact sin_pi_mul_two_thirds
  rw [hc, hs, show (-(2 / 3 : ℂ)) = -2 / 3 by ring]

/-- For `x < 0`, `|x|^{-1/2} N²(x) = (ζ/2)(J_{2/3}²(ζ) + Y_{2/3}²(ζ))` with
`ζ = (2/3)|x|^{3/2}` (DLMF 9.8.10). -/
@[dlmf 9.8.E10]
theorem airyDerivModulus_bessel {x : ℝ} (hx : x < 0) :
    ((|x| ^ (-1 / 2 : ℝ) * airyDerivModulus x ^ 2 : ℝ) : ℂ) =
      airyZeta |x| / 2 * (Complex.besselJ (2 / 3) (airyZeta |x|) ^ 2 +
        DLMF.Bessel.besselY (2 / 3) (airyZeta |x|) ^ 2) := by
  set y := |x| with hy
  have hy0 : 0 < y := abs_pos.mpr hx.ne
  have hxy : x = -y := by rw [hy, abs_of_neg hx]; ring
  have hA := airyAiDeriv_neg_eq_besselJ_real hy0
  have hB := airyBiDeriv_neg_eq_besselJ_real hy0
  rw [show (-(y : ℂ)) = ((-y : ℝ) : ℂ) by push_cast; ring, ← hxy, airyAiDeriv_ofReal_eq] at hA
  rw [show (-(y : ℂ)) = ((-y : ℝ) : ℂ) by push_cast; ring, ← hxy, airyBiDeriv_ofReal_eq] at hB
  rw [besselY_two_thirds_eq, airyDerivModulus_sq]
  have hz : airyZeta y = 2 / 3 * (Real.sqrt y * y) := by
    rw [airyZeta_eq hy0.le, show Real.sqrt y ^ 3 = Real.sqrt y * (Real.sqrt y * Real.sqrt y) by
      ring, Real.mul_self_sqrt hy0.le]
  have hsq : y ^ (-1 / 2 : ℝ) = (Real.sqrt y)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hy0.le, Real.sqrt_eq_rpow]
  have hs3' : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    exact_mod_cast sqrt_three_mul_self
  have hsy' : ((Real.sqrt y : ℝ) : ℂ) * ((Real.sqrt y : ℝ) : ℂ) = y := by
    exact_mod_cast Real.mul_self_sqrt hy0.le
  have hr0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hry : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hy0).ne'
  push_cast
  rw [hsq, hA, hB]
  generalize Complex.besselJ (2 / 3) (airyZeta y) = a
  generalize Complex.besselJ (-2 / 3) (airyZeta y) = b
  rw [hz]
  push_cast
  rw [← hsy']
  field_simp
  linear_combination (-2 * a * b - 2 * a ^ 2 + b ^ 2) * hs3'

/-- For `x < 0`, `φ(x) = π/3 + arctan(Y_{2/3}(ζ)/J_{2/3}(ζ))` modulo `π`, with
`ζ = (2/3)|x|^{3/2}` (DLMF 9.8.12). -/
@[dlmf 9.8.E12]
theorem airyDerivPhase_bessel_atan {x : ℝ} (hx : x < 0)
    (hJ : (Complex.besselJ (2 / 3) (airyZeta |x|)).re ≠ 0) :
    ∃ k : ℤ, airyDerivPhase x = 1 * π / 3 +
      Real.arctan ((DLMF.Bessel.besselY (2 / 3) (airyZeta |x|)).re /
        (Complex.besselJ (2 / 3) (airyZeta |x|)).re) + k * π := by
  set y := |x| with hy
  have hy0 : 0 < y := abs_pos.mpr hx.ne
  have hxy : x = -y := by rw [hy, abs_of_neg hx]; ring
  have hA := airyAiDeriv_neg_eq_besselJ_real hy0
  have hB := airyBiDeriv_neg_eq_besselJ_real hy0
  rw [show (-(y : ℂ)) = ((-y : ℝ) : ℂ) by push_cast; ring, ← hxy, airyAiDeriv_ofReal_eq] at hA
  rw [show (-(y : ℂ)) = ((-y : ℝ) : ℂ) by push_cast; ring, ← hxy, airyBiDeriv_ofReal_eq] at hB
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  have hYr : (DLMF.Bessel.besselY (2 / 3) (airyZeta y)).re =
      -((Complex.besselJ (2 / 3) (airyZeta y)).re + 2 * (Complex.besselJ (-2 / 3) (airyZeta y)).re) /
        Real.sqrt 3 := by
    rw [besselY_two_thirds_eq, Complex.div_ofReal_re]
    simp only [Complex.sub_re, Complex.mul_re]
    norm_num
    field_simp
    ring
  have hAr := congrArg Complex.re hA
  have hBr := congrArg Complex.re hB
  rw [show ((y : ℂ) / 3) = ((y / 3 : ℝ) : ℂ) by push_cast; ring] at hAr
  rw [show ((y : ℂ) / (Real.sqrt 3 : ℂ)) = ((y / Real.sqrt 3 : ℝ) : ℂ) by push_cast; ring] at hBr
  simp only [Complex.ofReal_re, Complex.re_ofReal_mul, Complex.add_re, Complex.sub_re] at hAr hBr
  rw [hYr]
  generalize (Complex.besselJ (2 / 3) (airyZeta y)).re = J at *
  generalize (Complex.besselJ (-2 / 3) (airyZeta y)).re = K at *
  have hM := airyDerivModulus_pos x
  have h33 := sqrt_three_mul_self
  have hc : airyDerivModulus x * Real.cos (airyDerivPhase x - 1 * π / 3) = y * J / Real.sqrt 3 := by
    rw [one_mul, Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three, mul_add, ← mul_assoc,
      ← mul_assoc, ← airyBiDerivReal_eq_modulus_cos, ← airyAiDerivReal_eq_modulus_sin, hAr, hBr]
    field_simp
    linear_combination (J - K) * h33
  have hs : airyDerivModulus x * Real.sin (airyDerivPhase x - 1 * π / 3) =
      y * (-(J + 2 * K) / Real.sqrt 3) / Real.sqrt 3 := by
    rw [one_mul, Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three, mul_sub, ← mul_assoc,
      ← mul_assoc, ← airyBiDerivReal_eq_modulus_cos, ← airyAiDerivReal_eq_modulus_sin, hAr, hBr]
    field_simp
    linear_combination (-2 * J - 4 * K) * h33
  exact airyMod_eq_add_arctan (c := y / Real.sqrt 3) hM (div_ne_zero hy0.ne' hs3) hJ
    (by rw [hc]; ring) (by rw [hs]; ring)

/-- Wronskian in modulus–phase form: `M N sin(θ - φ) = 1/π` (DLMF 9.8.13). -/
@[dlmf 9.8.E13]
theorem airy_modulus_phase_wronskian {x : ℝ} (hx : x ≤ 0) :
    airyModulus x * airyDerivModulus x * Real.sin (airyPhase x - airyDerivPhase x) = 1 / π :=
  airy_modulus_phase_wronskian' x

/-- `M² θ' = -1/π`, `N² φ' = x/π` and `N N' = x M M'` (DLMF 9.8.14). -/
@[dlmf 9.8.E14]
theorem airy_modulus_phase_derivatives {x : ℝ} :
    airyModulus x ^ 2 * deriv airyPhase x = -1 / π ∧
      airyDerivModulus x ^ 2 * deriv airyDerivPhase x = x / π ∧
      airyDerivModulus x * deriv airyDerivModulus x = x * airyModulus x * deriv airyModulus x := by
  have hM := (airyModulus_pos x).ne'
  have hN := (airyDerivModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  rw [deriv_airyPhase, deriv_airyDerivPhase, deriv_airyDerivModulus, deriv_airyModulus]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

/-- `N² = M'² + M² θ'² = M'² + 1/(π² M²)` (DLMF 9.8.15). -/
@[dlmf 9.8.E15]
theorem airy_derivModulus_identity {x : ℝ} :
    airyDerivModulus x ^ 2 = deriv airyModulus x ^ 2 + airyModulus x ^ 2 * deriv airyPhase x ^ 2 ∧
      airyDerivModulus x ^ 2 = deriv airyModulus x ^ 2 + 1 / (π ^ 2 * airyModulus x ^ 2) := by
  have hM := (airyModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  have hL := airy_lagrange x
  rw [deriv_airyPhase, deriv_airyModulus]
  simp only
  rw [div_pow, ← airyModulus_sq, ← airyDerivModulus_sq] at *
  refine ⟨?_, ?_⟩
  · field_simp
    linear_combination hL
  · field_simp
    linear_combination hL

/-- `x² M² = N'² + N² φ'² = N'² + x²/(π² N²)` (DLMF 9.8.16). -/
@[dlmf 9.8.E16]
theorem airy_modulus_identity {x : ℝ} :
    x ^ 2 * airyModulus x ^ 2 = deriv airyDerivModulus x ^ 2 + airyDerivModulus x ^ 2 * deriv airyDerivPhase x ^ 2 ∧
      x ^ 2 * airyModulus x ^ 2 = deriv airyDerivModulus x ^ 2 + x ^ 2 / (π ^ 2 * airyDerivModulus x ^ 2) := by
  have hN := (airyDerivModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  have hL := airy_lagrange x
  rw [deriv_airyDerivPhase, deriv_airyDerivModulus]
  simp only
  rw [div_pow, ← airyModulus_sq, ← airyDerivModulus_sq] at *
  refine ⟨?_, ?_⟩
  · field_simp
    linear_combination x ^ 2 * hL
  · field_simp
    linear_combination x ^ 2 * hL

/-- `tan(θ - φ) = 1/(π M M') = -M θ'/M'` (DLMF 9.8.17). -/
@[dlmf 9.8.E17]
theorem airy_phase_difference_tan {x : ℝ} :
    Real.tan (airyPhase x - airyDerivPhase x) = 1 / (π * airyModulus x * deriv airyModulus x) ∧
      Real.tan (airyPhase x - airyDerivPhase x) = -airyModulus x * deriv airyPhase x / deriv airyModulus x := by
  have hM := (airyModulus_pos x).ne'
  have hN := (airyDerivModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  have hs := airy_modulus_phase_wronskian' x
  have hc := airy_modulus_phase_cos x
  rw [deriv_airyPhase, deriv_airyModulus, Real.tan_eq_sin_div_cos]
  simp only
  set S := airyAiReal x * airyAiDerivReal x + airyBiReal x * airyBiDerivReal x
  have hsin : Real.sin (airyPhase x - airyDerivPhase x) =
      1 / (π * (airyModulus x * airyDerivModulus x)) := by
    rw [eq_div_iff (mul_ne_zero hπ (mul_ne_zero hM hN)),
      show Real.sin (airyPhase x - airyDerivPhase x) * (π * (airyModulus x * airyDerivModulus x)) =
        (airyModulus x * airyDerivModulus x * Real.sin (airyPhase x - airyDerivPhase x)) * π by ring,
      hs, one_div, inv_mul_cancel₀ hπ]
  have hcos : Real.cos (airyPhase x - airyDerivPhase x) = S / (airyModulus x * airyDerivModulus x) := by
    rw [eq_div_iff (mul_ne_zero hM hN), ← hc]; ring
  rw [hsin, hcos]
  by_cases hS : S = 0
  · simp [hS]
  · constructor <;> field_simp

/-- The modulus satisfies `M'' = x M + 1/(π² M³)`, and `M²` satisfies
`w''' - 4x w' - 2w = 0` (DLMF 9.8.18). -/
@[dlmf 9.8.E18]
theorem airy_modulus_ode {x : ℝ} :
    deriv (deriv airyModulus) x = x * airyModulus x + 1 / (π ^ 2 * airyModulus x ^ 3) ∧
      iteratedDeriv 3 (fun t => airyModulus t ^ 2) x -
        4 * x * deriv (fun t => airyModulus t ^ 2) x - 2 * airyModulus x ^ 2 = 0 := by
  constructor
  · rw [deriv_airyModulus]
    have hM := (airyModulus_pos x).ne'
    have h : HasDerivAt (fun t => (airyAiReal t * airyAiDerivReal t +
        airyBiReal t * airyBiDerivReal t) / airyModulus t) _ x :=
      (hasDerivAt_airyCross x).div (hasDerivAt_airyModulus x) hM
    rw [h.deriv]
    have hπ := Real.pi_ne_zero
    have hL := airy_lagrange x
    have hM2 := airyModulus_sq x
    field_simp
    linear_combination hL + ((airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2) * π ^ 2 -
      x * airyModulus x ^ 2 * π ^ 2) * hM2
  · have d1 : deriv (fun t => airyModulus t ^ 2) = fun t =>
        2 * (airyAiReal t * airyAiDerivReal t + airyBiReal t * airyBiDerivReal t) := by
      rw [airyModulus_sq_fun]
      funext t
      exact (((hasDerivAt_airyAiReal t).pow 2).add ((hasDerivAt_airyBiReal t).pow 2)).deriv.trans
        (by simp; ring)
    have d2 : deriv (fun t => 2 * (airyAiReal t * airyAiDerivReal t +
        airyBiReal t * airyBiDerivReal t)) = fun t => 2 * (airyAiDerivReal t ^ 2 +
          airyBiDerivReal t ^ 2 + t * (airyAiReal t ^ 2 + airyBiReal t ^ 2)) :=
      funext fun t => ((hasDerivAt_airyCross t).const_mul 2).deriv
    have d3 : HasDerivAt (fun t => 2 * (airyAiDerivReal t ^ 2 + airyBiDerivReal t ^ 2 +
          t * (airyAiReal t ^ 2 + airyBiReal t ^ 2)))
        (2 * (2 * airyAiDerivReal x * (x * airyAiReal x) + 2 * airyBiDerivReal x * (x * airyBiReal x) +
          ((airyAiReal x ^ 2 + airyBiReal x ^ 2) + x * (2 * (airyAiReal x * airyAiDerivReal x +
            airyBiReal x * airyBiDerivReal x))))) x := by
      have h := (((((hasDerivAt_airyAiDerivReal x).pow 2).add
        ((hasDerivAt_airyBiDerivReal x).pow 2)).add ((hasDerivAt_id x).mul
          (((hasDerivAt_airyAiReal x).pow 2).add ((hasDerivAt_airyBiReal x).pow 2)))).const_mul 2)
      exact h.congr_deriv (by simp only [Pi.add_apply, Pi.pow_apply, id]; push_cast; ring)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [d1, d2, d3.deriv, airyModulus_sq]
    ring

/-- The phase satisfies `θ'² + θ'''/(2θ') - (3/4)(θ''/θ')² = -x` (DLMF 9.8.19). -/
@[dlmf 9.8.E19]
theorem airy_phase_ode {x : ℝ} :
    deriv airyPhase x ^ 2 + iteratedDeriv 3 airyPhase x / (2 * deriv airyPhase x) -
      3 / 4 * (iteratedDeriv 2 airyPhase x / deriv airyPhase x) ^ 2 = -x := by
  set p : ℝ → ℝ := fun t => airyAiReal t ^ 2 + airyBiReal t ^ 2 with hp
  set S : ℝ → ℝ := fun t => airyAiReal t * airyAiDerivReal t + airyBiReal t * airyBiDerivReal t
    with hS
  have hp' : ∀ t, HasDerivAt p (2 * S t) t := fun t =>
    (((hasDerivAt_airyAiReal t).pow 2).add ((hasDerivAt_airyBiReal t).pow 2)).congr_deriv
      (by simp only [hS]; push_cast; ring)
  have hS' : ∀ t, HasDerivAt S (airyAiDerivReal t ^ 2 + airyBiDerivReal t ^ 2 + t * p t) t :=
    hasDerivAt_airyCross
  have hpos : ∀ t, π * p t ≠ 0 := fun t => by
    have := airyModulusSq_pos t; have := Real.pi_pos; simp only [hp]; positivity
  have d1 : deriv airyPhase = fun t => -(π * p t)⁻¹ := by
    rw [deriv_airyPhase]; funext t; rw [airyModulus_sq, one_div]
  have h2 : ∀ t, HasDerivAt (fun t => -(π * p t)⁻¹) (2 * π * S t / (π * p t) ^ 2) t := fun t =>
    (((hp' t).const_mul π).inv (hpos t)).neg.congr_deriv (by ring)
  have d2 : deriv (fun t => -(π * p t)⁻¹) = fun t => 2 * π * S t / (π * p t) ^ 2 :=
    funext fun t => (h2 t).deriv
  have h3 := (((hS' x).const_mul (2 * π)).div (((hp' x).const_mul π).pow 2)
    (pow_ne_zero 2 (hpos x)))
  have h3' : HasDerivAt (fun t => 2 * π * S t / (π * p t) ^ 2) _ x := h3
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [d1, d2, h3'.deriv]
  have hL := airy_lagrange x
  have hπ := Real.pi_ne_zero
  have hp0 := airyModulusSq_pos x
  simp only [hp, hS, Pi.pow_apply] at hL ⊢
  generalize airyAiReal x = a at *
  generalize airyBiReal x = b at *
  generalize airyAiDerivReal x = a' at *
  generalize airyBiDerivReal x = b' at *
  push_cast
  field_simp
  linear_combination (-4 : ℝ) * hL

end DLMF.Airy
end
