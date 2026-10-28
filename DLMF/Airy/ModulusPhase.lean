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
# Airy modulus and continuous phase, DLMF §9.8

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
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
theorem airyAiReal_modulus_phase {x : ℝ} (hx : x ≤ 0) :
    airyAiReal x = airyModulus x * Real.sin (airyPhase x) :=
  airyAiReal_eq_modulus_sin x

/-- For `x ≤ 0`, `Bi(x) = M(x) cos θ(x)` (DLMF 9.8.2). -/
@[dlmf 9.8.E2]
theorem airyBiReal_modulus_phase {x : ℝ} (hx : x ≤ 0) :
    airyBiReal x = airyModulus x * Real.cos (airyPhase x) :=
  airyBiReal_eq_modulus_cos x

/-- For `x ≤ 0`, `Ai'(x) = N(x) sin φ(x)` (DLMF 9.8.5). -/
@[dlmf 9.8.E5]
theorem airyAiDerivReal_modulus_phase {x : ℝ} (hx : x ≤ 0) :
    airyAiDerivReal x = airyDerivModulus x * Real.sin (airyDerivPhase x) :=
  airyAiDerivReal_eq_modulus_sin x

/-- For `x ≤ 0`, `Bi'(x) = N(x) cos φ(x)` (DLMF 9.8.6). -/
@[dlmf 9.8.E6]
theorem airyBiDerivReal_modulus_phase {x : ℝ} (hx : x ≤ 0) :
    airyBiDerivReal x = airyDerivModulus x * Real.cos (airyDerivPhase x) :=
  airyBiDerivReal_eq_modulus_cos x

/-- The arctangent formula with its continuous branch retained (DLMF 9.8.4). -/
@[dlmf 9.8.E4]
theorem airyPhase_atan_branch {x : ℝ} (hx : x ≤ 0) (hb : airyBiReal x ≠ 0) :
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
theorem airyDerivPhase_atan_branch {x : ℝ} (hx : x ≤ 0) (hb : airyBiDerivReal x ≠ 0) :
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
theorem airy_modulus_phase_derivatives {x : ℝ} (hx : x ≤ 0) :
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
theorem airy_derivModulus_identity {x : ℝ} (hx : x ≤ 0) :
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
theorem airy_modulus_identity {x : ℝ} (hx : x ≤ 0) :
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
theorem airy_phase_difference_tan {x : ℝ} (hx : x ≤ 0) :
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
theorem airy_modulus_ode {x : ℝ} (hx : x ≤ 0) :
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
theorem airy_phase_ode {x : ℝ} (hx : x ≤ 0) :
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

/-! ### Nicholson's formula on the real line and its consequences -/

section Nicholson

open scoped Nat

/-- The real Nicholson kernel `e^{xt} e^{-t³/12} t^{-1/2}`. -/
noncomputable def airyMod_kernel (x t : ℝ) : ℝ :=
  Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ))

/-- The real Nicholson kernel is positive on `(0, ∞)`. -/
theorem airyMod_kernel_pos (x : ℝ) {t : ℝ} (ht : 0 < t) : 0 < airyMod_kernel x t := by
  unfold airyMod_kernel; positivity

/-- **Nicholson's formula on the real line** (DLMF 9.11.4):
`M(x)² = π^{-3/2} ∫₀^∞ e^{xt - t³/12} t^{-1/2} dt`. -/
theorem airyMod_sq_eq_integral (x : ℝ) :
    airyModulus x ^ 2 = (∫ t in Ioi (0 : ℝ), airyMod_kernel x t) / (π * Real.sqrt π) := by
  have h := (airyMod_modulus_sq_exp_integral x).2
  rw [airyAi_ofReal_eq, airyBi_ofReal_eq, airyMod_pi_cpow] at h
  have hI : (∫ t : ℝ in Ioi 0, exp ((x : ℂ) * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) =
      ((∫ t in Ioi (0 : ℝ), airyMod_kernel x t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [airyMod_kernel]
    rw [ofReal_mul, ofReal_mul, ofReal_exp, ofReal_exp, ofReal_cpow ht.le]
    push_cast
    rw [sub_eq_add_neg, Complex.exp_add, show (-(1 / 2) : ℂ) = -1 / 2 by ring]; ring
  rw [hI] at h
  rw [airyModulus_sq]
  exact_mod_cast h

/-- The real Nicholson kernel is integrable on `(0, ∞)`. -/
theorem airyMod_kernel_integrable (x : ℝ) : IntegrableOn (airyMod_kernel x) (Ioi 0) :=
  airyMod_integrableOn_exp x

/-- A function positive on `(0, ∞)` and integrable there has positive integral. -/
theorem airyMod_integral_pos {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (hpos : ∀ t, 0 < t → 0 < f t) : 0 < ∫ t in Ioi (0 : ℝ), f t := by
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hf).2 ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    exact (hpos t ht).le
  · have : Ioi (0 : ℝ) ⊆ Function.support f ∩ Ioi 0 := fun t (ht : 0 < t) =>
      ⟨(hpos t ht).ne', ht⟩
    refine lt_of_lt_of_le ?_ (measure_mono this)
    rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top

/-- `M²` is strictly increasing on the whole real line. -/
theorem airyMod_sq_strictMono : StrictMono fun x => airyModulus x ^ 2 := by
  intro x y hxy
  simp only [airyMod_sq_eq_integral]
  have hπ : 0 < π * Real.sqrt π := by positivity
  refine div_lt_div_of_pos_right ?_ hπ
  rw [← sub_pos, ← integral_sub (airyMod_kernel_integrable y) (airyMod_kernel_integrable x)]
  refine airyMod_integral_pos ((airyMod_kernel_integrable y).sub (airyMod_kernel_integrable x))
    fun t ht => ?_
  simp only [airyMod_kernel]
  have h1 : Real.exp (x * t) < Real.exp (y * t) := Real.exp_lt_exp.2 (by nlinarith)
  have h2 : 0 < Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ) := by positivity
  nlinarith

/-- Scaling form of Nicholson's formula: for `s > 0`,
`s^{1/2} M(-s)² = π^{-3/2} ∫₀^∞ e^{-u} e^{-u³/(12 s³)} u^{-1/2} du`. -/
theorem airyMod_sqrt_mul_sq {s : ℝ} (hs : 0 < s) :
    s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2 = (∫ u in Ioi (0 : ℝ),
      Real.exp (-u) * (Real.exp (-(u ^ 3 / (12 * s ^ 3))) * u ^ (-(1 / 2) : ℝ))) /
        (π * Real.sqrt π) := by
  rw [airyMod_sq_eq_integral, mul_div_assoc']
  congr 1
  have h := integral_comp_mul_left_Ioi (airyMod_kernel (-s)) 0 (inv_pos.mpr hs)
  rw [mul_zero, smul_eq_mul, inv_inv] at h
  have hs12 : 0 < s ^ (1 / 2 : ℝ) := by positivity
  have key : ∀ u ∈ Ioi (0 : ℝ), airyMod_kernel (-s) (s⁻¹ * u) = s ^ (1 / 2 : ℝ) *
      (Real.exp (-u) * (Real.exp (-(u ^ 3 / (12 * s ^ 3))) * u ^ (-(1 / 2) : ℝ))) := by
    intro u (hu : 0 < u)
    simp only [airyMod_kernel]
    rw [Real.mul_rpow (inv_pos.mpr hs).le hu.le, Real.inv_rpow hs.le, Real.rpow_neg hs.le,
      inv_inv]
    have : -s * (s⁻¹ * u) = -u := by field_simp
    rw [this, mul_pow, inv_pow]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul] at h
  have hs0 : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by
    rw [← Real.rpow_add hs]; norm_num
  apply mul_left_cancel₀ hs12.ne'
  rw [← mul_assoc, hs0, h]

/-- The scaled Nicholson integrand is integrable. -/
theorem airyMod_scaled_integrable {s : ℝ} (hs : 0 ≤ s) : IntegrableOn (fun u : ℝ =>
    Real.exp (-u) * (Real.exp (-(u ^ 3 / (12 * s ^ 3))) * u ^ (-(1 / 2) : ℝ))) (Ioi 0) := by
  have hint := Real.GammaIntegral_convergent (s := 1 / 2) (by norm_num)
  refine hint.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact ((Real.continuous_exp.comp continuous_neg).continuousAt.mul
      ((Real.continuous_exp.comp (by fun_prop)).continuousAt.mul
        (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [Real.norm_of_nonneg (by positivity), show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
    have : Real.exp (-(t ^ 3 / (12 * s ^ 3))) ≤ 1 := Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (by positivity))
    have h0 : 0 ≤ t ^ (-(1 / 2) : ℝ) := by positivity
    have h1 : 0 < Real.exp (-t) := Real.exp_pos _
    calc Real.exp (-t) * (Real.exp (-(t ^ 3 / (12 * s ^ 3))) * t ^ (-(1 / 2) : ℝ))
        ≤ Real.exp (-t) * (1 * t ^ (-(1 / 2) : ℝ)) := by gcongr
      _ = _ := by ring

/-- The remainder of the exponential series for `e^{-w}` after `K` terms. -/
noncomputable def airyMod_rem (K : ℕ) (w : ℝ) : ℝ :=
  Real.exp (-w) - ∑ k ∈ Finset.range K, (-w) ^ k / k !

/-- Derivative of the partial sums of `e^{-w}`. -/
theorem airyMod_hasDerivAt_partial (K : ℕ) (w : ℝ) :
    HasDerivAt (fun w : ℝ => ∑ k ∈ Finset.range (K + 1), (-w) ^ k / k !)
      (-∑ k ∈ Finset.range K, (-w) ^ k / k !) w := by
  induction K with
  | zero => simpa using hasDerivAt_const w (1 : ℝ)
  | succ K ih =>
    have h := ih.add (((hasDerivAt_neg w).pow (K + 1)).div_const ((K + 1) ! : ℝ))
    simp only [Finset.sum_range_succ] at h ⊢
    convert h using 1
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- Derivative of the exponential remainder: `R_{K+1}' = -R_K`. -/
theorem airyMod_hasDerivAt_rem (K : ℕ) (w : ℝ) :
    HasDerivAt (airyMod_rem (K + 1)) (-airyMod_rem K w) w := by
  have h := ((Real.hasDerivAt_exp (-w)).comp w (hasDerivAt_neg w)).sub
    (airyMod_hasDerivAt_partial K w)
  unfold airyMod_rem
  exact h.congr_deriv (by ring)

/-- `R_{K+1}(0) = 0`. -/
theorem airyMod_rem_zero (K : ℕ) : airyMod_rem (K + 1) 0 = 0 := by
  simp [airyMod_rem, Finset.sum_range_succ']

/-- The alternating bound for the exponential remainder: for `w ≥ 0`,
`0 ≤ (-1)^K R_K(w) ≤ w^K / K!`. -/
theorem airyMod_rem_bounds (K : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ (-1) ^ K * airyMod_rem K w ∧ (-1) ^ K * airyMod_rem K w ≤ w ^ K / K ! := by
  induction K generalizing w with
  | zero =>
    simp only [pow_zero, one_mul, airyMod_rem, Finset.range_zero, Finset.sum_empty, sub_zero,
      Nat.factorial_zero, Nat.cast_one, div_one]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  | succ K ih =>
    have hg : ∀ v : ℝ, HasDerivAt (fun v => (-1) ^ (K + 1) * airyMod_rem (K + 1) v)
        ((-1) ^ K * airyMod_rem K v) v := fun v => by
      convert (airyMod_hasDerivAt_rem K v).const_mul ((-1 : ℝ) ^ (K + 1)) using 1; ring
    have hh : ∀ v : ℝ, HasDerivAt (fun v => v ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) -
        (-1) ^ (K + 1) * airyMod_rem (K + 1) v) (v ^ K / (Nat.factorial K : ℝ) - (-1) ^ K * airyMod_rem K v) v :=
      fun v => by
        convert ((hasDerivAt_pow (K + 1) v).div_const (Nat.factorial (K + 1) : ℝ)).sub (hg v)
          using 1
        rw [Nat.factorial_succ]; push_cast; field_simp
    have mono : ∀ {f f' : ℝ → ℝ}, (∀ v, HasDerivAt f (f' v) v) → (∀ v, 0 ≤ v → 0 ≤ f' v) →
        f 0 ≤ f w := by
      intro f f' hf hf'
      have hm : MonotoneOn f (Ici 0) := by
        refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
          (fun v _ => (hf v).continuousAt.continuousWithinAt)
          (fun v _ => (hf v).hasDerivWithinAt) ?_
        intro v hv
        rw [interior_Ici] at hv
        exact hf' v (le_of_lt hv)
      exact hm (Set.self_mem_Ici) hw hw
    constructor
    · have := mono hg (fun v hv => (ih hv).1)
      simpa [airyMod_rem_zero] using this
    · have := mono hh (fun v hv => sub_nonneg.mpr (ih hv).2)
      simp only [airyMod_rem_zero, mul_zero, sub_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, not_false_eq_true, zero_pow, zero_div] at this
      linarith

/-- `Γ(m + 1/2) = √π ∏_{j<m} (2j+1) / 2^m`. -/
theorem airyMod_gamma_half (m : ℕ) :
    Real.Gamma (m + 1 / 2) = Real.sqrt π * (∏ j ∈ Finset.range m, (2 * (j : ℝ) + 1)) / 2 ^ m := by
  induction m with
  | zero => simpa using Real.Gamma_one_half_eq
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : ℝ) + 1 / 2 = (m + 1 / 2) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), ih, Finset.prod_range_succ, pow_succ]
    field_simp

/-- The moment terms of the expansion of `M²` at `-∞`. -/
theorem airyMod_term_identity (k : ℕ) {s : ℝ} (hs : 0 < s) :
    (π * Real.sqrt π)⁻¹ * (Real.Gamma ((3 * k : ℕ) + 1 / 2) * s ^ (-(((3 * k : ℕ) : ℝ) + 1 / 2)) *
      ((-1) ^ k / (12 ^ k * k !))) =
      s ^ (-1 / 2 : ℝ) / π * airyModulusCoeff k * (-s) ^ (-(3 * k : ℤ)) := by
  have hπ := Real.pi_pos
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  rw [airyMod_gamma_half, airyModulusCoeff, Real.rpow_neg hs.le, Real.rpow_add hs,
    Real.rpow_natCast, zpow_neg, show (3 * (k : ℤ)) = ((3 * k : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, neg_pow s, show (-1 : ℝ) ^ (3 * k) = (-1) ^ k by
      rw [pow_mul]; norm_num,
    show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.le]
  have h1 : (0 : ℝ) < s ^ (1 / 2 : ℝ) := by positivity
  have h3 : (96 : ℝ) ^ k = 2 ^ (3 * k) * 12 ^ k := by rw [pow_mul, ← mul_pow]; norm_num
  rw [h3]
  field_simp
  rw [← pow_mul, pow_mul]
  norm_num
  exact neg_one_pow_eq_or ℝ k

/-- The terms `e^{-st} t^{3k-1/2}` integrate to `Γ(3k+1/2) s^{-(3k+1/2)}`. -/
theorem airyMod_term_integral (k : ℕ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ ((((3 * k : ℕ) : ℝ) + 1 / 2) - 1)) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ ((((3 * k : ℕ) : ℝ) + 1 / 2) - 1) =
      Real.Gamma ((3 * k : ℕ) + 1 / 2) * s ^ (-(((3 * k : ℕ) : ℝ) + 1 / 2)) :=
  ⟨integrableOn_exp_neg_mul_mul_rpow_sub_one (by positivity) hs,
    integral_exp_neg_mul_mul_rpow_sub_one (by positivity) hs⟩

/-- The error of the truncated expansion of `M²` at `-∞` as an integral of the exponential
remainder: for `s > 0`, `M(-s)² - (s^{-1/2}/π) ∑_{k<N} c_k (-s)^{-3k} =
π^{-3/2} ∫₀^∞ e^{-st} t^{-1/2} R_N(t³/12) dt`. -/
theorem airyMod_sq_error_integral {s : ℝ} (hs : 0 < s) (N : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem N (t ^ 3 / 12))
      (Ioi 0) ∧
    airyModulus (-s) ^ 2 - s ^ (-1 / 2 : ℝ) / π * airyModulusSum false N (-s) =
      (π * Real.sqrt π)⁻¹ * ∫ t in Ioi (0 : ℝ),
        Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem N (t ^ 3 / 12) := by
  set B : ℕ → ℝ → ℝ := fun k t => Real.exp (-s * t) * t ^ ((((3 * k : ℕ) : ℝ) + 1 / 2) - 1) *
    ((-1) ^ k / (12 ^ k * k !))
  have hB : ∀ k, IntegrableOn (B k) (Ioi 0) := fun k => (airyMod_term_integral k hs).1.mul_const _
  have hBi : ∀ k, ∫ t in Ioi (0 : ℝ), B k t =
      Real.Gamma ((3 * k : ℕ) + 1 / 2) * s ^ (-(((3 * k : ℕ) : ℝ) + 1 / 2)) *
        ((-1) ^ k / (12 ^ k * k !)) := fun k => by
    rw [integral_mul_const, (airyMod_term_integral k hs).2]
  have hpt : ∀ t : ℝ, 0 < t → airyMod_kernel (-s) t =
      Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem N (t ^ 3 / 12) +
        ∑ k ∈ Finset.range N, B k t := by
    intro t ht
    simp only [airyMod_kernel, airyMod_rem, B]
    have : ∀ k ∈ Finset.range N, Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        ((-(t ^ 3 / 12)) ^ k / k !) = Real.exp (-s * t) * t ^ ((((3 * k : ℕ) : ℝ) + 1 / 2) - 1) *
          ((-1) ^ k / (12 ^ k * k !)) := by
      intro k _
      rw [show (((3 * k : ℕ) : ℝ) + 1 / 2) - 1 = ((3 * k : ℕ) : ℝ) + (-(1 / 2)) by ring,
        Real.rpow_add ht, Real.rpow_natCast, neg_pow, div_pow, pow_mul]
      field_simp
    rw [← Finset.sum_congr rfl this, ← Finset.mul_sum]
    ring
  have hA : IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
      airyMod_rem N (t ^ 3 / 12)) (Ioi 0) := by
    refine ((airyMod_kernel_integrable (-s)).sub (integrable_finsetSum (Finset.range N) fun k _ => hB k)).congr_fun
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hpt t ht]
    ring
  refine ⟨hA, ?_⟩
  rw [airyMod_sq_eq_integral, setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_add hA (integrable_finsetSum (Finset.range N) fun k _ => hB k), integral_finsetSum (Finset.range N) fun k _ => hB k]
  simp only [hBi, airyModulusSum, Bool.false_eq_true, ite_false]
  rw [Finset.mul_sum, div_eq_inv_mul, mul_add, Finset.mul_sum]
  have : ∀ k ∈ Finset.range N, (π * Real.sqrt π)⁻¹ * (Real.Gamma ((3 * k : ℕ) + 1 / 2) *
      s ^ (-(((3 * k : ℕ) : ℝ) + 1 / 2)) * ((-1) ^ k / (12 ^ k * k !))) =
      s ^ (-1 / 2 : ℝ) / π * (airyModulusCoeff k * (-s) ^ (-(3 * k : ℤ))) := by
    intro k _; rw [airyMod_term_identity k hs]; ring
  rw [Finset.sum_congr rfl this]
  ring

/-- Signed first-neglected-term bound for the expansion of `M²` at `-∞` (DLMF §9.8(iv)). -/
theorem airyMod_sq_error_bound {x : ℝ} (hx : x < 0) (N : ℕ) :
    |(airyModulus x ^ 2) - ((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusSum false N x| ≤ |((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusCoeff N * x ^ (-(3 * N : ℤ))| ∧
      0 ≤ ((airyModulus x ^ 2) - ((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusSum false N x) * (((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusCoeff N * x ^ (-(3 * N : ℤ))) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ x = -s := ⟨-x, by linarith, by ring⟩
  rw [neg_neg]
  have hπ := Real.pi_pos
  have hc : 0 < (π * Real.sqrt π)⁻¹ := by positivity
  obtain ⟨hA, hE⟩ := airyMod_sq_error_integral hs N
  rw [hE, ← airyMod_term_identity N hs]
  set J := ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem N (t ^ 3 / 12)
  set G := Real.Gamma ((3 * N : ℕ) + 1 / 2) * s ^ (-(((3 * N : ℕ) : ℝ) + 1 / 2))
  have hJ1 : 0 ≤ (-1) ^ N * J := by
    rw [← integral_const_mul]
    refine setIntegral_nonneg measurableSet_Ioi fun t (ht : 0 < t) => ?_
    have := (airyMod_rem_bounds N (w := t ^ 3 / 12) (by positivity)).1
    have : 0 ≤ Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) := by positivity
    nlinarith
  have hJ2 : (-1) ^ N * J ≤ G / (12 ^ N * N !) := by
    have hI := (airyMod_term_integral N hs)
    rw [show G / (12 ^ N * N !) = ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) *
        t ^ ((((3 * N : ℕ) : ℝ) + 1 / 2) - 1) / (12 ^ N * N !) by
      rw [integral_div, hI.2], ← integral_const_mul]
    refine setIntegral_mono_on (hA.const_mul _) (hI.1.div_const _) measurableSet_Ioi
      fun t (ht : 0 < t) => ?_
    have hb := (airyMod_rem_bounds N (w := t ^ 3 / 12) (by positivity)).2
    have h0 : 0 ≤ Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) := by positivity
    have e : Real.exp (-s * t) * t ^ ((((3 * N : ℕ) : ℝ) + 1 / 2) - 1) / (12 ^ N * N !) =
        Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * ((t ^ 3 / 12) ^ N / N !) := by
      rw [show (((3 * N : ℕ) : ℝ) + 1 / 2) - 1 = ((3 * N : ℕ) : ℝ) + (-(1 / 2)) by ring,
        Real.rpow_add ht, Real.rpow_natCast, div_pow, pow_mul]
      field_simp
    rw [e]
    calc (-1) ^ N * (Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem N (t ^ 3 / 12))
        = Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * ((-1) ^ N * airyMod_rem N (t ^ 3 / 12)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb h0
  have hsq : ((-1 : ℝ) ^ N) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hab : |(-1 : ℝ) ^ N| = 1 := by simp
  have hG : 0 ≤ G / (12 ^ N * N !) := hJ1.trans hJ2
  constructor
  · rw [show (π * Real.sqrt π)⁻¹ * J = (-1) ^ N * ((π * Real.sqrt π)⁻¹ * ((-1) ^ N * J)) by
      rw [← mul_assoc ((-1 : ℝ) ^ N), mul_comm ((-1 : ℝ) ^ N), mul_assoc, ← mul_assoc ((-1 : ℝ) ^ N),
        ← pow_two, hsq, one_mul],
      show (π * Real.sqrt π)⁻¹ * (G * ((-1) ^ N / (12 ^ N * N !))) =
        (-1) ^ N * ((π * Real.sqrt π)⁻¹ * (G / (12 ^ N * N !))) by ring,
      abs_mul ((-1 : ℝ) ^ N), abs_mul ((-1 : ℝ) ^ N), hab, one_mul, one_mul,
      abs_of_nonneg (mul_nonneg hc.le hJ1), abs_of_nonneg (mul_nonneg hc.le hG)]
    exact mul_le_mul_of_nonneg_left hJ2 hc.le
  · have : (π * Real.sqrt π)⁻¹ * J * ((π * Real.sqrt π)⁻¹ * (G * ((-1) ^ N / (12 ^ N * N !)))) =
        ((π * Real.sqrt π)⁻¹ * ((-1) ^ N * J)) * ((π * Real.sqrt π)⁻¹ * (G / (12 ^ N * N !))) := by
      ring
    rw [this]
    exact mul_nonneg (mul_nonneg hc.le hJ1) (mul_nonneg hc.le hG)

/-- The second Nicholson kernel `e^{xt} e^{-t³/12} t^{3/2}`. -/
noncomputable def airyMod_kernel2 (x t : ℝ) : ℝ :=
  Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)))

/-- The second Nicholson kernel is integrable on `(0, ∞)`. -/
theorem airyMod_kernel2_integrable (x : ℝ) : IntegrableOn (airyMod_kernel2 x) (Ioi 0) :=
  airyMod_integrableOn_exp_pow x 2

/-- **Nicholson-type formula for `N²`** on the real line:
`N(x)² = π^{-3/2} (½ ∫₀^∞ e^{xt - t³/12} t^{3/2} dt - x ∫₀^∞ e^{xt - t³/12} t^{-1/2} dt)`. -/
theorem airyMod_derivSq_eq_integral (x : ℝ) :
    airyDerivModulus x ^ 2 = ((∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t) / 2 -
      x * ∫ t in Ioi (0 : ℝ), airyMod_kernel x t) / (π * Real.sqrt π) := by
  have h := airyMod_derivModulus_sq_integral x
  rw [airyAiDeriv_ofReal_eq, airyBiDeriv_ofReal_eq, airyMod_pi_cpow] at h
  have hc : ∀ t : ℝ, 0 < t → ((t : ℂ) ^ (-1 / 2 : ℂ)) = ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    intro t ht; rw [ofReal_cpow ht.le]; push_cast; ring_nf
  have hI : (∫ t : ℝ in Ioi 0, exp ((x : ℂ) * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) =
      ((∫ t in Ioi (0 : ℝ), airyMod_kernel x t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [airyMod_kernel]
    rw [hc t ht]; push_cast
    rw [sub_eq_add_neg, Complex.exp_add]; ring
  have hI2 : (∫ t : ℝ in Ioi 0, exp ((x : ℂ) * t - (t : ℂ) ^ 3 / 12) *
      ((t : ℂ) ^ 2 * (t : ℂ) ^ (-1 / 2 : ℂ))) = ((∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [airyMod_kernel2]
    rw [hc t ht]; push_cast
    rw [sub_eq_add_neg, Complex.exp_add]; ring
  rw [hI, hI2] at h
  rw [airyDerivModulus_sq]
  have h' : ((airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2 : ℝ) : ℂ) =
      ((((∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t) / 2 - x * ∫ t in Ioi (0 : ℝ), airyMod_kernel x t) /
        (π * Real.sqrt π) : ℝ) : ℂ) := by
    push_cast; rw [h]; push_cast; ring
  exact_mod_cast h'

/-- Strict monotonicity of Laplace-type integrals `∫₀^∞ e^{xt} w(t) dt` in `x` for a positive
weight `w`. -/
theorem airyMod_integral_exp_strictMono {w : ℝ → ℝ} (hw : ∀ t, 0 < t → 0 < w t)
    (hint : ∀ a : ℝ, IntegrableOn (fun t => Real.exp (a * t) * w t) (Ioi 0)) {x y : ℝ}
    (hxy : x < y) :
    ∫ t in Ioi (0 : ℝ), Real.exp (x * t) * w t < ∫ t in Ioi (0 : ℝ), Real.exp (y * t) * w t := by
  rw [← sub_pos, ← integral_sub (hint y) (hint x)]
  refine airyMod_integral_pos ((hint y).sub (hint x)) fun t ht => ?_
  have h1 : Real.exp (x * t) < Real.exp (y * t) := Real.exp_lt_exp.2 (by nlinarith)
  have := hw t ht
  nlinarith

/-- The moment terms `e^{-st} t^{m-1/2}` integrate to `Γ(m+1/2) s^{-(m+1/2)}`. -/
theorem airyMod_mom_integral (m : ℕ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ (((m : ℝ) + 1 / 2) - 1)) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (((m : ℝ) + 1 / 2) - 1) =
      Real.Gamma (m + 1 / 2) * s ^ (-((m : ℝ) + 1 / 2)) :=
  ⟨integrableOn_exp_neg_mul_mul_rpow_sub_one (by positivity) hs,
    integral_exp_neg_mul_mul_rpow_sub_one (by positivity) hs⟩

/-- The moment terms of the expansion of `N²` at `-∞` coming from `∫ e^{-st} t^{3/2} e^{-t³/12}`. -/
theorem airyMod_deriv_term_identity (j : ℕ) {s : ℝ} (hs : 0 < s) :
    (π * Real.sqrt π)⁻¹ / 2 * (Real.Gamma ((3 * j + 2 : ℕ) + 1 / 2) *
      s ^ (-(((3 * j + 2 : ℕ) : ℝ) + 1 / 2)) * ((-1) ^ j / (12 ^ j * j !))) =
      s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
        (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1)) := by
  have hπ := Real.pi_pos
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have hP : ∏ i ∈ Finset.range (3 * (j + 1)), (2 * (i : ℝ) + 1) =
      (∏ i ∈ Finset.range (3 * j + 2), (2 * (i : ℝ) + 1)) * (6 * j + 5) := by
    rw [show 3 * (j + 1) = (3 * j + 2) + 1 by ring, Finset.prod_range_succ]; push_cast; ring
  rw [airyDerivModulusCoeff, airyModulusCoeff, hP, airyMod_gamma_half (3 * j + 2)]
  generalize ∏ i ∈ Finset.range (3 * j + 2), (2 * (i : ℝ) + 1) = P
  rw [Real.rpow_neg hs.le, Real.rpow_add hs, Real.rpow_natCast, zpow_neg,
    show (3 * ((j + 1 : ℕ) : ℤ)) = ((3 * j + 3 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    neg_pow s, show (-1 : ℝ) ^ (3 * j + 3) = -(-1) ^ j by
      rw [show 3 * j + 3 = 3 * (j + 1) by ring, pow_mul]; norm_num; ring,
    show s ^ (3 * j + 3) = s ^ (3 * j + 2) * s by ring, Nat.factorial_succ]
  have h3 : (96 : ℝ) ^ (j + 1) = 2 ^ (3 * j + 2) * 12 ^ j * 24 := by
    rw [pow_succ, pow_add, pow_mul, show (96 : ℝ) = 2 ^ 3 * 12 by norm_num, mul_pow]; ring
  rw [h3]
  push_cast
  have h65 : (1 - 6 * ((j : ℝ) + 1)) ≠ 0 := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have h1 : (0 : ℝ) < s ^ (1 / 2 : ℝ) := by positivity
  have hsq : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by rw [← Real.rpow_add hs]; norm_num
  have hpj : ((-1 : ℝ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  have e1 : (s ^ (1 / 2 : ℝ)) ^ 2 = s := by rw [sq, hsq]
  have e2 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e1, e2]
  ring

/-- The truncation error of `π^{-3/2}/2 ∫₀^∞ e^{-st} t^{3/2} e^{-t³/12} dt` at `s → +∞`. -/
theorem airyMod_kernel2_error {s : ℝ} (hs : 0 < s) (N : ℕ) :
    |(π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) -
      ∑ j ∈ Finset.range N, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
        (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1))| ≤
      (π * Real.sqrt π)⁻¹ / 2 * (Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) *
        s ^ (-(((3 * N + 2 : ℕ) : ℝ) + 1 / 2)) / (12 ^ N * N !)) := by
  have hπ := Real.pi_pos
  have hc : 0 < (π * Real.sqrt π)⁻¹ / 2 := by positivity
  set B : ℕ → ℝ → ℝ := fun j t => Real.exp (-s * t) * t ^ ((((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1) *
    ((-1) ^ j / (12 ^ j * j !))
  have hB : ∀ j, IntegrableOn (B j) (Ioi 0) := fun j =>
    (airyMod_mom_integral (3 * j + 2) hs).1.mul_const _
  have hBi : ∀ j, ∫ t in Ioi (0 : ℝ), B j t =
      Real.Gamma ((3 * j + 2 : ℕ) + 1 / 2) * s ^ (-(((3 * j + 2 : ℕ) : ℝ) + 1 / 2)) *
        ((-1) ^ j / (12 ^ j * j !)) := fun j => by
    rw [integral_mul_const, (airyMod_mom_integral (3 * j + 2) hs).2]
  have hpw : ∀ t : ℝ, 0 < t → ∀ j : ℕ, t ^ ((((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1) =
      t ^ (3 * j) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) := fun t ht j => by
    rw [show (((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1 = ((3 * j + 2 : ℕ) : ℝ) + (-(1 / 2)) by ring,
      Real.rpow_add ht, Real.rpow_natCast, pow_add]; ring
  have hpt : ∀ t : ℝ, 0 < t → airyMod_kernel2 (-s) t =
      Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) * airyMod_rem N (t ^ 3 / 12) +
        ∑ j ∈ Finset.range N, B j t := by
    intro t ht
    simp only [airyMod_kernel2, airyMod_rem, B]
    have : ∀ j ∈ Finset.range N, Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
        ((-(t ^ 3 / 12)) ^ j / j !) = Real.exp (-s * t) *
          t ^ ((((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1) * ((-1) ^ j / (12 ^ j * j !)) := by
      intro j _
      rw [hpw t ht j, neg_pow, div_pow, pow_mul]
      field_simp
    rw [← Finset.sum_congr rfl this, ← Finset.mul_sum]
    ring
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ ((((3 * N + 2 : ℕ) : ℝ) + 1 / 2) - 1) /
      (12 ^ N * N !)) (Ioi 0) := (airyMod_mom_integral (3 * N + 2) hs).1.div_const _
  have hA : IntegrableOn (fun t : ℝ => Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
      airyMod_rem N (t ^ 3 / 12)) (Ioi 0) := by
    refine ((airyMod_kernel2_integrable (-s)).sub
      (integrable_finsetSum (Finset.range N) fun k _ => hB k)).congr_fun
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hpt t ht]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_add hA (integrable_finsetSum (Finset.range N) fun k _ => hB k),
    integral_finsetSum (Finset.range N) fun k _ => hB k, mul_add, Finset.mul_sum]
  simp only [hBi, airyMod_deriv_term_identity _ hs, add_sub_cancel_right]
  rw [abs_mul, abs_of_pos hc]
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  rw [show Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) * s ^ (-(((3 * N + 2 : ℕ) : ℝ) + 1 / 2)) /
      (12 ^ N * N !) = ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) *
        t ^ ((((3 * N + 2 : ℕ) : ℝ) + 1 / 2) - 1) / (12 ^ N * N !) by
    rw [integral_div, (airyMod_mom_integral (3 * N + 2) hs).2]]
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hg ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  have hb := airyMod_rem_bounds N (w := t ^ 3 / 12) (by positivity)
  have h0 : 0 ≤ Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) := by positivity
  have habs : |airyMod_rem N (t ^ 3 / 12)| ≤ (t ^ 3 / 12) ^ N / N ! := by
    have : |airyMod_rem N (t ^ 3 / 12)| = (-1) ^ N * airyMod_rem N (t ^ 3 / 12) := by
      rw [← abs_of_nonneg hb.1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [this]; exact hb.2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, hpw t ht N]
  calc Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) * |airyMod_rem N (t ^ 3 / 12)|
      ≤ Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) * ((t ^ 3 / 12) ^ N / N !) :=
        mul_le_mul_of_nonneg_left habs h0
    _ = _ := by rw [div_pow, pow_mul]; field_simp

/-- Error bound for the truncated expansion of `N²` at `-∞` with `N + 1` terms. -/
theorem airyMod_derivSq_error {x : ℝ} (hx : x < 0) (N : ℕ) :
    |airyDerivModulus x ^ 2 - ∑ k ∈ Finset.range (N + 1),
        (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * k : ℤ)) * airyDerivModulusCoeff k| ≤
      (|airyModulusCoeff (N + 1)| + π * ((π * Real.sqrt π)⁻¹ / 2 *
        (Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) / (12 ^ N * N !)))) *
        |(-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * (N + 1 : ℕ) : ℤ))| := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ x = -s := ⟨-x, by linarith, by ring⟩
  rw [neg_neg]
  have hπ := Real.pi_pos
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have hsq : s * s ^ (-1 / 2 : ℝ) = s ^ (1 / 2 : ℝ) := by
    rw [show s * s ^ (-1 / 2 : ℝ) = s ^ (1 : ℝ) * s ^ (-1 / 2 : ℝ) by rw [Real.rpow_one],
      ← Real.rpow_add hs]; norm_num
  -- decomposition of `N²`
  have hN : airyDerivModulus (-s) ^ 2 = (π * Real.sqrt π)⁻¹ / 2 *
      (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) + s * airyModulus (-s) ^ 2 := by
    rw [airyMod_derivSq_eq_integral, airyMod_sq_eq_integral]; ring
  have hsum : ∑ k ∈ Finset.range (N + 1),
      s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * k : ℤ)) * airyDerivModulusCoeff k =
      s * (s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (N + 1) (-s)) +
        ∑ j ∈ Finset.range N, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1)) := by
    simp only [airyModulusSum, Bool.false_eq_true, ite_false, Finset.mul_sum]
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_range_succ']
    have h0 : airyDerivModulusCoeff 0 = airyModulusCoeff 0 := by
      simp [airyDerivModulusCoeff]
    rw [h0]
    simp only [CharP.cast_eq_zero, mul_zero, neg_zero, zpow_zero, mul_one]
    rw [show s ^ (1 / 2 : ℝ) / π * airyModulusCoeff 0 - s * (s ^ (-1 / 2 : ℝ) / π *
      airyModulusCoeff 0) = 0 by rw [← hsq]; ring, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hsq]; push_cast; ring
  rw [hN, hsum]
  have e1 := (airyMod_sq_error_bound (x := -s) (by linarith) (N + 1)).1
  rw [neg_neg] at e1
  have e2 := airyMod_kernel2_error hs N
  have key : (π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) +
      s * airyModulus (-s) ^ 2 - (s * (s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (N + 1) (-s)) +
        ∑ j ∈ Finset.range N, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1))) =
      s * (airyModulus (-s) ^ 2 - s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (N + 1) (-s)) +
      ((π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) -
        ∑ j ∈ Finset.range N, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1))) := by ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  have hphi : |s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (N + 1 : ℕ) : ℤ))| =
      s ^ (-(((3 * N + 2 : ℕ) : ℝ) + 1 / 2)) / π := by
    rw [abs_mul, abs_of_pos (by positivity), zpow_neg, abs_inv, abs_zpow, abs_neg, abs_of_pos hs,
      show (3 * ((N + 1 : ℕ) : ℤ)) = ((3 * N + 3 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      Real.rpow_neg hs.le, Real.rpow_add hs, Real.rpow_natCast,
      show s ^ (3 * N + 3) = s ^ (3 * N + 2) * (s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ)) by
        rw [← Real.rpow_add hs]; norm_num; ring]
    field_simp
  have hpsi : s * |s ^ (-1 / 2 : ℝ) / π * airyModulusCoeff (N + 1) * (-s) ^ (-(3 * (N + 1 : ℕ) : ℤ))| =
      |airyModulusCoeff (N + 1)| * |s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (N + 1 : ℕ) : ℤ))| := by
    rw [← hsq, ← abs_of_pos hs]
    simp only [abs_mul, abs_div, abs_of_pos hπ, abs_abs]
    ring
  rw [hphi] at hpsi ⊢
  rw [abs_mul, abs_of_pos hs]
  have := mul_le_mul_of_nonneg_left e1 hs.le
  push_cast at this hpsi e2 ⊢
  rw [hpsi] at this
  have e2' : (π * Real.sqrt π)⁻¹ / 2 * (Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) *
      s ^ (-(((3 * N + 2 : ℕ) : ℝ) + 1 / 2)) / (12 ^ N * N !)) =
      π * ((π * Real.sqrt π)⁻¹ / 2 * (Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) / (12 ^ N * N !))) *
        (s ^ (-(((3 * N + 2 : ℕ) : ℝ) + 1 / 2)) / π) := by
    field_simp
  push_cast at e2'
  rw [e2'] at e2
  nlinarith [this, e2]

/-- The exponential remainder is continuous. -/
theorem airyMod_rem_continuous (K : ℕ) : Continuous (airyMod_rem K) := by
  unfold airyMod_rem; fun_prop

/-- `|R_K(w)| ≤ w^K / K!` for `w ≥ 0`. -/
theorem airyMod_rem_abs_le (K : ℕ) {w : ℝ} (hw : 0 ≤ w) : |airyMod_rem K w| ≤ w ^ K / K ! := by
  have hb := airyMod_rem_bounds K hw
  have : |airyMod_rem K w| = (-1) ^ K * airyMod_rem K w := by
    rw [← abs_of_nonneg hb.1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [this]; exact hb.2

/-- The moment `t^{3K+3/2}` written in the kernel's factored form. -/
theorem airyMod_pow_factor {t : ℝ} (ht : 0 < t) (K : ℕ) :
    t ^ ((((3 * K + 2 : ℕ) : ℝ) + 1 / 2) - 1) = t ^ (3 * K) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) := by
  rw [show (((3 * K + 2 : ℕ) : ℝ) + 1 / 2) - 1 = ((3 * K + 2 : ℕ) : ℝ) + (-(1 / 2)) by ring,
    Real.rpow_add ht, Real.rpow_natCast, pow_add]; ring

/-- The pointwise first-neglected-term bound for the `N²` error integrand. -/
theorem airyMod_derivErr_pointwise (s : ℝ) (K : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ (-1) ^ K * (Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))) ∧
    (-1) ^ K * (Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))) ≤
      Real.exp (-s * t) * t ^ ((((3 * K + 2 : ℕ) : ℝ) + 1 / 2) - 1) *
        ((6 * K + 7) / (24 * 12 ^ K * (K + 1 : ℕ)!)) := by
  have hu : 0 ≤ t ^ 3 / 12 := by positivity
  obtain ⟨p0, p1⟩ := airyMod_rem_bounds K hu
  obtain ⟨q0, q1⟩ := airyMod_rem_bounds (K + 1) hu
  set p := (-1) ^ K * airyMod_rem K (t ^ 3 / 12)
  set q := (-1) ^ (K + 1) * airyMod_rem (K + 1) (t ^ 3 / 12)
  have ex : 0 < Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) := by positivity
  have e : (-1) ^ K * (Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
      (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))) =
      Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * (t ^ 2 * p / 4 + q / (2 * t)) := by
    simp only [p, q, pow_succ]; ring
  rw [e, airyMod_pow_factor ht K]
  constructor
  · positivity
  · have hb : t ^ 2 * p / 4 + q / (2 * t) ≤ t ^ (3 * K) * t ^ 2 *
        ((6 * K + 7) / (24 * 12 ^ K * (K + 1 : ℕ)!)) := by
      have h1 : t ^ 2 * p / 4 ≤ t ^ 2 * ((t ^ 3 / 12) ^ K / K !) / 4 := by gcongr
      have h2 : q / (2 * t) ≤ (t ^ 3 / 12) ^ (K + 1) / (K + 1)! / (2 * t) := by gcongr
      refine (add_le_add h1 h2).trans (le_of_eq ?_)
      rw [Nat.factorial_succ, div_pow, div_pow, pow_mul, pow_succ, pow_succ]
      push_cast
      field_simp
      ring
    calc _ ≤ Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * (t ^ (3 * K) * t ^ 2 *
          ((6 * K + 7) / (24 * 12 ^ K * (K + 1 : ℕ)!))) := mul_le_mul_of_nonneg_left hb ex.le
      _ = _ := by ring


/-- The truncation error of `π^{-3/2}/2 ∫₀^∞ e^{-st} t^{3/2} e^{-t³/12} dt` as an integral of the
exponential remainder. -/
theorem airyMod_kernel2_error_integral {s : ℝ} (hs : 0 < s) (K : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
      airyMod_rem K (t ^ 3 / 12)) (Ioi 0) ∧
    (π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) -
      ∑ j ∈ Finset.range K, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
        (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1)) =
      (π * Real.sqrt π)⁻¹ / 2 * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) *
        (t ^ 2 * t ^ (-(1 / 2) : ℝ)) * airyMod_rem K (t ^ 3 / 12) := by
  set B : ℕ → ℝ → ℝ := fun j t => Real.exp (-s * t) * t ^ ((((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1) *
    ((-1) ^ j / (12 ^ j * j !))
  have hB : ∀ j, IntegrableOn (B j) (Ioi 0) := fun j =>
    (airyMod_mom_integral (3 * j + 2) hs).1.mul_const _
  have hBi : ∀ j, ∫ t in Ioi (0 : ℝ), B j t =
      Real.Gamma ((3 * j + 2 : ℕ) + 1 / 2) * s ^ (-(((3 * j + 2 : ℕ) : ℝ) + 1 / 2)) *
        ((-1) ^ j / (12 ^ j * j !)) := fun j => by
    rw [integral_mul_const, (airyMod_mom_integral (3 * j + 2) hs).2]
  have hpt : ∀ t : ℝ, 0 < t → airyMod_kernel2 (-s) t =
      Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) * airyMod_rem K (t ^ 3 / 12) +
        ∑ j ∈ Finset.range K, B j t := by
    intro t ht
    simp only [airyMod_kernel2, airyMod_rem, B]
    have : ∀ j ∈ Finset.range K, Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
        ((-(t ^ 3 / 12)) ^ j / j !) = Real.exp (-s * t) *
          t ^ ((((3 * j + 2 : ℕ) : ℝ) + 1 / 2) - 1) * ((-1) ^ j / (12 ^ j * j !)) := by
      intro j _
      rw [airyMod_pow_factor ht j, neg_pow, div_pow, pow_mul]
      field_simp
    rw [← Finset.sum_congr rfl this, ← Finset.mul_sum]
    ring
  have hA : IntegrableOn (fun t : ℝ => Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
      airyMod_rem K (t ^ 3 / 12)) (Ioi 0) := by
    refine ((airyMod_kernel2_integrable (-s)).sub
      (integrable_finsetSum (Finset.range K) fun k _ => hB k)).congr_fun
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hpt t ht]
    ring
  refine ⟨hA, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_add hA (integrable_finsetSum (Finset.range K) fun k _ => hB k),
    integral_finsetSum (Finset.range K) fun k _ => hB k, mul_add, Finset.mul_sum]
  simp only [hBi, airyMod_deriv_term_identity _ hs, add_sub_cancel_right]

/-- The `N²` error integrand `e^{-st} t^{-1/2} (t² R_K/4 - R_{K+1}/(2t))` is integrable. -/
theorem airyMod_derivErr_integrable (s : ℝ) (hs : 0 < s) (K : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
      (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t)))
      (Ioi 0) := by
  have hc := airyMod_rem_continuous
  refine ((airyMod_mom_integral (3 * K + 2) hs).1.mul_const
    ((6 * K + 7) / (24 * 12 ^ K * (K + 1 : ℕ)!))).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t (ht : 0 < t)
    have : t ≠ 0 := ht.ne'
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) t :=
      Real.continuousAt_rpow_const _ _ (Or.inl this)
    have h2 : ContinuousAt (fun t : ℝ => airyMod_rem K (t ^ 3 / 12)) t :=
      ((hc K).comp (by fun_prop)).continuousAt
    have h3 : ContinuousAt (fun t : ℝ => airyMod_rem (K + 1) (t ^ 3 / 12)) t :=
      ((hc (K + 1)).comp (by fun_prop)).continuousAt
    have h5 : ContinuousAt (fun t : ℝ => 2 * t) t := by fun_prop
    exact (((Real.continuous_exp.continuousAt).comp (by fun_prop)).mul h1).mul
      ((((continuousAt_id.pow 2).mul h2).div_const 4).sub
        (h3.div h5 (by simpa using this)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    obtain ⟨h0, h1⟩ := airyMod_derivErr_pointwise s K ht
    have e : ‖Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))‖ =
        (-1) ^ K * (Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))) := by
      rw [← abs_of_nonneg h0, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        Real.norm_eq_abs]
    rw [e]
    exact h1


/-- Integration by parts for the `M²` error integrand:
`s ∫ e^{-st} t^{-1/2} R_{K+1}(t³/12) = ∫ e^{-st} t^{-1/2}(t² R_K/4 - R_{K+1}/(2t)) - ½ ∫ e^{-st} t^{3/2} R_K`. -/
theorem airyMod_derivErr_ibp {s : ℝ} (hs : 0 < s) (K : ℕ) :
    s * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem (K + 1) (t ^ 3 / 12) =
      (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))) -
      (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
        airyMod_rem K (t ^ 3 / 12)) / 2 := by
  set F : ℝ → ℝ := fun t => Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * airyMod_rem (K + 1) (t ^ 3 / 12)
  set E : ℝ → ℝ := fun t => Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
    (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))
  set B : ℝ → ℝ := fun t => Real.exp (-s * t) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) *
    airyMod_rem K (t ^ 3 / 12)
  have hA : IntegrableOn F (Ioi 0) := (airyMod_sq_error_integral hs (K + 1)).1
  have hE : IntegrableOn E (Ioi 0) := airyMod_derivErr_integrable s hs K
  have hB : IntegrableOn B (Ioi 0) := (airyMod_kernel2_error_integral hs K).1
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (-s * F t + (E t - B t / 2)) t := by
    intro t (ht : 0 < t)
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-s * t)) (Real.exp (-s * t) * (-s)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-s)).exp
    have h2 := Real.hasDerivAt_rpow_const (p := (-(1 / 2) : ℝ)) (Or.inl ht.ne')
    have h3 : HasDerivAt (fun t : ℝ => airyMod_rem (K + 1) (t ^ 3 / 12))
        (-airyMod_rem K (t ^ 3 / 12) * (3 * t ^ 2 / 12)) t := by
      have h4 : HasDerivAt (fun t : ℝ => t ^ 3 / 12) (3 * t ^ 2 / 12) t := by
        simpa using (hasDerivAt_pow 3 t).div_const 12
      exact (airyMod_hasDerivAt_rem K (t ^ 3 / 12)).comp t h4
    convert (h1.mul h2).mul h3 using 1
    simp only [F, E, B, Pi.mul_apply]
    rw [Real.rpow_sub_one ht.ne']
    field_simp
    ring
  have f'int : IntegrableOn (fun t => -s * F t + (E t - B t / 2)) (Ioi 0) :=
    (hA.const_mul (-s)).add (hE.sub (hB.div_const 2))
  have hlim : Tendsto F atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hderiv f'int hA
  have hF0 : F 0 = 0 := by simp [F]
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    rw [ContinuousWithinAt, hF0]
    set p : ℝ := ((3 * (K + 1) : ℕ) : ℝ) + (-(1 / 2))
    have hp : 0 < p := by simp only [p]; push_cast; linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    have hg : Tendsto (fun t : ℝ => t ^ p / (12 ^ (K + 1) * (K + 1)!)) (𝓝[Ici 0] 0) (𝓝 0) := by
      have := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).div_const
        (12 ^ (K + 1) * ((K + 1)! : ℝ))).tendsto
      rw [Real.zero_rpow hp.ne', zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 ≤ t)
    rcases ht.eq_or_lt with rfl | ht
    · rw [hF0, norm_zero, Real.zero_rpow hp.ne', zero_div]
    · have hb := airyMod_rem_abs_le (K + 1) (w := t ^ 3 / 12) (by positivity)
      have he : Real.exp (-s * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hw : 0 < t ^ (-(1 / 2) : ℝ) := by positivity
      simp only [F, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hw]
      have e : t ^ p / (12 ^ (K + 1) * (K + 1)!) =
          t ^ (-(1 / 2) : ℝ) * ((t ^ 3 / 12) ^ (K + 1) / (K + 1)!) := by
        simp only [p]
        rw [Real.rpow_add ht, Real.rpow_natCast, div_pow, pow_mul]
        field_simp
      rw [e]
      calc Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) * |airyMod_rem (K + 1) (t ^ 3 / 12)|
          ≤ 1 * t ^ (-(1 / 2) : ℝ) * ((t ^ 3 / 12) ^ (K + 1) / (K + 1)!) := by gcongr
        _ = _ := by ring
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv f'int hlim
  rw [hF0, sub_zero] at key
  have i1 : ∫ t in Ioi (0 : ℝ), -s * F t + (E t - B t / 2) =
      (∫ t in Ioi (0 : ℝ), -s * F t) + ∫ t in Ioi (0 : ℝ), (E t - B t / 2) :=
    integral_add (hA.const_mul (-s)) (hE.sub (hB.div_const 2))
  have i2 : ∫ t in Ioi (0 : ℝ), (E t - B t / 2) =
      (∫ t in Ioi (0 : ℝ), E t) - ∫ t in Ioi (0 : ℝ), B t / 2 :=
    integral_sub hE (hB.div_const 2)
  rw [i1, i2, integral_const_mul, integral_div] at key
  linarith


/-- `d_{K+1} = (d_{K+1} - a_{K+1}) (6K+7)/(12(K+1))` for the `N²` and `M²` coefficients. -/
theorem airyMod_derivCoeff_eq (K : ℕ) :
    airyDerivModulusCoeff (K + 1) = (airyDerivModulusCoeff (K + 1) - airyModulusCoeff (K + 1)) *
      ((6 * K + 7) / (12 * (K + 1))) := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : (1 - 6 * ((K + 1 : ℕ) : ℝ)) ≠ 0 := by push_cast; linarith
  have h2 : (12 * ((K : ℝ) + 1)) ≠ 0 := by positivity
  simp only [airyDerivModulusCoeff]
  field_simp
  push_cast
  ring

/-- The first neglected term of the `N²` expansion as a moment integral. -/
theorem airyMod_derivMod_term_identity (K : ℕ) {s : ℝ} (hs : 0 < s) :
    (π * Real.sqrt π)⁻¹ * (Real.Gamma ((3 * K + 2 : ℕ) + 1 / 2) *
      s ^ (-(((3 * K + 2 : ℕ) : ℝ) + 1 / 2)) * ((6 * K + 7) / (24 * 12 ^ K * (K + 1 : ℕ)!))) *
        (-1) ^ K =
      s ^ (1 / 2 : ℝ) / π * airyDerivModulusCoeff (K + 1) * (-s) ^ (-(3 * (K + 1 : ℕ) : ℤ)) := by
  have h := airyMod_deriv_term_identity K hs
  rw [airyMod_derivCoeff_eq K]
  have e : s ^ (1 / 2 : ℝ) / π * ((airyDerivModulusCoeff (K + 1) - airyModulusCoeff (K + 1)) *
      ((6 * K + 7) / (12 * (K + 1)))) * (-s) ^ (-(3 * (K + 1 : ℕ) : ℤ)) =
      (s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (K + 1 : ℕ) : ℤ)) *
        (airyDerivModulusCoeff (K + 1) - airyModulusCoeff (K + 1))) *
          ((6 * K + 7) / (12 * (K + 1))) := by ring
  rw [e, ← h, Nat.factorial_succ]
  push_cast
  field_simp
  norm_num

/-- Splitting the truncated `N²` series into the `M²` series and the kernel-2 series. -/
theorem airyMod_derivSum_split {s : ℝ} (hs : 0 < s) (K : ℕ) :
    s ^ (1 / 2 : ℝ) / π * airyModulusSum true (K + 1) (-s) =
      s * (s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (K + 1) (-s)) +
        ∑ j ∈ Finset.range K, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1)) := by
  have hsq : s * s ^ (-1 / 2 : ℝ) = s ^ (1 / 2 : ℝ) := by
    rw [show s * s ^ (-1 / 2 : ℝ) = s ^ (1 : ℝ) * s ^ (-1 / 2 : ℝ) by rw [Real.rpow_one],
      ← Real.rpow_add hs]; norm_num
  simp only [airyModulusSum, ite_true, Bool.false_eq_true, ite_false, Finset.mul_sum]
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  have h0 : airyDerivModulusCoeff 0 = airyModulusCoeff 0 := by
    simp [airyDerivModulusCoeff]
  rw [h0]
  simp only [CharP.cast_eq_zero, mul_zero, neg_zero, zpow_zero, mul_one]
  rw [show s ^ (1 / 2 : ℝ) / π * airyModulusCoeff 0 - s * (s ^ (-1 / 2 : ℝ) / π *
    airyModulusCoeff 0) = 0 by rw [← hsq]; ring, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hsq]; push_cast; ring

/-- The error of the truncated expansion of `N²` at `-∞` as a single integral:
`N(-s)² - (s^{1/2}/π) ∑_{k<K+1} d_k (-s)^{-3k} =
π^{-3/2} ∫₀^∞ e^{-st} t^{-1/2} (t² R_K(t³/12)/4 - R_{K+1}(t³/12)/(2t)) dt`. -/
theorem airyMod_derivSq_error_integral {s : ℝ} (hs : 0 < s) (K : ℕ) :
    airyDerivModulus (-s) ^ 2 - s ^ (1 / 2 : ℝ) / π * airyModulusSum true (K + 1) (-s) =
      (π * Real.sqrt π)⁻¹ * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t)) := by
  have hN : airyDerivModulus (-s) ^ 2 = (π * Real.sqrt π)⁻¹ / 2 *
      (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) + s * airyModulus (-s) ^ 2 := by
    rw [airyMod_derivSq_eq_integral, airyMod_sq_eq_integral]; ring
  have h1 := (airyMod_sq_error_integral hs (K + 1)).2
  have h2 := (airyMod_kernel2_error_integral hs K).2
  have h3 := airyMod_derivErr_ibp hs K
  rw [hN, airyMod_derivSum_split hs K]
  have : (π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) +
      s * airyModulus (-s) ^ 2 - (s * (s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (K + 1) (-s)) +
        ∑ j ∈ Finset.range K, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1))) =
      s * (airyModulus (-s) ^ 2 - s ^ (-1 / 2 : ℝ) / π * airyModulusSum false (K + 1) (-s)) +
      ((π * Real.sqrt π)⁻¹ / 2 * (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) -
        ∑ j ∈ Finset.range K, s ^ (1 / 2 : ℝ) / π * (-s) ^ (-(3 * (j + 1 : ℕ) : ℤ)) *
          (airyDerivModulusCoeff (j + 1) - airyModulusCoeff (j + 1))) := by ring
  rw [this, h1, h2]
  have e : s * ((π * Real.sqrt π)⁻¹ * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) *
      t ^ (-(1 / 2) : ℝ) * airyMod_rem (K + 1) (t ^ 3 / 12)) = (π * Real.sqrt π)⁻¹ *
      (s * ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
        airyMod_rem (K + 1) (t ^ 3 / 12)) := by ring
  rw [e, h3]
  ring

/-- The cross-term Nicholson kernel `e^{xt} e^{-t³/12} t^{1/2}`. -/
noncomputable def airyMod_kernel1 (x t : ℝ) : ℝ :=
  Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) * (t ^ 1 * t ^ (-(1 / 2) : ℝ)))

/-- Nicholson-type formula for `Ai Ai' + Bi Bi'` on the real line. -/
theorem airyMod_cross_eq_integral (x : ℝ) :
    airyAiReal x * airyAiDerivReal x + airyBiReal x * airyBiDerivReal x =
      (∫ t in Ioi (0 : ℝ), airyMod_kernel1 x t) / (2 * (π * Real.sqrt π)) := by
  have h := airyMod_cross_integral x
  rw [airyAi_ofReal_eq, airyBi_ofReal_eq, airyAiDeriv_ofReal_eq, airyBiDeriv_ofReal_eq,
    airyMod_pi_cpow] at h
  have hI : (∫ t : ℝ in Ioi 0, exp ((x : ℂ) * t - (t : ℂ) ^ 3 / 12) *
      ((t : ℂ) ^ 1 * (t : ℂ) ^ (-1 / 2 : ℂ))) = ((∫ t in Ioi (0 : ℝ), airyMod_kernel1 x t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    have hc : ((t : ℂ) ^ (-1 / 2 : ℂ)) = ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
      rw [ofReal_cpow ht.le]; push_cast; ring_nf
    simp only [airyMod_kernel1]
    rw [hc]; push_cast
    rw [sub_eq_add_neg, Complex.exp_add]; ring
  rw [hI] at h
  exact_mod_cast h

/-- `|x|^{1/2} M(x)² < 1/π` for `x < 0`. -/
theorem airyMod_sqrt_mul_sq_lt {s : ℝ} (hs : 0 < s) : s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2 < 1 / π := by
  have hπ := Real.pi_pos
  rw [airyMod_sqrt_mul_sq hs]
  have hG : ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (-(1 / 2) : ℝ) = Real.sqrt π := by
    rw [← Real.Gamma_one_half_eq, Real.Gamma_eq_integral (by norm_num)]
    norm_num
  have hint := Real.GammaIntegral_convergent (s := 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num] at hint
  have hlt : (∫ u in Ioi (0 : ℝ), Real.exp (-u) * (Real.exp (-(u ^ 3 / (12 * s ^ 3))) *
      u ^ (-(1 / 2) : ℝ))) < ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (-(1 / 2) : ℝ) := by
    rw [← sub_pos, ← integral_sub hint (airyMod_scaled_integrable hs.le)]
    refine airyMod_integral_pos (hint.sub (airyMod_scaled_integrable hs.le)) fun u hu => ?_
    have : Real.exp (-(u ^ 3 / (12 * s ^ 3))) < 1 := Real.exp_lt_one_iff.mpr
      (neg_lt_zero.mpr (by positivity))
    have h2 : 0 < Real.exp (-u) * u ^ (-(1 / 2) : ℝ) := by positivity
    nlinarith
  rw [hG] at hlt
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
  rw [div_lt_div_iff₀ (by positivity) hπ]
  nlinarith

end Nicholson

/-- `M(x)` is strictly increasing on `(-∞, 0]`, DLMF §9.8(iii). -/
theorem airy_modulus_monotone :
    StrictMonoOn (airyModulus) (Iic 0) := by
  intro x _ y _ hxy
  exact lt_of_pow_lt_pow_left₀ 2 (airyModulus_pos y).le (airyMod_sq_strictMono hxy)

/-- `M'(x)` is strictly increasing on `(-∞, 0]`, DLMF §9.8(iii). -/
theorem airy_modulus_deriv_monotone :
    StrictMonoOn (deriv airyModulus) (Iic 0) := by
  have hπ := Real.pi_pos
  set C : ℝ → ℝ := fun x => airyAiReal x * airyAiDerivReal x + airyBiReal x * airyBiDerivReal x
  have hC : ∀ x, HasDerivAt C (airyDerivModulus x ^ 2 + x * airyModulus x ^ 2) x := fun x => by
    have h := ((hasDerivAt_airyAiReal x).mul (hasDerivAt_airyAiDerivReal x)).add
      ((hasDerivAt_airyBiReal x).mul (hasDerivAt_airyBiDerivReal x))
    refine h.congr_deriv ?_
    rw [airyDerivModulus_sq, airyModulus_sq]; ring
  have hD : ∀ x, HasDerivAt (deriv airyModulus)
      (((airyDerivModulus x ^ 2 + x * airyModulus x ^ 2) * airyModulus x -
        C x * (C x / airyModulus x)) / airyModulus x ^ 2) x := fun x => by
    rw [deriv_airyModulus]
    exact (hC x).div (hasDerivAt_airyModulus x) (airyModulus_pos x).ne'
  refine strictMonoOn_of_deriv_pos (convex_Iic 0)
    (fun x _ => (hD x).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Iic, mem_Iio] at hx
  rw [(hD x).deriv]
  have hM := airyModulus_pos x
  have hL := airy_lagrange x
  rw [← airyModulus_sq, ← airyDerivModulus_sq] at hL
  have hb := airyMod_sqrt_mul_sq_lt (s := -x) (by linarith)
  rw [neg_neg] at hb
  have hsq : ((-x) ^ (1 / 2 : ℝ)) ^ 2 = -x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have key : 0 < 1 / π ^ 2 + x * airyModulus x ^ 4 := by
    have h0 : 0 ≤ (-x) ^ (1 / 2 : ℝ) * airyModulus x ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (by positivity)
    have h1 : ((-x) ^ (1 / 2 : ℝ) * airyModulus x ^ 2) ^ 2 < (1 / π) ^ 2 :=
      pow_lt_pow_left₀ hb h0 (by norm_num)
    rw [mul_pow, hsq] at h1
    have : (1 / π) ^ 2 = 1 / π ^ 2 := by ring
    nlinarith
  have e : ((airyDerivModulus x ^ 2 + x * airyModulus x ^ 2) * airyModulus x -
      C x * (C x / airyModulus x)) / airyModulus x ^ 2 =
      (1 / π ^ 2 + x * airyModulus x ^ 4) / airyModulus x ^ 3 := by
    have hNC : (airyDerivModulus x ^ 2 + x * airyModulus x ^ 2) * airyModulus x ^ 2 - C x ^ 2 =
        1 / π ^ 2 + x * airyModulus x ^ 4 := by
      simp only [C]
      field_simp
      linear_combination hL
    rw [← hNC]
    field_simp
  rw [e]; positivity

/-! ### The weighted Nicholson function for `|x|^{-1/4} N(x)` -/

/-- `e^{-u} u^a e^{-v u³/12}` is integrable on `(0, ∞)` for `a > -1` and `v ≥ 0`. -/
theorem airyMod_wInt {a : ℝ} (ha : -1 < a) {v : ℝ} (hv : 0 ≤ v) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ a * Real.exp (-(v * u ^ 3 / 12))) (Ioi 0) := by
  have hint := Real.GammaIntegral_convergent (s := a + 1) (by linarith)
  rw [show a + 1 - 1 = a by ring] at hint
  refine hint.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact (((Real.continuous_exp.comp continuous_neg).continuousAt.mul
      (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht)))).mul
      ((Real.continuous_exp.comp (by fun_prop)).continuousAt)).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    have h1 : Real.exp (-(v * t ^ 3 / 12)) ≤ 1 := Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (by positivity))
    have h0 : 0 ≤ Real.exp (-t) * t ^ a := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    calc Real.exp (-t) * t ^ a * Real.exp (-(v * t ^ 3 / 12)) ≤ Real.exp (-t) * t ^ a * 1 := by
          gcongr
      _ = _ := by ring

/-- The weighted Nicholson function `G(v) = ∫₀^∞ e^{-u}(u^{-1/2} + (v/2) u^{3/2}) e^{-vu³/12} du`. -/
noncomputable def airyMod_wG (v : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-u) * (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ)) *
    Real.exp (-(v * u ^ 3 / 12))

/-- The `v`-derivative of the integrand of `G`. -/
theorem airyMod_wG_hasDerivAt_integrand (u v : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (-u) * (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ)) *
        Real.exp (-(v * u ^ 3 / 12)))
      (Real.exp (-u) * (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) +
        v / 2 * u ^ (3 / 2 : ℝ))) * Real.exp (-(v * u ^ 3 / 12))) v := by
  have h1 : HasDerivAt (fun v : ℝ => u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ))
      (u ^ (3 / 2 : ℝ) / 2) v := by
    have := (((hasDerivAt_id' v).div_const 2).mul_const (u ^ (3 / 2 : ℝ))).const_add
      (u ^ (-(1 / 2) : ℝ))
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun v : ℝ => Real.exp (-(v * u ^ 3 / 12)))
      (Real.exp (-(v * u ^ 3 / 12)) * (-(u ^ 3 / 12))) v := by
    have e : (fun v : ℝ => Real.exp (-(v * u ^ 3 / 12))) =
        fun v => Real.exp (v * (-(u ^ 3 / 12))) := by funext v; ring_nf
    rw [e]
    exact ((hasDerivAt_mul_const (-(u ^ 3 / 12))).exp).congr_deriv
      (by rw [show v * -(u ^ 3 / 12) = -(v * u ^ 3 / 12) by ring])
  have := (h1.const_mul (Real.exp (-u))).mul h2
  convert this using 1
  ring

/-- `u^{a} ≤ u^{b_1} + u^{b_2}` style domination: `u^a ≤ u^{-1/2} + u^{9/2}` for `-1/2 ≤ a ≤ 9/2`. -/
theorem airyMod_rpow_le_sum {u a : ℝ} (hu : 0 < u) (ha1 : -(1 / 2) ≤ a) (ha2 : a ≤ 9 / 2) :
    u ^ a ≤ u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ) := by
  rcases le_total u 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hu h ha1
    have : 0 ≤ u ^ (9 / 2 : ℝ) := by positivity
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h ha2
    have : 0 ≤ u ^ (-(1 / 2) : ℝ) := by positivity
    linarith

/-- Rewriting `u³ u^{a}` as `u^{a+3}` for `u > 0`. -/
theorem airyMod_pow_three_mul_rpow {u : ℝ} (hu : 0 < u) (a : ℝ) :
    u ^ 3 * u ^ a = u ^ (a + 3) := by
  rw [Real.rpow_add hu, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring

/-- Domination of the `v`-derivative of the integrand of `G` near `v`, uniformly for
`|w - v| < v/2`. -/
private lemma airyMod_wG_deriv_bound {u v w : ℝ} (hu : 0 < u)
    (hw : w ∈ Metric.ball v (v / 2)) :
    ‖Real.exp (-u) * (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) +
        w / 2 * u ^ (3 / 2 : ℝ))) * Real.exp (-(w * u ^ 3 / 12))‖ ≤
      (1 + 1 / 12 + v / 24 * 3 / 2 + 1) *
        (Real.exp (-u) * (u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ))) := by
  have hw' : |w - v| < v / 2 := by simpa [Real.dist_eq] using hw
  have hw0 : 0 < w := by have := abs_lt.mp hw'; linarith
  have hw1 : w ≤ 3 * v / 2 := by have := abs_lt.mp hw'; linarith
  have hE : Real.exp (-(w * u ^ 3 / 12)) ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (by positivity))
  have hE0 := Real.exp_pos (-(w * u ^ 3 / 12))
  have he := Real.exp_pos (-u)
  -- the three powers appearing
  have p1 := airyMod_rpow_le_sum hu (a := 3 / 2) (by norm_num) (by norm_num)
  have p2 : u ^ 3 * u ^ (-(1 / 2) : ℝ) ≤ u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ) := by
    rw [airyMod_pow_three_mul_rpow hu]
    exact airyMod_rpow_le_sum hu (by norm_num) (by norm_num)
  have p3 : u ^ 3 * u ^ (3 / 2 : ℝ) ≤ u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ) := by
    rw [airyMod_pow_three_mul_rpow hu]
    exact airyMod_rpow_le_sum hu (by norm_num) (by norm_num)
  have q1 : 0 ≤ u ^ (3 / 2 : ℝ) := by positivity
  have q2 : 0 ≤ u ^ 3 * u ^ (-(1 / 2) : ℝ) := by positivity
  have q3 : 0 ≤ u ^ 3 * u ^ (3 / 2 : ℝ) := by positivity
  have hS : 0 ≤ u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ) := by positivity
  have habs : |u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) +
      w / 2 * u ^ (3 / 2 : ℝ))| ≤ (1 + 1 / 12 + v / 24 * 3 / 2 + 1) *
        (u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ)) := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos he, abs_of_pos hE0]
  calc Real.exp (-u) * |u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) +
        w / 2 * u ^ (3 / 2 : ℝ))| * Real.exp (-(w * u ^ 3 / 12))
      ≤ Real.exp (-u) * ((1 + 1 / 12 + v / 24 * 3 / 2 + 1) *
        (u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ))) * 1 := by
        gcongr
        exact mul_nonneg he.le (mul_nonneg (by linarith) hS)
    _ = _ := by ring

/-- `G'(v) = ∫₀^∞ e^{-u}(u^{3/2}/2 - u^{5/2}/12 - (v/24) u^{9/2}) e^{-vu³/12} du` for `v > 0`. -/
theorem airyMod_wG_hasDerivAt {v : ℝ} (hv : 0 < v) :
    HasDerivAt airyMod_wG (∫ u in Ioi (0 : ℝ), Real.exp (-u) *
      (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ))) *
        Real.exp (-(v * u ^ 3 / 12))) v := by
  have hball : Metric.ball v (v / 2) ∈ 𝓝 v := Metric.ball_mem_nhds v (by positivity)
  set B : ℝ → ℝ := fun u => (1 + 1 / 12 + v / 24 * 3 / 2 + 1) *
    (Real.exp (-u) * (u ^ (-(1 / 2) : ℝ) + u ^ (9 / 2 : ℝ)))
  have hBi : IntegrableOn B (Ioi 0) := by
    have h1 := airyMod_wInt (a := -(1 / 2)) (by norm_num) (le_refl 0)
    have h2 := airyMod_wInt (a := 9 / 2) (by norm_num) (le_refl 0)
    refine IntegrableOn.congr_fun ((h1.add h2).const_mul (1 + 1 / 12 + v / 24 * 3 / 2 + 1))
      (fun u _ => ?_) measurableSet_Ioi
    simp only [B, Pi.add_apply, zero_mul, zero_div, neg_zero, Real.exp_zero, mul_one]; ring
  have hmeas : ∀ w : ℝ, AEStronglyMeasurable (fun u : ℝ => Real.exp (-u) *
      (u ^ (-(1 / 2) : ℝ) + w / 2 * u ^ (3 / 2 : ℝ)) * Real.exp (-(w * u ^ 3 / 12)))
      (volume.restrict (Ioi 0)) := by
    intro w
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact (((Real.continuous_exp.comp continuous_neg).continuousAt.mul
      ((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))).add
        (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht)))))).mul
      ((Real.continuous_exp.comp (by fun_prop)).continuousAt)).continuousWithinAt
  have hint0 : IntegrableOn (fun u : ℝ => Real.exp (-u) *
      (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ)) * Real.exp (-(v * u ^ 3 / 12))) (Ioi 0) := by
    have h1 := airyMod_wInt (a := -(1 / 2)) (by norm_num) hv.le
    have h2 := (airyMod_wInt (a := 3 / 2) (by norm_num) hv.le).const_mul (v / 2)
    refine IntegrableOn.congr_fun (h1.add h2) (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0)) hball
    (F := fun w (u : ℝ) => Real.exp (-u) * (u ^ (-(1 / 2) : ℝ) + w / 2 * u ^ (3 / 2 : ℝ)) *
      Real.exp (-(w * u ^ 3 / 12)))
    (F' := fun w (u : ℝ) => Real.exp (-u) *
      (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) + w / 2 * u ^ (3 / 2 : ℝ))) *
        Real.exp (-(w * u ^ 3 / 12)))
    (Eventually.of_forall hmeas) hint0 ?_
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu w hw => ?_)) hBi
    (Eventually.of_forall fun u w _ => airyMod_wG_hasDerivAt_integrand u w)
  · exact h.2
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have hc1 := Real.continuousAt_rpow_const t (3 / 2 : ℝ) (Or.inl (ne_of_gt ht))
    have hc2 := Real.continuousAt_rpow_const t (-(1 / 2) : ℝ) (Or.inl (ne_of_gt ht))
    exact (((Real.continuous_exp.comp continuous_neg).continuousAt.mul
      ((hc1.div_const 2).sub (((continuous_pow 3).continuousAt.div_const 12).mul
        (hc2.add (continuousAt_const.mul hc1))))).mul
      ((Real.continuous_exp.comp (by fun_prop)).continuousAt)).continuousWithinAt
  · exact airyMod_wG_deriv_bound hu hw

/-- The boundary term `e^{-u} u^{5/2} e^{-vu³/12}` of the integration by parts tends to `0`
as `u → ∞`. -/
private lemma airyMod_wG_tendsto_boundary {v : ℝ} (hv : 0 < v) :
    Tendsto (fun u : ℝ => Real.exp (-u) * u ^ (5 / 2 : ℝ) * Real.exp (-(v * u ^ 3 / 12))) atTop
      (𝓝 0) := by
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 2) 1 one_pos
  refine squeeze_zero' (Eventually.of_forall fun u => ?_) ?_ h0
  · rcases le_or_gt 0 u with hu | hu
    · positivity
    · rw [Real.rpow_def_of_neg hu]
      have h := Real.exp_pos (-u)
      have h' := Real.exp_pos (-(v * u ^ 3 / 12))
      have hc : 0 ≤ Real.exp (Real.log u * (5 / 2)) * Real.cos (5 / 2 * π) := by
        rw [show (5 / 2 : ℝ) * π = π / 2 + 2 * π by ring, Real.cos_add_two_pi,
          Real.cos_pi_div_two, mul_zero]
      positivity
  · filter_upwards [eventually_gt_atTop 0] with u hu
    have hE : Real.exp (-(v * u ^ 3 / 12)) ≤ 1 := Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (by positivity))
    calc Real.exp (-u) * u ^ (5 / 2 : ℝ) * Real.exp (-(v * u ^ 3 / 12))
        ≤ Real.exp (-u) * u ^ (5 / 2 : ℝ) * 1 := by gcongr
      _ = u ^ (5 / 2 : ℝ) * Real.exp (-1 * u) := by ring_nf

/-- **The integration by parts behind 9.8(iii)**: `G'(v) = (1/12) ∫₀^∞ e^{-u}(u^{5/2} + u^{3/2})
e^{-vu³/12} du`, which is positive. -/
theorem airyMod_wG_deriv_eq {v : ℝ} (hv : 0 < v) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-u) *
      (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ))) *
        Real.exp (-(v * u ^ 3 / 12))) =
      1 / 12 * ∫ u in Ioi (0 : ℝ), Real.exp (-u) * (u ^ (5 / 2 : ℝ) + u ^ (3 / 2 : ℝ)) *
        Real.exp (-(v * u ^ 3 / 12)) := by
  set E : ℝ → ℝ := fun u => Real.exp (-(v * u ^ 3 / 12))
  set φ : ℝ → ℝ := fun u => Real.exp (-u) * u ^ (5 / 2 : ℝ) * E u
  set φ' : ℝ → ℝ := fun u => Real.exp (-u) *
    (5 / 2 * u ^ (3 / 2 : ℝ) - u ^ (5 / 2 : ℝ) - v / 4 * u ^ (9 / 2 : ℝ)) * E u
  have i32 := airyMod_wInt (a := 3 / 2) (by norm_num) hv.le
  have i52 := airyMod_wInt (a := 5 / 2) (by norm_num) hv.le
  have i92 := airyMod_wInt (a := 9 / 2) (by norm_num) hv.le
  have hφ'i : IntegrableOn φ' (Ioi 0) := by
    refine IntegrableOn.congr_fun (((i32.const_mul (5 / 2)).sub i52).sub (i92.const_mul (v / 4)))
      (fun u _ => ?_) measurableSet_Ioi
    simp only [φ', E, Pi.sub_apply]; ring
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt φ (φ' u) u := by
    intro u (hu : 0 < u)
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-u) * (-1)) u :=
      (hasDerivAt_neg u).exp
    have h2 : HasDerivAt (fun u : ℝ => u ^ (5 / 2 : ℝ)) (5 / 2 * u ^ (5 / 2 - 1 : ℝ)) u :=
      Real.hasDerivAt_rpow_const (Or.inl hu.ne')
    have h3 : HasDerivAt E (E u * (-(v * (3 * u ^ 2) / 12))) u := by
      have := ((((hasDerivAt_pow 3 u).const_mul v).div_const 12).neg).exp
      simp only [E]; convert this using 1
    have := (h1.mul h2).mul h3
    refine this.congr_deriv ?_
    simp only [φ', E, Pi.mul_apply]
    rw [show (5 / 2 - 1 : ℝ) = 3 / 2 by norm_num]
    have e1 : u ^ (5 / 2 : ℝ) * u ^ 2 = u ^ (9 / 2 : ℝ) := by
      rw [show (9 / 2 : ℝ) = 5 / 2 + 2 by norm_num, Real.rpow_add hu,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← e1]; ring
  have hcont : ContinuousWithinAt φ (Ici 0) 0 := by
    have : Continuous φ := by
      simp only [φ, E]
      exact ((Real.continuous_exp.comp continuous_neg).mul
        (Real.continuous_rpow_const (by norm_num))).mul (Real.continuous_exp.comp (by fun_prop))
    exact this.continuousWithinAt
  have hlim : Tendsto φ atTop (𝓝 0) := airyMod_wG_tendsto_boundary hv
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hφ'i hlim
  have hφ0 : φ 0 = 0 := by simp [φ]
  rw [hφ0, sub_zero] at hftc
  -- split the integrand
  have hsplit : ∀ u ∈ Ioi (0 : ℝ), Real.exp (-u) *
      (u ^ (3 / 2 : ℝ) / 2 - u ^ 3 / 12 * (u ^ (-(1 / 2) : ℝ) + v / 2 * u ^ (3 / 2 : ℝ))) *
        Real.exp (-(v * u ^ 3 / 12)) =
      1 / 12 * (Real.exp (-u) * (u ^ (5 / 2 : ℝ) + u ^ (3 / 2 : ℝ)) *
        Real.exp (-(v * u ^ 3 / 12))) + 1 / 6 * φ' u := by
    intro u (hu : 0 < u)
    simp only [φ', E]
    have e1 := airyMod_pow_three_mul_rpow hu (-(1 / 2))
    have e2 := airyMod_pow_three_mul_rpow hu (3 / 2)
    rw [show (-(1 / 2) + 3 : ℝ) = 5 / 2 by norm_num] at e1
    rw [show (3 / 2 + 3 : ℝ) = 9 / 2 by norm_num] at e2
    linear_combination (-(Real.exp (-u) * Real.exp (-(v * u ^ 3 / 12))) / 12) * e1 +
      (-(Real.exp (-u) * Real.exp (-(v * u ^ 3 / 12))) * v / 24) * e2
  have hI : IntegrableOn (fun u => Real.exp (-u) * (u ^ (5 / 2 : ℝ) + u ^ (3 / 2 : ℝ)) *
      Real.exp (-(v * u ^ 3 / 12))) (Ioi 0) :=
    (i52.add i32).congr_fun (fun u _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
    integral_add (hI.const_mul _) (hφ'i.const_mul _),
    integral_const_mul, integral_const_mul, hftc]
  ring

/-- `G'(v) > 0` for `v > 0`. -/
theorem airyMod_wG_deriv_pos {v : ℝ} (hv : 0 < v) : 0 < deriv airyMod_wG v := by
  rw [(airyMod_wG_hasDerivAt hv).deriv, airyMod_wG_deriv_eq hv]
  have i32 := airyMod_wInt (a := 3 / 2) (by norm_num) hv.le
  have i52 := airyMod_wInt (a := 5 / 2) (by norm_num) hv.le
  refine mul_pos (by norm_num) (airyMod_integral_pos
    (IntegrableOn.congr_fun (i52.add i32) (fun u _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi) fun u hu => by positivity)

/-- `G` is strictly increasing on `(0, ∞)`. -/
theorem airyMod_wG_strictMono : StrictMonoOn airyMod_wG (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · exact fun v hv => (airyMod_wG_hasDerivAt hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    exact airyMod_wG_deriv_pos hv

/-- Scaling `t = u/s` in the Nicholson-type integrals:
`∫₀^∞ e^{-st} e^{-t³/12} t^p dt = s^{-(p+1)} ∫₀^∞ e^{-u} u^p e^{-s^{-3}u³/12} du`. -/
theorem airyMod_wScale {s : ℝ} (hs : 0 < s) (p : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ p)) =
      s ^ (-(p + 1)) * ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ p *
        Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12)) := by
  set g : ℝ → ℝ := fun t => Real.exp (-s * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ p)
  have h := integral_comp_mul_left_Ioi g 0 (inv_pos.mpr hs)
  rw [mul_zero, smul_eq_mul, inv_inv] at h
  have key : ∀ u ∈ Ioi (0 : ℝ), g (s⁻¹ * u) = s ^ (-p) *
      (Real.exp (-u) * u ^ p * Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12))) := by
    intro u (hu : 0 < u)
    simp only [g]
    rw [Real.mul_rpow (inv_pos.mpr hs).le hu.le, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le]
    have : -s * (s⁻¹ * u) = -u := by field_simp
    rw [this, mul_pow, inv_pow]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul] at h
  have hs0 : 0 < s ^ (-p) := by positivity
  have : (∫ t in Ioi (0 : ℝ), g t) = s⁻¹ * (s ^ (-p) * ∫ u in Ioi (0 : ℝ),
      Real.exp (-u) * u ^ p * Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12))) := by
    rw [h]; field_simp
  rw [this, Real.rpow_neg hs.le (p + 1), Real.rpow_neg hs.le p, Real.rpow_add_one hs.ne']
  field_simp

/-- **Scaling form for `N²`**: for `s > 0`, `π^{3/2} s^{-1/2} N(-s)² = G(s^{-3})`. -/
theorem airyMod_wG_scaling {s : ℝ} (hs : 0 < s) :
    s ^ (-(1 / 2) : ℝ) * airyDerivModulus (-s) ^ 2 = airyMod_wG ((s ^ 3)⁻¹) / (π * Real.sqrt π) := by
  have hv : 0 ≤ (s ^ 3)⁻¹ := by positivity
  have h0 : (∫ t in Ioi (0 : ℝ), airyMod_kernel (-s) t) = s ^ (-(-(1 / 2) + 1) : ℝ) *
      ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (-(1 / 2) : ℝ) *
        Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12)) := by
    rw [← airyMod_wScale hs]; rfl
  have h2 : (∫ t in Ioi (0 : ℝ), airyMod_kernel2 (-s) t) = s ^ (-(3 / 2 + 1) : ℝ) *
      ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (3 / 2 : ℝ) *
        Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12)) := by
    rw [← airyMod_wScale hs]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [airyMod_kernel2]
    rw [show (3 / 2 : ℝ) = 2 + -(1 / 2) by norm_num, Real.rpow_add ht,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hG : airyMod_wG ((s ^ 3)⁻¹) = (∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (-(1 / 2) : ℝ) *
        Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12))) + (s ^ 3)⁻¹ / 2 * ∫ u in Ioi (0 : ℝ),
          Real.exp (-u) * u ^ (3 / 2 : ℝ) * Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12)) := by
    rw [← integral_const_mul, ← integral_add (airyMod_wInt (by norm_num) hv)
      ((airyMod_wInt (by norm_num) hv).const_mul _)]
    unfold airyMod_wG
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [airyMod_derivSq_eq_integral, h0, h2, hG]
  have e1 : s ^ (-(1 / 2) : ℝ) * s ^ (-(3 / 2 + 1) : ℝ) = (s ^ 3)⁻¹ := by
    rw [← Real.rpow_add hs, ← Real.rpow_natCast, ← Real.rpow_neg hs.le]; norm_num
  have e2 : s ^ (-(1 / 2) : ℝ) * s * s ^ (-(-(1 / 2) + 1) : ℝ) = 1 := by
    rw [mul_assoc, mul_comm s, ← Real.rpow_add_one hs.ne', ← Real.rpow_add hs]; norm_num
  rw [mul_div_assoc']
  congr 1
  linear_combination (∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (3 / 2 : ℝ) *
      Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12))) / 2 * e1 + (∫ u in Ioi (0 : ℝ), Real.exp (-u) *
        u ^ (-(1 / 2) : ℝ) * Real.exp (-((s ^ 3)⁻¹ * u ^ 3 / 12))) * e2

/-- `|x|^{-1/4} N(x)` is strictly increasing on `(-∞, 0)`, DLMF §9.8(iii). -/
theorem airy_weighted_derivModulus_monotone :
    StrictMonoOn (fun x : ℝ => |x| ^ (-1 / 4 : ℝ) * airyDerivModulus x) (Iio 0) := by
  intro x (hx : x < 0) y (hy : y < 0) hxy
  have hsq : ∀ z : ℝ, z < 0 → (|z| ^ (-1 / 4 : ℝ) * airyDerivModulus z) ^ 2 =
      airyMod_wG (((-z) ^ 3)⁻¹) / (π * Real.sqrt π) := by
    intro z hz
    rw [← airyMod_wG_scaling (neg_pos.mpr hz), neg_neg, mul_pow, abs_of_neg hz,
      ← Real.rpow_natCast, ← Real.rpow_mul (neg_pos.mpr hz).le]
    norm_num
  have hpos : ∀ z : ℝ, z < 0 → 0 ≤ |z| ^ (-1 / 4 : ℝ) * airyDerivModulus z := fun z _ =>
    mul_nonneg (by positivity) (airyDerivModulus_pos z).le
  refine lt_of_pow_lt_pow_left₀ 2 (hpos y hy) ?_
  rw [hsq x hx, hsq y hy]
  refine div_lt_div_of_pos_right ?_ (by positivity)
  have hx3 : 0 < (-x) ^ 3 := pow_pos (by linarith) 3
  have hy3 : 0 < (-y) ^ 3 := pow_pos (by linarith) 3
  have h3 : (-y) ^ 3 < (-x) ^ 3 := pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
  exact airyMod_wG_strictMono (inv_pos.mpr hx3) (inv_pos.mpr hy3) (inv_strictAnti₀ hy3 h3)

/-- `M(x) N(x)` is strictly increasing on `(-∞, 0]`, DLMF §9.8(iii). -/
theorem airy_modulus_product_monotone :
    StrictMonoOn (fun x => airyModulus x * airyDerivModulus x) (Iic 0) := by
  intro x _ y _ hxy
  have hπ := Real.pi_pos
  have w1 : ∀ t, 0 < t → 0 < Real.exp (-(t ^ 3 / 12)) * (t ^ 1 * t ^ (-(1 / 2) : ℝ)) :=
    fun t _ => by positivity
  have mono := airyMod_integral_exp_strictMono w1 (fun a => airyMod_integrableOn_exp_pow a 1) hxy
  have pos : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel1 x t :=
    airyMod_integral_pos (airyMod_integrableOn_exp_pow x 1) fun t ht => by
      unfold airyMod_kernel1; positivity
  have hc : ∀ z, (airyModulus z * airyDerivModulus z) ^ 2 =
      (airyAiReal z * airyAiDerivReal z + airyBiReal z * airyBiDerivReal z) ^ 2 + (π ^ 2)⁻¹ := by
    intro z
    have hL := airy_lagrange z
    rw [mul_pow, airyModulus_sq, airyDerivModulus_sq]
    field_simp
    linear_combination hL
  have hx0 : 0 ≤ airyModulus x * airyDerivModulus x :=
    mul_nonneg (airyModulus_pos x).le (airyDerivModulus_pos x).le
  refine lt_of_pow_lt_pow_left₀ 2 (mul_nonneg (airyModulus_pos y).le (airyDerivModulus_pos y).le) ?_
  simp only
  rw [hc, hc, airyMod_cross_eq_integral, airyMod_cross_eq_integral]
  have hd : 0 < 2 * (π * Real.sqrt π) := by positivity
  simp only [airyMod_kernel1] at pos ⊢
  have : (∫ t in Ioi (0 : ℝ), Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) *
      (t ^ 1 * t ^ (-(1 / 2) : ℝ)))) / (2 * (π * Real.sqrt π)) <
      (∫ t in Ioi (0 : ℝ), Real.exp (y * t) * (Real.exp (-(t ^ 3 / 12)) *
      (t ^ 1 * t ^ (-(1 / 2) : ℝ)))) / (2 * (π * Real.sqrt π)) := div_lt_div_of_pos_right mono hd
  have h0 : 0 < (∫ t in Ioi (0 : ℝ), Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) *
      (t ^ 1 * t ^ (-(1 / 2) : ℝ)))) / (2 * (π * Real.sqrt π)) := div_pos pos hd
  nlinarith

/-- `θ'(x)` is strictly increasing on `(-∞, 0]`, DLMF §9.8(iii). -/
theorem airy_phase_deriv_monotone :
    StrictMonoOn (deriv airyPhase) (Iic 0) := by
  intro x _ y _ hxy
  rw [deriv_airyPhase]
  have hπ := Real.pi_pos
  have h := airyMod_sq_strictMono hxy
  have hx := pow_pos (airyModulus_pos x) 2
  simp only at h ⊢
  rw [neg_lt_neg_iff]
  exact one_div_lt_one_div_of_lt (by positivity) (mul_lt_mul_of_pos_left h hπ)

/-- `φ'(x)` is strictly increasing on `(-∞, 0]`, DLMF §9.8(iii). -/
theorem airy_derivPhase_deriv_monotone :
    StrictMonoOn (deriv airyDerivPhase) (Iic 0) := by
  have hπ := Real.pi_pos
  rw [deriv_airyDerivPhase]
  have key : ∀ x : ℝ, x < 0 → x / (π * airyDerivModulus x ^ 2) =
      -1 / (π * (π * Real.sqrt π)⁻¹ * ((∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t) / (2 * (-x)) +
        ∫ t in Ioi (0 : ℝ), airyMod_kernel x t)) := by
    intro x hx
    have p2 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t :=
      airyMod_integral_pos (airyMod_kernel2_integrable x) fun t ht => by
        unfold airyMod_kernel2; positivity
    have p0 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel x t :=
      airyMod_integral_pos (airyMod_kernel_integrable x) (fun t ht => airyMod_kernel_pos x ht)
    have hN := pow_pos (airyDerivModulus_pos x) 2
    have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
    have hq : 0 < (∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t) / (2 * (-x)) +
        ∫ t in Ioi (0 : ℝ), airyMod_kernel x t := by
      have : 0 < (∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t) / (2 * (-x)) :=
        div_pos p2 (by linarith)
      linarith
    rw [div_eq_div_iff (by positivity) (by positivity), airyMod_derivSq_eq_integral]
    have : x ≠ 0 := hx.ne
    field_simp
    ring
  intro x (hx : x ≤ 0) y (hy : y ≤ 0) hxy
  have hxn : x < 0 := lt_of_lt_of_le hxy hy
  simp only
  rcases hy.lt_or_eq with hy' | rfl
  · rw [key x hxn, key y hy']
    have w0 : ∀ t, 0 < t → 0 < Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ) :=
      fun t _ => by positivity
    have w2 : ∀ t, 0 < t → 0 < Real.exp (-(t ^ 3 / 12)) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)) :=
      fun t _ => by positivity
    have i0 := airyMod_integral_exp_strictMono w0
      (fun a => (airyMod_integrableOn_exp a).congr_fun (fun t _ => rfl) measurableSet_Ioi) hxy
    have i2 := airyMod_integral_exp_strictMono w2 (fun a => airyMod_integrableOn_exp_pow a 2) hxy
    have p2 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel2 x t :=
      airyMod_integral_pos (airyMod_kernel2_integrable x) fun t ht => by
        unfold airyMod_kernel2; positivity
    have p0 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel x t :=
      airyMod_integral_pos (airyMod_kernel_integrable x) (fun t ht => airyMod_kernel_pos x ht)
    simp only [airyMod_kernel, airyMod_kernel2] at i0 i2 p0 p2 ⊢
    have hc : 0 < π * (π * Real.sqrt π)⁻¹ := by positivity
    have h2 : (∫ t in Ioi (0 : ℝ), Real.exp (x * t) * (Real.exp (-(t ^ 3 / 12)) *
        (t ^ 2 * t ^ (-(1 / 2) : ℝ)))) / (2 * -x) < (∫ t in Ioi (0 : ℝ), Real.exp (y * t) *
        (Real.exp (-(t ^ 3 / 12)) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)))) / (2 * -y) := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hq : ∀ z : ℝ, z < 0 → 0 < (∫ t in Ioi (0 : ℝ), Real.exp (z * t) *
        (Real.exp (-(t ^ 3 / 12)) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)))) / (2 * -z) +
        ∫ t in Ioi (0 : ℝ), Real.exp (z * t) * (Real.exp (-(t ^ 3 / 12)) * t ^ (-(1 / 2) : ℝ)) := by
      intro z hz
      have a2 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel2 z t :=
        airyMod_integral_pos (airyMod_kernel2_integrable z) fun t ht => by
          unfold airyMod_kernel2; positivity
      have a0 : 0 < ∫ t in Ioi (0 : ℝ), airyMod_kernel z t :=
        airyMod_integral_pos (airyMod_kernel_integrable z) (fun t ht => airyMod_kernel_pos z ht)
      simp only [airyMod_kernel, airyMod_kernel2] at a0 a2
      have : 0 < (∫ t in Ioi (0 : ℝ), Real.exp (z * t) *
          (Real.exp (-(t ^ 3 / 12)) * (t ^ 2 * t ^ (-(1 / 2) : ℝ)))) / (2 * -z) :=
        div_pos a2 (by linarith)
      linarith
    rw [neg_div, neg_div, neg_lt_neg_iff]
    exact one_div_lt_one_div_of_lt (mul_pos hc (hq x hxn))
      (mul_lt_mul_of_pos_left (add_lt_add h2 i0) hc)
  · have : 0 < airyDerivModulus x ^ 2 := pow_pos (airyDerivModulus_pos x) 2
    simp only [zero_div]
    exact div_neg_of_neg_of_pos hxn (by positivity)

/-- `|x|^{1/4} M(x)` is strictly decreasing on `(-∞, 0)`, DLMF §9.8(iii). -/
theorem airy_weighted_modulus_monotone :
    StrictAntiOn (fun x : ℝ => |x| ^ (1 / 4 : ℝ) * airyModulus x) (Iio 0) := by
  intro x (hx : x < 0) y (hy : y < 0) hxy
  have hπ := Real.pi_pos
  have hsq : ∀ z : ℝ, z < 0 → (|z| ^ (1 / 4 : ℝ) * airyModulus z) ^ 2 =
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * (Real.exp (-(u ^ 3 / (12 * (-z) ^ 3))) *
        u ^ (-(1 / 2) : ℝ))) / (π * Real.sqrt π) := by
    intro z hz
    rw [← airyMod_sqrt_mul_sq (neg_pos.mpr hz), neg_neg, mul_pow, abs_of_neg hz,
      ← Real.rpow_natCast, ← Real.rpow_mul (neg_pos.mpr hz).le]
    norm_num
  have hpos : ∀ z : ℝ, z < 0 → 0 ≤ |z| ^ (1 / 4 : ℝ) * airyModulus z := fun z _ =>
    mul_nonneg (by positivity) (airyModulus_pos z).le
  refine lt_of_pow_lt_pow_left₀ 2 (hpos x hx) ?_
  rw [hsq x hx, hsq y hy]
  refine div_lt_div_of_pos_right ?_ (by positivity)
  rw [← sub_pos, ← integral_sub (airyMod_scaled_integrable (by linarith)) (airyMod_scaled_integrable (by linarith))]
  refine airyMod_integral_pos ((airyMod_scaled_integrable (by linarith)).sub (airyMod_scaled_integrable (by linarith)))
    fun u hu => ?_
  have h3 : (-y) ^ 3 < (-x) ^ 3 := by
    have : 0 < -y := by linarith
    exact pow_lt_pow_left₀ (by linarith) this.le (by norm_num)
  have hy3 : 0 < (-y) ^ 3 := by have : 0 < -y := by linarith
                                positivity
  have hlt : u ^ 3 / (12 * (-x) ^ 3) < u ^ 3 / (12 * (-y) ^ 3) :=
    div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  have h1 := Real.exp_lt_exp.mpr (neg_lt_neg hlt)
  have h2 : 0 < Real.exp (-u) * u ^ (-(1 / 2) : ℝ) := by positivity
  nlinarith

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_phase_monotone :
    StrictAntiOn (airyPhase) (Iic 0) := by
  refine (strictAnti_of_deriv_neg fun x => ?_).strictAntiOn _
  rw [deriv_airyPhase]
  have := airyModulus_pos x; have := Real.pi_pos
  simp only [neg_lt_zero]; positivity

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_derivPhase_monotone :
    StrictAntiOn (airyDerivPhase) (Iic 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Iic 0) airyDerivPhase_continuous.continuousOn
    fun x hx => ?_
  rw [interior_Iic, mem_Iio] at hx
  rw [deriv_airyDerivPhase]
  have := airyDerivModulus_pos x; have := Real.pi_pos
  exact div_neg_of_neg_of_pos hx (by positivity)

/-! ### Termwise integration of the reciprocal expansions (phases) -/

/-- A function whose derivative is bounded by `K s^{p-1}` (`p < 0`) on `[R, ∞)` converges at
`+∞`, and its distance to the limit is at most `K s^p / (-p)`. -/
theorem airyMod_tendsto_of_deriv_bound {F f : ℝ → ℝ} {R K p : ℝ} (hR : 0 < R) (hp : p < 0)
    (hF : ∀ s, R ≤ s → HasDerivAt F (f s) s) (hf : ∀ s, R ≤ s → |f s| ≤ K * s ^ (p - 1)) :
    ∃ L, Tendsto F atTop (𝓝 L) ∧ ∀ s, R ≤ s → |F s - L| ≤ K * s ^ p / (-p) := by
  set Q : ℝ → ℝ := fun s => K * s ^ p / (-p)
  have hK : 0 ≤ K := by
    have h := (abs_nonneg _).trans (hf R le_rfl)
    have : 0 < R ^ (p - 1) := Real.rpow_pos_of_pos hR _
    nlinarith
  have hQ : ∀ s, R ≤ s → HasDerivAt Q (-(K * s ^ (p - 1))) s := fun s hs => by
    have hs0 : s ≠ 0 := (hR.trans_le hs).ne'
    have := ((Real.hasDerivAt_rpow_const (p := p) (Or.inl hs0)).const_mul K).div_const (-p)
    convert this using 1
    field_simp [hp.ne]
  have hQ0 : ∀ s, R ≤ s → 0 ≤ Q s := fun s hs => by
    have : 0 ≤ s ^ p := Real.rpow_nonneg (hR.le.trans hs) p
    exact div_nonneg (mul_nonneg hK this) (by linarith)
  have mono : ∀ {g g' : ℝ → ℝ}, (∀ s, R ≤ s → HasDerivAt g (g' s) s) →
      (∀ s, R ≤ s → 0 ≤ g' s) → MonotoneOn g (Ici R) := by
    intro g g' hg hg'
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici R)
      (fun s hs => (hg s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hg s (interior_subset hs)).hasDerivWithinAt) ?_
    intro s hs
    exact hg' s (interior_subset hs)
  have m1 : MonotoneOn (fun s => F s - Q s) (Ici R) :=
    mono (fun s hs => (hF s hs).sub (hQ s hs)) fun s hs => by
      have := (abs_le.mp (hf s hs)).1; linarith
  have m2 : MonotoneOn (fun s => -(F s + Q s)) (Ici R) :=
    mono (fun s hs => ((hF s hs).add (hQ s hs)).neg) fun s hs => by
      have := (abs_le.mp (hf s hs)).2; linarith
  have key : ∀ s t, R ≤ s → s ≤ t → |F t - F s| ≤ Q s := fun s t hs hst => by
    have h1 := m1 (show s ∈ Ici R from hs) (show t ∈ Ici R from hs.trans hst) hst
    have h2 := m2 (show s ∈ Ici R from hs) (show t ∈ Ici R from hs.trans hst) hst
    have h3 := hQ0 t (hs.trans hst)
    simp only at h1 h2
    rw [abs_le]; constructor <;> linarith
  have hQlim : Tendsto Q atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (y := -p) (by linarith)).const_mul K).div_const (-p)
    simp only [neg_neg, mul_zero, zero_div] at this
    exact this
  have hc : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (eventually_ge_atTop R).and (hQlim.eventually (gt_mem_nhds hε)) |>.exists_forall_of_atTop
    refine ⟨max N R, fun n hn => ?_⟩
    have hNR := (hN (max N R) (le_max_left _ _))
    rw [Real.dist_eq]
    exact (key _ _ hNR.1 hn).trans_lt hNR.2
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨L, hL, fun s hs => ?_⟩
  have ht : Tendsto (fun t => |F t - F s|) atTop (𝓝 |L - F s|) :=
    ((hL.sub_const (F s)).abs)
  have := le_of_tendsto ht (eventually_ge_atTop s |>.mono fun t hst => key s t hs hst)
  rwa [abs_sub_comm] at this


/-- `s^a (-s)^{-3k} = (-1)^k s^{a-3k}` for `s > 0`. -/
theorem airyMod_rpow_mul_zpow {s : ℝ} (hs : 0 < s) (a : ℝ) (k : ℕ) :
    s ^ a * (-s) ^ (-(3 * k : ℤ)) = (-1) ^ k * s ^ (a - 3 * k) := by
  rw [show (-(3 * k : ℤ)) = -((3 * k : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    neg_pow, show (-1 : ℝ) ^ (3 * k) = (-1) ^ k by rw [pow_mul]; norm_num,
    Real.rpow_sub hs, ← Real.rpow_natCast s (3 * k)]
  push_cast
  have : (0 : ℝ) < s ^ ((3 : ℝ) * k) := Real.rpow_pos_of_pos hs _
  have h1 : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  field_simp
  exact h1.symm

/-- Derivative of the primitive scale `(2/3) s^{3/2} (-s)^{-3k} / (1 - 2k)`. -/
theorem airyMod_hasDerivAt_sigma {s : ℝ} (hs : 0 < s) (k : ℕ) (c : ℝ) :
    HasDerivAt (fun s : ℝ => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * (c / (1 - 2 * k)))
      (s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * c) s := by
  have hk : (1 - 2 * (k : ℝ)) ≠ 0 := by
    intro h
    have : (2 : ℝ) * k = 1 := by linarith
    have h2 : (2 * k : ℕ) = 1 := by exact_mod_cast this
    omega
  have e : ∀ u : ℝ, 0 < u → 2 / 3 * u ^ (3 / 2 : ℝ) * (-u) ^ (-(3 * k : ℤ)) * (c / (1 - 2 * k)) =
      2 / 3 * (c / (1 - 2 * k)) * (-1) ^ k * u ^ ((3 / 2 : ℝ) - 3 * k) := fun u hu => by
    rw [mul_assoc (2 / 3 : ℝ), airyMod_rpow_mul_zpow hu]; ring
  have h := ((Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ) - 3 * k) (Or.inl hs.ne')).const_mul
    (2 / 3 * (c / (1 - 2 * k)) * (-1) ^ k))
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [lt_mem_nhds hs] with u hu
    exact e u hu
  · rw [airyMod_rpow_mul_zpow hs, show (3 / 2 : ℝ) - 3 * k - 1 = 1 / 2 - 3 * k by ring]
    field_simp

/-- `|s^a (-s)^{-3k}| = s^{a-3k}`. -/
theorem airyMod_abs_rpow_mul_zpow {s : ℝ} (hs : 0 < s) (a : ℝ) (k : ℕ) :
    |s ^ a * (-s) ^ (-(3 * k : ℤ))| = s ^ (a - 3 * k) := by
  rw [airyMod_rpow_mul_zpow hs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (Real.rpow_pos_of_pos hs _)]

/-- Each term `(2/3) a s^{3/2} (-s)^{-3(k+1)}` of the integrated expansion tends to `0`. -/
private lemma airyMod_tendsto_sigma_succ (k : ℕ) (a : ℝ) :
    Tendsto (fun s : ℝ => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * ((k + 1 : ℕ) : ℤ))) * a)
      atTop (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => 2 / 3 * a * (-1) ^ (k + 1) *
      s ^ ((3 / 2 : ℝ) - 3 * ((k + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have hq : (3 / 2 : ℝ) - 3 * ((k + 1 : ℕ) : ℝ) = -(3 * ((k + 1 : ℕ) : ℝ) - 3 / 2) := by ring
    rw [hq]
    simpa using (tendsto_rpow_neg_atTop (y := 3 * ((k + 1 : ℕ) : ℝ) - 3 / 2)
      (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).const_mul
        (2 / 3 * a * (-1) ^ (k + 1))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [mul_assoc (2 / 3 : ℝ) (s ^ (3 / 2 : ℝ)), airyMod_rpow_mul_zpow hs]; ring

/-- **Termwise integration of an expansion at `+∞`.** If `G' = g` and
`g(s) ~ ∑ c_k s^{1/2} (-s)^{-3k}`, then `G(s) - L ~ ∑ c_k/(1-2k) · (2/3) s^{3/2} (-s)^{-3k}` for a
constant `L = lim (G(s) - (2/3) c₀ s^{3/2})`. -/
theorem airyMod_expansion_of_deriv {G g : ℝ → ℝ} {c : ℕ → ℝ}
    (hG : ∀ s, 0 < s → HasDerivAt G (g s) s)
    (hg : ∀ N : ℕ, (fun s => g s - ∑ k ∈ Finset.range N, s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * c k)
      =O[atTop] (fun s => s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ)))) :
    ∃ L, Tendsto (fun s => G s - 2 / 3 * s ^ (3 / 2 : ℝ) * c 0) atTop (𝓝 L) ∧
      ∀ N : ℕ, (fun s => G s - L - ∑ k ∈ Finset.range N,
        2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * (c k / (1 - 2 * k))) =O[atTop]
        (fun s => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  set σ : ℕ → ℝ → ℝ := fun k s => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * (c k / (1 - 2 * k))
  set F : ℕ → ℝ → ℝ := fun N s => G s - ∑ k ∈ Finset.range N, σ k s
  have hF : ∀ N s, 0 < s → HasDerivAt (F N) (g s - ∑ k ∈ Finset.range N,
      s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * c k) s := fun N s hs =>
    (hG s hs).sub (HasDerivAt.fun_sum fun k _ => airyMod_hasDerivAt_sigma hs k (c k))
  -- limits with explicit bounds for `N ≥ 1`
  have hlim : ∀ N : ℕ, 1 ≤ N → ∃ L K R, 0 < R ∧ Tendsto (F N) atTop (𝓝 L) ∧
      ∀ s, R ≤ s → |F N s - L| ≤ K * s ^ ((3 / 2 : ℝ) - 3 * N) / (-((3 / 2 : ℝ) - 3 * N)) := by
    intro N hN
    obtain ⟨K, hK⟩ := (hg N).bound
    obtain ⟨R, hR⟩ := eventually_atTop.mp hK
    have hp : (3 / 2 : ℝ) - 3 * N < 0 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    obtain ⟨L, hL1, hL2⟩ := airyMod_tendsto_of_deriv_bound (F := F N) (R := max R 1) (K := K)
      (by positivity) hp (fun s hs => hF N s (by linarith [le_max_right R 1]))
      (fun s hs => by
        have hs0 : 0 < s := by linarith [le_max_right R 1]
        have := hR s (le_trans (le_max_left _ _) hs)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, airyMod_abs_rpow_mul_zpow hs0] at this
        rwa [show (3 / 2 : ℝ) - 3 * N - 1 = 1 / 2 - 3 * N by ring])
    exact ⟨L, K, max R 1, by positivity, hL1, hL2⟩
  obtain ⟨L, K₁, R₁, hR₁, hL, hb₁⟩ := hlim 1 le_rfl
  have hF1 : F 1 = fun s => G s - 2 / 3 * s ^ (3 / 2 : ℝ) * c 0 := by
    funext s; simp [F, σ]
  have hσ0 : ∀ k, Tendsto (σ (k + 1)) atTop (𝓝 0) := fun k =>
    airyMod_tendsto_sigma_succ k _
  have hsame : ∀ N : ℕ, 1 ≤ N → Tendsto (F N) atTop (𝓝 L) := by
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h : F (M + 1) = fun s => F 1 s - ∑ k ∈ Finset.range M, σ (k + 1) s := by
      funext s; simp only [F, Finset.sum_range_succ']; ring
    rw [h]
    simpa using hL.sub (tendsto_finsetSum _ fun k _ => hσ0 k)
  refine ⟨L, hF1 ▸ hL, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- `G - L = (F 1 - L) + σ₀`
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, CharP.cast_eq_zero, mul_zero,
      neg_zero, zpow_zero, mul_one]
    have h1 : (fun s => F 1 s - L) =O[atTop] (fun s : ℝ => 2 / 3 * s ^ (3 / 2 : ℝ)) := by
      refine ((hL.sub_const L).isBigO_one ℝ).trans ?_
      refine IsBigO.of_bound (3 / 2) ?_
      filter_upwards [eventually_ge_atTop 1] with s hs
      rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : 1 ≤ s ^ (3 / 2 : ℝ) := Real.one_le_rpow hs (by norm_num)
      nlinarith
    have h2 : (fun s => 2 / 3 * s ^ (3 / 2 : ℝ) * c 0) =O[atTop] (fun s : ℝ => 2 / 3 * s ^ (3 / 2 : ℝ)) :=
      IsBigO.of_bound |c 0| (Eventually.of_forall fun s => by
        rw [norm_mul, Real.norm_eq_abs (c 0), mul_comm])
    refine (h1.add h2).congr' (Eventually.of_forall fun s => ?_) EventuallyEq.rfl
    simp [F, σ]
    ring
  · obtain ⟨L', K, R, hR, hL', hb⟩ := hlim N hN
    have hLL : L' = L := tendsto_nhds_unique hL' (hsame N hN)
    subst hLL
    refine IsBigO.of_bound (K * (3 / 2) / (-((3 / 2 : ℝ) - 3 * N))) ?_
    filter_upwards [eventually_ge_atTop R] with s hs
    have hs0 : 0 < s := hR.trans_le hs
    have hb' := hb s hs
    have e : G s - L' - ∑ k ∈ Finset.range N, σ k s = F N s - L' := by simp only [F]; ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, e, mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3),
      airyMod_abs_rpow_mul_zpow hs0]
    have : (0 : ℝ) < -((3 / 2 : ℝ) - 3 * N) := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    calc |F N s - L'| ≤ K * s ^ ((3 / 2 : ℝ) - 3 * N) / (-((3 / 2 : ℝ) - 3 * N)) := hb'
      _ = K * (3 / 2) / (-((3 / 2 : ℝ) - 3 * N)) * (2 / 3 * s ^ ((3 / 2 : ℝ) - 3 * N)) := by
        field_simp


/-- The reciprocal of the formal series `∑ c_k X^k` with `c₀ = 1` has coefficients
`airyReciprocalCoeff c`. -/
theorem airyMod_coeff_recip_mk {c : ℕ → ℝ} (hc : c 0 = 1) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk c)⁻¹ = airyReciprocalCoeff c n := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.mk c) ≠ 0 := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc]
  have key : PowerSeries.mk (airyReciprocalCoeff c) = (PowerSeries.mk c)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one h0]
    ext m
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rcases m with _ | m
    · simp [airyReciprocalCoeff, hc]
    · rw [Finset.sum_range_succ]
      simp only [PowerSeries.coeff_mk, Nat.sub_self, hc, mul_one, PowerSeries.coeff_one,
        Nat.succ_ne_zero, ite_false]
      rw [airyReciprocalCoeff]
      rw [← Finset.sum_range_reflect]
      have : ∀ j ∈ Finset.range (m + 1), airyReciprocalCoeff c (m + 1 - 1 - j) * c (m + 1 - (m + 1 - 1 - j)) =
          c (j + 1) * airyReciprocalCoeff c (m - j) := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [show m + 1 - 1 - j = m - j by omega, show m + 1 - (m - j) = j + 1 by omega, mul_comm]
      rw [Finset.sum_congr rfl this]
      ring
  rw [← key, PowerSeries.coeff_mk]

/-- Convert an expansion `F(x) ~ ∑ c_k p(x) x^{-3k}` at `-∞` to an asymptotic power series of
`F(-s)/p(-s)` in `w = (-s)^{-3}` at `+∞`. -/
theorem airyMod_powerSeries_of_expansion {F p : ℝ → ℝ} {c : ℕ → ℝ}
    (hF : HasAsymptoticExpansion atBot (fun k (x : ℝ) => p x * x ^ (-(3 * k : ℤ))) c F)
    (hp : ∀ x < 0, p x ≠ 0) :
    HasAsymptoticPowerSeries atTop (fun s : ℝ => (-s) ^ (-(3 : ℤ))) (PowerSeries.mk c)
      (fun s => F (-s) / p (-s)) := by
  intro N
  have h := ((hF N).comp_tendsto tendsto_neg_atTop_atBot).mul
    (isBigO_refl (fun s : ℝ => (p (-s))⁻¹) atTop)
  have hz : ∀ (s : ℝ) (k : ℕ), (-s) ^ (-(3 * k : ℤ)) = ((-s) ^ (-(3 : ℤ))) ^ k := fun s k => by
    rw [← zpow_natCast, ← zpow_mul]; congr 1
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with s hs
    have hp0 := hp (-s) (by linarith)
    simp only [Function.comp_apply, smul_eq_mul, PowerSeries.coeff_mk]
    rw [sub_mul, Finset.sum_mul]
    simp only [hz]
    congr 1
    field_simp
  · filter_upwards [eventually_gt_atTop 0] with s hs
    have hp0 := hp (-s) (by linarith)
    simp only [Function.comp_apply]
    rw [hz]
    field_simp

/-- **Reciprocal expansion of an integrand.** If `F(x) ~ ∑ c_k p(x) x^{-3k}` at `-∞` with
`c₀ = 1` and `g(s) = s^{1/2} p(-s)/F(-s)`, then `g(s) ~ ∑ r_k s^{1/2} (-s)^{-3k}` with
`r = airyReciprocalCoeff c`. -/
theorem airyMod_integrand_expansion {F p g : ℝ → ℝ} {c : ℕ → ℝ}
    (hF : HasAsymptoticExpansion atBot (fun k (x : ℝ) => p x * x ^ (-(3 * k : ℤ))) c F)
    (hp : ∀ x < 0, p x ≠ 0) (hc : c 0 = 1)
    (hg : ∀ s, 0 < s → g s = s ^ (1 / 2 : ℝ) * (F (-s) / p (-s))⁻¹) (N : ℕ) :
    (fun s => g s - ∑ k ∈ Finset.range N, s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) *
      airyReciprocalCoeff c k) =O[atTop] (fun s => s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  have hw : Tendsto (fun s : ℝ => (-s) ^ (-(3 : ℤ))) atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ => -((s ^ 3)⁻¹)) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)).inv_tendsto_atTop).neg
    refine this.congr fun s => ?_
    rw [zpow_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, neg_pow]; ring_nf
  have h0 : PowerSeries.constantCoeff (PowerSeries.mk c) ≠ 0 := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc]
  have hi := ((airyMod_powerSeries_of_expansion hF hp).recip hw h0) N
  have hz : ∀ (s : ℝ) (k : ℕ), (-s) ^ (-(3 * k : ℤ)) = ((-s) ^ (-(3 : ℤ))) ^ k := fun s k => by
    rw [← zpow_natCast, ← zpow_mul]; congr 1
  have h := (isBigO_refl (fun s : ℝ => s ^ (1 / 2 : ℝ)) atTop).mul hi
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [smul_eq_mul, airyMod_coeff_recip_mk hc, hg s hs]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hz]; ring
  · filter_upwards with s
    rw [hz]

/-- As `x → -∞`, `M²(x) ∼ (1/(π(-x)^{1/2})) ∑ₖ aₖ x^{-3k}` with the coefficients
`airyModulusCoeff` (DLMF 9.8.20). -/
@[dlmf 9.8.E20]
theorem airyModulus_asymptotic :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => (-x) ^ (-1 / 2 : ℝ) / π * x ^ (-(3 * k : ℤ)))
      airyModulusCoeff (fun x => airyModulus x ^ 2) := by
  intro N
  refine IsBigO.of_bound |airyModulusCoeff N| ?_
  filter_upwards [eventually_lt_atBot 0] with x hx
  have h := (airyMod_sq_error_bound hx N).1
  simp only [smul_eq_mul, Real.norm_eq_abs]
  have e : ∑ n ∈ Finset.range N, (-x) ^ (-1 / 2 : ℝ) / π * x ^ (-(3 * n : ℤ)) * airyModulusCoeff n =
      (-x) ^ (-1 / 2 : ℝ) / π * airyModulusSum false N x := by
    simp only [airyModulusSum, Bool.false_eq_true, ite_false, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [e]
  calc _ ≤ _ := h
    _ = _ := by simp only [abs_mul]; ring

/-- As `x → -∞`, `N²(x) ∼ ((-x)^{1/2}/π) ∑ₖ bₖ x^{-3k}` with the coefficients
`airyDerivModulusCoeff` (DLMF 9.8.21). -/
@[dlmf 9.8.E21]
theorem airyDerivModulus_asymptotic :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * k : ℤ)))
      airyDerivModulusCoeff (fun x => airyDerivModulus x ^ 2) := by
  have step : ∀ N : ℕ, (fun x => airyDerivModulus x ^ 2 - ∑ n ∈ Finset.range (N + 1),
      ((-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * n : ℤ))) • airyDerivModulusCoeff n) =O[atBot]
      (fun x : ℝ => (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * (N + 1 : ℕ) : ℤ))) := fun N => by
    refine IsBigO.of_bound (|airyModulusCoeff (N + 1)| + π * ((π * Real.sqrt π)⁻¹ / 2 *
        (Real.Gamma ((3 * N + 2 : ℕ) + 1 / 2) / (12 ^ N * (Nat.factorial N : ℝ))))) ?_
    filter_upwards [eventually_lt_atBot 0] with x hx
    simp only [smul_eq_mul, Real.norm_eq_abs]
    exact airyMod_derivSq_error hx N
  intro N
  rcases N with _ | N
  · -- `N² = O(φ₀)` from the one-term bound
    have h1 := step 0
    have hφ : (fun x : ℝ => (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * (0 + 1 : ℕ) : ℤ))) =O[atBot]
        (fun x : ℝ => (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * (0 : ℕ) : ℤ))) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_le_atBot (-1)] with x hx
      simp only [Nat.cast_zero, mul_zero, neg_zero, zpow_zero, mul_one, zero_add, Nat.cast_one,
        one_mul, Real.norm_eq_abs, abs_mul]
      have : |x ^ (-(3 : ℤ))| ≤ 1 := by
        rw [abs_zpow, zpow_neg]
        exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by rw [abs_of_neg (by linarith)]; linarith)
          (by norm_num))
      have h0 : 0 ≤ |(-x) ^ (1 / 2 : ℝ) / π| := abs_nonneg _
      nlinarith
    have h0 : (fun x : ℝ => ∑ n ∈ Finset.range (0 + 1),
        ((-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * n : ℤ))) • airyDerivModulusCoeff n) =O[atBot]
        (fun x : ℝ => (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * (0 : ℕ) : ℤ))) := by
      refine IsBigO.of_bound |airyDerivModulusCoeff 0| (Eventually.of_forall fun x => ?_)
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, smul_eq_mul, Real.norm_eq_abs,
        abs_mul]
      push_cast
      ring_nf
      rfl
    simpa using (h1.trans hφ).add h0
  · simpa using step N

/-- Signed first-neglected-term bounds, DLMF §9.8(iv). -/
theorem airyModulus_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 0 ≤ N) :
    |(airyModulus x ^ 2) - ((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusSum false N x| ≤ |((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusCoeff N * x ^ (-(3 * N : ℤ))| ∧
      0 ≤ ((airyModulus x ^ 2) - ((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusSum false N x) * (((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusCoeff N * x ^ (-(3 * N : ℤ))) :=
  airyMod_sq_error_bound hx N

/-- For `x < 0`, the error of the `θ` expansion after `N + 1` terms is bounded by, and has
the sign of, the first neglected term, DLMF §9.8(iv). -/
theorem airyPhase_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 0 ≤ N) :
    |(airyPhase x - (π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum false (N + 1) x| ≤ |(2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))| ∧
      0 ≤ ((airyPhase x - (π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum false (N + 1) x) * ((2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))) := by
  sorry

/-- Signed first-neglected-term bounds, DLMF §9.8(iv). -/
theorem airyDerivModulus_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 1 ≤ N) :
    |(airyDerivModulus x ^ 2) - ((-x) ^ (1 / 2 : ℝ) / π) * airyModulusSum true N x| ≤ |((-x) ^ (1 / 2 : ℝ) / π) * airyDerivModulusCoeff N * x ^ (-(3 * N : ℤ))| ∧
      0 ≤ ((airyDerivModulus x ^ 2) - ((-x) ^ (1 / 2 : ℝ) / π) * airyModulusSum true N x) * (((-x) ^ (1 / 2 : ℝ) / π) * airyDerivModulusCoeff N * x ^ (-(3 * N : ℤ))) := by
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ x = -s := ⟨-x, by linarith, by ring⟩
  rw [neg_neg]
  have hπ := Real.pi_pos
  have hc : 0 < (π * Real.sqrt π)⁻¹ := by positivity
  rw [airyMod_derivSq_error_integral hs K, ← airyMod_derivMod_term_identity K hs]
  set J := ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) * t ^ (-(1 / 2) : ℝ) *
    (t ^ 2 * airyMod_rem K (t ^ 3 / 12) / 4 - airyMod_rem (K + 1) (t ^ 3 / 12) / (2 * t))
  set c₀ : ℝ := (6 * K + 7) / (24 * 12 ^ K * Nat.factorial (K + 1))
  set G := Real.Gamma ((3 * K + 2 : ℕ) + 1 / 2) * s ^ (-(((3 * K + 2 : ℕ) : ℝ) + 1 / 2)) * c₀
  have hI := airyMod_mom_integral (3 * K + 2) hs
  have hJ1 : 0 ≤ (-1) ^ K * J := by
    rw [← integral_const_mul]
    exact setIntegral_nonneg measurableSet_Ioi fun t (ht : 0 < t) =>
      (airyMod_derivErr_pointwise s K ht).1
  have hJ2 : (-1) ^ K * J ≤ G := by
    rw [show G = ∫ t in Ioi (0 : ℝ), Real.exp (-s * t) *
        t ^ ((((3 * K + 2 : ℕ) : ℝ) + 1 / 2) - 1) * c₀ by
      rw [integral_mul_const, hI.2], ← integral_const_mul]
    exact setIntegral_mono_on ((airyMod_derivErr_integrable s hs K).const_mul _)
      (hI.1.mul_const _) measurableSet_Ioi fun t (ht : 0 < t) =>
        (airyMod_derivErr_pointwise s K ht).2
  have hsq : ((-1 : ℝ) ^ K) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hab : |(-1 : ℝ) ^ K| = 1 := by simp
  have hG : 0 ≤ G := hJ1.trans hJ2
  constructor
  · rw [show (π * Real.sqrt π)⁻¹ * J = (-1) ^ K * ((π * Real.sqrt π)⁻¹ * ((-1) ^ K * J)) by
      rw [← mul_assoc ((-1 : ℝ) ^ K), mul_comm ((-1 : ℝ) ^ K), mul_assoc, ← mul_assoc ((-1 : ℝ) ^ K),
        ← pow_two, hsq, one_mul],
      show (π * Real.sqrt π)⁻¹ * G * (-1) ^ K = (-1) ^ K * ((π * Real.sqrt π)⁻¹ * G) by ring,
      abs_mul ((-1 : ℝ) ^ K), abs_mul ((-1 : ℝ) ^ K), hab, one_mul, one_mul,
      abs_of_nonneg (mul_nonneg hc.le hJ1), abs_of_nonneg (mul_nonneg hc.le hG)]
    exact mul_le_mul_of_nonneg_left hJ2 hc.le
  · have : (π * Real.sqrt π)⁻¹ * J * ((π * Real.sqrt π)⁻¹ * G * (-1) ^ K) =
        ((π * Real.sqrt π)⁻¹ * ((-1) ^ K * J)) * ((π * Real.sqrt π)⁻¹ * G) := by ring
    rw [this]
    exact mul_nonneg (mul_nonneg hc.le hJ1) (mul_nonneg hc.le hG)

/-- For `x < 0`, the error of the `φ` expansion after `N + 1` terms is bounded by, and has
the sign of, the first neglected term, DLMF §9.8(iv). -/
theorem airyDerivPhase_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 0 ≤ N) :
    |(airyDerivPhase x - (-π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum true (N + 1) x| ≤ |(2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyDerivPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))| ∧
      0 ≤ ((airyDerivPhase x - (-π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum true (N + 1) x) * ((2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyDerivPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))) := by
  sorry

/-! ### The phase expansions 9.8.22 and 9.8.23 -/
/-- If `u → 1`, `u sin θ - sin β → 0`, `u cos θ - cos β → 0` and `θ - β → L`, then
`cos L = 1`. -/
theorem airyMod_cos_eq_one_of_limits {u θ β : ℝ → ℝ} {L : ℝ} (hu : Tendsto u atTop (𝓝 1))
    (hs : Tendsto (fun s => u s * Real.sin (θ s) - Real.sin (β s)) atTop (𝓝 0))
    (hc : Tendsto (fun s => u s * Real.cos (θ s) - Real.cos (β s)) atTop (𝓝 0))
    (hL : Tendsto (fun s => θ s - β s) atTop (𝓝 L)) : Real.cos L = 1 := by
  have key : ∀ s, u s * Real.cos (θ s - β s) = 1 +
      (u s * Real.cos (θ s) - Real.cos (β s)) * Real.cos (β s) +
      (u s * Real.sin (θ s) - Real.sin (β s)) * Real.sin (β s) := fun s => by
    rw [Real.cos_sub]; linear_combination Real.sin_sq_add_cos_sq (β s)
  have t1 : Tendsto (fun s => (u s * Real.cos (θ s) - Real.cos (β s)) * Real.cos (β s))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun s => ?_) (by simpa using hc.norm)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using Real.abs_cos_le_one _)
  have t2 : Tendsto (fun s => (u s * Real.sin (θ s) - Real.sin (β s)) * Real.sin (β s))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun s => ?_) (by simpa using hs.norm)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using Real.abs_sin_le_one _)
  have h1 : Tendsto (fun s => u s * Real.cos (θ s - β s)) atTop (𝓝 1) := by
    simp only [key]; simpa using (tendsto_const_nhds.add t1).add t2
  have h2 : Tendsto (fun s => u s * Real.cos (θ s - β s)) atTop (𝓝 (1 * Real.cos L)) :=
    hu.mul ((Real.continuous_cos.tendsto L).comp hL)
  have := tendsto_nhds_unique h2 h1
  linarith

/-- A real `x` with `cos x = 1` and `|x| < 2π` is `0`. -/
theorem airyMod_eq_zero_of_cos_eq_one {x : ℝ} (h : Real.cos x = 1) (hx : |x| < 2 * π) : x = 0 := by
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff x).mp h
  have hπ := Real.pi_pos
  rw [← hn] at hx ⊢
  have h1 : |(n : ℝ)| < 1 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hx
    nlinarith
  have h2 : |n| < 1 := by exact_mod_cast h1
  have : n = 0 := by have := abs_lt.mp h2; omega
  simp [this]

/-- Bounds for the limit `L` of `E` from derivative bounds `a ≤ E' ≤ b` on `(0,1)` and
`|E'(s)| ≤ K s^{-5/2}` on `[1,∞)`. -/
theorem airyMod_limit_bounds {E e : ℝ → ℝ} {L a b K : ℝ} (hc : ContinuousOn E (Ici 0))
    (hd : ∀ s, 0 < s → HasDerivAt E (e s) s) (hab : ∀ s, 0 < s → s < 1 → a ≤ e s ∧ e s ≤ b)
    (hK : ∀ s, 1 ≤ s → |e s| ≤ K * s ^ (-(5 / 2) : ℝ)) (hL : Tendsto E atTop (𝓝 L)) :
    E 0 + a - 2 / 3 * K ≤ L ∧ L ≤ E 0 + b + 2 / 3 * K := by
  have hc' : ContinuousOn E (Icc 0 1) := hc.mono Icc_subset_Ici_self
  have mono : ∀ {g g' : ℝ → ℝ}, ContinuousOn g (Icc 0 1) → (∀ s, 0 < s → s < 1 → HasDerivAt g (g' s) s) →
      (∀ s, 0 < s → s < 1 → 0 ≤ g' s) → g 0 ≤ g 1 := by
    intro g g' hgc hg hg'
    have hm : MonotoneOn g (Icc 0 1) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := g') (convex_Icc 0 1) hgc
        (fun s hs => ?_) (fun s hs => ?_)
      · rw [interior_Icc] at hs; exact (hg s hs.1 hs.2).hasDerivWithinAt
      · rw [interior_Icc] at hs; exact hg' s hs.1 hs.2
    exact hm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have m1 := mono (g := fun s => E s - a * s) (g' := fun s => e s - a)
    (hc'.sub (continuousOn_const.mul continuousOn_id))
    (fun s hs _ => by convert (hd s hs).sub ((hasDerivAt_id s).const_mul a) using 1 <;> first | rfl | ring)
    (fun s hs hs1 => by linarith [(hab s hs hs1).1])
  have m2 := mono (g := fun s => b * s - E s) (g' := fun s => b - e s)
    ((continuousOn_const.mul continuousOn_id).sub hc')
    (fun s hs _ => by convert ((hasDerivAt_id s).const_mul b).sub (hd s hs) using 1 <;> first | rfl | ring)
    (fun s hs hs1 => by linarith [(hab s hs hs1).2])
  simp only [mul_zero, sub_zero, mul_one, zero_sub] at m1 m2
  obtain ⟨L', hL', hb⟩ := airyMod_tendsto_of_deriv_bound (F := E) (f := e) (R := 1) (K := K)
    (p := -(3 / 2)) one_pos (by norm_num) (fun s hs => hd s (by linarith))
    (fun s hs => by rw [show (-(3 / 2) : ℝ) - 1 = -(5 / 2) by norm_num]; exact hK s hs)
  have hLL := tendsto_nhds_unique hL' hL
  subst hLL
  have h1 := hb 1 le_rfl
  rw [Real.one_rpow, mul_one] at h1
  rw [abs_le] at h1
  constructor <;> linarith [h1.1, h1.2]


/-- `(-s)^{-3k} = (-(s³)⁻¹)^k`. -/
theorem airyMod_neg_zpow (s : ℝ) (k : ℕ) : (-s) ^ (-(3 * k : ℤ)) = (-(s ^ 3)⁻¹) ^ k := by
  rw [show (-(3 * k : ℤ)) = -((3 * k : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    pow_mul, ← inv_pow, neg_pow s 3, show (-1 : ℝ) ^ 3 = -1 by norm_num, neg_one_mul, inv_neg]

/-- The first coefficients of the expansion of `M²`. -/
theorem airyMod_coeff_values : airyModulusCoeff 0 = 1 ∧ airyModulusCoeff 1 = 5 / 32 ∧
    0 < airyModulusCoeff 2 := by
  refine ⟨by simp [airyModulusCoeff], by norm_num [airyModulusCoeff, Finset.prod_range_succ], ?_⟩
  unfold airyModulusCoeff
  refine div_pos (Finset.prod_pos fun j _ => by positivity) (by positivity)

/-- Two-sided bounds for `π s^{1/2} M(-s)²`: `1 - 5/(32 s³) ≤ π s^{1/2} M(-s)² < 1`. -/
theorem airyMod_modulus_bounds {s : ℝ} (hs : 0 < s) :
    1 - 5 / 32 * (s ^ 3)⁻¹ ≤ π * s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2 ∧
      π * s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2 < 1 := by
  have hπ := Real.pi_pos
  obtain ⟨c0, c1, c2⟩ := airyMod_coeff_values
  have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hqi : s ^ (-1 / 2 : ℝ) = (s ^ (1 / 2 : ℝ))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.le]
  constructor
  · have h := (airyModulus_error (x := -s) (by linarith) (N := 2) (by norm_num)).2
    rw [neg_neg] at h
    simp only [airyModulusSum, Finset.sum_range_succ, Finset.sum_range_zero, ite_false,
      Bool.false_eq_true, airyMod_neg_zpow, c0, c1, hqi] at h
    have hw : 0 < (s ^ 3)⁻¹ := by positivity
    have hpos : 0 < (s ^ (1 / 2 : ℝ))⁻¹ / π * airyModulusCoeff 2 * (-(s ^ 3)⁻¹) ^ 2 := by
      have : 0 < (-(s ^ 3)⁻¹) ^ 2 := by rw [neg_sq]; positivity
      positivity
    have h' := (mul_nonneg_iff_of_pos_right hpos).mp h
    simp only [pow_zero, pow_one, mul_one, zero_add] at h'
    have : (s ^ (1 / 2 : ℝ))⁻¹ / π * (1 + 5 / 32 * -(s ^ 3)⁻¹) ≤ airyModulus (-s) ^ 2 := by
      linarith
    have e : π * s ^ (1 / 2 : ℝ) * ((s ^ (1 / 2 : ℝ))⁻¹ / π * (1 + 5 / 32 * -(s ^ 3)⁻¹)) =
        1 - 5 / 32 * (s ^ 3)⁻¹ := by field_simp; ring
    rw [← e]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · have := airyMod_sqrt_mul_sq_lt hs
    calc π * s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2 = π * (s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2) := by ring
      _ < π * (1 / π) := by gcongr
      _ = 1 := by field_simp


/-- If `f = O(s^b)` and `a + b < 0`, then `c s^a f(s) → 0`. -/
theorem airyMod_tendsto_rpow_mul {f : ℝ → ℝ} {a b : ℝ} (c : ℝ) (hab : a + b < 0)
    (hf : f =O[atTop] (fun s => s ^ b)) : Tendsto (fun s => c * s ^ a * f s) atTop (𝓝 0) := by
  refine ((isBigO_refl (fun s => c * s ^ a) atTop).mul hf).trans_tendsto ?_
  have h := (tendsto_rpow_neg_atTop (y := -(a + b)) (by linarith)).const_mul c
  rw [mul_zero, neg_neg] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [Real.rpow_add hs]; ring

/-- `Ai(-s) = π^{-1/2} s^{-1/4} cos(ζ - π/4) + O(s^{-7/4})`, real form. -/
theorem airyMod_aiReal_neg_sub :
    (fun s : ℝ => airyAiReal (-s) - s ^ (-(1 / 4) : ℝ) / Real.sqrt π * Real.cos (airyZeta s - π / 4))
      =O[atTop] (fun s : ℝ => s ^ (-(7 / 4) : ℝ)) := by
  refine (airyMod_ai_neg_sub.norm_left.congr_left fun s => ?_).of_norm_left
  rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring, airyAi_ofReal_eq, ← ofReal_sub,
    norm_real]

/-- `Bi(-s) = -π^{-1/2} s^{-1/4} sin(ζ - π/4) + O(s^{-7/4})`, real form. -/
theorem airyMod_biReal_neg_sub :
    (fun s : ℝ => airyBiReal (-s) + s ^ (-(1 / 4) : ℝ) / Real.sqrt π * Real.sin (airyZeta s - π / 4))
      =O[atTop] (fun s : ℝ => s ^ (-(7 / 4) : ℝ)) := by
  refine (airyMod_bi_neg_sub.norm_left.congr_left fun s => ?_).of_norm_left
  rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring, airyBi_ofReal_eq, ← ofReal_add,
    norm_real]

/-- `√(π s^{1/2} M²) = √π s^{1/4} M` for `s > 0`. -/
theorem airyMod_sqrt_eq {s m : ℝ} (hs : 0 < s) (hm : 0 ≤ m) (a : ℝ) :
    Real.sqrt (π * s ^ a * m ^ 2) = Real.sqrt π * s ^ (a / 2) * m := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hm,
    Real.sqrt_eq_rpow (s ^ a), ← Real.rpow_mul hs.le]
  ring_nf

/-- The phase `θ(-s)` has derivative `1/(π M(-s)²)`. -/
theorem airyMod_phase_hasDerivAt (s : ℝ) :
    HasDerivAt (fun s => airyPhase (-s)) (1 / (π * airyModulus (-s) ^ 2)) s := by
  convert (hasDerivAt_airyPhase (-s)).comp s (hasDerivAt_neg s) using 1 <;> first | rfl | ring

/-- Reciprocal expansion of `1/(π M(-s)²)` as `s → ∞`. -/
theorem airyMod_phase_integrand (N : ℕ) :
    (fun s => 1 / (π * airyModulus (-s) ^ 2) - ∑ k ∈ Finset.range N,
      s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * airyReciprocalCoeff airyModulusCoeff k) =O[atTop]
      (fun s => s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  refine airyMod_integrand_expansion (F := fun x => airyModulus x ^ 2)
    (p := fun x => (-x) ^ (-1 / 2 : ℝ) / π) airyModulus_asymptotic
    (fun x hx => div_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne' Real.pi_ne_zero)
    airyMod_coeff_values.1 (fun s hs => ?_) N
  have hM := (airyModulus_pos (-s)).ne'
  have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  simp only [neg_neg]
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.le]
  field_simp

/-- The phase expansion at `+∞` in the variable `s = -x`, with an undetermined constant. -/
theorem airyMod_phase_expansion_s : ∃ L, Tendsto (fun s => airyPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ))
      atTop (𝓝 L) ∧
    ∀ N : ℕ, (fun s => airyPhase (-s) - L - ∑ k ∈ Finset.range N,
      2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * airyPhaseCoeff k) =O[atTop]
      (fun s => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  obtain ⟨L, hL, hN⟩ := airyMod_expansion_of_deriv (fun s _ => airyMod_phase_hasDerivAt s)
    airyMod_phase_integrand
  refine ⟨L, by simpa [airyReciprocalCoeff] using hL, fun N => ?_⟩
  simpa [airyPhaseCoeff] using hN N

/-- Explicit bounds on the constant `L` of the phase expansion. -/
private lemma airyMod_phase_limit_bounds {L : ℝ}
    (hL : Tendsto (fun s => airyPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    π / 6 + 0 - 2 / 3 * (5 / 27) ≤ L ∧ L ≤ π / 6 + 32 / 27 + 2 / 3 * (5 / 27) := by
  have hπ := Real.pi_pos
  have h := airyMod_limit_bounds (E := fun s => airyPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ))
    (e := fun s => 1 / (π * airyModulus (-s) ^ 2) - s ^ (1 / 2 : ℝ)) (a := 0) (b := 32 / 27)
    (K := 5 / 27)
    (((airyPhase_continuous.comp continuous_neg).sub
      (continuous_const.mul (Real.continuous_rpow_const (by norm_num)))).continuousOn)
    (fun s hs => by
      convert (airyMod_phase_hasDerivAt s).sub
        ((Real.hasDerivAt_rpow_const (p := 3 / 2) (Or.inl hs.ne')).const_mul (2 / 3)) using 1
      norm_num; ring_nf)
    (fun s hs hs1 => by
      obtain ⟨h1, h2⟩ := airyMod_modulus_bounds hs
      obtain ⟨h3, _⟩ := airyMod_modulus_bounds one_pos
      have hm := airyMod_sq_strictMono (show -1 < -s by linarith)
      simp only [Real.one_rpow, mul_one, one_pow, inv_one] at h3
      have hA := airyModulus_pos (-s)
      have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
      have hA2 : 0 < π * airyModulus (-s) ^ 2 := by positivity
      constructor
      · rw [sub_nonneg, le_div_iff₀ hA2]; nlinarith
      · have : 27 / 32 ≤ π * airyModulus (-s) ^ 2 := by nlinarith
        have : 1 / (π * airyModulus (-s) ^ 2) ≤ 32 / 27 := by
          rw [div_le_iff₀ hA2]; linarith
        linarith)
    (fun s hs => by
      have hs0 : 0 < s := by linarith
      obtain ⟨h1, h2⟩ := airyMod_modulus_bounds hs0
      set q := s ^ (1 / 2 : ℝ)
      set w := (s ^ 3)⁻¹
      set y := π * q * airyModulus (-s) ^ 2
      have hq : 0 < q := Real.rpow_pos_of_pos hs0 _
      have hw : 0 < w := by positivity
      have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hs)
      have hy : 27 / 32 ≤ y := by nlinarith
      have he : 1 / (π * airyModulus (-s) ^ 2) = q / y := by
        simp only [y]; field_simp
      have hp : s ^ (-(5 / 2) : ℝ) = q * w := by
        rw [show (-(5 / 2) : ℝ) = 1 / 2 + (-3 : ℝ) by norm_num, Real.rpow_add hs0,
          Real.rpow_neg hs0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [he, hp]
      have hy0 : 0 < y := by linarith
      have hnn : 0 ≤ q / y - q := by
        rw [sub_nonneg, le_div_iff₀ hy0]; nlinarith
      rw [abs_of_nonneg hnn, div_sub' hy0.ne', div_le_iff₀ hy0]
      nlinarith [mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 5 * q * w)])
    hL
  simpa [airyPhase_zero, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)] using h
-- the oscillatory asymptotics fix `L - π/4 ∈ 2πℤ`

/-- The oscillatory asymptotics of `Ai`, `Bi` force `cos (L - π/4) = 1`. -/
private lemma airyMod_phase_limit_cos {L : ℝ}
    (hL : Tendsto (fun s => airyPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    Real.cos (L - π / 4) = 1 := by
  have hπ := Real.pi_pos
  set y : ℝ → ℝ := fun s => π * s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2
  have hy : Tendsto y atTop (𝓝 1) := by
    have hw : Tendsto (fun s : ℝ => 1 - 5 / 32 * (s ^ 3)⁻¹) atTop (𝓝 1) := by
      have := ((tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)).inv_tendsto_atTop).const_mul
        (5 / 32 : ℝ)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hw tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs using (airyMod_modulus_bounds hs).1
    · filter_upwards [eventually_gt_atTop 0] with s hs using (airyMod_modulus_bounds hs).2.le
  have hu : Tendsto (fun s => Real.sqrt (y s)) atTop (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp hy
    rw [Real.sqrt_one] at this
    exact this
  refine airyMod_cos_eq_one_of_limits (u := fun s => Real.sqrt (y s))
    (θ := fun s => airyPhase (-s)) (β := fun s => airyZeta s - π / 4 + π / 2) hu ?_ ?_ ?_
  · refine (airyMod_tendsto_rpow_mul (Real.sqrt π) (a := 1 / 4) (by norm_num)
      airyMod_aiReal_neg_sub).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [y]
    rw [airyMod_sqrt_eq hs (airyModulus_pos _).le, Real.sin_add_pi_div_two,
      airyAiReal_eq_modulus_sin (-s)]
    have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
    have h4 : s ^ (1 / 4 : ℝ) * s ^ (-(1 / 4) : ℝ) = 1 := by
      rw [← Real.rpow_add hs]; norm_num
    field_simp
    norm_num
    linear_combination (-Real.cos ((4 * airyZeta s - π) / 4)) * h4
  · refine (airyMod_tendsto_rpow_mul (Real.sqrt π) (a := 1 / 4) (by norm_num)
      airyMod_biReal_neg_sub).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [y]
    rw [airyMod_sqrt_eq hs (airyModulus_pos _).le, Real.cos_add_pi_div_two,
      airyBiReal_eq_modulus_cos (-s)]
    have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
    have h4 : s ^ (1 / 4 : ℝ) * s ^ (-(1 / 4) : ℝ) = 1 := by
      rw [← Real.rpow_add hs]; norm_num
    field_simp
    norm_num
    linear_combination (Real.sin ((4 * airyZeta s - π) / 4)) * h4
  · refine (hL.sub_const (π / 4)).congr fun s => ?_
    simp only [airyZeta]; ring

/-- The constant in the phase expansion is `π/4`. -/
theorem airyMod_phase_limit {L : ℝ}
    (hL : Tendsto (fun s => airyPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    L = π / 4 := by
  have hπ := Real.pi_pos
  have hb := airyMod_phase_limit_bounds hL
  have := airyMod_eq_zero_of_cos_eq_one (airyMod_phase_limit_cos hL) (by
    rw [abs_lt]; constructor <;> nlinarith [Real.pi_gt_three])
  linarith


/-- The first coefficients of the expansion of `N²`. -/
theorem airyMod_derivCoeff_values : airyDerivModulusCoeff 0 = 1 ∧ airyDerivModulusCoeff 1 = -(7 / 32) ∧
    airyDerivModulusCoeff 2 < 0 := by
  obtain ⟨c0, c1, c2⟩ := airyMod_coeff_values
  refine ⟨by simp [airyDerivModulusCoeff, c0], by rw [airyDerivModulusCoeff, c1]; norm_num, ?_⟩
  rw [airyDerivModulusCoeff]
  push_cast
  have : (1 - 6 * (2 : ℝ)) < 0 := by norm_num
  exact div_neg_of_pos_of_neg (by positivity) this

/-- Two-sided bounds for `π s^{-1/2} N(-s)²`: `1 ≤ π s^{-1/2} N(-s)² ≤ 1 + 7/(32 s³)`. -/
theorem airyMod_derivModulus_bounds {s : ℝ} (hs : 0 < s) :
    1 ≤ π * s ^ (-(1 / 2) : ℝ) * airyDerivModulus (-s) ^ 2 ∧
      π * s ^ (-(1 / 2) : ℝ) * airyDerivModulus (-s) ^ 2 ≤ 1 + 7 / 32 * (s ^ 3)⁻¹ := by
  have hπ := Real.pi_pos
  obtain ⟨c0, c1, c2⟩ := airyMod_derivCoeff_values
  have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hqi : s ^ (-(1 / 2) : ℝ) = (s ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hs.le _
  have hw : 0 < (s ^ 3)⁻¹ := by positivity
  rw [hqi]
  constructor
  · have h := (airyDerivModulus_error (x := -s) (by linarith) (N := 1) le_rfl).2
    rw [neg_neg] at h
    simp only [airyModulusSum, Finset.sum_range_succ, Finset.sum_range_zero, ite_true,
      airyMod_neg_zpow, c0, c1] at h
    have hpos : 0 < s ^ (1 / 2 : ℝ) / π * -(7 / 32) * (-(s ^ 3)⁻¹) ^ 1 := by
      rw [pow_one]; nlinarith [div_pos hq hπ]
    have h' := (mul_nonneg_iff_of_pos_right hpos).mp h
    simp only [pow_zero, mul_one, zero_add] at h'
    have : s ^ (1 / 2 : ℝ) / π ≤ airyDerivModulus (-s) ^ 2 := by linarith
    calc (1 : ℝ) = π * (s ^ (1 / 2 : ℝ))⁻¹ * (s ^ (1 / 2 : ℝ) / π) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  · have h := (airyDerivModulus_error (x := -s) (by linarith) (N := 2) (by norm_num)).2
    rw [neg_neg] at h
    simp only [airyModulusSum, Finset.sum_range_succ, Finset.sum_range_zero, ite_true,
      airyMod_neg_zpow, c0, c1] at h
    have hneg : s ^ (1 / 2 : ℝ) / π * airyDerivModulusCoeff 2 * (-(s ^ 3)⁻¹) ^ 2 < 0 := by
      have : 0 < (-(s ^ 3)⁻¹) ^ 2 := by rw [neg_sq]; positivity
      have h3 : s ^ (1 / 2 : ℝ) / π * airyDerivModulusCoeff 2 < 0 :=
        mul_neg_of_pos_of_neg (div_pos hq hπ) c2
      exact mul_neg_of_neg_of_pos h3 this
    have h' : airyDerivModulus (-s) ^ 2 - s ^ (1 / 2 : ℝ) / π *
        (0 + 1 * (-(s ^ 3)⁻¹) ^ 0 + -(7 / 32) * (-(s ^ 3)⁻¹) ^ 1) ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith
    simp only [pow_zero, pow_one, mul_one, zero_add] at h'
    have : airyDerivModulus (-s) ^ 2 ≤ s ^ (1 / 2 : ℝ) / π * (1 + 7 / 32 * (s ^ 3)⁻¹) := by
      linarith
    calc π * (s ^ (1 / 2 : ℝ))⁻¹ * airyDerivModulus (-s) ^ 2
        ≤ π * (s ^ (1 / 2 : ℝ))⁻¹ * (s ^ (1 / 2 : ℝ) / π * (1 + 7 / 32 * (s ^ 3)⁻¹)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp

/-- `Ai'(-s) = π^{-1/2} s^{1/4} sin(ζ - π/4) + O(s^{-5/4})`, real form. -/
theorem airyMod_aiDerivReal_neg_sub :
    (fun s : ℝ => airyAiDerivReal (-s) - s ^ (1 / 4 : ℝ) / Real.sqrt π * Real.sin (airyZeta s - π / 4))
      =O[atTop] (fun s : ℝ => s ^ (-(5 / 4) : ℝ)) := by
  refine (airyInt_aiDeriv_neg_sub.norm_left.congr_left fun s => ?_).of_norm_left
  rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring, airyAiDeriv_ofReal_eq, ← ofReal_sub,
    norm_real]

/-- `Bi'(-s) = π^{-1/2} s^{1/4} cos(ζ - π/4) + O(s^{-5/4})`, real form. -/
theorem airyMod_biDerivReal_neg_sub :
    (fun s : ℝ => airyBiDerivReal (-s) - s ^ (1 / 4 : ℝ) / Real.sqrt π * Real.cos (airyZeta s - π / 4))
      =O[atTop] (fun s : ℝ => s ^ (-(5 / 4) : ℝ)) := by
  refine (airyInt_biDeriv_neg_sub.norm_left.congr_left fun s => ?_).of_norm_left
  rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring, airyBiDeriv_ofReal_eq, ← ofReal_sub,
    norm_real]

/-- The derivative phase `φ(-s)` has derivative `s/(π N(-s)²)`. -/
theorem airyMod_derivPhase_hasDerivAt (s : ℝ) :
    HasDerivAt (fun s => airyDerivPhase (-s)) (s / (π * airyDerivModulus (-s) ^ 2)) s := by
  convert (hasDerivAt_airyDerivPhase (-s)).comp s (hasDerivAt_neg s) using 1 <;>
    first | rfl | ring

/-- Reciprocal expansion of `s/(π N(-s)²)` as `s → ∞`. -/
theorem airyMod_derivPhase_integrand (N : ℕ) :
    (fun s => s / (π * airyDerivModulus (-s) ^ 2) - ∑ k ∈ Finset.range N,
      s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * airyReciprocalCoeff airyDerivModulusCoeff k)
      =O[atTop] (fun s => s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  refine airyMod_integrand_expansion (F := fun x => airyDerivModulus x ^ 2)
    (p := fun x => (-x) ^ (1 / 2 : ℝ) / π) airyDerivModulus_asymptotic
    (fun x hx => div_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne' Real.pi_ne_zero)
    airyMod_derivCoeff_values.1 (fun s hs => ?_) N
  have hM := (airyDerivModulus_pos (-s)).ne'
  have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hsq : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by
    rw [← Real.rpow_add hs]; norm_num
  simp only [neg_neg]
  have e : s ^ (1 / 2 : ℝ) * (airyDerivModulus (-s) ^ 2 / (s ^ (1 / 2 : ℝ) / π))⁻¹ =
      (s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ)) / (π * airyDerivModulus (-s) ^ 2) := by
    rw [inv_div]; field_simp
  rw [e, hsq]

/-- The derivative-phase expansion at `+∞` in `s = -x`, with an undetermined constant. -/
theorem airyMod_derivPhase_expansion_s : ∃ L, Tendsto (fun s => airyDerivPhase (-s) -
      2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L) ∧
    ∀ N : ℕ, (fun s => airyDerivPhase (-s) - L - ∑ k ∈ Finset.range N,
      2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * airyDerivPhaseCoeff k) =O[atTop]
      (fun s => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  obtain ⟨L, hL, hN⟩ := airyMod_expansion_of_deriv (fun s _ => airyMod_derivPhase_hasDerivAt s)
    airyMod_derivPhase_integrand
  refine ⟨L, by simpa [airyReciprocalCoeff] using hL, fun N => ?_⟩
  simpa [airyDerivPhaseCoeff] using hN N

/-- Explicit bounds on the constant `L` of the derivative-phase expansion. -/
private lemma airyMod_derivPhase_limit_bounds {L : ℝ}
    (hL : Tendsto (fun s => airyDerivPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    -π / 6 + -1 - 2 / 3 * (7 / 32) ≤ L ∧ L ≤ -π / 6 + 0 + 2 / 3 * (7 / 32) := by
  have hπ := Real.pi_pos
  have h := airyMod_limit_bounds (E := fun s => airyDerivPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ))
    (e := fun s => s / (π * airyDerivModulus (-s) ^ 2) - s ^ (1 / 2 : ℝ)) (a := -1) (b := 0)
    (K := 7 / 32)
    (((airyDerivPhase_continuous.comp continuous_neg).sub
      (continuous_const.mul (Real.continuous_rpow_const (by norm_num)))).continuousOn)
    (fun s hs => by
      convert (airyMod_derivPhase_hasDerivAt s).sub
        ((Real.hasDerivAt_rpow_const (p := 3 / 2) (Or.inl hs.ne')).const_mul (2 / 3)) using 1
      norm_num; ring_nf)
    (fun s hs hs1 => by
      obtain ⟨h1, h2⟩ := airyMod_derivModulus_bounds hs
      have hA := airyDerivModulus_pos (-s)
      have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
      have hq1 : s ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hs.le hs1.le (by norm_num)
      have hsq : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by
        rw [← Real.rpow_add hs]; norm_num
      have hqi : s ^ (-(1 / 2) : ℝ) = (s ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hs.le _
      rw [hqi] at h1
      have hA2 : 0 < π * airyDerivModulus (-s) ^ 2 := by positivity
      have hkey : s ^ (1 / 2 : ℝ) ≤ π * airyDerivModulus (-s) ^ 2 := by
        have := mul_le_mul_of_nonneg_left h1 hq.le
        rw [show s ^ (1 / 2 : ℝ) * (π * (s ^ (1 / 2 : ℝ))⁻¹ * airyDerivModulus (-s) ^ 2) =
          π * airyDerivModulus (-s) ^ 2 by field_simp] at this
        linarith
      have hnn : 0 ≤ s / (π * airyDerivModulus (-s) ^ 2) := by positivity
      constructor
      · linarith
      · rw [sub_nonpos, div_le_iff₀ hA2]
        calc s = s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) := hsq.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hkey hq.le)
    (fun s hs => by
      have hs0 : 0 < s := by linarith
      obtain ⟨h1, h2⟩ := airyMod_derivModulus_bounds hs0
      set q := s ^ (1 / 2 : ℝ)
      set w := (s ^ 3)⁻¹
      have hq : 0 < q := Real.rpow_pos_of_pos hs0 _
      have hw : 0 < w := by positivity
      have hqi : s ^ (-(1 / 2) : ℝ) = q⁻¹ := Real.rpow_neg hs0.le _
      rw [hqi] at h1 h2
      set z := π * q⁻¹ * airyDerivModulus (-s) ^ 2
      have hsq : q * q = s := by
        simp only [q]; rw [← Real.rpow_add hs0]; norm_num
      have he : s / (π * airyDerivModulus (-s) ^ 2) = q / z := by
        simp only [z]; rw [← hsq]; field_simp
      have hp : s ^ (-(5 / 2) : ℝ) = q * w := by
        rw [show (-(5 / 2) : ℝ) = 1 / 2 + (-3 : ℝ) by norm_num, Real.rpow_add hs0,
          Real.rpow_neg hs0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [he, hp]
      have hz0 : 0 < z := by linarith
      have hnp : q / z - q ≤ 0 := by
        rw [sub_nonpos, div_le_iff₀ hz0]; nlinarith
      rw [abs_of_nonpos hnp, neg_sub, sub_div' hz0.ne', div_le_iff₀ hz0]
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 7 / 32 * q * w)])
    hL
  simpa [airyDerivPhase_zero, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)] using h

/-- The oscillatory asymptotics of `Ai'`, `Bi'` force `cos (L + π/4) = 1`. -/
private lemma airyMod_derivPhase_limit_cos {L : ℝ}
    (hL : Tendsto (fun s => airyDerivPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    Real.cos (L + π / 4) = 1 := by
  have hπ := Real.pi_pos
  set y : ℝ → ℝ := fun s => π * s ^ (-(1 / 2) : ℝ) * airyDerivModulus (-s) ^ 2
  have hy : Tendsto y atTop (𝓝 1) := by
    have hw : Tendsto (fun s : ℝ => 1 + 7 / 32 * (s ^ 3)⁻¹) atTop (𝓝 1) := by
      have := ((tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)).inv_tendsto_atTop).const_mul
        (7 / 32 : ℝ)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hw ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs using (airyMod_derivModulus_bounds hs).1
    · filter_upwards [eventually_gt_atTop 0] with s hs using (airyMod_derivModulus_bounds hs).2
  have hu : Tendsto (fun s => Real.sqrt (y s)) atTop (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp hy
    rw [Real.sqrt_one] at this
    exact this
  refine airyMod_cos_eq_one_of_limits (u := fun s => Real.sqrt (y s))
    (θ := fun s => airyDerivPhase (-s)) (β := fun s => airyZeta s - π / 4) hu ?_ ?_ ?_
  · refine (airyMod_tendsto_rpow_mul (Real.sqrt π) (a := -(1 / 4)) (by norm_num)
      airyMod_aiDerivReal_neg_sub).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [y]
    rw [airyMod_sqrt_eq hs (airyDerivModulus_pos _).le, airyAiDerivReal_eq_modulus_sin (-s)]
    have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
    have h4 : s ^ (-(1 / 4) : ℝ) * s ^ (1 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hs]; norm_num
    generalize airyZeta s - π / 4 = α
    norm_num
    field_simp
    linear_combination (-Real.sin α) * h4
  · refine (airyMod_tendsto_rpow_mul (Real.sqrt π) (a := -(1 / 4)) (by norm_num)
      airyMod_biDerivReal_neg_sub).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [y]
    rw [airyMod_sqrt_eq hs (airyDerivModulus_pos _).le, airyBiDerivReal_eq_modulus_cos (-s)]
    have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
    have h4 : s ^ (-(1 / 4) : ℝ) * s ^ (1 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hs]; norm_num
    generalize airyZeta s - π / 4 = α
    norm_num
    field_simp
    linear_combination (-Real.cos α) * h4
  · refine (hL.add_const (π / 4)).congr fun s => ?_
    simp only [airyZeta]; ring

/-- The constant in the derivative-phase expansion is `-π/4`. -/
theorem airyMod_derivPhase_limit {L : ℝ}
    (hL : Tendsto (fun s => airyDerivPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    L = -π / 4 := by
  have hπ := Real.pi_pos
  have hb := airyMod_derivPhase_limit_bounds hL
  have := airyMod_eq_zero_of_cos_eq_one (airyMod_derivPhase_limit_cos hL) (by
    rw [abs_lt]; constructor <;> nlinarith [Real.pi_gt_three])
  linarith

/-- As `x → -∞`, `θ(x) - π/4 ∼ (2/3)(-x)^{3/2} ∑ₖ cₖ x^{-3k}` with the coefficients
`airyPhaseCoeff` (DLMF 9.8.22). -/
@[dlmf 9.8.E22]
theorem airyPhase_asymptotic :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => 2 / 3 * (-x) ^ (3 / 2 : ℝ) * x ^ (-(3 * k : ℤ)))
      airyPhaseCoeff (fun x => airyPhase x - (π / 4)) := by
  obtain ⟨L, hL, hN⟩ := airyMod_phase_expansion_s
  have hL4 := airyMod_phase_limit hL
  subst hL4
  intro N
  refine ((hN N).comp_tendsto tendsto_neg_atBot_atTop).congr' ?_ ?_
  · exact Eventually.of_forall fun x => by simp only [Function.comp_apply, neg_neg, smul_eq_mul]
  · exact Eventually.of_forall fun x => by simp only [Function.comp_apply, neg_neg]


/-- As `x → -∞`, `φ(x) + π/4 ∼ (2/3)(-x)^{3/2} ∑ₖ dₖ x^{-3k}` with the coefficients
`airyDerivPhaseCoeff` (DLMF 9.8.23). -/
@[dlmf 9.8.E23]
theorem airyDerivPhase_asymptotic :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => 2 / 3 * (-x) ^ (3 / 2 : ℝ) * x ^ (-(3 * k : ℤ)))
      airyDerivPhaseCoeff (fun x => airyDerivPhase x - (-π / 4)) := by
  obtain ⟨L, hL, hN⟩ := airyMod_derivPhase_expansion_s
  have hL4 := airyMod_derivPhase_limit hL
  subst hL4
  intro N
  refine ((hN N).comp_tendsto tendsto_neg_atBot_atTop).congr' ?_ ?_
  · exact Eventually.of_forall fun x => by simp only [Function.comp_apply, neg_neg, smul_eq_mul]
  · exact Eventually.of_forall fun x => by simp only [Function.comp_apply, neg_neg]

/-- Every printed coefficient in the phase expansions 9.8.22 and 9.8.23. -/
@[dlmf 9.8.E22, dlmf 9.8.E23]
theorem airy_phase_printed_coefficients :
    (∀ n < 5, airyPhaseCoeff n = ([1, 5/32, 1105/6144, 82825/65536, 1282031525/58720256] : List ℝ)[n]!) ∧
    (∀ n < 5, airyDerivPhaseCoeff n = ([1, -7/32, -1463/6144, -495271/327680, -206530429/8388608] : List ℝ)[n]!) := by
  constructor <;> intro n hn <;> interval_cases n <;>
    norm_num [airyPhaseCoeff, airyDerivPhaseCoeff, airyReciprocalCoeff,
      airyModulusCoeff, airyDerivModulusCoeff, Finset.sum_range_succ, Finset.prod_range_succ]

end DLMF.Airy
