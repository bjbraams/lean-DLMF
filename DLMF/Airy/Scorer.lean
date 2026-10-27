/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Equation
public import DLMF.Airy.Zeros
public import DLMFMathlib.Analysis.ODE.SturmCount

/-!
# Scorer functions, DLMF §9.12

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology Nat
namespace DLMF.Airy

/-- Maclaurin coefficient of Hi, DLMF 9.12.17. -/
def scorerHiCoeff (k : ℕ) : ℂ :=
  (3 : ℂ) ^ (((k : ℂ) - 2) / 3) * Gamma (((k : ℂ) + 1) / 3) / (π * k.factorial)
/-- The entire Scorer function Hi, specified by its Maclaurin series. -/
@[dlmf 9.12.E17]
def scorerHi (z : ℂ) : ℂ := ∑' k : ℕ, scorerHiCoeff k * z ^ k
/-- The complementary Scorer function Gi, with Gi+Hi=Bi. -/
def scorerGi (z : ℂ) : ℂ := airyBi z - scorerHi z
/-- The derivative of Hi. -/
def scorerHiDeriv : ℂ → ℂ := deriv scorerHi
/-- The derivative of Gi. -/
def scorerGiDeriv : ℂ → ℂ := deriv scorerGi
/-- The inhomogeneous Airy equation with forcing 1/π. -/
def IsScorerSol (w w' : ℂ → ℂ) : Prop :=
  ∀ z, HasDerivAt w (w' z) z ∧ HasDerivAt w' (z * w z + 1 / π) z
/-- The determinant of the value/first-derivative/second-derivative matrix. -/
def airyWronskian3 (f g h : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * (deriv g z * deriv (deriv h) z - deriv h z * deriv (deriv g) z) -
    g z * (deriv f z * deriv (deriv h) z - deriv h z * deriv (deriv f) z) +
    h z * (deriv f z * deriv (deriv g) z - deriv g z * deriv (deriv f) z)
/-- Uniform numerical separation of a third-order fundamental system. -/
def IsWellConditionedTripleOn (f g h : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z ∈ s,
    ‖f z‖ * (‖deriv g z‖ * ‖deriv (deriv h) z‖ + ‖deriv h z‖ * ‖deriv (deriv g) z‖) +
      ‖g z‖ * (‖deriv f z‖ * ‖deriv (deriv h) z‖ + ‖deriv h z‖ * ‖deriv (deriv f) z‖) +
      ‖h z‖ * (‖deriv f z‖ * ‖deriv (deriv g) z‖ + ‖deriv g z‖ * ‖deriv (deriv f) z‖) ≤
        C * ‖airyWronskian3 f g h z‖

section HiSeries
open FormalMultilinearSeries
open scoped NNReal ENNReal

/-- The three-step recurrence `c_{k+3}(k+3)(k+2) = c_k` of the Hi coefficients. -/
theorem scorerHiCoeff_rec (k : ℕ) :
    scorerHiCoeff (k + 3) * (((k : ℂ) + 3) * ((k : ℂ) + 2)) = scorerHiCoeff k := by
  simp only [scorerHiCoeff]
  push_cast
  rw [show ((k : ℂ) + 3 - 2) / 3 = ((k : ℂ) - 2) / 3 + 1 by ring,
    Complex.cpow_add _ _ (by norm_num), Complex.cpow_one,
    show ((k : ℂ) + 3 + 1) / 3 = ((k : ℂ) + 1) / 3 + 1 by ring,
    Complex.Gamma_add_one _ (by
      intro h; have := congrArg Complex.re h; simp at this; linarith),
    show k + 3 = (k + 2) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  generalize (3 : ℂ) ^ (((k : ℂ) - 2) / 3) = a
  generalize Gamma (((k : ℂ) + 1) / 3) = G
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have h2 : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 1))
  have h3 : (k : ℂ) + 3 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 2))
  have h2' : (k : ℂ) + 1 + 1 ≠ 0 := by rw [add_assoc]; norm_num; exact h2
  have h3' : (k : ℂ) + 2 + 1 ≠ 0 := by rw [add_assoc]; norm_num; exact h3
  field_simp
  ring

/-- A three-step recurrence `c_{k+3}(k+3)(k+2) = c_k` forces an infinite radius. -/
theorem radius_ofScalars_eq_top_of_rec3 {c : ℕ → ℂ}
    (h : ∀ k : ℕ, c (k + 3) * (((k : ℂ) + 3) * ((k : ℂ) + 2)) = c k) :
    (ofScalars ℂ c).radius = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  set u : ℕ → ℝ := fun k => ‖c k‖ * (r : ℝ) ^ k with hu
  obtain ⟨K, hK⟩ := exists_nat_ge ((r : ℝ) ^ 3)
  have hstep : ∀ k, K ≤ k → u (k + 3) ≤ u k := by
    intro k hk
    have hc : ‖c (k + 3)‖ * (((k : ℝ) + 3) * ((k : ℝ) + 2)) = ‖c k‖ := by
      rw [← h k, norm_mul]; congr 1
      rw [show ((k : ℂ) + 3) * ((k : ℂ) + 2) = (((k + 3) * (k + 2) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hk' : (r : ℝ) ^ 3 ≤ ((k : ℝ) + 3) * ((k : ℝ) + 2) := by
      have : (K : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    simp only [hu, pow_add]
    rw [← hc]
    have := norm_nonneg (c (k + 3))
    have : 0 ≤ (r : ℝ) ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hk' (mul_nonneg (norm_nonneg (c (k + 3))) this)]
  set B := ∑ j ∈ Finset.range (K + 3), u j
  have hB : ∀ k, u k ≤ B := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < K + 3
      · exact Finset.single_le_sum (f := u) (fun j _ => by positivity) (Finset.mem_range.mpr hk)
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
        exact (hstep m (by omega)).trans (ih m (by omega))
  refine (ofScalars ℂ c).le_radius_of_bound B fun n => ?_
  refine le_trans ?_ (hB n)
  simp only [hu]
  gcongr
  rw [ofScalars_norm]

/-- The Maclaurin series of Hi has infinite radius. -/
theorem radius_scorerHi : (ofScalars ℂ scorerHiCoeff).radius = ⊤ :=
  radius_ofScalars_eq_top_of_rec3 scorerHiCoeff_rec

/-- Hi is the sum of its Maclaurin series on all of `ℂ`. -/
theorem hasFPowerSeriesOnBall_scorerHi :
    HasFPowerSeriesOnBall scorerHi (ofScalars ℂ scorerHiCoeff) 0 ⊤ := by
  have h := (ofScalars ℂ scorerHiCoeff).hasFPowerSeriesOnBall (by rw [radius_scorerHi]; simp)
  rw [radius_scorerHi] at h
  have he : (ofScalars ℂ scorerHiCoeff).sum = scorerHi := by
    funext z
    simp only [scorerHi, FormalMultilinearSeries.sum, ofScalars_apply_eq, smul_eq_mul]
  rwa [he] at h

theorem mem_eball_top (z : ℂ) : z ∈ Metric.eball (0 : ℂ) ⊤ := by simp
/-- Hi is entire. -/
theorem differentiable_scorerHi : Differentiable ℂ scorerHi := fun z =>
  (hasFPowerSeriesOnBall_scorerHi.analyticAt_of_mem (mem_eball_top z)).differentiableAt

theorem scorerHiCoeff_two : scorerHiCoeff 2 = 1 / (2 * π) := by
  simp only [scorerHiCoeff]
  norm_num
  ring

/-- `Hi'' = z Hi + 1/π`. -/
theorem hasDerivAt_scorerHiDeriv (z : ℂ) :
    HasDerivAt scorerHiDeriv (z * scorerHi z + 1 / π) z := by
  have h1 := hasFPowerSeriesOnBall_scorerHi.deriv_ofScalars
  have h2 := h1.deriv_ofScalars
  have hdiff : DifferentiableAt ℂ scorerHiDeriv z :=
    (h1.analyticAt_of_mem (mem_eball_top z)).differentiableAt
  have hs := h2.hasSum_mul_pow (mem_eball_top z)
  have hH := (hasFPowerSeriesOnBall_scorerHi.hasSum_mul_pow (mem_eball_top z)).mul_left z
  have hs' : HasSum (fun n : ℕ => ((n : ℂ) + 1) * (((n + 1 : ℕ) : ℂ) + 1) *
      scorerHiCoeff (n + 2) * z ^ n) (z * scorerHi z + 1 / π) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_zero, mul_one, scorerHiCoeff_two]
    convert hH using 1
    · funext n
      have := scorerHiCoeff_rec n
      rw [show n + 1 + 2 = n + 3 by ring, pow_succ]
      push_cast
      linear_combination (z * z ^ n) * this
    · push_cast; ring
  have he : deriv scorerHiDeriv z = z * scorerHi z + 1 / π :=
    hs.unique (by simpa only [mul_assoc] using hs')
  have := hdiff.hasDerivAt
  rwa [he] at this

/-- `Hi' ` as a derivative. -/
theorem hasDerivAt_scorerHi (z : ℂ) : HasDerivAt scorerHi (scorerHiDeriv z) z :=
  (differentiable_scorerHi z).hasDerivAt

/-- `Gi' = Bi' - Hi'`. -/
theorem scorerGiDeriv_eq (z : ℂ) : scorerGiDeriv z = airyBiDeriv z - scorerHiDeriv z :=
  ((hasDerivAt_airyBi z).sub (hasDerivAt_scorerHi z)).deriv
/-- `exp(-ε·2πi/3)` is a cube root of unity for `ε = ±1`. -/
theorem exp_neg_eps_cube {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : exp (-ε * (2 * π * I / 3)) ^ 3 = 1 := by
  rcases hε with rfl | rfl
  · simpa using omega_recip_cube
  · simpa using omega_cube

end HiSeries

/-- Hi is entire, DLMF §9.12(i). -/
theorem scorerHi_entire  :
    Differentiable ℂ scorerHi := by
  exact differentiable_scorerHi

/-- Gi is entire, DLMF §9.12(i). -/
theorem scorerGi_entire  :
    Differentiable ℂ scorerGi := by
  exact differentiable_airyBi.sub differentiable_scorerHi

/-- scorerHi ode (DLMF 9.12.1). -/
@[dlmf 9.12.E1]
theorem scorerHi_ode  :
    IsScorerSol scorerHi scorerHiDeriv := by
  exact fun z =>
    ⟨hasDerivAt_scorerHi z, hasDerivAt_scorerHiDeriv z⟩

/-- scorerGi ode (DLMF 9.12.3). -/
@[dlmf 9.12.E3]
theorem scorerGi_ode  :
    IsScorerSol (fun z => -scorerGi z) (fun z => -scorerGiDeriv z) := by
  intro z
  have hG : scorerGiDeriv = fun z => airyBiDeriv z - scorerHiDeriv z := funext scorerGiDeriv_eq
  refine ⟨((hasDerivAt_airyBi z).sub (hasDerivAt_scorerHi z)).neg.congr_deriv
    (by simp [scorerGiDeriv_eq]), ?_⟩
  rw [hG]
  exact ((hasDerivAt_airyBiDeriv z).sub (hasDerivAt_scorerHiDeriv z)).neg.congr_deriv
    (by simp only [scorerGi]; ring)

/-- scorerHi rotated ode (DLMF 9.12.3). -/
@[dlmf 9.12.E3]
theorem scorerHi_rotated_ode {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    IsScorerSol (fun z => exp (-ε * (2 * π * I / 3)) * scorerHi (z * exp (-ε * (2 * π * I / 3))))
      (fun z => exp (-ε * (4 * π * I / 3)) * scorerHiDeriv (z * exp (-ε * (2 * π * I / 3)))) := by
  set ω := exp (-ε * (2 * π * I / 3)) with hω
  have h3 : ω ^ 3 = 1 := exp_neg_eps_cube hε
  have h2 : exp (-ε * (4 * π * I / 3)) = ω ^ 2 := by
    rw [hω, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2]
  intro z
  have hl : HasDerivAt (fun z : ℂ => z * ω) ω z := (hasDerivAt_id z).mul_const ω |>.congr_deriv
    (by simp)
  have e1 := ((hasDerivAt_scorerHi (z * ω)).comp z hl).const_mul ω
  have e2 := ((hasDerivAt_scorerHiDeriv (z * ω)).comp z hl).const_mul (ω ^ 2)
  change HasDerivAt (fun z => ω * scorerHi (z * ω)) _ z at e1
  change HasDerivAt (fun z => ω ^ 2 * scorerHiDeriv (z * ω)) _ z at e2
  refine ⟨e1.congr_deriv (by ring), e2.congr_deriv ?_⟩
  linear_combination (z * ω * scorerHi (z * ω) + 1 / π) * h3

/-- scorer general solution (DLMF 9.12.2). -/
@[dlmf 9.12.E2]
theorem scorer_general_solution {w w' p p' f f' g g' : ℂ → ℂ} (hw : IsScorerSol w w') (hp : IsScorerSol p p')
    (hf : IsAirySol f f') (hg : IsAirySol g g') (hind : f 0 * g' 0 - f' 0 * g 0 ≠ 0) :
    ∃ a b : ℂ, ∀ z, w z = a * f z + b * g z + p z := by
  set D := f 0 * g' 0 - f' 0 * g 0
  set u0 := w 0 - p 0
  set u1 := w' 0 - p' 0
  refine ⟨(u0 * g' 0 - u1 * g 0) / D, (f 0 * u1 - f' 0 * u0) / D, fun z => ?_⟩
  have hu : IsAirySol (fun z => w z - p z) (fun z => w' z - p' z) := fun z =>
    ⟨(hw z).1.sub (hp z).1, ((hw z).2.sub (hp z).2).congr_deriv (by ring)⟩
  have hs : IsAirySol (fun z => (u0 * g' 0 - u1 * g 0) / D * f z + (f 0 * u1 - f' 0 * u0) / D * g z)
      (fun z => (u0 * g' 0 - u1 * g 0) / D * f' z + (f 0 * u1 - f' 0 * u0) / D * g' z) :=
    fun z => ⟨((hf z).1.const_mul _).add ((hg z).1.const_mul _),
      (((hf z).2.const_mul _).add ((hg z).2.const_mul _)).congr_deriv (by ring)⟩
  have h := hu.eq_of_initial hs (by field_simp; simp only [u0, u1, D]; ring)
    (by field_simp; simp only [u0, u1, D]; ring) z
  linear_combination h

/-- scorer zero (DLMF 9.12.6). -/
@[dlmf 9.12.E6]
theorem scorer_zero  :
    scorerGi 0 = scorerHi 0 / 2 ∧ scorerGi 0 = airyBi 0 / 3 ∧
      scorerGi 0 = 1 / ((3 : ℂ) ^ (7 / 6 : ℂ) * Gamma (2 / 3)) := by
  have hHi : scorerHi 0 = (((3 : ℝ) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) * Gamma (1 / 3) / π := by
    rw [scorerHi, tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
    simp only [scorerHiCoeff, pow_zero, mul_one, Nat.cast_zero, Nat.factorial_zero,
      Nat.cast_one, zero_add, zero_sub]
    rw [show (-2 / 3 : ℂ) = ((-(2 / 3) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3)]
    push_cast; ring
  have hG := Gamma_one_third_mul_Gamma_two_thirds
  have hG2 : Gamma (2 / 3) ≠ 0 := by
    intro h; rw [h, mul_zero] at hG
    have : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    exact (div_ne_zero (mul_ne_zero two_ne_zero hp) this) hG.symm
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h76 : (3 : ℂ) ^ (7 / 6 : ℂ) = (((3 : ℝ) ^ (7 / 6 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num)]; push_cast; ring_nf
  have r1 : (3 : ℝ) ^ (7 / 6 : ℝ) = 3 * (3 : ℝ) ^ (1 / 6 : ℝ) := by
    rw [show (7 / 6 : ℝ) = 1 + 1 / 6 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
  have r2 : (3 : ℝ) ^ (-(2 / 3) : ℝ) * (3 * (3 : ℝ) ^ (1 / 6 : ℝ)) = Real.sqrt 3 := by
    rw [Real.sqrt_eq_rpow, ← r1, ← Real.rpow_add (by norm_num)]
    norm_num
  have r2' : (((3 : ℝ) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) * (3 * (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ)) =
      ((Real.sqrt 3 : ℝ) : ℂ) := by exact_mod_cast r2
  have hBi := airyBi_zero
  have hGi : scorerGi 0 = airyBi 0 - scorerHi 0 := rfl
  have h6 : (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).ne'
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hGam : Gamma (1 / 3) = 2 * π / (Real.sqrt 3 * Gamma (2 / 3)) := by
    rw [eq_div_iff (mul_ne_zero h3 hG2), show Gamma (1 / 3) * ((Real.sqrt 3 : ℂ) * Gamma (2 / 3)) =
      (Real.sqrt 3 : ℂ) * (Gamma (1 / 3) * Gamma (2 / 3)) by ring, hG]
    field_simp
  have hHi' : scorerHi 0 = 2 * (2 / 3) * airyBi 0 / 2 := by
    rw [hHi, hBi, hGam, ← r2']
    field_simp
  rw [h76, r1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hGi, hHi']; ring
  · rw [hGi, hHi']; ring
  · rw [hGi, hHi', hBi]; push_cast; field_simp; norm_num

/-- `Hi'(0) = 3^{-1/3} Γ(2/3)/π`. -/
theorem scorerHiDeriv_zero : scorerHiDeriv 0 = scorerHiCoeff 1 := by
  have h := hasFPowerSeriesOnBall_scorerHi.deriv_ofScalars.hasSum_mul_pow (mem_eball_top 0)
  have h' : HasSum (fun n : ℕ => ((n : ℂ) + 1) * scorerHiCoeff (n + 1) * (0 : ℂ) ^ n)
      ((((0 : ℕ) : ℂ) + 1) * scorerHiCoeff (0 + 1) * (0 : ℂ) ^ 0) :=
    hasSum_single 0 (fun n hn => by simp [zero_pow hn])
  simp only [Nat.cast_zero, zero_add, one_mul, pow_zero, mul_one] at h'
  exact h.unique h'

/-- scorerDeriv zero (DLMF 9.12.7). -/
@[dlmf 9.12.E7]
theorem scorerDeriv_zero  :
    scorerGiDeriv 0 = scorerHiDeriv 0 / 2 ∧ scorerGiDeriv 0 = airyBiDeriv 0 / 3 ∧
      scorerGiDeriv 0 = 1 / ((3 : ℂ) ^ (5 / 6 : ℂ) * Gamma (1 / 3)) := by
  have hH : scorerHiDeriv 0 = (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ)⁻¹ ^ 2 * Gamma (2 / 3) / π := by
    rw [scorerHiDeriv_zero, scorerHiCoeff]
    simp only [Nat.cast_one, Nat.factorial_one, mul_one]
    rw [show (3 : ℂ) ^ (((1 : ℂ) - 2) / 3) = (((3 : ℝ) ^ (-(1 / 3) : ℝ) : ℝ) : ℂ) by
        rw [Complex.ofReal_cpow (by norm_num)]; norm_num,
      show ((1 : ℂ) + 1) / 3 = 2 / 3 by norm_num]
    have : (3 : ℝ) ^ (-(1 / 3) : ℝ) = ((3 : ℝ) ^ (1 / 6 : ℝ))⁻¹ ^ 2 := by
      rw [← Real.rpow_natCast, Real.inv_rpow (by positivity), ← Real.rpow_mul (by norm_num),
        Real.rpow_neg (by norm_num)]
      norm_num
    rw [this]; push_cast; ring
  have hG := Gamma_one_third_mul_Gamma_two_thirds
  set A : ℂ := (((3 : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) with hA
  have hA0 : A ≠ 0 := by
    rw [hA]; exact_mod_cast (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).ne'
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) = A ^ 3 := by
    rw [hA, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      Real.sqrt_eq_rpow]; norm_num
  have h56 : (3 : ℂ) ^ (5 / 6 : ℂ) = A ^ 5 := by
    rw [hA, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show (3 : ℂ) ^ (5 / 6 : ℂ) = (((3 : ℝ) ^ (5 / 6 : ℝ) : ℝ) : ℂ) by
        rw [Complex.ofReal_cpow (by norm_num)]; norm_num]; norm_num
  have hA6 : A ^ 6 = 3 := by
    rw [hA, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hB : airyBiDeriv 0 = A / Gamma (1 / 3) := airyBiDeriv_zero
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hs3] at hG
  rw [eq_div_iff (pow_ne_zero 3 hA0)] at hG
  have hG1 : Gamma (1 / 3) ≠ 0 := by
    intro h; rw [h, zero_mul, zero_mul] at hG
    exact (mul_ne_zero two_ne_zero hp) hG.symm
  have hG2 : Gamma (2 / 3) = 2 * π / (A ^ 3 * Gamma (1 / 3)) := by
    rw [eq_div_iff (mul_ne_zero (pow_ne_zero 3 hA0) hG1)]; linear_combination hG
  have hH' : scorerHiDeriv 0 = 2 / (A ^ 5 * Gamma (1 / 3)) := by
    rw [hH, hG2, inv_pow]; field_simp
  have hB' : airyBiDeriv 0 = 3 / (A ^ 5 * Gamma (1 / 3)) := by
    rw [hB]; field_simp; linear_combination hA6
  rw [scorerGiDeriv_eq, h56, hH', hB']
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- Solutions of the inhomogeneous Airy equation `w'' = z w + c`. -/
def IsAiryInhomSol (c : ℂ) (w w' : ℂ → ℂ) : Prop :=
  ∀ z, HasDerivAt w (w' z) z ∧ HasDerivAt w' (z * w z + c) z

theorem IsAiryInhomSol.of_airy {w w' : ℂ → ℂ} (h : IsAirySol w w') : IsAiryInhomSol 0 w w' :=
  fun z => ⟨(h z).1, (h z).2.congr_deriv (by ring)⟩

theorem IsAiryInhomSol.add {c d : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsAiryInhomSol c f f')
    (hg : IsAiryInhomSol d g g') :
    IsAiryInhomSol (c + d) (fun z => f z + g z) (fun z => f' z + g' z) := fun z =>
  ⟨(hf z).1.add (hg z).1, ((hf z).2.add (hg z).2).congr_deriv (by ring)⟩

theorem IsAiryInhomSol.const_mul {c : ℂ} (a : ℂ) {f f' : ℂ → ℂ} (hf : IsAiryInhomSol c f f') :
    IsAiryInhomSol (a * c) (fun z => a * f z) (fun z => a * f' z) := fun z =>
  ⟨(hf z).1.const_mul a, ((hf z).2.const_mul a).congr_deriv (by ring)⟩

theorem IsAiryInhomSol.congr_const {c d : ℂ} {f f' : ℂ → ℂ} (hf : IsAiryInhomSol c f f')
    (h : c = d) : IsAiryInhomSol d f f' := h ▸ hf

/-- Inhomogeneous Airy solutions with the same forcing are determined by their initial data. -/
theorem IsAiryInhomSol.eq_of_initial {c : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsAiryInhomSol c f f')
    (hg : IsAiryInhomSol c g g') (h0 : f 0 = g 0) (h1 : f' 0 = g' 0) (z : ℂ) : f z = g z := by
  have hd : IsAirySol (fun w => f w - g w) (fun w => f' w - g' w) := fun w =>
    ⟨(hf w).1.sub (hg w).1, ((hf w).2.sub (hg w).2).congr_deriv (by ring)⟩
  exact sub_eq_zero.mp (hd.eq_zero (by simp [h0]) (by simp [h1]) z)

/-- `Hi` solves `w'' = z w + 1/π`. -/
theorem isAiryInhomSol_scorerHi : IsAiryInhomSol (1 / π) scorerHi scorerHiDeriv := fun z =>
  ⟨hasDerivAt_scorerHi z, hasDerivAt_scorerHiDeriv z⟩

/-- `Gi` solves `w'' = z w - 1/π`. -/
theorem isAiryInhomSol_scorerGi : IsAiryInhomSol (-(1 / π)) scorerGi scorerGiDeriv := by
  intro z
  have hG : scorerGiDeriv = fun z => airyBiDeriv z - scorerHiDeriv z := funext scorerGiDeriv_eq
  refine ⟨((hasDerivAt_airyBi z).sub (hasDerivAt_scorerHi z)).congr_deriv
    (by rw [scorerGiDeriv_eq]), ?_⟩
  rw [hG]
  exact ((hasDerivAt_airyBiDeriv z).sub (hasDerivAt_scorerHiDeriv z)).congr_deriv
    (by simp only [scorerGi]; ring)

/-- Rotating the argument of an inhomogeneous solution by a cube root of unity. -/
theorem IsAiryInhomSol.rotate {c ν : ℂ} (hν : ν ^ 3 = 1) {f f' : ℂ → ℂ}
    (hf : IsAiryInhomSol c f f') :
    IsAiryInhomSol (ν ^ 2 * c) (fun z => f (z * ν)) (fun z => ν * f' (z * ν)) := by
  intro z
  have hl : HasDerivAt (fun z : ℂ => z * ν) ν z := (hasDerivAt_id z).mul_const ν |>.congr_deriv
    (by simp)
  have e1 := (hf (z * ν)).1.comp z hl
  have e2 := ((hf (z * ν)).2.comp z hl).const_mul ν
  change HasDerivAt (fun z => f (z * ν)) _ z at e1
  change HasDerivAt (fun z => ν * f' (z * ν)) _ z at e2
  refine ⟨e1.congr_deriv (by ring), e2.congr_deriv ?_⟩
  linear_combination (z * f (z * ν)) * hν

/-- The third-order Wronskian of an inhomogeneous solution and two Airy solutions. -/
lemma airyWronskian3_eq {c : ℂ} {f f' g g' h h' : ℂ → ℂ} (hf : IsAiryInhomSol c f f')
    (hg : IsAirySol g g') (hh : IsAirySol h h') (z : ℂ) :
    airyWronskian3 f g h z = c * (g z * h' z - h z * g' z) := by
  have df : deriv f = f' := funext fun w => (hf w).1.deriv
  have dg : deriv g = g' := funext fun w => (hg w).1.deriv
  have dh : deriv h = h' := funext fun w => (hh w).1.deriv
  simp only [airyWronskian3, df, dg, dh, (hf z).2.deriv, (hg z).2.deriv, (hh z).2.deriv]
  ring

theorem isAirySol_airyAi_mul {ν : ℂ} (hν : ν ^ 3 = 1) :
    IsAirySol (fun t => airyAi (t * ν)) (fun t => ν * airyAiDeriv (t * ν)) := by
  have h := isAirySol_rotated hν
  simp only [mul_comm _ ν]
  exact h

/-- The segment primitive of an entire function differentiates to it. -/
theorem hasDerivAt_primitive {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasDerivAt (primitive f) (f z) z := by
  have he : primitive f = fun w : ℂ => w * ∫ t : ℝ in 0..1, f (t * w) := by
    funext w; simp [primitive, lineIntegral]
  rw [he]; exact Complex.hasDerivAt_mul_integral_comp_mul hf z

theorem primitive_zero (f : ℂ → ℂ) : primitive f 0 = 0 := by simp [primitive, lineIntegral]

/-- `Bi(0) = √3 Ai(0)`. -/
theorem airyBi_zero_eq : airyBi 0 = (Real.sqrt 3 : ℂ) * airyAi 0 := by
  simp only [airyBi, airyAi, airyG_zero, mul_zero, add_zero, sub_zero]

/-- `Bi'(0) = -√3 Ai'(0)`. -/
theorem airyBiDeriv_zero_eq : airyBiDeriv 0 = -(Real.sqrt 3 : ℂ) * airyAiDeriv 0 := by
  simp only [airyBiDeriv, airyAiDeriv, airyFDeriv_zero, mul_zero, zero_add, zero_sub]
  ring

theorem exp_neg_two_pi_I_div_three' : exp (-2 * π * I / 3) = -1 / 2 - (Real.sqrt 3 / 2 : ℝ) * I := by
  rw [show (-2 * π * I / 3 : ℂ) = -(2 * π * I / 3) by ring, exp_neg_two_pi_I_div_three]

theorem exp_neg_pi_I_div_three' : exp (-π * I / 3) = (1 / 2 : ℂ) - (Real.sqrt 3 / 2 : ℝ) * I := by
  rw [show (-π * I / 3 : ℂ) = -(π * I / 3) by ring, exp_neg_pi_I_div_three]

theorem sqrt_three_cube : ((Real.sqrt 3 : ℝ) : ℂ) ^ 3 = 3 * (Real.sqrt 3 : ℝ) := by
  rw [pow_succ, sqrt_three_sq]

theorem sqrt_three_four : ((Real.sqrt 3 : ℝ) : ℂ) ^ 4 = 9 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, sqrt_three_sq]; norm_num

theorem scorerHi_zero_eq : scorerHi 0 = 2 * (Real.sqrt 3 : ℂ) / 3 * airyAi 0 := by
  have h1 := scorer_zero.1
  have h2 := scorer_zero.2.1
  rw [airyBi_zero_eq] at h2
  linear_combination -2 * h1 + 2 * h2

theorem scorerHiDeriv_zero_eq : scorerHiDeriv 0 = -(2 * (Real.sqrt 3 : ℂ) / 3) * airyAiDeriv 0 := by
  have h1 := scorerDeriv_zero.1
  have h2 := scorerDeriv_zero.2.1
  rw [airyBiDeriv_zero_eq] at h2
  linear_combination -2 * h1 + 2 * h2

/-- Normalize polynomial identities in `√3` and `i`. -/
macro "sqrt3_ring" : tactic =>
  `(tactic| (ring_nf; simp only [sqrt_three_sq, sqrt_three_cube, sqrt_three_four, I_sq,
    I_pow_three]; ring_nf))

theorem exp_eps_values {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    exp (ε * (2 * π * I / 3)) = -1 / 2 + ε * (Real.sqrt 3 / 2 : ℝ) * I ∧
    exp (-ε * (2 * π * I / 3)) = -1 / 2 - ε * (Real.sqrt 3 / 2 : ℝ) * I ∧
    exp (-ε * (π * I / 3)) = 1 / 2 - ε * (Real.sqrt 3 / 2 : ℝ) * I ∧
    exp (-ε * (π * I / 6)) = (Real.sqrt 3 / 2 : ℝ) - ε * (1 / 2 : ℂ) * I := by
  rcases hε with rfl | rfl
  · simp only [ofReal_one, one_mul, neg_mul]
    rw [exp_two_pi_I_div_three, exp_neg_two_pi_I_div_three, exp_neg_pi_I_div_three,
      exp_neg_pi_I_div_six]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  · simp only [ofReal_neg, ofReal_one, neg_mul, one_mul, neg_neg]
    rw [exp_two_pi_I_div_three, exp_neg_two_pi_I_div_three, exp_pi_I_div_three,
      exp_pi_I_div_six]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- scorerGi variation (DLMF 9.12.4). -/
@[dlmf 9.12.E4]
theorem scorerGi_variation (z : ℂ) :
    scorerGi z = airyBi z * (1 / 3 - primitive airyAi z) + airyAi z * primitive airyBi z := by
  have hR : IsAiryInhomSol (-(1 / π))
      (fun z => airyBi z * (1 / 3 - primitive airyAi z) + airyAi z * primitive airyBi z)
      (fun z => airyBiDeriv z * (1 / 3 - primitive airyAi z) +
        airyAiDeriv z * primitive airyBi z) := by
    intro z
    have pA := hasDerivAt_primitive differentiable_airyAi z
    have pB := hasDerivAt_primitive differentiable_airyBi z
    refine ⟨(((hasDerivAt_airyBi z).mul ((hasDerivAt_const z (1 / 3 : ℂ)).sub pA)).add
      ((hasDerivAt_airyAi z).mul pB)).congr_deriv (by simp only [Pi.sub_apply]; ring), ?_⟩
    refine (((hasDerivAt_airyBiDeriv z).mul ((hasDerivAt_const z (1 / 3 : ℂ)).sub pA)).add
      ((hasDerivAt_airyAiDeriv z).mul pB)).congr_deriv ?_
    simp only [Pi.sub_apply]
    linear_combination -wronskian_airyAi_airyBi z
  refine isAiryInhomSol_scorerGi.eq_of_initial hR ?_ ?_ z
  · simp only [primitive_zero, sub_zero, mul_zero, add_zero]
    rw [scorer_zero.2.1]; ring
  · simp only [primitive_zero, sub_zero, mul_zero, add_zero]
    rw [scorerDeriv_zero.2.1]; ring

/-- scorerHi variation (DLMF 9.12.5). -/
@[dlmf 9.12.E5]
theorem scorerHi_variation (z : ℂ) :
    scorerHi z = airyBi z * (2 / 3 + primitive airyAi z) - airyAi z * primitive airyBi z := by
  have h := scorerGi_variation z
  simp only [scorerGi] at h
  linear_combination -h

/-- The standard particular and complementary system in 9.12.8. -/
@[dlmf 9.12.E8]
theorem scorerGi_standard_system (z : ℂ) :
    airyWronskian3 (fun t => -scorerGi t) airyAi airyBi z ≠ 0 := by
  have hf : IsAiryInhomSol (1 / π) (fun t => -scorerGi t) (fun t => -scorerGiDeriv t) :=
    scorerGi_ode
  rw [airyWronskian3_eq hf isAirySol_airyAi isAirySol_airyBi,
    show airyAi z * airyBiDeriv z - airyBi z * airyAiDeriv z = 1 / π by
      rw [← wronskian_airyAi_airyBi z]; ring]
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp [hp]

/-- The rotated complementary system of 9.12.9. -/
@[dlmf 9.12.E9]
theorem scorerHi_standard_system (z : ℂ) :
    airyWronskian3 scorerHi (fun t => airyAi (t * exp (-2 * π * I / 3)))
      (fun t => airyAi (t * exp (2 * π * I / 3))) z ≠ 0 := by
  have h1 : exp (-2 * π * I / 3) ^ 3 = 1 := by
    rw [show (-2 * π * I / 3 : ℂ) = -(2 * π * I / 3) by ring]; exact omega_recip_cube
  rw [airyWronskian3_eq isAiryInhomSol_scorerHi (isAirySol_airyAi_mul h1)
    (isAirySol_airyAi_mul omega_cube)]
  have hW := wronskian_airyAi_rotations z
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show airyAi (z * exp (-2 * π * I / 3)) * (exp (2 * π * I / 3) *
      airyAiDeriv (z * exp (2 * π * I / 3))) - airyAi (z * exp (2 * π * I / 3)) *
      (exp (-2 * π * I / 3) * airyAiDeriv (z * exp (-2 * π * I / 3))) = 1 / (2 * π * I) by
    rw [← hW]; ring]
  simp [hp, I_ne_zero]

/-- The two systems in 9.12.10; their sectorial expansions are recorded separately. -/
@[dlmf 9.12.E10]
theorem scorerHi_rotated_standard_system (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyWronskian3 (fun t => exp (-ε * (2 * π * I / 3)) * scorerHi (t * exp (-ε * (2 * π * I / 3))))
      airyAi (fun t => airyAi (t * exp (ε * (2 * π * I / 3)))) z ≠ 0 := by
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> simp
  have h1 : exp (ε * (2 * π * I / 3)) ^ 3 = 1 := by
    have := exp_neg_eps_cube hε'; push_cast at this; simpa using this
  have hf : IsAiryInhomSol (1 / π) _ _ := scorerHi_rotated_ode hε
  rw [airyWronskian3_eq hf isAirySol_airyAi (isAirySol_airyAi_mul h1)]
  have hW := wronskian_airyAi_rotated z hε'
  push_cast at hW
  simp only [neg_neg] at hW
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show airyAi z * (exp (ε * (2 * π * I / 3)) * airyAiDeriv (z * exp (ε * (2 * π * I / 3)))) -
      airyAi (z * exp (ε * (2 * π * I / 3))) * airyAiDeriv z = exp (-ε * (π * I / 6)) / (2 * π) by
    rw [← hW]; ring]
  simp [hp, Complex.exp_ne_zero]

/-- scorerGi add scorerHi (DLMF 9.12.11). -/
@[dlmf 9.12.E11]
theorem scorerGi_add_scorerHi (z : ℂ) :
    scorerGi z + scorerHi z = airyBi z := by
  simp [scorerGi]

/-- scorerGi rotations (DLMF 9.12.12). -/
@[dlmf 9.12.E12]
theorem scorerGi_rotations (z : ℂ) :
    scorerGi z = exp (π * I / 3) / 2 * scorerHi (z * exp (-2 * π * I / 3)) +
      exp (-π * I / 3) / 2 * scorerHi (z * exp (2 * π * I / 3)) := by
  have h1 : exp (-2 * π * I / 3) ^ 3 = 1 := by
    rw [show (-2 * π * I / 3 : ℂ) = -(2 * π * I / 3) by ring]; exact omega_recip_cube
  have hR := ((isAiryInhomSol_scorerHi.rotate h1).const_mul (exp (π * I / 3) / 2)).add
    ((isAiryInhomSol_scorerHi.rotate omega_cube).const_mul (exp (-π * I / 3) / 2))
  have hc : exp (π * I / 3) / 2 * (exp (-2 * π * I / 3) ^ 2 * (1 / π)) +
      exp (-π * I / 3) / 2 * (exp (2 * π * I / 3) ^ 2 * (1 / π)) = -(1 / π) := by
    rw [exp_pi_I_div_three, exp_neg_pi_I_div_three', exp_neg_two_pi_I_div_three',
      exp_two_pi_I_div_three]
    push_cast
    ring_nf
    simp only [sqrt_three_sq, sqrt_three_cube, sqrt_three_four, I_sq, I_pow_three]
    ring
  refine isAiryInhomSol_scorerGi.eq_of_initial (hR.congr_const hc) ?_ ?_ z
  · simp only [zero_mul]
    rw [scorer_zero.1, exp_pi_I_div_three, exp_neg_pi_I_div_three']; ring
  · simp only [zero_mul]
    rw [scorerDeriv_zero.1, exp_pi_I_div_three, exp_neg_pi_I_div_three', exp_neg_two_pi_I_div_three',
      exp_two_pi_I_div_three]
    push_cast
    ring_nf
    simp only [sqrt_three_sq, sqrt_three_cube, sqrt_three_four, I_sq, I_pow_three]
    ring

/-- scorerGi eq rotated scorerHi (DLMF 9.12.13). -/
@[dlmf 9.12.E13]
theorem scorerGi_eq_rotated_scorerHi (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    scorerGi z = exp (-ε * (π * I / 3)) * scorerHi (z * exp (ε * (2 * π * I / 3))) + ε * I * airyAi z := by
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> simp
  have h1 : exp (ε * (2 * π * I / 3)) ^ 3 = 1 := by
    have := exp_neg_eps_cube hε'; push_cast at this; simpa using this
  have hε2 : (ε : ℂ) ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε3 : (ε : ℂ) ^ 3 = ε := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨e1, -, e3, -⟩ := exp_eps_values hε
  have hR := ((isAiryInhomSol_scorerHi.rotate h1).const_mul (exp (-ε * (π * I / 3)))).add
    ((IsAiryInhomSol.of_airy isAirySol_airyAi).const_mul (ε * I))
  have hc : exp (-ε * (π * I / 3)) * (exp (ε * (2 * π * I / 3)) ^ 2 * (1 / π)) + ε * I * 0 =
      -(1 / π) := by
    rw [e1, e3]; push_cast; sqrt3_ring; try (simp only [hε2, hε3]; ring_nf)
  refine isAiryInhomSol_scorerGi.eq_of_initial (hR.congr_const hc) ?_ ?_ z
  · simp only [zero_mul]
    rw [scorer_zero.2.1, airyBi_zero_eq, scorerHi_zero_eq, e3]
    push_cast; sqrt3_ring; try (simp only [hε2, hε3]; ring_nf)
  · simp only [zero_mul]
    rw [scorerDeriv_zero.2.1, airyBiDeriv_zero_eq, scorerHiDeriv_zero_eq, e3, e1]
    push_cast; sqrt3_ring; try (simp only [hε2, hε3]; ring_nf)

/-- scorerHi connection (DLMF 9.12.14). -/
@[dlmf 9.12.E14]
theorem scorerHi_connection (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    scorerHi z = exp (ε * (2 * π * I / 3)) * scorerHi (z * exp (ε * (2 * π * I / 3))) +
      2 * exp (-ε * (π * I / 6)) * airyAi (z * exp (-ε * (2 * π * I / 3))) := by
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> simp
  have h1 : exp (ε * (2 * π * I / 3)) ^ 3 = 1 := by
    have := exp_neg_eps_cube hε'; push_cast at this; simpa using this
  have h2 : exp (-ε * (2 * π * I / 3)) ^ 3 = 1 := exp_neg_eps_cube hε
  have hε2 : (ε : ℂ) ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε3 : (ε : ℂ) ^ 3 = ε := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨e1, e2, -, e4⟩ := exp_eps_values hε
  have hR := ((isAiryInhomSol_scorerHi.rotate h1).const_mul (exp (ε * (2 * π * I / 3)))).add
    ((IsAiryInhomSol.of_airy (isAirySol_airyAi_mul h2)).const_mul (2 * exp (-ε * (π * I / 6))))
  have hc : exp (ε * (2 * π * I / 3)) * (exp (ε * (2 * π * I / 3)) ^ 2 * (1 / π)) +
      2 * exp (-ε * (π * I / 6)) * 0 = 1 / π := by
    rw [mul_zero, add_zero, ← mul_assoc, ← pow_succ', h1, one_mul]
  refine isAiryInhomSol_scorerHi.eq_of_initial (hR.congr_const hc) ?_ ?_ z
  · simp only [zero_mul]
    rw [scorerHi_zero_eq, e1, e4]
    push_cast; sqrt3_ring; try (simp only [hε2, hε3]; ring_nf)
  · simp only [zero_mul]
    rw [scorerHiDeriv_zero_eq, e1, e2, e4]
    push_cast; sqrt3_ring; try (simp only [hε2, hε3]; ring_nf)

/-- Maclaurin coefficient of Gi, DLMF 9.12.15. -/
def scorerGiCoeff (k : ℕ) : ℂ :=
  (3 : ℂ) ^ (-2 / 3 : ℂ) / π * cos ((2 * (k : ℂ) - 1) * π / 3) * Gamma (((k : ℂ) + 1) / 3) *
    ((3 : ℂ) ^ (1 / 3 : ℂ)) ^ k / k.factorial

/-- `(3^{1/3})^3 = 3`. -/
theorem three_cpow_third_cube : ((3 : ℂ) ^ (1 / 3 : ℂ)) ^ 3 = 3 := by
  rw [one_div]; exact_mod_cast cpow_nat_inv_pow (3 : ℂ) (n := 3) (by norm_num)

/-- The three-step recurrence of the Gi coefficients. -/
theorem scorerGiCoeff_rec (k : ℕ) :
    scorerGiCoeff (k + 3) * (((k : ℂ) + 3) * ((k : ℂ) + 2)) = scorerGiCoeff k := by
  simp only [scorerGiCoeff]
  push_cast
  rw [show (2 * ((k : ℂ) + 3) - 1) * π / 3 = (2 * (k : ℂ) - 1) * π / 3 + 2 * π by ring,
    Complex.cos_add_two_pi,
    show ((k : ℂ) + 3 + 1) / 3 = ((k : ℂ) + 1) / 3 + 1 by ring,
    Complex.Gamma_add_one _ (by
      intro h; have := congrArg Complex.re h; simp at this; linarith),
    pow_add, three_cpow_third_cube,
    show k + 3 = (k + 2) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  generalize Gamma (((k : ℂ) + 1) / 3) = G
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have h2 : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 1))
  have h3 : (k : ℂ) + 3 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 2))
  have h2' : (k : ℂ) + 1 + 1 ≠ 0 := by rw [add_assoc]; norm_num; exact h2
  have h3' : (k : ℂ) + 2 + 1 ≠ 0 := by rw [add_assoc]; norm_num; exact h3
  field_simp
  ring

/-- `3^{-2/3} 3^{1/3} = 3^{-1/3}`. -/
theorem three_cpow_neg_two_thirds_mul_third :
    (3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (1 / 3 : ℂ) = (3 : ℂ) ^ (-1 / 3 : ℂ) := by
  rw [← cpow_add _ _ (by norm_num)]; norm_num

/-- `c₀(Gi) = c₀(Hi)/2`. -/
theorem scorerGiCoeff_zero : scorerGiCoeff 0 = scorerHiCoeff 0 / 2 := by
  simp only [scorerGiCoeff, scorerHiCoeff, Nat.cast_zero, mul_zero, zero_sub, pow_zero,
    Nat.factorial_zero, Nat.cast_one, zero_add]
  rw [show (-1 : ℂ) * π / 3 = ((-(π / 3) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
    Real.cos_neg, Real.cos_pi_div_three]
  push_cast
  ring_nf

/-- `c₁(Gi) = c₁(Hi)/2`. -/
theorem scorerGiCoeff_one : scorerGiCoeff 1 = scorerHiCoeff 1 / 2 := by
  simp only [scorerGiCoeff, scorerHiCoeff, Nat.cast_one, pow_one, Nat.factorial_one]
  rw [show (2 * (1 : ℂ) - 1) * π / 3 = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
    Real.cos_pi_div_three, mul_assoc, show ((1 : ℂ) - 2) / 3 = -1 / 3 by norm_num,
    ← three_cpow_neg_two_thirds_mul_third]
  push_cast
  ring

/-- `c₂(Gi) = -1/(2π)`. -/
theorem scorerGiCoeff_two : scorerGiCoeff 2 = -(1 / (2 * π)) := by
  simp only [scorerGiCoeff]
  rw [show (2 * ((2 : ℕ) : ℂ) - 1) * π / 3 = π + 0 by push_cast; ring, Complex.cos_add,
    Complex.cos_pi, Complex.sin_pi, Complex.cos_zero, Complex.sin_zero,
    show (((2 : ℕ) : ℂ) + 1) / 3 = 1 by norm_num, Complex.Gamma_one,
    ← cpow_nat_mul]
  have h : (3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (((2 : ℕ) : ℂ) * (1 / 3)) = 1 := by
    rw [← cpow_add _ _ (by norm_num)]; norm_num
  rw [Nat.factorial_two]
  linear_combination (-1 / (2 * π) : ℂ) * h

/-- The Maclaurin series of Gi sums to an entire function. -/
theorem hasFPowerSeriesOnBall_scorerGiSeries :
    HasFPowerSeriesOnBall (fun z => ∑' k : ℕ, scorerGiCoeff k * z ^ k)
      (FormalMultilinearSeries.ofScalars ℂ scorerGiCoeff) 0 ⊤ := by
  have hr := radius_ofScalars_eq_top_of_rec3 scorerGiCoeff_rec
  have h := (FormalMultilinearSeries.ofScalars ℂ scorerGiCoeff).hasFPowerSeriesOnBall (by rw [hr]; simp)
  rw [hr] at h
  have he : (FormalMultilinearSeries.ofScalars ℂ scorerGiCoeff).sum = fun z => ∑' k : ℕ, scorerGiCoeff k * z ^ k := by
    funext z
    simp only [FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rwa [he] at h

/-- The Gi Maclaurin series solves `w'' = z w - 1/π`. -/
theorem isAiryInhomSol_scorerGiSeries :
    IsAiryInhomSol (-(1 / π)) (fun z => ∑' k : ℕ, scorerGiCoeff k * z ^ k)
      (deriv fun z => ∑' k : ℕ, scorerGiCoeff k * z ^ k) := by
  set f := fun z => ∑' k : ℕ, scorerGiCoeff k * z ^ k
  have h0 := hasFPowerSeriesOnBall_scorerGiSeries
  have h1 := h0.deriv_ofScalars
  have h2 := h1.deriv_ofScalars
  intro z
  refine ⟨((h0.analyticAt_of_mem (mem_eball_top z)).differentiableAt).hasDerivAt, ?_⟩
  have hdiff : DifferentiableAt ℂ (deriv f) z :=
    (h1.analyticAt_of_mem (mem_eball_top z)).differentiableAt
  have hs := h2.hasSum_mul_pow (mem_eball_top z)
  have hH := (h0.hasSum_mul_pow (mem_eball_top z)).mul_left z
  have hs' : HasSum (fun n : ℕ => ((n : ℂ) + 1) * (((n + 1 : ℕ) : ℂ) + 1) *
      scorerGiCoeff (n + 2) * z ^ n) (z * f z + -(1 / π)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_zero, mul_one, scorerGiCoeff_two]
    convert hH using 1
    · funext n
      have := scorerGiCoeff_rec n
      rw [show n + 1 + 2 = n + 3 by ring, pow_succ]
      push_cast
      linear_combination (z * z ^ n) * this
    · push_cast; ring
  have he : deriv (deriv f) z = z * f z + -(1 / π) :=
    hs.unique (by simpa only [mul_assoc] using hs')
  have := hdiff.hasDerivAt
  rwa [he] at this

/-- The Gi Maclaurin series equals Gi. -/
theorem scorerGiSeries_eq : (fun z => ∑' k : ℕ, scorerGiCoeff k * z ^ k) = scorerGi := by
  have h0 := hasFPowerSeriesOnBall_scorerGiSeries
  funext z
  refine isAiryInhomSol_scorerGiSeries.eq_of_initial isAiryInhomSol_scorerGi ?_ ?_ z
  · rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
    simp only [pow_zero, mul_one]
    rw [scorerGiCoeff_zero, scorer_zero.1, scorerHi, tsum_eq_single 0
      (fun k hk => by simp [zero_pow hk])]
    simp
  · have h := h0.deriv_ofScalars.hasSum_mul_pow (mem_eball_top 0)
    have h' : HasSum (fun n : ℕ => ((n : ℂ) + 1) * scorerGiCoeff (n + 1) * (0 : ℂ) ^ n)
        ((((0 : ℕ) : ℂ) + 1) * scorerGiCoeff (0 + 1) * (0 : ℂ) ^ 0) :=
      hasSum_single 0 (fun n hn => by simp [zero_pow hn])
    simp only [Nat.cast_zero, zero_add, one_mul, pow_zero, mul_one] at h'
    rw [h.unique h', scorerGiCoeff_one, scorerDeriv_zero.1, scorerHiDeriv_zero]

/-- hasSum scorerGi (DLMF 9.12.15). -/
@[dlmf 9.12.E15]
theorem hasSum_scorerGi (z : ℂ) :
    HasSum (fun k : ℕ => (3 : ℂ) ^ (-2 / 3 : ℂ) / π * cos ((2 * (k : ℂ) - 1) * π / 3) *
      Gamma (((k : ℂ) + 1) / 3) * ((3 : ℂ) ^ (1 / 3 : ℂ) * z) ^ k / k.factorial) (scorerGi z) := by
  have h := hasFPowerSeriesOnBall_scorerGiSeries.hasSum_mul_pow (mem_eball_top z)
  rw [show (∑' k : ℕ, scorerGiCoeff k * z ^ k) = scorerGi z from congrFun scorerGiSeries_eq z] at h
  convert h using 1
  funext k
  simp only [scorerGiCoeff]
  ring

/-- hasSum scorerGiDeriv (DLMF 9.12.16). -/
@[dlmf 9.12.E16]
theorem hasSum_scorerGiDeriv (z : ℂ) :
    HasSum (fun k : ℕ => (3 : ℂ) ^ (-1 / 3 : ℂ) / π * cos ((2 * (k : ℂ) + 1) * π / 3) *
      Gamma (((k : ℂ) + 2) / 3) * ((3 : ℂ) ^ (1 / 3 : ℂ) * z) ^ k / k.factorial) (scorerGiDeriv z) := by
  have h := hasFPowerSeriesOnBall_scorerGiSeries.deriv_ofScalars.hasSum_mul_pow (mem_eball_top z)
  rw [scorerGiSeries_eq] at h
  rw [show scorerGiDeriv z = deriv scorerGi z from rfl]
  convert h using 1
  funext k
  simp only [scorerGiCoeff]
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  rw [Nat.factorial_succ, ← three_cpow_neg_two_thirds_mul_third]
  push_cast
  rw [show (2 * ((k : ℂ) + 1) - 1) = 2 * (k : ℂ) + 1 by ring,
    show ((k : ℂ) + 1 + 1) = (k : ℂ) + 2 by ring]
  field_simp
  ring

/-- hasSum scorerHi (DLMF 9.12.17). -/
@[dlmf 9.12.E17]
theorem hasSum_scorerHi (z : ℂ) :
    HasSum (fun k : ℕ => scorerHiCoeff k * z ^ k) (scorerHi z) := by
  exact hasFPowerSeriesOnBall_scorerHi.hasSum_mul_pow (mem_eball_top z)

/-- hasSum scorerHiDeriv (DLMF 9.12.18). -/
@[dlmf 9.12.E18]
theorem hasSum_scorerHiDeriv (z : ℂ) :
    HasSum (fun k : ℕ => (3 : ℂ) ^ (-1 / 3 : ℂ) / π * Gamma (((k : ℂ) + 2) / 3) *
      ((3 : ℂ) ^ (1 / 3 : ℂ) * z) ^ k / k.factorial) (scorerHiDeriv z) := by
  have h := hasFPowerSeriesOnBall_scorerHi.deriv_ofScalars.hasSum_mul_pow (mem_eball_top z)
  change HasSum _ (deriv scorerHi z)
  convert h using 1
  funext n
  simp only [scorerHiCoeff]
  rw [mul_pow, ← Complex.cpow_nat_mul, mul_div_assoc, mul_div_assoc]
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have h1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have e : (3 : ℂ) ^ (-1 / 3 : ℂ) * (3 : ℂ) ^ ((n : ℂ) * (1 / 3)) =
      (3 : ℂ) ^ ((((n + 1 : ℕ) : ℂ) - 2) / 3) := by
    rw [← Complex.cpow_add _ _ (by norm_num)]; congr 1; push_cast; ring
  rw [Nat.factorial_succ, ← e, show (((n + 1 : ℕ) : ℂ) + 1) = (n : ℂ) + 2 by push_cast; ring]
  push_cast
  field_simp

-- `scorerGi_sin_integral` (DLMF 9.12.19) is in `DLMF/Airy/IntegralRepresentations.lean`.

/-- `t^k e^{-t³/3}` in `rpow` form. -/
theorem pow_mul_exp_neg_cube_eq (k : ℕ) :
    (fun t : ℝ => t ^ k * Real.exp (-(t ^ 3 / 3))) =
      fun t : ℝ => t ^ (k : ℝ) * Real.exp (-(1 / 3) * t ^ (3 : ℝ)) := by
  funext t
  rw [Real.rpow_natCast, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring_nf

/-- `t^k e^{-t³/3}` is integrable on `(0,∞)`. -/
theorem integrableOn_pow_mul_exp_neg_cube (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(t ^ 3 / 3))) (Ioi 0) := by
  rw [pow_mul_exp_neg_cube_eq]
  exact integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith [k.cast_nonneg (α := ℝ)])
    (by norm_num) (by norm_num)

/-- `∫₀^∞ t^k e^{-t³/3} dt = 3^{(k-2)/3} Γ((k+1)/3)`. -/
theorem integral_pow_mul_exp_neg_cube (k : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (-(t ^ 3 / 3)) =
      (3 : ℝ) ^ (((k : ℝ) - 2) / 3) * Real.Gamma (((k : ℝ) + 1) / 3) := by
  rw [pow_mul_exp_neg_cube_eq, _root_.integral_rpow_mul_exp_neg_mul_rpow (by norm_num)
    (by linarith [k.cast_nonneg (α := ℝ)]) (by norm_num)]
  congr 1
  rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
    show (3 : ℝ)⁻¹ = (3 : ℝ) ^ (-1 : ℝ) by norm_num, ← Real.rpow_add (by norm_num)]
  congr 1; ring

/-- The real form of the Hi coefficients. -/
theorem scorerHiCoeff_eq_ofReal (k : ℕ) :
    scorerHiCoeff k = (((3 : ℝ) ^ (((k : ℝ) - 2) / 3) * Real.Gamma (((k : ℝ) + 1) / 3) /
      (π * k !) : ℝ) : ℂ) := by
  rw [scorerHiCoeff]
  push_cast
  rw [← Complex.Gamma_ofReal, ofReal_cpow (by norm_num)]
  push_cast; ring_nf

/-- `t^m e^{-t³/3 + z t}` is integrable on `(0,∞)`. -/
theorem integrableOn_pow_mul_exp_cubic (m : ℕ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ m * exp (-(t : ℂ) ^ 3 / 3 + z * t)) (Ioi 0) := by
  set b : ℝ := |z.re| + 2
  have hb : 1 ≤ b := by simp only [b]; linarith [abs_nonneg z.re]
  have hint : IntegrableOn (fun t : ℝ => (m ! * Real.exp (b ^ 2 + 3 * b)) * Real.exp (-1 * t))
      (Ioi 0) := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul _
  refine hint.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg ht.le, norm_exp]
  have hre : (-(t : ℂ) ^ 3 / 3 + z * t).re = -(t ^ 3 / 3) + z.re * t := by
    simp [pow_succ]; ring
  rw [hre]
  have h1 : t ^ m ≤ m ! * Real.exp t := by
    have := Real.pow_div_factorial_le_exp t ht.le m
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 : -(t ^ 3 / 3) + z.re * t ≤ b ^ 2 + 3 * b + -1 * t - t := by
    have hz : z.re * t ≤ (b - 2) * t := by
      have := le_abs_self z.re
      nlinarith
    have key : b * t ≤ t ^ 3 / 3 + b ^ 2 + 3 * b := by
      rcases le_or_gt (3 * b) (t ^ 2) with h | h
      · nlinarith
      · nlinarith [sq_nonneg (b * t - b ^ 2 - 3 * b), sq_nonneg t, mul_pos ht (by linarith : (0:ℝ) < b)]
    linarith
  calc t ^ m * Real.exp (-(t ^ 3 / 3) + z.re * t)
      ≤ (m ! * Real.exp t) * Real.exp (b ^ 2 + 3 * b + -1 * t - t) :=
        mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (by positivity)
    _ = (m ! * Real.exp (b ^ 2 + 3 * b)) * Real.exp (-1 * t) := by
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]; ring_nf

/-- Termwise integration of `t^m e^{-t³/3} e^{zt}` over `(0,∞)`. -/
theorem hasSum_integral_pow_mul_exp_cubic (m : ℕ) (z : ℂ)
    (hs : Summable fun k : ℕ => ‖z‖ ^ k / k ! *
      ∫ t in Ioi (0 : ℝ), t ^ (k + m) * Real.exp (-(t ^ 3 / 3))) :
    HasSum (fun k : ℕ => z ^ k / k ! *
        ((∫ t in Ioi (0 : ℝ), t ^ (k + m) * Real.exp (-(t ^ 3 / 3)) : ℝ) : ℂ))
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * exp (-(t : ℂ) ^ 3 / 3 + z * t)) := by
  set F : ℕ → ℝ → ℂ := fun k t => z ^ k / k ! * ((t ^ (k + m) * Real.exp (-(t ^ 3 / 3)) : ℝ) : ℂ)
  have hF : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := fun k =>
    ((integrableOn_pow_mul_exp_neg_cube (k + m)).ofReal).const_mul _
  have hnorm : ∀ k, ∫ t in Ioi (0 : ℝ), ‖F k t‖ =
      ‖z‖ ^ k / k ! * ∫ t in Ioi (0 : ℝ), t ^ (k + m) * Real.exp (-(t ^ 3 / 3)) := by
    intro k
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [F, norm_mul, norm_div, norm_pow, norm_natCast, norm_real,
      Real.norm_of_nonneg ht.le, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h := hasSum_integral_of_summable_integral_norm hF (by simpa only [hnorm] using hs)
  convert h using 1
  · funext k
    simp only [F]
    rw [integral_const_mul, integral_complex_ofReal]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    have he := (NormedSpace.expSeries_div_hasSum_exp (z * t)).mul_left
      ((t : ℂ) ^ m * exp (-(t : ℂ) ^ 3 / 3))
    rw [← Complex.exp_eq_exp_ℂ] at he
    rw [exp_add, ← mul_assoc, ← he.tsum_eq]
    congr 1
    funext k
    simp only [F]
    push_cast
    rw [neg_div]
    ring

/-- `c_k = I_k/(π k!)` with `I_k = ∫₀^∞ t^k e^{-t³/3}`. -/
theorem scorerHiCoeff_eq_integral (k : ℕ) :
    scorerHiCoeff k = ((∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (-(t ^ 3 / 3)) : ℝ) : ℂ) /
      (π * k !) := by
  rw [scorerHiCoeff_eq_ofReal, integral_pow_mul_exp_neg_cube]; push_cast; ring

/-- scorerHi exp integral (DLMF 9.12.20). -/
@[dlmf 9.12.E20]
theorem scorerHi_exp_integral (z : ℂ) :
    IntegrableOn (fun t : ℝ => exp (-(t : ℂ) ^ 3 / 3 + z * t)) (Ioi 0) ∧
      scorerHi z = (∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 + z * t)) / π := by
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨by simpa using integrableOn_pow_mul_exp_cubic 0 z, ?_⟩
  have hs : Summable fun k : ℕ => ‖z‖ ^ k / k ! *
      ∫ t in Ioi (0 : ℝ), t ^ (k + 0) * Real.exp (-(t ^ 3 / 3)) := by
    have h := (hasSum_scorerHi (‖z‖ : ℂ)).summable
    have h' : Summable fun k : ℕ => (((∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (-(t ^ 3 / 3))) /
        (π * k !) * ‖z‖ ^ k : ℝ) : ℂ) := by
      refine h.congr fun k => ?_
      rw [scorerHiCoeff_eq_integral]; push_cast; ring
    refine ((Complex.summable_ofReal.mp h').mul_left π).congr fun k => ?_
    simp only [add_zero]
    field_simp
  have h := (hasSum_integral_pow_mul_exp_cubic 0 z hs).div_const π
  simp only [pow_zero, one_mul, add_zero] at h
  refine (hasSum_scorerHi z).unique (h.congr_fun fun k => ?_)
  rw [scorerHiCoeff_eq_integral]
  field_simp

/-- scorerGi exp cos integral (DLMF 9.12.21). -/
@[dlmf 9.12.E21]
theorem scorerGi_exp_cos_integral (z : ℂ) :
    scorerGi z = -(∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 - z * t / 2) *
      cos (Real.sqrt 3 * z * t / 2 + 2 * π / 3)) / π := by
  rw [scorerGi_rotations, (scorerHi_exp_integral _).2, (scorerHi_exp_integral _).2]
  have i1 := (scorerHi_exp_integral (z * exp (-2 * π * I / 3))).1
  have i2 := (scorerHi_exp_integral (z * exp (2 * π * I / 3))).1
  rw [mul_div_assoc', mul_div_assoc', ← add_div, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (i1.const_mul _) (i2.const_mul _), ← integral_neg]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  rw [exp_neg_two_pi_I_div_three', exp_two_pi_I_div_three]
  set θ : ℂ := Real.sqrt 3 * z * t / 2 + 2 * π / 3
  have hpi : ∀ w : ℂ, exp (w + π * I) = -exp w := fun w => by rw [exp_add, exp_pi_mul_I]; ring
  have hpi' : ∀ w : ℂ, exp (w - π * I) = -exp w := fun w => by
    rw [exp_sub, exp_pi_mul_I]; ring
  have e1 : exp (π * I / 3) * exp (-(t : ℂ) ^ 3 / 3 + z * (-1 / 2 - (Real.sqrt 3 / 2 : ℝ) * I) * t)
      = -exp (-(t : ℂ) ^ 3 / 3 - z * t / 2 - θ * I) := by
    rw [← exp_add, ← hpi]; congr 1; simp only [θ]; push_cast; ring
  have e2 : exp (-π * I / 3) * exp (-(t : ℂ) ^ 3 / 3 + z * (-1 / 2 + (Real.sqrt 3 / 2 : ℝ) * I) * t)
      = -exp (-(t : ℂ) ^ 3 / 3 - z * t / 2 + θ * I) := by
    rw [← exp_add, ← hpi']; congr 1; simp only [θ]; push_cast; ring
  have hc : cos θ = (exp (θ * I) + exp (-θ * I)) / 2 := by
    rw [Complex.cos]
  rw [hc]
  have := e1; have := e2
  rw [show exp (-(t : ℂ) ^ 3 / 3 - z * t / 2 - θ * I) =
      exp (-(t : ℂ) ^ 3 / 3 - z * t / 2) * exp (-θ * I) by rw [← exp_add]; ring_nf] at e1
  rw [show exp (-(t : ℂ) ^ 3 / 3 - z * t / 2 + θ * I) =
      exp (-(t : ℂ) ^ 3 / 3 - z * t / 2) * exp (θ * I) by rw [← exp_add]] at e2
  linear_combination (1 / 2 : ℂ) * e1 + (1 / 2 : ℂ) * e2

/-- scorerHi stieltjes integral (DLMF 9.12.22). -/
@[dlmf 9.12.E22]
theorem scorerHi_stieltjes_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π / 3) :
    scorerHi (-z) = 4 * z ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * π ^ 2) *
      ∫ t : ℝ in Ioi 0, DLMF.Bessel.besselK (1 / 3) t / (airyZetaComplex z ^ 2 + (t : ℂ) ^ 2) := by
  sorry

/-- scorerGi principalValue (DLMF 9.12.23). -/
@[dlmf 9.12.E23]
theorem scorerGi_principalValue {x : ℝ} (hx : 0 < x) :
    scorerGi x = 4 * (x : ℂ) ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * π ^ 2) *
      principalValueIoi (fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t /
        ((airyZeta x : ℂ) ^ 2 - (t : ℂ) ^ 2)) (airyZeta x) := by
  sorry

/-- Barnes contour on a separating vertical line; boundary values are ordinary improper integrals (DLMF 9.12.24). -/
@[dlmf 9.12.E24]
theorem scorerHi_mellinBarnes {z : ℂ} (hz0 : z ≠ 0) (hz : |arg (-z)| < 2 * π / 3) {σ : ℝ} (hσ0 : -1 < σ) (hσ1 : σ < 0) :
    HasIntegralWholeLine (fun y : ℝ => Gamma (1 / 3 + ((σ : ℂ) + y * I) / 3) *
      Gamma (-((σ : ℂ) + y * I)) *
        exp (((σ : ℂ) + y * I) * (log (3 : ℂ) / 3 + log (-z))))
      (2 * π ^ 2 * (3 : ℂ) ^ (2 / 3 : ℂ) * scorerHi z) := by
  sorry

/-- `I_{k+1}/k!` form of the Hi′ coefficients. -/
theorem scorerHiDeriv_coeff_eq_integral (k : ℕ) (z : ℂ) :
    (3 : ℂ) ^ (-1 / 3 : ℂ) / π * Gamma (((k : ℂ) + 2) / 3) * ((3 : ℂ) ^ (1 / 3 : ℂ) * z) ^ k /
      k ! = z ^ k / k ! *
        ((∫ t in Ioi (0 : ℝ), t ^ (k + 1) * Real.exp (-(t ^ 3 / 3)) : ℝ) : ℂ) / π := by
  rw [integral_pow_mul_exp_neg_cube, mul_pow, ← cpow_nat_mul]
  push_cast
  rw [← Complex.Gamma_ofReal, ofReal_cpow (by norm_num)]
  push_cast
  have h3 : (3 : ℂ) ^ (-1 / 3 : ℂ) * (3 : ℂ) ^ ((k : ℂ) * (1 / 3)) =
      (3 : ℂ) ^ (((k : ℂ) + 1 - 2) / 3) := by
    rw [← cpow_add _ _ (by norm_num)]; ring_nf
  rw [show ((k : ℂ) + 1 + 1) / 3 = ((k : ℂ) + 2) / 3 by ring]
  linear_combination (Gamma (((k : ℂ) + 2) / 3) * z ^ k / π / k !) * h3

/-- Laplace integral for Hi′. -/
theorem scorerHiDeriv_exp_integral (z : ℂ) :
    scorerHiDeriv z = (∫ t : ℝ in Ioi 0, (t : ℂ) * exp (-(t : ℂ) ^ 3 / 3 + z * t)) / π := by
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : Summable fun k : ℕ => ‖z‖ ^ k / k ! *
      ∫ t in Ioi (0 : ℝ), t ^ (k + 1) * Real.exp (-(t ^ 3 / 3)) := by
    have h := (hasSum_scorerHiDeriv (‖z‖ : ℂ)).summable
    have h' : Summable fun k : ℕ => ((‖z‖ ^ k / k ! *
        (∫ t in Ioi (0 : ℝ), t ^ (k + 1) * Real.exp (-(t ^ 3 / 3))) / π : ℝ) : ℂ) := by
      refine h.congr fun k => ?_
      rw [scorerHiDeriv_coeff_eq_integral]; push_cast; ring
    refine ((Complex.summable_ofReal.mp h').mul_left π).congr fun k => ?_
    field_simp
  have h := (hasSum_integral_pow_mul_exp_cubic 1 z hs).div_const π
  simp only [pow_one] at h
  refine (hasSum_scorerHiDeriv z).unique (h.congr_fun fun k => ?_)
  rw [scorerHiDeriv_coeff_eq_integral]

/-! ### Asymptotic expansions of Hi, Hi', Gi, Gi' (DLMF 9.12(viii))

The Laplace integrals `π Hi(z) = ∫₀^∞ e^{zt} e^{-t³/3} dt` and `π Hi'(z) = ∫₀^∞ e^{zt} t e^{-t³/3} dt`
are rotated to rays `|arg t| < π/6` and expanded by Watson's lemma
(`hasAsymptoticExpansion_integral_cexp_smul_rotate_comap`); two rotated rays cover the sector
`|arg(-z)| < 2π/3`. The expansions of `Gi`, `Gi'` follow from the rotation formula 9.12.12. -/

/-- The cubic kernel `e^{-t³/3}` along the ray `t = r e^{iy}`. -/
theorem scorerAsym_norm_kernel (r y : ℝ) :
    ‖cexp (-(((r : ℂ) * exp (y * I)) ^ 3 / 3))‖ = Real.exp (-(r ^ 3 * Real.cos (3 * y)) / 3) := by
  rw [Complex.norm_exp]
  congr 1
  have h : ((r : ℂ) * exp (y * I)) ^ 3 = ((r ^ 3 : ℝ) : ℂ) * exp (((3 * y : ℝ) : ℂ) * I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf
  rw [h, neg_re, div_ofNat_re, re_ofReal_mul, exp_ofReal_mul_I_re]
  ring

/-- The cubic kernel is bounded by `1` in the sector `|arg t| ≤ π/6`. -/
theorem scorerAsym_norm_kernel_le_one {r : ℝ} (hr : 0 ≤ r) {y : ℝ} (hy : |y| ≤ π / 6) :
    ‖cexp (-(((r : ℂ) * exp (y * I)) ^ 3 / 3))‖ ≤ 1 := by
  rw [scorerAsym_norm_kernel, Real.exp_le_one_iff]
  have : 0 ≤ Real.cos (3 * y) := by
    rw [← Real.cos_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg y, Real.pi_pos], by linarith⟩
  have := mul_nonneg (pow_nonneg hr 3) this
  linarith

/-- `r^m e^{-cr - br³}` is integrable on `(0, ∞)` for `b > 0`. -/
theorem scorerAsym_integrableOn_pow_exp (m : ℕ) (c : ℝ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => r ^ m * Real.exp (-c * r - b * r ^ 3)) (Ioi 0) := by
  set A : ℝ := |c| + 2
  set R : ℝ := Real.sqrt (A / b)
  have hA : 2 ≤ A := by simp only [A]; linarith [abs_nonneg c]
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = A / b := Real.sq_sqrt (by positivity)
  have hint : IntegrableOn (fun r : ℝ => (m.factorial * Real.exp (A * R)) * Real.exp (-1 * r))
      (Ioi 0) := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul _
  refine hint.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : 0 < r)
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hr.le, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : r ^ m ≤ m.factorial * Real.exp r := by
    have := Real.pow_div_factorial_le_exp r hr.le m
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have hc : -c * r ≤ (A - 2) * r := by
    have := neg_abs_le c
    have : -c ≤ A - 2 := by simp only [A]; linarith
    nlinarith
  have h2 : -c * r - b * r ^ 3 ≤ A * R + -1 * r - r := by
    rcases le_or_gt R r with h | h
    · have : A * r ≤ b * r ^ 3 := by
        have hb2 : A = b * R ^ 2 := by rw [hR2]; field_simp
        rw [hb2]
        have : R ^ 2 ≤ r ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hb.le hr.le)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ A) hR0]
    · have : 0 ≤ b * r ^ 3 := by positivity
      nlinarith
  calc r ^ m * Real.exp (-c * r - b * r ^ 3)
      ≤ (m.factorial * Real.exp r) * Real.exp (A * R + -1 * r - r) :=
        mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (by positivity)
    _ = (m.factorial * Real.exp (A * R)) * Real.exp (-1 * r) := by
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]; ring_nf

/-- The rotated kernel `(re^{iθ})^m e^{-(re^{iθ})³/3}` is Laplace-integrable for `|θ| < π/6`. -/
theorem scorerAsym_integrableOn_rotate (m : ℕ) (c : ℝ) {θ : ℝ} (hθ : |θ| < π / 6) :
    IntegrableOn (fun r : ℝ => Real.exp (-c * r) •
      (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)))) (Ioi 0) := by
  have hb : 0 < Real.cos (3 * θ) / 3 := by
    have : 0 < Real.cos (3 * θ) := by
      rw [← Real.cos_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg θ, Real.pi_pos], by linarith⟩
    positivity
  refine (scorerAsym_integrableOn_pow_exp m c hb).mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : 0 < r)
    rw [norm_smul, norm_mul, norm_pow, norm_mul, norm_real, norm_exp_ofReal_mul_I, mul_one,
      scorerAsym_norm_kernel, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg hr.le, ← mul_assoc, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
    apply le_of_eq; congr 2; ring


/-- The Laplace integral `∫₀^∞ e^{-wt} t^m e^{-t³/3} dt` (an entire function of `w`). -/
noncomputable def scorerAsym_laplace (m : ℕ) (w : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(w * t)) • ((t : ℂ) ^ m * cexp (-((t : ℂ) ^ 3 / 3)))

theorem scorerAsym_integrableOn_zero (m : ℕ) (c : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * t) • ((t : ℂ) ^ m * cexp (-((t : ℂ) ^ 3 / 3))))
      (Ioi 0) := by
  have h := scorerAsym_integrableOn_rotate m c (θ := 0) (by rw [abs_zero]; positivity)
  simpa using h

theorem scorerAsym_differentiable_laplace (m : ℕ) : Differentiable ℂ (scorerAsym_laplace m) :=
  fun w => (differentiableOn_integral_cexp_neg_mul_smul
    (scorerAsym_integrableOn_zero m (w.re - 1))).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp))

/-- Hi and Hi' as Laplace integrals: `π Hi(z) = L₀(-z)`, `π Hi'(z) = L₁(-z)`. -/
theorem scorerAsym_scorerHi_eq (z : ℂ) : π * scorerHi z = scorerAsym_laplace 0 (-z) := by
  rw [(scorerHi_exp_integral z).2, scorerAsym_laplace, mul_div_cancel₀ _
    (ofReal_ne_zero.mpr Real.pi_ne_zero)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul, pow_zero, one_mul]
  rw [← Complex.exp_add]; ring_nf

theorem scorerAsym_scorerHiDeriv_eq (z : ℂ) : π * scorerHiDeriv z = scorerAsym_laplace 1 (-z) := by
  rw [scorerHiDeriv_exp_integral z, scorerAsym_laplace, mul_div_cancel₀ _
    (ofReal_ne_zero.mpr Real.pi_ne_zero)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul, pow_one]
  rw [mul_left_comm, ← Complex.exp_add]; ring_nf

/-- **Rotation of the Laplace contour** for `|θ| < π/6`, valid for every complex `w`. -/
theorem scorerAsym_laplace_rotate (m : ℕ) {θ : ℝ} (hθ : |θ| < π / 6) (w : ℂ) :
    scorerAsym_laplace m w = exp (θ * I) • ∫ r in Ioi (0 : ℝ), cexp (-(w * exp (θ * I) * r)) •
      (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3))) := by
  have hd2 : Differentiable ℂ (fun w : ℂ => exp (θ * I) • ∫ r in Ioi (0 : ℝ),
      cexp (-(w * exp (θ * I) * r)) •
        (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)))) := by
    have hL : Differentiable ℂ (fun v : ℂ => ∫ r in Ioi (0 : ℝ), cexp (-(v * r)) •
        (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)))) := fun v =>
      (differentiableOn_integral_cexp_neg_mul_smul
        (scorerAsym_integrableOn_rotate m (v.re - 1) hθ)).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp))
    exact (hL.comp (differentiable_id.mul_const (exp (θ * I)))).const_smul (exp (θ * I))
  have hy : ∀ y ∈ uIcc 0 θ, |y| ≤ π / 6 := fun y hy =>
    (abs_le_abs_of_mem_uIcc_zero hy).trans hθ.le
  have hreal : ∀ x : ℝ, 0 < x → scorerAsym_laplace m x = exp (θ * I) • ∫ r in Ioi (0 : ℝ),
      cexp (-((x : ℂ) * exp (θ * I) * r)) •
        (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3))) := by
    intro x hx
    simp only [scorerAsym_laplace, smul_eq_mul]
    refine integral_cexp_neg_mul_mul_eq_rotate (F := fun t => t ^ m * cexp (-(t ^ 3 / 3)))
      (σ := m + 1) (C := 1) (k := m) (by positivity) (fun r _ y _ => by fun_prop)
      (fun r hr _ y hy' => ?_) (fun r hr y hy' => ?_) (fun y hy' => ?_)
    · rw [add_sub_cancel_right, one_mul, Real.rpow_natCast, norm_mul, norm_pow, norm_mul,
        norm_real, Real.norm_of_nonneg hr.le, norm_exp_ofReal_mul_I, mul_one]
      calc r ^ m * _ ≤ r ^ m * 1 := by
            gcongr; exact scorerAsym_norm_kernel_le_one hr.le (hy y hy')
        _ = r ^ m := mul_one _
    · have hr0 : 0 ≤ r := by linarith
      rw [one_mul, Real.rpow_natCast, norm_mul, norm_pow, norm_mul,
        norm_real, Real.norm_of_nonneg hr0, norm_exp_ofReal_mul_I, mul_one]
      calc r ^ m * _ ≤ r ^ m * 1 := by
            gcongr; exact scorerAsym_norm_kernel_le_one hr0 (hy y hy')
        _ = r ^ m := mul_one _
    · rw [re_ofReal_mul, exp_ofReal_mul_I_re]
      have := hy y hy'
      exact mul_pos hx (Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le y, Real.pi_pos],
        by linarith [le_abs_self y, Real.pi_pos]⟩)
  have hfreq : ∃ᶠ v in 𝓝[≠] (1 : ℂ), scorerAsym_laplace m v = exp (θ * I) •
      ∫ r in Ioi (0 : ℝ), cexp (-(v * exp (θ * I) * r)) •
        (((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3))) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
        rwa [ofReal_one] at this
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact hreal r hr
  exact ((scorerAsym_differentiable_laplace m).differentiableOn.analyticOnNhd
    isOpen_univ).eqOn_of_preconnected_of_frequently_eq
    (hd2.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ _) hfreq
    (mem_univ w)


/-- Taylor coefficients of `e^{-t³/3} = ∑ aₙ tⁿ`. -/
noncomputable def scorerAsym_coeff (n : ℕ) : ℂ :=
  if 3 ∣ n then (-1 / 3 : ℂ) ^ (n / 3) / ((n / 3).factorial : ℂ) else 0

theorem scorerAsym_sum_coeff (t : ℂ) (M : ℕ) :
    (∑ n ∈ Finset.range (3 * M), t ^ n * scorerAsym_coeff n =
      ∑ k ∈ Finset.range M, (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ)) ∧
    (∑ n ∈ Finset.range (3 * M + 1), t ^ n * scorerAsym_coeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ)) ∧
    (∑ n ∈ Finset.range (3 * M + 2), t ^ n * scorerAsym_coeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ)) := by
  have h0 : ∀ M : ℕ, ∑ n ∈ Finset.range (3 * M), t ^ n * scorerAsym_coeff n =
      ∑ k ∈ Finset.range M, (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show 3 * (M + 1) = 3 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have h1 : ¬ 3 ∣ 3 * M + 1 := by omega
      have h2 : ¬ 3 ∣ 3 * M + 1 + 1 := by omega
      have h3 : (3 * M) / 3 = M := by omega
      simp only [scorerAsym_coeff, h1, h2, ite_false, mul_zero, add_zero,
        dvd_mul_right, ite_true, h3]
      congr 1
      rw [pow_mul, neg_pow, div_pow]
      field_simp
      rw [div_pow]; field_simp
  have h1 : ∑ n ∈ Finset.range (3 * M + 1), t ^ n * scorerAsym_coeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ) := by
    rw [Finset.sum_range_succ, h0, Finset.sum_range_succ]
    have h3 : (3 * M) / 3 = M := by omega
    simp only [scorerAsym_coeff, dvd_mul_right, ite_true, h3]
    congr 1
    rw [pow_mul, neg_pow, div_pow]
    field_simp
    rw [div_pow]; field_simp
  refine ⟨h0 M, h1, ?_⟩
  rw [Finset.sum_range_succ, h1]
  have h2 : ¬ 3 ∣ 3 * M + 1 := by omega
  simp [scorerAsym_coeff, h2]

/-- Taylor remainders of `t^m e^{-t³/3}` along a ray, as required by Watson's lemma. -/
theorem scorerAsym_sub_sum_isBigO (m : ℕ) (θ : ℝ) (N : ℕ) :
    (fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ m * cexp (-(((r : ℂ) * exp (θ * I)) ^ 3 / 3)) -
      ∑ n ∈ Finset.range N,
        (((r : ℂ) * exp (θ * I)) ^ ((n : ℂ) + ((m : ℂ) + 1) - 1)) • scorerAsym_coeff n)
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + ((m : ℂ) + 1).re - 1) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, N ≤ 3 * M ∧
      ∀ t : ℂ, ∑ n ∈ Finset.range N, t ^ n * scorerAsym_coeff n =
        ∑ k ∈ Finset.range M, (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ) := by
    rcases (by omega : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2) with h | h | h
    · obtain ⟨q, rfl⟩ : ∃ q, N = 3 * q := ⟨N / 3, by omega⟩
      exact ⟨q, le_rfl, fun t => (scorerAsym_sum_coeff t q).1⟩
    · obtain ⟨q, rfl⟩ : ∃ q, N = 3 * q + 1 := ⟨N / 3, by omega⟩
      exact ⟨q + 1, by omega, fun t => (scorerAsym_sum_coeff t q).2.1⟩
    · obtain ⟨q, rfl⟩ : ∃ q, N = 3 * q + 2 := ⟨N / 3, by omega⟩
      exact ⟨q + 1, by omega, fun t => (scorerAsym_sum_coeff t q).2.2⟩
  refine IsBigO.of_bound 3 ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))]
    with r hr hr1
  have hr : (0 : ℝ) < r := hr
  have hr1 : r < 1 := hr1
  set t : ℂ := (r : ℂ) * exp (θ * I)
  have hnt : ‖t‖ = r := by
    simp only [t]; rw [norm_mul, norm_real, Real.norm_of_nonneg hr.le, norm_exp_ofReal_mul_I,
      mul_one]
  have hsum : ∑ n ∈ Finset.range N, (t ^ ((n : ℂ) + ((m : ℂ) + 1) - 1)) • scorerAsym_coeff n =
      t ^ m * ∑ n ∈ Finset.range N, t ^ n * scorerAsym_coeff n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (n : ℂ) + ((m : ℂ) + 1) - 1 = ((n + m : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
      smul_eq_mul, pow_add]
    ring
  rw [hsum, hM.2, ← mul_sub]
  have hb := Complex.norm_exp_sub_sum_le_norm_mul_exp (-(t ^ 3 / 3)) M
  have hn : ‖-(t ^ 3 / 3)‖ = r ^ 3 / 3 := by
    rw [norm_neg, norm_div, norm_pow, hnt]; simp
  rw [hn] at hb
  simp only [add_re, natCast_re, one_re]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hr.le _),
    show (N : ℝ) + ((m : ℝ) + 1) - 1 = ((N + m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, norm_mul,
    norm_pow, hnt]
  have h1 : (r ^ 3 / 3) ^ M ≤ r ^ N := by
    calc (r ^ 3 / 3) ^ M ≤ (r ^ 3) ^ M := by
          gcongr; linarith [pow_nonneg hr.le 3]
      _ = r ^ (3 * M) := by rw [← pow_mul]
      _ ≤ r ^ N := pow_le_pow_of_le_one hr.le hr1.le hM.1
  have h2 : Real.exp (r ^ 3 / 3) ≤ 3 := by
    have : r ^ 3 / 3 ≤ 1 := by nlinarith [pow_le_one₀ hr.le hr1.le (n := 3)]
    calc Real.exp (r ^ 3 / 3) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  calc r ^ m * ‖cexp (-(t ^ 3 / 3)) - ∑ k ∈ Finset.range M, (-(t ^ 3 / 3)) ^ k / (k.factorial : ℂ)‖
      ≤ r ^ m * ((r ^ 3 / 3) ^ M * Real.exp (r ^ 3 / 3)) := by gcongr
    _ ≤ r ^ m * (r ^ N * 3) := by gcongr
    _ = 3 * r ^ (N + m) := by ring


/-- Watson's expansion of `L_m(w) = ∫₀^∞ e^{-wt} t^m e^{-t³/3} dt` in the sector
`|arg w| ≤ α < 2π/3`, obtained from two rotated rays. -/
theorem scorerAsym_laplace_expansion (m : ℕ) {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 * π / 3) :
    HasAsymptoticExpansion (airySector α) (fun (n : ℕ) (w : ℂ) => w ^ (-((n : ℂ) + ((m : ℂ) + 1))))
      (fun n => Gamma ((n : ℂ) + ((m : ℂ) + 1)) • scorerAsym_coeff n) (scorerAsym_laplace m) := by
  have hπ := Real.pi_pos
  have hcov := le_sup_comap_rotate (α := α) (β := α / 4) (γ := 3 * α / 4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hcos : 0 < Real.cos (3 * α / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hrot : ∀ θ : ℝ, |θ| < π / 6 → HasAsymptoticExpansion
      (comap (fun w : ℂ => w * exp (θ * I)) (sectorAtTop (Real.cos (3 * α / 4))))
      (fun (n : ℕ) (w : ℂ) => w ^ (-((n : ℂ) + ((m : ℂ) + 1))))
      (fun n => Gamma ((n : ℂ) + ((m : ℂ) + 1)) • scorerAsym_coeff n) (scorerAsym_laplace m) := by
    intro θ hθ
    have hθ' : |θ| < π / 2 := by linarith
    have hμ : 0 < ((m : ℂ) + 1).re := by simp; positivity
    refine (hasAsymptoticExpansion_integral_cexp_smul_rotate_comap
      (F := fun t => t ^ m * cexp (-(t ^ 3 / 3))) (a := scorerAsym_coeff) (μ := (m : ℂ) + 1)
      (c := 0) hθ' hμ hcos (scorerAsym_integrableOn_rotate m 0 hθ)
      (scorerAsym_sub_sum_isBigO m θ)).congr' (Eventually.of_forall fun w => ?_)
    exact (scorerAsym_laplace_rotate m hθ w).symm
  have hb : |α / 4| < π / 6 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h1 := hrot (-(α / 4)) (by rwa [abs_neg])
  have h2 := hrot (α / 4) hb
  exact (h1.sup h2).mono hcov


theorem scorerAsym_sum_three {g : ℕ → ℂ} (h1 : ∀ k, g (3 * k + 1) = 0) (h2 : ∀ k, g (3 * k + 2) = 0)
    (N : ℕ) : ∑ n ∈ Finset.range (3 * N), g n = ∑ k ∈ Finset.range N, g (3 * k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, h1, h2]
    ring

/-- The expansion of `L_m(-z)` in powers of `1/z`, truncated after `N` nonzero terms, for
`-z` in the sector `|arg(-z)| ≤ α < 2π/3`. -/
theorem scorerAsym_laplace_neg_isBigO (m : ℕ) {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector α))
      (fun z => scorerAsym_laplace m (-z) - ∑ k ∈ Finset.range N,
        ((3 * k + m).factorial : ℂ) * ((-1 / 3 : ℂ) ^ k / (k.factorial : ℂ)) *
          ((-z) ^ (3 * k + m + 1))⁻¹)
      (fun z => ((z ^ (3 * N + m + 1))⁻¹)) := by
  have hE := (scorerAsym_laplace_expansion m hα0 hα (3 * N)).comp_tendsto
    (tendsto_comap : Tendsto (fun z : ℂ => -z) (comap (fun z : ℂ => -z) (airySector α))
      (airySector α))
  have hpow : ∀ (j : ℕ) (w : ℂ), w ^ (-((j : ℂ) + ((m : ℂ) + 1))) = (w ^ (j + m + 1))⁻¹ := by
    intro j w
    rw [show ((j : ℂ) + ((m : ℂ) + 1)) = ((j + m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
      cpow_natCast]
  refine (hE.congr' (Eventually.of_forall fun z => ?_) EventuallyEq.rfl).trans ?_
  · simp only [Function.comp_apply]
    congr 1
    rw [scorerAsym_sum_three (g := fun n => (-z) ^ (-((n : ℂ) + ((m : ℂ) + 1))) •
      (Gamma ((n : ℂ) + ((m : ℂ) + 1)) • scorerAsym_coeff n))]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hd : 3 ∣ 3 * k := dvd_mul_right 3 k
      have hk : 3 * k / 3 = k := by omega
      simp only [scorerAsym_coeff, hd, ite_true, hk, smul_eq_mul, hpow]
      rw [show ((3 * k : ℕ) : ℂ) + ((m : ℂ) + 1) = ((3 * k + m : ℕ) : ℂ) + 1 by push_cast; ring,
        Gamma_nat_eq_factorial]
      ring
    · intro k
      have : ¬ 3 ∣ 3 * k + 1 := by omega
      simp [scorerAsym_coeff, this]
    · intro k
      have : ¬ 3 ∣ 3 * k + 2 := by omega
      simp [scorerAsym_coeff, this]
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply]
    rw [hpow, one_mul, norm_inv, norm_inv, norm_pow, norm_pow, norm_neg]


theorem scorerAsym_eventually_ne_zero (α : ℝ) :
    ∀ᶠ z in comap (fun z : ℂ => -z) (airySector α), z ≠ 0 := by
  have h : ∀ᶠ w in airySector α, w ≠ 0 ∧ |arg w| ≤ α := mem_inf_of_right (mem_principal_self _)
  exact (tendsto_comap.eventually h).mono fun z hz => neg_ne_zero.mp hz.1

theorem scorerAsym_neg_one_pow (k j : ℕ) : (-1 : ℂ) ^ (3 * k + j) = (-1) ^ k * (-1) ^ j := by
  rw [pow_add, pow_mul]; norm_num

/-- `Hi(z) = -(πz)⁻¹ ∑_{k<N} (3k)!/(k!(3z³)^k) + O(z^{-3N-1})` for `|arg(-z)| ≤ α < 2π/3`. -/
theorem scorerAsym_scorerHi_isBigO {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector α))
      (fun z : ℂ => scorerHi z - -1 / (π * z ^ 1) *
        ∑ k ∈ Finset.range N, (((3 * k + 0).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => (z ^ (3 * N + 0 + 1))⁻¹) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (scorerAsym_laplace_neg_isBigO 0 hα0 hα N).const_mul_left (1 / π : ℂ)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [scorerAsym_eventually_ne_zero α] with z hz
  rw [← scorerAsym_scorerHi_eq, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [add_zero, pow_one]
    rw [neg_pow, scorerAsym_neg_one_pow k 1, mul_pow, ← pow_mul, div_pow, pow_succ z]
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp

/-- `Hi'(z) = (πz²)⁻¹ ∑_{k<N} (3k+1)!/(k!(3z³)^k) + O(z^{-3N-2})` for `|arg(-z)| ≤ α < 2π/3`. -/
theorem scorerAsym_scorerHiDeriv_isBigO {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector α))
      (fun z : ℂ => scorerHiDeriv z - 1 / (π * z ^ 2) *
        ∑ k ∈ Finset.range N, (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => (z ^ (3 * N + 1 + 1))⁻¹) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (scorerAsym_laplace_neg_isBigO 1 hα0 hα N).const_mul_left (1 / π : ℂ)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [scorerAsym_eventually_ne_zero α] with z hz
  rw [← scorerAsym_scorerHiDeriv_eq, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [show 3 * k + 1 + 1 = 3 * k + 2 by ring, neg_pow, scorerAsym_neg_one_pow k 2, mul_pow,
      ← pow_mul, div_pow, pow_add z (3 * k) 2]
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp

theorem scorerAsym_arg_mul_exp {z : ℂ} (hz : z ≠ 0) {c : ℝ} (h1 : -π < arg z + c)
    (h2 : arg z + c ≤ π) : arg (z * exp (c * I)) = arg z + c := by
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [mul_assoc, ← Complex.exp_add, show (arg z : ℂ) * I + c * I = ((arg z + c : ℝ) : ℂ) * I by
    push_cast; ring, exp_mul_I]
  exact arg_mul_cos_add_sin_mul_I (norm_pos_iff.mpr hz) ⟨h1, h2⟩

/-- Rotation by `c` maps the sector `|arg z| ≤ α` into `|arg z| ≤ β` when `|c| + α ≤ β < π`. -/
theorem scorerAsym_tendsto_rotate {α β c : ℝ} (hc : |c| + α ≤ β) (hβ : β < π) :
    Tendsto (fun z : ℂ => z * exp (c * I)) (airySector α) (airySector β) := by
  exact airyRot_tendsto_rotate hc hβ

theorem scorerAsym_tendsto_omega {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) :
    Tendsto (fun z : ℂ => z * exp (-2 * π * I / 3)) (airySector (π / 3 - δ))
        (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ))) ∧
      Tendsto (fun z : ℂ => z * exp (2 * π * I / 3)) (airySector (π / 3 - δ))
        (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ))) := by
  have hπ := Real.pi_pos
  have e1 : ∀ z : ℂ, -(z * exp (-2 * π * I / 3)) = z * exp (((π / 3 : ℝ) : ℂ) * I) := fun z => by
    rw [show (-2 * π * I / 3 : ℂ) = ((π / 3 : ℝ) : ℂ) * I - π * I by push_cast; ring,
      Complex.exp_sub, exp_pi_mul_I]; field_simp
  have e2 : ∀ z : ℂ, -(z * exp (2 * π * I / 3)) = z * exp (((-(π / 3)) : ℝ) * I) := fun z => by
    rw [show (2 * π * I / 3 : ℂ) = ((-(π / 3)) : ℝ) * I + π * I by push_cast; ring,
      Complex.exp_add, exp_pi_mul_I]; ring
  constructor
  · refine tendsto_comap_iff.mpr ?_
    have := scorerAsym_tendsto_rotate (α := π / 3 - δ) (β := 2 * π / 3 - δ) (c := π / 3)
      (by rw [abs_of_pos (by positivity)]; linarith) (by linarith)
    exact this.congr fun z => (e1 z).symm
  · refine tendsto_comap_iff.mpr ?_
    have := scorerAsym_tendsto_rotate (α := π / 3 - δ) (β := 2 * π / 3 - δ) (c := -(π / 3))
      (by rw [abs_neg, abs_of_pos (by positivity)]; linarith) (by linarith)
    exact this.congr fun z => (e2 z).symm

/-- The derivative of the rotation formula 9.12.12. -/
theorem scorerAsym_scorerGiDeriv_rotations (z : ℂ) :
    scorerGiDeriv z = exp (π * I / 3) / 2 * (scorerHiDeriv (z * exp (-2 * π * I / 3)) *
        exp (-2 * π * I / 3)) +
      exp (-π * I / 3) / 2 * (scorerHiDeriv (z * exp (2 * π * I / 3)) * exp (2 * π * I / 3)) := by
  have hfun : scorerGi = fun z => exp (π * I / 3) / 2 * scorerHi (z * exp (-2 * π * I / 3)) +
      exp (-π * I / 3) / 2 * scorerHi (z * exp (2 * π * I / 3)) := funext scorerGi_rotations
  have h1 := (hasDerivAt_scorerHi (z * exp (-2 * π * I / 3))).comp z
    ((hasDerivAt_id z).mul_const (exp (-2 * π * I / 3)))
  have h2 := (hasDerivAt_scorerHi (z * exp (2 * π * I / 3))).comp z
    ((hasDerivAt_id z).mul_const (exp (2 * π * I / 3)))
  have h := (h1.const_mul (exp (π * I / 3) / 2)).add (h2.const_mul (exp (-π * I / 3) / 2))
  rw [scorerGiDeriv, hfun]
  refine h.deriv.trans ?_
  simp

theorem scorerAsym_norm_omega : ‖exp (-2 * π * I / 3)‖ = 1 ∧ ‖exp (2 * π * I / 3)‖ = 1 := by
  constructor
  · rw [show (-2 * π * I / 3 : ℂ) = ((-2 * π / 3 : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]
  · rw [show (2 * π * I / 3 : ℂ) = ((2 * π / 3 : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]

theorem scorerAsym_omega_cube : exp (-2 * π * I / 3) ^ 3 = 1 ∧ exp (2 * π * I / 3) ^ 3 = 1 := by
  constructor
  · rw [show (-2 * π * I / 3 : ℂ) = -(2 * π * I / 3) by ring]; exact omega_recip_cube
  · exact omega_cube

/-- Composite bound: `((z c)^n)⁻¹ = O((z^n)⁻¹)` when `‖c‖ = 1`. -/
theorem scorerAsym_isBigO_recip_pow_mul {l : Filter ℂ} {c : ℂ} (hc : ‖c‖ = 1) (n : ℕ) :
    (fun z : ℂ => ((z * c) ^ n)⁻¹) =O[l] (fun z : ℂ => (z ^ n)⁻¹) :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [one_mul, norm_inv, norm_inv, norm_pow, norm_pow, norm_mul, hc, mul_one])


theorem scorerAsym_rot_coeffs :
    exp (π * I / 3) / 2 = -exp (-2 * π * I / 3) / 2 ∧ exp (-π * I / 3) / 2 = -exp (2 * π * I / 3) / 2 := by
  constructor
  · rw [show (-2 * π * I / 3 : ℂ) = π * I / 3 - π * I by ring, Complex.exp_sub, exp_pi_mul_I]
    ring
  · rw [show (2 * π * I / 3 : ℂ) = -π * I / 3 + π * I by ring, Complex.exp_add, exp_pi_mul_I]
    ring

/-- scorerGi asymptotic (DLMF 9.12.25). -/
@[dlmf 9.12.E25]
theorem scorerGi_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => z) (airySector (π / 3 - δ)))
      (fun z : ℂ => scorerGi z - 1 / (π * z ^ 1) *
        ∑ k ∈ Finset.range N, (((3 * k + 0).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 1))) := by
  rw [comap_id']
  have hπ := Real.pi_pos
  obtain ⟨T1, T2⟩ := scorerAsym_tendsto_omega hδ hδ'
  obtain ⟨n1, n2⟩ := scorerAsym_norm_omega
  obtain ⟨c1, c2⟩ := scorerAsym_omega_cube
  obtain ⟨ha, hb⟩ := scorerAsym_rot_coeffs
  have H := scorerAsym_scorerHi_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith) N
  have h1 := ((H.comp_tendsto T1).trans (scorerAsym_isBigO_recip_pow_mul n1 _)).const_mul_left
    (exp (π * I / 3) / 2)
  have h2 := ((H.comp_tendsto T2).trans (scorerAsym_isBigO_recip_pow_mul n2 _)).const_mul_left
    (exp (-π * I / 3) / 2)
  have hev : ∀ᶠ z in airySector (π / 3 - δ), z ≠ 0 ∧ |arg z| ≤ π / 3 - δ :=
    mem_inf_of_right (mem_principal_self _)
  refine (h1.add h2).congr' ?_ (Eventually.of_forall fun z => ?_)
  · filter_upwards [hev] with z hz
    have hz0 := hz.1
    set S : ℂ → ℂ := fun w => ∑ k ∈ Finset.range N,
      (((3 * k + 0).factorial : ℂ) / k.factorial) / (3 * w ^ 3) ^ k with hSdef
    have hS : ∀ c : ℂ, c ^ 3 = 1 → S (z * c) = S z := fun c hc => by
      simp only [hSdef, mul_pow, hc, mul_one]
    simp only [Function.comp_apply]
    change exp (π * I / 3) / 2 * (scorerHi (z * exp (-2 * π * I / 3)) -
        -1 / (π * (z * exp (-2 * π * I / 3)) ^ 1) * S (z * exp (-2 * π * I / 3))) +
      exp (-π * I / 3) / 2 * (scorerHi (z * exp (2 * π * I / 3)) -
        -1 / (π * (z * exp (2 * π * I / 3)) ^ 1) * S (z * exp (2 * π * I / 3))) =
      scorerGi z - 1 / (π * z ^ 1) * S z
    rw [hS _ c1, hS _ c2, scorerGi_rotations, ha, hb]
    have e1 : exp (-2 * π * I / 3) ≠ 0 := exp_ne_zero _
    have e2 : exp (2 * π * I / 3) ≠ 0 := exp_ne_zero _
    have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  · simp only
    rw [show (3 * (N : ℂ) + 1) = ((3 * N + 0 + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
      cpow_natCast]

/-- scorerGiDeriv asymptotic (DLMF 9.12.26). -/
@[dlmf 9.12.E26]
theorem scorerGiDeriv_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => z) (airySector (π / 3 - δ)))
      (fun z : ℂ => scorerGiDeriv z - -1 / (π * z ^ 2) *
        ∑ k ∈ Finset.range N, (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 2))) := by
  rw [comap_id']
  have hπ := Real.pi_pos
  obtain ⟨T1, T2⟩ := scorerAsym_tendsto_omega hδ hδ'
  obtain ⟨n1, n2⟩ := scorerAsym_norm_omega
  obtain ⟨c1, c2⟩ := scorerAsym_omega_cube
  obtain ⟨ha, hb⟩ := scorerAsym_rot_coeffs
  have H := scorerAsym_scorerHiDeriv_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith) N
  have h1 := ((H.comp_tendsto T1).trans (scorerAsym_isBigO_recip_pow_mul n1 _)).const_mul_left
    (exp (π * I / 3) / 2 * exp (-2 * π * I / 3))
  have h2 := ((H.comp_tendsto T2).trans (scorerAsym_isBigO_recip_pow_mul n2 _)).const_mul_left
    (exp (-π * I / 3) / 2 * exp (2 * π * I / 3))
  have hev : ∀ᶠ z in airySector (π / 3 - δ), z ≠ 0 ∧ |arg z| ≤ π / 3 - δ :=
    mem_inf_of_right (mem_principal_self _)
  refine (h1.add h2).congr' ?_ (Eventually.of_forall fun z => ?_)
  · filter_upwards [hev] with z hz
    have hz0 := hz.1
    set S : ℂ → ℂ := fun w => ∑ k ∈ Finset.range N,
      (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * w ^ 3) ^ k with hSdef
    have hS : ∀ c : ℂ, c ^ 3 = 1 → S (z * c) = S z := fun c hc => by
      simp only [hSdef, mul_pow, hc, mul_one]
    simp only [Function.comp_apply]
    change exp (π * I / 3) / 2 * exp (-2 * π * I / 3) * (scorerHiDeriv (z * exp (-2 * π * I / 3)) -
        1 / (π * (z * exp (-2 * π * I / 3)) ^ 2) * S (z * exp (-2 * π * I / 3))) +
      exp (-π * I / 3) / 2 * exp (2 * π * I / 3) * (scorerHiDeriv (z * exp (2 * π * I / 3)) -
        1 / (π * (z * exp (2 * π * I / 3)) ^ 2) * S (z * exp (2 * π * I / 3))) =
      scorerGiDeriv z - -1 / (π * z ^ 2) * S z
    rw [hS _ c1, hS _ c2, scorerAsym_scorerGiDeriv_rotations, ha, hb]
    have e1 : exp (-2 * π * I / 3) ≠ 0 := exp_ne_zero _
    have e2 : exp (2 * π * I / 3) ≠ 0 := exp_ne_zero _
    have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  · simp only
    rw [show (3 * (N : ℂ) + 2) = ((3 * N + 1 + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
      cpow_natCast]

/-- scorerHi asymptotic (DLMF 9.12.27). -/
@[dlmf 9.12.E27]
theorem scorerHi_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ)))
      (fun z : ℂ => scorerHi z - -1 / (π * z ^ 1) *
        ∑ k ∈ Finset.range N, (((3 * k + 0).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 1))) := by
  refine (scorerAsym_scorerHi_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith) N).congr'
    EventuallyEq.rfl (Eventually.of_forall fun z => ?_)
  simp only
  rw [show (3 * (N : ℂ) + 1) = ((3 * N + 0 + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
    cpow_natCast]

/-- scorerHiDeriv asymptotic (DLMF 9.12.28). -/
@[dlmf 9.12.E28]
theorem scorerHiDeriv_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ)))
      (fun z : ℂ => scorerHiDeriv z - 1 / (π * z ^ 2) *
        ∑ k ∈ Finset.range N, (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 2))) := by
  refine (scorerAsym_scorerHiDeriv_isBigO (α := 2 * π / 3 - δ) (by linarith) (by linarith)
    N).congr' EventuallyEq.rfl (Eventually.of_forall fun z => ?_)
  simp only
  rw [show (3 * (N : ℂ) + 2) = ((3 * N + 1 + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg,
    cpow_natCast]

/-- All complex zeros are simple, DLMF §9.12(ix). -/
theorem scorerGi_simple_zeros {z : ℂ} (hz : scorerGi z = 0) :
    deriv scorerGi z ≠ 0 := by
  sorry

/-- All complex zeros are simple, DLMF §9.12(ix). -/
theorem scorerHi_simple_zeros {z : ℂ} (hz : scorerHi z = 0) :
    deriv scorerHi z ≠ 0 := by
  sorry

/-- On the real line the Laplace integral is real. -/
theorem integral_pow_mul_exp_cubic_ofReal (m : ℕ) (x : ℝ) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ m * exp (-(t : ℂ) ^ 3 / 3 + x * t) =
      ((∫ t : ℝ in Ioi 0, t ^ m * Real.exp (-(t ^ 3 / 3) + x * t) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  push_cast; rw [neg_div]

/-- The real Laplace integral is positive. -/
theorem integral_pow_mul_exp_cubic_pos (m : ℕ) (x : ℝ) :
    0 < ∫ t : ℝ in Ioi 0, t ^ m * Real.exp (-(t ^ 3 / 3) + x * t) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(t ^ 3 / 3) + x * t)) (Ioi 0) := by
    have := (integrableOn_pow_mul_exp_cubic m x).re
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    beta_reduce
    rw [RCLike.re_to_complex, show (-(t : ℂ) ^ 3 / 3 + (x : ℂ) * t) = ((-(t ^ 3 / 3) + x * t : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_exp, ← ofReal_pow, ← ofReal_mul, ofReal_re]
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hi]
  · rw [show Function.support (fun t : ℝ => t ^ m * Real.exp (-(t ^ 3 / 3) + x * t)) ∩ Ioi 0 =
        Ioi 0 by
      ext t
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
      constructor
      · exact fun h => h.2
      · intro ht; exact ⟨(mul_pos (pow_pos ht m) (Real.exp_pos _)).ne', ht⟩]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    exact (mul_pos (pow_pos ht m) (Real.exp_pos _)).le

/-- There are no real zeros, DLMF §9.12(ix). -/
theorem scorerHi_real_ne_zero (x : ℝ) :
    scorerHi x ≠ 0 := by
  rw [(scorerHi_exp_integral x).2]
  have h := integral_pow_mul_exp_cubic_ofReal 0 x
  simp only [pow_zero, one_mul] at h
  rw [h]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp := integral_pow_mul_exp_cubic_pos 0 x
  simp only [pow_zero, one_mul] at hp
  exact div_ne_zero (ofReal_ne_zero.mpr hp.ne') hpi

/-- There are no real zeros, DLMF §9.12(ix). -/
theorem scorerHiDeriv_real_ne_zero (x : ℝ) :
    scorerHiDeriv x ≠ 0 := by
  rw [scorerHiDeriv_exp_integral]
  have h := integral_pow_mul_exp_cubic_ofReal 1 x
  simp only [pow_one] at h
  rw [h]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp := integral_pow_mul_exp_cubic_pos 1 x
  simp only [pow_one] at hp
  exact div_ne_zero (ofReal_ne_zero.mpr hp.ne') hpi

/-! ### Real zeros of `Gi` and `Gi'`

The real restrictions satisfy `Gi'' = x Gi - 1/π`. Positivity on `[0, ∞)` follows from the
maximum principle (`ODE.sturmCount_neg_of_maxPrinciple`) and the asymptotics 9.12.25–26; on
the negative axis `Gi = Bi - Hi`, where `Hi(x) ≤ 1/(π|x|)` is dominated by the Airy modulus
`M(x)`, so `Gi` alternates in sign at the points where the Airy phase is a multiple of `π`.
-/

/-- `Gi` on the real axis. -/
def scorerZ_gi (x : ℝ) : ℝ := (scorerGi x).re
/-- `Gi'` on the real axis. -/
def scorerZ_gi' (x : ℝ) : ℝ := (scorerGiDeriv x).re
/-- `Hi` on the real axis, as a real Laplace integral. -/
def scorerZ_hi (x : ℝ) : ℝ := (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + x * t)) / π

theorem scorerZ_integrable (m : ℕ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(t ^ 3 / 3) + x * t)) (Ioi 0) := by
  have := (integrableOn_pow_mul_exp_cubic m x).re
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  beta_reduce
  rw [RCLike.re_to_complex, show (-(t : ℂ) ^ 3 / 3 + (x : ℂ) * t) =
      ((-(t ^ 3 / 3) + x * t : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_exp, ← ofReal_pow, ← ofReal_mul, ofReal_re]

theorem scorerZ_hi_eq (x : ℝ) : scorerHi x = (scorerZ_hi x : ℂ) := by
  rw [(scorerHi_exp_integral x).2]
  have h := integral_pow_mul_exp_cubic_ofReal 0 x
  simp only [pow_zero, one_mul] at h
  rw [h, scorerZ_hi]; push_cast; rfl

theorem scorerZ_hiDeriv_eq (x : ℝ) : scorerHiDeriv x =
    (((∫ t in Ioi (0 : ℝ), t ^ 1 * Real.exp (-(t ^ 3 / 3) + x * t)) / π : ℝ) : ℂ) := by
  rw [scorerHiDeriv_exp_integral]
  have h := integral_pow_mul_exp_cubic_ofReal 1 x
  simp only [pow_one] at h ⊢
  rw [h]; push_cast; rfl

theorem scorerZ_gi_ofReal (x : ℝ) : scorerGi x = (scorerZ_gi x : ℂ) := by
  have h : scorerGi x = ((airyBiReal x - scorerZ_hi x : ℝ) : ℂ) := by
    rw [scorerGi, airyBi_ofReal_eq, scorerZ_hi_eq]; push_cast; ring
  rw [scorerZ_gi, h, ofReal_re]

theorem scorerZ_gi_eq (x : ℝ) : scorerZ_gi x = airyBiReal x - scorerZ_hi x := by
  rw [scorerZ_gi, scorerGi, sub_re, scorerZ_hi_eq, ofReal_re]; rfl

theorem scorerZ_gi'_ofReal (x : ℝ) : scorerGiDeriv x = (scorerZ_gi' x : ℂ) := by
  have h : ∃ r : ℝ, scorerGiDeriv x = (r : ℂ) := by
    rw [scorerGiDeriv_eq, airyBiDeriv_ofReal_eq, scorerZ_hiDeriv_eq]
    exact ⟨airyBiDerivReal x - (∫ t in Ioi (0 : ℝ), t ^ 1 * Real.exp (-(t ^ 3 / 3) + x * t)) / π,
      by push_cast; ring⟩
  obtain ⟨r, hr⟩ := h
  rw [scorerZ_gi', hr, ofReal_re]

theorem scorerZ_hasDerivAt_gi (x : ℝ) : HasDerivAt scorerZ_gi (scorerZ_gi' x) x :=
  ((isAiryInhomSol_scorerGi x).1).real_of_complex

theorem scorerZ_hasDerivAt_gi' (x : ℝ) :
    HasDerivAt scorerZ_gi' (x * scorerZ_gi x - 1 / π) x := by
  have h : HasDerivAt scorerZ_gi' _ x := ((isAiryInhomSol_scorerGi x).2).real_of_complex
  refine h.congr_deriv ?_
  rw [scorerZ_gi_ofReal]
  simp only [add_re, re_ofReal_mul, neg_re, div_ofReal_re, one_re]
  rw [ofReal_re]; ring

theorem scorerZ_hasDerivAt_gi'' (x : ℝ) :
    HasDerivAt (fun t => t * scorerZ_gi t - 1 / π) (scorerZ_gi x + x * scorerZ_gi' x) x := by
  have := ((hasDerivAt_id x).mul (scorerZ_hasDerivAt_gi x)).sub_const (1 / π)
  convert this using 1 <;> simp

theorem scorerZ_continuous_gi : Continuous scorerZ_gi :=
  continuous_iff_continuousAt.mpr fun x => (scorerZ_hasDerivAt_gi x).continuousAt

theorem scorerZ_continuous_gi' : Continuous scorerZ_gi' :=
  continuous_iff_continuousAt.mpr fun x => (scorerZ_hasDerivAt_gi' x).continuousAt

theorem scorerZ_gi_zero_pos : 0 < scorerZ_gi 0 := by
  rw [scorerZ_gi, ofReal_zero, scorer_zero.2.1, div_ofNat_re]
  exact div_pos (airyBiReal_pos le_rfl) (by norm_num)

theorem scorerZ_gi'_zero_pos : 0 < scorerZ_gi' 0 := by
  rw [scorerZ_gi', ofReal_zero, scorerDeriv_zero.2.1, div_ofNat_re]
  exact div_pos airyBiDerivReal_zero_pos (by norm_num)


/-- Real form of a sector bound: `‖F x‖ ≤ C x^{-p}` eventually along the positive axis. -/
theorem scorerZ_real_bound {F : ℂ → ℂ} {p : ℂ}
    (h : IsBigO (comap (fun z : ℂ => z) (airySector (π / 3 - π / 6))) F (fun z => z ^ p)) :
    ∃ C, ∀ᶠ x : ℝ in atTop, ‖F x‖ ≤ C * x ^ p.re := by
  rw [comap_id'] at h
  obtain ⟨C, hC⟩ := (h.comp_tendsto (airyInt_tendsto_ofReal_sector (by
    linarith [Real.pi_pos]))).bound
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop 0] with x hx hx0
  simpa [Function.comp, Complex.norm_cpow_eq_rpow_re_of_pos hx0] using hx

theorem scorerZ_gi_eventually_pos : ∀ᶠ x in atTop, 0 < scorerZ_gi x := by
  have hπ := Real.pi_pos
  obtain ⟨C, hC⟩ := scorerZ_real_bound (scorerGi_asymptotic (δ := π / 6)
    (by positivity) (by linarith) 1)
  filter_upwards [hC, eventually_gt_atTop (max 1 (C * π))] with x hx hxM
  have hx1 : 1 < x := (le_max_left _ _).trans_lt hxM
  have hxC : C * π < x := (le_max_right _ _).trans_lt hxM
  have hx0 : 0 < x := by linarith
  simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
    mul_one, mul_zero, zero_add, pow_one] at hx
  rw [scorerZ_gi_ofReal, show (1 : ℂ) / (π * (x : ℂ)) = ((1 / (π * x) : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_sub, norm_real, Real.norm_eq_abs] at hx
  have hre : (-(3 + 1 : ℂ)).re = -4 := by norm_num
  rw [hre, Real.rpow_neg hx0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    at hx
  have h1 := (abs_le.mp hx).1
  have hx4 : 0 < x ^ 4 := by positivity
  have key : C * (x ^ 4)⁻¹ < 1 / (π * x) := by
    rw [← div_eq_mul_inv, div_lt_div_iff₀ hx4 (by positivity)]
    have : x ≤ x ^ 3 := le_self_pow₀ hx1.le (by norm_num)
    nlinarith
  linarith

theorem scorerZ_gi'_eventually_neg : ∀ᶠ x in atTop, scorerZ_gi' x < 0 := by
  have hπ := Real.pi_pos
  obtain ⟨C, hC⟩ := scorerZ_real_bound (scorerGiDeriv_asymptotic (δ := π / 6)
    (by positivity) (by linarith) 1)
  filter_upwards [hC, eventually_gt_atTop (max 1 (C * π))] with x hx hxM
  have hx1 : 1 < x := (le_max_left _ _).trans_lt hxM
  have hxC : C * π < x := (le_max_right _ _).trans_lt hxM
  have hx0 : 0 < x := by linarith
  simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
    mul_one, mul_zero, zero_add, Nat.factorial_one] at hx
  rw [scorerZ_gi'_ofReal, show (-1 : ℂ) / (π * (x : ℂ) ^ 2) = ((-1 / (π * x ^ 2) : ℝ) : ℂ) by
      push_cast; ring, ← ofReal_sub, norm_real, Real.norm_eq_abs] at hx
  have hre : (-(3 + 2 : ℂ)).re = -5 := by norm_num
  rw [hre, Real.rpow_neg hx0.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    at hx
  have h1 := (abs_le.mp hx).2
  have hx5 : 0 < x ^ 5 := by positivity
  have key : C * (x ^ 5)⁻¹ < 1 / (π * x ^ 2) := by
    rw [← div_eq_mul_inv, div_lt_div_iff₀ hx5 (by positivity)]
    have : x ≤ x ^ 3 := le_self_pow₀ hx1.le (by norm_num)
    nlinarith [pow_pos hx0 2]
  have : -1 / (π * x ^ 2) = -(1 / (π * x ^ 2)) := by ring
  linarith

/-- `Gi(x) > 0` for `x ≥ 0`. -/
theorem scorerZ_gi_pos {x : ℝ} (hx : 0 ≤ x) : 0 < scorerZ_gi x := by
  obtain ⟨X, hX, hXx⟩ := (scorerZ_gi_eventually_pos.and (eventually_gt_atTop x)).exists
  have hπ := Real.pi_pos
  have := ODE.sturmCount_neg_of_maxPrinciple (g := fun t => -scorerZ_gi t)
    (g' := fun t => -scorerZ_gi' t) (g'' := fun t => -(t * scorerZ_gi t - 1 / π)) (a := 0) (b := X)
    scorerZ_continuous_gi.neg.continuousOn (fun t _ => (scorerZ_hasDerivAt_gi t).neg)
    (fun t _ => (scorerZ_hasDerivAt_gi' t).neg) (by simpa using scorerZ_gi_zero_pos)
    (by simpa using hX) (fun t ht h0 _ => by
      have : t * scorerZ_gi t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1.le (by linarith)
      have : 0 < 1 / π := by positivity
      linarith) x ⟨hx, hXx.le⟩
  linarith

/-- `Gi'` has at most one zero on `[0, ∞)`. -/
theorem scorerZ_gi'_zero_unique {y₁ y₂ : ℝ} (h₁ : 0 ≤ y₁) (hlt : y₁ < y₂) (e₁ : scorerZ_gi' y₁ = 0)
    (e₂ : scorerZ_gi' y₂ = 0) : False := by
  obtain ⟨X, hX, hXx⟩ := (scorerZ_gi'_eventually_neg.and (eventually_gt_atTop y₂)).exists
  have hle := ODE.sturmCount_nonpos_of_maxPrinciple (g := scorerZ_gi')
    (g' := fun t => t * scorerZ_gi t - 1 / π) (g'' := fun t => scorerZ_gi t + t * scorerZ_gi' t)
    (a := y₁) (b := X) scorerZ_continuous_gi'.continuousOn
    (fun t _ => scorerZ_hasDerivAt_gi' t) (fun t _ => scorerZ_hasDerivAt_gi'' t) e₁.le hX.le
    (fun t ht hpos _ => by
      have h0 : 0 < t := lt_of_le_of_lt h₁ ht.1
      have := scorerZ_gi_pos h0.le
      positivity)
  have hloc : IsLocalMax scorerZ_gi' y₂ := by
    filter_upwards [Icc_mem_nhds hlt hXx] with t ht
    rw [e₂]; exact hle t ht
  have hd0 := hloc.hasDerivAt_eq_zero (scorerZ_hasDerivAt_gi' y₂)
  refine ODE.sturmCount_not_isLocalMax (Eventually.of_forall fun t => scorerZ_hasDerivAt_gi' t)
    (scorerZ_hasDerivAt_gi'' y₂) hd0 ?_ hloc
  rw [e₂, mul_zero, add_zero]
  exact scorerZ_gi_pos (h₁.trans hlt.le)



/-- `0 < Hi(x) ≤ 1/(π|x|)` for `x < 0`. -/
theorem scorerZ_hi_le {x : ℝ} (hx : x < 0) : scorerZ_hi x ≤ 1 / (π * (-x)) := by
  have hπ := Real.pi_pos
  have hI : ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + x * t) ≤ 1 / (-x) := by
    calc ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + x * t)
        ≤ ∫ t in Ioi (0 : ℝ), Real.exp (x * t) := by
          refine setIntegral_mono_on (by simpa using scorerZ_integrable 0 x)
            (integrableOn_exp_mul_Ioi hx 0) measurableSet_Ioi fun t ht => ?_
          have ht : (0 : ℝ) < t := ht
          exact Real.exp_le_exp.mpr (by nlinarith [pow_pos ht 3])
      _ = 1 / (-x) := by rw [integral_exp_mul_Ioi hx 0]; simp; field_simp
  rw [scorerZ_hi, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right hI hπ.le

/-- The Airy modulus beats the Hi bound: `1/(π|x|) < M(x)` for `x ≤ -1`. -/
theorem scorerZ_modulus_gt {x : ℝ} (hx : x ≤ -1) : 1 / (π * (-x)) < airyModulus x := by
  have hπ := Real.pi_pos
  set s := -x with hs
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  obtain ⟨hb, -⟩ := airyMod_modulus_bounds hs0
  rw [hs, neg_neg] at hb
  set r := s ^ (1 / 2 : ℝ)
  have hr2 : r ^ 2 = s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]; norm_num
  have hr1 : 1 ≤ r := Real.one_le_rpow hs1 (by norm_num)
  have hrs : r ≤ s := by nlinarith
  have hM := airyModulus_pos x
  have h3 : (s ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hs1)
  have hb' : 27 / 32 ≤ π * r * airyModulus x ^ 2 := by linarith
  rw [div_lt_iff₀ (by positivity)]
  -- `(π s M)² ≥ π s · 27/32 > 1`
  have hsq : 1 < (airyModulus x * (π * s)) ^ 2 := by
    have : (airyModulus x * (π * s)) ^ 2 = (π * r * airyModulus x ^ 2) * (π * s * r) := by
      have e : s ^ 2 = s * r ^ 2 := by rw [hr2]; ring
      linear_combination (airyModulus x ^ 2 * π ^ 2) * e
    rw [this]
    have hsr : 1 ≤ s * r := one_le_mul_of_one_le_of_one_le hs1 hr1
    have h1 : 3 ≤ π * s * r := by nlinarith [Real.pi_gt_three]
    nlinarith
  nlinarith [sq_nonneg (airyModulus x * (π * s) - 1), mul_pos hM (mul_pos hπ hs0)]

/-- `Gi` takes both signs arbitrarily far to the left. -/
theorem scorerZ_gi_signs (M : ℝ) (σ : ℝ) (hσ : σ = 0 ∨ σ = π) :
    ∃ x < M, x ≤ -1 ∧ Real.cos (airyPhase x) = Real.cos σ := by
  have hπ := Real.pi_pos
  set A := min M (-1) - 1
  obtain ⟨m, hm⟩ := exists_nat_gt (airyPhase A / (2 * π))
  have hmA : airyPhase A < m * (2 * π) := by
    rwa [div_lt_iff₀ (by positivity)] at hm
  obtain ⟨y, hy, hyA⟩ := ((tendsto_airyPhase_atBot.eventually
    (eventually_ge_atTop (m * (2 * π) + π))).and (eventually_lt_atBot A)).exists
  have hσ0 : 0 ≤ σ ∧ σ ≤ π := by rcases hσ with rfl | rfl <;> constructor <;> linarith
  obtain ⟨x, hx, hxθ⟩ := intermediate_value_Icc' hyA.le airyPhase_continuous.continuousOn
    (show m * (2 * π) + σ ∈ Icc (airyPhase A) (airyPhase y) from
      ⟨by linarith, by linarith⟩)
  refine ⟨x, ?_, ?_, ?_⟩
  · have : A < M := by simp only [A]; linarith [min_le_left M (-1)]
    linarith [hx.2]
  · have : A ≤ -2 := by simp only [A]; linarith [min_le_right M (-1)]
    linarith [hx.2]
  · rw [hxθ, add_comm, Real.cos_add_nat_mul_two_pi]

theorem scorerZ_gi_frequently (M : ℝ) :
    (∃ x < M, 0 < scorerZ_gi x) ∧ ∃ x < M, scorerZ_gi x < 0 := by
  have hπ := Real.pi_pos
  constructor
  · obtain ⟨x, hxM, hx1, hc⟩ := scorerZ_gi_signs M 0 (Or.inl rfl)
    refine ⟨x, hxM, ?_⟩
    rw [scorerZ_gi_eq, airyBiReal_eq_modulus_cos, hc, Real.cos_zero, mul_one]
    linarith [scorerZ_hi_le (show x < 0 by linarith), scorerZ_modulus_gt hx1]
  · obtain ⟨x, hxM, hx1, hc⟩ := scorerZ_gi_signs M π (Or.inr rfl)
    refine ⟨x, hxM, ?_⟩
    rw [scorerZ_gi_eq, airyBiReal_eq_modulus_cos, hc, Real.cos_pi, mul_neg_one]
    have : 0 < scorerZ_hi x := by
      rw [scorerZ_hi]
      exact div_pos (by simpa using integral_pow_mul_exp_cubic_pos 0 x) hπ
    linarith [airyModulus_pos x]

theorem scorerZ_gi_zeros_infinite : {x : ℝ | x < 0 ∧ scorerZ_gi x = 0}.Infinite :=
  ODE.sturmCount_infinite_zeros_atBot scorerZ_continuous_gi.continuousOn
    (fun M => (scorerZ_gi_frequently M).1) (fun M => (scorerZ_gi_frequently M).2)

/-- Gi has no nonnegative real zeros, DLMF §9.12(ix). -/
theorem scorerGi_nonneg_ne_zero {x : ℝ} (hx : 0 ≤ x) :
    scorerGi x ≠ 0 := by
  rw [scorerZ_gi_ofReal, ofReal_ne_zero]
  exact (scorerZ_gi_pos hx).ne'

/-- Gi' has exactly one nonnegative real zero, DLMF §9.12(ix). -/
theorem scorerGiDeriv_unique_nonneg_zero  :
    ∃! x : ℝ, 0 ≤ x ∧ scorerGiDeriv x = 0 := by
  obtain ⟨X, hX, hX0⟩ := (scorerZ_gi'_eventually_neg.and (eventually_gt_atTop 0)).exists
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hX0.le scorerZ_continuous_gi'.continuousOn
    ⟨hX.le, scorerZ_gi'_zero_pos.le⟩
  refine ⟨x, ⟨hx.1, by rw [scorerZ_gi'_ofReal, hx0, ofReal_zero]⟩, fun y ⟨hy, hy0⟩ => ?_⟩
  rw [scorerZ_gi'_ofReal, ofReal_eq_zero] at hy0
  rcases lt_trichotomy y x with h | h | h
  · exact (scorerZ_gi'_zero_unique hy h hy0 hx0).elim
  · exact h
  · exact (scorerZ_gi'_zero_unique hx.1 h hx0 hy0).elim

/-- Infinitely many negative real zeros, DLMF §9.12(ix). -/
theorem scorerGi_infinite_negative_zeros  :
    Set.Infinite {x : ℝ | x < 0 ∧ scorerGi x = 0} := by
  convert scorerZ_gi_zeros_infinite using 3 with x
  rw [scorerZ_gi_ofReal, ofReal_eq_zero]

/-- Infinitely many negative real zeros, DLMF §9.12(ix). -/
theorem scorerGiDeriv_infinite_negative_zeros  :
    Set.Infinite {x : ℝ | x < 0 ∧ scorerGiDeriv x = 0} := by
  have h := ODE.sturmCount_infinite_deriv_zeros (s := Iio 0) ordConnected_Iio
    (fun x _ => scorerZ_hasDerivAt_gi x) scorerZ_gi_zeros_infinite
  convert h using 3 with x
  rw [scorerZ_gi'_ofReal, ofReal_eq_zero]; rfl

/-- Negative zeros of Gi and Gi' interlace, DLMF §9.12(ix). -/
theorem scorerGi_zeros_interlace {a b : ℝ} (hab : a < b) (hb : b < 0)
    (ha0 : scorerGi a = 0) (hb0 : scorerGi b = 0)
    (hgap : ∀ x ∈ Ioo a b, scorerGi x ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ scorerGiDeriv x = 0 := by
  sorry

/-- The reverse interlacing of the two negative real Scorer zero families. -/
theorem scorerGiDeriv_zeros_interlace {a b : ℝ} (hab : a < b) (hb : b < 0)
    (ha0 : scorerGiDeriv a = 0) (hb0 : scorerGiDeriv b = 0)
    (hgap : ∀ x ∈ Ioo a b, scorerGiDeriv x ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ scorerGi x = 0 := by
  sorry

/-- Convergence of the symmetric principal value in DLMF 9.12.23. -/
@[dlmf 9.12.E23]
theorem scorerGi_principalValue_converges {x : ℝ} (hx : 0 < x) :
    let f := fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t /
      ((airyZeta x : ℂ) ^ 2 - (t : ℂ) ^ 2)
    HasPrincipalValueIoi f (airyZeta x) (principalValueIoi f (airyZeta x)) := by
  sorry

end DLMF.Airy
