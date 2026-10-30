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
# Series and integral representations of Scorer functions

Series, differential equations, connection formulas and integral representations of the
inhomogeneous Airy functions.

Source references and common attribution are retained in
`DLMF.Airy.Scorer`.
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

/-- Every complex number lies in the ball of infinite radius about `0`. -/
theorem mem_eball_top (z : ℂ) : z ∈ Metric.eball (0 : ℂ) ⊤ := by simp
/-- Hi is entire. -/
theorem differentiable_scorerHi : Differentiable ℂ scorerHi := fun z =>
  (hasFPowerSeriesOnBall_scorerHi.analyticAt_of_mem (mem_eball_top z)).differentiableAt

/-- The second Maclaurin coefficient of `Hi` is `1/(2π)`. -/
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

/-- Gi is entire, DLMF §9.12(i). -/
theorem scorerGi_entire  :
    Differentiable ℂ scorerGi := by
  exact differentiable_airyBi.sub differentiable_scorerHi

/-- `Hi` solves the inhomogeneous Airy equation `w'' = z w + 1/π` (DLMF 9.12.1). -/
@[dlmf 9.12.E1]
theorem scorerHi_ode  :
    IsScorerSol scorerHi scorerHiDeriv := by
  exact fun z =>
    ⟨hasDerivAt_scorerHi z, hasDerivAt_scorerHiDeriv z⟩

/-- `-Gi` solves `w'' = z w + 1/π`, that is, `Gi'' = z Gi - 1/π` (DLMF 9.12.3). -/
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

/-- For `ε = ±1`, `e^{-2πiε/3} Hi(z e^{-2πiε/3})` solves `w'' = z w + 1/π` (DLMF 9.12.3). -/
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

/-- Every solution of `w'' = z w + 1/π` is a particular solution plus a combination of two
independent Airy solutions (DLMF 9.12.2). -/
@[dlmf 9.12.E2]
theorem scorer_general_solution {w w' p p' f f' g g' : ℂ → ℂ} (hw : IsScorerSol w w')
    (hp : IsScorerSol p p')
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

/-- `Gi(0) = Hi(0)/2 = Bi(0)/3 = 1/(3^{7/6} Γ(2/3))` (DLMF 9.12.6). -/
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

/-- `Gi'(0) = Hi'(0)/2 = Bi'(0)/3 = 1/(3^{5/6} Γ(1/3))` (DLMF 9.12.7). -/
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

/-- A solution of the Airy equation solves the inhomogeneous equation with forcing `0`. -/
theorem IsAiryInhomSol.of_airy {w w' : ℂ → ℂ} (h : IsAirySol w w') : IsAiryInhomSol 0 w w' :=
  fun z => ⟨(h z).1, (h z).2.congr_deriv (by ring)⟩

/-- The sum of solutions with forcings `c` and `d` solves the equation with forcing `c + d`. -/
theorem IsAiryInhomSol.add {c d : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsAiryInhomSol c f f')
    (hg : IsAiryInhomSol d g g') :
    IsAiryInhomSol (c + d) (fun z => f z + g z) (fun z => f' z + g' z) := fun z =>
  ⟨(hf z).1.add (hg z).1, ((hf z).2.add (hg z).2).congr_deriv (by ring)⟩

/-- Multiplying a solution with forcing `c` by `a` gives a solution with forcing `a c`. -/
theorem IsAiryInhomSol.const_mul {c : ℂ} (a : ℂ) {f f' : ℂ → ℂ} (hf : IsAiryInhomSol c f f') :
    IsAiryInhomSol (a * c) (fun z => a * f z) (fun z => a * f' z) := fun z =>
  ⟨(hf z).1.const_mul a, ((hf z).2.const_mul a).congr_deriv (by ring)⟩

/-- The forcing constant of an inhomogeneous Airy solution may be rewritten by an equality. -/
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

/-- For a cube root of unity `ν`, `t ↦ Ai(t ν)` (with derivative `ν Ai'(t ν)`) solves the Airy
equation. -/
theorem isAirySol_airyAi_mul {ν : ℂ} (hν : ν ^ 3 = 1) :
    IsAirySol (fun t => airyAi (t * ν)) (fun t => ν * airyAiDeriv (t * ν)) := by
  have h := isAirySol_rotated hν
  simp only [mul_comm _ ν]
  exact h

/-- The segment primitive of an entire function differentiates to it. -/
theorem hasDerivAt_primitive {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasDerivAt (primitive f) (f z) z := by
  have he : primitive f = fun w : ℂ => w * ∫ t : ℝ in 0..1, f (t * w) := by
    funext w; simp [primitive, segmentIntegral]
  rw [he]; exact Complex.hasDerivAt_mul_integral_comp_mul hf z

/-- The primitive `∫₀^z f` vanishes at `z = 0`. -/
theorem primitive_zero (f : ℂ → ℂ) : primitive f 0 = 0 := by simp [primitive, segmentIntegral]

/-- `Bi(0) = √3 Ai(0)`. -/
theorem airyBi_zero_eq : airyBi 0 = (Real.sqrt 3 : ℂ) * airyAi 0 := by
  simp only [airyBi, airyAi, airyG_zero, mul_zero, add_zero, sub_zero]

/-- `Bi'(0) = -√3 Ai'(0)`. -/
theorem airyBiDeriv_zero_eq : airyBiDeriv 0 = -(Real.sqrt 3 : ℂ) * airyAiDeriv 0 := by
  simp only [airyBiDeriv, airyAiDeriv, airyFDeriv_zero, mul_zero, zero_add, zero_sub]
  ring

/-- `e^{-2πi/3} = -1/2 - (√3/2) i`, with the exponent written as `-2πi/3`. -/
theorem exp_neg_two_pi_I_div_three' :
    exp (-2 * π * I / 3) = -1 / 2 - (Real.sqrt 3 / 2 : ℝ) * I := by
  rw [show (-2 * π * I / 3 : ℂ) = -(2 * π * I / 3) by ring, exp_neg_two_pi_I_div_three]

/-- `e^{-πi/3} = 1/2 - (√3/2) i`, with the exponent written as `-πi/3`. -/
theorem exp_neg_pi_I_div_three' : exp (-π * I / 3) = (1 / 2 : ℂ) - (Real.sqrt 3 / 2 : ℝ) * I := by
  rw [show (-π * I / 3 : ℂ) = -(π * I / 3) by ring, exp_neg_pi_I_div_three]

/-- `Hi(0) = (2/√3) Ai(0)`, written as `(2√3/3) Ai(0)`. -/
theorem scorerHi_zero_eq : scorerHi 0 = 2 * (Real.sqrt 3 : ℂ) / 3 * airyAi 0 := by
  have h1 := scorer_zero.1
  have h2 := scorer_zero.2.1
  rw [airyBi_zero_eq] at h2
  linear_combination -2 * h1 + 2 * h2

/-- `Hi'(0) = -(2/√3) Ai'(0)`, written as `-(2√3/3) Ai'(0)`. -/
theorem scorerHiDeriv_zero_eq : scorerHiDeriv 0 = -(2 * (Real.sqrt 3 : ℂ) / 3) * airyAiDeriv 0 := by
  have h1 := scorerDeriv_zero.1
  have h2 := scorerDeriv_zero.2.1
  rw [airyBiDeriv_zero_eq] at h2
  linear_combination -2 * h1 + 2 * h2

/-- `√3 ^ 4 = 9` in `ℂ`, for the `sqrt3_ring` normalization. -/
private lemma sqrt_three_pow_four : ((Real.sqrt 3 : ℝ) : ℂ) ^ 4 = 9 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, sqrt_three_sq]; norm_num

/-- Normalize polynomial identities in `√3` and `i`. -/
macro "sqrt3_ring" : tactic =>
  `(tactic| (ring_nf; simp only [sqrt_three_sq, sqrt_three_pow_three_complex,
    sqrt_three_pow_four, I_sq, I_pow_three]; ring_nf))

/-- For `ε = ±1`, the values of `e^{±2πiε/3}`, `e^{-πiε/3}` and `e^{-πiε/6}` in Cartesian form. -/
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

/-- Variation of parameters: `Gi(z) = Bi(z) (1/3 - ∫₀^z Ai) + Ai(z) ∫₀^z Bi` (DLMF 9.12.4). -/
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

/-- Variation of parameters: `Hi(z) = Bi(z) (2/3 + ∫₀^z Ai) - Ai(z) ∫₀^z Bi` (DLMF 9.12.5). -/
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

/-- `Gi(z) + Hi(z) = Bi(z)` (DLMF 9.12.11). -/
@[dlmf 9.12.E11]
theorem scorerGi_add_scorerHi (z : ℂ) :
    scorerGi z + scorerHi z = airyBi z := by
  simp [scorerGi]

/-- `Gi(z) = (e^{πi/3}/2) Hi(z e^{-2πi/3}) + (e^{-πi/3}/2) Hi(z e^{2πi/3})` (DLMF 9.12.12). -/
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
    simp only [sqrt_three_sq, I_sq]
    ring
  refine isAiryInhomSol_scorerGi.eq_of_initial (hR.congr_const hc) ?_ ?_ z
  · simp only [zero_mul]
    rw [scorer_zero.1, exp_pi_I_div_three, exp_neg_pi_I_div_three']; ring
  · simp only [zero_mul]
    rw [scorerDeriv_zero.1, exp_pi_I_div_three, exp_neg_pi_I_div_three',
        exp_neg_two_pi_I_div_three',
      exp_two_pi_I_div_three]
    push_cast
    ring_nf
    simp only [sqrt_three_sq, I_sq]
    ring

/-- For `ε = ±1`, `Gi(z) = e^{-πiε/3} Hi(z e^{2πiε/3}) + iε Ai(z)` (DLMF 9.12.13). -/
@[dlmf 9.12.E13]
theorem scorerGi_eq_rotated_scorerHi (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    scorerGi z = exp (-ε * (π * I / 3)) * scorerHi (z * exp (ε * (2 * π * I / 3))) + ε * I *
        airyAi z := by
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
    push_cast; sqrt3_ring
  · simp only [zero_mul]
    rw [scorerDeriv_zero.2.1, airyBiDeriv_zero_eq, scorerHiDeriv_zero_eq, e3, e1]
    push_cast; sqrt3_ring; try (simp only [hε2]; ring_nf)

/-- For `ε = ±1`, `Hi(z) = e^{2πiε/3} Hi(z e^{2πiε/3}) + 2 e^{-πiε/6} Ai(z e^{-2πiε/3})`
(DLMF 9.12.14). -/
@[dlmf 9.12.E14]
theorem scorerHi_connection (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    scorerHi z = exp (ε * (2 * π * I / 3)) * scorerHi (z * exp (ε * (2 * π * I / 3))) +
      2 * exp (-ε * (π * I / 6)) * airyAi (z * exp (-ε * (2 * π * I / 3))) := by
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> simp
  have h1 : exp (ε * (2 * π * I / 3)) ^ 3 = 1 := by
    have := exp_neg_eps_cube hε'; push_cast at this; simpa using this
  have h2 : exp (-ε * (2 * π * I / 3)) ^ 3 = 1 := exp_neg_eps_cube hε
  obtain ⟨e1, e2, -, e4⟩ := exp_eps_values hε
  have hR := ((isAiryInhomSol_scorerHi.rotate h1).const_mul (exp (ε * (2 * π * I / 3)))).add
    ((IsAiryInhomSol.of_airy (isAirySol_airyAi_mul h2)).const_mul (2 * exp (-ε * (π * I / 6))))
  have hc : exp (ε * (2 * π * I / 3)) * (exp (ε * (2 * π * I / 3)) ^ 2 * (1 / π)) +
      2 * exp (-ε * (π * I / 6)) * 0 = 1 / π := by
    rw [mul_zero, add_zero, ← mul_assoc, ← pow_succ', h1, one_mul]
  refine isAiryInhomSol_scorerHi.eq_of_initial (hR.congr_const hc) ?_ ?_ z
  · simp only [zero_mul]
    rw [scorerHi_zero_eq, e1, e4]
    push_cast; sqrt3_ring
  · simp only [zero_mul]
    rw [scorerHiDeriv_zero_eq, e1, e2, e4]
    push_cast; sqrt3_ring

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
  have h := (FormalMultilinearSeries.ofScalars ℂ scorerGiCoeff).hasFPowerSeriesOnBall
      (by rw [hr]; simp)
  rw [hr] at h
  have he : (FormalMultilinearSeries.ofScalars ℂ scorerGiCoeff).sum = fun z =>
      ∑' k : ℕ, scorerGiCoeff k * z ^ k := by
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

/-- Maclaurin series `Gi(z) = 3^{-2/3} π⁻¹ ∑ cos((2k-1)π/3) Γ((k+1)/3) (3^{1/3} z)^k / k!`
(DLMF 9.12.15). -/
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

/-- Maclaurin series `Gi'(z) = 3^{-1/3} π⁻¹ ∑ cos((2k+1)π/3) Γ((k+2)/3) (3^{1/3} z)^k / k!`
(DLMF 9.12.16). -/
@[dlmf 9.12.E16]
theorem hasSum_scorerGiDeriv (z : ℂ) :
    HasSum (fun k : ℕ => (3 : ℂ) ^ (-1 / 3 : ℂ) / π * cos ((2 * (k : ℂ) + 1) * π / 3) *
      Gamma (((k : ℂ) + 2) / 3) * ((3 : ℂ) ^ (1 / 3 : ℂ) * z) ^ k /
          k.factorial) (scorerGiDeriv z) := by
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

/-- Maclaurin series `Hi(z) = 3^{-2/3} π⁻¹ ∑ Γ((k+1)/3) (3^{1/3} z)^k / k!` (DLMF 9.12.17). -/
@[dlmf 9.12.E17]
theorem hasSum_scorerHi (z : ℂ) :
    HasSum (fun k : ℕ => scorerHiCoeff k * z ^ k) (scorerHi z) := by
  exact hasFPowerSeriesOnBall_scorerHi.hasSum_mul_pow (mem_eball_top z)

/-- Maclaurin series `Hi'(z) = 3^{-1/3} π⁻¹ ∑ Γ((k+2)/3) (3^{1/3} z)^k / k!` (DLMF 9.12.18). -/
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
      · nlinarith
          [sq_nonneg (b * t - b ^ 2 - 3 * b), sq_nonneg t, mul_pos ht (by linarith : (0:ℝ) < b)]
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

/-- `Hi(z) = π⁻¹ ∫₀^∞ exp(-t³/3 + z t) dt`, with the integrand integrable (DLMF 9.12.20). -/
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

/-- `Gi(z) = -π⁻¹ ∫₀^∞ exp(-t³/3 - z t/2) cos(√3 z t/2 + 2π/3) dt` (DLMF 9.12.21). -/
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

/-- For `|arg z| < π/3`,
`Hi(-z) = 4z²/(3^{3/2} π²) ∫₀^∞ K_{1/3}(t)/(ζ² + t²) dt` with `ζ = (2/3) z^{3/2}` (DLMF 9.12.22). -/
@[dlmf 9.12.E22]
theorem scorerHi_stieltjes_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π / 3) :
    scorerHi (-z) = 4 * z ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * π ^ 2) *
      ∫ t : ℝ in Ioi 0, DLMF.Bessel.besselK (1 / 3) t / (airyZetaComplex z ^ 2 + (t : ℂ) ^ 2) := by
  sorry

/-- For `x > 0`, `Gi(x) = 4x²/(3^{3/2} π²) ⨍₀^∞ K_{1/3}(t)/(ζ² - t²) dt` (principal value at
`t = ζ = (2/3) x^{3/2}`) (DLMF 9.12.23). -/
@[dlmf 9.12.E23]
theorem scorerGi_principalValue {x : ℝ} (hx : 0 < x) :
    scorerGi x = 4 * (x : ℂ) ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * π ^ 2) *
      principalValueIoi (fun t : ℝ => DLMF.Bessel.besselK (1 / 3) t /
        ((airyZeta x : ℂ) ^ 2 - (t : ℂ) ^ 2)) (airyZeta x) := by
  sorry

/-- Mellin–Barnes integral for `Hi` on a vertical line `Re s = σ ∈ (-1, 0)`, for
`|arg(-z)| < 2π/3`; boundary values are ordinary improper integrals (DLMF 9.12.24). -/
@[dlmf 9.12.E24]
theorem scorerHi_mellinBarnes {z : ℂ} (hz0 : z ≠ 0) (hz : |arg (-z)| < 2 * π / 3) {σ : ℝ}
    (hσ0 : -1 < σ) (hσ1 : σ < 0) :
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

end DLMF.Airy
end
