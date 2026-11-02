/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Basic.Properties
public import DLMFMathlib.Analysis.Analytic.OfScalarsDeriv

/-!
# Scorer functions (DLMF §9.12)

The Scorer function `Hi` is defined by its Maclaurin series (DLMF 9.12.17), and `Gi = Bi - Hi`.
Both solve the inhomogeneous Airy equation `w'' = z w ± 1/π`.

## Main definitions

* `scorerHi`, `scorerHiCoeff`: `Hi` and its Maclaurin coefficients (DLMF 9.12.17).
* `scorerGi`: the complementary function, with `Gi + Hi = Bi`.
* `scorerHiDeriv`, `scorerGiDeriv`: the derivatives.
* `IsScorerSol`: solutions of `w'' = z w + 1/π` on all of `ℂ`.

## Main results

* `hasFPowerSeriesOnBall_scorerHi`, `differentiable_scorerHi`, `scorerGi_entire`: both
  functions are entire.
* `scorerHi_ode`, `scorerGi_ode`, `scorerHi_rotated_ode`: DLMF 9.12.1, 9.12.3.
* `scorer_general_solution`: DLMF 9.12.2.
* `scorer_zero`, `scorerDeriv_zero`: DLMF 9.12.6, 9.12.7.

## Implementation notes

The variation-of-parameters formulas, connection formulas, the Maclaurin series of `Gi` and
the integral representations are in `DLMF.Airy.Scorer.Representations`.
-/

@[expose] public noncomputable section

open Complex FormalMultilinearSeries
open scoped Real Nat NNReal ENNReal

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
  have h1 := HasFPowerSeriesOnBall.deriv_ofScalars hasFPowerSeriesOnBall_scorerHi
  have h2 := HasFPowerSeriesOnBall.deriv_ofScalars h1
  have hdiff : DifferentiableAt ℂ scorerHiDeriv z :=
    (h1.analyticAt_of_mem (mem_eball_top z)).differentiableAt
  have hs := HasFPowerSeriesOnBall.hasSum_mul_pow h2 (mem_eball_top z)
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
  have h := hasFPowerSeriesOnBall_scorerHi.deriv_ofScalars.hasSum_mul_pow
    (mem_eball_top 0)
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

end DLMF.Airy
