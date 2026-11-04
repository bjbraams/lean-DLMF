/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.GeneralIdentities
public import DLMF.Painleve.Basic.Solutions
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Orthogonal polynomials for the Freud weight (DLMF §32.15)

The monic orthogonal polynomials `p_n` of the weight `exp(-ξ⁴/4 - zξ²)` on `ℝ` (DLMF 32.15.1),
constructed by Gram–Schmidt, and the discrete Painlevé I equation 32.15.3 for the squared
recurrence coefficients `u_n = h_n/h_{n-1}`, with `h_n = ∫ p_n² dμ`. The proof combines the
three-term recurrence of the symmetric weight with the integration-by-parts identity
`∫ q' w = ∫ q (ξ³ + 2zξ) w` applied to `q = p_n p_{n-1}` (the string equation).

## Main results

* `DLMF.Painleve.FreudWeight.exists_monic_isOrthogonalPolynomials`: a measure with finite
  moments that is positive on nonzero squares has monic orthogonal polynomials.
* `DLMF.Painleve.FreudWeight.measure`: the measure `exp(-ξ⁴/4 - zξ²) dξ`.
* `DLMF.Painleve.FreudWeight.functional_derivative`: integration by parts against the weight.
* `DLMF.Painleve.FreudWeight.string_equation`: `(m+1) h_m = h_{m+2} + (h_{m+1}/h_m) ∫ (ξ p_m)²
  + 2z h_{m+1}`.
* `DLMF.Painleve.FreudWeight.freudRecurrenceSq_succ`: the Hankel-determinant `u_{m+1}` equals
  `h_{m+1}/h_m`.
* `DLMF.Painleve.FreudWeight.discretePainleveI`: DLMF 32.15.3.
-/

@[expose] public section

open Polynomial MeasureTheory DLMF.OrthogonalPolynomials
open scoped NNReal ENNReal

namespace DLMF.Painleve.FreudWeight

variable {μ : Measure ℝ}

/-- Every polynomial is integrable when all monomials are. -/
theorem integrable_eval (hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    Integrable (fun x => q.eval x) μ := by
  have : (fun x => q.eval x) = fun x => ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * x ^ i := funext fun x => eval_eq_sum_range x
  rw [this]
  exact integrable_finsetSum _ fun i _ => (hint i).const_mul _

/-- Integration against `μ` as a linear functional on polynomials. -/
noncomputable def polyIntegral (μ : Measure ℝ) (hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) :
    ℝ[X] →ₗ[ℝ] ℝ where
  toFun q := ∫ x, q.eval x ∂μ
  map_add' q r := by
    simp only [eval_add]
    exact integral_add (integrable_eval hint q) (integrable_eval hint r)
  map_smul' c q := by
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

/-- `polyIntegral μ hint q = ∫ q dμ`. -/
theorem polyIntegral_apply (hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    polyIntegral μ hint q = ∫ x, q.eval x ∂μ := rfl

/-- The Gram–Schmidt polynomials: `p_n = Xⁿ - ∑_{k<n} (∫ xⁿ p_k / ∫ p_k²) p_k`. -/
noncomputable def gramSchmidtPoly (μ : Measure ℝ) (n : ℕ) : ℝ[X] :=
  X ^ n - ∑ k : Fin n, C ((∫ x, x ^ n * (gramSchmidtPoly μ k).eval x ∂μ) /
      ∫ x, (gramSchmidtPoly μ k).eval x ^ 2 ∂μ) * gramSchmidtPoly μ k
termination_by n
decreasing_by all_goals exact k.isLt

/-- The Gram–Schmidt polynomials are monic of exact degree and mutually orthogonal. -/
theorem gramSchmidtPoly_spec (hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ)
    (hpos : ∀ q : ℝ[X], q ≠ 0 → 0 < ∫ x, q.eval x ^ 2 ∂μ) (n : ℕ) :
    (gramSchmidtPoly μ n).Monic ∧ (gramSchmidtPoly μ n).natDegree = n ∧
      ∀ m < n, ∫ x, (gramSchmidtPoly μ n).eval x * (gramSchmidtPoly μ m).eval x ∂μ = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  set p := gramSchmidtPoly μ with hp
  have hdef : p n = X ^ n - ∑ k : Fin n, C ((∫ x, x ^ n * (p k).eval x ∂μ) /
      ∫ x, (p k).eval x ^ 2 ∂μ) * p k := by
    rw [hp, gramSchmidtPoly]
  have hdeg : (∑ k : Fin n, C ((∫ x, x ^ n * (p k).eval x ∂μ) /
      ∫ x, (p k).eval x ^ 2 ∂μ) * p k).degree < (X ^ n : ℝ[X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr (by simp))).2 fun k _ => ?_
    rw [← smul_eq_C_mul]
    refine lt_of_le_of_lt (degree_smul_le _ _) ?_
    rw [degree_eq_natDegree (ih k k.isLt).1.ne_zero, (ih k k.isLt).2.1]
    exact_mod_cast k.isLt
  have hmon : (p n).Monic := by
    rw [hdef]
    exact (monic_X_pow n).sub_of_left hdeg
  refine ⟨hmon, ?_, ?_⟩
  · rw [hdef]
    refine natDegree_eq_of_degree_eq_some ?_
    rw [degree_sub_eq_left_of_degree_lt hdeg, degree_X_pow]
  · intro m hm
    have L := polyIntegral μ hint
    have hprod : ∀ q r : ℝ[X], ∫ x, q.eval x * r.eval x ∂μ = polyIntegral μ hint (q * r) := by
      intro q r; simp [polyIntegral_apply]
    have horth : ∀ k : Fin n, (k : ℕ) ≠ m → polyIntegral μ hint (p k * p m) = 0 := by
      intro k hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [mul_comm, ← hprod]; exact (ih m hm).2.2 k h
      · rw [← hprod]; exact (ih k k.isLt).2.2 m h
    have hnorm : 0 < polyIntegral μ hint (p m * p m) := by
      rw [← hprod]
      simpa [sq] using hpos (p m) (ih m hm).1.ne_zero
    rw [hprod, hdef, sub_mul, map_sub, Finset.sum_mul, map_sum]
    rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin n)]
    · rw [mul_assoc, ← smul_eq_C_mul, map_smul, smul_eq_mul]
      rw [← hprod, ← hprod]
      have hn2 : ∫ x, (p m).eval x ^ 2 ∂μ = ∫ x, (p m).eval x * (p m).eval x ∂μ := by
        simp [sq]
      have hne : ∫ x, (p m).eval x * (p m).eval x ∂μ ≠ 0 := by rw [hprod]; exact hnorm.ne'
      rw [hn2, div_mul_cancel₀ _ hne]
      simp
    · intro k _ hk
      rw [mul_assoc, ← smul_eq_C_mul, map_smul, horth k (fun h => hk (Fin.ext h)), smul_zero]
    · simp

/-- A measure with finite moments that is positive on nonzero squares of polynomials has a
sequence of monic orthogonal polynomials. -/
theorem exists_monic_isOrthogonalPolynomials
    (hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ)
    (hpos : ∀ q : ℝ[X], q ≠ 0 → 0 < ∫ x, q.eval x ^ 2 ∂μ) :
    ∃ p : ℕ → ℝ[X], IsOrthogonalPolynomials μ p ∧ ∀ n, (p n).Monic := by
  have hs := gramSchmidtPoly_spec hint hpos
  refine ⟨gramSchmidtPoly μ, ⟨fun n => (hs n).2.1, fun n => ?_,
    fun n => hpos _ (hs n).1.ne_zero, fun m n hmn => ?_⟩, fun n => (hs n).1⟩
  · exact (integrable_eval hint (gramSchmidtPoly μ n ^ 2)).congr
      (Filter.Eventually.of_forall fun x => by simp [Polynomial.eval_pow])
  · rcases lt_or_gt_of_ne hmn with h | h
    · rw [← (hs n).2.2 m h]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    · exact (hs m).2.2 n h

/-- The Freud weight `exp(-ξ⁴/4 - zξ²)` as a nonnegative function. -/
noncomputable def density (z x : ℝ) : ℝ≥0 := (Real.exp (-(x ^ 4 / 4) - z * x ^ 2)).toNNReal

/-- The density as a real number. -/
private theorem coe_density (z x : ℝ) : (density z x : ℝ) = Real.exp (-(x ^ 4 / 4) - z * x ^ 2) :=
  Real.coe_toNNReal _ (Real.exp_pos _).le

/-- The Freud density is measurable. -/
private theorem measurable_density (z : ℝ) : Measurable (density z) :=
  (by fun_prop : Measurable fun x : ℝ => Real.exp (-(x ^ 4 / 4) - z * x ^ 2)).real_toNNReal

/-- The measure `exp(-ξ⁴/4 - zξ²) dξ` of DLMF 32.15.1. -/
noncomputable def measure (z : ℝ) : Measure ℝ :=
  volume.withDensity fun x => (density z x : ℝ≥0∞)

/-- Integrals against the Freud measure are integrals against the weight. -/
theorem integral_measure (z : ℝ) (g : ℝ → ℝ) :
    ∫ x, g x ∂measure z = ∫ x, Real.exp (-(x ^ 4 / 4) - z * x ^ 2) * g x := by
  rw [measure, integral_withDensity_eq_integral_smul (measurable_density z)]
  simp [NNReal.smul_def, coe_density]

/-- Integrability against the Freud measure. -/
theorem integrable_measure_iff (z : ℝ) (g : ℝ → ℝ) :
    Integrable g (measure z) ↔
      Integrable (fun x => Real.exp (-(x ^ 4 / 4) - z * x ^ 2) * g x) := by
  rw [measure, integrable_withDensity_iff_integrable_smul (measurable_density z)]
  simp [NNReal.smul_def, coe_density]

/-- The Freud weight is dominated by a Gaussian. -/
private theorem exp_le (z x : ℝ) :
    Real.exp (-(x ^ 4 / 4) - z * x ^ 2) ≤ Real.exp ((z - 1) ^ 2) * Real.exp (-(x ^ 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (x ^ 2 / 2 + (z - 1))]

/-- All moments of the Freud measure are finite. -/
theorem integrable_pow (z : ℝ) (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (measure z) := by
  rw [integrable_measure_iff]
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
    (s := (k : ℝ)) (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  have h' : Integrable fun x : ℝ => x ^ k * Real.exp (-(x ^ 2)) :=
    h.congr (Filter.Eventually.of_forall fun x => by simp [Real.rpow_natCast])
  refine (h'.norm.const_mul (Real.exp ((z - 1) ^ 2))).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-(x ^ 4 / 4) - z * x ^ 2) * ‖x ^ k‖
      ≤ Real.exp ((z - 1) ^ 2) * Real.exp (-(x ^ 2)) * ‖x ^ k‖ :=
        mul_le_mul_of_nonneg_right (exp_le z x) (norm_nonneg _)
    _ = _ := by ring

/-- The Freud measure is positive on the square of a nonzero polynomial. -/
theorem integral_sq_pos (z : ℝ) {q : ℝ[X]} (hq : q ≠ 0) :
    0 < ∫ x, q.eval x ^ 2 ∂measure z := by
  rw [integral_measure]
  have hint : Integrable fun x => Real.exp (-(x ^ 4 / 4) - z * x ^ 2) * q.eval x ^ 2 := by
    rw [← integrable_measure_iff]
    exact (integrable_eval (integrable_pow z) (q ^ 2)).congr
      (Filter.Eventually.of_forall fun x => by simp [Polynomial.eval_pow])
  rw [integral_pos_iff_support_of_nonneg (fun x => by positivity) hint]
  have hopen : IsOpen {x : ℝ | q.eval x ≠ 0} :=
    isOpen_ne_fun (Polynomial.continuous q) continuous_const
  obtain ⟨x, hx⟩ : ∃ x : ℝ, q.eval x ≠ 0 := by
    by_contra h
    push Not at h
    exact hq (Polynomial.funext (by simpa using h))
  refine lt_of_lt_of_le (hopen.measure_pos volume ⟨x, hx⟩) (measure_mono fun y hy => ?_)
  simp only [Function.mem_support]
  exact mul_ne_zero (Real.exp_pos _).ne' (pow_ne_zero 2 hy)

/-- The Freud measure is symmetric under `ξ ↦ -ξ`. -/
theorem map_neg_measure (z : ℝ) : Measure.map (fun x : ℝ => -x) (measure z) = measure z := by
  ext s hs
  rw [Measure.map_apply measurable_neg hs, measure, withDensity_apply _ hs,
    withDensity_apply _ (measurable_neg hs)]
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage hs
    (f := fun x => (density z x : ℝ≥0∞)) (measurable_density z).coe_nnreal_ennreal
  rw [← h]
  congr 1
  funext x
  have h4 : (-x) ^ 4 = x ^ 4 := by ring
  simp [density, h4]



/-- Integration against the Freud measure as a linear functional on polynomials. -/
noncomputable def functional (z : ℝ) : ℝ[X] →ₗ[ℝ] ℝ := polyIntegral (measure z) (integrable_pow z)

/-- `functional z q = ∫ q dμ_z`. -/
private theorem functional_apply (z : ℝ) (q : ℝ[X]) :
    functional z q = ∫ x, q.eval x ∂measure z := rfl

/-- Integrals of products of polynomials through `functional`. -/
private theorem integral_eq_functional (z : ℝ) (q r : ℝ[X]) :
    ∫ x, q.eval x * r.eval x ∂measure z = functional z (q * r) := by
  simp [functional_apply]

/-- Integration by parts against the Freud weight: `∫ q' w = ∫ q (ξ³ + 2zξ) w`. -/
theorem functional_derivative (z : ℝ) (q : ℝ[X]) :
    functional z (derivative q) = functional z (q * (X ^ 3 + C (2 * z) * X)) := by
  set w : ℝ → ℝ := fun x => Real.exp (-(x ^ 4 / 4) - z * x ^ 2) with hw
  have hI : ∀ r : ℝ[X], Integrable fun x => w x * r.eval x := fun r =>
    (integrable_measure_iff z _).1 (integrable_eval (integrable_pow z) r)
  rw [functional_apply, functional_apply, integral_measure, integral_measure]
  have hu : ∀ x ∈ tsupport w, HasDerivAt (fun x => q.eval x) ((derivative q).eval x) x :=
    fun x _ => q.hasDerivAt x
  have hv : ∀ x ∈ tsupport (fun x => q.eval x),
      HasDerivAt w (-(x ^ 3 + 2 * z * x) * w x) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -(x ^ 4 / 4) - z * x ^ 2)
        (-x ^ 3 - z * (2 * x)) x := by
      have := (((hasDerivAt_pow 4 x).div_const 4).neg).sub ((hasDerivAt_pow 2 x).const_mul z)
      exact this.congr_deriv (by norm_num)
    have := h1.exp
    refine this.congr_deriv ?_
    simp only [hw]
    ring
  have huv' : Integrable ((fun x => q.eval x) * fun x => -(x ^ 3 + 2 * z * x) * w x) :=
    (hI (-(q * (X ^ 3 + C (2 * z) * X)))).congr
      (Filter.Eventually.of_forall fun x => by simp; ring)
  have hu'v : Integrable ((fun x => (derivative q).eval x) * w) :=
    (hI (derivative q)).congr (Filter.Eventually.of_forall fun x => by simp; ring)
  have huv : Integrable ((fun x => q.eval x) * w) :=
    (hI q).congr (Filter.Eventually.of_forall fun x => by simp; ring)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv huv' hu'v huv
  have e1 : ∫ x, w x * (derivative q).eval x = ∫ x, (derivative q).eval x * w x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have e2 : ∫ x, w x * (q * (X ^ 3 + C (2 * z) * X)).eval x =
      -∫ x, q.eval x * (-(x ^ 3 + 2 * z * x) * w x) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp; ring)
  rw [e1, e2, key, neg_neg]

/-- The Hankel determinants `freudHankel` are those of the Freud measure. -/
theorem freudHankel_eq (z : ℝ) (n : ℕ) : freudHankel z n = hankelDeterminant (measure z) n := by
  unfold freudHankel hankelDeterminant
  congr 1
  ext i j
  simp only [Matrix.of_apply, moment, freudMoment, integral_measure]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

section Orthogonal

variable {z : ℝ} {p : ℕ → ℝ[X]} (hp : IsOrthogonalPolynomials (measure z) p)
  (hmon : ∀ n, (p n).Monic)
include hp

/-- The norms `h_k = ∫ p_k² dμ_z` are positive. -/
private theorem functional_pos (k : ℕ) : 0 < functional z (p k * p k) := by
  rw [← integral_eq_functional]
  simpa [sq] using hp.2.2.1 k

/-- Orthogonality in terms of `functional`. -/
private theorem functional_orth {i j : ℕ} (hij : i ≠ j) : functional z (p i * p j) = 0 := by
  rw [← integral_eq_functional]
  exact hp.2.2.2 i j hij

include hmon

/-- The leading coefficient of the monic `p_k`. -/
private theorem coeff_self (k : ℕ) : (p k).coeff k = 1 := by
  have := (hmon k).coeff_natDegree
  rwa [hp.1 k] at this

/-- For `deg q ≤ k`, `∫ q p_k dμ_z = [ξᵏ]q · h_k`. -/
private theorem functional_mul_eq {q : ℝ[X]} {k : ℕ} (hq : q.natDegree ≤ k) :
    functional z (q * p k) = q.coeff k * functional z (p k * p k) := by
  set r := q - C (q.coeff k) * p k with hr_def
  have hr : r.degree < k := by
    rw [degree_lt_iff_coeff_zero]
    intro m hm'
    simp only [r, coeff_sub, coeff_C_mul]
    rcases eq_or_lt_of_le hm' with rfl | hlt
    · rw [coeff_self hp hmon]; ring
    · rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt hlt),
        coeff_eq_zero_of_natDegree_lt (p := p k) (n := m) (by rw [hp.1 k]; exact hlt)]
      ring
  have h0 := hp.integral_mul_eq_zero_of_degree_lt hr
  rw [integral_eq_functional] at h0
  have : q = r + C (q.coeff k) * p k := by simp [r]
  conv_lhs => rw [this]
  rw [add_mul, map_add, h0, mul_assoc, ← smul_eq_C_mul, map_smul, smul_eq_mul, zero_add]

omit hmon in
/-- By symmetry, `∫ ξ p_k² dμ_z = 0`. -/
private theorem functional_X_mul_mul_self (k : ℕ) : functional z (X * p k * p k) = 0 := by
  have hpar := symmetric_measure_parity hp (map_neg_measure z) k
  rw [functional_apply]
  set f : ℝ → ℝ := fun x => (X * p k * p k).eval x with hf
  have hodd : ∀ x, f (-x) = -f x := by
    intro x
    simp only [f, eval_mul, eval_X, hpar]
    have : ((-1 : ℝ) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_pow]; simp
    linear_combination (-x * (p k).eval x * (p k).eval x) * this
  have hmap : ∫ x, f x ∂measure z = ∫ x, f (-x) ∂measure z := by
    conv_lhs => rw [← map_neg_measure z]
    exact integral_map measurable_neg.aemeasurable
      (X * p k * p k).continuous.aestronglyMeasurable
  simp_rw [hodd, integral_neg] at hmap
  change ∫ x, f x ∂measure z = 0
  linarith

omit hmon in
/-- `deg (X p_k) ≤ k + 1`. -/
private theorem natDegree_X_mul_le (k : ℕ) : (X * p k).natDegree ≤ k + 1 :=
  natDegree_mul_le.trans (by rw [natDegree_X, hp.1 k]; omega)

/-- `X p_k` is monic of degree `k + 1`. -/
private theorem coeff_X_mul_self (k : ℕ) : (X * p k).coeff (k + 1) = 1 := by
  rw [coeff_X_mul, coeff_self hp hmon]

/-- The recurrence at `n = 0`: `ξ p_0 = p_1`. -/
theorem X_mul_zero : X * p 0 = p 1 := by
  have h0 : p 0 = 1 := eq_one_of_monic_natDegree_zero (hmon 0) (hp.1 0)
  set r := X * p 0 - p 1 with hr_def
  have hr : r.natDegree ≤ 0 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [r, h0, mul_one, coeff_sub, coeff_X]
    rcases Nat.lt_or_ge 1 N with h | h
    · simp [show 1 ≠ N by omega,
        coeff_eq_zero_of_natDegree_lt (p := p 1) (n := N) (by rw [hp.1 1]; exact h)]
    · obtain rfl : N = 1 := by omega
      simp [coeff_self hp hmon]
  have hL : functional z (r * p 0) = 0 := by
    rw [hr_def, sub_mul, map_sub, functional_X_mul_mul_self hp, functional_orth hp (by omega)]
    ring
  rw [functional_mul_eq hp hmon hr] at hL
  have hc : r.coeff 0 = 0 := by
    rcases mul_eq_zero.1 hL with h | h
    · exact h
    · exact absurd h (functional_pos hp 0).ne'
  have : r = 0 := by rw [eq_C_of_natDegree_le_zero hr, hc, map_zero]
  exact sub_eq_zero.1 this

/-- The three-term recurrence `ξ p_{k+1} = p_{k+2} + (h_{k+1}/h_k) p_k` of the symmetric
Freud weight. -/
theorem X_mul_succ (k : ℕ) :
    X * p (k + 1) = p (k + 2) +
      C (functional z (p (k + 1) * p (k + 1)) / functional z (p k * p k)) * p k := by
  obtain ⟨a, b, c, habc⟩ := three_term_recurrence hp k
  have key : ∀ j, functional z (X * p (k + 1) * p j) = a * functional z (p (k + 2) * p j) +
      b * functional z (p (k + 1) * p j) + c * functional z (p k * p j) := by
    intro j
    rw [habc]
    simp only [add_mul, map_add, ← smul_eq_C_mul, smul_mul_assoc, map_smul, smul_eq_mul]
  have ha : a = 1 := by
    have h := key (k + 2)
    rw [functional_mul_eq hp hmon (natDegree_X_mul_le hp (k + 1)), coeff_X_mul_self hp hmon,
      functional_orth hp (i := k + 1) (j := k + 2) (by omega),
      functional_orth hp (i := k) (j := k + 2) (by omega)] at h
    have := functional_pos hp (k + 2)
    have h' : (a - 1) * functional z (p (k + 2) * p (k + 2)) = 0 := by linarith
    rcases mul_eq_zero.1 h' with h'' | h''
    · linarith
    · linarith
  have hb : b = 0 := by
    have h := key (k + 1)
    rw [functional_X_mul_mul_self hp, functional_orth hp (i := k + 2) (j := k + 1) (by omega),
      functional_orth hp (i := k) (j := k + 1) (by omega)] at h
    have := functional_pos hp (k + 1)
    rcases mul_eq_zero.1 (show b * functional z (p (k + 1) * p (k + 1)) = 0 by linarith)
      with h'' | h''
    · exact h''
    · linarith
  have hc : c = functional z (p (k + 1) * p (k + 1)) / functional z (p k * p k) := by
    have h := key k
    rw [show X * p (k + 1) * p k = X * p k * p (k + 1) by ring,
      functional_mul_eq hp hmon (natDegree_X_mul_le hp k), coeff_X_mul_self hp hmon,
      functional_orth hp (i := k + 2) (j := k) (by omega),
      functional_orth hp (i := k + 1) (j := k) (by omega)] at h
    have := functional_pos hp k
    rw [eq_div_iff this.ne']
    linarith
  rw [habc, ha, hb, hc]
  simp

/-- `∫ (ξ p_0)² dμ_z = h_1`. -/
private theorem functional_X_mul_sq_zero :
    functional z (X * p 0 * (X * p 0)) = functional z (p 1 * p 1) := by
  rw [X_mul_zero hp hmon]

/-- `∫ (ξ p_{j+1})² dμ_z = h_{j+2} + (h_{j+1}/h_j) h_{j+1}`. -/
private theorem functional_X_mul_sq_succ (j : ℕ) :
    functional z (X * p (j + 1) * (X * p (j + 1))) = functional z (p (j + 2) * p (j + 2)) +
      functional z (p (j + 1) * p (j + 1)) / functional z (p j * p j) *
        functional z (p (j + 1) * p (j + 1)) := by
  nth_rewrite 2 [X_mul_succ hp hmon]
  rw [mul_add, map_add, functional_mul_eq hp hmon (natDegree_X_mul_le hp (j + 1)),
    coeff_X_mul_self hp hmon, one_mul,
    show X * p (j + 1) * (C (functional z (p (j + 1) * p (j + 1)) /
      functional z (p j * p j)) * p j) = C (functional z (p (j + 1) * p (j + 1)) /
      functional z (p j * p j)) * (X * p j * p (j + 1)) by ring,
    ← smul_eq_C_mul, map_smul, smul_eq_mul,
    functional_mul_eq hp hmon (natDegree_X_mul_le hp j), coeff_X_mul_self hp hmon, one_mul]

/-- The Freud string equation in terms of the norms `h_m = ∫ p_m² dμ`. -/
theorem string_equation (m : ℕ) :
    (m + 1) * functional z (p m * p m) = functional z (p (m + 2) * p (m + 2)) +
      functional z (p (m + 1) * p (m + 1)) / functional z (p m * p m) *
        functional z (X * p m * (X * p m)) + 2 * z * functional z (p (m + 1) * p (m + 1)) := by
  have hibp := functional_derivative z (p (m + 1) * p m)
  have hd1 : (derivative (p (m + 1))).natDegree ≤ m :=
    (natDegree_derivative_le _).trans (by rw [hp.1]; omega)
  have hd2 : (derivative (p m)).natDegree ≤ m + 1 :=
    (natDegree_derivative_le _).trans (by rw [hp.1]; omega)
  rw [derivative_mul, map_add, functional_mul_eq hp hmon hd1, mul_comm (p (m + 1)),
    functional_mul_eq hp hmon hd2, coeff_derivative, coeff_derivative, coeff_self hp hmon,
    coeff_eq_zero_of_natDegree_lt (by rw [hp.1]; omega : (p m).natDegree < m + 1 + 1)] at hibp
  have hXX : (X * (X * p m)).natDegree ≤ m + 2 := by
    have h1 := natDegree_X_mul_le hp m
    have h2 : (X * (X * p m)).natDegree ≤ (X : ℝ[X]).natDegree + (X * p m).natDegree :=
      natDegree_mul_le
    rw [natDegree_X] at h2
    omega
  rw [show p (m + 1) * p m * (X ^ 3 + C (2 * z) * X) =
      X * p (m + 1) * (X * (X * p m)) + C (2 * z) * (X * p m * p (m + 1)) by ring,
    map_add, ← smul_eq_C_mul, map_smul, smul_eq_mul,
    functional_mul_eq hp hmon (natDegree_X_mul_le hp m), coeff_X_mul_self hp hmon, one_mul,
    X_mul_succ hp hmon, add_mul (p (m + 2)), map_add, mul_comm (p (m + 2)),
    functional_mul_eq hp hmon hXX,
    coeff_X_mul, coeff_X_mul_self hp hmon, one_mul, ← smul_eq_C_mul, smul_mul_assoc, map_smul,
    smul_eq_mul, show p m * (X * (X * p m)) = X * p m * (X * p m) by ring] at hibp
  push_cast at hibp
  linear_combination hibp

/-- `u_{m+1} = h_{m+1}/h_m`. -/
theorem freudRecurrenceSq_succ (m : ℕ) :
    freudRecurrenceSq z (m + 1) =
      functional z (p (m + 1) * p (m + 1)) / functional z (p m * p m) := by
  have hD : ∀ j, hankelDeterminant (measure z) (j + 1) =
      functional z (p j * p j) * hankelDeterminant (measure z) j := by
    intro j
    rw [hankelDeterminant_succ_eq_squaredNorm_mul hp hmon, squaredNorm,
      ← integral_eq_functional]
    simp [sq]
  simp only [freudRecurrenceSq, Nat.add_one_ne_zero, ↓reduceIte]
  rw [freudHankel_eq, freudHankel_eq, freudHankel_eq, Nat.add_sub_cancel, hD (m + 1), hD m]
  have h0 := functional_pos hp m
  have h1 := functional_pos hp (m + 1)
  have hd := hankelDeterminant_pos hp m
  field_simp

end Orthogonal

/-- DLMF 32.15.3 for the Freud weight. -/
theorem discretePainleveI (z : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (freudRecurrenceSq z (n + 1) + freudRecurrenceSq z n + freudRecurrenceSq z (n - 1)) *
      freudRecurrenceSq z n = n - 2 * z * freudRecurrenceSq z n := by
  obtain ⟨p, hp, hmon⟩ :=
    exists_monic_isOrthogonalPolynomials (integrable_pow z) (fun q hq => integral_sq_pos z hq)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hs := string_equation hp hmon m
  have h0 := functional_pos hp m
  have h1 := functional_pos hp (m + 1)
  have h2 := functional_pos hp (m + 2)
  rw [freudRecurrenceSq_succ hp hmon (m + 1), freudRecurrenceSq_succ hp hmon m,
    Nat.add_sub_cancel]
  rcases m with _ | j
  · rw [functional_X_mul_sq_zero hp hmon] at hs
    rw [show freudRecurrenceSq z 0 = 0 by simp [freudRecurrenceSq]]
    linear_combination (norm := skip) (-1 / functional z (p 0 * p 0)) * hs
    field_simp
    ring
  · rw [functional_X_mul_sq_succ hp hmon j] at hs
    rw [freudRecurrenceSq_succ hp hmon j]
    have hj := functional_pos hp j
    linear_combination (norm := skip) (-1 / functional z (p (j + 1) * p (j + 1))) * hs
    field_simp
    push_cast
    ring

end DLMF.Painleve.FreudWeight
