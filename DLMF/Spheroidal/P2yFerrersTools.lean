/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.IntegralTools
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Tools for the Ferrers expansion of spheroidal functions (DLMF §30.8)

General facts on the weighted space `L²((1-x²)^m dx)` on `[-1, 1]` used for the expansion 30.8.1
of `𝖯s^m_n` in Ferrers functions:

* completeness of the monomials (Weierstrass approximation) and hence of the derivatives
  `P_ν^{(m)}` of the Legendre polynomials;
* the three-term recurrence, parity, orthogonality and an exponential bound of `P_ν^{(m)}`.
-/

@[expose] public noncomputable section

open Complex Set Filter DLMF.Legendre MeasureTheory
open scoped Topology Real

namespace DLMF.Spheroidal

/-- Interval integrals over `[-1, 1]` agree when the integrands agree on `(-1, 1)`. -/
theorem p2y_integral_congr_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f₁ f₂ : ℝ → E} (h : ∀ x ∈ Ioo (-1 : ℝ) 1, f₁ x = f₂ x) :
    ∫ x in (-1 : ℝ)..1, f₁ x = ∫ x in (-1 : ℝ)..1, f₂ x := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with x hx hxI
  rw [uIoc_of_le (by norm_num)] at hxI
  exact h x ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩

/-- A continuous nonnegative function on `[-1, 1]` with zero integral vanishes on `(-1, 1)`. -/
theorem p2y_eq_zero_of_integral_eq_zero {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (h0 : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ f x) (hint : ∫ x in (-1 : ℝ)..1, f x = 0) :
    ∀ x ∈ Ioo (-1 : ℝ) 1, f x = 0 := by
  intro c hc
  by_contra hne
  have hpos : 0 < f c := lt_of_le_of_ne (h0 c (Ioo_subset_Icc_self hc)) (Ne.symm hne)
  have hcont : ContinuousAt f c := hf.continuousAt (Icc_mem_nhds hc.1 hc.2)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont (f c / 2) (by linarith)
  set r := min (δ / 2) (min ((c + 1) / 2) ((1 - c) / 2)) with hr
  have hr0 : 0 < r := by
    simp only [hr, lt_min_iff]; refine ⟨by linarith, by linarith [hc.1], by linarith [hc.2]⟩
  have hr1 : r ≤ δ / 2 := min_le_left _ _
  have hr2 : r ≤ (c + 1) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ (1 - c) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Icc (c - r) (c + r) ⊆ Icc (-1) 1 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hfi : IntervalIntegrable f volume (-1) 1 := hf.intervalIntegrable_of_Icc (by norm_num)
  have hfi' : IntervalIntegrable f volume (c - r) (c + r) :=
    (hf.mono hsub).intervalIntegrable_of_Icc (by linarith)
  have hmono : ∫ x in (c - r)..(c + r), f x ≤ ∫ x in (-1 : ℝ)..1, f x := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith) ?_ hfi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact h0 x ⟨hx.1.le, hx.2⟩
  have hlow : ∫ x in (c - r)..(c + r), f x > 0 := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hfi' (fun x hx => ?_) (by linarith)
    have hd : dist x c < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
    have := hball hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  linarith

/-- **Completeness of the monomials** in `L²((1-x²)^m dx)` on `[-1, 1]`: a continuous `H` all of
whose weighted moments vanish is zero on `(-1, 1)` (Weierstrass approximation). -/
theorem p2y_eq_zero_of_moments {H : ℝ → ℝ} (hH : ContinuousOn H (Icc (-1) 1)) (m : ℕ)
    (h : ∀ i : ℕ, ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x * x ^ i = 0) :
    ∀ x ∈ Ioo (-1 : ℝ) 1, H x = 0 := by
  have hw : ContinuousOn (fun x : ℝ => (1 - x ^ 2) ^ m * H x) (Icc (-1) 1) :=
    (by fun_prop : Continuous fun x : ℝ => (1 - x ^ 2) ^ m).continuousOn.mul hH
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hH).isBounded.exists_norm_le
  have hM' : ∀ x ∈ Icc (-1 : ℝ) 1, |H x| ≤ M := fun x hx => hM _ ⟨x, hx, rfl⟩
  have hw1 : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ (1 - x ^ 2) ^ m ∧ (1 - x ^ 2) ^ m ≤ 1 := by
    intro x hx
    have h1 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have h2 : 1 - x ^ 2 ≤ 1 := by nlinarith
    exact ⟨pow_nonneg h1 m, pow_le_one₀ h1 h2⟩
  -- the integral against any polynomial vanishes
  have hpoly : ∀ p : Polynomial ℝ,
      ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x * p.eval x = 0 := by
    intro p
    have e : (fun x : ℝ => (1 - x ^ 2) ^ m * H x * p.eval x) = fun x =>
        ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ((1 - x ^ 2) ^ m * H x * x ^ i) := by
      funext x; rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e, intervalIntegral.integral_finsetSum]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [intervalIntegral.integral_const_mul, h i, mul_zero]
    · intro i _
      exact (continuousOn_const.mul (hw.mul (continuous_pow i).continuousOn))
        |>.intervalIntegrable_of_Icc (by norm_num)
  -- `∫ w H² ≤ 2 M ε` for every `ε`
  have hsq : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x ^ 2 = 0 := by
    have hnn : 0 ≤ ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x ^ 2 := by
      refine intervalIntegral.integral_nonneg (by norm_num) fun x hx => ?_
      exact mul_nonneg (hw1 x hx).1 (sq_nonneg _)
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) hnn
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 H hH (ε / (2 * (M + 1)))
      (by have : 0 ≤ M := le_trans (abs_nonneg _) (hM' 0 (by norm_num)); positivity)
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM' 0 (by norm_num))
    have e : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x ^ 2 =
        ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x * (H x - p.eval x) := by
      have := hpoly p
      rw [show (fun x : ℝ => (1 - x ^ 2) ^ m * H x * (H x - p.eval x)) = fun x =>
          (1 - x ^ 2) ^ m * H x ^ 2 - (1 - x ^ 2) ^ m * H x * p.eval x by funext x; ring,
        intervalIntegral.integral_sub, this, sub_zero]
      · exact ((hw.mul hH).intervalIntegrable_of_Icc (by norm_num)).congr_uIoo
          (fun x _ => by simp only [Pi.mul_apply]; ring)
      · exact (hw.mul p.continuous.continuousOn).intervalIntegrable_of_Icc (by norm_num)
    rw [e, zero_add]
    calc ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x * (H x - p.eval x)
        ≤ ∫ x in (-1 : ℝ)..1, M * (ε / (2 * (M + 1))) := by
          refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const
            fun x hx => ?_
          · exact (hw.mul (hH.sub p.continuous.continuousOn)).intervalIntegrable_of_Icc
              (by norm_num)
          · have h1 := hw1 x hx
            have h2 := hM' x hx
            have h3 := (hp x hx).le
            rw [abs_sub_comm] at h3
            calc (1 - x ^ 2) ^ m * H x * (H x - p.eval x)
                ≤ |(1 - x ^ 2) ^ m * H x * (H x - p.eval x)| := le_abs_self _
              _ = (1 - x ^ 2) ^ m * |H x| * |H x - p.eval x| := by
                  rw [abs_mul, abs_mul, abs_of_nonneg h1.1]
              _ ≤ 1 * M * (ε / (2 * (M + 1))) := by
                  gcongr
                  exact h1.2
              _ = M * (ε / (2 * (M + 1))) := by ring
      _ ≤ ε := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          rw [show (1 : ℝ) - -1 = 2 by norm_num]
          rw [show 2 * (M * (ε / (2 * (M + 1)))) = ε * (M / (M + 1)) by field_simp]
          have : M / (M + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          nlinarith
  have hz := p2y_eq_zero_of_integral_eq_zero (f := fun x => (1 - x ^ 2) ^ m * H x ^ 2)
    (((by fun_prop : Continuous fun x : ℝ => (1 - x ^ 2) ^ m).continuousOn).mul (hH.pow 2))
    (fun x hx => mul_nonneg (hw1 x hx).1 (sq_nonneg _)) hsq
  intro x hx
  have h1 : 0 < (1 - x ^ 2) ^ m := pow_pos (by nlinarith [hx.1, hx.2]) m
  have := hz x hx
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h1.ne'
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

/-- The three-term recurrence of `P_ν^{(m)}` (from DLMF 14.10.3) on `(-1, 1)`:
`(2ν+1) x P_ν^{(m)} = (ν-m+1) P_{ν+1}^{(m)} + (ν+m) P_{ν-1}^{(m)}`, the last term absent for
`ν = m`. -/
theorem p2y_D_rec (m ν : ℕ) (hν : m ≤ ν) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (2 * (ν : ℝ) + 1) * x * (legInt_D ν m x).re =
      ((ν : ℝ) - m + 1) * (legInt_D (ν + 1) m x).re +
        ((ν : ℝ) + m) * (if m < ν then (legInt_D (ν - 1) m x).re else 0) := by
  have R := ferrersP_recurrence_3 ((ν : ℂ) - 1) m hx
  rw [show (ν : ℂ) - 1 + 2 = ((ν + 1 : ℕ) : ℂ) by push_cast; ring,
    show (ν : ℂ) - 1 + 1 = (ν : ℂ) by ring] at R
  have hs : (0 : ℝ) < (1 - x ^ 2) ^ ((m : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by nlinarith [hx.1, hx.2]) _
  have hlow : ((ν : ℂ) - 1 + m + 1) * ferrersP ((ν : ℂ) - 1) m x =
      ((ν : ℂ) + m) * (if m < ν then (-1) ^ m * (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        legInt_D (ν - 1) m x else 0) := by
    split_ifs with h
    · rw [show (ν : ℂ) - 1 = ((ν - 1 : ℕ) : ℂ) by push_cast [Nat.cast_sub (by omega : 1 ≤ ν)]; ring,
        legInt_ferrersP_nat_nat _ _ hx]
      rw [Nat.cast_sub (by omega : 1 ≤ ν)]; push_cast; ring
    · have hνm : ν = m := by omega
      subst hνm
      rcases Nat.eq_zero_or_pos ν with h0 | h0
      · subst h0; simp
      · rw [show (ν : ℂ) - 1 = ((ν - 1 : ℕ) : ℂ) by push_cast [Nat.cast_sub h0]; ring,
          ferrersP_order_gt_degree _ _ (by omega) hx]
        simp
  rw [hlow, legInt_ferrersP_nat_nat _ _ hx, legInt_ferrersP_nat_nat _ _ hx] at R
  have hsq : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  have hsc : (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have R' : ((ν : ℂ) - m + 1) * legInt_D (ν + 1) m x - (2 * ν + 1) * x * legInt_D ν m x +
      ((ν : ℂ) + m) * (if m < ν then legInt_D (ν - 1) m x else 0) = 0 := by
    have : ((-1 : ℂ) ^ m * (((1 - x ^ 2) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) *
        (((ν : ℂ) - m + 1) * legInt_D (ν + 1) m x - (2 * ν + 1) * x * legInt_D ν m x +
          ((ν : ℂ) + m) * (if m < ν then legInt_D (ν - 1) m x else 0)) = 0 := by
      split_ifs at R ⊢
      · linear_combination R
      · linear_combination R
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero (pow_ne_zero _ (by norm_num)) hsc)
    · exact h
  have h := congrArg Complex.re R'
  split_ifs at h ⊢ with hc
  · simp only [Complex.add_re, Complex.sub_re, Complex.zero_re] at h
    rw [show ((ν : ℂ) - m + 1) = (((ν : ℝ) - m + 1 : ℝ) : ℂ) by push_cast; ring,
      show (2 * (ν : ℂ) + 1) * x = (((2 * (ν : ℝ) + 1) * x : ℝ) : ℂ) by push_cast; ring,
      show ((ν : ℂ) + m) = (((ν : ℝ) + m : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at h
    linarith
  · simp only [mul_zero, add_zero, Complex.sub_re, Complex.zero_re] at h
    rw [show ((ν : ℂ) - m + 1) = (((ν : ℝ) - m + 1 : ℝ) : ℂ) by push_cast; ring,
      show (2 * (ν : ℂ) + 1) * x = (((2 * (ν : ℝ) + 1) * x : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul] at h
    linarith

/-- `P_m^{(m)}` is a nonzero constant. -/
theorem p2y_D_self (m : ℕ) : ∃ c : ℝ, c ≠ 0 ∧ ∀ x : ℝ, (legInt_D m m x).re = c := by
  set q := legendrePolyR m with hq
  have hf : OrthogonalPolynomials.legendrePolyP m =
      fun z => ((legendrePolyR m).map ofRealHom).eval z := funext (legendrePolyP_eq_eval m)
  have hD : ∀ x : ℝ, (legInt_D m m x).re = (Polynomial.derivative^[m] q).eval x := by
    intro x
    rw [legInt_D, hf, iteratedDeriv_eval_polynomial, Polynomial.iterate_derivative_map]
    dsimp only
    rw [eval_ofReal_map_ofRealHom, ofReal_re]
  have hlin : (Polynomial.C (1 / 2 : ℝ) * (1 - Polynomial.X)).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul (by norm_num)]
    rw [show (1 : Polynomial ℝ) - Polynomial.X = -(Polynomial.X - Polynomial.C 1) by simp,
      Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have hdeg : q.natDegree = m := by
    rw [hq, legendrePolyR, Polynomial.natDegree_comp, hlin, mul_one,
      Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℝ)),
      Polynomial.natDegree_shiftedLegendre]
  have hq0 : q ≠ 0 := by
    intro h
    have : (Polynomial.shiftedLegendre m).map (Int.castRingHom ℝ) ≠ 0 := by
      rw [Ne, Polynomial.map_eq_zero_iff (RingHom.injective_int (Int.castRingHom ℝ))]
      intro h0
      have := Polynomial.degree_shiftedLegendre m
      rw [h0, Polynomial.degree_zero] at this
      exact WithBot.bot_ne_coe this
    rw [hq, legendrePolyR, Polynomial.comp_eq_zero_iff] at h
    rcases h with h | ⟨_, h⟩
    · exact this h
    · have h' := congrArg Polynomial.natDegree h
      rw [hlin, Polynomial.natDegree_C] at h'
      exact one_ne_zero h'
  refine ⟨(Polynomial.derivative^[m] q).coeff 0, ?_, fun x => ?_⟩
  · rw [Polynomial.coeff_iterate_derivative, zero_add, Nat.descFactorial_self, nsmul_eq_mul]
    refine mul_ne_zero (by exact_mod_cast m.factorial_ne_zero) ?_
    rw [← hdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq0
  · rw [hD]
    have hle : (Polynomial.derivative^[m] q).natDegree ≤ 0 :=
      (Polynomial.natDegree_iterate_derivative q m).trans (by omega)
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_le_zero hle]
    rw [Polynomial.eval_C]


/-- **Ferrers moments determine the monomial moments**: if `∫ (1-x²)^m H P_ν^{(m)} = 0` for every
`ν ≥ m`, then `∫ (1-x²)^m H x^i = 0` for every `i`. -/
theorem p2y_moments_of_ferrers {H : ℝ → ℝ} (hH : ContinuousOn H (Icc (-1) 1)) (m : ℕ)
    (h : ∀ ν : ℕ, m ≤ ν → ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x * (legInt_D ν m x).re = 0) :
    ∀ i : ℕ, ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x * x ^ i = 0 := by
  have hc : ∀ (i ν : ℕ), ContinuousOn (fun x : ℝ => (1 - x ^ 2) ^ m * H x * x ^ i *
      (legInt_D ν m x).re) (Icc (-1) 1) := fun i ν =>
    (((by fun_prop : Continuous fun x : ℝ => (1 - x ^ 2) ^ m).continuousOn.mul hH).mul
      (continuous_pow i).continuousOn).mul
      (Complex.continuous_re.comp (legInt_cont_D ν m)).continuousOn
  have hi : ∀ (i ν : ℕ), IntervalIntegrable (fun x : ℝ => (1 - x ^ 2) ^ m * H x * x ^ i *
      (legInt_D ν m x).re) volume (-1) 1 := fun i ν =>
    (hc i ν).intervalIntegrable_of_Icc (by norm_num)
  have key : ∀ i : ℕ, ∀ ν : ℕ, m ≤ ν →
      ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x * x ^ i * (legInt_D ν m x).re = 0 := by
    intro i
    induction i with
    | zero =>
      intro ν hν
      simpa using h ν hν
    | succ i ih =>
      intro ν hν
      have h2 : (2 * (ν : ℝ) + 1) ≠ 0 := by positivity
      have e : (2 * (ν : ℝ) + 1) *
          ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x * x ^ (i + 1) * (legInt_D ν m x).re =
          ((ν : ℝ) - m + 1) *
            (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x * x ^ i * (legInt_D (ν + 1) m x).re) +
          ((ν : ℝ) + m) * (if m < ν then
            ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * H x * x ^ i * (legInt_D (ν - 1) m x).re
            else 0) := by
        rw [← intervalIntegral.integral_const_mul]
        split_ifs with hm
        · rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
            ← intervalIntegral.integral_add ((hi i _).const_mul _) ((hi i _).const_mul _)]
          apply p2y_integral_congr_Ioo
          intro x hx
          have hr := p2y_D_rec m ν hν hx
          simp only [hm, ↓reduceIte] at hr
          linear_combination (1 - x ^ 2) ^ m * H x * x ^ i * hr
        · rw [mul_zero, add_zero, ← intervalIntegral.integral_const_mul]
          apply p2y_integral_congr_Ioo
          intro x hx
          have hr := p2y_D_rec m ν hν hx
          simp only [hm, ↓reduceIte] at hr
          linear_combination (1 - x ^ 2) ^ m * H x * x ^ i * hr
      rw [ih (ν + 1) (by omega)] at e
      split_ifs at e with hm
      · rw [ih (ν - 1) (by omega)] at e
        simpa [h2] using e
      · simpa [h2] using e
  intro i
  obtain ⟨c, hc0, hcD⟩ := p2y_D_self m
  have := key i m le_rfl
  simp only [hcD] at this
  rw [intervalIntegral.integral_mul_const] at this
  exact (mul_eq_zero.mp this).resolve_right hc0

/-- `P_N^{(m)}(x)` is real for real `x`. -/
theorem p2y_legInt_D_real (N m : ℕ) (x : ℝ) :
    (legInt_D N m x) = ((legInt_D N m x).re : ℂ) := by
  have hf : OrthogonalPolynomials.legendrePolyP N =
      fun z => ((legendrePolyR N).map ofRealHom).eval z := funext (legendrePolyP_eq_eval N)
  rw [legInt_D, hf, iteratedDeriv_eval_polynomial, Polynomial.iterate_derivative_map]
  dsimp only
  rw [eval_ofReal_map_ofRealHom]
  simp

/-- Parity of `P_ν^{(m)}`: `P_ν^{(m)}(-x) = (-1)^{ν+m} P_ν^{(m)}(x)`. -/
theorem p2y_D_neg (ν m : ℕ) (x : ℝ) :
    (legInt_D ν m ((-x : ℝ) : ℂ)).re = (-1) ^ (ν + m) * (legInt_D ν m x).re := by
  have hP : OrthogonalPolynomials.legendrePolyP ν =
      fun z => (-1 : ℂ) ^ ν * OrthogonalPolynomials.legendrePolyP ν (-z) := by
    funext z
    have h := OrthogonalPolynomials.jacobi_reflection (α := 0) (β := 0) (by norm_num)
      (by norm_num) ν (-z)
    rw [neg_neg] at h
    change OrthogonalPolynomials.jacobiPolyP 0 0 ν z =
      (-1) ^ ν * OrthogonalPolynomials.jacobiPolyP 0 0 ν (-z)
    rw [h]
  have hD : iteratedDeriv m (OrthogonalPolynomials.legendrePolyP ν) (-(x : ℂ)) =
      (-1 : ℂ) ^ (ν + m) * iteratedDeriv m (OrthogonalPolynomials.legendrePolyP ν) (x : ℂ) := by
    conv_lhs => rw [hP]
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_neg, neg_neg, smul_eq_mul]
    ring
  have hr := p2y_legInt_D_real ν m x
  simp only [legInt_D] at hr
  rw [Complex.ofReal_neg, legInt_D, hD, hr,
    show ((-1 : ℂ) ^ (ν + m)) = (((-1 : ℝ) ^ (ν + m) : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re]

/-- **Orthogonality** of `P_ν^{(m)}` with weight `(1-x²)^m` on `[-1, 1]`, with the norm
`2(ν+m)!/((2ν+1)(ν-m)!)`. -/
theorem p2y_D_orth {m ν : ℕ} (hν : m ≤ ν) (μ : ℕ) :
    ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (legInt_D ν m x).re * (legInt_D μ m x).re =
      if ν = μ then 2 * ((ν + m).factorial : ℝ) / ((2 * ν + 1) * (ν - m).factorial) else 0 := by
  have e : legInt_I m ν μ = ((∫ x in (-1 : ℝ)..1,
      (1 - x ^ 2) ^ m * (legInt_D ν m x).re * (legInt_D μ m x).re : ℝ) : ℂ) := by
    rw [legInt_I, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [p2y_legInt_D_real ν m x, p2y_legInt_D_real μ m x]
    push_cast
    simp [legInt_D]
  have h := legInt_I_eq m ν μ
  rw [e] at h
  apply Complex.ofReal_injective
  rw [h]
  split_ifs with hνμ
  · subst hνμ
    have hp := legInt_prod_factorial hν
    have hf : ((ν - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (ν - m).factorial_ne_zero
    have h2 : (2 * (ν : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < 2 * ν + 1 := by positivity
      exact_mod_cast this.ne'
    push_cast
    rw [← hp]
    field_simp
  · simp

/-- **An exponential bound** for `P_ν^{(m)}` on `[-1, 1]`: `|P_ν^{(m)}(x)| ≤ C (2m+3)^{ν-m}`. -/
theorem p2y_D_bound (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℕ, m ≤ ν → ∀ x ∈ Icc (-1 : ℝ) 1,
    |(legInt_D ν m x).re| ≤ C * (2 * (m : ℝ) + 3) ^ (ν - m) := by
  obtain ⟨c, -, hc⟩ := p2y_D_self m
  refine ⟨|c|, abs_nonneg c, ?_⟩
  set L : ℝ := 2 * (m : ℝ) + 3 with hL
  have hL0 : 0 ≤ L := by positivity
  have key : ∀ t : ℕ, ∀ s ≤ t, ∀ x ∈ Ioo (-1 : ℝ) 1, |(legInt_D (m + s) m x).re| ≤ |c| * L ^ s := by
    intro t
    induction t with
    | zero =>
      intro s hs x _
      obtain rfl : s = 0 := by omega
      simp [hc]
    | succ t ih =>
      intro s hs x hx
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · exact ih s (by omega) x hx
      obtain rfl : s = t + 1 := by omega
      have hr := p2y_D_rec m (m + t) (by omega) hx
      have hx1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
      have h0 := ih t le_rfl x hx
      rw [show m + t + 1 = m + (t + 1) by ring] at hr
      have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
      have hcoef : ((m + t : ℕ) : ℝ) - m + 1 = (t : ℝ) + 1 := by push_cast; ring
      rw [hcoef] at hr
      have hPt : 0 ≤ |c| * L ^ t := by positivity
      rcases Nat.eq_zero_or_pos t with h0t | h0t
      · subst h0t
        simp only [lt_irrefl, ↓reduceIte, mul_zero, add_zero, Nat.cast_zero,
          zero_add, one_mul, pow_one] at hr h0 ⊢
        rw [← hr]
        have : |(2 * (m : ℝ) + 1) * x * (legInt_D m m x).re| ≤ (2 * (m : ℝ) + 1) * |c| := by
          rw [abs_mul, abs_mul, hc, abs_of_pos (by positivity : (0 : ℝ) < 2 * m + 1)]
          nlinarith [mul_le_mul_of_nonneg_left hx1
            (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * m + 1) (abs_nonneg c))]
        simp only [pow_zero, mul_one] at h0
        calc _ ≤ (2 * (m : ℝ) + 1) * |c| := by simpa [Nat.cast_add] using this
          _ ≤ |c| * L := by rw [hL]; nlinarith [abs_nonneg c]
      · have hm : m < m + t := by omega
        simp only [hm, ↓reduceIte] at hr
        have h1 := ih (t - 1) (by omega) x hx
        rw [show m + (t - 1) = m + t - 1 by omega] at h1
        obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at h1
        have e : (legInt_D (m + (u + 1 + 1)) m x).re = ((2 * ((m + (u + 1) : ℕ) : ℝ) + 1) * x *
            (legInt_D (m + (u + 1)) m x).re - (((m + (u + 1) : ℕ) : ℝ) + m) *
              (legInt_D (m + (u + 1) - 1) m x).re) / ((u + 1 : ℕ) + 1 : ℝ) := by
          rw [eq_div_iff ht1.ne']; linarith
        rw [e, abs_div, abs_of_pos ht1, div_le_iff₀ ht1]
        have hb1 : |(2 * ((m + (u + 1) : ℕ) : ℝ) + 1) * x * (legInt_D (m + (u + 1)) m x).re| ≤
            (2 * ((m + (u + 1) : ℕ) : ℝ) + 1) * (|c| * L ^ (u + 1)) := by
          rw [abs_mul, abs_mul, abs_of_pos (by positivity), mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc |x| * |(legInt_D (m + (u + 1)) m x).re|
              ≤ 1 * |(legInt_D (m + (u + 1)) m x).re| :=
                mul_le_mul_of_nonneg_right hx1 (abs_nonneg _)
            _ ≤ _ := by rw [one_mul]; exact h0
        have hb2 : |(((m + (u + 1) : ℕ) : ℝ) + m) * (legInt_D (m + (u + 1) - 1) m x).re| ≤
            (((m + (u + 1) : ℕ) : ℝ) + m) * (|c| * L ^ u) := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        have hfin : (2 * ((m + (u + 1) : ℕ) : ℝ) + 1) * (|c| * L ^ (u + 1)) +
            (((m + (u + 1) : ℕ) : ℝ) + m) * (|c| * L ^ u) ≤
              |c| * L ^ (u + 1 + 1) * (((u + 1 : ℕ) : ℝ) + 1) := by
          have hPu : 0 ≤ |c| * L ^ u := by positivity
          have eq1 : |c| * L ^ (u + 1) = (|c| * L ^ u) * L := by ring
          have eq2 : |c| * L ^ (u + 1 + 1) = (|c| * L ^ u) * L ^ 2 := by ring
          rw [eq1, eq2]
          push_cast
          have hineq : (2 * ((m : ℝ) + (u + 1)) + 1) * L + ((m : ℝ) + (u + 1) + m) ≤
              L ^ 2 * ((u : ℝ) + 1 + 1) := by
            have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg u
            have ha : (0 : ℝ) ≤ m := Nat.cast_nonneg m
            rw [hL]
            nlinarith [mul_nonneg (mul_nonneg ha ha) hu, mul_nonneg ha hu]
          nlinarith [mul_le_mul_of_nonneg_left hineq hPu]
        calc _ ≤ _ := abs_sub _ _
          _ ≤ _ := add_le_add hb1 hb2
          _ ≤ _ := hfin
  -- extend from `(-1, 1)` to `[-1, 1]` by continuity
  intro ν hν x hx
  have hcl : closure (Ioo (-1 : ℝ) 1) ⊆ {x : ℝ | |(legInt_D ν m x).re| ≤ |c| * L ^ (ν - m)} := by
    refine (isClosed_le ?_ continuous_const).closure_subset_iff.mpr ?_
    · exact (Complex.continuous_re.comp (legInt_cont_D ν m)).abs
    · intro y hy
      have := key (ν - m) (ν - m) le_rfl y hy
      rwa [show m + (ν - m) = ν by omega] at this
  rw [closure_Ioo (by norm_num)] at hcl
  exact hcl hx

/-- **The expansion theorem** in the functions `P_ν^{(m)}`, `ν = ν₀ + 2j`: a continuous `G` on
`[-1, 1]` whose coefficients `b_μ = ∫ (1-x²)^m G P_μ^{(m)}` vanish for the other parity, and whose
series `∑ c_ν b_ν P_ν^{(m)}` (`c_ν = (2ν+1)(ν-m)!/(2(ν+m)!)`) is dominated by a summable
sequence on `[-1, 1]`, is the sum of that series on `(-1, 1)`. -/
theorem p2y_hasSum_expansion {G : ℝ → ℝ} (hG : ContinuousOn G (Icc (-1) 1)) {m ν₀ : ℕ}
    (hν₀ : m ≤ ν₀)
    (hpar : ∀ μ : ℕ, m ≤ μ → (∀ j : ℕ, μ ≠ ν₀ + 2 * j) →
      ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * G x * (legInt_D μ m x).re = 0)
    {u : ℕ → ℝ} (hu : Summable u)
    (hb : ∀ j : ℕ, ∀ x ∈ Icc (-1 : ℝ) 1,
      |(2 * ((ν₀ + 2 * j : ℕ) : ℝ) + 1) * ((ν₀ + 2 * j - m).factorial : ℝ) /
          (2 * ((ν₀ + 2 * j + m).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * G y * (legInt_D (ν₀ + 2 * j) m y).re) *
          (legInt_D (ν₀ + 2 * j) m x).re| ≤ u j) :
    ∀ x ∈ Ioo (-1 : ℝ) 1, HasSum (fun j : ℕ =>
      (2 * ((ν₀ + 2 * j : ℕ) : ℝ) + 1) * ((ν₀ + 2 * j - m).factorial : ℝ) /
          (2 * ((ν₀ + 2 * j + m).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * G y * (legInt_D (ν₀ + 2 * j) m y).re) *
          (legInt_D (ν₀ + 2 * j) m x).re) (G x) := by
  set c : ℕ → ℝ := fun j => (2 * ((ν₀ + 2 * j : ℕ) : ℝ) + 1) *
    ((ν₀ + 2 * j - m).factorial : ℝ) / (2 * ((ν₀ + 2 * j + m).factorial : ℝ)) with hc
  set b : ℕ → ℝ := fun μ => ∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * G y * (legInt_D μ m y).re
    with hbdef
  set f : ℕ → ℝ → ℝ := fun j x => c j * b (ν₀ + 2 * j) * (legInt_D (ν₀ + 2 * j) m x).re with hf
  have hD : ∀ μ : ℕ, Continuous fun x : ℝ => (legInt_D μ m x).re := fun μ =>
    Complex.continuous_re.comp (legInt_cont_D μ m)
  have hw : Continuous fun x : ℝ => (1 - x ^ 2) ^ m := by fun_prop
  have hsum : ∀ x ∈ Icc (-1 : ℝ) 1, Summable fun j => f j x := fun x hx =>
    Summable.of_norm_bounded hu fun j => by rw [Real.norm_eq_abs]; exact hb j x hx
  set S : ℝ → ℝ := fun x => ∑' j, f j x with hS
  have hSc : ContinuousOn S (Icc (-1) 1) :=
    continuousOn_tsum (fun j => (continuous_const.mul (hD _)).continuousOn) hu
      fun j x hx => by rw [Real.norm_eq_abs]; exact hb j x hx
  have hH : ContinuousOn (fun x => G x - S x) (Icc (-1) 1) := hG.sub hSc
  have horth : ∀ μ : ℕ, m ≤ μ →
      ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (G x - S x) * (legInt_D μ m x).re = 0 := by
    intro μ hμ
    obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn
      ((hw.mul (hD μ)).continuousOn (s := Icc (-1 : ℝ) 1))).isBounded.exists_norm_le
    have hB' : ∀ x ∈ Icc (-1 : ℝ) 1, |(1 - x ^ 2) ^ m * (legInt_D μ m x).re| ≤ B :=
      fun x hx => hB _ ⟨x, hx, rfl⟩
    have hint : HasSum (fun j => ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * f j x *
        (legInt_D μ m x).re) (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * S x * (legInt_D μ m x).re) := by
      refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun j _ => u j * B)
        (fun j => ((hw.mul (continuous_const.mul (hD _))).mul (hD μ)).aestronglyMeasurable)
        (fun j => ?_) ?_ intervalIntegrable_const ?_
      · refine Filter.Eventually.of_forall fun x hx => ?_
        rw [uIoc_of_le (by norm_num)] at hx
        have hx' : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
        rw [Real.norm_eq_abs, show (1 - x ^ 2) ^ m * f j x * (legInt_D μ m x).re =
          f j x * ((1 - x ^ 2) ^ m * (legInt_D μ m x).re) by ring, abs_mul]
        exact mul_le_mul (hb j x hx') (hB' x hx') (abs_nonneg _)
          ((abs_nonneg _).trans (hb j x hx'))
      · exact Filter.Eventually.of_forall fun x _ => hu.mul_right B
      · refine Filter.Eventually.of_forall fun x hx => ?_
        rw [uIoc_of_le (by norm_num)] at hx
        have h := ((hsum x ⟨hx.1.le, hx.2⟩).hasSum.mul_left ((1 - x ^ 2) ^ m)).mul_right
          (legInt_D μ m x).re
        simpa only [hS] using h
    have hterm : ∀ j, ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * f j x * (legInt_D μ m x).re =
        if ν₀ + 2 * j = μ then b μ else 0 := by
      intro j
      have e : (fun x : ℝ => (1 - x ^ 2) ^ m * f j x * (legInt_D μ m x).re) = fun x : ℝ =>
          c j * b (ν₀ + 2 * j) * ((1 - x ^ 2) ^ m * (legInt_D (ν₀ + 2 * j) m x).re *
            (legInt_D μ m x).re) := by
        funext x; simp only [hf]; ring
      rw [e, intervalIntegral.integral_const_mul, p2y_D_orth (by omega) μ]
      split_ifs with h
      · subst h
        have hf1 : ((ν₀ + 2 * j - m).factorial : ℝ) ≠ 0 := by positivity
        have hf2 : ((ν₀ + 2 * j + m).factorial : ℝ) ≠ 0 := by positivity
        have h2 : (2 * ((ν₀ + 2 * j : ℕ) : ℝ) + 1) ≠ 0 := by positivity
        simp only [hc]
        field_simp
      · rw [mul_zero]
    simp_rw [hterm] at hint
    have hSμ : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * S x * (legInt_D μ m x).re =
        b μ := by
      by_cases hex : ∃ j, μ = ν₀ + 2 * j
      · obtain ⟨j0, rfl⟩ := hex
        have h1 : HasSum (fun j => if ν₀ + 2 * j = ν₀ + 2 * j0 then b (ν₀ + 2 * j0) else 0)
            (b (ν₀ + 2 * j0)) := by
          convert hasSum_ite_eq j0 (b (ν₀ + 2 * j0)) using 2 with j
          by_cases hj : j = j0
          · simp [hj]
          · simp [hj]
        exact hint.unique h1
      · simp only [not_exists] at hex
        have h0 : ∀ j, (if ν₀ + 2 * j = μ then b μ else 0) = 0 := fun j => by
          simp only [show ν₀ + 2 * j ≠ μ from fun h => hex j h.symm, ↓reduceIte]
        simp_rw [h0] at hint
        rw [hint.unique hasSum_zero]
        exact (hpar μ hμ hex).symm
    have e2 : (fun x : ℝ => (1 - x ^ 2) ^ m * (G x - S x) * (legInt_D μ m x).re) = fun x : ℝ =>
        (1 - x ^ 2) ^ m * G x * (legInt_D μ m x).re -
          (1 - x ^ 2) ^ m * S x * (legInt_D μ m x).re := by funext x; ring
    rw [e2, intervalIntegral.integral_sub, hSμ]
    · simp [hbdef]
    · exact ((hw.continuousOn.mul hG).mul (hD μ).continuousOn).intervalIntegrable_of_Icc
        (by norm_num)
    · exact ((hw.continuousOn.mul hSc).mul (hD μ).continuousOn).intervalIntegrable_of_Icc
        (by norm_num)
  have hz := p2y_eq_zero_of_moments hH m (p2y_moments_of_ferrers hH m horth)
  intro x hx
  have hGS : G x = S x := sub_eq_zero.mp (hz x hx)
  rw [hGS]
  exact (hsum x (Ioo_subset_Icc_self hx)).hasSum

end DLMF.Spheroidal
