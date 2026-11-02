/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.GeneralizedContours

/-!
# The finite-part Reid functions for positive `p`

For integer `p ≥ 1` the ray functions `B_k(z, p)` of DLMF 9.13.27 are Hadamard finite parts.
Writing `c_j(z)` for the Taylor coefficients of `e^{zt - t³/3}`, the finite part at angle `0`
is the unit-ray integral plus the series `∑_{j ≠ p - 1} c_j(z)/(j + 1 - p)`; the closed
contour gives `B₀(z, p) = c_{p-1}(z)`. Termwise differentiation shows that `∂_z` lowers `p` by
one for every integer `p`, and the recurrence `j c_j = z c_{j-1} - c_{j-3}`, read off from
the difference equation of `B₀`, gives the inhomogeneous difference and differential equations.

## Main results

* `reidAiryB0_natCast_add_one`: `B₀(z, m + 1) = c_m(z)`.
* `hasDerivAt_reidAiryB`: `∂_z B_k(z, p) = B_k(z, p - 1)` for every integer `p`.
* `reidAiryB_difference_finitePart`: `B_k(z, p-3) - z B_k(z, p-1) + (p-1) B_k(z, p) = B₀(z, p)`.
* `reidAiryB_finitePart_ode`: `w''' - z w' + (p - 1) w = c_{p-1}(z)` for `p ≥ 1`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Real Topology Nat

namespace DLMF.Airy

/-- For `p = m + 1 ≥ 1`, `B₀(z, p)` is the residue `c_m(z)` of `t^{-p} e^{zt-t³/3}`. -/
theorem reidAiryB0_natCast_add_one (z : ℂ) (m : ℕ) :
    reidAiryB0 z ((m : ℤ) + 1) = reidTaylorCoeff z m := by
  obtain ⟨G, hG⟩ := (differentiable_reidTaylorTail z (m + 1)).isExactOn_univ
  have hG' : ∀ u, HasDerivAt G (reidTaylorTail z (m + 1) u) u := fun u => hG u (mem_univ u)
  have h := reidArc_finitePart z m hG' 0 (2 * π)
  have hpi : (2 * π * I : ℂ) ≠ 0 := by
    have := Real.pi_pos; simp [Real.pi_ne_zero, I_ne_zero]
  have he : ∀ j : ℕ, exp (((2 * π : ℝ) : ℂ) * I * ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ))) = 1 := by
    intro j
    rw [show ((2 * π : ℝ) : ℂ) * I * ((j : ℂ) + 1 - ((m + 1 : ℕ) : ℂ)) =
      (((j : ℤ) - m : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
    exact exp_int_mul_two_pi_mul_I _
  have h2 : exp (((2 * π : ℝ) : ℂ) * I) = 1 := by push_cast; exact exp_two_pi_mul_I
  simp only [reidFinitePartH, he, h2, ofReal_zero, zero_mul, exp_zero] at h
  rw [reidAiryB0, show (((m : ℤ) + 1 : ℤ) : ℂ) = ((m + 1 : ℕ) : ℂ) by push_cast; ring, h]
  field_simp
  push_cast
  ring

/-- The `z`-derivative of `B₀(z, q)` is `B₀(z, q - 1)`. -/
theorem hasDerivAt_reidAiryB0 (q : ℤ) (z : ℂ) :
    HasDerivAt (fun z => reidAiryB0 z q) (reidAiryB0 z (q - 1)) z := by
  have h := (hasDerivAt_reidArc (q : ℂ) 0 (2 * π) z).div_const (2 * π * I)
  simp only [reidAiryB0]
  push_cast
  exact h

/-- A geometric bound for the Reid Taylor coefficients. -/
private lemma norm_reidTaylorCoeff_le (z : ℂ) (j : ℕ) :
    ‖reidTaylorCoeff z j‖ ≤ (j + 1) * Real.exp (2 * ‖z‖ + 8 / 3) * (1 / 2) ^ j := by
  unfold reidTaylorCoeff
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (j / 3 + 1), ‖(-1 / 3 : ℂ) ^ k * z ^ (j - 3 * k) /
      (k.factorial * (j - 3 * k).factorial)‖ ≤ Real.exp (2 * ‖z‖ + 8 / 3) * (1 / 2) ^ j := by
    intro k hk
    have hk3 : 3 * k ≤ j := by have := Finset.mem_range.mp hk; omega
    obtain ⟨l, rfl⟩ : ∃ l, j = 3 * k + l := ⟨j - 3 * k, by omega⟩
    rw [show 3 * k + l - 3 * k = l by omega]
    have h1 := Real.pow_div_factorial_le_exp (8 / 3) (by norm_num) k
    have h2 := Real.pow_div_factorial_le_exp (2 * ‖z‖) (by positivity) l
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_mul, Complex.norm_natCast,
      Complex.norm_natCast, norm_div, norm_neg, norm_one, Complex.norm_ofNat]
    have hk0 : (0 : ℝ) < k ! := by exact_mod_cast k.factorial_pos
    have hl0 : (0 : ℝ) < l ! := by exact_mod_cast l.factorial_pos
    have e1 : (8 / 3 : ℝ) ^ k * ((1 / 2) ^ 3) ^ k = (1 / 3) ^ k := by
      rw [← mul_pow]; norm_num
    have e2 : (2 : ℝ) ^ l * (1 / 2) ^ l = 1 := by rw [← mul_pow]; norm_num
    calc (1 / 3 : ℝ) ^ k * ‖z‖ ^ l / (k ! * l !)
        = ((8 / 3 : ℝ) ^ k * ((1 / 2) ^ 3) ^ k) * ((2 : ℝ) ^ l * (1 / 2) ^ l) * ‖z‖ ^ l /
            (k ! * l !) := by rw [e1, e2]; ring
      _ = ((8 / 3) ^ k / k !) * ((2 * ‖z‖) ^ l / l !) * (1 / 2) ^ (3 * k + l) := by
          rw [mul_pow, pow_add, pow_mul]; ring
      _ ≤ Real.exp (8 / 3) * Real.exp (2 * ‖z‖) * (1 / 2) ^ (3 * k + l) := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm (8 / 3 : ℝ)]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : ((j / 3 + 1 : ℕ) : ℝ) ≤ j + 1 := by
    have : j / 3 ≤ j := Nat.div_le_self _ _
    exact_mod_cast Nat.add_le_add_right this 1
  have hp : 0 ≤ Real.exp (2 * ‖z‖ + 8 / 3) * (1 / 2 : ℝ) ^ j := by positivity
  nlinarith

/-- A geometric bound for `B₀(z, q)` in `q`. -/
private lemma norm_reidAiryB0_le (z : ℂ) (q : ℤ) :
    ‖reidAiryB0 z q‖ ≤
      2 * Real.exp (2 * ‖z‖ + 8 / 3) * (((q.natAbs : ℝ) + 1) * (1 / 2) ^ q.natAbs) := by
  rcases le_or_gt q 0 with hq | hq
  · rw [reidAiryB0_of_nonpos z hq, norm_zero]; positivity
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = (m : ℤ) + 1 := ⟨q.toNat - 1, by omega⟩
    rw [reidAiryB0_natCast_add_one]
    have hn : ((m : ℤ) + 1).natAbs = m + 1 := by omega
    rw [hn]
    refine (norm_reidTaylorCoeff_le z m).trans ?_
    have hp : 0 ≤ Real.exp (2 * ‖z‖ + 8 / 3) * (1 / 2 : ℝ) ^ m := by positivity
    push_cast
    rw [pow_succ]
    nlinarith

/-- Summability of the geometric majorant over `ℤ`. -/
private lemma summable_natAbs_geom :
    Summable (fun q : ℤ => ((q.natAbs : ℝ) + 1) * (1 / 2 : ℝ) ^ q.natAbs) := by
  have h1 : Summable (fun n : ℕ => ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) := by
    have ha := summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num [Real.norm_eq_abs, abs_of_pos])
    have hb := summable_geometric_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine (ha.add hb).congr fun n => ?_
    simp; ring
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine h1.congr fun n => ?_
    simp
  · have := (summable_nat_add_iff 1).mpr h1
    refine this.congr fun n => ?_
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    simp only [this]


/-- `‖(q - p)⁻¹‖ ≤ 1` for integers `q, p`. -/
private lemma norm_int_sub_inv_le (q p : ℤ) : ‖((q : ℂ) - p)⁻¹‖ ≤ 1 := by
  rcases eq_or_ne q p with rfl | h
  · simp
  · rw [norm_inv]
    apply inv_le_one_of_one_le₀
    rw [show (q : ℂ) - p = ((q - p : ℤ) : ℂ) by push_cast; ring, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h)

/-- The finite-part series `∑_q B₀(z, q) (q - p)⁻¹`. -/
private def reidSeries (z : ℂ) (p : ℤ) : ℂ :=
  ∑' q : ℤ, reidAiryB0 z q * ((q : ℂ) - p)⁻¹

/-- A majorant for the terms of the finite-part series. -/
private lemma norm_reidSeries_term_le (z : ℂ) (p q : ℤ) :
    ‖reidAiryB0 z q * ((q : ℂ) - p)⁻¹‖ ≤
      2 * Real.exp (2 * ‖z‖ + 8 / 3) * (((q.natAbs : ℝ) + 1) * (1 / 2) ^ q.natAbs) := by
  rw [norm_mul]
  calc _ ≤ ‖reidAiryB0 z q‖ * 1 := by gcongr; exact norm_int_sub_inv_le q p
    _ ≤ _ := by rw [mul_one]; exact norm_reidAiryB0_le z q

/-- The finite-part series converges absolutely. -/
private lemma summable_reidSeries (z : ℂ) (p : ℤ) :
    Summable (fun q : ℤ => reidAiryB0 z q * ((q : ℂ) - p)⁻¹) :=
  .of_norm_bounded (summable_natAbs_geom.mul_left _) (norm_reidSeries_term_le z p)

/-- Shifting the summation index. -/
private lemma reidSeries_shift (z : ℂ) (p : ℤ) (s : ℤ) :
    reidSeries z (p - s) = ∑' q : ℤ, reidAiryB0 z (q - s) * ((q : ℂ) - p)⁻¹ := by
  unfold reidSeries
  rw [← (Equiv.subRight s).tsum_eq]
  congr 1; funext q
  simp only [Equiv.subRight_apply]
  push_cast; ring_nf

/-- The shifted finite-part series converges. -/
private lemma summable_reidSeries_shift (z : ℂ) (p : ℤ) (s : ℤ) :
    Summable (fun q : ℤ => reidAiryB0 z (q - s) * ((q : ℂ) - p)⁻¹) := by
  have h := (Equiv.subRight s).summable_iff.mpr (summable_reidSeries z (p - s))
  refine h.congr fun q => ?_
  simp only [Function.comp_apply, Equiv.subRight_apply]
  push_cast; ring_nf

/-- Termwise differentiation: the `z`-derivative lowers `p` by one. -/
private lemma hasDerivAt_reidSeries (p : ℤ) (z₀ : ℂ) :
    HasDerivAt (fun z => reidSeries z p) (reidSeries z₀ (p - 1)) z₀ := by
  set K := 2 * Real.exp (2 * (‖z₀‖ + 1) + 8 / 3)
  have hu : Summable (fun q : ℤ =>
      K * ((((q - 1 : ℤ).natAbs : ℝ) + 1) * (1 / 2) ^ (q - 1 : ℤ).natAbs)) := by
    have := (Equiv.subRight (1 : ℤ)).summable_iff.mpr (summable_natAbs_geom.mul_left K)
    exact this
  have h := hasDerivAt_tsum_of_isPreconnected
    (g := fun (q : ℤ) z => reidAiryB0 z q * ((q : ℂ) - p)⁻¹)
    (g' := fun (q : ℤ) z => reidAiryB0 z (q - 1) * ((q : ℂ) - p)⁻¹) hu Metric.isOpen_ball
    (convex_ball z₀ 1).isPreconnected (fun q y _ => (hasDerivAt_reidAiryB0 q y).mul_const _)
    (fun q y hy => by
      refine (norm_mul_le _ _).trans ?_
      have hy' : ‖y‖ ≤ ‖z₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' y z₀
        rw [Metric.mem_ball, dist_eq_norm] at hy; linarith
      calc _ ≤ ‖reidAiryB0 y (q - 1)‖ * 1 := by gcongr; exact norm_int_sub_inv_le q p
        _ ≤ _ := by
          rw [mul_one]
          refine (norm_reidAiryB0_le y (q - 1)).trans ?_
          exact mul_le_mul_of_nonneg_right (by simp only [K]; gcongr) (by positivity))
    (Metric.mem_ball_self one_pos) (summable_reidSeries z₀ p) (Metric.mem_ball_self one_pos)
  rw [reidSeries_shift z₀ p 1]
  exact h

/-- A `ℤ`-indexed series supported on the positive integers. -/
private lemma hasSum_int_of_nat_succ {f : ℤ → ℂ} (hf : ∀ q ≤ 0, f q = 0) {a : ℂ}
    (h : HasSum (fun j : ℕ => f ((j : ℤ) + 1)) a) : HasSum f a := by
  have h1 : HasSum (fun n : ℕ => f n) a := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [hf 0 le_rfl] using h
  have h2 : HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) 0 := by
    have : (fun n : ℕ => f (-((n : ℤ) + 1))) = fun _ => 0 := by
      funext n; exact hf _ (by omega)
    rw [this]; exact hasSum_zero
  simpa using h1.of_nat_of_neg_add_one h2

/-- `∑_q B₀(z, q) = e^{z - 1/3}`. -/
private lemma hasSum_reidAiryB0 (z : ℂ) :
    HasSum (fun q : ℤ => reidAiryB0 z q) (exp (z - 1 / 3)) := by
  refine hasSum_int_of_nat_succ (fun q hq => reidAiryB0_of_nonpos z hq) ?_
  have h := hasSum_reidTaylorCoeff z 1
  simp only [one_pow, mul_one] at h
  norm_num at h
  simpa [reidAiryB0_natCast_add_one] using h

/-- The 9.13.32 combination of the finite-part series. -/
private lemma reidSeries_difference (z : ℂ) (p : ℤ) :
    reidSeries z (p - 3) - z * reidSeries z (p - 1) + ((p : ℂ) - 1) * reidSeries z p =
      reidAiryB0 z p - exp (z - 1 / 3) := by
  rw [reidSeries_shift z p 3, reidSeries_shift z p 1]
  have s3 := summable_reidSeries_shift z p 3
  have s1 := (summable_reidSeries_shift z p 1).mul_left z
  have s0 := (summable_reidSeries z p).mul_left ((p : ℂ) - 1)
  unfold reidSeries
  rw [← tsum_mul_left, ← tsum_mul_left, ← s3.tsum_sub s1, ← (s3.sub s1).tsum_add s0]
  have hS := ((hasSum_reidAiryB0 z).neg.add (hasSum_ite_eq p (reidAiryB0 z p)))
  rw [neg_add_eq_sub] at hS
  refine Eq.trans ?_ hS.tsum_eq
  congr 1; funext q
  have hrec := reidAiryB0_difference z q
  rcases eq_or_ne q p with rfl | hqp
  · simp
  · have hd : (q : ℂ) - p ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hqp
    simp only [hqp, ↓reduceIte]
    field_simp
    linear_combination hrec


/-- Termwise integration of a power series over `[0, 1]`. -/
private lemma integral_tsum_pow (a : ℕ → ℂ) (ha : Summable fun j => ‖a j‖) (n : ℕ) :
    ∫ t in (0 : ℝ)..1, ∑' j, a j * (t : ℂ) ^ (j + n) = ∑' j, a j / ((j : ℂ) + n + 1) := by
  have hint : ∀ j, ∫ t in (0 : ℝ)..1, a j * (t : ℂ) ^ (j + n) = a j / ((j : ℂ) + n + 1) := by
    intro j
    simp_rw [← ofReal_pow]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, integral_pow]
    push_cast; simp; field_simp
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [← integral_tsum_of_summable_integral_norm]
  · refine tsum_congr fun j => ?_
    rw [← intervalIntegral.integral_of_le zero_le_one, hint]
  · intro j
    exact (by fun_prop : Continuous fun t : ℝ => a j * (t : ℂ) ^ (j + n)).integrableOn_Ioc
  · refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun t => norm_nonneg _)
      (fun j => ?_) ha
    calc ∫ t in Ioc (0 : ℝ) 1, ‖a j * (t : ℂ) ^ (j + n)‖
        ≤ ∫ t in Ioc (0 : ℝ) 1, ‖a j‖ := by
          refine setIntegral_mono_on ?_ (by simp) measurableSet_Ioc fun t ht => ?_
          · exact (by fun_prop : Continuous fun t : ℝ =>
              ‖a j * (t : ℂ) ^ (j + n)‖).integrableOn_Ioc
          · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
            exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ ht.1.le ht.2)
      _ = ‖a j‖ := by simp


/-- Absolute summability of the Reid Taylor coefficients. -/
private lemma summable_norm_reidTaylorCoeff (z : ℂ) : Summable fun j => ‖reidTaylorCoeff z j‖ := by
  simpa using (hasSum_reidTaylorCoeff' z 1).1

/-- The series in its `ℕ`-indexed form. -/
private lemma reidSeries_eq_nat (z : ℂ) (p : ℤ) :
    reidSeries z p = ∑' j : ℕ, reidTaylorCoeff z j * ((j : ℂ) + 1 - p)⁻¹ := by
  have hs : Summable fun j : ℕ => reidTaylorCoeff z j * ((j : ℂ) + 1 - p)⁻¹ := by
    refine .of_norm_bounded (summable_norm_reidTaylorCoeff z) fun j => ?_
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    have := norm_int_sub_inv_le ((j : ℤ) + 1) p
    push_cast at this; exact this
  unfold reidSeries
  refine (hasSum_int_of_nat_succ (fun q hq => by rw [reidAiryB0_of_nonpos z hq, zero_mul])
    ?_).tsum_eq
  refine hs.hasSum.congr_fun fun j => ?_
  simp only [reidAiryB0_natCast_add_one]
  push_cast; ring_nf

/-- `B₀`'s ray function at angle `0`: a unit-ray integral plus the finite-part series. -/
private lemma reidAiryB_zero_eq (z : ℂ) (p : ℤ) :
    reidAiryB 0 z p = reidRay z p 0 1 + reidSeries z p := by
  have hc0 : exp (3 * (((0 : ℝ) : ℂ) * I)) = 1 := by simp
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = -(n : ℤ) := ⟨(-p).toNat, by omega⟩
    rw [reidAiryB_ordinary_ray 0 z hp]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul, zero_div]
    have hI0 := integrableOn_reidRay hc0 z ((-(n : ℤ) : ℤ) : ℂ) le_rfl (Or.inr (by simp))
    have hI1 := integrableOn_reidRay hc0 z ((-(n : ℤ) : ℤ) : ℂ) zero_le_one (Or.inl le_rfl)
    have hsplit := intervalIntegral.integral_interval_add_Ioi hI0 hI1
    unfold reidRay
    rw [← hsplit, add_comm]
    congr 1
    have hker : ∀ t ∈ Set.uIoc (0 : ℝ) 1, exp (((0 : ℝ) : ℂ) * I) *
        reidKernel z (((-(n : ℤ)) : ℤ) : ℂ) (log t + ((0 : ℝ) : ℂ) * I) =
          ∑' j, reidTaylorCoeff z j * (t : ℂ) ^ (j + n) := by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      rw [reidKernel_log_add hc0 z _ ht.1]
      have ht' : exp (log (t : ℂ)) = t := exp_log (ofReal_ne_zero.mpr ht.1.ne')
      simp_rw [pow_add, ← mul_assoc]
      rw [tsum_mul_right, (hasSum_reidTaylorCoeff z t).tsum_eq]
      push_cast
      simp only [zero_mul, add_zero, exp_zero, mul_one, one_mul, neg_neg]
      rw [add_sub_assoc, exp_add, exp_nat_mul, ht']
      ring
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ hker), integral_tsum_pow _
      (summable_norm_reidTaylorCoeff z) n, reidSeries_eq_nat]
    refine tsum_congr fun j => ?_
    push_cast; rw [div_eq_mul_inv]; ring_nf
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = (m : ℤ) + 1 := ⟨p.toNat - 1, by omega⟩
    have hp' : ¬ ((m : ℤ) + 1 ≤ 0) := by omega
    have hn : ((m : ℤ) + 1).toNat = m + 1 := by omega
    simp only [reidAiryB, hp', ↓reduceIte, hn, Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul,
      zero_div, ofReal_zero, exp_zero, mul_one, one_mul, add_zero, Nat.add_sub_cancel]
    have hsm : Summable fun j => ‖reidTaylorCoeff z (j + (m + 1))‖ :=
      (summable_norm_reidTaylorCoeff z).comp_injective (add_left_injective _)
    have hker : ∀ t ∈ Set.uIoc (0 : ℝ) 1, (t : ℂ) ^ (-(((m : ℤ) + 1 : ℤ) : ℂ)) *
        (exp (z * t - (t : ℂ) ^ 3 / 3) - ∑ x ∈ Finset.range (m + 1),
          reidTaylorCoeff z x * (t : ℂ) ^ x) =
          ∑' j, reidTaylorCoeff z (j + (m + 1)) * (t : ℂ) ^ (j + 0) := by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
      rw [← pow_mul_reidTaylorTail, show (((m : ℤ) + 1 : ℤ) : ℂ) = ((m + 1 : ℕ) : ℂ) by
        push_cast; ring, cpow_neg, cpow_natCast, inv_mul_cancel_left₀ (pow_ne_zero _ ht0)]
      rfl
    rw [add_assoc, intervalIntegral.integral_congr_ae (ae_of_all _ hker),
      integral_tsum_pow _ hsm 0, reidSeries_eq_nat]
    have hs : Summable fun j : ℕ =>
        reidTaylorCoeff z j * ((j : ℂ) + 1 - (((m : ℤ) + 1 : ℤ) : ℂ))⁻¹ := by
      refine .of_norm_bounded (summable_norm_reidTaylorCoeff z) fun j => ?_
      rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      have := norm_int_sub_inv_le ((j : ℤ) + 1) ((m : ℤ) + 1)
      push_cast at this ⊢; exact this
    rw [← hs.sum_add_tsum_nat_add (m + 1), Finset.sum_range_succ]
    have h0 : ((m : ℂ) + 1 - (((m : ℤ) + 1 : ℤ) : ℂ))⁻¹ = 0 := by push_cast; simp
    rw [h0, mul_zero, add_zero]
    congr 1
    rw [add_comm]
    congr 1
    refine tsum_congr fun j => ?_
    push_cast; rw [div_eq_mul_inv]; ring_nf


/-- `B_k` as a unit-ray integral, the finite-part series and a Reid contour. -/
private lemma reidAiryB_eq_decomp (k : Fin 3) (z : ℂ) (p : ℤ) :
    reidAiryB k z p = reidRay z p 0 1 + reidSeries z p +
      reidContour z p 0 (2 * k.val * π / 3) := by
  have h := reidAiryB_sub_eq_reidContour k 0 z p
  simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul, zero_div] at h
  rw [← reidAiryB_zero_eq]; linear_combination h

/-- The `z`-derivative of the finite-part `B_k(z, p)` is `B_k(z, p - 1)`, for every integer
`p`. -/
theorem hasDerivAt_reidAiryB (k : Fin 3) (p : ℤ) (z : ℂ) :
    HasDerivAt (fun z => reidAiryB k z p) (reidAiryB k z (p - 1)) z := by
  have hc0 : exp (3 * (((0 : ℝ) : ℂ) * I)) = 1 := by simp
  have h1 := hasDerivAt_reidRay hc0 (p : ℂ) zero_le_one (Or.inl le_rfl) z
  have h2 := hasDerivAt_reidSeries p z
  have h3 := hasDerivAt_reidContour hc0 (exp_three_reidAiryB_angle k) (p : ℂ) z
  have e : (fun z => reidAiryB k z p) = fun z => reidRay z p 0 1 + reidSeries z p +
      reidContour z p 0 (2 * k.val * π / 3) := funext fun z => reidAiryB_eq_decomp k z p
  rw [e, reidAiryB_eq_decomp k z (p - 1)]
  push_cast
  exact (h1.add h2).add h3

/-- The difference equation for the finite-part `B_k` and every integer `p`:
`B_k(z, p-3) - z B_k(z, p-1) + (p-1) B_k(z, p) = B₀(z, p)`; the right side vanishes for
`p ≤ 0` (DLMF 9.13.32). -/
theorem reidAiryB_difference_finitePart (k : Fin 3) (z : ℂ) (p : ℤ) :
    reidAiryB k z (p - 3) - z * reidAiryB k z (p - 1) + ((p : ℂ) - 1) * reidAiryB k z p =
      reidAiryB0 z p := by
  have hc0 : exp (3 * (((0 : ℝ) : ℂ) * I)) = 1 := by simp
  have hray := reidRay_difference hc0 z (p : ℂ) zero_le_one (Or.inl le_rfl)
      (g := fun t : ℝ => reidKernel z ((p : ℂ) - 1) (log t + ((0 : ℝ) : ℂ) * I)) (fun _ _ => rfl)
      (hasDerivAt_reidKernel_log z p 0 one_pos).continuousAt.continuousWithinAt
  have hcon := reidContour_difference hc0 (exp_three_reidAiryB_angle k) z (p : ℂ)
  have hser := reidSeries_difference z p
  rw [reidAiryB_eq_decomp k z (p - 3), reidAiryB_eq_decomp k z (p - 1),
    reidAiryB_eq_decomp k z p]
  have hk : reidKernel z ((p : ℂ) - 1) (log ((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) =
      exp (z - 1 / 3) := by
    simp [reidKernel]
  rw [hk] at hray
  push_cast
  linear_combination hray + hcon + hser

/-- Positive-p finite-part correction: the lower endpoint contributes a polynomial forcing. -/
theorem reidAiryB_finitePart_ode (k : Fin 3) (z : ℂ) {p : ℤ} (hp : 1 ≤ p) :
    iteratedDeriv 3 (fun t => reidAiryB k t p) z - z * deriv (fun t => reidAiryB k t p) z +
      ((p : ℂ) - 1) * reidAiryB k z p = reidTaylorCoeff z (p.toNat - 1) := by
  have hd : ∀ q : ℤ, deriv (fun t => reidAiryB k t q) = fun t => reidAiryB k t (q - 1) :=
    fun q => funext fun t => (hasDerivAt_reidAiryB k q t).deriv
  have h3 : iteratedDeriv 3 (fun t => reidAiryB k t p) = fun t => reidAiryB k t (p - 3) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, hd, hd, hd]
    funext t; congr 1; ring
  rw [h3, hd]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = (m : ℤ) + 1 := ⟨p.toNat - 1, by omega⟩
  rw [show ((m : ℤ) + 1).toNat - 1 = m by omega, ← reidAiryB0_natCast_add_one]
  exact reidAiryB_difference_finitePart k z _

end DLMF.Airy

end
