/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Hurwitz.ValuesAndDerivatives
public import DLMF.Zeta.Riemann

/-!
# Higher `s`-derivatives of the Hurwitz zeta function

For real `a > 0` and `Re s > -1`, `s ≠ 1`, the Euler–Maclaurin representation
`ζ(s, a) = a^{-s}(1/2 + a/(s-1)) - (s(s+1)/2) ∫_0^∞ (B̃₂(x) - B₂)/(x+a)^{s+2} dx`
(`hurwitzZetaComplex_eulerMaclaurin_two`) is differentiated `k` times in `s` under the integral
sign. This gives DLMF 25.11.20.

## Main results

* `iteratedDeriv_hurwitzZetaComplex'`: the formula for all `k`, stronger than DLMF.
* `iteratedDeriv_hurwitzZetaComplex`: DLMF 25.11.20 for `k ≥ 1`.

## Implementation notes

Writing `I_j(t) = ∫_0^∞ (B̃₂(x) - B₂)(ln(x+a))^j/(x+a)^{t+2} dx`, one has `I_j' = -I_{j+1}`
on `Re t > -1`. An explicit family of functions whose derivatives are the next member of the
family is checked against `ζ(·, a)` at `k = 0`, which identifies all iterated derivatives.
-/

@[expose] public section

open Complex Filter Set MeasureTheory HurwitzZeta

open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta


private lemma exists_abs_log_pow_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → |Real.log y| ^ n ≤ C * (y ^ δ + y ^ (-δ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, zero_le_one, fun y hy => ?_⟩
    rw [pow_zero, one_mul]
    rcases le_or_gt 1 y with h | h
    · have := Real.one_le_rpow h hδ.le; linarith [Real.rpow_pos_of_pos hy (-δ)]
    · have : 1 ≤ y ^ (-δ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy h.le (by linarith)
      linarith [Real.rpow_pos_of_pos hy δ]
  · set ε := δ / n
    have hε : 0 < ε := by positivity
    refine ⟨(1 / ε) ^ n, by positivity, fun y hy => ?_⟩
    have key : ∀ z : ℝ, 0 < z → 0 ≤ Real.log z → Real.log z ^ n ≤ (1 / ε) ^ n * z ^ δ := by
      intro z hz hl
      have h1 := Real.log_le_rpow_div hz.le hε
      calc Real.log z ^ n ≤ (z ^ ε / ε) ^ n := pow_le_pow_left₀ hl h1 n
        _ = (1 / ε) ^ n * z ^ δ := by
          rw [div_pow, ← Real.rpow_natCast (z ^ ε), ← Real.rpow_mul hz.le]
          have : ε * (n : ℝ) = δ := by simp only [ε]; field_simp
          rw [this]; ring
    have h0 := Real.rpow_pos_of_pos hy (-δ)
    have h0' := Real.rpow_pos_of_pos hy δ
    have hC : 0 ≤ (1 / ε) ^ n := by positivity
    rcases le_or_gt 0 (Real.log y) with hl | hl
    · rw [abs_of_nonneg hl]; have := key y hy hl; nlinarith
    · have hl' : 0 ≤ Real.log y⁻¹ := by rw [Real.log_inv]; linarith
      have := key y⁻¹ (inv_pos.mpr hy) hl'
      rw [Real.log_inv, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le] at this
      rw [abs_of_neg hl]
      linarith [mul_nonneg hC h0'.le]

private lemma iteratedDeriv_eq_of_hasDerivAt {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    {F : ℕ → ℂ → ℂ} (h0 : ∀ t ∈ U, f t = F 0 t)
    (hd : ∀ k, ∀ t ∈ U, HasDerivAt (F k) (F (k + 1) t) t) :
    ∀ k, ∀ t ∈ U, iteratedDeriv k f t = F k t := by
  intro k
  induction k with
  | zero => intro t ht; simpa using h0 t ht
  | succ k ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k f =ᶠ[𝓝 t] F k := by
      filter_upwards [hU.mem_nhds ht] with u hu using ih u hu
    rw [hev.deriv_eq]
    exact (hd k t ht).deriv

private lemma hasDerivAt_inv_sub_one_pow (n : ℕ) {t : ℂ} (ht : t ≠ 1) :
    HasDerivAt (fun u : ℂ => ((u - 1)⁻¹) ^ n) (-(n : ℂ) * ((t - 1)⁻¹) ^ (n + 1)) t := by
  have h1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  have hinv : HasDerivAt (fun u : ℂ => (u - 1)⁻¹) (-((t - 1) ^ 2)⁻¹) t := by
    have := ((hasDerivAt_id t).sub_const (1 : ℂ)).fun_inv h1
    convert this using 1
    · rfl
    · simp only [id, neg_div, one_div]
  have := hinv.fun_pow n
  convert this using 1
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, ← inv_pow]
    push_cast
    ring

/-- Differentiation under the integral sign for `∫_0^∞ f(x) (ln(x+a))^j/(x+a)^{s+2} dx` with
bounded measurable `f`, `a > 0`, `Re s > -1`. -/
private lemma hasDerivAt_integral_log_pow_div {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) {a : ℝ} (ha : 0 < a) (j : ℕ) {s : ℂ} (hs : -1 < s.re) :
    HasDerivAt (fun t => ∫ x in Ioi (0 : ℝ), ((f x : ℝ) : ℂ) * (Real.log (x + a) : ℂ) ^ j /
        (((x + a : ℝ)) : ℂ) ^ (t + 2))
      (-∫ x in Ioi (0 : ℝ), ((f x : ℝ) : ℂ) * (Real.log (x + a) : ℂ) ^ (j + 1) /
        (((x + a : ℝ)) : ℂ) ^ (s + 2)) s := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set ε := (s.re + 1) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  set lo := s.re - ε + 2
  set hi := s.re + ε + 2
  have hlo : 1 < lo := by simp only [lo, ε]; linarith
  set δ := (lo - 1) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  obtain ⟨C, hC0, hC⟩ := exists_abs_log_pow_le (j + 1) hδ
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_abs_log_pow_le j hδ
  have hint : ∀ r : ℝ, r < -1 → IntegrableOn (fun x : ℝ => (x + a) ^ r) (Ioi 0) := fun r hr =>
    integrableOn_add_rpow_Ioi_of_lt hr (by linarith)
  set F : ℂ → ℝ → ℂ := fun t x => ((f x : ℝ) : ℂ) * (Real.log (x + a) : ℂ) ^ j /
    (((x + a : ℝ)) : ℂ) ^ (t + 2)
  set F' : ℂ → ℝ → ℂ := fun t x =>
    -(((f x : ℝ) : ℂ) * (Real.log (x + a) : ℂ) ^ (j + 1) / (((x + a : ℝ)) : ℂ) ^ (t + 2))
  have hlogm : Measurable fun x : ℝ => (Real.log (x + a) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_log.comp (measurable_id.add_const a))
  have hmeasF : ∀ t, Measurable (F t) := fun t =>
    ((Complex.measurable_ofReal.comp hf).mul (hlogm.pow_const j)).div
      ((Complex.measurable_ofReal.comp (measurable_id.add_const a)).pow_const _)
  have hmeasF' : Measurable (F' s) :=
    (((Complex.measurable_ofReal.comp hf).mul (hlogm.pow_const (j + 1))).div
      ((Complex.measurable_ofReal.comp (measurable_id.add_const a)).pow_const _)).neg
  have hnorm : ∀ (n : ℕ) (t : ℂ) (x : ℝ), 0 < x + a →
      ‖((f x : ℝ) : ℂ) * (Real.log (x + a) : ℂ) ^ n / (((x + a : ℝ)) : ℂ) ^ (t + 2)‖ =
        |f x| * |Real.log (x + a)| ^ n * (x + a) ^ (-(t.re + 2)) := by
    intro n t x hxa
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_cpow_eq_rpow_re_of_pos hxa, Real.rpow_neg hxa.le, div_eq_mul_inv]
    simp
  set bound : ℝ → ℝ := fun x => B * C * (((x + a) ^ (δ - lo) + (x + a) ^ (δ - hi)) +
    ((x + a) ^ (-δ - lo) + (x + a) ^ (-δ - hi)))
  have hbound : IntegrableOn bound (Ioi 0) := by
    refine Integrable.const_mul ?_ _
    refine Integrable.add (Integrable.add ?_ ?_) (Integrable.add ?_ ?_) <;>
      exact hint _ (by simp only [δ, hi, lo, ε] at *; linarith)
  have hFs : Integrable (F s) (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' (g := fun x => B * C₀ * ((x + a) ^ (δ - (s.re + 2)) +
      (x + a) ^ (-δ - (s.re + 2)))) ?_ (hmeasF s).aestronglyMeasurable ?_
    · refine Integrable.const_mul (Integrable.add ?_ ?_) _ <;>
        exact hint _ (by simp only [δ, lo, ε] at *; linarith)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxa : 0 < x + a := by linarith [mem_Ioi.mp hx]
      simp only [F]
      rw [hnorm j s x hxa, Real.rpow_sub hxa, Real.rpow_sub hxa, Real.rpow_neg hxa.le,
        ← div_eq_mul_inv, ← add_div, div_eq_mul_inv, div_eq_mul_inv]
      have h1 := hC₀ (x + a) hxa
      have h2 := hB x
      have h3 : 0 ≤ ((x + a) ^ (s.re + 2))⁻¹ := by positivity
      calc |f x| * |Real.log (x + a)| ^ j * ((x + a) ^ (s.re + 2))⁻¹
          ≤ B * (C₀ * ((x + a) ^ δ + (x + a) ^ (-δ))) * ((x + a) ^ (s.re + 2))⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul h2 h1 (by positivity) hB0) h3
        _ = _ := by ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := s) (bound := bound) (Metric.ball_mem_nhds s hε)
    (Eventually.of_forall fun t => (hmeasF t).aestronglyMeasurable) hFs
    hmeasF'.aestronglyMeasurable ?_ hbound ?_
  · simpa only [F, F', integral_neg] using h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t ht
    have hxa : 0 < x + a := by linarith [mem_Ioi.mp hx]
    rw [Metric.mem_ball, dist_eq_norm] at ht
    have := abs_re_le_norm (t - s)
    simp only [sub_re] at this
    have h1 : lo ≤ t.re + 2 := by simp only [lo]; linarith [neg_abs_le (t.re - s.re)]
    have h2 : t.re + 2 ≤ hi := by simp only [hi]; linarith [le_abs_self (t.re - s.re)]
    simp only [F', norm_neg]
    rw [hnorm (j + 1) t x hxa]
    have hlog := hC (x + a) hxa
    have hp : (x + a) ^ (-(t.re + 2)) ≤ (x + a) ^ (-lo) + (x + a) ^ (-hi) := by
      have := rpow_neg_sub_one_le_add (x := x + a) (σ := t.re + 1) (σ₀ := lo - 1) (R := hi - 1) hxa
        (by linarith) (by linarith)
      convert this using 2 <;> ring_nf
    calc |f x| * |Real.log (x + a)| ^ (j + 1) * (x + a) ^ (-(t.re + 2))
        ≤ B * ((C * ((x + a) ^ δ + (x + a) ^ (-δ))) * ((x + a) ^ (-lo) + (x + a) ^ (-hi))) := by
          rw [mul_assoc]
          exact mul_le_mul (hB x) (mul_le_mul hlog hp (by positivity) (by positivity))
            (by positivity) hB0
      _ = bound x := by
          simp only [bound]
          rw [Real.rpow_sub hxa, Real.rpow_sub hxa, Real.rpow_sub hxa, Real.rpow_sub hxa,
            Real.rpow_neg hxa.le, Real.rpow_neg hxa.le, Real.rpow_neg hxa.le]
          field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx t _
    have hxa : 0 < x + a := by linarith [mem_Ioi.mp hx]
    have hy0 : (((x + a : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hxa.ne'
    have hlin : HasDerivAt (fun u : ℂ => -(u + 2)) (-1) t := by
      have := ((hasDerivAt_id t).add_const (2 : ℂ)).fun_neg
      simpa only [id] using this
    have hd := hlin.const_cpow (c := (((x + a : ℝ)) : ℂ)) (Or.inl hy0)
    have hd2 := hd.const_mul (((f x : ℝ) : ℂ) * (Real.log (x + a) : ℂ) ^ j)
    simp only [F, F']
    convert hd2 using 1
    · funext u; rw [div_eq_mul_inv, ← cpow_neg]
    · rw [← Complex.ofReal_log hxa.le, div_eq_mul_inv, ← cpow_neg]; ring

/-- The sum `∑_{r ≤ k} (k!/r!) L^r u^{k+1-r}` occurring in the `k`-th derivative of
`c^{1-t}/(t-1)`. -/
private def powerSum (L u : ℂ) (k : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (k + 1), (k ! / r ! : ℂ) * L ^ r * u ^ (k + 1 - r)

private lemma powerSum_succ (L u : ℂ) (k : ℕ) :
    L * powerSum L u k + ∑ r ∈ Finset.range (k + 1),
      (k ! / r ! : ℂ) * L ^ r * (((k + 1 - r : ℕ) : ℂ) * u ^ (k + 1 - r + 1)) =
      powerSum L u (k + 1) := by
  have hsplit : powerSum L u (k + 1) =
      ∑ r ∈ Finset.range (k + 2), (k ! / r ! : ℂ) * ((k + 1 - r : ℕ) : ℂ) * L ^ r *
        u ^ (k + 2 - r) +
      ∑ r ∈ Finset.range (k + 2), (k ! / r ! : ℂ) * (r : ℂ) * L ^ r * u ^ (k + 2 - r) := by
    rw [powerSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hr : r ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [show k + 1 + 1 - r = k + 2 - r by omega, Nat.cast_sub hr, Nat.factorial_succ]
    push_cast
    ring
  have e1 : ∑ r ∈ Finset.range (k + 2), (k ! / r ! : ℂ) * ((k + 1 - r : ℕ) : ℂ) * L ^ r *
      u ^ (k + 2 - r) = ∑ r ∈ Finset.range (k + 1),
        (k ! / r ! : ℂ) * L ^ r * (((k + 1 - r : ℕ) : ℂ) * u ^ (k + 1 - r + 1)) := by
    rw [Finset.sum_range_succ, Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul, zero_mul,
      add_zero]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hr : r < k + 1 := Finset.mem_range.mp hr
    rw [show k + 1 - r + 1 = k + 2 - r by omega]
    ring
  have e2 : ∑ r ∈ Finset.range (k + 2), (k ! / r ! : ℂ) * (r : ℂ) * L ^ r * u ^ (k + 2 - r) =
      L * powerSum L u k := by
    rw [Finset.sum_range_succ', Nat.cast_zero, mul_zero, zero_mul, zero_mul, add_zero, powerSum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [show k + 2 - (r + 1) = k + 1 - r by omega, Nat.factorial_succ]
    push_cast
    have : (r ! : ℂ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
    field_simp
    ring
  rw [hsplit, e1, e2]
  ring

/-- `I_j(t) = ∫_0^∞ (B̃₂(x) - B₂)(ln(x+a))^j/(x+a)^{t+2} dx`. -/
private def logPowIntegral (a : ℝ) (j : ℕ) (t : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) *
    (Real.log (x + a) : ℂ) ^ j / (((x + a : ℝ)) : ℂ) ^ (t + 2)

private lemma hasDerivAt_logPowIntegral {a : ℝ} (ha : 0 < a) (j : ℕ) {t : ℂ}
    (ht : -1 < t.re) :
    HasDerivAt (logPowIntegral a j) (-logPowIntegral a (j + 1) t) t := by
  obtain ⟨C, hC⟩ := exists_abs_periodicBernoulli_le 2
  refine hasDerivAt_integral_log_pow_div (f := fun x => periodicBernoulli 2 x - bernoulli 2)
    ((measurable_periodicBernoulli 2).sub_const _) (B := C + |(bernoulli 2 : ℝ)|)
    (fun x => ?_) ha j ht
  exact (abs_sub _ _).trans (by linarith [hC x])

/-- The explicit `k`-th `s`-derivative of `ζ(s, a)` (DLMF 25.11.20, with the sign `(-1)^k`
not yet removed). -/
private def iteratedDerivFormula (a : ℝ) (k : ℕ) (t : ℂ) : ℂ :=
  (-(Real.log a : ℂ)) ^ k * (a : ℂ) ^ (-t) / 2 +
    (-1) ^ k * (a : ℂ) ^ (1 - t) * powerSum (Real.log a) (t - 1)⁻¹ k -
    (-1) ^ k * (t * (t + 1) / 2 * logPowIntegral a k t -
      k * ((2 * t + 1) / 2) * logPowIntegral a (k - 1) t +
      k * (k - 1) / 2 * logPowIntegral a (k - 2) t)

private lemma hasDerivAt_powerSum (L : ℂ) (k : ℕ) {t : ℂ} (ht : t ≠ 1) :
    HasDerivAt (fun u => powerSum L (u - 1)⁻¹ k)
      (-∑ r ∈ Finset.range (k + 1),
        (k ! / r ! : ℂ) * L ^ r * (((k + 1 - r : ℕ) : ℂ) * ((t - 1)⁻¹) ^ (k + 1 - r + 1))) t := by
  simp only [powerSum]
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum (fun r _ => ?_)
  have := (hasDerivAt_inv_sub_one_pow (k + 1 - r) ht).const_mul ((k ! / r ! : ℂ) * L ^ r)
  convert this using 1
  ring

private lemma hasDerivAt_iteratedDerivFormula {a : ℝ} (ha : 0 < a) (k : ℕ) {t : ℂ}
    (ht1 : t ≠ 1) (ht : -1 < t.re) :
    HasDerivAt (iteratedDerivFormula a k) (iteratedDerivFormula a (k + 1) t) t := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set L : ℂ := (Real.log a : ℂ)
  have hL : Complex.log (a : ℂ) = L := (Complex.ofReal_log ha.le).symm
  have hE : HasDerivAt (fun u : ℂ => (a : ℂ) ^ (-u)) ((a : ℂ) ^ (-t) * L * (-1)) t := by
    rw [← hL]; exact (hasDerivAt_neg t).const_cpow (Or.inl ha0)
  have hE1 : HasDerivAt (fun u : ℂ => (a : ℂ) ^ (1 - u)) ((a : ℂ) ^ (1 - t) * L * (-1)) t := by
    rw [← hL]
    have := ((hasDerivAt_id t).const_sub (1 : ℂ)).const_cpow (c := (a : ℂ)) (Or.inl ha0)
    simpa [id] using this
  have hS := hasDerivAt_powerSum L k ht1
  have hP : HasDerivAt (fun u : ℂ => u * (u + 1) / 2) ((2 * t + 1) / 2) t := by
    have := ((hasDerivAt_id' t).fun_mul ((hasDerivAt_id' t).add_const (1 : ℂ))).div_const 2
    convert this using 1; ring
  have hP' : HasDerivAt (fun u : ℂ => (2 * u + 1) / 2) 1 t := by
    have := (((hasDerivAt_id' t).const_mul (2 : ℂ)).add_const (1 : ℂ)).div_const 2
    convert this using 1; ring
  have hI := fun j => hasDerivAt_logPowIntegral ha j ht
  have hD := (((hE.mul_const ((-L) ^ k / 2)).add
    (((hE1.mul hS).const_mul ((-1) ^ k)))).sub
    ((((hP.mul (hI k)).sub ((hP'.mul (hI (k - 1))).const_mul (k : ℂ))).add
      ((hI (k - 2)).const_mul ((k : ℂ) * (k - 1) / 2))).const_mul ((-1) ^ k)))
  convert hD using 1
  · funext u
    simp only [iteratedDerivFormula, L, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  · simp only [iteratedDerivFormula]
    rw [← powerSum_succ]
    rcases k with _ | _ | k
    · simp; ring
    · simp; ring
    · simp only [show k + 1 + 1 - 2 = k by omega,
        show k + 1 + 1 + 1 - 2 = k + 1 by omega, show k + 1 + 1 + 1 - 1 = k + 1 + 1 by omega,
        show k + 1 + 1 - 1 = k + 1 by omega]
      push_cast
      ring

/-- **Higher `s`-derivatives** (DLMF 25.11.20), for all `k`, `Re s > -1`, `s ≠ 1`, real
`a > 0`; stronger than DLMF, which assumes `k ≥ 1`. For `k = 0` it is
`hurwitzZetaComplex_eulerMaclaurin_two`; for `k ≤ 1` the terms with `I (k - 1)` or `I (k - 2)`
have coefficient `0`. -/
@[dlmf 25.11.E20 "stronger than DLMF: no hypothesis k ≥ 1"]
theorem iteratedDeriv_hurwitzZetaComplex' (k : ℕ) {s : ℂ} (hs : s ≠ 1)
    (hs0 : -1 < s.re) {a : ℝ} (ha : 0 < a) :
    let I : ℕ → ℂ := fun j => ∫ x in Ioi (0 : ℝ), ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) *
      (Real.log (x + a) : ℂ) ^ j / (((x + a : ℝ)) : ℂ) ^ (s + 2)
    (-1) ^ k * iteratedDeriv k (fun t => hurwitzZetaComplex t a) s =
      (Real.log a : ℂ) ^ k / (a : ℂ) ^ s * (1 / 2 + a / (s - 1)) +
      k ! * (a : ℂ) ^ (1 - s) * ∑ r ∈ Finset.range k,
        (Real.log a : ℂ) ^ r / (r ! * (s - 1) ^ (k - r + 1)) -
      s * (s + 1) / 2 * I k + k * (2 * s + 1) / 2 * I (k - 1) -
      k * (k - 1 : ℂ) / 2 * I (k - 2) := by
  intro I
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set U : Set ℂ := {t : ℂ | -1 < t.re} \ {1}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  have hcpow : ∀ t : ℂ, (a : ℂ) ^ (1 - t) = a * (a : ℂ) ^ (-t) := fun t => by
    rw [sub_eq_add_neg, cpow_add _ _ ha0, cpow_one]
  have hmain := iteratedDeriv_eq_of_hasDerivAt hU (f := fun t => hurwitzZetaComplex t a)
    (F := iteratedDerivFormula a) (fun t ht => ?_)
    (fun k t ht => hasDerivAt_iteratedDerivFormula ha k ht.2 ht.1) k s ⟨hs0, hs⟩
  · rw [hmain]
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    have hk : (k ! / k ! : ℂ) = 1 := div_self (by exact_mod_cast k.factorial_ne_zero)
    set S := ∑ r ∈ Finset.range k, (Real.log a : ℂ) ^ r / (r ! * (s - 1) ^ (k - r + 1))
    have hPS : powerSum (Real.log a) (s - 1)⁻¹ k = k ! * S + (Real.log a : ℂ) ^ k * (s - 1)⁻¹ := by
      rw [powerSum, Finset.sum_range_succ, hk, show k + 1 - k = 1 by omega, pow_one, one_mul,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have hr : r < k := Finset.mem_range.mp hr
      rw [show k + 1 - r = k - r + 1 by omega, inv_pow]
      have : (r ! : ℂ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
      field_simp
    have hF : iteratedDerivFormula a k s = (-1) ^ k * ((Real.log a : ℂ) ^ k * (a : ℂ) ^ (-s) / 2 +
        (a : ℂ) ^ (1 - s) * (k ! * S + (Real.log a : ℂ) ^ k * (s - 1)⁻¹) -
        (s * (s + 1) / 2 * I k - k * ((2 * s + 1) / 2) * I (k - 1) +
          k * (k - 1) / 2 * I (k - 2))) := by
      have hI : ∀ j, logPowIntegral a j s = I j := fun j => rfl
      simp only [iteratedDerivFormula, hPS, neg_pow (Real.log a : ℂ), hI]
      ring
    have h1 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [hF, ← mul_assoc, h1, one_mul, hcpow, cpow_neg]
    have has : (a : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; simp [ha0]
    field_simp
    ring
  · rw [hurwitzZetaComplex_eulerMaclaurin_two ht.2 ht.1 ha]
    simp only [iteratedDerivFormula, powerSum, logPowIntegral]
    simp [hcpow]
    ring

/-- **Higher `s`-derivatives** (DLMF 25.11.20): for `k ≥ 1` (for `k = 1` the last integral has
coefficient `0`), `Re s > -1`, `s ≠ 1`, real `a > 0`,
`(-1)^k ζ^{(k)}(s,a) = (ln a)^k a^{-s}(1/2 + a/(s-1)) + k! a^{1-s} ∑_{r=0}^{k-1}
(ln a)^r/(r!(s-1)^{k-r+1}) - (s(s+1)/2) I_k + (k(2s+1)/2) I_{k-1} - (k(k-1)/2) I_{k-2}`,
`I_j = ∫_0^∞ (B̃₂(x) - B₂)(ln(x+a))^j/(x+a)^{s+2} dx`. -/
@[dlmf 25.11.E20]
theorem iteratedDeriv_hurwitzZetaComplex {k : ℕ} (_hk : 1 ≤ k) {s : ℂ} (hs : s ≠ 1)
    (hs0 : -1 < s.re) {a : ℝ} (ha : 0 < a) :
    let I : ℕ → ℂ := fun j => ∫ x in Ioi (0 : ℝ), ((periodicBernoulli 2 x - bernoulli 2 : ℝ) : ℂ) *
      (Real.log (x + a) : ℂ) ^ j / (((x + a : ℝ)) : ℂ) ^ (s + 2)
    (-1) ^ k * iteratedDeriv k (fun t => hurwitzZetaComplex t a) s =
      (Real.log a : ℂ) ^ k / (a : ℂ) ^ s * (1 / 2 + a / (s - 1)) +
      k ! * (a : ℂ) ^ (1 - s) * ∑ r ∈ Finset.range k,
        (Real.log a : ℂ) ^ r / (r ! * (s - 1) ^ (k - r + 1)) -
      s * (s + 1) / 2 * I k + k * (2 * s + 1) / 2 * I (k - 1) -
      k * (k - 1 : ℂ) / 2 * I (k - 2) := by
  exact iteratedDeriv_hurwitzZetaComplex' k hs hs0 ha

end DLMF.Zeta
