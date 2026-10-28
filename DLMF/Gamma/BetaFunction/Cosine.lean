/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.BetaFunction.ParameterIntegrals

/-!
# Cosine Beta integrals

Trigonometric Beta integrals with cosine kernels and their continuation in complex parameters.

Source references and common attribution are retained in
`DLMF.Gamma.BetaFunction`.
-/

@[expose] public section

open Complex MeasureTheory intervalIntegral

open scoped Real

noncomputable section

namespace DLMF.Gamma

section CosineBeta

/-! ### DLMF 5.12.5–5.12.6

For `a - 1 < b < a + 1` the integral `∫_{-π/2}^{π/2} (2 cos x)^{a-1} e^{ibx} dx` is the
Abel limit `r → 1⁻` of the termwise integral of the binomial series of
`(1 + r e^{2ix})^{a-1} e^{i(b-a+1)x}`. The same series integrated against `u^{s-1}` on `[0, 1]`
gives a Beta integral, and Euler's reflection formula identifies the result. The remaining
range `|b| ≤ a - 1` follows by induction on `a` from the integration-by-parts recurrence
`(a - 1 + b) K(a, b) = (a - 1) K(a - 1, b - 1)`.
-/

open Filter Topology

/-- `cos ^ β` is integrable on `[0, π/2]` for `β > -1`; the integral is a positive Beta value. -/
theorem intervalIntegrable_cos_rpow {β : ℝ} (hβ : -1 < β) :
    IntervalIntegrable (fun x : ℝ => Real.cos x ^ β) volume 0 (π / 2) := by
  have h := beta_sin_cos (a := 1 / 2) (b := (β + 1) / 2) (by norm_num) (by linarith)
  have heq : (fun θ : ℝ => Real.sin θ ^ (2 * (1 / 2 : ℝ) - 1) *
      Real.cos θ ^ (2 * ((β + 1) / 2) - 1)) = fun θ => Real.cos θ ^ β := by
    funext θ
    rw [show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, one_mul]
    congr 1
    ring
  rw [heq] at h
  by_contra hni
  rw [intervalIntegral.integral_undef hni] at h
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < (β + 1) / 2 by linarith)
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 + (β + 1) / 2 by linarith)
  have : 0 < (1 / 2 : ℝ) * (Real.Gamma (1 / 2) * Real.Gamma ((β + 1) / 2) /
    Real.Gamma (1 / 2 + (β + 1) / 2)) := by positivity
  linarith

/-- `cos ^ β` is integrable on `[-π/2, π/2]` for `β > -1`. -/
theorem intervalIntegrable_cos_rpow' {β : ℝ} (hβ : -1 < β) :
    IntervalIntegrable (fun x : ℝ => Real.cos x ^ β) volume (-(π / 2)) (π / 2) := by
  have h0 := intervalIntegrable_cos_rpow hβ
  have h1 : IntervalIntegrable (fun x : ℝ => Real.cos x ^ β) volume (-(π / 2)) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (f := fun x : ℝ => Real.cos x ^ β)).mp h0
    simpa [Real.cos_neg] using this.symm
  exact h1.trans h0

/-- An even function: the integral over `[-c, c]` is twice that over `[0, c]`. -/
theorem integral_symm_of_even {f : ℝ → ℝ} {c : ℝ}
    (hf : IntervalIntegrable f volume 0 c) (heven : ∀ x, f (-x) = f x) :
    ∫ x in (-c)..c, f x = 2 * ∫ x in (0 : ℝ)..c, f x := by
  have h1 : IntervalIntegrable f volume (-c) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (f := f)).mp hf
    simpa [heven] using this.symm
  rw [← integral_add_adjacent_intervals h1 hf]
  have h2 : ∫ x in (-c)..0, f x = ∫ x in (0 : ℝ)..c, f x := by
    rw [← neg_zero, ← integral_comp_neg]
    simp [heven]
  rw [h2]
  ring

/-- An odd function integrates to zero over `[-c, c]`. -/
theorem integral_symm_of_odd {f : ℝ → ℝ} {c : ℝ}
    (hf : IntervalIntegrable f volume 0 c) (hodd : ∀ x, f (-x) = -f x) :
    ∫ x in (-c)..c, f x = 0 := by
  have h1 : IntervalIntegrable f volume (-c) 0 := by
    have h' : IntervalIntegrable (fun x => -f x) volume (-c) 0 := by
      simpa [hodd] using ((IntervalIntegrable.iff_comp_neg (f := f)).mp hf).symm
    have h'' := h'.neg
    simp only [Pi.neg_def, neg_neg] at h''
    exact h''
  rw [← integral_add_adjacent_intervals h1 hf]
  have h2 : ∫ x in (-c)..0, f x = -∫ x in (0 : ℝ)..c, f x := by
    rw [← neg_zero, ← integral_comp_neg]
    simp [hodd]
  rw [h2]
  ring

/-- For `β > -1` and continuous `g`, `cos^β x · g x` is interval integrable on subintervals of
`[-π/2, π/2]`. -/
theorem intervalIntegrable_cos_rpow_mul {β : ℝ} (hβ : -1 < β) {g : ℝ → ℝ} (hg : Continuous g)
    {s t : ℝ} (hst : Set.uIcc s t ⊆ Set.Icc (-(π / 2)) (π / 2)) :
    IntervalIntegrable (fun x : ℝ => Real.cos x ^ β * g x) volume s t :=
  ((intervalIntegrable_cos_rpow' hβ).mul_continuousOn hg.continuousOn).mono_set (by
    rwa [Set.uIcc_of_le (by linarith [Real.pi_pos] : -(π / 2) ≤ π / 2)])

/-- The complex cast of an interval-integrable real function is interval integrable. -/
theorem intervalIntegrable_ofReal {f : ℝ → ℝ} {s t : ℝ} (hf : IntervalIntegrable f volume s t) :
    IntervalIntegrable (fun x => (f x : ℂ)) volume s t :=
  ⟨hf.1.ofReal, hf.2.ofReal⟩

/-- The complex exponential integral of `cos ^ α` over `[-π/2, π/2]` is twice the cosine
integral over `[0, π/2]`. -/
theorem integral_cos_rpow_mul_exp {α : ℝ} (hα : -1 < α) (b : ℝ) :
    ∫ x in (-(π / 2))..(π / 2), ((Real.cos x ^ α : ℝ) : ℂ) * Complex.exp (↑(b * x) * I) =
      ↑(2 * ∫ x in (0 : ℝ)..(π / 2), Real.cos x ^ α * Real.cos (b * x)) := by
  have hpt : ∀ x : ℝ, ((Real.cos x ^ α : ℝ) : ℂ) * Complex.exp (↑(b * x) * I) =
      ((Real.cos x ^ α * Real.cos (b * x) : ℝ) : ℂ) +
        ((Real.cos x ^ α * Real.sin (b * x) : ℝ) : ℂ) * I := by
    intro x
    rw [Complex.exp_mul_I]
    push_cast
    ring
  simp_rw [hpt]
  have hsub : Set.uIcc (-(π / 2)) (π / 2) ⊆ Set.Icc (-(π / 2)) (π / 2) := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])]
  have hsub0 : Set.uIcc 0 (π / 2) ⊆ Set.Icc (-(π / 2)) (π / 2) := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])]
    exact Set.Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl
  have hc := intervalIntegrable_cos_rpow_mul hα (g := fun x => Real.cos (b * x))
    (by fun_prop) hsub
  have hs := intervalIntegrable_cos_rpow_mul hα (g := fun x => Real.sin (b * x))
    (by fun_prop) hsub
  rw [intervalIntegral.integral_add (intervalIntegrable_ofReal hc)
      ((intervalIntegrable_ofReal hs).mul_const I),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  rw [integral_symm_of_odd (intervalIntegrable_cos_rpow_mul hα (g := fun x => Real.sin (b * x))
    (by fun_prop) hsub0) (fun x => by simp [Real.cos_neg, Real.sin_neg]),
    integral_symm_of_even (intervalIntegrable_cos_rpow_mul hα (g := fun x => Real.cos (b * x))
    (by fun_prop) hsub0) (fun x => by simp [Real.cos_neg])]
  simp

/-- Almost every real number differs from a given `c`. -/
theorem ae_ne_real (c : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
  rw [ae_iff]
  simp

/-- The complex binomial series inside the unit disc. -/
theorem hasSum_choose_mul_pow (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose a n * z ^ n) ((1 + z) ^ a) := by
  have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum
    (y := z) (by
      simp only [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
      exact ENNReal.ofReal_lt_one.mpr hz)
  simpa [binomialSeries, FormalMultilinearSeries.coeff_ofScalars, mul_comm] using h

/-- The real binomial series inside the unit interval. -/
theorem hasSum_choose_mul_pow_real (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => Ring.choose a n * x ^ n) ((1 + x) ^ a) := by
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum
    (y := x) (by
      simp only [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
      exact ENNReal.ofReal_lt_one.mpr (by simpa using hx))
  simpa [binomialSeries, FormalMultilinearSeries.coeff_ofScalars, mul_comm] using h

/-- Absolute convergence of the binomial coefficients against `r ^ n` for `r < 1`. -/
theorem summable_norm_choose_mul_pow (a : ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun n : ℕ => ‖Ring.choose a n‖ * r ^ n) := by
  have h := (binomialSeries ℂ a).summable_norm_mul_pow (r := r.toNNReal)
    (lt_of_lt_of_le (ENNReal.coe_lt_one_iff.mpr (Real.toNNReal_lt_one.mpr hr))
      binomialSeries_radius_ge_one)
  simpa [binomialSeries, FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal _ hr0] using h

/-- `∫_{-π/2}^{π/2} e^{i(2n+μ)x} dx = (-1)ⁿ sin(πμ/2) / (n + μ/2)`. -/
theorem integral_exp_shifted_freq (n : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ∫ x in (-(π / 2))..(π / 2), Complex.exp (↑((2 * n + μ) * x) * I) =
      ↑(Real.sin (π * (μ / 2)) * (-1) ^ n / (n + μ / 2)) := by
  have hν : (0 : ℝ) < 2 * n + μ := by positivity
  have hc : ((2 * n + μ : ℝ) : ℂ) * I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hν.ne') I_ne_zero
  have hfun : (fun x : ℝ => Complex.exp (↑((2 * n + μ) * x) * I)) =
      fun x : ℝ => Complex.exp (((2 * n + μ : ℝ) : ℂ) * I * x) := by
    funext x
    push_cast
    ring_nf
  rw [hfun, integral_exp_mul_complex hc]
  set θ : ℝ := (2 * n + μ) * (π / 2) with hθ
  have h1 : ((2 * n + μ : ℝ) : ℂ) * I * ↑(π / 2) = (θ : ℂ) * I := by
    rw [hθ]; push_cast; ring
  have h2 : ((2 * n + μ : ℝ) : ℂ) * I * ↑(-(π / 2)) = ((-θ : ℝ) : ℂ) * I := by
    rw [hθ]; push_cast; ring
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
  have hsin : Real.sin θ = (-1) ^ n * Real.sin (π * (μ / 2)) := by
    rw [hθ, show (2 * n + μ) * (π / 2) = π * (μ / 2) + n * π by ring, Real.sin_add_nat_mul_pi]
  have hne : ((2 * n + μ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hne' : ((n : ℝ) + μ / 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < n + μ / 2 := by positivity
    exact_mod_cast this.ne'
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, hsin]
  push_cast
  field_simp
  ring

/-- Termwise integration of the binomial series of `(1 + r e^{2ix})^α` against `e^{iμx}`. -/
theorem hasSum_integral_one_add_mul_exp (α : ℝ) {μ r : ℝ} (hμ : 0 < μ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    HasSum (fun n : ℕ =>
        ((Real.sin (π * (μ / 2)) * (Ring.choose α n * (-r) ^ n / (n + μ / 2)) : ℝ) : ℂ))
      (∫ x in (-(π / 2))..(π / 2),
        (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I)) := by
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -(π / 2)) (b := π / 2)
    (F := fun (n : ℕ) (x : ℝ) =>
      Ring.choose (α : ℂ) n * (r : ℂ) ^ n * Complex.exp (↑((2 * n + μ) * x) * I))
    (f := fun x : ℝ =>
      (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I))
    (fun n _ => ‖Ring.choose (α : ℂ) n‖ * r ^ n)
    (fun n => (by fun_prop : Continuous fun x : ℝ =>
      Ring.choose (α : ℂ) n * (r : ℂ) ^ n *
        Complex.exp (↑((2 * n + μ) * x) * I)).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun x _ => by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0,
        Complex.norm_exp_ofReal_mul_I, mul_one])
    (Eventually.of_forall fun x _ => summable_norm_choose_mul_pow (α : ℂ) hr0 hr1)
    intervalIntegrable_const
    (Eventually.of_forall fun x _ => by
      have hz : ‖(r : ℂ) * Complex.exp (↑(2 * x) * I)‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        exact hr1
      convert (hasSum_choose_mul_pow (α : ℂ) hz).mul_right
        (Complex.exp (↑(μ * x) * I)) using 1
      funext n
      rw [mul_pow, ← Complex.exp_nat_mul, mul_assoc, mul_assoc, mul_assoc, ← Complex.exp_add]
      congr 3
      push_cast
      ring)
  convert key using 1
  funext n
  rw [intervalIntegral.integral_const_mul, integral_exp_shifted_freq n hμ]
  push_cast
  rw [neg_pow]
  ring

/-- `∫₀¹ uⁿ u^(s-1) du = 1/(n + s)` for `0 < s < 1`. -/
theorem integral_pow_mul_rpow (n : ℕ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∫ u in (0 : ℝ)..1, u ^ n * u ^ (s - 1) = 1 / (n + s) := by
  have hne : (n : ℝ) + (s - 1) ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp; linarith
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  have hcongr : ∀ u ∈ Set.uIcc (0 : ℝ) 1, u ^ n * u ^ (s - 1) = u ^ ((n : ℝ) + (s - 1)) := by
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    rw [Real.rpow_add' hu.1 hne, Real.rpow_natCast]
  rw [intervalIntegral.integral_congr hcongr,
    integral_rpow (Or.inl (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))]
  rw [show (n : ℝ) + (s - 1) + 1 = n + s by ring, Real.one_rpow,
    Real.zero_rpow (by positivity)]
  simp

/-- Termwise integration of the binomial series of `(1 - r u)^α` against `u^(s-1)`. -/
theorem hasSum_integral_one_sub_mul (α : ℝ) {s r : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    HasSum (fun n : ℕ => Ring.choose α n * (-r) ^ n / (n + s))
      (∫ u in (0 : ℝ)..1, (1 - r * u) ^ α * u ^ (s - 1)) := by
  have hsum : Summable fun n : ℕ => |Ring.choose α n| * r ^ n := by
    have := summable_norm_choose_mul_pow (α : ℂ) hr0 hr1
    simpa [← Complex.ofReal_choose, Complex.norm_real] using this
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 1)
    (F := fun (n : ℕ) (u : ℝ) => Ring.choose α n * (-r) ^ n * (u ^ n * u ^ (s - 1)))
    (f := fun u : ℝ => (1 - r * u) ^ α * u ^ (s - 1))
    (fun n u => |Ring.choose α n| * r ^ n * u ^ (s - 1))
    (fun n => (by fun_prop : Measurable fun u : ℝ =>
      Ring.choose α n * (-r) ^ n * (u ^ n * u ^ (s - 1))).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun u hu => by
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hu0 : 0 ≤ u := hu.1.le
      rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_pow, abs_neg, abs_of_nonneg hr0, abs_of_nonneg (pow_nonneg hu0 n),
        abs_of_nonneg (Real.rpow_nonneg hu0 _)]
      have h1 : u ^ n ≤ 1 := pow_le_one₀ hu0 hu.2
      have h2 : 0 ≤ |Ring.choose α n| * r ^ n := by positivity
      have h3 : 0 ≤ u ^ (s - 1) := Real.rpow_nonneg hu0 _
      calc |Ring.choose α n| * r ^ n * (u ^ n * u ^ (s - 1))
          ≤ |Ring.choose α n| * r ^ n * (1 * u ^ (s - 1)) := by gcongr
        _ = _ := by ring)
    (Eventually.of_forall fun u _ => hsum.mul_right _)
    (by
      simp_rw [tsum_mul_right]
      exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
    (Eventually.of_forall fun u hu => by
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hx : |-(r * u)| < 1 := by
        rw [abs_neg, abs_of_nonneg (mul_nonneg hr0 hu.1.le)]
        calc r * u ≤ r * 1 := by gcongr; exact hu.2
          _ < 1 := by linarith
      convert (hasSum_choose_mul_pow_real α hx).mul_right (u ^ (s - 1)) using 1
      funext n
      ring)
  convert key using 1
  funext n
  rw [intervalIntegral.integral_const_mul, integral_pow_mul_rpow n hs0 hs1]
  ring

/-- For `0 ≤ r ≤ 1`, `cos x ≤ |1 + r e^(2ix)| ≤ 2`. -/
theorem norm_one_add_mul_exp_bounds {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.cos x ≤ ‖1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)‖ ∧
      ‖1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)‖ ≤ 2 := by
  constructor
  · rcases lt_or_ge (Real.cos x) 0 with hc | hc
    · exact hc.le.trans (norm_nonneg _)
    rw [← pow_le_pow_iff_left₀ hc (norm_nonneg _) two_ne_zero, Complex.sq_norm,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.normSq_apply]
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, add_im, one_im, mul_im, I_re, I_im]
    have h2c : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := Real.cos_two_mul x
    have hs : Real.sin (2 * x) ^ 2 = 1 - Real.cos (2 * x) ^ 2 := by
      rw [← Real.sin_sq_add_cos_sq (2 * x)]; ring
    have hc1 : Real.cos x ^ 2 ≤ 1 := by
      rw [← Real.sin_sq_add_cos_sq x]; nlinarith [sq_nonneg (Real.sin x)]
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1), mul_nonneg (mul_nonneg hr0 hr0)
      (sub_nonneg.mpr hc1), sq_nonneg (1 - r), mul_nonneg (sq_nonneg (1 - r)) (sub_nonneg.mpr hc1)]
  · calc ‖1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)‖
        ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * Complex.exp (↑(2 * x) * I)‖ := norm_add_le _ _
      _ = 1 + r := by
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      _ ≤ 2 := by linarith

/-- A point of `(-π/2, π/2]` other than `π/2` lies in `(-π/2, π/2)`. -/
theorem mem_Ioo_of_mem_uIoc {x : ℝ} (hx : x ≠ π / 2) (hxI : x ∈ Set.uIoc (-(π / 2)) (π / 2)) :
    x ∈ Set.Ioo (-(π / 2)) (π / 2) := by
  rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
  exact ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩

/-- Abel limit `r → 1⁻` of the integral of `(1 + r e^{2ix})^α e^{iμx}`. -/
theorem tendsto_integral_one_add_mul_exp {α : ℝ} (hα : -1 < α) (μ : ℝ) :
    Tendsto (fun r : ℝ => ∫ x in (-(π / 2))..(π / 2),
        (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I))
      (𝓝[<] 1)
      (𝓝 (∫ x in (-(π / 2))..(π / 2),
        (1 + Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => (2 : ℝ) ^ α + Real.cos x ^ α)
  · exact Eventually.of_forall fun r => (by fun_prop : Measurable fun x : ℝ =>
      (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) *
        Complex.exp (↑(μ * x) * I)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    filter_upwards [ae_ne_real (π / 2)] with x hx hxI
    have hxo := mem_Ioo_of_mem_uIoc hx hxI
    have hcpos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hxo
    obtain ⟨hlo, hhi⟩ := norm_one_add_mul_exp_bounds (x := x) hr.1.le hr.2.le
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_cpow_real]
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ α := by positivity
    have hc : (0 : ℝ) ≤ Real.cos x ^ α := Real.rpow_nonneg hcpos.le _
    rcases le_or_gt 0 α with hα0 | hα0
    · have := Real.rpow_le_rpow (norm_nonneg _) hhi hα0
      linarith
    · have := Real.rpow_le_rpow_of_nonpos hcpos hlo hα0.le
      linarith
  · exact intervalIntegrable_const.add (intervalIntegrable_cos_rpow' hα)
  · filter_upwards [ae_ne_real (π / 2)] with x hx hxI
    have hxo := mem_Ioo_of_mem_uIoc hx hxI
    have hcpos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hxo
    have hslit : 1 + ((1 : ℝ) : ℂ) * Complex.exp (↑(2 * x) * I) ∈ slitPlane := by
      refine Or.inl ?_
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
      rw [Real.cos_two_mul]
      nlinarith
    have hcont : ContinuousAt (fun r : ℝ =>
        (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) *
          Complex.exp (↑(μ * x) * I)) 1 :=
      (ContinuousAt.comp (f := fun r : ℝ => 1 + (r : ℂ) * Complex.exp (↑(2 * x) * I))
        (continuousAt_cpow_const (b := (α : ℂ)) hslit) (by fun_prop)).mul continuousAt_const
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using this

/-- The Beta integrand is integrable on `[0, 1]`; its integral is a positive Gamma value. -/
theorem intervalIntegrable_beta_integrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntervalIntegrable (fun u : ℝ => u ^ (p - 1) * (1 - u) ^ (q - 1)) volume 0 1 := by
  have h := real_betaIntegral hp hq
  by_contra hni
  rw [intervalIntegral.integral_undef hni] at h
  have := Real.Gamma_pos_of_pos hp
  have := Real.Gamma_pos_of_pos hq
  have := Real.Gamma_pos_of_pos (add_pos hp hq)
  have : 0 < Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by positivity
  linarith

/-- Abel limit `r → 1⁻` of `∫₀¹ (1 - r u)^α u^(s-1) du`. -/
theorem tendsto_integral_one_sub_mul {α s : ℝ} (hα : -1 < α) (hs0 : 0 < s) :
    Tendsto (fun r : ℝ => ∫ u in (0 : ℝ)..1, (1 - r * u) ^ α * u ^ (s - 1)) (𝓝[<] 1)
      (𝓝 (∫ u in (0 : ℝ)..1, (1 - u) ^ α * u ^ (s - 1))) := by
  have hB : IntervalIntegrable (fun u : ℝ => u ^ (s - 1) * (1 - u) ^ α) volume 0 1 := by
    have := intervalIntegrable_beta_integrand hs0 (show 0 < α + 1 by linarith)
    simpa only [add_sub_cancel_right] using this
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun u => u ^ (s - 1) + u ^ (s - 1) * (1 - u) ^ α)
  · exact Eventually.of_forall fun r => (by fun_prop : Measurable fun u : ℝ =>
      (1 - r * u) ^ α * u ^ (s - 1)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    filter_upwards [ae_ne_real 1] with u hu huI
    rw [Set.uIoc_of_le zero_le_one] at huI
    have hu1 : u < 1 := lt_of_le_of_ne huI.2 hu
    have hu0 : 0 < u := huI.1
    have hlo : 1 - u ≤ 1 - r * u := by nlinarith [hr.2]
    have hpos : 0 < 1 - u := by linarith
    have hup : 1 - r * u ≤ 1 := by nlinarith [hr.1]
    have hp : 0 ≤ u ^ (s - 1) := Real.rpow_nonneg hu0.le _
    have hq : 0 ≤ (1 - u) ^ α := Real.rpow_nonneg hpos.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) hp)]
    rcases le_or_gt 0 α with hα0 | hα0
    · have : (1 - r * u) ^ α ≤ 1 := Real.rpow_le_one (by linarith) hup hα0
      nlinarith [mul_nonneg hp hq]
    · have : (1 - r * u) ^ α ≤ (1 - u) ^ α := Real.rpow_le_rpow_of_nonpos hpos hlo hα0.le
      nlinarith [mul_nonneg hp hq]
  · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).add hB
  · filter_upwards [ae_ne_real 1] with u hu huI
    rw [Set.uIoc_of_le zero_le_one] at huI
    have hu1 : u < 1 := lt_of_le_of_ne huI.2 hu
    have hcont : ContinuousAt (fun r : ℝ => (1 - r * u) ^ α * u ^ (s - 1)) 1 := by
      refine ContinuousAt.mul ?_ continuousAt_const
      exact ContinuousAt.rpow_const (by fun_prop) (Or.inl (by simp; linarith))
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using this

/-- `(1 + e^{2ix})^α e^{iμx} = (2 cos x)^α e^{i(α+μ)x}` for `|x| < π/2`. -/
theorem one_add_exp_cpow_mul_exp {α μ x : ℝ} (hx : x ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    (1 + Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I) =
      (((2 : ℝ) ^ α * Real.cos x ^ α : ℝ) : ℂ) * Complex.exp (↑((α + μ) * x) * I) := by
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hx
  have hpi := Real.pi_pos
  have hfac : 1 + Complex.exp (↑(2 * x) * I) =
      ((2 * Real.cos x : ℝ) : ℂ) * Complex.exp (↑x * I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_two_mul, Complex.sin_two_mul]
    ring
  have hlog : Complex.log (((2 * Real.cos x : ℝ) : ℂ) * Complex.exp (↑x * I)) =
      (Real.log (2 * Real.cos x) : ℂ) + ↑x * I := by
    rw [Complex.log_ofReal_mul (by positivity) (Complex.exp_ne_zero _), Complex.log_exp]
    · simp; linarith [hx.1]
    · simp; linarith [hx.2]
  have hne : ((2 * Real.cos x : ℝ) : ℂ) * Complex.exp (↑x * I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.cos x).ne')
      (Complex.exp_ne_zero _)
  rw [hfac, Complex.cpow_def_of_ne_zero hne, hlog, ← Real.mul_rpow (by norm_num) hc.le,
    Real.rpow_def_of_pos (by positivity), Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- DLMF 5.12.5 in the range `a - 1 < b < a + 1`, by Abel summation of the binomial series
of `(1 + e^{2ix})^{a-1}`. -/
theorem integral_cos_rpow_mul_cos_of_lt {a b : ℝ} (ha : 0 < a) (h1 : a - 1 < b) (h2 : b < a + 1) :
    ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) =
      π * Real.Gamma a /
        ((2 : ℝ) ^ a * (Real.Gamma ((a + b + 1) / 2) * Real.Gamma ((a - b + 1) / 2))) := by
  set α := a - 1 with hαdef
  set μ := b - a + 1 with hμdef
  set s := μ / 2 with hsdef
  have hα : -1 < α := by linarith
  have hμ : 0 < μ := by linarith
  have hs0 : 0 < s := by positivity
  have hs1 : s < 1 := by rw [hsdef]; linarith
  -- The Abel-regularized identity `L(r) = sin(πs) R(r)` and its limit `r → 1⁻`.
  have hL := tendsto_integral_one_add_mul_exp hα μ
  have hR := ((Complex.continuous_ofReal.tendsto _).comp
    ((tendsto_integral_one_sub_mul hα hs0).const_mul (Real.sin (π * s))))
  have heq : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), (∫ x in (-(π / 2))..(π / 2),
      (1 + (r : ℂ) * Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I)) =
      (fun r : ℝ => ((Real.sin (π * s) *
        ∫ u in (0 : ℝ)..1, (1 - r * u) ^ α * u ^ (s - 1) : ℝ) : ℂ)) r := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hA := hasSum_integral_one_add_mul_exp α hμ hr.1.le hr.2
    have hB := Complex.hasSum_ofReal.mpr
      ((hasSum_integral_one_sub_mul α hs0 hs1 hr.1.le hr.2).mul_left (Real.sin (π * s)))
    exact hA.unique hB
  have hlim := tendsto_nhds_unique (hL.congr' heq) hR
  -- Identify the two limits.
  have hbeta : ∫ u in (0 : ℝ)..1, (1 - u) ^ α * u ^ (s - 1) =
      Real.Gamma s * Real.Gamma a / Real.Gamma (s + a) := by
    rw [← real_betaIntegral hs0 ha]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hαdef]
    ring
  have hleft : (∫ x in (-(π / 2))..(π / 2),
      (1 + Complex.exp (↑(2 * x) * I)) ^ (α : ℂ) * Complex.exp (↑(μ * x) * I)) =
      (((2 : ℝ) ^ α : ℝ) : ℂ) *
        ↑(2 * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ α * Real.cos (b * t)) := by
    rw [← integral_cos_rpow_mul_exp hα b, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_real (π / 2)] with x hx hxI
    rw [one_add_exp_cpow_mul_exp (mem_Ioo_of_mem_uIoc hx hxI),
      show α + μ = b by rw [hαdef, hμdef]; ring]
    push_cast
    ring
  rw [hleft, hbeta] at hlim
  have hreal : (2 : ℝ) ^ α *
      (2 * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ α * Real.cos (b * t)) =
      Real.sin (π * s) * (Real.Gamma s * Real.Gamma a / Real.Gamma (s + a)) := by
    exact_mod_cast hlim
  -- Euler's reflection formula.
  have hsin : 0 < Real.sin (π * s) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hrefl := Real.Gamma_mul_Gamma_one_sub s
  have hG1 : 0 < Real.Gamma (1 - s) := Real.Gamma_pos_of_pos (by linarith)
  have hGs : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs0
  have hGsa : 0 < Real.Gamma (s + a) := Real.Gamma_pos_of_pos (by linarith)
  have h2a : (2 : ℝ) ^ a = 2 ^ α * 2 := by
    rw [hαdef, Real.rpow_sub (by norm_num), Real.rpow_one]
    field_simp
  have hp : (a + b + 1) / 2 = s + a := by rw [hsdef, hμdef]; ring
  have hq : (a - b + 1) / 2 = 1 - s := by rw [hsdef, hμdef]; ring
  rw [hp, hq, h2a]
  have h2α : 0 < (2 : ℝ) ^ α := by positivity
  field_simp
  rw [eq_div_iff hsin.ne'] at hrefl
  have h3 : (2 : ℝ) ^ α * (2 * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ α * Real.cos (b * t)) *
      Real.Gamma (s + a) = Real.sin (π * s) * Real.Gamma s * Real.Gamma a := by
    rw [hreal]
    field_simp
  linear_combination Real.Gamma (1 - s) * h3 + Real.Gamma a * hrefl

/-- Integration by parts of `d/dt (cos^(a-1) t · sin (b t))`:
`(a - 1 + b) K(a, b) = (a - 1) K(a - 1, b - 1)`. -/
theorem integral_cos_rpow_mul_cos_shift {a : ℝ} (ha : 1 < a) (b : ℝ) :
    (a - 1 + b) * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) =
      (a - 1) * ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1 - 1) * Real.cos ((b - 1) * t) := by
  have hp : 0 < a - 1 := by linarith
  have hpi := Real.pi_pos
  have hsub : Set.uIcc 0 (π / 2) ⊆ Set.Icc (-(π / 2)) (π / 2) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  have hA := intervalIntegrable_cos_rpow_mul (β := a - 1 - 1) (by linarith)
    (g := fun t => Real.cos ((b - 1) * t)) (by fun_prop) hsub
  have hB := intervalIntegrable_cos_rpow_mul (β := a - 1) (by linarith)
    (g := fun t => Real.cos (b * t)) (by fun_prop) hsub
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith : (0 : ℝ) ≤ π / 2)
    (f := fun t => Real.cos t ^ (a - 1) * Real.sin (b * t))
    (f' := fun t => -(a - 1) * (Real.cos t ^ (a - 1 - 1) * Real.cos ((b - 1) * t)) +
      (a - 1 + b) * (Real.cos t ^ (a - 1) * Real.cos (b * t)))
    ((Real.continuous_cos.rpow_const fun _ => Or.inr hp.le).mul
      (by fun_prop : Continuous fun t : ℝ => Real.sin (b * t))).continuousOn
    (fun t ht => by
      have hc : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], ht.2⟩
      have h1 := (Real.hasDerivAt_cos t).rpow_const (p := a - 1) (Or.inl hc.ne')
      have h2 := (Real.hasDerivAt_sin (b * t)).comp t ((hasDerivAt_id t).const_mul b)
      refine (h1.mul h2).congr_deriv ?_
      have hcp : Real.cos t ^ (a - 1) = Real.cos t ^ (a - 1 - 1) * Real.cos t := by
        rw [← Real.rpow_add_one hc.ne', sub_add_cancel]
      rw [hcp, show (b - 1) * t = b * t - t by ring, Real.cos_sub]
      simp only [Function.comp_apply]
      ring)
    ((hA.const_mul _).add (hB.const_mul _))
  rw [intervalIntegral.integral_add (hA.const_mul _) (hB.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
  simp only [Real.cos_pi_div_two, Real.zero_rpow hp.ne', zero_mul, Real.cos_zero,
    Real.one_rpow, mul_zero, Real.sin_zero, sub_zero] at hftc
  linarith

/-- `∫₀^{π/2} cos^(a-1)t cos(-bt) dt = ∫₀^{π/2} cos^(a-1)t cos(bt) dt`. -/
theorem integral_cos_rpow_mul_cos_neg (a b : ℝ) :
    ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (-b * t) =
      ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) := by
  simp only [neg_mul, Real.cos_neg]

/-- DLMF 5.12.5 with the right-hand side written as `π Γ(a) / (2^a Γ(p) Γ(q))`. -/
theorem integral_cos_rpow_mul_cos {a b : ℝ} (ha : 0 < a) (hb : |b| < a + 1) :
    ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) =
      π * Real.Gamma a /
        ((2 : ℝ) ^ a * (Real.Gamma ((a + b + 1) / 2) * Real.Gamma ((a - b + 1) / 2))) := by
  suffices H : ∀ n : ℕ, ∀ a b : ℝ, 0 < a → a ≤ n → |b| < a + 1 →
      ∫ t in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) =
        π * Real.Gamma a /
          ((2 : ℝ) ^ a * (Real.Gamma ((a + b + 1) / 2) * Real.Gamma ((a - b + 1) / 2))) from
    H ⌈a⌉₊ a b ha (Nat.le_ceil a) hb
  intro n
  induction n with
  | zero => intro a b ha han _; norm_num at han; linarith
  | succ n ih =>
    intro a b ha han hb
    wlog hb0 : 0 ≤ b generalizing b with H'
    · have h := H' (-b) (by rwa [abs_neg]) (by linarith)
      rw [integral_cos_rpow_mul_cos_neg] at h
      rw [h, show a + -b + 1 = a - b + 1 by ring, show a - -b + 1 = a + b + 1 by ring,
        mul_comm (Real.Gamma ((a - b + 1) / 2))]
    have hb1 : b < a + 1 := (abs_lt.mp hb).2
    by_cases h : a - 1 < b
    · exact integral_cos_rpow_mul_cos_of_lt ha h hb1
    push Not at h
    rcases eq_or_lt_of_le (show 1 ≤ a by linarith) with h1 | h1
    · subst h1
      have hb' : b = 0 := by linarith
      subst hb'
      norm_num [Real.Gamma_one]
    · have hrec := integral_cos_rpow_mul_cos_shift h1 b
      have hih := ih (a - 1) (b - 1) (by linarith) (by push_cast at han; linarith)
        (abs_lt.mpr ⟨by linarith, by linarith⟩)
      rw [hih] at hrec
      have hpos : 0 < a - 1 + b := by linarith
      have e1 : a - 1 + (b - 1) + 1 = a + b - 1 := by ring
      have e2 : a - 1 - (b - 1) + 1 = a - b + 1 := by ring
      rw [e1, e2] at hrec
      have hGa : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
        rw [← Real.Gamma_add_one (by linarith : a - 1 ≠ 0)]; ring_nf
      have hGp : Real.Gamma ((a + b + 1) / 2) =
          (a + b - 1) / 2 * Real.Gamma ((a + b - 1) / 2) := by
        rw [← Real.Gamma_add_one (by linarith : (a + b - 1) / 2 ≠ 0)]; ring_nf
      have h2a : (2 : ℝ) ^ a = 2 * 2 ^ (a - 1) := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one]
        field_simp
      have g1 : 0 < Real.Gamma (a - 1) := Real.Gamma_pos_of_pos (by linarith)
      have g2 : 0 < Real.Gamma ((a + b - 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
      have g3 : 0 < Real.Gamma ((a - b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
      have h2 : 0 < (2 : ℝ) ^ (a - 1) := by positivity
      rw [hGa, hGp, h2a]
      field_simp at hrec ⊢
      rw [eq_div_iff (by linarith)]
      linear_combination hrec

end CosineBeta

/-- DLMF 5.12.5: `∫₀^{π/2} cos^(a-1)t cos(bt) dt = π / (2^a a B((a + b + 1)/2, (a - b + 1)/2))` for
`a > 0`, `|b| < a + 1`. -/
@[dlmf 5.12.E5]
theorem beta_cos_cos {a b : ℝ} (ha : 0 < a) (hba : |b| < a + 1) :
    ∫ t : ℝ in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) =
      π / (2 : ℝ) ^ a /
        (a * (Real.Gamma ((a + b + 1) / 2) * Real.Gamma ((a - b + 1) / 2) /
          Real.Gamma (a + 1))) := by
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hba
  rw [integral_cos_rpow_mul_cos ha hba, Real.Gamma_add_one ha.ne']
  have g1 : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have g2 : 0 < Real.Gamma ((a + b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have g3 : 0 < Real.Gamma ((a - b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < (2 : ℝ) ^ a := by positivity
  field_simp

/-- DLMF 5.12.6: `∫₀^π sin^(a-1)t e^(ibt) dt = π e^(iπb/2) / (2^(a-1) a B((a + b + 1)/2, (a - b +
1)/2))` for `a > 0`, `|b| < a + 1`. -/
@[dlmf 5.12.E6]
theorem beta_sin_exp {a b : ℝ} (ha : 0 < a) (hba : |b| < a + 1) :
    ∫ t : ℝ in (0 : ℝ)..π, (Real.sin t : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * b * t) =
      (π : ℂ) / (2 : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * π * b / 2) /
        ((a : ℂ) * betaIntegral ((a + b + 1 : ℂ) / 2) ((a - b + 1 : ℂ) / 2)) := by
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hba
  have hpi := Real.pi_pos
  -- Shift `t = x + π/2`.
  have hshift : ∫ t : ℝ in (0 : ℝ)..π, (Real.sin t : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * b * t) =
      ∫ x : ℝ in (-(π / 2))..(π / 2), (Real.sin (x + π / 2) : ℂ) ^ (a - 1 : ℂ) *
        Complex.exp (I * b * ↑(x + π / 2)) := by
    rw [intervalIntegral.integral_comp_add_right
      (fun t : ℝ => (Real.sin t : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * b * t))]
    congr 1 <;> ring
  have hcongr : ∀ x ∈ Set.uIcc (-(π / 2)) (π / 2),
      (Real.sin (x + π / 2) : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * b * ↑(x + π / 2)) =
        Complex.exp (I * π * b / 2) *
          (((Real.cos x ^ (a - 1) : ℝ) : ℂ) * Complex.exp (↑(b * x) * I)) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc hx
    rw [Real.sin_add_pi_div_two, Complex.ofReal_cpow hc,
      show ((a : ℂ) - 1) = ((a - 1 : ℝ) : ℂ) by push_cast; ring,
      mul_left_comm (Complex.exp _) _ _, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hshift, intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    integral_cos_rpow_mul_exp (by linarith) b, integral_cos_rpow_mul_cos ha hba]
  -- Evaluate the Beta integral.
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := ((a + b + 1 : ℂ) / 2)) (t := ((a - b + 1 : ℂ) / 2))
    (by simp; linarith) (by simp; linarith)
  have e1 : ((a + b + 1 : ℂ) / 2) = (((a + b + 1) / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((a - b + 1 : ℂ) / 2) = (((a - b + 1) / 2 : ℝ) : ℂ) := by push_cast; ring
  have e3 : ((a + b + 1 : ℂ) / 2) + ((a - b + 1 : ℂ) / 2) = ((a + 1 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e3] at hbeta
  have g0 : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have g1 : 0 < Real.Gamma ((a + b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have g2 : 0 < Real.Gamma ((a - b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have g3 : 0 < Real.Gamma (a + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hB : betaIntegral ((a + b + 1 : ℂ) / 2) ((a - b + 1 : ℂ) / 2) =
      ((Real.Gamma ((a + b + 1) / 2) * Real.Gamma ((a - b + 1) / 2) / Real.Gamma (a + 1) : ℝ)
        : ℂ) := by
    have hne : Complex.Gamma ((a + 1 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.Gamma_ofReal]; exact_mod_cast g3.ne'
    have hB' : betaIntegral ((a + b + 1 : ℂ) / 2) ((a - b + 1 : ℂ) / 2) =
        Complex.Gamma ((a + b + 1 : ℂ) / 2) * Complex.Gamma ((a - b + 1 : ℂ) / 2) /
          Complex.Gamma ((a + 1 : ℝ) : ℂ) := by
      rw [hbeta]; field_simp
    rw [hB', e1, e2, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    push_cast
    ring
  have h2 : (2 : ℂ) ^ (a - 1 : ℂ) = (((2 : ℝ) ^ (a - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num)]
    push_cast
    ring_nf
  rw [hB, h2, Real.Gamma_add_one ha.ne']
  have h2a : (2 : ℝ) ^ a = 2 * 2 ^ (a - 1) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
    field_simp
  rw [h2a]
  have h2p : 0 < (2 : ℝ) ^ (a - 1) := by positivity
  have hE : Complex.exp (I * π * b / 2) ≠ 0 := Complex.exp_ne_zero _
  have c0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have c1 : ((Real.Gamma a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast g0.ne'
  have c2 : ((Real.Gamma ((a + b + 1) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast g1.ne'
  have c3 : ((Real.Gamma ((a - b + 1) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast g2.ne'
  have c4 : (((2 : ℝ) ^ (a - 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2p.ne'
  push_cast
  field_simp

/-- The real form of `beta_on_Ioi`, together with integrability of the integrand. -/
theorem real_beta_on_Ioi {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun u : ℝ => u ^ (p - 1) / (1 + u) ^ (p + q)) (Set.Ioi 0) ∧
      ∫ u : ℝ in Set.Ioi 0, u ^ (p - 1) / (1 + u) ^ (p + q) =
        Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have hval : ∫ u : ℝ in Set.Ioi 0, u ^ (p - 1) / (1 + u) ^ (p + q) =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
    apply Complex.ofReal_injective
    have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (p : ℂ)) (t := (q : ℂ))
      (by simpa using hp) (by simpa using hq)
    have hne : Complex.Gamma ((p : ℂ) + q) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    push_cast
    rw [← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal,
      Complex.ofReal_add, eq_div_iff hne, hG, ← integral_complex_ofReal, mul_comm,
      ← beta_on_Ioi (a := (p : ℂ)) (b := (q : ℂ)) (by simpa using hp) (by simpa using hq)]
    congr 1
    refine setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) fun u hu => ?_
    have hu0 : (0 : ℝ) ≤ u := (Set.mem_Ioi.mp hu).le
    rw [Complex.ofReal_div, Complex.ofReal_cpow hu0, Complex.ofReal_cpow (by linarith)]
    push_cast
    rfl
  refine ⟨?_, hval⟩
  by_contra h
  rw [integral_undef h] at hval
  have := Real.Gamma_pos_of_pos hp
  have := Real.Gamma_pos_of_pos hq
  have := Real.Gamma_pos_of_pos (add_pos hp hq)
  have : 0 < Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by positivity
  linarith

/-- `cosh t ^ (2a)` written with exponentials, for the substitution `u = exp (2t)`. -/
theorem cosh_rpow_eq_exp_mul (a t : ℝ) :
    Real.cosh t ^ (2 * a) =
      Real.exp (-(2 * a * t)) * (1 + Real.exp (2 * t)) ^ (2 * a) / (2 : ℝ) ^ (2 * a) := by
  have h : Real.cosh t = Real.exp (-t) * (1 + Real.exp (2 * t)) / 2 := by
    rw [Real.cosh_eq, mul_add, ← Real.exp_add]
    ring_nf
  rw [h, Real.div_rpow (by positivity) (by norm_num), Real.mul_rpow (by positivity)
    (by positivity), ← Real.exp_mul]
  ring_nf

/-- `∫ exp(2ct) / cosh(t)^(2a) dt` over `ℝ`, by the substitution `u = exp (2t)` in
`real_beta_on_Ioi`. -/
theorem integral_exp_div_cosh_rpow {a c : ℝ} (hc : |c| < a) :
    Integrable (fun t : ℝ => Real.exp (2 * c * t) / Real.cosh t ^ (2 * a)) ∧
      ∫ t : ℝ, Real.exp (2 * c * t) / Real.cosh t ^ (2 * a) =
        (2 : ℝ) ^ (2 * a - 1) *
          (Real.Gamma (a + c) * Real.Gamma (a - c) / Real.Gamma (2 * a)) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hc
  -- The substitution `u = exp (2 t)` maps `ℝ` onto `(0, ∞)`.
  set f : ℝ → ℝ := fun t => Real.exp (2 * t) with hf
  set f' : ℝ → ℝ := fun t => 2 * Real.exp (2 * t) with hf'
  have hderiv : ∀ t ∈ (Set.univ : Set ℝ), HasDerivWithinAt f (f' t) Set.univ t := by
    intro t _
    refine HasDerivAt.hasDerivWithinAt ?_
    have h := ((hasDerivAt_id t).const_mul (2 : ℝ)).exp
    simp only [id, mul_one] at h
    exact h.congr_deriv (mul_comm _ _)
  have hinj : Set.InjOn f Set.univ := fun x _ y _ hxy => by
    simpa using Real.exp_injective hxy
  have himage : f '' Set.univ = Set.Ioi 0 := by
    rw [Set.image_univ]
    ext u
    refine ⟨fun ⟨t, ht⟩ => ht ▸ Real.exp_pos _, fun hu => ⟨Real.log u / 2, ?_⟩⟩
    simp only [hf]
    rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log hu]
  set g : ℝ → ℝ := fun u => u ^ (a + c - 1) / (1 + u) ^ (a + c + (a - c))
  obtain ⟨hint, hval⟩ := real_beta_on_Ioi (p := a + c) (q := a - c) (by linarith) (by linarith)
  have key := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj g
  have keyI := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj g
  rw [himage] at key keyI
  have hpt (t : ℝ) : Real.exp (2 * c * t) / Real.cosh t ^ (2 * a) =
      (2 : ℝ) ^ (2 * a - 1) * (|f' t| • g (f t)) := by
    simp only [hf, hf', g, smul_eq_mul]
    rw [abs_of_pos (by positivity), cosh_rpow_eq_exp_mul, ← Real.exp_mul,
      show a + c + (a - c) = 2 * a by ring, Real.rpow_sub (by norm_num), Real.rpow_one]
    field_simp
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  simp_rw [hpt]
  refine ⟨?_, ?_⟩
  · rw [← integrableOn_univ]
    exact (keyI.mp hint).const_mul _
  · rw [MeasureTheory.integral_const_mul, ← setIntegral_univ, ← key, hval,
      show a + c + (a - c) = 2 * a by ring]

/-- DLMF 5.12.7: `∫₀^∞ cosh(2bt)/cosh^(2a)t dt = 4^(a-1) B(a + b, a - b)` for `|b| < a`. -/
@[dlmf 5.12.E7]
theorem beta_cosh {a b : ℝ} (ha : |b| < a) :
    ∫ t : ℝ in Set.Ioi 0, Real.cosh (2 * b * t) / Real.cosh t ^ (2 * a) =
      (4 : ℝ) ^ (a - 1) *
        (Real.Gamma (a + b) * Real.Gamma (a - b) / Real.Gamma (2 * a)) := by
  obtain ⟨hI₁, hv₁⟩ := integral_exp_div_cosh_rpow ha
  obtain ⟨hI₂, hv₂⟩ := integral_exp_div_cosh_rpow (c := -b) (by rwa [abs_neg])
  have heven := integral_comp_abs (f := fun t => Real.cosh (2 * b * t) / Real.cosh t ^ (2 * a))
  have habs (t : ℝ) : Real.cosh (2 * b * |t|) / Real.cosh |t| ^ (2 * a) =
      (1 / 2) * (Real.exp (2 * b * t) / Real.cosh t ^ (2 * a)) +
        (1 / 2) * (Real.exp (2 * -b * t) / Real.cosh t ^ (2 * a)) := by
    rw [Real.cosh_abs]
    rcases abs_choice t with h | h <;> rw [h] <;>
      simp only [Real.cosh_eq] <;> ring_nf
  simp only [habs] at heven
  rw [integral_add (hI₁.const_mul _) (hI₂.const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hv₁, hv₂, sub_neg_eq_add,
    show a + -b = a - b by ring, mul_comm (Real.Gamma (a - b))] at heven
  have h4 : (4 : ℝ) ^ (a - 1) = (2 : ℝ) ^ (2 * a - 1) / 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
      show 2 * (a - 1) = 2 * a - 1 - 1 by ring, Real.rpow_sub_one two_ne_zero]
  rw [h4]
  linear_combination (-1 / 2 : ℝ) * heven

end DLMF.Gamma
end
end
