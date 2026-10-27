/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Integrals

/-!
# Legendre polynomials: bounds and expansions (Temme §§6.8–6.9.1)

Laplace's integral `P_n(cos θ) = (1/π) ∫₀^π (cos θ + i sin θ cos φ)^n dφ` is proved in
`DLMF.OrthogonalPolynomials.Integrals` (`legendre_laplace_integral`). Following Temme it gives
the bounds of this file. The orthogonality relation `legendre_orthogonality` gives the
mean-square optimality of truncated Legendre expansions.

## Main results

* `norm_legendrePolyP_le_one`: `|P_n(x)| ≤ 1` on `[-1, 1]` (Temme (6.52)).
* `norm_legendrePolyP_cos_le`: `|P_n(cos θ)| ≤ √(π/(2n)) / sin θ` for `n ≥ 1` (Temme (6.53)).
* `conj_legendrePolyP`: `P_n` is real on the real line.
* `integral_norm_sub_sum_legendrePolyP_sq`: the mean-square error identity (Temme (6.61)).
* `integral_norm_sub_sum_legendreCoeff_sq_le`: the truncated Legendre series is the best
  mean-square polynomial approximation.
* `sum_legendreCoeff_sq_le`: Bessel's inequality (Temme (6.62)).
* `besselJ_zero_eq_integral`, `legendre_exponential_generating_function`: Bessel's integral
  `J₀(u) = (1/π) ∫₀^π e^{iu cos φ} dφ` and `∑ Pₙ(x) zⁿ/n! = e^{xz} J₀(z√(1-x²))` (DLMF 18.12.12).
* `ultrasphPoly_bessel_generating_function`: the Gegenbauer analogue (DLMF 18.12.6), from the
  same termwise integration of Laplace's integral, against the weight `sin^{2λ-1} φ`, and
  Poisson's integral for `J_{λ-1/2}`.
* `tendsto_sqrt_mul_legendrePolyP_cos`: the Laplace–Heine formula
  `√n P_n(cos θ) - √(2/(π sin θ)) cos((n + 1/2)θ - π/4) → 0` (Temme §6.8.4). Laplace's integral
  is split at `π/2`, rescaled by `√n`, and passed to the limit by dominated convergence, with
  the Gaussian majorant of Temme's bound.

The Dirichlet–Mehler formula and Stieltjes' full asymptotic expansion are not yet formalized.
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Real Topology Nat ComplexConjugate
open DLMF.Hypergeometric
open DLMF.Bessel

noncomputable section

namespace DLMF.OrthogonalPolynomials

theorem norm_laplace_integrand (θ t : ℝ) :
    ‖(Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t‖ =
      Real.sqrt (1 - Real.sin θ ^ 2 * Real.sin t ^ 2) := by
  rw [show (Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t =
    (Real.cos θ : ℂ) + ((Real.sin θ * Real.cos t : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_add_mul_I]
  congr 1
  have h1 := Real.cos_sq_add_sin_sq θ
  have h2 := Real.cos_sq_add_sin_sq t
  linear_combination h1 + Real.sin θ ^ 2 * h2

/-- `|P_n(cos θ)| ≤ 1` (Temme (6.52)), from Laplace's integral. -/
theorem norm_legendrePolyP_cos_le_one (n : ℕ) (θ : ℝ) : ‖legendrePolyP n (Real.cos θ)‖ ≤ 1 := by
  rw [legendre_laplace_integral, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π) (C := 1)
    (f := fun t : ℝ => ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n) (fun t _ => by
      rw [norm_pow, norm_laplace_integrand]
      refine pow_le_one₀ (Real.sqrt_nonneg _) ?_
      rw [Real.sqrt_le_one]
      nlinarith [sq_nonneg (Real.sin θ * Real.sin t)])
  rw [one_mul, sub_zero, abs_of_pos Real.pi_pos] at h
  calc π⁻¹ * ‖∫ t : ℝ in (0 : ℝ)..π, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n‖
      ≤ π⁻¹ * π := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr Real.pi_pos.le)
    _ = 1 := inv_mul_cancel₀ Real.pi_ne_zero

/-- `|P_n(x)| ≤ 1` on `[-1, 1]` (Temme (6.52); DLMF 18.14.1 with `α = β = 0`). -/
theorem norm_legendrePolyP_le_one (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) : ‖legendrePolyP n x‖ ≤ 1 := by
  have := norm_legendrePolyP_cos_le_one n (Real.arccos x)
  rwa [Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2] at this

/-- The Gaussian majorant `|cos θ + i sin θ cos t|ⁿ ≤ exp(-(n sin²θ / 2) sin² t)`. -/
theorem norm_laplace_integrand_pow_le (n : ℕ) (θ t : ℝ) :
    ‖((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n‖ ≤
      Real.exp (-(n * Real.sin θ ^ 2 / 2) * Real.sin t ^ 2) := by
  set s := Real.sin θ with hs
  rw [norm_pow, norm_laplace_integrand]
  have hu : Real.sqrt (1 - s ^ 2 * Real.sin t ^ 2) ≤ Real.exp (-(s ^ 2 * Real.sin t ^ 2) / 2) := by
    rw [Real.sqrt_le_iff]
    refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [← Real.exp_nat_mul]
    have := Real.add_one_le_exp (-(s ^ 2 * Real.sin t ^ 2))
    calc 1 - s ^ 2 * Real.sin t ^ 2 = -(s ^ 2 * Real.sin t ^ 2) + 1 := by ring
      _ ≤ Real.exp (-(s ^ 2 * Real.sin t ^ 2)) := this
      _ = _ := by congr 1; push_cast; ring
  calc Real.sqrt (1 - s ^ 2 * Real.sin t ^ 2) ^ n
      ≤ Real.exp (-(s ^ 2 * Real.sin t ^ 2) / 2) ^ n :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hu n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- **Temme's bound** (6.53): for `n ≥ 1` and `0 < θ < π`,
`|P_n(cos θ)| ≤ √(π/(2n)) / sin θ`, from Laplace's integral, `1 - u ≤ e^{-u}` and Jordan's
inequality `sin φ ≥ 2φ/π`. -/
theorem norm_legendrePolyP_cos_le (n : ℕ) (hn : 0 < n) {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < π) :
    ‖legendrePolyP n (Real.cos θ)‖ ≤ Real.sqrt (π / (2 * n)) / Real.sin θ := by
  set s := Real.sin θ with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set h : ℝ → ℝ := fun t => Real.exp (-(n * s ^ 2 / 2) * Real.sin t ^ 2) with hh
  set a : ℝ := 2 * n * s ^ 2 / π ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have hcont : Continuous h := by fun_prop
  have hpt : ∀ t : ℝ, ‖((Real.cos θ : ℂ) + I * s * Real.cos t) ^ n‖ ≤ h t :=
    fun t => norm_laplace_integrand_pow_le n θ t
  -- `h` is symmetric about `π/2` and Gaussian-dominated on `[0, π/2]`
  have hsym : ∫ t in (0 : ℝ)..π, h t = 2 * ∫ t in (0 : ℝ)..(π / 2), h t := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0)
      (b := π / 2) (c := π) (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    have h2 := intervalIntegral.integral_comp_sub_left h (a := 0) (b := π / 2) π
    rw [show π - π / 2 = π / 2 by ring, sub_zero] at h2
    have h3 : ∫ t in (0 : ℝ)..(π / 2), h (π - t) = ∫ t in (0 : ℝ)..(π / 2), h t := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hh, Real.sin_pi_sub]
    rw [← h1, ← h2, h3]
    ring
  have hgauss : ∫ t in (0 : ℝ)..(π / 2), h t ≤ Real.sqrt (π / a) / 2 := by
    rw [← integral_gaussian_Ioi a, intervalIntegral.integral_of_le (by positivity)]
    have hk : IntegrableOn (fun t : ℝ => Real.exp (-a * t ^ 2)) (Ioi 0) :=
      (integrable_exp_neg_mul_sq ha0).integrableOn
    calc ∫ t in Ioc (0 : ℝ) (π / 2), h t ≤ ∫ t in Ioc (0 : ℝ) (π / 2), Real.exp (-a * t ^ 2) := by
          refine setIntegral_mono_on (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
            (hk.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
          simp only [hh]
          refine Real.exp_le_exp.mpr ?_
          have hj := Real.mul_le_sin ht.1.le ht.2
          have hj2 : (2 / π * t) ^ 2 ≤ Real.sin t ^ 2 := pow_le_pow_left₀ (by
            have := ht.1; positivity) hj 2
          have hc : 0 ≤ n * s ^ 2 / 2 := by positivity
          calc -(n * s ^ 2 / 2) * Real.sin t ^ 2 ≤ -(n * s ^ 2 / 2) * (2 / π * t) ^ 2 :=
                mul_le_mul_of_nonpos_left hj2 (by linarith)
            _ = -a * t ^ 2 := by rw [ha]; field_simp
      _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-a * t ^ 2) :=
          setIntegral_mono_set hk (Eventually.of_forall fun t => (Real.exp_pos _).le)
            (Eventually.of_forall Ioc_subset_Ioi_self)
  -- assemble
  rw [legendre_laplace_integral, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have hI : ‖∫ t : ℝ in (0 : ℝ)..π, ((Real.cos θ : ℂ) + I * s * Real.cos t) ^ n‖ ≤
      ∫ t in (0 : ℝ)..π, h t :=
    (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans
      (intervalIntegral.integral_mono_on Real.pi_pos.le
        ((by fun_prop : Continuous fun t : ℝ =>
          ‖((Real.cos θ : ℂ) + I * s * Real.cos t) ^ n‖).intervalIntegrable 0 π)
        (hcont.intervalIntegrable 0 π) fun t _ => hpt t)
  have hsqrt : Real.sqrt (π / a) = Real.sqrt (π / (2 * n)) * (π / s) := by
    rw [show π / a = π / (2 * n) * (π / s) ^ 2 by rw [ha]; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  calc π⁻¹ * ‖∫ t : ℝ in (0 : ℝ)..π, ((Real.cos θ : ℂ) + I * s * Real.cos t) ^ n‖
      ≤ π⁻¹ * (2 * (Real.sqrt (π / a) / 2)) := by
        refine mul_le_mul_of_nonneg_left (hI.trans ?_) (inv_nonneg.mpr Real.pi_pos.le)
        rw [hsym]; linarith
    _ = Real.sqrt (π / (2 * n)) / s := by
        rw [hsqrt]; field_simp

/-! ### Expansions in Legendre polynomials (Temme §6.9.1) -/

/-- Legendre polynomials are real on the real line. -/
theorem conj_legendrePolyP (n : ℕ) (x : ℝ) : conj (legendrePolyP n x) = legendrePolyP n x := by
  suffices h : ∀ n : ℕ, conj (legendrePolyP n x) = legendrePolyP n x ∧
      conj (legendrePolyP (n + 1) x) = legendrePolyP (n + 1) x from (h n).1
  intro n
  induction n with
  | zero => simp [legendrePolyP_zero]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hr := legendrePolyP_recurrence n x
    have hn : (n + 2 : ℂ) ≠ 0 := by norm_cast
    have hc := congrArg conj hr
    simp only [map_mul, map_sub, map_add, map_natCast, map_ofNat, map_one, Complex.conj_ofReal,
      ih.1, ih.2] at hc
    apply mul_left_cancel₀ hn
    rw [show n + 1 + 1 = n + 2 by ring]
    linear_combination hc - hr

theorem continuous_legendrePolyP_ofReal (n : ℕ) : Continuous fun x : ℝ => legendrePolyP n x :=
  (continuous_iff_continuousAt.mpr fun z =>
    ((analyticOnNhd_jacobiPolyP 0 0 n) z (Set.mem_univ z)).continuousAt).comp continuous_ofReal

/-- The Legendre coefficient `c_n = (n + 1/2) ∫₋₁¹ f(x) P_n(x) dx` (Temme (6.59)). -/
def legendreCoeff (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  (n + 1 / 2) * ∫ x : ℝ in (-1 : ℝ)..1, f x * legendrePolyP n x

theorem integral_mul_legendrePolyP_eq (f : ℝ → ℂ) (n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, f x * legendrePolyP n x = 2 / (2 * n + 1) * legendreCoeff f n := by
  rw [legendreCoeff]
  have h : (2 * (n : ℂ) + 1) ≠ 0 := by norm_cast
  field_simp

/-- **The mean-square error of a truncated Legendre expansion** (Temme (6.60)–(6.61)):
for `f` continuous on `[-1,1]` and any coefficients `a`,
`∫|f - ∑_{n<N} aₙ Pₙ|² = ∫|f|² - ∑ 2/(2n+1) |cₙ|² + ∑ 2/(2n+1) |aₙ - cₙ|²`. -/
theorem integral_norm_sub_sum_legendrePolyP_sq {f : ℝ → ℂ} (hf : ContinuousOn f (Icc (-1) 1))
    (a : ℕ → ℂ) (N : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, ‖f x - ∑ n ∈ Finset.range N, a n * legendrePolyP n x‖ ^ 2 =
      (∫ x : ℝ in (-1 : ℝ)..1, ‖f x‖ ^ 2) -
        ∑ n ∈ Finset.range N, 2 / (2 * n + 1) * ‖legendreCoeff f n‖ ^ 2 +
        ∑ n ∈ Finset.range N, 2 / (2 * n + 1) * ‖a n - legendreCoeff f n‖ ^ 2 := by
  set c := legendreCoeff f with hc
  set P : ℕ → ℝ → ℂ := fun n x => legendrePolyP n x with hP
  have hU : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hPc : ∀ n, Continuous (P n) := continuous_legendrePolyP_ofReal
  have hfc : ContinuousOn (fun x => conj (f x)) (Icc (-1) 1) :=
    Complex.continuous_conj.comp_continuousOn hf
  have hII : ∀ {u : ℝ → ℂ}, ContinuousOn u (Icc (-1) 1) →
      IntervalIntegrable u volume (-1) 1 := fun hu => (hU ▸ hu).intervalIntegrable
  -- the three families of integrals
  have hF1 : ∀ n, ∫ x : ℝ in (-1 : ℝ)..1, f x * P n x = 2 / (2 * n + 1) * c n :=
    fun n => integral_mul_legendrePolyP_eq f n
  have hF2 : ∀ n, ∫ x : ℝ in (-1 : ℝ)..1, P n x * conj (f x) = 2 / (2 * n + 1) * conj (c n) := by
    intro n
    have h := congrArg conj (hF1 n)
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_conj] at h
    simp only [map_mul, map_div₀, map_add, map_one, map_ofNat, map_natCast] at h
    rw [intervalIntegral.integral_of_le (by norm_num), ← h]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    simp only [hP, map_mul, conj_legendrePolyP]
    ring
  have hF3 : ∀ m n, ∫ x : ℝ in (-1 : ℝ)..1, P m x * P n x =
      if m = n then (2 : ℂ) / (2 * (n : ℂ) + 1) else 0 := legendre_orthogonality
  set h : ℕ → ℂ := fun n => 2 / (2 * n + 1) with hh
  -- integrability of the pieces
  have hfP : ∀ n, IntervalIntegrable (fun x => f x * P n x) volume (-1) 1 :=
    fun n => hII (hf.mul (hPc n).continuousOn)
  have hPf : ∀ n, IntervalIntegrable (fun x => P n x * conj (f x)) volume (-1) 1 :=
    fun n => hII ((hPc n).continuousOn.mul hfc)
  have hPP : ∀ m n, IntervalIntegrable (fun x => P m x * P n x) volume (-1) 1 :=
    fun m n => ((hPc m).mul (hPc n)).intervalIntegrable _ _
  have hff : IntervalIntegrable (fun x => f x * conj (f x)) volume (-1) 1 := hII (hf.mul hfc)
  -- the pointwise expansion
  have hexp : ∀ x : ℝ, ((‖f x - ∑ n ∈ Finset.range N, a n * legendrePolyP n x‖ ^ 2 : ℝ) : ℂ) =
      f x * conj (f x) - ∑ n ∈ Finset.range N, conj (a n) * (f x * P n x) -
        ∑ n ∈ Finset.range N, a n * (P n x * conj (f x)) +
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, a m * conj (a n) * (P m x * P n x) := by
    intro x
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sub, map_sum]
    simp only [map_mul, conj_legendrePolyP, hP]
    rw [sub_mul, mul_sub, mul_sub, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul_sum]
    have e1 : ∑ i ∈ Finset.range N, f x * (conj (a i) * legendrePolyP i x) =
        ∑ n ∈ Finset.range N, conj (a n) * (f x * legendrePolyP n x) :=
      Finset.sum_congr rfl fun n _ => by ring
    have e2 : ∑ i ∈ Finset.range N, a i * legendrePolyP i x * conj (f x) =
        ∑ n ∈ Finset.range N, a n * (legendrePolyP n x * conj (f x)) :=
      Finset.sum_congr rfl fun n _ => by ring
    have e3 : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        a i * legendrePolyP i x * (conj (a j) * legendrePolyP j x) =
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          a m * conj (a n) * (legendrePolyP m x * legendrePolyP n x) :=
      Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
    rw [e1, e2, e3]
    ring
  -- integrate
  have hL : (((∫ x : ℝ in (-1 : ℝ)..1,
      ‖f x - ∑ n ∈ Finset.range N, a n * legendrePolyP n x‖ ^ 2) : ℝ) : ℂ) =
      (∫ x : ℝ in (-1 : ℝ)..1, f x * conj (f x)) -
        ∑ n ∈ Finset.range N, h n * (conj (a n) * c n + a n * conj (c n) - a n * conj (a n)) := by
    have hS1 : IntervalIntegrable (fun x => ∑ n ∈ Finset.range N, conj (a n) * (f x * P n x))
        volume (-1) 1 := hII (continuousOn_finsetSum _ fun n _ =>
          continuousOn_const.mul (hf.mul (hPc n).continuousOn))
    have hS2 : IntervalIntegrable (fun x => ∑ n ∈ Finset.range N, a n * (P n x * conj (f x)))
        volume (-1) 1 := hII (continuousOn_finsetSum _ fun n _ =>
          continuousOn_const.mul ((hPc n).continuousOn.mul hfc))
    have hS3 : IntervalIntegrable (fun x => ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        a m * conj (a n) * (P m x * P n x)) volume (-1) 1 :=
      (continuous_finsetSum _ fun m _ => continuous_finsetSum _ fun n _ =>
        continuous_const.mul ((hPc m).mul (hPc n))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_ofReal, intervalIntegral.integral_congr fun x _ => hexp x,
      intervalIntegral.integral_add ((hff.sub hS1).sub hS2) hS3,
      intervalIntegral.integral_sub (hff.sub hS1) hS2, intervalIntegral.integral_sub hff hS1,
      intervalIntegral.integral_finsetSum fun n _ => (hfP n).const_mul _,
      intervalIntegral.integral_finsetSum fun n _ => (hPf n).const_mul _]
    have hD : ∫ x : ℝ in (-1 : ℝ)..1, ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        a m * conj (a n) * (P m x * P n x) = ∑ m ∈ Finset.range N, a m * conj (a m) * h m := by
      rw [intervalIntegral.integral_finsetSum (f := fun m x => ∑ n ∈ Finset.range N,
        a m * conj (a n) * (P m x * P n x)) fun m _ => (continuous_finsetSum _ fun n _ =>
          continuous_const.mul ((hPc m).mul (hPc n))).intervalIntegrable _ _]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [intervalIntegral.integral_finsetSum (f := fun n x => a m * conj (a n) * (P m x * P n x))
        fun n _ => (hPP m n).const_mul _]
      simp only [intervalIntegral.integral_const_mul, hF3, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq (Finset.range N) m, if_pos hm]
    rw [hD]
    simp only [intervalIntegral.integral_const_mul, hF1, hF2]
    rw [sub_sub, sub_add, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hh]
    ring
  have hR : (((∫ x : ℝ in (-1 : ℝ)..1, ‖f x‖ ^ 2) -
      ∑ n ∈ Finset.range N, 2 / (2 * n + 1) * ‖c n‖ ^ 2 +
      ∑ n ∈ Finset.range N, 2 / (2 * n + 1) * ‖a n - c n‖ ^ 2 : ℝ) : ℂ) =
      (∫ x : ℝ in (-1 : ℝ)..1, f x * conj (f x)) -
        ∑ n ∈ Finset.range N, h n * (conj (a n) * c n + a n * conj (c n) - a n * conj (a n)) := by
    push_cast
    rw [← intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_pow, ← Complex.mul_conj']
    rw [sub_add, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hh, map_sub]
    ring
  exact Complex.ofReal_injective (hL.trans hR.symm)

/-- **Optimality of the Legendre coefficients** (Temme §6.9.1): among all polynomials
`∑_{n<N} aₙ Pₙ`, the truncated Legendre series of `f` minimizes the mean-square error. -/
theorem integral_norm_sub_sum_legendreCoeff_sq_le {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1) 1)) (a : ℕ → ℂ) (N : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, ‖f x - ∑ n ∈ Finset.range N,
        legendreCoeff f n * legendrePolyP n x‖ ^ 2 ≤
      ∫ x : ℝ in (-1 : ℝ)..1, ‖f x - ∑ n ∈ Finset.range N, a n * legendrePolyP n x‖ ^ 2 := by
  rw [integral_norm_sub_sum_legendrePolyP_sq hf, integral_norm_sub_sum_legendrePolyP_sq hf]
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, Finset.sum_const_zero, add_zero]
  have : 0 ≤ ∑ n ∈ Finset.range N, 2 / (2 * (n : ℝ) + 1) * ‖a n - legendreCoeff f n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  linarith

/-- **Bessel's inequality** for Legendre expansions (Temme (6.62)):
`∑_{n<N} 2/(2n+1) |cₙ|² ≤ ∫₋₁¹ |f|²`. -/
theorem sum_legendreCoeff_sq_le {f : ℝ → ℂ} (hf : ContinuousOn f (Icc (-1) 1)) (N : ℕ) :
    ∑ n ∈ Finset.range N, 2 / (2 * (n : ℝ) + 1) * ‖legendreCoeff f n‖ ^ 2 ≤
      ∫ x : ℝ in (-1 : ℝ)..1, ‖f x‖ ^ 2 := by
  have h := integral_norm_sub_sum_legendrePolyP_sq hf (legendreCoeff f) N
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, Finset.sum_const_zero, add_zero] at h
  have h0 : 0 ≤ ∫ x : ℝ in (-1 : ℝ)..1,
      ‖f x - ∑ n ∈ Finset.range N, legendreCoeff f n * legendrePolyP n x‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => by positivity
  linarith

/-! ### Large-degree asymptotics (Temme §6.8.4) -/

/-- The rotated Laplace integrand `u(ψ) = 1 - κ sin²(ψ/2)`, `κ = 2i sin θ e^{-iθ}`. -/
def laplaceKappa (θ : ℝ) : ℂ := 2 * Real.sin θ ^ 2 + 2 * I * Real.sin θ * Real.cos θ

theorem laplace_integrand_eq (θ ψ : ℝ) :
    (Real.cos θ : ℂ) + I * Real.sin θ * Real.cos ψ =
      Complex.exp (θ * I) * (1 - laplaceKappa θ * Real.sin (ψ / 2) ^ 2) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, laplaceKappa]
  have h1 : Real.cos ψ = 1 - 2 * Real.sin (ψ / 2) ^ 2 := by
    have h := Real.cos_two_mul (ψ / 2)
    rw [show 2 * (ψ / 2) = ψ by ring] at h
    have h2 := Real.sin_sq_add_cos_sq (ψ / 2)
    linarith
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.cos_sq_add_sin_sq]
    simp
  rw [h1]
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  linear_combination ((2 : ℂ) * I * Real.sin θ * (Real.sin (ψ / 2) : ℂ) ^ 2) * hcs +
    (2 * Real.sin θ ^ 2 * Real.cos θ * (Real.sin (ψ / 2) : ℂ) ^ 2) * Complex.I_sq

/-- Splitting Laplace's integral at `π/2`: the two halves are complex conjugate. -/
theorem integral_laplace_eq_add_conj (n : ℕ) (θ : ℝ) :
    ∫ t : ℝ in (0 : ℝ)..π, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n =
      (∫ t : ℝ in (0 : ℝ)..(π / 2), ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n) +
        conj (∫ t : ℝ in (0 : ℝ)..(π / 2), ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n) := by
  set g : ℝ → ℂ := fun t => ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n with hg
  have hgc : Continuous g := by fun_prop
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0)
    (b := π / 2) (c := π) (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
  have h2 := intervalIntegral.integral_comp_sub_left g (a := 0) (b := π / 2) π
  rw [show π - π / 2 = π / 2 by ring, sub_zero] at h2
  rw [← h1, ← h2]
  congr 1
  rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity),
    ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  simp only [hg, map_pow, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Real.cos_pi_sub]
  push_cast
  ring

theorem laplaceKappa_eq (θ : ℝ) : laplaceKappa θ =
    ((2 * Real.sin θ ^ 2 : ℝ) : ℂ) + ((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ) * I := by
  rw [laplaceKappa]; push_cast; ring

theorem laplaceKappa_re (θ : ℝ) : (laplaceKappa θ).re = 2 * Real.sin θ ^ 2 := by
  rw [laplaceKappa_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

theorem norm_one_sub_laplaceKappa_pow_le (n : ℕ) (θ ψ : ℝ) :
    ‖(1 - laplaceKappa θ * Real.sin (ψ / 2) ^ 2) ^ n‖ ≤
      Real.exp (-(n * Real.sin θ ^ 2 / 2) * Real.sin ψ ^ 2) := by
  have h := norm_laplace_integrand_pow_le n θ ψ
  rwa [laplace_integrand_eq, mul_pow, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow,
    one_mul] at h

/-- `n sin²(t / (2√n)) → t²/4`. -/
theorem tendsto_nat_mul_sin_sq (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.sin (t / (2 * Real.sqrt n)) ^ 2) atTop (𝓝 (t ^ 2 / 4)) := by
  have hx : Tendsto (fun n : ℕ => t / (2 * Real.sqrt n)) atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ => 2 * Real.sqrt n) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop two_pos
    exact tendsto_const_nhds.div_atTop hs
  have hs := (Real.continuous_sinc.tendsto 0).comp hx
  rw [Real.sinc_zero] at hs
  have h2 := (hs.pow 2).const_mul (t ^ 2 / 4)
  rw [one_pow, mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have hsq0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  by_cases ht : t = 0
  · simp [ht]
  · have hx0 : t / (2 * Real.sqrt n) ≠ 0 := by positivity
    simp only [Function.comp_apply]
    rw [Real.sinc_of_ne_zero hx0]
    field_simp
    rw [hsq]
    ring

/-- **The local Laplace limit**: `√n ∫₀^{π/2} (1 - κ sin²(ψ/2))ⁿ dψ → ∫₀^∞ e^{-κt²/4} dt`. -/
theorem tendsto_sqrt_mul_integral_laplace_half {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < π) :
    Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) *
      ∫ ψ : ℝ in (0 : ℝ)..(π / 2), (1 - laplaceKappa θ * Real.sin (ψ / 2) ^ 2) ^ n) atTop
      (𝓝 ((π / (laplaceKappa θ / 4)) ^ (1 / 2 : ℂ) / 2)) := by
  set κ := laplaceKappa θ with hκ
  set s := Real.sin θ with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  set L : ℕ → ℝ := fun n => π / 2 * Real.sqrt n with hL
  set G : ℕ → ℝ → ℂ := fun n => Set.indicator (Iic (L n))
    (fun t => (1 - κ * Real.sin (t / (2 * Real.sqrt n)) ^ 2) ^ n) with hG
  set c : ℝ := 2 * s ^ 2 / π ^ 2 with hc
  have hc0 : 0 < c := by positivity
  -- the rescaled integrals
  have hresc : ∀ n : ℕ, 0 < n → (Real.sqrt n : ℂ) *
      ∫ ψ : ℝ in (0 : ℝ)..(π / 2), (1 - κ * Real.sin (ψ / 2) ^ 2) ^ n =
      ∫ t in Ioi (0 : ℝ), G n t := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
    have h := intervalIntegral.integral_comp_div
      (fun ψ : ℝ => (1 - κ * Real.sin (ψ / 2) ^ 2) ^ n) hsq.ne' (a := 0) (b := L n)
    rw [zero_div, show L n / Real.sqrt n = π / 2 by rw [hL]; field_simp] at h
    rw [← Complex.real_smul, ← h, intervalIntegral.integral_of_le (by positivity),
      ← Ioi_inter_Iic, ← setIntegral_indicator measurableSet_Iic]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hG, Set.indicator]
    split_ifs <;> simp only [div_div, mul_comm (Real.sqrt n)]
  -- dominated convergence
  have hlim : Tendsto (fun n => ∫ t in Ioi (0 : ℝ), G n t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), Complex.exp (-(κ / 4) * (t : ℂ) ^ 2))) := by
    refine tendsto_integral_of_dominated_convergence (fun t => Real.exp (-c * t ^ 2)) ?_ ?_ ?_ ?_
    · intro n
      refine (Continuous.aestronglyMeasurable ?_).indicator measurableSet_Iic
      fun_prop
    · exact (integrable_exp_neg_mul_sq hc0).integrableOn
    · intro n
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht : (0 : ℝ) < t := ht
      simp only [hG, Set.indicator]
      split_ifs with htL
      · rcases Nat.eq_zero_or_pos n with h0 | hn
        · subst h0; simp [hL] at htL; linarith
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
        have hb := norm_one_sub_laplaceKappa_pow_le n θ (t / Real.sqrt n)
        rw [show t / Real.sqrt n / 2 = t / (2 * Real.sqrt n) by ring] at hb
        refine hb.trans (Real.exp_le_exp.mpr ?_)
        have hψ0 : 0 ≤ t / Real.sqrt n := by positivity
        have hψ1 : t / Real.sqrt n ≤ π / 2 := by
          rw [div_le_iff₀ hsq]; exact htL
        have hj := Real.mul_le_sin hψ0 hψ1
        have hj2 : (2 / π * (t / Real.sqrt n)) ^ 2 ≤ Real.sin (t / Real.sqrt n) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hj 2
        have hnn : (n : ℝ) * (t / Real.sqrt n) ^ 2 = t ^ 2 := by
          rw [div_pow, Real.sq_sqrt hn'.le]; field_simp
        have hk : 0 ≤ n * s ^ 2 / 2 := by positivity
        calc -(n * s ^ 2 / 2) * Real.sin (t / Real.sqrt n) ^ 2
            ≤ -(n * s ^ 2 / 2) * (2 / π * (t / Real.sqrt n)) ^ 2 :=
              mul_le_mul_of_nonpos_left hj2 (by linarith)
          _ = -c * t ^ 2 := by
              rw [hc, show -(n * s ^ 2 / 2) * (2 / π * (t / Real.sqrt n)) ^ 2 =
                -(2 * s ^ 2 / π ^ 2) * ((n : ℝ) * (t / Real.sqrt n) ^ 2) by ring, hnn]
      · rw [norm_zero]; exact (Real.exp_pos _).le
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht : (0 : ℝ) < t := ht
      have hev : ∀ᶠ n : ℕ in atTop, t ≤ L n := by
        have hL' : Tendsto L atTop atTop :=
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
            (by positivity)
        exact hL'.eventually_ge_atTop t
      have hpow := Complex.tendsto_one_add_pow_exp_of_tendsto
        (g := fun n : ℕ => -(κ * Real.sin (t / (2 * Real.sqrt n)) ^ 2)) (t := -(κ / 4) * t ^ 2)
        (by
          have h := ((Complex.continuous_ofReal.tendsto _).comp (tendsto_nat_mul_sin_sq t)).const_mul
            (-κ)
          convert h using 1
          · funext n; simp only [Function.comp_apply]; push_cast; ring
          · push_cast; ring)
      refine hpow.congr' ?_
      filter_upwards [hev] with n hn
      simp only [hG, Set.indicator, mem_Iic, if_pos hn]
      ring_nf
  have hκ4 : 0 < (κ / 4).re := by
    rw [Complex.div_ofNat_re, hκ, laplaceKappa_re]; positivity
  rw [integral_gaussian_complex_Ioi hκ4] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (hresc n hn).symm

/-- The Gaussian constant `(π/(κ/4))^{1/2}/2 = ½ √(2π / sin θ) e^{i(θ/2 - π/4)}`. -/
theorem laplace_gaussian_constant {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < π) :
    (π / (laplaceKappa θ / 4)) ^ (1 / 2 : ℂ) / 2 =
      ((Real.sqrt (2 * π / Real.sin θ) / 2 : ℝ) : ℂ) * Complex.exp (((θ / 2 - π / 4 : ℝ) : ℂ) * I) := by
  set s := Real.sin θ with hs
  set c := Real.cos θ with hc
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hr : 0 < 2 * π / s := by positivity
  set z : ℂ := (Real.log (2 * π / s) : ℂ) + ((θ - π / 2 : ℝ) : ℂ) * I with hz
  have hcs : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, hc, hs,
      Real.cos_sq_add_sin_sq]; simp
  have hsc : (s : ℂ) + I * c ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.zero_re] at this
    linarith
  have hs0' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have hk : laplaceKappa θ / 4 = (s / 2) * (s + I * c) := by rw [laplaceKappa]; ring
  have hinv : π / (laplaceKappa θ / 4) = (2 * π / s) * (s - I * c) := by
    rw [hk, div_eq_iff (mul_ne_zero (div_ne_zero hs0' two_ne_zero) hsc),
      show 2 * (π : ℂ) / s * (s - I * c) * (s / 2 * (s + I * c)) =
        π * (s / s) * (s ^ 2 - I ^ 2 * c ^ 2) by ring, div_self hs0', Complex.I_sq]
    linear_combination (-(π : ℂ)) * hcs
  have hexpz : Complex.exp z = π / (laplaceKappa θ / 4) := by
    rw [hinv, hz, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two,
      ← hs, ← hc]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_neg]
    ring
  have hlog : Complex.log (Complex.exp z) = z := by
    apply Complex.log_exp
    · simp only [hz, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]; nlinarith [Real.pi_pos]
    · simp only [hz, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]; nlinarith [Real.pi_pos]
  rw [← hexpz, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero z), hlog, hz]
  rw [show ((Real.log (2 * π / s) : ℂ) + ((θ - π / 2 : ℝ) : ℂ) * I) * (1 / 2) =
    ((Real.log (2 * π / s) / 2 : ℝ) : ℂ) + ((θ / 2 - π / 4 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_add, ← Complex.ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
  push_cast
  ring_nf

/-- **The Laplace–Heine asymptotic formula** (Temme §6.8.4; DLMF 18.15.1 for `α = β = 0`):
for `0 < θ < π`,
`√n P_n(cos θ) - √(2/(π sin θ)) cos((n + 1/2)θ - π/4) → 0` as `n → ∞`. -/
theorem tendsto_sqrt_mul_legendrePolyP_cos {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < π) :
    Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) * legendrePolyP n (Real.cos θ) -
      ((Real.sqrt (2 / (π * Real.sin θ)) * Real.cos ((n + 1 / 2) * θ - π / 4) : ℝ) : ℂ))
      atTop (𝓝 0) := by
  set κ := laplaceKappa θ with hκ
  set K : ℕ → ℂ := fun n => ∫ ψ : ℝ in (0 : ℝ)..(π / 2), (1 - κ * Real.sin (ψ / 2) ^ 2) ^ n
    with hK
  set A : ℂ := (π / (κ / 4)) ^ (1 / 2 : ℂ) / 2 with hA
  set e : ℕ → ℂ := fun n => Complex.exp ((n * θ : ℝ) * I) with he
  have hnorme : ∀ n, ‖e n‖ = 1 := fun n => Complex.norm_exp_ofReal_mul_I _
  -- `P_n(cos θ) = π⁻¹ (e_n K_n + conj (e_n K_n))`
  have hP : ∀ n : ℕ, legendrePolyP n (Real.cos θ) = (π : ℂ)⁻¹ * (e n * K n + conj (e n * K n)) := by
    intro n
    rw [legendre_laplace_integral, integral_laplace_eq_add_conj]
    have hJ : ∫ t : ℝ in (0 : ℝ)..(π / 2), ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n =
        e n * K n := by
      rw [hK, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [he]
      rw [laplace_integrand_eq, mul_pow, ← Complex.exp_nat_mul]
      congr 2
      push_cast; ring
    rw [hJ]
  -- the oscillating main term
  have hmain : ∀ n : ℕ, (π : ℂ)⁻¹ * (e n * A + conj (e n * A)) =
      ((Real.sqrt (2 / (π * Real.sin θ)) * Real.cos ((n + 1 / 2) * θ - π / 4) : ℝ) : ℂ) := by
    intro n
    have hs0 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
    rw [hA, hκ, laplace_gaussian_constant hθ hθπ]
    set r : ℝ := Real.sqrt (2 * π / Real.sin θ) / 2 with hr
    set ph : ℝ := (n + 1 / 2) * θ - π / 4 with hph
    have hcomb : e n * ((r : ℂ) * Complex.exp (((θ / 2 - π / 4 : ℝ) : ℂ) * I)) =
        (r : ℂ) * ((Real.cos ph : ℂ) + (Real.sin ph : ℂ) * I) := by
      rw [he, mul_left_comm, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add,
        show n * θ + (θ / 2 - π / 4) = ph by rw [hph]; ring, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [hcomb]
    simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
    have hsq : Real.sqrt (2 * π / Real.sin θ) = π * Real.sqrt (2 / (π * Real.sin θ)) := by
      rw [show 2 * π / Real.sin θ = π ^ 2 * (2 / (π * Real.sin θ)) by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq Real.pi_pos.le]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [hr, hsq]
    push_cast
    field_simp
    ring
  have hlim := tendsto_sqrt_mul_integral_laplace_half hθ hθπ
  have hΔ : Tendsto (fun n : ℕ => e n * ((Real.sqrt n : ℂ) * K n - A)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) * K n - A) atTop (𝓝 0) := by
      have := hlim.sub_const A
      rwa [sub_self] at this
    refine squeeze_zero_norm (fun n => ?_) (tendsto_norm_zero.comp h0)
    rw [norm_mul, hnorme, one_mul]; rfl
  have hfin := ((hΔ.add (Complex.continuous_conj.tendsto 0 |>.comp hΔ)).const_mul
    ((π : ℂ)⁻¹))
  simp only [map_zero, add_zero, mul_zero] at hfin
  refine hfin.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [hP n, ← hmain n]
  simp only [map_mul, map_sub, Complex.conj_ofReal]
  ring

/-! ### The exponential generating function (Temme §6.7) -/

/-- Wallis' integrals on `[0, π]`: odd powers of `cos` integrate to zero. -/
theorem integral_cos_pow_odd_zero_pi (m : ℕ) : ∫ t in (0 : ℝ)..π, Real.cos t ^ (2 * m + 1) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, integral_cos_pow, ih]
    simp

/-- Wallis' integrals on `[0, π]`: `∫₀^π cos^{2m} = π (2m)! / (4^m (m!)²)`. -/
theorem integral_cos_pow_even_zero_pi (m : ℕ) :
    ∫ t in (0 : ℝ)..π, Real.cos t ^ (2 * m) = π * ((2 * m)! / (4 ^ m * (m ! : ℝ) ^ 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, integral_cos_pow, ih]
    simp only [Real.sin_pi, Real.sin_zero, mul_zero, sub_zero, zero_div, zero_add]
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ m, pow_succ]
    push_cast
    have hf : (m ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- Termwise integration over `[0, π]` of a power series in a bounded continuous function. -/
theorem hasSum_integral_pow_div_factorial {g : ℝ → ℂ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ 1) (u : ℂ) :
    HasSum (fun k : ℕ => ∫ t in (0 : ℝ)..π, (u * g t) ^ k / k !)
      (∫ t in (0 : ℝ)..π, Complex.exp (u * g t)) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k _ => ‖u‖ ^ k / k !) (fun k => (by fun_prop : Continuous fun t =>
      (u * g t) ^ k / (k ! : ℂ)).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun t _ => ?_)
    (Eventually.of_forall fun t _ => Real.summable_pow_div_factorial ‖u‖)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ => by
      simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (u * g t))
  rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast]
  gcongr
  calc ‖u‖ * ‖g t‖ ≤ ‖u‖ * 1 := by gcongr; exact hb t
    _ = ‖u‖ := mul_one _

/-- **Bessel's integral for `J₀`** (DLMF 10.9.1 with `n = 0`): for every complex `u`,
`J₀(u) = (1/π) ∫₀^π e^{iu cos φ} dφ`. -/
theorem besselJ_zero_eq_integral (u : ℂ) :
    besselJ 0 u = (π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..π, Complex.exp (I * u * Real.cos t) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hS := hasSum_integral_pow_div_factorial (g := fun t => (Real.cos t : ℂ))
    (by fun_prop) (fun t => by rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one t)
    (I * u)
  -- the terms
  have hterm : ∀ k : ℕ, ∫ t in (0 : ℝ)..π, (I * u * (Real.cos t : ℂ)) ^ k / k ! =
      (I * u) ^ k / k ! * ((∫ t in (0 : ℝ)..π, Real.cos t ^ k : ℝ) : ℂ) := by
    intro k
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast; ring
  simp only [hterm] at hS
  -- only even terms survive
  have hodd : ∀ k ∉ Set.range (fun m : ℕ => 2 * m), (I * u) ^ k / k ! *
      ((∫ t in (0 : ℝ)..π, Real.cos t ^ k : ℝ) : ℂ) = 0 := by
    intro k hk
    obtain ⟨m, rfl⟩ : Odd k := by
      rcases Nat.even_or_odd k with ⟨m, rfl⟩ | h
      · exact absurd ⟨m, by ring⟩ hk
      · exact h
    rw [integral_cos_pow_odd_zero_pi]; simp
  rw [← (show Function.Injective (fun m : ℕ => 2 * m) from fun a b h => by simpa using h).hasSum_iff
    hodd] at hS
  -- the Bessel series
  have hB := (hasFPowerSeriesOnBall_regularized0F1 (0 + 1)).hasSum_mul_pow
    (z := -(u ^ 2 / 4)) (by simp)
  rw [besselJ_eq_regularized, Complex.cpow_zero, one_mul]
  refine hB.unique ?_
  have h2 := hS.mul_left (π : ℂ)⁻¹
  convert h2 using 1
  · funext m
    simp only [Function.comp_apply, regularizedHGFunCoeff_empty, zero_add]
    rw [integral_cos_pow_even_zero_pi, show (1 : ℂ) + m = (m : ℂ) + 1 by ring,
      Complex.Gamma_nat_eq_factorial, pow_mul, mul_pow, Complex.I_sq]
    have hf : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
    have hf2 : ((2 * m)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (2 * m).factorial_ne_zero
    push_cast
    field_simp
    rw [← mul_pow]
    ring_nf

/-- **The exponential generating function of Legendre polynomials** (DLMF 18.12.12):
`∑ Pₙ(x) zⁿ/n! = e^{xz} J₀(z √(1-x²))` for `|x| ≤ 1`. -/
@[dlmf 18.12.E12]
theorem legendre_exponential_generating_function {x : ℝ} (hx : |x| ≤ 1) (z : ℂ) :
    HasSum (fun n : ℕ => legendrePolyP n x / n.factorial * z ^ n)
      (exp (x * z) * besselJ 0 (z * Real.sqrt (1 - x ^ 2))) := by
  set θ := Real.arccos x with hθ
  have hc : Real.cos θ = x := Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2
  have hs : Real.sin θ = Real.sqrt (1 - x ^ 2) := Real.sin_arccos x
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hS := hasSum_integral_pow_div_factorial
    (g := fun t => (Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) (by fun_prop)
    (fun t => by
      rw [norm_laplace_integrand, Real.sqrt_le_one]
      nlinarith [sq_nonneg (Real.sin θ * Real.sin t)]) z
  have h := hS.mul_left (π : ℂ)⁻¹
  convert h using 1
  · funext n
    have hI : ∫ t in (0 : ℝ)..π, (z * ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t)) ^ n /
        n ! = z ^ n / n ! * ∫ t in (0 : ℝ)..π, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [mul_pow]; ring
    rw [hI, ← hc, legendre_laplace_integral]
    ring
  · rw [besselJ_zero_eq_integral, ← hs, ← hc, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]
    ring_nf

/-- Termwise integration over `[0, π]` of a power series in a bounded continuous function,
against an integrable weight. -/
theorem hasSum_integral_pow_div_factorial_mul {g : ℝ → ℂ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ 1) {ρ : ℝ → ℂ} (hρ : IntervalIntegrable ρ volume 0 π) (u : ℂ) :
    HasSum (fun k : ℕ => ∫ t in (0 : ℝ)..π, (u * g t) ^ k / k ! * ρ t)
      (∫ t in (0 : ℝ)..π, Complex.exp (u * g t) * ρ t) := by
  have hρm : AEStronglyMeasurable ρ (volume.restrict (Set.uIoc 0 π)) := by
    rw [uIoc_of_le Real.pi_pos.le]; exact hρ.1.aestronglyMeasurable
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k t => ‖u‖ ^ k / k ! * ‖ρ t‖)
    (fun k => ((by fun_prop : Continuous fun t =>
      (u * g t) ^ k / (k ! : ℂ)).aestronglyMeasurable).mul hρm)
    (fun k => Eventually.of_forall fun t _ => ?_)
    (Eventually.of_forall fun t _ => (Real.summable_pow_div_factorial ‖u‖).mul_right _)
    ?_
    (Eventually.of_forall fun t _ => by
      simpa only [Complex.exp_eq_exp_ℂ] using
        (NormedSpace.expSeries_div_hasSum_exp (u * g t)).mul_right (ρ t))
  · rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_natCast]
    gcongr
    calc ‖u‖ * ‖g t‖ ≤ ‖u‖ * 1 := by gcongr; exact hb t
      _ = ‖u‖ := mul_one _
  · have h : (fun t => ∑' k : ℕ, ‖u‖ ^ k / k ! * ‖ρ t‖) = fun t => Real.exp ‖u‖ * ‖ρ t‖ := by
      funext t
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ,
        ← (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) ‖u‖).tsum_eq]
    rw [h]
    exact hρ.norm.const_mul _

/-- Poisson's integral in angular form: with `t = cos ψ`,
`∫₋₁¹ (1 - t²)^{λ-1} e^{iwt} dt = ∫₀^π e^{iw cos ψ} sin^{2λ-1} ψ dψ`. -/
theorem integral_one_sub_sq_cpow_mul_exp_eq_integral_cos {lam : ℝ} (w : ℝ) :
    ∫ t : ℝ in (-1 : ℝ)..1, (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1) * Complex.exp (I * w * t) =
      ∫ ψ : ℝ in (0 : ℝ)..π, Complex.exp (I * w * Real.cos ψ) *
        (Real.rpow (Real.sin ψ) (2 * lam - 1) : ℂ) := by
  set G : ℝ → ℂ := fun t => (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1) * Complex.exp (I * w * t)
  have hcv := integral_image_eq_integral_abs_deriv_smul (f := Real.cos)
    (f' := fun ψ => -Real.sin ψ) measurableSet_Icc
    (fun ψ _ => (Real.hasDerivAt_cos ψ).hasDerivWithinAt) Real.injOn_cos G
  rw [Real.bijOn_cos.image_eq] at hcv
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc, hcv,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  refine intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le fun ψ hψ => ?_
  have hs : 0 < Real.sin ψ := Real.sin_pos_of_pos_of_lt_pi hψ.1 hψ.2
  have hbase : 1 - ((Real.cos ψ : ℝ) : ℂ) ^ 2 = ((Real.sin ψ ^ 2 : ℝ) : ℂ) := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) (Real.sin_sq_add_cos_sq ψ)
    push_cast at h ⊢
    linear_combination -h
  have hpow : ((Real.sin ψ ^ 2 : ℝ) : ℂ) ^ ((lam : ℂ) - 1) =
      ((Real.sin ψ ^ (2 * lam - 2) : ℝ) : ℂ) := by
    rw [show ((lam : ℂ) - 1) = ((lam - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 2; push_cast; ring
  have hsin : Real.sin ψ * Real.sin ψ ^ (2 * lam - 2) = Real.rpow (Real.sin ψ) (2 * lam - 1) := by
    rw [Real.rpow_eq_pow, show 2 * lam - 1 = (2 * lam - 2) + 1 by ring,
      Real.rpow_add_one hs.ne', mul_comm]
  simp only [G, abs_neg, abs_of_pos hs, Complex.real_smul, hbase, hpow]
  rw [← hsin]; push_cast; ring

/-- **The Bessel generating function of Gegenbauer polynomials** (DLMF 18.12.6):
`∑ C_n^λ(cos θ) zⁿ/(2λ)_n = Γ(λ+1/2) e^{z cos θ} (z sin θ/2)^{1/2-λ} J_{λ-1/2}(z sin θ)`, from
Laplace's integral for `C_n^λ` and Poisson's integral for `J`. -/
@[dlmf 18.12.E6]
theorem ultrasphPoly_bessel_generating_function {lam : ℝ} (hlam : 0 < lam)
    {θ z : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) (hz : 0 < z) :
    HasSum (fun n : ℕ => ultrasphPoly lam n (Real.cos θ) / poch (2 * lam) n * (z : ℂ) ^ n)
      (Gamma (lam + 1 / 2 : ℂ) * exp (z * Real.cos θ : ℂ) *
        (z * Real.sin θ / 2 : ℂ) ^ (1 / 2 - lam : ℂ) * besselJ (lam - 1 / 2) (z * Real.sin θ)) := by
  set ρ : ℝ → ℂ := fun ψ => (Real.rpow (Real.sin ψ) (2 * lam - 1) : ℂ) with hρ
  set A : ℂ := Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) with hA
  set g : ℝ → ℂ := fun t => (Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t with hg
  have hρi : IntervalIntegrable ρ volume 0 π := by
    have h := (integral_sin_rpow_aux hlam).1
    have h' : IntervalIntegrable (fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) volume 0 π :=
      ⟨h.1.ofReal, h.2.ofReal⟩
    simpa [ρ, Real.rpow_eq_pow] using h'
  have hS := hasSum_integral_pow_div_factorial_mul (g := g) (by fun_prop)
    (fun t => by
      rw [hg, norm_laplace_integrand, Real.sqrt_le_one]
      nlinarith [sq_nonneg (Real.sin θ * Real.sin t)]) hρi (z : ℂ)
  have h := hS.mul_left A
  convert h using 1
  · funext n
    have hL := ultrasphPoly_laplace_integral hlam n θ
    have h1 : ultrasphPoly (lam : ℂ) n 1 = poch (2 * (lam : ℂ)) n / n.factorial :=
      ultrasphPoly_at_one (by simp; linarith) n
    have hp : poch (2 * (lam : ℂ)) n ≠ 0 := poch_ne_zero_of_re_pos (by simp; linarith) n
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hC1 : ultrasphPoly (lam : ℂ) n 1 ≠ 0 := by rw [h1]; exact div_ne_zero hp hf
    rw [div_eq_iff hC1] at hL
    have hI : ∫ t in (0 : ℝ)..π, ((z : ℂ) * g t) ^ n / n ! * ρ t =
        (z : ℂ) ^ n / n ! * ∫ t in (0 : ℝ)..π, g t ^ n * ρ t := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [mul_pow]; ring
    have hp' : poch ((lam : ℂ) * 2) n ≠ 0 := by rwa [mul_comm]
    rw [hI, hL, h1]
    simp only [g, ρ, A]
    field_simp
  · have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
    have hw : 0 < z * Real.sin θ := mul_pos hz hs
    have hP := besselJ_eq_poisson_integral (ν := (lam : ℂ) - 1 / 2) (x := z * Real.sin θ)
      (by simp; linarith) hw
    rw [show (lam : ℂ) - 1 / 2 - 1 / 2 = (lam : ℂ) - 1 by ring,
      show (lam : ℂ) - 1 / 2 + 1 / 2 = lam by ring,
      integral_one_sub_sq_cpow_mul_exp_eq_integral_cos] at hP
    rw [Complex.ofReal_mul] at hP
    have hE : ∫ t in (0 : ℝ)..π, Complex.exp ((z : ℂ) * g t) * ρ t =
        Complex.exp (z * Real.cos θ) * ∫ t in (0 : ℝ)..π,
          Complex.exp (I * (z * Real.sin θ) * Real.cos t) * ρ t := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [g]
      rw [← mul_assoc, ← Complex.exp_add]
      ring_nf
    have hw2 : ((z : ℂ) * Real.sin θ / 2) ≠ 0 := by
      have : ((z * Real.sin θ / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      simpa using this
    have hcp : ((z : ℂ) * Real.sin θ / 2) ^ (1 / 2 - (lam : ℂ)) *
        ((z : ℂ) * Real.sin θ / 2) ^ ((lam : ℂ) - 1 / 2) = 1 := by
      rw [← Complex.cpow_add _ _ hw2, show 1 / 2 - (lam : ℂ) + ((lam : ℂ) - 1 / 2) = 0 by ring,
        Complex.cpow_zero]
    have hG : Gamma (lam : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hlam)
    have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    rw [hE, hP, hA]
    simp only [ρ]
    calc _ = Gamma (lam + 1 / 2 : ℂ) * Complex.exp (z * Real.cos θ) *
          (((z : ℂ) * Real.sin θ / 2) ^ (1 / 2 - (lam : ℂ)) *
            ((z : ℂ) * Real.sin θ / 2) ^ ((lam : ℂ) - 1 / 2)) /
          (Real.sqrt π * Gamma (lam : ℂ)) *
          ∫ t in (0 : ℝ)..π, Complex.exp (I * (z * Real.sin θ) * Real.cos t) *
            ((Real.sin t).rpow (2 * lam - 1) : ℂ) := by ring
      _ = _ := by rw [hcp]; field_simp

end DLMF.OrthogonalPolynomials