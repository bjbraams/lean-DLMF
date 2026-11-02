/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Noninteger.Basic
public import DLMF.Mathieu.Properties
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Exponential series of solutions of the recurrence 28.14.4

An absolutely summable solution `c` of the three-term recurrence 28.14.4 (DLMF §28.14) decays
faster than every exponential, so the series `∑_m c_m e^{i(ν+2m)z}` converges for every complex
`z`, can be differentiated termwise and solves Mathieu's equation; on `[0, π]` its Fourier
coefficients are the `c_m`.

## Main results

* `summable_exp_series_of_rec`, `hasDerivAt_tsum_exp_series_of_summable_exp`: convergence and
  termwise differentiation of `∑ c_m e^{i(ν+2m)z}`.
* `isMathieuSolution_tsum_exp_series`: the series solves Mathieu's equation 28.2.1.
* `integral_tsum_exp_series_mul_exp`: `∫₀^π f(x) e^{-i(ν+2n)x} dx = π c_n`.
* `integral_tsum_exp_series_mul_neg`: `∫₀^π f(x) f(-x) dx = π ∑ c_m²`.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics MeasureTheory
open scoped Topology Real Classical ComplexConjugate

namespace DLMF.Mathieu

/-! ### Absolutely convergent solutions of the recurrence 28.14.4 -/

/-- An absolutely summable solution of the recurrence 28.14.4 decays faster than every
exponential: `∑ |c_m| e^{K|m|} < ∞` for every real `K`. -/
private lemma summable_norm_mul_exp_of_rec {ν q a : ℂ} {c : ℤ → ℂ}
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0)
    (hs : Summable (fun m => ‖c m‖)) (K : ℝ) :
    Summable (fun m : ℤ => ‖c m‖ * Real.exp (K * |(m : ℝ)|)) := by
  set ρ : ℝ := Real.exp (-K) / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρK : ρ * Real.exp K = 1 / 2 := by
    rw [hρdef, div_mul_eq_mul_div, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  set B : ℝ := ∑' m, ‖c m‖
  have hB : ∀ m, ‖c m‖ ≤ B := fun m => hs.le_tsum m (fun j _ => norm_nonneg _)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨N, hN⟩ := exists_nat_ge (‖ν‖ + ‖a‖ + 2 * ‖q‖ / ρ + 1)
  have hqρ : 0 ≤ 2 * ‖q‖ / ρ := by positivity
  have hD : ∀ k : ℤ, N ≤ k.natAbs → 2 * ‖q‖ / ρ + 1 ≤ ‖a - (ν + 2 * k) ^ 2‖ := by
    intro k hk
    have hk' : (N : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast hk
    have h2k : ‖(2 : ℂ) * k‖ = 2 * |(k : ℝ)| := by
      rw [norm_mul, Complex.norm_intCast]; norm_num
    have h1 : 2 * |(k : ℝ)| - ‖ν‖ ≤ ‖ν + 2 * k‖ := by
      have := norm_sub_norm_le ((2 : ℂ) * k) (-ν)
      rw [h2k, norm_neg, sub_neg_eq_add, add_comm] at this
      exact this
    have h3 : ‖a‖ + (2 * ‖q‖ / ρ + 1) ≤ ‖ν + 2 * k‖ := by
      have := norm_nonneg ν; have := norm_nonneg a; linarith
    have h4 : ‖ν + 2 * k‖ ≤ ‖(ν + 2 * k) ^ 2‖ := by
      have : 1 ≤ ‖ν + 2 * k‖ := by linarith [norm_nonneg a]
      rw [norm_pow]; nlinarith
    have h5 := norm_sub_norm_le ((ν + 2 * k) ^ 2) a
    rw [norm_sub_rev] at h5
    linarith
  have hind : ∀ n : ℕ, ∀ k : ℤ, N + n ≤ k.natAbs → ‖c k‖ ≤ B * ρ ^ n := by
    intro n
    induction n with
    | zero => intro k _; simpa using hB k
    | succ n ih =>
      intro k hk
      have hp := ih (k + 1) (by omega)
      have hm := ih (k - 1) (by omega)
      have hDk := hD k (by omega)
      have hDpos : 0 < ‖a - (ν + 2 * k) ^ 2‖ := by linarith
      have he : (a - (ν + 2 * k) ^ 2) * c k = q * (c (k + 1) + c (k - 1)) := by
        linear_combination -(hrec k)
      have hn : ‖a - (ν + 2 * k) ^ 2‖ * ‖c k‖ ≤ ‖q‖ * (2 * (B * ρ ^ n)) := by
        rw [← norm_mul, he, norm_mul]
        gcongr
        exact (norm_add_le _ _).trans (by linarith)
      have hDρ : 2 * ‖q‖ ≤ ‖a - (ν + 2 * k) ^ 2‖ * ρ := by
        have : (2 * ‖q‖ / ρ + 1) * ρ ≤ ‖a - (ν + 2 * k) ^ 2‖ * ρ :=
          mul_le_mul_of_nonneg_right hDk hρ.le
        rw [add_mul, div_mul_cancel₀ _ hρ.ne', one_mul] at this
        linarith
      have hBρ : 0 ≤ B * ρ ^ n := by positivity
      refine le_of_mul_le_mul_left ?_ hDpos
      calc ‖a - (ν + 2 * k) ^ 2‖ * ‖c k‖ ≤ ‖q‖ * (2 * (B * ρ ^ n)) := hn
        _ = (2 * ‖q‖) * (B * ρ ^ n) := by ring
        _ ≤ (‖a - (ν + 2 * k) ^ 2‖ * ρ) * (B * ρ ^ n) := mul_le_mul_of_nonneg_right hDρ hBρ
        _ = ‖a - (ν + 2 * k) ^ 2‖ * (B * ρ ^ (n + 1)) := by ring
  set C : ℝ := B * (ρ ^ N)⁻¹
  have hg : Summable (fun k : ℤ => C * (1 / 2 : ℝ) ^ k.natAbs) := by
    have hgeo : Summable (fun n : ℕ => C * (1 / 2 : ℝ) ^ n) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
    refine Summable.of_nat_of_neg ?_ ?_
    · simpa using hgeo
    · simpa using hgeo
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Int.cofinite_eq, Filter.eventually_sup]
  have key : ∀ k : ℤ, N ≤ k.natAbs →
      ‖‖c k‖ * Real.exp (K * |(k : ℝ)|)‖ ≤ C * (1 / 2 : ℝ) ^ k.natAbs := by
    intro k hk
    have hc := hind (k.natAbs - N) k (by omega)
    have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]; rfl
    rw [Real.norm_of_nonneg (by positivity), habs, mul_comm K, Real.exp_nat_mul]
    have hpow : ρ ^ (k.natAbs - N) = (ρ ^ N)⁻¹ * ρ ^ k.natAbs := by
      rw [pow_sub₀ _ hρ.ne' hk]; ring
    calc ‖c k‖ * Real.exp K ^ k.natAbs ≤ B * ρ ^ (k.natAbs - N) * Real.exp K ^ k.natAbs := by
          gcongr
      _ = C * (ρ * Real.exp K) ^ k.natAbs := by rw [hpow, mul_pow]; ring
      _ = C * (1 / 2 : ℝ) ^ k.natAbs := by rw [hρK]
  constructor
  · exact eventually_atBot.2 ⟨-(N : ℤ), fun k hk => key k (by omega)⟩
  · exact eventually_atTop.2 ⟨(N : ℤ), fun k hk => key k (by omega)⟩

/-- Bound on `(i(ν+2m))^j e^{i(ν+2m)z}` for `‖z‖ ≤ R`. -/
theorem norm_pow_mul_exp_le (ν z : ℂ) (m : ℤ) {R : ℝ} (hz : ‖z‖ ≤ R) (j : ℕ) :
    ‖(I * (ν + 2 * m)) ^ j * Complex.exp (I * (ν + 2 * m) * z)‖ ≤
      Real.exp (‖ν‖ * (R + j)) * Real.exp (2 * (R + j) * |(m : ℝ)|) := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  set y : ℝ := ‖ν‖ + 2 * |(m : ℝ)|
  have hx : ‖ν + 2 * m‖ ≤ y := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_intCast]; norm_num [y]
  have hy : 0 ≤ y := by positivity
  have h1 : ‖(I * (ν + 2 * m)) ^ j‖ ≤ Real.exp (j * y) := by
    rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Real.exp_nat_mul]
    refine pow_le_pow_left₀ (norm_nonneg _) (hx.trans ?_) j
    linarith [Real.add_one_le_exp y]
  have h2 : ‖Complex.exp (I * (ν + 2 * m) * z)‖ ≤ Real.exp (y * R) := by
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    exact mul_le_mul hx hz (norm_nonneg _) hy
  calc _ ≤ Real.exp (j * y) * Real.exp (y * R) := by
        rw [norm_mul]; exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; simp only [y]; ring

/-- The summable majorant (from faster-than-exponential decay) of the termwise
differentiated series. -/
private lemma summable_majorant_of_summable_exp {ν : ℂ} {c : ℤ → ℂ}
    (hb : ∀ K : ℝ, Summable (fun m : ℤ => ‖c m‖ * Real.exp (K * |(m : ℝ)|))) (R : ℝ) (j : ℕ) :
    Summable (fun m : ℤ => ‖c m‖ *
      (Real.exp (‖ν‖ * (R + j)) * Real.exp (2 * (R + j) * |(m : ℝ)|))) :=
  ((hb (2 * (R + j))).mul_left (Real.exp (‖ν‖ * (R + j)))).congr
    fun m => by ring

/-- Termwise differentiation of `∑ c_m (i(ν+2m))^j e^{i(ν+2m)z}`. -/
theorem hasDerivAt_tsum_exp_series_of_summable_exp {ν : ℂ} {c : ℤ → ℂ}
    (hb : ∀ K : ℝ, Summable (fun m : ℤ => ‖c m‖ * Real.exp (K * |(m : ℝ)|))) (j : ℕ) (z : ℂ) :
    HasDerivAt (fun w => ∑' m : ℤ, c m * ((I * (ν + 2 * m)) ^ j *
        Complex.exp (I * (ν + 2 * m) * w)))
      (∑' m : ℤ, c m * ((I * (ν + 2 * m)) ^ (j + 1) * Complex.exp (I * (ν + 2 * m) * z))) z := by
  set R : ℝ := ‖z‖ + 1
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun m w => c m * ((I * (ν + 2 * m)) ^ j * Complex.exp (I * (ν + 2 * m) * w)))
    (g' := fun m w => c m * ((I * (ν + 2 * m)) ^ (j + 1) * Complex.exp (I * (ν + 2 * m) * w)))
    (summable_majorant_of_summable_exp (ν := ν) hb R (j + 1))
    Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected (fun m w _ => ?_)
    (fun m w hw => ?_) (Metric.mem_ball_self (by positivity : (0 : ℝ) < R)) ?_
    (by rw [Metric.mem_ball, dist_zero_right]; simp [R])
  rotate_left
  · rw [norm_mul]
    gcongr
    have := norm_pow_mul_exp_le ν w m (R := R)
      (by rw [Metric.mem_ball, dist_zero_right] at hw; exact hw.le) (j + 1)
    simpa using this
  · refine .of_norm_bounded (summable_majorant_of_summable_exp (ν := ν) hb R j) fun m => ?_
    rw [norm_mul]
    gcongr
    have := norm_pow_mul_exp_le ν (0 : ℂ) m (R := R) (by simp [R]; positivity) j
    simpa using this
  · have h := ((hasDerivAt_id w).const_mul (I * (ν + 2 * m))).cexp
    have := (h.const_mul ((I * (ν + 2 * m)) ^ j)).const_mul (c m)
    convert this using 1
    · funext w; simp [mul_assoc]
    · simp only [id]; ring

/-- Absolute convergence of `∑ c_m (i(ν+2m))^j e^{i(ν+2m)z}` for every complex `z`. -/
theorem summable_exp_series_of_summable_exp {ν : ℂ} {c : ℤ → ℂ}
    (hb : ∀ K : ℝ, Summable (fun m : ℤ => ‖c m‖ * Real.exp (K * |(m : ℝ)|))) (j : ℕ) (z : ℂ) :
    Summable (fun m : ℤ => ‖c m * ((I * (ν + 2 * m)) ^ j * Complex.exp (I * (ν + 2 * m) * z))‖) :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by
    rw [norm_mul]; gcongr; exact norm_pow_mul_exp_le ν z m le_rfl j)
    (summable_majorant_of_summable_exp (ν := ν) hb ‖z‖ j)

/-- The summable majorant of the termwise differentiated series. -/
theorem summable_majorant_of_rec {ν q a : ℂ} {c : ℤ → ℂ}
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0)
    (hs : Summable (fun m => ‖c m‖)) (R : ℝ) (j : ℕ) :
    Summable (fun m : ℤ => ‖c m‖ *
      (Real.exp (‖ν‖ * (R + j)) * Real.exp (2 * (R + j) * |(m : ℝ)|))) :=
  summable_majorant_of_summable_exp (summable_norm_mul_exp_of_rec hrec hs) R j

/-- Termwise differentiation of `∑ c_m (i(ν+2m))^j e^{i(ν+2m)z}`. -/
private lemma hasDerivAt_tsum_exp_series_of_rec {ν q a : ℂ} {c : ℤ → ℂ}
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0)
    (hs : Summable (fun m => ‖c m‖)) (j : ℕ) (z : ℂ) :
    HasDerivAt (fun w => ∑' m : ℤ, c m * ((I * (ν + 2 * m)) ^ j *
        Complex.exp (I * (ν + 2 * m) * w)))
      (∑' m : ℤ, c m * ((I * (ν + 2 * m)) ^ (j + 1) * Complex.exp (I * (ν + 2 * m) * z))) z :=
  hasDerivAt_tsum_exp_series_of_summable_exp (summable_norm_mul_exp_of_rec hrec hs) j z

/-- Absolute convergence of `∑ c_m (i(ν+2m))^j e^{i(ν+2m)z}` for every complex `z`. -/
theorem summable_exp_series_of_rec {ν q a : ℂ} {c : ℤ → ℂ}
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0)
    (hs : Summable (fun m => ‖c m‖)) (j : ℕ) (z : ℂ) :
    Summable (fun m : ℤ => ‖c m * ((I * (ν + 2 * m)) ^ j * Complex.exp (I * (ν + 2 * m) * z))‖) :=
  summable_exp_series_of_summable_exp (summable_norm_mul_exp_of_rec hrec hs) j z

/-- An absolutely summable solution of 28.14.4 gives an entire solution
`∑ c_m e^{i(ν+2m)z}` of Mathieu's equation. -/
theorem isMathieuSolution_tsum_exp_series {ν q a : ℂ} {c : ℤ → ℂ}
    (hrec : ∀ m : ℤ, q * c (m + 1) - (a - (ν + 2 * m) ^ 2) * c m + q * c (m - 1) = 0)
    (hs : Summable (fun m => ‖c m‖)) :
    IsMathieuSolution a q (fun z => ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * z)) := by
  set S : ℕ → ℂ → ℂ := fun j z => ∑' m : ℤ, c m * ((I * (ν + 2 * m)) ^ j *
    Complex.exp (I * (ν + 2 * m) * z)) with hS
  have h0 : (fun z => ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * z)) = S 0 := by
    funext z; simp [hS]
  have hd : ∀ j z, HasDerivAt (S j) (S (j + 1) z) z := fun j z =>
    hasDerivAt_tsum_exp_series_of_rec hrec hs j z
  have hderiv : deriv (S 0) = S 1 := funext fun z => (hd 0 z).deriv
  rw [h0]
  refine ⟨fun z => (hd 0 z).differentiableAt, fun z => ?_⟩
  rw [hderiv]
  convert hd 1 z using 1
  -- the coefficient identity
  set e : ℤ → ℂ := fun m => Complex.exp (I * (ν + 2 * m) * z) with he
  set E : ℂ := Complex.exp (2 * I * z)
  set E' : ℂ := Complex.exp (-(2 * I * z))
  have hs0 : HasSum (fun m => c m * e m) (S 0 z) := by
    have := (summable_exp_series_of_rec hrec hs 0 z).of_norm.hasSum
    simpa [hS] using this
  have hs2 : HasSum (fun m => c m * ((I * (ν + 2 * m)) ^ 2 * e m)) (S 2 z) :=
    (summable_exp_series_of_rec hrec hs 2 z).of_norm.hasSum
  have hE : ∀ m : ℤ, e (m + 1) = E * e m := fun m => by
    simp only [he, E, ← Complex.exp_add]; congr 1; push_cast; ring
  have hE' : ∀ m : ℤ, e (m - 1) = E' * e m := fun m => by
    simp only [he, E', ← Complex.exp_add]; congr 1; push_cast; ring
  have H1 : HasSum (fun m => q * c (m - 1) * e m) (q * E * S 0 z) := by
    rw [← (Equiv.addRight (1 : ℤ)).hasSum_iff]
    refine (hs0.mul_left (q * E)).congr_fun fun m => ?_
    simp only [Function.comp, Equiv.coe_addRight, add_sub_cancel_right, hE]; ring
  have H2 : HasSum (fun m => q * c (m + 1) * e m) (q * E' * S 0 z) := by
    rw [← (Equiv.subRight (1 : ℤ)).hasSum_iff]
    refine (hs0.mul_left (q * E')).congr_fun fun m => ?_
    simp only [Function.comp, Equiv.subRight_apply, sub_add_cancel, hE']; ring
  have H := (H1.add H2).sub (hs0.mul_left a)
  have hcos : 2 * Complex.cos (2 * z) = E + E' := by
    rw [Complex.cos]; simp only [E, E']; ring_nf
  have key := H.unique (hs2.congr_fun fun m => ?_)
  · rw [show 1 + 1 = 2 from rfl, ← key]; linear_combination (q * S 0 z) * hcos
  · have := hrec m
    rw [mul_pow, Complex.I_sq]
    linear_combination (e m) * this

/-- `|e^{i(ν+2m)x}| = e^{-ℑν x}` for real `x`. -/
theorem norm_exp_I_mul_add_two_mul_ofReal (ν : ℂ) (m : ℤ) (x : ℝ) :
    ‖Complex.exp (I * (ν + 2 * m) * x)‖ = Real.exp (-(ν.im * x)) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]

/-- `∫₀^π e^{2ikx} dx = π δ_{k0}`. -/
private lemma integral_exp_two_mul_I_intCast_mul (k : ℤ) :
    ∫ x in (0 : ℝ)..π, Complex.exp (2 * I * k * x) = if k = 0 then (π : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hc : (2 * I * k : ℂ) ≠ 0 := by
      simp [hk, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * I * k * π) = 1 := by
      rw [show (2 * I * k * π : ℂ) = k * (2 * π * I) by ring, Complex.exp_int_mul_two_pi_mul_I]
    simp [this]

/-- Fourier coefficients of an absolutely convergent series `∑ c_m e^{i(ν+2m)x}` on `[0, π]`. -/
theorem integral_tsum_exp_series_mul_exp {ν : ℂ} {c : ℤ → ℂ} (hs : Summable (fun m => ‖c m‖))
    (n : ℤ) :
    ∫ x in (0 : ℝ)..π, (∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * x)) *
      Complex.exp (-(I * (ν + 2 * n) * x)) = π * c n := by
  have hF : ∀ m : ℤ, ∀ x : ℝ, c m * Complex.exp (I * (ν + 2 * m) * x) *
      Complex.exp (-(I * (ν + 2 * n) * x)) = c m * Complex.exp (2 * I * (m - n : ℤ) * x) := by
    intro m x
    rw [mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
  have hnorm : ∀ m : ℤ, ∀ x : ℝ, ‖c m * Complex.exp (2 * I * (m - n : ℤ) * x)‖ = ‖c m‖ := by
    intro m x
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.mul_re]
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := π)
    (F := fun m x => c m * Complex.exp (2 * I * (m - n : ℤ) * x))
    (f := fun x => (∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * x)) *
      Complex.exp (-(I * (ν + 2 * n) * x)))
    (fun m _ => ‖c m‖) (fun m => by fun_prop)
    (fun m => ae_of_all _ fun x _ => (hnorm m x).le) (ae_of_all _ fun _ _ => hs)
    intervalIntegrable_const (ae_of_all _ fun x _ => ?_)
  · have hval : ∀ m : ℤ, ∫ x in (0 : ℝ)..π, c m * Complex.exp (2 * I * (m - n : ℤ) * x) =
        if m = n then (π : ℂ) * c n else 0 := by
      intro m
      rw [intervalIntegral.integral_const_mul, integral_exp_two_mul_I_intCast_mul]
      by_cases h : m = n
      · subst h; simp; ring
      · simp [sub_eq_zero, h]
    simp only [hval] at hsum
    exact hsum.unique (hasSum_ite_eq n _)
  · have hs' : Summable (fun m : ℤ => c m * Complex.exp (I * (ν + 2 * m) * x)) := by
      refine Summable.of_norm ?_
      simp only [norm_mul, norm_exp_I_mul_add_two_mul_ofReal]
      exact hs.mul_right _
    exact (hs'.hasSum.mul_right _).congr_fun fun m => (hF m x).symm


/-- `∫₀^π f(x) f(-x) dx = π ∑ c_m²` for `f(x) = ∑ c_m e^{i(ν+2m)x}` (absolutely convergent). -/
theorem integral_tsum_exp_series_mul_neg {ν : ℂ} {c : ℤ → ℂ} (hs : Summable (fun m => ‖c m‖))
    (hf : Continuous (fun x : ℝ => ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * x)))
    {s : ℂ} (hsq : HasSum (fun m => c m ^ 2) s) :
    ∫ x in (0 : ℝ)..π, (∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * x)) *
      (∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * -(x : ℂ))) = π * s := by
  set f : ℝ → ℂ := fun x => ∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * x)
  have hneg : ∀ (m : ℤ) (x : ℝ), Complex.exp (I * (ν + 2 * m) * -(x : ℂ)) =
      Complex.exp (-(I * (ν + 2 * m) * x)) := fun m x => by congr 1; ring
  have hnorm : ∀ (m : ℤ) (x : ℝ),
      ‖Complex.exp (I * (ν + 2 * m) * -(x : ℂ))‖ = Real.exp (ν.im * x) := by
    intro m x
    rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring, norm_exp_I_mul_add_two_mul_ofReal]
    congr 1; ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := π)
    (F := fun m x => f x * (c m * Complex.exp (I * (ν + 2 * m) * -(x : ℂ))))
    (f := fun x => f x * (∑' m : ℤ, c m * Complex.exp (I * (ν + 2 * m) * -(x : ℂ))))
    (fun m t => ‖f t‖ * (‖c m‖ * Real.exp (ν.im * t)))
    (fun m => (hf.mul (by fun_prop)).aestronglyMeasurable)
    (fun m => ae_of_all _ fun x _ => by rw [norm_mul, norm_mul, hnorm])
    (ae_of_all _ fun t _ => (hs.mul_right _).mul_left _) ?_ (ae_of_all _ fun x _ => ?_)
  · have hval : ∀ m : ℤ, ∫ x in (0 : ℝ)..π, f x * (c m * Complex.exp (I * (ν + 2 * m) *
        -(x : ℂ))) = π * c m ^ 2 := by
      intro m
      have : (fun x : ℝ => f x * (c m * Complex.exp (I * (ν + 2 * m) * -(x : ℂ)))) =
          fun x : ℝ => c m * (f x * Complex.exp (-(I * (ν + 2 * m) * x))) := by
        funext x; rw [hneg]; ring
      rw [this, intervalIntegral.integral_const_mul, integral_tsum_exp_series_mul_exp hs]; ring
    simp only [hval] at hsum
    exact hsum.unique (hsq.mul_left _)
  · have : (fun t : ℝ => ∑' m : ℤ, ‖f t‖ * (‖c m‖ * Real.exp (ν.im * t))) =
        fun t => ‖f t‖ * ((∑' m : ℤ, ‖c m‖) * Real.exp (ν.im * t)) := by
      funext t; rw [tsum_mul_left, tsum_mul_right]
    rw [this]
    exact (hf.norm.mul (continuous_const.mul (by fun_prop))).intervalIntegrable _ _
  · have hs' : Summable (fun m : ℤ => c m * Complex.exp (I * (ν + 2 * m) * -(x : ℂ))) := by
      refine Summable.of_norm ?_
      simp only [norm_mul, hnorm]
      exact hs.mul_right _
    exact hs'.hasSum.mul_left _

end DLMF.Mathieu
