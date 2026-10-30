/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic.AuxiliaryData
public import DLMF.CoalescingSaddles.DifferentialEquations
public import DLMFMathlib.Analysis.Analytic.OfScalarsUnique

/-!
# Convergent series for the canonical integrals: DLMF §36.8

* 36.8.1–36.8.2: the power series of `Ψ_K(x)` in the parameters, with the coefficients
  `a_n(x)` of `exp(i ∑ xₘ tᵐ) = ∑ aₙ(x) tⁿ` (`cuspoidSeriesCoeff`) and the moments
  `∫ tⁿ exp(i t^{K+2}) dt` written with gamma functions;
* 36.8.3: the hyperbolic umbilic `Ψ^{(H)}` as a series in `z` with Airy coefficients;
* 36.8.4–36.8.6: the elliptic umbilic `Ψ^{(E)}` as a series in `z`, with the functions `f_n` and
  the polynomials `c_n, d_n` (`ellipticUmbilicSeriesF`, `umbilicSeriesC`, `umbilicSeriesD`).

The series are stated with `HasSum` (all of them converge absolutely, the canonical integrals
being entire in the parameters). DLMF starts three of the four series of 36.8.3 at `n = 2, 2, 1`;
the omitted terms vanish because `d₀ = 0` and `c₁ = 0` (`umbilicSeriesD_zero`,
`umbilicSeriesC_one`), so 36.8.3 is stated as one series from `n = 0`.

Numerical checks (mpmath, rotated-contour quadrature): 36.8.1 for `K = 1, …, 4`, 36.8.3 and
36.8.4 at sample points, agreement to 19 digits.
-/

@[expose] public noncomputable section

open Complex
open scoped Real ComplexConjugate

namespace DLMF.CoalescingSaddles

/-! ### The recurrences 36.8.2 and 36.8.6 -/

/-- `a₀(x) = 1` (DLMF 36.8.2). -/
@[dlmf 36.8.E2]
theorem cuspoidSeriesCoeff_zero (K : ℕ) (x : Fin K → ℝ) : cuspoidSeriesCoeff K x 0 = 1 := by
  rw [cuspoidSeriesCoeff]

/-- `a_{n+1}(x) = (i/(n+1)) ∑_{p=0}^{min(n,K-1)} (p+1) x_{p+1} a_{n-p}(x)` (DLMF 36.8.2). -/
@[dlmf 36.8.E2]
theorem cuspoidSeriesCoeff_succ (K : ℕ) (x : Fin K → ℝ) (n : ℕ) :
    cuspoidSeriesCoeff K x (n + 1) = I / ((n : ℂ) + 1) * ∑ p : Fin (min (n + 1) K),
      (((p : ℕ) : ℂ) + 1) * ((x ⟨p, lt_of_lt_of_le p.isLt (min_le_right _ _)⟩ : ℝ) : ℂ) *
        cuspoidSeriesCoeff K x (n - p) := by
  rw [cuspoidSeriesCoeff]

/-- The recurrence 36.8.6: `c₀ = 1`, `d₀ = 0`, `c_{n+1} = c_n' + t d_n`, `d_{n+1} = c_n + d_n'`. -/
@[dlmf 36.8.E6]
theorem umbilicSeries_recurrence :
    umbilicSeriesC 0 = 1 ∧ umbilicSeriesD 0 = 0 ∧
      (∀ n, umbilicSeriesC (n + 1) =
        Polynomial.derivative (umbilicSeriesC n) + Polynomial.X * umbilicSeriesD n) ∧
      ∀ n, umbilicSeriesD (n + 1) = umbilicSeriesC n + Polynomial.derivative (umbilicSeriesD n) :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- `d₀ = 0`. -/
theorem umbilicSeriesD_zero : umbilicSeriesD 0 = 0 := rfl

/-- `c₁ = 0`. -/
theorem umbilicSeriesC_one : umbilicSeriesC 1 = 0 := by
  simp [umbilicSeriesC, umbilicSeriesCD]

/-- `d₁ = 1`. -/
theorem umbilicSeriesD_one : umbilicSeriesD 1 = 1 := by
  simp [umbilicSeriesD, umbilicSeriesCD]

/-! ### Helpers for 36.8.1: Taylor coefficients and termwise integration

The coefficients `aₙ(x)` of 36.8.2 are the Taylor coefficients of the entire function
`exp(i ∑ₘ xₘ t^{m+1})` (`q2t_coeff_eq_taylor`, by the Leibniz rule applied to its differential
equation); Cauchy's estimate bounds them (`q2t_norm_coeff_le`), so that the series may be
integrated termwise along the rotated contour against `exp(i t^{K+2})`
(`q2t_hasSum_cuspoidIntegral`, dominated convergence). The moments
`∫ tⁿ exp(i t^{K+2}) dt` are gamma functions (`q2t_cuspoidMoment_zero`). -/

section q2t

open MeasureTheory Set Filter Function
open scoped Nat Topology

/-- The lower-order part `∑ₘ xₘ t^{m+1}` of the cuspoid potential. -/
def q2t_lower (K : ℕ) (x : Fin K → ℝ) (t : ℂ) : ℂ :=
  ∑ m : Fin K, ((x m : ℝ) : ℂ) * t ^ ((m : ℕ) + 1)

/-- Its derivative `∑ₘ (m+1) xₘ tᵐ`. -/
def q2t_lowerDeriv (K : ℕ) (x : Fin K → ℝ) (t : ℂ) : ℂ :=
  ∑ m : Fin K, (((m : ℕ) : ℂ) + 1) * ((x m : ℝ) : ℂ) * t ^ (m : ℕ)

/-- The lower-order part `∑ₘ xₘ t^{m+1}` has derivative `∑ₘ (m+1) xₘ tᵐ`. -/
lemma q2t_hasDerivAt_lower (K : ℕ) (x : Fin K → ℝ) (t : ℂ) :
    HasDerivAt (q2t_lower K x) (q2t_lowerDeriv K x t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun (m : Fin K) _ =>
    (hasDerivAt_pow ((m : ℕ) + 1) t).const_mul ((x m : ℝ) : ℂ))
  unfold q2t_lower q2t_lowerDeriv
  convert h using 1
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast; ring

/-- Derivative of `exp(i ∑ₘ xₘ t^{m+1})`. -/
lemma q2t_deriv_exp_lower (K : ℕ) (x : Fin K → ℝ) :
    deriv (fun t => exp (I * q2t_lower K x t)) =
      (fun t => I * q2t_lowerDeriv K x t) * fun t => exp (I * q2t_lower K x t) := by
  funext t
  rw [(((q2t_hasDerivAt_lower K x t).const_mul I).cexp).deriv]
  simp only [Pi.mul_apply]; ring

/-- `i ∑ₘ (m+1) xₘ tᵐ` is smooth in `t`. -/
lemma q2t_contDiff_lowerDeriv (K : ℕ) (x : Fin K → ℝ) {n : ℕ∞} :
    ContDiff ℂ n fun t => I * q2t_lowerDeriv K x t := by
  unfold q2t_lowerDeriv; fun_prop

/-- `exp(i ∑ₘ xₘ t^{m+1})` is smooth in `t`. -/
lemma q2t_contDiff_exp_lower (K : ℕ) (x : Fin K → ℝ) {n : ℕ∞} :
    ContDiff ℂ n fun t => exp (I * q2t_lower K x t) := by
  unfold q2t_lower; fun_prop

/-- The `i`-th derivative at `0` of `i ∑ₘ (m+1) xₘ tᵐ` is `i (i+1) x_i i!` for `i < K` and `0`
otherwise. -/
lemma q2t_iteratedDeriv_lowerDeriv (K : ℕ) (x : Fin K → ℝ) (i : ℕ) :
    iteratedDeriv i (fun t => I * q2t_lowerDeriv K x t) 0 =
      if h : i < K then I * (((i : ℂ) + 1) * ((x ⟨i, h⟩ : ℝ) : ℂ) * (i ! : ℂ)) else 0 := by
  rw [iteratedDeriv_const_mul_field]
  unfold q2t_lowerDeriv
  rw [iteratedDeriv_fun_sum (fun m _ => by fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i, h⟩]
    · simp
    · intro m _ hm
      have : i ≠ (m : ℕ) := fun e => hm (Fin.ext e.symm)
      simp [this]
    · simp
  · rw [Finset.sum_eq_zero]; · simp
    intro m _
    have : i ≠ (m : ℕ) := fun e => h (e ▸ m.isLt)
    simp [this]

/-- Rewrites the recurrence sum over `Fin (min (n+1) K)` as a sum over `range (n+1)` with a guard `i
< K`. -/
lemma q2t_sum_fin_min (K n : ℕ) (F : ℕ → ℂ) (x : Fin K → ℝ) :
    ∑ p : Fin (min (n + 1) K), (((p : ℕ) : ℂ) + 1) *
        ((x ⟨p, lt_of_lt_of_le p.isLt (min_le_right _ _)⟩ : ℝ) : ℂ) * F (n - p) =
      ∑ i ∈ Finset.range (n + 1),
        if h : i < K then ((i : ℂ) + 1) * ((x ⟨i, h⟩ : ℝ) : ℂ) * F (n - i) else 0 := by
  have h1 : ∑ p : Fin (min (n + 1) K), (((p : ℕ) : ℂ) + 1) *
      ((x ⟨p, lt_of_lt_of_le p.isLt (min_le_right _ _)⟩ : ℝ) : ℂ) * F (n - p) =
      ∑ p : Fin (min (n + 1) K), (fun i : ℕ =>
        if h : i < K then ((i : ℂ) + 1) * ((x ⟨i, h⟩ : ℝ) : ℂ) * F (n - i) else 0) p := by
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [lt_of_lt_of_le p.isLt (min_le_right _ _), dite_true]
  rw [h1, ← Finset.sum_range (fun i : ℕ =>
    if h : i < K then ((i : ℂ) + 1) * ((x ⟨i, h⟩ : ℝ) : ℂ) * F (n - i) else 0)]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (min_le_left _ _)) fun i hi hni => ?_
  simp only [Finset.mem_range] at hi hni
  have : ¬ i < K := fun h => hni (lt_min hi h)
  simp [this]

/-- The coefficients `a_n(x)` of 36.8.2 are the Taylor coefficients of `exp(i ∑ₘ xₘ t^{m+1})`. -/
lemma q2t_coeff_eq_taylor (K : ℕ) (x : Fin K → ℝ) (n : ℕ) :
    cuspoidSeriesCoeff K x n =
      iteratedDeriv n (fun t => exp (I * q2t_lower K x t)) 0 / (n ! : ℂ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · simp [cuspoidSeriesCoeff, q2t_lower]
  · rw [cuspoidSeriesCoeff, iteratedDeriv_succ', q2t_deriv_exp_lower,
      iteratedDeriv_mul (q2t_contDiff_lowerDeriv K x).contDiffAt
        (q2t_contDiff_exp_lower K x).contDiffAt]
    simp only [q2t_iteratedDeriv_lowerDeriv]
    have hterm : ∀ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : ℂ) *
        (if h : i < K then I * (((i : ℂ) + 1) * ((x ⟨i, h⟩ : ℝ) : ℂ) * (i ! : ℂ)) else 0) *
        iteratedDeriv (n - i) (fun t => exp (I * q2t_lower K x t)) 0 =
        (n ! : ℂ) * I * (if h : i < K then ((i : ℂ) + 1) * ((x ⟨i, h⟩ : ℝ) : ℂ) *
          cuspoidSeriesCoeff K x (n - i) else 0) := by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hc := ih (n - i) (by omega)
      have hf : ((n - i) ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
      have hD : iteratedDeriv (n - i) (fun t => exp (I * q2t_lower K x t)) 0 =
          ((n - i) ! : ℂ) * cuspoidSeriesCoeff K x (n - i) := by
        rw [hc]; field_simp
      have hcf : ((n.choose i : ℕ) : ℂ) * (i ! : ℂ) * ((n - i) ! : ℂ) = (n ! : ℂ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
      rw [hD]
      split_ifs
      · linear_combination (I * ((i : ℂ) + 1) * ((x ⟨i, by assumption⟩ : ℝ) : ℂ) *
          cuspoidSeriesCoeff K x (n - i)) * hcf
      · simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← q2t_sum_fin_min]
    have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
    rw [Nat.factorial_succ]; push_cast
    field_simp

/-- `exp(i ∑ₘ xₘ t^{m+1})` is entire. -/
lemma q2t_differentiable_exp_lower (K : ℕ) (x : Fin K → ℝ) :
    Differentiable ℂ fun t => exp (I * q2t_lower K x t) :=
  (q2t_contDiff_exp_lower K x (n := 1)).differentiable one_ne_zero

/-- `exp(i ∑ₘ xₘ t^{m+1}) = ∑ aₙ(x) tⁿ` for all complex `t` (DLMF 36.8.2). -/
lemma q2t_hasSum_exp_lower (K : ℕ) (x : Fin K → ℝ) (t : ℂ) :
    HasSum (fun n => cuspoidSeriesCoeff K x n * t ^ n) (exp (I * q2t_lower K x t)) := by
  have h := Complex.hasSum_taylorSeries_of_entire (q2t_differentiable_exp_lower K x) 0 t
  convert h using 1
  funext n
  rw [q2t_coeff_eq_taylor, sub_zero, smul_eq_mul, smul_eq_mul]
  field_simp

/-- `‖∑ₘ xₘ t^{m+1}‖ ≤ ∑ₘ |xₘ| ‖t‖^{m+1}`. -/
lemma q2t_norm_lower_le (K : ℕ) (x : Fin K → ℝ) (t : ℂ) :
    ‖q2t_lower K x t‖ ≤ ∑ m : Fin K, |x m| * ‖t‖ ^ ((m : ℕ) + 1) := by
  unfold q2t_lower
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- Cauchy's estimate for the coefficients `aₙ(x)`. -/
lemma q2t_norm_coeff_le (K : ℕ) (x : Fin K → ℝ) (n : ℕ) {R : ℝ} (hR : 0 < R) :
    ‖cuspoidSeriesCoeff K x n‖ ≤
      Real.exp (∑ m : Fin K, |x m| * R ^ ((m : ℕ) + 1)) / R ^ n := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    (q2t_differentiable_exp_lower K x).diffContOnCl
    (C := Real.exp (∑ m : Fin K, |x m| * R ^ ((m : ℕ) + 1))) (c := 0) (fun z hz => by
      rw [mem_sphere_zero_iff_norm] at hz
      rw [norm_exp]
      refine Real.exp_le_exp.mpr ((re_le_norm _).trans ?_)
      rw [norm_mul, norm_I, one_mul, ← hz]
      exact q2t_norm_lower_le K x z)
  rw [q2t_coeff_eq_taylor, norm_div, norm_natCast]
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf]
  calc _ ≤ (n ! : ℝ) * Real.exp (∑ m : Fin K, |x m| * R ^ ((m : ℕ) + 1)) / R ^ n := h
    _ = _ := by ring

/-- `∑ ‖aₙ(x)‖ ρⁿ` converges, with sum at most `2 exp(∑ₘ |xₘ| (2ρ+1)^{m+1})`. -/
lemma q2t_summable_norm_coeff (K : ℕ) (x : Fin K → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Summable (fun n => ‖cuspoidSeriesCoeff K x n‖ * ρ ^ n) ∧
      ∑' n, ‖cuspoidSeriesCoeff K x n‖ * ρ ^ n ≤
        2 * Real.exp (∑ m : Fin K, |x m| * (2 * ρ + 1) ^ ((m : ℕ) + 1)) := by
  set M := Real.exp (∑ m : Fin K, |x m| * (2 * ρ + 1) ^ ((m : ℕ) + 1))
  have hR : 0 < 2 * ρ + 1 := by linarith
  have hb : ∀ n, ‖cuspoidSeriesCoeff K x n‖ * ρ ^ n ≤ M * (1 / 2) ^ n := by
    intro n
    have h1 := q2t_norm_coeff_le K x n hR
    have h2 : ρ ^ n ≤ (2 * ρ + 1) ^ n * (1 / 2) ^ n := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hρ (by linarith) n
    have hpos : 0 < (2 * ρ + 1) ^ n := pow_pos hR n
    calc ‖cuspoidSeriesCoeff K x n‖ * ρ ^ n ≤ (M / (2 * ρ + 1) ^ n) * ((2 * ρ + 1) ^ n *
          (1 / 2) ^ n) := mul_le_mul h1 h2 (pow_nonneg hρ n) (by positivity)
      _ = M * (1 / 2) ^ n := by field_simp
  have hg : Summable fun n : ℕ => M * (1 / 2 : ℝ) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left M
  have hs : Summable (fun n => ‖cuspoidSeriesCoeff K x n‖ * ρ ^ n) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hb hg
  refine ⟨hs, (hs.tsum_le_tsum hb hg).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  ring

/-- `(2a + 1)^K ≤ 3^K (1 + a^K)` for `a ≥ 0`. -/
lemma q2t_pow_two_mul_add_one_le (K : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (2 * a + 1) ^ K ≤ 3 ^ K * (1 + a ^ K) := by
  rcases le_total a 1 with h | h
  · have : (2 * a + 1) ^ K ≤ 3 ^ K := pow_le_pow_left₀ (by linarith) (by linarith) K
    have := pow_nonneg ha K
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) K]
  · have : (2 * a + 1) ^ K ≤ (3 * a) ^ K := pow_le_pow_left₀ (by linarith) (by linarith) K
    rw [mul_pow] at this
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) K]

/-- The exponent bound behind the majorant of the termwise integrated series. -/
lemma q2t_majorant_exponent_le (K : ℕ) (x : Fin K → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ∑ m : Fin K, |x m| * (2 * a + 1) ^ ((m : ℕ) + 1) - a ^ (K + 2) ≤
      (∑ m, |x m|) * 3 ^ K + (∑ m, |x m|) * 3 ^ K * (1 + 2 * ((∑ m, |x m|) * 3 ^ K)) ^ K +
        1 / 2 - a ^ 2 / 2 := by
  set S := ∑ m, |x m|
  have hS : 0 ≤ S := Finset.sum_nonneg fun m _ => abs_nonneg _
  have h1 : ∑ m : Fin K, |x m| * (2 * a + 1) ^ ((m : ℕ) + 1) ≤ S * (2 * a + 1) ^ K := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact pow_le_pow_right₀ (by linarith) m.isLt
  have h2 := q2t_pow_two_mul_add_one_le K ha
  have h3 := s36a_young K ha (mul_nonneg hS (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) K))
  have h4 := s36a_pow_ge_sq_sub_one K ha
  have h5 : S * (2 * a + 1) ^ K ≤ S * 3 ^ K + S * 3 ^ K * a ^ K := by
    have := mul_le_mul_of_nonneg_left h2 hS; nlinarith
  nlinarith

/-- The majorant `2 exp(∑ₘ |xₘ| (2|r| + 1)^{m+1}) exp(-|r|^{K+2})` is integrable on `ℝ`. -/
lemma q2t_integrable_majorant (K : ℕ) (x : Fin K → ℝ) :
    Integrable fun r : ℝ => 2 * Real.exp (∑ m : Fin K, |x m| * (2 * |r| + 1) ^ ((m : ℕ) + 1)) *
      Real.exp (-|r| ^ (K + 2)) := by
  set S := ∑ m, |x m| with hS
  set c := S * 3 ^ K + S * 3 ^ K * (1 + 2 * (S * 3 ^ K)) ^ K + 1 / 2 with hc
  refine ((integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul
    (2 * Real.exp c)).mono' (by fun_prop) (ae_of_all _ fun r => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc, mul_assoc,
    ← Real.exp_add, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  have := q2t_majorant_exponent_le K x (abs_nonneg r)
  rw [sq_abs, ← hS] at this
  rw [hc]; linarith

/-- On the rotated contour the leading factor has modulus `‖exp(i t(r)^{K+2})‖ = exp(-|r|^{K+2})`.
-/
lemma q2t_norm_exp_top (K : ℕ) (r : ℝ) :
    ‖exp (I * cuspoidContour K r ^ (K + 2))‖ = Real.exp (-|r| ^ (K + 2)) := by
  rw [norm_exp, cuspoidContour_pow, ← mul_assoc, I_mul_I]
  congr 1
  rw [neg_one_mul, neg_re, ofReal_re]

/-- Termwise integration of `exp(i ∑ xₘ t^{m+1}) = ∑ aₙ tⁿ` along the rotated contour:
`Ψ_K(x) = ∑ₙ aₙ(x) ∫ tⁿ exp(i t^{K+2}) dt`. -/
lemma q2t_hasSum_cuspoidIntegral (K : ℕ) (x : Fin K → ℝ) :
    HasSum (fun n => cuspoidSeriesCoeff K x n * cuspoidMoment K 0 n) (cuspoidIntegral K x) := by
  have hpot0 : ∀ t, cuspoidPotential K t 0 = t ^ (K + 2) := fun t => by simp [cuspoidPotential]
  have hpot : ∀ t, cuspoidPotential K t x = t ^ (K + 2) + q2t_lower K x t := fun t => rfl
  set F : ℕ → ℝ → ℂ := fun n r => cuspoidContourDir K r *
    (cuspoidSeriesCoeff K x n * cuspoidContour K r ^ n) *
      exp (I * cuspoidContour K r ^ (K + 2)) with hF
  have hint : ∀ n, ∫ r, F n r = cuspoidSeriesCoeff K x n * cuspoidMoment K 0 n := by
    intro n
    rw [cuspoidMoment, ← integral_const_mul]
    congr 1; funext r
    rw [hF, hpot0]; ring
  simp only [← hint]
  have hnorm : ∀ n r, ‖F n r‖ =
      ‖cuspoidSeriesCoeff K x n‖ * |r| ^ n * Real.exp (-|r| ^ (K + 2)) := by
    intro n r
    rw [hF, norm_mul, norm_mul, norm_mul, norm_cuspoidContourDir, norm_pow, norm_cuspoidContour,
      q2t_norm_exp_top, one_mul]
  unfold cuspoidIntegral
  refine hasSum_integral_of_dominated_convergence
    (fun n r => ‖cuspoidSeriesCoeff K x n‖ * |r| ^ n * Real.exp (-|r| ^ (K + 2)))
    (fun n => ?_) (fun n => ae_of_all _ fun r => (hnorm n r).le)
    (ae_of_all _ fun r => ((q2t_summable_norm_coeff K x (abs_nonneg r)).1.mul_right _)) ?_
    (ae_of_all _ fun r => ?_)
  · exact ((measurable_cuspoidContourDir K).mul (measurable_const.mul
      ((measurable_cuspoidContour K).pow_const n))).mul (measurable_exp.comp
        (measurable_const.mul ((measurable_cuspoidContour K).pow_const _))) |>.aestronglyMeasurable
  · refine (q2t_integrable_majorant K x).mono' ?_ (ae_of_all _ fun r => ?_)
    · exact (Measurable.tsum fun n => by fun_prop).aestronglyMeasurable
    · rw [tsum_mul_right, Real.norm_eq_abs, abs_of_nonneg (by
        exact mul_nonneg (tsum_nonneg fun n => by positivity) (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_right (q2t_summable_norm_coeff K x (abs_nonneg r)).2
        (Real.exp_pos _).le
  · have h := ((q2t_hasSum_exp_lower K x (cuspoidContour K r)).mul_left
      (cuspoidContourDir K r)).mul_right (exp (I * cuspoidContour K r ^ (K + 2)))
    convert h using 1
    rw [hpot, mul_add, exp_add]; ring

/-- `∫_0^∞ rⁿ exp(-r^{K+2}) dr = Γ((n+1)/(K+2))/(K+2)`. -/
lemma q2t_integral_pow_exp (K n : ℕ) :
    ∫ r in Ioi (0 : ℝ), r ^ n * Real.exp (-r ^ (K + 2)) =
      1 / ((K : ℝ) + 2) * Real.Gamma ((n + 1) / ((K : ℝ) + 2)) := by
  have h := integral_rpow_mul_exp_neg_rpow (p := (K : ℝ) + 2) (q := (n : ℝ)) (by positivity)
    (by have := n.cast_nonneg (α := ℝ); linarith)
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [Real.rpow_natCast, show ((K : ℝ) + 2) = ((K + 2 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

/-- The moments `∫ tⁿ exp(i t^{K+2}) dt` over the rotated contour:
`(e^{i(n+1)θ} + (-1)ⁿ d₋^{n+1}) Γ((n+1)/(K+2))/(K+2)`, with `d₋` the direction for `r < 0`. -/
lemma q2t_cuspoidMoment_zero (K n : ℕ) :
    cuspoidMoment K 0 n = (exp ((cuspoidAngle K : ℂ) * I) ^ (n + 1) +
      (-1) ^ n * cuspoidContourDir K (-1) ^ (n + 1)) *
        ((1 / ((K : ℝ) + 2) * Real.Gamma ((n + 1) / ((K : ℝ) + 2)) : ℝ) : ℂ) := by
  set G : ℂ := ((1 / ((K : ℝ) + 2) * Real.Gamma ((n + 1) / ((K : ℝ) + 2)) : ℝ) : ℂ) with hG
  have hf : ∀ r : ℝ, cuspoidContourDir K r * cuspoidContour K r ^ n *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0) =
      cuspoidContourDir K r ^ (n + 1) * (r : ℂ) ^ n *
        ((Real.exp (-|r| ^ (K + 2)) : ℝ) : ℂ) := by
    intro r
    have hp : cuspoidPotential K (cuspoidContour K r) 0 = cuspoidContour K r ^ (K + 2) := by
      simp [cuspoidPotential]
    rw [hp, cuspoidContour_pow, ← mul_assoc, I_mul_I, ofReal_exp]
    rw [cuspoidContour]; push_cast; ring_nf
  have hint := s36b_integrable_moment_integrand K 0 n
  unfold cuspoidMoment
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn (b := 0)]
  have hI : ∫ r in Ioi (0 : ℝ), (((r ^ n * Real.exp (-r ^ (K + 2)) : ℝ)) : ℂ) = G := by
    rw [integral_complex_ofReal, q2t_integral_pow_exp]
  have hR : ∫ r in Ioi (0 : ℝ), cuspoidContourDir K r * cuspoidContour K r ^ n *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0) =
      exp ((cuspoidAngle K : ℂ) * I) ^ (n + 1) * G := by
    rw [← hI, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [hf, s36a_dir_of_nonneg K hr.le, abs_of_pos hr]; push_cast; ring
  have hL : ∫ r in Iic (0 : ℝ), cuspoidContourDir K r * cuspoidContour K r ^ n *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0) =
      (-1) ^ n * cuspoidContourDir K (-1) ^ (n + 1) * G := by
    have := integral_comp_neg_Ioi 0 (fun r => cuspoidContourDir K r * cuspoidContour K r ^ n *
      exp (I * cuspoidPotential K (cuspoidContour K r) 0))
    rw [neg_zero] at this
    rw [← this, ← hI, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
    rw [hf, s36a_dir_neg (neg_neg_of_pos hr), abs_neg, abs_of_pos hr]; push_cast; ring
  rw [hL, hR]; ring

/-- `e^{i(n+1)θ} + (-1)ⁿ e^{-i(n+1)θ} = 2 iⁿ cos(nπ/2 - (n+1)θ)`. -/
lemma q2t_exp_pow_add (θ : ℝ) (n : ℕ) :
    exp ((θ : ℂ) * I) ^ (n + 1) + (-1) ^ n * exp (-(θ : ℂ) * I) ^ (n + 1) =
      2 * I ^ n * (Real.cos (n * π / 2 - (n + 1) * θ) : ℂ) := by
  have e1 : exp ((θ : ℂ) * I) ^ (n + 1) = exp ((((n + 1) * θ : ℝ) : ℂ) * I) := by
    rw [← exp_nat_mul]; push_cast; ring_nf
  have e2 : exp (-(θ : ℂ) * I) ^ (n + 1) = exp (-(((n + 1) * θ : ℝ) : ℂ) * I) := by
    rw [← exp_nat_mul]; push_cast; ring_nf
  have e3 : (-1 : ℂ) ^ n = exp (((n * π : ℝ) : ℂ) * I) := by
    rw [← exp_pi_mul_I, ← exp_nat_mul]; push_cast; ring_nf
  have e4 : I ^ n = exp (((n * π / 2 : ℝ) : ℂ) * I) := by
    conv_lhs => rw [← exp_pi_div_two_mul_I]
    rw [← exp_nat_mul]; push_cast; ring_nf
  rw [e1, e2, e3, e4, ofReal_cos, Complex.cos]
  have : 2 * exp (((n * π / 2 : ℝ) : ℂ) * I) * ((exp ((((n * π / 2 - (n + 1) * θ : ℝ)) : ℂ) * I) +
      exp (-(((n * π / 2 - (n + 1) * θ : ℝ)) : ℂ) * I)) / 2) =
      exp (((n * π / 2 : ℝ) : ℂ) * I + (((n * π / 2 - (n + 1) * θ : ℝ)) : ℂ) * I) +
      exp (((n * π / 2 : ℝ) : ℂ) * I + -(((n * π / 2 - (n + 1) * θ : ℝ)) : ℂ) * I) := by
    rw [exp_add, exp_add]; ring
  rw [this, ← exp_add, add_comm]
  congr 2 <;> push_cast <;> ring

/-! ### Helpers for 36.8.3: termwise integration of `exp(izst)`

`Ai^{(n)} = cₙ Ai + dₙ Ai'` (`q2t_hasDerivAt_airyN`, from 36.8.6 and the Airy equation), so
that the fold moments `∫ sⁿ exp(i(s³ + xs)) ds` are Airy derivatives (`q2t_cuspoidMoment_one`,
from 36.2.13 and differentiation under the integral sign); expanding `exp(izst)` in the
hyperbolic umbilic integral and integrating termwise over the product contour gives a series
of products of fold moments (`q2t_hasSum_hyperbolicUmbilicIntegral`). -/

/-- `Ai^{(n)}(w) = cₙ(w) Ai(w) + dₙ(w) Ai'(w)` (the polynomials of 36.8.6). -/
def q2t_airyN (n : ℕ) (w : ℂ) : ℂ :=
  (umbilicSeriesC n).eval w * Airy.airyAi w + (umbilicSeriesD n).eval w * Airy.airyAiDeriv w

/-- `Ai^{(n)}` in the form `cₙ Ai + dₙ Ai'` has derivative `Ai^{(n+1)}`. -/
lemma q2t_hasDerivAt_airyN (n : ℕ) (w : ℂ) :
    HasDerivAt (q2t_airyN n) (q2t_airyN (n + 1) w) w := by
  unfold q2t_airyN
  have h := (((umbilicSeriesC n).hasDerivAt w).mul (Airy.hasDerivAt_airyAi w)).add
    (((umbilicSeriesD n).hasDerivAt w).mul (Airy.hasDerivAt_airyAiDeriv w))
  convert h using 1
  obtain ⟨-, -, hc, hd⟩ := umbilicSeries_recurrence
  rw [hc, hd]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  ring

/-- Iterated derivatives of `s ↦ Ai(s/a)` for real `s`. -/
lemma q2t_iteratedDeriv_airy_scaled (a : ℝ) (n : ℕ) :
    iteratedDeriv n (fun s : ℝ => Airy.airyAi (((s / a : ℝ)) : ℂ)) =
      fun s : ℝ => ((a⁻¹ : ℝ) : ℂ) ^ n * q2t_airyN n (((s / a : ℝ)) : ℂ) := by
  induction n with
  | zero =>
    funext s; simp [q2t_airyN, umbilicSeriesC, umbilicSeriesD, umbilicSeriesCD]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have h1 : HasDerivAt (fun s : ℝ => (((s / a : ℝ)) : ℂ)) ((a⁻¹ : ℝ) : ℂ) s := by
      have := ((hasDerivAt_id s).div_const a).ofReal_comp
      simpa [div_eq_mul_inv] using this
    have h2 := ((q2t_hasDerivAt_airyN n _).comp s h1).const_mul (((a⁻¹ : ℝ) : ℂ) ^ n)
    rw [show (fun s : ℝ => ((a⁻¹ : ℝ) : ℂ) ^ n * q2t_airyN n (((s / a : ℝ)) : ℂ)) =
      fun y => ((a⁻¹ : ℝ) : ℂ) ^ n * (q2t_airyN n ∘ fun s : ℝ => (((s / a : ℝ)) : ℂ)) y from rfl,
      h2.deriv]; ring

/-- The fold moments: `∫ sⁿ exp(i(s³ + Xs)) ds = (-i)ⁿ (2π/a) a^{-n} Ai^{(n)}(X/a)`,
`a = 3^{1/3}`. -/
lemma q2t_cuspoidMoment_one (X : ℝ) (n : ℕ) :
    cuspoidMoment 1 ![X] n = (-I) ^ n * (2 * π / (((3 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) *
      ((((3 : ℝ) ^ (1 / 3 : ℝ))⁻¹ : ℝ) : ℂ) ^ n *
        q2t_airyN n (((X / (3 : ℝ) ^ (1 / 3 : ℝ) : ℝ)) : ℂ) := by
  have h := iteratedDeriv_cuspoidIntegral_update 1 ![X] 0 n
  have hu : ∀ s : ℝ, update ![X] 0 s = ![s] := fun s => by
    funext m; fin_cases m; simp
  simp only [hu, cuspoidIntegral_one, iteratedDeriv_const_mul_field,
    q2t_iteratedDeriv_airy_scaled, Fin.val_zero, zero_add, mul_one, Matrix.cons_val_fin_one] at h
  have hI := s36b_negI_pow_mul_I_pow n
  linear_combination (-I) ^ n * h.symm + cuspoidMoment 1 ![X] n * hI.symm

/-- The fold factor `exp(i(s³ + Xs))` on the cubic V-contour. -/
def q2t_foldExp (X σ : ℝ) : ℂ := exp (I * cuspoidPotential 1 (cuspoidContour 1 σ) ![X])

/-- The fold factor on the cubic V-contour is measurable. -/
lemma q2t_measurable_foldExp (X : ℝ) : Measurable (q2t_foldExp X) :=
  measurable_exp.comp (measurable_const.mul
    ((continuous_cuspoidPotential 1 ![X]).measurable.comp (measurable_cuspoidContour 1)))

/-- The fold factor is bounded by `exp(-|σ|³ + |X|(1 + |σ|))`. -/
lemma q2t_norm_foldExp_le (X σ : ℝ) :
    ‖q2t_foldExp X σ‖ ≤ Real.exp (-|σ| ^ 3 + |X| * (1 + |σ|)) := by
  rw [q2t_foldExp, norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have h := s36a_im_potential_ge 1 ![X] σ
  simp only [Fin.sum_univ_one, Matrix.cons_val_fin_one, pow_one,
    show (1 : ℕ) + 2 = 3 from rfl] at h
  have : (I * cuspoidPotential 1 (cuspoidContour 1 σ) ![X]).re =
      -(cuspoidPotential 1 (cuspoidContour 1 σ) ![X]).im := by simp [mul_re]
  rw [this]; linarith

/-- On the product of V-contours the hyperbolic umbilic phase factor splits as fold factor in `x`,
fold factor in `y`, and `exp(i z s t)`. -/
lemma q2t_hyperbolic_split (σ τ x y z : ℝ) :
    exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 σ) (cuspoidContour 1 τ) x y z) =
      q2t_foldExp x σ * q2t_foldExp y τ *
        exp (I * z * cuspoidContour 1 σ * cuspoidContour 1 τ) := by
  rw [q2t_foldExp, q2t_foldExp, ← exp_add, ← exp_add]
  congr 1
  simp only [hyperbolicUmbilicPotential, cuspoidPotential, Fin.sum_univ_one,
    Matrix.cons_val_fin_one, Fin.val_zero, zero_add, pow_one]
  ring

/-- The majorant `‖e₁(σ)‖ ‖e₂(τ)‖ exp(|z||σ||τ|)` is integrable on `ℝ²`. -/
lemma q2t_integrable_hyperbolic_majorant (x y z : ℝ) :
    Integrable fun p : ℝ × ℝ => ‖q2t_foldExp x p.1‖ * ‖q2t_foldExp y p.2‖ *
      Real.exp (|z| * |p.1| * |p.2|) := by
  set C := |x| + |y| + |z|
  have hC : 0 ≤ C := by positivity
  set B := (3 * C + 1) / 2 with hB
  refine ((s36b_integrable_gauss_prod 0 0).const_mul (Real.exp (2 * C + 2 * (B ^ 3 + B)))).mono'
    (((((q2t_measurable_foldExp x).comp measurable_fst).norm).mul
      (((q2t_measurable_foldExp y).comp measurable_snd).norm)).mul
      (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun p => ?_)
  have h1 := q2t_norm_foldExp_le x p.1
  have h2 := q2t_norm_foldExp_le y p.2
  have hσ := s36b_cubic_le (abs_nonneg p.1) hC
  have hτ := s36b_cubic_le (abs_nonneg p.2) hC
  rw [← hB] at hσ hτ
  have hst : 2 * (|p.1| * |p.2|) ≤ |p.1| ^ 2 + |p.2| ^ 2 := by
    nlinarith [sq_nonneg (|p.1| - |p.2|)]
  have hz : |z| * |p.1| * |p.2| ≤ C * (|p.1| ^ 2 + |p.2| ^ 2) / 2 := by
    have : |z| ≤ C := by linarith [abs_nonneg x, abs_nonneg y]
    have := mul_le_mul_of_nonneg_right this (mul_nonneg (abs_nonneg p.1) (abs_nonneg p.2))
    nlinarith
  have hx : |x| * (1 + |p.1|) ≤ C * (1 + |p.1|) :=
    mul_le_mul_of_nonneg_right (by linarith [abs_nonneg y, abs_nonneg z]) (by positivity)
  have hy : |y| * (1 + |p.2|) ≤ C * (1 + |p.2|) :=
    mul_le_mul_of_nonneg_right (by linarith [abs_nonneg x, abs_nonneg z]) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖q2t_foldExp x p.1‖ * ‖q2t_foldExp y p.2‖ * Real.exp (|z| * |p.1| * |p.2|)
      ≤ Real.exp (-|p.1| ^ 3 + |x| * (1 + |p.1|)) * Real.exp (-|p.2| ^ 3 + |y| * (1 + |p.2|)) *
          Real.exp (|z| * |p.1| * |p.2|) := by gcongr
    _ = Real.exp ((-|p.1| ^ 3 + |x| * (1 + |p.1|)) + (-|p.2| ^ 3 + |y| * (1 + |p.2|)) +
          |z| * |p.1| * |p.2|) := by simp only [← Real.exp_add]
    _ ≤ Real.exp ((2 * C + 2 * (B ^ 3 + B)) + (-(1 / 2) * p.1 ^ 2 + -(1 / 2) * p.2 ^ 2)) := by
        apply Real.exp_le_exp.mpr
        rw [← sq_abs p.1, ← sq_abs p.2]
        linarith
    _ = _ := by rw [Real.exp_add, Real.exp_add]; simp [Real.exp_add]

/-- Termwise integration of `exp(izst) = ∑ (izst)ⁿ/n!`:
`Ψ^{(H)}(x, y, z) = ∑ₙ (iz)ⁿ/n! (∫ sⁿ e^{i(s³+xs)} ds)(∫ tⁿ e^{i(t³+yt)} dt)`. -/
lemma q2t_hasSum_hyperbolicUmbilicIntegral (x y z : ℝ) :
    HasSum (fun n : ℕ => (I * z) ^ n / (n ! : ℂ) *
      (cuspoidMoment 1 ![x] n * cuspoidMoment 1 ![y] n)) (hyperbolicUmbilicIntegral x y z) := by
  set F : ℕ → ℝ × ℝ → ℂ := fun n p =>
    (cuspoidContourDir 1 p.1 * cuspoidContour 1 p.1 ^ n * q2t_foldExp x p.1) *
      (cuspoidContourDir 1 p.2 * cuspoidContour 1 p.2 ^ n * q2t_foldExp y p.2) *
        ((I * z) ^ n / (n ! : ℂ)) with hF
  have hint : ∀ n, ∫ p, F n p = (I * z) ^ n / (n ! : ℂ) *
      (cuspoidMoment 1 ![x] n * cuspoidMoment 1 ![y] n) := by
    intro n
    rw [hF, integral_mul_const, Measure.volume_eq_prod,
      integral_prod_mul (fun σ => cuspoidContourDir 1 σ * cuspoidContour 1 σ ^ n *
        q2t_foldExp x σ) (fun τ => cuspoidContourDir 1 τ * cuspoidContour 1 τ ^ n *
        q2t_foldExp y τ)]
    simp only [cuspoidMoment, q2t_foldExp]; ring
  simp only [← hint]
  have hnorm : ∀ n p, ‖F n p‖ = ‖q2t_foldExp x p.1‖ * ‖q2t_foldExp y p.2‖ *
      ((|z| * |p.1| * |p.2|) ^ n / (n ! : ℝ)) := by
    intro n p
    rw [hF]
    simp only [norm_mul, norm_div, norm_pow, norm_cuspoidContourDir, norm_cuspoidContour,
      norm_I, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    ring
  have htsum : (fun p : ℝ × ℝ => ∑' n, ‖q2t_foldExp x p.1‖ * ‖q2t_foldExp y p.2‖ *
      ((|z| * |p.1| * |p.2|) ^ n / (n ! : ℝ))) = fun p => ‖q2t_foldExp x p.1‖ *
        ‖q2t_foldExp y p.2‖ * Real.exp (|z| * |p.1| * |p.2|) := by
    funext p; rw [tsum_mul_left, (Real.hasSum_pow_div_factorial _).tsum_eq]
  have hmeas : ∀ n, Measurable (F n) := by
    intro n
    have h1 := ((measurable_cuspoidContourDir 1).mul
      ((measurable_cuspoidContour 1).pow_const n)).mul (q2t_measurable_foldExp x)
    have h2 := ((measurable_cuspoidContourDir 1).mul
      ((measurable_cuspoidContour 1).pow_const n)).mul (q2t_measurable_foldExp y)
    exact ((h1.comp measurable_fst).mul (h2.comp measurable_snd)).mul_const _
  unfold hyperbolicUmbilicIntegral
  refine hasSum_integral_of_dominated_convergence
    (fun n p => ‖q2t_foldExp x p.1‖ * ‖q2t_foldExp y p.2‖ *
      ((|z| * |p.1| * |p.2|) ^ n / (n ! : ℝ)))
    (fun n => (hmeas n).aestronglyMeasurable) (fun n => ae_of_all _ fun p => (hnorm n p).le)
    (ae_of_all _ fun p => (Real.summable_pow_div_factorial _).mul_left _) ?_
    (ae_of_all _ fun p => ?_)
  · rw [htsum]; exact q2t_integrable_hyperbolic_majorant x y z
  · have h := (Complex.hasSum_pow_div_factorial (I * z * cuspoidContour 1 p.1 * cuspoidContour 1
      p.2)).mul_left
      (cuspoidContourDir 1 p.1 * q2t_foldExp x p.1 * (cuspoidContourDir 1 p.2 * q2t_foldExp y p.2))
    rw [q2t_hyperbolic_split]
    convert h using 1
    · funext n; rw [hF]; simp only [mul_pow]; ring
    · ring

end q2t

/-! ### Cuspoids (36.8.1) -/

/-- The power series of the cuspoid canonical integral for even `K` (DLMF 36.8.1):
`Ψ_K(x) = (2/(K+2)) ∑_{n≥0} exp(iπ(2n+1)/(2(K+2))) Γ((2n+1)/(K+2)) a_{2n}(x)`. -/
@[dlmf 36.8.E1]
theorem hasSum_cuspoidIntegral_even (K : ℕ) (hK : Even K) (x : Fin K → ℝ) :
    HasSum (fun n : ℕ => 2 / ((K : ℂ) + 2) *
        exp (I * (π * (2 * n + 1) / (2 * ((K : ℂ) + 2)))) *
        (Real.Gamma ((2 * n + 1) / ((K : ℝ) + 2)) : ℂ) * cuspoidSeriesCoeff K x (2 * n))
      (cuspoidIntegral K x) := by
  have hd : cuspoidContourDir K (-1) = exp ((cuspoidAngle K : ℂ) * I) := by
    rw [s36a_dir_neg_one, ite_eq_left hK]
  have h := q2t_hasSum_cuspoidIntegral K x
  rw [← (show Function.Injective (fun n : ℕ => 2 * n) from
    fun a b h => by simpa using h).hasSum_iff] at h
  · convert h using 1
    funext n
    simp only [Function.comp_apply, q2t_cuspoidMoment_zero, hd, pow_mul, neg_one_sq, one_pow,
      one_mul]
    rw [← exp_nat_mul]
    have hK2 : ((K : ℂ) + 2) ≠ 0 := by exact_mod_cast (show (K : ℝ) + 2 ≠ 0 by positivity)
    unfold cuspoidAngle
    push_cast
    field_simp
    ring_nf
  · intro m hm
    have hodd : ¬ Even m := fun he => hm ⟨m / 2, by
      obtain ⟨k, hk⟩ := he; simp only; omega⟩
    rw [q2t_cuspoidMoment_zero, hd, (Nat.not_even_iff_odd.mp hodd).neg_one_pow]
    ring

/-- The power series of the cuspoid canonical integral for odd `K` (DLMF 36.8.1):
`Ψ_K(x) = (2/(K+2)) ∑_{n≥0} iⁿ cos(π(n(K+1)-1)/(2(K+2))) Γ((n+1)/(K+2)) a_n(x)`. -/
@[dlmf 36.8.E1]
theorem hasSum_cuspoidIntegral_odd (K : ℕ) (hK : ¬ Even K) (x : Fin K → ℝ) :
    HasSum (fun n : ℕ => 2 / ((K : ℂ) + 2) * I ^ n *
        (Real.cos (π * (n * ((K : ℝ) + 1) - 1) / (2 * ((K : ℝ) + 2))) : ℂ) *
        (Real.Gamma ((n + 1) / ((K : ℝ) + 2)) : ℂ) * cuspoidSeriesCoeff K x n)
      (cuspoidIntegral K x) := by
  have hd : cuspoidContourDir K (-1) = exp (-(cuspoidAngle K : ℂ) * I) := by
    rw [s36a_dir_neg_one, ite_eq_right hK]
  convert q2t_hasSum_cuspoidIntegral K x using 1
  funext n
  rw [q2t_cuspoidMoment_zero, hd, q2t_exp_pow_add]
  have harg : (n : ℝ) * π / 2 - (n + 1) * cuspoidAngle K =
      π * (n * ((K : ℝ) + 1) - 1) / (2 * ((K : ℝ) + 2)) := by
    unfold cuspoidAngle; field_simp; ring
  rw [harg]
  have hK2 : ((K : ℂ) + 2) ≠ 0 := by exact_mod_cast (show (K : ℝ) + 2 ≠ 0 by positivity)
  push_cast
  field_simp

/-! ### Umbilics (36.8.3–36.8.5) -/

/-- The series of the hyperbolic umbilic canonical integral in `z` (DLMF 36.8.3):
`(3^{2/3}/(4π²)) Ψ^{(H)}(3^{1/3}x) = ∑ₙ (-3^{-1/3} i z)ⁿ/n! (Ai(x)Ai(y) cₙ(x)cₙ(y)
  + Ai(x)Ai'(y) cₙ(x)dₙ(y) + Ai'(x)Ai(y) dₙ(x)cₙ(y) + Ai'(x)Ai'(y) dₙ(x)dₙ(y))`, where
`3^{1/3}x = (3^{1/3}x, 3^{1/3}y, 3^{1/3}z)`. DLMF writes four series, the second and third from
`n = 2` and the fourth from `n = 1`; the omitted terms vanish (`d₀ = c₁ = 0`). -/
@[dlmf 36.8.E3]
theorem hasSum_hyperbolicUmbilicIntegral (x y z : ℝ) :
    HasSum (fun n : ℕ => (-(((3 : ℝ) ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * I * z) ^ n / (n.factorial : ℂ) *
        (Airy.airyAi x * Airy.airyAi y * (umbilicSeriesC n).eval (x : ℂ) *
            (umbilicSeriesC n).eval (y : ℂ) +
          Airy.airyAi x * Airy.airyAiDeriv y * (umbilicSeriesC n).eval (x : ℂ) *
            (umbilicSeriesD n).eval (y : ℂ) +
          Airy.airyAiDeriv x * Airy.airyAi y * (umbilicSeriesD n).eval (x : ℂ) *
            (umbilicSeriesC n).eval (y : ℂ) +
          Airy.airyAiDeriv x * Airy.airyAiDeriv y * (umbilicSeriesD n).eval (x : ℂ) *
            (umbilicSeriesD n).eval (y : ℂ)))
      ((((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) / (4 * (π : ℂ) ^ 2) *
        hyperbolicUmbilicIntegral ((3 : ℝ) ^ (1 / 3 : ℝ) * x) ((3 : ℝ) ^ (1 / 3 : ℝ) * y)
          ((3 : ℝ) ^ (1 / 3 : ℝ) * z)) := by
  set a : ℝ := (3 : ℝ) ^ (1 / 3 : ℝ) with ha_def
  have ha : 0 < a := by positivity
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have h3 : (((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) = (a : ℂ) ^ 2 := by
    have : (3 : ℝ) ^ (2 / 3 : ℝ) = a ^ 2 := by
      rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this]; push_cast; ring
  have h3' : (((3 : ℝ) ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) = (a : ℂ)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), ← ha_def]; push_cast; ring
  have hxa : ∀ u : ℝ, a * u / a = u := fun u => by field_simp
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  convert (q2t_hasSum_hyperbolicUmbilicIntegral (a * x) (a * y) (a * z)).mul_left
    ((((3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) / (4 * (π : ℂ) ^ 2)) using 1
  funext n
  rw [q2t_cuspoidMoment_one, q2t_cuspoidMoment_one, ← ha_def, hxa, hxa, h3, h3']
  have key : -(a : ℂ)⁻¹ * I * z = (-I) * (I * ((a * z : ℝ) : ℂ)) * ((a⁻¹ : ℝ) : ℂ) *
      ((a⁻¹ : ℝ) : ℂ) * (-I) := by
    have hu : (a : ℂ) * (a : ℂ)⁻¹ = 1 := mul_inv_cancel₀ ha0
    push_cast
    linear_combination (-(a : ℂ)⁻¹ * I * z) * I_sq + (-(a : ℂ)⁻¹ * I ^ 3 * z) * hu
  rw [key, mul_pow, mul_pow, mul_pow, mul_pow]
  simp only [q2t_airyN]
  field_simp
  ring

/-- The series of the elliptic umbilic canonical integral in `z` (DLMF 36.8.4):
`Ψ^{(E)}(x) = 2π²(2/3)^{2/3} ∑ₙ (-i(2/3)^{2/3}z)ⁿ/n! Re fₙ(ζ, ζ̄)`, `ζ = (x + iy)/12^{1/3}`, with
`fₙ` from 36.8.5 (`ellipticUmbilicSeriesF`). -/
@[dlmf 36.8.E4]
theorem hasSum_ellipticUmbilicIntegral (x y z : ℝ) :
    HasSum (fun n : ℕ => 2 * (π : ℂ) ^ 2 * (((2 / 3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
        ((-I * (((2 / 3 : ℝ) ^ (2 / 3 : ℝ) : ℝ) : ℂ) * z) ^ n / (n.factorial : ℂ)) *
        (((ellipticUmbilicSeriesF n ((x + I * y) / (((12 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ))
          (conj ((x + I * y) / (((12 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ)))).re : ℝ) : ℂ))
      (ellipticUmbilicIntegral x y z) := by
  sorry

end DLMF.CoalescingSaddles
