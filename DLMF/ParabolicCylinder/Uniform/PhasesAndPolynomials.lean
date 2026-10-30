/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.ParabolicCylinder
public import DLMF.Core.Framework
public import DLMFMathlib.Analysis.Calculus.DoubleZeroSqrt
public import DLMFMathlib.Analysis.Calculus.InverseSeries
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Cylinder phases and Olver coefficient polynomials

Real cylinder phase functions, Gamma coefficients and the recurrence for Olver U and V
polynomials.

Source references and common attribution are retained in
`DLMF.ParabolicCylinder.Uniform`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

open Polynomial

/-- The exterior cylinder phase `(t√(t²-1) - log (t+√(t²-1)))/2` used in the exponential uniform
expansion. -/
@[dlmf 12.10.E7]
def pcfXi (t : ℝ) : ℝ :=
  (t*Real.sqrt (t^2-1)-Real.log (t+Real.sqrt (t^2-1)))/2

/-- The interior cylinder phase `(arccos t - t√(1-t²))/2` used in the oscillatory uniform
expansion. -/
@[dlmf 12.10.E23]
def pcfEta (t : ℝ) : ℝ :=
  (Real.arccos t-t*Real.sqrt (1-t^2))/2

/-- The positive-parameter cylinder phase `(t√(t²+1) + log (t+√(t²+1)))/2`. -/
@[dlmf 12.10.E26]
def pcfXiBar (t : ℝ) : ℝ :=
  (t*Real.sqrt (t^2+1)+Real.log (t+Real.sqrt (t^2+1)))/2

/-- The principal-power normalizing factor `2^(-μ²/4-1/4) exp (-μ²/4) μ^(μ²/2-1/2)` for uniform
cylinder expansions. -/
@[dlmf 12.10.E15]
def pcfH (μ : ℂ) : ℂ :=
  2^(-μ^2/4-1/4)*exp (-μ^2/4)*μ^(μ^2/2-1/2)

/-- The `s`th asymptotic coefficient of the normalized half-shifted Gamma function that enters the
cylinder normalizers. -/
@[dlmf 12.10.E16]
def pcfGammaCoeff (s : ℕ) : ℂ :=
  asymptoticCoeff (fun z : ℝ => Gamma (1/2+z)/((Real.sqrt (2*π):ℂ)*exp (-z)*(z:ℂ)^(z:ℂ))) s

/-- Coefficients identified by limits: if `f(t) = ∑_{s<N} c_s t^{-s} + O(t^{-N})` for all `N`,
then the successive limits `asymptoticCoeff f` are the `c_s`. -/
theorem pcfLG_asymptoticCoeff_eq {f : ℝ → ℂ} {c : ℕ → ℂ}
    (h : ∀ N : ℕ, (fun t : ℝ => f t - ∑ s ∈ Finset.range N, c s / (t:ℂ)^s) =O[atTop]
      (fun t : ℝ => (t:ℂ)^(-(N:ℤ)))) (n : ℕ) : asymptoticCoeff f n = c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  -- `t^n (f - ∑_{s<n} c_s t^{-s}) → c_n`
  have hT : Tendsto (fun t : ℝ => (t:ℂ)^n * (f t - ∑ s ∈ Finset.range n, c s / (t:ℂ)^s)) atTop
      (𝓝 (c n)) := by
    have h1 := h (n+1)
    have h2 : (fun t : ℝ => (t:ℂ)^n * (f t - ∑ s ∈ Finset.range (n+1), c s / (t:ℂ)^s)) =O[atTop]
        (fun t : ℝ => (t:ℂ)^(-1:ℤ)) := by
      refine ((isBigO_refl (fun t : ℝ => (t:ℂ)^n) atTop).mul h1).congr' EventuallyEq.rfl ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      have : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_one, pow_succ]; field_simp
    have h3 : Tendsto (fun t : ℝ => (t:ℂ)^(-1:ℤ)) atTop (𝓝 0) := by
      simp only [zpow_neg, zpow_one]
      exact (tendsto_inv_atTop_zero.comp tendsto_id).ofReal.congr (fun t => by simp)
    have h4 := (h2.trans_tendsto h3).add_const (c n)
    rw [zero_add] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [Finset.sum_range_succ]; field_simp; ring
  rcases n with _ | n
  · rw [asymptoticCoeff]
    exact (hT.congr fun t => by simp).limUnder_eq
  · rw [asymptoticCoeff]
    refine (hT.congr fun t => ?_).limUnder_eq
    congr 2
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [ih (n-j) (by omega), show n + 1 - 1 - j = n - j by omega, zpow_neg, zpow_natCast,
      div_eq_mul_inv]

open DLMF.Gamma in
/-- The coefficients of `exp` of the shifted Stirling series at shift `1/2`. -/
noncomputable def pcfLG_gammaG : ℕ → ℂ
  | 0 => 1
  | n + 1 => (∑ k : Fin (n + 1),
      (-1 : ℂ) ^ k.val * Polynomial.aeval (1/2 : ℂ) (Polynomial.bernoulli (k.val + 2)) /
        (k.val + 2) * pcfLG_gammaG (n - k.val)) / (n + 1)
termination_by n => n

open DLMF.Gamma in
/-- The recurrence of `pcfLG_gammaG` in the form used by the exponentiation lemma. -/
theorem pcfLG_gammaG_recurrence (n : ℕ) :
    ((n : ℂ) + 1) * pcfLG_gammaG (n + 1) = ∑ k ∈ Finset.range (n + 1),
      ((k : ℂ) + 1) * stirlingShiftCoeff (1/2) k * pcfLG_gammaG (n - k) := by
  rw [pcfLG_gammaG]
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [mul_div_cancel₀ _ hn, Fin.sum_univ_eq_sum_range (fun k => (-1 : ℂ) ^ k *
    Polynomial.aeval (1/2 : ℂ) (Polynomial.bernoulli (k + 2)) / (k + 2) *
    pcfLG_gammaG (n - k)) (n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h2 : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
  simp only [stirlingShiftCoeff]
  field_simp

open DLMF.Gamma in
/-- `Γ(1/2+t)/(√(2π) e^{-t} t^t)` is the exponential of the shifted Stirling remainder. -/
theorem pcfLG_gamma_ratio_eq {t : ℝ} (ht : 0 < t) :
    Gamma (1/2+t)/((Real.sqrt (2*π):ℂ)*exp (-t)*(t:ℂ)^(t:ℂ)) =
      cexp (stirlingShiftRem (1/2) t) := by
  have hta : (t : ℂ) + 1/2 ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by
    simp only [add_re, ofReal_re]; norm_num; linarith))
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hs : (Real.sqrt (2*π):ℂ) = cexp ((1/2) * log (2*π)) := by
    rw [show (2*π : ℂ) = ((2*π : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), ← Complex.ofReal_ofNat, ← Complex.ofReal_one,
      ← Complex.ofReal_div, ← Complex.ofReal_mul, ← Complex.ofReal_exp, Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos (by positivity)]
    congr 2; ring
  rw [add_comm (1/2 : ℂ), Gamma_eq_exp_binetExponent hta, hs, cpow_def_of_ne_zero ht0,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub, stirlingShiftRem]
  congr 1; ring

open DLMF.Gamma in
/-- The `pcfGammaCoeff` expansion with the coefficients `pcfLG_gammaG`. -/
theorem pcfLG_gamma_expansion (N : ℕ) :
    (fun z : ℝ => Gamma (1/2+z)/((Real.sqrt (2*π):ℂ)*exp (-z)*(z:ℂ)^(z:ℂ))-∑ s ∈ Finset.range N,
      pcfLG_gammaG s/(z:ℂ)^s) =O[atTop] (fun z : ℝ => (z:ℂ)^(-(N:ℤ))) := by
  have hE := isBigO_cexp_sub_of_hasAsymptoticExpansion
    (hasAsymptoticExpansion_stirlingShiftRem (1/2)) (by rw [pcfLG_gammaG] : pcfLG_gammaG 0 = 1)
    (fun m => by simpa using pcfLG_gammaG_recurrence m) N
  have hconv : ∀ M : ℕ, (fun t : ℝ => t ^ (-((M : ℝ)))) =O[atTop] fun t : ℝ => (t:ℂ)^(-(M:ℤ)) := by
    intro M
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _), norm_zpow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, Real.rpow_neg ht.le, Real.rpow_natCast,
      zpow_neg, zpow_natCast]
  have hstep : (fun t : ℝ => t ^ (-((N : ℝ) + 1))) =O[atTop] fun t => t ^ (-(N : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _),
      abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have hlast : (fun t : ℝ => pcfLG_gammaG N * ((t⁻¹ : ℝ) : ℂ) ^ N) =O[atTop]
      fun t : ℝ => (t:ℂ)^(-(N:ℤ)) := by
    refine IsBigO.of_bound ‖pcfLG_gammaG N‖ ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_mul, zpow_neg, zpow_natCast, Complex.ofReal_inv, inv_pow, norm_inv]
  refine ((hE.trans (hstep.trans (hconv N))).add hlast).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [pcfLG_gamma_ratio_eq ht, Finset.sum_range_succ]
  simp only [Complex.ofReal_inv, inv_pow, div_eq_mul_inv]
  ring

open DLMF.Gamma in
/-- The Bernoulli polynomials `B_n(1/2)` for `n ≤ 5`. -/
theorem pcfLG_bernoulli_half (n : ℕ) (hn : n ≤ 5) :
    Polynomial.aeval (1/2 : ℂ) (Polynomial.bernoulli n) =
      [1, 0, -1/12, 0, 7/240, 0].getD n 0 := by
  have hb5 : _root_.bernoulli 5 = 0 := bernoulli_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  have hb3 : _root_.bernoulli 3 = 0 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_three]
  have hb4 : _root_.bernoulli 4 = -1/30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
  interval_cases n <;>
    simp [aeval_bernoulli_eq_sum, Finset.sum_range_succ, _root_.bernoulli_one, _root_.bernoulli_two, hb3, hb4, hb5,
      Nat.choose] <;> norm_num

open DLMF.Gamma in
/-- The first five coefficients `γ_s`. -/
theorem pcfLG_gammaG_values : pcfLG_gammaG 0 = 1 ∧ pcfLG_gammaG 1 = -1/24 ∧ pcfLG_gammaG 2 = 1/1152 ∧
    pcfLG_gammaG 3 = 1003/414720 ∧ pcfLG_gammaG 4 = -4027/39813120 := by
  have h2 := pcfLG_bernoulli_half 2 (by norm_num)
  have h3 := pcfLG_bernoulli_half 3 (by norm_num)
  have h4 := pcfLG_bernoulli_half 4 (by norm_num)
  have h5 := pcfLG_bernoulli_half 5 (by norm_num)
  simp only [List.getD_cons_succ, List.getD_cons_zero, one_div] at h2 h3 h4 h5
  have g0 : pcfLG_gammaG 0 = 1 := by rw [pcfLG_gammaG]
  have g1 : pcfLG_gammaG 1 = -1/24 := by
    rw [pcfLG_gammaG]; simp [g0]; rw [h2]; norm_num
  have g2 : pcfLG_gammaG 2 = 1/1152 := by
    rw [pcfLG_gammaG]; simp [Fin.sum_univ_succ, g0, g1]; rw [h2, h3]; norm_num
  have g3 : pcfLG_gammaG 3 = 1003/414720 := by
    rw [pcfLG_gammaG]; simp [Fin.sum_univ_succ, g0, g1, g2]; rw [h2, h3, h4]; norm_num
  have g4 : pcfLG_gammaG 4 = -4027/39813120 := by
    rw [pcfLG_gammaG]; simp [Fin.sum_univ_succ, g0, g1, g2, g3]; rw [h2, h3, h4, h5]; norm_num
  exact ⟨g0, g1, g2, g3, g4⟩

open DLMF.Gamma in
/-- The coefficients `pcfGammaCoeff` are the `pcfLG_gammaG`. -/
theorem pcfLG_gammaCoeff_eq (s : ℕ) : pcfGammaCoeff s = pcfLG_gammaG s :=
  pcfLG_asymptoticCoeff_eq pcfLG_gamma_expansion s

/-- Asymptotic bound with the indicated comparison function: `(fun z : ℝ => Gamma
(1/2+z)/((Real.sqrt (2*π):ℂ)*exp (-z)*(z:ℂ)^(z:ℂ))-∑ s ∈ Finset.range N, pcfGammaCoeff
s/(z:ℂ)^s) =O[atTop] (fun z : ℝ => (z:ℂ)^(-(N:ℤ)))`. -/
@[dlmf 12.10.E16]
theorem pcfGammaCoeff_expansion (N : ℕ) :
    (fun z : ℝ => Gamma (1/2+z)/((Real.sqrt (2*π):ℂ)*exp (-z)*(z:ℂ)^(z:ℂ))-∑ s ∈ Finset.range N, pcfGammaCoeff s/(z:ℂ)^s) =O[atTop] (fun z : ℝ => (z:ℂ)^(-(N:ℤ))) := by
  simp only [pcfLG_gammaCoeff_eq]; exact pcfLG_gamma_expansion N

/-- Identity under the stated parameter and domain assumptions: `pcfGammaCoeff 0=1 ∧ pcfGammaCoeff
1=-1/24 ∧ pcfGammaCoeff 2=1/1152 ∧ pcfGammaCoeff 3=1003/414720 ∧ pcfGammaCoeff
4=-4027/39813120`. -/
@[dlmf 12.10.E17]
theorem pcfGammaCoeff_initial  :
    pcfGammaCoeff 0=1 ∧ pcfGammaCoeff 1=-1/24 ∧ pcfGammaCoeff 2=1/1152 ∧ pcfGammaCoeff 3=1003/414720 ∧ pcfGammaCoeff 4=-4027/39813120 := by
  simp only [pcfLG_gammaCoeff_eq]; exact pcfLG_gammaG_values

/-- Polynomial pairs `(u_s,r_{s-1})`; the polynomial degree condition fixes the integration constant.
Existence of the chosen polynomial is asserted separately, not inferred from choice.
The `u`-equation coefficient is `3(s+1)` as in DLMF 12.10.11 (corrected 2026-10-20 from
`3/2(s+1)`, for which no polynomial solution exists at `s = 0`). -/
def pcfOlverPair : ℕ → Polynomial ℝ × Polynomial ℝ
  | 0 => (1,0)
  | s+1 =>
    let q := pcfOlverPair s
    let r := C (1/8:ℝ)*(C 3*X^2+C 2)*q.1 - C (3/2*(s+1:ℝ))*X*q.2 + C (1/2:ℝ)*(X^2-1)*derivative q.2
    (Classical.epsilon (fun p : Polynomial ℝ =>
      (X^2-1)*derivative p-C (3*(s+1:ℝ))*X*p=r ∧
      p.natDegree ≤ if Even (s+1) then 3*(s+1)-2 else 3*(s+1)),r)

/-- The polynomial coefficient U of order `s` in the Olver recurrence for cylinder expansions. -/
@[dlmf 12.10.E11]
def pcfOlverU (s : ℕ) : Polynomial ℝ :=
  (pcfOlverPair s).1

/-- The auxiliary polynomial R paired with the next U coefficient in the Olver recurrence. -/
@[dlmf 12.10.E12]
def pcfOlverR (s : ℕ) : Polynomial ℝ :=
  (pcfOlverPair (s+1)).2

/-- The derivative coefficient polynomial V obtained from the Olver U and R families. -/
@[dlmf 12.10.E13]
def pcfOlverV (s : ℕ) : Polynomial ℝ :=
  if s=0 then 1 else pcfOlverU s+C (1/2:ℝ)*X*pcfOlverU (s-1)-(pcfOlverPair (s-1)).2

/-- Coefficient recursion of `(X²-1)p' - kXp`. -/
theorem olver_homog_coeff (k : ℝ) (p : Polynomial ℝ) (n : ℕ) :
    ((X^2-1)*derivative p-C k*X*p).coeff (n+1) = (n-k) * p.coeff n - (n+2) * p.coeff (n+2) := by
  have : (X^2-1)*derivative p-C k*X*p = X^2*derivative p - derivative p - C k*(X*p) := by ring
  rw [this, coeff_sub, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative]
  rcases n with _ | n
  · simp [coeff_X_pow_mul']; ring
  · rw [show n+1+1 = n+2 by ring, coeff_X_pow_mul']
    simp [coeff_derivative]; ring

/-- Constant coefficient of `(X²-1)p' - kXp`. -/
theorem olver_homog_coeff_zero (k : ℝ) (p : Polynomial ℝ) :
    ((X^2-1)*derivative p-C k*X*p).coeff 0 = - p.coeff 1 := by
  have : (X^2-1)*derivative p-C k*X*p = X^2*derivative p - derivative p - C k*(X*p) := by ring
  rw [this]; simp [coeff_derivative]

/-- Polynomial solutions of `(X²-1)p' - 3Xp = 0` of degree `≤ 3` vanish. -/
theorem olver_homog_three {p : Polynomial ℝ} (hp : (X^2-1)*derivative p-C 3*X*p=0)
    (hd : p.natDegree ≤ 3) : p = 0 := by
  have h4 : p.coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have e0 := olver_homog_coeff_zero 3 p
  have e1 := olver_homog_coeff 3 p 0
  have e2 := olver_homog_coeff 3 p 1
  have e3 := olver_homog_coeff 3 p 2
  rw [hp, coeff_zero] at e0 e1 e2 e3
  push_cast at e1 e2 e3
  have h1 : p.coeff 1 = 0 := by linarith
  have h3 : p.coeff 3 = 0 := by linarith
  have h2 : p.coeff 2 = 0 := by linarith
  have h0 : p.coeff 0 = 0 := by linarith
  ext n
  rcases (show n ≤ 3 ∨ 3 < n by omega) with hn | hn
  · interval_cases n <;> simp [h0, h1, h2, h3]
  · simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hn)]

/-- Polynomial solutions of `(X²-1)p' - 6Xp = 0` of degree `≤ 4` vanish. -/
theorem olver_homog_six {p : Polynomial ℝ} (hp : (X^2-1)*derivative p-C 6*X*p=0)
    (hd : p.natDegree ≤ 4) : p = 0 := by
  have h5 : p.coeff 5 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h6 : p.coeff 6 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have e0 := olver_homog_coeff_zero 6 p
  have e1 := olver_homog_coeff 6 p 0
  have e2 := olver_homog_coeff 6 p 1
  have e3 := olver_homog_coeff 6 p 2
  have e4 := olver_homog_coeff 6 p 3
  have e5 := olver_homog_coeff 6 p 4
  rw [hp, coeff_zero] at e0 e1 e2 e3 e4 e5
  push_cast at e1 e2 e3 e4 e5
  have h4 : p.coeff 4 = 0 := by linarith
  have h1 : p.coeff 1 = 0 := by linarith
  have h3 : p.coeff 3 = 0 := by linarith
  have h2 : p.coeff 2 = 0 := by linarith
  have h0 : p.coeff 0 = 0 := by linarith
  ext n
  rcases (show n ≤ 4 ∨ 4 < n by omega) with hn | hn
  · interval_cases n <;> simp [h0, h1, h2, h3, h4]
  · simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hn)]

/-- A choice value is pinned down by a witness and uniqueness. -/
theorem olver_epsilon_eq {Q : Polynomial ℝ → Prop} {w : Polynomial ℝ} (hw : Q w)
    (hu : ∀ p, Q p → p = w) : Classical.epsilon Q = w :=
  hu _ (Classical.epsilon_spec ⟨w, hw⟩)

/-- Difference of two solutions of the `u`-equation. -/
theorem olver_sub_eq {k : ℝ} {r p w : Polynomial ℝ} (hp : (X^2-1)*derivative p-C k*X*p=r)
    (hw : (X^2-1)*derivative w-C k*X*w=r) : (X^2-1)*derivative (p-w)-C k*X*(p-w)=0 := by
  rw [derivative_sub]; linear_combination hp - hw

/-- The Olver operator `T_k p = (X²-1)p' - kXp` applied to a monomial. -/
theorem pcfLG_olverOp_X_pow (k : ℝ) (j : ℕ) :
    (X^2-1)*derivative (X^(j+1) : Polynomial ℝ)-C k*X*X^(j+1) =
      C ((j:ℝ)+1-k) * X^(j+2) - C ((j:ℝ)+1) * X^j := by
  rw [derivative_X_pow]
  apply Polynomial.funext; intro x
  simp; ring

/-- Homogeneous solutions of the Olver operator below the critical degree vanish. -/
theorem pcfLG_olver_homog {k : ℕ} (hk : 1 ≤ k) {q : Polynomial ℝ}
    (hq : (X^2-1)*derivative q-C (k:ℝ)*X*q=0)
    (hd : q.natDegree ≤ if Even k then k-2 else k) : q = 0 := by
  by_contra hq0
  set d := q.natDegree with hdd
  have hlc : q.coeff d ≠ 0 := by simpa [hdd] using hq0
  have e := pcfLG_coeff_rel hq d
  have hd2 : q.coeff (d+2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hd2, mul_zero, sub_zero] at e
  have hdk : d = k := by
    have : ((d:ℝ) - k) = 0 := by
      rcases mul_eq_zero.mp e with h | h
      · exact h
      · exact absurd h hlc
    exact_mod_cast sub_eq_zero.mp this
  split_ifs at hd with hke
  · obtain ⟨j, hj⟩ := hke; omega
  · have hko : Odd k := Nat.not_even_iff_odd.mp hke
    obtain ⟨m, hm⟩ := hko
    -- coefficients `q_{k-2j}` are nonzero
    have key : ∀ j ≤ m, q.coeff (k - 2*j) ≠ 0 := by
      intro j
      induction j with
      | zero => intro _; simpa [hdk] using hlc
      | succ j ih =>
        intro hj
        have h1 := ih (by omega)
        have e' := pcfLG_coeff_rel hq (k - 2*(j+1))
        rw [show k - 2*(j+1) + 2 = k - 2*j by omega] at e'
        intro h0
        rw [h0, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at e'
        rcases e' with h | h
        · have : ((k - 2*j : ℕ):ℝ) + 2 = 0 := by
            have := h; linarith
          have : (0:ℝ) < ((k - 2*j : ℕ):ℝ) + 2 := by positivity
          linarith
        · exact h1 h
    have h1 := key m le_rfl
    rw [show k - 2*m = 1 by omega] at h1
    have e0 := olver_homog_coeff_zero (k:ℝ) q
    rw [hq, coeff_zero] at e0
    exact h1 (by linarith)
where
  pcfLG_coeff_rel {k : ℕ} {q : Polynomial ℝ} (hq : (X^2-1)*derivative q-C (k:ℝ)*X*q=0) (n : ℕ) :
      ((n:ℝ) - k) * q.coeff n - ((n:ℝ)+2) * q.coeff (n+2) = 0 := by
    have := olver_homog_coeff (k:ℝ) q n
    rw [hq, coeff_zero] at this
    linarith

/-- Linearity of the Olver operator. -/
theorem pcfLG_olverOp_sub_C_mul (k a : ℝ) (p q : Polynomial ℝ) :
    (X^2-1)*derivative (p - C a * q)-C k*X*(p - C a * q) =
      ((X^2-1)*derivative p-C k*X*p) - C a * ((X^2-1)*derivative q-C k*X*q) := by
  rw [derivative_sub, derivative_C_mul]; ring

/-- Existence of polynomial solutions of `(X²-1)p' - kXp = r` for `r` of parity opposite to `k`
and degree `< k`; the solution has degree `≤ k` and the parity of `k`. -/
lemma pcfLG_olver_exists_aux {k : ℕ} (i : ℕ) : ∀ r : Polynomial ℝ,
    (∀ n, r.coeff n ≠ 0 → Odd (n+k) ∧ k - i ≤ n ∧ n < k) →
    ∃ p : Polynomial ℝ, (X^2-1)*derivative p-C (k:ℝ)*X*p = r ∧ p.natDegree ≤ k ∧
      ∀ n, p.coeff n ≠ 0 → Even (n+k) := by
  induction i with
  | zero =>
    intro r hr
    have : r = 0 := by
      ext n; by_contra h; have := hr n h; omega
    exact ⟨0, by simp [this], by simp, by simp⟩
  | succ i ih =>
    intro r hr
    by_cases hik : k < i + 1
    · exact ih r fun n hn => by have := hr n hn; exact ⟨this.1, by omega, this.2.2⟩
    set m := k - (i+1) with hm
    by_cases hc : r.coeff m = 0
    · refine ih r fun n hn => ?_
      have h := hr n hn
      refine ⟨h.1, ?_, h.2.2⟩
      rcases Nat.lt_or_ge n (k - i) with h' | h'
      · exfalso; have : n = m := by omega
        exact hn (this ▸ hc)
      · exact h'
    set c := r.coeff m
    have hmo : Odd (m + k) := (hr m hc).1
    set a : ℝ := c / ((m:ℝ)+1)
    set r' := r + C a * (C ((m:ℝ)+1-k) * X^(m+2) - C ((m:ℝ)+1) * X^m) with hr'
    have hm1 : ((m:ℝ)+1) ≠ 0 := by positivity
    have hcoef : ∀ n, r'.coeff n = r.coeff n + a * (((m:ℝ)+1-k) * (if n = m+2 then 1 else 0)
        - ((m:ℝ)+1) * (if n = m then 1 else 0)) := by
      intro n
      simp only [hr', coeff_add, coeff_C_mul, coeff_sub, coeff_X_pow]
    obtain ⟨p', hp', hpd, hpp⟩ := ih r' (by
      intro n hn
      rw [hcoef n] at hn
      by_cases hnm : n = m
      · subst hnm
        exfalso; apply hn
        have : m ≠ m + 2 := by omega
        simp only [this, ite_true, ite_false]
        simp only [a, c]; field_simp; ring
      by_cases hnm2 : n = m+2
      · subst hnm2
        have hk2 : m + 2 < k ∨ m + 1 = k := by
          obtain ⟨j, hj⟩ := hmo; omega
        rcases hk2 with hk2 | hk2
        · refine ⟨?_, by omega, hk2⟩
          obtain ⟨j, hj⟩ := hmo; exact ⟨j+1, by omega⟩
        · exfalso; apply hn
          have hr0 : r.coeff (m+2) = 0 := by
            by_contra h; have := hr _ h; omega
          have : ((m:ℝ)+1-k) = 0 := by
            have : ((m+1 : ℕ):ℝ) = k := by exact_mod_cast hk2
            push_cast at this; linarith
          simp [hr0, this]
      · simp only [hnm, hnm2, ite_false, mul_zero, sub_zero, add_zero] at hn
        have h := hr n hn
        exact ⟨h.1, by omega, h.2.2⟩)
    refine ⟨p' - C a * X^(m+1), ?_, ?_, ?_⟩
    · rw [pcfLG_olverOp_sub_C_mul, hp', pcfLG_olverOp_X_pow, hr']; ring
    · refine (natDegree_sub_le _ _).trans (max_le hpd ?_)
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_X_pow]; omega
    · intro n hn
      rw [coeff_sub, coeff_C_mul, coeff_X_pow] at hn
      by_cases hn' : n = m+1
      · subst hn'; obtain ⟨j, hj⟩ := hmo; exact ⟨j+1, by omega⟩
      · simp only [hn', ite_false, mul_zero, sub_zero] at hn
        exact hpp n hn

/-- `(X²-1)^j` solves the homogeneous Olver equation with `k = 2j`. -/
theorem pcfLG_olver_homog_sol (j : ℕ) :
    (X^2-1)*derivative ((X^2-1)^j : Polynomial ℝ)-C ((2*j:ℕ):ℝ)*X*(X^2-1)^j = 0 := by
  rcases j with _ | j
  · simp
  · rw [derivative_pow, pow_succ]
    apply Polynomial.funext; intro x
    simp; ring

/-- Existence with the Olver degree bound. -/
theorem pcfLG_olver_exists {k : ℕ} (hk : 1 ≤ k) {r : Polynomial ℝ}
    (hr : ∀ n, r.coeff n ≠ 0 → Odd (n+k) ∧ n < k) :
    ∃ p : Polynomial ℝ, (X^2-1)*derivative p-C (k:ℝ)*X*p = r ∧
      (p.natDegree ≤ if Even k then k-2 else k) ∧ ∀ n, p.coeff n ≠ 0 → Even (n+k) := by
  obtain ⟨p, hp, hpd, hpp⟩ := pcfLG_olver_exists_aux (k := k) k r
    (fun n hn => ⟨(hr n hn).1, by omega, (hr n hn).2⟩)
  split_ifs with hke
  · obtain ⟨j, hj⟩ := hke
    have hk2 : k = 2*j := by omega
    have hqe : ((X^2-1)^j : Polynomial ℝ) = expand ℝ 2 ((X-C 1)^j) := by
      simp [map_pow, map_sub, expand_X]
    have hqmon : ((X-C 1)^j : Polynomial ℝ).Monic := (monic_X_sub_C (1:ℝ)).pow j
    set q : Polynomial ℝ := (X^2-1)^j with hq
    have hqc : ∀ n, q.coeff n = if 2 ∣ n then ((X-C 1)^j : Polynomial ℝ).coeff (n/2) else 0 := by
      intro n; rw [hqe, coeff_expand (by norm_num)]
    have hqd : q.natDegree = k := by
      rw [hqe, natDegree_expand, natDegree_pow, natDegree_X_sub_C]; omega
    have hqk : q.coeff k = 1 := by
      rw [hqc]; simp only [show 2 ∣ k from ⟨j, hk2⟩, ↓reduceIte]; rw [show k/2 = j by omega]
      have := hqmon.coeff_natDegree
      rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at this
    refine ⟨p - C (p.coeff k) * q, ?_, ?_, ?_⟩
    · rw [pcfLG_olverOp_sub_C_mul, hp, show (k:ℝ) = ((2*j:ℕ):ℝ) by rw [hk2], pcfLG_olver_homog_sol]
      simp
    · have hcz : ∀ n, k - 2 < n → (p - C (p.coeff k) * q).coeff n = 0 := by
        intro n hn
        rw [coeff_sub, coeff_C_mul]
        rcases (show n = k - 1 ∨ n = k ∨ k < n by omega) with h | h | h
        · have h1 : p.coeff n = 0 := by
            by_contra h0; obtain ⟨i, hi⟩ := hpp n h0; omega
          have h2 : q.coeff n = 0 := by
            have : ¬ 2 ∣ n := by rintro ⟨i, hi⟩; omega
            rw [hqc]; simp only [this, ↓reduceIte]
          rw [h1, h2]; ring
        · subst h; rw [hqk]; ring
        · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpd h),
            coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]; ring
      by_contra hlt
      replace hlt := not_le.mp hlt
      have := hcz _ hlt
      rw [coeff_natDegree, leadingCoeff_eq_zero] at this
      rw [this, natDegree_zero] at hlt; omega
    · intro n hn
      rw [coeff_sub, coeff_C_mul] at hn
      by_contra hne
      have h1 : p.coeff n = 0 := by by_contra h0; exact hne (hpp n h0)
      have h2 : q.coeff n = 0 := by
        have : ¬ 2 ∣ n := by rintro ⟨i, hi⟩; exact hne ⟨i + j, by omega⟩
        rw [hqc]; simp only [this, ↓reduceIte]
      rw [h1, h2] at hn; simp at hn
  · exact ⟨p, hp, hpd, hpp⟩

/-- Parity–degree class: the support of `f` lies in `{n ≤ D : n ≡ e mod 2}`. -/
def PcfLGGood (e D : ℕ) (f : Polynomial ℝ) : Prop :=
  ∀ n, f.coeff n ≠ 0 → Even (n + e) ∧ n ≤ D

/-- The stated relation follows from the given hypotheses: `PcfLGGood e D' f`. -/
theorem pcfLG_good_mono {e D D' : ℕ} {f : Polynomial ℝ} (h : D ≤ D') (hf : PcfLGGood e D f) :
    PcfLGGood e D' f := fun n hn => ⟨(hf n hn).1, (hf n hn).2.trans h⟩

/-- The stated relation follows from the given hypotheses: `PcfLGGood e D f`. -/
theorem pcfLG_good_add_two {e D : ℕ} {f : Polynomial ℝ} (hf : PcfLGGood (e+2) D f) :
    PcfLGGood e D f := fun n hn => by
  obtain ⟨⟨j, hj⟩, h2⟩ := hf n hn; exact ⟨⟨j-1, by omega⟩, h2⟩

/-- The stated relation follows from the given hypotheses: `PcfLGGood (e+2) D f`. -/
theorem pcfLG_good_two {e D : ℕ} {f : Polynomial ℝ} (hf : PcfLGGood e D f) :
    PcfLGGood (e+2) D f := fun n hn => by
  obtain ⟨⟨j, hj⟩, h2⟩ := hf n hn; exact ⟨⟨j+1, by omega⟩, h2⟩

/-- The stated relation follows from the given hypotheses: `PcfLGGood e D 0`. -/
theorem pcfLG_good_zero (e D : ℕ) : PcfLGGood e D 0 := fun n hn => by simp at hn

/-- The stated relation follows from the given hypotheses: `PcfLGGood e D (f + g)`. -/
theorem pcfLG_good_add {e D : ℕ} {f g : Polynomial ℝ} (hf : PcfLGGood e D f)
    (hg : PcfLGGood e D g) : PcfLGGood e D (f + g) := fun n hn => by
  rw [coeff_add] at hn
  by_cases h : f.coeff n = 0
  · rw [h, zero_add] at hn; exact hg n hn
  · exact hf n h

/-- The stated relation follows from the given hypotheses: `PcfLGGood e D (C a * f)`. -/
theorem pcfLG_good_C_mul {e D : ℕ} {f : Polynomial ℝ} (a : ℝ) (hf : PcfLGGood e D f) :
    PcfLGGood e D (C a * f) := fun n hn => by
  rw [coeff_C_mul] at hn; exact hf n (right_ne_zero_of_mul hn)

/-- The stated relation follows from the given hypotheses: `PcfLGGood e D (f - g)`. -/
theorem pcfLG_good_sub {e D : ℕ} {f g : Polynomial ℝ} (hf : PcfLGGood e D f)
    (hg : PcfLGGood e D g) : PcfLGGood e D (f - g) := by
  rw [sub_eq_add_neg, ← neg_one_mul, show (-1 : Polynomial ℝ) = C (-1) by simp]
  exact pcfLG_good_add hf (pcfLG_good_C_mul _ hg)

/-- The stated relation follows from the given hypotheses: `PcfLGGood (e+1) (D+1) (X * f)`. -/
theorem pcfLG_good_X_mul {e D : ℕ} {f : Polynomial ℝ} (hf : PcfLGGood e D f) :
    PcfLGGood (e+1) (D+1) (X * f) := fun n hn => by
  rcases n with _ | n
  · simp at hn
  · rw [coeff_X_mul] at hn
    obtain ⟨⟨j, hj⟩, h2⟩ := hf n hn; exact ⟨⟨j+1, by omega⟩, by omega⟩

/-- The stated relation follows from the given hypotheses: `PcfLGGood (e+1) D (derivative f)`. -/
theorem pcfLG_good_derivative {e D : ℕ} {f : Polynomial ℝ} (hf : PcfLGGood e (D+1) f) :
    PcfLGGood (e+1) D (derivative f) := fun n hn => by
  rw [coeff_derivative] at hn
  obtain ⟨⟨j, hj⟩, h2⟩ := hf (n+1) (left_ne_zero_of_mul hn); exact ⟨⟨j, by omega⟩, by omega⟩

/-- One step of the Olver recursion: existence and uniqueness of `u_{s+1}`. -/
theorem pcfLG_olver_step (s : ℕ) {r : Polynomial ℝ} (hr : PcfLGGood s (3*s+2) r) :
    ∃ p : Polynomial ℝ, ((X^2-1)*derivative p-C (3*(s+1:ℝ))*X*p=r ∧
      p.natDegree ≤ if Even (s+1) then 3*(s+1)-2 else 3*(s+1)) ∧
      PcfLGGood (s+1) (3*(s+1)) p ∧
      ∀ q : Polynomial ℝ, ((X^2-1)*derivative q-C (3*(s+1:ℝ))*X*q=r ∧
        q.natDegree ≤ if Even (s+1) then 3*(s+1)-2 else 3*(s+1)) → q = p := by
  have hk : (3*(s+1:ℝ)) = ((3*(s+1) : ℕ) : ℝ) := by push_cast; ring
  have hev : Even (3*(s+1)) ↔ Even (s+1) := by
    rw [Nat.even_mul]; simp [show ¬ Even 3 by decide]
  obtain ⟨p, hp, hpd, hpp⟩ := pcfLG_olver_exists (k := 3*(s+1)) (by omega) (r := r) (by
    intro n hn
    obtain ⟨⟨j, hj⟩, h2⟩ := hr n hn
    exact ⟨⟨j+s+1, by omega⟩, by omega⟩)
  simp only [hev] at hpd
  refine ⟨p, ⟨by rw [hk]; exact hp, hpd⟩, fun n hn => ?_, fun q ⟨hq, hqd⟩ => ?_⟩
  · obtain ⟨j, hj⟩ := hpp n hn
    refine ⟨⟨j - s - 1, by omega⟩, ?_⟩
    by_contra h
    exact hn (coeff_eq_zero_of_natDegree_lt (by split_ifs at hpd <;> omega))
  · rw [hk] at hq
    refine sub_eq_zero.mp (pcfLG_olver_homog (k := 3*(s+1)) (by omega) (olver_sub_eq hq hp) ?_)
    simp only [hev]
    refine (natDegree_sub_le _ _).trans (max_le hqd hpd)

/-- The right-hand side `r_s` of the Olver recursion has parity `s` and degree `≤ 3s+2`. -/
theorem pcfLG_r_good {s : ℕ} {u ρ : Polynomial ℝ} (hu : PcfLGGood s (3*s) u)
    (hρ : PcfLGGood (s+1) (3*s+1) ρ) :
    PcfLGGood s (3*s+2) (C (1/8:ℝ)*(C 3*X^2+C 2)*u - C (3/2*(s+1:ℝ))*X*ρ +
      C (1/2:ℝ)*(X^2-1)*derivative ρ) := by
  have e : C (1/8:ℝ)*(C 3*X^2+C 2)*u - C (3/2*(s+1:ℝ))*X*ρ + C (1/2:ℝ)*(X^2-1)*derivative ρ =
      C (1/8:ℝ)*(C 3*(X*(X*u)) + C 2*u) - C (3/2*(s+1:ℝ))*(X*ρ) +
      C (1/2:ℝ)*(X*(X*derivative ρ) - derivative ρ) := by ring
  have hρ' : PcfLGGood (s+2) (3*s) (derivative ρ) := pcfLG_good_derivative hρ
  rw [e]
  refine pcfLG_good_add (pcfLG_good_sub (pcfLG_good_C_mul _ (pcfLG_good_add
    (pcfLG_good_C_mul _ (pcfLG_good_add_two (pcfLG_good_X_mul (pcfLG_good_X_mul hu))))
    (pcfLG_good_C_mul _ (pcfLG_good_mono (by omega) hu))))
    (pcfLG_good_C_mul _ (pcfLG_good_add_two (pcfLG_good_mono (by omega)
      (pcfLG_good_X_mul hρ))))) (pcfLG_good_C_mul _ (pcfLG_good_sub ?_ ?_))
  · exact pcfLG_good_add_two (pcfLG_good_add_two (pcfLG_good_X_mul (pcfLG_good_X_mul hρ')))
  · exact pcfLG_good_add_two (pcfLG_good_mono (by omega) hρ')

/-- Parity and degree invariants of the Olver pairs `(u_s, r_{s-1})`. -/
theorem pcfLG_olverPair_inv (s : ℕ) :
    PcfLGGood s (3*s) (pcfOlverPair s).1 ∧ PcfLGGood (s+1) (3*s+1) (pcfOlverPair s).2 := by
  induction s with
  | zero =>
    refine ⟨fun n hn => ?_, pcfLG_good_zero _ _⟩
    simp only [pcfOlverPair, coeff_one] at hn
    split_ifs at hn with h
    · subst h; exact ⟨⟨0, rfl⟩, le_rfl⟩
    · exact absurd rfl hn
  | succ s ih =>
    obtain ⟨hu, hρ⟩ := ih
    have hrg := pcfLG_r_good hu hρ
    set r := C (1/8:ℝ)*(C 3*X^2+C 2)*(pcfOlverPair s).1 - C (3/2*(s+1:ℝ))*X*(pcfOlverPair s).2 +
      C (1/2:ℝ)*(X^2-1)*derivative (pcfOlverPair s).2 with hr
    obtain ⟨p, hp, hpg, hpu⟩ := pcfLG_olver_step s hrg
    have hpair : pcfOlverPair (s+1) = (p, r) := by
      rw [pcfOlverPair]
      exact Prod.ext (olver_epsilon_eq hp hpu) rfl
    rw [hpair]
    exact ⟨hpg, pcfLG_good_two (pcfLG_good_mono (by omega) hrg)⟩

/-- Estimate under the stated parameter and domain assumptions: `(X^2-1)*derivative (pcfOlverU
(s+1))-C (3*(s+1:ℝ))*X*pcfOlverU (s+1)=pcfOlverR s ∧ (pcfOlverU (s+1)).natDegree ≤ if Even
(s+1) then 3*(s+1)-2 else 3*(s+1)`. -/
@[dlmf 12.10.E11]
theorem pcfOlverU_spec (s : ℕ) :
    (X^2-1)*derivative (pcfOlverU (s+1))-C (3*(s+1:ℝ))*X*pcfOlverU (s+1)=pcfOlverR s ∧ (pcfOlverU (s+1)).natDegree ≤ if Even (s+1) then 3*(s+1)-2 else 3*(s+1) := by
  obtain ⟨hu, hρ⟩ := pcfLG_olverPair_inv s
  obtain ⟨p, hp, -, hpu⟩ := pcfLG_olver_step s (pcfLG_r_good hu hρ)
  rw [pcfOlverU, pcfOlverR, pcfOlverPair]
  dsimp only
  rw [olver_epsilon_eq hp hpu]
  exact hp

/-- The first Olver pair `(u₁, r₀)`. -/
theorem pcfOlverPair_one :
    pcfOlverPair 1 = (X*(X^2-C 6)*C (1/24:ℝ), C (1/8:ℝ)*(C 3*X^2+C 2)) := by
  simp only [pcfOlverPair]
  have hw : (X^2-1)*derivative (X*(X^2-C 6)*C (1/24:ℝ))-C (3*((0:ℕ)+1:ℝ))*X*(X*(X^2-C 6)*C (1/24:ℝ)) =
      C (1/8:ℝ)*(C 3*X^2+C 2)*1 - C (3/2*((0:ℕ)+1:ℝ))*X*0 + C (1/2:ℝ)*(X^2-1)*derivative 0 := by
    apply Polynomial.funext; intro x
    simp [derivative_mul]; ring
  rw [olver_epsilon_eq (w := X*(X^2-C 6)*C (1/24:ℝ)) ⟨hw, by norm_num; compute_degree⟩]
  · simp
  · rintro _p ⟨hp, hd⟩
    have h := olver_sub_eq hp hw
    rw [show (3*((0:ℕ)+1:ℝ)) = 3 by norm_num] at h
    norm_num at hd
    refine sub_eq_zero.mp (olver_homog_three h ?_)
    refine (natDegree_sub_le _ _).trans (max_le hd ?_)
    compute_degree

/-- The chosen Olver polynomial equals any witness, given uniqueness of homogeneous solutions. -/
theorem olver_epsilon_of {k : ℝ} {N : ℕ} {r w : Polynomial ℝ}
    (hw : (X^2-1)*derivative w-C k*X*w=r) (hwd : w.natDegree ≤ N)
    (hu : ∀ q : Polynomial ℝ, (X^2-1)*derivative q-C k*X*q=0 → q.natDegree ≤ N → q = 0) :
    Classical.epsilon (fun p : Polynomial ℝ => (X^2-1)*derivative p-C k*X*p=r ∧ p.natDegree ≤ N) = w :=
  olver_epsilon_eq ⟨hw, hwd⟩ fun _ hp => sub_eq_zero.mp
    (hu _ (olver_sub_eq hp.1 hw) ((natDegree_sub_le _ _).trans (max_le hp.2 hwd)))

/-- The second Olver pair `(u₂, r₁)`. -/
theorem pcfOlverU_two : pcfOlverU 2 = (-C 9*X^4+C 249*X^2+C 145)*C (1/1152:ℝ) := by
  rw [pcfOlverU, pcfOlverPair.eq_2 1, pcfOlverPair_one]
  dsimp only
  rw [olver_epsilon_of (w := (-C 9*X^4+C 249*X^2+C 145)*C (1/1152:ℝ))]
  · apply Polynomial.funext; intro x
    simp [derivative_mul]; ring
  · norm_num; compute_degree
  · intro q hq hd
    rw [show (3*((1:ℕ)+1:ℝ)) = 6 by norm_num] at hq
    norm_num at hd
    exact olver_homog_six hq hd

/-- Identity under the stated parameter and domain assumptions: `pcfOlverU 0=1 ∧ pcfOlverU
1=X*(X^2-C 6)*C (1/24:ℝ) ∧ pcfOlverU 2=(-C 9*X^4+C 249*X^2+C 145)*C (1/1152:ℝ) ∧ pcfOlverV 0=1
∧ pcfOlverV 1=X*(X^2+C 6)*C (1/24:ℝ) ∧ pcfOlverV 2=(C 15*X^4-C 327*X^2-C 143)*C (1/1152:ℝ)`. -/
@[dlmf 12.10.E9, dlmf 12.10.E10]
theorem pcfOlverUV_initial  :
    pcfOlverU 0=1 ∧ pcfOlverU 1=X*(X^2-C 6)*C (1/24:ℝ) ∧ pcfOlverU 2=(-C 9*X^4+C 249*X^2+C 145)*C (1/1152:ℝ) ∧ pcfOlverV 0=1 ∧ pcfOlverV 1=X*(X^2+C 6)*C (1/24:ℝ) ∧ pcfOlverV 2=(C 15*X^4-C 327*X^2-C 143)*C (1/1152:ℝ) := by
  have hU1 : pcfOlverU 1 = X*(X^2-C 6)*C (1/24:ℝ) := by rw [pcfOlverU, pcfOlverPair_one]
  refine ⟨by simp [pcfOlverU, pcfOlverPair], hU1, pcfOlverU_two, by simp [pcfOlverV], ?_, ?_⟩
  · rw [show pcfOlverV 1 = pcfOlverU 1 + C (1/2:ℝ)*X*pcfOlverU 0 - (pcfOlverPair 0).2 from rfl, hU1]
    simp only [pcfOlverU, pcfOlverPair]
    apply Polynomial.funext; intro x
    simp; ring
  · rw [show pcfOlverV 2 = pcfOlverU 2 + C (1/2:ℝ)*X*pcfOlverU 1 - (pcfOlverPair 1).2 from rfl, hU1, pcfOlverU_two, pcfOlverPair_one]
    apply Polynomial.funext; intro x
    simp; ring

end DLMF.Confluent
end
