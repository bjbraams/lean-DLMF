/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.AsymptoticsZeros
public import DLMF.Airy.Basic
public import DLMFMathlib.Analysis.Calculus.DoubleZeroSqrt
public import DLMFMathlib.Analysis.Calculus.InverseSeries

/-!
# Olver and Temme uniform cylinder expansions and coefficient systems

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open Polynomial

/-- pcfXi. -/
@[dlmf 12.10.E7]
def pcfXi (t : ℝ) : ℝ :=
  (t*Real.sqrt (t^2-1)-Real.log (t+Real.sqrt (t^2-1)))/2

/-- pcfEta. -/
@[dlmf 12.10.E23]
def pcfEta (t : ℝ) : ℝ :=
  (Real.arccos t-t*Real.sqrt (1-t^2))/2

/-- pcfXiBar. -/
@[dlmf 12.10.E26]
def pcfXiBar (t : ℝ) : ℝ :=
  (t*Real.sqrt (t^2+1)+Real.log (t+Real.sqrt (t^2+1)))/2

/-- pcfH. -/
@[dlmf 12.10.E15]
def pcfH (μ : ℂ) : ℂ :=
  2^(-μ^2/4-1/4)*exp (-μ^2/4)*μ^(μ^2/2-1/2)

/-- pcfGammaCoeff. -/
@[dlmf 12.10.E16]
def pcfGammaCoeff (s : ℕ) : ℂ :=
  asymptoticCoeff (fun z : ℝ => Gamma (1/2+z)/((Real.sqrt (2*π):ℂ)*exp (-z)*(z:ℂ)^(z:ℂ))) s

/-- Coefficients identified by limits: if `f(t) = ∑_{s<N} c_s t^{-s} + O(t^{-N})` for all `N`,
then the successive limits `asymptoticCoeff f` are the `c_s`. -/
lemma pcfLG_asymptoticCoeff_eq {f : ℝ → ℂ} {c : ℕ → ℂ}
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
lemma pcfLG_gammaG_recurrence (n : ℕ) :
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
lemma pcfLG_gamma_ratio_eq {t : ℝ} (ht : 0 < t) :
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
lemma pcfLG_gamma_expansion (N : ℕ) :
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
lemma pcfLG_bernoulli_half (n : ℕ) (hn : n ≤ 5) :
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
lemma pcfLG_gammaG_values : pcfLG_gammaG 0 = 1 ∧ pcfLG_gammaG 1 = -1/24 ∧ pcfLG_gammaG 2 = 1/1152 ∧
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
lemma pcfLG_gammaCoeff_eq (s : ℕ) : pcfGammaCoeff s = pcfLG_gammaG s :=
  pcfLG_asymptoticCoeff_eq pcfLG_gamma_expansion s

/-- pcfGammaCoeff expansion. -/
@[dlmf 12.10.E16]
theorem pcfGammaCoeff_expansion (N : ℕ) :
    (fun z : ℝ => Gamma (1/2+z)/((Real.sqrt (2*π):ℂ)*exp (-z)*(z:ℂ)^(z:ℂ))-∑ s ∈ Finset.range N, pcfGammaCoeff s/(z:ℂ)^s) =O[atTop] (fun z : ℝ => (z:ℂ)^(-(N:ℤ))) := by
  simp only [pcfLG_gammaCoeff_eq]; exact pcfLG_gamma_expansion N

/-- pcfGammaCoeff initial. -/
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

/-- pcfOlverU. -/
@[dlmf 12.10.E11]
def pcfOlverU (s : ℕ) : Polynomial ℝ :=
  (pcfOlverPair s).1

/-- pcfOlverR. -/
@[dlmf 12.10.E12]
def pcfOlverR (s : ℕ) : Polynomial ℝ :=
  (pcfOlverPair (s+1)).2

/-- pcfOlverV. -/
@[dlmf 12.10.E13]
def pcfOlverV (s : ℕ) : Polynomial ℝ :=
  if s=0 then 1 else pcfOlverU s+C (1/2:ℝ)*X*pcfOlverU (s-1)-(pcfOlverPair (s-1)).2

/-- Coefficient recursion of `(X²-1)p' - kXp`. -/
lemma olver_homog_coeff (k : ℝ) (p : Polynomial ℝ) (n : ℕ) :
    ((X^2-1)*derivative p-C k*X*p).coeff (n+1) = (n-k) * p.coeff n - (n+2) * p.coeff (n+2) := by
  have : (X^2-1)*derivative p-C k*X*p = X^2*derivative p - derivative p - C k*(X*p) := by ring
  rw [this, coeff_sub, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative]
  rcases n with _ | n
  · simp [coeff_X_pow_mul']; ring
  · rw [show n+1+1 = n+2 by ring, coeff_X_pow_mul']
    simp [coeff_derivative]; ring

/-- Constant coefficient of `(X²-1)p' - kXp`. -/
lemma olver_homog_coeff_zero (k : ℝ) (p : Polynomial ℝ) :
    ((X^2-1)*derivative p-C k*X*p).coeff 0 = - p.coeff 1 := by
  have : (X^2-1)*derivative p-C k*X*p = X^2*derivative p - derivative p - C k*(X*p) := by ring
  rw [this]; simp [coeff_derivative]

/-- Polynomial solutions of `(X²-1)p' - 3Xp = 0` of degree `≤ 3` vanish. -/
lemma olver_homog_three {p : Polynomial ℝ} (hp : (X^2-1)*derivative p-C 3*X*p=0)
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
lemma olver_homog_six {p : Polynomial ℝ} (hp : (X^2-1)*derivative p-C 6*X*p=0)
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
lemma olver_epsilon_eq {Q : Polynomial ℝ → Prop} {w : Polynomial ℝ} (hw : Q w)
    (hu : ∀ p, Q p → p = w) : Classical.epsilon Q = w :=
  hu _ (Classical.epsilon_spec ⟨w, hw⟩)

/-- Difference of two solutions of the `u`-equation. -/
lemma olver_sub_eq {k : ℝ} {r p w : Polynomial ℝ} (hp : (X^2-1)*derivative p-C k*X*p=r)
    (hw : (X^2-1)*derivative w-C k*X*w=r) : (X^2-1)*derivative (p-w)-C k*X*(p-w)=0 := by
  rw [derivative_sub]; linear_combination hp - hw

/-- The Olver operator `T_k p = (X²-1)p' - kXp` applied to a monomial. -/
lemma pcfLG_olverOp_X_pow (k : ℝ) (j : ℕ) :
    (X^2-1)*derivative (X^(j+1) : Polynomial ℝ)-C k*X*X^(j+1) =
      C ((j:ℝ)+1-k) * X^(j+2) - C ((j:ℝ)+1) * X^j := by
  rw [derivative_X_pow]
  apply Polynomial.funext; intro x
  simp; ring

/-- Homogeneous solutions of the Olver operator below the critical degree vanish. -/
lemma pcfLG_olver_homog {k : ℕ} (hk : 1 ≤ k) {q : Polynomial ℝ}
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
lemma pcfLG_olverOp_sub_C_mul (k a : ℝ) (p q : Polynomial ℝ) :
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
lemma pcfLG_olver_homog_sol (j : ℕ) :
    (X^2-1)*derivative ((X^2-1)^j : Polynomial ℝ)-C ((2*j:ℕ):ℝ)*X*(X^2-1)^j = 0 := by
  rcases j with _ | j
  · simp
  · rw [derivative_pow, pow_succ]
    apply Polynomial.funext; intro x
    simp; ring

/-- Existence with the Olver degree bound. -/
lemma pcfLG_olver_exists {k : ℕ} (hk : 1 ≤ k) {r : Polynomial ℝ}
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
def pcfLG_good (e D : ℕ) (f : Polynomial ℝ) : Prop :=
  ∀ n, f.coeff n ≠ 0 → Even (n + e) ∧ n ≤ D

lemma pcfLG_good_mono {e D D' : ℕ} {f : Polynomial ℝ} (h : D ≤ D') (hf : pcfLG_good e D f) :
    pcfLG_good e D' f := fun n hn => ⟨(hf n hn).1, (hf n hn).2.trans h⟩

lemma pcfLG_good_add_two {e D : ℕ} {f : Polynomial ℝ} (hf : pcfLG_good (e+2) D f) :
    pcfLG_good e D f := fun n hn => by
  obtain ⟨⟨j, hj⟩, h2⟩ := hf n hn; exact ⟨⟨j-1, by omega⟩, h2⟩

lemma pcfLG_good_two {e D : ℕ} {f : Polynomial ℝ} (hf : pcfLG_good e D f) :
    pcfLG_good (e+2) D f := fun n hn => by
  obtain ⟨⟨j, hj⟩, h2⟩ := hf n hn; exact ⟨⟨j+1, by omega⟩, h2⟩

lemma pcfLG_good_zero (e D : ℕ) : pcfLG_good e D 0 := fun n hn => by simp at hn

lemma pcfLG_good_add {e D : ℕ} {f g : Polynomial ℝ} (hf : pcfLG_good e D f)
    (hg : pcfLG_good e D g) : pcfLG_good e D (f + g) := fun n hn => by
  rw [coeff_add] at hn
  by_cases h : f.coeff n = 0
  · rw [h, zero_add] at hn; exact hg n hn
  · exact hf n h

lemma pcfLG_good_C_mul {e D : ℕ} {f : Polynomial ℝ} (a : ℝ) (hf : pcfLG_good e D f) :
    pcfLG_good e D (C a * f) := fun n hn => by
  rw [coeff_C_mul] at hn; exact hf n (right_ne_zero_of_mul hn)

lemma pcfLG_good_sub {e D : ℕ} {f g : Polynomial ℝ} (hf : pcfLG_good e D f)
    (hg : pcfLG_good e D g) : pcfLG_good e D (f - g) := by
  rw [sub_eq_add_neg, ← neg_one_mul, show (-1 : Polynomial ℝ) = C (-1) by simp]
  exact pcfLG_good_add hf (pcfLG_good_C_mul _ hg)

lemma pcfLG_good_X_mul {e D : ℕ} {f : Polynomial ℝ} (hf : pcfLG_good e D f) :
    pcfLG_good (e+1) (D+1) (X * f) := fun n hn => by
  rcases n with _ | n
  · simp at hn
  · rw [coeff_X_mul] at hn
    obtain ⟨⟨j, hj⟩, h2⟩ := hf n hn; exact ⟨⟨j+1, by omega⟩, by omega⟩

lemma pcfLG_good_derivative {e D : ℕ} {f : Polynomial ℝ} (hf : pcfLG_good e (D+1) f) :
    pcfLG_good (e+1) D (derivative f) := fun n hn => by
  rw [coeff_derivative] at hn
  obtain ⟨⟨j, hj⟩, h2⟩ := hf (n+1) (left_ne_zero_of_mul hn); exact ⟨⟨j, by omega⟩, by omega⟩

/-- One step of the Olver recursion: existence and uniqueness of `u_{s+1}`. -/
lemma pcfLG_olver_step (s : ℕ) {r : Polynomial ℝ} (hr : pcfLG_good s (3*s+2) r) :
    ∃ p : Polynomial ℝ, ((X^2-1)*derivative p-C (3*(s+1:ℝ))*X*p=r ∧
      p.natDegree ≤ if Even (s+1) then 3*(s+1)-2 else 3*(s+1)) ∧
      pcfLG_good (s+1) (3*(s+1)) p ∧
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
lemma pcfLG_r_good {s : ℕ} {u ρ : Polynomial ℝ} (hu : pcfLG_good s (3*s) u)
    (hρ : pcfLG_good (s+1) (3*s+1) ρ) :
    pcfLG_good s (3*s+2) (C (1/8:ℝ)*(C 3*X^2+C 2)*u - C (3/2*(s+1:ℝ))*X*ρ +
      C (1/2:ℝ)*(X^2-1)*derivative ρ) := by
  have e : C (1/8:ℝ)*(C 3*X^2+C 2)*u - C (3/2*(s+1:ℝ))*X*ρ + C (1/2:ℝ)*(X^2-1)*derivative ρ =
      C (1/8:ℝ)*(C 3*(X*(X*u)) + C 2*u) - C (3/2*(s+1:ℝ))*(X*ρ) +
      C (1/2:ℝ)*(X*(X*derivative ρ) - derivative ρ) := by ring
  have hρ' : pcfLG_good (s+2) (3*s) (derivative ρ) := pcfLG_good_derivative hρ
  rw [e]
  refine pcfLG_good_add (pcfLG_good_sub (pcfLG_good_C_mul _ (pcfLG_good_add
    (pcfLG_good_C_mul _ (pcfLG_good_add_two (pcfLG_good_X_mul (pcfLG_good_X_mul hu))))
    (pcfLG_good_C_mul _ (pcfLG_good_mono (by omega) hu))))
    (pcfLG_good_C_mul _ (pcfLG_good_add_two (pcfLG_good_mono (by omega)
      (pcfLG_good_X_mul hρ))))) (pcfLG_good_C_mul _ (pcfLG_good_sub ?_ ?_))
  · exact pcfLG_good_add_two (pcfLG_good_add_two (pcfLG_good_X_mul (pcfLG_good_X_mul hρ')))
  · exact pcfLG_good_add_two (pcfLG_good_mono (by omega) hρ')

/-- Parity and degree invariants of the Olver pairs `(u_s, r_{s-1})`. -/
lemma pcfLG_olverPair_inv (s : ℕ) :
    pcfLG_good s (3*s) (pcfOlverPair s).1 ∧ pcfLG_good (s+1) (3*s+1) (pcfOlverPair s).2 := by
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

/-- pcfOlverU spec. -/
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
lemma pcfOlverPair_one :
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
lemma olver_epsilon_of {k : ℝ} {N : ℕ} {r w : Polynomial ℝ}
    (hw : (X^2-1)*derivative w-C k*X*w=r) (hwd : w.natDegree ≤ N)
    (hu : ∀ q : Polynomial ℝ, (X^2-1)*derivative q-C k*X*q=0 → q.natDegree ≤ N → q = 0) :
    Classical.epsilon (fun p : Polynomial ℝ => (X^2-1)*derivative p-C k*X*p=r ∧ p.natDegree ≤ N) = w :=
  olver_epsilon_eq ⟨hw, hwd⟩ fun _ hp => sub_eq_zero.mp
    (hu _ (olver_sub_eq hp.1 hw) ((natDegree_sub_le _ _).trans (max_le hp.2 hwd)))

/-- The second Olver pair `(u₂, r₁)`. -/
lemma pcfOlverU_two : pcfOlverU 2 = (-C 9*X^4+C 249*X^2+C 145)*C (1/1152:ℝ) := by
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

/-- pcfOlverUV initial. -/
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

/-- pcfOlverA. -/
@[dlmf 12.10.E8]
def pcfOlverA (s : ℕ) (t : ℝ) : ℂ :=
  (((pcfOlverU s).eval t:ℝ):ℂ)/(t^2-1:ℂ)^(3*(s:ℂ)/2)

/-- pcfOlverATilde. -/
@[dlmf 12.10.E24]
def pcfOlverATilde (s : ℕ) (t : ℝ) : ℂ :=
  (((pcfOlverU s).eval t:ℝ):ℂ)/(1-t^2:ℂ)^(3*(s:ℂ)/2)

/-- pcfOlverUBar. -/
@[dlmf 12.10.E27]
def pcfOlverUBar (s : ℕ) (t : ℝ) : ℂ :=
  I^s*aeval (-I*t) (pcfOlverU s)

/-- pcfOlverB. -/
@[dlmf 12.10.E8]
def pcfOlverB (s : ℕ) (t : ℝ) : ℂ :=
  (((pcfOlverV s).eval t:ℝ):ℂ)/(t^2-1:ℂ)^(3*(s:ℂ)/2)

/-- pcfOlverBTilde. -/
@[dlmf 12.10.E24]
def pcfOlverBTilde (s : ℕ) (t : ℝ) : ℂ :=
  (((pcfOlverV s).eval t:ℝ):ℂ)/(1-t^2:ℂ)^(3*(s:ℂ)/2)

/-- pcfOlverVBar. -/
@[dlmf 12.10.E30]
def pcfOlverVBar (s : ℕ) (t : ℝ) : ℂ :=
  I^s*aeval (-I*t) (pcfOlverV s)

/-- pcfUniformFilter. -/
def pcfUniformFilter (S : Set ℝ) : Filter (ℝ × ℝ) :=
  comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | p.2 ∈ S}

/-- HasCylinderUniformExpansion. -/
def HasCylinderUniformExpansion (F : ℝ → ℝ → ℂ) (C : ℕ → ℝ → ℂ) (S : Set ℝ) : Prop :=
  ∀ N : ℕ, (fun p : ℝ × ℝ => F p.1 p.2-∑ s ∈ Finset.range N, C s p.2/(p.1:ℂ)^(2*s)) =O[pcfUniformFilter S] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ)))

/-- IsCylinderGNormalizer. -/
@[dlmf 12.10.E14]
def IsCylinderGNormalizer (g : ℝ → ℂ) : Prop :=
  ∀ N : ℕ, (fun μ : ℝ => g μ/pcfH μ-1-1/2*∑ j ∈ Finset.range N, pcfGammaCoeff (j+1)/(μ^2/2:ℂ)^(j+1)) =O[atTop] (fun μ : ℝ => (μ:ℂ)^(-(2*(N+1):ℤ)))

/-- pcf negative parameter uniform. -/
@[dlmf 12.10.E3, dlmf 12.10.E4, dlmf 12.10.E5, dlmf 12.10.E6, dlmf 12.10.E14]
theorem pcf_negative_parameter_uniform  :
    ∃ g : ℝ → ℂ, IsCylinderGNormalizer g ∧ ∀ δ : ℝ, 0 < δ → HasCylinderUniformExpansion (fun μ t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2)/(g μ*exp (-μ^2*pcfXi t)/(t^2-1:ℂ)^(1/4:ℂ))) (fun s t => pcfOlverA s t) (Ici (1+δ)) ∧ HasCylinderUniformExpansion (fun μ t => pcfUDeriv (-μ^2/2) (μ*t*Real.sqrt 2)/(-(μ:ℂ)/Real.sqrt 2*g μ*(t^2-1:ℂ)^(1/4:ℂ)*exp (-μ^2*pcfXi t))) (fun s t => pcfOlverB s t) (Ici (1+δ)) ∧ HasCylinderUniformExpansion (fun μ t => pcfV (-μ^2/2) (μ*t*Real.sqrt 2)/(2*g μ/Gamma (1/2+μ^2/2)*exp (μ^2*pcfXi t)/(t^2-1:ℂ)^(1/4:ℂ))) (fun s t => (-1)^s*pcfOlverA s t) (Ici (1+δ)) ∧ HasCylinderUniformExpansion (fun μ t => pcfVDeriv (-μ^2/2) (μ*t*Real.sqrt 2)/(Real.sqrt 2*μ*g μ/Gamma (1/2+μ^2/2)*(t^2-1:ℂ)^(1/4:ℂ)*exp (μ^2*pcfXi t))) (fun s t => (-1)^s*pcfOlverB s t) (Ici (1+δ)) := by
  sorry

/-- pcfKappa. -/
@[dlmf 12.10.E22]
def pcfKappa (μ t : ℝ) : ℝ :=
  μ^2*pcfEta t-π/4

/-- pcfChi. -/
@[dlmf 12.10.E22]
def pcfChi (μ t : ℝ) : ℝ :=
  μ^2*pcfEta t+π/4

/-- pcf oscillatory parameter uniform. -/
@[dlmf 12.10.E18, dlmf 12.10.E19, dlmf 12.10.E20, dlmf 12.10.E21]
theorem pcf_oscillatory_parameter_uniform  :
    ∃ g : ℝ → ℂ, IsCylinderGNormalizer g ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ N : ℕ, (fun p : ℝ × ℝ => pcfU (-p.1^2/2) (p.1*p.2*Real.sqrt 2)/(2*g p.1/(1-p.2^2:ℂ)^(1/4:ℂ))-∑ s ∈ Finset.range N, Real.cos (pcfKappa p.1 p.2+s*π/2)*pcfOlverATilde s p.2/(p.1:ℂ)^(2*s)) =O[pcfUniformFilter (Icc (-1+δ) (1-δ))] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ))) ∧ (fun p : ℝ × ℝ => pcfUDeriv (-p.1^2/2) (p.1*p.2*Real.sqrt 2)/(p.1*Real.sqrt 2*g p.1*(1-p.2^2:ℂ)^(1/4:ℂ))-∑ s ∈ Finset.range N, Real.sin (pcfKappa p.1 p.2+s*π/2)*pcfOlverBTilde s p.2/(p.1:ℂ)^(2*s)) =O[pcfUniformFilter (Icc (-1+δ) (1-δ))] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ))) ∧ (fun p : ℝ × ℝ => pcfV (-p.1^2/2) (p.1*p.2*Real.sqrt 2)/(2*g p.1/(Gamma (1/2+p.1^2/2)*(1-p.2^2:ℂ)^(1/4:ℂ)))-∑ s ∈ Finset.range N, Real.cos (pcfChi p.1 p.2+s*π/2)*pcfOlverATilde s p.2/(p.1:ℂ)^(2*s)) =O[pcfUniformFilter (Icc (-1+δ) (1-δ))] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ))) ∧ (fun p : ℝ × ℝ => pcfVDeriv (-p.1^2/2) (p.1*p.2*Real.sqrt 2)/(p.1*Real.sqrt 2*g p.1*(1-p.2^2:ℂ)^(1/4:ℂ)/Gamma (1/2+p.1^2/2))-∑ s ∈ Finset.range N, Real.sin (pcfChi p.1 p.2+s*π/2)*pcfOlverBTilde s p.2/(p.1:ℂ)^(2*s)) =O[pcfUniformFilter (Icc (-1+δ) (1-δ))] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ))) := by
  sorry

/-- IsCylinderGBarNormalizer. -/
@[dlmf 12.10.E28]
def IsCylinderGBarNormalizer (g : ℝ → ℂ) : Prop :=
  ∀ N : ℕ, (fun μ : ℝ => g μ*μ*Real.sqrt 2*pcfH μ-1-1/2*∑ j ∈ Finset.range N, (-1)^(j+1)*pcfGammaCoeff (j+1)/(μ^2/2:ℂ)^(j+1)) =O[atTop] (fun μ : ℝ => (μ:ℂ)^(-(2*(N+1):ℤ)))

-- `pcf_positive_parameter_uniform` (DLMF 12.10.25, 12.10.29) is stated and proved in
-- `DLMF/ParabolicCylinder/UniformLG2.lean`.

/-- pcfTau. -/
@[dlmf 12.10.E32]
def pcfTau (t : ℝ) : ℝ :=
  (t/Real.sqrt (t^2-1)-1)/2

/-- Polynomial primitive based at zero. -/
def pcfPolyPrimitive (p : Polynomial ℝ) : Polynomial ℝ :=
  p.sum (fun n c => C (c/(n+1))*X^(n+1))

/-- Temme polynomials, with an explicit derivative-integral recursion. -/
def pcfTemmePoly : ℕ → Polynomial ℝ
  | 0 => 1
  | s+1 => -C 4*X^2*(X+1)^2*derivative (pcfTemmePoly s)-C (1/4:ℝ)*pcfPolyPrimitive ((C 20*X^2+C 20*X+C 3)*pcfTemmePoly s)

/-- Real polynomials with equal derivatives and equal values at `0` are equal. -/
lemma pcfPoly_eq_of_derivative_eq {P Q : Polynomial ℝ} (hd : derivative P = derivative Q)
    (h0 : P.eval 0 = Q.eval 0) : P = Q := by
  have hc : ∀ x : ℝ, HasDerivAt (fun x => (P - Q).eval x) 0 x := fun x => by
    have := (P - Q).hasDerivAt x
    rwa [derivative_sub, hd, sub_self, eval_zero] at this
  have := fun x => is_const_of_deriv_eq_zero (fun x => (hc x).differentiableAt) (fun x => (hc x).deriv) x 0
  refine sub_eq_zero.mp (Polynomial.funext fun x => ?_)
  rw [this x, eval_sub, h0, sub_self, eval_zero]

/-- The primitive is additive. -/
lemma pcfPolyPrimitive_add (p q : Polynomial ℝ) :
    pcfPolyPrimitive (p + q) = pcfPolyPrimitive p + pcfPolyPrimitive q := by
  unfold pcfPolyPrimitive
  exact Polynomial.sum_add_index _ _ _ (fun n => by simp) (fun n a b => by rw [add_div, C_add, add_mul])

/-- The primitive of a monomial. -/
lemma pcfPolyPrimitive_monomial (n : ℕ) (c : ℝ) :
    pcfPolyPrimitive (monomial n c) = C (c/(n+1)) * X^(n+1) := by
  unfold pcfPolyPrimitive
  exact Polynomial.sum_monomial_index _ _ (by simp)

/-- The primitive has derivative `p`. -/
lemma derivative_pcfPolyPrimitive (p : Polynomial ℝ) : derivative (pcfPolyPrimitive p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [pcfPolyPrimitive_add, derivative_add, hp, hq]
  | monomial n c =>
    rw [pcfPolyPrimitive_monomial, derivative_C_mul_X_pow, ← C_mul_X_pow_eq_monomial]
    congr 1
    · congr 1; push_cast; field_simp

/-- The primitive vanishes at `0`. -/
lemma eval_zero_pcfPolyPrimitive (p : Polynomial ℝ) : (pcfPolyPrimitive p).eval 0 = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [pcfPolyPrimitive_add, eval_add, hp, hq, add_zero]
  | monomial n c => simp [pcfPolyPrimitive_monomial]

/-- Characterization of the primitive. -/
lemma pcfPolyPrimitive_eq {p P : Polynomial ℝ} (hd : derivative P = p) (h0 : P.eval 0 = 0) :
    pcfPolyPrimitive p = P :=
  pcfPoly_eq_of_derivative_eq (by rw [derivative_pcfPolyPrimitive, hd]) (by rw [eval_zero_pcfPolyPrimitive, h0])

/-- pcfTemmePoly initial. -/
@[dlmf 12.10.E34]
theorem pcfTemmePoly_initial  :
    pcfTemmePoly 1=-C (1/12:ℝ)*X*(C 20*X^2+C 30*X+C 9) ∧ pcfTemmePoly 2=C (1/288:ℝ)*X^2*(C 6160*X^4+C 18480*X^3+C 19404*X^2+C 8028*X+C 945) := by
  have h1 : pcfTemmePoly 1 = -C (1/12:ℝ)*X*(C 20*X^2+C 30*X+C 9) := by
    rw [pcfTemmePoly, pcfTemmePoly, pcfPolyPrimitive_eq (P := C (20/3:ℝ)*X^3 + C 10*X^2 + C 3*X)]
    · apply Polynomial.funext; intro r; simp; ring
    · apply Polynomial.funext; intro r; simp; ring
    · simp
  refine ⟨h1, ?_⟩
  rw [show (2:ℕ) = 1 + 1 from rfl, pcfTemmePoly, h1,
    pcfPolyPrimitive_eq (P := -C (1/12:ℝ) * (C (400/6:ℝ)*X^6 + C 200*X^5 + C 210*X^4 + C 90*X^3 + C (27/2:ℝ)*X^2))]
  · apply Polynomial.funext; intro r; simp; ring
  · apply Polynomial.funext; intro r; simp; ring
  · simp

/-- pcfTemmePoly recurrence. -/
@[dlmf 12.10.E33]
theorem pcfTemmePoly_recurrence (s : ℕ) (τ : ℝ) :
    (pcfTemmePoly (s+1)).eval τ=-4*τ^2*(τ+1)^2*(derivative (pcfTemmePoly s)).eval τ-1/4*∫ u : ℝ in 0..τ, (20*u^2+20*u+3)*(pcfTemmePoly s).eval u := by
  set q := (C 20*X^2+C 20*X+C 3)*pcfTemmePoly s
  have hint : ∫ u : ℝ in 0..τ, (20*u^2+20*u+3)*(pcfTemmePoly s).eval u = (pcfPolyPrimitive q).eval τ := by
    have : ∀ u : ℝ, (20*u^2+20*u+3)*(pcfTemmePoly s).eval u = q.eval u := fun u => by simp [q]
    simp_rw [this]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => (pcfPolyPrimitive q).eval u)
      (fun u _ => by simpa [derivative_pcfPolyPrimitive] using (pcfPolyPrimitive q).hasDerivAt u)
      (q.continuous.intervalIntegrable _ _), eval_zero_pcfPolyPrimitive, sub_zero]
  rw [hint, pcfTemmePoly]
  simp [q]

-- `pcfU_temme_uniform` (DLMF 12.10.31) is stated and proved in
-- `DLMF/ParabolicCylinder/UniformLG2.lean`.

/-- pcfZeta. -/
@[dlmf 12.10.E39]
def pcfZeta (t : ℝ) : ℝ :=
  if 1 ≤ t then (3/2*pcfXi t)^(2/3:ℝ) else -(3/2*pcfEta t)^(2/3:ℝ)

/-- Inverse turning-point coordinate; its domain and uniqueness are asserted separately. -/
def pcfInverseZeta (ζ : ℝ) : ℝ :=
  Classical.epsilon (fun t : ℝ => -1 < t ∧ pcfZeta t=ζ)

/-- `ξ' = √(t²-1)` (DLMF 12.10.7). -/
lemma pcfZ_hasDerivAt_xi {t : ℝ} (ht : 1 < t) :
    HasDerivAt pcfXi (Real.sqrt (t^2-1)) t := by
  have hy : 0 < t^2-1 := by nlinarith
  set r := Real.sqrt (t^2-1) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hy
  have hr2 : r^2 = t^2-1 := Real.sq_sqrt hy.le
  have h1 : HasDerivAt (fun t : ℝ => t^2-1) (2*t) t := by
    simpa using (hasDerivAt_pow 2 t).sub_const 1
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (t^2-1)) (2*t / (2 * r)) t := h1.sqrt hy.ne'
  have htr : 0 < t + r := by linarith
  have hl : HasDerivAt (fun t : ℝ => Real.log (t + Real.sqrt (t^2-1))) ((1 + 2*t/(2*r)) / (t + r)) t :=
    ((hasDerivAt_id t).add hs).log htr.ne'
  have := (((hasDerivAt_id t).mul hs).sub hl).div_const 2
  have e : pcfXi = fun x => ((((id : ℝ → ℝ) * fun t : ℝ => Real.sqrt (t^2-1)) -
      fun t : ℝ => Real.log (t + Real.sqrt (t^2-1))) : ℝ → ℝ) x / 2 := by
    funext x; simp [pcfXi]
  rw [e]
  convert this using 1
  simp only [id]
  field_simp
  rw [← hr]
  nlinarith [hr2]

/-- `η' = -√(1-t²)` (DLMF 12.10.23). -/
lemma pcfZ_hasDerivAt_eta {t : ℝ} (ht : -1 < t) (ht1 : t < 1) :
    HasDerivAt pcfEta (-Real.sqrt (1-t^2)) t := by
  have hy : 0 < 1-t^2 := by nlinarith
  set r := Real.sqrt (1-t^2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hy
  have hr2 : r^2 = 1-t^2 := Real.sq_sqrt hy.le
  have h1 : HasDerivAt (fun t : ℝ => 1-t^2) (-(2*t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_sub 1
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (1-t^2)) (-(2*t) / (2 * r)) t := h1.sqrt hy.ne'
  have ha := Real.hasDerivAt_arccos ht.ne' ht1.ne
  have := ((ha.sub ((hasDerivAt_id t).mul hs))).div_const 2
  have e : pcfEta = fun x => (Real.arccos x - ((id : ℝ → ℝ) * fun t : ℝ => Real.sqrt (1-t^2)) x) / 2 := by
    funext x; simp [pcfEta]
  rw [e]
  convert this using 1
  simp only [id]
  rw [← hr]
  field_simp
  nlinarith [hr2]

/-- `η` is continuous. -/
lemma pcfZ_continuous_eta : Continuous pcfEta := by
  unfold pcfEta; fun_prop

/-- `ξ` is continuous on `[1, ∞)`. -/
lemma pcfZ_continuousOn_xi : ContinuousOn pcfXi (Ici 1) := by
  intro t ht
  have ht : (1:ℝ) ≤ t := ht
  have h0 : 0 < t + Real.sqrt (t^2-1) := by positivity
  refine ContinuousAt.continuousWithinAt ?_
  unfold pcfXi
  have hs : Continuous fun t : ℝ => Real.sqrt (t^2-1) := by fun_prop
  exact (((continuous_id.mul hs).continuousAt).sub
    ((continuous_id.add hs).continuousAt.log h0.ne')).div_const 2

/-- `ξ(t) = ∫₁ᵗ √(s²-1) ds`. -/
lemma pcfZ_xi_eq_integral {t : ℝ} (ht : 1 ≤ t) :
    pcfXi t = ∫ s in (1:ℝ)..t, Real.sqrt ((s - 1) * (s + 1)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (pcfZ_continuousOn_xi.mono Icc_subset_Ici_self)
    (fun s hs => by
      rw [show (s - 1) * (s + 1) = s^2 - 1 by ring]; exact pcfZ_hasDerivAt_xi hs.1)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [pcfXi]

/-- `η(t) = ∫ₜ¹ √(1-s²) ds`. -/
lemma pcfZ_eta_eq_integral {t : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1) :
    pcfEta t = ∫ s in t..1, Real.sqrt ((1 - s) * (s + 1)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht1
    pcfZ_continuous_eta.continuousOn
    (fun s hs => by
      have := pcfZ_hasDerivAt_eta (lt_of_le_of_lt ht hs.1) hs.2
      rwa [show 1 - s^2 = (1 - s) * (s + 1) by ring] at this)
    (by apply Continuous.intervalIntegrable; fun_prop)
  rw [intervalIntegral.integral_neg] at h
  have h1 : pcfEta 1 = 0 := by simp [pcfEta]
  linarith

/-- On `[-1, ∞)` the turning-point coordinate of DLMF 12.10.39 is the Airy coordinate of
`t² - 1 = (t - 1)(t + 1)`. -/
lemma pcfZ_eq_airyCoord {t : ℝ} (ht : -1 ≤ t) :
    pcfZeta t = dblZero_airyCoord (fun s => s + 1) 1 t := by
  rcases lt_trichotomy t 1 with h | h | h
  · rw [dblZero_airyCoord_of_gt _ h, pcfZeta, pcfZ_eta_eq_integral ht h.le]
    simp only [not_le.2 h, ↓reduceIte]
  · subst h; simp [pcfZeta, pcfXi, dblZero_airyCoord]
  · rw [dblZero_airyCoord_of_lt _ h, pcfZeta, pcfZ_xi_eq_integral h.le]
    simp only [h.le, ↓reduceIte]

/-- `ζ` is continuous on `[-1, ∞)`. -/
lemma pcfZ_continuousOn_zeta : ContinuousOn pcfZeta (Ici (-1)) :=
  (dblZero_continuous_airyCoord (continuous_id.add continuous_const) 1).continuousOn.congr
    fun _ ht => pcfZ_eq_airyCoord ht

/-- `η` decreases strictly on `[-1, 1]`. -/
lemma pcfZ_eta_strictAntiOn : StrictAntiOn pcfEta (Icc (-1) 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) pcfZ_continuous_eta.continuousOn ?_
  intro t ht
  rw [interior_Icc] at ht
  rw [(pcfZ_hasDerivAt_eta ht.1 ht.2).deriv, neg_lt_zero]
  exact Real.sqrt_pos.2 (by nlinarith [ht.1, ht.2])

/-- `ξ` increases strictly on `[1, ∞)`. -/
lemma pcfZ_xi_strictMonoOn : StrictMonoOn pcfXi (Ici 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) pcfZ_continuousOn_xi ?_
  intro t ht
  rw [interior_Ici] at ht
  have ht : (1:ℝ) < t := ht
  rw [(pcfZ_hasDerivAt_xi ht).deriv]
  exact Real.sqrt_pos.2 (by nlinarith)

/-- `ξ(1) = 0`. -/
lemma pcfZ_xi_one : pcfXi 1 = 0 := by simp [pcfXi]
/-- `η(1) = 0`. -/
lemma pcfZ_eta_one : pcfEta 1 = 0 := by simp [pcfEta]

/-- `ζ` increases strictly on `[-1, ∞)`. -/
lemma pcfZ_zeta_strictMonoOn : StrictMonoOn pcfZeta (Ici (-1)) := by
  intro a ha b hb hab
  have ha : (-1:ℝ) ≤ a := ha
  have hb : (-1:ℝ) ≤ b := hb
  have e23 : (0:ℝ) < 2/3 := by norm_num
  by_cases hb1 : 1 ≤ b
  · have hxb : 0 ≤ pcfXi b := by
      rcases hb1.lt_or_eq with h | h
      · exact (pcfZ_xi_one ▸ pcfZ_xi_strictMonoOn (le_refl (1:ℝ)) hb1 h).le
      · rw [← h, pcfZ_xi_one]
    by_cases ha1 : 1 ≤ a
    · simp only [pcfZeta, ha1, hb1, ↓reduceIte]
      have hxa : 0 ≤ pcfXi a := by
        rcases ha1.lt_or_eq with h | h
        · exact (pcfZ_xi_one ▸ pcfZ_xi_strictMonoOn (le_refl (1:ℝ)) ha1 h).le
        · rw [← h, pcfZ_xi_one]
      exact Real.rpow_lt_rpow (by positivity)
        (by linarith [pcfZ_xi_strictMonoOn ha1 hb1 hab]) e23
    · simp only [pcfZeta, ha1, hb1, ↓reduceIte]
      have hea : 0 < pcfEta a := pcfZ_eta_one ▸
        pcfZ_eta_strictAntiOn ⟨ha, (not_le.1 ha1).le⟩ ⟨by norm_num, le_refl _⟩ (not_le.1 ha1)
      have := Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 3/2 * pcfEta a) (2/3)
      have := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 3/2 * pcfXi b) (2/3)
      linarith
  · have ha1 : ¬ 1 ≤ a := fun h => hb1 (h.trans hab.le)
    simp only [pcfZeta, ha1, hb1, ↓reduceIte, neg_lt_neg_iff]
    have hb1' : b < 1 := not_le.1 hb1
    have heb : 0 < pcfEta b := pcfZ_eta_one ▸
      pcfZ_eta_strictAntiOn ⟨hb, hb1'.le⟩ ⟨by norm_num, le_refl _⟩ hb1'
    exact Real.rpow_lt_rpow (by positivity)
      (by linarith [pcfZ_eta_strictAntiOn ⟨ha, (hab.trans hb1').le⟩ ⟨hb, hb1'.le⟩ hab]) e23

/-- `ζ(-1) = -(3π/4)^{2/3}`. -/
lemma pcfZ_zeta_neg_one : pcfZeta (-1) = -(3*π/4)^(2/3:ℝ) := by
  simp only [pcfZeta, show ¬ (1:ℝ) ≤ -1 by norm_num, ↓reduceIte, pcfEta, Real.arccos_neg_one]
  congr 2
  norm_num; ring

/-- A crude lower bound `ξ(t) ≥ (t-1)²/2`. -/
lemma pcfZ_xi_ge {t : ℝ} (ht : 1 ≤ t) : (t - 1)^2/2 ≤ pcfXi t := by
  rw [pcfZ_xi_eq_integral ht]
  have h : ∫ s in (1:ℝ)..t, (s - 1) = (t - 1)^2/2 := by
    simp [intervalIntegral.integral_sub]; ring
  rw [← h]
  refine intervalIntegral.integral_mono_on ht (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop) fun s hs => ?_
  exact Real.le_sqrt_of_sq_le (by nlinarith [hs.1])

/-- An exponent identity used for `ζ'`. -/
lemma pcfZ_rpow_aux {A : ℝ} (hA : 0 < A) : (A ^ (2/3 - 1 : ℝ)) ^ 2 * A ^ (2/3 : ℝ) = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le, ← Real.rpow_add hA]; norm_num

/-- Away from the turning point, `ζ' = d > 0` with `d² ζ = t² - 1`. -/
lemma pcfZ_hasDerivAt_zeta {t : ℝ} (ht : -1 < t) (ht1 : t ≠ 1) :
    ∃ d : ℝ, 0 < d ∧ d^2 * pcfZeta t = t^2 - 1 ∧ HasDerivAt pcfZeta d t := by
  rcases lt_or_gt_of_ne ht1 with h | h
  · have hη : 0 < pcfEta t := pcfZ_eta_one ▸
      pcfZ_eta_strictAntiOn ⟨ht.le, h.le⟩ ⟨by norm_num, le_refl _⟩ h
    have hA : 0 < 3/2 * pcfEta t := by positivity
    have hr : 0 < Real.sqrt (1 - t^2) := Real.sqrt_pos.2 (by nlinarith)
    have hd := (((pcfZ_hasDerivAt_eta ht h).const_mul (3/2)).rpow_const
      (p := 2/3) (Or.inl hA.ne')).neg
    refine ⟨-((3/2 * -Real.sqrt (1 - t^2)) * (2/3) * (3/2 * pcfEta t) ^ (2/3 - 1 : ℝ)), ?_, ?_, ?_⟩
    · have := Real.rpow_pos_of_pos hA (2/3 - 1); nlinarith
    · have e := pcfZ_rpow_aux hA
      have hs := Real.sq_sqrt (show 0 ≤ 1 - t^2 by nlinarith)
      simp only [pcfZeta, show ¬ 1 ≤ t from not_le.2 h, ↓reduceIte]
      linear_combination (-(1 - t^2)) * e +
        (-(((3/2 * pcfEta t) ^ (2/3 - 1 : ℝ)) ^ 2 * (3/2 * pcfEta t) ^ (2/3 : ℝ))) * hs
    · refine hd.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with s hs
      simp only [pcfZeta, show ¬ 1 ≤ s from not_le.2 hs, ↓reduceIte, Pi.neg_apply]
  · have hξ : 0 < pcfXi t := pcfZ_xi_one ▸ pcfZ_xi_strictMonoOn (le_refl (1:ℝ)) h.le h
    have hA : 0 < 3/2 * pcfXi t := by positivity
    have hr : 0 < Real.sqrt (t^2 - 1) := Real.sqrt_pos.2 (by nlinarith)
    have hd := ((pcfZ_hasDerivAt_xi h).const_mul (3/2)).rpow_const (p := 2/3) (Or.inl hA.ne')
    refine ⟨(3/2 * Real.sqrt (t^2 - 1)) * (2/3) * (3/2 * pcfXi t) ^ (2/3 - 1 : ℝ), ?_, ?_, ?_⟩
    · have := Real.rpow_pos_of_pos hA (2/3 - 1); positivity
    · have e := pcfZ_rpow_aux hA
      have hs := Real.sq_sqrt (show 0 ≤ t^2 - 1 by nlinarith)
      simp only [pcfZeta, h.le, ↓reduceIte]
      linear_combination (t^2 - 1) * e +
        (((3/2 * pcfXi t) ^ (2/3 - 1 : ℝ)) ^ 2 * (3/2 * pcfXi t) ^ (2/3 : ℝ)) * hs
    · refine hd.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with s hs
      simp only [pcfZeta, (le_of_lt hs : (1:ℝ) ≤ s), ↓reduceIte]

/-- pcfInverseZeta spec. -/
@[dlmf 12.10.E39]
theorem pcfInverseZeta_spec {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    -1 < pcfInverseZeta ζ ∧ pcfZeta (pcfInverseZeta ζ)=ζ ∧ ∀ t : ℝ, -1 < t → pcfZeta t=ζ → t=pcfInverseZeta ζ := by
  have hex : ∃ t : ℝ, -1 < t ∧ pcfZeta t = ζ := by
    obtain ⟨T, hT1, hT⟩ : ∃ T : ℝ, 1 ≤ T ∧ ζ ≤ pcfZeta T := by
      rcases le_or_gt ζ 0 with h | h
      · exact ⟨1, le_refl _, by simp [pcfZeta, pcfZ_xi_one]; exact h⟩
      · set c := ζ ^ (3/2:ℝ)
        have hc : 0 ≤ c := by positivity
        refine ⟨2 + 2*c, by linarith, ?_⟩
        have h2 := pcfZ_xi_ge (show (1:ℝ) ≤ 2 + 2*c by linarith)
        simp only [pcfZeta, show (1:ℝ) ≤ 2 + 2*c by linarith, ↓reduceIte]
        have h3 : c ≤ 3/2 * pcfXi (2 + 2*c) := by nlinarith
        calc ζ = c ^ (2/3:ℝ) := by
              rw [← Real.rpow_mul h.le]; norm_num
          _ ≤ _ := Real.rpow_le_rpow hc h3 (by norm_num)
    have hIVT := intermediate_value_Icc (show (-1:ℝ) ≤ T by linarith)
      (pcfZ_continuousOn_zeta.mono Icc_subset_Ici_self)
    obtain ⟨t, ht, hft⟩ := hIVT ⟨by rw [pcfZ_zeta_neg_one]; exact hζ.le, hT⟩
    refine ⟨t, lt_of_le_of_ne ht.1 ?_, hft⟩
    rintro rfl
    rw [pcfZ_zeta_neg_one] at hft
    linarith
  have hs := Classical.epsilon_spec hex
  refine ⟨hs.1, hs.2, fun t ht htz => ?_⟩
  exact pcfZ_zeta_strictMonoOn.injOn (le_of_lt ht) (le_of_lt hs.1) (htz.trans hs.2.symm)

/-- `pcfInverseZeta` is a left inverse of `pcfZeta` on `(-1, ∞)`. -/
lemma pcfZ_inverse_zeta {t : ℝ} (ht : -1 < t) : pcfInverseZeta (pcfZeta t) = t := by
  have hc : -(3*π/4)^(2/3:ℝ) < pcfZeta t := by
    rw [← pcfZ_zeta_neg_one]; exact pcfZ_zeta_strictMonoOn (le_refl (-1:ℝ)) ht.le ht
  exact ((pcfInverseZeta_spec hc).2.2 t ht rfl).symm

/-- `pcfInverseZeta` is strictly increasing. -/
lemma pcfZ_inverse_strictMonoOn : StrictMonoOn pcfInverseZeta (Ioi (-(3*π/4)^(2/3:ℝ))) := by
  intro a ha b hb hab
  have sa := pcfInverseZeta_spec ha
  have sb := pcfInverseZeta_spec hb
  by_contra h
  have := pcfZ_zeta_strictMonoOn.monotoneOn sb.1.le sa.1.le (not_lt.1 h)
  rw [sa.2.1, sb.2.1] at this
  linarith

/-- Derivative of the inverse coordinate away from `ζ = 0`. -/
lemma pcfZ_hasDerivAt_inverse {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) (hz : ζ ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ d^2 * ζ = pcfInverseZeta ζ ^ 2 - 1 ∧
      HasDerivAt pcfInverseZeta d⁻¹ ζ := by
  have hs := pcfInverseZeta_spec hζ
  have h1 : pcfInverseZeta ζ ≠ 1 := by
    intro h; rw [h] at hs; apply hz; rw [← hs.2.1]; simp [pcfZeta, pcfZ_xi_one]
  obtain ⟨d, hd, hdz, hder⟩ := pcfZ_hasDerivAt_zeta hs.1 h1
  rw [hs.2.1] at hdz
  refine ⟨d, hd, hdz, ?_⟩
  have hcont : ContinuousAt pcfInverseZeta ζ := by
    refine continuousAt_of_monotoneOn_of_image_mem_nhds pcfZ_inverse_strictMonoOn.monotoneOn
      (Ioi_mem_nhds hζ) (mem_of_superset (Ioi_mem_nhds hs.1) fun t ht => ?_)
    refine ⟨pcfZeta t, ?_, pcfZ_inverse_zeta ht⟩
    show -(3*π/4)^(2/3:ℝ) < pcfZeta t
    have ht' : (-1:ℝ) < t := ht
    rw [← pcfZ_zeta_neg_one]; exact pcfZ_zeta_strictMonoOn (le_refl (-1:ℝ)) ht'.le ht'
  refine hder.of_local_left_inverse hcont hd.ne' ?_
  filter_upwards [Ioi_mem_nhds hζ] with y hy
  exact (pcfInverseZeta_spec hy).2.1

/-- pcfPhi. -/
@[dlmf 12.10.E40]
def pcfPhi (ζ : ℝ) : ℝ :=
  if ζ=0 then 2^(-1/6:ℝ) else (ζ/((pcfInverseZeta ζ)^2-1))^(1/4:ℝ)

/-- The turning-point coordinate is analytic at the turning point. -/
theorem pcfZeta_analytic_at_one  :
    AnalyticAt ℝ pcfZeta 1 := by
  have h := dblZero_analyticAt_airyCoord (p := fun s : ℝ => s + 1) (x₀ := 1)
    (analyticAt_id.add analyticAt_const) (by norm_num)
  refine h.congr ?_
  filter_upwards [Ioi_mem_nhds (show (-1:ℝ) < 1 by norm_num)] with t ht
  exact (pcfZ_eq_airyCoord (le_of_lt ht)).symm

/-- Degree-4 Taylor polynomial of `√(2+y)/√2`. -/
noncomputable def pcfTay_T (y : ℝ) : ℝ := 1 + y/4 - y^2/32 + y^3/128 - 5*y^4/2048

/-- Truncated expansion `√(2+y) = √2 T(y) + O(y⁵)`, via `T² - (2+y) = O(y⁵)`. -/
lemma pcfTay_sqrt : (fun y : ℝ => Real.sqrt (2+y) - Real.sqrt 2 * pcfTay_T y) =O[𝓝 0]
    (fun y => y^5) := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  refine invSer_isBigO_sub_of_pow_sub (n := 2) two_ne_zero h2.ne' ?_ ?_ ?_
  · have := ((continuous_const.add continuous_id).sqrt (f := fun y : ℝ => 2 + y)).tendsto 0
    simpa using this
  · have : Continuous fun y => Real.sqrt 2 * pcfTay_T y := by unfold pcfTay_T; fun_prop
    simpa [pcfTay_T] using this.tendsto 0
  · refine invSer_isBigO_pow_of_eq_mul 5
      (q := fun y : ℝ => -25*y^3/2097152 + 5*y^2/65536 - 7*y/16384 + 7/2048) ?_ ?_
    · exact ((by fun_prop : Continuous fun y : ℝ =>
        -25*y^3/2097152 + 5*y^2/65536 - 7*y/16384 + 7/2048).tendsto 0).isBigO_one ℝ
    · filter_upwards [Ioi_mem_nhds (show (-2:ℝ) < 0 by norm_num)] with y hy
      have hy : (-2:ℝ) < y := hy
      rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by norm_num), pcfTay_T]
      ring

/-- `∫₀¹ τ^{1/2} τ^k dτ = 1/(k+3/2)`. -/
lemma pcfTay_integral_pow (k : ℕ) :
    ∫ τ in (0:ℝ)..1, τ^(1/2:ℝ) * τ^k = 1/(k+3/2) := by
  have h : ∫ τ in (0:ℝ)..1, τ^(1/2:ℝ) * τ^k = ∫ τ in (0:ℝ)..1, τ^((1/2:ℝ) + k) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    have hτ0 : 0 ≤ τ := by
      rw [uIcc_of_le zero_le_one] at hτ; exact hτ.1
    rw [Real.rpow_add' hτ0 (by positivity), Real.rpow_natCast]
  rw [h, integral_rpow (Or.inl (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]))]
  rw [Real.one_rpow, Real.zero_rpow (by positivity)]
  field_simp
  ring

/-- The Airy average of `p(s) = s+1` at `1+u`. -/
noncomputable def pcfTay_K (u : ℝ) : ℝ := dblZero_airyAvg (fun s => s + 1) 1 (1 + u)

/-- Degree-4 Taylor polynomial of `K/√2`. -/
noncomputable def pcfTay_Kp (u : ℝ) : ℝ := 2/3 + u/10 - u^2/112 + u^3/576 - 5*u^4/11264

/-- `K(1+u) = ∫₀¹ τ^{1/2} √(2+uτ) dτ`. -/
lemma pcfTay_K_eq (u : ℝ) :
    pcfTay_K u = ∫ τ in (0:ℝ)..1, τ^(1/2:ℝ) * Real.sqrt (2 + u*τ) := by
  unfold pcfTay_K dblZero_airyAvg
  refine intervalIntegral.integral_congr fun τ _ => ?_
  simp only
  congr 2; ring

/-- Termwise integration of the truncated square root. -/
lemma pcfTay_Kp_eq (u : ℝ) :
    ∫ τ in (0:ℝ)..1, τ^(1/2:ℝ) * (Real.sqrt 2 * pcfTay_T (u*τ)) = Real.sqrt 2 * pcfTay_Kp u := by
  have e : ∀ τ : ℝ, τ^(1/2:ℝ) * (Real.sqrt 2 * pcfTay_T (u*τ)) =
      ∑ k ∈ Finset.range 5, (Real.sqrt 2 * ([1, 1/4, -1/32, 1/128, -5/2048] : List ℝ).getD k 0
        * u^k) * (τ^(1/2:ℝ) * τ^k) := by
    intro τ
    simp [Finset.sum_range_succ, pcfTay_T]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, pcfTay_integral_pow]
    simp [Finset.sum_range_succ, pcfTay_Kp]
    ring
  · intro k _
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.mul ((Real.continuous_rpow_const (by norm_num)).mul (continuous_pow k))


/-- `K(1+u) = √2 Kp(u) + O(u⁵)`. -/
lemma pcfTay_K_expansion :
    (fun u => pcfTay_K u - Real.sqrt 2 * pcfTay_Kp u) =O[𝓝 0] (fun u => u^5) := by
  obtain ⟨C, hC0, hC⟩ := pcfTay_sqrt.exists_pos
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 hC.bound
  refine IsBigO.of_bound C ?_
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδ] with u hu
  have hu : |u| < δ := by simpa using hu
  have hint : IntervalIntegrable (fun τ : ℝ => τ^(1/2:ℝ) * Real.sqrt (2 + u*τ)) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hint2 : IntervalIntegrable (fun τ : ℝ => τ^(1/2:ℝ) * (Real.sqrt 2 * pcfTay_T (u*τ)))
      volume 0 1 :=
    Continuous.intervalIntegrable (by unfold pcfTay_T; fun_prop) _ _
  rw [pcfTay_K_eq, ← pcfTay_Kp_eq, ← intervalIntegral.integral_sub hint hint2]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := C * ‖u^5‖)
    (f := fun τ : ℝ => τ^(1/2:ℝ) * Real.sqrt (2 + u*τ) - τ^(1/2:ℝ) * (Real.sqrt 2 * pcfTay_T (u*τ)))
    (fun τ hτ => by
      rw [uIoc_of_le zero_le_one] at hτ
      have h1 : |u*τ| < δ := by
        rw [abs_mul, abs_of_pos hτ.1]
        exact lt_of_le_of_lt (mul_le_of_le_one_right (abs_nonneg u) hτ.2) hu
      have h2 := hb (y := u*τ) (by simpa using h1)
      rw [← mul_sub, norm_mul]
      have h3 : ‖τ^(1/2:ℝ)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hτ.1.le _)]
        exact Real.rpow_le_one hτ.1.le hτ.2 (by norm_num)
      have h4 : ‖(u*τ)^5‖ ≤ ‖u^5‖ := by
        rw [mul_pow, norm_mul]
        have : ‖τ^5‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ.1.le 5)]
          exact pow_le_one₀ hτ.1.le hτ.2
        nlinarith [norm_nonneg (u^5)]
      calc ‖τ^(1/2:ℝ)‖ * ‖Real.sqrt (2 + u*τ) - Real.sqrt 2 * pcfTay_T (u*τ)‖
          ≤ 1 * (C * ‖u^5‖) := by
            refine mul_le_mul h3 (h2.trans (mul_le_mul_of_nonneg_left h4 hC0.le))
              (norm_nonneg _) zero_le_one
        _ = C * ‖u^5‖ := one_mul _)
  simpa using this

/-- `(2^{1/3})³ = 2`. -/
lemma pcfTay_c_cube : ((2:ℝ)^(1/3:ℝ))^3 = 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- Degree-4 Taylor polynomial of `((3/2)K)^{2/3}/2^{1/3}`. -/
noncomputable def pcfTay_R (u : ℝ) : ℝ :=
  1 + u/10 - 2*u^2/175 + 37*u^3/15750 - 1849*u^4/3031875

/-- `K(1+u) → (2/3)√2` as `u → 0`. -/
lemma pcfTay_K_tendsto : Tendsto pcfTay_K (𝓝 0) (𝓝 ((2/3) * Real.sqrt 2)) := by
  have hp : AnalyticAt ℝ (fun s : ℝ => s + 1) 1 := analyticAt_id.add analyticAt_const
  have h := (dblZero_analyticAt_airyAvg hp (by norm_num)).continuousAt
  have h2 : Tendsto (fun u : ℝ => 1 + u) (𝓝 0) (𝓝 1) := by
    simpa using (by fun_prop : Continuous fun u : ℝ => 1 + u).tendsto 0
  have := h.tendsto.comp h2
  rw [dblZero_airyAvg_self] at this
  norm_num at this
  exact this

/-- `((3/2)K)^{2/3} = 2^{1/3} R(u) + O(u⁵)`, via the cube relation. -/
lemma pcfTay_Z_expansion :
    (fun u => ((3/2) * pcfTay_K u)^(2/3:ℝ) - (2:ℝ)^(1/3:ℝ) * pcfTay_R u) =O[𝓝 0]
      (fun u => u^5) := by
  have hc : (0:ℝ) < (2:ℝ)^(1/3:ℝ) := by positivity
  have hK0 : ∀ u, 0 ≤ pcfTay_K u := fun u => dblZero_airyAvg_nonneg _ _ _
  refine invSer_isBigO_sub_of_pow_sub (n := 3) three_ne_zero hc.ne' ?_ ?_ ?_
  · have h1 := (pcfTay_K_tendsto.const_mul (3/2)).rpow_const (p := 2/3)
      (Or.inl (by positivity))
    convert h1 using 2
    rw [Real.sqrt_eq_rpow, show (3/2:ℝ) * ((2/3) * (2:ℝ)^(1/2:ℝ)) = (2:ℝ)^(1/2:ℝ) by ring,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  · have : Continuous fun u => (2:ℝ)^(1/3:ℝ) * pcfTay_R u := by unfold pcfTay_R; fun_prop
    simpa [pcfTay_R] using this.tendsto 0
  · have e1 : ∀ u, (((3/2) * pcfTay_K u)^(2/3:ℝ))^3 = (9/4) * pcfTay_K u ^ 2 := by
      intro u
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by have := hK0 u; positivity),
        show (2/3:ℝ) * ((3:ℕ):ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
    have hA := (pcfTay_K_expansion.mul ((pcfTay_K_tendsto.add
      ((by unfold pcfTay_Kp; fun_prop : Continuous fun u => Real.sqrt 2 * pcfTay_Kp u).tendsto 0)).isBigO_one ℝ)).const_mul_left (9/4)
    have hB := invSer_isBigO_pow_of_eq_mul (l := 𝓝 (0:ℝ)) (y := id) 5
      (f := fun u => (9/2) * pcfTay_Kp u ^ 2 - 2 * pcfTay_R u ^ 3)
      (q := fun u : ℝ => 12642726098*u^7/27869801526123046875 - 126495637*u^6/24129698291015625 + 441062309*u^5/9651879316406250 - 29489287*u^4/66184315312500 + 316335933107*u^3/257034387456000000 - 188911973*u^2/57953280000000 + 111563237*u/26078976000000 + 3059827/10348800000)
      (((by fun_prop : Continuous fun u : ℝ => 12642726098*u^7/27869801526123046875 - 126495637*u^6/24129698291015625 + 441062309*u^5/9651879316406250 - 29489287*u^4/66184315312500 + 316335933107*u^3/257034387456000000 - 188911973*u^2/57953280000000 + 111563237*u/26078976000000 + 3059827/10348800000).tendsto 0).isBigO_one ℝ)
      (Eventually.of_forall fun u => by simp only [pcfTay_Kp, pcfTay_R, id]; ring)
    have hA' : _ =O[𝓝 (0:ℝ)] (fun u : ℝ => u^5) := hA.trans (by simpa using isBigO_refl (fun u : ℝ => u^5) _)
    refine ((hA'.add hB).congr' (Eventually.of_forall fun u => ?_)
      (Eventually.of_forall fun u => by simp)).trans (isBigO_refl _ _)
    simp only [e1, mul_pow, pcfTay_c_cube]
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    linear_combination (-(9/4) * pcfTay_Kp u ^ 2) * h2


/-- `ζ(1+u) = u ((3/2)K(1+u))^{2/3}` (DLMF 12.10.39 as an Airy coordinate). -/
lemma pcfTay_zeta_eq {u : ℝ} (hu : -2 ≤ u) :
    pcfZeta (1 + u) = u * ((3/2) * pcfTay_K u)^(2/3:ℝ) := by
  rw [pcfZ_eq_airyCoord (by linarith), dblZero_airyCoord, pcfTay_K]
  ring_nf

/-- Forward expansion `ζ(1+u) = 2^{1/3} u R(u) + O(u⁶)`. -/
lemma pcfTay_zeta_expansion :
    (fun u => pcfZeta (1 + u) - (2:ℝ)^(1/3:ℝ) * (u * pcfTay_R u)) =O[𝓝 0] (fun u => u^6) := by
  have h := (isBigO_refl (fun u : ℝ => u) (𝓝 0)).mul pcfTay_Z_expansion
  refine h.congr' ?_ (Eventually.of_forall fun u => by ring)
  filter_upwards [Ioi_mem_nhds (show (-2:ℝ) < 0 by norm_num)] with u hu
  rw [pcfTay_zeta_eq (le_of_lt hu)]; ring

/-- The printed inverse polynomial in `w = 2^{-1/3} ζ` minus `1`. -/
noncomputable def pcfTay_v (w : ℝ) : ℝ :=
  w-w^2/10+11*w^3/350-823*w^4/63000+150653*w^5/24255000

/-- The residual of the inversion, `(v R(v) - w)/w⁶`. -/
noncomputable def pcfTay_q (w : ℝ) : ℝ :=
  w*(w*(w*(w*(w*(w*(w*(w*(w*(w*(w*(w*(w*(w*(w*(w*(w*(w*(783876931167548774559650287/13221689470271539282265625000000000000000 - 143491386769361756420091123557*w/25451752230272713118361328125000000000000000) - 47119937620258209964619261/120197177002468538929687500000000000000) + 82288713654128684005237699/37776255629347255092187500000000000000) - 30517117985044689320850841/2158643178819843148125000000000000000) + 3043919389270844484453637/39248057796724420875000000000000000) - 392955749776850760448801/1090223827686789468750000000000000) + 3200410982445578048767/2076616814641503750000000000000) - 1444810931500592024107/207661681464150375000000000000) + 18399562789495057631/647257188979170000000000000) - 16908374496178801/160530056790468750000000) + 3148285199483107/8561603028825000000000) - 42209311381812853/32106011358093750000000) + 7972127151497/1853160828750000000) - 6165851047/463290207187500) + 146438784931/3529830150000000) - 14538540377/117661005000000) + 41220257/122245200000) - 90737/97453125) + 20917/6930000

/-- The printed inverse polynomial inverts `w ↦ w R(w)` to order `w⁵`. -/
lemma pcfTay_inversion_identity (w : ℝ) :
    pcfTay_v w * pcfTay_R (pcfTay_v w) - w = w^6 * pcfTay_q w := by
  unfold pcfTay_v pcfTay_R pcfTay_q; ring

/-- pcfInverseZeta taylor. -/
@[dlmf 12.10.E41]
theorem pcfInverseZeta_taylor  :
    (fun ζ : ℝ => let w:=2^(-1/3:ℝ)*ζ; pcfInverseZeta ζ-(1+w-w^2/10+11*w^3/350-823*w^4/63000+150653*w^5/24255000)) =O[𝓝 0] (fun ζ : ℝ => ζ^6) := by
  set k : ℝ := (2:ℝ)^(-1/3:ℝ) with hk
  set c : ℝ := (2:ℝ)^(1/3:ℝ) with hc
  have hck : c * k = 1 := by
    rw [hc, hk, ← Real.rpow_add (by norm_num)]; norm_num
  set v : ℝ → ℝ := fun ζ => pcfTay_v (k * ζ) with hv
  have hvc : Continuous v := by simp only [hv, pcfTay_v]; fun_prop
  have hv0 : Tendsto v (𝓝 0) (𝓝 0) := by
    simpa [hv, pcfTay_v] using hvc.tendsto 0
  have hvO : v =O[𝓝 0] (fun ζ => ζ^1) := by
    refine invSer_isBigO_pow_of_eq_mul (y := id) 1
      (q := fun ζ => k * (1 - (k*ζ)/10 + 11*(k*ζ)^2/350 - 823*(k*ζ)^3/63000
        + 150653*(k*ζ)^4/24255000)) ?_ (Eventually.of_forall fun ζ => ?_)
    · exact ((by fun_prop : Continuous fun ζ : ℝ => k * (1 - (k*ζ)/10 + 11*(k*ζ)^2/350
        - 823*(k*ζ)^3/63000 + 150653*(k*ζ)^4/24255000)).tendsto 0).isBigO_one ℝ
    · simp only [hv, pcfTay_v, id]; ring
  -- `ζ(1 + v) - ζ = O(ζ⁶)`
  have hE : (fun ζ => pcfZeta (1 + v ζ) - ζ) =O[𝓝 0] (fun ζ => ζ^6) := by
    have h1 : (fun ζ => pcfZeta (1 + v ζ) - c * (v ζ * pcfTay_R (v ζ))) =O[𝓝 0]
        (fun ζ => ζ^6) := by
      refine (pcfTay_zeta_expansion.comp_tendsto hv0).trans ?_
      simpa [Function.comp_def] using hvO.pow 6
    have h2 : (fun ζ => c * (v ζ * pcfTay_R (v ζ)) - ζ) =O[𝓝 0] (fun ζ => ζ^6) := by
      refine invSer_isBigO_pow_of_eq_mul (y := id) 6 (q := fun ζ => c * k^6 * pcfTay_q (k*ζ))
        (((by unfold pcfTay_q; fun_prop : Continuous fun ζ : ℝ => c * k^6 * pcfTay_q (k*ζ)).tendsto
          0).isBigO_one ℝ) (Eventually.of_forall fun ζ => ?_)
      have := pcfTay_inversion_identity (k * ζ)
      simp only [hv, id]
      linear_combination c * this + ζ * hck
    exact (h1.add h2).congr (fun ζ => by ring) (fun _ => rfl)
  -- the analytic inverse
  have hp : AnalyticAt ℝ (fun s : ℝ => s + 1) 1 := analyticAt_id.add analyticAt_const
  obtain ⟨g, hga, -, hg1, hgl, hgr⟩ :=
    dblZero_exists_analytic_inverse_airyCoord hp (by norm_num : (0:ℝ) < 1 + 1)
  have hf0 : dblZero_airyCoord (fun s : ℝ => s + 1) 1 1 = 0 := by simp [dblZero_airyCoord]
  have hfc : ContinuousAt (dblZero_airyCoord (fun s : ℝ => s + 1) 1) 1 :=
    (dblZero_continuous_airyCoord (continuous_id.add continuous_const) 1).continuousAt
  have hP : Tendsto (fun ζ => 1 + v ζ) (𝓝 0) (𝓝 1) := by
    simpa using hv0.const_add 1
  have hmain := invSer_isBigO_sub_of_leftInverse (hf0 ▸ hga.hasStrictDerivAt) hgl hfc hP
    (h := id) (by rw [hf0]; exact tendsto_id)
  -- `g = pcfInverseZeta` near `0`
  have hgP : ∀ᶠ ζ in 𝓝 (0:ℝ), g ζ = pcfInverseZeta ζ := by
    have hgc : Tendsto g (𝓝 0) (𝓝 1) := hg1 ▸ hga.continuousAt.tendsto
    have hneg : -(3*π/4)^(2/3:ℝ) < (0:ℝ) := by
      have : 0 < (3*π/4)^(2/3:ℝ) := by positivity
      linarith
    filter_upwards [hgr, hgc.eventually (Ioi_mem_nhds (show (-1:ℝ) < 1 by norm_num)),
      Ioi_mem_nhds hneg] with ζ h1 h2 h3
    have h2' : (-1:ℝ) < g ζ := h2
    refine (pcfInverseZeta_spec h3).2.2 (g ζ) h2' ?_
    rw [pcfZ_eq_airyCoord h2'.le, h1]
  have hfP : ∀ᶠ ζ in 𝓝 (0:ℝ), dblZero_airyCoord (fun s : ℝ => s + 1) 1 (1 + v ζ) =
      pcfZeta (1 + v ζ) := by
    filter_upwards [hP.eventually (Ioi_mem_nhds (show (-1:ℝ) < 1 by norm_num))] with ζ h
    exact (pcfZ_eq_airyCoord (le_of_lt h)).symm
  have h3 := (hmain.congr' (hgP.mono fun ζ h =>
      show 1 + v ζ - g (id ζ) = 1 + v ζ - pcfInverseZeta ζ by simp only [id, h])
    (hfP.mono fun ζ h => show dblZero_airyCoord (fun s : ℝ => s + 1) 1 (1 + v ζ) - id ζ =
      pcfZeta (1 + v ζ) - ζ by simp only [id, h])).trans hE
  refine h3.neg_left.congr (fun ζ => ?_) (fun _ => rfl)
  simp only [hv, pcfTay_v, hk]
  ring


/-- pcfAiryAlpha. -/
@[dlmf 12.10.E43]
def pcfAiryAlpha (m : ℕ) : ℝ :=
  (∏ j ∈ Finset.range (2*m), (2*m+1+2*j:ℝ))/((m.factorial:ℝ)*144^m)

/-- pcfAiryBeta. -/
@[dlmf 12.10.E43]
def pcfAiryBeta (m : ℕ) : ℝ :=
  -(6*m+1:ℝ)/(6*m-1:ℝ)*pcfAiryAlpha m

/-- Continuous coefficient at zero is supplied by a removable limit. -/
@[dlmf 12.10.E42]
def pcfAiryA (s : ℕ) (ζ : ℝ) : ℝ :=
  limUnder (𝓝[≠] ζ) (fun u : ℝ => (∑ m ∈ Finset.range (2*s+1), pcfAiryBeta m*(pcfPhi u)^(6*(2*s-m))*(pcfOlverU (2*s-m)).eval (pcfInverseZeta u))/u^(3*s+0))

/-- pcfAiryA limit. -/
@[dlmf 12.10.E42]
theorem pcfAiryA_limit (s : ℕ) {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    Tendsto (fun u : ℝ => (∑ m ∈ Finset.range (2*s+1), pcfAiryBeta m*(pcfPhi u)^(6*(2*s-m))*(pcfOlverU (2*s-m)).eval (pcfInverseZeta u))/u^(3*s+0)) (𝓝[≠] ζ) (𝓝 (pcfAiryA s ζ)) := by
  sorry

/-- Continuous coefficient at zero is supplied by a removable limit. -/
@[dlmf 12.10.E42]
def pcfAiryB (s : ℕ) (ζ : ℝ) : ℝ :=
  limUnder (𝓝[≠] ζ) (fun u : ℝ => -(∑ m ∈ Finset.range (2*s+1+1), pcfAiryAlpha m*(pcfPhi u)^(6*(2*s+1-m))*(pcfOlverU (2*s+1-m)).eval (pcfInverseZeta u))/u^(3*s+2))

/-- pcfAiryB limit. -/
@[dlmf 12.10.E42]
theorem pcfAiryB_limit (s : ℕ) {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    Tendsto (fun u : ℝ => -(∑ m ∈ Finset.range (2*s+1+1), pcfAiryAlpha m*(pcfPhi u)^(6*(2*s+1-m))*(pcfOlverU (2*s+1-m)).eval (pcfInverseZeta u))/u^(3*s+2)) (𝓝[≠] ζ) (𝓝 (pcfAiryB s ζ)) := by
  sorry

/-- Continuous coefficient at zero is supplied by a removable limit. -/
@[dlmf 12.10.E46]
def pcfAiryC (s : ℕ) (ζ : ℝ) : ℝ :=
  limUnder (𝓝[≠] ζ) (fun u : ℝ => -(∑ m ∈ Finset.range (2*s+1+1), pcfAiryBeta m*(pcfPhi u)^(6*(2*s+1-m))*(pcfOlverV (2*s+1-m)).eval (pcfInverseZeta u))/u^(3*s+1))

/-- pcfAiryC limit. -/
@[dlmf 12.10.E46]
theorem pcfAiryC_limit (s : ℕ) {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    Tendsto (fun u : ℝ => -(∑ m ∈ Finset.range (2*s+1+1), pcfAiryBeta m*(pcfPhi u)^(6*(2*s+1-m))*(pcfOlverV (2*s+1-m)).eval (pcfInverseZeta u))/u^(3*s+1)) (𝓝[≠] ζ) (𝓝 (pcfAiryC s ζ)) := by
  sorry

/-- Continuous coefficient at zero is supplied by a removable limit. -/
@[dlmf 12.10.E46]
def pcfAiryD (s : ℕ) (ζ : ℝ) : ℝ :=
  limUnder (𝓝[≠] ζ) (fun u : ℝ => (∑ m ∈ Finset.range (2*s+1), pcfAiryAlpha m*(pcfPhi u)^(6*(2*s-m))*(pcfOlverV (2*s-m)).eval (pcfInverseZeta u))/u^(3*s+0))

/-- pcfAiryD limit. -/
@[dlmf 12.10.E46]
theorem pcfAiryD_limit (s : ℕ) {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    Tendsto (fun u : ℝ => (∑ m ∈ Finset.range (2*s+1), pcfAiryAlpha m*(pcfPhi u)^(6*(2*s-m))*(pcfOlverV (2*s-m)).eval (pcfInverseZeta u))/u^(3*s+0)) (𝓝[≠] ζ) (𝓝 (pcfAiryD s ζ)) := by
  sorry

/-- pcfAiryChi. -/
@[dlmf 12.10.E45]
def pcfAiryChi (ζ : ℝ) : ℝ :=
  deriv pcfPhi ζ/pcfPhi ζ

/-- pcfAiryChi formula. -/
@[dlmf 12.10.E45]
theorem pcfAiryChi_formula {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) (hz : ζ ≠ 0) :
    pcfAiryChi ζ=(1-2*pcfInverseZeta ζ*(pcfPhi ζ)^6)/(4*ζ) := by
  obtain ⟨d, hd, hdz, hT⟩ := pcfZ_hasDerivAt_inverse hζ hz
  set t := pcfInverseZeta ζ with ht
  set B : ℝ → ℝ := fun u => u / (pcfInverseZeta u ^ 2 - 1) with hB
  have ht1 : t ^ 2 - 1 ≠ 0 := by
    rw [← hdz]; exact mul_ne_zero (pow_ne_zero 2 hd.ne') hz
  have hBζ : B ζ = (d^2)⁻¹ := by
    simp only [hB, ← ht, ← hdz]; field_simp
  have hB0 : 0 < B ζ := by rw [hBζ]; positivity
  have hBd : HasDerivAt B ((1 * (t^2 - 1) - ζ * (2 * t * d⁻¹)) / (t^2 - 1)^2) ζ := by
    have h2 : HasDerivAt (fun u => pcfInverseZeta u ^ 2 - 1) (2 * t * d⁻¹) ζ := by
      simpa [ht] using (hT.pow 2).sub_const 1
    exact (hasDerivAt_id ζ).div h2 ht1
  have hφ : pcfPhi =ᶠ[𝓝 ζ] fun u => B u ^ (1/4:ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with u hu
    simp [pcfPhi, hu, hB]
  have hφd := hBd.rpow_const (p := 1/4) (Or.inl hB0.ne')
  have hφζ : pcfPhi ζ = B ζ ^ (1/4:ℝ) := hφ.self_of_nhds
  rw [pcfAiryChi, hφ.deriv_eq, hφd.deriv, hφζ]
  have h6 : (B ζ ^ (1/4:ℝ)) ^ 6 = B ζ * d⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le, show (1/4:ℝ) * (6:ℕ) = 1 + 1/2 by norm_num,
      Real.rpow_add hB0, Real.rpow_one, ← Real.sqrt_eq_rpow, hBζ, Real.sqrt_inv,
      Real.sqrt_sq hd.le]
  have h4 : B ζ ^ (1/4 - 1 : ℝ) = B ζ ^ (1/4:ℝ) * (B ζ)⁻¹ := by
    rw [Real.rpow_sub hB0, Real.rpow_one, div_eq_mul_inv]
  rw [h6, h4, hBζ]
  have hq : 0 < ((d^2)⁻¹) ^ (1/4:ℝ) := by positivity
  rw [← hdz]
  field_simp

/-- pcfAiryCD derivative. -/
@[dlmf 12.10.E44]
theorem pcfAiryCD_derivative (s : ℕ) {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    pcfAiryC s ζ=pcfAiryChi ζ*pcfAiryA s ζ+deriv (pcfAiryA s) ζ+ζ*pcfAiryB s ζ ∧ pcfAiryD (s+1) ζ=pcfAiryA (s+1) ζ+pcfAiryChi ζ*pcfAiryB s ζ+deriv (pcfAiryB s) ζ := by
  sorry

end DLMF.Confluent
