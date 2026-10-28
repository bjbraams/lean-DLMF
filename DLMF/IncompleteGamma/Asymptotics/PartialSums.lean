/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.Asymptotics.LargeArgument

/-!
# Transition estimates and exponential partial sums

Incomplete-Gamma transition estimates and asymptotic expansions of remainders of exponential
partial sums.

Source references and common attribution are retained in
`DLMF.IncompleteGamma.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

open DLMF.Statistical

/-- The identity 8.11.14 with `S_n` unfolded. -/
theorem igAsy_exp_identity (n : ℕ) (x : ℝ) :
    exp (n*x : ℂ)=expPartialSum n (n*x)+(n*x : ℂ)^n/n.factorial*
      (lowerIncGamma (n+1) (n*x)/((n*x : ℂ)^n*exp (-n*x : ℂ))) := by
  rw [show (-n*x : ℂ) = -(n*x : ℂ) by ring]
  set z : ℂ := (n*x : ℂ)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  by_cases hz : z = 0
  · have h0 : lowerIncGamma (n+1) z = 0 := by
      rw [lowerIncGamma_eq_regularized (natCast_add_one_ne_neg_nat n), hz,
        zero_cpow (by exact_mod_cast n.succ_ne_zero), mul_zero, zero_mul]
    rw [h0, zero_div, mul_zero, add_zero, hz, Complex.exp_zero, expPartialSum,
      Finset.sum_eq_single 0]
    · simp
    · intro k _ hk; simp [hk]
    · simp
  · rw [lowerIncGamma_nat_succ_expPartialSum n hz, Complex.exp_neg]
    have he : exp z ≠ 0 := Complex.exp_ne_zero z
    have hzn : z^n ≠ 0 := pow_ne_zero _ hz
    field_simp
    ring

/-- `q(u) = -(log(1-u)+u)/u²`, extended by `1/2` at `0`. -/
noncomputable def igAsy_q (u : ℝ) : ℝ := if u = 0 then 1/2 else -(Real.log (1-u) + u)/u^2

/-- `|q(u) - 1/2| ≤ 2u` on `[0, 1/8]`. -/
theorem igAsy_q_sub_half {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1/8) : |igAsy_q u - 1/2| ≤ 2*u := by
  unfold igAsy_q
  split_ifs with h
  · simp [h]
  have hu' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm h)
  have habs : |u| < 1 := by rw [abs_of_pos hu']; linarith
  have hl := Real.abs_log_sub_add_sum_range_le habs 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_pos hu'] at hl
  norm_num at hl
  have h1 : u^3/(1-u) ≤ 2*u^3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos hu' 3]
  have heq : -(Real.log (1-u) + u)/u^2 - 1/2 = -((u + u^2/2 + Real.log (1-u))/u^2) := by
    field_simp; ring
  rw [heq, abs_neg, abs_div, abs_of_pos (by positivity : (0:ℝ) < u^2), div_le_iff₀ (by positivity)]
  nlinarith

/-- The even integrand `(1-|t|)^k e^{k|t|}`. -/
noncomputable def igAsy_E (k : ℕ) (t : ℝ) : ℝ := (1-|t|)^k * Real.exp (k*|t|)

/-- The Gaussian form `e^{-k t² q(|t|)} = (1-|t|)^k e^{k|t|}`. -/
theorem igAsy_exp_q_eq (k : ℕ) {t : ℝ} (ht : |t| < 1) :
    exp (-((k:ℝ):ℂ) * (t:ℂ)^2 * ((igAsy_q |t| : ℝ) : ℂ)) = (igAsy_E k t : ℂ) := by
  unfold igAsy_E igAsy_q
  split_ifs with h
  · have : t = 0 := abs_eq_zero.mp h
    subst this; simp
  · have hpos : 0 < 1 - |t| := by linarith
    have hr : t^2 * (-(Real.log (1-|t|) + |t|)/|t|^2) = -(Real.log (1-|t|) + |t|) := by
      have : |t|^2 ≠ 0 := by positivity
      rw [← sq_abs t]; field_simp
    have ht2 : -((k:ℝ):ℂ) * (t:ℂ)^2 * ((-(Real.log (1-|t|) + |t|)/|t|^2 : ℝ) : ℂ) =
        ((k * Real.log (1-|t|) + k*|t| : ℝ) : ℂ) := by
      rw [mul_assoc, show (t:ℂ)^2 = ((t^2:ℝ):ℂ) by push_cast; ring, ← ofReal_mul, hr]
      push_cast; ring
    rw [ht2, ← ofReal_exp]
    congr 1
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hpos]

/-- Laplace's method at the endpoint maximum: `√k ∫_{-1/8}^{1/8} E_k → √(2π)`. -/
theorem igAsy_tendsto_sqrt_mul_integral_E :
    Tendsto (fun k : ℕ => Real.sqrt k * ∫ t in Icc (-(1/8:ℝ)) (1/8), igAsy_E k t) atTop
      (𝓝 (Real.sqrt (2*π))) := by
  have hqm : Measurable igAsy_q := by
    unfold igAsy_q
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  have H := (Complex.tendstoUniformlyOn_sqrt_mul_integral_laplace_Icc (S := (univ : Set Unit))
    (A := fun _ _ => (1:ℂ)) (q := fun _ t => ((igAsy_q |t| : ℝ) : ℂ)) (c := 1/4) (L := 0) (M := 1)
    (B := 2) (δ := 1/8) (by norm_num) (by norm_num) (fun _ _ => measurable_const)
    (fun _ _ => (Complex.measurable_ofReal.comp (hqm.comp continuous_abs.measurable)))
    (fun _ _ t ht => ?_) (fun _ _ => by simp) (fun _ _ t _ => by simp)
    (fun _ _ t ht => ?_)).tendsto_at (mem_univ ())
  rotate_left
  · have h := igAsy_q_sub_half (abs_nonneg t) (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
    simp only [ofReal_re]
    have := (abs_le.mp h).1
    have : |t| ≤ 1/8 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    linarith
  · have h := igAsy_q_sub_half (abs_nonneg t) (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
    rw [abs_zero, show igAsy_q 0 = 1/2 by simp [igAsy_q], ← ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact h
  have hq0 : igAsy_q |0| = 1/2 := by simp [igAsy_q]
  simp only [hq0, one_mul] at H
  have hC : ((Real.pi : ℂ) / ((1/2 : ℝ) : ℂ)) ^ (1/2 : ℂ) = (Real.sqrt (2*π) : ℂ) := by
    rw [show ((Real.pi : ℂ) / ((1/2 : ℝ) : ℂ)) = ((2*π : ℝ) : ℂ) by push_cast; ring,
      show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      Real.sqrt_eq_rpow]
  rw [hC] at H
  have H2 := H.comp tendsto_natCast_atTop_atTop
  have hE : ∀ k : ℕ, ((Real.sqrt k * ∫ t in Icc (-(1/8:ℝ)) (1/8), igAsy_E k t : ℝ) : ℂ) =
      (Real.sqrt k : ℂ) * ∫ t in Icc (-(1/8:ℝ)) (1/8),
        exp (-((k:ℝ):ℂ) * (t:ℂ)^2 * ((igAsy_q |t| : ℝ) : ℂ)) := by
    intro k
    rw [ofReal_mul, ← integral_complex_ofReal]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    rw [igAsy_exp_q_eq k (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2])]
  have H3 : Tendsto (fun k : ℕ => ((Real.sqrt k * ∫ t in Icc (-(1/8:ℝ)) (1/8), igAsy_E k t : ℝ) : ℂ))
      atTop (𝓝 (Real.sqrt (2*π) : ℂ)) := by
    simp only [hE]; exact H2
  have H4 := (Complex.continuous_re.tendsto _).comp H3
  simp only [Function.comp_def, ofReal_re] at H4
  exact H4

/-- Folding the even integrand: `∫_{-1/8}^{1/8} E_{m+1} = 2 ∫_{7/8}^1 s^{m+1} e^{(m+1)(1-s)} ds`. -/
theorem igAsy_integral_E_eq (m : ℕ) :
    ∫ t in Icc (-(1/8:ℝ)) (1/8), igAsy_E (m+1) t = 2 * ∫ s in (7/8:ℝ)..1, igAsy_F m 1 s := by
  have hc : Continuous (igAsy_E (m+1)) := by unfold igAsy_E; fun_prop
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have h1 : ∫ t in (-(1/8:ℝ))..0, igAsy_E (m+1) t = ∫ t in (0:ℝ)..(1/8), igAsy_E (m+1) t := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1/8) (igAsy_E (m+1))
    rw [neg_zero] at this
    rw [← this]
    congr 1; funext t; simp [igAsy_E]
  have h2 : ∫ t in (0:ℝ)..(1/8), igAsy_E (m+1) t = ∫ s in (7/8:ℝ)..1, igAsy_F m 1 s := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1/8) (igAsy_F m 1) 1
    rw [show (1:ℝ) - 1/8 = 7/8 by norm_num, sub_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [igAsy_E, igAsy_F, abs_of_nonneg ht.1]
    push_cast
    ring_nf
  rw [h1, h2]; ring

/-- `s^n e^{n(1-s)} ≤ e^{-n(1-s)²/2}` on `[0,1]`. -/
theorem igAsy_F_one_le (m : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    igAsy_F m 1 s ≤ Real.exp (-((m+1)*(1-s)^2/2)) := by
  rcases hs0.eq_or_lt with h | h
  · subst h; simp [igAsy_F]; positivity
  have hu : |1-s| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hS := Real.hasSum_pow_div_log_of_abs_lt_one hu
  have hle := sum_le_hasSum (Finset.range 2) (fun i _ => by
    have : 0 ≤ 1-s := by linarith
    positivity) hS
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_sub_cancel] at hle
  norm_num at hle
  unfold igAsy_F
  rw [← Real.exp_log (pow_pos h (m+1)), ← Real.exp_add, Real.exp_le_exp, Real.log_pow]
  push_cast
  nlinarith [show (0:ℝ) ≤ (m:ℝ)+1 by positivity]

/-- The tail `√n ∫₀^{7/8} s^n e^{n(1-s)} ds → 0`. -/
theorem igAsy_tendsto_tail :
    Tendsto (fun m : ℕ => Real.sqrt ((m:ℝ)+1) * ∫ s in (0:ℝ)..(7/8), igAsy_F m 1 s) atTop (𝓝 0) := by
  have hb : ∀ m : ℕ, ∫ s in (0:ℝ)..(7/8), igAsy_F m 1 s ≤ 7/8 * Real.exp (-(((m:ℝ)+1)/128)) := by
    intro m
    have := intervalIntegral.integral_mono_on (g := fun _ => Real.exp (-(((m:ℝ)+1)/128)))
      (by norm_num : (0:ℝ) ≤ 7/8)
      ((by unfold igAsy_F; fun_prop : Continuous (igAsy_F m 1)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable (μ := volume) _ _) (fun s hs => by
        refine (igAsy_F_one_le m hs.1 (by linarith [hs.2])).trans ?_
        rw [Real.exp_le_exp]
        have : 1/64 ≤ (1-s)^2 := by nlinarith [hs.2]
        nlinarith [show (0:ℝ) ≤ (m:ℝ)+1 by positivity])
    simpa using this
  have hnn : ∀ m : ℕ, 0 ≤ ∫ s in (0:ℝ)..(7/8), igAsy_F m 1 s := fun m =>
    intervalIntegral.integral_nonneg (by norm_num) fun s hs => igAsy_F_nonneg m 1 hs.1
  have hlim : Tendsto (fun m : ℕ => 7/8 * 128 * ((((m:ℝ)+1)/128)^1 * Real.exp (-(((m:ℝ)+1)/128))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ((m:ℝ)+1)/128) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_div_const (by norm_num)
    have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h1).const_mul (7/8*128)
    simpa using this
  refine squeeze_zero (fun m => mul_nonneg (Real.sqrt_nonneg _) (hnn m)) (fun m => ?_) hlim
  have hm : (1:ℝ) ≤ (m:ℝ)+1 := by simp
  have hs : Real.sqrt ((m:ℝ)+1) ≤ (m:ℝ)+1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  calc Real.sqrt ((m:ℝ)+1) * ∫ s in (0:ℝ)..(7/8), igAsy_F m 1 s
      ≤ ((m:ℝ)+1) * (7/8 * Real.exp (-(((m:ℝ)+1)/128))) :=
        mul_le_mul hs (hb m) (hnn m) (by positivity)
    _ = 7/8 * 128 * ((((m:ℝ)+1)/128)^1 * Real.exp (-(((m:ℝ)+1)/128))) := by ring

/-- `√n ∫₀¹ s^n e^{n(1-s)} ds → √(π/2)`, written as `√(2π)/2`. -/
theorem igAsy_tendsto_sqrt_J :
    Tendsto (fun m : ℕ => Real.sqrt ((m:ℝ)+1) * ∫ s in (0:ℝ)..1, igAsy_F m 1 s) atTop
      (𝓝 (Real.sqrt (2*π)/2)) := by
  have hE := (igAsy_tendsto_sqrt_mul_integral_E.comp (tendsto_add_atTop_nat 1)).div_const 2
  have hc : Continuous (igAsy_F 0 1) := by unfold igAsy_F; fun_prop
  have H := igAsy_tendsto_tail.add hE
  rw [zero_add] at H
  refine H.congr fun m => ?_
  have hcF : Continuous (igAsy_F m 1) := by unfold igAsy_F; fun_prop
  have hsplit : ∫ s in (0:ℝ)..1, igAsy_F m 1 s =
      (∫ s in (0:ℝ)..(7/8), igAsy_F m 1 s) + ∫ s in (7/8:ℝ)..1, igAsy_F m 1 s :=
    (intervalIntegral.integral_add_adjacent_intervals (hcF.intervalIntegrable _ _)
      (hcF.intervalIntegrable _ _)).symm
  simp only [Function.comp_apply, igAsy_integral_E_eq]
  rw [hsplit]
  push_cast
  ring

/-- `e_n(nx)/e^{nx} = 1 - (nx)^n/n! · S_n(x)/e^{nx}` with the integral form of `S_n`. -/
theorem igAsy_ratio_eq (m : ℕ) (x : ℝ) :
    expPartialSum (m+1) (((m+1:ℕ):ℂ)*x)/exp (((m+1:ℕ):ℂ)*x) =
      ((1 - ((m+1)*x)^(m+1)/((m+1).factorial) * ((m+1)*x*∫ s in (0:ℝ)..1, igAsy_F m x s) /
        Real.exp ((m+1)*x) : ℝ) : ℂ) := by
  have hI := igAsy_exp_identity (m+1) x
  rw [igAsy_lowerIncGamma_ratio_eq] at hI
  have he : exp (((m+1:ℕ):ℂ)*x) ≠ 0 := Complex.exp_ne_zero _
  rw [div_eq_iff he]
  push_cast at hI ⊢
  have he' : exp (((m:ℂ)+1)*x) ≠ 0 := Complex.exp_ne_zero _
  rw [sub_mul, one_mul, div_mul_cancel₀ _ he']
  linear_combination -hI

/-- `x e^{1-x} < 1` for `x ≠ 1`. -/
theorem igAsy_mul_exp_lt_one {x : ℝ} (hx1 : x ≠ 1) : x * Real.exp (1-x) < 1 := by
  have h := Real.add_one_lt_exp (sub_ne_zero.mpr hx1)
  have he : Real.exp (x-1) * Real.exp (1-x) = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (1-x)
  nlinarith

/-- `(nx)^n/(n! e^{nx}) ≤ (x e^{1-x})^n` for `x ≥ 0`. -/
theorem igAsy_pow_div_factorial_le (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) :
    ((n:ℝ)*x)^n/n.factorial/Real.exp (n*x) ≤ (x*Real.exp (1-x))^n := by
  have h := Real.pow_div_factorial_le_exp (n:ℝ) (n.cast_nonneg) n
  rw [div_le_iff₀ (Real.exp_pos _), mul_pow, mul_pow, ← Real.exp_nat_mul]
  have he : Real.exp (n*(1-x)) * Real.exp (n*x) = Real.exp n := by rw [← Real.exp_add]; ring_nf
  calc (n:ℝ)^n * x^n / n.factorial = x^n * ((n:ℝ)^n/n.factorial) := by ring
    _ ≤ x^n * Real.exp n := by gcongr
    _ = x^n * Real.exp (n*(1-x)) * Real.exp (n*x) := by rw [mul_assoc, he]

/-- 8.11.13 for `0 ≤ x < 1`. -/
theorem igAsy_poisson_lt {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun m : ℕ => ((m+1)*x)^(m+1)/((m+1).factorial) * ((m+1)*x*∫ s in (0:ℝ)..1, igAsy_F m x s) /
        Real.exp ((m+1)*x)) atTop (𝓝 0) := by
  set r := x*Real.exp (1-x)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := igAsy_mul_exp_lt_one hx1.ne
  have hlim : Tendsto (fun m : ℕ => r^(m+1) * (x/(1-x))) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)).mul_const
      (x/(1-x))
    simpa [Function.comp_def] using this
  refine squeeze_zero (fun m => ?_) (fun m => ?_) hlim
  · have := intervalIntegral.integral_nonneg (μ := volume) (zero_le_one' ℝ) fun s hs => igAsy_F_nonneg m x hs.1
    positivity
  · have hJ := igAsy_integral_F_le m hx1
    have hJ0 := intervalIntegral.integral_nonneg (μ := volume) (zero_le_one' ℝ) fun s hs => igAsy_F_nonneg m x hs.1
    have hP := igAsy_pow_div_factorial_le (m+1) hx0
    push_cast at hP
    have h1 : (m+1)*x*∫ s in (0:ℝ)..1, igAsy_F m x s ≤ x/(1-x) := by
      have hm : (0:ℝ) < m+1 := by positivity
      have hx' : 0 < 1-x := by linarith
      calc (m+1)*x*∫ s in (0:ℝ)..1, igAsy_F m x s ≤ (m+1)*x*(1/((m+1)*(1-x))) := by gcongr
        _ = x/(1-x) := by field_simp
    rw [mul_div_right_comm]
    exact mul_le_mul hP h1 (by positivity) (by positivity)

/-- 8.11.13 at `x = 1`. -/
theorem igAsy_poisson_one :
    Tendsto (fun m : ℕ => ((m+1)*1)^(m+1)/((m+1).factorial) * ((m+1)*1*∫ s in (0:ℝ)..1, igAsy_F m 1 s) /
        Real.exp ((m+1)*1)) atTop (𝓝 (1/2)) := by
  have hst := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)).inv₀
    (by positivity : Real.sqrt π ≠ 0)
  have H := (hst.mul igAsy_tendsto_sqrt_J).div_const (Real.sqrt 2)
  have hval : (Real.sqrt π)⁻¹ * (Real.sqrt (2*π)/2) / Real.sqrt 2 = 1/2 := by
    rw [Real.sqrt_mul (by norm_num)]
    have : Real.sqrt π ≠ 0 := by positivity
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  rw [hval] at H
  refine H.congr fun m => ?_
  simp only [Function.comp_apply, Stirling.stirlingSeq]
  push_cast
  have hm : (0:ℝ) < m+1 := by positivity
  have hs : Real.sqrt ((m:ℝ)+1) * Real.sqrt ((m:ℝ)+1) = (m:ℝ)+1 := Real.mul_self_sqrt hm.le
  rw [Real.sqrt_mul (by norm_num), div_pow, ← Real.exp_nat_mul]
  have hf : ((m+1).factorial : ℝ) ≠ 0 := by positivity
  have : Real.sqrt 2 ≠ 0 := by positivity
  have : Real.sqrt ((m:ℝ)+1) ≠ 0 := by positivity
  push_cast
  field_simp
  rw [Real.sq_sqrt hm.le]

/-- Exponential-series terms increase up to index `n` when `n ≤ y`. -/
theorem igAsy_term_le {k : ℕ} {y : ℝ} : ∀ n, k ≤ n → (n:ℝ) ≤ y →
    y^k/k.factorial ≤ y^n/n.factorial := by
  intro n hkn
  induction n, hkn using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ n hkn ih =>
    intro hy
    have hy' : (n:ℝ) ≤ y := by push_cast at hy; linarith
    refine (ih hy').trans ?_
    have hn : (0:ℝ) < n+1 := by positivity
    have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg n) hy'
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast at hy
    have : 0 ≤ y^n * (n.factorial : ℝ) := by positivity
    nlinarith

/-- 8.11.13 for `x > 1`. -/
theorem igAsy_poisson_gt {x : ℝ} (hx : 1 < x) :
    Tendsto (fun m : ℕ => expPartialSum (m+1) (((m+1:ℕ):ℂ)*x)/exp (((m+1:ℕ):ℂ)*x)) atTop (𝓝 0) := by
  set r := x*Real.exp (1-x)
  have hr0 : 0 ≤ r := by have : 0 ≤ x := by linarith
                         positivity
  have hr1 : r < 1 := igAsy_mul_exp_lt_one hx.ne'
  have heq : ∀ m : ℕ, expPartialSum (m+1) (((m+1:ℕ):ℂ)*x)/exp (((m+1:ℕ):ℂ)*x) =
      (((∑ k ∈ Finset.range (m+1+1), ((m+1:ℕ)*x)^k/k.factorial)/Real.exp ((m+1:ℕ)*x) : ℝ) : ℂ) := by
    intro m; simp only [expPartialSum]; push_cast; rfl
  simp only [heq]
  rw [show (0:ℂ) = ((0:ℝ):ℂ) by simp]
  refine (continuous_ofReal.tendsto _).comp ?_
  have hlim : Tendsto (fun m : ℕ => ((m+1:ℕ):ℝ)*r^(m+1) + r^(m+1)) atTop (𝓝 0) := by
    have h1 := (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)
    have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using h1.add h2
  refine squeeze_zero (fun m => by positivity) (fun m => ?_) hlim
  set n := m+1
  have hy : (n:ℝ) ≤ n*x := by nlinarith [show (0:ℝ) ≤ n by positivity]
  have hsum : ∑ k ∈ Finset.range (n+1), ((n:ℝ)*x)^k/k.factorial ≤ (n+1) * (((n:ℝ)*x)^n/n.factorial) := by
    have := Finset.sum_le_card_nsmul (Finset.range (n+1)) (fun k => ((n:ℝ)*x)^k/k.factorial)
      (((n:ℝ)*x)^n/n.factorial) (fun k hk => igAsy_term_le n
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hy)
    simpa using this
  have hP := igAsy_pow_div_factorial_le n (by linarith : 0 ≤ x)
  calc (∑ k ∈ Finset.range (n+1), ((n:ℝ)*x)^k/k.factorial)/Real.exp (n*x)
      ≤ (n+1) * (((n:ℝ)*x)^n/n.factorial) / Real.exp (n*x) := by gcongr
    _ = (n+1) * (((n:ℝ)*x)^n/n.factorial/Real.exp (n*x)) := by ring
    _ ≤ (n+1) * r^n := by gcongr
    _ = (n:ℝ)*r^n + r^n := by ring

/-- The map `(fun n : ℕ => expPartialSum n (n*x)/exp (n*x : ℂ))` tends to `(𝓝 (if 1 < x then 0
else if x=1 then 1/2 else 1))` along `atTop`. -/
@[dlmf 8.11.E13]
theorem expPartialSum_poisson_limit {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => expPartialSum n (n*x)/exp (n*x : ℂ)) atTop (𝓝 (if 1 < x then 0 else if x=1 then 1/2 else 1)) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  split_ifs with h1 h2
  · exact igAsy_poisson_gt h1
  · subst h2
    simp only [igAsy_ratio_eq]
    have := (continuous_ofReal.tendsto _).comp (tendsto_const_nhds (x := (1:ℝ)) |>.sub igAsy_poisson_one)
    rw [show (1/2:ℂ) = ((1 - 1/2 : ℝ) : ℂ) by push_cast; norm_num]
    exact this
  · have hx1 : x < 1 := by
      rcases lt_trichotomy x 1 with h | h | h
      · exact h
      · exact absurd h h2
      · exact absurd h h1
    simp only [igAsy_ratio_eq]
    have := (continuous_ofReal.tendsto _).comp (tendsto_const_nhds (x := (1:ℝ)) |>.sub (igAsy_poisson_lt hx hx1))
    rw [show (1:ℂ) = ((1 - 0 : ℝ) : ℂ) by push_cast; norm_num]
    exact this

/-- The exponential partial-sum remainder S_n. -/
@[dlmf 8.11.E15]
def expPartialSumRemainderS (n : ℕ) (x : ℝ) : ℂ :=
  lowerIncGamma (n+1) (n*x)/((n*x : ℂ)^n*exp (-n*x : ℂ))

/-- Identity under the stated parameter and domain assumptions: `exp (n*x : ℂ)=expPartialSum n
(n*x)+(n*x : ℂ)^n/n.factorial*expPartialSumRemainderS n x`. -/
@[dlmf 8.11.E14]
theorem expPartialSumRemainderS_identity (n : ℕ) (x : ℝ) :
    exp (n*x : ℂ)=expPartialSum n (n*x)+(n*x : ℂ)^n/n.factorial*expPartialSumRemainderS n x := by
  rw [expPartialSumRemainderS]
  exact igAsy_exp_identity n x

/-- `S_n(x) = n x ∫₀¹ s^n e^{n x (1-s)} ds`. -/
theorem igAsy_S_eq (m : ℕ) (x : ℝ) :
    expPartialSumRemainderS (m+1) x = (((m+1)*x * ∫ s in (0:ℝ)..1, igAsy_F m x s : ℝ) : ℂ) := by
  unfold expPartialSumRemainderS
  exact igAsy_lowerIncGamma_ratio_eq m x

/-- The real coefficients `d_k(x) = (-1)^k x h_k(x)/(1-x)` of 8.11.18. -/
noncomputable def igAsy_d (k : ℕ) (x : ℝ) : ℝ := (-1)^k * (x * igAsy_h k x/(1-x))

/-- The exact remainder of 8.11.18. -/
theorem igAsy_S_remainder (m N : ℕ) {x : ℝ} (hx : x < 1) :
    expPartialSumRemainderS (m+1) x - ∑ k ∈ Finset.range N, (igAsy_d k x : ℂ)/((m:ℂ)+1)^k =
      (((m+1)*x*((-1)^N/((m:ℝ)+1)^N * ∫ s in (0:ℝ)..1, igAsy_F m x s * igAsy_h N (x*s)) : ℝ) : ℂ) := by
  rw [igAsy_S_eq, igAsy_iter m hx N]
  have hm : (m:ℝ)+1 ≠ 0 := by positivity
  have hcast : ∀ k : ℕ, ((m:ℂ)+1)^k = (((m:ℝ)+1)^k : ℝ) := fun k => by push_cast; ring
  simp only [igAsy_d, hcast, ← ofReal_div, ← ofReal_sum, ← ofReal_sub]
  congr 1
  rw [mul_add, Finset.mul_sum, add_sub_right_comm]
  rw [show ∑ i ∈ Finset.range N, ((m:ℝ)+1)*x*((-1)^i/((m:ℝ)+1)^(i+1)*(igAsy_h i x/(1-x))) -
      ∑ k ∈ Finset.range N, (-1)^k*(x*igAsy_h k x/(1-x))/((m:ℝ)+1)^k = 0 by
    rw [sub_eq_zero]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ]; field_simp]
  ring

/-- The remainder bound behind 8.11.18. -/
theorem igAsy_S_remainder_bound (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, ∀ m : ℕ, ∀ x : ℝ, x ≤ 1-δ →
      ‖expPartialSumRemainderS (m+1) x - ∑ k ∈ Finset.range N, (igAsy_d k x : ℂ)/((m:ℂ)+1)^k‖
        ≤ C * (1/((m:ℝ)+1)^N) := by
  obtain ⟨K, hK0, hK⟩ := igAsy_h_bound N hδ
  refine ⟨K * max 1 (1/δ), fun m x hxδ => ?_⟩
  have hx : x < 1 := by linarith
  have hx1 : 0 < 1 - x := by linarith
  have hm : (0:ℝ) < (m:ℝ)+1 := by positivity
  rw [igAsy_S_remainder m N hx, Complex.norm_real, Real.norm_eq_abs]
  set I := ∫ s in (0:ℝ)..1, igAsy_F m x s * igAsy_h N (x*s)
  have hFc : Continuous (igAsy_F m x) := by unfold igAsy_F; fun_prop
  have hI : |I| ≤ K * (1/((m+1)*(1-x))) := by
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (igAsy_integral_F_le m hx) hK0)
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one ?_
      ((hFc.const_smul K).intervalIntegrable _ _) ?_
    · exact ((hFc.continuousOn.mul (igAsy_continuousOn_h N hx)).abs).intervalIntegrable
    · intro s hs
      have hy : x*s ≤ max 0 (1-δ) := by
        rcases le_or_gt x 0 with h | h
        · exact (mul_nonpos_of_nonpos_of_nonneg h hs.1).trans (le_max_left _ _)
        · exact (le_trans (by nlinarith [hs.2]) hxδ).trans (le_max_right _ _)
      rw [abs_mul, abs_of_nonneg (igAsy_F_nonneg m x hs.1), mul_comm K]
      exact mul_le_mul_of_nonneg_left (hK _ hy) (igAsy_F_nonneg m x hs.1)
  have hxr : |x|/(1-x) ≤ max 1 (1/δ) := by
    rw [div_le_iff₀ hx1]
    rcases le_or_gt x 0 with h | h
    · rw [abs_of_nonpos h]; nlinarith [le_max_left 1 (1/δ)]
    · rw [abs_of_pos h]
      have h1 : 1/δ ≤ max 1 (1/δ) := le_max_right _ _
      have h2 : δ ≤ 1-x := by linarith
      have h3 : 1 ≤ (1/δ)*(1-x) := by rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]; linarith
      nlinarith
  have hpos : 0 < ((m:ℝ)+1)^N := by positivity
  rw [abs_mul, abs_mul, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hm, abs_of_pos hpos]
  calc ((m:ℝ)+1)*|x| * (1/((m:ℝ)+1)^N*|I|) ≤ ((m:ℝ)+1)*|x| * (1/((m:ℝ)+1)^N*(K*(1/((m+1)*(1-x))))) := by
        gcongr
    _ = K*(|x|/(1-x))*(1/((m:ℝ)+1)^N) := by field_simp
    _ ≤ K*max 1 (1/δ)*(1/((m:ℝ)+1)^N) := by gcongr

/-- The phase `φ(u) = u - log(1+u)`, with `(1+u)^n e^{-nu} = e^{-n φ(u)}`. -/
noncomputable def igAsy_phi (u : ℝ) : ℝ := u - Real.log (1+u)

/-- The quotient `φ(u)/u²`, extended analytically to `u = 0`. -/
noncomputable def igAsy_Q : ℝ → ℝ := dslope (dslope igAsy_phi 0) 0

/-- `φ` is analytic at `0`. -/
theorem igAsy_analyticAt_phi : AnalyticAt ℝ igAsy_phi 0 := by
  unfold igAsy_phi
  exact analyticAt_id.sub ((analyticAt_const.add analyticAt_id).log (by norm_num))

/-- `Q` is analytic at `0`. -/
theorem igAsy_analyticAt_Q : AnalyticAt ℝ igAsy_Q 0 :=
  (igAsy_analyticAt_phi.dslope 0).dslope 0

/-- `φ(u) = u² Q(u)`. -/
theorem igAsy_phi_eq (u : ℝ) : igAsy_phi u = u^2 * igAsy_Q u := by
  have h := dblZero_eq_sq_mul_dslope (g := igAsy_phi) (x₀ := 0) (by simp [igAsy_phi]) ?_ u
  · simpa [igAsy_Q] using h
  · have : HasDerivAt igAsy_phi (1 - 1/(1+0)) 0 :=
      (hasDerivAt_id 0).sub (((hasDerivAt_id (0:ℝ)).const_add 1).log (by norm_num))
    rw [this.deriv]; norm_num

/-- `|φ(u) - u²/2| ≤ 2|u|³` for `|u| ≤ 1/2`. -/
theorem igAsy_phi_sub_le {u : ℝ} (hu : |u| ≤ 1/2) : |igAsy_phi u - u^2/2| ≤ 2*|u|^3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  have h1 : |igAsy_phi u - u^2/2| = |(0 + (-u)^(0+1)/((0:ℕ)+1) + (-u)^(1+1)/((1:ℕ)+1))
      + Real.log (1+u)| := by
    rw [← abs_neg]; unfold igAsy_phi; congr 1; push_cast; ring
  rw [h1]
  refine h.trans ?_
  show |u|^3/(1-|u|) ≤ 2*|u|^3
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ |u|^3 := by positivity
  nlinarith [abs_nonneg u]

/-- `Q(0) = 1/2`. -/
theorem igAsy_Q_zero : igAsy_Q 0 = 1/2 := by
  have hc : Tendsto (fun u => |igAsy_Q u - 1/2|) (𝓝[≠] 0) (𝓝 |igAsy_Q 0 - 1/2|) :=
    ((igAsy_analyticAt_Q.continuousAt.sub continuousAt_const).abs).tendsto.mono_left
      nhdsWithin_le_nhds
  have h2 : Tendsto (fun u : ℝ => 2*|u|) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun u : ℝ => 2*|u|) (𝓝 0) (𝓝 (2*|0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ u in 𝓝[≠] (0:ℝ), |igAsy_Q u - 1/2| ≤ 2*|u| := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ)
      (by norm_num : (0:ℝ) < 1/2))] with u hu hb
    have hu0 : u ≠ 0 := hu
    have hb' : |u| ≤ 1/2 := by simpa [Real.dist_eq] using (Metric.mem_ball.1 hb).le
    have h := igAsy_phi_sub_le hb'
    rw [igAsy_phi_eq, show u^2 * igAsy_Q u - u^2/2 = u^2 * (igAsy_Q u - 1/2) by ring, abs_mul,
      abs_of_nonneg (sq_nonneg u), ← sq_abs, show 2*|u|^3 = |u|^2 * (2*|u|) by ring] at h
    exact le_of_mul_le_mul_left h (by positivity)
  have := le_of_tendsto_of_tendsto hc h2 hle
  have h0 : |igAsy_Q 0 - 1/2| = 0 := le_antisymm this (abs_nonneg _)
  linarith [abs_eq_zero.1 h0]

/-- The signed square root `u √(2 Q(u))` of `2φ(u)`. -/
noncomputable def igAsy_sqrtPhi (u : ℝ) : ℝ := (u - 0) * Real.sqrt (2 * igAsy_Q u)

/-- The signed square root vanishes at `0`. -/
theorem igAsy_sqrtPhi_zero : igAsy_sqrtPhi 0 = 0 := by simp [igAsy_sqrtPhi]

/-- The signed square root is analytic at `0` with derivative `1`, and `φ = V²/2` near `0`. -/
theorem igAsy_sqrtPhi_props : AnalyticAt ℝ igAsy_sqrtPhi 0 ∧ HasDerivAt igAsy_sqrtPhi 1 0 ∧
    ∀ᶠ x in 𝓝 0, igAsy_phi x = igAsy_sqrtPhi x ^ 2 / 2 := by
  obtain ⟨h1, h2, h3⟩ := dblZero_signedSqrt (g := igAsy_phi) igAsy_analyticAt_Q
    (by rw [igAsy_Q_zero]; norm_num) (Eventually.of_forall fun x => by rw [igAsy_phi_eq]; ring)
  refine ⟨h1, ?_, h3.mono fun x hx => hx.1⟩
  have : Real.sqrt (2 * igAsy_Q 0) = 1 := by rw [igAsy_Q_zero]; norm_num
  rw [this] at h2
  exact h2

/-- Taylor coefficients of the inverse of `u ↦ u √(2Q(u))` up to degree `8`. -/
noncomputable def igAsy_Pc : ℕ → ℝ
  | 1 => 1 | 2 => 1/3 | 3 => 1/36 | 4 => -1/270 | 5 => 1/4320 | 6 => 1/17010
  | 7 => -139/5443200 | 8 => 1/204120 | _ => 0

/-- The degree-`8` polynomial `P(v) = ∑_{k<9} P_k v^k` divided by `v`. -/
noncomputable def igAsy_P1 (v : ℝ) : ℝ :=
  1 + v/3 + v^2/36 - v^3/270 + v^4/4320 + v^5/17010 - 139*v^6/5443200 + v^7/204120

/-- Formula under the stated hypotheses: `∑ k ∈ Finset.range 9, igAsy_Pc k * v^k = v * igAsy_P1
v`. -/
theorem igAsy_sum_Pc (v : ℝ) : ∑ k ∈ Finset.range 9, igAsy_Pc k * v^k = v * igAsy_P1 v := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, igAsy_Pc, igAsy_P1]
  ring

/-- The residual polynomial of the inverse-series verification. -/
noncomputable def igAsy_R (v : ℝ) : ℝ := -v^62/2768104942150133660519356040269823606784000000000 + 139*v^61/8201792421185581216353647526725403279360000000000 - 64363*v^60/164035848423711624327072950534508065587200000000000 + 8414711*v^59/1458096430432992216240648449195627249664000000000000 - 39398720783*v^58/699886286607836263795511255613901079838720000000000000 + 800844031091*v^57/2666233472791757195411471449957718399385600000000000000 + 203207581524653*v^56/319948016735010863449376573994926207926272000000000000000 - 589903790773392367*v^55/19907876596845120392405653493017630715412480000000000000000 + 1812135294676417436239*v^54/6370520510990438525569809117765641828931993600000000000000000 - 61536180983488037268223*v^53/56626848986581675782842747713472371812728832000000000000000000 - 3200028968192764058201*v^52/530876709249203210464150759813803485744332800000000000000000 + 311443135429997527330939*v^51/2831342449329083789142137385673618590636441600000000000000000 - 44454799605418997643991*v^50/75839529892743315780592965687686212249190400000000000000000 - 559676526517695375461*v^49/674129154602162806938604139446099664437248000000000000000 + 198376372993988324996513*v^48/5898630102768924560712786220153372063825920000000000000000 - 128833516499331115639963*v^47/655403344752102728968087357794819118202880000000000000000 - 3667317918596362552760177*v^46/15729680274050465495234096587075658836869120000000000000000 + 324230753132416786833013*v^45/32770167237605136448404367889740955910144000000000000000 - 14952974654565356951124521*v^44/294931505138446228035639311007668603191296000000000000000 - 13252544188014095919239*v^43/130040346180972763684144317022781571072000000000000000 + 27771663040102917607741*v^42/10403227694477821094731545361822525685760000000000000 - 11954991339734226940007*v^41/1083669551508106364034535975189846425600000000000000 - 36449936144571194043961*v^40/722446367672070909356357316793230950400000000000000 + 75166882097473144608997*v^39/120407727945345151559392886132205158400000000000000 - 22315566379032504120787*v^38/16054363726046020207919051484294021120000000000000 - 120052626821536535467*v^37/7963474070459335420594767601336320000000000000 + 6103713633575949013303*v^36/47780844422756012523568605608017920000000000000 - 29626459559588237*v^35/530898271363955694706317840089088000000000 - 517463897990836994347*v^34/106179654272791138941263568017817600000000000 + 121286984931364029473*v^33/8848304522732594911771964001484800000000000 + 17223711251174594586739*v^32/309690658295640821912018740051968000000000000 - 25997842511592509407*v^31/35112319534653154411793507942400000000000 + 252464389076981274511*v^30/140449278138612617647174031769600000000000 + 58750710510092643809*v^29/2926026627887762867649458995200000000000 - 11171106973961039807*v^28/65022813953061397058876866560000000000 - 522621430896224857*v^27/602063092157975898693304320000000000 + 6291240544991059709*v^26/6095888808099505974269706240000000000 - 181301900023966397*v^25/20158362460646514465177600000000000 - 17454651767210771*v^24/368610056423250550220390400000000 + 696576869128085983*v^23/1075112664567814104809472000000000 - 200522812574221273*v^22/179185444094635684134912000000000 - 35470128327336733*v^21/597284813648785613783040000000 - 132577309851169703*v^20/398189875765857075855360000000 - 510374274227141*v^19/493787048320755302400000000 - 2858145000327557*v^18/967419523240663449600000000 + 517628494375877*v^17/131676546218868080640000000 + 2490219288582629*v^16/65838273109434040320000000 - 14261288811003299*v^15/10973045518239006720000000 - 7688700092268269*v^14/438921820729560268800000 - 469646448720269*v^13/4354383142158336000000 - 1797913715932633*v^12/4354383142158336000000 - 713769681139453*v^11/725730523693056000000 - 7696763934359*v^10/7679688081408000000 - 16218691291337*v^9/1343945414246400000 - 408540701317127*v^8/1511938591027200000 - 8497883956229*v^7/3199870033920000 - 1823729366989*v^6/114281072640000 - 17479190864627*v^5/266655836160000 - 16977567694037*v^4/88885278720000 - 58412710933*v^3/148142131200 - 15240966109*v^2/27433728000 - 158347621*v/326592000 - 235145669/1175731200

/-- The polynomial identity behind the inverse-series verification. -/
theorem igAsy_residual_identity (v : ℝ) :
    2*(v * igAsy_P1 v - (-∑ i ∈ Finset.range 9, (-(v * igAsy_P1 v))^(i+1)/((i:ℝ)+1))) - v^2 =
      v^10 * igAsy_R v := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, igAsy_P1, igAsy_R]
  norm_num
  ring

/-- `P₁` is continuous. -/
theorem igAsy_continuous_P1 : Continuous igAsy_P1 := by unfold igAsy_P1; fun_prop

/-- The residual polynomial is continuous. -/
theorem igAsy_continuous_R : Continuous igAsy_R := by unfold igAsy_R; fun_prop

/-- `2φ(P(v)) - v² = O(v^{10})`. -/
theorem igAsy_isBigO_residual :
    (fun v => 2 * igAsy_phi (v * igAsy_P1 v) - v^2) =O[𝓝 0] fun v => v^10 := by
  set Pn : ℝ → ℝ := fun v => v * igAsy_P1 v with hPn
  have hPc : Continuous Pn := continuous_id.mul igAsy_continuous_P1
  have hP0 : Tendsto Pn (𝓝 0) (𝓝 0) := by simpa [hPn] using hPc.tendsto 0
  have hP1 : Tendsto igAsy_P1 (𝓝 0) (𝓝 1) := by
    simpa [igAsy_P1] using igAsy_continuous_P1.tendsto 0
  set E : ℝ → ℝ := fun v => ∑ i ∈ Finset.range 9, (-(Pn v))^(i+1)/((i:ℝ)+1) +
    Real.log (1 + Pn v) with hE
  have hEO : E =O[𝓝 0] fun v => v^10 := by
    refine IsBigO.of_bound (2*2^10) ?_
    filter_upwards [hP0.eventually (Metric.closedBall_mem_nhds (0:ℝ) (by norm_num : (0:ℝ) < 1/2)),
      hP1.eventually (Metric.closedBall_mem_nhds (1:ℝ) one_pos)] with v hv h1
    have hv' : |Pn v| ≤ 1/2 := by simpa [Real.dist_eq] using Metric.mem_closedBall.1 hv
    have h1' : |igAsy_P1 v| ≤ 2 := by
      have := Metric.mem_closedBall.1 h1
      rw [Real.dist_eq] at this
      have := abs_sub_abs_le_abs_sub (igAsy_P1 v) 1
      norm_num at this ⊢; linarith
    have hb := Real.abs_log_sub_add_sum_range_le (x := -(Pn v)) (by rw [abs_neg]; linarith) 9
    rw [abs_neg, sub_neg_eq_add] at hb
    have h2 : |Pn v| ^ (9+1) / (1 - |Pn v|) ≤ 2 * |Pn v|^10 := by
      rw [div_le_iff₀ (by linarith), show 9+1 = 10 by rfl]
      have : 0 ≤ |Pn v|^10 := by positivity
      nlinarith
    have h3 : |Pn v| ≤ 2 * |v| := by
      simp only [hPn, abs_mul]; nlinarith [abs_nonneg v]
    have h4 : |Pn v|^10 ≤ (2*|v|)^10 := pow_le_pow_left₀ (abs_nonneg _) h3 10
    rw [Real.norm_eq_abs, norm_pow, Real.norm_eq_abs]
    calc |E v| ≤ 2 * |Pn v|^10 := hb.trans h2
      _ ≤ 2 * (2*|v|)^10 := by gcongr
      _ = 2*2^10 * |v|^10 := by ring
  have hRO : (fun v => v^10 * igAsy_R v) =O[𝓝 0] fun v => v^10 := by
    have := (isBigO_refl (fun v : ℝ => v^10) (𝓝 0)).mul
      ((igAsy_continuous_R.tendsto 0).isBigO_one ℝ)
    simpa using this
  refine (hRO.sub (hEO.const_mul_left 2)).congr' (Eventually.of_forall fun v => ?_)
    EventuallyEq.rfl
  have := igAsy_residual_identity v
  simp only [hE, hPn, igAsy_phi] at this ⊢
  rw [← this]
  ring

/-- `V(P(v)) - v = O(v⁹)` as `v → 0`, `v ≠ 0`. -/
theorem igAsy_isBigO_sqrtPhi_P :
    (fun v => igAsy_sqrtPhi (v * igAsy_P1 v) - v) =O[𝓝[≠] 0] fun v => v^9 := by
  set Pn : ℝ → ℝ := fun v => v * igAsy_P1 v with hPn
  set A : ℝ → ℝ := fun v => igAsy_P1 v * Real.sqrt (2 * igAsy_Q (Pn v)) with hA
  have hPc : Continuous Pn := continuous_id.mul igAsy_continuous_P1
  have hP0 : Tendsto Pn (𝓝 0) (𝓝 0) := by simpa [hPn] using hPc.tendsto 0
  have hQP : Tendsto (fun v => igAsy_Q (Pn v)) (𝓝 0) (𝓝 (1/2)) := by
    rw [← igAsy_Q_zero]; exact igAsy_analyticAt_Q.continuousAt.tendsto.comp hP0
  have hAt : Tendsto A (𝓝 0) (𝓝 1) := by
    have h1 : Tendsto igAsy_P1 (𝓝 0) (𝓝 1) := by
      simpa [igAsy_P1] using igAsy_continuous_P1.tendsto 0
    have := h1.mul ((hQP.const_mul 2).sqrt)
    rw [show (1:ℝ) * Real.sqrt (2*(1/2)) = 1 by norm_num] at this
    exact this
  have hsq : (fun v => A v ^ 2 - 1 ^ 2) =O[𝓝[≠] 0] fun v => v^8 := by
    have h := (igAsy_isBigO_residual.mono nhdsWithin_le_nhds).mul
      (isBigO_refl (fun v : ℝ => (v^2)⁻¹) (𝓝[≠] 0))
    refine h.congr' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, Eventually.filter_mono nhdsWithin_le_nhds
        (hQP.eventually (lt_mem_nhds (by norm_num : (0:ℝ) < 1/2)))] with v hv hq
      have hv : v ≠ 0 := hv
      simp only [hA]
      rw [mul_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2 * igAsy_Q (Pn v))]
      simp only [igAsy_phi_eq, hPn]
      field_simp
    · filter_upwards [self_mem_nhdsWithin] with v hv
      have hv : v ≠ 0 := hv
      field_simp
  have h1 := invSer_isBigO_sub_of_pow_sub two_ne_zero one_ne_zero
    (hAt.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hsq
  refine ((isBigO_refl (fun v : ℝ => v) _).mul h1).congr' (Eventually.of_forall fun v => ?_)
    (Eventually.of_forall fun v => by ring)
  simp only [hA, hPn, igAsy_sqrtPhi]
  ring

/-- The Taylor coefficients of a local inverse of `u ↦ u √(2Q(u))` up to degree `8`. -/
theorem igAsy_coeff_of_inverse {U : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    (hp : HasFPowerSeriesAt U p 0) (hl : ∀ᶠ x in 𝓝 0, U (igAsy_sqrtPhi x) = x) :
    ∀ k < 9, p.coeff k = igAsy_Pc k := by
  have hs : HasStrictDerivAt U (deriv U 0) (igAsy_sqrtPhi 0) := by
    rw [igAsy_sqrtPhi_zero]; exact hp.analyticAt.hasStrictDerivAt
  have hPt : Tendsto (fun v => v * igAsy_P1 v) (𝓝[≠] 0) (𝓝 0) := by
    have h : Continuous fun v : ℝ => v * igAsy_P1 v := continuous_id.mul igAsy_continuous_P1
    have := h.tendsto 0
    simp only [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun v : ℝ => v) (𝓝[≠] 0) (𝓝 (igAsy_sqrtPhi 0)) := by
    rw [igAsy_sqrtPhi_zero]; exact tendsto_id.mono_left nhdsWithin_le_nhds
  have ha : (fun v => v * igAsy_P1 v - U v) =O[𝓝[≠] 0] fun v => v^9 :=
    (invSer_isBigO_sub_of_leftInverse hs hl igAsy_sqrtPhi_props.1.continuousAt hPt hid).trans
      igAsy_isBigO_sqrtPhi_P
  have hc := (hp.isBigO_sub_partialSum_pow 9).mono (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [zero_add, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] at hc
  have hc' : (fun y => U y - ∑ k ∈ Finset.range 9, y^k * p.coeff k) =O[𝓝[≠] 0]
      fun y => y^9 :=
    hc.trans (IsBigO.of_bound 1 (Eventually.of_forall fun y => by simp))
  have H := hc'.neg_left.sub ha
  have H' : (fun v : ℝ => ∑ k ∈ Finset.range 9, (fun k => p.coeff k - igAsy_Pc k) k * v^k)
      =O[𝓝[≠] 0] fun v => v^9 := by
    refine H.congr' (Eventually.of_forall fun v => ?_) EventuallyEq.rfl
    simp only [sub_mul, Finset.sum_sub_distrib, igAsy_sum_Pc, mul_comm (p.coeff _)]
    ring
  intro k hk
  exact sub_eq_zero.1 (lapSad_coeff_eq_zero_of_isBigO 9 H' k hk)

/-- **The saddle substitution for `φ(u) = u - log(1+u)`.** There is an analytic `U` with
`φ(U(v)) = v²/2` near `0`, `sign U(v) = sign v`, and Taylor coefficients `igAsy_Pc`. -/
theorem igAsy_saddle : ∃ (U : ℝ → ℝ) (p : FormalMultilinearSeries ℝ ℝ ℝ) (v₀ : ℝ), 0 < v₀ ∧
    HasFPowerSeriesAt U p 0 ∧ (∀ k < 9, p.coeff k = igAsy_Pc k) ∧
    (∀ v ∈ Icc (-v₀) v₀, HasDerivAt U (deriv U v) v ∧ ContinuousAt (deriv U) v ∧
      -1/2 < U v ∧ igAsy_phi (U v) = v^2/2) ∧ U (-v₀) < 0 ∧ 0 < U v₀ := by
  obtain ⟨hVa, hVd, hVphi⟩ := igAsy_sqrtPhi_props
  obtain ⟨U, hUa, -, hU0, hl, hr⟩ := dblZero_exists_analytic_inverse hVa hVd one_ne_zero
  rw [igAsy_sqrtPhi_zero] at hUa hU0 hr
  obtain ⟨p, hp⟩ := hUa
  have hUt : Tendsto U (𝓝 0) (𝓝 0) := by
    simpa [hU0] using hp.analyticAt.continuousAt.tendsto
  have hev : ∀ᶠ v in 𝓝 (0:ℝ), AnalyticAt ℝ U v ∧ -1/2 < U v ∧ igAsy_phi (U v) = v^2/2 ∧
      igAsy_sqrtPhi (U v) = v := by
    filter_upwards [hp.analyticAt.eventually_analyticAt,
      hUt.eventually (lt_mem_nhds (by norm_num : (-1/2:ℝ) < 0)), hUt.eventually hVphi, hr]
      with v h1 h2 h3 h4
    exact ⟨h1, h2, by rw [h3, h4], h4⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hmem : ∀ v ∈ Icc (-(ε/2)) (ε/2), dist v 0 < ε := fun v hv => by
    rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [hv.1, hv.2]
  refine ⟨U, p, ε/2, by positivity, hp, igAsy_coeff_of_inverse hp hl, fun v hv => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := hball (hmem v hv)
    exact ⟨h1.differentiableAt.hasDerivAt, h1.deriv.continuousAt, h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := hball (hmem (-(ε/2)) ⟨le_rfl, by linarith⟩)
    by_contra hc
    replace hc := not_lt.1 hc
    have : 0 ≤ igAsy_sqrtPhi (U (-(ε/2))) := by
      unfold igAsy_sqrtPhi; rw [sub_zero]; exact mul_nonneg hc (Real.sqrt_nonneg _)
    linarith
  · obtain ⟨-, -, -, h4⟩ := hball (hmem (ε/2) ⟨by linarith, le_rfl⟩)
    by_contra hc
    replace hc := not_lt.1 hc
    have : igAsy_sqrtPhi (U (ε/2)) ≤ 0 := by
      unfold igAsy_sqrtPhi; rw [sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg _)
    linarith

/-- `s^n e^{n(1-s)} = e^{-n φ(s-1)}` at `s = 1 + u > 0`. -/
theorem igAsy_F_one_add (m : ℕ) {u : ℝ} (hu : -1 < u) :
    igAsy_F m 1 (1+u) = Real.exp (-((m:ℝ)+1) * igAsy_phi u) := by
  have h : 0 < 1+u := by linarith
  unfold igAsy_F igAsy_phi
  rw [← Real.exp_log (pow_pos h (m+1)), ← Real.exp_add, Real.log_pow]
  congr 1; push_cast; ring

/-- `∫₀^∞ s^n e^{n(1-s)} ds = eⁿ n!/n^{n+1}`. -/
theorem igAsy_integral_F_Ioi (m : ℕ) :
    IntegrableOn (igAsy_F m 1) (Ioi 0) ∧ ∫ s in Ioi (0:ℝ), igAsy_F m 1 s =
      Real.exp ((m:ℝ)+1) * ((m+1).factorial * (((m:ℝ)+1)^(m+2))⁻¹) := by
  have hs : (0:ℝ) < (m:ℝ)+2 := by positivity
  have hz : (0:ℝ) < (m:ℝ)+1 := by positivity
  have heq : EqOn (igAsy_F m 1) (fun s => Real.exp ((m:ℝ)+1) *
      (Real.exp (-((m:ℝ)+1) * s) * s ^ ((m:ℝ)+2-1))) (Ioi 0) := by
    intro s _
    dsimp only
    rw [show (m:ℝ)+2-1 = ((m+1:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
    unfold igAsy_F
    rw [show ((m:ℝ)+1)*1*(1-s) = ((m:ℝ)+1) + (-((m:ℝ)+1) * s) by ring, Real.exp_add]
    ring
  have hI : IntegrableOn (fun s => Real.exp ((m:ℝ)+1) *
      (Real.exp (-((m:ℝ)+1) * s) * s ^ ((m:ℝ)+2-1))) (Ioi 0) :=
    (integrableOn_exp_neg_mul_mul_rpow_sub_one hs hz).const_mul _
  refine ⟨hI.congr_fun heq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
    integral_exp_neg_mul_mul_rpow_sub_one hs hz,
    show (m:ℝ)+2 = ((m+1:ℕ):ℝ)+1 by push_cast; ring, Real.Gamma_nat_eq_factorial,
    Real.rpow_neg hz.le, show ((m+1:ℕ):ℝ)+1 = ((m+2:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]

/-- `φ` decreases on `(-1, 0]`: `φ(t-1) ≤ φ(s-1)` for `0 < s ≤ t ≤ 1`. -/
theorem igAsy_phi_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1) :
    igAsy_phi (t-1) ≤ igAsy_phi (s-1) := by
  have ht0 : 0 < t := hs.trans_le hst
  have h := Real.one_sub_inv_le_log_of_pos (div_pos ht0 hs)
  rw [Real.log_div ht0.ne' hs.ne', inv_div] at h
  unfold igAsy_phi
  simp only [add_sub_cancel]
  have h2 : 0 ≤ (t - s) * (1/t - 1) := mul_nonneg (by linarith) (by
    rw [sub_nonneg, le_div_iff₀ ht0]; linarith)
  have h3 : s/t = 1 - (t-s)/t := by field_simp; ring
  have h4 : (t-s)/t = (t-s)*(1/t) := by ring
  nlinarith

/-- Left tail: `∫₀ᵗ F ≤ t e^{-n φ(t-1)}` for `0 < t ≤ 1`. -/
theorem igAsy_left_tail (m : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ ∫ s in (0:ℝ)..t, igAsy_F m 1 s ∧
      ∫ s in (0:ℝ)..t, igAsy_F m 1 s ≤ t * Real.exp (-((m:ℝ)+1) * igAsy_phi (t-1)) := by
  have hc : Continuous (igAsy_F m 1) := by unfold igAsy_F; fun_prop
  refine ⟨intervalIntegral.integral_nonneg ht0.le fun s hs => igAsy_F_nonneg m 1 hs.1, ?_⟩
  have := intervalIntegral.integral_mono_on ht0.le (hc.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable (μ := volume) _ _)
    (g := fun _ => Real.exp (-((m:ℝ)+1) * igAsy_phi (t-1))) fun s hs => by
      rcases hs.1.eq_or_lt with h | h
      · subst h; simp [igAsy_F]; positivity
      · have := igAsy_F_one_add m (u := s-1) (by linarith)
        rw [add_sub_cancel] at this
        rw [this, Real.exp_le_exp]
        have := igAsy_phi_anti h hs.2 ht1
        nlinarith [show (0:ℝ) ≤ (m:ℝ)+1 by positivity]
  simpa using this

/-- Right tail: `∫_{1+a}^∞ F ≤ e^{-n φ(a)} (1+a)/(n a)` for `a > 0`. -/
theorem igAsy_right_tail (m : ℕ) {a : ℝ} (ha : 0 < a) :
    0 ≤ ∫ s in Ioi (1+a), igAsy_F m 1 s ∧ ∫ s in Ioi (1+a), igAsy_F m 1 s ≤
      Real.exp (-((m:ℝ)+1) * igAsy_phi a) * ((1+a)/(((m:ℝ)+1)*a)) := by
  set n : ℝ := (m:ℝ)+1 with hn
  have hn0 : 0 < n := by positivity
  set t := 1+a with ht
  have ht0 : 0 < t := by linarith
  set θ := a/t with hθ
  have hθ0 : 0 < θ := div_pos ha ht0
  have hFi : IntegrableOn (igAsy_F m 1) (Ioi t) :=
    (igAsy_integral_F_Ioi m).1.mono_set (Ioi_subset_Ioi ht0.le)
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun s hs =>
    igAsy_F_nonneg m 1 (ht0.trans hs).le, ?_⟩
  set C := Real.exp (-n * igAsy_phi a + n*θ*t) with hC
  have hgi : IntegrableOn (fun s => C * Real.exp ((-(n*θ)) * s)) (Ioi t) :=
    (integrableOn_exp_mul_Ioi (by nlinarith) t).const_mul C
  have hle := setIntegral_mono_on hFi hgi measurableSet_Ioi fun s (hs : t < s) => by
    have hs0 : 0 < s := ht0.trans hs
    have h1 := igAsy_F_one_add m (u := s-1) (by linarith)
    rw [add_sub_cancel] at h1
    rw [h1, hC, ← Real.exp_add, Real.exp_le_exp]
    have h2 := Real.log_le_sub_one_of_pos (div_pos hs0 ht0)
    rw [Real.log_div hs0.ne' ht0.ne'] at h2
    have h3 : igAsy_phi (s-1) - igAsy_phi a ≥ θ * (s - t) := by
      unfold igAsy_phi
      rw [show 1 + (s-1) = s by ring, ← ht]
      have : s/t - 1 = (s - t) - θ*(s-t) := by rw [hθ, ht]; field_simp; ring
      linarith
    nlinarith
  rw [integral_const_mul, integral_exp_mul_Ioi (by nlinarith) t, hC] at hle
  refine hle.trans (le_of_eq ?_)
  rw [neg_div_neg_eq, mul_div_assoc', ← Real.exp_add, show -n * igAsy_phi a + n*θ*t + -(n*θ)*t =
    -n * igAsy_phi a by ring, hθ]
  field_simp

/-- The exact decomposition behind 8.11.16: the Gaussian integral after the saddle substitution
plus exponentially small boundary terms. -/
theorem igAsy_one_decomp {U : ℝ → ℝ} {v₀ : ℝ} (hv₀ : 0 < v₀) (hU0 : U 0 = 0)
    (hd : ∀ v ∈ Icc (-v₀) v₀, HasDerivAt U (deriv U v) v ∧ ContinuousAt (deriv U) v ∧
      -1/2 < U v ∧ igAsy_phi (U v) = v^2/2) (ha : 0 < U v₀) (m : ℕ) :
    ((m:ℝ)+1)*1 * (∫ s in (0:ℝ)..1, igAsy_F m 1 s) -
        (m+1).factorial * Real.exp ((m:ℝ)+1) / (2*((m:ℝ)+1)^(m+1)) =
      ((m:ℝ)+1)^2/2 * (∫ v in (0:ℝ)..v₀, Real.exp (-((m:ℝ)+1) * v^2/2) * (v * (-U (-v) - U v))) +
      ((m:ℝ)+1)/2 * ((∫ s in (0:ℝ)..(1 + U (-v₀)), igAsy_F m 1 s) -
        (∫ s in Ioi (1 + U v₀), igAsy_F m 1 s) +
        Real.exp (-((m:ℝ)+1) * v₀^2/2) * (-U (-v₀) - U v₀)) := by
  set n : ℝ := (m:ℝ)+1 with hn
  set F := igAsy_F m 1 with hF
  have hFc : Continuous F := by rw [hF]; unfold igAsy_F; fun_prop
  set g : ℝ → ℝ := fun v => Real.exp (-n * v^2/2) with hg
  have hgd : ∀ v, HasDerivAt g (-n * v * g v) v := fun v => by
    have := (((hasDerivAt_pow 2 v).const_mul (-n)).div_const 2).exp
    convert this using 1
    simp only [hg]; push_cast; ring
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hUc : ContinuousOn U (Icc (-v₀) v₀) := fun v hv =>
    (hd v hv).1.continuousAt.continuousWithinAt
  have hU'c : ContinuousOn (deriv U) (Icc (-v₀) v₀) := fun v hv =>
    (hd v hv).2.1.continuousWithinAt
  have hIcc1 : uIcc (-v₀) 0 ⊆ Icc (-v₀) v₀ := by
    rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl hv₀.le
  have hIcc2 : uIcc 0 v₀ ⊆ Icc (-v₀) v₀ := by
    rw [uIcc_of_le hv₀.le]; exact Icc_subset_Icc (by linarith) le_rfl
  have hFU : ∀ v ∈ Icc (-v₀) v₀, F (1 + U v) = g v := fun v hv => by
    rw [hF, igAsy_F_one_add m (by linarith [(hd v hv).2.2.1]), (hd v hv).2.2.2, hg]
    congr 1; ring
  -- substitution
  have hsub : ∀ {a b : ℝ}, uIcc a b ⊆ Icc (-v₀) v₀ →
      ∫ v in a..b, g v * deriv U v = ∫ s in (1 + U a)..(1 + U b), F s := by
    intro a b hab
    rw [← intervalIntegral.integral_comp_mul_deriv (f := fun v => 1 + U v) (f' := deriv U)
      (fun x hx => ((hd x (hab hx)).1.const_add 1)) (hU'c.mono hab) hFc]
    refine intervalIntegral.integral_congr fun v hv => ?_
    simp only [Function.comp_apply, hFU v (hab hv)]
  -- integration by parts
  have hibp : ∀ {a b : ℝ}, uIcc a b ⊆ Icc (-v₀) v₀ →
      ∫ v in a..b, g v * deriv U v = g b * U b - g a * U a - ∫ v in a..b, (-n * v * g v) * U v := by
    intro a b hab
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => hgd x)
      (fun x hx => (hd x (hab hx)).1)
      ((by fun_prop : Continuous fun v => -n * v * g v).intervalIntegrable _ _)
      ((hU'c.mono hab).intervalIntegrable)
  have h1 := hsub hIcc1
  have h2 := hsub hIcc2
  rw [hibp hIcc1] at h1
  rw [hibp hIcc2] at h2
  rw [hU0, add_zero] at h1 h2
  -- reflection
  have hrefl : ∫ v in (-v₀)..0, (-n * v * g v) * U v = ∫ v in (0:ℝ)..v₀, (n * v * g v) * U (-v) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := v₀)
      (fun v => (-n * v * g v) * U v)
    rw [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [hg]; ring_nf
  rw [hrefl] at h1
  -- the Gaussian integral
  have hUc2 : ContinuousOn U (uIcc 0 v₀) := hUc.mono hIcc2
  have hUn : ContinuousOn (fun v => U (-v)) (uIcc 0 v₀) := hUc.comp continuousOn_neg
    (fun v hv => by
      rw [uIcc_of_le hv₀.le] at hv
      exact ⟨by linarith [hv.2], by linarith [hv.1]⟩)
  have hi1 : IntervalIntegrable (fun v => (n * v * g v) * U (-v)) volume 0 v₀ :=
    ((by fun_prop : Continuous fun v => n * v * g v).continuousOn.mul hUn).intervalIntegrable
  have hi2 : IntervalIntegrable (fun v => (-n * v * g v) * U v) volume 0 v₀ :=
    ((by fun_prop : Continuous fun v => -n * v * g v).continuousOn.mul hUc2).intervalIntegrable
  have hI : n * ∫ v in (0:ℝ)..v₀, Real.exp (-n * v^2/2) * (v * (-U (-v) - U v)) =
      -(∫ v in (0:ℝ)..v₀, (n * v * g v) * U (-v)) + ∫ v in (0:ℝ)..v₀, (-n * v * g v) * U v := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg,
      ← intervalIntegral.integral_add (f := fun v => -((n * v * g v) * U (-v))) hi1.neg hi2]
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [hg]; ring
  -- splitting the integrals
  obtain ⟨hFi, hFI⟩ := igAsy_integral_F_Ioi m
  have hb1 : 0 < 1 + U (-v₀) := by linarith [(hd (-v₀) ⟨le_rfl, by linarith⟩).2.2.1]
  have ha1 : (1:ℝ) ≤ 1 + U v₀ := by linarith
  have hs1 : ∫ s in (0:ℝ)..1, F s = (∫ s in (0:ℝ)..(1 + U (-v₀)), F s) +
      ∫ s in (1 + U (-v₀))..1, F s :=
    (intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
      (hFc.intervalIntegrable _ _)).symm
  have hs2 : ∫ s in Ioi (0:ℝ), F s = (∫ s in (0:ℝ)..1, F s) + ((∫ s in (1:ℝ)..(1 + U v₀), F s) +
      ∫ s in Ioi (1 + U v₀), F s) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hFi.mono_set Ioc_subset_Ioi_self) (hFi.mono_set (Ioi_subset_Ioi
      zero_le_one)), ← Ioc_union_Ioi_eq_Ioi ha1, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hFi.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one)))
      (hFi.mono_set (Ioi_subset_Ioi (by linarith))), intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le ha1]
  have hfac : ((m+1).factorial : ℝ) * Real.exp n / (2 * n^(m+1)) =
      n/2 * ∫ s in Ioi (0:ℝ), F s := by
    rw [hF, hFI]
    have : (0:ℝ) < n := by positivity
    field_simp
    ring
  rw [hfac, hs2, hs1]
  have hg0 : g 0 = 1 := by simp [hg]
  have hgv : g v₀ = Real.exp (-n * v₀^2/2) := rfl
  have hgv' : g (-v₀) = Real.exp (-n * v₀^2/2) := by simp [hg]
  rw [hgv', hg0] at h1
  rw [hgv, hg0] at h2
  linear_combination (n/2) * (h2 - h1 - hI)

/-- `x^{-(j+1)} = (x^{j+1})⁻¹` for `x > 0`. -/
theorem igAsy_rpow_neg_succ {x : ℝ} (hx : 0 < x) (j : ℕ) : x ^ (-((j:ℝ)+1)) = (x^(j+1))⁻¹ := by
  rw [Real.rpow_neg hx.le, show (j:ℝ)+1 = ((j+1:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]

/-- `n e^{-n κ} = O(n^{-N})`. -/
theorem igAsy_exp_small {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    ∀ᶠ m : ℕ in atTop, ((m:ℝ)+1) * Real.exp (-((m:ℝ)+1) * κ) ≤
      κ⁻¹^(N+1) * (((m:ℝ)+1)^N)⁻¹ := by
  have h1 : Tendsto (fun m : ℕ => ((m:ℝ)+1) * κ) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const hκ
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (N+1)).comp h1
  filter_upwards [h2.eventually (ge_mem_nhds (zero_lt_one))] with m hm
  simp only [Function.comp_apply] at hm
  have hn : (0:ℝ) < (m:ℝ)+1 := by positivity
  rw [← mul_le_mul_iff_of_pos_left (pow_pos hκ (N+1)),
    ← mul_le_mul_iff_of_pos_left (pow_pos hn N)]
  calc ((m:ℝ)+1)^N * (κ^(N+1) * (((m:ℝ)+1) * Real.exp (-((m:ℝ)+1) * κ)))
      = (((m:ℝ)+1) * κ)^(N+1) * Real.exp (-(((m:ℝ)+1) * κ)) := by
        rw [mul_pow, show -(((m:ℝ)+1) * κ) = -((m:ℝ)+1) * κ by ring]; ring
    _ ≤ 1 := hm
    _ = ((m:ℝ)+1)^N * (κ^(N+1) * (κ⁻¹^(N+1) * (((m:ℝ)+1)^N)⁻¹)) := by
      rw [inv_pow]; field_simp

/-- Estimate under the stated parameter and domain assumptions: `∃ c : ℕ → ℂ, (∀ n < 4, c
n=([-2/3,4/135,-8/2835,-16/8505] : List ℂ)[n]!) ∧ HasAsymptoticExpansion atTop (fun j (n : ℕ)
=> (n+1 : ℂ)^(-(j : ℤ))) c (fun n => expPartialSumRemainderS (n+1) 1-(n+1).factorial*exp (n+1
: ℂ)/(2*(n+1 : ℂ)^(n+1)))`. -/
@[dlmf 8.11.E16]
theorem expPartialSumRemainderS_one_asymptotic  :
    ∃ c : ℕ → ℂ, (∀ n < 4, c n=([-2/3,4/135,-8/2835,-16/8505] : List ℂ)[n]!) ∧ HasAsymptoticExpansion atTop (fun j (n : ℕ) => (n+1 : ℂ)^(-(j : ℤ))) c (fun n => expPartialSumRemainderS (n+1) 1-(n+1).factorial*exp (n+1 : ℂ)/(2*(n+1 : ℂ)^(n+1))) := by
  obtain ⟨U, p, v₀, hv₀, hp, hc, hd, hb, ha⟩ := igAsy_saddle
  have hc0 : p.coeff 0 = 0 := (hc 0 (by norm_num)).trans (by simp [igAsy_Pc])
  have hU0 : U 0 = 0 := by rw [← hp.coeff_zero 1]; exact hc0
  have hUc : ContinuousOn U (Icc (-v₀) v₀) := fun v hv =>
    (hd v hv).1.continuousAt.continuousWithinAt
  set γ : ℕ → ℝ := fun j => Real.Gamma ((j:ℝ)+1) * (2^j * (-2 * p.coeff (2*j))) with hγ
  have hγ0 : γ 0 = 0 := by simp [hγ, hc0]
  have hγs : ∀ k, γ (k+1) / 2 = -((k+1).factorial : ℝ) * 2^(k+1) * p.coeff (2*k+2) := by
    intro k
    simp only [hγ]
    rw [show ((k+1:ℕ):ℝ)+1 = ((k+1:ℕ):ℝ)+1 from rfl, Real.Gamma_nat_eq_factorial,
      show 2*(k+1) = 2*k+2 by ring]
    ring
  have H := lapSad_hasAsymptoticExpansion_gauss_analytic hp hv₀ hUc
  refine ⟨fun k => ((γ (k+1) / 2 : ℝ) : ℂ), ?_, ?_⟩
  · intro k hk
    interval_cases k <;>
      norm_num [hγs, hc 2 (by norm_num), hc 4 (by norm_num), hc 6 (by norm_num),
        hc 8 (by norm_num), igAsy_Pc, Nat.factorial]
  intro N
  have hnat : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  obtain ⟨C, hC⟩ := ((H (N+1)).comp_tendsto hnat).bound
  set κ : ℝ := v₀^2/2 with hκ
  have hκ0 : 0 < κ := by positivity
  set a := U v₀
  set b := U (-v₀)
  set K : ℝ := (1 + b) + (1 + a)/a + |-b - a| with hK
  have hφb : igAsy_phi b = κ := by
    rw [(hd (-v₀) ⟨le_rfl, by linarith⟩).2.2.2]; ring
  have hφa : igAsy_phi a = κ := (hd v₀ ⟨by linarith, le_rfl⟩).2.2.2
  have hb1 : 0 < 1 + b := by linarith [(hd (-v₀) ⟨le_rfl, by linarith⟩).2.2.1]
  refine IsBigO.of_bound (C/2 + K/2 * κ⁻¹^(N+1)) ?_
  filter_upwards [hC, igAsy_exp_small hκ0 N] with m hCm hEm
  simp only [Function.comp_apply] at hCm
  set n : ℝ := (m:ℝ)+1 with hn
  have hn0 : 0 < n := by positivity
  have hn1 : 1 ≤ n := by simp [hn]
  have hdec := igAsy_one_decomp hv₀ hU0 hd ha m
  obtain ⟨hL0, hL1⟩ := igAsy_left_tail m hb1 (by linarith)
  obtain ⟨hR0, hR1⟩ := igAsy_right_tail m ha
  rw [add_sub_cancel_left, hφb] at hL1
  rw [hφa] at hR1
  set I := ∫ v in (0:ℝ)..v₀, Real.exp (-n * v^2/2) * (v * (-U (-v) - U v))
  set TL := ∫ s in (0:ℝ)..(1 + b), igAsy_F m 1 s
  set TR := ∫ s in Ioi (1 + a), igAsy_F m 1 s
  set E := Real.exp (-n * κ) with hE
  have hE' : Real.exp (-n * v₀^2/2) = E := by rw [hE, hκ]; congr 1; ring
  rw [hE'] at hdec
  -- the real form of the function
  have hfun : expPartialSumRemainderS (m+1) 1 - ((m+1).factorial : ℂ) * Complex.exp ((m:ℂ)+1) /
      (2*((m:ℂ)+1)^(m+1)) = ((n^2/2 * I + n/2 * (TL - TR + E * (-b - a)) : ℝ) : ℂ) := by
    rw [← hdec, igAsy_S_eq]
    push_cast
    rfl
  have hsumC : ∑ j ∈ Finset.range N, ((m:ℂ)+1)^(-(j:ℤ)) • (((γ (j+1) / 2 : ℝ)) : ℂ) =
      ((∑ j ∈ Finset.range N, (n^j)⁻¹ * (γ (j+1) / 2) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zpow_neg, zpow_natCast, smul_eq_mul, hn]
    push_cast
    ring
  have hsumR : ∑ j ∈ Finset.range N, (n^j)⁻¹ * (γ (j+1) / 2) =
      n^2/2 * ∑ j ∈ Finset.range (N+1), n ^ (-((j:ℝ)+1)) • γ j := by
    rw [Finset.sum_range_succ', hγ0, smul_zero, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, igAsy_rpow_neg_succ hn0 (j+1)]
    field_simp
    ring
  have hnorm : ‖((m:ℂ)+1)^(-(N:ℤ))‖ = (n^N)⁻¹ := by
    rw [zpow_neg, zpow_natCast, norm_inv, norm_pow,
      show ‖(m:ℂ)+1‖ = (m:ℝ)+1 by exact_mod_cast Complex.norm_natCast (m+1)]
  rw [igAsy_rpow_neg_succ hn0 (N+1), Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (pow_pos hn0 _))] at hCm
  rw [hfun, hsumC, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hsumR, hnorm]
  set T := TL - TR + E * (-b - a) with hT
  set Ss := ∑ j ∈ Finset.range (N+1), n ^ (-((j:ℝ)+1)) • γ j
  have hEp : 0 < E := Real.exp_pos _
  have hK0 : 0 ≤ K := by
    rw [hK]; have := div_pos (by linarith : 0 < 1 + a) ha; positivity
  have hTb : |T| ≤ K * E := by
    have h1 : (1+a)/(n*a) ≤ (1+a)/a :=
      div_le_div_of_nonneg_left (by linarith) ha (by nlinarith)
    have h2 := hR1.trans (mul_le_mul_of_nonneg_left h1 hEp.le)
    have h3 := mul_le_mul_of_nonneg_left (le_abs_self (-b - a)) hEp.le
    have h4 := mul_le_mul_of_nonneg_left (neg_abs_le (-b - a)) hEp.le
    have h5 : K*E = (1+b)*E + E*((1+a)/a) + E*|-b-a| := by rw [hK]; ring
    have h6 : 0 ≤ (1+b)*E := by positivity
    have h7 : 0 ≤ E*((1+a)/a) := mul_nonneg hEp.le (div_pos (by linarith) ha).le
    rw [abs_le]; constructor <;> linarith
  calc |n^2/2 * I + n/2 * T - n^2/2 * Ss| = |n^2/2 * (I - Ss) + n/2 * T| := by ring_nf
    _ ≤ n^2/2 * |I - Ss| + n/2 * |T| := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < n^2/2),
        abs_of_pos (by positivity : (0:ℝ) < n/2)]
    _ ≤ n^2/2 * (C * (n^(N+1+1))⁻¹) + K/2 * (n * E) := by
      have := mul_le_mul_of_nonneg_left hTb (by positivity : (0:ℝ) ≤ n/2)
      exact add_le_add (mul_le_mul_of_nonneg_left hCm (by positivity))
        (this.trans (le_of_eq (by ring)))
    _ ≤ n^2/2 * (C * (n^(N+1+1))⁻¹) + K/2 * (κ⁻¹^(N+1) * (n^N)⁻¹) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hEm (by positivity))
    _ = (C/2 + K/2 * κ⁻¹^(N+1)) * (n^N)⁻¹ := by
      field_simp
      ring

/-- Estimate under the stated parameter and domain assumptions: `∃ c : ℕ → ℂ, (∀ n < 5, c
n=([-1/2,1/8,1/32,-1/128,-13/512] : List ℂ)[n]!) ∧ HasAsymptoticExpansion atTop (fun j (n : ℕ)
=> (n+1 : ℂ)^(-(j : ℤ))) c (fun n => expPartialSumRemainderS (n+1) (-1))`. -/
@[dlmf 8.11.E17]
theorem expPartialSumRemainderS_neg_one_asymptotic  :
    ∃ c : ℕ → ℂ, (∀ n < 5, c n=([-1/2,1/8,1/32,-1/128,-13/512] : List ℂ)[n]!) ∧ HasAsymptoticExpansion atTop (fun j (n : ℕ) => (n+1 : ℂ)^(-(j : ℤ))) c (fun n => expPartialSumRemainderS (n+1) (-1)) := by
  refine ⟨fun k => (igAsy_d k (-1) : ℂ), ?_, ?_⟩
  · intro n hn
    interval_cases n <;>
      norm_num [igAsy_d, igAsy_h, igAsy_poly, Polynomial.derivative_mul]
  · intro N
    obtain ⟨C, hC⟩ := igAsy_S_remainder_bound N (δ := 1) one_pos
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    have hm : (0:ℝ) < (n:ℝ)+1 := by positivity
    have hsum : ∑ j ∈ Finset.range N, ((n:ℂ)+1)^(-(j:ℤ)) • (igAsy_d j (-1) : ℂ) =
        ∑ k ∈ Finset.range N, (igAsy_d k (-1) : ℂ)/((n:ℂ)+1)^k := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_comm]
    rw [hsum]
    dsimp only
    rw [zpow_neg, zpow_natCast, norm_inv, norm_pow,
      show ‖(n:ℂ)+1‖ = (n:ℝ)+1 by exact_mod_cast Complex.norm_natCast (n+1), ← one_div]
    exact hC n (-1) (by norm_num)

/-- The coefficients d_k(x). -/
@[dlmf 8.11.E19]
def expPartialSumRemainderCoeff (k : ℕ) (x : ℝ) : ℂ :=
  if k=0 then x/(1-x) else (-1 : ℂ)^k*(incGammaLambdaPolynomial k).eval (x : ℂ)/(1-x : ℂ)^(2*k+1)

/-- `b_k = X p_k` for `k ≥ 1`. -/
theorem igAsy_lambdaPoly_eq {k : ℕ} (hk : 1 ≤ k) :
    incGammaLambdaPolynomial k = Polynomial.X * (igAsy_poly k).map (algebraMap ℝ ℂ) := by
  induction k, hk using Nat.le_induction with
  | base =>
    simp [incGammaLambdaPolynomial, igAsy_poly]
  | succ k hk ih =>
    rw [incGammaLambdaPolynomial, ih, igAsy_poly]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X,
      Polynomial.map_C, Polynomial.derivative_map]
    simp
    ring

/-- `b_k(x) = x p_k(x)` for `k ≥ 1`, evaluated at a real point. -/
theorem igAsy_lambdaPoly_eval {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    (incGammaLambdaPolynomial k).eval (x : ℂ) = x * (((igAsy_poly k).eval x : ℝ) : ℂ) := by
  rw [igAsy_lambdaPoly_eq hk, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_map,
    show (x:ℂ) = algebraMap ℝ ℂ x from rfl, Polynomial.eval₂_at_apply]
  rfl

/-- The coefficients `d_k(x)` of 8.11.19 in terms of `h_k`. -/
theorem igAsy_coeff_eq (k : ℕ) {x : ℝ} (hx : x ≠ 1) :
    expPartialSumRemainderCoeff k x = (igAsy_d k x : ℂ) := by
  unfold igAsy_d
  have hx1 : (1:ℂ) - x ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hx.symm
  unfold expPartialSumRemainderCoeff
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [igAsy_h_zero]
  · simp only [hk.ne', ↓reduceIte]
    rw [igAsy_lambdaPoly_eval hk, igAsy_h]
    push_cast
    rw [pow_succ]
    field_simp

/-- Estimate under the stated parameter and domain assumptions: `IsBigO (comap (fun p : ℕ × ℝ =>
p.1) atTop ⊓ 𝓟 {p : ℕ × ℝ | p.2 ≤ 1-δ}) (fun p => expPartialSumRemainderS (p.1+1) p.2-∑ k ∈
Finset.range N, expPartialSumRemainderCoeff k p.2/(p.1+1 : ℂ)^k) (fun p => (p.1+1 : ℝ)^(-(N :
ℤ)))`. -/
@[dlmf 8.11.E18]
theorem expPartialSumRemainderS_uniform_asymptotic {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    IsBigO (comap (fun p : ℕ × ℝ => p.1) atTop ⊓ 𝓟 {p : ℕ × ℝ | p.2 ≤ 1-δ}) (fun p => expPartialSumRemainderS (p.1+1) p.2-∑ k ∈ Finset.range N, expPartialSumRemainderCoeff k p.2/(p.1+1 : ℂ)^k) (fun p => (p.1+1 : ℝ)^(-(N : ℤ))) := by
  obtain ⟨C, hC⟩ := igAsy_S_remainder_bound N hδ
  refine IsBigO.of_bound C ?_
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with p hp
  have hp' : p.2 ≠ 1 := fun h => by have : p.2 ≤ 1-δ := hp; linarith
  rw [Finset.sum_congr rfl fun k _ => by rw [igAsy_coeff_eq k hp']]
  have hm : (0:ℝ) < (p.1:ℝ)+1 := by positivity
  rw [Real.norm_eq_abs, zpow_neg, zpow_natCast, abs_inv, abs_of_pos (by positivity), ← one_div]
  exact hC p.1 p.2 hp

end DLMF.Confluent
end
