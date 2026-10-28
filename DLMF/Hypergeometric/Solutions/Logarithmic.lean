/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Solutions.Equation

/-!
# Logarithmic solutions of the Gauss equation

Logarithmic fundamental solutions at integral parameters and their Wronskians, including
terminating cases.

Source references and common attribution are retained in
`DLMF.Hypergeometric.Solutions`.
-/

@[expose] public section

open Complex Filter

open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-! ### Logarithmic solutions for integral `c` (DLMF 15.10.8–10) -/

section LogSolutions

open FormalMultilinearSeries
open scoped ENNReal

/-- The Gauss operator applied to a power series, coefficientwise. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_gaussOperator {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) (a b d : ℂ) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) r) :
    HasSum (fun n : ℕ => ((n + 1) * (d + n) * c (n + 1) - (n + a) * (n + b) * c n) * z ^ n)
      (gaussOperator a b d f z) := by
  have h0 := h.hasSum_mul_pow hz
  have h1 := h.deriv_ofScalars.hasSum_mul_pow hz
  have hz1 := h.hasSum_z_mul_deriv hz
  have hz2 := h.deriv_ofScalars.hasSum_z_mul_deriv hz
  have hzz2 : HasSum (fun n : ℕ => (n : ℂ) * (n - 1) * c n * z ^ n)
      (z ^ 2 * deriv (deriv f) z) := by
    have hs : HasSum (fun n : ℕ =>
        (n + 1 : ℂ) * ((n + 1 : ℂ) - 1) * c (n + 1) * z ^ n)
        (z * deriv (deriv f) z) := by
      convert hz2 using 1
      funext n
      ring
    have ht := HasSum.mul_pow_shift (c := fun n => (n : ℂ) * (n - 1) * c n)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hs) (by simp)
    convert ht using 1
    ring
  have hall := ((hz2.add (h1.mul_left d)).sub (hzz2.add (hz1.mul_left (a + b + 1)))).sub
    (h0.mul_left (a * b))
  convert hall using 1
  · funext n; ring
  · simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero]; ring

/-- The Gauss operator on `F · log`. -/
theorem gaussOperator_mul_log {a b c : ℂ} {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z)
    (hz : z ∈ slitPlane) :
    gaussOperator a b c (fun v => F v * log v) z =
      log z * gaussOperator a b c F z + (2 * (1 - z) * deriv F z + (c - 1) * F z / z -
        (a + b) * F z) := by
  have hz0 := slitPlane_ne_zero hz
  have hd : deriv (fun v => F v * log v) =ᶠ[𝓝 z] fun v => deriv F v * log v + F v * v⁻¹ := by
    filter_upwards [hF.eventually_analyticAt, isOpen_slitPlane.mem_nhds hz] with v hv hvs
    exact (hv.differentiableAt.hasDerivAt.mul (hasDerivAt_log hvs)).deriv
  have hdd : deriv (deriv (fun v => F v * log v)) z =
      deriv (deriv F) z * log z + deriv F z * z⁻¹ + (deriv F z * z⁻¹ + F z * (-(z ^ 2)⁻¹)) := by
    rw [hd.deriv_eq]
    have h := (hF.deriv.differentiableAt.hasDerivAt.mul (hasDerivAt_log hz)).add
      (hF.differentiableAt.hasDerivAt.mul (hasDerivAt_inv hz0))
    exact h.deriv
  simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hdd, hd.eq_of_nhds]
  field_simp
  ring

/-- For `v ≠ 0`, the derivative of `w ↦ w⁻ᵖ` at `v` is `-p v^{-(p+1)}`. -/
theorem hasDerivAt_recip_pow (p : ℕ) {v : ℂ} (hv : v ≠ 0) :
    HasDerivAt (fun w : ℂ => w⁻¹ ^ p) (-(p : ℂ) * v⁻¹ ^ (p + 1)) v := by
  have h := (hasDerivAt_inv hv).pow p
  refine h.congr_deriv ?_
  rcases p with _ | p
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [show v⁻¹ ^ (p + 1 + 1) = v⁻¹ ^ p * (v ^ 2)⁻¹ by rw [← inv_pow v 2, ← pow_add]]
    push_cast
    ring

/-- The pole part of the logarithmic solutions (DLMF 15.10.8–10). -/
def logSing (a b : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n - 1),
    ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
      (((n - j - 2).factorial : ℂ) * poch (1 - a) (j + 1) * poch (1 - b) (j + 1)) * ((-z)⁻¹) ^ (j + 1)

/-- If `(x)_N ≠ 0` then `(x)_k ≠ 0` for every `k ≤ N`. -/
theorem poch_ne_zero_of_le {x : ℂ} {N k : ℕ} (hk : k ≤ N) (h : poch x N ≠ 0) : poch x k ≠ 0 := by
  intro h0
  apply h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [poch_add, h0, zero_mul]

/-- For `c = n ≥ 1`, the Gauss operator maps the pole part `logSing` to `(n - 1)/z`. -/
theorem gaussOperator_logSing {a b : ℂ} {n : ℕ} (hn : 0 < n)
    (ha : poch (1 - a) (n - 1) ≠ 0) (hb : poch (1 - b) (n - 1) ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    gaussOperator a b n (logSing a b n) z = (n - 1) / z := by
  set e : ℕ → ℂ := fun j => ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
      (((n - j - 2).factorial : ℂ) * poch (1 - a) (j + 1) * poch (1 - b) (j + 1)) with he
  set σ : ℕ → ℂ := fun j => e j * (-1) ^ (j + 1) with hσ
  have hS : logSing a b n = fun v => ∑ j ∈ Finset.range (n - 1), σ j * v⁻¹ ^ (j + 1) := by
    funext v
    simp only [logSing, hσ, he]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inv_neg, neg_eq_neg_one_mul, mul_pow, inv_pow]
    ring
  have hS1 : ∀ v : ℂ, v ≠ 0 → HasDerivAt (logSing a b n)
      (∑ j ∈ Finset.range (n - 1), σ j * (-((j + 1 : ℕ) : ℂ) * v⁻¹ ^ (j + 2))) v := by
    intro v hv
    rw [hS]
    exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_recip_pow (j + 1) hv).const_mul (σ j)
  have hS2 : HasDerivAt (fun v => ∑ j ∈ Finset.range (n - 1), σ j * (-((j + 1 : ℕ) : ℂ) * v⁻¹ ^ (j + 2)))
      (∑ j ∈ Finset.range (n - 1), σ j * (-((j + 1 : ℕ) : ℂ) * (-((j + 2 : ℕ) : ℂ) * z⁻¹ ^ (j + 3))))
      z :=
    HasDerivAt.fun_sum fun j _ => ((hasDerivAt_recip_pow (j + 2) hz).const_mul _).const_mul (σ j)
  have hev : deriv (logSing a b n) =ᶠ[𝓝 z]
      fun v => ∑ j ∈ Finset.range (n - 1), σ j * (-((j + 1 : ℕ) : ℂ) * v⁻¹ ^ (j + 2)) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with v hv
    exact (hS1 v hv).deriv
  simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hev.deriv_eq, hS2.deriv, (hS1 z hz).deriv, hS]
  set u := z⁻¹ with hu
  have hzu : z * u = 1 := mul_inv_cancel₀ hz
  set t : ℕ → ℂ := fun j => if j < n - 1 then σ j * (j + 1 - a) * (j + 1 - b) * u ^ (j + 1) else 0
    with ht
  have hterm : ∀ j ∈ Finset.range (n - 1),
      z * (1 - z) * (σ j * (-((j + 1 : ℕ) : ℂ) * (-((j + 2 : ℕ) : ℂ) * u ^ (j + 3)))) +
        (n - (a + b + 1) * z) * (σ j * (-((j + 1 : ℕ) : ℂ) * u ^ (j + 2))) -
        a * b * (σ j * u ^ (j + 1)) = t (j + 1) - t j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have htj : t j = σ j * (j + 1 - a) * (j + 1 - b) * u ^ (j + 1) := by simp [ht, hj]
    have key : t (j + 1) = σ j * (j + 1) * (j + 2 - n) * u ^ (j + 2) := by
      by_cases hj1 : j + 1 < n - 1
      · obtain ⟨N, hN⟩ : ∃ N, n = N + j + 3 := ⟨n - j - 3, by omega⟩
        have hpa := poch_ne_zero_of_le (show j + 2 ≤ n - 1 by omega) ha
        have hpb := poch_ne_zero_of_le (show j + 2 ≤ n - 1 by omega) hb
        have hpa1 := poch_ne_zero_of_le (show j + 1 ≤ j + 2 by omega) hpa
        have hpb1 := poch_ne_zero_of_le (show j + 1 ≤ j + 2 by omega) hpb
        rw [poch_succ] at hpa hpb
        have h1 : n - j - 2 = N + 1 := by omega
        have h2 : n - (j + 1) - 2 = N := by omega
        simp only [ht, ite_eq_left_iff.mpr (fun h => absurd hj1 h), hσ, he, h1, h2]
        rw [poch_succ (1 - a) (j + 1), poch_succ (1 - b) (j + 1), Nat.factorial_succ j,
          Nat.factorial_succ N]
        have hn' : (n : ℂ) = N + j + 3 := by rw [hN]; push_cast; ring
        rw [hn']
        generalize poch (1 - a) (j + 1) = Pa at *
        generalize poch (1 - b) (j + 1) = Pb at *
        generalize ((n - 1).factorial : ℂ) = M
        have hF : (N.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr N.factorial_ne_zero
        have hJ : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
        have hN1 : ((N + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast at hpa hpb hN1 ⊢
        have hA := right_ne_zero_of_mul hpa
        have hB := right_ne_zero_of_mul hpb
        have hPa := left_ne_zero_of_mul hpa
        have hPb := left_ne_zero_of_mul hpb
        field_simp
        ring
      · have hjn : j + 2 = n := by omega
        simp only [ht, ite_eq_right_iff.mpr (fun h => absurd h hj1)]
        rw [← hjn]; push_cast; ring
    rw [key, htj]
    have e3 : u ^ (j + 3) = u ^ (j + 1) * u * u := by ring
    have e2 : u ^ (j + 2) = u ^ (j + 1) * u := by ring
    rw [e3, e2]
    generalize σ j = sj
    generalize u ^ (j + 1) = U
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linear_combination (sj * U * (j + 1) * (j + 2) * (u - z * u - 1) +
      sj * U * (a + b + 1) * (j + 1)) * hzu
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm,
    Finset.sum_range_sub]
  have htn : t (n - 1) = 0 := by simp [ht]
  rw [htn, zero_sub]
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have : n = 1 := by omega
    subst this
    simp [ht]
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
    have h0 : (0 : ℕ) < N + 2 - 1 := by omega
    have hpa := poch_ne_zero_of_le (show 1 ≤ N + 2 - 1 by omega) ha
    have hpb := poch_ne_zero_of_le (show 1 ≤ N + 2 - 1 by omega) hb
    rw [poch_one] at hpa hpb
    have ht0 : t 0 = σ 0 * (1 - a) * (1 - b) * u := by
      simp only [ht]
      rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
      simp
    have he0 : e 0 = ((N + 1 : ℕ) : ℂ) / ((1 - a) * (1 - b)) := by
      simp only [he]
      rw [show N + 2 - 1 = N + 1 by omega, show N + 2 - 0 - 2 = N by omega, Nat.factorial_succ N,
        Nat.factorial_zero, zero_add, poch_one, poch_one]
      have hF : (N.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr N.factorial_ne_zero
      push_cast
      field_simp
    rw [ht0, hσ]
    simp only
    rw [he0, hu]
    push_cast
    field_simp
    ring

/-- The pole part `logSing` is analytic away from `0`. -/
theorem analyticAt_logSing (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) : AnalyticAt ℂ (logSing a b n) z := by
  unfold logSing
  have h : ∀ j ∈ Finset.range (n - 1), AnalyticAt ℂ (fun v : ℂ => ((n - 1).factorial : ℂ) *
      (j.factorial : ℂ) / (((n - j - 2).factorial : ℂ) * poch (1 - a) (j + 1) *
        poch (1 - b) (j + 1)) * ((-v)⁻¹) ^ (j + 1)) z := fun j _ =>
    analyticAt_const.mul ((analyticAt_id.neg.inv (neg_ne_zero.mpr hz)).pow _)
  exact (Finset.analyticAt_fun_sum _ h)

/-- A logarithmic solution of the Gauss equation with integral denominator `n`, given the
recurrence for the coefficients of its power-series part. -/
theorem gaussOperator_logSolution {a b : ℂ} {n : ℕ} (hn : 0 < n)
    (ha : poch (1 - a) (n - 1) ≠ 0) (hb : poch (1 - b) (n - 1) ≠ 0) {h : ℕ → ℂ} {H : ℂ → ℂ}
    (hH : HasFPowerSeriesOnBall H (ofScalars ℂ h) 0 1)
    (hrec : ∀ k : ℕ, (k + 1) * (n + k) * h (k + 1) - (k + a) * (k + b) * h k +
      2 * (k + 1) * gaussHGCoeff a b n (k + 1) - (2 * k + a + b) * gaussHGCoeff a b n k +
      (n - 1) * gaussHGCoeff a b n (k + 1) = 0)
    {z : ℂ} (hz : ‖z‖ < 1) (hs : z ∈ slitPlane) :
    gaussOperator a b n (fun v => ₂F₁ a b (n : ℂ) v * log v - logSing a b n v + H v) z = 0 := by
  have hz0 := slitPlane_ne_zero hs
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  set F : ℂ → ℂ := ₂F₁ a b (n : ℂ) with hFdef
  have hFs := hasFPowerSeriesOnBall_ordinaryHypergeometric a b (n : ℂ)
  have hzb : z ∈ Metric.eball (0 : ℂ) 1 := mem_eball_one_of_norm_lt_one hz
  have hFa : AnalyticAt ℂ F z := hFs.analyticAt_of_mem hzb
  have hFlog : AnalyticAt ℂ (fun v => F v * log v) z := hFa.mul (analyticAt_clog hs)
  have hHa : AnalyticAt ℂ H z := hH.analyticAt_of_mem hzb
  have hfun : (fun v => F v * log v - logSing a b n v + H v) =
      fun v => F v * log v - 1 * logSing a b n v - (-1) * H v := by funext v; ring
  rw [hfun, gaussOperator_sub_smul hFlog (analyticAt_logSing a b n hz0) hHa,
    gaussOperator_mul_log hFa hs, gaussOperator_logSing hn ha hb hz0]
  have hnc : ∀ k : ℕ, (n : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have := congrArg re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  have hLF : gaussOperator a b n F z = 0 := by
    have := ordinaryHypergeometric_ode (a := a) (b := b) hnc hz hz0 hz1
    simpa [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero] using this
  rw [hLF]
  -- the series parts
  set f := gaussHGCoeff a b (n : ℂ) with hf
  have h0 := hFs.hasSum_mul_pow hzb
  have h1 := hFs.deriv_ofScalars.hasSum_mul_pow hzb
  have hz1' := hFs.hasSum_z_mul_deriv hzb
  have hsh : HasSum (fun k : ℕ => f (k + 1) * z ^ k) ((F z - 1) / z) := by
    have h0' := (hasSum_nat_add_iff' 1).mpr h0
    have hf0 : f 0 = 1 := by simp [hf, gaussHGCoeff, poch_zero]
    simp only [Finset.sum_range_one, pow_zero, mul_one, hf0] at h0'
    have h2 := h0'.mul_left z⁻¹
    convert h2 using 1
    · funext k; rw [pow_succ]; field_simp
    · field_simp; rfl
  have hLH := hH.hasSum_gaussOperator a b (n : ℂ) hzb
  have hall := ((((h1.mul_left 2).sub (hz1'.mul_left 2)).add (hsh.mul_left ((n : ℂ) - 1))).sub
    (h0.mul_left (a + b))).add hLH
  have hzero : (fun k : ℕ => 2 * ((k + 1) * f (k + 1) * z ^ k) - 2 * ((k : ℂ) * f k * z ^ k) +
      ((n : ℂ) - 1) * (f (k + 1) * z ^ k) - (a + b) * (f k * z ^ k) +
      ((k + 1) * ((n : ℂ) + k) * h (k + 1) - (k + a) * (k + b) * h k) * z ^ k) = fun _ => 0 := by
    funext k
    linear_combination z ^ k * hrec k
  rw [hzero] at hall
  have hval := hall.unique hasSum_zero
  rw [← hFdef] at hval
  field_simp at hval ⊢
  linear_combination hval

/-- Signed coefficients of the pole part `logSing`. -/
def logSingCoeff (a b : ℂ) (n j : ℕ) : ℂ :=
  ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
    (((n - j - 2).factorial : ℂ) * poch (1 - a) (j + 1) * poch (1 - b) (j + 1)) * (-1) ^ (j + 1)

/-- The pole part `logSing` written with the signed coefficients `logSingCoeff`. -/
theorem logSing_eq (a b : ℂ) (n : ℕ) (v : ℂ) :
    logSing a b n v = ∑ j ∈ Finset.range (n - 1), logSingCoeff a b n j * v⁻¹ ^ (j + 1) := by
  simp only [logSing, logSingCoeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inv_neg, neg_eq_neg_one_mul, mul_pow, inv_pow]
  ring

/-- Termwise derivative of the pole part `logSing` away from `0`. -/
theorem hasDerivAt_logSing (a b : ℂ) (n : ℕ) {v : ℂ} (hv : v ≠ 0) :
    HasDerivAt (logSing a b n)
      (∑ j ∈ Finset.range (n - 1), logSingCoeff a b n j * (-((j + 1 : ℕ) : ℂ) * v⁻¹ ^ (j + 2))) v := by
  have h : logSing a b n = fun v => ∑ j ∈ Finset.range (n - 1), logSingCoeff a b n j * v⁻¹ ^ (j + 1) :=
    funext (logSing_eq a b n)
  rw [h]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_recip_pow (j + 1) hv).const_mul _

/-- `z^n` times the pole part, a polynomial. -/
def logSingPoly0 (a b : ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n - 1), logSingCoeff a b n j * v ^ (n - j - 1)

/-- `z^n` times the derivative of the pole part, a polynomial. -/
def logSingPoly1 (a b : ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n - 1), logSingCoeff a b n j * (-((j + 1 : ℕ) : ℂ) * v ^ (n - j - 2))

/-- For `v ≠ 0` and `k ≤ n`, `vⁿ v⁻ᵏ = v^{n-k}`. -/
theorem pow_mul_recip_pow {v : ℂ} (hv : v ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    v ^ n * v⁻¹ ^ k = v ^ (n - k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, pow_add, inv_pow]
  field_simp

/-- `zⁿ` times the pole part is the polynomial `logSingPoly0`. -/
theorem pow_mul_logSing (a b : ℂ) (n : ℕ) {v : ℂ} (hv : v ≠ 0) :
    v ^ n * logSing a b n v = logSingPoly0 a b n v := by
  rw [logSing_eq, logSingPoly0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [mul_left_comm, pow_mul_recip_pow hv (by omega), show n - (j + 1) = n - j - 1 by omega]

/-- `zⁿ` times the derivative of the pole part is the polynomial `logSingPoly1`. -/
theorem pow_mul_deriv_logSing (a b : ℂ) (n : ℕ) {v : ℂ} (hv : v ≠ 0) :
    v ^ n * deriv (logSing a b n) v = logSingPoly1 a b n v := by
  rw [(hasDerivAt_logSing a b n hv).deriv, logSingPoly1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [show v ^ n * (logSingCoeff a b n j * (-((j + 1 : ℕ) : ℂ) * v⁻¹ ^ (j + 2))) =
      logSingCoeff a b n j * (-((j + 1 : ℕ) : ℂ) * (v ^ n * v⁻¹ ^ (j + 2))) by ring,
    pow_mul_recip_pow hv (by omega), show n - (j + 2) = n - j - 2 by omega]

/-- The polynomial `logSingPoly0` is entire. -/
theorem differentiable_logSingPoly0 (a b : ℂ) (n : ℕ) : Differentiable ℂ (logSingPoly0 a b n) := by
  unfold logSingPoly0
  fun_prop

/-- The polynomial `logSingPoly1` is entire. -/
theorem differentiable_logSingPoly1 (a b : ℂ) (n : ℕ) : Differentiable ℂ (logSingPoly1 a b n) := by
  unfold logSingPoly1
  fun_prop

/-- The leading coefficient of the pole part is nonzero when `n ≥ 2` and the Pochhammer factors do
  not vanish. -/
theorem logSingCoeff_ne_zero {a b : ℂ} {n : ℕ} (hn : 2 ≤ n)
    (ha : poch (1 - a) (n - 1) ≠ 0) (hb : poch (1 - b) (n - 1) ≠ 0) :
    logSingCoeff a b n (n - 2) ≠ 0 := by
  unfold logSingCoeff
  rw [show n - 2 + 1 = n - 1 by omega]
  have h1 : ((n - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((n - 2).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((n - (n - 2) - 2).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero (mul_ne_zero h3 ha) hb))
    (pow_ne_zero _ (by norm_num))

/-- The Wronskian of `₂F₁(a,b;n;z)` and a logarithmic solution does not vanish. -/
theorem wronskian_logSolution_ne_zero {a b : ℂ} {n : ℕ} (hn : 0 < n)
    (ha : poch (1 - a) (n - 1) ≠ 0) (hb : poch (1 - b) (n - 1) ≠ 0) {h : ℕ → ℂ} {H : ℂ → ℂ}
    (hH : HasFPowerSeriesOnBall H (ofScalars ℂ h) 0 1)
    (hrec : ∀ k : ℕ, (k + 1) * (n + k) * h (k + 1) - (k + a) * (k + b) * h k +
      2 * (k + 1) * gaussHGCoeff a b n (k + 1) - (2 * k + a + b) * gaussHGCoeff a b n k +
      (n - 1) * gaussHGCoeff a b n (k + 1) = 0)
    {z : ℂ} (hz : ‖z‖ < 1) (hs : z ∈ slitPlane) :
    solutionWronskian (₂F₁ a b (n : ℂ))
      (fun v => ₂F₁ a b (n : ℂ) v * log v - logSing a b n v + H v) z ≠ 0 := by
  set F : ℂ → ℂ := ₂F₁ a b (n : ℂ) with hFdef
  set w : ℂ → ℂ := fun v => F v * log v - logSing a b n v + H v with hw
  set U : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ slitPlane with hU
  have hUo : IsOpen U := Metric.isOpen_ball.inter isOpen_slitPlane
  have hFs := hasFPowerSeriesOnBall_ordinaryHypergeometric a b (n : ℂ)
  have hball : ∀ v ∈ Metric.ball (0 : ℂ) 1, ‖v‖ < 1 := fun v hv => by simpa using hv
  have hFa : ∀ v ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ F v := fun v hv =>
    hFs.analyticAt_of_mem (mem_eball_one_of_norm_lt_one (hball v hv))
  have hHa : ∀ v ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ H v := fun v hv =>
    hH.analyticAt_of_mem (mem_eball_one_of_norm_lt_one (hball v hv))
  have hwa : ∀ v ∈ U, AnalyticAt ℂ w v := fun v hv =>
    (((hFa v hv.1).mul (analyticAt_clog hv.2)).sub
      (analyticAt_logSing a b n (slitPlane_ne_zero hv.2))).add (hHa v hv.1)
  have hnc : ∀ k : ℕ, (n : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have := congrArg re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  have hodeF : ∀ v ∈ U, gaussOperator a b n F v = 0 := by
    intro v hv
    have hv1 : v ≠ 1 := by rintro rfl; simpa using hball _ hv.1
    have := ordinaryHypergeometric_ode (a := a) (b := b) hnc (hball v hv.1)
      (slitPlane_ne_zero hv.2) hv1
    simpa [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero] using this
  have hodew : ∀ v ∈ U, gaussOperator a b n w v = 0 := fun v hv =>
    gaussOperator_logSolution hn ha hb hH hrec (hball v hv.1) hv.2
  -- Abel's identity
  set W : ℂ → ℂ := solutionWronskian F w with hWdef
  have hWd : ∀ v ∈ U, HasDerivAt W (F v * deriv (deriv w) v - deriv (deriv F) v * w v) v := by
    intro v hv
    have h1 := (hFa v hv.1).differentiableAt.hasDerivAt
    have h2 := (hFa v hv.1).deriv.differentiableAt.hasDerivAt
    have h3 := (hwa v hv).differentiableAt.hasDerivAt
    have h4 := (hwa v hv).deriv.differentiableAt.hasDerivAt
    exact ((h1.mul h4).sub (h2.mul h3)).congr_deriv (by ring)
  have hAbel : ∀ v ∈ U, v * (1 - v) * (F v * deriv (deriv w) v - deriv (deriv F) v * w v) =
      -((n : ℂ) - (a + b + 1) * v) * W v := by
    intro v hv
    have e1 := hodeF v hv
    have e2 := hodew v hv
    simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero] at e1 e2
    simp only [hWdef, solutionWronskian]
    linear_combination F v * e2 - w v * e1
  -- the analytic factor
  set G : ℂ → ℂ := fun v => v ^ (n - 1) * F v ^ 2 +
    F v * (v ^ n * deriv H v - logSingPoly1 a b n v) -
    deriv F v * (v ^ n * H v - logSingPoly0 a b n v) with hG
  have hGW : ∀ v ∈ U, G v = v ^ n * W v := by
    intro v hv
    have hv0 := slitPlane_ne_zero hv.2
    have hdw : deriv w v = deriv F v * log v + F v * v⁻¹ - deriv (logSing a b n) v + deriv H v := by
      have := ((((hFa v hv.1).differentiableAt.hasDerivAt.mul (hasDerivAt_log hv.2)).sub
        (hasDerivAt_logSing a b n hv0)).add (hHa v hv.1).differentiableAt.hasDerivAt)
      rw [← (hasDerivAt_logSing a b n hv0).deriv] at this
      exact this.deriv
    have hP0 := pow_mul_logSing a b n hv0
    have hP1 := pow_mul_deriv_logSing a b n hv0
    have hvn : v ^ n * v⁻¹ = v ^ (n - 1) := by
      rw [← pow_mul_recip_pow hv0 (show 1 ≤ n by omega), pow_one]
    simp only [hG, hWdef, solutionWronskian]
    rw [hdw]
    simp only [hw]
    rw [← hP0, ← hP1]
    linear_combination (-(F v) ^ 2) * hvn
  -- `G (1 - v)^s` is constant on the disk
  set s : ℂ := a + b + 1 - n with hsdef
  clear_value s
  set K : ℂ → ℂ := fun v => G v * (1 - v) ^ s with hK
  have hslit1 : ∀ v ∈ Metric.ball (0 : ℂ) 1, 1 - v ∈ slitPlane := by
    intro v hv
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have := (re_le_norm v).trans_lt (hball v hv)
    simp only [sub_re, one_re]; linarith
  have hGa : ∀ v ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ G v := by
    intro v hv
    have hP0 : AnalyticAt ℂ (logSingPoly0 a b n) v :=
      (differentiable_logSingPoly0 a b n).analyticAt v
    have hP1 : AnalyticAt ℂ (logSingPoly1 a b n) v :=
      (differentiable_logSingPoly1 a b n).analyticAt v
    exact ((analyticAt_id.pow _).mul ((hFa v hv).pow 2)).add
      ((hFa v hv).mul (((analyticAt_id.pow _).mul (hHa v hv).deriv).sub hP1)) |>.sub
      ((hFa v hv).deriv.mul (((analyticAt_id.pow _).mul (hHa v hv)).sub hP0))
  have hKa : AnalyticOnNhd ℂ K (Metric.ball (0 : ℂ) 1) := fun v hv =>
    (hGa v hv).mul ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const (hslit1 v hv))
  have hKd0 : ∀ v ∈ U, deriv K v = 0 := by
    intro v hv
    have hv0 := slitPlane_ne_zero hv.2
    have hv1 : 1 - v ≠ 0 := slitPlane_ne_zero (hslit1 v hv.1)
    have hGev : G =ᶠ[𝓝 v] fun u => u ^ n * W u := by
      filter_upwards [hUo.mem_nhds hv] with u hu
      exact hGW u hu
    have hGd : HasDerivAt G ((n : ℂ) * v ^ (n - 1) * W v +
        v ^ n * (F v * deriv (deriv w) v - deriv (deriv F) v * w v)) v := by
      have := (hasDerivAt_pow n v).mul (hWd v hv)
      exact (this.congr_of_eventuallyEq hGev).congr_deriv (by ring)
    have hp := ((hasDerivAt_const v (1 : ℂ)).sub (hasDerivAt_id v)).cpow_const (c := s)
      (hslit1 v hv.1)
    have hKd : HasDerivAt K _ v := hGd.mul hp
    rw [hKd.deriv]
    simp only [_root_.id, Pi.sub_apply]
    rw [cpow_sub _ _ hv1, cpow_one]
    have hA := hAbel v hv
    have hGv := hGW v hv
    have hvn : v ^ n = v ^ (n - 1) * v := by
      rw [← pow_succ, show n - 1 + 1 = n by omega]
    rw [hvn] at hGv ⊢
    have hdi : (1 - v) * (1 - v)⁻¹ = 1 := mul_inv_cancel₀ hv1
    rw [div_eq_mul_inv]
    apply mul_left_cancel₀ hv1
    linear_combination (1 - v) ^ s * v ^ (n - 1) * hA - s * (1 - v) ^ s * hGv -
      (1 - v) ^ s * v ^ (n - 1) * v * W v * hsdef - G v * s * (1 - v) ^ s * hdi
  have hhalf : (1 / 2 : ℂ) ∈ U := ⟨by simp; norm_num, by
    refine mem_slitPlane_iff.mpr (Or.inl ?_); norm_num⟩
  have hev : deriv K =ᶠ[𝓝 (1 / 2 : ℂ)] 0 := by
    filter_upwards [hUo.mem_nhds hhalf] with v hv
    exact hKd0 v hv
  have hzero := hKa.deriv.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected hhalf.1 hev
  have hzb : z ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz
  have hKc := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    (fun v hv => (hKa v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => hzero hv) (x := z) (y := 0) hzb (by simp)
  have hK0 : K 0 = G 0 := by simp [hK]
  have hF0 : F 0 = 1 := by simp [hFdef, ordinaryHypergeometric_zero]
  have hP0 : logSingPoly0 a b n 0 = 0 := by
    unfold logSingPoly0
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [zero_pow (by omega), mul_zero]
  have h0n : (0 : ℂ) ^ n = 0 := zero_pow (by omega)
  have hG0 : G 0 ≠ 0 := by
    simp only [hG, hF0, h0n, hP0, zero_mul, zero_sub, sub_zero, mul_zero, one_pow, mul_one]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have : n = 1 := by omega
      subst this
      simp [logSingPoly1]
    · have hP1 : logSingPoly1 a b n 0 = logSingCoeff a b n (n - 2) * (-((n - 1 : ℕ) : ℂ)) := by
        unfold logSingPoly1
        rw [Finset.sum_eq_single (n - 2)]
        · rw [show n - 2 + 1 = n - 1 by omega, show n - (n - 2) - 2 = 0 by omega, pow_zero, mul_one]
        · intro j hj hjn
          rw [Finset.mem_range] at hj
          rw [zero_pow (by omega), mul_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      rw [hP1]
      have hc := logSingCoeff_ne_zero hn2 ha hb
      have hn1 : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [zero_pow (by omega)]
      simp only [zero_add, one_mul, mul_neg, neg_neg]
      exact mul_ne_zero hc hn1
  intro hW0
  have hGz : G z = 0 := by rw [hGW z ⟨hzb, hs⟩, hW0, mul_zero]
  have : K z = 0 := by simp [hK, hGz]
  rw [hKc, hK0] at this
  exact hG0 this

/-- The Gauss operator at `z` depends only on the germ of the function at `z`. -/
theorem gaussOperator_congr {a b c : ℂ} {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    gaussOperator a b c f z = gaussOperator a b c g z := by
  simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h.deriv.deriv_eq, h.deriv_eq, h.eq_of_nhds]

/-- The Wronskian at `z` depends only on the germ of the second function at `z`. -/
theorem solutionWronskian_congr {f g₁ g₂ : ℂ → ℂ} {z : ℂ} (h : g₁ =ᶠ[𝓝 z] g₂) :
    solutionWronskian f g₁ z = solutionWronskian f g₂ z := by
  simp only [solutionWronskian]
  rw [h.deriv_eq, h.eq_of_nhds]

/-- A coefficient sequence with `∑ ‖h k‖ r^k < ∞` for all `r < 1` has radius at least one. -/
theorem one_le_radius_ofScalars {h : ℕ → ℂ}
    (hs : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun k => ‖h k‖ * r ^ k) :
    1 ≤ (ofScalars ℂ h).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  refine (ofScalars ℂ h).le_radius_of_summable ?_
  have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
  refine (hs r r.2 hr').congr fun k => ?_
  rw [ofScalars_norm]

/-- Coefficients eventually of polynomial growth relative to a Gauss series give radius at
least one. -/
theorem one_le_radius_of_le_gaussHGCoeff {h : ℕ → ℂ} (a b c : ℂ) {C : ℝ} (N : ℕ)
    (hC : ∀ k, N ≤ k → ‖h k‖ ≤ C * (k + 1) * ‖gaussHGCoeff a b c k‖) :
    1 ≤ (ofScalars ℂ h).radius := by
  refine one_le_radius_ofScalars fun r hr0 hr1 => ?_
  set r' : ℝ := (1 + r) / 2 with hr'
  have hr'0 : 0 < r' := by rw [hr']; linarith
  have hr'1 : r' < 1 := by rw [hr']; linarith
  have hsum := summable_norm_gaussHGCoeff_mul_pow a b c (z := (r' : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr'0]; exact hr'1)
  set M := ∑' k, ‖gaussHGCoeff a b c k * (r' : ℂ) ^ k‖
  have hM : ∀ k, ‖gaussHGCoeff a b c k‖ * r' ^ k ≤ M := by
    intro k
    have := hsum.le_tsum k (fun j _ => norm_nonneg _)
    rwa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr'0] at this
  set q := r / r' with hq
  have hq0 : 0 ≤ q := div_nonneg hr0 hr'0.le
  have hq1 : q < 1 := by rw [hq, div_lt_one hr'0, hr']; linarith
  have hgeom : Summable fun k : ℕ => ((k : ℝ) + 1) * q ^ k := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
    have h2 := summable_geometric_of_lt_one hq0 hq1
    refine (h1.add h2).congr fun k => ?_
    simp
    ring
  have hgeom' := (summable_nat_add_iff N).mpr hgeom
  refine (summable_nat_add_iff N).mp ?_
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((hgeom'.mul_left (|C| * M)))
  have hk := hC (k + N) (by omega)
  have hrk : r ^ (k + N) = q ^ (k + N) * r' ^ (k + N) := by
    rw [hq, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hr'0.ne')]
  rw [hrk]
  push_cast at hk ⊢
  calc ‖h (k + N)‖ * (q ^ (k + N) * r' ^ (k + N))
      ≤ C * ((k : ℝ) + N + 1) * ‖gaussHGCoeff a b c (k + N)‖ * (q ^ (k + N) * r' ^ (k + N)) := by
        gcongr
    _ = C * ((k : ℝ) + N + 1) * q ^ (k + N) * (‖gaussHGCoeff a b c (k + N)‖ * r' ^ (k + N)) := by
        ring
    _ ≤ |C| * ((k : ℝ) + N + 1) * q ^ (k + N) * M := by
        calc C * ((k : ℝ) + N + 1) * q ^ (k + N) * (‖gaussHGCoeff a b c (k + N)‖ * r' ^ (k + N))
            ≤ |C| * ((k : ℝ) + N + 1) * q ^ (k + N) *
                (‖gaussHGCoeff a b c (k + N)‖ * r' ^ (k + N)) := by
              gcongr; exact le_abs_self C
          _ ≤ |C| * ((k : ℝ) + N + 1) * q ^ (k + N) * M := by gcongr; exact hM _
    _ = |C| * M * (((k : ℝ) + N + 1) * q ^ (k + N)) := by ring

/-- Linear growth of `ψ(x + k)`. -/
theorem exists_norm_digamma_add_nat_le {x : ℂ} (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    ∃ C : ℝ, ∀ k : ℕ, ‖digamma (x + k)‖ ≤ C * (k + 1) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖x‖ + 1 ≤ N := exists_nat_ge _
  set M : ℝ := 1 + ∑ j ∈ Finset.range N, ‖(x + j)⁻¹‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hb : ∀ j : ℕ, ‖(x + j)⁻¹‖ ≤ M := by
    intro j
    rcases Nat.lt_or_ge j N with hj | hj
    · have := Finset.single_le_sum (f := fun j : ℕ => ‖(x + j)⁻¹‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr hj)
      linarith
    · have hj' : (N : ℝ) ≤ j := by exact_mod_cast hj
      have h1 : 1 ≤ ‖x + j‖ := by
        have := norm_sub_norm_le ((j : ℂ)) (-x)
        rw [Complex.norm_natCast, norm_neg, sub_neg_eq_add, add_comm] at this
        linarith
      rw [norm_inv]
      have := inv_le_one_of_one_le₀ h1
      have : 0 ≤ ∑ j ∈ Finset.range N, ‖(x + j)⁻¹‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      linarith
  refine ⟨‖digamma x‖ + M, fun k => ?_⟩
  rw [digamma_apply_add_nat hx k]
  calc ‖digamma x + ∑ j ∈ Finset.range k, (x + j)⁻¹‖
      ≤ ‖digamma x‖ + ∑ j ∈ Finset.range k, ‖(x + j)⁻¹‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
    _ ≤ ‖digamma x‖ + k * M := by
        gcongr
        calc ∑ j ∈ Finset.range k, ‖(x + j)⁻¹‖ ≤ ∑ _j ∈ Finset.range k, M :=
              Finset.sum_le_sum fun j _ => hb j
          _ = k * M := by simp
    _ ≤ (‖digamma x‖ + M) * (k + 1) := by
        have : 0 ≤ ‖digamma x‖ := norm_nonneg _
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith

/-- A complex number that is not an integer is not a nonpositive integer. -/
theorem not_neg_nat_of_not_int {c : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ)) : ∀ k : ℕ, c ≠ -(k : ℂ) := by
  intro k h
  exact hc (-(k : ℤ)) (by rw [h]; push_cast; ring)

/-- A positive natural number is not a nonpositive integer. -/
theorem natCast_not_neg_nat {n : ℕ} (hn : 0 < n) : ∀ k : ℕ, (n : ℂ) ≠ -(k : ℂ) := by
  intro k hk
  have := congrArg re hk
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]

/-- The power series part is analytic on the unit disk, given a radius bound. -/
theorem hasFPowerSeriesOnBall_ofScalars_sum {h : ℕ → ℂ} (hr : 1 ≤ (ofScalars ℂ h).radius) :
    HasFPowerSeriesOnBall (ofScalars ℂ h).sum (ofScalars ℂ h) 0 1 :=
  ((ofScalars ℂ h).hasFPowerSeriesOnBall (lt_of_lt_of_le one_pos hr)).mono one_pos hr

/-- Identity under the stated parameter and domain assumptions: `gaussOperator a b n
(logarithmicSecond a b n) z = 0 ∧ solutionWronskian (₂F₁ a b (n : ℂ)) (logarithmicSecond a b
n) z ≠ 0`. -/
@[dlmf 15.10.E8]
theorem logarithmic_second_fundamental
    {a b : ℂ}
    (n : ℕ)
    (hn : 0 < n)
    (ha : ∀ k : ℤ, a ≠
    (k : ℂ))
    (hb : ∀ k : ℤ, b ≠
    (k : ℂ))
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator a b n (logarithmicSecond a b n) z = 0 ∧
      solutionWronskian (₂F₁ a b (n : ℂ)) (logarithmicSecond a b n) z ≠ 0 := by
  have ha' := not_neg_nat_of_not_int ha
  have hb' := not_neg_nat_of_not_int hb
  have hnc := natCast_not_neg_nat hn
  have h1c : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := fun m => by
    simpa using natCast_not_neg_nat (n := 1) one_pos m
  set δ : ℕ → ℂ := fun k => digamma (a + k) + digamma (b + k) - digamma (1 + k) - digamma (n + k)
    with hδ
  set h : ℕ → ℂ := fun k => gaussHGCoeff a b n k * δ k with hh
  obtain ⟨Ca, hCa⟩ := exists_norm_digamma_add_nat_le ha'
  obtain ⟨Cb, hCb⟩ := exists_norm_digamma_add_nat_le hb'
  obtain ⟨C1, hC1⟩ := exists_norm_digamma_add_nat_le h1c
  obtain ⟨Cn, hCn⟩ := exists_norm_digamma_add_nat_le hnc
  have hr : 1 ≤ (ofScalars ℂ h).radius := by
    refine one_le_radius_of_le_gaussHGCoeff a b n (C := Ca + Cb + C1 + Cn) 0 fun k _ => ?_
    simp only [hh, hδ, norm_mul]
    have : ‖digamma (a + k) + digamma (b + k) - digamma (1 + k) - digamma (n + k)‖ ≤
        (Ca + Cb + C1 + Cn) * (k + 1) := by
      calc ‖digamma (a + k) + digamma (b + k) - digamma (1 + k) - digamma (n + k)‖
          ≤ ‖digamma (a + k) + digamma (b + k) - digamma (1 + k)‖ + ‖digamma (n + k)‖ :=
            norm_sub_le _ _
        _ ≤ ‖digamma (a + k) + digamma (b + k)‖ + ‖digamma (1 + k)‖ + ‖digamma (n + k)‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ ‖digamma (a + k)‖ + ‖digamma (b + k)‖ + ‖digamma (1 + k)‖ + ‖digamma (n + k)‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ Ca * (k + 1) + Cb * (k + 1) + C1 * (k + 1) + Cn * (k + 1) := by
            gcongr
            · exact hCa k
            · exact hCb k
            · exact hC1 k
            · exact hCn k
        _ = _ := by ring
    calc ‖gaussHGCoeff a b n k‖ * ‖digamma (a + k) + digamma (b + k) - digamma (1 + k) -
          digamma (n + k)‖ ≤ ‖gaussHGCoeff a b n k‖ * ((Ca + Cb + C1 + Cn) * (k + 1)) := by
          gcongr
      _ = _ := by ring
  have hH := hasFPowerSeriesOnBall_ofScalars_sum hr
  set H := (ofScalars ℂ h).sum with hHdef
  have hrec : ∀ k : ℕ, (k + 1) * (n + k) * h (k + 1) - (k + a) * (k + b) * h k +
      2 * (k + 1) * gaussHGCoeff a b n (k + 1) - (2 * k + a + b) * gaussHGCoeff a b n k +
      (n - 1) * gaussHGCoeff a b n (k + 1) = 0 := by
    intro k
    have hrec0 := gaussHGCoeff_recurrence (a := a) (b := b) hnc k
    have hk : ∀ x : ℂ, (∀ m : ℕ, x ≠ -(m : ℂ)) →
        digamma (x + ((k + 1 : ℕ) : ℂ)) = digamma (x + k) + (x + k)⁻¹ := by
      intro x hx
      rw [show x + ((k + 1 : ℕ) : ℂ) = (x + k) + 1 by push_cast; ring]
      exact digamma_apply_add_one _ (not_neg_nat_add_nat hx k)
    have hne : ∀ x : ℂ, (∀ m : ℕ, x ≠ -(m : ℂ)) → (x + k) * (x + k)⁻¹ = 1 := fun x hx =>
      mul_inv_cancel₀ (by simpa using not_neg_nat_add_nat hx k 0)
    simp only [hh, hδ]
    rw [hk a ha', hk b hb', hk 1 h1c, hk n hnc]
    linear_combination (digamma (a + k) + digamma (b + k) - digamma (1 + k) - digamma (n + k) +
        (a + k)⁻¹ + (b + k)⁻¹) * hrec0 +
      (b + k) * gaussHGCoeff a b n k * hne a ha' + (a + k) * gaussHGCoeff a b n k * hne b hb' -
      (n + k) * gaussHGCoeff a b n (k + 1) * hne 1 h1c -
      (k + 1) * gaussHGCoeff a b n (k + 1) * hne n hnc
  have hpa : poch (1 - a) (n - 1) ≠ 0 := poch_ne_zero_of_not_neg_nat
    (fun k hk => ha (k + 1) (by push_cast; linear_combination -hk)) _
  have hpb : poch (1 - b) (n - 1) ≠ 0 := poch_ne_zero_of_not_neg_nat
    (fun k hk => hb (k + 1) (by push_cast; linear_combination -hk)) _
  have hev : logarithmicSecond a b n =ᶠ[𝓝 z]
      fun v => ₂F₁ a b (n : ℂ) v * log v - logSing a b n v + H v := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball (0 : ℂ) 1 by simpa using hz)]
      with v hv
    have hv' : v ∈ Metric.eball (0 : ℂ) 1 := mem_eball_one_of_norm_lt_one (by simpa using hv)
    rw [logarithmicSecond, ← (hH.hasSum_mul_pow hv').tsum_eq]
    congr 1
    refine tsum_congr fun k => ?_
    simp only [hh, hδ]
    ring
  refine ⟨?_, ?_⟩
  · rw [gaussOperator_congr hev]
    exact gaussOperator_logSolution hn hpa hpb hH hrec hz hs
  · rw [solutionWronskian_congr hev]
    exact wronskian_logSolution_ne_zero hn hpa hpb hH hrec hz hs

/-- For a positive integer `n`, `k! ≤ ‖(n)ₖ‖`. -/
theorem factorial_le_norm_poch_natCast {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (k.factorial : ℝ) ≤ ‖poch (n : ℂ) k‖ :=
  factorial_le_norm_ascPochhammer_eval (by simp; exact_mod_cast hn) k

/-- Identity under the stated parameter and domain assumptions: `gaussOperator (-m) b n
(logarithmicSecondTerminating b m n) z = 0 ∧ solutionWronskian (₂F₁ (-m : ℂ) b (n : ℂ))
(logarithmicSecondTerminating b m n) z ≠ 0`. -/
@[dlmf 15.10.E9]
theorem logarithmic_second_terminating_fundamental
    {b : ℂ}
    (m n : ℕ)
    (hn : 0 < n)
    (hb : ∀ k : ℤ, b ≠
    (k : ℂ))
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator (-m) b n (logarithmicSecondTerminating b m n) z = 0 ∧
      solutionWronskian (₂F₁ (-m : ℂ) b (n : ℂ)) (logarithmicSecondTerminating b m n) z ≠ 0 := by
  have hb' := not_neg_nat_of_not_int hb
  have hnc := natCast_not_neg_nat hn
  have h1c : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := fun m => by
    simpa using natCast_not_neg_nat (n := 1) one_pos m
  set f : ℕ → ℂ := gaussHGCoeff (-(m : ℂ)) b n with hf
  set δ : ℕ → ℂ := fun k => digamma (1 + m - k) + digamma (b + k) - digamma (1 + k) -
    digamma (n + k) with hδ
  set h : ℕ → ℂ := fun k => if k ≤ m then f k * δ k else
    (-1) ^ m * (m.factorial : ℂ) * ((k - m - 1).factorial : ℂ) * poch b k /
      (poch n k * (k.factorial : ℂ)) with hh
  have hf0 : ∀ k, m < k → f k = 0 := fun k hk => by
    simp only [hf, gaussHGCoeff, poch_neg_nat_eq_zero hk, zero_mul, zero_div]
  have hr : 1 ≤ (ofScalars ℂ h).radius := by
    refine one_le_radius_of_le_gaussHGCoeff b 1 1 (C := m.factorial) (m + 1) fun k hk => ?_
    have hkm : ¬ k ≤ m := by omega
    simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h hkm)]
    have hfk : (0 : ℝ) < k.factorial := by positivity
    have hpn := factorial_le_norm_poch_natCast hn k
    have hkf : (((k - m - 1).factorial : ℕ) : ℝ) ≤ k.factorial :=
      by exact_mod_cast Nat.factorial_le (by omega)
    rw [gaussHGCoeff_self_right]
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
    have hQ : (0 : ℝ) < ‖poch (n : ℂ) k‖ := lt_of_lt_of_le hfk hpn
    rw [div_le_iff₀ (mul_pos hQ hfk)]
    have e : (m.factorial : ℝ) * (k + 1) * (‖poch b k‖ / k.factorial) * (‖poch (n : ℂ) k‖ * k.factorial)
        = m.factorial * ‖poch b k‖ * ((k + 1) * ‖poch (n : ℂ) k‖) := by
      field_simp
    rw [e]
    have h1 : (k.factorial : ℝ) ≤ (k + 1) * ‖poch (n : ℂ) k‖ := by
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h2 : (0 : ℝ) ≤ m.factorial * ‖poch b k‖ := by positivity
    calc (m.factorial : ℝ) * ((k - m - 1).factorial : ℝ) * ‖poch b k‖
        ≤ m.factorial * k.factorial * ‖poch b k‖ := by gcongr
      _ = m.factorial * ‖poch b k‖ * k.factorial := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  have hH := hasFPowerSeriesOnBall_ofScalars_sum hr
  set H := (ofScalars ℂ h).sum with hHdef
  have hrec : ∀ k : ℕ, (k + 1) * (n + k) * h (k + 1) - (k + -(m : ℂ)) * (k + b) * h k +
      2 * (k + 1) * f (k + 1) - (2 * k + -(m : ℂ) + b) * f k + (n - 1) * f (k + 1) = 0 := by
    intro k
    have hrec0 := gaussHGCoeff_recurrence (a := -(m : ℂ)) (b := b) hnc k
    rw [← hf] at hrec0
    rcases Nat.lt_trichotomy k m with hkm | rfl | hkm
    · -- both coefficients come from the finite part
      have hk1 : k + 1 ≤ m := hkm
      simp only [hh, ite_eq_left_iff.mpr (fun h => absurd hk1 h),
        ite_eq_left_iff.mpr (fun h => absurd hkm.le h), hδ]
      have hshift : ∀ x : ℂ, (∀ j : ℕ, x ≠ -(j : ℂ)) →
          digamma (x + ((k + 1 : ℕ) : ℂ)) = digamma (x + k) + (x + k)⁻¹ := by
        intro x hx
        rw [show x + ((k + 1 : ℕ) : ℂ) = (x + k) + 1 by push_cast; ring]
        exact digamma_apply_add_one _ (not_neg_nat_add_nat hx k)
      have hne : ∀ x : ℂ, (∀ j : ℕ, x ≠ -(j : ℂ)) → (x + k) * (x + k)⁻¹ = 1 := fun x hx =>
        mul_inv_cancel₀ (by simpa using not_neg_nat_add_nat hx k 0)
      have hxpos : ∀ j : ℕ, ((m - k - 1 : ℕ) : ℂ) + 1 ≠ -(j : ℂ) := by
        intro j hj
        have := congrArg re hj
        simp at this
        linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg (m - k - 1) : (0 : ℝ) ≤ _)]
      have hmk : ((m - k - 1 : ℕ) : ℂ) + 1 = (m : ℂ) - k := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      have hdm : digamma (1 + m - k) = digamma (1 + m - ((k + 1 : ℕ) : ℂ)) + ((m : ℂ) - k)⁻¹ := by
        rw [show (1 : ℂ) + m - ((k + 1 : ℕ) : ℂ) = ((m - k - 1 : ℕ) : ℂ) + 1 by rw [hmk]; push_cast; ring,
          show (1 : ℂ) + m - k = ((m - k - 1 : ℕ) : ℂ) + 1 + 1 by rw [hmk]; ring,
          digamma_apply_add_one _ hxpos, hmk]
      have hx : ((m : ℂ) - k) * ((m : ℂ) - k)⁻¹ = 1 :=
        mul_inv_cancel₀ (by rw [← hmk]; simpa using hxpos 0)
      rw [hshift b hb', hshift 1 h1c, hshift n hnc,
        show digamma (1 + m - ((k + 1 : ℕ) : ℂ)) = digamma (1 + m - k) - ((m : ℂ) - k)⁻¹ by
          rw [hdm]; ring]
      linear_combination (digamma (1 + m - k) + digamma (b + k) - digamma (1 + k) - digamma (n + k) -
          ((m : ℂ) - k)⁻¹ + (b + k)⁻¹) * hrec0 +
        (b + k) * f k * hx + (-(m : ℂ) + k) * f k * hne b hb' -
        (n + k) * f (k + 1) * hne 1 h1c - (k + 1) * f (k + 1) * hne n hnc
    · -- the transition `k = m`
      simp only [hh, ite_eq_left_iff.mpr (fun h => absurd le_rfl h), ite_eq_right_iff.mpr (fun h => absurd h (by omega : ¬ k + 1 ≤ k)),
        hf0 (k + 1) (by omega), show k + 1 - k - 1 = 0 by omega, Nat.factorial_zero]
      have hfm : f k = (-1) ^ k * poch b k / poch (n : ℂ) k := by
        rw [hf, gaussHGCoeff_neg_nat, Nat.choose_self]; simp
      rw [hfm, poch_succ b k, poch_succ (n : ℂ) k, Nat.factorial_succ]
      have hpn : poch (n : ℂ) k ≠ 0 := poch_ne_zero_of_not_neg_nat hnc k
      have hnk : (n : ℂ) + k ≠ 0 := by simpa using not_neg_nat_add_nat hnc k 0
      have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
      push_cast
      field_simp
      ring
    · -- both coefficients come from the series part
      have hk1 : ¬ k + 1 ≤ m := by omega
      have hk : ¬ k ≤ m := by omega
      simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h hk1),
        ite_eq_right_iff.mpr (fun h => absurd h hk), hf0 k hkm, hf0 (k + 1) (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, k = m + 1 + j := ⟨k - m - 1, by omega⟩
      rw [show m + 1 + j + 1 - m - 1 = j + 1 by omega, show m + 1 + j - m - 1 = j by omega,
        poch_succ b, poch_succ (n : ℂ), Nat.factorial_succ (m + 1 + j), Nat.factorial_succ j]
      have hpn : poch (n : ℂ) (m + 1 + j) ≠ 0 := poch_ne_zero_of_not_neg_nat hnc _
      have hnk : (n : ℂ) + ((m + 1 + j : ℕ) : ℂ) ≠ 0 := by
        simpa using not_neg_nat_add_nat hnc (m + 1 + j) 0
      have hkf : ((m + 1 + j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : ((m + 1 + j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at hnk h2 ⊢
      field_simp
      ring
  have hpa : poch (1 - -(m : ℂ)) (n - 1) ≠ 0 := by
    refine poch_ne_zero_of_not_neg_nat (fun k hk => ?_) _
    have := congrArg re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hpb : poch (1 - b) (n - 1) ≠ 0 := poch_ne_zero_of_not_neg_nat
    (fun k hk => hb (k + 1) (by push_cast; linear_combination -hk)) _
  have hev : logarithmicSecondTerminating b m n =ᶠ[𝓝 z]
      fun v => ₂F₁ (-(m : ℂ)) b (n : ℂ) v * log v - logSing (-(m : ℂ)) b n v + H v := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball (0 : ℂ) 1 by simpa using hz)]
      with v hv
    have hv' : v ∈ Metric.eball (0 : ℂ) 1 := mem_eball_one_of_norm_lt_one (by simpa using hv)
    have hsum := hH.hasSum_mul_pow hv'
    rw [← hsum.tsum_eq, ← hsum.summable.sum_add_tsum_nat_add (m + 1)]
    have hS : logSing (-(m : ℂ)) b n v = ∑ j ∈ Finset.range (n - 1),
        ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
          (((n - j - 2).factorial : ℂ) * poch (m + 1) (j + 1) * poch (1 - b) (j + 1)) *
            ((-v)⁻¹) ^ (j + 1) := by
      simp only [logSing, show (1 : ℂ) - -(m : ℂ) = m + 1 by ring]
    have hP : ∑ k ∈ Finset.range (m + 1), h k * v ^ k =
        ∑ k ∈ Finset.range (m + 1), gaussHGCoeff (-m) b n k * v ^ k *
          (digamma (1 + m - k) + digamma (b + k) - digamma (1 + k) - digamma (n + k)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp only [hh, ite_eq_left_iff.mpr (fun h => absurd (Nat.lt_succ_iff.mp hk) h), hδ, hf]
      ring
    have hT : ∑' j : ℕ, h (j + (m + 1)) * v ^ (j + (m + 1)) =
        (-1 : ℂ) ^ m * (m.factorial : ℂ) * ∑' j : ℕ,
          (j.factorial : ℂ) * poch b (m + 1 + j) /
            (poch n (m + 1 + j) * ((m + 1 + j).factorial : ℂ)) * v ^ (m + 1 + j) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun j => ?_
      rw [show j + (m + 1) = m + 1 + j by omega]
      simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h (by omega : ¬ m + 1 + j ≤ m)),
        show m + 1 + j - m - 1 = j by omega]
      ring
    rw [logarithmicSecondTerminating, hS, hP, hT]
    ring
  refine ⟨?_, ?_⟩
  · rw [gaussOperator_congr hev]
    exact gaussOperator_logSolution hn hpa hpb hH hrec hz hs
  · rw [solutionWronskian_congr hev]
    exact wronskian_logSolution_ne_zero hn hpa hpb hH hrec hz hs

/-- `ψ(1 + p - (k+1)) = ψ(1 + p - k) - (p - k)⁻¹` for `k < p`. -/
theorem digamma_one_add_sub_succ {p k : ℕ} (hk : k < p) :
    digamma (1 + p - ((k + 1 : ℕ) : ℂ)) = digamma (1 + p - k) - ((p : ℂ) - k)⁻¹ ∧
      ((p : ℂ) - k) * ((p : ℂ) - k)⁻¹ = 1 := by
  have hxpos : ∀ j : ℕ, ((p - k - 1 : ℕ) : ℂ) + 1 ≠ -(j : ℂ) := by
    intro j hj
    have := congrArg re hj
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg (p - k - 1) : (0 : ℝ) ≤ _)]
  have hmk : ((p - k - 1 : ℕ) : ℂ) + 1 = (p : ℂ) - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  refine ⟨?_, mul_inv_cancel₀ (by rw [← hmk]; simpa using hxpos 0)⟩
  rw [show (1 : ℂ) + p - ((k + 1 : ℕ) : ℂ) = ((p - k - 1 : ℕ) : ℂ) + 1 by rw [hmk]; push_cast; ring,
    show (1 : ℂ) + p - k = ((p - k - 1 : ℕ) : ℂ) + 1 + 1 by rw [hmk]; ring,
    digamma_apply_add_one _ hxpos, hmk]
  ring

/-- Identity under the stated parameter and domain assumptions: `gaussOperator (-m) (-l) n
(logarithmicSecondBothTerminating m l n) z = 0 ∧ solutionWronskian (₂F₁ (-m : ℂ) (-l : ℂ) (n :
ℂ)) (logarithmicSecondBothTerminating m l n) z ≠ 0`. -/
@[dlmf 15.10.E10]
theorem logarithmic_second_both_terminating_fundamental
    (m l n : ℕ)
    (hn : 0 < n)
    (hl : l ≤ m)
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator (-m) (-l) n (logarithmicSecondBothTerminating m l n) z = 0 ∧
      solutionWronskian (₂F₁ (-m : ℂ) (-l : ℂ) (n : ℂ)) (logarithmicSecondBothTerminating m l n) z ≠ 0 := by
  have hnc := natCast_not_neg_nat hn
  have h1c : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := fun m => by
    simpa using natCast_not_neg_nat (n := 1) one_pos m
  set f : ℕ → ℂ := gaussHGCoeff (-(m : ℂ)) (-(l : ℂ)) n with hf
  set δ : ℕ → ℂ := fun k => digamma (1 + m - k) + digamma (1 + l - k) - digamma (1 + k) -
    digamma (n + k) with hδ
  set h : ℕ → ℂ := fun k => if k ≤ l then f k * δ k else
    (-1) ^ l * (l.factorial : ℂ) * ((k - l - 1).factorial : ℂ) * poch (-(m : ℂ)) k /
      (poch n k * (k.factorial : ℂ)) with hh
  have hf0 : ∀ k, l < k → f k = 0 := fun k hk => by
    simp only [hf, gaussHGCoeff, poch_neg_nat_eq_zero hk, mul_zero, zero_div]
  have hh0 : ∀ k, m < k → h k = 0 := fun k hk => by
    simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h (by omega : ¬ k ≤ l)),
      poch_neg_nat_eq_zero hk, mul_zero, zero_div]
  have hr : 1 ≤ (ofScalars ℂ h).radius :=
    one_le_radius_of_le_gaussHGCoeff 1 1 1 (C := 0) (m + 1) fun k hk => by
      rw [hh0 k (by omega)]; simp
  have hH := hasFPowerSeriesOnBall_ofScalars_sum hr
  set H := (ofScalars ℂ h).sum with hHdef
  have hrec : ∀ k : ℕ, (k + 1) * (n + k) * h (k + 1) - (k + -(m : ℂ)) * (k + -(l : ℂ)) * h k +
      2 * (k + 1) * f (k + 1) - (2 * k + -(m : ℂ) + -(l : ℂ)) * f k + (n - 1) * f (k + 1) = 0 := by
    intro k
    have hrec0 := gaussHGCoeff_recurrence (a := -(m : ℂ)) (b := -(l : ℂ)) hnc k
    rw [← hf] at hrec0
    rcases Nat.lt_trichotomy k l with hkl | rfl | hkl
    · have hk1 : k + 1 ≤ l := hkl
      simp only [hh, ite_eq_left_iff.mpr (fun h => absurd hk1 h),
        ite_eq_left_iff.mpr (fun h => absurd hkl.le h), hδ]
      have hshift : ∀ x : ℂ, (∀ j : ℕ, x ≠ -(j : ℂ)) →
          digamma (x + ((k + 1 : ℕ) : ℂ)) = digamma (x + k) + (x + k)⁻¹ := by
        intro x hx
        rw [show x + ((k + 1 : ℕ) : ℂ) = (x + k) + 1 by push_cast; ring]
        exact digamma_apply_add_one _ (not_neg_nat_add_nat hx k)
      have hne : ∀ x : ℂ, (∀ j : ℕ, x ≠ -(j : ℂ)) → (x + k) * (x + k)⁻¹ = 1 := fun x hx =>
        mul_inv_cancel₀ (by simpa using not_neg_nat_add_nat hx k 0)
      obtain ⟨hdm, hxm⟩ := digamma_one_add_sub_succ (show k < m by omega)
      obtain ⟨hdl, hxl⟩ := digamma_one_add_sub_succ hkl
      rw [hshift 1 h1c, hshift n hnc, hdm, hdl]
      linear_combination (digamma (1 + m - k) + digamma (1 + l - k) - digamma (1 + k) -
          digamma (n + k) - ((m : ℂ) - k)⁻¹ - ((l : ℂ) - k)⁻¹) * hrec0 +
        (-(l : ℂ) + k) * f k * hxm + (-(m : ℂ) + k) * f k * hxl -
        (n + k) * f (k + 1) * hne 1 h1c - (k + 1) * f (k + 1) * hne n hnc
    · simp only [hh, ite_eq_left_iff.mpr (fun h => absurd le_rfl h),
        ite_eq_right_iff.mpr (fun h => absurd h (by omega : ¬ k + 1 ≤ k)),
        hf0 (k + 1) (by omega), show k + 1 - k - 1 = 0 by omega, Nat.factorial_zero]
      have hfm : f k = (-1) ^ k * poch (-(m : ℂ)) k / poch (n : ℂ) k := by
        have : f k = gaussHGCoeff (-(k : ℂ)) (-(m : ℂ)) n k := by
          simp only [hf, gaussHGCoeff]; ring
        rw [this, gaussHGCoeff_neg_nat, Nat.choose_self]; simp
      rw [hfm, poch_succ (-(m : ℂ)) k, poch_succ (n : ℂ) k, Nat.factorial_succ]
      have hpn : poch (n : ℂ) k ≠ 0 := poch_ne_zero_of_not_neg_nat hnc k
      have hnk : (n : ℂ) + k ≠ 0 := by simpa using not_neg_nat_add_nat hnc k 0
      have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
      push_cast
      field_simp
      ring
    · have hk1 : ¬ k + 1 ≤ l := by omega
      have hk : ¬ k ≤ l := by omega
      simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h hk1),
        ite_eq_right_iff.mpr (fun h => absurd h hk), hf0 k hkl, hf0 (k + 1) (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, k = l + 1 + j := ⟨k - l - 1, by omega⟩
      rw [show l + 1 + j + 1 - l - 1 = j + 1 by omega, show l + 1 + j - l - 1 = j by omega,
        poch_succ (-(m : ℂ)), poch_succ (n : ℂ), Nat.factorial_succ (l + 1 + j), Nat.factorial_succ j]
      have hpn : poch (n : ℂ) (l + 1 + j) ≠ 0 := poch_ne_zero_of_not_neg_nat hnc _
      have hnk : (n : ℂ) + ((l + 1 + j : ℕ) : ℂ) ≠ 0 := by
        simpa using not_neg_nat_add_nat hnc (l + 1 + j) 0
      have hkf : ((l + 1 + j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : ((l + 1 + j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at hnk h2 ⊢
      field_simp
      ring
  have hpos : ∀ p : ℕ, poch (1 - -(p : ℂ)) (n - 1) ≠ 0 := by
    intro p
    refine poch_ne_zero_of_not_neg_nat (fun k hk => ?_) _
    have := congrArg re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hev : logarithmicSecondBothTerminating m l n =ᶠ[𝓝 z]
      fun v => ₂F₁ (-(m : ℂ)) (-(l : ℂ)) (n : ℂ) v * log v - logSing (-(m : ℂ)) (-(l : ℂ)) n v +
        H v := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball (0 : ℂ) 1 by simpa using hz)]
      with v hv
    have hv' : v ∈ Metric.eball (0 : ℂ) 1 := mem_eball_one_of_norm_lt_one (by simpa using hv)
    have hsum := hH.hasSum_mul_pow hv'
    rw [← hsum.tsum_eq, ← hsum.summable.sum_add_tsum_nat_add (l + 1)]
    have hS : logSing (-(m : ℂ)) (-(l : ℂ)) n v = ∑ j ∈ Finset.range (n - 1),
        ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
          (((n - j - 2).factorial : ℂ) * poch (m + 1) (j + 1) * poch (l + 1) (j + 1)) *
            ((-v)⁻¹) ^ (j + 1) := by
      simp only [logSing, show (1 : ℂ) - -(m : ℂ) = m + 1 by ring,
        show (1 : ℂ) - -(l : ℂ) = l + 1 by ring]
    have hP : ∑ k ∈ Finset.range (l + 1), h k * v ^ k =
        ∑ k ∈ Finset.range (l + 1), gaussHGCoeff (-m) (-l) n k * v ^ k *
          (digamma (1 + m - k) + digamma (1 + l - k) - digamma (1 + k) - digamma (n + k)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp only [hh, ite_eq_left_iff.mpr (fun h => absurd (Nat.lt_succ_iff.mp hk) h), hδ, hf]
      ring
    have hT : ∑' j : ℕ, h (j + (l + 1)) * v ^ (j + (l + 1)) =
        (-1 : ℂ) ^ l * (l.factorial : ℂ) * ∑ j ∈ Finset.range (m - l),
          (j.factorial : ℂ) * poch (-m) (l + 1 + j) /
            (poch n (l + 1 + j) * ((l + 1 + j).factorial : ℂ)) * v ^ (l + 1 + j) := by
      rw [tsum_eq_sum (s := Finset.range (m - l)), Finset.mul_sum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [show j + (l + 1) = l + 1 + j by omega]
        simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h (by omega : ¬ l + 1 + j ≤ l)),
          show l + 1 + j - l - 1 = j by omega]
        ring
      · intro j hj
        rw [Finset.mem_range] at hj
        rw [hh0 _ (by omega), zero_mul]
    rw [logarithmicSecondBothTerminating, hS, hP, hT]
    ring
  refine ⟨?_, ?_⟩
  · rw [gaussOperator_congr hev]
    exact gaussOperator_logSolution hn (hpos m) (hpos l) hH hrec hz hs
  · rw [solutionWronskian_congr hev]
    exact wronskian_logSolution_ne_zero hn (hpos m) (hpos l) hH hrec hz hs

end LogSolutions

end DLMF.Hypergeometric
end
end
