/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.TrigSeriesExtension
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivative identities for scalar power-series operations

Mathlib's Cauchy–Taylor coefficients give the differentiated coefficient series near the
center. The principal complex power derivative is written as a first-order differential
identity, convenient for determining coefficients of powers by convolution.

## Main results

* `Complex.eventually_hasSum_deriv_powerSeries`: a scalar power series is differentiated near its
  center by shifting its coefficients.
* `Complex.iteratedDeriv_mul_div_factorial`: normalized Leibniz coefficients.
* `Complex.taylorCoeff_recurrence_of_deriv_mul_sub_one`: the quadratic coefficient recurrence
  for `f'(f-1)=z f` with `f(0)=f'(0)=1`.
* `Complex.mul_deriv_cpow_const`: the first-order differential identity for principal complex
  powers on the slit plane.
-/

@[expose] public noncomputable section
open Filter Finset
open scoped Topology
namespace Complex

/-- Differentiate a scalar power series near its center by shifting its coefficients. -/
theorem eventually_hasSum_deriv_powerSeries {a : ℕ → ℂ} {f : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ => (n + 1 : ℂ) * a (n + 1) * z ^ n) (deriv f z) := by
  have hfa := hf.analyticAt
  have ha : a = fun n : ℕ => iteratedDeriv n f 0 / n.factorial :=
    FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
      (hf.eq_formalMultilinearSeries hfa.hasFPowerSeriesAt)
  have hs := hfa.deriv.hasFPowerSeriesAt.eventually_hasSum
  simp only [zero_add] at hs
  filter_upwards [hs] with z hz
  convert hz using 1
  ext n
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, ha,
    ← iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

/-- The normalized Taylor coefficient of a product is the convolution of its coefficients. -/
theorem iteratedDeriv_mul_div_factorial {f g : ℂ → ℂ} {x : ℂ} (n : ℕ)
    (hf : ContDiffAt ℂ n f x) (hg : ContDiffAt ℂ n g x) :
    iteratedDeriv n (f * g) x / (n.factorial : ℂ) =
      ∑ k ∈ Finset.range (n + 1), (iteratedDeriv k f x / (k.factorial : ℂ)) *
        (iteratedDeriv (n - k) g x / ((n - k).factorial : ℂ)) := by
  rw [iteratedDeriv_mul hf hg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hfac : (n.choose k : ℂ) * (k.factorial : ℂ) * ((n - k).factorial : ℂ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hk0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk0 : ((n - k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hc0 : (n.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  rw [← hfac]
  field_simp

set_option maxHeartbeats 1000000 in
/-- Taylor coefficients of an analytic solution of `f'(z)(f(z)-1)=z f(z)`, normalized by
`f(0)=f'(0)=1`, satisfy a quadratic convolution recurrence. -/
theorem taylorCoeff_recurrence_of_deriv_mul_sub_one {f : ℂ → ℂ} {a : ℕ → ℂ} (hf : AnalyticAt ℂ f 0)
    (ha : ∀ n, iteratedDeriv n f 0 / (n.factorial : ℂ) = a n)
    (ha0 : a 0 = 1) (ha1 : a 1 = 1)
    (hode : ∀ᶠ z in 𝓝 (0 : ℂ), deriv f z * (f z - 1) = z * f z) (m : ℕ) :
    a (m+2) = a (m+1)/(m+3 : ℂ) - 1/2 *
      ∑ k ∈ range m, a (k+2) * a (m+1-k) := by
  let q : ℂ → ℂ := fun z => (f z - 1) * (f z - 1)
  have hq : deriv q =ᶠ[𝓝 (0 : ℂ)] fun z => 2 * (z * f z) := by
    filter_upwards [hf.eventually_analyticAt, hode] with z hz he
    dsimp [q]
    rw [deriv_fun_mul (hz.differentiableAt.sub_const 1)
      (hz.differentiableAt.sub_const 1), deriv_sub_const]
    linear_combination 2 * he
  have hb (n : ℕ) : iteratedDeriv n (fun z => f z - 1) 0 / (n.factorial : ℂ) =
      if n=0 then 0 else a n := by
    rw [iteratedDeriv_fun_sub hf.contDiffAt contDiffAt_const, sub_div, ha]
    by_cases hn : n=0
    · subst n; simp [ha0]
    · simp [iteratedDeriv_const, hn]
  have hcoeff (n : ℕ) : iteratedDeriv n q 0 / (n.factorial : ℂ) =
      ∑ k ∈ range (n+1), (if k=0 then 0 else a k) *
        (if n-k=0 then 0 else a (n-k)) := by
    dsimp [q]
    rw [show (fun z => (f z - 1)*(f z-1)) =
      (fun z => f z-1)*(fun z => f z-1) from rfl,
      iteratedDeriv_mul_div_factorial (f := fun z => f z - 1)
        (g := fun z => f z - 1) n
        (hf.sub analyticAt_const).contDiffAt (hf.sub analyticAt_const).contDiffAt]
    simp_rw [hb]
  have hd := congrArg (fun v => v / ((m+2).factorial : ℂ)) (hq.iteratedDeriv_eq (m+2))
  rw [iteratedDeriv_const_mul_field] at hd
  rw [← iteratedDeriv_succ'] at hd
  have hfac : ((m+3).factorial : ℂ) = (m+3 : ℂ) * ((m+2).factorial : ℂ) := by
    rw [show m+3=(m+2)+1 by omega, Nat.factorial_succ]; push_cast; ring
  have hfac0 : ((m+2).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hm3 : (m+3 : ℂ) ≠ 0 := by exact_mod_cast (show m+3≠0 by omega)
  have hleft : iteratedDeriv (m+2+1) q 0 / ((m+2).factorial : ℂ) =
      (m+3 : ℂ) * (iteratedDeriv (m+3) q 0 / ((m+3).factorial : ℂ)) := by
    rw [show m+2+1=m+3 by omega, hfac]; field_simp
  rw [hleft, hcoeff] at hd
  have hright : iteratedDeriv (m+2) (fun z => z*f z) 0 /
      ((m+2).factorial : ℂ) = a (m+1) := by
    have h := iteratedDeriv_mul_div_factorial (f := fun z : ℂ => z) (g := f) (x := 0) (m+2)
      contDiffAt_id hf.contDiffAt
    change iteratedDeriv (m+2) ((fun z : ℂ => z)*f) 0 / ((m+2).factorial : ℂ) = _
    rw [h]
    simp only [iteratedDeriv_fun_id_zero]
    rw [sum_eq_single 1]
    · simpa using ha (m+1)
    · intro b hb hb1; simp [hb1]
    · simp
  rw [mul_div_assoc, hright] at hd
  have hs : (∑ k ∈ range (m+3+1), (if k=0 then 0 else a k) *
      (if m+3-k=0 then 0 else a (m+3-k))) =
      2*a (m+2) + ∑ k ∈ range m, a (k+2)*a (m+1-k) := by
    rw [sum_range_succ, sum_range_succ, sum_range_succ', sum_range_succ']
    simp only [show m+3-(m+3)=0 by omega, show m+3-(m+2)=1 by omega,
      show m+3-1=m+2 by omega, show m+2≠0 by omega, show m+3≠0 by omega,
      show (1:ℕ)≠0 by omega, ite_true, ite_false, ha1, mul_zero, mul_one,
      one_mul, zero_mul, add_zero, zero_add]
    have he : (∑ k ∈ range m, (if k+1+1=0 then 0 else a (k+1+1)) *
        (if m+3-(k+1+1)=0 then 0 else a (m+3-(k+1+1)))) =
        ∑ k ∈ range m, a (k+2)*a (m+1-k) := by
      apply sum_congr rfl
      intro k hk
      have hk' := mem_range.mp hk
      simp only [show k+1+1=k+2 by omega, show k+2≠0 by omega,
        show m+3-(k+2)=m+1-k by omega, show m+1-k≠0 by omega, ↓reduceIte]
    rw [he]
    ring
  rw [hs] at hd
  field_simp
  linear_combination hd

/-- Principal complex powers satisfy the first-order power differential identity on the slit plane.
-/
theorem mul_deriv_cpow_const {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hz : f z ∈ slitPlane) (ν : ℂ) :
    f z * deriv (fun w => f w ^ ν) z = ν * (deriv f z * f z ^ ν) := by
  rw [(hf.hasDerivAt.cpow_const (c := ν) hz).deriv]
  have hpow : f z ^ (ν - 1) * f z = f z ^ ν := by
    calc
      _ = f z ^ (ν - 1) * f z ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = f z ^ ((ν - 1) + 1) := (Complex.cpow_add _ _ (Complex.slitPlane_ne_zero hz)).symm
      _ = _ := by congr 1; ring
  calc
    _ = ν * deriv f z * (f z ^ (ν - 1) * f z) := by ring
    _ = _ := by rw [hpow]; ring

end Complex
