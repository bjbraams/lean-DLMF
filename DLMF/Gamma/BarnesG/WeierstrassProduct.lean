/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import DLMF.Gamma.Basic.BarnesG
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import DLMF.Gamma.IntegralRepresentations

/-!
# The Barnes G-function: the integral formula and the Glaisher–Kinkelin constant (DLMF §5.17)

The Barnes G-function and the Glaisher–Kinkelin constant are defined in
`DLMF.Gamma.Basic.BarnesG`, together with the functional equation and the integer values. This
file proves the integral formula for `ln G(x + 1)` and the zeta form of `ln A`.

## Main definitions

* `logGammaTerm`, `barnesLogTerm`: the terms of the series for `ln Γ(t + 1)` and
  `ln G(x + 1)`.

## Main results

* `barnesGSucc_ofReal`: `G(x + 1)` for real `x ≥ 0` as the exponential of a real series.
* `log_barnesGSucc`: `Ln G(x + 1)` as an integral of `ln Γ` for `x > 0` (DLMF 5.17.4).
* `glaisherKinkelin_eq_zeta_neg_one`: `ln A = 1/12 - ζ'(-1)` (DLMF 5.17.7).
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral

open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

/-! ### The Weierstrass product: convergence and the shift identity -/

/-! ### The real logarithm of the Weierstrass product -/

/-- `u - u²/2 ≤ log(1 + u)` for `u ≥ 0`. -/
theorem sub_sq_div_two_le_log_one_add {u : ℝ} (hu : 0 ≤ u) : u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  let F : ℝ → ℝ := fun y => Real.log (1 + y) - y + y ^ 2 / 2
  have A : ∀ y ∈ Set.Icc 0 u, HasDerivAt F (1 / (1 + y) - 1 + y) y := by
    intro y hy
    have h1 : (1 + y) ≠ 0 := by linarith [hy.1]
    have := (((hasDerivAt_id y).const_add 1).log h1).sub (hasDerivAt_id y)
    have h2 : HasDerivAt F (1 / (1 + y) - 1 + (2 : ℕ) * y ^ (2 - 1) / 2) y :=
      this.add ((hasDerivAt_pow 2 y).div_const 2)
    convert h2 using 1
    norm_num
  have hmono : MonotoneOn F (Set.Icc 0 u) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u)
      (fun y hy ↦ (A y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (A y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    simp only [interior_Icc, Set.mem_Ioo] at hy
    have h1 : 0 < 1 + y := by linarith
    rw [show 1 / (1 + y) - 1 + y = y ^ 2 / (1 + y) by field_simp; ring]
    positivity
  have := hmono ⟨le_rfl, hu⟩ ⟨hu, le_rfl⟩ hu
  simp only [F, add_zero, Real.log_one, sub_zero] at this
  norm_num at this
  linarith

/-- The terms of the Weierstrass series for `log Γ(t+1)`. -/
def logGammaTerm (t : ℝ) (n : ℕ) : ℝ := t / (n + 1) - Real.log (1 + t / (n + 1))

/-- `t/(n+1) - log(1 + t/(n+1)) ≥ 0` for `t ≥ 0`. -/
theorem logGammaTerm_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ logGammaTerm t n := by
  have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + t / (n + 1))
  unfold logGammaTerm; linarith

/-- `t/(n+1) - log(1 + t/(n+1)) ≤ t²/(2(n+1)²)` for `t ≥ 0`. -/
theorem logGammaTerm_le {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    logGammaTerm t n ≤ t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2) := by
  have := sub_sq_div_two_le_log_one_add (by positivity : 0 ≤ t / (n + 1))
  unfold logGammaTerm
  rw [div_pow] at this
  have : t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2) = t ^ 2 / ((n : ℝ) + 1) ^ 2 / 2 := by
    rw [div_div, mul_comm]
  linarith

/-- `∑ₙ (t/(n+1) - log(1 + t/(n+1)))` converges for `t ≥ 0`. -/
theorem summable_logGammaTerm {t : ℝ} (ht : 0 ≤ t) : Summable (logGammaTerm t) := by
  have hs : Summable fun n : ℕ => t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine (this.mul_left (t ^ 2 / 2)).congr fun k => ?_
    push_cast; field_simp
  exact Summable.of_nonneg_of_le (logGammaTerm_nonneg ht) (logGammaTerm_le ht) hs

/-- `∑ₙ (t/(n+1) - log(1 + t/(n+1))) = log Γ(t + 1) + γ t` for `t ≥ 0`. -/
theorem hasSum_logGammaTerm {t : ℝ} (ht : 0 ≤ t) :
    HasSum (logGammaTerm t)
      (Real.log (Real.Gamma (t + 1)) + Real.eulerMascheroniConstant * t) := by
  rcases ht.eq_or_lt with rfl | ht
  · have h0 : logGammaTerm 0 = 0 := by funext n; simp [logGammaTerm]
    rw [h0]
    simp only [zero_add, Real.Gamma_one, Real.log_one, mul_zero]
    exact hasSum_zero
  have hW : ∀ n : ℕ, 0 < Real.weierstrassGammaTerm t n := fun n => by
    unfold Real.weierstrassGammaTerm; positivity
  have hlogW : ∀ n : ℕ, Real.log (Real.weierstrassGammaTerm t n) = -logGammaTerm t n := by
    intro n
    unfold Real.weierstrassGammaTerm logGammaTerm
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hsum : Summable fun n => Real.log (Real.weierstrassGammaTerm t n) := by
    simp only [hlogW]; exact (summable_logGammaTerm ht.le).neg
  have hprod := Real.rexp_tsum_eq_tprod hW hsum
  have hG := Real.one_div_Gamma_eq_tprod t
  rw [← hprod] at hG
  simp only [hlogW, tsum_neg] at hG
  have hGpos : 0 < Real.Gamma t := Real.Gamma_pos_of_pos ht
  have hG1 : Real.Gamma (t + 1) = Real.exp (∑' n, logGammaTerm t n -
      Real.eulerMascheroniConstant * t) := by
    rw [Real.Gamma_add_one ht.ne', Real.exp_sub]
    have : Real.Gamma t = (t * Real.exp (Real.eulerMascheroniConstant * t) *
        Real.exp (-∑' n, logGammaTerm t n))⁻¹ := by rw [← hG, inv_inv]
    rw [this, Real.exp_neg]
    field_simp
  rw [hG1, Real.log_exp, sub_add_cancel]
  exact (summable_logGammaTerm ht.le).hasSum

/-- Each term `t/(n+1) - log(1 + t/(n+1))` is continuous on `[0, ∞)`. -/
theorem continuousOn_logGammaTerm (n : ℕ) :
    ContinuousOn (fun t => logGammaTerm t n) (Set.Ici 0) := by
  intro t ht
  have h1 : (1 + t / (n + 1)) ≠ 0 := by
    have : (0 : ℝ) ≤ t := ht
    positivity
  unfold logGammaTerm
  exact (((continuous_id.div_const _).continuousAt).sub
    ((continuous_const.add (continuous_id.div_const _)).continuousAt.log h1)).continuousWithinAt

/-- `∫₀ˣ (t/(n+1) - log(1 + t/(n+1))) dt = x²/(2(n+1)) - ((n + 1 + x) log(1 + x/(n+1)) - x)`. -/
theorem integral_logGammaTerm {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ∫ t in (0 : ℝ)..x, logGammaTerm t n =
      x ^ 2 / (2 * (n + 1)) - (((n : ℝ) + 1 + x) * Real.log (1 + x / (n + 1)) - x) := by
  have hm : (0 : ℝ) < n + 1 := by positivity
  have hsub : Set.uIcc 0 x ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hx]; exact Set.Icc_subset_Ici_self
  have hderiv : ∀ t ∈ Set.uIcc 0 x, HasDerivAt
      (fun t : ℝ => t ^ 2 / (2 * (n + 1)) - (((n : ℝ) + 1 + t) * Real.log (1 + t / (n + 1)) - t))
      (logGammaTerm t n) t := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := hsub ht
    have h1 : (1 + t / (n + 1)) ≠ 0 := by positivity
    have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t / (n + 1)))
        ((1 / (n + 1)) / (1 + t / (n + 1))) t := by
      have := ((hasDerivAt_id t).div_const ((n : ℝ) + 1)).const_add 1
      exact this.log h1
    have h := (((hasDerivAt_pow 2 t).div_const (2 * ((n : ℝ) + 1))).sub
      ((((hasDerivAt_id t).const_add ((n : ℝ) + 1)).mul hlog).sub (hasDerivAt_id t)))
    refine h.congr_deriv ?_
    unfold logGammaTerm
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuousOn_logGammaTerm n).mono hsub).intervalIntegrable]
  simp

/-- The logarithms of the factors in the Weierstrass product for `G(x+1)`, for real `x`. -/
def barnesLogTerm (x : ℝ) (n : ℕ) : ℝ :=
  (n + 1) * Real.log (1 + x / (n + 1)) - x + x ^ 2 / (2 * (n + 1))

/-- `barnesLogTerm x n = x · logGammaTerm x n - ∫₀ˣ logGammaTerm t n dt`. -/
theorem barnesLogTerm_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    barnesLogTerm x n = x * logGammaTerm x n - ∫ t in (0 : ℝ)..x, logGammaTerm t n := by
  have hm : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [integral_logGammaTerm hx, barnesLogTerm, logGammaTerm]
  field_simp
  ring

/-- Termwise integration of `∑ₙ logGammaTerm t n` over `[0, x]`. -/
theorem hasSum_integral_logGammaTerm {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun n => ∫ t in (0 : ℝ)..x, logGammaTerm t n)
      (∫ t in (0 : ℝ)..x, ∑' n, logGammaTerm t n) := by
  have hsub : Set.uIoc 0 x ⊆ Set.Ici 0 := by
    rw [Set.uIoc_of_le hx]; exact fun t ht => le_of_lt ht.1
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => x ^ 2 / (2 * ((n : ℝ) + 1) ^ 2)) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · exact ((continuousOn_logGammaTerm n).mono hsub).aestronglyMeasurable measurableSet_uIoc
  · refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hx] at ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    rw [Real.norm_of_nonneg (logGammaTerm_nonneg ht0 n)]
    refine (logGammaTerm_le ht0 n).trans ?_
    gcongr
    exact ht.2
  · refine Filter.Eventually.of_forall fun t _ => ?_
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine (this.mul_left (x ^ 2 / 2)).congr fun k => ?_
    push_cast; field_simp
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht => ?_
    exact (summable_logGammaTerm (hsub ht)).hasSum

/-- `t ↦ log Γ(t + 1)` is continuous on `[0, ∞)`. -/
theorem continuousOn_log_Gamma_add_one :
    ContinuousOn (fun t : ℝ => Real.log (Real.Gamma (t + 1))) (Set.Ici 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t + 1 := by have : (0 : ℝ) ≤ t := ht; linarith
  have hG : ContinuousAt Real.Gamma (t + 1) := by
    refine (Real.differentiableAt_Gamma fun m h => ?_).continuousAt
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have hc : ContinuousAt (fun s : ℝ => Real.Gamma (s + 1)) t :=
    ContinuousAt.comp (g := Real.Gamma) (f := fun s : ℝ => s + 1) hG (by fun_prop)
  exact (hc.log (Real.Gamma_pos_of_pos ht0).ne').continuousWithinAt

/-- `∑ₙ barnesLogTerm x n = x log Γ(x + 1) - ∫₀ˣ log Γ(t + 1) dt + γx²/2` for `x ≥ 0`. -/
theorem hasSum_barnesLogTerm {x : ℝ} (hx : 0 ≤ x) :
    HasSum (barnesLogTerm x)
      (x * Real.log (Real.Gamma (x + 1)) - (∫ t in (0 : ℝ)..x, Real.log (Real.Gamma (t + 1))) +
        Real.eulerMascheroniConstant * x ^ 2 / 2) := by
  set γ := Real.eulerMascheroniConstant
  have hsub : Set.uIcc 0 x ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hx]; exact Set.Icc_subset_Ici_self
  have hI : ∫ t in (0 : ℝ)..x, ∑' n, logGammaTerm t n =
      (∫ t in (0 : ℝ)..x, Real.log (Real.Gamma (t + 1))) + γ * (x ^ 2 / 2) := by
    rw [intervalIntegral.integral_congr (g := fun t => Real.log (Real.Gamma (t + 1)) + γ * t)
      fun t ht => (hasSum_logGammaTerm (hsub ht)).tsum_eq]
    rw [intervalIntegral.integral_add (f := fun t => Real.log (Real.Gamma (t + 1)))
      (g := fun t => γ * t) (continuousOn_log_Gamma_add_one.mono hsub).intervalIntegrable
      ((continuous_const.mul continuous_id : Continuous fun t : ℝ => γ * t).intervalIntegrable 0 x),
      intervalIntegral.integral_const_mul, integral_id]
    ring
  have h := ((hasSum_logGammaTerm hx).mul_left x).sub (hasSum_integral_logGammaTerm hx)
  rw [hI] at h
  convert h using 1
  · funext n; exact barnesLogTerm_eq hx n
  · ring

/-- At real `x ≥ 0` the Weierstrass factor is `exp(barnesLogTerm x k)`. -/
theorem barnesGTerm_ofReal {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    barnesGTerm x k = Complex.exp (barnesLogTerm x k) := by
  have hpos : (0 : ℝ) < 1 + x / (k + 1) := by positivity
  have hreal : (1 + x / (k + 1)) ^ (k + 1) * Real.exp (-x + x ^ 2 / (2 * (k + 1))) =
      Real.exp (barnesLogTerm x k) := by
    rw [barnesLogTerm, show ((k : ℝ) + 1) * Real.log (1 + x / (k + 1)) - x +
      x ^ 2 / (2 * (k + 1)) = ((k + 1 : ℕ) : ℝ) * Real.log (1 + x / (k + 1)) +
        (-x + x ^ 2 / (2 * (k + 1))) by push_cast; ring,
      Real.exp_add (((k + 1 : ℕ) : ℝ) * _), Real.exp_nat_mul, Real.exp_log hpos]
  rw [barnesGTerm_eq, ← Complex.ofReal_exp, ← hreal]
  push_cast
  rfl

/-- For real `x ≥ 0`, `G(x + 1) = exp((x/2) log 2π - x(x+1)/2 - γx²/2 + ∑ₙ barnesLogTerm x n)`. -/
theorem barnesGSucc_ofReal {x : ℝ} (hx : 0 ≤ x) :
    barnesGSucc x = Real.exp (x / 2 * Real.log (2 * π) - x * (x + 1) / 2 -
      Real.eulerMascheroniConstant * x ^ 2 / 2 + ∑' n, barnesLogTerm x n) := by
  have hb := (hasSum_barnesLogTerm hx).summable.hasSum
  have hc : HasSum (fun n => (barnesLogTerm x n : ℂ)) (∑' n, barnesLogTerm x n : ℝ) :=
    Complex.hasSum_ofReal.mpr hb
  have hprod : ∏' k : ℕ, barnesGTerm x k = Complex.exp (∑' n, barnesLogTerm x n : ℝ) := by
    rw [← hc.cexp.tprod_eq]
    congr 1
    funext k
    exact barnesGTerm_ofReal hx k
  have h2pi : (2 * π : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * π := by positivity
    exact_mod_cast this.ne'
  have hlog : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  unfold barnesGSucc
  rw [hprod, cpow_def_of_ne_zero h2pi, hlog, ← Complex.exp_add, ← Complex.exp_add,
    Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- DLMF 5.17.4: `Ln G(x + 1) = (x/2) ln 2π - x(x+1)/2 + x ln Γ(x + 1) - ∫₀ˣ ln Γ(t + 1) dt` for `x
> 0`. -/
@[dlmf 5.17.E4]
theorem log_barnesGSucc {x : ℝ} (hx : 0 < x) :
    Complex.log (barnesGSucc x) =
      (1 / 2 : ℂ) * x * Complex.log (2 * π) - (1 / 2 : ℂ) * x * (x + 1) +
        x * Complex.log (Complex.Gamma (x + 1)) -
        ∫ t : ℝ in (0 : ℝ)..x, Complex.log (Complex.Gamma (t + 1)) := by
  have hsub : Set.uIcc 0 x ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hx.le]; exact Set.Icc_subset_Ici_self
  have hG : ∀ t : ℝ, 0 ≤ t →
      Complex.log (Complex.Gamma (t + 1)) = ((Real.log (Real.Gamma (t + 1)) : ℝ) : ℂ) := by
    intro t ht
    rw [show (t : ℂ) + 1 = ((t + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      Complex.ofReal_log (Real.Gamma_pos_of_pos (by linarith)).le]
  have hlog : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  rw [barnesGSucc_ofReal hx.le, ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp,
    hG x hx.le, intervalIntegral.integral_congr
      (g := fun t : ℝ => ((Real.log (Real.Gamma (t + 1)) : ℝ) : ℂ)) fun t ht => hG t (hsub ht),
    intervalIntegral.integral_ofReal, hlog, (hasSum_barnesLogTerm hx.le).tsum_eq]
  push_cast
  ring

/-- DLMF 5.17.7: `ln A = 1/12 - ζ'(-1)` for the Glaisher–Kinkelin constant `A`. -/
@[dlmf 5.17.E7]
theorem glaisherKinkelin_eq_zeta_neg_one :
    Real.log glaisherKinkelin = 1 / 12 - (deriv riemannZeta (-1)).re := by
  set γ := Real.eulerMascheroniConstant
  set Z := deriv riemannZeta 2
  -- Differentiate the functional equation `ζ(1 - s) = 2 (2π)^{-s} Γ(s) cos(πs/2) ζ(s)` at `s = 2`.
  have h2pi : (2 * π : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * π := by positivity
    exact_mod_cast this.ne'
  have hA : HasDerivAt (fun s : ℂ => (2 * π : ℂ) ^ (-s))
      ((2 * π : ℂ) ^ (-(2 : ℂ)) * Complex.log (2 * π) * (-1)) 2 :=
    (hasDerivAt_neg (2 : ℂ)).const_cpow (Or.inl h2pi)
  have hG : HasDerivAt Complex.Gamma (1 - γ) 2 := by
    have := Complex.hasDerivAt_Gamma_nat 1
    norm_num [harmonic] at this
    convert this using 1; ring
  have hC : HasDerivAt (fun s : ℂ => Complex.cos (π * s / 2))
      (-Complex.sin (π * 2 / 2) * (π / 2)) 2 := by
    have h : HasDerivAt (fun s : ℂ => π * s / 2) (π / 2) 2 := by
      simpa using ((hasDerivAt_id (2 : ℂ)).const_mul (π : ℂ)).div_const 2
    exact h.ccos
  have hZ : HasDerivAt riemannZeta Z 2 :=
    (differentiableAt_riemannZeta (by norm_num)).hasDerivAt
  have hR := ((((hA.const_mul 2).mul hG).mul hC).mul hZ)
  have hL : HasDerivAt (fun s => riemannZeta (1 - s)) (deriv riemannZeta (-1) * (-1)) 2 := by
    have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) 2 := by
      simpa using (hasDerivAt_id (2 : ℂ)).const_sub 1
    have hz : HasDerivAt riemannZeta (deriv riemannZeta (-1)) (1 - 2) := by
      rw [show (1 : ℂ) - 2 = -1 by norm_num]
      exact (differentiableAt_riemannZeta (by norm_num)).hasDerivAt
    exact hz.comp 2 h1
  have heq : (fun s => riemannZeta (1 - s)) =ᶠ[𝓝 2]
      fun s => 2 * (2 * π : ℂ) ^ (-s) * Complex.Gamma s * Complex.cos (π * s / 2) *
        riemannZeta s := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
    refine riemannZeta_one_sub (fun n h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp at this hs; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    · rw [h] at hs; simp at hs
  have huniq := hL.unique (hR.congr_of_eventuallyEq heq)
  simp only [Pi.mul_apply] at huniq
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpow : (2 * π : ℂ) ^ (-(2 : ℂ)) = 1 / (4 * (π : ℂ) ^ 2) := by
    rw [cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]; ring
  have hlog : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  have hG2 : Complex.Gamma 2 = 1 := by
    rw [show (2 : ℂ) = ((1 : ℕ) : ℂ) + 1 by norm_num, Complex.Gamma_nat_eq_factorial]; simp
  rw [show (π : ℂ) * 2 / 2 = π by ring, Complex.cos_pi, Complex.sin_pi, riemannZeta_two,
    hpow, hlog, hG2] at huniq
  have h : deriv riemannZeta (-1) =
      (((1 / 12 - (γ + Real.log (2 * π)) / 12 : ℝ) : ℂ)) + Z / ((2 * π ^ 2 : ℝ) : ℂ) := by
    rw [show deriv riemannZeta (-1) = -(deriv riemannZeta (-1) * -1) by ring, huniq]
    push_cast
    field_simp
    ring
  rw [h, Complex.add_re, Complex.ofReal_re, Complex.div_ofReal_re, glaisherKinkelin,
    Real.log_exp]
  ring

end DLMF.Gamma
end
end
