/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Deriv

public import DLMF.QSeries.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# q-gamma and q-beta (DLMF §5.18)

The q-Pochhammer symbols 5.18.1 and 5.18.3, the q-gamma function 5.18.4–5.18.7,
and Jackson's q-beta integral 5.18.12 are already in `DLMF.QSeries`. The remaining
identities are recorded here without duplicating those definitions.
-/

@[expose] public section

open Complex Filter Set DLMF.QSeries
open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

/-- q-factorial, DLMF 5.18.2. -/
@[dlmf 5.18.E2]
def qFactorial (q : ℂ) (n : ℕ) : ℂ :=
  qPochhammer q q n * (1 - q) ^ (-(n : ℂ))

/-- DLMF 5.18.6: `[n]_q! = Γ_q(n + 1)` for `|q| < 1`. -/
@[dlmf 5.18.E6]
theorem qFactorial_eq_qGamma (q : ℂ) (n : ℕ) (hq : ‖q‖ < 1) (hq0 : q ≠ 1) :
    qFactorial q n = qGamma q (n + 1) := by
  have hb : 1 - q ≠ 0 := sub_ne_zero.mpr fun h => hq0 h.symm
  have hcast : (n + 1 : ℂ) = ↑(n + 1) := by
    rw [Nat.cast_add, Nat.cast_one]
  have hpow : q * q ^ n = q ^ (n + 1 : ℂ) := by
    rw [hcast, cpow_natCast, pow_succ']
  have hsplit := qPochhammerInf_mul_qPochhammer (a := q) hq n
  have hexp : (1 - q) ^ (1 - (n + 1 : ℂ)) = (1 - q) ^ (-(n : ℂ)) := by
    congr 1
    ring
  have hinf : qPochhammerInf (q ^ (n + 1 : ℂ)) q ≠ 0 := by
    refine qPochhammerInf_ne_zero hq fun k hk => ?_
    have hpow' : q ^ (n + 1 : ℂ) = q ^ (n + 1) := by
      rw [hcast, cpow_natCast]
    have hpos : 0 < n + 1 + k := Nat.add_pos_left (Nat.succ_pos n) k
    have hlt : ‖q ^ (n + 1 + k)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq hpos.ne'
    have : q ^ (n + 1) * q ^ k = q ^ (n + 1 + k) := (pow_add _ _ _).symm
    rw [hpow', this, sub_eq_zero] at hk
    rw [← hk, norm_one] at hlt
    exact (lt_irrefl (1 : ℝ)) hlt
  unfold qFactorial qGamma
  rw [hsplit, hpow, hexp]
  field [hinf, hb]

/-- DLMF 5.18.5 at `x = 2`: `Γ_q(2) = 1`. -/
@[dlmf 5.18.E5]
theorem qGamma_two {q : ℂ} (hq : ‖q‖ < 1) : qGamma q 2 = 1 := by
  by_cases hq0 : q = 0
  · subst hq0
    have h0 : (0 : ℂ) ^ (2 : ℂ) = 0 := zero_cpow (by norm_num)
    have hone : qPochhammerInf (0 : ℂ) 0 = 1 := by
      simp [qPochhammerInf, tprod_one]
    simp [qGamma, h0, hone]
  · have hx : ∀ n : ℕ, q ^ ((1 : ℂ) + n) ≠ 1 := by
      intro n h
      have hpow : q ^ ((1 : ℂ) + n) = q ^ (n + 1) := by
        rw [add_comm, ← Nat.cast_one, ← Nat.cast_add, cpow_natCast]
      have hlt : ‖q ^ (n + 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero n)
      rw [hpow] at h
      rw [h, norm_one] at hlt
      exact (lt_irrefl (1 : ℝ)) hlt
    have hrec := qGamma_add_one hq hq0 hx (x := 1)
    have hq1 : q ≠ 1 := by
      intro h
      rw [h, norm_one] at hq
      exact (lt_irrefl (1 : ℝ)) hq
    have hb : 1 - q ≠ 0 := sub_ne_zero.mpr fun h => hq1 h.symm
    have hsimp : (1 - q ^ (1 : ℂ)) / (1 - q) * qGamma q 1 = 1 := by
      simp [qGamma_one hq, cpow_one, hb]
    have : qGamma q ((1 : ℂ) + 1) = 1 := hrec.trans hsimp
    simpa [show (1 : ℂ) + 1 = 2 by ring] using this

/-- q-beta function, DLMF 5.18.11. -/
@[dlmf 5.18.E11]
def qBeta (q a b : ℂ) : ℂ :=
  qGamma q a * qGamma q b / qGamma q (a + b)

/-! ### The limit `q → 1⁻` (DLMF 5.18.10)

For `0 < x ≤ 1` the concavity of `t ↦ log (1 - q^t)` sandwiches `Γ_q(x)` between
`[n]_q! [n]_q^x / ∏_{k=0}^n [x+k]_q` and the same with `[n+1]_q^x`. As `q → 1⁻` these tend to
Euler's `GammaSeq x n` and `GammaSeq x n · (1 + 1/n)^x`, which both tend to `Γ(x)`. The
functional equation `Γ_q(x+1) = [x]_q Γ_q(x)` extends the limit to all `x > 0`. -/

namespace QGammaLimit

open Finset

/-- `log (1 - q ^ t)`, the logarithm of a factor of `(q^t;q)_∞`. -/
def g (q t : ℝ) : ℝ := Real.log (1 - q ^ t)

/-- The `q`-number `[t]_q = (1 - q^t)/(1 - q)`. -/
def qNum (q t : ℝ) : ℝ := (1 - q ^ t) / (1 - q)

variable {q x : ℝ}

/-- `1 - q^t > 0` for `0 < q < 1` and `t > 0`. -/
theorem one_sub_rpow_pos (hq0 : 0 < q) (hq1 : q < 1) {t : ℝ} (ht : 0 < t) :
    0 < 1 - q ^ t := by
  have := Real.rpow_lt_one hq0.le hq1 ht
  linarith

/-- `g q t = log(1 - q^t) ≤ 0` for `0 < q < 1` and `t > 0`. -/
theorem g_nonpos (hq0 : 0 < q) (hq1 : q < 1) {t : ℝ} (ht : 0 < t) : g q t ≤ 0 := by
  have := Real.rpow_pos_of_pos hq0 t
  exact Real.log_nonpos (one_sub_rpow_pos hq0 hq1 ht).le (by linarith)

/-- `log(1 - q^t) = log [t]_q + log(1 - q)`, where `[t]_q = (1 - q^t)/(1 - q)`. -/
theorem g_eq (hq0 : 0 < q) (hq1 : q < 1) {t : ℝ} (ht : 0 < t) :
    g q t = Real.log (qNum q t) + Real.log (1 - q) := by
  unfold g qNum
  rw [Real.log_div (one_sub_rpow_pos hq0 hq1 ht).ne' (by linarith)]
  ring

/-- `t ↦ log (1 - q^t)` is concave on `(0, ∞)`. -/
theorem concaveOn_g (hq0 : 0 < q) (hq1 : q < 1) : ConcaveOn ℝ (Ioi 0) (g q) := by
  refine ⟨convex_Ioi 0, fun s hs t ht a b ha hb hab => ?_⟩
  have hs' := one_sub_rpow_pos hq0 hq1 hs
  have ht' := one_sub_rpow_pos hq0 hq1 ht
  have hc := (convexOn_rpow_left hq0).2 (mem_univ s) (mem_univ t) ha hb hab
  have hl := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.2 hs') (mem_Ioi.2 ht') ha hb hab
  simp only [smul_eq_mul] at hc hl ⊢
  unfold g
  have hpos : 0 < a * (1 - q ^ s) + b * (1 - q ^ t) := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left (1 - q ^ s) (1 - q ^ t)) ha,
      mul_le_mul_of_nonneg_left (min_le_right (1 - q ^ s) (1 - q ^ t)) hb, lt_min hs' ht']
  calc a * Real.log (1 - q ^ s) + b * Real.log (1 - q ^ t)
      ≤ Real.log (a * (1 - q ^ s) + b * (1 - q ^ t)) := hl
    _ ≤ Real.log (1 - q ^ (a * s + b * t)) := by
      refine Real.log_le_log hpos ?_
      have : a * (1 - q ^ s) + b * (1 - q ^ t) = 1 - (a * q ^ s + b * q ^ t) := by
        linear_combination hab
      linarith

/-- Concavity of `t ↦ log(1 - q^t)` between `t` and `t + 1`: `(1 - x) g(t) + x g(t + 1) ≤ g(t + x)`
for `0 ≤ x ≤ 1`. -/
theorem g_concave_one (hq0 : 0 < q) (hq1 : q < 1) {t : ℝ} (ht : 0 < t) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) : (1 - x) * g q t + x * g q (t + 1) ≤ g q (t + x) := by
  have h := (concaveOn_g hq0 hq1).2 (mem_Ioi.2 ht) (mem_Ioi.2 (by linarith : (0 : ℝ) < t + 1))
    (by linarith : (0 : ℝ) ≤ 1 - x) hx0 (by ring)
  simp only [smul_eq_mul] at h
  convert h using 2
  ring

/-- Concavity of `t ↦ log(1 - q^t)`: `g(t + x) - g(t) ≤ x (g(t) - g(t - 1))` for `t > 1`, `x ≥ 0`.
-/
theorem g_concave_two (hq0 : 0 < q) (hq1 : q < 1) {t : ℝ} (ht : 1 < t) (hx0 : 0 ≤ x) :
    g q (t + x) - g q t ≤ x * (g q t - g q (t - 1)) := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h1' : 1 + x ≠ 0 := h1.ne'
  have h := (concaveOn_g hq0 hq1).2 (mem_Ioi.2 (by linarith : (0 : ℝ) < t - 1))
    (mem_Ioi.2 (by linarith : (0 : ℝ) < t + x)) (div_nonneg hx0 h1.le)
    (div_nonneg zero_le_one h1.le) (by rw [← add_div, add_comm x 1, div_self h1'])
  simp only [smul_eq_mul] at h
  have hpt : x / (1 + x) * (t - 1) + 1 / (1 + x) * (t + x) = t := by
    field_simp
    ring
  rw [hpt] at h
  have h2 := mul_le_mul_of_nonneg_left h h1.le
  have he : (1 + x) * (x / (1 + x) * g q (t - 1) + 1 / (1 + x) * g q (t + x)) =
      x * g q (t - 1) + g q (t + x) := by
    field_simp
  linarith

/-- The partial log-sums of the products in `qGamma`. -/
def D (q x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, g q ((k : ℝ) + 1) - ∑ k ∈ range N, g q (x + k)

/-- The first `n` (resp. `n + 1`) terms of `D`. -/
def K (q x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, g q ((k : ℝ) + 1) - ∑ k ∈ range (n + 1), g q (x + k)

/-- Recurrence for the partial log-sums: `D(N + 1) = D(N) + g(N + 1) - g(x + N)`. -/
theorem D_succ (q x : ℝ) (N : ℕ) :
    D q x (N + 1) = D q x N + g q ((N : ℝ) + 1) - g q (x + N) := by
  unfold D
  rw [sum_range_succ, sum_range_succ]
  ring

/-- `D(n + 1) = K(n) + g(n + 1)`. -/
theorem D_base (q x : ℝ) (n : ℕ) : D q x (n + 1) = K q x n + g q ((n : ℝ) + 1) := by
  unfold D K
  rw [sum_range_succ (fun k : ℕ => g q ((k : ℝ) + 1))]
  ring

/-- Lower bound for the partial log-sums `D(N)`, `N ≥ n + 1`, from concavity of `g`. -/
theorem D_lower (hq0 : 0 < q) (hq1 : q < 1) (hx0 : 0 ≤ x) {n : ℕ} (hn : 1 ≤ n) :
    ∀ N, n + 1 ≤ N →
      K q x n + g q N + x * g q n - x * g q ((N : ℝ) - 1) ≤ D q x N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    rw [D_base]
    push_cast
    simp only [add_sub_cancel_right]
    linarith
  | succ N hN ih =>
    have hN1 : (1 : ℝ) < N := by
      have : 2 ≤ N := by omega
      exact_mod_cast this
    have hc := g_concave_two hq0 hq1 hN1 hx0
    rw [add_comm (N : ℝ) x] at hc
    rw [D_succ]
    push_cast
    simp only [add_sub_cancel_right]
    linarith

/-- Upper bound for the partial log-sums `D(N)`, `N ≥ n + 1`, from concavity of `g`, for `0 ≤ x ≤
1`. -/
theorem D_upper (hq0 : 0 < q) (hq1 : q < 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    ∀ N, n + 1 ≤ N →
      D q x N ≤ K q x n + x * g q ((n : ℝ) + 1) + (1 - x) * g q N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    rw [D_base]
    push_cast
    linarith
  | succ N hN ih =>
    have hN0 : (0 : ℝ) < N := by
      have : 1 ≤ N := by omega
      exact_mod_cast this
    have hc := g_concave_one hq0 hq1 hN0 hx0 hx1
    rw [add_comm (N : ℝ) x] at hc
    rw [D_succ]
    push_cast
    linarith

/-- The finite truncations of `qGamma q x`, as real numbers. -/
def r (q x : ℝ) (N : ℕ) : ℝ :=
  (∏ k ∈ range N, (1 - q ^ (k + 1))) / (∏ k ∈ range N, (1 - q ^ (x + k))) *
    (1 - q) ^ (1 - x)

/-- `log r(N) = D(N) + (1 - x) log(1 - q)` for the truncations `r` of `Γ_q(x)`. -/
theorem log_r (hq0 : 0 < q) (hq1 : q < 1) (hx0 : 0 < x) (N : ℕ) :
    Real.log (r q x N) = D q x N + (1 - x) * Real.log (1 - q) := by
  have hA : ∀ k ∈ range N, (1 - q ^ (k + 1) : ℝ) ≠ 0 := fun k _ =>
    (sub_pos.2 (pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero k))).ne'
  have hB : ∀ k ∈ range N, (1 - q ^ (x + k) : ℝ) ≠ 0 := fun k _ =>
    (one_sub_rpow_pos hq0 hq1 (add_pos_of_pos_of_nonneg hx0 k.cast_nonneg)).ne'
  have hA' := prod_ne_zero_iff.2 hA
  have hB' := prod_ne_zero_iff.2 hB
  unfold r D g
  rw [Real.log_mul (div_ne_zero hA' hB') (Real.rpow_pos_of_pos (by linarith) _).ne',
    Real.log_div hA' hB', Real.log_prod hA, Real.log_prod hB, Real.log_rpow (by linarith)]
  have e : ∑ k ∈ range N, Real.log (1 - q ^ (k + 1)) =
      ∑ k ∈ range N, Real.log (1 - q ^ ((k : ℝ) + 1)) :=
    sum_congr rfl fun k _ => by norm_cast
  rw [e]

/-- The truncations `r q x N` of `Γ_q(x)` are positive. -/
theorem r_pos (hq0 : 0 < q) (hq1 : q < 1) (hx0 : 0 < x) (N : ℕ) : 0 < r q x N := by
  unfold r
  refine mul_pos (div_pos (prod_pos fun k _ => ?_) (prod_pos fun k _ => ?_))
    (Real.rpow_pos_of_pos (by linarith) _)
  · exact sub_pos.2 (pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero k))
  · exact one_sub_rpow_pos hq0 hq1 (add_pos_of_pos_of_nonneg hx0 k.cast_nonneg)

/-- Two-sided exponential bounds for the truncations `r q x N` of `Γ_q(x)`, `0 < x ≤ 1`. -/
theorem r_bounds (hq0 : 0 < q) (hq1 : q < 1) (hx0 : 0 < x) (hx1 : x ≤ 1) {n : ℕ}
    (hn : 1 ≤ n) {N : ℕ} (hN : n + 1 ≤ N) :
    Real.exp (K q x n + x * g q n + (1 - x) * Real.log (1 - q) + g q N) ≤ r q x N ∧
      r q x N ≤ Real.exp (K q x n + x * g q ((n : ℝ) + 1) + (1 - x) * Real.log (1 - q)) := by
  rw [← Real.exp_log (r_pos hq0 hq1 hx0 N), log_r hq0 hq1 hx0]
  have hNm : (0 : ℝ) < (N : ℝ) - 1 := by
    have : 2 ≤ N := by omega
    have : (2 : ℝ) ≤ N := by exact_mod_cast this
    linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hlo := D_lower hq0 hq1 hx0.le hn N hN
  have hup := D_upper hq0 hq1 hx0.le hx1 n N hN
  have h1 := mul_nonpos_of_nonneg_of_nonpos hx0.le (g_nonpos hq0 hq1 hNm)
  have h2 := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ 1 - x)
    (g_nonpos hq0 hq1 hN0)
  constructor <;> refine Real.exp_le_exp.2 ?_ <;> linarith

/-- `log(1 - q^N) → 0` as `N → ∞`. -/
theorem tendsto_g_nat (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun N : ℕ => g q N) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => q ^ (N : ℝ)) atTop (𝓝 0) := by
    simpa [Real.rpow_natCast] using tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
  have h2 : Tendsto (fun N : ℕ => 1 - q ^ (N : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simpa [g] using h2.log one_ne_zero

/-- `‖(q : ℂ)‖ < 1` for real `0 < q < 1`. -/
theorem norm_ofReal_lt_one (hq0 : 0 < q) (hq1 : q < 1) : ‖(q : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
  exact hq1

/-- The real truncations `r q x N` converge to `Γ_q(x)`. -/
theorem tendsto_r_complex (hq0 : 0 < q) (hq1 : q < 1) (hx0 : 0 < x) :
    Tendsto (fun N => (r q x N : ℂ)) atTop (𝓝 (qGamma q x)) := by
  have hq := norm_ofReal_lt_one hq0 hq1
  have hA := tendsto_qPochhammer (w := (q : ℂ)) hq
  have hB := tendsto_qPochhammer (w := (q : ℂ) ^ (x : ℂ)) hq
  have hpow : ∀ k : ℕ, (q : ℂ) ^ (x : ℂ) * (q : ℂ) ^ k = ((q ^ (x + k) : ℝ) : ℂ) := by
    intro k
    rw [Real.rpow_add hq0, Real.rpow_natCast, ofReal_mul, ofReal_cpow hq0.le]
    push_cast
    ring
  have hB0 : qPochhammerInf ((q : ℂ) ^ (x : ℂ)) q ≠ 0 := qPochhammerInf_ne_zero hq fun k h => by
    rw [hpow, sub_eq_zero] at h
    have hlt := Real.rpow_lt_one hq0.le hq1 (add_pos_of_pos_of_nonneg hx0 k.cast_nonneg)
    exact hlt.ne (by exact_mod_cast h.symm)
  have := (hA.div hB hB0).mul_const ((1 - (q : ℂ)) ^ (1 - (x : ℂ)))
  unfold qGamma
  refine this.congr fun N => ?_
  have e1 : (∏ k ∈ range N, (1 - (q : ℂ) * (q : ℂ) ^ k)) =
      ((∏ k ∈ range N, (1 - q ^ (k + 1)) : ℝ) : ℂ) := by
    push_cast
    exact prod_congr rfl fun k _ => by ring
  have e2 : (∏ k ∈ range N, (1 - (q : ℂ) ^ (x : ℂ) * (q : ℂ) ^ k)) =
      ((∏ k ∈ range N, (1 - q ^ (x + k)) : ℝ) : ℂ) := by
    rw [ofReal_prod]
    exact prod_congr rfl fun k _ => by rw [hpow, ofReal_sub, ofReal_one]
  have e3 : (1 - (q : ℂ)) ^ (1 - (x : ℂ)) = (((1 - q) ^ (1 - x) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by linarith)]
    push_cast
    rfl
  rw [Pi.div_apply, qPochhammer_eq_prod, qPochhammer_eq_prod, e1, e2, e3, ← ofReal_div,
    ← ofReal_mul]
  rfl

/-- The logarithmic bound expressed through `q`-numbers. -/
def L (q x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range n, Real.log (qNum q ((k : ℝ) + 1)) -
    ∑ k ∈ range (n + 1), Real.log (qNum q (x + k)) + x * Real.log (qNum q t)

/-- Rewriting the bound exponent through `q`-numbers: `K(n) + x g(t) + (1 - x) log(1 - q) = L(n,
t)`. -/
theorem K_add_eq (hq0 : 0 < q) (hq1 : q < 1) (hx0 : 0 < x) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    K q x n + x * g q t + (1 - x) * Real.log (1 - q) = L q x n t := by
  have e1 : ∑ k ∈ range n, g q ((k : ℝ) + 1) =
      ∑ k ∈ range n, (Real.log (qNum q ((k : ℝ) + 1)) + Real.log (1 - q)) :=
    sum_congr rfl fun k _ => g_eq hq0 hq1 (by positivity)
  have e2 : ∑ k ∈ range (n + 1), g q (x + k) =
      ∑ k ∈ range (n + 1), (Real.log (qNum q (x + k)) + Real.log (1 - q)) :=
    sum_congr rfl fun k _ => g_eq hq0 hq1 (add_pos_of_pos_of_nonneg hx0 (Nat.cast_nonneg k))
  unfold K L
  rw [e1, e2, g_eq hq0 hq1 ht, sum_add_distrib, sum_add_distrib]
  simp only [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- `[t]_q → t` as `q → 1⁻`. -/
theorem tendsto_qNum (t : ℝ) : Tendsto (fun q : ℝ => qNum q t) (𝓝[<] 1) (𝓝 t) := by
  have hd : HasDerivAt (fun q : ℝ => q ^ t) (t * (1 : ℝ) ^ (t - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  rw [Real.one_rpow, mul_one] at hd
  have hs := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
    (nhdsWithin_mono (s := Iio (1 : ℝ)) (t := {1}ᶜ) 1 fun y (hy : y < 1) => (ne_of_lt hy : y ≠ 1))
  refine hs.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y (hy : y < 1)
  have h1 : y - 1 ≠ 0 := sub_ne_zero.2 hy.ne
  have h2 : 1 - y ≠ 0 := sub_ne_zero.2 hy.ne'
  rw [slope_def_field, Real.one_rpow, qNum]
  field_simp
  ring

/-- As `q → 1⁻`, `L q x n t → ∑_{k<n} log(k + 1) - ∑_{k≤n} log(x + k) + x log t`. -/
theorem tendsto_L (hx0 : 0 < x) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun q => L q x n t) (𝓝[<] 1)
      (𝓝 (∑ k ∈ range n, Real.log ((k : ℝ) + 1) - ∑ k ∈ range (n + 1), Real.log (x + k) +
        x * Real.log t)) := by
  unfold L
  refine ((tendsto_finsetSum _ fun k _ => (tendsto_qNum _).log ?_).sub
    (tendsto_finsetSum _ fun k _ => (tendsto_qNum _).log ?_)).add
    (((tendsto_qNum t).log ht.ne').const_mul x)
  · positivity
  · exact (add_pos_of_pos_of_nonneg hx0 k.cast_nonneg).ne'

/-- `exp(∑_{k<n} log(k + 1) - ∑_{k≤n} log(x + k) + x log n) = Γₙ(x)`, the Gauss approximant. -/
theorem exp_lim (hx0 : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (∑ k ∈ range n, Real.log ((k : ℝ) + 1) - ∑ k ∈ range (n + 1), Real.log (x + k) +
      x * Real.log n) = Real.GammaSeq x n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (∏ k ∈ range n, ((k : ℝ) + 1)) = (Nat.factorial n : ℝ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    rfl
  have p1 : ∏ k ∈ range n, Real.exp (Real.log ((k : ℝ) + 1)) = ∏ k ∈ range n, ((k : ℝ) + 1) :=
    prod_congr rfl fun k _ => Real.exp_log (by positivity)
  have p2 : ∏ k ∈ range (n + 1), Real.exp (Real.log (x + k)) = ∏ k ∈ range (n + 1), (x + k) :=
    prod_congr rfl fun k _ => Real.exp_log (add_pos_of_pos_of_nonneg hx0 (Nat.cast_nonneg k))
  rw [Real.exp_add, Real.exp_sub, Real.exp_sum, Real.exp_sum, p1, p2,
    show x * Real.log n = Real.log n * x from mul_comm _ _, ← Real.rpow_def_of_pos hn0,
    Real.GammaSeq, hfac]
  ring

/-- For `0 < x ≤ 1`, `Γ_q(x)` is real and squeezed between `exp(L(n, n))` and `exp(L(n, n + 1))`. -/
theorem key (hq0 : 0 < q) (hq1 : q < 1) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    qGamma q x = ((qGamma q x).re : ℂ) ∧ ∀ n : ℕ, 1 ≤ n →
      Real.exp (L q x n n) ≤ (qGamma q x).re ∧
        (qGamma q x).re ≤ Real.exp (L q x n ((n : ℝ) + 1)) := by
  have h := tendsto_r_complex hq0 hq1 hx0
  have hre : Tendsto (r q x) atTop (𝓝 (qGamma q x).re) :=
    ((Complex.continuous_re.tendsto _).comp h).congr fun N => by simp
  have him : Tendsto (fun N => ((r q x N : ℂ)).im) atTop (𝓝 (qGamma q x).im) :=
    (Complex.continuous_im.tendsto _).comp h
  simp only [ofReal_im] at him
  have him0 : (qGamma q x).im = 0 := tendsto_nhds_unique him tendsto_const_nhds
  refine ⟨Complex.ext (by simp) (by simp [him0]), fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← K_add_eq hq0 hq1 hx0 n hn0, ← K_add_eq hq0 hq1 hx0 n (by linarith)]
  constructor
  · have hlo : Tendsto (fun N : ℕ => Real.exp (K q x n + x * g q n +
        (1 - x) * Real.log (1 - q) + g q N)) atTop
        (𝓝 (Real.exp (K q x n + x * g q n + (1 - x) * Real.log (1 - q)))) := by
      simpa using ((tendsto_g_nat hq0 hq1).const_add
        (K q x n + x * g q n + (1 - x) * Real.log (1 - q))).rexp
    refine le_of_tendsto_of_tendsto hlo hre ?_
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    exact (r_bounds hq0 hq1 hx0 hx1 hn hN).1
  · refine le_of_tendsto hre ?_
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    exact (r_bounds hq0 hq1 hx0 hx1 hn hN).2

/-- `Γ_q(x) → Γ(x)` as `q → 1⁻`, for `0 < x ≤ 1`. -/
theorem tendsto_base (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Tendsto (fun q : ℝ => qGamma q x) (𝓝[<] (1 : ℝ)) (𝓝 (Real.Gamma x : ℂ)) := by
  have hev : ∀ᶠ q in 𝓝[<] (1 : ℝ), 0 < q ∧ q < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with q hq using hq
  have hre : Tendsto (fun q : ℝ => (qGamma q x).re) (𝓝[<] 1) (𝓝 (Real.Gamma x)) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      obtain ⟨n, hn, hn1⟩ := (((Real.GammaSeq_tendsto_Gamma x).eventually
        (lt_mem_nhds ha)).and (eventually_ge_atTop 1)).exists
      have hlim := (tendsto_L hx0 n (by exact_mod_cast hn1 : (0 : ℝ) < n)).rexp
      rw [exp_lim hx0 hn1] at hlim
      filter_upwards [hlim.eventually (lt_mem_nhds hn), hev] with q h1 h2
      exact h1.trans_le ((key h2.1 h2.2 hx0 hx1).2 n hn1).1
    · intro b hb
      have hU : Tendsto (fun n : ℕ => Real.GammaSeq x n *
          Real.exp (x * (Real.log ((n : ℝ) + 1) - Real.log n))) atTop
          (𝓝 (Real.Gamma x)) := by
        have := (Real.GammaSeq_tendsto_Gamma x).mul
          ((Real.tendsto_log_nat_add_one_sub_log.const_mul x).rexp)
        simpa only [mul_zero, Real.exp_zero, mul_one] using this
      obtain ⟨n, hn, hn1⟩ := ((hU.eventually (gt_mem_nhds hb)).and
        (eventually_ge_atTop 1)).exists
      have hlim := (tendsto_L hx0 n (by positivity : (0 : ℝ) < (n : ℝ) + 1)).rexp
      have he : Real.exp (∑ k ∈ range n, Real.log ((k : ℝ) + 1) -
          ∑ k ∈ range (n + 1), Real.log (x + k) + x * Real.log ((n : ℝ) + 1)) =
          Real.GammaSeq x n * Real.exp (x * (Real.log ((n : ℝ) + 1) - Real.log n)) := by
        rw [← exp_lim hx0 hn1, ← Real.exp_add]
        congr 1
        ring
      rw [he] at hlim
      filter_upwards [hlim.eventually (gt_mem_nhds hn), hev] with q h1 h2
      exact ((key h2.1 h2.2 hx0 hx1).2 n hn1).2.trans_lt h1
  refine ((Complex.continuous_ofReal.tendsto _).comp hre).congr' ?_
  filter_upwards [hev] with q hq using ((key hq.1 hq.2 hx0 hx1).1).symm

/-- If `Γ_q(x) → Γ(x)` as `q → 1⁻`, then also `Γ_q(x + 1) → Γ(x + 1)`. -/
theorem tendsto_step (hx0 : 0 < x)
    (h : Tendsto (fun q : ℝ => qGamma q x) (𝓝[<] (1 : ℝ)) (𝓝 (Real.Gamma x : ℂ))) :
    Tendsto (fun q : ℝ => qGamma q (x + 1 : ℝ)) (𝓝[<] (1 : ℝ))
      (𝓝 (Real.Gamma (x + 1) : ℂ)) := by
  have hqn : Tendsto (fun q : ℝ => (qNum q x : ℂ)) (𝓝[<] 1) (𝓝 (x : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_qNum x)
  rw [Real.Gamma_add_one hx0.ne', Complex.ofReal_mul]
  refine (hqn.mul h).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with q ⟨hq0, hq1⟩
  have hq := norm_ofReal_lt_one hq0 hq1
  have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hx : ∀ n : ℕ, (q : ℂ) ^ ((x : ℂ) + n) ≠ 1 := by
    intro n hn
    have e : (q : ℂ) ^ ((x : ℂ) + n) = ((q ^ (x + n) : ℝ) : ℂ) := by
      rw [ofReal_cpow hq0.le]
      push_cast
      rfl
    rw [e] at hn
    have hlt := Real.rpow_lt_one hq0.le hq1 (add_pos_of_pos_of_nonneg hx0 n.cast_nonneg)
    exact hlt.ne (by exact_mod_cast hn)
  rw [Complex.ofReal_add, Complex.ofReal_one, qGamma_add_one hq hq0' hx, qNum, ofReal_div,
    ofReal_sub, ofReal_sub, ofReal_one, ofReal_cpow hq0.le]

end QGammaLimit

/-- DLMF 5.18.10: `Γ_q(x) → Γ(x)` as `q → 1⁻`, for `x > 0`. -/
@[dlmf 5.18.E10]
theorem tendsto_qGamma_one {x : ℝ} (hx : 0 < x) :
    Tendsto (fun q : ℝ => qGamma q x) (𝓝[<] (1 : ℝ)) (𝓝 (Real.Gamma x : ℂ)) := by
  have : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ m + 1 →
      Tendsto (fun q : ℝ => qGamma q y) (𝓝[<] (1 : ℝ)) (𝓝 (Real.Gamma y : ℂ)) := by
    intro m
    induction m with
    | zero =>
      intro y hy0 hy1
      exact QGammaLimit.tendsto_base hy0 (by simpa using hy1)
    | succ m ih =>
      intro y hy0 hy1
      rcases le_or_gt y 1 with h | h
      · exact QGammaLimit.tendsto_base hy0 h
      · have := QGammaLimit.tendsto_step (sub_pos.2 h)
          (ih (y - 1) (sub_pos.2 h) (by push_cast at hy1; linarith))
        simp only [sub_add_cancel] at this
        exact this
  exact this ⌈x⌉₊ x hx (by have := Nat.le_ceil x; linarith)

/-! ### Monotonicity in the base (DLMF 5.18.8–5.18.9)

For `0 < q < p < 1` the difference `G(t) = log (1 - p^t) - log (1 - q^t)` is strictly concave
on `(0, ∞)`: with `p = e^{-b}`, `q = e^{-a}`, `G'' = (a / 2 sinh (at/2))² - (b / 2 sinh (bt/2))²`,
which is negative because `sinh y / y` increases. The logarithm of `Γ_p(x)/Γ_q(x)` is the limit
of `∑_{k<N} (G(k+1) - G(x+k)) + (1-x) G(1)`. Comparing the terms at `x + k` with those at
`k + 1` and `k + 2` by strict concavity gives a gap of fixed sign that survives the limit,
because `Γ_q(1) = Γ_q(2) = 1`. -/

namespace QGammaMono

open Finset QGammaLimit

/-- `y ↦ sinh y / y` is strictly increasing on `(0, ∞)`. -/
theorem mul_sinh_lt {y Y : ℝ} (hy : 0 < y) (hyY : y < Y) :
    Y * Real.sinh y < y * Real.sinh Y := by
  have hconv : StrictConvexOn ℝ (Ici 0) Real.sinh := by
    refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0)
      Real.continuous_sinh.continuousOn ?_
    rw [Real.deriv_sinh, interior_Ici]
    exact Real.cosh_strictMonoOn.mono Ioi_subset_Ici_self
  have hY : 0 < Y := hy.trans hyY
  have hw : 0 < 1 - y / Y := by
    rw [sub_pos, div_lt_one hY]
    exact hyY
  have h := hconv.2 (mem_Ici.2 le_rfl) (mem_Ici.2 hY.le) hY.ne hw (div_pos hy hY) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sinh_zero] at h
  rw [div_mul_cancel₀ _ hY.ne'] at h
  have := mul_lt_mul_of_pos_left h hY
  rwa [← mul_assoc, mul_div_cancel₀ _ hY.ne'] at this

/-- `e^u/(e^u - 1)² = 1/(2 sinh(u/2))²` for `u > 0`. -/
theorem exp_div_sq_eq {u : ℝ} (hu : 0 < u) :
    Real.exp u / (Real.exp u - 1) ^ 2 = 1 / (2 * Real.sinh (u / 2)) ^ 2 := by
  have hE : Real.exp u = Real.exp (u / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h1 : Real.exp (u / 2) ≠ 0 := (Real.exp_pos _).ne'
  have h2 : Real.exp (u / 2) ^ 2 - 1 ≠ 0 := by
    have : 1 < Real.exp (u / 2) := Real.one_lt_exp_iff.2 (by linarith)
    nlinarith
  rw [Real.sinh_eq, Real.exp_neg, hE]
  field_simp

/-- For `0 < b < a` and `t > 0`: `a² e^(at)/(e^(at) - 1)² < b² e^(bt)/(e^(bt) - 1)²` (since `sinh y
/ y` increases). -/
theorem sq_mul_exp_div_lt {b a t : ℝ} (hb : 0 < b) (hba : b < a) (ht : 0 < t) :
    a ^ 2 * (Real.exp (a * t) / (Real.exp (a * t) - 1) ^ 2) <
      b ^ 2 * (Real.exp (b * t) / (Real.exp (b * t) - 1) ^ 2) := by
  have ha : 0 < a := hb.trans hba
  have hu : 0 < b * t / 2 := by positivity
  have huv : b * t / 2 < a * t / 2 := by nlinarith
  have hs := mul_sinh_lt hu huv
  have hsu : 0 < Real.sinh (a * t / 2) := Real.sinh_pos_iff.2 (hu.trans huv)
  have hsv : 0 < Real.sinh (b * t / 2) := Real.sinh_pos_iff.2 hu
  have hk : t * (a * Real.sinh (b * t / 2)) < t * (b * Real.sinh (a * t / 2)) := by
    linear_combination 2 * hs
  have hk' := lt_of_mul_lt_mul_left hk ht.le
  rw [exp_div_sq_eq (by positivity), exp_div_sq_eq (by positivity), mul_one_div, mul_one_div,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have h0 : 0 ≤ a * Real.sinh (b * t / 2) := by positivity
  have := mul_self_lt_mul_self h0 hk'
  have e1 : b * t / 2 = b * t / 2 := rfl
  nlinarith [this]

/-- `log (1 - e^{-ct})`. -/
def ell (c t : ℝ) : ℝ := Real.log (1 - Real.exp (-(c * t)))

/-- `t ↦ log(1 - e^(-ct))` has derivative `c/(e^(ct) - 1)` for `c, t > 0`. -/
theorem hasDerivAt_ell {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (ell c) (c / (Real.exp (c * t) - 1)) t := by
  have hE : 1 < Real.exp (c * t) := Real.one_lt_exp_iff.2 (by positivity)
  have hne : 1 - Real.exp (-(c * t)) ≠ 0 := by
    rw [Real.exp_neg]
    have : (Real.exp (c * t))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hE
    linarith
  have h1 : HasDerivAt (fun t => -(c * t)) (-c) t := by
    convert ((hasDerivAt_id t).const_mul c).neg using 1 <;> first | (funext s; simp) | simp
  have h2 := (h1.exp.const_sub 1).log hne
  unfold ell
  refine h2.congr_deriv ?_
  rw [Real.exp_neg]
  have h1 : Real.exp (c * t) ≠ 0 := (Real.exp_pos _).ne'
  have h2 : Real.exp (c * t) - 1 ≠ 0 := by linarith
  field_simp

/-- `t ↦ c/(e^(ct) - 1)` has derivative `-c² e^(ct)/(e^(ct) - 1)²` for `c, t > 0`. -/
theorem hasDerivAt_phi {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun t => c / (Real.exp (c * t) - 1))
      (-(c ^ 2 * (Real.exp (c * t) / (Real.exp (c * t) - 1) ^ 2))) t := by
  have hE : 1 < Real.exp (c * t) := Real.one_lt_exp_iff.2 (by positivity)
  have h2 : Real.exp (c * t) - 1 ≠ 0 := by linarith
  have h1 : HasDerivAt (fun t => c * t) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have h := (hasDerivAt_const t c).div (h1.exp.sub_const 1) h2
  convert h using 1
  field_simp
  ring

/-- For `0 < b < a`, `t ↦ log(1 - e^(-bt)) - log(1 - e^(-at))` is strictly concave on `(0, ∞)`. -/
theorem strictConcaveOn_ell_sub {b a : ℝ} (hb : 0 < b) (hba : b < a) :
    StrictConcaveOn ℝ (Ioi 0) (fun t => ell b t - ell a t) := by
  have ha : 0 < a := hb.trans hba
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => ell b t - ell a t)
      (b / (Real.exp (b * t) - 1) - a / (Real.exp (a * t) - 1)) t := fun t ht =>
    (hasDerivAt_ell hb ht).sub (hasDerivAt_ell ha ht)
  have hd' : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt
      (fun t => b / (Real.exp (b * t) - 1) - a / (Real.exp (a * t) - 1))
      (-(b ^ 2 * (Real.exp (b * t) / (Real.exp (b * t) - 1) ^ 2)) -
        -(a ^ 2 * (Real.exp (a * t) / (Real.exp (a * t) - 1) ^ 2))) t := fun t ht =>
    (hasDerivAt_phi hb ht).sub (hasDerivAt_phi ha ht)
  have hanti : StrictAntiOn
      (fun t => b / (Real.exp (b * t) - 1) - a / (Real.exp (a * t) - 1)) (Ioi 0) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
      (fun t ht => (hd' t ht).continuousAt.continuousWithinAt) fun t ht => ?_
    rw [interior_Ioi] at ht
    rw [(hd' t ht).deriv]
    linarith [sq_mul_exp_div_lt hb hba (mem_Ioi.1 ht)]
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  rw [(hd s hs).deriv, (hd t ht).deriv]
  exact hanti hs ht hst

variable {q p x : ℝ}

/-- `t ↦ log(1 - q^t)` is monotone on `(0, ∞)` for `0 < q < 1`. -/
theorem g_mono (hq0 : 0 < q) (hq1 : q < 1) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    g q s ≤ g q t := by
  unfold g
  refine Real.log_le_log (one_sub_rpow_pos hq0 hq1 hs) ?_
  linarith [Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hst]

/-- `g q 1 = log(1 - q)`. -/
theorem g_one (q : ℝ) : g q 1 = Real.log (1 - q) := by
  simp [g]

/-- The difference of the logarithmic factors for the bases `p` and `q`. -/
def G (q p t : ℝ) : ℝ := g p t - g q t

/-- For `0 < q < p < 1`, `G(t) = log(1 - p^t) - log(1 - q^t)` is strictly concave on `(0, ∞)`. -/
theorem strictConcaveOn_G (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) :
    StrictConcaveOn ℝ (Ioi 0) (G q p) := by
  have hp0 : 0 < p := hq0.trans hqp
  have hb : 0 < -Real.log p := neg_pos.2 (Real.log_neg hp0 hp1)
  have hba : -Real.log p < -Real.log q := neg_lt_neg (Real.log_lt_log hq0 hqp)
  have e : G q p = fun t => ell (-Real.log p) t - ell (-Real.log q) t := by
    funext t
    simp only [G, g, ell, Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hq0, neg_mul, neg_neg]
  rw [e]
  exact strictConcaveOn_ell_sub hb hba

/-- Strict-concavity step for `0 < x < 1`: `G(x + s) + (1 - x) G(s + 2) < (2 - x) G(s + 1)`. -/
theorem G_step_left (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) (hx0 : 0 < x) (hx1 : x < 1)
    {s : ℝ} (hs : 0 ≤ s) :
    G q p (x + s) + (1 - x) * G q p (s + 2) < (2 - x) * G q p (s + 1) := by
  have h2x : 0 < 2 - x := by linarith
  have h2x' : 2 - x ≠ 0 := h2x.ne'
  have h := (strictConcaveOn_G hq0 hqp hp1).2 (mem_Ioi.2 (by linarith : 0 < x + s))
    (mem_Ioi.2 (by linarith : (0 : ℝ) < s + 2)) (by intro h; linarith)
    (div_pos one_pos h2x) (div_pos (by linarith : (0 : ℝ) < 1 - x) h2x)
    (by field_simp; ring)
  simp only [smul_eq_mul] at h
  have hpt : 1 / (2 - x) * (x + s) + (1 - x) / (2 - x) * (s + 2) = s + 1 := by
    field_simp
    ring
  rw [hpt] at h
  have h' := mul_lt_mul_of_pos_left h h2x
  have he : (2 - x) * (1 / (2 - x) * G q p (x + s) + (1 - x) / (2 - x) * G q p (s + 2)) =
      G q p (x + s) + (1 - x) * G q p (s + 2) := by
    field_simp
  linarith

/-- Strict-concavity step for `1 < x < 2`: `(2 - x) G(s + 1) + (x - 1) G(s + 2) < G(x + s)`. -/
theorem G_step_right (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) (hx : 1 < x) (hx2 : x < 2)
    {s : ℝ} (hs : 0 ≤ s) :
    (2 - x) * G q p (s + 1) + (x - 1) * G q p (s + 2) < G q p (x + s) := by
  have h := (strictConcaveOn_G hq0 hqp hp1).2 (mem_Ioi.2 (by linarith : (0 : ℝ) < s + 1))
    (mem_Ioi.2 (by linarith : (0 : ℝ) < s + 2)) (by intro h; linarith)
    (by linarith : (0 : ℝ) < 2 - x) (by linarith : (0 : ℝ) < x - 1) (by ring)
  simp only [smul_eq_mul] at h
  have hpt : (2 - x) * (s + 1) + (x - 1) * (s + 2) = x + s := by ring
  rwa [hpt] at h

/-- The difference of the logarithms of the truncations `r p x N` and `r q x N`. -/
def T (q p x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, (G q p ((k : ℝ) + 1) - G q p (x + k)) + (1 - x) * G q p 1

/-- Recurrence `T(N + 1) = T(N) + G(N + 1) - G(x + N)`. -/
theorem T_succ (q p x : ℝ) (N : ℕ) :
    T q p x (N + 1) = T q p x N + G q p ((N : ℝ) + 1) - G q p (x + N) := by
  unfold T
  rw [sum_range_succ]
  ring

/-- `T(1) = (2 - x) G(1) - G(x)`. -/
theorem T_one (q p x : ℝ) : T q p x 1 = (2 - x) * G q p 1 - G q p x := by
  simp [T]
  ring

/-- `r p x N = r q x N · exp(T q p x N)`. -/
theorem r_eq (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) (hx0 : 0 < x) (N : ℕ) :
    r p x N = r q x N * Real.exp (T q p x N) := by
  have hp0 : 0 < p := hq0.trans hqp
  have hq1 : q < 1 := hqp.trans hp1
  have hl : Real.log (r p x N) - Real.log (r q x N) = T q p x N := by
    rw [log_r hp0 hp1 hx0, log_r hq0 hq1 hx0, ← g_one, ← g_one]
    simp only [T, G, D, sum_sub_distrib]
    ring
  rw [← hl, Real.exp_sub, Real.exp_log (r_pos hp0 hp1 hx0 N),
    Real.exp_log (r_pos hq0 hq1 hx0 N)]
  field_simp [(r_pos hq0 hq1 hx0 N).ne']

/-- `G(N + 1) → 0` as `N → ∞`. -/
theorem tendsto_G (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) :
    Tendsto (fun N : ℕ => G q p ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hp0 : 0 < p := hq0.trans hqp
  have hq1 : q < 1 := hqp.trans hp1
  have h := ((tendsto_g_nat hp0 hp1).sub (tendsto_g_nat hq0 hq1)).comp
    (tendsto_add_atTop_nat 1)
  simp only [sub_zero] at h
  refine h.congr fun N => ?_
  simp [G]

/-- The truncations `r q x N` converge to `Re Γ_q(x)`. -/
theorem tendsto_r_re (hq0 : 0 < q) (hq1 : q < 1) (hx0 : 0 < x) :
    Tendsto (r q x) atTop (𝓝 (qGamma q x).re) :=
  ((Complex.continuous_re.tendsto _).comp (tendsto_r_complex hq0 hq1 hx0)).congr
    fun N => by simp

/-- `D(N) ≥ g(1) - g(N + 1)` for `0 < x ≤ 2`. -/
theorem D_ge (hq0 : 0 < q) (hq1 : q < 1) (hx0 : 0 < x) (hx2 : x ≤ 2) (N : ℕ) :
    g q 1 - g q ((N : ℝ) + 1) ≤ D q x N := by
  induction N with
  | zero => simp [D]
  | succ N ih =>
    rw [D_succ]
    have := g_mono hq0 hq1 (by positivity : 0 < x + N) (by linarith : x + N ≤ N + 1 + 1)
    push_cast
    linarith

/-- `Re Γ_q(x) > 0` for `0 < q < 1`, `0 < x ≤ 2`. -/
theorem qGamma_re_pos (hq0 : 0 < q) (hq1 : q < 1) (hx0 : 0 < x) (hx2 : x ≤ 2) :
    0 < (qGamma q x).re := by
  have hlow : ∀ N, Real.exp (g q 1 + (1 - x) * Real.log (1 - q)) ≤ r q x N := by
    intro N
    rw [← Real.exp_log (r_pos hq0 hq1 hx0 N), log_r hq0 hq1 hx0]
    refine Real.exp_le_exp.2 ?_
    linarith [D_ge hq0 hq1 hx0 hx2 N, g_nonpos hq0 hq1 (by positivity : (0 : ℝ) < N + 1)]
  exact (Real.exp_pos _).trans_le (ge_of_tendsto' (tendsto_r_re hq0 hq1 hx0) hlow)

/-- For `0 < x < 1`, `T(N) - (1 - x) G(N + 1)` is bounded below by its value at `N = 1`. -/
theorem T_lower (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ N, 1 ≤ N →
      T q p x 1 - (1 - x) * G q p 2 ≤ T q p x N - (1 - x) * G q p ((N : ℝ) + 1) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    have := G_step_left hq0 hqp hp1 hx0 hx1 (N.cast_nonneg : (0 : ℝ) ≤ N)
    rw [T_succ q p x N]
    push_cast
    rw [show (N : ℝ) + 1 + 1 = N + 2 by ring]
    linarith

/-- For `1 < x < 2`, `T(N) + (x - 1) G(N + 1)` is bounded above by its value at `N = 1`. -/
theorem T_upper (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) (hx : 1 < x) (hx2 : x < 2) :
    ∀ N, 1 ≤ N →
      T q p x N + (x - 1) * G q p ((N : ℝ) + 1) ≤ T q p x 1 + (x - 1) * G q p 2 := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    have := G_step_right hq0 hqp hp1 hx hx2 (N.cast_nonneg : (0 : ℝ) ≤ N)
    rw [T_succ q p x N]
    push_cast
    rw [show (N : ℝ) + 1 + 1 = N + 2 by ring]
    linarith

end QGammaMono

/-- DLMF 5.18.8: `Γ_q(x) < Γ_r(x)` for `0 < q < r < 1` and `0 < x < 1`. -/
@[dlmf 5.18.E8]
theorem qGamma_mono_left {q r x : ℝ} (hq0 : 0 < q) (hqr : q < r) (hr1 : r < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (qGamma q x).re < (qGamma r x).re := by
  open QGammaMono QGammaLimit in
  have hp0 : 0 < r := hq0.trans hqr
  have hq1 : q < 1 := hqr.trans hr1
  set c := T q r x 1 - (1 - x) * G q r 2 with hc_def
  have hc : 0 < c := by
    have h := G_step_left hq0 hqr hr1 hx0 hx1 (le_refl (0 : ℝ))
    rw [hc_def, T_one]
    simp only [add_zero, zero_add] at h
    linarith
  have hlo : Tendsto
      (fun N => QGammaLimit.r q x N * Real.exp (c + (1 - x) * G q r ((N : ℝ) + 1)))
      atTop (𝓝 ((qGamma q x).re * Real.exp (c + (1 - x) * 0))) :=
    (tendsto_r_re hq0 hq1 hx0).mul
      (((tendsto_G hq0 hqr hr1).const_mul (1 - x)).const_add c).rexp
  rw [mul_zero, add_zero] at hlo
  have hle : (qGamma q x).re * Real.exp c ≤ (qGamma r x).re := by
    refine le_of_tendsto_of_tendsto hlo (tendsto_r_re hp0 hr1 hx0) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [r_eq hq0 hqr hr1 hx0 N]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (r_pos hq0 hq1 hx0 N).le
    linarith [T_lower hq0 hqr hr1 hx0 hx1 N hN]
  exact (lt_mul_of_one_lt_right (qGamma_re_pos hq0 hq1 hx0 (by linarith))
    (Real.one_lt_exp_iff.2 hc)).trans_le hle

/-- Strict decrease of the q-Gamma function in its base when `1 < x < 2`.
At `x = 2` the function is constant, so the upper restriction is essential. -/
@[dlmf 5.18.E9]
theorem qGamma_mono_right {q r x : ℝ} (hq0 : 0 < q) (hqr : q < r) (hr1 : r < 1)
    (hx : 1 < x) (hx2 : x < 2) :
    (qGamma r x).re < (qGamma q x).re := by
  open QGammaMono QGammaLimit in
  have hp0 : 0 < r := hq0.trans hqr
  have hq1 : q < 1 := hqr.trans hr1
  have hx0 : 0 < x := by linarith
  set c := T q r x 1 + (x - 1) * G q r 2 with hc_def
  have hc : c < 0 := by
    have h := G_step_right hq0 hqr hr1 hx hx2 (le_refl (0 : ℝ))
    rw [hc_def, T_one]
    simp only [add_zero, zero_add] at h
    linarith
  have hup : Tendsto
      (fun N => QGammaLimit.r q x N * Real.exp (c - (x - 1) * G q r ((N : ℝ) + 1)))
      atTop (𝓝 ((qGamma q x).re * Real.exp (c - (x - 1) * 0))) :=
    (tendsto_r_re hq0 hq1 hx0).mul
      (((tendsto_G hq0 hqr hr1).const_mul (x - 1)).const_sub c).rexp
  rw [mul_zero, sub_zero] at hup
  have hle : (qGamma r x).re ≤ (qGamma q x).re * Real.exp c := by
    refine le_of_tendsto_of_tendsto (tendsto_r_re hp0 hr1 hx0) hup ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [r_eq hq0 hqr hr1 hx0 N]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (r_pos hq0 hq1 hx0 N).le
    linarith [T_upper hq0 hqr hr1 hx hx2 N hN]
  exact hle.trans_lt (mul_lt_of_lt_one_right (qGamma_re_pos hq0 hq1 hx0 hx2.le)
    (Real.exp_lt_one_iff.2 hc))

end DLMF.Gamma
