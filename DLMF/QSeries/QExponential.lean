/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.QBinomial
public import DLMF.QSeries.Heine

/-!
# Euler's second `q`-exponential (Duverney §10.1.3)

`E_q(x) = ∑ q^{n(n-1)/2} xⁿ/(q;q)_n = (-x;q)_∞` for `|q| < 1` and every complex `x`. The proof lets
`N → ∞` in Cauchy's finite `q`-binomial theorem `(-x;q)_N = ∑_k [N k]_q q^{k(k-1)/2} x^k`, by
Tannery's theorem: `[N k]_q = (q^{N-k+1};q)_k/(q;q)_k → 1/(q;q)_k`, with a uniform bound. Together
with Euler's first identity this gives `e_q(x) E_q(-x) = 1`.
-/

@[expose] public section

open Complex Finset Filter
open scoped Topology

noncomputable section

namespace DLMF.QSeries

/-- `|(q^{m+1};q)_k| ≤ exp(1/(1-|q|))`, uniformly in `m` and `k`. -/
theorem norm_qPochhammer_le {q : ℂ} (hq : ‖q‖ < 1) (m k : ℕ) :
    ‖qPochhammer (q * q ^ m) q k‖ ≤ Real.exp (1 / (1 - ‖q‖)) := by
  rw [qPochhammer_eq_prod, norm_prod]
  have hb : ∀ j ∈ range k, ‖1 - q * q ^ m * q ^ j‖ ≤ Real.exp (‖q‖ ^ j) := by
    intro j _
    calc ‖1 - q * q ^ m * q ^ j‖ ≤ 1 + ‖q‖ ^ j := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_one, norm_mul, norm_mul, norm_pow, norm_pow]
          have h1 : ‖q‖ * ‖q‖ ^ m ≤ 1 := by
            have := pow_le_one₀ (n := m) (norm_nonneg q) hq.le
            nlinarith [norm_nonneg q, pow_nonneg (norm_nonneg q) m]
          nlinarith [pow_nonneg (norm_nonneg q) j]
      _ ≤ Real.exp (‖q‖ ^ j) := by linarith [Real.add_one_le_exp (‖q‖ ^ j)]
  calc ∏ j ∈ range k, ‖1 - q * q ^ m * q ^ j‖ ≤ ∏ j ∈ range k, Real.exp (‖q‖ ^ j) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hb
    _ = Real.exp (∑ j ∈ range k, ‖q‖ ^ j) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1 / (1 - ‖q‖)) := by
        rw [Real.exp_le_exp, one_div]
        rw [← tsum_geometric_of_lt_one (norm_nonneg q) hq]
        exact (summable_geometric_of_lt_one (norm_nonneg q) hq).sum_le_tsum _
          (fun _ _ => by positivity)

/-- `1/(q;q)_k` is bounded for `|q| < 1`. -/
theorem exists_norm_recip_qPochhammer_le {q : ℂ} (hq : ‖q‖ < 1) :
    ∃ D, ∀ k, ‖(qPochhammer q q k)⁻¹‖ ≤ D := by
  have h := ((tendsto_qPochhammer (w := q) hq).inv₀
    (qPochhammerInf_ne_zero_of_norm_lt_one hq hq)).norm
  obtain ⟨D, hD⟩ := h.bddAbove_range
  exact ⟨D, fun k => hD ⟨k, rfl⟩⟩

/-- `[k+m, k]_q = (q^{m+1};q)_k / (q;q)_k`. -/
@[dlmf 17.2.E29 "exact: |q|<1, after q*q^n=q^(n+1)"]
theorem qBinom_eq {q : ℂ} (hq : ‖q‖ < 1) (k m : ℕ) :
    qBinom q (k + m) k = qPochhammer (q * q ^ m) q k / qPochhammer q q k := by
  have h := qBinom_mul_qPochhammer q k m
  have hk := qPochhammer_self_ne_zero hq k
  have hm := qPochhammer_self_ne_zero hq m
  rw [add_comm k m, qPochhammer_add q q m k] at h
  rw [add_comm k m]
  field_simp
  apply mul_right_cancel₀ hm
  linear_combination h

/-- `(w;q)_k` is continuous in `w`. -/
theorem continuous_qPochhammer (q : ℂ) (k : ℕ) : Continuous fun w : ℂ => qPochhammer w q k := by
  simp_rw [qPochhammer_eq_prod]; fun_prop

/-- **Euler's second identity** `E_q(x) = ∑ q^{n(n-1)/2} xⁿ/(q;q)_n = (-x;q)_∞` for `|q| < 1` and
every `x` (Duverney (10.33)–(10.34)). -/
@[dlmf 17.5.E1 "exact: Euler q-exponential sum; local phase/exponent adapter proved"]
theorem tsum_qExp {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) :
    ∑' n : ℕ, q ^ n.choose 2 * x ^ n / qPochhammer q q n = qPochhammerInf (-x) q := by
  set f : ℕ → ℕ → ℂ := fun N k => qBinom q N k * q ^ k.choose 2 * x ^ k
  have hfN (N : ℕ) : ∑' k, f N k = qPochhammer (-x) q N := by
    rw [tsum_eq_sum (s := range (N + 1)) (fun k hk => by
      simp only [f, qBinom_eq_zero_of_lt q (by simpa using hk), zero_mul]),
      qPochhammer_eq_sum_qBinom]
    refine sum_congr rfl fun k _ => ?_
    simp only [f]
    have h1 : ((-1 : ℂ)) ^ k * (-x) ^ k = x ^ k := by rw [← mul_pow]; ring
    linear_combination (-(qBinom q N k * q ^ k.choose 2)) * h1
  obtain ⟨D, hD⟩ := exists_norm_recip_qPochhammer_le hq
  set E := Real.exp (1 / (1 - ‖q‖))
  have hlimk (k : ℕ) : Tendsto (fun N => f N k) atTop
      (𝓝 (q ^ k.choose 2 * x ^ k / qPochhammer q q k)) := by
    refine (tendsto_add_atTop_iff_nat k).mp ?_
    have h0 : Tendsto (fun m : ℕ => q * q ^ m) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul q
    have h1 := ((continuous_qPochhammer q k).tendsto 0).comp h0
    simp only [qPochhammer_zero_param] at h1
    refine ((h1.div_const (qPochhammer q q k)).mul_const
      (q ^ k.choose 2 * x ^ k)).congr' ?_ |>.trans ?_
    · exact Eventually.of_forall fun m => by
        simp only [f, Function.comp, add_comm m k, qBinom_eq hq k m]; ring
    · rw [show (1 : ℂ) / qPochhammer q q k * (q ^ k.choose 2 * x ^ k) =
        q ^ k.choose 2 * x ^ k / qPochhammer q q k by ring]
  have hbound : ∀ N k, ‖f N k‖ ≤ E * D * (‖q‖ ^ k.choose 2 * ‖x‖ ^ k) := by
    intro N k
    have hE : 0 ≤ E := (Real.exp_pos _).le
    have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
    rcases lt_or_ge N k with h | h
    · simp only [f, qBinom_eq_zero_of_lt q h, zero_mul, norm_zero]; positivity
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [f, qBinom_eq hq k m, norm_mul, norm_div, norm_pow]
    rw [div_eq_mul_inv, ← norm_inv]
    have h1 := norm_qPochhammer_le hq m k
    have h2 := hD k
    calc ‖qPochhammer (q * q ^ m) q k‖ * ‖(qPochhammer q q k)⁻¹‖ * ‖q‖ ^ k.choose 2 * ‖x‖ ^ k
        ≤ E * D * ‖q‖ ^ k.choose 2 * ‖x‖ ^ k := by gcongr
      _ = _ := by ring
  have hsum : Summable fun k : ℕ => E * D * (‖q‖ ^ k.choose 2 * ‖x‖ ^ k) := by
    refine Summable.mul_left _ (summable_of_ratio_norm_eventually_le (r := 1 / 2)
      (by norm_num) ?_)
    have ht : Tendsto (fun k : ℕ => ‖q‖ ^ k * ‖x‖) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).mul_const ‖x‖
    filter_upwards [ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      Nat.choose_succ_succ', Nat.choose_one_right, pow_add, pow_succ]
    have : 0 ≤ ‖q‖ ^ k.choose 2 * ‖x‖ ^ k := by positivity
    nlinarith
  have hT := tendsto_tsum_of_dominated_convergence hsum hlimk
    (Eventually.of_forall fun N k => hbound N k)
  simp_rw [hfN] at hT
  exact tendsto_nhds_unique hT (tendsto_qPochhammer hq)

/-- `e_q(x) E_q(-x) = 1` for `|x| < 1` (Duverney (10.35)). -/
theorem qExp_mul_qExp {q x : ℂ} (hq : ‖q‖ < 1) (hx : ‖x‖ < 1) :
    (∑' n : ℕ, x ^ n / qPochhammer q q n) *
      (∑' n : ℕ, q ^ n.choose 2 * (-x) ^ n / qPochhammer q q n) = 1 := by
  rw [tsum_qExp hq, neg_neg, tsum_div_qPochhammer hq hx]
  field [qPochhammerInf_ne_zero_of_norm_lt_one hx hq]

end DLMF.QSeries

end
