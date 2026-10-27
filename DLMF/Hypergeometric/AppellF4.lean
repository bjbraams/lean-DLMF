/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Saalschutz
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Appell's function F₄ and Bailey's product formula

We define the coefficients `appF4Coeff` and the totalized double-series function `appF4` of
Appell's fourth function (DLMF 16.13.4), and prove Bailey's product formula
`₂F₁(a,b;c;X) ₂F₁(a,b;c';Y) = F₄(a,b;c,c';X(1-Y),Y(1-X))` for `c + c' = a + b + 1`,
`Re c, Re c' > 0` and small `X`, `Y` (`appF4_bailey`, `appF4_eq_mul`).

The proof expands `X^m (1-X)^n` and `Y^n (1-Y)^m` binomially and compares coefficients of
`X^M Y^N` in an absolutely summable four-index family. The coefficient identity
(`appF4_coeff`) reduces, after a Chu–Vandermonde summation (`appF4_inner`), to the
Pfaff–Saalschütz convolution `regularized_saalschutz_convolution`; the balancing condition
`c + c' = a + b + 1` is what makes the inner `₃F₂` Saalschützian. Absolute convergence uses
the crude bound `|(a)_{m+n}(b)_{m+n}/((c)_m(c')_n m!n!)| ≤ Q^{m+n}` (`appF4Coeff_norm_le`).
-/

@[expose] public section

open Complex Filter
open scoped Topology Nat

noncomputable section

namespace DLMF.Hypergeometric

/-- Reflection of a Pochhammer symbol: `(1 - y - m)_m = (-1)^m (y)_m`. -/
lemma appF4_poch_reflect (y : ℂ) (m : ℕ) : poch (1 - y - m) m = (-1 : ℂ) ^ m * poch y m := by
  exact poch_reflect y m

/-- The binomial theorem for rising factorials (Chu–Vandermonde). -/
lemma appF4_poch_add_binomial (u v : ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * poch u j * poch v (n - j) = poch (u + v) n := by
  exact poch_add_binomial_sum u v n

/-- The coefficients of Appell's `F₄`:
`(a)_{m+n} (b)_{m+n} / ((c)_m (c')_n m! n!)`. -/
noncomputable def appF4Coeff (a b c c' : ℂ) (m n : ℕ) : ℂ :=
  poch a (m + n) * poch b (m + n) / (poch c m * poch c' n * (m ! * n !))

/-- One term of the coefficient comparison in Bailey's formula. -/
lemma appF4_term (a b c c' : ℂ) (hc : ∀ k, poch c k ≠ 0) (hc' : ∀ k, poch c' k ≠ 0)
    (t d e f : ℕ) :
    appF4Coeff a b c c' (t + d) (e + f) * ((-1) ^ e * ((e + f).choose e : ℂ)) *
        ((-1) ^ d * ((t + d).choose d : ℂ)) =
      poch a (t + d + e + f) * poch b (t + d + e + f) * ((d + e).choose d : ℂ) *
        poch (1 - c' - ((d + e + f : ℕ) : ℂ)) d * poch (1 - c - ((t + d + e : ℕ) : ℂ)) e /
        (poch c (t + d + e) * poch c' (d + e + f) * (f ! * t ! * (d + e)!)) := by
  unfold appF4Coeff
  have hC : poch c (t + d + e) =
      poch c (t + d) * ((-1) ^ e * poch (1 - c - ((t + d + e : ℕ) : ℂ)) e) := by
    rw [poch_add]
    congr 1
    have := appF4_poch_reflect (c + ((t + d : ℕ) : ℂ)) e
    rw [show 1 - (c + ((t + d : ℕ) : ℂ)) - (e : ℂ) = 1 - c - ((t + d + e : ℕ) : ℂ) by
      push_cast; ring] at this
    rw [this, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  have hC' : poch c' (d + e + f) = poch c' (e + f) *
      ((-1) ^ d * poch (1 - c' - ((d + e + f : ℕ) : ℂ)) d) := by
    rw [show d + e + f = (e + f) + d by ring, poch_add]
    congr 1
    have := appF4_poch_reflect (c' + ((e + f : ℕ) : ℂ)) d
    rw [show 1 - (c' + ((e + f : ℕ) : ℂ)) - (d : ℂ) = 1 - c' - (((e + f) + d : ℕ) : ℂ) by
      push_cast; ring] at this
    rw [this, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  rw [hC, hC', show t + d + (e + f) = t + d + e + f by ring,
    Nat.cast_choose ℂ (show e ≤ e + f by omega), Nat.cast_choose ℂ (show d ≤ t + d by omega),
    Nat.cast_choose ℂ (show d ≤ d + e by omega),
    show e + f - e = f by omega, show t + d - d = t by omega, show d + e - d = e by omega]
  have h1 := hc (t + d)
  have h2 := hc' (e + f)
  have hr1 : poch (1 - c - ((t + d + e : ℕ) : ℂ)) e ≠ 0 := by
    intro h; have := hc (t + d + e); rw [hC, h] at this; simp at this
  have hr2 : poch (1 - c' - ((d + e + f : ℕ) : ℂ)) d ≠ 0 := by
    intro h; have := hc' (d + e + f); rw [hC', h] at this; simp at this
  have hs : ((-1 : ℂ) ^ e) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hs' : ((-1 : ℂ) ^ d) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have he : ((-1 : ℂ) ^ e) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hd : ((-1 : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (by norm_num)
  have f1 : ((t + d)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f2 : ((e + f)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f3 : ((d + e)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f4 : (e ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f5 : (f ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f6 : (d ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f7 : (t ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  rw [hs, hs', mul_one, mul_one]


/-- The summand of the coefficient comparison in Bailey's formula. -/
noncomputable def appF4Term (a b c c' : ℂ) (M N m n : ℕ) : ℂ :=
  appF4Coeff a b c c' m n * ((-1) ^ (M - m) * (n.choose (M - m) : ℂ)) *
    ((-1) ^ (N - n) * (m.choose (N - n) : ℂ))

/-- The inner (Chu–Vandermonde) sum in Bailey's coefficient comparison. -/
lemma appF4_inner {a b c c' : ℂ} (hcc : c + c' = a + b + 1) (hc : ∀ k, poch c k ≠ 0)
    (hc' : ∀ k, poch c' k ≠ 0) (t s f : ℕ) :
    ∑ d ∈ Finset.range (s + 1), appF4Term a b c c' (t + s) (s + f) (t + d) (s + f - d) =
      poch a (t + s + f) * poch b (t + s + f) *
        poch (1 - a - b - ((t + s : ℕ) : ℂ) - ((s + f : ℕ) : ℂ)) s /
        (poch c (t + s) * poch c' (s + f) * (f ! * t ! * s !)) := by
  have hv := appF4_poch_add_binomial (1 - c' - ((s + f : ℕ) : ℂ)) (1 - c - ((t + s : ℕ) : ℂ)) s
  rw [show 1 - c' - ((s + f : ℕ) : ℂ) + (1 - c - ((t + s : ℕ) : ℂ)) =
    1 - a - b - ((t + s : ℕ) : ℂ) - ((s + f : ℕ) : ℂ) by linear_combination (-1 : ℂ) * hcc] at hv
  rw [← hv, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hds : d ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  obtain ⟨e, rfl⟩ : ∃ e, s = d + e := ⟨s - d, by omega⟩
  unfold appF4Term
  rw [show t + (d + e) - (t + d) = e by omega, show d + e + f - d = e + f by omega,
    show d + e + f - (e + f) = d by omega, appF4_term a b c c' hc hc' t d e f,
    show d + e - d = e by omega, show t + d + e + f = t + (d + e) + f by ring,
    show t + d + e = t + (d + e) by ring]
  ring


/-- The outer (Pfaff–Saalschütz) sum in Bailey's coefficient comparison, for `M ≤ N`. -/
lemma appF4_outer (a b c c' : ℂ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ t ∈ Finset.range (M + 1), poch a (N + t) * poch b (N + t) *
        poch (1 - a - b - (M : ℂ) - (N : ℂ)) (M - t) /
        (poch c M * poch c' N * ((N - (M - t))! * t ! * (M - t)!)) =
      gaussHGCoeff a b c M * gaussHGCoeff a b c' N := by
  have h := regularized_saalschutz_convolution (a + N) (b + N) ((N : ℂ) - M + 1) M
  rw [show (N : ℂ) - M + 1 - (a + N) - (b + N) = 1 - a - b - M - N by ring,
    show (N : ℂ) - M + 1 - (a + N) = 1 - a - M by ring,
    show (N : ℂ) - M + 1 - (b + N) = 1 - b - M by ring,
    show (N : ℂ) - M + 1 + M = (N : ℕ) + 1 by ring, Gamma_nat_eq_factorial,
    appF4_poch_reflect, appF4_poch_reflect] at h
  have hG : ∀ k ∈ Finset.range (M + 1), Gamma ((N : ℂ) - M + 1 + k) = ((N - (M - k))! : ℂ) := by
    intro k hk
    have hkM : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show (N : ℂ) - M + 1 + k = ((N - (M - k) : ℕ) : ℂ) + 1 by
      push_cast [Nat.cast_sub hkM, Nat.cast_sub (show M - k ≤ N by omega)]; ring,
      Gamma_nat_eq_factorial]
  rw [Finset.sum_congr rfl fun k hk => by rw [hG k hk]] at h
  unfold gaussHGCoeff
  have hfM : (M ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfN : (N ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have key : ∑ t ∈ Finset.range (M + 1), poch a (N + t) * poch b (N + t) *
        poch (1 - a - b - (M : ℂ) - (N : ℂ)) (M - t) /
        ((N - (M - t))! * t ! * (M - t)!) =
      poch a M * poch b M / M ! * (poch a N * poch b N / N !) := by
    have h2 := congrArg (fun w => poch a N * poch b N * w) h
    simp only [Finset.mul_sum] at h2
    rw [show poch a N * poch b N * ((-1) ^ M * poch a M * ((-1) ^ M * poch b M) / (M ! * N !)) =
      poch a M * poch b M / M ! * (poch a N * poch b N / N !) * ((-1) ^ M) ^ 2 by ring,
      show ((-1 : ℂ) ^ M) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; simp, mul_one] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [poch_add a N t, poch_add b N t]
    have h3 : ((N - (M - t))! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h4 : (t ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h5 : ((M - t)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  rw [show (∑ t ∈ Finset.range (M + 1), poch a (N + t) * poch b (N + t) *
        poch (1 - a - b - (M : ℂ) - (N : ℂ)) (M - t) /
        (poch c M * poch c' N * ((N - (M - t))! * t ! * (M - t)!))) =
      (∑ t ∈ Finset.range (M + 1), poch a (N + t) * poch b (N + t) *
        poch (1 - a - b - (M : ℂ) - (N : ℂ)) (M - t) /
        ((N - (M - t))! * t ! * (M - t)!)) / (poch c M * poch c' N) by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun t _ => ?_; ring, key]
  ring


/-- Bailey's coefficient identity for `M ≤ N`. -/
lemma appF4_coeff_of_le {a b c c' : ℂ} (hcc : c + c' = a + b + 1) (hc : ∀ k, poch c k ≠ 0)
    (hc' : ∀ k, poch c' k ≠ 0) {M N : ℕ} (hMN : M ≤ N) :
    ∑ m ∈ Finset.range (M + 1), ∑ n ∈ Finset.range (N + 1), appF4Term a b c c' M N m n =
      gaussHGCoeff a b c M * gaussHGCoeff a b c' N := by
  have h1 : ∀ m ∈ Finset.range (M + 1), ∑ n ∈ Finset.range (N + 1), appF4Term a b c c' M N m n =
      ∑ k ∈ Finset.range (m + 1), appF4Term a b c c' M N m (N - m + k) := by
    intro m hm
    have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [show N + 1 = (N - m) + (m + 1) by omega, Finset.sum_range_add]
    rw [Finset.sum_eq_zero (fun n hn => ?_), zero_add]
    have hn' : n < N - m := Finset.mem_range.mp hn
    unfold appF4Term
    rw [Nat.choose_eq_zero_of_lt (show m < N - n by omega)]
    simp
  rw [Finset.sum_congr rfl h1]
  have h2 := Finset.sum_range_diag_flip (M + 1) (fun t d => appF4Term a b c c' M N (t + d) (N - d))
  rw [show (∑ m ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (m + 1),
      appF4Term a b c c' M N m (N - m + k)) = ∑ m ∈ Finset.range (M + 1),
      ∑ k ∈ Finset.range (m + 1), appF4Term a b c c' M N (k + (m - k)) (N - (m - k)) by
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun k hk => ?_
    have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show k + (m - k) = m by omega, show N - (m - k) = N - m + k by omega], h2,
    ← appF4_outer a b c c' hMN]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htM : t ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  have h3 := appF4_inner hcc hc hc' t (M - t) (N - (M - t))
  rw [show t + (M - t) + (N - (M - t)) = N + t by omega, show t + (M - t) = M by omega,
    show M - t + (N - (M - t)) = N by omega] at h3
  rw [show M + 1 - t = M - t + 1 by omega, h3]

/-- **Bailey's coefficient identity**: for `c + c' = a + b + 1` the coefficient of `XᴹYᴺ` in
`F₄(a,b;c,c';X(1-Y),Y(1-X))` is the product of the Gauss coefficients. -/
theorem appF4_coeff {a b c c' : ℂ} (hcc : c + c' = a + b + 1) (hc : ∀ k, poch c k ≠ 0)
    (hc' : ∀ k, poch c' k ≠ 0) (M N : ℕ) :
    ∑ m ∈ Finset.range (M + 1), ∑ n ∈ Finset.range (N + 1), appF4Term a b c c' M N m n =
      gaussHGCoeff a b c M * gaussHGCoeff a b c' N := by
  rcases le_total M N with h | h
  · exact appF4_coeff_of_le hcc hc hc' h
  · rw [Finset.sum_comm, mul_comm]
    rw [← appF4_coeff_of_le (by rw [add_comm]; exact hcc) hc' hc h]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    unfold appF4Term appF4Coeff
    rw [add_comm n m]
    ring


/-- `|(μ)_m| ≤ (1 + |μ|)^m m!`. -/
theorem appF4_norm_poch_le (μ : ℂ) (m : ℕ) : ‖poch μ m‖ ≤ (1 + ‖μ‖) ^ m * m ! := by
  induction m with
  | zero => simp [poch_zero]
  | succ m ih =>
    rw [poch_succ, norm_mul, Nat.factorial_succ, pow_succ]
    have h1 : ‖μ + m‖ ≤ (1 + ‖μ‖) * (m + 1) := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_natCast]
      nlinarith [norm_nonneg μ, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    push_cast
    calc ‖poch μ m‖ * ‖μ + m‖ ≤ ((1 + ‖μ‖) ^ m * m !) * ((1 + ‖μ‖) * (m + 1)) :=
          mul_le_mul ih h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- `k! ≤ (1 + 1/Re c)^k |(c)_k|` for `Re c > 0`. -/
lemma appF4_factorial_le_norm_poch {c : ℂ} (hc : 0 < c.re) (k : ℕ) :
    (k ! : ℝ) ≤ (1 + 1 / c.re) ^ k * ‖poch c k‖ := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ, norm_mul, Nat.factorial_succ, pow_succ]
    have h1 : (c.re + k) ≤ ‖c + k‖ := by
      have := Complex.re_le_norm (c + k)
      simpa using this
    have h2 : ((k : ℝ) + 1) ≤ (1 + 1 / c.re) * ‖c + k‖ := by
      have h3 : ((k : ℝ) + 1) ≤ (1 + 1 / c.re) * (c.re + k) := by
        rw [add_mul, one_div, inv_mul_eq_div, add_div, div_self hc.ne']
        have : 0 ≤ (k : ℝ) / c.re := by positivity
        linarith
      exact h3.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    push_cast
    calc ((k : ℝ) + 1) * k ! ≤ ((1 + 1 / c.re) * ‖c + k‖) * ((1 + 1 / c.re) ^ k * ‖poch c k‖) :=
          mul_le_mul h2 ih (by positivity) (by positivity)
      _ = _ := by ring

/-- A geometric bound for the `F₄` coefficients. -/
lemma appF4Coeff_norm_le (a b : ℂ) {c c' : ℂ} (hc : 0 < c.re) (hc' : 0 < c'.re) (m n : ℕ) :
    ‖appF4Coeff a b c c' m n‖ ≤ (4 * (1 + ‖a‖) * (1 + ‖b‖) * (1 + 1 / c.re)) ^ m *
      (4 * (1 + ‖a‖) * (1 + ‖b‖) * (1 + 1 / c'.re)) ^ n := by
  have hA := appF4_norm_poch_le a (m + n)
  have hB := appF4_norm_poch_le b (m + n)
  have hC := appF4_factorial_le_norm_poch hc m
  have hC' := appF4_factorial_le_norm_poch hc' n
  have hL : ((m + n)! : ℝ) ≤ 2 ^ (m + n) * (m ! * n !) := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
    rw [Nat.add_sub_cancel_left] at this
    have h2 : (((m + n).choose m : ℕ) : ℝ) ≤ 2 ^ (m + n) := by
      exact_mod_cast Nat.choose_le_two_pow _ _
    calc ((m + n)! : ℝ) = ((m + n).choose m : ℝ) * (m ! * n !) := by
          rw [← this]; push_cast; ring
      _ ≤ _ := by gcongr
  have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  have hn : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hpc : 0 < ‖poch c m‖ := by
    by_contra h; push Not at h
    have : ‖poch c m‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [this, mul_zero] at hC; linarith
  have hpc' : 0 < ‖poch c' n‖ := by
    by_contra h; push Not at h
    have : ‖poch c' n‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [this, mul_zero] at hC'; linarith
  unfold appF4Coeff
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_natCast,
    Complex.norm_natCast, div_le_iff₀ (by positivity)]
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hL0 : (0 : ℝ) ≤ ((m + n)! : ℝ) := by positivity
  calc ‖poch a (m + n)‖ * ‖poch b (m + n)‖
      ≤ ((1 + ‖a‖) ^ (m + n) * (m + n)!) * ((1 + ‖b‖) ^ (m + n) * (m + n)!) :=
        mul_le_mul hA hB (norm_nonneg _) (by positivity)
    _ ≤ ((1 + ‖a‖) ^ (m + n) * (2 ^ (m + n) * (m ! * n !))) *
        ((1 + ‖b‖) ^ (m + n) * (2 ^ (m + n) * (m ! * n !))) := by gcongr
    _ = (1 + ‖a‖) ^ (m + n) * (1 + ‖b‖) ^ (m + n) * 4 ^ (m + n) * (m ! * n !) * (m ! * n !) := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
    _ ≤ (1 + ‖a‖) ^ (m + n) * (1 + ‖b‖) ^ (m + n) * 4 ^ (m + n) * (m ! * n !) *
        (((1 + 1 / c.re) ^ m * ‖poch c m‖) * ((1 + 1 / c'.re) ^ n * ‖poch c' n‖)) := by gcongr
    _ = _ := by simp only [mul_pow, pow_add]; ring


/-- The coefficient of `X^M` in `X^m (1 - X)^n`. -/
noncomputable def appF4E (m n M : ℕ) : ℂ :=
  if m ≤ M then (-1) ^ (M - m) * (n.choose (M - m) : ℂ) else 0

theorem appF4E_eq_zero_of_lt {m n M : ℕ} (h : m + n < M) : appF4E m n M = 0 := by
  unfold appF4E
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- `X^m (1 - X)^n = ∑_M appF4E m n M X^M`. -/
theorem appF4E_sum (m n : ℕ) (X : ℂ) :
    ∑ M ∈ Finset.range (m + n + 1), appF4E m n M * X ^ M = X ^ m * (1 - X) ^ n := by
  rw [show m + n + 1 = m + (n + 1) by ring, Finset.sum_range_add,
    Finset.sum_eq_zero (fun M hM => by
      unfold appF4E
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := Finset.mem_range.mp hM; omega))]
      simp), zero_add,
    show (1 - X) = -X + 1 by ring, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold appF4E
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Nat.add_sub_cancel_left, pow_add, neg_pow,
    one_pow]
  ring

/-- A bound for one factor of the four-index family. -/
theorem appF4E_norm_le (m n M : ℕ) {X : ℂ} (hX : ‖X‖ ≤ 1) :
    ‖appF4E m n M * X ^ M‖ ≤ 2 ^ n * Real.sqrt ‖X‖ ^ m * Real.sqrt ‖X‖ ^ M := by
  unfold appF4E
  split_ifs with h
  · rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast,
      norm_pow]
    have h1 : ((n.choose (M - m) : ℕ) : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow _ _
    have hs0 : 0 ≤ Real.sqrt ‖X‖ := Real.sqrt_nonneg _
    have hs1 : Real.sqrt ‖X‖ ≤ 1 := Real.sqrt_le_one.mpr hX
    have h2 : ‖X‖ ^ M ≤ Real.sqrt ‖X‖ ^ m * Real.sqrt ‖X‖ ^ M := by
      calc ‖X‖ ^ M = (Real.sqrt ‖X‖ ^ 2) ^ M := by rw [Real.sq_sqrt (norm_nonneg _)]
        _ = Real.sqrt ‖X‖ ^ (2 * M) := by rw [← pow_mul]
        _ ≤ Real.sqrt ‖X‖ ^ (m + M) := pow_le_pow_of_le_one hs0 hs1 (by omega)
        _ = _ := pow_add _ _ _
    calc ((n.choose (M - m) : ℕ) : ℝ) * ‖X‖ ^ M ≤ 2 ^ n * (Real.sqrt ‖X‖ ^ m * Real.sqrt ‖X‖ ^ M) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring
  · simp only [zero_mul, norm_zero]; positivity

/-- The four-index family behind Bailey's formula. -/
noncomputable def appF4Fam (a b c c' X Y : ℂ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  appF4Coeff a b c c' p.1.1 p.1.2 * (appF4E p.1.1 p.1.2 p.2.1 * X ^ p.2.1) *
    (appF4E p.1.2 p.1.1 p.2.2 * Y ^ p.2.2)


/-- **Appell's function `F₄`** (DLMF 16.13.4), as the sum of its double series
`∑ (a)_{m+n}(b)_{m+n}/((c)_m(c')_n m! n!) sᵐ tⁿ` (totalized to `0` where it diverges). -/
@[dlmf 16.13.E4]
noncomputable def appF4 (a b c c' s t : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, appF4Coeff a b c c' p.1 p.2 * s ^ p.1 * t ^ p.2

/-- **Bailey's product formula**: for `c + c' = a + b + 1` (and `Re c, Re c' > 0`),
`₂F₁(a,b;c;X) ₂F₁(a,b;c';Y) = F₄(a,b;c,c';X(1-Y),Y(1-X))` for small `X`, `Y`, the double
series of `F₄` converging there. -/
@[dlmf 16.16.E6]
theorem appF4_bailey {a b c c' : ℂ} (hcc : c + c' = a + b + 1) (hc : 0 < c.re)
    (hc' : 0 < c'.re) : ∃ δ > 0, ∀ X Y : ℂ, ‖X‖ < δ → ‖Y‖ < δ →
      HasSum (fun p : ℕ × ℕ => appF4Coeff a b c c' p.1 p.2 * (X * (1 - Y)) ^ p.1 *
        (Y * (1 - X)) ^ p.2) (₂F₁ a b c X * ₂F₁ a b c' Y) := by
  set Q1 := 4 * (1 + ‖a‖) * (1 + ‖b‖) * (1 + 1 / c.re) with hQ1
  set Q2 := 4 * (1 + ‖a‖) * (1 + ‖b‖) * (1 + 1 / c'.re) with hQ2
  set Q := max Q1 Q2 with hQ
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hQ1pos : 1 ≤ Q1 := by
    have : 0 < 1 / c.re := by positivity
    rw [hQ1]; nlinarith [mul_nonneg ha hb]
  have hQ1Q : Q1 ≤ Q := le_max_left _ _
  have hQ2Q : Q2 ≤ Q := le_max_right _ _
  have hQ0 : 0 < Q := by linarith
  have hQ20 : 0 ≤ Q2 := by rw [hQ2]; positivity
  refine ⟨1 / (16 * Q ^ 2), by positivity, fun X Y hX hY => ?_⟩
  have hpc : ∀ k, poch c k ≠ 0 := poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hc)
  have hpc' : ∀ k, poch c' k ≠ 0 := poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hc')
  have hsq : ∀ W : ℂ, ‖W‖ < 1 / (16 * Q ^ 2) → Real.sqrt ‖W‖ < 1 / (4 * Q) := by
    intro W hW
    rw [show 1 / (4 * Q) = Real.sqrt (1 / (16 * Q ^ 2)) by
      rw [show 1 / (16 * Q ^ 2) = (1 / (4 * Q)) ^ 2 by field_simp; ring,
        Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_lt_sqrt (norm_nonneg _) hW
  have hδ1 : 1 / (16 * Q ^ 2) ≤ 1 / 16 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hX1 : ‖X‖ ≤ 1 := by linarith
  have hY1 : ‖Y‖ ≤ 1 := by linarith
  set sX := Real.sqrt ‖X‖ with hsX
  set sY := Real.sqrt ‖Y‖ with hsY
  have hsX0 : 0 ≤ sX := Real.sqrt_nonneg _
  have hsY0 : 0 ≤ sY := Real.sqrt_nonneg _
  have hQ4 : 1 / (4 * Q) ≤ 1 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    (by linarith)
  have hsXQ : sX < 1 / (4 * Q) := hsq X hX
  have hsYQ : sY < 1 / (4 * Q) := hsq Y hY
  have hsX1 : sX < 1 := by linarith
  have hsY1 : sY < 1 := by linarith
  set rX := 2 * Q1 * sX with hrX
  set rY := 2 * Q2 * sY with hrY
  have hrX0 : 0 ≤ rX := by positivity
  have hrY0 : 0 ≤ rY := by positivity
  have hQs : ∀ q s : ℝ, 0 ≤ q → q ≤ Q → 0 ≤ s → s < 1 / (4 * Q) → 2 * q * s < 1 := by
    intro q s hq hqQ hs hsQ
    have : Q * s < 1 / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hsQ; nlinarith
    nlinarith
  have hrX1 : rX < 1 := hQs Q1 sX (by linarith) hQ1Q hsX0 hsXQ
  have hrY1 : rY < 1 := hQs Q2 sY hQ20 hQ2Q hsY0 hsYQ
  -- summability of the four-index family
  have hgeo : ∀ u v : ℝ, 0 ≤ u → u < 1 → 0 ≤ v → v < 1 →
      Summable fun p : ℕ × ℕ => u ^ p.1 * v ^ p.2 := fun u v hu0 hu1 hv0 hv1 =>
    (summable_geometric_of_lt_one hu0 hu1).mul_of_nonneg (summable_geometric_of_lt_one hv0 hv1)
      (fun _ => by positivity) (fun _ => by positivity)
  have hD : Summable fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      (rX ^ p.1.1 * rY ^ p.1.2) * (sX ^ p.2.1 * sY ^ p.2.2) :=
    (hgeo rX rY hrX0 hrX1 hrY0 hrY1).mul_of_nonneg (hgeo sX sY hsX0 hsX1 hsY0 hsY1)
      (fun _ => by positivity) (fun _ => by positivity)
  have hsum : Summable (appF4Fam a b c c' X Y) := by
    refine Summable.of_norm_bounded hD fun p => ?_
    obtain ⟨⟨m, n⟩, ⟨M, N⟩⟩ := p
    unfold appF4Fam
    simp only
    rw [norm_mul, norm_mul]
    have h1 := appF4Coeff_norm_le a b hc hc' m n
    have h2 := appF4E_norm_le m n M hX1
    have h3 := appF4E_norm_le n m N hY1
    calc ‖appF4Coeff a b c c' m n‖ * ‖appF4E m n M * X ^ M‖ * ‖appF4E n m N * Y ^ N‖
        ≤ (Q1 ^ m * Q2 ^ n) * (2 ^ n * sX ^ m * sX ^ M) * (2 ^ m * sY ^ n * sY ^ N) := by
          gcongr
      _ = _ := by rw [hrX, hrY]; simp only [mul_pow]; ring
  have hS := hsum.hasSum
  -- fibres over `(m, n)`: the `F₄` series
  have hfib1 : ∀ p : ℕ × ℕ, HasSum (fun q => appF4Fam a b c c' X Y (p, q))
      (appF4Coeff a b c c' p.1 p.2 * (X * (1 - Y)) ^ p.1 * (Y * (1 - X)) ^ p.2) := by
    rintro ⟨m, n⟩
    have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
      (s := Finset.range (m + n + 1) ×ˢ Finset.range (m + n + 1))
      (f := fun q => appF4Fam a b c c' X Y ((m, n), q)) (fun q hq => by
        obtain ⟨M, N⟩ := q
        simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hq
        unfold appF4Fam
        simp only
        rcases hq with h | h
        · rw [appF4E_eq_zero_of_lt (by omega)]; simp
        · rw [appF4E_eq_zero_of_lt (m := n) (n := m) (by omega)]; simp)
    convert hfin using 1
    rw [Finset.sum_product]
    simp only [appF4Fam]
    have h1 := appF4E_sum m n X
    have h2 := appF4E_sum n m Y
    rw [show n + m + 1 = m + n + 1 by ring] at h2
    have : ∑ x ∈ Finset.range (m + n + 1), ∑ y ∈ Finset.range (m + n + 1),
        appF4Coeff a b c c' m n * (appF4E m n x * X ^ x) * (appF4E n m y * Y ^ y) =
        appF4Coeff a b c c' m n * ((∑ x ∈ Finset.range (m + n + 1), appF4E m n x * X ^ x) *
          (∑ y ∈ Finset.range (m + n + 1), appF4E n m y * Y ^ y)) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [this, h1, h2]
    simp only [mul_pow]
    ring
  have hF4 := hS.prod_fiberwise hfib1
  -- fibres over `(M, N)`: the Gauss coefficients
  have hfib2 : ∀ q : ℕ × ℕ, HasSum (fun p => appF4Fam a b c c' X Y (p, q))
      (gaussHGCoeff a b c q.1 * X ^ q.1 * (gaussHGCoeff a b c' q.2 * Y ^ q.2)) := by
    rintro ⟨M, N⟩
    have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
      (s := Finset.range (M + 1) ×ˢ Finset.range (N + 1))
      (f := fun p => appF4Fam a b c c' X Y (p, (M, N))) (fun p hp => by
        obtain ⟨m, n⟩ := p
        simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
        unfold appF4Fam appF4E
        simp only
        rcases hp with h | h
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; simp
        · rw [ite_eq_right_of_eq_false (c := n ≤ N) _ _ (eq_false (by omega))]; simp)
    convert hfin using 1
    rw [Finset.sum_product]
    simp only
    rw [show gaussHGCoeff a b c M * X ^ M * (gaussHGCoeff a b c' N * Y ^ N) =
      (gaussHGCoeff a b c M * gaussHGCoeff a b c' N) * (X ^ M * Y ^ N) by ring,
      ← appF4_coeff hcc hpc hpc' M N, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    unfold appF4Fam appF4Term appF4E
    simp only
    rw [ite_eq_left_of_eq_true _ _ (eq_true hmM), ite_eq_left_of_eq_true _ _ (eq_true hnN)]
    ring
  have hS' : HasSum (fun x : (ℕ × ℕ) × (ℕ × ℕ) => appF4Fam a b c c' X Y (x.2, x.1))
      (∑' p, appF4Fam a b c c' X Y p) :=
    ((Equiv.prodComm (ℕ × ℕ) (ℕ × ℕ)).hasSum_iff (f := appF4Fam a b c c' X Y)).mpr hS
  have hG := hS'.prod_fiberwise hfib2
  -- the product of the two Gauss series
  have hXs := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one (show ‖X‖ < 1 by linarith))
  have hYs := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c').hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one (show ‖Y‖ < 1 by linarith))
  have hprod := hXs.mul hYs hG.summable
  rw [hG.unique hprod] at hF4
  exact hF4

/-- Bailey's product formula in terms of the (totalized) function `appF4`. -/
lemma appF4_eq_mul {a b c c' : ℂ} (hcc : c + c' = a + b + 1) (hc : 0 < c.re)
    (hc' : 0 < c'.re) : ∃ δ > 0, ∀ X Y : ℂ, ‖X‖ < δ → ‖Y‖ < δ →
      appF4 a b c c' (X * (1 - Y)) (Y * (1 - X)) = ₂F₁ a b c X * ₂F₁ a b c' Y := by
  obtain ⟨δ, hδ, h⟩ := appF4_bailey hcc hc hc'
  exact ⟨δ, hδ, fun X Y hX hY => (h X Y hX hY).tsum_eq⟩

end DLMF.Hypergeometric

end
