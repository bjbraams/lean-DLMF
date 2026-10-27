/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Binomial

/-!
# Real generating functions of Catalan-type transforms

`s26a_hasSum_transform`: if `∑ c_k yᵏ = g` at `y = x^e/(1 - bx)²` (absolutely), then
`∑_n (∑_k c_k C(n - ek + 2k, 2k) b^{n-ek}) xⁿ = g/(1 - bx)` (summing the double series
`∑_k c_k x^{ek} (1 - bx)^{-(2k+1)}` by diagonals). Also the central binomial series
`∑ C(2k, k) yᵏ = 1/√(1 - 4y)` for `|y| < 1/4`.
-/

@[expose] public section

open Finset

noncomputable section

/-- Summing a doubly indexed series `∑_k c_k x^{ek} (1 - bx)^{-(2k+1)}` by diagonals. -/
theorem s26a_hasSum_transform (c : ℕ → ℝ) {e : ℕ} (he : 1 ≤ e) {b x g : ℝ} (hbx : |b * x| < 1)
    (hs : Summable fun k => |c k| * (|x| ^ e / (1 - |b * x|) ^ 2) ^ k)
    (hg : HasSum (fun k => c k * (x ^ e / (1 - b * x) ^ 2) ^ k) g) :
    HasSum (fun n => (∑ k ∈ range (n + 1), c k *
      if e * k ≤ n then ((n - e * k + 2 * k).choose (2 * k) : ℝ) * b ^ (n - e * k) else 0) *
        x ^ n) (g / (1 - b * x)) := by
  have hbx' : 1 - b * x ≠ 0 := by
    have := (abs_lt.mp hbx).2; linarith
  have hbxa : 0 < 1 - |b * x| := by linarith
  set F : ℕ × ℕ → ℝ := fun p =>
    c p.1 * ((p.2 + 2 * p.1).choose (2 * p.1) : ℝ) * b ^ p.2 * x ^ (e * p.1 + p.2) with hF
  have hrow : ∀ k, HasSum (fun j => F (k, j)) (c k * (x ^ e / (1 - b * x) ^ 2) ^ k /
      (1 - b * x)) := by
    intro k
    have h := (hasSum_choose_mul_geometric_of_norm_lt_one (2 * k) (r := b * x)
      (by rwa [Real.norm_eq_abs])).mul_left (c k * x ^ (e * k))
    convert h using 1
    · ext j; simp only [hF, mul_pow, pow_add]; ring
    · rw [div_pow, ← pow_mul, ← pow_mul, pow_succ]; field_simp
  have hrowa : ∀ k, HasSum (fun j => |F (k, j)|) (|c k| * (|x| ^ e / (1 - |b * x|) ^ 2) ^ k /
      (1 - |b * x|)) := by
    intro k
    have h := (hasSum_choose_mul_geometric_of_norm_lt_one (2 * k) (r := |b * x|)
      (by rwa [Real.norm_eq_abs, abs_abs])).mul_left (|c k| * |x| ^ (e * k))
    convert h using 1
    · ext j; simp only [hF, abs_mul, abs_pow, Nat.abs_cast, pow_add]; ring
    · rw [div_pow, ← pow_mul, ← pow_mul, pow_succ]; field_simp
  have hsumF : Summable F := by
    refine Summable.of_norm ?_
    simp only [Real.norm_eq_abs]
    refine (summable_prod_of_nonneg fun _ => abs_nonneg _).mpr ⟨fun k => (hrowa k).summable, ?_⟩
    simp_rw [fun k => (hrowa k).tsum_eq]
    exact hs.div_const _
  have hFg : HasSum F (g / (1 - b * x)) := by
    have h1 := hsumF.hasSum.prod_fiberwise hrow
    have h2 : HasSum (fun k => c k * (x ^ e / (1 - b * x) ^ 2) ^ k / (1 - b * x))
        (g / (1 - b * x)) := hg.div_const _
    rw [← h1.unique h2]
    exact hsumF.hasSum
  set G : ℕ × ℕ → ℝ := fun p => c p.2 * (if e * p.2 ≤ p.1 then
    ((p.1 - e * p.2 + 2 * p.2).choose (2 * p.2) : ℝ) * b ^ (p.1 - e * p.2) else 0) * x ^ p.1
    with hG
  set ι : ℕ × ℕ → ℕ × ℕ := fun p => (e * p.1 + p.2, p.1) with hι
  have hιinj : Function.Injective ι := by
    rintro ⟨k, j⟩ ⟨k', j'⟩ h
    simp only [hι, Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    simp only [Prod.mk.injEq, true_and]; omega
  have hGι : G ∘ ι = F := by
    ext ⟨k, j⟩
    simp only [Function.comp, hG, hι, hF, ite_eq_left (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
    ring
  have hGsum : HasSum G (g / (1 - b * x)) := by
    rw [← (hιinj.hasSum_iff ?_), hGι]
    · exact hFg
    · rintro ⟨n, k⟩ hnk
      simp only [hG]
      by_cases h : e * k ≤ n
      · exact absurd ⟨(k, n - e * k), by simp [hι]; omega⟩ hnk
      · simp [h]
  refine hGsum.prod_fiberwise fun n => ?_
  rw [sum_mul]
  refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
  simp only [mem_range, not_lt] at hk
  simp only [hG]
  rw [ite_eq_right (by nlinarith)]; simp

/-- The generalized binomial coefficient recursion over `ℝ`. -/
lemma s26a_ringChoose_succ (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 1) = Ring.choose a n * (a - n) / (n + 1) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, ← Polynomial.aeval_eq_smeval,
    ← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, Polynomial.aeval_def,
    ← Polynomial.eval_map, ← Polynomial.eval_map, descPochhammer_map, descPochhammer_map,
    descPochhammer_succ_eval, smul_eq_mul, smul_eq_mul, Nat.factorial_succ]
  push_cast
  have : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- `binom(-1/2, n) (-4)ⁿ = C(2n, n)`. -/
lemma s26a_ringChoose_neg_half (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n * (-4) ^ n = (2 * n).choose n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb := Nat.succ_mul_centralBinom_succ n
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hb
    have hb' : ((n + 1 : ℕ) : ℝ) * ((2 * (n + 1)).choose (n + 1) : ℝ) =
        2 * (2 * n + 1) * ((2 * n).choose n : ℝ) := by exact_mod_cast hb
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [s26a_ringChoose_succ, pow_succ]
    push_cast at hb'
    apply mul_left_cancel₀ hn
    rw [hb', ← ih]
    field_simp
    ring

/-- `∑ C(2k, k) yᵏ = 1/√(1 - 4y)` for real `|y| < 1/4`. -/
theorem s26a_hasSum_centralBinom {y : ℝ} (hy : |y| < 1 / 4) :
    HasSum (fun k : ℕ => ((2 * k).choose k : ℝ) * y ^ k) (1 / Real.sqrt (1 - 4 * y)) := by
  have hb := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (-1 / 2 : ℝ))).hasSum
    (y := -4 * y) (by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, Real.norm_eq_abs, abs_mul]
      rw [ENNReal.ofReal_lt_one]; norm_num; linarith)
  simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul,
    zero_add] at hb
  have hpos : 0 < 1 - 4 * y := by have := (abs_lt.mp hy).2; linarith
  convert hb using 1
  · ext k
    rw [← s26a_ringChoose_neg_half, mul_pow]; ring
  · rw [show 1 + -4 * y = 1 - 4 * y by ring, Real.sqrt_eq_rpow, one_div,
      ← Real.rpow_neg hpos.le]
    norm_num

end
