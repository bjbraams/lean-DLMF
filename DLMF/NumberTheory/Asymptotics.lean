/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Functions
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Chebyshev

/-!
# Asymptotic formulas: partial sums (DLMF §27.11)

DLMF's `∑_{n≤x}` is the sum over `1 ≤ n ≤ ⌊x⌋` (`Finset.Icc 1 ⌊x⌋₊`) and `∑_{p≤x}` the sum over
the primes `p ≤ ⌊x⌋` (`Nat.primesLE ⌊x⌋₊`). The error terms `O(g(x))` are
`Asymptotics.IsBigO atTop`; DLMF's "for all `x ≥ 1`" (resp. `x ≥ 2`) uniform bounds imply these
and conversely they follow from them when both sides are bounded on compact intervals, which is
the case here. Constants that DLMF only asserts to exist (`A` in 27.11.8, `B` in 27.11.9, `C` in
27.11.12) are existentially quantified. `γ` is `Real.eulerMascheroniConstant`.

Dirichlet's theorem on primes in arithmetic progressions (§27.11 after 27.11.11) is Mathlib's
`Nat.infinite_setOfPred_prime_and_modEq` (`Nat.setOf_prime_and_eq_mod_infinite`).
-/

@[expose] public noncomputable section

open Finset Filter Asymptotics ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.Moebius Real

namespace DLMF.NumberTheory

/-- DLMF 27.11.1: the asymptotic formula `∑_{n≤x} f(n) = F(x) + O(g(x))` as `x → ∞`. -/
@[dlmf 27.11.E1]
def HasPartialSumAsymptotic (f : ℕ → ℂ) (F g : ℝ → ℂ) : Prop :=
  (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n - F x) =O[atTop] g

/-! ### Elementary partial-sum estimates (helpers) -/

section R27Helpers

open scoped ArithmeticFunction.zeta

/-- `range (N + 1) = {0} ∪ (0, N]`. -/
theorem r27_range_eq_insert_Ioc (N : ℕ) : range (N + 1) = insert 0 (Ioc 0 N) := by
  ext n; simp only [mem_range, mem_insert, mem_Ioc]; omega

/-- Tail bound: `|A - ∑_{d ≤ N} a(d)/d²| ≤ 2/(N+1)` when `|a| ≤ 1` and `∑ a(d)/d² = A`. -/
theorem r27_tail_inv_sq {a : ℕ → ℝ} (ha : ∀ d, |a d| ≤ 1) {A : ℝ}
    (hA : HasSum (fun d : ℕ ↦ a d / (d : ℝ) ^ 2) A) (N : ℕ) :
    |A - ∑ d ∈ Ioc 0 N, a d / (d : ℝ) ^ 2| ≤ 2 / (N + 1) := by
  set f : ℕ → ℝ := fun d ↦ a d / (d : ℝ) ^ 2
  have hf : ∀ d, |f d| ≤ ((d : ℝ) ^ 2)⁻¹ := by
    intro d
    simp only [f, abs_div, abs_pow, Nat.abs_cast]
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) (ha d)
  have hrange : ∑ d ∈ Ioc 0 N, f d = ∑ d ∈ range (N + 1), f d := by
    rw [r27_range_eq_insert_Ioc, sum_insert (by simp)]; simp [f]
  have hsplit := (hA.summable.sum_add_tsum_nat_add (N + 1))
  rw [hA.tsum_eq] at hsplit
  have hsumg : Summable fun i ↦ (((i + (N + 1) : ℕ) : ℝ) ^ 2)⁻¹ := by
    have := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective
      (add_left_injective (N + 1))
    simpa [Function.comp_def] using this
  rw [hrange, ← hsplit, add_sub_cancel_left]
  calc |∑' i, f (i + (N + 1))| ≤ ∑' i, (((i + (N + 1) : ℕ) : ℝ) ^ 2)⁻¹ := by
        rw [← Real.norm_eq_abs]
        refine (norm_tsum_le_tsum_norm ?_).trans ?_
        · exact hsumg.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun i ↦ hf _
        · exact (hsumg.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun i ↦ hf _).tsum_le_tsum
            (fun i ↦ hf _) hsumg
    _ ≤ 2 / (N + 1) := by
        refine Real.tsum_le_of_sum_range_le (fun _ ↦ by positivity) fun M ↦ ?_
        calc ∑ i ∈ range M, (((i + (N + 1) : ℕ) : ℝ) ^ 2)⁻¹
            = ∑ j ∈ Ioo N (M + N + 1), ((j : ℝ) ^ 2)⁻¹ := by
              refine sum_nbij' (· + (N + 1)) (· - (N + 1)) ?_ ?_ ?_ ?_ ?_
              · intro i hi; simp only [mem_range] at hi; simp only [mem_Ioo]; omega
              · intro j hj; simp only [mem_Ioo] at hj; simp only [mem_range]; omega
              · intro i _; simp
              · intro j hj; simp only [mem_Ioo] at hj; omega
              · intro i _; rfl
          _ ≤ 2 / (N + 1) := sum_Ioo_inv_sq_le N _

/-- `∑_{d ≤ N} 1/d ≤ 1 + ln N`. -/
theorem r27_sum_inv_le (N : ℕ) : ∑ d ∈ Ioc 0 N, ((d : ℝ))⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  have hI : Ioc 0 N = Icc 1 N := by ext; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI]
  push_cast at h
  exact h

/-- `(N/d) - 1 < ⌊N/d⌋ ≤ N/d`. -/
theorem r27_div_bounds (N d : ℕ) (hd : 0 < d) :
    ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d ∧ (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · rw [le_div_iff₀ hd']; exact_mod_cast Nat.div_mul_le_self N d
  · rw [div_lt_iff₀ hd']
    have := Nat.lt_div_mul_add (a := N) hd
    have h2 : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
    linarith

/-- `∑_{m ≤ M} m = M(M+1)/2` in `ℝ`. -/
theorem r27_sum_Ioc_id (M : ℕ) : ∑ m ∈ Ioc 0 M, (m : ℝ) = M * (M + 1) / 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_Ioc_succ_top (by omega), ih]
    push_cast; ring

/-- Core estimate for `∑_{d ≤ N} a(d) T(⌊N/d⌋)`, `T(M) = M(M+1)/2`. -/
theorem r27_sum_triangle_bound {a : ℕ → ℝ} (ha : ∀ d, |a d| ≤ 1) {A : ℝ}
    (hA : HasSum (fun d : ℕ ↦ a d / (d : ℝ) ^ 2) A) {N : ℕ} (hN : 1 ≤ N) :
    |∑ d ∈ Ioc 0 N, a d * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2) - A * N ^ 2 / 2| ≤
      N * (2 + Real.log N) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsplit : ∑ d ∈ Ioc 0 N, a d * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2) -
      A * N ^ 2 / 2 = ∑ d ∈ Ioc 0 N, a d * ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) -
        ((N : ℝ) / d) ^ 2) / 2) + (N : ℝ) ^ 2 / 2 * (∑ d ∈ Ioc 0 N, a d / (d : ℝ) ^ 2 - A) := by
    have h1 : ∀ d ∈ Ioc 0 N, a d * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2) =
        a d * ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) - ((N : ℝ) / d) ^ 2) / 2) +
          (N : ℝ) ^ 2 / 2 * (a d / (d : ℝ) ^ 2) := by
      intro d hd
      have : (d : ℝ) ≠ 0 := by have := (mem_Ioc.mp hd).1; positivity
      field_simp; ring
    rw [sum_congr rfl h1, sum_add_distrib, ← mul_sum]; ring
  have hterm : ∀ d ∈ Ioc 0 N, |a d * ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) -
      ((N : ℝ) / d) ^ 2) / 2)| ≤ N / 2 * ((d : ℝ))⁻¹ := by
    intro d hd
    have hd := (mem_Ioc.mp hd).1
    obtain ⟨h1, h2⟩ := r27_div_bounds N d hd
    set M : ℝ := ((N / d : ℕ) : ℝ)
    set u : ℝ := (N : ℝ) / d
    have hM0 : 0 ≤ M := Nat.cast_nonneg _
    have hu : |M * (M + 1) - u ^ 2| ≤ u := by
      rw [abs_le]; constructor <;> nlinarith
    rw [abs_mul, abs_div, abs_two]
    calc |a d| * (|M * (M + 1) - u ^ 2| / 2) ≤ 1 * (u / 2) := by
          gcongr
          · exact ha d
      _ = N / 2 * ((d : ℝ))⁻¹ := by simp only [u]; ring
  have hfirst := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
  rw [← mul_sum] at hfirst
  have hsecond : |(N : ℝ) ^ 2 / 2 * (∑ d ∈ Ioc 0 N, a d / (d : ℝ) ^ 2 - A)| ≤ (N : ℝ) := by
    rw [abs_mul, abs_sub_comm, abs_of_nonneg (by positivity)]
    calc (N : ℝ) ^ 2 / 2 * |A - ∑ d ∈ Ioc 0 N, a d / (d : ℝ) ^ 2|
        ≤ (N : ℝ) ^ 2 / 2 * (2 / (N + 1)) := by gcongr; exact r27_tail_inv_sq ha hA N
      _ ≤ (N : ℝ) := by
          rw [show (N : ℝ) ^ 2 / 2 * (2 / (N + 1)) = N * (N / (N + 1)) by ring]
          exact mul_le_of_le_one_right (by positivity)
            ((div_le_one (by positivity)).mpr (by linarith))
  have hinv := r27_sum_inv_le N
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN'
  rw [hsplit]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ (N : ℝ) / 2 * (1 + Real.log N) + N := by
        gcongr
        exact hfirst.trans (by gcongr)
    _ ≤ N * (2 + Real.log N) := by nlinarith

/-- Core estimate for `∑_{d ≤ N} (a(d)/d) ⌊N/d⌋`. -/
theorem r27_sum_floor_bound {a : ℕ → ℝ} (ha : ∀ d, |a d| ≤ 1) {A : ℝ}
    (hA : HasSum (fun d : ℕ ↦ a d / (d : ℝ) ^ 2) A) {N : ℕ} (hN : 1 ≤ N) :
    |∑ d ∈ Ioc 0 N, a d / d * ((N / d : ℕ) : ℝ) - A * N| ≤ 3 + Real.log N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsplit : ∑ d ∈ Ioc 0 N, a d / d * ((N / d : ℕ) : ℝ) - A * N =
      ∑ d ∈ Ioc 0 N, a d / d * (((N / d : ℕ) : ℝ) - (N : ℝ) / d) +
        (N : ℝ) * (∑ d ∈ Ioc 0 N, a d / (d : ℝ) ^ 2 - A) := by
    have h1 : ∀ d ∈ Ioc 0 N, a d / d * ((N / d : ℕ) : ℝ) =
        a d / d * (((N / d : ℕ) : ℝ) - (N : ℝ) / d) + (N : ℝ) * (a d / (d : ℝ) ^ 2) := by
      intro d hd
      have : (d : ℝ) ≠ 0 := by have := (mem_Ioc.mp hd).1; positivity
      field_simp; ring
    rw [sum_congr rfl h1, sum_add_distrib, ← mul_sum]; ring
  have hterm : ∀ d ∈ Ioc 0 N, |a d / d * (((N / d : ℕ) : ℝ) - (N : ℝ) / d)| ≤ ((d : ℝ))⁻¹ := by
    intro d hd
    have hd := (mem_Ioc.mp hd).1
    obtain ⟨h1, h2⟩ := r27_div_bounds N d hd
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rw [abs_mul, abs_div, Nat.abs_cast]
    calc |a d| / d * |((N / d : ℕ) : ℝ) - (N : ℝ) / d| ≤ 1 / d * 1 := by
          gcongr
          · exact ha d
          · rw [abs_le]; constructor <;> linarith
      _ = ((d : ℝ))⁻¹ := by ring
  have hfirst := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
  have hsecond : |(N : ℝ) * (∑ d ∈ Ioc 0 N, a d / (d : ℝ) ^ 2 - A)| ≤ 2 := by
    rw [abs_mul, abs_sub_comm, Nat.abs_cast]
    calc (N : ℝ) * |A - ∑ d ∈ Ioc 0 N, a d / (d : ℝ) ^ 2| ≤ (N : ℝ) * (2 / (N + 1)) := by
          gcongr; exact r27_tail_inv_sq ha hA N
      _ ≤ 2 := by
          rw [show (N : ℝ) * (2 / (N + 1)) = 2 * (N / (N + 1)) by ring]
          exact mul_le_of_le_one_right (by positivity)
            ((div_le_one (by positivity)).mpr (by linarith))
  have hinv := r27_sum_inv_le N
  rw [hsplit]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ (1 + Real.log N) + 2 := add_le_add (hfirst.trans hinv) hsecond
    _ = 3 + Real.log N := by ring

/-- Converting a real bound to a complex `IsBigO`. -/
theorem r27_isBigO_ofReal {u v : ℝ → ℝ} (c : ℝ) (h : ∀ᶠ x in atTop, |u x| ≤ c * |v x|) :
    (fun x ↦ (u x : ℂ)) =O[atTop] fun x ↦ (v x : ℂ) :=
  IsBigO.of_bound c (by simpa only [Complex.norm_real, Real.norm_eq_abs] using h)

/-- `1 ≤ ln x` for `x ≥ 3`. -/
theorem r27_one_le_log {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  norm_num at this
  linarith

/-- `∑_{n ≤ N} σ₁(n) = ∑_{d ≤ N} T(⌊N/d⌋)`. -/
theorem r27_sum_sigma_one (N : ℕ) :
    ∑ n ∈ Icc 1 N, (σ 1 n : ℝ) =
      ∑ d ∈ Ioc 0 N, (1 : ℝ) * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2) := by
  have h := sum_Ioc_mul_eq_sum_sum (ζ : ArithmeticFunction ℕ) (pow 1) N
  rw [zeta_mul_pow_eq_sigma] at h
  have hI : Icc 1 N = Ioc 0 N := by ext; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI]
  have h' := congrArg (fun t : ℕ ↦ (t : ℝ)) h
  simp only [Nat.cast_sum, Nat.cast_mul] at h'
  rw [h']
  refine sum_congr rfl fun d hd ↦ ?_
  rw [zeta_apply_ne (mem_Ioc.mp hd).1.ne', Nat.cast_one, ← r27_sum_Ioc_id]
  congr 1
  refine sum_congr rfl fun m hm ↦ ?_
  rw [pow_apply, ite_eq_right_iff.mpr (fun h ↦ absurd h.2 (by have := (mem_Ioc.mp hm).1; omega)),
    pow_one]

/-- From `|S(N) - c N²| ≤ N(2 + ln N)` to `|S(⌊x⌋) - c x²| ≤ 8 x ln x`, `x ≥ 3`. -/
theorem r27_quadratic_conversion {S : ℕ → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2)
    (h : ∀ N : ℕ, 1 ≤ N → |S N - c * N ^ 2| ≤ N * (2 + Real.log N)) {x : ℝ} (hx : 3 ≤ x) :
    |S ⌊x⌋₊ - c * x ^ 2| ≤ 8 * |x * Real.log x| := by
  have hx0 : 0 ≤ x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hcore := h N hN1
  have hlog := r27_one_le_log hx
  have hlogN : Real.log N ≤ Real.log x := Real.log_le_log (by linarith) hNx
  have hsq : x ^ 2 - (N : ℝ) ^ 2 ≤ 2 * x := by
    have h1 : x ^ 2 - (N : ℝ) ^ 2 = (x - N) * (x + N) := by ring
    rw [h1]
    calc (x - N) * (x + N) ≤ 1 * (2 * x) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
      _ = 2 * x := one_mul _
  have hsq0 : 0 ≤ x ^ 2 - (N : ℝ) ^ 2 := by nlinarith
  have hC0 : 0 ≤ c * (x ^ 2 - N ^ 2) := by positivity
  have hC1 : c * (x ^ 2 - N ^ 2) ≤ 2 * (2 * x) := by
    calc c * (x ^ 2 - N ^ 2) ≤ 2 * (x ^ 2 - N ^ 2) := by gcongr
      _ ≤ 2 * (2 * x) := by gcongr
  have hE : (N : ℝ) * (2 + Real.log N) ≤ x * (2 + Real.log x) := by gcongr
  have hc' := abs_le.mp hcore
  rw [abs_of_nonneg (by positivity : 0 ≤ x * Real.log x), abs_le]
  have : c * x ^ 2 = c * N ^ 2 + c * (x ^ 2 - N ^ 2) := by ring
  rw [this]
  have hxl : x ≤ x * Real.log x := by nlinarith
  have hE' : x * (2 + Real.log x) ≤ 3 * (x * Real.log x) := by nlinarith
  constructor <;> linarith

/-- From `|S(N) - c N| ≤ 3 + ln N` to `|S(⌊x⌋) - c x| ≤ 5 ln x`, `x ≥ 3`. -/
theorem r27_linear_conversion {S : ℕ → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1)
    (h : ∀ N : ℕ, 1 ≤ N → |S N - c * N| ≤ 3 + Real.log N) {x : ℝ} (hx : 3 ≤ x) :
    |S ⌊x⌋₊ - c * x| ≤ 5 * |Real.log x| := by
  have hx0 : 0 ≤ x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hcore := abs_le.mp (h N hN1)
  have hlog := r27_one_le_log hx
  have hlogN : Real.log N ≤ Real.log x :=
    Real.log_le_log (by have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
                        linarith) hNx
  have hC : 0 ≤ c * (x - N) ∧ c * (x - N) ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  rw [abs_of_nonneg (by linarith : 0 ≤ Real.log x), abs_le]
  have : c * x = c * N + c * (x - N) := by ring
  rw [this]
  constructor <;> linarith

/-- DLMF 27.11.4 (proof). -/
theorem r27_sum_sigma_one_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (σ 1 n : ℂ)) (fun x ↦ (π ^ 2 / 12 * x ^ 2 : ℝ))
      (fun x ↦ (x * Real.log x : ℝ)) := by
  unfold HasPartialSumAsymptotic
  have he : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (σ 1 n : ℂ) - ((π ^ 2 / 12 * x ^ 2 : ℝ) : ℂ)) =
      fun x ↦ ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (σ 1 n : ℝ) - π ^ 2 / 12 * x ^ 2 : ℝ) : ℂ) := by
    funext x; push_cast; rfl
  rw [he]
  refine r27_isBigO_ofReal 8 ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
  refine r27_quadratic_conversion (S := fun N ↦ ∑ n ∈ Finset.Icc 1 N, (σ 1 n : ℝ))
    (by positivity) (by nlinarith [Real.pi_le_four, Real.pi_pos]) (fun N hN ↦ ?_) hx
  have hcore := r27_sum_triangle_bound (a := fun _ ↦ (1 : ℝ)) (fun _ ↦ by simp)
    (by simpa using hasSum_zeta_two) hN
  rw [← r27_sum_sigma_one] at hcore
  convert hcore using 3; ring

/-- `φ(n) = ∑_{ab = n} μ(a) b` in `ℝ`. -/
theorem r27_totient_eq_sum (n : ℕ) (hn : 0 < n) :
    (n.totient : ℝ) = ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) * (x.2 : ℝ) := by
  have h := (sum_eq_iff_sum_mul_moebius_eq (R := ℝ) (f := fun n ↦ (n.totient : ℝ))
    (g := fun n ↦ (n : ℝ))).mp (fun n _ ↦ by exact_mod_cast Nat.sum_totient n) n hn
  exact h.symm

/-- `∑ μ(d)/d² = 6/π²`. -/
theorem r27_hasSum_moebius_div_sq :
    HasSum (fun d : ℕ ↦ (μ d : ℝ) / (d : ℝ) ^ 2) (6 / π ^ 2) := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h1 := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at h1
  have h : LSeriesHasSum (fun n ↦ ((μ n : ℤ) : ℂ)) 2 (riemannZeta 2)⁻¹ := by
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact (LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  rw [riemannZeta_two] at h
  unfold LSeriesHasSum at h
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  · funext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    rw [LSeries.term_of_ne_zero hd]
    push_cast
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  · push_cast
    field_simp

/-- `∑_{n ≤ N} φ(n) = ∑_{d ≤ N} μ(d) T(⌊N/d⌋)`. -/
theorem r27_sum_totient (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.totient : ℝ) =
      ∑ d ∈ Ioc 0 N, (μ d : ℝ) * (((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2) := by
  have h := sum_Ioc_mul_eq_sum_sum ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
    ((pow 1 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) N
  have hI : Icc 1 N = Ioc 0 N := by ext; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI]
  have hl : ∀ n ∈ Ioc 0 N, (n.totient : ℝ) =
      (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
        ((pow 1 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) n := by
    intro n hn
    rw [r27_totient_eq_sum n (mem_Ioc.mp hn).1, mul_apply]
    refine sum_congr rfl fun x hx ↦ ?_
    have hx2 : x.2 ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hx |>.2) ∘ fun h ↦ by
      have := (Nat.mem_divisorsAntidiagonal.mp hx).1; rw [h, mul_zero] at this; exact this.symm
    simp [pow_apply, hx2]
  rw [sum_congr rfl hl, h]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [intCoe_apply, ← r27_sum_Ioc_id]
  congr 1
  refine sum_congr rfl fun m hm ↦ ?_
  have : m ≠ 0 := by have := (mem_Ioc.mp hm).1; omega
  simp [pow_apply, this]

/-- `∑_{n ≤ N} φ(n)/n = ∑_{d ≤ N} (μ(d)/d) ⌊N/d⌋`. -/
theorem r27_sum_totient_div (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.totient : ℝ) / n = ∑ d ∈ Ioc 0 N, (μ d : ℝ) / d * ((N / d : ℕ) : ℝ) := by
  let F : ArithmeticFunction ℝ := ⟨fun d ↦ (μ d : ℝ) / d, by simp⟩
  have h := sum_Ioc_mul_zeta_eq_sum F N
  have hI : Icc 1 N = Ioc 0 N := by ext; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI]
  have hl : ∀ n ∈ Ioc 0 N, (n.totient : ℝ) / n = (F * ζ) n := by
    intro n hn
    have hn0 := (mem_Ioc.mp hn).1
    rw [coe_mul_zeta_apply, r27_totient_eq_sum n hn0, Nat.sum_divisorsAntidiagonal
      (fun a b ↦ (μ a : ℝ) * (b : ℝ)), sum_div]
    refine sum_congr rfl fun d hd ↦ ?_
    have hdn := Nat.dvd_of_mem_divisors hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    show (μ d : ℝ) * ((n / d : ℕ) : ℝ) / n = (μ d : ℝ) / d
    rw [Nat.cast_div hdn hd0]
    field_simp
  rw [sum_congr rfl hl, h]
  rfl

/-- DLMF 27.11.6 (proof). -/
theorem r27_sum_totient_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (n.totient : ℂ)) (fun x ↦ (3 / π ^ 2 * x ^ 2 : ℝ))
      (fun x ↦ (x * Real.log x : ℝ)) := by
  unfold HasPartialSumAsymptotic
  have he : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.totient : ℂ) - ((3 / π ^ 2 * x ^ 2 : ℝ) : ℂ)) =
      fun x ↦ ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.totient : ℝ) - 3 / π ^ 2 * x ^ 2 : ℝ) : ℂ) := by
    funext x; push_cast; rfl
  rw [he]
  refine r27_isBigO_ofReal 8 ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
  have hpi : 3 < π := Real.pi_gt_three
  refine r27_quadratic_conversion (S := fun N ↦ ∑ n ∈ Finset.Icc 1 N, (n.totient : ℝ))
    (by positivity) ?_ (fun N hN ↦ ?_) hx
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  have hcore := r27_sum_triangle_bound (a := fun d ↦ (μ d : ℝ))
    (fun d ↦ by exact_mod_cast abs_moebius_le_one) r27_hasSum_moebius_div_sq hN
  rw [← r27_sum_totient] at hcore
  convert hcore using 3; ring

/-- DLMF 27.11.7 (proof). -/
theorem r27_sum_totient_div_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (n.totient : ℂ) / n) (fun x ↦ (6 / π ^ 2 * x : ℝ))
      (fun x ↦ (Real.log x : ℂ)) := by
  unfold HasPartialSumAsymptotic
  have he : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.totient : ℂ) / n - ((6 / π ^ 2 * x : ℝ) : ℂ)) =
      fun x ↦ ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.totient : ℝ) / n - 6 / π ^ 2 * x : ℝ) : ℂ) := by
    funext x; push_cast; rfl
  rw [he]
  refine r27_isBigO_ofReal 5 ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
  have hpi : 3 < π := Real.pi_gt_three
  refine r27_linear_conversion (S := fun N ↦ ∑ n ∈ Finset.Icc 1 N, (n.totient : ℝ) / n)
    (by positivity) ?_ (fun N hN ↦ ?_) hx
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  have hcore := r27_sum_floor_bound (a := fun d ↦ (μ d : ℝ))
    (fun d ↦ by exact_mod_cast abs_moebius_le_one) r27_hasSum_moebius_div_sq hN
  rw [← r27_sum_totient_div] at hcore
  exact hcore

/-- For `d > √N`, `⌊N/d⌋ = #{b ≤ √N : b d ≤ N}`. -/
theorem s27_card_filter_mul_le (N m d : ℕ) (hm : N < (m + 1) * (m + 1)) (hd : m < d) :
    ((Ioc 0 m).filter (fun b ↦ b * d ≤ N)).card = N / d := by
  have : (Ioc 0 m).filter (fun b ↦ b * d ≤ N) = Ioc 0 (N / d) := by
    ext b
    simp only [mem_filter, mem_Ioc]
    have hd0 : 0 < d := by omega
    rw [← Nat.le_div_iff_mul_le hd0]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, h2⟩
      by_contra hb
      rw [not_le] at hb
      have h3 : (m + 1) * (m + 1) ≤ b * d := Nat.mul_le_mul hb hd
      have h4 := (Nat.le_div_iff_mul_le hd0).mp h2
      omega
  rw [this, Nat.card_Ioc, Nat.sub_zero]

/-- For `b ≤ √N`, `#{√N < d ≤ N : b d ≤ N} = ⌊N/b⌋ - √N`. -/
theorem s27_card_filter_mul_le' (N m b : ℕ) (hb : b ∈ Ioc 0 m) :
    ((Ioc m N).filter (fun d ↦ b * d ≤ N)).card = N / b - m := by
  obtain ⟨hb0, hbm⟩ := mem_Ioc.mp hb
  have : (Ioc m N).filter (fun d ↦ b * d ≤ N) = Ioc m (N / b) := by
    ext d
    simp only [mem_filter, mem_Ioc]
    rw [mul_comm, ← Nat.le_div_iff_mul_le hb0]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans (Nat.div_le_self N b)⟩, h2⟩
  rw [this, Nat.card_Ioc]

/-- Dirichlet's hyperbola identity: `∑_{d ≤ N} ⌊N/d⌋ + m² = 2 ∑_{d ≤ m} ⌊N/d⌋`, `m = ⌊√N⌋`. -/
theorem s27_hyperbola (N : ℕ) :
    ∑ d ∈ Ioc 0 N, N / d + N.sqrt * N.sqrt = 2 * ∑ d ∈ Ioc 0 N.sqrt, N / d := by
  set m := N.sqrt
  have hm1 : m * m ≤ N := Nat.sqrt_le N
  have hm2 : N < (m + 1) * (m + 1) := Nat.lt_succ_sqrt N
  have hmN : m ≤ N := Nat.sqrt_le_self N
  have hsplit : ∑ d ∈ Ioc 0 N, N / d = ∑ d ∈ Ioc 0 m, N / d + ∑ d ∈ Ioc m N, N / d := by
    rw [← sum_Ioc_consecutive _ (Nat.zero_le m) hmN]
  have htail : ∑ d ∈ Ioc m N, N / d = ∑ b ∈ Ioc 0 m, (N / b - m) := by
    calc ∑ d ∈ Ioc m N, N / d
        = ∑ d ∈ Ioc m N, ∑ b ∈ Ioc 0 m, if b * d ≤ N then 1 else 0 := by
          refine sum_congr rfl fun d hd ↦ ?_
          rw [sum_boole, Nat.cast_id, s27_card_filter_mul_le N m d hm2 (mem_Ioc.mp hd).1]
      _ = ∑ b ∈ Ioc 0 m, ∑ d ∈ Ioc m N, if b * d ≤ N then 1 else 0 := sum_comm
      _ = ∑ b ∈ Ioc 0 m, (N / b - m) := by
          refine sum_congr rfl fun b hb ↦ ?_
          rw [sum_boole, Nat.cast_id, s27_card_filter_mul_le' N m b hb]
  have hge : ∀ b ∈ Ioc 0 m, m ≤ N / b := by
    intro b hb
    obtain ⟨hb0, hbm⟩ := mem_Ioc.mp hb
    rw [Nat.le_div_iff_mul_le hb0]
    exact (Nat.mul_le_mul_left m hbm).trans hm1
  have hsub : ∑ b ∈ Ioc 0 m, (N / b - m) + m * m = ∑ b ∈ Ioc 0 m, N / b := by
    have : ∑ b ∈ Ioc 0 m, (N / b - m) + ∑ b ∈ Ioc 0 m, m = ∑ b ∈ Ioc 0 m, N / b := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun b hb ↦ Nat.sub_add_cancel (hge b hb)
    simpa [Nat.card_Ioc] using this
  rw [hsplit, htail]
  omega


/-- `0 ≤ H_n - ln n - γ ≤ 1/n` for `n ≥ 1`. -/
theorem s27_harmonic_sub_bounds {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ ∑ d ∈ Ioc 0 n, ((d : ℝ))⁻¹ - Real.log n - Real.eulerMascheroniConstant ∧
      ∑ d ∈ Ioc 0 n, ((d : ℝ))⁻¹ - Real.log n - Real.eulerMascheroniConstant ≤ 1 / n := by
  have hH : ∑ d ∈ Ioc 0 n, ((d : ℝ))⁻¹ = harmonic n := by
    rw [harmonic_eq_sum_Icc]
    have hI : Ioc 0 n = Icc 1 n := by ext; simp only [mem_Ioc, mem_Icc]; omega
    rw [hI]; push_cast; rfl
  have h1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have h2 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  simp only [Real.eulerMascheroniSeq', Real.eulerMascheroniSeq, show n ≠ 0 by omega,
    ite_false] at h1 h2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (n + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by positivity) hn'.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    field_simp; ring
  rw [hH]
  constructor <;> linarith

/-- `0 ≤ ln N - 2 ln ⌊√N⌋ ≤ 3/⌊√N⌋` for `N ≥ 1`. -/
theorem s27_log_sqrt_gap {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ Real.log N - 2 * Real.log N.sqrt ∧
      Real.log N - 2 * Real.log N.sqrt ≤ 3 / N.sqrt := by
  have hm : 1 ≤ N.sqrt := Nat.le_sqrt.mpr (by omega)
  have hm' : (1 : ℝ) ≤ N.sqrt := by exact_mod_cast hm
  have h1 : ((N.sqrt : ℕ) : ℝ) * N.sqrt ≤ N := by exact_mod_cast Nat.sqrt_le N
  have h2 : (N : ℝ) < (N.sqrt + 1) * (N.sqrt + 1) := by exact_mod_cast Nat.lt_succ_sqrt N
  have he : Real.log N - 2 * Real.log N.sqrt = Real.log (N / (N.sqrt * N.sqrt)) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity)]; ring
  rw [he]
  constructor
  · exact Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  · refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- 27.11.2 for integer `N`: `|D(N) - N ln N - (2γ-1)N| ≤ 25 √N`. -/
theorem s27_sum_sigma_zero_bound {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, (σ 0 n : ℝ) - (N * Real.log N + (2 * Real.eulerMascheroniConstant - 1) * N)|
      ≤ 25 * Real.sqrt N := by
  set m := N.sqrt with hmdef
  have hm : 1 ≤ m := Nat.le_sqrt.mpr (by omega)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (m : ℝ) * m ≤ N := by exact_mod_cast Nat.sqrt_le N
  have h2 : (N : ℝ) < (m + 1) * (m + 1) := by exact_mod_cast Nat.lt_succ_sqrt N
  have hmsq : (m : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  -- D(N) = 2 ∑_{d ≤ m} ⌊N/d⌋ - m²
  have hD : ∑ n ∈ Icc 1 N, (σ 0 n : ℝ) = 2 * ∑ d ∈ Ioc 0 m, ((N / d : ℕ) : ℝ) - m * m := by
    have hI : Icc 1 N = Ioc 0 N := by ext; simp only [mem_Ioc, mem_Icc]; omega
    have h := sum_Ioc_sigma0_eq_sum_div N
    have h' := s27_hyperbola N
    rw [← h] at h'
    rw [hI, eq_sub_iff_add_eq]
    exact_mod_cast h'
  -- ∑_{d ≤ m} ⌊N/d⌋ = N H_m - E
  set E := ∑ d ∈ Ioc 0 m, ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) with hE
  have hE0 : 0 ≤ E := sum_nonneg fun d hd ↦ by
    have := (r27_div_bounds N d (mem_Ioc.mp hd).1).1; linarith
  have hE1 : E ≤ m := by
    have : E ≤ ∑ d ∈ Ioc 0 m, (1 : ℝ) := sum_le_sum fun d hd ↦ by
      have := (r27_div_bounds N d (mem_Ioc.mp hd).1).2; linarith
    simpa using this
  have hsum : ∑ d ∈ Ioc 0 m, ((N / d : ℕ) : ℝ) = N * ∑ d ∈ Ioc 0 m, ((d : ℝ))⁻¹ - E := by
    rw [hE, sum_sub_distrib, mul_sum]
    simp only [div_eq_mul_inv]; ring
  obtain ⟨hδ0, hδ1⟩ := s27_harmonic_sub_bounds hm
  obtain ⟨hη0, hη1⟩ := s27_log_sqrt_gap hN
  rw [← hmdef] at hη0 hη1
  set δ := ∑ d ∈ Ioc 0 m, ((d : ℝ))⁻¹ - Real.log m - Real.eulerMascheroniConstant
  set η := Real.log N - 2 * Real.log m
  have hkey : ∑ n ∈ Icc 1 N, (σ 0 n : ℝ) -
      (N * Real.log N + (2 * Real.eulerMascheroniConstant - 1) * N) =
      -(N * η) + 2 * (N * δ) - 2 * E + (N - m * m) := by
    rw [hD, hsum]; simp only [δ, η]; ring
  have hNm : (N : ℝ) ≤ 4 * m * m := by nlinarith
  have hNδ : N * δ ≤ 4 * m := by
    calc N * δ ≤ N * (1 / m) := mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ ≤ 4 * m := by rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
  have hNη : N * η ≤ 12 * m := by
    calc N * η ≤ N * (3 / m) := mul_le_mul_of_nonneg_left hη1 (by positivity)
      _ ≤ 12 * m := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hNδ0 : 0 ≤ N * δ := by positivity
  have hNη0 : 0 ≤ N * η := by positivity
  rw [hkey, abs_le]
  constructor <;> nlinarith


/-- `ln x ≤ 2 √x` for `x > 0`. -/
theorem s27_log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hx.le] at h
  linarith

/-- `0 ≤ x ln x - N ln N ≤ ln x + 1` for `N = ⌊x⌋`, `x ≥ 1`. -/
theorem s27_xlogx_floor {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ x * Real.log x - ⌊x⌋₊ * Real.log ⌊x⌋₊ ∧
      x * Real.log x - ⌊x⌋₊ * Real.log ⌊x⌋₊ ≤ Real.log x + 1 := by
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlN : Real.log N ≤ Real.log x := Real.log_le_log (by positivity) hNx
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg hN1'
  have hdiff : Real.log x - Real.log N ≤ (x - N) / N := by
    rw [← Real.log_div hx0.ne' (by positivity)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    field_simp
  have he : x * Real.log x - N * Real.log N =
      (x - N) * Real.log x + N * (Real.log x - Real.log N) := by ring
  rw [he]
  constructor
  · have := sub_nonneg.mpr hNx; have := sub_nonneg.mpr hlN; positivity
  · have h1 : (x - N) * Real.log x ≤ Real.log x := by
      have : x - N ≤ 1 := by linarith
      nlinarith
    have h2 : N * (Real.log x - Real.log N) ≤ 1 := by
      calc N * (Real.log x - Real.log N) ≤ N * ((x - N) / N) :=
            mul_le_mul_of_nonneg_left hdiff (by positivity)
        _ = x - N := by field_simp
        _ ≤ 1 := by linarith
    linarith

/-- DLMF 27.11.2 (proof). -/
theorem s27_sum_sigma_zero_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (σ 0 n : ℂ))
      (fun x ↦ (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x : ℝ))
      (fun x ↦ (Real.sqrt x : ℂ)) := by
  unfold HasPartialSumAsymptotic
  have he : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (σ 0 n : ℂ) -
      ((x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x : ℝ) : ℂ)) =
      fun x ↦ ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (σ 0 n : ℝ) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) : ℝ) : ℂ) := by
    funext x; push_cast; rfl
  rw [he]
  refine r27_isBigO_ofReal 29 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hcore := s27_sum_sigma_zero_bound hN1
  obtain ⟨h1, h2⟩ := s27_xlogx_floor hx
  have hsq : Real.sqrt N ≤ Real.sqrt x := Real.sqrt_le_sqrt hNx
  have hsx : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx
  have hlog := s27_log_le_two_sqrt hx0
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  rw [abs_of_nonneg (Real.sqrt_nonneg x)]
  rw [abs_le] at hcore ⊢
  have hc : 0 ≤ (2 * Real.eulerMascheroniConstant - 1) * (x - N) ∧
      (2 * Real.eulerMascheroniConstant - 1) * (x - N) ≤ 1 := by
    constructor <;> nlinarith
  constructor <;> nlinarith


/-- The error sequence of the telescoping comparison for `∑ ln a / a`. -/
noncomputable def s27_errLog (a : ℕ) : ℝ := Real.log a / (a * ((a : ℝ) - 1)) + 1 / ((a : ℝ) - 1) ^ 2

theorem s27_errLog_nonneg (a : ℕ) : 0 ≤ s27_errLog a := by
  unfold s27_errLog
  rcases Nat.lt_or_ge a 1 with h | h
  · interval_cases a; simp
  · have : (1 : ℝ) ≤ a := by exact_mod_cast h
    have := Real.log_nonneg this
    have : 0 ≤ (a : ℝ) - 1 := by linarith
    positivity

theorem s27_summable_errLog : Summable s27_errLog := by
  have hs : Summable fun n : ℕ ↦ 8 * ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 8
  refine Summable.of_norm_bounded_eventually_nat hs ?_
  filter_upwards [eventually_ge_atTop 2] with a ha
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  rw [Real.norm_of_nonneg (s27_errLog_nonneg a)]
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hp : (a : ℝ) ^ ((3 : ℝ) / 2) = a * Real.sqrt a := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ha0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [hp]
  have hss : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  have hlog : Real.log a ≤ 2 * Real.sqrt a := by
    have h := Real.log_le_sub_one_of_pos hsq
    rw [Real.log_sqrt ha0.le] at h
    linarith
  have hsq1 : 1 ≤ Real.sqrt a := by rw [Real.one_le_sqrt]; linarith
  unfold s27_errLog
  have hb : (0 : ℝ) < a - 1 := by linarith
  have h1 : Real.log a / (a * ((a : ℝ) - 1)) ≤ 4 * (a * Real.sqrt a)⁻¹ := by
    rw [div_le_iff₀ (by positivity), mul_comm, ← mul_assoc, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hlog (show 0 ≤ (a : ℝ) * Real.sqrt a by positivity)
    nlinarith
  have h2 : 1 / ((a : ℝ) - 1) ^ 2 ≤ 4 * (a * Real.sqrt a)⁻¹ := by
    rw [div_le_iff₀ (by positivity), mul_comm, ← mul_assoc, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- One telescoping step: `|ln a/a - (½ ln²a - ½ ln²(a-1))| ≤ e(a)` for `a ≥ 1`. -/
theorem s27_log_step {a : ℕ} (ha : 1 ≤ a) :
    |Real.log a / a - (Real.log a ^ 2 / 2 - Real.log ((a - 1 : ℕ) : ℝ) ^ 2 / 2)| ≤
      s27_errLog a := by
  rcases Nat.lt_or_ge a 2 with h | h
  · obtain rfl : a = 1 := by omega
    simp [s27_errLog]
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast h
  have hc : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by push_cast [Nat.cast_sub ha]; ring
  rw [hc]
  set u := Real.log a - Real.log ((a : ℝ) - 1) with hu
  have hb : (0 : ℝ) < a - 1 := by linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have hu1 : u ≤ 1 / ((a : ℝ) - 1) := by
    rw [hu, ← Real.log_div ha0.ne' hb.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    field_simp; ring
  have hu0 : 1 / (a : ℝ) ≤ u := by
    rw [hu, ← neg_sub, ← Real.log_div hb.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < ((a : ℝ) - 1) / a by positivity)
    have he : ((a : ℝ) - 1) / a - 1 = -(1 / a) := by field_simp; ring
    linarith
  have hl : Real.log ((a : ℝ) - 1) = Real.log a - u := by rw [hu]; ring
  rw [hl]
  have hlog0 : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
  have hd1 : u - 1 / a ≤ 1 / (a * ((a : ℝ) - 1)) := by
    have : 1 / ((a : ℝ) - 1) - 1 / a = 1 / (a * ((a : ℝ) - 1)) := by field_simp; ring
    linarith
  have he : Real.log a / a - (Real.log a ^ 2 / 2 - (Real.log a - u) ^ 2 / 2) =
      -((u - 1 / a) * Real.log a) + u ^ 2 / 2 := by ring
  rw [he]
  have hA : 0 ≤ (u - 1 / a) * Real.log a := mul_nonneg (by linarith) hlog0
  have hA' : (u - 1 / a) * Real.log a ≤ Real.log a / (a * ((a : ℝ) - 1)) := by
    calc (u - 1 / a) * Real.log a ≤ 1 / (a * ((a : ℝ) - 1)) * Real.log a :=
          mul_le_mul_of_nonneg_right hd1 hlog0
      _ = _ := by ring
  have hu0' : 0 ≤ u := le_trans (by positivity) hu0
  have hB : u ^ 2 / 2 ≤ 1 / ((a : ℝ) - 1) ^ 2 := by
    have : u ^ 2 ≤ (1 / ((a : ℝ) - 1)) ^ 2 := pow_le_pow_left₀ hu0' hu1 2
    rw [div_pow, one_pow] at this
    have : 0 ≤ 1 / ((a : ℝ) - 1) ^ 2 := by positivity
    linarith
  unfold s27_errLog
  rw [abs_le]; constructor <;> nlinarith

/-- `∑_{a ≤ N} ln a / a = ½ ln² N + O(1)`. -/
theorem s27_sum_log_div_bound :
    ∃ C : ℝ, ∀ N : ℕ, |∑ a ∈ Ioc 0 N, Real.log a / a - Real.log N ^ 2 / 2| ≤ C := by
  refine ⟨∑' a, s27_errLog a, fun N ↦ ?_⟩
  have htel : ∀ N : ℕ, Real.log N ^ 2 / 2 =
      ∑ a ∈ Ioc 0 N, (Real.log a ^ 2 / 2 - Real.log ((a - 1 : ℕ) : ℝ) ^ 2 / 2) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_Ioc_succ_top (by omega), ← ih]
      simp
  rw [htel, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun a ha ↦ s27_log_step (mem_Ioc.mp ha).1).trans ?_
  exact s27_summable_errLog.sum_le_tsum _ fun a _ ↦ s27_errLog_nonneg a


/-- `∑_{n ≤ N} d(n)/n = ∑_{a ≤ N} (1/a) H_{⌊N/a⌋}`. -/
theorem s27_sum_sigma_zero_div (N : ℕ) :
    ∑ n ∈ Icc 1 N, (σ 0 n : ℝ) / n =
      ∑ a ∈ Ioc 0 N, ((a : ℝ))⁻¹ * ∑ b ∈ Ioc 0 (N / a), ((b : ℝ))⁻¹ := by
  let f : ArithmeticFunction ℝ := ⟨fun n ↦ ((n : ℝ))⁻¹, by simp⟩
  have h := sum_Ioc_mul_eq_sum_sum f f N
  have hI : Icc 1 N = Ioc 0 N := by ext; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI]
  have hl : ∀ n ∈ Ioc 0 N, (σ 0 n : ℝ) / n = (f * f) n := by
    intro n hn
    have hn0 := (mem_Ioc.mp hn).1
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ f a * f b), sigma_zero_apply]
    have : ∀ i ∈ n.divisors, f i * f (n / i) = ((n : ℝ))⁻¹ := by
      intro i hi
      have hin := Nat.dvd_of_mem_divisors hi
      have hi0 : (i : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hi).ne'
      show ((i : ℝ))⁻¹ * (((n / i : ℕ) : ℝ))⁻¹ = ((n : ℝ))⁻¹
      rw [Nat.cast_div hin hi0, ← mul_inv, mul_div_cancel₀ _ hi0]
    rw [sum_congr rfl this, sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [sum_congr rfl hl, h]
  rfl

/-- `|H_{⌊N/a⌋} - (ln N - ln a + γ)| ≤ 4a/N` for `1 ≤ a ≤ N`. -/
theorem s27_harmonic_floor_div {N a : ℕ} (ha : a ∈ Ioc 0 N) :
    |∑ b ∈ Ioc 0 (N / a), ((b : ℝ))⁻¹ - (Real.log N - Real.log a + Real.eulerMascheroniConstant)|
      ≤ 4 * a / N := by
  obtain ⟨ha0, haN⟩ := mem_Ioc.mp ha
  have hk1 : 1 ≤ N / a := (Nat.one_le_div_iff ha0).mpr haN
  set k := N / a with hkdef
  obtain ⟨hk0, hk1'⟩ := r27_div_bounds N a ha0
  rw [← hkdef] at hk0 hk1'
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have har : (0 : ℝ) < a := by exact_mod_cast ha0
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hδ0, hδ1⟩ := s27_harmonic_sub_bounds hk1
  have hlN : Real.log N - Real.log a = Real.log ((N : ℝ) / a) := (Real.log_div hNr.ne' har.ne').symm
  have hg0 : 0 ≤ Real.log ((N : ℝ) / a) - Real.log k := by
    have := Real.log_le_log (by positivity) hk0; linarith
  have hg1 : Real.log ((N : ℝ) / a) - Real.log k ≤ 1 / k := by
    rw [← Real.log_div (by positivity) (by positivity)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    linarith
  have hk2 : 1 / (k : ℝ) ≤ 2 * a / N := by
    rw [div_le_div_iff₀ (by positivity) hNr]
    have : (N : ℝ) / a * a = N := div_mul_cancel₀ _ har.ne'
    nlinarith
  rw [hlN]
  set Hk := ∑ b ∈ Ioc 0 k, ((b : ℝ))⁻¹
  have e1 : 1 / (k : ℝ) ≤ 2 * a / N := hk2
  have e2 : 2 * (2 * (a : ℝ) / N) = 4 * a / N := by ring
  rw [abs_le]
  constructor <;> linarith

/-- 27.11.3 for integer `N`, with an unspecified constant. -/
theorem s27_sum_sigma_zero_div_bound :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → |∑ n ∈ Icc 1 N, (σ 0 n : ℝ) / n -
      (Real.log N ^ 2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log N)| ≤ C := by
  obtain ⟨C, hC⟩ := s27_sum_log_div_bound
  set γ := Real.eulerMascheroniConstant
  refine ⟨γ ^ 2 + 1 + γ + C + 4, fun N hN ↦ ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [s27_sum_sigma_zero_div]
  set H := ∑ a ∈ Ioc 0 N, ((a : ℝ))⁻¹
  set L := ∑ a ∈ Ioc 0 N, Real.log a / a
  set R := ∑ a ∈ Ioc 0 N, ((a : ℝ))⁻¹ * (∑ b ∈ Ioc 0 (N / a), ((b : ℝ))⁻¹ -
    (Real.log N - Real.log a + γ))
  have hsplit : ∑ a ∈ Ioc 0 N, ((a : ℝ))⁻¹ * ∑ b ∈ Ioc 0 (N / a), ((b : ℝ))⁻¹ =
      (Real.log N + γ) * H - L + R := by
    have hY : ∑ a ∈ Ioc 0 N, ((a : ℝ))⁻¹ * (Real.log N - Real.log a + γ) =
        (Real.log N + γ) * H - L := by
      simp only [H, L, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun a _ ↦ ?_
      rw [div_eq_inv_mul]; ring
    simp only [R, mul_sub, sum_sub_distrib]
    rw [hY]; ring
  have hR : |R| ≤ 4 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a ∈ Ioc 0 N, |((a : ℝ))⁻¹ * (∑ b ∈ Ioc 0 (N / a), ((b : ℝ))⁻¹ -
          (Real.log N - Real.log a + γ))|
        ≤ ∑ a ∈ Ioc 0 N, ((a : ℝ))⁻¹ * (4 * a / N) := by
          refine sum_le_sum fun a ha ↦ ?_
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (s27_harmonic_floor_div ha) (by positivity)
      _ = ∑ a ∈ Ioc 0 N, 4 / (N : ℝ) := by
          refine sum_congr rfl fun a ha ↦ ?_
          have : (a : ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.mp ha).1.ne'
          field_simp
      _ = 4 := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero]
          field_simp
  obtain ⟨hδ0, hδ1⟩ := s27_harmonic_sub_bounds hN
  have hL := hC N
  rw [hsplit]
  set δ := H - Real.log N - γ
  have hHe : H = Real.log N + γ + δ := by simp only [δ]; ring
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hlogN : Real.log N * δ ≤ 1 := by
    calc Real.log N * δ ≤ Real.log N * (1 / N) := mul_le_mul_of_nonneg_left hδ1 hlog0
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by positivity); linarith
  have hδ1' : δ ≤ 1 := hδ1.trans (by rw [div_le_one (by positivity)]; exact hNr)
  have hγ0 : 0 < γ := by have := Real.one_half_lt_eulerMascheroniConstant; simp only [γ]; linarith
  have he : (Real.log N + γ) * H - L + R - (Real.log N ^ 2 / 2 + 2 * γ * Real.log N) =
      γ ^ 2 + Real.log N * δ + γ * δ - (L - Real.log N ^ 2 / 2) + R := by
    rw [hHe]; ring
  rw [he]
  rw [abs_le] at hL hR ⊢
  have hlδ0 : 0 ≤ Real.log N * δ := mul_nonneg hlog0 hδ0
  have hγδ0 : 0 ≤ γ * δ := mul_nonneg hγ0.le hδ0
  have hγδ : γ * δ ≤ γ := by nlinarith
  constructor <;> nlinarith


/-- DLMF 27.11.3 (proof). -/
theorem s27_sum_sigma_zero_div_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (σ 0 n : ℂ) / n)
      (fun x ↦ (Real.log x ^ 2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log x : ℝ))
      (fun _ ↦ (1 : ℂ)) := by
  unfold HasPartialSumAsymptotic
  obtain ⟨C, hC⟩ := s27_sum_sigma_zero_div_bound
  set γ := Real.eulerMascheroniConstant
  have he : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (σ 0 n : ℂ) / n -
      ((Real.log x ^ 2 / 2 + 2 * γ * Real.log x : ℝ) : ℂ)) =
      fun x ↦ ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (σ 0 n : ℝ) / n -
        (Real.log x ^ 2 / 2 + 2 * γ * Real.log x) : ℝ) : ℂ) := by
    funext x; push_cast; rfl
  have he1 : (fun _ : ℝ ↦ (1 : ℂ)) = fun _ ↦ ((1 : ℝ) : ℂ) := by simp
  rw [he, he1]
  refine r27_isBigO_ofReal (C + 3) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hcore := hC N hN1
  have hlN : Real.log N ≤ Real.log x := Real.log_le_log (by positivity) hNx
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg hN1'
  have hdiff : Real.log x - Real.log N ≤ 1 / N := by
    rw [← Real.log_div hx0.ne' (by positivity)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    linarith
  have hlx : Real.log x ≤ N := by
    have := Real.log_le_sub_one_of_pos hx0; linarith
  have hsq : Real.log x ^ 2 / 2 - Real.log N ^ 2 / 2 ≤ 1 := by
    have h1 : Real.log x ^ 2 / 2 - Real.log N ^ 2 / 2 =
        (Real.log x - Real.log N) * ((Real.log x + Real.log N) / 2) := by ring
    rw [h1]
    calc (Real.log x - Real.log N) * ((Real.log x + Real.log N) / 2)
        ≤ 1 / N * N := by
          apply mul_le_mul hdiff (by linarith) (by linarith) (by positivity)
      _ = 1 := by field_simp
  have hsq0 : 0 ≤ Real.log x ^ 2 / 2 - Real.log N ^ 2 / 2 := by nlinarith
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have h1N : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hN1'
  have hγd : 0 ≤ γ * (Real.log x - Real.log N) ∧ γ * (Real.log x - Real.log N) ≤ 1 := by
    constructor
    · exact mul_nonneg (by simp only [γ]; linarith) (by linarith)
    · nlinarith
  rw [abs_one, mul_one]
  rw [abs_le] at hcore ⊢
  constructor <;> nlinarith


/-- `∑_{n ≤ N} Λ(n)/n` as a double sum over primes and exponents (after Mathlib's
`Chebyshev.psi_eq_sum_mul_log_prime`). -/
theorem s27_sum_vonMangoldt_div (n : ℕ) :
    ∑ m ∈ Ioc 0 n, Λ m / m =
      ∑ p ∈ Nat.primesLE n, ∑ k ∈ Icc 1 (Nat.log p n), Real.log p / (p : ℝ) ^ k := by
  have hI : Ioc 0 n = Icc 1 n := by ext; simp only [mem_Ioc, mem_Icc]; omega
  calc ∑ m ∈ Ioc 0 n, Λ m / m
    _ = ∑ m ∈ ((Icc 1 n).filter Nat.Prime).biUnion
            fun p ↦ image (p ^ ·) (Icc 1 (Nat.log p n)), Λ m / m := by
        rw [hI]
        refine (sum_subset (fun q hq ↦ ?_) fun x hx hnot ↦ ?_).symm
        · simp only [mem_biUnion, mem_filter, mem_Icc, mem_image] at hq ⊢
          obtain ⟨p, _, k, ⟨_, hk⟩, rfl⟩ := hq
          exact ⟨by grind, Nat.pow_le_of_le_log (by linarith) hk⟩
        · suffices Λ x = 0 by rw [this, zero_div]
          rw [vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
          rintro ⟨p, k, hp, hk, rfl⟩
          simp only [mem_Icc] at hx
          have hpn : p ≤ n := (Nat.le_of_dvd (by lia) (dvd_pow_self p hk.ne')).trans hx.2
          apply hnot
          simp only [mem_biUnion, mem_filter, mem_Icc, mem_image]
          exact ⟨p, ⟨⟨hp.one_le, hpn⟩, hp⟩, k, ⟨by lia, Nat.le_log_of_pow_le hp.one_lt hx.2⟩,
            rfl⟩
    _ = ∑ p ∈ Icc 1 n with p.Prime, ∑ q ∈ image (fun k ↦ p ^ k) (Icc 1 (Nat.log p n)),
            Λ q / q := by
        rw [sum_biUnion <| by rw [pairwiseDisjoint_iff]; grind [Nat.Prime.pow_inj']]
    _ = ∑ p ∈ Nat.primesLE n, ∑ k ∈ Icc 1 (Nat.log p n), Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) := by
        refine sum_congr (Nat.primesLE_eq_filter_Icc_one n).symm fun p hp ↦ ?_
        exact sum_image fun a _ b _ hab ↦
          Nat.pow_right_injective (Nat.two_le_of_mem_primesLE hp) hab
    _ = _ := by
        refine sum_congr rfl fun p hp ↦ sum_congr rfl fun k hk ↦ ?_
        rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime <|
          Nat.prime_of_mem_primesLE hp, Nat.cast_pow]


/-- `1/p ≤ ∑_{k=1}^K p^{-k} ≤ 1/(p-1)` for `p ≥ 2`, `K ≥ 1`. -/
theorem s27_geom_bounds {p : ℝ} (hp : 2 ≤ p) {K : ℕ} (hK : 1 ≤ K) :
    1 / p ≤ ∑ k ∈ Icc 1 K, 1 / p ^ k ∧ ∑ k ∈ Icc 1 K, 1 / p ^ k ≤ 1 / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hr : ∀ K : ℕ, (∑ k ∈ Icc 1 K, 1 / p ^ k) * (p - 1) = 1 - 1 / p ^ K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_Icc_succ_top (by omega), add_mul, ih]
      field_simp; ring
  constructor
  · have := single_le_sum (f := fun k ↦ 1 / p ^ k) (fun k _ ↦ by positivity)
      (show 1 ∈ Icc 1 K by simp [hK])
    simpa using this
  · rw [le_div_iff₀ (by linarith), hr]
    have : 0 < 1 / p ^ K := by positivity
    linarith

/-- `∑_{n ≤ N} ln n = ln N!`. -/
theorem s27_sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Real.log n = Real.log N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (by omega), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), add_comm]

/-- `N ln N - N ≤ ln N! ≤ N ln N`. -/
theorem s27_log_factorial_bounds (N : ℕ) :
    N * Real.log N - N ≤ Real.log N.factorial ∧ Real.log N.factorial ≤ N * Real.log N := by
  rw [← s27_sum_log_eq_log_factorial]
  constructor
  · rw [s27_sum_log_eq_log_factorial]
    have h := Real.pow_div_factorial_le_exp (x := (N : ℝ)) (by positivity) N
    have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have := Real.log_le_log (by positivity) h
    rw [Real.log_exp, Real.log_div (by positivity) hf.ne', Real.log_pow] at this
    linarith
  · calc ∑ n ∈ Ioc 0 N, Real.log n ≤ ∑ n ∈ Ioc 0 N, Real.log N := by
          refine sum_le_sum fun n hn ↦ ?_
          obtain ⟨h1, h2⟩ := mem_Ioc.mp hn
          exact Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast h2)
      _ = N * Real.log N := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero]

/-- `ln N - 1 ≤ ∑_{n ≤ N} Λ(n)/n ≤ ln N + ln 4 + 4` for `N ≥ 1`. -/
theorem s27_sum_vonMangoldt_div_bounds {N : ℕ} (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ m ∈ Ioc 0 N, Λ m / m ∧
      ∑ m ∈ Ioc 0 N, Λ m / m ≤ Real.log N + (Real.log 4 + 4) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hleg : ∑ n ∈ Ioc 0 N, Real.log n = ∑ d ∈ Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
    rw [← sum_Ioc_mul_zeta_eq_sum, vonMangoldt_mul_zeta]
    rfl
  rw [s27_sum_log_eq_log_factorial] at hleg
  set E := ∑ d ∈ Ioc 0 N, Λ d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))
  have hE : N * ∑ m ∈ Ioc 0 N, Λ m / m - E = Real.log N.factorial := by
    rw [hleg, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ ↦ ?_
    ring
  have hE0 : 0 ≤ E := sum_nonneg fun d hd ↦ by
    have := (r27_div_bounds N d (mem_Ioc.mp hd).1).1
    exact mul_nonneg vonMangoldt_nonneg (by linarith)
  have hE1 : E ≤ (Real.log 4 + 4) * N := by
    calc E ≤ ∑ d ∈ Ioc 0 N, Λ d := sum_le_sum fun d hd ↦ by
          have := (r27_div_bounds N d (mem_Ioc.mp hd).1).2
          exact mul_le_of_le_one_right vonMangoldt_nonneg (by linarith)
      _ = Chebyshev.psi N := by rw [Chebyshev.psi, Nat.floor_natCast]
      _ ≤ _ := Chebyshev.psi_le_const_mul_self (by positivity)
  obtain ⟨hf1, hf2⟩ := s27_log_factorial_bounds N
  set A := ∑ m ∈ Ioc 0 N, Λ m / m
  have hA : A = (Real.log N.factorial + E) / N := by
    rw [eq_div_iff hN'.ne']; linarith
  rw [hA]
  constructor
  · rw [le_div_iff₀ hN']; nlinarith
  · rw [div_le_iff₀ hN']; nlinarith


/-- `0 ≤ ∑_{n ≤ N} Λ(n)/n - ∑_{p ≤ N} (ln p)/p ≤ ∑' e`. -/
theorem s27_vonMangoldt_sub_prime_bounds (N : ℕ) :
    0 ≤ ∑ m ∈ Ioc 0 N, Λ m / m - ∑ p ∈ Nat.primesLE N, Real.log p / p ∧
      ∑ m ∈ Ioc 0 N, Λ m / m - ∑ p ∈ Nat.primesLE N, Real.log p / p ≤
        ∑' a, s27_errLog a := by
  rw [s27_sum_vonMangoldt_div, ← sum_sub_distrib]
  have hterm : ∀ p ∈ Nat.primesLE N,
      0 ≤ ∑ k ∈ Icc 1 (Nat.log p N), Real.log p / (p : ℝ) ^ k - Real.log p / p ∧
      ∑ k ∈ Icc 1 (Nat.log p N), Real.log p / (p : ℝ) ^ k - Real.log p / p ≤
        s27_errLog p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hpN : p ≤ N := Nat.le_of_mem_primesLE hp
    have hK : 1 ≤ Nat.log p N := Nat.le_log_of_pow_le hpp.one_lt (by simpa using hpN)
    obtain ⟨g1, g2⟩ := s27_geom_bounds hp2 hK
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have he : ∑ k ∈ Icc 1 (Nat.log p N), Real.log p / (p : ℝ) ^ k =
        Real.log p * ∑ k ∈ Icc 1 (Nat.log p N), 1 / (p : ℝ) ^ k := by
      rw [mul_sum]; exact sum_congr rfl fun k _ ↦ by ring
    rw [he]
    constructor
    · have := mul_le_mul_of_nonneg_left g1 hl
      rw [mul_one_div] at this; linarith
    · have := mul_le_mul_of_nonneg_left g2 hl
      unfold s27_errLog
      have hp1 : (0 : ℝ) < p - 1 := by linarith
      have h1 : Real.log p * (1 / ((p : ℝ) - 1)) - Real.log p / p =
          Real.log p / (p * ((p : ℝ) - 1)) := by field_simp; ring
      have h2 : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
      linarith
  constructor
  · exact sum_nonneg fun p hp ↦ (hterm p hp).1
  · calc _ ≤ ∑ p ∈ Nat.primesLE N, s27_errLog p := sum_le_sum fun p hp ↦ (hterm p hp).2
      _ ≤ _ := s27_summable_errLog.sum_le_tsum _ fun a _ ↦ s27_errLog_nonneg a

/-- DLMF 27.11.10 (proof). -/
theorem s27_sum_log_prime_div_asymptotic :
    (fun x : ℝ ↦ ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x) =O[atTop]
      fun _ ↦ (1 : ℝ) := by
  refine IsBigO.of_bound (∑' a, s27_errLog a + 10) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hlN : Real.log N ≤ Real.log x := Real.log_le_log (by positivity) hNx
  have hdiff : Real.log x - Real.log N ≤ 1 := by
    rw [← Real.log_div hx0.ne' (by positivity)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by positivity), div_le_one (by positivity)]
    linarith
  obtain ⟨a1, a2⟩ := s27_sum_vonMangoldt_div_bounds hN1
  obtain ⟨b1, b2⟩ := s27_vonMangoldt_sub_prime_bounds N
  have hl4 : Real.log 4 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    calc (4 : ℝ) < 2.7182818283 ^ 2 := by norm_num
      _ < Real.exp 1 ^ 2 := by gcongr
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hC0 : 0 ≤ ∑' a, s27_errLog a := tsum_nonneg s27_errLog_nonneg
  rw [norm_one, mul_one, Real.norm_eq_abs, abs_le]
  constructor <;> linarith


/-- The constant bounding `|∑_{p ≤ N} (ln p)/p - ln N|`. -/
noncomputable def s27_mertensC : ℝ := ∑' a, s27_errLog a + 6

theorem s27_mertensC_nonneg : 0 ≤ s27_mertensC := by
  have : 0 ≤ ∑' a, s27_errLog a := tsum_nonneg s27_errLog_nonneg
  unfold s27_mertensC; linarith

/-- `|∑_{p ≤ N} (ln p)/p - ln N| ≤ C` for `N ≥ 1`. -/
theorem s27_prime_log_div_bound {N : ℕ} (hN : 1 ≤ N) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ s27_mertensC := by
  obtain ⟨a1, a2⟩ := s27_sum_vonMangoldt_div_bounds hN
  obtain ⟨b1, b2⟩ := s27_vonMangoldt_sub_prime_bounds N
  have hl4 : Real.log 4 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    calc (4 : ℝ) < 2.7182818283 ^ 2 := by norm_num
      _ < Real.exp 1 ^ 2 := by gcongr
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hC0 : 0 ≤ ∑' a, s27_errLog a := tsum_nonneg s27_errLog_nonneg
  unfold s27_mertensC
  rw [abs_le]
  constructor <;> linarith

/-- Sums over `primesLE` as sums over `range` with an indicator. -/
theorem s27_sum_primesLE (h : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, h p = ∑ m ∈ range (N + 1), if m.Prime then h m else 0 := by
  rw [← sum_filter]; rfl

/-- `P(n) = ∑_{p ≤ n} (ln p)/p`. -/
noncomputable def s27_P (n : ℕ) : ℝ := ∑ p ∈ Nat.primesLE n, Real.log p / p

/-- `f(n) = 1/ln n` (with `f 0 = f 1 = 0`). -/
noncomputable def s27_f (n : ℕ) : ℝ := 1 / Real.log n

/-- Abel summation: `∑_{p ≤ N} 1/p = P(N) f(N) + ∑_{n < N} P(n) (f(n) - f(n+1))`. -/
theorem s27_abel (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, (1 / p : ℝ) =
      s27_P N * s27_f N + ∑ n ∈ range N, s27_P n * (s27_f n - s27_f (n + 1)) := by
  have hP : ∀ n, s27_P n = ∑ m ∈ range (n + 1), if m.Prime then Real.log m / m else 0 :=
    fun n ↦ s27_sum_primesLE _ n
  rw [s27_sum_primesLE]
  induction N with
  | zero => simp [hP, s27_f]
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ _ N, hP (N + 1), sum_range_succ, ← hP N]
    have : (if (N + 1).Prime then (1 / ((N + 1 : ℕ) : ℝ)) else 0) =
        (if (N + 1).Prime then Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) else 0) *
          s27_f (N + 1) := by
      split_ifs with hp
      · have : Real.log ((N + 1 : ℕ) : ℝ) ≠ 0 := by
          have := Real.log_pos (show (1 : ℝ) < ((N + 1 : ℕ) : ℝ) by exact_mod_cast hp.one_lt)
          exact this.ne'
        simp only [s27_f]; field_simp
      · simp
    rw [this]; ring


/-- `G(n) = P(n)(f(n) - f(n+1)) - (ln ln (n+1) - ln ln n)`. -/
noncomputable def s27_G (n : ℕ) : ℝ :=
  s27_P n * (s27_f n - s27_f (n + 1)) -
    (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n))

theorem s27_f_nonneg (n : ℕ) : 0 ≤ s27_f n := by
  unfold s27_f
  have : 0 ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  positivity

/-- For `n ≥ 2`: `0 ≤ f(n) - f(n+1)` and `|G(n)| ≤ (C + 1)(f(n) - f(n+1))`. -/
theorem s27_G_bound {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ s27_f n - s27_f (n + 1) ∧
      |s27_G n| ≤ (s27_mertensC + 1) * (s27_f n - s27_f (n + 1)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set L0 := Real.log n with hL0
  set L1 := Real.log ((n + 1 : ℕ) : ℝ) with hL1
  have hc : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
  have hL0p : 0 < L0 := Real.log_pos (by linarith)
  have hL01 : L0 ≤ L1 := Real.log_le_log hn0 (by rw [hc]; linarith)
  have hL1p : 0 < L1 := lt_of_lt_of_le hL0p hL01
  have hd : L1 - L0 ≤ 1 / n := by
    rw [hL1, hL0, ← Real.log_div (by positivity) hn0.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    rw [hc]; field_simp; ring
  have hd1 : L1 - L0 ≤ 1 := hd.trans (by rw [div_le_one hn0]; linarith)
  have hh : s27_f n - s27_f (n + 1) = (L1 - L0) / (L0 * L1) := by
    simp only [s27_f]
    rw [← hL0, show Real.log ((n + 1 : ℕ) : ℝ) = L1 from rfl]
    field_simp
  have hh0 : 0 ≤ (L1 - L0) / (L0 * L1) := div_nonneg (by linarith) (by positivity)
  refine ⟨hh ▸ hh0, ?_⟩
  -- D = ln(L1/L0)
  have hD : Real.log L1 - Real.log L0 = Real.log (L1 / L0) := (Real.log_div hL1p.ne' hL0p.ne').symm
  have hDu : Real.log (L1 / L0) ≤ (L1 - L0) / L0 := by
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    field_simp
  have hDl : (L1 - L0) / L1 ≤ Real.log (L1 / L0) := by
    have := Real.log_le_sub_one_of_pos (show 0 < L0 / L1 by positivity)
    rw [Real.log_div hL0p.ne' hL1p.ne'] at this
    rw [Real.log_div hL1p.ne' hL0p.ne']
    have he : L0 / L1 - 1 = -((L1 - L0) / L1) := by field_simp; ring
    linarith
  have hR := s27_prime_log_div_bound (show 1 ≤ n by omega)
  set R := s27_P n - L0 with hRdef
  have hPe : s27_P n = L0 + R := by rw [hRdef]; ring
  have hGe : s27_G n = R * ((L1 - L0) / (L0 * L1)) +
      ((L1 - L0) / L1 - Real.log (L1 / L0)) := by
    unfold s27_G
    rw [hh, hPe, ← hL0, ← hD]
    have : L0 * ((L1 - L0) / (L0 * L1)) = (L1 - L0) / L1 := by field_simp
    rw [← hL1]
    linear_combination this
  have hgap : Real.log (L1 / L0) - (L1 - L0) / L1 ≤ (L1 - L0) / (L0 * L1) := by
    have : (L1 - L0) / L0 - (L1 - L0) / L1 = (L1 - L0) * ((L1 - L0) / (L0 * L1)) := by
      field_simp
    have h2 : (L1 - L0) * ((L1 - L0) / (L0 * L1)) ≤ (L1 - L0) / (L0 * L1) :=
      mul_le_of_le_one_left hh0 hd1
    linarith
  have hRb : |R * ((L1 - L0) / (L0 * L1))| ≤ s27_mertensC * ((L1 - L0) / (L0 * L1)) := by
    rw [abs_mul, abs_of_nonneg hh0]
    exact mul_le_mul_of_nonneg_right (by simpa [hRdef, s27_P] using hR) hh0
  rw [hGe, hh]
  rw [abs_le] at hRb ⊢
  constructor <;> nlinarith

/-- Telescoped tail bound: `∑_{i < M} |G(i + N)| ≤ (C + 1) f(N)` for `N ≥ 2`. -/
theorem s27_G_tail {N : ℕ} (hN : 2 ≤ N) (M : ℕ) :
    ∑ i ∈ range M, |s27_G (i + N)| ≤ (s27_mertensC + 1) * s27_f N := by
  calc ∑ i ∈ range M, |s27_G (i + N)|
      ≤ ∑ i ∈ range M, (s27_mertensC + 1) * (s27_f (i + N) - s27_f (i + 1 + N)) := by
        refine sum_le_sum fun i _ ↦ ?_
        have := (s27_G_bound (show 2 ≤ i + N by omega)).2
        rwa [show i + N + 1 = i + 1 + N by ring] at this
    _ = (s27_mertensC + 1) * (s27_f N - s27_f (M + N)) := by
        rw [← mul_sum, sum_range_sub' (fun i ↦ s27_f (i + N)), zero_add]
    _ ≤ (s27_mertensC + 1) * s27_f N := by
        have := s27_f_nonneg (M + N)
        have := s27_mertensC_nonneg
        nlinarith

theorem s27_summable_G : Summable s27_G := by
  rw [← summable_nat_add_iff 2]
  refine Summable.of_abs ?_
  exact summable_of_sum_range_le (fun _ ↦ abs_nonneg _) (s27_G_tail le_rfl)

/-- Mertens 27.11.8 for integer `N ≥ 2`. -/
theorem s27_mertens_nat {N : ℕ} (hN : 2 ≤ N) :
    |∑ p ∈ Nat.primesLE N, (1 / p : ℝ) - (Real.log (Real.log N) + (1 + ∑' n, s27_G n))| ≤
      (2 * s27_mertensC + 1) * s27_f N := by
  have habel := s27_abel N
  have htel : ∑ n ∈ range N, s27_P n * (s27_f n - s27_f (n + 1)) =
      ∑ n ∈ range N, s27_G n + Real.log (Real.log N) := by
    unfold s27_G
    rw [sum_sub_distrib]
    have := sum_range_sub (fun n ↦ Real.log (Real.log n)) N
    simp only [Nat.cast_zero, Real.log_zero, sub_zero] at this
    push_cast at this ⊢
    rw [this]; ring
  have hsplit := s27_summable_G.sum_add_tsum_nat_add N
  have htail : |∑' i, s27_G (i + N)| ≤ (s27_mertensC + 1) * s27_f N := by
    have hs : Summable fun i ↦ |s27_G (i + N)| :=
      summable_of_sum_range_le (fun _ ↦ abs_nonneg _) (s27_G_tail hN)
    calc |∑' i, s27_G (i + N)| ≤ ∑' i, |s27_G (i + N)| := by
          rw [← Real.norm_eq_abs]
          exact norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hs)
      _ ≤ _ := Real.tsum_le_of_sum_range_le (fun _ ↦ abs_nonneg _) (s27_G_tail hN)
  have hN1 : 1 ≤ N := by omega
  have hR := s27_prime_log_div_bound hN1
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hPf : s27_P N * s27_f N = 1 + (s27_P N - Real.log N) * s27_f N := by
    simp only [s27_f]; field_simp; ring
  have hRf : |(s27_P N - Real.log N) * s27_f N| ≤ s27_mertensC * s27_f N := by
    rw [abs_mul, abs_of_nonneg (s27_f_nonneg N)]
    exact mul_le_mul_of_nonneg_right hR (s27_f_nonneg N)
  rw [habel, htel, hPf, ← hsplit]
  have he : 1 + (s27_P N - Real.log N) * s27_f N + (∑ n ∈ range N, s27_G n +
      Real.log (Real.log N)) - (Real.log (Real.log N) + (1 + (∑ i ∈ range N, s27_G i +
        ∑' i, s27_G (i + N)))) = (s27_P N - Real.log N) * s27_f N - ∑' i, s27_G (i + N) := by
    ring
  rw [he]
  calc _ ≤ |(s27_P N - Real.log N) * s27_f N| + |∑' i, s27_G (i + N)| := abs_sub _ _
    _ ≤ _ := by linarith


/-- DLMF 27.11.8 (proof). -/
theorem s27_sum_prime_inv_asymptotic :
    ∃ A : ℝ, (fun x : ℝ ↦ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 / p : ℝ) - (Real.log (Real.log x) + A))
      =O[atTop] fun x ↦ 1 / Real.log x := by
  refine ⟨1 + ∑' n, s27_G n, IsBigO.of_bound (2 * (2 * s27_mertensC + 2)) ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hcore := s27_mertens_nat hN2
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlNx : Real.log N ≤ Real.log x := Real.log_le_log (by positivity) hNx
  have hlx : 0 < Real.log x := lt_of_lt_of_le hlN hlNx
  have hdiff : Real.log x - Real.log N ≤ 1 / N := by
    rw [← Real.log_div hx0.ne' (by positivity)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    linarith
  have hl2 : 1 / 2 ≤ Real.log N := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hN2'
    linarith
  have h1N : 1 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hlx2 : Real.log x ≤ 2 * Real.log N := by linarith
  -- ln ln x - ln ln N
  have hll0 : 0 ≤ Real.log (Real.log x) - Real.log (Real.log N) := by
    have := Real.log_le_log hlN hlNx; linarith
  have hll1 : Real.log (Real.log x) - Real.log (Real.log N) ≤ s27_f N := by
    rw [← Real.log_div hlx.ne' hlN.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one hlN.ne', s27_f, div_le_div_iff_of_pos_right hlN]
    linarith
  have hfN : s27_f N ≤ 2 * (1 / Real.log x) := by
    rw [s27_f, div_le_iff₀ hlN, mul_comm, ← mul_assoc, mul_one_div, mul_comm,
      le_div_iff₀ hlx]
    linarith
  have hC := s27_mertensC_nonneg
  have hf0 := s27_f_nonneg N
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  have he : ∑ p ∈ Nat.primesLE N, (1 / p : ℝ) - (Real.log (Real.log x) + (1 + ∑' n, s27_G n)) =
      (∑ p ∈ Nat.primesLE N, (1 / p : ℝ) - (Real.log (Real.log N) + (1 + ∑' n, s27_G n))) -
        (Real.log (Real.log x) - Real.log (Real.log N)) := by ring
  rw [he]
  calc _ ≤ |∑ p ∈ Nat.primesLE N, (1 / p : ℝ) - (Real.log (Real.log N) +
        (1 + ∑' n, s27_G n))| + |Real.log (Real.log x) - Real.log (Real.log N)| := abs_sub _ _
    _ ≤ (2 * s27_mertensC + 1) * s27_f N + s27_f N := by
        rw [abs_of_nonneg hll0]; linarith
    _ = (2 * s27_mertensC + 2) * s27_f N := by ring
    _ ≤ (2 * s27_mertensC + 2) * (2 * (1 / Real.log x)) :=
        mul_le_mul_of_nonneg_left hfN (by linarith)
    _ = _ := by ring


/-- Mean-value bounds for `t ↦ t^(α+1)`: `p u^α (v-u) ≤ v^p - u^p ≤ p v^α (v-u)`. -/
theorem s27_rpow_mvt {α : ℝ} (hα : 0 < α) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (α + 1) * u ^ α * (v - u) ≤ v ^ (α + 1) - u ^ (α + 1) ∧
      v ^ (α + 1) - u ^ (α + 1) ≤ (α + 1) * v ^ α * (v - u) := by
  have hp : 1 ≤ α + 1 := by linarith
  constructor
  · rcases eq_or_lt_of_le hu with rfl | hu0
    · rw [Real.zero_rpow hα.ne', Real.zero_rpow (by linarith)]
      have : 0 ≤ v ^ (α + 1) := Real.rpow_nonneg (by linarith) _
      simpa using this
    · have hb := one_add_mul_self_le_rpow_one_add (s := v / u - 1) (by
        have : 0 ≤ v / u := div_nonneg (by linarith) hu0.le
        linarith) hp
      rw [add_sub_cancel] at hb
      have hvu : v = u * (v / u) := by field_simp
      have h1 : v ^ (α + 1) = u ^ (α + 1) * (v / u) ^ (α + 1) := by
        conv_lhs => rw [hvu]
        exact Real.mul_rpow hu0.le (div_nonneg (by linarith) hu0.le)
      have h2 : u ^ (α + 1) = u ^ α * u := by rw [Real.rpow_add hu0, Real.rpow_one]
      have hup : 0 ≤ u ^ (α + 1) := Real.rpow_nonneg hu0.le _
      have h3 : u ^ (α + 1) * (1 + (α + 1) * (v / u - 1)) =
          u ^ (α + 1) + (α + 1) * u ^ α * (v - u) := by
        rw [h2]; field_simp
      nlinarith [mul_le_mul_of_nonneg_left hb hup]
  · have hv0 : 0 < v ∨ v = 0 := by
      rcases eq_or_lt_of_le (hu.trans huv) with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    rcases hv0 with hv0 | hv0
    · have hb := one_add_mul_self_le_rpow_one_add (s := u / v - 1) (by
        have : 0 ≤ u / v := div_nonneg hu hv0.le
        linarith) hp
      rw [add_sub_cancel] at hb
      have huv' : u = v * (u / v) := by field_simp
      have h1 : u ^ (α + 1) = v ^ (α + 1) * (u / v) ^ (α + 1) := by
        conv_lhs => rw [huv']
        exact Real.mul_rpow hv0.le (div_nonneg hu hv0.le)
      have h2 : v ^ (α + 1) = v ^ α * v := by rw [Real.rpow_add hv0, Real.rpow_one]
      have hvp : 0 ≤ v ^ (α + 1) := Real.rpow_nonneg hv0.le _
      have h3 : v ^ (α + 1) * (1 + (α + 1) * (u / v - 1)) =
          v ^ (α + 1) - (α + 1) * v ^ α * (v - u) := by
        rw [h2]; field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_left hb hvp]
    · have : u = 0 := le_antisymm (hv0 ▸ huv) hu
      subst this; subst hv0; simp

/-- `M^p/p ≤ ∑_{m ≤ M} m^α ≤ M^p/p + M^α`, `p = α + 1`. -/
theorem s27_sum_rpow_bounds {α : ℝ} (hα : 0 < α) (M : ℕ) :
    (M : ℝ) ^ (α + 1) / (α + 1) ≤ ∑ m ∈ Ioc 0 M, (m : ℝ) ^ α ∧
      ∑ m ∈ Ioc 0 M, (m : ℝ) ^ α ≤ (M : ℝ) ^ (α + 1) / (α + 1) + (M : ℝ) ^ α := by
  have hp : 0 < α + 1 := by linarith
  induction M with
  | zero =>
    simp [Real.zero_rpow hα.ne', Real.zero_rpow hp.ne']
  | succ M ih =>
    rw [sum_Ioc_succ_top (by omega)]
    obtain ⟨h1, h2⟩ := s27_rpow_mvt hα (u := M) (v := (M + 1 : ℕ)) (by positivity)
      (by push_cast; linarith)
    have hd : ((M + 1 : ℕ) : ℝ) - M = 1 := by push_cast; ring
    rw [hd, mul_one] at h1 h2
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · rw [div_le_iff₀ hp] at ih1 ⊢
      nlinarith
    · have : (M : ℝ) ^ (α + 1) / (α + 1) + (M : ℝ) ^ α ≤ ((M + 1 : ℕ) : ℝ) ^ (α + 1) / (α + 1) := by
        rw [div_add' _ _ _ hp.ne', div_le_div_iff_of_pos_right hp]; linarith
      linarith


/-- Integral comparison: `∑_{i < M} f(N + i + 1) ≤ N^{-a}/a` for `f(t) = (t^{a+1})⁻¹`, `a > 0`. -/
theorem s27_tail_rpow {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ i ∈ range M, (((N + (i + 1 : ℕ) : ℝ)) ^ (a + 1))⁻¹ ≤ (N : ℝ) ^ (-a) / a := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun t : ℝ ↦ t ^ (-(a + 1))) (Set.Icc (N : ℝ) (N + M)) := by
    intro s hs t ht hst
    have hs0 : 0 < s := by linarith [hs.1]
    exact Real.rpow_le_rpow_of_nonpos hs0 hst (by linarith)
  have h := hanti.sum_le_integral
  have hint : ∫ t in (N : ℝ)..(N + M), t ^ (-(a + 1)) =
      (((N : ℝ) + M) ^ (-a) - (N : ℝ) ^ (-a)) / (-a) := by
    rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
    · congr 1 <;> ring_nf
    · rw [Set.uIcc_of_le (by linarith)]
      intro h0; linarith [h0.1]
  rw [hint] at h
  calc ∑ i ∈ range M, (((N + (i + 1 : ℕ) : ℝ)) ^ (a + 1))⁻¹
      = ∑ i ∈ range M, ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-(a + 1)) := by
        refine sum_congr rfl fun i _ ↦ ?_
        rw [Real.rpow_neg (by positivity)]
    _ ≤ _ := h
    _ ≤ (N : ℝ) ^ (-a) / a := by
        rw [div_neg, ← neg_div, neg_sub]
        have : 0 ≤ ((N : ℝ) + M) ^ (-a) := Real.rpow_nonneg (by positivity) _
        gcongr
        linarith

/-- `∑_{d ≤ N} d^{-a} ≤ 1 + (N^{1-a} - 1)/(1 - a)` for `a > 0`, `a ≠ 1`, `N ≥ 1`. -/
theorem s27_sum_rpow_neg_le {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ a)⁻¹ ≤ 1 + ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hanti : AntitoneOn (fun t : ℝ ↦ t ^ (-a)) (Set.Icc (1 : ℝ) (1 + M)) := by
    intro s hs t ht hst
    have hs0 : 0 < s := by linarith [hs.1]
    exact Real.rpow_le_rpow_of_nonpos hs0 hst (by linarith)
  have h := hanti.sum_le_integral
  have hint : ∫ t in (1 : ℝ)..(1 + M), t ^ (-a) =
      (((M + 1 : ℕ) : ℝ) ^ (1 - a) - 1) / (1 - a) := by
    rw [integral_rpow (Or.inr ⟨fun h ↦ ha1 (by linarith), ?_⟩)]
    · push_cast
      rw [Real.one_rpow, show -a + 1 = 1 - a by ring, add_comm (1 : ℝ)]
    · rw [Set.uIcc_of_le (by linarith)]
      intro h0; linarith [h0.1]
  rw [hint] at h
  have hsplit : ∑ d ∈ Ioc 0 (M + 1), ((d : ℝ) ^ a)⁻¹ =
      1 + ∑ i ∈ range M, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-a) := by
    have : Ioc 0 (M + 1) = insert 1 ((range M).map ⟨(· + 2), add_left_injective 2⟩) := by
      ext d; simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk]
      constructor
      · intro hd
        by_cases h1 : d = 1
        · exact Or.inl h1
        · exact Or.inr ⟨d - 2, by omega, by omega⟩
      · rintro (rfl | ⟨i, hi, rfl⟩) <;> omega
    rw [this, sum_insert (by simp), sum_map]
    simp only [Nat.cast_one, Real.one_rpow, inv_one, Function.Embedding.coeFn_mk]
    congr 1
    refine sum_congr rfl fun i _ ↦ ?_
    rw [Real.rpow_neg (by positivity)]
    push_cast; ring_nf
  rw [hsplit]
  linarith


/-- `∑_{n ≤ N} σ_α(n) = ∑_{d ≤ N} ∑_{m ≤ N/d} m^α` (real `α > 0`). -/
theorem s27_sum_sigmaR (α : ℝ) (hα : 0 < α) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α =
      ∑ d ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α := by
  let g : ArithmeticFunction ℝ := ⟨fun m ↦ (m : ℝ) ^ α, by simp [Real.zero_rpow hα.ne']⟩
  have h := sum_Ioc_mul_eq_sum_sum ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) g N
  have hI : Icc 1 N = Ioc 0 N := by ext; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI]
  have hl : ∀ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α =
      (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) * g) n := by
    intro n _
    rw [coe_zeta_mul_apply]; rfl
  rw [sum_congr rfl hl, h]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd0 : d ≠ 0 := (mem_Ioc.mp hd).1.ne'
  simp [natCoe_apply, zeta_apply, hd0, g]

/-- One term: `|S(⌊N/d⌋) - (N/d)^p/p| ≤ (N/d)^α`. -/
theorem s27_term_bound {α : ℝ} (hα : 0 < α) {N d : ℕ} (hd : d ∈ Ioc 0 N) :
    |∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α - (N : ℝ) ^ (α + 1) / (α + 1) * ((d : ℝ) ^ (α + 1))⁻¹|
      ≤ (N : ℝ) ^ α * ((d : ℝ) ^ α)⁻¹ := by
  obtain ⟨hd0, hdN⟩ := mem_Ioc.mp hd
  have hp : 0 < α + 1 := by linarith
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  set y : ℝ := (N : ℝ) / d
  obtain ⟨hM1, hM2⟩ := r27_div_bounds N d hd0
  set M := N / d
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hy1 : M ≤ y := hM1
  obtain ⟨s1, s2⟩ := s27_sum_rpow_bounds hα M
  obtain ⟨-, m2⟩ := s27_rpow_mvt hα hM0 hy1
  have hyM : y - M ≤ 1 := by linarith
  have hya : 0 ≤ y ^ α := Real.rpow_nonneg (by positivity) _
  have hMa : (M : ℝ) ^ α ≤ y ^ α := Real.rpow_le_rpow hM0 hy1 hα.le
  have hMp : (M : ℝ) ^ (α + 1) ≤ y ^ (α + 1) := Real.rpow_le_rpow hM0 hy1 hp.le
  have hyp : y ^ (α + 1) = (N : ℝ) ^ (α + 1) * ((d : ℝ) ^ (α + 1))⁻¹ := by
    rw [Real.div_rpow (by positivity) hdr.le, div_eq_mul_inv]
  have hyα : y ^ α = (N : ℝ) ^ α * ((d : ℝ) ^ α)⁻¹ := by
    rw [Real.div_rpow (by positivity) hdr.le, div_eq_mul_inv]
  rw [← hyα, mul_comm ((N : ℝ) ^ (α + 1) / (α + 1)), ← mul_div_assoc,
    mul_comm _ ((N : ℝ) ^ (α + 1)), ← hyp]
  have h3 : y ^ (α + 1) - (M : ℝ) ^ (α + 1) ≤ (α + 1) * y ^ α := by
    calc _ ≤ (α + 1) * y ^ α * (y - M) := m2
      _ ≤ (α + 1) * y ^ α * 1 := by gcongr
      _ = _ := by ring
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, ← sub_eq_neg_add, sub_le_iff_le_add]
    have : y ^ (α + 1) / (α + 1) ≤ (M : ℝ) ^ (α + 1) / (α + 1) + y ^ α := by
      rw [div_add' _ _ _ hp.ne', div_le_div_iff_of_pos_right hp]; linarith
    linarith
  · have : (M : ℝ) ^ (α + 1) / (α + 1) ≤ y ^ (α + 1) / (α + 1) := by gcongr
    linarith


/-- `Z = ∑ 1/d^p`. -/
noncomputable def s27_Z (α : ℝ) : ℝ := ∑' d : ℕ, ((d : ℝ) ^ (α + 1))⁻¹

/-- `0 ≤ Z - ∑_{d ≤ N} d^{-p} ≤ N^{-α}/α`. -/
theorem s27_Z_tail {α : ℝ} (hα : 0 < α) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ s27_Z α - ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ (α + 1))⁻¹ ∧
      s27_Z α - ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ (α + 1))⁻¹ ≤ (N : ℝ) ^ (-α) / α := by
  have hs : Summable fun d : ℕ ↦ ((d : ℝ) ^ (α + 1))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  have hsplit := hs.sum_add_tsum_nat_add (N + 1)
  have hr : ∑ d ∈ range (N + 1), ((d : ℝ) ^ (α + 1))⁻¹ = ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ (α + 1))⁻¹ := by
    rw [r27_range_eq_insert_Ioc, sum_insert (by simp)]
    simp [Real.zero_rpow (show α + 1 ≠ 0 by linarith)]
  rw [hr] at hsplit
  have he : s27_Z α - ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ (α + 1))⁻¹ =
      ∑' i, (((i + (N + 1) : ℕ) : ℝ) ^ (α + 1))⁻¹ := by
    rw [s27_Z, ← hsplit, add_sub_cancel_left]
  rw [he]
  constructor
  · exact tsum_nonneg fun i ↦ by positivity
  · refine Real.tsum_le_of_sum_range_le (fun i ↦ by positivity) fun M ↦ ?_
    have := s27_tail_rpow hα hN M
    convert this using 3 with i
    push_cast; ring_nf

/-- 27.11.5 for integer `N`: `|∑_{n ≤ N} σ_α(n) - Z N^p/p| ≤ N/(pα) + N^α ∑_{d ≤ N} d^{-α}`. -/
theorem s27_sigma_nat_bound {α : ℝ} (hα : 0 < α) {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α - s27_Z α * (N : ℝ) ^ (α + 1) / (α + 1)| ≤
      N / ((α + 1) * α) + (N : ℝ) ^ α * ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ α)⁻¹ := by
  have hp : 0 < α + 1 := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [s27_sum_sigmaR α hα]
  set A := ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ (α + 1))⁻¹
  have he : ∑ d ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α - s27_Z α * (N : ℝ) ^ (α + 1) /
      (α + 1) = ∑ d ∈ Ioc 0 N, (∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α -
        (N : ℝ) ^ (α + 1) / (α + 1) * ((d : ℝ) ^ (α + 1))⁻¹) -
        (N : ℝ) ^ (α + 1) / (α + 1) * (s27_Z α - A) := by
    rw [sum_sub_distrib, ← mul_sum]; ring
  rw [he]
  have h1 : |∑ d ∈ Ioc 0 N, (∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α -
      (N : ℝ) ^ (α + 1) / (α + 1) * ((d : ℝ) ^ (α + 1))⁻¹)| ≤
      (N : ℝ) ^ α * ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ α)⁻¹ := by
    rw [mul_sum]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd ↦ s27_term_bound hα hd)
  obtain ⟨t0, t1⟩ := s27_Z_tail hα hN
  have hNp : 0 ≤ (N : ℝ) ^ (α + 1) / (α + 1) := by positivity
  have hNN : (N : ℝ) ^ (α + 1) * (N : ℝ) ^ (-α) = N := by
    rw [← Real.rpow_add hN0]; simp
  have h2 : (N : ℝ) ^ (α + 1) / (α + 1) * (s27_Z α - A) ≤ N / ((α + 1) * α) := by
    calc _ ≤ (N : ℝ) ^ (α + 1) / (α + 1) * ((N : ℝ) ^ (-α) / α) :=
          mul_le_mul_of_nonneg_left t1 hNp
      _ = (N : ℝ) ^ (α + 1) * (N : ℝ) ^ (-α) / ((α + 1) * α) := by field_simp
      _ = _ := by rw [hNN]
  have h3 : 0 ≤ (N : ℝ) ^ (α + 1) / (α + 1) * (s27_Z α - A) := mul_nonneg hNp t0
  calc _ ≤ |∑ d ∈ Ioc 0 N, (∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α -
        (N : ℝ) ^ (α + 1) / (α + 1) * ((d : ℝ) ^ (α + 1))⁻¹)| +
        |(N : ℝ) ^ (α + 1) / (α + 1) * (s27_Z α - A)| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg h3]; linarith


/-- The integer bound of 27.11.5 is `O(N^β)`, `β = max(1, α)`. -/
theorem s27_sigma_nat_bigO {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α - s27_Z α * (N : ℝ) ^ (α + 1) / (α + 1)| ≤
        K * (N : ℝ) ^ max 1 α := by
  have hp : 0 < α + 1 := by linarith
  refine ⟨1 / ((α + 1) * α) + 1 + 1 / |1 - α|, by positivity, fun N hN ↦ ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hb := s27_sigma_nat_bound hα hN
  have hs := s27_sum_rpow_neg_le hα hα1 hN
  have hNa : 0 ≤ (N : ℝ) ^ α := by positivity
  refine hb.trans ?_
  have hab : 0 < |1 - α| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hα1))
  rcases lt_or_gt_of_ne hα1 with h | h
  · -- `α < 1`, `β = 1`
    rw [max_eq_left h.le, Real.rpow_one, abs_of_pos (by linarith)]
    have hNaN : (N : ℝ) ^ α ≤ N := by
      calc (N : ℝ) ^ α ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 h.le
        _ = N := Real.rpow_one _
    have hpow : (N : ℝ) ^ α * (N : ℝ) ^ (1 - α) = N := by
      rw [← Real.rpow_add hN0]; simp
    have h1a : 0 < 1 - α := by linarith
    have hI : (N : ℝ) ^ α * (((N : ℝ) ^ (1 - α) - 1) / (1 - α)) ≤ N / (1 - α) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right h1a, mul_sub, hpow]
      linarith
    calc (N : ℝ) / ((α + 1) * α) + (N : ℝ) ^ α * ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ α)⁻¹
        ≤ N / ((α + 1) * α) + (N : ℝ) ^ α * (1 + ((N : ℝ) ^ (1 - α) - 1) / (1 - α)) := by
          gcongr
      _ = N / ((α + 1) * α) + (N : ℝ) ^ α + (N : ℝ) ^ α * (((N : ℝ) ^ (1 - α) - 1) / (1 - α)) := by
          ring
      _ ≤ N / ((α + 1) * α) + N + N / (1 - α) := by linarith
      _ = _ := by ring
  · -- `α > 1`, `β = α`
    rw [max_eq_right h.le, abs_of_neg (by linarith)]
    have hNN : (N : ℝ) ≤ (N : ℝ) ^ α := by
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le hN1 h.le
    have hI : ((N : ℝ) ^ (1 - α) - 1) / (1 - α) ≤ 1 / -(1 - α) := by
      have : 0 ≤ (N : ℝ) ^ (1 - α) := by positivity
      have e1 : ((N : ℝ) ^ (1 - α) - 1) / (1 - α) = (1 - (N : ℝ) ^ (1 - α)) / (α - 1) := by
        rw [div_eq_div_iff (by linarith) (by linarith)]; ring
      rw [e1, neg_sub, div_le_div_iff_of_pos_right (by linarith)]
      linarith
    calc (N : ℝ) / ((α + 1) * α) + (N : ℝ) ^ α * ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ α)⁻¹
        ≤ (N : ℝ) ^ α / ((α + 1) * α) + (N : ℝ) ^ α * (1 + 1 / -(1 - α)) := by
          gcongr
          linarith
      _ = _ := by ring


theorem s27_Z_nonneg (α : ℝ) : 0 ≤ s27_Z α := tsum_nonneg fun d ↦ by positivity

/-- `ζ(α + 1) = Z` for real `α > 0`. -/
theorem s27_riemannZeta_eq_Z {α : ℝ} (hα : 0 < α) :
    riemannZeta ((α : ℂ) + 1) = (s27_Z α : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simp; linarith), s27_Z, Complex.ofReal_tsum]
  refine tsum_congr fun n ↦ ?_
  rw [Complex.ofReal_inv, Complex.ofReal_cpow (by positivity), one_div]
  push_cast; rfl

/-- `σ_α(n)` for real `α` is the real divisor sum. -/
theorem s27_sigmaC_ofReal (α : ℝ) (n : ℕ) :
    sigmaC α n = ((∑ d ∈ n.divisors, (d : ℝ) ^ α : ℝ) : ℂ) := by
  rw [sigmaC_apply, Complex.ofReal_sum]
  refine sum_congr rfl fun d _ ↦ ?_
  rw [Complex.ofReal_cpow (by positivity)]
  rfl

/-- DLMF 27.11.5 (proof). -/
theorem s27_sum_sigmaC_asymptotic {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    HasPartialSumAsymptotic (fun n ↦ sigmaC α n)
      (fun x ↦ riemannZeta (α + 1) / (α + 1) * ((x ^ (α + 1) : ℝ) : ℂ))
      (fun x ↦ ((x ^ max 1 α : ℝ) : ℂ)) := by
  unfold HasPartialSumAsymptotic
  obtain ⟨K, hK0, hK⟩ := s27_sigma_nat_bigO hα hα1
  have hp : 0 < α + 1 := by linarith
  have he : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, sigmaC α n -
      riemannZeta (α + 1) / (α + 1) * ((x ^ (α + 1) : ℝ) : ℂ)) =
      fun x ↦ ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, (d : ℝ) ^ α -
        s27_Z α * x ^ (α + 1) / (α + 1) : ℝ) : ℂ) := by
    funext x
    simp only [s27_sigmaC_ofReal, s27_riemannZeta_eq_Z hα]
    push_cast; ring
  rw [he]
  refine r27_isBigO_ofReal (K + s27_Z α) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hcore := hK N hN1
  obtain ⟨-, m2⟩ := s27_rpow_mvt hα (u := N) (v := x) (by positivity) hNx
  obtain ⟨m1, -⟩ := s27_rpow_mvt hα (u := N) (v := x) (by positivity) hNx
  have hβ : 0 ≤ max 1 α := le_max_of_le_left zero_le_one
  have hxβ : 0 ≤ x ^ max 1 α := by positivity
  rw [abs_of_nonneg hxβ]
  have hNβ : (N : ℝ) ^ max 1 α ≤ x ^ max 1 α := Real.rpow_le_rpow (by positivity) hNx hβ
  have hxα : x ^ α ≤ x ^ max 1 α := Real.rpow_le_rpow_of_exponent_le hx (le_max_right _ _)
  have hZ := s27_Z_nonneg α
  have hxa0 : 0 ≤ x ^ α := by positivity
  have hd : x ^ (α + 1) - (N : ℝ) ^ (α + 1) ≤ (α + 1) * x ^ α := by
    calc _ ≤ (α + 1) * x ^ α * (x - N) := m2
      _ ≤ (α + 1) * x ^ α * 1 := by gcongr; linarith
      _ = _ := by ring
  have hd0 : 0 ≤ x ^ (α + 1) - (N : ℝ) ^ (α + 1) := by
    have : 0 ≤ (α + 1) * (N : ℝ) ^ α * (x - N) := by
      have : 0 ≤ x - N := by linarith
      positivity
    linarith
  have hZd : s27_Z α * (x ^ (α + 1) - (N : ℝ) ^ (α + 1)) / (α + 1) ≤ s27_Z α * x ^ max 1 α := by
    rw [div_le_iff₀ hp]
    calc s27_Z α * (x ^ (α + 1) - (N : ℝ) ^ (α + 1)) ≤ s27_Z α * ((α + 1) * x ^ α) :=
          mul_le_mul_of_nonneg_left hd hZ
      _ ≤ s27_Z α * ((α + 1) * x ^ max 1 α) := by gcongr
      _ = _ := by ring
  have hZd0 : 0 ≤ s27_Z α * (x ^ (α + 1) - (N : ℝ) ^ (α + 1)) / (α + 1) := by positivity
  have he2 : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α - s27_Z α * x ^ (α + 1) / (α + 1)
      = (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α -
        s27_Z α * (N : ℝ) ^ (α + 1) / (α + 1)) -
        s27_Z α * (x ^ (α + 1) - (N : ℝ) ^ (α + 1)) / (α + 1) := by ring
  rw [he2]
  have hKN : K * (N : ℝ) ^ max 1 α ≤ K * x ^ max 1 α := mul_le_mul_of_nonneg_left hNβ hK0
  calc _ ≤ |∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α -
        s27_Z α * (N : ℝ) ^ (α + 1) / (α + 1)| +
        |s27_Z α * (x ^ (α + 1) - (N : ℝ) ^ (α + 1)) / (α + 1)| := abs_sub _ _
    _ ≤ K * x ^ max 1 α + s27_Z α * x ^ max 1 α := by
        rw [abs_of_nonneg hZd0]; linarith
    _ = _ := by ring


end R27Helpers

/-- DLMF 27.11.2 (Dirichlet): `∑_{n≤x} d(n) = x ln x + (2γ - 1)x + O(√x)`. -/
@[dlmf 27.11.E2]
theorem sum_sigma_zero_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (σ 0 n : ℂ))
      (fun x ↦ (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x : ℝ))
      (fun x ↦ (Real.sqrt x : ℂ)) :=
  s27_sum_sigma_zero_asymptotic

/-- §27.11 after 27.11.2, Huxley's bound in Dirichlet's divisor problem: the error term in
27.11.2 is `O(x^θ)` for every `θ > 131/416`. -/
@[dlmf 27.11]
theorem sum_sigma_zero_huxley {θ : ℝ} (hθ : 131 / 416 < θ) :
    HasPartialSumAsymptotic (fun n ↦ (σ 0 n : ℂ))
      (fun x ↦ (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x : ℝ))
      (fun x ↦ ((x ^ θ : ℝ) : ℂ)) := by
  sorry

/-- DLMF 27.11.3: `∑_{n≤x} d(n)/n = ½(ln x)² + 2γ ln x + O(1)`. -/
@[dlmf 27.11.E3]
theorem sum_sigma_zero_div_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (σ 0 n : ℂ) / n)
      (fun x ↦ (Real.log x ^ 2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log x : ℝ))
      (fun _ ↦ (1 : ℂ)) :=
  s27_sum_sigma_zero_div_asymptotic

/-- DLMF 27.11.4: `∑_{n≤x} σ₁(n) = (π²/12) x² + O(x ln x)`. -/
@[dlmf 27.11.E4]
theorem sum_sigma_one_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (σ 1 n : ℂ)) (fun x ↦ (π ^ 2 / 12 * x ^ 2 : ℝ))
      (fun x ↦ (x * Real.log x : ℝ)) :=
  r27_sum_sigma_one_asymptotic

/-- DLMF 27.11.5: `∑_{n≤x} σ_α(n) = ζ(α + 1)/(α + 1) x^{α+1} + O(x^β)`, `α > 0`, `α ≠ 1`,
`β = max(1, α)`. -/
@[dlmf 27.11.E5]
theorem sum_sigmaC_asymptotic {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    HasPartialSumAsymptotic (fun n ↦ sigmaC α n)
      (fun x ↦ riemannZeta (α + 1) / (α + 1) * ((x ^ (α + 1) : ℝ) : ℂ))
      (fun x ↦ ((x ^ max 1 α : ℝ) : ℂ)) :=
  s27_sum_sigmaC_asymptotic hα hα1

/-- DLMF 27.11.6: `∑_{n≤x} φ(n) = (3/π²) x² + O(x ln x)`. -/
@[dlmf 27.11.E6]
theorem sum_totient_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (n.totient : ℂ)) (fun x ↦ (3 / π ^ 2 * x ^ 2 : ℝ))
      (fun x ↦ (x * Real.log x : ℝ)) :=
  r27_sum_totient_asymptotic

/-- DLMF 27.11.7: `∑_{n≤x} φ(n)/n = (6/π²) x + O(ln x)`. -/
@[dlmf 27.11.E7]
theorem sum_totient_div_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (n.totient : ℂ) / n) (fun x ↦ (6 / π ^ 2 * x : ℝ))
      (fun x ↦ (Real.log x : ℂ)) :=
  r27_sum_totient_div_asymptotic

/-- DLMF 27.11.8 (Mertens): there is a constant `A` with
`∑_{p≤x} 1/p = ln ln x + A + O(1/ln x)`. -/
@[dlmf 27.11.E8]
theorem sum_prime_inv_asymptotic :
    ∃ A : ℝ, (fun x : ℝ ↦ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 / p : ℝ) - (Real.log (Real.log x) + A))
      =O[atTop] fun x ↦ 1 / Real.log x :=
  s27_sum_prime_inv_asymptotic

/-- DLMF 27.11.9: for `(h, k) = 1`, `k > 0`, there is a constant `B` (depending on `h, k`) with
`∑_{p≤x, p≡h (mod k)} 1/p = (1/φ(k)) ln ln x + B + O(1/ln x)`. -/
@[dlmf 27.11.E9]
theorem sum_prime_inv_ap_asymptotic {h k : ℕ} (hk : 0 < k) (hhk : h.Coprime k) :
    ∃ B : ℝ, (fun x : ℝ ↦ ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ p ≡ h [MOD k]), (1 / p : ℝ)
      - (Real.log (Real.log x) / k.totient + B)) =O[atTop] fun x ↦ 1 / Real.log x := by
  sorry

/-- DLMF 27.11.10 (Mertens): `∑_{p≤x} (ln p)/p = ln x + O(1)`. -/
@[dlmf 27.11.E10]
theorem sum_log_prime_div_asymptotic :
    (fun x : ℝ ↦ ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x) =O[atTop]
      fun _ ↦ (1 : ℝ) :=
  s27_sum_log_prime_div_asymptotic

/-- DLMF 27.11.11: for `(h, k) = 1`, `k > 0`,
`∑_{p≤x, p≡h (mod k)} (ln p)/p = (1/φ(k)) ln x + O(1)`. -/
@[dlmf 27.11.E11]
theorem sum_log_prime_div_ap_asymptotic {h k : ℕ} (hk : 0 < k) (hhk : h.Coprime k) :
    (fun x : ℝ ↦ ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ p ≡ h [MOD k]), Real.log p / p
      - Real.log x / k.totient) =O[atTop] fun _ ↦ (1 : ℝ) := by
  sorry

/-- §27.11 after 27.11.11 and §27.12 (Prime Number Theorem paragraph): Dirichlet's theorem,
there are infinitely many primes `p ≡ h (mod k)` when `(h, k) = 1`. -/
@[dlmf 27.11, dlmf 27.12]
theorem infinite_primes_mod {h k : ℕ} (hk : 0 < k) (hhk : h.Coprime k) :
    {p : ℕ | p.Prime ∧ p ≡ h [MOD k]}.Infinite :=
  Nat.infinite_setOfPred_prime_and_modEq hk.ne' hhk

/-- DLMF 27.11.12: for some constant `C > 0`, `∑_{n≤x} μ(n) = O(x e^{-C√(ln x)})`. -/
@[dlmf 27.11.E12]
theorem sum_moebius_isBigO :
    ∃ C : ℝ, 0 < C ∧ (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ))) =O[atTop]
      fun x ↦ x * Real.exp (-C * Real.sqrt (Real.log x)) := by
  sorry

/-- DLMF 27.11.13: `lim_{x→∞} x⁻¹ ∑_{n≤x} μ(n) = 0` (equivalent to the prime number
theorem). -/
@[dlmf 27.11.E13]
theorem tendsto_sum_moebius_div :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)) / x) atTop (nhds 0) := by
  sorry

/-- DLMF 27.11.14: `lim_{x→∞} ∑_{n≤x} μ(n)/n = 0`. -/
@[dlmf 27.11.E14]
theorem tendsto_sum_moebius_div_self :
    Tendsto (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) / n) atTop (nhds 0) := by
  sorry

/-- DLMF 27.11.15: `lim_{x→∞} ∑_{n≤x} μ(n) ln n / n = -1`. -/
@[dlmf 27.11.E15]
theorem tendsto_sum_moebius_log_div :
    Tendsto (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * Real.log n / n) atTop
      (nhds (-1)) := by
  sorry

/-- §27.11 after 27.11.15, the prime number theorem for arithmetic progressions: for
`(h, k) = 1`, `k > 0`, the number of primes `p ≤ x` with `p ≡ h (mod k)` is asymptotic to
`x/(φ(k) ln x)`. -/
@[dlmf 27.11]
theorem primeCounting_ap_isEquivalent {h k : ℕ} (hk : 0 < k) (hhk : h.Coprime k) :
    (fun x : ℝ ↦ (((Nat.primesLE ⌊x⌋₊).filter (fun p ↦ p ≡ h [MOD k])).card : ℝ)) ~[atTop]
      fun x ↦ x / (k.totient * Real.log x) := by
  sorry

end DLMF.NumberTheory
