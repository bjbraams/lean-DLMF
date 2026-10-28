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
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Asymptotics of elementary arithmetic sums

Partial-sum estimates for divisor, totient and related arithmetic functions.

Source references and common attribution are retained in
`DLMF.NumberTheory.Asymptotics`.
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
lemma r27_range_eq_insert_Ioc (N : ℕ) : range (N + 1) = insert 0 (Ioc 0 N) := by
  ext n; simp only [mem_range, mem_insert, mem_Ioc]; omega

/-- Tail bound: `|A - ∑_{d ≤ N} a(d)/d²| ≤ 2/(N+1)` when `|a| ≤ 1` and `∑ a(d)/d² = A`. -/
lemma r27_tail_inv_sq {a : ℕ → ℝ} (ha : ∀ d, |a d| ≤ 1) {A : ℝ}
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
lemma r27_sum_inv_le (N : ℕ) : ∑ d ∈ Ioc 0 N, ((d : ℝ))⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  have hI : Ioc 0 N = Icc 1 N := by ext; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI]
  push_cast at h
  exact h

/-- `(N/d) - 1 < ⌊N/d⌋ ≤ N/d`. -/
lemma r27_div_bounds (N d : ℕ) (hd : 0 < d) :
    ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d ∧ (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · rw [le_div_iff₀ hd']; exact_mod_cast Nat.div_mul_le_self N d
  · rw [div_lt_iff₀ hd']
    have := Nat.lt_div_mul_add (a := N) hd
    have h2 : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
    linarith

/-- `∑_{m ≤ M} m = M(M+1)/2` in `ℝ`. -/
lemma r27_sum_Ioc_id (M : ℕ) : ∑ m ∈ Ioc 0 M, (m : ℝ) = M * (M + 1) / 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_Ioc_succ_top (by omega), ih]
    push_cast; ring

/-- Core estimate for `∑_{d ≤ N} a(d) T(⌊N/d⌋)`, `T(M) = M(M+1)/2`. -/
lemma r27_sum_triangle_bound {a : ℕ → ℝ} (ha : ∀ d, |a d| ≤ 1) {A : ℝ}
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
lemma r27_sum_floor_bound {a : ℕ → ℝ} (ha : ∀ d, |a d| ≤ 1) {A : ℝ}
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
lemma r27_isBigO_ofReal {u v : ℝ → ℝ} (c : ℝ) (h : ∀ᶠ x in atTop, |u x| ≤ c * |v x|) :
    (fun x ↦ (u x : ℂ)) =O[atTop] fun x ↦ (v x : ℂ) :=
  IsBigO.of_bound c (by simpa only [Complex.norm_real, Real.norm_eq_abs] using h)

/-- `1 ≤ ln x` for `x ≥ 3`. -/
lemma r27_one_le_log {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  norm_num at this
  linarith

/-- `∑_{n ≤ N} σ₁(n) = ∑_{d ≤ N} T(⌊N/d⌋)`. -/
lemma r27_sum_sigma_one (N : ℕ) :
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
lemma r27_quadratic_conversion {S : ℕ → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2)
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
lemma r27_linear_conversion {S : ℕ → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1)
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
lemma r27_sum_sigma_one_asymptotic :
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
lemma r27_totient_eq_sum (n : ℕ) (hn : 0 < n) :
    (n.totient : ℝ) = ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) * (x.2 : ℝ) := by
  have h := (sum_eq_iff_sum_mul_moebius_eq (R := ℝ) (f := fun n ↦ (n.totient : ℝ))
    (g := fun n ↦ (n : ℝ))).mp (fun n _ ↦ by exact_mod_cast Nat.sum_totient n) n hn
  exact h.symm

/-- `∑ μ(d)/d² = 6/π²`. -/
lemma r27_hasSum_moebius_div_sq :
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
lemma r27_sum_totient (N : ℕ) :
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
lemma r27_sum_totient_div (N : ℕ) :
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
lemma r27_sum_totient_asymptotic :
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
lemma r27_sum_totient_div_asymptotic :
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
lemma s27_card_filter_mul_le (N m d : ℕ) (hm : N < (m + 1) * (m + 1)) (hd : m < d) :
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
lemma s27_card_filter_mul_le' (N m b : ℕ) (hb : b ∈ Ioc 0 m) :
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
lemma s27_hyperbola (N : ℕ) :
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
lemma s27_harmonic_sub_bounds {n : ℕ} (hn : 1 ≤ n) :
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
lemma s27_log_sqrt_gap {N : ℕ} (hN : 1 ≤ N) :
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
lemma s27_sum_sigma_zero_bound {N : ℕ} (hN : 1 ≤ N) :
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
lemma s27_log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hx.le] at h
  linarith

/-- `0 ≤ x ln x - N ln N ≤ ln x + 1` for `N = ⌊x⌋`, `x ≥ 1`. -/
lemma s27_xlogx_floor {x : ℝ} (hx : 1 ≤ x) :
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
lemma s27_sum_sigma_zero_asymptotic :
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

/-- Estimate under the stated parameter and domain assumptions: `0 ≤ s27_errLog a`. -/
lemma s27_errLog_nonneg (a : ℕ) : 0 ≤ s27_errLog a := by
  unfold s27_errLog
  rcases Nat.lt_or_ge a 1 with h | h
  · interval_cases a; simp
  · have : (1 : ℝ) ≤ a := by exact_mod_cast h
    have := Real.log_nonneg this
    have : 0 ≤ (a : ℝ) - 1 := by linarith
    positivity

/-- The series with terms `s27_errLog` is summable. -/
lemma s27_summable_errLog : Summable s27_errLog := by
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
lemma s27_log_step {a : ℕ} (ha : 1 ≤ a) :
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
lemma s27_sum_log_div_bound :
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
lemma s27_sum_sigma_zero_div (N : ℕ) :
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
lemma s27_harmonic_floor_div {N a : ℕ} (ha : a ∈ Ioc 0 N) :
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
lemma s27_sum_sigma_zero_div_bound :
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
lemma s27_sum_sigma_zero_div_asymptotic :
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

end R27Helpers
end DLMF.NumberTheory
end
