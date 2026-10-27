/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.Schroder
public import Mathlib.Data.Nat.Choose.Vandermonde
public import DLMFMathlib.Combinatorics.S26aSeriesTransform
public import DLMF.Combinatorics.Catalan

/-!
# Other lattice path numbers (DLMF §26.6)

DLMF defines the Delannoy number `D(m, n)`, the Motzkin number `M(n)`, the Narayana number
`N(n, k)` and the Schröder number `r(n)` as numbers of lattice paths (§26.6(i)). Mathlib has the
large Schröder numbers `Nat.largeSchroder` (`1, 2, 6, 22, 90, …`), which are DLMF's `r(n)`; the
other three are defined here, by the recurrence 26.6.10 (Delannoy), by the recurrence 26.6.11
(Motzkin), and by the explicit formula 26.6.3 (Narayana, with `N(n, 0) = 0`). The path counts
in DLMF's definitions are acquired as theorems about `latticePaths`.

The generating functions §26.6(ii) are stated for real arguments in explicit disks of
convergence (`3 - 2√2` is the radius for the central Delannoy and the Schröder numbers, `1/3`
for the Motzkin numbers), and with "sufficiently small" bounds where DLMF gives none (26.6.5,
26.6.8).
-/

@[expose] public section

open Finset Filter Topology

noncomputable section

namespace DLMF.Combinatorics

/-! ### Definitions (§26.6(i)) -/

/-- DLMF §26.6(i): the Delannoy number `D(m, n)`, defined by `D(0, n) = D(m, 0) = 1` and the
recurrence 26.6.10. -/
@[dlmf 26.6.i]
def delannoy : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | m + 1, n + 1 => delannoy m (n + 1) + delannoy (m + 1) n + delannoy m n

@[simp] theorem delannoy_zero_left (n : ℕ) : delannoy 0 n = 1 := by cases n <;> simp [delannoy]

@[simp] theorem delannoy_zero_right (m : ℕ) : delannoy m 0 = 1 := by cases m <;> simp [delannoy]

/-- DLMF 26.6.10: `D(m, n) = D(m, n-1) + D(m-1, n) + D(m-1, n-1)`, `m, n ≥ 1` (written with
`m + 1`, `n + 1`). -/
@[dlmf 26.6.E10]
theorem delannoy_succ_succ (m n : ℕ) :
    delannoy (m + 1) (n + 1) = delannoy (m + 1) n + delannoy m (n + 1) + delannoy m n := by
  rw [delannoy]; ring

/-- DLMF §26.6(i): the Motzkin number `M(n)`, defined by `M(0) = 1` and the recurrence 26.6.11,
`M(n+1) = M(n) + ∑_{i=0}^{n-1} M(i) M(n-1-i)`. -/
@[dlmf 26.6.i]
def motzkin : ℕ → ℕ
  | 0 => 1
  | n + 1 => motzkin n + ∑ i : Fin n,
      have := i.2
      have : n - 1 - i < n + 1 := by omega
      motzkin i * motzkin (n - 1 - i)

/-- DLMF 26.6.11: `M(n) = M(n-1) + ∑_{k=2}^{n} M(k-2) M(n-k)`, `n ≥ 2`. -/
@[dlmf 26.6.E11]
theorem motzkin_eq {n : ℕ} (hn : 2 ≤ n) :
    motzkin n = motzkin (n - 1) + ∑ k ∈ Icc 2 n, motzkin (k - 2) * motzkin (n - k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [motzkin, Nat.add_sub_cancel]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => motzkin i * motzkin (m - 1 - i)) m]
  rw [show Icc 2 (m + 1) = (range m).map ⟨(· + 2), add_left_injective 2⟩ by
    ext k; simp only [mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨k - 2, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega, sum_map]
  refine sum_congr rfl fun i hi => ?_
  simp only [Function.Embedding.coeFn_mk, Nat.add_sub_cancel]
  congr 2; omega

/-- DLMF §26.6(i): the Narayana number `N(n, k) = C(n, k) C(n, k-1) / n` (26.6.3), with
`N(n, 0) = 0`. The division is exact (`narayana_mul`). -/
@[dlmf 26.6.i]
def narayana : ℕ → ℕ → ℕ
  | _, 0 => 0
  | n, k + 1 => n.choose (k + 1) * n.choose k / n

/-- The divisibility behind `narayana`: `n ∣ C(n, k+1) C(n, k)`. -/
lemma c26a_dvd_choose_mul_choose (n k : ℕ) : n ∣ n.choose (k + 1) * n.choose k := by
  rcases n with _ | a
  · simp
  · -- `(a+2) C(a+1,k+1) C(a+1,k) = (a+1) C(a,k) C(a+2,k+1)`
    have h1 := Nat.add_one_mul_choose_eq a k
    have h2 := Nat.add_one_mul_choose_eq (a + 1) k
    have key : (a + 1).choose (k + 1) * (a + 1).choose k * (a + 1 + 1) =
        (a + 1) * (a.choose k * (a + 1 + 1).choose (k + 1)) := by
      have : (a + 1).choose (k + 1) * (a + 1).choose k * (a + 1 + 1) * (k + 1) =
          (a + 1) * (a.choose k * (a + 1 + 1).choose (k + 1)) * (k + 1) := by
        calc _ = (a + 1).choose (k + 1) * ((a + 1 + 1) * (a + 1).choose k) * (k + 1) := by ring
          _ = (a + 1).choose (k + 1) * ((a + 1 + 1).choose (k + 1) * (k + 1)) * (k + 1) := by
            rw [h2]
          _ = ((a + 1).choose (k + 1) * (k + 1)) * (a + 1 + 1).choose (k + 1) * (k + 1) := by ring
          _ = _ := by rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    have hcop : Nat.Coprime (a + 1) (a + 1 + 1) :=
      Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    exact hcop.dvd_of_dvd_mul_right ⟨_, key⟩

/-- DLMF 26.6.3: `n N(n, k) = C(n, k) C(n, k-1)` for `k ≥ 1`. -/
theorem narayana_mul (n k : ℕ) : n * narayana n (k + 1) = n.choose (k + 1) * n.choose k := by
  rw [narayana, Nat.mul_div_cancel' (c26a_dvd_choose_mul_choose n k)]

/-- DLMF 26.6.3: `N(n, k) = (1/n) C(n, k) C(n, k-1)`, `n, k ≥ 1`. -/
@[dlmf 26.6.E3]
theorem narayana_eq {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (narayana n k : ℚ) = (n.choose k * n.choose (k - 1) : ℚ) / n := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have := narayana_mul n j
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Nat.add_sub_cancel, eq_div_iff hn', mul_comm]
  exact_mod_cast this

/-! ### Lattice path counts (§26.6(i)) -/

/-- DLMF §26.6(i): `D(m, n)` is the number of paths from `(0, 0)` to `(m, n)` with steps
`(1, 0)`, `(0, 1)`, `(1, 1)`. -/
@[dlmf 26.6.i]
theorem card_latticePaths_eq_delannoy (m n : ℕ) :
    #(latticePaths {(1, 0), (0, 1), (1, 1)} m n) = delannoy m n := by
  have h0 : ((0 : ℕ), (0 : ℕ)) ∉ ({(1, 0), (0, 1), (1, 1)} : Finset (ℕ × ℕ)) := by decide
  have key := fun m n (hmn : (m, n) ≠ (0, 0)) =>
    q26a_card_filter_latticePaths h0 (m := m) (n := n) hmn (fun _ => True)
  simp only [filter_true] at key
  induction m generalizing n with
  | zero =>
    induction n with
    | zero => simp [q26a_latticePaths_zero h0]
    | succ n ih =>
      rw [key 0 (n + 1) (by simp), show ({(1, 0), (0, 1), (1, 1)} : Finset (ℕ × ℕ)).filter
          (fun s => s.1 ≤ 0 ∧ s.2 ≤ n + 1) = {(0, 1)} by
        ext ⟨a, b⟩; simp only [mem_filter, mem_insert, mem_singleton, Prod.mk.injEq]; omega]
      simp [ih]
  | succ m ih =>
    induction n with
    | zero =>
      rw [key (m + 1) 0 (by simp), show ({(1, 0), (0, 1), (1, 1)} : Finset (ℕ × ℕ)).filter
          (fun s => s.1 ≤ m + 1 ∧ s.2 ≤ 0) = {(1, 0)} by
        ext ⟨a, b⟩; simp only [mem_filter, mem_insert, mem_singleton, Prod.mk.injEq]; omega]
      simp [ih]
    | succ n ihn =>
      rw [key (m + 1) (n + 1) (by simp), show ({(1, 0), (0, 1), (1, 1)} : Finset (ℕ × ℕ)).filter
          (fun s => s.1 ≤ m + 1 ∧ s.2 ≤ n + 1) = {(1, 0), (0, 1), (1, 1)} by
        ext ⟨a, b⟩; simp only [mem_filter, mem_insert, mem_singleton, Prod.mk.injEq]; omega]
      rw [sum_insert (by decide), sum_pair (by decide)]
      simp only [Nat.add_sub_cancel, Nat.sub_zero, ih, ihn, delannoy_succ_succ]
      ring

/-- DLMF §26.6(i): `M(n)` is the number of lattice paths from `(0, 0)` to `(n, n)` that stay on
or above `y = x`, with steps `(2, 0)`, `(0, 2)`, `(1, 1)`. -/
@[dlmf 26.6.i]
theorem card_latticePaths_above_eq_motzkin (n : ℕ) :
    #{l ∈ latticePaths {(2, 0), (0, 2), (1, 1)} n n | StaysWeaklyAboveDiagonal l} = motzkin n := by
  sorry

/-- The number of occurrences of a step `(0, 1)` immediately followed by a step `(1, 0)`. -/
def c26a_numPeaks (l : List (ℕ × ℕ)) : ℕ := (l.zip l.tail).count ((0, 1), (1, 0))

/-- DLMF §26.6(i): `N(n, k)` is the number of lattice paths from `(0, 0)` to `(n, n)` with
steps `(1, 0)`, `(0, 1)` that stay on or above `y = x` and have exactly `k` occurrences of a
step `(0, 1)` followed by a step `(1, 0)` (`n ≥ 1`; for `n = 0` the empty path has no such
occurrence and `N(0, 0) = 0` by convention). -/
@[dlmf 26.6.i]
theorem card_latticePaths_peaks_eq_narayana {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    #{l ∈ latticePaths unitSteps n n | StaysWeaklyAboveDiagonal l ∧ c26a_numPeaks l = k} =
      narayana n k := by
  sorry

/-- DLMF §26.6(i): the Schröder number `r(n)` (Mathlib `Nat.largeSchroder n`) is the number of
paths from `(0, 0)` to `(n, n)` with steps `(1, 0)`, `(0, 1)`, `(1, 1)` that stay on or above
`y = x`. -/
@[dlmf 26.6.i]
theorem card_latticePaths_above_eq_largeSchroder (n : ℕ) :
    #{l ∈ latticePaths {(1, 0), (0, 1), (1, 1)} n n | StaysWeaklyAboveDiagonal l} =
      Nat.largeSchroder n := by
  sorry

/-! ### Helpers (agent p26a) -/


/-- A function satisfying the Delannoy boundary values and recurrence is `delannoy`. -/
lemma q26a_eq_delannoy (f : ℕ → ℕ → ℕ) (h0 : ∀ n, f 0 n = 1) (h1 : ∀ m, f m 0 = 1)
    (hs : ∀ m n, f (m + 1) (n + 1) = f (m + 1) n + f m (n + 1) + f m n) (m n : ℕ) :
    f m n = delannoy m n := by
  induction m generalizing n with
  | zero => simp [h0]
  | succ m ih =>
    induction n with
    | zero => simp [h1]
    | succ n ihn => rw [hs, delannoy_succ_succ, ihn, ih, ih]

/-- DLMF 26.6.1, first form. -/
lemma q26a_delannoy_eq_sum1 (m n : ℕ) :
    delannoy m n = ∑ k ∈ range (n + 1), n.choose k * (m + n - k).choose n := by
  symm
  apply q26a_eq_delannoy (fun m n => ∑ k ∈ range (n + 1), n.choose k * (m + n - k).choose n)
  · intro n
    rw [sum_eq_single 0]
    · simp
    · intro k hk hk0
      rw [Nat.choose_eq_zero_of_lt (n := 0 + n - k) (by simp at hk; omega)]; simp
    · simp
  · intro m; simp
  · intro m n
    set H : ℕ → ℕ → ℕ := fun m n => ∑ k ∈ range (n + 1), n.choose k * (m + n - k).choose n
      with hH
    have hT : ∀ k ∈ range (n + 1),
        (n + 1).choose (k + 1) * (m + 1 + (n + 1) - (k + 1)).choose (n + 1)
        = (n + 1).choose (k + 1) * (m + (n + 1) - (k + 1)).choose (n + 1) +
          n.choose (k + 1) * (m + 1 + n - (k + 1)).choose n +
          n.choose k * (m + n - k).choose n := by
      intro k hk
      have hk : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      rw [show m + 1 + (n + 1) - (k + 1) = (m + n - k) + 1 by omega,
        show m + (n + 1) - (k + 1) = m + n - k by omega,
        show m + 1 + n - (k + 1) = m + n - k by omega, Nat.choose_succ_succ' (m + n - k) n,
        Nat.choose_succ_succ' n k]
      ring
    have eL : H (m + 1) (n + 1) = ∑ k ∈ range (n + 1),
        (n + 1).choose (k + 1) * (m + 1 + (n + 1) - (k + 1)).choose (n + 1) +
        (m + 1 + (n + 1)).choose (n + 1) := by
      simp only [hH]; rw [sum_range_succ']; simp
    have e2 : H m (n + 1) = ∑ k ∈ range (n + 1),
        (n + 1).choose (k + 1) * (m + (n + 1) - (k + 1)).choose (n + 1) +
        (m + (n + 1)).choose (n + 1) := by
      simp only [hH]; rw [sum_range_succ']; simp
    have e1 : H (m + 1) n = ∑ k ∈ range (n + 1), n.choose (k + 1) * (m + 1 + n - (k + 1)).choose n +
        (m + 1 + n).choose n := by
      simp only [hH]
      have := sum_range_succ' (fun k => n.choose k * (m + 1 + n - k).choose n) (n + 1)
      rw [sum_range_succ, Nat.choose_succ_self, zero_mul, add_zero] at this
      rw [this]; simp
    change H (m + 1) (n + 1) = H (m + 1) n + H m (n + 1) + H m n
    rw [eL, e1, e2, sum_congr rfl hT, sum_add_distrib, sum_add_distrib,
      show m + 1 + (n + 1) = (m + n + 1) + 1 by ring, Nat.choose_succ_succ' (m + n + 1) n,
      show m + n + 1 = m + 1 + n by ring, show m + (n + 1) = m + 1 + n by ring]
    ring

/-- DLMF 26.6.1, second form. -/
lemma q26a_delannoy_eq_sum2 (m n : ℕ) :
    delannoy m n = ∑ k ∈ range (n + 1), 2 ^ k * m.choose k * n.choose k := by
  symm
  apply q26a_eq_delannoy (fun m n => ∑ k ∈ range (n + 1), 2 ^ k * m.choose k * n.choose k)
  · intro n
    rw [sum_eq_single 0]
    · simp
    · intro k _ hk0
      rw [Nat.choose_eq_zero_of_lt (n := 0) (by omega)]; simp
    · simp
  · intro m; simp
  · intro m n
    set F : ℕ → ℕ → ℕ := fun m n => ∑ k ∈ range (n + 1), 2 ^ k * m.choose k * n.choose k
      with hF
    change F (m + 1) (n + 1) = F (m + 1) n + F m (n + 1) + F m n
    have hT : ∀ k ∈ range (n + 1),
        2 ^ (k + 1) * (m + 1).choose (k + 1) * (n + 1).choose (k + 1) +
          2 ^ (k + 1) * m.choose (k + 1) * n.choose (k + 1) =
        2 ^ (k + 1) * (m + 1).choose (k + 1) * n.choose (k + 1) +
          2 ^ (k + 1) * m.choose (k + 1) * (n + 1).choose (k + 1) +
          2 * (2 ^ k * m.choose k * n.choose k) := by
      intro k _
      rw [Nat.choose_succ_succ' m k, Nat.choose_succ_succ' n k]
      ring
    have hs := sum_congr rfl hT
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum] at hs
    have eL : F (m + 1) (n + 1) = ∑ k ∈ range (n + 1),
        2 ^ (k + 1) * (m + 1).choose (k + 1) * (n + 1).choose (k + 1) + 1 := by
      simp only [hF]; rw [sum_range_succ']; simp
    have e2 : F m (n + 1) = ∑ k ∈ range (n + 1),
        2 ^ (k + 1) * m.choose (k + 1) * (n + 1).choose (k + 1) + 1 := by
      simp only [hF]; rw [sum_range_succ']; simp
    have e1 : F (m + 1) n = ∑ k ∈ range (n + 1),
        2 ^ (k + 1) * (m + 1).choose (k + 1) * n.choose (k + 1) + 1 := by
      simp only [hF]
      have := sum_range_succ' (fun k => 2 ^ k * (m + 1).choose k * n.choose k) (n + 1)
      rw [sum_range_succ, Nat.choose_succ_self, mul_zero, add_zero] at this
      rw [this]; simp
    have e3 : F m n =
        ∑ k ∈ range (n + 1), 2 ^ (k + 1) * m.choose (k + 1) * n.choose (k + 1) + 1 := by
      simp only [hF]
      have := sum_range_succ' (fun k => 2 ^ k * m.choose k * n.choose k) (n + 1)
      rw [sum_range_succ, Nat.choose_succ_self, mul_zero, add_zero] at this
      rw [this]; simp
    have e4 : F m n = ∑ k ∈ range (n + 1), 2 ^ k * m.choose k * n.choose k := rfl
    omega

/-- DLMF 26.6.12 as printed fails for `n = 0` (`C(0) = 1`, empty sum). -/
lemma q26a_not_catalan_eq_sum_narayana :
    ¬ ∀ n : ℕ, catalan n = ∑ k ∈ Icc 1 n, narayana n k := by
  intro h; simpa using h 0

/-- DLMF 26.6.12 for `n ≥ 1`: `C(n) = ∑_{k=1}^{n} N(n, k)`. -/
lemma q26a_catalan_eq_sum_narayana {n : ℕ} (hn : 1 ≤ n) :
    catalan n = ∑ k ∈ Icc 1 n, narayana n k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hv : ∑ j ∈ range (m + 1), (m + 1).choose (j + 1) * (m + 1).choose j =
      (m + 1 + (m + 1)).choose m := by
    rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine sum_congr rfl fun j hj => ?_
    have hj : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [mul_comm, ← Nat.choose_symm (show m - j ≤ m + 1 by omega),
      show m + 1 - (m - j) = j + 1 by omega]
  have hc := succ_mul_catalan_eq_centralBinom (m + 1)
  have hr := Nat.choose_succ_right_eq (m + 1 + (m + 1)) m
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul] at hc
  rw [show m + 1 + (m + 1) - m = m + 2 by omega] at hr
  have hsum : ∑ k ∈ Icc 1 (m + 1), narayana (m + 1) k =
      ∑ j ∈ range (m + 1), narayana (m + 1) (j + 1) := by
    rw [range_eq_Ico, Finset.sum_Ico_add']
    rfl
  apply Nat.eq_of_mul_eq_mul_left (show 0 < m + 1 by omega)
  rw [hsum, mul_sum]
  simp_rw [narayana_mul]
  rw [hv]
  apply Nat.eq_of_mul_eq_mul_left (show 0 < m + 2 by omega)
  rw [show m + 1 + 1 = m + 2 by ring] at hc
  calc (m + 2) * ((m + 1) * catalan (m + 1)) = (m + 1) * ((m + 2) * catalan (m + 1)) := by ring
    _ = _ := by rw [hc]; linarith

/-! ### Motzkin numbers via the Catalan series (agent p26a) -/

/-- The Motzkin series satisfies `M = 1 + XM + X²M²`. -/
lemma s26a_motzkinSeries_eq :
    (PowerSeries.mk fun n => (motzkin n : ℚ)) =
      1 + PowerSeries.C 1 * PowerSeries.X * (PowerSeries.mk fun n => (motzkin n : ℚ)) +
        PowerSeries.X ^ 2 * (PowerSeries.mk fun n => (motzkin n : ℚ)) ^ 2 := by
  ext n
  rcases n with _ | n
  · simp [motzkin]
  rw [show (PowerSeries.C 1 : PowerSeries ℚ) = 1 from map_one _, one_mul, map_add, map_add,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, ite_eq_right (by omega), zero_add]
  rcases n with _ | n
  · simp [motzkin, PowerSeries.coeff_X_pow_mul']
  rw [show n + 1 + 1 = n + 2 by ring, PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega),
    Nat.add_sub_cancel, pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk]
  rw [show n + 2 = (n + 1) + 1 by ring, motzkin, Nat.cast_add, Nat.cast_sum,
    Fin.sum_univ_eq_sum_range (fun i => ((motzkin i * motzkin (n + 1 - 1 - i) : ℕ) : ℚ)) (n + 1)]
  simp only [PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (motzkin i : ℚ) * motzkin j)]
  simp

/-- `M(n) = ∑_k C(n, 2k) C(k)`. -/
lemma s26a_motzkin_eq_sum (n : ℕ) :
    (motzkin n : ℚ) = ∑ k ∈ range (n + 1), (catalan k : ℚ) * n.choose (2 * k) := by
  have := s26a_quad_unique 1 (by norm_num) s26a_motzkinSeries_eq
    (s26a_quadSeries_eq 1 (by norm_num))
  have h := congrArg (PowerSeries.coeff n) this
  rw [s26a_coeff_quadSeries_two, PowerSeries.coeff_mk] at h
  simpa using h

/-- `C(n+1) = ∑_k C(n, k) M(k)`. -/
lemma s26a_catalan_succ_eq_sum_motzkin (n : ℕ) :
    (catalan (n + 1) : ℚ) = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * motzkin k := by
  simp_rw [s26a_motzkin_eq_sum, mul_sum]
  have : ∀ k ∈ range (n + 1), ∑ j ∈ range (k + 1),
      (n.choose k : ℚ) * ((catalan j : ℚ) * k.choose (2 * j)) =
      ∑ j ∈ range (n + 1), (n.choose k : ℚ) * ((catalan j : ℚ) * k.choose (2 * j)) := by
    intro k hk
    refine sum_subset (range_subset_range.mpr (by simp at hk; omega)) fun j _ hj => ?_
    rw [Nat.choose_eq_zero_of_lt (n := k) (by simp at hj; omega)]; simp
  rw [sum_congr rfl this, sum_comm, s26a_catalan_succ_eq_sum]
  refine sum_congr rfl fun j _ => ?_
  have h := s26a_sum_choose_mul_choose n (2 * j)
  have h' : (∑ k ∈ range (n + 1), (n.choose k : ℚ) * k.choose (2 * j)) =
      n.choose (2 * j) * 2 ^ (n - 2 * j) := by exact_mod_cast h
  rw [mul_assoc, ← h', mul_sum]
  exact sum_congr rfl fun k _ => by ring

/-- `∑_{j < 2N} f j = ∑_{k < N} (f (2k) + f (2k+1))`. -/
lemma s26a_sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ j ∈ range (2 * N), f j = ∑ k ∈ range N, (f (2 * k) + f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- `M(m) = ∑_j C(m, j) a_j` with `a_j = C(j/2)` for even `j`, `0` for odd `j`. -/
lemma s26a_motzkin_eq_sum_even (m : ℕ) :
    (motzkin m : ℤ) = ∑ j ∈ range (m + 1),
      (m.choose j : ℤ) * (if Even j then (catalan (j / 2) : ℤ) else 0) := by
  have h := s26a_motzkin_eq_sum m
  have h' : (motzkin m : ℤ) = ∑ k ∈ range (m + 1), (catalan k : ℤ) * m.choose (2 * k) := by
    exact_mod_cast h
  rw [h', sum_subset (range_subset_range.mpr (by omega : m + 1 ≤ 2 * (m + 1)))
    (f := fun j => (m.choose j : ℤ) * (if Even j then (catalan (j / 2) : ℤ) else 0)),
    s26a_sum_range_two_mul]
  · refine sum_congr rfl fun k _ => ?_
    have h1 : ¬ Even (2 * k + 1) := by simp
    rw [ite_eq_left (even_two_mul k), ite_eq_right h1, Nat.mul_div_cancel_left k two_pos]; ring
  · intro j _ hj
    rw [Nat.choose_eq_zero_of_lt (by simp at hj; omega)]; simp


/-- DLMF 26.6.13 (helper): `M(n) = ∑_k (-1)^k C(n, k) C(n+1-k)`, by binomial inversion. -/
lemma s26a_motzkin_eq_sum_catalan (n : ℕ) :
    (motzkin n : ℤ) = ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℤ) * catalan (n + 1 - k) := by
  have hb : ∀ m, (catalan (m + 1) : ℤ) =
      ∑ k ∈ range (m + 1), (m.choose k : ℤ) * motzkin k := fun m => by
    exact_mod_cast s26a_catalan_succ_eq_sum_motzkin m
  rw [s26a_binomial_inversion (fun k => (motzkin k : ℤ)) (fun k => (catalan (k + 1) : ℤ)) hb n,
    ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_range] at hk
  rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega,
    Nat.choose_symm (by omega), show n - k + 1 = n + 1 - k by omega]

/-- `D(n, n) = ∑_k C(2k, k) C(n+k, 2k)`. -/
lemma s26a_delannoy_diag_eq_sum (n : ℕ) :
    (delannoy n n : ℚ) = ∑ k ∈ range (n + 1), ((2 * k).choose k : ℚ) * (n + k).choose (2 * k) := by
  rw [q26a_delannoy_eq_sum1, Nat.cast_sum, ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_range] at hk
  have := Nat.choose_mul (n := n + k) (k := 2 * k) (s := k) (by omega)
  rw [show n + k - k = n by omega, show 2 * k - k = k by omega] at this
  rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm (by omega),
    show n + n - (n - k) = n + k by omega,
    Nat.choose_symm_of_eq_add (show n + k = n + k by ring), mul_comm, ← this]
  push_cast; ring

/-- `√(P/(1-x)²) = √P/(1-x)` for `1 - x > 0`. -/
lemma s26a_sqrt_div_sq {x : ℝ} (P : ℝ) (h : 0 < 1 - x) :
    Real.sqrt (P / (1 - x) ^ 2) = Real.sqrt P / (1 - x) := by
  rw [Real.sqrt_div' P (sq_nonneg _), Real.sqrt_sq h.le]

/-- For `|x| < 3 - 2√2`: `4|x| < (1 - |x|)²`. -/
lemma s26a_schroder_bound {x : ℝ} (hx : |x| < 3 - 2 * Real.sqrt 2) :
    4 * |x| < (1 - |x|) ^ 2 ∧ |x| < 1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have ha := abs_nonneg x
  constructor
  · nlinarith [mul_pos (by linarith : (0 : ℝ) < 3 - 2 * Real.sqrt 2 - |x|)
      (by linarith : (0 : ℝ) < 3 + 2 * Real.sqrt 2 - |x|)]
  · linarith

/-- `D(m, n) = D(n, m)`. -/
lemma s26a_delannoy_comm (m n : ℕ) : delannoy m n = delannoy n m := by
  rw [q26a_delannoy_eq_sum2, q26a_delannoy_eq_sum2,
    sum_subset (range_subset_range.mpr (by omega : n + 1 ≤ m + n + 1)),
    sum_subset (range_subset_range.mpr (by omega : m + 1 ≤ m + n + 1))]
  · exact sum_congr rfl fun k _ => by ring
  · intro k _ hk
    rw [Nat.choose_eq_zero_of_lt (n := m) (by simp at hk; omega)]; simp
  · intro k _ hk
    rw [Nat.choose_eq_zero_of_lt (n := n) (by simp at hk; omega)]; simp

/-- Shifting a series by `k` places. -/
lemma s26a_hasSum_shift {f : ℕ → ℝ} {a : ℝ} (hf : HasSum f a) (k : ℕ) :
    HasSum (fun n => if k ≤ n then f (n - k) else 0) a := by
  rw [← hasSum_nat_add_iff' k]
  simp only [Nat.le_add_left, ite_true, Nat.add_sub_cancel]
  rw [sum_eq_zero fun i hi => by simp at hi; simp [show ¬ k ≤ i by omega], sub_zero]
  exact hf

/-- The row generating function `∑_n D(m, n) tⁿ = (1+t)^m/(1-t)^{m+1}`. -/
lemma s26a_hasSum_delannoy_row (m : ℕ) {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n => (delannoy m n : ℝ) * t ^ n) ((1 + t) ^ m / (1 - t) ^ (m + 1)) := by
  have hk : ∀ k ∈ range (m + 1), HasSum (fun n => if k ≤ n then
      (m.choose k : ℝ) * t ^ k * (((n - k + m).choose m : ℝ) * t ^ (n - k)) else 0)
      ((m.choose k : ℝ) * t ^ k * (1 / (1 - t) ^ (m + 1))) := fun k _ =>
    s26a_hasSum_shift ((hasSum_choose_mul_geometric_of_norm_lt_one m (r := t)
      (by rwa [Real.norm_eq_abs])).mul_left _) k
  have h := hasSum_sum hk
  rw [← sum_mul] at h
  have hp : (1 + t) ^ m = ∑ k ∈ range (m + 1), (m.choose k : ℝ) * t ^ k := by
    rw [add_comm, add_pow]; exact sum_congr rfl fun k _ => by rw [one_pow, mul_one, mul_comm]
  convert h using 1
  · ext n
    rw [s26a_delannoy_comm, q26a_delannoy_eq_sum1, Nat.cast_sum, sum_mul]
    refine sum_congr rfl fun k hk => ?_
    simp only [mem_range] at hk
    split_ifs with h
    · rw [show n - k + m = n + m - k by omega,
        show t ^ n = t ^ k * t ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' h]]
      push_cast; ring
    · rw [Nat.choose_eq_zero_of_lt (n := n + m - k) (by omega)]; simp
  · rw [div_eq_mul_one_div, hp]

/-! ### Explicit formulas (§26.6(i)) -/

/-- DLMF 26.6.1: `D(m, n) = ∑_{k=0}^{n} C(n, k) C(m+n-k, n) = ∑_{k=0}^{n} 2^k C(m, k) C(n, k)`. -/
@[dlmf 26.6.E1]
theorem delannoy_eq_sum (m n : ℕ) :
    delannoy m n = ∑ k ∈ range (n + 1), n.choose k * (m + n - k).choose n ∧
      delannoy m n = ∑ k ∈ range (n + 1), 2 ^ k * m.choose k * n.choose k :=
  ⟨q26a_delannoy_eq_sum1 m n, q26a_delannoy_eq_sum2 m n⟩

/-- DLMF 26.6.2: `M(n) = ∑_{k=0}^{n} (-1)^k/(n+2-k) · C(n, k) C(2n+2-2k, n+1-k)`. -/
@[dlmf 26.6.E2]
theorem motzkin_eq_sum (n : ℕ) :
    (motzkin n : ℚ) = ∑ k ∈ range (n + 1), (-1) ^ k / ((n + 2 - k : ℕ) : ℚ) *
      n.choose k * (2 * n + 2 - 2 * k).choose (n + 1 - k) := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (s26a_motzkin_eq_sum_catalan n)
  push_cast at h
  rw [h]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_range] at hk
  have hc := succ_mul_catalan_eq_centralBinom (n + 1 - k)
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (n + 1 - k) = 2 * n + 2 - 2 * k by omega]
    at hc
  have hpos : ((n + 2 - k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : n + 2 - k ≠ 0)
  rw [← hc, show n + 1 - k + 1 = n + 2 - k by omega]
  push_cast
  field_simp

/-- DLMF 26.6.4: `r(n) = D(n, n) - D(n+1, n-1)`, `n ≥ 1`. -/
@[dlmf 26.6.E4]
theorem largeSchroder_eq_delannoy_sub {n : ℕ} (hn : 1 ≤ n) :
    (Nat.largeSchroder n : ℤ) = delannoy n n - delannoy (n + 1) (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hcat : ∀ k : ℕ, (catalan k : ℚ) = (2 * k).choose k - (2 * k).choose (k + 1) := by
    intro k
    have h1 := succ_mul_catalan_eq_centralBinom k
    have h2 := Nat.choose_succ_right_eq (2 * k) k
    rw [Nat.centralBinom_eq_two_mul_choose] at h1
    rw [show 2 * k - k = k by omega] at h2
    have h1' : ((k + 1 : ℕ) : ℚ) * catalan k = (2 * k).choose k := by exact_mod_cast h1
    have h2' : ((2 * k).choose (k + 1) : ℚ) * (k + 1) = (2 * k).choose k * k := by
      exact_mod_cast h2
    have hk : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hk
    push_cast at h1' hk ⊢
    linear_combination h1' + h2'
  have hD1 : (delannoy (m + 1) (m + 1) : ℚ) =
      ∑ k ∈ range (m + 2), ((2 * k).choose k : ℚ) * (m + 1 + k).choose (2 * k) :=
    s26a_delannoy_diag_eq_sum (m + 1)
  have hD2 : (delannoy (m + 1 + 1) m : ℚ) =
      ∑ k ∈ range (m + 2), ((2 * k).choose (k + 1) : ℚ) * (m + 1 + k).choose (2 * k) := by
    rw [q26a_delannoy_eq_sum1, Nat.cast_sum, sum_range_succ' _ (m + 1), ← sum_range_reflect]
    simp only [mul_zero, Nat.choose_zero_succ, Nat.cast_zero, zero_mul, add_zero]
    refine sum_congr rfl fun i hi => ?_
    simp only [mem_range] at hi
    have := Nat.choose_mul (n := m + 2 + i) (k := 2 * i + 2) (s := i + 2) (by omega)
    rw [show m + 2 + i - (i + 2) = m by omega, show 2 * i + 2 - (i + 2) = i by omega] at this
    rw [show m + 1 - 1 - i = m - i by omega, Nat.choose_symm (by omega),
      show m + 1 + 1 + m - (m - i) = m + 2 + i by omega,
      Nat.choose_symm_of_eq_add (show m + 2 + i = m + (i + 2) by ring),
      show 2 * (i + 1) = 2 * i + 2 by ring, show i + 1 + 1 = i + 2 by ring,
      show m + 1 + (i + 1) = m + 2 + i by ring]
    have this' : ((m + 2 + i).choose (2 * i + 2) : ℚ) * (2 * i + 2).choose (i + 2) =
        (m + 2 + i).choose (i + 2) * m.choose i := by exact_mod_cast this
    push_cast; rw [mul_comm, ← this']; ring
  have h : (Nat.largeSchroder (m + 1) : ℚ) =
      delannoy (m + 1) (m + 1) - delannoy (m + 1 + 1) m := by
    rw [s26a_largeSchroder_eq_sum, hD1, hD2, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [hcat]; ring
  exact_mod_cast h

/-! ### Generating functions (§26.6(ii)) -/

/-- DLMF 26.6.5: `∑_{m,n=0}^∞ D(m, n) x^m y^n = 1/(1 - x - y - xy)`, for real `x, y` with
`|x| + |y| + |xy| < 1` (a sufficient smallness condition). -/
@[dlmf 26.6.E5]
theorem hasSum_delannoy {x y : ℝ} (h : |x| + |y| + |x * y| < 1) :
    HasSum (fun p : ℕ × ℕ => (delannoy p.1 p.2 : ℝ) * x ^ p.1 * y ^ p.2)
      (1 / (1 - x - y - x * y)) := by
  have hy1 : |y| < 1 := by nlinarith [abs_nonneg x, abs_nonneg (x * y)]
  have h1y : 0 < 1 - |y| := by linarith
  have h1y' : 0 < 1 - y := by have := le_abs_self y; linarith
  have hr : |x| * (1 + |y|) / (1 - |y|) < 1 := by
    rw [div_lt_one h1y, abs_mul] at *; nlinarith
  have hr' : |x * (1 + y) / (1 - y)| < 1 := by
    rw [abs_div, abs_mul, abs_of_pos h1y', div_lt_one h1y']
    have : |1 + y| ≤ 1 + |y| := by
      have := abs_add_le 1 y; rwa [abs_one] at this
    have hxy : |x| * |1 + y| ≤ |x| * (1 + |y|) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    have := le_abs_self y
    rw [div_lt_one h1y] at hr; linarith
  have hrowa : ∀ m, HasSum (fun n => |(delannoy m n : ℝ) * x ^ m * y ^ n|)
      (|x| ^ m * ((1 + |y|) ^ m / (1 - |y|) ^ (m + 1))) := by
    intro m
    have := (s26a_hasSum_delannoy_row m (t := |y|) (by rwa [abs_abs])).mul_left (|x| ^ m)
    convert this using 1
    ext n; rw [abs_mul, abs_mul, abs_pow, abs_pow, Nat.abs_cast]; ring
  have hrow : ∀ m, HasSum (fun n => (delannoy m n : ℝ) * x ^ m * y ^ n)
      (x ^ m * ((1 + y) ^ m / (1 - y) ^ (m + 1))) := by
    intro m
    have := (s26a_hasSum_delannoy_row m hy1).mul_left (x ^ m)
    convert this using 1
    ext n; ring
  have hgeoa : HasSum (fun m => |x| ^ m * ((1 + |y|) ^ m / (1 - |y|) ^ (m + 1)))
      (1 / (1 - |y|) * (1 - |x| * (1 + |y|) / (1 - |y|))⁻¹) := by
    have := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left (1 / (1 - |y|))
    convert this using 1
    ext m; rw [div_pow, pow_succ, mul_pow]; field_simp
  have hgeo : HasSum (fun m => x ^ m * ((1 + y) ^ m / (1 - y) ^ (m + 1)))
      (1 / (1 - y) * (1 - x * (1 + y) / (1 - y))⁻¹) := by
    have := (hasSum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])).mul_left
      (1 / (1 - y))
    convert this using 1
    ext m; rw [div_pow, pow_succ, mul_pow]; field_simp
  have hsum : Summable (fun p : ℕ × ℕ => (delannoy p.1 p.2 : ℝ) * x ^ p.1 * y ^ p.2) := by
    refine Summable.of_norm ?_
    simp only [Real.norm_eq_abs]
    refine (summable_prod_of_nonneg fun _ => abs_nonneg _).mpr
      ⟨fun m => (hrowa m).summable, ?_⟩
    simp_rw [fun m => (hrowa m).tsum_eq]
    exact hgeoa.summable
  have hD : 1 - x - y - x * y ≠ 0 := by
    intro h0
    have : x * (1 + y) / (1 - y) = 1 := by rw [div_eq_one_iff_eq h1y'.ne']; linarith
    rw [this, abs_one] at hr'; exact lt_irrefl _ hr'
  have hval : 1 / (1 - y) * (1 - x * (1 + y) / (1 - y))⁻¹ = 1 / (1 - x - y - x * y) := by
    rw [one_sub_div h1y'.ne']
    field_simp
    ring
  have h1 := hsum.hasSum.prod_fiberwise hrow
  rw [← hval, ← h1.unique hgeo]
  exact hsum.hasSum

/-- DLMF 26.6.6: `∑_{n=0}^∞ D(n, n) xⁿ = 1/√(1 - 6x + x²)`, real `|x| < 3 - 2√2`. -/
@[dlmf 26.6.E6]
theorem hasSum_delannoy_diag {x : ℝ} (hx : |x| < 3 - 2 * Real.sqrt 2) :
    HasSum (fun n : ℕ => (delannoy n n : ℝ) * x ^ n) (1 / Real.sqrt (1 - 6 * x + x ^ 2)) := by
  obtain ⟨hb4, hx1⟩ := s26a_schroder_bound hx
  have h1x : 0 < 1 - x := by have := le_abs_self x; linarith
  have h1a : 0 < 1 - |x| := by linarith
  have hle : 1 - |x| ≤ |1 - x| := by
    have := abs_sub_abs_le_abs_sub 1 x; rw [abs_one] at this; linarith
  have hy' : |(|x| ^ 1 / (1 - |1 * x|) ^ 2)| < 1 / 4 := by
    rw [one_mul, pow_one, abs_of_nonneg (by positivity), div_lt_iff₀ (by positivity)]
    linarith
  have hy : |x ^ 1 / (1 - 1 * x) ^ 2| < 1 / 4 := by
    rw [one_mul, pow_one, abs_div, abs_pow, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg (1 - x)]
  have hT := s26a_hasSum_transform (fun k => ((2 * k).choose k : ℝ)) le_rfl
    (b := 1) (x := x) (by rwa [one_mul]) (by
      simpa [Nat.abs_cast] using
        (s26a_hasSum_centralBinom hy').summable)
    (s26a_hasSum_centralBinom hy)
  convert hT using 1
  · ext n
    congr 1
    have := congrArg (fun q : ℚ => (q : ℝ)) (s26a_delannoy_diag_eq_sum n)
    push_cast at this
    rw [this]
    refine sum_congr rfl fun k hk => ?_
    simp only [mem_range] at hk
    rw [ite_eq_left (by omega), one_pow, mul_one, show n - 1 * k + 2 * k = n + k by omega]
  · rw [one_mul, pow_one, show 1 - 4 * (x / (1 - x) ^ 2) = (1 - 6 * x + x ^ 2) / (1 - x) ^ 2 by
      field_simp; ring, s26a_sqrt_div_sq _ h1x]
    have hP : 0 < 1 - 6 * x + x ^ 2 := by
      have := le_abs_self x; have := neg_abs_le x
      nlinarith [sq_abs x]
    have := Real.sqrt_pos.mpr hP
    field_simp

/-- DLMF 26.6.7: `∑_{n=0}^∞ M(n) xⁿ = (1 - x - √(1 - 2x - 3x²))/(2x²)`, real `0 < |x| < 1/3`
(the value at `x = 0` is the removable value `1`). -/
@[dlmf 26.6.E7]
theorem hasSum_motzkin {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 1 / 3) :
    HasSum (fun n : ℕ => (motzkin n : ℝ) * x ^ n)
      ((1 - x - Real.sqrt (1 - 2 * x - 3 * x ^ 2)) / (2 * x ^ 2)) := by
  have hxa := abs_nonneg x
  have h1x : 0 < 1 - x := by have := le_abs_self x; linarith
  have h1a : 0 < 1 - |x| := by linarith
  have hle : 1 - |x| ≤ |1 - x| := by
    have := abs_sub_abs_le_abs_sub 1 x; rw [abs_one] at this; linarith
  have hx0' : 0 < |x| := abs_pos.mpr hx0
  have hy' : |(|x| ^ 2 / (1 - |1 * x|) ^ 2)| < 1 / 4 := by
    rw [one_mul, abs_of_nonneg (by positivity), div_lt_iff₀ (by positivity)]
    nlinarith
  have hy : |x ^ 2 / (1 - 1 * x) ^ 2| < 1 / 4 := by
    rw [one_mul, abs_div, abs_pow, abs_pow, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg (1 - x), mul_le_mul hle hle h1a.le (abs_nonneg _)]
  have hy0 : x ^ 2 / (1 - 1 * x) ^ 2 ≠ 0 := by
    rw [one_mul]; exact div_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ h1x.ne')
  have hy0' : |x| ^ 2 / (1 - |1 * x|) ^ 2 ≠ 0 := by
    rw [one_mul]; exact div_ne_zero (pow_ne_zero _ hx0'.ne') (pow_ne_zero _ h1a.ne')
  have hT := s26a_hasSum_transform (fun k => (catalan k : ℝ)) (by norm_num : 1 ≤ 2)
    (b := 1) (x := x) (by rw [one_mul]; linarith) (by
      simpa [Nat.abs_cast] using
        (hasSum_catalan_mul_pow hy0' hy').summable)
    (hasSum_catalan_mul_pow hy0 hy)
  convert hT using 1
  · ext n
    congr 1
    have := congrArg (fun q : ℚ => (q : ℝ)) (s26a_motzkin_eq_sum n)
    push_cast at this
    rw [this]
    refine sum_congr rfl fun k _ => ?_
    split_ifs with h
    · rw [one_pow, mul_one, show n - 2 * k + 2 * k = n by omega]
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · rw [one_mul, show 1 - 4 * (x ^ 2 / (1 - x) ^ 2) = (1 - 2 * x - 3 * x ^ 2) / (1 - x) ^ 2 by
      field_simp; ring, s26a_sqrt_div_sq _ h1x]
    field_simp

/-- DLMF 26.6.8: `∑_{n,k=1}^∞ N(n, k) xⁿ y^k = (1 - x - xy - √((1-x-xy)² - 4x²y))/(2x)`, for
sufficiently small real `x ≠ 0` and `y`. -/
@[dlmf 26.6.E8]
theorem hasSum_narayana : ∃ δ > (0 : ℝ), ∀ x y : ℝ, x ≠ 0 → |x| < δ → |y| < δ →
    HasSum (fun p : ℕ × ℕ => (narayana (p.1 + 1) (p.2 + 1) : ℝ) * x ^ (p.1 + 1) * y ^ (p.2 + 1))
      ((1 - x - x * y - Real.sqrt ((1 - x - x * y) ^ 2 - 4 * x ^ 2 * y)) / (2 * x)) := by
  sorry

/-- DLMF 26.6.9: `∑_{n=0}^∞ r(n) xⁿ = (1 - x - √(1 - 6x + x²))/(2x)`, real
`0 < |x| < 3 - 2√2`. -/
@[dlmf 26.6.E9]
theorem hasSum_largeSchroder {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 3 - 2 * Real.sqrt 2) :
    HasSum (fun n : ℕ => (Nat.largeSchroder n : ℝ) * x ^ n)
      ((1 - x - Real.sqrt (1 - 6 * x + x ^ 2)) / (2 * x)) := by
  obtain ⟨hb4, hx1⟩ := s26a_schroder_bound hx
  have h1x : 0 < 1 - x := by have := le_abs_self x; linarith
  have h1a : 0 < 1 - |x| := by linarith
  have hle : 1 - |x| ≤ |1 - x| := by
    have := abs_sub_abs_le_abs_sub 1 x; rw [abs_one] at this; linarith
  have hx0' : 0 < |x| := abs_pos.mpr hx0
  have hy' : |(|x| ^ 1 / (1 - |1 * x|) ^ 2)| < 1 / 4 := by
    rw [one_mul, pow_one, abs_of_nonneg (by positivity), div_lt_iff₀ (by positivity)]
    linarith
  have hy : |x ^ 1 / (1 - 1 * x) ^ 2| < 1 / 4 := by
    rw [one_mul, pow_one, abs_div, abs_pow, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg (1 - x)]
  have hy0 : x ^ 1 / (1 - 1 * x) ^ 2 ≠ 0 := by
    rw [one_mul]; exact div_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ h1x.ne')
  have hy0' : |x| ^ 1 / (1 - |1 * x|) ^ 2 ≠ 0 := by
    rw [one_mul]; exact div_ne_zero (pow_ne_zero _ hx0'.ne') (pow_ne_zero _ h1a.ne')
  have hT := s26a_hasSum_transform (fun k => (catalan k : ℝ)) le_rfl
    (b := 1) (x := x) (by rwa [one_mul]) (by
      simpa [Nat.abs_cast] using
        (hasSum_catalan_mul_pow hy0' hy').summable)
    (hasSum_catalan_mul_pow hy0 hy)
  convert hT using 1
  · ext n
    congr 1
    have := congrArg (fun q : ℚ => (q : ℝ)) (s26a_largeSchroder_eq_sum n)
    push_cast at this
    rw [this]
    refine sum_congr rfl fun k hk => ?_
    simp only [mem_range] at hk
    rw [ite_eq_left (by omega), one_pow, mul_one, show n - 1 * k + 2 * k = n + k by omega]
  · rw [one_mul, pow_one, show 1 - 4 * (x / (1 - x) ^ 2) = (1 - 6 * x + x ^ 2) / (1 - x) ^ 2 by
      field_simp; ring, s26a_sqrt_div_sq _ h1x]
    field_simp

/-! ### Identities (§26.6(iv)) -/

/-- DLMF 26.6.12: `C(n) = ∑_{k=1}^{n} N(n, k)`, for `n ≥ 1`. Correction: DLMF prints no
condition, but at `n = 0` the sum is empty while `C(0) = 1`
(`q26a_not_catalan_eq_sum_narayana`). -/
@[dlmf 26.6.E12]
theorem catalan_eq_sum_narayana {n : ℕ} (hn : 1 ≤ n) :
    catalan n = ∑ k ∈ Icc 1 n, narayana n k :=
  q26a_catalan_eq_sum_narayana hn


/-- DLMF 26.6.13: `M(n) = ∑_{k=0}^{n} (-1)^k C(n, k) C(n+1-k)`. -/
@[dlmf 26.6.E13]
theorem motzkin_eq_sum_catalan (n : ℕ) :
    (motzkin n : ℤ) = ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℤ) * catalan (n + 1 - k) :=
  s26a_motzkin_eq_sum_catalan n

/-- DLMF 26.6.14: `C(n) = ∑_{k=0}^{2n} (-1)^k C(2n, k) M(2n-k)`. -/
@[dlmf 26.6.E14]
theorem catalan_eq_sum_motzkin (n : ℕ) :
    (catalan n : ℤ) =
      ∑ k ∈ range (2 * n + 1), (-1) ^ k * ((2 * n).choose k : ℤ) * motzkin (2 * n - k) := by
  have h := s26a_binomial_inversion (fun j => if Even j then (catalan (j / 2) : ℤ) else 0)
    (fun k => (motzkin k : ℤ)) s26a_motzkin_eq_sum_even (2 * n)
  simp only [even_two_mul, ite_true, Nat.mul_div_cancel_left n two_pos] at h
  rw [h, ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_range] at hk
  rw [show 2 * n + 1 - 1 - k = 2 * n - k by omega, show 2 * n - (2 * n - k) = k by omega,
    Nat.choose_symm (by omega)]

end DLMF.Combinatorics
