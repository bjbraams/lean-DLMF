/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Tannery's theorem from a uniform ratio bound

A geometric bound on successive term norms, uniform in the parameter and beyond a fixed
index, supplies the summable majorant needed for Tannery's theorem. Pointwise convergence
provides uniform bounds on the finitely many earlier terms.
-/

@[expose] public noncomputable section

open Filter Finset
open scoped Topology

/-- Infinite sums commute with a parameter limit when their terms converge and their successive
norms satisfy a uniform eventual geometric bound. -/
lemma tendsto_tsum_of_ratio_norm_eventually_le {α G : Type*} {L : Filter α}
    [NormedAddCommGroup G] [CompleteSpace G] {f : α → ℕ → G} {g : ℕ → G} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hterm : ∀ n, Tendsto (fun x => f x n) L (𝓝 (g n)))
    (hratio : ∀ᶠ p : α × ℕ in L ×ˢ atTop, ‖f p.1 (p.2 + 1)‖ ≤ r * ‖f p.1 p.2‖) :
    Tendsto (fun x => ∑' n, f x n) L (𝓝 (∑' n, g n)) := by
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp hratio
  obtain ⟨N, hN⟩ := eventually_atTop.mp hQ
  let C := ∑ n ∈ range (N + 1), (‖g n‖ + 1)
  have hC0 : 0 ≤ C := sum_nonneg fun _ _ => by positivity
  have hprefix : ∀ᶠ x in L, ∀ n ∈ range (N + 1), ‖f x n‖ ≤ ‖g n‖ + 1 := by
    apply (eventually_all_finset _).mpr
    intro n hn
    exact ((hterm n).norm.eventually_lt_const (by linarith : ‖g n‖ < ‖g n‖ + 1)).mono
      fun _ h => h.le
  let bound (n : ℕ) : ℝ := C * r ^ (n - N)
  have hsum : Summable bound := by
    rw [← summable_nat_add_iff N]
    simpa [bound] using (summable_geometric_of_lt_one hr0 hr1).mul_left C
  refine tendsto_tsum_of_dominated_convergence hsum hterm ?_
  filter_upwards [hP, hprefix] with x hx hprefix
  have hsmall (n : ℕ) (hn : n ≤ N) : ‖f x n‖ ≤ C := by
    exact (hprefix n (mem_range.mpr (by omega))).trans
      (single_le_sum (f := fun k : ℕ => ‖g k‖ + 1)
        (s := range (N + 1)) (fun _ _ => by positivity) (mem_range.mpr (by omega)))
  have htail (k : ℕ) : ‖f x (N + k)‖ ≤ C * r ^ k := by
    induction k with
    | zero => simpa using hsmall N le_rfl
    | succ k ih =>
      calc
        ‖f x (N + (k + 1))‖ ≤ r * ‖f x (N + k)‖ := by
          simpa only [Nat.add_assoc] using hPQ hx (hN (N + k) (by omega))
        _ ≤ r * (C * r ^ k) := mul_le_mul_of_nonneg_left ih hr0
        _ = C * r ^ (k + 1) := by rw [pow_succ]; ring
  intro n
  by_cases hn : n < N
  · simpa [bound, Nat.sub_eq_zero_of_le hn.le] using hsmall n hn.le
  · simpa [bound, Nat.add_sub_of_le (Nat.le_of_not_gt hn)] using htail (n - N)
