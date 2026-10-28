/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.PartitionIdentities.StaircaseAndPentagonal

/-!
# Rogers-Ramanujan partition identities

Rogers-Ramanujan generating functions and their partition interpretations.

Source references and common attribution are retained in
`DLMF.Combinatorics.PartitionIdentities`.
-/

@[expose] public section

noncomputable section

open Finset Filter Asymptotics

open DLMF.QSeries DLMF.Partitions

namespace DLMF.Combinatorics

/-! ### Rogers–Ramanujan (agent p26a) -/

/-- Coefficients of two natural-number power series agreeing on the unit disk are equal. -/
lemma s26a_coeff_unique_nat {a b : ℕ → ℕ} {F : ℂ → ℂ}
    (ha : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => (a n : ℂ) * q ^ n) (F q))
    (hb : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => (b n : ℂ) * q ^ n) (F q)) : a = b := by
  have hser : ∀ c : ℕ → ℕ, (∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => (c n : ℂ) * q ^ n) (F q)) →
      HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ fun n => (c n : ℂ)).sum
        (FormalMultilinearSeries.ofScalars ℂ fun n => (c n : ℂ)) 0 ∧
      ∀ q : ℂ, ‖q‖ < 1 →
        (FormalMultilinearSeries.ofScalars ℂ fun n => (c n : ℂ)).sum q = F q := by
    intro c hc
    set P := FormalMultilinearSeries.ofScalars ℂ fun n => (c n : ℂ)
    have hsumP : ∀ q : ℂ, P.sum q = ∑' n, (c n : ℂ) * q ^ n := fun q => by
      change FormalMultilinearSeries.ofScalarsSum _ q = _
      rw [FormalMultilinearSeries.ofScalars_sum_eq]; simp [smul_eq_mul]
    have hrad : 1 ≤ P.radius := by
      refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
      refine P.le_radius_of_summable_norm ?_
      have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
      have h := (hc (r : ℂ) (by simpa using hr1)).summable
      have h' : Summable fun n => (c n : ℝ) * (r : ℝ) ^ n := by
        rw [← Complex.summable_ofReal]; simpa using h
      simpa [P, FormalMultilinearSeries.ofScalars_norm] using h'
    refine ⟨(P.hasFPowerSeriesOnBall (lt_of_lt_of_le zero_lt_one hrad)).hasFPowerSeriesAt,
      fun q hq => by rw [hsumP]; exact (hc q hq).tsum_eq⟩
  obtain ⟨h1, e1⟩ := hser a ha
  obtain ⟨h2, e2⟩ := hser b hb
  have hev : ∀ᶠ z in nhds (0 : ℂ),
      (FormalMultilinearSeries.ofScalars ℂ fun n => (a n : ℂ)).sum z =
        (FormalMultilinearSeries.ofScalars ℂ fun n => (b n : ℂ)).sum z := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
    have : ‖z‖ < 1 := by simpa using hz
    rw [e1 z this, e2 z this]
  have := FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (h1.eq_formalMultilinearSeries_of_eventually h2 hev)
  ext n
  exact_mod_cast congrFun this n

/-- A product over two residue classes mod 5. -/
lemma s26a_hasProd_two_progressions {q : ℂ} (hq : ‖q‖ < 1) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a < b) (hb : b < 5) (S : Set ℕ) [DecidablePred (· ∈ S)]
    (hS : ∀ n, n ∈ S ↔ 1 ≤ n ∧ (n % 5 = a ∨ n % 5 = b)) :
    HasProd (fun j : ℕ => if j + 1 ∈ S then (1 - q ^ (j + 1))⁻¹ else 1)
      ((qPochhammerInf (q ^ a) (q ^ 5))⁻¹ * (qPochhammerInf (q ^ b) (q ^ 5))⁻¹) := by
  have hpos : ∀ r : ℕ, 0 < r → ‖q ^ r‖ < 1 := fun r hr => by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq hr.ne'
  set ι : ℕ ⊕ ℕ → ℕ := Sum.elim (fun i => 5 * i + (a - 1)) (fun i => 5 * i + (b - 1)) with hι
  have hιinj : Function.Injective ι := by
    rintro (i | i) (j | j) h <;> simp only [hι, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq] at h ⊢ <;> omega
  rw [← hιinj.hasProd_iff]
  · apply HasProd.sum
    · convert (r26a_hasProd_one_sub (w := q ^ a) (hpos 5 (by norm_num))).inv₀
        (qPochhammerInf_ne_zero_of_norm_lt_one (hpos a (by omega)) (hpos 5 (by norm_num)))
        using 1
      ext i
      simp only [Function.comp, hι, Sum.elim_inl]
      rw [ite_eq_left ((hS _).mpr ⟨by omega, Or.inl (by omega)⟩), ← pow_mul, ← pow_add,
        show 5 * i + (a - 1) + 1 = a + 5 * i by omega]
    · convert (r26a_hasProd_one_sub (w := q ^ b) (hpos 5 (by norm_num))).inv₀
        (qPochhammerInf_ne_zero_of_norm_lt_one (hpos b (by omega)) (hpos 5 (by norm_num)))
        using 1
      ext i
      simp only [Function.comp, hι, Sum.elim_inr]
      rw [ite_eq_left ((hS _).mpr ⟨by omega, Or.inr (by omega)⟩), ← pow_mul, ← pow_add,
        show 5 * i + (b - 1) + 1 = b + 5 * i by omega]
  · intro j hj
    refine ite_eq_right fun hS' => ?_
    obtain ⟨h1, h2⟩ := (hS _).mp hS'
    rcases h2 with h2 | h2
    · exact hj ⟨Sum.inl ((j + 1) / 5), by simp only [hι, Sum.elim_inl]; omega⟩
    · exact hj ⟨Sum.inr ((j + 1) / 5), by simp only [hι, Sum.elim_inr]; omega⟩

/-- Estimate under the stated parameter and domain assumptions: `n ∈ residueSetPM j 5 ↔ 1 ≤ n ∧ (n
% 5 = j % 5 ∨ n % 5 = (5 - j) % 5)`. -/
lemma s26a_mem_residueSetPM_five (j n : ℕ) (hj : j < 5) :
    n ∈ residueSetPM j 5 ↔ 1 ≤ n ∧ (n % 5 = j % 5 ∨ n % 5 = (5 - j) % 5) := by
  simp only [residueSetPM, Set.mem_ofPred_eq, Int.ModEq]
  omega

/-- Identity under the stated parameter and domain assumptions: `2 * m.choose 2 + m = m * m`. -/
lemma s26a_two_choose_add (m : ℕ) : 2 * m.choose 2 + m = m * m := by
  rcases m with _ | m
  · simp
  · rw [Nat.choose_two_right, Nat.add_sub_cancel]
    obtain ⟨t, ht⟩ := Nat.even_mul_pred_self (m + 1)
    rw [Nat.add_sub_cancel] at ht
    rw [ht, show t + t = 2 * t by ring, Nat.mul_div_cancel_left t two_pos]
    nlinarith

/-- The generating function of `p(∈ S, n)` for `S` two residue classes mod 5. -/
lemma s26a_hasSum_partitionCountIn_five {q : ℂ} (hq : ‖q‖ < 1) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a < b) (hb : b < 5) (S : Set ℕ) [DecidablePred (· ∈ S)]
    (hS : ∀ n, n ∈ S ↔ 1 ≤ n ∧ (n % 5 = a ∨ n % 5 = b)) :
    HasSum (fun n => (partitionCountIn S n : ℂ) * q ^ n)
      (1 / (qPochhammerInf (q ^ a) (q ^ 5) * qPochhammerInf (q ^ b) (q ^ 5))) := by
  obtain ⟨h1, h2⟩ := hasSum_partitionCountIn hq S
  rw [h2.unique (s26a_hasProd_two_progressions hq ha hab hb S hS), ← mul_inv, ← one_div] at h1
  exact h1

/-- (26.10.13), first Rogers–Ramanujan identity: `p(𝒟2, n) = p(∈ A_{1,5}, n)`. -/
@[dlmf 26.10.E13]
theorem partitionCountDiff_two_eq (n : ℕ) :
    partitionCountDiff 2 n = partitionCountIn (residueSetPM 1 5) n := by
  refine congrFun (s26a_coeff_unique_nat (F := fun q =>
    1 / (qPochhammerInf (q ^ 1) (q ^ 5) * qPochhammerInf (q ^ 4) (q ^ 5))) (fun q hq => ?_)
    (fun q hq => s26a_hasSum_partitionCountIn_five hq le_rfl (by norm_num) (by norm_num) _
      fun n => s26a_mem_residueSetPM_five 1 n (by norm_num))) n
  have h := (hasSum_partitionCountDiff hq 2).1
  simp_rw [s26a_two_choose_add] at h
  rw [DLMF.Bailey.rogers_ramanujan_first hq] at h
  simpa using h

/-- (26.10.14), second Rogers–Ramanujan identity: `p(𝒟2, ∈ T, n) = p(∈ A_{2,5}, n)`. -/
@[dlmf 26.10.E14]
theorem partitionCountDiffTwoNoOne_eq (n : ℕ) :
    partitionCountDiffTwoNoOne n = partitionCountIn (residueSetPM 2 5) n := by
  refine congrFun (s26a_coeff_unique_nat (F := fun q =>
    1 / (qPochhammerInf (q ^ 2) (q ^ 5) * qPochhammerInf (q ^ 3) (q ^ 5))) (fun q hq => ?_)
    (fun q hq => s26a_hasSum_partitionCountIn_five hq (by norm_num) (by norm_num) (by norm_num)
      _ fun n => s26a_mem_residueSetPM_five 2 n (by norm_num))) n
  have hc : ∀ n, partitionCountDiffTwoNoOne n = ∑ m ∈ range (n + 1) with m * (m + 1) ≤ n,
      partitionCountAtMostParts m (n - m * (m + 1)) := by
    intro n
    have h := s26a_card_diff_min_eq_sum 2 2 n (by norm_num)
    have he : ∀ m : ℕ, 2 * m.choose 2 + 2 * m = m * (m + 1) := fun m => by
      have := s26a_two_choose_add m; nlinarith
    simp only [he] at h
    rw [← h]
    rfl
  have h := (s26a_hasSum_staircase hq (fun m => m * (m + 1)) (fun m => by nlinarith)
    partitionCountDiffTwoNoOne hc).1
  have he : (∑' m : ℕ, q ^ (m * (m + 1)) * ∏ j ∈ Icc 1 m, (1 - q ^ j)⁻¹) =
      ∑' m : ℕ, q ^ (m * (m + 1) : ℕ) / qPochhammer q q m := by
    congr 1; ext m; rw [s26a_qPochhammer_eq_prod, div_eq_mul_inv, prod_inv_distrib]
  rw [he, DLMF.Bailey.rogers_ramanujan_second hq] at h
  exact h

/-- (26.10.15), Schur's theorem: `p(𝒟'3, n) = p(∈ A_{1,6}, n)`. -/
@[dlmf 26.10.E15]
theorem partitionCountSchur_eq (n : ℕ) :
    partitionCountSchur n = partitionCountIn (residueSetPM 1 6) n := by
  sorry

/-- §26.10(iv): `p(𝒟'3, n) ≤ p(𝒟3, n)`. -/
@[dlmf 26.10.iv]
theorem partitionCountSchur_le (n : ℕ) : partitionCountSchur n ≤ partitionCountDiff 3 n := by
  unfold partitionCountSchur partitionCountDiff
  exact Finset.card_le_card fun p => by simp only [mem_filter]; exact fun h => ⟨h.1, h.2.1⟩

/-- A partition of `n` from a multiset of positive parts. -/
def r26a_ofParts (n : ℕ) (s : Multiset ℕ) (hpos : ∀ i ∈ s, 0 < i) (hs : s.sum = n) :
    n.Partition := ⟨s, fun hi => hpos _ hi, hs⟩

/-- For distinct parts, `PartsDifferAtLeast` is a condition on pairs of different parts. -/
lemma r26a_partsDiffer_iff_of_nodup {n : ℕ} (k : ℕ) (p : n.Partition) (hp : p.parts.Nodup) :
    PartsDifferAtLeast k p ↔ ∀ x ∈ p.parts, ∀ y ∈ p.parts, x ≠ y → x + k ≤ y ∨ y + k ≤ x := by
  unfold PartsDifferAtLeast
  refine forall₂_congr fun x hx => ⟨fun h y hy hxy => h y ((hp.mem_erase_iff).2 ⟨Ne.symm hxy, hy⟩),
    fun h y hy => ?_⟩
  rw [hp.mem_erase_iff] at hy
  exact h y hy.2 (Ne.symm hy.1)

/-- A witness against Schur's condition: parts differ by at least `3`, two multiples of `3`
differ by `3`. -/
lemma r26a_exists_bad (n : ℕ) (hn : n = 9 ∨ 15 ≤ n) :
    ∃ p : n.Partition, PartsDifferAtLeast 3 p ∧ ¬ SchurCondition p := by
  -- the parts: two multiples of 3 at distance 3 and possibly a third part
  obtain ⟨a, c, ha, hcs, hsum⟩ : ∃ a c : ℕ, (a = 3 ∨ a = 6) ∧
      (c = 0 ∨ (c ≥ 1 ∧ (c + 3 ≤ a ∨ a + 6 ≤ c))) ∧ a + (a + 3) + c = n := by
    rcases hn with rfl | hn
    · exact ⟨3, 0, Or.inl rfl, Or.inl rfl, rfl⟩
    · by_cases h18 : 18 ≤ n
      · exact ⟨3, n - 9, Or.inl rfl, Or.inr ⟨by omega, Or.inr (by omega)⟩, by omega⟩
      · exact ⟨6, n - 15, Or.inr rfl, by omega, by omega⟩
  have h3a : 3 ∣ a := by rcases ha with rfl | rfl <;> norm_num
  -- common conclusion from the list of parts
  have key : ∀ (s : Multiset ℕ), s.Nodup → a ∈ s → a + 3 ∈ s → (∀ i ∈ s, 0 < i) → s.sum = n →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → x + 3 ≤ y ∨ y + 3 ≤ x) →
      ∃ p : n.Partition, PartsDifferAtLeast 3 p ∧ ¬ SchurCondition p := by
    intro s hnd has has3 hpos hs hd
    refine ⟨r26a_ofParts n s hpos hs, (r26a_partsDiffer_iff_of_nodup 3 _ hnd).2 hd, fun h => ?_⟩
    have := h.2 a has (a + 3) ((hnd.mem_erase_iff).2 ⟨by omega, has3⟩) h3a (by omega)
    omega
  rcases hcs with rfl | ⟨hc1, hc⟩
  · refine key {a, a + 3} ?_ (by simp) (by simp) ?_ (by simp; omega) ?_
    · simp
    · intro i hi; simp at hi; rcases ha with rfl | rfl <;> omega
    · intro x hx y hy hxy; simp at hx hy; omega
  · refine key {a, a + 3, c} ?_ (by simp) (by simp) ?_ (by simp; omega) ?_
    · simp; omega
    · intro i hi; simp at hi; rcases ha with rfl | rfl <;> omega
    · intro x hx y hy hxy; simp at hx hy; omega

/-- A partition with parts differing by at least `3` that violates Schur's condition has
`n = 9` or `n ≥ 15`. -/
lemma r26a_bad_imp {n : ℕ} (p : n.Partition) (hd : PartsDifferAtLeast 3 p)
    (hs : ¬ SchurCondition p) : n = 9 ∨ 15 ≤ n := by
  unfold SchurCondition at hs
  simp only [hd, true_and, not_forall] at hs
  obtain ⟨x, hx, y, hy, h3x, h3y, hxy⟩ := hs
  have hd' := hd x hx y hy
  have hyx : y ∈ p.parts := Multiset.mem_of_mem_erase hy
  -- `lo ∈ parts`, `lo + 3 ∈ parts.erase lo`
  obtain ⟨lo, hlo, hhi, h3lo⟩ : ∃ lo, lo ∈ p.parts ∧ lo + 3 ∈ p.parts.erase lo ∧ 3 ∣ lo := by
    rcases hd' with h | h
    · have : y = x + 3 := by omega
      exact ⟨x, hx, this ▸ hy, h3x⟩
    · have hxe : x = y + 3 := by omega
      refine ⟨y, hyx, ?_, h3y⟩
      rw [← hxe]; exact Multiset.mem_erase_of_ne (by omega) |>.2 hx
  have hlo0 := p.parts_pos hlo
  set rest := (p.parts.erase lo).erase (lo + 3)
  have e : p.parts = lo ::ₘ (lo + 3) ::ₘ rest := by
    rw [Multiset.cons_erase hhi, Multiset.cons_erase hlo]
  have hsum : lo + (lo + 3) + rest.sum = n := by
    have := p.parts_sum
    rw [e, Multiset.sum_cons, Multiset.sum_cons] at this
    omega
  rcases Nat.lt_or_ge lo 6 with hl6 | hl6
  · have hl3 : lo = 3 := by obtain ⟨t, rfl⟩ := h3lo; omega
    subst hl3
    rcases Multiset.empty_or_exists_mem rest with h0 | ⟨c, hc⟩
    · rw [h0, Multiset.sum_zero] at hsum; left; omega
    · right
      have hc1 : c ∈ p.parts.erase 3 := Multiset.mem_of_mem_erase hc
      have hc2 : c ∈ p.parts.erase (3 + 3) := by
        have : c ∈ (p.parts.erase (3 + 3)).erase 3 := by
          rw [Multiset.erase_comm]; exact hc
        exact Multiset.mem_of_mem_erase this
      have hc0 := p.parts_pos (Multiset.mem_of_mem_erase hc1)
      have d1 := hd 3 hlo c hc1
      have d2 := hd (3 + 3) (Multiset.mem_of_mem_erase hhi) c hc2
      have hcs : c ≤ rest.sum := Multiset.le_sum_of_mem hc
      omega
  · right; omega

/-- §26.10(iv), corrected: `p(𝒟'3, n) < p(𝒟3, n)` exactly for `n = 9` and `n ≥ 15`. DLMF
states strict inequality for `n ≥ 9`, but equality holds for `10 ≤ n ≤ 14`. -/
@[dlmf 26.10.iv "corrected: strict for n = 9 and n ≥ 15 (equality for 10 ≤ n ≤ 14)"]
theorem partitionCountSchur_lt_iff (n : ℕ) :
    partitionCountSchur n < partitionCountDiff 3 n ↔ n = 9 ∨ 15 ≤ n := by
  unfold partitionCountSchur partitionCountDiff
  have hsub : (univ.filter fun p : n.Partition => SchurCondition p) ⊆
      univ.filter fun p : n.Partition => PartsDifferAtLeast 3 p :=
    fun p => by simp only [mem_filter, mem_univ, true_and]; exact fun h => h.1
  constructor
  · intro h
    obtain ⟨p, hpB, hpA⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hsub (fun e => by
      rw [e] at h; exact lt_irrefl _ h))
    simp only [mem_filter, mem_univ, true_and] at hpB hpA
    exact r26a_bad_imp p hpB hpA
  · intro hn
    obtain ⟨p, hd, hs⟩ := r26a_exists_bad n hn
    refine card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun e => ?_⟩)
    have : p ∈ univ.filter fun p : n.Partition => PartsDifferAtLeast 3 p := by simp [hd]
    rw [← e] at this
    simp only [mem_filter, mem_univ, true_and] at this
    exact hs this

/-- §26.10(iv), Alder's conjecture (Yee 2004; DLMF's statement): for `k > 3`,
`p(𝒟k, n) ≥ p(∈ A_{1,k+3}, n)`. -/
@[dlmf 26.10.iv]
theorem partitionCountIn_le_partitionCountDiff {k : ℕ} (hk : 3 < k) (n : ℕ) :
    partitionCountIn (residueSetPM 1 (k + 3)) n ≤ partitionCountDiff k n := by
  sorry

/-- §26.10(iv): the inequality is strict for all sufficiently large `n` when `k = 2^m - 1`,
`m = 3, 4, 5`, or `k ≥ 32` (Yee 2004). -/
@[dlmf 26.10.iv]
theorem eventually_partitionCountIn_lt_partitionCountDiff {k : ℕ}
    (hk : k = 7 ∨ k = 15 ∨ k = 31 ∨ 32 ≤ k) :
    ∀ᶠ n in atTop, partitionCountIn (residueSetPM 1 (k + 3)) n < partitionCountDiff k n := by
  sorry

/-- (26.10.16): `p(𝒟, n) ∼ e^{π √(n/3)}/(768 n³)^{1/4}` as `n → ∞`. -/
@[dlmf 26.10.E16]
theorem partitionCountDistinct_isEquivalent :
    (fun n : ℕ => (partitionCountDistinct n : ℝ)) ~[atTop]
      fun n : ℕ => Real.exp (Real.pi * Real.sqrt (n / 3)) / (768 * (n : ℝ) ^ 3) ^ (1 / 4 : ℝ) := by
  sorry

/-- (26.10.20): the sawtooth `[[x]] = x - ⌊x⌋ - 1/2` for `x ∉ ℤ`, `[[x]] = 0` for `x ∈ ℤ`. -/
@[dlmf 26.10.E20]
def sawtooth (x : ℝ) : ℝ := if Int.fract x = 0 then 0 else x - ⌊x⌋ - 1 / 2

/-- (26.10.19): `f(h, k) = ∑_{j=1}^k [[(2j-1)/(2k)]] [[h(2j-1)/k]]`. -/
@[dlmf 26.10.E19]
def distinctPartitionDedekindSum (h k : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 k, sawtooth ((2 * j - 1 : ℝ) / (2 * k)) * sawtooth ((h : ℝ) * (2 * j - 1) / k)

/-- (26.10.18), corrected: `A_k(n) = ∑_{1 ≤ h ≤ k, (h,k) = 1} e^{π i f(h,k) - 2π i n h/k}`.
DLMF prints the range `1 < h ≤ k`, which gives `A_1(n) = 0` (see the module docstring). -/
@[dlmf 26.10.E18 "corrected: summation range 1 ≤ h ≤ k (printed 1 < h ≤ k)"]
def distinctPartitionKloosterman (k n : ℕ) : ℂ :=
  ∑ h ∈ Icc 1 k with Nat.Coprime h k,
    Complex.exp (Real.pi * Complex.I * distinctPartitionDedekindSum h k -
      2 * Real.pi * Complex.I * n * h / k)

/-- The sawtooth function has period `1`. -/
lemma r26a_sawtooth_add_int (x : ℝ) (m : ℤ) : sawtooth (x + m) = sawtooth x := by
  unfold sawtooth
  rw [Int.fract_add_intCast, Int.floor_add_intCast]
  push_cast; ring_nf

/-- The sawtooth function is odd. -/
lemma r26a_sawtooth_neg (x : ℝ) : sawtooth (-x) = -sawtooth x := by
  unfold sawtooth
  by_cases hx : Int.fract x = 0
  · have h0 : Int.fract (-x) = 0 := Int.fract_neg_eq_zero.mpr hx
    simp [hx, h0]
  · have h0 : Int.fract (-x) ≠ 0 := fun h => hx (Int.fract_neg_eq_zero.mp h)
    simp only [hx, h0, ↓reduceIte]
    have h1 := Int.fract_neg hx
    rw [← Int.self_sub_floor, ← Int.self_sub_floor] at h1
    linarith

/-- `f(k - h, k) = -f(h, k)`. -/
lemma r26a_dedekind_sub (h k : ℕ) (hhk : h ≤ k) (hk : 0 < k) :
    distinctPartitionDedekindSum (k - h) k = -distinctPartitionDedekindSum h k := by
  unfold distinctPartitionDedekindSum
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have : ((k - h : ℕ) : ℝ) * (2 * j - 1) / k =
      -((h : ℝ) * (2 * j - 1) / k) + ((2 * j - 1 : ℤ) : ℝ) := by
    push_cast [Nat.cast_sub hhk]; field_simp; ring
  rw [this, r26a_sawtooth_add_int, r26a_sawtooth_neg]; ring

open Complex in
/-- §26.10(vi): the terms for `h` and `k - h` are complex conjugates. -/
lemma r26a_kloosterman_im (k n : ℕ) : (distinctPartitionKloosterman k n).im = 0 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp [distinctPartitionKloosterman]
    · have hf : distinctPartitionDedekindSum 1 1 = 0 := by
        simp [distinctPartitionDedekindSum, sawtooth]
      have hs : (Icc 1 1).filter (fun h => Nat.Coprime h 1) = {1} := by decide
      rw [distinctPartitionKloosterman, hs, sum_singleton, hf]
      have h1 : (Real.pi : ℂ) * I * ((0 : ℝ) : ℂ) -
            2 * Real.pi * I * n * ((1 : ℕ) : ℂ) / ((1 : ℕ) : ℂ) =
          0 - (n : ℂ) * (2 * Real.pi * I) := by push_cast; ring
      rw [h1, exp_sub, exp_nat_mul_two_pi_mul_I, div_one, exp_zero, one_im]
  rw [← conj_eq_iff_im]
  unfold distinctPartitionKloosterman
  rw [map_sum]
  refine sum_nbij' (fun h => k - h) (fun h => k - h) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [mem_filter, mem_Icc] at hh ⊢
    have hne : h ≠ k := by
      rintro rfl
      have := hh.2; rw [Nat.coprime_self] at this; omega
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.coprime_self_sub_left hh.1.2]; exact hh.2
  · intro h hh
    simp only [mem_filter, mem_Icc] at hh ⊢
    have hne : h ≠ k := by
      rintro rfl
      have := hh.2; rw [Nat.coprime_self] at this; omega
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.coprime_self_sub_left hh.1.2]; exact hh.2
  · intro h hh; simp only [mem_filter, mem_Icc] at hh; omega
  · intro h hh; simp only [mem_filter, mem_Icc] at hh; omega
  · intro h hh
    simp only [mem_filter, mem_Icc] at hh
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    rw [← exp_conj, r26a_dedekind_sub h k hh.1.2 (by omega)]
    have e : (Real.pi : ℂ) * I * ((-distinctPartitionDedekindSum h k : ℝ) : ℂ) -
        2 * Real.pi * I * n * ((k - h : ℕ) : ℂ) / k =
        (starRingEnd ℂ) ((Real.pi : ℂ) * I * (distinctPartitionDedekindSum h k : ℂ) -
          2 * Real.pi * I * n * h / k) - (n : ℂ) * (2 * Real.pi * I) := by
      simp only [map_sub, map_mul, map_div₀, conj_ofReal, conj_I, map_natCast, map_ofNat]
      push_cast [Nat.cast_sub hh.1.2]
      field_simp
      ring
    rw [e, exp_sub, exp_nat_mul_two_pi_mul_I, div_one]
/-- §26.10(vi): `A_k(n)` is real-valued. -/
@[dlmf 26.10.vi]
theorem distinctPartitionKloosterman_im (k n : ℕ) : (distinctPartitionKloosterman k n).im = 0 :=
  r26a_kloosterman_im k n

/-- (26.10.17): `p(𝒟, n) = π ∑_{k ≥ 1} A_{2k-1}(n)/((2k-1)√(24n+1)) I₁(π/(2k-1) √((24n+1)/72))`
(with the corrected `A_k`, (26.10.18)); `I₁` is the project's `DLMF.Bessel.besselI 1`. -/
@[dlmf 26.10.E17]
theorem hasSum_partitionCountDistinct_bessel (n : ℕ) :
    HasSum (fun k : ℕ => (Real.pi : ℂ) * distinctPartitionKloosterman (2 * k + 1) n /
        ((2 * k + 1 : ℂ) * (Real.sqrt (24 * n + 1) : ℂ)) *
          DLMF.Bessel.besselI 1 ((Real.pi / (2 * k + 1) * Real.sqrt ((24 * n + 1) / 72) : ℝ)))
      (partitionCountDistinct n : ℂ) := by
  sorry

end DLMF.Combinatorics

end
end
