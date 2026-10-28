/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.PartitionIdentities.RestrictedProducts

/-!
# Staircase and pentagonal partition identities

Staircase bijections, distinct-part generating functions and the pentagonal theorem.

Source references and common attribution are retained in
`DLMF.Combinatorics.PartitionIdentities`.
-/

@[expose] public section

noncomputable section

open Finset Filter Asymptotics

open DLMF.QSeries DLMF.Partitions

namespace DLMF.Combinatorics

/-! ### Staircase generating functions (agent p26a) -/

/-- DLMF (26.10.10) (helper): the staircase count with minimal part `1`. -/
lemma s26a_partitionCountDiff_eq_sum (k n : ℕ) :
    partitionCountDiff k n =
      ∑ m ∈ range (n + 1) with k * m.choose 2 + m ≤ n,
        partitionCountAtMostParts m (n - (k * m.choose 2 + m)) := by
  have h := s26a_card_diff_min_eq_sum k 1 n le_rfl
  simp only [one_mul] at h
  rw [← h, partitionCountDiff]
  congr 1
  refine filter_congr fun p _ => ?_
  exact ⟨fun hp => ⟨hp, fun i hi => p.parts_pos hi⟩, fun hp => hp.1⟩

/-- `(q;q)_m = ∏_{j=1}^m (1 - q^j)`. -/
lemma s26a_qPochhammer_eq_prod (q : ℂ) (m : ℕ) :
    qPochhammer q q m = ∏ j ∈ Icc 1 m, (1 - q ^ j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [qPochhammer_succ, ih, Finset.prod_Icc_succ_top (by omega), pow_succ' q m]

/-- Generating function of `c n = ∑_{m, e m ≤ n} p_m(n - e m)` for `e m ≥ m`. -/
lemma s26a_hasSum_staircase {q : ℂ} (hq : ‖q‖ < 1) (e : ℕ → ℕ) (he : ∀ m, m ≤ e m)
    (c : ℕ → ℕ) (hc : ∀ n, c n = ∑ m ∈ range (n + 1) with e m ≤ n,
      partitionCountAtMostParts m (n - e m)) :
    HasSum (fun n => (c n : ℂ) * q ^ n) (∑' m : ℕ, q ^ e m * ∏ j ∈ Icc 1 m, (1 - q ^ j)⁻¹) ∧
      Summable fun m : ℕ => q ^ e m * ∏ j ∈ Icc 1 m, (1 - q ^ j)⁻¹ := by
  set r := ‖q‖
  have hr0 : 0 ≤ r := norm_nonneg q
  set F : ℕ × ℕ → ℂ := fun p => (partitionCountAtMostParts p.1 p.2 : ℂ) * q ^ (p.2 + e p.1)
    with hF
  have hrow : ∀ m, HasSum (fun N => F (m, N)) (q ^ e m * ∏ j ∈ Icc 1 m, (1 - q ^ j)⁻¹) := by
    intro m
    convert (hasSum_partitionCountAtMostParts hq m).mul_left (q ^ e m) using 1
    ext N; simp only [hF, pow_add]; ring
  have hrowa : ∀ m, HasSum (fun N => ‖F (m, N)‖) (r ^ e m * ∏ j ∈ Icc 1 m, (1 - r ^ j)⁻¹) := by
    intro m
    have h := (hasSum_partitionCountAtMostParts (q := (r : ℂ)) (by simpa [r] using hq) m).mul_left
      ((r : ℂ) ^ e m)
    have h2 : HasSum (fun N => ((‖F (m, N)‖ : ℝ) : ℂ))
        (((r ^ e m * ∏ j ∈ Icc 1 m, (1 - r ^ j)⁻¹ : ℝ)) : ℂ) := by
      convert h using 1
      · ext N; simp only [hF, norm_mul, norm_pow, Complex.norm_natCast, r, pow_add]
        push_cast; ring
      · push_cast; rfl
    exact Complex.hasSum_ofReal.mp h2
  have hbound : ∀ m, r ^ e m * ∏ j ∈ Icc 1 m, (1 - r ^ j)⁻¹ ≤
      Real.exp (1 / (1 - r) ^ 2) * r ^ m := by
    intro m
    rw [mul_comm]
    exact mul_le_mul (r26a_prod_inv_le hr0 hq _ (by simp))
      (pow_le_pow_of_le_one hr0 hq.le (he m)) (by positivity) (by positivity)
  have hsumF : Summable F := by
    refine Summable.of_norm ?_
    refine (summable_prod_of_nonneg fun _ => norm_nonneg _).mpr
      ⟨fun m => (hrowa m).summable, ?_⟩
    simp_rw [fun m => (hrowa m).tsum_eq]
    refine Summable.of_nonneg_of_le (fun m => by
      have := (hrowa m).nonneg (fun _ => norm_nonneg _); exact this) hbound ?_
    exact (summable_geometric_of_lt_one hr0 hq).mul_left _
  have h1 := hsumF.hasSum.prod_fiberwise hrow
  refine ⟨?_, h1.summable⟩
  rw [h1.tsum_eq]
  -- reindex by `n = N + e m`
  set G : ℕ × ℕ → ℂ := fun p => if e p.2 ≤ p.1 then
    (partitionCountAtMostParts p.2 (p.1 - e p.2) : ℂ) * q ^ p.1 else 0 with hG
  set ι : ℕ × ℕ → ℕ × ℕ := fun p => (p.2 + e p.1, p.1) with hι
  have hιinj : Function.Injective ι := by
    rintro ⟨m, N⟩ ⟨m', N'⟩ h
    simp only [hι, Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    simp only [Prod.mk.injEq, true_and]; omega
  have hGι : G ∘ ι = F := by
    ext ⟨m, N⟩
    simp only [Function.comp, hG, hι, hF, Nat.le_add_left, ite_true, Nat.add_sub_cancel]
  have hGsum : HasSum G (∑' p, F p) := by
    rw [← (hιinj.hasSum_iff ?_), hGι]
    · exact hsumF.hasSum
    · rintro ⟨n, m⟩ hnm
      simp only [hG]
      by_cases h : e m ≤ n
      · exact absurd ⟨(m, n - e m), by simp [hι]; omega⟩ hnm
      · simp [h]
  refine hGsum.prod_fiberwise fun n => ?_
  rw [hc n, Nat.cast_sum, sum_mul, sum_filter]
  refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
  simp only [mem_range, not_lt] at hm
  simp only [hG]
  rw [ite_eq_right (by have := he m; omega)]

/-- (26.10.4): `∑ p(𝒟k, n) qⁿ = 1 + ∑_{m ≥ 1} q^{(km² + (2-k)m)/2}/(q;q)_m` for `|q| < 1`;
the exponent is written `k·m(m-1)/2 + m` (the `m = 0` term is `1`). -/
@[dlmf 26.10.E4]
theorem hasSum_partitionCountDiff {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    HasSum (fun n => (partitionCountDiff k n : ℂ) * q ^ n)
        (∑' m : ℕ, q ^ (k * m.choose 2 + m) / qPochhammer q q m) ∧
      Summable fun m : ℕ => q ^ (k * m.choose 2 + m) / qPochhammer q q m := by
  have h := s26a_hasSum_staircase hq (fun m => k * m.choose 2 + m) (fun m => by omega)
    (partitionCountDiff k) (s26a_partitionCountDiff_eq_sum k)
  have he : (fun m : ℕ => q ^ (k * m.choose 2 + m) / qPochhammer q q m) =
      fun m => q ^ (k * m.choose 2 + m) * ∏ j ∈ Icc 1 m, (1 - q ^ j)⁻¹ := by
    ext m; rw [s26a_qPochhammer_eq_prod, div_eq_mul_inv, prod_inv_distrib]
  rw [he]
  exact h

/-- (26.10.5): `∑ p(∈ S, n) qⁿ = ∏_{j ∈ S} (1 - q^j)⁻¹` for `|q| < 1` and any set `S` of
positive integers (`0 ∉ S`; the product over `j ∉ S` contributes `1`). -/
@[dlmf 26.10.E5]
theorem hasSum_partitionCountIn {q : ℂ} (hq : ‖q‖ < 1) (S : Set ℕ) [DecidablePred (· ∈ S)] :
    HasSum (fun n => (partitionCountIn S n : ℂ) * q ^ n)
        (∏' j : ℕ, if j + 1 ∈ S then (1 - q ^ (j + 1))⁻¹ else 1) ∧
      HasProd (fun j : ℕ => if j + 1 ∈ S then (1 - q ^ (j + 1))⁻¹ else 1)
        (∏' j : ℕ, if j + 1 ∈ S then (1 - q ^ (j + 1))⁻¹ else 1) :=
  r26a_hasSum_partitionCountIn hq S

/-- Removing `k` copies of an allowed part `a`: partitions of `n` with parts in `P` and at least `k`
copies of `a` correspond to partitions of `n - k a` with parts in `P`. -/
lemma r26a_card_restricted_count_ge (P : ℕ → Prop) [DecidablePred P] {a : ℕ} (ha1 : 1 ≤ a)
    (hP : P a) : ∀ k n : ℕ, k * a ≤ n →
      #{p ∈ Nat.Partition.restricted n P | k ≤ p.parts.count a} =
        #(Nat.Partition.restricted (n - k * a) P) := by
  intro k
  induction k with
  | zero =>
    intro n _
    rw [zero_mul, Nat.sub_zero]
    congr 1
    exact filter_true_of_mem fun _ _ => Nat.zero_le _
  | succ k ih =>
    intro n hn
    have ha : a ≤ n := by nlinarith
    rw [show n - (k + 1) * a = n - a - k * a by rw [add_mul, one_mul]; omega,
      ← ih (n - a) (by rw [add_mul, one_mul] at hn; omega)]
    let e := Nat.Partition.partitionWithPartEquiv ha1 ha
    refine card_bij (fun p hp => e ⟨p, ?_⟩) ?_ ?_ ?_
    · simp only [mem_filter] at hp
      exact Multiset.count_pos.mp (by omega)
    · intro p hp
      simp only [mem_filter, Nat.Partition.restricted, mem_univ, true_and] at hp ⊢
      rw [Nat.Partition.partitionWithPartEquiv_apply_parts]
      refine ⟨fun i hi => hp.1 i (Multiset.mem_of_mem_erase hi), ?_⟩
      rw [Multiset.count_erase_self]; exact Nat.le_sub_of_add_le hp.2
    · intro p _ p' _ h
      exact congrArg Subtype.val (e.injective h)
    · intro q hq
      simp only [mem_filter, Nat.Partition.restricted, mem_univ, true_and] at hq
      refine ⟨(e.symm q).1, ?_, by simp⟩
      simp only [mem_filter, Nat.Partition.restricted, mem_univ, true_and,
        Nat.Partition.partitionWithPartEquiv_symm_apply_parts, e]
      refine ⟨fun i hi => ?_, ?_⟩
      · rcases Multiset.mem_cons.mp hi with rfl | hi
        · exact hP
        · exact hq.1 i hi
      · rw [Multiset.count_cons_self]; omega

/-- (26.10.11) for a predicate: `n p(P, n) = ∑_{t=1}^n p(P, n - t) ∑_{j ∣ t, P j} j`. -/
lemma r26a_card_restricted_recurrence (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    n * #(Nat.Partition.restricted n P) =
      ∑ t ∈ Icc 1 n, #(Nat.Partition.restricted (n - t) P) * ∑ j ∈ t.divisors with P j, j := by
  set R := Nat.Partition.restricted n P
  -- left side: sum over partitions of the sum of the parts
  have hL : n * #R = ∑ j ∈ (Icc 1 n).filter P, j * ∑ p ∈ R, p.parts.count j := by
    have h1 : ∀ p ∈ R, n = ∑ j ∈ (Icc 1 n).filter P, j * p.parts.count j := by
      intro p hp
      simp only [R, Nat.Partition.restricted, mem_filter, mem_univ, true_and] at hp
      conv_lhs => rw [← p.parts_sum, Finset.sum_multiset_count]
      simp_rw [smul_eq_mul, mul_comm (Multiset.count _ _)]
      apply sum_subset
      · intro j hj
        rw [Multiset.mem_toFinset] at hj
        simp only [mem_filter, mem_Icc]
        exact ⟨⟨p.parts_pos hj, Nat.Partition.le_of_mem_parts hj⟩, hp j hj⟩
      · intro j _ hj; rw [Multiset.mem_toFinset] at hj; simp [Multiset.count_eq_zero_of_notMem hj]
    rw [mul_comm, ← smul_eq_mul, ← sum_const, sum_congr rfl h1, sum_comm]
    simp_rw [mul_sum]
  -- the multiplicity of `j` as a sum of indicator counts
  have hC : ∀ j ∈ (Icc 1 n).filter P, ∑ p ∈ R, p.parts.count j =
      ∑ t ∈ (Icc 1 n).filter (j ∣ ·), #(Nat.Partition.restricted (n - t) P) := by
    intro j hj
    simp only [mem_filter, mem_Icc] at hj
    have hcount : ∀ p ∈ R,
        p.parts.count j = ∑ k ∈ Icc 1 n, if k ≤ p.parts.count j then 1 else 0 := by
      intro p _
      rw [sum_boole, Nat.cast_id]
      have hle : p.parts.count j ≤ n := by
        have := Multiset.count_le_card j p.parts
        have h2 : Multiset.card p.parts ≤ n := by
          have := Multiset.card_nsmul_le_sum (s := p.parts) (a := 1) fun i hi => p.parts_pos hi
          rw [smul_eq_mul, mul_one, p.parts_sum] at this
          exact this
        omega
      rw [show (Icc 1 n).filter (fun k => k ≤ p.parts.count j) = Icc 1 (p.parts.count j) by
        ext k; simp only [mem_filter, mem_Icc]; omega]
      simp
    rw [sum_congr rfl hcount, sum_comm]
    simp_rw [← card_filter]
    -- reindex `t = k j`
    have hk : ∀ k ∈ Icc 1 n, #{p ∈ R | k ≤ p.parts.count j} =
        if k * j ≤ n then #(Nat.Partition.restricted (n - k * j) P) else 0 := by
      intro k _
      split_ifs with hkj
      · exact r26a_card_restricted_count_ge P hj.1.1 hj.2 k n hkj
      · rw [card_eq_zero, filter_eq_empty_iff]
        intro p _ hp
        apply hkj
        have : p.parts.count j * j ≤ n := by
          obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp
            (Multiset.le_count_iff_replicate_le.mp (le_refl (p.parts.count j)))
          calc p.parts.count j * j = (Multiset.replicate (p.parts.count j) j).sum := by simp
            _ ≤ (Multiset.replicate (p.parts.count j) j).sum + u.sum := Nat.le_add_right _ _
            _ = p.parts.sum := by rw [← Multiset.sum_add, ← hu]
            _ = n := p.parts_sum
        calc k * j ≤ p.parts.count j * j := Nat.mul_le_mul_right _ hp
          _ ≤ n := this
    rw [sum_congr rfl hk, ← sum_filter]
    have hmap : (Icc 1 n).filter (j ∣ ·) =
        ((Icc 1 n).filter (· * j ≤ n)).map ⟨(· * j), mul_left_injective₀ (by omega)⟩ := by
      ext t
      simp only [mem_filter, mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨h1, h2⟩, k, rfl⟩
        refine ⟨k, ⟨⟨?_, ?_⟩, by rw [mul_comm]; omega⟩, mul_comm _ _⟩
        · rcases k with _ | k
          · simp at h1
          · omega
        · nlinarith
      · rintro ⟨k, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
        exact ⟨⟨by nlinarith, h3⟩, Dvd.intro_left k rfl⟩
    rw [hmap, sum_map]
    rfl
  rw [hL, sum_congr rfl fun j hj => by rw [hC j hj]]
  simp_rw [mul_sum]
  rw [sum_comm' (t' := Icc 1 n) (s' := fun t => t.divisors.filter P)]
  · refine sum_congr rfl fun t _ => sum_congr rfl fun j _ => mul_comm _ _
  · intro j t
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hPj⟩, ⟨h3, h4⟩, hjt⟩
      exact ⟨⟨⟨hjt, by omega⟩, hPj⟩, h3, h4⟩
    · rintro ⟨⟨⟨hjt, ht0⟩, hPj⟩, h3, h4⟩
      have := Nat.le_of_dvd (by omega) hjt
      have : 0 < j := Nat.pos_of_dvd_of_pos hjt (by omega)
      exact ⟨⟨⟨by omega, by omega⟩, hPj⟩, ⟨h3, h4⟩, hjt⟩

/-- (26.10.6): `n p(𝒟, n) = ∑_{t=1}^n p(𝒟, n - t) ∑_{j ∣ t, j odd} j` (stated multiplied by
`n`). -/
@[dlmf 26.10.E6]
theorem partitionCountDistinct_recurrence (n : ℕ) :
    n * partitionCountDistinct n =
      ∑ t ∈ Icc 1 n, partitionCountDistinct (n - t) * ∑ j ∈ t.divisors with Odd j, j := by
  -- Euler: `p(𝒟, m) = p(𝒪, m)`, then (26.10.11) for odd parts
  have h : ∀ m, partitionCountDistinct m = #(Nat.Partition.restricted m (¬ Even ·)) := fun m => by
    rw [partitionCountDistinct, ← Nat.Partition.card_odds_eq_card_distincts]; rfl
  simp_rw [h]
  rw [r26a_card_restricted_recurrence]
  refine sum_congr rfl fun t _ => ?_
  congr 1
  refine sum_congr (filter_congr fun j _ => Nat.not_even_iff_odd) fun _ _ => rfl

open PowerSeries PowerSeries.WithPiTopology in
/-- Coefficients of the partial products `∏_{i ∈ s} (1 + X^{i+1})` are eventually the distinct
partition counts. -/
lemma r26a_coeff_prod_one_add_eventually (n : ℕ) :
    ∀ᶠ s in atTop, coeff n (∏ i ∈ s, (1 + X ^ (i + 1) : ℤ⟦X⟧)) = partitionCountDistinct n := by
  have h := Nat.Partition.hasProd_powerSeriesMk_card_countRestricted ℤ (m := 2) two_pos
  rw [HasProd, tendsto_iff_coeff_tendsto] at h
  have h2 := h n
  rw [coeff_mk, nhds_discrete, tendsto_pure] at h2
  filter_upwards [h2] with s hs
  rw [partitionCountDistinct, ← Nat.Partition.countRestricted_two, ← hs]
  congr 1
  exact prod_congr rfl fun i _ => by simp [sum_range_succ]

open PowerSeries PowerSeries.WithPiTopology in
/-- `(q;q)_∞ ∏ (1 + q^j) = (q²;q²)_∞`, coefficientwise:
`∑_{i ≤ n} [q^i](q;q)_∞ · p(𝒟, n - i) = [q^n](q²;q²)_∞`. -/
lemma r26a_sum_pentagonal_mul_distinct (n : ℕ) :
    ∑ i ∈ range (n + 1), coeff i (pentagonalSeries ℤ) * partitionCountDistinct (n - i) =
      if 2 ∣ n then coeff (n / 2) (pentagonalSeries ℤ) else 0 := by
  have e1 : ∀ᶠ s in atTop, ∀ j ∈ range (n + 1),
      coeff j (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)) = coeff j (pentagonalSeries ℤ) :=
    (eventually_all_finset _).2 fun j _ => coeff_prod_one_sub_X_pow_eventually_eq ℤ j
  have e2 : ∀ᶠ s in atTop, ∀ j ∈ range (n + 1),
      coeff j (∏ i ∈ s, (1 + X ^ (i + 1) : ℤ⟦X⟧)) = partitionCountDistinct j :=
    (eventually_all_finset _).2 fun j _ => r26a_coeff_prod_one_add_eventually j
  obtain ⟨s, h1, h2, h3⟩ :=
    (e1.and (e2.and (coeff_prod_one_sub_X_pow_eventually_eq ℤ (n / 2)))).exists
  have hprod : (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)) * ∏ i ∈ s, (1 + X ^ (i + 1) : ℤ⟦X⟧) =
      expand 2 two_ne_zero (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)) := by
    rw [← prod_mul_distrib, map_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [map_sub, map_one, map_pow, expand_X]
    ring
  have hc := congrArg (coeff n) hprod
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_expand] at hc
  rw [← h3]
  convert hc using 1
  refine sum_congr rfl fun i hi => ?_
  simp only
  rw [h1 i hi, h2 (n - i) (by simp)]

open PowerSeries PowerSeries.WithPiTopology in
/-- `(-1)^k = (-1)^{|k|}` for the `negOnePow` sign. -/
lemma r26a_coe_negOnePow (k : ℤ) : ((k.negOnePow : ℤˣ) : ℤ) = (-1) ^ k.natAbs := by
  rw [← Int.negOnePow_abs, ← Int.natCast_natAbs, Int.coe_negOnePow_natCast]

open PowerSeries PowerSeries.WithPiTopology in
/-- `|k| ≤ k(3k-1)/2`. -/
lemma r26a_natAbs_le_pentagonal (k : ℤ) : k.natAbs ≤ pentagonal k := by
  have h := two_mul_natCast_pentagonal k
  have : (k.natAbs : ℤ) ≤ pentagonal k := by
    rcases le_or_gt 0 k with hk | hk
    · rw [Int.natAbs_of_nonneg hk]; nlinarith
    · rw [Int.ofNat_natAbs_of_nonpos hk.le]; nlinarith
  exact_mod_cast this

open PowerSeries PowerSeries.WithPiTopology in
/-- (26.10.7), proved via `(q;q)_∞ (-q;q)_∞ = (q²;q²)_∞` and the pentagonal number theorem. -/
lemma r26a_pentagonal_distinct (n : ℕ) :
    ∑ k ∈ Icc (-(n : ℤ)) n with pentagonal k ≤ n,
        (-1 : ℤ) ^ k.natAbs * partitionCountDistinct (n - pentagonal k) =
      ∑ r ∈ Icc (-(n : ℤ)) n, if (n : ℤ) = r * (3 * r - 1) then (-1 : ℤ) ^ r.natAbs else 0 := by
  set K := (Icc (-(n : ℤ)) n).filter (pentagonal · ≤ n)
  have hL : ∑ k ∈ K, (-1 : ℤ) ^ k.natAbs * partitionCountDistinct (n - pentagonal k) =
      ∑ i ∈ range (n + 1), coeff i (pentagonalSeries ℤ) * partitionCountDistinct (n - i) := by
    simp_rw [coeff_pentagonalSeries_mul_eq_extend ℤ _
      (fun i => (partitionCountDistinct (n - i) : ℤ))]
    rw [← sum_subset (s₁ := K.image pentagonal)]
    · rw [sum_image (fun x _ y _ h => pentagonal_injective h)]
      refine sum_congr rfl fun k _ => ?_
      rw [pentagonal_injective.extend_apply, r26a_coe_negOnePow, Int.cast_id]
    · intro i hi
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hi
      simp only [K, mem_filter] at hk
      exact mem_range.mpr (Nat.lt_succ_of_le hk.2)
    · intro i hi hiK
      by_cases hr : ∃ k, pentagonal k = i
      · obtain ⟨k, rfl⟩ := hr
        exfalso; apply hiK
        refine mem_image_of_mem _ ?_
        have h1 := r26a_natAbs_le_pentagonal k
        have h2 : pentagonal k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
        simp only [K, mem_filter, mem_Icc]
        refine ⟨⟨?_, ?_⟩, h2⟩ <;> omega
      · rw [Function.extend_apply' _ _ _ (by simpa using hr)]; rfl
  rw [hL, r26a_sum_pentagonal_mul_distinct]
  have hcond : ∀ r : ℤ, ((n : ℤ) = r * (3 * r - 1) ↔ 2 * pentagonal r = n) := by
    intro r
    rw [← two_mul_natCast_pentagonal]; constructor <;> intro h <;> omega
  by_cases hex : ∃ r : ℤ, 2 * pentagonal r = n
  · obtain ⟨r, hr⟩ := hex
    have hr1 := r26a_natAbs_le_pentagonal r
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨_, hr.symm⟩), show n / 2 = pentagonal r by omega,
      coeff_pentagonalSeries_pentagonal, r26a_coe_negOnePow, Int.cast_id]
    rw [sum_eq_single r]
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ((hcond r).2 hr))]
    · intro b _ hb
      refine ite_eq_right_of_eq_false _ _ (eq_false fun h => ?_)
      exact hb (pentagonal_injective (by have := (hcond b).1 h; omega))
    · intro h; exfalso; apply h; simp only [mem_Icc]; constructor <;> omega
  · push Not at hex
    rw [sum_eq_zero fun r _ =>
      ite_eq_right_of_eq_false _ _ (eq_false fun h => hex r ((hcond r).1 h))]
    split_ifs with h2
    · apply coeff_pentagonalSeries_eq_zero
      rintro ⟨k, hk⟩
      exact hex k (by omega)
    · rfl

/-- (26.10.7): `∑_{k ∈ ℤ} (-1)^k p(𝒟, n - k(3k-1)/2) = (-1)^r` if `n = r(3r ± 1)` and `0`
otherwise. The printed sum over `k ≥ 0` with both signs (the `k = 0` term once) is the sum over
`k ∈ ℤ` with the pentagonal numbers `pentagonal k = k(3k-1)/2`; all relevant `k` lie in
`[-n, n]`, and the right side is written as a sum over the (at most one) `r ∈ ℤ` with
`n = r(3r - 1)`. -/
@[dlmf 26.10.E7]
theorem sum_neg_one_pow_partitionCountDistinct_pentagonal (n : ℕ) :
    ∑ k ∈ Icc (-(n : ℤ)) n with pentagonal k ≤ n,
        (-1 : ℤ) ^ k.natAbs * partitionCountDistinct (n - pentagonal k) =
      ∑ r ∈ Icc (-(n : ℤ)) n, if (n : ℤ) = r * (3 * r - 1) then (-1 : ℤ) ^ r.natAbs else 0 :=
  r26a_pentagonal_distinct n

/-- (26.10.8): `∑_{k ∈ ℤ} (-1)^k p(𝒟, n - k(3k-1)) = 1` if `n = r(r ± 1)/2` (a triangular
number) and `0` otherwise (same reading of the `±` sum as in (26.10.7)); the right side is a sum
over the (at most one) `r ≥ 0` with `n = r(r+1)/2`. -/
@[dlmf 26.10.E8]
theorem sum_neg_one_pow_partitionCountDistinct_two_pentagonal (n : ℕ) :
    ∑ k ∈ Icc (-(n : ℤ)) n with 2 * pentagonal k ≤ n,
        (-1 : ℤ) ^ k.natAbs * partitionCountDistinct (n - 2 * pentagonal k) =
      ∑ r ∈ range (n + 1), if n = r * (r + 1) / 2 then (1 : ℤ) else 0 := by
  sorry

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_sum_map_succ (s : Multiset ℕ) : (s.map (· + 1)).sum = s.sum + Multiset.card s := by
  rw [Multiset.sum_map_add, Multiset.map_id', Multiset.map_const', Multiset.sum_replicate,
    smul_eq_mul, mul_one]

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_map_pred_succ {s : Multiset ℕ} (hs : ∀ i ∈ s, 0 < i) :
    (s.map (· - 1)).map (· + 1) = s := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id s]
  exact Multiset.map_congr rfl fun i hi => by simp only [Function.comp, id]; have := hs i hi; omega

/-- Adding `1` to each part of a partition of `N` into `m` parts. -/
def r26a_shift {N : ℕ} (q : N.Partition) (n : ℕ) (h : N + Multiset.card q.parts = n) :
    n.Partition where
  parts := q.parts.map (· + 1)
  parts_pos := by intro i hi; obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hi; omega
  parts_sum := by rw [r26a_sum_map_succ, q.parts_sum, h]

/-- Adding `1` to each part of a partition of `N` into `m - 1` parts and adjoining a part `1`. -/
def r26a_shiftCons {N : ℕ} (q : N.Partition) (n : ℕ) (h : N + Multiset.card q.parts + 1 = n) :
    n.Partition where
  parts := 1 ::ₘ q.parts.map (· + 1)
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi
    · exact one_pos
    · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hi; omega
  parts_sum := by rw [Multiset.sum_cons, r26a_sum_map_succ, q.parts_sum, ← h]; ring

/-- Subtracting `1` from each part. -/
def r26a_unshift {n : ℕ} (p : n.Partition) (N : ℕ) (h : N + Multiset.card p.parts = n)
    (h1 : 1 ∉ p.parts) : N.Partition where
  parts := p.parts.map (· - 1)
  parts_pos := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hi
    have := p.parts_pos hj
    have : j ≠ 1 := fun e => h1 (e ▸ hj)
    omega
  parts_sum := by
    have := r26a_sum_map_succ (p.parts.map (· - 1))
    rw [r26a_map_pred_succ (fun i hi => p.parts_pos hi), Multiset.card_map, p.parts_sum] at this
    omega

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_parts_shift {N : ℕ} (q : N.Partition) (n : ℕ) (h : N + Multiset.card q.parts = n) :
    (r26a_shift q n h).parts = q.parts.map (· + 1) := rfl

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_parts_shiftCons {N : ℕ} (q : N.Partition) (n : ℕ)
    (h : N + Multiset.card q.parts + 1 = n) :
    (r26a_shiftCons q n h).parts = 1 ::ₘ q.parts.map (· + 1) := rfl

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_parts_unshift {n : ℕ} (p : n.Partition) (N : ℕ) (h : N + Multiset.card p.parts = n)
    (h1 : 1 ∉ p.parts) : (r26a_unshift p N h h1).parts = p.parts.map (· - 1) := rfl

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_nodup_map_pred {s : Multiset ℕ} (hs : ∀ i ∈ s, 0 < i) (hn : s.Nodup) :
    (s.map (· - 1)).Nodup :=
  hn.map_on fun x hx y hy hxy => by have := hs x hx; have := hs y hy; omega

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_card_distinct_no_one {m n : ℕ} (hmn : m ≤ n) :
    #{p ∈ Nat.Partition.distincts n | p.parts.card = m ∧ 1 ∉ p.parts} =
      #{p ∈ Nat.Partition.distincts (n - m) | p.parts.card = m} := by
  symm
  refine card_bij (fun q hq => r26a_shift q n (by
    simp only [mem_filter] at hq; rw [hq.2]; omega)) ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and] at hq ⊢
    rw [r26a_parts_shift]
    refine ⟨hq.1.map (add_left_injective 1), by rw [Multiset.card_map, hq.2], fun h => ?_⟩
    obtain ⟨j, hj, hj1⟩ := Multiset.mem_map.mp h
    have := q.parts_pos hj
    omega
  · intro q _ q' _ h
    have := congrArg Nat.Partition.parts h
    rw [r26a_parts_shift, r26a_parts_shift] at this
    exact Nat.Partition.ext (Multiset.map_injective (add_left_injective 1) this)
  · intro p hp
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and] at hp
    have hN : n - m + Multiset.card p.parts = n := by rw [hp.2.1]; omega
    refine ⟨r26a_unshift p (n - m) hN hp.2.2, ?_, ?_⟩
    · simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and]
      rw [r26a_parts_unshift, Multiset.card_map]
      exact ⟨r26a_nodup_map_pred (fun i hi => p.parts_pos hi) hp.1, hp.2.1⟩
    · apply Nat.Partition.ext
      rw [r26a_parts_shift, r26a_parts_unshift, r26a_map_pred_succ (fun i hi => p.parts_pos hi)]

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_card_distinct_one {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    #{p ∈ Nat.Partition.distincts n | p.parts.card = m ∧ 1 ∈ p.parts} =
      #{p ∈ Nat.Partition.distincts (n - m) | p.parts.card = m - 1} := by
  symm
  refine card_bij (fun q hq => r26a_shiftCons q n (by
    simp only [mem_filter] at hq; rw [hq.2]; omega)) ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and] at hq ⊢
    rw [r26a_parts_shiftCons]
    refine ⟨Multiset.nodup_cons.mpr ⟨fun h => ?_, hq.1.map (add_left_injective 1)⟩,
      by rw [Multiset.card_cons, Multiset.card_map, hq.2]; omega, Multiset.mem_cons_self _ _⟩
    obtain ⟨j, hj, hj1⟩ := Multiset.mem_map.mp h
    have := q.parts_pos hj
    omega
  · intro q _ q' _ h
    have := congrArg Nat.Partition.parts h
    rw [r26a_parts_shiftCons, r26a_parts_shiftCons, Multiset.cons_inj_right] at this
    exact Nat.Partition.ext (Multiset.map_injective (add_left_injective 1) this)
  · intro p hp
    simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and] at hp
    have hn1 : 1 ≤ n := by omega
    let p' := Nat.Partition.partitionWithPartEquiv le_rfl hn1 ⟨p, hp.2.2⟩
    have hp' : p'.parts = p.parts.erase 1 := by
      simp [p', Nat.Partition.partitionWithPartEquiv_apply_parts]
    have hcard : Multiset.card p'.parts = m - 1 := by
      rw [hp', Multiset.card_erase_of_mem hp.2.2, hp.2.1]; rfl
    have h1 : 1 ∉ p'.parts := by
      rw [hp']; exact (Multiset.nodup_iff_count_le_one.mp hp.1 1 |> fun h =>
        fun hm1 => by
          have := Multiset.count_erase_self 1 p.parts
          have h2 := Multiset.count_pos.mpr hm1
          omega)
    have hN : n - m + Multiset.card p'.parts = n - 1 := by rw [hcard]; omega
    refine ⟨r26a_unshift p' (n - m) hN h1, ?_, ?_⟩
    · simp only [mem_filter, Nat.Partition.distincts, mem_univ, true_and]
      rw [r26a_parts_unshift, Multiset.card_map, hcard]
      refine ⟨r26a_nodup_map_pred (fun i hi => p'.parts_pos hi) ?_, rfl⟩
      rw [hp']; exact hp.1.erase 1
    · apply Nat.Partition.ext
      rw [r26a_parts_shiftCons, r26a_parts_unshift,
        r26a_map_pred_succ (fun i hi => p'.parts_pos hi), hp']
      exact Multiset.cons_erase hp.2.2

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_atMost_succ (m N : ℕ) :
    partitionCountAtMostDistinct (m + 1) N = partitionCountAtMostDistinct m N +
      #{p ∈ Nat.Partition.distincts N | p.parts.card = m + 1} := by
  unfold partitionCountAtMostDistinct
  rw [← card_filter_add_card_filter_not (fun p : N.Partition => p.parts.card ≤ m), filter_filter,
    filter_filter]
  congr 2
  · exact filter_congr fun p _ => by omega
  · exact filter_congr fun p _ => by omega

/-- Helper for (26.10.9) (agent p26a). -/
lemma r26a_atMost_zero (N : ℕ) :
    partitionCountAtMostDistinct 0 N = #{p ∈ Nat.Partition.distincts N | p.parts.card = 0} := by
  unfold partitionCountAtMostDistinct
  congr 1
  exact filter_congr fun p _ => by omega

/-- (26.10.9), corrected, for exactly `m` distinct parts:
`q_m(n) = q_m(n - m) + q_{m-1}(n - m)` for `1 ≤ m ≤ n`, where
`q_m(n) = p_m(𝒟, n) - p_{m-1}(𝒟, n)`. -/
@[dlmf 26.10.E9 "corrected form for exactly m distinct parts"]
theorem card_distinct_card_eq_recurrence {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    #{p ∈ Nat.Partition.distincts n | p.parts.card = m} =
      #{p ∈ Nat.Partition.distincts (n - m) | p.parts.card = m} +
        #{p ∈ Nat.Partition.distincts (n - m) | p.parts.card = m - 1} := by
  rw [← card_filter_add_card_filter_not (fun p : n.Partition => 1 ∉ p.parts), filter_filter,
    filter_filter, add_comm]
  simp only [not_not]
  rw [← r26a_card_distinct_no_one hmn, ← r26a_card_distinct_one hm hmn, add_comm]

/-- (26.10.9), corrected: `p_m(𝒟, n) = p_{m-1}(𝒟, n) + p_m(𝒟, n - m) - p_{m-2}(𝒟, n - m)`
for `1 ≤ m ≤ n` (with `p_{-1} = 0`). DLMF prints `p_m(𝒟, n) = p_m(𝒟, n - m) + p_{m-1}(𝒟, n)`,
which fails already at `m = n = 2` (see the module docstring). -/
@[dlmf 26.10.E9
  "corrected: printed recurrence is false; removing 1 from m distinct parts leaves m or m-1 parts"]
theorem partitionCountAtMostDistinct_recurrence {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (partitionCountAtMostDistinct m n : ℤ) =
      partitionCountAtMostDistinct (m - 1) n + partitionCountAtMostDistinct m (n - m) -
        if 2 ≤ m then (partitionCountAtMostDistinct (m - 2) (n - m) : ℤ) else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 := r26a_atMost_succ k n
  have h2 := r26a_atMost_succ k (n - (k + 1))
  have h3 := card_distinct_card_eq_recurrence hm hmn
  simp only [Nat.add_sub_cancel] at h3 ⊢
  rcases k with _ | k
  · have h4 := r26a_atMost_zero (n - 1)
    simp only [zero_add] at h1 h2 h3 h4 ⊢
    norm_num
    push_cast [h1, h2, h3, h4]
    ring
  · have h4 := r26a_atMost_succ k (n - (k + 1 + 1))
    have h2le : 2 ≤ k + 1 + 1 := by omega
    simp only [h2le, ↓reduceIte, show k + 1 + 1 - 2 = k by omega]
    push_cast [h1, h2, h3, h4]
    ring

/-- (26.10.10): `p(𝒟k, n) = ∑_m p_m(n - km²/2 - m + km/2)` over the `m ≥ 0` with nonnegative
argument; the argument is `n - k·m(m-1)/2 - m`. -/
@[dlmf 26.10.E10]
theorem partitionCountDiff_eq_sum (k n : ℕ) :
    partitionCountDiff k n =
      ∑ m ∈ range (n + 1) with k * m.choose 2 + m ≤ n,
        partitionCountAtMostParts m (n - (k * m.choose 2 + m)) :=
  s26a_partitionCountDiff_eq_sum k n

/-- (26.10.11): `n p(∈ S, n) = ∑_{t=1}^n p(∈ S, n - t) ∑_{j ∣ t, j ∈ S} j` (stated multiplied
by `n`). -/
@[dlmf 26.10.E11]
theorem partitionCountIn_recurrence (S : Set ℕ) [DecidablePred (· ∈ S)] (n : ℕ) :
    n * partitionCountIn S n =
      ∑ t ∈ Icc 1 n, partitionCountIn S (n - t) * ∑ j ∈ t.divisors with j ∈ S, j :=
  r26a_card_restricted_recurrence (· ∈ S) n

end DLMF.Combinatorics
end
end
