/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.Stirling.RecurrencesAndIdentities

/-!
# Stirling asymptotics and cycle interpretations

Asymptotic formulas and permutation-cycle counting interpretations of Stirling numbers.

Source references and common attribution are retained in
`DLMF.Combinatorics.Stirling`.
-/

@[expose] public section

open Finset Polynomial Filter Topology Asymptotics

noncomputable section

namespace DLMF.Combinatorics

/-! ### Asymptotic approximations (§26.8(vii)) -/

/-- DLMF 26.8.40: `s(n+1, k+1) ~ (-1)^{n-k} (n!/k!) (γ + ln n)^k` as `n → ∞`, uniformly for
`k = o(ln n)`: stated for every sequence `k = k(n)` with `k(n) = o(ln n)`. -/
@[dlmf 26.8.E40]
theorem tendsto_signedStirlingFirst_div (k : ℕ → ℕ)
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => Real.log n) :
    Tendsto (fun n : ℕ => (signedStirlingFirst (n + 1) (k n + 1) : ℝ) /
        ((-1) ^ (n - k n) * n.factorial / (k n).factorial *
          (Real.eulerMascheroniConstant + Real.log n) ^ (k n))) atTop (𝓝 1) := by
  sorry

/-- Faulhaber asymptotics: `∑_{j<K} j^p ~ K^{p+1}/(p+1)`. -/
lemma q26a_sum_range_pow_isEquivalent (p : ℕ) :
    (fun K : ℕ => ∑ j ∈ range K, (j : ℝ) ^ p) ~[atTop] fun K => (K : ℝ) ^ (p + 1) / (p + 1) := by
  apply isEquivalent_of_tendsto_one
  have hval : ∀ K : ℕ, 0 < K → (∑ j ∈ range K, (j : ℝ) ^ p) / ((K : ℝ) ^ (p + 1) / (p + 1)) =
      ∑ i ∈ range (p + 1), (bernoulli i : ℝ) * ((p + 1).choose i) * ((K : ℝ)⁻¹) ^ i := by
    intro K hK
    have h := congrArg (Rat.cast : ℚ → ℝ) (sum_range_pow K p)
    push_cast at h
    rw [h, div_div_eq_mul_div, sum_mul, sum_div]
    refine sum_congr rfl fun i hi => ?_
    have hi : i ≤ p + 1 := by have := mem_range.mp hi; omega
    have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    rw [inv_pow, show (K : ℝ) ^ (p + 1) = (K : ℝ) ^ (p + 1 - i) * (K : ℝ) ^ i by
      rw [← pow_add, Nat.sub_add_cancel hi]]
    have : (K : ℝ) ^ i ≠ 0 := pow_ne_zero _ hK'
    have : (K : ℝ) ^ (p + 1 - i) ≠ 0 := pow_ne_zero _ hK'
    field_simp
  have hlim : Tendsto (fun K : ℕ => ∑ i ∈ range (p + 1), (bernoulli i : ℝ) * ((p + 1).choose i) *
      ((K : ℝ)⁻¹) ^ i) atTop (𝓝 (∑ i ∈ range (p + 1), (bernoulli i : ℝ) * ((p + 1).choose i) *
        (0 : ℝ) ^ i)) := by
    apply tendsto_finsetSum
    intro i _
    exact ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).pow i).const_mul _
  rw [sum_eq_single 0 (fun i _ hi => by simp [zero_pow hi]) (by simp)] at hlim
  simp only [bernoulli_zero, Rat.cast_one, Nat.choose_zero_right, Nat.cast_one, pow_zero,
    mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK
  rw [Pi.div_apply, hval K hK]

/-- Summing asymptotic equivalents of a nonnegative divergent comparison sequence. -/
lemma q26a_sum_range_isEquivalent {u v : ℕ → ℝ} (h : u ~[atTop] v) (hv : 0 ≤ v)
    (hs : Tendsto (fun n => ∑ i ∈ range n, v i) atTop atTop) :
    (fun n => ∑ i ∈ range n, u i) ~[atTop] fun n => ∑ i ∈ range n, v i := by
  have := h.isLittleO.sum_range hv hs
  refine IsLittleO.isEquivalent ?_
  convert this using 1
  ext n; simp [sum_sub_distrib]

/-- Unsigned form of DLMF 26.8.41: `c(n+k, k) ~ k^{2n}/(2ⁿ n!)`. -/
lemma q26a_stirlingFirst_add_isEquivalent (n : ℕ) :
    (fun k : ℕ => (Nat.stirlingFirst (n + k) k : ℝ)) ~[atTop]
      fun k => (k : ℝ) ^ (2 * n) / (2 ^ n * n.factorial) := by
  induction n with
  | zero =>
    simp only [zero_add, Nat.stirlingFirst_self, Nat.cast_one, mul_zero, pow_zero,
      Nat.factorial_zero, mul_one, div_one]
    exact IsEquivalent.refl
  | succ n ih =>
    -- telescoping: `c(n+1+K, K) = ∑_{j<K} (n+j+1) c(n+j+1, j+1)`
    have htel : ∀ K, (Nat.stirlingFirst (n + 1 + K) K : ℝ) =
        ∑ j ∈ range K, ((n + j + 1 : ℕ) : ℝ) * Nat.stirlingFirst (n + (j + 1)) (j + 1) := by
      intro K
      induction K with
      | zero => simp [Nat.stirlingFirst_succ_zero]
      | succ K ihK =>
        rw [sum_range_succ, ← ihK, show n + 1 + (K + 1) = (n + K + 1) + 1 by ring,
          Nat.stirlingFirst_succ_succ, show n + K + 1 = n + 1 + K by ring,
          show n + (K + 1) = n + K + 1 by ring, show n + 1 + K = n + K + 1 by ring]
        push_cast; ring
    set c : ℝ := 1 / (2 ^ n * n.factorial) with hc
    have hcpos : 0 < c := by positivity
    have hu :
        (fun j : ℕ => ((n + j + 1 : ℕ) : ℝ) * Nat.stirlingFirst (n + (j + 1)) (j + 1)) ~[atTop]
        fun j : ℕ => c * (j : ℝ) ^ (2 * n + 1) := by
      have h1 : (fun j : ℕ => ((n + j + 1 : ℕ) : ℝ)) ~[atTop] fun j : ℕ => (j : ℝ) := by
        apply isEquivalent_of_tendsto_one
        have : Tendsto (fun j : ℕ => 1 + ((n + 1 : ℝ)) * (j : ℝ)⁻¹) atTop (𝓝 (1 + (n + 1) * 0)) :=
          tendsto_const_nhds.add
            ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul _)
        rw [mul_zero, add_zero] at this
        refine this.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with j hj
        have : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
        simp only [Pi.div_apply]; push_cast; field_simp; ring
      have h2 : (fun j : ℕ => (Nat.stirlingFirst (n + (j + 1)) (j + 1) : ℝ)) ~[atTop]
          fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (2 * n) / (2 ^ n * n.factorial) :=
        ih.comp_tendsto (tendsto_add_atTop_nat 1)
      have h3 : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (2 * n) / (2 ^ n * n.factorial)) ~[atTop]
          fun j : ℕ => c * (j : ℝ) ^ (2 * n) := by
        have h4 : (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) ~[atTop] fun j : ℕ => (j : ℝ) := by
          have := h1
          apply isEquivalent_of_tendsto_one
          have : Tendsto (fun j : ℕ => 1 + (j : ℝ)⁻¹) atTop (𝓝 (1 + 0)) :=
            tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
          rw [add_zero] at this
          refine this.congr' ?_
          filter_upwards [eventually_gt_atTop 0] with j hj
          have : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
          simp only [Pi.div_apply]; push_cast; field_simp
        have := (h4.pow (2 * n)).mul (IsEquivalent.refl (u := fun _ : ℕ => c))
        convert this using 1
        · ext j; simp [hc, div_eq_mul_inv]
        · ext j; simp [mul_comm]
      have := h1.mul (h2.trans h3)
      convert this using 1
      ext j; simp only [Pi.mul_apply]; ring
    have hp : (fun K : ℕ => ∑ j ∈ range K, c * (j : ℝ) ^ (2 * n + 1)) ~[atTop]
        fun K : ℕ => c * ((K : ℝ) ^ (2 * n + 1 + 1) / (((2 * n + 1 : ℕ) : ℝ) + 1)) := by
      have := (IsEquivalent.refl (u := fun _ : ℕ => c)).mul
        (q26a_sum_range_pow_isEquivalent (2 * n + 1))
      convert this using 1
      ext K; simp [mul_sum]
    have hdiv : Tendsto
        (fun K : ℕ => c * ((K : ℝ) ^ (2 * n + 1 + 1) / (((2 * n + 1 : ℕ) : ℝ) + 1))) atTop
        atTop := by
      apply Tendsto.const_mul_atTop hcpos
      apply Tendsto.atTop_div_const (by positivity)
      exact (tendsto_pow_atTop (by omega)).comp tendsto_natCast_atTop_atTop
    have hsum := q26a_sum_range_isEquivalent hu (fun j => by positivity) (by
      exact hp.symm.tendsto_atTop hdiv)
    have hsum' : (fun K : ℕ => ∑ j ∈ range K, c * (j : ℝ) ^ (2 * n + 1)) ~[atTop]
        fun K : ℕ => c * ((K : ℝ) ^ (2 * n + 1 + 1) / (((2 * n + 1 : ℕ) : ℝ) + 1)) := hp
    have := hsum.trans hsum'
    convert this using 1
    · ext K; exact htel K
    · ext K; rw [hc, Nat.factorial_succ]; push_cast; field_simp; ring_nf

/-- DLMF 26.8.41: `s(n+k, k) ~ (-1)ⁿ k^{2n} / (2ⁿ n!)` as `k → ∞`, `n` fixed. -/
@[dlmf 26.8.E41]
theorem signedStirlingFirst_add_isEquivalent (n : ℕ) :
    (fun k : ℕ => (signedStirlingFirst (n + k) k : ℝ)) ~[atTop]
      fun k => (-1) ^ n / (2 ^ n * n.factorial) * (k : ℝ) ^ (2 * n) := by
  have h := (IsEquivalent.refl (u := fun _ : ℕ => (-1 : ℝ) ^ n)).mul
    (q26a_stirlingFirst_add_isEquivalent n)
  convert h using 1
  · ext k; simp [signedStirlingFirst]
  · ext k; simp only [Pi.mul_apply]; ring

/-- DLMF 26.8.42: `S(n, k) ~ kⁿ / k!` as `n → ∞`, `k` fixed. -/
@[dlmf 26.8.E42]
theorem stirlingSecond_isEquivalent (k : ℕ) :
    (fun n : ℕ => (Nat.stirlingSecond n k : ℝ)) ~[atTop]
      fun n => (k : ℝ) ^ n / k.factorial := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine IsEquivalent.congr_left IsEquivalent.refl ?_
    filter_upwards with n
    rcases n with _ | n <;> simp
  apply isEquivalent_of_tendsto_one
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : ∀ n, (Nat.stirlingSecond n k : ℝ) / ((k : ℝ) ^ n / k.factorial) =
      ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * ((j : ℝ) / k) ^ n := by
    intro n
    have := congrArg (Rat.cast : ℚ → ℝ) (q26a_sum_alt_choose_pow n k)
    push_cast at this
    simp_rw [div_pow, ← mul_div_assoc, ← sum_div, this]
    have : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  simp_rw [Pi.div_def, hc]
  have hlim : ∀ j ∈ range (k + 1), Tendsto (fun n : ℕ => (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) *
      ((j : ℝ) / k) ^ n) atTop (𝓝 (if j = k then 1 else 0)) := by
    intro j hj
    have hj : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    split_ifs with hjk
    · subst hjk
      simp [div_self hkR.ne']
    · have hlt : (j : ℝ) / k < 1 := by
        rw [div_lt_one hkR]; exact_mod_cast lt_of_le_of_ne hj hjk
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt).const_mul
        ((-1 : ℝ) ^ (k - j) * (k.choose j : ℝ))
      simpa using this
  have := tendsto_finsetSum _ hlim
  rw [Finset.sum_ite_eq'] at this
  simpa using this

/-- DLMF 26.8.43: `S(n+k, k) ~ k^{2n} / (2ⁿ n!)` as `k → ∞`, uniformly for `n = o(k^{1/2})`:
stated for every sequence `n = n(k)` with `n(k) = o(√k)`. -/
@[dlmf 26.8.E43]
theorem tendsto_stirlingSecond_add_div (n : ℕ → ℕ)
    (hn : (fun k => (n k : ℝ)) =o[atTop] fun k => Real.sqrt k) :
    Tendsto (fun k : ℕ => (Nat.stirlingSecond (n k + k) k : ℝ) /
        ((k : ℝ) ^ (2 * n k) / (2 ^ (n k) * (n k).factorial))) atTop (𝓝 1) := by
  sorry

/-! ### Combinatorial interpretations (§26.8(i)) -/

section CycleCount

open Equiv Equiv.Perm

/-- A relation that is an equivalence and relates every point to its image contains `SameCycle`. -/
lemma q26a_sameCycle_le {α : Type*} {f : Perm α} {R : α → α → Prop} (hR : Equivalence R)
    (hf : ∀ x, R x (f x)) {x y : α} (h : SameCycle f x y) : R x y := by
  obtain ⟨i, rfl⟩ := h
  induction i using Int.induction_on with
  | zero => simpa using hR.refl x
  | succ i ih =>
    rw [add_comm, zpow_add, zpow_one, Perm.mul_apply]
    exact hR.trans ih (hf _)
  | pred i ih =>
    have h1 := hf ((f ^ (-(i : ℤ) - 1)) x)
    rw [← Perm.mul_apply, ← zpow_one_add, show (1 + (-(i:ℤ) - 1)) = -i by ring] at h1
    exact hR.trans ih (hR.symm h1)

/-- The cycle maxima of a permutation. -/
def q26a_cycleMax {α : Type*} [Fintype α] [LinearOrder α] (σ : Perm α) : Finset α :=
  {a | ∀ b, SameCycle σ a b → b ≤ a}

/-- Inserting `0` into a permutation of `Fin n` (via `decomposeFin`) does not change which
nonzero points lie in a common cycle. -/
lemma q26a_sameCycle_succ {n : ℕ} (p : Fin (n + 1)) (τ : Perm (Fin n)) (x y : Fin n) :
    SameCycle (decomposeFin.symm (p, τ)) x.succ y.succ ↔ SameCycle τ x y := by
  set σ := decomposeFin.symm (p, τ)
  constructor
  · intro h
    let g : Fin (n + 1) → Fin (n + 1) := fun a => if a = 0 then p else a
    let R : Fin (n + 1) → Fin (n + 1) → Prop := fun a b =>
      g a = g b ∨ ∃ x y, g a = Fin.succ x ∧ g b = Fin.succ y ∧ SameCycle τ x y
    have hR : Equivalence R := by
      refine ⟨fun a => Or.inl rfl, ?_, ?_⟩
      · rintro a b (h | ⟨x, y, hx, hy, h⟩)
        · exact Or.inl h.symm
        · exact Or.inr ⟨y, x, hy, hx, h.symm⟩
      · rintro a b c (h | ⟨x, y, hx, hy, h⟩) (h' | ⟨x', y', hx', hy', h'⟩)
        · exact Or.inl (h.trans h')
        · exact Or.inr ⟨x', y', h ▸ hx', hy', h'⟩
        · exact Or.inr ⟨x, y, hx, h' ▸ hy, h⟩
        · rw [hy, Fin.succ_inj] at hx'
          subst hx'
          exact Or.inr ⟨x, y', hx, hy', h.trans h'⟩
    have hstep : ∀ a, R a (σ a) := by
      intro a
      refine Fin.cases ?_ (fun x => ?_) a
      · left
        by_cases hp : p = 0 <;> simp [σ, g, hp]
      · simp only [σ, decomposeFin_symm_apply_succ]
        by_cases hx : (τ x).succ = p
        · right
          rw [← hx, swap_apply_right]
          exact ⟨x, τ x, by simp [g], by simp [g, hx], (SameCycle.refl _ _).apply_right⟩
        · right
          rw [swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hx]
          exact ⟨x, τ x, by simp [g], by simp [g], (SameCycle.refl _ _).apply_right⟩
    rcases q26a_sameCycle_le hR hstep h with h | ⟨x', y', hx, hy, h⟩
    · simp only [g, Fin.succ_ne_zero, ite_false, Fin.succ_inj] at h
      subst h; exact SameCycle.refl _ _
    · simp only [g, Fin.succ_ne_zero, ite_false, Fin.succ_inj] at hx hy
      subst hx hy; exact h
  · intro h
    let R : Fin n → Fin n → Prop := fun a b => SameCycle σ a.succ b.succ
    have hR : Equivalence R :=
      ⟨fun a => SameCycle.refl _ _, fun h => h.symm, fun h h' => h.trans h'⟩
    refine q26a_sameCycle_le (R := R) hR (fun a => ?_) h
    simp only [R]
    by_cases hx : (τ a).succ = p
    · have h1 : σ a.succ = 0 := by simp [σ, ← hx]
      have h2 : σ (σ a.succ) = (τ a).succ := by rw [h1]; simp [σ, hx]
      rw [← h2]; exact (SameCycle.refl _ _).apply_right.apply_right
    · have h1 : σ a.succ = (τ a).succ := by
        simp only [σ, decomposeFin_symm_apply_succ]
        exact swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hx
      rw [← h1]; exact (SameCycle.refl _ _).apply_right

/-- Inserting `0` adds a cycle exactly when `0` becomes a fixed point. -/
lemma q26a_card_cycleMax_decomposeFin {n : ℕ} (p : Fin (n + 1)) (τ : Perm (Fin n)) :
    #(q26a_cycleMax (decomposeFin.symm (p, τ))) = #(q26a_cycleMax τ) + if p = 0 then 1 else 0 := by
  simp only [q26a_cycleMax, card_filter, Fin.sum_univ_succ]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    apply propext
    constructor
    · intro h y hy
      exact Fin.succ_le_succ_iff.mp (h _ ((q26a_sameCycle_succ p τ x y).2 hy))
    · intro h b hb
      refine Fin.cases (fun _ => Fin.zero_le _) (fun y hy => ?_) b hb
      exact Fin.succ_le_succ_iff.mpr (h y ((q26a_sameCycle_succ p τ x y).1 hy))
  · by_cases hp : p = 0
    · subst hp
      simp only [ite_true]
      split_ifs with hc
      · rfl
      refine absurd (fun b hb => ?_) hc
      have : Function.IsFixedPt (decomposeFin.symm ((0 : Fin (n+1)), τ)) 0 := by
        simp [Function.IsFixedPt]
      exact (hb.eq_of_left this).symm.le
    · simp only [hp, ite_false]
      split_ifs with h
      swap; · rfl
      exfalso
      have hs : SameCycle (decomposeFin.symm (p, τ)) 0 p := by
        have := (SameCycle.refl (decomposeFin.symm (p, τ)) 0).apply_right
        simpa using this
      exact hp (le_antisymm (h p hs) (Fin.zero_le _))
/-- The number of cycles (fixed points included) equals the number of cycle maxima. -/
lemma q26a_card_parts_partition {α : Type*} [Fintype α] [LinearOrder α] (σ : Perm α) :
    Multiset.card σ.partition.parts = #(q26a_cycleMax σ) := by
  rw [parts_partition, Multiset.card_add, Multiset.card_replicate, cycleType_def,
    Multiset.card_map]
  rw [← card_filter_add_card_filter_not (s := q26a_cycleMax σ) (fun x => x ∈ σ.support)]
  congr 1
  · change #σ.cycleFactorsFinset = _
    symm
    apply Finset.card_bij (fun a _ => σ.cycleOf a)
    · intro a ha
      simp only [mem_filter] at ha
      exact cycleOf_mem_cycleFactorsFinset_iff.2 ha.2
    · intro a ha b hb hab
      simp only [mem_filter, q26a_cycleMax, mem_univ, true_and] at ha hb
      have : SameCycle σ a b := by
        have hb' : b ∈ (σ.cycleOf b).support :=
          (mem_support_cycleOf_iff.2 ⟨SameCycle.refl _ _, hb.2⟩)
        rw [← hab] at hb'
        exact (mem_support_cycleOf_iff.1 hb').1
      exact le_antisymm (hb.1 a this.symm) (ha.1 b this)
    · intro c hc
      have hne : c.support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty_iff]
        exact (mem_cycleFactorsFinset_iff.1 hc).1.ne_one
      set m := c.support.max' hne
      have hm : m ∈ c.support := c.support.max'_mem hne
      have hcm := cycle_is_cycleOf hm hc
      have hms : m ∈ σ.support := mem_cycleFactorsFinset_support_le hc hm
      refine ⟨m, ?_, hcm.symm⟩
      simp only [mem_filter, q26a_cycleMax, mem_univ, true_and]
      refine ⟨fun b hb => ?_, hms⟩
      apply c.support.le_max'
      rw [hcm]
      exact mem_support_cycleOf_iff.2 ⟨hb, hms⟩
  · have : (q26a_cycleMax σ).filter (fun x => x ∉ σ.support) = univ \ σ.support := by
      ext a
      simp only [mem_filter, q26a_cycleMax, mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨fun b hb => (hb.eq_of_left (notMem_support.1 h)).symm.le, h⟩
    rw [this, card_sdiff_of_subset (subset_univ _), card_univ]

/-- Permutations of `Fin n` with `k` cycle maxima are counted by `Nat.stirlingFirst n k`. -/
lemma q26a_card_cycleMax_eq (n k : ℕ) :
    #{σ : Perm (Fin n) | #(q26a_cycleMax σ) = k} = Nat.stirlingFirst n k := by
  induction n generalizing k with
  | zero =>
    rcases k with _ | k
    · simp only [Nat.stirlingFirst_zero]
      rw [Finset.card_eq_one]
      refine ⟨1, ?_⟩
      ext σ
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro _; exact Subsingleton.elim _ _
      · intro _; simp [q26a_cycleMax]
    · simp only [Nat.stirlingFirst_zero_succ, card_eq_zero, filter_eq_empty_iff]
      intro σ _
      simp [q26a_cycleMax]
  | succ n ih =>
    have key : ∀ m, #{σ : Perm (Fin (n + 1)) | #(q26a_cycleMax σ) = m} =
        #{τ : Perm (Fin n) | #(q26a_cycleMax τ) + 1 = m} +
          n * #{τ : Perm (Fin n) | #(q26a_cycleMax τ) = m} := by
      intro m
      simp only [card_filter]
      rw [← Equiv.sum_comp decomposeFin.symm, Fintype.sum_prod_type, Fin.sum_univ_succ]
      simp only [q26a_card_cycleMax_decomposeFin, Fin.succ_ne_zero, ite_true, ite_false, add_zero,
        sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    rcases k with _ | k
    · rw [Nat.stirlingFirst_succ_zero, key, ih]
      rcases n with _ | n <;> simp
    · rw [key, Nat.stirlingFirst_succ_succ, ← ih, ← ih]
      simp only [Nat.add_right_cancel_iff]
      ring

end CycleCount

/-- DLMF §26.8(i): `|s(n, k)|` (Mathlib's `Nat.stirlingFirst n k`) is the number of
permutations of `{1, …, n}` with exactly `k` cycles (fixed points counted as cycles, i.e. the
number of parts of the cycle-type partition `σ.partition`). -/
@[dlmf 26.8.i]
theorem card_perm_numCycles (n k : ℕ) :
    #{σ : Equiv.Perm (Fin n) | σ.partition.parts.card = k} = Nat.stirlingFirst n k := by
  simp only [q26a_card_parts_partition]
  exact q26a_card_cycleMax_eq n k

/-- DLMF §26.8(i): `s(n, k) = (-1)^{n-k}` times the number of permutations of `{1, …, n}`
with exactly `k` cycles. -/
@[dlmf 26.8.i]
theorem signedStirlingFirst_eq_card (n k : ℕ) :
    signedStirlingFirst n k =
      (-1) ^ (n - k) * (#{σ : Equiv.Perm (Fin n) | σ.partition.parts.card = k} : ℤ) := by
  rw [card_perm_numCycles, signedStirlingFirst]

/-- DLMF §26.8(i): `S(n, k)` is the number of partitions of `{1, …, n}` into exactly `k`
nonempty subsets. -/
@[dlmf 26.8.i]
theorem card_finpartition_eq_stirlingSecond (n k : ℕ) :
    #{P : Finpartition (univ : Finset (Fin n)) | P.parts.card = k} = Nat.stirlingSecond n k := by
  -- each finpartition with `k` parts comes from `k!` surjections `Fin n → Fin k`
  have h := r26a_card_surjective_filter (α := Fin n) k (fun _ => True)
  simp only [and_true] at h
  rw [q26b_card_surjective_fin] at h
  exact (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k) h).symm

end DLMF.Combinatorics

end
end
