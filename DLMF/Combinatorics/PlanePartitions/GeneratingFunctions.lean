/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Combinatorics.PlanePartitions.BoxFormula

/-!
# Plane partition recurrences and generating functions

The plane partition recurrence and MacMahon infinite generating function, with convergence
stated explicitly.

Source references and common attribution are retained in
`DLMF.Combinatorics.PlanePartitions`.
-/

@[expose] public section

noncomputable section

open Finset Filter Asymptotics

namespace DLMF.Combinatorics

/-! ### The recurrence (26.12.25)

From the box formula for `B(n, n, n)` modulo `X^(n+1)`, `G · ∏_{m ≤ n} (1 - X^m)^m ≡ 1`, where
`G = ∑ X^{|π|}` has the coefficients `pp(k)`, `k ≤ n`; applying the Euler operator `θ = X d/dX`
gives `θ G ≡ G · ∑_{m ≤ n} m² ∑_{l ≤ n} X^{ml}`. -/

section Recurrence

open Polynomial

/-- Truncation ideal `(X^(N+1))` of `ℤ[X]`. -/
abbrev s26b_I (N : ℕ) : Ideal ℤ[X] := Ideal.span {(X : ℤ[X]) ^ (N + 1)}

/-- The quotient map modulo `X^(N+1)`. -/
abbrev s26b_mk (N : ℕ) : ℤ[X] →+* ℤ[X] ⧸ s26b_I N := Ideal.Quotient.mk (s26b_I N)

/-- `X^e` vanishes modulo `X^(N+1)` for `e ≥ N + 1`. -/
lemma s26b_mk_X_pow {N e : ℕ} (he : N + 1 ≤ e) : s26b_mk N ((X : ℤ[X]) ^ e) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact pow_dvd_pow _ he

/-- Congruent polynomials modulo `X^(N+1)` share their coefficients up to `N`. -/
lemma s26b_coeff_eq_of_mk_eq {N : ℕ} {A B : ℤ[X]} (h : s26b_mk N A = s26b_mk N B) {n : ℕ}
    (hn : n ≤ N) : A.coeff n = B.coeff n := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨C, hC⟩ := h
  have := congrArg (fun p => p.coeff n) hC
  simp only [coeff_sub, coeff_X_pow_mul'] at this
  split_ifs at this with hh
  · omega
  · omega

/-- The Euler operator `θ = X d/dX`. -/
def s26b_θ (A : ℤ[X]) : ℤ[X] := X * derivative A

/-- `θ` is a derivation. -/
lemma s26b_θ_mul (A B : ℤ[X]) : s26b_θ (A * B) = s26b_θ A * B + A * s26b_θ B := by
  simp only [s26b_θ, derivative_mul]; ring

/-- `θ` preserves congruence modulo `X^(N+1)`. -/
lemma s26b_mk_θ {N : ℕ} {A B : ℤ[X]} (h : s26b_mk N A = s26b_mk N B) :
    s26b_mk N (s26b_θ A) = s26b_mk N (s26b_θ B) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨(N + 1 : ℤ[X]) * C + X * derivative C, ?_⟩
  rw [s26b_θ, s26b_θ, ← mul_sub, ← derivative_sub, hC, derivative_mul, derivative_X_pow]
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, map_add, map_one, map_natCast]
  ring

/-- Logarithmic derivative of a product modulo `X^(N+1)`. -/
lemma s26b_mk_θ_prod {N : ℕ} {ι : Type*} (s : Finset ι) (g c : ι → ℤ[X])
    (h : ∀ i ∈ s, s26b_mk N (s26b_θ (g i)) = s26b_mk N (g i * c i)) :
    s26b_mk N (s26b_θ (∏ i ∈ s, g i)) = s26b_mk N ((∏ i ∈ s, g i) * ∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [s26b_θ]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, s26b_θ_mul, map_add, map_mul, map_mul,
      h a (mem_insert_self a s), ih fun i hi => h i (mem_insert_of_mem hi)]
    simp only [map_mul, map_add]
    ring

/-- A plane partition lies in the cube of side `|π|`. -/
lemma s26b_subset_planeBox_card {π : Finset (ℕ × ℕ × ℕ)} (hπ : IsPlanePartition π) :
    π ⊆ planeBox #π #π #π := by
  rintro ⟨h, j, k⟩ hx
  obtain ⟨h1, j1, k1, -⟩ := hπ _ hx
  have c1 : (Icc 1 h).image (fun i => (i, 1, 1)) ⊆ π := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    rw [mem_Icc] at hi
    exact s26b_down hπ hx hi.1 hi.2 le_rfl j1 le_rfl k1
  have c2 : (Icc 1 j).image (fun i => (1, i, 1)) ⊆ π := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    rw [mem_Icc] at hi
    exact s26b_down hπ hx le_rfl h1 hi.1 hi.2 le_rfl k1
  have c3 : (Icc 1 k).image (fun i => (1, 1, i)) ⊆ π := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    rw [mem_Icc] at hi
    exact s26b_down hπ hx le_rfl h1 le_rfl j1 hi.1 hi.2
  have e1 := card_le_card c1
  have e2 := card_le_card c2
  have e3 := card_le_card c3
  rw [card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).1)] at e1
  rw [card_image_of_injective _ (fun a b hab => (Prod.mk.inj (Prod.mk.inj hab).2).1)] at e2
  rw [card_image_of_injective _ (fun a b hab => (Prod.mk.inj (Prod.mk.inj hab).2).2)] at e3
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at e1 e2 e3
  exact s26b_mem_planeBox.mpr ⟨h1, e1, j1, e2, k1, e3⟩

/-- The box generating polynomial has `pp(n)` as its coefficients up to the side length. -/
lemma s26b_coeff_boxPoly {N n : ℕ} (hn : n ≤ N) :
    (∑ π ∈ planePartitionsIn N N N, (X : ℤ[X]) ^ #π).coeff n = planePartitionCount n := by
  simp only [finsetSum_coeff, coeff_X_pow]
  rw [sum_boole, planePartitionCount]
  congr 2
  ext π
  simp only [mem_filter, s26b_mem_planePartitionsIn, mem_powerset]
  constructor
  · rintro ⟨⟨_, hπ⟩, rfl⟩
    exact ⟨s26b_subset_planeBox_card hπ, hπ, rfl⟩
  · rintro ⟨hsub, hπ, rfl⟩
    refine ⟨⟨hsub.trans fun x hx => ?_, hπ⟩, rfl⟩
    rw [planeBox, mem_product, mem_product, mem_Icc, mem_Icc, mem_Icc] at hx ⊢
    omega

/-- Regrouping the box denominator modulo `X^(N+1)`. -/
lemma s26b_mk_denom (N : ℕ) :
    s26b_mk N (∏ h ∈ Icc 1 N, ∏ k ∈ Icc 1 N, (1 - (X : ℤ[X]) ^ (h + k - 1))) =
      s26b_mk N (∏ m ∈ Icc 1 N, (1 - (X : ℤ[X]) ^ m) ^ m) := by
  set f : ℕ → ℤ[X] ⧸ s26b_I N := fun m => s26b_mk N (1 - X ^ m) with hf
  have hf1 : ∀ m, N + 1 ≤ m → f m = 1 := fun m hm => by
    simp only [hf, map_sub, map_one, s26b_mk_X_pow hm, sub_zero]
  simp only [map_prod, map_pow]
  change ∏ h ∈ Icc 1 N, ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ m ∈ Icc 1 N, f m ^ m
  have hin : ∀ h ∈ Icc 1 N, ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ m ∈ Icc h N, f m := by
    intro h hh
    rw [mem_Icc] at hh
    have : ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ k ∈ Icc 1 (N + 1 - h), f (h + k - 1) := by
      symm
      refine prod_subset (fun k hk => by simp only [mem_Icc] at hk ⊢; omega) fun k hk hk' => ?_
      simp only [mem_Icc] at hk hk'
      exact hf1 _ (by omega)
    rw [this]
    refine prod_nbij' (fun k => h + k - 1) (fun m => m + 1 - h) ?_ ?_ ?_ ?_ fun _ _ => rfl
    · intro k hk; simp at hk ⊢; omega
    · intro m hm; simp at hm ⊢; omega
    · intro k hk; simp at hk; omega
    · intro m hm; simp at hm; omega
  rw [prod_congr rfl hin, prod_comm' (t' := Icc 1 N) (s' := fun m => Icc 1 m)]
  · refine prod_congr rfl fun m _ => ?_
    rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  · intro h m
    simp only [mem_Icc]
    omega

/-- The truncated divisor series `T_m = ∑_{l=1}^{N} X^{ml}`. -/
def s26b_T (N m : ℕ) : ℤ[X] := ∑ l ∈ range N, X ^ (m * (l + 1))

/-- `θ (1 - X^m)^m ≡ -(1 - X^m)^m m² T_m` modulo `X^(N+1)`. -/
lemma s26b_mk_θ_factor {N m : ℕ} (hm : 1 ≤ m) :
    s26b_mk N (s26b_θ ((1 - (X : ℤ[X]) ^ m) ^ m)) =
      s26b_mk N ((1 - (X : ℤ[X]) ^ m) ^ m * (-(C ((m : ℤ) ^ 2)) * s26b_T N m)) := by
  have htel : (1 - (X : ℤ[X]) ^ m) * s26b_T N m = X ^ m - X ^ (m * (N + 1)) := by
    rw [s26b_T, mul_sum]
    have := sum_range_sub (fun l => -(X : ℤ[X]) ^ (m * (l + 1))) N
    simp only [neg_sub_neg] at this
    rw [show ∑ l ∈ range N, (1 - (X : ℤ[X]) ^ m) * X ^ (m * (l + 1)) =
        ∑ l ∈ range N, ((X : ℤ[X]) ^ (m * (l + 1)) - X ^ (m * (l + 1 + 1))) from
      sum_congr rfl fun l _ => by ring, this]
    ring
  have hz : s26b_mk N ((X : ℤ[X]) ^ (m * (N + 1))) = 0 :=
    s26b_mk_X_pow (by nlinarith)
  have hθ : s26b_θ ((1 - (X : ℤ[X]) ^ m) ^ m) =
      -(C ((m : ℤ) ^ 2)) * (1 - X ^ m) ^ (m - 1) * X ^ m := by
    rw [s26b_θ, derivative_pow, derivative_sub, derivative_one, derivative_X_pow]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, map_pow, map_natCast]
    ring
  rw [hθ]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [show (1 - (X : ℤ[X]) ^ (m' + 1)) ^ (m' + 1) * (-(C (((m' + 1 : ℕ) : ℤ) ^ 2)) *
      s26b_T N (m' + 1)) = -(C (((m' + 1 : ℕ) : ℤ) ^ 2)) * (1 - X ^ (m' + 1)) ^ m' *
      ((1 - X ^ (m' + 1)) * s26b_T N (m' + 1)) by ring, htel]
  simp only [Nat.add_sub_cancel, map_mul, map_sub, hz, sub_zero]

/-- Coefficients of `∑_{m ≤ N} m² T_m` are `σ₂`. -/
lemma s26b_coeff_S {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) :
    (∑ m ∈ Icc 1 N, C ((m : ℤ) ^ 2) * s26b_T N m).coeff j = ArithmeticFunction.sigma 2 j := by
  simp only [finsetSum_coeff, coeff_C_mul, s26b_T, coeff_X_pow]
  rw [ArithmeticFunction.sigma_apply, Nat.cast_sum]
  have : ∀ m ∈ Icc 1 N, ((m : ℤ) ^ 2 * ∑ l ∈ range N, if j = m * (l + 1) then (1 : ℤ) else 0) =
      if m ∣ j then (m : ℤ) ^ 2 else 0 := by
    intro m hm
    rw [mem_Icc] at hm
    rw [sum_boole]
    split_ifs with hd
    · obtain ⟨c, rfl⟩ := hd
      have hc : 1 ≤ c := by rcases c with _ | c <;> simp_all
      have : (range N).filter (fun l => m * c = m * (l + 1)) = {c - 1} := by
        ext l
        simp only [mem_filter, mem_range, mem_singleton]
        constructor
        · rintro ⟨_, h⟩
          have := Nat.eq_of_mul_eq_mul_left (by omega) h
          omega
        · rintro rfl
          refine ⟨?_, by rw [Nat.sub_add_cancel hc]⟩
          have : c ≤ m * c := Nat.le_mul_of_pos_left c (by omega)
          omega
      rw [this, card_singleton]; simp
    · have : (range N).filter (fun l => j = m * (l + 1)) = ∅ := by
        ext l
        simp only [mem_filter, mem_range, notMem_empty, iff_false, not_and]
        intro _ h
        exact hd ⟨_, h⟩
      rw [this]; simp
  rw [sum_congr rfl this, ← sum_filter]
  push_cast
  refine sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [mem_filter, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨_, h⟩; exact ⟨h, by omega⟩
  · rintro ⟨h, _⟩
    have := Nat.le_of_dvd (by omega) h
    have : 0 < m := Nat.pos_of_dvd_of_pos h (by omega)
    omega

/-- The recurrence (26.12.25) (helper used before its statement). -/
lemma s26b_pp_recurrence (n : ℕ) :
    n * planePartitionCount n =
      ∑ j ∈ Icc 1 n, planePartitionCount (n - j) * ArithmeticFunction.sigma 2 j := by
  set G : ℤ[X] := ∑ π ∈ planePartitionsIn n n n, (X : ℤ[X]) ^ #π with hG
  set E : ℤ[X] := ∏ m ∈ Icc 1 n, (1 - (X : ℤ[X]) ^ m) ^ m with hE
  set S : ℤ[X] := ∑ m ∈ Icc 1 n, C ((m : ℤ) ^ 2) * s26b_T n m with hS
  -- `G E ≡ 1`
  have hGE : s26b_mk n (G * E) = s26b_mk n 1 := by
    have hb := congrArg (s26b_mk n) (s26b_box_poly n n n)
    rw [map_mul, s26b_mk_denom, ← map_mul] at hb
    rw [hb, map_prod, map_one]
    refine prod_eq_one fun h hh => ?_
    rw [map_prod]
    refine prod_eq_one fun k hk => ?_
    simp only [mem_Icc] at hh hk
    rw [map_sub, map_one, s26b_mk_X_pow (by omega), sub_zero]
  -- `θ E ≡ -E S`
  have hθE : s26b_mk n (s26b_θ E) = s26b_mk n (E * -S) := by
    rw [hE, s26b_mk_θ_prod _ _ (fun m : ℕ => -(C ((m : ℤ) ^ 2)) * s26b_T n m)
      (fun m hm => s26b_mk_θ_factor (mem_Icc.mp hm).1), hS, ← sum_neg_distrib]
    simp only [neg_mul]
  have hθ1 : s26b_mk n (s26b_θ (G * E)) = 0 := by
    rw [s26b_mk_θ hGE]; simp [s26b_θ]
  rw [s26b_θ_mul, map_add, map_mul, map_mul, hθE, map_mul, map_neg] at hθ1
  rw [map_mul, map_one] at hGE
  have key : s26b_mk n (s26b_θ G) = s26b_mk n (G * S) := by
    rw [map_mul]
    linear_combination (s26b_mk n G) * hθ1 +
      (s26b_mk n G * s26b_mk n S - s26b_mk n (s26b_θ G)) * hGE
  have hc := s26b_coeff_eq_of_mk_eq key (le_refl n)
  -- read off coefficient `n`
  have hl : (s26b_θ G).coeff n = n * planePartitionCount n := by
    rcases n with _ | m
    · simp [s26b_θ]
    · rw [s26b_θ, coeff_X_mul, coeff_derivative, s26b_coeff_boxPoly le_rfl]
      push_cast; ring
  have hr : (G * S).coeff n =
      ∑ j ∈ Icc 1 n, (planePartitionCount (n - j) * ArithmeticFunction.sigma 2 j : ℤ) := by
    have hS0 : S.coeff 0 = 0 := by
      rw [hS, finsetSum_coeff]
      refine sum_eq_zero fun m hm => ?_
      rw [coeff_C_mul, s26b_T, finsetSum_coeff, sum_eq_zero, mul_zero]
      intro l _
      simp only [mem_Icc] at hm
      have := Nat.mul_pos (by omega : 0 < m) (by omega : 0 < l + 1)
      rw [coeff_X_pow]
      split_ifs with h
      · omega
      · rfl
    rw [mul_comm, coeff_mul,
      Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => S.coeff i * G.coeff j), range_eq_Ico,
      sum_eq_sum_Ico_succ_bot (by omega), hS0, zero_mul, zero_add,
      show Ico (0 + 1) (n + 1) = Icc 1 n by ext; simp]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_Icc] at hj
    rw [s26b_coeff_S hj.1 hj.2, s26b_coeff_boxPoly (by omega)]
    ring
  have := hl.symm.trans (hc.trans hr)
  exact_mod_cast this

end Recurrence

/-! ### MacMahon's generating function (26.12.20)

`pp(n) ρⁿ` is bounded by the recurrence, so `∑ pp(n) qⁿ` converges for `|q| < 1`; it is the limit
of the box sums `∑_{π ⊆ B(N,N,N)} q^{|π|}`, which by (26.12.21) are
`∏_{h,j ≤ N} (1 - q^{h+j+N-1})/(1 - q^{h+j-1})`, and these tend to MacMahon's product. -/

section GenFun

open Filter Topology

/-- `σ₂(j) ≤ j³`. -/
lemma s26b_sigma_two_le (j : ℕ) : ArithmeticFunction.sigma 2 j ≤ j ^ 3 := by
  rw [ArithmeticFunction.sigma_apply]
  calc ∑ d ∈ j.divisors, d ^ 2 ≤ ∑ _d ∈ j.divisors, j ^ 2 :=
        sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) 2
    _ = #j.divisors * j ^ 2 := by rw [sum_const, smul_eq_mul]
    _ ≤ j * j ^ 2 := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self j)
    _ = j ^ 3 := by ring

/-- `pp(n) ρⁿ` is bounded for `0 < ρ < 1` (from the recurrence (26.12.25)). -/
lemma s26b_pp_bound {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, (planePartitionCount n : ℝ) * ρ ^ n ≤ B := by
  have hsum : Summable fun j : ℕ => ((j : ℝ) ^ 3 * ρ ^ j) :=
    summable_pow_mul_geometric_of_norm_lt_one 3
      (by rw [Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1)
  set K := ∑' j : ℕ, ((j : ℝ) ^ 3 * ρ ^ j) with hK
  have hpart : ∀ n, ∑ j ∈ Icc 1 n, (ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j ≤ K := by
    intro n
    calc ∑ j ∈ Icc 1 n, (ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j
        ≤ ∑ j ∈ Icc 1 n, ((j : ℝ) ^ 3 * ρ ^ j) := sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast s26b_sigma_two_le j) (by positivity)
      _ ≤ K := hsum.sum_le_tsum _ fun j _ => by positivity
  set K0 := ⌈K⌉₊
  set B := ∑ n ∈ range (K0 + 1), (planePartitionCount n : ℝ) * ρ ^ n
  have hB0 : 0 ≤ B := sum_nonneg fun n _ => by positivity
  refine ⟨B, hB0, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ K0
    · exact single_le_sum (f := fun n => (planePartitionCount n : ℝ) * ρ ^ n)
        (fun n _ => by positivity) (mem_range.mpr (by omega))
    · push Not at hn
      have hrec := s26b_pp_recurrence n
      have hrecR : (n : ℝ) * ((planePartitionCount n : ℝ) * ρ ^ n) =
          ∑ j ∈ Icc 1 n, ((planePartitionCount (n - j) : ℝ) * ρ ^ (n - j)) *
            ((ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j) := by
        rw [← mul_assoc]
        have : ((n * planePartitionCount n : ℕ) : ℝ) =
            ((∑ j ∈ Icc 1 n, planePartitionCount (n - j) * ArithmeticFunction.sigma 2 j : ℕ) :
              ℝ) := by rw [hrec]
        push_cast at this
        rw [this, sum_mul]
        refine sum_congr rfl fun j hj => ?_
        rw [mem_Icc] at hj
        rw [show ρ ^ n = ρ ^ (n - j) * ρ ^ j by rw [← pow_add, Nat.sub_add_cancel hj.2]]
        ring
      have hle : (n : ℝ) * ((planePartitionCount n : ℝ) * ρ ^ n) ≤ B * n := by
        rw [hrecR]
        calc ∑ j ∈ Icc 1 n, ((planePartitionCount (n - j) : ℝ) * ρ ^ (n - j)) *
              ((ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j)
            ≤ ∑ j ∈ Icc 1 n, B * ((ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j) := by
              refine sum_le_sum fun j hj => ?_
              rw [mem_Icc] at hj
              exact mul_le_mul_of_nonneg_right (ih _ (by omega)) (by positivity)
          _ = B * ∑ j ∈ Icc 1 n, (ArithmeticFunction.sigma 2 j : ℝ) * ρ ^ j := by
              rw [mul_sum]
          _ ≤ B * K := mul_le_mul_of_nonneg_left (hpart n) hB0
          _ ≤ B * n := by
              refine mul_le_mul_of_nonneg_left ?_ hB0
              have := Nat.le_ceil K
              have : (K0 : ℝ) < n := by exact_mod_cast hn
              linarith
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      nlinarith

/-- Summability of `pp(n) qⁿ` for `|q| < 1`. -/
lemma s26b_summable_pp {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n => ‖(planePartitionCount n : ℂ) * q ^ n‖ := by
  obtain ⟨ρ, hqρ, hρ1⟩ := exists_between hq
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg q) hqρ
  obtain ⟨B, hB0, hB⟩ := s26b_pp_bound hρ0 hρ1
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (div_nonneg (norm_nonneg q) hρ0.le)
      ((div_lt_one hρ0).mpr hqρ)).mul_left B)
  rw [norm_mul, norm_pow, Complex.norm_natCast, div_pow]
  have := hB n
  have hρn : 0 < ρ ^ n := pow_pos hρ0 n
  rw [mul_div_assoc', le_div_iff₀ hρn]
  calc (planePartitionCount n : ℝ) * ‖q‖ ^ n * ρ ^ n
      = ((planePartitionCount n : ℝ) * ρ ^ n) * ‖q‖ ^ n := by ring
    _ ≤ B * ‖q‖ ^ n := mul_le_mul_of_nonneg_right this (by positivity)

/-- `1 - qᵐ ≠ 0` for `|q| < 1`, `m > 0`. -/
lemma s26b_one_sub_pow_ne_zero {q : ℂ} (hq : ‖q‖ < 1) {m : ℕ} (hm : 0 < m) : 1 - q ^ m ≠ 0 := by
  intro h
  have : ‖q ^ m‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
  rw [norm_pow] at this
  have : ‖q‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg q) hq hm.ne'
  linarith

/-- MacMahon's product `∏ (1 - q^{k+1})^{-(k+1)}` converges, as an exponential of a sum. -/
lemma s26b_hasProd_macMahon {q : ℂ} (hq : ‖q‖ < 1) :
    ∃ A : ℂ, HasProd (fun k : ℕ => ((1 - q ^ (k + 1)) ^ (k + 1))⁻¹) (Complex.exp A) := by
  set a : ℕ → ℂ := fun k => -(((k + 1 : ℕ) : ℂ) * Complex.log (1 - q ^ (k + 1))) with ha
  have h0 : Summable fun n : ℕ => (n : ℝ) ^ 1 * ‖q‖ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖q‖) (by rw [norm_norm]; exact hq)
  have h1 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 1 * ‖q‖ ^ (n + 1) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ 1 * ‖q‖ ^ n) 1).mpr h0
  have hsg : Summable fun k : ℕ => (3 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ) ^ 1 * ‖q‖ ^ (k + 1)) :=
    h1.mul_left _
  have hev : ∀ᶠ k : ℕ in atTop, ‖q‖ ^ (k + 1) ≤ 1 / 2 := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).comp
      (tendsto_add_atTop_nat 1)
    exact (this.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hs : Summable a := by
    refine Summable.of_norm_bounded_eventually_nat hsg ?_
    filter_upwards [hev] with k hk
    rw [ha, norm_neg, norm_mul, Complex.norm_natCast, sub_eq_add_neg]
    have := Complex.norm_log_one_add_half_le_self (z := -q ^ (k + 1)) (by rwa [norm_neg, norm_pow])
    rw [norm_neg, norm_pow] at this
    rw [pow_one]
    nlinarith [norm_nonneg (Complex.log (1 + -q ^ (k + 1)))]
  refine ⟨∑' k, a k, ?_⟩
  have := hs.hasSum.cexp
  convert this using 1
  funext k
  simp only [Function.comp, ha, Complex.exp_neg, Complex.exp_nat_mul,
    Complex.exp_log (s26b_one_sub_pow_ne_zero hq (Nat.succ_pos k))]

/-- Products `∏ (1 - wᵢ)` over finite families with `∑ ‖wᵢ‖ → 0` tend to `1`. -/
lemma s26b_tendsto_prod_one_sub {ι : Type*} (s : ℕ → Finset ι) (w : ℕ → ι → ℂ)
    (hw : ∀ᶠ N in atTop, ∀ x ∈ s N, ‖w N x‖ ≤ 1 / 2)
    (hsum : Tendsto (fun N => ∑ x ∈ s N, ‖w N x‖) atTop (𝓝 0)) :
    Tendsto (fun N => ∏ x ∈ s N, (1 - w N x)) atTop (𝓝 1) := by
  have hL : Tendsto (fun N => ∑ x ∈ s N, Complex.log (1 + -w N x)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
      (by simpa using hsum.const_mul (3 / 2 : ℝ))
    filter_upwards [hw] with N hN
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun x hx => ?_
    have := Complex.norm_log_one_add_half_le_self (z := -w N x) (by rw [norm_neg]; exact hN x hx)
    rwa [norm_neg] at this
  have hE := (Complex.continuous_exp.tendsto 0).comp hL
  rw [Complex.exp_zero] at hE
  refine hE.congr' ?_
  filter_upwards [hw] with N hN
  simp only [Function.comp, Complex.exp_sum]
  refine prod_congr rfl fun x hx => ?_
  rw [Complex.exp_log, sub_eq_add_neg]
  intro h
  have h1 : ‖w N x‖ = 1 := by
    rw [← norm_neg, show -w N x = 1 + -w N x - 1 by ring, h, zero_sub, norm_neg, norm_one]
  have := hN x hx
  linarith

/-- Regrouping `∏_{h,k ≤ N} f(h+k-1) = ∏_{m ≤ N} f(m)^m` when `f = 1` beyond `N`. -/
lemma s26b_prod_regroup {M : Type*} [CommMonoid M] (N : ℕ) (f : ℕ → M)
    (hf1 : ∀ m, N + 1 ≤ m → f m = 1) :
    ∏ h ∈ Icc 1 N, ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ m ∈ Icc 1 N, f m ^ m := by
  have hin : ∀ h ∈ Icc 1 N, ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ m ∈ Icc h N, f m := by
    intro h hh
    rw [mem_Icc] at hh
    have : ∏ k ∈ Icc 1 N, f (h + k - 1) = ∏ k ∈ Icc 1 (N + 1 - h), f (h + k - 1) := by
      symm
      refine prod_subset (fun k hk => by simp only [mem_Icc] at hk ⊢; omega) fun k hk hk' => ?_
      simp only [mem_Icc] at hk hk'
      exact hf1 _ (by omega)
    rw [this]
    refine prod_nbij' (fun k => h + k - 1) (fun m => m + 1 - h) ?_ ?_ ?_ ?_ fun _ _ => rfl
    · intro k hk; simp at hk ⊢; omega
    · intro m hm; simp at hm ⊢; omega
    · intro k hk; simp at hk; omega
    · intro m hm; simp at hm; omega
  rw [prod_congr rfl hin, prod_comm' (t' := Icc 1 N) (s' := fun m => Icc 1 m)]
  · refine prod_congr rfl fun m _ => ?_
    rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  · intro h m
    simp only [mem_Icc]
    omega

/-- The number of plane partitions of `n` in `B(N, N, N)`. -/
def s26b_c (N n : ℕ) : ℕ := #{π ∈ planePartitionsIn N N N | π.card = n}

/-- `c_N(n) ≤ pp(n)`. -/
lemma s26b_c_le (N n : ℕ) : s26b_c N n ≤ planePartitionCount n := by
  refine card_le_card fun π hπ => ?_
  simp only [mem_filter, s26b_mem_planePartitionsIn, mem_powerset] at hπ ⊢
  obtain ⟨⟨_, hπ⟩, rfl⟩ := hπ
  exact ⟨s26b_subset_planeBox_card hπ, hπ, rfl⟩

/-- `c_N(n) = pp(n)` for `n ≤ N`. -/
lemma s26b_c_eq {N n : ℕ} (hn : n ≤ N) : s26b_c N n = planePartitionCount n := by
  have := s26b_coeff_boxPoly (N := N) hn
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, sum_boole] at this
  rw [s26b_c]
  exact_mod_cast (congrArg (fun F => #F) (filter_congr fun π _ => eq_comm)).trans
    (by exact_mod_cast this)

/-- `∑_{π ⊆ B(N,N,N)} q^{|π|} = ∑ₙ c_N(n) qⁿ`. -/
lemma s26b_hasSum_c {q : ℂ} (N : ℕ) :
    HasSum (fun n => (s26b_c N n : ℂ) * q ^ n) (∑ π ∈ planePartitionsIn N N N, q ^ π.card) := by
  have hmaps : ∀ π ∈ planePartitionsIn N N N, π.card ∈ range (N ^ 3 + 1) := by
    intro π hπ
    have := card_le_card (s26b_mem_planePartitionsIn.mp hπ).1
    simp only [planeBox, card_product, Nat.card_Icc, Nat.add_sub_cancel] at this
    rw [mem_range]; nlinarith
  rw [← sum_fiberwise_of_maps_to hmaps]
  have : ∀ n ∈ range (N ^ 3 + 1), ∑ π ∈ planePartitionsIn N N N with π.card = n, q ^ π.card =
      (s26b_c N n : ℂ) * q ^ n := by
    intro n _
    rw [sum_congr rfl fun π hπ => by rw [(mem_filter.mp hπ).2], sum_const, nsmul_eq_mul, s26b_c]
  rw [sum_congr rfl this]
  refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
  rw [s26b_c, card_eq_zero.mpr, Nat.cast_zero, zero_mul]
  refine filter_eq_empty_iff.mpr fun π hπ hc => hn ?_
  rw [← hc]; exact hmaps π hπ

/-- Double products `∏_{h,j ≤ N} (1 - w)` with `‖w‖ ≤ ‖q‖^{N+1}` tend to `1`. -/
lemma s26b_tendsto_box_prod {q : ℂ} (hq : ‖q‖ < 1) (w : ℕ → ℕ × ℕ → ℂ)
    (hw : ∀ N, ∀ x ∈ Icc 1 N ×ˢ Icc 1 N, ‖w N x‖ ≤ ‖q‖ ^ (N + 1)) :
    Tendsto (fun N => ∏ h ∈ Icc 1 N, ∏ j ∈ Icc 1 N, (1 - w N (h, j))) atTop (𝓝 1) := by
  simp only [← prod_product']
  have hq0 := norm_nonneg q
  refine s26b_tendsto_prod_one_sub (fun N => Icc 1 N ×ˢ Icc 1 N) w ?_ ?_
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).comp (tendsto_add_atTop_nat 1)
    filter_upwards [this.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with N hN x hx
    exact (hw N x hx).trans hN
  · have hlim : Tendsto (fun N : ℕ => ‖q‖ * ((N : ℝ) ^ 2 * ‖q‖ ^ N)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
        (by rw [abs_of_nonneg hq0]; exact hq)).const_mul ‖q‖
    refine squeeze_zero (fun N => sum_nonneg fun x _ => norm_nonneg _) (fun N => ?_) hlim
    calc ∑ x ∈ Icc 1 N ×ˢ Icc 1 N, ‖w N x‖ ≤ ∑ _x ∈ Icc 1 N ×ˢ Icc 1 N, ‖q‖ ^ (N + 1) :=
          sum_le_sum (hw N)
      _ = ‖q‖ * ((N : ℝ) ^ 2 * ‖q‖ ^ N) := by
          rw [sum_const, card_product, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          push_cast; ring

end GenFun

open Topology in
/-- (26.12.20), MacMahon: `∑_π q^{|π|} = ∑ₙ pp(n) qⁿ = ∏_{k ≥ 1} (1 - q^k)^{-k}` for `|q| < 1`. -/
@[dlmf 26.12.E20]
theorem hasSum_planePartitionCount {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (planePartitionCount n : ℂ) * q ^ n)
        (∏' k : ℕ, ((1 - q ^ (k + 1)) ^ (k + 1))⁻¹) ∧
      HasProd (fun k : ℕ => ((1 - q ^ (k + 1)) ^ (k + 1))⁻¹)
        (∏' k : ℕ, ((1 - q ^ (k + 1)) ^ (k + 1))⁻¹) := by
  obtain ⟨A, hA⟩ := s26b_hasProd_macMahon hq
  rw [hA.tprod_eq]
  refine ⟨?_, hA⟩
  set F := Complex.exp A
  have hF0 : F ≠ 0 := Complex.exp_ne_zero A
  have hq0 := norm_nonneg q
  have hsP : Summable fun n => (planePartitionCount n : ℂ) * q ^ n :=
    (s26b_summable_pp hq).of_norm
  set GN : ℕ → ℂ := fun N => ∑ π ∈ planePartitionsIn N N N, q ^ π.card with hGN
  -- `GN → P`
  set u : ℕ → ℝ := fun n => ‖(planePartitionCount n : ℂ) * q ^ n‖ with hu
  have T1 : Tendsto GN atTop (𝓝 (∑' n, (planePartitionCount n : ℂ) * q ^ n)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim := (tendsto_sum_nat_add u).comp (tendsto_add_atTop_nat 1)
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hlim
    set d : ℕ → ℂ := fun n =>
      ((planePartitionCount n : ℂ) - s26b_c N n) * q ^ n with hd
    have hdsum : HasSum d (∑' n, (planePartitionCount n : ℂ) * q ^ n - GN N) := by
      have := hsP.hasSum.sub (s26b_hasSum_c (q := q) N)
      convert this using 1
      funext n; simp only [hd]; ring
    have hd0 : ∀ n < N + 1, d n = 0 := fun n hn => by
      simp only [hd, s26b_c_eq (Nat.lt_succ_iff.mp hn), sub_self, zero_mul]
    have hdle : ∀ n, ‖d n‖ ≤ u n := fun n => by
      simp only [hd, hu, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [show ((planePartitionCount n : ℂ) - s26b_c N n) =
        ((planePartitionCount n - s26b_c N n : ℕ) : ℂ) by
          rw [Nat.cast_sub (s26b_c_le N n)], Complex.norm_natCast, Complex.norm_natCast]
      exact_mod_cast Nat.sub_le _ _
    have hshift := (hasSum_nat_add_iff' (f := d) (N + 1)).mpr hdsum
    rw [sum_eq_zero fun n hn => hd0 n (mem_range.mp hn), sub_zero] at hshift
    rw [norm_sub_rev, ← hshift.tsum_eq]
    have hus : Summable fun k => u (k + (N + 1)) :=
      (summable_nat_add_iff (N + 1)).mpr (s26b_summable_pp hq)
    refine (norm_tsum_le_tsum_norm (hus.of_nonneg_of_le (fun _ => norm_nonneg _)
      fun k => hdle _)).trans ?_
    exact Summable.tsum_le_tsum (fun k => hdle _)
      (hus.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => hdle _) hus
  -- `GN → F`
  have hq' : ∀ m : ℕ, 0 < m → q ^ m ≠ 1 := fun m hm h =>
    s26b_one_sub_pow_ne_zero hq hm (by rw [h, sub_self])
  set Num : ℕ → ℂ := fun N => ∏ h ∈ Icc 1 N, ∏ j ∈ Icc 1 N, (1 - q ^ (h + j + N - 1))
  set Xt : ℕ → ℂ := fun N => ∏ h ∈ Icc 1 N, ∏ j ∈ Icc 1 N,
    (1 - (if N < h + j - 1 then q ^ (h + j - 1) else 0))
  set E : ℕ → ℂ := fun N => ∏ m ∈ Icc 1 N, (1 - q ^ m) ^ m
  have hG : ∀ N, GN N = Num N / (E N * Xt N) := by
    intro N
    have hden : ∏ h ∈ Icc 1 N, ∏ j ∈ Icc 1 N, (1 - q ^ (h + j - 1)) = E N * Xt N := by
      have hsplit : ∀ m : ℕ, (1 - q ^ m) = (if m ≤ N then 1 - q ^ m else 1) *
          (1 - (if N < m then q ^ m else 0)) := fun m => by
        split_ifs with h1 h2 h2 <;> first | omega | ring
      rw [prod_congr rfl fun h _ => prod_congr rfl fun j _ => hsplit (h + j - 1)]
      simp only [prod_mul_distrib]
      congr 1
      rw [s26b_prod_regroup N (fun m => if m ≤ N then 1 - q ^ m else 1)
        (fun m hm => by simp only [show ¬m ≤ N by omega, ↓reduceIte])]
      exact prod_congr rfl fun m hm => by simp only [(mem_Icc.mp hm).2, ↓reduceIte]
    show ∑ π ∈ planePartitionsIn N N N, q ^ π.card = _
    rw [s26b_sum_box_pow hq' N N N, ← hden]
    simp only [prod_div_distrib]
    rfl
  have hNum : Tendsto Num atTop (𝓝 1) := by
    refine s26b_tendsto_box_prod hq (fun N x => q ^ (x.1 + x.2 + N - 1)) fun N x hx => ?_
    simp only [mem_product, mem_Icc] at hx
    rw [norm_pow]
    exact pow_le_pow_of_le_one hq0 hq.le (by omega)
  have hXt : Tendsto Xt atTop (𝓝 1) := by
    refine s26b_tendsto_box_prod hq
      (fun N x => if N < x.1 + x.2 - 1 then q ^ (x.1 + x.2 - 1) else 0) fun N x hx => ?_
    split_ifs with h
    · rw [norm_pow]; exact pow_le_pow_of_le_one hq0 hq.le (by omega)
    · rw [norm_zero]; positivity
  have hE : Tendsto E atTop (𝓝 F⁻¹) := by
    refine (hA.tendsto_prod_nat.inv₀ hF0).congr fun N => ?_
    rw [← prod_inv_distrib]
    simp only [inv_inv]
    refine prod_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ fun _ _ => rfl
    · intro k hk; simp at hk ⊢; omega
    · intro m hm; simp at hm ⊢; omega
    · intro k hk; simp
    · intro m hm; simp at hm; omega
  have T2 : Tendsto GN atTop (𝓝 F) := by
    have := hNum.div (hE.mul hXt) (by simpa using hF0)
    rw [mul_one, one_div, inv_inv] at this
    exact this.congr fun N => (hG N).symm
  have := tendsto_nhds_unique T1 T2
  rw [← this]
  exact hsP.hasSum

/-- (26.12.21): `∑_{π ⊆ B(r,s,t)} q^{|π|} = ∏_{(h,j,k) ∈ B} (1-q^{h+j+k-1})/(1-q^{h+j+k-2})
= ∏_{h=1}^r ∏_{j=1}^s (1-q^{h+j+t-1})/(1-q^{h+j-1})`, for `q` not a root of unity. -/
@[dlmf 26.12.E21]
theorem sum_planePartitionsIn_pow {q : ℂ} (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) (r s t : ℕ) :
    ∑ π ∈ planePartitionsIn r s t, q ^ π.card =
        ∏ x ∈ planeBox r s t, (1 - q ^ (x.1 + x.2.1 + x.2.2 - 1)) /
          (1 - q ^ (x.1 + x.2.1 + x.2.2 - 2)) ∧
      ∑ π ∈ planePartitionsIn r s t, q ^ π.card =
        ∏ h ∈ Icc 1 r, ∏ j ∈ Icc 1 s, (1 - q ^ (h + j + t - 1)) / (1 - q ^ (h + j - 1)) := by
  have hne : ∀ m : ℕ, 0 < m → (1 - q ^ m) ≠ 0 := fun m hm h => hq m hm (sub_eq_zero.mp h).symm
  have h2 : ∑ π ∈ planePartitionsIn r s t, q ^ π.card =
      ∏ h ∈ Icc 1 r, ∏ j ∈ Icc 1 s, (1 - q ^ (h + j + t - 1)) / (1 - q ^ (h + j - 1)) :=
    s26b_sum_box_pow hq r s t
  refine ⟨h2.trans ?_, h2⟩
  rw [planeBox, prod_product]
  refine prod_congr rfl fun h hh => ?_
  rw [prod_product]
  refine prod_congr rfl fun j hj => ?_
  simp only [mem_Icc] at hh hj
  have := s26b_prod_Icc_div (fun k : ℕ => 1 - q ^ (h + j + k - 1)) t
    (fun k _ => hne _ (by omega))
  simp only [add_zero] at this
  rw [← this]
  refine prod_congr rfl fun k hk => ?_
  simp only [mem_Icc] at hk
  show _ = (1 - q ^ (h + j + k - 1)) / (1 - q ^ (h + j + k - 2))
  rw [show h + j + (k - 1) - 1 = h + j + k - 2 by omega]

/-- (26.12.22): `∑_{π ⊆ B(r,r,t) symmetric} q^{|π|} = ∏_{h=1}^r (1-q^{2h+t-1})/(1-q^{2h-1})
∏_{1≤h<j≤r} (1-q^{2(h+j+t-1)})/(1-q^{2(h+j-1)})`, for `q` not a root of unity. -/
@[dlmf 26.12.E22]
theorem sum_symmetric_planePartitionsIn_pow {q : ℂ} (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) (r t : ℕ) :
    ∑ π ∈ (planePartitionsIn r r t).filter IsSymmetricPP, q ^ π.card =
      (∏ h ∈ Icc 1 r, (1 - q ^ (2 * h + t - 1)) / (1 - q ^ (2 * h - 1))) *
        ∏ h ∈ Icc 1 r, ∏ j ∈ Ioc h r,
          (1 - q ^ (2 * (h + j + t - 1))) / (1 - q ^ (2 * (h + j - 1))) := by
  sorry

/-- (26.12.23): `∑_{π ⊆ B(r,r,r) cyclically symmetric} q^{|π|}` equals
`∏_{h=1}^r (1-q^{3h-1})/(1-q^{3h-2}) ∏_{1≤h<j≤r} (1-q^{3(h+2j-1)})/(1-q^{3(h+j-1)})` and
`∏_{h=1}^r ((1-q^{3h-1})/(1-q^{3h-2}) ∏_{j=h}^r (1-q^{3(r+h+j-1)})/(1-q^{3(2h+j-1)}))`, for `q`
not a root of unity. -/
@[dlmf 26.12.E23]
theorem sum_cyclicallySymmetric_planePartitionsIn_pow {q : ℂ}
    (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) (r : ℕ) :
    ∑ π ∈ (planePartitionsIn r r r).filter IsCyclicallySymmetricPP, q ^ π.card =
        (∏ h ∈ Icc 1 r, (1 - q ^ (3 * h - 1)) / (1 - q ^ (3 * h - 2))) *
          ∏ h ∈ Icc 1 r, ∏ j ∈ Ioc h r,
            (1 - q ^ (3 * (h + 2 * j - 1))) / (1 - q ^ (3 * (h + j - 1))) ∧
      ∑ π ∈ (planePartitionsIn r r r).filter IsCyclicallySymmetricPP, q ^ π.card =
        ∏ h ∈ Icc 1 r, ((1 - q ^ (3 * h - 1)) / (1 - q ^ (3 * h - 2)) *
          ∏ j ∈ Icc h r, (1 - q ^ (3 * (r + h + j - 1))) / (1 - q ^ (3 * (2 * h + j - 1)))) := by
  sorry

/-- (26.12.24), corrected: `∑ q^{|π|}` over the descending plane partitions in `B(r, r, r)` is
`∏_{1≤h≤j≤r} (1-q^{r+h+j-1})/(1-q^{2h+j-1})` (DLMF prints `h < j`; see the module docstring),
for `q` not a root of unity. -/
@[dlmf 26.12.E24 "corrected: product over 1 ≤ h ≤ j ≤ r (printed h < j)"]
theorem sum_descendingPPIn_pow {q : ℂ} (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) (r : ℕ) :
    ∑ᶠ d : DescendingPPIn r, q ^ (d.1.map List.sum).sum =
      ∏ h ∈ Icc 1 r, ∏ j ∈ Icc h r, (1 - q ^ (r + h + j - 1)) / (1 - q ^ (2 * h + j - 1)) := by
  sorry

/-- (26.12.25): `n pp(n) = ∑_{j=1}^n pp(n-j) σ₂(j)`, `σ₂(j)` the sum of the squares of the
divisors of `j` (stated multiplied by `n`). -/
@[dlmf 26.12.E25]
theorem planePartitionCount_recurrence (n : ℕ) :
    n * planePartitionCount n =
      ∑ j ∈ Icc 1 n, planePartitionCount (n - j) * ArithmeticFunction.sigma 2 j := by
  exact s26b_pp_recurrence n

/-- (26.12.26): `pp(n) ∼ ζ(3)^{7/36}/(2^{11/36} (3π)^{1/2} n^{25/36})
exp(3 ζ(3)^{1/3} (n/2)^{2/3} + ζ'(-1))` as `n → ∞`. -/
@[dlmf 26.12.E26]
theorem planePartitionCount_isEquivalent :
    (fun n : ℕ => (planePartitionCount n : ℝ)) ~[atTop] fun n : ℕ =>
      (riemannZeta 3).re ^ (7 / 36 : ℝ) /
          ((2 : ℝ) ^ (11 / 36 : ℝ) * Real.sqrt (3 * Real.pi) * (n : ℝ) ^ (25 / 36 : ℝ)) *
        Real.exp (3 * (riemannZeta 3).re ^ (1 / 3 : ℝ) * ((n : ℝ) / 2) ^ (2 / 3 : ℝ) +
          (deriv riemannZeta (-1)).re) := by
  sorry

end DLMF.Combinatorics

end
end
