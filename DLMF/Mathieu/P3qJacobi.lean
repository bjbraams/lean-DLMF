/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.EReal.Inv

/-!
# Three-term recurrences of Mathieu type

The Fourier coefficients of the Mathieu functions satisfy the recurrences 28.4.5–28.4.8,
`d_i A_i + q (lo_i + A_{i+1}) = a A_i`, where `lo_0 = 0`, `lo_1 = β A_0`, `lo_i = A_{i-1}`
(`β = 2` for 28.4.5, `β = 1` otherwise). This file contains the elementary theory of such
recurrences used for the small-`q` behaviour (DLMF §28.6, §28.4(vi)):

* `p3q_pair`: the finite Green identity (symmetry of the recurrence with the weights
  `w₀ = β`, `w_i = 1`);
* `p3q_window`: a solution tending to `0` forces some `|a - d_i| ≤ 3|q|` (maximum principle);
* `p3q_decay`: geometric decay `|A_i| ≤ (3|q|)^{|i-n|} |A_n|` away from an isolated diagonal
  entry;
* `p3q_eig_isBigO`: the eigenvalue estimate `a(q) - p(q) = O(q^K)` from a trial vector with
  small residual.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-- Lower neighbour term of the three-term recurrences 28.4.5–28.4.8: `0`, `β A₀`, `A_{i-1}`. -/
def p3qLo (β : ℂ) (A : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => β * A 0
  | i + 2 => A (i + 1)

/-- The tridiagonal operator `(L v)_i = d_i v_i + q (lo_i + v_{i+1})` of 28.4.5–28.4.8. -/
def p3qL (d : ℕ → ℂ) (β q : ℂ) (v : ℕ → ℂ) (i : ℕ) : ℂ :=
  d i * v i + q * (p3qLo β v i + v (i + 1))

/-- The recurrence `L A = a A`. -/
def p3qRec (d : ℕ → ℂ) (β q a : ℂ) (A : ℕ → ℂ) : Prop :=
  ∀ i, p3qL d β q A i = a * A i

/-- The symmetrizing weights `w₀ = β`, `w_i = 1`. -/
def p3qW (β : ℂ) (i : ℕ) : ℂ := if i = 0 then β else 1

lemma p3q_pair_aux (d : ℕ → ℂ) (β q : ℂ) (A v : ℕ → ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), p3qW β i * (A i * p3qL d β q v i - p3qL d β q A i * v i) =
      p3qW β N * q * (A N * v (N + 1) - A (N + 1) * v N) := by
  induction N with
  | zero => simp [p3qW, p3qL, p3qLo]; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rcases N with _ | N
    · simp [p3qW, p3qL, p3qLo]; ring
    · simp only [p3qW, p3qL, p3qLo, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      ring

/-- **Symmetry of the recurrence** (finite Green identity): for `v` supported in `[0, N)`,
`∑ w_i A_i ((Lv)_i - p v_i) = (a - p) ∑ w_i A_i v_i`. -/
lemma p3q_pair {d : ℕ → ℂ} {β q a : ℂ} {A : ℕ → ℂ} (hrec : p3qRec d β q a A) (v : ℕ → ℂ)
    (p : ℂ) {N : ℕ} (hv : v N = 0) (hv' : v (N + 1) = 0) :
    ∑ i ∈ Finset.range (N + 1), p3qW β i * A i * (p3qL d β q v i - p * v i) =
      (a - p) * ∑ i ∈ Finset.range (N + 1), p3qW β i * A i * v i := by
  have h := p3q_pair_aux d β q A v N
  rw [hv, hv'] at h
  simp only [mul_zero, sub_self] at h
  simp only [show ∀ i, p3qL d β q A i = a * A i from hrec] at h
  rw [Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← h]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma p3q_row {d : ℕ → ℂ} {β q a : ℂ} {A : ℕ → ℂ} (hrec : p3qRec d β q a A) (i : ℕ) :
    ‖a - d i‖ * ‖A i‖ ≤ ‖q‖ * (‖p3qLo β A i‖ + ‖A (i + 1)‖) := by
  have h := hrec i
  simp only [p3qL] at h
  have : (a - d i) * A i = q * (p3qLo β A i + A (i + 1)) := by linear_combination -h
  rw [← norm_mul, this, norm_mul]
  gcongr
  exact norm_add_le _ _

theorem p3q_lo_le {β : ℂ} (hβ : ‖β‖ ≤ 2) (A : ℕ → ℂ) {i : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ j, j + 1 = i → ‖A j‖ ≤ M) : ‖p3qLo β A i‖ ≤ 2 * M := by
  rcases i with _ | _ | i
  · simp [p3qLo]; linarith
  · simp only [p3qLo, norm_mul]
    exact mul_le_mul hβ (h 0 rfl) (norm_nonneg _) (by norm_num)
  · simp only [p3qLo]
    linarith [h (i + 1) rfl]

theorem p3q_exists_tail_max {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) (hf0 : ∀ i, 0 ≤ f i)
    (i : ℕ) : ∃ k ≥ i, ∀ j ≥ i, f j ≤ f k := by
  by_cases h : ∃ j ≥ i, 0 < f j
  · obtain ⟨j₀, hj₀, hpos⟩ := h
    obtain ⟨N, hN⟩ := (hf.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
    obtain ⟨k, hk, hmax⟩ := (Finset.Icc i (max N j₀)).exists_max_image f
      ⟨j₀, Finset.mem_Icc.2 ⟨hj₀, le_max_right _ _⟩⟩
    refine ⟨k, (Finset.mem_Icc.1 hk).1, fun j hj => ?_⟩
    by_cases hjN : j ≤ max N j₀
    · exact hmax j (Finset.mem_Icc.2 ⟨hj, hjN⟩)
    · have := hN j (by omega)
      have := hmax j₀ (Finset.mem_Icc.2 ⟨hj₀, le_max_right _ _⟩)
      linarith
  · push Not at h
    exact ⟨i, le_rfl, fun j hj => (h j hj).trans (hf0 i)⟩

/-- **Window**: some diagonal entry is within `3|q|` of the eigenvalue. -/
theorem p3q_window {d : ℕ → ℂ} {β q a : ℂ} {A : ℕ → ℂ} (hβ : ‖β‖ ≤ 2)
    (hrec : p3qRec d β q a A) (hA : Tendsto A atTop (𝓝 0)) (hne : ∃ i, A i ≠ 0) :
    ∃ i, ‖a - d i‖ ≤ 3 * ‖q‖ := by
  obtain ⟨k, -, hk⟩ := p3q_exists_tail_max (f := fun i => ‖A i‖) (by simpa using hA.norm)
    (fun _ => norm_nonneg _) 0
  obtain ⟨i₀, hi₀⟩ := hne
  have hM : 0 < ‖A k‖ := (norm_pos_iff.2 hi₀).trans_le (hk i₀ (Nat.zero_le _))
  refine ⟨k, ?_⟩
  have h1 := p3q_row hrec k
  have h2 := p3q_lo_le hβ A (i := k) hM.le (fun j _ => hk j (Nat.zero_le _))
  have h3 := hk (k + 1) (Nat.zero_le _)
  have : ‖a - d k‖ * ‖A k‖ ≤ 3 * ‖q‖ * ‖A k‖ := by
    nlinarith [norm_nonneg q]
  exact le_of_mul_le_mul_right this hM

lemma p3q_up {d : ℕ → ℂ} {β q a : ℂ} {A : ℕ → ℂ} (hβ : ‖β‖ ≤ 2)
    (hrec : p3qRec d β q a A) (hA : Tendsto A atTop (𝓝 0)) (hq : ‖q‖ ≤ 1 / 4) {n : ℕ}
    (hgap : ∀ i ≠ n, 1 ≤ ‖a - d i‖) {i : ℕ} (hi : n < i) :
    ‖A i‖ ≤ 3 * ‖q‖ * ‖A (i - 1)‖ := by
  obtain ⟨k, hki, hk⟩ := p3q_exists_tail_max (f := fun i => ‖A i‖) (by simpa using hA.norm)
    (fun _ => norm_nonneg _) i
  have hq0 := norm_nonneg q
  have h1 := p3q_row hrec k
  have hg := hgap k (by omega)
  have hAk := norm_nonneg (A k)
  have hAi := hk i le_rfl
  have h3 := hk (k + 1) (by omega)
  rcases hki.lt_or_eq with hlt | heq
  · have h2 := p3q_lo_le hβ A (i := k) hAk (fun j hj => hk j (by omega))
    have : ‖A k‖ ≤ 0 := by nlinarith
    nlinarith [norm_nonneg (A (i - 1))]
  · subst heq
    have h2 := p3q_lo_le hβ A (i := i) (norm_nonneg (A (i - 1)))
      (fun j hj => by rw [show j = i - 1 by omega])
    nlinarith [norm_nonneg (A (i - 1))]

lemma p3q_down {d : ℕ → ℂ} {β q a : ℂ} {A : ℕ → ℂ} (hβ : ‖β‖ ≤ 2)
    (hrec : p3qRec d β q a A) (hq : ‖q‖ ≤ 1 / 4) {n : ℕ}
    (hgap : ∀ i ≠ n, 1 ≤ ‖a - d i‖) {i : ℕ} (hi : i < n) :
    ‖A i‖ ≤ 3 * ‖q‖ * ‖A (i + 1)‖ := by
  obtain ⟨k, hk, hmax⟩ := (Finset.range (i + 1)).exists_max_image (fun j => ‖A j‖)
    ⟨i, Finset.mem_range.2 (by omega)⟩
  rw [Finset.mem_range] at hk
  have hq0 := norm_nonneg q
  have h1 := p3q_row hrec k
  have hg := hgap k (by omega)
  have hAk := norm_nonneg (A k)
  have hAi := hmax i (Finset.mem_range.2 (by omega))
  have h2 := p3q_lo_le hβ A (i := k) hAk (fun j hj => hmax j (Finset.mem_range.2 (by omega)))
  rcases (Nat.lt_succ_iff.1 hk).lt_or_eq with hlt | heq
  · have h3 := hmax (k + 1) (Finset.mem_range.2 (by omega))
    have : ‖A k‖ ≤ 0 := by nlinarith
    nlinarith [norm_nonneg (A (i + 1))]
  · subst heq
    nlinarith [norm_nonneg (A (k + 1))]

/-- **Geometric decay** of the solution away from the index `n` of the eigenvalue:
`|A_i| ≤ (3|q|)^{|i-n|} |A_n|`. -/
theorem p3q_decay {d : ℕ → ℂ} {β q a : ℂ} {A : ℕ → ℂ} (hβ : ‖β‖ ≤ 2)
    (hrec : p3qRec d β q a A) (hA : Tendsto A atTop (𝓝 0)) (hq : ‖q‖ ≤ 1 / 4) {n : ℕ}
    (hgap : ∀ i ≠ n, 1 ≤ ‖a - d i‖) (i : ℕ) :
    ‖A i‖ ≤ (3 * ‖q‖) ^ (Nat.dist i n) * ‖A n‖ := by
  have hq0 : 0 ≤ 3 * ‖q‖ := by positivity
  rcases le_total n i with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show Nat.dist (n + j) n = j by simp [Nat.dist]]
    induction j with
    | zero => simp
    | succ j ih =>
      have := p3q_up hβ hrec hA hq hgap (i := n + (j + 1)) (by omega)
      rw [show n + (j + 1) - 1 = n + j by omega] at this
      calc _ ≤ 3 * ‖q‖ * ‖A (n + j)‖ := this
        _ ≤ 3 * ‖q‖ * ((3 * ‖q‖) ^ j * ‖A n‖) := by gcongr; exact ih (by omega)
        _ = _ := by ring
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le h
    have key : ∀ j i, i + j ≤ n → ‖A i‖ ≤ (3 * ‖q‖) ^ j * ‖A (i + j)‖ := by
      intro j
      induction j with
      | zero => intro i _; simp
      | succ j ih =>
        intro i hij
        have := p3q_down hβ hrec hq hgap (i := i) (by omega)
        calc _ ≤ 3 * ‖q‖ * ‖A (i + 1)‖ := this
          _ ≤ 3 * ‖q‖ * ((3 * ‖q‖) ^ j * ‖A (i + 1 + j)‖) := by
              gcongr; exact ih (i + 1) (by omega)
          _ = _ := by rw [show i + 1 + j = i + (j + 1) by ring]; ring
    have := key j i (by omega)
    rw [← hj] at this
    rwa [show Nat.dist i n = j by simp [Nat.dist]; omega]


theorem p3q_pow_isBigO {m k : ℕ} (h : k ≤ m) :
    (fun x : ℝ => x ^ m) =O[𝓝 0] (fun x => x ^ k) := by
  rcases h.lt_or_eq with h | rfl
  · exact (isLittleO_pow_pow h).isBigO
  · exact isBigO_refl _ _

lemma p3qW_ne_zero {β : ℂ} (hβ : β ≠ 0) (i : ℕ) : p3qW β i ≠ 0 := by
  unfold p3qW; split_ifs <;> simp [hβ]

lemma p3qW_norm_le {β : ℂ} (hβ : ‖β‖ ≤ 2) (i : ℕ) : ‖p3qW β i‖ ≤ 2 := by
  unfold p3qW; split_ifs <;> norm_num [hβ]

/-- **Eigenvalue perturbation estimate.** Let `A(q)` solve the recurrence `L A = a A` with an
eigenvalue `a(q)` separated by `1` from all diagonal entries except the `n`-th, and let `v(q)`
(supported in `[0, N)`, `v_n = 1`) be a trial vector whose residual `(L - p) v` is
`O(q^{K - |i - n|})` in the `i`-th row. Then `a(q) - p(q) = O(q^K)` as `q → 0`. -/
theorem p3q_eig_isBigO {d : ℝ → ℕ → ℂ} {β : ℂ} (hβ : ‖β‖ ≤ 2) (hβ0 : β ≠ 0)
    {a : ℝ → ℂ} {A : ℝ → ℕ → ℂ} {n N K : ℕ} (hnN : n < N)
    (hrec : ∀ᶠ q : ℝ in 𝓝 0, p3qRec (d q) β q (a q) (A q))
    (hA : ∀ᶠ q : ℝ in 𝓝 0, Tendsto (A q) atTop (𝓝 0))
    (hne : ∀ᶠ q : ℝ in 𝓝 0, ∃ i, A q i ≠ 0)
    (hgap : ∀ᶠ q : ℝ in 𝓝 0, ∀ i ≠ n, 1 ≤ ‖a q - d q i‖)
    {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ} (hvN : ∀ q, v q N = 0) (hvN1 : ∀ q, v q (N + 1) = 0)
    (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q => p3qL (d q) β q (v q) i - p q * v q i) =O[𝓝 0]
      (fun q : ℝ => q ^ (K - Nat.dist i n))) :
    (fun q => a q - p q) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
  set α : ℝ → ℕ → ℂ := fun q i => A q i / A q n with hαdef
  have hq4 : ∀ᶠ q : ℝ in 𝓝 0, ‖(q : ℂ)‖ ≤ 1 / 4 := by
    have : ∀ᶠ q : ℝ in 𝓝 0, q ∈ Metric.ball (0 : ℝ) (1 / 4) := Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [this] with q hq
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hq
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hq.le
  have hdec : ∀ᶠ q : ℝ in 𝓝 0, A q n ≠ 0 ∧ ∀ i, ‖α q i‖ ≤ (3 * |q|) ^ Nat.dist i n := by
    filter_upwards [hrec, hA, hne, hgap, hq4] with q h1 h2 h3 h4 h5
    have hd := p3q_decay hβ h1 h2 h5 h4
    have hn : A q n ≠ 0 := by
      intro h0
      obtain ⟨i, hi⟩ := h3
      have := hd i
      rw [h0, norm_zero, mul_zero] at this
      exact hi (norm_le_zero_iff.1 this)
    refine ⟨hn, fun i => ?_⟩
    rw [hαdef, norm_div, div_le_iff₀ (norm_pos_iff.2 hn)]
    simpa [Complex.norm_real] using hd i
  set D : ℝ → ℂ := fun q => ∑ i ∈ Finset.range (N + 1), p3qW β i * α q i * v q i with hD
  set R : ℝ → ℂ := fun q => ∑ i ∈ Finset.range (N + 1),
    p3qW β i * α q i * (p3qL (d q) β q (v q) i - p q * v q i) with hR
  have hid : ∀ᶠ q : ℝ in 𝓝 0, (a q - p q) * D q = R q := by
    filter_upwards [hrec, hdec] with q h1 h2
    have := p3q_pair h1 (v q) (p q) (hvN q) (hvN1 q)
    have e : ∀ x : ℕ → ℂ, ∑ i ∈ Finset.range (N + 1), p3qW β i * α q i * x i =
        (∑ i ∈ Finset.range (N + 1), p3qW β i * A q i * x i) / A q n := by
      intro x; rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => by simp only [hαdef]; ring
    simp only [hD, hR]
    rw [e, e, this, mul_div_assoc]
  have hα : ∀ i, (fun q => p3qW β i * α q i) =O[𝓝 0] (fun q : ℝ => q ^ (Nat.dist i n)) := by
    intro i
    refine IsBigO.of_bound (2 * 3 ^ Nat.dist i n) ?_
    filter_upwards [hdec] with q hq
    rw [norm_mul, norm_pow, Real.norm_eq_abs]
    calc ‖p3qW β i‖ * ‖α q i‖ ≤ 2 * (3 * |q|) ^ Nat.dist i n :=
          mul_le_mul (p3qW_norm_le hβ i) (hq.2 i) (norm_nonneg _) (by norm_num)
      _ = _ := by rw [mul_pow]; ring
  have hRO : R =O[𝓝 0] (fun q : ℝ => q ^ K) := by
    simp only [hR]
    refine IsBigO.fun_sum fun i hi => ?_
    refine ((hα i).mul (hr i (Finset.mem_range.1 hi))).trans ?_
    simp only [← pow_add]
    exact p3q_pow_isBigO (by omega)
  have hw : p3qW β n ≠ 0 := p3qW_ne_zero hβ0 n
  have hDt : Tendsto D (𝓝 0) (𝓝 (p3qW β n)) := by
    have e : p3qW β n = ∑ i ∈ Finset.range (N + 1), if i = n then p3qW β n else 0 := by
      rw [Finset.sum_ite_eq']; simp only [Finset.mem_range]
      rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h)]
    rw [e]
    refine tendsto_finsetSum _ fun i hi => ?_
    split_ifs with h
    · subst h
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hdec] with q hq
      simp only [hαdef, div_self hq.1, hvn, mul_one]
    · have hdist : 1 ≤ Nat.dist i n := by
        rcases lt_or_gt_of_ne h with h' | h'
        · simp [Nat.dist]; omega
        · simp [Nat.dist]; omega
      refine ((hα i).mul (hv i (Finset.mem_range.1 hi))).trans_tendsto ?_
      have : Tendsto (fun q : ℝ => q ^ Nat.dist i n * (1 : ℝ)) (𝓝 0)
          (𝓝 ((0 : ℝ) ^ Nat.dist i n * 1)) :=
        ((continuous_pow _).mul continuous_const).tendsto 0
      rwa [zero_pow (by omega), zero_mul] at this
  have hDinv : (fun q => (D q)⁻¹) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
    (hDt.inv₀ hw).isBigO_one ℝ
  have hD0 : ∀ᶠ q in 𝓝 0, D q ≠ 0 := hDt.eventually_ne hw
  have := hRO.mul hDinv
  simp only [mul_one] at this
  refine this.congr' ?_ EventuallyEq.rfl
  filter_upwards [hid, hD0] with q h1 h2
  rw [← h1, mul_inv_cancel_right₀ h2]

end DLMF.Mathieu
