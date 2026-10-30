/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.P3qSpectrum

/-!
# Expansions of `ce_n(z, q)`, `se_n(z, q)` near `q = 0` from trial vectors

The Fourier coefficients `A_i` of `ce_n`, `se_n` solve one of the recurrences 28.4.5–28.4.8.
Given a trial vector `v` (`v_n = 1`, finitely supported) whose residuals in every row are
`O(q^K)`, the maximum principle of `DLMF.Mathieu.P3qJacobi` gives the uniform estimate
`|A_i/A_n - v_i| ≤ C|q|^K` together with the decay `|A_i/A_n| ≤ (3|q|)^{|i-n|}`
(`p3q_vec_bound`). The normalization 28.4.9–28.4.12 and the sign convention
`ce_n(0, q) > 0`, `se_n'(0, q) > 0` then fix `A_n = c(q) + O(q^K)` for any `c` with
`c(0) = 1` and `c² ∑ w_i v_i² = 1 + O(q^K)`, so that
`ce_n(z, q) = c(q) ∑ v_i cos((2i+δ)z) + O(q^K)` for every fixed `z ∈ ℂ` (`p3q_expand`, and the
class versions `p3q_expand_AE`, `p3q_expand_AE0`, `p3q_expand_AO`, `p3q_expand_BO`,
`p3q_expand_BE`).
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-- The lower neighbour term is additive: `lo(A - B) = lo A - lo B`. -/
lemma p3qLo_sub (β : ℂ) (A B : ℕ → ℂ) (i : ℕ) :
    p3qLo β (fun j => A j - B j) i = p3qLo β A i - p3qLo β B i := by
  rcases i with _ | _ | i <;> simp [p3qLo]; ring

/-- The lower neighbour term is homogeneous: `lo(c A) = c lo A`. -/
lemma p3qLo_smul (β c : ℂ) (A : ℕ → ℂ) (i : ℕ) :
    p3qLo β (fun j => c * A j) i = c * p3qLo β A i := by
  rcases i with _ | _ | i <;> simp [p3qLo]; ring

/-- A scalar multiple of a solution of the recurrence `L A = a A` is again a solution. -/
theorem P3qRec.smul {d : ℕ → ℂ} {β q a : ℂ} {A : ℕ → ℂ} (h : P3qRec d β q a A) (c : ℂ) :
    P3qRec d β q a (fun i => c * A i) := by
  intro i
  have := h i
  simp only [p3qL, p3qLo_smul] at this ⊢
  linear_combination c * this

/-- A big-O relation `f = O(g)` at `0` gives `C ≥ 0` with `‖f q‖ ≤ C ‖g q‖` near `0`. -/
lemma p3q_eventually_bound {f : ℝ → ℂ} {g : ℝ → ℝ} (h : f =O[𝓝 0] g) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ q in 𝓝 0, ‖f q‖ ≤ C * ‖g q‖ := by
  obtain ⟨C, hC⟩ := h.exists_nonneg
  exact ⟨C, hC.1, hC.2.bound⟩

/-- **Eigenvector estimate.** Under the hypotheses of `p3q_eig_isBigO`, with residuals
`O(q^K)` in every row, the normalized solution `α_i = A_i / A_n` satisfies
`|α_i - v_i| ≤ C |q|^K` uniformly in `i`, and `|α_i| ≤ (3|q|)^{|i-n|}`. -/
lemma p3q_vec_bound {d : ℝ → ℕ → ℂ} {β : ℂ} (hβ : ‖β‖ ≤ 2) (hβ0 : β ≠ 0)
    {a : ℝ → ℂ} {A : ℝ → ℕ → ℂ} {n N K : ℕ} (hnN : n < N)
    (hrec : ∀ᶠ q : ℝ in 𝓝 0, P3qRec (d q) β q (a q) (A q))
    (hA : ∀ᶠ q : ℝ in 𝓝 0, Tendsto (A q) atTop (𝓝 0))
    (hne : ∀ᶠ q : ℝ in 𝓝 0, ∃ i, A q i ≠ 0)
    (hgap : ∀ᶠ q : ℝ in 𝓝 0, ∀ i ≠ n, 1 ≤ ‖a q - d q i‖)
    {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ} (hvN : ∀ q i, N ≤ i → v q i = 0)
    (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q => p3qL (d q) β q (v q) i - p q * v q i) =O[𝓝 0]
      (fun q : ℝ => q ^ K)) :
    ∃ C, ∀ᶠ q : ℝ in 𝓝 0, A q n ≠ 0 ∧
      (∀ i, ‖A q i / A q n‖ ≤ (3 * |q|) ^ Nat.dist i n) ∧
      ∀ i, ‖A q i / A q n - v q i‖ ≤ C * |q| ^ K := by
  have hap := p3q_eig_isBigO (K := K) hβ hβ0 hnN hrec hA hne hgap (fun q => hvN q N le_rfl)
    (fun q => hvN q (N + 1) (by omega)) hvn hv
    (fun i hi => (hr i hi).trans (p3q_pow_isBigO (by omega)))
  obtain ⟨C₁, hC₁0, hC₁⟩ := p3q_eventually_bound hap
  choose! Cr hCr0 hCr using fun i (hi : i < N + 1) => p3q_eventually_bound (hr i hi)
  choose! Cv hCv0 hCv using fun i (hi : i < N + 1) => p3q_eventually_bound (hv i hi)
  set C₂ := ∑ i ∈ Finset.range (N + 1), Cr i
  set C₃ := ∑ i ∈ Finset.range (N + 1), Cv i
  have hC₂ : ∀ i < N + 1, Cr i ≤ C₂ := fun i hi =>
    Finset.single_le_sum (fun j hj => hCr0 j (Finset.mem_range.1 hj)) (Finset.mem_range.2 hi)
  have hC₃ : ∀ i < N + 1, Cv i ≤ C₃ := fun i hi =>
    Finset.single_le_sum (fun j hj => hCv0 j (Finset.mem_range.1 hj)) (Finset.mem_range.2 hi)
  have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun j hj => hCr0 j (Finset.mem_range.1 hj)
  have hC₃0 : 0 ≤ C₃ := Finset.sum_nonneg fun j hj => hCv0 j (Finset.mem_range.1 hj)
  have hRall := (Finset.range (N + 1)).eventually_all.2 fun i hi => hCr i (Finset.mem_range.1 hi)
  have hVall := (Finset.range (N + 1)).eventually_all.2 fun i hi => hCv i (Finset.mem_range.1 hi)
  have hR0 : ∀ q i, N + 1 ≤ i → p3qL (d q) β q (v q) i - p q * v q i = 0 := by
    intro q i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    simp only [p3qL, p3qLo, hvN q (j + 2) (by omega), hvN q (j + 1) (by omega),
      hvN q (j + 2 + 1) (by omega)]
    ring
  have hq4 : ∀ᶠ q : ℝ in 𝓝 0, |q| ≤ 1 / 4 := by
    have : ∀ᶠ q : ℝ in 𝓝 0, q ∈ Metric.ball (0 : ℝ) (1 / 4) :=
      Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [this] with q hq
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hq; exact hq.le
  refine ⟨4 * (C₂ + C₁ * C₃), ?_⟩
  filter_upwards [hrec, hA, hne, hgap, hq4, hC₁, hRall, hVall] with q h1 h2 h3 h4 h5 h6 h7 h8
  have h5' : ‖(q : ℂ)‖ ≤ 1 / 4 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hd := p3q_decay hβ h1 h2 h5' h4
  have hn : A q n ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := h3
    have := hd i
    rw [h0, norm_zero, mul_zero] at this
    exact hi (norm_le_zero_iff.1 this)
  have hdec : ∀ i, ‖A q i / A q n‖ ≤ (3 * |q|) ^ Nat.dist i n := fun i => by
    rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hn)]
    simpa [Complex.norm_real] using hd i
  refine ⟨hn, hdec, ?_⟩
  set α : ℕ → ℂ := fun i => A q i / A q n with hαdef
  set e : ℕ → ℂ := fun i => α i - v q i with hedef
  have hαrec : P3qRec (d q) β q (a q) α := by
    have := h1.smul (A q n)⁻¹
    intro i; have h := this i
    simpa only [hαdef, div_eq_inv_mul] using h
  have hαt : Tendsto α atTop (𝓝 0) := by
    have := h2.const_mul (A q n)⁻¹
    simpa only [hαdef, div_eq_inv_mul, mul_zero] using this
  have het : Tendsto e atTop (𝓝 0) := by
    have hv0 : Tendsto (fun i => v q i) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop N] with i hi using (hvN q i hi).symm)
    simpa using hαt.sub hv0
  obtain ⟨i₀, -, hmax⟩ := p3q_exists_tail_max (f := fun i => ‖e i‖) (by simpa using het.norm)
    (fun _ => norm_nonneg _) 0
  have hM : ∀ i, ‖e i‖ ≤ ‖e i₀‖ := fun i => hmax i (Nat.zero_le _)
  have hqK : ‖((q : ℝ) ^ K)‖ = |q| ^ K := by rw [norm_pow, Real.norm_eq_abs]
  -- bound on the inhomogeneity in row `i₀`
  have hB : ‖p3qL (d q) β q (v q) i₀ - p q * v q i₀‖ + ‖a q - p q‖ * ‖v q i₀‖ ≤
      (C₂ + C₁ * C₃) * |q| ^ K := by
    by_cases hi : i₀ < N + 1
    · have e1 := h7 i₀ (Finset.mem_range.2 hi)
      have e2 := h8 i₀ (Finset.mem_range.2 hi)
      simp only [norm_one, mul_one] at e2
      rw [hqK] at e1 h6
      have : Cr i₀ * |q| ^ K ≤ C₂ * |q| ^ K := by gcongr; exact hC₂ i₀ hi
      have : ‖a q - p q‖ * ‖v q i₀‖ ≤ (C₁ * |q| ^ K) * C₃ :=
        mul_le_mul h6 (e2.trans (hC₃ i₀ hi)) (norm_nonneg _) (by positivity)
      nlinarith
    · rw [hR0 q i₀ (by omega), hvN q i₀ (by omega)]
      simp only [norm_zero, mul_zero, add_zero]
      positivity
  have hrow : ‖e i₀‖ ≤ 3 * |q| * ‖e i₀‖ + (C₂ + C₁ * C₃) * |q| ^ K := by
    by_cases hin : i₀ = n
    · have : e i₀ = 0 := by
        simp only [hedef, hαdef, hin, div_self hn, hvn, sub_self]
      rw [this, norm_zero]; positivity
    · have hrel : (a q - d q i₀) * e i₀ = q * (p3qLo β e i₀ + e (i₀ + 1)) +
          (p3qL (d q) β q (v q) i₀ - p q * v q i₀) - (a q - p q) * v q i₀ := by
        have h := hαrec i₀
        simp only [hedef, p3qLo_sub]
        simp only [p3qL] at h ⊢
        linear_combination -h
      have hg := h4 i₀ hin
      have hlo := p3q_lo_le hβ e (i := i₀) (norm_nonneg (e i₀)) (fun j _ => hM j)
      have hn1 := hM (i₀ + 1)
      have : ‖e i₀‖ ≤ ‖(a q - d q i₀) * e i₀‖ := by
        rw [norm_mul]; nlinarith [norm_nonneg (e i₀)]
      rw [hrel] at this
      have t1 := norm_sub_le (q * (p3qLo β e i₀ + e (i₀ + 1)) +
        (p3qL (d q) β q (v q) i₀ - p q * v q i₀)) ((a q - p q) * v q i₀)
      have t2 := norm_add_le (q * (p3qLo β e i₀ + e (i₀ + 1)))
        (p3qL (d q) β q (v q) i₀ - p q * v q i₀)
      have t3 : ‖(q : ℂ) * (p3qLo β e i₀ + e (i₀ + 1))‖ ≤ |q| * (3 * ‖e i₀‖) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        exact (norm_add_le _ _).trans (by linarith)
      rw [norm_mul] at t1
      nlinarith
  intro i
  have h9 := hM i
  have hq0 := abs_nonneg q
  have hpow : 0 ≤ |q| ^ K := by positivity
  have hm := mul_le_mul_of_nonneg_right h5 (norm_nonneg (e i₀))
  have : ‖e i₀‖ ≤ 4 * ((C₂ + C₁ * C₃) * |q| ^ K) := by linarith
  calc ‖A q i / A q n - v q i‖ = ‖e i‖ := rfl
    _ ≤ ‖e i₀‖ := h9
    _ ≤ _ := by linarith

/-- For `ε > 0`, eventually as `q → 0`, `|q| ≤ ε`. -/
lemma p3q_small_nhds (ε : ℝ) (hε : 0 < ε) : ∀ᶠ q : ℝ in 𝓝 0, |q| ≤ ε := by
  have : ∀ᶠ q : ℝ in 𝓝 0, q ∈ Metric.ball (0 : ℝ) ε := Metric.ball_mem_nhds _ hε
  filter_upwards [this] with q hq
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hq; exact hq.le

/-- **Tail bound.** If `|α_i| ≤ (3|q|)^{|i-n|}`, `|α_i - v_i| ≤ C|q|^K`, `v_i = 0` for
`i ≥ n + K`, and `|g_i| ≤ B R^i`, then `|(α_i - v_i) g_i| ≤ |q|^K D 2^{-i}` for small `q`. -/
lemma p3q_tail {α v g : ℝ → ℕ → ℂ} {n K : ℕ} {C B R : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hR : 1 ≤ R)
    (hα : ∀ᶠ q : ℝ in 𝓝 0, ∀ i, ‖α q i‖ ≤ (3 * |q|) ^ Nat.dist i n)
    (hv : ∀ᶠ q : ℝ in 𝓝 0, ∀ i, n + K ≤ i → v q i = 0)
    (he : ∀ᶠ q : ℝ in 𝓝 0, ∀ i, ‖α q i - v q i‖ ≤ C * |q| ^ K)
    (hg : ∀ᶠ q : ℝ in 𝓝 0, ∀ i, ‖g q i‖ ≤ B * R ^ i) :
    ∃ D, 0 ≤ D ∧ ∀ᶠ q : ℝ in 𝓝 0, ∀ i,
      ‖(α q i - v q i) * g q i‖ ≤ |q| ^ K * (D * (1 / 2) ^ i) := by
  set D := C * B * (2 * R) ^ (n + K) + B * (2 * R) ^ n * (3 * (2 * R)) ^ K with hD
  refine ⟨D, by positivity, ?_⟩
  have hR0 : 0 < R := by linarith
  filter_upwards [hα, hv, he, hg, p3q_small_nhds (1 / (6 * R)) (by positivity)]
    with q h1 h2 h3 h4 h5 i
  have hq0 := abs_nonneg q
  have h6 : 3 * |q| * (2 * R) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at h5; linarith
  have h2i : (0 : ℝ) < (1 / 2) ^ i := by positivity
  have key : R ^ i = (2 * R) ^ i * (1 / 2) ^ i := by
    rw [← mul_pow]; congr 1; ring
  have hD1 : 0 ≤ C * B * (2 * R) ^ (n + K) := by positivity
  have hD2 : 0 ≤ B * (2 * R) ^ n * (3 * (2 * R)) ^ K := by positivity
  rw [norm_mul]
  by_cases hi : i < n + K
  · have hle : (2 * R) ^ i ≤ (2 * R) ^ (n + K) := pow_le_pow_right₀ (by linarith) hi.le
    calc ‖α q i - v q i‖ * ‖g q i‖ ≤ (C * |q| ^ K) * (B * R ^ i) :=
          mul_le_mul (h3 i) (h4 i) (norm_nonneg _) (by positivity)
      _ = |q| ^ K * ((C * B * (2 * R) ^ i) * (1 / 2) ^ i) := by rw [key]; ring
      _ ≤ |q| ^ K * (D * (1 / 2) ^ i) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ h2i.le) (by positivity)
          have := mul_le_mul_of_nonneg_left hle (mul_nonneg hC hB)
          linarith
  · push Not at hi
    rw [h2 i hi, sub_zero]
    obtain ⟨k, rfl⟩ : ∃ k, i = n + K + k := ⟨i - (n + K), by omega⟩
    have hd : Nat.dist (n + K + k) n = K + k := by unfold Nat.dist; omega
    have ha := h1 (n + K + k)
    rw [hd] at ha
    have hpow : (3 * |q| * (2 * R)) ^ k ≤ 1 := pow_le_one₀ (by positivity) h6
    calc ‖α q (n + K + k)‖ * ‖g q (n + K + k)‖ ≤ (3 * |q|) ^ (K + k) * (B * R ^ (n + K + k)) :=
          mul_le_mul ha (h4 _) (norm_nonneg _) (by positivity)
      _ = |q| ^ K * ((B * (2 * R) ^ n * (3 * (2 * R)) ^ K * (3 * |q| * (2 * R)) ^ k) *
            (1 / 2) ^ (n + K + k)) := by
          rw [key]; generalize 2 * R = x; ring
      _ ≤ |q| ^ K * (D * (1 / 2) ^ (n + K + k)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          have := mul_le_mul_of_nonneg_left hpow hD2
          linarith

/-- If `‖f_q(i)‖ ≤ |q|^K D 2^{-i}` near `q = 0`, then each `f_q` is summable and
`∑_i f_q(i) = O(q^K)`. -/
lemma p3q_tsum_isBigO {f : ℝ → ℕ → ℂ} {K : ℕ} {D : ℝ} (_hD : 0 ≤ D)
    (h : ∀ᶠ q : ℝ in 𝓝 0, ∀ i, ‖f q i‖ ≤ |q| ^ K * (D * (1 / 2) ^ i)) :
    (∀ᶠ q : ℝ in 𝓝 0, Summable (f q)) ∧
      (fun q => ∑' i, f q i) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
  have hs : Summable (fun i : ℕ => D * (1 / 2 : ℝ) ^ i) := summable_geometric_two.mul_left D
  refine ⟨h.mono fun q hq => Summable.of_norm_bounded (hs.mul_left (|q| ^ K)) hq, ?_⟩
  refine IsBigO.of_bound (2 * D) ?_
  filter_upwards [h] with q hq
  calc ‖∑' i, f q i‖ ≤ ∑' i, |q| ^ K * (D * (1 / 2 : ℝ) ^ i) :=
        tsum_of_norm_bounded (hs.mul_left _).hasSum hq
    _ = 2 * D * ‖q ^ K‖ := by
        rw [tsum_mul_left, tsum_mul_left, tsum_geometric_two, norm_pow, Real.norm_eq_abs]; ring

/-- If `Re r > 0` near `0` and `r² - 1 = O(k)`, then `r - 1 = O(k)`. -/
lemma p3q_isBigO_sub_one_of_sq {r : ℝ → ℂ} {k : ℝ → ℝ}
    (hre : ∀ᶠ q : ℝ in 𝓝 0, 0 < (r q).re)
    (h : (fun q => r q ^ 2 - 1) =O[𝓝 0] k) : (fun q => r q - 1) =O[𝓝 0] k := by
  refine (IsBigO.of_bound 1 ?_).trans h
  filter_upwards [hre] with q hq
  rw [one_mul, show r q ^ 2 - 1 = (r q - 1) * (r q + 1) by ring, norm_mul]
  have : 1 ≤ ‖r q + 1‖ := by
    have := Complex.abs_re_le_norm (r q + 1)
    rw [Complex.add_re, Complex.one_re] at this
    have := le_abs_self ((r q).re + 1)
    linarith
  nlinarith [norm_nonneg (r q - 1)]

/-- **Expansion of the normalized eigenvector.** Under the hypotheses of `p3q_vec_bound`, with
the normalization `∑ w_i A_i² = 1`, the sign condition `∑ u_i A_i > 0` (`u_n = 1`), and a
normalizing function `c(q) → c₀ > 0` with `c² ∑_{i<N} w_i v_i² = 1 + O(q^K)`, every series
`∑ A_i g_i` with `|g_i| ≤ B R^i` equals `c ∑_{i<N} v_i g_i + O(q^K)`. -/
lemma p3q_expand {d : ℝ → ℕ → ℂ} {β : ℂ} (hβ : ‖β‖ ≤ 2) (hβ0 : β ≠ 0)
    {a : ℝ → ℂ} {A : ℝ → ℕ → ℂ} {n N K : ℕ} (hnN : n < N) (hNK : N ≤ n + K) (hK : 1 ≤ K)
    (hrec : ∀ᶠ q : ℝ in 𝓝 0, P3qRec (d q) β q (a q) (A q))
    (hA : ∀ᶠ q : ℝ in 𝓝 0, Tendsto (A q) atTop (𝓝 0))
    (hne : ∀ᶠ q : ℝ in 𝓝 0, ∃ i, A q i ≠ 0)
    (hgap : ∀ᶠ q : ℝ in 𝓝 0, ∀ i ≠ n, 1 ≤ ‖a q - d q i‖)
    {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ} (hvN : ∀ q i, N ≤ i → v q i = 0)
    (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q => p3qL (d q) β q (v q) i - p q * v q i) =O[𝓝 0]
      (fun q : ℝ => q ^ K))
    {w : ℕ → ℂ} (hw : ∀ i, ‖w i‖ ≤ 2)
    (hsq : ∀ᶠ q : ℝ in 𝓝 0, HasSum (fun i => w i * A q i ^ 2) 1)
    {u : ℕ → ℂ} {Bu Ru : ℝ} (hBu : 0 ≤ Bu) (hRu : 1 ≤ Ru) (hu : ∀ i, ‖u i‖ ≤ Bu * Ru ^ i)
    (hun : u n = 1)
    (hsign : ∀ᶠ q : ℝ in 𝓝 0, ∃ s : ℝ, 0 < s ∧ HasSum (fun i => u i * A q i) (s : ℂ))
    {c : ℝ → ℂ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : Tendsto c (𝓝 0) (𝓝 (c₀ : ℂ)))
    (hcn : (fun q => c q ^ 2 * ∑ i ∈ Finset.range N, w i * v q i ^ 2 - 1) =O[𝓝 0]
      (fun q : ℝ => q ^ K))
    {g : ℕ → ℂ} {B R : ℝ} (hB : 0 ≤ B) (hR : 1 ≤ R) (hg : ∀ i, ‖g i‖ ≤ B * R ^ i) :
    (fun q => ∑' i, A q i * g i - c q * ∑ i ∈ Finset.range N, v q i * g i) =O[𝓝 0]
      (fun q : ℝ => q ^ K) := by
  obtain ⟨C₀, hvb⟩ := p3q_vec_bound hβ hβ0 hnN hrec hA hne hgap hvN hvn hv hr
  set C := max C₀ 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  set α : ℝ → ℕ → ℂ := fun q i => A q i / A q n with hαdef
  have hAn : ∀ᶠ q : ℝ in 𝓝 0, A q n ≠ 0 := hvb.mono fun q h => h.1
  have hdec : ∀ᶠ q : ℝ in 𝓝 0, ∀ i, ‖α q i‖ ≤ (3 * |q|) ^ Nat.dist i n :=
    hvb.mono fun q h => h.2.1
  have hunif : ∀ᶠ q : ℝ in 𝓝 0, ∀ i, ‖α q i - v q i‖ ≤ C * |q| ^ K :=
    hvb.mono fun q h i => (h.2.2 i).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hvK : ∀ᶠ q : ℝ in 𝓝 0, ∀ i, n + K ≤ i → v q i = 0 :=
    Eventually.of_forall fun q i hi => hvN q i (by omega)
  have hvsum : ∀ (q : ℝ) (f : ℕ → ℂ), ∑' i, v q i * f i = ∑ i ∈ Finset.range N, v q i * f i :=
    fun q f => tsum_eq_sum fun i hi => by
      rw [hvN q i (by simpa using hi), zero_mul]
  have hvsumm : ∀ (q : ℝ) (f : ℕ → ℂ), Summable fun i => v q i * f i := fun q f =>
    summable_of_ne_finset_zero (s := Finset.range N) fun i hi => by
      rw [hvN q i (by simpa using hi), zero_mul]
  -- (T1) the series `∑ (α - v) g`
  obtain ⟨D₁, hD₁, hT1⟩ := p3q_tail (g := fun _ i => g i) hC hB hR hdec hvK hunif
    (Eventually.of_forall fun _ => hg)
  obtain ⟨hS1, hO1⟩ := p3q_tsum_isBigO hD₁ hT1
  -- small `q`
  have hsmall : ∀ᶠ q : ℝ in 𝓝 0, 3 * |q| ≤ 1 ∧ C * |q| ^ K ≤ 1 := by
    have h1 := p3q_small_nhds (1 / 3) (by norm_num)
    have h2 : Tendsto (fun q : ℝ => C * |q| ^ K) (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun q : ℝ => C * |q| ^ K) (𝓝 0) (𝓝 (C * |(0 : ℝ)| ^ K)) :=
        ((continuous_abs.pow K).const_mul C).tendsto 0
      simpa [zero_pow (by omega : K ≠ 0)] using this
    filter_upwards [h1, h2.eventually (ge_mem_nhds one_pos)] with q hq1 hq2
    exact ⟨by linarith, hq2⟩
  have hαle : ∀ᶠ q : ℝ in 𝓝 0, ∀ i, ‖α q i‖ ≤ 1 := by
    filter_upwards [hdec, hsmall] with q h1 h2 i
    exact (h1 i).trans (pow_le_one₀ (by positivity) h2.1)
  -- (T2) the normalization
  obtain ⟨D₂, hD₂, hT2⟩ := p3q_tail (g := fun q i => w i * (α q i + v q i)) (B := 6) (R := 1)
    hC (by norm_num) le_rfl hdec hvK hunif (by
      filter_upwards [hαle, hunif, hsmall] with q h1 h2 h3 i
      rw [one_pow, mul_one, norm_mul]
      have hvi : ‖v q i‖ ≤ 2 := by
        have := norm_sub_le_norm_sub_add_norm_sub (v q i) (α q i) 0
        rw [sub_zero, sub_zero, norm_sub_rev] at this
        linarith [h1 i, h2 i, h3.2]
      have := norm_add_le (α q i) (v q i)
      have hw0 := hw i
      nlinarith [norm_nonneg (w i), norm_nonneg (α q i + v q i), h1 i])
  obtain ⟨-, hO2⟩ := p3q_tsum_isBigO hD₂ hT2
  set P2 : ℝ → ℂ := fun q => ∑ i ∈ Finset.range N, w i * v q i ^ 2 with hP2
  have hinv : (fun q => ((A q n) ^ 2)⁻¹ - P2 q) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
    refine hO2.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [hAn, hsq] with q h1 h2
    have hα2 : HasSum (fun i => w i * α q i ^ 2) ((A q n) ^ 2)⁻¹ := by
      have := h2.mul_left ((A q n) ^ 2)⁻¹
      rw [mul_one] at this
      convert this using 2 with i
      simp only [hαdef, div_pow]; ring
    have hv2 : HasSum (fun i => w i * v q i ^ 2) (P2 q) := by
      refine hasSum_sum_of_ne_finset_zero fun i hi => ?_
      rw [hvN q i (by simpa using hi)]; ring
    rw [← (hα2.sub hv2).tsum_eq]
    congr 1; ext i; ring
  -- (T3) the sign
  set δ : ℝ → ℕ → ℂ := fun _ i => if i = n then 1 else 0 with hδ
  obtain ⟨D₃, hD₃, hT3⟩ := p3q_tail (α := α) (v := δ) (g := fun _ i => u i) (K := 1) (C := 3)
    (by norm_num) hBu hRu hdec (Eventually.of_forall fun q i hi => by
      simp only [hδ, show i ≠ n by omega, ↓reduceIte]) (by
      filter_upwards [hdec, hsmall, hAn] with q h1 h2 h3 i
      by_cases hi : i = n
      · subst hi; simp only [hδ, hαdef, ↓reduceIte, div_self h3, sub_self, norm_zero]
        positivity
      · simp only [hδ, hi, ↓reduceIte, sub_zero, pow_one]
        refine (h1 i).trans ?_
        have hd : 1 ≤ Nat.dist i n := by
          unfold Nat.dist; omega
        simpa using pow_le_pow_of_le_one (by positivity) h2.1 hd)
    (Eventually.of_forall fun _ => hu)
  obtain ⟨hS3, hO3⟩ := p3q_tsum_isBigO hD₃ hT3
  set σ : ℝ → ℂ := fun q => ∑' i, u i * α q i with hσ
  have hσt : Tendsto σ (𝓝 0) (𝓝 1) := by
    have h0 : Tendsto (fun q => ∑' i, (α q i - δ q i) * u i) (𝓝 0) (𝓝 0) :=
      hO3.trans_tendsto (by simpa using ((continuous_pow 1).tendsto (0 : ℝ)))
    have := h0.add_const 1
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [hS3] with q h1
    have hδs : HasSum (fun i => δ q i * u i) 1 := by
      have : HasSum (fun i => δ q i * u i) (∑ i ∈ ({n} : Finset ℕ), δ q i * u i) :=
        hasSum_sum_of_ne_finset_zero fun i hi => by
          simp only [hδ, Finset.mem_singleton] at hi ⊢; simp only [hi, ↓reduceIte, zero_mul]
      simpa [hδ, hun] using this
    rw [hσ]; simp only
    rw [← (h1.hasSum.add hδs).tsum_eq]
    congr 1; ext i; ring
  have hcσ : Tendsto (fun q => c q * σ q) (𝓝 0) (𝓝 (c₀ : ℂ)) := by
    simpa using hc.mul hσt
  have hcσre : ∀ᶠ q : ℝ in 𝓝 0, 0 < (c q * σ q).re := by
    have := (Complex.continuous_re.tendsto _).comp hcσ
    rw [Complex.ofReal_re] at this
    exact this.eventually (lt_mem_nhds hc₀)
  set r : ℝ → ℂ := fun q => c q / A q n with hr'
  have hrre : ∀ᶠ q : ℝ in 𝓝 0, 0 < (r q).re := by
    filter_upwards [hcσre, hsign, hAn] with q h1 h2 h3
    obtain ⟨s, hs, hsum⟩ := h2
    have hσq : σ q = s / A q n := by
      have := hsum.div_const (A q n)
      rw [hσ]; simp only
      rw [← this.tsum_eq]
      congr 1; ext i; simp only [hαdef]; ring
    have : r q = (c q * σ q) / (s : ℂ) := by
      rw [hσq, hr']; simp only
      have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      field_simp
    rw [this, Complex.div_ofReal_re]
    positivity
  have hcO : c =O[𝓝 0] (fun _ => (1 : ℝ)) := hc.isBigO_one ℝ
  have hr2 : (fun q => r q ^ 2 - 1) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
    have h1 : (fun q => c q * c q * ((A q n ^ 2)⁻¹ - P2 q)) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
      simpa using (hcO.mul hcO).mul hinv
    refine (h1.add hcn).congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [hAn] with q h1
    simp only [hr', hP2]
    field_simp
    ring
  have hr1 := p3q_isBigO_sub_one_of_sq hrre hr2
  have hqK : Tendsto (fun q : ℝ => q ^ K) (𝓝 0) (𝓝 0) := by
    simpa [zero_pow (by omega : K ≠ 0)] using ((continuous_pow K).tendsto (0 : ℝ))
  have hrt : Tendsto r (𝓝 0) (𝓝 1) := by
    have := (hr1.trans_tendsto hqK).add_const 1
    simpa using this
  have hAnt : Tendsto (fun q => A q n) (𝓝 0) (𝓝 (c₀ : ℂ)) := by
    have := hc.div hrt one_ne_zero
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [hAn, hrre] with q h1 h2
    have : r q ≠ 0 := fun h => by rw [h, Complex.zero_re] at h2; exact lt_irrefl _ h2
    have hcq : c q ≠ 0 := fun h => this (by simp [hr', h])
    show c q / (c q / A q n) = A q n
    field_simp
  have hAnO : (fun q => A q n) =O[𝓝 0] (fun _ => (1 : ℝ)) := hAnt.isBigO_one ℝ
  have hAc : (fun q => A q n - c q) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
    have h1 : (fun q => A q n * (r q - 1)) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
      simpa using hAnO.mul hr1
    refine h1.neg_left.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [hAn] with q h1
    simp only [hr']
    field_simp
    ring
  have hvgO : (fun q => ∑ i ∈ Finset.range N, v q i * g i) =O[𝓝 0] (fun _ => (1 : ℝ)) := by
    have hs := IsBigO.sum (A := fun i (q : ℝ) => v q i * g i) (g := fun _ : ℝ => (1 : ℝ))
      (l := 𝓝 0) (s := Finset.range N) fun i hi => by
        have hi' : i < N + 1 := by simp at hi; omega
        simpa using (hv i hi').mul (isBigO_const_one ℝ (g i) (𝓝 (0 : ℝ)))
    exact hs.congr_left fun q => by simp [Finset.sum_apply]
  have h1 : (fun q => A q n * ∑' i, (α q i - v q i) * g i) =O[𝓝 0] (fun q : ℝ => q ^ K) := by
    simpa using hAnO.mul hO1
  have h2 : (fun q => (A q n - c q) * ∑ i ∈ Finset.range N, v q i * g i) =O[𝓝 0]
      (fun q : ℝ => q ^ K) := by
    simpa using hAc.mul hvgO
  refine (h1.add h2).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [hAn, hS1] with q h1 h2
  have hAg : ∑' i, A q i * g i = A q n * ∑' i, α q i * g i := by
    rw [← tsum_mul_left]; congr 1; ext i; simp only [hαdef]; field_simp
  have hsplit : ∑' i, α q i * g i = ∑' i, (α q i - v q i) * g i +
      ∑ i ∈ Finset.range N, v q i * g i := by
    rw [← hvsum q g, ← (h2.hasSum.add (hvsumm q g).hasSum).tsum_eq]
    congr 1; ext i; ring
  rw [hAg, hsplit]
  ring

/-! ### The Mathieu recurrences -/

/-- For small `q`, `a_{2n}(q)` is at distance `≥ 1` from every diagonal entry `4i²`, `i ≠ n`. -/
lemma p3q_gap_AE (n : ℕ) : ∀ᶠ q : ℝ in 𝓝 0, ∀ i ≠ n,
    1 ≤ ‖(mathieuA (2 * n) q : ℂ) - 4 * (i : ℂ) ^ 2‖ := by
  filter_upwards [p3q_mathieuA_near (2 * n), p3q_eventually_small] with q h1 h2
  intro i hi
  rw [show (4 * (i : ℂ) ^ 2) = ((((2 * i + 0 : ℕ) : ℝ) ^ 2 + 0 : ℝ) : ℂ) by push_cast; ring,
    p3q_norm_ofReal_sub]
  exact p3q_gap_aux h2 (by simpa using h1) (p3q_sq_sep hi 0) (by simp)

/-- For small `q`, `a_{2n+1}(q)` is at distance `≥ 1` from every diagonal entry of 28.4.6
other than the `n`-th. -/
lemma p3q_gap_AO (n : ℕ) : ∀ᶠ q : ℝ in 𝓝 0, ∀ i ≠ n,
    1 ≤ ‖(mathieuA (2 * n + 1) q : ℂ) -
      ((2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0)‖ := by
  filter_upwards [p3q_mathieuA_near (2 * n + 1), p3q_eventually_small] with q h1 h2
  intro i hi
  rw [show ((2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0) =
      ((((2 * i + 1 : ℕ) : ℝ) ^ 2 + (if i = 0 then q else 0) : ℝ) : ℂ) by
      split_ifs <;> push_cast <;> ring, p3q_norm_ofReal_sub]
  exact p3q_gap_aux h2 (by simpa using h1) (p3q_sq_sep hi 1) (by split_ifs <;> simp)

/-- For small `q`, `b_{2n+1}(q)` is at distance `≥ 1` from every diagonal entry of 28.4.7
other than the `n`-th. -/
lemma p3q_gap_BO (n : ℕ) : ∀ᶠ q : ℝ in 𝓝 0, ∀ i ≠ n,
    1 ≤ ‖(mathieuB (2 * n + 1) q : ℂ) -
      ((2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0)‖ := by
  filter_upwards [p3q_mathieuB_near (m := 2 * n + 1) (by omega), p3q_eventually_small]
    with q h1 h2
  intro i hi
  rw [show ((2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0) =
      ((((2 * i + 1 : ℕ) : ℝ) ^ 2 + -(if i = 0 then q else 0) : ℝ) : ℂ) by
      split_ifs <;> push_cast <;> ring, p3q_norm_ofReal_sub]
  exact p3q_gap_aux h2 (by simpa using h1) (p3q_sq_sep hi 1) (by split_ifs <;> simp)

/-- For small `q`, `b_{2n+2}(q)` is at distance `≥ 1` from every `(2i+2)²`, `i ≠ n`. -/
lemma p3q_gap_BE (n : ℕ) : ∀ᶠ q : ℝ in 𝓝 0, ∀ i ≠ n,
    1 ≤ ‖(mathieuB (2 * n + 2) q : ℂ) - (2 * (i : ℂ) + 2) ^ 2‖ := by
  filter_upwards [p3q_mathieuB_near (m := 2 * n + 2) (by omega), p3q_eventually_small]
    with q h1 h2
  intro i hi
  rw [show ((2 * (i : ℂ) + 2) ^ 2) = ((((2 * i + 2 : ℕ) : ℝ) ^ 2 + 0 : ℝ) : ℂ) by
      push_cast; ring, p3q_norm_ofReal_sub]
  exact p3q_gap_aux h2 (by simpa using h1) (p3q_sq_sep hi 2) (by simp)

/-- For `δ ≤ 2`, `|cos((2i+δ)z)|` and `|sin((2i+δ)z)|` are at most
`e^{2|Im z|} (e^{2|Im z|})^i`. -/
lemma p3q_trig_bound (z : ℂ) {δ : ℕ} (hδ : δ ≤ 2) (i : ℕ) :
    ‖Complex.cos ((2 * (i : ℂ) + δ) * z)‖ ≤
        Real.exp (2 * |z.im|) * Real.exp (2 * |z.im|) ^ i ∧
      ‖Complex.sin ((2 * (i : ℂ) + δ) * z)‖ ≤
        Real.exp (2 * |z.im|) * Real.exp (2 * |z.im|) ^ i := by
  have him : |((2 * (i : ℂ) + δ) * z).im| ≤ 2 * |z.im| + i * (2 * |z.im|) := by
    rw [show ((2 * (i : ℂ) + δ) * z).im = (2 * i + δ) * z.im by
      simp [Complex.mul_im]]
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have : (δ : ℝ) ≤ 2 := by exact_mod_cast hδ
    nlinarith [abs_nonneg z.im]
  have he : Real.exp |((2 * (i : ℂ) + δ) * z).im| ≤
      Real.exp (2 * |z.im|) * Real.exp (2 * |z.im|) ^ i := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 him
  exact ⟨(p2f_norm_cos_le _).trans he, (p2f_norm_sin_le _).trans he⟩

/-- `se'_{2n+1}(0, q) = ∑_i (2i+1) B^{2n+1}_{2i+1}(q)`. -/
lemma p3q_hasSum_deriv_se_odd (n : ℕ) (q : ℝ) :
    HasSum (fun i : ℕ => ((2 * i + 1 : ℕ) : ℂ) * mathieuFourierB (2 * n + 1) (2 * i + 1) q)
      (mathieuSeDerivZero (2 * n + 1) q : ℂ) := by
  have h := (mathieuFourier_sign (2 * n + 1) q).2.1 (by omega)
  rw [deriv_mathieuSe_zero] at h
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m + 1)
    (fun a b h => by simpa using h) ?_)] at h
  · exact h
  · intro x hx
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' x
    · rw [p1a2_fourierB_odd_even]; simp
    · exact absurd ⟨j, rfl⟩ hx

/-- `se'_{2n+2}(0, q) = ∑_i (2i+2) B^{2n+2}_{2i+2}(q)`. -/
lemma p3q_hasSum_deriv_se_even (n : ℕ) (q : ℝ) :
    HasSum (fun i : ℕ => ((2 * i + 2 : ℕ) : ℂ) * mathieuFourierB (2 * n + 2) (2 * i + 2) q)
      (mathieuSeDerivZero (2 * n + 2) q : ℂ) := by
  have h := (mathieuFourier_sign (2 * n + 2) q).2.1 (by omega)
  rw [deriv_mathieuSe_zero] at h
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m + 2)
    (fun a b h => by simpa using h) ?_)] at h
  · exact h
  · intro x hx
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' x
    · rcases j with _ | j
      · simp
      · exact absurd ⟨j, by ring⟩ hx
    · rw [p1a2_fourierB_even_odd]; simp

/-- For `c ≤ 2`, `|(2i+c)/(2n+c)| ≤ 2 · 2^i`. -/
lemma p3q_u_bound (c : ℕ) (hc : c ≤ 2) (n : ℕ) (i : ℕ) :
    ‖((2 * i + c : ℕ) : ℂ) / ((2 * n + c : ℕ) : ℂ)‖ ≤ 2 * 2 ^ i := by
  have h1 : ((2 * i + c : ℕ) : ℝ) ≤ 2 * 2 ^ i := by
    have : (i : ℝ) + 1 ≤ 2 ^ i := by
      have := Nat.lt_two_pow_self (n := i)
      exact_mod_cast this
    push_cast
    have : (c : ℝ) ≤ 2 := by exact_mod_cast hc
    linarith
  rcases Nat.eq_zero_or_pos (2 * n + c) with h0 | h0
  · rw [h0]; simp
  · rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    rw [div_le_iff₀ (by exact_mod_cast h0)]
    have : (1 : ℝ) ≤ ((2 * n + c : ℕ) : ℝ) := by exact_mod_cast h0
    nlinarith [show (0 : ℝ) ≤ 2 * 2 ^ i by positivity]

/-! ### Expansions of `ce_n`, `se_n` from trial vectors -/

/-- `ce_{2n}`, `n ≥ 1`, from a trial vector for recurrence 28.4.5. -/
theorem p3q_expand_AE (n : ℕ) (_hn : n ≠ 0) {N K : ℕ} (hnN : n < N) (hNK : N ≤ n + K)
    (hK : 1 ≤ K) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ} (hvN : ∀ q i, N ≤ i → v q i = 0)
    (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => p3qL (fun i => 4 * (i : ℂ) ^ 2) 2 q (v q) i -
      p q * v q i) =O[𝓝 0] (fun q : ℝ => q ^ K))
    {c : ℝ → ℂ} (hc : Tendsto c (𝓝 0) (𝓝 1))
    (hcn : (fun q => c q ^ 2 * ∑ i ∈ Finset.range N, (if i = 0 then 2 else 1) * v q i ^ 2 - 1)
      =O[𝓝 0] (fun q : ℝ => q ^ K)) (z : ℂ) :
    (fun q : ℝ => mathieuCe (2 * n) z q -
      c q * ∑ i ∈ Finset.range N, v q i * Complex.cos (2 * (i : ℂ) * z)) =O[𝓝 0]
      (fun q : ℝ => q ^ K) := by
  have h := p3q_expand (d := fun _ i => 4 * (i : ℂ) ^ 2) (β := 2) (by norm_num) (by norm_num)
    (a := fun q => (mathieuA (2 * n) q : ℂ)) (A := fun q i => mathieuFourierA (2 * n) (2 * i) q)
    hnN hNK hK (Eventually.of_forall (p3q_rec_AE n)) (Eventually.of_forall (p3q_lim_AE n))
    (Eventually.of_forall (p3q_ne_AE n)) (p3q_gap_AE n) hvN hvn hv hr
    (w := fun i => if i = 0 then 2 else 1) (fun i => by split_ifs <;> norm_num)
    (Eventually.of_forall (hasSum_mathieuFourierA_even_sq n))
    (u := fun _ => 1) (Bu := 1) (Ru := 1) zero_le_one le_rfl (fun i => by simp) rfl
    (Eventually.of_forall fun q => ⟨mathieuCeZero (2 * n) q, mathieuCeZero_pos _ _, by
      simpa [mathieuCe_zero] using hasSum_mathieuCe_even n q 0⟩)
    (c₀ := 1) one_pos (by rw [Complex.ofReal_one]; exact hc) hcn
    (g := fun i => Complex.cos (2 * (i : ℂ) * z)) (B := Real.exp (2 * |z.im|))
    (R := Real.exp (2 * |z.im|)) (by positivity) (Real.one_le_exp (by positivity))
    (fun i => by simpa using (p3q_trig_bound z (δ := 0) (by norm_num) i).1)
  refine h.congr_left fun q => ?_
  rw [(hasSum_mathieuCe_even n q z).tsum_eq]

/-- `√2 ce₀`, from a trial vector for recurrence 28.4.5 with `n = 0`. -/
theorem p3q_expand_AE0 {N K : ℕ} (hnN : 0 < N) (hNK : N ≤ K)
    (hK : 1 ≤ K) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ} (hvN : ∀ q i, N ≤ i → v q i = 0)
    (hvn : ∀ q, v q 0 = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => p3qL (fun i => 4 * (i : ℂ) ^ 2) 2 q (v q) i -
      p q * v q i) =O[𝓝 0] (fun q : ℝ => q ^ K))
    {c : ℝ → ℂ} (hc : Tendsto c (𝓝 0) (𝓝 1))
    (hcn : (fun q => c q ^ 2 * ∑ i ∈ Finset.range N, (if i = 0 then 1 else 1 / 2) * v q i ^ 2 - 1)
      =O[𝓝 0] (fun q : ℝ => q ^ K)) (z : ℂ) :
    (fun q : ℝ => (Real.sqrt 2 : ℂ) * mathieuCe 0 z q -
      c q * ∑ i ∈ Finset.range N, v q i * Complex.cos (2 * (i : ℂ) * z)) =O[𝓝 0]
      (fun q : ℝ => q ^ K) := by
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have h := p3q_expand (d := fun _ i => 4 * (i : ℂ) ^ 2) (β := 2) (by norm_num) (by norm_num)
    (a := fun q => (mathieuA (2 * 0) q : ℂ))
    (A := fun q i => (Real.sqrt 2 : ℂ) * mathieuFourierA (2 * 0) (2 * i) q) (n := 0)
    hnN (by omega) hK (Eventually.of_forall fun q => (p3q_rec_AE 0 q).smul _)
    (Eventually.of_forall fun q => by simpa using (p3q_lim_AE 0 q).const_mul (Real.sqrt 2 : ℂ))
    (Eventually.of_forall fun q => by
      obtain ⟨i, hi⟩ := p3q_ne_AE 0 q
      exact ⟨i, mul_ne_zero hs0 hi⟩) (p3q_gap_AE 0) hvN hvn hv hr
    (w := fun i => if i = 0 then 1 else 1 / 2) (fun i => by split_ifs <;> norm_num)
    (Eventually.of_forall fun q => by
      have := hasSum_mathieuFourierA_even_sq 0 q
      convert this using 2 with i
      rw [mul_pow, hs2]; split_ifs <;> ring)
    (u := fun _ => 1) (Bu := 1) (Ru := 1) zero_le_one le_rfl (fun i => by simp) rfl
    (Eventually.of_forall fun q => ⟨Real.sqrt 2 * mathieuCeZero (2 * 0) q,
      mul_pos (by positivity) (mathieuCeZero_pos _ _), by
      have := (hasSum_mathieuCe_even 0 q 0).mul_left (Real.sqrt 2 : ℂ)
      simpa [mathieuCe_zero] using this⟩)
    (c₀ := 1) one_pos (by rw [Complex.ofReal_one]; exact hc) hcn
    (g := fun i => Complex.cos (2 * (i : ℂ) * z)) (B := Real.exp (2 * |z.im|))
    (R := Real.exp (2 * |z.im|)) (by positivity) (Real.one_le_exp (by positivity))
    (fun i => by simpa using (p3q_trig_bound z (δ := 0) (by norm_num) i).1)
  refine h.congr_left fun q => ?_
  have := ((hasSum_mathieuCe_even 0 q z).mul_left (Real.sqrt 2 : ℂ)).tsum_eq
  simp only [mul_assoc] at this ⊢
  rw [this]

/-- `ce_{2n+1}` from a trial vector for recurrence 28.4.6. -/
theorem p3q_expand_AO (n : ℕ) {N K : ℕ} (hnN : n < N) (hNK : N ≤ n + K)
    (hK : 1 ≤ K) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ} (hvN : ∀ q i, N ≤ i → v q i = 0)
    (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => p3qL (fun i => (2 * (i : ℂ) + 1) ^ 2 +
      if i = 0 then (q : ℂ) else 0) 1 q (v q) i - p q * v q i) =O[𝓝 0] (fun q : ℝ => q ^ K))
    {c : ℝ → ℂ} (hc : Tendsto c (𝓝 0) (𝓝 1))
    (hcn : (fun q => c q ^ 2 * ∑ i ∈ Finset.range N, 1 * v q i ^ 2 - 1)
      =O[𝓝 0] (fun q : ℝ => q ^ K)) (z : ℂ) :
    (fun q : ℝ => mathieuCe (2 * n + 1) z q -
      c q * ∑ i ∈ Finset.range N, v q i * Complex.cos ((2 * (i : ℂ) + 1) * z)) =O[𝓝 0]
      (fun q : ℝ => q ^ K) := by
  have h := p3q_expand
    (d := fun q i => (2 * (i : ℂ) + 1) ^ 2 + if i = 0 then (q : ℂ) else 0) (β := 1)
    (by norm_num) (by norm_num)
    (a := fun q => (mathieuA (2 * n + 1) q : ℂ))
    (A := fun q i => mathieuFourierA (2 * n + 1) (2 * i + 1) q)
    hnN hNK hK (Eventually.of_forall (p3q_rec_AO n)) (Eventually.of_forall (p3q_lim_AO n))
    (Eventually.of_forall (p3q_ne_AO n)) (p3q_gap_AO n) hvN hvn hv hr
    (w := fun _ => 1) (fun i => by norm_num)
    (Eventually.of_forall fun q => by simpa using hasSum_mathieuFourierA_odd_sq n q)
    (u := fun _ => 1) (Bu := 1) (Ru := 1) zero_le_one le_rfl (fun i => by simp) rfl
    (Eventually.of_forall fun q => ⟨mathieuCeZero (2 * n + 1) q, mathieuCeZero_pos _ _, by
      simpa [mathieuCe_zero] using hasSum_mathieuCe_odd n q 0⟩)
    (c₀ := 1) one_pos (by rw [Complex.ofReal_one]; exact hc) hcn
    (g := fun i => Complex.cos ((2 * (i : ℂ) + 1) * z)) (B := Real.exp (2 * |z.im|))
    (R := Real.exp (2 * |z.im|)) (by positivity) (Real.one_le_exp (by positivity))
    (fun i => by simpa using (p3q_trig_bound z (δ := 1) (by norm_num) i).1)
  refine h.congr_left fun q => ?_
  rw [(hasSum_mathieuCe_odd n q z).tsum_eq]

/-- `se_{2n+1}` from a trial vector for recurrence 28.4.7. -/
theorem p3q_expand_BO (n : ℕ) {N K : ℕ} (hnN : n < N) (hNK : N ≤ n + K)
    (hK : 1 ≤ K) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ} (hvN : ∀ q i, N ≤ i → v q i = 0)
    (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => p3qL (fun i => (2 * (i : ℂ) + 1) ^ 2 -
      if i = 0 then (q : ℂ) else 0) 1 q (v q) i - p q * v q i) =O[𝓝 0] (fun q : ℝ => q ^ K))
    {c : ℝ → ℂ} (hc : Tendsto c (𝓝 0) (𝓝 1))
    (hcn : (fun q => c q ^ 2 * ∑ i ∈ Finset.range N, 1 * v q i ^ 2 - 1)
      =O[𝓝 0] (fun q : ℝ => q ^ K)) (z : ℂ) :
    (fun q : ℝ => mathieuSe (2 * n + 1) z q -
      c q * ∑ i ∈ Finset.range N, v q i * Complex.sin ((2 * (i : ℂ) + 1) * z)) =O[𝓝 0]
      (fun q : ℝ => q ^ K) := by
  have hm : ((2 * n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * n + 1 ≠ 0)
  have h := p3q_expand
    (d := fun q i => (2 * (i : ℂ) + 1) ^ 2 - if i = 0 then (q : ℂ) else 0) (β := 1)
    (by norm_num) (by norm_num)
    (a := fun q => (mathieuB (2 * n + 1) q : ℂ))
    (A := fun q i => mathieuFourierB (2 * n + 1) (2 * i + 1) q)
    hnN hNK hK (Eventually.of_forall (p3q_rec_BO n)) (Eventually.of_forall (p3q_lim_BO n))
    (Eventually.of_forall (p3q_ne_BO n)) (p3q_gap_BO n) hvN hvn hv hr
    (w := fun _ => 1) (fun i => by norm_num)
    (Eventually.of_forall fun q => by simpa using hasSum_mathieuFourierB_odd_sq n q)
    (u := fun i => ((2 * i + 1 : ℕ) : ℂ) / ((2 * n + 1 : ℕ) : ℂ)) (Bu := 2) (Ru := 2)
    (by norm_num) (by norm_num) (p3q_u_bound 1 (by norm_num) n) (div_self hm)
    (Eventually.of_forall fun q => ⟨mathieuSeDerivZero (2 * n + 1) q / (2 * n + 1 : ℕ),
      div_pos (mathieuSeDerivZero_pos _ _) (by positivity), by
      have := (p3q_hasSum_deriv_se_odd n q).div_const ((2 * n + 1 : ℕ) : ℂ)
      push_cast at this ⊢
      convert this using 2 with i
      ring⟩)
    (c₀ := 1) one_pos (by rw [Complex.ofReal_one]; exact hc) hcn
    (g := fun i => Complex.sin ((2 * (i : ℂ) + 1) * z)) (B := Real.exp (2 * |z.im|))
    (R := Real.exp (2 * |z.im|)) (by positivity) (Real.one_le_exp (by positivity))
    (fun i => by simpa using (p3q_trig_bound z (δ := 1) (by norm_num) i).2)
  refine h.congr_left fun q => ?_
  rw [(hasSum_mathieuSe_odd n q z).tsum_eq]

/-- `se_{2n+2}` from a trial vector for recurrence 28.4.8. -/
theorem p3q_expand_BE (n : ℕ) {N K : ℕ} (hnN : n < N) (hNK : N ≤ n + K)
    (hK : 1 ≤ K) {p : ℝ → ℂ} {v : ℝ → ℕ → ℂ} (hvN : ∀ q i, N ≤ i → v q i = 0)
    (hvn : ∀ q, v q n = 1)
    (hv : ∀ i < N + 1, (fun q => v q i) =O[𝓝 0] (fun _ => (1 : ℝ)))
    (hr : ∀ i < N + 1, (fun q : ℝ => p3qL (fun i => (2 * (i : ℂ) + 2) ^ 2) 1 q (v q) i -
      p q * v q i) =O[𝓝 0] (fun q : ℝ => q ^ K))
    {c : ℝ → ℂ} (hc : Tendsto c (𝓝 0) (𝓝 1))
    (hcn : (fun q => c q ^ 2 * ∑ i ∈ Finset.range N, 1 * v q i ^ 2 - 1)
      =O[𝓝 0] (fun q : ℝ => q ^ K)) (z : ℂ) :
    (fun q : ℝ => mathieuSe (2 * n + 2) z q -
      c q * ∑ i ∈ Finset.range N, v q i * Complex.sin ((2 * (i : ℂ) + 2) * z)) =O[𝓝 0]
      (fun q : ℝ => q ^ K) := by
  have hm : ((2 * n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * n + 2 ≠ 0)
  have h := p3q_expand
    (d := fun _ i => (2 * (i : ℂ) + 2) ^ 2) (β := 1) (by norm_num) (by norm_num)
    (a := fun q => (mathieuB (2 * n + 2) q : ℂ))
    (A := fun q i => mathieuFourierB (2 * n + 2) (2 * i + 2) q)
    hnN hNK hK (Eventually.of_forall (p3q_rec_BE n)) (Eventually.of_forall (p3q_lim_BE n))
    (Eventually.of_forall (p3q_ne_BE n)) (p3q_gap_BE n) hvN hvn hv hr
    (w := fun _ => 1) (fun i => by norm_num)
    (Eventually.of_forall fun q => by simpa using hasSum_mathieuFourierB_even_sq n q)
    (u := fun i => ((2 * i + 2 : ℕ) : ℂ) / ((2 * n + 2 : ℕ) : ℂ)) (Bu := 2) (Ru := 2)
    (by norm_num) (by norm_num) (p3q_u_bound 2 (by norm_num) n) (div_self hm)
    (Eventually.of_forall fun q => ⟨mathieuSeDerivZero (2 * n + 2) q / (2 * n + 2 : ℕ),
      div_pos (mathieuSeDerivZero_pos _ _) (by positivity), by
      have := (p3q_hasSum_deriv_se_even n q).div_const ((2 * n + 2 : ℕ) : ℂ)
      push_cast at this ⊢
      convert this using 2 with i
      ring⟩)
    (c₀ := 1) one_pos (by rw [Complex.ofReal_one]; exact hc) hcn
    (g := fun i => Complex.sin ((2 * (i : ℂ) + 2) * z)) (B := Real.exp (2 * |z.im|))
    (R := Real.exp (2 * |z.im|)) (by positivity) (Real.one_le_exp (by positivity))
    (fun i => by simpa using (p3q_trig_bound z (δ := 2) (by norm_num) i).2)
  refine h.congr_left fun q => ?_
  rw [(hasSum_mathieuSe_even n q z).tsum_eq]

end DLMF.Mathieu
