/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.SeriesProperties
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Convergence tools for double power series (Appell functions, DLMF §16.13)

Subexponential Pochhammer ratio bounds, geometric domination of double series, and a
generic theorem turning a locally dominated double power series into a sum that is
jointly analytic in both variables. Joint analyticity uses the pinned TauCeti several-variable
form `DifferentiableOn.analyticAt_of_finiteDimensional` together with the local
`differentiableOn_tsum_of_locally_dominated`.
-/

@[expose] public noncomputable section
open Complex Filter Set
open scoped Topology Nat
namespace DLMF.Hypergeometric

/-- For every `σ > 1` and every `k` there is `τ > 1` with `τ ^ k ≤ σ`. -/
theorem ghaR4_exists_pow_le {σ : ℝ} (hσ : 1 < σ) (k : ℕ) : ∃ τ : ℝ, 1 < τ ∧ τ ^ k ≤ σ := by
  have h : Tendsto (fun t : ℝ => t ^ k) (𝓝[>] 1) (𝓝 1) := by
    have := (continuous_pow k).tendsto (1 : ℝ)
    rw [one_pow] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨τ, hτ1, hτ2⟩ := ((h.eventually (gt_mem_nhds hσ)).and self_mem_nhdsWithin).exists
  exact ⟨τ, hτ2, hτ1.le⟩

/-- Pochhammer symbols grow at most subexponentially faster than one with a regular
parameter: `‖(μ)ₘ‖ ≤ C σ^m ‖(ν)ₘ‖` for every `σ > 1`. -/
theorem ghaR4_norm_poch_le (μ ν : ℂ) (hν : ∀ k : ℕ, ν ≠ -k) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, ‖poch μ m‖ ≤ C * σ ^ m * ‖poch ν m‖ := by
  obtain ⟨K, hK⟩ := exists_nat_ge ((‖μ‖ + σ * ‖ν‖) / (σ - 1))
  have hpos : ∀ j, 0 < ‖poch ν j‖ := fun j => norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat hν j)
  set C := ∑ j ∈ Finset.range (K + 1), ‖poch μ j‖ / ‖poch ν j‖ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => div_nonneg (norm_nonneg _) (hpos j).le
  have hsmall : ∀ j ≤ K, ‖poch μ j‖ ≤ C * ‖poch ν j‖ := by
    intro j hj
    have h1 : ‖poch μ j‖ / ‖poch ν j‖ ≤ C :=
      Finset.single_le_sum (f := fun j => ‖poch μ j‖ / ‖poch ν j‖)
        (fun j _ => div_nonneg (norm_nonneg _) (hpos j).le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    rwa [div_le_iff₀ (hpos j)] at h1
  have hstep : ∀ k : ℕ, K ≤ k → ‖μ + k‖ ≤ σ * ‖ν + k‖ := by
    intro k hk
    have h1 : ‖μ + k‖ ≤ ‖μ‖ + k := by
      calc ‖μ + k‖ ≤ ‖μ‖ + ‖(k : ℂ)‖ := norm_add_le _ _
        _ = ‖μ‖ + k := by rw [Complex.norm_natCast]
    have h2 : (k : ℝ) - ‖ν‖ ≤ ‖ν + k‖ := by
      have := norm_sub_norm_le ((k : ℂ)) (-ν)
      rwa [norm_neg, sub_neg_eq_add, add_comm, Complex.norm_natCast] at this
    have hk' : (‖μ‖ + σ * ‖ν‖) / (σ - 1) ≤ k := hK.trans (by exact_mod_cast hk)
    rw [div_le_iff₀ (by linarith)] at hk'
    nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ σ)]
  refine ⟨C, hC0, fun m => ?_⟩
  induction m with
  | zero => simpa using hsmall 0 (Nat.zero_le _)
  | succ m ih =>
    by_cases hm : m + 1 ≤ K
    · calc ‖poch μ (m + 1)‖ ≤ C * ‖poch ν (m + 1)‖ := hsmall _ hm
        _ ≤ C * σ ^ (m + 1) * ‖poch ν (m + 1)‖ := by
          have h1 : C ≤ C * σ ^ (m + 1) := le_mul_of_one_le_right hC0 (one_le_pow₀ hσ.le)
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    · rw [poch_succ, poch_succ, norm_mul, norm_mul]
      have := hstep m (by omega)
      calc ‖poch μ m‖ * ‖μ + m‖ ≤ (C * σ ^ m * ‖poch ν m‖) * (σ * ‖ν + m‖) :=
            mul_le_mul ih this (norm_nonneg _) (by positivity)
        _ = C * σ ^ (m + 1) * (‖poch ν m‖ * ‖ν + m‖) := by ring

/-- `‖(μ)ₘ‖ ≤ C σ^m m!` for every `σ > 1`. -/
theorem ghaR4_norm_poch_le_factorial (μ : ℂ) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, ‖poch μ m‖ ≤ C * σ ^ m * (m ! : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := ghaR4_norm_poch_le μ 1 (fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]) hσ
  refine ⟨C, hC0, fun m => ?_⟩
  simpa [poch_nat_one, Complex.norm_natCast] using hC m

/-- `m! ≤ C σ^m ‖(ν)ₘ‖` for a regular `ν` and every `σ > 1`. -/
theorem ghaR4_factorial_le_norm_poch (ν : ℂ) (hν : ∀ k : ℕ, ν ≠ -k) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, (m ! : ℝ) ≤ C * σ ^ m * ‖poch ν m‖ := by
  obtain ⟨C, hC0, hC⟩ := ghaR4_norm_poch_le 1 ν hν hσ
  refine ⟨C, hC0, fun m => ?_⟩
  simpa [poch_nat_one, Complex.norm_natCast] using hC m

/-- A single binomial term is bounded by the full binomial power. -/
lemma ghaR4_choose_mul_pow_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (m n : ℕ) :
    ((m + n).choose m : ℝ) * u ^ m * v ^ n ≤ (u + v) ^ (m + n) := by
  rw [add_pow]
  have h := Finset.single_le_sum (f := fun k => u ^ k * v ^ (m + n - k) * ((m + n).choose k : ℝ))
    (fun k _ => by positivity) (Finset.mem_range.mpr (by omega : m < m + n + 1))
  simp only [show m + n - m = n by omega] at h
  linarith

/-- Geometric domination of a nonnegative double sequence. -/
lemma ghaR4_summable_of_geom_bound {f : ℕ × ℕ → ℝ} {C s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1)
    (hf0 : ∀ q, 0 ≤ f q) (hf : ∀ q, f q ≤ C * s ^ (q.1 + q.2)) : Summable f := by
  have hg := summable_geometric_of_lt_one hs0 hs
  have hprod : Summable fun q : ℕ × ℕ => s ^ q.1 * s ^ q.2 :=
    hg.mul_of_nonneg hg (fun _ => pow_nonneg hs0 _) (fun _ => pow_nonneg hs0 _)
  refine Summable.of_nonneg_of_le hf0 (fun q => (hf q).trans_eq ?_) (hprod.mul_left C)
  rw [pow_add]

/-- A double power series dominated on a polydisc around each point of `U` converges there,
and its sum is jointly analytic on `U`. -/
theorem ghaR4_double_series_hasSum_analytic (c : ℕ × ℕ → ℂ) (U : Set (ℂ × ℂ))
    (h : ∀ p ∈ U, ∃ A B : ℝ, ‖p.1‖ < A ∧ ‖p.2‖ < B ∧
      Summable (fun q : ℕ × ℕ => ‖c q‖ * A ^ q.1 * B ^ q.2)) :
    (∀ p ∈ U, HasSum (fun q : ℕ × ℕ => c q * p.1 ^ q.1 * p.2 ^ q.2)
        (∑' q : ℕ × ℕ, c q * p.1 ^ q.1 * p.2 ^ q.2)) ∧
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => ∑' q : ℕ × ℕ, c q * p.1 ^ q.1 * p.2 ^ q.2) U := by
  have key : ∀ p ∈ U, ∃ V : Set (ℂ × ℂ), IsOpen V ∧ p ∈ V ∧ ∃ u : ℕ × ℕ → ℝ, Summable u ∧
      ∀ q, ∀ z ∈ V, ‖c q * z.1 ^ q.1 * z.2 ^ q.2‖ ≤ u q := by
    intro p hp
    obtain ⟨A, B, hA, hB, hs⟩ := h p hp
    refine ⟨{z | ‖z.1‖ < A ∧ ‖z.2‖ < B}, ?_, ⟨hA, hB⟩, _, hs, fun q z hz => ?_⟩
    · exact (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
        (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)
    · rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖z.1‖ ^ q.1 ≤ A ^ q.1 := pow_le_pow_left₀ (norm_nonneg _) hz.1.le _
      have h2 : ‖z.2‖ ^ q.2 ≤ B ^ q.2 := pow_le_pow_left₀ (norm_nonneg _) hz.2.le _
      have hA0 : 0 ≤ A := (norm_nonneg _).trans hz.1.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h2 (by positivity)
        (by positivity)
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨V, -, hpV, u, hu, hle⟩ := key p hp
    exact (Summable.of_norm_bounded hu fun q => hle q p hpV).hasSum
  · obtain ⟨V, hV, hpV, u, hu, hle⟩ := key p hp
    have hd : DifferentiableOn ℂ
        (fun z : ℂ × ℂ => ∑' q : ℕ × ℕ, c q * z.1 ^ q.1 * z.2 ^ q.2) V :=
      differentiableOn_tsum_of_locally_dominated hV
        (fun q => by fun_prop) (fun z hz => ⟨V, hV.mem_nhds hz, u, hu, hle⟩)
    exact hd.analyticAt_of_finiteDimensional (hV.mem_nhds hpV)

/-- Local domination on the unit bidisc from a subexponential coefficient bound. -/
theorem ghaR4_dom_bidisc (c : ℕ × ℕ → ℂ)
    (hc : ∀ σ : ℝ, 1 < σ → ∃ C : ℝ, ∀ q : ℕ × ℕ, ‖c q‖ ≤ C * σ ^ (q.1 + q.2))
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    ∃ A B : ℝ, ‖x‖ < A ∧ ‖y‖ < B ∧
      Summable (fun q : ℕ × ℕ => ‖c q‖ * A ^ q.1 * B ^ q.2) := by
  set t := (max ‖x‖ ‖y‖ + 1) / 2 with ht
  have hm : max ‖x‖ ‖y‖ < 1 := max_lt hx hy
  have hm0 : 0 ≤ max ‖x‖ ‖y‖ := (norm_nonneg x).trans (le_max_left _ _)
  have ht1 : t < 1 := by rw [ht]; linarith
  have ht0 : 1 / 2 ≤ t := by rw [ht]; linarith
  obtain ⟨C, hC⟩ := hc ((1 + t) / (2 * t)) (by rw [lt_div_iff₀ (by linarith)]; linarith)
  refine ⟨t, t, by rw [ht]; linarith [le_max_left ‖x‖ ‖y‖],
    by rw [ht]; linarith [le_max_right ‖x‖ ‖y‖], ?_⟩
  refine ghaR4_summable_of_geom_bound (C := C) (s := (1 + t) / 2) (by linarith) (by linarith)
    (fun q => by positivity) (fun q => ?_)
  have hst : (1 + t) / (2 * t) * t = (1 + t) / 2 := by field_simp
  calc ‖c q‖ * t ^ q.1 * t ^ q.2 = ‖c q‖ * t ^ (q.1 + q.2) := by rw [pow_add]; ring
    _ ≤ C * ((1 + t) / (2 * t)) ^ (q.1 + q.2) * t ^ (q.1 + q.2) := by
      gcongr; exact hC q
    _ = C * ((1 + t) / 2) ^ (q.1 + q.2) := by rw [mul_assoc, ← mul_pow, hst]

/-- Local domination on the diamond `‖x‖+‖y‖<1` from a binomially weighted bound. -/
theorem ghaR4_dom_diamond (c : ℕ × ℕ → ℂ)
    (hc : ∀ σ : ℝ, 1 < σ → ∃ C : ℝ, ∀ q : ℕ × ℕ,
      ‖c q‖ ≤ C * σ ^ (q.1 + q.2) * ((q.1 + q.2).choose q.1 : ℝ))
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    ∃ A B : ℝ, ‖x‖ < A ∧ ‖y‖ < B ∧
      Summable (fun q : ℕ × ℕ => ‖c q‖ * A ^ q.1 * B ^ q.2) := by
  set δ := (1 - ‖x‖ - ‖y‖) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set t := ‖x‖ + δ + (‖y‖ + δ) with ht
  have hx0 := norm_nonneg x
  have hy0 := norm_nonneg y
  have ht1 : t < 1 := by rw [ht, hδ]; linarith
  have ht0 : 1 / 2 ≤ t := by rw [ht, hδ]; linarith
  obtain ⟨C, hC⟩ := hc ((1 + t) / (2 * t)) (by rw [lt_div_iff₀ (by linarith)]; linarith)
  refine ⟨‖x‖ + δ, ‖y‖ + δ, by linarith, by linarith, ?_⟩
  refine ghaR4_summable_of_geom_bound (C := C) (s := (1 + t) / 2) (by linarith) (by linarith)
    (fun q => by positivity) (fun q => ?_)
  have hst : (1 + t) / (2 * t) * t = (1 + t) / 2 := by field_simp
  have hb := ghaR4_choose_mul_pow_le (u := ‖x‖ + δ) (v := ‖y‖ + δ) (by linarith) (by linarith)
    q.1 q.2
  have hC0 : 0 ≤ C * ((1 + t) / (2 * t)) ^ (q.1 + q.2) := by
    have h1 := (norm_nonneg (c q)).trans (hC q)
    have h2 : (0 : ℝ) < ((q.1 + q.2).choose q.1 : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    exact nonneg_of_mul_nonneg_left h1 h2
  calc ‖c q‖ * (‖x‖ + δ) ^ q.1 * (‖y‖ + δ) ^ q.2
      ≤ C * ((1 + t) / (2 * t)) ^ (q.1 + q.2) * ((q.1 + q.2).choose q.1 : ℝ) *
          (‖x‖ + δ) ^ q.1 * (‖y‖ + δ) ^ q.2 := by gcongr; exact hC q
    _ = C * ((1 + t) / (2 * t)) ^ (q.1 + q.2) *
          (((q.1 + q.2).choose q.1 : ℝ) * (‖x‖ + δ) ^ q.1 * (‖y‖ + δ) ^ q.2) := by ring
    _ ≤ C * ((1 + t) / (2 * t)) ^ (q.1 + q.2) * t ^ (q.1 + q.2) := by
      gcongr
    _ = C * ((1 + t) / 2) ^ (q.1 + q.2) := by rw [mul_assoc, ← mul_pow, hst]

/-- Local domination on the F4 domain `√‖x‖+√‖y‖<1` from a squared-binomial bound. -/
theorem ghaR4_dom_F4 (c : ℕ × ℕ → ℂ)
    (hc : ∀ σ : ℝ, 1 < σ → ∃ C : ℝ, ∀ q : ℕ × ℕ,
      ‖c q‖ ≤ C * σ ^ (q.1 + q.2) * ((q.1 + q.2).choose q.1 : ℝ) ^ 2)
    {x y : ℂ} (hxy : Real.sqrt ‖x‖ + Real.sqrt ‖y‖ < 1) :
    ∃ A B : ℝ, ‖x‖ < A ∧ ‖y‖ < B ∧
      Summable (fun q : ℕ × ℕ => ‖c q‖ * A ^ q.1 * B ^ q.2) := by
  set δ := (1 - Real.sqrt ‖x‖ - Real.sqrt ‖y‖) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hsx := Real.sqrt_nonneg ‖x‖
  have hsy := Real.sqrt_nonneg ‖y‖
  set α := Real.sqrt ‖x‖ + δ with hα
  set β := Real.sqrt ‖y‖ + δ with hβ
  set t := (α + β) ^ 2 with ht
  have hab1 : α + β < 1 := by rw [hα, hβ, hδ]; linarith
  have hab0 : 1 / 2 ≤ α + β := by rw [hα, hβ, hδ]; linarith
  have ht1 : t < 1 := by rw [ht]; nlinarith
  have ht0 : 1 / 4 ≤ t := by rw [ht]; nlinarith
  have hxA : ‖x‖ < α ^ 2 := by
    rw [hα]; nlinarith [Real.sq_sqrt (norm_nonneg x)]
  have hyB : ‖y‖ < β ^ 2 := by
    rw [hβ]; nlinarith [Real.sq_sqrt (norm_nonneg y)]
  obtain ⟨C, hC⟩ := hc ((1 + t) / (2 * t)) (by rw [lt_div_iff₀ (by linarith)]; linarith)
  refine ⟨α ^ 2, β ^ 2, hxA, hyB, ?_⟩
  refine ghaR4_summable_of_geom_bound (C := C) (s := (1 + t) / 2) (by linarith) (by linarith)
    (fun q => by positivity) (fun q => ?_)
  have hst : (1 + t) / (2 * t) * t = (1 + t) / 2 := by field_simp
  have hb := ghaR4_choose_mul_pow_le (u := α) (v := β) (by linarith) (by linarith) q.1 q.2
  have hb2 : (((q.1 + q.2).choose q.1 : ℝ) * α ^ q.1 * β ^ q.2) ^ 2 ≤ t ^ (q.1 + q.2) := by
    rw [ht, ← pow_mul, mul_comm 2, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hb 2
  have hC0 : 0 ≤ C * ((1 + t) / (2 * t)) ^ (q.1 + q.2) := by
    have h1 := (norm_nonneg (c q)).trans (hC q)
    have h2 : (0 : ℝ) < ((q.1 + q.2).choose q.1 : ℝ) ^ 2 := by
      have : (0 : ℝ) < ((q.1 + q.2).choose q.1 : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega)
      positivity
    exact nonneg_of_mul_nonneg_left h1 h2
  calc ‖c q‖ * (α ^ 2) ^ q.1 * (β ^ 2) ^ q.2
      ≤ C * ((1 + t) / (2 * t)) ^ (q.1 + q.2) * ((q.1 + q.2).choose q.1 : ℝ) ^ 2 *
          (α ^ 2) ^ q.1 * (β ^ 2) ^ q.2 := by gcongr; exact hC q
    _ = C * ((1 + t) / (2 * t)) ^ (q.1 + q.2) *
          (((q.1 + q.2).choose q.1 : ℝ) * α ^ q.1 * β ^ q.2) ^ 2 := by
      rw [← pow_mul, ← pow_mul, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 q.1,
        mul_comm 2 q.2]
      ring
    _ ≤ C * ((1 + t) / (2 * t)) ^ (q.1 + q.2) * t ^ (q.1 + q.2) := by gcongr
    _ = C * ((1 + t) / 2) ^ (q.1 + q.2) := by rw [mul_assoc, ← mul_pow, hst]

end DLMF.Hypergeometric
