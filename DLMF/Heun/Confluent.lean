/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Equation

/-!
# Confluent forms of Heun's equation (DLMF §31.12)

The four standard confluent forms 31.12.1–31.12.4 are defined in DLMF/Heun/Basic.lean
(`IsConfluentHeunSolOn`, `IsDoublyConfluentHeunSolOn`, `IsBiconfluentHeunSolOn` with the sign
corrected in DLMF 1.0.7, `IsTriconfluentHeunSolOn`). This file records the classification of
their singular points stated after each equation: at most regular singular points through the
API of `DLMFMathlib.Analysis.ODE.Singularities`, and the ranks of the irregular singularities
through Poincaré's rank (`HasIrregularRankAtInfinity`, `HasIrregularRankAt`). The rank
statements need the leading coefficient to be nonzero (`ε ≠ 0` for 31.12.1, `δ ≠ 0` at `0` for
31.12.2); for other parameters the singularity is weaker.

The remark that Mathieu, spheroidal and Coulomb spheroidal functions are special cases of
solutions of the confluent Heun equation (31.12.1) is not acquired: it is not attached to
explicit transformations in DLMF.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology

noncomputable section

namespace DLMF.Heun

/-- A function with a nonzero limit is not `O(g)` for `g → 0`. -/
lemma p1h_not_isBigO_of_tendsto {l : Filter ℂ} [l.NeBot] {f g : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 0)) : ¬ f =O[l] g := fun h =>
  hc (tendsto_nhds_unique hf (h.trans_tendsto hg))

/-- `z ^ (-n) → 0` at infinity for `n > 0`. -/
lemma p1h_tendsto_zpow_neg_cobounded {n : ℕ} (hn : 0 < n) :
    Tendsto (fun z : ℂ => z ^ (-(n : ℤ))) (Bornology.cobounded ℂ) (𝓝 0) := by
  have h := (tendsto_inv₀_cobounded (α := ℂ)).pow n
  simp only [zero_pow hn.ne'] at h
  refine h.congr fun z => ?_
  simp [zpow_neg, inv_pow]

/-- If `f / g → c ≠ 0` and `g' / g → 0` then `f` is not `O(g')`. -/
lemma p1h_not_isBigO_of_div {l : Filter ℂ} [l.NeBot] {f g g' : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hf : Tendsto (fun z => f z / g z) l (𝓝 c)) (hg : Tendsto (fun z => g' z / g z) l (𝓝 0)) :
    ¬ f =O[l] g' := fun h =>
  p1h_not_isBigO_of_tendsto hc hf hg
    (by simpa [div_eq_mul_inv] using h.mul (isBigO_refl (fun z => (g z)⁻¹) l))

/-- `f = O(g)` from a limit of `f / g`, for `g` eventually nonzero. -/
lemma p1h_isBigO_of_div {l : Filter ℂ} {f g : ℂ → ℂ} {c : ℂ}
    (hf : Tendsto (fun z => f z / g z) l (𝓝 c)) (hg : ∀ᶠ z in l, g z ≠ 0) : f =O[l] g :=
  isBigO_of_div_tendsto_nhds (hg.mono fun _ hz h => absurd h hz) c hf

/-- DLMF 31.12.1: the confluent Heun equation has at most regular singular points at `z = 0`
and `z = 1`, every other finite point is ordinary, and for `ε ≠ 0` it has an irregular
singularity of rank `1` at `∞`. Coefficients indexed as in `heunODECoeff`. -/
@[dlmf 31.12.E1]
theorem confluentHeun_singularities (q α γ δ ε : ℂ) (hε : ε ≠ 0) :
    let c : Fin 2 → ℂ → ℂ := ![fun z => (α * z - q) / (z * (z - 1)),
      fun z => γ / z + δ / (z - 1) + ε]
    Complex.LinearODEAtMostRegularAt c 0 ∧ Complex.LinearODEAtMostRegularAt c 1 ∧
    (∀ z : ℂ, z ≠ 0 → z ≠ 1 → Complex.LinearODEOrdinaryAt c z) ∧
    HasIrregularRankAtInfinity (fun z => γ / z + δ / (z - 1) + ε)
      (fun z => (α * z - q) / (z * (z - 1))) 1 := by
  intro c
  have hm1 : (0 : ℂ) - 1 ≠ 0 := by norm_num
  have h1 : (1 : ℂ) ≠ 0 := one_ne_zero
  refine ⟨?_, ?_, fun z hz0 hz1 => ?_, ?_⟩
  · refine p1h_atMostRegular_two (g₀ := fun z => z * (α * z - q) / (z - 1))
      (g₁ := fun z => γ + z * δ / (z - 1) + z * ε) (by fun_prop (disch := simpa))
      (by fun_prop (disch := simpa)) (fun z hz => ?_) (fun z hz => ?_)
    · rw [sub_zero]; field_simp
    · rw [sub_zero]; field_simp
  · refine p1h_atMostRegular_two (g₀ := fun z => (z - 1) * (α * z - q) / z)
      (g₁ := fun z => (z - 1) * γ / z + δ + (z - 1) * ε) (by fun_prop (disch := simpa))
      (by fun_prop (disch := simpa)) (fun z hz => ?_) (fun z hz => ?_)
    · have hz' : z - 1 ≠ 0 := sub_ne_zero.2 hz
      rcases eq_or_ne z 0 with rfl | hz0
      · simp
      · field_simp
    · have hz' : z - 1 ≠ 0 := sub_ne_zero.2 hz
      rcases eq_or_ne z 0 with rfl | hz0
      · simp; ring
      · field_simp
  · have hz1' : z - 1 ≠ 0 := sub_ne_zero.2 hz1
    exact p1h_ordinary_two (by fun_prop (disch := simp [hz0, hz1']))
      (by fun_prop (disch := simp [hz0, hz1']))
  · have hev : ∀ᶠ z in Bornology.cobounded ℂ, z ≠ 0 ∧ z ≠ 1 :=
      (Bornology.eventually_ne_cobounded 0).and (Bornology.eventually_ne_cobounded 1)
    have hp : Tendsto (fun z => γ / z + δ / (z - 1) + ε) (Bornology.cobounded ℂ) (𝓝 ε) := by
      have h : Tendsto (fun u => γ * u + δ * u / (1 - u) + ε) (𝓝 0)
          (𝓝 (γ * 0 + δ * 0 / (1 - 0) + ε)) := by
        apply ContinuousAt.tendsto
        fun_prop (disch := norm_num)
      simp only [mul_zero, zero_div, zero_add] at h
      refine (h.comp tendsto_inv₀_cobounded).congr' ?_
      filter_upwards [hev] with z ⟨hz0, hz1⟩
      have hz1' : z - 1 ≠ 0 := sub_ne_zero.2 hz1
      simp only [Function.comp_apply]
      field_simp
    have hr : Tendsto (fun z => (α * z - q) / (z * (z - 1))) (Bornology.cobounded ℂ) (𝓝 0) := by
      have h : Tendsto (fun u => (α * u - q * u ^ 2) / (1 - u)) (𝓝 0)
          (𝓝 ((α * 0 - q * 0 ^ 2) / (1 - 0))) := by
        apply ContinuousAt.tendsto
        fun_prop (disch := norm_num)
      simp only [mul_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        sub_zero] at h
      refine (h.comp tendsto_inv₀_cobounded).congr' ?_
      filter_upwards [hev] with z ⟨hz0, hz1⟩
      have hz1' : z - 1 ≠ 0 := sub_ne_zero.2 hz1
      simp only [Function.comp_apply]
      field_simp
    refine ⟨le_rfl, ?_, ?_, ?_⟩
    · simpa using hp.isBigO_one ℂ
    · simpa using hr.isBigO_one ℂ
    · rintro ⟨h, -⟩
      exact p1h_not_isBigO_of_tendsto hε hp (p1h_tendsto_zpow_neg_cobounded (n := 1) one_pos)
        (by simpa using h)

/-- DLMF 31.12.2: the doubly-confluent Heun equation has irregular singularities of rank `1` at
`z = 0` (for `δ ≠ 0`) and at `∞`, and every other finite point is ordinary. -/
@[dlmf 31.12.E2]
theorem doublyConfluentHeun_singularities (q α γ δ : ℂ) (hδ : δ ≠ 0) :
    let c : Fin 2 → ℂ → ℂ := ![fun z => (α * z - q) / z ^ 2, fun z => δ / z ^ 2 + γ / z + 1]
    (∀ z : ℂ, z ≠ 0 → Complex.LinearODEOrdinaryAt c z) ∧
    HasIrregularRankAt (fun z => δ / z ^ 2 + γ / z + 1) (fun z => (α * z - q) / z ^ 2) 0 1 ∧
    HasIrregularRankAtInfinity (fun z => δ / z ^ 2 + γ / z + 1)
      (fun z => (α * z - q) / z ^ 2) 1 := by
  intro c
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0 := self_mem_nhdsWithin
  have hevi : ∀ᶠ z in Bornology.cobounded ℂ, z ≠ 0 := Bornology.eventually_ne_cobounded 0
  refine ⟨fun z hz0 => ?_, ?_, ?_⟩
  · exact p1h_ordinary_two (by fun_prop (disch := simp [hz0]))
      (by fun_prop (disch := simp [hz0]))
  · have hp : Tendsto (fun z => (δ / z ^ 2 + γ / z + 1) / (z - 0) ^ (-((1 : ℕ) : ℤ) - 1))
        (𝓝[≠] 0) (𝓝 δ) := by
      have h : Tendsto (fun z : ℂ => δ + γ * z + z ^ 2) (𝓝 0) (𝓝 (δ + γ * 0 + 0 ^ 2)) :=
        (by fun_prop : Continuous fun z : ℂ => δ + γ * z + z ^ 2).tendsto 0
      simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] at h
      refine (tendsto_nhdsWithin_of_tendsto_nhds h).congr' ?_
      filter_upwards [hev] with z hz
      rw [sub_zero]
      norm_num [zpow_neg]
      field_simp
    have hr : Tendsto (fun z => (α * z - q) / z ^ 2 / (z - 0) ^ (-2 * ((1 : ℕ) : ℤ) - 2))
        (𝓝[≠] 0) (𝓝 0) := by
      have h : Tendsto (fun z : ℂ => (α * z - q) * z ^ 2) (𝓝 0) (𝓝 ((α * 0 - q) * 0 ^ 2)) :=
        (by fun_prop : Continuous fun z : ℂ => (α * z - q) * z ^ 2).tendsto 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h
      refine (tendsto_nhdsWithin_of_tendsto_nhds h).congr' ?_
      filter_upwards [hev] with z hz
      rw [sub_zero]
      norm_num [zpow_neg]
      field_simp
    have hz : Tendsto (fun z : ℂ => (z - 0) ^ (-((1 : ℕ) : ℤ)) / (z - 0) ^ (-((1 : ℕ) : ℤ) - 1))
        (𝓝[≠] 0) (𝓝 0) := by
      have h : Tendsto (fun z : ℂ => z) (𝓝 0) (𝓝 0) := tendsto_id
      refine (tendsto_nhdsWithin_of_tendsto_nhds h).congr' ?_
      filter_upwards [hev] with z hz
      rw [sub_zero]
      norm_num [zpow_neg]
      field_simp
    refine ⟨le_rfl, p1h_isBigO_of_div hp ?_, p1h_isBigO_of_div hr ?_, ?_⟩
    · filter_upwards [hev] with z hz; simp [hz]
    · filter_upwards [hev] with z hz; simp [hz]
    · rintro ⟨h, -⟩
      exact p1h_not_isBigO_of_div hδ hp hz h
  · have hp : Tendsto (fun z => δ / z ^ 2 + γ / z + 1) (Bornology.cobounded ℂ) (𝓝 1) := by
      have h : Tendsto (fun u : ℂ => δ * u ^ 2 + γ * u + 1) (𝓝 0)
          (𝓝 (δ * 0 ^ 2 + γ * 0 + 1)) :=
        (by fun_prop : Continuous fun u : ℂ => δ * u ^ 2 + γ * u + 1).tendsto 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        add_zero, zero_add] at h
      refine (h.comp tendsto_inv₀_cobounded).congr' ?_
      filter_upwards [hevi] with z hz
      simp only [Function.comp_apply]
      field_simp
    have hr : Tendsto (fun z => (α * z - q) / z ^ 2) (Bornology.cobounded ℂ) (𝓝 0) := by
      have h : Tendsto (fun u : ℂ => α * u - q * u ^ 2) (𝓝 0) (𝓝 (α * 0 - q * 0 ^ 2)) :=
        (by fun_prop : Continuous fun u : ℂ => α * u - q * u ^ 2).tendsto 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        sub_zero] at h
      refine (h.comp tendsto_inv₀_cobounded).congr' ?_
      filter_upwards [hevi] with z hz
      simp only [Function.comp_apply]
      field_simp
    refine ⟨le_rfl, ?_, ?_, ?_⟩
    · simpa using hp.isBigO_one ℂ
    · simpa using hr.isBigO_one ℂ
    · rintro ⟨h, -⟩
      exact p1h_not_isBigO_of_tendsto one_ne_zero hp
        (p1h_tendsto_zpow_neg_cobounded (n := 1) one_pos) (by simpa using h)

/-- DLMF 31.12.3: the biconfluent Heun equation (sign as corrected in DLMF 1.0.7) has an at
most regular singular point at `z = 0`, every other finite point is ordinary, and it has an
irregular singularity of rank `2` at `∞`. -/
@[dlmf 31.12.E3]
theorem biconfluentHeun_singularities (q α γ δ : ℂ) :
    let c : Fin 2 → ℂ → ℂ := ![fun z => (α * z - q) / z, fun z => -(γ / z + δ + z)]
    Complex.LinearODEAtMostRegularAt c 0 ∧
    (∀ z : ℂ, z ≠ 0 → Complex.LinearODEOrdinaryAt c z) ∧
    HasIrregularRankAtInfinity (fun z => -(γ / z + δ + z)) (fun z => (α * z - q) / z) 2 := by
  intro c
  have hevi : ∀ᶠ z in Bornology.cobounded ℂ, z ≠ 0 := Bornology.eventually_ne_cobounded 0
  refine ⟨?_, fun z hz0 => ?_, ?_⟩
  · refine p1h_atMostRegular_two (g₀ := fun z => z * (α * z - q))
      (g₁ := fun z => -(γ + δ * z + z ^ 2)) (by fun_prop) (by fun_prop)
      (fun z hz => ?_) (fun z hz => ?_)
    · rw [sub_zero]; field_simp
    · rw [sub_zero]; field_simp
  · exact p1h_ordinary_two (by fun_prop (disch := simp [hz0]))
      (by fun_prop (disch := simp [hz0]))
  · have hp : Tendsto (fun z => -(γ / z + δ + z) / z ^ ((2 : ℕ) - 1 : ℤ))
        (Bornology.cobounded ℂ) (𝓝 (-1)) := by
      have h : Tendsto (fun u : ℂ => -(γ * u ^ 2 + δ * u + 1)) (𝓝 0)
          (𝓝 (-(γ * 0 ^ 2 + δ * 0 + 1))) :=
        (by fun_prop : Continuous fun u : ℂ => -(γ * u ^ 2 + δ * u + 1)).tendsto 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        add_zero, zero_add] at h
      refine (h.comp tendsto_inv₀_cobounded).congr' ?_
      filter_upwards [hevi] with z hz
      simp only [Function.comp_apply]
      norm_num
      field_simp
    have hr : Tendsto (fun z => (α * z - q) / z / z ^ (2 * ((2 : ℕ) : ℤ) - 2))
        (Bornology.cobounded ℂ) (𝓝 0) := by
      have h : Tendsto (fun u : ℂ => α * u ^ 2 - q * u ^ 3) (𝓝 0)
          (𝓝 (α * 0 ^ 2 - q * 0 ^ 3)) :=
        (by fun_prop : Continuous fun u : ℂ => α * u ^ 2 - q * u ^ 3).tendsto 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        sub_zero] at h
      refine (h.comp tendsto_inv₀_cobounded).congr' ?_
      filter_upwards [hevi] with z hz
      simp only [Function.comp_apply]
      norm_num
      field_simp
    have hz : Tendsto (fun z : ℂ => z ^ ((2 : ℕ) - 2 : ℤ) / z ^ ((2 : ℕ) - 1 : ℤ))
        (Bornology.cobounded ℂ) (𝓝 0) := by
      refine (tendsto_inv₀_cobounded (α := ℂ)).congr' ?_
      filter_upwards [hevi] with z hz
      norm_num
    refine ⟨by norm_num, p1h_isBigO_of_div hp ?_, p1h_isBigO_of_div hr ?_, ?_⟩
    · filter_upwards [hevi] with z hz; simp [hz]
    · filter_upwards [hevi] with z hz; simp [hz]
    · rintro ⟨h, -⟩
      exact p1h_not_isBigO_of_div (by norm_num) hp hz h

/-- DLMF 31.12.4: the triconfluent Heun equation has no finite singular points (every finite
point is ordinary). -/
@[dlmf 31.12.E4]
theorem triconfluentHeun_ordinary (q α γ : ℂ) (z : ℂ) :
    Complex.LinearODEOrdinaryAt (![fun z => α * z - q, fun z => (γ + z) * z] : Fin 2 → ℂ → ℂ)
      z := by
  intro j
  refine ⟨(![fun z => α * z - q, fun z => (γ + z) * z] : Fin 2 → ℂ → ℂ) j, ?_,
    Filter.EventuallyEq.rfl⟩
  fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    fun_prop
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    fun_prop

/-- DLMF 31.12.4: the triconfluent Heun equation has an irregular singularity of rank `3` at
`∞`. -/
@[dlmf 31.12.E4]
theorem triconfluentHeun_rank_infinity (q α γ : ℂ) :
    HasIrregularRankAtInfinity (fun z => (γ + z) * z) (fun z => α * z - q) 3 := by
  have h1 := eventually_cobounded_le_norm (E := ℂ) 1
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · norm_num
    refine IsBigO.of_bound (‖γ‖ + 1) ?_
    filter_upwards [h1] with z hz
    rw [norm_mul, norm_pow, sq]
    have : ‖γ + z‖ ≤ (‖γ‖ + 1) * ‖z‖ := by
      calc ‖γ + z‖ ≤ ‖γ‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ‖γ‖ * ‖z‖ + ‖z‖ := by nlinarith [norm_nonneg γ]
        _ = _ := by ring
    nlinarith [norm_nonneg z]
  · norm_num
    refine IsBigO.of_bound (‖α‖ + ‖q‖) ?_
    filter_upwards [h1] with z hz
    rw [norm_pow]
    have h4 : ‖z‖ ≤ ‖z‖ ^ 4 := by
      calc ‖z‖ = ‖z‖ ^ 1 := (pow_one _).symm
        _ ≤ ‖z‖ ^ 4 := pow_le_pow_right₀ hz (by norm_num)
    have h4' : 1 ≤ ‖z‖ ^ 4 := one_le_pow₀ hz
    calc ‖α * z - q‖ ≤ ‖α‖ * ‖z‖ + ‖q‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ ‖α‖ * ‖z‖ ^ 4 + ‖q‖ * ‖z‖ ^ 4 := by
          gcongr
          · nlinarith [norm_nonneg q]
      _ = _ := by ring
  · rintro ⟨hp, -⟩
    norm_num at hp
    obtain ⟨c, hc⟩ := hp.bound
    have h2 := eventually_cobounded_le_norm (E := ℂ) (max 1 (|c| + ‖γ‖ + 1))
    obtain ⟨z, hz, hz2⟩ := (hc.and h2).exists
    have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hz2
    have hz3 : |c| + ‖γ‖ + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz2
    rw [norm_mul] at hz
    have hpos : 0 < ‖z‖ := by linarith
    have : ‖γ + z‖ ≤ c := by
      have := le_of_mul_le_mul_right (a := ‖z‖) (by simpa using hz) hpos
      exact this
    have : ‖z‖ - ‖γ‖ ≤ ‖γ + z‖ := by
      have := norm_sub_norm_le z (-γ)
      simpa [sub_neg_eq_add, add_comm] using this
    linarith [le_abs_self c]

end DLMF.Heun
