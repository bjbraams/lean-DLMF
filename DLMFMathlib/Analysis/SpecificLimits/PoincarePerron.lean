/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Tactic.LinearCombination

/-!
# Perron's and Pincherle's theorems for three-term recurrences

A solution of a second-order linear recurrence whose coefficients converge, and whose limiting
characteristic roots `ρ₁, ρ₂` have distinct moduli with `‖ρ₂‖ > 1`, is either unbounded,
eventually zero, or satisfies `x_{p+1}/x_p → ρ₁` (the minimal solution). This is the case of
the Poincaré–Perron theorem needed for the coefficients of Fourier expansions defined by
three-term recurrences.

The proof follows the two combinations `y_p = x_{p+1} - ρ₂x_p` and `z_p = x_{p+1} - ρ₁x_p`,
which satisfy `y_{p+1} ≈ ρ₁y_p` and `z_{p+1} ≈ ρ₂z_p`: the cone `‖y‖ ≤ ‖z‖` is invariant and
forces geometric growth, and otherwise `‖z_p‖/‖y_p‖ → 0`.

## Main results

* `tendsto_succ_div_of_recurrence_of_bounded`: `x_{p+1}/x_p → ρ₁` for a bounded solution of
  `x_{p+2} + a_p x_{p+1} + b_p x_p = 0` that is not eventually zero.
* `tendsto_succ_div_of_three_term_recurrence_of_bounded`: the same for
  `γ_p x_p + β_p x_{p+1} + α_p x_{p+2} = 0`.
* `tendsto_nestedFraction_of_minimal`: Pincherle's theorem, the convergence of the continued
  fraction `α_pγ_{p+1}/(β_{p+1} - α_{p+1}γ_{p+2}/(β_{p+2} - ⋯))` to `-α_p f_{p+1}/f_p` for a
  solution `f` with `f_{q+1}/f_q → ρ ∈ (0, 1)`.
-/

@[expose] public section

open Filter
open scoped Topology

/-- The dichotomy behind Perron's theorem, for the norms `u = ‖y‖`, `v = ‖z‖` of the two
characteristic combinations of a solution: either `u` and `v` vanish together infinitely often,
or eventually `v < u` and `v/u → 0`. -/
private theorem norm_dichotomy_of_le_mul_add {u v : ℕ → ℝ} {r₁ r₂ : ℝ} (hu : ∀ p, 0 ≤ u p)
    (hv : ∀ p, 0 ≤ v p) (hr₁ : 0 ≤ r₁) (hr : r₁ < r₂) (hr₂ : 1 < r₂) {C : ℝ}
    (hvb : ∀ p, v p ≤ C)
    (hδ : ∀ δ > 0, ∀ᶠ p in atTop,
      r₂ * v p - δ * (u p + v p) ≤ v (p + 1) ∧ u (p + 1) ≤ r₁ * u p + δ * (u p + v p)) :
    (∃ᶠ p in atTop, u p = 0 ∧ v p = 0) ∨
      ((∀ᶠ p in atTop, v p < u p) ∧ Tendsto (fun p => v p / u p) atTop (𝓝 0)) := by
  by_cases hII : ∀ᶠ p in atTop, v p < u p
  · right
    refine ⟨hII, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    set η := min ε 1 with hη
    have hη0 : 0 < η := lt_min hε one_pos
    have hη1 : η ≤ 1 := min_le_right _ _
    set δ := η * (r₂ - r₁) / 8 with hδdef
    have hδ0 : 0 < δ := by positivity
    set l := (r₂ - 2 * δ / η) / (r₁ + 2 * δ) with hl
    have h2δ : 2 * δ / η = (r₂ - r₁) / 4 := by rw [hδdef]; field_simp; ring
    have hden : 0 < r₁ + 2 * δ := by positivity
    have hl1 : 1 < l := by
      rw [hl, lt_div_iff₀ hden, h2δ, one_mul]
      have : 2 * δ ≤ (r₂ - r₁) / 4 := by
        rw [hδdef]; nlinarith
      linarith
    obtain ⟨P, hP⟩ := eventually_atTop.1 (hII.and (hδ δ hδ0))
    refine ⟨P, fun p hp => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hv p) (hu p))]
    refine lt_of_lt_of_le ?_ (min_le_left ε 1)
    by_contra hcon
    replace hcon : η ≤ v p / u p := not_lt.1 hcon
    -- geometric growth of the ratio
    have key : ∀ j : ℕ, l ^ j * η ≤ v (p + j) / u (p + j) := by
      intro j
      induction j with
      | zero => simpa using hcon
      | succ j ih =>
        have hq := hP (p + j) (by omega)
        have hq1 := hP (p + j + 1) (by omega)
        obtain ⟨hvu, h1, h2⟩ := hq
        have hupos : 0 < u (p + j) := lt_of_le_of_lt (hv _) hvu
        have hupos1 : 0 < u (p + j + 1) := lt_of_le_of_lt (hv _) hq1.1
        have hlj : 1 ≤ l ^ j := one_le_pow₀ hl1.le
        have hge : η ≤ v (p + j) / u (p + j) := le_trans (by nlinarith) ih
        rw [le_div_iff₀ hupos] at hge ih
        rw [show p + (j + 1) = p + j + 1 by omega, le_div_iff₀ hupos1]
        -- v_{q+1} ≥ (r₂ - 2δ/η) v_q and u_{q+1} ≤ (r₁ + 2δ) u_q
        have hA : (r₂ - 2 * δ / η) * v (p + j) ≤ v (p + j + 1) := by
          have : 2 * δ * u (p + j) ≤ 2 * δ / η * v (p + j) := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hη0]; nlinarith
          nlinarith
        have hB : u (p + j + 1) ≤ (r₁ + 2 * δ) * u (p + j) := by nlinarith
        have hlpos : 0 ≤ r₂ - 2 * δ / η := by rw [h2δ]; linarith
        calc l ^ (j + 1) * η * u (p + j + 1) ≤ l ^ (j + 1) * η * ((r₁ + 2 * δ) * u (p + j)) := by
              have : 0 ≤ l ^ (j + 1) * η := by positivity
              exact mul_le_mul_of_nonneg_left hB this
          _ = (r₂ - 2 * δ / η) * (l ^ j * η * u (p + j)) := by
              rw [hl, pow_succ]; field_simp
          _ ≤ (r₂ - 2 * δ / η) * v (p + j) := mul_le_mul_of_nonneg_left ih hlpos
          _ ≤ v (p + j + 1) := hA
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / η) hl1
    have h1 := key j
    have hq := (hP (p + j) (by omega)).1
    have hupos : 0 < u (p + j) := lt_of_le_of_lt (hv _) hq
    rw [div_lt_iff₀ hη0] at hj
    have : v (p + j) / u (p + j) < 1 := (div_lt_one hupos).2 hq
    linarith
  · left
    rw [not_eventually] at hII
    set δ := min (r₂ - r₁) (r₂ - 1) / 4 with hδdef
    have hδ0 : 0 < δ := by
      have : 0 < min (r₂ - r₁) (r₂ - 1) := lt_min (by linarith) (by linarith)
      positivity
    have hδ1 : 4 * δ ≤ r₂ - r₁ := by rw [hδdef]; linarith [min_le_left (r₂ - r₁) (r₂ - 1)]
    have hδ2 : 4 * δ ≤ r₂ - 1 := by rw [hδdef]; linarith [min_le_right (r₂ - r₁) (r₂ - 1)]
    obtain ⟨Q, hQ⟩ := eventually_atTop.1 (hδ δ hδ0)
    rw [Filter.frequently_atTop] at hII ⊢
    intro N
    obtain ⟨P, hPN, hP⟩ := hII (max N Q)
    refine ⟨P, le_of_max_le_left hPN, ?_⟩
    have huv : u P ≤ v P := not_lt.1 hP
    by_cases hv0 : v P = 0
    · exact ⟨le_antisymm (huv.trans hv0.le) (hu P), hv0⟩
    exfalso
    have hvpos : 0 < v P := lt_of_le_of_ne (hv P) (Ne.symm hv0)
    set g := r₂ - 2 * δ with hg
    have hg1 : 1 < g := by linarith
    have key : ∀ j : ℕ, u (P + j) ≤ v (P + j) ∧ g ^ j * v P ≤ v (P + j) := by
      intro j
      induction j with
      | zero => simpa using huv
      | succ j ih =>
        obtain ⟨h1, h2⟩ := ih
        obtain ⟨hA, hB⟩ := hQ (P + j) (by have := le_of_max_le_right hPN; omega)
        have hvq := hv (P + j)
        have huq := hu (P + j)
        rw [show P + (j + 1) = P + j + 1 by omega, pow_succ]
        have hC : g * v (P + j) ≤ v (P + j + 1) := by nlinarith
        refine ⟨?_, ?_⟩
        · nlinarith
        · nlinarith
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (C / v P) hg1
    rw [div_lt_iff₀ hvpos] at hj
    linarith [(key j).2, hvb (P + j)]

/-- **Perron's theorem for bounded solutions.** Let `x` solve
`x_{p+2} + a_p x_{p+1} + b_p x_p = 0` for large `p`, where `a_p → -(ρ₁ + ρ₂)` and
`b_p → ρ₁ρ₂`, the characteristic roots satisfy `‖ρ₁‖ < ‖ρ₂‖` and `1 < ‖ρ₂‖`. If `x` is
bounded and not eventually zero, then `x_{p+1}/x_p → ρ₁`. -/
theorem tendsto_succ_div_of_recurrence_of_bounded {𝕜 : Type*} [NormedField 𝕜]
    {x a b : ℕ → 𝕜} {ρ₁ ρ₂ : 𝕜} (hρ : ‖ρ₁‖ < ‖ρ₂‖) (hρ₂ : 1 < ‖ρ₂‖)
    (ha : Tendsto a atTop (𝓝 (-(ρ₁ + ρ₂)))) (hb : Tendsto b atTop (𝓝 (ρ₁ * ρ₂)))
    (hrec : ∀ᶠ p in atTop, x (p + 2) + a p * x (p + 1) + b p * x p = 0)
    {C : ℝ} (hbdd : ∀ p, ‖x p‖ ≤ C) (hne : ∃ᶠ p in atTop, x p ≠ 0) :
    Tendsto (fun p => x (p + 1) / x p) atTop (𝓝 ρ₁) := by
  have hd : ρ₂ - ρ₁ ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hρ; exact lt_irrefl _ hρ
  set r₁ := ‖ρ₁‖
  set r₂ := ‖ρ₂‖
  set D := ‖ρ₂ - ρ₁‖ with hD
  have hD0 : 0 < D := norm_pos_iff.2 hd
  have hr₂ : 0 < r₂ := by linarith
  set y : ℕ → 𝕜 := fun p => x (p + 1) - ρ₂ * x p with hy
  set z : ℕ → 𝕜 := fun p => x (p + 1) - ρ₁ * x p with hz
  have ex0 : ∀ p, (ρ₂ - ρ₁) * x p = z p - y p := fun p => by simp only [y, z]; ring
  have ex1 : ∀ p, (ρ₂ - ρ₁) * x (p + 1) = ρ₂ * z p - ρ₁ * y p := fun p => by
    simp only [y, z]; ring
  have nx0 : ∀ p, ‖x p‖ ≤ (‖y p‖ + ‖z p‖) / D := fun p => by
    rw [le_div_iff₀ hD0, mul_comm, ← norm_mul, ex0]
    exact (norm_sub_le _ _).trans (by linarith)
  have nx1 : ∀ p, ‖x (p + 1)‖ ≤ r₂ * (‖y p‖ + ‖z p‖) / D := fun p => by
    rw [le_div_iff₀ hD0, mul_comm, ← norm_mul, ex1]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [norm_nonneg (y p), norm_nonneg (z p)]
  -- perturbation estimate
  have hδ : ∀ δ > 0, ∀ᶠ p in atTop,
      r₂ * ‖z p‖ - δ * (‖y p‖ + ‖z p‖) ≤ ‖z (p + 1)‖ ∧
        ‖y (p + 1)‖ ≤ r₁ * ‖y p‖ + δ * (‖y p‖ + ‖z p‖) := by
    intro δ hδ
    have ha' := (Metric.tendsto_nhds.1 ha) (δ * D / (2 * r₂)) (by positivity)
    have hb' := (Metric.tendsto_nhds.1 hb) (δ * D / 2) (by positivity)
    filter_upwards [ha', hb', hrec] with p hap hbp hp
    rw [dist_eq_norm, sub_neg_eq_add] at hap
    rw [dist_eq_norm] at hbp
    set E := (a p + (ρ₁ + ρ₂)) * x (p + 1) + (b p - ρ₁ * ρ₂) * x p
    have hE : ‖E‖ ≤ δ * (‖y p‖ + ‖z p‖) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h1 := mul_le_mul hap.le (nx1 p) (norm_nonneg _) (by positivity)
      have h2 := mul_le_mul hbp.le (nx0 p) (norm_nonneg _) (by positivity)
      have e1 : δ * D / (2 * r₂) * (r₂ * (‖y p‖ + ‖z p‖) / D) = δ * (‖y p‖ + ‖z p‖) / 2 := by
        field_simp
      have e2 : δ * D / 2 * ((‖y p‖ + ‖z p‖) / D) = δ * (‖y p‖ + ‖z p‖) / 2 := by
        field_simp
      linarith
    have hzs : z (p + 1) = ρ₂ * z p - E := by
      simp only [z, E]; rw [show p + 1 + 1 = p + 2 by ring]; linear_combination hp
    have hys : y (p + 1) = ρ₁ * y p - E := by
      simp only [y, E]; rw [show p + 1 + 1 = p + 2 by ring]; linear_combination hp
    refine ⟨?_, ?_⟩
    · rw [hzs]
      have := norm_sub_norm_le (ρ₂ * z p) E
      rw [norm_mul] at this
      linarith
    · rw [hys]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      linarith
  have hvb : ∀ p, ‖z p‖ ≤ C + r₁ * C := fun p => by
    simp only [z]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have := hbdd p
    have := hbdd (p + 1)
    have : r₁ * ‖x p‖ ≤ r₁ * C := mul_le_mul_of_nonneg_left (hbdd p) (norm_nonneg _)
    linarith
  rcases norm_dichotomy_of_le_mul_add (u := fun p => ‖y p‖) (v := fun p => ‖z p‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (norm_nonneg _) hρ hρ₂ hvb hδ with
    h0 | ⟨hlt, hlim⟩
  · -- two consecutive zeros force `x` to vanish eventually
    exfalso
    obtain ⟨N, hN⟩ := eventually_atTop.1 hrec
    obtain ⟨P, hPN, hy0, hz0⟩ := (Filter.frequently_atTop.1 h0) N
    simp only [norm_eq_zero] at hy0 hz0
    have hx0 : x P = 0 := by
      have := ex0 P; rw [hy0, hz0, sub_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hd
    have hx1 : x (P + 1) = 0 := by
      have := ex1 P; rw [hy0, hz0] at this; simp only [mul_zero, sub_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hd
    have hall : ∀ j, x (P + j) = 0 ∧ x (P + j + 1) = 0 := by
      intro j
      induction j with
      | zero => exact ⟨hx0, hx1⟩
      | succ j ih =>
        refine ⟨by rw [show P + (j + 1) = P + j + 1 by omega]; exact ih.2, ?_⟩
        have := hN (P + j) (by omega)
        rw [ih.1, ih.2, show P + j + 2 = P + (j + 1) + 1 by omega] at this
        simpa using this
    obtain ⟨Q, hQP, hQ⟩ := (Filter.frequently_atTop.1 hne) P
    obtain ⟨j, rfl⟩ : ∃ j, Q = P + j := ⟨Q - P, by omega⟩
    exact hQ (hall j).1
  · -- the ratio `z/y` tends to zero
    have hw : Tendsto (fun p => z p / y p) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [norm_div] using hlim
    have hcont : Tendsto (fun w : 𝕜 => (ρ₂ * w - ρ₁) / (w - 1)) (𝓝 0)
        (𝓝 ((ρ₂ * 0 - ρ₁) / (0 - 1))) :=
      ((continuous_const.mul continuous_id).sub continuous_const).continuousAt.div
        (continuous_id.sub continuous_const).continuousAt (by norm_num)
    rw [show (ρ₂ * 0 - ρ₁) / (0 - 1) = ρ₁ by ring] at hcont
    refine (hcont.comp hw).congr' ?_
    filter_upwards [hlt] with p hp
    have hy0 : y p ≠ 0 := by
      intro h; simp only [h, norm_zero] at hp; exact (not_lt.2 (norm_nonneg _)) hp
    simp only [Function.comp]
    rw [← mul_div_mul_left (x (p + 1)) (x p) hd, ex1 p, ex0 p]
    rw [show ρ₂ * (z p / y p) - ρ₁ = (ρ₂ * z p - ρ₁ * y p) / y p by field_simp,
      show z p / y p - 1 = (z p - y p) / y p by field_simp, div_div_div_cancel_right₀ hy0]

/-- **Perron's theorem for bounded solutions**, three-term form: if
`γ_p x_p + β_p x_{p+1} + α_p x_{p+2} = 0` for large `p` with `α_p ≠ 0`, `β_p/α_p → -(ρ₁ + ρ₂)`,
`γ_p/α_p → ρ₁ρ₂`, `‖ρ₁‖ < ‖ρ₂‖`, `1 < ‖ρ₂‖`, and `x` is bounded and not eventually zero, then
`x_{p+1}/x_p → ρ₁`. -/
theorem tendsto_succ_div_of_three_term_recurrence_of_bounded {𝕜 : Type*} [NormedField 𝕜]
    {x α β γ : ℕ → 𝕜} {ρ₁ ρ₂ : 𝕜} (hρ : ‖ρ₁‖ < ‖ρ₂‖) (hρ₂ : 1 < ‖ρ₂‖)
    (hα : ∀ᶠ p in atTop, α p ≠ 0)
    (hβ : Tendsto (fun p => β p / α p) atTop (𝓝 (-(ρ₁ + ρ₂))))
    (hγ : Tendsto (fun p => γ p / α p) atTop (𝓝 (ρ₁ * ρ₂)))
    (hrec : ∀ᶠ p in atTop, γ p * x p + β p * x (p + 1) + α p * x (p + 2) = 0)
    {C : ℝ} (hbdd : ∀ p, ‖x p‖ ≤ C) (hne : ∃ᶠ p in atTop, x p ≠ 0) :
    Tendsto (fun p => x (p + 1) / x p) atTop (𝓝 ρ₁) := by
  refine tendsto_succ_div_of_recurrence_of_bounded hρ hρ₂ hβ hγ ?_ hbdd hne
  filter_upwards [hα, hrec] with p hp h
  field_simp
  linear_combination h

section NestedFraction

variable {α β γ : ℕ → ℝ}

/-- The solution with `g₀ = 0`, `g₁ = 1` by forward recursion. -/
private noncomputable def threeTermSecondSolution (α β γ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | q + 2 => -(γ (q + 1) * threeTermSecondSolution α β γ q +
      β (q + 1) * threeTermSecondSolution α β γ (q + 1)) / α (q + 1)

private theorem threeTermSecondSolution_rec (hα : ∀ q, α q ≠ 0) (q : ℕ) :
    γ (q + 1) * threeTermSecondSolution α β γ q +
      β (q + 1) * threeTermSecondSolution α β γ (q + 1) +
        α (q + 1) * threeTermSecondSolution α β γ (q + 2) = 0 := by
  rw [threeTermSecondSolution]
  have := hα (q + 1)
  field_simp
  ring

/-- The nested finite continued fraction with zero tail equals `-α_j u_{j+1}/u_j` for a
solution `u` with `u_{N+1} = 0` that does not vanish on `(j, N]`. -/
private theorem nestedFraction_eq_of_solution {R : ℕ → ℕ → ℝ} (hR0 : ∀ q, R q 0 = 0)
    (hRs : ∀ q d, R q (d + 1) = α q * γ (q + 1) / (β (q + 1) - R (q + 1) d))
    (hγ : ∀ q, γ (q + 1) ≠ 0) {u : ℕ → ℝ}
    (hu : ∀ q, γ (q + 1) * u q + β (q + 1) * u (q + 1) + α (q + 1) * u (q + 2) = 0)
    {N : ℕ} (huN : u (N + 1) = 0) :
    ∀ d j, j + d = N → (∀ i, j < i → i ≤ N → u i ≠ 0) → R j d = -α j * u (j + 1) / u j := by
  intro d
  induction d with
  | zero =>
    intro j hj _
    rw [hR0, add_zero] at *
    subst hj
    rw [huN]; simp
  | succ d ih =>
    intro j hj hne
    have h1 := ih (j + 1) (by omega) fun i hi hiN => hne i (by omega) hiN
    have hu1 : u (j + 1) ≠ 0 := hne (j + 1) (by omega) (by omega)
    rw [hRs, h1]
    have hden : β (j + 1) - -α (j + 1) * u (j + 1 + 1) / u (j + 1) =
        -γ (j + 1) * u j / u (j + 1) := by
      field_simp
      linear_combination hu j
    rw [hden, div_div_eq_mul_div]
    by_cases huj : u j = 0
    · simp [huj]
    · have := hγ j
      field_simp


/-- **Pincherle's theorem** for a three-term recurrence
`γ_{q+1} f_q + β_{q+1} f_{q+1} + α_{q+1} f_{q+2} = 0` with `α_q ≠ 0`, `γ_{q+1} ≠ 0` and
`γ_{q+1}/α_{q+1} → 1`: if `f₀ ≠ 0` and `f_{q+1}/f_q → ρ ∈ (0, 1)`, then the truncations
`R_p(d) = α_pγ_{p+1}/(β_{p+1} - α_{p+1}γ_{p+2}/(β_{p+2} - ⋯))` (zero tail) converge to
`-α_p f_{p+1}/f_p` whenever `f_p ≠ 0`. The solution `f` is minimal: the second solution with
`g₀ = 0`, `g₁ = 1` satisfies `f_N/g_N → 0`, because the Casoratian has ratio tending to `1`.
-/
theorem tendsto_nestedFraction_of_minimal {R : ℕ → ℕ → ℝ} (hR0 : ∀ q, R q 0 = 0)
    (hRs : ∀ q d, R q (d + 1) = α q * γ (q + 1) / (β (q + 1) - R (q + 1) d))
    (hα : ∀ q, α q ≠ 0) (hγ : ∀ q, γ (q + 1) ≠ 0) {f : ℕ → ℝ}
    (hf : ∀ q, γ (q + 1) * f q + β (q + 1) * f (q + 1) + α (q + 1) * f (q + 2) = 0)
    (hf0 : f 0 ≠ 0) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hratio : Tendsto (fun q => f (q + 1) / f q) atTop (𝓝 ρ))
    (hγα : Tendsto (fun q => γ (q + 1) / α (q + 1)) atTop (𝓝 1)) {p : ℕ} (hfp : f p ≠ 0) :
    Tendsto (R p) atTop (𝓝 (-α p * f (p + 1) / f p)) := by
  set g := threeTermSecondSolution α β γ with hgdef
  have hg := threeTermSecondSolution_rec (β := β) (γ := γ) hα
  -- the Casoratian
  set W : ℕ → ℝ := fun q => f q * g (q + 1) - f (q + 1) * g q with hWdef
  have hWs : ∀ q, W (q + 1) * α (q + 1) = γ (q + 1) * W q := fun q => by
    simp only [W]
    have e1 := hf q
    have e2 := hg q
    rw [show q + 1 + 1 = q + 2 by ring]
    linear_combination (-(g (q + 1))) * e1 + f (q + 1) * e2
  have hW : ∀ q, W q ≠ 0 := by
    intro q
    induction q with
    | zero => simp [W, g, threeTermSecondSolution, hf0]
    | succ q ih =>
      intro h0
      have := hWs q
      rw [h0, zero_mul] at this
      exact mul_ne_zero (hγ q) ih this.symm
  -- eventual properties of `f`
  have hfev : ∀ᶠ q in atTop, f q ≠ 0 := by
    have := hratio.eventually (lt_mem_nhds hρ0)
    filter_upwards [this] with q hq h0
    rw [h0, div_zero] at hq; exact lt_irrefl _ hq
  have hratio_pos := hratio.eventually (lt_mem_nhds hρ0)
  have hWratio : Tendsto (fun q => W (q + 1) / W q) atTop (𝓝 1) := by
    refine hγα.congr fun q => ?_
    rw [div_eq_div_iff (hα (q + 1)) (hW q)]
    linear_combination (hWs q).symm
  -- `D q = W q/(f q f (q+1))`
  set D : ℕ → ℝ := fun q => W q / (f q * f (q + 1)) with hDdef
  have hDratio : Tendsto (fun q => D (q + 1) / D q) atTop (𝓝 (1 * (ρ⁻¹ * ρ⁻¹))) := by
    have h1 := (hratio.inv₀ hρ0.ne')
    have h2 := (hratio.comp (tendsto_add_atTop_nat 1)).inv₀ hρ0.ne'
    refine (hWratio.mul (h1.mul h2)).congr' ?_
    filter_upwards [hfev, (tendsto_add_atTop_nat 1).eventually hfev,
      (tendsto_add_atTop_nat 2).eventually hfev] with q h0 h1 h2
    simp only [D, Function.comp_apply] at *
    rw [show q + 1 + 1 = q + 2 by ring]
    have := hW q
    have := hW (q + 1)
    field_simp
  have hθ : 1 < 1 * (ρ⁻¹ * ρ⁻¹) := by
    rw [one_mul, ← mul_inv]
    exact one_lt_inv_iff₀.2 ⟨by positivity, by nlinarith⟩
  set θ := (1 + 1 * (ρ⁻¹ * ρ⁻¹)) / 2 with hθdef
  have hθ1 : 1 < θ := by rw [hθdef]; linarith
  have hDev := hDratio.eventually (lt_mem_nhds (show θ < 1 * (ρ⁻¹ * ρ⁻¹) by
    rw [hθdef]; linarith))
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 (hfev.and (hDev.and
    ((tendsto_add_atTop_nat 1).eventually hfev)))
  -- sign of `D`
  have hDne : ∀ q ≥ Q, D q ≠ 0 := fun q hq => by
    simp only [D]
    exact div_ne_zero (hW q) (mul_ne_zero (hQ q hq).1 (hQ q hq).2.2)
  set σ : ℝ := if 0 < D Q then 1 else -1 with hσ
  have hσD : ∀ q ≥ Q, 0 < σ * D q := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base =>
      have := hDne Q le_rfl
      simp only [σ]; split_ifs with h
      · linarith
      · have : D Q < 0 := lt_of_le_of_ne (not_lt.1 h) this
        linarith
    | succ q hq ih =>
      have hr := (hQ q hq).2.1
      have hd := hDne q hq
      have : D (q + 1) = D (q + 1) / D q * D q := by field_simp
      rw [this, mul_left_comm]
      exact mul_pos (by linarith) ih
  have hσ2 : σ * σ = 1 := by simp only [σ]; split_ifs <;> norm_num
  -- `h q = g q / f q` increases (after the sign `σ`) strictly with increments `σ D q`
  set h : ℕ → ℝ := fun q => g q / f q with hhdef
  have hstep : ∀ q ≥ Q, h (q + 1) = h q + D q := by
    intro q hq
    have h0 := (hQ q hq).1
    have h1 := (hQ q hq).2.2
    simp only [h, D, W]
    field_simp
    ring
  have hmono : ∀ j ≥ Q, ∀ N, j ≤ N → σ * h j < σ * h (N + 1) := by
    intro j hj N hjN
    induction N, hjN using Nat.le_induction with
    | base =>
      rw [hstep j hj, mul_add]; linarith [hσD j hj]
    | succ N hN ih =>
      rw [hstep (N + 1) (by omega), mul_add]; linarith [hσD (N + 1) (by omega)]
  -- `σ D` grows geometrically, so `σ h → ∞`
  have hDgrow : ∀ i, θ ^ i * (σ * D Q) ≤ σ * D (Q + i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hr := (hQ (Q + i) (by omega)).2.1
      have hd := hDne (Q + i) (by omega)
      have hpos := hσD (Q + i) (by omega)
      rw [show Q + (i + 1) = Q + i + 1 by ring]
      have : σ * D (Q + i + 1) = D (Q + i + 1) / D (Q + i) * (σ * D (Q + i)) := by
        field_simp
      rw [this, pow_succ]
      nlinarith
  have hh : Tendsto (fun N => σ * h (N + 1)) atTop atTop := by
    have hpow : Tendsto (fun i : ℕ => θ ^ i * (σ * D Q) + σ * h Q) atTop atTop :=
      tendsto_atTop_add_const_right _ _
        ((tendsto_pow_atTop_atTop_of_one_lt hθ1).atTop_mul_const (hσD Q le_rfl))
    refine tendsto_atTop_mono' atTop ?_ (hpow.comp (tendsto_sub_atTop_nat Q))
    filter_upwards [eventually_ge_atTop Q] with N hN
    simp only [Function.comp_apply]
    have e := hstep N hN
    have := hDgrow (N - Q)
    rw [show Q + (N - Q) = N by omega] at this
    rcases eq_or_lt_of_le hN with hQN | hQN
    · subst hQN; simp at this ⊢; rw [e, mul_add]; linarith
    · have hm := hmono Q le_rfl (N - 1) (by omega)
      rw [show N - 1 + 1 = N by omega] at hm
      rw [e, mul_add]; linarith
  -- `f (N+1)/g (N+1) → 0`
  have hε : Tendsto (fun N => f (N + 1) / g (N + 1)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp hh).const_mul σ
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop Q] with N hN
    simp only [Function.comp_apply, h]
    have hσ0 : σ ≠ 0 := fun h0 => by rw [h0, zero_mul] at hσ2; exact zero_ne_one hσ2
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hσ0, one_mul, inv_div]
  -- `g` is eventually nonzero
  have hgev : ∀ᶠ N in atTop, g (N + 1) ≠ 0 := by
    filter_upwards [hh.eventually_gt_atTop 0] with N hN h0
    simp only [h, h0, zero_div, mul_zero] at hN
    exact lt_irrefl _ hN
  -- the backward solutions `u^N`
  set u : ℕ → ℕ → ℝ := fun N j => f j * g (N + 1) - g j * f (N + 1) with hudef
  have hu : ∀ N q, γ (q + 1) * u N q + β (q + 1) * u N (q + 1) + α (q + 1) * u N (q + 2) = 0 :=
    fun N q => by simp only [u]; linear_combination g (N + 1) * hf q - f (N + 1) * hg q
  have huN : ∀ N, u N (N + 1) = 0 := fun N => by simp only [u]; ring
  -- `u^N` does not vanish on `(p, N]` for large `N`
  have hfar : ∀ N, ∀ j, Q ≤ j → j ≤ N → u N j ≠ 0 := by
    intro N j hj hjN
    have hfj := (hQ j hj).1
    have hfN := (hQ N (by omega)).2.2
    have hm := hmono j hj N hjN
    have e : u N j = f j * f (N + 1) * (h (N + 1) - h j) := by
      simp only [u, h]; field_simp
    rw [e]
    refine mul_ne_zero (mul_ne_zero hfj hfN) (sub_ne_zero.2 fun h0 => ?_)
    rw [h0] at hm; exact lt_irrefl _ hm
  have hnear : ∀ j ∈ Finset.range Q, ∀ᶠ N in atTop, u N j ≠ 0 := by
    intro j _
    by_cases hfj : f j = 0
    · have hgj : g j ≠ 0 := by
        intro h0; apply hW j; simp only [W, hfj, h0]; ring
      filter_upwards [eventually_ge_atTop Q] with N hN
      simp only [u, hfj, zero_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero hgj (hQ N hN).2.2
    · have hlim : Tendsto (fun N => f j - g j * (f (N + 1) / g (N + 1))) atTop (𝓝 (f j)) := by
        simpa using tendsto_const_nhds.sub (hε.const_mul (g j))
      filter_upwards [hlim.eventually_ne hfj, hgev] with N hN hg0
      intro h0
      apply hN
      simp only [u] at h0
      field_simp
      linear_combination h0
  have hall : ∀ᶠ N in atTop, ∀ i, p < i → i ≤ N → u N i ≠ 0 := by
    filter_upwards [(Filter.eventually_all_finset _).2 hnear] with N hN i _ hiN
    by_cases hi : Q ≤ i
    · exact hfar N i hi hiN
    · exact hN i (Finset.mem_range.2 (by omega))
  -- the nested fraction equals `-α_p u_{p+1}/u_p`
  have hR : ∀ᶠ N in atTop, R p (N - p) = -α p * u N (p + 1) / u N p := by
    filter_upwards [hall, eventually_ge_atTop p] with N hN hpN
    exact nestedFraction_eq_of_solution hR0 hRs hγ (hu N) (huN N) (N - p) p (by omega) hN
  have hlim : Tendsto (fun N => -α p * (f (p + 1) - g (p + 1) * (f (N + 1) / g (N + 1))) /
      (f p - g p * (f (N + 1) / g (N + 1)))) atTop (𝓝 (-α p * f (p + 1) / f p)) := by
    have h1 : Tendsto (fun N => f (p + 1) - g (p + 1) * (f (N + 1) / g (N + 1))) atTop
        (𝓝 (f (p + 1))) := by simpa using tendsto_const_nhds.sub (hε.const_mul (g (p + 1)))
    have h2 : Tendsto (fun N => f p - g p * (f (N + 1) / g (N + 1))) atTop (𝓝 (f p)) := by
      simpa using tendsto_const_nhds.sub (hε.const_mul (g p))
    have := (h1.const_mul (-α p)).div h2 hfp
    exact this
  have hlim' : Tendsto (fun N => R p (N - p)) atTop (𝓝 (-α p * f (p + 1) / f p)) := by
    refine hlim.congr' ?_
    filter_upwards [hR, hgev] with N hN hg0
    rw [hN]
    simp only [u]
    rw [← mul_div_mul_right _ _ hg0]
    congr 1
    · field_simp
    · field_simp
  have := hlim'.comp (tendsto_add_atTop_nat p)
  refine this.congr fun d => ?_
  simp

end NestedFraction
