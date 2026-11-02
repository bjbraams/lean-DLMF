/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.LagrangeBurmann
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The Lagrange inversion theorem

Let `h` be analytic at `0` with `h(0) = 0` and `h'(0) ≠ 0`, so that `h(t) = t D(t)` with
`D = dslope h 0` analytic and nonzero at `0`, and put `Ψ = 1 / D`. For `G` analytic at `0` the
Lagrange inversion theorem (in Bürmann's form) states that, for all `w` near `0`,
`G(w) - G(0) = ∑_{n ≥ 1} h(w)ⁿ / n · [tⁿ⁻¹](G' Ψⁿ)`.
The statement is formulated in terms of the point `w` itself, so that no inverse function is
needed: the series is a power series in `ζ = h(w)`.

## Main results

* `Complex.hasSum_lagrangeInversion`: the Lagrange–Bürmann expansion
  `G(w) - G(0) = ∑ₙ (G' Ψⁿ⁺¹)⁽ⁿ⁾(0) / (n + 1)! · h(w)ⁿ⁺¹` for `w` near `0`.

## Implementation notes

The proof applies the coefficient form `Complex.lagB_hasSum_iteratedDeriv` of the
Lagrange–Bürmann formula with `F(t) = (G(t) - G(0)) (1 - t Ψ'(t) / Ψ(t))` and the factorization
`t - ζ Ψ(t) = (t - w) g(t)`, `g = dslope (t ↦ t - ζ Ψ(t)) w`. For small `w` the map `t ↦ ζ Ψ(t)`
is a contraction on a fixed closed disc, so `g` has no zeros there; and
`F(w) / g(w) = G(w) - G(0)`. The coefficients are then identified by the Leibniz rule:
`[tⁿ⁺¹](F Ψⁿ⁺¹) = [tⁿ](G' Ψⁿ⁺¹) / (n + 1)`.
-/

@[expose] public noncomputable section

open Complex Metric Set Filter MeasureTheory
open scoped Real Topology Nat NNReal ENNReal

namespace Complex


/-- The coefficient identity behind the Lagrange inversion theorem:
`(A Ψⁿ⁺¹ - t A Ψ' Ψⁿ)⁽ⁿ⁺¹⁾(0) = (A' Ψⁿ⁺¹)⁽ⁿ⁾(0)`. -/
private theorem iteratedDeriv_succ_lagrange_aux {A Ψ : ℂ → ℂ} (hA : AnalyticAt ℂ A 0)
    (hΨ : AnalyticAt ℂ Ψ 0) (m : ℕ) :
    iteratedDeriv (m + 1) (fun t => A t * Ψ t ^ (m + 1) - t * (A t * deriv Ψ t * Ψ t ^ m)) 0 =
      iteratedDeriv m (fun t => deriv A t * Ψ t ^ (m + 1)) 0 := by
  have hX : AnalyticAt ℂ (fun t => A t * deriv Ψ t * Ψ t ^ m) 0 :=
    (hA.mul hΨ.deriv).mul (hΨ.pow m)
  have hP : AnalyticAt ℂ (fun t => A t * Ψ t ^ (m + 1)) 0 := hA.mul (hΨ.pow _)
  have hQ : AnalyticAt ℂ (fun t => deriv A t * Ψ t ^ (m + 1)) 0 := hA.deriv.mul (hΨ.pow _)
  have hY : AnalyticAt ℂ (fun t => t * (A t * deriv Ψ t * Ψ t ^ m)) 0 := analyticAt_id.mul hX
  have h1 := iteratedDeriv_fun_sub (n := m + 1) (x := (0 : ℂ)) hP.contDiffAt hY.contDiffAt
  rw [h1]
  have h2 : iteratedDeriv (m + 1) (fun t => t * (A t * deriv Ψ t * Ψ t ^ m)) 0 =
      (m + 1) * iteratedDeriv m (fun t => A t * deriv Ψ t * Ψ t ^ m) 0 := by
    rw [iteratedDeriv_fun_mul (n := m + 1) (f := fun t => t) analyticAt_id.contDiffAt
      hX.contDiffAt]
    simp only [iteratedDeriv_fun_id_zero]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  have h3 : deriv (fun t => A t * Ψ t ^ (m + 1)) =ᶠ[𝓝 0]
      fun t => deriv A t * Ψ t ^ (m + 1) + (m + 1 : ℂ) * (A t * deriv Ψ t * Ψ t ^ m) := by
    filter_upwards [hA.eventually_analyticAt, hΨ.eventually_analyticAt] with t hAt hΨt
    have := hAt.differentiableAt.hasDerivAt.mul (hΨt.differentiableAt.hasDerivAt.pow (m + 1))
    refine this.deriv.trans ?_
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    ring
  have hZ : AnalyticAt ℂ (fun t => ((m : ℂ) + 1) * (A t * deriv Ψ t * Ψ t ^ m)) 0 :=
    analyticAt_const.mul hX
  rw [h2, iteratedDeriv_succ', h3.iteratedDeriv_eq,
    iteratedDeriv_fun_add hQ.contDiffAt hZ.contDiffAt,
    iteratedDeriv_const_mul_field]
  ring


/-- **Lagrange inversion theorem** (Bürmann's form). If `h` is analytic at `0`, `h(0) = 0`,
`h'(0) ≠ 0`, and `G` is analytic at `0`, then for all `w` near `0`
`G(w) - G(0) = ∑ₙ (G' Ψⁿ⁺¹)⁽ⁿ⁾(0) / (n + 1)! · h(w)ⁿ⁺¹`, where `Ψ(t) = t / h(t)`
(`Ψ = (dslope h 0)⁻¹`). -/
theorem hasSum_lagrangeInversion {h G : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (h0 : h 0 = 0)
    (hd : deriv h 0 ≠ 0) (hG : AnalyticAt ℂ G 0) :
    ∃ ε > 0, ∀ w : ℂ, ‖w‖ < ε → HasSum (fun n : ℕ =>
      iteratedDeriv n (fun t => deriv G t * (dslope h 0 t)⁻¹ ^ (n + 1)) 0 / (n + 1)! *
        h w ^ (n + 1)) (G w - G 0) := by
  obtain ⟨R₁, hR₁, hh₁⟩ := hh.exists_ball_analyticOnNhd
  obtain ⟨R₂, hR₂, hG₂⟩ := hG.exists_ball_analyticOnNhd
  have hDc : ContinuousAt (dslope h 0) 0 := continuousAt_dslope_same.2 hh.differentiableAt
  have hD0 : dslope h 0 0 ≠ 0 := by rwa [dslope_same]
  obtain ⟨R₃, hR₃, hD₃⟩ := Metric.eventually_nhds_iff.1 (hDc.eventually_ne hD0)
  set R := min R₁ (min R₂ R₃) with hRdef
  have hR : 0 < R := lt_min hR₁ (lt_min hR₂ hR₃)
  set U := ball (0 : ℂ) R with hUdef
  have hUo : IsOpen U := isOpen_ball
  have hhU : DifferentiableOn ℂ h U :=
    (hh₁.mono (ball_subset_ball (min_le_left _ _))).differentiableOn
  have hGU : DifferentiableOn ℂ G U :=
    (hG₂.mono (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)))).differentiableOn
  have hDU : DifferentiableOn ℂ (dslope h 0) U :=
    (differentiableOn_dslope (ball_mem_nhds 0 hR)).2 hhU
  have hDne : ∀ t ∈ U, dslope h 0 t ≠ 0 := fun t ht => hD₃ (lt_of_lt_of_le (mem_ball.1 ht)
    ((min_le_right _ _).trans (min_le_right _ _)))
  set Ψ : ℂ → ℂ := fun t => (dslope h 0 t)⁻¹ with hΨdef
  have hΨU : DifferentiableOn ℂ Ψ U := hDU.inv hDne
  have hΨne : ∀ t ∈ U, Ψ t ≠ 0 := fun t ht => inv_ne_zero (hDne t ht)
  have hΨ'U : DifferentiableOn ℂ (deriv Ψ) U := hΨU.deriv hUo
  set r := R / 2 with hrdef
  have hr : 0 < r := by positivity
  have hsub : closedBall (0 : ℂ) r ⊆ U := closedBall_subset_ball (by linarith)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (hΨU.continuousOn.mono hsub)
  obtain ⟨M', hM'⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (hΨ'U.continuousOn.mono hsub)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (hDU.continuousOn.mono hsub)
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) r := mem_closedBall_self hr.le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 h0mem)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' 0 h0mem)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 h0mem)
  set ε := min (r / 2) (min (r / (2 * (K + 1) * (M + 1))) (1 / (2 * (K + 1) * (M' + 1))))
    with hεdef
  refine ⟨ε, by positivity, fun w hw => ?_⟩
  have hw1 : ‖w‖ < r / 2 := hw.trans_le (min_le_left _ _)
  have hw2 : ‖w‖ < r / (2 * (K + 1) * (M + 1)) :=
    hw.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hw3 : ‖w‖ < 1 / (2 * (K + 1) * (M' + 1)) :=
    hw.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hwB : w ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hwU : w ∈ U := hsub hwB
  set ζ := h w with hζdef
  have hζ : ζ = w * dslope h 0 w := by
    have := sub_smul_dslope h 0 w
    rw [h0, sub_zero, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hζn : ‖ζ‖ ≤ ‖w‖ * (K + 1) := by
    rw [hζ, norm_mul]
    exact mul_le_mul_of_nonneg_left ((hK w hwB).trans (by linarith)) (norm_nonneg _)
  have hζM : ‖ζ‖ * (M + 1) < r / 2 := by
    have h1 : ‖w‖ * (K + 1) * (M + 1) < r / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hw2
      nlinarith
    calc ‖ζ‖ * (M + 1) ≤ ‖w‖ * (K + 1) * (M + 1) :=
          mul_le_mul_of_nonneg_right hζn (by linarith)
      _ < r / 2 := h1
  have hζM' : ‖ζ‖ * (M' + 1) < 1 := by
    have h1 : ‖w‖ * (K + 1) * (M' + 1) < 1 / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hw3
      nlinarith
    calc ‖ζ‖ * (M' + 1) ≤ ‖w‖ * (K + 1) * (M' + 1) :=
          mul_le_mul_of_nonneg_right hζn (by linarith)
      _ < 1 := by linarith
  set f : ℂ → ℂ := fun t => t - ζ * Ψ t with hfdef
  have hfU : DifferentiableOn ℂ f U := differentiableOn_id.sub (hΨU.const_mul ζ)
  set g := dslope f w with hgdef
  have hgU : DifferentiableOn ℂ g U := (differentiableOn_dslope (hUo.mem_nhds hwU)).2 hfU
  have hfw : f w = 0 := by
    simp only [hfdef, hΨdef, hζ]
    field_simp [hDne w hwU]
    ring
  have hfac : ∀ t, t - ζ * Ψ t = (t - w) * g t := by
    intro t
    have := sub_smul_dslope f w t
    rw [hfw, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hgw : g w = 1 - ζ * deriv Ψ w := by
    rw [hgdef, dslope_same]
    exact ((hasDerivAt_id w).sub ((hΨU.differentiableAt (hUo.mem_nhds hwU)).hasDerivAt.const_mul
      ζ)).deriv
  have hg0 : ∀ t ∈ closedBall (0 : ℂ) r, g t ≠ 0 := by
    intro t ht hgt
    by_cases htw : t = w
    · subst htw
      rw [hgw, sub_eq_zero] at hgt
      have : ‖ζ * deriv Ψ t‖ < 1 := by
        rw [norm_mul]
        calc ‖ζ‖ * ‖deriv Ψ t‖ ≤ ‖ζ‖ * (M' + 1) :=
              mul_le_mul_of_nonneg_left ((hM' t ht).trans (by linarith)) (norm_nonneg _)
          _ < 1 := hζM'
      rw [← hgt, norm_one] at this
      exact lt_irrefl _ this
    · have hft : t - ζ * Ψ t = 0 := by rw [hfac t, hgt, mul_zero]
      have hlip : ‖Ψ t - Ψ w‖ ≤ M' * ‖t - w‖ :=
        (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
          (fun x hx => hΨU.differentiableAt (hUo.mem_nhds (hsub hx))) hM' hwB ht
      have heq : t - w = ζ * (Ψ t - Ψ w) := by
        have : w - ζ * Ψ w = 0 := hfw
        linear_combination hft - this
      have hpos : 0 < ‖t - w‖ := norm_pos_iff.2 (sub_ne_zero.2 htw)
      have : ‖t - w‖ ≤ ‖ζ‖ * M' * ‖t - w‖ := by
        calc ‖t - w‖ = ‖ζ‖ * ‖Ψ t - Ψ w‖ := by rw [heq, norm_mul]
          _ ≤ ‖ζ‖ * (M' * ‖t - w‖) := mul_le_mul_of_nonneg_left hlip (norm_nonneg _)
          _ = ‖ζ‖ * M' * ‖t - w‖ := by ring
      nlinarith [norm_nonneg ζ]
  set F : ℂ → ℂ := fun t => (G t - G 0) * (1 - t * deriv Ψ t / Ψ t) with hFdef
  have hFU : DifferentiableOn ℂ F U :=
    (hGU.sub_const _).mul ((differentiableOn_const 1).sub
      ((differentiableOn_id.mul hΨ'U).div hΨU hΨne))
  have key := lagB_hasSum_iteratedDeriv (F := F) (Φ := Ψ) (g := g) (ρ := ‖ζ‖ * (M + 1))
    (z := ζ) (w := w) hr (hFU.mono hsub) (hΨU.mono hsub) (hgU.mono hsub) hg0 (by linarith)
    (fun t ht => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((hM t (sphere_subset_closedBall ht)).trans
        (by linarith)) (norm_nonneg _))
    (by linarith) (fun t _ => hfac t)
  have hFw : F w / g w = G w - G 0 := by
    have hFw' : F w = (G w - G 0) * g w := by
      rw [hgw, hFdef]
      simp only
      congr 1
      rw [hζ, hΨdef]
      simp only
      field_simp [hDne w hwU]
    rw [hFw', mul_div_assoc, div_self (hg0 w hwB), mul_one]
  rw [hFw] at key
  have key1 := (hasSum_nat_add_iff' 1).2 key
  have hF0 : F 0 = 0 := by simp [hFdef]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, iteratedDeriv_zero,
    one_mul, Nat.factorial_zero, Nat.cast_one, div_one, hF0, zero_mul, sub_zero] at key1
  have hAan : AnalyticAt ℂ (fun t => G t - G 0) 0 := hG.sub analyticAt_const
  have hΨan : AnalyticAt ℂ Ψ 0 := hΨU.analyticAt (hUo.mem_nhds (mem_ball_self hR))
  refine key1.congr_fun fun n => ?_
  have hev : (fun t => F t * Ψ t ^ (n + 1)) =ᶠ[𝓝 0] fun t => (G t - G 0) * Ψ t ^ (n + 1) -
      t * ((G t - G 0) * deriv Ψ t * Ψ t ^ n) := by
    filter_upwards [hUo.mem_nhds (mem_ball_self hR)] with t ht
    simp only [hFdef]
    have := hΨne t ht
    field_simp
    ring
  rw [hev.iteratedDeriv_eq, iteratedDeriv_succ_lagrange_aux hAan hΨan n]
  simp only [deriv_sub_const]
  ring

end Complex
