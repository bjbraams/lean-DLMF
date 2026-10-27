/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential

/-!
# Localizing zeros of holomorphic functions near approximate zeros

A quantitative, Newton–Kantorovich-type criterion for a function of a complex variable to have
*exactly one* zero in a closed disc around an approximate zero `z₀`: if the derivative of `f` stays
within relative distance `κ < 1` of a fixed nonzero number `c` on the disc `closedBall z₀ r`, and
`‖f z₀‖ ≤ (1 - κ) ‖c‖ r`, then the simplified Newton map `z ↦ z - f z / c` is a `κ`-contraction of
the disc into itself, so by the Banach fixed-point theorem `f` has exactly one zero there; the zero
lies within `‖f z₀‖ / ((1 - κ) ‖c‖)` of `z₀` and is simple.

The file also records elementary lower and upper bounds for `exp ζ - 1` near `0` (the model
function for zeros of exponential type, used together with Rouché's theorem) and the passage from
eventual pointwise localization to a sequence of zeros with a Landau bound, which is the form in
which asymptotic zero results (DLMF §§7.13, 9.9, 13.9) are stated.

Mathlib has no argument principle or Rouché theorem; for zero counting with multiplicity see
`TauCeti.rouche` in `TauCeti.Analysis.Complex.Conformal.Rouche`.

## Main results

* `Complex.zloc_existsUnique_zero_closedBall`: exactly one zero in the closed disc.
* `Complex.zloc_exists_zero_norm_sub_le`: the zero lies within `‖f z₀‖ / ((1 - κ) ‖c‖)` of `z₀`,
  and its derivative is nonzero.
* `Complex.zloc_eventually_exists_zero_isBigO`: a sequence (or filter) version producing zeros
  `r k` with `r k - w k = O(ρ k)`.
* `Complex.zloc_norm_exp_sub_one_ge`: `‖ζ‖ / 2 ≤ ‖exp ζ - 1‖` for `‖ζ‖ ≤ 1/2`.
-/

@[expose] public noncomputable section

open Set Metric Filter Asymptotics
open scoped Topology NNReal

namespace Complex

/-- Lower bound for the exponential model near its zero: `‖ζ‖ / 2 ≤ ‖exp ζ - 1‖` when
`‖ζ‖ ≤ 1/2`. -/
theorem zloc_norm_exp_sub_one_ge {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) : ‖ζ‖ / 2 ≤ ‖exp ζ - 1‖ := by
  have h := norm_exp_sub_one_sub_id_le (x := ζ) (by linarith)
  have htri : ‖ζ‖ ≤ ‖exp ζ - 1‖ + ‖exp ζ - 1 - ζ‖ := by
    have := norm_sub_le (exp ζ - 1) (exp ζ - 1 - ζ)
    simpa using this
  nlinarith [norm_nonneg ζ]

/-- The simplified Newton map `z ↦ z - f z / c` is `κ`-Lipschitz on a convex set on which the
derivative of `f` stays within `κ ‖c‖` of `c`. -/
theorem zloc_newton_lipschitz {f f' : ℂ → ℂ} {s : Set ℂ} {c : ℂ} {κ : ℝ} (hc : c ≠ 0)
    (hs : Convex ℝ s) (hf : ∀ z ∈ s, HasDerivAt f (f' z) z)
    (hf' : ∀ z ∈ s, ‖f' z - c‖ ≤ κ * ‖c‖) {x y : ℂ} (hx : x ∈ s) (hy : y ∈ s) :
    ‖(y - f y / c) - (x - f x / c)‖ ≤ κ * ‖y - x‖ := by
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  refine hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => z - f z / c) (f' := fun z => 1 - f' z / c)
    (fun z hz => (((hasDerivAt_id z).sub ((hf z hz).div_const c))).hasDerivWithinAt)
    (fun z hz => ?_) hx hy
  have : 1 - f' z / c = -((f' z - c) / c) := by field_simp; ring
  rw [this, norm_neg, norm_div, div_le_iff₀ hc']
  exact hf' z hz

/-- **Exactly one zero in a disc** (simplified Newton–Kantorovich). Let `f` have derivative `f'`
at every point of `closedBall z₀ r`, let `c ≠ 0` and `κ < 1` with `‖f' z - c‖ ≤ κ ‖c‖` on the
disc, and suppose `‖f z₀‖ ≤ (1 - κ) ‖c‖ r`. Then `f` has exactly one zero in `closedBall z₀ r`. -/
theorem zloc_existsUnique_zero_closedBall {f f' : ℂ → ℂ} {z₀ c : ℂ} {r κ : ℝ} (hc : c ≠ 0)
    (hκ : κ < 1) (hf : ∀ z ∈ closedBall z₀ r, HasDerivAt f (f' z) z)
    (hf' : ∀ z ∈ closedBall z₀ r, ‖f' z - c‖ ≤ κ * ‖c‖)
    (h0 : ‖f z₀‖ ≤ (1 - κ) * ‖c‖ * r) :
    ∃! z, z ∈ closedBall z₀ r ∧ f z = 0 := by
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hr : 0 ≤ r := by
    by_contra hr
    push Not at hr
    have : (1 - κ) * ‖c‖ * r < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by linarith) hc') hr
    linarith [norm_nonneg (f z₀)]
  have hz₀ : z₀ ∈ closedBall z₀ r := mem_closedBall_self hr
  have hκ0 : 0 ≤ κ := by
    have := (norm_nonneg _).trans (hf' z₀ hz₀)
    exact nonneg_of_mul_nonneg_left this hc'
  set T : ℂ → ℂ := fun z => z - f z / c with hT
  have hlip : ∀ x ∈ closedBall z₀ r, ∀ y ∈ closedBall z₀ r, ‖T y - T x‖ ≤ κ * ‖y - x‖ :=
    fun x hx y hy => zloc_newton_lipschitz hc (convex_closedBall z₀ r) hf hf' hx hy
  have hTz₀ : ‖T z₀ - z₀‖ = ‖f z₀‖ / ‖c‖ := by
    simp [hT]
  have hmaps : MapsTo T (closedBall z₀ r) (closedBall z₀ r) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz ⊢
    have h1 := hlip z₀ hz₀ z (mem_closedBall_iff_norm.mpr hz)
    have h2 : ‖f z₀‖ / ‖c‖ ≤ (1 - κ) * r := by
      rw [div_le_iff₀ hc']; linarith
    calc ‖T z - z₀‖ ≤ ‖T z - T z₀‖ + ‖T z₀ - z₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ κ * ‖z - z₀‖ + (1 - κ) * r := by rw [hTz₀]; exact add_le_add h1 h2
      _ ≤ κ * r + (1 - κ) * r := by gcongr
      _ = r := by ring
  have hzero : ∀ z, f z = 0 ↔ T z = z := by
    intro z
    simp only [hT, sub_eq_self, div_eq_zero_iff, hc, or_false]
  let K : ℝ≥0 := ⟨κ, hκ0⟩
  have hcontr : ContractingWith K (hmaps.restrict T (closedBall z₀ r) (closedBall z₀ r)) := by
    refine ⟨by exact_mod_cast hκ, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [MapsTo.restrict, Subtype.dist_eq, dist_eq_norm]
    change ‖T x - T y‖ ≤ κ * ‖(x : ℂ) - y‖
    exact hlip y y.2 x x.2
  obtain ⟨y, hy, hfix, -⟩ := hcontr.exists_fixedPoint' isClosed_closedBall.isComplete hmaps hz₀
    (edist_ne_top _ _)
  refine ⟨y, ⟨hy, (hzero y).2 hfix⟩, ?_⟩
  rintro z ⟨hz, hfz⟩
  have hTz := (hzero z).1 hfz
  have hTy : T y = y := hfix
  have hle := hlip y hy z hz
  rw [hTz, hTy] at hle
  have : ‖z - y‖ = 0 := by nlinarith [norm_nonneg (z - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- **Localization of the zero.** Under the hypotheses of `zloc_existsUnique_zero_closedBall`,
the zero `z` satisfies `‖z - z₀‖ ≤ ‖f z₀‖ / ((1 - κ) ‖c‖)` and `f' z ≠ 0` (it is simple). -/
theorem zloc_exists_zero_norm_sub_le {f f' : ℂ → ℂ} {z₀ c : ℂ} {r κ : ℝ} (hc : c ≠ 0)
    (hκ : κ < 1) (hf : ∀ z ∈ closedBall z₀ r, HasDerivAt f (f' z) z)
    (hf' : ∀ z ∈ closedBall z₀ r, ‖f' z - c‖ ≤ κ * ‖c‖)
    (h0 : ‖f z₀‖ ≤ (1 - κ) * ‖c‖ * r) :
    ∃ z ∈ closedBall z₀ r, f z = 0 ∧ ‖z - z₀‖ ≤ ‖f z₀‖ / ((1 - κ) * ‖c‖) ∧ f' z ≠ 0 := by
  obtain ⟨z, ⟨hz, hfz⟩, -⟩ := zloc_existsUnique_zero_closedBall hc hκ hf hf' h0
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hr : 0 ≤ r := (norm_nonneg _).trans (mem_closedBall_iff_norm.mp hz)
  have hz₀ : z₀ ∈ closedBall z₀ r := mem_closedBall_self hr
  have hle := zloc_newton_lipschitz hc (convex_closedBall z₀ r) hf hf' hz₀ hz
  rw [hfz, zero_div, sub_zero] at hle
  refine ⟨z, hz, hfz, ?_, ?_⟩
  · rw [le_div_iff₀ (mul_pos (by linarith) hc')]
    have htri : ‖z - z₀‖ ≤ ‖z - (z₀ - f z₀ / c)‖ + ‖f z₀ / c‖ := by
      have he : z - z₀ = (z - (z₀ - f z₀ / c)) + -(f z₀ / c) := by ring
      rw [he]
      exact (norm_add_le _ _).trans_eq (by rw [norm_neg])
    rw [norm_div] at htri
    have h3 : ‖z - z₀‖ * ‖c‖ ≤ κ * ‖z - z₀‖ * ‖c‖ + ‖f z₀‖ := by
      have := mul_le_mul_of_nonneg_right (htri.trans (add_le_add_left hle _)) hc'.le
      rwa [add_mul, div_mul_cancel₀ _ hc'.ne'] at this
    nlinarith
  · intro h
    have := hf' z hz
    rw [h, zero_sub, norm_neg] at this
    nlinarith

/-- **Sequence version.** If eventually along `l` the function `f k` has a zero within `ρ k` of
`w k`, then there is a family `r` of points with `f k (r k) = 0` eventually and
`r k - w k = O(g k)` whenever `ρ = O(g)`. This packages pointwise localization (for instance by
`zloc_exists_zero_norm_sub_le` or Rouché's theorem) into the form of asymptotic zero results. -/
theorem zloc_eventually_exists_zero_isBigO {ι : Type*} {l : Filter ι} {f : ι → ℂ → ℂ}
    {w : ι → ℂ} {ρ g : ι → ℝ}
    (h : ∀ᶠ k in l, ∃ z, ‖z - w k‖ ≤ ρ k ∧ f k z = 0) (hρ : ρ =O[l] g) :
    ∃ r : ι → ℂ, (fun k => r k - w k) =O[l] g ∧ ∀ᶠ k in l, f k (r k) = 0 := by
  classical
  let r : ι → ℂ := fun k => if hk : ∃ z, ‖z - w k‖ ≤ ρ k ∧ f k z = 0 then hk.choose else w k
  have hr : ∀ᶠ k in l, ‖r k - w k‖ ≤ ρ k ∧ f k (r k) = 0 := by
    filter_upwards [h] with k hk
    simp only [r, hk]
    exact hk.choose_spec
  refine ⟨r, ?_, hr.mono fun k hk => hk.2⟩
  refine IsBigO.trans ?_ hρ
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hr] with k hk
  rw [one_mul, Real.norm_eq_abs]
  exact hk.1.trans (le_abs_self _)

end Complex
