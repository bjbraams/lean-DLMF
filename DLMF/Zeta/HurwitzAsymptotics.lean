/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.HurwitzIntegrals

/-!
# The Hurwitz zeta function: asymptotic behaviour in `a`

Behaviour of `ζ(s, a)` for small `a`, for large imaginary part of `a`, and asymptotic
expansions for large `a` (DLMF §25.11(xii)).

## Main definitions

* `phaseSector`: the sector `|ph a| ≤ π - δ` of DLMF §25.11(xii).

## Main results

* `hurwitzZetaComplex_add_one_isBigO`: small `a`, DLMF 25.11.41.
* `tendstoUniformlyOn_hurwitzZetaComplex_im`: large imaginary part, DLMF 25.11.42.
* `hurwitzZetaComplex_asymptotic`, `deriv_hurwitzZetaComplex_neg_one_asymptotic`,
  `deriv_hurwitzZetaComplex_neg_two_asymptotic`: large `a`, DLMF 25.11.43–25.11.45.

## Implementation notes

Asymptotic expansions (25.11.43–25.11.45) are stated for each truncation order `K`, with
remainder `O` of the next power, as `a → ∞` in the sector `|ph a| ≤ π - δ`.
-/

@[expose] public section

open Complex Filter Set MeasureTheory HurwitzZeta Asymptotics
open scoped Nat Real Topology

noncomputable section

namespace DLMF.Zeta

open DLMF.Hypergeometric (pochhammer)

/-! ### §25.11(xii) `a`-asymptotic behaviour -/

/-- **Small `a`** (DLMF 25.11.41): as `a → 0` (complex), for fixed `s ≠ 1`,
`ζ(s, a+1) = ζ(s) - s ζ(s+1) a + O(a²)`. We also assume `s ≠ 0` (implicit condition: at `s = 0`
the coefficient `s ζ(s+1)` is to be read as its limit `1`; with Lean's junk `ζ(1)` the literal
statement fails there). -/
@[dlmf 25.11.E41]
theorem hurwitzZetaComplex_add_one_isBigO {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (fun a => hurwitzZetaComplex s (a + 1) - (riemannZeta s - s * riemannZeta (s + 1) * a))
      =O[𝓝 0] (fun a => a ^ 2) := by
  set f : ℂ → ℂ := fun a => hurwitzZetaComplex s (a + 1)
  have hB : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ one_pos
  have hre : ∀ a ∈ Metric.ball (0 : ℂ) 1, 0 < (a + 1).re := fun a ha => by
    rw [Metric.mem_ball, dist_zero_right] at ha
    have := neg_abs_le a.re
    have := abs_re_le_norm a
    simp; linarith
  have hf : DifferentiableOn ℂ f (Metric.ball 0 1) := fun a ha =>
    ((differentiableOn_hurwitzZetaComplex_param' hs1 (a + 1) (hre a ha)).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds (hre a ha))).comp a
      (differentiableAt_id.add_const 1) |>.differentiableWithinAt
  have hd : DifferentiableOn ℂ (dslope f 0) (Metric.ball 0 1) :=
    (differentiableOn_dslope hB).mpr hf
  have hc : ContinuousAt (dslope (dslope f 0) 0) 0 :=
    continuousAt_dslope_same.mpr (hd.differentiableAt hB)
  have hf0 : f 0 = riemannZeta s := by simp [f, hurwitzZetaComplex_one hs1]
  have hs1' : s + 1 ≠ 1 := fun h => hs0 (by linear_combination h)
  have hder : deriv f 0 = -s * riemannZeta (s + 1) := by
    have h1 := hasDerivAt_hurwitzZetaComplex_param' hs0 hs1 (a₀ := 1) (by simp)
    rw [show (1 : ℂ) = 0 + 1 by ring] at h1
    have h := h1.comp_add_const (0 : ℂ) 1
    simp only [zero_add] at h
    rw [h.deriv, hurwitzZetaComplex_one hs1']
  have key : ∀ a, f a - (riemannZeta s - s * riemannZeta (s + 1) * a) =
      a ^ 2 * dslope (dslope f 0) 0 a := by
    intro a
    have h1 := sub_smul_dslope f 0 a
    have h2 := sub_smul_dslope (dslope f 0) 0 a
    rw [dslope_same, hder] at h2
    simp only [sub_zero, smul_eq_mul] at h1 h2
    rw [← hf0]
    linear_combination -h1 - a * h2
  have hO : (fun a => dslope (dslope f 0) 0 a) =O[𝓝 0] (fun _ => (1 : ℂ)) :=
    hc.tendsto.isBigO_one ℂ
  have := (isBigO_refl (fun a : ℂ => a ^ 2) (𝓝 0)).mul hO
  simp only [mul_one] at this
  exact this.congr_left fun a => (key a).symm

/-- Termwise bound for the Hurwitz series off the real axis. -/
private lemma norm_one_div_cpow_le {s : ℂ} (hs : 0 ≤ s.re) {α β : ℝ} (hα : 0 ≤ α)
    (hβ : 1 ≤ |β|) (n : ℕ) :
    ‖1 / ((n : ℂ) + (α + β * I)) ^ s‖ ≤
      Real.exp (π * |s.im|) * (((n : ℝ) ^ 2 + β ^ 2) ^ (-(s.re / 2))) := by
  set w : ℂ := (n : ℂ) + (α + β * I)
  have hwre : w.re = n + α := by simp [w]
  have hwim : w.im = β := by simp [w]
  have hw : w ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hwim] at this; simp at this
    rw [this] at hβ; simp at hβ; linarith
  have hnw : ‖w‖ ^ 2 = (n + α) ^ 2 + β ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hwre, hwim]; ring
  have hpos : 0 < (n : ℝ) ^ 2 + β ^ 2 := by nlinarith [abs_nonneg β, sq_abs β]
  rw [norm_div, norm_one, norm_cpow_of_ne_zero hw, one_div_div]
  have h1 : Real.exp (arg w * s.im) ≤ Real.exp (π * |s.im|) := by
    apply Real.exp_le_exp.mpr
    calc arg w * s.im ≤ |arg w * s.im| := le_abs_self _
      _ = |arg w| * |s.im| := abs_mul _ _
      _ ≤ π * |s.im| := by gcongr; exact abs_arg_le_pi w
  have h2 : ‖w‖ ^ s.re ≠ 0 := by positivity
  have h3 : 1 / ‖w‖ ^ s.re ≤ ((n : ℝ) ^ 2 + β ^ 2) ^ (-(s.re / 2)) := by
    have e : ‖w‖ ^ s.re = (‖w‖ ^ 2) ^ (s.re / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; ring_nf
    rw [e, hnw, one_div, ← Real.rpow_neg (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos hpos (by nlinarith) (by linarith)
  rw [div_eq_mul_one_div]
  exact mul_le_mul h1 h3 (by positivity) (Real.exp_pos _).le

private lemma summable_sq_add_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => (((n : ℝ) ^ 2 + 1) ^ (-(σ / 2))) := by
  have hs : Summable fun n : ℕ => (2 : ℝ) ^ (σ / 2) * ((n + 1 : ℕ) : ℝ) ^ (-σ) := by
    refine Summable.mul_left _ ?_
    exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h : ((n + 1 : ℕ) : ℝ) ^ 2 / 2 ≤ (n : ℝ) ^ 2 + 1 := by
    push_cast; nlinarith [sq_nonneg ((n : ℝ) - 1)]
  calc (((n : ℝ) ^ 2 + 1) ^ (-(σ / 2))) ≤ (((n + 1 : ℕ) : ℝ) ^ 2 / 2) ^ (-(σ / 2)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h (by linarith)
    _ = (2 : ℝ) ^ (σ / 2) * ((n + 1 : ℕ) : ℝ) ^ (-σ) := by
        rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul hn.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
        ring_nf

/-- **Large imaginary part** (DLMF 25.11.42): for `Re s > 1`, `ζ(s, α + iβ) → 0` as `β → ±∞`,
uniformly for `α` in bounded subsets of `[0, ∞)`. -/
@[dlmf 25.11.E42]
theorem tendstoUniformlyOn_hurwitzZetaComplex_im {s : ℂ} (hs : 1 < s.re) (A : ℝ) :
    TendstoUniformlyOn (fun (β : ℝ) (α : ℝ) => hurwitzZetaComplex s (α + β * I)) 0
      (cocompact ℝ) (Icc 0 A) := by
  set σ := s.re
  set g : ℝ → ℝ := fun β => Real.exp (π * |s.im|) *
    ∑' n : ℕ, (((n : ℝ) ^ 2 + β ^ 2) ^ (-(σ / 2)))
  have hβ : Tendsto (fun β : ℝ => β ^ 2) (cocompact ℝ) atTop := by
    have := tendsto_norm_cocompact_atTop (E := ℝ)
    exact ((tendsto_pow_atTop two_ne_zero).comp this).congr fun β => by
      simp [Real.norm_eq_abs, sq_abs]
  have habs : ∀ᶠ β in cocompact ℝ, 1 ≤ |β| := by
    have := tendsto_norm_cocompact_atTop (E := ℝ)
    simpa [Real.norm_eq_abs] using this.eventually (eventually_ge_atTop 1)
  have hg : Tendsto g (cocompact ℝ) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := cocompact ℝ)
      (f := fun β (n : ℕ) => (((n : ℝ) ^ 2 + β ^ 2) ^ (-(σ / 2))))
      (g := fun _ => 0) (summable_sq_add_rpow hs) (fun n => ?_) ?_
    · simpa [g] using h.const_mul (Real.exp (π * |s.im|))
    · have : Tendsto (fun β : ℝ => (n : ℝ) ^ 2 + β ^ 2) (cocompact ℝ) atTop :=
        tendsto_atTop_add_const_left _ _ hβ
      exact (tendsto_rpow_neg_atTop (by linarith)).comp this
    · filter_upwards [habs] with β hb n
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
      nlinarith [sq_abs β]
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hg.eventually (gt_mem_nhds hε), habs] with β hgβ hb α hα
  simp only [Pi.zero_apply, dist_zero_left]
  have hsum := hasSum_hurwitzZetaComplex' (a := (α : ℂ) + β * I) (by linarith : 1 < s.re)
  have hb2 : Summable fun n : ℕ => Real.exp (π * |s.im|) *
      (((n : ℝ) ^ 2 + β ^ 2) ^ (-(σ / 2))) := by
    refine Summable.mul_left _ (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (summable_sq_add_rpow hs))
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    nlinarith [sq_abs β]
  calc ‖hurwitzZetaComplex s (α + β * I)‖
      ≤ ∑' n : ℕ, Real.exp (π * |s.im|) * (((n : ℝ) ^ 2 + β ^ 2) ^ (-(σ / 2))) :=
        tsum_of_norm_bounded hb2.hasSum
          (fun n => norm_one_div_cpow_le (by linarith) hα.1 hb n) |>.trans_eq' (by
            rw [hsum.tsum_eq])
    _ = g β := by simp only [g, tsum_mul_left]
    _ < ε := hgβ

/-- The sector `|ph a| ≤ π - δ` of DLMF §25.11(xii). -/
def phaseSector (δ : ℝ) : Set ℂ := {a | |arg a| ≤ π - δ}

/-- **Large-`a` expansion** (DLMF 25.11.43): for `s ≠ 1` and `0 < δ < π`, as `a → ∞` in
`|ph a| ≤ π - δ`, `ζ(s,a) - a^{1-s}/(s-1) - a^{-s}/2 ∼ ∑_{k≥1} (B_{2k}/(2k)!) (s)_{2k-1}
a^{1-s-2k}`: for every `K` the remainder after `K` terms is `O(a^{-1-s-2K})`. -/
@[dlmf 25.11.E43]
theorem hurwitzZetaComplex_asymptotic {s : ℂ} (hs : s ≠ 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π)
    (K : ℕ) :
    (fun a => hurwitzZetaComplex s a - a ^ (1 - s) / (s - 1) - a ^ (-s) / 2 -
        ∑ k ∈ Finset.Icc 1 K, (bernoulli (2 * k) : ℂ) / (2 * k)! * pochhammer s (2 * k - 1) *
          a ^ (1 - s - 2 * k))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 (phaseSector δ)] (fun a => a ^ (-1 - s - 2 * K)) := by
  sorry

/-- **Large-`a` expansion of `ζ'(-1, a)`** (DLMF 25.11.44), `0 < δ < π`, `|ph a| ≤ π - δ`:
`ζ'(-1,a) - 1/12 + a²/4 - (1/12 - a/2 + a²/2) ln a ∼ -∑_{k≥1} B_{2k+2}/((2k+2)(2k+1)2k) a^{-2k}`. -/
@[dlmf 25.11.E44]
theorem deriv_hurwitzZetaComplex_neg_one_asymptotic {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π) (K : ℕ) :
    (fun a : ℂ => deriv (fun s => hurwitzZetaComplex s a) (-1) - 1 / 12 + a ^ 2 / 4 -
        (1 / 12 - a / 2 + a ^ 2 / 2) * Complex.log a +
        ∑ k ∈ Finset.Icc 1 K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2) * (2 * k + 1) * (2 * k)) *
          a ^ (-(2 * k : ℤ)))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 (phaseSector δ)] (fun a => a ^ (-(2 * K + 2 : ℤ))) := by
  sorry

/-- **Large-`a` expansion of `ζ'(-2, a)`** (DLMF 25.11.45), `0 < δ < π`, `|ph a| ≤ π - δ`:
`ζ'(-2,a) - a/12 + a³/9 - (a/6 - a²/2 + a³/3) ln a ∼
∑_{k≥1} 2B_{2k+2}/((2k+2)(2k+1)2k(2k-1)) a^{-(2k-1)}`. -/
@[dlmf 25.11.E45]
theorem deriv_hurwitzZetaComplex_neg_two_asymptotic {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π) (K : ℕ) :
    (fun a : ℂ => deriv (fun s => hurwitzZetaComplex s a) (-2) - a / 12 + a ^ 3 / 9 -
        (a / 6 - a ^ 2 / 2 + a ^ 3 / 3) * Complex.log a -
        ∑ k ∈ Finset.Icc 1 K, 2 * (bernoulli (2 * k + 2) : ℂ) /
          ((2 * k + 2) * (2 * k + 1) * (2 * k) * (2 * k - 1)) * a ^ (-(2 * k - 1 : ℤ)))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 (phaseSector δ)] (fun a => a ^ (-(2 * K + 1 : ℤ))) := by
  sorry

end DLMF.Zeta

end
