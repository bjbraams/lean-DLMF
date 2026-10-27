/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.ContinuedFractions.Convergents

/-!
# Convergence of continued fractions (DLMF §1.12(v))

* **Pringsheim's theorem** (1.12.25): if `b₀ = 0` and `|b_n| ≥ |a_n| + 1` for `n ≥ 1`, then
  `|C_n| < 1` and `C_n → C` with `|C| ≤ 1`. The proof is the classical one: the canonical
  denominators satisfy `|B_n| - |B_{n-1}| ≥ |a₁ ⋯ a_n|`, so the series 1.12.9 of the convergents
  is dominated by the telescoping series `∑ (1/|B_{n-1}| - 1/|B_n|) ≤ 1`. The hypothesis
  `a_n ≠ 0` of DLMF is not needed (stronger than DLMF). It is proved in any complete normed
  field.
* **Van Vleck's theorem** (1.12.26–1.12.28), for `1/(b₁ + 1/(b₂ + ⋯))` with all `b_n` in the
  sector `|ph b_n| < π/2 - δ` (admitted).
-/

@[expose] public noncomputable section

open Filter Finset GenContFract
open scoped Topology

namespace DLMF.AlgebraicAnalytic

section Pringsheim

variable {K : Type*} [NormedField K] {a b : ℕ → K}

/-- Under the Pringsheim condition the canonical denominators satisfy
`|B_{m+1}| - |B_m| ≥ |a₁ ⋯ a_{m+1}|`. -/
lemma g1d_pringsheim_dens_diff (h : ∀ n, 1 ≤ n → ‖a n‖ + 1 ≤ ‖b n‖) (m : ℕ) :
    ∏ k ∈ range (m + 1), ‖a (k + 1)‖ ≤
      ‖(contFrac a b).dens (m + 1)‖ - ‖(contFrac a b).dens m‖ := by
  induction m with
  | zero =>
    simp only [zero_add, range_one, prod_singleton, contFrac_dens_one, contFrac_dens_zero,
      norm_one]
    linarith [h 1 le_rfl]
  | succ m ih =>
    rw [prod_range_succ, contFrac_dens_step]
    have h2 := h (m + 2) (by omega)
    have hn1 : ‖b (m + 2) * (contFrac a b).dens (m + 1)‖ -
        ‖a (m + 2) * (contFrac a b).dens m‖ ≤
        ‖b (m + 2) * (contFrac a b).dens (m + 1) + a (m + 2) * (contFrac a b).dens m‖ := by
      have := norm_sub_norm_le (b (m + 2) * (contFrac a b).dens (m + 1))
        (-(a (m + 2) * (contFrac a b).dens m))
      simpa only [norm_neg, sub_neg_eq_add] using this
    rw [norm_mul, norm_mul] at hn1
    have hd : 0 ≤ ‖(contFrac a b).dens (m + 1)‖ := norm_nonneg _
    have ha : 0 ≤ ‖a (m + 2)‖ := norm_nonneg _
    have key : ‖a (m + 2)‖ * (‖(contFrac a b).dens (m + 1)‖ - ‖(contFrac a b).dens m‖) ≤
        ‖b (m + 2)‖ * ‖(contFrac a b).dens (m + 1)‖ - ‖a (m + 2)‖ * ‖(contFrac a b).dens m‖ -
          ‖(contFrac a b).dens (m + 1)‖ := by
      nlinarith
    calc (∏ k ∈ range (m + 1), ‖a (k + 1)‖) * ‖a (m + 1 + 1)‖
        ≤ (‖(contFrac a b).dens (m + 1)‖ - ‖(contFrac a b).dens m‖) * ‖a (m + 2)‖ :=
          mul_le_mul_of_nonneg_right ih ha
      _ ≤ _ := by linarith

/-- Under the Pringsheim condition `|B_n| ≥ 1`. -/
lemma g1d_pringsheim_dens_ge_one (h : ∀ n, 1 ≤ n → ‖a n‖ + 1 ≤ ‖b n‖) (n : ℕ) :
    1 ≤ ‖(contFrac a b).dens n‖ := by
  induction n with
  | zero => simp
  | succ m ih =>
    have := g1d_pringsheim_dens_diff h m
    have : 0 ≤ ∏ k ∈ range (m + 1), ‖a (k + 1)‖ := prod_nonneg fun _ _ => norm_nonneg _
    linarith

/-- The telescoping bound `|C_{m+1} - C_m| ≤ 1/|B_m| - 1/|B_{m+1}|`. -/
lemma g1d_pringsheim_step (h : ∀ n, 1 ≤ n → ‖a n‖ + 1 ≤ ‖b n‖) (m : ℕ) :
    ‖(contFrac a b).convs (m + 1) - (contFrac a b).convs m‖ ≤
      1 / ‖(contFrac a b).dens m‖ - 1 / ‖(contFrac a b).dens (m + 1)‖ := by
  have h0 := g1d_pringsheim_dens_ge_one h m
  have h1 := g1d_pringsheim_dens_ge_one h (m + 1)
  have hne0 : (contFrac a b).dens m ≠ 0 := norm_pos_iff.mp (by linarith)
  have hne1 : (contFrac a b).dens (m + 1) ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [contFrac_convs_sub a b m hne0 hne1, norm_div, norm_mul, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul, norm_prod, div_sub_div _ _ (by positivity) (by positivity),
    one_mul, mul_one]
  exact div_le_div_of_nonneg_right (g1d_pringsheim_dens_diff h m) (by positivity)

/-- The partial sums of the telescoping bound. -/
lemma g1d_pringsheim_sum (n : ℕ) :
    ∑ m ∈ range n, (1 / ‖(contFrac a b).dens m‖ - 1 / ‖(contFrac a b).dens (m + 1)‖) =
      1 - 1 / ‖(contFrac a b).dens n‖ := by
  rw [sum_range_sub' (fun m => 1 / ‖(contFrac a b).dens m‖), contFrac_dens_zero, norm_one,
    div_one]

/-- DLMF 1.12.25 (Pringsheim's theorem), first part: if `b₀ = 0` and `|b_n| ≥ |a_n| + 1` for
`n ≥ 1`, then the convergents satisfy `|C_n| < 1` (for all `n ≥ 0`; `C₀ = 0`). Stronger than
DLMF: `a_n ≠ 0` is not assumed. -/
@[dlmf 1.12.E25]
theorem pringsheim_norm_convs_lt_one (hb0 : b 0 = 0) (h : ∀ n, 1 ≤ n → ‖a n‖ + 1 ≤ ‖b n‖)
    (n : ℕ) : ‖(contFrac a b).convs n‖ < 1 := by
  have hsum : ‖(contFrac a b).convs n‖ ≤ 1 - 1 / ‖(contFrac a b).dens n‖ := by
    rw [← g1d_pringsheim_sum (a := a) (b := b) n]
    have htel : (contFrac a b).convs n =
        ∑ m ∈ range n, ((contFrac a b).convs (m + 1) - (contFrac a b).convs m) := by
      rw [sum_range_sub (fun m => (contFrac a b).convs m), contFrac_convs_zero, hb0, sub_zero]
    rw [htel]
    exact (norm_sum_le _ _).trans (sum_le_sum fun m _ => g1d_pringsheim_step h m)
  have := g1d_pringsheim_dens_ge_one h n
  have : 0 < 1 / ‖(contFrac a b).dens n‖ := by positivity
  linarith

/-- DLMF 1.12.25 (Pringsheim's theorem): if `b₀ = 0` and `|b_n| ≥ |a_n| + 1` for `n ≥ 1`, the
continued fraction `a₁/(b₁ + a₂/(b₂ + ⋯))` converges, to a limit `C` with `|C| ≤ 1`. Stronger
than DLMF: `a_n ≠ 0` is not assumed; proved in any complete normed field. -/
@[dlmf 1.12.E25]
theorem pringsheim [CompleteSpace K] (hb0 : b 0 = 0) (h : ∀ n, 1 ≤ n → ‖a n‖ + 1 ≤ ‖b n‖) :
    ∃ C, ‖C‖ ≤ 1 ∧ Tendsto (contFrac a b).convs atTop (𝓝 C) := by
  set d : ℕ → ℝ := fun m => 1 / ‖(contFrac a b).dens m‖ - 1 / ‖(contFrac a b).dens (m + 1)‖
  have hd0 : ∀ m, 0 ≤ d m := fun m =>
    (norm_nonneg _).trans (g1d_pringsheim_step h m)
  have hds : Summable d := by
    refine summable_of_sum_range_le hd0 (c := 1) fun n => ?_
    rw [g1d_pringsheim_sum (a := a) (b := b) n]
    have := g1d_pringsheim_dens_ge_one h n
    have : 0 < 1 / ‖(contFrac a b).dens n‖ := by positivity
    linarith
  have hc : CauchySeq (contFrac a b).convs := by
    refine cauchySeq_of_dist_le_of_summable d (fun m => ?_) hds
    rw [dist_comm, dist_eq_norm]
    exact g1d_pringsheim_step h m
  obtain ⟨C, hC⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨C, le_of_tendsto' hC.norm fun n => (pringsheim_norm_convs_lt_one hb0 h n).le, hC⟩

/-- DLMF §1.12(v): under the Pringsheim condition 1.12.25 the continued fraction converges in
the sense of `ContFracConverges`. -/
@[dlmf 1.12.E25]
theorem contFracConverges_of_pringsheim [CompleteSpace K] (hb0 : b 0 = 0)
    (h : ∀ n, 1 ≤ n → ‖a n‖ + 1 ≤ ‖b n‖) : ContFracConverges a b :=
  let ⟨C, _, hC⟩ := pringsheim hb0 h
  ⟨C, hC⟩

end Pringsheim

section VanVleck

/-- DLMF 1.12.26–1.12.27 (Van Vleck's theorem, first part): if `b₀ = 0`, all partial numerators
are `1`, and `-π/2 + δ < ph b_n < π/2 - δ` for `n ≥ 1` (`δ > 0`), then the convergents satisfy
`-π/2 + δ < ph C_n < π/2 - δ` for `n ≥ 1` (in particular `C_n ≠ 0`). -/
@[dlmf 1.12.E26, dlmf 1.12.E27]
theorem vanVleck_arg_convs {b : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hb0 : b 0 = 0)
    (hb : ∀ n, 1 ≤ n → b n ≠ 0 ∧ |(b n).arg| < Real.pi / 2 - δ) (n : ℕ) (hn : 1 ≤ n) :
    (contFrac (fun _ => 1) b).convs n ≠ 0 ∧
      |((contFrac (fun _ => 1) b).convs n).arg| < Real.pi / 2 - δ := by
  sorry

/-- DLMF §1.12(v) (Van Vleck's theorem, second part): under 1.12.26 the even and odd parts of
`1/(b₁ + 1/(b₂ + ⋯))` converge to finite values, i.e. `C_{2n}` and `C_{2n+1}` converge. -/
@[dlmf 1.12.v]
theorem vanVleck_even_odd {b : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hb0 : b 0 = 0)
    (hb : ∀ n, 1 ≤ n → b n ≠ 0 ∧ |(b n).arg| < Real.pi / 2 - δ) :
    (∃ C, Tendsto (fun n => (contFrac (fun _ => 1) b).convs (2 * n)) atTop (𝓝 C)) ∧
      ∃ C, Tendsto (fun n => (contFrac (fun _ => 1) b).convs (2 * n + 1)) atTop (𝓝 C) := by
  sorry

/-- DLMF 1.12.28 (Van Vleck's theorem, third part): under 1.12.26 the continued fraction
`1/(b₁ + 1/(b₂ + ⋯))` converges iff `∑_{n ≥ 1} |b_n| = ∞`. -/
@[dlmf 1.12.E28]
theorem vanVleck_converges_iff {b : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hb0 : b 0 = 0)
    (hb : ∀ n, 1 ≤ n → b n ≠ 0 ∧ |(b n).arg| < Real.pi / 2 - δ) :
    ContFracConverges (fun _ => 1) b ↔ ¬ Summable fun n => ‖b (n + 1)‖ := by
  sorry

/-- DLMF §1.12(v) (Van Vleck's theorem, last part): under 1.12.26, if the continued fraction
converges to `C`, then `|ph C| ≤ π/2`. -/
@[dlmf 1.12.v]
theorem vanVleck_arg_limit {b : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hb0 : b 0 = 0)
    (hb : ∀ n, 1 ≤ n → b n ≠ 0 ∧ |(b n).arg| < Real.pi / 2 - δ) {C : ℂ}
    (hC : Tendsto (contFrac (fun _ => 1) b).convs atTop (𝓝 C)) : |C.arg| ≤ Real.pi / 2 := by
  rw [Complex.abs_arg_le_pi_div_two_iff]
  have hre : Tendsto (fun n => ((contFrac (fun _ => 1) b).convs n).re) atTop (𝓝 C.re) :=
    (Complex.continuous_re.tendsto C).comp hC
  refine ge_of_tendsto hre (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  obtain ⟨-, hn'⟩ := vanVleck_arg_convs hδ hb0 hb n hn
  have : |((contFrac (fun _ => 1) b).convs n).arg| ≤ Real.pi / 2 := by linarith
  exact Complex.abs_arg_le_pi_div_two_iff.mp this

end VanVleck

end DLMF.AlgebraicAnalytic
