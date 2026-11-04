/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.ModulusInversion
public import DLMF.Theta.Products.LogDerivativesAndDoubleProducts

/-!
# Monotonicity of the theta constants on the imaginary axis

For `τ = it`, `t > 0`, with real nome `q = e^{-πt}`: `θ₃(0|it)` is strictly decreasing and
`θ₄(0|it)` strictly increasing in `t` (from the series `∑ q^{n²}` and the product DLMF 20.4.5),
and `θ₃⁴ + θ₄⁴` at `it` is `4θ₃⁴ - 2θ₄⁴` at `2it` (from DLMF 20.7.11–20.7.12 for a real nome).
These give the monotonicity of the roots `e_j` of rectangular lattices (DLMF §23.5(ii)).

## Main results

* `Real.jacobiThetaThreeNullQ_lt`: `θ₃(q)` is strictly increasing in `0 < q < 1`.
* `jacobiThetaThreeImag_lt`, `jacobiThetaFourImag_lt`: strict monotonicity in `t`.
* `jacobiThetaThreeImag_pow_four_add`: `θ₃⁴(it) + θ₄⁴(it) = 4θ₃⁴(2it) - 2θ₄⁴(2it)`.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

noncomputable section

open DLMF.Elliptic DLMF.JacobiElliptic

namespace DLMF.Theta

/-- `θ₃(q) = ∑ q^{n²}` is strictly increasing in the real nome `0 < q < 1`. -/
theorem Real.jacobiThetaThreeNullQ_lt {q₁ q₂ : ℝ} (h0 : 0 < q₁) (h12 : q₁ < q₂) (h1 : q₂ < 1) :
    Real.jacobiThetaThreeNullQ q₁ < Real.jacobiThetaThreeNullQ q₂ := by
  refine Summable.tsum_lt_tsum (i := 1) (fun n => ?_) ?_ (summable_zpow_sq h0 (h12.trans h1))
    (summable_zpow_sq (h0.trans h12) h1)
  · exact zpow_le_zpow_left₀ (sq_nonneg n) h0.le h12.le
  · simpa using h12

/-- Comparison of infinite products of positive real factors: if `0 < g k ≤ f k` for all `k`,
with strict inequality at `k = 0`, then `∏ g < ∏ f`. -/
private lemma lt_of_tendsto_prod {f g : ℕ → ℝ} {A B : ℝ}
    (hA : Tendsto (fun n => ∏ k ∈ Finset.range n, f k) atTop (𝓝 A))
    (hB : Tendsto (fun n => ∏ k ∈ Finset.range n, g k) atTop (𝓝 B))
    (hg : ∀ k, 0 < g k) (hfg : ∀ k, g k ≤ f k) (h0 : g 0 < f 0) (hB0 : 0 < B) : B < A := by
  set r := f 0 / g 0 with hr
  have hr1 : 1 < r := by rw [hr, one_lt_div (hg 0)]; exact h0
  have key : ∀ n, r * ∏ k ∈ Finset.range (n + 1), g k ≤ ∏ k ∈ Finset.range (n + 1), f k := by
    intro n
    induction n with
    | zero => simp [hr, (hg 0).ne']
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ (fun k => f k), ← mul_assoc]
      exact mul_le_mul ih (hfg _) (hg _).le (le_trans (mul_nonneg (by linarith)
        (Finset.prod_nonneg fun k _ => (hg k).le)) ih)
  have hA' := hA.comp (tendsto_add_atTop_nat 1)
  have hB' := (hB.comp (tendsto_add_atTop_nat 1)).const_mul r
  have := le_of_tendsto_of_tendsto' hB' hA' key
  nlinarith

/-- The partial products of `θ₄(0|it) = ∏ (1 - q^{2k+2})(1 - q^{2k+1})²`, `q = e^{-πt}`. -/
private lemma tendsto_prod_jacobiThetaFourImag {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => ∏ k ∈ Finset.range n, ((1 - Real.exp (-(π * t)) ^ (2 * (k + 1))) *
      (1 - Real.exp (-(π * t)) ^ (2 * k + 1)) ^ 2)) atTop (𝓝 (jacobiThetaFourImag t)) := by
  have hτ : 0 < (I * (t : ℂ)).im := by simpa using ht
  obtain ⟨hm, he⟩ := jacobiThetaFourNullTau_prod hτ
  have hq : cexp (π * I * (I * t)) = ((Real.exp (-(π * t)) : ℝ) : ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  have h := hm.hasProd.tendsto_prod_nat
  rw [← he, hq] at h
  simp only [jacobiThetaFourNullTau, jacobiThetaFourTau_zero_I_mul_eq_imag] at h
  have h' := (Complex.continuous_re.tendsto _).comp h
  simp only [Function.comp_def, ofReal_re] at h'
  refine h'.congr fun n => ?_
  rw [← ofReal_one]
  simp only [← ofReal_pow, ← ofReal_sub, ← ofReal_mul, ← ofReal_prod, ofReal_re]

/-- `θ₄(0|it)` is strictly increasing in `t > 0`. -/
theorem jacobiThetaFourImag_lt {t₁ t₂ : ℝ} (h0 : 0 < t₁) (h12 : t₁ < t₂) :
    jacobiThetaFourImag t₁ < jacobiThetaFourImag t₂ := by
  set q₁ := Real.exp (-(π * t₁))
  set q₂ := Real.exp (-(π * t₂))
  have hq₂ : 0 < q₂ := Real.exp_pos _
  have hq21 : q₂ < q₁ := Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  have hq₁ : q₁ < 1 := _root_.Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hq0 : 0 < q₁ := Real.exp_pos _
  refine lt_of_tendsto_prod (tendsto_prod_jacobiThetaFourImag (h0.trans h12))
    (tendsto_prod_jacobiThetaFourImag h0) (fun k => ?_) (fun k => ?_) ?_
    (jacobiThetaFourImag_pos h0)
  · have a := pow_lt_one₀ hq0.le hq₁ (n := 2 * (k + 1)) (by omega)
    have b := pow_lt_one₀ hq0.le hq₁ (n := 2 * k + 1) (by omega)
    have : 0 < 1 - q₁ ^ (2 * k + 1) := by linarith
    positivity [sub_pos.mpr a]
  · have a := pow_le_pow_left₀ hq₂.le hq21.le (2 * (k + 1))
    have b := pow_le_pow_left₀ hq₂.le hq21.le (2 * k + 1)
    have b1 := pow_lt_one₀ hq0.le hq₁ (n := 2 * k + 1) (by omega)
    have a1 := pow_lt_one₀ hq0.le hq₁ (n := 2 * (k + 1)) (by omega)
    gcongr
    linarith
  · simp only [zero_add, mul_one, mul_zero, pow_one]
    have : q₂ ^ 2 < q₁ ^ 2 := by gcongr
    have : q₁ ^ 2 < 1 := by nlinarith
    gcongr

/-- `θ₃(0|it)` is strictly decreasing in `t > 0`. -/
theorem jacobiThetaThreeImag_lt {t₁ t₂ : ℝ} (h0 : 0 < t₁) (h12 : t₁ < t₂) :
    jacobiThetaThreeImag t₂ < jacobiThetaThreeImag t₁ :=
  Real.jacobiThetaThreeNullQ_lt (_root_.Real.exp_pos _)
    (_root_.Real.exp_lt_exp.mpr (by nlinarith [_root_.Real.pi_pos]))
    (_root_.Real.exp_lt_one_iff.mpr (by nlinarith [_root_.Real.pi_pos]))

/-- `θ₃⁴(0|it) + θ₄⁴(0|it) = 4θ₃⁴(0|2it) - 2θ₄⁴(0|2it)`. -/
theorem jacobiThetaThreeImag_pow_four_add {t : ℝ} (ht : 0 < t) :
    jacobiThetaThreeImag t ^ 4 + jacobiThetaFourImag t ^ 4 =
      4 * jacobiThetaThreeImag (2 * t) ^ 4 - 2 * jacobiThetaFourImag (2 * t) ^ 4 := by
  have hq0 : 0 < _root_.Real.exp (-(π * t)) := _root_.Real.exp_pos _
  have hq1 : _root_.Real.exp (-(π * t)) < 1 :=
    _root_.Real.exp_lt_one_iff.mpr (by nlinarith [_root_.Real.pi_pos])
  have hsq : _root_.Real.exp (-(π * t)) ^ 2 = _root_.Real.exp (-(π * (2 * t))) := by
    rw [← _root_.Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1 := Real.jacobiThetaThreeNullQ_sq_add_jacobiThetaFourNullQ_sq hq0 hq1
  have h2 := Real.jacobiThetaThreeNullQ_mul_jacobiThetaFourNullQ hq0 hq1
  rw [hsq] at h1 h2
  simp only [jacobiThetaThreeImag, jacobiThetaFourImag]
  linear_combination (Real.jacobiThetaThreeNullQ (_root_.Real.exp (-(π * t))) ^ 2 +
      Real.jacobiThetaFourNullQ (_root_.Real.exp (-(π * t))) ^ 2 +
      2 * Real.jacobiThetaThreeNullQ (_root_.Real.exp (-(π * (2 * t)))) ^ 2) * h1 -
    2 * (Real.jacobiThetaThreeNullQ (_root_.Real.exp (-(π * t))) *
      Real.jacobiThetaFourNullQ (_root_.Real.exp (-(π * t))) +
      Real.jacobiThetaFourNullQ (_root_.Real.exp (-(π * (2 * t)))) ^ 2) * h2

end DLMF.Theta
