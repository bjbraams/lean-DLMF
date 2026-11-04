/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Identities
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction

/-!
# The quintuple product identity (DLMF 17.8.3)

This file proves the quintuple product identity
`∑_{n ∈ ℤ} (-1)ⁿ q^{n(3n-1)/2} z^{3n} (1 + z qⁿ) = (q, -z, -q/z; q)_∞ (qz², q/z²; q²)_∞`
for `0 < |q| < 1` and `z ≠ 0`.

## Main definitions

* `QuintupleProduct.productSide`: the product side of the identity.

## Main results

* `QuintupleProduct.hasSum_quintuple`: the quintuple product identity (DLMF 17.8.3).

## Implementation notes

Write `Θ(z) = ∑ (-1)ⁿ q^{n(n-1)/2} zⁿ = (q, z, q/z; q)_∞` (Jacobi triple product) and `S(z)` for
the quintuple series. The product side `P(z)` satisfies `Θ(z) P(z) = (q;q)_∞ Θ(z²)` by
elementary product manipulations. For the series side, the Laurent coefficients `c_m` of
`Θ(z) S(z)` are written in terms of the theta series `∑_n q^{6n² + bn}`; they satisfy
`c_{m+4} = q^{m+1} c_m`, and the four initial values follow from Euler's pentagonal number
theorem (Mathlib's `hasSum_eulerFunction_pentagonal`). Hence `Θ(z) S(z) = (q;q)_∞ Θ(z²)` as
well, and `S = P` off the zeros `z ∈ q^ℤ` of `Θ`; at those zeros the identity follows by
continuity, both sides being finite combinations of infinite products.
-/

@[expose] public noncomputable section

open Complex Finset Filter
open scoped Topology
open DLMF.QSeries DLMF.QSeries.TripleProduct

namespace DLMF.QHypergeometric.QuintupleProduct


/-- The theta-type series `∑_{n ∈ ℤ} q^{6n² + bn}`. -/
private def sixSeries (q : ℂ) (b : ℤ) : ℂ := ∑' n : ℤ, q ^ (6 * n ^ 2 + b * n)

/-- `tri (n+1) = tri n + n`. -/
private lemma tri_add_one (n : ℤ) : tri (n + 1) = tri n + n := by
  have h1 := tri_mul_two (n + 1)
  have h2 := tri_mul_two n
  linarith

/-- `(-1)^{m+2n} = (-1)^m`. -/
private lemma neg_one_zpow_add_two_mul (m n : ℤ) : (-1 : ℂ) ^ (m + 2 * n) = (-1) ^ m := by
  rw [zpow_add₀ (by norm_num), zpow_mul]; norm_num

/-- The terms `q^{6n²+bn}` as triple-product terms in base `q¹²`. -/
private lemma zpow_sixSeries_eq_term {q : ℂ} (hq0 : q ≠ 0) (b n : ℤ) :
    q ^ (6 * n ^ 2 + b * n) = term (q ^ 12) (-q ^ (6 + b)) n := by
  have h := tri_mul_two n
  have hneg : ((-1 : ℂ) ^ n) * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_zpow]; norm_num
  rw [term, neg_eq_neg_one_mul (q ^ (6 + b)), mul_zpow, ← zpow_natCast q 12, ← zpow_mul,
    ← zpow_mul]
  have he : 6 * n ^ 2 + b * n = (12 : ℕ) * tri n + (6 + b) * n := by push_cast; nlinarith
  rw [he, zpow_add₀ hq0]
  linear_combination (-(q ^ ((12 : ℕ) * tri n) * q ^ ((6 + b) * n))) * hneg

/-- Absolute summability of `∑ q^{6n²+bn}`. -/
private lemma summable_norm_sixSeries {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (b : ℤ) :
    Summable fun n : ℤ => ‖q ^ (6 * n ^ 2 + b * n)‖ := by
  have hQ : ‖q ^ 12‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have := summable_norm_term hQ (pow_ne_zero _ hq0) (neg_ne_zero.mpr (zpow_ne_zero (6 + b) hq0))
  simpa only [← zpow_sixSeries_eq_term hq0] using this

/-- `∑ q^{6n²-bn} = ∑ q^{6n²+bn}`. -/
private lemma sixSeries_neg (q : ℂ) (b : ℤ) : sixSeries q (-b) = sixSeries q b := by
  rw [sixSeries, sixSeries, ← (Equiv.neg ℤ).tsum_eq]
  congr 1; funext n; simp only [Equiv.neg_apply]; congr 1; ring

/-- Shifting the linear coefficient by `12r`. -/
private lemma sixSeries_add_twelve_mul {q : ℂ} (hq0 : q ≠ 0) (b r : ℤ) :
    sixSeries q (b + 12 * r) = q ^ (-(6 * r ^ 2 + b * r)) * sixSeries q b := by
  rw [sixSeries, sixSeries, ← tsum_mul_left]
  conv_rhs => rw [← (Equiv.addRight r).tsum_eq]
  congr 1; funext n
  simp only [Equiv.coe_addRight]
  rw [← zpow_add₀ hq0]; congr 1; ring

/-- Shifting the linear coefficient by `-12`. -/
private lemma sixSeries_sub_twelve {q : ℂ} (hq0 : q ≠ 0) (b : ℤ) :
    sixSeries q (b - 12) = q ^ (b - 6) * sixSeries q b := by
  have h := sixSeries_add_twelve_mul hq0 (b - 12) 1
  rw [show b - 12 + 12 * 1 = b by ring] at h
  rw [h, ← mul_assoc, ← zpow_add₀ hq0]
  rw [show b - 6 + -(6 * 1 ^ 2 + (b - 12) * 1) = 0 by ring, zpow_zero, one_mul]

/-- A sum over `ℤ` split into even and odd indices. -/
private lemma hasSum_int_even_add_odd {f : ℤ → ℂ} {a b : ℂ} (he : HasSum (fun k => f (2 * k)) a)
    (ho : HasSum (fun k => f (2 * k + 1)) b) : HasSum f (a + b) := by
  have := mul_right_injective₀ (two_ne_zero' ℤ)
  replace ho := ((add_left_injective 1).comp this).hasSum_range_iff.2 ho
  refine (this.hasSum_range_iff.2 he).add_isCompl ?_ ho
  simpa [Function.comp_def] using Int.isCompl_even_odd

/-- Euler's pentagonal theorem in the form `(q;q)_∞ = ∑ q^{6n²+n} - q ∑ q^{6n²+5n}`. -/
private lemma qPochhammerInf_self_eq_sixSeries {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    qPochhammerInf q q = sixSeries q 1 - q * sixSeries q 5 := by
  have h := hasSum_eulerFunction_pentagonal hq
  rw [eulerFunction_eq_tprod hq] at h
  have hP : (∏' n : ℕ, (1 - q ^ (n + 1))) = qPochhammerInf q q := by
    rw [qPochhammerInf]; congr 1; funext n; ring
  rw [hP] at h
  have hpow : ∀ k : ℤ, (k.negOnePow : ℂ) * q ^ pentagonal k =
      (-1) ^ k * q ^ (k * (3 * k - 1) / 2) := by
    intro k
    have hs : (-1 : ℂ) ^ k = (-1) ^ k.natAbs := by
      rcases Int.natAbs_eq k with h | h
      · conv_lhs => rw [h]
        rw [zpow_natCast]
      · conv_lhs => rw [h]
        rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
    rw [Int.coe_negOnePow, ← natCast_pentagonal, zpow_natCast, hs]
  simp_rw [hpow] at h
  have he : HasSum (fun n : ℤ => (-1 : ℂ) ^ (2 * n) * q ^ (2 * n * (3 * (2 * n) - 1) / 2))
      (sixSeries q (-1)) := by
    have := (summable_norm_sixSeries hq0 hq (-1)).of_norm.hasSum
    convert this using 1
    funext n
    rw [zpow_mul]; norm_num
    congr 1
    rw [show 2 * n * (3 * (2 * n) - 1) = 2 * (n * (6 * n - 1)) by ring,
      Int.mul_ediv_cancel_left _ two_ne_zero]
    ring
    rfl
  have ho : HasSum (fun n : ℤ => (-1 : ℂ) ^ (2 * n + 1) *
      q ^ ((2 * n + 1) * (3 * (2 * n + 1) - 1) / 2)) (-(q * sixSeries q 5)) := by
    have := ((summable_norm_sixSeries hq0 hq 5).of_norm.hasSum.mul_left q).neg
    convert this using 1
    funext n
    rw [zpow_add₀ (by norm_num), zpow_mul]; norm_num
    rw [show (2 * n + 1) * (3 * (2 * n + 1) - 1) = 2 * (6 * n ^ 2 + 5 * n + 1) by ring,
      Int.mul_ediv_cancel_left _ two_ne_zero, zpow_add₀ hq0, zpow_one]
    ring
    rfl
  rw [h.unique (hasSum_int_even_add_odd he ho), sixSeries_neg]
  ring


/-- The division in `n(3n-1)/2` is exact. -/
private lemma quintuple_exponent_mul_two (n : ℤ) : n * (3 * n - 1) / 2 * 2 = n * (3 * n - 1) := by
  apply Int.ediv_mul_cancel
  have : n * (3 * n - 1) = n * (n - 1) + 2 * n ^ 2 := by ring
  rw [this]
  exact dvd_add (even_iff_two_dvd.mp (Int.even_mul_pred_self n)) (dvd_mul_right 2 _)

/-- The products of coefficients contributing to `A_m`. -/
private lemma term_one_mul_sigma_zero {q : ℂ} (hq0 : q ≠ 0) (m n : ℤ) :
    term q 1 (m - 3 * n) * ((-1) ^ n * q ^ (n * (3 * n - 1) / 2)) =
      (-1) ^ m * q ^ tri m * q ^ (6 * n ^ 2 + (1 - 3 * m) * n) := by
  have h1 : (-1 : ℂ) ^ (m - 3 * n) * (-1) ^ n = (-1) ^ m := by
    rw [← zpow_add₀ (by norm_num), show m - 3 * n + n = m + 2 * (-n) by ring,
      neg_one_zpow_add_two_mul]
  have hexp : tri (m - 3 * n) + n * (3 * n - 1) / 2 = tri m + (6 * n ^ 2 + (1 - 3 * m) * n) := by
    have := tri_mul_two (m - 3 * n)
    have := tri_mul_two m
    have := quintuple_exponent_mul_two n
    linarith
  have h2 : q ^ tri (m - 3 * n) * q ^ (n * (3 * n - 1) / 2) =
      q ^ tri m * q ^ (6 * n ^ 2 + (1 - 3 * m) * n) := by
    rw [← zpow_add₀ hq0, ← zpow_add₀ hq0, hexp]
  simp only [term, one_zpow, mul_one]
  calc (-1) ^ (m - 3 * n) * q ^ tri (m - 3 * n) * ((-1) ^ n * q ^ (n * (3 * n - 1) / 2))
      = ((-1 : ℂ) ^ (m - 3 * n) * (-1) ^ n) * (q ^ tri (m - 3 * n) *
          q ^ (n * (3 * n - 1) / 2)) := by ring
    _ = _ := by rw [h1, h2]; ring

/-- The products of coefficients contributing to `B_m`. -/
private lemma term_one_mul_sigma_one {q : ℂ} (hq0 : q ≠ 0) (m n : ℤ) :
    term q 1 (m - 3 * n - 1) * ((-1) ^ n * q ^ (n * (3 * n - 1) / 2) * q ^ n) =
      -((-1) ^ m * q ^ tri (m - 1) * q ^ (6 * n ^ 2 + (5 - 3 * m) * n)) := by
  have h1 : (-1 : ℂ) ^ (m - 3 * n - 1) * (-1) ^ n = -(-1) ^ m := by
    rw [← zpow_add₀ (by norm_num), show m - 3 * n - 1 + n = (m - 1) + 2 * (-n) by ring,
      neg_one_zpow_add_two_mul, zpow_sub₀ (by norm_num), zpow_one]
    ring
  have hexp : tri (m - 3 * n - 1) + n * (3 * n - 1) / 2 + n =
      tri (m - 1) + (6 * n ^ 2 + (5 - 3 * m) * n) := by
    have := tri_mul_two (m - 3 * n - 1)
    have := tri_mul_two (m - 1)
    have := quintuple_exponent_mul_two n
    linarith
  have h2 : q ^ tri (m - 3 * n - 1) * q ^ (n * (3 * n - 1) / 2) * q ^ n =
      q ^ tri (m - 1) * q ^ (6 * n ^ 2 + (5 - 3 * m) * n) := by
    rw [← zpow_add₀ hq0, ← zpow_add₀ hq0, ← zpow_add₀ hq0, hexp]
  simp only [term, one_zpow, mul_one]
  calc (-1) ^ (m - 3 * n - 1) * q ^ tri (m - 3 * n - 1) *
        ((-1) ^ n * q ^ (n * (3 * n - 1) / 2) * q ^ n)
      = ((-1 : ℂ) ^ (m - 3 * n - 1) * (-1) ^ n) * (q ^ tri (m - 3 * n - 1) *
          q ^ (n * (3 * n - 1) / 2) * q ^ n) := by ring
    _ = _ := by rw [h1, h2]; ring

/-- The closed form of the Laurent coefficients of `Θ(z) S(z)`. -/
private def coefficient (q : ℂ) (m : ℤ) : ℂ :=
  (-1) ^ m * (q ^ tri m * sixSeries q (1 - 3 * m) - q ^ tri (m - 1) * sixSeries q (5 - 3 * m))

/-- The target coefficients `(q;q)_∞ θ_{m/2}`. -/
private def targetCoefficient (q : ℂ) (m : ℤ) : ℂ :=
  (sixSeries q 1 - q * sixSeries q 5) * (if Even m then term q 1 (m / 2) else 0)

/-- `θ_{s+1} = -q^s θ_s`. -/
private lemma term_one_add_one {q : ℂ} (hq0 : q ≠ 0) (s : ℤ) :
    term q 1 (s + 1) = -q ^ s * term q 1 s := by
  simp only [term, one_zpow, mul_one]
  rw [tri_add_one, zpow_add₀ (by norm_num), zpow_add₀ hq0, zpow_one]
  ring

/-- The recurrence `c_{m+4} = q^{m+1} c_m`. -/
private lemma coefficient_add_four {q : ℂ} (hq0 : q ≠ 0) (m : ℤ) :
    coefficient q (m + 4) = q ^ (m + 1) * coefficient q m := by
  have hA := sixSeries_sub_twelve hq0 (1 - 3 * m)
  have hB := sixSeries_sub_twelve hq0 (5 - 3 * m)
  rw [show 1 - 3 * m - 12 = 1 - 3 * (m + 4) by ring] at hA
  rw [show 5 - 3 * m - 12 = 5 - 3 * (m + 4) by ring] at hB
  have t1 : tri (m + 4) = tri m + 4 * m + 6 := by
    have := tri_mul_two (m + 4); have := tri_mul_two m; linarith
  have t2 : tri (m + 4 - 1) = tri (m - 1) + 4 * m + 2 := by
    have := tri_mul_two (m + 4 - 1); have := tri_mul_two (m - 1); linarith
  have e1 : q ^ tri (m + 4) * q ^ (1 - 3 * m - 6) = q ^ (m + 1) * q ^ tri m := by
    rw [← zpow_add₀ hq0, ← zpow_add₀ hq0, t1]; congr 1; ring
  have e2 : q ^ tri (m + 4 - 1) * q ^ (5 - 3 * m - 6) = q ^ (m + 1) * q ^ tri (m - 1) := by
    rw [← zpow_add₀ hq0, ← zpow_add₀ hq0, t2]; congr 1; ring
  have hs : (-1 : ℂ) ^ (m + 4) = (-1) ^ m := by
    rw [show m + 4 = m + 2 * 2 by ring, neg_one_zpow_add_two_mul]
  rw [coefficient, coefficient, hA, hB, hs]
  linear_combination (-1 : ℂ) ^ m * (sixSeries q (1 - 3 * m) * e1 -
    sixSeries q (5 - 3 * m) * e2)

/-- The target coefficients satisfy the same recurrence. -/
private lemma targetCoefficient_add_four {q : ℂ} (hq0 : q ≠ 0) (m : ℤ) :
    targetCoefficient q (m + 4) = q ^ (m + 1) * targetCoefficient q m := by
  rw [targetCoefficient, targetCoefficient]
  by_cases hm : Even m
  · have hm4 : Even (m + 4) := hm.add (by decide)
    obtain ⟨s, rfl⟩ := hm
    have hs : Even (s + s) := ⟨s, rfl⟩
    rw [ite_eq_left hm4, ite_eq_left hs, show s + s + 4 = (s + 1 + 1) * 2 by ring,
      show s + s = s * 2 by ring, Int.mul_ediv_cancel _ two_ne_zero,
      Int.mul_ediv_cancel _ two_ne_zero, term_one_add_one hq0, term_one_add_one hq0,
      show s * 2 + 1 = s + (s + 1) by ring]
    simp only [zpow_add₀ hq0, zpow_one]
    ring
  · have hm4 : ¬ Even (m + 4) := fun h => hm (by
      have := h.sub (show Even (4 : ℤ) by decide); simpa using this)
    rw [ite_eq_right hm4, ite_eq_right hm]; ring

/-- The Laurent coefficients of `Θ(z) S(z)` are those of `(q;q)_∞ Θ(z²)`. -/
private lemma coefficient_eq_targetCoefficient {q : ℂ} (hq0 : q ≠ 0) (m : ℤ) :
    coefficient q m = targetCoefficient q m := by
  have hstep : ∀ m, coefficient q m = targetCoefficient q m ↔
      coefficient q (m + 4) = targetCoefficient q (m + 4) := by
    intro m
    rw [coefficient_add_four hq0, targetCoefficient_add_four hq0]
    exact (mul_right_inj' (zpow_ne_zero _ hq0)).symm
  have hbase : ∀ ρ : ℤ, 0 ≤ ρ → ρ < 4 → coefficient q ρ = targetCoefficient q ρ := by
    intro ρ h0 h4
    have hG8 := sixSeries_sub_twelve hq0 4
    norm_num at hG8
    interval_cases ρ <;>
      simp [coefficient, targetCoefficient, tri, sixSeries_neg, hG8, term]
    rw [ite_eq_right (by decide)]; field_simp; ring
  have hall : ∀ k : ℤ, ∀ ρ, coefficient q ρ = targetCoefficient q ρ →
      coefficient q (ρ + 4 * k) = targetCoefficient q (ρ + 4 * k) := by
    intro k
    induction k using Int.induction_on with
    | zero => intro ρ h; simpa using h
    | succ k ih =>
      intro ρ h
      rw [show ρ + 4 * (k + 1) = ρ + 4 * k + 4 by ring, ← hstep]; exact ih ρ h
    | pred k ih =>
      intro ρ h
      rw [hstep, show ρ + 4 * (-k - 1) + 4 = ρ + 4 * (-k) by ring]; exact ih ρ h
  have := hall (m / 4) (m % 4) (hbase _ (Int.emod_nonneg _ (by norm_num))
    (Int.emod_lt_of_pos _ (by norm_num)))
  rwa [Int.emod_add_mul_ediv] at this


/-- Separating the variable from a triple-product term. -/
private lemma term_eq_term_one_mul (q z : ℂ) (n : ℤ) : term q z n = term q 1 n * z ^ n := by
  simp [term]

/-- The Jacobi triple product in the `term` form. -/
private lemma tsum_term_eq_prod {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    ∑' n : ℤ, term q z n = qPochhammerInf q q * qPochhammerInf z q * qPochhammerInf (q / z) q := by
  rw [jacobi_triple_product hq hz]
  congr 1; funext n; rw [term, cpow_tri]

/-- Cauchy product of a Laurent series with a series in `z^{3n+ε}`, collected by powers. -/
private lemma hasSum_laurent_mul (θ σ : ℤ → ℂ) {z : ℂ} (hz : z ≠ 0) (ε : ℤ)
    (hθ : Summable fun a => ‖θ a * z ^ a‖) (hσ : Summable fun n => ‖σ n * z ^ (3 * n + ε)‖) :
    HasSum (fun m : ℤ => (∑' n, θ (m - 3 * n - ε) * σ n) * z ^ m)
      ((∑' a, θ a * z ^ a) * ∑' n, σ n * z ^ (3 * n + ε)) := by
  set P : ℤ × ℤ → ℂ := fun p => θ p.1 * z ^ p.1 * (σ p.2 * z ^ (3 * p.2 + ε))
  have hP : HasSum P ((∑' a, θ a * z ^ a) * ∑' n, σ n * z ^ (3 * n + ε)) := by
    rw [tsum_mul_tsum_of_summable_norm hθ hσ]
    exact (summable_mul_of_summable_norm hθ hσ).hasSum
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1 - 3 * p.2 - ε, p.2)
      invFun := fun p => (p.1 + 3 * p.2 + ε, p.2)
      left_inv := fun p => Prod.ext (by dsimp only; ring) rfl
      right_inv := fun p => Prod.ext (by dsimp only; ring) rfl }
  have hPe : HasSum (P ∘ e) ((∑' a, θ a * z ^ a) * ∑' n, σ n * z ^ (3 * n + ε)) :=
    e.hasSum_iff.mpr hP
  have hterm : ∀ m n : ℤ, (P ∘ e) (m, n) = θ (m - 3 * n - ε) * σ n * z ^ m := by
    intro m n
    simp only [P, e, Function.comp_apply, Equiv.coe_fn_mk]
    have : z ^ (m - 3 * n - ε) * z ^ (3 * n + ε) = z ^ m := by
      rw [← zpow_add₀ hz]; congr 1; ring
    linear_combination θ (m - 3 * n - ε) * σ n * this
  refine hPe.prod_fiberwise fun m => ?_
  have hs := hPe.summable.prod_factor m
  convert hs.hasSum using 1
  rw [← tsum_mul_right]; congr 1; funext n; exact (hterm m n).symm

/-- The first half of the quintuple summand is a triple-product term in base `q³`. -/
private lemma sigma_zero_eq_term {q : ℂ} (hq0 : q ≠ 0) (z : ℂ) (n : ℤ) :
    (-1) ^ n * q ^ (n * (3 * n - 1) / 2) * z ^ (3 * n + 0) = term (q ^ 3) (q * z ^ 3) n := by
  simp only [term, add_zero]
  have hexp : n * (3 * n - 1) / 2 = 3 * tri n + n := by
    have := tri_mul_two n; have := quintuple_exponent_mul_two n; linarith
  rw [hexp, zpow_add₀ hq0, mul_zpow, show (q ^ 3 : ℂ) = q ^ (3 : ℤ) by norm_cast, ← zpow_mul,
    zpow_mul z 3 n]
  norm_cast
  ring

/-- The second half of the quintuple summand is a triple-product term in base `q³`. -/
private lemma sigma_one_eq_term {q z : ℂ} (hq0 : q ≠ 0) (hz : z ≠ 0) (n : ℤ) :
    (-1) ^ n * q ^ (n * (3 * n - 1) / 2) * q ^ n * z ^ (3 * n + 1) =
      z * term (q ^ 3) (q ^ 2 * z ^ 3) n := by
  simp only [term]
  have hexp : n * (3 * n - 1) / 2 + n = 3 * tri n + 2 * n := by
    have := tri_mul_two n; have := quintuple_exponent_mul_two n; linarith
  rw [mul_assoc ((-1) ^ n), ← zpow_add₀ hq0, hexp, zpow_add₀ hq0, zpow_add₀ hz, zpow_one,
    mul_zpow, show (q ^ 3 : ℂ) = q ^ (3 : ℤ) by norm_cast, ← zpow_mul,
    show (q ^ 2 : ℂ) = q ^ (2 : ℤ) by norm_cast, ← zpow_mul,
    show (z ^ 3 : ℂ) = z ^ (3 : ℤ) by norm_cast, ← zpow_mul]
  ring

/-- The quintuple series times the theta series: `Θ(z) S(z) = (q;q)_∞ Θ(z²)`. -/
private lemma theta_mul_quintuple {q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    HasSum (fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n - 1) / 2) * z ^ (3 * n) *
      (1 + z * q ^ n)) (∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (3 * n - 1) / 2) * z ^ (3 * n) *
      (1 + z * q ^ n)) ∧
    (∑' n : ℤ, term q z n) * (∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (3 * n - 1) / 2) *
      z ^ (3 * n) * (1 + z * q ^ n)) = qPochhammerInf q q * ∑' n : ℤ, term q (z ^ 2) n := by
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hq30 : q ^ 3 ≠ 0 := pow_ne_zero _ hq0
  set σ0 : ℤ → ℂ := fun n => (-1) ^ n * q ^ (n * (3 * n - 1) / 2)
  set σ1 : ℤ → ℂ := fun n => (-1) ^ n * q ^ (n * (3 * n - 1) / 2) * q ^ n
  have hσ0 : ∀ n, σ0 n * z ^ (3 * n + 0) = term (q ^ 3) (q * z ^ 3) n :=
    fun n => sigma_zero_eq_term hq0 z n
  have hσ1 : ∀ n, σ1 n * z ^ (3 * n + 1) = z * term (q ^ 3) (q ^ 2 * z ^ 3) n :=
    fun n => sigma_one_eq_term hq0 hz n
  have hz3 : ∀ c : ℂ, c ≠ 0 → c * z ^ 3 ≠ 0 := fun c hc => mul_ne_zero hc (pow_ne_zero _ hz)
  have hs0 : Summable fun n => ‖σ0 n * z ^ (3 * n + 0)‖ := by
    simp_rw [hσ0]; exact summable_norm_term hq3 hq30 (hz3 q hq0)
  have hs1 : Summable fun n => ‖σ1 n * z ^ (3 * n + 1)‖ := by
    simp_rw [hσ1, norm_mul]
    exact (summable_norm_term hq3 hq30 (hz3 _ (pow_ne_zero 2 hq0))).mul_left _
  have hθ : Summable fun a => ‖term q 1 a * z ^ a‖ := by
    simp_rw [← term_eq_term_one_mul]; exact summable_norm_term hq hq0 hz
  have hsplit : ∀ n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (3 * n - 1) / 2) * z ^ (3 * n) *
      (1 + z * q ^ n) = σ0 n * z ^ (3 * n + 0) + σ1 n * z ^ (3 * n + 1) := by
    intro n; simp only [σ0, σ1, add_zero]; rw [zpow_add₀ hz, zpow_one]; ring
  have hS : HasSum (fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n - 1) / 2) * z ^ (3 * n) *
      (1 + z * q ^ n)) ((∑' n, σ0 n * z ^ (3 * n + 0)) + ∑' n, σ1 n * z ^ (3 * n + 1)) := by
    simp_rw [hsplit]; exact hs0.of_norm.hasSum.add hs1.of_norm.hasSum
  refine ⟨hS.summable.hasSum, ?_⟩
  rw [hS.tsum_eq]
  have h0 := hasSum_laurent_mul (term q 1) σ0 hz 0 hθ hs0
  have h1 := hasSum_laurent_mul (term q 1) σ1 hz 1 hθ hs1
  have hT : (∑' n : ℤ, term q z n) = ∑' a, term q 1 a * z ^ a := by
    congr 1; funext a; exact term_eq_term_one_mul q z a
  rw [hT, mul_add]
  have hsum := h0.add h1
  have hcoef : ∀ m : ℤ, (∑' n, term q 1 (m - 3 * n - 0) * σ0 n) * z ^ m +
      (∑' n, term q 1 (m - 3 * n - 1) * σ1 n) * z ^ m = coefficient q m * z ^ m := by
    intro m
    have hA : (∑' n, term q 1 (m - 3 * n - 0) * σ0 n) =
        (-1) ^ m * q ^ tri m * sixSeries q (1 - 3 * m) := by
      rw [sixSeries, ← tsum_mul_left]; congr 1; funext n
      simp only [sub_zero, σ0]; exact term_one_mul_sigma_zero hq0 m n
    have hB : (∑' n, term q 1 (m - 3 * n - 1) * σ1 n) =
        -((-1) ^ m * q ^ tri (m - 1) * sixSeries q (5 - 3 * m)) := by
      rw [sixSeries, ← tsum_mul_left, ← tsum_neg]; congr 1; funext n
      simp only [σ1]; rw [term_one_mul_sigma_one hq0 m n]
    rw [hA, hB, coefficient]; ring
  simp_rw [hcoef, coefficient_eq_targetCoefficient hq0] at hsum
  have hE := qPochhammerInf_self_eq_sixSeries hq0 hq
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero _ hz
  have hT2 : HasSum (fun m : ℤ => targetCoefficient q m * z ^ m)
      (qPochhammerInf q q * ∑' n : ℤ, term q (z ^ 2) n) := by
    have hinj : Function.Injective fun s : ℤ => 2 * s := mul_right_injective₀ two_ne_zero
    have hbase := (summable_norm_term hq hq0 hz2).of_norm.hasSum.mul_left (qPochhammerInf q q)
    rw [← hinj.hasSum_iff]
    · convert hbase using 1
      funext s
      simp only [Function.comp_apply, targetCoefficient, ← hE, even_two_mul, ite_true,
        Int.mul_ediv_cancel_left _ two_ne_zero, term_eq_term_one_mul q (z ^ 2), zpow_mul]
      norm_cast
      ring
    · intro m hm
      simp only [targetCoefficient]
      rw [ite_eq_right, mul_zero, zero_mul]
      rintro ⟨s, rfl⟩
      exact hm ⟨s, by dsimp only; ring⟩
  exact hsum.unique hT2


/-- `(a;p)_∞ (-a;p)_∞ = (a²;p²)_∞`. -/
private lemma qPochhammerInf_mul_neg_self {a p : ℂ} (hp : ‖p‖ < 1) :
    qPochhammerInf a p * qPochhammerInf (-a) p = qPochhammerInf (a ^ 2) (p ^ 2) := by
  rw [qPochhammerInf, qPochhammerInf, qPochhammerInf,
    ← (multipliable_one_sub_mul_pow hp).tprod_mul (multipliable_one_sub_mul_pow hp)]
  congr 1; funext k; ring

/-- `(a;q)_∞ = (a;q²)_∞ (aq;q²)_∞`. -/
private lemma qPochhammerInf_eq_mul_sq_base {a q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf a q = qPochhammerInf a (q ^ 2) * qPochhammerInf (a * q) (q ^ 2) := by
  have hp : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  rw [qPochhammerInf, qPochhammerInf, qPochhammerInf, ← tprod_even_mul_odd]
  · congr 1
    · congr 1; funext k; rw [pow_mul]
    · congr 1; funext k; rw [pow_succ, pow_mul]; ring
  · convert multipliable_one_sub_mul_pow (w := a) hp using 2; ring
  · convert multipliable_one_sub_mul_pow (w := a * q) hp using 2; ring

/-- The product side of the quintuple product identity. -/
def productSide (q z : ℂ) : ℂ :=
  qPochhammerInf q q * qPochhammerInf (-z) q * qPochhammerInf (-q / z) q *
    (qPochhammerInf (q * z ^ 2) (q ^ 2) * qPochhammerInf (q / z ^ 2) (q ^ 2))

/-- `Θ(z) P(z) = (q;q)_∞ Θ(z²)`. -/
private lemma theta_mul_productSide {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    (∑' n : ℤ, term q z n) * productSide q z = qPochhammerInf q q * ∑' n : ℤ, term q (z ^ 2) n := by
  rw [tsum_term_eq_prod hq hz, tsum_term_eq_prod hq (pow_ne_zero 2 hz), productSide,
    qPochhammerInf_eq_mul_sq_base (a := z ^ 2) hq,
    qPochhammerInf_eq_mul_sq_base (a := q / z ^ 2) hq,
    ← qPochhammerInf_mul_neg_self (a := z) hq,
    show q / z ^ 2 * q = (q / z) ^ 2 by field_simp,
    ← qPochhammerInf_mul_neg_self (a := q / z) hq, neg_div,
    show z ^ 2 * q = q * z ^ 2 by ring]
  ring

/-- The quintuple series as a sum of two triple products. -/
private def seriesSide (q z : ℂ) : ℂ :=
  ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (3 * n - 1) / 2) * z ^ (3 * n) * (1 + z * q ^ n)

/-- The quintuple series as a sum of two triple products. -/
private lemma seriesSide_eq_prod {q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    seriesSide q z =
      qPochhammerInf (q ^ 3) (q ^ 3) * qPochhammerInf (q * z ^ 3) (q ^ 3) *
          qPochhammerInf (q ^ 3 / (q * z ^ 3)) (q ^ 3) +
        z * (qPochhammerInf (q ^ 3) (q ^ 3) * qPochhammerInf (q ^ 2 * z ^ 3) (q ^ 3) *
          qPochhammerInf (q ^ 3 / (q ^ 2 * z ^ 3)) (q ^ 3)) := by
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hz3 : ∀ c : ℂ, c ≠ 0 → c * z ^ 3 ≠ 0 := fun c hc => mul_ne_zero hc (pow_ne_zero _ hz)
  rw [← tsum_term_eq_prod hq3 (hz3 q hq0), ← tsum_term_eq_prod hq3 (hz3 _ (pow_ne_zero 2 hq0)),
    ← tsum_mul_left, seriesSide,
    ← (summable_norm_term hq3 (pow_ne_zero 3 hq0) (hz3 q hq0)).of_norm.tsum_add
      ((summable_norm_term hq3 (pow_ne_zero 3 hq0) (hz3 _ (pow_ne_zero 2 hq0))).of_norm.mul_left z)]
  congr 1; funext n
  rw [← sigma_zero_eq_term hq0 z n, ← sigma_one_eq_term hq0 hz n, add_zero,
    zpow_add₀ hz (3 * n) 1, zpow_one]
  ring


/-- Continuity of `(f(z);Q)_∞`. -/
private lemma continuousAt_qPochhammerInf_comp {Q : ℂ} (hQ : ‖Q‖ < 1) {f : ℂ → ℂ} {z0 : ℂ}
    (hf : ContinuousAt f z0) : ContinuousAt (fun z => qPochhammerInf (f z) Q) z0 :=
  ((differentiable_qPochhammerInf_left hQ).continuous.continuousAt).comp hf

/-- Continuity of the series side away from `0`. -/
private lemma continuousAt_seriesSide {q z0 : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz0 : z0 ≠ 0) :
    ContinuousAt (seriesSide q) z0 := by
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have h1 : q * z0 ^ 3 ≠ 0 := mul_ne_zero hq0 (pow_ne_zero _ hz0)
  have h2 : q ^ 2 * z0 ^ 3 ≠ 0 := mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ hz0)
  have c1 : ContinuousAt (fun z => qPochhammerInf (q * z ^ 3) (q ^ 3)) z0 :=
    continuousAt_qPochhammerInf_comp hq3 (by fun_prop)
  have c2 : ContinuousAt (fun z => qPochhammerInf (q ^ 3 / (q * z ^ 3)) (q ^ 3)) z0 :=
    continuousAt_qPochhammerInf_comp hq3 (continuousAt_const.div (by fun_prop) h1)
  have c3 : ContinuousAt (fun z => qPochhammerInf (q ^ 2 * z ^ 3) (q ^ 3)) z0 :=
    continuousAt_qPochhammerInf_comp hq3 (by fun_prop)
  have c4 : ContinuousAt (fun z => qPochhammerInf (q ^ 3 / (q ^ 2 * z ^ 3)) (q ^ 3)) z0 :=
    continuousAt_qPochhammerInf_comp hq3 (continuousAt_const.div (by fun_prop) h2)
  have hc := ((continuousAt_const (y := qPochhammerInf (q ^ 3) (q ^ 3))).mul c1 |>.mul c2).add
    (continuousAt_id.mul (((continuousAt_const (y := qPochhammerInf (q ^ 3) (q ^ 3))).mul
      c3).mul c4))
  refine hc.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hz0] with z hz
  exact (seriesSide_eq_prod hq0 hq hz).symm

/-- Continuity of the product side away from `0`. -/
private lemma continuousAt_productSide {q z0 : ℂ} (hq : ‖q‖ < 1) (hz0 : z0 ≠ 0) :
    ContinuousAt (productSide q) z0 := by
  have hp : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  unfold productSide
  refine ((continuousAt_const.mul (continuousAt_qPochhammerInf_comp hq (by fun_prop))).mul
    (continuousAt_qPochhammerInf_comp hq (continuousAt_const.div continuousAt_id hz0))).mul
    ((continuousAt_qPochhammerInf_comp hp (by fun_prop)).mul
      (continuousAt_qPochhammerInf_comp hp (continuousAt_const.div (by fun_prop)
        (pow_ne_zero 2 hz0))))

/-- A vanishing infinite product has a vanishing factor. -/
private lemma exists_one_sub_eq_zero_of_qPochhammerInf_eq_zero {a q : ℂ} (hq : ‖q‖ < 1)
    (h : qPochhammerInf a q = 0) : ∃ n : ℕ, 1 - a * q ^ n = 0 := by
  by_contra hc
  exact qPochhammerInf_ne_zero hq (fun n hn => hc ⟨n, hn⟩) h

/-- The zeros of `Θ` are integer powers of `q`. -/
private lemma exists_eq_zpow_of_theta_eq_zero {q w : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hw : w ≠ 0)
    (h : ∑' n : ℤ, term q w n = 0) : ∃ k : ℤ, w = q ^ k := by
  rw [tsum_term_eq_prod hq hw] at h
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h (qPochhammerInf_ne_zero_of_norm_lt_one hq hq)
    · obtain ⟨n, hn⟩ := exists_one_sub_eq_zero_of_qPochhammerInf_eq_zero hq h
      refine ⟨-(n : ℤ), ?_⟩
      rw [zpow_neg, zpow_natCast]
      have : w * q ^ n = 1 := by linear_combination -hn
      field_simp; linear_combination this
  · obtain ⟨n, hn⟩ := exists_one_sub_eq_zero_of_qPochhammerInf_eq_zero hq h
    refine ⟨(n : ℤ) + 1, ?_⟩
    rw [zpow_add₀ hq0, zpow_natCast, zpow_one]
    field_simp at hn
    linear_combination hn

/-- `Θ` does not vanish at `q^k (1+t)` for `0 < t < |q|⁻¹ - 1`. -/
private lemma theta_ne_zero_of_mul {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (k : ℤ) {t : ℝ}
    (ht0 : 0 < t)
    (ht1 : t < ‖q‖⁻¹ - 1) : ∑' n : ℤ, term q (q ^ k * (1 + t)) n ≠ 0 := by
  have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hw : q ^ k * (1 + (t : ℂ)) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hq0) (by exact_mod_cast (by linarith : (1 + t) ≠ 0))
  intro h
  obtain ⟨j, hj⟩ := exists_eq_zpow_of_theta_eq_zero hq0 hq hw h
  have h1 : (1 + (t : ℂ)) = q ^ (j - k) := by
    rw [zpow_sub₀ hq0, ← hj]; field_simp
  have h2 : 1 + t = ‖q‖ ^ (j - k) := by
    have := congrArg norm h1
    rwa [norm_zpow, show (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg (by linarith)] at this
  rcases le_or_gt 0 (j - k) with hl | hl
  · have : ‖q‖ ^ (j - k) ≤ 1 := by
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hl
      rw [hm, zpow_natCast]; exact pow_le_one₀ (norm_nonneg _) hq.le
    linarith
  · have hle : ‖q‖⁻¹ ≤ ‖q‖ ^ (j - k) := by
      rw [← zpow_neg_one]
      exact zpow_le_zpow_right_of_le_one₀ hr hq.le (by omega)
    linarith

/-- The quintuple product identity, `0 < |q| < 1`, `z ≠ 0`. -/
theorem hasSum_quintuple {q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    HasSum (fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n - 1) / 2) * z ^ (3 * n) *
      (1 + z * q ^ n)) (productSide q z) := by
  have key : ∀ w : ℂ, w ≠ 0 → ∑' n : ℤ, term q w n ≠ 0 → seriesSide q w = productSide q w := by
    intro w hw hθ
    have h1 := (theta_mul_quintuple hq0 hq hw).2
    have h2 := theta_mul_productSide hq hw
    rw [← h2] at h1
    exact mul_left_cancel₀ hθ h1
  have hS := (theta_mul_quintuple hq0 hq hz).1
  suffices h : seriesSide q z = productSide q z by rw [← h]; exact hS
  by_cases hθ : ∑' n : ℤ, term q z n = 0
  · obtain ⟨k, rfl⟩ := exists_eq_zpow_of_theta_eq_zero hq0 hq hz hθ
    have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    have hr1 : 0 < ‖q‖⁻¹ - 1 := by
      rw [sub_pos, one_lt_inv₀ hr]; exact hq
    set γ : ℝ → ℂ := fun t => q ^ k * (1 + t)
    have hγ : Filter.Tendsto γ (𝓝[>] 0) (𝓝 (q ^ k)) := by
      have : Continuous γ := by fun_prop
      have h := this.tendsto 0
      simp only [γ, ofReal_zero, add_zero, mul_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), seriesSide q (γ t) = productSide q (γ t) := by
      have hI : Set.Ioo (0 : ℝ) (‖q‖⁻¹ - 1) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hr1
      filter_upwards [hI] with t ht
      have hγ0 : γ t ≠ 0 := mul_ne_zero (zpow_ne_zero _ hq0)
        (by exact_mod_cast (by linarith [ht.1] : (1 + t) ≠ 0))
      exact key _ hγ0 (theta_ne_zero_of_mul hq0 hq k ht.1 ht.2)
    have hA := (continuousAt_seriesSide hq0 hq hz).tendsto.comp hγ
    have hB := (continuousAt_productSide hq hz).tendsto.comp hγ
    exact tendsto_nhds_unique (hA.congr' hev) hB
  · exact key z hz hθ

end DLMF.QHypergeometric.QuintupleProduct
