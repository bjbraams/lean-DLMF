/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Identities

/-!
# Heine's transformations and summations (Duverney §§10.2–10.3)

From the `q`-binomial theorem and Heine's first transformation `heine_transformation`
(AAR §10.10):
* Euler's identity `∑ xⁿ/(q;q)_n = 1/(x;q)_∞` (Duverney (10.28)), and the product formula
  `₁φ₀(a;x) ₁φ₀(b;ax) = ₁φ₀(ab;x)` (Exercise 10.11);
* Heine's second and third transformations (Duverney (10.50)–(10.51)), by applying the first
  transformation twice and three times;
* Heine's `q`-Gauss summation (10.53) and its terminating case, `q`-Chu–Vandermonde (10.54).

The convergence hypotheses are those of the series manipulations (`|b| < 1`, `|c/b| < 1`, …).
Duverney removes them by viewing both sides as rational functions; that step is not formalized.
-/

@[expose] public section

open Complex Finset Filter
open scoped Topology

noncomputable section

namespace DLMF.QSeries

/-- Swapping the numerator parameters of `₂φ₁`. -/
theorem basicHG_swap (a b c q z : ℂ) : basicHG [a, b] [c] q z = basicHG [b, a] [c] q z := by
  simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  congr 1; funext n; ring

/-- `₂φ₁(d, w; d; q, z)` collapses to `₁φ₀(w; q, z)`. -/
theorem basicHG_cancel {d w q z : ℂ} (hd : ∀ n : ℕ, qPochhammer d q n ≠ 0) :
    basicHG [d, w] [d] q z = ∑' n : ℕ, qPochhammer w q n / qPochhammer q q n * z ^ n := by
  simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  congr 1; funext n; field [hd n]

/-- `(0;q)_∞ = 1`. -/
@[simp] theorem qPochhammerInf_zero (q : ℂ) : qPochhammerInf 0 q = 1 := by
  simp [qPochhammerInf]

/-- **Euler's identity** `e_q(x) = ∑ xⁿ/(q;q)_n = 1/(x;q)_∞` for `|x| < 1` (Duverney (10.28)). -/
@[dlmf 17.5.E4 "exact: upper-zero one-phi-zero in |z|<1"]
theorem tsum_div_qPochhammer {q x : ℂ} (hq : ‖q‖ < 1) (hx : ‖x‖ < 1) :
    ∑' n : ℕ, x ^ n / qPochhammer q q n = 1 / qPochhammerInf x q := by
  have h := q_binomial_theorem (a := 0) hq hx
  simp only [zero_mul, qPochhammerInf_zero, qPochhammer_zero_param] at h
  rw [h]; congr 1; funext n; ring

/-- The product formula `₁φ₀(a; x) ₁φ₀(b; ax) = ₁φ₀(ab; x)` (Duverney, Exercise 10.11). -/
theorem one_phi_zero_mul {a b q x : ℂ} (hq : ‖q‖ < 1) (hx : ‖x‖ < 1) (hax : ‖a * x‖ < 1) :
    (∑' n : ℕ, qPochhammer a q n / qPochhammer q q n * x ^ n) *
        (∑' n : ℕ, qPochhammer b q n / qPochhammer q q n * (a * x) ^ n) =
      ∑' n : ℕ, qPochhammer (a * b) q n / qPochhammer q q n * x ^ n := by
  rw [← q_binomial_theorem hq hx, ← q_binomial_theorem hq hax, ← q_binomial_theorem hq hx]
  have h1 := qPochhammerInf_ne_zero_of_norm_lt_one hax hq
  have h2 := qPochhammerInf_ne_zero_of_norm_lt_one hx hq
  rw [show b * (a * x) = a * b * x by ring]
  field

/-- **Heine's summation** (the `q`-Gauss sum, Duverney (10.53)):
`₂φ₁(a, b; c; q, c/(ab)) = (c/a;q)_∞ (c/b;q)_∞ / ((c;q)_∞ (c/(ab);q)_∞)`. -/
@[dlmf 17.6.E1 "partial: additionally assumes |b|<1 and avoids intermediate c/b q-lattice; full source domain acquired separately"]
theorem q_gauss_summation {a b c q : ℂ} (hq : ‖q‖ < 1) (ha : a ≠ 0) (hb : ‖b‖ < 1)
    (hb0 : b ≠ 0) (hz : ‖c / (a * b)‖ < 1) (hc : ∀ k : ℕ, c * q ^ k ≠ 1)
    (hcb : ∀ k : ℕ, c / b * q ^ k ≠ 1) :
    basicHG [a, b] [c] q (c / (a * b)) =
      qPochhammerInf (c / a) q * qPochhammerInf (c / b) q /
        (qPochhammerInf c q * qPochhammerInf (c / (a * b)) q) := by
  have haz : ∀ k : ℕ, a * (c / (a * b)) * q ^ k ≠ 1 := by
    intro k; rw [show a * (c / (a * b)) = c / b by field]; exact hcb k
  rw [heine_transformation hq hz hb hb0 hc haz, show a * (c / (a * b)) = c / b by field,
    basicHG_cancel (qPochhammer_ne_zero_of_factors hq fun k h => hcb k (sub_eq_zero.mp h).symm),
    ← q_binomial_theorem hq hb, show c / (a * b) * b = c / a by field]
  have h1 := qPochhammerInf_ne_zero_of_norm_lt_one hb hq
  field

/-- **Heine's second transformation** (Duverney (10.50)):
`₂φ₁(a,b;c;q,z) = (c/b;q)_∞ (bz;q)_∞/((c;q)_∞ (z;q)_∞) · ₂φ₁(abz/c, b; bz; q, c/b)`. -/
@[dlmf 17.6.E7 "partial: additional |b|<1 and intermediate az q-lattice exclusion"]
theorem heine_transformation_two {a b c q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (hb : ‖b‖ < 1) (hb0 : b ≠ 0) (hcb : ‖c / b‖ < 1) (hc0 : c ≠ 0)
    (hc : ∀ k : ℕ, c * q ^ k ≠ 1) (haz : ∀ k : ℕ, a * z * q ^ k ≠ 1)
    (hbz : ∀ k : ℕ, z * b * q ^ k ≠ 1) :
    basicHG [a, b] [c] q z =
      qPochhammerInf (c / b) q * qPochhammerInf (b * z) q /
          (qPochhammerInf c q * qPochhammerInf z q) *
        basicHG [a * b * z / c, b] [b * z] q (c / b) := by
  rw [heine_transformation hq hz hb hb0 hc haz, basicHG_swap,
    heine_transformation hq hb hcb (div_ne_zero hc0 hb0) haz hbz]
  have h1 := qPochhammerInf_ne_zero_of_norm_lt_one hb hq
  have h2 := qPochhammerInf_ne_zero hq fun k h => haz k (sub_eq_zero.mp h).symm
  rw [show a * z / (c / b) = a * b * z / c by field, show z * b = b * z by ring]
  field

/-- **Heine's third transformation** (the `q`-Euler transformation, Duverney (10.51)):
`₂φ₁(a,b;c;q,z) = (abz/c;q)_∞/(z;q)_∞ · ₂φ₁(c/a, c/b; c; q, abz/c)`. -/
@[dlmf 17.6.E8 "partial: additional intermediate |b|<1, |c/b|<1, nonzero z and az,bz exclusions"]
theorem heine_transformation_three {a b c q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (hb : ‖b‖ < 1) (hb0 : b ≠ 0) (ha0 : a ≠ 0) (hz0 : z ≠ 0) (hcb : ‖c / b‖ < 1) (hc0 : c ≠ 0)
    (habz : ‖a * b * z / c‖ < 1) (hc : ∀ k : ℕ, c * q ^ k ≠ 1)
    (haz : ∀ k : ℕ, a * z * q ^ k ≠ 1) (hbz : ∀ k : ℕ, z * b * q ^ k ≠ 1) :
    basicHG [a, b] [c] q z =
      qPochhammerInf (a * b * z / c) q / qPochhammerInf z q *
        basicHG [c / a, c / b] [c] q (a * b * z / c) := by
  have hbz' : ∀ k : ℕ, b * z * q ^ k ≠ 1 := fun k => by rw [mul_comm b z]; exact hbz k
  have hcc : ∀ k : ℕ, b * (c / b) * q ^ k ≠ 1 := fun k => by
    rw [show b * (c / b) = c by field]; exact hc k
  rw [heine_transformation_two hq hz hb hb0 hcb hc0 hc haz hbz, basicHG_swap,
    heine_transformation hq hcb habz (by simp [ha0, hb0, hz0, hc0]) hbz' hcc]
  have h1 := qPochhammerInf_ne_zero hq fun k h => hbz' k (sub_eq_zero.mp h).symm
  have h2 := qPochhammerInf_ne_zero_of_norm_lt_one hcb hq
  have h3 := qPochhammerInf_ne_zero hq fun k h => hc k (sub_eq_zero.mp h).symm
  rw [show b * z / (a * b * z / c) = c / a by field, show b * (c / b) = c by field]
  field

/-- `(q^{-n};q)_k = 0` for `k > n`. -/
theorem qPochhammer_recip_pow_eq_zero {q : ℂ} (hq0 : q ≠ 0) {n k : ℕ} (hk : n < k) :
    qPochhammer (q ^ n)⁻¹ q k = 0 := by
  rw [qPochhammer_eq_prod]
  exact prod_eq_zero (mem_range.mpr hk) (by field)

/-- **`q`-Chu–Vandermonde** (Duverney (10.54)): for `|b| < 1`, `|c qⁿ/b| < 1` and `c ≠ q^{-m}`,
`∑_{k ≤ n} (q^{-n};q)_k (b;q)_k / ((c;q)_k (q;q)_k) (c qⁿ/b)^k = (c/b;q)_n / (c;q)_n`. -/
@[dlmf 17.6.E2 "partial: additionally bounds the other upper parameter by1 and excludes later lower poles; finite full-domain statement acquired separately"]
theorem q_chu_vandermonde {b c q : ℂ} (n : ℕ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hb : ‖b‖ < 1)
    (hb0 : b ≠ 0) (hz : ‖c * q ^ n / b‖ < 1) (hc : ∀ k : ℕ, c * q ^ k ≠ 1)
    (hcb : ∀ k : ℕ, c / b * q ^ k ≠ 1) :
    ∑ k ∈ range (n + 1), qPochhammer (q ^ n)⁻¹ q k * qPochhammer b q k /
        (qPochhammer c q k * qPochhammer q q k) * (c * q ^ n / b) ^ k =
      qPochhammer (c / b) q n / qPochhammer c q n := by
  have hqn : (q ^ n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero n hq0)
  have hz' : ‖c / ((q ^ n)⁻¹ * b)‖ < 1 := by
    rwa [show c / ((q ^ n)⁻¹ * b) = c * q ^ n / b by field]
  have h := q_gauss_summation hq hqn hb hb0 hz' hc hcb
  have hfin : basicHG [(q ^ n)⁻¹, b] [c] q (c / ((q ^ n)⁻¹ * b)) =
      ∑ k ∈ range (n + 1), qPochhammer (q ^ n)⁻¹ q k * qPochhammer b q k /
        (qPochhammer c q k * qPochhammer q q k) * (c * q ^ n / b) ^ k := by
    simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [show c / ((q ^ n)⁻¹ * b) = c * q ^ n / b by field]
    refine tsum_eq_sum fun k hk => ?_
    rw [qPochhammer_recip_pow_eq_zero hq0 (by simpa using hk)]
    simp
  rw [← hfin, h, show c / (q ^ n)⁻¹ = c * q ^ n by field,
    show c / ((q ^ n)⁻¹ * b) = c / b * q ^ n by field,
    qPochhammerInf_mul_qPochhammer (a := c) hq n,
    qPochhammerInf_mul_qPochhammer (a := c / b) hq n]
  have hcf : ∀ k : ℕ, 1 - c * q ^ k ≠ 0 := fun k h => hc k (sub_eq_zero.mp h).symm
  have hcbf : ∀ k : ℕ, 1 - c / b * q ^ k ≠ 0 := fun k h => hcb k (sub_eq_zero.mp h).symm
  have h1 := qPochhammerInf_shift_ne_zero hq hcf n
  have h2 := qPochhammerInf_shift_ne_zero hq hcbf n
  have h3 := qPochhammer_ne_zero_of_factors hq hcf n
  field

end DLMF.QSeries

end
