/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.LargeA
public import DLMF.OrthogonalPolynomials.Differential
/-!
# Limits between families and Mehler–Heine formulas

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.

The Jacobi Mehler–Heine proof uses Mathlib’s dominated convergence theorem for
series (Tannery), descending-factorial bounds and continuity of the sinc function.
The terminating range supplies a geometric majorant for the two varying numerator
parameters; the existing local Gamma-ratio limit supplies the normalization.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology
open DLMF.Hypergeometric
open DLMF.Confluent
open DLMF.Bessel

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- As `b → ∞`, the terminating Jacobi series `₂F₁(-n, n+α+b+1; α+1; u)`, divided by `bⁿ`,
tends to its top-degree term. -/
theorem tendsto_jacobiSeries_div_pow {α : ℂ} (n : ℕ) (u : ℂ) :
    Tendsto (fun b : ℝ => (∑ k ∈ Finset.range (n + 1),
      gaussHGCoeff (-(n : ℂ)) (n + α + b + 1) (α + 1) k * u ^ k) / (b : ℂ) ^ n) atTop
      (𝓝 (poch (-(n : ℂ)) n / (poch (α + 1) n * n !) * u ^ n)) := by
  have hinv : Tendsto (fun b : ℝ => (b : ℂ)⁻¹) atTop (𝓝 0) := by
    have := (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    rw [ofReal_zero] at this
    exact this.congr fun b => by simp
  have hlow : Tendsto (fun b : ℝ => ∑ k ∈ Finset.range n,
      poch (-(n : ℂ)) k / (poch (α + 1) k * k !) * u ^ k *
        (poch ((n : ℂ) + α + 1 + b) k / (b : ℂ) ^ k) * ((b : ℂ)⁻¹) ^ (n - k)) atTop (𝓝 0) := by
    rw [show (0 : ℂ) = ∑ k ∈ Finset.range n, poch (-(n : ℂ)) k / (poch (α + 1) k * k !) * u ^ k *
      1 * 0 ^ (n - k) by
        refine (Finset.sum_eq_zero fun k hk => ?_).symm
        rw [zero_pow (by simp at hk; omega), mul_zero]]
    apply tendsto_finsetSum
    intro k _
    exact ((tendsto_poch_add_div_pow _ k).const_mul _).mul (hinv.pow _)
  have htop := (tendsto_poch_add_div_pow ((n : ℂ) + α + 1) n).const_mul
    (poch (-(n : ℂ)) n / (poch (α + 1) n * n !) * u ^ n)
  have := hlow.add htop
  rw [zero_add, mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  rw [Finset.sum_range_succ, add_div, Finset.sum_div]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := by simp at hk; omega
    unfold gaussHGCoeff
    rw [show (n : ℂ) + α + b + 1 = n + α + 1 + b by ring, inv_pow,
      show (b : ℂ) ^ n = b ^ k * b ^ (n - k) by rw [← pow_add]; congr 1; omega]
    field_simp
  · unfold gaussHGCoeff
    rw [show (n : ℂ) + α + b + 1 = n + α + 1 + b by ring]
    field_simp

/-- The map `(fun a : ℝ => jacobiPolyP a β n x / jacobiPolyP a β n 1)` tends to `(𝓝 (((1 + x) / 2)
^ n))` along `atTop`. -/
@[dlmf 18.6.E2]
theorem jacobi_limit_alpha {β : ℂ} (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => jacobiPolyP a β n x / jacobiPolyP a β n 1) atTop
        (𝓝 (((1 + x) / 2) ^ n)) := by
  have hx : ((1 + x) / 2) ^ n = (1 - (1 - x) / 2) ^ n := by ring_nf
  rw [hx, ← sum_poch_neg_nat_div_factorial_mul_pow]
  have hlim : Tendsto (fun a : ℝ => ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k / k ! * ((1 - x) / 2) ^ k *
        ((poch ((n : ℂ) + β + 1 + a) k / (a : ℂ) ^ k) * (poch (1 + (a : ℂ)) k / (a : ℂ) ^ k)⁻¹))
      atTop (𝓝 (∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k / k ! * ((1 - x) / 2) ^ k *
        (1 * 1⁻¹))) := by
    apply tendsto_finsetSum
    intro k _
    exact ((tendsto_poch_add_div_pow _ k).mul
      ((tendsto_poch_add_div_pow 1 k).inv₀ one_ne_zero)).const_mul _
  simp only [inv_one, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hc : ∀ k : ℕ, (a : ℂ) + 1 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hp : poch ((a : ℂ) + 1) n / n ! ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hc n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have h0 : ₂F₁ (-(n : ℂ)) (n + a + β + 1) (a + 1) (0 : ℂ) = 1 := by
    rw [ordinaryHypergeometric_eq_sum_neg_nat, Finset.sum_range_succ']
    simp [gaussHGCoeff, poch_zero]
  unfold jacobiPolyP
  rw [show ((1 : ℂ) - 1) / 2 = 0 by ring, h0, mul_one, mul_div_cancel_left₀ _ hp,
    ordinaryHypergeometric_eq_sum_neg_nat]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hpk : poch ((a : ℂ) + 1) k ≠ 0 := poch_ne_zero_of_not_neg_nat hc k
  unfold gaussHGCoeff
  rw [add_comm (1 : ℂ) (a : ℂ), show (n : ℂ) + a + β + 1 = n + β + 1 + a by ring]
  field_simp

/-- The map `(fun b : ℝ => jacobiPolyP α b n x / jacobiPolyP α b n (-1))` tends to `(𝓝 (((1 - x) /
2) ^ n))` along `atTop`. -/
@[dlmf 18.6.E3]
theorem jacobi_limit_beta {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    Tendsto (fun b : ℝ => jacobiPolyP α b n x / jacobiPolyP α b n (-1)) atTop
        (𝓝 (((1 - x) / 2) ^ n)) := by
  have hc : ∀ k : ℕ, α + 1 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hG : poch (-(n : ℂ)) n / (poch (α + 1) n * n !) ≠ 0 := by
    refine div_ne_zero ?_ (mul_ne_zero (poch_ne_zero_of_not_neg_nat hc n)
      (Nat.cast_ne_zero.mpr n.factorial_ne_zero))
    rw [poch_neg_coe_nat, Nat.descFactorial_self]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have hp : poch (α + 1) n / n ! ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hc n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have h := (tendsto_jacobiSeries_div_pow (α := α) n ((1 - x) / 2)).div
    (tendsto_jacobiSeries_div_pow (α := α) n 1) (by simpa using hG)
  rw [one_pow, mul_one, mul_div_cancel_left₀ _ hG] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb' : (b : ℂ) ^ n ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr hb.ne')
  unfold jacobiPolyP
  rw [Pi.div_apply, show (1 - (-1 : ℂ)) / 2 = 1 by norm_num, ordinaryHypergeometric_eq_sum_neg_nat,
    ordinaryHypergeometric_eq_sum_neg_nat, mul_div_mul_left _ _ hp, div_div_div_cancel_right₀ hb']

/-- The map `(fun a : ℝ => ultrasphPoly a n x / ultrasphPoly a n 1)` tends to `(𝓝 (x ^ n))` along
`atTop`. -/
@[dlmf 18.6.E4]
theorem ultrasphPoly_limit_monomial (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => ultrasphPoly a n x / ultrasphPoly a n 1) atTop (𝓝 (x ^ n)) := by
  have hx : x ^ n = (1 - (1 - x)) ^ n := by ring
  rw [hx, ← sum_poch_neg_nat_div_factorial_mul_pow]
  have h2 : Tendsto (fun a : ℝ => 2 * a) atTop atTop := tendsto_id.const_mul_atTop two_pos
  have hlim : Tendsto (fun a : ℝ => ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k / k ! * (1 - x) ^ k *
        ((poch ((n : ℂ) + ((2 * a : ℝ) : ℂ)) k / ((2 * a : ℝ) : ℂ) ^ k) *
          (poch (1 / 2 + (a : ℂ)) k / (a : ℂ) ^ k)⁻¹)) atTop
      (𝓝 (∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k / k ! * (1 - x) ^ k * (1 * 1⁻¹))) := by
    apply tendsto_finsetSum
    intro k _
    exact (((tendsto_poch_add_div_pow n k).comp h2).mul
      ((tendsto_poch_add_div_pow (1 / 2) k).inv₀ one_ne_zero)).const_mul _
  simp only [inv_one, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have h2a : ∀ k : ℕ, 2 * (a : ℂ) ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hc : ∀ k : ℕ, (a : ℂ) + 1 / 2 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hp : poch (2 * (a : ℂ)) n / n ! ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat h2a n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  unfold ultrasphPoly
  have h0 : ₂F₁ (-(n : ℂ)) (n + 2 * a) (a + 1 / 2) (0 : ℂ) = 1 := by
    rw [ordinaryHypergeometric_eq_sum_neg_nat, Finset.sum_range_succ']
    simp [gaussHGCoeff, poch_zero]
  rw [show ((1 : ℂ) - 1) / 2 = 0 by ring, h0, mul_one, mul_div_cancel_left₀ _ hp,
    ordinaryHypergeometric_eq_sum_neg_nat]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hpk : poch ((a : ℂ) + 1 / 2) k ≠ 0 := poch_ne_zero_of_not_neg_nat hc k
  unfold gaussHGCoeff
  push_cast
  rw [add_comm (1 / 2 : ℂ), div_pow]
  field_simp
  ring

/-- The map `(fun a : ℝ => laguerrePolyL a n (a * x) / laguerrePolyL a n 0)` tends to `(𝓝 ((1 - x)
^ n))` along `atTop`. -/
@[dlmf 18.6.E5]
theorem laguerrePolyL_limit_monomial (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => laguerrePolyL a n (a * x) / laguerrePolyL a n 0) atTop
        (𝓝 ((1 - x) ^ n)) := by
  rw [← sum_poch_neg_nat_div_factorial_mul_pow]
  have hlim : Tendsto (fun a : ℝ => ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k / k ! * x ^ k * (poch (1 + a) k / (a : ℂ) ^ k)⁻¹) atTop
      (𝓝 (∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k / k ! * x ^ k * 1⁻¹)) := by
    apply tendsto_finsetSum
    intro k _
    exact ((tendsto_poch_add_div_pow 1 k).inv₀ one_ne_zero).const_mul _
  simp only [inv_one, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hα : ∀ k : ℕ, (a : ℂ) + 1 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hp : poch ((a : ℂ) + 1) n / n ! ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hα n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  unfold laguerrePolyL
  rw [kummerM_zero, mul_one, mul_div_cancel_left₀ _ hp, kummerM_eq_sum_neg_nat]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hpk : poch ((a : ℂ) + 1) k ≠ 0 := poch_ne_zero_of_not_neg_nat hα k
  rw [add_comm (1 : ℂ)]
  field_simp
  ring

/-- The map `(fun b : ℝ => jacobiPolyP α b n (1 - 2 * x / b))` tends to `(𝓝 (laguerrePolyL α n
x))` along `atTop`. -/
@[dlmf 18.7.E21]
theorem jacobi_limit_laguerrePolyL {α : ℂ} (n : ℕ) (x : ℂ) :
    Tendsto (fun b : ℝ => jacobiPolyP α b n (1 - 2 * x / b)) atTop (𝓝 (laguerrePolyL α n x)) := by
  unfold laguerrePolyL
  rw [kummerM_eq_sum_neg_nat]
  unfold jacobiPolyP
  apply Tendsto.const_mul
  have hlim : Tendsto (fun b : ℝ => ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k / (poch (α + 1) k * k !) * x ^ k *
        (poch ((n : ℂ) + α + 1 + b) k / (b : ℂ) ^ k))
      atTop (𝓝 (∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k / (poch (α + 1) k * k !) * x ^ k *
        1)) := by
    apply tendsto_finsetSum
    intro k _
    exact (tendsto_poch_add_div_pow _ k).const_mul _
  simp only [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold gaussHGCoeff
  rw [show (1 - (1 - 2 * x / b)) / 2 = x / b by ring,
    show (n : ℂ) + α + b + 1 = n + α + 1 + b by ring, div_pow]
  field_simp

/-- The map `(fun a : ℝ => jacobiPolyP a β n (2 * x / a - 1))` tends to `(𝓝 ((-1 : ℂ) ^ n *
laguerrePolyL β n x))` along `atTop`. -/
@[dlmf 18.7.E22]
theorem jacobi_limit_laguerrePolyL_reflected {β : ℂ} (hβ : -1 < β.re) (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => jacobiPolyP a β n (2 * x / a - 1)) atTop
        (𝓝 ((-1 : ℂ) ^ n * laguerrePolyL β n x)) := by
  refine ((jacobi_limit_laguerrePolyL (α := β) n x).const_mul ((-1 : ℂ) ^ n)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  rw [show 2 * x / (a : ℂ) - 1 = -(1 - 2 * x / a) by ring,
    jacobi_reflection (by simp; linarith) hβ]

/-- The map `(fun a : ℝ => (Real.sqrt a : ℂ)⁻¹ ^ n * jacobiPolyP a a n (x / Real.sqrt a))` tends
to `(𝓝 (aeval x (hermitePolyH n) / ((2 : ℂ) ^ n * n.factorial)))` along `atTop`. -/
@[dlmf 18.7.E23]
theorem jacobi_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => (Real.sqrt a : ℂ)⁻¹ ^ n * jacobiPolyP a a n (x / Real.sqrt a)) atTop
      (𝓝 (aeval x (hermitePolyH n) / ((2 : ℂ) ^ n * n.factorial))) := by
  have hc (c : ℂ) (d : ℂ) : Tendsto (fun a : ℝ => d + c / (a : ℂ)) atTop (𝓝 d) := by
    simpa using (tendsto_const_div_ofReal_atTop c).const_add d
  refine tendsto_of_three_term (f := fun n a => (Real.sqrt a : ℂ)⁻¹ ^ n *
      jacobiPolyP a a n (x / Real.sqrt a))
    (g := fun n => aeval x (hermitePolyH n) / ((2 : ℂ) ^ n * (n ! : ℂ)))
    (A := fun n a => x * ((2 + (2 * n + 3) / (a : ℂ)) * (1 + (n + 2) / (a : ℂ))) /
      ((n + 2) * (2 + (n + 2) / (a : ℂ))))
    (B := fun n a => -((1 + (n + 1) / (a : ℂ)) * (1 + (n + 2) / (a : ℂ))) /
      ((n + 2) * (2 + (n + 2) / (a : ℂ))))
    (A' := fun n => x * (2 * 1) / ((n + 2) * 2)) (B' := fun n => -(1 * 1) / ((n + 2) * 2))
    ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp
  · have h := (hc 1 1).const_mul x
    rw [mul_one] at h
    refine (h.congr' ?_).trans (by simp [map_ofNat])
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hs : (Real.sqrt a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne'
    have hs2 : (a : ℂ) = (Real.sqrt a : ℂ) ^ 2 := by
      rw [← ofReal_pow, Real.sq_sqrt ha.le]
    rw [jacobiPolyP_one_eq (by simp; linarith), hs2]
    field_simp
    ring
  · intro n
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    exact (((hc _ 2).mul (hc _ 1)).const_mul x).div ((hc _ 2).const_mul _)
      (mul_ne_zero hn two_ne_zero)
  · intro n
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    exact ((hc _ 1).mul (hc _ 1)).neg.div ((hc _ 2).const_mul _) (mul_ne_zero hn two_ne_zero)
  · intro n
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hs : (Real.sqrt a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne'
    have hs2 : (a : ℂ) = (Real.sqrt a : ℂ) ^ 2 := by
      rw [← ofReal_pow, Real.sq_sqrt ha.le]
    have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have hd : 2 * (a : ℂ) + (n + 2) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hd1 : (a : ℂ) + (n + 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hr := jacobi_recurrence (α := a) (β := a) (by simp; linarith) n (x / Real.sqrt a)
    simp only [inv_pow]
    field_simp
    field_simp at hr
    apply mul_left_cancel₀ hd1
    rw [hs2] at hr ⊢
    linear_combination ((Real.sqrt a : ℂ) ^ 2 * (Real.sqrt a : ℂ) ^ (2 * n) / 4) * hr
  · intro n
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn2 : (n : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 + 1 ≠ 0)
    simp only [hermitePolyH_recurrence, map_sub, map_mul, aeval_X, aeval_C, map_ofNat,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The map `(fun a : ℝ => (Real.sqrt a : ℂ)⁻¹ ^ n * ultrasphPoly a n (x / Real.sqrt a))` tends to
`(𝓝 (aeval x (hermitePolyH n) / (n.factorial : ℂ)))` along `atTop`. -/
@[dlmf 18.7.E24]
theorem ultrasphPoly_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => (Real.sqrt a : ℂ)⁻¹ ^ n * ultrasphPoly a n (x / Real.sqrt a)) atTop
      (𝓝 (aeval x (hermitePolyH n) / (n.factorial : ℂ))) := by
  refine tendsto_of_three_term (f := fun n a => (Real.sqrt a : ℂ)⁻¹ ^ n *
      ultrasphPoly a n (x / Real.sqrt a)) (g := fun n => aeval x (hermitePolyH n) / (n ! : ℂ))
    (A := fun n a => 2 * x / (n + 2) * (1 + (n + 1) / (a : ℂ)))
    (B := fun n a => -(1 / (n + 2)) * (2 + n / (a : ℂ)))
    (A' := fun n => 2 * x / (n + 2)) (B' := fun n => -(1 / (n + 2)) * 2) ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hs : (Real.sqrt a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne'
    have hs2 : (Real.sqrt a : ℂ) ^ 2 = a := by
      rw [← ofReal_pow, Real.sq_sqrt ha.le]
    rw [ultrasphPoly_one_eq (by simp; linarith)]
    simp only [hermitePolyH_one, map_mul, aeval_X, Nat.factorial_one, Nat.cast_one, div_one,
      pow_one]
    rw [← hs2]
    field_simp
    rw [map_ofNat]
    ring
  · intro n
    simpa using ((tendsto_const_div_ofReal_atTop ((n : ℂ) + 1)).const_add 1).const_mul
      (2 * x / (n + 2))
  · intro n
    simpa using ((tendsto_const_div_ofReal_atTop (n : ℂ)).const_add 2).const_mul
      (-(1 / ((n : ℂ) + 2)))
  · intro n
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hs : (Real.sqrt a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne'
    have hs2 : (a : ℂ) = (Real.sqrt a : ℂ) ^ 2 := by
      rw [← ofReal_pow, Real.sq_sqrt ha.le]
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have hr := ultrasphPoly_recurrence (lam := a) (by simp; linarith) n (x / Real.sqrt a)
    rw [hs2] at hr ⊢
    simp only [inv_pow]
    field_simp
    field_simp at hr
    linear_combination (Real.sqrt a : ℂ) ^ (n + 1) * (Real.sqrt a : ℂ) ^ (n + 1) * hr
  · intro n
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn2 : (n : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 + 1 ≠ 0)
    simp only [hermitePolyH_recurrence, map_sub, map_mul, aeval_X, aeval_C, map_ofNat,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The map `(fun a : ℂ => (n + a) / a * ultrasphPoly a n x)` tends to `(𝓝 (if n = 0 then 1 else 2
* (Chebyshev.T ℂ n).eval x))` along `(𝓝[≠] 0)`. -/
@[dlmf 18.7.E25]
theorem ultrasphPoly_limit_chebyshev (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℂ => (n + a) / a * ultrasphPoly a n x) (𝓝[≠] 0)
      (𝓝 (if n = 0 then 1 else 2 * (Chebyshev.T ℂ n).eval x)) := by
  -- a punctured neighbourhood on which the recurrence is valid
  have hev : ∀ᶠ a : ℂ in 𝓝[≠] 0, a ≠ 0 ∧ ‖a‖ < 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))]
      with a h0 h1
    exact ⟨h0, by simpa using h1⟩
  have hre : ∀ a : ℂ, ‖a‖ < 1 / 2 → -1 / 2 < a.re := by
    intro a ha
    have := neg_abs_le a.re
    have := abs_re_le_norm a
    linarith
  have hk : ∀ a : ℂ, ‖a‖ < 1 / 2 → ∀ k : ℕ, 0 < k → (k : ℂ) + a ≠ 0 := by
    intro a ha k hk h
    have h' : a = -k := by linear_combination h
    rw [h', norm_neg, Complex.norm_natCast] at ha
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine tendsto_of_three_term (f := fun n a => (n + a) / a * ultrasphPoly a n x)
    (g := fun n => if n = 0 then 1 else 2 * (Chebyshev.T ℂ n).eval x)
    (A := fun n a => (n + 2 + a) / (n + 2) * (2 * x))
    (B := fun n a => -((n + 2 + a) / (n + 2) * ((n + 2 * a) / (n + a))))
    (A' := fun n => 2 * x) (B' := fun n => if n = 0 then -2 else -1) ?_ ?_ ?_ ?_ ?_ ?_ n
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    simp [div_self ha]
  · have h : Tendsto (fun a : ℂ => 2 * (1 + a) * x) (𝓝[≠] 0) (𝓝 (2 * (1 + 0) * x)) :=
      ((continuous_const.mul (continuous_const.add continuous_id)).mul
        continuous_const).tendsto 0 |>.mono_left nhdsWithin_le_nhds
    refine (h.congr' ?_).trans (by simp)
    filter_upwards [hev] with a ⟨ha0, ha⟩
    rw [ultrasphPoly_one_eq (hre a ha)]
    field_simp
    push_cast
    ring
  · intro n
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have h : Tendsto (fun a : ℂ => (n + 2 + a) / (n + 2) * (2 * x)) (𝓝 0)
        (𝓝 ((n + 2 + 0) / (n + 2) * (2 * x))) :=
      (Continuous.tendsto (by fun_prop) 0)
    rw [add_zero, div_self hn, one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  · intro n
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have h : Tendsto (fun a : ℂ => -((0 + 2 + a) / (0 + 2) * 2)) (𝓝 0)
          (𝓝 (-((0 + 2 + 0) / (0 + 2) * 2))) := Continuous.tendsto (by fun_prop) 0
      refine ((h.mono_left nhdsWithin_le_nhds).congr' ?_).trans (by norm_num)
      filter_upwards [self_mem_nhdsWithin] with a ha
      have ha' : a ≠ 0 := ha
      push_cast
      rw [show ((0 : ℂ) + 2 * a) / (0 + a) = 2 by rw [zero_add, zero_add]; field_simp]
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      have h : Tendsto (fun a : ℂ => -((n + 2 + a) / (n + 2) * ((n + 2 * a) / (n + a)))) (𝓝 0)
          (𝓝 (-((n + 2 + 0) / (n + 2) * ((n + 2 * 0) / (n + 0))))) := by
        apply ContinuousAt.tendsto
        apply ContinuousAt.neg
        apply ContinuousAt.mul (by fun_prop)
        exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hn0)
      simp only [add_zero, mul_zero, div_self hn, div_self hn0, one_mul] at h
      simpa [hpos.ne'] using h.mono_left nhdsWithin_le_nhds
  · intro n
    filter_upwards [hev] with a ⟨ha0, ha⟩
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have h1 := hk a ha (n + 1) (by omega)
    have h2 := hk a ha (n + 2) (by omega)
    have hr := ultrasphPoly_recurrence (hre a ha) n x
    push_cast at h1 h2
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [CharP.cast_eq_zero, zero_add] at hr h1 h2 ⊢
      field_simp
      linear_combination (1 + a / 2) * hr
    · have h0 := hk a ha n hpos
      field_simp
      push_cast
      linear_combination ((n : ℂ) + 2 + a) * hr
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [Chebyshev.T_two, Chebyshev.T_one]
      ring
    · have := Chebyshev.T_add_two ℂ (n : ℤ)
      simp only [hpos.ne', ↓reduceIte, show n + 2 ≠ 0 by omega, show n + 1 ≠ 0 by omega]
      push_cast
      rw [this]
      simp
      ring

/-- The map `(fun a : ℝ => (Real.sqrt (2 / a) : ℂ) ^ n * laguerrePolyL a n ((Real.sqrt (2 * a) :
ℂ) * x + a))` tends to `(𝓝 ((-1 : ℂ) ^ n / n.factorial * aeval x (hermitePolyH n)))` along
`atTop`. -/
@[dlmf 18.7.E26]
theorem laguerrePolyL_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => (Real.sqrt (2 / a) : ℂ) ^ n
        * laguerrePolyL a n ((Real.sqrt (2 * a) : ℂ) * x + a)) atTop
      (𝓝 ((-1 : ℂ) ^ n / n.factorial * aeval x (hermitePolyH n))) := by
  have hr0 : Tendsto (fun a : ℝ => (Real.sqrt (2 / a) : ℂ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun a : ℝ => 2 / a) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    have h3 := (continuous_ofReal.tendsto 0).comp h2
    rw [ofReal_zero] at h3
    exact h3
  -- `√(2/a) √(2a) = 2` and `√(2/a)^2 = 2/a` for `a > 0`
  have hsq : ∀ a : ℝ, 0 < a → (Real.sqrt (2 / a) : ℂ) * Real.sqrt (2 * a) = 2 ∧
      (Real.sqrt (2 / a) : ℂ) ^ 2 * a = 2 := by
    intro a ha
    constructor
    · rw [← ofReal_mul, ← Real.sqrt_mul (by positivity), show 2 / a * (2 * a) = 2 ^ 2 by
        field_simp, Real.sqrt_sq (by norm_num)]
      all_goals norm_num
    · rw [← ofReal_pow, Real.sq_sqrt (by positivity), ← ofReal_mul, div_mul_cancel₀ _ ha.ne']
      all_goals norm_num
  have hlag1 : ∀ α y : ℂ, α + 1 ≠ 0 → laguerrePolyL α 1 y = α + 1 - y := by
    intro α y hα
    unfold laguerrePolyL
    rw [kummerM_eq_sum_neg_nat]
    simp [Finset.sum_range_succ, poch_one, poch_zero]
    field_simp
    ring
  refine tendsto_of_three_term (f := fun n a => (Real.sqrt (2 / a) : ℂ) ^ n *
      laguerrePolyL a n ((Real.sqrt (2 * a) : ℂ) * x + a))
    (g := fun n => (-1 : ℂ) ^ n / (n ! : ℂ) * aeval x (hermitePolyH n))
    (A := fun n a => ((2 * n + 3) * (Real.sqrt (2 / a) : ℂ) - 2 * x) / (n + 2))
    (B := fun n a => -(2 + 2 * (n + 1) / (a : ℂ)) / (n + 2))
    (A' := fun n => -(2 * x) / (n + 2)) (B' := fun n => -2 / (n + 2)) ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp
  · have h : Tendsto (fun a : ℝ => (Real.sqrt (2 / a) : ℂ) - 2 * x) atTop (𝓝 (0 - 2 * x)) :=
      hr0.sub tendsto_const_nhds
    refine (h.congr' ?_).trans (by simp [map_ofNat])
    filter_upwards [eventually_gt_atTop 0] with a ha
    have ha1 : (a : ℂ) + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [hlag1 _ _ ha1]
    simp only [pow_one]
    linear_combination x * (hsq a ha).1
  · intro n
    have h := ((hr0.const_mul (2 * (n : ℂ) + 3)).sub (tendsto_const_nhds (x := 2 * x))).div_const
      ((n : ℂ) + 2)
    simpa using h
  · intro n
    have h := ((tendsto_const_div_ofReal_atTop (2 * ((n : ℂ) + 1))).const_add 2).neg.div_const
      ((n : ℂ) + 2)
    simpa [mul_div_assoc] using h
  · intro n
    filter_upwards [eventually_gt_atTop 0] with a ha
    have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have hl := laguerrePolyL_recurrence (α := a) (by simp; linarith) n
      ((Real.sqrt (2 * a) : ℂ) * x + a)
    obtain ⟨h1, h2⟩ := hsq a ha
    set r : ℂ := (Real.sqrt (2 / a) : ℂ)
    set s : ℂ := (Real.sqrt (2 * a) : ℂ)
    field_simp
    linear_combination r ^ (n + 2) * a * hl -
      a * r ^ (n + 1) * x * laguerrePolyL a (n + 1) (s * x + a) * h1 -
      (n + a + 1) * r ^ n * laguerrePolyL a n (s * x + a) * h2
  · intro n
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn2 : (n : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 + 1 ≠ 0)
    simp only [hermitePolyH_recurrence, map_sub, map_mul, aeval_X, aeval_C, map_ofNat,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The normalized terminating numerator Pochhammer symbol has norm at most one. -/
private lemma norm_poch_neg_nat_div_pow_le_one {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ‖poch (-(n : ℂ)) k / (n : ℂ) ^ k‖ ≤ 1 := by
  simp only [poch_neg_coe_nat, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_natCast]
  apply (div_le_one (pow_pos (by exact_mod_cast hn) k)).mpr
  exact_mod_cast Nat.descFactorial_le_pow n k

/-- A bound for the other Jacobi numerator, restricted to its terminating range. -/
private lemma norm_poch_nat_add_div_pow_le (c : ℂ) {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k ≤ n) :
    ‖poch ((n : ℂ) + c) k / (n : ℂ) ^ k‖ ≤ (2 + ‖c‖) ^ k := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have hkn : k ≤ n := by omega
    have hb : ‖((n : ℂ) + c + k) / n‖ ≤ 2 + ‖c‖ := by
      rw [norm_div, Complex.norm_natCast, div_le_iff₀ hn0]
      have ht := norm_add_le ((n : ℂ) + c) (k : ℂ)
      have ht' := norm_add_le (n : ℂ) c
      simp only [Complex.norm_natCast] at ht ht'
      have hkR : (k : ℝ) ≤ n := by exact_mod_cast hkn
      nlinarith [norm_nonneg c]
    have he : poch ((n : ℂ) + c) (k + 1) / (n : ℂ) ^ (k + 1) =
        (poch ((n : ℂ) + c) k / (n : ℂ) ^ k) * (((n : ℂ) + c + k) / n) := by
      rw [poch_succ, pow_succ]
      ring
    rw [he, norm_mul, pow_succ]
    exact mul_le_mul (ih hkn) hb (norm_nonneg _) (by positivity)

/-- A terminating Gauss series with both numerator parameters growing converges to `₀F̃₁`. -/
private lemma tendsto_jacobi_scaled_series (c b : ℂ) {wseq : ℕ → ℂ} {w : ℂ}
    (hw : Tendsto wseq atTop (𝓝 w)) :
    Tendsto (fun n : ℕ => ∑' k : ℕ,
      (poch (-(n : ℂ)) k / (n : ℂ) ^ k) *
      (poch ((n : ℂ) + c) k / (n : ℂ) ^ k) *
      wseq n ^ k * regularizedHGFunCoeff ∅ {b} k) atTop
      (𝓝 (regularizedHGFun ∅ {b} (-w))) := by
  let D : ℝ := 2 + ‖c‖
  let R : ℝ := ‖w‖ + 1
  have hsum : Summable (fun k : ℕ => (D * R) ^ k * ‖regularizedHGFunCoeff ∅ {b} k‖) := by
    have hs := summable_norm_iff.mpr
      ((hasFPowerSeriesOnBall_regularized0F1 b).hasSum_mul_pow
        (by simp : ((D * R : ℝ) : ℂ) ∈ Metric.eball (0 : ℂ) ⊤)).summable
    refine hs.congr fun k => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by dsimp [D, R]; positivity)]
    ring
  have hpoint (k : ℕ) : Tendsto (fun n : ℕ =>
      (poch (-(n : ℂ)) k / (n : ℂ) ^ k) *
      (poch ((n : ℂ) + c) k / (n : ℂ) ^ k) *
      wseq n ^ k * regularizedHGFunCoeff ∅ {b} k) atTop
      (𝓝 ((-1 : ℂ) ^ k * w ^ k * regularizedHGFunCoeff ∅ {b} k)) := by
    have hn := (tendsto_poch_sub_div_pow 0 k).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have hp := (tendsto_poch_add_div_pow c k).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simp only [zero_sub, ofReal_neg] at hn hp
    have h := ((hn.mul hp).mul (hw.pow k)).mul_const (regularizedHGFunCoeff ∅ {b} k)
    simpa only [Function.comp_apply, ofReal_natCast, mul_one, add_comm c] using h
  have hbnd : ∀ᶠ (n : ℕ) in atTop, ∀ k : ℕ,
      ‖(poch (-(n : ℂ)) k / (n : ℂ) ^ k) *
        (poch ((n : ℂ) + c) k / (n : ℂ) ^ k) *
        wseq n ^ k * regularizedHGFunCoeff ∅ {b} k‖ ≤
        (D * R) ^ k * ‖regularizedHGFunCoeff ∅ {b} k‖ := by
    have hwB : ∀ᶠ n in atTop, ‖wseq n‖ < R :=
      hw.norm.eventually (gt_mem_nhds (by dsimp [R]; linarith))
    filter_upwards [eventually_gt_atTop (0 : ℕ), hwB] with n hn hwB k
    by_cases hk : k ≤ n
    · have hneg := norm_poch_neg_nat_div_pow_le_one hn k
      have hpos := norm_poch_nat_add_div_pow_le c hn hk
      have hprod : ‖poch (-(n : ℂ)) k / (n : ℂ) ^ k‖ *
          ‖poch ((n : ℂ) + c) k / (n : ℂ) ^ k‖ ≤ D ^ k := by
        exact (mul_le_mul hneg hpos (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      simp only [norm_mul, norm_pow]
      calc
        _ ≤ (D ^ k * R ^ k) * ‖regularizedHGFunCoeff ∅ {b} k‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hprod (pow_le_pow_left₀ (norm_nonneg _) hwB.le k)
              (by positivity) (by dsimp [D]; positivity)) (norm_nonneg _)
        _ = _ := by rw [mul_pow]
    · rw [poch_neg_nat_eq_zero (by omega : n < k)]
      simp only [zero_div, zero_mul, norm_zero]
      positivity
  -- Mathlib’s Tannery theorem applies with an entire regularized Bessel series majorant.
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint hbnd
  convert ht using 1
  rw [regularizedHGFun_eq_tsum]
  congr 1
  apply tsum_congr
  intro k
  rw [neg_pow]
  ring
/-- The finite Jacobi series with reciprocal Gamma coefficients. -/
private lemma jacobi_eq_Gamma_mul_scaled_series {α : ℝ} (hα : -1 < α) (β : ℂ)
    {n : ℕ} (hn : 0 < n) (w : ℂ) :
    jacobiPolyP α β n (1 - 2 * w / (n : ℂ) ^ 2) =
      Gamma ((n : ℂ) + α + 1) / n.factorial *
        ∑' k : ℕ, (poch (-(n : ℂ)) k / (n : ℂ) ^ k) *
          (poch ((n : ℂ) + (α + β + 1)) k / (n : ℂ) ^ k) *
          w ^ k * regularizedHGFunCoeff ∅ {(α : ℂ) + 1} k := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have ha : 0 < ((α : ℂ) + 1).re := by simp; linarith
  have hG : Gamma ((α : ℂ) + 1) ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hp (k : ℕ) : poch ((α : ℂ) + 1) k ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos ha) k
  have hGn : Gamma ((n : ℂ) + α + 1) = poch ((α : ℂ) + 1) n * Gamma ((α : ℂ) + 1) := by
    rw [show (n : ℂ) + α + 1 = ((α : ℂ) + 1) + n by ring]
    exact DLMF.Gamma.Gamma_add_nat_eq_poch_mul_Gamma ha n
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk => by
    rw [poch_neg_nat_eq_zero (by simp only [Finset.mem_range, not_lt] at hk; omega)]
    simp), jacobiPolyP, ordinaryHypergeometric_eq_sum_neg_nat,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [regularizedHGFunCoeff_empty, gaussHGCoeff, hGn,
    DLMF.Gamma.Gamma_add_nat_eq_poch_mul_Gamma ha k,
    show (1 - (1 - 2 * w / (n : ℂ) ^ 2)) / 2 = w / (n : ℂ) ^ 2 by ring,
    show (n : ℂ) + α + β + 1 = n + (α + β + 1) by ring,
    div_pow, show ((n : ℂ) ^ 2) ^ k = ((n : ℂ) ^ k) ^ 2 by ring]
  field_simp [hp, hG, hnC]

/-- Jacobi polynomials at a shrinking endpoint scale have a regularized Bessel limit. -/
theorem jacobi_mehler_heine_regularized {α : ℝ} (hα : -1 < α) (β : ℂ)
    {wseq : ℕ → ℂ} {w : ℂ} (hw : Tendsto wseq atTop (𝓝 w)) :
    Tendsto (fun n : ℕ => (Real.rpow (n : ℝ) (-α) : ℂ) *
      jacobiPolyP α β n (1 - 2 * wseq n / (n : ℂ) ^ 2)) atTop
      (𝓝 (regularizedHGFun ∅ {(α : ℂ) + 1} (-w))) := by
  have hR := (DLMF.Gamma.Gamma_ratio_power (a := (α : ℂ) + 1) (b := 1)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hS := tendsto_jacobi_scaled_series ((α : ℂ) + β + 1) ((α : ℂ) + 1) hw
  have h := hR.mul hS
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (Real.rpow (n : ℝ) (-α) : ℂ) = (n : ℂ) ^ (-(α : ℂ)) := by
    change (((n : ℝ) ^ (-α) : ℝ) : ℂ) = _
    rw [ofReal_cpow hnR.le, ofReal_neg, ofReal_natCast]
  rw [jacobi_eq_Gamma_mul_scaled_series hα β hn]
  simp only [Function.comp_apply, ofReal_natCast]
  rw [show (α : ℂ) + 1 - 1 = α by ring, Gamma_nat_eq_factorial, hp, cpow_neg,
    show (n : ℂ) + ((α : ℂ) + 1) = n + α + 1 by ring]
  ring
/-- The Jacobi Mehler–Heine formula with the original Bessel normalization. -/
@[dlmf 18.11.E5]
theorem jacobi_mehler_heine {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => (Real.rpow (n : ℝ) (-α) : ℂ) * jacobiPolyP α β n (cos ((z : ℂ) / n)))
        atTop
      (𝓝 ((Real.rpow (2 / z) α : ℂ) * besselJ α z)) := by
  -- The series argument allows arbitrary complex β; retain the original real-parameter interface.
  clear hβ
  let wseq (n : ℕ) : ℂ := (n : ℂ) ^ 2 * ((1 - cos ((z : ℂ) / n)) / 2)
  have ht : Tendsto (fun n : ℕ => (z / (n : ℝ)) / 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))).div_const (2 : ℝ)
  have hs := ((Real.continuous_sinc.tendsto 0).comp ht).const_mul (z / 2)
  simp only [Real.sinc_zero, mul_one] at hs
  have hw : Tendsto wseq atTop (𝓝 ((z : ℂ) ^ 2 / 4)) := by
    have h := (continuous_ofReal.tendsto _).comp (hs.pow 2)
    convert h.congr' ?_ using 1
    · congr 1
      push_cast
      ring
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have ht0 : z / (n : ℝ) / 2 ≠ 0 := by positivity
      have hcos : (1 - Real.cos (z / n)) / 2 = Real.sin (z / n / 2) ^ 2 := by
        have he := Real.cos_two_mul (z / n / 2)
        rw [show 2 * (z / n / 2) = z / n by ring] at he
        nlinarith [Real.sin_sq_add_cos_sq (z / n / 2)]
      dsimp [wseq]
      rw [Real.sinc_of_ne_zero ht0]
      push_cast
      have hcosC := congrArg Complex.ofReal hcos
      push_cast at hcosC
      rw [hcosC]
      field_simp [ofReal_ne_zero.mpr hz.ne']
  have h := jacobi_mehler_heine_regularized hα (β : ℂ) hw
  have harg : ∀ᶠ n : ℕ in atTop,
      1 - 2 * wseq n / (n : ℂ) ^ 2 = cos ((z : ℂ) / n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    dsimp [wseq]
    field_simp
    ring
  have h' := h.congr' (harg.mono fun n hn => by rw [hn])
  convert h' using 1
  have hJ := besselJ_ofReal_eq α hz
  rw [hJ, ← mul_assoc, ← ofReal_mul]
  have hp : Real.rpow (2 / z) α * Real.rpow (z / 2) α = 1 := by
    change (2 / z) ^ α * (z / 2) ^ α = 1
    rw [← Real.mul_rpow (by positivity : 0 ≤ 2 / z) (by positivity : 0 ≤ z / 2)]
    have hz0 : z ≠ 0 := hz.ne'
    rw [show 2 / z * (z / 2) = 1 by field_simp, Real.one_rpow]
  change 𝓝 (((Real.rpow (2 / z) α * Real.rpow (z / 2) α : ℝ) : ℂ) *
    regularizedHGFun ∅ {(α : ℂ) + 1} (((-(z ^ 2 / 4) : ℝ)) : ℂ)) = _
  rw [hp, ofReal_one, one_mul]
  push_cast
  rfl

/-- The complex scaled Laguerre limit, without choosing a square-root branch. -/
theorem laguerrePolyL_mehler_heine_regularized {α : ℝ} (hα : -1 < α) (z : ℂ) :
    Tendsto (fun n : ℕ => (Real.rpow (n : ℝ) (-α) : ℂ) * laguerrePolyL α n (z / n))
      atTop (𝓝 (regularizedHGFun ∅ {(α : ℂ) + 1} (-z))) := by
  have hc : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := by
    intro k hk
    have h := congrArg Complex.re hk
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hR := (DLMF.Gamma.Gamma_ratio_power (a := (α : ℂ) + 1) (b := 1)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hM := (tendsto_regularizedConfluent_sub_div 0 ((α : ℂ) + 1) z).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hR.mul hM
  simp only [one_mul] at h
  convert h.congr' ?_ using 1
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [laguerrePolyL_eq_Gamma_mul_regularized hc]
  simp only [Function.comp_apply, ofReal_natCast, zero_sub, ofReal_neg]
  have hp : (Real.rpow (n : ℝ) (-α) : ℂ) = (n : ℂ) ^ (-(α : ℂ)) := by
    change (((n : ℝ) ^ (-α) : ℝ) : ℂ) = _
    rw [ofReal_cpow hnR.le, ofReal_neg, ofReal_natCast]
  rw [show (α : ℂ) + 1 - 1 = α by ring, Gamma_nat_eq_factorial, hp, cpow_neg,
    show (n : ℂ) + ((α : ℂ) + 1) = n + α + 1 by ring]
  ring

/-- The map `(fun n : ℕ => (Real.rpow (n : ℝ) (-α) : ℂ) * laguerrePolyL α n ((z : ℂ) / n))` tends
to `(𝓝 ((Real.rpow z (-α / 2) : ℂ) * besselJ α (2 * Real.sqrt z)))` along `atTop`. -/
@[dlmf 18.11.E6]
theorem laguerrePolyL_mehler_heine {α : ℝ} (hα : -1 < α) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => (Real.rpow (n : ℝ) (-α) : ℂ) * laguerrePolyL α n ((z : ℂ) / n)) atTop
      (𝓝 ((Real.rpow z (-α / 2) : ℂ) * besselJ α (2 * Real.sqrt z))) := by
  have h := laguerrePolyL_mehler_heine_regularized hα (z : ℂ)
  convert h using 1
  have hs : 0 < 2 * Real.sqrt z := by positivity
  have hJ := besselJ_ofReal_eq α hs
  have hzsq : (2 * Real.sqrt z) ^ 2 / 4 = z := by nlinarith [Real.sq_sqrt hz.le]
  have hp : Real.rpow z (-α / 2) * Real.rpow (Real.sqrt z) α = 1 := by
    change (z ^ (-α / 2) : ℝ) * (Real.sqrt z) ^ α = 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]
    norm_num [show -α / 2 + 1 / 2 * α = 0 by ring]
  push_cast at hJ
  rw [hJ]
  norm_num only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  have harg : -(((2 * (Real.sqrt z : ℂ)) ^ 2) / 4) = -(z : ℂ) := by
    exact_mod_cast congrArg Neg.neg hzsq
  rw [harg, ← mul_assoc, ← ofReal_mul]
  change 𝓝 (((Real.rpow z (-α / 2) * Real.rpow (Real.sqrt z) α : ℝ) : ℂ) *
    regularizedHGFun ∅ {(α : ℂ) + 1} (-z)) = _
  rw [hp, ofReal_one, one_mul]

/-- The map `(fun n : ℕ => (-1 : ℂ) ^ n * Real.sqrt n / (2 ^ (2 * n) * (n.factorial : ℂ)) * aeval
(z / (2 * (Real.sqrt n : ℂ))) (hermitePolyH (2 * n)))` tends to `(𝓝 (cos z / (Real.sqrt
Real.pi : ℂ)))` along `atTop`. -/
@[dlmf 18.11.E7]
theorem hermite_even_mehler_heine (z : ℂ) :
    Tendsto (fun n : ℕ => (-1 : ℂ) ^ n * Real.sqrt n / (2 ^ (2 * n) * (n.factorial : ℂ)) *
      aeval (z / (2 * (Real.sqrt n : ℂ))) (hermitePolyH (2 * n))) atTop
      (𝓝 (cos z / (Real.sqrt Real.pi : ℂ))) := by
  have h := laguerrePolyL_mehler_heine_regularized (α := -1 / 2) (by norm_num) (z ^ 2 / 4)
  norm_num only [ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat] at h
  have hΓ : Gamma (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Gamma_ofReal, Real.Gamma_one_half_eq]
  rw [regularized0F1_half_eq_cos, hΓ] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (Real.sqrt n : ℂ) ^ 2 = n := by
    exact_mod_cast Real.sq_sqrt hnR.le
  have hs0 : (Real.sqrt n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hnR).ne'
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have harg : (z / (2 * (Real.sqrt n : ℂ))) ^ 2 = (z ^ 2 / 4) / n := by
    rw [div_pow, mul_pow, hs]; ring
  rw [hermitePolyH_even_eq_laguerrePolyL, harg]
  have hnPow : Real.rpow (n : ℝ) (1 / 2) = Real.sqrt n := by
    change (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt n
    exact (Real.sqrt_eq_rpow _).symm
  rw [hnPow]
  have hsgn : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have htwo : (2 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsgn2 : (-1 : ℂ) ^ (n * 2) = 1 := by rw [Nat.mul_comm, pow_mul]; norm_num
  norm_num only [neg_div]
  field_simp [hf, htwo]
  ring_nf
  simp only [hsgn2, mul_one]

/-- The map `(fun n : ℕ => (-1 : ℂ) ^ n / (2 ^ (2 * n) * (n.factorial : ℂ)) * aeval (z / (2 *
(Real.sqrt n : ℂ))) (hermitePolyH (2 * n + 1)))` tends to `(𝓝 (2 * sin z / (Real.sqrt Real.pi
: ℂ)))` along `atTop`. -/
@[dlmf 18.11.E8]
theorem hermite_odd_mehler_heine (z : ℂ) :
    Tendsto (fun n : ℕ => (-1 : ℂ) ^ n / (2 ^ (2 * n) * (n.factorial : ℂ)) *
      aeval (z / (2 * (Real.sqrt n : ℂ))) (hermitePolyH (2 * n + 1))) atTop
      (𝓝 (2 * sin z / (Real.sqrt Real.pi : ℂ))) := by
  have h := (laguerrePolyL_mehler_heine_regularized (α := 1 / 2) (by norm_num) (z ^ 2 / 4)).const_mul z
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at h
  have hΓ : Gamma (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Gamma_ofReal, Real.Gamma_one_half_eq]
  have hval : z * regularizedHGFun ∅ {(3 / 2 : ℂ)} (-(z ^ 2 / 4)) =
      2 * sin z / (Real.sqrt Real.pi : ℂ) := by
    by_cases hz : z = 0
    · simp [hz]
    · rw [regularized0F1_three_halves_eq_sinc hz, hΓ]
      field_simp
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (Real.sqrt n : ℂ) ^ 2 = n := by exact_mod_cast Real.sq_sqrt hnR.le
  have hs0 : (Real.sqrt n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hnR).ne'
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have harg : (z / (2 * (Real.sqrt n : ℂ))) ^ 2 = (z ^ 2 / 4) / n := by
    rw [div_pow, mul_pow, hs]; ring
  have hnPow : Real.rpow (n : ℝ) (-(1 / 2)) = (Real.sqrt n)⁻¹ := by
    change (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt n)⁻¹
    rw [Real.rpow_neg hnR.le, Real.sqrt_eq_rpow]
  rw [hermitePolyH_odd_eq_laguerrePolyL, harg, hnPow, ofReal_inv,
    pow_succ (2 : ℂ) (2 * n)]
  have hsgn : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have htwo : (2 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsgn2 : (-1 : ℂ) ^ (n * 2) = 1 := by rw [Nat.mul_comm, pow_mul]; norm_num
  field_simp [hf, htwo, hs0]
  ring_nf
  simp only [hsgn2, mul_one]


end DLMF.OrthogonalPolynomials
