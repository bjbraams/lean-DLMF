/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Hahn
public import DLMF.Confluent.Relations
/-!
# Wilson, continuous dual Hahn, Racah, and dual Hahn polynomials

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology
open DLMF.Hypergeometric
open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- Wilson polynomials in the polynomial argument `x = y²`. The product form
avoids choosing a square root. -/
@[dlmf 18.26.E1]
def wilson (a b c d : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (a + b) n * poch (a + c) n * poch (a + d) n *
    ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k * poch (n + a + b + c + d - 1) k *
        (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
        (poch (a + b) k * poch (a + c) k * poch (a + d) k * k.factorial)

/-- The continuous dual Hahn polynomial `S_n(x; a, b, c)` with polynomial argument `x = y²`,
as the finite `₃F₂` sum of DLMF 18.26.2. -/
@[dlmf 18.26.E2]
def continuousDualHahn (a b c : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (a + b) n * poch (a + c) n *
    ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
      (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
      (poch (a + b) k * poch (a + c) k * k.factorial)

/-- The Racah polynomial `R_n(x; α, β, γ, δ)` in the variable `x = λ(y)`, as the finite `₄F₃`
sum of DLMF 18.26.3. -/
@[dlmf 18.26.E3]
def racah (α β γ δ : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k * poch (n + α + β + 1) k *
    (∏ j ∈ Finset.range k, ((j : ℂ) * (j + γ + δ + 1) - x)) /
    (poch (α + 1) k * poch (β + δ + 1) k * poch (γ + 1) k * k.factorial)

/-- The dual Hahn polynomial `R_n(x; γ, δ, N)` in the variable `x = λ(y)`, as the finite `₃F₂`
sum of DLMF 18.26.4. -/
@[dlmf 18.26.E4]
def dualHahn (γ δ : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
    (∏ j ∈ Finset.range k, ((j : ℂ) * (j + γ + δ + 1) - x)) /
    (poch (γ + 1) k * poch (-(N : ℂ)) k * k.factorial)

/-- Factoring the quadratic product into two Pochhammer symbols. -/
theorem poch_mul_eq_prod (u v : ℂ) (k : ℕ) :
    poch u k * poch v k = ∏ j ∈ Finset.range k, (u + j) * (v + j) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ, poch_succ, Finset.prod_range_succ, ← ih]
    ring

/-- `∏_{j<k} ((a+j)² + y²) = (a+iy)_k (a-iy)_k`. -/
theorem poch_conjugate_pair (a y : ℂ) (k : ℕ) :
    ∏ j ∈ Finset.range k, ((a + j) ^ 2 + y ^ 2) = poch (a + I * y) k * poch (a - I * y) k := by
  rw [poch_mul_eq_prod]
  apply Finset.prod_congr rfl
  intro j _
  calc
    _ = (a + I * y + j) * (a - I * y + j) + (I ^ 2 + 1) * y ^ 2 := by ring
    _ = _ := by rw [I_sq]; ring

/-- `∏_{j<k} (j(j+v) - y(y+v)) = (-y)_k (y+v)_k`. -/
theorem poch_quadratic_pair (v y : ℂ) (k : ℕ) :
    ∏ j ∈ Finset.range k, ((j : ℂ) * (j + v) - y * (y + v)) =
      poch (-y) k * poch (y + v) k := by
  rw [poch_mul_eq_prod]
  apply Finset.prod_congr rfl
  intro j _
  ring

@[dlmf 18.26.E1]
theorem wilson_hypergeometric (a b c d : ℂ) (n : ℕ) (y : ℂ) :
    wilson a b c d n (y ^ 2) = poch (a + b) n * poch (a + c) n * poch (a + d) n *
      terminatingHG n [-(n : ℂ), n + a + b + c + d - 1, a + I * y, a - I * y] [a + b, a + c, a + d] 1 := by
  unfold wilson terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [poch_conjugate_pair]
  ring

@[dlmf 18.26.E2]
theorem continuousDualHahn_hypergeometric (a b c : ℂ) (n : ℕ) (y : ℂ) :
    continuousDualHahn a b c n (y ^ 2) = poch (a + b) n * poch (a + c) n *
      terminatingHG n [-(n : ℂ), a + I * y, a - I * y] [a + b, a + c] 1 := by
  unfold continuousDualHahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [poch_conjugate_pair]
  ring

@[dlmf 18.26.E3]
theorem racah_hypergeometric (α β γ δ : ℂ) (n : ℕ) (y : ℂ) :
    racah α β γ δ n (y * (y + γ + δ + 1)) =
      terminatingHG n [-(n : ℂ), n + α + β + 1, -y, y + γ + δ + 1] [α + 1, β + δ + 1, γ + 1] 1 := by
  unfold racah terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  apply Finset.sum_congr rfl
  intro k _
  have hp := poch_quadratic_pair (γ + δ + 1) y k
  simp only [show y + (γ + δ + 1) = y + γ + δ + 1 by ring,
    show ∀ j : ℕ, (j : ℂ) + (γ + δ + 1) = j + γ + δ + 1 by intro j; ring] at hp
  rw [hp]
  ring

@[dlmf 18.26.E4]
theorem dualHahn_hypergeometric (γ δ : ℂ) (N n : ℕ) (y : ℂ) :
    dualHahn γ δ N n (y * (y + γ + δ + 1)) =
      terminatingHG n [-(n : ℂ), -y, y + γ + δ + 1] [γ + 1, -(N : ℂ)] 1 := by
  unfold dualHahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  apply Finset.sum_congr rfl
  intro k _
  have hp := poch_quadratic_pair (γ + δ + 1) y k
  simp only [show y + (γ + δ + 1) = y + γ + δ + 1 by ring,
    show ∀ j : ℕ, (j : ℂ) + (γ + δ + 1) = j + γ + δ + 1 by intro j; ring] at hp
  rw [hp]
  ring

@[dlmf 18.26.E4_1]
theorem dualHahn_hahn_duality (γ δ : ℂ) {N n y : ℕ} (hn : n ≤ N) (hy : y ≤ N) :
    dualHahn γ δ N n ((y : ℂ) * (y + γ + δ + 1)) = hahn γ δ N y n := by
  rw [dualHahn_hypergeometric, hahn]
  have hs := terminatingHG_hasSum_neg_nat n [-(y : ℂ), y + γ + δ + 1] [γ + 1, -(N : ℂ)] 1
  have ht := terminatingHG_hasSum_neg_nat y [y + γ + δ + 1, -(n : ℂ)] [γ + 1, -(N : ℂ)] 1
  apply hs.unique
  convert ht using 1
  funext k
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

@[dlmf 18.26.E4_2]
theorem racah_duality (α β γ δ : ℂ) (n y : ℕ) :
    racah α β γ δ n ((y : ℂ) * (y + γ + δ + 1)) = racah γ δ α β y ((n : ℂ) * (n + α + β + 1)) := by
  rw [racah_hypergeometric, racah_hypergeometric]
  have hs := terminatingHG_hasSum_neg_nat n [n + α + β + 1, -(y : ℂ), y + γ + δ + 1]
    [α + 1, β + δ + 1, γ + 1] 1
  have ht := terminatingHG_hasSum_neg_nat y [y + γ + δ + 1, -(n : ℂ), n + α + β + 1]
    [γ + 1, δ + β + 1, α + 1] 1
  apply hs.unique
  convert ht using 1
  funext k
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [show δ + β + 1 = β + δ + 1 by ring]
  ring

@[dlmf 18.25.E2]
theorem wilson_orthogonal {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) {m n : ℕ} (hmn : m ≠ n) :
    ∫ y : ℝ in Set.Ioi 0, wilson a b c d m ((y : ℂ) ^ 2) * wilson a b c d n ((y : ℂ) ^ 2) *
      (‖Gamma (a + I * y) * Gamma (b + I * y) * Gamma (c + I * y) * Gamma (d + I * y) / Gamma (2 * I * y)‖ ^ 2 : ℝ) = 0 := by
  sorry

@[dlmf 18.25.E8]
theorem continuousDualHahn_orthogonality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (m n : ℕ) :
    ∫ y : ℝ in Set.Ioi 0, continuousDualHahn a b c m ((y : ℂ) ^ 2) * continuousDualHahn a b c n ((y : ℂ) ^ 2) *
      (‖Gamma (a + I * y) * Gamma (b + I * y) * Gamma (c + I * y) / Gamma (2 * I * y)‖ ^ 2 : ℝ) =
      if m = n then n.factorial * 2 * Real.pi * Gamma (n + (a : ℂ) + b) *
        Gamma (n + (a : ℂ) + c) * Gamma (n + (b : ℂ) + c) else 0 := by
  sorry

/-- `(u + d)_k / (v + d)_k → 1` as the real `d → ∞`. -/
theorem tendsto_poch_ratio_atTop (u v : ℂ) (k : ℕ) :
    Tendsto (fun d : ℝ => poch (u + d) k / poch (v + d) k) atTop (𝓝 1) := by
  have h := (tendsto_poch_add_div_pow u k).div (tendsto_poch_add_div_pow v k) one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hd' : (d : ℂ) ^ k ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr hd.ne')
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hd']

/-- For fixed `u` and `k`, eventually as `d → ∞` the symbol `(u+d)_k` is nonzero. -/
theorem eventually_poch_add_ne_zero (u : ℂ) (k : ℕ) :
    ∀ᶠ d : ℝ in atTop, poch (u + d) k ≠ 0 := by
  filter_upwards [(tendsto_poch_add_div_pow u k).eventually_ne one_ne_zero] with d hd h
  exact hd (by rw [h, zero_div])

@[dlmf 18.26.E5]
theorem wilson_limit_continuousDualHahn {a b c : ℂ} (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (n : ℕ) (x : ℂ) :
    Tendsto (fun d : ℝ => wilson a b c d n x / poch (a + d) n) atTop (𝓝 (continuousDualHahn a b c n x)) := by
  unfold wilson continuousDualHahn
  have hT : Tendsto (fun d : ℝ => poch (a + b) n * poch (a + c) n *
      ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
        (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
        (poch (a + b) k * poch (a + c) k * k.factorial) *
        (poch ((n + a + b + c - 1) + d) k / poch (a + d) k)) atTop
      (𝓝 (poch (a + b) n * poch (a + c) n *
        ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
          (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
          (poch (a + b) k * poch (a + c) k * k.factorial))) := by
    refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun k _ => ?_)
    simpa using (tendsto_poch_ratio_atTop (n + a + b + c - 1) a k).const_mul
      (poch (-(n : ℂ)) k * (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
        (poch (a + b) k * poch (a + c) k * k.factorial))
  refine hT.congr' ?_
  filter_upwards [eventually_poch_add_ne_zero a n] with d hd
  rw [eq_div_iff hd, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (n : ℂ) + a + b + c + d - 1 = n + a + b + c - 1 + d by ring]
  by_cases hk : poch (a + ↑d) k = 0
  · simp [hk]
  · field_simp

@[dlmf 18.26.E9]
theorem racah_limit_dualHahn {γ δ : ℂ} (hγ : -1 < γ.re) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    Tendsto (fun b : ℝ => racah (-(N : ℂ) - 1) b γ δ n x) atTop (𝓝 (dualHahn γ δ N n x)) := by
  unfold racah dualHahn
  refine tendsto_finsetSum _ fun k _ => ?_
  have h := (tendsto_poch_ratio_atTop ((n : ℂ) - N) (δ + 1) k).const_mul
    (poch (-(n : ℂ)) k * (∏ j ∈ Finset.range k, ((j : ℂ) * (j + γ + δ + 1) - x)) /
      (poch (γ + 1) k * poch (-(N : ℂ)) k * k.factorial))
  rw [mul_one] at h
  refine h.congr' (Eventually.of_forall fun b => ?_)
  beta_reduce
  rw [show (n : ℂ) + (-(N : ℂ) - 1) + b + 1 = n - N + b by ring,
    show -(N : ℂ) - 1 + 1 = -N by ring, show (b : ℂ) + δ + 1 = δ + 1 + b by ring]
  by_cases hk : poch (δ + 1 + ↑b) k = 0
  · simp [hk]
  · field_simp

@[dlmf 18.26.E10]
theorem racah_limit_hahn {α β : ℂ} (hα : -1 < α.re) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    Tendsto (fun d : ℝ => racah α β (-(N : ℂ) - 1) d n (x * (x - N + d))) atTop (𝓝 (hahn α β N n x)) := by
  unfold racah hahn terminatingHG
  refine tendsto_finsetSum _ fun k _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  have h := (tendsto_poch_ratio_atTop (x - N) (β + 1) k).const_mul
    (poch (-(n : ℂ)) k * (poch (n + α + β + 1) k * poch (-x) k) /
      (poch (α + 1) k * poch (-(N : ℂ)) k) / k.factorial)
  rw [mul_one] at h
  refine h.congr' (Eventually.of_forall fun d => ?_)
  have hprod : ∏ j ∈ Finset.range k, ((j : ℂ) * (j + (-(N : ℂ) - 1) + d + 1) - x * (x - N + d)) =
      poch (-x) k * poch (x - N + d) k := by
    rw [poch_mul_eq_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  beta_reduce
  rw [hprod, show -(N : ℂ) - 1 + 1 = -N by ring, show (β : ℂ) + d + 1 = β + 1 + d by ring]
  by_cases hk : poch (β + 1 + ↑d) k = 0
  · simp [hk]
  · field_simp

/-- Factoring the shifted Wilson product. -/
theorem prod_sq_add_shift (a y s : ℂ) (k : ℕ) :
    ∏ j ∈ Finset.range k, ((a + j) ^ 2 + (y + s * I / 2) ^ 2) =
      poch (a + I * y - s / 2) k * poch (a - I * y + s / 2) k := by
  rw [poch_mul_eq_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  linear_combination (y ^ 2 + s ^ 2 / 4) * I_sq

/-- The forward difference of the Wilson product pair. -/
theorem poch_pair_sub (u v : ℂ) (k : ℕ) :
    poch (u - 1 / 2) (k + 1) * poch (v + 1 / 2) (k + 1) -
      poch (u + 1 / 2) (k + 1) * poch (v - 1 / 2) (k + 1) =
      (k + 1) * (u - v) * (poch (u + 1 / 2) k * poch (v + 1 / 2) k) := by
  rw [poch_succ_left (u - 1 / 2), poch_succ (v + 1 / 2), poch_succ (u + 1 / 2),
    poch_succ_left (v - 1 / 2), show u - 1 / 2 + 1 = u + 1 / 2 by ring,
    show v - 1 / 2 + 1 = v + 1 / 2 by ring]
  ring

@[dlmf 18.26.E14]
theorem wilson_central_difference {a b c d : ℂ}
    (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (had : 0 < (a + d).re) (n : ℕ) (y : ℂ) :
    wilson a b c d (n + 1) ((y + I / 2) ^ 2) - wilson a b c d (n + 1) ((y - I / 2) ^ 2) =
      -2 * I * y * (n + 1) * (n + a + b + c + d) *
        wilson (a + 1 / 2) (b + 1 / 2) (c + 1 / 2) (d + 1 / 2) n (y ^ 2) := by
  have hp : ∀ (z : ℂ) (k : ℕ), 0 < z.re → poch (z + 1) k ≠ 0 := fun z k hz =>
    poch_ne_zero_of_re_pos (by simp; linarith) k
  have h0 : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  unfold wilson
  have e1 : ∀ k, ∏ j ∈ Finset.range k, ((a + j) ^ 2 + (y + I / 2) ^ 2) =
      poch (a + I * y - 1 / 2) k * poch (a - I * y + 1 / 2) k := fun k => by
    simpa using prod_sq_add_shift a y 1 k
  have e2 : ∀ k, ∏ j ∈ Finset.range k, ((a + j) ^ 2 + (y - I / 2) ^ 2) =
      poch (a + I * y + 1 / 2) k * poch (a - I * y - 1 / 2) k := fun k => by
    have := prod_sq_add_shift a y (-1) k
    simp only [neg_mul, one_mul, neg_div] at this
    rw [show y - I / 2 = y + -(I / 2) by ring, this]
    congr 2; ring
  have e3 : ∀ k, ∏ j ∈ Finset.range k, ((a + 1 / 2 + j) ^ 2 + y ^ 2) =
      poch (a + I * y + 1 / 2) k * poch (a - I * y + 1 / 2) k := fun k => by
    have := prod_sq_add_shift (a + 1 / 2) y 0 k
    simp only [zero_mul, zero_div, add_zero, sub_zero] at this
    rw [this]; congr 2 <;> ring
  simp_rw [e1, e2, e3]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [poch_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, sub_self,
    add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key := poch_pair_sub (a + I * y) (a - I * y) k
  rw [← sub_div, ← mul_sub, key]
  rw [poch_succ_left (a + b), poch_succ_left (a + c), poch_succ_left (a + d),
    poch_succ_left (a + b) k, poch_succ_left (a + c) k, poch_succ_left (a + d) k,
    poch_succ_left (-((n + 1 : ℕ) : ℂ)), poch_succ_left (((n + 1 : ℕ) : ℂ) + a + b + c + d - 1),
    Nat.factorial_succ,
    show a + 1 / 2 + (b + 1 / 2) = a + b + 1 by ring, show a + 1 / 2 + (c + 1 / 2) = a + c + 1 by ring,
    show a + 1 / 2 + (d + 1 / 2) = a + d + 1 by ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring,
    show ((n + 1 : ℕ) : ℂ) + a + b + c + d - 1 + 1 = (n : ℂ) + (a + 1 / 2) + (b + 1 / 2) +
      (c + 1 / 2) + (d + 1 / 2) - 1 by push_cast; ring]
  have := h0 _ hab; have := h0 _ hac; have := h0 _ had
  have := hp _ k hab; have := hp _ k hac; have := hp _ k had
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  push_cast
  field_simp
  ring

@[dlmf 18.26.E15]
theorem continuousDualHahn_central_difference {a b c : ℂ}
    (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (n : ℕ) (y : ℂ) :
    continuousDualHahn a b c (n + 1) ((y + I / 2) ^ 2) - continuousDualHahn a b c (n + 1) ((y - I / 2) ^ 2) =
      -2 * I * y * (n + 1) * continuousDualHahn (a + 1 / 2) (b + 1 / 2) (c + 1 / 2) n (y ^ 2) := by
  have hp : ∀ (z : ℂ) (k : ℕ), 0 < z.re → poch (z + 1) k ≠ 0 := fun z k hz =>
    poch_ne_zero_of_re_pos (by simp; linarith) k
  have h0 : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  unfold continuousDualHahn
  have e1 : ∀ k, ∏ j ∈ Finset.range k, ((a + j) ^ 2 + (y + I / 2) ^ 2) =
      poch (a + I * y - 1 / 2) k * poch (a - I * y + 1 / 2) k := fun k => by
    simpa using prod_sq_add_shift a y 1 k
  have e2 : ∀ k, ∏ j ∈ Finset.range k, ((a + j) ^ 2 + (y - I / 2) ^ 2) =
      poch (a + I * y + 1 / 2) k * poch (a - I * y - 1 / 2) k := fun k => by
    have := prod_sq_add_shift a y (-1) k
    simp only [neg_mul, one_mul, neg_div] at this
    rw [show y - I / 2 = y + -(I / 2) by ring, this]
    congr 2; ring
  have e3 : ∀ k, ∏ j ∈ Finset.range k, ((a + 1 / 2 + j) ^ 2 + y ^ 2) =
      poch (a + I * y + 1 / 2) k * poch (a - I * y + 1 / 2) k := fun k => by
    have := prod_sq_add_shift (a + 1 / 2) y 0 k
    simp only [zero_mul, zero_div, add_zero, sub_zero] at this
    rw [this]; congr 2 <;> ring
  simp_rw [e1, e2, e3]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [poch_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, sub_self,
    add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key := poch_pair_sub (a + I * y) (a - I * y) k
  rw [← sub_div, ← mul_sub, key]
  rw [poch_succ_left (a + b), poch_succ_left (a + c),
    poch_succ_left (a + b) k, poch_succ_left (a + c) k,
    poch_succ_left (-((n + 1 : ℕ) : ℂ)), Nat.factorial_succ,
    show a + 1 / 2 + (b + 1 / 2) = a + b + 1 by ring, show a + 1 / 2 + (c + 1 / 2) = a + c + 1 by ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring]
  have := h0 _ hab; have := h0 _ hac
  have := hp _ k hab; have := hp _ k hac
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  push_cast
  field_simp
  ring

/-- Wilson coefficients are a convolution of two Gauss coefficient sequences. -/
theorem wilson_coeff_convolution {a b c d : ℂ}
    (hab : 0 < (a+b).re) (hac : 0 < (a+c).re) (had : 0 < (a+d).re)
    (hbc : 0 < (b+c).re) (y : ℂ) (n : ℕ) :
    wilson a b c d n (y^2) / (poch (a+d) n * poch (b+c) n * n !) =
      ∑ j ∈ Finset.range (n+1), gaussHGCoeff (a+I*y) (d+I*y) (a+d) j *
        gaussHGCoeff (b-I*y) (c-I*y) (b+c) (n-j) := by
  have hE := poch_ne_zero_of_re_pos hab
  have hF := poch_ne_zero_of_re_pos hac
  have hR := poch_ne_zero_of_re_pos had
  have hT := poch_ne_zero_of_re_pos hbc
  have ht := balanced_4F3_convolution (a+I*y) (a-I*y) (n+a+b+c+d-1) (a+b) (a+c) (a+d)
    hab hac had n (by ring)
  rw [show a+d-(a-I*y) = d+I*y by ring,
    show a+d-(n+a+b+c+d-1) = 1-(b+c)-n by ring,
    show a+b-(a+I*y) = b-I*y by ring,
    show a+c-(a+I*y) = c-I*y by ring] at ht
  have he : wilson a b c d n (y^2) / (poch (a+d) n * poch (b+c) n * n !) =
      poch (a+b) n * poch (a+c) n / (poch (b+c) n * n !) *
      (∑ k ∈ Finset.range (n+1), poch (-(n : ℂ)) k * poch (a+I*y) k * poch (a-I*y) k *
        poch (n+a+b+c+d-1) k /
        (poch (a+d) k * poch (a+b) k * poch (a+c) k * k !)) := by
    rw [wilson_hypergeometric]
    simp only [terminatingHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
    have hs : (∑ k ∈ Finset.range (n+1),
        poch (-(n : ℂ)) k * (poch (n+a+b+c+d-1) k *
          (poch (a+I*y) k * poch (a-I*y) k)) /
        (poch (a+b) k * (poch (a+c) k * poch (a+d) k)) / k !) =
        ∑ k ∈ Finset.range (n+1), poch (-(n : ℂ)) k * poch (a+I*y) k * poch (a-I*y) k *
          poch (n+a+b+c+d-1) k / (poch (a+d) k * poch (a+b) k * poch (a+c) k * k !) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hs]
    field_simp [hR n]
  rw [he, ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := by simpa using hj
  have hEn : poch (a+b) n = poch (a+b) j * poch (a+b+j) (n-j) := by
    rw [← poch_add, Nat.add_sub_cancel' hj']
  have hFn : poch (a+c) n = poch (a+c) j * poch (a+c+j) (n-j) := by
    rw [← poch_add, Nat.add_sub_cancel' hj']
  have hf : (n.choose j : ℂ) * j ! * (n-j)! = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj'
  have hpn : poch (1-(b+c)-n) j = (-1)^j * poch (b+c) n / poch (b+c) (n-j) := by
    apply (eq_div_iff (hT (n-j))).2
    rw [poch_eq_poch_sub_mul (b+c) hj']
    have hs : (-1 : ℂ)^j * (-1)^j = 1 := by rw [← mul_pow]; simp
    linear_combination -(poch (b+c) (n-j) * poch (1-(b+c)-n) j) * hs
  rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose, hEn, hFn, hpn]
  dsimp only [gaussHGCoeff]
  have hjf : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hlf : ((n-j)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n-j).factorial_ne_zero
  have hchoose : (n.choose j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hj').ne'
  have hEs := poch_ne_zero_of_re_pos (show 0 < (a+b+j).re by change 0 < (a+b).re + (j : ℝ); exact add_pos_of_pos_of_nonneg hab j.cast_nonneg) (n-j)
  have hFs := poch_ne_zero_of_re_pos (show 0 < (a+c+j).re by change 0 < (a+c).re + (j : ℝ); exact add_pos_of_pos_of_nonneg hac j.cast_nonneg) (n-j)
  rw [← hf]
  push_cast
  field_simp [hE j, hF j, hR j, hT n, hT (n-j), hjf, hlf, hchoose, hEs, hFs]
  have hsign : ((-1 : ℂ)^j)^2 = 1 := by rw [← pow_mul, pow_mul']; norm_num
  simp only [hsign, one_mul]


@[dlmf 18.26.E18]
theorem wilson_generating_function {a b c d : ℂ}
    (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (had : 0 < (a + d).re)
    (hbc : 0 < (b + c).re) (y : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => wilson a b c d n (y ^ 2) / (poch (a + d) n * poch (b + c) n * n.factorial) * z ^ n)
      (₂F₁ (a + I * y) (d + I * y) (a + d) z * ₂F₁ (b - I * y) (c - I * y) (b + c) z) := by
  have h1 := (hasFPowerSeriesOnBall_ordinaryHypergeometric (a+I*y) (d+I*y) (a+d)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hz)
  have h2 := (hasFPowerSeriesOnBall_ordinaryHypergeometric (b-I*y) (c-I*y) (b+c)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hz)
  have h := hasSum_coefficient_convolution h1 h2
  apply h.congr_fun
  intro n
  rw [wilson_coeff_convolution hab hac had hbc]


/-- Continuous dual Hahn coefficients are a binomial–Gauss convolution. -/
theorem dualHahn_coeff_convolution {a b c : ℂ}
    (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (y : ℂ) (n : ℕ) :
    continuousDualHahn a b c n (y ^ 2) / (poch (a + b) n * n.factorial) =
      ∑ k ∈ Finset.range (n + 1),
        (poch (a + I * y) k * poch (b + I * y) k / (poch (a + b) k * k !)) *
        (poch (c - I * y) (n - k) / (n - k)!) := by
  have hR := poch_ne_zero_of_re_pos hab
  have hD := poch_ne_zero_of_re_pos hac
  have ht := terminating_3F2_convolution (a + I * y) (a - I * y) (a + b) (a + c) hR n
  rw [show a + b - (a - I * y) = b + I * y by ring,
    show a + c - (a + I * y) = c - I * y by ring] at ht
  have he : continuousDualHahn a b c n (y ^ 2) / (poch (a + b) n * n.factorial) =
      (∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * n.choose k * poch (a + I * y) k *
        poch (a - I * y) k / poch (a + b) k * poch (a + c + k) (n - k)) / n ! := by
    unfold continuousDualHahn
    rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by simpa using hk
    rw [poch_conjugate_pair, poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
    have hp : poch (a + c) n = poch (a + c) k * poch (a + c + k) (n - k) := by
      rw [← poch_add, Nat.add_sub_cancel' hk']
    rw [hp]
    push_cast
    field_simp [hR n, hR k, hD k, Nat.cast_ne_zero.mpr k.factorial_ne_zero]
  rw [he, ht, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using hk
  have hf : (n.choose k : ℂ) * k ! * (n - k)! = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hkf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnk : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  field_simp [hn, hkf, hnk, hR k]
  linear_combination (poch (a + I * y) k * poch (b + I * y) k * poch (c - I * y) (n-k)) * hf


@[dlmf 18.26.E19]
theorem continuousDualHahn_generating_function {a b c : ℂ}
    (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (y : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => continuousDualHahn a b c n (y ^ 2) / (poch (a + b) n * n.factorial) * z ^ n)
      ((1 - z) ^ (-c + I * y) * ₂F₁ (a + I * y) (b + I * y) (a + b) z) := by
  have hg := (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + I * y) (b + I * y) (a + b)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hz)
  have hb := hasSum_one_sub_cpow_neg (c - I * y) hz
  have h := hasSum_coefficient_convolution hg hb
  rw [show -(c - I * y) = -c + I * y by ring] at h
  rw [mul_comm ((1 - z) ^ (-c + I * y))]
  apply h.congr_fun
  intro n
  rw [dualHahn_coeff_convolution hab hac]
  rfl


/-- Charlier polynomials as Laguerre polynomials with a degree-dependent parameter,
`C_n(z; a) = (-1)ⁿ n! a⁻ⁿ L_n^{(z-n)}(a)`. Both sides are the Tricomi function
`U(-n, z - n + 1, a)` up to normalization. -/
theorem charlier_eq_laguerrePolyL {a : ℂ} (ha : a ≠ 0) (n : ℕ) (z : ℂ)
    (hz : ∀ k : ℕ, z - n + 1 ≠ -k) :
    charlier a n z = (-1 : ℂ) ^ n * n.factorial / a ^ n * laguerrePolyL (z - n) n a := by
  have h1 := (kummerU_charlier n z a ha hz).2
  have h2 := (kummerU_laguerrePolyL n (z - n) a hz).2
  rw [h1] at h2
  have han : a ^ n ≠ 0 := pow_ne_zero n ha
  field_simp
  linear_combination h2

end DLMF.OrthogonalPolynomials
