/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.QFamilies.BasicIdentities

/-!
# Classical limits of q-orthogonal polynomials

Limits as q tends to one relate the basic hypergeometric families to their classical
counterparts.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.QFamilies`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter DLMF.QSeries

open scoped Real Nat Topology NNReal ENNReal

open DLMF.Hypergeometric

open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- `(1 - q^t)/(1 - q) → t` as `q → 1⁻`. -/
theorem tendsto_one_sub_rpow_div (t : ℝ) :
    Tendsto (fun q : ℝ => (1 - q ^ t) / (1 - q)) (𝓝[<] 1) (𝓝 t) := by
  have hd : HasDerivAt (fun q : ℝ => q ^ t) t 1 := by
    simpa using Real.hasDerivAt_rpow_const (x := 1) (p := t) (Or.inl one_ne_zero)
  have hs := hd.tendsto_slope.mono_left
    (nhdsWithin_mono (s := Set.Iio (1 : ℝ)) _ (fun q (hq : q < 1) => hq.ne))
  refine hs.congr' (eventually_nhdsWithin_of_forall fun q (hq : q < 1) => ?_)
  rw [slope_def_field, Real.one_rpow]
  have : q - 1 ≠ 0 := sub_ne_zero.mpr hq.ne
  have : 1 - q ≠ 0 := sub_ne_zero.mpr hq.ne'
  field_simp
  ring

/-- Eventually `0 < q` as `q → 1⁻`. -/
theorem eventually_pos_nhdsWithin_lt_one : ∀ᶠ q : ℝ in 𝓝[<] 1, 0 < q :=
  nhdsWithin_le_nhds (lt_mem_nhds one_pos)

/-- `(q^t;q)_k / (1-q)^k → (t)_k` as `q → 1⁻`. -/
theorem tendsto_qPochhammer_rpow_div (t : ℝ) (k : ℕ) :
    Tendsto (fun q : ℝ => qPochhammer ((q ^ t : ℝ) : ℂ) (q : ℂ) k / (1 - (q : ℂ)) ^ k)
      (𝓝[<] 1) (𝓝 (poch (t : ℂ) k)) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have hf : Tendsto (fun q : ℝ => (((1 - q ^ (t + k)) / (1 - q) : ℝ) : ℂ)) (𝓝[<] 1)
        (𝓝 ((t + k : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto _).comp (tendsto_one_sub_rpow_div (t + k))
    rw [poch_succ]
    refine ((ih.mul hf).congr' ?_).trans (by push_cast; rfl)
    filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
    have h1 : (1 : ℂ) - q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hq1))
    rw [qPochhammer_succ, pow_succ]
    have hrp : ((q ^ t : ℝ) : ℂ) * (q : ℂ) ^ k = ((q ^ (t + k) : ℝ) : ℂ) := by
      rw [Real.rpow_add hq, Real.rpow_natCast]; push_cast; ring
    rw [hrp]
    push_cast
    field_simp

/-- `q^a q^b = q^{a+b}` for real `q > 0`, after casting to `ℂ`. -/
lemma ofReal_rpow_eq_cpow_aux {q : ℝ} (hq : 0 < q) (a b : ℝ) :
    ((q ^ a : ℝ) : ℂ) * ((q ^ b : ℝ) : ℂ) = ((q ^ (a + b) : ℝ) : ℂ) := by
  rw [Real.rpow_add hq]; push_cast; ring

/-- A natural power of a real number, cast to `ℂ`, as a real power. -/
theorem ofReal_pow_eq_rpow {q : ℝ} (m : ℕ) : (q : ℂ) ^ m = ((q ^ (m : ℝ) : ℝ) : ℂ) := by
  rw [Real.rpow_natCast]; push_cast; ring

/-- `(1/q)^m = q^{-m}` for real `q > 0`, cast to `ℂ`. -/
theorem ofReal_recip_pow_eq_rpow {q : ℝ} (hq : 0 < q) (m : ℕ) :
    (q : ℂ)⁻¹ ^ m = ((q ^ (-(m : ℝ)) : ℝ) : ℂ) := by
  rw [Real.rpow_neg hq.le, Real.rpow_natCast]; push_cast; ring

/-- The ratio limit for the four `q`-Pochhammer symbols of a `₂φ₁`-type term. -/
theorem tendsto_qPoch_two_two (t₁ t₂ s₁ s₂ : ℝ) (k : ℕ) (hs₁ : poch (s₁ : ℂ) k ≠ 0)
    (hs₂ : poch (s₂ : ℂ) k ≠ 0) :
    Tendsto (fun q : ℝ => qPochhammer ((q ^ t₁ : ℝ) : ℂ) (q : ℂ) k *
        qPochhammer ((q ^ t₂ : ℝ) : ℂ) (q : ℂ) k /
        (qPochhammer ((q ^ s₁ : ℝ) : ℂ) (q : ℂ) k * qPochhammer ((q ^ s₂ : ℝ) : ℂ) (q : ℂ) k))
      (𝓝[<] 1) (𝓝 (poch (t₁ : ℂ) k * poch (t₂ : ℂ) k / (poch (s₁ : ℂ) k * poch (s₂ : ℂ) k))) := by
  have h := ((tendsto_qPochhammer_rpow_div t₁ k).mul (tendsto_qPochhammer_rpow_div t₂ k)).div
    ((tendsto_qPochhammer_rpow_div s₁ k).mul (tendsto_qPochhammer_rpow_div s₂ k))
    (mul_ne_zero hs₁ hs₂)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq1
  have h1 : ((1 : ℂ) - q) ^ k ≠ 0 := pow_ne_zero _ (by
    rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hq1)))
  simp only [Pi.div_apply]
  field_simp

/-- The cast `q ↦ (q : ℂ)` tends to `1` as `q → 1⁻`. -/
theorem tendsto_ofReal_nhdsWithin_lt_one :
    Tendsto (fun q : ℝ => (q : ℂ)) (𝓝[<] 1) (𝓝 1) := by
  simpa using (continuous_ofReal.tendsto (1 : ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))

/-- `(1 - q)^k ≠ 0` for real `q < 1`. -/
theorem one_sub_ofReal_pow_ne_zero {q : ℝ} (hq1 : q < 1) (k : ℕ) : ((1 : ℂ) - q) ^ k ≠ 0 :=
  pow_ne_zero _ (by
    rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hq1)))

/-- `q^{α+1}` as a complex power of a real `q > 0` equals the real power, cast. -/
theorem ofReal_cpow_add_one {q : ℝ} (hq : 0 < q) (α : ℝ) :
    (q : ℂ) ^ ((α : ℂ) + 1) = ((q ^ (α + 1) : ℝ) : ℂ) := by
  rw [ofReal_cpow hq.le]; push_cast; ring_nf

/-- `q^t → 1` as `q → 1⁻`, for every real `t`. -/
theorem tendsto_rpow_nhdsWithin_lt_one (t : ℝ) :
    Tendsto (fun q : ℝ => ((q ^ t : ℝ) : ℂ)) (𝓝[<] 1) (𝓝 1) := by
  have h : Tendsto (fun q : ℝ => q ^ t) (𝓝 1) (𝓝 ((1 : ℝ) ^ t)) :=
    (Real.continuousAt_rpow_const 1 t (Or.inl one_ne_zero)).tendsto
  rw [Real.one_rpow] at h
  have h2 := (continuous_ofReal.tendsto 1).comp (h.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1)))
  rw [ofReal_one] at h2
  exact h2

/-- The quadratic Askey–Wilson factor tends to the Wilson factor. -/
theorem tendsto_askeyWilson_prod (a : ℝ) (x : ℂ) (k : ℕ) :
    Tendsto (fun q : ℝ => (∏ j ∈ Finset.range k, (1 - 2 * ((q ^ a : ℝ) : ℂ) * (q : ℂ) ^ j *
        (1 - x * (1 - q : ℂ) ^ 2 / 2) + ((q ^ a : ℝ) : ℂ) ^ 2 * (q : ℂ) ^ (2 * j))) /
        ((1 - q : ℂ) ^ 2) ^ k) (𝓝[<] 1)
      (𝓝 (∏ j ∈ Finset.range k, (((a : ℂ) + j) ^ 2 + x))) := by
  have hfac : ∀ j : ℕ, Tendsto (fun q : ℝ => (1 - 2 * ((q ^ a : ℝ) : ℂ) * (q : ℂ) ^ j *
      (1 - x * (1 - q : ℂ) ^ 2 / 2) + ((q ^ a : ℝ) : ℂ) ^ 2 * (q : ℂ) ^ (2 * j)) /
      (1 - q : ℂ) ^ 2) (𝓝[<] 1) (𝓝 (((a : ℂ) + j) ^ 2 + x)) := by
    intro j
    have h1 : Tendsto (fun q : ℝ => (((1 - q ^ (a + j)) / (1 - q) : ℝ) : ℂ)) (𝓝[<] 1)
        (𝓝 ((a + j : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto _).comp (tendsto_one_sub_rpow_div (a + j))
    have h2 := (h1.pow 2).add ((tendsto_rpow_nhdsWithin_lt_one (a + j)).mul_const x)
    push_cast at h2
    rw [one_mul] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
    have h1q : (1 : ℂ) - q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hq1))
    have hr : ((q ^ (a + j) : ℝ) : ℂ) = ((q ^ a : ℝ) : ℂ) * (q : ℂ) ^ j := by
      rw [Real.rpow_add hq, Real.rpow_natCast]; push_cast; ring
    rw [hr]
    field_simp
    ring
  have h := tendsto_finsetProd (Finset.range k) fun j _ => hfac j
  refine h.congr' (Eventually.of_forall fun q => ?_)
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]

/-- The Wilson polynomial as a sum with the normalising Pochhammer products shifted into
the summand, valid when no `(a+b)_k`, `(a+c)_k`, `(a+d)_k` vanishes. -/
theorem wilson_eq_sum_shifted {a b c d : ℂ} (hab : ∀ k : ℕ, poch (a + b) k ≠ 0)
    (hac : ∀ k : ℕ, poch (a + c) k ≠ 0) (had : ∀ k : ℕ, poch (a + d) k ≠ 0) (n : ℕ) (x : ℂ) :
    wilson a b c d n x = ∑ k ∈ Finset.range (n + 1),
      poch (a + b + k) (n - k) * poch (a + c + k) (n - k) * poch (a + d + k) (n - k) *
        (poch (-(n : ℂ)) k * poch (n + a + b + c + d - 1) k / k.factorial *
          ∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) := by
  unfold wilson
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsplit : ∀ u : ℂ, poch u n = poch u k * poch (u + k) (n - k) := fun u => by
    rw [← poch_add, Nat.add_sub_cancel' hkn]
  rw [hsplit (a + b), hsplit (a + c), hsplit (a + d)]
  have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have := hab k; have := hac k; have := had k
  field_simp

/-- Field algebra used to rescale the Askey–Wilson summand. -/
theorem aw_algebra (A Q u F1 F2 F3 G1 G2 G3 P : ℂ) (n m k : ℕ) (h1 : u ≠ 0) :
    A⁻¹ ^ n * Q ^ k * (F1 / u ^ m) * (F2 / u ^ m) * (F3 / u ^ m) * (G1 / u ^ k) * (G2 / u ^ k) /
        (G3 / u ^ k) * (P / (u ^ 2) ^ k) =
    A⁻¹ ^ n * (Q ^ k * F1 * F2 * F3 * G1 * G2 / G3 * P) / ((u ^ m) ^ 3 * (u ^ k) ^ 3) := by
  field_simp
  ring

/-- `q² → 1⁻` as `q → 1⁻`. -/
theorem tendsto_sq_nhdsWithin_lt_one :
    Tendsto (fun q : ℝ => q ^ 2) (𝓝[<] 1) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun q : ℝ => q ^ 2) (𝓝 1) (𝓝 (1 ^ 2)) := (continuous_pow 2).tendsto 1
    rw [one_pow] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
    have hq1' : q < 1 := hq1
    show q ^ 2 < 1
    nlinarith

/-- `(q;q)_k / (1-q)^k → k!`. -/
theorem tendsto_qPochhammer_self_div (k : ℕ) :
    Tendsto (fun q : ℝ => qPochhammer (q : ℂ) (q : ℂ) k / (1 - (q : ℂ)) ^ k) (𝓝[<] 1)
      (𝓝 (k ! : ℂ)) := by
  have h := tendsto_qPochhammer_rpow_div 1 k
  push_cast at h
  rw [poch_nat_one] at h
  refine h.congr' (Eventually.of_forall fun q => ?_)
  simp [Real.rpow_one]

/-- `(q²;q²)_k / (1 - q²)^k → k!` as `q → 1⁻`. -/
theorem tendsto_qPochhammer_sq_div (k : ℕ) :
    Tendsto (fun q : ℝ => qPochhammer ((q : ℂ) ^ 2) ((q : ℂ) ^ 2) k / (1 - (q : ℂ) ^ 2) ^ k)
      (𝓝[<] 1) (𝓝 (k ! : ℂ)) := by
  have h := (tendsto_qPochhammer_self_div k).comp tendsto_sq_nhdsWithin_lt_one
  refine h.congr' (Eventually.of_forall fun q => ?_)
  simp

/-- Field algebra used to rescale the discrete `q`-Hermite summand. -/
theorem dqh_algebra (Pn Pm Gk A x u v s : ℂ) (m k : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) (hs : s ≠ 0)
    (hs2 : s ^ 2 = u * v) :
    Pn * (A * (s * x) ^ m / (Gk * Pm)) / s ^ (m + 2 * k) =
      Pn / u ^ (m + 2 * k) * A * x ^ m / (Gk / (u * v) ^ k * (Pm / u ^ m)) * (v⁻¹) ^ (2 * k) := by
  rw [inv_pow, pow_add s, pow_mul s, hs2]
  field_simp
  ring

/-- The map `(fun q : ℝ => qHahn (Real.rpow q α) (Real.rpow q β) q N n (Real.rpow q (-x)))` tends
to `(𝓝 (hahn α β N n x))` along `(𝓝[<] 1)`. -/
@[dlmf 18.27.E4_2]
theorem qHahn_limit_hahn {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {N n : ℕ} (hn : n ≤ N) (x : ℝ) :
    Tendsto (fun q : ℝ => qHahn (Real.rpow q α) (Real.rpow q β) q N n (Real.rpow q (-x))) (𝓝[<] 1) (𝓝 (hahn α β N n x)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  unfold qHahn hahn terminatingBasicHG terminatingHG
  refine tendsto_finsetSum _ fun k hk => ?_
  have hkN : k ≤ N := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hn
  have hs₁ : poch (((α + 1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; exact poch_ne_zero_of_not_neg_nat hα' k
  have hs₂ : poch ((-(N : ℝ) : ℝ) : ℂ) k ≠ 0 := by
    push_cast
    rw [poch_neg_coe_nat]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hkN).ne'
  have hs₃ : poch (((1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; rw [poch_nat_one]; exact Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hq := tendsto_ofReal_nhdsWithin_lt_one
  have h := (((tendsto_qPochhammer_rpow_div (-(n : ℝ)) k).mul
    (tendsto_qPochhammer_rpow_div (α + β + (n + 1 : ℕ)) k)).mul
    (tendsto_qPochhammer_rpow_div (-x) k)).div
    (((tendsto_qPochhammer_rpow_div (α + 1) k).mul (tendsto_qPochhammer_rpow_div (-(N : ℝ)) k)).mul
      (tendsto_qPochhammer_rpow_div 1 k))
    (mul_ne_zero (mul_ne_zero hs₁ hs₂) hs₃) |>.mul (hq.pow k)
  convert h.congr' ?_ using 2
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
    push_cast
    rw [poch_nat_one]
    ring_nf
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq0 hq1
    have h1 := one_sub_ofReal_pow_ne_zero (q := q) hq1 k
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil]
    rw [ofReal_recip_pow_eq_rpow hq0, ofReal_recip_pow_eq_rpow hq0,
      show (Real.rpow q α : ℂ) * (Real.rpow q β : ℂ) * (q : ℂ) ^ (n + 1)
      = ((q ^ (α + β + (n + 1 : ℕ)) : ℝ) : ℂ) by
        rw [ofReal_pow_eq_rpow, Real.rpow_eq_pow, Real.rpow_eq_pow, ofReal_rpow_eq_cpow_aux hq0,
          ofReal_rpow_eq_cpow_aux hq0],
      show (Real.rpow q α : ℂ) * (q : ℂ) = ((q ^ (α + 1) : ℝ) : ℂ) by
        rw [Real.rpow_eq_pow, ← ofReal_rpow_eq_cpow_aux hq0, Real.rpow_one],
      show qPochhammer (q : ℂ) (q : ℂ) k =
        qPochhammer ((q ^ (1 : ℝ) : ℝ) : ℂ) (q : ℂ) k by rw [Real.rpow_one]]
    simp only [Pi.div_apply, Real.rpow_eq_pow]
    norm_num
    field_simp
    simp

/-- The map `(fun q : ℝ => littleQJacobi (Real.rpow q α) (Real.rpow q β) q n x)` tends to `(𝓝
((n.factorial : ℂ) / poch (α + 1) n * jacobiPolyP α β n (1 - 2 * x)))` along `(𝓝[<] 1)`. -/
@[dlmf 18.27.E14_4]
theorem littleQJacobi_limit_jacobi {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => littleQJacobi (Real.rpow q α) (Real.rpow q β) q n x) (𝓝[<] 1)
        (𝓝 ((n.factorial : ℂ) / poch (α + 1) n * jacobiPolyP α β n (1 - 2 * x))) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hP := poch_ne_zero_of_not_neg_nat hα' n
  have hJ : (n.factorial : ℂ) / poch (α + 1) n * jacobiPolyP α β n (1 - 2 * x) =
      ∑ k ∈ Finset.range (n + 1), gaussHGCoeff (-(n : ℂ)) (n + α + β + 1) (α + 1) k * x ^ k := by
    unfold jacobiPolyP
    rw [show (1 - (1 - 2 * x)) / 2 = x by ring, ordinaryHypergeometric_eq_sum_neg_nat]
    have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  rw [hJ]
  unfold littleQJacobi terminatingBasicHG
  refine tendsto_finsetSum _ fun k _ => ?_
  have hs₁ : poch (((α + 1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; exact poch_ne_zero_of_not_neg_nat hα' k
  have hs₂ : poch (((1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; rw [poch_nat_one]; exact Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hx : Tendsto (fun q : ℝ => ((q : ℂ) * x) ^ k) (𝓝[<] 1) (𝓝 (x ^ k)) := by
    have : Tendsto (fun q : ℝ => (q : ℂ) * x) (𝓝[<] 1) (𝓝 x) := by
      have := ((continuous_ofReal.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))).mul_const x
      simpa using this
    exact this.pow k
  have h := (tendsto_qPoch_two_two (-(n : ℝ)) (α + β + (n + 1 : ℕ)) (α + 1) 1 k hs₁ hs₂).mul hx
  convert h.congr' ?_ using 2
  · rw [gaussHGCoeff]
    push_cast
    rw [poch_nat_one]
    ring_nf
  · filter_upwards [eventually_pos_nhdsWithin_lt_one] with q hq
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil]
    rw [ofReal_recip_pow_eq_rpow hq, show (Real.rpow q α : ℂ) * (Real.rpow q β : ℂ) * (q : ℂ) ^ (n + 1)
      = ((q ^ (α + β + (n + 1 : ℕ)) : ℝ) : ℂ) by
        rw [ofReal_pow_eq_rpow, Real.rpow_eq_pow, Real.rpow_eq_pow, ofReal_rpow_eq_cpow_aux hq,
          ofReal_rpow_eq_cpow_aux hq],
      show (Real.rpow q α : ℂ) * (q : ℂ) = ((q ^ (α + 1) : ℝ) : ℂ) by
        rw [Real.rpow_eq_pow, ← ofReal_rpow_eq_cpow_aux hq, Real.rpow_one]]
    conv_rhs => rw [show (q : ℂ) = ((q ^ (1 : ℝ) : ℝ) : ℂ) by rw [Real.rpow_one]]
    norm_num

/-- The map `(fun q : ℝ => littleQLaguerre (Real.rpow q α) q n ((1 - q : ℂ) * x))` tends to `(𝓝
((n.factorial : ℂ) / poch (α + 1) n * laguerrePolyL α n x))` along `(𝓝[<] 1)`. -/
@[dlmf 18.27.E14_6]
theorem littleQLaguerre_limit_laguerrePolyL {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => littleQLaguerre (Real.rpow q α) q n ((1 - q : ℂ) * x)) (𝓝[<] 1)
        (𝓝 ((n.factorial : ℂ) / poch (α + 1) n * laguerrePolyL α n x)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hP := poch_ne_zero_of_not_neg_nat hα' n
  have hL : (n.factorial : ℂ) / poch (α + 1) n * laguerrePolyL α n x =
      ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k / (poch (α + 1) k * k.factorial) * x ^ k := by
    unfold laguerrePolyL
    rw [kummerM_eq_sum_neg_nat]
    have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  rw [hL]
  unfold littleQLaguerre littleQJacobi terminatingBasicHG
  refine tendsto_finsetSum _ fun k _ => ?_
  have hs₁ : poch (((α + 1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; exact poch_ne_zero_of_not_neg_nat hα' k
  have hs₂ : poch (((1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; rw [poch_nat_one]; exact Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hx : Tendsto (fun q : ℝ => ((q : ℂ) * x) ^ k) (𝓝[<] 1) (𝓝 (x ^ k)) := by
    simpa using (tendsto_ofReal_nhdsWithin_lt_one.mul_const x).pow k
  have h := ((tendsto_qPochhammer_rpow_div (-(n : ℝ)) k).div
    ((tendsto_qPochhammer_rpow_div (α + 1) k).mul (tendsto_qPochhammer_rpow_div 1 k))
    (mul_ne_zero hs₁ hs₂)).mul hx
  convert h.congr' ?_ using 2
  · push_cast
    rw [poch_nat_one]
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
    have h1 := one_sub_ofReal_pow_ne_zero (q := q) hq1 k
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil, mul_zero, zero_mul, qPochhammer_zero_param]
    rw [ofReal_recip_pow_eq_rpow hq,
      show (Real.rpow q α : ℂ) * (q : ℂ) = ((q ^ (α + 1) : ℝ) : ℂ) by
        rw [Real.rpow_eq_pow, ← ofReal_rpow_eq_cpow_aux hq, Real.rpow_one]]
    conv_rhs => rw [show (q : ℂ) = ((q ^ (1 : ℝ) : ℝ) : ℂ) by rw [Real.rpow_one]]
    simp only [Pi.div_apply]
    norm_num
    field_simp
    simp only [mul_pow]
    ring

/-- The map `(fun q : ℝ => qLaguerre α q n ((1 - q : ℂ) * x))` tends to `(𝓝 (laguerrePolyL α n
x))` along `(𝓝[<] 1)`. -/
@[dlmf 18.27.E17_3]
theorem qLaguerre_limit_laguerrePolyL {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => qLaguerre α q n ((1 - q : ℂ) * x)) (𝓝[<] 1)
        (𝓝 (laguerrePolyL α n x)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hs : ∀ k : ℕ, poch (((α + 1 : ℝ)) : ℂ) k ≠ 0 := fun k => by
    push_cast; exact poch_ne_zero_of_not_neg_nat hα' k
  have h1s : ∀ k : ℕ, poch (((1 : ℝ)) : ℂ) k ≠ 0 := fun k => by
    push_cast; rw [poch_nat_one]; exact Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hL : laguerrePolyL α n x = poch (α + 1) n / n ! *
      ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k / (poch (α + 1) k * k.factorial) *
        ((-1) ^ k * (-x) ^ k) := by
    unfold laguerrePolyL
    rw [kummerM_eq_sum_neg_nat]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_pow]; ring_nf
  rw [hL]
  unfold qLaguerre terminatingBasicHG
  have hpre : Tendsto (fun q : ℝ => qPochhammer ((q : ℂ) ^ ((α : ℂ) + 1)) q n /
      qPochhammer (q : ℂ) q n) (𝓝[<] 1) (𝓝 (poch (α + 1) n / n !)) := by
    have h := (tendsto_qPochhammer_rpow_div (α + 1) n).div (tendsto_qPochhammer_rpow_div 1 n)
      (h1s n)
    convert h.congr' ?_ using 2
    · push_cast
      rw [poch_nat_one]
    · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
      have h1 := one_sub_ofReal_pow_ne_zero (q := q) hq1 n
      rw [ofReal_cpow_add_one hq, show qPochhammer (q : ℂ) (q : ℂ) n =
        qPochhammer ((q ^ (1 : ℝ) : ℝ) : ℂ) (q : ℂ) n by rw [Real.rpow_one]]
      simp only [Pi.div_apply]
      field_simp
  refine hpre.mul (tendsto_finsetSum _ fun k _ => ?_)
  have hq1 := tendsto_ofReal_nhdsWithin_lt_one
  have hpow : Tendsto (fun q : ℝ => (q : ℂ) ^ ((n : ℂ) + (α : ℂ) + 1)) (𝓝[<] 1) (𝓝 1) := by
    have hc : ContinuousAt (fun w : ℂ => w ^ ((n : ℂ) + (α : ℂ) + 1)) 1 :=
      continuousAt_id.cpow continuousAt_const (by simp)
    have h2 := hc.tendsto.comp hq1
    rw [one_cpow] at h2
    exact h2
  have hz : Tendsto (fun q : ℝ => ((-1 : ℂ) ^ k * (q : ℂ) ^ (k * (k - 1) / 2)) *
      (-x * (q : ℂ) ^ ((n : ℂ) + (α : ℂ) + 1)) ^ k) (𝓝[<] 1) (𝓝 ((-1) ^ k * (-x) ^ k)) := by
    have := ((hq1.pow (k * (k - 1) / 2)).const_mul ((-1 : ℂ) ^ k)).mul
      ((hpow.const_mul (-x)).pow k)
    simpa using this
  have h := ((tendsto_qPochhammer_rpow_div (-(n : ℝ)) k).div
    ((tendsto_qPochhammer_rpow_div (α + 1) k).mul (tendsto_qPochhammer_rpow_div 1 k))
    (mul_ne_zero (hs k) (h1s k))).mul hz
  convert h.congr' ?_ using 2
  · push_cast
    rw [poch_nat_one]
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
    have h1 := one_sub_ofReal_pow_ne_zero (q := q) hq1 k
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil]
    rw [ofReal_recip_pow_eq_rpow hq, ofReal_cpow_add_one hq, show qPochhammer (q : ℂ) (q : ℂ) k =
        qPochhammer ((q ^ (1 : ℝ) : ℝ) : ℂ) (q : ℂ) k by rw [Real.rpow_one]]
    simp only [Pi.div_apply]
    norm_num
    field_simp
    simp only [neg_pow (x * _), neg_pow ((1 - (q : ℂ)) * x * _), mul_pow]
    ring

/-- The map `(fun q : ℝ => askeyWilson (Real.rpow q a) (Real.rpow q b) (Real.rpow q c) (Real.rpow
q d) q n (1 - x * (1 - q : ℂ) ^ 2 / 2) / (1 - q : ℂ) ^ (3 * n))` tends to `(𝓝 (wilson a b c d
n x))` along `(𝓝[<] 1)`. -/
@[dlmf 18.28.E29]
theorem askeyWilson_limit_wilson {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => askeyWilson (Real.rpow q a) (Real.rpow q b) (Real.rpow q c) (Real.rpow q d) q n (1 - x * (1 - q : ℂ) ^ 2 / 2) / (1 - q : ℂ) ^ (3 * n)) (𝓝[<] 1) (𝓝 (wilson a b c d n x)) := by
  have hpos : ∀ (u : ℝ), 0 < u → ∀ k : ℕ, poch (u : ℂ) k ≠ 0 := fun u hu k =>
    poch_ne_zero_of_not_neg_nat (fun j h => by
      have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) k
  have hab : ∀ k : ℕ, poch ((a : ℂ) + b) k ≠ 0 := fun k => by
    have := hpos (a + b) (by linarith) k; push_cast at this; exact this
  have hac : ∀ k : ℕ, poch ((a : ℂ) + c) k ≠ 0 := fun k => by
    have := hpos (a + c) (by linarith) k; push_cast at this; exact this
  have had : ∀ k : ℕ, poch ((a : ℂ) + d) k ≠ 0 := fun k => by
    have := hpos (a + d) (by linarith) k; push_cast at this; exact this
  rw [wilson_eq_sum_shifted hab hac had]
  unfold askeyWilson
  simp_rw [Finset.mul_sum, Finset.sum_div]
  refine tendsto_finsetSum _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hk1 : poch ((1 : ℝ) : ℂ) k ≠ 0 := by
    push_cast; rw [poch_nat_one]; exact Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hq := tendsto_ofReal_nhdsWithin_lt_one
  have hA : Tendsto (fun q : ℝ => ((Real.rpow q a : ℝ) : ℂ)⁻¹ ^ n) (𝓝[<] 1) (𝓝 1) := by
    simpa using ((tendsto_rpow_nhdsWithin_lt_one a).inv₀ one_ne_zero).pow n
  have h := ((((((((hA.mul (hq.pow k)).mul
    (tendsto_qPochhammer_rpow_div (a + b + k) (n - k))).mul
    (tendsto_qPochhammer_rpow_div (a + c + k) (n - k))).mul
    (tendsto_qPochhammer_rpow_div (a + d + k) (n - k))).mul
    (tendsto_qPochhammer_rpow_div (-(n : ℝ)) k)).mul
    (tendsto_qPochhammer_rpow_div (a + b + c + d + ((n : ℝ) - 1)) k)).div
    (tendsto_qPochhammer_rpow_div 1 k) hk1).mul (tendsto_askeyWilson_prod a x k))
  convert h.congr' ?_ using 2
  · push_cast
    rw [poch_nat_one]
    generalize ∏ j ∈ Finset.range k, (((a : ℂ) + j) ^ 2 + x) = P
    ring_nf
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq0 hq1
    have h1 : (1 : ℂ) - q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hq1))
    have e3 : ((1 : ℂ) - q) ^ (3 * n) = (((1 : ℂ) - q) ^ (n - k)) ^ 3 * ((1 - q) ^ k) ^ 3 := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
    have cv2 : ∀ u v : ℝ, ((Real.rpow q u : ℝ) : ℂ) * ((Real.rpow q v : ℝ) : ℂ) * (q : ℂ) ^ k =
        ((q ^ (u + v + k) : ℝ) : ℂ) := fun u v => by
      rw [ofReal_pow_eq_rpow, Real.rpow_eq_pow, Real.rpow_eq_pow, ofReal_rpow_eq_cpow_aux hq0,
        ofReal_rpow_eq_cpow_aux hq0]
    have cv4 : ((Real.rpow q a : ℝ) : ℂ) * ((Real.rpow q b : ℝ) : ℂ) * ((Real.rpow q c : ℝ) : ℂ) *
        ((Real.rpow q d : ℝ) : ℂ) * (q : ℂ) ^ ((n : ℤ) - 1) =
        ((q ^ (a + b + c + d + ((n : ℝ) - 1)) : ℝ) : ℂ) := by
      have : (q : ℂ) ^ ((n : ℤ) - 1) = ((q ^ ((n : ℝ) - 1) : ℝ) : ℂ) := by
        rw [show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
        push_cast; ring
      rw [this, Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_eq_pow,
        ofReal_rpow_eq_cpow_aux hq0, ofReal_rpow_eq_cpow_aux hq0, ofReal_rpow_eq_cpow_aux hq0,
        ofReal_rpow_eq_cpow_aux hq0]
    rw [cv2 a b, cv2 a c, cv2 a d, cv4, ofReal_recip_pow_eq_rpow hq0,
      show qPochhammer (q : ℂ) (q : ℂ) k = qPochhammer ((q ^ (1 : ℝ) : ℝ) : ℂ) (q : ℂ) k by
        rw [Real.rpow_one], e3]
    simp only [Pi.div_apply, Real.rpow_eq_pow]
    exact aw_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ h1

/-- The map `(fun q : ℝ => qGegenbauer (Real.rpow q lam) q n (exp (I * θ)))` tends to `(𝓝
(ultrasphPoly lam n (Real.cos θ)))` along `(𝓝[<] 1)`. -/
@[dlmf 18.28.E31]
theorem qGegenbauer_limit_ultrasphPoly {lam : ℝ} (hlam : -1 / 2 < lam) (n : ℕ) (θ : ℝ) :
    Tendsto (fun q : ℝ => qGegenbauer (Real.rpow q lam) q n (exp (I * θ))) (𝓝[<] 1)
        (𝓝 (ultrasphPoly lam n (Real.cos θ))) := by
  let w : ℂ := exp (-I * θ)
  have hw : w ≠ 0 := exp_ne_zero _
  have hwi : w⁻¹ = exp (I * θ) := by
    dsimp [w]
    rw [← exp_neg]
    congr 1
    ring
  have hcos : (w + w⁻¹) / 2 = (Real.cos θ : ℂ) := by
    rw [hwi, ofReal_cos]
    dsimp [w]
    rw [Complex.cos]
    congr 1; ring
  rw [← hcos, ultrasphPoly_eq_coeff_gegenbauerSeries (by simpa using hlam) hw,
    coeff_gegenbauerSeries]
  unfold qGegenbauer
  refine tendsto_finsetSum _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (exp (I * θ)) ^ ((n : ℤ) - 2 * k) = w ^ k * w⁻¹ ^ (n - k) := by
    rw [← exp_int_mul, hwi]
    dsimp [w]
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
    congr 1
    push_cast [Nat.cast_sub hkn]
    ring
  have h := (((tendsto_qPochhammer_rpow_div lam k).mul
    (tendsto_qPochhammer_rpow_div lam (n - k))).div
    ((tendsto_qPochhammer_self_div k).mul (tendsto_qPochhammer_self_div (n - k)))
    (mul_ne_zero (Nat.cast_ne_zero.mpr k.factorial_ne_zero)
      (Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero))).mul_const
        ((exp (I * θ)) ^ ((n : ℤ) - 2 * k))
  rw [hpow] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hk0 := one_sub_ofReal_pow_ne_zero hq k
  have hnk0 := one_sub_ofReal_pow_ne_zero hq (n - k)
  simp only [Pi.div_apply]
  rw [hpow]
  field_simp
  simp only [Real.rpow_eq_pow]

/-- The map `(fun q : ℝ => discreteQHermiteI q n ((Real.sqrt (1 - q ^ 2) : ℂ) * x) / (Real.sqrt (1
- q ^ 2) : ℂ) ^ n)` tends to `(𝓝 ((2 : ℂ)⁻¹ ^ n * aeval x (hermitePolyH n)))` along `(𝓝[<]
1)`. -/
@[dlmf 18.27.E25]
theorem discreteQHermiteI_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => discreteQHermiteI q n ((Real.sqrt (1 - q ^ 2) : ℂ) * x) /
      (Real.sqrt (1 - q ^ 2) : ℂ) ^ n) (𝓝[<] 1) (𝓝 ((2 : ℂ)⁻¹ ^ n * aeval x (hermitePolyH n))) := by
  rw [hermitePolyH_finite_sum, Finset.mul_sum, Finset.mul_sum]
  unfold discreteQHermiteI
  simp_rw [Finset.mul_sum, Finset.sum_div]
  refine tendsto_finsetSum _ fun k hk => ?_
  have hk2 : 2 * k ≤ n := by
    have := Finset.mem_range.mp hk; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * k := ⟨n - 2 * k, by omega⟩
  rw [show m + 2 * k - 2 * k = m by omega]
  have hq := tendsto_ofReal_nhdsWithin_lt_one
  have hv : Tendsto (fun q : ℝ => ((1 + (q : ℂ))⁻¹) ^ (2 * k)) (𝓝[<] 1) (𝓝 ((2 : ℂ)⁻¹ ^ (2 * k))) := by
    have := ((hq.const_add 1).inv₀ (by norm_num)).pow (2 * k)
    norm_num at this ⊢
    exact this
  have hfk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hfm : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have h := (((((tendsto_qPochhammer_self_div (m + 2 * k)).mul
    ((hq.pow (k * (k - 1))).const_mul ((-1 : ℂ) ^ k))).mul_const (x ^ m)).div
    ((tendsto_qPochhammer_sq_div k).mul (tendsto_qPochhammer_self_div m))
    (mul_ne_zero hfk hfm)).mul hv)
  convert h.congr' ?_ using 2
  · rw [one_pow, mul_one, mul_pow, pow_add (2 : ℂ)⁻¹]
    simp only [inv_pow]
    field_simp
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq0 hq1
    have hq1' : q < 1 := hq1
    have hu : (1 : ℂ) - q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith)
    have hv0 : (1 : ℂ) + q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith)
    have hpos : 0 < 1 - q ^ 2 := by nlinarith
    have hs : ((Real.sqrt (1 - q ^ 2) : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
    have hs2 : ((Real.sqrt (1 - q ^ 2) : ℝ) : ℂ) ^ 2 = (1 - q) * (1 + q) := by
      rw [← ofReal_pow, Real.sq_sqrt hpos.le]; push_cast; ring
    have hq2 : (1 : ℂ) - (q : ℂ) ^ 2 = (1 - q) * (1 + q) := by ring
    simp only [Pi.div_apply]
    rw [hq2, dqh_algebra _ _ _ _ _ _ _ _ m k hu hv0 hs hs2]

/-- The map `(fun q : ℝ => discreteQHermiteII q n ((Real.sqrt (1 - q ^ 2) : ℂ) * x) / (Real.sqrt
(1 - q ^ 2) : ℂ) ^ n)` tends to `(𝓝 ((2 : ℂ)⁻¹ ^ n * aeval x (hermitePolyH n)))` along `(𝓝[<]
1)`. -/
@[dlmf 18.27.E26]
theorem discreteQHermiteII_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => discreteQHermiteII q n ((Real.sqrt (1 - q ^ 2) : ℂ) * x) /
      (Real.sqrt (1 - q ^ 2) : ℂ) ^ n) (𝓝[<] 1) (𝓝 ((2 : ℂ)⁻¹ ^ n * aeval x (hermitePolyH n))) := by
  rw [hermitePolyH_finite_sum, Finset.mul_sum, Finset.mul_sum]
  unfold discreteQHermiteII
  simp_rw [Finset.mul_sum, Finset.sum_div]
  refine tendsto_finsetSum _ fun k hk => ?_
  have hk2 : 2 * k ≤ n := by
    have := Finset.mem_range.mp hk; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * k := ⟨n - 2 * k, by omega⟩
  rw [show m + 2 * k - 2 * k = m by omega]
  have hq := tendsto_ofReal_nhdsWithin_lt_one
  have hv : Tendsto (fun q : ℝ => ((1 + (q : ℂ))⁻¹) ^ (2 * k)) (𝓝[<] 1) (𝓝 ((2 : ℂ)⁻¹ ^ (2 * k))) := by
    have := ((hq.const_add 1).inv₀ (by norm_num)).pow (2 * k)
    norm_num at this ⊢
    exact this
  have hfk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hfm : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have h := (((((tendsto_qPochhammer_self_div (m + 2 * k)).mul
    ((((hq.inv₀ one_ne_zero).pow (2 * (m + 2 * k) * k)).mul (hq.pow (k * (2 * k + 1)))).const_mul
      ((-1 : ℂ) ^ k))).mul_const (x ^ m)).div
    ((tendsto_qPochhammer_sq_div k).mul (tendsto_qPochhammer_self_div m))
    (mul_ne_zero hfk hfm)).mul hv)
  convert h.congr' ?_ using 2
  · rw [inv_one, one_pow, one_pow, mul_one, mul_one, mul_pow, pow_add (2 : ℂ)⁻¹]
    simp only [inv_pow]
    field_simp
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq0 hq1
    have hq1' : q < 1 := hq1
    have hu : (1 : ℂ) - q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith)
    have hv0 : (1 : ℂ) + q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith)
    have hpos : 0 < 1 - q ^ 2 := by nlinarith
    have hs : ((Real.sqrt (1 - q ^ 2) : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
    have hs2 : ((Real.sqrt (1 - q ^ 2) : ℝ) : ℂ) ^ 2 = (1 - q) * (1 + q) := by
      rw [← ofReal_pow, Real.sq_sqrt hpos.le]; push_cast; ring
    have hq2 : (1 : ℂ) - (q : ℂ) ^ 2 = (1 - q) * (1 + q) := by ring
    simp only [Pi.div_apply]
    rw [hq2, dqh_algebra _ _ _ _ _ _ _ _ m k hu hv0 hs hs2]
    ring

/-- The coefficient in the Askey–Wilson q-difference operator. -/
@[dlmf 18.28.E6_2]
def askeyWilsonDifferenceCoefficient (a b c d q z : ℂ) : ℂ :=
  (1 - a * z) * (1 - b * z) * (1 - c * z) * (1 - d * z) / ((1 - z ^ 2) * (1 - q * z ^ 2))

/-- The Askey–Wilson operator is triangular on the paired q-Pochhammer basis. -/
private lemma askeyWilson_basis_step {a b c d q z : ℂ} (hq : q ≠ 0) (hz : z ≠ 0)
    (hz1 : z^2 ≠ 1) (hzq : q*z^2 ≠ 1) (hzqi : q*z⁻¹^2 ≠ 1) (k : ℕ) :
    askeyWilsonDifferenceCoefficient a b c d q z *
      (qPochhammer (a*(q*z)) q (k+1)*qPochhammer (a/(q*z)) q (k+1) -
       qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) +
    askeyWilsonDifferenceCoefficient a b c d q z⁻¹ *
      (qPochhammer (a*(z/q)) q (k+1)*qPochhammer (a/(z/q)) q (k+1) -
       qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) =
    (q⁻¹^(k+1)-1)*(1-a*b*c*d*q^k)*
      (qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) -
    (q⁻¹^(k+1)-1)*(1-a*b*q^k)*(1-a*c*q^k)*(1-a*d*q^k)*
      (qPochhammer (a*z) q k*qPochhammer (a/z) q k) := by
  have hp : (1-a*z)*qPochhammer (a*(q*z)) q (k+1) =
      (1-a*z*q^(k+1))*qPochhammer (a*z) q (k+1) := by
    rw [show a*(q*z)=a*z*q by ring, ← qPochhammer_succ', qPochhammer_succ]
    ring
  have hm : (1-a/z)*qPochhammer (a/(z/q)) q (k+1) =
      (1-a/z*q^(k+1))*qPochhammer (a/z) q (k+1) := by
    rw [show a/(z/q)=a/z*q by field_simp,
      ← qPochhammer_succ', qPochhammer_succ]
    ring
  have hlow : qPochhammer (a/(q*z)) q (k+1) =
      (1-a/(q*z))*qPochhammer (a/z) q k := by
    rw [qPochhammer_succ', show a/(q*z)*q=a/z by field_simp]
  have hlow' : qPochhammer (a*(z/q)) q (k+1) =
      (1-a*(z/q))*qPochhammer (a*z) q k := by
    rw [qPochhammer_succ', show a*(z/q)*q=a*z by field_simp]
  have hz2 : 1-z^2 ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hzq2 : 1-q*z^2 ≠ 0 := sub_ne_zero.mpr hzq.symm
  have hzqi2 : 1-q*z⁻¹^2 ≠ 0 := sub_ne_zero.mpr hzqi.symm
  have hzInv : 1-z⁻¹^2 ≠ 0 := by
    rw [inv_pow, sub_ne_zero, ne_eq, eq_comm, inv_eq_one]
    exact hz1
  have hzq2' : 1-z^2*q ≠ 0 := by simpa [mul_comm] using hzq2
  have hzqi2' : z^2-q ≠ 0 := by
    intro h
    apply hzqi2
    rw [sub_eq_zero] at h
    rw [← h, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hz),sub_self]
  let Cplus := (1-b*z)*(1-c*z)*(1-d*z)/((1-z^2)*(1-q*z^2))
  let Cminus := (1-b/z)*(1-c/z)*(1-d/z)/((1-z⁻¹^2)*(1-q*z⁻¹^2))
  have hplus : askeyWilsonDifferenceCoefficient a b c d q z *
      (qPochhammer (a*(q*z)) q (k+1)*qPochhammer (a/(q*z)) q (k+1) -
       qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) =
      -(a*(1-q^(k+1))/q)*(1-a*z*q^k)*(1-b*z)*(1-c*z)*(1-d*z)/(z*(1-z^2))*
        (qPochhammer (a*z) q k*qPochhammer (a/z) q k) := by
    calc
      _ = Cplus * ((1-a*z)*qPochhammer (a*(q*z)) q (k+1)*
          qPochhammer (a/(q*z)) q (k+1) -
        (1-a*z)*qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) := by
          dsimp only [askeyWilsonDifferenceCoefficient,Cplus];ring
      _ = Cplus * ((1-a*z*q^(k+1))*qPochhammer (a*z) q (k+1)*
          ((1-a/(q*z))*qPochhammer (a/z) q k) -
        (1-a*z)*qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) := by
          rw [hp,hlow]
      _ = _ := by
        simp only [qPochhammer_succ, pow_succ q k]
        dsimp only [Cplus]
        generalize qPochhammer (a*z) q k = P
        generalize qPochhammer (a/z) q k = Q
        field_simp [hq,hz,hz2,hzq2,hzq2']
        ring
  have hminus : askeyWilsonDifferenceCoefficient a b c d q z⁻¹ *
      (qPochhammer (a*(z/q)) q (k+1)*qPochhammer (a/(z/q)) q (k+1) -
       qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) =
      -(a*(1-q^(k+1))/q)*(1-a/z*q^k)*(1-b/z)*(1-c/z)*(1-d/z)*z/(1-z⁻¹^2)*
        (qPochhammer (a*z) q k*qPochhammer (a/z) q k) := by
    calc
      _ = Cminus * ((1-a/z)*qPochhammer (a/(z/q)) q (k+1)*
          qPochhammer (a*(z/q)) q (k+1) -
        (1-a/z)*qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) := by
          simp only [askeyWilsonDifferenceCoefficient,div_eq_mul_inv,Cminus];ring
      _ = Cminus * ((1-a/z*q^(k+1))*qPochhammer (a/z) q (k+1)*
          ((1-a*(z/q))*qPochhammer (a*z) q k) -
        (1-a/z)*qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) := by
          rw [hm,hlow']
      _ = _ := by
        simp only [qPochhammer_succ, pow_succ q k]
        dsimp only [Cminus]
        generalize qPochhammer (a*z) q k = P
        generalize qPochhammer (a/z) q k = Q
        field_simp [hq,hz,hzInv,hzqi2,hzqi2']
        ring
  rw [hplus,hminus]
  simp only [qPochhammer_succ,inv_pow,pow_succ q k]
  generalize qPochhammer (a*z) q k = P
  generalize qPochhammer (a/z) q k = Q
  field_simp [hq,hz,hz2,hzInv]
  ring

/-- Identity under the stated parameter and domain assumptions: `askeyWilsonDifferenceCoefficient
a b c d q z * (askeyWilsonLaurent a b c d q n (q * z) - askeyWilsonLaurent a b c d q n z) +
askeyWilsonDifferenceCoefficient a b c d q z⁻¹ * (askeyWilsonLaurent a b c d q n (z / q) -
askeyWilsonLaurent a b c d q n z) = (q⁻¹ ^ n - 1) * (1 - a * b * c * d * q ^ ((n : ℤ) - 1)) *
askeyWilsonLaurent a b c d q n z`. -/
@[dlmf 18.28.E6_1]
theorem askeyWilson_difference_equation {a b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hab : ‖a * b‖ < 1) (hac : ‖a * c‖ < 1) (had : ‖a * d‖ < 1) (n : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hz1 : z ^ 2 ≠ 1) (hzq : q * z ^ 2 ≠ 1) (hzqi : q * z⁻¹ ^ 2 ≠ 1) :
    askeyWilsonDifferenceCoefficient a b c d q z *
      (askeyWilsonLaurent a b c d q n (q * z) - askeyWilsonLaurent a b c d q n z) +
    askeyWilsonDifferenceCoefficient a b c d q z⁻¹ *
      (askeyWilsonLaurent a b c d q n (z / q) - askeyWilsonLaurent a b c d q n z) =
    (q⁻¹ ^ n - 1) * (1 - a * b * c * d * q ^ ((n : ℤ) - 1)) * askeyWilsonLaurent a b c d q n z := by
  let P := a*b*c*d/q
  let c₀ (k : ℕ) := qPochhammer (q⁻¹^n) q k * qPochhammer (P*q^n) q k * q^k /
    (qPochhammer (a*b) q k*qPochhammer (a*c) q k*qPochhammer (a*d) q k*qPochhammer q q k)
  let e (k : ℕ) := (q⁻¹^k-1)*(1-P*q^k)
  let L (k : ℕ) := (q⁻¹^(k+1)-1)*(1-a*b*q^k)*(1-a*c*q^k)*(1-a*d*q^k)
  let B (k : ℕ) (w : ℂ) := qPochhammer (a*w) q k*qPochhammer (a/w) q k
  have hP (k : ℕ) : P*q^(k+1)=a*b*c*d*q^k := by
    dsimp only [P];rw [pow_succ];field_simp
  have hPn : a*b*c*d*q^((n:ℤ)-1)=P*q^n := by
    rw [zpow_sub₀ hq0,zpow_natCast,zpow_one];dsimp only [P];ring
  have hD (w : ℂ) (hw : ‖w‖ < 1) (k : ℕ) : qPochhammer w q k ≠ 0 :=
    qPochhammer_ne_zero_of_factors hq (one_sub_mul_pow_ne_zero_of_norm hw hq) k
  have hc (k : ℕ) : c₀ (k+1)*L k = (e k-e n)*c₀ k := by
    have hAk := hD (a*b) hab k
    have hBk := hD (a*c) hac k
    have hCk := hD (a*d) had k
    have hQk := qPochhammer_self_ne_zero hq k
    have hA1 := one_sub_mul_pow_ne_zero_of_norm hab hq k
    have hB1 := one_sub_mul_pow_ne_zero_of_norm hac hq k
    have hC1 := one_sub_mul_pow_ne_zero_of_norm had hq k
    have hQ1 := one_sub_mul_pow_ne_zero_of_norm hq hq k
    have hraw : c₀ (k+1)*((1-a*b*q^k)*(1-a*c*q^k)*(1-a*d*q^k)*(1-q*q^k)) =
        c₀ k*q*(1-q⁻¹^n*q^k)*(1-P*q^n*q^k) := by
      dsimp only [c₀]
      simp only [qPochhammer_succ]
      generalize qPochhammer (a*b) q k = A at hAk ⊢
      generalize qPochhammer (a*c) q k = B at hBk ⊢
      generalize qPochhammer (a*d) q k = C at hCk ⊢
      generalize qPochhammer q q k = F at hQk ⊢
      generalize 1-a*b*q^k = U at hA1 ⊢
      generalize 1-a*c*q^k = V at hB1 ⊢
      generalize 1-a*d*q^k = W at hC1 ⊢
      generalize 1-q*q^k = X at hQ1 ⊢
      rw [pow_succ q k]
      field_simp
    have hL : L k = ((1-a*b*q^k)*(1-a*c*q^k)*(1-a*d*q^k)*(1-q*q^k))/q^(k+1) := by
      dsimp only [L];simp only [inv_pow,pow_succ q k]
      field_simp
    rw [hL,←mul_div_assoc,hraw]
    dsimp only [e]
    simp only [inv_pow,pow_succ q k]
    field_simp
    ring
  let R (k : ℕ) := askeyWilsonDifferenceCoefficient a b c d q z*(B k (q*z)-B k z) +
    askeyWilsonDifferenceCoefficient a b c d q z⁻¹*(B k (z/q)-B k z)-e n*B k z
  let G (k : ℕ) := c₀ k*(e k-e n)*B k z
  have ht (k : ℕ) : c₀ (k+1)*R (k+1)=G (k+1)-G k := by
    have hb := askeyWilson_basis_step (a:=a) (b:=b) (c:=c) (d:=d) hq0 hz hz1 hzq hzqi k
    rw [← hP k] at hb
    change askeyWilsonDifferenceCoefficient a b c d q z*(B (k+1) (q*z)-B (k+1) z) +
      askeyWilsonDifferenceCoefficient a b c d q z⁻¹*(B (k+1) (z/q)-B (k+1) z) =
      e (k+1)*B (k+1) z-L k*B k z at hb
    dsimp only [R,G]
    rw [hb]
    linear_combination -(B k z)*hc k
  have hkey : ∑ k ∈ Finset.range (n+1),c₀ k*R k = 0 := by
    rw [Finset.sum_range_succ']
    rw [Finset.sum_congr rfl fun k _ => ht k,Finset.sum_range_sub]
    simp only [G,R,c₀,e,B,qPochhammer_zero,pow_zero,one_mul,sub_self,zero_mul,
      mul_zero,zero_sub,div_one]
    ring
  have hpoly (w : ℂ) : askeyWilsonLaurent a b c d q n w =
      ∑ k ∈ Finset.range (n+1),c₀ k*B k w := by
    unfold askeyWilsonLaurent terminatingBasicHG
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,List.length_cons,
      List.length_nil,mul_one]
    norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,
      show (1+(3:ℤ)-4)=0 by norm_num,zpow_zero,mul_one]
    rw [hPn]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [c₀,B]
    ring
  rw [hpoly,hpoly,hpoly,hPn]
  change _ = e n*∑ k ∈ Finset.range (n+1),c₀ k*B k z
  have he : ∑ k ∈ Finset.range (n+1),c₀ k*R k =
      askeyWilsonDifferenceCoefficient a b c d q z*
        ((∑ k ∈ Finset.range (n+1),c₀ k*B k (q*z))-∑ k ∈ Finset.range (n+1),c₀ k*B k z) +
      askeyWilsonDifferenceCoefficient a b c d q z⁻¹*
        ((∑ k ∈ Finset.range (n+1),c₀ k*B k (z/q))-∑ k ∈ Finset.range (n+1),c₀ k*B k z) -
      e n*∑ k ∈ Finset.range (n+1),c₀ k*B k z := by
    simp only [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [R]
    ring
  rw [hkey] at he
  exact sub_eq_zero.mp he.symm

/-- Leading asymptotic coefficient; its argument is on the unit circle. -/
@[dlmf 18.29.E2]
def askeyWilsonAsymptoticCoefficient (a b c d q z : ℂ) : ℂ :=
  qPochhammerInf (a / z) q * qPochhammerInf (b / z) q *
    qPochhammerInf (c / z) q * qPochhammerInf (d / z) q / qPochhammerInf (z⁻¹ ^ 2) q

/-- The map `(fun n : ℕ => askeyWilson a b c d q n (Real.cos θ) - (exp (I * n * θ) *
askeyWilsonAsymptoticCoefficient a b c d q (exp (I * θ)) + exp (-I * n * θ) *
askeyWilsonAsymptoticCoefficient a b c d q (exp (-I * θ))))` tends to `(𝓝 0)` along `atTop`. -/
@[dlmf 18.29.E1]
theorem askeyWilson_asymptotic {a b c d q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (ha0 : a ≠ 0) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) (hd : |d| < 1)
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Tendsto (fun n : ℕ => askeyWilson a b c d q n (Real.cos θ) -
      (exp (I * n * θ) * askeyWilsonAsymptoticCoefficient a b c d q (exp (I * θ)) +
       exp (-I * n * θ) * askeyWilsonAsymptoticCoefficient a b c d q (exp (-I * θ)))) atTop (𝓝 0) := by
  sorry

end DLMF.OrthogonalPolynomials

end
end
