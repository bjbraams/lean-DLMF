/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Series
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Bernoulli and Euler numbers and polynomials: inequalities (DLMF §24.9)

Real `x`. DLMF §24.9.p1: the inequalities hold for `n = 1, 2, …` except where noted
(24.9.3–24.9.5 for `0 < x < 1/2`; 24.9.4, 24.9.6, 24.9.7 for `n ≥ 2`). The constant
`β = 2 + ln(1 - 6/π²)/ln 2` of 24.9.9 is `bernoulliIneqBeta`; its decimal value `0.6491…` is
numerical and not acquired. All inequalities were checked numerically (mpmath, 30 digits, on
grids of `x` and for `n < 60`).
-/

@[expose] public section

noncomputable section

open Real Finset Filter Topology
open scoped Nat Real

namespace DLMF.BernoulliEuler

/-- **DLMF 24.9.1**: `|B₂ₙ| > |B₂ₙ(x)|` for `0 < x < 1`, `n ≥ 1`. -/
@[dlmf 24.9.E1]
theorem abs_bernoulliFun_two_mul_lt {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    |bernoulliFun (2 * n) x| < |(bernoulli (2 * n) : ℝ)| := by
  have hn0 : n ≠ 0 := by omega
  have hc := hasSum_one_div_nat_pow_mul_cos hn0 (x := x) ⟨hx0.le, hx1.le⟩
  have h1 := hasSum_one_div_nat_pow_mul_cos hn0 (x := 0) ⟨le_rfl, zero_le_one⟩
  simp only [mul_zero, Real.cos_zero, mul_one, Polynomial.eval_zero_map,
    Polynomial.bernoulli_eval_zero, eq_ratCast] at h1
  set K : ℝ := (-1 : ℝ) ^ (n + 1) * (2 * π) ^ (2 * n) / 2 / (2 * n)!
  have hK : K ≠ 0 := by
    simp only [K]
    have : (0 : ℝ) < (2 * π) ^ (2 * n) / 2 / (2 * n)! := by positivity
    rw [mul_div_assoc, mul_div_assoc]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact this.ne'
  have ha0 : ∀ m : ℕ, 0 ≤ 1 / (m : ℝ) ^ (2 * n) := fun m => by positivity
  have hcos1 : Real.cos (2 * π * ((1 : ℕ) : ℝ) * x) < 1 := by
    rw [Nat.cast_one, mul_one]
    refine lt_of_le_of_ne (Real.cos_le_one _) fun h => ?_
    rw [Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
      at h
    nlinarith [Real.pi_pos]
  have hup := hasSum_lt (f := fun m : ℕ => 1 / (m : ℝ) ^ (2 * n) * Real.cos (2 * π * m * x))
    (g := fun m : ℕ => 1 / (m : ℝ) ^ (2 * n)) (i := 1)
    (fun m => mul_le_of_le_one_right (ha0 m) (Real.cos_le_one _))
    (by rw [Nat.cast_one, one_pow, div_one, one_mul]; simpa using hcos1) hc h1
  have hlow : -(K * (bernoulli (2 * n) : ℝ)) <
      K * (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n))).eval x := by
    have hneg := h1.neg
    have hle : ∀ m : ℕ, -(1 / (m : ℝ) ^ (2 * n)) ≤ 1 / (m : ℝ) ^ (2 * n) *
        Real.cos (2 * π * m * x) := fun m => by
      have := Real.neg_one_le_cos (2 * π * m * x)
      nlinarith [ha0 m]
    by_cases hc1 : Real.cos (2 * π * x) = -1
    · refine hasSum_lt (i := 2) hle ?_ hneg hc
      have : Real.cos (2 * π * ((2 : ℕ) : ℝ) * x) = 1 := by
        rw [show 2 * π * ((2 : ℕ) : ℝ) * x = 2 * (2 * π * x) by push_cast; ring, Real.cos_two_mul,
          hc1]; norm_num
      rw [this, mul_one]
      have : (0 : ℝ) < 1 / ((2 : ℕ) : ℝ) ^ (2 * n) := by positivity
      linarith
    · refine hasSum_lt (i := 1) hle ?_ hneg hc
      simp only [Nat.cast_one, one_pow, div_one, one_mul, mul_one]
      exact lt_of_le_of_ne (Real.neg_one_le_cos _) (Ne.symm hc1) |> fun h => by linarith
  have habs : |K * bernoulliFun (2 * n) x| < |K * (bernoulli (2 * n) : ℝ)| := by
    have hpos : 0 < K * (bernoulli (2 * n) : ℝ) := by
      have := hasSum_lt (f := fun _ : ℕ => (0 : ℝ)) (i := 1) ha0
        (by simp) hasSum_zero h1
      exact this
    rw [abs_lt, abs_of_pos hpos]
    exact ⟨hlow, hup⟩
  rw [abs_mul, abs_mul] at habs
  exact lt_of_mul_lt_mul_left habs (abs_nonneg K)

/-! ### Signs and monotonicity on `[0, 1/2]` (helpers for 24.9.2–24.9.5) -/

/-- `(-1)ⁿ⁺¹ B₂ₙ = 2 (2n)!/(2π)^{2n} · ζ(2n)` with `ζ(2n)` the value of `∑ 1/m^{2n}`. -/
lemma r24a_bernoulli_eq_zeta {n : ℕ} (hn : n ≠ 0) :
    ∃ Z : ℝ, HasSum (fun m : ℕ => 1 / (m : ℝ) ^ (2 * n)) Z ∧
      (-1) ^ (n + 1) * (bernoulli (2 * n) : ℝ) = 2 * (2 * n)! / (2 * π) ^ (2 * n) * Z := by
  refine ⟨_, hasSum_zeta_nat hn, ?_⟩
  have e1 : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have e2 : (2 : ℝ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [mul_pow, e2]
  field_simp

/-- `|sin(mθ)| ≤ m |sin θ|`. -/
lemma r24a_abs_sin_nat_mul_le (m : ℕ) (θ : ℝ) : |sin (m * θ)| ≤ m * |sin θ| := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    rw [add_mul, one_mul, sin_add]
    calc |sin (m * θ) * cos θ + cos (m * θ) * sin θ|
        ≤ |sin (m * θ)| * |cos θ| + |cos (m * θ)| * |sin θ| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |sin (m * θ)| * 1 + 1 * |sin θ| := by
          gcongr
          · exact abs_cos_le_one _
          · exact abs_cos_le_one _
      _ ≤ (m + 1) * |sin θ| := by linarith

/-- `∑ 1/m^{2n} ≤ π²/6` for `n ≥ 1`. -/
lemma r24a_zeta_le {n : ℕ} (hn : 1 ≤ n) {Z : ℝ}
    (hz : HasSum (fun m : ℕ => 1 / (m : ℝ) ^ (2 * n)) Z) : Z ≤ π ^ 2 / 6 := by
  refine hasSum_le (fun m => ?_) hz hasSum_zeta_two
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [show 2 * n ≠ 0 by omega]
  · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    gcongr
    omega

/-- Sign of the odd Bernoulli polynomials: `(-1)ⁿ⁺¹ B₂ₙ₊₁(x) > 0` for `0 < x < 1/2`, `n ≥ 1`
(from the Fourier series and `|sin mθ| ≤ m sin θ`). -/
lemma r24a_bernoulliFun_odd_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    0 < (-1) ^ (n + 1) * bernoulliFun (2 * n + 1) x := by
  have hn0 : n ≠ 0 := by omega
  have hs := hasSum_one_div_nat_pow_mul_sin hn0 (x := x) ⟨hx0.le, by linarith⟩
  set C : ℝ := (-1 : ℝ) ^ (n + 1) * (2 * π) ^ (2 * n + 1) / 2 / (2 * n + 1)!
  set u := sin (2 * π * x)
  have hu : 0 < u := sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])
  have hz := hasSum_zeta_nat hn0
  set Z := (-1 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n - 1) * π ^ (2 * n) * bernoulli (2 * n) / (2 * n)!
  have hZ := r24a_zeta_le hn hz
  have hpi := pi_lt_d2
  have hZ2 : Z < 2 := by nlinarith [pi_pos]
  have hg : HasSum (fun m : ℕ => u * (2 * (if m = 1 then 1 else 0) - 1 / (m : ℝ) ^ (2 * n)))
      (u * (2 * 1 - Z)) := ((((hasSum_ite_eq 1 (1 : ℝ)).mul_left 2).sub hz).mul_left u)
  have hle := hasSum_le (fun m => ?_) hg hs
  · have hS : 0 < (C * (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n + 1))).eval x)
      := lt_of_lt_of_le (by nlinarith) hle
    change 0 < C * bernoulliFun (2 * n + 1) x at hS
    have hC : C = (-1) ^ (n + 1) * ((2 * π) ^ (2 * n + 1) / 2 / (2 * n + 1)!) := by
      simp only [C]; ring
    have hpos : 0 < (2 * π) ^ (2 * n + 1) / 2 / (2 * n + 1)! := by positivity
    rw [hC, mul_assoc, mul_comm, mul_assoc] at hS
    exact pos_of_mul_pos_right hS hpos.le |> fun h => by
      linarith [mul_comm ((-1 : ℝ) ^ (n + 1)) (bernoulliFun (2 * n + 1) x)]
  · rcases eq_or_ne m 1 with rfl | hm1
    · simp [u]; linarith
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [hn0]
    simp only [hm1, ite_false, mul_zero, zero_sub]
    have hm : (0 : ℝ) < m := by exact_mod_cast hm0
    have hb := r24a_abs_sin_nat_mul_le m (2 * π * x)
    rw [abs_of_pos hu, show (m : ℝ) * (2 * π * x) = 2 * π * m * x by ring] at hb
    have hb' := neg_abs_le (sin (2 * π * m * x))
    have e : u * -(1 / (m : ℝ) ^ (2 * n)) = 1 / (m : ℝ) ^ (2 * n + 1) * (-(m * u)) := by
      field_simp; ring
    rw [e]
    gcongr
    linarith


/-- Odd part of `ζ(2n)`: `∑ 1/(2k+1)^{2n} = ζ(2n)(1 - 4⁻ⁿ)`, and `η(2n) = ζ(2n)(1 - 2·4⁻ⁿ) ≤ 1`. -/
lemma r24a_zeta_odd {n : ℕ} (hn : 1 ≤ n) {Z : ℝ}
    (hz : HasSum (fun m : ℕ => 1 / (m : ℝ) ^ (2 * n)) Z) :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ (2 * n)) (Z - Z / 4 ^ n) ∧
      Z - 2 * (Z / 4 ^ n) ≤ 1 := by
  set f : ℕ → ℝ := fun m => 1 / (m : ℝ) ^ (2 * n) with hf
  have hev : HasSum (fun k : ℕ => f (2 * k)) (Z / 4 ^ n) := by
    refine (hz.div_const (4 ^ n)).congr_fun fun k => ?_
    simp only [f]; push_cast; rw [mul_pow, pow_mul]; norm_num; ring
  have hinj : StrictMono (fun k : ℕ => 2 * k + 1) := fun a b h => by dsimp; omega
  obtain ⟨b, hb⟩ := hz.summable.comp_injective hinj.injective
  have hZ := hz.unique (HasSum.even_add_odd (f := f) hev hb)
  have hb' : HasSum (fun k : ℕ => f (2 * k + 1)) (Z - Z / 4 ^ n) := by
    rw [show Z - Z / 4 ^ n = b by linarith]; exact hb
  refine ⟨hb'.congr_fun fun k => by simp [f], ?_⟩
  -- shifted comparison
  have h1 : HasSum (fun k : ℕ => f (2 * (k + 1) + 1)) (Z - Z / 4 ^ n - 1) := by
    have := (hasSum_nat_add_iff' (f := fun k : ℕ => f (2 * k + 1)) 1).mpr hb'
    simpa [f] using this
  have h2 : HasSum (fun k : ℕ => f (2 * (k + 1))) (Z / 4 ^ n) := by
    have := (hasSum_nat_add_iff' (f := fun k : ℕ => f (2 * k)) 1).mpr hev
    simpa [f, show 2 * n ≠ 0 by omega] using this
  have hle := hasSum_le (fun k => ?_) h1 h2
  · linarith
  · simp only [f]
    gcongr
    linarith

/-- Sign of the odd Euler polynomials: `(-1)ⁿ E₂ₙ₋₁(x) > 0` for `0 < x < 1/2`, `n ≥ 1`. -/
lemma r24a_eulerFun_odd_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    0 < (-1) ^ n * eulerFun (2 * n - 1) x := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    simp [eulerFun, Polynomial.euler_one]; linarith
  have hE := (hasSum_cos_odd_eulerFun hn (x := x) hx0.le (by linarith)).mul_left ((-1) ^ n)
  set K : ℝ := 4 * (2 * n - 1)! / π ^ (2 * n)
  have hK : 0 < K := by positivity
  have h1 : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hE' : HasSum (fun k : ℕ => K * (cos ((2 * k + 1) * π * x) / (2 * k + 1) ^ (2 * n)))
      ((-1) ^ n * eulerFun (2 * n - 1) x) := by
    refine hE.congr_fun fun k => ?_
    rw [← mul_assoc, ← mul_assoc, h1, one_mul]
  set v := cos (π * x)
  have hv : 0 < v := cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩
  -- `∑ 1/(2k+1)^{2n-1} < 2`
  have hsq := hasSum_zeta_two
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by simp at h; omega
  have hsumm : Summable (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ (2 * n - 1)) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (hsq.summable.comp_injective hinj)
    simp only [Function.comp]; push_cast
    have : (1 : ℝ) ≤ 2 * k + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    gcongr
    omega
  set W := ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ (2 * n - 1)
  have hW : W ≤ π ^ 2 / 6 := by
    refine hasSum_le_inj _ hinj (fun c _ => by positivity) (fun k => ?_) hsumm.hasSum hsq
    push_cast
    have : (1 : ℝ) ≤ 2 * k + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    gcongr
    omega
  have hpi := pi_lt_d2
  have hW2 : W < 2 := by nlinarith [pi_pos]
  have hg : HasSum (fun k : ℕ => K * (v * (2 * (if k = 0 then 1 else 0) -
      1 / (2 * (k : ℝ) + 1) ^ (2 * n - 1)))) (K * (v * (2 * 1 - W))) :=
    ((((hasSum_ite_eq 0 (1 : ℝ)).mul_left 2).sub hsumm.hasSum).mul_left v).mul_left K
  refine lt_of_lt_of_le (mul_pos hK (mul_pos hv (by linarith))) (hasSum_le (fun k => ?_) hg hE')
  gcongr
  rcases eq_or_ne k 0 with rfl | hk
  · norm_num [v]
  simp only [hk, ite_false, mul_zero, zero_sub]
  -- `|cos((2k+1)θ)| ≤ (2k+1) cos θ` via `φ = π/2 - θ`
  have hb := r24a_abs_sin_nat_mul_le (2 * k + 1) (π / 2 - π * x)
  have hcos : cos ((2 * k + 1) * π * x) = (-1) ^ k * sin ((2 * k + 1 : ℕ) * (π / 2 - π * x)) := by
    rw [show ((2 * k + 1 : ℕ) : ℝ) * (π / 2 - π * x) = -((2 * k + 1) * π * x) + k * π + π / 2 by
      push_cast; ring, sin_add_pi_div_two, cos_add_nat_mul_pi, cos_neg]
    rw [← mul_assoc, ← mul_pow]; norm_num
  rw [sin_pi_div_two_sub, abs_of_pos hv] at hb
  have habs : |cos ((2 * k + 1) * π * x)| ≤ (2 * k + 1) * v := by
    rw [hcos, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; push_cast at hb ⊢; exact hb
  have hb' := neg_abs_le (cos ((2 * k + 1) * π * x))
  have hk0 : (0 : ℝ) < 2 * k + 1 := by positivity
  have e : v * -(1 / (2 * (k : ℝ) + 1) ^ (2 * n - 1)) =
      -((2 * k + 1) * v) / (2 * k + 1) ^ (2 * n) := by
    rw [show 2 * n = (2 * n - 1) + 1 by omega, pow_succ]; field_simp
    rw [show 2 * n - 1 + 1 - 1 = 2 * n - 1 by omega]
  rw [e]
  gcongr
  linarith


/-- Strict monotonicity on `[0, 1/2]` from a positive derivative on `(0, 1/2)`. -/
lemma r24a_strictMonoOn_half {f f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), 0 < f' x) : StrictMonoOn f (Set.Icc 0 (1 / 2)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun x _ => (hd x).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hd x).deriv]; exact hpos x hx

/-- `E₂ₙ(0) = 0` for `n ≥ 1`. -/
lemma r24a_eulerFun_two_mul_zero {n : ℕ} (hn : 1 ≤ n) : eulerFun (2 * n) 0 = 0 := by
  have h1 := Polynomial.euler_eval_one_add_eval_zero (2 * n)
  have h2 := eulerFun_one_sub (2 * n) 0
  rw [zero_pow (by omega), mul_zero] at h1
  have h1' : eulerFun (2 * n) 1 + eulerFun (2 * n) 0 = 0 := by
    simp only [eulerFun, Polynomial.eval_one_map, Polynomial.eval_zero_map, eq_ratCast]
    exact_mod_cast h1
  rw [sub_zero, pow_mul] at h2; norm_num at h2
  linarith


/-- `(-1)ⁿ B₂ₙ₋₁(x) > 0` for `0 < x < 1/2`, `n ≥ 1`. -/
lemma r24a_bernoulliFun_odd_pos' {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    0 < (-1) ^ n * bernoulliFun (2 * n - 1) x := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    simp [bernoulliFun_one]; linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
  exact r24a_bernoulliFun_odd_pos (by omega) hx0 hx1

/-- `eulerFun n (1/2) = Eₙ / 2ⁿ`. -/
lemma r24a_eulerFun_half (n : ℕ) : eulerFun n (1 / 2) = eulerNumber n / 2 ^ n := by
  have h := eulerPolyE_half n
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, eulerPolyE_ofReal] at h
  exact_mod_cast h

/-- **DLMF 24.9.2**: `(2 - 2^{1-2n})|B₂ₙ| ≥ |B₂ₙ(x) - B₂ₙ|` for `0 ≤ x ≤ 1`, `n ≥ 1`. -/
@[dlmf 24.9.E2]
theorem abs_bernoulliFun_two_mul_sub_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    |bernoulliFun (2 * n) x - bernoulli (2 * n)| ≤
      (2 - (2 : ℝ) ^ (1 - 2 * (n : ℤ))) * |(bernoulli (2 * n) : ℝ)| := by
  -- reduce to `x ≤ 1/2`
  wlog hx : x ≤ 1 / 2 generalizing x
  · have := this (x := 1 - x) (by linarith) (by linarith) (by linarith)
    rwa [bernoulliFun_eval_one_sub, pow_mul, neg_one_sq, one_pow, one_mul] at this
  set f : ℝ → ℝ := fun y => (-1) ^ n * bernoulliFun (2 * n) y
  have hmono : StrictMonoOn f (Set.Icc 0 (1 / 2)) := by
    refine r24a_strictMonoOn_half
      (f' := fun y => (-1) ^ n * ((2 * n : ℕ) * bernoulliFun (2 * n - 1) y))
      (fun y => (hasDerivAt_bernoulliFun _ y).const_mul _) fun y hy => ?_
    have := r24a_bernoulliFun_odd_pos' hn hy.1 hy.2
    have h2n : (0 : ℝ) < (2 * n : ℕ) := by exact_mod_cast (show 0 < 2 * n by omega)
    nlinarith
  have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hx0, hx⟩
  have h0 : f 0 ≤ f x := hmono.monotoneOn ⟨le_rfl, by norm_num⟩ hx' hx0
  have h12 : f x ≤ f (1 / 2) := hmono.monotoneOn hx' ⟨by norm_num, le_rfl⟩ hx
  simp only [f, bernoulliFun_eval_zero, one_div, bernoulliFun_eval_half] at h0 h12
  -- sign of `B₂ₙ`
  obtain ⟨Z, hz, hA⟩ := r24a_bernoulli_eq_zeta (n := n) (by omega)
  have hZ : 0 < Z := by
    have := le_hasSum hz 1 (fun _ _ => by positivity)
    norm_num at this; linarith
  have hb : 0 < (-1) ^ (n + 1) * (bernoulli (2 * n) : ℝ) := by rw [hA]; positivity
  set B := (bernoulli (2 * n) : ℝ)
  have hsgn : (-1 : ℝ) ^ (n + 1) = -(-1) ^ n := by rw [pow_succ]; ring
  rw [hsgn] at hb
  have hs2 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hzp : (2 : ℝ) ^ (1 - 2 * (n : ℤ)) = 2 / 2 ^ (2 * n) := by
    rw [zpow_sub₀ (by norm_num), zpow_one]; norm_cast
  rw [hzp, abs_le]
  have hBabs : |B| = -((-1) ^ n * B) := by
    rw [show |B| = |(-1) ^ n * B| by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul],
      abs_of_neg (by linarith)]
  have hq : (0 : ℝ) < 2 / 2 ^ (2 * n) := by positivity
  have hq1 : 2 / (2 : ℝ) ^ (2 * n) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ 2 ≤ 2 ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  rw [hBabs]
  rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] at h0 h12 hb ⊢ <;> constructor <;>
    nlinarith [mul_pos hq hb]

/-- **DLMF 24.9.3**: `4⁻ⁿ|E₂ₙ| > (-1)ⁿ E₂ₙ(x) > 0` for `0 < x < 1/2`, `n ≥ 1`. -/
@[dlmf 24.9.E3]
theorem eulerFun_two_mul_bounds {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    0 < (-1) ^ n * eulerFun (2 * n) x ∧
      (-1) ^ n * eulerFun (2 * n) x < (4 : ℝ)⁻¹ ^ n * |(eulerNumber (2 * n) : ℝ)| := by
  set f : ℝ → ℝ := fun y => (-1) ^ n * eulerFun (2 * n) y
  have hmono : StrictMonoOn f (Set.Icc 0 (1 / 2)) := by
    refine r24a_strictMonoOn_half (f' := fun y => (-1) ^ n * ((2 * n : ℕ) * eulerFun (2 * n - 1) y))
      (fun y => (hasDerivAt_eulerFun _ y).const_mul _) fun y hy => ?_
    have := r24a_eulerFun_odd_pos hn hy.1 hy.2
    have h2n : (0 : ℝ) < (2 * n : ℕ) := by exact_mod_cast (show 0 < 2 * n by omega)
    nlinarith
  have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hx0.le, hx1.le⟩
  have h0 : f 0 < f x := hmono ⟨le_rfl, by norm_num⟩ hx' hx0
  have h12 : f x < f (1 / 2) := hmono hx' ⟨by norm_num, le_rfl⟩ hx1
  simp only [f, r24a_eulerFun_two_mul_zero hn, mul_zero, r24a_eulerFun_half] at h0 h12
  refine ⟨h0, h12.trans_le (le_of_eq ?_)⟩
  have hpos := (eulerNumber_two_mul_add_one_eq_zero_and_sign n).2
  have hpos' : (0 : ℝ) < (-1) ^ n * (eulerNumber (2 * n) : ℝ) := by exact_mod_cast hpos
  rw [show |(eulerNumber (2 * n) : ℝ)| = (-1) ^ n * eulerNumber (2 * n) by
    rw [← abs_of_pos hpos', abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]]
  rw [pow_mul, inv_pow]; norm_num; ring

/-- **DLMF 24.9.4**: `2(2n+1)!/(2π)^{2n+1} > (-1)ⁿ⁺¹ B₂ₙ₊₁(x) > 0` for `0 < x < 1/2`, `n ≥ 2`. -/
@[dlmf 24.9.E4]
theorem bernoulliFun_two_mul_add_one_bounds {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1 / 2) :
    0 < (-1) ^ (n + 1) * bernoulliFun (2 * n + 1) x ∧
      (-1) ^ (n + 1) * bernoulliFun (2 * n + 1) x < 2 * (2 * n + 1)! / (2 * π) ^ (2 * n + 1) := by
  sorry

/-- **DLMF 24.9.5**: `4(2n-1)!/π^{2n} (2^{2n} - 1)/(2^{2n} - 2) > (-1)ⁿ E₂ₙ₋₁(x) > 0` for
`0 < x < 1/2`, `n ≥ 1`. -/
@[dlmf 24.9.E5]
theorem eulerFun_two_mul_sub_one_bounds {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1 / 2) :
    0 < (-1) ^ n * eulerFun (2 * n - 1) x ∧
      (-1) ^ n * eulerFun (2 * n - 1) x <
        4 * (2 * n - 1)! / π ^ (2 * n) * ((2 ^ (2 * n) - 1) / (2 ^ (2 * n) - 2)) := by
  refine ⟨r24a_eulerFun_odd_pos hn hx0 hx1, ?_⟩
  have hE := (hasSum_cos_odd_eulerFun hn (x := x) hx0.le (by linarith)).mul_left ((-1) ^ n)
  set K : ℝ := 4 * (2 * n - 1)! / π ^ (2 * n)
  have hK : 0 < K := by positivity
  have h1 : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hE' : HasSum (fun k : ℕ => K * (cos ((2 * k + 1) * π * x) / (2 * k + 1) ^ (2 * n)))
      ((-1) ^ n * eulerFun (2 * n - 1) x) := by
    refine hE.congr_fun fun k => ?_
    rw [← mul_assoc, ← mul_assoc, h1, one_mul]
  have hz := hasSum_zeta_nat (k := n) (by omega)
  set Z := (-1 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n - 1) * π ^ (2 * n) * bernoulli (2 * n) / (2 * n)!
  obtain ⟨hodd, heta⟩ := r24a_zeta_odd hn hz
  have hlt := hasSum_lt (f := fun k : ℕ => K * (cos ((2 * k + 1) * π * x) / (2 * k + 1) ^ (2 * n)))
    (g := fun k : ℕ => K * (1 / (2 * (k : ℝ) + 1) ^ (2 * n))) (i := 0) (fun k => ?_) ?_ hE'
    (hodd.mul_left K)
  · have h4 : (0 : ℝ) < 4 ^ n := by positivity
    have h42 : (2 : ℝ) < 4 ^ n := by
      calc (2 : ℝ) < 4 ^ 1 := by norm_num
        _ ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hn
    rw [show (2 : ℝ) ^ (2 * n) = 4 ^ n by rw [pow_mul]; norm_num]
    refine hlt.trans_le ?_
    gcongr
    rw [le_div_iff₀ (by linarith)]
    have : Z * (4 ^ n - 2) ≤ 4 ^ n := by
      have := mul_le_mul_of_nonneg_left heta h4.le
      rw [show (4 : ℝ) ^ n * (Z - 2 * (Z / 4 ^ n)) = Z * (4 ^ n - 2) by field_simp] at this
      linarith
    have e : (Z - Z / 4 ^ n) * (4 ^ n - 2) = Z * (4 ^ n - 2) * (4 ^ n - 1) / 4 ^ n := by
      field_simp
    rw [e, div_le_iff₀ h4]
    nlinarith
  · simp only
    gcongr
    exact cos_le_one _
  · simp only [Nat.cast_zero, mul_zero, zero_add, one_mul, one_pow, div_one]
    gcongr
    refine lt_of_le_of_ne (cos_le_one _) fun h => ?_
    rw [Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith [pi_pos]) (by nlinarith [pi_pos])] at h
    nlinarith [pi_pos]

/-! ### Stirling bounds (helpers for 24.9.6–24.9.7) -/

/-- Upper bound from Robbins' stepwise bound: `log s(N) - log √π ≤ 1/(12N)`, `N ≥ 1`. -/
lemma r24a_log_stirlingSeq_le {N : ℕ} (hN : 1 ≤ N) :
    log (Stirling.stirlingSeq N) - log √π ≤ 1 / (12 * N) := by
  have hstep : ∀ M : ℕ, log (Stirling.stirlingSeq N) - log (Stirling.stirlingSeq (N + M)) ≤
      1 / (12 * N) - 1 / (12 * ((N + M : ℕ) : ℝ)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have h := Stirling.log_stirlingSeq_sdiff_le (N + M)
      have hk : (0 : ℝ) < ((N + M : ℕ) : ℝ) := by exact_mod_cast (show 0 < N + M by omega)
      have e : 1 / (12 * ((N + M : ℕ) : ℝ) * (((N + M : ℕ) : ℝ) + 1)) =
          1 / (12 * ((N + M : ℕ) : ℝ)) - 1 / (12 * ((N + M + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp; ring
      rw [e] at h
      show log (Stirling.stirlingSeq N) - log (Stirling.stirlingSeq (N + M + 1)) ≤
        1 / (12 * N) - 1 / (12 * ((N + M + 1 : ℕ) : ℝ))
      linarith
  have hlim : Tendsto (fun M : ℕ => log (Stirling.stirlingSeq (N + M))) atTop (𝓝 (log √π)) :=
    ((Real.continuousAt_log (by positivity)).tendsto).comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp
        (tendsto_atTop_mono (fun M => Nat.le_add_left M N) tendsto_id))
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine le_of_tendsto' (hlim.const_sub _) fun M => ?_
  have hp : 0 ≤ 1 / (12 * ((N + M : ℕ) : ℝ)) := by positivity
  linarith [hstep M]

/-- Lower bound from the first term of the Stirling difference series. -/
lemma r24a_log_stirlingSeq_ge {N : ℕ} (hN : 1 ≤ N) :
    1 / (3 * (2 * (N : ℝ) + 1) ^ 2) ≤ log (Stirling.stirlingSeq N) - log √π := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have h := Stirling.log_stirlingSeq_sdiff_hasSum m
  have h0 := le_hasSum h 0 (fun _ _ => by positivity)
  have hs : √π ≤ Stirling.stirlingSeq (m + 2) := Stirling.sqrt_pi_le_stirlingSeq (by omega)
  have hl : log √π ≤ log (Stirling.stirlingSeq (m + 2)) := log_le_log (by positivity) hs
  have e : (1 : ℝ) / (2 * ((0 + 1 : ℕ) : ℝ) + 1) * ((1 / (2 * ((m + 1 : ℕ) : ℝ) + 1)) ^ 2) ^ (0 + 1)
      = 1 / (3 * (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 2) := by
    push_cast; field_simp; ring
  rw [e] at h0
  linarith

/-- Two-sided Stirling bounds: `√π e^{1/(3(2N+1)²)} ≤ s(N) ≤ √π e^{1/(12N)}`, `N ≥ 1`. -/
lemma r24a_stirlingSeq_bounds {N : ℕ} (hN : 1 ≤ N) :
    √π * exp (1 / (3 * (2 * (N : ℝ) + 1) ^ 2)) ≤ Stirling.stirlingSeq N ∧
      Stirling.stirlingSeq N ≤ √π * exp (1 / (12 * N)) := by
  have hpos : 0 < Stirling.stirlingSeq N := by
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    exact Stirling.stirlingSeq'_pos m
  have hpi : 0 < √π := by positivity
  have h1 := r24a_log_stirlingSeq_ge hN
  have h2 := r24a_log_stirlingSeq_le hN
  constructor
  · rw [← le_div_iff₀' hpi, ← Real.le_log_iff_exp_le (by positivity), log_div hpos.ne' hpi.ne']
    exact h1
  · rw [← div_le_iff₀' hpi, ← Real.log_le_iff_le_exp (by positivity), log_div hpos.ne' hpi.ne']
    linarith

/-- `N! = s(N) √(2N) (N/e)^N`. -/
lemma r24a_factorial_eq (N : ℕ) (hN : 1 ≤ N) :
    (N ! : ℝ) = Stirling.stirlingSeq N * (√(2 * N) * (N / exp 1) ^ N) := by
  unfold Stirling.stirlingSeq
  have : 0 < √(2 * (N : ℝ)) * (N / exp 1) ^ N := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  field_simp


/-- `exp x ≤ 1 + 2x` for `0 < x ≤ 1/2`. -/
lemma r24a_exp_le_one_add_two_mul {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1 / 2) :
    exp x ≤ 1 + 2 * x := by
  have := Real.exp_bound_div_one_sub_of_interval' h0 (by linarith)
  have h2 : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- `(4n+1)² ≤ 9ⁿ` for `n ≥ 2`. -/
lemma r24a_sq_le_nine_pow {n : ℕ} (hn : 2 ≤ n) : (4 * n + 1) ^ 2 ≤ 9 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc (4 * (k + 1) + 1) ^ 2 ≤ 9 * (4 * k + 1) ^ 2 := by nlinarith
      _ ≤ 9 * 9 ^ k := Nat.mul_le_mul_left 9 ih
      _ = 9 ^ (k + 1) := by ring

/-- **DLMF 24.9.6**: `5√(πn) (n/(πe))^{2n} > (-1)ⁿ⁺¹ B₂ₙ > 4√(πn) (n/(πe))^{2n}`, `n ≥ 2`. -/
@[dlmf 24.9.E6]
theorem bernoulli_two_mul_stirling_bounds {n : ℕ} (hn : 2 ≤ n) :
    4 * √(π * n) * (n / (π * exp 1)) ^ (2 * n) < (-1) ^ (n + 1) * (bernoulli (2 * n) : ℝ) ∧
      (-1) ^ (n + 1) * (bernoulli (2 * n) : ℝ) < 5 * √(π * n) * (n / (π * exp 1)) ^ (2 * n) := by
  have hn0 : n ≠ 0 := by omega
  have hz := hasSum_zeta_nat hn0
  set Z := (-1 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n - 1) * π ^ (2 * n) * bernoulli (2 * n) / (2 * n)!
    with hZ
  -- bounds on `Z`
  have hZ1 : 1 < Z := by
    have := sum_le_hasSum ({1, 2} : Finset ℕ) (fun _ _ => by positivity) hz
    rw [sum_pair (by norm_num)] at this
    have : (0 : ℝ) < 1 / ((2 : ℕ) : ℝ) ^ (2 * n) := by positivity
    norm_num at *
    have : (0 : ℝ) < ((2 : ℝ) ^ (2 * n))⁻¹ := by positivity
    linarith
  have hZ2 : Z ≤ π ^ 4 / 90 := by
    refine hasSum_le (fun m => ?_) hz hasSum_zeta_four
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hn0]
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      gcongr; omega
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hZ3 : Z < 1.1 := by
    have : π ^ 4 < 3.15 ^ 4 := by gcongr
    norm_num at this; linarith
  -- Stirling
  have h2n : 1 ≤ 2 * n := by omega
  obtain ⟨hs1, hs2⟩ := r24a_stirlingSeq_bounds h2n
  have hf := r24a_factorial_eq (2 * n) h2n
  set s := Stirling.stirlingSeq (2 * n)
  have hsq : √(π * n) = √π * √n := Real.sqrt_mul hpi0.le _
  have hsq2 : √(2 * ((2 * n : ℕ) : ℝ)) = 2 * √n := by
    rw [show 2 * ((2 * n : ℕ) : ℝ) = 2 ^ 2 * n by push_cast; ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hA : (-1) ^ (n + 1) * (bernoulli (2 * n) : ℝ) =
      4 * Z * s * √n * (n / (π * exp 1)) ^ (2 * n) := by
    rw [hsq2] at hf
    have e1 : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    have e2 : (2 : ℝ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hZ, hf]
    push_cast
    rw [div_pow, div_pow, mul_pow, mul_pow, e2]
    have hs0 : s ≠ 0 := (lt_of_lt_of_le (by positivity) hs1).ne'
    have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hsn : √(n : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num
  have hP : 0 < (n / (π * exp 1)) ^ (2 * n) := by positivity
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hspi : 0 < √π := by positivity
  have hx : exp (1 / (12 * ((2 * n : ℕ) : ℝ))) ≤ 1 + 2 * (1 / (12 * ((2 * n : ℕ) : ℝ))) :=
    r24a_exp_le_one_add_two_mul (by positivity) (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith)
  have hx2 : 2 * (1 / (12 * ((2 * n : ℕ) : ℝ))) ≤ 1 / 24 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hs1' : √π ≤ s :=
    le_trans (le_mul_of_one_le_right hspi.le (Real.one_le_exp (by positivity))) hs1
  have hs2' : s ≤ √π * (25 / 24) := by
    refine hs2.trans ?_
    gcongr
    linarith
  rw [hA, hsq]
  constructor
  · have : √π < Z * s := by nlinarith
    have h4 : 0 < 4 * √n * (n / (π * exp 1)) ^ (2 * n) := by positivity
    nlinarith
  · have : Z * s < 5 / 4 * √π := by nlinarith
    have h4 : 0 < 4 * √n * (n / (π * exp 1)) ^ (2 * n) := by positivity
    nlinarith

/-- The constant `β = 2 + ln(1 - 6/π²)/ln 2` of DLMF 24.9.9 (exact definition; the decimal value
`0.6491…` is numerical and not acquired). -/
@[dlmf 24.9.E9]
def bernoulliIneqBeta : ℝ := 2 + log (1 - 6 / π ^ 2) / log 2

/-- **DLMF 24.9.8**: `2(2n)!/(2π)^{2n} · 1/(1 - 2^{β-2n}) ≥ (-1)ⁿ⁺¹ B₂ₙ
≥ 2(2n)!/(2π)^{2n} · 1/(1 - 2^{-2n})`, `n ≥ 1`, with `β` of 24.9.9. -/
@[dlmf 24.9.E8]
theorem bernoulli_two_mul_zeta_bounds {n : ℕ} (hn : 1 ≤ n) :
    2 * (2 * n)! / (2 * π) ^ (2 * n) * (1 / (1 - (2 : ℝ) ^ (-(2 * n : ℝ)))) ≤
        (-1) ^ (n + 1) * (bernoulli (2 * n) : ℝ) ∧
      (-1) ^ (n + 1) * (bernoulli (2 * n) : ℝ) ≤
        2 * (2 * n)! / (2 * π) ^ (2 * n) * (1 / (1 - (2 : ℝ) ^ (bernoulliIneqBeta - 2 * n))) := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨Z, hz, hA⟩ := r24a_bernoulli_eq_zeta hn0
  rw [hA]
  have hK : 0 < 2 * ((2 * n)! : ℝ) / (2 * π) ^ (2 * n) := by positivity
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have h41 : (1 : ℝ) < 4 ^ n := one_lt_pow₀ (by norm_num) hn0
  have hpow : (2 : ℝ) ^ (-(2 * n : ℝ)) = 1 / 4 ^ n := by
    rw [Real.rpow_neg (by norm_num), show (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]; norm_num
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  set c : ℝ := 1 - 6 / π ^ 2 with hc
  have hc0 : 0 < c := by
    rw [hc, sub_pos, div_lt_one (by positivity)]; nlinarith
  have hc1 : c < 1 := by
    have : 0 < 6 / π ^ 2 := by positivity
    linarith
  have hbeta : (2 : ℝ) ^ (bernoulliIneqBeta - 2 * n) = 4 * c / 4 ^ n := by
    rw [Real.rpow_sub (by norm_num), bernoulliIneqBeta, Real.rpow_add (by norm_num)]
    rw [show log (1 - 6 / π ^ 2) / log 2 = Real.logb 2 c from rfl, Real.rpow_logb (by norm_num)
      (by norm_num) hc0, show (2 * n : ℝ) = - -(2 * n : ℝ) by ring, Real.rpow_neg (by norm_num),
      hpow]
    norm_num
  rw [hpow, hbeta]
  -- odd part
  have hodd : 1 ≤ Z - Z / 4 ^ n := by
    have hev : HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ (2 * n)) (Z / 4 ^ n) := by
      refine (hz.div_const (4 ^ n)).congr_fun fun k => ?_
      push_cast; rw [mul_pow, pow_mul]; norm_num; ring
    have hinj : StrictMono (fun k : ℕ => 2 * k + 1) := fun a b h => by dsimp; omega
    obtain ⟨b, hb⟩ := hz.summable.comp_injective hinj.injective
    have hsum := HasSum.even_add_odd (f := fun m : ℕ => 1 / (m : ℝ) ^ (2 * n)) hev hb
    have hZ := hz.unique hsum
    have hb1 := le_hasSum hb 0 (fun j _ => by simp only [Function.comp]; positivity)
    simp at hb1
    linarith
  have hZ1 : 1 ≤ Z := by
    have : 0 ≤ Z / 4 ^ n := div_nonneg (hz.nonneg fun _ => by positivity) h4.le
    linarith
  constructor
  · gcongr
    rw [div_le_iff₀ (by rw [sub_pos]; exact div_lt_one h4 |>.mpr h41)]
    linarith [show Z * (1 - 1 / 4 ^ n) = Z - Z / 4 ^ n by ring]
  · gcongr
    have hden : 0 < 1 - 4 * c / 4 ^ n := by
      rw [sub_pos, div_lt_one h4]
      calc 4 * c < 4 := by linarith
        _ ≤ 4 ^ n := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hn
    rw [le_div_iff₀ hden]
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      have := hz.unique (by simpa using hasSum_zeta_two)
      rw [this, hc]; field_simp; ring_nf; rfl
    -- `Z - 1 ≤ 4 c / 4ⁿ` suffices
    suffices Z - 1 ≤ 4 * c / 4 ^ n by
      have : 4 * c / 4 ^ n ≤ Z * (4 * c / 4 ^ n) := le_mul_of_one_le_left (by positivity) hZ1
      nlinarith
    have hF := hz.update 1 0
    have hG := (hasSum_zeta_four.mul_left (16 / 4 ^ n)).update 1 0
    have hle := hasSum_le (fun m => ?_) hF hG
    · simp only [Nat.cast_one, one_pow, div_one] at hle
      have hp4 : π ^ 4 < 3.15 ^ 4 := by gcongr
      have hp2 : 3.14 ^ 2 < π ^ 2 := by gcongr
      have hc' : 0.39 < c := by
        rw [hc, lt_sub_comm, div_lt_iff₀ (by positivity)]; nlinarith
      have : 16 / 4 ^ n * (π ^ 4 / 90) - 16 / 4 ^ n ≤ 4 * c / 4 ^ n := by
        rw [show 16 / 4 ^ n * (π ^ 4 / 90) - 16 / 4 ^ n = (16 * (π ^ 4 / 90) - 16) / 4 ^ n by
          ring]
        gcongr
        norm_num at hp4
        nlinarith
      linarith
    · rcases eq_or_ne m 1 with rfl | hm1
      · simp
      rw [Function.update_of_ne hm1, Function.update_of_ne hm1]
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp [hn0]
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
      have hm4 : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
      rw [show 2 * n = 4 + 2 * (n - 2) by omega, pow_add, pow_mul,
        show (4 : ℝ) ^ n = 16 * 4 ^ (n - 2) by
          rw [show n = 2 + (n - 2) by omega, pow_add]; norm_num]
      have h' : (4 : ℝ) ^ (n - 2) ≤ ((m : ℝ) ^ 2) ^ (n - 2) := by
        gcongr; nlinarith
      have h40 : (0 : ℝ) < 4 ^ (n - 2) := by positivity
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

/-- **DLMF 24.9.10**: `4ⁿ⁺¹(2n)!/π^{2n+1} > (-1)ⁿ E₂ₙ > 4ⁿ⁺¹(2n)!/π^{2n+1} · 1/(1 + 3^{-1-2n})`,
`n ≥ 1`. -/
@[dlmf 24.9.E10]
theorem eulerNumber_two_mul_beta_bounds {n : ℕ} (hn : 1 ≤ n) :
    4 ^ (n + 1) * (2 * n)! / π ^ (2 * n + 1) * (1 / (1 + (3 : ℝ)⁻¹ ^ (2 * n + 1))) <
        (-1) ^ n * (eulerNumber (2 * n) : ℝ) ∧
      (-1) ^ n * (eulerNumber (2 * n) : ℝ) < 4 ^ (n + 1) * (2 * n)! / π ^ (2 * n + 1) := by
  obtain ⟨hl, hu⟩ := q24a_dirichletBeta_bounds (k := n) (by omega)
  set V := (-1) ^ n * (eulerNumber (2 * n) : ℝ) * π ^ (2 * n + 1) / (4 ^ (n + 1) * (2 * n)!)
  set K := 4 ^ (n + 1) * (2 * n)! / π ^ (2 * n + 1) with hKdef
  have hK : 0 < K := by positivity
  have hE : (-1) ^ n * (eulerNumber (2 * n) : ℝ) = K * V := by
    simp only [hKdef, V]; field_simp
  set u := (1 / 3 : ℝ) ^ (2 * n + 1)
  set v := (1 / 5 : ℝ) ^ (2 * n + 1)
  set w := (1 / 7 : ℝ) ^ (2 * n + 1)
  have hs : 3 ≤ 2 * n + 1 := by omega
  have hu0 : 0 < u := by positivity
  have hvu : v < u := by simp only [u, v]; gcongr; norm_num
  have hwv : w ≤ v := by simp only [w, v]; gcongr; norm_num
  -- `v - w > u²`: `(5/7)^s + (5/9)^s < 1` for `s ≥ 3`
  have hkey : u ^ 2 < v - w := by
    have e1 : w = v * (5 / 7 : ℝ) ^ (2 * n + 1) := by
      simp only [w, v]; rw [← mul_pow]; norm_num
    have e2 : u ^ 2 = v * (5 / 9 : ℝ) ^ (2 * n + 1) := by
      simp only [u, v]; rw [← pow_mul, mul_comm, pow_mul, ← mul_pow]; norm_num
    have b1 : (5 / 7 : ℝ) ^ (2 * n + 1) ≤ (5 / 7) ^ 3 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
    have b2 : (5 / 9 : ℝ) ^ (2 * n + 1) ≤ (5 / 9) ^ 3 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
    have hv0 : 0 < v := by positivity
    rw [e1, e2]
    nlinarith
  have h3inv : (3 : ℝ)⁻¹ ^ (2 * n + 1) = u := by simp only [u, one_div]
  rw [hE, h3inv]
  constructor
  · rw [mul_lt_mul_iff_right₀ hK, one_div, inv_lt_iff_one_lt_mul₀ (by positivity)]
    nlinarith
  · calc K * V ≤ K * (1 - u + v) := by gcongr
      _ < K * 1 := by gcongr; linarith
      _ = K := mul_one K

/-- **DLMF 24.9.7**: `8√(n/π) (4n/(πe))^{2n} (1 + 1/(12n)) > (-1)ⁿ E₂ₙ > 8√(n/π) (4n/(πe))^{2n}`,
`n ≥ 2`. -/
@[dlmf 24.9.E7]
theorem eulerNumber_two_mul_stirling_bounds {n : ℕ} (hn : 2 ≤ n) :
    8 * √(n / π) * (4 * n / (π * exp 1)) ^ (2 * n) < (-1) ^ n * (eulerNumber (2 * n) : ℝ) ∧
      (-1) ^ n * (eulerNumber (2 * n) : ℝ) <
        8 * √(n / π) * (4 * n / (π * exp 1)) ^ (2 * n) * (1 + 1 / (12 * n)) := by
  obtain ⟨hl, hu⟩ := eulerNumber_two_mul_beta_bounds (n := n) (by omega)
  have hpi0 := Real.pi_pos
  have h2n : 1 ≤ 2 * n := by omega
  obtain ⟨hs1, hs2⟩ := r24a_stirlingSeq_bounds h2n
  have hf := r24a_factorial_eq (2 * n) h2n
  set s := Stirling.stirlingSeq (2 * n)
  have hspi : 0 < √π := by positivity
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs1
  have hsq : √(n / π) = √n / √π := Real.sqrt_div' _ hpi0.le
  have hsq2 : √(2 * ((2 * n : ℕ) : ℝ)) = 2 * √n := by
    rw [show 2 * ((2 * n : ℕ) : ℝ) = 2 ^ 2 * n by push_cast; ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  set Q := 8 * √(n / π) * (4 * n / (π * exp 1)) ^ (2 * n) with hQ
  have hQ0 : 0 < Q := by positivity
  have hK : 4 ^ (n + 1) * ((2 * n)! : ℝ) / π ^ (2 * n + 1) = Q * (s / √π) := by
    rw [hf, hsq2, hQ, hsq]
    have hpi2 : π = √π ^ 2 := (Real.sq_sqrt hpi0.le).symm
    have hn0' : (n : ℝ) ≠ 0 := by positivity
    set d := √π with hd
    push_cast
    rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow, hpi2]
    field_simp
    rw [show (4 : ℝ) ^ (2 * n) = 4 ^ n * 4 ^ n by rw [two_mul, pow_add]]
    rw [show (2 : ℝ) ^ (2 * n) = 4 ^ n by rw [pow_mul]; norm_num]
    ring
  rw [hK] at hl hu
  constructor
  · -- `s/√π > 1 + 3^{-(2n+1)}`
    have hu3 : (3 : ℝ)⁻¹ ^ (2 * n + 1) ≤ 1 / (3 * (2 * ((2 * n : ℕ) : ℝ) + 1) ^ 2) := by
      have h9 := r24a_sq_le_nine_pow hn
      have h9' : ((4 * n + 1 : ℕ) : ℝ) ^ 2 ≤ ((9 ^ n : ℕ) : ℝ) := by exact_mod_cast h9
      rw [inv_pow, pow_succ, show (3 : ℝ) ^ (2 * n) = 9 ^ n by rw [pow_mul]; norm_num]
      rw [one_div, inv_le_inv₀ (by positivity) (by positivity)]
      push_cast at h9' ⊢
      nlinarith
    have hexp := Real.add_one_lt_exp (x := 1 / (3 * (2 * ((2 * n : ℕ) : ℝ) + 1) ^ 2))
      (by positivity)
    have hr : 1 + (3 : ℝ)⁻¹ ^ (2 * n + 1) < s / √π := by
      rw [lt_div_iff₀ hspi]; nlinarith
    calc Q = Q * (s / √π) * (1 / (s / √π)) := by field_simp
      _ < Q * (s / √π) * (1 / (1 + (3 : ℝ)⁻¹ ^ (2 * n + 1))) := by
          gcongr
      _ < _ := hl
  · have hx : exp (1 / (12 * ((2 * n : ℕ) : ℝ))) ≤ 1 + 2 * (1 / (12 * ((2 * n : ℕ) : ℝ))) :=
      r24a_exp_le_one_add_two_mul (by positivity) (by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith)
    have e : 1 + 2 * (1 / (12 * ((2 * n : ℕ) : ℝ))) = 1 + 1 / (12 * n) := by
      push_cast; field_simp
    have hr : s / √π ≤ 1 + 1 / (12 * n) := by
      rw [div_le_iff₀ hspi, ← e]; nlinarith
    calc _ < Q * (s / √π) := hu
      _ ≤ _ := by gcongr

end DLMF.BernoulliEuler
