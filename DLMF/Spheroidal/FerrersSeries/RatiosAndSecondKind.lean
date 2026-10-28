/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.FerrersSeries.RecurrencesAndConvergence

/-!
# Spheroidal coefficient ratios and second-kind series

Ratio asymptotics of the spheroidal coefficients and Ferrers expansions of the second kind.

Source references and common attribution are retained in
`DLMF.Spheroidal.FerrersSeries`.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics DLMF.Legendre MeasureTheory

open scoped Topology Real

namespace DLMF.Spheroidal

/-! #### Proof of the ratio asymptotics 30.8.7

For `γ² ≠ 0` the coefficients are not eventually zero (else backward recursion with `A_k ≠ 0`
and 30.8.1 would give `𝖯s = 0`); with `|a_{j+1}| ≤ (|a_j| + |a_{j+2}|)/8` and the linear bound
this forces `|a_{j+1}| ≤ |a_j|/4` eventually. -/

/-- `A_k ≠ 0` for `k > -R` when `γ² ≠ 0`. -/
lemma p2y_recA_ne_zero {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} (hγ : γ2 ≠ 0) {k : ℤ}
    (hk : -(((n - m) / 2 : ℕ) : ℤ) < k) : spheroidalRecA n m γ2 k ≠ 0 := by
  unfold spheroidalRecA
  have h1 : ((n : ℤ) - m + 2 * k - 1) ≠ 0 := by omega
  have h2 : ((n : ℤ) - m + 2 * k) ≠ 0 := by omega
  have h3 : (2 * (n : ℤ) + 4 * k - 3) ≠ 0 := by omega
  have h4 : (2 * (n : ℤ) + 4 * k - 1) ≠ 0 := by omega
  have h1' : ((n : ℝ) - m + 2 * k - 1) ≠ 0 := by exact_mod_cast h1
  have h2' : ((n : ℝ) - m + 2 * k) ≠ 0 := by exact_mod_cast h2
  have h3' : (2 * (n : ℝ) + 4 * k - 3) ≠ 0 := by exact_mod_cast h3
  have h4' : (2 * (n : ℝ) + 4 * k - 1) ≠ 0 := by exact_mod_cast h4
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hγ) (mul_ne_zero h1' h2'))
    (mul_ne_zero h3' h4')

/-- For `γ² ≠ 0` the coefficients `a^m_{n,k}`, `k ≥ -R`, are not eventually zero. -/
lemma p2y_coeff_not_eventually_zero {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} (hγ : γ2 ≠ 0) :
    ¬ ∃ J : ℕ, ∀ j : ℕ, J ≤ j → spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ)) = 0 := by
  rintro ⟨J, hJ⟩
  have hall : ∀ d j : ℕ, J ≤ j + d → spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ)) = 0 := by
    intro d
    induction d with
    | zero => intro j hj; exact hJ j (by omega)
    | succ d ih =>
      intro j _
      have h1 := ih (j + 1) (by omega)
      have h2 := ih (j + 2) (by omega)
      have hrec := spheroidalCoeff_recurrence_of_le hmn γ2
        (k := ((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ)) (by omega)
      simp only [show -(((n - m) / 2 : ℕ) : ℤ) ≤ ((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ) - 1 by
        omega, ↓reduceIte] at hrec
      rw [show ((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ) - 1 = (j : ℤ) - ((n - m) / 2 : ℕ) by
          push_cast; ring,
        show ((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ) + 1 = ((j + 2 : ℕ) : ℤ) - ((n - m) / 2 : ℕ) by
          push_cast; ring, h1, h2] at hrec
      simp only [mul_zero, add_zero] at hrec
      exact (mul_eq_zero.mp hrec).resolve_left (p2y_recA_ne_zero hmn hγ (by omega))
  have hz : ∀ j : ℕ, spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ)) = 0 :=
    fun j => hall J j (by omega)
  have hG : ∀ x ∈ Ioo (-1 : ℝ) 1, (spheroidalPsFactor n m γ2 x).re = 0 := by
    intro x hx
    have h := p2y_factor_expansion hmn γ2 x hx
    have h0 : ∀ j : ℕ, (2 * ((n - 2 * ((n - m) / 2) + 2 * j : ℕ) : ℝ) + 1) *
          ((n - 2 * ((n - m) / 2) + 2 * j - m).factorial : ℝ) /
          (2 * ((n - 2 * ((n - m) / 2) + 2 * j + m).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ m * (spheroidalPsFactor n m γ2 y).re *
          (legInt_D (n - 2 * ((n - m) / 2) + 2 * j) m y).re) = 0 := by
      intro j
      have := hz j
      rw [p2y_coeff_eq hmn γ2 j] at this
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (zpow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (by norm_num)))
    simp only [h0, zero_mul] at h
    exact h.unique hasSum_zero
  have hnorm := (spheroidalPsFactor_spec hmn γ2).normalized
  have h0 : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (spheroidalPsFactor n m γ2 x).re ^ 2 = 0 := by
    rw [p2y_integral_congr_Ioo (f₂ := fun _ => (0 : ℝ)) (fun x hx => by
      simp only [hG x hx]; ring)]
    simp
  rw [h0] at hnorm
  have : (0 : ℝ) < 2 / (2 * n + 1) * (((n + m).factorial : ℝ) / (n - m).factorial) := by
    positivity
  linarith

/-- Eventually `|a_{j+1}| ≤ |a_j|/4`. -/
lemma p2y_coeff_ratio_le {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      |spheroidalCoeff n m γ2 (((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ))| ≤
        |spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))| / 4 := by
  obtain ⟨J, hJ⟩ := p2y_coeff_eps hmn γ2 (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨M, hM0, hM⟩ := p2y_coeff_linear hmn γ2
  refine ⟨J, fun j0 hj0 => ?_⟩
  set a : ℕ → ℝ := fun j => |spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))| with ha
  change a (j0 + 1) ≤ a j0 / 4
  by_contra hcon
  push Not at hcon
  have key : ∀ i : ℕ, a (j0 + i) / 4 < a (j0 + i + 1) ∧ 4 ^ i * a (j0 + 1) ≤ a (j0 + i + 1) := by
    intro i
    induction i with
    | zero => exact ⟨by simpa using hcon, by simp⟩
    | succ i ih =>
      have h := hJ (j0 + i) (by omega)
      change a (j0 + i + 1) ≤ 1 / 8 * (a (j0 + i) + a (j0 + i + 2)) at h
      have hnn : 0 ≤ a (j0 + i + 1) := abs_nonneg _
      have h2 : 4 * a (j0 + i + 1) < a (j0 + i + 2) := by linarith [ih.1]
      refine ⟨by rw [show j0 + (i + 1) = j0 + i + 1 by ring]; linarith, ?_⟩
      rw [show j0 + (i + 1) + 1 = j0 + i + 2 by ring, pow_succ]
      nlinarith [ih.2]
  have hδ : 0 < a (j0 + 1) := lt_of_le_of_lt (by positivity) (key 0).1
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (M * (j0 + 2) / a (j0 + 1)) (by norm_num : (1 : ℝ) < 2)
  have hlin := hM (j0 + i + 1)
  have hk := (key i).2
  have h2i : ((i : ℝ) + 1) ≤ 2 ^ i := by
    have := Nat.lt_two_pow_self (n := i)
    exact_mod_cast this
  have h4 : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
  rw [div_lt_iff₀ hδ] at hi
  have hj0 : (0 : ℝ) ≤ j0 := Nat.cast_nonneg j0
  have : (4 : ℝ) ^ i * a (j0 + 1) ≤ M * (j0 + 2) * 2 ^ i := by
    calc (4 : ℝ) ^ i * a (j0 + 1) ≤ a (j0 + i + 1) := hk
      _ ≤ M * (((j0 + i + 1 : ℕ) : ℝ) + 1) := hlin
      _ ≤ M * ((j0 + 2) * (i + 1)) := by
          gcongr; push_cast; nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      _ ≤ M * (j0 + 2) * 2 ^ i := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h2i (by positivity)
  rw [h4] at this
  have h2pos : (0 : ℝ) < 2 ^ i := by positivity
  nlinarith

/-- `|B_k - (n+2k)(n+2k+1)| ≤ 2|γ²|(1+m²)` for `k ≥ 1`. -/
lemma p2y_recB_close {n m : ℕ} (γ2 : ℝ) {k : ℤ} (hk : 1 ≤ k) :
    |spheroidalRecB n m γ2 k - ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1)| ≤
      2 * |γ2| * (1 + m ^ 2) := by
  have kr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold spheroidalRecB
  set F := (((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - 1 + m ^ 2) /
    ((2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3)) with hF
  have hQ : 0 < (2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3) := by nlinarith
  have hF0 : 0 ≤ F := div_nonneg (by nlinarith) hQ.le
  have hF1 : F ≤ 1 + m ^ 2 := by
    have hQ1 : 1 ≤ (2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3) := by nlinarith
    rw [hF, div_le_iff₀ hQ]
    nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (by linarith : (0 : ℝ) ≤
      (2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3) - 1)]
  rw [show 2 * γ2 * (((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - 1 + m ^ 2) /
    ((2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3)) = 2 * γ2 * F by rw [hF]; ring,
    show ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - 2 * γ2 * F -
      ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) = -(2 * γ2 * F) by ring, abs_neg, abs_mul,
    abs_mul, abs_of_nonneg hF0, abs_two, mul_assoc, mul_assoc]
  gcongr

/-- `|-4A_k - γ²| ≤ |γ²|(4m²+12m+7)/k` for `k ≥ 2`. -/
lemma p2y_recA_close {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {k : ℤ} (hk : 2 ≤ k) :
    |-4 * spheroidalRecA n m γ2 k - γ2| ≤ |γ2| * (4 * m ^ 2 + 12 * m + 7) / k := by
  have kr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmr : (m : ℝ) ≤ n := by exact_mod_cast hmn
  unfold spheroidalRecA
  set ν : ℝ := (n : ℝ) + 2 * k with hν
  have hν4 : 4 ≤ ν := by rw [hν]; linarith
  have hkν : (k : ℝ) ≤ ν := by rw [hν]; linarith
  have hQ : ν ^ 2 ≤ (2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1) := by
    rw [show (2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1) = (2 * ν - 3) * (2 * ν - 1) by
      rw [hν]; ring]
    nlinarith
  have hQ0 : 0 < (2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1) := by nlinarith
  rw [show -4 * (-γ2 * (((n : ℝ) - m + 2 * k - 1) * ((n : ℝ) - m + 2 * k)) /
      ((2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1))) - γ2 =
      γ2 * (((4 - 8 * m) * ν + 4 * m ^ 2 + 4 * m - 3) /
        ((2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1))) by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    set Qi := ((2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1))⁻¹ with hQi
    have hQQ : ((2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1)) * Qi = 1 :=
      mul_inv_cancel₀ hQ0.ne'
    rw [hν]
    linear_combination γ2 * hQQ]
  rw [abs_mul, abs_div, abs_of_pos hQ0, le_div_iff₀ (by linarith), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [div_mul_eq_mul_div, div_le_iff₀ hQ0]
  have hl : |(4 - 8 * (m : ℝ)) * ν + 4 * m ^ 2 + 4 * m - 3| ≤ (4 * m ^ 2 + 12 * m + 7) * ν := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hm0 (by linarith : (0 : ℝ) ≤ ν)]
  calc |(4 - 8 * (m : ℝ)) * ν + 4 * m ^ 2 + 4 * m - 3| * k
      ≤ (4 * m ^ 2 + 12 * m + 7) * ν * ν :=
        mul_le_mul hl hkν (by linarith) (by positivity)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by nlinarith [hQ]) (by positivity)

/-- The algebra of 30.8.7: from `16 D E = 4k² X + γ² Y`, `D ≥ k²`, `|X| ≤ c₃/k`, `|Y| ≤ c₂ k`. -/
lemma p2y_alg_ratio {k D X Y E γ2 c₂ c₃ : ℝ} (hk : 1 ≤ k) (hD : k ^ 2 ≤ D)
    (h : 16 * D * E = 4 * k ^ 2 * X + γ2 * Y) (hX : |X| ≤ c₃ / k) (hY : |Y| ≤ c₂ * k) :
    |E| ≤ (4 * c₃ + |γ2| * c₂) / 16 * k⁻¹ := by
  have hk0 : 0 < k := by linarith
  have hD0 : 0 < D := by nlinarith
  have h1 : 16 * D * |E| ≤ k * (4 * c₃ + |γ2| * c₂) := by
    have := congrArg abs h
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 16 * D)] at this
    rw [this]
    have hX' : k * |X| ≤ c₃ := by rw [le_div_iff₀ hk0] at hX; linarith
    calc |4 * k ^ 2 * X + γ2 * Y| ≤ |4 * k ^ 2 * X| + |γ2 * Y| := abs_add_le _ _
      _ = 4 * k * (k * |X|) + |γ2| * |Y| := by
          rw [abs_mul (4 * k ^ 2), abs_mul γ2, abs_of_pos (by positivity : (0 : ℝ) < 4 * k ^ 2)]
          ring
      _ ≤ 4 * k * c₃ + |γ2| * (c₂ * k) := by gcongr
      _ = _ := by ring
  have hE := abs_nonneg E
  rw [← div_eq_mul_inv, le_div_iff₀ hk0]
  nlinarith

/-- For `γ² ≠ 0`, eventually `a_j ≠ 0` and `|a_{j+1}| ≤ |a_j|/4`. -/
lemma p2y_coeff_ne_zero {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} (hγ : γ2 ≠ 0) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ)) ≠ 0 ∧
      |spheroidalCoeff n m γ2 (((j + 1 : ℕ) : ℤ) - ((n - m) / 2 : ℕ))| ≤
        |spheroidalCoeff n m γ2 ((j : ℤ) - ((n - m) / 2 : ℕ))| / 4 := by
  obtain ⟨J, hJ⟩ := p2y_coeff_ratio_le hmn γ2
  refine ⟨J, fun j hj => ⟨fun h0 => ?_, hJ j hj⟩⟩
  apply p2y_coeff_not_eventually_zero hmn hγ
  refine ⟨j, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
  induction d with
  | zero => simpa using h0
  | succ d ih =>
    have h := hJ (j + d) (by omega)
    rw [ih (by omega), abs_zero, zero_div] at h
    exact abs_nonpos_iff.mp h

/-- **Ratio asymptotics** (DLMF 30.8.7): `k² a^m_{n,k}(γ²)/a^m_{n,k-1}(γ²) = γ²/16 + O(1/k)` as
`k → ∞`. Proved: for `γ² = 0` the coefficients vanish for `k ≥ 1`; otherwise they are eventually
nonzero with `|a_{k+1}/a_k| ≤ 1/4`, and 30.8.4 gives
`k² a_k/a_{k-1} = -k² A_k/(B_k - λ + C_k a_{k+1}/a_k)`. -/
@[dlmf 30.8.E7]
theorem spheroidalCoeff_ratio_isBigO {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    (fun k : ℕ => (k : ℝ) ^ 2 * spheroidalCoeff n m γ2 k / spheroidalCoeff n m γ2 ((k : ℤ) - 1) -
        γ2 / 16) =O[atTop] (fun k : ℕ => (k : ℝ)⁻¹) := by
  by_cases hγ : γ2 = 0
  · subst hγ
    refine (isBigO_zero (fun k : ℕ => (k : ℝ)⁻¹) atTop).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hrec := spheroidalCoeff_recurrence_of_le hmn 0 (k := (k : ℤ)) (by omega)
    have hA : spheroidalRecA n m 0 k = 0 := by simp [spheroidalRecA]
    have hC : spheroidalRecC n m 0 k = 0 := by simp [spheroidalRecC]
    have hB : spheroidalRecB n m 0 k = ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) := by
      simp [spheroidalRecB]
    rw [hA, hC, hB, p1s_spheroidalEigenvalue_zero hmn] at hrec
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpos : ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - n * (n + 1) ≠ 0 := by
      have : (0 : ℝ) < ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - n * (n + 1) := by nlinarith
      exact this.ne'
    have h0 : spheroidalCoeff n m 0 k = 0 := by
      simp only [zero_mul, zero_add, add_zero] at hrec
      exact (mul_eq_zero.mp hrec).resolve_left hpos
    simp [h0]
  -- `γ² ≠ 0`
  obtain ⟨J1, hJ1⟩ := p2y_coeff_ne_zero hmn hγ
  set R := (n - m) / 2 with hR
  set lam := spheroidalEigenvalue n m γ2
  set c₀ : ℝ := 2 * |γ2| * (1 + m ^ 2) + |lam| + |γ2| / 4 with hc₀
  set c₂ : ℝ := (n : ℝ) ^ 2 + 5 * n + 2 + c₀ with hc₂
  set c₃ : ℝ := |γ2| * (4 * m ^ 2 + 12 * m + 7) with hc₃
  obtain ⟨K0, hK0⟩ := exists_nat_ge c₀
  refine IsBigO.of_bound ((4 * c₃ + |γ2| * c₂) / 16) ?_
  filter_upwards [eventually_ge_atTop (J1 + 2 + K0)] with k hk
  have ha0 : spheroidalCoeff n m γ2 ((k : ℤ) - 1) ≠ 0 := by
    have := (hJ1 (k - 1 + R) (by omega)).1
    have h1k : 1 ≤ k := by omega
    rwa [show ((k - 1 + R : ℕ) : ℤ) - R = (k : ℤ) - 1 by push_cast [Nat.cast_sub h1k]; ring]
      at this
  have ha1 : spheroidalCoeff n m γ2 (k : ℤ) ≠ 0 := by
    have := (hJ1 (k + R) (by omega)).1
    rwa [show ((k + R : ℕ) : ℤ) - R = (k : ℤ) by push_cast; ring] at this
  have hs : |spheroidalCoeff n m γ2 ((k : ℤ) + 1)| ≤ |spheroidalCoeff n m γ2 (k : ℤ)| / 4 := by
    have := (hJ1 (k + R) (by omega)).2
    rwa [show ((k + R + 1 : ℕ) : ℤ) - R = (k : ℤ) + 1 by push_cast; ring,
      show ((k + R : ℕ) : ℤ) - R = (k : ℤ) by push_cast; ring] at this
  have hk2 : (2 : ℤ) ≤ (k : ℤ) := by omega
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by omega
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkc : c₀ ≤ (k : ℝ) := by
    have : (K0 : ℝ) ≤ k := by exact_mod_cast (by omega : K0 ≤ k)
    linarith
  have hrec := spheroidalCoeff_recurrence_of_le hmn γ2 (k := (k : ℤ)) (by omega)
  simp only [show -(((n - m) / 2 : ℕ) : ℤ) ≤ (k : ℤ) - 1 by omega, ↓reduceIte] at hrec
  obtain ⟨hA, hC, -⟩ := p2y_rec_bounds hmn γ2 hk1
  have hBc := p2y_recB_close (n := n) (m := m) γ2 hk1
  have hX := p2y_recA_close hmn γ2 hk2
  set a0 := spheroidalCoeff n m γ2 ((k : ℤ) - 1)
  set a1 := spheroidalCoeff n m γ2 (k : ℤ)
  set a2 := spheroidalCoeff n m γ2 ((k : ℤ) + 1)
  set A := spheroidalRecA n m γ2 k
  set B := spheroidalRecB n m γ2 k
  set C := spheroidalRecC n m γ2 k
  set sr := a2 / a1 with hsr
  have hsr4 : |sr| ≤ 1 / 4 := by
    rw [hsr, abs_div, div_le_iff₀ (abs_pos.mpr ha1)]; linarith
  have hCs : |C * sr| ≤ |γ2| / 4 := by
    rw [abs_mul]
    calc |C| * |sr| ≤ |γ2| * (1 / 4) := mul_le_mul hC hsr4 (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  set D := B - lam + C * sr with hD
  set r := a1 / a0 with hr
  have hrD : r * D = -A := by
    rw [hr, hD, hsr]
    field_simp
    linear_combination hrec
  set ν : ℝ := (n : ℝ) + 2 * k with hν
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlam := abs_le.mp (le_refl |lam|)
  have hBc' := abs_le.mp hBc
  have hCs' := abs_le.mp hCs
  have hlam' : -|lam| ≤ lam ∧ lam ≤ |lam| := ⟨neg_abs_le lam, le_abs_self lam⟩
  simp only [Int.cast_natCast] at hBc' hX
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hk1r : (1 : ℝ) ≤ k := by linarith
  have hc0 : 0 ≤ c₀ := by positivity
  set t := B - ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) with ht
  have hid : D = 4 * (k : ℝ) ^ 2 + ((n : ℝ) ^ 2 + n + (4 * n + 2) * k) + t - lam + C * sr := by
    rw [hD, ht]; ring
  have hpos : 0 ≤ (n : ℝ) ^ 2 + n + (4 * n + 2) * k := by positivity
  have hDk : (k : ℝ) ^ 2 ≤ D := by
    rw [hid]; linarith [hBc'.1, hCs'.1, hlam'.2]
  have h1 : (n : ℝ) ^ 2 + n + c₀ ≤ ((n : ℝ) ^ 2 + n + c₀) * k :=
    le_mul_of_one_le_right (by positivity) hk1r
  have hY : |4 * (k : ℝ) ^ 2 - D| ≤ c₂ * k := by
    have e1 : 4 * (k : ℝ) ^ 2 - (4 * (k : ℝ) ^ 2 + ((n : ℝ) ^ 2 + n + (4 * n + 2) * k) + t - lam +
        C * sr) = -((n : ℝ) ^ 2 + n) - (4 * n + 2) * k - t + lam - C * sr := by ring
    have e2 : c₂ * k = ((n : ℝ) ^ 2 + n + c₀) * k + (4 * n + 2) * k := by rw [hc₂]; ring
    rw [hid, e1, e2, abs_le]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnk : 0 ≤ (4 * (n : ℝ) + 2) * k := by positivity
    constructor <;> linarith [hBc'.1, hBc'.2, hCs'.1, hCs'.2, hlam'.1, hlam'.2]
  have hE : 16 * D * ((k : ℝ) ^ 2 * a1 / a0 - γ2 / 16) =
      4 * (k : ℝ) ^ 2 * (-4 * A - γ2) + γ2 * (4 * (k : ℝ) ^ 2 - D) := by
    rw [mul_div_assoc, ← hr]
    linear_combination 16 * (k : ℝ) ^ 2 * hrD
  have hfin := p2y_alg_ratio (c₃ := c₃) (by linarith) hDk hE (by rw [hc₃]; exact hX) hY
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
  exact hfin

/-- For `γ² ≠ 0`, eventually `a_{k-1} ≠ 0`, `a_k ≠ 0` and `|a_k/a_{k-1}| ≤ |γ²|/k²`. -/
lemma p2y_ratio_small {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} (hγ : γ2 ≠ 0) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → spheroidalCoeff n m γ2 ((k : ℤ) - 1) ≠ 0 ∧
      spheroidalCoeff n m γ2 (k : ℤ) ≠ 0 ∧
      |spheroidalCoeff n m γ2 (k : ℤ) / spheroidalCoeff n m γ2 ((k : ℤ) - 1)| ≤
        |γ2| / (k : ℝ) ^ 2 := by
  -- `γ² ≠ 0`
  obtain ⟨J1, hJ1⟩ := p2y_coeff_ne_zero hmn hγ
  set R := (n - m) / 2 with hR
  set lam := spheroidalEigenvalue n m γ2
  set c₀ : ℝ := 2 * |γ2| * (1 + m ^ 2) + |lam| + |γ2| / 4 with hc₀
  set c₂ : ℝ := (n : ℝ) ^ 2 + 5 * n + 2 + c₀ with hc₂
  set c₃ : ℝ := |γ2| * (4 * m ^ 2 + 12 * m + 7) with hc₃
  obtain ⟨K0, hK0⟩ := exists_nat_ge c₀
  refine ⟨J1 + 2 + K0, fun k hk => ?_⟩
  have ha0 : spheroidalCoeff n m γ2 ((k : ℤ) - 1) ≠ 0 := by
    have := (hJ1 (k - 1 + R) (by omega)).1
    have h1k : 1 ≤ k := by omega
    rwa [show ((k - 1 + R : ℕ) : ℤ) - R = (k : ℤ) - 1 by push_cast [Nat.cast_sub h1k]; ring]
      at this
  have ha1 : spheroidalCoeff n m γ2 (k : ℤ) ≠ 0 := by
    have := (hJ1 (k + R) (by omega)).1
    rwa [show ((k + R : ℕ) : ℤ) - R = (k : ℤ) by push_cast; ring] at this
  have hs : |spheroidalCoeff n m γ2 ((k : ℤ) + 1)| ≤ |spheroidalCoeff n m γ2 (k : ℤ)| / 4 := by
    have := (hJ1 (k + R) (by omega)).2
    rwa [show ((k + R + 1 : ℕ) : ℤ) - R = (k : ℤ) + 1 by push_cast; ring,
      show ((k + R : ℕ) : ℤ) - R = (k : ℤ) by push_cast; ring] at this
  have hk2 : (2 : ℤ) ≤ (k : ℤ) := by omega
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by omega
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkc : c₀ ≤ (k : ℝ) := by
    have : (K0 : ℝ) ≤ k := by exact_mod_cast (by omega : K0 ≤ k)
    linarith
  have hrec := spheroidalCoeff_recurrence_of_le hmn γ2 (k := (k : ℤ)) (by omega)
  simp only [show -(((n - m) / 2 : ℕ) : ℤ) ≤ (k : ℤ) - 1 by omega, ↓reduceIte] at hrec
  obtain ⟨hA, hC, -⟩ := p2y_rec_bounds hmn γ2 hk1
  have hBc := p2y_recB_close (n := n) (m := m) γ2 hk1
  have hX := p2y_recA_close hmn γ2 hk2
  set a0 := spheroidalCoeff n m γ2 ((k : ℤ) - 1)
  set a1 := spheroidalCoeff n m γ2 (k : ℤ)
  set a2 := spheroidalCoeff n m γ2 ((k : ℤ) + 1)
  set A := spheroidalRecA n m γ2 k
  set B := spheroidalRecB n m γ2 k
  set C := spheroidalRecC n m γ2 k
  set sr := a2 / a1 with hsr
  have hsr4 : |sr| ≤ 1 / 4 := by
    rw [hsr, abs_div, div_le_iff₀ (abs_pos.mpr ha1)]; linarith
  have hCs : |C * sr| ≤ |γ2| / 4 := by
    rw [abs_mul]
    calc |C| * |sr| ≤ |γ2| * (1 / 4) := mul_le_mul hC hsr4 (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  set D := B - lam + C * sr with hD
  set r := a1 / a0 with hr
  have hrD : r * D = -A := by
    rw [hr, hD, hsr]
    field_simp
    linear_combination hrec
  set ν : ℝ := (n : ℝ) + 2 * k with hν
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlam := abs_le.mp (le_refl |lam|)
  have hBc' := abs_le.mp hBc
  have hCs' := abs_le.mp hCs
  have hlam' : -|lam| ≤ lam ∧ lam ≤ |lam| := ⟨neg_abs_le lam, le_abs_self lam⟩
  simp only [Int.cast_natCast] at hBc' hX
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hk1r : (1 : ℝ) ≤ k := by linarith
  have hc0 : 0 ≤ c₀ := by positivity
  set t := B - ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) with ht
  have hid : D = 4 * (k : ℝ) ^ 2 + ((n : ℝ) ^ 2 + n + (4 * n + 2) * k) + t - lam + C * sr := by
    rw [hD, ht]; ring
  have hpos : 0 ≤ (n : ℝ) ^ 2 + n + (4 * n + 2) * k := by positivity
  have hDk : (k : ℝ) ^ 2 ≤ D := by
    rw [hid]; linarith [hBc'.1, hCs'.1, hlam'.2]
  have h1 : (n : ℝ) ^ 2 + n + c₀ ≤ ((n : ℝ) ^ 2 + n + c₀) * k :=
    le_mul_of_one_le_right (by positivity) hk1r
  refine ⟨ha0, ha1, ?_⟩
  have hk0 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hD0 : 0 < D := lt_of_lt_of_le hk0 hDk
  have hrA : |r| * D = |A| := by
    rw [← abs_neg A, ← hrD, abs_mul, abs_of_pos hD0]
  change |r| ≤ _
  rw [le_div_iff₀ hk0]
  calc |r| * (k : ℝ) ^ 2 ≤ |r| * D := mul_le_mul_of_nonneg_left hDk (abs_nonneg _)
    _ = |A| := hrA
    _ ≤ |γ2| := hA

/-- `|A_k| ≥ |γ²|/16` when `n + 2k ≥ 2m + 2`. -/
lemma p2y_recA_ge {n m : ℕ} (γ2 : ℝ) {k : ℤ} (hk : 2 * (m : ℤ) + 2 ≤ n + 2 * k) :
    |γ2| / 16 ≤ |spheroidalRecA n m γ2 k| := by
  have hkr : 2 * (m : ℝ) + 2 ≤ n + 2 * k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold spheroidalRecA
  have hQ : 0 < (2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1) := by nlinarith
  have hP : (0 : ℝ) ≤ ((n : ℝ) - m + 2 * k - 1) * ((n : ℝ) - m + 2 * k) := by nlinarith
  rw [mul_div_assoc, abs_mul, abs_neg, abs_div, abs_of_pos hQ, abs_of_nonneg hP,
    show |γ2| / 16 = |γ2| * (1 / 16) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [div_le_div_iff₀ (by norm_num) hQ]
  nlinarith

/-- **Ratio asymptotics** (DLMF 30.8.8):
`(λ^m_n(γ²) - B_k)/A_k · a^m_{n,k}(γ²)/a^m_{n,k-1}(γ²) = 1 + O(k⁻⁴)` as `k → ∞`.
Corrected: the hypothesis `γ2 ≠ 0` was added (2026-10-26), since at `γ² = 0` the statement fails
(`p2y_not_spheroidalCoeff_ratio_isBigO_four_zero`). Proved: by 30.8.4 the expression equals
`C_k (a_k/a_{k-1})(a_{k+1}/a_k)/A_k`, and both ratios are `O(k⁻²)` while `|A_k| ≥ |γ²|/16`. -/
@[dlmf 30.8.E8]
theorem spheroidalCoeff_ratio_isBigO_four {n m : ℕ} (hmn : m ≤ n) {γ2 : ℝ} (hγ : γ2 ≠ 0) :
    (fun k : ℕ => (spheroidalEigenvalue n m γ2 - spheroidalRecB n m γ2 k) /
        spheroidalRecA n m γ2 k *
          (spheroidalCoeff n m γ2 k / spheroidalCoeff n m γ2 ((k : ℤ) - 1)) - 1)
      =O[atTop] (fun k : ℕ => ((k : ℝ) ^ 4)⁻¹) := by
  obtain ⟨K, hK⟩ := p2y_ratio_small hmn hγ
  refine IsBigO.of_bound (16 * |γ2| ^ 2) ?_
  filter_upwards [eventually_ge_atTop (K + m + 2)] with k hk
  obtain ⟨ha0, ha1, hr⟩ := hK k (by omega)
  obtain ⟨-, ha2', hs⟩ := hK (k + 1) (by omega)
  push_cast at ha2' hs
  rw [show ((k : ℤ) + 1 - 1) = (k : ℤ) by ring] at hs
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by omega
  have hA0 := p2y_recA_ne_zero hmn hγ (k := (k : ℤ)) (by omega)
  have hAge := p2y_recA_ge (n := n) (m := m) γ2 (k := (k : ℤ)) (by omega)
  obtain ⟨-, hC, -⟩ := p2y_rec_bounds hmn γ2 hk1
  have hrec := spheroidalCoeff_recurrence_of_le hmn γ2 (k := (k : ℤ)) (by omega)
  simp only [show -(((n - m) / 2 : ℕ) : ℤ) ≤ (k : ℤ) - 1 by omega, ↓reduceIte] at hrec
  set a0 := spheroidalCoeff n m γ2 ((k : ℤ) - 1)
  set a1 := spheroidalCoeff n m γ2 (k : ℤ)
  set a2 := spheroidalCoeff n m γ2 ((k : ℤ) + 1)
  set A := spheroidalRecA n m γ2 k
  set B := spheroidalRecB n m γ2 k
  set C := spheroidalRecC n m γ2 k
  have e : (spheroidalEigenvalue n m γ2 - B) / A * (a1 / a0) - 1 =
      C * (a1 / a0) * (a2 / a1) / A := by
    field_simp
    linear_combination -hrec
  rw [e, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_mul, abs_mul]
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkpos : (0 : ℝ) < k := by linarith
  have hk2 : (k : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
  have hs' : |a2 / a1| ≤ |γ2| / (k : ℝ) ^ 2 :=
    hs.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hk2)
  have hγ0 : 0 < |γ2| := abs_pos.mpr hγ
  rw [abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) ^ 4), div_le_iff₀ (lt_of_lt_of_le
    (by positivity) hAge)]
  calc |C| * |a1 / a0| * |a2 / a1| ≤ |γ2| * (|γ2| / (k : ℝ) ^ 2) * (|γ2| / (k : ℝ) ^ 2) := by
        gcongr
    _ = 16 * |γ2| ^ 2 * ((k : ℝ) ^ 4)⁻¹ * (|γ2| / 16) := by field_simp
    _ ≤ 16 * |γ2| ^ 2 * ((k : ℝ) ^ 4)⁻¹ * |A| := by gcongr

/-- **30.8.8 fails at `γ² = 0`** as stated: then `A_k = 0`, the Lean quotient
`(λ - B_k)/A_k` is `0`, and the expression is the constant `-1`, which is not `O(k⁻⁴)`. -/
lemma p2y_not_spheroidalCoeff_ratio_isBigO_four_zero (n m : ℕ) :
    ¬ (fun k : ℕ => (spheroidalEigenvalue n m 0 - spheroidalRecB n m 0 k) /
        spheroidalRecA n m 0 k *
          (spheroidalCoeff n m 0 k / spheroidalCoeff n m 0 ((k : ℤ) - 1)) - 1)
      =O[atTop] (fun k : ℕ => ((k : ℝ) ^ 4)⁻¹) := by
  intro h
  have hA : ∀ k : ℕ, spheroidalRecA n m 0 k = 0 := fun k => by simp [spheroidalRecA]
  simp only [hA, div_zero, zero_mul, zero_sub] at h
  have ht : Tendsto (fun k : ℕ => ((k : ℝ) ^ 4)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
      |>.inv_tendsto_atTop
  have h2 := h.trans_tendsto ht
  have h3 : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1)) := tendsto_const_nhds
  have := tendsto_nhds_unique h3 h2
  norm_num at this

/-! ### §30.8(ii) Functions of the second kind -/

/-- **The expansion of `𝖰s`** (DLMF 30.8.9–30.8.11): for `-1 < x < 1`,
`𝖰s^m_n(x, γ²) = ∑_{k ≤ -N-1} (-1)^k a'^m_{n,k}(γ²) 𝖯^m_{n+2k}(x)
  + ∑_{k ≥ -N} (-1)^k a^m_{n,k}(γ²) 𝖰^m_{n+2k}(x)`, with `a'` the recessive solution of 30.8.4
normalized by 30.8.10–30.8.11 and `a^m_{n,k}` extended to `-N ≤ k < -R` by forward recursion
(hypothesis: the forward solution does not vanish at `-R`, else `𝖰s` does not exist). -/
@[dlmf 30.8.E9, dlmf 30.8.E10, dlmf 30.8.E11]
theorem spheroidalQs_eq_ferrers_series {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∃ S₁ S₂ : ℝ,
      HasSum (fun j : ℕ =>
          let k : ℤ := -(((n + m) / 2 : ℕ) : ℤ) - 1 - j
          (-1 : ℝ) ^ k * spheroidalCoeffPrime n m γ2 k * (ferrersP ((n : ℂ) + 2 * k) m x).re)
        S₁ ∧
      HasSum (fun j : ℕ =>
          let k : ℤ := -(((n + m) / 2 : ℕ) : ℤ) + j
          (-1 : ℝ) ^ k * spheroidalCoeff n m γ2 k * (ferrersQ ((n : ℂ) + 2 * k) m x).re)
        S₂ ∧
      spheroidalQs n m x γ2 = S₁ + S₂ := by
  sorry

/-- **The extended coefficients** (DLMF §30.8(ii)): for `-N ≤ k < -R` they are obtained by
forward recursion from `a^m_{n,-N-1} = 0`, matched to `a^m_{n,-R}`. Proved (definition). -/
@[dlmf 30.8.ii]
theorem spheroidalCoeff_of_lt {n m : ℕ} (γ2 : ℝ) {k : ℤ} (hk : k < -(((n - m) / 2 : ℕ) : ℤ))
    (hk' : -(((n + m) / 2 : ℕ) : ℤ) ≤ k) :
    spheroidalCoeff n m γ2 k = spheroidalCoeff n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) *
      spheroidalFwd n m γ2 (k + ((n + m) / 2 : ℕ) + 1).toNat /
        spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) := by
  have h1 : ¬ (-(((n - m) / 2 : ℕ) : ℤ) ≤ k) := not_le.mpr hk
  have h2 : spheroidalCoeff n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) =
      spheroidalCoeffMain n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) := by
    unfold spheroidalCoeff
    simp only [le_refl, ↓reduceIte]
  rw [h2]
  unfold spheroidalCoeff
  simp only [h1, hk', ↓reduceIte]

/-- **The recurrence** (DLMF 30.8.4, §30.8(ii)): the coefficients `a^m_{n,k}(γ²)` satisfy
`A_k a_{k-1} + (B_k - λ^m_n(γ²)) a_k + C_k a_{k+1} = 0` for all `k ∈ ℤ` (with `a_k = 0` for
`k < -N` and the extension of §30.8(ii) for `-N ≤ k < -R`), when the forward solution does not
vanish at `k = -R`. Proved from `spheroidalCoeff_recurrence_of_le` and the forward recursion. -/
@[dlmf 30.8.E4]
theorem spheroidalCoeff_recurrence {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) (k : ℤ) :
    spheroidalRecA n m γ2 k * spheroidalCoeff n m γ2 (k - 1) +
        (spheroidalRecB n m γ2 k - spheroidalEigenvalue n m γ2) * spheroidalCoeff n m γ2 k +
      spheroidalRecC n m γ2 k * spheroidalCoeff n m γ2 (k + 1) = 0 := by
  set R := (n - m) / 2 with hR
  set N := (n + m) / 2 with hN
  have hRN : R ≤ N := Nat.div_le_div_right (by omega)
  have hNR : N - R = m := by omega
  -- values below `-N` vanish
  have hlow : ∀ j : ℤ, j < -(N : ℤ) → spheroidalCoeff n m γ2 j = 0 := by
    intro j hj
    unfold spheroidalCoeff
    split_ifs <;> first | omega | rfl
  -- the extended coefficients are proportional to the forward solution
  have hext : ∀ j : ℤ, -(N : ℤ) - 1 ≤ j → j ≤ -(R : ℤ) → spheroidalCoeff n m γ2 j =
      spheroidalCoeff n m γ2 (-(R : ℤ)) / spheroidalFwd n m γ2 (N - R + 1) *
        spheroidalFwd n m γ2 (j + N + 1).toNat := by
    intro j hj1 hj2
    rcases lt_or_eq_of_le hj2 with hj2 | rfl
    · rcases lt_or_eq_of_le hj1 with hj1 | rfl
      · rw [spheroidalCoeff_of_lt γ2 hj2 (by omega)]
        ring
      · rw [hlow _ (by omega), show (-(N : ℤ) - 1 + N + 1).toNat = 0 by omega]
        simp [spheroidalFwd]
    · rw [show (-(R : ℤ) + N + 1).toNat = N - R + 1 by omega]
      field_simp
  -- `C_k` vanishes at `k = -N - 1`
  have hC : spheroidalRecC n m γ2 (-(N : ℤ) - 1) = 0 := by
    unfold spheroidalRecC
    have hpar := Nat.div_add_mod (n + m) 2
    have hnum : ((n : ℝ) + m + 2 * ((-(N : ℤ) - 1 : ℤ) : ℝ) + 1) *
        ((n : ℝ) + m + 2 * ((-(N : ℤ) - 1 : ℤ) : ℝ) + 2) = 0 := by
      have hc : (n : ℝ) + m = 2 * N + ((n + m) % 2 : ℕ) := by
        exact_mod_cast (by omega : n + m = 2 * N + (n + m) % 2)
      push_cast
      rw [hc]
      rcases Nat.mod_two_eq_zero_or_one (n + m) with h | h <;> rw [h] <;> push_cast <;> ring
    rw [hnum]; ring
  rcases lt_trichotomy k (-(R : ℤ)) with hk | hk | hk
  · -- `k < -R`
    rcases lt_or_ge k (-(N : ℤ) - 1) with hk1 | hk1
    · rw [hlow _ (by omega), hlow _ (by omega), hlow _ (by omega)]; ring
    rcases eq_or_lt_of_le hk1 with hk1 | hk1
    · subst hk1
      rw [hlow _ (by omega), hlow _ (by omega), hC]; ring
    -- `-N ≤ k ≤ -R - 1`: the forward recursion
    have hγ : γ2 ≠ 0 := by
      intro h0
      apply hf
      rw [show N - R + 1 = (m - 1) + 2 by omega]
      simp only [spheroidalFwd, spheroidalRecC, h0]
      simp
    obtain ⟨j, hj⟩ : ∃ j : ℕ, k = -(N : ℤ) + j := ⟨(k + N).toNat, by omega⟩
    have hCk : spheroidalRecC n m γ2 k ≠ 0 := by
      unfold spheroidalRecC
      have h1 : ((n : ℝ) + m + 2 * k + 1) ≠ 0 := by
        have : (0 : ℤ) < n + m + 2 * k + 1 := by omega
        exact_mod_cast this.ne'
      have h2 : ((n : ℝ) + m + 2 * k + 2) ≠ 0 := by
        have : (0 : ℤ) < n + m + 2 * k + 2 := by omega
        exact_mod_cast this.ne'
      have h3 : (2 * (n : ℝ) + 4 * k + 3) ≠ 0 := by
        have : (2 * (n : ℤ) + 4 * k + 3) ≠ 0 := by omega
        exact_mod_cast this
      have h4 : (2 * (n : ℝ) + 4 * k + 5) ≠ 0 := by
        have : (2 * (n : ℤ) + 4 * k + 5) ≠ 0 := by omega
        exact_mod_cast this
      exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hγ) (mul_ne_zero h1 h2)) (mul_ne_zero h3 h4)
    rw [hext (k - 1) (by omega) (by omega), hext k (by omega) (by omega),
      hext (k + 1) (by omega) (by omega)]
    rw [show (k - 1 + N + 1).toNat = j by omega, show (k + N + 1).toNat = j + 1 by omega,
      show (k + 1 + N + 1).toNat = j + 2 by omega]
    have hrec : spheroidalFwd n m γ2 (j + 2) = -(spheroidalRecA n m γ2 k * spheroidalFwd n m γ2 j +
        (spheroidalRecB n m γ2 k - spheroidalEigenvalue n m γ2) * spheroidalFwd n m γ2 (j + 1)) /
          spheroidalRecC n m γ2 k := by
      rw [hj]; rfl
    rw [hrec]
    field_simp
    ring
  · -- `k = -R`
    subst hk
    have h := spheroidalCoeff_recurrence_of_le hmn γ2 (k := -(R : ℤ)) le_rfl
    split_ifs at h with hh
    · omega
    · rw [spheroidalRecA_neg_R hmn γ2]
      linear_combination h
  · -- `k > -R`
    have h := spheroidalCoeff_recurrence_of_le hmn γ2 (k := k) hk.le
    split_ifs at h with hh
    · exact h
    · omega

end DLMF.Spheroidal

end
