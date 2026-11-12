/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic
import DLMF.WignerSymbols.ThreeJ
public import DLMF.OrthogonalPolynomials.Series.JacobiParameterSeries
import DLMF.OrthogonalPolynomials.Legendre
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Legendre products and zero-projection Wigner symbols

The Gegenbauer product expansion at parameter `1/2` gives a finite Legendre expansion.
The factorial formula for zero-projection `3j` symbols identifies its coefficients.
Legendre orthogonality then evaluates the triple integral, and the cosine substitution
puts it in the angular form of DLMF 34.3.21. The product identity is DLMF 34.3.19.

The proof reuses `ultrasphericalPolynomial_product_eq_sum_of_le`, the closed forms
`pochhammer_half` and `wigner3j_zero_zero_zero_of_even`, and `legendre_orthogonality`.
The angular substitution uses Mathlib's one-dimensional Jacobian theorem.

## Main results

* `linearization`: the finite Legendre product expansion.
* `triple_integral`: the triple product integral on `[-1, 1]`.
* `triple_integral_cos`: the angular form of the triple product integral.
-/

public noncomputable section

open Complex Finset MeasureTheory intervalIntegral
open scoped Real

namespace DLMF.WignerSymbols.LegendreProducts
open DLMF.OrthogonalPolynomials DLMF.Hypergeometric

/-- The square of the zero-projection `3j` symbol in nonnegative triangle-gap indices. -/
lemma zero_projection_square (a b k : ℕ)  :
    wigner3j (a + k) (b + k) (a + b) 0 0 0 ^ 2 =
      ((2 * a).factorial * (2 * b).factorial * (2 * k).factorial : ℝ) /
        (2 * (a + b + k) + 1).factorial *
          ((a + b + k).factorial / (a.factorial * b.factorial * k.factorial : ℝ)) ^ 2 := by
  have ht : IsTriad (a + k) (b + k) (a + b) :=
    ⟨⟨2 * k, by push_cast; ring⟩, ⟨2 * a, by push_cast; ring⟩, ⟨2 * b, by push_cast; ring⟩⟩
  rw [wigner3j_zero_zero_zero_of_even ht
    ⟨a + k, by push_cast; ring⟩ ⟨b + k, by push_cast; ring⟩ ⟨a + b, by push_cast; ring⟩
    (a + b + k) (by push_cast; ring)]
  rw [ratFactorial_of_eq (n := 2 * b) (by push_cast; ring),
    ratFactorial_of_eq (n := 2 * a) (by push_cast; ring),
    ratFactorial_of_eq (n := 2 * k) (by push_cast; ring),
    ratFactorial_of_eq (n := 2 * (a + b + k) + 1) (by push_cast; ring),
    ratFactorial_of_eq (n := b) (by push_cast; ring),
    ratFactorial_of_eq (n := a) (by push_cast; ring),
    ratFactorial_of_eq (n := k) (by push_cast; ring)]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hs : ((-1 : ℝ) ^ (a + b + k)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hs]
  ring

/-- The half-parameter Gegenbauer product coefficient is the corresponding squared `3j` weight. -/
lemma coefficient (a b k : ℕ)  :
    gegenbauerProductCoeff (1 / 2) a b k =
      (((2 * (a + b : ℕ) + 1 : ℕ) : ℝ) * wigner3j (a + k) (b + k) (a + b) 0 0 0 ^ 2 : ℝ) := by
  rw [zero_projection_square]
  unfold gegenbauerProductCoeff
  have htwo : (2 : ℂ) * (1 / 2) = 1 := by norm_num
  norm_num only [htwo, pochhammer_nat_one]
  rw [pochhammer_half, pochhammer_half, pochhammer_half, pochhammer_half]
  push_cast
  have hf : ((2 * (a + b + k) + 1).factorial : ℂ) =
      (2 * (a + b + k) + 1 : ℂ) * (2 * (a + b + k)).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hf]
  have hp : (4 : ℂ) ^ (a + b + k) = 4 ^ a * 4 ^ b * 4 ^ k := by rw [pow_add, pow_add]
  rw [hp]
  have ha : (a.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr a.factorial_ne_zero
  have hb : (b.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr b.factorial_ne_zero
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hab : ((a + b).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (a + b).factorial_ne_zero
  have hs : ((a + b + k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (a + b + k).factorial_ne_zero
  have h2s : ((2 * (a + b + k)).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (2 * (a + b + k)).factorial_ne_zero
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  have hd : (1 / 2 + (a : ℂ) + b + k) ≠ 0 := by
    have hr : (1 / 2 + (a : ℂ) + b + k).re = 1 / 2 + (a : ℝ) + b + k := by norm_num
    exact ne_zero_of_re_pos (hr.symm ▸ (by positivity))
  field_simp [ha, hb, hk, hab, hs, h2s, h4, hd]
  ring

/-- A zero-projection `3j` symbol vanishes outside the even triangular degree range. -/
lemma zero_of_not_gap {m n l : ℕ}
    (hgap : ¬∃ k : ℕ, k ≤ min m n ∧ m + n - 2 * k = l)  :
    wigner3j m n l 0 0 0 = 0 := by
  by_cases ht : IsTriad (m : ℚ) n l
  · have h1 : m ≤ n + l := by
      obtain ⟨q, hq⟩ := ht.2.2
      have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
      exact_mod_cast (by linarith [hq0, hq] : (m : ℚ) ≤ n + l)
    have h2 : n ≤ m + l := by
      obtain ⟨q, hq⟩ := ht.2.1
      have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
      exact_mod_cast (by linarith [hq0, hq] : (n : ℚ) ≤ m + l)
    have h3 : l ≤ m + n := by
      obtain ⟨q, hq⟩ := ht.1
      have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
      exact_mod_cast (by linarith [hq0, hq] : (l : ℚ) ≤ m + n)
    by_cases he : Even (m + n + l)
    · obtain ⟨q, hq⟩ := he
      exfalso
      apply hgap
      exact ⟨(m + n - l) / 2, by omega, by omega⟩
    · obtain ⟨q, hq⟩ := Nat.not_even_iff_odd.mp he
      exact wigner3j_zero_zero_zero_of_odd q (by exact_mod_cast hq)
  · exact wigner3j_of_not (fun h => ht h.1)

/-- Legendre products have the finite zero-projection `3j` expansion, for every complex argument. -/
lemma linearization (m n : ℕ) (x : ℂ)  :
    legendrePolynomialP m x * legendrePolynomialP n x =
      ∑ l ∈ range (m + n + 1),
        ((2 * (l : ℝ) + 1) * wigner3j m n l 0 0 0 ^ 2 : ℝ) * legendrePolynomialP l x := by
  let S : Finset ℕ := (range (min m n + 1)).image (fun k => m + n - 2 * k)
  have hsub : S ⊆ range (m + n + 1) := by
    intro l hl
    obtain ⟨k, _, rfl⟩ := mem_image.mp hl
    simp only [mem_range]
    omega
  have hs :
      ∑ l ∈ S, ((2 * (l : ℝ) + 1) * wigner3j m n l 0 0 0 ^ 2 : ℝ) * legendrePolynomialP l x =
      ∑ l ∈ range (m + n + 1),
        ((2 * (l : ℝ) + 1) * wigner3j m n l 0 0 0 ^ 2 : ℝ) * legendrePolynomialP l x := by
    apply sum_subset hsub
    intro l _ hnot
    have hz : wigner3j m n l 0 0 0 = 0 := by
      apply zero_of_not_gap
      rintro ⟨k, hk, he⟩
      apply hnot
      exact mem_image.mpr ⟨k, mem_range.mpr (by omega), he⟩
    simp [hz]
  rw [← hs]
  dsimp only [S]
  rw [sum_image]
  · have hg : legendrePolynomialP m x * legendrePolynomialP n x =
      ∑ k ∈ range (min m n + 1),
        gegenbauerProductCoeff (1 / 2) (m - k) (n - k) k *
          legendrePolynomialP (m + n - 2 * k) x := by
      rcases le_total n m with hnm | hmn
      · have h := ultrasphericalPolynomial_product_eq_sum_of_le
          (lam := (1 / 2 : ℂ)) (by norm_num) m n hnm x
        simpa only [← legendre_eq_ultrasphericalPolynomial, gegenbauerLinearizationSum,
          min_eq_right hnm] using h
      · have h := ultrasphericalPolynomial_product_eq_sum_of_le
          (lam := (1 / 2 : ℂ)) (by norm_num) n m hmn x
        simpa only [← legendre_eq_ultrasphericalPolynomial, gegenbauerLinearizationSum,
          min_eq_left hmn, gegenbauerProductCoeff_swap (1 / 2 : ℂ), Nat.add_comm n m,
          mul_comm] using h
    rw [hg]
    apply sum_congr rfl
    intro k hk
    have hk' := mem_range.mp hk
    have hm : k ≤ m := by omega
    have hn : k ≤ n := by omega
    have he : (m - k) + (n - k) = m + n - 2 * k := by omega
    have hma : m - k + k = m := Nat.sub_add_cancel hm
    have hna : n - k + k = n := Nat.sub_add_cancel hn
    rw [coefficient]
    simp only [← Nat.cast_add, hma, hna, he]
    push_cast
    ring
  · intro a ha b hb he
    dsimp only at he
    have ha' : a < min m n + 1 := mem_range.mp ha
    have hb' : b < min m n + 1 := mem_range.mp hb
    omega

/-- The triple Legendre integral on `[-1,1]` is twice the squared zero-projection `3j` symbol. -/
lemma triple_integral (m n l : ℕ)  :
    ∫ x in (-1 : ℝ)..1,
      legendrePolynomialP m x * legendrePolynomialP n x * legendrePolynomialP l x =
        ((2 * wigner3j m n l 0 0 0 ^ 2 : ℝ) : ℂ) := by
  let C : ℕ → ℂ := fun j => ((2 * (j : ℝ) + 1) * wigner3j m n j 0 0 0 ^ 2 : ℝ)
  have hI : (∫ x in (-1 : ℝ)..1,
      legendrePolynomialP m x * legendrePolynomialP n x * legendrePolynomialP l x) =
        ∑ j ∈ range (m + n + 1), C j *
          (if j = l then 2 / (2 * (l : ℂ) + 1) else 0) := by
    calc _ = ∫ x in (-1 : ℝ)..1, ∑ j ∈ range (m + n + 1),
        C j * (legendrePolynomialP j x * legendrePolynomialP l x) := by
          apply intervalIntegral.integral_congr
          intro x _
          dsimp only
          rw [linearization, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          simp only [C]
          ring
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum
          (f := fun j x => C j * (legendrePolynomialP j x * legendrePolynomialP l x))
          (fun j _ => ((continuous_legendrePolynomialP_ofReal j).mul
            (continuous_legendrePolynomialP_ofReal l)).intervalIntegrable _ _ |>.const_mul (C j))]
        simp only [intervalIntegral.integral_const_mul, legendre_orthogonality]
  rw [hI]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases hl : l ∈ range (m + n + 1)
  · rw [ite_eq_left hl]
    dsimp only [C]
    push_cast
    have hden : (2 * (l : ℂ) + 1) ≠ 0 := by
      have hr : (2 * (l : ℂ) + 1).re = 2 * (l : ℝ) + 1 := by norm_num
      exact ne_zero_of_re_pos (hr.symm ▸ (by positivity))
    field_simp [hden]
  · rw [ite_eq_right hl]
    have hz : wigner3j m n l 0 0 0 = 0 := by
      apply zero_of_not_gap
      rintro ⟨k, _, he⟩
      apply hl
      simp only [mem_range]
      omega
    simp [hz]

/-- The angular triple Legendre integral is twice the squared zero-projection `3j` symbol. -/
lemma triple_integral_cos (m n l : ℕ)  :
    ∫ θ in (0 : ℝ)..Real.pi, legendrePolynomialP m (Real.cos θ) *
      legendrePolynomialP n (Real.cos θ) * legendrePolynomialP l (Real.cos θ) *
        (Real.sin θ : ℂ) = ((2 * wigner3j m n l 0 0 0 ^ 2 : ℝ) : ℂ) := by
  let F : ℝ → ℂ := fun x => legendrePolynomialP m x * legendrePolynomialP n x *
    legendrePolynomialP l x
  have hinj : Set.InjOn Real.cos (Set.Ioo 0 Real.pi) := by
    intro a ha b hb he
    exact Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩ he
  have him : Real.cos '' Set.Ioo 0 Real.pi = Set.Ioo (-1 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi ht.1.le le_rfl ht.2
      have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl ht.2.le ht.1
      simpa only [Set.mem_Ioo, Real.cos_pi, Real.cos_zero] using And.intro h1 h2
    · intro hx
      exact ⟨Real.arccos x, ⟨Real.arccos_pos.mpr hx.2, Real.arccos_lt_pi.mpr hx.1⟩,
        Real.cos_arccos hx.1.le hx.2.le⟩
  have ht := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t (_ : t ∈ Set.Ioo (0 : ℝ) Real.pi) => (Real.hasDerivAt_cos t).hasDerivWithinAt) hinj F
  rw [him] at ht
  have hi : (∫ θ in (0 : ℝ)..Real.pi, legendrePolynomialP m (Real.cos θ) *
      legendrePolynomialP n (Real.cos θ) * legendrePolynomialP l (Real.cos θ) *
        (Real.sin θ : ℂ)) = ∫ x in (-1 : ℝ)..1, F x := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo, ht]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only [F]
    rw [abs_neg, abs_of_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2), Complex.real_smul]
    ring
  rw [hi]
  exact triple_integral m n l
end DLMF.WignerSymbols.LegendreProducts
