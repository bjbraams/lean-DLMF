/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Pochhammer
public import DLMF.Hypergeometric.Basic.SpecialValues
public import DLMF.Gamma.Integrals.BarnesAndRamanujan
public import Mathlib.Algebra.Group.ForwardDiff

/-!
# Orthogonality of the Szegő–Askey polynomials

The Szegő–Askey polynomials `φₙ(z) = ∑ₖ (λ+1)ₖ (λ)_{n-k} / (k! (n-k)!) zᵏ` (DLMF 18.33.13) are
orthogonal on the unit circle for the weight `(1 - cos θ)^λ`, `λ > -1/2` (DLMF 18.33.14).

The trigonometric moments are `∫₀^{2π} e^{ilθ} (1 - cos θ)^λ dθ = c (-1)^l / (Γ(1+λ+l) Γ(1+λ-l))`
for every integer `l`, by the substitution `θ = π + 2x` and the Cauchy-type integral
`∫ cos^α x e^{iζx} dx` (DLMF 5.12.5 continued to complex `ζ`). With `1/Γ(s) = (s)_p/Γ(s+p)`, the
inner product of `φₙ` with `z^j`, `j < n`, becomes the `n`-th finite difference of a polynomial
of degree `n - 1` in the summation index, which vanishes.

## Main results

* `szegoAskey`: the Szegő–Askey polynomials (DLMF 18.33.13).
* `SzegoAskeyOrthogonality.integral_szegoAskey_mul_star_szegoAskey`: the orthogonality relation;
  it gives `szegoAskey_orthogonal` (DLMF 18.33.14) in `DLMF.OrthogonalPolynomials.UnitCircle`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- The Szegő–Askey polynomials `∑_k (λ+1)_k (λ)_{n-k} / (k! (n-k)!) zᵏ` (DLMF 18.33.13). -/
@[dlmf 18.33.E13]
def szegoAskey (lam : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), pochhammer (lam + 1) k * pochhammer lam (n - k) /
    ((k.factorial : ℂ) * (n - k).factorial) * z ^ k

namespace SzegoAskeyOrthogonality


/-- `1/Γ(s) = s/Γ(s+1)` for every `s` (both sides vanish at the poles). -/
private theorem inv_Gamma_eq_mul (s : ℂ) : (Gamma s)⁻¹ = s * (Gamma (s + 1))⁻¹ := by
  by_cases hs : s = 0
  · simp [hs, Complex.Gamma_zero]
  · rw [Complex.Gamma_add_one s hs, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- `1/Γ(s) = (s)_p/Γ(s+p)` for every `s`. -/
private theorem inv_Gamma_eq_pochhammer_mul (s : ℂ) (p : ℕ) :
    (Gamma s)⁻¹ = pochhammer s p * (Gamma (s + p))⁻¹ := by
  induction p with
  | zero => simp [pochhammer_zero]
  | succ p ih =>
    rw [ih, inv_Gamma_eq_mul (s + p), pochhammer_succ]
    push_cast; ring_nf

/-- The `n`-th finite difference of a polynomial of degree `< n` vanishes. -/
private theorem sum_neg_one_pow_choose_mul_eval {P : ℂ[X]} {n : ℕ} (hP : P.natDegree < n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k : ℂ) * P.eval (k : ℂ) = 0 := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP) 0
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [zero_add, nsmul_eq_mul, mul_one, Pi.zero_apply, zsmul_eq_mul] at h
  have e : ∀ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k : ℂ) * P.eval (k : ℂ) =
      (-1) ^ n * ((((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) : ℤ) : ℂ) * P.eval (k : ℂ)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have : (-1 : ℂ) ^ n = (-1) ^ k * (-1) ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
    rw [this]; push_cast
    have h2 : ((-1 : ℂ) ^ (n - k)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    linear_combination (-(-1 : ℂ) ^ k * (n.choose k : ℂ) * P.eval (k : ℂ)) * h2
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, h, mul_zero]

/-- The polynomial `(λ+1+k-j)_j (λ+1+j-k)_{n-1-j}` in `k`. -/
private def keyPoly (lam : ℂ) (n j : ℕ) : ℂ[X] :=
  (ascPochhammer ℂ j).comp (X + C (lam + 1 - j)) *
    (ascPochhammer ℂ (n - 1 - j)).comp (C (lam + 1 + j) - X)

/-- `keyPoly` has degree `< n`. -/
private theorem natDegree_keyPoly (lam : ℂ) {n j : ℕ} (hj : j < n) :
    (keyPoly lam n j).natDegree < n := by
  unfold keyPoly
  refine lt_of_le_of_lt (natDegree_mul_le) ?_
  have h1 : ((ascPochhammer ℂ j).comp (X + C (lam + 1 - j))).natDegree ≤ j := by
    refine natDegree_comp_le.trans ?_
    rw [ascPochhammer_natDegree]
    calc j * (X + C (lam + 1 - j)).natDegree ≤ j * 1 :=
          Nat.mul_le_mul_left _ (natDegree_X_add_C _).le
      _ = j := mul_one j
  have h2 : ((ascPochhammer ℂ (n - 1 - j)).comp (C (lam + 1 + j) - X)).natDegree ≤ n - 1 - j := by
    refine natDegree_comp_le.trans ?_
    rw [ascPochhammer_natDegree]
    calc (n - 1 - j) * (C (lam + 1 + j) - X).natDegree ≤ (n - 1 - j) * 1 :=
          Nat.mul_le_mul_left _
            ((natDegree_sub_le _ _).trans (by rw [natDegree_C, natDegree_X]; simp))
      _ = n - 1 - j := mul_one _
  omega

/-- The moment identity behind the orthogonality: a finite difference of order `n` of a
polynomial of degree `n - 1`. -/
private theorem key_sum (lam : ℂ) {n j : ℕ} (hj : j < n) :
    ∑ k ∈ Finset.range (n + 1), pochhammer (lam + 1) k * pochhammer lam (n - k) /
      ((k.factorial : ℂ) * (n - k).factorial) *
        ((-1) ^ k * ((Gamma (lam + 1 + k - j))⁻¹ * (Gamma (lam + 1 + j - k))⁻¹)) = 0 := by
  have e : ∀ k ∈ Finset.range (n + 1), pochhammer (lam + 1) k * pochhammer lam (n - k) /
      ((k.factorial : ℂ) * (n - k).factorial) *
        ((-1) ^ k * ((Gamma (lam + 1 + k - j))⁻¹ * (Gamma (lam + 1 + j - k))⁻¹)) =
      ((Gamma (lam + 1))⁻¹ * (Gamma lam)⁻¹ / n.factorial) *
        ((-1 : ℂ) ^ k * (n.choose k : ℂ) * (keyPoly lam n j).eval (k : ℂ)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have a1 := inv_Gamma_eq_pochhammer_mul (lam + 1 + k - j) j
    have a2 := inv_Gamma_eq_pochhammer_mul (lam + 1) k
    have a3 := inv_Gamma_eq_pochhammer_mul (lam + 1 + j - k) (n - 1 - j)
    have a4 := inv_Gamma_eq_pochhammer_mul lam (n - k)
    rw [show lam + 1 + k - j + (j : ℂ) = lam + 1 + k by ring] at a1
    rw [show lam + 1 + j - k + ((n - 1 - j : ℕ) : ℂ) = lam + ((n - k : ℕ) : ℂ) by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub hkn]; push_cast; ring]
      at a3
    have hch : (n.choose k : ℂ) = n.factorial / (k.factorial * (n - k).factorial) := by
      rw [eq_div_iff (by exact_mod_cast (mul_pos (Nat.factorial_pos k)
        (Nat.factorial_pos _)).ne'), ← mul_assoc]
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
    simp only [keyPoly, eval_mul, eval_comp, eval_add, eval_sub, eval_X, eval_C]
    rw [show (k : ℂ) + (lam + 1 - j) = lam + 1 + k - j by ring,
      show lam + 1 + j - (k : ℂ) = lam + 1 + j - k from rfl, hch, a1, a3, a2, a4]
    simp only [pochhammer]
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    field_simp
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum,
    sum_neg_one_pow_choose_mul_eval (natDegree_keyPoly lam hj), mul_zero]

/-- The weight `(1 - cos θ)^λ` as a complex function. -/
private def weight (lam : ℝ) (θ : ℝ) : ℂ := ((Real.rpow (1 - Real.cos θ) lam : ℝ) : ℂ)

/-- The constant of the trigonometric moments. -/
private def momentConst (lam : ℝ) : ℝ :=
  2 * 2 ^ lam * (π * Real.Gamma (2 * lam + 1) / 2 ^ (2 * lam))

/-- The trigonometric moments `∫₀^{2π} e^{ilθ} (1 - cos θ)^λ dθ`, from DLMF 5.12.5 continued to
complex frequencies. -/
private theorem integral_exp_mul_weight {lam : ℝ} (hlam : -1 / 2 < lam) (l : ℤ) :
    ∫ θ in (0:ℝ)..(2 * π), exp (I * l * θ) * weight lam θ =
      (momentConst lam : ℂ) * (-1) ^ l *
        ((Gamma (1 + lam + l))⁻¹ * (Gamma (1 + lam - l))⁻¹) := by
  set F : ℝ → ℂ := fun θ => exp (I * l * θ) * weight lam θ
  have hsub := intervalIntegral.integral_comp_mul_add (f := F) (a := -(π / 2)) (b := π / 2)
    (two_ne_zero : (2:ℝ) ≠ 0) π
  rw [show 2 * -(π / 2) + π = 0 by ring, show 2 * (π / 2) + π = 2 * π by ring] at hsub
  change ∫ θ in (0:ℝ)..(2 * π), F θ = _
  have h2 : ∫ θ in (0:ℝ)..(2 * π), F θ = (2:ℝ) • ∫ x in -(π / 2)..(π / 2), F (2 * x + π) := by
    rw [hsub, smul_inv_smul₀ two_ne_zero]
  rw [h2]
  have hcongr : ∀ x ∈ Set.uIcc (-(π / 2)) (π / 2), F (2 * x + π) =
      (exp (I * l * π) * (2 ^ lam : ℝ)) *
        (((Real.cos x ^ (2 * lam) : ℝ) : ℂ) * exp ((2 * l : ℂ) * x * I)) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx
    have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc hx
    have h1 : 1 - Real.cos (2 * x + π) = 2 * Real.cos x ^ 2 := by
      rw [Real.cos_add_pi, Real.cos_two_mul]; ring
    have h2 : Real.rpow (1 - Real.cos (2 * x + π)) lam = 2 ^ lam * Real.cos x ^ (2 * lam) := by
      rw [h1, show Real.rpow (2 * Real.cos x ^ 2) lam = (2 * Real.cos x ^ 2) ^ lam from rfl,
        Real.mul_rpow (by norm_num) (by positivity), Real.rpow_mul hc,
        show ((2:ℝ):ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    simp only [F, weight]
    rw [h2]
    push_cast
    rw [show I * l * (2 * x + π) = I * l * π + (2 * l) * x * I by ring, Complex.exp_add]
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    DLMF.Gamma.RamanujanIntegral.integral_cos_rpow_mul_cexp (by linarith)]
  have he : exp (I * l * π) = (-1) ^ l := by
    rw [show I * l * π = l * (π * I) by ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [he, momentConst]
  push_cast
  rw [show 1 + 2 * (lam : ℂ) / 2 + 2 * l / 2 = 1 + lam + l by ring,
    show 1 + 2 * (lam : ℂ) / 2 - 2 * l / 2 = 1 + lam - l by ring]
  rw [real_smul]
  push_cast
  ring

/-- The weight is integrable, its integral being nonzero. -/
private theorem intervalIntegrable_weight {lam : ℝ} (hlam : -1 / 2 < lam) :
    IntervalIntegrable (weight lam) volume 0 (2 * π) := by
  have h := integral_exp_mul_weight hlam 0
  simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, add_zero, sub_zero,
    zpow_zero, mul_one] at h
  refine intervalIntegral.intervalIntegrable_of_integral_ne_zero ?_
  rw [h]
  have hc : (momentConst lam : ℂ) ≠ 0 := by
    have : 0 < momentConst lam := by
      unfold momentConst
      have := Real.Gamma_pos_of_pos (show 0 < 2 * lam + 1 by linarith)
      positivity
    exact_mod_cast this.ne'
  have hg : (Gamma (1 + (lam : ℂ)))⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  exact mul_ne_zero hc (mul_ne_zero hg hg)

/-- Continuous multiples of the weight are integrable. -/
private theorem intervalIntegrable_mul_weight {lam : ℝ} (hlam : -1 / 2 < lam) {g : ℝ → ℂ}
    (hg : Continuous g) : IntervalIntegrable (fun θ => g θ * weight lam θ) volume 0 (2 * π) :=
  (intervalIntegrable_weight hlam).continuousOn_mul hg.continuousOn

/-- `φₙ` is orthogonal to `z^j`, `j < n`. -/
private theorem integral_poly_mul_exp {lam : ℝ} (hlam : -1 / 2 < lam) {n j : ℕ} (hj : j < n) :
    ∫ θ in (0:ℝ)..(2 * π), szegoAskey lam n (exp (I * θ)) * exp (-(I * j * θ)) *
      weight lam θ = 0 := by
  set A : ℕ → ℂ := fun k => pochhammer ((lam : ℂ) + 1) k * pochhammer (lam : ℂ) (n - k) /
    ((k.factorial : ℂ) * (n - k).factorial)
  have e : ∀ θ : ℝ, szegoAskey lam n (exp (I * θ)) * exp (-(I * j * θ)) * weight lam θ =
      ∑ k ∈ Finset.range (n + 1), A k * (exp (I * ((k : ℤ) - j : ℤ) * θ) * weight lam θ) := by
    intro θ
    rw [szegoAskey, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.exp_nat_mul, show exp (I * (((k : ℤ) - j : ℤ) : ℂ) * θ) =
      exp (k * (I * θ)) * exp (-(I * j * θ)) by rw [← Complex.exp_add]; push_cast; ring_nf]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (intervalIntegrable_mul_weight hlam (by fun_prop)).const_mul _]
  simp_rw [intervalIntegral.integral_const_mul, integral_exp_mul_weight hlam]
  have e2 : ∀ k ∈ Finset.range (n + 1), A k * ((momentConst lam : ℂ) * (-1) ^ ((k : ℤ) - j : ℤ) *
      ((Gamma (1 + lam + (((k : ℤ) - j : ℤ) : ℂ)))⁻¹ *
        (Gamma (1 + lam - (((k : ℤ) - j : ℤ) : ℂ)))⁻¹)) =
      ((momentConst lam : ℂ) * (-1) ^ j) * (A k * ((-1) ^ k *
        ((Gamma (lam + 1 + k - j))⁻¹ * (Gamma (lam + 1 + j - k))⁻¹))) := by
    intro k _
    have hs : ((-1 : ℂ)) ^ ((k : ℤ) - j : ℤ) = (-1) ^ k * (-1) ^ j := by
      rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
      have h2 : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
      rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right h2]
    rw [hs]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, key_sum (lam : ℂ) hj, mul_zero]

/-- `z^k` is orthogonal to `φₙ`, `k < n`. -/
private theorem integral_exp_mul_star_szegoAskey {lam : ℝ} (hlam : -1 / 2 < lam) {n k : ℕ}
    (hk : k < n) :
    ∫ θ in (0:ℝ)..(2 * π), exp (I * k * θ) * star (szegoAskey lam n (exp (I * θ))) *
      weight lam θ = 0 := by
  have h := integral_poly_mul_exp hlam hk
  rw [intervalIntegral.integral_of_le (by positivity)] at h ⊢
  have := congrArg (starRingEnd ℂ) h
  rw [← integral_conj, map_zero] at this
  rw [← this]
  refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  simp only [map_mul, weight, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I,
    Complex.conj_natCast]
  simp only [star_def]
  ring_nf

/-- Orthogonality of the Szegő–Askey polynomials for the weight `(1 - cos θ)^λ`. -/
theorem integral_szegoAskey_mul_star_szegoAskey {lam : ℝ} (hlam : -1 / 2 < lam) {m n : ℕ}
    (hmn : m ≠ n) :
    ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), szegoAskey lam m (exp (I * θ)) *
      star (szegoAskey lam n (exp (I * θ))) * (Real.rpow (1 - Real.cos θ) lam : ℂ) = 0 := by
  change ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), szegoAskey lam m (exp (I * θ)) *
      star (szegoAskey lam n (exp (I * θ))) * weight lam θ = 0
  rcases lt_or_gt_of_ne hmn with h | h
  · have e : ∀ θ : ℝ, szegoAskey lam m (exp (I * θ)) * star (szegoAskey lam n (exp (I * θ))) *
        weight lam θ = ∑ k ∈ Finset.range (m + 1), pochhammer ((lam : ℂ) + 1) k *
            pochhammer (lam : ℂ) (m - k) /
          ((k.factorial : ℂ) * (m - k).factorial) *
          (exp (I * k * θ) * star (szegoAskey lam n (exp (I * θ))) * weight lam θ) := by
      intro θ
      rw [szegoAskey, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.exp_nat_mul]; ring_nf
    simp_rw [e]
    rw [intervalIntegral.integral_finsetSum fun k _ =>
      (intervalIntegrable_mul_weight hlam (by
        unfold szegoAskey; fun_prop)).const_mul _]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_star_szegoAskey hlam
      (by have := Finset.mem_range.mp hk; omega), mul_zero]
  · have e : ∀ θ : ℝ, szegoAskey lam m (exp (I * θ)) * star (szegoAskey lam n (exp (I * θ))) *
        weight lam θ = ∑ j ∈ Finset.range (n + 1), star (pochhammer ((lam : ℂ) + 1) j *
          pochhammer (lam : ℂ) (n - j) / ((j.factorial : ℂ) * (n - j).factorial)) *
          (szegoAskey lam m (exp (I * θ)) * exp (-(I * j * θ)) * weight lam θ) := by
      intro θ
      have hS : szegoAskey lam n (exp (I * θ)) = ∑ j ∈ Finset.range (n + 1),
          pochhammer ((lam : ℂ) + 1) j * pochhammer (lam : ℂ) (n - j) /
            ((j.factorial : ℂ) * (n - j).factorial) * exp (I * θ) ^ j := rfl
      rw [hS, star_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul, star_pow, star_def, ← Complex.exp_conj, map_mul, Complex.conj_I,
        Complex.conj_ofReal, ← Complex.exp_nat_mul]
      ring_nf
    simp_rw [e]
    rw [intervalIntegral.integral_finsetSum fun k _ =>
      (intervalIntegrable_mul_weight hlam (by
        unfold szegoAskey; fun_prop)).const_mul _]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [intervalIntegral.integral_const_mul, integral_poly_mul_exp hlam
      (by have := Finset.mem_range.mp hj; omega), mul_zero]

end SzegoAskeyOrthogonality

end DLMF.OrthogonalPolynomials
