/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Appell.ComposedF4
import DLMF.Hypergeometric.FiniteConvolution

/-!
# Burchnall–Chaundy expansion of Appell F4

For regular lower parameters, the composed Appell function
`F₄(a,b;c,c';X(1-Y),Y(1-X))` is a convergent sum of products of two Gauss functions
with parameters shifted by the summation index (DLMF 16.16.7).

Euler's transformation gives the finite coefficient identity. The coefficient factors
into two Pochhammer ratios and shifted binomial coefficients, yielding absolute
convergence of the three-index series near the origin. Regrouping by the monomial degrees
identifies its sum with the binomial expansion of F4; regrouping by the shift index gives
the Gauss products. This proof uses the project's Bailey coefficient comparison
`appellF4_term`, the regularized Gauss Euler transformation, and Mathlib's unconditional
summation and power-series convolution APIs.

* `regularized_euler_binomial_convolution`: Euler's coefficient identity with a binomial factor.
* `BurchnallChaundy.coefficient_sum`: the finite composed-F4 coefficient identity.
* `BurchnallChaundy.exists_summable_term`: absolute convergence of the expanded series.
* `BurchnallChaundy.hasSum_expansion`: the Gauss-product expansion.
-/

public noncomputable section
open Complex Filter Set Finset Polynomial
open scoped Topology Nat Real
namespace DLMF.Hypergeometric

set_option maxHeartbeats 1000000 in
/-- Euler's transformation after convolution with an arbitrary binomial series. -/
theorem regularized_euler_binomial_convolution (a b c d : ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1), pochhammer a k * pochhammer b k / (k ! * Gamma (c + k)) *
        (pochhammer d (n - k) / (n - k)!) =
      ∑ k ∈ range (n + 1), pochhammer (c - a) k * pochhammer (c - b) k /
        (k ! * Gamma (c + k)) *
        (pochhammer (d + a + b - c) (n - k) / (n - k)!) := by
  have h := Complex.powerSeries_coefficients_unique
    (f := fun z => regularizedGaussHGFun (c - a) (c - b) c z *
      (1 - z) ^ (-(d + a + b - c)))
    (c := fun n => ∑ k ∈ range (n + 1), pochhammer a k * pochhammer b k /
      (k ! * Gamma (c + k)) * (pochhammer d (n - k) / (n - k)!))
    (d := fun n => ∑ k ∈ range (n + 1), pochhammer (c - a) k * pochhammer (c - b) k /
      (k ! * Gamma (c + k)) * (pochhammer (d + a + b - c) (n - k) / (n - k)!))
    (fun z hz => ?_)
    (fun z hz => Complex.hasSum_powerSeries_convolution
      (c := fun k => pochhammer (c - a) k * pochhammer (c - b) k /
        (k ! * Gamma (c + k)))
      (d := fun k => pochhammer (d + a + b - c) k / k !)
      (z := z)
      (hasSum_regularizedGaussHypergeometricFun_coeff (c - a) (c - b) c hz)
      (hasSum_pochhammer_div_factorial (β := d + a + b - c) hz))
  · exact congrFun h n
  have hconv := Complex.hasSum_powerSeries_convolution
    (hasSum_regularizedGaussHypergeometricFun_coeff a b c hz)
    (hasSum_pochhammer_div_factorial (β := d) hz)
  have hz0 : 1 - z ≠ 0 := sub_ne_zero.mpr (ne_of_apply_ne norm (by simpa using hz.ne)).symm
  rw [regularizedGaussHypergeometricFun_euler a b c hz] at hconv
  have heq : (1 - z) ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b) c z *
      (1 - z) ^ (-d) = regularizedGaussHGFun (c - a) (c - b) c z *
        (1 - z) ^ (-(d + a + b - c)) := by
    rw [mul_comm ((1 - z) ^ (c - a - b)), mul_assoc, ← cpow_add _ _ hz0]
    congr 2
    ring
  rwa [heq] at hconv


namespace BurchnallChaundy

/-- The inner Chu–Vandermonde sum in the general composed F4 coefficient. -/
private lemma inner_sum {a b c c' : ℂ} (hc : ∀ k, pochhammer c k ≠ 0)
    (hc' : ∀ k, pochhammer c' k ≠ 0) (t s f : ℕ) :
    ∑ d ∈ Finset.range (s + 1), appellF4Term a b c c' (t + s) (s + f) (t + d) (s + f - d) =
      pochhammer a (t + s + f) * pochhammer b (t + s + f) *
        pochhammer (2 - c - c' - ((t + s : ℕ) : ℂ) - ((s + f : ℕ) : ℂ)) s /
        (pochhammer c (t + s) * pochhammer c' (s + f) * (f ! * t ! * s !)) := by
  have hv := pochhammer_add_binomial_sum (1 - c' - ((s + f : ℕ) : ℂ)) (1 - c - ((t + s : ℕ) : ℂ)) s
  rw [show 1 - c' - ((s + f : ℕ) : ℂ) + (1 - c - ((t + s : ℕ) : ℂ)) =
    2 - c - c' - ((t + s : ℕ) : ℂ) - ((s + f : ℕ) : ℂ) by ring] at hv
  rw [← hv, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hds : d ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  obtain ⟨e, rfl⟩ : ∃ e, s = d + e := ⟨s - d, by omega⟩
  unfold appellF4Term
  rw [show t + (d + e) - (t + d) = e by omega, show d + e + f - d = e + f by omega,
    show d + e + f - (e + f) = d by omega, appellF4_term a b c c' hc hc' t d e f,
    show d + e - d = e by omega, show t + d + e + f = t + (d + e) + f by ring,
    show t + d + e = t + (d + e) by ring]
  ring

/-- The composed F4 coefficient as a single finite convolution when `M ≤ N`. -/
private lemma composed_coefficient_eq_outer_sum {a b c c' : ℂ}
    (hc : ∀ k, pochhammer c k ≠ 0) (hc' : ∀ k, pochhammer c' k ≠ 0)
    {M N : ℕ} (hMN : M ≤ N) :
    ∑ m ∈ range (M + 1), ∑ n ∈ range (N + 1), appellF4Term a b c c' M N m n =
      ∑ t ∈ range (M + 1), pochhammer a (N + t) * pochhammer b (N + t) *
        pochhammer (2 - c - c' - (M : ℂ) - (N : ℂ)) (M - t) /
        (pochhammer c M * pochhammer c' N * ((N - (M - t))! * t ! * (M - t)!)) := by
  have h1 : ∀ m ∈ Finset.range (M + 1), ∑ n ∈ Finset.range (N + 1), appellF4Term a b c c' M N m n =
      ∑ k ∈ Finset.range (m + 1), appellF4Term a b c c' M N m (N - m + k) := by
    intro m hm
    have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [show N + 1 = (N - m) + (m + 1) by omega, Finset.sum_range_add]
    rw [Finset.sum_eq_zero (fun n hn => ?_), zero_add]
    have hn' : n < N - m := Finset.mem_range.mp hn
    unfold appellF4Term
    rw [Nat.choose_eq_zero_of_lt (show m < N - n by omega)]
    simp
  rw [Finset.sum_congr rfl h1]
  have h2 := Finset.sum_range_diag_flip (M + 1)
      (fun t d => appellF4Term a b c c' M N (t + d) (N - d))
  rw [show (∑ m ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (m + 1),
      appellF4Term a b c c' M N m (N - m + k)) = ∑ m ∈ Finset.range (M + 1),
      ∑ k ∈ Finset.range (m + 1), appellF4Term a b c c' M N (k + (m - k)) (N - (m - k)) by
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun k hk => ?_
    have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show k + (m - k) = m by omega, show N - (m - k) = N - m + k by omega], h2]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htM : t ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  have h3 := inner_sum (a := a) (b := b) hc hc' t (M - t) (N - (M - t))
  rw [show t + (M - t) + (N - (M - t)) = N + t by omega, show t + (M - t) = M by omega,
    show M - t + (N - (M - t)) = N by omega] at h3
  rw [show M + 1 - t = M - t + 1 by omega, h3]


/-- A coefficient in the three-index Gauss-product expansion of F4. -/
def coefficient (a b c c' : ℂ) (k m n : ℕ) : ℂ :=
  pochhammer a k * pochhammer b k * pochhammer (a + b - c - c' + 1) k /
    (pochhammer c k * pochhammer c' k * k.factorial) *
    gaussHypergeometricCoeff (a + k) (b + k) (c + k) m *
    gaussHypergeometricCoeff (a + k) (b + k) (c' + k) n

/-- The coefficient consists of its shift factor and two Gauss coefficients. -/
lemma coefficient_def (a b c c' : ℂ) (k m n : ℕ) :
    coefficient a b c c' k m n =
      pochhammer a k * pochhammer b k * pochhammer (a + b - c - c' + 1) k /
        (pochhammer c k * pochhammer c' k * k.factorial) *
        gaussHypergeometricCoeff (a + k) (b + k) (c + k) m *
        gaussHypergeometricCoeff (a + k) (b + k) (c' + k) n := by rfl

/-- Factoring the coefficients separates regular parameter ratios from shifted binomials. -/
lemma coefficient_factorization (a b c c' : ℂ) (k m n : ℕ) :
    coefficient a b c c' k m n =
      (pochhammer a (k + m) / pochhammer c (k + m)) *
      (pochhammer b (k + n) / pochhammer c' (k + n)) *
      (pochhammer (a + k) n / (n ! : ℂ)) *
      (pochhammer (b + k) m / (m ! : ℂ)) *
      (pochhammer (a + b - c - c' + 1) k / (k ! : ℂ)) := by
  simp only [coefficient, gaussHypergeometricCoeff, pochhammer_add, div_eq_mul_inv,
    mul_inv_rev]
  ring

/-- A geometric majorant for the three-index Burchnall–Chaundy coefficient family. -/
lemma exists_norm_coefficient_le (a b c c' : ℂ) (hc : AppellRegular c)
    (hc' : AppellRegular c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k m n : ℕ, ‖coefficient a b c c' k m n‖ ≤
      C * (16 * (1 + ‖a + b - c - c' + 1‖)) ^ k *
        (4 * (1 + ‖b‖)) ^ m * (4 * (1 + ‖a‖)) ^ n := by
  obtain ⟨Ca, hCa, hA⟩ := norm_pochhammer_le_mul_norm_pochhammer a c hc (σ := 2) (by norm_num)
  obtain ⟨Cb, hCb, hB⟩ := norm_pochhammer_le_mul_norm_pochhammer b c' hc' (σ := 2) (by norm_num)
  have hratA (j : ℕ) : ‖pochhammer a j / pochhammer c j‖ ≤ Ca * 2 ^ j := by
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (pochhammer_ne_zero_of_not_neg_nat hc j))]
    exact hA j
  have hratB (j : ℕ) : ‖pochhammer b j / pochhammer c' j‖ ≤ Cb * 2 ^ j := by
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (pochhammer_ne_zero_of_not_neg_nat hc' j))]
    exact hB j
  refine ⟨Ca * Cb, mul_nonneg hCa hCb, fun k m n => ?_⟩
  have hbin (p q : ℕ) : ((p + q).choose p : ℝ) ≤ 2 ^ (p + q) := by
    exact_mod_cast Nat.choose_le_two_pow (p + q) p
  have htop : ‖pochhammer (a + b - c - c' + 1) k / (k ! : ℂ)‖ ≤
      (1 + ‖a + b - c - c' + 1‖) ^ k := by
    simpa only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, add_zero,
      mul_one] using
      norm_pochhammer_add_div_factorial_le (a + b - c - c' + 1) 0 k
  rw [coefficient_factorization]
  simp only [norm_mul]
  calc ‖pochhammer a (k + m) / pochhammer c (k + m)‖ *
          ‖pochhammer b (k + n) / pochhammer c' (k + n)‖ *
          ‖pochhammer (a + k) n / (n ! : ℂ)‖ *
          ‖pochhammer (b + k) m / (m ! : ℂ)‖ *
          ‖pochhammer (a + b - c - c' + 1) k / (k ! : ℂ)‖
      ≤ (Ca * 2 ^ (k + m)) * (Cb * 2 ^ (k + n)) *
          ((1 + ‖a‖) ^ n * ((k + n).choose k : ℝ)) *
          ((1 + ‖b‖) ^ m * ((k + m).choose k : ℝ)) *
          (1 + ‖a + b - c - c' + 1‖) ^ k := by
            exact mul_le_mul
              (mul_le_mul
                (mul_le_mul
                  (mul_le_mul (hratA _) (hratB _) (norm_nonneg _) (by positivity))
                  (norm_pochhammer_add_div_factorial_le a k n) (norm_nonneg _) (by positivity))
                (norm_pochhammer_add_div_factorial_le b k m) (norm_nonneg _) (by positivity))
              htop (norm_nonneg _) (by positivity)
      _ ≤ (Ca * 2 ^ (k + m)) * (Cb * 2 ^ (k + n)) *
          ((1 + ‖a‖) ^ n * 2 ^ (k + n)) *
          ((1 + ‖b‖) ^ m * 2 ^ (k + m)) *
          (1 + ‖a + b - c - c' + 1‖) ^ k := by
            gcongr
            exacts [hbin k n, hbin k m]
      _ = _ := by
        rw [show (16 : ℝ) = 2 * 2 * 2 * 2 by norm_num,
          show (4 : ℝ) = 2 * 2 by norm_num]
        simp only [mul_pow, pow_add]
        ring

/-- Euler's convolution identifies the remaining finite outer sum. -/
private lemma outer_sum_eq_coefficient_sum (a b c c' : ℂ)
    (hc : ∀ k, pochhammer c k ≠ 0) (hc' : ∀ k, pochhammer c' k ≠ 0)
    {M N : ℕ} (hMN : M ≤ N) :
    (∑ t ∈ range (M + 1), pochhammer a (N + t) * pochhammer b (N + t) *
        pochhammer (2 - c - c' - (M : ℂ) - (N : ℂ)) (M - t) /
        (pochhammer c M * pochhammer c' N * ((N - (M - t))! * t ! * (M - t)!))) =
      ∑ k ∈ range (M + 1), coefficient a b c c' k (M - k) (N - k) := by
  have h := regularized_euler_binomial_convolution (a + N) (b + N)
    ((N : ℂ) - M + 1) (2 - c - c' - M - N) M
  have hG : ∀ k ∈ range (M + 1), Gamma ((N : ℂ) - M + 1 + k) =
      ((N - (M - k))! : ℂ) := by
    intro k hk
    have hkM : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show (N : ℂ) - M + 1 + k = ((N - (M - k) : ℕ) : ℂ) + 1 by
      push_cast [Nat.cast_sub hkM, Nat.cast_sub (show M - k ≤ N by omega)]; ring,
      Gamma_nat_eq_factorial]
  rw [show (N : ℂ) - M + 1 - (a + N) = 1 - a - M by ring,
    show (N : ℂ) - M + 1 - (b + N) = 1 - b - M by ring,
    show 2 - c - c' - (M : ℂ) - N + (a + N) + (b + N) - (N - M + 1) =
      a + b - c - c' + 1 by ring] at h
  have hscaled := congrArg (fun w : ℂ =>
    pochhammer a N * pochhammer b N / (pochhammer c M * pochhammer c' N) * w) h
  simp only [Finset.mul_sum] at hscaled
  have hleft : (∑ t ∈ range (M + 1), pochhammer a (N + t) * pochhammer b (N + t) *
        pochhammer (2 - c - c' - (M : ℂ) - (N : ℂ)) (M - t) /
        (pochhammer c M * pochhammer c' N * ((N - (M - t))! * t ! * (M - t)!))) =
      ∑ t ∈ range (M + 1), pochhammer a N * pochhammer b N /
        (pochhammer c M * pochhammer c' N) *
        (pochhammer (a + N) t * pochhammer (b + N) t /
          (t ! * Gamma ((N : ℂ) - M + 1 + t)) *
          (pochhammer (2 - c - c' - M - N) (M - t) / (M - t)!)) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [hG t ht, pochhammer_add a N t, pochhammer_add b N t]
    ring
  rw [hleft, hscaled]
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkM : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hkN : k ≤ N := hkM.trans hMN
  have hMk : M - k ≤ M := Nat.sub_le _ _
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hkM]
  rw [hG (M - k) (Finset.mem_range.mpr (by omega))]
  rw [Nat.sub_sub_self hkM]
  have hA : pochhammer (1 - a - (M : ℂ)) (M - k) =
      (-1) ^ (M - k) * pochhammer (a + k) (M - k) := by
    have h := pochhammer_reflect (a + k) (M - k)
    rw [show 1 - (a + k) - ((M - k : ℕ) : ℂ) = 1 - a - M by
      push_cast [Nat.cast_sub hkM]; ring] at h
    exact h
  have hB : pochhammer (1 - b - (M : ℂ)) (M - k) =
      (-1) ^ (M - k) * pochhammer (b + k) (M - k) := by
    have h := pochhammer_reflect (b + k) (M - k)
    rw [show 1 - (b + k) - ((M - k : ℕ) : ℂ) = 1 - b - M by
      push_cast [Nat.cast_sub hkM]; ring] at h
    exact h
  have hAN : pochhammer a N = pochhammer a k * pochhammer (a + k) (N - k) := by
    rw [← pochhammer_add, Nat.add_sub_cancel' hkN]
  have hBN : pochhammer b N = pochhammer b k * pochhammer (b + k) (N - k) := by
    rw [← pochhammer_add, Nat.add_sub_cancel' hkN]
  have hCM : pochhammer c M = pochhammer c k * pochhammer (c + k) (M - k) := by
    rw [← pochhammer_add, Nat.add_sub_cancel' hkM]
  have hCN : pochhammer c' N = pochhammer c' k * pochhammer (c' + k) (N - k) := by
    rw [← pochhammer_add, Nat.add_sub_cancel' hkN]
  have hcm : pochhammer (c + k) (M - k) ≠ 0 := by
    intro h0
    exact hc M (by rw [hCM, h0, mul_zero])
  have hcn : pochhammer (c' + k) (N - k) ≠ 0 := by
    intro h0
    exact hc' N (by rw [hCN, h0, mul_zero])
  have hfK : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hfM : ((M - k).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (M - k).factorial_ne_zero
  have hfN : ((N - k).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (N - k).factorial_ne_zero
  simp only [coefficient, gaussHypergeometricCoeff]
  rw [hA, hB, hAN, hBN, hCM, hCN]
  have hck := hc k
  have hck' := hc' k
  generalize pochhammer c k = C0 at *
  generalize pochhammer c' k = C1 at *
  generalize pochhammer (c + k) (M - k) = C2 at *
  generalize pochhammer (c' + k) (N - k) = C3 at *
  have hs : ((-1 : ℂ) ^ (M - k)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  field_simp [hck, hck', hcm, hcn, hfK, hfM, hfN]
  linear_combination (pochhammer a k * pochhammer b k *
    pochhammer (a + k) (N - k) * pochhammer (b + k) (N - k) *
    pochhammer (a + k) (M - k) * pochhammer (b + k) (M - k) *
    pochhammer (a + b - c - c' + 1) k) * hs

/-- The coefficient identity for the general Burchnall–Chaundy expansion. -/
theorem coefficient_sum (a b c c' : ℂ) (hc : ∀ k, pochhammer c k ≠ 0)
    (hc' : ∀ k, pochhammer c' k ≠ 0) (M N : ℕ) :
    ∑ m ∈ range (M + 1), ∑ n ∈ range (N + 1), appellF4Term a b c c' M N m n =
      ∑ k ∈ range (min M N + 1), coefficient a b c c' k (M - k) (N - k) := by
  rcases le_total M N with h | h
  · rw [min_eq_left h, composed_coefficient_eq_outer_sum hc hc' h]
    exact outer_sum_eq_coefficient_sum a b c c' hc hc' h
  · rw [min_eq_right h, Finset.sum_comm]
    have he : ∀ n m, appellF4Term a b c c' M N m n = appellF4Term a b c' c N M n m := by
      intro n m
      unfold appellF4Term appellF4Coeff
      rw [add_comm m n]
      ring
    simp_rw [he]
    rw [composed_coefficient_eq_outer_sum hc' hc h,
      outer_sum_eq_coefficient_sum a b c' c hc' hc h]
    apply Finset.sum_congr rfl
    intro k _
    simp only [coefficient]
    rw [show a + b - c' - c + 1 = a + b - c - c' + 1 by ring]
    ring

/-- The three-index series before grouping the two Gauss factors. -/
def term (a b c c' X Y : ℂ) (p : ℕ × (ℕ × ℕ)) : ℂ :=
  coefficient a b c c' p.1 p.2.1 p.2.2 * X ^ (p.1 + p.2.1) * Y ^ (p.1 + p.2.2)

/-- The monomial powers include the shared shift index. -/
lemma term_def (a b c c' X Y : ℂ) (p : ℕ × (ℕ × ℕ)) :
    term a b c c' X Y p = coefficient a b c c' p.1 p.2.1 p.2.2 *
      X ^ (p.1 + p.2.1) * Y ^ (p.1 + p.2.2) := by rfl

/-- Absolute convergence of the three-index expansion on a sufficiently small bidisc. -/
lemma exists_summable_term (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    ∃ δ > 0, ∀ X Y : ℂ, ‖X‖ < δ → ‖Y‖ < δ → Summable (term a b c c' X Y) := by
  obtain ⟨C, -, hC⟩ := exists_norm_coefficient_le a b c c' hc hc'
  let R := 16 * (1 + ‖a + b - c - c' + 1‖)
  let S := 4 * (1 + ‖b‖)
  let T := 4 * (1 + ‖a‖)
  let Q := R + S + T + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith
  refine ⟨1 / (2 * Q), by positivity, fun X Y hX hY => ?_⟩
  have hXQ : Q * ‖X‖ < 1 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hX
    nlinarith
  have hYQ : Q * ‖Y‖ < 1 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hY
    nlinarith
  have hY1 : ‖Y‖ ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (norm_nonneg Y)]
  have hK : R * ‖X‖ * ‖Y‖ < 1 := by
    have hRQ : R ≤ Q := by dsimp [Q]; linarith
    have hRX : R * ‖X‖ ≤ Q * ‖X‖ := mul_le_mul_of_nonneg_right hRQ (norm_nonneg X)
    have hh : R * ‖X‖ * ‖Y‖ ≤ R * ‖X‖ :=
      mul_le_of_le_one_right (by positivity) hY1
    linarith
  have hM : S * ‖X‖ < 1 := by
    have hSQ : S ≤ Q := by dsimp [Q]; linarith
    have hh := mul_le_mul_of_nonneg_right hSQ (norm_nonneg X)
    linarith
  have hN : T * ‖Y‖ < 1 := by
    have hTQ : T ≤ Q := by dsimp [Q]; linarith
    have hh := mul_le_mul_of_nonneg_right hTQ (norm_nonneg Y)
    linarith
  have hgeo :=
    ((summable_geometric_of_lt_one (by positivity : 0 ≤ R * ‖X‖ * ‖Y‖) hK).mul_of_nonneg
      ((summable_geometric_of_lt_one (by positivity : 0 ≤ S * ‖X‖) hM).mul_of_nonneg
        (summable_geometric_of_lt_one (by positivity : 0 ≤ T * ‖Y‖) hN)
        (fun _ => by positivity) (fun _ => by positivity))
      (fun _ => by positivity) (fun _ => by positivity)).mul_left C
  apply Summable.of_norm_bounded hgeo
  rintro ⟨k, m, n⟩
  dsimp only [term]
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  calc ‖coefficient a b c c' k m n‖ * ‖X‖ ^ (k + m) * ‖Y‖ ^ (k + n)
      ≤ (C * R ^ k * S ^ m * T ^ n) * ‖X‖ ^ (k + m) * ‖Y‖ ^ (k + n) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hC k m n) (by positivity)) (by positivity)
    _ = _ := by simp only [mul_pow, pow_add]; ring

/-- The same terms indexed by their two final monomial degrees. -/
def family (a b c c' X Y : ℂ) (p : (ℕ × ℕ) × ℕ) : ℂ :=
  if p.2 ≤ p.1.1 ∧ p.2 ≤ p.1.2 then
    coefficient a b c c' p.2 (p.1.1 - p.2) (p.1.2 - p.2) * X ^ p.1.1 * Y ^ p.1.2
  else 0

/-- A final-degree coefficient is zero unless its shift lies below both degrees. -/
lemma family_def (a b c c' X Y : ℂ) (p : (ℕ × ℕ) × ℕ) :
    family a b c c' X Y p =
      if p.2 ≤ p.1.1 ∧ p.2 ≤ p.1.2 then
        coefficient a b c c' p.2 (p.1.1 - p.2) (p.1.2 - p.2) * X ^ p.1.1 * Y ^ p.1.2
      else 0 := by rfl

/-- Reindexing the three-index expansion by its monomial degrees. -/
lemma hasSum_family {a b c c' X Y v : ℂ} (h : HasSum (term a b c c' X Y) v) :
    HasSum (family a b c c' X Y) v := by
  let E : ℕ × (ℕ × ℕ) → (ℕ × ℕ) × ℕ := fun p => ((p.1 + p.2.1,p.1 + p.2.2),p.1)
  have hE : Function.Injective E := by
    rintro ⟨k, m, n⟩ ⟨l, r, s⟩ he
    simp only [E, Prod.mk.injEq] at he
    obtain ⟨⟨h1, h2⟩, h3⟩ := he
    subst l
    congr <;> omega
  apply (hE.hasSum_iff (f := family a b c c' X Y) ?_).mp
  · have heq : family a b c c' X Y ∘ E = term a b c c' X Y := by
      funext p
      simp only [Function.comp_def, family, E, Nat.le_add_right, and_self, ↓reduceIte,
        Nat.add_sub_cancel_left, term]
    rw [heq]
    exact h
  · rintro ⟨⟨M, N⟩, k⟩ hnot
    by_cases hk : k ≤ M ∧ k ≤ N
    · exfalso
      apply hnot
      exact ⟨(k,M - k,N - k), by dsimp [E]; congr <;> omega⟩
    · simp only [family, hk, ↓reduceIte]

/-- Each final-degree fiber has finite support. -/
lemma hasSum_family_fst (a b c c' X Y : ℂ) (p : ℕ × ℕ) :
    HasSum (fun k => family a b c c' X Y (p, k))
      ((∑ k ∈ range (min p.1 p.2 + 1), coefficient a b c c' k (p.1 - k) (p.2 - k)) *
        X ^ p.1 * Y ^ p.2) := by
  have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
    (s := range (min p.1 p.2 + 1))
    (f := fun k => family a b c c' X Y (p, k)) (fun k hk => by
      simp only [Finset.mem_range, not_lt] at hk
      have hn : ¬(k ≤ p.1 ∧ k ≤ p.2) := by omega
      simp only [family, hn, ↓reduceIte])
  convert hfin using 1
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hm : k ≤ p.1 ∧ k ≤ p.2 := by have hh := Finset.mem_range.mp hk; omega
  simp only [family, hm.1, hm.2, and_self, ↓reduceIte]

/-- Summing the composed F4 family over its first indices gives the diagonal convolution. -/
lemma hasSum_appellF4Family_snd (a b c c' X Y : ℂ) (hc : AppellRegular c)
    (hc' : AppellRegular c') (p : ℕ × ℕ) :
    HasSum (fun q => appellF4Family a b c c' X Y (q,p))
      ((∑ k ∈ range (min p.1 p.2 + 1), coefficient a b c c' k (p.1 - k) (p.2 - k)) *
        X ^ p.1 * Y ^ p.2) := by
  obtain ⟨M, N⟩ := p
  have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
    (s := range (M + 1) ×ˢ range (N + 1))
    (f := fun q => appellF4Family a b c c' X Y (q, (M, N))) (fun q hq => by
      obtain ⟨m, n⟩ := q
      simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hq
      unfold appellF4Family appellF4BinomialCoeff
      simp only
      rcases hq with h | h
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; simp
      · rw [ite_eq_right_of_eq_false (c := n ≤ N) _ _ (eq_false (by omega))]; simp)
  convert hfin using 1
  rw [← coefficient_sum a b c c' (pochhammer_ne_zero_of_not_neg_nat hc)
    (pochhammer_ne_zero_of_not_neg_nat hc') M N, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  unfold appellF4Family appellF4Term appellF4BinomialCoeff
  simp only [hmM, hnN, ↓reduceIte]
  ring

/-- The Gauss-series product obtained by summing each fixed diagonal-shift fiber. -/
lemma hasSum_term_fst (a b c c' X Y : ℂ) (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) (k : ℕ) :
    HasSum (fun p : ℕ × ℕ => term a b c c' X Y (k,p))
      (pochhammer a k * pochhammer b k * pochhammer (a + b - c - c'+1) k /
        (pochhammer c k * pochhammer c' k * k !) * X ^ k * Y ^ k *
          ₂F₁ (a + k) (b + k) (c + k) X * ₂F₁ (a + k) (b + k) (c' + k) Y) := by
  have hx := (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + k) (b + k) (c + k)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hX)
  have hy := (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + k) (b + k) (c' + k)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hY)
  have hs : Summable (fun p : ℕ × ℕ =>
      (gaussHypergeometricCoeff (a + k) (b + k) (c + k) p.1 * X ^ p.1) *
      (gaussHypergeometricCoeff (a + k) (b + k) (c' + k) p.2 * Y ^ p.2)) := by
    apply Summable.of_norm
    simpa only [norm_mul] using hx.summable.norm.mul_of_nonneg hy.summable.norm
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hp := (hx.mul hy hs).mul_left
    (pochhammer a k * pochhammer b k * pochhammer (a + b - c - c'+1) k /
      (pochhammer c k * pochhammer c' k * k !) * X ^ k * Y ^ k)
  convert hp using 1
  · funext p
    simp only [term, coefficient, pow_add]
    ring
  · ring

/-- The Burchnall–Chaundy Gauss-product expansion of the composed F4 series. -/
theorem hasSum_expansion (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    ∃ δ > 0, ∀ X Y : ℂ, ‖X‖ < δ → ‖Y‖ < δ →
      HasSum (fun k : ℕ => pochhammer a k * pochhammer b k * pochhammer (a + b - c - c'+1) k/
        (pochhammer c k * pochhammer c' k * k !) * X ^ k * Y ^ k*₂F₁ (a + k) (b + k) (c + k) X*
          ₂F₁ (a + k) (b + k) (c' + k) Y) (appellF4 a b c c' (X * (1 - Y)) (Y * (1 - X))) := by
  obtain ⟨δ, hδ, hterm⟩ := exists_summable_term a b c c' hc hc'
  refine ⟨min δ (1 / 1024), lt_min hδ (by norm_num), fun X Y hX hY => ?_⟩
  have hXδ : ‖X‖ < δ := hX.trans_le (min_le_left _ _)
  have hYδ : ‖Y‖ < δ := hY.trans_le (min_le_left _ _)
  have hXt : ‖X‖ < 1 / 1024 := hX.trans_le (min_le_right _ _)
  have hYt : ‖Y‖ < 1 / 1024 := hY.trans_le (min_le_right _ _)
  have hS := (hterm X Y hXδ hYδ).hasSum
  have hF := (hasSum_family hS).prod_fiberwise (hasSum_family_fst a b c c' X Y)
  have hcomposed := (summable_appellF4Family a b c c' hc hc' hXt hYt).hasSum
  have hcomposed' := (Equiv.prodComm (ℕ × ℕ) (ℕ × ℕ)).hasSum_iff.mpr hcomposed
  have hcoeff := hcomposed'.prod_fiberwise (hasSum_appellF4Family_snd a b c c' X Y hc hc')
  have hvalue := (hcomposed.prod_fiberwise
    (DLMF.Hypergeometric.hasSum_appellF4Family_fst a b c c' X Y)).tsum_eq
  have he := hF.unique hcoeff
  rw [he, ← hvalue] at hS
  exact hS.prod_fiberwise (hasSum_term_fst a b c c' X Y
    (by linarith) (by linarith))

end BurchnallChaundy

end DLMF.Hypergeometric

