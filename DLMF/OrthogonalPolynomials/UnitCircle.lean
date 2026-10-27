/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Pochhammer
public import DLMF.Hypergeometric.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
/-!
# Orthogonal polynomials on the unit circle

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter DLMF.QSeries
open scoped Real Nat Topology
open DLMF.Hypergeometric

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- Reverse-conjugation at a specified degree; meaningful even if the constant
coefficient vanishes. -/
@[dlmf 18.33.E22]
def reflectedPolynomial (n : ℕ) (p : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (star (p.coeff (n - k))) * X ^ k

/-- Monic orthogonal polynomials for a probability measure supported on the unit
circle. Positive norms in every degree exclude finite support. -/
@[dlmf 18.33.E17]
def IsUnitCircleOP (μ : Measure ℂ) (p : ℕ → ℂ[X]) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ z ∂μ, ‖z‖ = 1) ∧
    (∀ n, (p n).Monic ∧ (p n).natDegree = n) ∧
    (∀ n, Integrable (fun z => ‖(p n).eval z‖ ^ 2) μ) ∧
    (∀ n, 0 < ∫ z, ‖(p n).eval z‖ ^ 2 ∂μ) ∧
    ∀ m n, m ≠ n → ∫ z, (p m).eval z * star ((p n).eval z) ∂μ = 0

@[dlmf 18.33.E25]
def verblunskyCoefficient (p : ℕ → ℂ[X]) (n : ℕ) : ℂ := -star ((p (n + 1)).eval 0)

@[dlmf 18.33.E13]
def szegoAskey (lam : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (lam + 1) k * poch lam (n - k) /
    ((k.factorial : ℂ) * (n - k).factorial) * z ^ k

@[dlmf 18.33.E15]
def szegoAskeyQ (a q : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), qPochhammer (a * q ^ 2) (q ^ 2) k *
    qPochhammer a (q ^ 2) (n - k) / (qPochhammer (q ^ 2) (q ^ 2) k *
      qPochhammer (q ^ 2) (q ^ 2) (n - k)) * (z / q) ^ k

namespace IsUnitCircleOP

variable {μ : Measure ℂ} {p : ℕ → ℂ[X]}

/-- The `L²(μ)` inner product of two polynomials. -/
def ip (μ : Measure ℂ) (f g : ℂ[X]) : ℂ := ∫ z, f.eval z * star (g.eval z) ∂μ

theorem integrable_eval_mul (h : IsUnitCircleOP μ p) (f g : ℂ[X]) :
    Integrable (fun z => f.eval z * star (g.eval z)) μ := by
  haveI := h.1
  have hc : Continuous fun z => f.eval z * star (g.eval z) :=
    (f.continuous.mul (continuous_star.comp g.continuous))
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn hc.continuousOn
  refine Integrable.of_bound hc.aestronglyMeasurable C ?_
  filter_upwards [h.2.1] with z hz
  exact hC z (by simpa using hz)

theorem ip_add_left (h : IsUnitCircleOP μ p) (f g k : ℂ[X]) :
    ip μ (f + g) k = ip μ f k + ip μ g k := by
  unfold ip
  rw [← integral_add (integrable_eval_mul h f k) (integrable_eval_mul h g k)]
  congr 1; funext z; simp [eval_add]; ring

theorem ip_sub_left (h : IsUnitCircleOP μ p) (f g k : ℂ[X]) :
    ip μ (f - g) k = ip μ f k - ip μ g k := by
  unfold ip
  rw [← integral_sub (integrable_eval_mul h f k) (integrable_eval_mul h g k)]
  congr 1; funext z; simp [eval_sub]; ring

theorem ip_C_mul_left (f k : ℂ[X]) (c : ℂ) : ip μ (C c * f) k = c * ip μ f k := by
  unfold ip
  rw [← integral_const_mul]
  congr 1; funext z; simp; ring

theorem ip_C_mul_right (f k : ℂ[X]) (c : ℂ) : ip μ f (C c * k) = star c * ip μ f k := by
  unfold ip
  rw [← integral_const_mul]
  congr 1; funext z; simp; ring

theorem ip_add_right (h : IsUnitCircleOP μ p) (f g k : ℂ[X]) :
    ip μ f (g + k) = ip μ f g + ip μ f k := by
  unfold ip
  rw [← integral_add (integrable_eval_mul h f g) (integrable_eval_mul h f k)]
  congr 1; funext z; simp [eval_add]; ring

theorem ip_sum_right (h : IsUnitCircleOP μ p) (f : ℂ[X]) {ι : Type*} (s : Finset ι)
    (g : ι → ℂ[X]) : ip μ f (∑ i ∈ s, g i) = ∑ i ∈ s, ip μ f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ip_add_right h, ih]

theorem ip_swap (f g : ℂ[X]) : ip μ g f = star (ip μ f g) := by
  unfold ip
  change _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  congr 1; funext z; simp [mul_comm]

theorem ip_X_mul (h : IsUnitCircleOP μ p) (f g : ℂ[X]) : ip μ (X * f) (X * g) = ip μ f g := by
  unfold ip
  refine integral_congr_ae ?_
  filter_upwards [h.2.1] with z hz
  simp only [eval_mul, eval_X, star_mul']
  have : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  linear_combination (f.eval z * star (g.eval z)) * this

theorem ip_zero_right (f : ℂ[X]) : ip μ f 0 = 0 := by simp [ip]

theorem ip_zero_left (f : ℂ[X]) : ip μ 0 f = 0 := by simp [ip]

/-- Peeling off the leading term against the monic `p d`. -/
theorem exists_decomp (h : IsUnitCircleOP μ p) (q : ℂ[X]) :
    ∃ t : ℂ[X], q = C q.leadingCoeff * p q.natDegree + t ∧
      (t = 0 ∨ t.natDegree < q.natDegree) := by
  set d := q.natDegree with hd
  have hm := (h.2.2.1 d).1
  have hdeg := (h.2.2.1 d).2
  refine ⟨q - C q.leadingCoeff * p d, by ring, ?_⟩
  by_cases ht : q - C q.leadingCoeff * p d = 0
  · exact Or.inl ht
  right
  by_cases hq : q = 0
  · simp [hq] at ht
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · exfalso; apply ht
    have hp0 : p d = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm (by rw [hdeg, h0])
    rw [hp0, mul_one, Polynomial.eq_C_of_natDegree_eq_zero (show q.natDegree = 0 from h0),
      leadingCoeff_C, sub_self]
  · have hlt : (q - C q.leadingCoeff * p d).degree < q.degree := by
      apply Polynomial.degree_sub_lt_left
      · rw [degree_C_mul (leadingCoeff_ne_zero.mpr hq), degree_eq_natDegree hm.ne_zero, hdeg,
          degree_eq_natDegree hq]
      · exact hq
      · rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hq)),
          hm.leadingCoeff, mul_one]
    exact natDegree_lt_natDegree ht hlt

/-- `p m` is orthogonal to every polynomial of lower degree. -/
theorem ip_p_eq_zero (h : IsUnitCircleOP μ p) (m : ℕ) :
    ∀ q : ℂ[X], q.natDegree < m → ip μ (p m) q = 0 := by
  intro q
  induction hd : q.natDegree using Nat.strong_induction_on generalizing q with
  | _ d ih =>
    intro hdm
    obtain ⟨t, hqt, ht⟩ := exists_decomp h q
    have horth : ip μ (p m) (p d) = 0 := h.2.2.2.2.2 m d (by omega)
    rw [hqt, ip_add_right h, ip_C_mul_right, hd, horth, mul_zero, zero_add]
    rcases ht with ht | ht
    · rw [ht, ip_zero_right]
    · exact ih _ (by omega) t rfl (by omega)

end IsUnitCircleOP

theorem reflectedPolynomial_eval_zero (n : ℕ) (f : ℂ[X]) :
    (reflectedPolynomial n f).eval 0 = star (f.coeff n) := by
  unfold reflectedPolynomial
  rw [eval_finsetSum, Finset.sum_range_succ']
  simp

theorem natDegree_reflectedPolynomial_le (n : ℕ) (f : ℂ[X]) :
    (reflectedPolynomial n f).natDegree ≤ n := by
  unfold reflectedPolynomial
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem coeff_reflectedPolynomial (n : ℕ) (f : ℂ[X]) (j : ℕ) :
    (reflectedPolynomial n f).coeff j = if j ≤ n then star (f.coeff (n - j)) else 0 := by
  unfold reflectedPolynomial
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with hj
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hj'; simp at hj'; omega
  · refine Finset.sum_eq_zero fun k hk => ?_
    have := Finset.mem_range.mp hk
    simp only [ite_eq_right_iff]; intro h; omega

theorem reflectedPolynomial_add (n : ℕ) (f g : ℂ[X]) :
    reflectedPolynomial n (f + g) = reflectedPolynomial n f + reflectedPolynomial n g := by
  ext j; simp only [coeff_add, coeff_reflectedPolynomial]; split_ifs <;> simp

theorem reflectedPolynomial_C_mul (n : ℕ) (c : ℂ) (f : ℂ[X]) :
    reflectedPolynomial n (C c * f) = C (star c) * reflectedPolynomial n f := by
  ext j; simp only [coeff_C_mul, coeff_reflectedPolynomial]; split_ifs <;> simp [mul_comm]

theorem reflectedPolynomial_X_mul {n : ℕ} {f : ℂ[X]} :
    reflectedPolynomial (n + 1) (X * f) = reflectedPolynomial n f := by
  ext j
  simp only [coeff_reflectedPolynomial]
  split_ifs with h1 h2 h2
  · rw [show n + 1 - j = (n - j) + 1 by omega, coeff_X_mul]
  · rw [show j = n + 1 by omega, Nat.sub_self, mul_comm, coeff_mul_X_zero, star_zero]
  · omega
  · rfl

theorem reflectedPolynomial_reflectedPolynomial {n : ℕ} {f : ℂ[X]} (hf : f.natDegree ≤ n) :
    reflectedPolynomial (n + 1) (reflectedPolynomial n f) = X * f := by
  ext j
  simp only [coeff_reflectedPolynomial]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero, show ¬ (n + 1 ≤ n) by omega, star_zero,
      mul_comm X f, coeff_mul_X_zero]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [coeff_X_mul]
    split_ifs with h1 h2
    · rw [show n - (n + 1 - (i + 1)) = i by omega, star_star]
    · omega
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]

/-- On the unit circle, `f*(z) = zⁿ conj(f(z))`. -/
theorem reflectedPolynomial_eval_of_norm_eq_one {n : ℕ} {f : ℂ[X]} (hf : f.natDegree ≤ n) {z : ℂ}
    (hz : ‖z‖ = 1) : (reflectedPolynomial n f).eval z = z ^ n * star (f.eval z) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hstar : star z = z⁻¹ := by
    rw [Complex.star_def, Complex.inv_def, Complex.normSq_eq_norm_sq, hz]; simp
  unfold reflectedPolynomial
  rw [eval_finsetSum, eval_eq_sum_range' (n := n + 1) (by omega), star_sum, Finset.mul_sum]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega]
  simp only [eval_mul, eval_C, eval_pow, eval_X, star_mul', star_pow, hstar]
  rw [show z ^ n = z ^ (n - k) * z ^ k by rw [← pow_add, Nat.sub_add_cancel hkn]]
  rw [inv_pow, Nat.sub_sub_self hkn]
  field_simp


namespace IsUnitCircleOP

variable {μ : Measure ℂ} {p : ℕ → ℂ[X]}

theorem ip_self_ne_zero (h : IsUnitCircleOP μ p) (d : ℕ) : ip μ (p d) (p d) ≠ 0 := by
  have hpos := h.2.2.2.2.1 d
  have heq : ip μ (p d) (p d) = ((∫ z, ‖(p d).eval z‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    unfold ip
    rw [← integral_complex_ofReal]
    congr 1; funext z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [heq]
  exact ofReal_ne_zero.mpr hpos.ne'

/-- A polynomial orthogonal to all polynomials of degree below `n` and of degree below `n` is
zero. -/
theorem eq_zero_of_ip_eq_zero (h : IsUnitCircleOP μ p) {n : ℕ} {s : ℂ[X]} (hs : s.natDegree < n)
    (horth : ∀ g : ℂ[X], g.natDegree < n → ip μ s g = 0) : s = 0 := by
  by_contra hs0
  set d := s.natDegree
  obtain ⟨t, hst, ht⟩ := exists_decomp h s
  have h1 := horth (p d) (by rw [(h.2.2.1 d).2]; exact hs)
  have h2 : ip μ t (p d) = 0 := by
    rcases ht with ht | ht
    · rw [ht, ip_zero_left]
    · rw [ip_swap, ip_p_eq_zero h d t ht, star_zero]
  rw [hst, ip_add_left h, ip_C_mul_left, h2, add_zero] at h1
  rcases mul_eq_zero.mp h1 with h3 | h3
  · exact hs0 (leadingCoeff_eq_zero.mp h3)
  · exact ip_self_ne_zero h d h3

/-- Orthogonality to the monomials `X^i`, `i < n`, gives orthogonality to all lower degrees. -/
theorem ip_eq_zero_of_monomials (h : IsUnitCircleOP μ p) {n : ℕ} {s : ℂ[X]}
    (hmono : ∀ i < n, ip μ s (X ^ i) = 0) (g : ℂ[X]) (hg : g.natDegree < n) : ip μ s g = 0 := by
  rw [as_sum_range' g n hg, ip_sum_right h]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← C_mul_X_pow_eq_monomial, ip_C_mul_right, hmono i (Finset.mem_range.mp hi), mul_zero]

/-- `p n^*` is orthogonal to `X^j` for `1 ≤ j ≤ n`. -/
theorem ip_reflected_X_pow (h : IsUnitCircleOP μ p) {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ip μ (reflectedPolynomial n (p n)) (X ^ j) = 0 := by
  have hdeg : (p n).natDegree ≤ n := (h.2.2.1 n).2.le
  have key : ip μ (reflectedPolynomial n (p n)) (X ^ j) = star (ip μ (p n) (X ^ (n - j))) := by
    unfold ip
    change _ = (starRingEnd ℂ) _
    rw [← integral_conj]
    refine integral_congr_ae ?_
    filter_upwards [h.2.1] with z hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz
    have hstar : star z = z⁻¹ := by
      rw [Complex.star_def, Complex.inv_def, Complex.normSq_eq_norm_sq, hz]; simp
    rw [reflectedPolynomial_eval_of_norm_eq_one hdeg hz]
    simp only [eval_pow, eval_X, star_pow, hstar, map_mul, map_pow]
    rw [map_inv₀]
    simp only [← Complex.star_def, hstar, inv_inv]
    rw [show z ^ n = z ^ (n - j) * z ^ j by rw [← pow_add, Nat.sub_add_cancel hjn], inv_pow]
    field_simp
  rw [key, ip_p_eq_zero h n _ (by rw [natDegree_X_pow]; omega), star_zero]

theorem szego (h : IsUnitCircleOP μ p) (n : ℕ) :
    p (n + 1) = X * p n + C ((p (n + 1)).eval 0) * reflectedPolynomial n (p n) := by
  set c0 := (p (n + 1)).eval 0
  set R := reflectedPolynomial n (p n)
  set r := p (n + 1) - X * p n - C c0 * R with hr
  have hmn := h.2.2.1 n
  have hmn1 := h.2.2.1 (n + 1)
  -- degree of r
  have hq : (p (n + 1) - X * p n).natDegree ≤ n := by
    have hX : (X * p n).Monic := monic_X.mul hmn.1
    have hXdeg : (X * p n).natDegree = n + 1 := by
      rw [natDegree_mul monic_X.ne_zero hmn.1.ne_zero, natDegree_X, hmn.2]; ring
    by_cases h0 : p (n + 1) - X * p n = 0
    · rw [h0, natDegree_zero]; omega
    have hlt : (p (n + 1) - X * p n).degree < (p (n + 1)).degree :=
      degree_sub_lt_left (by rw [degree_eq_natDegree hmn1.1.ne_zero, degree_eq_natDegree hX.ne_zero,
        hmn1.2, hXdeg]) hmn1.1.ne_zero (by rw [hmn1.1.leadingCoeff, hX.leadingCoeff])
    have := natDegree_lt_natDegree h0 hlt
    rw [hmn1.2] at this; omega
  have hrdeg : r.natDegree ≤ n :=
    (natDegree_sub_le _ _).trans (max_le hq ((natDegree_C_mul_le _ _).trans
      (natDegree_reflectedPolynomial_le n _)))
  have hr0 : r.eval 0 = 0 := by
    simp only [hr, eval_sub, eval_mul, eval_X, zero_mul, sub_zero, eval_C, R,
      reflectedPolynomial_eval_zero]
    have hc : (p n).coeff n = 1 := by have := hmn.1.coeff_natDegree; rwa [hmn.2] at this
    rw [hc, star_one, mul_one, sub_self]
  have hrX : ∀ j : ℕ, 1 ≤ j → j ≤ n → ip μ r (X ^ j) = 0 := by
    intro j hj1 hjn
    rw [hr, ip_sub_left h, ip_sub_left h, ip_C_mul_left, ip_reflected_X_pow h hj1 hjn,
      ip_p_eq_zero h (n + 1) _ (by rw [natDegree_X_pow]; omega),
      show (X : ℂ[X]) ^ j = X * X ^ (j - 1) by rw [← pow_succ', Nat.sub_add_cancel hj1],
      ip_X_mul h, ip_p_eq_zero h n _ (by rw [natDegree_X_pow]; omega)]
    ring
  obtain ⟨t, ht⟩ : X ∣ r := X_dvd_iff.mpr (by rw [coeff_zero_eq_eval_zero, hr0])
  have ht0 : t = 0 := by
    by_contra htne
    have htdeg : t.natDegree < n := by
      have := natDegree_mul X_ne_zero htne
      rw [← ht, natDegree_X] at this; omega
    refine htne (eq_zero_of_ip_eq_zero h htdeg (ip_eq_zero_of_monomials h ?_))
    intro i hi
    rw [← ip_X_mul h, ← ht, ← pow_succ']
    exact hrX (i + 1) (by omega) (by omega)
  rw [ht0, mul_zero, hr] at ht
  linear_combination ht

theorem ip_reflected_self (h : IsUnitCircleOP μ p) (n : ℕ) :
    ip μ (reflectedPolynomial n (p n)) (reflectedPolynomial n (p n)) = ip μ (p n) (p n) := by
  have hdeg : (p n).natDegree ≤ n := (h.2.2.1 n).2.le
  unfold ip
  refine integral_congr_ae ?_
  filter_upwards [h.2.1] with z hz
  rw [reflectedPolynomial_eval_of_norm_eq_one hdeg hz]
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  simp only [star_mul', star_pow, star_star]
  have : z ^ n * star z ^ n = 1 := by rw [← mul_pow, hzz, one_pow]
  linear_combination (star ((p n).eval z) * (p n).eval z) * this

theorem ip_self_eq_ofReal (h : IsUnitCircleOP μ p) (f : ℂ[X]) :
    ip μ f f = ((∫ z, ‖f.eval z‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  unfold ip
  rw [← integral_complex_ofReal]
  congr 1; funext z
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem ip_succ_self (h : IsUnitCircleOP μ p) (n : ℕ) :
    ip μ (p (n + 1)) (p (n + 1)) =
      (1 - (p (n + 1)).eval 0 * star ((p (n + 1)).eval 0)) * ip μ (p n) (p n) := by
  set c0 := (p (n + 1)).eval 0
  set R := reflectedPolynomial n (p n)
  have hs : p (n + 1) = X * p n + C c0 * R := szego h n
  have hR : ip μ (p (n + 1)) R = 0 :=
    ip_p_eq_zero h (n + 1) R ((natDegree_reflectedPolynomial_le n (p n)).trans_lt (by omega))
  have hXR : ip μ (X * p n) R = -c0 * ip μ (p n) (p n) := by
    have : X * p n = p (n + 1) - C c0 * R := by rw [hs]; ring
    rw [this, ip_sub_left h, hR, ip_C_mul_left, ip_reflected_self h]; ring
  have hRX : ip μ R (X * p n) = -star c0 * ip μ (p n) (p n) := by
    rw [ip_swap, hXR, star_mul', star_neg]
    have hN := ip_self_eq_ofReal h (p n)
    rw [hN, Complex.star_def, Complex.conj_ofReal]
  have e1 : ip μ (p (n + 1)) (p (n + 1)) =
      ip μ (p (n + 1)) (X * p n) + star c0 * ip μ (p (n + 1)) R := by
    conv_lhs => arg 3; rw [hs]
    rw [ip_add_right h, ip_C_mul_right]
  have e2 : ip μ (p (n + 1)) (X * p n) = ip μ (X * p n) (X * p n) + c0 * ip μ R (X * p n) := by
    conv_lhs => arg 2; rw [hs]
    rw [ip_add_left h, ip_C_mul_left]
  rw [e1, e2, hR, ip_X_mul h, hRX]
  ring

/-- The norm ratio, as a helper for 18.33.25 and 18.33.26. -/
lemma norm_ratio_aux (h : IsUnitCircleOP μ p) (n : ℕ) :
    (∫ z, ‖(p (n + 1)).eval z‖ ^ 2 ∂μ) =
      (1 - ‖verblunskyCoefficient p n‖ ^ 2) * ∫ z, ‖(p n).eval z‖ ^ 2 ∂μ := by
  have h1 := ip_succ_self h n
  rw [ip_self_eq_ofReal h, ip_self_eq_ofReal h] at h1
  have hc : (p (n + 1)).eval 0 * star ((p (n + 1)).eval 0) =
      ((‖verblunskyCoefficient p n‖ ^ 2 : ℝ) : ℂ) := by
    rw [verblunskyCoefficient, norm_neg, norm_star, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [hc] at h1
  exact_mod_cast h1

theorem norm_sq_eq_mul_star (a : ℂ) : (((‖a‖ ^ 2 : ℝ)) : ℂ) = a * star a := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

end IsUnitCircleOP

open IsUnitCircleOP

@[dlmf 18.33.E23]
theorem szego_recurrence {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    p (n + 1) = X * p n - C (star (verblunskyCoefficient p n)) * reflectedPolynomial n (p n) := by
  rw [szego h n, verblunskyCoefficient, star_neg, star_star, map_neg]
  ring

@[dlmf 18.33.E24]
theorem szego_reflected_recurrence {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    reflectedPolynomial (n + 1) (p (n + 1)) = reflectedPolynomial n (p n) -
      C (verblunskyCoefficient p n) * X * p n := by
  conv_lhs => rw [szego h n]
  rw [reflectedPolynomial_add, reflectedPolynomial_X_mul, reflectedPolynomial_C_mul,
    reflectedPolynomial_reflectedPolynomial (h.2.2.1 n).2.le, verblunskyCoefficient, map_neg]
  ring

@[dlmf 18.33.E25]
theorem verblunskyCoefficient_norm_lt_one {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    ‖verblunskyCoefficient p n‖ < 1 := by
  have h1 := norm_ratio_aux h n
  have hp1 := h.2.2.2.2.1 (n + 1)
  have hp0 := h.2.2.2.2.1 n
  have hlt : ‖verblunskyCoefficient p n‖ ^ 2 < 1 := by
    by_contra hge
    push Not at hge
    rw [h1] at hp1
    nlinarith
  have := norm_nonneg (verblunskyCoefficient p n)
  nlinarith

@[dlmf 18.33.E26]
theorem unitCircle_norm_ratio {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    (∫ z, ‖(p (n + 1)).eval z‖ ^ 2 ∂μ) =
      (1 - ‖verblunskyCoefficient p n‖ ^ 2) * ∫ z, ‖(p n).eval z‖ ^ 2 ∂μ := by
  exact norm_ratio_aux h n

@[dlmf 18.33.E27]
theorem inverse_szego_recurrence {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    C (1 - ((‖verblunskyCoefficient p n‖ ^ 2 : ℝ) : ℂ)) * X * p n = p (n + 1) +
      C (star (verblunskyCoefficient p n)) * reflectedPolynomial (n + 1) (p (n + 1)) := by
  rw [szego_reflected_recurrence h n]
  conv_rhs => arg 1; rw [szego_recurrence h n]
  rw [norm_sq_eq_mul_star]
  simp only [map_sub, map_one, map_mul]
  ring

@[dlmf 18.33.E28]
theorem inverse_reflected_szego_recurrence {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    C (1 - ((‖verblunskyCoefficient p n‖ ^ 2 : ℝ) : ℂ)) * reflectedPolynomial n (p n) =
      reflectedPolynomial (n + 1) (p (n + 1)) + C (verblunskyCoefficient p n) * p (n + 1) := by
  rw [szego_reflected_recurrence h n]
  conv_rhs => arg 2; rw [szego_recurrence h n]
  rw [norm_sq_eq_mul_star]
  simp only [map_sub, map_one, map_mul]
  ring

@[dlmf 18.33.E30]
theorem unitCircle_three_term_recurrence {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    C (star (verblunskyCoefficient p n)) * p (n + 2) =
      (C (star (verblunskyCoefficient p (n + 1))) + C (star (verblunskyCoefficient p n)) * X) * p (n + 1) -
      C (star (verblunskyCoefficient p (n + 1)) * (1 - (‖verblunskyCoefficient p n‖ ^ 2 : ℝ))) * X * p n := by
  have e23 := szego_recurrence h (n + 1)
  have e27 := inverse_szego_recurrence h n
  simp only [map_mul] at e27 ⊢
  push_cast at e27 ⊢
  linear_combination (C (star (verblunskyCoefficient p n))) * e23 +
    (C (star (verblunskyCoefficient p (n + 1)))) * e27

@[dlmf 18.33.vi]
theorem verblunsky_theorem (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ < 1) :
    ∃! μ : Measure ℂ, ∃ p : ℕ → ℂ[X], IsUnitCircleOP μ p ∧ verblunskyCoefficient p = a := by
  sorry

@[dlmf 18.33.E14]
theorem szegoAskey_orthogonal {lam : ℝ} (hlam : -1 / 2 < lam) {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), szegoAskey lam m (exp (I * θ)) *
      star (szegoAskey lam n (exp (I * θ))) * (Real.rpow (1 - Real.cos θ) lam : ℂ) = 0 := by
  sorry

@[dlmf 18.33.E16]
theorem szegoAskeyQ_orthogonal {a q : ℝ} (hq : 0 < q) (hq1 : q < 1) (ha : |a * q| < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), szegoAskeyQ a q m (exp (I * θ)) *
      star (szegoAskeyQ a q n (exp (I * θ))) *
      (‖qPochhammerInf (q * exp (I * θ)) (q ^ 2) / qPochhammerInf (a * q * exp (I * θ)) (q ^ 2)‖ ^ 2 : ℝ) = 0 := by
  sorry


end DLMF.OrthogonalPolynomials
