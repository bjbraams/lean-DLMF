/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Polynomials.P2pEigen
public import DLMF.Lame.FourierSeries

/-!
# Lamé polynomials as normalized Lamé functions (helpers for DLMF 29.12.1–29.12.8)

The Lamé polynomial `lamePolyEk t n m` is on the real line an eigenfunction for the `m`th
eigenvalue of the problem of Table 29.3.2 of its type (`p2p_isLameEigenfunction`,
`p2p_lameEigenvalue_eq`). This file reduces its identification with the normalized Lamé
function of §29.3 to two facts about its coefficients: the normalization integral 29.3.18
equals `π/4` times the quadratic form `t.normForm` of the coefficients, and the value (or
minus the derivative) at `K` is a positive multiple of the linear form `t.signForm`
(`p2p_eq_lameEigenfunction`). The coefficients are normalized by `t.normForm = 1` and
`t.signForm > 0` (29.15.4–29.15.6 and analogues), where `t.signForm ≠ 0` follows from the
uniqueness theorem for the Lamé equation. It also provides the substitution
`φ = π/2 - am(x, k)` in the normalization integral (`p2p_integral_dn_comp`) and the
orthogonality integrals of `cos(aφ)` and `sin(aφ)` on `[0, π/2]`.
-/

@[expose] public section

open Polynomial Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set
open scoped Topology Real

noncomputable section

namespace DLMF.Lame

/-- `normForm` depends only on the coefficients `c₀, …, cₙ`. -/
lemma p2p_normForm_congr (t : LamePolyType) (k : ℝ) (n : ℕ) {c c' : ℕ → ℝ}
    (h : ∀ p ≤ n, c p = c' p) : t.normForm k n c = t.normForm k n c' := by
  have h1 : ∑ p ∈ Finset.range (n + 1), c p ^ 2 = ∑ p ∈ Finset.range (n + 1), c' p ^ 2 :=
    Finset.sum_congr rfl fun p hp => by rw [h p (by simp at hp; omega)]
  have h2 : ∑ p ∈ Finset.range n, c p * c (p + 1) = ∑ p ∈ Finset.range n, c' p * c' (p + 1) :=
    Finset.sum_congr rfl fun p hp => by
      rw [h p (by simp at hp; omega), h (p + 1) (by simp at hp; omega)]
  have h0 := h 0 (Nat.zero_le _)
  cases t <;> simp only [LamePolyType.normForm, h1, h2, h0]

/-- `normForm` is a quadratic form. -/
lemma p2p_normForm_smul (t : LamePolyType) (k : ℝ) (n : ℕ) (a : ℝ) (c : ℕ → ℝ) :
    t.normForm k n (fun p => a * c p) = a ^ 2 * t.normForm k n c := by
  have h1 : ∑ p ∈ Finset.range (n + 1), (a * c p) ^ 2 =
      a ^ 2 * ∑ p ∈ Finset.range (n + 1), c p ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
  have h2 : ∑ p ∈ Finset.range n, a * c p * (a * c (p + 1)) =
      a ^ 2 * ∑ p ∈ Finset.range n, c p * c (p + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
  cases t <;> simp only [LamePolyType.normForm, h1, h2] <;> ring

/-- `signForm` depends only on the coefficients `c₀, …, cₙ`. -/
lemma p2p_signForm_congr (t : LamePolyType) (n : ℕ) {c c' : ℕ → ℝ}
    (h : ∀ p ≤ n, c p = c' p) : t.signForm n c = t.signForm n c' := by
  have h1 : ∀ f : ℕ → ℝ, ∑ p ∈ Finset.range (n + 1), f p * c p =
      ∑ p ∈ Finset.range (n + 1), f p * c' p := fun f =>
    Finset.sum_congr rfl fun p hp => by rw [h p (by simp at hp; omega)]
  have h1' : ∑ p ∈ Finset.range (n + 1), c p = ∑ p ∈ Finset.range (n + 1), c' p :=
    Finset.sum_congr rfl fun p hp => by rw [h p (by simp at hp; omega)]
  have h2 : ∑ p ∈ Finset.Ioc 0 n, c p = ∑ p ∈ Finset.Ioc 0 n, c' p :=
    Finset.sum_congr rfl fun p hp => by rw [h p (by simp at hp; omega)]
  have h0 := h 0 (Nat.zero_le _)
  cases t <;> simp only [LamePolyType.signForm, h1, h1', h2, h0]

/-- `signForm` is linear. -/
lemma p2p_signForm_smul (t : LamePolyType) (n : ℕ) (a : ℝ) (c : ℕ → ℝ) :
    t.signForm n (fun p => a * c p) = a * t.signForm n c := by
  cases t <;> simp only [LamePolyType.signForm] <;>
    first
    | (rw [mul_add, Finset.mul_sum (Finset.Ioc 0 n)]; try ring)
    | (simp only [Finset.mul_sum]; try exact Finset.sum_congr rfl fun p _ => by ring)

/-- The normalized coefficients: `t.normForm = 1`, `t.signForm ≥ 0`, provided the Lamé
polynomial does not vanish identically. -/
lemma p2p_coeff_forms {k : ℝ} (t : LamePolyType) {n m : ℕ}
    (hne : (fun x : ℝ => (lamePolyEk t n m x k).re) ≠ 0) :
    t.normForm k n (lamePolyCoeff t n m k) = 1 ∧ 0 ≤ t.signForm n (lamePolyCoeff t n m k) := by
  set v := lameRecVec t.recurrence (t.order n) k (lamePolyH t n m k)
  set s : ℝ := if t.signForm n v < 0 then -1 else 1
  set r := Real.sqrt (t.normForm k n v)
  have hc : ∀ p ≤ n, lamePolyCoeff t n m k p = (s / r) * v p := fun p hp => by
    simp only [lamePolyCoeff, hp, ↓reduceIte, s, r, v]; ring
  have hpos : 0 < t.normForm k n v := by
    by_contra hle
    have hr : r = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hle)
    apply hne
    funext x
    have : ∀ p ∈ Finset.range (n + 1), lamePolyCoeff t n m k p = 0 := fun p hp => by
      rw [hc p (by simp at hp; omega), hr, div_zero, zero_mul]
    have h0 : ∑ p ∈ Finset.range (n + 1), (lamePolyCoeff t n m k p : ℂ) *
        t.basis p (jacobiSnk (x : ℂ) k) = 0 :=
      Finset.sum_eq_zero fun p hp => by rw [this p hp]; simp
    simp [lamePolyEk, h0]
  have hr2 : r ^ 2 = t.normForm k n v := Real.sq_sqrt hpos.le
  have hr0 : 0 < r := Real.sqrt_pos.2 hpos
  refine ⟨?_, ?_⟩
  · rw [p2p_normForm_congr t k n hc, p2p_normForm_smul, div_pow, hr2]
    have : s ^ 2 = 1 := by simp only [s]; split_ifs <;> norm_num
    rw [this]; field_simp
  · rw [p2p_signForm_congr t n hc, p2p_signForm_smul]
    simp only [s]
    split_ifs with h
    · have : 0 ≤ -1 / r * t.signForm n v := by
        rw [neg_div, neg_mul]; exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos
          (by positivity) h.le)
      exact this
    · exact mul_nonneg (by positivity) (not_lt.1 h)

/-- **Identification with the normalized Lamé function.** If the normalization integral of
the Lamé polynomial is `π/4` times `t.normForm` of its coefficients and its value at `K`
(`Ec` types) or minus its derivative there (`Es` types) is a positive multiple of
`t.signForm`, then it is the normalized `m`th eigenfunction of §29.3. -/
theorem p2p_eq_lameEigenfunction {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m : ℕ} (hm : m ≤ n)
    (hN : ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
        Real.jacobiDnm x (k ^ 2) * (lamePolyEk t n m x k).re ^ 2 =
      π / 4 * t.normForm k n (lamePolyCoeff t n m k))
    {σ : ℝ} (hσ : 0 < σ)
    (hS : (if p2p_oddK t then -deriv (fun x : ℝ => (lamePolyEk t n m x k).re)
        (Real.compEllIntKm (k ^ 2)) else (lamePolyEk t n m (Real.compEllIntKm (k ^ 2)) k).re) =
      σ * t.signForm n (lamePolyCoeff t n m k)) :
    (fun x : ℝ => (lamePolyEk t n m x k).re) =
      Real.lameEigenfunction (t.order n : ℝ) k (p2p_odd0 t) (p2p_oddK t) m := by
  have hk : k ^ 2 < 1 := by nlinarith
  set w := fun x : ℝ => (lamePolyEk t n m x k).re with hw
  set K := Real.compEllIntKm (k ^ 2)
  have hE := p2p_isLameEigenfunction hk0 hk1 t hm
  rw [← p2p_lameEigenvalue_eq hk0 hk1 t hm] at hE
  obtain ⟨hre, hbc, hne⟩ := hE
  obtain ⟨hn1, hs0⟩ := p2p_coeff_forms t hne
  have hν : -1 / 2 ≤ (t.order n : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) (t.order n); linarith
  have hsol := (p2l_isLameSolution_iff).mp hre
  -- the sign condition
  have hsign : if p2p_oddK t then deriv w K < 0 else 0 < w K := by
    have hge : 0 ≤ σ * t.signForm n (lamePolyCoeff t n m k) := mul_nonneg hσ.le hs0
    rw [← hS] at hge
    have hne0 : (if p2p_oddK t then -deriv w K else w K) ≠ 0 := by
      intro h0
      apply hne
      have hb := hbc.2
      cases hK : p2p_oddK t
      · simp only [hK, Bool.false_eq_true, ite_false] at h0 hb
        exact ODE.p2l_eq_zero (p2lPot_continuous hk) hsol h0 hb
      · simp only [hK, ite_true, neg_eq_zero] at h0 hb
        exact ODE.p2l_eq_zero (p2lPot_continuous hk) hsol hb h0
    cases hK : p2p_oddK t
    · simp only [hK, Bool.false_eq_true, ite_false] at hge hne0 ⊢
      exact lt_of_le_of_ne hge (Ne.symm hne0)
    · simp only [hK, ite_true] at hge hne0 ⊢
      have := lt_of_le_of_ne hge (Ne.symm hne0)
      linarith
  have hnorm : Real.IsNormalizedLameEigenfunction (t.order n : ℝ) k (p2p_odd0 t) (p2p_oddK t)
      m w := ⟨⟨hre, hbc, hne⟩, by rw [hN, hn1, mul_one], hsign⟩
  exact (Real.lameEigenfunction_spec hν hk0 hk1 _ _ m).unique hnorm
    (Real.isNormalizedLameEigenfunction_lameEigenfunction hν hk0 hk1 _ _ m)

/-! ### The substitution `φ = π/2 - am(x, k)` and trigonometric orthogonality -/

/-- `∫₀^K dn(x) g(φ(x)) dx = ∫₀^{π/2} g(φ) dφ` for `φ = π/2 - am(x, k)`. -/
lemma p2p_integral_dn_comp {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {g : ℝ → ℝ}
    (hg : Continuous g) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm x (k ^ 2) * g (Real.lamePhi x k) =
      ∫ t in (0 : ℝ)..π / 2, g t := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hdn : Continuous fun x => Real.jacobiDnm x (k ^ 2) :=
    continuous_iff_continuousAt.2 fun x => (Real.hasDerivAt_jacobiDnm hk x).continuousAt
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := Real.compEllIntKm (k ^ 2))
    (f := fun x => Real.lamePhi x k) (f' := fun x => -Real.jacobiDnm x (k ^ 2))
    (g := g) (fun x _ => p1l_hasDerivAt_phi hk x) hdn.neg.continuousOn hg
  have h0 : Real.lamePhi 0 k = π / 2 := by simp [Real.lamePhi, Real.jacobiAmm_zero hk]
  have hK : Real.lamePhi (Real.compEllIntKm (k ^ 2)) k = 0 := by
    rw [Real.lamePhi, Real.jacobiAmm_compEllIntKm hk, sub_self]
  rw [h0, hK] at hsub
  have e : ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
      Real.jacobiDnm x (k ^ 2) * g (Real.lamePhi x k) =
      -∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
        (g ∘ fun x => Real.lamePhi x k) x * -Real.jacobiDnm x (k ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [Function.comp_apply]; ring
  rw [e, hsub, intervalIntegral.integral_symm (π / 2)]

/-- `∫₀^{π/2} cos(2jφ) dφ = π/2` if `j = 0` and `0` otherwise. -/
lemma p2p_integral_cos_two_mul (j : ℤ) :
    ∫ t in (0 : ℝ)..π / 2, Real.cos (2 * j * t) = if j = 0 then π / 2 else 0 := by
  split_ifs with hj
  · simp [hj]
  · have hj' : (2 * j : ℝ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hj
    rw [intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hj', integral_cos]
    have : (2 * j : ℝ) * (π / 2) = (j : ℝ) * π := by ring
    rw [this, Real.sin_int_mul_pi, mul_zero, Real.sin_zero, sub_zero, smul_zero]

/-- Orthogonality of `cos(aφ)` on `[0, π/2]` for `a ≡ b (mod 2)`. -/
lemma p2p_integral_cos_cos (a b : ℕ) (hab : Even (a + b)) :
    ∫ t in (0 : ℝ)..π / 2, Real.cos (a * t) * Real.cos (b * t) =
      if a = b then (if a = 0 then π / 2 else π / 4) else 0 := by
  obtain ⟨r, hr⟩ := hab
  have e : ∀ t : ℝ, Real.cos (a * t) * Real.cos (b * t) =
      Real.cos (2 * ((r : ℤ) - b : ℤ) * t) / 2 + Real.cos (2 * (r : ℤ) * t) / 2 := fun t => by
    have ha : (a : ℝ) = 2 * r - b := by
      have : (a : ℝ) + b = r + r := by exact_mod_cast hr
      linarith
    push_cast
    rw [show 2 * ((r : ℝ) - b) * t = a * t - b * t by rw [ha]; ring,
      show 2 * (r : ℝ) * t = a * t + b * t by rw [ha]; ring, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_div, intervalIntegral.integral_div,
    p2p_integral_cos_two_mul, p2p_integral_cos_two_mul]
  · by_cases h : a = b
    · subst h
      have : (r : ℤ) - a = 0 := by omega
      simp only [this, ↓reduceIte]
      by_cases h0 : a = 0
      · subst h0; have : r = 0 := by omega
        simp [this]
      · have : r ≠ 0 := by omega
        simp [this, h0]; ring
    · have h1 : (r : ℤ) - b ≠ 0 := by omega
      have h2 : r ≠ 0 := by omega
      simp [h, h1, h2]
  all_goals exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- Orthogonality of `sin(aφ)` on `[0, π/2]` for `a ≡ b (mod 2)`. -/
lemma p2p_integral_sin_sin (a b : ℕ) (hab : Even (a + b)) :
    ∫ t in (0 : ℝ)..π / 2, Real.sin (a * t) * Real.sin (b * t) =
      if a = b then (if a = 0 then 0 else π / 4) else 0 := by
  obtain ⟨r, hr⟩ := hab
  have e : ∀ t : ℝ, Real.sin (a * t) * Real.sin (b * t) =
      Real.cos (2 * ((r : ℤ) - b : ℤ) * t) / 2 - Real.cos (2 * (r : ℤ) * t) / 2 := fun t => by
    have ha : (a : ℝ) = 2 * r - b := by
      have : (a : ℝ) + b = r + r := by exact_mod_cast hr
      linarith
    push_cast
    rw [show 2 * ((r : ℝ) - b) * t = a * t - b * t by rw [ha]; ring,
      show 2 * (r : ℝ) * t = a * t + b * t by rw [ha]; ring, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_div, intervalIntegral.integral_div,
    p2p_integral_cos_two_mul, p2p_integral_cos_two_mul]
  · by_cases h : a = b
    · subst h
      have : (r : ℤ) - a = 0 := by omega
      simp only [this, ↓reduceIte]
      by_cases h0 : a = 0
      · subst h0; have : r = 0 := by omega
        simp [this]
      · have : r ≠ 0 := by omega
        simp [this, h0]; ring
    · have h1 : (r : ℤ) - b ≠ 0 := by omega
      have h2 : r ≠ 0 := by omega
      simp [h, h1, h2]
  all_goals exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- `∫ (∑ bₚ fₚ)² = ∑ bₚ² Iₚ` for an orthogonal family `fₚ` with `∫ fₚ² = Iₚ`. -/
lemma p2p_integral_sq_sum {a b : ℝ} (N : ℕ) (c : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hf : ∀ p, Continuous (f p)) (I : ℕ → ℝ)
    (horth : ∀ p q, ∫ t in a..b, f p t * f q t = if p = q then I p else 0) :
    ∫ t in a..b, (∑ p ∈ Finset.range N, c p * f p t) ^ 2 =
      ∑ p ∈ Finset.range N, c p ^ 2 * I p := by
  have e : ∀ t, (∑ p ∈ Finset.range N, c p * f p t) ^ 2 =
      ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, c p * c q * (f p t * f q t) := fun t => by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum
    (f := fun p t => ∑ q ∈ Finset.range N, c p * c q * (f p t * f q t)) fun p _ =>
    (Continuous.intervalIntegrable (continuous_finsetSum _ fun q _ =>
      continuous_const.mul ((hf p).mul (hf q))) _ _)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [intervalIntegral.integral_finsetSum
    (f := fun q t => c p * c q * (f p t * f q t)) fun q _ =>
    (Continuous.intervalIntegrable (continuous_const.mul ((hf p).mul (hf q))) _ _)]
  simp_rw [intervalIntegral.integral_const_mul, horth]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hp, ↓reduceIte]
  ring

/-- `∑_{p ∈ (0, n]} f p = ∑_{p < n} f (p + 1)`. -/
theorem p2p_sum_Ioc (f : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ Finset.Ioc 0 n, f p = ∑ p ∈ Finset.range n, f (p + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ih, Finset.sum_range_succ]

/-- The normalization integral of a finite cosine series in `φ = π/2 - am(x, k)`. -/
theorem p2p_norm_cos {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (N : ℕ) (b : ℕ → ℝ) {e : ℕ → ℕ}
    (he : Function.Injective e) (hpar : ∀ p q, Even (e p + e q)) {w : ℝ → ℝ}
    (hw : ∀ y, w y = ∑ p ∈ Finset.range N, b p * Real.cos (e p * Real.lamePhi y k)) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm x (k ^ 2) * w x ^ 2 =
      ∑ p ∈ Finset.range N, b p ^ 2 * (if e p = 0 then π / 2 else π / 4) := by
  simp_rw [hw]
  rw [p2p_integral_dn_comp hk0 hk1
    (g := fun φ => (∑ p ∈ Finset.range N, b p * Real.cos (e p * φ)) ^ 2) (by fun_prop)]
  refine p2p_integral_sq_sum N b (fun p t => Real.cos (e p * t)) (fun p => by fun_prop) _
    fun p q => ?_
  rw [p2p_integral_cos_cos _ _ (hpar p q)]
  by_cases h : p = q
  · simp [h]
  · simp [h, he.ne h]

/-- The normalization integral of a finite sine series in `φ = π/2 - am(x, k)`. -/
theorem p2p_norm_sin {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (N : ℕ) (b : ℕ → ℝ) {e : ℕ → ℕ}
    (he : Function.Injective e) (hpar : ∀ p q, Even (e p + e q)) {w : ℝ → ℝ}
    (hw : ∀ y, w y = ∑ p ∈ Finset.range N, b p * Real.sin (e p * Real.lamePhi y k)) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm x (k ^ 2) * w x ^ 2 =
      ∑ p ∈ Finset.range N, b p ^ 2 * (if e p = 0 then 0 else π / 4) := by
  simp_rw [hw]
  rw [p2p_integral_dn_comp hk0 hk1
    (g := fun φ => (∑ p ∈ Finset.range N, b p * Real.sin (e p * φ)) ^ 2) (by fun_prop)]
  refine p2p_integral_sq_sum N b (fun p t => Real.sin (e p * t)) (fun p => by fun_prop) _
    fun p q => ?_
  rw [p2p_integral_sin_sin _ _ (hpar p q)]
  by_cases h : p = q
  · simp [h]
  · simp [h, he.ne h]

/-- The value at `K` of a finite cosine series in `φ` (`φ(K) = 0`). -/
theorem p2p_val_cos {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (N : ℕ) (b : ℕ → ℝ) (e : ℕ → ℝ)
    {w : ℝ → ℝ}
    (hw : ∀ y, w y = ∑ p ∈ Finset.range N, b p * Real.cos (e p * Real.lamePhi y k)) :
    w (Real.compEllIntKm (k ^ 2)) = ∑ p ∈ Finset.range N, b p := by
  rw [hw, l29_lamePhi_K hk0 hk1]; simp

/-- Minus the derivative at `K` of a finite sine series in `φ`: `dn(K) ∑ eₚ bₚ`. -/
theorem p2p_deriv_sin {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (N : ℕ) (b : ℕ → ℝ) (e : ℕ → ℝ)
    {w : ℝ → ℝ}
    (hw : ∀ y, w y = ∑ p ∈ Finset.range N, b p * Real.sin (e p * Real.lamePhi y k)) :
    -deriv w (Real.compEllIntKm (k ^ 2)) =
      Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2) * ∑ p ∈ Finset.range N, e p * b p := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hw' : w = fun y => ∑ p ∈ Finset.range N, b p * Real.sin (e p * Real.lamePhi y k) :=
    funext hw
  set K := Real.compEllIntKm (k ^ 2)
  have hd : HasDerivAt w (∑ p ∈ Finset.range N, b p * (Real.cos (e p * Real.lamePhi K k) *
      (e p * -Real.jacobiDnm K (k ^ 2)))) K := by
    rw [hw']
    exact HasDerivAt.fun_sum fun p _ =>
      (((p1l_hasDerivAt_phi hk K).const_mul (e p)).sin).const_mul (b p)
  rw [hd.deriv, l29_lamePhi_K hk0 hk1, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp; ring

/-- `∫ ρ (∑ cₚ fₚ)² = ∑ₚ ∑_q cₚ c_q ∫ ρ fₚ f_q`. -/
lemma p2p_integral_wsq_sum {a b : ℝ} (N : ℕ) (c : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hf : ∀ p, Continuous (f p)) {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    ∫ t in a..b, ρ t * (∑ p ∈ Finset.range N, c p * f p t) ^ 2 =
      ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N,
        c p * c q * ∫ t in a..b, ρ t * (f p t * f q t) := by
  have e : ∀ t, ρ t * (∑ p ∈ Finset.range N, c p * f p t) ^ 2 =
      ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, c p * c q * (ρ t * (f p t * f q t)) :=
    fun t => by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum
    (f := fun p t => ∑ q ∈ Finset.range N, c p * c q * (ρ t * (f p t * f q t))) fun p _ =>
    (Continuous.intervalIntegrable (continuous_finsetSum _ fun q _ =>
      continuous_const.mul (hρ.mul ((hf p).mul (hf q)))) _ _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [intervalIntegral.integral_finsetSum
    (f := fun q t => c p * c q * (ρ t * (f p t * f q t))) fun q _ =>
    (Continuous.intervalIntegrable (continuous_const.mul (hρ.mul ((hf p).mul (hf q)))) _ _)]
  simp_rw [intervalIntegral.integral_const_mul]

/-- `∫₀^{π/2} cos 2φ cos aφ cos bφ dφ` for `a ≡ b (mod 2)`. -/
lemma p2p_integral_cos2_cos_cos (a b : ℕ) (hab : Even (a + b)) :
    ∫ t in (0 : ℝ)..π / 2, Real.cos (2 * t) * (Real.cos (a * t) * Real.cos (b * t)) =
      π / 8 * ((if b = a + 2 then 1 else 0) + (if a = b + 2 then 1 else 0) +
        (if a + b = 2 then 1 else 0)) := by
  obtain ⟨r, hr⟩ := hab
  have ha : (a : ℝ) = 2 * r - b := by
    have : (a : ℝ) + b = r + r := by exact_mod_cast hr
    linarith
  have e : ∀ t : ℝ, Real.cos (2 * t) * (Real.cos (a * t) * Real.cos (b * t)) =
      Real.cos (2 * ((r : ℤ) + 1 : ℤ) * t) / 4 + Real.cos (2 * ((r : ℤ) - b + 1 : ℤ) * t) / 4 +
      Real.cos (2 * ((b : ℤ) - r + 1 : ℤ) * t) / 4 + Real.cos (2 * (1 - (r : ℤ) : ℤ) * t) / 4 :=
    fun t => by
      push_cast
      rw [show 2 * ((r : ℝ) + 1) * t = a * t + b * t + 2 * t by rw [ha]; ring,
        show 2 * ((r : ℝ) - b + 1) * t = a * t - b * t + 2 * t by rw [ha]; ring,
        show 2 * ((b : ℝ) - r + 1) * t = 2 * t - (a * t - b * t) by rw [ha]; ring,
        show 2 * (1 - (r : ℝ)) * t = 2 * t - (a * t + b * t) by rw [ha]; ring]
      simp only [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
      ring
  simp_rw [e]
  have hi : ∀ j : ℤ, IntervalIntegrable (fun t => Real.cos (2 * (j : ℝ) * t) / 4)
      MeasureTheory.volume 0 (π / 2) := fun j =>
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_add ((hi _).add (hi _) |>.add (hi _)) (hi _),
    intervalIntegral.integral_add ((hi _).add (hi _)) (hi _),
    intervalIntegral.integral_add (hi _) (hi _)]
  simp only [intervalIntegral.integral_div, p2p_integral_cos_two_mul]
  have h1 : ((r : ℤ) + 1 = 0) = False := by simp; omega
  simp only [h1, ↓reduceIte]
  split_ifs <;> first | omega | ring

/-- `∫₀^{π/2} cos 2φ sin aφ sin bφ dφ` for `a ≡ b (mod 2)`. -/
lemma p2p_integral_cos2_sin_sin (a b : ℕ) (hab : Even (a + b)) :
    ∫ t in (0 : ℝ)..π / 2, Real.cos (2 * t) * (Real.sin (a * t) * Real.sin (b * t)) =
      π / 8 * ((if b = a + 2 then 1 else 0) + (if a = b + 2 then 1 else 0) -
        (if a + b = 2 then 1 else 0)) := by
  obtain ⟨r, hr⟩ := hab
  have ha : (a : ℝ) = 2 * r - b := by
    have : (a : ℝ) + b = r + r := by exact_mod_cast hr
    linarith
  have e : ∀ t : ℝ, Real.cos (2 * t) * (Real.sin (a * t) * Real.sin (b * t)) =
      Real.cos (2 * ((r : ℤ) - b + 1 : ℤ) * t) / 4 +
      Real.cos (2 * ((b : ℤ) - r + 1 : ℤ) * t) / 4 - Real.cos (2 * ((r : ℤ) + 1 : ℤ) * t) / 4 -
      Real.cos (2 * (1 - (r : ℤ) : ℤ) * t) / 4 :=
    fun t => by
      push_cast
      rw [show 2 * ((r : ℝ) + 1) * t = a * t + b * t + 2 * t by rw [ha]; ring,
        show 2 * ((r : ℝ) - b + 1) * t = a * t - b * t + 2 * t by rw [ha]; ring,
        show 2 * ((b : ℝ) - r + 1) * t = 2 * t - (a * t - b * t) by rw [ha]; ring,
        show 2 * (1 - (r : ℝ)) * t = 2 * t - (a * t + b * t) by rw [ha]; ring]
      simp only [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
      ring
  simp_rw [e]
  have hi : ∀ j : ℤ, IntervalIntegrable (fun t => Real.cos (2 * (j : ℝ) * t) / 4)
      MeasureTheory.volume 0 (π / 2) := fun j =>
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_sub (((hi _).add (hi _)).sub (hi _)) (hi _),
    intervalIntegral.integral_sub ((hi _).add (hi _)) (hi _),
    intervalIntegral.integral_add (hi _) (hi _)]
  simp only [intervalIntegral.integral_div, p2p_integral_cos_two_mul]
  have h1 : ((r : ℤ) + 1 = 0) = False := by simp; omega
  simp only [h1, ↓reduceIte]
  split_ifs <;> first | omega | ring

/-- The normalization integral of `dn` times a finite series in `φ`: with
`dn² = 1 - k² cos² φ = (1 - k²/2) - (k²/2) cos 2φ`. -/
lemma p2p_norm_dn {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (N : ℕ) (b : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hf : ∀ p, Continuous (f p)) {w : ℝ → ℝ}
    (hw : ∀ y, w y = Real.jacobiDnm y (k ^ 2) *
      ∑ p ∈ Finset.range N, b p * f p (Real.lamePhi y k)) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm x (k ^ 2) * w x ^ 2 =
      ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q *
        ((1 - k ^ 2 / 2) * ∫ t in (0 : ℝ)..π / 2, f p t * f q t) -
      k ^ 2 / 2 * ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q *
        ∫ t in (0 : ℝ)..π / 2, Real.cos (2 * t) * (f p t * f q t) := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hF : Continuous fun t => ∑ p ∈ Finset.range N, b p * f p t :=
    continuous_finsetSum _ fun p _ => continuous_const.mul (hf p)
  have e : ∀ x, Real.jacobiDnm x (k ^ 2) * w x ^ 2 = Real.jacobiDnm x (k ^ 2) *
      (fun t => (1 - k ^ 2 * Real.cos t ^ 2) * (∑ p ∈ Finset.range N, b p * f p t) ^ 2)
        (Real.lamePhi x k) := fun x => by
    have h1 := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hk x
    rw [hw]
    beta_reduce
    rw [p1l_cos_phi, mul_pow,
      show Real.jacobiDnm x (k ^ 2) ^ 2 = 1 - k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2 by linarith]
  simp_rw [e]
  rw [p2p_integral_dn_comp hk0 hk1
    (g := fun t => (1 - k ^ 2 * Real.cos t ^ 2) * (∑ p ∈ Finset.range N, b p * f p t) ^ 2)
    (by fun_prop)]
  rw [p2p_integral_wsq_sum N b f hf (ρ := fun t => 1 - k ^ 2 * Real.cos t ^ 2) (by fun_prop)]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have e2 : ∀ t, (1 - k ^ 2 * Real.cos t ^ 2) * (f p t * f q t) =
      (1 - k ^ 2 / 2) * (f p t * f q t) - k ^ 2 / 2 * (Real.cos (2 * t) * (f p t * f q t)) :=
    fun t => by rw [Real.cos_sq t]; ring
  simp_rw [e2]
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

/-- `∑ₚ ∑_q bₚ b_q ([q = p + 1] + [p = q + 1]) = 2 ∑ₚ bₚ b_{p+1}` when `b_N = 0`. -/
lemma p2p_sum_shift (N : ℕ) (b : ℕ → ℝ) (hb : b N = 0) :
    ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q *
      ((if q = p + 1 then 1 else 0) + (if p = q + 1 then 1 else 0)) =
      2 * ∑ p ∈ Finset.range N, b p * b (p + 1) := by
  have h1 : ∀ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q *
      (if q = p + 1 then (1 : ℝ) else 0) = b p * b (p + 1) := fun p hp => by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with h
    · rfl
    · have : p + 1 = N := by simp at hp; omega
      rw [this, hb, mul_zero]
  have h2 : ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q *
      (if p = q + 1 then (1 : ℝ) else 0) = ∑ p ∈ Finset.range N, b p * b (p + 1) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← h1 q hq]
    exact Finset.sum_congr rfl fun p _ => by ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl h1, h2]; ring

/-- Bookkeeping for the `dn`-type normalization integrals. -/
lemma p2p_dsum_aux (k : ℝ) (N : ℕ) (b : ℕ → ℝ) (α : ℝ) (I : ℕ → ℝ) (X : ℕ → ℕ → ℝ) (hb : b N = 0) :
    ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q * (α * if p = q then I p else 0) -
      k ^ 2 / 2 * ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q *
        (π / 8 * (((if q = p + 1 then 1 else 0) + (if p = q + 1 then 1 else 0)) + X p q)) =
    α * ∑ p ∈ Finset.range N, b p ^ 2 * I p - k ^ 2 / 2 * (π / 8) *
      (2 * ∑ p ∈ Finset.range N, b p * b (p + 1) +
        ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q * X p q) := by
  have A : ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q * (α * if p = q then I p else 0)
      = α * ∑ p ∈ Finset.range N, b p ^ 2 * I p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hp, ↓reduceIte]
    ring
  have B : ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q *
      (π / 8 * (((if q = p + 1 then 1 else 0) + (if p = q + 1 then 1 else 0)) + X p q)) =
      π / 8 * (2 * ∑ p ∈ Finset.range N, b p * b (p + 1) +
        ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q * X p q) := by
    rw [← p2p_sum_shift N b hb, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [A, B]; ring

/-- The `dn`-type normalization integral for a cosine series `∑ bₚ cos((2p+δ)φ)`. -/
theorem p2p_norm_dn_cos {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (N : ℕ) (b : ℕ → ℝ) (δ : ℕ)
    (hb : b N = 0) {w : ℝ → ℝ}
    (hw : ∀ y, w y = Real.jacobiDnm y (k ^ 2) *
      ∑ p ∈ Finset.range N, b p * Real.cos (((2 * p + δ : ℕ) : ℝ) * Real.lamePhi y k)) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm x (k ^ 2) * w x ^ 2 =
      (1 - k ^ 2 / 2) * ∑ p ∈ Finset.range N, b p ^ 2 * (if 2 * p + δ = 0 then π / 2 else π / 4)
      - k ^ 2 / 2 * (π / 8) * (2 * ∑ p ∈ Finset.range N, b p * b (p + 1) +
        ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q *
          (if 2 * p + δ + (2 * q + δ) = 2 then 1 else 0)) := by
  rw [p2p_norm_dn hk0 hk1 N b (fun p t => Real.cos (((2 * p + δ : ℕ) : ℝ) * t))
    (fun p => by fun_prop) hw]
  have hI : ∀ p q, ∫ t in (0 : ℝ)..π / 2, Real.cos (((2 * p + δ : ℕ) : ℝ) * t) *
      Real.cos (((2 * q + δ : ℕ) : ℝ) * t) =
      if p = q then (if 2 * p + δ = 0 then π / 2 else π / 4) else 0 := fun p q => by
    rw [p2p_integral_cos_cos _ _ ⟨p + q + δ, by ring⟩]
    by_cases h : p = q
    · simp [h]
    · simp [h]
  have hJ : ∀ p q, ∫ t in (0 : ℝ)..π / 2, Real.cos (2 * t) *
      (Real.cos (((2 * p + δ : ℕ) : ℝ) * t) * Real.cos (((2 * q + δ : ℕ) : ℝ) * t)) =
      π / 8 * (((if q = p + 1 then 1 else 0) + (if p = q + 1 then 1 else 0)) +
        (if 2 * p + δ + (2 * q + δ) = 2 then 1 else 0)) := fun p q => by
    rw [p2p_integral_cos2_cos_cos _ _ ⟨p + q + δ, by ring⟩]
    congr 2
    have e1 : (2 * q + δ = 2 * p + δ + 2) ↔ q = p + 1 := by omega
    have e2 : (2 * p + δ = 2 * q + δ + 2) ↔ p = q + 1 := by omega
    simp only [e1, e2]
  simp_rw [hI, hJ]
  exact p2p_dsum_aux k N b _ _ (fun p q => (if 2 * p + δ + (2 * q + δ) = 2 then 1 else 0)) hb

/-- The `dn`-type normalization integral for a sine series `∑ bₚ sin((2p+δ)φ)`. -/
theorem p2p_norm_dn_sin {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (N : ℕ) (b : ℕ → ℝ) (δ : ℕ)
    (hb : b N = 0) {w : ℝ → ℝ}
    (hw : ∀ y, w y = Real.jacobiDnm y (k ^ 2) *
      ∑ p ∈ Finset.range N, b p * Real.sin (((2 * p + δ : ℕ) : ℝ) * Real.lamePhi y k)) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm x (k ^ 2) * w x ^ 2 =
      (1 - k ^ 2 / 2) * ∑ p ∈ Finset.range N, b p ^ 2 * (if 2 * p + δ = 0 then 0 else π / 4)
      - k ^ 2 / 2 * (π / 8) * (2 * ∑ p ∈ Finset.range N, b p * b (p + 1) +
        ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q *
          (-(if 2 * p + δ + (2 * q + δ) = 2 then 1 else 0))) := by
  rw [p2p_norm_dn hk0 hk1 N b (fun p t => Real.sin (((2 * p + δ : ℕ) : ℝ) * t))
    (fun p => by fun_prop) hw]
  have hI : ∀ p q, ∫ t in (0 : ℝ)..π / 2, Real.sin (((2 * p + δ : ℕ) : ℝ) * t) *
      Real.sin (((2 * q + δ : ℕ) : ℝ) * t) =
      if p = q then (if 2 * p + δ = 0 then 0 else π / 4) else 0 := fun p q => by
    rw [p2p_integral_sin_sin _ _ ⟨p + q + δ, by ring⟩]
    by_cases h : p = q
    · simp [h]
    · simp [h]
  have hJ : ∀ p q, ∫ t in (0 : ℝ)..π / 2, Real.cos (2 * t) *
      (Real.sin (((2 * p + δ : ℕ) : ℝ) * t) * Real.sin (((2 * q + δ : ℕ) : ℝ) * t)) =
      π / 8 * (((if q = p + 1 then 1 else 0) + (if p = q + 1 then 1 else 0)) +
        -(if 2 * p + δ + (2 * q + δ) = 2 then 1 else 0)) := fun p q => by
    rw [p2p_integral_cos2_sin_sin _ _ ⟨p + q + δ, by ring⟩, ← sub_eq_add_neg]
    congr 2
    have e1 : (2 * q + δ = 2 * p + δ + 2) ↔ q = p + 1 := by omega
    have e2 : (2 * p + δ = 2 * q + δ + 2) ↔ p = q + 1 := by omega
    simp only [e1, e2]
  simp_rw [hI, hJ]
  exact p2p_dsum_aux k N b _ _ (fun p q => -(if 2 * p + δ + (2 * q + δ) = 2 then 1 else 0)) hb

/-- The extra term of the `dn`-type normalization for `δ = 0`. -/
theorem p2p_extra0 (b : ℕ → ℝ) (M : ℕ) (hb : b (M + 1) = 0) :
    ∑ p ∈ Finset.range (M + 1), ∑ q ∈ Finset.range (M + 1), b p * b q *
      (if 2 * p + 0 + (2 * q + 0) = 2 then (1 : ℝ) else 0) = 2 * b 0 * b 1 := by
  have key : ∀ p q : ℕ, (if 2 * p + 0 + (2 * q + 0) = 2 then (1 : ℝ) else 0) =
      (if p = 0 then (if q = 1 then 1 else 0) else 0) +
      (if p = 1 then (if q = 0 then 1 else 0) else 0) := by
    intro p q; split_ifs <;> first | omega | norm_num
  simp only [key, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  rcases M with _ | M
  · simp [hb]
  · simp; ring

/-- The extra term of the `dn`-type normalization for `δ = 1`. -/
theorem p2p_extra1 (b : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1), b p * b q *
      (if 2 * p + 1 + (2 * q + 1) = 2 then (1 : ℝ) else 0) = b 0 ^ 2 := by
  have key : ∀ p q : ℕ, (if 2 * p + 1 + (2 * q + 1) = 2 then (1 : ℝ) else 0) =
      (if p = 0 then (if q = 0 then 1 else 0) else 0) := by
    intro p q; split_ifs <;> first | omega | norm_num
  simp only [key, mul_ite, mul_one, mul_zero]
  simp; ring

/-- The extra term of the `dn`-type normalization for `δ = 2` vanishes. -/
theorem p2p_extra2 (b : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, b p * b q *
      (if 2 * p + 2 + (2 * q + 2) = 2 then (1 : ℝ) else 0) = 0 := by
  have key : ∀ p q : ℕ, (if 2 * p + 2 + (2 * q + 2) = 2 then (1 : ℝ) else 0) = 0 := by
    intro p q; split_ifs <;> first | omega | norm_num
  simp [key]

/-- The value at `K` of `dn` times a finite cosine series in `φ`. -/
theorem p2p_val_dn_cos {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (N : ℕ) (b : ℕ → ℝ) (e : ℕ → ℝ)
    {w : ℝ → ℝ}
    (hw : ∀ y, w y = Real.jacobiDnm y (k ^ 2) *
      ∑ p ∈ Finset.range N, b p * Real.cos (e p * Real.lamePhi y k)) :
    w (Real.compEllIntKm (k ^ 2)) =
      Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2) * ∑ p ∈ Finset.range N, b p := by
  rw [hw, l29_lamePhi_K hk0 hk1]; simp

/-- Minus the derivative at `K` of `dn` times a finite sine series in `φ`. -/
theorem p2p_deriv_dn_sin {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (N : ℕ) (b : ℕ → ℝ) (e : ℕ → ℝ)
    {w : ℝ → ℝ}
    (hw : ∀ y, w y = Real.jacobiDnm y (k ^ 2) *
      ∑ p ∈ Finset.range N, b p * Real.sin (e p * Real.lamePhi y k)) :
    -deriv w (Real.compEllIntKm (k ^ 2)) =
      Real.jacobiDnm (Real.compEllIntKm (k ^ 2)) (k ^ 2) ^ 2 *
        ∑ p ∈ Finset.range N, e p * b p := by
  have hk : k ^ 2 < 1 := by nlinarith
  set K := Real.compEllIntKm (k ^ 2)
  set v := fun y => ∑ p ∈ Finset.range N, b p * Real.sin (e p * Real.lamePhi y k) with hv
  have hdv := p2p_deriv_sin hk0 hk1 N b e (w := v) fun y => rfl
  have hvd : DifferentiableAt ℝ v K := by
    simp only [hv]
    exact DifferentiableAt.fun_sum fun p _ =>
      (((p1l_hasDerivAt_phi hk K).differentiableAt.const_mul (e p)).sin).const_mul (b p)
  have hw' : w = fun y => Real.jacobiDnm y (k ^ 2) * v y := funext hw
  have hd := ((Real.hasDerivAt_jacobiDnm hk K).fun_mul hvd.hasDerivAt)
  rw [hw', hd.deriv]
  have hv0 : v K = 0 := by simp [hv, K, l29_lamePhi_K hk0 hk1]
  rw [hv0, mul_zero, zero_add, neg_mul_eq_mul_neg, hdv]
  ring

end DLMF.Lame
