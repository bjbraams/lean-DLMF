/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.QOrthogonalityTools
public import DLMF.QSeries.Identities
public import DLMF.OrthogonalPolynomials.Basic.QFamilies

/-!
# Orthogonality of the continuous `q`-Hermite polynomials

The continuous `q`-Hermite polynomials `H_n(cos θ | q) = Σ_k [n k]_q e^{i(n-2k)θ}` are orthogonal
for the weight `|(e^{2iθ};q)_∞|²` on `[0, π]` (DLMF 18.28.17). The Jacobi triple product turns
the weight into the theta series `(q;q)_∞⁻¹ Σ_p (-1)^p q^{p(p-1)/2} (e^{2ipθ} - e^{2i(p-1)θ})`, so
the orthogonality integrals reduce to finite sums that Cauchy's `q`-binomial theorem evaluates.

## Main results

* `continuousQHermite_orthogonality`: DLMF 18.28.17.
-/

@[expose] public section
open Complex Finset DLMF.QSeries DLMF.QSeries.TripleProduct
open scoped Real

noncomputable section
set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

namespace ContinuousQHermite

/-- Fourier coefficients of the theta series. -/
private def coef (Q : ℂ) (p : ℤ) : ℂ := (-1 : ℂ) ^ p * Q ^ tri p

/-- `tri (p + 1) = tri p + p`. -/
private lemma tri_succ (p : ℤ) : tri (p + 1) = tri p + p := by
  have h1 := tri_mul_two (p + 1)
  have h2 := tri_mul_two p
  have : (tri (p + 1) - tri p - p) * 2 = 0 := by linear_combination h1 - h2
  have := (mul_eq_zero.mp this).resolve_right two_ne_zero
  linarith

/-- Shift relation of the theta coefficients. -/
private lemma coef_succ {Q : ℂ} (hQ : Q ≠ 0) (p : ℤ) :
    coef Q (p + 1) = -coef Q p * Q ^ p := by
  rw [coef, coef, tri_succ, zpow_add₀ hQ, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  ring

/-- The theta coefficient at `l - s` in `q`-binomial form. -/
private lemma coef_sub {Q : ℂ} (hQ : Q ≠ 0) (l s : ℕ) :
    coef Q ((l : ℤ) - s) = (-1) ^ s * Q ^ ((s + 1).choose 2) *
      ((-1) ^ l * Q ^ l.choose 2 * (Q⁻¹ ^ s) ^ l) := by
  rw [coef, ← tri_sub_cast, zpow_sub₀ hQ, zpow_add₀ hQ, zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp only [zpow_natCast]
  rw [show ((s : ℤ) * l) = ((s * l : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h1 : ((-1 : ℂ) ^ s)⁻¹ = (-1) ^ s := by
    rw [← inv_pow, inv_neg, inv_one]
  rw [div_eq_mul_inv ((-1 : ℂ) ^ l), h1, div_eq_mul_inv _ (Q ^ (s * l)), ← inv_pow, ← pow_mul,
    mul_comm s l]
  ring

/-- The `q`-binomial sum of differences of theta coefficients. -/
private lemma sum_qBinom_coef {Q : ℂ} (hQ : Q ≠ 0) (n s : ℕ) :
    ∑ l ∈ range (n + 1), qBinom Q n l * (coef Q ((l : ℤ) - s) - coef Q ((l : ℤ) - s + 1)) =
      (-1) ^ s * Q ^ ((s + 1).choose 2) *
        (qPochhammer (Q⁻¹ ^ s) Q n + Q⁻¹ ^ s * qPochhammer (Q * Q⁻¹ ^ s) Q n) := by
  rw [qPochhammer_eq_sum_qBinom, qPochhammer_eq_sum_qBinom, mul_sum, ← sum_add_distrib,
    mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [coef_succ hQ, coef_sub hQ]
  have hz : Q ^ ((l : ℤ) - s) = Q ^ l * Q⁻¹ ^ s := by
    rw [zpow_sub₀ hQ, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]
  rw [hz, mul_pow (Q) (Q⁻¹ ^ s) l]
  ring

/-- `(-1)^n q^{n(n+1)/2} (q^{-n};q)_n = (q;q)_n`. -/
private lemma qPochhammer_inv_pow_self {Q : ℂ} (hQ : Q ≠ 0) (n : ℕ) :
    (-1) ^ n * Q ^ ((n + 1).choose 2) * qPochhammer (Q⁻¹ ^ n) Q n = qPochhammer Q Q n := by
  rw [qPochhammer_eq_prod, qPochhammer_eq_prod, ← prod_range_reflect]
  have hterm : ∀ k ∈ range n, 1 - Q⁻¹ ^ n * Q ^ (n - 1 - k) =
      (-Q⁻¹ ^ (k + 1)) * (1 - Q * Q ^ k) := by
    intro k hk
    have hk := mem_range.mp hk
    have h1 : Q⁻¹ ^ n * Q ^ (n - 1 - k) = Q⁻¹ ^ (k + 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + k + 1 := ⟨n - k - 1, by omega⟩
      rw [show j + k + 1 - 1 - k = j by omega, show j + k + 1 = j + (k + 1) by ring, pow_add]
      simp only [inv_pow]
      field_simp
    rw [h1]
    simp only [inv_pow, pow_succ]
    field_simp
    ring
  rw [prod_congr rfl hterm, prod_mul_distrib]
  have hp : ∀ n : ℕ, ∏ k ∈ range n, (-Q⁻¹ ^ (k + 1)) = (-1) ^ n * Q⁻¹ ^ ((n + 1).choose 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [prod_range_succ, ih, show (n + 1 + 1).choose 2 = (n + 1).choose 2 + (n + 1) by
        rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm], pow_add, pow_succ]
      ring
  rw [hp, ← mul_assoc, ← mul_assoc, mul_assoc ((-1) ^ n), mul_comm (Q ^ _), ← mul_assoc,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, inv_pow, mul_inv_cancel₀
      (pow_ne_zero _ hQ), one_mul]

/-- `q · q^{-s} · q^{s-1} = 1`. -/
private lemma mul_inv_pow_mul_pow {Q : ℂ} (hQ : Q ≠ 0) {s : ℕ} (hs : 1 ≤ s) :
    Q * Q⁻¹ ^ s * Q ^ (s - 1) = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  simp only [inv_pow]
  field_simp

/-- The `q`-binomial sum vanishes in the interior range. -/
private lemma sum_qBinom_coef_eq_zero {Q : ℂ} (hQ : Q ≠ 0) {n s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s < n) :
    ∑ l ∈ range (n + 1), qBinom Q n l * (coef Q ((l : ℤ) - s) - coef Q ((l : ℤ) - s + 1)) =
      0 := by
  rw [sum_qBinom_coef hQ, QOrthogonality.qPochhammer_eq_zero (k := s) hsn (by
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hQ)]),
    QOrthogonality.qPochhammer_eq_zero (w := Q * Q⁻¹ ^ s) (k := s - 1) (by omega)
      (mul_inv_pow_mul_pow hQ hs1)]
  ring

/-- The `q`-binomial sum at `s = 0`. -/
private lemma sum_qBinom_coef_zero {Q : ℂ} (hQ : Q ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ∑ l ∈ range (n + 1), qBinom Q n l * (coef Q ((l : ℤ) - (0 : ℕ)) -
      coef Q ((l : ℤ) - (0 : ℕ) + 1)) = qPochhammer Q Q n := by
  rw [sum_qBinom_coef hQ, QOrthogonality.qPochhammer_eq_zero (k := 0) hn (by simp)]
  simp

/-- The `q`-binomial sum at `s = n`. -/
private lemma sum_qBinom_coef_self {Q : ℂ} (hQ : Q ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ∑ l ∈ range (n + 1), qBinom Q n l * (coef Q ((l : ℤ) - n) - coef Q ((l : ℤ) - n + 1)) =
      qPochhammer Q Q n := by
  rw [sum_qBinom_coef hQ, QOrthogonality.qPochhammer_eq_zero (w := Q * Q⁻¹ ^ n) (k := n - 1)
    (n := n) (by omega) (mul_inv_pow_mul_pow hQ hn), mul_zero, add_zero]
  exact qPochhammer_inv_pow_self hQ n



/-- `∫_{-π}^{π} e^{ijθ} dθ = 2π δ_{j0}`. -/
private lemma integral_exp_int_mul (j : ℤ) :
    ∫ θ : ℝ in -π..π, cexp (I * j * θ) = if j = 0 then 2 * (π : ℂ) else 0 := by
  split_ifs with hj
  · subst hj; simp; ring
  · have hc : I * (j : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hj)
    rw [integral_exp_mul_complex hc]
    have h : cexp (I * j * (π : ℝ)) = cexp (I * j * ((-π : ℝ) : ℂ)) := by
      rw [show I * j * (π : ℝ) = I * j * ((-π : ℝ) : ℂ) + j * (2 * π * I) by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h, sub_self, zero_div]

/-- Complex conjugation of `(a;q)_∞` for real `q`. -/
private lemma conj_qPochhammerInf (a : ℂ) {q : ℝ} (hq : |q| < 1) :
    (starRingEnd ℂ) (qPochhammerInf a q) = qPochhammerInf ((starRingEnd ℂ) a) q := by
  have hq' : ‖(q : ℂ)‖ < 1 := by simpa using hq
  have h := ((multipliable_one_sub_mul_pow (w := a) hq').hasProd).map (starRingEnd ℂ)
    Complex.continuous_conj
  unfold qPochhammerInf
  refine h.tprod_eq.symm.trans ?_
  congr 1
  funext k
  simp [map_sub, map_mul, map_pow, Complex.conj_ofReal]


/-- The weight `|(e^{2iθ};q)_∞|²`. -/
private def weight (q θ : ℝ) : ℂ := ((‖qPochhammerInf (cexp (2 * I * θ)) q‖ ^ 2 : ℝ) : ℂ)

/-- `|e^{ijθ}| = 1`. -/
private lemma norm_exp_I_int_mul (j : ℤ) (θ : ℝ) : ‖cexp (I * j * θ)‖ = 1 := by
  rw [show I * (j : ℂ) * (θ : ℂ) = ((j * θ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- The theta coefficients are absolutely summable. -/
private lemma summable_norm_coef {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun p : ℤ => ‖coef q p‖ := by
  have hq' : ‖(q : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hq0.le]; exact hq1
  have h := summable_norm_term hq' (by exact_mod_cast hq0.ne') one_ne_zero
  refine h.congr fun p => ?_
  simp [term, coef]

/-- The theta-series expansion of the weight. -/
private lemma weight_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (θ : ℝ) :
    weight q θ = (qPochhammerInf q q)⁻¹ * ∑' p : ℤ, coef q p *
      (cexp (I * ((2 * p : ℤ) : ℂ) * θ) - cexp (I * ((2 * p - 2 : ℤ) : ℂ) * θ)) := by
  have hq' : ‖(q : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hq0.le]; exact hq1
  have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  set z := cexp (2 * I * θ) with hzdef
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hconj : (starRingEnd ℂ) z = z⁻¹ := by
    rw [hzdef, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp [map_mul, Complex.conj_ofReal, map_ofNat]
  have hW : weight q θ = qPochhammerInf z q * (starRingEnd ℂ) (qPochhammerInf z q) := by
    rw [weight, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hW, conj_qPochhammerInf z (by rw [abs_of_pos hq0]; exact hq1), hconj,
    qPochhammerInf_shift (a := z⁻¹) hq', show z⁻¹ * (q : ℂ) = q / z by field_simp,
    show qPochhammerInf z q * ((1 - z⁻¹) * qPochhammerInf (q / z) q) =
      (1 - z⁻¹) * (qPochhammerInf (q / z) q * qPochhammerInf z q) by ring,
    jtp_ne_zero hq' hq0' hz, ← mul_assoc, mul_comm (1 - z⁻¹), mul_assoc, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun p => ?_
  have hzp : ∀ j : ℤ, z ^ j = cexp (I * ((2 * j : ℤ) : ℂ) * θ) := fun j => by
    rw [hzdef, ← Complex.exp_int_mul]; congr 1; push_cast; ring
  rw [term, ← hzp, show (2 * p - 2 : ℤ) = 2 * (p - 1) by ring, ← hzp, coef,
    zpow_sub₀ hz, zpow_one]
  field_simp

/-- The weight is continuous. -/
private lemma continuous_weight {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Continuous (weight q) := by
  have hq' : ‖(q : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hq0.le]; exact hq1
  unfold weight
  refine Complex.continuous_ofReal.comp ((((differentiable_qPochhammerInf_left hq').continuous.comp
    ?_).norm).pow 2)
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

/-- Fourier coefficients of the weight. -/
private lemma integral_exp_mul_weight {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (a : ℤ) :
    ∫ θ : ℝ in -π..π, cexp (I * a * θ) * weight q θ = (qPochhammerInf q q)⁻¹ * (2 * π) *
      ∑' p : ℤ, coef q p * ((if a + 2 * p = 0 then 1 else 0) -
        (if a + (2 * p - 2) = 0 then 1 else 0)) := by
  let F : ℤ → C(ℝ, ℂ) := fun p => ⟨fun θ => coef q p * (cexp (I * ((a + 2 * p : ℤ) : ℂ) * θ) -
    cexp (I * ((a + (2 * p - 2) : ℤ) : ℂ) * θ)), by fun_prop⟩
  have hF : ∀ θ : ℝ, cexp (I * a * θ) * weight q θ = (qPochhammerInf q q)⁻¹ * ∑' p, F p θ := by
    intro θ
    rw [weight_eq hq0 hq1, mul_left_comm, ← tsum_mul_left]
    congr 1
    refine tsum_congr fun p => ?_
    simp only [F, ContinuousMap.coe_mk]
    rw [mul_left_comm, mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    congr 3 <;> push_cast <;> ring
  have hsum : Summable fun p : ℤ =>
      ‖(F p).restrict (⟨Set.uIcc (-π) π, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      ((summable_norm_coef hq0 hq1).mul_left 2)
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
    simp only [ContinuousMap.restrict_apply, F, ContinuousMap.coe_mk, norm_mul]
    have := norm_sub_le (cexp (I * ((a + 2 * p : ℤ) : ℂ) * x))
      (cexp (I * ((a + (2 * p - 2) : ℤ) : ℂ) * x))
    rw [norm_exp_I_int_mul, norm_exp_I_int_mul] at this
    nlinarith [norm_nonneg (coef q p)]
  simp_rw [hF]
  rw [intervalIntegral.integral_const_mul,
    ← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum, mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr fun p => ?_
  simp only [F, ContinuousMap.coe_mk]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_exp_int_mul, integral_exp_int_mul]
  split_ifs <;> ring

/-- Symmetry of the Gaussian binomial coefficients. -/
private lemma qBinom_symm {Q : ℂ} (hQ : ‖Q‖ < 1) {n k : ℕ} (hk : k ≤ n) :
    qBinom Q n (n - k) = qBinom Q n k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  rw [show k + m - k = m by omega]
  have h1 := qBinom_mul_qPochhammer Q k m
  have h2 := qBinom_mul_qPochhammer Q m k
  rw [add_comm m k] at h2
  have hk' := qPochhammer_self_ne_zero hQ k
  have hm' := qPochhammer_self_ne_zero hQ m
  apply mul_right_cancel₀ (mul_ne_zero hk' hm')
  linear_combination h2 - h1

/-- The Laurent form of the continuous `q`-Hermite polynomial. -/
private lemma continuousQHermiteLaurent_eq {Q : ℂ} (hQ : ‖Q‖ < 1) (n : ℕ) (z : ℂ) :
    continuousQHermiteLaurent Q n z =
      ∑ k ∈ range (n + 1), qBinom Q n k * z ^ ((n : ℤ) - 2 * k) := by
  unfold continuousQHermiteLaurent qGegenbauer
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have h := qBinom_mul_qPochhammer Q k (n - k)
  rw [Nat.add_sub_cancel' hk] at h
  have h0 : ∀ j, qPochhammer 0 Q j = 1 := fun j => by simp [qPochhammer_eq_prod]
  rw [h0, h0, ← h]
  have hk' := qPochhammer_self_ne_zero hQ k
  have hm' := qPochhammer_self_ne_zero hQ (n - k)
  field_simp

/-- `H_n(e^{iθ})` as a trigonometric sum. -/
private lemma continuousQHermiteLaurent_exp {Q : ℂ} (hQ : ‖Q‖ < 1) (n : ℕ) (θ : ℝ) :
    continuousQHermiteLaurent Q n (cexp (I * θ)) =
      ∑ k ∈ range (n + 1), qBinom Q n k * cexp (I * (((n : ℤ) - 2 * k : ℤ) : ℂ) * θ) := by
  rw [continuousQHermiteLaurent_eq hQ]
  refine sum_congr rfl fun k _ => ?_
  rw [← Complex.exp_int_mul]; congr 2; push_cast; ring

/-- `H_n(e^{-iθ}) = H_n(e^{iθ})`. -/
private lemma continuousQHermiteLaurent_exp_neg {Q : ℂ} (hQ : ‖Q‖ < 1) (n : ℕ) (θ : ℝ) :
    continuousQHermiteLaurent Q n (cexp (I * ((-θ : ℝ) : ℂ))) =
      continuousQHermiteLaurent Q n (cexp (I * θ)) := by
  rw [continuousQHermiteLaurent_exp hQ, continuousQHermiteLaurent_exp hQ, ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega, qBinom_symm hQ hk]
  congr 2
  push_cast [Nat.cast_sub hk]
  ring


/-- The weight is even. -/
private lemma weight_neg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (θ : ℝ) :
    weight q (-θ) = weight q θ := by
  unfold weight
  have h : cexp (2 * I * ((-θ : ℝ) : ℂ)) = (starRingEnd ℂ) (cexp (2 * I * θ)) := by
    rw [← Complex.exp_conj]; congr 1; simp [map_mul, map_ofNat]
  rw [h, ← conj_qPochhammerInf _ (by rw [abs_of_pos hq0]; exact hq1), Complex.norm_conj]

/-- The coefficient sum at an even frequency. -/
private lemma tsum_coef_even (Q : ℂ) {a t : ℤ} (ha : a = -2 * t) :
    ∑' p : ℤ, coef Q p * ((if a + 2 * p = 0 then 1 else 0) -
      (if a + (2 * p - 2) = 0 then 1 else 0)) = coef Q t - coef Q (t + 1) := by
  have h : ∀ p : ℤ, coef Q p * ((if a + 2 * p = 0 then 1 else 0) -
      (if a + (2 * p - 2) = 0 then 1 else 0)) =
      (if p = t then coef Q t else 0) - (if p = t + 1 then coef Q (t + 1) else 0) := by
    intro p
    by_cases h1 : p = t
    · subst h1; simp [show a + 2 * p = 0 by omega, show a + (2 * p - 2) ≠ 0 by omega]
    · by_cases h2 : p = t + 1
      · subst h2; simp [show a + 2 * (t + 1) ≠ 0 by omega, show a + (2 * (t + 1) - 2) = 0 by omega]
      · simp [h1, h2, show a + 2 * p ≠ 0 by omega, show a + (2 * p - 2) ≠ 0 by omega]
  simp_rw [h]
  rw [Summable.tsum_sub (hasSum_ite_eq t _).summable (hasSum_ite_eq (t + 1) _).summable,
    tsum_ite_eq,
    tsum_ite_eq]

/-- The coefficient sum at an odd frequency vanishes. -/
private lemma tsum_coef_odd (Q : ℂ) {a : ℤ} (ha : Odd a) :
    ∑' p : ℤ, coef Q p * ((if a + 2 * p = 0 then 1 else 0) -
      (if a + (2 * p - 2) = 0 then 1 else 0)) = 0 := by
  obtain ⟨t, rfl⟩ := ha
  have h : ∀ p : ℤ, coef Q p * ((if 2 * t + 1 + 2 * p = 0 then 1 else 0) -
      (if 2 * t + 1 + (2 * p - 2) = 0 then 1 else 0)) = 0 := fun p => by
    simp [show 2 * t + 1 + 2 * p ≠ 0 by omega, show 2 * t + 1 + (2 * p - 2) ≠ 0 by omega]
  simp_rw [h, tsum_zero]

/-- Expansion of the full-period integral into Fourier coefficients of the weight. -/
private lemma integral_full {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (m n : ℕ) :
    ∫ θ : ℝ in -π..π, continuousQHermiteLaurent q m (cexp (I * θ)) *
      continuousQHermiteLaurent q n (cexp (I * θ)) * weight q θ =
    ∑ k ∈ range (m + 1), ∑ l ∈ range (n + 1), qBinom q m k * qBinom q n l *
      ∫ θ : ℝ in -π..π, cexp (I * (((m : ℤ) - 2 * k + ((n : ℤ) - 2 * l) : ℤ) : ℂ) * θ) *
        weight q θ := by
  have hq' : ‖(q : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hq0.le]; exact hq1
  have hW := continuous_weight hq0 hq1
  simp_rw [continuousQHermiteLaurent_exp hq', sum_mul_sum, sum_mul]
  rw [intervalIntegral.integral_finsetSum fun k _ => ?_]
  · refine sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_finsetSum fun l _ => ?_]
    · refine sum_congr rfl fun l _ => ?_
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext θ
      rw [show (((m : ℤ) - 2 * k + ((n : ℤ) - 2 * l) : ℤ) : ℂ) =
        (((m : ℤ) - 2 * k : ℤ) : ℂ) + (((n : ℤ) - 2 * l : ℤ) : ℂ) by push_cast; ring,
        mul_add, add_mul, Complex.exp_add]
      ring
    · exact (by fun_prop : Continuous fun θ : ℝ => _).intervalIntegrable _ _
  · refine (continuous_finsetSum _ fun l _ => ?_).intervalIntegrable _ _
    fun_prop

/-- The full-period integral for `m ≤ n`. -/
private lemma integral_full_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {m n : ℕ}
    (hmn : m ≤ n) :
    ∫ θ : ℝ in -π..π, continuousQHermiteLaurent q m (cexp (I * θ)) *
      continuousQHermiteLaurent q n (cexp (I * θ)) * weight q θ =
    if m = n then 4 * π * qPochhammer q q n / qPochhammerInf q q else 0 := by
  have hQ : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  rw [integral_full hq0 hq1]
  simp_rw [integral_exp_mul_weight hq0 hq1]
  rcases Nat.even_or_odd (m + n) with ⟨r, hr⟩ | hodd
  · have hT : ∀ k ∈ range (m + 1), ∀ l ∈ range (n + 1),
        ∑' p : ℤ, coef q p * ((if (((m : ℤ) - 2 * k + ((n : ℤ) - 2 * l) : ℤ)) + 2 * p = 0
          then 1 else 0) - (if (((m : ℤ) - 2 * k + ((n : ℤ) - 2 * l) : ℤ)) + (2 * p - 2) = 0
          then 1 else 0)) = coef q ((l : ℤ) - ((r - k : ℕ) : ℤ)) -
            coef q ((l : ℤ) - ((r - k : ℕ) : ℤ) + 1) := by
      intro k hk l _
      have hk := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hkr : k ≤ r := by omega
      rw [tsum_coef_even (q : ℂ) (t := (l : ℤ) - ((r - k : ℕ) : ℤ)) (by push_cast [hkr]; omega)]
    have hS : ∀ k ∈ range (m + 1), ∑ l ∈ range (n + 1), qBinom q m k * qBinom q n l *
        ((qPochhammerInf q q)⁻¹ * (2 * π) * ∑' p : ℤ, coef q p *
          ((if (((m : ℤ) - 2 * k + ((n : ℤ) - 2 * l) : ℤ)) + 2 * p = 0 then 1 else 0) -
            (if (((m : ℤ) - 2 * k + ((n : ℤ) - 2 * l) : ℤ)) + (2 * p - 2) = 0 then 1 else 0))) =
        qBinom q m k * ((qPochhammerInf q q)⁻¹ * (2 * π)) *
          ∑ l ∈ range (n + 1), qBinom q n l * (coef q ((l : ℤ) - ((r - k : ℕ) : ℤ)) -
            coef q ((l : ℤ) - ((r - k : ℕ) : ℤ) + 1)) := by
      intro k hk
      rw [mul_sum]
      refine sum_congr rfl fun l hl => ?_
      rw [hT k hk l hl]
      ring
    rw [sum_congr rfl hS]
    split_ifs with hmn'
    · subst hmn'
      have hr' : r = m := by omega
      subst hr'
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0
        simp [coef, tri]
        ring
      · obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
        rw [sum_range_succ, sum_range_succ']
        rw [sum_eq_zero fun k hk => by
          have hk := mem_range.mp hk
          rw [sum_qBinom_coef_eq_zero hQ (s := j + 1 - (k + 1)) (by omega) (by omega), mul_zero]]
        rw [Nat.sub_self, Nat.sub_zero, sum_qBinom_coef_zero hQ (by omega),
          sum_qBinom_coef_self hQ (by omega), qBinom_self, qBinom_zero_right]
        ring
    · rw [sum_eq_zero fun k hk => by
        have hk := Nat.lt_succ_iff.mp (mem_range.mp hk)
        rw [sum_qBinom_coef_eq_zero hQ (s := r - k) (by omega) (by omega), mul_zero]]
  · rw [sum_eq_zero fun k _ => sum_eq_zero fun l _ => by
      rw [tsum_coef_odd (q : ℂ) (by
        obtain ⟨t, ht⟩ := hodd
        exact ⟨(t : ℤ) - k - l, by omega⟩), mul_zero, mul_zero]]
    rw [ite_eq_right_iff.mpr fun h => absurd h (by rintro rfl; obtain ⟨t, ht⟩ := hodd; omega)]

end ContinuousQHermite

open ContinuousQHermite in
/-- Identity under the stated parameter and domain assumptions: `(∫ θ : ℝ in (0 : ℝ)..Real.pi,
continuousQHermiteLaurent q m (exp (I * θ)) * continuousQHermiteLaurent q n (exp (I * θ)) *
(‖qPochhammerInf (exp (2 * I * θ)) q‖ ^ 2 : ℝ)) / (2 * Real.pi) = if m = n then
(qPochhammerInf ((q : ℂ) ^ (n + 1)) q)⁻¹ else 0`. -/
@[dlmf 18.28.E17]
theorem continuousQHermite_orthogonality {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (m n : ℕ) :
    (∫ θ : ℝ in (0 : ℝ)..Real.pi, continuousQHermiteLaurent q m (exp (I * θ)) *
      continuousQHermiteLaurent q n (exp (I * θ)) *
      (‖qPochhammerInf (exp (2 * I * θ)) q‖ ^ 2 : ℝ)) / (2 * Real.pi) =
      if m = n then (qPochhammerInf ((q : ℂ) ^ (n + 1)) q)⁻¹ else 0 := by
  have hq' : ‖(q : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hq.le]; exact hq1
  set F : ℕ → ℕ → ℝ → ℂ := fun m n θ => continuousQHermiteLaurent q m (cexp (I * θ)) *
    continuousQHermiteLaurent q n (cexp (I * θ)) * weight q θ with hF
  have hcont : ∀ m n, Continuous (F m n) := fun m n => by
    simp only [hF]
    simp_rw [continuousQHermiteLaurent_exp hq']
    exact ((continuous_finsetSum _ fun k _ => by fun_prop).mul
      (continuous_finsetSum _ fun k _ => by fun_prop)).mul (continuous_weight hq hq1)
  have hhalf : ∀ m n, ∫ θ : ℝ in (0 : ℝ)..π, F m n θ = (1 / 2) * ∫ θ : ℝ in -π..π, F m n θ := by
    intro m n
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := -π) (b := 0) (c := π)
      ((hcont m n).intervalIntegrable _ _) ((hcont m n).intervalIntegrable _ _)]
    have hneg : ∫ θ : ℝ in -π..0, F m n θ = ∫ θ : ℝ in (0 : ℝ)..π, F m n θ := by
      rw [← neg_zero, ← intervalIntegral.integral_comp_neg, neg_zero]
      congr 1; funext θ
      simp only [hF]
      rw [continuousQHermiteLaurent_exp_neg hq', continuousQHermiteLaurent_exp_neg hq',
        weight_neg hq hq1]
    rw [hneg]; ring
  have hsym : ∀ m n, F m n = F n m := fun m n => by
    funext θ; simp only [hF]; ring
  have hmain : ∫ θ : ℝ in (0 : ℝ)..π, F m n θ =
      if m = n then 2 * π * qPochhammer q q n / qPochhammerInf q q else 0 := by
    rw [hhalf]
    rcases le_total m n with h | h
    · rw [integral_full_eq hq hq1 h]; split_ifs <;> ring
    · rw [hsym, integral_full_eq hq hq1 h]
      split_ifs with h1 h2 h2
      · subst h1; ring
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · ring
  change (∫ θ : ℝ in (0 : ℝ)..π, F m n θ) / (2 * π) = _
  rw [hmain]
  split_ifs with hmn
  · have hP := qPochhammerInf_mul_qPochhammer (a := (q : ℂ)) hq' n
    rw [← pow_succ'] at hP
    have h1 := qPochhammer_self_ne_zero hq' n
    have hqn : ‖(q : ℂ) ^ (n + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq' (by omega)
    have h2 : qPochhammerInf ((q : ℂ) ^ (n + 1)) q ≠ 0 :=
      qPochhammerInf_ne_zero_of_norm_lt_one hqn hq'
    rw [hP]
    field_simp
  · exact zero_div _

end DLMF.OrthogonalPolynomials
