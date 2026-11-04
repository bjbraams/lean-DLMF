/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Convergence
public import DLMF.QSeries.Saalschutz

/-!
# Constant terms of `q`-products (DLMF §17.14)

This file proves the `q`-Dyson constant-term identity and the four Rogers–Ramanujan-type
constant-term identities of DLMF §17.14.

## Main definitions

* `qDysonLaurent`: the finite `q`-Dyson Laurent polynomial in `n` variables.
* `circleConstantTerm`: the Laurent coefficient of order zero on a positively oriented circle.
* `rogersThetaProduct`: the Jacobi triple-product numerator of the four constant-term
  identities.

## Main results

* `qDyson_constantTerm_mul`, `qDyson_constantTerm`: the `q`-Dyson identity (DLMF 17.14.1) in
  polynomial form, valid even at roots of unity, and in quotient form.
* `rogers_constantTerm_H`: DLMF 17.14.2.
* `rogers_constantTerm_G_corrected`: the corrected form of DLMF 17.14.3.
* `rogers_constantTerm_G_four`, `rogers_constantTerm_H_four`: the constant-term forms of
  `G(q⁴)` and `H(q⁴)` (DLMF 17.14.4–17.14.5).

## Implementation notes

The finite `q`-Dyson product is a multivariate Laurent polynomial, represented by its finitely
supported integer exponent vectors. Infinite-product constant terms are Laurent coefficients
computed by the normalized integral on `|z| = ρ`, `ρ > 1`. This annulus fixes the expansion of
inverse powers and excludes all denominator poles.

The printed left side of DLMF 17.14.3 repeats 17.14.2. Its coefficient of `q` is `-1`, whereas
the printed `G(q)/(-q;q²)_∞` has coefficient `0`. The correct denominator is `(-q;q²)_n`, as
also obtained from the constant-term expression; the corrected formula is stated as
`rogers_constantTerm_G_corrected`.

The constant terms are computed by expanding the numerator by the Jacobi triple product,
`∑ q^{n²} zⁿ`, and the denominator by Euler's sum `1/(w;Q)_∞ = ∑ wᵏ/(Q;Q)_k`, and integrating
the absolutely convergent double series term by term. The series sides are proved by expanding
the tails `(∓q^{2n+1};q²)_∞` by Euler's second sum and summing along antidiagonals; the inner
sums are values of the Rogers–Szegő polynomials `∑_j [N j]_{q²} xʲ` at `x = q` (giving
`(-q;q)_N`) and `x = -1` (Gauss's alternating sum).
-/

@[expose] public noncomputable section
open Complex Finset MeasureTheory
open scoped Real
open DLMF.QSeries DLMF.QSeries.TripleProduct
namespace DLMF.QHypergeometric

/-- The finite q-Dyson Laurent polynomial in `n` variables. -/
def qDysonLaurent (n : ℕ) (a : Fin n → ℕ) (q : ℂ) :
    AddMonoidAlgebra ℂ (Fin n → ℤ) :=
  ∏ j : Fin n, ∏ k : Fin n, if j < k then
    (∏ t ∈ range (a j), (1 - AddMonoidAlgebra.single
      (Pi.single j 1 - Pi.single k 1) (q^t))) *
    (∏ t ∈ range (a k), (1 - AddMonoidAlgebra.single
      (Pi.single k 1 - Pi.single j 1) (q^(t+1)))) else 1

/-- Polynomial form of the q-Dyson identity, valid even at roots of unity. -/
@[dlmf 17.14.E1]
theorem qDyson_constantTerm_mul (n : ℕ) (a : Fin n → ℕ) (q : ℂ) :
    (qDysonLaurent n a q).coeff 0 * (∏ i, qPochhammer q q (a i)) =
      qPochhammer q q (∑ i, a i) := by
  sorry

/-- The quotient form of the q-Dyson identity, with exactly the needed denominator condition. -/
@[dlmf 17.14.E1]
theorem qDyson_constantTerm (n : ℕ) (a : Fin n → ℕ) (q : ℂ)
    (hden : ∀ i, qPochhammer q q (a i) ≠ 0) :
    (qDysonLaurent n a q).coeff 0 =
      qPochhammer q q (∑ i, a i) / (∏ i, qPochhammer q q (a i)) := by
  exact (eq_div_iff (Finset.prod_ne_zero_iff.mpr fun i _ => hden i)).mpr
    (qDyson_constantTerm_mul n a q)

/-- Laurent coefficient of order zero on a specified positively oriented circle. -/
def circleConstantTerm (f : ℂ → ℂ) (ρ : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ θ : ℝ in 0..(2 * Real.pi), f (ρ * exp (θ * I))

/-- The Jacobi triple-product numerator used in the four constant-term identities. -/
def rogersThetaProduct (q z : ℂ) : ℂ :=
  qPochhammerInf (-z*q) (q^2) * qPochhammerInf (-q/z) (q^2) *
    qPochhammerInf (q^2) (q^2)

/-! ### Auxiliary lemmas for the Rogers constant terms -/

/-- The Rogers–Szegő polynomial `∑_j [N j]_p x^j`. -/
private def rogersSzegoSum (p : ℂ) (N : ℕ) (x : ℂ) : ℂ :=
  ∑ j ∈ range (N + 1), qBinom p N j * x ^ j

/-- The sum may run over any range containing `0, …, N`. -/
private lemma rogersSzegoSum_eq_sum_range (p : ℂ) {N M : ℕ} (hM : N + 1 ≤ M) (x : ℂ) :
    rogersSzegoSum p N x = ∑ j ∈ range M, qBinom p N j * x ^ j := by
  rw [rogersSzegoSum, ← sum_range_add_sum_Ico _ hM, left_eq_add]
  exact sum_eq_zero fun j hj => by
    rw [qBinom_eq_zero_of_lt p (by simp at hj; omega), zero_mul]

/-- First Pascal recurrence: `H_{N+1}(x) = x H_N(x) + H_N(px)`. -/
private lemma rogersSzegoSum_succ (p : ℂ) (N : ℕ) (x : ℂ) :
    rogersSzegoSum p (N + 1) x = x * rogersSzegoSum p N x + rogersSzegoSum p N (p * x) := by
  rw [rogersSzegoSum, sum_range_succ',
    rogersSzegoSum_eq_sum_range p (show N + 1 ≤ N + 2 by omega) (p * x),
    sum_range_succ' _ (N + 1), rogersSzegoSum, mul_sum]
  simp only [qBinom_succ_succ, add_mul, sum_add_distrib]
  have h1 : ∀ i ∈ range (N + 1), qBinom p N i * x ^ (i + 1) = x * (qBinom p N i * x ^ i) :=
    fun i _ => by ring
  have h2 : ∀ i ∈ range (N + 1), p ^ (i + 1) * qBinom p N (i + 1) * x ^ (i + 1) =
      qBinom p N (i + 1) * (p * x) ^ (i + 1) := fun i _ => by ring
  rw [sum_congr rfl h1, sum_congr rfl h2]
  simp [qBinom]
  ring

/-- Second Pascal recurrence: `H_{N+1}(px) = H_N(px) + p^{N+1} x H_N(x)`. -/
private lemma rogersSzegoSum_succ_mul (p : ℂ) (N : ℕ) (x : ℂ) :
    rogersSzegoSum p (N + 1) (p * x) =
      rogersSzegoSum p N (p * x) + p ^ (N + 1) * x * rogersSzegoSum p N x := by
  rw [rogersSzegoSum, sum_range_succ',
    rogersSzegoSum_eq_sum_range p (show N + 1 ≤ N + 2 by omega) (p * x),
    sum_range_succ' _ (N + 1), rogersSzegoSum, mul_sum]
  simp only [qBinom_succ_succ', add_mul, sum_add_distrib]
  have h2 : ∀ i ∈ range (N + 1), p ^ (N - i) * qBinom p N i * (p * x) ^ (i + 1) =
      p ^ (N + 1) * x * (qBinom p N i * x ^ i) := fun i hi => by
    have : p ^ (N - i) * p ^ (i + 1) = p ^ (N + 1) := by
      rw [← pow_add]; congr 1; simp at hi; omega
    linear_combination (qBinom p N i * x ^ (i + 1)) * this
  rw [sum_congr rfl h2]
  simp [qBinom]
  ring

/-- The three-term recurrence of the Rogers–Szegő polynomials. -/
private lemma rogersSzegoSum_succ_succ (p : ℂ) (N : ℕ) (x : ℂ) :
    rogersSzegoSum p (N + 2) x =
      (1 + x) * rogersSzegoSum p (N + 1) x - x * (1 - p ^ (N + 1)) * rogersSzegoSum p N x := by
  have h1 := rogersSzegoSum_succ p (N + 1) x
  have h2 := rogersSzegoSum_succ_mul p N x
  have h3 := rogersSzegoSum_succ p N x
  linear_combination h1 + h2 - h3

/-- `H_0 = 1`. -/
private lemma rogersSzegoSum_zero (p x : ℂ) : rogersSzegoSum p 0 x = 1 := by
  simp [rogersSzegoSum, qBinom]

/-- `H_1(x) = 1 + x`. -/
private lemma rogersSzegoSum_one (p x : ℂ) : rogersSzegoSum p 1 x = 1 + x := by
  simp [rogersSzegoSum, sum_range_succ, qBinom]

/-- `∑_j [N j]_{q²} q^j = (-q;q)_N`. -/
private lemma rogersSzegoSum_sq_self (q : ℂ) (N : ℕ) :
    rogersSzegoSum (q ^ 2) N q = qPochhammer (-q) q N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp [rogersSzegoSum_zero, qPochhammer]
    | 1 => simp [rogersSzegoSum_one, qPochhammer]
    | N + 2 =>
      rw [rogersSzegoSum_succ_succ, ih (N + 1) (by omega), ih N (by omega)]
      simp only [qPochhammer_succ]
      ring

/-- Gauss: `∑_j (-1)^j [2M j]_p = (p;p²)_M`. -/
private lemma rogersSzegoSum_neg_one_even (p : ℂ) (M : ℕ) :
    rogersSzegoSum p (2 * M) (-1) = qPochhammer p (p ^ 2) M := by
  induction M with
  | zero => simp [rogersSzegoSum_zero, qPochhammer]
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 2 by ring, rogersSzegoSum_succ_succ, ih, qPochhammer_succ]
    ring_nf

/-- Gauss: `∑_j (-1)^j [2M+1 j]_p = 0`. -/
private lemma rogersSzegoSum_neg_one_odd (p : ℂ) (M : ℕ) :
    rogersSzegoSum p (2 * M + 1) (-1) = 0 := by
  induction M with
  | zero => simp [rogersSzegoSum_one]
  | succ M ih =>
    rw [show 2 * (M + 1) + 1 = 2 * M + 1 + 2 by ring, rogersSzegoSum_succ_succ, ih]
    ring



/-- `∫₀^{2π} e^{ikθ} dθ = 2π δ_{k0}` for integer `k`. -/
private lemma integral_exp_intCast_mul_I (k : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (I * k * θ) = if k = 0 then 2 * π else 0 := by
  split_ifs with hk
  · simp [hk]
  · have hc : I * (k : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Int.cast_ne_zero.mpr hk)
    rw [integral_exp_mul_complex hc]
    have h1 : exp (I * k * (2 * π)) = 1 := by
      rw [← exp_int_mul_two_pi_mul_I k]
      ring_nf
    simp [h1]

/-- Integer powers of a point on the circle `|z| = ρ`. -/
private lemma circle_zpow (ρ θ : ℝ) (e : ℤ) :
    ((ρ : ℂ) * exp (θ * I)) ^ e = (ρ : ℂ) ^ e * exp (I * e * θ) := by
  rw [mul_zpow, ← exp_int_mul]; ring_nf

/-- Norms of integer powers of a point on the circle `|z| = ρ`. -/
private lemma norm_circle_zpow {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) (e : ℤ) :
    ‖((ρ : ℂ) * exp (θ * I)) ^ e‖ = ρ ^ e := by
  rw [norm_zpow, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hρ.le]

/-- Constant term of an absolutely convergent Laurent-type series on a circle. -/
private lemma circleConstantTerm_of_hasSum {ι : Type*} [Countable ι] {c : ι → ℂ} {e : ι → ℤ}
    {ρ : ℝ} (hρ : 0 < ρ) (hs : Summable fun i => ‖c i‖ * ρ ^ e i) {f : ℂ → ℂ}
    (hf : ∀ θ : ℝ, HasSum (fun i => c i * ((ρ : ℂ) * exp (θ * I)) ^ e i)
      (f (ρ * exp (θ * I)))) :
    circleConstantTerm f ρ = ∑' i, (if e i = 0 then c i else 0) ∧
      IntervalIntegrable (fun θ : ℝ => f (ρ * exp (θ * I))) volume 0 (2 * Real.pi) := by
  have hcont : ∀ i, Continuous fun θ : ℝ => c i * ((ρ : ℂ) * exp (θ * I)) ^ e i := by
    intro i
    simp_rw [circle_zpow]
    fun_prop
  have hb : ∀ i (θ : ℝ), ‖c i * ((ρ : ℂ) * exp (θ * I)) ^ e i‖ ≤ ‖c i‖ * ρ ^ e i := by
    intro i θ; rw [norm_mul, norm_circle_zpow hρ]
  have hfeq : (fun θ : ℝ => f (ρ * exp (θ * I))) =
      fun θ : ℝ => ∑' i, c i * ((ρ : ℂ) * exp (θ * I)) ^ e i := by
    funext θ; exact (hf θ).tsum_eq.symm
  have hfc : Continuous fun θ : ℝ => f (ρ * exp (θ * I)) := by
    rw [hfeq]; exact continuous_tsum hcont hs hb
  refine ⟨?_, hfc.intervalIntegrable _ _⟩
  have hI := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 2 * Real.pi)
    (F := fun i (θ : ℝ) => c i * ((ρ : ℂ) * exp (θ * I)) ^ e i)
    (f := fun θ : ℝ => f (ρ * exp (θ * I)))
    (fun i _ => ‖c i‖ * ρ ^ e i) (fun i => (hcont i).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall fun θ _ => hb i θ)
    (Filter.Eventually.of_forall fun _ _ => hs) intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => hf θ)
  have hval : ∀ i, (∫ θ in (0 : ℝ)..2 * π, c i * ((ρ : ℂ) * exp (θ * I)) ^ e i) =
      2 * π * (if e i = 0 then c i else 0) := by
    intro i
    simp_rw [circle_zpow]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_exp_intCast_mul_I]
    split_ifs with h
    · simp [h]; ring
    · simp
  simp_rw [hval] at hI
  rw [circleConstantTerm, ← hI.tsum_eq, tsum_mul_left, ← mul_assoc]
  have : (2 * π : ℂ) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [inv_mul_cancel₀ (by exact_mod_cast this), one_mul]



/-- The triple-product terms in base `q²` at `-zq` are `q^{n²} zⁿ`. -/
private lemma term_sq_neg_mul {q z : ℂ} (hq : q ≠ 0) (n : ℤ) :
    term (q ^ 2) (-z * q) n = q ^ (n.natAbs ^ 2) * z ^ n := by
  have h2 : (2 * tri n + n : ℤ) = ((n.natAbs ^ 2 : ℕ) : ℤ) := by
    have := tri_mul_two n
    push_cast; rw [sq_abs]; linarith
  have hneg : ((-1 : ℂ) ^ n) * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_zpow]; norm_num
  have hq2 : (q ^ 2) ^ (tri n) = q ^ (2 * tri n) := by rw [zpow_mul]; norm_cast
  have hpow : q ^ (n.natAbs ^ 2) = q ^ (2 * tri n) * q ^ n := by
    rw [← zpow_natCast, ← zpow_add₀ hq, h2]
  have hz : (-z) ^ n = (-1) ^ n * z ^ n := by rw [neg_eq_neg_one_mul, mul_zpow]
  rw [term, mul_zpow, hq2, hz, hpow]
  linear_combination q ^ (2 * tri n) * z ^ n * q ^ n * hneg

/-- The Jacobi triple-product expansion `rogersThetaProduct q z = ∑ q^{n²} zⁿ`. -/
private lemma hasSum_rogersThetaProduct {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    HasSum (fun n : ℤ => q ^ (n.natAbs ^ 2) * z ^ n) (rogersThetaProduct q z) ∧
      Summable fun n : ℤ => ‖q ^ (n.natAbs ^ 2) * z ^ n‖ := by
  rcases eq_or_ne q 0 with rfl | hq0
  · have h0 : ∀ n : ℤ, n ≠ 0 → (0 : ℂ) ^ (n.natAbs ^ 2) * z ^ n = 0 := fun n hn => by
      simp [hn]
    refine ⟨?_, (hasSum_single (0 : ℤ) fun n hn => by rw [h0 n hn, norm_zero]).summable⟩
    convert hasSum_single (0 : ℤ) h0 using 1
    simp [rogersThetaProduct]
  · have hQ : ‖q ^ 2‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
    have hQ0 : q ^ 2 ≠ 0 := pow_ne_zero _ hq0
    have hZ : -z * q ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hz) hq0
    have hs := summable_norm_term hQ hQ0 hZ
    simp_rw [term_sq_neg_mul hq0] at hs
    refine ⟨?_, hs⟩
    have hj := jtp_ne_zero hQ hQ0 hZ
    simp_rw [term_sq_neg_mul hq0] at hj
    have hP := qPochhammerInf_ne_zero_of_norm_lt_one hQ hQ
    have heq : rogersThetaProduct q z = ∑' n : ℤ, q ^ (n.natAbs ^ 2) * z ^ n := by
      have hrw : q ^ 2 / (-z * q) = -q / z := by field_simp
      rw [hrw] at hj
      have h' := congrArg (qPochhammerInf (q ^ 2) (q ^ 2) * ·) hj
      simp only [← mul_assoc, mul_inv_cancel₀ hP, one_mul] at h'
      rw [rogersThetaProduct, ← h']
      ring
    rw [heq]
    exact hs.of_norm.hasSum


/-- Euler's expansion `1/(w;Q)_∞ = ∑ w^k/(Q;Q)_k` with absolute convergence. -/
private lemma hasSum_inv_qPochhammerInf {Q w : ℂ} (hQ : ‖Q‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => w ^ k / qPochhammer Q Q k) (1 / qPochhammerInf w Q) ∧
      Summable fun k : ℕ => ‖w ^ k / qPochhammer Q Q k‖ := by
  obtain ⟨D, hD⟩ := exists_norm_recip_qPochhammer_le hQ
  have hs : Summable fun k : ℕ => ‖w ^ k / qPochhammer Q Q k‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left D)
    rw [div_eq_mul_inv, norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hD k) (by positivity)
  exact ⟨tsum_div_qPochhammer hQ hw ▸ hs.of_norm.hasSum, hs⟩

/-- The constant term of `rogersThetaProduct q z / (x z^{-d}; Q)_∞` on `|z| = ρ`. -/
private lemma constantTerm_theta_div {q Q x : ℂ} {d : ℕ} (hq : ‖q‖ < 1) (hQ : ‖Q‖ < 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hx : ‖x‖ < ρ ^ d) :
    circleConstantTerm (fun z => rogersThetaProduct q z / qPochhammerInf (x / z ^ d) Q) ρ =
        ∑' k : ℕ, q ^ ((d * k) ^ 2) * x ^ k / qPochhammer Q Q k ∧
      IntervalIntegrable (fun θ : ℝ => rogersThetaProduct q (ρ * exp (θ * I)) /
        qPochhammerInf (x / (ρ * exp (θ * I)) ^ d) Q) volume 0 (2 * π) := by
  obtain ⟨D, hD⟩ := exists_norm_recip_qPochhammer_le hQ
  have hρd : 0 < ρ ^ d := pow_pos hρ d
  set r := ‖x‖ / ρ ^ d with hr
  have hr1 : r < 1 := (div_lt_one hρd).mpr hx
  have hr0 : 0 ≤ r := by positivity
  set a : ℤ → ℂ := fun m => q ^ (m.natAbs ^ 2)
  set c : ℤ × ℕ → ℂ := fun i => a i.1 * (x ^ i.2 / qPochhammer Q Q i.2)
  set e : ℤ × ℕ → ℤ := fun i => i.1 - d * i.2
  have hsa : Summable fun m : ℤ => ‖a m‖ * ρ ^ m := by
    have := (hasSum_rogersThetaProduct hq (z := (ρ : ℂ)) (by exact_mod_cast hρ.ne')).2
    refine this.congr fun m => ?_
    rw [norm_mul, norm_zpow, norm_real, Real.norm_of_nonneg hρ.le]
  have hsb : Summable fun k : ℕ => ‖x ^ k / qPochhammer Q Q k‖ * ρ ^ (-(d * k : ℤ)) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left D)
    rw [div_eq_mul_inv, norm_mul, norm_pow, zpow_neg, zpow_mul, zpow_natCast, zpow_natCast, hr,
      div_pow]
    calc ‖x‖ ^ k * ‖(qPochhammer Q Q k)⁻¹‖ * ((ρ ^ d) ^ k)⁻¹
        ≤ ‖x‖ ^ k * D * ((ρ ^ d) ^ k)⁻¹ := by gcongr; exact hD k
      _ = D * (‖x‖ ^ k / (ρ ^ d) ^ k) := by ring
  have hs : Summable fun i : ℤ × ℕ => ‖c i‖ * ρ ^ e i := by
    refine (hsa.mul_of_nonneg hsb (fun _ => by positivity) (fun _ => by positivity)).congr ?_
    rintro ⟨m, k⟩
    simp only [c, e, norm_mul]
    rw [sub_eq_add_neg, zpow_add₀ hρ.ne']
    ring
  have hf : ∀ θ : ℝ, HasSum (fun i => c i * ((ρ : ℂ) * exp (θ * I)) ^ e i)
      ((fun z => rogersThetaProduct q z / qPochhammerInf (x / z ^ d) Q) (ρ * exp (θ * I))) := by
    intro θ
    set z : ℂ := ρ * exp (θ * I)
    have hz0 : z ≠ 0 := mul_ne_zero (by exact_mod_cast hρ.ne') (exp_ne_zero _)
    have hzn : ‖z‖ = ρ := by
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hρ.le]
    have hw : ‖x / z ^ d‖ < 1 := by
      rw [norm_div, norm_pow, hzn]; exact hr1
    obtain ⟨hT, hTs⟩ := hasSum_rogersThetaProduct hq hz0
    obtain ⟨hE, hEs⟩ := hasSum_inv_qPochhammerInf hQ hw
    have hprod := summable_mul_of_summable_norm hTs hEs
    have heq : rogersThetaProduct q z / qPochhammerInf (x / z ^ d) Q =
        ∑' i : ℤ × ℕ, q ^ (i.1.natAbs ^ 2) * z ^ i.1 *
          ((x / z ^ d) ^ i.2 / qPochhammer Q Q i.2) := by
      rw [← tsum_mul_tsum_of_summable_norm hTs hEs, hT.tsum_eq, hE.tsum_eq, mul_one_div]
    simp only
    rw [heq]
    convert hprod.hasSum using 1
    funext i
    simp only [c, e, a]
    rw [zpow_sub₀ hz0, div_pow, ← pow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    field_simp
    ring
  obtain ⟨h1, h2⟩ := circleConstantTerm_of_hasSum
    (f := fun z => rogersThetaProduct q z / qPochhammerInf (x / z ^ d) Q) hρ hs hf
  refine ⟨?_, h2⟩
  rw [h1]
  have hinj : Function.Injective fun k : ℕ => ((d * k : ℤ), k) := fun k l h => by
    simpa using congrArg Prod.snd h
  rw [← hinj.tsum_eq]
  · congr 1
    funext k
    simp only [c, e, a, sub_self, ite_true]
    have : ((d : ℤ) * k).natAbs = d * k := by
      rw [Int.natAbs_mul]; simp
    rw [this]; ring
  · intro i hi
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp, e] at hi
    exact ⟨i.2, by ext <;> simp; omega⟩

/-- Summation of an absolutely summable double series along antidiagonals. -/
private lemma tsum_prod_eq_tsum_antidiagonal {F : ℕ × ℕ → ℂ} (h : Summable F) :
    ∑' x, F x = ∑' N, ∑ kl ∈ antidiagonal N, F kl := by
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq]
  rw [Summable.tsum_sigma (f := fun c => F (HasAntidiagonal.sigmaAntidiagonalEquivProd c))
    ((Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr h)]
  congr 1
  funext N
  rw [tsum_fintype, ← Finset.sum_coe_sort (antidiagonal N)]
  rfl

/-- Expanding the tails `(-y p^n; p)_∞` by Euler's second identity and summing along
antidiagonals, `p = q²`. -/
private lemma tsum_mul_qExp_eq_tsum_antidiagonal {q y : ℂ} (hq : ‖q‖ < 1) (hy : ‖y‖ < 1) (A : ℕ → ℕ)
    (hA : ∀ n, n ≤ A n) :
    ∑' n, q ^ A n / qPochhammer (q ^ 2) (q ^ 2) n * qPochhammerInf (-(y * (q ^ 2) ^ n)) (q ^ 2) =
      ∑' N, ∑ kl ∈ antidiagonal N, q ^ A kl.1 * ((q ^ 2) ^ (kl.2.choose 2) *
        (y * (q ^ 2) ^ kl.1) ^ kl.2) /
          (qPochhammer (q ^ 2) (q ^ 2) kl.1 * qPochhammer (q ^ 2) (q ^ 2) kl.2) := by
  have hp : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have hp1 : ‖q ^ 2‖ ≤ 1 := hp.le
  obtain ⟨D, hD⟩ := exists_norm_recip_qPochhammer_le hp
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  set F : ℕ × ℕ → ℂ := fun kl => q ^ A kl.1 * ((q ^ 2) ^ (kl.2.choose 2) *
    (y * (q ^ 2) ^ kl.1) ^ kl.2) /
      (qPochhammer (q ^ 2) (q ^ 2) kl.1 * qPochhammer (q ^ 2) (q ^ 2) kl.2) with hF
  have hFs : Summable fun kl => ‖F kl‖ := by
    have hg := (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left D
    have hg' := (summable_geometric_of_lt_one (norm_nonneg y) hy).mul_left D
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun kl => ?_)
      (hg.mul_of_nonneg hg' (fun _ => by positivity) (fun _ => by positivity))
    simp only [F, div_eq_mul_inv, mul_inv, norm_mul, norm_pow]
    have h1 : ‖q‖ ^ A kl.1 ≤ ‖q‖ ^ kl.1 := pow_le_pow_of_le_one (norm_nonneg _) hq.le (hA _)
    have h2 : (‖q‖ ^ 2) ^ kl.2.choose 2 ≤ 1 := pow_le_one₀ (by positivity) (by
      rw [← norm_pow]; exact hp1)
    have h3 : ((‖q‖ ^ 2) ^ kl.1) ^ kl.2 ≤ 1 := pow_le_one₀ (by positivity)
      (pow_le_one₀ (by positivity) (by rw [← norm_pow]; exact hp1))
    have h4 := hD kl.1
    have h5 := hD kl.2
    calc ‖q‖ ^ A kl.1 * ((‖q‖ ^ 2) ^ kl.2.choose 2 * (‖y‖ * (‖q‖ ^ 2) ^ kl.1) ^ kl.2) *
          (‖(qPochhammer (q ^ 2) (q ^ 2) kl.1)⁻¹‖ * ‖(qPochhammer (q ^ 2) (q ^ 2) kl.2)⁻¹‖)
        = ‖q‖ ^ A kl.1 * (‖q‖ ^ 2) ^ kl.2.choose 2 * ((‖q‖ ^ 2) ^ kl.1) ^ kl.2 * ‖y‖ ^ kl.2 *
          ‖(qPochhammer (q ^ 2) (q ^ 2) kl.1)⁻¹‖ * ‖(qPochhammer (q ^ 2) (q ^ 2) kl.2)⁻¹‖ := by
          ring
      _ ≤ ‖q‖ ^ kl.1 * 1 * 1 * ‖y‖ ^ kl.2 * D * D := by gcongr
      _ = D * ‖q‖ ^ kl.1 * (D * ‖y‖ ^ kl.2) := by ring
  have hrow : ∀ n, q ^ A n / qPochhammer (q ^ 2) (q ^ 2) n *
      qPochhammerInf (-(y * (q ^ 2) ^ n)) (q ^ 2) = ∑' j, F (n, j) := by
    intro n
    rw [← tsum_qExp hp, ← tsum_mul_left]
    congr 1; funext j
    simp only [F]
    ring
  simp_rw [hrow]
  rw [← hFs.of_norm.tsum_prod, tsum_prod_eq_tsum_antidiagonal hFs.of_norm]

/-- `∑_{k+j=N} x^j / ((p;p)_k (p;p)_j) = H_N(x) / (p;p)_N`. -/
private lemma sum_antidiagonal_div_qPochhammer {p : ℂ} (x : ℂ) (hp : ∀ k, qPochhammer p p k ≠ 0)
    (N : ℕ) :
    ∑ kl ∈ antidiagonal N, x ^ kl.2 / (qPochhammer p p kl.1 * qPochhammer p p kl.2) =
      rogersSzegoSum p N x / qPochhammer p p N := by
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => x ^ i / (qPochhammer p p j * qPochhammer p p i)), rogersSzegoSum, sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hkN : k + (N - k) = N := by simp at hk; omega
  have h := qBinom_mul_qPochhammer p k (N - k)
  rw [hkN] at h
  have hb : qBinom p N k ≠ 0 := fun h0 => hp N (by rw [← h, h0]; ring)
  rw [← h]
  field_simp [hp k, hp (N - k), hb]

/-- `2 C(j,2) + j = j²`. -/
private lemma choose_two_mul_two_add (j : ℕ) : j.choose 2 * 2 + j = j * j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; nlinarith

/-- `(q²;q²)_N = (q;q)_N (-q;q)_N`. -/
private lemma qPochhammer_sq_sq (q : ℂ) (N : ℕ) :
    qPochhammer (q ^ 2) (q ^ 2) N = qPochhammer q q N * qPochhammer (-q) q N := by
  induction N with
  | zero => simp [qPochhammer]
  | succ N ih => rw [qPochhammer_succ, qPochhammer_succ, qPochhammer_succ, ih]; ring

/-- `(p;p)_{2M} = (p;p²)_M (p²;p²)_M`. -/
private lemma qPochhammer_two_mul (p : ℂ) (M : ℕ) :
    qPochhammer p p (2 * M) = qPochhammer p (p ^ 2) M * qPochhammer (p ^ 2) (p ^ 2) M := by
  induction M with
  | zero => simp [qPochhammer]
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, qPochhammer_succ, qPochhammer_succ, ih,
      qPochhammer_succ, qPochhammer_succ]
    ring

/-- `|q| < 1` implies `|q²| < 1`. -/
private lemma norm_sq_lt_one {q : ℂ} (hq : ‖q‖ < 1) : ‖q ^ 2‖ < 1 := by
  rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero

/-- The tail factorization `(a;p)_∞ = (a;p)_n (a pⁿ;p)_∞` with nonvanishing `(a;p)_n`. -/
private lemma qPochhammerInf_div_qPochhammer {a p : ℂ} (hp : ‖p‖ < 1) (ha : ‖a‖ < 1) (n : ℕ) :
    qPochhammer a p n ≠ 0 ∧
      qPochhammerInf a p / qPochhammer a p n = qPochhammerInf (a * p ^ n) p := by
  have h := qPochhammerInf_mul_qPochhammer (a := a) hp n
  have hne : qPochhammer a p n ≠ 0 := by
    have := qPochhammerInf_ne_zero_of_norm_lt_one ha hp
    rw [h] at this; exact left_ne_zero_of_mul this
  refine ⟨hne, ?_⟩
  rw [h]; field_simp

/-- The series side of DLMF 17.14.2. -/
private lemma rogers_series_H (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, q ^ (n * (n + 1)) /
      (qPochhammer (q ^ 2) (q ^ 2) n * qPochhammer (-q) (q ^ 2) (n + 1))) *
        qPochhammerInf (-q) (q ^ 2) = rogersH q := by
  have hp := norm_sq_lt_one hq
  have hpp : ∀ k, qPochhammer (q ^ 2) (q ^ 2) k ≠ 0 := qPochhammer_self_ne_zero hp
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hnq : ‖-q‖ < 1 := by rwa [norm_neg]
  rw [← tsum_mul_right]
  have hrow : ∀ n : ℕ, q ^ (n * (n + 1)) /
      (qPochhammer (q ^ 2) (q ^ 2) n * qPochhammer (-q) (q ^ 2) (n + 1)) *
        qPochhammerInf (-q) (q ^ 2) = q ^ (n * (n + 1)) / qPochhammer (q ^ 2) (q ^ 2) n *
          qPochhammerInf (-(q ^ 3 * (q ^ 2) ^ n)) (q ^ 2) := by
    intro n
    obtain ⟨hne, hdiv⟩ := qPochhammerInf_div_qPochhammer hp hnq (n + 1)
    rw [show -(q ^ 3 * (q ^ 2) ^ n) = -q * (q ^ 2) ^ (n + 1) by ring, ← hdiv]
    field_simp
  simp_rw [hrow]
  rw [tsum_mul_qExp_eq_tsum_antidiagonal hq hq3 (fun n => n * (n + 1))
    (fun n => Nat.le_mul_of_pos_right n (Nat.succ_pos n)), rogersH]
  congr 1; funext N
  have hterm : ∀ kl ∈ antidiagonal N, q ^ (kl.1 * (kl.1 + 1)) * ((q ^ 2) ^ (kl.2.choose 2) *
      (q ^ 3 * (q ^ 2) ^ kl.1) ^ kl.2) /
        (qPochhammer (q ^ 2) (q ^ 2) kl.1 * qPochhammer (q ^ 2) (q ^ 2) kl.2) =
      q ^ (N * (N + 1)) * (q ^ kl.2 /
        (qPochhammer (q ^ 2) (q ^ 2) kl.1 * qPochhammer (q ^ 2) (q ^ 2) kl.2)) := by
    rintro ⟨k, j⟩ hkj
    rw [mem_antidiagonal] at hkj
    subst hkj
    simp only [← pow_mul, ← pow_add]
    rw [mul_div_assoc', ← pow_add]
    congr 2
    have := choose_two_mul_two_add j
    nlinarith
  rw [sum_congr rfl hterm, ← mul_sum, sum_antidiagonal_div_qPochhammer q hpp,
    rogersSzegoSum_sq_self,
    qPochhammer_sq_sq]
  have h1 := qPochhammer_self_ne_zero hq N
  have h2 : qPochhammer (-q) q N ≠ 0 := by
    have := hpp N; rw [qPochhammer_sq_sq] at this; exact right_ne_zero_of_mul this
  field_simp

/-- The series side of the corrected DLMF 17.14.3. -/
private lemma rogers_series_G (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, q ^ (n * (n + 1)) /
      (qPochhammer (q ^ 2) (q ^ 2) n * qPochhammer (-q) (q ^ 2) n)) *
        qPochhammerInf (-q) (q ^ 2) = rogersG q := by
  have hp := norm_sq_lt_one hq
  have hpp : ∀ k, qPochhammer (q ^ 2) (q ^ 2) k ≠ 0 := qPochhammer_self_ne_zero hp
  have hnq : ‖-q‖ < 1 := by rwa [norm_neg]
  rw [← tsum_mul_right]
  have hrow : ∀ n : ℕ, q ^ (n * (n + 1)) /
      (qPochhammer (q ^ 2) (q ^ 2) n * qPochhammer (-q) (q ^ 2) n) *
        qPochhammerInf (-q) (q ^ 2) = q ^ (n * (n + 1)) / qPochhammer (q ^ 2) (q ^ 2) n *
          qPochhammerInf (-(q * (q ^ 2) ^ n)) (q ^ 2) := by
    intro n
    obtain ⟨hne, hdiv⟩ := qPochhammerInf_div_qPochhammer hp hnq n
    rw [show -(q * (q ^ 2) ^ n) = -q * (q ^ 2) ^ n by ring, ← hdiv]
    field_simp
  simp_rw [hrow]
  rw [tsum_mul_qExp_eq_tsum_antidiagonal hq hq (fun n => n * (n + 1))
    (fun n => Nat.le_mul_of_pos_right n (Nat.succ_pos n)), rogersG]
  congr 1; funext N
  have hterm : ∀ kl ∈ antidiagonal N, q ^ (kl.1 * (kl.1 + 1)) * ((q ^ 2) ^ (kl.2.choose 2) *
      (q * (q ^ 2) ^ kl.1) ^ kl.2) /
        (qPochhammer (q ^ 2) (q ^ 2) kl.1 * qPochhammer (q ^ 2) (q ^ 2) kl.2) =
      q ^ (N * N) * (q ^ kl.swap.2 /
        (qPochhammer (q ^ 2) (q ^ 2) kl.swap.1 * qPochhammer (q ^ 2) (q ^ 2) kl.swap.2)) := by
    rintro ⟨k, j⟩ hkj
    rw [mem_antidiagonal] at hkj
    subst hkj
    simp only [Prod.swap, mul_pow, ← pow_mul, ← pow_add]
    rw [mul_div_assoc', ← pow_add, mul_comm (qPochhammer (q ^ 2) (q ^ 2) j)]
    congr 2
    have := choose_two_mul_two_add j
    linear_combination this
  rw [sum_congr rfl hterm, ← mul_sum,
    Finset.Nat.sum_antidiagonal_swap (f := fun kl => q ^ kl.2 /
      (qPochhammer (q ^ 2) (q ^ 2) kl.1 * qPochhammer (q ^ 2) (q ^ 2) kl.2)),
    sum_antidiagonal_div_qPochhammer q hpp, rogersSzegoSum_sq_self, qPochhammer_sq_sq]
  have h1 := qPochhammer_self_ne_zero hq N
  have h2 : qPochhammer (-q) q N ≠ 0 := by
    have := hpp N; rw [qPochhammer_sq_sq] at this; exact right_ne_zero_of_mul this
  field_simp

/-- Gauss's alternating sum collapses a series to its even terms. -/
private lemma tsum_rogersSzegoSum_neg_one {q : ℂ} (hq : ‖q‖ < 1) (E : ℕ → ℕ)
    (hE : ∀ M, M ≤ E (2 * M)) :
    ∑' N, q ^ E N * (rogersSzegoSum (q ^ 2) N (-1) / qPochhammer (q ^ 2) (q ^ 2) N) =
      ∑' M, q ^ E (2 * M) / qPochhammer (q ^ 4) (q ^ 4) M := by
  have hp := norm_sq_lt_one hq
  have hq4 : ‖q ^ 4‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have h4 : (q ^ 2) ^ 2 = q ^ 4 := by ring
  have heven : ∀ M, q ^ E (2 * M) * (rogersSzegoSum (q ^ 2) (2 * M) (-1) /
      qPochhammer (q ^ 2) (q ^ 2) (2 * M)) = q ^ E (2 * M) / qPochhammer (q ^ 4) (q ^ 4) M := by
    intro M
    have hne := qPochhammer_self_ne_zero hp (2 * M)
    rw [qPochhammer_two_mul, h4] at hne ⊢
    rw [rogersSzegoSum_neg_one_even, h4]
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    field_simp
  obtain ⟨D, hD⟩ := exists_norm_recip_qPochhammer_le hq4
  have hs : Summable fun M => q ^ E (2 * M) / qPochhammer (q ^ 4) (q ^ 4) M := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left D)
      fun M => ?_
    rw [div_eq_mul_inv, norm_mul, norm_pow, mul_comm]
    exact mul_le_mul (hD M) (pow_le_pow_of_le_one (norm_nonneg _) hq.le (hE M)) (by positivity)
      ((norm_nonneg _).trans (hD 0))
  rw [← tsum_even_add_odd]
  · simp only [rogersSzegoSum_neg_one_odd, zero_div, mul_zero, tsum_zero, add_zero, heven]
  · simpa only [heven] using hs
  · simp only [rogersSzegoSum_neg_one_odd, zero_div, mul_zero]; exact summable_zero

/-- The series side of DLMF 17.14.4. -/
private lemma rogers_series_G_four (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, q ^ (n * n) / (qPochhammer (q ^ 2) (q ^ 2) n * qPochhammer q (q ^ 2) n)) *
        qPochhammerInf q (q ^ 2) = rogersG (q ^ 4) := by
  have hp := norm_sq_lt_one hq
  have hpp : ∀ k, qPochhammer (q ^ 2) (q ^ 2) k ≠ 0 := qPochhammer_self_ne_zero hp
  have hnq : ‖-q‖ < 1 := by rwa [norm_neg]
  rw [← tsum_mul_right]
  have hrow : ∀ n : ℕ, q ^ (n * n) /
      (qPochhammer (q ^ 2) (q ^ 2) n * qPochhammer q (q ^ 2) n) *
        qPochhammerInf q (q ^ 2) = q ^ (n * n) / qPochhammer (q ^ 2) (q ^ 2) n *
          qPochhammerInf (-(-q * (q ^ 2) ^ n)) (q ^ 2) := by
    intro n
    obtain ⟨hne, hdiv⟩ := qPochhammerInf_div_qPochhammer hp hq n
    rw [show -(-q * (q ^ 2) ^ n) = q * (q ^ 2) ^ n by ring, ← hdiv]
    field_simp
  simp_rw [hrow]
  rw [tsum_mul_qExp_eq_tsum_antidiagonal hq hnq (fun n => n * n)
    (fun n => Nat.le_mul_self n), rogersG]
  have hterm : ∀ N, ∀ kl ∈ antidiagonal N, q ^ (kl.1 * kl.1) * ((q ^ 2) ^ (kl.2.choose 2) *
      (-q * (q ^ 2) ^ kl.1) ^ kl.2) /
        (qPochhammer (q ^ 2) (q ^ 2) kl.1 * qPochhammer (q ^ 2) (q ^ 2) kl.2) =
      q ^ (N * N) * ((-1) ^ kl.2 /
        (qPochhammer (q ^ 2) (q ^ 2) kl.1 * qPochhammer (q ^ 2) (q ^ 2) kl.2)) := by
    rintro N ⟨k, j⟩ hkj
    rw [mem_antidiagonal] at hkj
    subst hkj
    rw [mul_div_assoc']
    congr 1
    have hexp : k * k + (j.choose 2 * 2 + j) + 2 * k * j = (k + j) * (k + j) := by
      rw [choose_two_mul_two_add]; ring
    rw [← hexp]
    ring
  simp_rw [fun N => sum_congr rfl (hterm N), ← mul_sum, sum_antidiagonal_div_qPochhammer _ hpp]
  rw [tsum_rogersSzegoSum_neg_one hq (fun N => N * N) (fun M => by nlinarith)]
  congr 1; funext M
  rw [← pow_mul]; ring_nf

/-- The series side of DLMF 17.14.5. -/
private lemma rogers_series_H_four (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, q ^ (n * n + 2 * n) /
      (qPochhammer (q ^ 2) (q ^ 2) n * qPochhammer q (q ^ 2) (n + 1))) *
        qPochhammerInf q (q ^ 2) = rogersH (q ^ 4) := by
  have hp := norm_sq_lt_one hq
  have hpp : ∀ k, qPochhammer (q ^ 2) (q ^ 2) k ≠ 0 := qPochhammer_self_ne_zero hp
  have hq3 : ‖-q ^ 3‖ < 1 := by
    rw [norm_neg, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  rw [← tsum_mul_right]
  have hrow : ∀ n : ℕ, q ^ (n * n + 2 * n) /
      (qPochhammer (q ^ 2) (q ^ 2) n * qPochhammer q (q ^ 2) (n + 1)) *
        qPochhammerInf q (q ^ 2) = q ^ (n * n + 2 * n) / qPochhammer (q ^ 2) (q ^ 2) n *
          qPochhammerInf (-(-q ^ 3 * (q ^ 2) ^ n)) (q ^ 2) := by
    intro n
    obtain ⟨hne, hdiv⟩ := qPochhammerInf_div_qPochhammer hp hq (n + 1)
    rw [show -(-q ^ 3 * (q ^ 2) ^ n) = q * (q ^ 2) ^ (n + 1) by ring, ← hdiv]
    field_simp
  simp_rw [hrow]
  rw [tsum_mul_qExp_eq_tsum_antidiagonal hq hq3 (fun n => n * n + 2 * n)
    (fun n => by nlinarith), rogersH]
  have hterm : ∀ N, ∀ kl ∈ antidiagonal N, q ^ (kl.1 * kl.1 + 2 * kl.1) *
      ((q ^ 2) ^ (kl.2.choose 2) * (-q ^ 3 * (q ^ 2) ^ kl.1) ^ kl.2) /
        (qPochhammer (q ^ 2) (q ^ 2) kl.1 * qPochhammer (q ^ 2) (q ^ 2) kl.2) =
      q ^ (N * N + 2 * N) * ((-1) ^ kl.2 /
        (qPochhammer (q ^ 2) (q ^ 2) kl.1 * qPochhammer (q ^ 2) (q ^ 2) kl.2)) := by
    rintro N ⟨k, j⟩ hkj
    rw [mem_antidiagonal] at hkj
    subst hkj
    rw [mul_div_assoc']
    congr 1
    have hexp : k * k + 2 * k + (j.choose 2 * 2 + j) + 2 * j + 2 * k * j =
        (k + j) * (k + j) + 2 * (k + j) := by
      rw [choose_two_mul_two_add]; ring
    rw [← hexp]
    ring
  simp_rw [fun N => sum_congr rfl (hterm N), ← mul_sum, sum_antidiagonal_div_qPochhammer _ hpp]
  rw [tsum_rogersSzegoSum_neg_one hq (fun N => N * N + 2 * N) (fun M => by nlinarith)]
  congr 1; funext M
  rw [← pow_mul]; ring_nf

/-- `(a;q)_∞ = (a;q²)_∞ (aq;q²)_∞`. -/
private lemma qPochhammerInf_eq_mul_sq {a q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf a q = qPochhammerInf a (q ^ 2) * qPochhammerInf (a * q) (q ^ 2) := by
  have hp := norm_sq_lt_one hq
  rw [qPochhammerInf, qPochhammerInf, qPochhammerInf, ← tprod_even_mul_odd]
  · congr 1
    · congr 1; funext k; rw [pow_mul]
    · congr 1; funext k; rw [pow_succ, pow_mul]; ring
  · convert multipliable_one_sub_mul_pow (w := a) hp using 2; ring
  · convert multipliable_one_sub_mul_pow (w := a * q) hp using 2; ring

/-- `(a;p)_∞ (-a;p)_∞ = (a²;p²)_∞`. -/
private lemma qPochhammerInf_mul_neg {a p : ℂ} (hp : ‖p‖ < 1) :
    qPochhammerInf a p * qPochhammerInf (-a) p = qPochhammerInf (a ^ 2) (p ^ 2) := by
  rw [qPochhammerInf, qPochhammerInf, qPochhammerInf,
    ← (multipliable_one_sub_mul_pow hp).tprod_mul (multipliable_one_sub_mul_pow hp)]
  congr 1; funext k; ring

/-- The constant term is linear: division by a constant. -/
private lemma circleConstantTerm_div_const (g : ℂ → ℂ) (ρ : ℝ) (C : ℂ) :
    circleConstantTerm (fun z => g z / C) ρ = circleConstantTerm g ρ / C := by
  rw [circleConstantTerm, circleConstantTerm, intervalIntegral.integral_div, mul_div_assoc]

/-! ### The Rogers constant terms -/

/-- First infinite-product constant term; all three displayed equalities are retained. -/
@[dlmf 17.14.E2]
theorem rogers_constantTerm_H (q : ℂ) (hq : ‖q‖<1) (ρ : ℝ) (hρ : 1<ρ) :
    let f := fun z => rogersThetaProduct q z /
      (qPochhammerInf (q^2/z) (q^2) * qPochhammerInf (-q) (q^2) *
        qPochhammerInf (q/z) (q^2))
    let g := fun z => rogersThetaProduct q z / qPochhammerInf (q/z) q
    (∑' n : ℕ, q^(n*(n+1)) /
      (qPochhammer (q^2) (q^2) n * qPochhammer (-q) (q^2) (n+1))) =
        circleConstantTerm f ρ ∧
    circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf (-q) (q^2) ∧
    circleConstantTerm g ρ / qPochhammerInf (-q) (q^2) =
      rogersH q / qPochhammerInf (-q) (q^2) ∧
    IntervalIntegrable (fun θ : ℝ => f (ρ * exp (θ * I))) volume 0 (2*Real.pi) := by
  intro f g
  have hρ0 : 0 < ρ := by linarith
  have hfg : f = fun z => g z / qPochhammerInf (-q) (q ^ 2) := by
    funext z
    simp only [f, g]
    rw [qPochhammerInf_eq_mul_sq hq (a := q / z), show q / z * q = q ^ 2 / z by ring]
    ring
  obtain ⟨hCT, hint⟩ := constantTerm_theta_div (q := q) (Q := q) (x := q) (d := 1) hq hq hρ0
    (by rw [pow_one]; linarith)
  simp only [pow_one] at hCT hint
  have hC : qPochhammerInf (-q) (q ^ 2) ≠ 0 :=
    qPochhammerInf_ne_zero_of_norm_lt_one (by rwa [norm_neg]) (norm_sq_lt_one hq)
  have h3 : circleConstantTerm g ρ = rogersH q := by
    rw [show g = fun z => rogersThetaProduct q z / qPochhammerInf (q / z) q from rfl, hCT,
      rogersH]
    congr 1; funext k; ring
  have h2 : circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf (-q) (q ^ 2) := by
    rw [hfg, circleConstantTerm_div_const]
  refine ⟨?_, h2, by rw [h3], ?_⟩
  · rw [h2, h3, eq_div_iff hC, rogers_series_H q hq]
  · rw [hfg]; exact hint.div_const _

/-- Corrected 17.14.3: the finite factor is `(-q;q²)_n`, rather than the repeated `n+1`.
The constant-term side and G(q) side are retained exactly. -/
@[dlmf 17.14.E3]
theorem rogers_constantTerm_G_corrected (q : ℂ) (hq : ‖q‖<1) (ρ : ℝ) (hρ : 1<ρ) :
    let f := fun z => rogersThetaProduct q z /
      (qPochhammerInf z⁻¹ (q^2) * qPochhammerInf (-q) (q^2) *
        qPochhammerInf (q/z) (q^2))
    let g := fun z => rogersThetaProduct q z / qPochhammerInf z⁻¹ q
    (∑' n : ℕ, q^(n*(n+1)) /
      (qPochhammer (q^2) (q^2) n * qPochhammer (-q) (q^2) n)) =
        circleConstantTerm f ρ ∧
    circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf (-q) (q^2) ∧
    circleConstantTerm g ρ / qPochhammerInf (-q) (q^2) =
      rogersG q / qPochhammerInf (-q) (q^2) ∧
    IntervalIntegrable (fun θ : ℝ => f (ρ * exp (θ * I))) volume 0 (2*Real.pi) := by
  intro f g
  have hρ0 : 0 < ρ := by linarith
  have hfg : f = fun z => g z / qPochhammerInf (-q) (q ^ 2) := by
    funext z
    simp only [f, g]
    rw [qPochhammerInf_eq_mul_sq hq (a := z⁻¹), show z⁻¹ * q = q / z by ring]
    ring
  obtain ⟨hCT, hint⟩ := constantTerm_theta_div (q := q) (Q := q) (x := 1) (d := 1) hq hq hρ0
    (by rw [pow_one, norm_one]; linarith)
  simp only [pow_one, one_div] at hCT hint
  have hC : qPochhammerInf (-q) (q ^ 2) ≠ 0 :=
    qPochhammerInf_ne_zero_of_norm_lt_one (by rwa [norm_neg]) (norm_sq_lt_one hq)
  have h3 : circleConstantTerm g ρ = rogersG q := by
    rw [show g = fun z => rogersThetaProduct q z / qPochhammerInf z⁻¹ q from rfl, hCT,
      rogersG]
    congr 1; funext k; ring
  have h2 : circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf (-q) (q ^ 2) := by
    rw [hfg, circleConstantTerm_div_const]
  refine ⟨?_, h2, by rw [h3], ?_⟩
  · rw [h2, h3, eq_div_iff hC, rogers_series_G q hq]
  · rw [hfg]; exact hint.div_const _

/-- The constant-term form of G(q⁴). -/
@[dlmf 17.14.E4]
theorem rogers_constantTerm_G_four (q : ℂ) (hq : ‖q‖<1) (ρ : ℝ) (hρ : 1<ρ) :
    let f := fun z => rogersThetaProduct q z /
      (qPochhammerInf (-z⁻¹) (q^2) * qPochhammerInf q (q^2) *
        qPochhammerInf z⁻¹ (q^2))
    let g := fun z => rogersThetaProduct q z / qPochhammerInf (z⁻¹^2) (q^4)
    (∑' n : ℕ, q^(n*n) / (qPochhammer (q^2) (q^2) n * qPochhammer q (q^2) n)) =
        circleConstantTerm f ρ ∧
    circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf q (q^2) ∧
    circleConstantTerm g ρ / qPochhammerInf q (q^2) =
      rogersG (q^4) / qPochhammerInf q (q^2) ∧
    IntervalIntegrable (fun θ : ℝ => f (ρ * exp (θ * I))) volume 0 (2*Real.pi) := by
  intro f g
  have hρ0 : 0 < ρ := by linarith
  have hp := norm_sq_lt_one hq
  have hfg : f = fun z => g z / qPochhammerInf q (q ^ 2) := by
    funext z
    simp only [f, g]
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, ← qPochhammerInf_mul_neg hp]
    ring
  have hq4 : ‖q ^ 4‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  obtain ⟨hCT, hint⟩ := constantTerm_theta_div (q := q) (Q := q ^ 4) (x := 1) (d := 2) hq hq4
    hρ0 (by rw [norm_one]; nlinarith)
  simp only [one_div, ← inv_pow] at hCT hint
  have hC : qPochhammerInf q (q ^ 2) ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hq hp
  have h3 : circleConstantTerm g ρ = rogersG (q ^ 4) := by
    rw [show g = fun z => rogersThetaProduct q z / qPochhammerInf (z⁻¹ ^ 2) (q ^ 4) from rfl,
      hCT, rogersG]
    congr 1; funext k; ring
  have h2 : circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf q (q ^ 2) := by
    rw [hfg, circleConstantTerm_div_const]
  refine ⟨?_, h2, by rw [h3], ?_⟩
  · rw [h2, h3, eq_div_iff hC, rogers_series_G_four q hq]
  · rw [hfg]; exact hint.div_const _

/-- The constant-term form of H(q⁴). -/
@[dlmf 17.14.E5]
theorem rogers_constantTerm_H_four (q : ℂ) (hq : ‖q‖<1) (ρ : ℝ) (hρ : 1<ρ) :
    let f := fun z => rogersThetaProduct q z /
      (qPochhammerInf (-q^2/z) (q^2) * qPochhammerInf q (q^2) *
        qPochhammerInf (q^2/z) (q^2))
    let g := fun z => rogersThetaProduct q z / qPochhammerInf (q^4/z^2) (q^4)
    (∑' n : ℕ, q^(n*n+2*n) /
      (qPochhammer (q^2) (q^2) n * qPochhammer q (q^2) (n+1))) =
        circleConstantTerm f ρ ∧
    circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf q (q^2) ∧
    circleConstantTerm g ρ / qPochhammerInf q (q^2) =
      rogersH (q^4) / qPochhammerInf q (q^2) ∧
    IntervalIntegrable (fun θ : ℝ => f (ρ * exp (θ * I))) volume 0 (2*Real.pi) := by
  intro f g
  have hρ0 : 0 < ρ := by linarith
  have hp := norm_sq_lt_one hq
  have hfg : f = fun z => g z / qPochhammerInf q (q ^ 2) := by
    funext z
    simp only [f, g]
    rw [show q ^ 4 / z ^ 2 = (q ^ 2 / z) ^ 2 by ring, show q ^ 4 = (q ^ 2) ^ 2 by ring,
      ← qPochhammerInf_mul_neg hp, neg_div]
    ring
  have hq4 : ‖q ^ 4‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  obtain ⟨hCT, hint⟩ := constantTerm_theta_div (q := q) (Q := q ^ 4) (x := q ^ 4) (d := 2) hq hq4
    hρ0 (by nlinarith)
  have hC : qPochhammerInf q (q ^ 2) ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hq hp
  have h3 : circleConstantTerm g ρ = rogersH (q ^ 4) := by
    rw [show g = fun z => rogersThetaProduct q z / qPochhammerInf (q ^ 4 / z ^ 2) (q ^ 4) from rfl,
      hCT, rogersH]
    congr 1; funext k; ring
  have h2 : circleConstantTerm f ρ = circleConstantTerm g ρ / qPochhammerInf q (q ^ 2) := by
    rw [hfg, circleConstantTerm_div_const]
  refine ⟨?_, h2, by rw [h3], ?_⟩
  · rw [h2, h3, eq_div_iff hC, rogers_series_H_four q hq]
  · rw [hfg]; exact hint.div_const _

end DLMF.QHypergeometric
