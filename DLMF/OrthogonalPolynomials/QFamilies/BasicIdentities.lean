/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Wilson
public import DLMF.OrthogonalPolynomials.GegenbauerSeries
public import DLMF.QSeries.Identities
public import DLMF.OrthogonalPolynomials.QOrthogonalityTools
public import TauCeti.Probability.Distributions.LogNormal.Basic

/-!
# Basic identities of q-orthogonal polynomial families

Finite basic hypergeometric formulas, recurrences and duality of the q-orthogonal polynomial
families.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.QFamilies`.
This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter DLMF.QSeries

open scoped Real Nat Topology NNReal ENNReal

open DLMF.Hypergeometric

open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- Terminating basic hypergeometric sum with the standard integer exponent
`1 + s - r`; in particular this handles both ₁phi₁ and balanced ₄phi₃. -/
def terminatingBasicHG (n : ℕ) (a b : List ℂ) (q z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (a.map (fun t => qPochhammer t q k)).prod /
      ((b.map (fun t => qPochhammer t q k)).prod * qPochhammer q q k) *
      ((-1 : ℂ) ^ k * q ^ (k * (k - 1) / 2)) ^ (1 + (b.length : ℤ) - a.length) * z ^ k

/-- The `q`-Hahn polynomial `Q_n(x; a, b, N; q)` as a terminating `₃φ₂` (DLMF 18.27.3). -/
@[dlmf 18.27.E3]
def qHahn (a b q : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1), x] [a * q, q⁻¹ ^ N] q q

/-- The big `q`-Jacobi polynomial `P_n(x; a, b, c; q)` as a terminating `₃φ₂` (DLMF 18.27.5). -/
@[dlmf 18.27.E5]
def bigQJacobi (a b c q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1), x] [a * q, c * q] q q

/-- The little `q`-Jacobi polynomial `p_n(x; a, b; q)` as a terminating `₂φ₁` (DLMF 18.27.13). -/
@[dlmf 18.27.E13]
def littleQJacobi (a b q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1)] [a * q] q (q * x)

/-- The little `q`-Laguerre (Wall) polynomial, the little `q`-Jacobi polynomial with `b = 0`
(DLMF 18.27.14_5). -/
@[dlmf 18.27.E14_5]
def littleQLaguerre (a q : ℂ) (n : ℕ) (x : ℂ) : ℂ := littleQJacobi a 0 q n x

/-- The `q`-Laguerre polynomial `L_n^{(α)}(x; q)` as a terminating `₁φ₁` (DLMF 18.27.15). -/
@[dlmf 18.27.E15]
def qLaguerre (α q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  qPochhammer (q ^ (α + 1)) q n / qPochhammer q q n *
    terminatingBasicHG n [q⁻¹ ^ n] [q ^ (α + 1)] q (-x * q ^ (n + α + 1))

/-- The Stieltjes–Wigert polynomial `S_n(x; q)` as an explicit finite sum (DLMF 18.27.18). -/
@[dlmf 18.27.E18]
def stieltjesWigert (q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), q ^ (k ^ 2) * (-x) ^ k /
    (qPochhammer q q k * qPochhammer q q (n - k))

/-- The discrete `q`-Hermite I polynomial `h_n(x; q)` as an explicit finite sum (DLMF 18.27.21). -/
@[dlmf 18.27.E21]
def discreteQHermiteI (q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  qPochhammer q q n * ∑ k ∈ Finset.range (n / 2 + 1),
    (-1 : ℂ) ^ k * q ^ (k * (k - 1)) * x ^ (n - 2 * k) /
      (qPochhammer (q ^ 2) (q ^ 2) k * qPochhammer q q (n - 2 * k))

/-- The discrete `q`-Hermite II polynomial `h̃_n(x; q)` as an explicit finite sum
(DLMF 18.27.23). -/
@[dlmf 18.27.E23]
def discreteQHermiteII (q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  qPochhammer q q n * ∑ k ∈ Finset.range (n / 2 + 1),
    (-1 : ℂ) ^ k * q⁻¹ ^ (2 * n * k) * q ^ (k * (2 * k + 1)) * x ^ (n - 2 * k) /
      (qPochhammer (q ^ 2) (q ^ 2) k * qPochhammer q q (n - 2 * k))

/-- Finite polynomial form. The displayed formula requires `a ≠ 0`; claims below
retain that hypothesis rather than assigning continuation values at `a = 0`. -/
@[dlmf 18.28.E1]
def askeyWilson (a b c d q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  a⁻¹ ^ n * ∑ k ∈ Finset.range (n + 1), q ^ k *
    qPochhammer (a * b * q ^ k) q (n - k) * qPochhammer (a * c * q ^ k) q (n - k) *
    qPochhammer (a * d * q ^ k) q (n - k) * qPochhammer (q⁻¹ ^ n) q k *
    qPochhammer (a * b * c * d * q ^ ((n : ℤ) - 1)) q k / qPochhammer q q k *
    ∏ j ∈ Finset.range k, (1 - 2 * a * q ^ j * x + a ^ 2 * q ^ (2 * j))

/-- The Askey–Wilson polynomial in the Laurent variable `z`, `x = (z + z⁻¹)/2`, as a
terminating `₄φ₃` (DLMF 18.28.1_5). -/
@[dlmf 18.28.E1_5]
def askeyWilsonLaurent (a b c d q : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * c * d * q ^ ((n : ℤ) - 1), a * z, a / z]
    [a * b, a * c, a * d] q q

/-- The Al-Salam–Chihara polynomials, the Askey–Wilson polynomials with `c = d = 0`
(DLMF 18.28.7). -/
@[dlmf 18.28.E7]
def alSalamChihara (a b q : ℂ) (n : ℕ) (x : ℂ) : ℂ := askeyWilson a b 0 0 q n x

/-- Laurent argument `z`, representing the polynomial argument `(z + z⁻¹)/2`. -/
@[dlmf 18.28.E16]
def continuousQHermiteLaurent (q : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  qPochhammer q q n * qGegenbauer 0 q n z

/-- The `q`-Racah polynomial `R_n(x; α, β, γ, δ | q)` as a terminating `₄φ₃` (DLMF 18.28.19). -/
@[dlmf 18.28.E19]
def qRacah (a b c d q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), q ^ k * qPochhammer (q⁻¹ ^ n) q k *
    qPochhammer (a * b * q ^ (n + 1)) q k /
      (qPochhammer (a * q) q k * qPochhammer (b * d * q) q k *
        qPochhammer (c * q) q k * qPochhammer q q k) *
      ∏ j ∈ Finset.range k, (1 - q ^ j * x + c * d * q ^ (2 * j + 1))

/-- The q-Hahn difference operator is triangular on the q-Pochhammer basis. -/
private lemma qHahn_basis_step {q x : ℂ} (hq : q ≠ 0) (hx : x ≠ 0) (a b Q : ℂ) (k : ℕ) :
    (1 - a * q / x) * (1 - Q / x) *
        (qPochhammer (x / q) q (k + 1) - qPochhammer x q (k + 1)) +
      a * q * (1 - 1 / x) * (b - Q / (q * x)) *
        (qPochhammer (q * x) q (k + 1) - qPochhammer x q (k + 1)) =
      (q⁻¹ ^ (k + 1) - 1) * (1 - a * b * q ^ (k + 2)) * qPochhammer x q (k + 1) -
        (1 - q ^ (k + 1)) / q ^ (k + 1) * (1 - a * q ^ (k + 1)) *
          (1 - Q * q ^ k) * qPochhammer x q k := by
  have hp : (1 - x) * qPochhammer (q * x) q (k + 1) =
      (1 - x * q ^ (k + 1)) * qPochhammer x q (k + 1) := by
    rw [mul_comm q x, ← qPochhammer_succ', qPochhammer_succ]
    ring
  have hm : qPochhammer (x / q) q (k + 1) = (1 - x / q) * qPochhammer x q k := by
    rw [qPochhammer_succ', div_mul_cancel₀ _ hq]
  rw [hm]
  rw [qPochhammer_succ x q k] at ⊢ hp
  simp only [pow_succ, inv_pow] at ⊢ hp
  field_simp
  linear_combination -a * (b * q * x - Q) * q ^ (k + 1) * hp

/-- The terminating q-Hahn series is an eigenfunction of its q-difference operator. -/
private lemma qHahn_difference_equation_aux {a b q : ℂ} (hq : q ≠ 0) (hqn : ‖q‖ < 1)
    (N n : ℕ) (hA : ∀ k ≤ n, qPochhammer (a * q) q k ≠ 0)
    (hN : ∀ k ≤ n, qPochhammer (q⁻¹ ^ N) q k ≠ 0)
    {x : ℂ} (hx : x ≠ 0) :
    (1 - a * q / x) * (1 - q⁻¹ ^ N / x) *
        (qHahn a b q N n (x / q) - qHahn a b q N n x) +
      a * q * (1 - 1 / x) * (b - q⁻¹ ^ N / (q * x)) *
        (qHahn a b q N n (q * x) - qHahn a b q N n x) =
      (q⁻¹ ^ n - 1) * (1 - a * b * q ^ (n + 1)) * qHahn a b q N n x := by
  let c (k : ℕ) := qPochhammer (q⁻¹ ^ n) q k * qPochhammer (a * b * q ^ (n + 1)) q k * q ^ k /
    (qPochhammer (a * q) q k * qPochhammer (q⁻¹ ^ N) q k * qPochhammer q q k)
  let e (k : ℕ) := (q⁻¹ ^ k - 1) * (1 - a * b * q ^ (k + 1))
  let L (k : ℕ) := (1 - q ^ (k + 1)) / q ^ (k + 1) * (1 - a * q ^ (k + 1)) *
    (1 - q⁻¹ ^ N * q ^ k)
  have hc (k : ℕ) (hk : k < n) : c (k + 1) * L k = (e k - e n) * c k := by
    have hAk := hA k (by omega)
    have hNk := hN k (by omega)
    have hqk := qPochhammer_self_ne_zero hqn k
    have hA1 : 1 - a * q * q ^ k ≠ 0 := by
      have h := hA (k + 1) (by omega)
      rw [qPochhammer_succ] at h
      exact (mul_ne_zero_iff.mp h).2
    have hN1 : 1 - q⁻¹ ^ N * q ^ k ≠ 0 := by
      have h := hN (k + 1) (by omega)
      rw [qPochhammer_succ] at h
      exact (mul_ne_zero_iff.mp h).2
    have hq1 : 1 - q * q ^ k ≠ 0 := by
      have h := qPochhammer_self_ne_zero hqn (k + 1)
      rw [qPochhammer_succ] at h
      exact (mul_ne_zero_iff.mp h).2
    have hraw : c (k + 1) * ((1 - a * q * q ^ k) * (1 - q⁻¹ ^ N * q ^ k) * (1 - q * q ^ k)) =
        c k * q * (1 - q⁻¹ ^ n * q ^ k) * (1 - a * b * q ^ (n + 1) * q ^ k) := by
      dsimp only [c]
      simp only [qPochhammer_succ]
      generalize qPochhammer (a * q) q k = A at hAk ⊢
      generalize qPochhammer (q⁻¹ ^ N) q k = M at hNk ⊢
      generalize qPochhammer q q k = F at hqk ⊢
      generalize 1 - a * q * q ^ k = U at hA1 ⊢
      generalize 1 - q⁻¹ ^ N * q ^ k = V at hN1 ⊢
      generalize 1 - q * q ^ k = W at hq1 ⊢
      field_simp
      ring
    have hL : L k = ((1 - a * q * q ^ k) * (1 - q⁻¹ ^ N * q ^ k) * (1 - q * q ^ k)) / q ^ (k + 1) := by
      dsimp only [L]
      ring
    rw [hL, ← mul_div_assoc, hraw]
    dsimp only [e]
    simp only [inv_pow]
    field_simp
    ring
  let R (k : ℕ) := (1 - a * q / x) * (1 - q⁻¹ ^ N / x) *
      (qPochhammer (x / q) q k - qPochhammer x q k) +
      a * q * (1 - 1 / x) * (b - q⁻¹ ^ N / (q * x)) *
      (qPochhammer (q * x) q k - qPochhammer x q k) - e n * qPochhammer x q k
  let G (k : ℕ) := c k * (e k - e n) * qPochhammer x q k
  have ht (k : ℕ) (hk : k < n) : c (k + 1) * R (k + 1) = G (k + 1) - G k := by
    dsimp only [R, G]
    rw [qHahn_basis_step hq hx a b (q⁻¹ ^ N)]
    change c (k + 1) * (e (k + 1) * qPochhammer x q (k + 1) -
      L k * qPochhammer x q k - e n * qPochhammer x q (k + 1)) = _
    linear_combination -(qPochhammer x q k) * hc k hk
  have hkey : ∑ k ∈ Finset.range (n + 1), c k * R k = 0 := by
    rw [Finset.sum_range_succ']
    rw [Finset.sum_congr rfl fun k hk => ht k (Finset.mem_range.mp hk), Finset.sum_range_sub]
    simp only [G, R, c, e, qPochhammer_zero, pow_zero, one_mul, sub_self, zero_mul,
      mul_zero, zero_sub, div_one]
    ring
  have hpoly (z : ℂ) : qHahn a b q N n z =
      ∑ k ∈ Finset.range (n + 1), c k * qPochhammer z q k := by
    unfold qHahn terminatingBasicHG
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.length_cons,
      List.length_nil, mul_one]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      show (1 + (2 : ℤ) - 3) = 0 by norm_num, zpow_zero, mul_one]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [c]
    ring
  rw [hpoly, hpoly, hpoly]
  have he : ∑ k ∈ Finset.range (n + 1), c k * R k =
      (1 - a * q / x) * (1 - q⁻¹ ^ N / x) *
        ((∑ k ∈ Finset.range (n + 1), c k * qPochhammer (x / q) q k) -
          ∑ k ∈ Finset.range (n + 1), c k * qPochhammer x q k) +
      a * q * (1 - 1 / x) * (b - q⁻¹ ^ N / (q * x)) *
        ((∑ k ∈ Finset.range (n + 1), c k * qPochhammer (q * x) q k) -
          ∑ k ∈ Finset.range (n + 1), c k * qPochhammer x q k) -
      e n * ∑ k ∈ Finset.range (n + 1), c k * qPochhammer x q k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [R]
    ring
  rw [hkey] at he
  exact sub_eq_zero.mp he.symm

/-- The finite q-Hahn weight satisfies the Pearson balance identity. -/
private lemma qHahn_weight_balance {a b q : ℂ} (ha : a ≠ 0) (hq : q ≠ 0) (hqn : ‖q‖ < 1)
    {N y : ℕ} (hy : y < N) :
    (qPochhammer q q N / (qPochhammer q q (y + 1) * qPochhammer q q (N - (y + 1))) *
        qPochhammer (a * q) q (y + 1) * qPochhammer (b * q) q (N - (y + 1)) / (a * q) ^ (y + 1)) *
      (a * q * (1 - 1 / (q⁻¹ ^ (y + 1))) * (b - q⁻¹ ^ N / (q * q⁻¹ ^ (y + 1)))) =
    (qPochhammer q q N / (qPochhammer q q y * qPochhammer q q (N - y)) *
        qPochhammer (a * q) q y * qPochhammer (b * q) q (N - y) / (a * q) ^ y) *
      ((1 - a * q / (q⁻¹ ^ y)) * (1 - q⁻¹ ^ N / (q⁻¹ ^ y))) := by
  obtain ⟨d, rfl⟩ : ∃ d, N = y + 1 + d := ⟨N - (y + 1), by omega⟩
  rw [show y + 1 + d - (y + 1) = d by omega, show y + 1 + d - y = d + 1 by omega]
  have hqy := qPochhammer_self_ne_zero hqn y
  have hqd := qPochhammer_self_ne_zero hqn d
  have hqy1 : 1 - q * q ^ y ≠ 0 := by
    have h := qPochhammer_self_ne_zero hqn (y + 1)
    rw [qPochhammer_succ] at h
    exact (mul_ne_zero_iff.mp h).2
  have hqd1 : 1 - q * q ^ d ≠ 0 := by
    have h := qPochhammer_self_ne_zero hqn (d + 1)
    rw [qPochhammer_succ] at h
    exact (mul_ne_zero_iff.mp h).2
  rw [qPochhammer_succ q q y, qPochhammer_succ q q d,
    qPochhammer_succ (a * q) q y, qPochhammer_succ (b * q) q d]
  simp only [inv_pow, pow_add, pow_succ]
  field_simp [ha, hq, hqy, hqd, hqy1, hqd1]
  ring

/-- The terminating denominator has no zero factors up to the lattice size. -/
private lemma qHahn_denominator_ne_zero {q : ℝ} (hq : 0 < q) (hq1 : q < 1) {N k : ℕ} (hk : k ≤ N) :
    qPochhammer ((q : ℂ)⁻¹ ^ N) q k ≠ 0 := by
  apply qOrth_qPochhammer_ne_zero
  intro j hj h
  have hr : (q⁻¹ ^ N) * q ^ j = 1 := by exact_mod_cast h
  have hp := congrArg (fun z : ℝ => q ^ N * z) hr
  simp only [inv_pow] at hp
  have hp' : q ^ j = q ^ N := by
    simpa [← mul_assoc, hq.ne'] using hp
  have he := (pow_right_injective₀ hq hq1.ne) hp'
  omega

/-- The q-Hahn eigenvalues are distinct throughout the positive orthogonality regime. -/
private lemma qHahn_eigenvalue_ne {a b q : ℝ} (hq : 0 < q) (hq1 : q < 1) (ha : 0 < a)
    (haq : a * q < 1) (hb : 0 < b) (hbq : b * q < 1) {m n : ℕ} (hmn : m ≠ n) :
    ((q : ℂ)⁻¹ ^ m - 1) * (1 - a * b * (q : ℂ) ^ (m + 1)) ≠
      ((q : ℂ)⁻¹ ^ n - 1) * (1 - a * b * (q : ℂ) ^ (n + 1)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hfac : ((q : ℂ)⁻¹ ^ m - 1) * (1 - a * b * (q : ℂ) ^ (m + 1)) -
      ((q : ℂ)⁻¹ ^ n - 1) * (1 - a * b * (q : ℂ) ^ (n + 1)) =
      (((q : ℂ) ^ n - q ^ m) * (1 - a * b * (q : ℂ) ^ (m + n + 1))) /
        ((q : ℂ) ^ m * q ^ n) := by
    simp only [inv_pow]
    field_simp
    ring
  intro h
  have hzero : ((q : ℂ) ^ n - q ^ m) * (1 - a * b * (q : ℂ) ^ (m + n + 1)) = 0 := by
    rw [h, sub_self, eq_comm, div_eq_zero_iff] at hfac
    exact hfac.resolve_right (mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ hq0))
  have hzero' : (q ^ n - q ^ m) * (1 - a * b * q ^ (m + n + 1)) = 0 := by
    exact_mod_cast hzero
  rcases mul_eq_zero.mp hzero' with hp | hp
  · exact hmn ((pow_right_injective₀ hq hq1.ne) (sub_eq_zero.mp hp)).symm
  · have habq : a * q * (b * q) < 1 := by
      calc _ < a * q * 1 := mul_lt_mul_of_pos_left hbq (mul_pos ha hq)
           _ < 1 := by simpa using haq
    have he : m + n + 1 = (m + n - 1) + 2 := by omega
    have hle : q ^ (m + n - 1) ≤ 1 := pow_le_one₀ hq.le hq1.le
    have hlt : a * b * q ^ (m + n + 1) < 1 := by
      calc _ = (a * q * (b * q)) * q ^ (m + n - 1) := by rw [he]; ring
           _ ≤ a * q * (b * q) * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
           _ < 1 := by simpa using habq
    linarith

/-- Formula under the stated hypotheses: `∑ y ∈ Finset.range (N + 1), qHahn a b q N m ((q : ℂ)⁻¹ ^
y) * qHahn a b q N n ((q : ℂ)⁻¹ ^ y) * qPochhammer q q N / (qPochhammer q q y * qPochhammer q
q (N - y)) * qPochhammer (a * q) q y * qPochhammer (b * q) q (N - y) / ((a * q : ℂ) ^ y) = 0`. -/
@[dlmf 18.27.E4]
theorem qHahn_orthogonal {a b q : ℝ} (hq : 0 < q) (hq1 : q < 1) (ha : 0 < a)
    (haq : a * q < 1) (hb : 0 < b) (hbq : b * q < 1) {N m n : ℕ}
    (hm : m ≤ N) (hn : n ≤ N) (hmn : m ≠ n) :
    ∑ y ∈ Finset.range (N + 1), qHahn a b q N m ((q : ℂ)⁻¹ ^ y) *
      qHahn a b q N n ((q : ℂ)⁻¹ ^ y) * qPochhammer q q N /
        (qPochhammer q q y * qPochhammer q q (N - y)) *
      qPochhammer (a * q) q y * qPochhammer (b * q) q (N - y) / ((a * q : ℂ) ^ y) = 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hqc : ‖(q : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  have haqc : ‖(a : ℂ) * q‖ < 1 := by
    rw [← ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos ha hq)]
    exact haq
  let t (x : ℂ) := Complex.exp (-x * Complex.log q)
  have ht0 : t 0 = 1 := by simp [t]
  have ht (x : ℂ) : t x ≠ 0 := Complex.exp_ne_zero _
  have htplus (x : ℂ) : t (x + 1) = t x / q := by
    simp only [t, show -(x + 1) * Complex.log q = -x * Complex.log q - Complex.log q by ring]
    rw [Complex.exp_sub, Complex.exp_log hq0]
  have htminus (x : ℂ) : t (x - 1) = q * t x := by
    simp only [t, show -(x - 1) * Complex.log q = Complex.log q + -x * Complex.log q by ring]
    rw [Complex.exp_add, Complex.exp_log hq0]
  have htnat (y : ℕ) : t y = (q : ℂ)⁻¹ ^ y := by
    induction y with
    | zero => simpa using ht0
    | succ y ih => rw [Nat.cast_succ, htplus, ih, pow_succ]; ring
  let w (y : ℕ) : ℂ := qPochhammer q q N / (qPochhammer q q y * qPochhammer q q (N - y)) *
      qPochhammer (a * q) q y * qPochhammer (b * q) q (N - y) / ((a * q : ℂ) ^ y)
  let B (x : ℂ) := (1 - a * q / t x) * (1 - (q : ℂ)⁻¹ ^ N / t x)
  let D (x : ℂ) := (a * q : ℂ) * (1 - 1 / t x) * (b - (q : ℂ)⁻¹ ^ N / (q * t x))
  let f (k : ℕ) (x : ℂ) := qHahn a b q N k (t x)
  have hD0 : D 0 = 0 := by simp [D, ht0]
  have hBN : B N = 0 := by simp [B, htnat, hq0]
  have hP (y : ℕ) (hy : y < N) : w (y + 1) * D ((y : ℂ) + 1) = w y * B y := by
    dsimp only [w, D, B]
    rw [← Nat.cast_succ, htnat, htnat]
    exact qHahn_weight_balance ha0 hq0 hqc hy
  have hE (k : ℕ) (hk : k ≤ N) (x : ℕ) (_hx : x ≤ N) :
      DiscreteOrtho.op B D (f k) x =
        ((q : ℂ)⁻¹ ^ k - 1) * (1 - a * b * (q : ℂ) ^ (k + 1)) * f k x := by
    dsimp only [DiscreteOrtho.op, B, D, f]
    rw [htplus, htminus]
    exact qHahn_difference_equation_aux hq0 hqc N k
      (fun j _ => qPochhammer_ne_zero_of_factors hqc
        (one_sub_mul_pow_ne_zero_of_norm haqc hqc) j)
      (fun j hj => qHahn_denominator_ne_zero hq hq1 (hj.trans hk)) (ht x)
  have h := DiscreteOrtho.sum_range_orthogonal N w B D (f m) (f n) hD0 hBN hP
    (hE m hm) (hE n hn) (qHahn_eigenvalue_ne hq hq1 ha haq hb hbq hmn)
  rw [← h]
  apply Finset.sum_congr rfl
  intro y _
  dsimp only [f, w]
  rw [htnat]
  ring

/-- The finite monomial expansion of the little q-Jacobi polynomial. -/
theorem littleQJacobi_eq_sum (a b q x : ℂ) (n : ℕ) :
    littleQJacobi a b q n x = ∑ j ∈ Finset.range (n + 1),
      (qPochhammer (q⁻¹ ^ n) q j * qPochhammer (a * b * q ^ (n + 1)) q j /
        (qPochhammer (a * q) q j * qPochhammer q q j) * q ^ j) * x ^ j := by
  unfold littleQJacobi terminatingBasicHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.length_cons,
    List.length_nil, mul_one]
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_zero,
    show (1 + (1 : ℤ) - 2) = 0 by norm_num, zpow_zero, mul_one]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

/-- A little q-Jacobi polynomial has zero weighted moments below its degree. -/
theorem littleQJacobi_moment_hasSum {a b q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (ha0 : a ≠ 0) (haq : ‖a * q‖ < 1)
    (hab : ∀ p : ℕ, a * b * q ^ (p + 2) ≠ 1)
    (ha1 : ∀ p : ℕ, a * q ^ (p + 1) ≠ 1) {i n : ℕ} (hin : i < n) :
    HasSum (fun y : ℕ => (q ^ y) ^ i * littleQJacobi a b q n (q ^ y) *
      (qPochhammer (b * q) q y * (a * q) ^ y / qPochhammer q q y)) 0 := by
  let c (j : ℕ) := qPochhammer (q⁻¹ ^ n) q j *
    qPochhammer (a * b * q ^ (n + 1)) q j /
      (qPochhammer (a * q) q j * qPochhammer q q j) * q ^ j
  have hs := hasSum_sum (s := Finset.range (n + 1)) (fun j _ =>
    (qOrth_littleQJacobi_moment (b := b) hq haq (i + j)).mul_left (c j))
  have hz := qOrth_littleQJacobi_sum_zero hq hq0 ha0 haq hab ha1 hin
  change ∑ j ∈ Finset.range (n + 1), c j * _ = 0 at hz
  rw [hz] at hs
  convert hs using 1
  funext y
  rw [littleQJacobi_eq_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [c]
  rw [pow_add, mul_pow]
  simp only [← pow_mul]
  ring

/-- Orthogonality of little q-Jacobi polynomials of strictly ordered degrees. -/
theorem littleQJacobi_orthogonal_lt {a b q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (ha0 : a ≠ 0) (haq : ‖a * q‖ < 1)
    (hab : ∀ p : ℕ, a * b * q ^ (p + 2) ≠ 1)
    (ha1 : ∀ p : ℕ, a * q ^ (p + 1) ≠ 1) {m n : ℕ} (hmn : m < n) :
    HasSum (fun y : ℕ => littleQJacobi a b q m (q ^ y) * littleQJacobi a b q n (q ^ y) *
      qPochhammer (b * q) q y * (a * q) ^ y / qPochhammer q q y) 0 := by
  let c (j : ℕ) := qPochhammer (q⁻¹ ^ m) q j *
    qPochhammer (a * b * q ^ (m + 1)) q j /
      (qPochhammer (a * q) q j * qPochhammer q q j) * q ^ j
  have hs := hasSum_sum (s := Finset.range (m + 1)) (fun j hj =>
    (littleQJacobi_moment_hasSum hq hq0 ha0 haq hab ha1
      (show j < n by have := Finset.mem_range.mp hj; omega)).mul_left (c j))
  simp only [mul_zero, Finset.sum_const_zero] at hs
  convert hs using 1
  funext y
  rw [littleQJacobi_eq_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [c]
  ring

/-- The series with terms `(fun y : ℕ => littleQJacobi a b q m ((q : ℂ) ^ y) * littleQJacobi a b q
n ((q : ℂ) ^ y) * qPochhammer (b * q) q y * ((a * q : ℂ) ^ y) / qPochhammer q q y)` converges
to `0`. -/
@[dlmf 18.27.E14]
theorem littleQJacobi_orthogonal {a b q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (ha : 0 < a) (haq : a * q < 1) (hb : b * q < 1) {m n : ℕ} (hmn : m ≠ n) :
    HasSum (fun y : ℕ => littleQJacobi a b q m ((q : ℂ) ^ y) *
      littleQJacobi a b q n ((q : ℂ) ^ y) * qPochhammer (b * q) q y *
      ((a * q : ℂ) ^ y) / qPochhammer q q y) 0 := by
  have hqc : ‖(q : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have haqc : ‖(a : ℂ) * q‖ < 1 := by
    rw [← ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos ha hq)]
    exact haq
  have ha1 : ∀ p : ℕ, (a : ℂ) * q ^ (p + 1) ≠ 1 := by
    intro p hp
    have h := norm_mul_pow_lt_one haqc hqc p
    have e : (a : ℂ) * q ^ (p + 1) = (a * q) * q ^ p := by ring
    rw [← e, hp, norm_one] at h
    exact lt_irrefl _ h
  have hab : ∀ p : ℕ, (a : ℂ) * b * q ^ (p + 2) ≠ 1 := by
    intro p hp
    have he : a * b * q ^ (p + 2) = 1 := by exact_mod_cast hp
    have hpow : 0 < q ^ p := pow_pos hq p
    have hle : q ^ p ≤ 1 := pow_le_one₀ hq.le hq1.le
    have he' : (a * q) * (b * q) * q ^ p = 1 := by
      calc _ = a * b * q ^ (p + 2) := by ring
           _ = 1 := he
    have habq : a * q * (b * q) < 1 := by
      calc a * q * (b * q) < a * q * 1 := mul_lt_mul_of_pos_left hb (mul_pos ha hq)
           _ < 1 := by simpa using haq
    have : a * q * (b * q) * q ^ p < 1 := by
      calc a * q * (b * q) * q ^ p < 1 * q ^ p := mul_lt_mul_of_pos_right habq hpow
           _ ≤ 1 := by simpa using hle
    linarith
  rcases lt_or_gt_of_ne hmn with h | h
  · exact littleQJacobi_orthogonal_lt hqc hq0 ha0 haqc hab ha1 h
  · have hs := littleQJacobi_orthogonal_lt hqc hq0 ha0 haqc hab ha1 h
    convert hs using 1
    funext y
    ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in Set.Ioi 0, qLaguerre α
q m x * qLaguerre α q n x * (Real.rpow x α : ℂ) / qPochhammerInf (-x) q = 0`. -/
@[dlmf 18.27.E16]
theorem qLaguerre_orthogonal {α q : ℝ} (hα : -1 < α) (hq : 0 < q) (hq1 : q < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x : ℝ in Set.Ioi 0, qLaguerre α q m x * qLaguerre α q n x *
      (Real.rpow x α : ℂ) / qPochhammerInf (-x) q = 0 := by
  sorry

/-- A triangular-number identity for the exponents of the lognormal moments. -/
private lemma twice_choose_two_add (k : ℕ) : 2 * k.choose 2 + k = k ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

open TauCeti.Probability in
/-- Gaussian-in-logarithm moments, obtained from TauCeti’s lognormal density and moments. -/
private lemma logGaussian_moment {s : ℝ} (hs : 0 < s) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(Real.log x) ^ 2 / (2 * s))) (Set.Ioi 0) ∧
    ∫ x : ℝ in Set.Ioi 0, x ^ k * Real.exp (-(Real.log x) ^ 2 / (2 * s)) =
      Real.sqrt (2 * Real.pi * s) * Real.exp ((k + 1 : ℝ) ^ 2 * s / 2) := by
  let v : ℝ≥0 := ⟨s, hs.le⟩
  have hv : v ≠ 0 := by intro h; have := congrArg (fun t : ℝ≥0 => (t : ℝ)) h; exact hs.ne' this
  have hC : Real.sqrt (2 * Real.pi * s) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have htop (x : ℝ) : logNormalPDF 0 v x < ∞ := by
    rcases le_or_gt x 0 with hx | hx
    · rw [logNormalPDF_of_nonpos hx]
      exact ENNReal.zero_lt_top
    · rw [logNormalPDF_of_pos hx]
      exact ENNReal.ofReal_lt_top
  have hint := integrable_pow_logNormalMeasure 0 v (k + 1)
  rw [logNormalMeasure_eq_withDensity 0 hv,
    integrable_withDensity_iff (measurable_logNormalPDF 0 v)
      (Filter.Eventually.of_forall htop)] at hint
  simp only [toReal_logNormalPDF] at hint
  have hI := integral_pow_logNormalMeasure 0 v (k + 1)
  rw [logNormalMeasure_eq_withDensity 0 hv,
    integral_withDensity_eq_integral_toReal_smul (measurable_logNormalPDF 0 v)
      (Filter.Eventually.of_forall htop)] at hI
  simp only [smul_eq_mul] at hI
  simp only [toReal_logNormalPDF] at hI
  change (∫ x : ℝ, logNormalPDFReal 0 v x * x ^ (k + 1)) =
    Real.exp (((k + 1 : ℕ) : ℝ) * 0 + (((k + 1 : ℕ) : ℝ)) ^ 2 * s / 2) at hI
  simp only [Nat.cast_add, Nat.cast_one, mul_zero, zero_add] at hI
  have he : (Set.Ioi (0 : ℝ)).indicator
      (fun x => x ^ k * Real.exp (-(Real.log x) ^ 2 / (2 * s))) =
      fun x => Real.sqrt (2 * Real.pi * s) * (x ^ (k + 1) * logNormalPDFReal 0 v x) := by
    funext x
    by_cases hx : 0 < x
    · rw [Set.indicator_of_mem hx, logNormalPDFReal_of_pos hx]
      change x ^ k * Real.exp (-(Real.log x) ^ 2 / (2 * s)) =
        Real.sqrt (2 * Real.pi * s) * (x ^ (k + 1) *
          ((x * Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(Real.log x - 0) ^ 2 / (2 * s))))
      simp only [sub_zero, pow_succ]
      field_simp
    · rw [Set.indicator_of_notMem hx, logNormalPDFReal_of_nonpos (le_of_not_gt hx)]
      simp
  constructor
  · rw [← integrable_indicator_iff measurableSet_Ioi, he]
    exact hint.const_mul _
  · rw [← integral_indicator measurableSet_Ioi, he, integral_const_mul]
    rw [show (fun x => x ^ (k + 1) * logNormalPDFReal 0 v x) =
      (fun x => logNormalPDFReal 0 v x * x ^ (k + 1)) by ext; ring]
    rw [hI]

/-- The scaled monomial moments of the Stieltjes–Wigert weight are reciprocal triangular powers of `q`. -/
theorem stieltjesWigert_scaled_moment_real {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (k : ℕ) :
    IntegrableOn (fun x : ℝ => (Real.sqrt q * x) ^ k *
      Real.exp (-(Real.log x) ^ 2 / (2 * Real.log q⁻¹))) (Set.Ioi 0) ∧
    ∫ x : ℝ in Set.Ioi 0, (Real.sqrt q * x) ^ k *
      Real.exp (-(Real.log x) ^ 2 / (2 * Real.log q⁻¹)) =
      (Real.sqrt (2 * Real.pi * (-Real.log q)) * Real.exp (-Real.log q / 2)) /
        q ^ (k + 1).choose 2 := by
  have hs : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  obtain ⟨hint, hI⟩ := logGaussian_moment hs k
  have he : (fun x : ℝ => (Real.sqrt q * x) ^ k *
      Real.exp (-(Real.log x) ^ 2 / (2 * Real.log q⁻¹))) =
      fun x => Real.sqrt q ^ k * (x ^ k * Real.exp (-(Real.log x) ^ 2 / (2 * -Real.log q))) := by
    funext x
    rw [Real.log_inv, mul_pow]
    ring
  rw [he]
  refine ⟨hint.const_mul _, ?_⟩
  rw [integral_const_mul, hI]
  have heq : Real.sqrt q ^ k * Real.exp ((k + 1 : ℝ) ^ 2 * (-Real.log q) / 2) =
      Real.exp (-Real.log q / 2) / q ^ (k + 1).choose 2 := by
    rw [← Real.exp_log hq, ← Real.exp_half, ← Real.exp_nat_mul,
      ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add]
    simp only [Real.log_exp]
    congr 1
    have hc : (2 : ℝ) * ((k + 1).choose 2 : ℝ) + (k + 1) = (k + 1) ^ 2 := by
      exact_mod_cast twice_choose_two_add (k + 1)
    linear_combination Real.log q / 2 * hc
  calc _ = Real.sqrt (2 * Real.pi * -Real.log q) *
      (Real.sqrt q ^ k * Real.exp ((k + 1 : ℝ) ^ 2 * (-Real.log q) / 2)) := by ring
       _ = _ := by rw [heq]; ring

/-- Cauchy’s finite q-binomial theorem cancels every moment below the polynomial’s degree. -/
theorem stieltjesWigert_moment_sum {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    {i n : ℕ} (hin : i < n) :
    ∑ k ∈ Finset.range (n + 1), q ^ (k ^ 2) * (-1) ^ k /
      (qPochhammer q q k * qPochhammer q q (n - k)) / q ^ (i + k + 1).choose 2 = 0 := by
  have he (k : ℕ) : k ^ 2 + (i + 1).choose 2 + i * k =
      k.choose 2 + (i + k + 1).choose 2 := by
    have h1 := twice_choose_two_add k
    have h2 := twice_choose_two_add (i + 1)
    have h3 := twice_choose_two_add (i + k + 1)
    nlinarith
  have hz : qPochhammer (q⁻¹ ^ i) q n = 0 :=
    qOrth_qPochhammer_eq_zero hin (by simp [inv_pow, hq0])
  rw [← zero_div (qPochhammer q q n * q ^ (i + 1).choose 2), ← hz,
    qPochhammer_eq_sum_qBinom, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using Finset.mem_range.mp hk
  have hB := qBinom_mul_qPochhammer q k (n - k)
  rw [Nat.add_sub_cancel' hkn] at hB
  have h1 := qPochhammer_self_ne_zero hq k
  have h2 := qPochhammer_self_ne_zero hq (n - k)
  have h3 := qPochhammer_self_ne_zero hq n
  rw [inv_pow, inv_pow, ← pow_mul]
  have hp : q ^ (k ^ 2) * q ^ (i + 1).choose 2 * q ^ (i * k) =
      q ^ k.choose 2 * q ^ (i + k + 1).choose 2 := by
    simp only [← pow_add]
    rw [he]
  field_simp
  rw [← hB]
  linear_combination (qBinom q n k * qPochhammer q q k * qPochhammer q q (n - k)) * hp

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in Set.Ioi 0,
stieltjesWigert q m (Real.sqrt q * x) * stieltjesWigert q n (Real.sqrt q * x) * Real.exp
(-(Real.log x) ^ 2 / (2 * Real.log q⁻¹)) = 0`. -/
@[dlmf 18.27.E20]
theorem stieltjesWigert_orthogonal {q : ℝ} (hq : 0 < q) (hq1 : q < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x : ℝ in Set.Ioi 0, stieltjesWigert q m (Real.sqrt q * x) *
      stieltjesWigert q n (Real.sqrt q * x) *
      Real.exp (-(Real.log x) ^ 2 / (2 * Real.log q⁻¹)) = 0 := by
  let u (x : ℝ) : ℂ := Real.sqrt q * x
  let w (x : ℝ) : ℂ := Real.exp (-(Real.log x) ^ 2 / (2 * Real.log q⁻¹))
  let K : ℂ := Real.sqrt (2 * Real.pi * (-Real.log q)) * Real.exp (-Real.log q / 2)
  let c (n k : ℕ) : ℂ := (q : ℂ) ^ (k ^ 2) * (-1) ^ k /
    (qPochhammer q q k * qPochhammer q q (n - k))
  have hpoly (d : ℕ) (x : ℂ) :
      stieltjesWigert q d x = ∑ k ∈ Finset.range (d + 1), c d k * x ^ k := by
    unfold stieltjesWigert
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [c]
    rw [neg_pow]
    ring
  have hi (k : ℕ) : IntegrableOn (fun x => u x ^ k * w x) (Set.Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => (((Real.sqrt q * x) ^ k *
        Real.exp (-(Real.log x) ^ 2 / (2 * Real.log q⁻¹)) : ℝ) : ℂ)) (Set.Ioi 0) :=
      (stieltjesWigert_scaled_moment_real hq hq1 k).1.ofReal
    simpa only [u, w, ofReal_mul, ofReal_pow] using h
  have hI (k : ℕ) : (∫ x : ℝ in Set.Ioi 0, u x ^ k * w x) =
      K / (q : ℂ) ^ (k + 1).choose 2 := by
    have h := congrArg Complex.ofReal (stieltjesWigert_scaled_moment_real hq hq1 k).2
    rw [← integral_complex_ofReal] at h
    simpa only [u, w, K, ofReal_mul, ofReal_div, ofReal_pow] using h
  have hqc : ‖(q : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hterm (i d k : ℕ) : IntegrableOn (fun x => c d k * (u x ^ (i + k) * w x)) (Set.Ioi 0) :=
    (hi (i + k)).const_mul _
  have hsum (i d : ℕ) : (fun x => u x ^ i * stieltjesWigert q d (u x) * w x) =
      fun x => ∑ k ∈ Finset.range (d + 1), c d k * (u x ^ (i + k) * w x) := by
    funext x
    rw [hpoly, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add]
    ring
  have hiP (i d : ℕ) : IntegrableOn (fun x => u x ^ i * stieltjesWigert q d (u x) * w x)
      (Set.Ioi 0) := by
    rw [hsum]
    exact integrable_finsetSum _ (fun k _ => hterm i d k)
  have hIP {i d : ℕ} (hid : i < d) :
      (∫ x : ℝ in Set.Ioi 0, u x ^ i * stieltjesWigert q d (u x) * w x) = 0 := by
    rw [hsum, integral_finsetSum _ (fun k _ => hterm i d k)]
    simp_rw [integral_const_mul, hI]
    have hz := stieltjesWigert_moment_sum hqc hq0 hid
    rw [← mul_zero K, ← hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [c]
    ring
  have hlt {a b : ℕ} (hab : a < b) :
      (∫ x : ℝ in Set.Ioi 0, stieltjesWigert q a (u x) * stieltjesWigert q b (u x) * w x) = 0 := by
    have he : (fun x => stieltjesWigert q a (u x) * stieltjesWigert q b (u x) * w x) =
        fun x => ∑ k ∈ Finset.range (a + 1), c a k * (u x ^ k * stieltjesWigert q b (u x) * w x) := by
      funext x
      rw [hpoly, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [he, integral_finsetSum _ (fun k _ => (hiP k b).const_mul (c a k))]
    apply Finset.sum_eq_zero
    intro k hk
    rw [integral_const_mul, hIP (show k < b by have := Finset.mem_range.mp hk; omega), mul_zero]
  change (∫ x : ℝ in Set.Ioi 0, stieltjesWigert q m (u x) * stieltjesWigert q n (u x) * w x) = 0
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hlt h
  · rw [← hlt h]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring

/-- Split a finite q-Pochhammer product at an intermediate index. -/
theorem qPochhammer_split (w q : ℂ) {n k : ℕ} (hk : k ≤ n) :
    qPochhammer w q n = qPochhammer w q k * qPochhammer (w * q ^ k) q (n - k) := by
  conv_lhs => rw [← Nat.add_sub_cancel' hk]
  simp only [qPochhammer_eq_prod, Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- Factor the Askey–Wilson quadratic kernel in a nonzero Laurent variable. -/
theorem askeyWilson_laurent_kernel (a q : ℂ) {z : ℂ} (hz : z ≠ 0) (k : ℕ) :
    (∏ j ∈ Finset.range k, (1 - 2 * a * q ^ j * ((z + z⁻¹) / 2) + a ^ 2 * q ^ (2 * j))) =
      qPochhammer (a * z) q k * qPochhammer (a / z) q k := by
  rw [qPochhammer_eq_prod, qPochhammer_eq_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [pow_mul]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `askeyWilson a b c d q n ((z +
z⁻¹) / 2) = a⁻¹ ^ n * qPochhammer (a * b) q n * qPochhammer (a * c) q n * qPochhammer (a * d)
q n * askeyWilsonLaurent a b c d q n z`. -/
@[dlmf 18.28.E1_5]
theorem askeyWilson_laurent_representation {a b c d q : ℂ} (ha : a ≠ 0) (hq : q ≠ 0)
    (hq1 : ‖q‖ < 1) (hab : ‖a * b‖ < 1) (hac : ‖a * c‖ < 1) (had : ‖a * d‖ < 1) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    askeyWilson a b c d q n ((z + z⁻¹) / 2) = a⁻¹ ^ n * qPochhammer (a * b) q n *
      qPochhammer (a * c) q n * qPochhammer (a * d) q n * askeyWilsonLaurent a b c d q n z := by
  have hne {w : ℂ} (hw : ‖w‖ < 1) (k : ℕ) : qPochhammer w q k ≠ 0 :=
    qPochhammer_ne_zero_of_factors hq1 (one_sub_mul_pow_ne_zero_of_norm hw hq1) k
  have hsplit {w : ℂ} (hw : ‖w‖ < 1) {k : ℕ} (hk : k ≤ n) :
      qPochhammer (w * q ^ k) q (n - k) = qPochhammer w q n / qPochhammer w q k := by
    rw [qPochhammer_split w q hk, mul_div_cancel_left₀ _ (hne hw k)]
  unfold askeyWilson askeyWilsonLaurent terminatingBasicHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.length_cons,
    List.length_nil, mul_one]
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, show (1 + (3 : ℤ) - 4) = 0 by norm_num,
    zpow_zero, mul_one]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using Finset.mem_range.mp hk
  rw [askeyWilson_laurent_kernel a q hz k, hsplit hab hkn, hsplit hac hkn, hsplit had hkn]
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ θ : ℝ in (0 : ℝ)..Real.pi,
askeyWilson a b c d q m (Real.cos θ) * askeyWilson a b c d q n (Real.cos θ) * (‖qPochhammerInf
(exp (2 * I * θ)) q / (qPochhammerInf (a * exp (I * θ)) q * qPochhammerInf (b * exp (I * θ)) q
* qPochhammerInf (c * exp (I * θ)) q * qPochhammerInf (d * exp (I * θ)) q)‖ ^ 2 : ℝ) = 0`. -/
@[dlmf 18.28.E2]
theorem askeyWilson_orthogonal {a b c d q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (ha0 : a ≠ 0) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) (hd : |d| < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ : ℝ in (0 : ℝ)..Real.pi, askeyWilson a b c d q m (Real.cos θ) *
      askeyWilson a b c d q n (Real.cos θ) *
      (‖qPochhammerInf (exp (2 * I * θ)) q /
        (qPochhammerInf (a * exp (I * θ)) q * qPochhammerInf (b * exp (I * θ)) q *
         qPochhammerInf (c * exp (I * θ)) q * qPochhammerInf (d * exp (I * θ)) q)‖ ^ 2 : ℝ) = 0 := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `∫ θ : ℝ in (0 : ℝ)..Real.pi,
qGegenbauer β q m (exp (I * θ)) * qGegenbauer β q n (exp (I * θ)) * (‖qPochhammerInf (exp (2 *
I * θ)) q / qPochhammerInf (β * exp (2 * I * θ)) q‖ ^ 2 : ℝ) = 0`. -/
@[dlmf 18.28.E15]
theorem qGegenbauer_orthogonal {β q : ℝ} (hq : 0 < q) (hq1 : q < 1) (hβ : |β| < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ : ℝ in (0 : ℝ)..Real.pi, qGegenbauer β q m (exp (I * θ)) * qGegenbauer β q n (exp (I * θ)) *
      (‖qPochhammerInf (exp (2 * I * θ)) q / qPochhammerInf (β * exp (2 * I * θ)) q‖ ^ 2 : ℝ) = 0 := by
  sorry

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
  sorry

/-- The factor with index `m` makes `(q⁻ᵐ;q)_k` vanish for `m < k`. -/
theorem qPochhammer_recip_pow_eq_zero {q : ℂ} (hq : q ≠ 0) {m k : ℕ} (hmk : m < k) :
    qPochhammer (q⁻¹ ^ m) q k = 0 := by
  rw [inv_pow]; exact DLMF.QSeries.qPochhammer_recip_pow_eq_zero hq hmk

/-- Factoring the quadratic kernel on the q-Racah lattice. -/
theorem qRacah_lattice_kernel {q : ℂ} (hq : q ≠ 0) (c d : ℂ) (y k : ℕ) :
    (∏ j ∈ Finset.range k,
      (1 - q ^ j * (q⁻¹ ^ y + c * d * q ^ (y + 1)) + c * d * q ^ (2 * j + 1))) =
      qPochhammer (q⁻¹ ^ y) q k * qPochhammer (c * d * q ^ (y + 1)) q k := by
  rw [qPochhammer_eq_prod, qPochhammer_eq_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hqpow : q⁻¹ ^ y * q ^ (y + 1) = q := by
    rw [pow_succ, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
  rw [show q ^ (2 * j + 1) = q ^ j * q ^ j * q by rw [pow_add, pow_mul]; ring]
  linear_combination -c * d * q ^ j * q ^ j * hqpow

/-- The terminating q-Racah sum may be padded to any larger degree. -/
theorem qRacah_eq_sum_lattice {q : ℂ} (hq : q ≠ 0) (a b c d : ℂ)
    (n y N : ℕ) (hn : n ≤ N) :
    qRacah a b c d q n (q⁻¹ ^ y + c * d * q ^ (y + 1)) =
      ∑ k ∈ Finset.range (N + 1),
        q ^ k * qPochhammer (q⁻¹ ^ n) q k * qPochhammer (a * b * q ^ (n + 1)) q k /
          (qPochhammer (a * q) q k * qPochhammer (b * d * q) q k *
            qPochhammer (c * q) q k * qPochhammer q q k) *
          (qPochhammer (q⁻¹ ^ y) q k * qPochhammer (c * d * q ^ (y + 1)) q k) := by
  unfold qRacah
  simp_rw [qRacah_lattice_kernel hq]
  apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
  intro k hk hkn
  have hnk : n < k := by simp only [Finset.mem_range] at hkn; omega
  rw [qPochhammer_recip_pow_eq_zero hq hnk]
  simp

/-- Identity under the stated parameter and domain assumptions: `qRacah a b c d q n (q⁻¹ ^ y + c *
d * q ^ (y + 1)) = qRacah c d a b q y (q⁻¹ ^ n + a * b * q ^ (n + 1))`. -/
@[dlmf 18.28.E23]
theorem qRacah_duality {a b c d q : ℂ} (hq : q ≠ 0) (hq1 : ‖q‖ < 1) (n y : ℕ) :
    qRacah a b c d q n (q⁻¹ ^ y + c * d * q ^ (y + 1)) =
      qRacah c d a b q y (q⁻¹ ^ n + a * b * q ^ (n + 1)) := by
  rw [qRacah_eq_sum_lattice hq a b c d n y (max n y) (le_max_left _ _),
    qRacah_eq_sum_lattice hq c d a b y n (max n y) (le_max_right _ _)]
  apply Finset.sum_congr rfl
  intro k _
  rw [show d * b * q = b * d * q by ring]
  ring

end DLMF.OrthogonalPolynomials
end
end
