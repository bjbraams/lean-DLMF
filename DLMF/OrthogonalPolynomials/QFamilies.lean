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
# The q-Hahn and Askey–Wilson classes

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
The `q`-Gegenbauer limit follows termwise from the finite `q`-Pochhammer ratio limits
and the proved coefficients of the Gegenbauer generating series.
The Askey–Wilson difference equation follows by triangular action on the paired
q-Pochhammer basis and a finite telescoping sum, retaining all stated parameters.
The q-Hahn proof reuses the finite summation-by-parts operator `DiscreteOrtho.sum_range_orthogonal` from `Hahn.lean`.
Little q-Jacobi orthogonality reuses the moment cancellations in `QOrthogonalityTools`.
Stieltjes–Wigert orthogonality uses the proved density and moment theorems from
`TauCeti.Probability.Distributions.LogNormal.Basic`, followed by Cauchy’s finite q-binomial theorem.
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

@[dlmf 18.27.E3]
def qHahn (a b q : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1), x] [a * q, q⁻¹ ^ N] q q

@[dlmf 18.27.E5]
def bigQJacobi (a b c q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1), x] [a * q, c * q] q q

@[dlmf 18.27.E13]
def littleQJacobi (a b q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1)] [a * q] q (q * x)

@[dlmf 18.27.E14_5]
def littleQLaguerre (a q : ℂ) (n : ℕ) (x : ℂ) : ℂ := littleQJacobi a 0 q n x

@[dlmf 18.27.E15]
def qLaguerre (α q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  qPochhammer (q ^ (α + 1)) q n / qPochhammer q q n *
    terminatingBasicHG n [q⁻¹ ^ n] [q ^ (α + 1)] q (-x * q ^ (n + α + 1))

@[dlmf 18.27.E18]
def stieltjesWigert (q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), q ^ (k ^ 2) * (-x) ^ k /
    (qPochhammer q q k * qPochhammer q q (n - k))

@[dlmf 18.27.E21]
def discreteQHermiteI (q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  qPochhammer q q n * ∑ k ∈ Finset.range (n / 2 + 1),
    (-1 : ℂ) ^ k * q ^ (k * (k - 1)) * x ^ (n - 2 * k) /
      (qPochhammer (q ^ 2) (q ^ 2) k * qPochhammer q q (n - 2 * k))

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

@[dlmf 18.28.E1_5]
def askeyWilsonLaurent (a b c d q : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * c * d * q ^ ((n : ℤ) - 1), a * z, a / z]
    [a * b, a * c, a * d] q q

@[dlmf 18.28.E7]
def alSalamChihara (a b q : ℂ) (n : ℕ) (x : ℂ) : ℂ := askeyWilson a b 0 0 q n x

/-- Laurent argument `z`, representing the polynomial argument `(z + z⁻¹)/2`. -/
@[dlmf 18.28.E16]
def continuousQHermiteLaurent (q : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  qPochhammer q q n * qGegenbauer 0 q n z

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

@[dlmf 18.28.E2]
theorem askeyWilson_orthogonal {a b c d q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (ha0 : a ≠ 0) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) (hd : |d| < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ : ℝ in (0 : ℝ)..Real.pi, askeyWilson a b c d q m (Real.cos θ) *
      askeyWilson a b c d q n (Real.cos θ) *
      (‖qPochhammerInf (exp (2 * I * θ)) q /
        (qPochhammerInf (a * exp (I * θ)) q * qPochhammerInf (b * exp (I * θ)) q *
         qPochhammerInf (c * exp (I * θ)) q * qPochhammerInf (d * exp (I * θ)) q)‖ ^ 2 : ℝ) = 0 := by
  sorry

@[dlmf 18.28.E15]
theorem qGegenbauer_orthogonal {β q : ℝ} (hq : 0 < q) (hq1 : q < 1) (hβ : |β| < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ : ℝ in (0 : ℝ)..Real.pi, qGegenbauer β q m (exp (I * θ)) * qGegenbauer β q n (exp (I * θ)) *
      (‖qPochhammerInf (exp (2 * I * θ)) q / qPochhammerInf (β * exp (2 * I * θ)) q‖ ^ 2 : ℝ) = 0 := by
  sorry

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
  rw [qPochhammer_eq_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hmk)
  simp [inv_pow, pow_ne_zero _ hq]

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

/-- `(1 - q^t)/(1 - q) → t` as `q → 1⁻`. -/
theorem tendsto_one_sub_rpow_div (t : ℝ) :
    Tendsto (fun q : ℝ => (1 - q ^ t) / (1 - q)) (𝓝[<] 1) (𝓝 t) := by
  have hd : HasDerivAt (fun q : ℝ => q ^ t) t 1 := by
    simpa using Real.hasDerivAt_rpow_const (x := 1) (p := t) (Or.inl one_ne_zero)
  have hs := hd.tendsto_slope.mono_left
    (nhdsWithin_mono (s := Set.Iio (1 : ℝ)) _ (fun q (hq : q < 1) => hq.ne))
  refine hs.congr' (eventually_nhdsWithin_of_forall fun q (hq : q < 1) => ?_)
  rw [slope_def_field, Real.one_rpow]
  have : q - 1 ≠ 0 := sub_ne_zero.mpr hq.ne
  have : 1 - q ≠ 0 := sub_ne_zero.mpr hq.ne'
  field_simp
  ring

theorem eventually_pos_nhdsWithin_lt_one : ∀ᶠ q : ℝ in 𝓝[<] 1, 0 < q :=
  nhdsWithin_le_nhds (lt_mem_nhds one_pos)

/-- `(q^t;q)_k / (1-q)^k → (t)_k` as `q → 1⁻`. -/
theorem tendsto_qPochhammer_rpow_div (t : ℝ) (k : ℕ) :
    Tendsto (fun q : ℝ => qPochhammer ((q ^ t : ℝ) : ℂ) (q : ℂ) k / (1 - (q : ℂ)) ^ k)
      (𝓝[<] 1) (𝓝 (poch (t : ℂ) k)) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have hf : Tendsto (fun q : ℝ => (((1 - q ^ (t + k)) / (1 - q) : ℝ) : ℂ)) (𝓝[<] 1)
        (𝓝 ((t + k : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto _).comp (tendsto_one_sub_rpow_div (t + k))
    rw [poch_succ]
    refine ((ih.mul hf).congr' ?_).trans (by push_cast; rfl)
    filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
    have h1 : (1 : ℂ) - q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hq1))
    rw [qPochhammer_succ, pow_succ]
    have hrp : ((q ^ t : ℝ) : ℂ) * (q : ℂ) ^ k = ((q ^ (t + k) : ℝ) : ℂ) := by
      rw [Real.rpow_add hq, Real.rpow_natCast]; push_cast; ring
    rw [hrp]
    push_cast
    field_simp

lemma ofReal_rpow_eq_cpow_aux {q : ℝ} (hq : 0 < q) (a b : ℝ) :
    ((q ^ a : ℝ) : ℂ) * ((q ^ b : ℝ) : ℂ) = ((q ^ (a + b) : ℝ) : ℂ) := by
  rw [Real.rpow_add hq]; push_cast; ring

theorem ofReal_pow_eq_rpow {q : ℝ} (m : ℕ) : (q : ℂ) ^ m = ((q ^ (m : ℝ) : ℝ) : ℂ) := by
  rw [Real.rpow_natCast]; push_cast; ring

theorem ofReal_recip_pow_eq_rpow {q : ℝ} (hq : 0 < q) (m : ℕ) :
    (q : ℂ)⁻¹ ^ m = ((q ^ (-(m : ℝ)) : ℝ) : ℂ) := by
  rw [Real.rpow_neg hq.le, Real.rpow_natCast]; push_cast; ring

/-- The ratio limit for the four `q`-Pochhammer symbols of a `₂φ₁`-type term. -/
theorem tendsto_qPoch_two_two (t₁ t₂ s₁ s₂ : ℝ) (k : ℕ) (hs₁ : poch (s₁ : ℂ) k ≠ 0)
    (hs₂ : poch (s₂ : ℂ) k ≠ 0) :
    Tendsto (fun q : ℝ => qPochhammer ((q ^ t₁ : ℝ) : ℂ) (q : ℂ) k *
        qPochhammer ((q ^ t₂ : ℝ) : ℂ) (q : ℂ) k /
        (qPochhammer ((q ^ s₁ : ℝ) : ℂ) (q : ℂ) k * qPochhammer ((q ^ s₂ : ℝ) : ℂ) (q : ℂ) k))
      (𝓝[<] 1) (𝓝 (poch (t₁ : ℂ) k * poch (t₂ : ℂ) k / (poch (s₁ : ℂ) k * poch (s₂ : ℂ) k))) := by
  have h := ((tendsto_qPochhammer_rpow_div t₁ k).mul (tendsto_qPochhammer_rpow_div t₂ k)).div
    ((tendsto_qPochhammer_rpow_div s₁ k).mul (tendsto_qPochhammer_rpow_div s₂ k))
    (mul_ne_zero hs₁ hs₂)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq1
  have h1 : ((1 : ℂ) - q) ^ k ≠ 0 := pow_ne_zero _ (by
    rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hq1)))
  simp only [Pi.div_apply]
  field_simp

theorem tendsto_ofReal_nhdsWithin_lt_one :
    Tendsto (fun q : ℝ => (q : ℂ)) (𝓝[<] 1) (𝓝 1) := by
  simpa using (continuous_ofReal.tendsto (1 : ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))

theorem one_sub_ofReal_pow_ne_zero {q : ℝ} (hq1 : q < 1) (k : ℕ) : ((1 : ℂ) - q) ^ k ≠ 0 :=
  pow_ne_zero _ (by
    rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hq1)))

theorem ofReal_cpow_add_one {q : ℝ} (hq : 0 < q) (α : ℝ) :
    (q : ℂ) ^ ((α : ℂ) + 1) = ((q ^ (α + 1) : ℝ) : ℂ) := by
  rw [ofReal_cpow hq.le]; push_cast; ring_nf

theorem tendsto_rpow_nhdsWithin_lt_one (t : ℝ) :
    Tendsto (fun q : ℝ => ((q ^ t : ℝ) : ℂ)) (𝓝[<] 1) (𝓝 1) := by
  have h : Tendsto (fun q : ℝ => q ^ t) (𝓝 1) (𝓝 ((1 : ℝ) ^ t)) :=
    (Real.continuousAt_rpow_const 1 t (Or.inl one_ne_zero)).tendsto
  rw [Real.one_rpow] at h
  have h2 := (continuous_ofReal.tendsto 1).comp (h.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1)))
  rw [ofReal_one] at h2
  exact h2

/-- The quadratic Askey–Wilson factor tends to the Wilson factor. -/
theorem tendsto_askeyWilson_prod (a : ℝ) (x : ℂ) (k : ℕ) :
    Tendsto (fun q : ℝ => (∏ j ∈ Finset.range k, (1 - 2 * ((q ^ a : ℝ) : ℂ) * (q : ℂ) ^ j *
        (1 - x * (1 - q : ℂ) ^ 2 / 2) + ((q ^ a : ℝ) : ℂ) ^ 2 * (q : ℂ) ^ (2 * j))) /
        ((1 - q : ℂ) ^ 2) ^ k) (𝓝[<] 1)
      (𝓝 (∏ j ∈ Finset.range k, (((a : ℂ) + j) ^ 2 + x))) := by
  have hfac : ∀ j : ℕ, Tendsto (fun q : ℝ => (1 - 2 * ((q ^ a : ℝ) : ℂ) * (q : ℂ) ^ j *
      (1 - x * (1 - q : ℂ) ^ 2 / 2) + ((q ^ a : ℝ) : ℂ) ^ 2 * (q : ℂ) ^ (2 * j)) /
      (1 - q : ℂ) ^ 2) (𝓝[<] 1) (𝓝 (((a : ℂ) + j) ^ 2 + x)) := by
    intro j
    have h1 : Tendsto (fun q : ℝ => (((1 - q ^ (a + j)) / (1 - q) : ℝ) : ℂ)) (𝓝[<] 1)
        (𝓝 ((a + j : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto _).comp (tendsto_one_sub_rpow_div (a + j))
    have h2 := (h1.pow 2).add ((tendsto_rpow_nhdsWithin_lt_one (a + j)).mul_const x)
    push_cast at h2
    rw [one_mul] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
    have h1q : (1 : ℂ) - q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hq1))
    have hr : ((q ^ (a + j) : ℝ) : ℂ) = ((q ^ a : ℝ) : ℂ) * (q : ℂ) ^ j := by
      rw [Real.rpow_add hq, Real.rpow_natCast]; push_cast; ring
    rw [hr]
    field_simp
    ring
  have h := tendsto_finsetProd (Finset.range k) fun j _ => hfac j
  refine h.congr' (Eventually.of_forall fun q => ?_)
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]

theorem wilson_eq_sum_shifted {a b c d : ℂ} (hab : ∀ k : ℕ, poch (a + b) k ≠ 0)
    (hac : ∀ k : ℕ, poch (a + c) k ≠ 0) (had : ∀ k : ℕ, poch (a + d) k ≠ 0) (n : ℕ) (x : ℂ) :
    wilson a b c d n x = ∑ k ∈ Finset.range (n + 1),
      poch (a + b + k) (n - k) * poch (a + c + k) (n - k) * poch (a + d + k) (n - k) *
        (poch (-(n : ℂ)) k * poch (n + a + b + c + d - 1) k / k.factorial *
          ∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) := by
  unfold wilson
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsplit : ∀ u : ℂ, poch u n = poch u k * poch (u + k) (n - k) := fun u => by
    rw [← poch_add, Nat.add_sub_cancel' hkn]
  rw [hsplit (a + b), hsplit (a + c), hsplit (a + d)]
  have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have := hab k; have := hac k; have := had k
  field_simp

theorem aw_algebra (A Q u F1 F2 F3 G1 G2 G3 P : ℂ) (n m k : ℕ) (h1 : u ≠ 0) :
    A⁻¹ ^ n * Q ^ k * (F1 / u ^ m) * (F2 / u ^ m) * (F3 / u ^ m) * (G1 / u ^ k) * (G2 / u ^ k) /
        (G3 / u ^ k) * (P / (u ^ 2) ^ k) =
    A⁻¹ ^ n * (Q ^ k * F1 * F2 * F3 * G1 * G2 / G3 * P) / ((u ^ m) ^ 3 * (u ^ k) ^ 3) := by
  field_simp
  ring

theorem tendsto_sq_nhdsWithin_lt_one :
    Tendsto (fun q : ℝ => q ^ 2) (𝓝[<] 1) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun q : ℝ => q ^ 2) (𝓝 1) (𝓝 (1 ^ 2)) := (continuous_pow 2).tendsto 1
    rw [one_pow] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
    have hq1' : q < 1 := hq1
    show q ^ 2 < 1
    nlinarith

/-- `(q;q)_k / (1-q)^k → k!`. -/
theorem tendsto_qPochhammer_self_div (k : ℕ) :
    Tendsto (fun q : ℝ => qPochhammer (q : ℂ) (q : ℂ) k / (1 - (q : ℂ)) ^ k) (𝓝[<] 1)
      (𝓝 (k ! : ℂ)) := by
  have h := tendsto_qPochhammer_rpow_div 1 k
  push_cast at h
  rw [poch_nat_one] at h
  refine h.congr' (Eventually.of_forall fun q => ?_)
  simp [Real.rpow_one]

theorem tendsto_qPochhammer_sq_div (k : ℕ) :
    Tendsto (fun q : ℝ => qPochhammer ((q : ℂ) ^ 2) ((q : ℂ) ^ 2) k / (1 - (q : ℂ) ^ 2) ^ k)
      (𝓝[<] 1) (𝓝 (k ! : ℂ)) := by
  have h := (tendsto_qPochhammer_self_div k).comp tendsto_sq_nhdsWithin_lt_one
  refine h.congr' (Eventually.of_forall fun q => ?_)
  simp

theorem dqh_algebra (Pn Pm Gk A x u v s : ℂ) (m k : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) (hs : s ≠ 0)
    (hs2 : s ^ 2 = u * v) :
    Pn * (A * (s * x) ^ m / (Gk * Pm)) / s ^ (m + 2 * k) =
      Pn / u ^ (m + 2 * k) * A * x ^ m / (Gk / (u * v) ^ k * (Pm / u ^ m)) * (v⁻¹) ^ (2 * k) := by
  rw [inv_pow, pow_add s, pow_mul s, hs2]
  field_simp
  ring

@[dlmf 18.27.E4_2]
theorem qHahn_limit_hahn {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {N n : ℕ} (hn : n ≤ N) (x : ℝ) :
    Tendsto (fun q : ℝ => qHahn (Real.rpow q α) (Real.rpow q β) q N n (Real.rpow q (-x))) (𝓝[<] 1) (𝓝 (hahn α β N n x)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  unfold qHahn hahn terminatingBasicHG terminatingHG
  refine tendsto_finsetSum _ fun k hk => ?_
  have hkN : k ≤ N := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hn
  have hs₁ : poch (((α + 1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; exact poch_ne_zero_of_not_neg_nat hα' k
  have hs₂ : poch ((-(N : ℝ) : ℝ) : ℂ) k ≠ 0 := by
    push_cast
    rw [poch_neg_coe_nat]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hkN).ne'
  have hs₃ : poch (((1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; rw [poch_nat_one]; exact Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hq := tendsto_ofReal_nhdsWithin_lt_one
  have h := (((tendsto_qPochhammer_rpow_div (-(n : ℝ)) k).mul
    (tendsto_qPochhammer_rpow_div (α + β + (n + 1 : ℕ)) k)).mul
    (tendsto_qPochhammer_rpow_div (-x) k)).div
    (((tendsto_qPochhammer_rpow_div (α + 1) k).mul (tendsto_qPochhammer_rpow_div (-(N : ℝ)) k)).mul
      (tendsto_qPochhammer_rpow_div 1 k))
    (mul_ne_zero (mul_ne_zero hs₁ hs₂) hs₃) |>.mul (hq.pow k)
  convert h.congr' ?_ using 2
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
    push_cast
    rw [poch_nat_one]
    ring_nf
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq0 hq1
    have h1 := one_sub_ofReal_pow_ne_zero (q := q) hq1 k
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil]
    rw [ofReal_recip_pow_eq_rpow hq0, ofReal_recip_pow_eq_rpow hq0,
      show (Real.rpow q α : ℂ) * (Real.rpow q β : ℂ) * (q : ℂ) ^ (n + 1)
      = ((q ^ (α + β + (n + 1 : ℕ)) : ℝ) : ℂ) by
        rw [ofReal_pow_eq_rpow, Real.rpow_eq_pow, Real.rpow_eq_pow, ofReal_rpow_eq_cpow_aux hq0,
          ofReal_rpow_eq_cpow_aux hq0],
      show (Real.rpow q α : ℂ) * (q : ℂ) = ((q ^ (α + 1) : ℝ) : ℂ) by
        rw [Real.rpow_eq_pow, ← ofReal_rpow_eq_cpow_aux hq0, Real.rpow_one],
      show qPochhammer (q : ℂ) (q : ℂ) k =
        qPochhammer ((q ^ (1 : ℝ) : ℝ) : ℂ) (q : ℂ) k by rw [Real.rpow_one]]
    simp only [Pi.div_apply, Real.rpow_eq_pow]
    norm_num
    field_simp
    simp

@[dlmf 18.27.E14_4]
theorem littleQJacobi_limit_jacobi {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => littleQJacobi (Real.rpow q α) (Real.rpow q β) q n x) (𝓝[<] 1)
        (𝓝 ((n.factorial : ℂ) / poch (α + 1) n * jacobiPolyP α β n (1 - 2 * x))) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hP := poch_ne_zero_of_not_neg_nat hα' n
  have hJ : (n.factorial : ℂ) / poch (α + 1) n * jacobiPolyP α β n (1 - 2 * x) =
      ∑ k ∈ Finset.range (n + 1), gaussHGCoeff (-(n : ℂ)) (n + α + β + 1) (α + 1) k * x ^ k := by
    unfold jacobiPolyP
    rw [show (1 - (1 - 2 * x)) / 2 = x by ring, ordinaryHypergeometric_eq_sum_neg_nat]
    have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  rw [hJ]
  unfold littleQJacobi terminatingBasicHG
  refine tendsto_finsetSum _ fun k _ => ?_
  have hs₁ : poch (((α + 1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; exact poch_ne_zero_of_not_neg_nat hα' k
  have hs₂ : poch (((1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; rw [poch_nat_one]; exact Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hx : Tendsto (fun q : ℝ => ((q : ℂ) * x) ^ k) (𝓝[<] 1) (𝓝 (x ^ k)) := by
    have : Tendsto (fun q : ℝ => (q : ℂ) * x) (𝓝[<] 1) (𝓝 x) := by
      have := ((continuous_ofReal.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))).mul_const x
      simpa using this
    exact this.pow k
  have h := (tendsto_qPoch_two_two (-(n : ℝ)) (α + β + (n + 1 : ℕ)) (α + 1) 1 k hs₁ hs₂).mul hx
  convert h.congr' ?_ using 2
  · rw [gaussHGCoeff]
    push_cast
    rw [poch_nat_one]
    ring_nf
  · filter_upwards [eventually_pos_nhdsWithin_lt_one] with q hq
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil]
    rw [ofReal_recip_pow_eq_rpow hq, show (Real.rpow q α : ℂ) * (Real.rpow q β : ℂ) * (q : ℂ) ^ (n + 1)
      = ((q ^ (α + β + (n + 1 : ℕ)) : ℝ) : ℂ) by
        rw [ofReal_pow_eq_rpow, Real.rpow_eq_pow, Real.rpow_eq_pow, ofReal_rpow_eq_cpow_aux hq,
          ofReal_rpow_eq_cpow_aux hq],
      show (Real.rpow q α : ℂ) * (q : ℂ) = ((q ^ (α + 1) : ℝ) : ℂ) by
        rw [Real.rpow_eq_pow, ← ofReal_rpow_eq_cpow_aux hq, Real.rpow_one]]
    conv_rhs => rw [show (q : ℂ) = ((q ^ (1 : ℝ) : ℝ) : ℂ) by rw [Real.rpow_one]]
    norm_num

@[dlmf 18.27.E14_6]
theorem littleQLaguerre_limit_laguerrePolyL {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => littleQLaguerre (Real.rpow q α) q n ((1 - q : ℂ) * x)) (𝓝[<] 1)
        (𝓝 ((n.factorial : ℂ) / poch (α + 1) n * laguerrePolyL α n x)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hP := poch_ne_zero_of_not_neg_nat hα' n
  have hL : (n.factorial : ℂ) / poch (α + 1) n * laguerrePolyL α n x =
      ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k / (poch (α + 1) k * k.factorial) * x ^ k := by
    unfold laguerrePolyL
    rw [kummerM_eq_sum_neg_nat]
    have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  rw [hL]
  unfold littleQLaguerre littleQJacobi terminatingBasicHG
  refine tendsto_finsetSum _ fun k _ => ?_
  have hs₁ : poch (((α + 1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; exact poch_ne_zero_of_not_neg_nat hα' k
  have hs₂ : poch (((1 : ℝ)) : ℂ) k ≠ 0 := by
    push_cast; rw [poch_nat_one]; exact Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hx : Tendsto (fun q : ℝ => ((q : ℂ) * x) ^ k) (𝓝[<] 1) (𝓝 (x ^ k)) := by
    simpa using (tendsto_ofReal_nhdsWithin_lt_one.mul_const x).pow k
  have h := ((tendsto_qPochhammer_rpow_div (-(n : ℝ)) k).div
    ((tendsto_qPochhammer_rpow_div (α + 1) k).mul (tendsto_qPochhammer_rpow_div 1 k))
    (mul_ne_zero hs₁ hs₂)).mul hx
  convert h.congr' ?_ using 2
  · push_cast
    rw [poch_nat_one]
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
    have h1 := one_sub_ofReal_pow_ne_zero (q := q) hq1 k
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil, mul_zero, zero_mul, qPochhammer_zero_param]
    rw [ofReal_recip_pow_eq_rpow hq,
      show (Real.rpow q α : ℂ) * (q : ℂ) = ((q ^ (α + 1) : ℝ) : ℂ) by
        rw [Real.rpow_eq_pow, ← ofReal_rpow_eq_cpow_aux hq, Real.rpow_one]]
    conv_rhs => rw [show (q : ℂ) = ((q ^ (1 : ℝ) : ℝ) : ℂ) by rw [Real.rpow_one]]
    simp only [Pi.div_apply]
    norm_num
    field_simp
    simp only [mul_pow]
    ring

@[dlmf 18.27.E17_3]
theorem qLaguerre_limit_laguerrePolyL {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => qLaguerre α q n ((1 - q : ℂ) * x)) (𝓝[<] 1)
        (𝓝 (laguerrePolyL α n x)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hs : ∀ k : ℕ, poch (((α + 1 : ℝ)) : ℂ) k ≠ 0 := fun k => by
    push_cast; exact poch_ne_zero_of_not_neg_nat hα' k
  have h1s : ∀ k : ℕ, poch (((1 : ℝ)) : ℂ) k ≠ 0 := fun k => by
    push_cast; rw [poch_nat_one]; exact Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hL : laguerrePolyL α n x = poch (α + 1) n / n ! *
      ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k / (poch (α + 1) k * k.factorial) *
        ((-1) ^ k * (-x) ^ k) := by
    unfold laguerrePolyL
    rw [kummerM_eq_sum_neg_nat]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_pow]; ring_nf
  rw [hL]
  unfold qLaguerre terminatingBasicHG
  have hpre : Tendsto (fun q : ℝ => qPochhammer ((q : ℂ) ^ ((α : ℂ) + 1)) q n /
      qPochhammer (q : ℂ) q n) (𝓝[<] 1) (𝓝 (poch (α + 1) n / n !)) := by
    have h := (tendsto_qPochhammer_rpow_div (α + 1) n).div (tendsto_qPochhammer_rpow_div 1 n)
      (h1s n)
    convert h.congr' ?_ using 2
    · push_cast
      rw [poch_nat_one]
    · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
      have h1 := one_sub_ofReal_pow_ne_zero (q := q) hq1 n
      rw [ofReal_cpow_add_one hq, show qPochhammer (q : ℂ) (q : ℂ) n =
        qPochhammer ((q ^ (1 : ℝ) : ℝ) : ℂ) (q : ℂ) n by rw [Real.rpow_one]]
      simp only [Pi.div_apply]
      field_simp
  refine hpre.mul (tendsto_finsetSum _ fun k _ => ?_)
  have hq1 := tendsto_ofReal_nhdsWithin_lt_one
  have hpow : Tendsto (fun q : ℝ => (q : ℂ) ^ ((n : ℂ) + (α : ℂ) + 1)) (𝓝[<] 1) (𝓝 1) := by
    have hc : ContinuousAt (fun w : ℂ => w ^ ((n : ℂ) + (α : ℂ) + 1)) 1 :=
      continuousAt_id.cpow continuousAt_const (by simp)
    have h2 := hc.tendsto.comp hq1
    rw [one_cpow] at h2
    exact h2
  have hz : Tendsto (fun q : ℝ => ((-1 : ℂ) ^ k * (q : ℂ) ^ (k * (k - 1) / 2)) *
      (-x * (q : ℂ) ^ ((n : ℂ) + (α : ℂ) + 1)) ^ k) (𝓝[<] 1) (𝓝 ((-1) ^ k * (-x) ^ k)) := by
    have := ((hq1.pow (k * (k - 1) / 2)).const_mul ((-1 : ℂ) ^ k)).mul
      ((hpow.const_mul (-x)).pow k)
    simpa using this
  have h := ((tendsto_qPochhammer_rpow_div (-(n : ℝ)) k).div
    ((tendsto_qPochhammer_rpow_div (α + 1) k).mul (tendsto_qPochhammer_rpow_div 1 k))
    (mul_ne_zero (hs k) (h1s k))).mul hz
  convert h.congr' ?_ using 2
  · push_cast
    rw [poch_nat_one]
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq hq1
    have h1 := one_sub_ofReal_pow_ne_zero (q := q) hq1 k
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_cons, List.length_nil]
    rw [ofReal_recip_pow_eq_rpow hq, ofReal_cpow_add_one hq, show qPochhammer (q : ℂ) (q : ℂ) k =
        qPochhammer ((q ^ (1 : ℝ) : ℝ) : ℂ) (q : ℂ) k by rw [Real.rpow_one]]
    simp only [Pi.div_apply]
    norm_num
    field_simp
    simp only [neg_pow (x * _), neg_pow ((1 - (q : ℂ)) * x * _), mul_pow]
    ring

@[dlmf 18.28.E29]
theorem askeyWilson_limit_wilson {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => askeyWilson (Real.rpow q a) (Real.rpow q b) (Real.rpow q c) (Real.rpow q d) q n (1 - x * (1 - q : ℂ) ^ 2 / 2) / (1 - q : ℂ) ^ (3 * n)) (𝓝[<] 1) (𝓝 (wilson a b c d n x)) := by
  have hpos : ∀ (u : ℝ), 0 < u → ∀ k : ℕ, poch (u : ℂ) k ≠ 0 := fun u hu k =>
    poch_ne_zero_of_not_neg_nat (fun j h => by
      have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) k
  have hab : ∀ k : ℕ, poch ((a : ℂ) + b) k ≠ 0 := fun k => by
    have := hpos (a + b) (by linarith) k; push_cast at this; exact this
  have hac : ∀ k : ℕ, poch ((a : ℂ) + c) k ≠ 0 := fun k => by
    have := hpos (a + c) (by linarith) k; push_cast at this; exact this
  have had : ∀ k : ℕ, poch ((a : ℂ) + d) k ≠ 0 := fun k => by
    have := hpos (a + d) (by linarith) k; push_cast at this; exact this
  rw [wilson_eq_sum_shifted hab hac had]
  unfold askeyWilson
  simp_rw [Finset.mul_sum, Finset.sum_div]
  refine tendsto_finsetSum _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hk1 : poch ((1 : ℝ) : ℂ) k ≠ 0 := by
    push_cast; rw [poch_nat_one]; exact Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hq := tendsto_ofReal_nhdsWithin_lt_one
  have hA : Tendsto (fun q : ℝ => ((Real.rpow q a : ℝ) : ℂ)⁻¹ ^ n) (𝓝[<] 1) (𝓝 1) := by
    simpa using ((tendsto_rpow_nhdsWithin_lt_one a).inv₀ one_ne_zero).pow n
  have h := ((((((((hA.mul (hq.pow k)).mul
    (tendsto_qPochhammer_rpow_div (a + b + k) (n - k))).mul
    (tendsto_qPochhammer_rpow_div (a + c + k) (n - k))).mul
    (tendsto_qPochhammer_rpow_div (a + d + k) (n - k))).mul
    (tendsto_qPochhammer_rpow_div (-(n : ℝ)) k)).mul
    (tendsto_qPochhammer_rpow_div (a + b + c + d + ((n : ℝ) - 1)) k)).div
    (tendsto_qPochhammer_rpow_div 1 k) hk1).mul (tendsto_askeyWilson_prod a x k))
  convert h.congr' ?_ using 2
  · push_cast
    rw [poch_nat_one]
    generalize ∏ j ∈ Finset.range k, (((a : ℂ) + j) ^ 2 + x) = P
    ring_nf
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq0 hq1
    have h1 : (1 : ℂ) - q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hq1))
    have e3 : ((1 : ℂ) - q) ^ (3 * n) = (((1 : ℂ) - q) ^ (n - k)) ^ 3 * ((1 - q) ^ k) ^ 3 := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
    have cv2 : ∀ u v : ℝ, ((Real.rpow q u : ℝ) : ℂ) * ((Real.rpow q v : ℝ) : ℂ) * (q : ℂ) ^ k =
        ((q ^ (u + v + k) : ℝ) : ℂ) := fun u v => by
      rw [ofReal_pow_eq_rpow, Real.rpow_eq_pow, Real.rpow_eq_pow, ofReal_rpow_eq_cpow_aux hq0,
        ofReal_rpow_eq_cpow_aux hq0]
    have cv4 : ((Real.rpow q a : ℝ) : ℂ) * ((Real.rpow q b : ℝ) : ℂ) * ((Real.rpow q c : ℝ) : ℂ) *
        ((Real.rpow q d : ℝ) : ℂ) * (q : ℂ) ^ ((n : ℤ) - 1) =
        ((q ^ (a + b + c + d + ((n : ℝ) - 1)) : ℝ) : ℂ) := by
      have : (q : ℂ) ^ ((n : ℤ) - 1) = ((q ^ ((n : ℝ) - 1) : ℝ) : ℂ) := by
        rw [show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
        push_cast; ring
      rw [this, Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_eq_pow,
        ofReal_rpow_eq_cpow_aux hq0, ofReal_rpow_eq_cpow_aux hq0, ofReal_rpow_eq_cpow_aux hq0,
        ofReal_rpow_eq_cpow_aux hq0]
    rw [cv2 a b, cv2 a c, cv2 a d, cv4, ofReal_recip_pow_eq_rpow hq0,
      show qPochhammer (q : ℂ) (q : ℂ) k = qPochhammer ((q ^ (1 : ℝ) : ℝ) : ℂ) (q : ℂ) k by
        rw [Real.rpow_one], e3]
    simp only [Pi.div_apply, Real.rpow_eq_pow]
    exact aw_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ h1

@[dlmf 18.28.E31]
theorem qGegenbauer_limit_ultrasphPoly {lam : ℝ} (hlam : -1 / 2 < lam) (n : ℕ) (θ : ℝ) :
    Tendsto (fun q : ℝ => qGegenbauer (Real.rpow q lam) q n (exp (I * θ))) (𝓝[<] 1)
        (𝓝 (ultrasphPoly lam n (Real.cos θ))) := by
  let w : ℂ := exp (-I * θ)
  have hw : w ≠ 0 := exp_ne_zero _
  have hwi : w⁻¹ = exp (I * θ) := by
    dsimp [w]
    rw [← exp_neg]
    congr 1
    ring
  have hcos : (w + w⁻¹) / 2 = (Real.cos θ : ℂ) := by
    rw [hwi, ofReal_cos]
    dsimp [w]
    rw [Complex.cos]
    congr 1 <;> ring
  rw [← hcos, ultrasphPoly_eq_coeff_gegenbauerSeries (by simpa using hlam) hw,
    coeff_gegenbauerSeries]
  unfold qGegenbauer
  refine tendsto_finsetSum _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (exp (I * θ)) ^ ((n : ℤ) - 2 * k) = w ^ k * w⁻¹ ^ (n - k) := by
    rw [← exp_int_mul, hwi]
    dsimp [w]
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
    congr 1
    push_cast [Nat.cast_sub hkn]
    ring
  have h := (((tendsto_qPochhammer_rpow_div lam k).mul
    (tendsto_qPochhammer_rpow_div lam (n - k))).div
    ((tendsto_qPochhammer_self_div k).mul (tendsto_qPochhammer_self_div (n - k)))
    (mul_ne_zero (Nat.cast_ne_zero.mpr k.factorial_ne_zero)
      (Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero))).mul_const
        ((exp (I * θ)) ^ ((n : ℤ) - 2 * k))
  rw [hpow] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hk0 := one_sub_ofReal_pow_ne_zero hq k
  have hnk0 := one_sub_ofReal_pow_ne_zero hq (n - k)
  simp only [Pi.div_apply]
  rw [hpow]
  field_simp
  simp only [Real.rpow_eq_pow]


@[dlmf 18.27.E25]
theorem discreteQHermiteI_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => discreteQHermiteI q n ((Real.sqrt (1 - q ^ 2) : ℂ) * x) /
      (Real.sqrt (1 - q ^ 2) : ℂ) ^ n) (𝓝[<] 1) (𝓝 ((2 : ℂ)⁻¹ ^ n * aeval x (hermitePolyH n))) := by
  rw [hermitePolyH_finite_sum, Finset.mul_sum, Finset.mul_sum]
  unfold discreteQHermiteI
  simp_rw [Finset.mul_sum, Finset.sum_div]
  refine tendsto_finsetSum _ fun k hk => ?_
  have hk2 : 2 * k ≤ n := by
    have := Finset.mem_range.mp hk; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * k := ⟨n - 2 * k, by omega⟩
  rw [show m + 2 * k - 2 * k = m by omega]
  have hq := tendsto_ofReal_nhdsWithin_lt_one
  have hv : Tendsto (fun q : ℝ => ((1 + (q : ℂ))⁻¹) ^ (2 * k)) (𝓝[<] 1) (𝓝 ((2 : ℂ)⁻¹ ^ (2 * k))) := by
    have := ((hq.const_add 1).inv₀ (by norm_num)).pow (2 * k)
    norm_num at this ⊢
    exact this
  have hfk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hfm : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have h := (((((tendsto_qPochhammer_self_div (m + 2 * k)).mul
    ((hq.pow (k * (k - 1))).const_mul ((-1 : ℂ) ^ k))).mul_const (x ^ m)).div
    ((tendsto_qPochhammer_sq_div k).mul (tendsto_qPochhammer_self_div m))
    (mul_ne_zero hfk hfm)).mul hv)
  convert h.congr' ?_ using 2
  · rw [one_pow, mul_one, mul_pow, pow_add (2 : ℂ)⁻¹]
    simp only [inv_pow]
    field_simp
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq0 hq1
    have hq1' : q < 1 := hq1
    have hu : (1 : ℂ) - q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith)
    have hv0 : (1 : ℂ) + q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith)
    have hpos : 0 < 1 - q ^ 2 := by nlinarith
    have hs : ((Real.sqrt (1 - q ^ 2) : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
    have hs2 : ((Real.sqrt (1 - q ^ 2) : ℝ) : ℂ) ^ 2 = (1 - q) * (1 + q) := by
      rw [← ofReal_pow, Real.sq_sqrt hpos.le]; push_cast; ring
    have hq2 : (1 : ℂ) - (q : ℂ) ^ 2 = (1 - q) * (1 + q) := by ring
    simp only [Pi.div_apply]
    rw [hq2, dqh_algebra _ _ _ _ _ _ _ _ m k hu hv0 hs hs2]


@[dlmf 18.27.E26]
theorem discreteQHermiteII_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => discreteQHermiteII q n ((Real.sqrt (1 - q ^ 2) : ℂ) * x) /
      (Real.sqrt (1 - q ^ 2) : ℂ) ^ n) (𝓝[<] 1) (𝓝 ((2 : ℂ)⁻¹ ^ n * aeval x (hermitePolyH n))) := by
  rw [hermitePolyH_finite_sum, Finset.mul_sum, Finset.mul_sum]
  unfold discreteQHermiteII
  simp_rw [Finset.mul_sum, Finset.sum_div]
  refine tendsto_finsetSum _ fun k hk => ?_
  have hk2 : 2 * k ≤ n := by
    have := Finset.mem_range.mp hk; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * k := ⟨n - 2 * k, by omega⟩
  rw [show m + 2 * k - 2 * k = m by omega]
  have hq := tendsto_ofReal_nhdsWithin_lt_one
  have hv : Tendsto (fun q : ℝ => ((1 + (q : ℂ))⁻¹) ^ (2 * k)) (𝓝[<] 1) (𝓝 ((2 : ℂ)⁻¹ ^ (2 * k))) := by
    have := ((hq.const_add 1).inv₀ (by norm_num)).pow (2 * k)
    norm_num at this ⊢
    exact this
  have hfk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hfm : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have h := (((((tendsto_qPochhammer_self_div (m + 2 * k)).mul
    ((((hq.inv₀ one_ne_zero).pow (2 * (m + 2 * k) * k)).mul (hq.pow (k * (2 * k + 1)))).const_mul
      ((-1 : ℂ) ^ k))).mul_const (x ^ m)).div
    ((tendsto_qPochhammer_sq_div k).mul (tendsto_qPochhammer_self_div m))
    (mul_ne_zero hfk hfm)).mul hv)
  convert h.congr' ?_ using 2
  · rw [inv_one, one_pow, one_pow, mul_one, mul_one, mul_pow, pow_add (2 : ℂ)⁻¹]
    simp only [inv_pow]
    field_simp
  · filter_upwards [eventually_pos_nhdsWithin_lt_one, self_mem_nhdsWithin] with q hq0 hq1
    have hq1' : q < 1 := hq1
    have hu : (1 : ℂ) - q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith)
    have hv0 : (1 : ℂ) + q ≠ 0 := by
      rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith)
    have hpos : 0 < 1 - q ^ 2 := by nlinarith
    have hs : ((Real.sqrt (1 - q ^ 2) : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
    have hs2 : ((Real.sqrt (1 - q ^ 2) : ℝ) : ℂ) ^ 2 = (1 - q) * (1 + q) := by
      rw [← ofReal_pow, Real.sq_sqrt hpos.le]; push_cast; ring
    have hq2 : (1 : ℂ) - (q : ℂ) ^ 2 = (1 - q) * (1 + q) := by ring
    simp only [Pi.div_apply]
    rw [hq2, dqh_algebra _ _ _ _ _ _ _ _ m k hu hv0 hs hs2]
    ring


/-- The coefficient in the Askey–Wilson q-difference operator. -/
@[dlmf 18.28.E6_2]
def askeyWilsonDifferenceCoefficient (a b c d q z : ℂ) : ℂ :=
  (1 - a * z) * (1 - b * z) * (1 - c * z) * (1 - d * z) / ((1 - z ^ 2) * (1 - q * z ^ 2))

/-- The Askey–Wilson operator is triangular on the paired q-Pochhammer basis. -/
private lemma askeyWilson_basis_step {a b c d q z : ℂ} (hq : q ≠ 0) (hz : z ≠ 0)
    (hz1 : z^2 ≠ 1) (hzq : q*z^2 ≠ 1) (hzqi : q*z⁻¹^2 ≠ 1) (k : ℕ) :
    askeyWilsonDifferenceCoefficient a b c d q z *
      (qPochhammer (a*(q*z)) q (k+1)*qPochhammer (a/(q*z)) q (k+1) -
       qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) +
    askeyWilsonDifferenceCoefficient a b c d q z⁻¹ *
      (qPochhammer (a*(z/q)) q (k+1)*qPochhammer (a/(z/q)) q (k+1) -
       qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) =
    (q⁻¹^(k+1)-1)*(1-a*b*c*d*q^k)*
      (qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) -
    (q⁻¹^(k+1)-1)*(1-a*b*q^k)*(1-a*c*q^k)*(1-a*d*q^k)*
      (qPochhammer (a*z) q k*qPochhammer (a/z) q k) := by
  have hp : (1-a*z)*qPochhammer (a*(q*z)) q (k+1) =
      (1-a*z*q^(k+1))*qPochhammer (a*z) q (k+1) := by
    rw [show a*(q*z)=a*z*q by ring, ← qPochhammer_succ', qPochhammer_succ]
    ring
  have hm : (1-a/z)*qPochhammer (a/(z/q)) q (k+1) =
      (1-a/z*q^(k+1))*qPochhammer (a/z) q (k+1) := by
    rw [show a/(z/q)=a/z*q by field_simp,
      ← qPochhammer_succ', qPochhammer_succ]
    ring
  have hlow : qPochhammer (a/(q*z)) q (k+1) =
      (1-a/(q*z))*qPochhammer (a/z) q k := by
    rw [qPochhammer_succ', show a/(q*z)*q=a/z by field_simp]
  have hlow' : qPochhammer (a*(z/q)) q (k+1) =
      (1-a*(z/q))*qPochhammer (a*z) q k := by
    rw [qPochhammer_succ', show a*(z/q)*q=a*z by field_simp]
  have hz2 : 1-z^2 ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hzq2 : 1-q*z^2 ≠ 0 := sub_ne_zero.mpr hzq.symm
  have hzqi2 : 1-q*z⁻¹^2 ≠ 0 := sub_ne_zero.mpr hzqi.symm
  have hzInv : 1-z⁻¹^2 ≠ 0 := by
    rw [inv_pow, sub_ne_zero, ne_eq, eq_comm, inv_eq_one]
    exact hz1
  have hzq2' : 1-z^2*q ≠ 0 := by simpa [mul_comm] using hzq2
  have hzqi2' : z^2-q ≠ 0 := by
    intro h
    apply hzqi2
    rw [sub_eq_zero] at h
    rw [← h, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hz),sub_self]
  let Cplus := (1-b*z)*(1-c*z)*(1-d*z)/((1-z^2)*(1-q*z^2))
  let Cminus := (1-b/z)*(1-c/z)*(1-d/z)/((1-z⁻¹^2)*(1-q*z⁻¹^2))
  have hplus : askeyWilsonDifferenceCoefficient a b c d q z *
      (qPochhammer (a*(q*z)) q (k+1)*qPochhammer (a/(q*z)) q (k+1) -
       qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) =
      -(a*(1-q^(k+1))/q)*(1-a*z*q^k)*(1-b*z)*(1-c*z)*(1-d*z)/(z*(1-z^2))*
        (qPochhammer (a*z) q k*qPochhammer (a/z) q k) := by
    calc
      _ = Cplus * ((1-a*z)*qPochhammer (a*(q*z)) q (k+1)*
          qPochhammer (a/(q*z)) q (k+1) -
        (1-a*z)*qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) := by
          dsimp only [askeyWilsonDifferenceCoefficient,Cplus];ring
      _ = Cplus * ((1-a*z*q^(k+1))*qPochhammer (a*z) q (k+1)*
          ((1-a/(q*z))*qPochhammer (a/z) q k) -
        (1-a*z)*qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) := by
          rw [hp,hlow]
      _ = _ := by
        simp only [qPochhammer_succ, pow_succ q k]
        dsimp only [Cplus]
        generalize qPochhammer (a*z) q k = P
        generalize qPochhammer (a/z) q k = Q
        field_simp [hq,hz,hz2,hzq2,hzq2']
        ring
  have hminus : askeyWilsonDifferenceCoefficient a b c d q z⁻¹ *
      (qPochhammer (a*(z/q)) q (k+1)*qPochhammer (a/(z/q)) q (k+1) -
       qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) =
      -(a*(1-q^(k+1))/q)*(1-a/z*q^k)*(1-b/z)*(1-c/z)*(1-d/z)*z/(1-z⁻¹^2)*
        (qPochhammer (a*z) q k*qPochhammer (a/z) q k) := by
    calc
      _ = Cminus * ((1-a/z)*qPochhammer (a/(z/q)) q (k+1)*
          qPochhammer (a*(z/q)) q (k+1) -
        (1-a/z)*qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) := by
          simp only [askeyWilsonDifferenceCoefficient,div_eq_mul_inv,Cminus];ring
      _ = Cminus * ((1-a/z*q^(k+1))*qPochhammer (a/z) q (k+1)*
          ((1-a*(z/q))*qPochhammer (a*z) q k) -
        (1-a/z)*qPochhammer (a*z) q (k+1)*qPochhammer (a/z) q (k+1)) := by
          rw [hm,hlow']
      _ = _ := by
        simp only [qPochhammer_succ, pow_succ q k]
        dsimp only [Cminus]
        generalize qPochhammer (a*z) q k = P
        generalize qPochhammer (a/z) q k = Q
        field_simp [hq,hz,hzInv,hzqi2,hzqi2']
        ring
  rw [hplus,hminus]
  simp only [qPochhammer_succ,inv_pow,pow_succ q k]
  generalize qPochhammer (a*z) q k = P
  generalize qPochhammer (a/z) q k = Q
  field_simp [hq,hz,hz2,hzInv]
  ring

@[dlmf 18.28.E6_1]
theorem askeyWilson_difference_equation {a b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hab : ‖a * b‖ < 1) (hac : ‖a * c‖ < 1) (had : ‖a * d‖ < 1) (n : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hz1 : z ^ 2 ≠ 1) (hzq : q * z ^ 2 ≠ 1) (hzqi : q * z⁻¹ ^ 2 ≠ 1) :
    askeyWilsonDifferenceCoefficient a b c d q z *
      (askeyWilsonLaurent a b c d q n (q * z) - askeyWilsonLaurent a b c d q n z) +
    askeyWilsonDifferenceCoefficient a b c d q z⁻¹ *
      (askeyWilsonLaurent a b c d q n (z / q) - askeyWilsonLaurent a b c d q n z) =
    (q⁻¹ ^ n - 1) * (1 - a * b * c * d * q ^ ((n : ℤ) - 1)) * askeyWilsonLaurent a b c d q n z := by
  let P := a*b*c*d/q
  let c₀ (k : ℕ) := qPochhammer (q⁻¹^n) q k * qPochhammer (P*q^n) q k * q^k /
    (qPochhammer (a*b) q k*qPochhammer (a*c) q k*qPochhammer (a*d) q k*qPochhammer q q k)
  let e (k : ℕ) := (q⁻¹^k-1)*(1-P*q^k)
  let L (k : ℕ) := (q⁻¹^(k+1)-1)*(1-a*b*q^k)*(1-a*c*q^k)*(1-a*d*q^k)
  let B (k : ℕ) (w : ℂ) := qPochhammer (a*w) q k*qPochhammer (a/w) q k
  have hP (k : ℕ) : P*q^(k+1)=a*b*c*d*q^k := by
    dsimp only [P];rw [pow_succ];field_simp
  have hPn : a*b*c*d*q^((n:ℤ)-1)=P*q^n := by
    rw [zpow_sub₀ hq0,zpow_natCast,zpow_one];dsimp only [P];ring
  have hD (w : ℂ) (hw : ‖w‖ < 1) (k : ℕ) : qPochhammer w q k ≠ 0 :=
    qPochhammer_ne_zero_of_factors hq (one_sub_mul_pow_ne_zero_of_norm hw hq) k
  have hc (k : ℕ) : c₀ (k+1)*L k = (e k-e n)*c₀ k := by
    have hAk := hD (a*b) hab k
    have hBk := hD (a*c) hac k
    have hCk := hD (a*d) had k
    have hQk := qPochhammer_self_ne_zero hq k
    have hA1 := one_sub_mul_pow_ne_zero_of_norm hab hq k
    have hB1 := one_sub_mul_pow_ne_zero_of_norm hac hq k
    have hC1 := one_sub_mul_pow_ne_zero_of_norm had hq k
    have hQ1 := one_sub_mul_pow_ne_zero_of_norm hq hq k
    have hraw : c₀ (k+1)*((1-a*b*q^k)*(1-a*c*q^k)*(1-a*d*q^k)*(1-q*q^k)) =
        c₀ k*q*(1-q⁻¹^n*q^k)*(1-P*q^n*q^k) := by
      dsimp only [c₀]
      simp only [qPochhammer_succ]
      generalize qPochhammer (a*b) q k = A at hAk ⊢
      generalize qPochhammer (a*c) q k = B at hBk ⊢
      generalize qPochhammer (a*d) q k = C at hCk ⊢
      generalize qPochhammer q q k = F at hQk ⊢
      generalize 1-a*b*q^k = U at hA1 ⊢
      generalize 1-a*c*q^k = V at hB1 ⊢
      generalize 1-a*d*q^k = W at hC1 ⊢
      generalize 1-q*q^k = X at hQ1 ⊢
      rw [pow_succ q k]
      field_simp
    have hL : L k = ((1-a*b*q^k)*(1-a*c*q^k)*(1-a*d*q^k)*(1-q*q^k))/q^(k+1) := by
      dsimp only [L];simp only [inv_pow,pow_succ q k]
      field_simp
    rw [hL,←mul_div_assoc,hraw]
    dsimp only [e]
    simp only [inv_pow,pow_succ q k]
    field_simp
    ring
  let R (k : ℕ) := askeyWilsonDifferenceCoefficient a b c d q z*(B k (q*z)-B k z) +
    askeyWilsonDifferenceCoefficient a b c d q z⁻¹*(B k (z/q)-B k z)-e n*B k z
  let G (k : ℕ) := c₀ k*(e k-e n)*B k z
  have ht (k : ℕ) : c₀ (k+1)*R (k+1)=G (k+1)-G k := by
    have hb := askeyWilson_basis_step (a:=a) (b:=b) (c:=c) (d:=d) hq0 hz hz1 hzq hzqi k
    rw [← hP k] at hb
    change askeyWilsonDifferenceCoefficient a b c d q z*(B (k+1) (q*z)-B (k+1) z) +
      askeyWilsonDifferenceCoefficient a b c d q z⁻¹*(B (k+1) (z/q)-B (k+1) z) =
      e (k+1)*B (k+1) z-L k*B k z at hb
    dsimp only [R,G]
    rw [hb]
    linear_combination -(B k z)*hc k
  have hkey : ∑ k ∈ Finset.range (n+1),c₀ k*R k = 0 := by
    rw [Finset.sum_range_succ']
    rw [Finset.sum_congr rfl fun k _ => ht k,Finset.sum_range_sub]
    simp only [G,R,c₀,e,B,qPochhammer_zero,pow_zero,one_mul,sub_self,zero_mul,
      mul_zero,zero_sub,div_one]
    ring
  have hpoly (w : ℂ) : askeyWilsonLaurent a b c d q n w =
      ∑ k ∈ Finset.range (n+1),c₀ k*B k w := by
    unfold askeyWilsonLaurent terminatingBasicHG
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,List.length_cons,
      List.length_nil,mul_one]
    norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,
      show (1+(3:ℤ)-4)=0 by norm_num,zpow_zero,mul_one]
    rw [hPn]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [c₀,B]
    ring
  rw [hpoly,hpoly,hpoly,hPn]
  change _ = e n*∑ k ∈ Finset.range (n+1),c₀ k*B k z
  have he : ∑ k ∈ Finset.range (n+1),c₀ k*R k =
      askeyWilsonDifferenceCoefficient a b c d q z*
        ((∑ k ∈ Finset.range (n+1),c₀ k*B k (q*z))-∑ k ∈ Finset.range (n+1),c₀ k*B k z) +
      askeyWilsonDifferenceCoefficient a b c d q z⁻¹*
        ((∑ k ∈ Finset.range (n+1),c₀ k*B k (z/q))-∑ k ∈ Finset.range (n+1),c₀ k*B k z) -
      e n*∑ k ∈ Finset.range (n+1),c₀ k*B k z := by
    simp only [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [R]
    ring
  rw [hkey] at he
  exact sub_eq_zero.mp he.symm


/-- Leading asymptotic coefficient; its argument is on the unit circle. -/
@[dlmf 18.29.E2]
def askeyWilsonAsymptoticCoefficient (a b c d q z : ℂ) : ℂ :=
  qPochhammerInf (a / z) q * qPochhammerInf (b / z) q *
    qPochhammerInf (c / z) q * qPochhammerInf (d / z) q / qPochhammerInf (z⁻¹ ^ 2) q

@[dlmf 18.29.E1]
theorem askeyWilson_asymptotic {a b c d q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (ha0 : a ≠ 0) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) (hd : |d| < 1)
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Tendsto (fun n : ℕ => askeyWilson a b c d q n (Real.cos θ) -
      (exp (I * n * θ) * askeyWilsonAsymptoticCoefficient a b c d q (exp (I * θ)) +
       exp (-I * n * θ) * askeyWilsonAsymptoticCoefficient a b c d q (exp (-I * θ)))) atTop (𝓝 0) := by
  sorry


end DLMF.OrthogonalPolynomials
