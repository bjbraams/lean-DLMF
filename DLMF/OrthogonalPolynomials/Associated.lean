/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Explicit
public import DLMF.OrthogonalPolynomials.Differential
/-!
# Associated, Bessel, Pollaczek, Freud, and exceptional polynomials

Finite Bessel orthogonality expands into reciprocal Gamma moments and a finite
Pochhammer Vandermonde convolution. Mathlib’s reciprocal-power and exponential changes
of variables justify the integrals and transfer the Bessel norm to the Morse functions.

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology
open DLMF.Hypergeometric
open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- General associated family. The shift may be real, as in DLMF §18.30.
The `n = 0` step is written separately to avoid a negative natural index. -/
@[dlmf 18.30.E3]
def associated (A B C : ℝ → ℂ) (c : ℝ) : ℕ → ℂ → ℂ
  | 0, _ => 1
  | 1, x => A c * x + B c
  | n + 2, x => (A (n + 1 + c) * x + B (n + 1 + c)) * associated A B C c (n + 1) x -
      C (n + 1 + c) * associated A B C c n x

/-- The associated Laguerre polynomials `L_n^{(λ)}(x; c)`, defined by the shifted Laguerre
recurrence (DLMF 18.30.9). -/
@[dlmf 18.30.E9]
def associatedLaguerre (lam : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => -(t + 1 : ℂ)⁻¹)
    (fun t => (2 * t + lam + 1) / (t + 1)) (fun t => (t + lam) / (t + 1)) c

/-- The associated Hermite polynomials `H_n(x; c)`, defined by the shifted Hermite recurrence
(DLMF 18.30.13). -/
@[dlmf 18.30.E13]
def associatedHermite (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun _ => 2) (fun _ => 0) (fun t => 2 * t) c

/-- The associated Meixner–Pollaczek polynomials `P_n^{(λ)}(x; φ, c)`, defined by the
shifted recurrence (DLMF 18.30.16). -/
@[dlmf 18.30.E16]
def associatedMeixnerPollaczek (lam phi : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => 2 * sin phi / (t + 1))
    (fun t => 2 * (t + lam) * cos phi / (t + 1))
    (fun t => (t + 2 * lam - 1) / (t + 1)) c

/-- The (associated) Pollaczek polynomials `P_n^{(λ)}(x; a, b, c)`, defined by their
three-term recurrence (DLMF 18.35.2). -/
@[dlmf 18.35.E2]
def pollaczek (lam a b : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => 2 * (t + lam + a) / (t + 1))
    (fun t => 2 * b / (t + 1)) (fun t => (t + 2 * lam - 1) / (t + 1)) c

/-- The Bessel polynomial `y_n(x; a) = ₂F₀(-n, n+a-1; ; -x/2)` (DLMF 18.34.1). -/
@[dlmf 18.34.E1]
def besselPolynomial (a : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), n + a - 1] [] (-x / 2)

/-- Polynomial form of the reversal, valid also at zero. -/
@[dlmf 18.34.E2]
def reverseBesselPolynomial (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k * poch (n + 1) k *
    (-1 / 2 : ℂ) ^ k * x ^ (n - k) / k.factorial

/-- The Freud weight `|x|^α e^{-Q(x)}` (DLMF 18.32.2). -/
@[dlmf 18.32.E2]
def freudWeight (α : ℝ) (Q : ℝ → ℝ) (x : ℝ) : ℝ :=
  |x| ^ α * Real.exp (-Q x)

/-- Degree `n + 1`: exceptional Laguerre has no degree-zero member. -/
@[dlmf 18.36.E5]
def exceptionalLaguerre (k : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  -(x + k + 1) * laguerrePolyL k n x + if n = 0 then 0 else laguerrePolyL k (n - 1) x

/-- The exceptional Laguerre weight `x^k e^{-x}/(x+k)²` (DLMF 18.36.3). -/
@[dlmf 18.36.E3]
def exceptionalLaguerreWeight (k x : ℝ) : ℝ := x ^ k * Real.exp (-x) / (x + k) ^ 2

/-- The exceptional Hermite degrees are 0, 3, 4, …; the index type omits 1 and 2. -/
@[dlmf 18.36.E9]
def exceptionalHermite : Option ℕ → ℝ → ℝ
  | none, _ => (2 : ℝ) ^ (3 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ)
  | some n, x => ((4 * x ^ 2 + 2) * aeval x (hermitePolyH (n + 1)) +
      8 * x * aeval x (hermitePolyH n)) /
      (Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (2 ^ (n + 1) * (n + 3) * n.factorial))

@[dlmf 18.30.E2]
theorem associated_zero (A B C : ℝ → ℂ) (c : ℝ) (x : ℂ) : associated A B C c 0 x = 1 := by
  rfl

@[dlmf 18.30.E19]
theorem associatedPollaczek_limit_laguerrePolyL (lam : ℂ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : ℂ) :
    Tendsto (fun phi : ℝ => associatedMeixnerPollaczek ((lam + 1) / 2) phi c n (-x / (2 * sin (phi : ℂ))))
      (𝓝[>] 0) (𝓝 (associatedLaguerre lam c n x)) := by
  have hcos : Tendsto (fun phi : ℝ => cos (phi : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    have h : Tendsto (fun phi : ℝ => cos (phi : ℂ)) (𝓝 0) (𝓝 (cos ((0 : ℝ) : ℂ))) :=
      Continuous.tendsto (by fun_prop) 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hsin : ∀ᶠ phi : ℝ in 𝓝[>] 0, sin (phi : ℂ) ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi by positivity)] with phi hphi
    rw [← ofReal_sin]
    exact ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hphi.1 hphi.2).ne'
  have ht : ∀ n : ℕ, ((n : ℝ) + 1 + c : ℂ) + 1 ≠ 0 := fun n => by
    have : (0 : ℝ) < n + 1 + c + 1 := by positivity
    exact_mod_cast this.ne'
  refine tendsto_of_three_term
    (f := fun n (phi : ℝ) => associatedMeixnerPollaczek ((lam + 1) / 2) phi c n
      (-x / (2 * sin (phi : ℂ))))
    (g := fun n => associatedLaguerre lam c n x)
    (A := fun n (phi : ℝ) => -x / (((n + 1 + c : ℝ) : ℂ) + 1) +
      2 * (((n + 1 + c : ℝ) : ℂ) + (lam + 1) / 2) * cos (phi : ℂ) / (((n + 1 + c : ℝ) : ℂ) + 1))
    (B := fun n (_ : ℝ) => -((((n + 1 + c : ℝ) : ℂ) + 2 * ((lam + 1) / 2) - 1) /
      (((n + 1 + c : ℝ) : ℂ) + 1)))
    (A' := fun n => -x / (((n + 1 + c : ℝ) : ℂ) + 1) +
      2 * (((n + 1 + c : ℝ) : ℂ) + (lam + 1) / 2) * 1 / (((n + 1 + c : ℝ) : ℂ) + 1))
    (B' := fun n => -((((n + 1 + c : ℝ) : ℂ) + 2 * ((lam + 1) / 2) - 1) /
      (((n + 1 + c : ℝ) : ℂ) + 1))) ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp [associatedMeixnerPollaczek, associatedLaguerre, associated]
  · have hc1 : (c : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < c + 1 := by positivity
      exact_mod_cast this.ne'
    have h := (tendsto_const_nhds (x := -x / ((c : ℂ) + 1))).add
      ((hcos.const_mul (2 * ((c : ℂ) + (lam + 1) / 2))).div_const ((c : ℂ) + 1))
    have hv : -x / ((c : ℂ) + 1) + 2 * ((c : ℂ) + (lam + 1) / 2) * 1 / ((c : ℂ) + 1) =
        associatedLaguerre lam c 1 x := by
      simp only [associatedLaguerre, associated]
      field_simp
      ring
    rw [hv] at h
    refine h.congr' ?_
    filter_upwards [hsin] with phi hphi
    simp only [associatedMeixnerPollaczek, associated]
    field_simp
  · intro n
    exact tendsto_const_nhds.add (((hcos.const_mul _).div_const _))
  · intro n; exact tendsto_const_nhds
  · intro n
    filter_upwards [hsin] with phi hphi
    simp only [associatedMeixnerPollaczek, associated]
    push_cast
    field_simp
    ring
  · intro n
    simp only [associatedLaguerre, associated]
    push_cast
    field_simp
    ring

@[dlmf 18.30.E20]
theorem associatedPollaczek_limit_hermite {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : ℂ) :
    Tendsto (fun lam : ℝ => poch (c + 1) n * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      associatedMeixnerPollaczek lam (Real.pi / 2) c n (x * Real.sqrt lam)) atTop
      (𝓝 (associatedHermite c n x)) := by
  have hsc : sin ((Real.pi : ℂ) / 2) = 1 := Complex.sin_pi_div_two
  have hcc : cos ((Real.pi : ℂ) / 2) = 0 := Complex.cos_pi_div_two
  refine tendsto_of_three_term (f := fun n (lam : ℝ) => poch (c + 1) n * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      associatedMeixnerPollaczek lam (Real.pi / 2) c n (x * Real.sqrt lam))
    (g := fun n => associatedHermite c n x)
    (A := fun _ _ => 2 * x)
    (B := fun n (lam : ℝ) => -(((n : ℂ) + c + 1) * (2 + (n + c) / (lam : ℂ))))
    (A' := fun _ => 2 * x) (B' := fun n => -(((n : ℂ) + c + 1) * 2)) ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp [associatedMeixnerPollaczek, associatedHermite, associated, poch_zero]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with lam hl
    have hs : (Real.sqrt lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne'
    have hc1 : (c : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < c + 1 := by positivity
      exact_mod_cast this.ne'
    simp only [associatedMeixnerPollaczek, associatedHermite, associated, hsc, hcc, poch_one]
    field_simp
    ring
  · intro n; exact tendsto_const_nhds
  · intro n
    simpa only [add_zero] using
      (((tendsto_const_div_ofReal_atTop ((n : ℂ) + c)).const_add 2).const_mul
        ((n : ℂ) + c + 1)).neg
  · intro n
    filter_upwards [eventually_gt_atTop 0] with lam hl
    have hs : (Real.sqrt lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne'
    have hs2 : (lam : ℂ) = (Real.sqrt lam : ℂ) ^ 2 := by
      rw [← ofReal_pow, Real.sq_sqrt hl.le]
    have ht : ((n + 1 + c : ℝ) : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < n + 1 + c + 1 := by positivity
      exact_mod_cast this.ne'
    simp only [associatedMeixnerPollaczek, associated, hsc, hcc, poch_succ, inv_pow]
    rw [hs2]
    push_cast at ht ⊢
    field_simp
    ring
  · intro n
    simp only [associatedHermite, associated]
    push_cast
    ring

/-- `(a+1)_b = (a+b)!/a!` for natural `a`, in factorial form. -/
theorem poch_nat_succ_mul_factorial (a b : ℕ) :
    (a ! : ℂ) * poch ((a : ℂ) + 1) b = ((a + b) ! : ℂ) := by
  rw [poch_nat_succ_eq_choose_mul_factorial]
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rw [Nat.add_sub_cancel_left] at h
  have h' : ((a + b).choose a : ℂ) * a ! * b ! = (a + b)! := by exact_mod_cast h
  linear_combination h'

@[dlmf 18.34.E1]
theorem besselPolynomial_eq_laguerrePolyL (a : ℂ) (n : ℕ) {x : ℂ} (hx : x ≠ 0) :
    besselPolynomial a n x = (n.factorial : ℂ) * (-x / 2) ^ n * laguerreExtended (1 - a - 2 * n) n (2 / x) := by
  unfold besselPolynomial terminatingHG laguerreExtended
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
  rw [Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega, Nat.sub_sub_self hkn]
  have e : (1 - a - 2 * n + ((n - k : ℕ) : ℂ) + 1) = 1 - (n + a - 1) - k := by
    push_cast [Nat.cast_sub hkn]; ring
  rw [e, poch_reflect]
  have p1 := poch_neg_nat_mul_factorial hkn
  have f1 : ((n - k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f2 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpow : (-x / 2) ^ n * (-(2 / x)) ^ (n - k) = (-x / 2) ^ k := by
    rw [show n = k + (n - k) by omega, pow_add, show k + (n - k) - k = n - k by omega, mul_assoc,
      ← mul_pow]
    rw [show -x / 2 * -(2 / x) = 1 by field_simp, one_pow, mul_one]
  have q1 : poch (-(n : ℂ)) k = (-1) ^ k * (n ! : ℂ) / (n - k) ! := by
    field_simp; linear_combination p1
  rw [q1]
  linear_combination (-(n ! : ℂ) * ((-1) ^ k * poch (n + a - 1) k / ((k ! : ℂ) * (n - k) !))) * hpow

@[dlmf 18.34.E2]
theorem reverseBesselPolynomial_eq (n : ℕ) {x : ℂ} (hx : x ≠ 0) :
    reverseBesselPolynomial n x = x ^ n * besselPolynomial 2 n x⁻¹ := by
  unfold reverseBesselPolynomial besselPolynomial terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hp : x ^ n = x ^ (n - k) * x ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  rw [show (n : ℂ) + 2 - 1 = n + 1 by ring, hp]
  rw [show -x⁻¹ / 2 = (-1 / 2 : ℂ) * x⁻¹ by ring, mul_pow, inv_pow]
  field_simp

/-- Coefficients of the Bessel polynomial in powers of `-x/2`. -/
def besselCoeff (a : ℂ) (m k : ℕ) : ℂ :=
  poch (-(m : ℂ)) k * poch ((m : ℂ) + a - 1) k / k.factorial

/-- The termwise form of the Bessel polynomial recurrence. -/
theorem besselCoeff_rec (a : ℂ) (n j : ℕ) :
    2 * (n + a) * (2 * n + a) * besselCoeff a (n + 2) (j + 1) =
      -2 * ((2 * n + a + 2) * (2 * n + a + 1) * (2 * n + a)) * besselCoeff a (n + 1) j +
        2 * (a - 2) * (2 * n + a + 1) * besselCoeff a (n + 1) (j + 1) +
        2 * (n + 1) * (2 * n + a + 2) * besselCoeff a n (j + 1) := by
  set X := poch (-(n : ℂ) - 1) j with hX
  set Y := poch ((n : ℂ) + a) j with hY
  have e1 : poch (-((n + 2 : ℕ) : ℂ)) (j + 1) = (-(n : ℂ) - 2) * X := by
    rw [poch_succ_left, hX]; push_cast; congr 1 <;> ring_nf
  have e2 : poch (-((n + 1 : ℕ) : ℂ)) j = X := by rw [hX]; push_cast; congr 1; ring_nf
  have e3 : poch (-((n + 1 : ℕ) : ℂ)) (j + 1) = X * (-(n : ℂ) - 1 + j) := by
    rw [poch_succ, hX]; push_cast; congr 1 <;> ring_nf
  have e4 : ((n : ℂ) + 1) * poch (-(n : ℂ)) (j + 1) =
      -(X * (-(n : ℂ) - 1 + j) * (-(n : ℂ) + j)) := by
    have h1 := poch_succ_left (-(n : ℂ) - 1) (j + 1)
    have h2 := poch_succ (-(n : ℂ) - 1) j
    have h3 := poch_succ (-(n : ℂ) - 1) (j + 1)
    rw [show -(n : ℂ) - 1 + 1 = -(n : ℂ) by ring] at h1
    rw [← hX] at h2
    push_cast at h3
    linear_combination h1 - h3 - (-(n : ℂ) + j) * h2
  have f1 : ((n : ℂ) + a) * poch (((n + 2 : ℕ) : ℂ) + a - 1) (j + 1) =
      Y * ((n : ℂ) + a + j) * ((n : ℂ) + a + (j + 1)) := by
    have h1 := poch_succ_left ((n : ℂ) + a) (j + 1)
    have h2 := poch_succ ((n : ℂ) + a) (j + 1)
    have h3 := poch_succ ((n : ℂ) + a) j
    rw [← hY] at h3
    push_cast at h2 ⊢
    rw [show (n : ℂ) + 2 + a - 1 = (n : ℂ) + a + 1 by ring, ← h1, h2, h3]
  have f2 : poch (((n + 1 : ℕ) : ℂ) + a - 1) j = Y := by rw [hY]; push_cast; congr 1; ring_nf
  have f3 : poch (((n + 1 : ℕ) : ℂ) + a - 1) (j + 1) = Y * ((n : ℂ) + a + j) := by
    rw [poch_succ, ← f2]; push_cast; ring_nf
  have f4 : poch ((n : ℂ) + a - 1) (j + 1) = ((n : ℂ) + a - 1) * Y := by
    rw [poch_succ_left, hY]; congr 1; ring_nf
  unfold besselCoeff
  rw [e1, e2, e3, f2, f3, f4, Nat.factorial_succ]
  have hj : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hj1 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  set P0 := poch (-(n : ℂ)) (j + 1)
  set P1 := poch (((n + 2 : ℕ) : ℂ) + a - 1) (j + 1)
  push_cast
  field_simp
  linear_combination ((2 * (n : ℂ) + a) * (-(n : ℂ) - 2) * X) * f1 -
    ((2 * (n : ℂ) + a + 2) * ((n : ℂ) + a - 1) * Y) * e4


/-- The Bessel polynomial as a sum over any sufficiently long range. -/
theorem besselPolynomial_eq_sum (a : ℂ) {m M : ℕ} (hM : m + 1 ≤ M) (x : ℂ) :
    besselPolynomial a m x = ∑ k ∈ Finset.range M, besselCoeff a m k * (-x / 2) ^ k := by
  unfold besselPolynomial terminatingHG besselCoeff
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
  obtain ⟨d, rfl⟩ : ∃ d, M = m + 1 + d := ⟨M - (m + 1), by omega⟩
  conv_rhs => rw [Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range d) (fun k _ => by
    rw [poch_neg_nat_eq_zero (by omega)]; simp), add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The constant coefficient. -/
theorem besselCoeff_zero (a : ℂ) (m : ℕ) : besselCoeff a m 0 = 1 := by
  simp [besselCoeff, poch_zero]

/-- Coefficients beyond the degree vanish. -/
theorem besselCoeff_eq_zero (a : ℂ) {m k : ℕ} (hk : m < k) : besselCoeff a m k = 0 := by
  simp [besselCoeff, poch_neg_nat_eq_zero hk]

@[dlmf 18.34.E4]
theorem besselPolynomial_recurrence (a : ℂ) (n : ℕ) (x : ℂ) :
    2 * (n + a) * (2 * n + a) * besselPolynomial a (n + 2) x =
      ((2 * n + a + 2) * (2 * n + a + 1) * (2 * n + a) * x +
        2 * (a - 2) * (2 * n + a + 1)) * besselPolynomial a (n + 1) x +
      2 * (n + 1) * (2 * n + a + 2) * besselPolynomial a n x := by
  set w := -x / 2 with hw
  have hx : x = -2 * w := by rw [hw]; ring
  rw [besselPolynomial_eq_sum a (show n + 2 + 1 ≤ n + 3 by omega),
    besselPolynomial_eq_sum a (show n + 1 + 1 ≤ n + 3 by omega),
    besselPolynomial_eq_sum a (show n + 1 ≤ n + 3 by omega)]
  -- `x` times the middle sum, shifted
  have hshift : x * ∑ k ∈ Finset.range (n + 3), besselCoeff a (n + 1) k * w ^ k =
      -2 * ∑ j ∈ Finset.range (n + 2), besselCoeff a (n + 1) j * w ^ (j + 1) := by
    rw [hx, Finset.sum_range_succ, besselCoeff_eq_zero a (by omega : n + 1 < n + 2), zero_mul,
      add_zero, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [show ((2 * n + a + 2) * (2 * n + a + 1) * (2 * n + a) * x + 2 * (a - 2) * (2 * n + a + 1)) *
      ∑ k ∈ Finset.range (n + 3), besselCoeff a (n + 1) k * w ^ k =
      (2 * n + a + 2) * (2 * n + a + 1) * (2 * n + a) *
        (x * ∑ k ∈ Finset.range (n + 3), besselCoeff a (n + 1) k * w ^ k) +
      2 * (a - 2) * (2 * n + a + 1) *
        ∑ k ∈ Finset.range (n + 3), besselCoeff a (n + 1) k * w ^ k by ring, hshift]
  rw [Finset.sum_range_succ' _ (n + 2), Finset.sum_range_succ' _ (n + 2),
    Finset.sum_range_succ' _ (n + 2)]
  simp only [besselCoeff_zero, pow_zero, mul_one]
  have key : ∀ j ∈ Finset.range (n + 2),
      2 * (n + a) * (2 * n + a) * (besselCoeff a (n + 2) (j + 1) * w ^ (j + 1)) =
        (2 * n + a + 2) * (2 * n + a + 1) * (2 * n + a) *
          (-2 * (besselCoeff a (n + 1) j * w ^ (j + 1))) +
        2 * (a - 2) * (2 * n + a + 1) * (besselCoeff a (n + 1) (j + 1) * w ^ (j + 1)) +
        2 * (n + 1) * (2 * n + a + 2) * (besselCoeff a n (j + 1) * w ^ (j + 1)) := by
    intro j _
    have := besselCoeff_rec a n j
    linear_combination (w ^ (j + 1)) * this
  rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

@[dlmf 18.34.E7]
theorem besselPolynomial_differential_equation (a : ℂ) (n : ℕ) (x : ℂ) :
    x ^ 2 * deriv (deriv (besselPolynomial a n)) x + (a * x + 2) * deriv (besselPolynomial a n) x -
      n * (n + a - 1) * besselPolynomial a n x = 0 := by
  set c : ℕ → ℂ := fun k =>
    poch (-(n : ℂ)) k * poch (n + a - 1) k * (-1 / 2) ^ k / (k.factorial : ℂ)
  set p : ℂ[X] := ∑ k ∈ Finset.range (n + 1), C (c k) * X ^ k
  have hp : besselPolynomial a n = fun x => p.eval x := by
    funext x
    unfold besselPolynomial terminatingHG
    simp only [p, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, c, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show -x / 2 = (-1 / 2) * x by ring, mul_pow]; ring
  have hcoeff : ∀ j, p.coeff j = c j := by
    intro j
    simp only [p, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · simp only [Finset.mem_range, not_lt] at h
      simp [c, poch_neg_nat_eq_zero (by omega : n < j)]
  have hc : ∀ k, 2 * (k + 1) * c (k + 1) = -((k - n) * (k + n + a - 1)) * c k := by
    intro k
    simp only [c, poch_succ, pow_succ, Nat.factorial_succ]
    have : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    push_cast
    field_simp
    ring
  have hQ : X ^ 2 * derivative (derivative p) + (C a * X + 2) * derivative p -
      C ((n : ℂ) * (n + a - 1)) * p = 0 := by
    ext k
    have e2 : (2 : ℂ[X]) = C 2 := rfl
    rw [coeff_zero, e2, show (C a * X + C 2) * derivative p =
      C a * (X ^ 1 * derivative p) + C 2 * derivative p by ring]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow_mul', coeff_derivative,
      hcoeff]
    rcases k with _ | _ | k
    · have := hc 0
      simp only [zero_add, Nat.reduceLeDiff, ↓reduceIte]
      push_cast at this ⊢
      linear_combination this
    · have := hc 1
      simp only [zero_add, Nat.reduceLeDiff, ↓reduceIte, Nat.sub_self]
      push_cast at this ⊢
      linear_combination this
    · have := hc (k + 2)
      simp only [show 2 ≤ k + 1 + 1 by omega, show 1 ≤ k + 1 + 1 by omega, ↓reduceIte,
        show k + 1 + 1 - 2 = k by omega, show k + 1 + 1 - 1 = k + 1 by omega]
      push_cast at this ⊢
      linear_combination this
  have hd : deriv (besselPolynomial a n) = fun x => (derivative p).eval x := by
    rw [hp]; funext x; exact Polynomial.deriv p
  rw [hd, hp]
  simp only [Polynomial.deriv]
  have := congrArg (eval x) hQ
  simpa [eval_add, eval_sub, eval_mul] using this

section FiniteBesselOrthogonality

open Set

set_option maxHeartbeats 1000000

/-- A reciprocal Gamma moment, with integrability, from the reciprocal substitution. -/
theorem reciprocal_gamma_moment {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1 : ℂ) * exp (-2 / x)) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (-s - 1 : ℂ) * exp (-2 / x)) =
      (2 : ℂ) ^ (-(s : ℂ)) * Gamma (s : ℂ) := by
  let g : ℝ → ℝ := fun u => u ^ (s - 1) * Real.exp (-(2 * u))
  have hg : IntegrableOn g (Ioi 0) := by
    simpa only [g, Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := 2)
        (by linarith) one_pos (by norm_num))
  have he (x : ℝ) (hx : 0 < x) :
      (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) * g (x ^ (-1 : ℝ)) =
        x ^ (-s - 1) * Real.exp (-2 / x) := by
    dsimp only [g]
    rw [show (-1 : ℝ) - 1 = -2 by ring, abs_neg, abs_one, one_mul,
      Real.rpow_neg_one, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le,
      ← mul_assoc, ← Real.rpow_add hx]
    congr 2 <;> ring
  -- Mathlib's reciprocal-power substitution transfers integrability as well as the integral.
  have hi := (integrableOn_Ioi_comp_rpow_iff g (p := (-1 : ℝ)) (by norm_num)).mpr hg
  simp only [smul_eq_mul] at hi
  have hi' := hi.congr_fun he measurableSet_Ioi
  have hreal : (∫ x : ℝ in Ioi 0, x ^ (-s - 1) * Real.exp (-2 / x)) =
      (2 : ℝ) ^ (-s) * Real.Gamma s := by
    have h := integral_comp_rpow_Ioi g (p := (-1 : ℝ)) (by norm_num)
    simp only [smul_eq_mul] at h
    rw [setIntegral_congr_fun measurableSet_Ioi he] at h
    rw [h, Real.integral_rpow_mul_exp_neg_mul_Ioi hs (by norm_num)]
    rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num)]
  have hc (x : ℝ) (hx : 0 < x) :
      (x : ℂ) ^ (-s - 1 : ℂ) * exp (-2 / x) =
        ((x ^ (-s - 1) * Real.exp (-2 / x) : ℝ) : ℂ) := by
    rw [show (-(s : ℂ) - 1) = ((-s - 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx.le]
    push_cast
    rfl
  refine ⟨hi'.ofReal.congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => (hc x hx).symm)), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hc, integral_complex_ofReal, hreal,
    ofReal_mul, ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), ← Gamma_ofReal]
  norm_cast

/-- A monomial moment of the finite Bessel weight. -/
theorem bessel_weight_moment {a : ℝ} (j : ℕ) (ha : a + j < 1) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ j *
      (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ j *
      (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)) =
      (2 : ℂ) ^ (a + j - 1 : ℂ) * Gamma (1 - a - j : ℂ) := by
  have hs : 0 < 1 - a - j := by linarith
  have h := reciprocal_gamma_moment hs
  have he (x : ℝ) (hx : 0 < x) : (x : ℂ) ^ j *
      (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ) =
      (x : ℂ) ^ (-(1 - a - j : ℝ) - 1 : ℂ) * exp (-2 / x) := by
    rw [ofReal_mul]
    rw [show ((Real.rpow x (a - 2) : ℝ) : ℂ) = (x : ℂ) ^ ((a : ℂ) - 2) by
      convert ofReal_cpow hx.le (a - 2) using 1 ; push_cast ; rfl,
      ofReal_exp]
    push_cast
    rw [← cpow_natCast, ← mul_assoc, ← cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]
    congr 2
    ring
  refine ⟨h.1.congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => (he x hx).symm)), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he, h.2]
  push_cast
  congr 2 ; ring

/-- Binomial form of the finite Bessel polynomial. -/
theorem bessel_binomial_sum (a : ℂ) (n : ℕ) (x : ℂ) :
    besselPolynomial a n x = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * poch (n + a - 1) k * (x / 2) ^ k := by
  unfold besselPolynomial terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
  apply Finset.sum_congr rfl
  intro k _
  rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [neg_div, neg_pow]
  have hs : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  calc
    _ = ((-1 : ℂ) ^ k * (-1) ^ k) * (n.choose k : ℂ) * poch (n + a - 1) k * (x / 2) ^ k := by
      field_simp
      simp only [one_pow, neg_pow (x / 2 : ℂ) k]
      ring
    _ = _ := by rw [hs]; ring

/-- Orthogonal moments of a Bessel polynomial; Vandermonde supplies the finite cancellation. -/
theorem bessel_monomial_moment {a : ℝ} (m j : ℕ) (ha : a + j + m < 1) :
    IntegrableOn (fun x : ℝ => besselPolynomial a m x * (x : ℂ) ^ j *
      (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0, besselPolynomial a m x * (x : ℂ) ^ j *
      (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)) =
      (2 : ℂ) ^ (a + j - 1 : ℂ) * Gamma (1 - a - j - m : ℂ) * poch (-(j : ℂ)) m := by
  let W : ℝ → ℂ := fun x => (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)
  have hpos : 0 < 1 - a - j - m := by linarith
  have heq : (fun x : ℝ => besselPolynomial a m x * (x : ℂ) ^ j * W x) =
      fun x : ℝ => ∑ k ∈ Finset.range (m + 1),
        ((m.choose k : ℂ) * poch (m + (a : ℂ) - 1) k / 2 ^ k) * ((x : ℂ) ^ (j + k) * W x) := by
    funext x
    rw [bessel_binomial_sum]
    simp only [Finset.sum_mul, div_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_add]
    ring
  have hM (k : ℕ) (hk : k ∈ Finset.range (m + 1)) :=
    bessel_weight_moment (a := a) (j + k) (by
      have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      push_cast
      have hkr : (k : ℝ) ≤ m := by exact_mod_cast hkm
      linarith)
  refine ⟨?_, ?_⟩
  · change IntegrableOn (fun x : ℝ => besselPolynomial a m x * (x : ℂ) ^ j * W x) (Ioi 0)
    rw [heq]
    exact integrable_finsetSum _ fun k hk => (hM k hk).1.const_mul _
  · change (∫ x : ℝ in Ioi 0, besselPolynomial a m x * (x : ℂ) ^ j * W x) = _
    rw [heq, integral_finsetSum _ fun k hk => (hM k hk).1.const_mul _]
    simp only [integral_const_mul]
    have hterm (k : ℕ) (hk : k ∈ Finset.range (m + 1)) :
        ((m.choose k : ℂ) * poch (m + (a : ℂ) - 1) k / 2 ^ k) *
          (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (j + k) * W x) =
        ((2 : ℂ) ^ (a + j - 1 : ℂ) * Gamma (1 - a - j - m : ℂ)) *
          ((m.choose k : ℂ) * poch (m + (a : ℂ) - 1) k * poch (1 - a - j - m : ℂ) (m - k)) := by
      have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [(hM k hk).2]
      have hg : Gamma (1 - a - (j + k : ℕ) : ℂ) =
          poch (1 - a - j - m : ℂ) (m - k) * Gamma (1 - a - j - m : ℂ) := by
        have hp : 0 < (1 - (a : ℂ) - j - m).re := by simpa using hpos
        have h := Complex.Gamma_add_nat_div_Gamma_eq (n := m - k) (1 - a - j - m : ℂ)
          (not_neg_nat_of_re_pos hp)
        have hΓ := Gamma_ne_zero_of_re_pos hp
        rw [div_eq_iff hΓ] at h
        convert h using 1 ; push_cast [Nat.cast_sub hkm] ; congr 1 ; ring
      have hp : (2 : ℂ) ^ (a + (j + k : ℕ) - 1 : ℂ) = (2 : ℂ) ^ (a + j - 1 : ℂ) * 2 ^ k := by
        rw [show (a : ℂ) + (j + k : ℕ) - 1 = ((a : ℂ) + j - 1) + k by push_cast; ring,
          cpow_add _ _ two_ne_zero, cpow_natCast]
      rw [hg, hp]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← poch_add_eq_sum]
    rw [show (m : ℂ) + a - 1 + (1 - a - j - m) = -j by ring]

/-- Product moments reduce to the top monomial after finite orthogonality. -/
theorem bessel_product_integral_of_le {a : ℝ} (m n : ℕ) (hnm : n ≤ m) (ha : a + 2 * m < 1) :
    (∫ x : ℝ in Ioi 0, besselPolynomial a m x * besselPolynomial a n x *
      (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)) =
      if m = n then (2 : ℂ) ^ (a - 1 : ℂ) * Gamma (1 - a - 2 * n : ℂ) *
        poch (2 - a - 2 * n : ℂ) n * n ! else 0 := by
  let W : ℝ → ℂ := fun x => (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)
  have heq : (fun x : ℝ => besselPolynomial a m x * besselPolynomial a n x * W x) =
      fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℂ) * poch (n + (a : ℂ) - 1) k / 2 ^ k) *
          (besselPolynomial a m x * (x : ℂ) ^ k * W x) := by
    funext x
    conv_lhs => arg 1; arg 2; rw [bessel_binomial_sum]
    simp only [Finset.mul_sum, Finset.sum_mul, div_pow]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hM (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :=
    bessel_monomial_moment (a := a) m k (by
      have hkm : (k : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hnm
      linarith)
  change (∫ x : ℝ in Ioi 0, besselPolynomial a m x * besselPolynomial a n x * W x) = _
  rw [heq, integral_finsetSum _ fun k hk => (hM k hk).1.const_mul _]
  simp only [integral_const_mul]
  rw [Finset.sum_congr rfl (g := fun k =>
    ((n.choose k : ℂ) * poch (n + (a : ℂ) - 1) k / 2 ^ k) *
      ((2 : ℂ) ^ (a + k - 1 : ℂ) * Gamma (1 - a - k - m : ℂ) * poch (-(k : ℂ)) m))
    (fun k hk => by rw [(hM k hk).2])]
  split_ifs with hmn
  · subst m
    rw [Finset.sum_eq_single n]
    · simp only [Nat.choose_self, Nat.cast_one, one_mul]
      rw [poch_neg_coe_nat, Nat.descFactorial_self]
      have hp : (2 : ℂ) ^ (a + n - 1 : ℂ) = (2 : ℂ) ^ (a - 1 : ℂ) * 2 ^ n := by
        rw [show (a : ℂ) + n - 1 = ((a : ℂ) - 1) + n by ring,
          cpow_add _ _ two_ne_zero, cpow_natCast]
      have hpoch : poch (2 - a - 2 * n : ℂ) n = (-1 : ℂ) ^ n * poch (n + (a : ℂ) - 1) n := by
        convert poch_reflect ((n : ℂ) + a - 1) n using 1 ; congr 1 ; ring
      rw [hp, hpoch]
      field_simp
      ; ring
    · intro k hk hkn
      have hlt : k < n := by have := Finset.mem_range.mp hk; omega
      rw [poch_neg_nat_eq_zero hlt]
      simp
    · simp
  · apply Finset.sum_eq_zero
    intro k hk
    have hlt : k < m := by have := Finset.mem_range.mp hk; omega
    rw [poch_neg_nat_eq_zero hlt]
    simp

/-- The Pochhammer cancellation in the finite Bessel squared norm. -/
theorem bessel_norm_pochhammer (s : ℂ) (n : ℕ) :
    s * poch (s + 1) n * poch (s + n + 1) n = (s + 2 * n) * poch s (2 * n) := by
  calc
    _ = s * poch (s + 1) (n + n) := by
      rw [poch_add, show s + 1 + (n : ℂ) = s + n + 1 by ring]
      ring
    _ = _ := by
      rw [← two_mul n, ← poch_succ_left, poch_succ]
      push_cast
      ring

/-- Gamma form of the finite Bessel norm cancellation. -/
theorem bessel_norm_gamma {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Gamma (s : ℂ) * poch (s + 1 : ℂ) n / Gamma (s + 2 * n : ℂ) =
      (s + 2 * n : ℂ) / ((s : ℂ) * poch (s + n + 1 : ℂ) n) := by
  have hp : 0 < (s : ℂ).re := by simpa using hs
  have hG := Gamma_ne_zero_of_re_pos hp
  have hP : poch (s : ℂ) (2 * n) ≠ 0 := poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hp) _
  have hQ : poch (s + n + 1 : ℂ) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; positivity)) _
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hg : Gamma (s + 2 * n : ℂ) = poch (s : ℂ) (2 * n) * Gamma (s : ℂ) := by
    have h := Gamma_add_nat_div_Gamma_eq (n := 2 * n) (s : ℂ) (not_neg_nat_of_re_pos hp)
    rw [div_eq_iff hG] at h
    push_cast at h
    exact h
  rw [hg]
  field_simp
  simpa only [mul_comm] using bessel_norm_pochhammer (s : ℂ) n

@[dlmf 18.34.E5_5]
theorem besselPolynomial_finite_orthogonality {a : ℝ} (m n : ℕ) (ha : a < 1 - 2 * max m n) :
    (2 : ℂ) ^ (1 - (a : ℂ)) / Gamma (1 - (a : ℂ)) *
      (∫ x : ℝ in Set.Ioi 0, besselPolynomial a m x * besselPolynomial a n x *
        (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)) =
      if m = n then (1 - a) / (1 - a - 2 * (n : ℂ)) * n.factorial / poch (2 - a - n) n else 0 := by
  have hm : a + 2 * m < 1 := by
    have hmax : (m : ℝ) ≤ max m n := by exact_mod_cast le_max_left m n
    linarith
  have hn : a + 2 * n < 1 := by
    have hmax : (n : ℝ) ≤ max m n := by exact_mod_cast le_max_right m n
    linarith
  have hi : (∫ x : ℝ in Ioi 0, besselPolynomial a m x * besselPolynomial a n x *
      (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)) =
      if m = n then (2 : ℂ) ^ (a - 1 : ℂ) * Gamma (1 - a - 2 * n : ℂ) *
        poch (2 - a - 2 * n : ℂ) n * n ! else 0 := by
    rcases le_total n m with hnm | hmn
    · exact bessel_product_integral_of_le m n hnm hm
    · have heq : (∫ x : ℝ in Ioi 0, besselPolynomial a m x * besselPolynomial a n x *
          (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)) =
        ∫ x : ℝ in Ioi 0, besselPolynomial a n x * besselPolynomial a m x *
          (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by dsimp only; ring
      rw [heq, bessel_product_integral_of_le n m hmn hn]
      by_cases he : m = n
      · subst n; simp
      · simp only [ite_eq_right he, ite_eq_right (Ne.symm he)]
  rw [hi]
  split_ifs with hmn
  · subst m
    have hs : 0 < 1 - a - 2 * n := by linarith
    have hpow : (2 : ℂ) ^ (1 - (a : ℂ)) * (2 : ℂ) ^ (a - 1 : ℂ) = 1 := by
      rw [← cpow_add _ _ two_ne_zero, sub_add_sub_cancel, sub_self, cpow_zero]
    have hratio := bessel_norm_gamma hs n
    push_cast at hratio
    have h0 : (1 - (a : ℂ) - 2 * n) + 1 = 2 - a - 2 * n := by ring
    have h1 : (1 - (a : ℂ) - 2 * n) + 2 * n = 1 - a := by ring
    have h2 : (1 - (a : ℂ) - 2 * n) + n + 1 = 2 - a - n := by ring
    rw [h0, h1, h2] at hratio
    calc
      _ = ((2 : ℂ) ^ (1 - (a : ℂ)) * (2 : ℂ) ^ (a - 1 : ℂ)) *
          (Gamma (1 - a - 2 * n : ℂ) * poch (2 - a - 2 * n : ℂ) n / Gamma (1 - a : ℂ)) * n ! := by ring
      _ = _ := by rw [hpow, one_mul, hratio]; simp only [div_eq_mul_inv, mul_inv]; ring
  · simp

end FiniteBesselOrthogonality

@[dlmf 18.34.E8]
theorem jacobi_limit_besselPolynomial (a : ℂ) (n : ℕ) (x : ℂ) :
    Tendsto (fun α : ℝ => jacobiPolyP α (a - α - 2) n (1 + α * x) / jacobiPolyP α (a - α - 2) n 1)
        atTop
      (𝓝 (besselPolynomial a n x)) := by
  unfold besselPolynomial terminatingHG
  have hlim : Tendsto (fun α : ℝ => ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k * poch (n + a - 1) k * (-x / 2) ^ k / k ! *
        (poch (1 + (α : ℂ)) k / (α : ℂ) ^ k)⁻¹) atTop
      (𝓝 (∑ k ∈ Finset.range (n + 1),
        poch (-(n : ℂ)) k * poch (n + a - 1) k * (-x / 2) ^ k / k ! * 1⁻¹)) := by
    apply tendsto_finsetSum
    intro k _
    exact ((tendsto_poch_add_div_pow 1 k).inv₀ one_ne_zero).const_mul _
  simp only [inv_one, mul_one] at hlim
  refine (hlim.congr' ?_).trans ?_
  · filter_upwards [eventually_gt_atTop 0] with α hα
    have hα' : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα.ne'
    have hc : ∀ k : ℕ, (α : ℂ) + 1 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
    have hp : poch ((α : ℂ) + 1) n / n ! ≠ 0 :=
      div_ne_zero (poch_ne_zero_of_not_neg_nat hc n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
    have h0 : ₂F₁ (-(n : ℂ)) (n + α + (a - α - 2) + 1) (α + 1) (0 : ℂ) = 1 := by
      rw [ordinaryHypergeometric_eq_sum_neg_nat, Finset.sum_range_succ']
      simp [gaussHGCoeff, poch_zero]
    unfold jacobiPolyP
    rw [show ((1 : ℂ) - 1) / 2 = 0 by ring, h0, mul_one, mul_div_cancel_left₀ _ hp,
      ordinaryHypergeometric_eq_sum_neg_nat]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hpk : poch ((α : ℂ) + 1) k ≠ 0 := poch_ne_zero_of_not_neg_nat hc k
    unfold gaussHGCoeff
    rw [show (n : ℂ) + α + (a - α - 2) + 1 = n + a - 1 by ring,
      show (1 - (1 + (α : ℂ) * x)) / 2 = α * (-x / 2) by ring, mul_pow, add_comm (1 : ℂ)]
    field_simp
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
    rfl

@[dlmf 18.35.E2_5]
theorem pollaczek_reflection (lam a b : ℂ) (c : ℝ) (n : ℕ) (x : ℂ) :
    pollaczek lam a b c n (-x) = (-1 : ℂ) ^ n * pollaczek lam a (-b) c n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pollaczek, associated]
  | one => simp [pollaczek, associated]; ring
  | more n ih0 ih1 =>
    change (2 * ((n + 1 + c : ℝ) + lam + a) / ((n + 1 + c : ℝ) + 1) * (-x) +
      2 * b / ((n + 1 + c : ℝ) + 1)) * pollaczek lam a b c (n + 1) (-x) -
      (((n + 1 + c : ℝ) + 2 * lam - 1) / ((n + 1 + c : ℝ) + 1)) * pollaczek lam a b c n (-x) = _
    rw [ih0, ih1]
    simp only [pollaczek, associated, pow_succ]
    ring

/-- The Pollaczek polynomial of degree zero. -/
theorem pollaczek_zero (lam a b x : ℂ) : pollaczek lam a b 0 0 x = 1 := by
  simp [pollaczek, associated]

/-- The Pollaczek polynomial of degree one. -/
theorem pollaczek_one (lam a b x : ℂ) :
    pollaczek lam a b 0 1 x = 2 * (lam + a) * x + 2 * b := by
  simp [pollaczek, associated]

/-- The three-term recurrence of the Pollaczek polynomials, DLMF 18.35.2. -/
theorem pollaczek_recurrence (lam a b x : ℂ) (n : ℕ) :
    (n + 2 : ℂ) * pollaczek lam a b 0 (n + 2) x =
      (2 * (n + 1 + lam + a) * x + 2 * b) * pollaczek lam a b 0 (n + 1) x -
        (n + 2 * lam) * pollaczek lam a b 0 n x := by
  have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  change (n + 2 : ℂ) * ((2 * ((n + 1 + (0 : ℝ) : ℝ) + lam + a) / ((n + 1 + (0 : ℝ) : ℝ) + 1) * x +
      2 * b / ((n + 1 + (0 : ℝ) : ℝ) + 1)) * pollaczek lam a b 0 (n + 1) x -
      (((n + 1 + (0 : ℝ) : ℝ) + 2 * lam - 1) / ((n + 1 + (0 : ℝ) : ℝ) + 1)) *
        pollaczek lam a b 0 n x) = _
  have hn' : (2 : ℂ) + n ≠ 0 := by rw [add_comm]; exact hn
  push_cast
  rw [show (n : ℂ) + 1 + 0 + 1 = n + 2 by ring, show (n : ℂ) + 1 + 0 = n + 1 by ring]
  field_simp
  ring

/-- Pollaczek polynomials at `cos θ` are the coefficients of
`G_{λ - iΦ}(e^{iθ}X) G_{λ + iΦ}(e^{-iθ}X)`, `Φ = (a cos θ + b)/sin θ`. -/
theorem pollaczek_eq_coeff_binomProductSeries (lam a b : ℂ) {θ : ℂ} (hθ : sin θ ≠ 0) (n : ℕ) :
    pollaczek lam a b 0 n (cos θ) = PowerSeries.coeff n (binomProductSeries
      (lam - I * ((a * cos θ + b) / sin θ)) (lam + I * ((a * cos θ + b) / sin θ))
      (exp (I * θ))) := by
  obtain ⟨hcos, hsin⟩ := exp_I_mul_add_recip θ
  set Φ := (a * cos θ + b) / sin θ with hΦ
  have hΦs : Φ * sin θ = a * cos θ + b := by rw [hΦ]; field_simp
  refine eq_coeff_binomProductSeries (f := fun n => pollaczek lam a b 0 n (cos θ))
    (Complex.exp_ne_zero _) (pollaczek_zero _ _ _ _) ?_ ?_ n
  · rw [pollaczek_one]
    linear_combination (-lam) * hcos + (I * Φ) * hsin + (2 * Φ * sin θ) * I_sq - 2 * hΦs
  · intro n
    rw [pollaczek_recurrence]
    set P := pollaczek lam a b 0 (n + 1) (cos θ)
    linear_combination (-(n + 1 + lam : ℂ) * P) * hcos + (I * Φ * P) * hsin +
      (2 * Φ * sin θ * P) * I_sq - (2 * P) * hΦs

@[dlmf 18.35.E4]
theorem pollaczek_finite_sum (lam a b : ℂ) (n : ℕ) {θ : ℂ} (hθ : sin θ ≠ 0) :
    pollaczek lam a b 0 n (cos θ) = ∑ k ∈ Finset.range (n + 1),
      poch (lam + I * (a * cos θ + b) / sin θ) k / k.factorial *
      (poch (lam - I * (a * cos θ + b) / sin θ) (n - k) / (n - k).factorial) *
      exp (I * ((n : ℂ) - 2 * k) * θ) := by
  rw [pollaczek_eq_coeff_binomProductSeries lam a b hθ, coeff_binomProductSeries,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega, Nat.sub_sub_self hkn, ← Complex.exp_neg,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  have he : (((n - k : ℕ) : ℂ) * (I * θ) + (k : ℂ) * -(I * θ)) = I * ((n : ℂ) - 2 * k) * θ := by
    push_cast [Nat.cast_sub hkn]; ring
  rw [he]
  have hd : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd' : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [mul_div_assoc, mul_div_assoc]
  field_simp

@[dlmf 18.35.E7]
theorem pollaczek_generating_function (lam a b : ℂ) (θ : ℝ) (hθ : Real.sin θ ≠ 0) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => pollaczek lam a b 0 n (Real.cos θ) * z ^ n)
      ((1 - z * exp (I * θ)) ^ (-lam + I * (a * Real.cos θ + b) / Real.sin θ) *
       (1 - z * exp (-I * θ)) ^ (-lam - I * (a * Real.cos θ + b) / Real.sin θ)) := by
  have hθ' : sin (θ : ℂ) ≠ 0 := by rw [← Complex.ofReal_sin]; exact_mod_cast hθ
  set u := exp (I * θ) with hu
  have hu1 : ‖u‖ = 1 := by rw [hu, mul_comm, Complex.norm_exp_ofReal_mul_I]
  have h1 : ‖u * z‖ < 1 := by rwa [norm_mul, hu1, one_mul]
  have h2 : ‖u⁻¹ * z‖ < 1 := by rwa [norm_mul, norm_inv, hu1, inv_one, one_mul]
  have h := hasSum_coeff_binomProductSeries_mul_pow (lam - I * ((a * cos θ + b) / sin θ))
    (lam + I * ((a * cos θ + b) / sin θ)) h1 h2
  rw [show u⁻¹ = exp (-I * θ) by rw [hu, ← Complex.exp_neg]; ring_nf] at h
  push_cast
  convert h using 1
  · funext n
    rw [pollaczek_eq_coeff_binomProductSeries lam a b hθ']
  · rw [mul_comm z, mul_comm z]
    congr 2 <;> ring

@[dlmf 18.35.E8]
theorem pollaczek_eq_ultrasphPoly {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    pollaczek lam 0 0 0 n x = ultrasphPoly lam n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pollaczek, associated]
  | one => simp [pollaczek, associated, ultrasphPoly_one_eq hlam]
  | more n ih0 ih1 =>
    have hr := ultrasphPoly_recurrence hlam n x
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    simp only [pollaczek, associated] at ih0 ih1 ⊢
    rw [ih0, ih1]
    push_cast
    simp only [add_zero, mul_zero, zero_div]
    rw [show (n : ℂ) + 1 + 1 = n + 2 by ring]
    field_simp
    linear_combination -hr


@[dlmf 18.35.E9]
theorem pollaczek_eq_meixnerPollaczek {lam : ℂ} (hlam : 0 < lam.re) (phi x : ℂ) (n : ℕ) :
    pollaczek lam 0 (x * sin phi) 0 n (cos phi) = meixnerPollaczek lam phi n x := by
  have hl : lam ≠ 0 := fun h => by simp [h] at hlam
  induction n using Nat.twoStepInduction with
  | zero => simp [pollaczek, associated, meixnerPollaczek, terminatingHG, poch_zero]
  | one =>
    simp [pollaczek, associated, meixnerPollaczek_one hl]
    ring
  | more n ih0 ih1 =>
    have hr := meixnerPollaczek_recurrence hlam phi n x
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    simp only [pollaczek, associated] at ih0 ih1 ⊢
    rw [ih0, ih1]
    push_cast
    simp only [add_zero]
    rw [show (n : ℂ) + 1 + 1 = n + 2 by ring]
    field_simp
    linear_combination -hr

@[dlmf 18.35.E10]
theorem pollaczek_eq_associatedMeixnerPollaczek (lam phi x : ℂ) (c : ℝ) (n : ℕ) :
    pollaczek lam 0 (x * sin phi) c n (cos phi) = associatedMeixnerPollaczek lam phi c n x := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [pollaczek, associatedMeixnerPollaczek, associated]; ring
  | more n ih0 ih1 =>
    change (2 * ((n + 1 + c : ℝ) + lam + 0) / ((n + 1 + c : ℝ) + 1) * cos phi +
      2 * (x * sin phi) / ((n + 1 + c : ℝ) + 1)) * pollaczek lam 0 (x * sin phi) c (n + 1) (cos phi) -
      (((n + 1 + c : ℝ) + 2 * lam - 1) / ((n + 1 + c : ℝ) + 1)) * pollaczek lam 0 (x * sin phi) c n (cos phi) = _
    rw [ih0, ih1]
    simp only [associatedMeixnerPollaczek, associated]
    ring

@[dlmf 18.36.E2]
theorem laguerrePolyL_negative_integer_parameter {n k : ℕ} (hk : k ≤ n) (x : ℂ) :
    laguerreExtended (-(k : ℂ)) n x = (-1 : ℂ) ^ k * (n - k).factorial / n.factorial * x ^ k
        * laguerrePolyL k (n - k) x := by
  have hα : ∀ j : ℕ, (k : ℂ) + 1 ≠ -(j : ℂ) := by
    intro j h
    have : ((k + 1 + j : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
    exact absurd (by exact_mod_cast this : k + 1 + j = 0) (by omega)
  rw [laguerrePolyL_eq_sum hα]
  unfold laguerreExtended
  obtain ⟨N, rfl⟩ : ∃ N, n = k + N := ⟨n - k, by omega⟩
  rw [show k + N + 1 = k + (N + 1) by ring, Finset.sum_range_add, Nat.add_sub_cancel_left]
  have hzero : ∑ j ∈ Finset.range k, poch (-(k : ℂ) + j + 1) (k + N - j) /
      ((j.factorial : ℂ) * (k + N - j).factorial) * (-x) ^ j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjk := Finset.mem_range.mp hj
    have : poch (-(k : ℂ) + j + 1) (k + N - j) = 0 := by
      rw [poch, ascPochhammer_eval_eq_zero_iff]
      refine ⟨k - 1 - j, by omega, ?_⟩
      push_cast [show 1 + j ≤ k by omega, Nat.sub_sub]
      ring
    simp [this]
  rw [hzero, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have e1 : k + N - (k + m) = N - m := by omega
  have e2 : -(k : ℂ) + ((k + m : ℕ) : ℂ) + 1 = (m : ℂ) + 1 := by push_cast; ring
  have e3 : (k : ℂ) + 1 + (m : ℂ) = ((k + m : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [e1, e2, e3]
  have p1 := poch_nat_succ_mul_factorial m (N - m)
  have p2 := poch_nat_succ_mul_factorial (k + m) (N - m)
  rw [show m + (N - m) = N by omega] at p1
  rw [show k + m + (N - m) = k + N by omega] at p2
  have f1 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f2 : ((k + m) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f3 : ((N - m) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f4 : ((k + N) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have q1 : poch ((m : ℂ) + 1) (N - m) = (N ! : ℂ) / m ! := by
    field_simp; linear_combination p1
  have q2 : poch (((k + m : ℕ) : ℂ) + 1) (N - m) = ((k + N) ! : ℂ) / (k + m) ! := by
    field_simp; linear_combination p2
  rw [q1, q2, pow_add, show (-x) ^ k = (-1) ^ k * x ^ k by ring]
  field_simp

/-- The Laguerre polynomial `L_n^{(α)}` is analytic at every point. -/
theorem analyticAt_laguerrePolyL {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    AnalyticAt ℂ (laguerrePolyL α n) x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]; linarith)
  have he : laguerrePolyL α n = fun z => poch (α + 1) n / (n.factorial : ℂ) *
      kummerM (-(n : ℂ)) (α + 1) z := rfl
  rw [he]
  exact analyticAt_const.mul ((hasFPowerSeriesOnBall_kummerM (a := -(n : ℂ)) hc).analyticAt_of_mem
    (by simp))

/-- `L'_{m+1} - L'_m + L_m = 0`. -/
theorem laguerrePolyL_deriv_succ_sub {α : ℂ} (hα : -1 < α.re) (m : ℕ) (x : ℂ) :
    deriv (laguerrePolyL α (m + 1)) x - deriv (laguerrePolyL α m) x + laguerrePolyL α m x = 0 := by
  rcases m with _ | j
  · have h0 : laguerrePolyL α 0 = fun _ => 1 := funext fun x => laguerrePolyL_zero α x
    rw [laguerrePolyL_derivative hα 0, h0, deriv_const, laguerrePolyL_zero]
    simp
  · have hα1 : -1 < (α + 1).re := by simp; linarith
    rw [laguerrePolyL_derivative hα (j + 1), laguerrePolyL_derivative hα j,
        laguerrePolyL_raise_parameter hα j]
    ring

@[dlmf 18.36.E6]
theorem exceptionalLaguerre_orthogonality {k : ℝ} (hk : 0 < k) (m n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exceptionalLaguerre k m x * exceptionalLaguerre k n x * exceptionalLaguerreWeight k x =
      if m = n then (n + 1 + (k : ℂ)) * Gamma (n + (k : ℂ)) / n.factorial else 0 := by
  sorry

@[dlmf 18.36.E7]
theorem exceptionalLaguerre_differential_equation {k : ℝ} (hk : 0 < k) (n : ℕ) {x : ℂ} (hx : x + k ≠ 0) :
    -x * deriv (deriv (exceptionalLaguerre k n)) x + (x - k) / (x + k) *
      ((x + k + 1) * deriv (exceptionalLaguerre k n) x - exceptionalLaguerre k n x) =
      n * exceptionalLaguerre k n x := by
  have hα : -1 < (k : ℂ).re := by simp; linarith
  have hL : ∀ j y,
      HasDerivAt (laguerrePolyL (k : ℂ) j) (deriv (laguerrePolyL (k : ℂ) j) y) y := fun j y =>
    (analyticAt_laguerrePolyL hα j y).differentiableAt.hasDerivAt
  have hL' : ∀ j y,
      HasDerivAt (deriv (laguerrePolyL (k : ℂ) j)) (deriv (deriv (laguerrePolyL (k : ℂ) j)) y) y :=
    fun j y => (analyticAt_laguerrePolyL hα j y).deriv.differentiableAt.hasDerivAt
  rcases n with _ | m
  · have he : exceptionalLaguerre k 0 = fun y : ℂ => -(y + (k : ℂ) + 1) := by
      funext y; simp [exceptionalLaguerre, laguerrePolyL_zero]
    have hd : deriv (exceptionalLaguerre k 0) = fun _ => -1 := by
      rw [he]; funext y
      have := ((hasDerivAt_id y).add_const ((k : ℂ) + 1)).neg
      simpa [add_assoc] using this.deriv
    rw [hd, he, deriv_const]
    push_cast; ring
  · have he : exceptionalLaguerre k (m + 1) = fun y => -(y + k + 1)
      * laguerrePolyL (k : ℂ) (m + 1) y +
        laguerrePolyL (k : ℂ) m y := by
      funext y; simp [exceptionalLaguerre]
    have hd1 : ∀ y, HasDerivAt (exceptionalLaguerre k (m + 1))
        (-laguerrePolyL (k : ℂ) (m + 1) y - (y + k + 1) * deriv (laguerrePolyL (k : ℂ) (m + 1)) y +
          deriv (laguerrePolyL (k : ℂ) m) y) y := by
      intro y
      rw [he]
      have := ((((hasDerivAt_id y).add_const ((k : ℂ) + 1)).neg).mul (hL (m + 1) y)).add (hL m y)
      convert this using 1
      · funext z; simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, id]; ring
      · simp; ring
    have hd : deriv (exceptionalLaguerre k (m + 1)) = fun y =>
        -laguerrePolyL (k : ℂ) (m + 1) y - (y + k + 1) * deriv (laguerrePolyL (k : ℂ) (m + 1)) y +
          deriv (laguerrePolyL (k : ℂ) m) y := funext fun y => (hd1 y).deriv
    have hd2 : deriv (deriv (exceptionalLaguerre k (m + 1))) x =
        -2 * deriv (laguerrePolyL (k : ℂ) (m + 1)) x -
          (x + k + 1) * deriv (deriv (laguerrePolyL (k : ℂ) (m + 1))) x +
          deriv (deriv (laguerrePolyL (k : ℂ) m)) x := by
      rw [hd]
      have h2 : HasDerivAt (fun y => -laguerrePolyL (k : ℂ) (m + 1) y -
          (y + k + 1) * deriv (laguerrePolyL (k : ℂ) (m + 1)) y + deriv (laguerrePolyL (k : ℂ) m) y)
          (-2 * deriv (laguerrePolyL (k : ℂ) (m + 1)) x -
          (x + k + 1) * deriv (deriv (laguerrePolyL (k : ℂ) (m + 1))) x +
          deriv (deriv (laguerrePolyL (k : ℂ) m)) x) x := by
        have := (((hL (m + 1) x).neg.sub (((hasDerivAt_id x).add_const ((k : ℂ) + 1)).mul
          (hL' (m + 1) x))).add (hL' m x))
        convert this using 1
        · funext y; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, id]; ring
        · simp; ring
      exact h2.deriv
    rw [hd2, (hd1 x).deriv, he]
    have E1 := laguerrePolyL_differential_equation hα (m + 1) x
    have E2 := laguerrePolyL_differential_equation hα m x
    have R2 := laguerrePolyL_deriv_succ_sub hα m x
    field_simp
    push_cast at E1 E2 ⊢
    linear_combination (x + k) * (x + k + 1) * E1 - (x + k) * E2 - 2 * x * R2

@[dlmf 18.36.E10]
theorem exceptionalHermite_orthonormal (m n : Option ℕ) :
    ∫ x : ℝ, exceptionalHermite m x * exceptionalHermite n x *
      (Real.exp (-(x ^ 2)) / (4 * x ^ 2 + 2) ^ 2) = if m = n then 1 else 0 := by
  sorry


/-- The auxiliary function `τ(θ) = (a cos θ + b)/sin θ` of the Pollaczek weight (DLMF 18.35.3). -/
@[dlmf 18.35.E3]
def pollaczekTau (a b θ : ℝ) : ℝ := (a * Real.cos θ + b) / Real.sin θ

/-- Angular density, including the Jacobian `sin θ` for `x = cos θ`. -/
@[dlmf 18.35.E6]
def pollaczekAngularWeight (lam a b θ : ℝ) : ℝ :=
  Real.pi⁻¹ * Real.exp ((2 * θ - Real.pi) * pollaczekTau a b θ) *
    (2 * Real.sin θ) ^ (2 * lam - 1) * ‖Gamma (lam + I * pollaczekTau a b θ)‖ ^ 2 * Real.sin θ

@[dlmf 18.35.E5]
theorem pollaczek_orthogonality {lam a b : ℝ} (hlam : 0 < lam) (hab : |b| ≤ a) (m n : ℕ) :
    ∫ θ : ℝ in (0 : ℝ)..Real.pi, pollaczek lam a b 0 m (Real.cos θ) *
      pollaczek lam a b 0 n (Real.cos θ) * pollaczekAngularWeight lam a b θ =
      if m = n then Gamma (2 * (lam : ℂ) + n) / (n.factorial * (lam + a + n)) else 0 := by
  sorry

/-- The finite family related to the Morse differential equation. -/
@[dlmf 18.34.E7_1]
def morsePolynomialFunction (lam : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  Real.exp (-lam * Real.exp (-x)) * (2 * lam * Real.exp (-x) : ℂ) ^ (lam - 1 / 2 : ℂ) *
    besselPolynomial (2 - 2 * lam) n (lam⁻¹ * Real.exp x) / n.factorial

/-- The Bessel polynomial is the evaluation of a polynomial. -/
theorem exists_besselPolynomial_eq_eval (a : ℂ) (n : ℕ) :
    ∃ p : ℂ[X], besselPolynomial a n = fun x => p.eval x := by
  refine ⟨∑ k ∈ Finset.range (n + 1), C (poch (-(n : ℂ)) k * poch (n + a - 1) k *
    (-1 / 2) ^ k / (k.factorial : ℂ)) * X ^ k, ?_⟩
  funext x
  unfold besselPolynomial terminatingHG
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show -x / 2 = (-1 / 2) * x by ring, mul_pow]; ring

@[dlmf 18.34.E7_2]
theorem morsePolynomialFunction_ode {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (x : ℝ) :
    deriv (deriv (morsePolynomialFunction lam n)) x -
      (lam ^ 2 * (Real.exp (-2 * x) - 2 * Real.exp (-x)) + (lam - (n + 1 / 2)) ^ 2 : ℝ) *
        morsePolynomialFunction lam n x = 0 := by
  obtain ⟨p, hp⟩ := exists_besselPolynomial_eq_eval (2 - 2 * lam) n
  have hO := besselPolynomial_differential_equation (2 - 2 * lam) n
  set Y : ℂ → ℂ := besselPolynomial (2 - 2 * lam) n
  set Y' : ℂ → ℂ := fun w => (derivative p).eval w
  set Y'' : ℂ → ℂ := fun w => (derivative (derivative p)).eval w
  have hY : ∀ w, HasDerivAt Y (Y' w) w := fun w => by rw [hp]; exact p.hasDerivAt w
  have hY' : ∀ w, HasDerivAt Y' (Y'' w) w := fun w => (derivative p).hasDerivAt w
  have hdY : deriv Y = Y' := funext fun w => (hY w).deriv
  have hdY' : deriv Y' = Y'' := funext fun w => (hY' w).deriv
  rw [hdY, hdY'] at hO
  -- the real phase and the argument of the polynomial
  set H : ℝ → ℝ := fun t => -lam * Real.exp (-t) - (lam - 1 / 2) * t
  set H' : ℝ → ℝ := fun t => lam * Real.exp (-t) - (lam - 1 / 2)
  set U : ℝ → ℂ := fun t => ((lam⁻¹ * Real.exp t : ℝ) : ℂ)
  set K : ℂ := (((2 * lam) ^ (lam - 1 / 2) : ℝ) : ℂ) / n.factorial
  have hψ : morsePolynomialFunction lam n = fun t => K * Complex.exp (H t) * Y (U t) := by
    funext t
    unfold morsePolynomialFunction
    have hb : (2 * (lam : ℂ) * (Real.exp (-t) : ℂ)) ^ ((lam : ℂ) - 1 / 2) =
        (((2 * lam) ^ (lam - 1 / 2) : ℝ) : ℂ) * Complex.exp (((-(lam - 1 / 2) * t : ℝ)) : ℂ) := by
      rw [show 2 * (lam : ℂ) * (Real.exp (-t) : ℂ) = ((2 * lam * Real.exp (-t) : ℝ) : ℂ) by
          push_cast; ring,
        show (lam : ℂ) - 1 / 2 = ((lam - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (by positivity),
        Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul,
        ← Complex.ofReal_exp]
      push_cast; ring_nf
    rw [hb]
    simp only [K, H, U, Y]
    push_cast
    rw [show -(lam : ℂ) * Complex.exp (-(t : ℂ)) - ((lam : ℂ) - 1 / 2) * t =
      -(lam : ℂ) * Complex.exp (-(t : ℂ)) + (-((lam : ℂ) - 1 / 2) * t) by ring, Complex.exp_add]
    ring
  -- derivatives of the pieces
  have hHr : ∀ t, HasDerivAt H (H' t) t := by
    intro t
    have h : HasDerivAt (fun y => -lam * Real.exp (-y) - (lam - 1 / 2) * y)
        (-lam * (Real.exp (-t) * -1) - (lam - 1 / 2) * 1) t :=
      ((hasDerivAt_neg t).exp.const_mul (-lam)).sub ((hasDerivAt_id' t).const_mul _)
    convert h using 1; simp only [H']; ring
  have hH'r : ∀ t, HasDerivAt H' (-lam * Real.exp (-t)) t := by
    intro t
    have h : HasDerivAt (fun y => lam * Real.exp (-y) - (lam - 1 / 2))
        (lam * (Real.exp (-t) * -1)) t :=
      ((hasDerivAt_neg t).exp.const_mul lam).sub_const _
    convert h using 1; ring
  have hUr : ∀ t, HasDerivAt U (U t) t := by
    intro t
    have h := ((Real.hasDerivAt_exp t).const_mul lam⁻¹).ofReal_comp
    simpa [U] using h
  have hE : ∀ t, HasDerivAt (fun t => Complex.exp (H t)) (Complex.exp (H t) * H' t) t :=
    fun t => (hHr t).ofReal_comp.cexp
  have hYU : ∀ t, HasDerivAt (fun t => Y (U t)) (Y' (U t) * U t) t :=
    fun t => (hY (U t)).comp t (hUr t)
  have hY'U : ∀ t, HasDerivAt (fun t => Y' (U t)) (Y'' (U t) * U t) t :=
    fun t => (hY' (U t)).comp t (hUr t)
  set ψ1 : ℝ → ℂ := fun t => K * Complex.exp (H t) * (H' t * Y (U t) + U t * Y' (U t))
  have hd1 : ∀ t, HasDerivAt (fun t => K * Complex.exp (H t) * Y (U t)) (ψ1 t) t := by
    intro t
    convert ((hE t).const_mul K).mul (hYU t) using 1
    simp only [ψ1]; ring
  have hd2 : ∀ t, HasDerivAt ψ1 (K * Complex.exp (H t) * (H' t * (H' t * Y (U t) + U t * Y' (U t))
      + ((-lam * Real.exp (-t) : ℝ) * Y (U t) + H' t * (Y' (U t) * U t) + U t * Y' (U t)
        + U t * (Y'' (U t) * U t)))) t := by
    intro t
    have h := ((hE t).const_mul K).mul ((((hH'r t).ofReal_comp).mul (hYU t)).add
      ((hUr t).mul (hY'U t)))
    convert h using 1
    simp only [Pi.mul_apply, Pi.add_apply]
    ring
  have hψd : deriv (morsePolynomialFunction lam n) = ψ1 := by
    rw [hψ]; funext t; exact (hd1 t).deriv
  rw [hψd, (hd2 x).deriv, hψ]
  have hO' := hO (U x)
  have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have hex : (Real.exp x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'
  have he2 : Real.exp (-2 * x) = (Real.exp x)⁻¹ ^ 2 := by
    rw [show -2 * x = -x + -x by ring, Real.exp_add, Real.exp_neg]; ring
  simp only [H', U] at hO' ⊢
  rw [he2, Real.exp_neg]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_div] at hO' ⊢
  linear_combination (norm := (field_simp; ring)) (K * Complex.exp (H x)) * hO'

section MorseOrthogonality

open Set

set_option maxHeartbeats 1000000

/-- The product of two Morse functions is a pulled-back finite Bessel weight. -/
theorem morse_product_weight {lam : ℝ} (hlam : 0 < lam) (m n : ℕ) (x : ℝ) :
    morsePolynomialFunction lam m x * morsePolynomialFunction lam n x =
      (2 : ℂ) ^ (2 * lam - 1 : ℂ) / ((m ! : ℂ) * n !) *
      (Real.exp x / lam : ℝ) *
      (besselPolynomial (2 - 2 * lam : ℂ) m (Real.exp x / lam) *
        besselPolynomial (2 - 2 * lam : ℂ) n (Real.exp x / lam) *
        (Real.rpow (Real.exp x / lam) (-2 * lam) * Real.exp (-2 / (Real.exp x / lam)) : ℝ)) := by
  let u : ℝ := Real.exp x / lam
  have hu : 0 < u := div_pos (Real.exp_pos x) hlam
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have hb : (2 * lam * Real.exp (-x) : ℝ) = 2 / u := by
    dsimp only [u]
    rw [Real.exp_neg]
    field_simp
  have he : exp (-lam * Real.exp (-x)) * exp (-lam * Real.exp (-x)) = exp (-2 / (u : ℂ)) := by
    rw [← exp_add]
    congr 1
    have hbc : (2 * lam * Real.exp (-x) : ℂ) = 2 / u := by exact_mod_cast hb
    linear_combination -hbc
  have hp : (2 / (u : ℂ)) ^ (lam - 1 / 2 : ℂ) * (2 / (u : ℂ)) ^ (lam - 1 / 2 : ℂ) =
      (2 : ℂ) ^ (2 * lam - 1 : ℂ) * (u : ℂ) * (u : ℂ) ^ (-2 * lam : ℂ) := by
    rw [← cpow_add _ _ (div_ne_zero two_ne_zero hu0),
      show (lam - 1 / 2 : ℂ) + (lam - 1 / 2 : ℂ) = 2 * lam - 1 by ring,
      show (2 / (u : ℂ)) ^ (2 * lam - 1 : ℂ) =
        (2 : ℂ) ^ (2 * lam - 1 : ℂ) / (u : ℂ) ^ (2 * lam - 1 : ℂ) by
          convert Complex.div_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu.le (2 * lam - 1 : ℂ) using 1]
    have hpow : (u : ℂ) * (u : ℂ) ^ (-2 * lam : ℂ) = (u : ℂ) ^ (-(2 * lam - 1 : ℂ)) := by
      conv_lhs => arg 1; rw [← cpow_one (u : ℂ)]
      rw [← cpow_add _ _ hu0]
      congr 1
      ring
    rw [mul_assoc, hpow, cpow_neg]
    ring
  have hbase : (2 * lam * Real.exp (-x) : ℂ) = 2 / (u : ℂ) := by exact_mod_cast hb
  have harg : (((lam⁻¹ : ℝ) : ℂ) * (Real.exp x : ℂ)) = (u : ℂ) := by dsimp only [u]; push_cast; ring
  unfold morsePolynomialFunction
  rw [hbase, harg]
  have hquot : (Real.exp x : ℂ) / (lam : ℂ) = (u : ℂ) := by
    dsimp only [u]
    rw [Complex.ofReal_div]
  rw [hquot]
  change _ = (2 : ℂ) ^ (2 * lam - 1 : ℂ) / ((m ! : ℂ) * n !) * (u : ℂ) *
    (besselPolynomial (2 - 2 * lam : ℂ) m u * besselPolynomial (2 - 2 * lam : ℂ) n u *
      (Real.rpow u (-2 * lam) * Real.exp (-2 / u) : ℝ))
  rw [ofReal_mul]
  rw [show ((Real.rpow u (-2 * lam) : ℝ) : ℂ) = (u : ℂ) ^ (-2 * lam : ℂ) by
    convert Complex.ofReal_cpow hu.le (-2 * lam) using 1 ; push_cast ; rfl,
    ofReal_exp]
  push_cast
  push_cast at he
  calc
    _ = (exp (-(lam : ℂ) * exp (-(x : ℂ))) * exp (-(lam : ℂ) * exp (-(x : ℂ)))) *
        ((2 / (u : ℂ)) ^ (lam - 1 / 2 : ℂ) * (2 / (u : ℂ)) ^ (lam - 1 / 2 : ℂ)) *
        besselPolynomial (2 - 2 * lam : ℂ) m u * besselPolynomial (2 - 2 * lam : ℂ) n u /
        ((m ! : ℂ) * n !) := by ring
    _ = _ := by rw [he, hp]; ring

/-- Exponential substitution in the product of two Morse functions. -/
theorem morse_product_integral {lam : ℝ} (hlam : 0 < lam) (m n : ℕ) :
    (∫ x : ℝ, morsePolynomialFunction lam m x * morsePolynomialFunction lam n x) =
      (2 : ℂ) ^ (2 * lam - 1 : ℂ) / ((m ! : ℂ) * n !) *
      ∫ u : ℝ in Ioi 0, besselPolynomial (2 - 2 * lam : ℂ) m u *
        besselPolynomial (2 - 2 * lam : ℂ) n u *
        (Real.rpow u (-2 * lam) * Real.exp (-2 / u) : ℝ) := by
  let H : ℝ → ℂ := fun u => besselPolynomial (2 - 2 * lam : ℂ) m u *
    besselPolynomial (2 - 2 * lam : ℂ) n u *
    (Real.rpow u (-2 * lam) * Real.exp (-2 / u) : ℝ)
  have hscale : (∫ u : ℝ in Ioi 0, H (u / lam)) = (lam : ℂ) * ∫ u : ℝ in Ioi 0, H u := by
    have h := integral_comp_mul_left_Ioi H 0 (inv_pos.mpr hlam)
    simpa [div_eq_mul_inv, mul_comm, Complex.real_smul] using h
  have he : (∫ x : ℝ, (Real.exp x : ℂ) * H (Real.exp x / lam)) =
      (lam : ℂ) * ∫ u : ℝ in Ioi 0, H u := by
    -- Mathlib's exponential substitution transports the unnormalized Bessel weight.
    have h := integral_comp_exp (fun u : ℝ => H (u / lam))
    rw [hscale] at h
    simpa only [Complex.real_smul] using h
  have hf : (fun x : ℝ => morsePolynomialFunction lam m x * morsePolynomialFunction lam n x) =
      fun x : ℝ => ((2 : ℂ) ^ (2 * lam - 1 : ℂ) / ((m ! : ℂ) * n !) / lam) *
        ((Real.exp x : ℂ) * H (Real.exp x / lam)) := by
    funext x
    rw [morse_product_weight hlam]
    dsimp only [H]
    push_cast
    ring
  rw [hf, integral_const_mul, he]
  have hlam0 : (lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr hlam.ne'
  change _ = (2 : ℂ) ^ (2 * lam - 1 : ℂ) / ((m ! : ℂ) * n !) * ∫ u : ℝ in Ioi 0, H u
  field_simp [hlam0]

@[dlmf 18.34.E7_3]
theorem morsePolynomialFunction_orthogonality {lam : ℝ} (m n : ℕ) (hm : (m : ℝ) < lam - 1 / 2) (hn : (n : ℝ) < lam - 1 / 2) :
    ∫ x : ℝ, morsePolynomialFunction lam m x * morsePolynomialFunction lam n x =
      if m = n then Gamma (2 * (lam : ℂ) - n) / ((2 * lam - 2 * n - 1) * n.factorial) else 0 := by
  have hlam : 0 < lam := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hmax : ((max m n : ℕ) : ℝ) < lam - 1 / 2 := by simpa only [Nat.cast_max] using max_lt hm hn
  have ha : 2 - 2 * lam < 1 - 2 * (max m n : ℕ) := by linarith
  have hB := besselPolynomial_finite_orthogonality (a := 2 - 2 * lam) m n ha
  rw [morse_product_integral hlam]
  have hW : (fun u : ℝ => besselPolynomial (2 - 2 * lam : ℂ) m u *
      besselPolynomial (2 - 2 * lam : ℂ) n u *
      (Real.rpow u (-2 * lam) * Real.exp (-2 / u) : ℝ)) =
    fun u : ℝ => besselPolynomial ((2 - 2 * lam : ℝ) : ℂ) m u *
      besselPolynomial ((2 - 2 * lam : ℝ) : ℂ) n u *
      (Real.rpow u ((2 - 2 * lam) - 2) * Real.exp (-2 / u) : ℝ) := by
    funext u
    push_cast
    rw [show 2 - 2 * lam - 2 = -2 * lam by ring]
  rw [hW]
  have hG : Gamma (2 * lam - 1 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith [Nat.cast_nonneg (α := ℝ) n])
  have hpow : (2 : ℂ) ^ (2 * lam - 1 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have he1 : (1 - ((2 - 2 * lam : ℝ) : ℂ)) = 2 * lam - 1 := by push_cast; ring
  rw [he1] at hB
  have hprod : (2 : ℂ) ^ (2 * lam - 1 : ℂ) /
      ((m ! : ℂ) * n !) *
      (∫ u : ℝ in Ioi 0, besselPolynomial ((2 - 2 * lam : ℝ) : ℂ) m u *
        besselPolynomial ((2 - 2 * lam : ℝ) : ℂ) n u *
        (Real.rpow u ((2 - 2 * lam) - 2) * Real.exp (-2 / u) : ℝ)) =
      Gamma (2 * lam - 1 : ℂ) / ((m ! : ℂ) * n !) *
        (if m = n then (1 - ((2 - 2 * lam : ℝ) : ℂ)) /
          (1 - ((2 - 2 * lam : ℝ) : ℂ) - 2 * n) * n ! /
          poch (2 - ((2 - 2 * lam : ℝ) : ℂ) - n) n else 0) := by
    rw [he1, ← hB]
    field_simp
  rw [hprod]
  split_ifs with hmn
  · subst m
    have hs : 0 < 2 * lam - n := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hG2 : Gamma (2 * lam - n : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hs)
    have hP : poch (2 * lam - n : ℂ) n ≠ 0 :=
      poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simpa using hs)) n
    have hΓ : Gamma (2 * lam : ℂ) = poch (2 * lam - n : ℂ) n * Gamma (2 * lam - n : ℂ) := by
      have h := Complex.Gamma_add_nat_div_Gamma_eq (n := n) (2 * lam - n : ℂ)
        (not_neg_nat_of_re_pos (by simpa using hs))
      rw [div_eq_iff hG2] at h
      convert h using 1 ; congr 1 ; ring
    have hΓ1 : Gamma (2 * lam : ℂ) = (2 * lam - 1 : ℂ) * Gamma (2 * lam - 1 : ℂ) := by
      have h0 : (2 * lam - 1 : ℂ) ≠ 0 := ne_zero_of_re_pos (by simp; linarith [Nat.cast_nonneg (α := ℝ) n])
      convert Gamma_add_one (2 * lam - 1 : ℂ) h0 using 1 ; congr 1 ; ring
    push_cast
    rw [show 1 - (2 - 2 * (lam : ℂ)) = 2 * lam - 1 by ring,
      show 2 - (2 - 2 * (lam : ℂ)) - n = 2 * lam - n by ring,
      show (2 * lam - 1 - 2 * n : ℂ) = 2 * lam - 2 * n - 1 by ring]
    have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hGammaProduct : (2 * lam - 1 : ℂ) * Gamma (2 * lam - 1 : ℂ) =
        poch (2 * lam - n : ℂ) n * Gamma (2 * lam - n : ℂ) := hΓ1.symm.trans hΓ
    calc
      _ = ((2 * lam - 1 : ℂ) * Gamma (2 * lam - 1 : ℂ)) /
          (poch (2 * lam - n : ℂ) n * ((2 * lam - 2 * n - 1 : ℂ) * n !)) := by
        simp only [div_eq_mul_inv, mul_inv]
        field_simp [hf]

      _ = _ := by
        rw [hGammaProduct]
        exact mul_div_mul_left _ _ hP
  · simp

end MorseOrthogonality


end DLMF.OrthogonalPolynomials
