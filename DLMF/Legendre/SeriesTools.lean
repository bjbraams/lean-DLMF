/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Integer
public import DLMF.Legendre.Laplace
public import Carlson.Elliptic.Addition

/-!
# Legendre generating functions and the polynomials `W_{n-1}`

Tools for the Legendre polynomials `P_n(z)` of complex argument and the polynomials
`W_{n-1}(z) = R_n(z)` with `Q_n = P_n Q_0 - R_n` (DLMF §14.7): polynomiality of the
hypergeometric representation, formal power series identities in `ℂ⟦X⟧`, and the generating
functions of DLMF 14.7.19.

## Main definitions

* `GeneratingSeries.legendreSeq`, `GeneratingSeries.generatingSeries`,
  `GeneratingSeries.primitiveSeries`: the sequence `n ↦ P_n(z)`, its generating series `∑ P_n(z) Xⁿ`
  and the primitive `∑ P_{n-1}(z) Xⁿ / n`.
* `GeneratingSeries.quadratic`, `GeneratingSeries.linear`: the power series `1 - 2zX + X²` and
  `z - X`.
* `GeneratingSeries.binomialSeries`: the formal binomial series of `(1 - ζX)^{-1/2}`.
* `GeneratingSeries.pCoeff`, `GeneratingSeries.secondKindCoeff`, `GeneratingSeries.secondKind`: the
  coefficients of `P_n` and `W_{n-1}` in powers of `z - 1` and the explicit polynomial of DLMF
  14.7.3.

## Main results

* `GeneratingSeries.legendreP_nat_eq_legendrePolynomialP`: the terminating hypergeometric function
  `P_n(z)` equals the Legendre polynomial for every `z ∈ ℂ`, including the cut `(-∞,-1]` of the
  continuation.
* `GeneratingSeries.generatingSeries_ode`, `GeneratingSeries.quadratic_generatingSeries_sq`:
  `(1-2zX+X²) G' = (z-X) G` and `(1-2zX+X²) G² = 1`.
* `GeneratingSeries.product_eq`: the coefficients of `F G` are the polynomials `R_n = W_{n-1}`
  (DLMF 14.7.4).
* `GeneratingSeries.binomialSeries_mul`: `G` is the product of the binomial series of
  `(1-ζ₁X)^{-1/2}` and `(1-ζ₂X)^{-1/2}` when `ζ₁+ζ₂ = 2z`, `ζ₁ζ₂ = 1`.
* `GeneratingSeries.generating`: the generating function of `P_n(z)` (DLMF 14.7.19) for complex `z`.
* `GeneratingSeries.secondKind_eq`: the explicit formula of DLMF 14.7.3 for `W_{n-1}`.
* `GeneratingSeries.hasSum_secondKind`, `GeneratingSeries.tsum_primitiveSeries_real`,
  `GeneratingSeries.hasSum_legendreQ_real`: generating functions of `W_{n-1}` and of combinations
  `c P_n - W_{n-1}` for real arguments.

## Implementation notes

The polynomiality of `P_n` on all of `ℂ` is proved by showing that the continuation recursion
at `a = -n` produces a polynomial function of `z` (`GeneratingSeries.recursion_poly`) and applying
the identity principle for polynomials. Helper names live in the namespace `GeneratingSeries`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric
open scoped Real Topology Nat PowerSeries
namespace DLMF.Legendre


/-- The Euler integral with `a = -m` is a polynomial function of `z` on all of `ℂ`. -/
theorem GeneratingSeries.integral_poly (m : ℕ) {b c : ℂ} (hb : 0 < b.re) (hcb : 0 < (c-b).re) :
    ∃ p : Polynomial ℂ, ∀ z, regularizedGaussHypergeometricIntegral (-(m:ℂ)) b c z = p.eval z := by
  set g : ℝ → ℂ := fun t => (t:ℂ)^(b-1) * (1-(t:ℂ))^(c-b-1) with hg
  have hgI : IntervalIntegrable g volume 0 1 := betaIntegral_convergent hb hcb
  set w : ℕ → ℂ := fun i => (Gamma b * Gamma (c-b))⁻¹ *
    ((-1)^i * (m.choose i : ℂ) * ∫ t in (0:ℝ)..1, g t * (t:ℂ)^i) with hw
  refine ⟨∑ i ∈ Finset.range (m+1), Polynomial.C (w i) * Polynomial.X^i, fun z => ?_⟩
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  have hexp : ∀ t : ℝ, eulerKernel (-(m:ℂ)) b c z t =
      ∑ i ∈ Finset.range (m+1), z^i * ((-1)^i * (m.choose i : ℂ) * (g t * (t:ℂ)^i)) := by
    intro t
    simp only [eulerKernel, neg_neg, cpow_natCast, hg]
    rw [show (1:ℂ) - z*t = -(z*t) + 1 by ring, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_pow, mul_pow, one_pow, mul_one]; ring
  unfold regularizedGaussHypergeometricIntegral
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum (fun i _ => by
    refine IntervalIntegrable.const_mul ?_ _
    refine IntervalIntegrable.const_mul ?_ _
    exact hgI.mul_continuousOn (by fun_prop)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [hw]; ring

/-- With `Re b ≥ 1`, the continuation recursion at `a = -m` is a polynomial function of `z`. -/
lemma GeneratingSeries.recursion_poly (k : ℕ) : ∀ (m : ℕ) (b c : ℂ), shiftB b = 0 → shiftC b c ≤ k →
    ∃ p : Polynomial ℂ, ∀ z,
        regularizedGaussHypergeometricByShifts k (-(m:ℂ)) b c z = p.eval z := by
  induction k with
  | zero =>
    intro m b c hB hC
    obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero hB (Nat.le_zero.mp hC)
    obtain ⟨p, hp⟩ := GeneratingSeries.integral_poly m (b := b) (c := c) (by linarith) (by linarith)
    exact ⟨p, fun z => by rw [regularizedGaussHypergeometricByShifts]; exact hp z⟩
  | succ k ih =>
    intro m b c hB hC
    by_cases hc : 0 < shiftC b c
    · have hlt := shiftC_add_one_lt hc
      obtain ⟨p1, hp1⟩ := ih m b (c+1) hB (by omega)
      rcases m with _ | m
      · refine ⟨Polynomial.C (c - 0) * p1, fun z => ?_⟩
        rw [regularizedGaussHypergeometricByShifts_succ_of_pos_c hc, hp1]; simp
      · obtain ⟨p2, hp2⟩ := ih m b (c+1) hB (by omega)
        refine ⟨Polynomial.C (c - -((m+1:ℕ):ℂ)) * p1 + Polynomial.C (-((m+1:ℕ):ℂ)) * p2,
          fun z => ?_⟩
        rw [regularizedGaussHypergeometricByShifts_succ_of_pos_c hc, hp1,
          show -((m+1:ℕ):ℂ) + 1 = -(m:ℂ) by push_cast; ring, hp2]
        simp
    · have hb : ¬ 0 < shiftB b := by omega
      have hC0 : shiftC b c = 0 := by omega
      obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero hB hC0
      obtain ⟨p, hp⟩ := GeneratingSeries.integral_poly m (b := b) (c := c)
          (by linarith) (by linarith)
      exact ⟨p, fun z => by
          rw [regularizedGaussHypergeometricByShifts_succ_of_zero hc hb]; exact hp z⟩

/-- `P_n` is a polynomial function on all of `ℂ`. -/
theorem GeneratingSeries.legendreP_poly (n : ℕ) : ∃ q : Polynomial ℂ, ∀ z,
    legendreP n z = q.eval z := by
  have hB : shiftB ((n:ℂ)+1) = 0 := by
    unfold shiftB; rw [Nat.ceil_eq_zero]; simp
  obtain ⟨p, hp⟩ := GeneratingSeries.recursion_poly (shiftMeasure ((n:ℂ)+1) 1) n ((n:ℂ)+1) 1 hB
    (by unfold shiftMeasure; omega)
  refine ⟨p.comp (Polynomial.C (1/2) - Polynomial.C (1/2) * Polynomial.X), fun z => ?_⟩
  rw [legendreP, regularizedGaussHypergeometric, hp]
  simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X]
  congr 1; ring

/-- The set `{z | 1 + z ∈ slitPlane}` is infinite. -/
theorem GeneratingSeries.infinite : {z : ℂ | 1 + z ∈ slitPlane}.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => ((n:ℝ):ℂ)) := fun a b h => by
    simpa using h
  refine Set.infinite_of_injective_forall_mem hinj fun n => ?_
  show 1 + ((n:ℝ):ℂ) ∈ slitPlane
  exact Or.inl (by simp; positivity)

/-- Two polynomial functions agreeing on `{1 + z ∈ slitPlane}` agree everywhere. -/
theorem GeneratingSeries.poly_ext {p q : Polynomial ℂ}
    (h : ∀ z : ℂ, 1 + z ∈ slitPlane → p.eval z = q.eval z)
    (z : ℂ) : p.eval z = q.eval z := by
  rw [Polynomial.eq_of_infinite_eval_eq p q (GeneratingSeries.infinite.mono fun w hw => h w hw)]

/-- The three-term recurrence for `P_n(z)` holds for every `z ∈ ℂ`. -/
theorem GeneratingSeries.legendreP_nat_recurrence (n : ℕ) (z : ℂ) :
    ((n:ℂ)+2) * legendreP ((n+2:ℕ):ℂ) z =
      (2*n+3) * z * legendreP ((n+1:ℕ):ℂ) z - ((n:ℂ)+1) * legendreP (n:ℂ) z := by
  obtain ⟨q0, h0⟩ := GeneratingSeries.legendreP_poly n
  obtain ⟨q1, h1⟩ := GeneratingSeries.legendreP_poly (n+1)
  obtain ⟨q2, h2⟩ := GeneratingSeries.legendreP_poly (n+2)
  have key := GeneratingSeries.poly_ext (p := Polynomial.C ((n:ℂ)+2) * q2)
    (q := Polynomial.C (2*(n:ℂ)+3) * Polynomial.X * q1 - Polynomial.C ((n:ℂ)+1) * q0)
    (fun w hw => by
      have e := DLMF.Legendre.legendreP_recurrence ((n:ℂ)+1) hw
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
        ← h0, ← h1, ← h2]
      push_cast
      rw [show (n:ℂ)+1+1 = n+2 by ring, show (n:ℂ)+1-1 = n by ring] at e
      linear_combination e) z
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    ← h0, ← h1, ← h2] at key
  linear_combination key

/-- `P_0(z) = 1` for every `z`. -/
theorem GeneratingSeries.legendreP_zero (z : ℂ) : legendreP ((0:ℕ):ℂ) z = 1 := by
  obtain ⟨q, h⟩ := GeneratingSeries.legendreP_poly 0
  have key := GeneratingSeries.poly_ext (p := q) (q := 1) (fun w hw => by
    rw [← h, DLMF.Legendre.legendreP_nat 0 hw];
        simp [DLMF.OrthogonalPolynomials.legendrePolynomialP_zero]) z
  rw [h, key]; simp

/-- `P_1(z) = z` for every `z`. -/
theorem GeneratingSeries.legendreP_one_left (z : ℂ) : legendreP ((1:ℕ):ℂ) z = z := by
  obtain ⟨q, h⟩ := GeneratingSeries.legendreP_poly 1
  have key := GeneratingSeries.poly_ext (p := q) (q := Polynomial.X) (fun w hw => by
    rw [← h, DLMF.Legendre.legendreP_nat 1 hw];
        simp [DLMF.OrthogonalPolynomials.legendrePolynomialP_one]) z
  rw [h, key]; simp

/-- `P_n(z)` equals the Legendre polynomial for every `z ∈ ℂ` (the hypergeometric
representation terminates). -/
theorem GeneratingSeries.legendreP_nat_eq_legendrePolynomialP (n : ℕ) (z : ℂ) :
    legendreP n z = DLMF.OrthogonalPolynomials.legendrePolynomialP n z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [GeneratingSeries.legendreP_zero,
                DLMF.OrthogonalPolynomials.legendrePolynomialP_zero]
    | 1, _ => rw [GeneratingSeries.legendreP_one_left,
                DLMF.OrthogonalPolynomials.legendrePolynomialP_one]
    | n+2, ih =>
      have e1 := GeneratingSeries.legendreP_nat_recurrence n z
      have e2 := DLMF.OrthogonalPolynomials.legendrePolynomialP_recurrence n z
      rw [ih n (by omega), ih (n+1) (by omega)] at e1
      have hn : (n:ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+1)
      exact mul_left_cancel₀ hn (e1.trans e2.symm)


/-- The quadratic `1 - 2zX + X²` as a power series. -/
noncomputable def GeneratingSeries.quadratic (z : ℂ) : ℂ⟦X⟧ :=
  1 - PowerSeries.C (2*z) * PowerSeries.X + PowerSeries.X^2

/-- The linear factor `z - X` as a power series. -/
noncomputable def GeneratingSeries.linear (z : ℂ) : ℂ⟦X⟧ := PowerSeries.C z - PowerSeries.X

/-- Multiplication by `GeneratingSeries.quadratic z = 1 - 2zX + X²` expands as `S - 2z·X S + X·X S`.
-/
theorem GeneratingSeries.quadratic_eq (z : ℂ) (S : ℂ⟦X⟧) : GeneratingSeries.quadratic z * S =
    S - PowerSeries.C (2*z) * (PowerSeries.X * S) + PowerSeries.X * (PowerSeries.X * S) := by
  unfold GeneratingSeries.quadratic; ring

/-- The constant coefficient of `(1 - 2zX + X²) S` equals that of `S`. -/
theorem GeneratingSeries.coeff_quadratic_zero (z : ℂ) (S : ℂ⟦X⟧) :
    PowerSeries.coeff 0 (GeneratingSeries.quadratic z * S) = PowerSeries.coeff 0 S := by
  rw [GeneratingSeries.quadratic_eq]; simp

/-- The coefficient of `X` in `(1 - 2zX + X²) S` is `s₁ - 2z s₀`. -/
theorem GeneratingSeries.coeff_quadratic_one (z : ℂ) (S : ℂ⟦X⟧) :
    PowerSeries.coeff 1 (GeneratingSeries.quadratic z * S) = PowerSeries.coeff 1 S -
        2*z*PowerSeries.coeff 0 S := by
  rw [GeneratingSeries.quadratic_eq, map_add, map_sub, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_succ_X_mul]
  simp

/-- The coefficient of `X^(n+2)` in `(1 - 2zX + X²) S` is `s_{n+2} - 2z s_{n+1} + s_n`. -/
theorem GeneratingSeries.coeff_quadratic_add_two (z : ℂ) (S : ℂ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff (n+2) (GeneratingSeries.quadratic z * S) = PowerSeries.coeff (n+2) S -
      2*z*PowerSeries.coeff (n+1) S + PowerSeries.coeff n S := by
  rw [GeneratingSeries.quadratic_eq, map_add, map_sub, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]

/-- The constant coefficient of `(z - X) S` is `z s₀`. -/
theorem GeneratingSeries.coeff_linear_zero (z : ℂ) (S : ℂ⟦X⟧) :
    PowerSeries.coeff 0 (GeneratingSeries.linear z * S) = z * PowerSeries.coeff 0 S := by
  unfold GeneratingSeries.linear; rw [sub_mul, map_sub, PowerSeries.coeff_C_mul]; simp

/-- The coefficient of `X^(n+1)` in `(z - X) S` is `z s_{n+1} - s_n`. -/
theorem GeneratingSeries.coeff_linear_succ (z : ℂ) (S : ℂ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff (n+1) (GeneratingSeries.linear z * S) = z * PowerSeries.coeff (n+1) S -
      PowerSeries.coeff n S := by
  unfold GeneratingSeries.linear;
      rw [sub_mul, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]

/-- The sequence `n ↦ P_n(z)`. -/
noncomputable def GeneratingSeries.legendreSeq (z : ℂ) (n : ℕ) : ℂ := legendreP (n:ℂ) z

/-- `P_0(z) = 1`. -/
theorem GeneratingSeries.legendreSeq_zero (z : ℂ) : GeneratingSeries.legendreSeq z 0 = 1 :=
    GeneratingSeries.legendreP_zero z
/-- `P_1(z) = z`. -/
theorem GeneratingSeries.legendreSeq_one (z : ℂ) : GeneratingSeries.legendreSeq z 1 = z :=
    GeneratingSeries.legendreP_one_left z
/-- Bonnet's recurrence `(n+2) P_{n+2}(z) = (2n+3) z P_{n+1}(z) - (n+1) P_n(z)`. -/
theorem GeneratingSeries.legendreSeq_recurrence (z : ℂ) (n : ℕ) :
    ((n:ℂ)+2) * GeneratingSeries.legendreSeq z (n+2) = (2*n+3) * z *
        GeneratingSeries.legendreSeq z (n+1) - ((n:ℂ)+1) * GeneratingSeries.legendreSeq z n :=
  GeneratingSeries.legendreP_nat_recurrence n z

/-- The generating series `∑ P_n(z) Xⁿ`. -/
noncomputable def GeneratingSeries.generatingSeries (z : ℂ) : ℂ⟦X⟧ :=
    PowerSeries.mk (GeneratingSeries.legendreSeq z)

/-- Its primitive `∑ P_{n-1}(z) Xⁿ / n`. -/
noncomputable def GeneratingSeries.primitiveSeries (z : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else GeneratingSeries.legendreSeq z (n-1) / n

/-- The `k`-th coefficient of the formal derivative of `∑ P_n(z) Xⁿ` is `(k+1) P_{k+1}(z)`. -/
theorem GeneratingSeries.coeff_derivative_generatingSeries (z : ℂ) (k : ℕ) :
    PowerSeries.coeff k (d⁄dX (GeneratingSeries.generatingSeries z)) =
        GeneratingSeries.legendreSeq z (k+1) * (k+1) := by
  rw [PowerSeries.coeff_derivative, GeneratingSeries.generatingSeries, PowerSeries.coeff_mk]

/-- `(1 - 2zX + X²) G' = (z - X) G`. -/
theorem GeneratingSeries.generatingSeries_ode (z : ℂ) : GeneratingSeries.quadratic z *
    d⁄dX (GeneratingSeries.generatingSeries z) = GeneratingSeries.linear z *
    GeneratingSeries.generatingSeries z := by
  ext n
  rcases n with _ | _ | n
  · rw [GeneratingSeries.coeff_quadratic_zero, GeneratingSeries.coeff_linear_zero,
        GeneratingSeries.coeff_derivative_generatingSeries]
    simp only [GeneratingSeries.generatingSeries, PowerSeries.coeff_mk, zero_add,
        GeneratingSeries.legendreSeq_one, GeneratingSeries.legendreSeq_zero]; ring
  · rw [GeneratingSeries.coeff_quadratic_one, GeneratingSeries.coeff_linear_succ,
        GeneratingSeries.coeff_derivative_generatingSeries,
        GeneratingSeries.coeff_derivative_generatingSeries]
    simp only [GeneratingSeries.generatingSeries, PowerSeries.coeff_mk]
    have e := GeneratingSeries.legendreSeq_recurrence z 0
    simp only [GeneratingSeries.legendreSeq_one, GeneratingSeries.legendreSeq_zero, zero_add] at e ⊢
    push_cast at e ⊢
    linear_combination e
  · rw [GeneratingSeries.coeff_quadratic_add_two, GeneratingSeries.coeff_linear_succ,
        GeneratingSeries.coeff_derivative_generatingSeries,
        GeneratingSeries.coeff_derivative_generatingSeries,
      GeneratingSeries.coeff_derivative_generatingSeries]
    simp only [GeneratingSeries.generatingSeries, PowerSeries.coeff_mk]
    have e := GeneratingSeries.legendreSeq_recurrence z (n+1)
    push_cast at e ⊢
    linear_combination e

/-- The formal derivative of `1 - 2zX + X²` is `-2z + 2X`. -/
theorem GeneratingSeries.derivative_quadratic (z : ℂ) : d⁄dX (GeneratingSeries.quadratic z) =
    -PowerSeries.C (2*z) + 2 * PowerSeries.X := by
  unfold GeneratingSeries.quadratic
  rw [map_add, map_sub, Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_C,
    PowerSeries.derivative_X, PowerSeries.derivative_one]
  simp only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_sub]
  push_cast; ring_nf

/-- `(1 - 2zX + X²) G² = 1`. -/
theorem GeneratingSeries.quadratic_generatingSeries_sq (z : ℂ) : GeneratingSeries.quadratic z *
    GeneratingSeries.generatingSeries z ^ 2 = 1 := by
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_one,
        GeneratingSeries.derivative_quadratic]
    simp only [smul_eq_mul]
    have h := GeneratingSeries.generatingSeries_ode z
    have : GeneratingSeries.quadratic z *
        (((2:ℕ):ℂ⟦X⟧) * GeneratingSeries.generatingSeries z ^ (2-1) *
        d⁄dX (GeneratingSeries.generatingSeries z)) =
        2 * GeneratingSeries.generatingSeries z *
            (GeneratingSeries.linear z * GeneratingSeries.generatingSeries z) := by
      rw [← h]; push_cast; ring
    rw [this]; unfold GeneratingSeries.linear; simp only [map_mul, map_ofNat]; ring
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      GeneratingSeries.coeff_quadratic_zero, pow_two, PowerSeries.coeff_mul]
    simp [GeneratingSeries.generatingSeries, GeneratingSeries.legendreSeq_zero]

/-- The formal derivative of `GeneratingSeries.primitiveSeries z = ∑ P_{n-1}(z) Xⁿ/n` is the
generating series `GeneratingSeries.generatingSeries z = ∑ P_n(z) Xⁿ`. -/
theorem GeneratingSeries.derivative_primitiveSeries (z : ℂ) : d⁄dX
    (GeneratingSeries.primitiveSeries z) = GeneratingSeries.generatingSeries z := by
  ext k
  rw [PowerSeries.coeff_derivative, GeneratingSeries.primitiveSeries, PowerSeries.coeff_mk,
      GeneratingSeries.generatingSeries, PowerSeries.coeff_mk]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  have : ((k+1:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  push_cast at this ⊢
  field_simp

/-- `(1 - 2zX + X²) (FG)' = 1 + (z - X) FG`. -/
theorem GeneratingSeries.product_ode (z : ℂ) : GeneratingSeries.quadratic z *
    d⁄dX (GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z) =
    1 + GeneratingSeries.linear z *
        (GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z) := by
  rw [Derivation.leibniz, GeneratingSeries.derivative_primitiveSeries]
  simp only [smul_eq_mul]
  rw [← GeneratingSeries.quadratic_generatingSeries_sq z, mul_add,
      show GeneratingSeries.quadratic z *
      (GeneratingSeries.primitiveSeries z * d⁄dX (GeneratingSeries.generatingSeries z)) =
    GeneratingSeries.primitiveSeries z *
        (GeneratingSeries.quadratic z * d⁄dX (GeneratingSeries.generatingSeries z)) by
        ring, GeneratingSeries.generatingSeries_ode]
  ring

/-- The coefficients of `F G` are the convolution sums of DLMF 14.7.4. -/
theorem GeneratingSeries.coeff_product (z : ℂ) (n : ℕ) : PowerSeries.coeff n
    (GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z) =
    ∑ j ∈ Finset.range n, GeneratingSeries.legendreSeq z j *
        GeneratingSeries.legendreSeq z (n-j-1) / (j+1:ℂ) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ']
  simp only [GeneratingSeries.primitiveSeries, GeneratingSeries.generatingSeries,
      PowerSeries.coeff_mk, ↓reduceIte, zero_mul, add_zero,
    Nat.add_one_ne_zero, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [show n - (j+1) = n - j - 1 by omega]
  push_cast; ring

/-- The convolution sums satisfy the recurrence of the polynomials `W_{n-1}`. -/
theorem GeneratingSeries.product_recurrence (z : ℂ) (n : ℕ) :
    ((n:ℂ)+2) * PowerSeries.coeff (n+2)
        (GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z) =
      (2*n+3) * z * PowerSeries.coeff (n+1)
          (GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z) -
        ((n:ℂ)+1) * PowerSeries.coeff n
            (GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z) := by
  have h := congrArg (PowerSeries.coeff (n+1)) (GeneratingSeries.product_ode z)
  set U := GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z
  rcases n with _ | n
  · rw [GeneratingSeries.coeff_quadratic_one, map_add, GeneratingSeries.coeff_linear_succ,
        PowerSeries.coeff_derivative,
      PowerSeries.coeff_derivative] at h
    simp only [PowerSeries.coeff_one] at h
    push_cast at h ⊢
    linear_combination h
  · rw [GeneratingSeries.coeff_quadratic_add_two, map_add, GeneratingSeries.coeff_linear_succ,
        PowerSeries.coeff_derivative,
      PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at h
    simp only [PowerSeries.coeff_one] at h
    push_cast at h ⊢
    linear_combination h

/-- The constant coefficient of
`GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z` is `0`. -/
theorem GeneratingSeries.product_zero (z : ℂ) : PowerSeries.coeff 0
    (GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z) = 0 := by
  rw [GeneratingSeries.coeff_product]; simp

/-- The coefficient of `X` in
`GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z` is `1`. -/
theorem GeneratingSeries.product_one (z : ℂ) : PowerSeries.coeff 1
    (GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z) = 1 := by
  rw [GeneratingSeries.coeff_product]; simp [GeneratingSeries.legendreSeq_zero]

/-- The `n`-th coefficient of
`GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z` equals
`R_n(z) = (legendreQPoly n).eval z`, the polynomial with `Q_n = P_n Q_0 - R_n`. -/
theorem GeneratingSeries.product_eq (z : ℂ) (n : ℕ) :
    PowerSeries.coeff n (GeneratingSeries.primitiveSeries z * GeneratingSeries.generatingSeries z) =
        (legendreQPoly n).eval z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [GeneratingSeries.product_zero]; simp [legendreQPoly]
    | 1, _ => rw [GeneratingSeries.product_one]; simp [legendreQPoly]
    | n+2, ih =>
      have e := GeneratingSeries.product_recurrence z n
      rw [ih n (by omega), ih (n+1) (by omega)] at e
      have hn : (n:ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+1)
      rw [legendreQPoly]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      rw [eq_inv_mul_iff_mul_eq₀ hn, e]


/-- The formal binomial series of `(1 - ζX)^{-1/2}`. -/
noncomputable def GeneratingSeries.binomialSeries (ζ : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun j => pochhammer (1/2) j * ζ^j / (j.factorial : ℂ)

/-- The binomial series `B = GeneratingSeries.binomialSeries ζ` of `(1 - ζX)^{-1/2}` satisfies
`(1 - ζX) B' = (ζ/2) B`. -/
theorem GeneratingSeries.binomialSeries_ode (ζ : ℂ) :
    (1 - PowerSeries.C ζ * PowerSeries.X) * d⁄dX (GeneratingSeries.binomialSeries ζ) =
        PowerSeries.C (ζ/2) * GeneratingSeries.binomialSeries ζ := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_derivative]
  rcases n with _ | n
  · simp [GeneratingSeries.binomialSeries, PowerSeries.coeff_mk, pochhammer_succ,
        pochhammer_zero]; ring
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    simp only [GeneratingSeries.binomialSeries, PowerSeries.coeff_mk]
    rw [pochhammer_succ (1/2) (n+1), pochhammer_succ (1/2) n, Nat.factorial_succ (n+1),
        Nat.factorial_succ n]
    have h1 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have h2 : (n:ℂ) + 1 + 1 ≠ 0 := by
      have : ((n + 1 + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at this; exact this
    have h3 : (n:ℂ) + 1 ≠ 0 := by
      have : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at this; exact this
    push_cast
    field_simp
    ring

/-- `(1 - ζX) B(ζ)² = 1`. -/
theorem GeneratingSeries.binomialSeries_sq (ζ : ℂ) : (1 - PowerSeries.C ζ * PowerSeries.X) *
    GeneratingSeries.binomialSeries ζ ^ 2 = 1 := by
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_one, map_sub,
      Derivation.leibniz, PowerSeries.derivative_one, PowerSeries.derivative_C,
          PowerSeries.derivative_X]
    simp only [smul_eq_mul]
    have h := GeneratingSeries.binomialSeries_ode ζ
    have : (1 - PowerSeries.C ζ * PowerSeries.X) *
        (((2:ℕ):ℂ⟦X⟧) * GeneratingSeries.binomialSeries ζ ^ (2-1) *
        d⁄dX (GeneratingSeries.binomialSeries ζ)) = 2 * GeneratingSeries.binomialSeries ζ *
            (PowerSeries.C (ζ/2) * GeneratingSeries.binomialSeries ζ) := by
      rw [← h]; push_cast; ring
    rw [this, show PowerSeries.C (ζ/2) = PowerSeries.C ζ * PowerSeries.C (1/2) by
      rw [← map_mul]; ring_nf]
    have h2 : (2:ℂ⟦X⟧) * PowerSeries.C (1/2) = 1 := by
      rw [← map_ofNat PowerSeries.C 2, ← map_mul]; norm_num
    linear_combination (PowerSeries.C ζ * GeneratingSeries.binomialSeries ζ ^ 2) * h2
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul,
      pow_two, PowerSeries.coeff_mul]
    simp [GeneratingSeries.binomialSeries, pochhammer_zero]

/-- Square roots of a power series with the same nonzero constant term coincide. -/
theorem GeneratingSeries.sq_inj {A B : ℂ⟦X⟧} (h : A^2 = B^2)
    (h0 : PowerSeries.constantCoeff A = PowerSeries.constantCoeff B)
    (h1 : PowerSeries.constantCoeff A ≠ 0) : A = B := by
  have hfac : (A - B) * (A + B) = 0 := by linear_combination h
  have hne : A + B ≠ 0 := by
    intro hab
    have := congrArg PowerSeries.constantCoeff hab
    rw [map_add, ← h0, map_zero] at this
    exact h1 (by linear_combination this/2)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hne)

/-- `B(ζ₁) B(ζ₂) = ∑ P_n(z) Xⁿ` when `ζ₁ + ζ₂ = 2z` and `ζ₁ ζ₂ = 1`. -/
theorem GeneratingSeries.binomialSeries_mul (z ζ₁ ζ₂ : ℂ) (hs : ζ₁ + ζ₂ = 2*z) (hp : ζ₁ * ζ₂ = 1) :
    GeneratingSeries.binomialSeries ζ₁ * GeneratingSeries.binomialSeries ζ₂ =
        GeneratingSeries.generatingSeries z := by
  have hQ : GeneratingSeries.quadratic z = (1 - PowerSeries.C ζ₁ * PowerSeries.X) *
      (1 - PowerSeries.C ζ₂ * PowerSeries.X) := by
    unfold GeneratingSeries.quadratic
    rw [show (2:ℂ)*z = ζ₁ + ζ₂ by rw [hs], map_add]
    have : PowerSeries.C ζ₁ * PowerSeries.C ζ₂ = (1:ℂ⟦X⟧) := by rw [← map_mul, hp, map_one]
    linear_combination -(PowerSeries.X^2 : ℂ⟦X⟧) * this
  have hQ0 : GeneratingSeries.quadratic z ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    simp [GeneratingSeries.quadratic] at this
  refine GeneratingSeries.sq_inj ?_ ?_ ?_
  · refine mul_left_cancel₀ hQ0 ?_
    rw [GeneratingSeries.quadratic_generatingSeries_sq, hQ]
    linear_combination (GeneratingSeries.binomialSeries_sq ζ₂) *
        ((1 - PowerSeries.C ζ₁ * PowerSeries.X) * GeneratingSeries.binomialSeries ζ₁ ^ 2) +
      GeneratingSeries.binomialSeries_sq ζ₁
  · rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [GeneratingSeries.binomialSeries, GeneratingSeries.generatingSeries, pochhammer_zero,
        GeneratingSeries.legendreSeq_zero]
  · rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [GeneratingSeries.binomialSeries, pochhammer_zero]


/-- `‖(1/2)_n‖ ≤ n!`. -/
theorem GeneratingSeries.norm_pochhammer_le (n : ℕ) : ‖pochhammer (1/2:ℂ) n‖ ≤ n.factorial := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [pochhammer_succ, norm_mul, Nat.factorial_succ, Nat.cast_mul]
    have h : ‖(1/2:ℂ) + n‖ ≤ n + 1 := by
      calc ‖(1/2:ℂ) + n‖ ≤ ‖(1/2:ℂ)‖ + ‖(n:ℂ)‖ := norm_add_le _ _
        _ ≤ n + 1 := by simp; linarith
    calc ‖pochhammer (1/2:ℂ) n‖ * ‖(1/2:ℂ) + n‖ ≤ n.factorial * (n + 1) :=
          mul_le_mul ih h (norm_nonneg _) (by positivity)
      _ = _ := by push_cast; ring

/-- The `j`-th term of the binomial series satisfies `‖b_j h^j‖ ≤ ‖hζ‖^j`. -/
theorem GeneratingSeries.norm_coeff_binomialSeries_le (ζ h : ℂ) (j : ℕ) :
    ‖PowerSeries.coeff j (GeneratingSeries.binomialSeries ζ) * h^j‖ ≤ ‖h*ζ‖^j := by
  simp only [GeneratingSeries.binomialSeries, PowerSeries.coeff_mk]
  have hf : (0:ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, norm_mul, mul_pow]
  calc ‖pochhammer (1/2:ℂ) j‖ * ‖ζ‖^j / j.factorial * ‖h‖^j ≤ j.factorial * ‖ζ‖^j /
         j.factorial * ‖h‖^j := by
        gcongr; exact GeneratingSeries.norm_pochhammer_le j
    _ = ‖h‖^j * ‖ζ‖^j := by field_simp

/-- For `‖hζ‖ < 1`, the binomial series `∑ b_j h^j` of `GeneratingSeries.binomialSeries ζ` converges
absolutely. -/
theorem GeneratingSeries.summable_binomialSeries (ζ h : ℂ) (hl : ‖h*ζ‖ < 1) :
    Summable fun j => ‖PowerSeries.coeff j (GeneratingSeries.binomialSeries ζ) * h^j‖ :=
  (summable_geometric_of_lt_one (norm_nonneg _) hl).of_nonneg_of_le (fun _ => norm_nonneg _)
    (GeneratingSeries.norm_coeff_binomialSeries_le ζ h)

/-- For `‖hζ‖ < 1`, the binomial series `∑ b_j h^j` of `GeneratingSeries.binomialSeries ζ` sums to
`(1 - hζ)^{-1/2}` (principal branch). -/
theorem GeneratingSeries.hasSum_binomialSeries (ζ h : ℂ) (hl : ‖h*ζ‖ < 1) :
    HasSum (fun j => PowerSeries.coeff j (GeneratingSeries.binomialSeries ζ) * h^j)
        ((1 - h*ζ)^(-1/2:ℂ)) := by
  have ht : ‖-(h*ζ)‖ < 1 := by rwa [norm_neg]
  have e := hasSum_one_add_cpow (-1/2:ℂ) ht
  rw [show (1:ℂ) + -(h*ζ) = 1 - h*ζ by ring, show -(-1/2:ℂ) = 1/2 by ring] at e
  refine e.congr_fun fun j => ?_
  simp only [GeneratingSeries.binomialSeries, PowerSeries.coeff_mk, neg_neg]
  ring

/-- Generating function of `P_n(z)` in the product form. -/
theorem GeneratingSeries.generating (z ζ₁ ζ₂ h : ℂ) (hs : ζ₁ + ζ₂ = 2*z) (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖h*ζ₁‖ < 1) (h2 : ‖h*ζ₂‖ < 1) :
    HasSum (fun n => GeneratingSeries.legendreSeq z n * h^n) ((1 - 2*z*h + h^2)^(-1/2:ℂ)) := by
  have hB1 := GeneratingSeries.hasSum_binomialSeries ζ₁ h h1
  have hB2 := GeneratingSeries.hasSum_binomialSeries ζ₂ h h2
  have hs1 := GeneratingSeries.summable_binomialSeries ζ₁ h h1
  have hs2 := GeneratingSeries.summable_binomialSeries ζ₂ h h2
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs1 hs2
  rw [hB1.tsum_eq, hB2.tsum_eq] at hprod
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hs1 hs2).of_norm
  have hre : ∀ ζ : ℂ, ‖h*ζ‖ < 1 → 0 < (1 - h*ζ).re := fun ζ hl => by
    have := Complex.re_le_norm (h*ζ)
    simp only [sub_re, one_re]; linarith
  rw [show (1:ℂ) - 2*z*h + h^2 = (1 - h*ζ₁) * (1 - h*ζ₂) by
      rw [show 2*z = ζ₁ + ζ₂ from hs.symm]; linear_combination -h^2 * hp,
    ← DLMF.Hypergeometric.cpow_mul_cpow_of_re_pos (hre ζ₁ h1) (hre ζ₂ h2), hprod]
  refine (hsum.hasSum).congr_fun fun n => ?_
  rw [show GeneratingSeries.legendreSeq z n =
      PowerSeries.coeff n (GeneratingSeries.generatingSeries z) by
      simp [GeneratingSeries.generatingSeries],
    ← GeneratingSeries.binomialSeries_mul z ζ₁ ζ₂ hs hp, PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring


/-- The two roots `z ± √(z²-1)` of `ζ² - 2zζ + 1`, with the exterior square root. -/
theorem GeneratingSeries.roots {z : ℂ} (hz : z-1 ∈ slitPlane) :
    let s := exp ((log (z-1)+log (z+1))/2)
    (z + s) + (z - s) = 2*z ∧ (z + s) * (z - s) = 1 := by
  intro s
  have hm0 := slitPlane_ne_zero hz
  have hp0 := slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  have hp0' : z + 1 ≠ 0 := by rwa [add_comm]
  have hs2 : s^2 = (z-1)*(z+1) := by
    simp only [s]
    rw [← Complex.exp_nat_mul, show ((2:ℕ):ℂ) * ((log (z-1)+log (z+1))/2) = log (z-1) + log (z+1) by
      push_cast; ring, Complex.exp_add, Complex.exp_log hm0, Complex.exp_log hp0']
  constructor
  · ring
  · linear_combination -hs2

/-! ### The explicit form of `W_{n-1}` (DLMF 14.7.3) -/

/-- Coefficients `(n+s)!/(2^s (n-s)! s!²)` of `P_n` in powers of `z-1`, extended by zero. -/
noncomputable def GeneratingSeries.pCoeff (n s : ℕ) : ℝ :=
  if s ≤ n then ((n+s).factorial : ℝ) / (2^s * ((n-s).factorial : ℝ) * (s.factorial : ℝ)^2) else 0

/-- Coefficients of `W_{n-1}` in powers of `z-1` (DLMF 14.7.3). -/
noncomputable def GeneratingSeries.secondKindCoeff (n s : ℕ) : ℝ := GeneratingSeries.pCoeff n s *
    ((harmonic n : ℝ) - harmonic s)

/-- `m! ≠ 0` as a real number. -/
theorem GeneratingSeries.factorial_ne (m : ℕ) : (m.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr m.factorial_ne_zero

/-- `GeneratingSeries.pCoeff n 0 = 1`: the constant coefficient of `P_n` in powers of `z - 1`. -/
theorem GeneratingSeries.pCoeff_zero (n : ℕ) : GeneratingSeries.pCoeff n 0 = 1 := by
  have := GeneratingSeries.factorial_ne n
  simp [GeneratingSeries.pCoeff, this]

/-- Factorial identity behind the three-term recurrence of `P_n` in powers of `z-1`. -/
theorem GeneratingSeries.pCoeff_recurrence (n s : ℕ) :
    ((n:ℝ)+2) * GeneratingSeries.pCoeff (n+2) (s+1) = (2*n+3) *
        (GeneratingSeries.pCoeff (n+1) (s+1) + GeneratingSeries.pCoeff (n+1) s) -
      ((n:ℝ)+1) * GeneratingSeries.pCoeff n (s+1) := by
  rcases Nat.lt_or_ge n (s+1) with h | h
  · rcases Nat.lt_or_ge (n+1) (s+1) with h' | h'
    · rcases Nat.lt_or_ge (n+2) (s+1) with h'' | h''
      · simp [GeneratingSeries.pCoeff, show ¬ s+1 ≤ n+2 by omega, show ¬ s+1 ≤ n+1 by omega,
          show ¬ s+1 ≤ n by omega, show ¬ s ≤ n+1 by omega]
      · -- s = n+1
        obtain rfl : s = n+1 := by omega
        simp only [GeneratingSeries.pCoeff, show n+1+1 ≤ n+2 by omega, show ¬ n+1+1 ≤ n+1 by omega,
          show ¬ n+1+1 ≤ n by omega, show n+1 ≤ n+1 by omega, ↓reduceIte, Nat.sub_self,
          show n+2-(n+1+1) = 0 by omega]
        rw [show n+2+(n+1+1) = (2*n+1+1+1)+1 by ring, show n+1+(n+1) = 2*n+1+1 by ring,
          Nat.factorial_succ (2*n+1+1+1), Nat.factorial_succ (2*n+1+1), Nat.factorial_succ (n+1)]
        have := GeneratingSeries.factorial_ne (2*n+1+1); have := GeneratingSeries.factorial_ne (n+1)
        push_cast; field_simp; ring
    · -- s = n
      obtain rfl : s = n := by omega
      simp only [GeneratingSeries.pCoeff, show s+1 ≤ s+2 by omega, show s+1 ≤ s+1 by omega,
        show ¬ s+1 ≤ s by omega, show s ≤ s+1 by omega, ↓reduceIte, Nat.sub_self,
        show s+2-(s+1) = 1 by omega, show s+1-s = 1 by omega]
      rw [show s+2+(s+1) = (2*s+1+1)+1 by ring, show s+1+(s+1) = 2*s+1+1 by ring,
        show s+1+s = 2*s+1 by ring, Nat.factorial_succ (2*s+1+1), Nat.factorial_succ (2*s+1),
        Nat.factorial_succ s]
      have := GeneratingSeries.factorial_ne (2*s+1); have := GeneratingSeries.factorial_ne s
      push_cast; field_simp; ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [GeneratingSeries.pCoeff, show s+1 ≤ s+1+d+2 by omega, show s+1 ≤ s+1+d+1 by omega,
      show s+1 ≤ s+1+d by omega, show s ≤ s+1+d+1 by omega, ↓reduceIte,
      show s+1+d+2-(s+1) = d+2 by omega, show s+1+d+1-(s+1) = d+1 by omega,
      show s+1+d-(s+1) = d by omega, show s+1+d+1-s = d+2 by omega]
    rw [show s+1+d+2+(s+1) = (2*s+d+2+1)+1 by ring, show s+1+d+1+(s+1) = 2*s+d+2+1 by ring,
      show s+1+d+(s+1) = 2*s+d+2 by ring, show s+1+d+1+s = 2*s+d+2 by ring,
      Nat.factorial_succ (2*s+d+2+1), Nat.factorial_succ (2*s+d+2), Nat.factorial_succ (d+1),
      Nat.factorial_succ d, Nat.factorial_succ s]
    have := GeneratingSeries.factorial_ne (2*s+d+2); have := GeneratingSeries.factorial_ne d;
        have := GeneratingSeries.factorial_ne s
    push_cast; field_simp; ring

/-- `A(n+2,s+1) - A(n,s+1) = (2n+3) A(n+1,s)/(s+1)`. -/
theorem GeneratingSeries.pCoeff_diff (n s : ℕ) :
    GeneratingSeries.pCoeff (n+2) (s+1) - GeneratingSeries.pCoeff n (s+1) = (2*n+3) *
        GeneratingSeries.pCoeff (n+1) s / ((s:ℝ)+1) := by
  rcases Nat.lt_or_ge n (s+1) with h | h
  · rcases Nat.lt_or_ge (n+1) s with h' | h'
    · simp [GeneratingSeries.pCoeff, show ¬ s+1 ≤ n+2 by omega, show ¬ s+1 ≤ n by
                                                           omega, show ¬ s ≤ n+1 by omega]
    · rcases Nat.lt_or_ge (n+1) (s+1) with h'' | h''
      · obtain rfl : s = n+1 := by omega
        simp only [GeneratingSeries.pCoeff, show n+1+1 ≤ n+2 by omega, show ¬ n+1+1 ≤ n by omega,
          show n+1 ≤ n+1 by omega, ↓reduceIte, Nat.sub_self, show n+2-(n+1+1) = 0 by omega]
        rw [show n+2+(n+1+1) = (2*n+1+1+1)+1 by ring, show n+1+(n+1) = 2*n+1+1 by ring,
          Nat.factorial_succ (2*n+1+1+1), Nat.factorial_succ (2*n+1+1), Nat.factorial_succ (n+1)]
        have := GeneratingSeries.factorial_ne (2*n+1+1); have := GeneratingSeries.factorial_ne (n+1)
        push_cast; field_simp; ring
      · obtain rfl : s = n := by omega
        simp only [GeneratingSeries.pCoeff, show s+1 ≤ s+2 by omega, show ¬ s+1 ≤ s by omega,
          show s ≤ s+1 by omega, ↓reduceIte, show s+2-(s+1) = 1 by omega,
          show s+1-s = 1 by omega]
        rw [show s+2+(s+1) = (2*s+1+1)+1 by ring, show s+1+s = 2*s+1 by ring,
          Nat.factorial_succ (2*s+1+1), Nat.factorial_succ (2*s+1), Nat.factorial_succ s]
        have := GeneratingSeries.factorial_ne (2*s+1); have := GeneratingSeries.factorial_ne s
        push_cast; field_simp; ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [GeneratingSeries.pCoeff, show s+1 ≤ s+1+d+2 by omega, show s+1 ≤ s+1+d by omega,
      show s ≤ s+1+d+1 by omega, ↓reduceIte,
      show s+1+d+2-(s+1) = d+2 by omega, show s+1+d-(s+1) = d by omega,
      show s+1+d+1-s = d+2 by omega]
    rw [show s+1+d+2+(s+1) = (2*s+d+2+1)+1 by ring, show s+1+d+(s+1) = 2*s+d+2 by ring,
      show s+1+d+1+s = 2*s+d+2 by ring,
      Nat.factorial_succ (2*s+d+2+1), Nat.factorial_succ (2*s+d+2), Nat.factorial_succ (d+1),
      Nat.factorial_succ d, Nat.factorial_succ s]
    have := GeneratingSeries.factorial_ne (2*s+d+2); have := GeneratingSeries.factorial_ne d;
        have := GeneratingSeries.factorial_ne s
    push_cast; field_simp; ring


/-- `GeneratingSeries.secondKindCoeff n 0 = H_n`, the `n`-th harmonic number. -/
theorem GeneratingSeries.secondKindCoeff_zero_right (n : ℕ) : GeneratingSeries.secondKindCoeff n 0 =
    harmonic n := by
  simp [GeneratingSeries.secondKindCoeff, GeneratingSeries.pCoeff_zero]

/-- For `n ≤ s`, `GeneratingSeries.secondKindCoeff n s = 0`. -/
theorem GeneratingSeries.secondKindCoeff_eq_zero {n s : ℕ} (h : n ≤ s) :
    GeneratingSeries.secondKindCoeff n s = 0 := by
  rcases h.lt_or_eq with h | rfl
  · simp [GeneratingSeries.secondKindCoeff, GeneratingSeries.pCoeff, show ¬ s ≤ n by omega]
  · simp [GeneratingSeries.secondKindCoeff]

/-- The coefficients `GeneratingSeries.secondKindCoeff n 0 = H_n` satisfy the Legendre recurrence
`(n+2)E_{n+2} = (2n+3)E_{n+1} - (n+1)E_n`. -/
theorem GeneratingSeries.secondKindCoeff_recurrence_zero (n : ℕ) :
    ((n:ℝ)+2) * GeneratingSeries.secondKindCoeff (n+2) 0 = (2*n+3) *
        GeneratingSeries.secondKindCoeff (n+1) 0 - ((n:ℝ)+1) *
        GeneratingSeries.secondKindCoeff n 0 := by
  simp only [GeneratingSeries.secondKindCoeff_zero_right, harmonic_succ]
  push_cast
  field_simp
  ring

/-- For `s ≥ 0`, `(n+2) E(n+2,s+1) = (2n+3)(E(n+1,s+1) + E(n+1,s)) - (n+1) E(n,s+1)`, the
coefficient form of the Legendre recurrence in powers of `z - 1`. -/
theorem GeneratingSeries.secondKindCoeff_recurrence_succ (n s : ℕ) :
    ((n:ℝ)+2) * GeneratingSeries.secondKindCoeff (n+2) (s+1) = (2*n+3) *
        (GeneratingSeries.secondKindCoeff (n+1) (s+1) + GeneratingSeries.secondKindCoeff (n+1) s) -
      ((n:ℝ)+1) * GeneratingSeries.secondKindCoeff n (s+1) := by
  have R1 := GeneratingSeries.pCoeff_recurrence n s
  have R2 := GeneratingSeries.pCoeff_diff n s
  simp only [GeneratingSeries.secondKindCoeff]
  have e1 : (harmonic (n+2) : ℝ) = harmonic (n+1) + 1/((n:ℝ)+2) := by
    rw [harmonic_succ]; push_cast; ring
  have e2 : (harmonic n : ℝ) = harmonic (n+1) - 1/((n:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; ring
  have e3 : (harmonic s : ℝ) = harmonic (s+1) - 1/((s:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; ring
  rw [e1, e2, e3]
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 : (n:ℝ)+2 ≠ 0 := by positivity
  have h3 : (s:ℝ)+1 ≠ 0 := by positivity
  rw [eq_div_iff h3] at R2
  have u1 := mul_inv_cancel₀ h1
  have u2 := mul_inv_cancel₀ h2
  have us := mul_inv_cancel₀ h3
  linear_combination ((harmonic (n+1):ℝ) - harmonic (s+1)) * R1 +
    GeneratingSeries.pCoeff (n+2) (s+1) * u2 - GeneratingSeries.pCoeff n (s+1) * u1 -
    (GeneratingSeries.pCoeff (n+2) (s+1) - GeneratingSeries.pCoeff n (s+1)) * us + ((s:ℝ)+1)⁻¹ * R2

/-- The explicit polynomial of DLMF 14.7.3 evaluated at `z`. -/
noncomputable def GeneratingSeries.secondKind (n : ℕ) (z : ℂ) : ℂ :=
  ∑ s ∈ Finset.range n, (GeneratingSeries.secondKindCoeff n s : ℂ) * (z-1)^s

/-- The sum defining `GeneratingSeries.secondKind n z` may be extended to `s < n + k`, since the
extra coefficients vanish. -/
theorem GeneratingSeries.secondKind_extend (n k : ℕ) (z : ℂ) :
    GeneratingSeries.secondKind n z = ∑ s ∈ Finset.range (n+k),
        (GeneratingSeries.secondKindCoeff n s : ℂ) * (z-1)^s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ih, ← add_assoc, Finset.sum_range_succ,
        GeneratingSeries.secondKindCoeff_eq_zero (by omega)]; simp

/-- The polynomials `GeneratingSeries.secondKind n` satisfy the Legendre recurrence
`(n+2)W_{n+2}(z) = (2n+3) z W_{n+1}(z) - (n+1) W_n(z)`. -/
theorem GeneratingSeries.secondKind_recurrence (n : ℕ) (z : ℂ) :
    ((n:ℂ)+2) * GeneratingSeries.secondKind (n+2) z = (2*n+3) * z *
        GeneratingSeries.secondKind (n+1) z - ((n:ℂ)+1) * GeneratingSeries.secondKind n z := by
  obtain ⟨t, rfl⟩ : ∃ t, z = 1 + t := ⟨z-1, by ring⟩
  rw [GeneratingSeries.secondKind_extend (n+2) 1, GeneratingSeries.secondKind_extend (n+1) 2,
      GeneratingSeries.secondKind_extend n 3]
  simp only [add_sub_cancel_left]
  have htE : t * ∑ s ∈ Finset.range (n+1+1), (GeneratingSeries.secondKindCoeff (n+1) s : ℂ) * t^s =
      ∑ s ∈ Finset.range (n+2), (GeneratingSeries.secondKindCoeff (n+1) s : ℂ) * t^(s+1) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
  have hE1 : ∑ s ∈ Finset.range (n+1+2), (GeneratingSeries.secondKindCoeff (n+1) s : ℂ) * t^s =
      ∑ s ∈ Finset.range (n+1+1), (GeneratingSeries.secondKindCoeff (n+1) s : ℂ) * t^s := by
    rw [show n+1+2 = n+1+1+1 by ring, Finset.sum_range_succ,
                                  GeneratingSeries.secondKindCoeff_eq_zero (by omega)]; simp
  rw [show (2*(n:ℂ)+3) * (1+t) * ∑ s ∈ Finset.range (n+1+2),
      (GeneratingSeries.secondKindCoeff (n+1) s : ℂ) * t^s =
      (2*(n:ℂ)+3) * (∑ s ∈ Finset.range (n+1+2),
          (GeneratingSeries.secondKindCoeff (n+1) s : ℂ) * t^s +
        t * ∑ s ∈ Finset.range (n+1+1), (GeneratingSeries.secondKindCoeff (n+1) s : ℂ) * t^s) by
            rw [hE1]; ring, htE]
  rw [show n+2+1 = n+2+1 by rfl, show n+1+2 = n+2+1 by ring, show n+3 = n+2+1 by ring,
    Finset.sum_range_succ' _ (n+2), Finset.sum_range_succ' _ (n+2), Finset.sum_range_succ' _ (n+2)]
  have key : ∀ s ∈ Finset.range (n+2),
      ((n:ℂ)+2) * ((GeneratingSeries.secondKindCoeff (n+2) (s+1) : ℂ) * t^(s+1)) =
        (2*n+3) * ((GeneratingSeries.secondKindCoeff (n+1) (s+1) : ℂ) * t^(s+1) +
            (GeneratingSeries.secondKindCoeff (n+1) s : ℂ) * t^(s+1)) -
          ((n:ℂ)+1) * ((GeneratingSeries.secondKindCoeff n (s+1) : ℂ) * t^(s+1)) := by
    intro s _
    have := congrArg (fun r : ℝ => (r : ℂ)) (GeneratingSeries.secondKindCoeff_recurrence_succ n s)
    push_cast at this
    linear_combination t^(s+1) * this
  have key0 := congrArg (fun r : ℝ => (r : ℂ)) (GeneratingSeries.secondKindCoeff_recurrence_zero n)
  push_cast at key0
  rw [mul_add ((n:ℂ)+2), Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [pow_zero, mul_one]
  linear_combination key0

/-- The explicit polynomial of DLMF 14.7.3 equals `R_n = legendreQPoly n`: `∑_{s<n} A(n,s)(H_n -
H_s)(z-1)^s = R_n(z)`. -/
theorem GeneratingSeries.secondKind_eq (n : ℕ) (z : ℂ) : GeneratingSeries.secondKind n z =
    (legendreQPoly n).eval z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [GeneratingSeries.secondKind, legendreQPoly]
    | 1, _ =>
      simp [GeneratingSeries.secondKind, legendreQPoly, GeneratingSeries.secondKindCoeff_zero_right]
    | n+2, ih =>
      have e := GeneratingSeries.secondKind_recurrence n z
      rw [ih n (by omega), ih (n+1) (by omega)] at e
      have hn : (n:ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+1)
      rw [legendreQPoly]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      rw [eq_inv_mul_iff_mul_eq₀ hn, e]

/-! ### Generating functions of `W_{n-1}` and of `Q_n` (DLMF 14.7.20, 14.7.22) -/

/-- Absolute convergence of `∑ P_n(z) hⁿ` inside the circle of the two roots. -/
theorem GeneratingSeries.summable_generatingSeries (z ζ₁ ζ₂ h : ℂ) (hs : ζ₁ + ζ₂ = 2*z)
    (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖h*ζ₁‖ < 1) (h2 : ‖h*ζ₂‖ < 1) :
    Summable fun n => ‖GeneratingSeries.legendreSeq z n * h^n‖ := by
  have hs1 := GeneratingSeries.summable_binomialSeries ζ₁ h h1
  have hs2 := GeneratingSeries.summable_binomialSeries ζ₂ h h2
  refine (summable_norm_sum_mul_antidiagonal_of_summable_norm hs1 hs2).congr fun n => ?_
  congr 1
  rw [show GeneratingSeries.legendreSeq z n =
      PowerSeries.coeff n (GeneratingSeries.generatingSeries z) by
      simp [GeneratingSeries.generatingSeries],
    ← GeneratingSeries.binomialSeries_mul z ζ₁ ζ₂ hs hp, PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring

/-- The `n`-th term of `GeneratingSeries.primitiveSeries z` satisfies
`‖f_n hⁿ‖ ≤ ‖h‖ ‖P_{n-1}(z) h^{n-1}‖`. -/
theorem GeneratingSeries.norm_coeff_primitiveSeries_le (z h : ℂ) (n : ℕ) :
    ‖PowerSeries.coeff n (GeneratingSeries.primitiveSeries z) * h^n‖ ≤ ‖h‖ *
        ‖GeneratingSeries.legendreSeq z (n-1) * h^(n-1)‖ := by
  simp only [GeneratingSeries.primitiveSeries, PowerSeries.coeff_mk]
  rcases n with _ | n
  · simp; positivity
  · simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte, norm_mul, norm_div, norm_pow,
      Complex.norm_natCast, pow_succ]
    have : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
    have h0 : 0 ≤ ‖GeneratingSeries.legendreSeq z n‖ * (‖h‖^n * ‖h‖) := by positivity
    calc ‖GeneratingSeries.legendreSeq z n‖ / ((n+1:ℕ):ℝ) * (‖h‖^n * ‖h‖) =
           (‖GeneratingSeries.legendreSeq z n‖ * (‖h‖^n * ‖h‖)) /
           ((n+1:ℕ):ℝ) := by ring
      _ ≤ ‖GeneratingSeries.legendreSeq z n‖ * (‖h‖^n * ‖h‖) := div_le_self h0 this
      _ = _ := by ring

/-- If `ζ₁ + ζ₂ = 2z`, `ζ₁ζ₂ = 1` and `‖hζ₁‖, ‖hζ₂‖ < 1`, then `∑ f_n hⁿ` for
`GeneratingSeries.primitiveSeries z` converges absolutely. -/
theorem GeneratingSeries.summable_primitiveSeries (z ζ₁ ζ₂ h : ℂ) (hs : ζ₁ + ζ₂ = 2*z)
    (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖h*ζ₁‖ < 1) (h2 : ‖h*ζ₂‖ < 1) :
    Summable fun n => ‖PowerSeries.coeff n (GeneratingSeries.primitiveSeries z) * h^n‖ := by
  have hG := GeneratingSeries.summable_generatingSeries z ζ₁ ζ₂ h hs hp h1 h2
  have hG' : Summable fun n => ‖h‖ * ‖GeneratingSeries.legendreSeq z (n-1) * h^(n-1)‖ := by
    refine Summable.mul_left _ ?_
    rw [← summable_nat_add_iff 1]
    simpa using hG
  exact hG'.of_nonneg_of_le (fun _ => norm_nonneg _)
      (GeneratingSeries.norm_coeff_primitiveSeries_le z h)

/-- Cauchy product: `∑ W_{n-1}(z) hⁿ = (∑ F_n hⁿ) (1-2zh+h²)^{-1/2}`. -/
theorem GeneratingSeries.hasSum_secondKind (z ζ₁ ζ₂ h : ℂ) (hs : ζ₁ + ζ₂ = 2*z) (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖h*ζ₁‖ < 1) (h2 : ‖h*ζ₂‖ < 1) :
    HasSum (fun n => (legendreQPoly n).eval z * h^n)
      ((∑' n, PowerSeries.coeff n (GeneratingSeries.primitiveSeries z) * h^n) *
          (1 - 2*z*h + h^2)^(-1/2:ℂ)) := by
  have hF := GeneratingSeries.summable_primitiveSeries z ζ₁ ζ₂ h hs hp h1 h2
  have hG := GeneratingSeries.summable_generatingSeries z ζ₁ ζ₂ h hs hp h1 h2
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF hG
  rw [(GeneratingSeries.generating z ζ₁ ζ₂ h hs hp h1 h2).tsum_eq] at hprod
  rw [hprod]
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hF hG).of_norm
  refine (hsum.hasSum).congr_fun fun n => ?_
  rw [← GeneratingSeries.product_eq z n, PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; simp [GeneratingSeries.generatingSeries]; ring

/-- Derivative of the closed form `log(1+x) - log(x - t + √(1-2xt+t²))`. -/
theorem GeneratingSeries.hasDerivAt_closedForm {x t : ℝ} (hq : 0 < 1-2*x*t+t^2)
    (hl : 0 < x - t + √(1-2*x*t+t^2)) :
    HasDerivAt (fun s : ℝ => Real.log (1+x) - Real.log (x - s + √(1-2*x*s+s^2)))
      (1 / √(1-2*x*t+t^2)) t := by
  have hQ : HasDerivAt (fun s : ℝ => 1-2*x*s+s^2) (-2*x + 2*t) t := by
    have := (((hasDerivAt_id' t).const_mul (2*x)).const_sub 1).add (hasDerivAt_pow 2 t)
    convert this using 1; push_cast; ring
  have hS := hQ.sqrt hq.ne'
  have hU : HasDerivAt (fun s : ℝ => x - s + √(1-2*x*s+s^2))
      (-1 + (-2*x + 2*t) / (2 * √(1-2*x*t+t^2))) t := by
    exact ((hasDerivAt_id' t).const_sub x).add hS
  have hL := (hU.log hl.ne').const_sub (Real.log (1+x))
  refine hL.congr_deriv ?_
  have hsq : 0 < √(1-2*x*t+t^2) := Real.sqrt_pos.mpr hq
  have hsq2 := Real.sq_sqrt hq.le
  field_simp
  ring

/-- `∑ P_{n-1}(x) tⁿ / n = log(1+x) - log(x - t + √(1-2xt+t²))` for real `t` in a disc where the
binomial factors converge and the logarithm is real. -/
theorem GeneratingSeries.tsum_primitiveSeries_real {x r : ℝ} (ζ₁ ζ₂ : ℂ) (hs : ζ₁ + ζ₂ = 2*x)
    (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖(r:ℂ)*ζ₁‖ < 1) (h2 : ‖(r:ℂ)*ζ₂‖ < 1)
    (hq : ∀ t : ℝ, |t| < r → 0 < 1-2*x*t+t^2)
    (hl : ∀ t : ℝ, |t| < r → 0 < x - t + √(1-2*x*t+t^2)) {t : ℝ} (ht : |t| < r) :
    ∑' n, PowerSeries.coeff n (GeneratingSeries.primitiveSeries x) * (t:ℂ)^n =
      ((Real.log (1+x) - Real.log (x - t + √(1-2*x*t+t^2)) : ℝ) : ℂ) := by
  set c : ℕ → ℂ := fun n => PowerSeries.coeff n (GeneratingSeries.primitiveSeries x) with hc
  have hc0 : c 0 = 0 := by simp [hc, GeneratingSeries.primitiveSeries]
  have hcn : ∀ n : ℕ, c (n+1) * ((n+1:ℕ):ℂ) = GeneratingSeries.legendreSeq x n := fun n => by
    simp only [hc, GeneratingSeries.primitiveSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero,
        ↓reduceIte, Nat.add_sub_cancel]
    have : ((n+1:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    field_simp
  set S : Set ℝ := Ioo (-r) r
  have hSo : IsOpen S := isOpen_Ioo
  have hSc : IsPreconnected S := isPreconnected_Ioo
  have hmem : ∀ y ∈ S, |y| < r := fun y hy => abs_lt.mpr hy
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg t) ht
  have h0S : (0:ℝ) ∈ S := ⟨by linarith, hr0⟩
  have htS : t ∈ S := abs_lt.mp ht
  have hnorm : ∀ y : ℝ, |y| < r → ∀ ζ : ℂ, ‖(r:ℂ)*ζ‖ < 1 → ‖(y:ℂ)*ζ‖ < 1 := fun y hy ζ hζ => by
    refine lt_of_le_of_lt ?_ hζ
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs,
      abs_of_pos hr0]
    exact mul_le_mul_of_nonneg_right hy.le (norm_nonneg _)
  -- termwise derivative
  set g : ℕ → ℝ → ℂ := fun n y => c n * (y:ℂ)^n
  set g' : ℕ → ℝ → ℂ := fun n y => c n * ((n:ℂ) * (y:ℂ)^(n-1))
  have hg : ∀ n y, y ∈ S → HasDerivAt (g n) (g' n y) y := fun n y _ =>
    ((hasDerivAt_pow n (y:ℂ)).comp_ofReal).const_mul (c n)
  set u : ℕ → ℝ := fun n => ‖GeneratingSeries.legendreSeq x (n-1) * (r:ℂ)^(n-1)‖
  have hu : Summable u := by
    rw [← summable_nat_add_iff 1]
    simpa [u] using GeneratingSeries.summable_generatingSeries x ζ₁ ζ₂ r hs hp h1 h2
  have hg' : ∀ n y, y ∈ S → ‖g' n y‖ ≤ u n := fun n y hy => by
    rcases n with _ | n
    · simp [g', hc0, u]
    · simp only [g', u, Nat.add_sub_cancel]
      rw [← mul_assoc, hcn, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr0]
      gcongr
      exact (hmem y hy).le
  have hsum0 : Summable fun n => g n 0 := by
    refine (summable_of_ne_finset_zero (s := {0}) fun n hn => ?_)
    rcases n with _ | n
    · simp at hn
    · simp [g]
  have hD : ∀ y ∈ S, HasDerivAt (fun z => ∑' n, g n z) ((1 - 2*(x:ℂ)*y + (y:ℂ)^2)^(-1/2:ℂ)) y := by
    intro y hy
    have := hasDerivAt_tsum_of_isPreconnected hu hSo hSc hg hg' h0S hsum0 hy
    convert this using 1
    have hsg : Summable fun n => g' n y :=
      Summable.of_norm_bounded hu fun n => hg' n y hy
    rw [hsg.tsum_eq_zero_add]
    simp only [g', hc0, zero_mul, zero_add, Nat.add_sub_cancel]
    rw [← (GeneratingSeries.generating x ζ₁ ζ₂ y hs hp (hnorm y (hmem y hy) ζ₁ h1)
      (hnorm y (hmem y hy) ζ₂ h2)).tsum_eq]
    refine tsum_congr fun n => ?_
    rw [← mul_assoc, hcn]
  set Φf : ℝ → ℂ := fun y => ((Real.log (1+x) - Real.log (x - y + √(1-2*x*y+y^2)) : ℝ) : ℂ)
  have hΦ : ∀ y ∈ S, HasDerivAt Φf ((1 - 2*(x:ℂ)*y + (y:ℂ)^2)^(-1/2:ℂ)) y := by
    intro y hy
    have := (GeneratingSeries.hasDerivAt_closedForm (hq y (hmem y hy))
        (hl y (hmem y hy))).ofReal_comp
    convert this using 1
    have hq0 := (hq y (hmem y hy)).le
    rw [show (1 - 2*(x:ℂ)*y + (y:ℂ)^2) = ((1-2*x*y+y^2 : ℝ) : ℂ) by push_cast; ring,
      show (-1/2:ℂ) = ((-1/2:ℝ):ℂ) by push_cast; ring, ← Complex.ofReal_cpow hq0,
      Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hq0]
    norm_num
  have heq := hSo.eqOn_of_deriv_eq hSc (f := fun z => ∑' n, g n z) (g := Φf)
    (fun y hy => (hD y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hΦ y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => by simp only [(hD y hy).deriv, (hΦ y hy).deriv]) h0S (by
      have : (fun n => g n 0) = fun _ => 0 := funext fun n => by
        rcases n with _ | n
        · simp [g, hc0]
        · simp [g]
      simp only [this, tsum_zero, Φf]
      norm_num [show x - 0 + √1 = 1 + x by simp; ring]
      rw [add_comm x 1, sub_self])
  exact heq htS

/-- Combination of the generating functions of `P_n` and `W_{n-1}` for real `x` and `h`. -/
theorem GeneratingSeries.hasSum_legendreQ_real {x h r : ℝ} (ζ₁ ζ₂ : ℂ) (hs : ζ₁ + ζ₂ = 2*x)
    (hp : ζ₁ * ζ₂ = 1)
    (h1 : ‖(r:ℂ)*ζ₁‖ < 1) (h2 : ‖(r:ℂ)*ζ₂‖ < 1)
    (hq : ∀ t : ℝ, |t| < r → 0 < 1-2*x*t+t^2)
    (hl : ∀ t : ℝ, |t| < r → 0 < x - t + √(1-2*x*t+t^2)) (hh : |h| < r) (c : ℂ) :
    HasSum (fun n : ℕ =>
        (c * GeneratingSeries.legendreSeq x n - (legendreQPoly n).eval (x:ℂ)) * (h:ℂ)^n)
      ((c - ((Real.log (1+x) - Real.log (x - h + √(1-2*x*h+h^2)) : ℝ) : ℂ)) *
        (1-2*x*h+h^2:ℂ)^(-1/2:ℂ)) := by
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg h) hh
  have hn : ∀ ζ : ℂ, ‖(r:ℂ)*ζ‖ < 1 → ‖(h:ℂ)*ζ‖ < 1 := fun ζ hζ => by
    refine lt_of_le_of_lt ?_ hζ
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs,
      abs_of_pos hr0]
    exact mul_le_mul_of_nonneg_right hh.le (norm_nonneg _)
  have hP := (GeneratingSeries.generating x ζ₁ ζ₂ h hs hp (hn ζ₁ h1) (hn ζ₂ h2)).mul_left c
  have hW := GeneratingSeries.hasSum_secondKind x ζ₁ ζ₂ h hs hp (hn ζ₁ h1) (hn ζ₂ h2)
  rw [GeneratingSeries.tsum_primitiveSeries_real ζ₁ ζ₂ hs hp h1 h2 hq hl hh] at hW
  convert hP.sub hW using 1
  · funext n; ring
  · ring

end DLMF.Legendre
