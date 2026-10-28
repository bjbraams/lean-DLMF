/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Classical
public import DLMF.OrthogonalPolynomials.JacobiDiscriminant
public import DLMF.Selberg.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Applications of the Selberg integral (AAR §§8.5–8.11)

Stieltjes electrostatics, Siegel's inequality, Dyson's constant-term identity, the
Hasse–Davenport relation for Gauss sums (Mathlib already defines `gaussSum`), and the
finite-field analogue of Selberg.

The discriminant of a Jacobi polynomial (AAR Theorem 8.5.3) is
`DLMF.OrthogonalPolynomials.jacobiPolyP_prod_sq_sub`, proved by Schur's resultant route. The
nearly poised `₃F₂(1)` of Theorem 8.9.1(a) is proved here from Aomoto's integral. Siegel's
inequality, the Hasse–Davenport relation and the finite-field Selberg formula remain admitted.
-/

@[expose] public section

open Complex
open scoped Real Nat
open DLMF.OrthogonalPolynomials
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Selberg

/-- The polynomial `P_n(t)` in AAR (8.6.2), p. 420. -/
def siegelP (n : ℕ) (t : ℝ) : ℝ :=
  1 / (n.factorial : ℝ) *
    ∏ k ∈ Finset.range (n - 1), ((t + k) / ((n : ℝ) - k)) ^ (n - k - 1)

/-- The rational function `Q_n(t)` in AAR (8.6.3), p. 420. -/
def siegelQ (n : ℕ) (t : ℝ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 (n - 1), (1 + ((n : ℝ) - k) / (t + k - 1))

/-- The squared Vandermonde product `Δ` used in AAR §8.6, p. 420. -/
def siegelDiscriminant {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i.val < j.val then (x i - x j) ^ 2 else 1

/-- Siegel's refinement of the arithmetic–geometric mean inequality, AAR Theorem 8.6.2,
p. 420. The positive parameter `μ` satisfies (8.6.4). -/
theorem siegel_inequality {n : ℕ} (hn : 2 ≤ n) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) (hΔ : siegelDiscriminant x ≠ 0)
    {μ : ℝ} (hμ : 0 < μ)
    (hroot : siegelP n μ = (∏ i, x i) ^ (n - 1) / siegelDiscriminant x) :
    (∏ i, x i) * siegelQ n μ ≤ ((∑ i, x i) / (n : ℝ)) ^ n := by
  sorry

/-- For two distinct positive numbers, Siegel's bound is an equality. In fact only
the nonzero discriminant, nonzero parameter, and defining equation are needed. -/
theorem siegel_inequality_two {x : Fin 2 → ℝ} {μ : ℝ}
    (hΔ : siegelDiscriminant x ≠ 0) (hμ : μ ≠ 0)
    (hroot : siegelP 2 μ = (∏ i, x i) / siegelDiscriminant x) :
    (∏ i, x i) * siegelQ 2 μ = ((∑ i, x i) / 2) ^ 2 := by
  have hd : (x 0 - x 1) ^ 2 ≠ 0 := by
    simpa [siegelDiscriminant, Fin.prod_univ_two] using hΔ
  norm_num [siegelP, siegelDiscriminant, Fin.prod_univ_two] at hroot
  norm_num [siegelQ, Fin.prod_univ_two, Fin.sum_univ_two]
  field_simp [hd] at hroot
  rw [eq_div_iff hd] at hroot
  field_simp [hμ]
  nlinarith [hroot]

/-- The complex factorial quotient equals the corresponding multinomial coefficient.
This is an algebraic ingredient for Dyson's identity; it does not compute a Laurent
polynomial constant term. -/
theorem factorial_sum_div_prod_factorial {n : ℕ} (a : Fin n → ℕ) :
    ((∑ i, a i).factorial : ℂ) / ∏ i, (a i).factorial = Nat.multinomial Finset.univ a := by
  -- Already known in Mathlib as `Nat.multinomial_spec`.
  have hden : (∏ i, ((a i).factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (a i).factorial_ne_zero
  rw [Nat.cast_prod]
  apply (div_eq_iff hden).mpr
  have h := congrArg (fun k : ℕ => (k : ℂ)) (Nat.multinomial_spec Finset.univ a)
  simpa [Nat.cast_mul, Nat.cast_prod, mul_comm] using h.symm

/-! ### A nearly poised `₃F₂(1)`

AAR's proof of Theorem 8.9.1(a): Aomoto's integral with `n = 2`, one linear factor `t₀` and
`c = k`, expanded by the binomial theorem in `(t₀ - t₁)^{2k}`, is a finite sum of products of
two Beta integrals. Dividing by the `r = 0` term gives the nearly poised series. -/

namespace NearlyPoised

open MeasureTheory Set
open DLMF.Gamma (Gamma_add_nat_eq_poch_mul_Gamma poch_neg_eq)

/-- The binomial theorem with Pochhammer coefficients. -/
theorem sub_pow_eq_sum_poch (x y : ℂ) (n : ℕ) :
    (x - y) ^ n = ∑ r ∈ Finset.range (n + 1), poch (-(n : ℂ)) r / r ! * (x ^ (n - r) * y ^ r) := by
  rw [sub_eq_neg_add, add_pow]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr : (r ! : ℂ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose, neg_pow]
  push_cast
  field_simp

/-- For `x > 0`, multiplying the Selberg weight by `xᵖ` shifts `a` to `a + p`. -/
theorem weight_mul_pow_eq {a b : ℂ} (p : ℕ) {x : ℝ} (hx : 0 < x) :
    weight a b x * (x : ℂ) ^ p = weight (a + p) b x := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold weight
  rw [mul_right_comm, ← cpow_natCast, ← cpow_add _ _ hx0]
  ring_nf

/-- For `Re a, Re b > 0`, `x^{a-1}(1-x)^{b-1} xᵖ` is integrable on `[0,1]`. -/
theorem integrableOn_weight_mul_pow {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (p : ℕ) :
    IntegrableOn (fun x : ℝ => weight a b x * (x : ℂ) ^ p) (Icc (0 : ℝ) 1) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  have h : IntegrableOn (weight (a + p) b) (Ioc (0 : ℝ) 1) :=
    (integrableOn_weight (by simp; positivity) hb).mono_set Ioc_subset_Icc_self
  exact h.congr_fun (fun x hx => (weight_mul_pow_eq p hx.1).symm) measurableSet_Ioc

/-- `∫₀¹ x^{a-1}(1-x)^{b-1} xᵖ dx = B(a + p, b)`. -/
theorem integral_weight_mul_pow {a b : ℂ} (p : ℕ) :
    ∫ x in Icc (0 : ℝ) 1, weight a b x * (x : ℂ) ^ p = betaIntegral (a + p) b := by
  rw [integral_Icc_eq_integral_Ioc, betaIntegral, intervalIntegral.integral_of_le zero_le_one]
  exact setIntegral_congr_fun measurableSet_Ioc fun x hx => weight_mul_pow_eq p hx.1

/-- `f(t₀) g(t₁)` written as a product over `Fin 2`. -/
theorem prod_fin_two_eq {f g : ℝ → ℂ} (t : Fin 2 → ℝ) :
    f (t 0) * g (t 1) = ∏ i : Fin 2, (![f, g] i) (t i) := by
  simp [Fin.prod_univ_two]

/-- A product `f(t₀) g(t₁)` of integrable functions is integrable on `[0,1]²`. -/
theorem integrableOn_cube_two {f g : ℝ → ℂ} (hf : IntegrableOn f (Icc (0 : ℝ) 1))
    (hg : IntegrableOn g (Icc (0 : ℝ) 1)) :
    IntegrableOn (fun t : Fin 2 → ℝ => f (t 0) * g (t 1)) (cube 2) := by
  simp_rw [prod_fin_two_eq]
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi]
  refine Integrable.fintype_prod_dep fun i => ?_
  fin_cases i
  · exact hf
  · exact hg

/-- Fubini on `[0,1]²` for a product `f(t₀) g(t₁)`. -/
theorem integral_cube_two {f g : ℝ → ℂ} :
    ∫ t in cube 2, f (t 0) * g (t 1) =
      (∫ x in Icc (0 : ℝ) 1, f x) * ∫ x in Icc (0 : ℝ) 1, g x := by
  simp_rw [prod_fin_two_eq]
  rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  simp [Fin.prod_univ_two]

/-- For `c = k` natural, the two-variable Vandermonde factor is `(t₀ - t₁)^{2k}`. -/
theorem vdm_two (k : ℕ) (t : Fin 2 → ℝ) :
    vdm 2 (k : ℂ) t = ((t 0 : ℂ) - t 1) ^ (2 * k) := by
  simp only [vdm, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, lt_irrefl, ite_false,
    zero_lt_one, ite_true, not_lt_zero, one_mul, mul_one]
  rw [show (2 * (k : ℂ)) = ((2 * k : ℕ) : ℂ) by push_cast; ring, cpow_natCast]
  rw [← ofReal_pow, (Even.pow_abs ⟨k, by ring⟩ _), ofReal_pow]
  push_cast; ring


/-- One term of the expanded Aomoto integral. -/
theorem term_eq {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) (k r : ℕ) (hr : r ≤ 2 * k) :
    poch (-((2 * k : ℕ) : ℂ)) r / r ! *
        (betaIntegral (α + ((2 * k - r + 1 : ℕ) : ℂ)) β * betaIntegral (α + r) β) =
      betaIntegral (α + 2 * k + 1) β * betaIntegral α β *
        (poch (-(2 * k : ℂ)) r * poch α r * poch (-α - β - 2 * k) r /
          (poch (-α - 2 * k) r * poch (α + β) r * (r ! : ℂ))) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set A : ℂ := α + ((2 * k - r + 1 : ℕ) : ℂ) with hAdef
  have hA : A = α + 2 * k + 1 - r := by
    rw [hAdef, Nat.cast_add, Nat.cast_sub hr]; push_cast; ring
  have hAre : 0 < A.re := by
    rw [hAdef]; simp only [add_re, natCast_re]; positivity
  have hABre : 0 < (A + β).re := by simp only [add_re]; linarith
  have hαr : 0 < (α + r).re := by simp; positivity
  have hαβ : 0 < (α + β).re := by simp only [add_re]; linarith
  have h1 : α + 2 * k + 1 = A + r := by rw [hA]; ring
  have hP1 : poch (-α - 2 * k) r = (-1) ^ r * poch A r := by
    rw [show -α - 2 * (k : ℂ) = -(α + 2 * k) by ring, poch_neg_eq, hA]; ring_nf
  have hP2 : poch (-α - β - 2 * k) r = (-1) ^ r * poch (A + β) r := by
    rw [show -α - β - 2 * (k : ℂ) = -(α + β + 2 * k) by ring, poch_neg_eq, hA]; ring_nf
  rw [betaIntegral_eq_Gamma_mul_div _ _ hAre hβ, betaIntegral_eq_Gamma_mul_div _ _ hαr hβ,
    betaIntegral_eq_Gamma_mul_div _ _ (by rw [h1]; simp; positivity) hβ,
    betaIntegral_eq_Gamma_mul_div _ _ hα hβ, h1, show A + (r : ℂ) + β = (A + β) + r by ring,
    Gamma_add_nat_eq_poch_mul_Gamma hAre, Gamma_add_nat_eq_poch_mul_Gamma hABre,
    show α + r + β = (α + β) + r by ring, Gamma_add_nat_eq_poch_mul_Gamma (k := r) hα,
    Gamma_add_nat_eq_poch_mul_Gamma (k := r) hαβ, hP1, hP2]
  have hGA := Gamma_ne_zero_of_re_pos hAre
  have hGAB := Gamma_ne_zero_of_re_pos hABre
  have hGb := Gamma_ne_zero_of_re_pos hβ
  have hGa := Gamma_ne_zero_of_re_pos hα
  have hGab := Gamma_ne_zero_of_re_pos hαβ
  have hpA := poch_ne_zero_of_re_pos hAre r
  have hpAB := poch_ne_zero_of_re_pos hABre r
  have hpa := poch_ne_zero_of_re_pos hα r
  have hpab := poch_ne_zero_of_re_pos hαβ r
  have hf : (r ! : ℂ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  push_cast
  field_simp


/-- The Aomoto integral with `n = 2`, one linear factor and `c = k`, expanded by the binomial
theorem: a sum of products of two Beta integrals. -/
theorem aomoto_two_expand {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) (k : ℕ) :
    ∫ t : Fin 2 → ℝ in Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1,
        selbergIntegrand 2 α β k t * ∏ i : Fin 1, (t (Fin.castLE (by norm_num) i) : ℂ) =
      ∑ r ∈ Finset.range (2 * k + 1), poch (-((2 * k : ℕ) : ℂ)) r / r ! *
        (betaIntegral (α + ((2 * k - r + 1 : ℕ) : ℂ)) β * betaIntegral (α + r) β) := by
  have hpt : ∀ t : Fin 2 → ℝ,
      selbergIntegrand 2 α β k t * ∏ i : Fin 1, (t (Fin.castLE (by norm_num) i) : ℂ) =
        ∑ r ∈ Finset.range (2 * k + 1), poch (-((2 * k : ℕ) : ℂ)) r / r ! *
          ((weight α β (t 0) * (t 0 : ℂ) ^ (2 * k - r + 1)) *
            (weight α β (t 1) * (t 1 : ℂ) ^ r)) := by
    intro t
    rw [selbergIntegrand_eq, vdm_two, sub_pow_eq_sum_poch, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Fin.prod_univ_two, Fin.prod_univ_one]
    have : (Fin.castLE (by norm_num : 1 ≤ 2) (0 : Fin 1)) = 0 := rfl
    rw [this, pow_succ]
    ring
  change ∫ t in cube 2, _ = _
  rw [setIntegral_congr_fun (measurableSet_cube 2) fun t _ => hpt t]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_const_mul,
      integral_cube_two (f := fun x => weight α β x * (x : ℂ) ^ (2 * k - r + 1))
      (g := fun x => weight α β x * (x : ℂ) ^ r), integral_weight_mul_pow, integral_weight_mul_pow]
  · intro r _
    exact (integrableOn_cube_two (integrableOn_weight_mul_pow hα hβ _)
      (integrableOn_weight_mul_pow hα hβ r)).const_mul _


/-- The Aomoto evaluation divided by the two Beta factors. -/
theorem final_identity {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) (k : ℕ) :
    betaIntegral (α + 2 * k + 1) β * betaIntegral α β *
      (poch (α + 1) k * poch β k * poch 1 (2 * k) /
        (poch (α + β) k * poch 1 k * poch (α + 1) (2 * k))) =
    (∏ j : Fin 1, (α + ((2 - 1 - j : ℕ) : ℂ) * k) / (α + β + ((2 * 2 - 2 - j : ℕ) : ℂ) * k)) *
      ∏ j : Fin 2,
        Gamma (α + (j : ℕ) * k) * Gamma (β + (j : ℕ) * k) * Gamma (1 + ((j : ℕ) + 1) * k) /
          (Gamma (α + β + (2 + j - 1 : ℕ) * k) * Gamma (1 + k)) := by
  simp only [Fin.prod_univ_one, Fin.prod_univ_two]
  norm_num
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ha1 : 0 < (α + 1).re := by simp; linarith
  have hab : 0 < (α + β).re := by simp; linarith
  have hab2 : 0 < (α + β + 2 * k).re := by simp; linarith
  have hak : 0 < (α + k).re := by simp; linarith
  have hb1 : 0 < (α + 2 * k + 1).re := by simp; linarith
  rw [betaIntegral_eq_Gamma_mul_div _ _ hb1 hβ, betaIntegral_eq_Gamma_mul_div _ _ hα hβ]
  have e1 : Gamma (α + 2 * k + 1) = poch (α + 1) (2 * k) * (α * Gamma α) := by
    rw [← Gamma_add_one α (ne_zero_of_re_pos hα), ← Gamma_add_nat_eq_poch_mul_Gamma ha1]
    push_cast; ring_nf
  have e2 : Gamma (α + 2 * k + 1 + β) = (α + β + 2 * k) * Gamma (α + β + 2 * k) := by
    rw [← Gamma_add_one _ (ne_zero_of_re_pos hab2)]; ring_nf
  have e3 : Gamma (α + k) = poch (α + 1) k * (α * Gamma α) / (α + k) := by
    rw [eq_div_iff (ne_zero_of_re_pos hak), mul_comm, ← Gamma_add_one _ (ne_zero_of_re_pos hak),
      ← Gamma_add_one α (ne_zero_of_re_pos hα), ← Gamma_add_nat_eq_poch_mul_Gamma ha1]
    ring_nf
  have e4 : Gamma (β + k) = poch β k * Gamma β := Gamma_add_nat_eq_poch_mul_Gamma hβ k
  have e5 : Gamma (α + β + k) = poch (α + β) k * Gamma (α + β) :=
    Gamma_add_nat_eq_poch_mul_Gamma hab k
  have e6 : Gamma (1 + k) = k ! := by
    rw [add_comm, Gamma_nat_eq_factorial]
  have e7 : Gamma (1 + 2 * k) = ((2 * k) ! : ℕ) := by
    rw [add_comm, show (2 * k : ℂ) = ((2 * k : ℕ) : ℂ) by push_cast; ring, Gamma_nat_eq_factorial]
  rw [e1, e2, e3, e4, e5, e6, e7]
  have := Gamma_ne_zero_of_re_pos hα
  have := Gamma_ne_zero_of_re_pos hβ
  have := Gamma_ne_zero_of_re_pos hab
  have := Gamma_ne_zero_of_re_pos hab2
  have := ne_zero_of_re_pos hα
  have := ne_zero_of_re_pos hak
  have := ne_zero_of_re_pos hab2
  have := poch_ne_zero_of_re_pos ha1 k
  have := poch_ne_zero_of_re_pos ha1 (2 * k)
  have := poch_ne_zero_of_re_pos hab k
  have : ((k ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have : (((2 * k) ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (2 * k).factorial_ne_zero
  field_simp

end NearlyPoised

/-- A terminating nearly poised `₃F₂(1)` evaluation, AAR Theorem 8.9.1(a), p. 429.
Positive real parts suffice to keep all denominators in the finite sum nonzero.

The supplied AAR printing has an error: the last denominator factor is printed
as `(α)_{2k}`, but must be `(α + 1)_{2k}`. For `k = 1`, `α = 1/2`, `β = 1`,
the finite sum is `8/15`, whereas the printed right-hand side is `8/3`.
The corrected formula also appears as equation (20) in Nagar, Naranjo-Ríos and
Gupta, "Generalized Selberg Integral and Nearly Poised 3F2 Series" (2015). -/
theorem nearly_poised_3F2 {α β : ℂ} (k : ℕ)
    (hα : 0 < α.re) (hβ : 0 < β.re) :
    (∑ r ∈ Finset.range (2 * k + 1),
      poch (-(2 * k : ℂ)) r * poch α r * poch (-α - β - 2 * k) r /
        (poch (-α - 2 * k) r * poch (α + β) r * (r.factorial : ℂ))) =
      poch (α + 1) k * poch β k * poch 1 (2 * k) /
        (poch (α + β) k * poch 1 k * poch (α + 1) (2 * k)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [poch_zero]
  have hA := aomoto_integral (n := 2) (m := 1) (a := α) (b := β) (c := (k : ℂ)) (by norm_num)
    hα hβ (by simp; exact_mod_cast hk)
  rw [NearlyPoised.aomoto_two_expand hα hβ k, ← NearlyPoised.final_identity hα hβ k] at hA
  have hsum : ∑ r ∈ Finset.range (2 * k + 1), poch (-((2 * k : ℕ) : ℂ)) r / r ! *
      (betaIntegral (α + ((2 * k - r + 1 : ℕ) : ℂ)) β * betaIntegral (α + r) β) =
      betaIntegral (α + 2 * k + 1) β * betaIntegral α β *
        ∑ r ∈ Finset.range (2 * k + 1),
          poch (-(2 * k : ℂ)) r * poch α r * poch (-α - β - 2 * k) r /
            (poch (-α - 2 * k) r * poch (α + β) r * (r.factorial : ℂ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r hr =>
      NearlyPoised.term_eq hα hβ k r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
  rw [hsum] at hA
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hK0 : betaIntegral (α + 2 * k + 1) β * betaIntegral α β ≠ 0 := by
    rw [betaIntegral_eq_Gamma_mul_div _ _ (by simp; linarith) hβ,
      betaIntegral_eq_Gamma_mul_div _ _ hα hβ]
    have := Gamma_ne_zero_of_re_pos hα
    have := Gamma_ne_zero_of_re_pos hβ
    have : Gamma (α + 2 * k + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have : Gamma (α + 2 * k + 1 + β) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have : Gamma (α + β) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    simp_all
  exact mul_left_cancel₀ hK0 hA

/-- The Hasse–Davenport lifting relation, AAR Theorem 8.10.4, p. 432.
The sum on `E` uses the norm lift of `χ` and the trace lift of `ψ`, as in
(8.10.5)–(8.10.6). The extension degree `Module.finrank F E` is positive.
Over a finite field, nontriviality of the additive character is sufficient;
the identity also allows the trivial multiplicative character. -/
theorem hasse_davenport {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] [FiniteDimensional F E]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    (∑ x : E, χ (Algebra.norm F x) * ψ (Algebra.trace F E x)) =
      (-1 : ℂ) ^ (Module.finrank F E - 1) * gaussSum χ ψ ^ Module.finrank F E := by
  sorry

/-- The monic polynomial with a specified vector of lower coefficients. -/
def selbergMonicPolynomial {F : Type*} [Field F] {n : ℕ} (v : Fin n → F) : Polynomial F :=
  Polynomial.X ^ n + ∑ i, Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)

/-- Finite-field Selberg evaluation, AAR Theorem 8.11.2, with the sum (8.11.7).
AAR §8.10 specifies only a nontrivial multiplicative character, but §8.11 uses
`χ^((q-1)/2)` as the quadratic character and tests exponents modulo `q-1`.
Here `χ` is required to have order `q-1`, as needed for those uses. -/
theorem selberg_finite_field {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : orderOf χ = Fintype.card F - 1) (hψ : ψ.IsPrimitive)
    (hodd : Odd (Fintype.card F)) {n a b c : ℕ}
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hparams : ∀ j : Fin n,
      ¬(Fintype.card F - 1) ∣ (a + (j : ℕ) * c) ∧
      ¬(Fintype.card F - 1) ∣ (b + (j : ℕ) * c) ∧
      ¬(Fintype.card F - 1) ∣ (((j : ℕ) + 1) * c)) :
    (∑ v : Fin n → F,
      let f := selbergMonicPolynomial v
      χ ((-1 : F) ^ (n * a) * f.eval 0 ^ a * f.eval 1 ^ b * f.discr ^ c) *
        (χ ^ ((Fintype.card F - 1) / 2)) f.discr) =
      let gstar := fun m : ℕ => (Fintype.card F : ℂ) / gaussSum ((χ ^ m)⁻¹) ψ
      ∏ j : Fin n,
        gstar (a + (j : ℕ) * c) * gstar (b + (j : ℕ) * c) * gstar (((j : ℕ) + 1) * c) /
          (gstar (a + b + (n - 1 + j : ℕ) * c) * gstar c) := by
  sorry

end DLMF.Selberg
