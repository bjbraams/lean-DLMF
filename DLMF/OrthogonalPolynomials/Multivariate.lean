/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Integrals
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Disk and triangle orthogonal polynomials

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.

The disk proof uses Mathlib’s polar-coordinate integration formula; the triangle proof
uses Mathlib’s Jacobian change-of-variables theorem. Both separate into the proved
one-variable Jacobi orthogonality integrals using `MeasureTheory.integral_prod_mul`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Set
open scoped Real Nat Topology
open DLMF.Hypergeometric

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

@[dlmf 18.37.E6]
def diskPolynomial (α : ℂ) (m n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (min m n + 1), (-1 : ℂ) ^ j * poch (α + 1) (m + n - j) *
    poch (-(m : ℂ)) j * poch (-(n : ℂ)) j /
    (poch (α + 1) m * poch (α + 1) n * j.factorial) * z ^ (m - j) * star z ^ (n - j)

/-- Triangle polynomials: the meaningful degree range is `n ≤ m`. The product
at `x = 0` is used only off the boundary in the integral statements below. -/
@[dlmf 18.37.E7]
def trianglePolynomial (α β γ : ℂ) (m n : ℕ) (x y : ℂ) : ℂ :=
  jacobiPolyP α (β + γ + 2 * n + 1) (m - n) (2 * x - 1) * x ^ n *
    jacobiPolyP β γ n (2 * y / x - 1)

/-- Reversed Jacobi coefficients in the normalization of the disk polynomials. -/
theorem jacobi_disk_coefficients {α : ℂ} (hα : -1 < α.re) {m n : ℕ} (hmn : n ≤ m) (s : ℂ) :
    jacobiPolyP α ((m - n : ℕ) : ℂ) n (2 * s - 1) / jacobiPolyP α ((m - n : ℕ) : ℂ) n 1 =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * poch (α + 1) (m + n - j) *
        poch (-(m : ℂ)) j * poch (-(n : ℂ)) j /
          (poch (α + 1) m * poch (α + 1) n * j.factorial) * s ^ (n - j) := by
  have hd : -1 < ((m - n : ℕ) : ℂ).re := by
    simp only [natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) (m - n)]
  have hnp : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  have hp (k : ℕ) := poch_ne_zero_of_not_neg_nat hnp k
  have hf (k : ℕ) : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [show 2 * s - 1 = -(1 - 2 * s) by ring, jacobi_reflection hα hd,
    jacobi_finite_sum hd, jacobi_at_one hα,
    show (1 - 2 * s - 1) / 2 = -s by ring, Finset.mul_sum, Finset.sum_div]
  conv_lhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjm : j ≤ m := hjn.trans hmn
  rw [show n + 1 - 1 - j = n - j by omega,
    show n - (n - j) = j by omega]
  have hbase : (n : ℂ) + (m - n : ℕ) + α + 1 = α + 1 + m := by
    rw [Nat.cast_sub hmn]; ring
  rw [hbase]
  have hpos : poch ((m - n : ℕ) + (n - j : ℕ) + 1 : ℂ) j =
      (m.factorial : ℂ) / (m - j).factorial := by
    rw [show ((m - n : ℕ) : ℂ) + (n - j : ℕ) + 1 = ((m - j + 1 : ℕ) : ℂ) by
      push_cast; rw [Nat.cast_sub hmn, Nat.cast_sub hjn, Nat.cast_sub hjm]; ring,
      poch, ascPochhammer_nat_eq_natCast_descFactorial,
      show m - j + 1 + j - 1 = m by omega]
    rw [Nat.descFactorial_eq_div hjm, Nat.cast_div
      (Nat.factorial_dvd_factorial (Nat.sub_le m j)) (hf _)]
  have hsplit : poch (α + 1) (m + n - j) = poch (α + 1) m * poch (α + 1 + m) (n - j) := by
    rw [show m + n - j = m + (n - j) by omega, poch_add]
  have hpm := poch_neg_nat_mul_factorial hjm
  have hpn := poch_neg_nat_mul_factorial hjn
  have hm' : poch (-(m : ℂ)) j = (-1) ^ j * m.factorial / (m - j).factorial :=
    (eq_div_iff (hf _)).mpr hpm
  have hn' : poch (-(n : ℂ)) j = (-1) ^ j * n.factorial / (n - j).factorial :=
    (eq_div_iff (hf _)).mpr hpn
  rw [hpos, hsplit, hm', hn', neg_pow]
  have hsgn : (-1 : ℂ) ^ n = (-1) ^ j * (-1) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjn]
  have hsgn2 (k : ℕ) : (-1 : ℂ) ^ (k * 2) = 1 := by
    rw [Nat.mul_comm, pow_mul]; norm_num
  rw [hsgn]
  field_simp [hp, hf]
  ring_nf
  simp only [hsgn2, mul_one]

/-- Factor the larger holomorphic degree from the finite disk polynomial. -/
theorem diskPolynomial_eq_jacobi_of_le {α : ℂ} (hα : -1 < α.re) {m n : ℕ} (hmn : n ≤ m) (z : ℂ) :
    diskPolynomial α m n z = z ^ (m - n) *
      (jacobiPolyP α ((m - n : ℕ) : ℂ) n (2 * (z * star z) - 1) / jacobiPolyP α ((m - n : ℕ) : ℂ) n 1) := by
  rw [jacobi_disk_coefficients hα hmn, Finset.mul_sum, diskPolynomial, min_eq_right hmn]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [mul_pow, ← mul_assoc, ← mul_assoc]
  have he : z ^ (m - j) = z ^ (m - n) * z ^ (n - j) := by
    rw [← pow_add]; congr 1; omega
  rw [he]
  ring

/-- Exchange the two disk degrees by conjugating the argument. -/
theorem diskPolynomial_swap (α : ℂ) (m n : ℕ) (z : ℂ) :
    diskPolynomial α m n z = diskPolynomial α n m (star z) := by
  unfold diskPolynomial
  rw [min_comm n m]
  apply Finset.sum_congr rfl
  intro j hj
  rw [star_star, Nat.add_comm n m]
  ring


@[dlmf 18.37.E1]
theorem diskPolynomial_polar {α : ℝ} (hα : -1 < α) (m n : ℕ) (r θ : ℝ) (_hr : 0 ≤ r) :
    diskPolynomial α m n ((r : ℂ) * exp (I * θ)) =
      exp (I * ((m : ℂ) - n) * θ) * (r : ℂ) ^ (Int.natAbs ((m : ℤ) - n)) *
      jacobiPolyP α (Int.natAbs ((m : ℤ) - n)) (min m n) (2 * (r : ℂ) ^ 2 - 1) /
      jacobiPolyP α (Int.natAbs ((m : ℤ) - n)) (min m n) 1 := by
  have hα' : -1 < (α : ℂ).re := by simpa using hα
  have hstar : star ((r : ℂ) * exp (I * θ)) = (r : ℂ) * exp (-(I * θ)) := by
    simp [star_mul, ← exp_conj, mul_comm]
  have hprod : ((r : ℂ) * exp (I * θ)) * star ((r : ℂ) * exp (I * θ)) = (r : ℂ) ^ 2 := by
    rw [hstar]
    calc
      _ = (r : ℂ) ^ 2 * (exp (I * θ) * exp (-(I * θ))) := by ring
      _ = _ := by rw [← exp_add]; simp
  rcases le_total n m with hnm | hmn
  · have habs : Int.natAbs ((m : ℤ) - n) = m - n := by
      rw [← Int.natCast_sub hnm, Int.natAbs_natCast]
    rw [diskPolynomial_eq_jacobi_of_le hα' hnm, hprod, habs, min_eq_right hnm, mul_pow]
    have he : exp (I * θ) ^ (m - n) = exp (I * ((m : ℂ) - n) * θ) := by
      rw [← exp_nat_mul, Nat.cast_sub hnm]
      congr 1
      ring
    rw [he]
    ring
  · have habs : Int.natAbs ((m : ℤ) - n) = n - m := by
      rw [← Int.natAbs_neg, neg_sub, ← Int.natCast_sub hmn, Int.natAbs_natCast]
    rw [diskPolynomial_swap, diskPolynomial_eq_jacobi_of_le hα' hmn]
    have hprod' : star ((r : ℂ) * exp (I * θ)) * star (star ((r : ℂ) * exp (I * θ))) =
        (r : ℂ) ^ 2 := by rw [star_star, mul_comm]; exact hprod
    rw [hprod', habs, min_eq_left hmn, hstar, mul_pow]
    have he : exp (-(I * θ)) ^ (n - m) = exp (I * ((m : ℂ) - n) * θ) := by
      rw [← exp_nat_mul, Nat.cast_sub hmn]
      congr 1
      ring
    rw [he]
    ring

@[dlmf 18.37.E5]
theorem diskPolynomial_at_one {α : ℂ} (hα : -1 < α.re) (m n : ℕ) : diskPolynomial α m n 1 = 1 := by
  have hnp : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hm := poch_ne_zero_of_not_neg_nat hnp m
  have hn := poch_ne_zero_of_not_neg_nat hnp n
  unfold diskPolynomial
  simp only [one_pow, mul_one, star_one]
  have hsub : ∑ j ∈ Finset.range (min m n + 1), (-1 : ℂ) ^ j * poch (α + 1) (m + n - j) *
      poch (-(m : ℂ)) j * poch (-(n : ℂ)) j / (poch (α + 1) m * poch (α + 1) n * j.factorial) =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * poch (α + 1) (m + n - j) *
      poch (-(m : ℂ)) j * poch (-(n : ℂ)) j / (poch (α + 1) m * poch (α + 1) n * j.factorial) := by
    apply Finset.sum_subset
    · intro j hj; simp at hj ⊢; omega
    · intro j hj hj'
      simp at hj hj'
      have : m < j := by omega
      rw [poch_neg_nat_eq_zero this]; simp
  rw [hsub]
  have key : ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * poch (α + 1) (m + n - j) *
      poch (-(m : ℂ)) j * poch (-(n : ℂ)) j / (poch (α + 1) m * poch (α + 1) n * j.factorial) =
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * poch (-(m : ℂ)) j * poch (α + 1 + m) (n - j)) /
        poch (α + 1) n := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsplit : poch (α + 1) (m + n - j) = poch (α + 1) m * poch (α + 1 + m) (n - j) := by
      rw [show m + n - j = m + (n - j) by omega, poch_add]
    have hpn : poch (-(n : ℂ)) j = (-1) ^ j * (j.factorial * n.choose j : ℕ) := by
      rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
    have hf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    have hs : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [hsplit, hpn]
    push_cast
    field_simp
    linear_combination (poch (α + 1 + m) (n - j) * poch (-(m : ℂ)) j * (n.choose j : ℂ)) * hs
  rw [key, poch_add_binomial, show -(m : ℂ) + (α + 1 + m) = α + 1 by ring, div_self hn]

/-- Shifted Jacobi orthogonality on the open unit interval. -/
theorem jacobi_unit_orthogonal {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    {m n : ℕ} (hmn : m ≠ n) :
    (∫ t : ℝ in Ioo 0 1,
      jacobiPolyP α β m (2 * t - 1) * jacobiPolyP α β n (2 * t - 1) *
        ((1 - t) ^ α * t ^ β : ℝ)) = 0 := by
  have hlt (m n : ℕ) (hmn : m < n) :
      (∫ t : ℝ in Ioo 0 1,
        jacobiPolyP α β m (2 * t - 1) * jacobiPolyP α β n (2 * t - 1) *
          ((1 - t) ^ α * t ^ β : ℝ)) = 0 := by
    have hi := jacobi_shifted_orthogonal hβ hα hmn
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo] at hi
    let C : ℂ := (-1) ^ m * (-1) ^ n *
      (poch ((β : ℂ) + 1) m / m.factorial) * (poch ((β : ℂ) + 1) n / n.factorial)
    calc
      _ = C * ∫ t : ℝ in Ioo 0 1,
          (t : ℂ) ^ (β : ℂ) * (1 - (t : ℂ)) ^ (α : ℂ) *
            ₂F₁ (-(n : ℂ)) (n + β + α + 1) (β + 1) (t : ℂ) *
            ₂F₁ (-(m : ℂ)) (m + β + α + 1) (β + 1) (t : ℂ) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        dsimp only
        have he : (2 : ℂ) * t - 1 = -(1 - 2 * t) := by ring
        rw [he, jacobi_reflection (by simpa using hα) (by simpa using hβ),
          jacobi_reflection (by simpa using hα) (by simpa using hβ)]
        simp only [jacobiPolyP, show (1 - (1 - 2 * (t : ℂ))) / 2 = t by ring]
        rw [ofReal_mul, ofReal_cpow ht.1.le, ofReal_cpow (sub_nonneg.mpr ht.2.le)]
        simp only [ofReal_sub, ofReal_one]
        dsimp [C]
        ring
      _ = 0 := by rw [hi, mul_zero]
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hlt m n h
  · calc
      _ = ∫ t : ℝ in Ioo 0 1,
          jacobiPolyP α β n (2 * t - 1) * jacobiPolyP α β m (2 * t - 1) *
            ((1 - t) ^ α * t ^ β : ℝ) :=
          setIntegral_congr_fun measurableSet_Ioo fun t _ => by ring
      _ = 0 := hlt n m h

/-- The differential of the map from a square to a triangle. -/
private def triangleMapDeriv (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![1, 0; p.2, p.1]).toContinuousLinearMap

/-- The map `(x,u) ↦ (x,xu)` has Jacobian determinant `x`. -/
private lemma hasFDerivAt_triangleMap (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => (q.1, q.1 * q.2)) (triangleMapDeriv p) p := by
  unfold triangleMapDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)
  have hg := hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)
  convert hf.prodMk (hf.mul hg) using 1
  simp [add_comm]

/-- Determinant of the square-to-triangle differential. -/
private lemma det_triangleMapDeriv (p : ℝ × ℝ) : (triangleMapDeriv p).det = p.1 := by
  simp [triangleMapDeriv, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]

/-- The square-to-triangle map is injective away from `x=0`. -/
private lemma triangleMap_injOn : InjOn (fun p : ℝ × ℝ => (p.1, p.1 * p.2))
    (Ioo 0 1 ×ˢ Ioo 0 1) := by
  intro p hp q hq he
  have hx := congrArg (fun r : ℝ × ℝ => r.1) he
  have hy := congrArg (fun r : ℝ × ℝ => r.2) he
  dsimp only at hx hy
  apply Prod.ext hx
  rw [← hx] at hy
  exact mul_left_cancel₀ hp.1.1.ne' hy

/-- The square-to-triangle map covers the open triangle exactly. -/
private lemma triangleMap_image : (fun p : ℝ × ℝ => (p.1, p.1 * p.2)) ''
    (Ioo 0 1 ×ˢ Ioo 0 1) = {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < 1} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨mul_pos hq.1.1 hq.2.1, (mul_lt_iff_lt_one_right hq.1.1).mpr hq.2.2, hq.1.2⟩
  · intro hp
    have hx : 0 < p.1 := hp.1.trans hp.2.1
    refine ⟨(p.1, p.2 / p.1), ⟨⟨hx, hp.2.2⟩, ?_⟩, ?_⟩
    · exact ⟨div_pos hp.1 hx, (div_lt_one hx).mpr hp.2.1⟩
    · apply Prod.ext
      · rfl
      · dsimp only
        field_simp

/-- Change of variables from the open triangle to the open square. -/
private lemma integral_triangle (f : ℝ × ℝ → ℂ) :
    (∫ p in {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < 1}, f p) =
      ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, (p.1 : ℂ) * f (p.1, p.1 * p.2) := by
  -- Mathlib Jacobian formula for the square-to-triangle map.
  rw [← triangleMap_image,
    integral_image_eq_integral_abs_det_fderiv_smul volume
      (measurableSet_Ioo.prod measurableSet_Ioo)
      (fun p _ => (hasFDerivAt_triangleMap p).hasFDerivWithinAt) triangleMap_injOn]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro p hp
  dsimp only
  rw [det_triangleMapDeriv, abs_of_pos hp.1.1, real_smul]

/-- Products separated in the two coordinates integrate as a product. -/
private lemma integral_unit_square_mul (f g : ℝ → ℂ) :
    (∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, f p.1 * g p.2) =
      (∫ x in Ioo (0 : ℝ) 1, f x) * ∫ u in Ioo (0 : ℝ) 1, g u := by
  change (∫ p, f p.1 * g p.2 ∂((volume : Measure ℝ).prod volume).restrict _) = _
  rw [← Measure.prod_restrict]
  exact integral_prod_mul f g
/-- Polar change of variables restricted to the open unit disk. -/
private lemma integral_unit_disk_polar (f : ℝ × ℝ → ℂ) :
    (∫ p : ℝ × ℝ in {p | p.1 ^ 2 + p.2 ^ 2 < 1}, f p) =
      ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 : ℂ) * f (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by
  let S : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 < 1}
  let R : Set (ℝ × ℝ) := {p | p.1 < 1}
  have hs : MeasurableSet S := (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hr : MeasurableSet R := (isOpen_lt continuous_fst continuous_const).measurableSet
  -- Restrict Mathlib’s polar-coordinate integration formula with an indicator.
  rw [← integral_indicator hs, ← integral_comp_polarCoord_symm]
  have he : (∫ p in polarCoord.target, p.1 • S.indicator f (polarCoord.symm p)) =
      ∫ p in polarCoord.target, R.indicator
        (fun p => (p.1 : ℂ) * f (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) p := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    have hr0 : 0 < p.1 := hp.1
    have hsq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq p.2]
    have hm : polarCoord.symm p ∈ S ↔ p ∈ R := by
      change (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 < 1 ↔ p.1 < 1
      rw [hsq]
      constructor <;> intro h <;> nlinarith
    dsimp only
    by_cases h : polarCoord.symm p ∈ S
    · rw [indicator_of_mem h, indicator_of_mem (hm.mp h), real_smul]
      rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (hm.not.mp h), smul_zero]
  rw [he, setIntegral_indicator hr]
  have hset : polarCoord.target ∩ R = Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [R, polarCoord_target, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioi, mem_Ioo]
    tauto
  rw [hset]

/-- The nonconstant integral Fourier modes have zero angular mean. -/
private lemma integral_exp_int_mode {l : ℤ} (hl : l ≠ 0) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, exp (I * (l : ℂ) * θ)) = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  rw [integral_exp_mul_complex (mul_ne_zero I_ne_zero (Int.cast_ne_zero.mpr hl))]
  have he : exp (I * (l : ℂ) * Real.pi) = exp (I * (l : ℂ) * (-Real.pi)) := by
    apply (div_eq_one_iff_eq (exp_ne_zero _)).mp
    rw [← exp_sub]
    have harg : I * (l : ℂ) * Real.pi - I * (l : ℂ) * (-Real.pi) =
        (l : ℂ) * (2 * Real.pi * I) := by ring
    rw [harg, exp_int_mul_two_pi_mul_I]
  simp only [ofReal_neg]
  rw [he, sub_self, zero_div]

/-- Squaring the radius in a disk integral contributes the factor `1/2`. -/
private lemma integral_radius_sq (F : ℝ → ℂ) :
    (∫ r : ℝ in Ioo 0 1, (r : ℂ) * F (r ^ 2)) =
      (1 / 2 : ℂ) * ∫ t : ℝ in Ioo 0 1, F t := by
  have hd : ∀ r ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * r) (Ioo 0 1) r := by
    intro r _
    simpa using (hasDerivAt_pow 2 r).hasDerivWithinAt (s := Ioo 0 1)
  have hinj : InjOn (fun r : ℝ => r ^ 2) (Ioo 0 1) := by
    intro r hr s hs h
    exact (pow_left_inj₀ hr.1.le hs.1.le two_ne_zero).mp h
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj F
  rw [square_image_Ioo] at he
  rw [he, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  dsimp only
  rw [abs_of_pos (mul_pos two_pos hr.1), real_smul]
  push_cast
  ring

/-- Orthogonality on the disk, by Fourier modes and radial Jacobi orthogonality. -/
@[dlmf 18.37.E2]
theorem diskPolynomial_orthogonal {α : ℝ} (hα : -1 < α) (m n j k : ℕ) (hne : (m, n) ≠ (j, k)) :
    ∫ p : ℝ × ℝ in {p | p.1 ^ 2 + p.2 ^ 2 < 1},
      diskPolynomial α m n (p.1 + I * p.2) * diskPolynomial α j k (p.1 - I * p.2) *
        (Real.rpow (1 - p.1 ^ 2 - p.2 ^ 2) α : ℂ) = 0 := by
  let d := Int.natAbs ((m : ℤ) - n)
  let e := Int.natAbs ((j : ℤ) - k)
  let l : ℤ := (m : ℤ) - n - ((j : ℤ) - k)
  let A : ℂ := jacobiPolyP α d (min m n) 1
  let B : ℂ := jacobiPolyP α e (min j k) 1
  let F (r : ℝ) : ℂ := (r : ℂ) ^ (d + e + 1) *
    jacobiPolyP α d (min m n) (2 * (r : ℂ) ^ 2 - 1) *
    jacobiPolyP α e (min j k) (2 * (r : ℂ) ^ 2 - 1) *
    ((1 - r ^ 2) ^ α : ℝ) / (A * B)
  let G (θ : ℝ) : ℂ := exp (I * (l : ℂ) * θ)
  have hsep : (∫ p : ℝ × ℝ in {p | p.1 ^ 2 + p.2 ^ 2 < 1},
      diskPolynomial α m n (p.1 + I * p.2) * diskPolynomial α j k (p.1 - I * p.2) *
        (Real.rpow (1 - p.1 ^ 2 - p.2 ^ 2) α : ℂ)) =
      (∫ r in Ioo (0 : ℝ) 1, F r) * ∫ θ in Ioo (-Real.pi) Real.pi, G θ := by
    rw [integral_unit_disk_polar]
    have hp : (∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi, F p.1 * G p.2) =
        (∫ r in Ioo (0 : ℝ) 1, F r) * ∫ θ in Ioo (-Real.pi) Real.pi, G θ := by
      change (∫ p, F p.1 * G p.2 ∂((volume : Measure ℝ).prod volume).restrict _) = _
      rw [← Measure.prod_restrict]
      exact integral_prod_mul F G
    rw [← hp]
    apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    dsimp only [Prod.fst, Prod.snd]
    have hz : ((r * Real.cos θ : ℝ) : ℂ) + I * ((r * Real.sin θ : ℝ) : ℂ) =
        (r : ℂ) * exp (I * θ) := by
      rw [mul_comm I (θ : ℂ), exp_mul_I]
      push_cast
      ring
    have hw : ((r * Real.cos θ : ℝ) : ℂ) - I * ((r * Real.sin θ : ℝ) : ℂ) =
        (r : ℂ) * exp (I * (-θ : ℝ)) := by
      rw [mul_comm I ((-θ : ℝ) : ℂ), exp_mul_I]
      simp only [ofReal_neg, cos_neg, sin_neg]
      push_cast
      ring
    have hsq : 1 - (r * Real.cos θ) ^ 2 - (r * Real.sin θ) ^ 2 = 1 - r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [hz, hw, hsq, diskPolynomial_polar hα m n r θ hr.1.le,
      diskPolynomial_polar hα j k r (-θ) hr.1.le]
    have hexp : exp (I * ((m : ℂ) - n) * θ) * exp (I * ((j : ℂ) - k) * (-θ : ℝ)) = G θ := by
      rw [← exp_add]
      dsimp [G, l]
      push_cast
      congr 1
      ring
    calc
      _ = F r * (exp (I * ((m : ℂ) - n) * θ) * exp (I * ((j : ℂ) - k) * (-θ : ℝ))) := by
        dsimp [F, A, B, d, e]
        simp only [pow_add, pow_one]
        ring
      _ = F r * G θ := by rw [hexp]
  rw [hsep]
  by_cases hl : l = 0
  · have hdiff : (m : ℤ) - n = (j : ℤ) - k := sub_eq_zero.mp hl
    have hde : d = e := congrArg Int.natAbs hdiff
    have hdeg : min m n ≠ min j k := by
      intro heq
      apply hne
      have hmj : m = j := by omega
      have hnk : n = k := by omega
      exact Prod.ext hmj hnk
    let H (t : ℝ) : ℂ := jacobiPolyP α d (min m n) (2 * t - 1) *
      jacobiPolyP α d (min j k) (2 * t - 1) * ((1 - t) ^ α * t ^ (d : ℝ) : ℝ)
    have hrad : (∫ r in Ioo (0 : ℝ) 1, F r) =
        (1 / (A * B) : ℂ) * (1 / 2 : ℂ) * ∫ t in Ioo (0 : ℝ) 1, H t := by
      rw [mul_assoc, ← integral_radius_sq, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp [F, H]
      rw [← hde, Real.rpow_natCast]
      push_cast
      simp only [pow_add, pow_one]
      ring
    have hd : -1 < (d : ℝ) := by have := Nat.cast_nonneg (α := ℝ) d; linarith
    rw [hrad, show (∫ t in Ioo (0 : ℝ) 1, H t) = 0 from jacobi_unit_orthogonal hα hd hdeg,
      mul_zero, zero_mul]
  · rw [show (∫ θ in Ioo (-Real.pi) Real.pi, G θ) = 0 from integral_exp_int_mode hl, mul_zero]

/-- Orthogonality of the triangle polynomials, by separation on the unit square. -/
@[dlmf 18.37.E8]
theorem trianglePolynomial_orthogonal {α β γ : ℝ} (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ)
    {m n j k : ℕ} (hn : n ≤ m) (hk : k ≤ j) (hne : (m, n) ≠ (j, k)) :
    ∫ p : ℝ × ℝ in {p | 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < 1},
      trianglePolynomial α β γ m n p.1 p.2 * trianglePolynomial α β γ j k p.1 p.2 *
      (Real.rpow (1 - p.1) α * Real.rpow (p.1 - p.2) β * Real.rpow p.2 γ : ℝ) = 0 := by
  let B (l : ℕ) : ℝ := β + γ + 2 * l + 1
  let F (x : ℝ) : ℂ := jacobiPolyP α (B n) (m - n) (2 * x - 1) *
    jacobiPolyP α (B k) (j - k) (2 * x - 1) *
    ((1 - x) ^ α * x ^ (β + γ + (n : ℝ) + k + 1) : ℝ)
  let G (u : ℝ) : ℂ := jacobiPolyP β γ n (2 * u - 1) *
    jacobiPolyP β γ k (2 * u - 1) * ((1 - u) ^ β * u ^ γ : ℝ)
  have he : (∫ p : ℝ × ℝ in {p | 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < 1},
      trianglePolynomial α β γ m n p.1 p.2 * trianglePolynomial α β γ j k p.1 p.2 *
      (Real.rpow (1 - p.1) α * Real.rpow (p.1 - p.2) β * Real.rpow p.2 γ : ℝ)) =
      (∫ x in Ioo (0 : ℝ) 1, F x) * ∫ u in Ioo (0 : ℝ) 1, G u := by
    rw [integral_triangle, ← integral_unit_square_mul]
    apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
    rintro ⟨x, u⟩ ⟨hx, hu⟩
    dsimp only [Prod.fst, Prod.snd]
    have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
    have hw : (1 - x) ^ α * (x - x * u) ^ β * (x * u) ^ γ =
        (1 - x) ^ α * x ^ β * (1 - u) ^ β * x ^ γ * u ^ γ := by
      rw [show x - x * u = x * (1 - u) by ring,
        Real.mul_rpow hx.1.le (sub_nonneg.mpr hu.2.le), Real.mul_rpow hx.1.le hu.1.le]
      ring
    dsimp [F, G, B, trianglePolynomial]
    rw [hw]
    simp only [Real.rpow_add hx.1, Real.rpow_natCast, Real.rpow_one]
    push_cast
    have ha : 2 * ((x : ℂ) * u) / x - 1 = 2 * u - 1 := by field_simp
    rw [ha]
    ring
  rw [he]
  by_cases hnk : n = k
  · subst k
    have hdeg : m - n ≠ j - n := by intro h; apply hne; congr 1; omega
    have hb : -1 < B n := by dsimp [B]; have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hf : (∫ x in Ioo (0 : ℝ) 1, F x) = 0 := by
      have hp : β + γ + (n : ℝ) + n + 1 = B n := by dsimp [B]; ring
      simpa only [F, hp] using jacobi_unit_orthogonal hα hb hdeg
    rw [hf, zero_mul]
  · rw [show (∫ u in Ioo (0 : ℝ) 1, G u) = 0 from jacobi_unit_orthogonal hβ hγ hnk, mul_zero]


end DLMF.OrthogonalPolynomials
