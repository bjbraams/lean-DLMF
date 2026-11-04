/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Convergence
public import DLMF.QHypergeometric.QuintupleProduct
public import DLMF.QHypergeometric.VeryWellPoisedSums

/-!
# Bilateral basic summations and continuation (DLMF §17.8)

This file proves the bilateral summation formulas of DLMF §17.8, from Ramanujan's `₁ψ₁` sum to
Bailey's `₆ψ₆` sum, together with the quintuple product identity, and shows that the product
sides continue the bilateral series analytically.

## Main definitions

* `qRamanujanValue`, `qBilateralTwoValue`, `qBilateralThreeValue`, `qBilateralFourValue`,
  `qBilateralSixValue`, `qBilateralEvenValue`: the product quotients of the summations.
* `qQuintupleExponent`: the integer triangular exponent in the quintuple product.

## Main results

* `ramanujan_one_psi_one`: Ramanujan's `₁ψ₁` summation for `|b/a| < |z| < 1` (DLMF 17.8.2).
* `quintuple_product`: the quintuple product identity (DLMF 17.8.3).
* `bilateral_two_sum`, `bilateral_three_sum`, `bilateral_four_sum`, `bilateral_six_sum`,
  `bilateral_even_sum`: DLMF 17.8.4–17.8.8.
* `ramanujan_continues`, `bilateral_two_continues`, `bilateral_three_continues`,
  `bilateral_four_continues`, `bilateral_six_continues`, `bilateral_even_continues`: the
  product sides continue the bilateral series analytically.

## Implementation notes

The series are asserted only on their convergence annuli. Analytic continuation is recorded
for their germs using TauCeti's `ContinuesInside` API, so a divergent `tsum` value is never
confused with the continued value. Cancelled product forms retain upper-parameter cases where
the displayed quotient has a removable `0/0`.

The `₃ψ₃` sum (DLMF 17.8.5) is the limit `a → 1` of the very-well-poised `₆φ₅` sum
`six_phi_five_sum`, taken after clearing the lower-parameter products so that the terms stay
bounded near `a = 1`.

For DLMF 17.8.8 the annulus of convergence additionally requires `|c/b²| < 1`. The weaker
printed inequality `|cq²/b²| < 1` describes a larger continuation region, not convergence of
the bilateral sum. The Jacobi triple product is `DLMF.QSeries.jacobi_triple_product`.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- Ramanujan's product quotient, giving continuation of one-psi-one. -/
def qRamanujanValue (a b q z : ℂ) : ℂ :=
  qPochhammerListInf [q,b/a,a*z,q/(a*z)] q/qPochhammerListInf [b,q/a,z,b/(a*z)] q
/-- The product quotient in the bilateral two-psi-two sum. -/
def qBilateralTwoValue (a b c q : ℂ) : ℂ :=
  qPochhammerInf (a*q/(b*c)) q*qPochhammerListInf [a*q^2/b^2,a*q^2/c^2,q^2,a*q,q/a] (q^2)/
    qPochhammerListInf [a*q/b,a*q/c,q/b,q/c,-a*q/(b*c)] q
/-- The product quotient in the bilateral three-psi-three sum. -/
def qBilateralThreeValue (b c d q : ℂ) : ℂ :=
  qPochhammerListInf [q,q/(b*c),q/(b*d),q/(c*d)] q/qPochhammerListInf [q/b,q/c,q/d,q/(b*c*d)] q
/-- Four-psi-four products with both removable square-root quotient factors cancelled. -/
def qBilateralFourValue (a b c d q : ℂ) : ℂ :=
  let r := Complex.sqrt a
  let t := Complex.sqrt q
  qPochhammerListInf [r*t, -r*t, -r*q, t/r, -t/r, -q/r, a*q/(b*c), a*q/(b*d), a*q/(c*d), q*r/b,
      q*r/c, q*r/d, q] q/
    qPochhammerListInf [a*q/b,a*q/c,a*q/d,q/b,q/c,q/d,q*a*r/(b*c*d)] q
/-- Bailey's six-psi-six product quotient. -/
def qBilateralSixValue (a b c d e q : ℂ) : ℂ :=
  qPochhammerListInf [a*q,a*q/(b*c),a*q/(b*d),a*q/(b*e),a*q/(c*d),a*q/(c*e),a*q/(d*e),q,q/a] q/
    qPochhammerListInf [a*q/b,a*q/c,a*q/d,a*q/e,q/b,q/c,q/d,q/e,q*a^2/(b*c*d*e)] q
/-- The even-base two-psi-two product, with the b√q denominator factors cancelled. -/
def qBilateralEvenValue (b c q : ℂ) : ℂ :=
  qPochhammerListInf [q^2,q/b^2,c*q/b^2] (q^2)/
    (2*qPochhammerListInf [c*q,c*q^2/b^2,q^2/b^2,c/b^2] (q^2))*
      (qPochhammerInf (-b*Complex.sqrt q) q*qPochhammerInf (c*Complex.sqrt q/b) q+
       qPochhammerInf (b*Complex.sqrt q) q*qPochhammerInf (-c*Complex.sqrt q/b) q)
/-- The integer triangular exponent in the quintuple product. -/
def qQuintupleExponent (n : ℤ) : ℤ := n*(3*n-1)/2
/-- Ramanujan's `1ψ1` summation, valid for `|b/a| < |z| < 1` (DLMF 17.8.E2). -/
@[dlmf 17.8.E2]
theorem ramanujan_one_psi_one {a b q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hab : QBilateralRegular [a] [b] q) (hz : ‖b/a‖<‖z‖ ∧ ‖z‖<1) :
    qPsi [a] [b] q z=qRamanujanValue a b q z := by
  have h := ramanujan_1psi1_of_regular hq0 hq ha (fun n => hab.2 a (by simp) n)
    (fun n => hab.1 b (by simp) n) hz
  unfold qPsi qRamanujanValue
  simp only [qPsiTerm, qPochhammerListInt, qPsiExponent, qPochhammerListInf, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, List.length_singleton, sub_self,
    zpow_zero]
  rw [h]
  ring

/-- The quintuple product identity (DLMF 17.8.E3). -/
@[dlmf 17.8.E3]
theorem quintuple_product {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : z≠0) :
    HasSum (fun n : ℤ => (-1:ℂ)^n*q^qQuintupleExponent n*z^(3*n)*(1+z*q^n))
      (qPochhammerListInf [q,-z,-q/z] q*qPochhammerListInf [q*z^2,q/z^2] (q^2)) := by
  have h := QuintupleProduct.hasSum_quintuple hq0 hq hz
  convert h using 1
  · rfl
  · simp only [QuintupleProduct.productSide, qPochhammerListInf, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    ring

/-- The well-poised `2ψ2` summation (DLMF 17.8.E4). -/
@[dlmf 17.8.E4]
theorem bilateral_two_sum {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0) (hz : ‖q*a‖<‖b*c‖)
    (hreg : QBilateralRegular [b,c] [a*q/b,a*q/c] q) :
    qPsi [b,c] [a*q/b,a*q/c] q (-a*q/(b*c))=qBilateralTwoValue a b c q := by
  sorry

/-- A term of the very-well-poised `₆φ₅` series in the parameter `a`, multiplied by the
lower-parameter products; it is continuous at `a = 1`. -/
private noncomputable def threeClearedTerm (b c d q a : ℂ) (k : ℕ) : ℂ :=
  DLMF.Bailey.unitD a q k * qPochhammer b q k * qPochhammer c q k * qPochhammer d q k *
    qPochhammerInf (a*q/b*q^k) q * qPochhammerInf (a*q/c*q^k) q * qPochhammerInf (a*q/d*q^k) q /
    qPochhammer q q k * (a*q/(b*c*d))^k

/-- The lower-parameter products clearing the `₆φ₅` denominators. -/
private noncomputable def threeDen (b c d q a : ℂ) : ℂ :=
  qPochhammerInf (a*q/b) q * qPochhammerInf (a*q/c) q * qPochhammerInf (a*q/d) q

private lemma threeCleared_bound {b c d q : ℂ} (hq : ‖q‖ < 1) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (hz : ‖q‖ < ‖b*c*d‖) :
    ∃ δ > 0, ∃ M ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ a ∈ Metric.closedBall (1:ℂ) δ, ∀ k, ‖threeClearedTerm b c d q a k‖ ≤ M * ρ^k := by
  have hbcd : 0 < ‖b*c*d‖ := norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero hb hc) hd)
  set δ := (‖b*c*d‖ - ‖q‖)/(2*(‖q‖+1)) with hδ
  have hgap : 0 < ‖b*c*d‖ - ‖q‖ := by linarith
  have hδ0 : 0 < δ := div_pos hgap (by positivity)
  set R₁ := 1 + δ with hR₁
  have hqR : ‖q‖ * R₁ < ‖b*c*d‖ := by
    have : ‖q‖ * δ ≤ (‖b*c*d‖ - ‖q‖)/2 := by
      rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [norm_nonneg q]
    rw [hR₁]; nlinarith
  set ρ := ‖q‖ * R₁ / ‖b*c*d‖ with hρ
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hbcd]; exact hqR
  have hρ0 : 0 ≤ ρ := by positivity
  have hR0 : 0 ≤ R₁ := by positivity
  set Y := ‖q‖*R₁ + ‖b‖ + ‖c‖ + ‖d‖ + R₁*‖q‖/‖b‖ + R₁*‖q‖/‖c‖ + R₁*‖q‖/‖d‖ with hY
  set E := Real.exp (Y / (1 - ‖q‖)) with hE
  obtain ⟨C, hC⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq
    (qPochhammerInf_ne_zero_of_norm_lt_one hq hq)
  have hEP : ∀ x : ℂ, ‖x‖ ≤ Y → ∀ k, ‖qPochhammer x q k‖ ≤ E := fun x hx k =>
    (norm_qPochhammer_le_exp hq k).trans (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right hx (by linarith)))
  have hEI : ∀ x : ℂ, ‖x‖ ≤ Y → ‖qPochhammerInf x q‖ ≤ E := fun x hx =>
    (norm_qPochhammerInf_le_exp hq).trans (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right hx (by linarith)))
  have hpow : ∀ k : ℕ, ‖q‖^k ≤ 1 := fun k => pow_le_one₀ (norm_nonneg _) hq.le
  have hb0 : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hd0 : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hn1 : 0 ≤ R₁*‖q‖/‖b‖ := by positivity
  have hn2 : 0 ≤ R₁*‖q‖/‖c‖ := by positivity
  have hn3 : 0 ≤ R₁*‖q‖/‖d‖ := by positivity
  have hn4 : 0 ≤ ‖q‖*R₁ := by positivity
  have hbn := norm_nonneg b
  have hcn := norm_nonneg c
  have hdn := norm_nonneg d
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by have := hq; positivity)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨δ, hδ0, E^7 * (1 + R₁) * C, ρ, hρ0, hρ1, fun a ha k => ?_⟩
  have ha' : ‖a‖ ≤ R₁ := by
    rw [Metric.mem_closedBall, dist_eq_norm] at ha
    have := norm_le_norm_add_norm_sub' a 1
    rw [hR₁, ← norm_one (α := ℂ)]; linarith [norm_sub_rev a 1]
  have hqa : ‖q‖ * ‖a‖ ≤ ‖q‖ * R₁ := mul_le_mul_of_nonneg_left ha' (norm_nonneg q)
  have hU : ‖DLMF.Bailey.unitD a q k‖ ≤ E * (1 + R₁) := by
    rcases k with _ | k
    · simp only [DLMF.Bailey.unitD, norm_one]; nlinarith
    · simp only [DLMF.Bailey.unitD, norm_mul]
      have h1 : ‖qPochhammer (a*q) q k‖ ≤ E := hEP _ (by rw [norm_mul]; linarith) k
      have h2 : ‖1 - a*q^(2*(k+1))‖ ≤ 1 + R₁ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, norm_mul, norm_pow]
        nlinarith [hpow (2*(k+1)), norm_nonneg a, pow_nonneg (norm_nonneg q) (2*(k+1))]
      exact mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
  have a3 : ‖b‖ ≤ Y := by linarith
  have a4 : ‖c‖ ≤ Y := by linarith
  have a5 : ‖d‖ ≤ Y := by linarith
  have hsq : ∀ x : ℂ, 0 < ‖x‖ → ‖a*q/x*q^k‖ ≤ R₁*‖q‖/‖x‖ := by
    intro x hx
    rw [norm_mul, norm_div, norm_mul, norm_pow]
    have h1 : ‖a‖*‖q‖/‖x‖ ≤ R₁*‖q‖/‖x‖ := by gcongr
    have h2 : 0 ≤ ‖a‖*‖q‖/‖x‖ := by positivity
    nlinarith [hpow k, pow_nonneg (norm_nonneg q) k]
  have a6 : ‖a*q/b*q^k‖ ≤ Y := by linarith [hsq b hb0]
  have a7 : ‖a*q/c*q^k‖ ≤ Y := by linarith [hsq c hc0]
  have a8 : ‖a*q/d*q^k‖ ≤ Y := by linarith [hsq d hd0]
  have hz' : ‖a*q/(b*c*d)‖ ≤ ρ := by
    rw [norm_div, norm_mul, hρ, mul_comm ‖a‖]; gcongr
  have hform : threeClearedTerm b c d q a k = DLMF.Bailey.unitD a q k * qPochhammer b q k *
      qPochhammer c q k * qPochhammer d q k * qPochhammerInf (a*q/b*q^k) q *
      qPochhammerInf (a*q/c*q^k) q * qPochhammerInf (a*q/d*q^k) q *
      (qPochhammer q q k)⁻¹ * (a*q/(b*c*d))^k := by
    unfold threeClearedTerm; ring
  rw [hform]
  simp only [norm_mul, norm_pow]
  have hE0 : 0 ≤ E := by linarith
  calc _ ≤ E * (1 + R₁) * E * E * E * E * E * E * C * ρ^k := by
        gcongr
        all_goals first
          | exact hEP _ a3 k | exact hEP _ a4 k | exact hEP _ a5 k
          | exact hEI _ a6 | exact hEI _ a7 | exact hEI _ a8 | exact hC k
    _ = E^7 * (1 + R₁) * C * ρ^k := by ring

private lemma threeClearedTerm_eq {a b c d q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) (ha : a ≠ 1)
    (hS : qPochhammer (Complex.sqrt a) q k * qPochhammer (-Complex.sqrt a) q k ≠ 0)
    (h1 : qPochhammer (a*q/b) q k ≠ 0) (h2 : qPochhammer (a*q/c) q k ≠ 0)
    (h3 : qPochhammer (a*q/d) q k ≠ 0) :
    threeClearedTerm b c d q a k = threeDen b c d q a *
      qPhiTerm [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d]
        [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q (a*q/(b*c*d)) k := by
  have h4 := qPochhammer_self_ne_zero hq k
  have hu := veryWellPoised_factor_eq_unitD (a := a) (q := q) k (Or.inr ⟨ha, hS⟩)
  unfold threeClearedTerm threeDen
  rw [← hu, qPochhammerInf_mul_qPochhammer hq k (a := a*q/b),
    qPochhammerInf_mul_qPochhammer hq k (a := a*q/c),
    qPochhammerInf_mul_qPochhammer hq k (a := a*q/d)]
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil]
  norm_num only [zpow_zero, mul_one]
  generalize qPochhammer (a*q/b) q k = X1 at h1 ⊢
  generalize qPochhammer (a*q/c) q k = X2 at h2 ⊢
  generalize qPochhammer (a*q/d) q k = X3 at h3 ⊢
  have hs1 := left_ne_zero_of_mul hS
  have hs2 := right_ne_zero_of_mul hS
  field_simp

private lemma threeClearedTerm_one {b c d q : ℂ} (hq : ‖q‖ < 1) (k : ℕ)
    (h1 : qPochhammer (q/b) q k ≠ 0) (h2 : qPochhammer (q/c) q k ≠ 0)
    (h3 : qPochhammer (q/d) q k ≠ 0) :
    threeClearedTerm b c d q 1 k = threeDen b c d q 1 *
      ((if k = 0 then 1 else 1 + q^k) * (qPochhammerList [b,c,d] q k /
        qPochhammerList [q/b,q/c,q/d] q k * (q/(b*c*d))^k)) := by
  unfold threeClearedTerm threeDen
  simp only [one_mul]
  rw [qPochhammerInf_mul_qPochhammer hq k (a := q/b),
    qPochhammerInf_mul_qPochhammer hq k (a := q/c),
    qPochhammerInf_mul_qPochhammer hq k (a := q/d)]
  simp only [qPochhammerList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rcases k with _ | k
  · simp [DLMF.Bailey.unitD, qPochhammer_zero]
  · have h4 := qPochhammer_self_ne_zero hq k
    have h5 : 1 - q*q^k ≠ 0 := by
      have := qPochhammer_self_ne_zero hq (k+1)
      rw [qPochhammer_succ] at this; exact right_ne_zero_of_mul this
    simp only [DLMF.Bailey.unitD, one_mul, Nat.succ_ne_zero, ite_false, qPochhammer_succ q q k]
    generalize qPochhammer (q/b) q (k+1) = X1 at h1 ⊢
    generalize qPochhammer (q/c) q (k+1) = X2 at h2 ⊢
    generalize qPochhammer (q/d) q (k+1) = X3 at h3 ⊢
    rw [show 1 - q^(2*(k+1)) = (1 - q*q^k) * (1 + q^(k+1)) by ring]
    field_simp

/-- The `3ψ3` summation at argument `q/(bcd)` (DLMF 17.8.E5). -/
@[dlmf 17.8.E5]
theorem bilateral_three_sum {b c d q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖q‖<‖b*c*d‖)
    (hreg : QBilateralRegular [b,c,d] [q/b,q/c,q/d] q) :
    qPsi [b,c,d] [q/b,q/c,q/d] q (q/(b*c*d))=qBilateralThreeValue b c d q := by
  have hbcd : b*c*d ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact (norm_nonneg _).not_gt hz
  have hb : b ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc : c ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd : d ≠ 0 := right_ne_zero_of_mul hbcd
  have hregI : ∀ x : ℂ, (∀ j : ℕ, x*q^j ≠ 1) → qPochhammerInf x q ≠ 0 :=
    fun x hx => qPochhammerInf_ne_zero hq (fun j h => hx j (sub_eq_zero.mp h).symm)
  have hregk : ∀ x : ℂ, (∀ j : ℕ, x*q^j ≠ 1) → ∀ k, qPochhammer x q k ≠ 0 :=
    fun x hx k => qPochhammer_ne_zero_of_factors hq (fun j h => hx j (sub_eq_zero.mp h).symm) k
  have hB : ∀ j : ℕ, q/b*q^j ≠ 1 := hreg.1 _ (by simp)
  have hC : ∀ j : ℕ, q/c*q^j ≠ 1 := hreg.1 _ (by simp)
  have hD : ∀ j : ℕ, q/d*q^j ≠ 1 := hreg.1 _ (by simp)
  have hz1 : ‖q/(b*c*d)‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hbcd)]; exact hz
  -- the bilateral series as two unilateral series
  have hsplit := qPsi_split hq0 hq hreg (by simp [hb, hc, hd]) (by simp [hb, hc, hd, hq0])
    (div_ne_zero hq0 hbcd) (by simp) (by
      simp only [List.prod_cons, List.prod_nil, mul_one]
      rw [show q/b*(q/c*(q/d))/(b*(c*d)*(q/(b*c*d))) = q*(q/(b*c*d)) by field_simp, norm_mul]
      nlinarith [norm_nonneg q, norm_nonneg (q/(b*c*d))]) (fun _ => hz1)
  set t : ℕ → ℂ := fun k => qPochhammerList [b,c,d] q k / qPochhammerList [q/b,q/c,q/d] q k *
    (q/(b*c*d))^k with ht
  have hpos : ∀ k : ℕ, qPsiTerm [b,c,d] [q/b,q/c,q/d] q (q/(b*c*d)) k = t k := by
    intro k
    simp only [qPsiTerm, qPsiExponent, qPochhammerListInt_natCast, ht, List.length_cons,
      List.length_nil]
    norm_num only [zpow_zero, mul_one, zpow_natCast]
  have hneg : ∀ k : ℕ, qPochhammerList ([q/b,q/c,q/d].map fun bi => q/bi) q (k+1) /
      qPochhammerList ([b,c,d].map fun ai => q/ai) q (k+1) *
      ([q/b,q/c,q/d].prod/([b,c,d].prod*(q/(b*c*d))))^(k+1) = q^(k+1) * t (k+1) := by
    intro k
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ht]
    rw [show q/(q/b) = b by field_simp, show q/(q/c) = c by field_simp,
      show q/(q/d) = d by field_simp,
      show q/b*(q/c*(q/d))/(b*(c*d)*(q/(b*c*d))) = q*(q/(b*c*d)) by field_simp, mul_pow]
    ring
  rw [hsplit, tsum_congr hpos, tsum_congr hneg]
  -- the `₆φ₅` sum in the limit `a → 1`
  obtain ⟨δ, hδ, M, ρ, hρ0, hρ1, hbound⟩ := threeCleared_bound hq hb hc hd hz
  have hcI : Continuous fun x => qPochhammerInf x q :=
    continuousOn_univ.mp (qPochhammerInf_analytic hq).continuousOn
  have hcL : ContinuousAt (fun a => ∑' k, threeClearedTerm b c d q a k) 1 := by
    refine (continuousOn_tsum (fun k => Continuous.continuousOn ?_)
      ((summable_geometric_of_lt_one hρ0 hρ1).mul_left M)
      (fun k a ha => hbound a ha k)).continuousAt (Metric.closedBall_mem_nhds 1 hδ)
    have hU : Continuous fun a => DLMF.Bailey.unitD a q k := by
      rcases k with _ | k
      · simp only [DLMF.Bailey.unitD]; exact continuous_const
      · simp only [DLMF.Bailey.unitD]
        exact ((continuous_qPochhammer q k).comp (continuous_id.mul continuous_const)).mul
          (by fun_prop)
    unfold threeClearedTerm
    exact (((((hU.mul continuous_const).mul continuous_const).mul continuous_const).mul
      (hcI.comp (by fun_prop))).mul (hcI.comp (by fun_prop))).mul (hcI.comp (by fun_prop))
      |>.div_const _ |>.mul (by fun_prop)
  have hcR : ContinuousAt (fun a : ℂ => qPochhammerListInf [a*q, a*q/(b*c), a*q/(b*d),
      a*q/(c*d)] q / qPochhammerInf (a*q/(b*c*d)) q) 1 := by
    simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    refine ContinuousAt.div (Continuous.continuousAt ?_) (hcI.comp (by fun_prop)).continuousAt
      (by rw [one_mul]; exact qPochhammerInf_ne_zero_of_norm_lt_one hz1 hq)
    exact (hcI.comp (by fun_prop)).mul ((hcI.comp (by fun_prop)).mul ((hcI.comp
      (by fun_prop)).mul (hcI.comp (by fun_prop))))
  have hsq : ∀ x : ℂ, (Complex.sqrt x)^2 = x := fun x => by
    rw [Complex.sqrt, ← Complex.cpow_nat_mul]; norm_num
  have hsqrt : Tendsto Complex.sqrt (𝓝[≠] 1) (𝓝[≠] 1) := by
    have hc1 : ContinuousAt Complex.sqrt 1 := by
      unfold Complex.sqrt; exact continuousAt_cpow_const (by simp)
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := hc1.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
      rwa [Complex.sqrt_one] at this
    · filter_upwards [self_mem_nhdsWithin] with a (ha : a ≠ 1)
      intro h
      apply ha
      rw [← hsq a, show Complex.sqrt a = 1 from h, one_pow]
  have hsqrt' : Tendsto (fun a => -Complex.sqrt a) (𝓝 1) (𝓝 (-1)) := by
    have hc1 : ContinuousAt Complex.sqrt 1 := by
      unfold Complex.sqrt; exact continuousAt_cpow_const (by simp)
    have := hc1.tendsto.neg
    rwa [Complex.sqrt_one] at this
  have hm1 : ∀ j : ℕ, -1*q^j ≠ 1 := by
    intro j h
    rcases j with _ | j
    · norm_num at h
    · have h1 : ‖q^(j+1)‖ = 1 := by
        rw [show q^(j+1) = -1 by linear_combination -h, norm_neg, norm_one]
      rw [norm_pow] at h1
      exact absurd h1 (pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero j)).ne
  have hev : ∀ᶠ a in 𝓝[≠] (1:ℂ), ∑' k, threeClearedTerm b c d q a k =
      qPochhammerListInf [a*q, a*q/(b*c), a*q/(b*d), a*q/(c*d)] q /
        qPochhammerInf (a*q/(b*c*d)) q := by
    have e2 : ∀ᶠ a in 𝓝 (1:ℂ), ‖a*q‖ < ‖b*c*d‖ :=
      ((by fun_prop : Continuous fun a : ℂ => ‖a*q‖).tendsto 1).eventually
        (gt_mem_nhds (by rw [one_mul]; exact hz))
    have e3 := hsqrt.eventually (eventually_mul_pow_ne_one_nhdsNE hq 1)
    have e4 := hsqrt'.eventually (eventually_mul_pow_ne_one_nhds hq hm1)
    have e5 : ∀ᶠ a in 𝓝 (1:ℂ), ∀ j : ℕ, a*q/b*q^j ≠ 1 :=
      ((by fun_prop : Continuous fun a : ℂ => a*q/b).tendsto 1).eventually
        (eventually_mul_pow_ne_one_nhds hq (by rw [one_mul]; exact hB))
    have e6 : ∀ᶠ a in 𝓝 (1:ℂ), ∀ j : ℕ, a*q/c*q^j ≠ 1 :=
      ((by fun_prop : Continuous fun a : ℂ => a*q/c).tendsto 1).eventually
        (eventually_mul_pow_ne_one_nhds hq (by rw [one_mul]; exact hC))
    have e7 : ∀ᶠ a in 𝓝 (1:ℂ), ∀ j : ℕ, a*q/d*q^j ≠ 1 :=
      ((by fun_prop : Continuous fun a : ℂ => a*q/d).tendsto 1).eventually
        (eventually_mul_pow_ne_one_nhds hq (by rw [one_mul]; exact hD))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds e2, e3, nhdsWithin_le_nhds e4,
      nhdsWithin_le_nhds e5, nhdsWithin_le_nhds e6, nhdsWithin_le_nhds e7]
      with a (h1 : a ≠ 1) h2 h3 h4 h5 h6 h7
    have hd6 : QDenominatorRegular [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7
    rw [tsum_congr fun k => threeClearedTerm_eq hq k h1
      (mul_ne_zero (hregk _ h3 k) (hregk _ h4 k)) (hregk _ h5 k) (hregk _ h6 k) (hregk _ h7 k),
      tsum_mul_left]
    change threeDen b c d q a * qPhi _ _ q _ = _
    rw [six_phi_five_sum hq h2 hd6]
    unfold threeDen
    simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    have f5 := hregI _ h5
    have f6 := hregI _ h6
    have f7 := hregI _ h7
    field_simp
  have hlim := tendsto_nhds_unique (hcL.tendsto.mono_left nhdsWithin_le_nhds)
    ((hcR.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun a h => h.symm))
  have hsumm1 : Summable (threeClearedTerm b c d q 1) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_left M)
      (hbound 1 (Metric.mem_closedBall_self hδ.le))
  set u : ℕ → ℂ := fun k => (if k = 0 then 1 else 1 + q^k) * t k with hu_def
  have hTu : ∀ k, threeClearedTerm b c d q 1 k = threeDen b c d q 1 * u k := fun k =>
    threeClearedTerm_one hq k (hregk _ hB k) (hregk _ hC k) (hregk _ hD k)
  have hD1 : threeDen b c d q 1 ≠ 0 := by
    unfold threeDen; simp only [one_mul]
    exact mul_ne_zero (mul_ne_zero (hregI _ hB) (hregI _ hC)) (hregI _ hD)
  have hu : Summable u := (hsumm1.div_const (threeDen b c d q 1)).congr fun k => by
    rw [hTu]; field_simp
  have h1q : 0 < 1 - ‖q‖ := by linarith
  have htsum : Summable t := by
    refine Summable.of_norm_bounded (hu.norm.div_const (1 - ‖q‖)) fun k => ?_
    rw [le_div_iff₀ h1q]
    rcases k with _ | k
    · simp only [hu_def, ite_true, one_mul]
      nlinarith [norm_nonneg (t 0), norm_nonneg q]
    · simp only [hu_def, Nat.succ_ne_zero, ite_false, norm_mul]
      have h1 := norm_sub_norm_le (1:ℂ) (-(q^(k+1)))
      rw [norm_one, norm_neg, sub_neg_eq_add, norm_pow] at h1
      have h2 : ‖q‖^(k+1) ≤ ‖q‖ := pow_le_of_le_one (norm_nonneg q) hq.le (Nat.succ_ne_zero k)
      nlinarith [norm_nonneg (t (k+1))]
  have ht1 : Summable fun k => t (k+1) := (summable_nat_add_iff 1).mpr htsum
  have hsq' : Summable fun k => q^(k+1) * t (k+1) :=
    Summable.of_norm_bounded ht1.norm fun k => by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
  have key : ∑' k, u k = ∑' k, t k + ∑' k, q^(k+1) * t (k+1) := by
    rw [hu.tsum_eq_zero_add, htsum.tsum_eq_zero_add, add_assoc, ← ht1.tsum_add hsq']
    simp only [hu_def, ite_true, one_mul, Nat.succ_ne_zero, ite_false]
    congr 1
    exact tsum_congr fun k => by ring
  rw [tsum_congr hTu, tsum_mul_left, key] at hlim
  refine mul_left_cancel₀ hD1 (hlim.trans ?_)
  unfold threeDen qBilateralThreeValue
  simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, one_mul]
  have f1 := hregI _ hB
  have f2 := hregI _ hC
  have f3 := hregI _ hD
  field_simp

/-- The `4ψ4` summation (DLMF 17.8.E6). -/
@[dlmf 17.8.E6]
theorem bilateral_four_sum {a b c d q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hz : ‖q*a*Complex.sqrt a‖<‖b*c*d‖)
    (hreg : QBilateralRegular [-q*Complex.sqrt a,b,c,d] [-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q) :
    qPsi [-q*Complex.sqrt a,b,c,d] [-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q
      (q*a*Complex.sqrt a/(b*c*d))=qBilateralFourValue a b c d q := by
  sorry

/-- The very-well-poised `6ψ6` summation (DLMF 17.8.E7). -/
@[dlmf 17.8.E7]
theorem bilateral_six_sum {a b c d e q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hz : ‖q*a^2‖<‖b*c*d*e‖)
    (hreg : QBilateralRegular [q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e] q) :
    qPsi [q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e] q
      (q*a^2/(b*c*d*e))=qBilateralSixValue a b c d e q := by
  sorry

/-- The actual series identity uses the full bilateral annulus; the continuation below covers the
larger printed region. -/
@[dlmf 17.8.E8]
theorem bilateral_even_sum {b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hb : b≠0) (hc : c≠0)
    (hz : ‖c/b^2‖<1)
    (hreg : QBilateralRegular [b^2,b^2/c] [q,c*q] (q^2)) :
    qPsi [b^2,b^2/c] [q,c*q] (q^2) (c*q^2/b^2)=qBilateralEvenValue b c q := by
  sorry

/-- The product side of Ramanujan's `1ψ1` sum is analytic off its zeros and continues the
bilateral series analytically from its annulus of convergence. -/
theorem ramanujan_continues {a b q z₀ : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hreg : QBilateralRegular [a] [b] q) (hz : ‖b/a‖<‖z₀‖ ∧ ‖z₀‖<1) :
    let U : Set ℂ := {z | z≠0 ∧ qPochhammerListInf [b,q/a,z,b/(a*z)] q≠0}
    AnalyticOnNhd ℂ (qRamanujanValue a b q) U ∧
    (qPsi [a] [b] q=ᶠ[𝓝 z₀] qRamanujanValue a b q) ∧
    TauCeti.ContinuesInside (qPsi [a] [b] q) U z₀ := by
  intro U
  have hP := qPochhammerInf_analytic hq
  have hAz : ∀ {f : ℂ → ℂ} {z : ℂ}, AnalyticAt ℂ f z →
      AnalyticAt ℂ (fun w => qPochhammerInf (f w) q) z :=
    fun hf => (hP _ (mem_univ _)).comp hf
  have hden : ∀ z : ℂ, z ≠ 0 →
      AnalyticAt ℂ (fun w => qPochhammerListInf [b,q/a,w,b/(a*w)] q) z := by
    intro z hz0
    simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    exact analyticAt_const.mul (analyticAt_const.mul ((hAz analyticAt_id).mul
      (hAz (analyticAt_const.div (analyticAt_const.mul analyticAt_id) (mul_ne_zero ha hz0)))))
  have hnum : ∀ z : ℂ, z ≠ 0 →
      AnalyticAt ℂ (fun w => qPochhammerListInf [q,b/a,a*w,q/(a*w)] q) z := by
    intro z hz0
    simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    exact analyticAt_const.mul (analyticAt_const.mul
      ((hAz (analyticAt_const.mul analyticAt_id)).mul (hAz (analyticAt_const.div
        (analyticAt_const.mul analyticAt_id) (mul_ne_zero ha hz0)))))
  have hF : AnalyticOnNhd ℂ (qRamanujanValue a b q) U := fun z hz =>
    (hnum z hz.1).div (hden z hz.1) hz.2
  have hUo : IsOpen U := by
    have hc : ContinuousOn (fun w => qPochhammerListInf [b,q/a,w,b/(a*w)] q) {z | z ≠ 0} :=
      fun z hz => (hden z hz).continuousAt.continuousWithinAt
    exact hc.isOpen_inter_preimage isOpen_ne isOpen_ne
  have heq : qPsi [a] [b] q=ᶠ[𝓝 z₀] qRamanujanValue a b q := by
    have hopen : IsOpen {z : ℂ | ‖b/a‖<‖z‖ ∧ ‖z‖<1} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    filter_upwards [hopen.mem_nhds hz] with z hz'
    exact ramanujan_one_psi_one hq0 hq ha hreg hz'
  exact ⟨hF, heq, qPsi_continuesInside_of_eq hUo hF heq⟩

/-- The product side of the `2ψ2` sum, as a function of `a`, analytically continues the bilateral
series. -/
theorem bilateral_two_continues {a₀ b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a₀≠0)
    (hz : ‖q*a₀‖<‖b*c‖) (hreg : QBilateralRegular [b,c] [a₀*q/b,a₀*q/c] q) :
    let U : Set ℂ := {a | a≠0 ∧ qPochhammerListInf [a*q/b,a*q/c,q/b,q/c,-a*q/(b*c)] q≠0}
    AnalyticOnNhd ℂ (fun a => qBilateralTwoValue a b c q) U ∧
    ((fun a => qPsi [b, c] [a*q/b, a*q/c] q (-a*q/(b*c)))=ᶠ[𝓝 a₀]
        (fun a => qBilateralTwoValue a b c q)) ∧
    TauCeti.ContinuesInside (fun a => qPsi [b,c] [a*q/b,a*q/c] q (-a*q/(b*c))) U a₀ := by
  sorry

/-- The product side of the `3ψ3` sum, as a function of `d`, analytically continues the bilateral
series. -/
theorem bilateral_three_continues {b c d₀ q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hz : ‖q‖<‖b*c*d₀‖) (hreg : QBilateralRegular [b,c,d₀] [q/b,q/c,q/d₀] q) :
    let U : Set ℂ := {d | d≠0 ∧ qPochhammerListInf [q/b,q/c,q/d,q/(b*c*d)] q≠0}
    AnalyticOnNhd ℂ (fun d => qBilateralThreeValue b c d q) U ∧
    ((fun d => qPsi [b, c, d] [q/b, q/c, q/d] q (q/(b*c*d)))=ᶠ[𝓝 d₀]
        (fun d => qBilateralThreeValue b c d q)) ∧
    TauCeti.ContinuesInside (fun d => qPsi [b,c,d] [q/b,q/c,q/d] q (q/(b*c*d))) U d₀ := by
  intro U
  have hP := qPochhammerInf_analytic hq
  have hAz : ∀ {f : ℂ → ℂ} {z : ℂ}, AnalyticAt ℂ f z →
      AnalyticAt ℂ (fun w => qPochhammerInf (f w) q) z :=
    fun hf => (hP _ (mem_univ _)).comp hf
  have hbc : b*c ≠ 0 := by
    intro h; rw [h, zero_mul, norm_zero] at hz; exact (norm_nonneg _).not_gt hz
  have hd₀ : d₀ ≠ 0 := by
    rintro rfl; rw [mul_zero, norm_zero] at hz; exact (norm_nonneg _).not_gt hz
  have hden : ∀ z : ℂ, z ≠ 0 →
      AnalyticAt ℂ (fun w => qPochhammerListInf [q/b,q/c,q/w,q/(b*c*w)] q) z := by
    intro z hz0
    simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    exact analyticAt_const.mul (analyticAt_const.mul ((hAz (analyticAt_const.div analyticAt_id
      hz0)).mul (hAz (analyticAt_const.div (analyticAt_const.mul analyticAt_id)
        (mul_ne_zero hbc hz0)))))
  have hnum : ∀ z : ℂ, z ≠ 0 →
      AnalyticAt ℂ (fun w => qPochhammerListInf [q,q/(b*c),q/(b*w),q/(c*w)] q) z := by
    intro z hz0
    have hb : b ≠ 0 := left_ne_zero_of_mul hbc
    have hc : c ≠ 0 := right_ne_zero_of_mul hbc
    simp only [qPochhammerListInf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    exact analyticAt_const.mul (analyticAt_const.mul
      ((hAz (analyticAt_const.div (analyticAt_const.mul analyticAt_id) (mul_ne_zero hb hz0))).mul
        (hAz (analyticAt_const.div (analyticAt_const.mul analyticAt_id) (mul_ne_zero hc hz0)))))
  have hF : AnalyticOnNhd ℂ (fun d => qBilateralThreeValue b c d q) U := fun z hz =>
    (hnum z hz.1).div (hden z hz.1) hz.2
  have hUo : IsOpen U := by
    have hc : ContinuousOn (fun w => qPochhammerListInf [q/b,q/c,q/w,q/(b*c*w)] q) {z | z ≠ 0} :=
      fun z hz => (hden z hz).continuousAt.continuousWithinAt
    exact hc.isOpen_inter_preimage isOpen_ne isOpen_ne
  have heq : (fun d => qPsi [b, c, d] [q/b, q/c, q/d] q (q/(b*c*d)))=ᶠ[𝓝 d₀]
      (fun d => qBilateralThreeValue b c d q) := by
    have h0 : ∀ j : ℕ, q/d₀*q^j ≠ 1 := hreg.1 _ (by simp)
    have ht : Tendsto (fun d : ℂ => q/d) (𝓝 d₀) (𝓝 (q/d₀)) :=
      (continuousAt_const.div continuousAt_id hd₀).tendsto
    have hopen : IsOpen {d : ℂ | ‖q‖<‖b*c*d‖} :=
      isOpen_lt continuous_const (continuous_const.mul continuous_id).norm
    filter_upwards [hopen.mem_nhds hz, ht.eventually (eventually_mul_pow_ne_one_nhds hq h0),
      isOpen_ne.mem_nhds hd₀] with d hzd hrd hd0
    refine bilateral_three_sum hq0 hq hzd ⟨?_, ?_⟩
    · intro bi hbi n
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbi
      rcases hbi with rfl | rfl | rfl
      · exact hreg.1 _ (by simp) n
      · exact hreg.1 _ (by simp) n
      · exact hrd n
    · intro ai hai n
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hai
      rcases hai with rfl | rfl | rfl
      · exact hreg.2 _ (by simp) n
      · exact hreg.2 _ (by simp) n
      · intro h
        apply hrd n
        rw [h, pow_succ]
        field_simp
  exact ⟨hF, heq, (TauCeti.ContinuesInside.of_differentiableOn hUo hF.differentiableOn).congr
    heq.symm⟩

/-- The product side of the `4ψ4` sum, as a function of `d`, analytically continues the bilateral
series. -/
theorem bilateral_four_continues {a b c d₀ q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hz : ‖q*a*Complex.sqrt a‖<‖b*c*d₀‖)
    (hreg : QBilateralRegular [-q*Complex.sqrt a,b,c,d₀] [-Complex.sqrt a,a*q/b,a*q/c,a*q/d₀] q) :
    let U : Set ℂ := {d | d≠0 ∧
                        qPochhammerListInf [a*q/b, a*q/c, a*q/d, q/b, q/c, q/d,
                        q*a*Complex.sqrt a/(b*c*d)] q≠0}
    AnalyticOnNhd ℂ (fun d => qBilateralFourValue a b c d q) U ∧
    ((fun d => qPsi [-q*Complex.sqrt a, b, c, d] [-Complex.sqrt a, a*q/b, a*q/c, a*q/d] q
        (q*a*Complex.sqrt a/(b*c*d)))=ᶠ[𝓝 d₀] (fun d => qBilateralFourValue a b c d q)) ∧
    TauCeti.ContinuesInside
        (fun d => qPsi [-q*Complex.sqrt a, b, c, d] [-Complex.sqrt a, a*q/b, a*q/c, a*q/d] q
        (q*a*Complex.sqrt a/(b*c*d))) U d₀ := by
  sorry

/-- The product side of the `6ψ6` sum, as a function of `e`, analytically continues the bilateral
series. -/
theorem bilateral_six_continues {a b c d e₀ q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (ha : a≠0)
    (hz : ‖q*a^2‖<‖b*c*d*e₀‖)
    (hreg : QBilateralRegular [q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e₀]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e₀] q) :
    let U : Set ℂ := {e | e≠0 ∧
                        qPochhammerListInf [a*q/b, a*q/c, a*q/d, a*q/e, q/b, q/c, q/d, q/e,
                        q*a^2/(b*c*d*e)] q≠0}
    AnalyticOnNhd ℂ (fun e => qBilateralSixValue a b c d e q) U ∧
    ((fun e => qPsi [q*Complex.sqrt a, -q*Complex.sqrt a, b, c, d, e]
        [Complex.sqrt a, -Complex.sqrt a, a*q/b, a*q/c, a*q/d, a*q/e] q (q*a^2/(b*c*d*e)))=ᶠ[𝓝 e₀]
        (fun e => qBilateralSixValue a b c d e q)) ∧
    TauCeti.ContinuesInside
        (fun e => qPsi [q*Complex.sqrt a, -q*Complex.sqrt a, b, c, d, e]
        [Complex.sqrt a, -Complex.sqrt a, a*q/b, a*q/c, a*q/d, a*q/e] q
        (q*a^2/(b*c*d*e))) U e₀ := by
  sorry

/-- The product side of the base-`q²` bilateral sum, as a function of `c`, analytically continues
the bilateral series. -/
theorem bilateral_even_continues {b c₀ q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hb : b≠0) (hc : c₀≠0)
    (hz : ‖c₀/b^2‖<1) (hreg : QBilateralRegular [b^2,b^2/c₀] [q,c₀*q] (q^2)) :
    let U : Set ℂ := {c | qPochhammerListInf [c*q,c*q^2/b^2,q^2/b^2,c/b^2] (q^2)≠0}
    AnalyticOnNhd ℂ (fun c => qBilateralEvenValue b c q) U ∧
    ((fun c => qPsi [b^2, b^2/c] [q, c*q] (q^2) (c*q^2/b^2))=ᶠ[𝓝 c₀]
        (fun c => qBilateralEvenValue b c q)) ∧
    TauCeti.ContinuesInside (fun c => qPsi [b^2,b^2/c] [q,c*q] (q^2) (c*q^2/b^2)) U c₀ := by
  sorry

end DLMF.QHypergeometric
