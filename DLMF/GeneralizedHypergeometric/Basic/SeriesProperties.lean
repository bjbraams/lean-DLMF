/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuation
public import DLMF.GeneralizedHypergeometric.Basic.BilateralAndBarnes
public import DLMF.Hypergeometric.Basic.GaussSeries

/-!
# Generalized hypergeometric series and the principal value (DLMF §16.2)

Basic properties of the definitions in `DLMF.GeneralizedHypergeometric.Basic.ParametersAndSeries`
and `DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuation`.

## Main results

* `principalContinuation_unique`: uniqueness of the normalized principal continuation.
* `regularizedGeneralizedHypergeometric_eq_series`,
  `regularizedGeneralizedHypergeometric_eq_series_of_terminates`: agreement with the power series.
* `generalizedHypergeometricCoeff_eq_gamma_mul_regularized`: ordinary and regularized coefficients,
  DLMF 16.2.5.
* `generalizedHypergeometric_hasSum_disk`: the defining series converges to the principal value,
  DLMF 16.2.1.
* `generalizedHypergeometric_eq_finite`: terminating series are polynomials.
* `generalizedHypergeometricTruncated_inversion`,
  `generalizedHypergeometricTruncated_partial_sum_inversion`: the terminating inversion formulas,
  DLMF 16.2.3–16.2.4.
* `pochhammerOfInt_eq_Gamma_div`: the integer-index Pochhammer symbol as a Gamma quotient.

## Implementation notes

Mathlib's `regularizedHGFun` is a totalized power-series sum, not an analytic continuation
outside its convergence disk. `regularizedGeneralizedHypergeometric` uses a uniquely normalized
principal continuation for `p = q + 1`, and `generalizedHypergeometric` restores the Gamma factors
when the lower parameters are regular. The existence of the continuation is stated separately in
`DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuationExistence`; nothing here depends
on it.
Finite inversion multiplies the scalar Pochhammer reflection identity `pochhammer_one_sub_sub_mul`
over the parameter multiset.
-/

@[expose] public section
open Complex Filter Set Finset FormalMultilinearSeries
open scoped Topology Real ENNReal
noncomputable section
namespace DLMF.Hypergeometric

/-- Uniqueness of the normalized continuation and its declared cut values. -/
theorem principalContinuation_unique (a b : Multiset ℂ)
    (F G : PrincipalContinuation a b) : F.value = G.value := by
  have heq : EqOn F.value G.value cutPlane :=
    eqOn_cutPlane_of_eqOn_disk F.analytic G.analytic fun z hz =>
      (F.germ z hz).trans (G.germ z hz).symm
  funext z
  by_cases hz : z ∈ cutPlane
  · exact heq hz
  · have hbad : ¬(0 < (1 - z).re ∨ (1 - z).im ≠ 0) := hz
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub, neg_ne_zero] at hbad
    push Not at hbad
    have hreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hbad.2]
    rw [hreal]
    by_cases hx : z.re = 1
    · simpa only [hx, Complex.ofReal_one] using F.one.trans G.one.symm
    · have hx' : 1 < z.re := lt_of_le_of_ne (by linarith [hbad.1]) (Ne.symm hx)
      have : NeBot (𝓝[{w : ℂ | 0 < w.im}] (z.re : ℂ)) := by
        apply mem_closure_iff_nhdsWithin_neBot.mp
        rw [Complex.closure_setOfPred_lt_im]
        simp
      have hev : F.value =ᶠ[𝓝[{w : ℂ | 0 < w.im}] (z.re : ℂ)] G.value := by
        filter_upwards [self_mem_nhdsWithin] with w hw
        apply heq
        change 0 < (1 - w).re ∨ (1 - w).im ≠ 0
        right
        simpa using neg_ne_zero.mpr hw.ne'
      exact tendsto_nhds_unique (F.upper_boundary z.re hx')
        ((G.upper_boundary z.re hx').congr' hev.symm)

/-- An explicitly supplied continuation gives the declared principal value, independently
of the separate existence theorem. -/
theorem regularizedGeneralizedHypergeometric_eq_choice {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hF : Nonempty (PrincipalContinuation a b)) (z : ℂ) :
    regularizedGeneralizedHypergeometric a b z = (Classical.choice hF).value z := by
  classical
  unfold regularizedGeneralizedHypergeometric
  rw [ite_eq_left h, dite_eq_left hF]

/-- A regular lower-parameter Gamma product is nonzero, including the empty product. -/
theorem gammaProduct_ne_zero {b : Multiset ℂ} (hb : LowerParametersRegular b) :
    gammaProduct b ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro h0
  obtain ⟨x, hx, heq⟩ := Multiset.mem_map.mp h0
  exact Complex.Gamma_ne_zero (hb x hx) heq

/-- Every retained rising-factorial product is nonzero for regular lower parameters. -/
theorem pochhammerProduct_ne_zero {b : Multiset ℂ} (hb : LowerParametersRegular b) (n : ℕ) :
    pochhammerProduct b n ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro h0
  obtain ⟨x, hx, heq⟩ := Multiset.mem_map.mp h0
  exact pochhammer_ne_zero_of_not_neg_nat (hb x hx) n heq

/-- The fixed Gamma product times the rising-factorial product gives all shifted
Gamma factors; this is Mathlib's Gamma/Pochhammer identity multiplied over parameters. -/
theorem gammaProduct_shift_nat {b : Multiset ℂ} (hb : LowerParametersRegular b) (n : ℕ) :
    (b.map fun x => Complex.Gamma (x + n)).prod = pochhammerProduct b n * gammaProduct b := by
  unfold pochhammerProduct gammaProduct
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro x hx
  exact (div_eq_iff (Complex.Gamma_ne_zero (hb x hx))).mp
    (Complex.Gamma_add_nat_div_Gamma_eq x (hb x hx))

/-- The regularized principal germ agrees with the native power-series germ. -/
theorem regularizedGeneralizedHypergeometric_eq_series {a b : Multiset ℂ}
    {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGeneralizedHypergeometric a b z = Complex.regularizedHGFun a b z := by
  classical
  unfold regularizedGeneralizedHypergeometric
  split_ifs with hc hF
  · exact (Classical.choice hF).germ z hz
  · rfl
  · rfl

/-- Ordinary and regularized coefficients differ by the fixed Gamma product. -/
@[dlmf 16.2.E5]
theorem generalizedHypergeometricCoeff_eq_gamma_mul_regularized {a b : Multiset ℂ}
    (hb : LowerParametersRegular b)
    (n : ℕ) : generalizedHypergeometricCoeff a b n = gammaProduct b *
        Complex.regularizedHGFunCoeff a b n := by
  unfold generalizedHypergeometricCoeff pochhammerProduct Complex.regularizedHGFunCoeff
  rw [gammaProduct_shift_nat hb n]
  have hΓ := gammaProduct_ne_zero hb
  have hP := pochhammerProduct_ne_zero hb n
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  change (a.map (fun x => pochhammer x n)).prod / (pochhammerProduct b n * n.factorial) = _
  field_simp [hΓ, hP, hn]

/-- The defining series converges to the principal value in its open disk. -/
@[dlmf 16.2.E1]
theorem generalizedHypergeometric_hasSum_disk {a b : Multiset ℂ} (h : a.card ≤ b.card + 1)
    (hb : LowerParametersRegular b) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => generalizedHypergeometricCoeff a b n * z ^ n)
        (generalizedHypergeometric a b z) := by
  have hr : (1 : ℝ≥0∞) ≤ (Complex.regularizedHGFunSeries a b).radius := by
    by_cases hc : a.card ≤ b.card
    · rw [Complex.radius_regularizedHGFunSeries_eq_top hc]; exact le_top
    · exact Complex.radius_regularizedHGFunSeries_ge_one (by omega)
  have hzr : z ∈ Metric.eball (0 : ℂ) (Complex.regularizedHGFunSeries a b).radius :=
    Metric.eball_subset_eball hr (mem_eball_one_of_norm_lt_one hz)
  have hs : HasSum (fun n : ℕ => Complex.regularizedHGFunCoeff a b n * z ^ n)
      (Complex.regularizedHGFun a b z) := by
    simpa [Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
      (Complex.regularizedHGFunSeries a b).hasSum (x := z) hzr
  rw [generalizedHypergeometric, regularizedGeneralizedHypergeometric_eq_series hz]
  refine (hs.mul_left (gammaProduct b)).congr_fun fun n => ?_
  rw [generalizedHypergeometricCoeff_eq_gamma_mul_regularized hb]
  ring

/-- A terminating native regularized series is entire, including exceptional lower
parameters; Mathlib already supplies its infinite convergence radius. -/
theorem regularizedGeneralizedHypergeometric_terminating_analytic {a b : Multiset ℂ}
    (ha : IsTerminating a) :
    AnalyticOnNhd ℂ (Complex.regularizedHGFun a b) univ := by
  obtain ⟨x, hx, m, hxm⟩ := ha
  have hr := Complex.radius_regularizedHGFunSeries_eq_top_of_finite (b := b) hx hxm
  convert! (Complex.regularizedHGFunSeries a b).analyticOnNhd
  simp [hr]

/-- On a terminating series the guarded continuation agrees everywhere with its
entire polynomial germ, without assuming existence of a nonterminating continuation. -/
theorem regularizedGeneralizedHypergeometric_eq_series_of_terminates {a b : Multiset ℂ}
    (ha : IsTerminating a)
    (z : ℂ) : regularizedGeneralizedHypergeometric a b z = Complex.regularizedHGFun a b z := by
  classical
  have han := regularizedGeneralizedHypergeometric_terminating_analytic (b := b) ha
  have hc : Continuous (Complex.regularizedHGFun a b) := continuousOn_univ.mp han.continuousOn
  let G : PrincipalContinuation a b := {
    value := Complex.regularizedHGFun a b
    analytic := han.mono (subset_univ _)
    germ := fun _ _ => rfl
    upper_boundary := fun x _ => (hc.tendsto (x : ℂ)).mono_left nhdsWithin_le_nhds
    one := rfl }
  unfold regularizedGeneralizedHypergeometric
  split_ifs with h hF
  · exact congrFun (principalContinuation_unique a b (Classical.choice hF) G) z
  · rfl
  · rfl

/-- Scalar ordinary and regularized multilinear series differ by the same fixed
nonzero Gamma product, so all convergence radii agree for regular bottoms. -/
theorem genScalarSeries_eq_gamma_smul {a b : Multiset ℂ} (hb : LowerParametersRegular b) :
    FormalMultilinearSeries.ofScalars ℂ (generalizedHypergeometricCoeff a b) =
      gammaProduct b • Complex.regularizedHGFunSeries a b := by
  have hc : generalizedHypergeometricCoeff a b =
      gammaProduct b • (fun n => Complex.regularizedHGFunCoeff a b n) := by
    funext n
    simpa only [Pi.smul_apply, smul_eq_mul] using
        generalizedHypergeometricCoeff_eq_gamma_mul_regularized hb n
  rw [hc, FormalMultilinearSeries.ofScalars_smul]
  rfl

/-- Terminating series are the retained polynomial, with the minimum terminating degree. -/
theorem generalizedHypergeometric_eq_finite {a b : Multiset ℂ} (hb : LowerParametersRegular b)
    {m : ℕ} (hm : (-m : ℂ) ∈ a) (z : ℂ) :
    generalizedHypergeometric a b z = generalizedHypergeometricTruncated m a b z := by
  rw [generalizedHypergeometric,
      regularizedGeneralizedHypergeometric_eq_series_of_terminates ⟨-m, hm, m, rfl⟩,
    regularizedHGFun_eq_tsum']
  rw [tsum_eq_sum (s := range (m + 1)) (fun n hn => by
    have hmn : m < n := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    rw [Complex.regularizedHGFunCoeff_eq_zero_left a b n m hm hmn, zero_mul])]
  unfold generalizedHypergeometricTruncated
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [generalizedHypergeometricCoeff_eq_gamma_mul_regularized hb]
  ring

/-- Nonvanishing of a retained multiset Pochhammer product follows from that
of its final product, without a global exclusion of nonpositive integer parameters. -/
theorem pochhammerProduct_ne_zero_of_le {a : Multiset ℂ} {m j : ℕ} (hj : j ≤ m)
    (ha : pochhammerProduct a m ≠ 0) : pochhammerProduct a j ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro hzero
  obtain ⟨x, hx, hzero⟩ := Multiset.mem_map.mp hzero
  have hx' : pochhammer x m ≠ 0 := by
    intro hx0
    apply ha
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨x, hx, hx0⟩)
  exact pochhammer_ne_zero_of_le hj hx' hzero

/-- Multiset Pochhammer reflection, obtained from the existing scalar identity
`pochhammer_one_sub_sub_mul` by multiplying over the parameter multiset. -/
theorem pochhammerProduct_reflect_mul (a : Multiset ℂ) {m j : ℕ} (hj : j ≤ m) :
    pochhammerProduct a j * pochhammerProduct (a.map fun x => 1 - m - x) (m - j) =
      (-1 : ℂ) ^ ((m - j) * a.card) * pochhammerProduct a m := by
  induction a using Multiset.induction_on with
  | empty => simp [pochhammerProduct]
  | @cons x a ih =>
    simp only [pochhammerProduct, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons,
      Multiset.map_map, Function.comp_def] at *
    have hx := pochhammer_one_sub_sub_mul (x := x) hj
    rw [show 1 - m - x = 1 - x - m by ring]
    rw [Nat.mul_add, pow_add, pow_mul]
    linear_combination (a.map (fun x => pochhammer x j)).prod *
      (a.map (fun x => pochhammer (1 - (m : ℂ) - x) (m - j))).prod * hx +
      (-1 : ℂ) ^ (m - j) * pochhammer x m * ih

/-- Reflected retained Pochhammer quotient; endpoint nonvanishing gives every
smaller original and reflected denominator needed in finite inversion. -/
theorem pochhammerProduct_reflect_eq_div (a : Multiset ℂ) {m j : ℕ} (hj : j ≤ m)
    (ha : pochhammerProduct a m ≠ 0) :
    pochhammerProduct (a.map fun x => 1 - m - x) (m - j) =
      (-1 : ℂ) ^ ((m - j) * a.card) * pochhammerProduct a m / pochhammerProduct a j := by
  apply (eq_div_iff (pochhammerProduct_ne_zero_of_le hj ha)).2
  simpa only [mul_comm] using pochhammerProduct_reflect_mul a hj

/-- A terminating coefficient uses the ordinary binomial coefficient, valid
at every finite retained index. -/
theorem generalizedHypergeometricCoeff_terminating (a b : Multiset ℂ) (m j : ℕ) :
    generalizedHypergeometricCoeff ((-m : ℂ) ::ₘ a) b j =
      (-1 : ℂ) ^ j * (m.choose j : ℂ) * pochhammerProduct a j / pochhammerProduct b j := by
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.map_cons,
      Multiset.prod_cons,
    pochhammer_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

/-- The terminating inversion formula, with all retained denominator factors nonzero. -/
@[dlmf 16.2.E3]
theorem generalizedHypergeometricTruncated_inversion (a b : Multiset ℂ) (m : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : pochhammerProduct a m ≠ 0) (hb : pochhammerProduct b m ≠ 0) :
    generalizedHypergeometricTruncated m ((-m : ℂ) ::ₘ a) b z =
      pochhammerProduct a m * (-z) ^ m / pochhammerProduct b m *
        generalizedHypergeometricTruncated m ((-m : ℂ) ::ₘ (b.map fun x => 1 - m - x))
          (a.map fun x => 1 - m - x) ((-1 : ℂ) ^ (a.card + b.card) / z) := by
  unfold generalizedHypergeometricTruncated
  rw [Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hsub : m + 1 - 1 - j = m - j := by omega
  rw [hsub, generalizedHypergeometricCoeff_terminating, generalizedHypergeometricCoeff_terminating,
      Nat.choose_symm hjm,
    pochhammerProduct_reflect_eq_div a hjm ha, pochhammerProduct_reflect_eq_div b hjm hb]
  have hAj := pochhammerProduct_ne_zero_of_le hjm ha
  have hBj := pochhammerProduct_ne_zero_of_le hjm hb
  have hpm : (-1 : ℂ) ^ m = (-1) ^ j * (-1) ^ (m - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hjm]
  have hzm : z ^ m = z ^ j * z ^ (m - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hjm]
  have hsq (n : ℕ) : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, neg_one_sq, one_pow]
  rw [neg_pow z, hpm, hzm, div_pow, pow_add, mul_pow, ← pow_mul, ← pow_mul,
    show a.card * (m - j) = (m - j) * a.card by exact Nat.mul_comm _ _,
    show b.card * (m - j) = (m - j) * b.card by exact Nat.mul_comm _ _]
  field_simp [hz, ha, hb, hAj, hBj]
  linear_combination -(m.choose j : ℂ) * hsq (m - j) -
    (m.choose j : ℂ) * ((-1 : ℂ) ^ (m - j)) ^ 2 * hsq ((m - j) * b.card)

/-- The terminating upper/lower pair cancels throughout every retained term,
even though it would be exceptional beyond the final retained index. -/
theorem generalizedHypergeometricTruncated_cancel_neg_nat (a b : Multiset ℂ) (m : ℕ) (z : ℂ) :
    generalizedHypergeometricTruncated m ((-m : ℂ) ::ₘ a) ((-m : ℂ) ::ₘ b) z =
        generalizedHypergeometricTruncated m a b z := by
  unfold generalizedHypergeometricTruncated
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hm : pochhammer (-(m : ℂ)) m ≠ 0 := by
    rw [pochhammer_neg_coe_nat, Nat.descFactorial_self]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast m.factorial_ne_zero)
  have hj' := pochhammer_ne_zero_of_le hjm hm
  congr 1
  simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.map_cons,
      Multiset.prod_cons]
  rw [mul_assoc, mul_div_mul_left _ _ hj']

/-- Every partial sum is a terminating inverted hypergeometric polynomial (16.2.4). -/
@[dlmf 16.2.E4]
theorem generalizedHypergeometricTruncated_partial_sum_inversion (a b : Multiset ℂ) (m : ℕ)
    {z : ℂ} (hz : z ≠ 0) (ha : pochhammerProduct a m ≠ 0) (hb : pochhammerProduct b m ≠ 0) :
    generalizedHypergeometricTruncated m a b z = pochhammerProduct a m * z ^ m /
        (pochhammerProduct b m * m.factorial) *
      generalizedHypergeometricTruncated m ((-m : ℂ) ::ₘ 1 ::ₘ (b.map fun x => 1 - m - x))
        (a.map fun x => 1 - m - x) ((-1 : ℂ) ^ (a.card + b.card + 1) / z) := by
  have hm : pochhammer (-(m : ℂ)) m ≠ 0 := by
    rw [pochhammer_neg_coe_nat, Nat.descFactorial_self]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast m.factorial_ne_zero)
  have hb' : pochhammerProduct ((-m : ℂ) ::ₘ b) m ≠ 0 := by
    simpa only [pochhammerProduct, Multiset.map_cons, Multiset.prod_cons] using mul_ne_zero hm hb
  have h := generalizedHypergeometricTruncated_inversion a ((-m : ℂ) ::ₘ b) m hz ha hb'
  rw [generalizedHypergeometricTruncated_cancel_neg_nat] at h
  have hmap : (((-m : ℂ) ::ₘ b).map fun x => 1 - (m : ℂ) - x) =
      (1 : ℂ) ::ₘ (b.map fun x => 1 - m - x) := by
    rw [Multiset.map_cons]
    congr 1
    ring
  have hfac : pochhammerProduct a m * (-z) ^ m / pochhammerProduct ((-m : ℂ) ::ₘ b) m =
      pochhammerProduct a m * z ^ m / (pochhammerProduct b m * m.factorial) := by
    have hden : pochhammerProduct ((-m : ℂ) ::ₘ b) m = pochhammer (-m : ℂ) m *
        pochhammerProduct b m := by
      simp only [pochhammerProduct, Multiset.map_cons, Multiset.prod_cons]
    rw [hden, pochhammer_neg_coe_nat, Nat.descFactorial_self, neg_pow]
    field_simp
  rw [hmap, hfac] at h
  simpa only [Multiset.card_cons, Nat.add_assoc] using h

/-- Integer-index Pochhammer/Gamma normalization, including positive integral
base parameters whose negatively shifted Gamma values are totalized to zero.
This extends Mathlib's `Complex.Gamma_add_nat_div_Gamma_eq` to integer indices. -/
theorem pochhammerOfInt_eq_Gamma_div {a : ℂ} (ha : ∀ j : ℕ, a ≠ -(j : ℂ)) (n : ℤ) :
    pochhammerOfInt a n = Gamma (a + n) / Gamma a := by
  cases n with
  | ofNat n =>
    simpa [pochhammerOfInt] using (Complex.Gamma_add_nat_div_Gamma_eq (n := n) a ha).symm
  | negSucc n =>
    have hneg : (pochhammer (a - (n + 1 : ℕ)) (n + 1))⁻¹ =
        Gamma (a - (n + 1 : ℕ)) / Gamma a := by
      by_cases hshift : ∀ j : ℕ, a - (n + 1 : ℕ) ≠ -(j : ℂ)
      · have hg := Complex.Gamma_add_nat_div_Gamma_eq (n := n + 1)
          (a - (n + 1 : ℕ)) hshift
        rw [sub_add_cancel] at hg
        change Gamma a / Gamma (a - (n + 1 : ℕ)) = pochhammer (a - (n + 1 : ℕ)) (n + 1) at hg
        rw [← hg, inv_div]
      · push Not at hshift
        obtain ⟨j, hj⟩ := hshift
        have hjn : j < n + 1 := by
          by_contra hbad
          have hjn' : n + 1 ≤ j := by omega
          apply ha (j - (n + 1))
          push_cast [Nat.cast_sub hjn'] at hj ⊢
          linear_combination hj
        rw [hj, pochhammer_neg_nat_eq_zero hjn, Complex.Gamma_neg_nat_eq_zero, inv_zero, zero_div]
    unfold pochhammerOfInt
    rw [ite_eq_right (show ¬(0 : ℤ) ≤ Int.negSucc n by omega)]
    simpa [Int.negSucc_eq, sub_eq_add_neg, Nat.cast_add, Nat.cast_one] using hneg

end DLMF.Hypergeometric
