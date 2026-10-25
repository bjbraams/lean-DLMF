/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Generalized
public import DLMF.Hypergeometric.GeneralizedCalculus
public import DLMF.Hypergeometric.GeneralizedIntegral
public import DLMF.Hypergeometric.ParameterHolomorphy
public import DLMF.Core.Framework

/-!
# Generalized hypergeometric definitions and continuation: DLMF §§16.1–16.2

Mathlib's `regularizedHGFun` is a totalized power-series sum. It is not an analytic
continuation outside its convergence disk. Here `genRegularizedHG` uses a uniquely
normalized principal continuation for `p=q+1`; `genHG` restores the Gamma factors
when lower parameters are regular. Nonprincipal boundary values are kept separately.
For `p>q+1` nonterminating series no analytic value is assigned by this API; contour
values are acquired separately in `Integrals`. `genFiniteHG` handles terminating
expressions whose lower parameters may be exceptional after the final retained term.

Mathlib supplies convergent-series radii and holomorphy. Existing local generalized
calculus supplies differentiation and contiguity; no duplicate proof is introduced.
Finite inversion multiplies the existing local scalar Pochhammer reflection identity
and uses Mathlib's descending-factorial/binomial normalization. The integer-index
Gamma bridge uses Mathlib's Gamma recurrence and its explicit pole totalization.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real ENNReal
noncomputable section
namespace DLMF.Hypergeometric

/-- Vector parameters represented as a multiset; no order-dependent normalization. -/
def genParams {p : ℕ} (a : Fin p → ℂ) : Multiset ℂ := (List.ofFn a : Multiset ℂ)

/-- Product of rising factorials in a parameter multiset (DLMF16.1). -/
def genPoch (a : Multiset ℂ) (n : ℕ) : ℂ := (a.map fun x => poch x n).prod

/-- Product of parameter Gamma factors. -/
def genGamma (a : Multiset ℂ) : ℂ := (a.map Complex.Gamma).prod

/-- The ordinary generalized hypergeometric coefficient (16.2.1). -/
@[dlmf 16.2.E1]
def genCoeff (a b : Multiset ℂ) (n : ℕ) : ℂ :=
  genPoch a n / (genPoch b n * n.factorial)

/-- Lower parameters avoid the nonpositive integers, unless a formula explicitly overrides this. -/
def genDenRegular (b : Multiset ℂ) : Prop := ∀ x ∈ b, ∀ n : ℕ, x ≠ -n

/-- At least one upper parameter terminates the series. -/
def genTerminates (a : Multiset ℂ) : Prop := ∃ x ∈ a, ∃ n : ℕ, x = -n

/-- The formal scalar series, meaningful even where the analytic series diverges. -/
def genFormalSeries (a b : Multiset ℂ) : PowerSeries ℂ := PowerSeries.mk (genCoeff a b)

/-- A finite retained sum; denominator exceptions beyond its degree are permitted. -/
def genFiniteHG (m : ℕ) (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ range (m + 1), genCoeff a b n * z ^ n

/-- Natural-order hypergeometric series convergence; unlike `HasSum`, permits conditional convergence. -/
def genSeriesConvergesTo (a b : Multiset ℂ) (z v : ℂ) : Prop :=
  Tendsto (fun N : ℕ => ∑ n ∈ range N, genCoeff a b n * z ^ n) atTop (𝓝 v)

/-- Absolute convergence of the ordinary coefficient series. -/
def genSeriesAbsolutelyConverges (a b : Multiset ℂ) (z : ℂ) : Prop :=
  Summable (fun n : ℕ => ‖genCoeff a b n * z ^ n‖)

/-- A normalized regularized continuation for `p=q+1`; its existence is acquired explicitly. -/
structure GenPrincipalContinuation (a b : Multiset ℂ) where
  /-- Principal values, with an upper-side cut convention. -/
  value : ℂ → ℂ
  /-- Analytic continuation on the plane cut from one to positive infinity. -/
  analytic : AnalyticOnNhd ℂ value cutPlane
  /-- The original germ on the open unit disk. -/
  germ : ∀ z, ‖z‖ < 1 → value z = Complex.regularizedHGFun a b z
  /-- Upper cut values away from the singular endpoint. -/
  upper_boundary : ∀ x : ℝ, 1 < x →
    Tendsto value (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (value x))
  /-- At the endpoint only the totalized series value is retained; convergence is separate. -/
  one : value 1 = Complex.regularizedHGFun a b 1

/-- Existence of principal continuation for all regularized parameters, including Gamma zeros. -/
theorem genPrincipalContinuation_exists (a b : Multiset ℂ) (h : a.card = b.card + 1) :
    Nonempty (GenPrincipalContinuation a b) := by
  sorry

/-- Uniqueness of the normalized continuation and its declared cut values. -/
theorem genPrincipalContinuation_unique (a b : Multiset ℂ)
    (F G : GenPrincipalContinuation a b) : F.value = G.value := by
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

/-- Regularized principal generalized hypergeometric function.
For `p>q+1` this expression retains only the totalized series; use Barnes values instead.
The guarded choice keeps local series facts independent of the separate existence admission. -/
@[dlmf 16.2.E5]
def genRegularizedHG (a b : Multiset ℂ) (z : ℂ) : ℂ := by
  classical
  exact if a.card = b.card + 1 then
    if hF : Nonempty (GenPrincipalContinuation a b) then (Classical.choice hF).value z
    else Complex.regularizedHGFun a b z
  else Complex.regularizedHGFun a b z

/-- An explicitly supplied continuation gives the declared principal value, independently
of the separate existence theorem. -/
lemma genRegularizedHG_eq_choice {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hF : Nonempty (GenPrincipalContinuation a b)) (z : ℂ) :
    genRegularizedHG a b z = (Classical.choice hF).value z := by
  classical
  unfold genRegularizedHG
  rw [ite_eq_left h, dite_eq_left hF]

/-- The guarded definition preserves the previous choice of continuation, assuming
exactly the recorded existence theorem. This does not prove existence. -/
theorem genRegularizedHG_eq_original (a b : Multiset ℂ) (z : ℂ) :
    genRegularizedHG a b z =
      if h : a.card = b.card + 1 then
        (Classical.choice (genPrincipalContinuation_exists a b h)).value z
      else Complex.regularizedHGFun a b z := by
  classical
  unfold genRegularizedHG
  split_ifs with h hF
  · rfl
  · exact False.elim (hF (genPrincipalContinuation_exists a b h))
  · rfl

/-- Ordinary principal generalized hypergeometric values, valid for regular lower parameters. -/
def genHG (a b : Multiset ℂ) (z : ℂ) : ℂ := genGamma b * genRegularizedHG a b z

/-- Lower-side principal cut values; conjugate the parameters as well as the variable. -/
def genHGLower (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  star (genHG (a.map star) (b.map star) (star z))

/-- The unit-circle excess parameter (16.2.2). -/
@[dlmf 16.2.E2]
def genExcess (a b : Multiset ℂ) : ℂ := b.sum - a.sum

/-- Shifting every parameter by the same complex number. -/
def genShift (a : Multiset ℂ) (t : ℂ) : Multiset ℂ := a.map (· + t)

/-- A regular lower-parameter Gamma product is nonzero, including the empty product. -/
lemma genGamma_ne_zero {b : Multiset ℂ} (hb : genDenRegular b) : genGamma b ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro h0
  obtain ⟨x, hx, heq⟩ := Multiset.mem_map.mp h0
  exact Complex.Gamma_ne_zero (hb x hx) heq

/-- Every retained rising-factorial product is nonzero for regular lower parameters. -/
lemma genPoch_ne_zero {b : Multiset ℂ} (hb : genDenRegular b) (n : ℕ) : genPoch b n ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro h0
  obtain ⟨x, hx, heq⟩ := Multiset.mem_map.mp h0
  exact poch_ne_zero_of_not_neg_nat (hb x hx) n heq

/-- The fixed Gamma product times the rising-factorial product gives all shifted
Gamma factors; this is Mathlib's Gamma/Pochhammer identity multiplied over parameters. -/
lemma genGamma_shift_nat {b : Multiset ℂ} (hb : genDenRegular b) (n : ℕ) :
    (b.map fun x => Complex.Gamma (x + n)).prod = genPoch b n * genGamma b := by
  unfold genPoch genGamma
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro x hx
  exact (div_eq_iff (Complex.Gamma_ne_zero (hb x hx))).mp
    (Complex.Gamma_add_nat_div_Gamma_eq x (hb x hx))

/-- The regularized principal germ agrees with the native power-series germ. -/
theorem genRegularizedHG_eq_series {a b : Multiset ℂ} (h : a.card ≤ b.card + 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    genRegularizedHG a b z = Complex.regularizedHGFun a b z := by
  classical
  unfold genRegularizedHG
  split_ifs with hc hF
  · exact (Classical.choice hF).germ z hz
  · rfl
  · rfl

/-- Ordinary and regularized coefficients differ by the fixed Gamma product. -/
@[dlmf 16.2.E5]
theorem genCoeff_eq_gamma_mul_regularized {a b : Multiset ℂ} (hb : genDenRegular b)
    (n : ℕ) : genCoeff a b n = genGamma b * Complex.regularizedHGFunCoeff a b n := by
  unfold genCoeff genPoch Complex.regularizedHGFunCoeff
  rw [genGamma_shift_nat hb n]
  have hΓ := genGamma_ne_zero hb
  have hP := genPoch_ne_zero hb n
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  change (a.map (fun x => poch x n)).prod / (genPoch b n * n.factorial) = _
  field_simp [hΓ, hP, hn]

/-- The defining series converges to the principal value in its open disk. -/
@[dlmf 16.2.E1]
theorem genHG_hasSum_disk {a b : Multiset ℂ} (h : a.card ≤ b.card + 1)
    (hb : genDenRegular b) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => genCoeff a b n * z ^ n) (genHG a b z) := by
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
  rw [genHG, genRegularizedHG_eq_series h hz]
  refine (hs.mul_left (genGamma b)).congr_fun fun n => ?_
  rw [genCoeff_eq_gamma_mul_regularized hb]
  ring

/-- A terminating native regularized series is entire, including exceptional lower
parameters; Mathlib already supplies its infinite convergence radius. -/
lemma genRegularizedHG_terminating_analytic {a b : Multiset ℂ} (ha : genTerminates a) :
    AnalyticOnNhd ℂ (Complex.regularizedHGFun a b) univ := by
  obtain ⟨x, hx, m, hxm⟩ := ha
  have hr := Complex.radius_regularizedHGFunSeries_eq_top_of_finite (b := b) hx hxm
  convert! (Complex.regularizedHGFunSeries a b).analyticOnNhd
  simp [hr]

/-- On a terminating series the guarded continuation agrees everywhere with its
entire polynomial germ, without assuming existence of a nonterminating continuation. -/
lemma genRegularizedHG_eq_series_of_terminates {a b : Multiset ℂ} (ha : genTerminates a)
    (z : ℂ) : genRegularizedHG a b z = Complex.regularizedHGFun a b z := by
  classical
  have han := genRegularizedHG_terminating_analytic (b := b) ha
  have hc : Continuous (Complex.regularizedHGFun a b) := continuousOn_univ.mp han.continuousOn
  let G : GenPrincipalContinuation a b := {
    value := Complex.regularizedHGFun a b
    analytic := han.mono (subset_univ _)
    germ := fun _ _ => rfl
    upper_boundary := fun x _ => (hc.tendsto (x : ℂ)).mono_left nhdsWithin_le_nhds
    one := rfl }
  unfold genRegularizedHG
  split_ifs with h hF
  · exact congrFun (genPrincipalContinuation_unique a b (Classical.choice hF) G) z
  · rfl
  · rfl

/-- Scalar ordinary and regularized multilinear series differ by the same fixed
nonzero Gamma product, so all convergence radii agree for regular bottoms. -/
lemma genScalarSeries_eq_gamma_smul {a b : Multiset ℂ} (hb : genDenRegular b) :
    FormalMultilinearSeries.ofScalars ℂ (genCoeff a b) =
      genGamma b • Complex.regularizedHGFunSeries a b := by
  have hc : genCoeff a b =
      genGamma b • (fun n => Complex.regularizedHGFunCoeff a b n) := by
    funext n
    simpa only [Pi.smul_apply, smul_eq_mul] using genCoeff_eq_gamma_mul_regularized hb n
  rw [hc, FormalMultilinearSeries.ofScalars_smul]
  rfl

/-- Terminating series are the retained polynomial, with the minimum terminating degree. -/
theorem genHG_eq_finite {a b : Multiset ℂ} (hb : genDenRegular b)
    {m : ℕ} (hm : (-m : ℂ) ∈ a) (z : ℂ) :
    genHG a b z = genFiniteHG m a b z := by
  rw [genHG, genRegularizedHG_eq_series_of_terminates ⟨-m, hm, m, rfl⟩,
    regularizedHGFun_eq_tsum']
  rw [tsum_eq_sum (s := range (m + 1)) (fun n hn => by
    have hmn : m < n := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    rw [Complex.regularizedHGFunCoeff_eq_zero_left a b n m hm hmn, zero_mul])]
  unfold genFiniteHG
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [genCoeff_eq_gamma_mul_regularized hb]
  ring

/-- Nonvanishing of a retained multiset Pochhammer product follows from that
of its final product, without a global exclusion of nonpositive integer parameters. -/
lemma genPoch_ne_zero_of_le {a : Multiset ℂ} {m j : ℕ} (hj : j ≤ m)
    (ha : genPoch a m ≠ 0) : genPoch a j ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro hzero
  obtain ⟨x, hx, hzero⟩ := Multiset.mem_map.mp hzero
  have hx' : poch x m ≠ 0 := by
    intro hx0
    apply ha
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨x, hx, hx0⟩)
  exact poch_ne_zero_of_le hj hx' hzero

/-- Multiset Pochhammer reflection, obtained from the existing scalar identity
`poch_one_sub_sub_mul` by multiplying over the parameter multiset. -/
lemma genPoch_reflect_mul (a : Multiset ℂ) {m j : ℕ} (hj : j ≤ m) :
    genPoch a j * genPoch (a.map fun x => 1 - m - x) (m - j) =
      (-1 : ℂ) ^ ((m - j) * a.card) * genPoch a m := by
  induction a using Multiset.induction_on with
  | empty => simp [genPoch, Multiset.empty_eq_zero]
  | @cons x a ih =>
    simp only [genPoch, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Multiset.map_map, Function.comp_def] at *
    have hx := poch_one_sub_sub_mul (x := x) hj
    rw [show 1 - m - x = 1 - x - m by ring]
    rw [Nat.mul_add, pow_add, pow_mul]
    linear_combination (a.map (fun x => poch x j)).prod *
      (a.map (fun x => poch (1 - (m : ℂ) - x) (m - j))).prod * hx +
      (-1 : ℂ) ^ (m - j) * poch x m * ih

/-- Reflected retained Pochhammer quotient; endpoint nonvanishing gives every
smaller original and reflected denominator needed in finite inversion. -/
lemma genPoch_reflect_eq_div (a : Multiset ℂ) {m j : ℕ} (hj : j ≤ m)
    (ha : genPoch a m ≠ 0) :
    genPoch (a.map fun x => 1 - m - x) (m - j) =
      (-1 : ℂ) ^ ((m - j) * a.card) * genPoch a m / genPoch a j := by
  apply (eq_div_iff (genPoch_ne_zero_of_le hj ha)).2
  simpa only [mul_comm] using genPoch_reflect_mul a hj

/-- A terminating coefficient uses the ordinary binomial coefficient, valid
at every finite retained index. -/
lemma genCoeff_terminating (a b : Multiset ℂ) (m j : ℕ) :
    genCoeff ((-m : ℂ) ::ₘ a) b j =
      (-1 : ℂ) ^ j * (m.choose j : ℂ) * genPoch a j / genPoch b j := by
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  simp only [genCoeff, genPoch, Multiset.map_cons, Multiset.prod_cons,
    poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

/-- The terminating inversion formula, with all retained denominator factors nonzero. -/
@[dlmf 16.2.E3]
theorem genFiniteHG_inversion (a b : Multiset ℂ) (m : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : genPoch a m ≠ 0) (hb : genPoch b m ≠ 0) :
    genFiniteHG m ((-m : ℂ) ::ₘ a) b z =
      genPoch a m * (-z) ^ m / genPoch b m *
        genFiniteHG m ((-m : ℂ) ::ₘ (b.map fun x => 1 - m - x))
          (a.map fun x => 1 - m - x) ((-1 : ℂ) ^ (a.card + b.card) / z) := by
  unfold genFiniteHG
  rw [Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hsub : m + 1 - 1 - j = m - j := by omega
  rw [hsub, genCoeff_terminating, genCoeff_terminating, Nat.choose_symm hjm,
    genPoch_reflect_eq_div a hjm ha, genPoch_reflect_eq_div b hjm hb]
  have hAj := genPoch_ne_zero_of_le hjm ha
  have hBj := genPoch_ne_zero_of_le hjm hb
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
lemma genFiniteHG_cancel_neg_nat (a b : Multiset ℂ) (m : ℕ) (z : ℂ) :
    genFiniteHG m ((-m : ℂ) ::ₘ a) ((-m : ℂ) ::ₘ b) z = genFiniteHG m a b z := by
  unfold genFiniteHG
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hm : poch (-(m : ℂ)) m ≠ 0 := by
    rw [poch_neg_coe_nat, Nat.descFactorial_self]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast m.factorial_ne_zero)
  have hj' := poch_ne_zero_of_le hjm hm
  congr 1
  simp only [genCoeff, genPoch, Multiset.map_cons, Multiset.prod_cons]
  rw [mul_assoc, mul_div_mul_left _ _ hj']

/-- Every partial sum is a terminating inverted hypergeometric polynomial (16.2.4). -/
@[dlmf 16.2.E4]
theorem genFiniteHG_partial_sum_inversion (a b : Multiset ℂ) (m : ℕ)
    {z : ℂ} (hz : z ≠ 0) (ha : genPoch a m ≠ 0) (hb : genPoch b m ≠ 0) :
    genFiniteHG m a b z = genPoch a m * z ^ m / (genPoch b m * m.factorial) *
      genFiniteHG m ((-m : ℂ) ::ₘ 1 ::ₘ (b.map fun x => 1 - m - x))
        (a.map fun x => 1 - m - x) ((-1 : ℂ) ^ (a.card + b.card + 1) / z) := by
  have hm : poch (-(m : ℂ)) m ≠ 0 := by
    rw [poch_neg_coe_nat, Nat.descFactorial_self]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast m.factorial_ne_zero)
  have hb' : genPoch ((-m : ℂ) ::ₘ b) m ≠ 0 := by
    simpa only [genPoch, Multiset.map_cons, Multiset.prod_cons] using mul_ne_zero hm hb
  have h := genFiniteHG_inversion a ((-m : ℂ) ::ₘ b) m hz ha hb'
  rw [genFiniteHG_cancel_neg_nat] at h
  have hmap : (((-m : ℂ) ::ₘ b).map fun x => 1 - (m : ℂ) - x) =
      (1 : ℂ) ::ₘ (b.map fun x => 1 - m - x) := by
    rw [Multiset.map_cons]
    congr 1
    ring
  have hfac : genPoch a m * (-z) ^ m / genPoch ((-m : ℂ) ::ₘ b) m =
      genPoch a m * z ^ m / (genPoch b m * m.factorial) := by
    have hden : genPoch ((-m : ℂ) ::ₘ b) m = poch (-m : ℂ) m * genPoch b m := by
      simp only [genPoch, Multiset.map_cons, Multiset.prod_cons]
    rw [hden, poch_neg_coe_nat, Nat.descFactorial_self, neg_pow]
    field_simp
  rw [hmap, hfac] at h
  simpa only [Multiset.card_cons, Nat.add_assoc] using h

/-- Rising factorial at an integer index; negative indices use the reciprocal continuation.
At singular parameters this expression is totalized, so analytic formulas state exclusions. -/
def genIntPoch (a : ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then poch a n.toNat else (poch (a + n) (-n).toNat)⁻¹

/-- Integer-index Pochhammer/Gamma normalization, including positive integral
base parameters whose negatively shifted Gamma values are totalized to zero.
This extends Mathlib's `Complex.Gamma_add_nat_div_Gamma_eq` to integer indices. -/
lemma genIntPoch_eq_Gamma_div {a : ℂ} (ha : ∀ j : ℕ, a ≠ -(j : ℂ)) (n : ℤ) :
    genIntPoch a n = Gamma (a + n) / Gamma a := by
  cases n with
  | ofNat n =>
    simpa [genIntPoch] using (Complex.Gamma_add_nat_div_Gamma_eq (n := n) a ha).symm
  | negSucc n =>
    have hneg : (poch (a - (n + 1 : ℕ)) (n + 1))⁻¹ =
        Gamma (a - (n + 1 : ℕ)) / Gamma a := by
      by_cases hshift : ∀ j : ℕ, a - (n + 1 : ℕ) ≠ -(j : ℂ)
      · have hg := Complex.Gamma_add_nat_div_Gamma_eq (n := n + 1)
          (a - (n + 1 : ℕ)) hshift
        rw [sub_add_cancel] at hg
        change Gamma a / Gamma (a - (n + 1 : ℕ)) = poch (a - (n + 1 : ℕ)) (n + 1) at hg
        rw [← hg, inv_div]
      · push Not at hshift
        obtain ⟨j, hj⟩ := hshift
        have hjn : j < n + 1 := by
          by_contra hbad
          have hjn' : n + 1 ≤ j := by omega
          apply ha (j - (n + 1))
          push_cast [Nat.cast_sub hjn'] at hj ⊢
          linear_combination hj
        rw [hj, poch_neg_nat_eq_zero hjn, Complex.Gamma_neg_nat_eq_zero, inv_zero, zero_div]
    unfold genIntPoch
    rw [ite_eq_right (show ¬(0 : ℤ) ≤ Int.negSucc n by omega)]
    simpa [Int.negSucc_eq, sub_eq_add_neg, Nat.cast_add, Nat.cast_one] using hneg

/-- Formal bilateral hypergeometric coefficient, with no factorial factor (16.4.16). -/
@[dlmf 16.4.E16]
def genBilateralCoeff (a b : Multiset ℂ) (n : ℤ) : ℂ :=
  (a.map fun x => genIntPoch x n).prod / (b.map fun x => genIntPoch x n).prod

/-- Totalized bilateral series. Outside an explicitly proved convergence regime this is
only a formal-series interface, not an analytically continued function (16.4.16). -/
@[dlmf 16.4.E16]
def genBilateralHG (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, genBilateralCoeff a b n * z ^ n

/-- Mellin–Barnes kernel on the logarithm sheet `w=Log(-z)`. -/
def genBarnesKernelLog (a b : Multiset ℂ) (w s : ℂ) : ℂ :=
  genGamma (genShift a s) / genGamma (genShift b s) * Gamma (-s) * Complex.exp (s * w)

/-- A convergent contour-defined ordinary pFq value, separate from the divergent formal
series. Both contour tails converge separately; the log sheet of `-z` is explicit. -/
def genHasBarnesValueLog (a b : Multiset ℂ) (L : ℝ → ℂ) (w v : ℂ) : Prop :=
  DLMF.HasIntegralWholeLine (fun t => deriv L t * genBarnesKernelLog a b w (L t))
    (2 * Real.pi * I * genGamma a / genGamma b * v)

/-- Totalized value of a Barnes contour. Every mathematical use asserts its separate
convergence with `genHasBarnesValueLog` and excludes poles in the parameter prefactor. -/
def genBarnesHGLog (a b : Multiset ℂ) (L : ℝ → ℂ) (w : ℂ) : ℂ :=
  genGamma b / (2 * Real.pi * I * genGamma a) *
    limUnder atTop (fun T : ℝ =>
      ∫ t in (-T)..T, deriv L t * genBarnesKernelLog a b w (L t))

end DLMF.Hypergeometric
