/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic
public import Mathlib.Algebra.Order.Ring.Star

/-!
# Analytic properties and zeros: DLMF §§16.2,16.9

Natural-order convergence is distinguished from absolute convergence on the unit
circle. The statement for `p>q+1` concerns the formal coefficient series, without
assigning its divergent sum an analytic meaning. Analytic continuation uses the
pinned TauCeti predicate for continuation along a path; no new continuation notion
is introduced. Parameter holomorphy applies to every such continued branch.

The finite-product coefficient-ratio estimates adapt Moritz Doll's private lemmas
in `Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric`, extending them
to positive degree. The adaptation is identified again at the helper lemmas.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real ENNReal
noncomputable section
namespace DLMF.Hypergeometric

/-- For p≤q the full ordinary principal function is entire, with regular lower parameters. -/
theorem genHG_entire {a b : Multiset ℂ} (h : a.card ≤ b.card) (hb : genDenRegular b) :
    AnalyticOnNhd ℂ (genHG a b) univ := by
  have hne : a.card ≠ b.card + 1 := by omega
  unfold genHG genRegularizedHG
  simp only [ite_eq_right hne]
  exact analyticOnNhd_const.mul (Complex.analyticOnNhd_regularizedHGFun_of_card_le h)

/-- The entire case has an absolutely convergent series for every finite z. -/
theorem genHG_hasSum_entire {a b : Multiset ℂ} (h : a.card ≤ b.card) (hb : genDenRegular b) (z : ℂ) :
    HasSum (fun n : ℕ => genCoeff a b n * z ^ n) (genHG a b z) := by
  have hne : a.card ≠ b.card + 1 := by omega
  have hs : HasSum (fun n => Complex.regularizedHGFunCoeff a b n * z ^ n)
      (Complex.regularizedHGFun a b z) := by
    simpa [Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
      (Complex.regularizedHGFunSeries a b).hasSum (x := z)
        (by simp [Complex.radius_regularizedHGFunSeries_eq_top h])
  unfold genHG genRegularizedHG
  simp only [ite_eq_right hne]
  refine (hs.mul_left (genGamma b)).congr_fun fun n => ?_
  rw [genCoeff_eq_gamma_mul_regularized hb]
  ring

/-- Any nonpositive integer upper parameter gives a polynomial for every p,q. -/
theorem genHG_terminating_entire {a b : Multiset ℂ} (hb : genDenRegular b) (ha : genTerminates a) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, genHG a b z = P.eval z := by
  obtain ⟨x, hx, m, rfl⟩ := ha
  refine ⟨∑ n ∈ range (m + 1), Polynomial.monomial n (genCoeff a b n), ?_⟩
  intro z
  rw [genHG_eq_finite hb hx]
  simp [genFiniteHG, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- The nonterminating p=q+1 series has exactly radius one. -/
theorem genHG_radius_one {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (ha : ¬genTerminates a) :
    (FormalMultilinearSeries.ofScalars ℂ (genCoeff a b)).radius = 1 := by
  rw [genScalarSeries_eq_gamma_smul hb,
    FormalMultilinearSeries.radius_smul_eq _ (genGamma_ne_zero hb)]
  apply Complex.radius_regularizedHGFunSeries_eq_one h
  intro x hx n hxn
  exact ha ⟨x, hx, n, hxn⟩

/-- Gauss asymptotics of one rising factorial: `(s)ₙ n^(1-s)/n! → 1/Γ(s)`. -/
lemma ghbR4_poch_tendsto {s : ℂ} (hs : ∀ k : ℕ, s ≠ -k) :
    Tendsto (fun n : ℕ => poch s n * (n : ℂ) ^ (1 - s) / (n.factorial : ℂ)) atTop
      (𝓝 (Gamma s)⁻¹) := by
  have hlim : Tendsto (fun n : ℕ => 1 + s / (n : ℂ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat s).const_add 1
  have ht := (hlim.mul (GammaSeq_tendsto_Gamma s)).inv₀ (by simpa using Gamma_ne_zero hs)
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsn : s + (n : ℂ) ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hs n
  have hp : (n : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn0)
  rw [GammaSeq_eq_poch, cpow_sub _ _ hn0, cpow_one]
  have := poch_ne_zero_of_not_neg_nat hs n
  have := (Nat.cast_ne_zero (R := ℂ)).mpr n.factorial_ne_zero
  field_simp
  rw [add_comm (n : ℂ) s, div_self hsn]

/-- Gauss asymptotics of a multiset rising-factorial product. -/
lemma ghbR4_genPoch_tendsto (a : Multiset ℂ) (ha : ∀ x ∈ a, ∀ k : ℕ, x ≠ -k) :
    Tendsto (fun n : ℕ => genPoch a n * (n : ℂ) ^ (a.map (fun x => 1 - x)).sum /
      (n.factorial : ℂ) ^ a.card) atTop (𝓝 (a.map fun x => (Gamma x)⁻¹).prod) := by
  induction a using Multiset.induction_on with
  | empty => simp [genPoch]
  | @cons x a ih =>
    have hx := ghbR4_poch_tendsto (ha x (Multiset.mem_cons_self x a))
    have ih' := ih (fun y hy => ha y (Multiset.mem_cons_of_mem hy))
    simp only [Multiset.map_cons, Multiset.prod_cons]
    apply (hx.mul ih').congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [genPoch, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons,
      Multiset.card_cons, cpow_add _ _ hn0, pow_succ]
    ring

/-- Sum of `1 - x` over a multiset. -/
lemma ghbR4_sum_one_sub (a : Multiset ℂ) :
    (a.map (fun x => 1 - x)).sum = a.card - a.sum := by
  induction a using Multiset.induction_on with
  | empty => simp
  | @cons x a ih => simp [Multiset.sum_cons, ih]; ring

/-- A product of reciprocal Gamma values at regular points is nonzero. -/
lemma ghbR4_prod_inv_Gamma_ne_zero {a : Multiset ℂ} (ha : ∀ x ∈ a, ∀ k : ℕ, x ≠ -k) :
    (a.map fun x => (Gamma x)⁻¹).prod ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro h0
  obtain ⟨x, hx, heq⟩ := Multiset.mem_map.mp h0
  exact inv_ne_zero (Gamma_ne_zero (ha x hx)) heq

/-- Balanced coefficients satisfy `genCoeff a b n · n^(γ+1) → Π Γ(a)⁻¹ / Π Γ(b)⁻¹`. -/
lemma ghbR4_genCoeff_tendsto {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (ha : ∀ x ∈ a, ∀ k : ℕ, x ≠ -k) (hb : genDenRegular b) :
    Tendsto (fun n : ℕ => genCoeff a b n * (n : ℂ) ^ (genExcess a b + 1)) atTop
      (𝓝 ((a.map fun x => (Gamma x)⁻¹).prod / (b.map fun x => (Gamma x)⁻¹).prod)) := by
  apply ((ghbR4_genPoch_tendsto a ha).div (ghbR4_genPoch_tendsto b hb)
    (ghbR4_prod_inv_Gamma_ne_zero hb)).congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hexp : genExcess a b + 1 = (a.map (fun x => 1 - x)).sum - (b.map (fun x => 1 - x)).sum := by
    rw [ghbR4_sum_one_sub, ghbR4_sum_one_sub, h, genExcess]; push_cast; ring
  rw [hexp, cpow_sub _ _ hn0, h, genCoeff, Pi.div_apply]
  have := genPoch_ne_zero hb n
  have := (Nat.cast_ne_zero (R := ℂ)).mpr n.factorial_ne_zero
  have : (n : ℂ) ^ (b.map (fun x => 1 - x)).sum ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn0)
  field_simp
  ring

/-- Norm form: `‖genCoeff a b n‖ · n^(Re γ + 1)` tends to a positive limit. -/
lemma ghbR4_norm_genCoeff_tendsto {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (ha : ∀ x ∈ a, ∀ k : ℕ, x ≠ -k) (hb : genDenRegular b) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (fun n : ℕ => ‖genCoeff a b n‖ * (n : ℝ) ^ ((genExcess a b).re + 1))
      atTop (𝓝 L) := by
  refine ⟨_, norm_pos_iff.mpr (div_ne_zero (ghbR4_prod_inv_Gamma_ne_zero ha)
    (ghbR4_prod_inv_Gamma_ne_zero hb)), (ghbR4_genCoeff_tendsto h ha hb).norm.congr' ?_⟩
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [norm_mul, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

/-- A nonterminating upper multiset has no nonpositive integer entry. -/
lemma ghbR4_not_neg_of_not_terminates {a : Multiset ℂ} (ha : ¬genTerminates a) :
    ∀ x ∈ a, ∀ k : ℕ, x ≠ -k := fun x hx k hxk => ha ⟨x, hx, k, hxk⟩

/-- The balanced nonterminating coefficients are absolutely summable iff `Re γ > 0`. -/
lemma ghbR4_summable_norm_iff {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (ha : ¬genTerminates a) :
    Summable (fun n : ℕ => ‖genCoeff a b n‖) ↔ 0 < (genExcess a b).re := by
  obtain ⟨L, hL, hlim⟩ := ghbR4_norm_genCoeff_tendsto h (ghbR4_not_neg_of_not_terminates ha) hb
  set e := (genExcess a b).re + 1
  have heq : Asymptotics.IsEquivalent atTop (fun n : ℕ => ‖genCoeff a b n‖)
      (fun n : ℕ => L * (n : ℝ) ^ (-e)) := by
    apply Asymptotics.isEquivalent_of_tendsto_one
    have := hlim.div_const L
    rw [div_self hL.ne'] at this
    apply this.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simp only [Pi.div_apply, Real.rpow_neg hn'.le]
    have : (n : ℝ) ^ e ≠ 0 := (Real.rpow_pos_of_pos hn' e).ne'
    field_simp
  rw [heq.summable_iff_nat, summable_mul_left_iff hL.ne', Real.summable_nat_rpow]
  constructor <;> intro hh <;> linarith

/-- Convergence of natural partial sums forces the terms to tend to zero. -/
lemma ghbR4_tendsto_zero_of_converges {a b : Multiset ℂ} {z v : ℂ}
    (hv : genSeriesConvergesTo a b z v) :
    Tendsto (fun n : ℕ => genCoeff a b n * z ^ n) atTop (𝓝 0) := by
  have hS : Tendsto (fun N : ℕ => ∑ n ∈ range N, genCoeff a b n * z ^ n) atTop (𝓝 v) := hv
  have hS' : Tendsto (fun N : ℕ => ∑ n ∈ range (N + 1), genCoeff a b n * z ^ n)
      atTop (𝓝 v) := (tendsto_add_atTop_iff_nat 1).2 hS
  simpa only [Finset.sum_range_succ, add_sub_cancel_left, sub_self] using hS'.sub hS

/-- At one the guarded principal value is always the totalized series value. -/
lemma ghbR4_genRegularizedHG_one (a b : Multiset ℂ) :
    genRegularizedHG a b 1 = Complex.regularizedHGFun a b 1 := by
  classical
  unfold genRegularizedHG
  split_ifs with hc hF
  · exact (Classical.choice hF).one
  · rfl
  · rfl

/-- The principal branch is analytic on the plane cut from one to positive infinity. -/
theorem genHG_principal_analytic {a b : Multiset ℂ} (h : a.card = b.card + 1) :
    AnalyticOnNhd ℂ (genHG a b) cutPlane := by
  sorry

/-- Full criterion for absolute convergence on the unit circle in the nonterminating case. -/
theorem genHG_unit_absolute_iff {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (ha : ¬genTerminates a) {z : ℂ} (hz : ‖z‖ = 1) :
    genSeriesAbsolutelyConverges a b z ↔ 0 < (genExcess a b).re := by
  unfold genSeriesAbsolutelyConverges
  simp only [norm_mul, norm_pow, hz, one_pow, mul_one]
  exact ghbR4_summable_norm_iff h hb ha

/-- Every nonunit point of the unit circle converges in natural order when the excess exceeds minus one. -/
theorem genHG_unit_conditional {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (hγ : -1 < (genExcess a b).re) : genSeriesConvergesTo a b z (genHG a b z) := by
  sorry

/-- Positive excess gives absolute convergence to the declared endpoint value. -/
theorem genHG_one_hasSum {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (hγ : 0 < (genExcess a b).re) :
    HasSum (fun n : ℕ => genCoeff a b n) (genHG a b 1) := by
  have hs : Summable (fun n : ℕ => genCoeff a b n) := by
    by_cases ha : genTerminates a
    · obtain ⟨x, hx, m, rfl⟩ := ha
      apply summable_of_ne_finset_zero (s := range (m + 1))
      intro n hn
      have hmn : m < n := by simp only [Finset.mem_range, not_lt] at hn; omega
      unfold genCoeff genPoch
      rw [Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨_, hx, poch_neg_nat_eq_zero hmn⟩),
        zero_div]
    · exact Summable.of_norm ((ghbR4_summable_norm_iff h hb ha).mpr hγ)
  convert hs.hasSum using 1
  rw [genHG, ghbR4_genRegularizedHG_one, regularizedHGFun_eq_tsum', ← tsum_mul_left]
  congr 1
  funext n
  rw [genCoeff_eq_gamma_mul_regularized hb, one_pow, mul_one]

/-- At real excess at most minus one, no point of the unit circle converges in the nonterminating case. -/
theorem genHG_unit_diverges {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (ha : ¬genTerminates a) {z : ℂ} (hz : ‖z‖ = 1)
    (hγ : (genExcess a b).re ≤ -1) : ¬∃ v : ℂ, genSeriesConvergesTo a b z v := by
  rintro ⟨v, hv⟩
  obtain ⟨L, hL, hlim⟩ := ghbR4_norm_genCoeff_tendsto h (ghbR4_not_neg_of_not_terminates ha) hb
  have ht : Tendsto (fun n : ℕ => ‖genCoeff a b n‖) atTop (𝓝 0) := by
    simpa only [norm_mul, norm_pow, hz, one_pow, mul_one, norm_zero] using
      (ghbR4_tendsto_zero_of_converges hv).norm
  have h0 : Tendsto (fun n : ℕ => ‖genCoeff a b n‖ * (n : ℝ) ^ ((genExcess a b).re + 1))
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ ht
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
    calc ‖genCoeff a b n‖ * (n : ℝ) ^ ((genExcess a b).re + 1)
        ≤ ‖genCoeff a b n‖ * 1 := by
          gcongr
          exact Real.rpow_le_one_of_one_le_of_nonpos hn' (by linarith)
      _ = _ := mul_one _
  exact hL.ne' (tendsto_nhds_unique hlim h0)

/- The next finite-product normalization follows the private ratio-test lemmas
in Mathlib's `RegularizedHypergeometric`, due to Moritz Doll.  Here it is
extended to the positive-degree case, where the coefficient ratio tends to infinity. -/

/-- `∏ (aᵢ + n) = n ^ card a * ∏ (aᵢ / n + 1)` for `n ≠ 0`. -/
private lemma gen_prod_shift (a : Multiset ℂ) {n : ℕ} (hn : n ≠ 0) :
    (a.map (· + (n : ℂ))).prod = n ^ a.card * (a.map (· / (n : ℂ) + 1)).prod := calc
  _ = (a.map (fun j ↦ n * (j / (n : ℂ) + 1))).prod := by
    congr; ext; field_simp
  _ = _ := by simp [Multiset.prod_map_mul]

/-- The shifted-product ratio `∏(aᵢ+n)/(∏(bⱼ+n)(n+1))` factored as a power of `n`
times normalized products. -/
private lemma gen_prod_ratio (a b : Multiset ℂ) {n : ℕ} (hn : n ≠ 0) :
    (a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod * (n + 1)) =
      n ^ (a.card - (b.card : ℤ) - 1) * (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹)) := by
  rw [gen_prod_shift a hn, gen_prod_shift b hn]
  field_simp
  congr 1
  calc
    _ = n * n ^ b.card * n ^ (a.card - b.card - (1 : ℤ)) *
        (a.map (fun x : ℂ ↦ (x + n) / n)).prod := by
      congr 1
      rw [← pow_succ', ← zpow_natCast, ← zpow_natCast, ← zpow_add' (by left; norm_cast)]
      grind
    _ = _ := by ring

/-- The normalized product `∏ (aᵢ / n + 1)` tends to `1` as `n → ∞`. -/
private lemma gen_prod_normalized_tendsto (a : Multiset ℂ) :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod) atTop (𝓝 1) := by
  suffices ∀ i ∈ a, Tendsto (fun n : ℕ ↦ (i / n + 1)) atTop (𝓝 ((fun _ : ℂ ↦ 1) i)) by
    simpa using tendsto_multiset_prod _ this
  intro i hi
  simpa using (tendsto_const_div_atTop_nhds_zero_nat i).add_const 1

/-- The ratio of normalized products appearing in `gen_prod_ratio` tends to `1`. -/
private lemma gen_prod_normalized_ratio_tendsto (a b : Multiset ℂ) :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have := (gen_prod_normalized_tendsto a).div
    ((gen_prod_normalized_tendsto b).mul (h.const_add 1)) (by simp)
  simp only [add_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, div_self] at this
  apply this.congr
  simp

/-- Telescoping (hockey-stick) identity for partial sums of Pochhammer ratios. -/
lemma ghbR4_hockey (x : ℂ) (N : ℕ) :
    ∑ n ∈ range (N + 1), poch x n / (n.factorial : ℂ) = poch (x + 1) N / (N.factorial : ℂ) := by
  induction N with
  | zero => simp [poch_zero]
  | succ N ih =>
    rw [sum_range_succ, ih, poch_succ_left, poch_succ, Nat.factorial_succ]
    have := (Nat.cast_ne_zero (R := ℂ)).mpr N.factorial_ne_zero
    have : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast N.succ_ne_zero
    push_cast
    field_simp
    ring

/-- The powers `N^(-γ)` with `γ ≠ 0` cannot converge to a nonzero limit. -/
lemma ghbR4_not_tendsto_cpow {γ : ℂ} (hγ : γ ≠ 0) {L : ℂ} (hL : L ≠ 0) :
    ¬Tendsto (fun N : ℕ => (N : ℂ) ^ (-γ)) atTop (𝓝 L) := by
  intro ht
  have hm : ∀ m : ℕ, 1 ≤ m → (m : ℂ) ^ (-γ) = 1 := by
    intro m hm1
    have hsub : Tendsto (fun N : ℕ => ((m * N : ℕ) : ℂ) ^ (-γ)) atTop (𝓝 L) :=
      ht.comp (tendsto_id.const_mul_atTop' (by omega : 0 < m))
    have h2 : Tendsto (fun N : ℕ => ((m * N : ℕ) : ℂ) ^ (-γ)) atTop
        (𝓝 ((m : ℂ) ^ (-γ) * L)) := by
      refine (ht.const_mul ((m : ℂ) ^ (-γ))).congr fun N => ?_
      push_cast; rw [natCast_mul_natCast_cpow]
    exact (mul_eq_right₀ hL).mp (tendsto_nhds_unique h2 hsub)
  have hlog := (Complex.continuous_ofReal.tendsto 0 |>.comp Real.tendsto_log_nat_add_one_sub_log).const_mul γ
  rw [Complex.ofReal_zero, mul_zero] at hlog
  have hev := (hlog.eventually (Metric.ball_mem_nhds 0 (by positivity : (0:ℝ) < 2 * π)))
  obtain ⟨M, hM⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have h1 := hm M hM.2
  have h2 := hm (M + 1) (by omega)
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hM1 : ((M + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : M + 1 ≠ 0)
  rw [cpow_def_of_ne_zero hM0] at h1
  rw [cpow_def_of_ne_zero hM1] at h2
  have h3 : Complex.exp (-(γ * ((Real.log (M + 1) - Real.log M : ℝ) : ℂ))) = 1 := by
    have : -(γ * ((Real.log (M + 1) - Real.log M : ℝ) : ℂ)) =
        Complex.log ((M + 1 : ℕ) : ℂ) * -γ - Complex.log (M : ℂ) * -γ := by
      rw [← natCast_log, ← natCast_log]; push_cast; ring
    rw [this, Complex.exp_sub, h1, h2, div_one]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h3
  have hball := hM.1
  simp only [Function.comp_apply] at hball
  rw [dist_zero_right, ← norm_neg, hk] at hball
  have hk0 : k = 0 := by
    by_contra hk0
    have : (2 * π : ℝ) ≤ ‖(k : ℂ) * (2 * π * I)‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      have : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
      nlinarith [Real.pi_pos]
    linarith
  rw [hk0, Int.cast_zero, zero_mul, neg_eq_zero, mul_eq_zero] at hk
  rcases hk with hk | hk
  · exact hγ hk
  · have hpos : Real.log M < Real.log (M + 1) :=
      Real.log_lt_log (by exact_mod_cast (by omega : 0 < M)) (by linarith)
    have : Real.log (M + 1) - Real.log M = 0 := by exact_mod_cast hk
    linarith

/-- The model series `∑ (-γ)_n/n!` diverges when `Re γ ≤ 0` and `γ ≠ 0`. -/
lemma ghbR4_model_not_conv {γ : ℂ} (hσ : γ.re ≤ 0) (hγ0 : γ ≠ 0) :
    ¬∃ L, Tendsto (fun N : ℕ => ∑ n ∈ range N, poch (-γ) n / (n.factorial : ℂ)) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hL' := (tendsto_add_atTop_iff_nat 1).2 hL
  simp only [ghbR4_hockey] at hL'
  set s := -γ + 1 with hs
  have hsp : ∀ k : ℕ, s ≠ -k := by
    intro k hk
    have := congrArg Complex.re hk
    simp [hs] at this
    linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hG := ghbR4_poch_tendsto hsp
  have hGne : (Gamma s)⁻¹ ≠ 0 := inv_ne_zero (Gamma_ne_zero hsp)
  have hq := hL'.div hG hGne
  have hpow : Tendsto (fun N : ℕ => (N : ℂ) ^ (-γ)) atTop (𝓝 (L / (Gamma s)⁻¹)) := by
    refine hq.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have h1s : 1 - s = γ := by rw [hs]; ring
    rw [h1s]
    have := poch_ne_zero_of_not_neg_nat hsp N
    have := (Nat.cast_ne_zero (R := ℂ)).mpr N.factorial_ne_zero
    have hg : (N : ℂ) ^ γ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hN0)
    rw [cpow_neg, Pi.div_apply]
    field_simp
  have hnorm : 1 ≤ ‖L / (Gamma s)⁻¹‖ := by
    refine ge_of_tendsto hpow.norm ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [norm_natCast_cpow_of_pos (by omega)]
    exact Real.one_le_rpow (by exact_mod_cast hN) (by simp; linarith)
  exact ghbR4_not_tendsto_cpow hγ0 (norm_pos_iff.mp (by linarith)) hpow

/-- The model series `∑ (1)_n/(2)_n = ∑ 1/(n+1)` diverges. -/
lemma ghbR4_harmonic_not_conv :
    ¬∃ L, Tendsto (fun N : ℕ => ∑ n ∈ range N, poch 1 n / poch 2 n) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hre := (Complex.continuous_re.tendsto L).comp hL
  have heq : (Complex.re ∘ fun N : ℕ => ∑ n ∈ range N, poch 1 n / poch 2 n) =
      fun N => ∑ n ∈ range N, (1 / (n + 1) : ℝ) := by
    funext N
    simp only [Function.comp_apply, Complex.re_sum]
    apply sum_congr rfl
    intro n _
    rw [poch_nat_one, poch_nat_two, Nat.factorial_succ]
    have := (Nat.cast_ne_zero (R := ℂ)).mpr n.factorial_ne_zero
    rw [show ((n.factorial : ℂ) / (((n + 1) * n.factorial : ℕ) : ℂ)) = ((1 / (n + 1) : ℝ) : ℂ) by
      push_cast; field_simp]
    exact Complex.ofReal_re _
  rw [heq] at hre
  exact not_tendsto_nhds_of_tendsto_atTop Real.tendsto_sum_range_one_div_nat_succ_atTop _ hre

/-- The first elementary symmetric function of a multiset is its sum. -/
lemma ghbR4_esymm_one (s : Multiset ℂ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

/-- Two monic linear-factor products with equal degree and equal root sums differ
by a polynomial of degree at most `card - 2`. -/
lemma ghbR4_prod_diff_bound (u v : Multiset ℂ) (hc : u.card = v.card) (hs : u.sum = v.sum) :
    ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖(u.map (· + (x : ℂ))).prod - (v.map (· + (x : ℂ))).prod‖ ≤ K * x ^ (u.card - 2) := by
  open Polynomial in
  set Pu : ℂ[X] := (u.map fun r => X + C r).prod
  set Pv : ℂ[X] := (v.map fun r => X + C r).prod
  have hdu : Pu.natDegree = u.card := by
    rw [Polynomial.natDegree_multiset_prod_of_monic _ (fun P hP => by
      obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hP; exact monic_X_add_C x)]
    simp [Multiset.map_map]
  have hdv : Pv.natDegree = v.card := by
    rw [Polynomial.natDegree_multiset_prod_of_monic _ (fun P hP => by
      obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hP; exact monic_X_add_C x)]
    simp [Multiset.map_map]
  set D := Pu - Pv
  set d := u.card - 2
  have hD : ∀ k, d < k → D.coeff k = 0 := by
    intro k hk
    simp only [D, coeff_sub]
    by_cases hku : k ≤ u.card
    · rw [Multiset.prod_X_add_C_coeff u hku, Multiset.prod_X_add_C_coeff v (hc ▸ hku), ← hc]
      have : u.card - k = 0 ∨ u.card - k = 1 := by omega
      rcases this with h | h <;> rw [h]
      · simp
      · rw [ghbR4_esymm_one, ghbR4_esymm_one, hs, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega),
        sub_zero]
  have hDdeg : D.natDegree ≤ d := natDegree_le_iff_coeff_eq_zero.mpr hD
  refine ⟨∑ i ∈ range (d + 1), ‖D.coeff i‖, fun x hx => ?_⟩
  have heval : (u.map (· + (x : ℂ))).prod - (v.map (· + (x : ℂ))).prod = D.eval (x : ℂ) := by
    simp only [D, Pu, Pv, eval_sub, eval_multiset_prod, Multiset.map_map, Function.comp_def,
      eval_add, eval_X, eval_C, add_comm (x : ℂ)]
  rw [heval, eval_eq_sum_range' (n := d + 1) (by omega), sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  gcongr
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)

/-- Lower bound `(x/2)^card` for `∏ (y + x)` when `2‖y‖ ≤ x` for all roots `y`. -/
lemma ghbR4_prod_lower (v : Multiset ℂ) {x : ℝ} (hx0 : 0 ≤ x) (hx : ∀ y ∈ v, 2 * ‖y‖ ≤ x) :
    (x / 2) ^ v.card ≤ ‖(v.map (· + (x : ℂ))).prod‖ := by
  induction v using Multiset.induction_on with
  | empty => simp
  | @cons y v ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm]
    have hy := hx y (Multiset.mem_cons_self y v)
    have h1 : x / 2 ≤ ‖y + (x : ℂ)‖ := by
      have := norm_sub_norm_le (x : ℂ) (-y)
      rw [Complex.norm_real, Real.norm_of_nonneg hx0, norm_neg, sub_neg_eq_add, add_comm] at this
      linarith
    exact mul_le_mul h1 (ih fun z hz => hx z (Multiset.mem_cons_of_mem hz)) (by positivity)
      (norm_nonneg _)

/-- Successor step for generalized Pochhammer products. -/
lemma ghbR4_genPoch_succ (a : Multiset ℂ) (n : ℕ) :
    genPoch a (n + 1) = genPoch a n * (a.map (· + (n : ℂ))).prod := by
  unfold genPoch
  rw [← Multiset.prod_map_mul]
  congr 1
  exact Multiset.map_congr rfl fun x _ => poch_succ x n

/-- Ratio identity between consecutive generalized hypergeometric coefficients. -/
lemma ghbR4_genCoeff_succ {a b : Multiset ℂ} (hb : genDenRegular b) (n : ℕ) :
    genCoeff a b (n + 1) * ((b.map (· + (n : ℂ))).prod * (n + 1)) =
      genCoeff a b n * (a.map (· + (n : ℂ))).prod := by
  have h1 := genPoch_ne_zero hb n
  have h2 := genPoch_ne_zero hb (n + 1)
  rw [ghbR4_genPoch_succ] at h2
  have h3 := (Nat.cast_ne_zero (R := ℂ)).mpr n.factorial_ne_zero
  have h4 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have h5 : (b.map (· + (n : ℂ))).prod ≠ 0 := right_ne_zero_of_mul h2
  unfold genCoeff
  rw [ghbR4_genPoch_succ, ghbR4_genPoch_succ, Nat.factorial_succ]
  push_cast
  field_simp

/-- Summable tail bound from a summable-difference bound `‖d (n+1) - d n‖ ≤ K/n²`. -/
lemma ghbR4_tail_bound {d : ℕ → ℂ} {D : ℂ} {K : ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (hd : Tendsto d atTop (𝓝 D)) (hK : ∀ n, n₀ ≤ n → ‖d (n + 1) - d n‖ ≤ K / (n : ℝ) ^ 2) :
    ∀ n, n₀ ≤ n → ‖d n - D‖ ≤ K / ((n : ℝ) - 1) := by
  intro n hn
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg _).trans (hK n₀ le_rfl)
    have hpos : (0 : ℝ) < (n₀ : ℝ) ^ 2 := by positivity
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hpos))
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hM : ∀ M, n ≤ M → ‖d M - d n‖ ≤ K * (1 / ((n : ℝ) - 1) - 1 / ((M : ℝ) - 1)) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hnM ih =>
      have hM1 : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
      calc ‖d (M + 1) - d n‖ ≤ ‖d (M + 1) - d M‖ + ‖d M - d n‖ := by
            rw [show d (M + 1) - d n = (d (M + 1) - d M) + (d M - d n) by ring]
            exact norm_add_le _ _
        _ ≤ K / (M : ℝ) ^ 2 + K * (1 / ((n : ℝ) - 1) - 1 / ((M : ℝ) - 1)) :=
            add_le_add (hK M (by omega)) ih
        _ ≤ K * (1 / ((n : ℝ) - 1) - 1 / (((M + 1 : ℕ) : ℝ) - 1)) := by
            push_cast
            have : 1 / (M : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) - 1 / ((M : ℝ) + 1 - 1) := by
              rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity)
                (by nlinarith)]
              nlinarith
            have h' := mul_le_mul_of_nonneg_left this hK0
            rw [div_eq_mul_one_div K]
            linarith
  have hlim : Tendsto (fun M => ‖d M - d n‖) atTop (𝓝 ‖D - d n‖) :=
    ((hd.sub_const (d n)).norm)
  have := le_of_tendsto (b := K * (1 / ((n : ℝ) - 1))) hlim (by
    filter_upwards [eventually_ge_atTop n, eventually_ge_atTop 2] with M hMn hM2
    have hM1 : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
    refine (hM M hMn).trans ?_
    have : 0 ≤ 1 / ((M : ℝ) - 1) := by
      have : (0:ℝ) < (M : ℝ) - 1 := by linarith
      positivity
    nlinarith)
  rw [norm_sub_rev] at this
  calc ‖d n - D‖ ≤ K * (1 / ((n : ℝ) - 1)) := this
    _ = K / ((n : ℝ) - 1) := by ring

/-- For `Re γ ≤ 0` there are regular parameters `α, β` with `β - α = 1 + γ` whose model
series `∑ (α)_n/(β)_n` diverges. -/
private lemma gen_one_model {γ : ℂ} (hγ : γ.re ≤ 0) :
    ∃ α β : ℂ, (∀ k : ℕ, α ≠ -k) ∧ (∀ k : ℕ, β ≠ -k) ∧ β - α = 1 + γ ∧
      ¬∃ L, Tendsto (fun N : ℕ => ∑ n ∈ range N, poch α n / poch β n) atTop (𝓝 L) := by
  by_cases h0 : γ = 0
  · refine ⟨1, 2, fun k hk => ?_, fun k hk => ?_, by rw [h0]; ring,
      ghbR4_harmonic_not_conv⟩ <;>
    · have := congrArg Complex.re hk; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  · refine ⟨-γ, 1, fun k hk => ?_, fun k hk => ?_, by ring, ?_⟩
    · rw [neg_inj] at hk
      have hre := congrArg Complex.re hk
      simp at hre
      have hk0 : (k : ℝ) = 0 := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      apply h0; rw [hk]; exact_mod_cast hk0
    · have := congrArg Complex.re hk; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    · simpa only [poch_nat_one] using ghbR4_model_not_conv hγ h0

/-- If `d (n+1) ∏(wᵢ+n) = d n ∏(uᵢ+n)` for bounded `d`, where `u, w` have equal cardinality
and equal sums, then the increments `d (n+1) - d n` are `O(n⁻²)`. -/
private lemma gen_ratio_step {d : ℕ → ℂ} {u w : Multiset ℂ} {k : ℕ} (hu : u.card = k + 2)
    (hw : w.card = k + 2) (hsum : u.sum = w.sum) {B : ℝ} (hB' : ∀ n, ‖d n‖ ≤ B)
    (hratio : ∀ n : ℕ, d (n + 1) * (w.map (· + (n : ℂ))).prod =
      d n * (u.map (· + (n : ℂ))).prod) :
    ∃ K2 : ℝ, ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n, n₀ ≤ n → ‖d (n + 1) - d n‖ ≤ K2 / (n : ℝ) ^ 2 := by
  obtain ⟨K, hK⟩ := ghbR4_prod_diff_bound u w (hu.trans hw.symm) hsum
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  set R : ℝ := (w.map (‖·‖)).sum
  have hR : ∀ y ∈ w, ‖y‖ ≤ R := fun y hy =>
    Multiset.single_le_sum (fun z hz => by
      obtain ⟨t, -, rfl⟩ := Multiset.mem_map.mp hz; exact norm_nonneg t) _
      (Multiset.mem_map_of_mem _ hy)
  refine ⟨B * K * 2 ^ (k + 2), max 2 ⌈2 * R⌉₊, le_max_left _ _, fun n hn => ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hnR : 2 * R ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have hlow := ghbR4_prod_lower w (x := n) (by positivity)
    (fun y hy => by linarith [hR y hy])
  have hdiff := hK n (by linarith)
  rw [hu, Nat.add_sub_cancel] at hdiff
  rw [hw] at hlow
  simp only [Complex.ofReal_natCast] at hlow hdiff
  have hpos : 0 < ((n : ℝ) / 2) ^ (k + 2) := by positivity
  have hW : (w.map (· + (n : ℂ))).prod ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hlow; linarith
  have hK0 : 0 ≤ K * (n : ℝ) ^ k := (norm_nonneg _).trans hdiff
  have heq : d (n + 1) - d n = d n * ((u.map (· + (n : ℂ))).prod -
      (w.map (· + (n : ℂ))).prod) / (w.map (· + (n : ℂ))).prod := by
    have := hratio n
    field_simp
    linear_combination this
  rw [heq, norm_div, norm_mul]
  calc ‖d n‖ * ‖(u.map (· + (n : ℂ))).prod - (w.map (· + (n : ℂ))).prod‖ /
        ‖(w.map (· + (n : ℂ))).prod‖
      ≤ B * (K * (n : ℝ) ^ k) / ((n : ℝ) / 2) ^ (k + 2) := by
        gcongr
        exact hB' n
    _ = B * K * 2 ^ (k + 2) / (n : ℝ) ^ 2 := by
        have : (n : ℝ) ≠ 0 := by positivity
        have h2 : ((1 : ℝ) / 2) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
        field_simp
        linear_combination (-(B * K * (n : ℝ) ^ 2 * (n : ℝ) ^ k)) * h2

/-- Comparison test: if `m n ~ C₂ n^{-(γ+1)}` with `Re γ > -1` and `c n / m n → D₀ ≠ 0` at
rate `O(1/n)`, then convergence of `∑ c n` implies convergence of `∑ m n`. -/
private lemma gen_one_compare {c m : ℕ → ℂ} {v D0 C2 γ : ℂ} {K2 : ℝ} {n₀ : ℕ}
    (hn₀ : 2 ≤ n₀) (hσ : -1 < γ.re) (hmne : ∀ n, m n ≠ 0) (hD0 : D0 ≠ 0)
    (hC2 : Tendsto (fun n : ℕ => m n * (n : ℂ) ^ (γ + 1)) atTop (𝓝 C2))
    (htail : ∀ n, n₀ ≤ n → ‖c n / m n - D0‖ ≤ K2 / ((n : ℝ) - 1))
    (hv : Tendsto (fun N : ℕ => ∑ n ∈ range N, c n) atTop (𝓝 v)) :
    ∃ L, Tendsto (fun N : ℕ => ∑ n ∈ range N, m n) atTop (𝓝 L) := by
  set σ := γ.re
  have hmb : ∀ᶠ n : ℕ in atTop, ‖m n‖ ≤ (‖C2‖ + 1) * ((n : ℝ) ^ (σ + 1))⁻¹ := by
    have := hC2.norm.eventually (gt_mem_nhds (lt_add_one ‖C2‖))
    filter_upwards [this, eventually_gt_atTop 0] with n hn hn0
    rw [norm_mul, norm_natCast_cpow_of_pos hn0] at hn
    have : (0 : ℝ) < (n : ℝ) ^ (σ + 1) := Real.rpow_pos_of_pos (by exact_mod_cast hn0) _
    simp only [Complex.add_re, Complex.one_re] at hn
    rw [← div_eq_mul_inv, le_div_iff₀ this]
    exact hn.le
  have hdiffb : ∀ᶠ n : ℕ in atTop,
      ‖c n - D0 * m n‖ ≤ (2 * (‖C2‖ + 1) * K2) * ((n : ℝ) ^ (σ + 2))⁻¹ := by
    filter_upwards [hmb, eventually_ge_atTop n₀] with n hmn hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn₀.trans hn
    have ht := htail n hn
    have hK20 : 0 ≤ K2 := by
      have := (norm_nonneg _).trans ht
      exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])
    have hcd : c n - D0 * m n = m n * (c n / m n - D0) := by field_simp [hmne n]
    have hp : (0 : ℝ) < (n : ℝ) ^ (σ + 1) := Real.rpow_pos_of_pos (by linarith) _
    have hp2 : (n : ℝ) ^ (σ + 2) = (n : ℝ) ^ (σ + 1) * n := by
      rw [show σ + 2 = (σ + 1) + 1 by ring, Real.rpow_add_one (by positivity)]
    rw [hcd, norm_mul, hp2]
    calc ‖m n‖ * ‖c n / m n - D0‖
          ≤ ((‖C2‖ + 1) * ((n : ℝ) ^ (σ + 1))⁻¹) * (K2 / ((n : ℝ) - 1)) :=
          mul_le_mul hmn ht (norm_nonneg _) (by positivity)
      _ ≤ ((‖C2‖ + 1) * ((n : ℝ) ^ (σ + 1))⁻¹) * (2 * K2 / n) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith
      _ = (2 * (‖C2‖ + 1) * K2) * ((n : ℝ) ^ (σ + 1) * n)⁻¹ := by
          field_simp
  have hsumm : Summable fun n => c n - D0 * m n := by
    refine Summable.of_norm_bounded_eventually
      ((Real.summable_nat_rpow_inv.mpr (by linarith : (1 : ℝ) < σ + 2)).mul_left
        (2 * (‖C2‖ + 1) * K2)) ?_
    exact Nat.cofinite_eq_atTop ▸ hdiffb
  refine ⟨(v - ∑' n, (c n - D0 * m n)) / D0, ?_⟩
  refine ((hv.sub hsumm.hasSum.tendsto_sum_nat).div_const D0).congr fun N => ?_
  rw [← Finset.sum_sub_distrib]
  have hx : ∀ x, c x - (c x - D0 * m x) = D0 * m x := fun x => by ring
  simp only [hx, ← Finset.mul_sum]
  field_simp

/-- At one, natural-order convergence requires strictly positive real excess unless the series terminates. -/
theorem genHG_one_converges_iff {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (ha : ¬genTerminates a) :
    (∃ v : ℂ, genSeriesConvergesTo a b 1 v) ↔ 0 < (genExcess a b).re := by
  constructor
  swap
  · intro hγ
    refine ⟨genHG a b 1, ?_⟩
    have := (genHG_one_hasSum h hb hγ).tendsto_sum_nat
    simpa only [genSeriesConvergesTo, one_pow, mul_one] using this
  rintro ⟨v, hv⟩
  by_contra hγ
  push Not at hγ
  set γ := genExcess a b with hγdef
  by_cases hle : γ.re ≤ -1
  · exact genHG_unit_diverges h hb ha (z := 1) norm_one hle ⟨v, hv⟩
  push Not at hle
  have hv' : Tendsto (fun N : ℕ => ∑ n ∈ range N, genCoeff a b n) atTop (𝓝 v) := by
    simpa only [genSeriesConvergesTo, one_pow, mul_one] using hv
  -- the comparison model
  obtain ⟨α, β, hαp, hβp, hβα, hmodel⟩ := gen_one_model hγ
  set m : ℕ → ℂ := fun n => poch α n / poch β n with hm
  have hmne : ∀ n, m n ≠ 0 := fun n =>
    div_ne_zero (poch_ne_zero_of_not_neg_nat hαp n) (poch_ne_zero_of_not_neg_nat hβp n)
  have ha' := ghbR4_not_neg_of_not_terminates ha
  set c : ℕ → ℂ := fun n => genCoeff a b n with hc
  -- asymptotics of both sequences
  have hC1 := ghbR4_genCoeff_tendsto h ha' hb
  rw [← hγdef] at hC1
  set C1 := (a.map fun x => (Gamma x)⁻¹).prod / (b.map fun x => (Gamma x)⁻¹).prod
  have hC1ne : C1 ≠ 0 := div_ne_zero (ghbR4_prod_inv_Gamma_ne_zero ha')
    (ghbR4_prod_inv_Gamma_ne_zero hb)
  have hC2 : Tendsto (fun n : ℕ => m n * (n : ℂ) ^ (γ + 1)) atTop
      (𝓝 ((Gamma α)⁻¹ / (Gamma β)⁻¹)) := by
    refine ((ghbR4_poch_tendsto hαp).div (ghbR4_poch_tendsto hβp)
      (inv_ne_zero (Gamma_ne_zero hβp))).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have := poch_ne_zero_of_not_neg_nat hβp n
    have := (Nat.cast_ne_zero (R := ℂ)).mpr n.factorial_ne_zero
    have h1 : γ + 1 = (1 - α) - (1 - β) := by linear_combination -hβα
    have : (n : ℂ) ^ (1 - β) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn0)
    simp only [Pi.div_apply, hm, h1, cpow_sub _ _ hn0]
    field_simp
  set C2 := (Gamma α)⁻¹ / (Gamma β)⁻¹
  have hC2ne : C2 ≠ 0 := div_ne_zero (inv_ne_zero (Gamma_ne_zero hαp))
    (inv_ne_zero (Gamma_ne_zero hβp))
  set d : ℕ → ℂ := fun n => c n / m n with hd
  have hdlim : Tendsto d atTop (𝓝 (C1 / C2)) := by
    refine (hC1.div hC2 hC2ne).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have : (n : ℂ) ^ (γ + 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn0)
    have := hmne n
    simp only [Pi.div_apply, hd, hc]
    field_simp
  -- the exact ratio identity
  set u : Multiset ℂ := β ::ₘ a
  set w : Multiset ℂ := α ::ₘ 1 ::ₘ b
  have hsum : u.sum = w.sum := by
    simp only [u, w, Multiset.sum_cons]
    have : β - α = 1 + (b.sum - a.sum) := by rw [hβα, hγdef, genExcess]
    linear_combination this
  have hratio : ∀ n : ℕ, d (n + 1) * (w.map (· + (n : ℂ))).prod =
      d n * (u.map (· + (n : ℂ))).prod := by
    intro n
    have hcs := ghbR4_genCoeff_succ (a := a) hb n
    have hαn : α + n ≠ 0 := by simpa [eq_neg_iff_add_eq_zero] using hαp n
    have hβn : β + n ≠ 0 := by simpa [eq_neg_iff_add_eq_zero] using hβp n
    have hms : m (n + 1) = m n * (α + n) / (β + n) := by
      simp only [hm, poch_succ]
      have := poch_ne_zero_of_not_neg_nat hβp n
      field_simp
    have hmn := hmne n
    have hq : c (n + 1) / m (n + 1) = c (n + 1) * (β + n) / (m n * (α + n)) := by
      rw [hms]; field_simp
    show c (n + 1) / m (n + 1) * (w.map (· + (n : ℂ))).prod =
      c n / m n * (u.map (· + (n : ℂ))).prod
    rw [hq]
    simp only [u, w, Multiset.map_cons, Multiset.prod_cons]
    generalize m n = M at hmn ⊢
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_eq_div_iff (mul_ne_zero hmn hαn) hmn]
    simp only [hc]
    linear_combination (β + n) * (α + n) * M * hcs
  -- boundedness of `d` and the `O(n⁻²)` increments
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto d hdlim)
  obtain ⟨K2, n₀, hn₀, hstep⟩ := gen_ratio_step (k := b.card) (by simp [u, h]) (by simp [w])
    hsum (fun n => hB _ ⟨n, rfl⟩) hratio
  exact hmodel (gen_one_compare hn₀ hle hmne (div_ne_zero hC1ne hC2ne) hC2
    (ghbR4_tail_bound hn₀ hdlim hstep) hv')

/-- The nonterminating p>q+1 formal series has radius zero. -/
theorem genHG_radius_zero {a b : Multiset ℂ} (h : b.card + 1 < a.card)
    (hb : genDenRegular b) (ha : ¬genTerminates a) :
    (FormalMultilinearSeries.ofScalars ℂ (genCoeff a b)).radius = 0 := by
  rw [genScalarSeries_eq_gamma_smul hb,
    FormalMultilinearSeries.radius_smul_eq _ (genGamma_ne_zero hb)]
  apply FormalMultilinearSeries.ofScalars_radius_eq_zero_of_tendsto
  have hp : 0 < (a.card : ℤ) - b.card - 1 := by omega
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ((a.card : ℤ) - b.card - 1)) atTop atTop :=
    (tendsto_zpow_atTop_atTop hp).comp tendsto_natCast_atTop_atTop
  have hprod := (gen_prod_normalized_ratio_tendsto a b).norm
  simp only [norm_one] at hprod
  have hlim := Filter.Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) ht hprod
  apply hlim.congr'
  have h_ne := Complex.eventually_atTop_regularizedHGFunCoeff_ne_zero b
    (fun x hx n hxn => ha ⟨x, hx, n, hxn⟩)
  filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
  rw [Nat.succ_eq_add_one, ← Complex.norm_div,
    Complex.regularizedHGFunCoeff_add_one_div_self hn₁, gen_prod_ratio a b hn₂, ← mul_div,
    norm_mul, norm_zpow, Complex.norm_natCast]

/-- The nonterminating overbalanced formal series diverges at every nonzero argument. -/
theorem genHG_diverges_nonzero {a b : Multiset ℂ} (h : b.card + 1 < a.card)
    (hb : genDenRegular b) (ha : ¬genTerminates a) {z : ℂ} (hz : z ≠ 0) :
    ¬∃ v : ℂ, genSeriesConvergesTo a b z v := by
  rintro ⟨v, hv⟩
  have hS : Tendsto (fun N : ℕ => ∑ n ∈ range N, genCoeff a b n * z ^ n) atTop (𝓝 v) := hv
  have hS' : Tendsto (fun N : ℕ => ∑ n ∈ range (N + 1), genCoeff a b n * z ^ n)
      atTop (𝓝 v) := (tendsto_add_atTop_iff_nat 1).2 hS
  have ht : Tendsto (fun n : ℕ => genCoeff a b n * z ^ n) atTop (𝓝 0) := by
    simpa only [Finset.sum_range_succ, add_sub_cancel_left, sub_self] using hS'.sub hS
  have htn : Tendsto (fun n : ℕ => ‖genCoeff a b n‖ * ‖z‖ ^ n) atTop (𝓝 0) := by
    simpa only [norm_mul, norm_pow, norm_zero] using ht.norm
  have hr := (FormalMultilinearSeries.ofScalars ℂ (genCoeff a b)).le_radius_of_tendsto
    (r := ‖z‖₊) (by simpa only [FormalMultilinearSeries.ofScalars_norm, coe_nnnorm] using htn)
  rw [genHG_radius_zero h hb ha] at hr
  have : z = 0 := by simpa using hr
  exact hz this

/-- General branches continue along every path avoiding the possible finite singularities zero and one. -/
theorem genHG_continuation_along {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (γ : ℝ → ℂ) (hc : ContinuousOn γ (Icc 0 1))
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0 ∧ γ t ≠ 1) (h0 : ‖γ 0‖ < 1) :
    ∃ F : ℝ → ℂ → ℂ, TauCeti.IsAnalyticContinuationAlong F γ (Icc 0 1) ∧
      F 0 =ᶠ[𝓝 (γ 0)] Complex.regularizedHGFun a b := by
  sorry

/-- The regularized principal branch is jointly entire in all parameters at every nonsingular fixed argument. -/
@[dlmf 16.2.E5]
theorem genRegularizedHG_parameter_entire {p q : ℕ} (h : p ≤ q + 1) {z : ℂ} (hz : p = q + 1 → z ≠ 1) :
    Differentiable ℂ (fun P : (Fin p → ℂ) × (Fin q → ℂ) =>
      genRegularizedHG (genParams P.1) (genParams P.2) z) := by
  sorry

/-- Every fixed analytically continued regularized branch is jointly entire in its parameters. -/
@[dlmf 16.2.E5]
theorem genContinued_parameter_entire {q : ℕ} (γ : ℝ → ℂ) (hc : ContinuousOn γ (Icc 0 1))
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0 ∧ γ t ≠ 1) (h0 : ‖γ 0‖ < 1)
    (F : ((Fin (q + 1) → ℂ) × (Fin q → ℂ)) → ℝ → ℂ → ℂ)
    (hF : ∀ P, TauCeti.IsAnalyticContinuationAlong (F P) γ (Icc 0 1) ∧
      F P 0 =ᶠ[𝓝 (γ 0)] Complex.regularizedHGFun (genParams P.1) (genParams P.2)) :
    Differentiable ℂ (fun P => F P 1 (γ 1)) := by
  sorry

/-- Equal-order generalized hypergeometric functions have finitely many complex zeros exactly for a matched nonnegative-integer parameter difference. -/
theorem genHG_finite_zeros_iff {p : ℕ} (a b : Fin p → ℂ)
    (hb : genDenRegular (genParams b)) (ha : ¬genTerminates (genParams a)) :
    {z : ℂ | genHG (genParams a) (genParams b) z = 0}.Finite ↔
      ∃ σ : Equiv.Perm (Fin p), ∀ j, ∃ n : ℕ, a (σ j) - b j = n := by
  sorry

/-- Equal-order real parameters and real coefficient ratios give only finitely many real zeros. -/
theorem genHG_finite_real_zeros {p : ℕ} (a b : Fin p → ℂ)
    (hb : genDenRegular (genParams b)) (ha : ∀ j, (a j).im = 0)
    (hr : ∀ n : ℕ, (genPoch (genParams a) n / genPoch (genParams b) n).im = 0) :
    {x : ℝ | genHG (genParams a) (genParams b) x = 0}.Finite := by
  sorry

end DLMF.Hypergeometric
