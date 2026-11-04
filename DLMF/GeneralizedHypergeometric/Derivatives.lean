/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuationExistence
public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.Hypergeometric.Basic.GeneralizedCalculus
public import Mathlib.RingTheory.PowerSeries.Basic
public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.Solutions
public import DLMFMathlib.Analysis.Calculus.DifferentialOperators
public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Derivatives and contiguous functions (DLMF §16.3)

## Main definitions

* `genAnalyticDomain`: the analytic domain of a principal value (the whole plane for a
  polynomial).
* `GenContiguous`: contiguity, integer shifts of corresponding parameters.

## Main results

* `generalizedHypergeometric_iteratedDeriv`: all derivatives, DLMF 16.3.1;
  `regularizedGeneralizedHypergeometric_iteratedDeriv` is the regularized form, for all parameters.
* `generalizedHypergeometric_weighted_iteratedDeriv`,
  `generalizedHypergeometric_lower_weighted_iteratedDeriv`: weighted derivatives, DLMF 16.3.2 and
  16.3.4; the primed forms drop the regularity of `b`.
* `generalizedHypergeometric_raising_iterate`, `genRaiseOp_iterate`: iterated raising operators,
  DLMF 16.3.3 and 16.3.5; `generalizedHypergeometric_raising_iterate'` drops the regularity of `b`.
* `generalizedHypergeometric_0F1_contiguous`, `generalizedHypergeometric_3F2_contiguous`: contiguous
  relations, DLMF 16.3.6–16.3.7.
* `genContiguous_linear_relation`: any `q + 2` contiguous functions are linearly dependent over
  the rational functions.

## Implementation notes

The statements cover all orders and the global principal continuation. Every displayed lower
parameter is kept away from the nonpositive integers. Weighted powers use the principal slit
plane. Contiguous linear dependence over rational functions is expressed, after clearing
denominators, with polynomial coefficients. The general raising-operator identity uses
Mathlib's `iteratedDeriv_fun_mul` and analytic germ congruence; it does not depend on
hypergeometric continuation.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

/-- The analytic domain of a principal value, enlarged to the whole plane for a polynomial. -/
def genAnalyticDomain (a b : Multiset ℂ) : Set ℂ :=
  by classical exact if a.card ≤ b.card ∨ IsTerminating a then univ else cutPlane

/-- Generalized contiguity means integer shifts of corresponding vector parameters. -/
def GenContiguous {p q : ℕ} (a a' : Fin p → ℂ) (b b' : Fin q → ℂ) : Prop :=
  (∀ j, ∃ k : ℤ, a' j - a j = k) ∧ (∀ j, ∃ k : ℤ, b' j - b j = k)

/-- Iterated derivatives depend only on the germ. -/
private lemma iteratedDeriv_eventuallyEq {f g : ℂ → ℂ} {x : ℂ} (h : f =ᶠ[𝓝 x] g) (n : ℕ) :
    iteratedDeriv n f =ᶠ[𝓝 x] iteratedDeriv n g := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

/-- The rising factorial of the parameters, one step further. -/
private lemma pochhammerProduct_succ' (a : Multiset ℂ) (n : ℕ) :
    pochhammerProduct a (n + 1) = pochhammerProduct a n * (shiftParameters a n).prod := by
  unfold pochhammerProduct shiftParameters
  rw [← Multiset.prod_map_mul]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => pochhammer_succ x n)

/-- Shifting the parameters by `n` and then by one is shifting by `n + 1`. -/
private lemma shiftParams_shiftParameters (a : Multiset ℂ) (n : ℕ) :
    shiftParams (shiftParameters a n) = shiftParameters a (n + 1 : ℕ) := by
  unfold shiftParams shiftParameters
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

/-- The power series of the `n`th derivative of the regularized series. -/
private lemma hasFPowerSeriesOnBall_iteratedDeriv_regularizedHGFun (a b : Multiset ℂ)
    (hr : 0 < (Complex.regularizedHGFunSeries a b).radius) (n : ℕ) :
    HasFPowerSeriesOnBall (iteratedDeriv n (Complex.regularizedHGFun a b))
      (FormalMultilinearSeries.ofScalars ℂ fun k => pochhammerProduct a n *
        Complex.regularizedHGFunCoeff (shiftParameters a n) (shiftParameters b n) k) 0
      (Complex.regularizedHGFunSeries a b).radius := by
  induction n with
  | zero =>
    have h0 := (Complex.regularizedHGFunSeries a b).hasFPowerSeriesOnBall hr
    have hc : (fun k => pochhammerProduct a 0 *
        Complex.regularizedHGFunCoeff (shiftParameters a ((0 : ℕ) : ℂ))
        (shiftParameters b ((0 : ℕ) : ℂ)) k) = Complex.regularizedHGFunCoeff a b := by
      funext k
      simp [pochhammerProduct, shiftParameters, pochhammer_zero]
    rw [iteratedDeriv_zero, hc]
    exact h0
  | succ n ih =>
    rw [iteratedDeriv_succ]
    convert ih.deriv_ofScalars using 2
    funext k
    have h1 := regularizedHGFunCoeff_succ_deriv (shiftParameters a n) (shiftParameters b n) k
    rw [shiftParams_shiftParameters, shiftParams_shiftParameters] at h1
    rw [pochhammerProduct_succ']
    linear_combination (-pochhammerProduct a n) * h1

/-- The `n`th derivative of the regularized series inside its disk of convergence. -/
private lemma iteratedDeriv_regularizedHGFun_eq (a b : Multiset ℂ)
    (hr : 0 < (Complex.regularizedHGFunSeries a b).radius) (n : ℕ) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) (Complex.regularizedHGFunSeries a b).radius) :
    iteratedDeriv n (Complex.regularizedHGFun a b) z =
      pochhammerProduct a n *
          Complex.regularizedHGFun (shiftParameters a n) (shiftParameters b n) z := by
  have hs := (hasFPowerSeriesOnBall_iteratedDeriv_regularizedHGFun a b hr n).hasSum_mul_pow hz
  by_cases hP : pochhammerProduct a n = 0
  · simp only [hP, zero_mul] at hs ⊢
    exact hs.unique hasSum_zero
  · have hs' := hs.mul_left (pochhammerProduct a n)⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hP, one_mul] at hs'
    rw [regularizedHGFun_eq_tsum', hs'.tsum_eq]
    field_simp

/-- A terminating parameter multiset stays terminating after a shift by `n` unless the
rising factorial vanishes. -/
private lemma isTerminating_shiftParameters {a : Multiset ℂ} (ha : IsTerminating a) {n : ℕ}
    (hP : pochhammerProduct a n ≠ 0) : IsTerminating (shiftParameters a n) := by
  obtain ⟨x, hx, m, rfl⟩ := ha
  have hpx : pochhammer (-(m : ℂ)) n ≠ 0 := by
    intro h0
    apply hP
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨_, hx, h0⟩)
  have hnm : n ≤ m := by
    by_contra hlt
    exact hpx (pochhammer_neg_nat_eq_zero (Nat.lt_of_not_le hlt))
  refine ⟨-(m : ℂ) + n, Multiset.mem_map.mpr ⟨_, hx, rfl⟩, m - n, ?_⟩
  push_cast [hnm]
  ring

/-- Outside the nonterminating case `p = q + 1` the regularized principal function is the
native series. -/
private lemma regularizedGeneralizedHypergeometric_eq_series_of_domain {a b : Multiset ℂ}
    (h : a.card ≤ b.card ∨ IsTerminating a) :
    regularizedGeneralizedHypergeometric a b = Complex.regularizedHGFun a b := by
  rcases h with h | h
  · have hne : a.card ≠ b.card + 1 := by omega
    funext w
    unfold regularizedGeneralizedHypergeometric
    simp only [ite_eq_right hne]
  · exact funext (regularizedGeneralizedHypergeometric_eq_series_of_terminates h)

/-- Outside the nonterminating case `p = q + 1` the regularized series is entire. -/
private lemma radius_eq_top_of_domain {a b : Multiset ℂ}
    (h : a.card ≤ b.card ∨ IsTerminating a) :
    (Complex.regularizedHGFunSeries a b).radius = ⊤ := by
  rcases h with h | ⟨x, hx, m, hxm⟩
  · exact Complex.radius_regularizedHGFunSeries_eq_top h
  · exact Complex.radius_regularizedHGFunSeries_eq_top_of_finite hx hxm

/-- All derivatives of the regularized principal function, for all parameters; the
regularized form of DLMF 16.3.1. -/
theorem regularizedGeneralizedHypergeometric_iteratedDeriv {a b : Multiset ℂ}
    (h : a.card ≤ b.card + 1 ∨ IsTerminating a) (n : ℕ)
    {z : ℂ} (hz : z ∈ genAnalyticDomain a b) :
    iteratedDeriv n (regularizedGeneralizedHypergeometric a b) z =
      pochhammerProduct a n *
          regularizedGeneralizedHypergeometric (shiftParameters a n) (shiftParameters b n) z := by
  classical
  have hcs : (shiftParameters a n).card = a.card := Multiset.card_map _ _
  have hcb : (shiftParameters b n).card = b.card := Multiset.card_map _ _
  by_cases hD : a.card ≤ b.card ∨ IsTerminating a
  · rw [regularizedGeneralizedHypergeometric_eq_series_of_domain hD]
    have hr := radius_eq_top_of_domain (b := b) hD
    rw [iteratedDeriv_regularizedHGFun_eq a b (by rw [hr]; simp) n (by rw [hr]; simp)]
    by_cases hP : pochhammerProduct a n = 0
    · simp [hP]
    · congr 1
      refine (congrFun (regularizedGeneralizedHypergeometric_eq_series_of_domain ?_) z).symm
      rcases hD with hD | hD
      · left; omega
      · right; exact isTerminating_shiftParameters hD hP
  · have hc : a.card = b.card + 1 := by
      rcases h with h | h
      · omega
      · exact absurd (Or.inr h) hD
    have hzc : z ∈ cutPlane := by
      unfold genAnalyticDomain at hz
      rwa [ite_eq_right hD] at hz
    have hA := analyticOnNhd_regularizedGeneralizedHypergeometric hc
    have hA' := analyticOnNhd_regularizedGeneralizedHypergeometric (a := shiftParameters a n)
        (b := shiftParameters b n)
      (by omega)
    have hr : (1 : ENNReal) ≤ (Complex.regularizedHGFunSeries a b).radius :=
      Complex.radius_regularizedHGFunSeries_ge_one hc
    refine eqOn_cutPlane_of_eqOn_disk
        (f := iteratedDeriv n (regularizedGeneralizedHypergeometric a b))
      (g := fun z => pochhammerProduct a n *
          regularizedGeneralizedHypergeometric (shiftParameters a n) (shiftParameters b n) z)
      (by rw [iteratedDeriv_eq_iterate]; exact hA.iterated_deriv n)
      (analyticOnNhd_const.mul hA') (fun w hw => ?_) hzc
    have hev : regularizedGeneralizedHypergeometric a b =ᶠ[𝓝 w] Complex.regularizedHGFun a b := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw)] with v hv
      exact regularizedGeneralizedHypergeometric_eq_series (by simpa using hv)
    rw [(iteratedDeriv_eventuallyEq hev n).eq_of_nhds,
      iteratedDeriv_regularizedHGFun_eq a b (lt_of_lt_of_le one_pos hr) n
        (Metric.eball_subset_eball hr (mem_eball_one_of_norm_lt_one hw)),
      regularizedGeneralizedHypergeometric_eq_series hw]

/-- All derivatives of the ordinary principal function, including every terminating p,q. -/
@[dlmf 16.3.E1]
theorem generalizedHypergeometric_iteratedDeriv {a b : Multiset ℂ} (hb : LowerParametersRegular b)
    (h : a.card ≤ b.card + 1 ∨ IsTerminating a) (n : ℕ)
    {z : ℂ} (hz : z ∈ genAnalyticDomain a b) :
    iteratedDeriv n (generalizedHypergeometric a b) z = pochhammerProduct a n /
        pochhammerProduct b n *
      generalizedHypergeometric (shiftParameters a n) (shiftParameters b n) z := by
  have hgen : generalizedHypergeometric a b = fun z => gammaProduct b *
      regularizedGeneralizedHypergeometric a b z := rfl
  rw [hgen, iteratedDeriv_const_mul_field,
      regularizedGeneralizedHypergeometric_iteratedDeriv h n hz, generalizedHypergeometric]
  have hΓ : gammaProduct (shiftParameters b n) = pochhammerProduct b n * gammaProduct b := by
    rw [← gammaProduct_shift_nat hb n]
    simp [gammaProduct, shiftParameters, Multiset.map_map]
  rw [hΓ]
  have hP := pochhammerProduct_ne_zero hb n
  field_simp

/-- The analytic domain is open. -/
private lemma isOpen_genAnalyticDomain (a b : Multiset ℂ) : IsOpen (genAnalyticDomain a b) := by
  unfold genAnalyticDomain
  split_ifs
  · exact isOpen_univ
  · exact isOpen_cutPlane

/-- The regularized principal function is analytic on its analytic domain. -/
private lemma analyticOnNhd_regularizedGeneralizedHypergeometric_domain {a b : Multiset ℂ}
    (h : a.card ≤ b.card + 1 ∨ IsTerminating a) :
    AnalyticOnNhd ℂ (regularizedGeneralizedHypergeometric a b) (genAnalyticDomain a b) := by
  by_cases hD : a.card ≤ b.card ∨ IsTerminating a
  · rw [regularizedGeneralizedHypergeometric_eq_series_of_domain hD]
    have hr := radius_eq_top_of_domain (b := b) hD
    have hF := (Complex.regularizedHGFunSeries a b).hasFPowerSeriesOnBall (by rw [hr]; simp)
    rw [hr] at hF
    intro z _
    exact hF.analyticAt_of_mem (by simp)
  · have hc : a.card = b.card + 1 := by
      rcases h with h | h
      · omega
      · exact absurd (Or.inr h) hD
    unfold genAnalyticDomain
    simp only [hD, ↓reduceIte]
    exact analyticOnNhd_regularizedGeneralizedHypergeometric hc

/-- The regularized principal function is the series on the unit disk. -/
private lemma hasSum_regularizedGeneralizedHypergeometric_disk {a b : Multiset ℂ}
    (h : a.card ≤ b.card + 1 ∨ IsTerminating a) {z : ℂ} (hz : ‖z‖ < 1) :
    HasFPowerSeriesOnBall (Complex.regularizedHGFun a b)
      (FormalMultilinearSeries.ofScalars ℂ (Complex.regularizedHGFunCoeff a b)) 0
      (Complex.regularizedHGFunSeries a b).radius ∧
      z ∈ Metric.eball (0 : ℂ) (Complex.regularizedHGFunSeries a b).radius := by
  have hr : (1 : ENNReal) ≤ (Complex.regularizedHGFunSeries a b).radius := by
    by_cases hD : a.card ≤ b.card ∨ IsTerminating a
    · rw [radius_eq_top_of_domain hD]; exact le_top
    · exact Complex.radius_regularizedHGFunSeries_ge_one (by
        rcases h with h | h
        · omega
        · exact absurd (Or.inr h) hD)
  exact ⟨(Complex.regularizedHGFunSeries a b).hasFPowerSeriesOnBall
    (lt_of_lt_of_le one_pos hr), Metric.eball_subset_eball hr (mem_eball_one_of_norm_lt_one hz)⟩

/-- Two analytic functions on the analytic domain that agree on the unit disk agree. -/
private lemma eqOn_genAnalyticDomain {a b : Multiset ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (genAnalyticDomain a b))
    (hg : AnalyticOnNhd ℂ g (genAnalyticDomain a b))
    (h : ∀ z : ℂ, ‖z‖ < 1 → f z = g z) : EqOn f g (genAnalyticDomain a b) := by
  unfold genAnalyticDomain at hf hg ⊢
  split_ifs at hf hg ⊢
  · refine hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ 0) ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)] with w hw
    exact h w (by simpa using hw)
  · exact eqOn_cutPlane_of_eqOn_disk hf hg h

/-- The analytic domain depends only on the number of lower parameters. -/
private lemma genAnalyticDomain_cons_right (a b : Multiset ℂ) (c c' : ℂ) :
    genAnalyticDomain a (c ::ₘ b) = genAnalyticDomain a (c' ::ₘ b) := by
  unfold genAnalyticDomain
  split_ifs with h1 h2 h2 <;> simp only [Multiset.card_cons] at h1 h2 <;> first | rfl | tauto

/-- The coefficient form of the lower contiguous relation, for all parameters. -/
private lemma regularizedHGFunCoeff_lower_contiguous (a b : Multiset ℂ) (c : ℂ) (k : ℕ) :
    (c - 1 + k) * Complex.regularizedHGFunCoeff a (c ::ₘ b) k =
      Complex.regularizedHGFunCoeff a ((c - 1) ::ₘ b) k := by
  unfold Complex.regularizedHGFunCoeff
  simp only [Multiset.map_cons, Multiset.prod_cons]
  have hΓ : (Gamma (c - 1 + k))⁻¹ = (c - 1 + k) * (Gamma (c + k))⁻¹ := by
    have := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c - 1 + k)
    simpa [one_div, show c - 1 + k + 1 = c + k by ring] using this
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv, mul_inv, mul_inv, hΓ]
  ring

/-- The lower contiguous relation `(c-1) 𝐅 + z 𝐅' = 𝐅(c-1)` on the whole analytic domain. -/
private lemma regularizedGeneralizedHypergeometric_lower_contiguous {a b : Multiset ℂ} (c : ℂ)
    (h : a.card ≤ b.card + 2 ∨ IsTerminating a) {z : ℂ}
    (hz : z ∈ genAnalyticDomain a (c ::ₘ b)) :
    (c - 1) * regularizedGeneralizedHypergeometric a (c ::ₘ b) z + z *
        deriv (regularizedGeneralizedHypergeometric a (c ::ₘ b)) z =
      regularizedGeneralizedHypergeometric a ((c - 1) ::ₘ b) z := by
  have h1 : a.card ≤ (c ::ₘ b).card + 1 ∨ IsTerminating a := by
    simpa [Multiset.card_cons] using h
  have h2 : a.card ≤ ((c - 1) ::ₘ b).card + 1 ∨ IsTerminating a := by
    simpa [Multiset.card_cons] using h
  have hA := analyticOnNhd_regularizedGeneralizedHypergeometric_domain h1
  have hA' := analyticOnNhd_regularizedGeneralizedHypergeometric_domain h2
  rw [genAnalyticDomain_cons_right a b (c - 1) c] at hA'
  have hO := isOpen_genAnalyticDomain a (c ::ₘ b)
  refine eqOn_genAnalyticDomain
      (f := fun z => (c - 1) * regularizedGeneralizedHypergeometric a (c ::ₘ b) z +
      z * deriv (regularizedGeneralizedHypergeometric a (c ::ₘ b)) z)
          (g := regularizedGeneralizedHypergeometric a ((c - 1) ::ₘ b))
    ((analyticOnNhd_const.mul hA).add (analyticOnNhd_id.mul (hA.deriv))) hA' (fun w hw => ?_) hz
  obtain ⟨hF, hwF⟩ := hasSum_regularizedGeneralizedHypergeometric_disk h1 hw
  obtain ⟨hF', hwF'⟩ := hasSum_regularizedGeneralizedHypergeometric_disk h2 hw
  have hev : regularizedGeneralizedHypergeometric a (c ::ₘ b) =ᶠ[𝓝 w] Complex.regularizedHGFun a
      (c ::ₘ b) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw)] with v hv
    exact regularizedGeneralizedHypergeometric_eq_series (by simpa using hv)
  rw [hev.deriv_eq, regularizedGeneralizedHypergeometric_eq_series hw,
      regularizedGeneralizedHypergeometric_eq_series hw]
  have hd := (hF.deriv_ofScalars.hasSum_mul_pow hwF).mul_left w
  have hs := hF.hasSum_mul_pow hwF
  have hs' := hF'.hasSum_mul_pow hwF'
  have hshift : HasSum (fun n : ℕ => (n : ℂ) * Complex.regularizedHGFunCoeff a (c ::ₘ b) n * w ^ n)
      (w * deriv (Complex.regularizedHGFun a (c ::ₘ b)) w) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    refine hd.congr_fun fun n => ?_
    push_cast; ring
  refine ((hs.mul_left (c - 1)).add hshift).unique (hs'.congr_fun fun n => ?_)
  rw [← regularizedHGFunCoeff_lower_contiguous]
  ring

/-- `z^(c-2) z = z^(c-1)` away from the origin. -/
private lemma cpow_one_add_eq {z : ℂ} (hz0 : z ≠ 0) {c : ℂ} :
    z ^ (c - 1 - 1) * z = z ^ (c - 1) := by
  have := cpow_add (c - 1 - 1) 1 hz0
  rw [cpow_one, show c - 1 - 1 + 1 = c - 1 by ring] at this
  exact this.symm

/-- One lowering step: `(z^(c-1) 𝐅(a; c, b; z))' = z^(c-2) 𝐅(a; c-1, b; z)`. -/
private lemma hasDerivAt_cpow_mul_regularizedGeneralizedHypergeometric_lower
    {a b : Multiset ℂ} (c : ℂ)
    (h : a.card ≤ b.card + 2 ∨ IsTerminating a) {z : ℂ}
    (hz : z ∈ Complex.slitPlane ∩ genAnalyticDomain a (c ::ₘ b)) :
    HasDerivAt (fun w => w ^ (c - 1) * regularizedGeneralizedHypergeometric a (c ::ₘ b) w)
      (z ^ (c - 1 - 1) * regularizedGeneralizedHypergeometric a ((c - 1) ::ₘ b) z) z := by
  have h1 : a.card ≤ (c ::ₘ b).card + 1 ∨ IsTerminating a := by
    simpa [Multiset.card_cons] using h
  have hA := analyticOnNhd_regularizedGeneralizedHypergeometric_domain h1 z hz.2
  have hp : HasDerivAt (fun w : ℂ => w ^ (c - 1)) ((c - 1) * z ^ (c - 1 - 1)) z := by
    simpa using (hasDerivAt_id z).cpow_const (c := c - 1) hz.1
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz.1
  convert hp.mul hA.differentiableAt.hasDerivAt using 1
  rw [← regularizedGeneralizedHypergeometric_lower_contiguous c h hz.2,
    show z ^ (c - 1) = z ^ (c - 1 - 1) * z by
      rw [← cpow_one_add_eq hz0]]
  ring

/-- The regularized form of DLMF 16.3.4, for all parameters. -/
private lemma iteratedDeriv_cpow_mul_regularizedGeneralizedHypergeometric_lower {a b : Multiset ℂ}
    (h : a.card ≤ b.card + 2 ∨ IsTerminating a) (n : ℕ) :
    ∀ (c z : ℂ), z ∈ Complex.slitPlane ∩ genAnalyticDomain a (c ::ₘ b) →
      iteratedDeriv n (fun w => w ^ (c - 1) *
          regularizedGeneralizedHypergeometric a (c ::ₘ b) w) z =
        z ^ (c - n - 1) * regularizedGeneralizedHypergeometric a ((c - n) ::ₘ b) z := by
  induction n with
  | zero => intro c z _; simp
  | succ n ih =>
    intro c z hz
    have hU : IsOpen (Complex.slitPlane ∩ genAnalyticDomain a (c ::ₘ b)) :=
      Complex.isOpen_slitPlane.inter (isOpen_genAnalyticDomain _ _)
    have hev : deriv (fun w => w ^ (c - 1) *
        regularizedGeneralizedHypergeometric a (c ::ₘ b) w) =ᶠ[𝓝 z]
        fun w => w ^ (c - 1 - 1) * regularizedGeneralizedHypergeometric a ((c - 1) ::ₘ b) w := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact (hasDerivAt_cpow_mul_regularizedGeneralizedHypergeometric_lower c h hw).deriv
    rw [iteratedDeriv_succ', (iteratedDeriv_eventuallyEq hev n).eq_of_nhds,
      ih (c - 1) z (by rwa [genAnalyticDomain_cons_right a b (c - 1) c])]
    push_cast
    ring_nf

/-- `Γ(c) = (c-n)_n Γ(c-n)` when `c - n` is regular. -/
private lemma Gamma_eq_pochhammer_mul_Gamma_sub {c : ℂ} {n : ℕ} (hc : ∀ k : ℕ, c - n ≠ -k) :
    Gamma c = pochhammer (c - n) n * Gamma (c - n) := by
  have := Complex.Gamma_add_nat_div_Gamma_eq (n := n) (c - n) hc
  rw [sub_add_cancel] at this
  rw [pochhammer, ← this, div_mul_cancel₀ _ (Complex.Gamma_ne_zero hc)]

/-- Adding the same regular parameter above and below leaves the domain larger. -/
private lemma genAnalyticDomain_subset_cons (a b : Multiset ℂ) (c c' : ℂ) :
    genAnalyticDomain a b ⊆ genAnalyticDomain (c ::ₘ a) (c' ::ₘ b) := by
  unfold genAnalyticDomain
  split_ifs with h1 h2
  · exact subset_rfl
  · exfalso
    apply h2
    rcases h1 with h1 | ⟨x, hx, m, hm⟩
    · left; simpa using h1
    · right; exact ⟨x, Multiset.mem_cons_of_mem hx, m, hm⟩
  · exact subset_univ _
  · exact subset_rfl

/-- Cancelling a regular parameter that appears both above and below. -/
private lemma generalizedHypergeometric_cons_cancel {a b : Multiset ℂ} {c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k)
    (h : a.card ≤ b.card + 1 ∨ IsTerminating a) {z : ℂ} (hz : z ∈ genAnalyticDomain a b) :
    generalizedHypergeometric (c ::ₘ a) (c ::ₘ b) z = generalizedHypergeometric a b z := by
  have h' : (c ::ₘ a).card ≤ (c ::ₘ b).card + 1 ∨ IsTerminating (c ::ₘ a) := by
    rcases h with h | ⟨x, hx, m, hm⟩
    · left; simpa using h
    · right; exact ⟨x, Multiset.mem_cons_of_mem hx, m, hm⟩
  have hA := (analyticOnNhd_regularizedGeneralizedHypergeometric_domain h').mono
    (genAnalyticDomain_subset_cons a b c c)
  have hA' := analyticOnNhd_regularizedGeneralizedHypergeometric_domain h
  have hE : EqOn (regularizedGeneralizedHypergeometric (c ::ₘ a) (c ::ₘ b))
      (fun w => (Gamma c)⁻¹ * regularizedGeneralizedHypergeometric a b w)
          (genAnalyticDomain a b) := by
    refine eqOn_genAnalyticDomain hA (analyticOnNhd_const.mul hA') fun w hw => ?_
    rw [regularizedGeneralizedHypergeometric_eq_series hw,
        regularizedGeneralizedHypergeometric_eq_series hw,
      regularizedHGFun_eq_tsum', regularizedHGFun_eq_tsum', ← tsum_mul_left]
    congr 1
    funext k
    rw [regularizedHGFunCoeff_cons, pochhammer, ← Complex.Gamma_add_nat_div_Gamma_eq c hc]
    have := Complex.Gamma_ne_zero hc
    have h2 : Gamma (c + k) ≠ 0 :=
      Complex.Gamma_ne_zero fun m hm => hc (m + k) (by push_cast; linear_combination hm)
    field_simp
  simp only [generalizedHypergeometric, gammaProduct, Multiset.map_cons, Multiset.prod_cons]
  rw [hE hz]
  have := Complex.Gamma_ne_zero hc
  field_simp

/-- Raising a nonzero numerator parameter by one does not shrink the analytic domain. -/
private lemma genAnalyticDomain_cons_succ_left {δ : ℂ} (hδ : δ ≠ 0) (a b : Multiset ℂ) :
    genAnalyticDomain (δ ::ₘ a) b ⊆ genAnalyticDomain ((δ + 1) ::ₘ a) b := by
  unfold genAnalyticDomain
  split_ifs with h1 h2
  · exact subset_rfl
  · exfalso
    apply h2
    rcases h1 with h1 | ⟨x, hx, m, hm⟩
    · left; simpa using h1
    · right
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
          rcases m with _ | m'
          · exact absurd (by simpa using hm) hδ
          · exact ⟨m', rfl⟩
        exact ⟨x + 1, Multiset.mem_cons_self _ _, m', by rw [hm]; push_cast; ring⟩
      · exact ⟨x, Multiset.mem_cons_of_mem hx, m, hm⟩
  · exact subset_univ _
  · exact subset_rfl

/-- With a zero numerator parameter the regularized function is constant. -/
private lemma regularizedGeneralizedHypergeometric_zero_cons (a b : Multiset ℂ) :
    regularizedGeneralizedHypergeometric (0 ::ₘ a) b = fun _ =>
        Complex.regularizedHGFunCoeff (0 ::ₘ a) b 0 := by
  rw [regularizedGeneralizedHypergeometric_eq_series_of_domain
      (Or.inr ⟨0, Multiset.mem_cons_self _ _, 0, by simp⟩)]
  funext z
  rw [regularizedHGFun_eq_tsum', tsum_eq_single 0 fun k hk => ?_]
  · simp
  · simp [regularizedHGFunCoeff_cons_left, pochhammer, hk]

/-- The numerator contiguous relation `δ 𝐅 + z 𝐅' = δ 𝐅(δ+1)` on the analytic domain. -/
private lemma regularizedGeneralizedHypergeometric_numerator_contiguous {a b : Multiset ℂ} (δ : ℂ)
    (h : a.card ≤ b.card ∨ IsTerminating (δ ::ₘ a)) {z : ℂ}
    (hz : z ∈ genAnalyticDomain (δ ::ₘ a) b) :
    δ * regularizedGeneralizedHypergeometric (δ ::ₘ a) b z + z *
        deriv (regularizedGeneralizedHypergeometric (δ ::ₘ a) b) z =
      δ * regularizedGeneralizedHypergeometric ((δ + 1) ::ₘ a) b z := by
  by_cases hδ : δ = 0
  · subst hδ
    rw [regularizedGeneralizedHypergeometric_zero_cons]
    simp
  have h1 : (δ ::ₘ a).card ≤ b.card + 1 ∨ IsTerminating (δ ::ₘ a) := by
    rcases h with h | h
    · left; simpa using h
    · exact Or.inr h
  have h2 : ((δ + 1) ::ₘ a).card ≤ b.card + 1 ∨ IsTerminating ((δ + 1) ::ₘ a) := by
    rcases h with h | ⟨x, hx, m, hm⟩
    · left; simpa using h
    · right
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
          rcases m with _ | m'
          · exact absurd (by simpa using hm) hδ
          · exact ⟨m', rfl⟩
        exact ⟨x + 1, Multiset.mem_cons_self _ _, m', by rw [hm]; push_cast; ring⟩
      · exact ⟨x, Multiset.mem_cons_of_mem hx, m, hm⟩
  have hA := analyticOnNhd_regularizedGeneralizedHypergeometric_domain h1
  have hA' := (analyticOnNhd_regularizedGeneralizedHypergeometric_domain h2).mono
    (genAnalyticDomain_cons_succ_left hδ a b)
  refine eqOn_genAnalyticDomain
      (f := fun z => δ * regularizedGeneralizedHypergeometric (δ ::ₘ a) b z +
      z * deriv (regularizedGeneralizedHypergeometric (δ ::ₘ a) b) z)
    (g := fun z => δ * regularizedGeneralizedHypergeometric ((δ + 1) ::ₘ a) b z)
    ((analyticOnNhd_const.mul hA).add (analyticOnNhd_id.mul (hA.deriv)))
    (analyticOnNhd_const.mul hA') (fun w hw => ?_) hz
  obtain ⟨hF, hwF⟩ := hasSum_regularizedGeneralizedHypergeometric_disk h1 hw
  obtain ⟨hF', hwF'⟩ := hasSum_regularizedGeneralizedHypergeometric_disk h2 hw
  have hev : regularizedGeneralizedHypergeometric (δ ::ₘ a) b =ᶠ[𝓝 w] Complex.regularizedHGFun
      (δ ::ₘ a) b := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw)] with v hv
    exact regularizedGeneralizedHypergeometric_eq_series (by simpa using hv)
  rw [hev.deriv_eq, regularizedGeneralizedHypergeometric_eq_series hw,
      regularizedGeneralizedHypergeometric_eq_series hw]
  have hc := regularizedHGFun_contiguous δ a b hwF hwF'
  linear_combination hc

/-- Raising a nonzero numerator parameter keeps a terminating series terminating. -/
private lemma isTerminating_cons_succ {δ : ℂ} (hδ : δ ≠ 0) {a : Multiset ℂ}
    (h : IsTerminating (δ ::ₘ a)) : IsTerminating ((δ + 1) ::ₘ a) := by
  obtain ⟨x, hx, m, hm⟩ := h
  rcases Multiset.mem_cons.mp hx with rfl | hx
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
      rcases m with _ | m'
      · exact absurd (by simpa using hm) hδ
      · exact ⟨m', rfl⟩
    exact ⟨x + 1, Multiset.mem_cons_self _ _, m', by rw [hm]; push_cast; ring⟩
  · exact ⟨x, Multiset.mem_cons_of_mem hx, m, hm⟩

/-- `mulDerivMul` depends only on the germ. -/
private lemma mulDerivMul_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    mulDerivMul f z = mulDerivMul g z := by
  rw [mulDerivMul_eq_mul, mulDerivMul_eq_mul]
  congr 1
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [h] with w hw
  rw [hw]

/-- `mulDerivMul` commutes with constant factors. -/
private lemma mulDerivMul_const_mul (c : ℂ) (f : ℂ → ℂ) :
    mulDerivMul (fun w => c * f w) = fun w => c * mulDerivMul f w := by
  funext z
  rw [mulDerivMul_eq_mul, mulDerivMul_eq_mul,
    show (fun w => w * (c * f w)) = fun w => c * (w * f w) by funext w; ring,
    deriv_const_mul_field']
  ring

/-- Iterates of `mulDerivMul` commute with constant factors. -/
private lemma mulDerivMul_iterate_const_mul (c : ℂ) (n : ℕ) :
    ∀ f : ℂ → ℂ, mulDerivMul^[n] (fun w => c * f w) = fun w => c * mulDerivMul^[n] f w := by
  induction n with
  | zero => intro f; rfl
  | succ n ih =>
    intro f
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, mulDerivMul_const_mul, ih]

/-- One raising step: `z (z · z^(δ-1) 𝐅(δ, a; b; z))' = δ z^δ 𝐅(δ+1, a; b; z)`. -/
private lemma mulDerivMul_cpow_mul_regularizedGeneralizedHypergeometric {a b : Multiset ℂ} (δ : ℂ)
    (h : a.card ≤ b.card ∨ IsTerminating (δ ::ₘ a)) {z : ℂ}
    (hz : z ∈ Complex.slitPlane ∩ genAnalyticDomain (δ ::ₘ a) b) :
    mulDerivMul (fun w => w ^ (δ - 1) * regularizedGeneralizedHypergeometric (δ ::ₘ a) b w) z =
      δ * z ^ δ * regularizedGeneralizedHypergeometric ((δ + 1) ::ₘ a) b z := by
  have h1 : (δ ::ₘ a).card ≤ b.card + 1 ∨ IsTerminating (δ ::ₘ a) := by
    rcases h with h | h
    · left; simpa using h
    · exact Or.inr h
  have hA := analyticOnNhd_regularizedGeneralizedHypergeometric_domain h1 z hz.2
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz.1
  have hev : (fun w => w *
      (w ^ (δ - 1) * regularizedGeneralizedHypergeometric (δ ::ₘ a) b w)) =ᶠ[𝓝 z]
      fun w => w ^ δ * regularizedGeneralizedHypergeometric (δ ::ₘ a) b w := by
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz.1] with w hw
    have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
    have := cpow_one_add_eq hw0 (c := δ + 1)
    rw [show δ + 1 - 1 - 1 = δ - 1 by ring, show δ + 1 - 1 = δ by ring] at this
    rw [← this]
    ring
  have hp : HasDerivAt (fun w : ℂ => w ^ δ) (δ * z ^ (δ - 1)) z := by
    simpa using (hasDerivAt_id z).cpow_const (c := δ) hz.1
  rw [mulDerivMul_eq_mul, hev.deriv_eq, (hp.fun_mul hA.differentiableAt.hasDerivAt).deriv]
  have hc := regularizedGeneralizedHypergeometric_numerator_contiguous δ h hz.2
  have hzp : z * z ^ (δ - 1) = z ^ δ := by
    have := cpow_one_add_eq hz0 (c := δ + 1)
    rw [show δ + 1 - 1 - 1 = δ - 1 by ring, show δ + 1 - 1 = δ by ring] at this
    rw [← this]
    ring
  linear_combination z ^ δ * hc + δ * regularizedGeneralizedHypergeometric (δ ::ₘ a) b z * hzp

/-- Raising a parameter `n` times keeps the domain and the hypotheses while `(γ)_n ≠ 0`. -/
private lemma genAnalyticDomain_cons_add_left {γ : ℂ} {a b : Multiset ℂ} (n : ℕ)
    (hp : pochhammer γ n ≠ 0) :
    genAnalyticDomain (γ ::ₘ a) b ⊆ genAnalyticDomain ((γ + n) ::ₘ a) b ∧
      (IsTerminating (γ ::ₘ a) → IsTerminating ((γ + n) ::ₘ a)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pochhammer_succ] at hp
    have hδ : γ + n ≠ 0 := right_ne_zero_of_mul hp
    obtain ⟨ih1, ih2⟩ := ih (left_ne_zero_of_mul hp)
    push_cast
    rw [← add_assoc]
    exact ⟨ih1.trans (genAnalyticDomain_cons_succ_left hδ a b),
      fun ht => isTerminating_cons_succ hδ (ih2 ht)⟩

/-- The regularized form of DLMF 16.3.3, for all parameters. -/
private lemma mulDerivMul_iterate_regularizedGeneralizedHypergeometric {a b : Multiset ℂ} (γ : ℂ)
    (h : a.card ≤ b.card ∨ IsTerminating (γ ::ₘ a)) (n : ℕ) :
    ∀ z ∈ Complex.slitPlane ∩ genAnalyticDomain (γ ::ₘ a) b,
      (mulDerivMul^[n]) (fun w => w ^ (γ - 1) *
          regularizedGeneralizedHypergeometric (γ ::ₘ a) b w) z =
        pochhammer γ n * z ^ (γ + n - 1) *
            regularizedGeneralizedHypergeometric ((γ + n) ::ₘ a) b z := by
  induction n with
  | zero => intro z _; simp [pochhammer]
  | succ n ih =>
    intro z hz
    have hU : IsOpen (Complex.slitPlane ∩ genAnalyticDomain (γ ::ₘ a) b) :=
      Complex.isOpen_slitPlane.inter (isOpen_genAnalyticDomain _ _)
    have hev : (mulDerivMul^[n])
        (fun w => w ^ (γ - 1) * regularizedGeneralizedHypergeometric (γ ::ₘ a) b w)
        =ᶠ[𝓝 z] fun w => pochhammer γ n *
          (w ^ (γ + n - 1) * regularizedGeneralizedHypergeometric ((γ + n) ::ₘ a) b w) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      rw [ih w hw]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul_congr hev, mulDerivMul_const_mul]
    by_cases hp : pochhammer γ n = 0
    · simp [pochhammer_succ, hp]
    obtain ⟨hD, hT⟩ := genAnalyticDomain_cons_add_left (b := b) n hp
    have h' : a.card ≤ b.card ∨ IsTerminating ((γ + n) ::ₘ a) := h.imp id hT
    simp only
    rw [mulDerivMul_cpow_mul_regularizedGeneralizedHypergeometric (γ + n) h' ⟨hz.1, hD hz.2⟩,
        pochhammer_succ]
    push_cast
    ring_nf

/-- DLMF 16.3.4 with fewer hypotheses: stronger than DLMF, which also assumes that `b` and `γ`
are regular. -/
@[dlmf 16.3.E4]
theorem generalizedHypergeometric_lower_weighted_iteratedDeriv' (a b : Multiset ℂ) (γ : ℂ) (n : ℕ)
    (hγ : LowerParametersRegular {γ - n})
    (h : a.card ≤ b.card + 2 ∨ IsTerminating a)
    {z : ℂ} (hz : z ∈ Complex.slitPlane ∩ genAnalyticDomain a (γ ::ₘ b)) :
    iteratedDeriv n (fun z => z ^ (γ - 1) * generalizedHypergeometric a (γ ::ₘ b) z) z =
      pochhammer (γ - n) n * z ^ (γ - n - 1) * generalizedHypergeometric a ((γ - n) ::ₘ b) z := by
  have hfun : (fun z => z ^ (γ - 1) * generalizedHypergeometric a (γ ::ₘ b) z) = fun z =>
      (Gamma γ * gammaProduct b) *
          (z ^ (γ - 1) * regularizedGeneralizedHypergeometric a (γ ::ₘ b) z) := by
    funext w
    simp only [generalizedHypergeometric, gammaProduct, Multiset.map_cons, Multiset.prod_cons]
    ring
  rw [hfun, iteratedDeriv_const_mul_field,
    iteratedDeriv_cpow_mul_regularizedGeneralizedHypergeometric_lower h n γ z hz,
    Gamma_eq_pochhammer_mul_Gamma_sub (hγ (γ - n) (by simp))]
  simp only [generalizedHypergeometric, gammaProduct, Multiset.map_cons, Multiset.prod_cons]
  ring

/-- DLMF 16.3.2 with fewer hypotheses: stronger than DLMF, which also assumes that `b` is
regular. -/
@[dlmf 16.3.E2]
theorem generalizedHypergeometric_weighted_iteratedDeriv' (a b : Multiset ℂ) (γ : ℂ) (n : ℕ)
    (hγ : LowerParametersRegular {(γ + 1 - n)})
    (h : a.card ≤ b.card + 1 ∨ IsTerminating a)
    {z : ℂ} (hz : z ∈ Complex.slitPlane ∩ genAnalyticDomain a b) :
    iteratedDeriv n (fun z => z ^ γ * generalizedHypergeometric a b z) z =
      pochhammer (γ - n + 1) n * z ^ (γ - n) *
        generalizedHypergeometric ((γ + 1) ::ₘ a) ((γ + 1 - n) ::ₘ b) z := by
  have hreg : ∀ k : ℕ, γ + 1 - n ≠ -k := hγ _ (by simp)
  have hc : ∀ k : ℕ, γ + 1 ≠ -k := fun k hk =>
    hreg (k + n) (by rw [hk]; push_cast; ring)
  have hU : IsOpen (Complex.slitPlane ∩ genAnalyticDomain a b) :=
    Complex.isOpen_slitPlane.inter (isOpen_genAnalyticDomain _ _)
  have hev : (fun z => z ^ γ * generalizedHypergeometric a b z) =ᶠ[𝓝 z]
      fun z => z ^ (γ + 1 - 1) * generalizedHypergeometric ((γ + 1) ::ₘ a) ((γ + 1) ::ₘ b) z := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [generalizedHypergeometric_cons_cancel hc h hw.2, add_sub_cancel_right]
  have h' : ((γ + 1) ::ₘ a).card ≤ b.card + 2 ∨ IsTerminating ((γ + 1) ::ₘ a) := by
    rcases h with h | ⟨x, hx, m, hm⟩
    · left; simp only [Multiset.card_cons]; omega
    · right; exact ⟨x, Multiset.mem_cons_of_mem hx, m, hm⟩
  rw [(iteratedDeriv_eventuallyEq hev n).eq_of_nhds,
    generalizedHypergeometric_lower_weighted_iteratedDeriv' _ b (γ + 1) n hγ h'
      ⟨hz.1, genAnalyticDomain_subset_cons a b _ _ hz.2⟩]
  ring_nf

/-- DLMF 16.3.3 with fewer hypotheses: stronger than DLMF, which also assumes that `b` is
regular. -/
@[dlmf 16.3.E3]
theorem generalizedHypergeometric_raising_iterate' (a b : Multiset ℂ) (γ : ℂ) (n : ℕ)
    (h : a.card + 1 ≤ b.card + 1 ∨ IsTerminating (γ ::ₘ a))
    {z : ℂ} (hz : z ∈ Complex.slitPlane ∩ genAnalyticDomain (γ ::ₘ a) b) :
    (mulDerivMul^[n]) (fun z => z ^ (γ - 1) * generalizedHypergeometric (γ ::ₘ a) b z) z =
      pochhammer γ n * z ^ (γ + n - 1) * generalizedHypergeometric ((γ + n) ::ₘ a) b z := by
  have hfun : (fun z => z ^ (γ - 1) * generalizedHypergeometric (γ ::ₘ a) b z) = fun z =>
      gammaProduct b * (z ^ (γ - 1) * regularizedGeneralizedHypergeometric (γ ::ₘ a) b z) := by
    funext w
    simp only [generalizedHypergeometric]
    ring
  rw [hfun, mulDerivMul_iterate_const_mul]
  dsimp only
  rw [mulDerivMul_iterate_regularizedGeneralizedHypergeometric γ
      (h.imp (fun h => by omega) id) n z hz]
  simp only [generalizedHypergeometric]
  ring

/-- All weighted power derivatives with every displayed lower parameter regular. -/
@[dlmf 16.3.E2]
theorem generalizedHypergeometric_weighted_iteratedDeriv (a b : Multiset ℂ)
    (_hb : LowerParametersRegular b) (γ : ℂ) (n : ℕ)
    (hγ : LowerParametersRegular {(γ + 1 - n)})
    (h : a.card ≤ b.card + 1 ∨ IsTerminating a)
    {z : ℂ} (hz : z ∈ Complex.slitPlane ∩ genAnalyticDomain a b) :
    iteratedDeriv n (fun z => z ^ γ * generalizedHypergeometric a b z) z =
      pochhammer (γ - n + 1) n * z ^ (γ - n) *
        generalizedHypergeometric ((γ + 1) ::ₘ a) ((γ + 1 - n) ::ₘ b) z :=
  generalizedHypergeometric_weighted_iteratedDeriv' a b γ n hγ h hz

/-- The iterated zDz identity, with all complex parameters and integer orders. -/
@[dlmf 16.3.E3]
theorem generalizedHypergeometric_raising_iterate (a b : Multiset ℂ)
    (_hb : LowerParametersRegular b) (γ : ℂ) (n : ℕ)
    (h : a.card + 1 ≤ b.card + 1 ∨ IsTerminating (γ ::ₘ a))
    {z : ℂ} (hz : z ∈ Complex.slitPlane ∩ genAnalyticDomain (γ ::ₘ a) b) :
    (mulDerivMul^[n]) (fun z => z ^ (γ - 1) * generalizedHypergeometric (γ ::ₘ a) b z) z =
      pochhammer γ n * z ^ (γ + n - 1) * generalizedHypergeometric ((γ + n) ::ₘ a) b z :=
  generalizedHypergeometric_raising_iterate' a b γ n h hz

/-- Weighted derivatives lowering one lower parameter by every natural order. -/
@[dlmf 16.3.E4]
theorem generalizedHypergeometric_lower_weighted_iteratedDeriv (a b : Multiset ℂ)
    (_hb : LowerParametersRegular b) (γ : ℂ)
    (n : ℕ)
    (hγ : LowerParametersRegular {γ, γ - n})
    (h : a.card ≤ b.card + 2 ∨ IsTerminating a)
    {z : ℂ} (hz : z ∈ Complex.slitPlane ∩ genAnalyticDomain a (γ ::ₘ b)) :
    iteratedDeriv n (fun z => z ^ (γ - 1) * generalizedHypergeometric a (γ ::ₘ b) z) z =
      pochhammer (γ - n) n * z ^ (γ - n - 1) * generalizedHypergeometric a ((γ - n) ::ₘ b) z :=
  generalizedHypergeometric_lower_weighted_iteratedDeriv' a b γ n
    (fun x hx => hγ x (by simp only [Multiset.mem_singleton] at hx; simp [hx])) h hz

/-- Leibniz' rule for an analytic function times the identity, keeping just
the two nonzero derivatives of the identity function. -/
theorem genIteratedDeriv_id_mul (f : ℂ → ℂ) (n : ℕ) {z : ℂ} (hf : AnalyticAt ℂ f z) :
    iteratedDeriv (n + 1) (fun w => w * f w) z =
      z * iteratedDeriv (n + 1) f z + (n + 1) * iteratedDeriv n f z := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf.contDiffAt]
  let F : ℕ → ℂ := fun i => (n + 1).choose i *
    iteratedDeriv i (fun w : ℂ => w) z * iteratedDeriv (n + 1 - i) f z
  have hsub : ({0, 1} : Finset ℕ) ⊆ range (n + 1 + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp
  have hs : (∑ i ∈ ({0, 1} : Finset ℕ), F i) = ∑ i ∈ range (n + 1 + 1), F i := by
    apply Finset.sum_subset hsub
    intro i hi hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    simp [F, iteratedDeriv_fun_id, hnot.1, hnot.2]
  change (∑ i ∈ range (n + 1 + 1), F i) = _
  rw [← hs]
  simp [F, iteratedDeriv_fun_id]

/-- The general operator identity for every analytic germ and every natural order. -/
@[dlmf 16.3.E5]
theorem genRaiseOp_iterate (f : ℂ → ℂ) (n : ℕ) {z : ℂ} (hf : AnalyticAt ℂ f z) :
    (mulDerivMul^[n]) f z = z ^ n * iteratedDeriv n (fun z => z ^ n * f z) z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have heq : (fun w => w * (mulDerivMul^[n]) f w) =ᶠ[𝓝 z]
        (fun w => w ^ (n + 1) * iteratedDeriv n (fun w => w ^ n * f w) w) := by
      filter_upwards [hf.eventually_analyticAt] with w hw
      rw [ih hw]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul_eq_mul, heq.deriv_eq]
    have hg : AnalyticAt ℂ (fun w => w ^ n * f w) z := by fun_prop
    have hD : HasDerivAt (iteratedDeriv n (fun w => w ^ n * f w))
        (iteratedDeriv (n + 1) (fun w => w ^ n * f w) z) z := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_eq_iterate] using
        (hg.iterated_deriv n).differentiableAt.hasDerivAt
    have hder : deriv (fun w => w ^ (n + 1) * iteratedDeriv n (fun w => w ^ n * f w) w) z =
        (n + 1) * z ^ n * iteratedDeriv n (fun w => w ^ n * f w) z +
          z ^ (n + 1) * iteratedDeriv (n + 1) (fun w => w ^ n * f w) z := by
      simpa only [id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one] using
        (((hasDerivAt_id z).fun_pow (n + 1)).fun_mul hD).deriv
    rw [hder]
    have hid := genIteratedDeriv_id_mul (fun w => w ^ n * f w) n hg
    have hfun : (fun w => w ^ (n + 1) * f w) = (fun w => w * (w ^ n * f w)) := by
      funext w
      ring
    rw [hfun, hid]
    simp only [pow_succ]
    ring

/-- Any q+2 contiguous functions are linearly dependent over rational functions. -/
theorem genContiguous_linear_relation {p q : ℕ} (hpq : p ≤ q + 1)
    (a : Fin (q + 2) → Fin p → ℂ) (b : Fin (q + 2) → Fin q → ℂ)
    (hb : ∀ i, LowerParametersRegular (parametersOfFin (b i)))
    (hc : ∀ i, GenContiguous (a 0) (a i) (b 0) (b i)) :
    ∃ P : Fin (q + 2) → Polynomial ℂ, (∃ i, P i ≠ 0) ∧
      ∀ z ∈ cutPlane, ∑ i, (P i).eval z *
          generalizedHypergeometric (parametersOfFin (a i)) (parametersOfFin (b i)) z = 0 := by
  sorry

/-- The three contiguous ordinary 0F1 functions, with all three lower parameters regular. -/
@[dlmf 16.3.E6]
theorem generalizedHypergeometric_0F1_contiguous (b z : ℂ)
    (hb : LowerParametersRegular {b - 1, b, b + 1}) :
    z * generalizedHypergeometric ∅ {b + 1} z + b * (b - 1) * generalizedHypergeometric ∅ {b} z -
      b * (b - 1) * generalizedHypergeometric ∅ {b - 1} z = 0 := by
  have hb₀ : b ≠ 0 := by simpa using hb b (by simp) 0
  have hb₁ : b - 1 ≠ 0 := by simpa using hb (b - 1) (by simp) 0
  have hΓ₀ := Complex.Gamma_add_one b hb₀
  have hΓ₁ := Complex.Gamma_add_one (b - 1) hb₁
  have hcont := Complex.regularizedHGFun_zero_singleton_eq_mul_add_mul (b - 1) z
  rw [show b - 1 + 1 = b by ring, show b - 1 + 2 = b + 1 by ring] at hcont
  rw [show b - 1 + 1 = b by ring] at hΓ₁
  simp [generalizedHypergeometric, regularizedGeneralizedHypergeometric, gammaProduct,
      Multiset.empty_eq_zero]
  rw [hΓ₀, hΓ₁, hcont]
  ring

/-- The coefficient identity behind the four-term contiguous `₃F₂` relation. -/
private lemma gen3F2_contiguous_coeff (a₁ a₂ a₃ b₁ b₂ : ℂ) (hb : LowerParametersRegular {b₁, b₂})
    (n : ℕ) :
    let c := fun (x : ℂ) (m : ℕ) => generalizedHypergeometricCoeff {x, a₂, a₃} {b₁, b₂} m
    (a₁ * (a₁ + 1) * c (a₁ + 2) (n + 1) + a₁ * (b₁ + b₂ - 3 * a₁ - 2) * c (a₁ + 1) (n + 1) +
      ((2 * a₁ - b₁) * (2 * a₁ - b₂) + a₁ - a₁ ^ 2) * c a₁ (n + 1) -
      (a₁ - b₁) * (a₁ - b₂) * c (a₁ - 1) (n + 1)) +
    (-(a₁ * (a₁ + 1)) * c (a₁ + 2) n + a₁ * (2 * a₁ - a₂ - a₃ + 1) * c (a₁ + 1) n -
      (a₁ - a₂) * (a₁ - a₃) * c a₁ n) = 0 := by
  intro c
  have hb₁ : b₁ + n ≠ 0 := fun h => hb b₁ (by simp) n (by linear_combination h)
  have hb₂ : b₂ + n ≠ 0 := fun h => hb b₂ (by simp) n (by linear_combination h)
  have hp₁ : pochhammer b₁ n ≠ 0 := pochhammer_ne_zero_of_not_neg_nat (hb b₁ (by simp)) n
  have hp₂ : pochhammer b₂ n ≠ 0 := pochhammer_ne_zero_of_not_neg_nat (hb b₂ (by simp)) n
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  set N := pochhammer a₂ n * pochhammer a₃ n with hN
  set D := pochhammer b₁ n * pochhammer b₂ n * (n.factorial : ℂ) with hD
  set E := (b₁ + n) * (b₂ + n) * ((n : ℂ) + 1) with hE
  set W := (a₂ + n) * (a₃ + n) with hW
  have hDE : D * E ≠ 0 := by
    simp only [hD, hE]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hp₁ hp₂) hf) (mul_ne_zero (mul_ne_zero hb₁ hb₂) hn1)
  have hc0 : ∀ x : ℂ, c x n = pochhammer x n * E * (N / (D * E)) := by
    intro x
    simp only [c, generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
        Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
    rw [hN, hD, hE]
    field_simp
  have hc1 : ∀ x : ℂ, c x (n + 1) = pochhammer x n * (x + n) * W * (N / (D * E)) := by
    intro x
    simp only [c, generalizedHypergeometricCoeff, pochhammerProduct, Multiset.insert_eq_cons,
        Multiset.map_cons,
      Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, pochhammer_succ,
      Nat.factorial_succ]
    push_cast
    rw [hN, hD, hE, hW]
    field_simp
  rw [hc1, hc1, hc1, hc1, hc0, hc0, hc0]
  have e0 : a₁ * pochhammer (a₁ + 1) n = (a₁ + n) * pochhammer a₁ n := pochhammer_succ_left_mul a₁ n
  have e1 : (a₁ + 1) * pochhammer (a₁ + 2) n = (a₁ + 1 + n) * pochhammer (a₁ + 1) n := by
    have := pochhammer_succ_left_mul (a₁ + 1) n
    rwa [show a₁ + 1 + 1 = a₁ + 2 by ring] at this
  have em : (a₁ - 1) * pochhammer a₁ n = (a₁ - 1 + n) * pochhammer (a₁ - 1) n := by
    have := pochhammer_succ_left_mul (a₁ - 1) n
    rwa [show a₁ - 1 + 1 = a₁ by ring] at this
  have e2 : a₁ * (a₁ + 1) * pochhammer (a₁ + 2) n = (a₁ + n) * (a₁ + 1 + n) * pochhammer a₁ n := by
    rw [mul_assoc, e1, mul_left_comm, e0]; ring
  linear_combination (N / (D * E)) * (((a₁ + 2 + n) * W - E) * e2 +
    ((b₁ + b₂ - 3 * a₁ - 2) * (a₁ + 1 + n) * W + (2 * a₁ - a₂ - a₃ + 1) * E) * e0 +
    ((a₁ - b₁) * (a₁ - b₂) * W) * em)

/-- The full four-term contiguous 3F2 identity. -/
@[dlmf 16.3.E7]
theorem generalizedHypergeometric_3F2_contiguous (a₁ a₂ a₃ b₁ b₂ : ℂ)
    (hb : LowerParametersRegular {b₁, b₂})
    {z : ℂ} (hz : z ∈ cutPlane) :
    generalizedHypergeometric {a₁ + 2, a₂, a₃} {b₁, b₂} z * a₁ * (a₁ + 1) * (1 - z) +
    generalizedHypergeometric {a₁ + 1, a₂, a₃} {b₁, b₂} z * a₁ *
      (b₁ + b₂ - 3 * a₁ - 2 + z * (2 * a₁ - a₂ - a₃ + 1)) +
    generalizedHypergeometric {a₁, a₂, a₃} {b₁, b₂} z *
      ((2 * a₁ - b₁) * (2 * a₁ - b₂) + a₁ - a₁ ^ 2 - z * (a₁ - a₂) * (a₁ - a₃)) -
    generalizedHypergeometric {a₁ - 1, a₂, a₃} {b₁, b₂} z * (a₁ - b₁) * (a₁ - b₂) = 0 := by
  have hA : ∀ x : ℂ, AnalyticOnNhd ℂ (generalizedHypergeometric {x, a₂, a₃} {b₁, b₂})
      cutPlane := fun x =>
    analyticOnNhd_const.mul (analyticOnNhd_regularizedGeneralizedHypergeometric (by simp))
  refine eqOn_cutPlane_of_eqOn_disk (g := fun _ => (0 : ℂ))
    (f := fun z => generalizedHypergeometric {a₁ + 2, a₂, a₃} {b₁, b₂} z * a₁ * (a₁ + 1) * (1 - z) +
      generalizedHypergeometric {a₁ + 1, a₂, a₃} {b₁, b₂} z * a₁ *
        (b₁ + b₂ - 3 * a₁ - 2 + z * (2 * a₁ - a₂ - a₃ + 1)) +
      generalizedHypergeometric {a₁, a₂, a₃} {b₁, b₂} z *
        ((2 * a₁ - b₁) * (2 * a₁ - b₂) + a₁ - a₁ ^ 2 - z * (a₁ - a₂) * (a₁ - a₃)) -
      generalizedHypergeometric {a₁ - 1, a₂, a₃} {b₁, b₂} z * (a₁ - b₁) * (a₁ - b₂))
    (by
      intro z hz
      have h₁ := hA (a₁ + 2) z hz
      have h₂ := hA (a₁ + 1) z hz
      have h₃ := hA a₁ z hz
      have h₄ := hA (a₁ - 1) z hz
      fun_prop)
    analyticOnNhd_const (fun w hw => ?_) hz
  set c := fun (x : ℂ) (m : ℕ) => generalizedHypergeometricCoeff {x, a₂, a₃} {b₁, b₂} m with hc
  have hs : ∀ x : ℂ, HasSum (fun n => c x n * w ^ n)
      (generalizedHypergeometric {x, a₂, a₃} {b₁, b₂} w) :=
    fun x => generalizedHypergeometric_hasSum_disk (by simp) hb hw
  set A : ℕ → ℂ := fun n => a₁ * (a₁ + 1) * c (a₁ + 2) n +
    a₁ * (b₁ + b₂ - 3 * a₁ - 2) * c (a₁ + 1) n +
    ((2 * a₁ - b₁) * (2 * a₁ - b₂) + a₁ - a₁ ^ 2) * c a₁ n -
    (a₁ - b₁) * (a₁ - b₂) * c (a₁ - 1) n with hAdef
  set Z : ℕ → ℂ := fun n => -(a₁ * (a₁ + 1)) * c (a₁ + 2) n +
    a₁ * (2 * a₁ - a₂ - a₃ + 1) * c (a₁ + 1) n - (a₁ - a₂) * (a₁ - a₃) * c a₁ n with hZdef
  have hSA : HasSum (fun n => A n * w ^ n)
      (a₁ * (a₁ + 1) * generalizedHypergeometric {a₁ + 2, a₂, a₃} {b₁, b₂} w +
        a₁ * (b₁ + b₂ - 3 * a₁ - 2) * generalizedHypergeometric {a₁ + 1, a₂, a₃} {b₁, b₂} w +
        ((2 * a₁ - b₁) * (2 * a₁ - b₂) + a₁ - a₁ ^ 2) *
            generalizedHypergeometric {a₁, a₂, a₃} {b₁, b₂} w -
        (a₁ - b₁) * (a₁ - b₂) * generalizedHypergeometric {a₁ - 1, a₂, a₃} {b₁, b₂} w) := by
    convert ((((hs (a₁ + 2)).mul_left (a₁ * (a₁ + 1))).add
      ((hs (a₁ + 1)).mul_left (a₁ * (b₁ + b₂ - 3 * a₁ - 2)))).add
      ((hs a₁).mul_left ((2 * a₁ - b₁) * (2 * a₁ - b₂) + a₁ - a₁ ^ 2))).sub
      ((hs (a₁ - 1)).mul_left ((a₁ - b₁) * (a₁ - b₂))) using 1
    funext n; simp only [hAdef]; ring
  have hSZ : HasSum (fun n => Z n * w ^ n)
      (-(a₁ * (a₁ + 1)) * generalizedHypergeometric {a₁ + 2, a₂, a₃} {b₁, b₂} w +
        a₁ * (2 * a₁ - a₂ - a₃ + 1) * generalizedHypergeometric {a₁ + 1, a₂, a₃} {b₁, b₂} w -
        (a₁ - a₂) * (a₁ - a₃) * generalizedHypergeometric {a₁, a₂, a₃} {b₁, b₂} w) := by
    convert (((hs (a₁ + 2)).mul_left (-(a₁ * (a₁ + 1)))).add
      ((hs (a₁ + 1)).mul_left (a₁ * (2 * a₁ - a₂ - a₃ + 1)))).sub
      ((hs a₁).mul_left ((a₁ - a₂) * (a₁ - a₃))) using 1
    funext n; simp only [hZdef]; ring
  have hA0 : A 0 = 0 := by
    simp only [hAdef, hc, generalizedHypergeometricCoeff, pochhammerProduct, pochhammer_zero,
        Multiset.insert_eq_cons,
      Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
    norm_num
    ring
  have h1 := (hasSum_nat_add_iff' 1).mpr hSA
  simp only [Finset.range_one, Finset.sum_singleton, hA0, pow_zero, mul_one, sub_zero] at h1
  have h2 := hSZ.mul_left w
  have h3 := h1.add h2
  have h4 : HasSum (fun n : ℕ => (A (n + 1) + Z n) * w ^ (n + 1)) 0 := by
    convert hasSum_zero using 1
    funext n
    have := gen3F2_contiguous_coeff a₁ a₂ a₃ b₁ b₂ hb n
    simp only [hAdef, hZdef]
    rw [this, zero_mul]
  have h5 := h3.unique (h4.congr_fun fun n => by rw [pow_succ]; ring)
  linear_combination h5

end DLMF.Hypergeometric
