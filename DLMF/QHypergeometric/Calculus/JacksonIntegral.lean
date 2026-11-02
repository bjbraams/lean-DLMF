/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.Calculus
public import DLMF.QHypergeometric.Convergence
public import DLMF.QSeries.QCalculus
public import DLMF.QSeries.Saalschutz
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import DLMF.QHypergeometric.Calculus.QBinomial

/-!
# Jackson integrals (DLMF 17.2.45–17.2.48)

Finite-interval and bilateral Jackson integrals as adapters around `DLMF.QSeries.jacksonIntegral`.
Natural partial-sum predicates keep conditional convergence distinct from Lean's totalized,
unordered `tsum`. The bilateral integral `jacksonBilateral` is defined in
`DLMF.QHypergeometric.Basic.Calculus`.

## Main results

* `jackson_series_hasSum`: the defining series 17.2.45–17.2.46.
* `jacksonBetween_additivity`: additivity in the endpoints.
* `jackson_classical_limit`: convergence to the Riemann integral as `q → 1` (17.2.47).
* `jackson_bilateral_limit`, `jackson_bilateral_natural_limit`: the bilateral integral 17.2.48.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory Asymptotics
open scoped Real Topology
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- A finite two-endpoint Jackson integral, reusing the existing integral from zero. -/
def jacksonBetween (q a b : ℂ) (f : ℂ → ℂ) : ℂ :=
  DLMF.QSeries.jacksonIntegral q b f-DLMF.QSeries.jacksonIntegral q a f
/-- Natural-order convergence of the finite-interval Jackson series, permitting conditional sums. -/
def HasNaturalJacksonIntegral (q a : ℂ) (f : ℂ → ℂ) (v : ℂ) : Prop :=
  Tendsto (fun N : ℕ => a*(1-q)*∑ j∈range N, f (a*q^j)*q^j) atTop (𝓝 v)
/-- Bilateral natural convergence means convergence of both tails separately. -/
def HasNaturalJacksonBilateral (q : ℂ) (f : ℂ → ℂ) (v : ℂ) : Prop :=
  ∃ vp vm : ℂ,
    Tendsto (fun N : ℕ => ∑ j∈range N, q^j*f (q^j)) atTop (𝓝 vp) ∧
    Tendsto (fun N : ℕ => ∑ j∈range N, q^(-(j:ℤ)-1)*f (q^(-(j:ℤ)-1))) atTop (𝓝 vm) ∧
    v=(1-q)*(vp+vm)

/-- For `|q| < 1` and `f` continuous at `0`, the Jackson integral `∫_0^a f d_q t` is the sum of
its defining series (DLMF 17.2.E45, E46). -/
@[dlmf 17.2.E45, dlmf 17.2.E46]
theorem jackson_series_hasSum {q a : ℂ} (hq : ‖q‖<1) {f : ℂ → ℂ} (hf : ContinuousAt f 0) :
    HasSum (fun j : ℕ => a*(1-q)*f (a*q^j)*q^j) (jacksonIntegral q a f) := by
  have hpow := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul a
  simp only [mul_zero] at hpow
  have hcont : Tendsto (fun j : ℕ => f (a*q^j)) atTop (𝓝 (f 0)) := by
    simpa only [Function.comp_def] using hf.tendsto.comp hpow
  obtain ⟨B,hB⟩ := hcont.norm.bddAbove_range
  have hs : Summable (fun j : ℕ => f (a*q^j)*q^j) :=
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left B)
      (fun j => by simpa [norm_mul,norm_pow] using
        mul_le_mul_of_nonneg_right (hB ⟨j,rfl⟩) (pow_nonneg (norm_nonneg q) j))
  simpa only [jacksonIntegral,mul_assoc] using hs.hasSum.mul_left (a*(1-q))

/-- Additivity of the two-endpoint Jackson integral over adjacent intervals. -/
theorem jacksonBetween_additivity (q a b c : ℂ) (f : ℂ → ℂ) :
    jacksonBetween q a c f=jacksonBetween q a b f+jacksonBetween q b c f := by
  simp only [jacksonBetween]; ring

/-- Uniform continuity controls the error of the geometric Riemann sum defining Jackson's
integral; the maximum interval width is `|a| (1-q)`. -/
private lemma jackson_error_bound {f : ℝ → ℂ} {a q ε : ℝ}
    (hf : ContinuousOn f (uIcc 0 a)) (hq0 : 0 < q) (hq1 : q < 1)
    (hmod : ∀ x ∈ uIcc 0 a, ∀ y ∈ uIcc 0 a,
      dist x y ≤ |a| * (1 - q) → ‖f x - f y‖ ≤ ε) :
    ‖jacksonIntegral (q : ℂ) (a : ℂ) (fun z => f z.re) - ∫ x in 0..a, f x‖ ≤ ε * |a| := by
  have hp (n : ℕ) : 0 ≤ q ^ n ∧ q ^ n ≤ 1 :=
    ⟨pow_nonneg hq0.le n, pow_le_one₀ hq0.le hq1.le⟩
  have hm (n : ℕ) : a * q ^ n ∈ uIcc 0 a := by
    rcases le_total 0 a with ha | ha
    · rw [uIcc_of_le ha]; exact ⟨by nlinarith [(hp n).1], by nlinarith [(hp n).2]⟩
    · rw [uIcc_of_ge ha]; exact ⟨by nlinarith [(hp n).2], by nlinarith [(hp n).1]⟩
  have hsub (n : ℕ) : uIcc (a * q ^ (n + 1)) (a * q ^ n) ⊆ uIcc 0 a :=
    uIcc_subset_uIcc (hm (n + 1)) (hm n)
  have hi (n : ℕ) : IntervalIntegrable f volume (a * q ^ (n + 1)) (a * q ^ n) :=
    hf.intervalIntegrable.mono_set (hsub n)
  have hw (n : ℕ) : |a * q ^ n - a * q ^ (n + 1)| = |a| * (1 - q) * q ^ n := by
    rw [show a * q ^ n - a * q ^ (n + 1) = a * (1 - q) * q ^ n by rw [pow_succ]; ring,
      abs_mul, abs_mul, abs_of_pos (sub_pos.mpr hq1), abs_of_nonneg (hp n).1]
  obtain ⟨B, hB⟩ := isCompact_uIcc.exists_bound_of_continuousOn hf
  have hv (n : ℕ) : ‖∫ x in 0..a * q ^ n, f x‖ ≤ B * |a| * q ^ n := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := a * q ^ n)
      (fun x hx => hB x (uIcc_subset_uIcc_left (hm n) (uIoc_subset_uIcc hx)))
    simpa [abs_mul, abs_of_nonneg (hp n).1, mul_assoc] using h
  have hlim : Tendsto (fun n : ℕ => ∫ x in 0..a * q ^ n, f x) atTop (𝓝 0) :=
    squeeze_zero_norm hv (by simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul (B * |a|))
  have hI : Summable (fun n : ℕ => ∫ x in a * q ^ (n + 1)..a * q ^ n, f x) := by
    apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0.le hq1).mul_left
      (B * |a| * (1 - q)))
    intro n
    simpa [hw, mul_assoc] using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a * q ^ (n + 1)) (b := a * q ^ n)
      (fun x hx => hB x (hsub n (uIoc_subset_uIcc hx)))
  have hsI : HasSum (fun n : ℕ => ∫ x in a * q ^ (n + 1)..a * q ^ n, f x) (∫ x in 0..a, f x) := by
    apply hI.hasSum_iff_tendsto_nat.mpr
    have he (n : ℕ) : (∫ x in a * q ^ (n + 1)..a * q ^ n, f x) =
        (∫ x in 0..a * q ^ n, f x) - ∫ x in 0..a * q ^ (n + 1), f x := by
      have h := intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable.mono_set (uIcc_subset_uIcc_left (hm (n + 1)))) (hi n)
      linear_combination h
    simp_rw [he, sum_range_sub']
    simpa using tendsto_const_nhds.sub hlim
  have hJ : Summable (fun n : ℕ => f (a * q ^ n) * (q : ℂ) ^ n) := by
    apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0.le hq1).mul_left B)
    intro n
    simpa [norm_mul, norm_pow, Complex.norm_of_nonneg hq0.le, abs_of_pos hq0] using
      mul_le_mul_of_nonneg_right (hB _ (hm n)) (hp n).1
  have hsJ : HasSum (fun n : ℕ => ((a * (1 - q) * q ^ n : ℝ) : ℂ) * f (a * q ^ n))
      (jacksonIntegral (q : ℂ) (a : ℂ) (fun z => f z.re)) := by
    convert hJ.hasSum.mul_left ((a : ℂ) * (1 - q)) using 1
    · ext n; push_cast; ring
    · simp [jacksonIntegral, ← Complex.ofReal_pow]
  have hg := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left (ε * |a| * (1 - q))
  have hgv : HasSum (fun n : ℕ => ε * |a| * (1 - q) * q ^ n) (ε * |a|) := by
    convert hg using 1
    field_simp
  apply (hsJ.sub hsI).norm_le_of_bounded hgv
  intro n
  have he : ((a * (1 - q) * q ^ n : ℝ) : ℂ) * f (a * q ^ n) -
      (∫ x in a * q ^ (n + 1)..a * q ^ n, f x) =
      ∫ x in a * q ^ (n + 1)..a * q ^ n, f (a * q ^ n) - f x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hi n),
        intervalIntegral.integral_const]
    push_cast
    rw [real_smul]
    congr 1
    push_cast
    rw [pow_succ]
    ring
  rw [he]
  have hb : ∀ x ∈ uIoc (a * q ^ (n + 1)) (a * q ^ n), ‖f (a * q ^ n) - f x‖ ≤ ε := by
    intro x hx
    have hx' := uIoc_subset_uIcc hx
    apply hmod _ (hm n) x (hsub n hx')
    have hd := Real.dist_right_le_of_mem_uIcc hx'
    rw [dist_comm]
    apply hd.trans
    rw [Real.dist_eq, abs_sub_comm, hw]
    exact mul_le_of_le_one_right (by positivity) (hp n).2
  simpa [hw, mul_assoc] using intervalIntegral.norm_integral_le_of_norm_le_const hb

/-- As `q → 1⁻`, the Jackson integral of a continuous function tends to its Riemann integral (DLMF
17.2.E47). -/
@[dlmf 17.2.E47]
theorem jackson_classical_limit {f : ℝ → ℂ} {a : ℝ} (hf : ContinuousOn f (uIcc 0 a)) :
    Tendsto (fun q : ℝ => jacksonIntegral (q : ℂ) (a : ℂ) (fun z => f z.re))
      (𝓝[<] 1) (𝓝 (∫ x : ℝ in 0..a, f x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η := ε / (|a| + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_uIcc.uniformContinuousOn_of_continuous hf) η hη
  have ht : Tendsto (fun q : ℝ => |a| * (1 - q)) (𝓝[<] 1) (𝓝 0) := by
    have hc : Continuous (fun q : ℝ => |a| * (1 - q)) := by fun_prop
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1), ht.eventually (Iio_mem_nhds hδ)]
    with q hq hmesh
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (jackson_error_bound (ε := η) hf hq.1 hq.2 ?_) ?_
  · intro x hx y hy hxy
    simpa only [dist_eq_norm] using (hmod x hx y hy (hxy.trans_lt hmesh)).le
  · dsimp [η]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < |a| + 1)]
    nlinarith [abs_nonneg a]

/-- For an absolutely summable bilateral Jackson series, the integrals `∫_0^(q^(-n)) f d_q t` tend
to the bilateral Jackson integral (DLMF 17.2.E48). -/
@[dlmf 17.2.E48]
theorem jackson_bilateral_limit {q : ℝ} (hq0 : 0<q) {f : ℂ → ℂ}
    (hf : Summable (fun j : ℤ => (q:ℂ)^j*f ((q:ℂ)^j))) :
    Tendsto (fun n : ℕ => jacksonIntegral (q:ℂ) ((q:ℂ)^(-(n:ℤ))) f) atTop
      (𝓝 (jacksonBilateral q f)) := by
  have hq0' : (q:ℂ)≠0 := by exact_mod_cast hq0.ne'
  simp only [jacksonIntegral_zpow_neg hq0' f]
  unfold jacksonBilateral
  apply Tendsto.const_mul
  apply tendsto_tsum_of_dominated_convergence (bound := fun k : ℤ => ‖(q:ℂ)^k*f ((q:ℂ)^k)‖)
  · exact summable_norm_iff.mpr hf
  · intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k.natAbs] with n hn
    split_ifs <;> first | rfl | omega
  · refine Eventually.of_forall fun n k => ?_
    split_ifs <;> simp; positivity

/-- The same improper-integral identity for two naturally convergent tails, without assuming
absolute summability. -/
@[dlmf 17.2.E48]
theorem jackson_bilateral_natural_limit {q : ℝ} (hq0 : 0<q) {f : ℂ → ℂ} {v : ℂ}
    (hf : HasNaturalJacksonBilateral q f v) :
    ∃ J : ℕ → ℂ,
      (∀ n : ℕ, HasNaturalJacksonIntegral q ((q:ℂ)^(-(n:ℤ))) f (J n)) ∧
      Tendsto J atTop (𝓝 v) := by
  obtain ⟨vp,vm,hp,hm,hv⟩ := hf
  have hq0' : (q:ℂ)≠0 := by exact_mod_cast hq0.ne'
  refine ⟨fun n => (1-(q:ℂ))*((∑ i∈range n, (q:ℂ)^(-(i:ℤ)-1)*f ((q:ℂ)^(-(i:ℤ)-1)))+vp),?_,?_⟩
  · intro n
    unfold HasNaturalJacksonIntegral
    have ht : Tendsto (fun N : ℕ => N-n) atTop atTop := tendsto_sub_atTop_nat n
    have h := ((hp.comp ht).const_add
        (∑ i∈range n, (q:ℂ)^(-(i:ℤ)-1)*f ((q:ℂ)^(-(i:ℤ)-1)))).const_mul
      (1-(q:ℂ))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    obtain ⟨M,rfl⟩ := Nat.exists_eq_add_of_le hN
    simp only [Function.comp_apply,Nat.add_sub_cancel_left]
    rw [jackson_finite_sum_split hq0' f n M]
  · rw [hv,add_comm vp vm]
    exact (hm.add_const vp).const_mul _

/-- The complete two-index Gaussian limit, including the fixed-index boundary s=0. -/
@[dlmf 17.2.E34]
theorem qBinom_two_index_limit {q : ℂ} (hq : ‖q‖<1) {r s : ℕ} (hrs : s<r)
    (u t : ℕ) : Tendsto (fun n : ℕ => qBinom q (r*n+u) (s*n+t)) atTop
      (𝓝 (if s=0 then (qPochhammer q q t)⁻¹ else (qPochhammerInf q q)⁻¹)) := by
  by_cases hs : s=0
  · subst s
    simp only [Nat.zero_mul,zero_add,ite_true]
    have hr : 0<r := hrs
    have ht : Tendsto (fun n : ℕ => r*n+u) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by nlinarith⟩
    exact (qBinom_fixed_lower_limit hq t).comp ht
  · simpa [hs] using qBinom_two_growing_indices hq (Nat.pos_of_ne_zero hs) hrs u t

end DLMF.QHypergeometric
