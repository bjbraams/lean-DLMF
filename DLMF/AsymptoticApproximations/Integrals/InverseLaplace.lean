/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Integrals.Watson
public import DLMFMathlib.Analysis.SpecialFunctions.Pow.Decay
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import DLMFMathlib.Analysis.Integral.LaplaceConvergence

/-!
# Inverse Laplace expansions with complex exponents

DLMF 2.4.4–2.4.5 holds for any strictly increasing sequence of positive real parts.
A differentiated remainder gives absolute convergence after one integration by parts;
the real parts need not tend to infinity.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology Real

namespace DLMF.AsymptoticApproximations

/-- The inverse Laplace integral of a principal complex power `z^(-α)` is
`t^(α-1)/Γ(α)` for `Re α > 0`. This checks the Gamma normalization. -/
theorem tendsto_bromwichPartialIntegral_cpow_neg {α : ℂ} (hα : 0 < α.re) {σ t : ℝ}
    (hσ : 0 < σ) (ht : 0 < t) :
    Tendsto (bromwichPartialIntegral (fun z => z ^ (-α)) σ t) atTop
      (𝓝 ((t : ℂ) ^ (α - 1) / Gamma α)) := by
  have hΓ : Gamma α ≠ 0 := Gamma_ne_zero fun n hn => by
    have h := congrArg Complex.re hn
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h := (tendsto_bromwichPartialIntegral_Gamma_cpow hα hσ ht).div_const (Gamma α)
  refine h.congr fun T => ?_
  unfold bromwichPartialIntegral
  rw [div_eq_mul_inv, mul_assoc, ← intervalIntegral.integral_mul_const]
  congr 1
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  field_simp

/-- Subtracting a finite sum of continuous transforms commutes with the truncated inverse
Laplace integral on a fixed line. -/
theorem bromwichPartialIntegral_sub_sum {Q : ℂ → ℂ} {P : ℕ → ℂ → ℂ} {σ : ℝ}
    (hQ : Continuous fun y : ℝ => Q (σ + y * I))
    (hP : ∀ s, Continuous fun y : ℝ => P s (σ + y * I)) (N : ℕ) (t T : ℝ) :
    bromwichPartialIntegral (fun z => Q z - ∑ s ∈ range N, P s z) σ t T =
      bromwichPartialIntegral Q σ t T -
        ∑ s ∈ range N, bromwichPartialIntegral (P s) σ t T := by
  have hi (s : ℕ) : IntervalIntegrable
      (fun y : ℝ => exp (t * (σ + y * I)) * P s (σ + y * I)) volume (-T) T :=
    ((by fun_prop : Continuous fun y : ℝ => exp (t * (σ + y * I))).mul
      (hP s)).intervalIntegrable _ _
  have hiQ : IntervalIntegrable
      (fun y : ℝ => exp (t * (σ + y * I)) * Q (σ + y * I)) volume (-T) T :=
    ((by fun_prop : Continuous fun y : ℝ => exp (t * (σ + y * I))).mul
      hQ).intervalIntegrable _ _
  have hiS : IntervalIntegrable (fun y : ℝ => ∑ s ∈ range N,
      exp (t * (σ + y * I)) * P s (σ + y * I)) volume (-T) T := by
    convert IntervalIntegrable.sum (range N) (fun s _ => hi s) using 1
    funext y
    simp only [Finset.sum_apply]
  simp only [bromwichPartialIntegral, mul_sub, mul_sum]
  rw [intervalIntegral.integral_sub hiQ hiS,
    intervalIntegral.integral_finsetSum (fun s _ => hi s), mul_sub, mul_sum]

/-- Inverse Laplace expansion for arbitrary complex exponents with positive real parts:
stronger than DLMF, which assumes that those real parts strictly increase. The two
expansions select the same inverse on every line in the closed half-plane. -/
@[dlmf 2.4.E4 "stronger than DLMF: no monotonicity of the exponent real parts",
  dlmf 2.4.E5 "stronger than DLMF: no monotonicity of the exponent real parts"]
theorem exists_inverseLaplace_hasExpansion' {Q : ℂ → ℂ} {a α : ℕ → ℂ} {c : ℝ}
    (hc : 0 < c) (hα : ∀ n, 0 < (α n).re)
    (hQ : AnalyticOnNhd ℂ Q {z | c ≤ z.re})
    (hexp : HasAsymptoticExpansion
      (comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | c ≤ z.re})
      (fun n z => z ^ (-α n)) (fun n => Gamma (α n) * a n) Q)
    (hexpd : HasAsymptoticExpansion
      (comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | c ≤ z.re})
      (fun n z => z ^ (-α n - 1)) (fun n => -α n * Gamma (α n) * a n) (deriv Q)) :
    ∃ q : ℝ → ℂ, (∀ σ, c ≤ σ → ∀ t, 0 < t →
      Tendsto (bromwichPartialIntegral Q σ t) atTop (𝓝 (q t))) ∧
      HasAsymptoticExpansion (𝓝[>] 0)
        (fun n (t : ℝ) => (t : ℂ) ^ (α n - 1)) a q := by
  classical
  let P : ℕ → ℂ → ℂ := fun s z => Gamma (α s) * a s * z ^ (-α s)
  let R : ℕ → ℂ → ℂ := fun N z => Q z - ∑ s ∈ range N, P s z
  have hP (s : ℕ) : AnalyticOnNhd ℂ (P s) {z | c ≤ z.re} := by
    intro z hz
    exact analyticAt_const.mul (analyticAt_id.cpow analyticAt_const
      (mem_slitPlane_iff.mpr (Or.inl (hc.trans_le hz))))
  have hRd (N : ℕ) {z : ℂ} (hz : c ≤ z.re) :
      HasDerivAt (R N)
        (deriv Q z - ∑ s ∈ range N, (-α s * Gamma (α s) * a s) * z ^ (-α s - 1)) z := by
    apply (hQ z hz).differentiableAt.hasDerivAt.sub
    convert HasDerivAt.fun_sum (fun s (_ : s ∈ range N) =>
      (((hasDerivAt_id z).cpow_const (c := -α s) (Or.inl (hc.trans_le hz))).const_mul
        (Gamma (α s) * a s))) using 1 <;>
      simp only [R, P, mul_one, id_eq]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hRa (N : ℕ) : AnalyticOnNhd ℂ (R N) {z | c ≤ z.re} :=
    hQ.sub (fun z hz => Finset.analyticAt_fun_sum _ fun s _ => hP s z hz)
  have hRi (N : ℕ) : ∃ qN : ℝ → ℂ,
      (∀ σ, c ≤ σ → ∀ t, 0 < t →
        Tendsto (bromwichPartialIntegral (R N) σ t) atTop (𝓝 (qN t))) ∧
      qN =O[𝓝[>] 0] (fun t : ℝ => t ^ ((α N).re - 1)) := by
    have hpow (β : ℂ) : (fun z : ℂ => z ^ β) =O[
        comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | c ≤ z.re}]
        (fun z : ℂ => ‖z‖ ^ β.re) :=
      isBigO_cpow_rpow isBoundedUnder_const
    have hbR := (hexp N).trans (hpow (-α N))
    have hbD := (hexpd N).trans (hpow (-α N - 1))
    obtain ⟨C, hC, hbC⟩ := hbR.exists_pos
    obtain ⟨D, hD, hbD⟩ := hbD.exists_pos
    have hb : ∀ᶠ z in comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | c ≤ z.re},
        ‖R N z‖ ≤ C * ‖z‖ ^ (-(α N).re) ∧
          ‖deriv (R N) z‖ ≤ D * ‖z‖ ^ (-((α N).re + 1)) := by
      filter_upwards [hbC.bound, hbD.bound,
        (show ∀ᶠ z in comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | c ≤ z.re}, c ≤ z.re from
          eventually_inf_principal.mpr (Eventually.of_forall fun z hz => hz))] with z hz hzD hzc
      rw [(hRd N hzc).deriv]
      simpa only [R, P, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
        neg_re, sub_re, add_re, one_re, neg_add, sub_eq_add_neg,
        Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)] using And.intro hz hzD
    rw [eventually_inf_principal, eventually_comap] at hb
    obtain ⟨K, hK⟩ := eventually_atTop.mp hb
    obtain ⟨qN, hqN, hbN⟩ := exists_inverseLaplace_of_deriv_norm_le_rpow hc hC.le hD.le
      (hα N) (hRa N) (fun z hz hKz => (hK ‖z‖ hKz z rfl hz).1)
      (fun z hz hKz => (hK ‖z‖ hKz z rfl hz).2)
    refine ⟨qN, fun σ hσ t ht => ?_, hbN⟩
    convert hqN σ hσ t ht using 1
    funext T
    simp only [bromwichPartialIntegral, ofReal_mul, ofReal_ofNat]
  have hlin (N : ℕ) (σ t T : ℝ) (hσ : c ≤ σ) :
      bromwichPartialIntegral (R N) σ t T = bromwichPartialIntegral Q σ t T -
        ∑ s ∈ range N, bromwichPartialIntegral (P s) σ t T :=
    bromwichPartialIntegral_sub_sum
      (continuous_iff_continuousAt.mpr fun y => ContinuousAt.comp
        (g := Q) (f := fun y : ℝ => (σ : ℂ) + y * I)
        (hQ _ (by simpa using hσ)).continuousAt (by fun_prop))
      (fun s => continuous_iff_continuousAt.mpr fun y => ContinuousAt.comp
        (g := P s) (f := fun y : ℝ => (σ : ℂ) + y * I)
        (hP s _ (by simpa using hσ)).continuousAt (by fun_prop)) N t T
  have hmodel (s : ℕ) (σ t : ℝ) (hσ : c ≤ σ) (ht : 0 < t) :
      Tendsto (bromwichPartialIntegral (P s) σ t) atTop
        (𝓝 ((t : ℂ) ^ (α s - 1) * a s)) := by
    have h := (tendsto_bromwichPartialIntegral_Gamma_cpow (hα s)
      (hc.trans_le hσ) ht).mul_const (a s)
    refine h.congr fun T => ?_
    simp only [bromwichPartialIntegral, P]
    rw [mul_assoc, ← intervalIntegral.integral_mul_const]
    congr 1
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    ring
  obtain ⟨q, hq, _⟩ := hRi 0
  have hq' (σ : ℝ) (hσ : c ≤ σ) (t : ℝ) (ht : 0 < t) :
      Tendsto (bromwichPartialIntegral Q σ t) atTop (𝓝 (q t)) := by
    simpa only [R, Finset.range_zero, sum_empty, sub_zero] using hq σ hσ t ht
  refine ⟨q, hq', fun N => ?_⟩
  obtain ⟨qN, hqN, hbN⟩ := hRi N
  have he (t : ℝ) (ht : 0 < t) : q t - ∑ s ∈ range N, (t : ℂ) ^ (α s - 1) * a s =
      qN t := by
    apply tendsto_nhds_unique _ (hqN c le_rfl t ht)
    have h := (hq' c le_rfl t ht).sub
      (tendsto_finsetSum (range N) fun s _ => hmodel s c t le_rfl ht)
    exact h.congr fun T => (hlin N c t T le_rfl).symm
  have hb := hbN.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (he t ht).symm) EventuallyEq.rfl
  refine hb.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [one_mul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]

/-- DLMF 2.4.4–2.4.5 for arbitrary complex exponents with strictly increasing positive
real parts. The real parts need not tend to infinity. -/
@[dlmf 2.4.E4, dlmf 2.4.E5]
theorem exists_inverseLaplace_hasExpansion {Q : ℂ → ℂ} {a α : ℕ → ℂ} {c : ℝ}
    (hc : 0 < c) (hα0 : 0 < (α 0).re) (hα : StrictMono fun n => (α n).re)
    (hQ : AnalyticOnNhd ℂ Q {z | c ≤ z.re})
    (hexp : HasAsymptoticExpansion
      (comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | c ≤ z.re})
      (fun n z => z ^ (-α n)) (fun n => Gamma (α n) * a n) Q)
    (hexpd : HasAsymptoticExpansion
      (comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | c ≤ z.re})
      (fun n z => z ^ (-α n - 1)) (fun n => -α n * Gamma (α n) * a n) (deriv Q)) :
    ∃ q : ℝ → ℂ, (∀ σ, c ≤ σ → ∀ t, 0 < t →
      Tendsto (bromwichPartialIntegral Q σ t) atTop (𝓝 (q t))) ∧
      HasAsymptoticExpansion (𝓝[>] 0)
        (fun n (t : ℝ) => (t : ℂ) ^ (α n - 1)) a q := by
  exact exists_inverseLaplace_hasExpansion' hc
    (fun n => hα0.trans_le (hα.monotone (Nat.zero_le n))) hQ hexp hexpd

end DLMF.AsymptoticApproximations
