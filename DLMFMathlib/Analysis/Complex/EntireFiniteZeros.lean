/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Entire functions of order less than one with finitely many zeros

An entire function `f` with finitely many zeros and growth `‖f z‖ ≤ C e^{‖z‖^ρ}`, `0 ≤ ρ < 1`, is
a polynomial. This is the special case of Hadamard's factorization theorem that is needed to show
that a transcendental entire function of order less than one has infinitely many zeros (for
example the discriminant of Hill's equation, of order `1/2`).

## Main results

* `Complex.exists_differentiable_exp_eq_of_ne_zero`: a nonvanishing entire function is `exp ∘ k`
  with `k` entire.
* `Complex.deriv_eq_zero_of_re_le_rpow`: an entire function with `Re k z ≤ A + ‖z‖^ρ`, `ρ < 1`,
  is constant (Borel–Carathéodory and the Cauchy estimate).
* `Complex.exists_polynomial_mul_of_finite_zeros`: an entire function with finitely many zeros
  is a polynomial times a nonvanishing entire function.
* `Complex.exists_eq_polynomial_eval_of_finite_zeros`: the main result.
-/

@[expose] public section

open Set Filter Metric Topology MeromorphicOn

namespace Complex

/-- A nonvanishing entire function is the exponential of an entire function. -/
theorem exists_differentiable_exp_eq_of_ne_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hne : ∀ z, g z ≠ 0) : ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ z, g z = exp (k z) := by
  have hg' : Differentiable ℂ (deriv g) := fun z => ((hg.analyticAt z).deriv).differentiableAt
  have hq : Differentiable ℂ fun z => deriv g z / g z := hg'.div hg hne
  obtain ⟨F, hF⟩ := hq.isExactOn_univ
  have hD : ∀ z, HasDerivAt (fun z => exp (-F z) * g z) 0 z := fun z => by
    have h1 := ((hF z (mem_univ z)).neg).cexp
    have h2 := h1.mul (hg z).hasDerivAt
    convert h2 using 1
    field_simp [hne z]
    ring
  have hc : ∀ z, exp (-F z) * g z = exp (-F 0) * g 0 := fun z =>
    is_const_of_deriv_eq_zero (fun z => (hD z).differentiableAt) (fun z => (hD z).deriv) z 0
  set c := exp (-F 0) * g 0
  have hc0 : c ≠ 0 := mul_ne_zero (exp_ne_zero _) (hne 0)
  refine ⟨fun z => F z + log c, fun z => ((hF z (mem_univ z)).differentiableAt).add_const _,
    fun z => ?_⟩
  rw [exp_add, exp_log hc0, ← hc z, ← mul_assoc, ← exp_add]
  simp

/-- An entire function whose real part grows at most like `A + ‖z‖^ρ`, `ρ < 1`, is constant. -/
theorem deriv_eq_zero_of_re_le_rpow {k : ℂ → ℂ} (hk : Differentiable ℂ k) {A ρ : ℝ}
    (hA : 0 < A) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (hre : ∀ z, (k z).re ≤ A + ‖z‖ ^ ρ) (c : ℂ) :
    deriv k c = 0 := by
  set B := 2 * A + 3 * ‖k 0‖
  have key : ∀ r : ℝ, ‖c‖ + 1 ≤ r → ‖deriv k c‖ ≤ B / r + 8 * r ^ (ρ - 1) := by
    intro r hr
    have hr0 : 0 < r := by linarith [norm_nonneg c]
    set s := ‖c‖ + r
    have hs : 0 < s := by positivity
    set M := A + (2 * s) ^ ρ
    have hM : 0 < M := by positivity
    have hbd : ∀ z ∈ sphere c r, ‖k z‖ ≤ B + 8 * r ^ ρ := by
      intro z hz
      have hzs : ‖z‖ ≤ s := by
        rw [mem_sphere, dist_eq_norm] at hz
        calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
          _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
          _ = s := by rw [hz]; ring
      have hzball : z ∈ ball (0 : ℂ) (2 * s) := by
        rw [mem_ball_zero_iff]; linarith
      have hmaps : MapsTo k (ball 0 (2 * s)) {w | w.re ≤ M} := by
        intro w hw
        rw [mem_ball_zero_iff] at hw
        show (k w).re ≤ M
        refine (hre w).trans ?_
        simp only [M]
        gcongr
      have hBC := borelCaratheodory hM hk.differentiableOn hmaps (by positivity) hzball
      have hden : s ≤ 2 * s - ‖z‖ := by linarith
      have hd0 : 0 < 2 * s - ‖z‖ := by linarith
      have e1 : 2 * M * ‖z‖ / (2 * s - ‖z‖) ≤ 2 * M := by
        rw [div_le_iff₀ hd0]; nlinarith [norm_nonneg z]
      have e2 : ‖k 0‖ * (2 * s + ‖z‖) / (2 * s - ‖z‖) ≤ 3 * ‖k 0‖ := by
        rw [div_le_iff₀ hd0]; nlinarith [norm_nonneg z, norm_nonneg (k 0)]
      have e3 : (2 * s) ^ ρ ≤ 4 * r ^ ρ := by
        have h1 : 2 * s ≤ 4 * r := by simp only [s]; linarith
        calc (2 * s) ^ ρ ≤ (4 * r) ^ ρ := Real.rpow_le_rpow (by positivity) h1 hρ0
          _ = 4 ^ ρ * r ^ ρ := Real.mul_rpow (by norm_num) hr0.le
          _ ≤ 4 * r ^ ρ := by
            gcongr
            calc (4 : ℝ) ^ ρ ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hρ.le
              _ = 4 := by simp
      calc ‖k z‖ ≤ _ := hBC
        _ ≤ 2 * M + 3 * ‖k 0‖ := add_le_add e1 e2
        _ ≤ B + 8 * r ^ ρ := by simp only [M, B]; linarith
    have hC := norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hk.diffContOnCl hbd
    calc ‖deriv k c‖ ≤ (B + 8 * r ^ ρ) / r := hC
      _ = B / r + 8 * r ^ (ρ - 1) := by
        rw [add_div, Real.rpow_sub hr0, Real.rpow_one]; ring
  have hlim : Tendsto (fun r : ℝ => B / r + 8 * r ^ (ρ - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => B / r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun r : ℝ => r ^ (ρ - 1)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := 1 - ρ) (by linarith)
      simpa [neg_sub] using this
    simpa using h1.add (h2.const_mul 8)
  have hle : ‖deriv k c‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨‖c‖ + 1, key⟩)
  exact norm_le_zero_iff.mp hle

/-- Continuous functions that agree on a codiscrete set agree everywhere. -/
private theorem eq_of_eventuallyEq_codiscrete {f h : ℂ → ℂ} (hf : Continuous f) (hh : Continuous h)
    (heq : f =ᶠ[codiscreteWithin univ] h) : f = h := by
  funext x
  have hx := (mem_codiscreteWithin.mp heq) x (mem_univ x)
  rw [disjoint_principal_right] at hx
  have hS : ∀ᶠ y in 𝓝[≠] x, f y = h y := by
    filter_upwards [hx] with y hy
    simpa using hy
  exact tendsto_nhds_unique ((hf.tendsto x).mono_left nhdsWithin_le_nhds)
    (((hh.tendsto x).mono_left nhdsWithin_le_nhds).congr' (hS.mono fun y hy => hy.symm))

/-- An entire function with finitely many zeros is a polynomial times a nonvanishing entire
function. -/
theorem exists_polynomial_mul_of_finite_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hZ : {z | f z = 0}.Finite) :
    ∃ (T : Finset ℂ) (n : ℂ → ℕ) (g : ℂ → ℂ), Differentiable ℂ g ∧ (∀ z, g z ≠ 0) ∧
      ∀ z, f z = (∏ u ∈ T, (z - u) ^ n u) * g z := by
  have han : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have h₁ : MeromorphicOn f univ := han.meromorphicOn
  have h₂ : ∀ u : (univ : Set ℂ), meromorphicOrderAt f u ≠ ⊤ := by
    intro u htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hc : ({z | f z = 0} \ {(u : ℂ)})ᶜ ∈ 𝓝 (u : ℂ) :=
      (hZ.sdiff).isClosed.compl_mem_nhds (by simp)
    have h1 : {z | f z = 0} \ {(u : ℂ)} ∈ 𝓝[≠] (u : ℂ) := by
      filter_upwards [htop, self_mem_nhdsWithin] with z hz hne
      exact ⟨hz, hne⟩
    have h2 := Filter.inter_mem h1 (mem_nhdsWithin_of_mem_nhds hc)
    simp at h2
  have hsupp : (divisor f univ).support ⊆ {z | f z = 0} := by
    intro z hz
    by_contra hfz
    apply hz
    rw [han.divisor_apply (mem_univ z)]
    have : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hfz)
    simp [this]
  have h₃ : (divisor f univ).support.Finite := hZ.subset hsupp
  obtain ⟨g, hg, hgne, heq⟩ := h₁.extract_zeros_poles h₂ h₃
  have hd0 : ∀ u, 0 ≤ divisor f univ u := fun u => han.divisor_nonneg u
  set T := h₃.toFinset
  set n : ℂ → ℕ := fun u => (divisor f univ u).toNat
  have hgd : Differentiable ℂ g := fun z => (hg z (mem_univ z)).differentiableAt
  have hφ : (∏ᶠ u, (· - u) ^ divisor f univ u) = fun z => ∏ u ∈ T, (z - u) ^ n u := by
    rw [Function.FactorizedRational.finprod_eq_fun h₃]
    funext z
    rw [finprod_eq_prod_of_mulSupport_subset (s := T)]
    · refine Finset.prod_congr rfl fun u _ => ?_
      simp only [n]
      rw [← zpow_natCast, Int.toNat_of_nonneg (hd0 u)]
    · intro u hu
      simp only [T, Set.Finite.coe_toFinset, Function.mem_support]
      intro h0
      apply hu
      simp [h0]
  rw [hφ] at heq
  refine ⟨T, n, g, hgd, fun z => hgne ⟨z, mem_univ z⟩, fun z => ?_⟩
  have := eq_of_eventuallyEq_codiscrete hf.continuous
    ((by fun_prop : Continuous fun z : ℂ => ∏ u ∈ T, (z - u) ^ n u).mul hgd.continuous) heq
  exact congrFun this z

/-- **An entire function of order less than one with finitely many zeros is a polynomial.** If
`f` is entire, has finitely many zeros and satisfies `‖f z‖ ≤ C e^{‖z‖^ρ}` for `‖z‖ ≥ R`, with
`0 ≤ ρ < 1`, then `f` is a polynomial function. -/
theorem exists_eq_polynomial_eval_of_finite_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hZ : {z | f z = 0}.Finite) {ρ C R : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hgrowth : ∀ z, R ≤ ‖z‖ → ‖f z‖ ≤ C * Real.exp (‖z‖ ^ ρ)) :
    ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z := by
  obtain ⟨T, n, g, hg, hgne, hfg⟩ := exists_polynomial_mul_of_finite_zeros hf hZ
  obtain ⟨k, hk, hgk⟩ := exists_differentiable_exp_eq_of_ne_zero hg hgne
  set R₁ := max R (1 + ∑ u ∈ T, ‖u‖)
  -- the polynomial factor has norm at least one far out
  have hP : ∀ z, R₁ ≤ ‖z‖ → 1 ≤ ‖∏ u ∈ T, (z - u) ^ n u‖ := by
    intro z hz
    rw [norm_prod]
    refine Finset.one_le_prod₀ fun u hu => ?_
    rw [norm_pow]
    refine one_le_pow₀ ?_
    have hu' : ‖u‖ ≤ ∑ u ∈ T, ‖u‖ :=
      Finset.single_le_sum (f := fun u => ‖u‖) (fun _ _ => norm_nonneg _) hu
    have := le_trans (le_max_right _ _) hz
    calc (1 : ℝ) ≤ ‖z‖ - ‖u‖ := by linarith
      _ ≤ ‖z - u‖ := norm_sub_norm_le z u
  set C' := max C 1
  have hgb : ∀ z, R₁ ≤ ‖z‖ → (k z).re ≤ Real.log C' + ‖z‖ ^ ρ := by
    intro z hz
    have h1 : ‖g z‖ ≤ C' * Real.exp (‖z‖ ^ ρ) := by
      have hf' := hgrowth z (le_trans (le_max_left _ _) hz)
      rw [hfg z, norm_mul] at hf'
      have hg0 : 0 ≤ ‖g z‖ := norm_nonneg _
      calc ‖g z‖ ≤ ‖∏ u ∈ T, (z - u) ^ n u‖ * ‖g z‖ :=
            le_mul_of_one_le_left hg0 (hP z hz)
        _ ≤ C * Real.exp (‖z‖ ^ ρ) := hf'
        _ ≤ C' * Real.exp (‖z‖ ^ ρ) := by gcongr; exact le_max_left _ _
    have h2 : ‖g z‖ = Real.exp (k z).re := by rw [hgk z, norm_exp]
    have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [h2, ← Real.exp_log hC', ← Real.exp_add, Real.exp_le_exp] at h1
    exact h1
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) R₁).exists_bound_of_continuousOn
    ((continuous_re.comp hk.continuous).continuousOn)
  set A := 1 + max K 0 + Real.log C'
  have hlogC : 0 ≤ Real.log C' := Real.log_nonneg (le_max_right _ _)
  have hA : 0 < A := by positivity
  have hre : ∀ z, (k z).re ≤ A + ‖z‖ ^ ρ := by
    intro z
    have hpow : 0 ≤ ‖z‖ ^ ρ := Real.rpow_nonneg (norm_nonneg z) ρ
    by_cases hz : R₁ ≤ ‖z‖
    · have := hgb z hz
      have : 0 ≤ max K 0 := le_max_right _ _
      simp only [A]; linarith
    · have hzb : z ∈ closedBall (0 : ℂ) R₁ := by
        rw [mem_closedBall_zero_iff]; linarith
      have h1 := hK z hzb
      have h2 : (k z).re ≤ K := le_trans (le_abs_self _) (by simpa using h1)
      have : K ≤ max K 0 := le_max_left _ _
      simp only [A]; linarith
  have hd : ∀ z, deriv k z = 0 := deriv_eq_zero_of_re_le_rpow hk hA hρ0 hρ hre
  have hkc : ∀ z, k z = k 0 := fun z => is_const_of_deriv_eq_zero hk hd z 0
  refine ⟨(∏ u ∈ T, (Polynomial.X - Polynomial.C u) ^ n u) * Polynomial.C (g 0), fun z => ?_⟩
  rw [hfg z, hgk z, hkc z, ← hgk 0]
  simp [Polynomial.eval_prod]

end Complex
