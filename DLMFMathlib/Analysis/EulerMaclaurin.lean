/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The Euler–Maclaurin summation formula

For `f : ℝ → E` of class `Cᵖ`, `p ≥ 1`, and `n : ℕ`,

`∑_{k=0}^{n} f(k) = ∫₀ⁿ f + (f(0) + f(n))/2
  + ∑_{j=1}^{p-1} (-1)^{j+1} B_{j+1}/(j+1)! (f⁽ʲ⁾(n) - f⁽ʲ⁾(0))
  + (-1)^{p+1}/p! ∫₀ⁿ B̃ₚ(x) f⁽ᵖ⁾(x) dx`,

where `B̃ₚ(x) = Bₚ({x})` is the periodic Bernoulli function (Temme, *Special Functions*,
§1.1.3). Since the odd Bernoulli numbers beyond `B₁` vanish, the sign `(-1)^{j+1}` may be
dropped; we keep it, as it is what the proof produces.

The proof integrates by parts on each `[a, a+1]` against `Bₚ(x - a)`, using
`Bₚ₊₁' = (p+1) Bₚ` (`integral_eq_sum_bernoulliFun_add`), and sums over the unit intervals.

## Main definitions

* `periodicBernoulli`: the periodic Bernoulli function `B̃ₚ(x) = Bₚ(x - ⌊x⌋)`.

## Main results

* `integral_eq_sum_bernoulliFun_add`: the one-interval identity.
* `sum_range_succ_eq_integral_add`: the Euler–Maclaurin formula with remainder.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory Set intervalIntegral

open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The periodic Bernoulli function `B̃ₚ(x) = Bₚ(x - ⌊x⌋)`. -/
def periodicBernoulli (p : ℕ) (x : ℝ) : ℝ := bernoulliFun p (Int.fract x)

theorem periodicBernoulli_add_intCast (p : ℕ) (x : ℝ) (m : ℤ) :
    periodicBernoulli p (x + m) = periodicBernoulli p x := by
  simp [periodicBernoulli]

theorem periodicBernoulli_eq_of_mem_Ico {p : ℕ} {x : ℝ} {m : ℤ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    periodicBernoulli p x = bernoulliFun p (x - m) := by
  rw [periodicBernoulli, Int.fract, Int.floor_eq_iff.mpr ⟨hx.1, hx.2⟩]

theorem measurable_periodicBernoulli (p : ℕ) : Measurable (periodicBernoulli p) :=
  (continuous_bernoulliFun p).measurable.comp measurable_fract

/-- The derivative of a shifted Bernoulli polynomial. -/
theorem hasDerivAt_bernoulliFun_sub (p : ℕ) (a x : ℝ) :
    HasDerivAt (fun y => bernoulliFun (p + 1) (y - a)) ((p + 1) * bernoulliFun p (x - a)) x := by
  have h := (hasDerivAt_bernoulliFun (p + 1) (x - a)).comp x ((hasDerivAt_id x).sub_const a)
  simpa [Function.comp_def] using h

/-- One step of integration by parts:
`∫ₐ^{a+1} Bₚ(x-a) g(x) = (B_{p+1}(1) g(a+1) - B_{p+1}(0) g(a) - ∫ B_{p+1}(x-a) g'(x))/(p+1)`. -/
theorem integral_bernoulliFun_sub_smul {g g' : ℝ → E} {a : ℝ} (p : ℕ)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') :
    ∫ x in a..a + 1, bernoulliFun p (x - a) • g x =
      ((p : ℝ) + 1)⁻¹ • (bernoulliFun (p + 1) 1 • g (a + 1) - bernoulliFun (p + 1) 0 • g a -
        ∫ x in a..a + 1, bernoulliFun (p + 1) (x - a) • g' x) := by
  have hu : Continuous fun y => bernoulliFun (p + 1) (y - a) :=
    (continuous_bernoulliFun _).comp (continuous_id.sub continuous_const)
  have hg0 : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have h := integral_smul_deriv_eq_deriv_smul_of_hasDerivAt (a := a) (b := a + 1)
    hu.continuousOn hg0.continuousOn (fun x _ => hasDerivAt_bernoulliFun_sub p a x)
    (fun x _ => hg x)
    ((continuous_const.mul ((continuous_bernoulliFun p).comp
      (continuous_id.sub continuous_const))).intervalIntegrable _ _)
    (hg'.intervalIntegrable _ _)
  have hp : ((p : ℝ) + 1) ≠ 0 := by positivity
  simp only [add_sub_cancel_left, sub_self] at h
  have hmul : ∫ x in a..a + 1, (((p : ℝ) + 1) * bernoulliFun p (x - a)) • g x =
      ((p : ℝ) + 1) • ∫ x in a..a + 1, bernoulliFun p (x - a) • g x := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [smul_smul]
  rw [hmul] at h
  rw [eq_inv_smul_iff₀ hp, h]
  abel

/-- The one-interval Euler–Maclaurin identity, for `f` of class `Cᵖ`:
`∫ₐ^{a+1} f = ∑_{j<p} (-1)ʲ/(j+1)! (B_{j+1}(1) f⁽ʲ⁾(a+1) - B_{j+1}(0) f⁽ʲ⁾(a))
  + (-1)ᵖ/p! ∫ₐ^{a+1} Bₚ(x-a) f⁽ᵖ⁾(x) dx`. -/
theorem integral_eq_sum_bernoulliFun_add {f : ℝ → E} (a : ℝ) (p : ℕ) (hf : ContDiff ℝ p f) :
    ∫ x in a..a + 1, f x =
      ∑ j ∈ range p, ((-1 : ℝ) ^ j / (j + 1)!) •
        (bernoulliFun (j + 1) 1 • iteratedDeriv j f (a + 1) -
          bernoulliFun (j + 1) 0 • iteratedDeriv j f a) +
      ((-1 : ℝ) ^ p / p !) • ∫ x in a..a + 1, bernoulliFun p (x - a) • iteratedDeriv p f x := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hfp : ContDiff ℝ p f := hf.of_le (by exact_mod_cast Nat.le_succ p)
    have hderiv : ∀ x, HasDerivAt (iteratedDeriv p f) (iteratedDeriv (p + 1) f x) x := by
      intro x
      rw [iteratedDeriv_succ]
      exact ((hf.differentiable_iteratedDeriv p (by exact_mod_cast Nat.lt_succ_self p))
        x).hasDerivAt
    have hcont : Continuous (iteratedDeriv (p + 1) f) := hf.continuous_iteratedDeriv _ le_rfl
    rw [ih hfp, integral_bernoulliFun_sub_smul p hderiv hcont, sum_range_succ, smul_smul,
      add_assoc]
    congr 1
    have hfac : ((p + 1)! : ℝ) = ((p : ℝ) + 1) * p ! := by push_cast [Nat.factorial_succ]; ring
    have hp : ((p : ℝ) + 1) ≠ 0 := by positivity
    have hpf : (p ! : ℝ) ≠ 0 := by positivity
    rw [smul_sub, sub_eq_add_neg, ← neg_smul]
    congr 1
    · congr 1
      rw [hfac]
      field_simp
    · congr 1
      rw [hfac, pow_succ]
      field_simp

/-- The Euler–Maclaurin summation formula with remainder. -/
theorem sum_range_succ_eq_integral_add {f : ℝ → E} {p : ℕ} (hp : 1 ≤ p) (hf : ContDiff ℝ p f)
    (n : ℕ) :
    ∑ k ∈ range (n + 1), f k =
      (∫ x in (0 : ℝ)..n, f x) + (2 : ℝ)⁻¹ • (f 0 + f n) -
        ∑ j ∈ Ico 1 p, ((-1 : ℝ) ^ j * (bernoulli (j + 1) : ℝ) / (j + 1)!) •
          (iteratedDeriv j f n - iteratedDeriv j f 0) -
        ((-1 : ℝ) ^ p / p !) • ∫ x in (0 : ℝ)..n, periodicBernoulli p x • iteratedDeriv p f x := by
  -- integrals over the unit intervals
  have hint : ∀ k : ℕ, ∫ x in (k : ℝ)..(k + 1 : ℕ), f x =
      ∑ j ∈ range p, ((-1 : ℝ) ^ j / (j + 1)!) •
        (bernoulliFun (j + 1) 1 • iteratedDeriv j f (k + 1) -
          bernoulliFun (j + 1) 0 • iteratedDeriv j f k) +
      ((-1 : ℝ) ^ p / p !) • ∫ x in (k : ℝ)..(k + 1 : ℕ), periodicBernoulli p x •
        iteratedDeriv p f x := by
    intro k
    push_cast
    rw [integral_eq_sum_bernoulliFun_add (k : ℝ) p hf]
    congr 2
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume ((k : ℝ) + 1)] with x hx hxI
    rw [uIoc_of_le (by linarith)] at hxI
    rw [periodicBernoulli_eq_of_mem_Ico (m := (k : ℤ)) (by
      push_cast; exact ⟨hxI.1.le, lt_of_le_of_ne hxI.2 hx⟩)]
    push_cast
    rfl
  have hfc : Continuous f := hf.continuous
  have hR : Continuous (iteratedDeriv p f) := hf.continuous_iteratedDeriv _ le_rfl
  have hRint : ∀ a b : ℝ, IntervalIntegrable (fun x => periodicBernoulli p x •
      iteratedDeriv p f x) volume a b := by
    intro a b
    -- `B̃ₚ` is bounded and measurable
    obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ Icc (0 : ℝ) 1, ‖bernoulliFun p y‖ ≤ M :=
      IsCompact.exists_bound_of_continuousOn isCompact_Icc
        (continuous_bernoulliFun p).continuousOn
    have hb : ∀ s : Set ℝ, IntegrableOn (iteratedDeriv p f) s →
        IntegrableOn (fun x => periodicBernoulli p x • iteratedDeriv p f x) s := fun s hs =>
      hs.bdd_smul M (measurable_periodicBernoulli p).aestronglyMeasurable
        (ae_of_all _ fun y => hM _ ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩)
    exact ⟨hb _ (hR.intervalIntegrable a b).1, hb _ (hR.intervalIntegrable a b).2⟩
  have hsplit_f := sum_integral_adjacent_intervals (μ := volume) (f := f)
    (a := fun k : ℕ => (k : ℝ))
    (n := n) fun k _ => hfc.intervalIntegrable _ _
  have hsplit_R := sum_integral_adjacent_intervals (μ := volume)
    (f := fun x => periodicBernoulli p x • iteratedDeriv p f x) (a := fun k : ℕ => (k : ℝ))
    (n := n) fun k _ => hRint _ _
  simp only [Nat.cast_zero] at hsplit_f hsplit_R
  -- the boundary terms
  set T : ℕ → ℕ → E := fun j k => ((-1 : ℝ) ^ j / (j + 1)!) •
    (bernoulliFun (j + 1) 1 • iteratedDeriv j f (k + 1) -
      bernoulliFun (j + 1) 0 • iteratedDeriv j f k) with hT
  set R := ∫ x in (0 : ℝ)..n, periodicBernoulli p x • iteratedDeriv p f x with hRdef
  have hF : ∫ x in (0 : ℝ)..n, f x =
      ∑ j ∈ range p, ∑ k ∈ range n, T j k + ((-1 : ℝ) ^ p / p !) • R := by
    rw [← hsplit_f, ← hsplit_R, sum_congr rfl fun k _ => hint k, sum_add_distrib,
      ← smul_sum, sum_comm]
  have hT0 : ∑ k ∈ range n, T 0 k = ∑ k ∈ range (n + 1), f k - (2 : ℝ)⁻¹ • (f 0 + f n) := by
    have hpt : ∀ k : ℕ, T 0 k = (2 : ℝ)⁻¹ • (f (k + 1) + f k) := by
      intro k
      simp only [hT, pow_zero, zero_add, Nat.factorial_one, Nat.cast_one, div_one, one_smul,
        iteratedDeriv_zero, bernoulliFun_one]
      module
    simp only [hpt]
    clear hint hsplit_f hsplit_R hF hRdef
    induction n with
    | zero => simp; module
    | succ n ih =>
      rw [sum_range_succ, ih, sum_range_succ (n := n + 1)]
      push_cast
      module
  have hTj : ∀ j ∈ Finset.Ico 1 p, ∑ k ∈ range n, T j k =
      ((-1 : ℝ) ^ j * (bernoulli (j + 1) : ℝ) / (j + 1)!) •
        (iteratedDeriv j f n - iteratedDeriv j f 0) := by
    intro j hj
    have hj1 : j + 1 ≠ 1 := by simp at hj; omega
    have hpt : ∀ k : ℕ, T j k = ((-1 : ℝ) ^ j * (bernoulli (j + 1) : ℝ) / (j + 1)!) •
        (iteratedDeriv j f ((k + 1 : ℕ) : ℝ) - iteratedDeriv j f (k : ℝ)) := by
      intro k
      simp only [hT, bernoulliFun_endpoints_eq_of_ne_one hj1, bernoulliFun_eval_zero,
        ← smul_sub, smul_smul]
      push_cast
      congr 1
      ring
    simp only [hpt, ← smul_sum]
    rw [sum_range_sub (fun k : ℕ => iteratedDeriv j f (k : ℝ)) n]
    simp
  have hsplit : ∑ j ∈ range p, ∑ k ∈ range n, T j k =
      ∑ k ∈ range n, T 0 k + ∑ j ∈ Finset.Ico 1 p, ∑ k ∈ range n, T j k := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  rw [hF, hsplit, hT0, sum_congr rfl hTj]
  abel
