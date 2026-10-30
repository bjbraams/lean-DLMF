/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.NumberTheory.EulerPolynomials
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Boole's summation formula

The alternating analogue of the Euler–Maclaurin formula (Temme, *Special Functions*,
§1.2.2; DLMF 24.17.1 with `h = 0`): for `f : ℝ → E` of class `Cᵐ`, `m ≥ 1`,

`2 ∑_{k<n} (-1)ᵏ f(k) = ∑_{j<m} cⱼ (f⁽ʲ⁾(0) - (-1)ⁿ f⁽ʲ⁾(n))
  + (-1)ᵐ/(m-1)! ∫₀ⁿ Ẽ_{m-1}(x) f⁽ᵐ⁾(x) dx`,

with `c₀ = 1`, `cⱼ = (-1)^{j+1} Eⱼ(0)/j!` for `j ≥ 1`, and the antiperiodic Euler function
`Ẽₖ(x) = (-1)^{⌊x⌋} Eₖ(x - ⌊x⌋)`. Since `Eⱼ(0) = 0` for even `j ≥ 2`, `cⱼ = Eⱼ(0)/j!`.

The proof integrates by parts on `[a, a+1]` against `Eⱼ(x - a)`, using `Eⱼ' = j Eⱼ₋₁` and
`Eⱼ(1) = -Eⱼ(0)` for `j ≥ 1`, and sums with alternating signs, which telescopes.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory Set intervalIntegral Polynomial

open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The antiperiodic Euler function `Ẽₖ(x) = (-1)^{⌊x⌋} Eₖ(x - ⌊x⌋)`. -/
@[dlmf 24.2.iii]
def antiperiodicEuler (k : ℕ) (x : ℝ) : ℝ := (-1 : ℝ) ^ ⌊x⌋ * eulerFun k (Int.fract x)

/-- Measurability of the indicated function: `Measurable (antiperiodicEuler k)`. -/
theorem measurable_antiperiodicEuler (k : ℕ) : Measurable (antiperiodicEuler k) := by
  unfold antiperiodicEuler
  have h1 : Measurable fun x : ℝ => (-1 : ℝ) ^ ⌊x⌋ :=
    (measurable_from_top (f := fun m : ℤ => (-1 : ℝ) ^ m)).comp Int.measurable_floor
  exact h1.mul ((continuous_eulerFun k).measurable.comp measurable_fract)

/-- Identity under the stated parameter and domain assumptions: `antiperiodicEuler k x = (-1 : ℝ)
^ m * eulerFun k (x - m)`. -/
theorem antiperiodicEuler_eq_of_mem_Ico {k : ℕ} {x : ℝ} {m : ℤ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    antiperiodicEuler k x = (-1 : ℝ) ^ m * eulerFun k (x - m) := by
  rw [antiperiodicEuler, Int.fract, Int.floor_eq_iff.mpr ⟨hx.1, hx.2⟩]

/-- Identity under the stated parameter and domain assumptions: `eulerFun k 1 = -eulerFun k 0`. -/
theorem eulerFun_one_eq_neg {k : ℕ} (hk : k ≠ 0) : eulerFun k 1 = -eulerFun k 0 := by
  have h := euler_eval_one_add_eval_zero k
  rw [zero_pow hk, mul_zero] at h
  have h' : (euler k).eval 1 = -(euler k).eval 0 := by linarith
  simp only [eulerFun, eval_one_map, eval_zero_map, eq_ratCast, h', Rat.cast_neg]

/-- Integration by parts against a shifted Euler polynomial:
`∫ₐ^{a+1} Eⱼ(x-a) g'(x) = Eⱼ(1) g(a+1) - Eⱼ(0) g(a) - j ∫ₐ^{a+1} Eⱼ₋₁(x-a) g(x)`. -/
theorem integral_eulerFun_sub_smul_deriv {g g' : ℝ → E} {a : ℝ} (j : ℕ)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') :
    ∫ x in a..a + 1, eulerFun j (x - a) • g' x =
      eulerFun j 1 • g (a + 1) - eulerFun j 0 • g a -
        ∫ x in a..a + 1, ((j : ℝ) * eulerFun (j - 1) (x - a)) • g x := by
  have hu : ∀ x, HasDerivAt (fun y => eulerFun j (y - a)) ((j : ℝ) * eulerFun (j - 1) (x - a))
      x := fun x => by
    simpa [Function.comp_def] using (hasDerivAt_eulerFun j (x - a)).comp x
      ((hasDerivAt_id x).sub_const a)
  have hg0 : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have h := integral_smul_deriv_eq_deriv_smul_of_hasDerivAt (a := a) (b := a + 1)
    (u := fun y => eulerFun j (y - a))
    ((continuous_eulerFun j).comp (continuous_id.sub continuous_const)).continuousOn
    hg0.continuousOn (fun x _ => hu x) (fun x _ => hg x)
    ((continuous_const.mul ((continuous_eulerFun _).comp
      (continuous_id.sub continuous_const))).intervalIntegrable _ _)
    (hg'.intervalIntegrable _ _)
  simpa only [add_sub_cancel_left, sub_self] using h

/-- The one-interval Boole identity, for `f` of class `Cᵐ`, `m ≥ 1`:
`2 f(a) = ∑_{j<m} cⱼ (f⁽ʲ⁾(a) + f⁽ʲ⁾(a+1)) + (-1)ᵐ/(m-1)! ∫ₐ^{a+1} E_{m-1}(x-a) f⁽ᵐ⁾(x) dx`. -/
theorem two_smul_eq_sum_eulerFun_add {f : ℝ → E} (a : ℝ) {m : ℕ} (hm : 1 ≤ m)
    (hf : ContDiff ℝ m f) :
    (2 : ℝ) • f a =
      ∑ j ∈ range m, (if j = 0 then (1 : ℝ) else (-1) ^ (j + 1) * eulerFun j 0 / j !) •
        (iteratedDeriv j f a + iteratedDeriv j f (a + 1)) +
      ((-1 : ℝ) ^ m / (m - 1)!) •
        ∫ x in a..a + 1, eulerFun (m - 1) (x - a) • iteratedDeriv m f x := by
  induction m, hm using Nat.le_induction with
  | base =>
    have hd : ∀ x, HasDerivAt f (iteratedDeriv 1 f x) x := by
      intro x
      rw [iteratedDeriv_one]
      exact ((hf.differentiable (by norm_num)) x).hasDerivAt
    have hint := integral_eq_sub_of_hasDerivAt (a := a) (b := a + 1) (fun x _ => hd x)
      ((hf.continuous_iteratedDeriv 1 le_rfl).intervalIntegrable _ _)
    simp only [Finset.range_one, sum_singleton, ↓reduceIte, one_smul, iteratedDeriv_zero, pow_one,
      Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one, eulerFun]
    simp only [euler_zero, Polynomial.map_one, eval_one, one_smul]
    rw [hint]
    module
  | succ m hm ih =>
    have hfm : ContDiff ℝ m f := hf.of_le (by exact_mod_cast Nat.le_succ m)
    have hderiv : ∀ x, HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f x) x := by
      intro x
      rw [iteratedDeriv_succ]
      exact ((hf.differentiable_iteratedDeriv m (by exact_mod_cast Nat.lt_succ_self m))
        x).hasDerivAt
    have hcont : Continuous (iteratedDeriv (m + 1) f) := hf.continuous_iteratedDeriv _ le_rfl
    -- `∫ E_m (x-a) f^{(m+1)} = E_m(1) f^{(m)}(a+1) - E_m(0) f^{(m)}(a) - m ∫ E_{m-1}(x-a) f^{(m)}`
    have hibp := integral_eulerFun_sub_smul_deriv (a := a) m hderiv hcont
    have hm0 : m ≠ 0 := by omega
    rw [eulerFun_one_eq_neg hm0] at hibp
    have hscale : ∫ x in a..a + 1, ((m : ℝ) * eulerFun (m - 1) (x - a)) • iteratedDeriv m f x =
        (m : ℝ) • ∫ x in a..a + 1, eulerFun (m - 1) (x - a) • iteratedDeriv m f x := by
      rw [← intervalIntegral.integral_smul]
      exact intervalIntegral.integral_congr fun x _ => by simp only [smul_smul]
    rw [hscale] at hibp
    rw [ih hfm, sum_range_succ, ite_eq_right_of_eq_false _ _ (eq_false hm0), Nat.add_sub_cancel,
      add_assoc]
    congr 1
    -- solve `hibp` for the `(m-1)`-integral
    have hfac : (m ! : ℝ) = m * (m - 1)! := by
      rw [← Nat.mul_factorial_pred hm0]; push_cast; ring
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    have hf1 : ((m - 1)! : ℝ) ≠ 0 := by positivity
    have hint_eq : ∫ x in a..a + 1, eulerFun (m - 1) (x - a) • iteratedDeriv m f x =
        (m : ℝ)⁻¹ • (-eulerFun m 0 • iteratedDeriv m f (a + 1) -
          eulerFun m 0 • iteratedDeriv m f a -
          ∫ x in a..a + 1, eulerFun m (x - a) • iteratedDeriv (m + 1) f x) := by
      rw [eq_inv_smul_iff₀ hmR]
      rw [hibp]
      abel
    rw [hint_eq, smul_smul]
    simp only [smul_sub, smul_add, smul_smul, neg_smul, smul_neg]
    rw [hfac, pow_succ]
    have e1 : (-1 : ℝ) ^ m / (m - 1)! * (m : ℝ)⁻¹ * eulerFun m 0 =
        -((-1) ^ (m + 1) * eulerFun m 0 / ((m : ℝ) * (m - 1)!)) := by
      first | (field_simp; done) | (field_simp; ring)
    have e2 : (-1 : ℝ) ^ m / (m - 1)! * (m : ℝ)⁻¹ = -((-1) ^ m * -1 / ((m : ℝ) * (m - 1)!)) := by
      field_simp
    rw [e1, e2]
    module

/-- **Boole's summation formula.** -/
theorem two_smul_sum_range_neg_one_pow_smul {f : ℝ → E} {m : ℕ} (hm : 1 ≤ m)
    (hf : ContDiff ℝ m f) (n : ℕ) :
    (2 : ℝ) • ∑ k ∈ range n, (-1 : ℝ) ^ k • f k =
      ∑ j ∈ range m, (if j = 0 then (1 : ℝ) else (-1) ^ (j + 1) * eulerFun j 0 / j !) •
        (iteratedDeriv j f 0 - (-1 : ℝ) ^ n • iteratedDeriv j f n) +
      ((-1 : ℝ) ^ m / (m - 1)!) •
        ∫ x in (0 : ℝ)..n, antiperiodicEuler (m - 1) x • iteratedDeriv m f x := by
  have hR : Continuous (iteratedDeriv m f) := hf.continuous_iteratedDeriv _ le_rfl
  have hRint : ∀ a b : ℝ, IntervalIntegrable (fun x => antiperiodicEuler (m - 1) x •
      iteratedDeriv m f x) volume a b := by
    intro a b
    obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ Icc (0 : ℝ) 1, ‖eulerFun (m - 1) y‖ ≤ M :=
      IsCompact.exists_bound_of_continuousOn isCompact_Icc (continuous_eulerFun _).continuousOn
    have hb : ∀ s : Set ℝ, IntegrableOn (iteratedDeriv m f) s →
        IntegrableOn (fun x => antiperiodicEuler (m - 1) x • iteratedDeriv m f x) s :=
      fun s hs => hs.bdd_smul M (measurable_antiperiodicEuler _).aestronglyMeasurable
        (ae_of_all _ fun y => by
          rw [antiperiodicEuler, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
          exact hM _ ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩)
    exact ⟨hb _ (hR.intervalIntegrable a b).1, hb _ (hR.intervalIntegrable a b).2⟩
  -- the integral over `[k, k+1]`
  have hpiece : ∀ k : ℕ, ∫ x in (k : ℝ)..(k + 1 : ℕ), antiperiodicEuler (m - 1) x •
      iteratedDeriv m f x =
      (-1 : ℝ) ^ k • ∫ x in (k : ℝ)..(k : ℝ) + 1, eulerFun (m - 1) (x - k) •
        iteratedDeriv m f x := by
    intro k
    rw [← intervalIntegral.integral_smul]
    push_cast
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume ((k : ℝ) + 1)] with x hx hxI
    rw [uIoc_of_le (by linarith)] at hxI
    rw [antiperiodicEuler_eq_of_mem_Ico (m := (k : ℤ)) (by
      push_cast; exact ⟨hxI.1.le, lt_of_le_of_ne hxI.2 hx⟩), smul_smul]
    push_cast
    rfl
  have hsplit := sum_integral_adjacent_intervals (μ := volume)
    (f := fun x => antiperiodicEuler (m - 1) x • iteratedDeriv m f x) (a := fun k : ℕ => (k : ℝ))
    (n := n) fun k _ => hRint _ _
  simp only [Nat.cast_zero] at hsplit
  rw [← hsplit, sum_congr rfl fun k _ => hpiece k, smul_sum, smul_sum]
  -- apply the one-interval identity at each `k`
  have hk : ∀ k ∈ range n, (2 : ℝ) • ((-1 : ℝ) ^ k • f k) =
      ∑ j ∈ range m, (if j = 0 then (1 : ℝ) else (-1) ^ (j + 1) * eulerFun j 0 / j !) •
        ((-1 : ℝ) ^ k • (iteratedDeriv j f k + iteratedDeriv j f (k + 1))) +
      ((-1 : ℝ) ^ m / (m - 1)!) • ((-1 : ℝ) ^ k • ∫ x in (k : ℝ)..(k : ℝ) + 1,
        eulerFun (m - 1) (x - k) • iteratedDeriv m f x) := by
    intro k _
    rw [smul_comm, two_smul_eq_sum_eulerFun_add (k : ℝ) hm hf, smul_add, smul_sum]
    congr 1
    · exact sum_congr rfl fun j _ => smul_comm _ _ _
    · exact smul_comm _ _ _
  rw [sum_congr rfl hk, sum_add_distrib, sum_comm]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [← smul_sum]
  congr 1
  -- telescoping
  clear hk hpiece hsplit
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    rw [pow_succ]
    simp only [smul_add, neg_smul, mul_neg, mul_one]
    abel
