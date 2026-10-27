/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Basics.Defs
public import DLMF.AsymptoticApproximations.Integrals.Watson
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Integration by parts (DLMF §2.3(i))

* 2.3.2: the Laplace transform of a function smooth at the origin has the expansion
  `∑ q^{(s)}(0)/x^{s+1}`; proved from the general Watson lemma of
  `DLMF.AsymptoticApproximations.Integrals.Watson` and Taylor's theorem.
* 2.3.3: the error bound `|q^{(n)}(0)/(xⁿ(x - σₙ))|`.
* 2.3.4–2.3.6: Fourier integrals over finite and infinite intervals, with the error bound
  `x⁻ⁿ 𝒱_{a,b}(q^{(n-1)})` in terms of the variational operator 2.3.6.

Smoothness "in a neighbourhood of the origin" is smoothness on some `[0, r]`, `r > 0` (only
`t ≥ 0` enters the Laplace transform), with one-sided derivatives `iteratedDerivWithin`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology Real ContDiff Nat

namespace DLMF.AsymptoticApproximations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- DLMF 2.3.2: if the Laplace transform 2.3.1 converges for large `x` (here `e^{-ct} q(t)` is
integrable on `(0, ∞)`) and `q` is infinitely differentiable on `[0, r]`, `r > 0`, then
`∫₀^∞ e^{-xt} q(t) dt ∼ ∑ q^{(s)}(0)/x^{s+1}` as `x → +∞` (one-sided derivatives at `0`). -/
@[dlmf 2.3.E2]
theorem laplace_hasAsymptoticExpansion_of_contDiffOn {q : ℝ → E} {c r : ℝ} (hr : 0 < r)
    (hq : ContDiffOn ℝ ∞ q (Icc 0 r))
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • q t) (Ioi 0)) :
    HasAsymptoticExpansion atTop (fun (s : ℕ) (x : ℝ) => x ^ (-((s : ℝ) + 1)))
      (fun s => iteratedDerivWithin s q (Icc 0 r) 0)
      (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • q t) := by
  set d : ℕ → E := fun s => iteratedDerivWithin s q (Icc 0 r) 0 with hd
  have hmem : Ioo (0 : ℝ) r ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hr
  have hT : ∀ N : ℕ, (fun t => q t - ∑ n ∈ range N, t ^ (((n : ℝ) + 1) - 1) •
      (((n ! : ℝ)⁻¹) • d n)) =O[𝓝[>] 0] fun t => t ^ (((N : ℝ) + 1) - 1) := by
    intro N
    rcases N with _ | n
    · obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hq.continuousOn
      refine IsBigO.of_bound C ?_
      filter_upwards [hmem] with t ht
      simpa using hC t (Ioo_subset_Icc_self ht)
    · have hcont : ContinuousOn (iteratedDerivWithin (n + 1) q (Icc 0 r)) (Icc 0 r) :=
        hq.continuousOn_iteratedDerivWithin (mod_cast le_top) (uniqueDiffOn_Icc hr)
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      refine IsBigO.of_bound (C / n !) ?_
      filter_upwards [hmem] with t ht
      have ht' : t ∈ Icc 0 r := Ioo_subset_Icc_self ht
      have hb := taylor_mean_remainder_bound hr.le (hq.of_le (mod_cast le_top)) ht' hC
      have heq : taylorWithinEval q n (Icc 0 r) 0 t = ∑ k ∈ range (n + 1),
          t ^ (((k : ℝ) + 1) - 1) • (((k ! : ℝ)⁻¹) • d k) := by
        rw [taylor_within_apply]
        refine sum_congr rfl fun k _ => ?_
        rw [smul_smul, add_sub_cancel_right, Real.rpow_natCast, sub_zero, mul_comm]
      rw [← heq]
      have h0 : 0 ≤ t := ht'.1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _), Nat.cast_add, Nat.cast_one,
        add_sub_cancel_right, ← Nat.cast_succ, Real.rpow_natCast]
      calc _ ≤ C * (t - 0) ^ (n + 1) / n ! := hb
        _ = C / n ! * t ^ (n + 1) := by rw [sub_zero]; ring
  have h := hasAsymptoticExpansion_integral_exp_smul_rpow_seq (e := fun s => (s : ℝ) + 1)
    (a := fun s => ((s ! : ℝ)⁻¹) • d s) (fun n => by positivity) hint hT
  refine h.congr_coeff (funext fun s => ?_)
  rw [smul_smul, Real.Gamma_nat_eq_factorial, mul_inv_cancel₀ (by positivity), one_smul]

/-- DLMF 2.3.3 and the bound after it: let `q` be infinitely differentiable on `[0, ∞)` with
`q^{(n)}(0) ≠ 0`, and let `σ` bound `t⁻¹ ln|q^{(n)}(t)/q^{(n)}(0)|` on `(0, ∞)`, that is,
`|q^{(n)}(t)| ≤ |q^{(n)}(0)| e^{σt}` (DLMF's `σₙ` of 2.3.3 is the least such `σ`). Then for
`x > max(0, σ)` the `n`th error term of 2.3.2 is bounded by `|q^{(n)}(0)/(xⁿ(x - σ))|`. -/
@[dlmf 2.3.E3, dlmf 2.3.i]
theorem laplace_error_bound {q : ℝ → ℂ} {n : ℕ} {σ x : ℝ} (hq : ContDiffOn ℝ ∞ q (Ici 0))
    (hn : iteratedDerivWithin n q (Ici 0) 0 ≠ 0)
    (hσ : ∀ t, 0 < t →
      ‖iteratedDerivWithin n q (Ici 0) t‖ ≤ ‖iteratedDerivWithin n q (Ici 0) 0‖ * Real.exp (σ * t))
    (hx0 : 0 < x) (hxσ : σ < x) :
    ‖(∫ t in Ioi (0 : ℝ), Complex.exp (-(x * t)) * q t) -
        ∑ s ∈ range n, iteratedDerivWithin s q (Ici 0) 0 / (x : ℂ) ^ (s + 1)‖ ≤
      ‖iteratedDerivWithin n q (Ici 0) 0‖ / (x ^ n * (x - σ)) := by
  sorry

/-- DLMF 2.3.4 (finite Fourier integral): if `q` is infinitely differentiable on `[a, b]`, then
`∫ₐᵇ e^{ixt} q(t) dt ∼ e^{iax} ∑ q^{(s)}(a)(i/x)^{s+1} - e^{ibx} ∑ q^{(s)}(b)(i/x)^{s+1}` as
`x → +∞`, a generalized asymptotic expansion with respect to the scale `x^{-s-1}`
(one-sided derivatives at the endpoints). -/
@[dlmf 2.3.E4]
theorem fourier_hasGeneralizedAsymptoticExpansion {q : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hq : ContDiffOn ℝ ∞ q (Icc a b)) :
    HasGeneralizedAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + 1)))
      (fun s x => (Complex.exp (I * a * x) * iteratedDerivWithin s q (Icc a b) a -
        Complex.exp (I * b * x) * iteratedDerivWithin s q (Icc a b) b) * (I / x) ^ (s + 1))
      (fun x => ∫ t in a..b, Complex.exp (I * x * t) * q t) := by
  sorry

/-- DLMF 2.3.4 with the error bound after 2.3.6: for `n ≥ 1` and `x > 0` the `n`th error term
of 2.3.4 is bounded in absolute value by `x⁻ⁿ 𝒱_{a,b}(q^{(n-1)})`, with the variational operator
2.3.6. -/
@[dlmf 2.3.E4, dlmf 2.3.E6, dlmf 2.3.i]
theorem fourier_error_bound {q : ℝ → ℂ} {a b x : ℝ} {n : ℕ} (hab : a < b)
    (hq : ContDiffOn ℝ ∞ q (Icc a b)) (hn : 1 ≤ n) (hx : 0 < x) :
    ‖(∫ t in a..b, Complex.exp (I * x * t) * q t) - ∑ s ∈ range n,
        (Complex.exp (I * a * x) * iteratedDerivWithin s q (Icc a b) a -
          Complex.exp (I * b * x) * iteratedDerivWithin s q (Icc a b) b) * (I / x) ^ (s + 1)‖ ≤
      x ^ (-(n : ℤ)) * variationalOperator a b (iteratedDerivWithin (n - 1) q (Icc a b)) := by
  sorry

/-- DLMF 2.3.5 (infinite Fourier integral): if `q` is infinitely differentiable on `[a, ∞)` and
each integral `∫ₐ^∞ e^{ixt} q^{(s)}(t) dt` converges (as `lim_{T→∞} ∫ₐᵀ`) uniformly for
`x ≥ x₀`, then the improper integral `I(x) = ∫ₐ^∞ e^{ixt} q(t) dt` satisfies
`I(x) ∼ e^{iax} ∑ q^{(s)}(a)(i/x)^{s+1}` as `x → +∞` (generalized expansion, scale `x^{-s-1}`),
and for `n ≥ 1`, `x ≥ max(x₀, 0)`, `x > 0`, the `n`th error term is at most
`x⁻ⁿ ∫ₐ^∞ |q^{(n)}(t)| dt` (`= x⁻ⁿ 𝒱_{a,∞}(q^{(n-1)})`) when that integral is finite. -/
@[dlmf 2.3.E5, dlmf 2.3.i]
theorem fourier_Ioi_hasGeneralizedAsymptoticExpansion {q : ℝ → ℂ} {a x₀ : ℝ}
    (hq : ContDiffOn ℝ ∞ q (Ici a)) {I₀ : ℝ → ℂ} {L : ℕ → ℝ → ℂ}
    (hunif : ∀ s : ℕ, TendstoUniformlyOn (fun (T x : ℝ) =>
      ∫ t in a..T, Complex.exp (I * x * t) * iteratedDerivWithin s q (Ici a) t) (L s) atTop
      (Ici x₀))
    (hI : ∀ x, x₀ ≤ x → I₀ x = L 0 x) :
    HasGeneralizedAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + 1)))
      (fun s x => Complex.exp (I * a * x) * iteratedDerivWithin s q (Ici a) a * (I / x) ^ (s + 1))
      I₀ ∧
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, x₀ ≤ x → 0 < x →
      IntegrableOn (iteratedDerivWithin n q (Ici a)) (Ioi a) →
      ‖I₀ x - ∑ s ∈ range n,
          Complex.exp (I * a * x) * iteratedDerivWithin s q (Ici a) a * (I / x) ^ (s + 1)‖ ≤
        x ^ (-(n : ℤ)) * ∫ t in Ioi a, ‖iteratedDerivWithin n q (Ici a) t‖ := by
  sorry

end DLMF.AsymptoticApproximations
