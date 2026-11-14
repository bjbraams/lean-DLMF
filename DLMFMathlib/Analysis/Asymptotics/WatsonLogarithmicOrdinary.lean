/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonComplexLog
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Ordinary logarithmically weighted Watson expansions

Olver, *Asymptotics and Special Functions*, Chapter 9, Theorem 1.1,
pp. 323–324, synopsis O-9.01. The natural improper limit is retained;
absolute convergence is not substituted for the source's convergence hypothesis.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace Complex

/-- Watson's lemma for every nonnegative integer logarithmic power and ordinary
improper convergence. Olver, Chapter 9, Theorem 1.1, pp. 323–324. -/
theorem isBigO_laplace_log_pow_sub_sum_of_tendsto
    {f L : ℝ → ℂ} {a : ℕ → ℂ} {lam mu X : ℝ}
    (hlam : 0 < lam) (hmu : 0 < mu) (m : ℕ)
    (hlocal : LocallyIntegrableOn f (Ioi 0))
    (hexp : ∀ N : ℕ, (fun v => f v - ∑ s ∈ Finset.range N,
      (v : ℂ) ^ ((((s : ℝ) + lam) / mu - 1 : ℝ) : ℂ) * a s) =O[𝓝[>] 0]
        (fun v : ℝ => v ^ (((N : ℝ) + lam) / mu - 1)))
    (hfinite : ∀ x > X, ∀ T > 0, IntervalIntegrable
      (fun v => exp (-(x * v : ℝ)) * f v * (Real.log v : ℂ) ^ m) volume 0 T)
    (hlim : ∀ x > X, Tendsto (fun T : ℝ => ∫ v in (0 : ℝ)..T,
      exp (-(x * v : ℝ)) * f v * (Real.log v : ℂ) ^ m) atTop (𝓝 (L x))) (N : ℕ) :
    (fun x : ℝ => L x - ∑ s ∈ Finset.range N,
      a s * (x : ℂ) ^ (-(((s : ℝ) + lam) / mu : ℝ) : ℂ) *
        ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) * (-(Real.log x : ℂ)) ^ j *
          iteratedDeriv (m - j) Gamma (((s : ℝ) + lam) / mu)) =O[atTop]
      (fun x : ℝ => x ^ (-((N : ℝ) + lam) / mu) * (1 + Real.log x) ^ m) := by
  sorry

end Complex
