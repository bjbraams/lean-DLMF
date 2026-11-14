/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Riemann–Lebesgue limits for uniformly convergent improper cutoffs

Olver, *Asymptotics and Special Functions*, Chapter 3, Theorem 4.1,
pp. 73–74, synopsis O-3.03. A finite family of intervals allows independent
excision of both endpoints and every interior improper point.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Complex
open scoped Topology

namespace Complex

/-- Uniform ordinary-improper convergence at finitely many endpoints preserves the
Riemann–Lebesgue limit. Olver, Chapter 3, Theorem 4.1, synopsis O-3.03.
No absolute integrability of the full improper amplitude is imposed. -/
theorem tendsto_zero_of_uniform_improper_fourier_cutoffs {ι : Type*}
    {l : Filter ι} [l.NeBot] {m : ℕ} {a b : ι → Fin m → ℝ}
    {q : ℝ → ℂ} {F : ℝ → ℂ} {X : ℝ}
    (hi : ∀ i j, IntervalIntegrable q volume (a i j) (b i j))
    (hlim : TendstoUniformlyOn (fun i (x : ℝ) => ∑ j : Fin m,
      ∫ t in a i j..b i j, exp (I * x * t) * q t) F l {x | X ≤ |x|}) :
    Tendsto F (atTop ⊔ atBot) (𝓝 0) := by
  sorry

end Complex
