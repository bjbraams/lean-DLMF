/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonComplexKernel

/-!
# Watson kernels with a logarithmic singularity at zero

Olver, *Asymptotics and Special Functions*, Chapter 9, Lemma 6.1
and §6, pp. 337–339, synopses O-9.07–O-9.08. The logarithmic weight
admits the Macdonald kernel K_0, unlike a globally bounded-kernel hypothesis.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace Complex

/-- A logarithmically singular, exponentially decaying kernel preserves ramified
power expansions. Olver, Chapter 9, Lemma 6.1 and §6, pp. 337–339. -/
theorem isBigO_integral_log_singular_kernel_sub_sum
    {g f : ℝ → ℂ} {a : ℕ → ℂ} {lam mu A b c κ : ℝ}
    (hlam : 0 < lam) (hmu : 0 < mu) (hA : 0 < A) (hb : 0 < b)
    (hc : 0 < c) (hκ : 0 < κ)
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hg : ∀ t > 0, ‖g t‖ ≤ A * (1 + |Real.log t|) * Real.exp (-b * t ^ κ))
    (hlocal : LocallyIntegrableOn f (Ioi 0))
    (hfar : f =O[atTop] (fun v : ℝ => Real.exp (c * v ^ κ)))
    (hexp : ∀ N : ℕ, (fun v => f v - ∑ s ∈ Finset.range N,
      (v : ℂ) ^ ((((s : ℝ) + lam) / mu - 1 : ℝ) : ℂ) * a s) =O[𝓝[>] 0]
        (fun v : ℝ => v ^ (((N : ℝ) + lam) / mu - 1))) (N : ℕ) :
    (fun x : ℝ => (∫ v in Ioi (0 : ℝ), g (x * v) * f v) -
      ∑ s ∈ Finset.range N,
        mellin g (((s : ℝ) + lam) / mu) * a s *
          (x : ℂ) ^ (-(((s : ℝ) + lam) / mu : ℝ) : ℂ)) =O[atTop]
      (fun x : ℝ => x ^ (-((N : ℝ) + lam) / mu)) := by
  sorry

end Complex
