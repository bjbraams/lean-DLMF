/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Digamma

/-!
# Integrals of `log Γ` and `ψ` (AAR §1.6)

The integrated form of the digamma series is the identity
`∫_1^x ψ(t) dt = log Γ(x)`, which is the fundamental theorem of calculus for
`log ∘ Γ` on `(0,∞)`. This is the source of AAR Theorem 1.6.2.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral

open scoped Real

noncomputable section

namespace Real

theorem uIcc_subset_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : uIcc a b ⊆ Ioi (0 : ℝ) := by
  intro x hx
  exact (lt_min ha hb).trans_le hx.1

theorem continuousOn_digamma : ContinuousOn digamma (Ioi 0) :=
  fun _ hx => (hasDerivAt_digamma hx).continuousAt.continuousWithinAt

theorem intervalIntegrable_digamma {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable digamma volume a b :=
  (continuousOn_digamma.mono (uIcc_subset_Ioi ha hb)).intervalIntegrable

/-- Integrating the digamma function recovers `log Γ`, AAR Theorem 1.6.2 (integrated form). -/
theorem intervalIntegral_digamma {x : ℝ} (hx : 0 < x) :
    ∫ t in (1 : ℝ)..x, digamma t = log (Gamma x) := by
  have h1 : (0 : ℝ) < 1 := one_pos
  have hderiv : ∀ t ∈ uIcc (1 : ℝ) x, HasDerivAt (fun y : ℝ => log (Gamma y)) (digamma t) t :=
    fun t ht => hasDerivAt_log_Gamma (uIcc_subset_Ioi h1 hx ht)
  simpa [Gamma_one, log_one] using
    integral_eq_sub_of_hasDerivAt hderiv (intervalIntegrable_digamma h1 hx)

end Real
