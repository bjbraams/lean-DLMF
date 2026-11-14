/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Zeros.RealAndAi
public import DLMF.AsymptoticApproximations.ODE.AiryEnvelopes

/-!
# Real Airy signs, monotonicity and transition-point interlacing

Positive-axis signs follow from the already established initial values and absence
of nonnegative zeros. The zero chains retain the largest negative crossing of
`Ai=Bi`. Source: Olver, *Asymptotics and Special Functions*, Chapter 11,
§1, pp. 392–394, and Lemma 5.1, pp. 403–405.
-/

@[expose] public noncomputable section

open Set
open scoped Real

namespace DLMF.Airy.Real

/-- The Airy derivative is strictly negative on the nonnegative real axis.
Olver, Chapter 11, §1, pp. 392–393. -/
theorem airyAiDeriv_neg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : airyAiDeriv x < 0 := by
  by_contra hn
  have hc : Continuous airyAiDeriv := continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_airyAiDeriv t).continuousAt
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hx hc.continuousOn
    (show 0 ∈ Icc (airyAiDeriv 0) (airyAiDeriv x) from
      ⟨airyAiDeriv_zero_lt.le, le_of_not_gt hn⟩)
  have hneg := DLMF.Airy.airyAiDeriv_real_zeros_negative heq
  linarith [ht.1]

/-- The derivative of `Bi` is positive on the nonnegative real axis.
Olver, Chapter 11, §1, pp. 392–393. -/
theorem airyBiDeriv_pos_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 < airyBiDeriv x := by
  by_contra hn
  have hc : Continuous airyBiDeriv := continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_airyBiDeriv t).continuousAt
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hx hc.continuousOn
    (show 0 ∈ Icc (airyBiDeriv x) (airyBiDeriv 0) from
      ⟨le_of_not_gt hn, airyBiDeriv_zero_pos.le⟩)
  have hneg := DLMF.Airy.airyBiDeriv_real_zeros_negative heq
  linarith [ht.1]

/-- `Ai` strictly decreases on the positive real axis, including zero.
Olver, Chapter 11, §1, p. 393. -/
theorem strictAntiOn_airyAi_nonneg : StrictAntiOn airyAi (Ici 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 0)
    (fun x _ => (hasDerivAt_airyAi x).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [(hasDerivAt_airyAi x).deriv]
  exact airyAiDeriv_neg_of_nonneg (le_of_lt (by simpa only [interior_Ici, mem_Ioi] using hx))

/-- `Ai'` strictly increases towards zero, equivalently `-Ai'` strictly decreases.
Olver, Chapter 11, §1, p. 393. -/
theorem strictMonoOn_airyAiDeriv_nonneg : StrictMonoOn airyAiDeriv (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun x _ => (hasDerivAt_airyAiDeriv x).continuousAt.continuousWithinAt) ?_
  intro x hx
  have hxpos : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  rw [(hasDerivAt_airyAiDeriv x).deriv]
  exact mul_pos hxpos (airyAi_pos hxpos.le)

/-- `Bi` strictly increases on the nonnegative real axis.
Olver, Chapter 11, §1, p. 393. -/
theorem strictMonoOn_airyBi_nonneg : StrictMonoOn airyBi (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun x _ => (hasDerivAt_airyBi x).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [(hasDerivAt_airyBi x).deriv]
  exact airyBiDeriv_pos_of_nonneg (le_of_lt (by simpa only [interior_Ici, mem_Ioi] using hx))

/-- `Bi'` strictly increases on the nonnegative real axis.
Olver, Chapter 11, §1, p. 393. -/
theorem strictMonoOn_airyBiDeriv_nonneg : StrictMonoOn airyBiDeriv (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun x _ => (hasDerivAt_airyBiDeriv x).continuousAt.continuousWithinAt) ?_
  intro x hx
  have hxpos : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  rw [(hasDerivAt_airyBiDeriv x).deriv]
  exact mul_pos hxpos (airyBi_pos hxpos.le)

end DLMF.Airy.Real

namespace DLMF.Airy

/-- The complete value-zero chain starts below the largest `Ai=Bi` crossing.
Olver, Chapter 11, Lemma5.1, pp. 403–405. -/
theorem real_zero_interlacing_below_transition :
    DLMF.AsymptoticApproximations.airyEnvCrit > airyBiZero 1 ∧
      ∀ n : ℕ, 1 ≤ n → airyBiZero n > airyAiZero n ∧ airyAiZero n > airyBiZero (n + 1) := by
  sorry

/-- The complete derivative-zero chain starts below the same crossing.
Olver, Chapter 11, Lemma5.1, pp. 403–405. -/
theorem real_derivative_zero_interlacing_below_transition :
    DLMF.AsymptoticApproximations.airyEnvCrit > airyAiDerivZero 1 ∧
      ∀ n : ℕ, 1 ≤ n → airyAiDerivZero n > airyBiDerivZero n ∧
        airyBiDerivZero n > airyAiDerivZero (n + 1) := by
  sorry

end DLMF.Airy
