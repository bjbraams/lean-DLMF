/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Basic
public import DLMF.Airy.Basic.ModulusPhase
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Weighted real Airy envelopes

The transition point is the existing canonical `airyEnvCrit`. These weighted
moduli differ from the unweighted DLMF Chapter 9 modulus on the positive side.
The phases are actual normalized functions and the error constants are actual
suprema, without replacing them by numerical approximations. Source:
Olver, *Asymptotics and Special Functions*, Chapter 11, §2, pp. 394–397.
-/

@[expose] public noncomputable section

open Filter Set
open DLMF.Airy
open scoped Real Topology Asymptotics

namespace DLMF.AsymptoticApproximations.Real.AiryEnvelope

/-- Olver's Airy weight `E`, with transition at the largest root `Ai=Bi`.
Olver, Chapter 11, §2, pp. 394–395. -/
def weight (x : ℝ) : ℝ :=
  if x ≤ airyEnvCrit then 1 else Real.sqrt (Airy.Real.airyBi x / Airy.Real.airyAi x)

/-- The two defining branches of the Airy weight. -/
theorem weight_def (x : ℝ) : weight x =
    if x ≤ airyEnvCrit then 1 else Real.sqrt (Airy.Real.airyBi x / Airy.Real.airyAi x) := rfl

/-- The oscillatory branch of the weight is one. -/
theorem weight_of_le {x : ℝ} (hx : x ≤ airyEnvCrit) : weight x = 1 := by
  simp [weight, hx]

/-- The exponential branch of the weight balances Ai and Bi. -/
theorem weight_of_gt {x : ℝ} (hx : airyEnvCrit < x) :
    weight x = Real.sqrt (Airy.Real.airyBi x / Airy.Real.airyAi x) := by
  simp [weight, hx.not_ge]

/-- The weighted Airy modulus `M`. Olver, Chapter 11, §2, p. 395. -/
def modulus (x : ℝ) : ℝ :=
  Real.sqrt ((weight x * Airy.Real.airyAi x) ^ 2 + (Airy.Real.airyBi x / weight x) ^ 2)

/-- The defining weighted sum of squares for `M`. -/
theorem modulus_def (x : ℝ) : modulus x =
    Real.sqrt ((weight x * Airy.Real.airyAi x) ^ 2 +
      (Airy.Real.airyBi x / weight x) ^ 2) := rfl

/-- The weighted derivative modulus `N`. Olver, Chapter 11, §2, p. 395. -/
def derivativeModulus (x : ℝ) : ℝ :=
  Real.sqrt ((weight x * Airy.Real.airyAiDeriv x) ^ 2 +
    (Airy.Real.airyBiDeriv x / weight x) ^ 2)

/-- The defining weighted derivative sum of squares. -/
theorem derivativeModulus_def (x : ℝ) : derivativeModulus x =
    Real.sqrt ((weight x * Airy.Real.airyAiDeriv x) ^ 2 +
      (Airy.Real.airyBiDeriv x / weight x) ^ 2) := rfl

/-- The continuous Airy phase with value `pi/4` at the transition point.
To its right the two weighted function values agree. Olver, Chapter 11, §2, p. 395. -/
def phase (x : ℝ) : ℝ := if x ≤ airyEnvCrit then airyPhase x else Real.pi / 4

/-- The defining normalized phase branches. -/
theorem phase_def (x : ℝ) : phase x =
    if x ≤ airyEnvCrit then airyPhase x else Real.pi / 4 := rfl

/-- The continuous weighted derivative phase. On the exponential side the vector
lies in the fourth quadrant, so its principal argument supplies the branch whose
limit is `-pi/4`. Olver, Chapter 11, §2, p. 395. -/
def derivativePhase (x : ℝ) : ℝ :=
  if x ≤ airyEnvCrit then airyDerivPhase x else
    Complex.arg ((Airy.Real.airyBiDeriv x / weight x : ℝ) +
      Complex.I * (weight x * Airy.Real.airyAiDeriv x : ℝ))

/-- The defining derivative-phase branches. -/
theorem derivativePhase_def (x : ℝ) : derivativePhase x =
    if x ≤ airyEnvCrit then airyDerivPhase x else
      Complex.arg ((Airy.Real.airyBiDeriv x / weight x : ℝ) +
        Complex.I * (weight x * Airy.Real.airyAiDeriv x : ℝ)) := rfl

/-- The Airy error constant `Lambda` is a supremum, with no numerical approximation.
Olver, Chapter 11, §2, p. 396. -/
def errorConstant : ℝ := sSup (range fun x : ℝ => Real.pi * |x| ^ (1 / 2 : ℝ) * modulus x ^ 2)

/-- The defining supremum of `Lambda`. -/
theorem errorConstant_def : errorConstant =
    sSup (range fun x : ℝ => Real.pi * |x| ^ (1 / 2 : ℝ) * modulus x ^ 2) := rfl

/-- The Ai-specific error constant `mu_1`. Olver, Chapter 11, §2, p. 396. -/
def aiErrorConstant : ℝ := sSup (range fun x : ℝ =>
  Real.pi * weight x * modulus x * |x| ^ (1 / 2 : ℝ) * |Airy.Real.airyAi x|)

/-- The defining supremum of `mu_1`. -/
theorem aiErrorConstant_def : aiErrorConstant = sSup (range fun x : ℝ =>
    Real.pi * weight x * modulus x * |x| ^ (1 / 2 : ℝ) * |Airy.Real.airyAi x|) := rfl

/-- The Bi-specific error constant `mu_2`. Olver, Chapter 11, §2, p. 396. -/
def biErrorConstant : ℝ := sSup (range fun x : ℝ =>
  Real.pi / weight x * modulus x * |x| ^ (1 / 2 : ℝ) * |Airy.Real.airyBi x|)

/-- The defining supremum of `mu_2`. -/
theorem biErrorConstant_def : biErrorConstant = sSup (range fun x : ℝ =>
    Real.pi / weight x * modulus x * |x| ^ (1 / 2 : ℝ) * |Airy.Real.airyBi x|) := rfl

/-- The transition point exists, is negative, and is the largest real crossing.
Olver, Chapter 11, §2, p. 394. -/
theorem transition_properties :
    airyEnvCrit < 0 ∧ Airy.Real.airyAi airyEnvCrit = Airy.Real.airyBi airyEnvCrit ∧
      ∀ x : ℝ, Airy.Real.airyAi x = Airy.Real.airyBi x → x ≤ airyEnvCrit := by
  sorry

/-- The weight is continuous, at least one, and nondecreasing.
Olver, Chapter 11, §2, pp. 394–395. -/
theorem weight_properties : Continuous weight ∧ Monotone weight ∧ ∀ x, 1 ≤ weight x := by
  sorry

/-- Both weighted moduli are continuous and strictly positive.
Olver, Chapter 11, §2, p. 395. -/
theorem modulus_properties : Continuous modulus ∧ Continuous derivativeModulus ∧
    ∀ x, 0 < modulus x ∧ 0 < derivativeModulus x := by
  sorry

/-- The actual phases give all four weighted sine/cosine representations.
Olver, Chapter 11, §2, p. 395. -/
theorem phase_representations (x : ℝ) :
    weight x * Airy.Real.airyAi x = modulus x * Real.sin (phase x) ∧
    Airy.Real.airyBi x / weight x = modulus x * Real.cos (phase x) ∧
    weight x * Airy.Real.airyAiDeriv x = derivativeModulus x * Real.sin (derivativePhase x) ∧
    Airy.Real.airyBiDeriv x / weight x = derivativeModulus x * Real.cos (derivativePhase x) := by
  sorry

/-- Continuity and the two source phase normalizations.
Olver, Chapter 11, §2, p. 395. -/
theorem phase_properties : Continuous phase ∧ Continuous derivativePhase ∧
    phase airyEnvCrit = Real.pi / 4 ∧ Tendsto derivativePhase atTop (𝓝 (-Real.pi / 4)) := by
  sorry

/-- The weight and the existing Ai/Bi envelopes agree with `M/E` and `M*E`.
Olver, Chapter 11, §2, pp. 395–396; DLMF 2.8.20–2.8.21. -/
theorem modulus_envelope (x : ℝ) :
    modulus x / weight x = envelopeAi x ∧ modulus x * weight x = envelopeBi x := by
  sorry

/-- The function modulus has the same normalized algebraic equivalent at both
real infinities. Olver, Chapter 11, §2, pp. 395–396. -/
theorem modulus_isEquivalent :
    (modulus ~[atTop] fun x : ℝ => |x| ^ (-1 / 4 : ℝ) / Real.sqrt Real.pi) ∧
      (modulus ~[atBot] fun x : ℝ => |x| ^ (-1 / 4 : ℝ) / Real.sqrt Real.pi) := by
  sorry

/-- The derivative modulus grows with exponent `1/4` at both real infinities.
Olver, Chapter 11, §2, pp. 395–396. -/
theorem derivativeModulus_isEquivalent :
    (derivativeModulus ~[atTop] fun x : ℝ => |x| ^ (1 / 4 : ℝ) / Real.sqrt Real.pi) ∧
      (derivativeModulus ~[atBot] fun x : ℝ => |x| ^ (1 / 4 : ℝ) / Real.sqrt Real.pi) := by
  sorry

/-- The weight has exactly the growing Airy exponential normalization.
Olver, Chapter 11, §2, pp. 395–396. -/
theorem weight_isEquivalent :
    weight ~[atTop] fun x : ℝ => Real.sqrt 2 * Real.exp ((2 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) := by
  sorry

/-- All three supremum constants are finite positive bounds for their defining
expressions. Olver, Chapter 11, §2, pp. 396–397. -/
theorem errorConstant_bounds :
    BddAbove (range fun x : ℝ => Real.pi * |x| ^ (1 / 2 : ℝ) * modulus x ^ 2) ∧
    BddAbove (range fun x : ℝ =>
      Real.pi * weight x * modulus x * |x| ^ (1 / 2 : ℝ) * |Airy.Real.airyAi x|) ∧
    BddAbove (range fun x : ℝ =>
      Real.pi / weight x * modulus x * |x| ^ (1 / 2 : ℝ) * |Airy.Real.airyBi x|) ∧
    0 < errorConstant ∧ 0 < aiErrorConstant ∧ 0 < biErrorConstant ∧ ∀ x : ℝ,
      Real.pi * |x| ^ (1 / 2 : ℝ) * modulus x ^ 2 ≤ errorConstant ∧
      Real.pi * weight x * modulus x * |x| ^ (1 / 2 : ℝ) * |Airy.Real.airyAi x| ≤ aiErrorConstant ∧
      Real.pi / weight x * modulus x * |x| ^ (1 / 2 : ℝ) * |Airy.Real.airyBi x| ≤
        biErrorConstant := by
  sorry

end DLMF.AsymptoticApproximations.Real.AiryEnvelope
