/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.GammaShiftBounds

/-!
# Uniform factorial decay of shifted reciprocal Gamma

The Gamma–Pochhammer identities and shift bounds formerly copied here from lean-codes
(`Pochhammer/Gamma.lean`) now come from lean-codes directly: see `Pochhammer.Gamma` and
`ToMathlib.Analysis.SpecialFunctions.GammaShiftBounds`. Only the name used by
`DLMF.Struve.Lommel` is kept, as an alias of the lean-codes theorem.
-/

namespace DLMF.Gamma.Simplex.Complex

open _root_.Complex

/-- Reciprocal Gamma has uniform factorial decay after a common natural shift on any compact
set of complex arguments (alias of `Complex.exists_uniform_norm_inv_Gamma_add_nat`). -/
public theorem exists_uniform_norm_recip_Gamma_add_nat {K : Set ℂ} (hK : IsCompact K) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, ∀ n : ℕ,
      ‖(Gamma (b + (n + m)))⁻¹‖ ≤ C / n.factorial :=
  _root_.Complex.exists_uniform_norm_inv_Gamma_add_nat hK

end DLMF.Gamma.Simplex.Complex
