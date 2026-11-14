/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Defs.Filter

/-!
# Morita's p-adic gamma function

The normalization is that of Andrews, Askey and Roy, *Special Functions*, §1.12:
on positive integers, multiply the positive integers below the argument not divisible
by `p`, and multiply by `(-1)^n`. The extension to `ℤ_[p]` uses the canonical
residue approximations. Convergence and interpolation are in `DLMF.Gamma.PadicGamma`.
-/

@[expose] public section

open Filter Finset

namespace DLMF.Gamma

/-- Integer values of Morita's gamma function. Andrews–Askey–Roy, *Special Functions*,
§1.12, pp. 45–46 (synopsis AAR-1.11–1.12). The value at zero is one. -/
def padicGammaInteger (p n : ℕ) : ℤ :=
  (-1) ^ n * ∏ j ∈ Ico 1 n, if p ∣ j then 1 else (j : ℤ)

/-- The signed product defining integer p-adic gamma values. -/
theorem padicGammaInteger_def (p n : ℕ) :
    padicGammaInteger p n = (-1) ^ n *
      ∏ j ∈ Ico 1 n, if p ∣ j then 1 else (j : ℤ) := rfl

/-- Morita's gamma function on p-adic integers, with the integer-product normalization.
Andrews–Askey–Roy, *Special Functions*, §1.12, pp. 45–46
(synopsis AAR-1.11–1.12). `PadicInt.appr` gives representatives in `[0,p^n)`. -/
noncomputable def padicGamma (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) : ℤ_[p] :=
  limUnder atTop fun n : ℕ => (padicGammaInteger p (x.appr n) : ℤ_[p])

/-- The canonical approximation limit defining p-adic gamma. -/
theorem padicGamma_def (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) :
    padicGamma p x =
      limUnder atTop (fun n : ℕ => (padicGammaInteger p (x.appr n) : ℤ_[p])) := rfl

end DLMF.Gamma
