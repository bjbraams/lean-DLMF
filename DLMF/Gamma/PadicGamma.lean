/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Basic.PadicGamma

/-!
# Continuity and congruences for Morita's gamma function

Statements from Andrews, Askey and Roy, *Special Functions*, §1.12, pp. 45–46
(synopsis AAR-1.11–1.12), for odd prime `p`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace DLMF.Gamma

/-- The integer products along canonical approximations converge to Morita's gamma.
Andrews–Askey–Roy, *Special Functions*, §1.12 (synopsis AAR-1.11–1.12). -/
theorem tendsto_padicGammaInteger_appr (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (x : ℤ_[p]) :
    Tendsto (fun n : ℕ => (padicGammaInteger p (x.appr n) : ℤ_[p])) atTop
      (𝓝 (padicGamma p x)) := by
  sorry

/-- Morita's gamma interpolates the integer signed products.
Andrews–Askey–Roy, *Special Functions*, §1.12 (synopsis AAR-1.11–1.12). -/
theorem padicGamma_natCast (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n : ℕ) :
    padicGamma p (n : ℤ_[p]) = (padicGammaInteger p n : ℤ_[p]) := by
  sorry

/-- Morita's gamma is continuous on the p-adic integers.
Andrews–Askey–Roy, *Special Functions*, §1.12 (synopsis AAR-1.11–1.12). -/
theorem continuous_padicGamma (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Continuous (padicGamma p) := by
  sorry

/-- Every value of Morita's gamma is a unit.
Andrews–Askey–Roy, *Special Functions*, §1.12 (synopsis AAR-1.11–1.12). -/
theorem isUnit_padicGamma (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (x : ℤ_[p]) :
    IsUnit (padicGamma p x) := by
  sorry

/-- The p-adic gamma functional equation distinguishes units from the maximal ideal.
Andrews–Askey–Roy, *Special Functions*, §1.12 (synopsis AAR-1.11–1.12). -/
theorem padicGamma_add_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (x : ℤ_[p]) :
    (IsUnit x → padicGamma p (x + 1) = -x * padicGamma p x) ∧
      (¬IsUnit x → padicGamma p (x + 1) = -padicGamma p x) := by
  sorry

/-- Congruent inputs have congruent gamma values at the same modulus.
Andrews–Askey–Roy, *Special Functions*, §1.12 (synopsis AAR-1.11–1.12). -/
theorem padicGamma_congr (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (r : ℕ)
    {x y : ℤ_[p]} (hxy : PadicInt.toZModPow r x = PadicInt.toZModPow r y) :
    PadicInt.toZModPow r (padicGamma p x) = PadicInt.toZModPow r (padicGamma p y) := by
  sorry

/-- The continuous interpolation of the integer signed products is unique.
Andrews–Askey–Roy, *Special Functions*, §1.12 (synopsis AAR-1.11–1.12). -/
theorem eq_padicGamma_of_continuous (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {f : ℤ_[p] → ℤ_[p]} (hf : Continuous f)
    (hinterp : ∀ n : ℕ, 0 < n → f n = (padicGammaInteger p n : ℤ_[p])) :
    f = padicGamma p := by
  sorry

end DLMF.Gamma
