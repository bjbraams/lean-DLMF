/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Basics.Transcendental
public import DLMF.AsymptoticApproximations.Basics.OrderSymbols

/-!
# Rational examples of Poincaré expansion and reversion

The geometric series gives the expansion of `1/(z-1)`. Lagrange reversion for
`z+a+b/z` gives the first three terms of any inverse branch equivalent to the identity.
-/

@[expose] public noncomputable section

open Set Filter Finset Asymptotics PowerSeries
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- The geometric series at infinity expands `1/(z-1)` with zero constant term and
all later coefficients one. -/
theorem hasPoincareExpansion_inv_sub_one :
    HasPoincareExpansion univ (fun n => if n = 0 then (0 : ℂ) else 1)
      (fun z : ℂ => (z - 1)⁻¹) := by
  apply hasPoincareExpansion_of_hasSum (R := 1)
  intro z hz
  have hz0 : z ≠ 0 := by intro he; subst z; norm_num at hz
  have hnorm : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have hs := (hasSum_geometric_of_norm_lt_one hnorm).mul_left z⁻¹
  have hshift : HasSum (fun n : ℕ =>
      (if n + 1 = 0 then (0 : ℂ) else 1) * z⁻¹ ^ (n + 1)) (z - 1)⁻¹ := by
    convert hs using 1
    · funext n; simp [pow_succ, mul_comm]
    · field_simp
  have h := (hasSum_nat_add_iff
    (f := fun n => (if n = 0 then (0 : ℂ) else 1) * z⁻¹ ^ n)
    (g := (z - 1)⁻¹) 1).mp hshift
  simpa using h

/-- The inverse branch of `z+a+b/z` equivalent to the identity has remainder `O(y^(-3))`
after `y-a-b/y-ab/y²`, as predicted by the first three Lagrange coefficients. -/
theorem rational_reversion_sub_isBigO {𝕜 : Type*} [NormedField 𝕜] [CharZero 𝕜]
    (a b : 𝕜) {S T : Set 𝕜} {x : 𝕜 → 𝕜}
    (hx : x ~[Bornology.cobounded 𝕜 ⊓ 𝓟 T] id)
    (hxy : ∀ᶠ y in Bornology.cobounded 𝕜 ⊓ 𝓟 T,
      x y ∈ S ∧ x y + a + b / x y = y) :
    (fun y => x y - (y - a - b / y - a * b / y ^ 2))
      =O[Bornology.cobounded 𝕜 ⊓ 𝓟 T] (fun y => (y ^ (3 : ℕ))⁻¹) := by
  let P : 𝕜⟦X⟧ := C a + C b * X
  let fc : ℕ → 𝕜 := fun n => coeff n P
  have hw : Tendsto (fun z : 𝕜 => z⁻¹)
      (Bornology.cobounded 𝕜 ⊓ 𝓟 S) (𝓝 0) :=
    tendsto_inv₀_cobounded.mono_left inf_le_left
  have hs := (hasAsymptoticPowerSeries_const hw a).add
    ((hasAsymptoticPowerSeries_var hw).const_mul hw b)
  have hm : mk fc = P := by ext n; simp [fc]
  have hf : HasPoincareExpansion S fc (fun z : 𝕜 => (z + a + b / z) - z) := by
    rw [hasPoincareExpansion_iff_hasAsymptoticPowerSeries, hm]
    convert hs using 1
    funext z
    simp only [div_eq_mul_inv]
    ring
  have hc := lagrangeReversionCoeff_le_two fc
  have h0 : fc 0 = a := by simp [fc, P, PowerSeries.coeff_X]
  have h1 : fc 1 = b := by simp [fc, P, PowerSeries.coeff_X]
  have h2 : fc 2 = 0 := by simp [fc, P, PowerSeries.coeff_X]
  have hr := lagrange_reversion_of_isEquivalent hf hx hxy 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, smul_eq_mul,
    pow_zero, inv_one, one_mul, pow_one, hc.1, hc.2.1, hc.2.2, h0, h1, h2,
    zero_add] at hr
  refine hr.congr' (Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · dsimp only
    simp only [div_eq_mul_inv]
    ring
  · dsimp only
    rw [inv_pow]

end DLMF.AsymptoticApproximations
