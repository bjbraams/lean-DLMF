/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.BinomialPowerSeries
public import Mathlib.Analysis.Complex.Asymptotics

/-!
# Normalizing ramified asymptotic expansions

Dividing an expansion in `w^(n+ν)` by its common factor `w^ν` yields an ordinary
asymptotic power series. The real scale may then be regarded as a complex scale for
complex-valued amplitudes.
-/

@[expose] public noncomputable section

open Filter Finset PowerSeries
open scoped Topology

namespace PowerSeries

/-- The real power of a formal series normalized at its positive constant coefficient. -/
def realPower (P : ℝ⟦X⟧) (β : ℝ) : ℝ⟦X⟧ :=
  C (constantCoeff P ^ β) * binomialSubstitution (C (constantCoeff P)⁻¹ * P - 1) β

/-- The constant coefficient of the real binomial power. -/
theorem constantCoeff_realPower {P : ℝ⟦X⟧} (hP : 0 < constantCoeff P) (β : ℝ) :
    constantCoeff (realPower P β) = constantCoeff P ^ β := by
  have hnorm : constantCoeff (C (constantCoeff P)⁻¹ * P - 1) = 0 := by
    simp only [map_sub, map_mul, constantCoeff_C, map_one, inv_mul_cancel₀ hP.ne', sub_self]
  have hB : constantCoeff (binomialSubstitution (C (constantCoeff P)⁻¹ * P - 1) β) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_binomialSubstitution hnorm]
    norm_num only [Nat.zero_add, range_one, sum_singleton, Ring.choose_zero_right, pow_zero,
      coeff_one, ite_true, mul_one]
  rw [realPower, map_mul, constantCoeff_C, hB, mul_one]

end PowerSeries

namespace Asymptotics

/-- Removing a common real-power factor from an asymptotic expansion. -/
theorem HasAsymptoticExpansion.smul_rpow_neg {α E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {l : Filter α} {w : α → ℝ} {c : ℕ → E} {f : α → E} {ν : ℝ}
    (hw : ∀ᶠ x in l, 0 < w x)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ ((n : ℝ) + ν)) c f) :
    HasAsymptoticExpansion l (fun n x => w x ^ n) c
      (fun x => w x ^ (-ν) • f x) := by
  apply (hf.mul_left (fun x => w x ^ (-ν))).congr_scale
  intro n
  filter_upwards [hw] with x hx
  rw [← Real.rpow_add hx, show -ν + ((n : ℝ) + ν) = n by ring, Real.rpow_natCast]

/-- A complex amplitude has the same ordinary expansion with real and complex powers. -/
theorem hasAsymptoticExpansion_real_pow_iff {α : Type*} {l : Filter α} {w : α → ℝ}
    {c : ℕ → ℂ} {f : α → ℂ} :
    HasAsymptoticExpansion l (fun n x => w x ^ n) c f ↔
      HasAsymptoticPowerSeries l (fun x => (w x : ℂ)) (PowerSeries.mk c) f := by
  simp only [HasAsymptoticExpansion, HasAsymptoticPowerSeries, PowerSeries.coeff_mk]
  constructor
  · intro h N
    have H := Complex.isBigO_ofReal_right.mpr (h N)
    simpa only [Complex.real_smul, Complex.ofReal_pow, smul_eq_mul] using H
  · intro h N
    apply Complex.isBigO_ofReal_right.mp
    simpa only [Complex.real_smul, Complex.ofReal_pow, smul_eq_mul] using h N

/-- Complexification preserves an ordinary real asymptotic power series. -/
theorem HasAsymptoticPowerSeries.ofReal {α : Type*} {l : Filter α} {w f : α → ℝ}
    {P : ℝ⟦X⟧} (hf : HasAsymptoticPowerSeries l w P f) :
    HasAsymptoticPowerSeries l (fun x => (w x : ℂ))
      (PowerSeries.map Complex.ofRealHom P) (fun x => (f x : ℂ)) := by
  intro N
  change (fun x => (f x : ℂ) - ∑ n ∈ range N,
    (w x : ℂ) ^ n * ((PowerSeries.coeff n P : ℝ) : ℂ)) =O[l] fun x => (w x : ℂ) ^ N
  have H := Complex.isBigO_ofReal_right.mpr (Complex.isBigO_ofReal_left.mpr (hf N))
  simpa only [Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow, smul_eq_mul] using H

/-- Normalizing a ramified complex amplitude produces an ordinary complex power series. -/
theorem HasAsymptoticExpansion.complex_powerSeries_of_rpow {α : Type*} {l : Filter α}
    {w : α → ℝ} {c : ℕ → ℂ} {f : α → ℂ} {ν : ℝ} (hw : ∀ᶠ x in l, 0 < w x)
    (hf : HasAsymptoticExpansion l (fun n x => w x ^ ((n : ℝ) + ν)) c f) :
    HasAsymptoticPowerSeries l (fun x => (w x : ℂ)) (PowerSeries.mk c)
      (fun x => w x ^ (-ν) • f x) :=
  hasAsymptoticExpansion_real_pow_iff.mp (hf.smul_rpow_neg hw)

/-- Real powers of a series with positive constant coefficient, with the binomial coefficients. -/
theorem HasAsymptoticPowerSeries.rpow {α : Type*} {l : Filter α} {w f : α → ℝ}
    {P : ℝ⟦X⟧} (hw : Tendsto w l (𝓝 0)) (hf : HasAsymptoticPowerSeries l w P f)
    (hP : 0 < PowerSeries.constantCoeff P) (β : ℝ) :
    HasAsymptoticPowerSeries l w
      (PowerSeries.C (PowerSeries.constantCoeff P ^ β) * PowerSeries.binomialSubstitution
        (PowerSeries.C (PowerSeries.constantCoeff P)⁻¹ * P - 1) β)
      (fun x => f x ^ β) := by
  let c : ℝ := PowerSeries.constantCoeff P
  have hc : 0 < c := hP
  have hnorm := (hf.const_mul hw c⁻¹).sub (HasAsymptoticPowerSeries.one hw)
  have hnorm0 : PowerSeries.constantCoeff (PowerSeries.C c⁻¹ * P - 1) = 0 := by
    simp only [map_sub, map_mul, PowerSeries.constantCoeff_C, map_one]
    exact sub_eq_zero.mpr (inv_mul_cancel₀ hc.ne')
  have H := (hnorm.one_add_rpow hw hnorm0 β).const_mul hw (c ^ β)
  refine H.congr' ?_
  filter_upwards [(hf.tendsto hw).eventually (eventually_gt_nhds hP)] with x hx
  change c ^ β * (1 + (c⁻¹ * f x - 1)) ^ β = f x ^ β
  rw [show 1 + (c⁻¹ * f x - 1) = c⁻¹ * f x by ring,
    ← Real.mul_rpow hc.le (by positivity : 0 ≤ c⁻¹ * f x), ← mul_assoc,
    mul_inv_cancel₀ hc.ne', one_mul]

/-- Real powers of an asymptotic power series with positive constant coefficient. -/
theorem HasAsymptoticPowerSeries.realPower {α : Type*} {l : Filter α} {w f : α → ℝ}
    {P : ℝ⟦X⟧} (hw : Tendsto w l (𝓝 0)) (hf : HasAsymptoticPowerSeries l w P f)
    (hP : 0 < PowerSeries.constantCoeff P) (β : ℝ) :
    HasAsymptoticPowerSeries l w (PowerSeries.realPower P β) (fun x => f x ^ β) :=
  hf.rpow hw hP β

/-- Re-expanding a function in a coordinate with a nonzero linear coefficient. -/
theorem HasAsymptoticPowerSeries.reparametrize {α 𝕜 : Type*} [NormedField 𝕜]
    {l : Filter α} {w f h : α → 𝕜} {P H : 𝕜⟦X⟧} (hw : Tendsto w l (𝓝 0))
    (hf : HasAsymptoticPowerSeries l w P f) (hh : HasAsymptoticPowerSeries l w H h)
    (hH0 : PowerSeries.constantCoeff H = 0) (hH1 : PowerSeries.coeff 1 H ≠ 0) :
    HasAsymptoticPowerSeries l h (P.subst (H.substInvOfIsUnit hH1.isUnit)) f := by
  have hinv := hh.inversion hw hH0 hH1 (tendsto_id : Tendsto id l l)
    (Eventually.of_forall (fun _ => rfl))
  have hh0 : Tendsto h l (𝓝 0) := by simpa only [hH0] using hh.tendsto hw
  have H := hf.comp (tendsto_id : Tendsto id l l) hh0
    (PowerSeries.constantCoeff_substInvOfIsUnit H hH1.isUnit) hinv
  simpa only [id_eq] using H

end Asymptotics
