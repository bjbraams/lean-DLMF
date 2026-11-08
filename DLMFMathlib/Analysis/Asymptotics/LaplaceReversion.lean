/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.LaplaceCoefficients
public import DLMFMathlib.Analysis.Asymptotics.RamifiedDensityWeights

/-!
# Asymptotic reversion of ramified phase densities

The coordinate `h=w g^(1/μ)` is invertible as an asymptotic power series when the
constant coefficient of `g` is positive. Reverting a weighted density in this coordinate
and applying the formal Bürmann identity gives its coefficients as finite binomial
convolutions, without convergence assumptions on the original power series.
-/

@[expose] public noncomputable section

open Filter Finset PowerSeries
open scoped Topology

namespace Asymptotics

/-- Reverting a ramified phase in a weighted asymptotic density. -/
theorem hasAsymptoticExpansion_ramified_density {α : Type*} {l : Filter α}
    {w g : α → ℝ} {q d : α → ℂ} {P : ℝ⟦X⟧} {Q : ℂ⟦X⟧} {lam mu : ℝ}
    (hw : Tendsto w l (𝓝 0)) (hwpos : ∀ᶠ x in l, 0 < w x)
    (hp0 : 0 < constantCoeff P) (hmu : mu ≠ 0)
    (hg : HasAsymptoticPowerSeries l w P g)
    (hq : HasAsymptoticPowerSeries l (fun x => (w x : ℂ)) Q q)
    (hd : HasAsymptoticPowerSeries l (fun x => (w x : ℂ))
      (C (mu : ℂ) * PowerSeries.map Complex.ofRealHom P +
        X * derivative (PowerSeries.map Complex.ofRealHom P)) d) :
    HasAsymptoticExpansion l
      (fun n x => (w x * g x ^ mu⁻¹) ^ ((n : ℝ) + lam - mu))
      (fun n => (mu : ℂ)⁻¹ * Complex.exp
        (-(((lam : ℂ) + n) / mu) * (Real.log (constantCoeff P) : ℂ)) *
        coeff n (Q * binomialSubstitution
          (C (constantCoeff (PowerSeries.map Complex.ofRealHom P))⁻¹ *
            PowerSeries.map Complex.ofRealHom P - 1) (-(((lam : ℂ) + n) / mu))))
      (fun x => (w x * g x ^ mu⁻¹) ^ (lam - mu) •
        (q x / d x * ((g x ^ (1 - lam / mu) : ℝ) : ℂ))) := by
  let Pc : ℂ⟦X⟧ := PowerSeries.map Complex.ofRealHom P
  let L : ℂ := (Real.log (constantCoeff P) : ℂ)
  let Phi : ℂ⟦X⟧ := logarithmicPower Pc L (-(mu : ℂ)⁻¹)
  let H : ℂ⟦X⟧ := X * Phi⁻¹
  let G : ℂ⟦X⟧ := Q * (C (mu : ℂ) * Pc + X * derivative Pc)⁻¹ *
    logarithmicPower Pc L (1 - (lam : ℂ) / mu)
  let phase : α → ℝ := fun x => w x * g x ^ mu⁻¹
  have hcoeff : constantCoeff Pc = ((constantCoeff P : ℝ) : ℂ) := by
    dsimp only [Pc]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
    rfl
  have hPc : constantCoeff Pc ≠ 0 := by rw [hcoeff]; exact Complex.ofReal_ne_zero.mpr hp0.ne'
  have hL : Complex.exp L = constantCoeff Pc := by
    rw [hcoeff]
    dsimp only [L]
    rw [← Complex.ofReal_exp, Real.exp_log hp0]
  have huc : Tendsto (fun x => (w x : ℂ)) l (𝓝 0) := by
    simpa only [Complex.ofReal_zero, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hw
  have hPhi : Phi⁻¹ = logarithmicPower Pc L (mu : ℂ)⁻¹ := by
    dsimp only [Phi]
    rw [← logarithmicPower_neg hPc, neg_neg]
  have hroot : HasAsymptoticPowerSeries l (fun x => (w x : ℂ))
      (logarithmicPower Pc L (mu : ℂ)⁻¹) (fun x => ((g x ^ mu⁻¹ : ℝ) : ℂ)) := by
    have HH := (hg.realPower hw hp0 mu⁻¹).ofReal
    rw [map_realPower_eq_logarithmicPower hp0] at HH
    simpa only [Complex.ofReal_inv] using HH
  have hphase : HasAsymptoticPowerSeries l (fun x => (w x : ℂ)) H
      (fun x => (phase x : ℂ)) := by
    have HH := hroot.mul_var huc
    rw [← hPhi] at HH
    simpa only [H, phase, Complex.ofReal_mul] using HH
  have hD0 : constantCoeff (C (mu : ℂ) * Pc + X * derivative Pc) ≠ 0 := by
    simp only [map_add, map_mul, constantCoeff_C, constantCoeff_X, zero_mul, add_zero]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hmu) hPc
  have hweight : HasAsymptoticPowerSeries l (fun x => (w x : ℂ))
      (logarithmicPower Pc L (1 - (lam : ℂ) / mu))
      (fun x => ((g x ^ (1 - lam / mu) : ℝ) : ℂ)) := by
    have HH := (hg.realPower hw hp0 (1 - lam / mu)).ofReal
    rw [map_realPower_eq_logarithmicPower hp0] at HH
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div] using HH
  have hG : HasAsymptoticPowerSeries l (fun x => (w x : ℂ)) G
      (fun x => q x / d x * ((g x ^ (1 - lam / mu) : ℝ) : ℂ)) := by
    simpa only [G, div_eq_mul_inv] using (hq.mul huc (hd.recip huc hD0)).mul huc hweight
  have hH0 : constantCoeff H = 0 := by simp only [H, map_mul, constantCoeff_X, zero_mul]
  have hH1 : coeff 1 H ≠ 0 := by
    change coeff 1 (X * Phi⁻¹) ≠ 0
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_inv]
    dsimp only [Phi]
    rw [constantCoeff_logarithmicPower hPc]
    exact inv_ne_zero (Complex.exp_ne_zero _)
  let T := H.substInvOfIsUnit hH1.isUnit
  have hT0 : constantCoeff T = 0 := constantCoeff_substInvOfIsUnit H hH1.isUnit
  have hTH : T.subst H = X := subst_substInvOfIsUnit_left H hH0 hH1.isUnit
  have hrev := hG.reparametrize huc hphase hH0 hH1
  have hreal : HasAsymptoticExpansion l (fun n x => phase x ^ n)
      (fun n => coeff n (G.subst T))
      (fun x => q x / d x * ((g x ^ (1 - lam / mu) : ℝ) : ℂ)) := by
    apply hasAsymptoticExpansion_real_pow_iff.mpr
    have he : PowerSeries.mk (fun n => coeff n (G.subst T)) = G.subst T := by
      ext n
      rw [coeff_mk]
    rw [he]
    exact hrev
  have hphasepos : ∀ᶠ x in l, 0 < phase x := by
    filter_upwards [hwpos, (hg.tendsto hw).eventually (eventually_gt_nhds hp0)] with x hx hgx
    exact mul_pos hx (Real.rpow_pos_of_pos hgx _)
  have hscaled := (hreal.mul_left (fun x => phase x ^ (lam - mu))).congr_scale
    (ψ := fun n x => phase x ^ ((n : ℝ) + lam - mu)) (fun n => by
      filter_upwards [hphasepos] with x hx
      rw [← Real.rpow_natCast, ← Real.rpow_add hx]
      congr 1
      ring)
  refine hscaled.congr_coeff ?_
  funext n
  exact coeff_weightedDensity_subst_inverse hL (Complex.ofReal_ne_zero.mpr hmu) hT0 hTH n

/-- The ramified quotient expansion from differentiated phase and amplitude expansions. -/
theorem hasAsymptoticExpansion_ramified_quotient {α : Type*} {l : Filter α}
    {w v d : α → ℝ} {q : α → ℂ} {P : ℝ⟦X⟧} {Q : ℂ⟦X⟧} {lam mu : ℝ}
    (hw : Tendsto w l (𝓝 0)) (hwpos : ∀ᶠ x in l, 0 < w x)
    (hp0 : 0 < constantCoeff P) (hmu : mu ≠ 0)
    (hv : HasAsymptoticExpansion l (fun n x => w x ^ ((n : ℝ) + mu))
      (fun n => coeff n P) v)
    (hd : HasAsymptoticExpansion l (fun n x => w x ^ ((n : ℝ) + mu - 1))
      (fun n => ((n : ℝ) + mu) * coeff n P) d)
    (hq : HasAsymptoticExpansion l (fun n x => w x ^ ((n : ℝ) + lam - 1))
      (fun n => coeff n Q) q) :
    HasAsymptoticExpansion l (fun n x => v x ^ (((n : ℝ) + lam - mu) / mu))
      (fun n => (mu : ℂ)⁻¹ * Complex.exp
        (-(((lam : ℂ) + n) / mu) * (Real.log (constantCoeff P) : ℂ)) *
        coeff n (Q * binomialSubstitution
          (C (constantCoeff (PowerSeries.map Complex.ofRealHom P))⁻¹ *
            PowerSeries.map Complex.ofRealHom P - 1) (-(((lam : ℂ) + n) / mu))))
      (fun x => q x / (d x : ℂ)) := by
  let g : α → ℝ := fun x => w x ^ (-mu) * v x
  let dn : α → ℝ := fun x => w x ^ (1 - mu) * d x
  let qn : α → ℂ := fun x => w x ^ (1 - lam) • q x
  let D : ℝ⟦X⟧ := PowerSeries.mk (fun n => ((n : ℝ) + mu) * coeff n P)
  have hg : HasAsymptoticPowerSeries l w P g := by
    simpa only [HasAsymptoticPowerSeries, smul_eq_mul] using hv.smul_rpow_neg hwpos
  have hd' : HasAsymptoticExpansion l (fun n x => w x ^ ((n : ℝ) + (mu - 1)))
      (fun n => ((n : ℝ) + mu) * coeff n P) d := by
    apply hd.congr_scale
    intro n
    exact Eventually.of_forall fun x => congrArg (fun r : ℝ => w x ^ r)
      (show (n : ℝ) + mu - 1 = (n : ℝ) + (mu - 1) by ring)
  have hdn : HasAsymptoticPowerSeries l w D dn := by
    have HH := hd'.smul_rpow_neg hwpos
    simpa only [HasAsymptoticPowerSeries, D, coeff_mk,
      show -(mu - 1) = 1 - mu by ring, smul_eq_mul] using HH
  have hq' : HasAsymptoticExpansion l (fun n x => w x ^ ((n : ℝ) + (lam - 1)))
      (fun n => coeff n Q) q := by
    apply hq.congr_scale
    intro n
    exact Eventually.of_forall fun x => congrArg (fun r : ℝ => w x ^ r)
      (show (n : ℝ) + lam - 1 = (n : ℝ) + (lam - 1) by ring)
  have hqn : HasAsymptoticPowerSeries l (fun x => (w x : ℂ)) Q qn := by
    have HH := hq'.complex_powerSeries_of_rpow hwpos
    have he : PowerSeries.mk (fun n => coeff n Q) = Q := by ext n; rw [coeff_mk]
    rw [he] at HH
    simpa only [show -(lam - 1) = 1 - lam by ring] using HH
  have hD : PowerSeries.map Complex.ofRealHom D =
      C (mu : ℂ) * PowerSeries.map Complex.ofRealHom P +
        X * derivative (PowerSeries.map Complex.ofRealHom P) := by
    ext n
    rw [coeff_map, show coeff n D = ((n : ℝ) + mu) * coeff n P from coeff_mk n _,
      map_add, coeff_C_mul]
    cases n with
    | zero =>
      have hz : coeff 0 (X * derivative (PowerSeries.map Complex.ofRealHom P)) = 0 := by
        rw [coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul]
      rw [hz, add_zero, coeff_map]
      simp only [Nat.cast_zero, zero_add, map_mul]
      rfl
    | succ n =>
      rw [coeff_succ_X_mul, coeff_derivative, coeff_map]
      change (((((n + 1 : ℕ) : ℝ) + mu) * coeff (n + 1) P : ℝ) : ℂ) =
        (mu : ℂ) * ((coeff (n + 1) P : ℝ) : ℂ) +
          ((coeff (n + 1) P : ℝ) : ℂ) * ((n : ℂ) + 1)
      push_cast
      ring
  have hdnC := hdn.ofReal
  rw [hD] at hdnC
  have HH := hasAsymptoticExpansion_ramified_density (lam := lam) hw hwpos hp0 hmu hg hqn hdnC
  have hgpos : ∀ᶠ x in l, 0 < g x := (hg.tendsto hw).eventually (eventually_gt_nhds hp0)
  have hvEq (x : α) (hx : 0 < w x) : w x ^ mu * g x = v x := by
    dsimp only [g]
    rw [← mul_assoc, ← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero, one_mul]
  have Hscale := HH.congr_scale (ψ := fun n x => v x ^ (((n : ℝ) + lam - mu) / mu))
    (fun n => by
      filter_upwards [hwpos, hgpos] with x hx hgx
      rw [Real.rpow_ramified_phase (w x) (g x) mu lam n hx hgx hmu, hvEq x hx])
  apply Hscale.congr'
  filter_upwards [hwpos, hgpos] with x hx hgx
  simpa only [qn, dn, Complex.ofReal_mul, Complex.real_smul] using
    Complex.smul_ramified_density (w x) (g x) mu lam (q x) (d x) hx hgx hmu

end Asymptotics
