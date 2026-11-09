/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.LaplaceCoefficients
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Complex powers and logarithms of asymptotic power series

Principal powers and logarithms preserve asymptotic power series whose constant coefficient
lies in the slit plane. The formal power is `PowerSeries.logarithmicPower`, with the principal
logarithm of that coefficient. Changing its logarithm by `2πi` records the change of branch.
These are the logarithm and power operations of DLMF §2.1(iii).
-/

@[expose] public noncomputable section

open Filter PowerSeries
open scoped Topology

namespace Complex

/-- Near a point of the slit plane, logarithms add under normalization by that point. -/
theorem eventually_log_eq_log_add_log_normalized {c : ℂ} (hc : c ∈ slitPlane) :
    ∀ᶠ z in 𝓝 c, log z = log c + log (c⁻¹ * z) := by
  have hc0 := (mem_slitPlane_iff_arg.mp hc).2
  have hnorm : Tendsto (fun z : ℂ => c⁻¹ * z) (𝓝 c) (𝓝 1) := by
    have hcont : Continuous (fun z : ℂ => c⁻¹ * z) := by fun_prop
    convert hcont.tendsto c using 1
    rw [inv_mul_cancel₀ hc0]
  have harg : Tendsto (fun z : ℂ => arg c + arg (c⁻¹ * z)) (𝓝 c) (𝓝 (arg c)) := by
    simpa only [arg_one, add_zero, Function.comp_def] using
      (continuousAt_arg (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp hnorm |>.const_add (arg c)
  have hbounds : Set.Ioo (-Real.pi) Real.pi ∈ 𝓝 (arg c) :=
    Ioo_mem_nhds (neg_pi_lt_arg c) (lt_of_le_of_ne (arg_le_pi c) (slitPlane_arg_ne_pi hc))
  filter_upwards [harg.eventually hbounds, hnorm.eventually_ne one_ne_zero] with z hz hz0
  simpa only [mul_inv_cancel_left₀ hc0] using
    log_mul hc0 hz0 ⟨hz.1, hz.2.le⟩

end Complex

namespace PowerSeries

/-- The formal series for `log (1 + X)`, with constant coefficient zero. -/
def logSeries : ℂ⟦X⟧ := mk fun n => (-1 : ℂ) ^ (n + 1) / (n : ℂ)

/-- The principal logarithm at one has the coefficients of the formal logarithm series. -/
theorem hasFPowerSeriesAt_log_one_add :
    HasFPowerSeriesAt (fun z : ℂ => Complex.log (1 + z))
      (.ofScalars ℂ (fun n => coeff n logSeries)) 0 := by
  convert hasFPowerSeriesAt_clog_one_add using 1
  congr 1
  funext n
  simp only [logSeries, coeff_mk, pow_succ, mul_neg_one]

/-- Natural logarithmic powers are the ordinary powers of the original formal series. -/
theorem logarithmicPower_natCast {P : ℂ⟦X⟧} {L : ℂ}
    (hL : Complex.exp L = constantCoeff P) (n : ℕ) :
    logarithmicPower P L n = P ^ n := by
  have hP : constantCoeff P ≠ 0 := hL ▸ Complex.exp_ne_zero L
  simpa only [one_mul, logarithmicPower_one hL] using logarithmicPower_mul_natCast hP L 1 n

/-- Increasing the logarithm by one turn multiplies a formal power by its monodromy factor. -/
theorem logarithmicPower_add_two_pi_mul_I (P : ℂ⟦X⟧) (L β : ℂ) :
    logarithmicPower P (L + 2 * Real.pi * Complex.I) β =
      C (Complex.exp (2 * Real.pi * Complex.I * β)) * logarithmicPower P L β := by
  simp only [logarithmicPower, mul_add, Complex.exp_add, map_mul]
  rw [mul_comm β (2 * Real.pi * Complex.I)]
  ring

end PowerSeries

namespace Asymptotics.HasAsymptoticPowerSeries

variable {α : Type*} {l : Filter α} {w f : α → ℂ} {P : ℂ⟦X⟧}

/-- The principal complex power of an asymptotic series with constant coefficient in the slit
plane has the corresponding formal logarithmic power as expansion. -/
theorem cpow (hf : HasAsymptoticPowerSeries l w P f) (hw : Tendsto w l (𝓝 0))
    (hP : constantCoeff P ∈ Complex.slitPlane) (β : ℂ) :
    HasAsymptoticPowerSeries l w (logarithmicPower P (Complex.log (constantCoeff P)) β)
      (fun x => f x ^ β) := by
  let c := constantCoeff P
  have hc : c ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hP).2
  have hu := (hf.const_mul hw c⁻¹).sub (one hw)
  have hu0 : constantCoeff (C c⁻¹ * P - 1) = 0 := by simp [c, hc]
  have hp := (hu.one_add_cpow hw hu0 β).const_mul hw (Complex.exp (β * Complex.log c))
  change HasAsymptoticPowerSeries l w (logarithmicPower P (Complex.log c) β) _
  refine hp.congr' ?_
  have hlog := (hf.tendsto hw).eventually
    (Complex.eventually_log_eq_log_add_log_normalized hP)
  have hne := (hf.tendsto hw).eventually_ne hc
  filter_upwards [hlog, hne] with x hx hx0
  simp only [add_sub_cancel]
  dsimp only [c] at *
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (inv_ne_zero hc) hx0),
    Complex.cpow_def_of_ne_zero hx0, hx, add_mul, Complex.exp_add]
  congr 1
  ring

/-- The principal logarithm of an asymptotic series with constant coefficient in the slit
plane is obtained by substituting its normalized nonconstant part into `logSeries`. -/
theorem log (hf : HasAsymptoticPowerSeries l w P f) (hw : Tendsto w l (𝓝 0))
    (hP : constantCoeff P ∈ Complex.slitPlane) :
    HasAsymptoticPowerSeries l w
      (C (Complex.log (constantCoeff P)) +
        logSeries.subst (C (constantCoeff P)⁻¹ * P - 1)) (fun x => Complex.log (f x)) := by
  let c := constantCoeff P
  have hc : c ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hP).2
  have hu := (hf.const_mul hw c⁻¹).sub (one hw)
  have hu0 : constantCoeff (C c⁻¹ * P - 1) = 0 := by simp [c, hc]
  have hs := hu.analytic_comp
    (by rw [hu0]; exact PowerSeries.hasFPowerSeriesAt_log_one_add) hw
  have hlog : HasAsymptoticPowerSeries l w (logSeries.subst (C c⁻¹ * P - 1))
      (fun x => Complex.log (c⁻¹ * f x)) := by
    simpa only [hu0, map_zero, sub_zero, FormalMultilinearSeries.coeff_ofScalars,
      logSeries, coeff_mk, Pi.sub_apply, Pi.one_apply, add_sub_cancel] using hs
  refine ((hasAsymptoticPowerSeries_const hw (Complex.log c)).add hlog).congr' ?_
  exact ((hf.tendsto hw).eventually
    (Complex.eventually_log_eq_log_add_log_normalized hP)).mono fun _ h => h.symm

end Asymptotics.HasAsymptoticPowerSeries
