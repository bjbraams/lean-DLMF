/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Integrals.Watson
public import DLMFMathlib.Analysis.Integral.RayLaplace

/-!
# Watson expansions on the logarithmic plane

The expansion of a rotated Laplace integral is expressed in `exp(-αζ)`, with `ζ` the
logarithm of the Laplace parameter. This retains the branch through strips crossing
`Im ζ = ±π`, as required for the continuation in DLMF §2.4(i).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics Complex Finset
open scoped Topology Real

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.4.1 on a rotated ray: a complex-power expansion at the origin gives the
Laplace expansion `∑ Γ(αₛ)cₛ exp(-αₛζ)` in each closed logarithmic subsector.
The expansion hypothesis is the restriction of the chosen branch to the ray of angle `θ`. -/
@[dlmf 2.4.E1]
theorem hasAsymptoticExpansion_rayLaplace {q : ℂ → ℂ} {a α : ℕ → ℂ} {c θ δ : ℝ}
    (hα : ∀ n, 0 < (α n).re) (hδ : 0 < δ) (hδπ : δ ≤ Real.pi / 2)
    (hint : IntegrableOn (fun r : ℝ => Real.exp (-c * r) • q (r * exp (θ * I))) (Ioi 0))
    (hq : ∀ N : ℕ, (fun r : ℝ => q (r * exp (θ * I)) -
      ∑ n ∈ range N, (r : ℂ) ^ (α n - 1) • (exp (θ * I * (α n - 1)) * a n))
        =O[𝓝[>] 0] (fun r : ℝ => r ^ ((α N).re - 1))) :
    HasAsymptoticExpansion
      (comap (fun ζ : ℂ => ζ.re) atTop ⊓ 𝓟 {ζ : ℂ | |ζ.im + θ| ≤ Real.pi / 2 - δ})
      (fun n ζ => exp (-α n * ζ)) (fun n => Gamma (α n) * a n) (rayLaplace q θ) := by
  let L := comap (fun ζ : ℂ => ζ.re) atTop ⊓
    𝓟 {ζ : ℂ | |ζ.im + θ| ≤ Real.pi / 2 - δ}
  let γ := Real.cos (Real.pi / 2 - δ)
  have hγ : 0 < γ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hphase : ∀ᶠ ζ : ℂ in L, |ζ.im + θ| ≤ Real.pi / 2 - δ := by
    dsimp only [L]
    rw [eventually_inf_principal]
    exact Eventually.of_forall fun _ h => h
  have he : Tendsto (fun ζ : ℂ => exp (ζ + θ * I)) L (sectorAtTop γ) := by
    rw [sectorAtTop, tendsto_inf]
    constructor
    · rw [tendsto_comap_iff]
      have ht : Tendsto (fun ζ : ℂ => ζ.re) L atTop :=
        tendsto_comap.mono_left inf_le_left
      convert Real.tendsto_exp_atTop.comp ht using 1
      funext ζ
      simp [Function.comp_def, norm_exp]
    · apply tendsto_principal.mpr
      filter_upwards [hphase] with ζ hζ
      have hc : γ ≤ Real.cos (ζ.im + θ) := by
        simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi
          (abs_nonneg (ζ.im + θ)) (by linarith [Real.pi_pos]) hζ
      simpa [norm_exp, exp_re, mul_comm] using
        mul_le_mul_of_nonneg_right hc (Real.exp_pos ζ.re).le
  have hw := (hasAsymptoticExpansion_integral_cexp_smul_cpow_seq hα hγ hint hq).comp_tendsto he
  have hw' := (hw.mul_left (fun _ => exp (θ * I))).smul_scale
    (ψ := fun n ζ => exp (-α n * ζ)) (κ := fun n => exp (θ * I * (1 - α n))) (fun n => by
      filter_upwards [hphase] with ζ hζ
      have hlog : log (exp (ζ + θ * I)) = ζ + θ * I := by
        apply log_exp <;> simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one,
          I_re, mul_zero, sub_zero] <;> linarith [(abs_le.mp hζ).1, (abs_le.mp hζ).2,
            Real.pi_pos]
      rw [cpow_def_of_ne_zero (exp_ne_zero _), hlog, ← exp_add, ← exp_add]
      congr 1
      ring)
  have hc : (fun n => exp (θ * I * (1 - α n)) •
      (Gamma (α n) • (exp (θ * I * (α n - 1)) * a n))) =
      (fun n => Gamma (α n) * a n) := by
    funext n
    simp only [smul_eq_mul]
    have hcancel : exp (θ * I * (1 - α n)) * exp (θ * I * (α n - 1)) = 1 := by
      rw [← exp_add, show θ * I * (1 - α n) + θ * I * (α n - 1) = 0 by ring, exp_zero]
    calc _ = (exp (θ * I * (1 - α n)) * exp (θ * I * (α n - 1))) *
        (Gamma (α n) * a n) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [hc] at hw'
  convert hw' using 1
  funext ζ
  unfold rayLaplace
  simp only [Function.comp_def, smul_eq_mul]

end DLMF.AsymptoticApproximations
