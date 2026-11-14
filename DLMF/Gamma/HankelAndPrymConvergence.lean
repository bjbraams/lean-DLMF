/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.IntegralRepresentations.PrymAndOscillatory
public import DLMFMathlib.Analysis.Asymptotics.WatsonHankel

/-!
# Fixed-radius Hankel contours and normal convergence of Prym's series

Temme, *Special Functions* (1996), §§3.2–3.3, pp. 43–49,
synopses TEM-03-02 and TEM-03-04. The two banks of the negative cut
are correlated through the same logarithmic integrand.
-/

@[expose] public noncomputable section
open Complex Filter MeasureTheory Set
open scoped Real Topology
namespace DLMF.Gamma

/-- Prym's meromorphic partial sums converge locally uniformly away from their poles,
Temme §3.2.1, pp. 43–44, synopsis TEM-03-02. -/
theorem tendstoLocallyUniformlyOn_prymSeries :
    TendstoLocallyUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n / ((z + n) * n.factorial))
      prymSeries atTop {z : ℂ | ∀ n : ℕ, z ≠ -(n : ℂ)} := by
  sorry

/-- The fixed-radius Hankel formula is valid for every complex Gamma parameter,
Temme (3.6), pp. 48–49, synopsis TEM-03-04. Both banks and the circular arc
are absolutely integrable at every fixed positive radius. -/
theorem inv_Gamma_eq_hankel_fixed_radius (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun t : ℝ => exp (-t) *
      (exp (-a * ((Real.log t : ℂ) - Real.pi * I)) -
        exp (-a * ((Real.log t : ℂ) + Real.pi * I)))) (Ioi ρ) ∧
    IntervalIntegrable (fun θ : ℝ => exp (ρ * exp (θ * I)) *
      exp (-a * ((Real.log ρ : ℂ) + θ * I)) * (I * ρ * exp (θ * I)))
        volume (-Real.pi) Real.pi ∧
    (Complex.Gamma a)⁻¹ =
      ((∫ t : ℝ in Ioi ρ, exp (-t) *
        (exp (-a * ((Real.log t : ℂ) - Real.pi * I)) -
          exp (-a * ((Real.log t : ℂ) + Real.pi * I)))) +
        ∫ θ : ℝ in -Real.pi..Real.pi, exp (ρ * exp (θ * I)) *
          exp (-a * ((Real.log ρ : ℂ) + θ * I)) * (I * ρ * exp (θ * I))) /
        (2 * Real.pi * I) := by
  sorry

/-- The small circular arc vanishes in the unregularized Hankel limit for `Re(a)<1`,
Temme (3.6), pp. 48–49, synopsis TEM-03-04. -/
theorem tendsto_hankel_small_arc {a : ℂ} (ha : a.re < 1) :
    Tendsto (fun ρ : ℝ => ∫ θ : ℝ in -Real.pi..Real.pi,
      exp (ρ * exp (θ * I)) * exp (-a * ((Real.log ρ : ℂ) + θ * I)) *
        (I * ρ * exp (θ * I))) (𝓝[>] 0) (𝓝 0) := by
  sorry

end DLMF.Gamma
