/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Properties
public import DLMF.CoalescingSaddles.Basic

/-!
# Integral identities for the canonical integrals: DLMF §36.9

The squared moduli of the canonical integrals as integrals of canonical integrals of lower
"dimension" (DLMF 36.9.1–36.9.9). Notation: `Ψ₁(x) = cuspoidIntegral 1 ![x]`,
`Ψ₂(x, y) = cuspoidIntegral 2 ![x, y]`, `Ψ₃(x, y, z) = cuspoidIntegral 3 ![x, y, z]`.

Where the integral of DLMF converges absolutely (36.9.1, 36.9.2, 36.9.4–36.9.8) the statement
includes the integrability of the integrand; 36.9.3 converges only conditionally (the integrand is
of size `u^{-1/2}`) and is stated as the limit of `∫_0^R` as `R → ∞`; 36.9.9 is stated as the
iterated integral of DLMF, with the inner `θ`-integral over `[0, 2π]` and the outer `u`-integral
as a limit of `∫_0^R` (the integrand `Ai(w)Bi(w̄)` grows like `exp(c u³)` in some directions, so
the double integral is not absolutely convergent).

Numerical checks (mpmath, rotated-contour quadrature for the canonical integrals): 36.9.1–36.9.8
agree to 6–15 digits at sample points. For 36.9.9 the inner `θ`-integral involves cancellation
from `10^{50}` and the partial `u`-integrals oscillate; the check was inconclusive (see the
ledger).
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace DLMF.CoalescingSaddles

/-- `|Ψ₁(x)|² = 2^{5/3} ∫_0^∞ Ψ₁(2^{2/3}(3u² + x)) du` (DLMF 36.9.1). -/
@[dlmf 36.9.E1]
theorem normSq_cuspoidIntegral_one_eq_integral (x : ℝ) :
    IntegrableOn (fun u : ℝ => cuspoidIntegral 1 ![(2 : ℝ) ^ (2 / 3 : ℝ) * (3 * u ^ 2 + x)])
        (Ioi 0) ∧
      ((‖cuspoidIntegral 1 ![x]‖ ^ 2 : ℝ) : ℂ) = (((2 : ℝ) ^ (5 / 3 : ℝ) : ℝ) : ℂ) *
        ∫ u in Ioi (0 : ℝ), cuspoidIntegral 1 ![(2 : ℝ) ^ (2 / 3 : ℝ) * (3 * u ^ 2 + x)] := by
  sorry

/-- `Ai(x)² = (2^{2/3}/π) ∫_0^∞ Ai(2^{2/3}(u² + x)) du` for real `x` (DLMF 36.9.2). -/
@[dlmf 36.9.E2]
theorem airyAi_sq_eq_integral (x : ℝ) :
    IntegrableOn (fun u : ℝ => Airy.airyAi (((2 : ℝ) ^ (2 / 3 : ℝ) * (u ^ 2 + x) : ℝ) : ℂ))
        (Ioi 0) ∧
      Airy.airyAi (x : ℂ) ^ 2 = (((2 : ℝ) ^ (2 / 3 : ℝ) / π : ℝ) : ℂ) *
        ∫ u in Ioi (0 : ℝ), Airy.airyAi (((2 : ℝ) ^ (2 / 3 : ℝ) * (u ^ 2 + x) : ℝ) : ℂ) := by
  sorry

/-- `|Ψ₁(x)|² = √(8π/3) ∫_0^∞ u^{-1/2} cos(2u(x + u²) + π/4) du` (DLMF 36.9.3), as an improper
integral (`∫_0^R → |Ψ₁(x)|²` as `R → ∞`; the integral is not absolutely convergent). -/
@[dlmf 36.9.E3]
theorem normSq_cuspoidIntegral_one_eq_improper (x : ℝ) :
    Tendsto (fun R : ℝ => Real.sqrt (8 * π / 3) *
        ∫ u in (0 : ℝ)..R, u ^ (-(1 / 2 : ℝ)) * Real.cos (2 * u * (x + u ^ 2) + π / 4))
      atTop (𝓝 (‖cuspoidIntegral 1 ![x]‖ ^ 2)) := by
  sorry

/-- `|Ψ₂(x, y)|² = ∫_0^∞ (Ψ₁((4u³ + 2uy + x)/u^{1/3}) + Ψ₁((4u³ + 2uy - x)/u^{1/3})) du/u^{1/3}`
(DLMF 36.9.4). -/
@[dlmf 36.9.E4]
theorem normSq_cuspoidIntegral_two_eq_integral (x y : ℝ) :
    IntegrableOn (fun u : ℝ =>
        (cuspoidIntegral 1 ![(4 * u ^ 3 + 2 * u * y + x) / u ^ (1 / 3 : ℝ)] +
          cuspoidIntegral 1 ![(4 * u ^ 3 + 2 * u * y - x) / u ^ (1 / 3 : ℝ)]) /
          ((u ^ (1 / 3 : ℝ) : ℝ) : ℂ)) (Ioi 0) ∧
      ((‖cuspoidIntegral 2 ![x, y]‖ ^ 2 : ℝ) : ℂ) = ∫ u in Ioi (0 : ℝ),
        (cuspoidIntegral 1 ![(4 * u ^ 3 + 2 * u * y + x) / u ^ (1 / 3 : ℝ)] +
          cuspoidIntegral 1 ![(4 * u ^ 3 + 2 * u * y - x) / u ^ (1 / 3 : ℝ)]) /
          ((u ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
  sorry

/-- `|Ψ₂(x, y)|² = 2 ∫_0^∞ cos(2xu) Ψ₁(2u^{2/3}(y + 2u²)) du/u^{1/3}` (DLMF 36.9.5). -/
@[dlmf 36.9.E5]
theorem normSq_cuspoidIntegral_two_eq_integral_cos (x y : ℝ) :
    IntegrableOn (fun u : ℝ => ((Real.cos (2 * x * u) / u ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        cuspoidIntegral 1 ![2 * u ^ (2 / 3 : ℝ) * (y + 2 * u ^ 2)]) (Ioi 0) ∧
      ((‖cuspoidIntegral 2 ![x, y]‖ ^ 2 : ℝ) : ℂ) = 2 * ∫ u in Ioi (0 : ℝ),
        ((Real.cos (2 * x * u) / u ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
          cuspoidIntegral 1 ![2 * u ^ (2 / 3 : ℝ) * (y + 2 * u ^ 2)] := by
  sorry

/-- `|Ψ₃(x, y, z)|² = 2^{4/5} ∫_{-∞}^{∞} Ψ₃(2^{4/5}(x + 2uy + 3u²z + 5u⁴), 0, 2^{2/5}(z + 10u²)) du`
(DLMF 36.9.6). -/
@[dlmf 36.9.E6]
theorem normSq_cuspoidIntegral_three_eq_integral (x y z : ℝ) :
    Integrable (fun u : ℝ => cuspoidIntegral 3
        ![(2 : ℝ) ^ (4 / 5 : ℝ) * (x + 2 * u * y + 3 * u ^ 2 * z + 5 * u ^ 4), 0,
          (2 : ℝ) ^ (2 / 5 : ℝ) * (z + 10 * u ^ 2)]) ∧
      ((‖cuspoidIntegral 3 ![x, y, z]‖ ^ 2 : ℝ) : ℂ) = (((2 : ℝ) ^ (4 / 5 : ℝ) : ℝ) : ℂ) *
        ∫ u : ℝ, cuspoidIntegral 3
          ![(2 : ℝ) ^ (4 / 5 : ℝ) * (x + 2 * u * y + 3 * u ^ 2 * z + 5 * u ^ 4), 0,
            (2 : ℝ) ^ (2 / 5 : ℝ) * (z + 10 * u ^ 2)] := by
  sorry

/-- `|Ψ₃(x, y, z)|² = (2^{7/4}/5^{1/4}) ∫_0^∞ Re(e^{2iu(u⁴ + zu² + x)}
  Ψ₂((2^{7/4}/5^{1/4}) y u^{3/4}, √(2u/5)(3z + 10u²))) du/u^{1/4}` (DLMF 36.9.7). -/
@[dlmf 36.9.E7]
theorem normSq_cuspoidIntegral_three_eq_integral_re (x y z : ℝ) :
    IntegrableOn (fun u : ℝ => (exp (2 * I * u * (u ^ 4 + z * u ^ 2 + x)) * cuspoidIntegral 2
        ![(2 : ℝ) ^ (7 / 4 : ℝ) / (5 : ℝ) ^ (1 / 4 : ℝ) * y * u ^ (3 / 4 : ℝ),
          Real.sqrt (2 * u / 5) * (3 * z + 10 * u ^ 2)]).re / u ^ (1 / 4 : ℝ)) (Ioi 0) ∧
      ‖cuspoidIntegral 3 ![x, y, z]‖ ^ 2 = (2 : ℝ) ^ (7 / 4 : ℝ) / (5 : ℝ) ^ (1 / 4 : ℝ) *
        ∫ u in Ioi (0 : ℝ), (exp (2 * I * u * (u ^ 4 + z * u ^ 2 + x)) * cuspoidIntegral 2
          ![(2 : ℝ) ^ (7 / 4 : ℝ) / (5 : ℝ) ^ (1 / 4 : ℝ) * y * u ^ (3 / 4 : ℝ),
            Real.sqrt (2 * u / 5) * (3 * z + 10 * u ^ 2)]).re / u ^ (1 / 4 : ℝ) := by
  sorry

/-- `|Ψ^{(H)}(x, y, z)|² = 8π²(2/9)^{1/3} ∫∫ Ai((4/3)^{1/3}(x + zv + 3u²))
  Ai((4/3)^{1/3}(y + zu + 3v²)) du dv` over `ℝ²` (DLMF 36.9.8). -/
@[dlmf 36.9.E8]
theorem normSq_hyperbolicUmbilicIntegral_eq_integral (x y z : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
        Airy.airyAi (((4 / 3 : ℝ) ^ (1 / 3 : ℝ) * (x + z * p.2 + 3 * p.1 ^ 2) : ℝ) : ℂ) *
          Airy.airyAi (((4 / 3 : ℝ) ^ (1 / 3 : ℝ) * (y + z * p.1 + 3 * p.2 ^ 2) : ℝ) : ℂ)) ∧
      ((‖hyperbolicUmbilicIntegral x y z‖ ^ 2 : ℝ) : ℂ) =
        8 * (π : ℂ) ^ 2 * (((2 / 9 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ∫ p : ℝ × ℝ,
          Airy.airyAi (((4 / 3 : ℝ) ^ (1 / 3 : ℝ) * (x + z * p.2 + 3 * p.1 ^ 2) : ℝ) : ℂ) *
            Airy.airyAi (((4 / 3 : ℝ) ^ (1 / 3 : ℝ) * (y + z * p.1 + 3 * p.2 ^ 2) : ℝ) : ℂ) := by
  sorry

/-- `|Ψ^{(E)}(x, y, z)|² = (8π²/3^{2/3}) ∫_0^∞ ∫_0^{2π} Re(Ai(3^{-1/3}(x + iy + 2zue^{iθ} +
  3u²e^{-2iθ})) Bi(3^{-1/3}(x - iy + 2zue^{-iθ} + 3u²e^{2iθ}))) u dθ du` (DLMF 36.9.9), as the
iterated integral: inner integral over `θ ∈ [0, 2π]`, outer integral over `u` as the limit of
`∫_0^R` as `R → ∞`. -/
@[dlmf 36.9.E9]
theorem normSq_ellipticUmbilicIntegral_eq_integral (x y z : ℝ) :
    Tendsto (fun R : ℝ => 8 * π ^ 2 / (3 : ℝ) ^ (2 / 3 : ℝ) * ∫ u in (0 : ℝ)..R,
        (∫ θ in (0 : ℝ)..2 * π,
          (Airy.airyAi ((((3 : ℝ) ^ (1 / 3 : ℝ))⁻¹ : ℝ) * (x + I * y +
              2 * z * u * exp (I * θ) + 3 * u ^ 2 * exp (-2 * I * θ))) *
            Airy.airyBi ((((3 : ℝ) ^ (1 / 3 : ℝ))⁻¹ : ℝ) * (x - I * y +
              2 * z * u * exp (-I * θ) + 3 * u ^ 2 * exp (2 * I * θ)))).re) * u)
      atTop (𝓝 (‖ellipticUmbilicIntegral x y z‖ ^ 2)) := by
  sorry

end DLMF.CoalescingSaddles
