/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Properties
public import DLMF.Airy.SquareTools
public import DLMF.CoalescingSaddles.CanonicalIntegrals.ContoursAndSymmetries
public import DLMF.CoalescingSaddles.Basic

/-!
# Integral identities for the canonical integrals

The squared moduli of the canonical integrals as integrals of canonical integrals of lower
"dimension" (DLMF §36.9, 36.9.1–36.9.9). Notation: `Ψ₁(x) = cuspoidIntegral 1 ![x]`,
`Ψ₂(x, y) = cuspoidIntegral 2 ![x, y]`, `Ψ₃(x, y, z) = cuspoidIntegral 3 ![x, y, z]`.

## Main results

* `normSq_cuspoidIntegral_one_eq_integral`, `airyAi_sq_eq_integral`: `|Ψ₁(x)|²` and `Ai(x)²`
  as integrals of `Ψ₁` and `Ai` (DLMF 36.9.1, 36.9.2).
* `normSq_cuspoidIntegral_one_eq_improper`: `|Ψ₁(x)|²` as an improper cosine integral
  (DLMF 36.9.3).
* `normSq_cuspoidIntegral_two_eq_integral`, `normSq_cuspoidIntegral_two_eq_integral_cos`:
  `|Ψ₂(x, y)|²` as integrals of `Ψ₁` (DLMF 36.9.4, 36.9.5).
* `normSq_cuspoidIntegral_three_eq_integral`, `normSq_cuspoidIntegral_three_eq_integral_re`:
  `|Ψ₃(x, y, z)|²` as integrals of `Ψ₃` and `Ψ₂` (DLMF 36.9.6, 36.9.7).
* `normSq_hyperbolicUmbilicIntegral_eq_integral`: `|Ψ^{(H)}|²` as a double integral of Airy
  functions (DLMF 36.9.8).
* `normSq_ellipticUmbilicIntegral_eq_integral`: `|Ψ^{(E)}|²` as an iterated integral of
  `Ai · Bi` (DLMF 36.9.9).

## Implementation notes

Where the integral of DLMF converges absolutely (36.9.1, 36.9.2, 36.9.4–36.9.8) the statement
includes the integrability of the integrand; 36.9.3 converges only conditionally (the integrand is
of size `u^{-1/2}`) and is stated as the limit of `∫_0^R` as `R → ∞`; 36.9.9 is stated as the
iterated integral of DLMF, with the inner `θ`-integral over `[0, 2π]` and the outer `u`-integral
as a limit of `∫_0^R` (the integrand `Ai(w)Bi(w̄)` grows like `exp(c u³)` in some directions, so
the double integral is not absolutely convergent).

Numerical checks (mpmath, rotated-contour quadrature for the canonical integrals): 36.9.1–36.9.8
agree to 6–15 digits at sample points. For 36.9.9 the inner `θ`-integral involves cancellation
from `10^{50}` and the partial `u`-integrals oscillate; the check was inconclusive.
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
  set a : ℝ := (3 : ℝ) ^ (1 / 3 : ℝ) with ha_def
  have ha : 0 < a := by positivity
  have ha3 : a ^ 3 = 3 := by
    rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  set c : ℝ := DLMF.Airy.AiSquare.scale with hc_def
  have hc : c = (2 : ℝ) ^ (2 / 3 : ℝ) := rfl
  have hc53 : (2 : ℝ) ^ (5 / 3 : ℝ) = 2 * c := by
    rw [hc, show (5 / 3 : ℝ) = 1 + 2 / 3 by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_one]
  set g : ℝ → ℝ := fun t => DLMF.Airy.Real.airyAi (c * (x / a + t ^ 2)) with hg
  have hgi : Integrable g :=
    DLMF.Airy.AiSquare.integrable DLMF.Airy.AiSquare.decay_ai DLMF.Airy.AiSquare.continuous_ai
      DLMF.Airy.AiSquare.scale_pos (x / a)
  have hrep := DLMF.Airy.AiSquare.scale_mul_tailIntegral (x / a)
  have hF : DLMF.Airy.AiSquare.tailIntegral (x / a) = ∫ t in Ioi 0, g t := rfl
  have hfun : (fun u : ℝ => cuspoidIntegral 1 ![(2 : ℝ) ^ (2 / 3 : ℝ) * (3 * u ^ 2 + x)]) =
      fun u : ℝ => (((2 * π / a) * g (a * u) : ℝ) : ℂ) := by
    funext u
    rw [cuspoidIntegral_one, DLMF.Airy.airyAi_ofReal_eq, ← ha_def, ← hc]
    have : c * (3 * u ^ 2 + x) / a = c * (x / a + (a * u) ^ 2) := by
      field_simp
      rw [← ha3]; ring
    rw [this]; push_cast; ring
  have hint : Integrable (fun u : ℝ => (((2 * π / a) * g (a * u) : ℝ) : ℂ)) :=
    ((hgi.comp_mul_left' ha.ne').const_mul _).ofReal
  refine ⟨hfun ▸ hint.integrableOn, ?_⟩
  rw [hfun, integral_complex_ofReal, integral_const_mul,
    integral_comp_mul_left_Ioi g 0 ha, mul_zero, ← hF, cuspoidIntegral_one,
    DLMF.Airy.airyAi_ofReal_eq, hc53, ← ha_def]
  rw [norm_mul, norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have : ‖(2 * π / (a : ℂ))‖ = 2 * π / a := by
    rw [show (2 * π / (a : ℂ)) = ((2 * π / a : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [this, smul_eq_mul]
  have hc0 : 0 < c := DLMF.Airy.AiSquare.scale_pos
  have hF' : DLMF.Airy.AiSquare.tailIntegral (x / a) = π *
      DLMF.Airy.Real.airyAi (x / a) ^ 2 / c := by
    field_simp; linarith
  rw [hF']
  have hcC : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc0.ne'
  have haC : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  push_cast
  field_simp

/-- `Ai(x)² = (2^{2/3}/π) ∫_0^∞ Ai(2^{2/3}(u² + x)) du` for real `x` (DLMF 36.9.2). -/
@[dlmf 36.9.E2]
theorem airyAi_sq_eq_integral (x : ℝ) :
    IntegrableOn (fun u : ℝ => Airy.airyAi (((2 : ℝ) ^ (2 / 3 : ℝ) * (u ^ 2 + x) : ℝ) : ℂ))
        (Ioi 0) ∧
      Airy.airyAi (x : ℂ) ^ 2 = (((2 : ℝ) ^ (2 / 3 : ℝ) / π : ℝ) : ℂ) *
        ∫ u in Ioi (0 : ℝ), Airy.airyAi (((2 : ℝ) ^ (2 / 3 : ℝ) * (u ^ 2 + x) : ℝ) : ℂ) := by
  simp_rw [add_comm _ x]
  exact DLMF.Airy.airyAi_sq_eq_integral x

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
