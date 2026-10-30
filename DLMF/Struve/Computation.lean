/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.SeriesAndEquations

/-!
# Mathematical approximation claims in DLMF computational sections

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Struve

/-- Struve functions of natural order are real on the real axis. -/
theorem struveH_nat_ofReal_im (n : ℕ) (x : ℝ) : (struveH n x).im = 0 := by
  have hterm : ∀ k : ℕ, ((-1:ℂ)^k*((x:ℂ)/2)^(2*k)*struveCoeff n k).im = 0 := by
    intro k
    have : (-1:ℂ)^k*((x:ℂ)/2)^(2*k)*struveCoeff n k =
        (((-1:ℝ)^k*(x/2)^(2*k)/(Real.Gamma (k+3/2)*Real.Gamma (k+n+3/2)) : ℝ) : ℂ) := by
      rw [struveCoeff, show (k:ℂ)+3/2 = ((k+3/2:ℝ):ℂ) by push_cast; ring,
        show (k:ℂ)+(n:ℂ)+3/2 = ((k+n+3/2:ℝ):ℂ) by push_cast; ring, Gamma_ofReal, Gamma_ofReal]
      push_cast; ring
    rw [this, ofReal_im]
  have hs := Complex.hasSum_im (hasSum_struveHCore n x)
  simp only [hterm] at hs
  have hcore : (struveHCore n x).im = 0 := hs.unique hasSum_zero
  have hpow : ((x:ℂ)/2)^((n:ℂ)+1) = (((x/2)^(n+1) : ℝ) : ℂ) := by
    rw [show (n:ℂ)+1 = ((n+1:ℕ):ℂ) by push_cast; ring, cpow_natCast]; push_cast; ring
  rw [struveH, hpow, mul_im, ofReal_im, ofReal_re, hcore]; ring

/- DLMF 11.8, 11.13–16 contain bibliographic guidance and numerical
method recommendations. The convergence statements in 11.13(ii) are covered by
the HasSum declarations. No running-time, cancellation, or numerical-stability
bound is inferred from qualitative computational recommendations. Tables in
11.14 are bibliographies of external tables, not numeric tables reproduced in DLMF.
The approximations in 11.15(ii), a polynomial approximation of 𝐇₀, 𝐇₁ on [0, 3] with
error 12·10⁻⁹ and a rational approximation of 𝐊₀, 𝐊₁ on [3, ∞) with error 25·10⁻⁹, are
numerical accuracy claims and are excluded: numerical (removed 2026-10-21). -/

end DLMF.Struve
