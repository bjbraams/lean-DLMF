/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.ZMod

/-!
# Parseval identities for the finite discrete Fourier transform

Andrews, Askey and Roy, *Special Functions*, §1.10, pp. 41–43
(synopsis AAR-1.10.1–1.10.11). Mathlib's `ZMod.dft` has negative Fourier
sign; the source has positive sign. Reflection of the frequency index converts
one convention to the other and leaves these finite sums unchanged.
-/

@[expose] public section

namespace ZMod

/-- The finite Fourier transform scales the Hermitian inner product by the group order.
Andrews–Askey–Roy, *Special Functions*, §1.10, pp. 41–43
(synopsis AAR-1.10.1–1.10.11). The order must be nonzero so that `ZMod N` is finite. -/
theorem sum_dft_mul_conj_dft {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    (∑ k : ZMod N, dft f k * star (dft g k)) =
      (N : ℂ) * ∑ k : ZMod N, f k * star (g k) := by
  sorry

/-- Parseval's finite Fourier norm identity with the unnormalized transform.
Andrews–Askey–Roy, *Special Functions*, §1.10, pp. 41–43
(synopsis AAR-1.10.1–1.10.11). -/
theorem sum_norm_dft_sq {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    (∑ k : ZMod N, ‖dft f k‖ ^ 2) = (N : ℝ) * ∑ k : ZMod N, ‖f k‖ ^ 2 := by
  have h := congrArg Complex.re (sum_dft_mul_conj_dft f f)
  simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using h

end ZMod
