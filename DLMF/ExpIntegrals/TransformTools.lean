/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.ExpIntegrals.TransformTools.LaplaceAndFourier
public import DLMF.ExpIntegrals.TransformTools.QuadraticMoments

/-!
# Tools for Laplace transforms and integrals of exponential and trigonometric integrals

Helper results for DLMF §§6.14–6.15 (`DLMF/ExpIntegrals/ZerosIntegrals.lean`):

* elementary complex Laplace transforms `∫₀^∞ e^{-at} e^{-ct}`, `cos(ut)`, `sin(ut)`;
* the representations `E₁(t) = ∫₁^∞ e^{-tu}/u du`, `Si(t) = ∫₀¹ sin(tu)/u du` and
  `Ein(t) - Cin(t) = ∫₀¹ (cos(tu) - e^{-tu})/u du`;
* Fubini swaps for Laplace transforms of such parametric integrals;
* the closed forms `∫₁^∞ du/((a+u)u) = log(1+a)/a` and
  `∫₀¹ du/(a²+u²) = (π/2 - arctan a)/a` for complex `a` (the latter through the
  principal-branch identity `log((1+ia)/(1-ia)) = log(1+ia) - log(1-ia)`, `Re a > 0`);
* the squared and product integrals of `E₁`, `Ci`, `Si - π/2` (DLMF 6.14.4–6.14.7), by
  integration by parts and explicit antiderivatives;
* for the sums of DLMF §6.15: the Laplace representations of the auxiliary functions `f`, `g`,
  summed geometrically, and evaluated through Binet's formulas, namely the digamma kernel
  integral DLMF 5.9.15 (`DLMF.Gamma.digamma_coth`) and Binet's second formula DLMF 5.9.10
  (`DLMF.Gamma.log_Gamma_binet_arctan`), both from `DLMF/Gamma`.

Helper names carry the prefix `eiTr_`.
-/
