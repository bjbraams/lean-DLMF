/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.ParabolicCylinder.UniformLG2.NegativeParameterEstimates
public import DLMF.ParabolicCylinder.UniformLG2.PositiveParameterEstimates
public import DLMF.ParabolicCylinder.UniformLG2.ExpansionAlgebra
public import DLMF.ParabolicCylinder.UniformLG2.UniformExpansions

/-!
# Uniform expansions of parabolic cylinder functions: second stage

A general form of the recessive Liouville–Green core of `DLMF.ParabolicCylinder.UniformLG`
(`pcfLG2_core`): for any amplitude `A` with `ξ' = A⁻²` on `(b, ∞)`, any coefficient family
satisfying the Liouville–Green recursion with uniform bounds and limits at `+∞`, and any solution
`U` of `U'' = μ⁴A⁻⁴U` normalised at `+∞`, the expansion of `U` and of `U'` holds with explicit
constants. It is applied here to Temme's form of the expansion of `U(-½μ², μt√2)` (DLMF 12.10.31),
whose coefficients `φ_s(τ(t))` satisfy the Liouville–Green recursion by the polynomial recursion
DLMF 12.10.33 (`pcfLG2_temme_rec`) and tend to `0` at `t = ∞` for `s ≥ 1`, so that the
normalizer is exactly `h(μ)`.

For positive parameter `a = ½μ²` the equation `w'' = μ⁴(t²+1)w` has no turning points, and the
core applies on every half-line `(b, ∞)` with constants uniform in `b`
(`pcfLG2_pos_core`), with the real coefficients `Ā_s = Re(i^s u_s(-it))/(t²+1)^{3s/2}`
(DLMF 12.10.27). Comparing the limits at `+∞` (DLMF 12.9.1) and at `-∞` (DLMF 12.2.15 with
DLMF 12.9.1–12.9.2) gives the formal identity `(∑ γ_j (u/2)^{-j})(∑ c_s u^{-s}) =
∑ (-1)^s c_s u^{-s}` (`pcfLG2_gamma_identity`), where `c_s` is the coefficient of `t^{3s}` in
`u_s`. Since the even `c_s`, `s ≥ 2`, vanish, this yields DLMF 12.10.14 for the normalizer of
DLMF 12.10.3.

## Main results

* `pcfLG2_core`: the general recessive Liouville–Green core.
* `pcfU_temme_uniform`: DLMF 12.10.31.
* `pcfLG2_gamma_identity`: the normalizer identity in formal form.
* `pcf_negative_parameter_uniform_U_normalizer`: DLMF 12.10.3 with a normalizer satisfying
  DLMF 12.10.14 (`IsCylinderGNormalizer`).
* `pcf_positive_parameter_uniform`: DLMF 12.10.25 and 12.10.29 with a normalizer satisfying
  DLMF 12.10.28.
* `pcf_negative_parameter_uniform_U_UDeriv`: DLMF 12.10.3 and 12.10.4 (the `U`- and `U'`-parts
  of `pcf_negative_parameter_uniform`) with one normalizer satisfying DLMF 12.10.14.
-/
