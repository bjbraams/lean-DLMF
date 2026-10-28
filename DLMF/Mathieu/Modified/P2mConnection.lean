/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Mathieu.Modified.P2mConnection.AngularKernels
public import DLMF.Mathieu.Modified.P2mConnection.RadialAndMonodromy

/-!
# Connection formulas of the radial Mathieu functions: proofs (DLMF §28.22)

Helpers for `DLMF.Mathieu.Modified.Connection`:

* nonvanishing of `A^{2n}_0`, `A^{2n+1}_1`, `B^{2n+1}_1`, `B^{2n+2}_2` for `q ≠ 0` (from the
  recurrences 28.4.5–28.4.8 and the normalizations 28.4.9–28.4.12);
* the Bessel-product sums `∑ (-1)^ℓ A_{2ℓ} J_ℓ(h)²`, `∑ (-1)^ℓ A_{2ℓ+1} J_ℓ(h) J_{ℓ+1}(h)`,
  `∑ B_{2ℓ+1} J_ℓ(ih) J_{ℓ+1}(ih)` (and the analogue for `se_{2n+2}`), evaluated by the product
  integral 10.9.26, Bessel's integral 10.9.2, Fubini and the integral equations 28.10.1–28.10.8;
  these give the values of `Mc^{(1)}_m`, `Ms^{(1)}_m` at `z = 0` or `z = ∓πi/2` through the
  cross-product series 28.24.2–28.24.5;
* parity and proportionality of `Mc^{(1)}_m`, `Ms^{(1)}_m` to `Ce_m`, `Se_m` (ODE uniqueness);
* the monodromy `z ↦ z + πi` of the second kind, giving 28.22.3–28.22.4.
-/
