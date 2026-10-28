/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.CoalescingSaddles.CanonicalIntegrals.ContoursAndSymmetries
public import DLMF.CoalescingSaddles.CanonicalIntegrals.OscillatoryRepresentations

/-!
# Catastrophes and canonical integrals (DLMF §36.2)

Statements acquired from the NIST DLMF (version 1.2.8), checked 2026-10-26.

The canonical integrals are defined in `DLMF.CoalescingSaddles.Basic` as absolutely convergent
integrals over rotated contours. This file proves their integrability, states the agreement with
the oscillatory real integrals of DLMF (36.2.4, 36.2.5; admitted), and acquires the alternative
representations 36.2.6–36.2.9, the special cases 36.2.12–36.2.21, 36.2.28–36.2.29 and the
symmetries 36.2.22–36.2.27.

## Main results

* `integrable_cuspoidIntegrand`: the rotated-contour integrand is integrable (any phase `κ > 0`);
* `cuspoidIntegral_zero_dim` (36.2.12), `cuspoidIntegral_one` (36.2.13, Airy),
  `cuspoidIntegral_at_zero` (36.2.15);
* `cuspoidIntegral_even_symm` (36.2.22), `cuspoidIntegral_odd_conj` (36.2.23);
* `hyperbolicUmbilicIntegral_z_zero` (36.2.21), `hyperbolicUmbilicIntegral_zero` (36.2.18),
  `hyperbolicUmbilicIntegral_conj` (36.2.24), `hyperbolicUmbilicIntegral_swap` (36.2.27);
* `ellipticUmbilicIntegral_rotate` (36.2.26).
-/
