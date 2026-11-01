/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.CoalescingSaddles.CanonicalIntegrals.ContoursAndSymmetries
public import DLMF.CoalescingSaddles.CanonicalIntegrals.OscillatoryRepresentations

/-!
# Catastrophes and canonical integrals

The canonical integrals of DLMF §36.2 are defined in `DLMF.CoalescingSaddles.Basic` as
absolutely convergent integrals over rotated contours. The files imported here prove their
integrability, the agreement with the oscillatory real integrals of DLMF (36.2.4, 36.2.5,
36.2.10, 36.2.11), the alternative representations 36.2.6–36.2.9, the special cases
36.2.12–36.2.21 and 36.2.28–36.2.29, and the symmetries 36.2.22–36.2.27.

## Main results

* `integrable_cuspoidIntegrand`: the rotated-contour integrand is integrable (any phase `κ > 0`).
* `hasIntegralWholeLine_cuspoidIntegral`, `hasIteratedIntegral_hyperbolicUmbilicIntegral`,
  `hasIteratedIntegral_ellipticUmbilicIntegral`: agreement with the improper real integrals
  (DLMF 36.2.4, 36.2.5).
* `ellipticUmbilicIntegral_eq_contour`, `ellipticUmbilicIntegral_eq_airy`,
  `hyperbolicUmbilicIntegral_eq_contour`, `hyperbolicUmbilicIntegral_eq_airy`: the alternative
  representations (DLMF 36.2.6–36.2.9).
* `cuspoidIntegral_zero_dim` (36.2.12), `cuspoidIntegral_one` (36.2.13, Airy),
  `cuspoidIntegral_at_zero` (36.2.15).
* `cuspoidIntegral_even_symm` (36.2.22), `cuspoidIntegral_odd_conj` (36.2.23).
* `hyperbolicUmbilicIntegral_z_zero` (36.2.21), `hyperbolicUmbilicIntegral_zero` (36.2.18),
  `hyperbolicUmbilicIntegral_conj` (36.2.24), `hyperbolicUmbilicIntegral_swap` (36.2.27).
* `ellipticUmbilicIntegral_rotate` (36.2.26).
-/
