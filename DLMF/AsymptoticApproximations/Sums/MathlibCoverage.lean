/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Mathlib coverage of DLMF §2.10

Pointers from DLMF §2.10 items to related Mathlib declarations; the DLMF statements themselves
are formalized in `DLMF.AsymptoticApproximations.Sums.EulerMaclaurin`.
-/

dlmf_upstream 2.10.E9 Finset.sum_range_by_parts
  "different convention: Abel summation over range n with partial sums from index 0"

dlmf_upstream 2.10.E8 Real.tendsto_harmonic_sub_log
  "partial: the leading terms, H_n - ln n → γ"
