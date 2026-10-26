/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.Properties

/-!
# Modified Mathieu functions: connection formulas (DLMF §28.22)

The radial functions of the first and second kinds in terms of `Ce_m`, `Se_m`, `Fe_m`, `Ge_m`
with the joining factors `g_{e,m}`, `g_{o,m}`, `f_{e,m}`, `f_{o,m}` (defined in
`DLMF.Mathieu.Modified.Defs` by 28.22.5–28.22.10), and, for noninteger `ν`, `M^{(1)}_ν` in
terms of `Me_ν` and `M^{(2)}_ν` in terms of `M^{(1)}_{±ν}`. All formulas were checked
numerically (`h = 1.2`, `m ≤ 4`, `ν = 0.3`). Real `h > 0` throughout (DLMF's joining factors
are defined for real `h`); `q = h²`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

/-- **Connection formula** (DLMF 28.22.1), `h > 0`, `m = 0, 1, …`:
`Mc^{(1)}_m(z, h) = √(2/π) (g_{e,m}(h) ce_m(0, h²))⁻¹ Ce_m(z, h²)`. -/
@[dlmf 28.22.E1]
theorem radialMathieuMc_one_eq (m : ℕ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMc 1 m z h = Real.sqrt (2 / π) / (mathieuJoinGe m h * mathieuCe m 0 (h ^ 2)) *
      modMathieuCe m z ((h ^ 2 : ℝ) : ℂ) := by
  sorry

/-- **Connection formula** (DLMF 28.22.2), `h > 0`, `m = 1, 2, …`:
`Ms^{(1)}_m(z, h) = √(2/π) (g_{o,m}(h) se'_m(0, h²))⁻¹ Se_m(z, h²)`. -/
@[dlmf 28.22.E2]
theorem radialMathieuMs_one_eq {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMs 1 m z h = Real.sqrt (2 / π) /
      (mathieuJoinGo m h * deriv (fun x => mathieuSe m x (h ^ 2)) 0) *
      modMathieuSe m z ((h ^ 2 : ℝ) : ℂ) := by
  sorry

/-- **Connection formula** (DLMF 28.22.3), `h > 0`, `m = 0, 1, …`:
`Mc^{(2)}_m(z, h) = √(2/π) (g_{e,m} ce_m(0, h²))⁻¹
(-f_{e,m} Ce_m(z, h²) + 2/(π C_m(h²)) Fe_m(z, h²))`. -/
@[dlmf 28.22.E3]
theorem radialMathieuMc_two_eq (m : ℕ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMc 2 m z h = Real.sqrt (2 / π) / (mathieuJoinGe m h * mathieuCe m 0 (h ^ 2)) *
      (-mathieuJoinFe m h * modMathieuCe m z ((h ^ 2 : ℝ) : ℂ) +
        2 / (π * mathieuFeC m (h ^ 2)) * modMathieuFe m z (h ^ 2)) := by
  sorry

/-- **Connection formula** (DLMF 28.22.4), `h > 0`, `m = 1, 2, …`:
`Ms^{(2)}_m(z, h) = √(2/π) (g_{o,m} se'_m(0, h²))⁻¹
(-f_{o,m} Se_m(z, h²) - 2/(π S_m(h²)) Ge_m(z, h²))`. -/
@[dlmf 28.22.E4]
theorem radialMathieuMs_two_eq {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    radialMathieuMs 2 m z h = Real.sqrt (2 / π) /
      (mathieuJoinGo m h * deriv (fun x => mathieuSe m x (h ^ 2)) 0) *
      (-mathieuJoinFo m h * modMathieuSe m z ((h ^ 2 : ℝ) : ℂ) -
        2 / (π * mathieuGeS m (h ^ 2)) * modMathieuGe m z (h ^ 2)) := by
  sorry

/-- **Values at `z = 0`** (DLMF 28.22.11), `h > 0`:
`Mc^{(2)'}_m(0, h) = √(2/π) g_{e,m}(h)` and `Ms^{(2)}_m(0, h) = -√(2/π) g_{o,m}(h)` (`m ≥ 1`
for the second). -/
@[dlmf 28.22.E11]
theorem radialMathieu_two_zero (m : ℕ) {h : ℝ} (hh : 0 < h) :
    deriv (fun z => radialMathieuMc 2 m z h) 0 = Real.sqrt (2 / π) * mathieuJoinGe m h ∧
      (m ≠ 0 → radialMathieuMs 2 m 0 h = -(Real.sqrt (2 / π) * mathieuJoinGo m h)) := by
  sorry

/-- **Initial values of the second solutions** (DLMF 28.22.12), `h > 0`:
`fe'_m(0, h²) = ½π C_m(h²) g_{e,m}(h)² ce_m(0, h²)` and
`ge_m(0, h²) = ½π S_m(h²) g_{o,m}(h)² se'_m(0, h²)` (`m ≥ 1` for the second). -/
@[dlmf 28.22.E12]
theorem mathieuFe_ge_zero_eq_joinG (m : ℕ) {h : ℝ} (hh : 0 < h) :
    deriv (fun z => mathieuFe m z (h ^ 2)) 0 =
        π / 2 * mathieuFeC m (h ^ 2) * mathieuJoinGe m h ^ 2 * mathieuCe m 0 (h ^ 2) ∧
      (m ≠ 0 → mathieuGe m 0 (h ^ 2) = π / 2 * mathieuGeS m (h ^ 2) * mathieuJoinGo m h ^ 2 *
        deriv (fun z => mathieuSe m z (h ^ 2)) 0) := by
  sorry

/-- **Noninteger order** (DLMF 28.22.13), `ν` real, `ν ∉ ℤ`, `h > 0`, `me_ν(0, h²) ≠ 0`:
`M^{(1)}_ν(z, h) = (M^{(1)}_ν(0, h) / me_ν(0, h²)) Me_ν(z, h²)`. (DLMF's further remark, that
`M^{(1)}_ν(0, h)` is best computed from 28.24.1 with an index of maximal `|c^ν_{2n}|`, is
computational advice; cf. `modMathieuIndex`.) -/
@[dlmf 28.22.E13]
theorem modMathieuM_one_eq_modMathieuMe {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ}
    (hh : 0 < h) (hme : mathieuMe ν 0 ((h : ℂ) ^ 2) ≠ 0) (z : ℂ) :
    modMathieuM 1 ν z h =
      modMathieuM 1 ν 0 h / mathieuMe ν 0 ((h : ℂ) ^ 2) * modMathieuMe ν z ((h : ℂ) ^ 2) := by
  sorry

/-- **Noninteger order** (DLMF 28.22.14), `ν` real, `ν ∉ ℤ`, `h > 0`:
`M^{(2)}_ν(z, h) = cot(νπ) M^{(1)}_ν(z, h) - M^{(1)}_{-ν}(z, h) / sin(νπ)`. -/
@[dlmf 28.22.E14]
theorem modMathieuM_two_eq {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) {h : ℝ} (hh : 0 < h)
    (z : ℂ) :
    modMathieuM 2 ν z h = Complex.cot (ν * π) * modMathieuM 1 ν z h -
      modMathieuM 1 (-(ν : ℂ)) z h / Complex.sin (ν * π) := by
  sorry

end DLMF.Mathieu
