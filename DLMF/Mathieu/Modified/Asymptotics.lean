/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.Properties
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion

/-!
# Modified Mathieu functions: asymptotics (DLMF §§28.25–28.26)

* 28.25.1–28.25.5: the asymptotic expansions of `M^{(3)}_ν`, `M^{(4)}_ν` for large `Re z`, with
  the coefficients `D^±_m` of the recurrence 28.25.3 (`modMathieuAsympD`); the initial values
  and the recurrence are proved from the definition.
* 28.26.1–28.26.5: Goldstein's expansions for large `h`; 28.26.1–28.26.2 are proved from the
  definitions of `Fc_m`, `Gc_m`, `Fs_m`, `Gs_m` and 28.20.13.

The expansion 28.25.1 and Goldstein's expansions 28.26.4–28.26.5 (with `Fs`, `Gs`) were
checked numerically (`ν = 0.3`, `h = 1.2`, `Re z ∈ {2.5, 3.5}`; `m ≤ 1`, `h ∈ {4, 8}`,
`z = 0.5`: the errors after the `h⁻³` terms scale like `h⁻⁴`).
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### §28.25 Asymptotic expansions for large `Re z` -/

/-- `D^±_{0} = 1` (DLMF 28.25.2). -/
@[dlmf 28.25.E2]
theorem modMathieuAsympD_zero (σ a h : ℂ) : modMathieuAsympD σ a h 0 = 1 := rfl

/-- The recurrence 28.25.3 for `m ≥ 0`, with `D_{-1} = 0` (DLMF 28.25.2):
`(m+1) D_{m+1} + ((m+½)² ± (m+¼) 8ih + 2h² - a) D_m ± (m-½)(8ihm) D_{m-1} = 0`, written with
`σ = ±1` and `D_{-1}` the first component of `modMathieuAsympDPair σ a h m`. -/
@[dlmf 28.25.E3, dlmf 28.25.E2]
theorem modMathieuAsympD_recurrence (σ a h : ℂ) (m : ℕ) :
    ((m : ℂ) + 1) * modMathieuAsympD σ a h (m + 1) +
        (((m : ℂ) + 1 / 2) ^ 2 + σ * ((m : ℂ) + 1 / 4) * (8 * I * h) + 2 * h ^ 2 - a) *
          modMathieuAsympD σ a h m +
        σ * ((m : ℂ) - 1 / 2) * (8 * I * h * m) * (modMathieuAsympDPair σ a h m).1 = 0 := by
  have hm : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  simp only [modMathieuAsympD, modMathieuAsympDPair]
  field_simp
  ring

/-- `D_{m-1}` in the recurrence is the previous coefficient: the first component of the pair at
`m + 1` is `D_m`, and at `0` it is `D_{-1} = 0` (DLMF 28.25.2). -/
@[dlmf 28.25.E2]
theorem modMathieuAsympDPair_fst (σ a h : ℂ) (m : ℕ) :
    (modMathieuAsympDPair σ a h (m + 1)).1 = modMathieuAsympD σ a h m ∧
      (modMathieuAsympDPair σ a h 0).1 = 0 :=
  ⟨rfl, rfl⟩

/-- **Asymptotic expansion of `M^{(3)}_ν`** for large `Re z` (DLMF 28.25.1, 28.25.4), fixed
`h ≠ 0` and `ν` (admissible), `δ > 0`:
`M^{(3)}_ν(z, h) ~ e^{i(2h cosh z - (ν/2+1/4)π)} (πh(cosh z+1))^{-1/2} ∑_m D^+_m (-4ih(cosh
z+1))^{-m}`
as `Re z → +∞` with `-π + δ ≤ ph h + Im z ≤ 2π - δ`, `a = λ_ν(h²)`. -/
@[dlmf 28.25.E1, dlmf 28.25.E4]
theorem modMathieuM_three_hasAsymptoticExpansion {ν h : ℂ} (hν : ModMathieuAdmissible ν h)
    (hh : h ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (modMathieuAsympFilter h (-π + δ) (2 * π - δ))
      (fun m z => modMathieuAsympPrefactor 1 ν h z * (-4 * I * h * (Complex.cosh z + 1))⁻¹ ^ m)
      (modMathieuAsympD 1 (mathieuLambda ν (h ^ 2)) h) (fun z => modMathieuM 3 ν z h) := by
  sorry

/-- **Asymptotic expansion of `M^{(4)}_ν`** for large `Re z` (DLMF 28.25.1, 28.25.5):
`M^{(4)}_ν(z, h) ~ e^{-i(2h cosh z - (ν/2+1/4)π)} (πh(cosh z+1))^{-1/2} ∑_m D^-_m (4ih(cosh
z+1))^{-m}`
as `Re z → +∞` with `-2π + δ ≤ ph h + Im z ≤ π - δ`. -/
@[dlmf 28.25.E1, dlmf 28.25.E5]
theorem modMathieuM_four_hasAsymptoticExpansion {ν h : ℂ} (hν : ModMathieuAdmissible ν h)
    (hh : h ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (modMathieuAsympFilter h (-2 * π + δ) (π - δ))
      (fun m z => modMathieuAsympPrefactor (-1) ν h z * (4 * I * h * (Complex.cosh z + 1))⁻¹ ^ m)
      (modMathieuAsympD (-1) (mathieuLambda ν (h ^ 2)) h) (fun z => modMathieuM 4 ν z h) := by
  sorry

/-! ### §28.26 Asymptotic approximations for large `q` -/

/-- **Goldstein's representation** (DLMF 28.26.1), `h ≠ 0`, `cosh z ≠ 0`:
`Mc^{(3)}_m(z, h) = e^{iφ} (πh cosh z)^{-1/2} (Fc_m(z, h) - i Gc_m(z, h))` (from the
definitions of `Fc_m`, `Gc_m` and 28.20.13). -/
@[dlmf 28.26.E1]
theorem radialMathieuMc_three_eq_goldstein (m : ℕ) {h : ℝ} (hh : h ≠ 0) {z : ℂ}
    (hz : Complex.cosh z ≠ 0) :
    radialMathieuMc 3 m z h = Complex.exp (I * goldsteinPhase m z h) /
      (π * h * Complex.cosh z) ^ (1 / 2 : ℂ) * (goldsteinFc m z h - I * goldsteinGc m z h) := by
  have hP : (π * (h : ℂ) * Complex.cosh z) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h' => hz (by
      have := h'.1
      simp only [mul_eq_zero, ofReal_eq_zero, Real.pi_ne_zero, hh, false_or] at this
      exact this)
  have hadm : ModMathieuAdmissible (m : ℂ) (h : ℂ) := Or.inr ⟨⟨m, by simp⟩, by
    rw [← ofReal_pow]; exact ofReal_im _⟩
  rw [radialMathieuMc, modMathieuM_three hadm (by exact_mod_cast hh)]
  simp only [goldsteinFc, goldsteinGc, radialMathieuMc]
  set φ := goldsteinPhase m z h
  have he : Complex.exp (I * φ) * (Complex.cos φ - I * Complex.sin φ) = 1 := by
    have hc : Complex.cos φ - I * Complex.sin φ = Complex.exp (-φ * I) := by
      rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]; ring
    rw [hc, ← Complex.exp_add]
    ring_nf
    simp
  rw [div_mul_eq_mul_div, eq_div_iff hP]
  linear_combination (-(modMathieuM 1 (m : ℂ) z h + I * modMathieuM 2 (m : ℂ) z h) *
    (π * (h : ℂ) * Complex.cosh z) ^ (1 / 2 : ℂ)) * he -
    (modMathieuM 2 (m : ℂ) z h * (π * (h : ℂ) * Complex.cosh z) ^ (1 / 2 : ℂ) *
      Complex.exp (I * φ) * Complex.sin φ) * I_sq

/-- **Goldstein's representation** (DLMF 28.26.2), `h ≠ 0`, `cosh z ≠ 0`:
`i Ms^{(3)}_{m+1}(z, h) = e^{iφ} (πh cosh z)^{-1/2} (Fs_m(z, h) - i Gs_m(z, h))`. -/
@[dlmf 28.26.E2]
theorem radialMathieuMs_three_eq_goldstein (m : ℕ) {h : ℝ} (hh : h ≠ 0) {z : ℂ}
    (hz : Complex.cosh z ≠ 0) :
    I * radialMathieuMs 3 (m + 1) z h = Complex.exp (I * goldsteinPhase m z h) /
      (π * h * Complex.cosh z) ^ (1 / 2 : ℂ) * (goldsteinFs m z h - I * goldsteinGs m z h) := by
  have hP : (π * (h : ℂ) * Complex.cosh z) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h' => hz (by
      have := h'.1
      simp only [mul_eq_zero, ofReal_eq_zero, Real.pi_ne_zero, hh, false_or] at this
      exact this)
  have hadm : ModMathieuAdmissible (-((m + 1 : ℕ) : ℂ)) (h : ℂ) :=
    Or.inr ⟨⟨-((m + 1 : ℕ) : ℤ), by push_cast; ring⟩, by rw [← ofReal_pow]; exact ofReal_im _⟩
  rw [radialMathieuMs, modMathieuM_three hadm (by exact_mod_cast hh)]
  simp only [goldsteinFs, goldsteinGs, radialMathieuMs]
  set φ := goldsteinPhase m z h
  set P := (π * (h : ℂ) * Complex.cosh z) ^ (1 / 2 : ℂ)
  have he : Complex.exp (I * φ) * (Complex.cos φ - I * Complex.sin φ) = 1 := by
    have hc : Complex.cos φ - I * Complex.sin φ = Complex.exp (-φ * I) := by
      rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]; ring
    rw [hc, ← Complex.exp_add]
    ring_nf
    simp
  set X1 := (-1 : ℂ) ^ (m + 1) * modMathieuM 1 (-((m + 1 : ℕ) : ℂ)) z h
  set X2 := (-1 : ℂ) ^ (m + 1) * modMathieuM 2 (-((m + 1 : ℕ) : ℂ)) z h
  rw [div_mul_eq_mul_div, eq_div_iff hP]
  linear_combination (-(I * X1 - X2) * P) * he +
    (modMathieuM 1 (-((m + 1 : ℕ) : ℂ)) z h * P * Complex.exp (I * φ) * Complex.sin φ *
      (-1) ^ m - modMathieuM 2 (-((m + 1 : ℕ) : ℂ)) z h * P * (-1) ^ m) * I_sq

/-- **Goldstein's expansion of `Fc_m`** (DLMF 28.26.4): as `h → +∞` with fixed `m` and fixed
`z`, `Re z > 0`, `Fc_m(z, h) = 1 + s/(8h cosh² z) + … + O(h⁻⁴)`, `s = 2m + 1`. Stated for
`|Im z| < π/2`, where the principal branches of `(πh cosh z)^{1/2}` and `arctan(sinh z)` are the
continuations from the real axis. -/
@[dlmf 28.26.E4]
theorem goldsteinFc_isBigO (m : ℕ) {z : ℂ} (hz : 0 < z.re) (hz' : |z.im| < π / 2) :
    (fun h : ℝ => goldsteinFc m z h - goldsteinFcApprox m z h) =O[atTop]
      (fun h : ℝ => h ^ (-4 : ℤ)) := by
  sorry

/-- **Goldstein's expansion of `Gc_m`** (DLMF 28.26.5), hypotheses as for 28.26.4:
`Gc_m(z, h) = (sinh z / cosh² z)((s²+3)/(2⁵h) + …) + O(h⁻⁴)`. -/
@[dlmf 28.26.E5]
theorem goldsteinGc_isBigO (m : ℕ) {z : ℂ} (hz : 0 < z.re) (hz' : |z.im| < π / 2) :
    (fun h : ℝ => goldsteinGc m z h - goldsteinGcApprox m z h) =O[atTop]
      (fun h : ℝ => h ^ (-4 : ℤ)) := by
  sorry

/-- **Goldstein's expansions of `Fs_m`, `Gs_m`** (DLMF §28.26(i): "also given by the
right-hand sides of 28.26.4 and 28.26.5"), hypotheses as for 28.26.4. -/
@[dlmf 28.26.i]
theorem goldsteinFs_Gs_isBigO (m : ℕ) {z : ℂ} (hz : 0 < z.re) (hz' : |z.im| < π / 2) :
    (fun h : ℝ => goldsteinFs m z h - goldsteinFcApprox m z h) =O[atTop]
        (fun h : ℝ => h ^ (-4 : ℤ)) ∧
      (fun h : ℝ => goldsteinGs m z h - goldsteinGcApprox m z h) =O[atTop]
        (fun h : ℝ => h ^ (-4 : ℤ)) := by
  sorry

end DLMF.Mathieu
