/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.SpectralExistence
public import DLMFMathlib.Analysis.ODE.P2sSturmOsc

/-!
# Mathieu's equation as a separated Sturm–Liouville problem

For real `a`, `q` the basic solutions `w_I(x; a, q)`, `w_II(x; a, q)` restricted to `ℝ` are the
basic solutions `ODE.p2lY V false a`, `ODE.p2lY V true a` of `w'' = (V - a) w` with
`V(x) = 2q cos 2x`, and the spectra of Table 28.2.1 are the separated spectra
`ODE.p2lSpec V (π/2) odd0 oddK`. Sturm's oscillation theorem (`ODE.p2s_oscillation`) then
gives the zero counts of the eigenfunctions in `(0, π/2)` (DLMF §28.2(vi)) and the signs of the
basic solutions at `π/2` (used for 28.2.34–28.2.37).
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

/-- The Mathieu potential `x ↦ 2q cos 2x` is continuous. -/
theorem p2s_hV (q : ℝ) : Continuous fun x : ℝ => 2 * q * Real.cos (2 * x) := by fun_prop

/-- The Mathieu potential is bounded: `|2q cos 2x| ≤ 2|q|`. -/
theorem p2s_hB (q : ℝ) (x : ℝ) : |2 * q * Real.cos (2 * x)| ≤ 2 * |q| := by
  rw [abs_mul, abs_mul, abs_two]
  have := Real.abs_cos_le_one (2 * x)
  nlinarith [abs_nonneg q]

/-- Cast identity `((π/2 : ℝ) : ℂ) = π/2`. -/
theorem p2s_hpi : ((π / 2 : ℝ) : ℂ) = (π : ℂ) / 2 := by push_cast; ring

/-- The real part of `w_I(x; a, q)` (real `a, q`) is the Sturm–Liouville solution `p2lY`
with initial data `(1, 0)`. -/
lemma p2s_WI_re (a q : ℝ) : (fun x : ℝ => (mathieuWI a q x).re) =
    ODE.p2lY (fun x : ℝ => 2 * q * Real.cos (2 * x)) false a := by
  obtain ⟨-, hd, hd', -⟩ := p2s_family q (w := fun a => mathieuWI a q)
    (fun a => isMathieuSolution_mathieuWI a q) (α := 1) (β := 0)
    (fun a => by simp [(mathieuWI_spec a q).2.1]) (fun a => by simp [(mathieuWI_spec a q).2.2])
  have hdw : deriv (fun x : ℝ => (mathieuWI a q x).re) =
      fun x : ℝ => (deriv (mathieuWI a q) x).re := funext fun x => (hd a x).deriv
  have hsol : ODE.p2lIsSol (fun x : ℝ => 2 * q * Real.cos (2 * x)) a
      (fun x : ℝ => (mathieuWI a q x).re) :=
    ⟨fun x => (hd a x).differentiableAt, fun x => by rw [hdw]; exact hd' a x⟩
  obtain ⟨y0, y1, hy⟩ := ODE.p2lY_spec (p2s_hV q) false a
  refine ODE.p2l_sol_eq (p2s_hV q) hsol hy (x₀ := 0) ?_ ?_
  · rw [y0]; simp [(mathieuWI_spec a q).2.1, ODE.p2lD0]
  · rw [hdw, y1]; simp [(mathieuWI_spec a q).2.2, ODE.p2lD1]

/-- The real part of `w_II(x; a, q)` (real `a, q`) is the Sturm–Liouville solution `p2lY`
with initial data `(0, 1)`. -/
lemma p2s_WII_re (a q : ℝ) : (fun x : ℝ => (mathieuWII a q x).re) =
    ODE.p2lY (fun x : ℝ => 2 * q * Real.cos (2 * x)) true a := by
  obtain ⟨-, hd, hd', -⟩ := p2s_family q (w := fun a => mathieuWII a q)
    (fun a => isMathieuSolution_mathieuWII a q) (α := 0) (β := 1)
    (fun a => by simp [(mathieuWII_spec a q).2.1])
    (fun a => by simp [(mathieuWII_spec a q).2.2])
  have hdw : deriv (fun x : ℝ => (mathieuWII a q x).re) =
      fun x : ℝ => (deriv (mathieuWII a q) x).re := funext fun x => (hd a x).deriv
  have hsol : ODE.p2lIsSol (fun x : ℝ => 2 * q * Real.cos (2 * x)) a
      (fun x : ℝ => (mathieuWII a q x).re) :=
    ⟨fun x => (hd a x).differentiableAt, fun x => by rw [hdw]; exact hd' a x⟩
  obtain ⟨y0, y1, hy⟩ := ODE.p2lY_spec (p2s_hV q) true a
  refine ODE.p2l_sol_eq (p2s_hV q) hsol hy (x₀ := 0) ?_ ?_
  · rw [y0]; simp [(mathieuWII_spec a q).2.1, ODE.p2lD0]
  · rw [hdw, y1]; simp [(mathieuWII_spec a q).2.2, ODE.p2lD1]

/-- For real `a, q, x`, `w_I(x; a, q)` and its derivative are the real values of the
Sturm–Liouville solution `p2lY … false a` and its derivative. -/
theorem p2s_WI_eq (a q x : ℝ) : mathieuWI a q x =
    (ODE.p2lY (fun x : ℝ => 2 * q * Real.cos (2 * x)) false a x : ℂ) ∧
    deriv (mathieuWI a q) x =
      ((deriv (ODE.p2lY (fun x : ℝ => 2 * q * Real.cos (2 * x)) false a) x : ℝ) : ℂ) := by
  obtain ⟨hre, hd, -, -⟩ := p2s_family q (w := fun a => mathieuWI a q)
    (fun a => isMathieuSolution_mathieuWI a q) (α := 1) (β := 0)
    (fun a => by simp [(mathieuWI_spec a q).2.1]) (fun a => by simp [(mathieuWI_spec a q).2.2])
  rw [← p2s_WI_re, (hd a x).deriv]
  exact hre a x

/-- For real `a, q, x`, `w_II(x; a, q)` and its derivative are the real values of the
Sturm–Liouville solution `p2lY … true a` and its derivative. -/
theorem p2s_WII_eq (a q x : ℝ) : mathieuWII a q x =
    (ODE.p2lY (fun x : ℝ => 2 * q * Real.cos (2 * x)) true a x : ℂ) ∧
    deriv (mathieuWII a q) x =
      ((deriv (ODE.p2lY (fun x : ℝ => 2 * q * Real.cos (2 * x)) true a) x : ℝ) : ℂ) := by
  obtain ⟨hre, hd, -, -⟩ := p2s_family q (w := fun a => mathieuWII a q)
    (fun a => isMathieuSolution_mathieuWII a q) (α := 0) (β := 1)
    (fun a => by simp [(mathieuWII_spec a q).2.1])
    (fun a => by simp [(mathieuWII_spec a q).2.2])
  rw [← p2s_WII_re, (hd a x).deriv]
  exact hre a x

/-- The spectra of Table 28.2.1 as separated Sturm–Liouville spectra on `[0, π/2]`. -/
theorem p2s_specA (n : ℕ) (q : ℝ) : mathieuSpecA n q =
    ODE.p2lSpec (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) false
      (if Even n then false else true) := by
  unfold mathieuSpecA
  split_ifs
  · rw [ODE.p2s_spec_eq_neu (p2s_hV q)]
    ext a; simp only [mem_ofPred_eq]; rw [← p2s_hpi, (p2s_WI_eq a q _).2, ofReal_eq_zero]
  · rw [ODE.p2s_spec_eq_dir (p2s_hV q)]
    ext a; simp only [mem_ofPred_eq]; rw [← p2s_hpi, (p2s_WI_eq a q _).1, ofReal_eq_zero]

/-- The `b_n` spectra of Table 28.2.1 as separated Sturm–Liouville spectra on `[0, π/2]`. -/
theorem p2s_specB (n : ℕ) (q : ℝ) : mathieuSpecB n q =
    ODE.p2lSpec (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) true
      (if Even n then true else false) := by
  unfold mathieuSpecB
  split_ifs
  · rw [ODE.p2s_spec_eq_dir (p2s_hV q)]
    ext a; simp only [mem_ofPred_eq]; rw [← p2s_hpi, (p2s_WII_eq a q _).1, ofReal_eq_zero]
  · rw [ODE.p2s_spec_eq_neu (p2s_hV q)]
    ext a; simp only [mem_ofPred_eq]; rw [← p2s_hpi, (p2s_WII_eq a q _).2, ofReal_eq_zero]

/-- **Zeros of `w_I(x; a_n(q), q)`** in `(0, π/2)`: exactly `⌊n/2⌋` (Sturm oscillation). -/
theorem p2s_zeros_A (n : ℕ) (q : ℝ) :
    {x : ℝ | x ∈ Ioo 0 (π / 2) ∧ mathieuWI (mathieuA n q) q x = 0}.encard = (n / 2 : ℕ) := by
  have hh := (mathieuA_spec n q).1
  rw [p2s_specA] at hh
  have := ODE.p2s_oscillation_encard (p2s_hV q) (p2s_hB q) (by positivity) _ _ hh
  rw [← p2s_specA, (mathieuA_spec n q).2] at this
  rw [← this]
  congr 1; ext x
  simp only [mem_ofPred_eq]
  rw [(p2s_WI_eq _ q x).1, ofReal_eq_zero]

/-- **Zeros of `w_II(x; b_n(q), q)`** in `(0, π/2)`, `n ≥ 1`: exactly `⌊(n-1)/2⌋`. -/
theorem p2s_zeros_B {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    {x : ℝ | x ∈ Ioo 0 (π / 2) ∧ mathieuWII (mathieuB n q) q x = 0}.encard =
      ((n - 1) / 2 : ℕ) := by
  have hh := (mathieuB_spec hn q).1
  rw [p2s_specB] at hh
  have := ODE.p2s_oscillation_encard (p2s_hV q) (p2s_hB q) (by positivity) _ _ hh
  rw [← p2s_specB, (mathieuB_spec hn q).2] at this
  rw [← this]
  congr 1; ext x
  simp only [mem_ofPred_eq]
  rw [(p2s_WII_eq _ q x).1, ofReal_eq_zero]

/-- A set of extended cardinality `k` has `ncard` equal to `k`. -/
theorem p2s_ncard_of_encard {S : Set ℝ} {k : ℕ} (h : S.encard = k) : S.ncard = k := by
  rw [Set.ncard_def, h]; rfl

/-- Sign of `w_I(π/2; a_{2n}(q), q)`: `(-1)ⁿ`. -/
theorem p2s_sign_A_even (n : ℕ) (q : ℝ) : ∃ α : ℝ,
    mathieuWI (mathieuA (2 * n) q) q (π / 2) = α ∧ 0 < (-1) ^ n * α := by
  have he : Even (2 * n) := even_two_mul n
  have hh := (mathieuA_spec (2 * n) q).1
  have hk := p2s_ncard_of_encard (mathieuA_spec (2 * n) q).2
  rw [p2s_specA] at hh hk
  simp only [he, ↓reduceIte] at hh hk
  have := ODE.p2s_sign_neumann (p2s_hV q) (p2s_hB q) (by positivity) false hh
  rw [hk, show 2 * n / 2 = n by omega] at this
  exact ⟨_, by rw [← p2s_hpi]; exact (p2s_WI_eq _ q _).1, this⟩

/-- Sign of `w_II(π/2; b_{2n+1}(q), q)`: `(-1)ⁿ`. -/
theorem p2s_sign_B_odd (n : ℕ) (q : ℝ) : ∃ β : ℝ,
    mathieuWII (mathieuB (2 * n + 1) q) q (π / 2) = β ∧ 0 < (-1) ^ n * β := by
  have he : ¬Even (2 * n + 1) := Nat.not_even_bit1 n
  have hh := (mathieuB_spec (n := 2 * n + 1) (by omega) q).1
  have hk := p2s_ncard_of_encard (mathieuB_spec (n := 2 * n + 1) (by omega) q).2
  rw [p2s_specB] at hh hk
  simp only [he, ↓reduceIte] at hh hk
  have := ODE.p2s_sign_neumann (p2s_hV q) (p2s_hB q) (by positivity) true hh
  rw [hk, show (2 * n + 1 - 1) / 2 = n by omega] at this
  exact ⟨_, by rw [← p2s_hpi]; exact (p2s_WII_eq _ q _).1, this⟩

/-- Sign of `w_I'(π/2; a_{2n+1}(q), q)`: `(-1)ⁿ⁺¹`. -/
theorem p2s_sign_A_odd (n : ℕ) (q : ℝ) : ∃ α : ℝ,
    deriv (mathieuWI (mathieuA (2 * n + 1) q) q) (π / 2) = α ∧ 0 < (-1) ^ (n + 1) * α := by
  have he : ¬Even (2 * n + 1) := Nat.not_even_bit1 n
  have hh := (mathieuA_spec (2 * n + 1) q).1
  have hk := p2s_ncard_of_encard (mathieuA_spec (2 * n + 1) q).2
  rw [p2s_specA] at hh hk
  simp only [he, ↓reduceIte] at hh hk
  have := ODE.p2s_sign_dirichlet (p2s_hV q) (p2s_hB q) (by positivity) false hh
  rw [hk, show (2 * n + 1) / 2 = n by omega] at this
  exact ⟨_, by rw [← p2s_hpi]; exact (p2s_WI_eq _ q _).2, this⟩

/-- Sign of `w_II'(π/2; b_{2n+2}(q), q)`: `(-1)ⁿ⁺¹`. -/
theorem p2s_sign_B_even (n : ℕ) (q : ℝ) : ∃ β : ℝ,
    deriv (mathieuWII (mathieuB (2 * n + 2) q) q) (π / 2) = β ∧ 0 < (-1) ^ (n + 1) * β := by
  have he : Even (2 * n + 2) := ⟨n + 1, by ring⟩
  have hh := (mathieuB_spec (n := 2 * n + 2) (by omega) q).1
  have hk := p2s_ncard_of_encard (mathieuB_spec (n := 2 * n + 2) (by omega) q).2
  rw [p2s_specB] at hh hk
  simp only [he, ↓reduceIte] at hh hk
  have := ODE.p2s_sign_dirichlet (p2s_hV q) (p2s_hB q) (by positivity) true hh
  rw [hk, show (2 * n + 2 - 1) / 2 = n by omega] at this
  exact ⟨_, by rw [← p2s_hpi]; exact (p2s_WII_eq _ q _).2, this⟩

end DLMF.Mathieu
