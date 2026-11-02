/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.SpectralExistence
public import DLMFMathlib.Analysis.ODE.SturmOscillation

/-!
# Mathieu's equation as a separated Sturm–Liouville problem

For real `a`, `q` the basic solutions `w_I(x; a, q)`, `w_II(x; a, q)` restricted to `ℝ` are the
basic solutions `ODE.basicSolution V false a`, `ODE.basicSolution V true a` of `w'' = (V - a) w`
with `V(x) = 2q cos 2x`, and the spectra of Table 28.2.1 are the separated spectra
`ODE.separatedSpectrum V (π/2) odd0 oddK`. Sturm's oscillation theorem
(`ODE.ncard_basicSolution_zeros_eq_ncard_separatedSpectrum_inter_Iio`) then gives the zero
counts of the eigenfunctions in `(0, π/2)` (DLMF §28.2(vi)) and the signs of the basic solutions
at `π/2` (used for 28.2.34–28.2.37).

## Main results

* `mathieuWI_ofReal_eq_sturmSolution`, `mathieuWII_ofReal_eq_sturmSolution`: `w_I`, `w_II` and
  their derivatives on the real axis are the Sturm–Liouville basic solutions.
* `mathieuSpecA_eq_sturmSpectrum`, `mathieuSpecB_eq_sturmSpectrum`: the spectra of
  Table 28.2.1 as separated Sturm–Liouville spectra on `[0, π/2]`.
* `encard_zeros_mathieuWI_mathieuA`, `encard_zeros_mathieuWII_mathieuB`: `w_I(·; a_n(q), q)`
  has exactly `⌊n/2⌋` zeros in `(0, π/2)`, and `w_II(·; b_n(q), q)` exactly `⌊(n-1)/2⌋`.
* `mathieuWI_half_pi_mathieuA_even_sign`, `mathieuWII_half_pi_mathieuB_odd_sign`,
  `deriv_mathieuWI_half_pi_mathieuA_odd_sign`, `deriv_mathieuWII_half_pi_mathieuB_even_sign`:
  the signs of the basic solutions and their derivatives at `π/2`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

/-- The Mathieu potential `x ↦ 2q cos 2x` is continuous. -/
theorem continuous_two_mul_cos_two_mul (q : ℝ) : Continuous fun x : ℝ => 2 * q *
    Real.cos (2 * x) := by fun_prop

/-- The Mathieu potential is bounded: `|2q cos 2x| ≤ 2|q|`. -/
theorem abs_two_mul_cos_two_mul_le (q : ℝ) (x : ℝ) : |2 * q * Real.cos (2 * x)| ≤ 2 * |q| := by
  rw [abs_mul, abs_mul, abs_two]
  have := Real.abs_cos_le_one (2 * x)
  nlinarith [abs_nonneg q]

/-- Cast identity `((π/2 : ℝ) : ℂ) = π/2`. -/
theorem ofReal_pi_div_two : ((π / 2 : ℝ) : ℂ) = (π : ℂ) / 2 := by push_cast; ring

/-- The real part of `w_I(x; a, q)` (real `a, q`) is the Sturm–Liouville solution `basicSolution`
with initial data `(1, 0)`. -/
private lemma re_mathieuWI_eq_sturmSolution (a q : ℝ) : (fun x : ℝ => (mathieuWI a q x).re) =
    ODE.basicSolution (fun x : ℝ => 2 * q * Real.cos (2 * x)) false a := by
  obtain ⟨-, hd, hd', -⟩ := real_family_of_isMathieuSolution q (w := fun a => mathieuWI a q)
    (fun a => isMathieuSolution_mathieuWI a q) (α := 1) (β := 0)
    (fun a => by simp [(mathieuWI_spec a q).2.1]) (fun a => by simp [(mathieuWI_spec a q).2.2])
  have hdw : deriv (fun x : ℝ => (mathieuWI a q x).re) =
      fun x : ℝ => (deriv (mathieuWI a q) x).re := funext fun x => (hd a x).deriv
  have hsol : ODE.IsSturmLiouvilleSolution (fun x : ℝ => 2 * q * Real.cos (2 * x)) a
      (fun x : ℝ => (mathieuWI a q x).re) :=
    ⟨fun x => (hd a x).differentiableAt, fun x => by rw [hdw]; exact hd' a x⟩
  obtain ⟨y0, y1, hy⟩ :=
      ODE.basicSolution_initial_and_isSol (continuous_two_mul_cos_two_mul q) false a
  refine ODE.isSturmLiouvilleSolution_eq_of_eq_of_deriv_eq (continuous_two_mul_cos_two_mul q) hsol
      hy (x₀ := 0) ?_ ?_
  · rw [y0]; simp [(mathieuWI_spec a q).2.1, ODE.basicInitValue]
  · rw [hdw, y1]; simp [(mathieuWI_spec a q).2.2, ODE.basicInitSlope]

/-- The real part of `w_II(x; a, q)` (real `a, q`) is the Sturm–Liouville solution `basicSolution`
with initial data `(0, 1)`. -/
private lemma re_mathieuWII_eq_sturmSolution (a q : ℝ) : (fun x : ℝ => (mathieuWII a q x).re) =
    ODE.basicSolution (fun x : ℝ => 2 * q * Real.cos (2 * x)) true a := by
  obtain ⟨-, hd, hd', -⟩ := real_family_of_isMathieuSolution q (w := fun a => mathieuWII a q)
    (fun a => isMathieuSolution_mathieuWII a q) (α := 0) (β := 1)
    (fun a => by simp [(mathieuWII_spec a q).2.1])
    (fun a => by simp [(mathieuWII_spec a q).2.2])
  have hdw : deriv (fun x : ℝ => (mathieuWII a q x).re) =
      fun x : ℝ => (deriv (mathieuWII a q) x).re := funext fun x => (hd a x).deriv
  have hsol : ODE.IsSturmLiouvilleSolution (fun x : ℝ => 2 * q * Real.cos (2 * x)) a
      (fun x : ℝ => (mathieuWII a q x).re) :=
    ⟨fun x => (hd a x).differentiableAt, fun x => by rw [hdw]; exact hd' a x⟩
  obtain ⟨y0, y1, hy⟩ :=
      ODE.basicSolution_initial_and_isSol (continuous_two_mul_cos_two_mul q) true a
  refine ODE.isSturmLiouvilleSolution_eq_of_eq_of_deriv_eq (continuous_two_mul_cos_two_mul q) hsol
      hy (x₀ := 0) ?_ ?_
  · rw [y0]; simp [(mathieuWII_spec a q).2.1, ODE.basicInitValue]
  · rw [hdw, y1]; simp [(mathieuWII_spec a q).2.2, ODE.basicInitSlope]

/-- For real `a, q, x`, `w_I(x; a, q)` and its derivative are the real values of the
Sturm–Liouville solution `basicSolution … false a` and its derivative. -/
theorem mathieuWI_ofReal_eq_sturmSolution (a q x : ℝ) : mathieuWI a q x =
    (ODE.basicSolution (fun x : ℝ => 2 * q * Real.cos (2 * x)) false a x : ℂ) ∧
    deriv (mathieuWI a q) x =
      ((deriv (ODE.basicSolution (fun x : ℝ => 2 * q * Real.cos (2 * x)) false a) x : ℝ) : ℂ) := by
  obtain ⟨hre, hd, -, -⟩ := real_family_of_isMathieuSolution q (w := fun a => mathieuWI a q)
    (fun a => isMathieuSolution_mathieuWI a q) (α := 1) (β := 0)
    (fun a => by simp [(mathieuWI_spec a q).2.1]) (fun a => by simp [(mathieuWI_spec a q).2.2])
  rw [← re_mathieuWI_eq_sturmSolution, (hd a x).deriv]
  exact hre a x

/-- For real `a, q, x`, `w_II(x; a, q)` and its derivative are the real values of the
Sturm–Liouville solution `basicSolution … true a` and its derivative. -/
theorem mathieuWII_ofReal_eq_sturmSolution (a q x : ℝ) : mathieuWII a q x =
    (ODE.basicSolution (fun x : ℝ => 2 * q * Real.cos (2 * x)) true a x : ℂ) ∧
    deriv (mathieuWII a q) x =
      ((deriv (ODE.basicSolution (fun x : ℝ => 2 * q * Real.cos (2 * x)) true a) x : ℝ) : ℂ) := by
  obtain ⟨hre, hd, -, -⟩ := real_family_of_isMathieuSolution q (w := fun a => mathieuWII a q)
    (fun a => isMathieuSolution_mathieuWII a q) (α := 0) (β := 1)
    (fun a => by simp [(mathieuWII_spec a q).2.1])
    (fun a => by simp [(mathieuWII_spec a q).2.2])
  rw [← re_mathieuWII_eq_sturmSolution, (hd a x).deriv]
  exact hre a x

/-- The spectra of Table 28.2.1 as separated Sturm–Liouville spectra on `[0, π/2]`. -/
theorem mathieuSpecA_eq_sturmSpectrum (n : ℕ) (q : ℝ) : mathieuSpecA n q =
    ODE.separatedSpectrum (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) false
      (if Even n then false else true) := by
  unfold mathieuSpecA
  split_ifs
  · rw [ODE.separatedSpectrum_false_eq (continuous_two_mul_cos_two_mul q)]
    ext a; simp only [mem_ofPred_eq];
        rw [← ofReal_pi_div_two, (mathieuWI_ofReal_eq_sturmSolution a q _).2, ofReal_eq_zero]
  · rw [ODE.separatedSpectrum_true_eq (continuous_two_mul_cos_two_mul q)]
    ext a; simp only [mem_ofPred_eq];
        rw [← ofReal_pi_div_two, (mathieuWI_ofReal_eq_sturmSolution a q _).1, ofReal_eq_zero]

/-- The `b_n` spectra of Table 28.2.1 as separated Sturm–Liouville spectra on `[0, π/2]`. -/
theorem mathieuSpecB_eq_sturmSpectrum (n : ℕ) (q : ℝ) : mathieuSpecB n q =
    ODE.separatedSpectrum (fun x : ℝ => 2 * q * Real.cos (2 * x)) (π / 2) true
      (if Even n then true else false) := by
  unfold mathieuSpecB
  split_ifs
  · rw [ODE.separatedSpectrum_true_eq (continuous_two_mul_cos_two_mul q)]
    ext a; simp only [mem_ofPred_eq];
        rw [← ofReal_pi_div_two, (mathieuWII_ofReal_eq_sturmSolution a q _).1, ofReal_eq_zero]
  · rw [ODE.separatedSpectrum_false_eq (continuous_two_mul_cos_two_mul q)]
    ext a; simp only [mem_ofPred_eq];
        rw [← ofReal_pi_div_two, (mathieuWII_ofReal_eq_sturmSolution a q _).2, ofReal_eq_zero]

/-- **Zeros of `w_I(x; a_n(q), q)`** in `(0, π/2)`: exactly `⌊n/2⌋` (Sturm oscillation). -/
theorem encard_zeros_mathieuWI_mathieuA (n : ℕ) (q : ℝ) :
    {x : ℝ | x ∈ Ioo 0 (π / 2) ∧ mathieuWI (mathieuA n q) q x = 0}.encard = (n / 2 : ℕ) := by
  have hh := (mathieuA_spec n q).1
  rw [mathieuSpecA_eq_sturmSpectrum] at hh
  have := ODE.encard_basicSolution_zeros_eq_encard_separatedSpectrum_inter_Iio
      (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) _ _ hh
  rw [← mathieuSpecA_eq_sturmSpectrum, (mathieuA_spec n q).2] at this
  rw [← this]
  congr 1; ext x
  simp only [mem_ofPred_eq]
  rw [(mathieuWI_ofReal_eq_sturmSolution _ q x).1, ofReal_eq_zero]

/-- **Zeros of `w_II(x; b_n(q), q)`** in `(0, π/2)`, `n ≥ 1`: exactly `⌊(n-1)/2⌋`. -/
theorem encard_zeros_mathieuWII_mathieuB {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    {x : ℝ | x ∈ Ioo 0 (π / 2) ∧ mathieuWII (mathieuB n q) q x = 0}.encard =
      ((n - 1) / 2 : ℕ) := by
  have hh := (mathieuB_spec hn q).1
  rw [mathieuSpecB_eq_sturmSpectrum] at hh
  have := ODE.encard_basicSolution_zeros_eq_encard_separatedSpectrum_inter_Iio
      (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) _ _ hh
  rw [← mathieuSpecB_eq_sturmSpectrum, (mathieuB_spec hn q).2] at this
  rw [← this]
  congr 1; ext x
  simp only [mem_ofPred_eq]
  rw [(mathieuWII_ofReal_eq_sturmSolution _ q x).1, ofReal_eq_zero]

/-- A set of extended cardinality `k` has `ncard` equal to `k`. -/
theorem ncard_eq_of_encard_eq_natCast {S : Set ℝ} {k : ℕ} (h : S.encard = k) : S.ncard = k := by
  rw [Set.ncard_def, h]; rfl

/-- Sign of `w_I(π/2; a_{2n}(q), q)`: `(-1)ⁿ`. -/
theorem mathieuWI_half_pi_mathieuA_even_sign (n : ℕ) (q : ℝ) : ∃ α : ℝ,
    mathieuWI (mathieuA (2 * n) q) q (π / 2) = α ∧ 0 < (-1) ^ n * α := by
  have he : Even (2 * n) := even_two_mul n
  have hh := (mathieuA_spec (2 * n) q).1
  have hk := ncard_eq_of_encard_eq_natCast (mathieuA_spec (2 * n) q).2
  rw [mathieuSpecA_eq_sturmSpectrum] at hh hk
  simp only [he, ↓reduceIte] at hh hk
  have := ODE.neg_one_pow_mul_basicSolution_pos_of_mem_separatedSpectrum_false
      (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) false hh
  rw [hk, show 2 * n / 2 = n by omega] at this
  exact ⟨_, by rw [← ofReal_pi_div_two]; exact (mathieuWI_ofReal_eq_sturmSolution _ q _).1, this⟩

/-- Sign of `w_II(π/2; b_{2n+1}(q), q)`: `(-1)ⁿ`. -/
theorem mathieuWII_half_pi_mathieuB_odd_sign (n : ℕ) (q : ℝ) : ∃ β : ℝ,
    mathieuWII (mathieuB (2 * n + 1) q) q (π / 2) = β ∧ 0 < (-1) ^ n * β := by
  have he : ¬Even (2 * n + 1) := Nat.not_even_bit1 n
  have hh := (mathieuB_spec (n := 2 * n + 1) (by omega) q).1
  have hk := ncard_eq_of_encard_eq_natCast (mathieuB_spec (n := 2 * n + 1) (by omega) q).2
  rw [mathieuSpecB_eq_sturmSpectrum] at hh hk
  simp only [he, ↓reduceIte] at hh hk
  have := ODE.neg_one_pow_mul_basicSolution_pos_of_mem_separatedSpectrum_false
      (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) true hh
  rw [hk, show (2 * n + 1 - 1) / 2 = n by omega] at this
  exact ⟨_, by rw [← ofReal_pi_div_two]; exact (mathieuWII_ofReal_eq_sturmSolution _ q _).1, this⟩

/-- Sign of `w_I'(π/2; a_{2n+1}(q), q)`: `(-1)ⁿ⁺¹`. -/
theorem deriv_mathieuWI_half_pi_mathieuA_odd_sign (n : ℕ) (q : ℝ) : ∃ α : ℝ,
    deriv (mathieuWI (mathieuA (2 * n + 1) q) q) (π / 2) = α ∧ 0 < (-1) ^ (n + 1) * α := by
  have he : ¬Even (2 * n + 1) := Nat.not_even_bit1 n
  have hh := (mathieuA_spec (2 * n + 1) q).1
  have hk := ncard_eq_of_encard_eq_natCast (mathieuA_spec (2 * n + 1) q).2
  rw [mathieuSpecA_eq_sturmSpectrum] at hh hk
  simp only [he, ↓reduceIte] at hh hk
  have := ODE.neg_one_pow_mul_deriv_basicSolution_pos_of_mem_separatedSpectrum_true
      (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) false hh
  rw [hk, show (2 * n + 1) / 2 = n by omega] at this
  exact ⟨_, by rw [← ofReal_pi_div_two]; exact (mathieuWI_ofReal_eq_sturmSolution _ q _).2, this⟩

/-- Sign of `w_II'(π/2; b_{2n+2}(q), q)`: `(-1)ⁿ⁺¹`. -/
theorem deriv_mathieuWII_half_pi_mathieuB_even_sign (n : ℕ) (q : ℝ) : ∃ β : ℝ,
    deriv (mathieuWII (mathieuB (2 * n + 2) q) q) (π / 2) = β ∧ 0 < (-1) ^ (n + 1) * β := by
  have he : Even (2 * n + 2) := ⟨n + 1, by ring⟩
  have hh := (mathieuB_spec (n := 2 * n + 2) (by omega) q).1
  have hk := ncard_eq_of_encard_eq_natCast (mathieuB_spec (n := 2 * n + 2) (by omega) q).2
  rw [mathieuSpecB_eq_sturmSpectrum] at hh hk
  simp only [he, ↓reduceIte] at hh hk
  have := ODE.neg_one_pow_mul_deriv_basicSolution_pos_of_mem_separatedSpectrum_true
      (continuous_two_mul_cos_two_mul q) (abs_two_mul_cos_two_mul_le q) (by positivity) true hh
  rw [hk, show (2 * n + 2 - 1) / 2 = n by omega] at this
  exact ⟨_, by rw [← ofReal_pi_div_two]; exact (mathieuWII_ofReal_eq_sturmSolution _ q _).2, this⟩

end DLMF.Mathieu
