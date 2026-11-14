/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Basic.AlternatingHurwitz
public import DLMF.Zeta.Lerch
public import DLMF.Gamma.Polygamma
public import DLMF.Constants.Dirichlet
public import DLMF.Constants.Catalan

/-!
# Alternating Hurwitz zeta and Dirichlet beta

The real alternating series and their Mellin integrals supplement the complex Lerch
transcendent. The source is Duverney, *An Introduction to Hypergeometric Functions*,
Chapter 2, equations (2.80)–(2.90), and Appendix A.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Finset
open scoped Topology Real

namespace DLMF.Zeta.Real

/-- Absolute convergence above order one. Duverney (2.81), DU-2.20. -/
theorem hasSum_alternatingHurwitzZeta {s a : ℝ} (hs : 1 < s) (ha : 0 < a) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + a) ^ s)
      (alternatingHurwitzZeta s a) := by
  sorry

/-- Dirichlet beta converges absolutely above order one. Duverney (2.86), DU-2.21. -/
theorem hasSum_dirichletBeta {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ s)
      (dirichletBeta s) := by
  sorry

/-- Ordered convergence for every positive alternating Hurwitz order.
Duverney (2.81), synopsis DU-2.20. -/
theorem tendsto_sum_alternatingHurwitzZeta {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℝ) ^ n / ((n : ℝ) + a) ^ s)
      atTop (𝓝 (alternatingHurwitzZeta s a)) := by
  sorry

/-- Ordered convergence of Dirichlet beta for all positive orders.
Duverney (2.86), synopsis DU-2.21. -/
theorem tendsto_sum_dirichletBeta {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ s)
      atTop (𝓝 (dirichletBeta s)) := by
  sorry

/-- The real eta function agrees with the existing complex eta series.
Duverney (2.69), DU-2.18 and DU-2.20. -/
theorem alternatingHurwitzZeta_one {s : ℝ} (hs : 1 < s) :
    (alternatingHurwitzZeta s 1 : ℂ) = DLMF.Constants.dirichletEta s := by
  sorry

/-- Alternating Hurwitz zeta is a boundary Lerch value.
Duverney Appendix A, (A.1)–(A.2), synopsis DU-A.01. -/
theorem alternatingHurwitzZeta_eq_lerchPhi {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    (alternatingHurwitzZeta s a : ℂ) = lerchPhi (-1) s a := by
  sorry

/-- The Mellin integral of alternating Hurwitz zeta is absolutely convergent.
Duverney (2.90), synopsis DU-2.22. -/
theorem integrableOn_alternatingHurwitzZeta_kernel {s a : ℝ}
    (hs : 0 < s) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-a * t) /
      (1 + Real.exp (-t))) (Ioi 0) := by
  sorry

/-- Mellin representation for alternating Hurwitz zeta.
Duverney (2.90), synopsis DU-2.22. -/
theorem alternatingHurwitzZeta_eq_integral {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    alternatingHurwitzZeta s a = (Real.Gamma s)⁻¹ *
      ∫ t in Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-a * t) / (1 + Real.exp (-t)) := by
  sorry

/-- The strict alternating-series bounds for eta. Duverney (2.72), DU-2.18. -/
theorem alternatingHurwitzZeta_one_bounds {s : ℝ} (hs : 0 < s) :
    1 - (2 : ℝ) ^ (-s) < alternatingHurwitzZeta s 1 ∧
      alternatingHurwitzZeta s 1 < 1 := by
  sorry

/-- The eta value at one. Duverney (2.73), synopsis DU-2.18. -/
theorem alternatingHurwitzZeta_one_one : alternatingHurwitzZeta 1 1 = Real.log 2 := by
  sorry

/-- The eta function tends to one at positive infinity. Duverney (2.75), DU-2.18. -/
theorem tendsto_alternatingHurwitzZeta_one :
    Tendsto (fun s : ℝ => alternatingHurwitzZeta s 1) atTop (𝓝 1) := by
  sorry

/-- Catalan's constant is Dirichlet beta at two. Duverney (2.88), DU-2.21. -/
theorem dirichletBeta_two : dirichletBeta 2 = DLMF.Constants.catalanConstant := by
  rw [← (hasSum_dirichletBeta (s := 2) (by norm_num)).tsum_eq]
  simp only [DLMF.Constants.catalanConstant, Real.rpow_two]

end DLMF.Zeta.Real
