/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Selberg.Applications
public import DLMF.OrthogonalPolynomials.Basic.Classical

/-!
# Maximum root discriminant with prescribed sum and product

Andrews, Askey and Roy, *Special Functions*, Lemma 8.6.3, pp. 420–422.
The discriminant is the product of squared root differences without any
leading-coefficient factor.
-/

@[expose] public section

open Polynomial Finset

namespace DLMF.Selberg

/-- The positive parameter determining a Laguerre extremum is unique.
Andrews–Askey–Roy, *Special Functions*, Lemma 8.6.3, pp. 420–422
(synopsis AAR-8.6.1–8.6.7). -/
theorem existsUnique_laguerre_discriminant_parameter {n : ℕ} (hn : 2 ≤ n)
    {s P : ℝ} (hs : 0 < s) (hP : 0 < P) (hPs : P < s ^ n) :
    ∃! t : ℝ, 0 < t ∧
      (ascPochhammer ℝ n).eval t / (((n : ℝ) + t - 1) / s) ^ n = P := by
  sorry

/-- Among positive configurations of prescribed sum and product, the largest root
 discriminant is attained exactly at the scaled Laguerre zero configurations.
Andrews–Askey–Roy, *Special Functions*, Lemma 8.6.3, pp. 420–422
(synopsis AAR-8.6.1–8.6.7). The exact maximum is retained, as are all permutations. -/
theorem siegelDiscriminant_le_laguerre_maximum {n : ℕ} (hn : 2 ≤ n)
    {s P t : ℝ} (hs : 0 < s) (hP : 0 < P) (hPs : P < s ^ n)
    (ht : 0 < t)
    (htP : (ascPochhammer ℝ n).eval t / (((n : ℝ) + t - 1) / s) ^ n = P)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hsum : ∑ i, x i = n * s) (hprod : ∏ i, x i = P) :
    let c := ((n : ℝ) + t - 1) / s
    let M := c ^ (-(n * (n - 1) : ℤ)) *
      ∏ j ∈ Icc 1 n, (j : ℝ) ^ j * (t + j - 1) ^ (j - 1)
    siegelDiscriminant x ≤ M ∧
      (siegelDiscriminant x = M ↔ Function.Injective x ∧
        ∀ i, DLMF.OrthogonalPolynomials.laguerrePolynomialL (t - 1 : ℂ) n
          (c * x i) = 0) := by
  sorry

end DLMF.Selberg
