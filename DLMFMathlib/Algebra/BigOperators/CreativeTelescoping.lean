/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-!
# Creative telescoping for finite and infinite supports

Andrews, Askey and Roy, *Special Functions*, §3.11, pp. 166–172.
The finite theorem uses finite support. The infinite theorem states ordered
convergence and the two boundary limits separately, without replacing a
conditionally convergent sum by an unconditional sum.
-/

@[expose] public section

open Finset Filter

namespace Finset

/-- A finitely supported telescoping certificate gives a recurrence of the definite sums.
Andrews–Askey–Roy, *Special Functions*, §3.11, pp. 166–172
(synopsis AAR-3.10–3.12). Order one with coefficients `(-1,1)` is the WZ
constant-sum theorem. -/
theorem sum_finsum_eq_zero_of_telescoping_certificate
    {K E : Type*} [CommRing K] [AddCommGroup E] [Module K E]
    (r : ℕ) (P : ℕ → Fin (r + 1) → K) (F G : ℕ → ℤ → E)
    (hF : ∀ n, (Function.support (F n)).Finite)
    (hG : ∀ n, (Function.support (G n)).Finite)
    (hcert : ∀ (n : ℕ) (k : ℤ),
      ∑ j : Fin (r + 1), P n j • F (n + j.val) k = G n (k + 1) - G n k) (n : ℕ) :
    ∑ j : Fin (r + 1), P n j • (∑ᶠ k : ℤ, F (n + j.val) k) = 0 := by
  sorry

/-- An infinite telescoping certificate gives the sum recurrence when each ordered
symmetric partial sum converges and the total boundary difference tends to zero.
Andrews–Askey–Roy, *Special Functions*, §3.11, pp. 166–172
(synopsis AAR-3.10–3.12). -/
theorem sum_eq_zero_of_tendsto_telescoping_certificate
    {K E : Type*} [NormedField K] [NormedAddCommGroup E] [NormedSpace K E]
    (r : ℕ) (P : ℕ → Fin (r + 1) → K) (F G : ℕ → ℤ → E) (S : ℕ → E)
    (hcert : ∀ (n : ℕ) (k : ℤ),
      ∑ j : Fin (r + 1), P n j • F (n + j.val) k = G n (k + 1) - G n k)
    (hF : ∀ n, Tendsto
      (fun N : ℕ => ∑ k ∈ Icc (-(N : ℤ)) N, F n k) atTop (nhds (S n)))
    (hboundary : ∀ n, Tendsto
      (fun N : ℕ => G n ((N : ℤ) + 1) - G n (-(N : ℤ))) atTop (nhds 0)) (n : ℕ) :
    ∑ j : Fin (r + 1), P n j • S (n + j.val) = 0 := by
  sorry

end Finset
