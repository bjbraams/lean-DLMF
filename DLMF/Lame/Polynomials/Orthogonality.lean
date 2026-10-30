/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Polynomials.Basic
public import DLMF.Lame.Polynomials.P2pODE

/-!
# Lamé polynomials: orthogonality and completeness (DLMF §29.14)

Besides the orthogonality 29.3.19 of the Lamé functions on `(0, K)` (which applies to the
Lamé polynomials by 29.12.1–29.12.8, see `DLMF.Lame.Eigenvalues`), the products
`E(s, k²) E(K + it, k²)` (`lameProduct`, 29.14.1, 29.14.4–29.14.10) of each of the eight types
form an orthogonal and complete system on `[0, K] × [0, K']` for the inner product 29.14.2 with
weight `w(s, t) = sn²(K + it, k) - sn²(s, k)` (29.14.3); together the eight systems are
orthogonal and complete on `[0, 4K] × [0, 2K']` (29.14.11). The inner product has no complex
conjugation (as in DLMF; the Lamé polynomials are real on both segments).

Completeness is stated as: a continuous function `g` on the closed rectangle orthogonal to
every member of the system vanishes on the rectangle.

The orthogonality 29.14.1–29.14.10 for a single type is proved: the Lamé polynomials solve
Lamé's equation (`DLMF.Lame.p2p_lamePolyEk_isLameSolution`), Green's identity on the segments
`[0, K]` and `K + i[0, K']` (the boundary Wronskians vanish by the parities of Table 29.12.1)
gives two linear relations between the one-dimensional integrals, and the eigenvalue pairs
`(h, ν(ν+1))` of distinct members differ (29.15.3). The orthogonality 29.14.11 of all eight
systems on `[0, 4K] × [0, 2K']` is proved in the same way, with a symmetry argument for products
of different parity. The completeness statements are admitted.
-/

@[expose] public section

open Complex DLMF.Elliptic DLMF.JacobiElliptic Set
open scoped Real

noncomputable section

namespace DLMF.Lame

variable {k : ℝ}

/-- 29.14.1–29.14.10, orthogonality: for each type `t`, the products `lameProduct t n m` and
`lameProduct t n' m'` (`m ≤ n`, `m' ≤ n'`, `(n, m) ≠ (n', m')`) are orthogonal for the inner
product 29.14.2 on `[0, K] × [0, K']`. Proved by Green's identity on the two segments. -/
@[dlmf 29.14.E1, dlmf 29.14.E2, dlmf 29.14.E3, dlmf 29.14.E4, dlmf 29.14.E5, dlmf 29.14.E6,
  dlmf 29.14.E7, dlmf 29.14.E8, dlmf 29.14.E9, dlmf 29.14.E10]
theorem lameProduct_orthogonal (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m n' m' : ℕ} (hm : m ≤ n) (hm' : m' ≤ n') (hne : (n, m) ≠ (n', m')) :
    lameInner k (Real.compEllIntKm (k ^ 2)) (Real.compEllIntKm (1 - k ^ 2))
      (lameProduct t n m k) (lameProduct t n' m' k) = 0 := by
  obtain ⟨s1, s2, s3, -, -, -⟩ := p2p_lamePolyEk_sym hk0 hk1 t n m
  obtain ⟨s1', s2', s3', -, -, -⟩ := p2p_lamePolyEk_sym hk0 hk1 t n' m'
  obtain ⟨cs, cc, cd⟩ := p2p_sgn_cases t
  refine p2p_inner_zero_green hk0 hk1 hm hm' _ _ (fun z hz => ?_)
    (p2p_eigen_ne hk0 hk1 hm hm' (by simpa using hne) rfl rfl)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact p2p_W_zero hk0 hk1 hm hm' (by simpa using p2p_regular_real hk0 hk1 0) cs s1 s1'
  · exact p2p_W_zero hk0 hk1 hm hm' (by simpa using p2p_regular_vert hk0 hk1 0) cc s2 s2'
  · exact p2p_W_zero hk0 hk1 hm hm' (by simpa using p2p_regular_vert hk0 hk1 0) cc s2 s2'
  · exact p2p_W_zero hk0 hk1 hm hm' (p2p_regular_vert hk0 hk1 _) cd s3 s3'

/-- 29.14.1–29.14.10, completeness: for each type `t`, a function `g` continuous on
`[0, K] × [0, K']` that is orthogonal (29.14.2) to every `lameProduct t n m`, `m ≤ n`,
vanishes on that rectangle. Admitted. -/
@[dlmf 29.14.E1, dlmf 29.14.E2, dlmf 29.14.E4, dlmf 29.14.E5, dlmf 29.14.E6, dlmf 29.14.E7,
  dlmf 29.14.E8, dlmf 29.14.E9, dlmf 29.14.E10]
theorem lameProduct_complete (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) {g : ℝ → ℝ → ℂ}
    (hg : ContinuousOn (Function.uncurry g)
      (Icc 0 (Real.compEllIntKm (k ^ 2)) ×ˢ Icc 0 (Real.compEllIntKm (1 - k ^ 2))))
    (horth : ∀ n m : ℕ, m ≤ n →
      lameInner k (Real.compEllIntKm (k ^ 2)) (Real.compEllIntKm (1 - k ^ 2)) g
        (lameProduct t n m k) = 0) :
    ∀ s ∈ Icc 0 (Real.compEllIntKm (k ^ 2)), ∀ τ ∈ Icc 0 (Real.compEllIntKm (1 - k ^ 2)),
      g s τ = 0 := by
  sorry

/-- 29.14.11, orthogonality: the eight systems together are orthogonal for the inner product
on `[0, 4K] × [0, 2K']`. Proved: if the two products have different parities about `0` or
about `K` the real integrals vanish by symmetry; otherwise Green's identity applies as for a
single type (the boundary Wronskians at `0, 4K` and `K, K + 2iK'` vanish by the parities and
periods of Table 29.12.1), and distinct members have distinct pairs `(h, ν(ν+1))`, since equal
orders and parities force equal types. -/
@[dlmf 29.14.E11]
theorem lameProduct_orthogonal_all (hk0 : 0 < k) (hk1 : k < 1) {t t' : LamePolyType}
    {n m n' m' : ℕ} (hm : m ≤ n) (hm' : m' ≤ n') (hne : (t, n, m) ≠ (t', n', m')) :
    lameInner k (4 * Real.compEllIntKm (k ^ 2)) (2 * Real.compEllIntKm (1 - k ^ 2))
      (lameProduct t n m k) (lameProduct t' n' m' k) = 0 := by
  obtain ⟨s1, s2, -, -, s5, s6⟩ := p2p_lamePolyEk_sym hk0 hk1 t n m
  obtain ⟨s1', s2', -, -, s5', s6'⟩ := p2p_lamePolyEk_sym hk0 hk1 t' n' m'
  obtain ⟨cs, cc, -⟩ := p2p_sgn_cases t
  obtain ⟨cs', cc', -⟩ := p2p_sgn_cases t'
  by_cases hs : p2p_sgnS t = p2p_sgnS t'
  · by_cases hc : p2p_sgnC t = p2p_sgnC t'
    · rw [← hs] at s1' s5'
      rw [← hc] at s2' s6'
      refine p2p_inner_zero_green hk0 hk1 hm hm' _ _ (fun z hz => ?_)
        (p2p_eigen_ne hk0 hk1 hm hm' hne hs hc)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact p2p_W_zero hk0 hk1 hm hm' (by simpa using p2p_regular_real hk0 hk1 0) cs s1 s1'
      · have hr := p2p_regular_real hk0 hk1 (4 * Real.compEllIntKm (k ^ 2))
        push_cast at hr ⊢
        exact p2p_W_zero hk0 hk1 hm hm' hr cs s5 s5'
      · exact p2p_W_zero hk0 hk1 hm hm' (by simpa using p2p_regular_vert hk0 hk1 0) cc s2 s2'
      · have hr := p2p_regular_vert hk0 hk1 (2 * Real.compEllIntKm (1 - k ^ 2))
        push_cast at hr ⊢
        exact p2p_W_zero hk0 hk1 hm hm' hr cc s6 s6'
    · have hmul := p2p_sgn_mul cc cc' hc
      obtain ⟨h0, h1⟩ := p2p_real_integrals_zero hk0 hk1 (t := t) (t' := t') (n := n) (m := m)
        (n' := n') (m' := m') _ (Or.inr rfl) fun z => by
          have a := s2 z
          have b := s2' z
          simp only at a b
          rw [a, b]; linear_combination (lamePolyEk t n m (_ + z) k *
            lamePolyEk t' n' m' (_ + z) k) * hmul
      rw [p2p_inner_split hk0 hk1 hm hm', h0, h1]; ring
  · have hmul := p2p_sgn_mul cs cs' hs
    obtain ⟨h0, h1⟩ := p2p_real_integrals_zero hk0 hk1 (t := t) (t' := t') (n := n) (m := m)
      (n' := n') (m' := m') 0 (Or.inl rfl) fun z => by
        have a := s1 z
        have b := s1' z
        simp only [Complex.ofReal_zero] at a b ⊢
        rw [a, b]; linear_combination (lamePolyEk t n m (0 + z) k *
          lamePolyEk t' n' m' (0 + z) k) * hmul
    rw [p2p_inner_split hk0 hk1 hm hm', h0, h1]; ring

/-- 29.14.11, completeness: a function continuous on `[0, 4K] × [0, 2K']` orthogonal to all
products of all eight types vanishes there. Admitted. -/
@[dlmf 29.14.E11]
theorem lameProduct_complete_all (hk0 : 0 < k) (hk1 : k < 1) {g : ℝ → ℝ → ℂ}
    (hg : ContinuousOn (Function.uncurry g)
      (Icc 0 (4 * Real.compEllIntKm (k ^ 2)) ×ˢ Icc 0 (2 * Real.compEllIntKm (1 - k ^ 2))))
    (horth : ∀ (t : LamePolyType) (n m : ℕ), m ≤ n →
      lameInner k (4 * Real.compEllIntKm (k ^ 2)) (2 * Real.compEllIntKm (1 - k ^ 2)) g
        (lameProduct t n m k) = 0) :
    ∀ s ∈ Icc 0 (4 * Real.compEllIntKm (k ^ 2)),
      ∀ τ ∈ Icc 0 (2 * Real.compEllIntKm (1 - k ^ 2)), g s τ = 0 := by
  sorry

end DLMF.Lame
