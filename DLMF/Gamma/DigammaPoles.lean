/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Meromorphic.Complex
public import DLMF.Gamma.Inequalities
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Simple poles of the digamma function

Olver, *Asymptotics and Special Functions*, Chapter 2, §2, pp. 39–40,
synopsis O-2.06. The punctured limit records the residue despite totalization at the pole.
-/

@[expose] public section

open Filter Complex Set
open scoped Topology

namespace DLMF.Gamma

/-- The digamma function is meromorphic at every complex point.
Olver, Chapter 2, §2, synopsis O-2.06. -/
theorem meromorphicAt_digamma (z : ℂ) : MeromorphicAt Complex.digamma z :=
  (Meromorphic.Gamma z).logDeriv

/-- Every nonpositive integer is a simple digamma pole of residue `-1`.
Olver, Chapter 2, §2, synopsis O-2.06. -/
theorem tendsto_mul_digamma_neg_nat (n : ℕ) :
    Tendsto (fun z : ℂ => (z + n) * Complex.digamma z) (𝓝[≠] (-(n : ℂ))) (𝓝 (-1)) := by
  sorry

/-- The positive real Gamma function has a unique global minimizer, lying strictly between
one and two. Olver, Chapter 2, §2, synopsis O-2.06. The proof combines the Mathlib minimum
with the proved strict convexity of its logarithm. -/
theorem Real.existsUnique_isMinOn_Gamma_Ioi :
    ∃! x : ℝ, x ∈ Ioo 1 2 ∧ IsMinOn _root_.Real.Gamma (Ioi 0) x := by
  obtain ⟨x, hx, hmin⟩ := _root_.Real.exists_isMinOn_Gamma_Ioi
  refine ⟨x, ⟨hx, hmin⟩, ?_⟩
  intro y hy
  have hxpos : 0 < x := zero_lt_one.trans hx.1
  have hypos : 0 < y := zero_lt_one.trans hy.1.1
  have hlogx : IsMinOn (fun u : ℝ => _root_.Real.log (_root_.Real.Gamma u)) (Ioi 0) x := by
    intro t ht
    exact _root_.Real.log_le_log (_root_.Real.Gamma_pos_of_pos hxpos) (hmin ht)
  have hlogy : IsMinOn (fun u : ℝ => _root_.Real.log (_root_.Real.Gamma u)) (Ioi 0) y := by
    intro t ht
    exact _root_.Real.log_le_log (_root_.Real.Gamma_pos_of_pos hypos) (hy.2 ht)
  exact DLMF.Gamma.strictConvexOn_log_Gamma.eq_of_isMinOn hlogy hlogx hypos hxpos

end DLMF.Gamma
