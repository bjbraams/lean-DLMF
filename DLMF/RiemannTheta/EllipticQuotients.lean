/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.RiemannTheta.Basic.Sections
public import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Tactic

/-!
# Elliptic functions from theta sections in genus one

The quotient of two theta sections of the same order is meromorphic and has all
periods `m + nτ`. When `Im τ > 0` these are two independent periods, giving the
classical construction of elliptic functions from theta functions. Assigned values
at denominator zeros use totalized division; meromorphy concerns the local germs.

References: Beals–Wong, *Explorations in Complex Functions*, §14.3;
Mumford, *Tata Lectures on Theta I*, Chapter I, §6.
-/

public noncomputable section

open Complex Matrix

namespace DLMF.RiemannTheta

/-- Equal-order theta quotients in genus one are meromorphic functions of one complex variable. -/
theorem meromorphic_thetaSectionSpace_quotient_fin_one {N : ℕ} {τ : ℂ}
    {f g : (Fin 1 → ℂ) → ℂ} (hf : f ∈ thetaSectionSpace N !![τ])
    (hg : g ∈ thetaSectionSpace N !![τ]) :
    Meromorphic (fun z : ℂ => f ![z] / g ![z]) := by
  have he : Differentiable ℂ (fun z : ℂ => (![z] : Fin 1 → ℂ)) := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i
    exact differentiable_id
  intro z
  exact ((hf.1.comp he).analyticAt z).meromorphicAt.div
    ((hg.1.comp he).analyticAt z).meromorphicAt

/-- All integer combinations of the two periods are periods of a genus-one theta quotient. -/
theorem periodic_thetaSectionSpace_quotient_fin_one {N : ℕ} {τ : ℂ}
    {f g : (Fin 1 → ℂ) → ℂ} (hf : f ∈ thetaSectionSpace N !![τ])
    (hg : g ∈ thetaSectionSpace N !![τ]) (m n : ℤ) :
    Function.Periodic (fun z : ℂ => f ![z] / g ![z]) ((m : ℂ) + n * τ) := by
  have hp := periodic_div_of_mem_thetaSectionSpace hf hg (fun _ => m) (fun _ => n)
  intro z
  dsimp only
  have he : (![z + ((m : ℂ) + n * τ)] : Fin 1 → ℂ) =
      ![z] + ((fun _ => (m : ℂ)) + !![τ] *ᵥ fun _ => (n : ℂ)) := by
    ext i
    fin_cases i
    simp only [Pi.add_apply, mulVec, dotProduct, Fin.sum_univ_one, of_apply, cons_val_fin_one]
    ring
  rw [he]
  exact hp ![z]

end DLMF.RiemannTheta
