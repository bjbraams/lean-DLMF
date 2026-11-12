/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LiouvilleGreenComparison

/-!
# Uniqueness of a normalized recessive solution

For solutions of `y'' = q y` on a real half-line, decay of both solutions and their first
derivatives forces the constant Wronskian to vanish. A nonvanishing solution then has
constant quotient with every other decaying solution. A quotient tending to one identifies
the solutions, over any real or complex scalar field.
-/

open Set Filter
open scoped Topology
@[expose] public section

namespace LiouvilleGreen
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Two solutions of the same second-order equation on `(a,∞)` coincide if both solutions
and their derivatives tend to zero, the first solution is nonvanishing, and the quotient
of the second by the first tends to one. -/
theorem eqOn_of_tendsto_zero_of_tendsto_div_one {a : ℝ} {q f f' g g' : ℝ → 𝕜}
    (hf : ∀ x, a < x → HasDerivAt f (f' x) x)
    (hf' : ∀ x, a < x → HasDerivAt f' (q x * f x) x)
    (hg : ∀ x, a < x → HasDerivAt g (g' x) x)
    (hg' : ∀ x, a < x → HasDerivAt g' (q x * g x) x)
    (hf0 : Tendsto f atTop (𝓝 0)) (hf'0 : Tendsto f' atTop (𝓝 0))
    (hg0 : Tendsto g atTop (𝓝 0)) (hg'0 : Tendsto g' atTop (𝓝 0))
    (hne : ∀ x, a < x → f x ≠ 0)
    (hratio : Tendsto (fun x => g x / f x) atTop (𝓝 1)) :
    EqOn g f (Ioi a) := by
  have hW0 : Tendsto (fun x => f x * g' x - f' x * g x) atTop (𝓝 0) := by
    simpa only [mul_zero, sub_self] using (hf0.mul hg'0).sub (hf'0.mul hg0)
  have hW (x : ℝ) (hx : a < x) : f x * g' x - f' x * g x = 0 := by
    have hconst : (fun y => f y * g' y - f' y * g y) =ᶠ[atTop]
        fun _ => f x * g' x - f' x * g x := by
      filter_upwards [eventually_gt_atTop a] with y hy
      exact wronskian_eq hf hf' hg hg' hy hx
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' hconst.symm) hW0
  have hD (x : ℝ) (hx : a < x) : HasDerivAt (fun y => g y / f y) 0 x := by
    have hd := (hg x hx).div (hf x hx) (hne x hx)
    have hn : g' x * f x - g x * f' x = 0 := by linear_combination hW x hx
    simpa only [hn, zero_div] using! hd
  intro x hx
  have hconst : (fun y => g y / f y) =ᶠ[atTop] fun _ => g x / f x := by
    filter_upwards [eventually_gt_atTop a] with y hy
    exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hD z hz).deriv) hy hx
  have hratio_one : g x / f x = 1 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hconst.symm) hratio
  exact (div_eq_one_iff_eq (hne x hx)).mp hratio_one

end LiouvilleGreen
