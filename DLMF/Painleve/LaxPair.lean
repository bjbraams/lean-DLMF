/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic.Polynomial.Basic

/-!
# The compatible linear system for Painlevé II

The matrices are Beals–Wong (15.4.1)–(15.4.11), in exactly the book's
normalization. The curvature identity identifies the compatibility condition
with `PII(c)` and records the spectral reflection symmetry (15.4.12).
This proves the compatibility identities, not existence of a fundamental
matrix or the global isomonodromy and Stokes theorems.
-/

@[expose] public noncomputable section

open Matrix
open scoped Matrix.Norms.Elementwise

namespace DLMF.Painleve

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The diagonal matrix `J`, Beals–Wong (15.4.13). -/
def laxJ : Matrix (Fin 2) (Fin 2) 𝕜 := !![1, 0; 0, -1]

/-- The exchange matrix `J₂`, Beals–Wong (15.4.13). -/
def laxS : Matrix (Fin 2) (Fin 2) 𝕜 := !![0, 1; 1, 0]

/-- The skew exchange matrix `J₃`, Beals–Wong (15.4.13). -/
def laxK : Matrix (Fin 2) (Fin 2) 𝕜 := !![0, 1; -1, 0]

/-- The coefficient of `Ψ_x = B Ψ` in the Painlevé II linear system. -/
def laxB (u l : 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜 := !![l, u; u, -l]

/-- The polynomial coefficient of `λ Ψ_λ = A Ψ`, where `v` stands for `u'`. -/
def laxA (c x u v l : 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜 :=
  !![-4 * l ^ 3 + l * (x + 2 * u ^ 2), -4 * l ^ 2 * u - 2 * l * v + c;
     -4 * l ^ 2 * u + 2 * l * v + c, 4 * l ^ 3 - l * (x + 2 * u ^ 2)]

/-- The `x` derivative of `A`, where `u'=v` and `v'=w`. -/
def laxAx (u v w l : 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜 :=
  !![l * (1 + 4 * u * v), -4 * l ^ 2 * v - 2 * l * w;
     -4 * l ^ 2 * v + 2 * l * w, -l * (1 + 4 * u * v)]

/-- The curvature of the linear system is exactly the Painlevé II residual. -/
theorem lax_curvature (c x u v w l : 𝕜) :
    laxAx u v w l - (laxB u l * laxA c x u v l - laxA c x u v l * laxB u l) - l • laxJ =
      (2 * l * (2 * u ^ 3 + x * u - c - w)) • laxK := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [laxAx, laxB, laxA, laxJ, laxK] <;> ring

/-- At a nonzero spectral parameter, zero curvature is equivalent to the scalar PII equation. -/
theorem lax_compatibility_iff (c x u v w : 𝕜) {l : 𝕜} (hl : l ≠ 0) :
    laxAx u v w l = laxB u l * laxA c x u v l - laxA c x u v l * laxB u l + l • laxJ ↔
      w = 2 * u ^ 3 + x * u - c := by
  constructor
  · intro he
    have hr := lax_curvature c x u v w l
    have hr0 : (2 * l * (2 * u ^ 3 + x * u - c - w)) • (laxK : Matrix (Fin 2) (Fin 2) 𝕜) = 0 := by
      rw [← hr, he]
      abel
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) 𝕜 => M 0 1) hr0
    have hz : 2 * l * (2 * u ^ 3 + x * u - c - w) = 0 := by simpa [laxK] using hentry
    have h2 : (2 : 𝕜) ≠ 0 := by norm_num
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero h2 hl))).symm
  · intro he
    subst w
    have hr := lax_curvature c x u v (2 * u ^ 3 + x * u - c) l
    simp only [sub_self, mul_zero, zero_smul] at hr
    apply sub_eq_zero.mp
    calc
      _ = laxAx u v (2 * u ^ 3 + x * u - c) l -
          (laxB u l * laxA c x u v l - laxA c x u v l * laxB u l) - l • laxJ := by abel
      _ = 0 := hr

/-- Differentiation of the Lax polynomial along a twice differentiable scalar function. -/
theorem hasDerivAt_laxA {u v : 𝕜 → 𝕜} {x w : 𝕜}
    (hu : HasDerivAt u (v x) x) (hv : HasDerivAt v w x) (c l : 𝕜) :
    HasDerivAt (fun x => laxA c x (u x) (v x) l) (laxAx (u x) (v x) w l) x := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact ((hasDerivAt_const x (-4 * l ^ 3)).add
      (((hasDerivAt_id x).add ((hu.pow 2).const_mul 2)).const_mul l)).congr_deriv (by
        dsimp [laxAx]; ring)
  · exact (((hu.const_mul (-4 * l ^ 2)).sub (hv.const_mul (2 * l))).add_const c).congr_deriv (by
        rfl)
  · exact (((hu.const_mul (-4 * l ^ 2)).add (hv.const_mul (2 * l))).add_const c).congr_deriv (by
        rfl)
  · exact ((hasDerivAt_const x (4 * l ^ 3)).sub
      (((hasDerivAt_id x).add ((hu.pow 2).const_mul 2)).const_mul l)).congr_deriv (by
        dsimp [laxAx]; ring)

/-- Every Painlevé II solution gives a compatible Lax pair, Beals–Wong (15.4.3). -/
theorem IsPIIOn.hasDerivAt_laxA {c : 𝕜} {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (h : IsPIIOn c u s) {x : 𝕜} (hx : x ∈ s) (l : 𝕜) :
    HasDerivAt (fun x => laxA c x (u x) (deriv u x) l)
      (laxB (u x) l * laxA c x (u x) (deriv u x) l -
        laxA c x (u x) (deriv u x) l * laxB (u x) l + l • laxJ) x := by
  have hd := Painleve.hasDerivAt_laxA (h.hasDerivAt hx) (h.hasDerivAt_deriv x hx) c l
  have hr := lax_curvature c x (u x) (deriv u x) (2 * u x ^ 3 + x * u x - c) l
  simp only [sub_self, mul_zero, zero_smul] at hr
  exact hd.congr_deriv (by
    apply sub_eq_zero.mp
    calc
      _ = laxAx (u x) (deriv u x) (2 * u x ^ 3 + x * u x - c) l -
          (laxB (u x) l * laxA c x (u x) (deriv u x) l -
            laxA c x (u x) (deriv u x) l * laxB (u x) l) - l • laxJ := by abel
      _ = 0 := hr)

/-- Both Lax coefficients have trace zero. -/
theorem lax_trace_zero (c x u v l : 𝕜) :
    Matrix.trace (laxB u l) = 0 ∧ Matrix.trace (laxA c x u v l) = 0 := by
  simp [Matrix.trace, laxB, laxA, Fin.sum_univ_two]

/-- The exchange symmetry of the `x` coefficient, Beals–Wong (15.4.12). -/
theorem laxB_reflection (u l : 𝕜) : laxS * laxB u l * laxS = laxB u (-l) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [laxS, laxB, Matrix.mul_apply, Fin.sum_univ_two]

/-- The exchange symmetry of the spectral coefficient, Beals–Wong (15.4.12). -/
theorem laxA_reflection (c x u v l : 𝕜) : laxS * laxA c x u v l * laxS = laxA c x u v (-l) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [laxS, laxA, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end DLMF.Painleve
