/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Derivatives of the reciprocal Gamma function

`1/Γ` is entire, while the digamma function `ψ = Γ'/Γ` has poles at `0, -1, -2, …`. Mathlib's
`Complex.digamma` takes the value `0` at those poles, so a product such as
`ψ(x) · (1/Γ(x))` evaluates to `0` there although its continuous extension is
`(-1)^{n+1} n!` at `x = -n`. Statements in which digamma occurs only through such products
are therefore best written with the entire functions `recipGammaDeriv n = (1/Γ)^{(n)}`:

* `(1/Γ)' = -ψ/Γ` (`recipGammaDeriv_one_eq`), with `(1/Γ)'(-n) = (-1)^n n!`;
* `(1/Γ)'' = (ψ² - ψ')/Γ` (`recipGammaDeriv_two_eq`), so that the entire function
  `((1/Γ)')² - (1/Γ)(1/Γ)''` extends `ψ'/Γ²` (`deriv_digamma_mul_recip_Gamma_sq`);
* `ψ(x+n)/Γ(x) = -(x)_n (1/Γ)'(x+n)` (`recip_Gamma_mul_digamma_add_nat`).

Results stated with `recipGammaDeriv` hold for all parameters; the digamma forms follow on the
complement of the poles.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Nat Topology

namespace DLMF.Gamma

open DLMF.Hypergeometric

/-- `1/Γ` is entire (Mathlib's `differentiable_one_div_Gamma`, in the `⁻¹` form). -/
theorem differentiable_recip_Gamma : Differentiable ℂ fun z : ℂ => (Gamma z)⁻¹ := by
  simpa [one_div] using differentiable_one_div_Gamma

/-- The `n`-th derivative of the reciprocal Gamma function, an entire function. -/
def recipGammaDeriv (n : ℕ) (z : ℂ) : ℂ :=
  iteratedDeriv n (fun w : ℂ => (Gamma w)⁻¹) z

@[simp]
theorem recipGammaDeriv_zero (z : ℂ) : recipGammaDeriv 0 z = (Gamma z)⁻¹ := by
  simp [recipGammaDeriv]

theorem recipGammaDeriv_succ (n : ℕ) : recipGammaDeriv (n + 1) = deriv (recipGammaDeriv n) := by
  funext z
  simp only [recipGammaDeriv, iteratedDeriv_succ]
  rfl

theorem recipGammaDeriv_one_eq_deriv (z : ℂ) :
    recipGammaDeriv 1 z = deriv (fun w : ℂ => (Gamma w)⁻¹) z := by
  simp [recipGammaDeriv]

/-- Each `recipGammaDeriv n` is entire. -/
theorem differentiable_recipGammaDeriv (n : ℕ) : Differentiable ℂ (recipGammaDeriv n) := by
  have h := (differentiable_recip_Gamma.contDiff (n := ⊤)).differentiable_iteratedDeriv n
    (by exact_mod_cast WithTop.coe_lt_top _)
  exact h

theorem hasDerivAt_recipGammaDeriv (n : ℕ) (z : ℂ) :
    HasDerivAt (recipGammaDeriv n) (recipGammaDeriv (n + 1) z) z := by
  rw [recipGammaDeriv_succ]
  exact (differentiable_recipGammaDeriv n z).hasDerivAt

theorem continuous_recipGammaDeriv (n : ℕ) : Continuous (recipGammaDeriv n) :=
  (differentiable_recipGammaDeriv n).continuous

theorem hasDerivAt_recip_Gamma' (z : ℂ) :
    HasDerivAt (fun w : ℂ => (Gamma w)⁻¹) (recipGammaDeriv 1 z) z := by
  have h := hasDerivAt_recipGammaDeriv 0 z
  have e : recipGammaDeriv 0 = fun w : ℂ => (Gamma w)⁻¹ := funext recipGammaDeriv_zero
  rwa [e] at h

/-- `(x)_n / Γ(x+n) = 1/Γ(x)` for every `x`, including the poles of `Γ`. -/
theorem poch_mul_recip_Gamma_add_nat (x : ℂ) (r : ℕ) :
    poch x r * (Gamma (x + r))⁻¹ = (Gamma x)⁻¹ := by
  induction r with
  | zero => simp [poch_zero]
  | succ r ih =>
    have h := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (x + r)
    rw [poch_succ, Nat.cast_succ, ← add_assoc, mul_assoc, ← h, ih]

/-- The non-poles of `Γ` form an open set. -/
theorem isOpen_setOf_Gamma_ne_zero : IsOpen {z : ℂ | Gamma z ≠ 0} := by
  have : {z : ℂ | Gamma z ≠ 0} = (fun z : ℂ => (Gamma z)⁻¹) ⁻¹' {0}ᶜ := by
    ext z; simp
  rw [this]
  exact isOpen_compl_singleton.preimage differentiable_recip_Gamma.continuous

theorem Gamma_ne_zero_iff {z : ℂ} : Gamma z ≠ 0 ↔ ∀ m : ℕ, z ≠ -(m : ℂ) := by
  rw [Ne, Gamma_eq_zero_iff]
  push Not
  rfl

/-- `ψ` is differentiable away from the poles. -/
theorem differentiableAt_digamma {x : ℂ} (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    DifferentiableAt ℂ digamma x := by
  have hU : {z : ℂ | Gamma z ≠ 0} ∈ 𝓝 x :=
    isOpen_setOf_Gamma_ne_zero.mem_nhds (Gamma_ne_zero_iff.mpr hx)
  have hdiff : DifferentiableOn ℂ Gamma {z : ℂ | Gamma z ≠ 0} := fun z hz =>
    (differentiableAt_Gamma z (Gamma_ne_zero_iff.mp hz)).differentiableWithinAt
  have han : AnalyticAt ℂ Gamma x :=
    hdiff.analyticAt hU
  have hd : DifferentiableAt ℂ (deriv Gamma) x := han.deriv.differentiableAt
  have : digamma = fun z => deriv Gamma z / Gamma z := by
    funext z; rw [digamma_def, logDeriv_apply]
  rw [this]
  exact hd.div (differentiableAt_Gamma x hx) (Gamma_ne_zero hx)

/-- `(1/Γ)' = -ψ/Γ` away from the poles. -/
theorem recipGammaDeriv_one_eq {x : ℂ} (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    recipGammaDeriv 1 x = -(digamma x) * (Gamma x)⁻¹ := by
  have hG := (differentiableAt_Gamma x hx).hasDerivAt
  have h0 := Gamma_ne_zero hx
  refine (hasDerivAt_recip_Gamma' x).unique ((hG.inv h0).congr_deriv ?_)
  rw [digamma_def, logDeriv_apply]
  field_simp

/-- `(1/Γ)'(-p) = (-1)^p p!`: the continuous extension of `-ψ/Γ` at its removable points. -/
theorem recipGammaDeriv_one_neg_nat (p : ℕ) :
    recipGammaDeriv 1 (-(p : ℂ)) = (-1 : ℂ) ^ p * (p ! : ℂ) := by
  have heq : (fun y : ℂ => (Gamma y)⁻¹) =
      fun y => poch y p * (y + p) * (Gamma (y + (p + 1 : ℕ)))⁻¹ := by
    funext y
    rw [← poch_mul_recip_Gamma_add_nat y (p + 1), poch_succ]
  have hp := Polynomial.hasDerivAt (ascPochhammer ℂ p) (-(p : ℂ))
  have h1 : HasDerivAt (fun y : ℂ => y + p) 1 (-(p : ℂ)) := (hasDerivAt_id _).add_const _
  have hpole : ∀ m : ℕ, -(p : ℂ) + ((p + 1 : ℕ) : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have := congrArg re hm
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h2 := (hasDerivAt_recip_Gamma' (-(p : ℂ) + ((p + 1 : ℕ) : ℂ))).comp (-(p : ℂ))
    ((hasDerivAt_id (-(p : ℂ))).add_const ((p + 1 : ℕ) : ℂ))
  have h := (hp.mul h1).mul h2
  rw [recipGammaDeriv_one_eq_deriv, heq]
  refine HasDerivAt.deriv (h.congr_deriv ?_)
  have e1 : -(p : ℂ) + ((p + 1 : ℕ) : ℂ) = 1 := by push_cast; ring
  simp only [_root_.id, Function.comp_apply, Pi.mul_apply, e1, Gamma_one, inv_one, mul_one,
    neg_add_cancel, mul_zero, zero_add]
  rw [show (Polynomial.eval (-(p : ℂ)) (ascPochhammer ℂ p)) = poch (-(p : ℂ)) p from rfl,
    poch_neg_coe_nat, Nat.descFactorial_self]
  ring

/-- `(1/Γ)'' = (ψ² - ψ')/Γ` away from the poles. -/
theorem recipGammaDeriv_two_eq {x : ℂ} (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    recipGammaDeriv 2 x = (digamma x ^ 2 - deriv digamma x) * (Gamma x)⁻¹ := by
  have hU : {z : ℂ | Gamma z ≠ 0} ∈ 𝓝 x :=
    isOpen_setOf_Gamma_ne_zero.mem_nhds (Gamma_ne_zero_iff.mpr hx)
  have hev : (fun y => -(digamma y) * (Gamma y)⁻¹) =ᶠ[𝓝 x] recipGammaDeriv 1 := by
    filter_upwards [hU] with y hy
    exact (recipGammaDeriv_one_eq (Gamma_ne_zero_iff.mp hy)).symm
  have hψ := (differentiableAt_digamma hx).hasDerivAt
  have hd := (hψ.neg.mul (hasDerivAt_recip_Gamma' x)).congr_of_eventuallyEq hev.symm
  rw [show (2 : ℕ) = 1 + 1 from rfl, recipGammaDeriv_succ]
  rw [hd.deriv, recipGammaDeriv_one_eq hx, Pi.neg_apply]
  ring

/-- The entire function `((1/Γ)')² - (1/Γ)(1/Γ)''` extends `ψ'/Γ²`. -/
theorem deriv_digamma_mul_recip_Gamma_sq {x : ℂ} (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    deriv digamma x * ((Gamma x)⁻¹) ^ 2 =
      recipGammaDeriv 1 x ^ 2 - (Gamma x)⁻¹ * recipGammaDeriv 2 x := by
  rw [recipGammaDeriv_one_eq hx, recipGammaDeriv_two_eq hx]
  ring

/-- `ψ(x+n)/Γ(x) = -(x)_n (1/Γ)'(x+n)` whenever `x + n` is not a pole. -/
theorem recip_Gamma_mul_digamma_add_nat {x : ℂ} (n : ℕ) (hx : ∀ m : ℕ, x + n ≠ -(m : ℂ)) :
    (Gamma x)⁻¹ * digamma (x + n) = -(poch x n * recipGammaDeriv 1 (x + n)) := by
  rw [← poch_mul_recip_Gamma_add_nat x n, recipGammaDeriv_one_eq hx]
  ring

end DLMF.Gamma
