/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Asymptotic expansions

Following Poincaré (and Temme, *Special Functions*, §2.2), a function `f` has the asymptotic
expansion `f ~ ∑ aₙ φₙ` along a filter `l` with respect to the scale functions `φₙ` if for
every `N` the remainder after `N` terms is `O(φ_N)`:

`f - ∑_{n<N} φₙ aₙ = O(φ_N)`.

The scale is *asymptotic* if `φₙ₊₁ = o(φₙ)`; then the remainder after `N` terms is also
`o(φ_{N-1})`, and the coefficients are unique as soon as each `φₙ` is frequently nonzero.
The expansion need not converge, and a function determines its expansion but not
conversely.

The scale functions are scalar-valued and the coefficients lie in a normed space, so that
real and complex expansions with vector coefficients are covered.

## Main definitions

* `Asymptotics.IsAsymptoticScale l φ`: `φ (n+1) =o[l] φ n` for all `n`.
* `Asymptotics.HasAsymptoticExpansion l φ a f`: `f ~ ∑ aₙ φₙ` along `l`.

## Main results

* `HasAsymptoticExpansion.add`, `.smul`, `.neg`, `.sub`: linearity.
* `HasAsymptoticExpansion.congr_scale`, `.smul_scale`, `.mul_left`, `.comp_tendsto`: changing,
  rescaling, multiplying and composing the scale.
* `HasAsymptoticExpansion.isLittleO`: the remainder after `N + 1` terms is `o(φ_N)`.
* `HasAsymptoticExpansion.unique`: uniqueness of the coefficients.
* `isAsymptoticScale_rpow_neg`: the scale `x ↦ x^{-(n+μ)}` at `+∞`.
-/

@[expose] public section

noncomputable section

open Filter Finset

open scoped Topology

namespace Asymptotics

variable {α 𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {l : Filter α} {φ : ℕ → α → 𝕜}

/-- An asymptotic scale: each scale function is negligible compared with the previous one. -/
def IsAsymptoticScale (l : Filter α) (φ : ℕ → α → 𝕜) : Prop :=
  ∀ n, φ (n + 1) =o[l] φ n

/-- The asymptotic expansion `f ~ ∑ aₙ φₙ` along `l`: for every `N`,
`f - ∑_{n<N} φₙ • aₙ = O(φ_N)`. -/
def HasAsymptoticExpansion (l : Filter α) (φ : ℕ → α → 𝕜) (a : ℕ → E) (f : α → E) : Prop :=
  ∀ N, (fun x => f x - ∑ n ∈ range N, φ n x • a n) =O[l] φ N

namespace HasAsymptoticExpansion

variable {a b : ℕ → E} {f g : α → E}

/-- Expansions transfer along eventually equal functions. -/
theorem congr' (hf : HasAsymptoticExpansion l φ a f) (hfg : f =ᶠ[l] g) :
    HasAsymptoticExpansion l φ a g := fun N =>
  (hf N).congr' (hfg.mono fun x hx => by simp only [hx]) EventuallyEq.rfl

/-- Expansions transfer along equal coefficient sequences. -/
theorem congr_coeff (hf : HasAsymptoticExpansion l φ a f) (hab : a = b) :
    HasAsymptoticExpansion l φ b f := hab ▸ hf

/-- Expansions transfer along scales that are eventually equal termwise. -/
theorem congr_scale {ψ : ℕ → α → 𝕜} (hf : HasAsymptoticExpansion l φ a f)
    (h : ∀ n, φ n =ᶠ[l] ψ n) : HasAsymptoticExpansion l ψ a f := fun N => by
  have hall : ∀ᶠ x in l, ∀ n ∈ range N, φ n x = ψ n x :=
    (eventually_all_finset (range N)).mpr fun n _ => h n
  refine (hf N).congr' (hall.mono fun x hx => ?_) (h N)
  simp only
  rw [sum_congr rfl fun n hn => by rw [hx n hn]]

/-- If each scale function is a constant multiple `κₙ ψₙ`, the expansion transfers to the scale
`ψ` with coefficients `κₙ aₙ`. -/
theorem smul_scale {ψ : ℕ → α → 𝕜} {κ : ℕ → 𝕜} (hf : HasAsymptoticExpansion l φ a f)
    (h : ∀ n, φ n =ᶠ[l] fun x => κ n * ψ n x) :
    HasAsymptoticExpansion l ψ (fun n => κ n • a n) f := fun N => by
  have hall : ∀ᶠ x in l, ∀ n ∈ range N, φ n x = κ n * ψ n x :=
    (eventually_all_finset (range N)).mpr fun n _ => h n
  refine ((hf N).trans ((isBigO_const_mul_self (κ N) (ψ N) l).congr' (h N).symm
    EventuallyEq.rfl)).congr' (hall.mono fun x hx => ?_) EventuallyEq.rfl
  simp only
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [hx n hn, smul_smul, mul_comm]

/-- Multiplying a function by `g` multiplies the scale by `g`. -/
theorem mul_left (hf : HasAsymptoticExpansion l φ a f) (g : α → 𝕜) :
    HasAsymptoticExpansion l (fun n x => g x * φ n x) a (fun x => g x • f x) := fun N =>
  ((isBigO_refl g l).smul (hf N)).congr_left fun x => by
    simp only [smul_sub, smul_sum, smul_smul]

/-- Expansions compose with a function tending to the base filter. -/
theorem comp_tendsto {β : Type*} {l' : Filter β} {g : β → α} (hf : HasAsymptoticExpansion l φ a f)
    (hg : Tendsto g l' l) : HasAsymptoticExpansion l' (fun n x => φ n (g x)) a (f ∘ g) :=
  fun N => (hf N).comp_tendsto hg

theorem add (hf : HasAsymptoticExpansion l φ a f) (hg : HasAsymptoticExpansion l φ b g) :
    HasAsymptoticExpansion l φ (a + b) (f + g) := fun N =>
  ((hf N).add (hg N)).congr_left fun x => by
    simp only [Pi.add_apply, smul_add, sum_add_distrib]; abel

theorem const_smul (hf : HasAsymptoticExpansion l φ a f) (c : 𝕜) :
    HasAsymptoticExpansion l φ (c • a) (c • f) := fun N =>
  ((hf N).const_smul_left c).congr_left fun x => by
    simp only [Pi.smul_apply, smul_sub, smul_sum, smul_comm c (φ _ x)]

theorem neg (hf : HasAsymptoticExpansion l φ a f) :
    HasAsymptoticExpansion l φ (-a) (-f) := by
  simpa using hf.const_smul (-1 : 𝕜)

theorem sub (hf : HasAsymptoticExpansion l φ a f) (hg : HasAsymptoticExpansion l φ b g) :
    HasAsymptoticExpansion l φ (a - b) (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- The remainder after `N + 1` terms is `o(φ_N)`. -/
theorem isLittleO (hφ : IsAsymptoticScale l φ) (hf : HasAsymptoticExpansion l φ a f) (N : ℕ) :
    (fun x => f x - ∑ n ∈ range (N + 1), φ n x • a n) =o[l] φ N :=
  (hf (N + 1)).trans_isLittleO (hφ N)

/-- The remainder after `N` terms is `φ_N • a_N + o(φ_N)`. -/
theorem sub_smul_isLittleO (hφ : IsAsymptoticScale l φ) (hf : HasAsymptoticExpansion l φ a f)
    (N : ℕ) : (fun x => f x - ∑ n ∈ range N, φ n x • a n - φ N x • a N) =o[l] φ N :=
  (hf.isLittleO hφ N).congr_left fun x => by rw [sum_range_succ]; abel

/-- If `φ` is frequently nonzero, a vector `c` with `φ • c = o(φ)` vanishes. -/
theorem eq_zero_of_smul_isLittleO {ψ : α → 𝕜} {c : E} (hψ : ∃ᶠ x in l, ψ x ≠ 0)
    (h : (fun x => ψ x • c) =o[l] ψ) : c = 0 := by
  by_contra hc
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hev := h.def (half_pos hcpos)
  obtain ⟨x, hx, hψx⟩ := (hψ.and_eventually hev).exists
  rw [norm_smul] at hψx
  have hψpos : 0 < ‖ψ x‖ := norm_pos_iff.mpr hx
  nlinarith

/-- Uniqueness of the coefficients of an asymptotic expansion. -/
theorem unique (hφ : IsAsymptoticScale l φ) (hne : ∀ n, ∃ᶠ x in l, φ n x ≠ 0)
    (ha : HasAsymptoticExpansion l φ a f) (hb : HasAsymptoticExpansion l φ b f) : a = b := by
  funext N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  have hsum : ∀ x, ∑ n ∈ range N, φ n x • a n = ∑ n ∈ range N, φ n x • b n := fun x =>
    sum_congr rfl fun n hn => by rw [ih n (mem_range.mp hn)]
  have h := (ha.sub_smul_isLittleO hφ N).sub (hb.sub_smul_isLittleO hφ N)
  have h' : (fun x => φ N x • (b N - a N)) =o[l] φ N := h.congr_left fun x => by
    simp only [hsum, smul_sub]; abel
  exact (sub_eq_zero.mp (eq_zero_of_smul_isLittleO (hne N) h')).symm

end HasAsymptoticExpansion

/-- The scale `x ↦ x^{-(n+μ)}` is an asymptotic scale at `+∞`. -/
theorem isAsymptoticScale_rpow_neg (μ : ℝ) :
    IsAsymptoticScale atTop (fun (n : ℕ) (x : ℝ) => x ^ (-((n : ℝ) + μ))) := by
  intro n
  have h0 : (fun x : ℝ => x⁻¹) =o[atTop] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr tendsto_inv_atTop_zero
  have h := h0.mul_isBigO (isBigO_refl (fun x : ℝ => x ^ (-((n : ℝ) + μ))) atTop)
  refine (h.congr' ?_ (Eventually.of_forall fun x => one_mul _)).congr_left fun x => rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  push_cast
  rw [show -((n : ℝ) + 1 + μ) = -1 + -((n : ℝ) + μ) by ring, Real.rpow_add hx,
    Real.rpow_neg_one]

end Asymptotics
