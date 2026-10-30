/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.ParameterAndSeriesProperties
public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Derivatives and contiguous functions: DLMF §16.3

The existing local first derivative theorem is reused; the statements below acquire
all orders and global principal continuation. Every displayed lower parameter is
subject to the chapter's exclusion of nonpositive integers. Weighted powers use
the principal slit plane. Contiguous linear dependence is over rational functions,
expressed after clearing denominators as polynomial coefficients.
The general raising-operator identity uses Mathlib's `iteratedDeriv_fun_mul` and
analytic germ congruence; it has no dependence on hypergeometric continuation.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

/-- The analytic domain of a principal value, enlarged to the whole plane for a polynomial. -/
def genAnalyticDomain (a b : Multiset ℂ) : Set ℂ :=
  by classical exact if a.card ≤ b.card ∨ genTerminates a then univ else cutPlane

/-- The raising differential operator `z D z`. -/
def genRaiseOp (f : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv (fun z => z * f z) z

/-- Generalized contiguity means integer shifts of corresponding vector parameters. -/
def genContiguous {p q : ℕ} (a a' : Fin p → ℂ) (b b' : Fin q → ℂ) : Prop :=
  (∀ j, ∃ k : ℤ, a' j - a j = k) ∧ (∀ j, ∃ k : ℤ, b' j - b j = k)

/-- All derivatives of the ordinary principal function, including every terminating p,q. -/
@[dlmf 16.3.E1]
theorem genHG_iteratedDeriv {a b : Multiset ℂ} (hb : genDenRegular b)
    (h : a.card ≤ b.card + 1 ∨ genTerminates a) (n : ℕ)
    {z : ℂ} (hz : z ∈ genAnalyticDomain a b) :
    iteratedDeriv n (genHG a b) z = genPoch a n / genPoch b n *
      genHG (genShift a n) (genShift b n) z := by
  sorry

/-- All weighted power derivatives with every displayed lower parameter regular. -/
@[dlmf 16.3.E2]
theorem genHG_weighted_iteratedDeriv (a b : Multiset ℂ) (hb : genDenRegular b) (γ : ℂ) (n : ℕ)
    (hγ : genDenRegular {(γ + 1 - n)})
    (h : a.card ≤ b.card + 1 ∨ genTerminates a)
    {z : ℂ} (hz : z ∈ Complex.slitPlane ∩ genAnalyticDomain a b) :
    iteratedDeriv n (fun z => z ^ γ * genHG a b z) z =
      poch (γ - n + 1) n * z ^ (γ - n) *
        genHG ((γ + 1) ::ₘ a) ((γ + 1 - n) ::ₘ b) z := by
  sorry

/-- The iterated zDz identity, with all complex parameters and integer orders. -/
@[dlmf 16.3.E3]
theorem genHG_raising_iterate (a b : Multiset ℂ) (hb : genDenRegular b) (γ : ℂ) (n : ℕ)
    (h : a.card + 1 ≤ b.card + 1 ∨ genTerminates (γ ::ₘ a))
    {z : ℂ} (hz : z ∈ Complex.slitPlane ∩ genAnalyticDomain (γ ::ₘ a) b) :
    (genRaiseOp^[n]) (fun z => z ^ (γ - 1) * genHG (γ ::ₘ a) b z) z =
      poch γ n * z ^ (γ + n - 1) * genHG ((γ + n) ::ₘ a) b z := by
  sorry

/-- Weighted derivatives lowering one lower parameter by every natural order. -/
@[dlmf 16.3.E4]
theorem genHG_lower_weighted_iteratedDeriv (a b : Multiset ℂ) (hb : genDenRegular b) (γ : ℂ) (n : ℕ)
    (hγ : genDenRegular {γ, γ - n})
    (h : a.card ≤ b.card + 2 ∨ genTerminates a)
    {z : ℂ} (hz : z ∈ Complex.slitPlane ∩ genAnalyticDomain a (γ ::ₘ b)) :
    iteratedDeriv n (fun z => z ^ (γ - 1) * genHG a (γ ::ₘ b) z) z =
      poch (γ - n) n * z ^ (γ - n - 1) * genHG a ((γ - n) ::ₘ b) z := by
  sorry

/-- Leibniz' rule for an analytic function times the identity, keeping just
the two nonzero derivatives of the identity function. -/
theorem genIteratedDeriv_id_mul (f : ℂ → ℂ) (n : ℕ) {z : ℂ} (hf : AnalyticAt ℂ f z) :
    iteratedDeriv (n + 1) (fun w => w * f w) z =
      z * iteratedDeriv (n + 1) f z + (n + 1) * iteratedDeriv n f z := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf.contDiffAt]
  let F : ℕ → ℂ := fun i => (n + 1).choose i *
    iteratedDeriv i (fun w : ℂ => w) z * iteratedDeriv (n + 1 - i) f z
  have hsub : ({0, 1} : Finset ℕ) ⊆ range (n + 1 + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp
  have hs : (∑ i ∈ ({0, 1} : Finset ℕ), F i) = ∑ i ∈ range (n + 1 + 1), F i := by
    apply Finset.sum_subset hsub
    intro i hi hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    simp [F, iteratedDeriv_fun_id, hnot.1, hnot.2]
  change (∑ i ∈ range (n + 1 + 1), F i) = _
  rw [← hs]
  simp [F, iteratedDeriv_fun_id]

/-- The general operator identity for every analytic germ and every natural order. -/
@[dlmf 16.3.E5]
theorem genRaiseOp_iterate (f : ℂ → ℂ) (n : ℕ) {z : ℂ} (hf : AnalyticAt ℂ f z) :
    (genRaiseOp^[n]) f z = z ^ n * iteratedDeriv n (fun z => z ^ n * f z) z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have heq : (fun w => w * (genRaiseOp^[n]) f w) =ᶠ[𝓝 z]
        (fun w => w ^ (n + 1) * iteratedDeriv n (fun w => w ^ n * f w) w) := by
      filter_upwards [hf.eventually_analyticAt] with w hw
      rw [ih hw]
      ring
    rw [Function.iterate_succ_apply', genRaiseOp, heq.deriv_eq]
    have hg : AnalyticAt ℂ (fun w => w ^ n * f w) z := by fun_prop
    have hD : HasDerivAt (iteratedDeriv n (fun w => w ^ n * f w))
        (iteratedDeriv (n + 1) (fun w => w ^ n * f w) z) z := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_eq_iterate] using
        (hg.iterated_deriv n).differentiableAt.hasDerivAt
    have hder : deriv (fun w => w ^ (n + 1) * iteratedDeriv n (fun w => w ^ n * f w) w) z =
        (n + 1) * z ^ n * iteratedDeriv n (fun w => w ^ n * f w) z +
          z ^ (n + 1) * iteratedDeriv (n + 1) (fun w => w ^ n * f w) z := by
      simpa only [id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one] using
        (((hasDerivAt_id z).fun_pow (n + 1)).fun_mul hD).deriv
    rw [hder]
    have hid := genIteratedDeriv_id_mul (fun w => w ^ n * f w) n hg
    have hfun : (fun w => w ^ (n + 1) * f w) = (fun w => w * (w ^ n * f w)) := by
      funext w
      ring
    rw [hfun, hid]
    simp only [pow_succ]
    ring

/-- Any q+2 contiguous functions are linearly dependent over rational functions. -/
theorem genContiguous_linear_relation {p q : ℕ} (hpq : p ≤ q + 1)
    (a : Fin (q + 2) → Fin p → ℂ) (b : Fin (q + 2) → Fin q → ℂ)
    (hb : ∀ i, genDenRegular (genParams (b i)))
    (hc : ∀ i, genContiguous (a 0) (a i) (b 0) (b i)) :
    ∃ P : Fin (q + 2) → Polynomial ℂ, (∃ i, P i ≠ 0) ∧
      ∀ z ∈ cutPlane, ∑ i, (P i).eval z * genHG (genParams (a i)) (genParams (b i)) z = 0 := by
  sorry

/-- The three contiguous ordinary 0F1 functions, with all three lower parameters regular. -/
@[dlmf 16.3.E6]
theorem genHG_0F1_contiguous (b z : ℂ) (hb : genDenRegular {b - 1, b, b + 1}) :
    z * genHG ∅ {b + 1} z + b * (b - 1) * genHG ∅ {b} z -
      b * (b - 1) * genHG ∅ {b - 1} z = 0 := by
  have hb₀ : b ≠ 0 := by simpa using hb b (by simp) 0
  have hb₁ : b - 1 ≠ 0 := by simpa using hb (b - 1) (by simp) 0
  have hΓ₀ := Complex.Gamma_add_one b hb₀
  have hΓ₁ := Complex.Gamma_add_one (b - 1) hb₁
  have hcont := Complex.regularizedHGFun_zero_singleton_eq_mul_add_mul (b - 1) z
  rw [show b - 1 + 1 = b by ring, show b - 1 + 2 = b + 1 by ring] at hcont
  rw [show b - 1 + 1 = b by ring] at hΓ₁
  simp [genHG, genRegularizedHG, genGamma, Multiset.empty_eq_zero]
  rw [hΓ₀, hΓ₁, hcont]
  ring

/-- The full four-term contiguous 3F2 identity. -/
@[dlmf 16.3.E7]
theorem genHG_3F2_contiguous (a₁ a₂ a₃ b₁ b₂ : ℂ) (hb : genDenRegular {b₁, b₂})
    {z : ℂ} (hz : z ∈ cutPlane) :
    genHG {a₁ + 2, a₂, a₃} {b₁, b₂} z * a₁ * (a₁ + 1) * (1 - z) +
    genHG {a₁ + 1, a₂, a₃} {b₁, b₂} z * a₁ *
      (b₁ + b₂ - 3 * a₁ - 2 + z * (2 * a₁ - a₂ - a₃ + 1)) +
    genHG {a₁, a₂, a₃} {b₁, b₂} z *
      ((2 * a₁ - b₁) * (2 * a₁ - b₂) + a₁ - a₁ ^ 2 - z * (a₁ - a₂) * (a₁ - a₃)) -
    genHG {a₁ - 1, a₂, a₃} {b₁, b₂} z * (a₁ - b₁) * (a₁ - b₂) = 0 := by
  sorry

end DLMF.Hypergeometric
