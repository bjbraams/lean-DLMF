/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Analytic.Basic

/-!
# Asymptotic power series: composition and inversion

An *asymptotic power series* of `f : α → 𝕜` in a small variable `w : α → 𝕜` along a filter `l`
is a Poincaré expansion `f ~ ∑ pₙ wⁿ` (`HasAsymptoticExpansion` with the scale `wⁿ`) whose
coefficients are those of a formal power series `P : 𝕜⟦X⟧`. With `w → 0`, these expansions form
an algebra on which `f ↦ P` acts as a ring homomorphism, and they are closed under composition
(formal substitution `PowerSeries.subst`) and reciprocals.

The main result is asymptotic (Lagrange) inversion: if `H ~ P(σ)` with `P = p₁X + O(X²)`,
`p₁ ≠ 0`, and `y` solves `H(y) = w` with `σ(y) → 0`, then `σ(y) ~ Q(w)` where
`Q = P.substInvOfIsUnit _` is the compositional inverse of `P`; all error bounds `O(wᴺ)` hold.
No a priori expansion of the solution is assumed: the estimate `σ(y) = O(w)` and the formal
identity `Q(P(X)) = X` give every order at once.

The McMahon form treats equations `ξ(x) + G(x) = T` with `G(x) ~ ∑ cₙ ξ(x)⁻ⁿ` (constant phase
shift `c₀` allowed) and a large variable `ξ`; a solution `x(T)` along any filter (for instance
indexed by `k : ℕ` with `T = βₖ → ∞`) satisfies `ξ(x) - T ~ ∑ dₙ T⁻ⁿ` with `d = mcMahonSeries C`,
and `D = mcMahonSeries C` is characterised formally by `D = -C(X (1 + X D)⁻¹)`.
An equation `F(x) = T` with `F(x) ~ x (1 + ∑_{n≥1} cₙ x⁻ⁿ)` is the case `G = F - ξ`.

## Main definitions

* `Asymptotics.HasAsymptoticPowerSeries l w P f`: `f ~ ∑ (coeff n P) wⁿ` along `l`.
* `Asymptotics.mcMahonSeries C`: the inverted coefficients of `x + G(x) = T`.

## Main results

* `HasAsymptoticPowerSeries.add`, `.mul`, `.pow`, `.aeval`, `.recip`, `.mul_var`, `.div_var`:
  algebra of asymptotic power series; `.unique`: uniqueness.
* `HasAsymptoticPowerSeries.comp`: composition `H ∘ y ~ P.subst Q`.
* `HasAsymptoticPowerSeries.analytic_comp`: composition with an analytic function.
* `HasAsymptoticPowerSeries.inversion`: asymptotic inversion.
* `HasAsymptoticPowerSeries.mcMahon`, `hasAsymptoticPowerSeries_mcMahon_atTop`: McMahon-type
  inversion `x = T + ∑ dₙ T⁻ⁿ`; `mcMahonSeries_spec`: the formal fixed-point identity.
* `hasAsymptoticPowerSeries_recip_iff`: translation to the scale `ξ^{-n}` of
  `HasAsymptoticExpansion`.
* `mcMahonSeries_coeff_le_two`: `d₀ = -c₀`, `d₁ = -c₁`, `d₂ = -(c₂ + c₀c₁)`.

Expansions whose coefficients are polynomials in a slowly varying parameter (logarithmic
terms, as in DLMF 7.13.1) are not covered.
-/

@[expose] public section

noncomputable section

open Filter Finset PowerSeries
open scoped Topology

namespace Asymptotics

variable {α β 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {w : α → 𝕜}

/-- `f` has the asymptotic power series `P` in the small variable `w` along `l`. -/
def HasAsymptoticPowerSeries (l : Filter α) (w : α → 𝕜) (P : 𝕜⟦X⟧) (f : α → 𝕜) : Prop :=
  HasAsymptoticExpansion l (fun n x => w x ^ n) (fun n => coeff n P) f

/-- Asymptotic power series via truncations: `f - (trunc N P)(w) = O(wᴺ)` for all `N`. -/
theorem hasAsymptoticPowerSeries_iff {P : 𝕜⟦X⟧} {f : α → 𝕜} :
    HasAsymptoticPowerSeries l w P f ↔
      ∀ N, (fun x => f x - (trunc N P).eval (w x)) =O[l] fun x => w x ^ N := by
  unfold HasAsymptoticPowerSeries HasAsymptoticExpansion
  refine forall_congr' fun N => ?_
  have : ∀ x, (trunc N P).eval (w x) = ∑ n ∈ range N, w x ^ n • coeff n P := fun x => by
    rw [Polynomial.eval, eval₂_trunc_eq_sum_range]
    exact sum_congr rfl fun n _ => by simp [smul_eq_mul, mul_comm]
  simp only [this]

/-- A polynomial whose coefficients below `N` vanish is `O(w^N)` at `w → 0`. -/
theorem asymInv_isBigO_eval_of_coeff_eq_zero (hw : Tendsto w l (𝓝 0)) {p : Polynomial 𝕜}
    {N : ℕ} (hp : ∀ n < N, p.coeff n = 0) :
    (fun x => p.eval (w x)) =O[l] fun x => w x ^ N := by
  obtain ⟨q, rfl⟩ := Polynomial.X_pow_dvd_iff.mpr hp
  have hq : (fun x => q.eval (w x)) =O[l] fun _ => (1 : 𝕜) :=
    ((q.continuous.tendsto 0).comp hw).isBigO_one 𝕜
  simpa using (isBigO_refl (fun x => w x ^ N) l).mul hq

/-- The value of a polynomial at `w → 0` is bounded. -/
theorem asymInv_isBigO_eval_one (hw : Tendsto w l (𝓝 0)) (p : Polynomial 𝕜) :
    (fun x => p.eval (w x)) =O[l] fun _ => (1 : 𝕜) :=
  ((p.continuous.tendsto 0).comp hw).isBigO_one 𝕜

namespace HasAsymptoticPowerSeries

variable {P Q : 𝕜⟦X⟧} {f g : α → 𝕜}

/-- The remainder after `N` terms is `O(wᴺ)`. -/
theorem remainder (hf : HasAsymptoticPowerSeries l w P f) (N : ℕ) :
    (fun x => f x - (trunc N P).eval (w x)) =O[l] fun x => w x ^ N :=
  hasAsymptoticPowerSeries_iff.mp hf N

/-- Asymptotic power series from remainder bounds. -/
theorem of_remainder
    (h : ∀ N, (fun x => f x - (trunc N P).eval (w x)) =O[l] fun x => w x ^ N) :
    HasAsymptoticPowerSeries l w P f :=
  hasAsymptoticPowerSeries_iff.mpr h

/-- A function with an asymptotic power series is bounded. -/
theorem isBigO_one (hf : HasAsymptoticPowerSeries l w P f) : f =O[l] fun _ => (1 : 𝕜) := by
  simpa using hf.remainder 0

/-- With vanishing constant term the function is `O(w)`. -/
theorem isBigO_of_constantCoeff_eq_zero (hf : HasAsymptoticPowerSeries l w P f)
    (hP : constantCoeff P = 0) : f =O[l] w := by
  simpa [trunc_one_left, hP] using hf.remainder 1

/-- The function tends to the constant coefficient. -/
theorem tendsto (hw : Tendsto w l (𝓝 0)) (hf : HasAsymptoticPowerSeries l w P f) :
    Tendsto f l (𝓝 (constantCoeff P)) := by
  have h := (hf.remainder 1).trans_tendsto (by simpa using hw)
  simp only [trunc_one_left, Polynomial.eval_C, coeff_zero_eq_constantCoeff_apply] at h
  simpa using h.add_const (constantCoeff P)

/-- Expansions compose with a map tending to the base filter. -/
theorem comp_tendsto {m : Filter β} {σ H : β → 𝕜} (hH : HasAsymptoticPowerSeries m σ P H)
    {y : α → β} (hy : Tendsto y l m) :
    HasAsymptoticPowerSeries l (fun x => σ (y x)) P (fun x => H (y x)) :=
  HasAsymptoticExpansion.comp_tendsto hH hy

/-- Asymptotic power series transfer along eventually equal functions. -/
theorem congr' (hf : HasAsymptoticPowerSeries l w P f) (h : f =ᶠ[l] g) :
    HasAsymptoticPowerSeries l w P g :=
  HasAsymptoticExpansion.congr' hf h

/-- A polynomial in `w` has itself as asymptotic power series. -/
theorem _root_.Asymptotics.hasAsymptoticPowerSeries_eval (hw : Tendsto w l (𝓝 0))
    (p : Polynomial 𝕜) :
    HasAsymptoticPowerSeries l w (p : 𝕜⟦X⟧) (fun x => p.eval (w x)) := by
  refine of_remainder fun N => ?_
  simp_rw [← Polynomial.eval_sub]
  refine asymInv_isBigO_eval_of_coeff_eq_zero hw fun n hn => ?_
  simp [coeff_trunc, hn]

/-- Constants. -/
theorem _root_.Asymptotics.hasAsymptoticPowerSeries_const (hw : Tendsto w l (𝓝 0)) (c : 𝕜) :
    HasAsymptoticPowerSeries l w (C c) (fun _ => c) := by
  simpa using hasAsymptoticPowerSeries_eval hw (Polynomial.C c)

/-- The variable itself has the series `X`. -/
theorem _root_.Asymptotics.hasAsymptoticPowerSeries_var (hw : Tendsto w l (𝓝 0)) :
    HasAsymptoticPowerSeries l w X w := by
  simpa using hasAsymptoticPowerSeries_eval hw Polynomial.X

/-- Sums. -/
theorem add (hf : HasAsymptoticPowerSeries l w P f) (hg : HasAsymptoticPowerSeries l w Q g) :
    HasAsymptoticPowerSeries l w (P + Q) (fun x => f x + g x) :=
  (HasAsymptoticExpansion.add hf hg).congr_coeff (funext fun _ => (map_add _ _ _).symm)

/-- Negation. -/
theorem neg (hf : HasAsymptoticPowerSeries l w P f) :
    HasAsymptoticPowerSeries l w (-P) (fun x => -f x) :=
  (HasAsymptoticExpansion.neg hf).congr_coeff (funext fun _ => (map_neg _ _).symm)

/-- Differences. -/
theorem sub (hf : HasAsymptoticPowerSeries l w P f) (hg : HasAsymptoticPowerSeries l w Q g) :
    HasAsymptoticPowerSeries l w (P - Q) (fun x => f x - g x) :=
  (HasAsymptoticExpansion.sub hf hg).congr_coeff (funext fun _ => (map_sub _ _ _).symm)

/-- Products: the series multiply as formal power series. -/
theorem mul (hw : Tendsto w l (𝓝 0)) (hf : HasAsymptoticPowerSeries l w P f)
    (hg : HasAsymptoticPowerSeries l w Q g) :
    HasAsymptoticPowerSeries l w (P * Q) (fun x => f x * g x) := by
  refine of_remainder fun N => ?_
  have h1 : (fun x => (f x - (trunc N P).eval (w x)) * g x) =O[l] fun x => w x ^ N := by
    simpa using (hf.remainder N).mul hg.isBigO_one
  have h2 : (fun x => (trunc N P).eval (w x) * (g x - (trunc N Q).eval (w x))) =O[l]
      fun x => w x ^ N := by
    simpa using (asymInv_isBigO_eval_one hw (trunc N P)).mul (hg.remainder N)
  have h3 : (fun x => (trunc N P * trunc N Q - trunc N (P * Q)).eval (w x)) =O[l]
      fun x => w x ^ N := by
    refine asymInv_isBigO_eval_of_coeff_eq_zero hw fun n hn => ?_
    rw [Polynomial.coeff_sub, coeff_trunc, ← Polynomial.coeff_coe,
      Polynomial.coe_mul, ← coeff_mul_eq_coeff_trunc_mul_trunc _ _ hn]
    simp [hn]
  refine ((h1.add h2).add h3).congr' (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => by simp)
  simp only [Polynomial.eval_sub, Polynomial.eval_mul]
  ring

/-- The constant `1`. -/
theorem one (hw : Tendsto w l (𝓝 0)) : HasAsymptoticPowerSeries l w 1 (fun _ => (1 : 𝕜)) := by
  simpa using hasAsymptoticPowerSeries_const hw (1 : 𝕜)

/-- Powers. -/
theorem pow (hw : Tendsto w l (𝓝 0)) (hf : HasAsymptoticPowerSeries l w P f) (n : ℕ) :
    HasAsymptoticPowerSeries l w (P ^ n) (fun x => f x ^ n) := by
  induction n with
  | zero => simpa using one hw
  | succ n ih => simpa [pow_succ] using ih.mul hw hf

/-- Constant multiples. -/
theorem const_mul (hw : Tendsto w l (𝓝 0)) (hf : HasAsymptoticPowerSeries l w P f) (c : 𝕜) :
    HasAsymptoticPowerSeries l w (C c * P) (fun x => c * f x) :=
  (hasAsymptoticPowerSeries_const hw c).mul hw hf

/-- Polynomial expressions in `f` have the formally substituted power series. -/
theorem aeval (hw : Tendsto w l (𝓝 0)) (hf : HasAsymptoticPowerSeries l w P f)
    (q : Polynomial 𝕜) :
    HasAsymptoticPowerSeries l w (Polynomial.aeval P q) (fun x => q.eval (f x)) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n c =>
    simpa [← C_eq_algebraMap, Polynomial.aeval_monomial] using
      (hf.pow hw n).const_mul hw c |>.congr' (Eventually.of_forall fun x => by simp)

end HasAsymptoticPowerSeries

/-- Truncations of a substitution only see the truncation of the outer series. -/
theorem asymInv_trunc_subst {P Q : 𝕜⟦X⟧} (hQ : constantCoeff Q = 0) (N : ℕ) :
    trunc N (P.subst Q) = trunc N (Polynomial.aeval Q (trunc N P)) := by
  have hs : HasSubst Q := HasSubst.of_constantCoeff_zero' hQ
  obtain ⟨R, hR⟩ := X_dvd_iff.mpr hQ
  conv_lhs => rw [eq_X_pow_mul_shift_add_trunc N P]
  rw [subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_coe hs, map_add, hR,
    mul_pow, mul_assoc, trunc_X_pow_self_mul, zero_add]

namespace HasAsymptoticPowerSeries

variable {P Q : 𝕜⟦X⟧} {f g : α → 𝕜}

/-- Composition of asymptotic power series: if `H ~ P(σ)` along `m`, and along `l` the inner
variable `σ ∘ y` has an asymptotic power series `Q(w)` without constant term, then
`H ∘ y ~ P(Q(w))`. -/
theorem comp {m : Filter β} {σ H : β → 𝕜} (hH : HasAsymptoticPowerSeries m σ P H) {y : α → β}
    (hy : Tendsto y l m) (hw : Tendsto w l (𝓝 0)) (hQ : constantCoeff Q = 0)
    (hs : HasAsymptoticPowerSeries l w Q (fun x => σ (y x))) :
    HasAsymptoticPowerSeries l w (P.subst Q) (fun x => H (y x)) := by
  refine of_remainder fun N => ?_
  have h1 : (fun x => H (y x) - (trunc N P).eval (σ (y x))) =O[l] fun x => w x ^ N :=
    ((hH.remainder N).comp_tendsto hy).trans
      ((hs.isBigO_of_constantCoeff_eq_zero hQ).pow N)
  have h2 := (hs.aeval hw (trunc N P)).remainder N
  rw [← asymInv_trunc_subst hQ] at h2
  exact (h1.add h2).congr_left fun x => by ring

/-- **Asymptotic inversion.** Let `H ~ P(σ)` along `m`, where `σ → 0`, `P` has no constant
term and an invertible linear coefficient. If `y : α → β` tends to `m` and solves `H (y x) = w x`
eventually, then `σ ∘ y` has the asymptotic power series of the compositional inverse of `P`
in the variable `w`. -/
theorem inversion {m : Filter β} {σ H : β → 𝕜} (hσ : Tendsto σ m (𝓝 0))
    (hH : HasAsymptoticPowerSeries m σ P H) (hP0 : constantCoeff P = 0) (hP1 : coeff 1 P ≠ 0)
    {y : α → β} (hy : Tendsto y l m) (heq : ∀ᶠ x in l, H (y x) = w x) :
    HasAsymptoticPowerSeries l w (P.substInvOfIsUnit hP1.isUnit) (fun x => σ (y x)) := by
  set s : α → 𝕜 := fun x => σ (y x) with hs_def
  have hs0 : Tendsto s l (𝓝 0) := hσ.comp hy
  have hW : HasAsymptoticPowerSeries l s P w :=
    (hH.comp_tendsto hy).congr' heq
  have hw : Tendsto w l (𝓝 0) := by simpa [hP0] using hW.tendsto hs0
  -- `s = O(w)`
  have hsw : s =O[l] w := by
    have h2 := hW.remainder 2
    have htr : ∀ x, (trunc 2 P).eval (s x) = coeff 1 P * s x := fun x => by
      rw [Polynomial.eval, eval₂_trunc_eq_sum_range]
      simp [sum_range_succ, hP0]
    simp only [htr] at h2
    have hsq : (fun x => s x ^ 2) =o[l] fun x => coeff 1 P * s x := by
      refine (isLittleO_const_mul_right_iff hP1).mpr ?_
      have : (fun x => s x * s x) =o[l] fun x => (1 : 𝕜) * s x :=
        ((isLittleO_one_iff 𝕜).mpr hs0).mul_isBigO (isBigO_refl s l)
      simpa [sq] using this
    have h3 := (h2.trans_isLittleO hsq).right_isBigO_add
    have h4 : (fun x => coeff 1 P * s x) =O[l] w := h3.congr_right fun x => by ring
    exact (isBigO_const_mul_left_iff hP1).mp h4
  refine of_remainder fun N => ?_
  rcases Nat.lt_or_ge N 2 with hN | hN
  · obtain rfl | rfl : N = 0 ∨ N = 1 := by omega
    · simpa using hs0.isBigO_one 𝕜
    · simpa [trunc_one_left] using hsw
  · have h := (hW.aeval hs0 (trunc N (P.substInvOfIsUnit hP1.isUnit))).remainder N
    rw [← asymInv_trunc_subst hP0, subst_substInvOfIsUnit_left _ hP0, trunc_X_of hN] at h
    have h' := (h.trans (hsw.pow N)).neg_left
    exact h'.congr_left fun x => by simp

/-- Reciprocal of an asymptotic power series with nonzero constant term. -/
theorem recip (hw : Tendsto w l (𝓝 0)) (hf : HasAsymptoticPowerSeries l w P f)
    (hP : constantCoeff P ≠ 0) :
    HasAsymptoticPowerSeries l w P⁻¹ (fun x => (f x)⁻¹) := by
  have hlim : Tendsto (fun x => (f x)⁻¹) l (𝓝 (constantCoeff P)⁻¹) :=
    (hf.tendsto hw).inv₀ hP
  have hne : ∀ᶠ x in l, f x ≠ 0 := (hf.tendsto hw).eventually_ne hP
  refine of_remainder fun N => ?_
  cases N with
  | zero => simpa using hlim.isBigO_one 𝕜
  | succ N =>
    have h := (hf.mul hw (hasAsymptoticPowerSeries_eval hw (trunc (N + 1) P⁻¹))).remainder
      (N + 1)
    rw [trunc_mul_trunc, PowerSeries.mul_inv_cancel _ hP, trunc_one] at h
    have h' := (hlim.isBigO_one 𝕜).mul h.neg_left
    refine (h'.trans (by simpa using isBigO_refl (fun x => w x ^ (N + 1)) l)).congr'
      (hne.mono fun x hx => ?_) EventuallyEq.rfl
    simp only [Polynomial.eval_one]
    field_simp
    ring

/-- Multiplying by the variable shifts the series. -/
theorem mul_var (hw : Tendsto w l (𝓝 0)) (hf : HasAsymptoticPowerSeries l w P f) :
    HasAsymptoticPowerSeries l w (X * P) (fun x => w x * f x) :=
  (hasAsymptoticPowerSeries_var hw).mul hw hf

/-- Dividing a series without constant term by the variable shifts it down. -/
theorem div_var (hf : HasAsymptoticPowerSeries l w P f) (hP : constantCoeff P = 0)
    (hw0 : ∀ᶠ x in l, w x ≠ 0) :
    HasAsymptoticPowerSeries l w (mk fun n => coeff (n + 1) P) (fun x => f x / w x) := by
  refine of_remainder fun N => ?_
  have h := hf.remainder (N + 1)
  have htr : ∀ x, (trunc (N + 1) P).eval (w x) =
      w x * (trunc N (mk fun n => coeff (n + 1) P)).eval (w x) := fun x => by
    simp only [Polynomial.eval, eval₂_trunc_eq_sum_range, sum_range_succ', coeff_mk,
      coeff_zero_eq_constantCoeff_apply, hP, mul_sum]
    simp [pow_succ]
    exact sum_congr rfl fun n _ => by ring
  have h' := h.mul (isBigO_refl (fun x => (w x)⁻¹) l)
  refine h'.congr' (hw0.mono fun x hx => ?_) (hw0.mono fun x hx => ?_)
  · simp only [htr]
    field_simp
  · simp only
    field_simp
    ring

/-- Uniqueness of asymptotic power series. -/
theorem unique (hw : Tendsto w l (𝓝 0)) (hne : ∃ᶠ x in l, w x ≠ 0)
    (hP : HasAsymptoticPowerSeries l w P f) (hQ : HasAsymptoticPowerSeries l w Q f) : P = Q := by
  have hsc : IsAsymptoticScale l (fun n x => w x ^ n) := fun n => by
    have := ((isLittleO_one_iff 𝕜).mpr hw).mul_isBigO (isBigO_refl (fun x => w x ^ n) l)
    simpa [pow_succ, mul_comm] using this
  have h := HasAsymptoticExpansion.unique hsc (fun n => hne.mono fun x hx => pow_ne_zero n hx)
    hP hQ
  ext n
  exact congrFun h n

end HasAsymptoticPowerSeries

/-- The phase series `X (1 + X C)⁻¹`: if `G(x) ~ C(1/x)`, then `1/(x + G(x)) ~ P(1/x)` for
this `P`. -/
def asymInv_mcMahonPhase (C : 𝕜⟦X⟧) : 𝕜⟦X⟧ := X * (1 + X * C)⁻¹

/-- The phase series has no constant term. -/
theorem asymInv_constantCoeff_mcMahonPhase (C : 𝕜⟦X⟧) :
    constantCoeff (asymInv_mcMahonPhase C) = 0 := by
  simp [asymInv_mcMahonPhase]

/-- The phase series has linear coefficient `1`. -/
theorem asymInv_coeff_one_mcMahonPhase (C : 𝕜⟦X⟧) :
    coeff 1 (asymInv_mcMahonPhase C) = 1 := by
  rw [asymInv_mcMahonPhase, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_inv]
  simp

/-- The McMahon series of `C`: the coefficients `dₙ` of the inverted expansion
`x = T + ∑ dₙ T⁻ⁿ` of the solution of `x + G(x) = T`, where `G(x) ~ ∑ cₙ x⁻ⁿ`.
It is built from the compositional inverse `Q` of `X (1 + X C)⁻¹` (the expansion of `1/x` in
powers of `1/T`) as the shifted coefficients of `(Q/X)⁻¹`. -/
def mcMahonSeries (C : 𝕜⟦X⟧) : 𝕜⟦X⟧ :=
  mk fun n => coeff (n + 1) (mk fun k => coeff (k + 1) ((asymInv_mcMahonPhase C).substInvOfIsUnit
    (by rw [asymInv_coeff_one_mcMahonPhase]; exact isUnit_one)))⁻¹

namespace HasAsymptoticPowerSeries

/-- **McMahon-type inversion.** Let `ξ : β → 𝕜` be a large variable along `m` (`1/ξ → 0`,
`ξ ≠ 0` eventually) and `G ~ ∑ cₙ ξ⁻ⁿ`. If `y : α → β` tends to `m` and solves
`ξ (y a) + G (y a) = T a` eventually, then
`ξ (y a) - T a ~ ∑ dₙ (T a)⁻ⁿ` with `d = mcMahonSeries C`, with `O(T⁻ᴺ)` error bounds for
every `N`. The constant term `c₀` (a phase shift) is allowed. -/
theorem mcMahon {m : Filter β} {ξ G : β → 𝕜} {C : 𝕜⟦X⟧}
    (hξ : Tendsto (fun b => (ξ b)⁻¹) m (𝓝 0)) (hξ0 : ∀ᶠ b in m, ξ b ≠ 0)
    (hG : HasAsymptoticPowerSeries m (fun b => (ξ b)⁻¹) C G) {y : α → β} (hy : Tendsto y l m)
    {T : α → 𝕜} (heq : ∀ᶠ a in l, ξ (y a) + G (y a) = T a) :
    HasAsymptoticPowerSeries l (fun a => (T a)⁻¹) (mcMahonSeries C)
      (fun a => ξ (y a) - T a) := by
  set σ : β → 𝕜 := fun b => (ξ b)⁻¹
  set P := asymInv_mcMahonPhase C with hP_def
  have hP0 : constantCoeff P = 0 := asymInv_constantCoeff_mcMahonPhase C
  have hP1 : coeff 1 P = 1 := asymInv_coeff_one_mcMahonPhase C
  have hP1' : coeff 1 P ≠ 0 := by rw [hP1]; exact one_ne_zero
  -- `1/(ξ + G) ~ P(1/ξ)`
  have hH : HasAsymptoticPowerSeries m σ P (fun b => (ξ b + G b)⁻¹) := by
    have h1 := (((one hξ).add (hG.mul_var hξ)).recip hξ (by simp)).mul_var hξ
    refine h1.congr' (hξ0.mono fun b hb => ?_)
    simp only [σ]
    rw [← mul_inv, mul_add, mul_one, mul_inv_cancel_left₀ hb]
  have heq' : ∀ᶠ a in l, (ξ (y a) + G (y a))⁻¹ = (T a)⁻¹ := heq.mono fun a ha => by rw [ha]
  have hs := hH.inversion hξ hP0 hP1' hy heq'
  set Q := P.substInvOfIsUnit hP1'.isUnit with hQ_def
  have hQ0 : constantCoeff Q = 0 := constantCoeff_substInvOfIsUnit _ _
  have hQ1 : coeff 1 Q = 1 := by
    rw [hQ_def, coeff_one_substInvOfIsUnit]
    have : hP1'.isUnit.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hP1]; rfl)
    rw [this]; rfl
  -- the variable `w = 1/T`
  have hw : Tendsto (fun a => (T a)⁻¹) l (𝓝 0) := by
    have h := (hH.comp_tendsto hy).tendsto (hξ.comp hy)
    rw [hP0] at h
    exact h.congr' heq'
  have hs0 : ∀ᶠ a in l, σ (y a) ≠ 0 := (hy.eventually hξ0).mono fun a ha => inv_ne_zero ha
  have hw0 : ∀ᶠ a in l, (T a)⁻¹ ≠ 0 := by
    obtain ⟨c, hc⟩ := (hs.isBigO_of_constantCoeff_eq_zero hQ0).bound
    filter_upwards [hc, hs0] with a ha hsa
    intro h0
    rw [h0, norm_zero, mul_zero] at ha
    exact hsa (norm_le_zero_iff.mp ha)
  have hq := hs.div_var hQ0 hw0
  have hq' := (hq.recip hw (by simp [hQ1])).sub (one hw)
  have hq'0 : constantCoeff ((mk fun k => coeff (k + 1) Q)⁻¹ - 1) = 0 := by
    simp [hQ1]
  have hfin := hq'.div_var hq'0 hw0
  have hD : (mk fun n => coeff (n + 1) ((mk fun k => coeff (k + 1) Q)⁻¹ - 1)) =
      mcMahonSeries C := by
    ext n
    simp [mcMahonSeries, hQ_def, coeff_one]
    rfl
  rw [hD] at hfin
  refine hfin.congr' ((hy.eventually hξ0).and hw0 |>.mono fun a ⟨h1, h2⟩ => ?_)
  simp only [σ]
  have hT : T a ≠ 0 := fun h => h2 (by simp [h])
  field_simp

end HasAsymptoticPowerSeries

/-- The formal McMahon identities: with `Q` the compositional inverse of `X (1 + X C)⁻¹` and
`D = mcMahonSeries C`, one has `Q = X (1 + X D)⁻¹` and `D = -C(Q)`. Thus
`D = -C(X (1 + X D)⁻¹)`, the formal form of `x - T = -G(x)` with `1/x = (1/T)/(1 + (x-T)/T)`. -/
theorem mcMahonSeries_spec (C : 𝕜⟦X⟧) :
    (asymInv_mcMahonPhase C).substInvOfIsUnit
        (by rw [asymInv_coeff_one_mcMahonPhase]; exact isUnit_one) =
      X * (1 + X * mcMahonSeries C)⁻¹ ∧
    mcMahonSeries C = -(C.subst (X * (1 + X * mcMahonSeries C)⁻¹ : 𝕜⟦X⟧)) := by
  set hu : IsUnit (coeff 1 (asymInv_mcMahonPhase C)) :=
    (by rw [asymInv_coeff_one_mcMahonPhase]; exact isUnit_one)
  set Q := (asymInv_mcMahonPhase C).substInvOfIsUnit hu with hQ_def
  have hQ0 : constantCoeff Q = 0 := constantCoeff_substInvOfIsUnit _ _
  have hQs : HasSubst Q := HasSubst.of_constantCoeff_zero' hQ0
  have hQ1 : coeff 1 Q = 1 := by
    rw [hQ_def, coeff_one_substInvOfIsUnit]
    have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, asymInv_coeff_one_mcMahonPhase]; rfl)
    rw [this]; rfl
  set U : 𝕜⟦X⟧ := 1 + X * C
  have hU : constantCoeff U ≠ 0 := by simp [U]
  -- `Q = X (1 + Q C(Q))`
  have hA : Q = X * (1 + Q * C.subst Q) := by
    have h1 : (asymInv_mcMahonPhase C).subst Q = X :=
      subst_substInvOfIsUnit_right _ (asymInv_constantCoeff_mcMahonPhase C) hu
    have h2 : U⁻¹.subst Q * U.subst Q = 1 := by
      rw [← subst_mul hQs, PowerSeries.inv_mul_cancel _ hU, ← Polynomial.coe_one,
        subst_coe hQs, map_one, Polynomial.coe_one]
    have h3 : U.subst Q = 1 + Q * C.subst Q := by
      rw [subst_add hQs, subst_mul hQs, subst_X hQs, ← Polynomial.coe_one, subst_coe hQs,
        map_one, Polynomial.coe_one]
    rw [asymInv_mcMahonPhase, subst_mul hQs, subst_X hQs] at h1
    rw [← h3, ← h1, mul_assoc, h2, mul_one]
  set Q' : 𝕜⟦X⟧ := mk fun k => coeff (k + 1) Q
  have hQQ' : Q = X * Q' := by
    ext n
    cases n with
    | zero => simp [hQ0]
    | succ n => simp [Q', coeff_succ_X_mul]
  have hQ'0 : constantCoeff Q' = 1 := by simp [Q', ← hQ1]
  have hB : Q' = 1 + X * Q' * C.subst Q := by
    have hQC : Q * C.subst Q = X * Q' * C.subst Q := congrArg (· * C.subst Q) hQQ'
    have h' : X * Q' = X * (1 + X * Q' * C.subst Q) := by
      rw [← hQC, ← hQQ']; exact hA
    exact mul_left_cancel₀ X_ne_zero h'
  set D := mcMahonSeries C
  have hD : Q'⁻¹ = 1 + X * D := by
    ext n
    cases n with
    | zero => simp [hQ'0]
    | succ n => simp [D, mcMahonSeries, Q', hQ_def, coeff_succ_X_mul, coeff_one]
  have hC : Q'⁻¹ = 1 - X * C.subst Q := by
    have hne : constantCoeff Q' ≠ 0 := by rw [hQ'0]; exact one_ne_zero
    have := congrArg (fun F => Q'⁻¹ * F) hB
    simp only [mul_add, mul_one, PowerSeries.inv_mul_cancel _ hne] at this
    rw [show Q'⁻¹ * (X * Q' * C.subst Q) = (Q'⁻¹ * Q') * (X * C.subst Q) by ring,
      PowerSeries.inv_mul_cancel _ hne, one_mul] at this
    rw [this]; ring
  have hQ'inv : Q' = (1 + X * D)⁻¹ := by
    have hne : constantCoeff (1 + X * D) ≠ 0 := by simp
    rw [PowerSeries.eq_inv_iff_mul_eq_one hne, ← hD, PowerSeries.mul_inv_cancel]
    rw [hQ'0]; exact one_ne_zero
  have hQX : Q = X * (1 + X * D)⁻¹ := by rw [hQQ', hQ'inv]
  refine ⟨hQX, ?_⟩
  have : X * D = X * -(C.subst Q) := by
    have := hD.symm.trans hC
    rw [mul_neg]; linear_combination this
  rw [← hQX]
  exact mul_left_cancel₀ X_ne_zero this

/-- The first three McMahon coefficients: `d₀ = -c₀`, `d₁ = -c₁`, `d₂ = -(c₂ + c₀ c₁)`. -/
theorem mcMahonSeries_coeff_le_two (G : 𝕜⟦X⟧) :
    coeff 0 (mcMahonSeries G) = -coeff 0 G ∧ coeff 1 (mcMahonSeries G) = -coeff 1 G ∧
      coeff 2 (mcMahonSeries G) = -(coeff 2 G + coeff 0 G * coeff 1 G) := by
  set D := mcMahonSeries G
  have hspec := (mcMahonSeries_spec G).2
  set V : 𝕜⟦X⟧ := (1 + X * D)⁻¹
  set Q : 𝕜⟦X⟧ := X * V
  have hQ0 : constantCoeff Q = 0 := by simp [Q]
  have hV0 : coeff 0 V = 1 := by simp [V]
  have hV1 : coeff 1 V = -coeff 0 D := by
    have h1 : V * (1 + X * D) = 1 := PowerSeries.inv_mul_cancel _ (by simp)
    have := congrArg (coeff 1) h1
    simp [mul_add, coeff_one, coeff_mul, Finset.Nat.antidiagonal_succ, hV0] at this
    rw [coeff_zero_eq_constantCoeff_apply]
    linear_combination this
  -- coefficients of `C(Q)` below `3`
  have hsub : ∀ n < 3, coeff n (G.subst Q) =
      coeff n (PowerSeries.C (coeff 0 G) + PowerSeries.C (coeff 1 G) * Q +
        PowerSeries.C (coeff 2 G) * Q ^ 2) := by
    intro n hn
    have h := congrArg (fun p => Polynomial.coeff p n) (asymInv_trunc_subst (P := G) hQ0 3)
    simp only [coeff_trunc, hn, ite_true] at h
    rw [h]
    simp [trunc_succ, Polynomial.aeval_monomial]
  have hc := fun n => congrArg (coeff n) hspec
  have h0 : coeff 0 D = -coeff 0 G := by
    rw [hc 0, map_neg, hsub 0 (by norm_num)]
    simp [Q, hQ0]
  refine ⟨h0, ?_, ?_⟩
  · rw [hc 1, map_neg, hsub 1 (by norm_num)]
    simp [Q, coeff_mul, Finset.Nat.antidiagonal_succ, hV0, pow_two]
  · rw [hc 2, map_neg, hsub 2 (by norm_num)]
    simp [Q, coeff_mul, Finset.Nat.antidiagonal_succ, hV0, hV1, pow_two, coeff_X]
    rw [← coeff_zero_eq_constantCoeff_apply, h0, ← coeff_zero_eq_constantCoeff_apply]
    ring

/-- Asymptotic power series in `ξ⁻¹` are expansions in the scale `ξ^{-n}`. -/
theorem hasAsymptoticPowerSeries_recip_iff {ξ : α → 𝕜} {P : 𝕜⟦X⟧} {f : α → 𝕜} :
    HasAsymptoticPowerSeries l (fun x => (ξ x)⁻¹) P f ↔
      HasAsymptoticExpansion l (fun n x => ξ x ^ (-(n : ℤ))) (fun n => coeff n P) f := by
  have : (fun (n : ℕ) x => (ξ x)⁻¹ ^ n) = fun (n : ℕ) x => ξ x ^ (-(n : ℤ)) := by
    funext n x; simp [zpow_neg, inv_pow]
  rw [HasAsymptoticPowerSeries, this]

/-- **McMahon-type inversion on the real line**, for sequences or any other index filter:
if `G(x) ~ ∑ cₙ x⁻ⁿ` as `x → +∞`, `y → +∞` along `l` and `y + G(y) = T` eventually, then
`y - T ~ ∑ dₙ T⁻ⁿ` with `d = mcMahonSeries C`. -/
theorem hasAsymptoticPowerSeries_mcMahon_atTop {G : ℝ → ℝ} {C : ℝ⟦X⟧}
    (hG : HasAsymptoticPowerSeries atTop (fun x => x⁻¹) C G) {y : α → ℝ}
    (hy : Tendsto y l atTop) {T : α → ℝ} (heq : ∀ᶠ a in l, y a + G (y a) = T a) :
    HasAsymptoticPowerSeries l (fun a => (T a)⁻¹) (mcMahonSeries C) (fun a => y a - T a) :=
  hG.mcMahon (ξ := id) tendsto_inv_atTop_zero (eventually_ne_atTop 0) hy heq

section Analytic

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂] {w : α → 𝕂}

/-- An analytic function at `c` has its Taylor series as asymptotic power series in `z - c`. -/
theorem hasAsymptoticPowerSeries_of_hasFPowerSeriesAt {φ : 𝕂 → 𝕂}
    {p : FormalMultilinearSeries 𝕂 𝕂 𝕂} {c : 𝕂} (h : HasFPowerSeriesAt φ p c) :
    HasAsymptoticPowerSeries (𝓝 c) (fun z => z - c) (mk fun n => p.coeff n) φ := by
  refine HasAsymptoticPowerSeries.of_remainder fun N => ?_
  have hc : Tendsto (fun z : 𝕂 => z - c) (𝓝 c) (𝓝 0) := by
    simpa using (continuous_sub_right c).tendsto c
  have h1 := (h.isBigO_sub_partialSum_pow N).comp_tendsto hc
  have h2 : (fun z : 𝕂 => ‖z - c‖ ^ N) =O[𝓝 c] fun z => (z - c) ^ N := by
    simpa [norm_pow] using (isBigO_refl (fun z : 𝕂 => (z - c) ^ N) (𝓝 c)).norm_left
  refine (h1.trans h2).congr_left fun z => ?_
  simp only [Function.comp_apply, add_sub_cancel, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, Polynomial.eval, eval₂_trunc_eq_sum_range,
    coeff_mk, smul_eq_mul, RingHom.id_apply]
  congr 1
  exact sum_congr rfl fun n _ => mul_comm _ _

/-- Composition of an analytic function with an asymptotic power series. -/
theorem HasAsymptoticPowerSeries.analytic_comp {φ : 𝕂 → 𝕂}
    {p : FormalMultilinearSeries 𝕂 𝕂 𝕂} {P : 𝕂⟦X⟧} {f : α → 𝕂}
    (h : HasFPowerSeriesAt φ p (constantCoeff P)) (hw : Tendsto w l (𝓝 0))
    (hf : HasAsymptoticPowerSeries l w P f) :
    HasAsymptoticPowerSeries l w ((mk fun n => p.coeff n).subst (P - C (constantCoeff P)))
      (fun x => φ (f x)) := by
  refine (hasAsymptoticPowerSeries_of_hasFPowerSeriesAt h).comp (hf.tendsto hw) hw (by simp) ?_
  exact hf.sub (hasAsymptoticPowerSeries_const hw _)

end Analytic

end Asymptotics
