/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.AnalyticProperties
public import DLMF.GeneralizedHypergeometric.Derivatives
public import DLMFMathlib.Analysis.ODE.Singularities
public import Mathlib.Algebra.Group.ForwardDiff

/-!
# Differential equations and confluence of `ₚF_q` (DLMF §16.8)

## Main definitions

* `genNormalizedODE`, `genD`: the normalized differential equation and the differentiation
  operator, DLMF 16.8.1–16.8.2 (`θ` is the existing `eulerTheta`).
* `genODEAlpha`, `genODEBeta`, `genODECoeff`, `genODEOrder`: the expanded equation.
* `GenODESolution`, `GenFundamentalSystem`: solutions and fundamental systems.
* `genFrobeniusZero`, `genFrobeniusInfinityLog`: Frobenius solutions at `0` and `∞`,
  DLMF 16.8.6–16.8.7.

## Main results

* `generalizedHypergeometric_theta_ode`: the `θ`-equation on the principal analytic domain, DLMF
  16.8.3 (`generalizedHypergeometric_theta_ode'` without the regularity hypothesis).
* `generalizedHypergeometric_expanded_ode_entire`,
  `generalizedHypergeometric_expanded_ode_balanced`: the expanded equations, DLMF 16.8.4–16.8.5
  (`generalizedHypergeometric_expanded_ode_balanced'` without the regularity hypothesis).
* `generalizedHypergeometric_ode_singularities_entire`,
  `generalizedHypergeometric_ode_singularities_balanced`,
  `generalizedHypergeometric_ode_nominal_order`: classification of the singularities and the order
  (the primed classifications drop the regularity hypothesis).
* `genFrobeniusZero_fundamental`, `genFrobeniusInfinity_fundamental`: fundamental systems at
  `0` and `∞`; `genFrobeniusZero_resonant`, `genFrobeniusInfinity_resonant` for the resonant
  cases.
* `generalizedHypergeometric_infinity_connection`,
  `generalizedHypergeometric_centered_infinity_connection`: connection formulas, DLMF 16.8.8–16.8.9.
* `generalizedHypergeometric_upper_confluence`, `generalizedHypergeometric_lower_confluence`:
  confluence, DLMF 16.8.10–16.8.11.

## Implementation notes

Stirling numbers convert `θ`-polynomials to ordinary derivative coefficients. Singularities are
classified by their coefficient germs: removable parameter specializations are allowed, and
`q = 0` is not declared singular at zero. Fundamental systems include resonant logarithmic
Frobenius series. Connection formulas retain correlated logarithm sheets; a displaced center
uses the common connected principal component rather than unrelated cut determinations. The
order computation uses Mathlib's degree formula for products of monic polynomials, including
empty parameter multisets.
-/

@[expose] public section
open Complex Filter Set Finset Polynomial
open scoped Topology Real fwdDiff
noncomputable section
namespace DLMF.Hypergeometric

/-- Normalized scalar ODE value (16.8.1). -/
@[dlmf 16.8.E1]
def genNormalizedODE {n : ℕ} (c : Fin n → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.linearODEValue c f z

/-- Differentiation operator; theta itself is the existing `eulerTheta` (16.8.2). -/
@[dlmf 16.8.E2]
def genD (f : ℂ → ℂ) : ℂ → ℂ := deriv f

/-- Upper-parameter theta polynomial. -/
def genThetaA (a : Multiset ℂ) : Polynomial ℂ := (a.map fun x => X + C x).prod

/-- Lower-parameter theta polynomial. -/
def genThetaB (b : Multiset ℂ) : Polynomial ℂ := X * (b.map fun x => X + C (x - 1)).prod

/-- Ordinary derivative coefficient of a theta polynomial, with the power of z removed. -/
def genThetaDCoeff (P : Polynomial ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ range (P.natDegree + 1), P.coeff k * (Nat.stirlingSecond k j : ℂ)

/-- The alpha constants in the expanded equation. -/
def genODEAlpha (a : Multiset ℂ) (j : ℕ) : ℂ := -genThetaDCoeff (genThetaA a) j

/-- The beta constants in the expanded equation. -/
def genODEBeta (b : Multiset ℂ) (j : ℕ) : ℂ := genThetaDCoeff (genThetaB b) j

/-- Nominal order of the full generalized hypergeometric operator. -/
def genODEOrder (a b : Multiset ℂ) : ℕ := max a.card (b.card + 1)

/-- Normalized derivative coefficients of the generalized hypergeometric operator. -/
def genODECoeff (a b : Multiset ℂ) (j : Fin (genODEOrder a b)) (z : ℂ) : ℂ :=
  (genThetaDCoeff (genThetaB b) j.val * z ^ j.val -
    genThetaDCoeff (genThetaA a) j.val * z ^ (j.val + 1)) /
  (genThetaDCoeff (genThetaB b) (genODEOrder a b) * z ^ genODEOrder a b -
    genThetaDCoeff (genThetaA a) (genODEOrder a b) * z ^ (genODEOrder a b + 1))

/-- Vanishing of the generalized hypergeometric theta operator. -/
def GenODESolution (a b : Multiset ℂ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  thetaPoly (genThetaB b) f z = z * thetaPoly (genThetaA a) f z

/-- A fundamental system on an open domain, expressed by independence and full span. -/
def GenFundamentalSystem {n : ℕ} (a b : Multiset ℂ) (D : Set ℂ)
    (F : Fin n → ℂ → ℂ) : Prop :=
  (∀ i, AnalyticOnNhd ℂ (F i) D ∧ ∀ z ∈ D, GenODESolution a b (F i) z) ∧
  LinearIndependent ℂ (fun i => fun z : D => F i z) ∧
  ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f D → (∀ z ∈ D, GenODESolution a b f z) →
    ∃ c : Fin n → ℂ, ∀ z ∈ D, f z = ∑ i, c i * F i z

/-- The common principal zero-to-one slit domain for Frobenius solutions at zero. -/
def genFrobeniusDomain : Set ℂ := Complex.slitPlane ∩ cutPlane

/-- The q+1 Frobenius exponents at zero. -/
def genFrobeniusRoot {q : ℕ} (b : Fin q → ℂ) : Fin (q + 1) → ℂ :=
  Fin.cases 0 (fun j => 1 - b j)

/-- The nonresonant Frobenius solutions at zero (16.8.6). -/
@[dlmf 16.8.E6]
def genFrobeniusZero {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (i : Fin (q + 1)) (z : ℂ) : ℂ := by
  classical
  exact Fin.cases (generalizedHypergeometric (parametersOfFin a) (parametersOfFin b) z)
    (fun j => z ^ (1 - b j) *
      generalizedHypergeometric (shiftParameters (parametersOfFin a) (1 - b j))
        ((2 - b j) ::ₘ shiftParameters ((parametersOfFin b).erase (b j)) (1 - b j)) z) i

/-- A closed log(-z) sheet: the upper edge corresponds to the lower z-cut value. -/
def genHGNegativeLog (a b : Multiset ℂ) (w : ℂ) : ℂ := by
  classical
  exact if w.im = Real.pi then generalizedHypergeometricLower a b (-Complex.exp w)
    else generalizedHypergeometric a b (-Complex.exp w)

/-- The nonresonant infinity solutions with an explicit log(-z) sheet (16.8.7). -/
@[dlmf 16.8.E7]
def genFrobeniusInfinityLog {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (j : Fin (q + 1)) (w : ℂ) : ℂ := by
  classical
  exact Complex.exp (-a j * w) *
    genHGNegativeLog ((a j) ::ₘ shiftParameters (parametersOfFin b) (1 + a j))
      (shiftParameters ((parametersOfFin a).erase (a j)) (1 + a j)) (-w)

/-- Connection coefficient to the jth infinity solution. -/
def genInfinityConnectionCoeff {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (j : Fin (q + 1)) : ℂ :=
  (∏ k ∈ univ.erase j, Gamma (a k - a j)) * gammaProduct (parametersOfFin b) /
    ((∏ k ∈ univ.erase j, Gamma (a k)) * gammaProduct (shiftParameters (parametersOfFin b) (-a j)))

/-- Principal component for the displaced-center infinity expansion. -/
def genCenteredInfinityDomain (z₀ : ℂ) : Set ℂ :=
  let R := max ‖z₀‖ ‖z₀ - 1‖
  connectedComponentIn {z : ℂ | R < ‖z - z₀‖ ∧ z₀ - z ∈ Complex.slitPlane ∧ z ∈ cutPlane}
    (z₀ - (R + 1))

/-- The nth inner coefficient of the displaced-center expansion, regularized before
multiplication to preserve the shifted exceptional lower parameters. -/
def genCenteredInfinityTerm {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (z₀ z : ℂ) (j : Fin (q + 1)) (n : ℕ) : ℂ :=
  Gamma (a j + n) / n.factorial * (∏ k ∈ univ.erase j, Gamma (a k - a j - n)) *
    (∑ k ∈ range (n + 1),
      Complex.regularizedHGFunCoeff (shiftParameters (parametersOfFin a) (-a j - n))
        (shiftParameters (parametersOfFin b) (-a j - n)) k * z₀ ^ k) * (z - z₀) ^ (-(n : ℤ))

/-- Derivative of an iterated derivative of a smooth function. -/
private lemma hasDerivAt_iteratedDeriv_of_contDiff {f : ℂ → ℂ} (hf : ContDiff ℂ ⊤ f)
    (j : ℕ) (w : ℂ) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f w) w := by
  rw [iteratedDeriv_succ]
  exact ((hf.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)) w).hasDerivAt

/-- Powers of theta in ordinary derivatives: `θ^k f = Σ S(k,j) z^j f^(j)` (Stirling numbers of the
second kind). -/
private lemma eulerTheta_iterate_eq_sum_stirlingSecond {f : ℂ → ℂ} (hf : ContDiff ℂ ⊤ f) (k : ℕ) :
    ∀ M, k ≤ M → ∀ z, (eulerTheta^[k] f) z =
      ∑ j ∈ range (M + 1), (Nat.stirlingSecond k j : ℂ) * z ^ j * iteratedDeriv j f z := by
  induction k with
  | zero =>
    intro M _ z
    rw [sum_range_succ']
    rw [sum_eq_zero (fun j _ => by simp [Nat.stirlingSecond_zero_succ])]
    simp
  | succ k ih =>
    intro M hM z
    have hfun : eulerTheta^[k] f = fun w =>
        ∑ j ∈ range (M + 1), (Nat.stirlingSecond k j : ℂ) * w ^ j * iteratedDeriv j f w :=
      funext (ih M (by omega))
    rw [Function.iterate_succ_apply', hfun, eulerTheta]
    have hd : HasDerivAt (fun w => ∑ j ∈ range (M + 1),
        (Nat.stirlingSecond k j : ℂ) * w ^ j * iteratedDeriv j f w)
        (∑ j ∈ range (M + 1), (Nat.stirlingSecond k j : ℂ) *
          ((j : ℂ) * z ^ (j - 1) * iteratedDeriv j f z + z ^ j * iteratedDeriv (j + 1) f z)) z := by
      apply HasDerivAt.fun_sum
      intro j _
      have := ((hasDerivAt_pow j z).mul (hasDerivAt_iteratedDeriv_of_contDiff hf j z)).const_mul
        (Nat.stirlingSecond k j : ℂ)
      simpa [mul_assoc] using this
    rw [hd.deriv, mul_sum]
    have hsplit : ∀ j ∈ range (M + 1), z * ((Nat.stirlingSecond k j : ℂ) *
        ((j : ℂ) * z ^ (j - 1) * iteratedDeriv j f z + z ^ j * iteratedDeriv (j + 1) f z)) =
        (Nat.stirlingSecond k j : ℂ) * j * z ^ j * iteratedDeriv j f z +
          (Nat.stirlingSecond k j : ℂ) * z ^ (j + 1) * iteratedDeriv (j + 1) f z := by
      intro j _
      rcases j with _ | j
      · simp; ring
      · simp only [Nat.add_sub_cancel, pow_succ]; ring
    rw [sum_congr rfl hsplit, sum_add_distrib]
    rw [sum_range_succ' (fun j => (Nat.stirlingSecond k j : ℂ) * j * z ^ j * iteratedDeriv j f z),
      sum_range_succ (fun j => (Nat.stirlingSecond k j : ℂ) * z ^ (j + 1) *
        iteratedDeriv (j + 1) f z),
      sum_range_succ' (fun j => (Nat.stirlingSecond (k + 1) j : ℂ) * z ^ j * iteratedDeriv j f z)]
    rw [Nat.stirlingSecond_eq_zero_of_lt (show k < M by omega), Nat.stirlingSecond_succ_zero]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.stirlingSecond_succ_succ]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    push_cast
    ring

/-- A theta polynomial expanded in ordinary derivatives with `genThetaDCoeff`. -/
private lemma thetaPoly_eq_sum_iteratedDeriv {f : ℂ → ℂ} (hf : ContDiff ℂ ⊤ f) (P : ℂ[X]) {M : ℕ}
    (hM : P.natDegree ≤ M) (z : ℂ) :
    thetaPoly P f z = ∑ j ∈ range (M + 1), genThetaDCoeff P j * z ^ j * iteratedDeriv j f z := by
  unfold thetaPoly genThetaDCoeff
  rw [sum_congr rfl fun k hk => by
    rw [eulerTheta_iterate_eq_sum_stirlingSecond hf k M
      (by have := Finset.mem_range.mp hk; omega) z, mul_sum]]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [sum_mul, sum_mul]
  apply sum_congr rfl
  intro k _
  ring

/-- Iterated theta commutes with constant multiples. -/
private lemma eulerTheta_iterate_const_mul (c : ℂ) (F : ℂ → ℂ) (k : ℕ) :
    (eulerTheta^[k] fun z => c * F z) = fun z => c * (eulerTheta^[k] F) z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext z
    simp only [eulerTheta, deriv_const_mul_field]
    ring

/-- Theta polynomials commute with constant multiples. -/
private lemma thetaPoly_const_mul (c : ℂ) (F : ℂ → ℂ) (P : ℂ[X]) (z : ℂ) :
    thetaPoly P (fun z => c * F z) z = c * thetaPoly P F z := by
  unfold thetaPoly
  rw [mul_sum]
  apply sum_congr rfl
  intro k _
  rw [eulerTheta_iterate_const_mul]
  ring

/-- Degree of the upper theta polynomial. -/
private lemma genThetaA_natDegree (c : Multiset ℂ) : (genThetaA c).natDegree = c.card := by
  unfold genThetaA
  rw [Polynomial.natDegree_multiset_prod_of_monic]
  · simp only [Multiset.map_map, Function.comp_def, Polynomial.natDegree_X_add_C,
      Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
  · intro P hP
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hP
    exact Polynomial.monic_X_add_C x

/-- The upper theta polynomial is monic. -/
private lemma genThetaA_monic (c : Multiset ℂ) : (genThetaA c).Monic := by
  unfold genThetaA
  apply Polynomial.monic_multiset_prod_of_monic
  intro x _
  exact Polynomial.monic_X_add_C x

/-- The lower theta polynomial as an upper one with an added zero parameter. -/
private lemma genThetaB_eq_genThetaA (b : Multiset ℂ) :
    genThetaB b = genThetaA ((0 : ℂ) ::ₘ b.map (fun x => x - 1)) := by
  simp only [genThetaB, genThetaA, Multiset.map_cons, Multiset.prod_cons,
    Polynomial.C_0, add_zero, Multiset.map_map, Function.comp_def]

/-- The top derivative coefficient of a monic theta polynomial is one. -/
private lemma genThetaDCoeff_natDegree_of_monic (P : ℂ[X]) (hP : P.Monic) :
    genThetaDCoeff P P.natDegree = 1 := by
  unfold genThetaDCoeff
  rw [sum_range_succ, sum_eq_zero (fun k hk => by
    rw [Nat.stirlingSecond_eq_zero_of_lt (Finset.mem_range.mp hk)]; simp)]
  rw [Nat.stirlingSecond_self, hP.coeff_natDegree]; simp

/-- Derivative coefficients above the degree vanish. -/
private lemma genThetaDCoeff_eq_zero_of_natDegree_lt (P : ℂ[X]) {j : ℕ} (hj : P.natDegree < j) :
    genThetaDCoeff P j = 0 := by
  unfold genThetaDCoeff
  exact sum_eq_zero (fun k hk => by
    rw [Nat.stirlingSecond_eq_zero_of_lt (by have := Finset.mem_range.mp hk; omega)]; simp)

/-- The zeroth derivative coefficient of the lower theta polynomial vanishes. -/
private lemma genThetaDCoeff_genThetaB_zero (b : Multiset ℂ) : genThetaDCoeff
    (genThetaB b) 0 = 0 := by
  unfold genThetaDCoeff
  rw [sum_range_succ']
  rw [sum_eq_zero (fun k _ => by rw [Nat.stirlingSecond_succ_zero]; simp)]
  simp [genThetaB]

/-- For p≤q the principal function is the Gamma-normalized native series. -/
private lemma generalizedHypergeometric_eq_gammaProduct_mul_of_card_le {a b : Multiset ℂ}
    (h : a.card ≤ b.card) :
    generalizedHypergeometric a b = fun z => gammaProduct b * Complex.regularizedHGFun a b z := by
  have hne : a.card ≠ b.card + 1 := by omega
  funext z
  unfold generalizedHypergeometric regularizedGeneralizedHypergeometric
  simp only [ite_eq_right hne]

/-- For p≤q the theta equation holds at every complex point. -/
private lemma genODESolution_generalizedHypergeometric_of_card_le {a b : Multiset ℂ}
    (h : a.card ≤ b.card) (z : ℂ) :
    GenODESolution a b (generalizedHypergeometric a b) z := by
  unfold GenODESolution
  rw [generalizedHypergeometric_eq_gammaProduct_mul_of_card_le h, thetaPoly_const_mul,
      thetaPoly_const_mul]
  have := regularizedHGFun_ode_of_card_le h z
  simp only [genThetaA, genThetaB]
  rw [this]; ring

/-- Iterated theta depends only on the germ. -/
private lemma eulerTheta_iterate_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) (k : ℕ) :
    eulerTheta^[k] f =ᶠ[𝓝 z] eulerTheta^[k] g := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    filter_upwards [ih.deriv] with w hw
    simp only [eulerTheta, hw]

/-- Theta polynomials depend only on the germ. -/
private lemma thetaPoly_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) (P : ℂ[X]) :
    thetaPoly P f z = thetaPoly P g z := by
  unfold thetaPoly
  exact sum_congr rfl fun k _ => by rw [(eulerTheta_iterate_congr h k).eq_of_nhds]

/-- Iterated theta preserves analyticity on an open set. -/
private lemma analyticOnNhd_eulerTheta_iterate {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (k : ℕ) : AnalyticOnNhd ℂ (eulerTheta^[k] f) U := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact analyticOnNhd_id.mul ih.deriv

/-- Theta polynomials preserve analyticity on an open set. -/
private lemma analyticOnNhd_thetaPoly {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (P : ℂ[X]) : AnalyticOnNhd ℂ (thetaPoly P f) U := by
  have : thetaPoly P f = fun z => ∑ k ∈ range (P.natDegree + 1),
      P.coeff k * (eulerTheta^[k] f) z := rfl
  rw [this]
  exact Finset.analyticOnNhd_fun_sum _ fun k _ =>
    analyticOnNhd_const.mul (analyticOnNhd_eulerTheta_iterate hf k)

/-- The theta equation for the regularized principal function on its analytic domain. -/
private lemma regularizedGeneralizedHypergeometric_theta_ode (a b : Multiset ℂ)
    (h : a.card ≤ b.card + 1 ∨ IsTerminating a) {z : ℂ} (hz : z ∈ genAnalyticDomain a b) :
    thetaPoly (genThetaB b) (regularizedGeneralizedHypergeometric a b) z =
      z * thetaPoly (genThetaA a) (regularizedGeneralizedHypergeometric a b) z := by
  by_cases hT : IsTerminating a
  · have heq : regularizedGeneralizedHypergeometric a b = Complex.regularizedHGFun a b :=
      funext (regularizedGeneralizedHypergeometric_eq_series_of_terminates hT)
    rw [heq]
    obtain ⟨x, hx, m, hxm⟩ := hT
    have hr := Complex.radius_regularizedHGFunSeries_eq_top_of_finite (b := b) hx hxm
    exact regularizedHGFun_ode a b (by rw [hr]; simp) (by rw [hr]; simp)
  · by_cases hc : a.card ≤ b.card
    · have hne : a.card ≠ b.card + 1 := by omega
      have heq : regularizedGeneralizedHypergeometric a b = Complex.regularizedHGFun a b := by
        funext w
        unfold regularizedGeneralizedHypergeometric
        simp only [ite_eq_right hne]
      rw [heq]
      exact regularizedHGFun_ode_of_card_le hc z
    · have hc' : a.card = b.card + 1 := by
        rcases h with h | h
        · omega
        · exact absurd h hT
      have hzc : z ∈ cutPlane := by
        unfold genAnalyticDomain at hz
        rwa [ite_eq_right (by tauto)] at hz
      have hA := analyticOnNhd_regularizedGeneralizedHypergeometric hc'
      refine eqOn_cutPlane_of_eqOn_disk
          (f := thetaPoly (genThetaB b) (regularizedGeneralizedHypergeometric a b))
        (g := fun z => z * thetaPoly (genThetaA a) (regularizedGeneralizedHypergeometric a b) z)
        (analyticOnNhd_thetaPoly hA _) (analyticOnNhd_id.mul (analyticOnNhd_thetaPoly hA _))
        (fun w hw => ?_) hzc
      have hev : regularizedGeneralizedHypergeometric a b =ᶠ[𝓝 w] Complex.regularizedHGFun a b := by
        filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw)] with v hv
        exact regularizedGeneralizedHypergeometric_eq_series (by simpa using hv)
      rw [thetaPoly_congr hev, thetaPoly_congr hev]
      exact regularizedHGFun_ode_of_card_eq_add_one hc' hw

/-- The theta equation on the principal analytic domain, without the regularity hypothesis on
the lower parameters; stronger than DLMF, which assumes regular lower parameters. -/
@[dlmf 16.8.E3]
theorem generalizedHypergeometric_theta_ode' (a b : Multiset ℂ)
    (h : a.card ≤ b.card + 1 ∨ IsTerminating a) {z : ℂ} (hz : z ∈ genAnalyticDomain a b) :
    GenODESolution a b (generalizedHypergeometric a b) z := by
  unfold GenODESolution
  have hgen : generalizedHypergeometric a b = fun z => gammaProduct b *
      regularizedGeneralizedHypergeometric a b z := rfl
  rw [hgen, thetaPoly_const_mul, thetaPoly_const_mul,
      regularizedGeneralizedHypergeometric_theta_ode a b h hz]
  ring

/-- The proved theta equation continued throughout the ordinary principal analytic domain. -/
@[dlmf 16.8.E3]
theorem generalizedHypergeometric_theta_ode (a b : Multiset ℂ) (_hb : LowerParametersRegular b)
    (h : a.card ≤ b.card + 1 ∨ IsTerminating a) {z : ℂ} (hz : z ∈ genAnalyticDomain a b) :
    GenODESolution a b (generalizedHypergeometric a b) z :=
  generalizedHypergeometric_theta_ode' a b h hz

/-- The full expanded equation for p≤q with the explicit alpha and beta constants. -/
@[dlmf 16.8.E4]
theorem generalizedHypergeometric_expanded_ode_entire (a b : Multiset ℂ)
    (h : a.card ≤ b.card) (z : ℂ) :
    z ^ b.card * iteratedDeriv (b.card + 1) (generalizedHypergeometric a b) z +
      (∑ j ∈ Finset.Icc 1 b.card, z ^ (j - 1) *
        (genODEAlpha a j * z + genODEBeta b j) *
            iteratedDeriv j (generalizedHypergeometric a b) z) +
      genODEAlpha a 0 * generalizedHypergeometric a b z = 0 := by
  set f := generalizedHypergeometric a b with hfdef
  set q := b.card
  have hf : ContDiff ℂ ⊤ f := (generalizedHypergeometric_entire h).contDiff
  have hc : ∀ j, Continuous (iteratedDeriv j f) := fun j => hf.continuous_iteratedDeriv j
    le_top
  have hBdeg : (genThetaB b).natDegree = q + 1 := by
    rw [genThetaB_eq_genThetaA, genThetaA_natDegree]; simp [q]
  have hAdeg : (genThetaA a).natDegree = a.card := genThetaA_natDegree a
  have hβtop : genODEBeta b (q + 1) = 1 := by
    rw [genODEBeta, ← hBdeg]
    exact genThetaDCoeff_natDegree_of_monic _
        (by rw [genThetaB_eq_genThetaA]; exact genThetaA_monic _)
  have hαtop : genODEAlpha a (q + 1) = 0 := by
    rw [genODEAlpha, genThetaDCoeff_eq_zero_of_natDegree_lt _ (by rw [hAdeg]; omega), neg_zero]
  have hβ0 : genODEBeta b 0 = 0 := genThetaDCoeff_genThetaB_zero b
  set T : ℂ → ℂ := fun z => z ^ q * iteratedDeriv (q + 1) f z +
      (∑ j ∈ Finset.Icc 1 q, z ^ (j - 1) *
        (genODEAlpha a j * z + genODEBeta b j) * iteratedDeriv j f z) +
      genODEAlpha a 0 * f z with hT
  have hzT : ∀ z, z * T z = 0 := by
    intro z
    have hode := genODESolution_generalizedHypergeometric_of_card_le h z
    unfold GenODESolution at hode
    rw [thetaPoly_eq_sum_iteratedDeriv hf _ (M := q + 1) hBdeg.le,
      thetaPoly_eq_sum_iteratedDeriv hf _ (M := q + 1) (by rw [hAdeg]; omega)] at hode
    have hE : ∑ j ∈ range (q + 1 + 1), (genODEBeta b j * z ^ j + genODEAlpha a j * z ^ (j + 1)) *
        iteratedDeriv j f z = 0 := by
      simp only [genODEBeta, genODEAlpha]
      rw [← sub_eq_zero] at hode
      rw [← hode, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      ring
    rw [← hE, sum_range_succ, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega),
      Finset.Ico_add_one_right_eq_Icc]
    simp only [hT, hβtop, hαtop, hβ0, pow_zero]
    rw [mul_add, mul_add, mul_sum]
    have hmid : ∀ j ∈ Finset.Icc 1 q, z * (z ^ (j - 1) * (genODEAlpha a j * z + genODEBeta b j) *
        iteratedDeriv j f z) = (genODEBeta b j * z ^ j + genODEAlpha a j * z ^ (j + 1)) *
          iteratedDeriv j f z := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]; ring
    rw [sum_congr rfl hmid, iteratedDeriv_zero, zero_add]
    ring
  by_cases hz : z = 0
  · have hTc : Continuous T := by
      simp only [hT]
      have := hc
      fun_prop
    have hlim : Tendsto T (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact ((mul_eq_zero.mp (hzT w)).resolve_left hw).symm
    have h0 := tendsto_nhds_unique ((hTc.tendsto 0).mono_left nhdsWithin_le_nhds) hlim
    rw [hz]; exact h0
  · exact (mul_eq_zero.mp (hzT z)).resolve_left hz

/-- Derivative of an iterated derivative of a function analytic on an open set. -/
private lemma hasDerivAt_iteratedDeriv_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (j : ℕ) {w : ℂ} (hw : w ∈ U) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f w) w := by
  rw [iteratedDeriv_succ, iteratedDeriv_eq_iterate]
  exact ((hf.iterated_deriv j) w hw).differentiableAt.hasDerivAt

/-- The local form of `eulerTheta_iterate_eq_sum_stirlingSecond` on an open set. -/
private lemma eulerTheta_iterate_eq_sum_stirlingSecond_on {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (k : ℕ) :
    ∀ M, k ≤ M → ∀ z ∈ U, (eulerTheta^[k] f) z =
      ∑ j ∈ range (M + 1), (Nat.stirlingSecond k j : ℂ) * z ^ j * iteratedDeriv j f z := by
  induction k with
  | zero =>
    intro M _ z _
    rw [sum_range_succ']
    rw [sum_eq_zero (fun j _ => by simp [Nat.stirlingSecond_zero_succ])]
    simp
  | succ k ih =>
    intro M hM z hz
    have hev : eulerTheta^[k] f =ᶠ[𝓝 z] fun w =>
        ∑ j ∈ range (M + 1), (Nat.stirlingSecond k j : ℂ) * w ^ j * iteratedDeriv j f w := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact ih M (by omega) w hw
    rw [Function.iterate_succ_apply', eulerTheta, hev.deriv_eq]
    have hd : HasDerivAt (fun w => ∑ j ∈ range (M + 1),
        (Nat.stirlingSecond k j : ℂ) * w ^ j * iteratedDeriv j f w)
        (∑ j ∈ range (M + 1), (Nat.stirlingSecond k j : ℂ) *
          ((j : ℂ) * z ^ (j - 1) * iteratedDeriv j f z + z ^ j * iteratedDeriv (j + 1) f z)) z := by
      apply HasDerivAt.fun_sum
      intro j _
      have := ((hasDerivAt_pow j z).mul
        (hasDerivAt_iteratedDeriv_of_analyticOnNhd hf j hz)).const_mul
        (Nat.stirlingSecond k j : ℂ)
      simpa [mul_assoc] using this
    rw [hd.deriv, mul_sum]
    have hsplit : ∀ j ∈ range (M + 1), z * ((Nat.stirlingSecond k j : ℂ) *
        ((j : ℂ) * z ^ (j - 1) * iteratedDeriv j f z + z ^ j * iteratedDeriv (j + 1) f z)) =
        (Nat.stirlingSecond k j : ℂ) * j * z ^ j * iteratedDeriv j f z +
          (Nat.stirlingSecond k j : ℂ) * z ^ (j + 1) * iteratedDeriv (j + 1) f z := by
      intro j _
      rcases j with _ | j
      · simp; ring
      · simp only [Nat.add_sub_cancel, pow_succ]; ring
    rw [sum_congr rfl hsplit, sum_add_distrib]
    rw [sum_range_succ' (fun j => (Nat.stirlingSecond k j : ℂ) * j * z ^ j * iteratedDeriv j f z),
      sum_range_succ (fun j => (Nat.stirlingSecond k j : ℂ) * z ^ (j + 1) *
        iteratedDeriv (j + 1) f z),
      sum_range_succ' (fun j => (Nat.stirlingSecond (k + 1) j : ℂ) * z ^ j * iteratedDeriv j f z)]
    rw [Nat.stirlingSecond_eq_zero_of_lt (show k < M by omega), Nat.stirlingSecond_succ_zero]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.stirlingSecond_succ_succ]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    push_cast
    ring

/-- The local form of `thetaPoly_eq_sum_iteratedDeriv` on an open set. -/
private lemma thetaPoly_eq_sum_iteratedDeriv_on {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (P : ℂ[X]) {M : ℕ} (hM : P.natDegree ≤ M) {z : ℂ} (hz : z ∈ U) :
    thetaPoly P f z = ∑ j ∈ range (M + 1), genThetaDCoeff P j * z ^ j * iteratedDeriv j f z := by
  unfold thetaPoly genThetaDCoeff
  rw [sum_congr rfl fun k hk => by
    rw [eulerTheta_iterate_eq_sum_stirlingSecond_on hU hf k M
      (by have := Finset.mem_range.mp hk; omega) z hz, mul_sum]]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [sum_mul, sum_mul]
  apply sum_congr rfl
  intro k _
  ring

/-- The full expanded equation for p=q+1, without the regularity hypothesis on the lower
parameters; stronger than DLMF, which assumes regular lower parameters. -/
@[dlmf 16.8.E5]
theorem generalizedHypergeometric_expanded_ode_balanced' (a b : Multiset ℂ)
    (h : a.card = b.card + 1)
    {z : ℂ} (hz : z ∈ cutPlane) :
    z ^ b.card * (1 - z) * iteratedDeriv (b.card + 1) (generalizedHypergeometric a b) z +
      (∑ j ∈ Finset.Icc 1 b.card, z ^ (j - 1) *
        (genODEAlpha a j * z + genODEBeta b j) *
            iteratedDeriv j (generalizedHypergeometric a b) z) +
      genODEAlpha a 0 * generalizedHypergeometric a b z = 0 := by
  set f := generalizedHypergeometric a b with hfdef
  set q := b.card
  have hf : AnalyticOnNhd ℂ f cutPlane :=
    analyticOnNhd_const.mul (analyticOnNhd_regularizedGeneralizedHypergeometric h)
  have hdom : cutPlane ⊆ genAnalyticDomain a b := by
    intro w hw
    unfold genAnalyticDomain
    split_ifs
    · exact mem_univ w
    · exact hw
  have hBdeg : (genThetaB b).natDegree = q + 1 := by
    rw [genThetaB_eq_genThetaA, genThetaA_natDegree]; simp [q]
  have hAdeg : (genThetaA a).natDegree = q + 1 := by rw [genThetaA_natDegree, h]
  have hβtop : genODEBeta b (q + 1) = 1 := by
    rw [genODEBeta, ← hBdeg]
    exact genThetaDCoeff_natDegree_of_monic _
        (by rw [genThetaB_eq_genThetaA]; exact genThetaA_monic _)
  have hαtop : genODEAlpha a (q + 1) = -1 := by
    rw [genODEAlpha, ← hAdeg, genThetaDCoeff_natDegree_of_monic _ (genThetaA_monic a)]
  have hβ0 : genODEBeta b 0 = 0 := genThetaDCoeff_genThetaB_zero b
  set T : ℂ → ℂ := fun z => z ^ q * (1 - z) * iteratedDeriv (q + 1) f z +
      (∑ j ∈ Finset.Icc 1 q, z ^ (j - 1) *
        (genODEAlpha a j * z + genODEBeta b j) * iteratedDeriv j f z) +
      genODEAlpha a 0 * f z with hT
  have hzT : ∀ z ∈ cutPlane, z * T z = 0 := by
    intro z hz
    have hode := generalizedHypergeometric_theta_ode' a b (Or.inl h.le) (hdom hz)
    unfold GenODESolution at hode
    rw [thetaPoly_eq_sum_iteratedDeriv_on isOpen_cutPlane hf _ (M := q + 1) hBdeg.le hz,
      thetaPoly_eq_sum_iteratedDeriv_on isOpen_cutPlane hf _ (M := q + 1) hAdeg.le hz] at hode
    have hE : ∑ j ∈ range (q + 1 + 1), (genODEBeta b j * z ^ j + genODEAlpha a j * z ^ (j + 1)) *
        iteratedDeriv j f z = 0 := by
      simp only [genODEBeta, genODEAlpha]
      rw [← sub_eq_zero] at hode
      rw [← hode, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      ring
    rw [← hE, sum_range_succ, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega),
      Finset.Ico_add_one_right_eq_Icc]
    simp only [hT, hβtop, hαtop, hβ0, pow_zero]
    rw [mul_add, mul_add, mul_sum]
    have hmid : ∀ j ∈ Finset.Icc 1 q, z * (z ^ (j - 1) * (genODEAlpha a j * z + genODEBeta b j) *
        iteratedDeriv j f z) = (genODEBeta b j * z ^ j + genODEAlpha a j * z ^ (j + 1)) *
          iteratedDeriv j f z := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]; ring
    rw [sum_congr rfl hmid, iteratedDeriv_zero, zero_add]
    ring
  by_cases hz0 : z = 0
  · have hTc : ContinuousAt T 0 := by
      have hc : ∀ j, ContinuousAt (iteratedDeriv j f) 0 := fun j => by
        rw [iteratedDeriv_eq_iterate]
        exact ((hf.iterated_deriv j) 0 zero_mem_cutPlane).continuousAt
      simp only [hT]
      have h1 := hc (q + 1)
      have h2 : ContinuousAt f 0 := (hf 0 zero_mem_cutPlane).continuousAt
      refine ((((continuousAt_id.pow q).mul (continuousAt_const.sub continuousAt_id)).mul
        h1).add ?_).add (continuousAt_const.mul h2)
      exact tendsto_finsetSum _ fun j _ =>
        ((continuousAt_id.pow _).mul ((continuousAt_const.mul continuousAt_id).add
          continuousAt_const)).mul (hc j)
    have hlim : Tendsto T (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_cutPlane.mem_nhds zero_mem_cutPlane)] with w hw hwc
      exact ((mul_eq_zero.mp (hzT w hwc)).resolve_left hw).symm
    have h0 := tendsto_nhds_unique (hTc.tendsto.mono_left nhdsWithin_le_nhds) hlim
    rw [hz0]; exact h0
  · exact (mul_eq_zero.mp (hzT z hz)).resolve_left hz0

/-- The full expanded equation for p=q+1. -/
@[dlmf 16.8.E5]
theorem generalizedHypergeometric_expanded_ode_balanced (a b : Multiset ℂ) (h : a.card = b.card + 1)
    (_hb : LowerParametersRegular b)
    {z : ℂ} (hz : z ∈ cutPlane) :
    z ^ b.card * (1 - z) * iteratedDeriv (b.card + 1) (generalizedHypergeometric a b) z +
      (∑ j ∈ Finset.Icc 1 b.card, z ^ (j - 1) *
        (genODEAlpha a j * z + genODEBeta b j) *
            iteratedDeriv j (generalizedHypergeometric a b) z) +
      genODEAlpha a 0 * generalizedHypergeometric a b z = 0 :=
  generalizedHypergeometric_expanded_ode_balanced' a b h hz

/-! ### Singularities of the expanded equation -/

/-- The common denominator of the normalized coefficients `genODECoeff`. -/
private def genODEDen (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  genThetaDCoeff (genThetaB b) (genODEOrder a b) * z ^ genODEOrder a b -
    genThetaDCoeff (genThetaA a) (genODEOrder a b) * z ^ (genODEOrder a b + 1)

/-- The finite difference `∑ₘ (j choose m) (-1)^(j-m) P(-m)` of a theta polynomial. -/
private def genThetaFinDiff (P : ℂ[X]) (j : ℕ) : ℂ :=
  ∑ m ∈ range (j + 1), (j.choose m : ℂ) * (-1) ^ (j - m) * P.eval (-(m : ℂ))

/-- The normalized operator as one quotient by the common denominator. -/
private lemma linearODEValue_genODECoeff (a b : Multiset ℂ) (f : ℂ → ℂ) {z : ℂ}
    (hz : genODEDen a b z ≠ 0) :
    Complex.linearODEValue (genODECoeff a b) f z =
      (∑ i ∈ range (genODEOrder a b + 1),
        (genThetaDCoeff (genThetaB b) i * z ^ i - genThetaDCoeff (genThetaA a) i * z ^ (i + 1)) *
          iteratedDeriv i f z) / genODEDen a b z := by
  rw [eq_div_iff hz, Complex.linearODEValue, sum_range_succ, add_mul, sum_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun i => (genThetaDCoeff (genThetaB b) i * z ^ i -
    genThetaDCoeff (genThetaA a) i * z ^ (i + 1)) * iteratedDeriv i f z)]
  have : ∀ j : Fin (genODEOrder a b), genODECoeff a b j z * iteratedDeriv j f z *
      genODEDen a b z = (genThetaDCoeff (genThetaB b) j * z ^ (j : ℕ) -
        genThetaDCoeff (genThetaA a) j * z ^ ((j : ℕ) + 1)) * iteratedDeriv j f z := by
    intro j
    simp only [genODECoeff]
    rw [show genThetaDCoeff (genThetaB b) (genODEOrder a b) * z ^ genODEOrder a b -
      genThetaDCoeff (genThetaA a) (genODEOrder a b) * z ^ (genODEOrder a b + 1) =
        genODEDen a b z from rfl]
    field_simp
  rw [sum_congr rfl fun j _ => this j]
  simp only [genODEDen]
  ring

/-- The theta polynomials have degree at most the nominal order. -/
private lemma genThetaB_natDegree_le (a b : Multiset ℂ) :
    (genThetaB b).natDegree ≤ genODEOrder a b := by
  rw [genThetaB_eq_genThetaA, genThetaA_natDegree]
  simp [genODEOrder]

/-- The upper theta polynomial has degree at most the nominal order. -/
private lemma genThetaA_natDegree_le (a b : Multiset ℂ) :
    (genThetaA a).natDegree ≤ genODEOrder a b := by
  rw [genThetaA_natDegree]
  simp [genODEOrder]

/-- The Euler operator acts diagonally on finite sums of negative powers. -/
private lemma eulerTheta_sum_zpow (w : ℕ → ℂ) (N : ℕ) :
    eulerTheta (fun z => ∑ m ∈ range N, w m * z ^ (-(m : ℤ))) =
      fun z => ∑ m ∈ range N, (w m * (-(m : ℂ))) * z ^ (-(m : ℤ)) := by
  funext z
  unfold eulerTheta
  by_cases hz : z = 0
  · subst hz
    rw [zero_mul]
    refine (sum_eq_zero fun m _ => ?_).symm
    rcases m with _ | m
    · simp
    · rw [zero_zpow _ (by omega)]; ring
  · rw [deriv_fun_sum fun m _ => ((differentiableAt_zpow).mpr (Or.inl hz)).const_mul _,
      mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [deriv_const_mul _ ((differentiableAt_zpow).mpr (Or.inl hz)), deriv_zpow]
    have : z * z ^ (-(m : ℤ) - 1) = z ^ (-(m : ℤ)) := by
      rw [zpow_sub_one₀ hz]; field_simp
    push_cast
    linear_combination (w m * (-(m : ℂ))) * this

/-- Iterates of the Euler operator on finite sums of negative powers. -/
private lemma eulerTheta_iterate_sum_zpow (w : ℕ → ℂ) (N k : ℕ) :
    eulerTheta^[k] (fun z => ∑ m ∈ range N, w m * z ^ (-(m : ℤ))) =
      fun z => ∑ m ∈ range N, (w m * (-(m : ℂ)) ^ k) * z ^ (-(m : ℤ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, eulerTheta_sum_zpow]
    funext z
    refine sum_congr rfl fun m _ => ?_
    ring

/-- Theta polynomials on finite sums of negative powers. -/
private lemma thetaPoly_sum_zpow (P : ℂ[X]) (w : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    thetaPoly P (fun z => ∑ m ∈ range N, w m * z ^ (-(m : ℤ))) z =
      ∑ m ∈ range N, w m * P.eval (-(m : ℂ)) * z ^ (-(m : ℤ)) := by
  unfold thetaPoly
  simp only [eulerTheta_iterate_sum_zpow, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [P.eval_eq_sum_range, mul_sum, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  ring

/-- The normalized monomials of the reciprocal change of variable as sums of negative powers. -/
private lemma inv_sub_pow_div_eq_sum (u : ℂ) (j : ℕ) :
    (fun z : ℂ => (z⁻¹ - u) ^ j / j.factorial) = fun z =>
      ∑ m ∈ range (j + 1), ((j.choose m : ℂ) * (-u) ^ (j - m) / j.factorial) *
        z ^ (-(m : ℤ)) := by
  funext z
  rw [sub_eq_add_neg, add_pow, sum_div]
  refine sum_congr rfl fun m _ => ?_
  rw [zpow_neg, zpow_natCast, inv_pow]
  ring

/-- The unnormalized reciprocal coefficients of the generalized hypergeometric equation. -/
private lemma linearODEReciprocalRaw_genODECoeff (a b : Multiset ℂ) (j : ℕ) {u : ℂ}
    (hu : u ≠ 0) (hd : genODEDen a b u⁻¹ ≠ 0) :
    Complex.linearODEReciprocalRaw (genODECoeff a b) j u =
      u ^ j / j.factorial * (genThetaFinDiff (genThetaB b) j -
        u⁻¹ * genThetaFinDiff (genThetaA a) j) / genODEDen a b u⁻¹ := by
  have hU : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hz : u⁻¹ ∈ ({0}ᶜ : Set ℂ) := inv_ne_zero hu
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => (z⁻¹ - u) ^ j / j.factorial) {0}ᶜ := fun z hz =>
    (((analyticAt_inv hz).sub analyticAt_const).pow j).div_const
  unfold Complex.linearODEReciprocalRaw
  rw [linearODEValue_genODECoeff a b _ hd]
  congr 1
  have hsum : ∀ P : ℂ[X], P.natDegree ≤ genODEOrder a b → thetaPoly P
      (fun z : ℂ => (z⁻¹ - u) ^ j / j.factorial) u⁻¹ = ∑ i ∈ range (genODEOrder a b + 1),
        genThetaDCoeff P i * u⁻¹ ^ i *
          iteratedDeriv i (fun z : ℂ => (z⁻¹ - u) ^ j / j.factorial) u⁻¹ :=
    fun P hP => thetaPoly_eq_sum_iteratedDeriv_on hU hg P hP hz
  have hB := hsum _ (genThetaB_natDegree_le a b)
  have hA := hsum _ (genThetaA_natDegree_le a b)
  rw [inv_sub_pow_div_eq_sum, thetaPoly_sum_zpow] at hB hA
  rw [← inv_sub_pow_div_eq_sum] at hB hA
  have hsplit : ∑ i ∈ range (genODEOrder a b + 1),
      (genThetaDCoeff (genThetaB b) i * u⁻¹ ^ i - genThetaDCoeff (genThetaA a) i *
        u⁻¹ ^ (i + 1)) * iteratedDeriv i (fun z : ℂ => (z⁻¹ - u) ^ j / j.factorial) u⁻¹ =
      (∑ i ∈ range (genODEOrder a b + 1), genThetaDCoeff (genThetaB b) i * u⁻¹ ^ i *
        iteratedDeriv i (fun z : ℂ => (z⁻¹ - u) ^ j / j.factorial) u⁻¹) -
      u⁻¹ * ∑ i ∈ range (genODEOrder a b + 1), genThetaDCoeff (genThetaA a) i * u⁻¹ ^ i *
        iteratedDeriv i (fun z : ℂ => (z⁻¹ - u) ^ j / j.factorial) u⁻¹ := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, ← hB, ← hA]
  unfold genThetaFinDiff
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmj : m ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hp : (-u) ^ (j - m) * u⁻¹ ^ (-(m : ℤ)) = (-1) ^ (j - m) * u ^ j := by
    rw [inv_zpow', neg_neg, zpow_natCast, neg_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hmj]
  linear_combination ((j.choose m : ℂ) / j.factorial *
    ((genThetaB b).eval (-(m : ℂ)) - u⁻¹ * (genThetaA a).eval (-(m : ℂ)))) * hp

/-- Finite differences vanish above the degree. -/
private lemma genThetaFinDiff_eq_zero_of_natDegree_lt (P : ℂ[X]) {j : ℕ}
    (hj : P.natDegree < j) : genThetaFinDiff P j = 0 := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    (P := P.comp (-X)) (n := j) (by simpa [natDegree_comp] using hj)) 0
  rw [Pi.zero_apply, fwdDiff_iter_eq_sum_shift] at h
  rw [← h]
  unfold genThetaFinDiff
  refine sum_congr rfl fun m _ => ?_
  simp [zsmul_eq_mul, mul_comm]

/-- The top finite difference of a monic polynomial. -/
private lemma genThetaFinDiff_natDegree_of_monic (P : ℂ[X]) (hP : P.Monic) :
    genThetaFinDiff P P.natDegree = (-1) ^ P.natDegree * P.natDegree.factorial := by
  have h := congrFun (Polynomial.fwdDiff_iter_degree_eq_factorial (P.comp (-X))) 0
  have hd : (P.comp (-X)).natDegree = P.natDegree := by simp [natDegree_comp]
  have hl : (P.comp (-X)).leadingCoeff = (-1) ^ P.natDegree := by
    rw [leadingCoeff_comp (by simp), hP.leadingCoeff]; simp
  rw [hd, hl, fwdDiff_iter_eq_sum_shift] at h
  unfold genThetaFinDiff
  rw [show ∑ m ∈ range (P.natDegree + 1), (P.natDegree.choose m : ℂ) * (-1) ^ (P.natDegree - m) *
      P.eval (-(m : ℂ)) = ∑ k ∈ range (P.natDegree + 1),
        ((-1 : ℤ) ^ (P.natDegree - k) * P.natDegree.choose k) • (P.comp (-X)).eval (0 + k • 1) from
    sum_congr rfl fun m _ => by simp [zsmul_eq_mul, mul_comm], h]
  simp

/-- Top coefficients of the theta polynomials and the denominator for `p ≤ q`. -/
private lemma genODEDen_of_card_le {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    genODEOrder a b = b.card + 1 ∧ genODEDen a b z = z ^ genODEOrder a b ∧
      genThetaFinDiff (genThetaB b) (genODEOrder a b) =
        (-1) ^ genODEOrder a b * (genODEOrder a b).factorial ∧
      genThetaFinDiff (genThetaA a) (genODEOrder a b) = 0 := by
  have hn : genODEOrder a b = b.card + 1 := by simp [genODEOrder]; omega
  have hBdeg : (genThetaB b).natDegree = genODEOrder a b := by
    rw [genThetaB_eq_genThetaA, genThetaA_natDegree, hn]; simp
  have hBm : (genThetaB b).Monic := by rw [genThetaB_eq_genThetaA]; exact genThetaA_monic _
  have hAdeg : (genThetaA a).natDegree < genODEOrder a b := by
    rw [genThetaA_natDegree, hn]; omega
  refine ⟨hn, ?_, ?_, genThetaFinDiff_eq_zero_of_natDegree_lt _ hAdeg⟩
  · simp only [genODEDen]
    rw [← hBdeg, genThetaDCoeff_natDegree_of_monic _ hBm, hBdeg,
      genThetaDCoeff_eq_zero_of_natDegree_lt _ hAdeg]
    ring
  · rw [← hBdeg, genThetaFinDiff_natDegree_of_monic _ hBm]

/-- Top coefficients of the theta polynomials and the denominator for `p = q + 1`. -/
private lemma genODEDen_of_card_eq {a b : Multiset ℂ} (h : a.card = b.card + 1) (z : ℂ) :
    genODEOrder a b = b.card + 1 ∧
      genODEDen a b z = z ^ genODEOrder a b * (1 - z) ∧
      genThetaFinDiff (genThetaB b) (genODEOrder a b) =
        (-1) ^ genODEOrder a b * (genODEOrder a b).factorial ∧
      genThetaFinDiff (genThetaA a) (genODEOrder a b) =
        (-1) ^ genODEOrder a b * (genODEOrder a b).factorial := by
  have hn : genODEOrder a b = b.card + 1 := by simp [genODEOrder, h]
  have hBdeg : (genThetaB b).natDegree = genODEOrder a b := by
    rw [genThetaB_eq_genThetaA, genThetaA_natDegree, hn]; simp
  have hBm : (genThetaB b).Monic := by rw [genThetaB_eq_genThetaA]; exact genThetaA_monic _
  have hAdeg : (genThetaA a).natDegree = genODEOrder a b := by
    rw [genThetaA_natDegree, hn, h]
  refine ⟨hn, ?_, ?_, ?_⟩
  · simp only [genODEDen]
    rw [← hBdeg, genThetaDCoeff_natDegree_of_monic _ hBm, hBdeg, ← hAdeg,
      genThetaDCoeff_natDegree_of_monic _ (genThetaA_monic a), hAdeg]
    ring
  · rw [← hBdeg, genThetaFinDiff_natDegree_of_monic _ hBm]
  · rw [← hAdeg, genThetaFinDiff_natDegree_of_monic _ (genThetaA_monic a)]

/-- Ordinary behavior where the common denominator does not vanish. -/
private lemma linearODEOrdinaryAt_genODECoeff {a b : Multiset ℂ} {z₀ : ℂ}
    (hz : genODEDen a b z₀ ≠ 0) : Complex.LinearODEOrdinaryAt (genODECoeff a b) z₀ := by
  intro j
  refine ⟨genODECoeff a b j, ?_, Filter.EventuallyEq.rfl⟩
  have hd : AnalyticAt ℂ (genODEDen a b) z₀ := by unfold genODEDen; fun_prop
  exact AnalyticAt.div (by fun_prop) hd hz

/-- At most regular behavior is implied by ordinary behavior. -/
private lemma linearODEAtMostRegularAt_of_ordinaryAt {n : ℕ} {c : Fin n → ℂ → ℂ} {z₀ : ℂ}
    (h : Complex.LinearODEOrdinaryAt c z₀) : Complex.LinearODEAtMostRegularAt c z₀ := by
  intro j
  obtain ⟨g, hg, hev⟩ := h j
  refine ⟨fun z => (z - z₀) ^ (n - j.val) * g z, by fun_prop, ?_⟩
  filter_upwards [hev] with z hz
  rw [hz]

/-- The classification for `p ≤ q`, without the regularity hypothesis on the lower parameters. -/
theorem generalizedHypergeometric_ode_singularities_entire' (a b : Multiset ℂ)
    (h : a.card ≤ b.card) :
    Complex.LinearODEAtMostRegularAt (genODECoeff a b) 0 ∧
    Complex.LinearODEIrregularAtInfinity (genODECoeff a b) ∧
    ∀ z : ℂ, z ≠ 0 → Complex.LinearODEOrdinaryAt (genODECoeff a b) z := by
  have hD := genODEDen_of_card_le h
  set n := genODEOrder a b with hndef
  refine ⟨fun j => ?_, ?_, fun z hz => linearODEOrdinaryAt_genODECoeff (by
    rw [(hD z).2.1]; exact pow_ne_zero _ hz)⟩
  · refine ⟨fun z => genThetaDCoeff (genThetaB b) j - genThetaDCoeff (genThetaA a) j * z,
      by fun_prop, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := hz
    simp only [genODECoeff]
    rw [show genThetaDCoeff (genThetaB b) (genODEOrder a b) * z ^ genODEOrder a b -
      genThetaDCoeff (genThetaA a) (genODEOrder a b) * z ^ (genODEOrder a b + 1) =
        genODEDen a b z from rfl, (hD z).2.1, sub_zero,
      show z ^ genODEOrder a b = z ^ (n - j.val) * z ^ j.val by
        rw [← pow_add, Nat.sub_add_cancel j.is_lt.le]]
    field_simp
    ring
  · -- the coefficient of order `p` has a pole beyond the regular order
    have hp : a.card < n := by rw [(hD 0).1]; omega
    have hnot : ¬Complex.LinearODEAtMostRegularAt
        (Complex.linearODEReciprocalCoeff (genODECoeff a b)) 0 := by
      intro H
      obtain ⟨g, hg, hev⟩ := H ⟨a.card, hp⟩
      set K := genThetaFinDiff (genThetaB b) a.card
      have hA : genThetaFinDiff (genThetaA a) a.card = (-1) ^ a.card * a.card.factorial := by
        have := genThetaFinDiff_natDegree_of_monic _ (genThetaA_monic a)
        rwa [genThetaA_natDegree] at this
      have hev' : (fun u => u * g u) =ᶠ[𝓝[≠] (0 : ℂ)] fun u =>
          (-1) ^ n * (u * K / a.card.factorial - (-1) ^ a.card) := by
        filter_upwards [hev, self_mem_nhdsWithin] with u hu hu0
        have hu0 : u ≠ 0 := hu0
        have hd : genODEDen a b u⁻¹ ≠ 0 := by
          rw [(hD _).2.1]; exact pow_ne_zero _ (inv_ne_zero hu0)
        rw [← hu]
        simp only [Complex.linearODEReciprocalCoeff, ← hndef]
        rw [linearODEReciprocalRaw_genODECoeff a b _ hu0 hd,
          linearODEReciprocalRaw_genODECoeff a b _ hu0 hd, (hD 0).2.2.1, (hD 0).2.2.2, hA,
          (hD u⁻¹).2.1]
        have hf : (a.card.factorial : ℂ) ≠ 0 := by exact_mod_cast a.card.factorial_ne_zero
        have hf' : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
        have hpow : u ^ n = u ^ (n - a.card) * u ^ a.card := by
          rw [← pow_add, Nat.sub_add_cancel hp.le]
        simp only [sub_zero, mul_zero, hpow]
        field_simp
        rw [show ((-1 : ℂ) ^ n) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; simp]
        ring
      have h1 : Filter.Tendsto (fun u => u * g u) (𝓝[≠] (0 : ℂ)) (𝓝 (0 * g 0)) :=
        ((continuous_id.continuousAt).mul hg.continuousAt).tendsto.mono_left
          nhdsWithin_le_nhds
      have h2 : Filter.Tendsto (fun u : ℂ => (-1) ^ n * (u * K / a.card.factorial -
          (-1) ^ a.card)) (𝓝[≠] (0 : ℂ)) (𝓝 ((-1) ^ n * (0 * K / a.card.factorial -
            (-1) ^ a.card))) :=
        (Continuous.tendsto (by fun_prop) _).mono_left nhdsWithin_le_nhds
      have := tendsto_nhds_unique (h1.congr' hev') h2
      simp only [zero_mul, zero_div, zero_sub, mul_neg] at this
      exact (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (by norm_num)))) this.symm
    exact ⟨fun H => hnot (linearODEAtMostRegularAt_of_ordinaryAt H), hnot⟩

/-- The classification for `p = q + 1`, without the regularity hypothesis on the lower
parameters. -/
theorem generalizedHypergeometric_ode_singularities_balanced' (a b : Multiset ℂ)
    (h : a.card = b.card + 1) :
    Complex.LinearODEAtMostRegularAt (genODECoeff a b) 0 ∧
    Complex.LinearODEAtMostRegularAt (genODECoeff a b) 1 ∧
    Complex.LinearODEAtMostRegularAtInfinity (genODECoeff a b) ∧
    ∀ z : ℂ, z ≠ 0 → z ≠ 1 → Complex.LinearODEOrdinaryAt (genODECoeff a b) z := by
  have hD := genODEDen_of_card_eq h
  set n := genODEOrder a b with hndef
  have hden : ∀ z, genODEDen a b z = z ^ n * (1 - z) := fun z => (hD z).2.1
  have hc : ∀ (j : Fin n) z, genODECoeff a b j z = (genThetaDCoeff (genThetaB b) j * z ^ j.val -
      genThetaDCoeff (genThetaA a) j * z ^ (j.val + 1)) / (z ^ n * (1 - z)) := fun j z => by
    rw [← hden]; rfl
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun z hz hz1 =>
    linearODEOrdinaryAt_genODECoeff (by
      rw [hden]; exact mul_ne_zero (pow_ne_zero _ hz) (sub_ne_zero.mpr (Ne.symm hz1)))⟩
  · refine ⟨fun z => (genThetaDCoeff (genThetaB b) j - genThetaDCoeff (genThetaA a) j * z) /
      (1 - z), AnalyticAt.div (by fun_prop) (by fun_prop) (by norm_num), ?_⟩
    have h1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 1 := nhdsWithin_le_nhds
      (isOpen_ne.mem_nhds (by norm_num : (0 : ℂ) ≠ 1))
    filter_upwards [self_mem_nhdsWithin, h1] with z hz hz1
    have hz0 : z ≠ 0 := hz
    have hz1' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    rw [hc, show z ^ n = z ^ (n - j.val) * z ^ j.val by
        rw [← pow_add, Nat.sub_add_cancel j.is_lt.le]]
    field_simp
    ring
  · refine ⟨fun z => -((z - 1) ^ (n - j.val - 1) * (genThetaDCoeff (genThetaB b) j * z ^ j.val -
      genThetaDCoeff (genThetaA a) j * z ^ (j.val + 1))) / z ^ n,
      AnalyticAt.div (by fun_prop) (by fun_prop) (by norm_num), ?_⟩
    have h0 : ∀ᶠ z in 𝓝[≠] (1 : ℂ), z ≠ 0 := nhdsWithin_le_nhds
      (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))
    filter_upwards [self_mem_nhdsWithin, h0] with z hz hz0
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    have hz1' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    rw [hc, show (z - 1) ^ (n - j.val) = (z - 1) ^ (n - j.val - 1) * (z - 1) by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.sub_pos_of_lt j.is_lt)]]
    field_simp
    ring
  · set KB := genThetaFinDiff (genThetaB b) j
    set KA := genThetaFinDiff (genThetaA a) j
    refine ⟨fun u => (u * KB - KA) / (j.val.factorial * (-1) ^ n * (u - 1)),
      AnalyticAt.div (by fun_prop) (by fun_prop) (by
        simp only [zero_sub, mul_neg, mul_one, ne_eq, neg_eq_zero]
        exact mul_ne_zero (by exact_mod_cast j.val.factorial_ne_zero)
          (pow_ne_zero _ (by norm_num))), ?_⟩
    have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ≠ 1 := nhdsWithin_le_nhds
      (isOpen_ne.mem_nhds (by norm_num : (0 : ℂ) ≠ 1))
    filter_upwards [self_mem_nhdsWithin, h1] with u hu hu1
    have hu0 : u ≠ 0 := hu
    have hu1' : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
    have hd : genODEDen a b u⁻¹ ≠ 0 := by
      rw [hden]
      refine mul_ne_zero (pow_ne_zero _ (inv_ne_zero hu0)) ?_
      rw [sub_ne_zero]; intro h1; apply hu1; rw [← inv_inv u, ← h1, inv_one]
    simp only [Complex.linearODEReciprocalCoeff]
    simp only [← hndef]
    rw [linearODEReciprocalRaw_genODECoeff a b _ hu0 hd,
      linearODEReciprocalRaw_genODECoeff a b _ hu0 hd, (hD 0).2.2.1, (hD 0).2.2.2, hden]
    have hf : (j.val.factorial : ℂ) ≠ 0 := by exact_mod_cast j.val.factorial_ne_zero
    have hf' : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hpow : u ^ n = u ^ (n - j.val) * u ^ j.val := by
      rw [← pow_add, Nat.sub_add_cancel j.is_lt.le]
    have hs : (1 : ℂ) - u⁻¹ ≠ 0 := by
      rw [sub_ne_zero]; intro h1; apply hu1; rw [← inv_inv u, ← h1, inv_one]
    simp only [sub_zero, hpow]
    field_simp
    ring

/-- Zero is at most regular, infinity is irregular, and there are no other singularities for p≤q. -/
theorem generalizedHypergeometric_ode_singularities_entire (a b : Multiset ℂ) (h : a.card ≤ b.card)
    (_hb : LowerParametersRegular b) :
    Complex.LinearODEAtMostRegularAt (genODECoeff a b) 0 ∧
    Complex.LinearODEIrregularAtInfinity (genODECoeff a b) ∧
    ∀ z : ℂ, z ≠ 0 → Complex.LinearODEOrdinaryAt (genODECoeff a b) z :=
  generalizedHypergeometric_ode_singularities_entire' a b h

/-- Zero, one and infinity are at most regular; removable parameter degeneracies are retained. -/
theorem generalizedHypergeometric_ode_singularities_balanced (a b : Multiset ℂ)
    (h : a.card = b.card + 1)
    (_hb : LowerParametersRegular b) :
    Complex.LinearODEAtMostRegularAt (genODECoeff a b) 0 ∧
    Complex.LinearODEAtMostRegularAt (genODECoeff a b) 1 ∧
    Complex.LinearODEAtMostRegularAtInfinity (genODECoeff a b) ∧
    ∀ z : ℂ, z ≠ 0 → z ≠ 1 → Complex.LinearODEOrdinaryAt (genODECoeff a b) z :=
  generalizedHypergeometric_ode_singularities_balanced' a b h

/-- The nominal operator order is max(p,q+1), independently of lower-order equations for special
solutions. -/
theorem generalizedHypergeometric_ode_nominal_order (a b : Multiset ℂ) :
    max (genThetaA a).natDegree (genThetaB b).natDegree = genODEOrder a b := by
  have hA (c : Multiset ℂ) : (genThetaA c).natDegree = c.card := by
    unfold genThetaA
    -- Mathlib's monic-product degree formula also covers the empty product.
    rw [Polynomial.natDegree_multiset_prod_of_monic]
    · simp only [Multiset.map_map, Function.comp_def, Polynomial.natDegree_X_add_C,
        Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
    · intro P hP
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hP
      exact Polynomial.monic_X_add_C x
  have hB : genThetaB b = genThetaA ((0 : ℂ) ::ₘ b.map (fun x => x - 1)) := by
    simp only [genThetaB, genThetaA, Multiset.map_cons, Multiset.prod_cons,
      Polynomial.C_0, add_zero, Multiset.map_map, Function.comp_def]
  rw [hB, hA, hA]
  simp only [Multiset.card_cons, Multiset.card_map, genODEOrder]

/-- The full nonresonant fundamental system at zero. -/
@[dlmf 16.8.E6]
theorem genFrobeniusZero_fundamental {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p ≤ q + 1)
    (hb : ∀ j, ∀ n : ℤ, b j ≠ n)
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, b i - b j ≠ n) :
    GenFundamentalSystem (parametersOfFin a) (parametersOfFin b) genFrobeniusDomain
        (genFrobeniusZero a b) := by
  sorry

/-- All resonant cases admit logarithmic Frobenius series, with analytic power series and logs
through order q. -/
theorem genFrobeniusZero_resonant {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p ≤ q + 1)
    (hb : LowerParametersRegular (parametersOfFin b)) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : Fin (q + 1) → ℂ → ℂ,
      GenFundamentalSystem (parametersOfFin a) (parametersOfFin b)
        (Complex.slitPlane ∩ Metric.ball 0 r) F ∧
      ∃ A : Fin (q + 1) → Fin (q + 1) → Fin (q + 1) → ℂ → ℂ,
        (∀ i j k, AnalyticOnNhd ℂ (A i j k) (Metric.ball 0 r)) ∧
        ∀ i z, z ∈ Complex.slitPlane ∩ Metric.ball 0 r →
          F i z = ∑ j, ∑ k, z ^ genFrobeniusRoot b j *
            Complex.log z ^ k.val * A i j k z := by
  sorry

/-- The nonresonant infinity solutions form a fundamental system in their principal exterior domain.
-/
@[dlmf 16.8.E7]
theorem genFrobeniusInfinity_fundamental {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (hb : LowerParametersRegular (parametersOfFin b))
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, a i - a j ≠ n) :
    GenFundamentalSystem (parametersOfFin a) (parametersOfFin b)
      {z : ℂ | 1 < ‖z‖ ∧ -z ∈ Complex.slitPlane}
      (fun j z => genFrobeniusInfinityLog a b j (Complex.log (-z))) := by
  sorry

/-- The connection formula on both correlated closed log(-z) cut sides. -/
@[dlmf 16.8.E8]
theorem generalizedHypergeometric_infinity_connection {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (hb : LowerParametersRegular (parametersOfFin b))
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, a i - a j ≠ n)
    {w : ℂ} (hw : |w.im| ≤ Real.pi) (hz : -Complex.exp w ≠ 1) :
    genHGNegativeLog (parametersOfFin a) (parametersOfFin b) w =
      ∑ j, genInfinityConnectionCoeff a b j * genFrobeniusInfinityLog a b j w := by
  sorry

/-- The convergent displaced-center expansion with correlated principal branches and all regularized
finite inner polynomials. -/
@[dlmf 16.8.E9]
theorem generalizedHypergeometric_centered_infinity_connection {q : ℕ} (a : Fin (q + 1) → ℂ)
    (b : Fin q → ℂ)
    (ha : LowerParametersRegular (parametersOfFin a))
        (hb : LowerParametersRegular (parametersOfFin b))
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, a i - a j ≠ n)
    (z₀ : ℂ) {z : ℂ} (hz : z ∈ genCenteredInfinityDomain z₀) :
    ∃ v : Fin (q + 1) → ℂ,
      (∀ j, HasSum (genCenteredInfinityTerm a b z₀ z j) (v j)) ∧
      gammaProduct (parametersOfFin a) *
          regularizedGeneralizedHypergeometric (parametersOfFin a) (parametersOfFin b) z =
        ∑ j, (z₀ - z) ^ (-a j) * v j := by
  sorry

/-- A rising factorial divided by the matching power is a product of `1 + j/α`. -/
private lemma pochhammer_div_pow_eq_prod {α : ℂ} (hα : α ≠ 0) (k : ℕ) :
    pochhammer α k / α ^ k = ∏ j ∈ range k, (1 + j / α) := by
  induction k with
  | zero => simp [pochhammer_zero]
  | succ k ih =>
    rw [pochhammer_succ, prod_range_succ, ← ih, pow_succ]
    field_simp

/-- Adding an upper parameter multiplies the coefficient by one rising factorial. -/
private lemma generalizedHypergeometricCoeff_cons (x : ℂ) (a b : Multiset ℂ) (n : ℕ) :
    generalizedHypergeometricCoeff (x ::ₘ a) b n = pochhammer x n *
        generalizedHypergeometricCoeff a b n := by
  simp only [generalizedHypergeometricCoeff, pochhammerProduct, Multiset.map_cons,
      Multiset.prod_cons]
  ring

/-- The coefficient series converges absolutely in the open unit disk for p≤q+1. -/
private lemma summable_norm_generalizedHypergeometricCoeff_mul_pow_of_norm_lt_one {a b : Multiset ℂ}
    (h : a.card ≤ b.card + 1)
    (hb : LowerParametersRegular b) {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun n : ℕ => ‖generalizedHypergeometricCoeff a b n * w ^ n‖) := by
  have hr : (1 : ENNReal) ≤
      (FormalMultilinearSeries.ofScalars ℂ (generalizedHypergeometricCoeff a b)).radius := by
    rw [genScalarSeries_eq_gamma_smul hb,
      FormalMultilinearSeries.radius_smul_eq _ (gammaProduct_ne_zero hb)]
    by_cases hc : a.card ≤ b.card
    · rw [Complex.radius_regularizedHGFunSeries_eq_top hc]; exact le_top
    · exact Complex.radius_regularizedHGFunSeries_ge_one (by omega)
  have hlt : ((‖w‖₊ : NNReal) : ENNReal) <
      (FormalMultilinearSeries.ofScalars ℂ (generalizedHypergeometricCoeff a b)).radius :=
    lt_of_lt_of_le (by exact_mod_cast hw) hr
  have := (FormalMultilinearSeries.ofScalars ℂ
      (generalizedHypergeometricCoeff a b)).summable_norm_mul_pow hlt
  simpa only [FormalMultilinearSeries.ofScalars_norm, coe_nnnorm, norm_mul, norm_pow] using this

/-- Upper-parameter confluence along every complex direction to infinity. -/
@[dlmf 16.8.E10]
theorem generalizedHypergeometric_upper_confluence (a b : Multiset ℂ) (h : a.card ≤ b.card)
    (hb : LowerParametersRegular b) (z : ℂ) :
    Tendsto (fun α : ℂ => generalizedHypergeometric (α ::ₘ a) b (z / α)) (Bornology.cobounded ℂ)
      (𝓝 (generalizedHypergeometric a b z)) := by
  set R : ℝ := ‖z‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  have hfar : ∀ᶠ α : ℂ in Bornology.cobounded ℂ, R ≤ ‖α‖ :=
    tendsto_norm_cobounded_atTop.eventually_ge_atTop R
  have hsum : ∀ᶠ α : ℂ in Bornology.cobounded ℂ,
      generalizedHypergeometric (α ::ₘ a) b (z / α) = ∑' n,
          generalizedHypergeometricCoeff (α ::ₘ a) b n * (z / α) ^ n := by
    filter_upwards [hfar] with α hα
    have hα0 : 0 < ‖α‖ := lt_of_lt_of_le hR0 hα
    refine (generalizedHypergeometric_hasSum_disk (by simp; omega) hb ?_).tsum_eq.symm
    rw [norm_div, div_lt_one hα0]; linarith
  rw [← (generalizedHypergeometric_hasSum_entire h hb z).tsum_eq]
  refine Tendsto.congr' (EventuallyEq.symm hsum) ?_
  have hRz : ‖z / (R : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR0.le, div_lt_one hR0]; linarith
  refine tendsto_tsum_of_dominated_convergence
    (summable_norm_generalizedHypergeometricCoeff_mul_pow_of_norm_lt_one (a := (R : ℂ) ::ₘ a)
        (by simp; omega) hb hRz) ?_ ?_
  · intro k
    have hinv : Tendsto (fun α : ℂ => α⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := tendsto_inv₀_cobounded
    have hprod : Tendsto (fun α : ℂ => ∏ j ∈ range k, (1 + (j : ℂ) * α⁻¹))
        (Bornology.cobounded ℂ) (𝓝 1) := by
      have := tendsto_finsetProd (range k) (fun j _ =>
        ((hinv.const_mul (j : ℂ)).const_add 1))
      simpa using this
    have := hprod.mul_const (generalizedHypergeometricCoeff a b k * z ^ k)
    rw [one_mul] at this
    refine this.congr' ?_
    filter_upwards [hfar] with α hα
    have hα0 : α ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR0 hα)
    simp only [← div_eq_mul_inv]
    rw [generalizedHypergeometricCoeff_cons, div_pow, ← pochhammer_div_pow_eq_prod hα0]
    ring
  · filter_upwards [hfar] with α hα k
    have hα0 : α ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR0 hα)
    have hR0' : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
    have e1 : generalizedHypergeometricCoeff (α ::ₘ a) b k * (z / α) ^ k =
        (∏ j ∈ range k, (1 + j / α)) * (generalizedHypergeometricCoeff a b k * z ^ k) := by
      rw [generalizedHypergeometricCoeff_cons, div_pow, ← pochhammer_div_pow_eq_prod hα0]; ring
    have e2 : generalizedHypergeometricCoeff ((R : ℂ) ::ₘ a) b k * (z / R) ^ k =
        (∏ j ∈ range k, (1 + j / (R : ℂ))) * (generalizedHypergeometricCoeff a b k * z ^ k) := by
      rw [generalizedHypergeometricCoeff_cons, div_pow, ← pochhammer_div_pow_eq_prod hR0']; ring
    rw [e1, e2, norm_mul, norm_mul _ (generalizedHypergeometricCoeff a b k * z ^ k)]
    gcongr
    rw [norm_prod, norm_prod]
    gcongr with j hj
    have hj : ‖(1 : ℂ) + j / R‖ = 1 + j / R := by
      rw [show (1 : ℂ) + j / R = ((1 + j / R : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [hj]
    calc ‖(1 : ℂ) + j / α‖ ≤ 1 + j / ‖α‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_one, norm_div, Complex.norm_natCast]
      _ ≤ 1 + j / R := by gcongr

/-- Lower-parameter confluence with the full angle-dependent z restriction from the source. -/
@[dlmf 16.8.E11]
theorem generalizedHypergeometric_lower_confluence (a b : Multiset ℂ) (h : a.card ≤ b.card + 1)
    (hb : LowerParametersRegular b)
    (z : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) :
    Tendsto (fun β : ℂ => generalizedHypergeometric a (β ::ₘ b) (β * z))
      (comap norm atTop ⊓ 𝓟 {β : ℂ | β ≠ 0 ∧ |β.arg| ≤ Real.pi - δ ∧
        (a.card ≤ b.card ∨ (|β.arg| ≤ Real.pi / 2 ∧ ‖z‖ < 1) ∨
          (Real.pi / 2 ≤ |β.arg| ∧ ‖z‖ < |Real.sin β.arg|))})
      (𝓝 (generalizedHypergeometric a b z)) := by
  sorry

/-- Resonant infinity exponents admit a fundamental system with power series in 1/z
and logarithms of degree at most q, without integer-difference exclusions. -/
theorem genFrobeniusInfinity_resonant {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (hb : LowerParametersRegular (parametersOfFin b)) :
    ∃ R : ℝ, 1 < R ∧ ∃ F : Fin (q + 1) → ℂ → ℂ,
      GenFundamentalSystem (parametersOfFin a) (parametersOfFin b)
        {z : ℂ | R < ‖z‖ ∧ -z ∈ Complex.slitPlane} F ∧
      ∃ A : Fin (q + 1) → Fin (q + 1) → Fin (q + 1) → ℂ → ℂ,
        (∀ i j k, AnalyticOnNhd ℂ (A i j k) (Metric.ball 0 (1 / R))) ∧
        ∀ i z, R < ‖z‖ → -z ∈ Complex.slitPlane →
          F i z = ∑ j, ∑ k, (-z) ^ (-a j) *
            Complex.log (-z) ^ k.val * A i j k z⁻¹ := by
  sorry

end DLMF.Hypergeometric
