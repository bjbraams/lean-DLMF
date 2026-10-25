/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.AnalyticProperties
public import DLMF.GeneralizedHypergeometric.Derivatives
public import DLMFMathlib.Analysis.ODE.Singularities
public import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Differential equations and confluence: DLMF §16.8

The existing proved theta equation is reused and extended to principal continuation.
Stirling numbers convert theta polynomials to ordinary derivative coefficients.
Singularities are classified by their coefficient germs: removable parameter
specializations are allowed, and q=0 is not falsely declared singular at zero.
Fundamental systems include resonant logarithmic Frobenius series. Connection
formulas retain correlated logarithm sheets; an arbitrary displaced center uses
the common connected principal component rather than unrelated cut determinations.
The nominal-order proof reuses Mathlib's degree formula for products of monic
polynomials, including empty parameter multisets.
-/

@[expose] public section
open Complex Filter Set Finset Polynomial
open scoped Topology Real
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
def genODESolution (a b : Multiset ℂ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  thetaPoly (genThetaB b) f z = z * thetaPoly (genThetaA a) f z

/-- A fundamental system on an open domain, expressed by independence and full span. -/
def genFundamentalSystem {n : ℕ} (a b : Multiset ℂ) (D : Set ℂ)
    (F : Fin n → ℂ → ℂ) : Prop :=
  (∀ i, AnalyticOnNhd ℂ (F i) D ∧ ∀ z ∈ D, genODESolution a b (F i) z) ∧
  LinearIndependent ℂ (fun i => fun z : D => F i z) ∧
  ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f D → (∀ z ∈ D, genODESolution a b f z) →
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
  exact Fin.cases (genHG (genParams a) (genParams b) z)
    (fun j => z ^ (1 - b j) *
      genHG (genShift (genParams a) (1 - b j))
        ((2 - b j) ::ₘ genShift ((genParams b).erase (b j)) (1 - b j)) z) i

/-- A closed log(-z) sheet: the upper edge corresponds to the lower z-cut value. -/
def genHGNegativeLog (a b : Multiset ℂ) (w : ℂ) : ℂ := by
  classical
  exact if w.im = Real.pi then genHGLower a b (-Complex.exp w)
    else genHG a b (-Complex.exp w)

/-- The nonresonant infinity solutions with an explicit log(-z) sheet (16.8.7). -/
@[dlmf 16.8.E7]
def genFrobeniusInfinityLog {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (j : Fin (q + 1)) (w : ℂ) : ℂ := by
  classical
  exact Complex.exp (-a j * w) *
    genHGNegativeLog ((a j) ::ₘ genShift (genParams b) (1 + a j))
      (genShift ((genParams a).erase (a j)) (1 + a j)) (-w)

/-- Connection coefficient to the jth infinity solution. -/
def genInfinityConnectionCoeff {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (j : Fin (q + 1)) : ℂ :=
  (∏ k ∈ univ.erase j, Gamma (a k - a j)) * genGamma (genParams b) /
    ((∏ k ∈ univ.erase j, Gamma (a k)) * genGamma (genShift (genParams b) (-a j)))

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
      Complex.regularizedHGFunCoeff (genShift (genParams a) (-a j - n))
        (genShift (genParams b) (-a j - n)) k * z₀ ^ k) * (z - z₀) ^ (-(n : ℤ))

/-- The proved theta equation continued throughout the ordinary principal analytic domain. -/
@[dlmf 16.8.E3]
theorem genHG_theta_ode (a b : Multiset ℂ) (hb : genDenRegular b)
    (h : a.card ≤ b.card + 1 ∨ genTerminates a) {z : ℂ} (hz : z ∈ genAnalyticDomain a b) :
    genODESolution a b (genHG a b) z := by
  sorry

/-- Derivative of an iterated derivative of a smooth function. -/
lemma ghbR4_hasDerivAt_iteratedDeriv {f : ℂ → ℂ} (hf : ContDiff ℂ ⊤ f) (j : ℕ) (w : ℂ) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f w) w := by
  rw [iteratedDeriv_succ]
  exact ((hf.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)) w).hasDerivAt

/-- Powers of theta in ordinary derivatives: `θ^k f = Σ S(k,j) z^j f^(j)` (Stirling numbers of the second kind). -/
lemma ghbR4_eulerTheta_iterate_stirling {f : ℂ → ℂ} (hf : ContDiff ℂ ⊤ f) (k : ℕ) :
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
      have := ((hasDerivAt_pow j z).mul (ghbR4_hasDerivAt_iteratedDeriv hf j z)).const_mul
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
lemma ghbR4_thetaPoly_eq_sum {f : ℂ → ℂ} (hf : ContDiff ℂ ⊤ f) (P : ℂ[X]) {M : ℕ}
    (hM : P.natDegree ≤ M) (z : ℂ) :
    thetaPoly P f z = ∑ j ∈ range (M + 1), genThetaDCoeff P j * z ^ j * iteratedDeriv j f z := by
  unfold thetaPoly genThetaDCoeff
  rw [sum_congr rfl fun k hk => by
    rw [ghbR4_eulerTheta_iterate_stirling hf k M
      (by have := Finset.mem_range.mp hk; omega) z, mul_sum]]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [sum_mul, sum_mul]
  apply sum_congr rfl
  intro k _
  ring

/-- Iterated theta commutes with constant multiples. -/
lemma ghbR4_eulerTheta_iterate_const_mul (c : ℂ) (F : ℂ → ℂ) (k : ℕ) :
    (eulerTheta^[k] fun z => c * F z) = fun z => c * (eulerTheta^[k] F) z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext z
    simp only [eulerTheta, deriv_const_mul_field]
    ring

/-- Theta polynomials commute with constant multiples. -/
lemma ghbR4_thetaPoly_const_mul (c : ℂ) (F : ℂ → ℂ) (P : ℂ[X]) (z : ℂ) :
    thetaPoly P (fun z => c * F z) z = c * thetaPoly P F z := by
  unfold thetaPoly
  rw [mul_sum]
  apply sum_congr rfl
  intro k _
  rw [ghbR4_eulerTheta_iterate_const_mul]
  ring

/-- Degree of the upper theta polynomial. -/
lemma ghbR4_genThetaA_natDegree (c : Multiset ℂ) : (genThetaA c).natDegree = c.card := by
  unfold genThetaA
  rw [Polynomial.natDegree_multiset_prod_of_monic]
  · simp only [Multiset.map_map, Function.comp_def, Polynomial.natDegree_X_add_C,
      Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
  · intro P hP
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hP
    exact Polynomial.monic_X_add_C x

/-- The upper theta polynomial is monic. -/
lemma ghbR4_genThetaA_monic (c : Multiset ℂ) : (genThetaA c).Monic := by
  unfold genThetaA
  apply Polynomial.monic_multiset_prod_of_monic
  intro x _
  exact Polynomial.monic_X_add_C x

/-- The lower theta polynomial as an upper one with an added zero parameter. -/
lemma ghbR4_genThetaB_eq (b : Multiset ℂ) :
    genThetaB b = genThetaA ((0 : ℂ) ::ₘ b.map (fun x => x - 1)) := by
  simp only [genThetaB, genThetaA, Multiset.map_cons, Multiset.prod_cons,
    Polynomial.C_0, add_zero, Multiset.map_map, Function.comp_def]

/-- The top derivative coefficient of a monic theta polynomial is one. -/
lemma ghbR4_genThetaDCoeff_top (P : ℂ[X]) (hP : P.Monic) :
    genThetaDCoeff P P.natDegree = 1 := by
  unfold genThetaDCoeff
  rw [sum_range_succ, sum_eq_zero (fun k hk => by
    rw [Nat.stirlingSecond_eq_zero_of_lt (Finset.mem_range.mp hk)]; simp)]
  rw [Nat.stirlingSecond_self, hP.coeff_natDegree]; simp

/-- Derivative coefficients above the degree vanish. -/
lemma ghbR4_genThetaDCoeff_above (P : ℂ[X]) {j : ℕ} (hj : P.natDegree < j) :
    genThetaDCoeff P j = 0 := by
  unfold genThetaDCoeff
  exact sum_eq_zero (fun k hk => by
    rw [Nat.stirlingSecond_eq_zero_of_lt (by have := Finset.mem_range.mp hk; omega)]; simp)

/-- The zeroth derivative coefficient of the lower theta polynomial vanishes. -/
lemma ghbR4_genThetaDCoeff_B_zero (b : Multiset ℂ) : genThetaDCoeff (genThetaB b) 0 = 0 := by
  unfold genThetaDCoeff
  rw [sum_range_succ']
  rw [sum_eq_zero (fun k _ => by rw [Nat.stirlingSecond_succ_zero]; simp)]
  simp [genThetaB]

/-- For p≤q the principal function is the Gamma-normalized native series. -/
lemma ghbR4_genHG_eq_entire {a b : Multiset ℂ} (h : a.card ≤ b.card) :
    genHG a b = fun z => genGamma b * Complex.regularizedHGFun a b z := by
  have hne : a.card ≠ b.card + 1 := by omega
  funext z
  unfold genHG genRegularizedHG
  simp only [ite_eq_right hne]

/-- For p≤q the theta equation holds at every complex point. -/
lemma ghbR4_genHG_entire_theta {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    genODESolution a b (genHG a b) z := by
  unfold genODESolution
  rw [ghbR4_genHG_eq_entire h, ghbR4_thetaPoly_const_mul, ghbR4_thetaPoly_const_mul]
  have := regularizedHGFun_ode_of_card_le h z
  simp only [genThetaA, genThetaB]
  rw [this]; ring

/-- The full expanded equation for p≤q with the explicit alpha and beta constants. -/
@[dlmf 16.8.E4]
theorem genHG_expanded_ode_entire (a b : Multiset ℂ) (h : a.card ≤ b.card) (hb : genDenRegular b) (z : ℂ) :
    z ^ b.card * iteratedDeriv (b.card + 1) (genHG a b) z +
      (∑ j ∈ Finset.Icc 1 b.card, z ^ (j - 1) *
        (genODEAlpha a j * z + genODEBeta b j) * iteratedDeriv j (genHG a b) z) +
      genODEAlpha a 0 * genHG a b z = 0 := by
  set f := genHG a b with hfdef
  set q := b.card
  have hf : ContDiff ℂ ⊤ f := (genHG_entire h hb).contDiff
  have hc : ∀ j, Continuous (iteratedDeriv j f) := fun j => hf.continuous_iteratedDeriv j
    le_top
  have hBdeg : (genThetaB b).natDegree = q + 1 := by
    rw [ghbR4_genThetaB_eq, ghbR4_genThetaA_natDegree]; simp [q]
  have hAdeg : (genThetaA a).natDegree = a.card := ghbR4_genThetaA_natDegree a
  have hβtop : genODEBeta b (q + 1) = 1 := by
    rw [genODEBeta, ← hBdeg]
    exact ghbR4_genThetaDCoeff_top _ (by rw [ghbR4_genThetaB_eq]; exact ghbR4_genThetaA_monic _)
  have hαtop : genODEAlpha a (q + 1) = 0 := by
    rw [genODEAlpha, ghbR4_genThetaDCoeff_above _ (by rw [hAdeg]; omega), neg_zero]
  have hβ0 : genODEBeta b 0 = 0 := ghbR4_genThetaDCoeff_B_zero b
  set T : ℂ → ℂ := fun z => z ^ q * iteratedDeriv (q + 1) f z +
      (∑ j ∈ Finset.Icc 1 q, z ^ (j - 1) *
        (genODEAlpha a j * z + genODEBeta b j) * iteratedDeriv j f z) +
      genODEAlpha a 0 * f z with hT
  have hzT : ∀ z, z * T z = 0 := by
    intro z
    have hode := ghbR4_genHG_entire_theta h z
    unfold genODESolution at hode
    rw [ghbR4_thetaPoly_eq_sum hf _ (M := q + 1) hBdeg.le,
      ghbR4_thetaPoly_eq_sum hf _ (M := q + 1) (by rw [hAdeg]; omega)] at hode
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

/-- The full expanded equation for p=q+1. -/
@[dlmf 16.8.E5]
theorem genHG_expanded_ode_balanced (a b : Multiset ℂ) (h : a.card = b.card + 1) (hb : genDenRegular b)
    {z : ℂ} (hz : z ∈ cutPlane) :
    z ^ b.card * (1 - z) * iteratedDeriv (b.card + 1) (genHG a b) z +
      (∑ j ∈ Finset.Icc 1 b.card, z ^ (j - 1) *
        (genODEAlpha a j * z + genODEBeta b j) * iteratedDeriv j (genHG a b) z) +
      genODEAlpha a 0 * genHG a b z = 0 := by
  sorry

/-- Zero is at most regular, infinity is irregular, and there are no other singularities for p≤q. -/
theorem genHG_ode_singularities_entire (a b : Multiset ℂ) (h : a.card ≤ b.card) (hb : genDenRegular b) :
    Complex.linearODEAtMostRegularAt (genODECoeff a b) 0 ∧
    Complex.linearODEIrregularAtInfinity (genODECoeff a b) ∧
    ∀ z : ℂ, z ≠ 0 → Complex.linearODEOrdinaryAt (genODECoeff a b) z := by
  sorry

/-- Zero, one and infinity are at most regular; removable parameter degeneracies are retained. -/
theorem genHG_ode_singularities_balanced (a b : Multiset ℂ) (h : a.card = b.card + 1) (hb : genDenRegular b) :
    Complex.linearODEAtMostRegularAt (genODECoeff a b) 0 ∧
    Complex.linearODEAtMostRegularAt (genODECoeff a b) 1 ∧
    Complex.linearODEAtMostRegularAtInfinity (genODECoeff a b) ∧
    ∀ z : ℂ, z ≠ 0 → z ≠ 1 → Complex.linearODEOrdinaryAt (genODECoeff a b) z := by
  sorry

/-- The nominal operator order is max(p,q+1), independently of lower-order equations for special solutions. -/
theorem genHG_ode_nominal_order (a b : Multiset ℂ) :
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
    genFundamentalSystem (genParams a) (genParams b) genFrobeniusDomain (genFrobeniusZero a b) := by
  sorry

/-- All resonant cases admit logarithmic Frobenius series, with analytic power series and logs through order q. -/
theorem genFrobeniusZero_resonant {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p ≤ q + 1)
    (hb : genDenRegular (genParams b)) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : Fin (q + 1) → ℂ → ℂ,
      genFundamentalSystem (genParams a) (genParams b)
        (Complex.slitPlane ∩ Metric.ball 0 r) F ∧
      ∃ A : Fin (q + 1) → Fin (q + 1) → Fin (q + 1) → ℂ → ℂ,
        (∀ i j k, AnalyticOnNhd ℂ (A i j k) (Metric.ball 0 r)) ∧
        ∀ i z, z ∈ Complex.slitPlane ∩ Metric.ball 0 r →
          F i z = ∑ j, ∑ k, z ^ genFrobeniusRoot b j *
            Complex.log z ^ k.val * A i j k z := by
  sorry

/-- The nonresonant infinity solutions form a fundamental system in their principal exterior domain. -/
@[dlmf 16.8.E7]
theorem genFrobeniusInfinity_fundamental {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (hb : genDenRegular (genParams b))
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, a i - a j ≠ n) :
    genFundamentalSystem (genParams a) (genParams b)
      {z : ℂ | 1 < ‖z‖ ∧ -z ∈ Complex.slitPlane}
      (fun j z => genFrobeniusInfinityLog a b j (Complex.log (-z))) := by
  sorry

/-- The connection formula on both correlated closed log(-z) cut sides. -/
@[dlmf 16.8.E8]
theorem genHG_infinity_connection {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (hb : genDenRegular (genParams b))
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, a i - a j ≠ n)
    {w : ℂ} (hw : |w.im| ≤ Real.pi) (hz : -Complex.exp w ≠ 1) :
    genHGNegativeLog (genParams a) (genParams b) w =
      ∑ j, genInfinityConnectionCoeff a b j * genFrobeniusInfinityLog a b j w := by
  sorry

/-- The convergent displaced-center expansion with correlated principal branches and all regularized finite inner polynomials. -/
@[dlmf 16.8.E9]
theorem genHG_centered_infinity_connection {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (ha : genDenRegular (genParams a)) (hb : genDenRegular (genParams b))
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, a i - a j ≠ n)
    (z₀ : ℂ) {z : ℂ} (hz : z ∈ genCenteredInfinityDomain z₀) :
    ∃ v : Fin (q + 1) → ℂ,
      (∀ j, HasSum (genCenteredInfinityTerm a b z₀ z j) (v j)) ∧
      genGamma (genParams a) * genRegularizedHG (genParams a) (genParams b) z =
        ∑ j, (z₀ - z) ^ (-a j) * v j := by
  sorry

/-- A rising factorial divided by the matching power is a product of `1 + j/α`. -/
lemma ghbR4_poch_div_pow {α : ℂ} (hα : α ≠ 0) (k : ℕ) :
    poch α k / α ^ k = ∏ j ∈ range k, (1 + j / α) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ, prod_range_succ, ← ih, pow_succ]
    field_simp

/-- Adding an upper parameter multiplies the coefficient by one rising factorial. -/
lemma ghbR4_genCoeff_cons (x : ℂ) (a b : Multiset ℂ) (n : ℕ) :
    genCoeff (x ::ₘ a) b n = poch x n * genCoeff a b n := by
  simp only [genCoeff, genPoch, Multiset.map_cons, Multiset.prod_cons]
  ring

/-- The coefficient series converges absolutely in the open unit disk for p≤q+1. -/
lemma ghbR4_summable_norm_disk {a b : Multiset ℂ} (h : a.card ≤ b.card + 1)
    (hb : genDenRegular b) {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun n : ℕ => ‖genCoeff a b n * w ^ n‖) := by
  have hr : (1 : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ (genCoeff a b)).radius := by
    rw [genScalarSeries_eq_gamma_smul hb,
      FormalMultilinearSeries.radius_smul_eq _ (genGamma_ne_zero hb)]
    by_cases hc : a.card ≤ b.card
    · rw [Complex.radius_regularizedHGFunSeries_eq_top hc]; exact le_top
    · exact Complex.radius_regularizedHGFunSeries_ge_one (by omega)
  have hlt : ((‖w‖₊ : NNReal) : ENNReal) < (FormalMultilinearSeries.ofScalars ℂ (genCoeff a b)).radius :=
    lt_of_lt_of_le (by exact_mod_cast hw) hr
  have := (FormalMultilinearSeries.ofScalars ℂ (genCoeff a b)).summable_norm_mul_pow hlt
  simpa only [FormalMultilinearSeries.ofScalars_norm, coe_nnnorm, norm_mul, norm_pow] using this

/-- Upper-parameter confluence along every complex direction to infinity. -/
@[dlmf 16.8.E10]
theorem genHG_upper_confluence (a b : Multiset ℂ) (h : a.card ≤ b.card) (hb : genDenRegular b) (z : ℂ) :
    Tendsto (fun α : ℂ => genHG (α ::ₘ a) b (z / α)) (Bornology.cobounded ℂ)
      (𝓝 (genHG a b z)) := by
  set R : ℝ := ‖z‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  have hfar : ∀ᶠ α : ℂ in Bornology.cobounded ℂ, R ≤ ‖α‖ :=
    tendsto_norm_cobounded_atTop.eventually_ge_atTop R
  have hsum : ∀ᶠ α : ℂ in Bornology.cobounded ℂ,
      genHG (α ::ₘ a) b (z / α) = ∑' n, genCoeff (α ::ₘ a) b n * (z / α) ^ n := by
    filter_upwards [hfar] with α hα
    have hα0 : 0 < ‖α‖ := lt_of_lt_of_le hR0 hα
    refine (genHG_hasSum_disk (by simp; omega) hb ?_).tsum_eq.symm
    rw [norm_div, div_lt_one hα0]; linarith
  rw [← (genHG_hasSum_entire h hb z).tsum_eq]
  refine Tendsto.congr' (EventuallyEq.symm hsum) ?_
  have hRz : ‖z / (R : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR0.le, div_lt_one hR0]; linarith
  refine tendsto_tsum_of_dominated_convergence
    (ghbR4_summable_norm_disk (a := (R : ℂ) ::ₘ a) (by simp; omega) hb hRz) ?_ ?_
  · intro k
    have hinv : Tendsto (fun α : ℂ => α⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := tendsto_inv₀_cobounded
    have hprod : Tendsto (fun α : ℂ => ∏ j ∈ range k, (1 + (j : ℂ) * α⁻¹))
        (Bornology.cobounded ℂ) (𝓝 1) := by
      have := tendsto_finsetProd (range k) (fun j _ =>
        ((hinv.const_mul (j : ℂ)).const_add 1))
      simpa using this
    have := hprod.mul_const (genCoeff a b k * z ^ k)
    rw [one_mul] at this
    refine this.congr' ?_
    filter_upwards [hfar] with α hα
    have hα0 : α ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR0 hα)
    simp only [← div_eq_mul_inv]
    rw [ghbR4_genCoeff_cons, div_pow, ← ghbR4_poch_div_pow hα0]
    ring
  · filter_upwards [hfar] with α hα k
    have hα0 : α ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR0 hα)
    have hR0' : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
    have e1 : genCoeff (α ::ₘ a) b k * (z / α) ^ k =
        (∏ j ∈ range k, (1 + j / α)) * (genCoeff a b k * z ^ k) := by
      rw [ghbR4_genCoeff_cons, div_pow, ← ghbR4_poch_div_pow hα0]; ring
    have e2 : genCoeff ((R : ℂ) ::ₘ a) b k * (z / R) ^ k =
        (∏ j ∈ range k, (1 + j / (R : ℂ))) * (genCoeff a b k * z ^ k) := by
      rw [ghbR4_genCoeff_cons, div_pow, ← ghbR4_poch_div_pow hR0']; ring
    rw [e1, e2, norm_mul, norm_mul _ (genCoeff a b k * z ^ k)]
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
theorem genHG_lower_confluence (a b : Multiset ℂ) (h : a.card ≤ b.card + 1) (hb : genDenRegular b)
    (z : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) :
    Tendsto (fun β : ℂ => genHG a (β ::ₘ b) (β * z))
      (comap norm atTop ⊓ 𝓟 {β : ℂ | β ≠ 0 ∧ |β.arg| ≤ Real.pi - δ ∧
        (a.card ≤ b.card ∨ (|β.arg| ≤ Real.pi / 2 ∧ ‖z‖ < 1) ∨
          (Real.pi / 2 ≤ |β.arg| ∧ ‖z‖ < |Real.sin β.arg|))})
      (𝓝 (genHG a b z)) := by
  sorry

/-- Resonant infinity exponents admit a fundamental system with power series in 1/z
and logarithms of degree at most q, without integer-difference exclusions. -/
theorem genFrobeniusInfinity_resonant {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (hb : genDenRegular (genParams b)) :
    ∃ R : ℝ, 1 < R ∧ ∃ F : Fin (q + 1) → ℂ → ℂ,
      genFundamentalSystem (genParams a) (genParams b)
        {z : ℂ | R < ‖z‖ ∧ -z ∈ Complex.slitPlane} F ∧
      ∃ A : Fin (q + 1) → Fin (q + 1) → Fin (q + 1) → ℂ → ℂ,
        (∀ i j k, AnalyticOnNhd ℂ (A i j k) (Metric.ball 0 (1 / R))) ∧
        ∀ i z, R < ‖z‖ → -z ∈ Complex.slitPlane →
          F i z = ∑ j, ∑ k, (-z) ^ (-a j) *
            Complex.log (-z) ^ k.val * A i j k z⁻¹ := by
  sorry

end DLMF.Hypergeometric
