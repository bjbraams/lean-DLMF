/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.SpecialValues.DerivativesAndResidues

/-!
# Real Jacobian functions and half-period values

The bridges between the complex theta quotients and the real-variable `sn, cn, dn`, the values
at quarter and three-quarter periods of Table 22.5.2, and the limits of `K` and `K'` in
DLMF §22.5(ii).

## Main definitions

* `AbsImLtRe`: the condition `|Im a| < Re a`, an argument in `(-π/4, π/4)`.
* `IsPosReal`: positive real numbers.

## Main results

* `jacobiSn_ofReal`, `jacobiCn_ofReal`, `jacobiDn_ofReal`: for `0 < k < 1` and real `u`,
  the complex `sn, cn, dn` are the real-variable functions defined through the amplitude.
* `jacobi_specialValues_HalfK`, `jacobi_specialValues_ThreeHalfK`,
  `jacobi_specialValues_HalfKp`, `jacobi_specialValues_ThreeHalfKp`,
  `jacobi_specialValues_HalfKKp`, `jacobi_specialValues_ThreeHalfKKp`: Table 22.5.2.
* `tendsto_completeEllipticK_zero`, `tendsto_completeEllipticKPrime_one`: `K(k) → π/2` as `k → 0+`
  and `K'(k) → π/2` as `k → 1-`.
* `tendsto_norm_completeEllipticKPrime_zero`, `tendsto_norm_completeEllipticK_one`: `K'(k) → ∞` as
  `k → 0+` and `K(k) → ∞` as `k → 1-`.

## Implementation notes

The real bridges are proved by ODE uniqueness. In Table 22.5.2 the squares follow from
Table 22.4.3 and the addition theorem, and the principal square roots are selected by the
identity theorem in `k` from the real case `0 < k < 1`; the `iK'/2` values use Jacobi's
imaginary transformation. The divergence of `K` and `K'` follows from
`K(1 - δ²) ≥ log(π/(2δ))/√2`.
-/

@[expose] public section

open Complex DLMF.Elliptic Filter

open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

macro "jacobi_value_tac " hk:term:max : tactic => `(tactic|
  (simp only [jacobiSn_zero $hk, jacobiCn_zero $hk, jacobiDn_zero $hk, jacobiCd_zero $hk,
    jacobiSd_zero $hk, jacobiNd_zero $hk, jacobiDc_zero $hk, jacobiNc_zero $hk,
    jacobiSc_zero $hk, mul_one, mul_zero, neg_zero] <;> try ring))

/-! ### Real bridges (DLMF 22.2.4–22.2.6 on the real line)

For `0 < k < 1` and real `u`, the theta-quotient `sn, cn, dn` agree with the amplitude-based
`Real.jacobiSnOfParameter, Real.jacobiCnOfParameter, Real.jacobiDnOfParameter` of parameter
`m = k²`: both triples solve `s' = cd, c' = -sd, d' = -k²sc` with `(s, c, d)(0) = (0, 1, 1)`, so
they agree by ODE uniqueness (`ODE_solution_unique_of_mem_Ioo`). (Moved here from `Basic`.) -/

/-- For real `0 < k < 1`, the complex `sn, cn, dn` have no pole on the real line. -/
theorem jacobiLetterTheta_n_ne_zero_of_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiLetterTheta .n (jacobiThetaArgument u k) (jacobiTau k) ≠ 0 := by
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  have hτ := jacobiTau_im_pos hk
  have hK := completeEllipticK_ofReal (k := k) (by nlinarith)
  have hKpos : 0 < Real.completeEllipticKOfParameter (k ^ 2) :=
      Real.completeEllipticKOfParameter_pos (by nlinarith)
  have hz : jacobiThetaArgument u k =
      ((u / (2 * Real.completeEllipticKOfParameter (k ^ 2)) : ℝ) : ℂ) * π := by
    rw [jacobiThetaArgument, hK]; push_cast; field_simp
  rw [hz, jacobiLetterTheta]
  exact div_ne_zero (jacobiThetaTau_real_mul_pi_ne_zero hτ _).1
      (by simpa using (jacobiThetaTau_real_mul_pi_ne_zero hτ 0).1)

open Set in
/-- Joint real-line identification of the complex and real `sn, cn, dn` (ODE uniqueness). -/
private lemma jacobiSn_cnk_dnk_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiSn u k = (Real.jacobiSnOfParameter u (k ^ 2) : ℂ) ∧
      jacobiCn u k = (Real.jacobiCnOfParameter u (k ^ 2) : ℂ) ∧
      jacobiDn u k = (Real.jacobiDnOfParameter u (k ^ 2) : ℂ) := by
  have hk := ofReal_mem_jacobiModulusDomain hk0 hk1
  have hm : k ^ 2 < 1 := by nlinarith
  set f : ℝ → ℂ × ℂ × ℂ := fun t => (jacobiSn t k, jacobiCn t k, jacobiDn t k) with hf
  set g : ℝ → ℂ × ℂ × ℂ := fun t =>
    ((Real.jacobiSnOfParameter t (k ^ 2) : ℂ), (Real.jacobiCnOfParameter t (k ^ 2) : ℂ),
      (Real.jacobiDnOfParameter t (k ^ 2) : ℂ)) with hg
  set v : ℝ → ℂ × ℂ × ℂ → ℂ × ℂ × ℂ := fun _ x =>
    (x.2.1 * x.2.2, -(x.1 * x.2.2), -((k : ℂ) ^ 2 * x.1 * x.2.1)) with hv
  have hf' : ∀ t : ℝ, HasDerivAt f (v t (f t)) t := fun t => by
    have hz := jacobiLetterTheta_n_ne_zero_of_real hk0 hk1 t
    exact ((hasDerivAt_jacobiSn hk hz).comp_ofReal).prodMk
      (((hasDerivAt_jacobiCn hk hz).comp_ofReal).prodMk
        ((hasDerivAt_jacobiDn hk hz).comp_ofReal))
  have hg' : ∀ t : ℝ, HasDerivAt g (v t (g t)) t := fun t => by
    have h1 := (Real.hasDerivAt_jacobiSnOfParameter hm t).ofReal_comp
    have h2 := (Real.hasDerivAt_jacobiCnOfParameter hm t).ofReal_comp
    have h3 := (Real.hasDerivAt_jacobiDnOfParameter hm t).ofReal_comp
    refine (HasDerivAt.prodMk h1 (HasDerivAt.prodMk h2 h3)).congr_deriv ?_
    simp only [hv, hg]; push_cast; rfl
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf' t).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg' t).continuousAt
  set a : ℝ := -(|u| + 1)
  set b : ℝ := |u| + 1
  obtain ⟨Rf, hRf⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hfc.continuousOn
  obtain ⟨Rg, hRg⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hgc.continuousOn
  set R := max Rf Rg
  have hvL : LocallyLipschitz (v 0) := by
    apply ContDiff.locallyLipschitz (𝕂 := ℝ)
    simp only [hv]; fun_prop
  obtain ⟨L, hL⟩ := (hvL.locallyLipschitzOn
      (s := Metric.closedBall 0 R)).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall 0 R)
  have h0 : f 0 = g 0 := by
    simp only [hf, hg, ofReal_zero, jacobiSn_zero hk, jacobiCn_zero hk, jacobiDn_zero hk,
      Real.jacobiSnOfParameter, Real.jacobiCnOfParameter, Real.jacobiDnOfParameter,
          Real.jacobiAmOfParameter_zero hm]
    norm_num
  have hu : u ∈ Ioo a b := ⟨by simp only [a]; linarith [neg_abs_le u], by
    simp only [b]; linarith [le_abs_self u]⟩
  have key := ODE_solution_unique_of_mem_Ioo (v := v) (s := fun _ => Metric.closedBall 0 R)
    (K := L) (a := a) (b := b) (t₀ := 0) (fun t _ => hL)
    ⟨by simp only [a]; linarith [abs_nonneg u], by simp only [b]; linarith [abs_nonneg u]⟩
    (fun t ht => ⟨hf' t, mem_closedBall_zero_iff.mpr ((hRf t (Ioo_subset_Icc_self ht)).trans
      (le_max_left _ _))⟩)
    (fun t ht => ⟨hg' t, mem_closedBall_zero_iff.mpr ((hRg t (Ioo_subset_Icc_self ht)).trans
      (le_max_right _ _))⟩) h0 hu
  simp only [hf, hg, Prod.mk.injEq] at key
  exact key

/-- Bridge to the real-variable `sn` (defined through the amplitude):
for `0 < k < 1` and real `u`, `sn(u, k) = Real.jacobiSnOfParameter u (k²)`. -/
@[dlmf 22.2.E4 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiSn_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiSn u k = (Real.jacobiSnOfParameter u (k ^ 2) : ℂ) :=
  (jacobiSn_cnk_dnk_ofReal hk0 hk1 u).1

/-- Bridge to the real-variable `cn`: for `0 < k < 1` and real `u`,
`cn(u, k) = Real.jacobiCnOfParameter u (k²)`. -/
@[dlmf 22.2.E5 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiCn_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiCn u k = (Real.jacobiCnOfParameter u (k ^ 2) : ℂ) :=
  (jacobiSn_cnk_dnk_ofReal hk0 hk1 u).2.1

/-- Bridge to the real-variable `dn`: for `0 < k < 1` and real `u`,
`dn(u, k) = Real.jacobiDnOfParameter u (k²)`. -/
@[dlmf 22.2.E6 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiDn_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiDn u k = (Real.jacobiDnOfParameter u (k ^ 2) : ℂ) :=
  (jacobiSn_cnk_dnk_ofReal hk0 hk1 u).2.2

/-- Estimate under the stated parameter and domain assumptions: `0 < (w ^ (1 / 2 : ℂ)).re`. -/
private lemma re_cpow_one_half_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w ^ (1 / 2 : ℂ)).re :=
  Carlson.re_cpow_half_pos (Or.inl hw)

/-- Estimate under the stated parameter and domain assumptions: `0 < (w ^ (-(1 / 2) : ℂ)).re`. -/
private lemma re_cpow_neg_one_half_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w ^ (-(1 / 2) : ℂ)).re := by
  rw [cpow_neg, inv_re]
  have h := re_cpow_one_half_pos hw
  exact div_pos h (normSq_pos.mpr fun h0 => by rw [h0] at h; simp at h)

/-- Estimate under the stated parameter and domain assumptions: `0 < (a / (1 + a)).re`. -/
private lemma re_div_one_add_pos {a : ℂ} (ha : 0 < a.re) : 0 < (a / (1 + a)).re := by
  have h1 : (1 + a) ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  rw [div_re]
  have hn : 0 < normSq (1 + a) := normSq_pos.mpr h1
  have : a.re * (1 + a).re / normSq (1 + a) + a.im * (1 + a).im / normSq (1 + a) =
      (a.re * (1 + a.re) + a.im * a.im) / normSq (1 + a) := by
    simp only [add_re, one_re, add_im, one_im, zero_add]; ring
  rw [this]
  exact div_pos (by nlinarith [mul_self_nonneg a.im]) hn

/-- Identity under the stated parameter and domain assumptions: `(w ^ (-(1 / 2) : ℂ)) ^ 2 = w⁻¹`. -/
private lemma cpow_neg_one_half_sq (w : ℂ) : (w ^ (-(1 / 2) : ℂ)) ^ 2 = w⁻¹ := by
  rw [cpow_neg, inv_pow, Carlson.cpow_half_sq]

/-- Estimate under the stated parameter and domain assumptions: `0 < (jacobiComodulus k).re`. -/
private lemma re_jacobiComodulus_pos {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    0 < (jacobiComodulus k).re := (jacobiComodulus_mem_jacobiModulusDomain hk).1

/-- Differentiability at the specified argument: `DifferentiableAt ℂ jacobiComodulus k`. -/
private lemma differentiableAt_jacobiComodulus {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    DifferentiableAt ℂ jacobiComodulus k := by
  have hk' := hk
  rw [jacobiModulusDomain_eq] at hk'
  exact (by fun_prop : DifferentiableAt ℂ (fun k : ℂ => 1 - k ^ 2) k).cpow_const hk'.2

/-- Square-root branch selection by the identity theorem. -/
private lemma eqOn_of_sq_eq_of_re_pos {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f jacobiModulusDomain)
    (hg : DifferentiableOn ℂ g jacobiModulusDomain)
    (hsq : ∀ x : ℝ, 0 < x → x < 1 → f x ^ 2 = g x ^ 2)
    (hfr : ∀ x : ℝ, 0 < x → x < 1 → 0 < (f x).re)
    (hgr : ∀ x : ℝ, 0 < x → x < 1 → 0 < (g x).re) : Set.EqOn f g jacobiModulusDomain := by
  refine eqOn_jacobiModulusDomain_of_real hf hg fun x h0 h1 => ?_
  have h : (f x - g x) * (f x + g x) = 0 := by linear_combination hsq x h0 h1
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg re h
    simp only [add_re, zero_re] at this
    linarith [hfr x h0 h1, hgr x h0 h1]

/-- Composition of Glaisher's quotient at a constant real theta argument with `τ(k)`. -/
private lemma differentiableOn_jacobiGlaisher_comp_jacobiTau (p q : JacobiLetter) (c : ℂ)
    (hq : ∀ τ : ℂ, 0 < τ.im → jacobiLetterTheta q c τ ≠ 0) :
    DifferentiableOn ℂ (fun k => jacobiGlaisher p q c (jacobiTau k)) jacobiModulusDomain := by
  refine differentiableOn_comp_jacobiTau fun τ hτ => ?_
  have hl : ∀ r : JacobiLetter, DifferentiableAt ℂ (fun σ => jacobiLetterTheta r c σ) τ :=
    fun r => (differentiableAt_jacobiLetterTheta_uncurry r (x := (c, τ)) hτ).comp τ
      (f := fun σ : ℂ => (c, σ)) (by fun_prop)
  unfold jacobiGlaisher
  by_cases hpq : p = q
  · simp only [hpq, ↓reduceIte]; exact differentiableAt_const _
  · simp only [hpq, ↓reduceIte]; exact (hl p).div (hl q) (hq τ hτ)

/-- Identity under the stated parameter and domain assumptions:
`jacobiThetaArgument (completeEllipticK k / 2) k = ((1 / 4 : ℝ) : ℂ) * π`. -/
private lemma jacobiThetaArgument_completeEllipticK_div_two {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiThetaArgument (completeEllipticK k / 2) k = ((1 / 4 : ℝ) : ℂ) * π := by
  have := completeEllipticK_ne_zero hk
  rw [jacobiThetaArgument]; push_cast; field_simp; ring

/-- Nonvanishing under the stated hypotheses: `jacobiLetterTheta r (((1 / 4 : ℝ) : ℂ) * π) τ ≠ 0`.
-/
private lemma jacobiLetterTheta_pi_div_four_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (r : JacobiLetter) :
    jacobiLetterTheta r (((1 / 4 : ℝ) : ℂ) * π) τ ≠ 0 := by
  obtain ⟨h4, h3, h1⟩ := jacobiThetaTau_real_mul_pi_ne_zero hτ (1 / 4)
  have n2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have n3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have n4 := jacobiThetaFourTau_zero_ne_zero hτ
  have hnz : ∀ m : ℤ, (1 / 4 : ℝ) ≠ m := by
    intro m hm
    have h1 : (0 : ℝ) < m := by rw [← hm]; norm_num
    have h2 : (m : ℝ) < 1 := by rw [← hm]; norm_num
    have : (0 : ℤ) < m := by exact_mod_cast h1
    have : m < 1 := by exact_mod_cast h2
    omega
  have hnz' : ∀ m : ℤ, (-(1 / 4) : ℝ) ≠ m := by
    intro m hm
    have h1 : (-1 : ℝ) < m := by rw [← hm]; norm_num
    have h2 : (m : ℝ) < 0 := by rw [← hm]; norm_num
    have : (-1 : ℤ) < m := by exact_mod_cast h1
    have : m < 0 := by exact_mod_cast h2
    omega
  cases r <;> simp only [jacobiLetterTheta]
  · exact mul_ne_zero (div_ne_zero n3 (mul_ne_zero n2 n4)) (h1 hnz)
  · refine div_ne_zero ?_ n2
    have h := (jacobiThetaTau_real_mul_pi_ne_zero hτ (-(1 / 4))).2.2 hnz'
    have e : jacobiThetaOneTau (((-(1 / 4) : ℝ) : ℂ) * π) τ =
        -jacobiThetaTwoTau (((1 / 4 : ℝ) : ℂ) * π) τ := by
      rw [jacobiThetaOneTau]; congr 2; push_cast; ring
    rw [e] at h; exact fun h' => h (by rw [h', neg_zero])
  · exact div_ne_zero h3 n3
  · exact div_ne_zero h4 n4

/-- Identity under the stated parameter and domain assumptions: `StrictMono fun u =>
Real.jacobiAmOfParameter u m`. -/
theorem strictMono_jacobiAmOfParameter {m : ℝ} (hm : m < 1) : StrictMono fun u =>
    Real.jacobiAmOfParameter u m := by
  simp only [Real.jacobiAmOfParameter, hm, ↓reduceDIte]
  exact (Real.incompleteEllipticFOfParameterOrderIso hm).symm.strictMono

/-- The values at `K/2` up to the choice of square roots. -/
private lemma jacobi_completeEllipticK_div_two_relations {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiDn (completeEllipticK k / 2) k ^ 2 = jacobiComodulus k ∧
      jacobiSn (completeEllipticK k / 2) k ^ 2 * (1 + jacobiComodulus k) = 1 ∧
      jacobiCn (completeEllipticK k / 2) k =
        jacobiSn (completeEllipticK k / 2) k * jacobiDn (completeEllipticK k / 2) k := by
  have hτ := jacobiTau_im_pos hk
  set u := completeEllipticK k / 2 with hu
  have hreg : ∀ r, IsJacobiRegular r u k := fun r => by
    unfold IsJacobiRegular; rw [hu, jacobiThetaArgument_completeEllipticK_div_two hk];
        exact jacobiLetterTheta_pi_div_four_ne_zero hτ r
  have hd : jacobiDn u k ≠ 0 := jacobiPQ_ne_zero (by decide) (hreg .d) (hreg .n)
  have hm : -u + completeEllipticK k = u := by rw [hu]; ring
  have e1 := (jacobiSn_shift hk (-u)).1
  have e3 := (jacobiDn_shift hk (-u)).1
  rw [hm] at e1 e3
  rw [jacobiCd, jacobiPQ_neg, ← jacobiCd] at e1
  rw [jacobiNd, jacobiPQ_neg, ← jacobiNd] at e3
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, decide_true, not_true_eq_false,
    ↓reduceIte, Bool.not_eq_true, eq_self_iff_true] at e1 e3
  obtain ⟨-, -, -, -, -, -, hsd, hcd, hnd⟩ := jacobiPQ_eq_div_of_regular_n (hreg .n)
  rw [hcd] at e1; rw [hnd] at e3
  obtain ⟨hsc, -⟩ := jacobi_sq_sum hk (hreg .n)
  have hdd : jacobiDn u k ^ 2 = jacobiComodulus k := by
    field_simp at e3; linear_combination e3
  refine ⟨hdd, ?_, ?_⟩
  · field_simp at e1
    have hc : jacobiCn u k = jacobiSn u k * jacobiDn u k := by linear_combination -e1
    rw [hc] at hsc
    linear_combination hsc - jacobiSn u k ^ 2 * hdd
  · field_simp at e1; linear_combination -e1

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = K/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSn (completeEllipticK k / 2) k = (1 + jacobiComodulus k) ^ (-(1 / 2) : ℂ) ∧
      jacobiCn (completeEllipticK k / 2) k = (jacobiComodulus k / (1 + jacobiComodulus k)) ^
          (1 / 2 : ℂ) ∧
      jacobiDn (completeEllipticK k / 2) k = jacobiComodulus k ^ (1 / 2 : ℂ) := by
  -- holomorphy of the three left-hand sides
  have hL : ∀ p q : JacobiLetter, q ≠ .s → DifferentiableOn ℂ
      (fun k => jacobiPQ p q (completeEllipticK k / 2) k) jacobiModulusDomain := by
    intro p q _
    refine (differentiableOn_jacobiGlaisher_comp_jacobiTau p q _
      fun τ hτ => jacobiLetterTheta_pi_div_four_ne_zero hτ q).congr fun k hk => ?_
    simp only [jacobiPQ, jacobiThetaArgument_completeEllipticK_div_two hk]
  have hkd : DifferentiableOn ℂ jacobiComodulus jacobiModulusDomain := fun k hk =>
    (differentiableAt_jacobiComodulus hk).differentiableWithinAt
  have hslit : ∀ {w : ℂ}, 0 < w.re → w ∈ slitPlane := fun h => Or.inl h
  have h1re : ∀ k ∈ jacobiModulusDomain, 0 < (1 + jacobiComodulus k).re := fun k hk => by
    simp only [add_re, one_re]; linarith [re_jacobiComodulus_pos hk]
  -- real positivity of the left-hand sides
  have hreal : ∀ x : ℝ, 0 < x → x < 1 → ∀ p : JacobiLetter, p ≠ .s → ∀ q : JacobiLetter,
      jacobiPQ q .n (completeEllipticK x / 2) x = jacobiPQ q .n
        ((Real.completeEllipticKOfParameter (x ^ 2) / 2 : ℝ) : ℂ) x := by
    intro x h0 h1 _ _ q
    rw [completeEllipticK_ofReal (by nlinarith)]; push_cast; rfl
  have hm : ∀ x : ℝ, 0 < x → x < 1 → x ^ 2 < 1 := fun x h0 h1 => by nlinarith
  have hamm : ∀ x : ℝ, 0 < x → x < 1 →
      0 < Real.jacobiAmOfParameter (Real.completeEllipticKOfParameter (x ^ 2) / 2) (x ^ 2) ∧
        Real.jacobiAmOfParameter (Real.completeEllipticKOfParameter (x ^ 2) / 2)
            (x ^ 2) < π / 2 := by
    intro x h0 h1
    have hK := Real.completeEllipticKOfParameter_pos (hm x h0 h1)
    have a := strictMono_jacobiAmOfParameter (hm x h0 h1)
        (show 0 < Real.completeEllipticKOfParameter (x ^ 2) / 2 by
      positivity)
    have b := strictMono_jacobiAmOfParameter (hm x h0 h1)
      (show Real.completeEllipticKOfParameter (x ^ 2) / 2 <
          Real.completeEllipticKOfParameter (x ^ 2) by linarith)
    simp only [Real.jacobiAmOfParameter_zero (hm x h0 h1),
        Real.jacobiAmOfParameter_completeEllipticKOfParameter (hm x h0 h1)] at a b
    exact ⟨a, b⟩
  refine ⟨?_, ?_, ?_⟩
  · refine eqOn_of_sq_eq_of_re_pos (f := fun k => jacobiSn (completeEllipticK k / 2) k)
      (g := fun k => (1 + jacobiComodulus k) ^ (-(1 / 2) : ℂ)) (hL .s .n (by decide))
      ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · intro k hk
      exact ((hkd k hk).const_add 1).cpow_const (hslit (h1re k hk))
        |>.differentiableAt (isOpen_jacobiModulusDomain.mem_nhds hk) |>.differentiableWithinAt
    · have h := (jacobi_completeEllipticK_div_two_relations
          (ofReal_mem_jacobiModulusDomain h0 h1)).2.1
      have hne : (1 + jacobiComodulus x) ≠ 0 := fun h' => by
        have := h1re x (ofReal_mem_jacobiModulusDomain h0 h1); rw [h'] at this; simp at this
      rw [cpow_neg_one_half_sq]
      field_simp
      linear_combination h
    · simp only [jacobiSn]
      rw [hreal x h0 h1 .c (by decide) .s, ← jacobiSn, jacobiSn_ofReal h0 h1, ofReal_re,
        Real.jacobiSnOfParameter]
      exact Real.sin_pos_of_pos_of_lt_pi (hamm x h0 h1).1 (by linarith [(hamm x h0 h1).2,
        Real.pi_pos])
    · exact re_cpow_neg_one_half_pos (h1re x (ofReal_mem_jacobiModulusDomain h0 h1))
  · have hne : ∀ k ∈ jacobiModulusDomain, (1 + jacobiComodulus k) ≠ 0 := fun k hk h' => by
      have := h1re k hk; rw [h'] at this; simp at this
    refine eqOn_of_sq_eq_of_re_pos (f := fun k => jacobiCn (completeEllipticK k / 2) k)
      (g := fun k => (jacobiComodulus k / (1 + jacobiComodulus k)) ^ (1 / 2 : ℂ))
      (hL .c .n (by decide)) ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · intro k hk
      exact ((hkd k hk).div ((hkd k hk).const_add 1) (hne k hk)).cpow_const
        (hslit (re_div_one_add_pos (re_jacobiComodulus_pos hk)))
        |>.differentiableAt (isOpen_jacobiModulusDomain.mem_nhds hk) |>.differentiableWithinAt
    · obtain ⟨hd, hs, hc⟩ :=
          jacobi_completeEllipticK_div_two_relations (ofReal_mem_jacobiModulusDomain h0 h1)
      have hn := hne x (ofReal_mem_jacobiModulusDomain h0 h1)
      rw [Carlson.cpow_half_sq, hc, mul_pow, hd]
      field_simp
      linear_combination jacobiComodulus x * hs
    · simp only [jacobiCn]
      rw [hreal x h0 h1 .c (by decide) .c, ← jacobiCn, jacobiCn_ofReal h0 h1, ofReal_re,
        Real.jacobiCnOfParameter]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [(hamm x h0 h1).1, Real.pi_pos],
        (hamm x h0 h1).2⟩
    · exact re_cpow_one_half_pos (re_div_one_add_pos
        (re_jacobiComodulus_pos (ofReal_mem_jacobiModulusDomain h0 h1)))
  · refine eqOn_of_sq_eq_of_re_pos (f := fun k => jacobiDn (completeEllipticK k / 2) k)
      (g := fun k => jacobiComodulus k ^ (1 / 2 : ℂ))
      (hL .d .n (by decide)) ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · intro k hk
      exact (hkd k hk).cpow_const (hslit (re_jacobiComodulus_pos hk))
        |>.differentiableAt (isOpen_jacobiModulusDomain.mem_nhds hk) |>.differentiableWithinAt
    · rw [Carlson.cpow_half_sq];
          exact (jacobi_completeEllipticK_div_two_relations
              (ofReal_mem_jacobiModulusDomain h0 h1)).1
    · simp only [jacobiDn]
      rw [hreal x h0 h1 .c (by decide) .d, ← jacobiDn, jacobiDn_ofReal h0 h1, ofReal_re]
      exact Real.jacobiDnOfParameter_pos (hm x h0 h1) _
    · exact re_cpow_one_half_pos (re_jacobiComodulus_pos (ofReal_mem_jacobiModulusDomain h0 h1))

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = 3K/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSn (3 * completeEllipticK k / 2) k = (1 + jacobiComodulus k) ^ (-(1 / 2) : ℂ) ∧
      jacobiCn (3 * completeEllipticK k / 2) k = -(jacobiComodulus k / (1 + jacobiComodulus k)) ^
          (1 / 2 : ℂ) ∧
      jacobiDn (3 * completeEllipticK k / 2) k = jacobiComodulus k ^ (1 / 2 : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := jacobi_specialValues_HalfK hk
  have e : 3 * completeEllipticK k / 2 = -(completeEllipticK k / 2) + 2 *
      completeEllipticK k := by ring
  rw [e, (jacobiSn_shift hk _).2.2.2.1, (jacobiCn_shift hk _).2.2.2.1,
    (jacobiDn_shift hk _).2.2.2.1, jacobiSn, jacobiCn, jacobiDn, jacobiPQ_neg,
    jacobiPQ_neg, jacobiPQ_neg, ← jacobiSn, ← jacobiCn, ← jacobiDn, h1, h2, h3]
  simp

/-- `|Im a| < Re a` (argument in `(-π/4, π/4)`). -/
def AbsImLtRe (a : ℂ) : Prop := |a.im| < a.re

/-- The stated relation follows from the given hypotheses: `AbsImLtRe (w ^ (1 / 2 : ℂ))`. -/
private lemma abs_im_lt_re_cpow_one_half {w : ℂ} (hw : 0 < w.re) : AbsImLtRe (w ^ (1 / 2 : ℂ)) := by
  have h := Carlson.cpow_half_sq w
  have hr := re_cpow_one_half_pos hw
  set a := w ^ (1 / 2 : ℂ)
  have : w.re = a.re ^ 2 - a.im ^ 2 := by rw [← h]; simp [pow_two]
  unfold AbsImLtRe
  rw [abs_lt]; constructor <;> nlinarith

/-- The stated relation follows from the given hypotheses: `AbsImLtRe a⁻¹`. -/
private lemma abs_im_lt_re_inv {a : ℂ} (ha : AbsImLtRe a) : AbsImLtRe a⁻¹ := by
  unfold AbsImLtRe at *
  have h0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hn := normSq_pos.mpr h0
  rw [inv_re, inv_im, neg_div, abs_neg, abs_div, abs_of_pos hn]
  exact div_lt_div_of_pos_right ha hn

/-- Estimate under the stated parameter and domain assumptions: `0 < a.re`. -/
private lemma re_pos_of_abs_im_lt_re {a : ℂ} (ha : AbsImLtRe a) : 0 < a.re :=
  lt_of_le_of_lt (abs_nonneg _) ha

/-- Estimate under the stated parameter and domain assumptions: `0 < (a * b).re`. -/
private lemma re_mul_pos_of_abs_im_lt_re {a b : ℂ} (ha : AbsImLtRe a) (hb : AbsImLtRe b) : 0 <
    (a * b).re := by
  unfold AbsImLtRe at ha hb
  rw [mul_re]
  have := abs_mul a.im b.im
  have h1 : a.im * b.im ≤ |a.im| * |b.im| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : |a.im| * |b.im| < a.re * b.re := mul_lt_mul'' ha hb (abs_nonneg _) (abs_nonneg _)
  linarith

/-- Uniqueness of a square root with positive real part. -/
private lemma eq_of_sq_eq_of_re_pos {a b : ℂ} (h : a ^ 2 = b ^ 2) (ha : 0 < a.re) (hb : 0 < b.re) :
    a = b := by
  have h' : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h' | h'
  · exact sub_eq_zero.mp h'
  · have := congrArg re h'; simp only [add_re, zero_re] at this; linarith

/-- Identity under the stated parameter and domain assumptions: `jacobiComodulus
(jacobiComodulus k) = k`. -/
private lemma jacobiComodulus_jacobiComodulus {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiComodulus (jacobiComodulus k) = k := by
  have hsl : k ^ 2 ∈ slitPlane := by
    rcases sq_im_ne_zero_or_mem_Ioo_of_mem_jacobiModulusDomain hk with h | ⟨-, h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  rw [jacobiComodulus, jacobiComodulus_sq, sub_sub_cancel]
  exact eq_of_sq_eq_of_re_pos (Carlson.cpow_half_sq _) (Carlson.re_cpow_half_pos hsl) hk.1

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = iK'/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSn (I * completeEllipticKPrime k / 2) k = I * k ^ (-(1 / 2) : ℂ) ∧
      jacobiCn (I * completeEllipticKPrime k / 2) k = (1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ) ∧
      jacobiDn (I * completeEllipticKPrime k / 2) k = (1 + k) ^ (1 / 2 : ℂ) := by
  have hk' := jacobiComodulus_mem_jacobiModulusDomain hk
  have hkk := jacobiComodulus_jacobiComodulus hk
  obtain ⟨s1, c1, d1⟩ := jacobi_specialValues_HalfK hk'
  rw [hkk] at s1 c1 d1
  have hτ' := jacobiTau_im_pos hk'
  have hreg : IsJacobiRegular .n (completeEllipticK (jacobiComodulus k) / 2)
      (jacobiComodulus k) := by
    unfold IsJacobiRegular; rw [jacobiThetaArgument_completeEllipticK_div_two hk'];
        exact jacobiLetterTheta_pi_div_four_ne_zero hτ' _
  obtain ⟨-, -, -, hsc, hdc, hnc, -, -, -⟩ := jacobiPQ_eq_div_of_regular_n hreg
  obtain ⟨t1, t2, t3, -⟩ := jacobi_imaginary_transformation hk
    (completeEllipticK (jacobiComodulus k) / 2)
  have e : I * completeEllipticKPrime k / 2 = I * (completeEllipticK (jacobiComodulus k) / 2) := by
    rw [completeEllipticK_jacobiComodulus_eq_completeEllipticKPrime]; ring
  rw [e, t1, t2, t3, hsc, hdc, hnc, s1, c1, d1]
  have hk0 : k ≠ 0 := fun h => by have := hk.1; rw [h] at this; simp at this
  have hre1 : 0 < (1 + k).re := by simp only [add_re, one_re]; linarith [hk.1]
  have h1k : 1 + k ≠ 0 := fun h => by rw [h] at hre1; simp at hre1
  have hq := re_div_one_add_pos hk.1
  have gS : AbsImLtRe ((1 + k) ^ (-(1 / 2) : ℂ)) := by
    rw [cpow_neg]; exact abs_im_lt_re_inv (abs_im_lt_re_cpow_one_half hre1)
  have gC := abs_im_lt_re_cpow_one_half hq
  have gCi := abs_im_lt_re_inv gC
  have gK : AbsImLtRe (k ^ (-(1 / 2) : ℂ)) := by
    rw [cpow_neg]; exact abs_im_lt_re_inv (abs_im_lt_re_cpow_one_half hk.1)
  refine ⟨?_, ?_, ?_⟩
  · congr 1
    refine eq_of_sq_eq_of_re_pos ?_
        (by rw [div_eq_mul_inv]; exact re_mul_pos_of_abs_im_lt_re gS gCi)
      (re_pos_of_abs_im_lt_re gK)
    rw [div_pow, cpow_neg_one_half_sq, Carlson.cpow_half_sq, cpow_neg_one_half_sq]
    field_simp
  · refine eq_of_sq_eq_of_re_pos ?_ (by rw [one_div]; exact re_pos_of_abs_im_lt_re gCi)
      (re_mul_pos_of_abs_im_lt_re (abs_im_lt_re_cpow_one_half hre1) gK)
    rw [div_pow, mul_pow, cpow_neg_one_half_sq, Carlson.cpow_half_sq, Carlson.cpow_half_sq]
    field_simp
  · have hr : 0 < (k ^ (1 / 2 : ℂ) / (k / (1 + k)) ^ (1 / 2 : ℂ)).re := by
      rw [div_eq_mul_inv]; exact re_mul_pos_of_abs_im_lt_re (abs_im_lt_re_cpow_one_half hk.1) gCi
    refine eq_of_sq_eq_of_re_pos ?_ hr (re_cpow_one_half_pos hre1)
    rw [div_pow, Carlson.cpow_half_sq, Carlson.cpow_half_sq, Carlson.cpow_half_sq]
    field_simp

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = 3iK'/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSn (3 * (I * completeEllipticKPrime k) / 2) k = -(I * k ^ (-(1 / 2) : ℂ)) ∧
      jacobiCn (3 * (I * completeEllipticKPrime k) / 2) k =
          -((1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ)) ∧
      jacobiDn (3 * (I * completeEllipticKPrime k) / 2) k = -(1 + k) ^ (1 / 2 : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := jacobi_specialValues_HalfKp hk
  have e : 3 * (I * completeEllipticKPrime k) / 2 = -(I * completeEllipticKPrime k / 2) +
      2 * (I * completeEllipticKPrime k) := by ring
  rw [e, (jacobiSn_shift hk _).2.2.2.2.2, (jacobiCn_shift hk _).2.2.2.2.2,
    (jacobiDn_shift hk _).2.2.2.2.2, jacobiSn, jacobiCn, jacobiDn, jacobiPQ_neg,
    jacobiPQ_neg, jacobiPQ_neg, ← jacobiSn, ← jacobiCn, ← jacobiDn, h1, h2, h3]
  simp

/-- Nonvanishing under the stated hypotheses: `jacobiThetaFourTau (((a : ℂ) + b * τ) * π) τ ≠ 0`. -/
private lemma jacobiThetaFourTau_ne_zero_of_ne_half {τ : ℂ} (hτ : 0 < τ.im) (a b : ℝ)
    (hb : ∀ n : ℤ, b ≠ n + 1 / 2) :
    jacobiThetaFourTau (((a : ℂ) + b * τ) * π) τ ≠ 0 := by
  rw [Ne, (DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ _).2.2.2]
  rintro ⟨m, n, h⟩
  have h' : ((a - m : ℝ) : ℂ) + ((b - (n + 1 / 2) : ℝ) : ℂ) * τ = 0 := by
    have := mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) h
    push_cast; linear_combination this
  have := DLMF.Theta.eq_zero_of_lattice_point_eq_zero hτ (a := a - m) (b := b - (n + 1 / 2))
    (by rw [h', zero_mul])
  exact hb n (by linarith [this.2])

/-- The stated relation follows from the given hypotheses:
`IsJacobiRegular .n (I * completeEllipticKPrime k / 2) k`. -/
private lemma isJacobiRegular_n_I_mul_completeEllipticKPrime_div_two {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) :
    IsJacobiRegular .n (I * completeEllipticKPrime k / 2) k := by
  have hτ := jacobiTau_im_pos hk
  have hK := completeEllipticK_ne_zero hk
  unfold IsJacobiRegular
  have hz : jacobiThetaArgument (I * completeEllipticKPrime k / 2) k =
      (((0 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * jacobiTau k) * π := by
    rw [jacobiThetaArgument, jacobiTau]; push_cast; field_simp; ring
  rw [hz, jacobiLetterTheta]
  refine div_ne_zero (jacobiThetaFourTau_ne_zero_of_ne_half hτ 0 (1 / 4) fun n h => ?_)
    (jacobiThetaFourTau_zero_ne_zero hτ)
  have h1 : (4 * n + 1 : ℝ) = 0 := by linarith
  have h2 : (4 * n + 1 : ℤ) = 0 := by exact_mod_cast h1
  omega

/-- The stated relation follows from the given hypotheses:
`IsJacobiRegular r (completeEllipticK k / 2) k`. -/
private lemma isJacobiRegular_completeEllipticK_div_two {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    (r : JacobiLetter) :
    IsJacobiRegular r (completeEllipticK k / 2) k := by
  unfold IsJacobiRegular; rw [jacobiThetaArgument_completeEllipticK_div_two hk]
  exact jacobiLetterTheta_pi_div_four_ne_zero (jacobiTau_im_pos hk) r

/-- `k + k' ≠ -1`, so `1 + k + k' ≠ 0`. -/
private lemma one_add_add_jacobiComodulus_ne_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    1 + k + jacobiComodulus k ≠ 0 := fun h => by
  have := congrArg re h
  simp only [add_re, one_re, zero_re] at this
  linarith [hk.1, re_jacobiComodulus_pos hk]

/-- Positive reals. -/
def IsPosReal (a : ℂ) : Prop := a.im = 0 ∧ 0 < a.re

/-- The stated relation follows from the given hypotheses: `IsPosReal (a * b)`. -/
private lemma isPosReal_mul {a b : ℂ} (ha : IsPosReal a) (hb : IsPosReal b) :
    IsPosReal (a * b) := by
  unfold IsPosReal at *; simp [mul_re, mul_im, ha.1, hb.1, mul_pos ha.2 hb.2]

/-- The stated relation follows from the given hypotheses: `IsPosReal (a + b)`. -/
private lemma isPosReal_add {a b : ℂ} (ha : IsPosReal a) (hb : IsPosReal b) :
    IsPosReal (a + b) := by
  unfold IsPosReal at *; simp [ha.1, hb.1]; linarith [ha.2, hb.2]

/-- The stated relation follows from the given hypotheses: `IsPosReal a⁻¹`. -/
private lemma isPosReal_inv {a : ℂ} (ha : IsPosReal a) : IsPosReal a⁻¹ := by
  unfold IsPosReal at *
  have h0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  refine ⟨by simp [inv_im, ha.1], ?_⟩
  rw [inv_re]; exact div_pos ha.2 (normSq_pos.mpr h0)

/-- The stated relation follows from the given hypotheses: `IsPosReal (a / b)`. -/
private lemma isPosReal_div {a b : ℂ} (ha : IsPosReal a) (hb : IsPosReal b) :
    IsPosReal (a / b) := by
  rw [div_eq_mul_inv]; exact isPosReal_mul ha (isPosReal_inv hb)

/-- The stated relation follows from the given hypotheses: `IsPosReal (a ^ (c : ℂ))`. -/
private lemma isPosReal_cpow_ofReal {a : ℂ} (ha : IsPosReal a) (c : ℝ) : IsPosReal
    (a ^ (c : ℂ)) := by
  have e : a = (a.re : ℂ) := by apply Complex.ext <;> simp [ha.1]
  rw [e, ← ofReal_cpow ha.2.le]
  exact ⟨ofReal_im _, by rw [ofReal_re]; exact Real.rpow_pos_of_pos ha.2 _⟩

/-- The stated relation follows from the given hypotheses: `IsPosReal 1`. -/
private lemma isPosReal_one : IsPosReal 1 := ⟨by simp, by simp⟩

/-- The stated relation follows from the given hypotheses: `IsPosReal (x : ℂ)`. -/
private lemma isPosReal_ofReal {x : ℝ} (hx : 0 < x) : IsPosReal (x : ℂ) := ⟨ofReal_im _, by simpa⟩

/-- The stated relation follows from the given hypotheses: `IsPosReal (jacobiComodulus x)`. -/
private lemma isPosReal_jacobiComodulus {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    IsPosReal (jacobiComodulus x) := by
  have : (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [jacobiComodulus, this, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
  exact isPosReal_cpow_ofReal (isPosReal_ofReal (by nlinarith)) _

/-- Identity under the stated parameter and domain assumptions: `(a + I * b).re = a.re`. -/
private lemma re_add_I_mul_of_isPosReal {a b : ℂ} (hb : IsPosReal b) :
    (a + I * b).re = a.re := by
  simp [hb.1]

/-- The values at `(K + iK')/2` from the addition theorem, in terms of the half-period values. -/
private lemma jacobi_completeEllipticK_add_I_mul_completeEllipticKPrime_div_two {k : ℂ}
    (hk : k ∈ jacobiModulusDomain) :
    let κ := jacobiComodulus k
    let S := (1 + κ) ^ (-(1 / 2) : ℂ)
    let Q := k ^ (-(1 / 2) : ℂ)
    let A := (1 + k) ^ (1 / 2 : ℂ)
    let D := κ ^ (1 / 2 : ℂ)
    jacobiSn ((completeEllipticK k + I * completeEllipticKPrime k) / 2) k =
        S * Q * (1 + k) * (1 + κ) / (1 + k + κ) + I * (S * Q * κ * (1 + κ) / (1 + k + κ)) ∧
      jacobiCn ((completeEllipticK k + I * completeEllipticKPrime k) / 2) k =
        S * D * A * Q * (1 + κ) / (1 + k + κ) - I * (S * D * A * Q * (1 + κ) / (1 + k + κ)) ∧
      jacobiDn ((completeEllipticK k + I * completeEllipticKPrime k) / 2) k =
        D * A * (1 + κ) / (1 + k + κ) - I * (D * A * k / (1 + k + κ)) := by
  intro κ S Q A D
  obtain ⟨s1, -, d1⟩ := jacobi_specialValues_HalfK hk
  obtain ⟨-, -, hc1⟩ := jacobi_completeEllipticK_div_two_relations hk
  obtain ⟨s2, c2, d2⟩ := jacobi_specialValues_HalfKp hk
  have hu := isJacobiRegular_completeEllipticK_div_two hk .n
  have hv := isJacobiRegular_n_I_mul_completeEllipticKPrime_div_two hk
  have e : (completeEllipticK k + I * completeEllipticKPrime k) / 2 =
      completeEllipticK k / 2 + I * completeEllipticKPrime k / 2 := by ring
  have hk0 : k ≠ 0 := fun h => by have := hk.1; rw [h] at this; simp at this
  have hre1 : 0 < (1 + κ).re := by simp only [add_re, one_re]; linarith [re_jacobiComodulus_pos hk]
  have h1κ : 1 + κ ≠ 0 := fun h => by rw [h] at hre1; simp at hre1
  have hSS : S ^ 2 * (1 + κ) = 1 := by
    simp only [S]; rw [cpow_neg_one_half_sq]; field_simp
  have hQQ : Q ^ 2 * k = 1 := by simp only [Q]; rw [cpow_neg_one_half_sq]; field_simp
  have hAA : A ^ 2 = 1 + k := Carlson.cpow_half_sq _
  have hDD : D ^ 2 = κ := Carlson.cpow_half_sq _
  have hκκ : κ ^ 2 = 1 - k ^ 2 := jacobiComodulus_sq k
  have hI : I ^ 2 = -1 := I_sq
  have h3 := one_add_add_jacobiComodulus_ne_zero hk
  have s1' : jacobiSn (completeEllipticK k / 2) k = S := s1
  have d1' : jacobiDn (completeEllipticK k / 2) k = D := d1
  have s2' : jacobiSn (I * completeEllipticKPrime k / 2) k = I * Q := s2
  have c2' : jacobiCn (I * completeEllipticKPrime k / 2) k = A * Q := c2
  have d2' : jacobiDn (I * completeEllipticKPrime k / 2) k = A := d2
  rw [s1', d1'] at hc1
  have hden0 : (1 - k ^ 2 * S ^ 2 * (I * Q) ^ 2) * (1 + κ) = 1 + k + κ := by
    linear_combination (-k ^ 2 * Q ^ 2 * I ^ 2) * hSS - k ^ 2 * Q ^ 2 * hI + k * hQQ
  have hden : 1 - k ^ 2 * jacobiSn (completeEllipticK k / 2) k ^ 2 *
      jacobiSn (I * completeEllipticKPrime k / 2) k ^ 2 ≠ 0 := by
    rw [s1', s2']; intro h; rw [h, zero_mul] at hden0; exact h3 hden0.symm
  rw [e, jacobiSn_add hk hu hv hden, jacobiCn_add hk hu hv hden, jacobiDn_add hk hu hv hden,
    s1', d1', hc1, s2', c2', d2']
  have hd2 : 1 - k ^ 2 * S ^ 2 * (I * Q) ^ 2 = (1 + k + κ) / (1 + κ) := by
    rw [← hden0]; field_simp
  rw [hd2]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    rw [hAA, hDD]
  · field_simp
  · field_simp
    rw [div_left_inj' h3]
    linear_combination (-D * A * k ^ 2 * I * Q ^ 2) * hSS - D * A * k * I * hQQ

/-- The stated relation follows from the given hypotheses: `IsPosReal (a ^ (1 / 2 : ℂ)) ∧ IsPosReal
(a ^ (-(1 / 2) : ℂ))`. -/
private lemma isPosReal_cpow_half {a : ℂ} (ha : IsPosReal a) :
    IsPosReal (a ^ (1 / 2 : ℂ)) ∧ IsPosReal (a ^ (-(1 / 2) : ℂ)) := by
  constructor
  · rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]; exact isPosReal_cpow_ofReal ha _
  · rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring];
        exact isPosReal_cpow_ofReal ha _

/-- Real data at a real modulus `0 < x < 1`. -/
private lemma isPosReal_half_period_data {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    let κ := jacobiComodulus x
    IsPosReal (x : ℂ) ∧ IsPosReal κ ∧ IsPosReal ((1 + κ) ^ (-(1 / 2) : ℂ)) ∧
      IsPosReal ((x : ℂ) ^ (-(1 / 2) : ℂ)) ∧ IsPosReal ((1 + (x : ℂ)) ^ (1 / 2 : ℂ)) ∧
      IsPosReal (κ ^ (1 / 2 : ℂ)) ∧ IsPosReal ((1 - (x : ℂ)) ^ (1 / 2 : ℂ)) ∧
      IsPosReal ((2 * (x : ℂ)) ^ (1 / 2 : ℂ)) ∧
      (1 + (x : ℂ)) ^ (1 / 2 : ℂ) * (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = κ := by
  intro κ
  have hx := isPosReal_ofReal h0
  have hκ := isPosReal_jacobiComodulus h0 h1
  have h1x : IsPosReal (1 + (x : ℂ)) := isPosReal_add isPosReal_one hx
  have h1mx : IsPosReal (1 - (x : ℂ)) := by
    rw [show (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
    exact isPosReal_ofReal (by linarith)
  have h2x : IsPosReal (2 * (x : ℂ)) := by
    rw [show (2 * (x : ℂ)) = ((2 * x : ℝ) : ℂ) by push_cast; ring]
    exact isPosReal_ofReal (by linarith)
  refine ⟨hx, hκ, (isPosReal_cpow_half (isPosReal_add isPosReal_one hκ)).2,
      (isPosReal_cpow_half hx).2,
    (isPosReal_cpow_half h1x).1, (isPosReal_cpow_half hκ).1, (isPosReal_cpow_half h1mx).1,
    (isPosReal_cpow_half h2x).1, ?_⟩
  refine eq_of_sq_eq_of_re_pos ?_
      (isPosReal_mul (isPosReal_cpow_half h1x).1 (isPosReal_cpow_half h1mx).1).2 hκ.2
  rw [mul_pow, Carlson.cpow_half_sq, Carlson.cpow_half_sq, jacobiComodulus_sq]; ring

/-- Identity under the stated parameter and domain assumptions: `(a + I * b).re = a.re`. -/
private lemma re_add_I_mul_of_im_eq_zero {a b : ℂ} (hb : b.im = 0) : (a + I * b).re =
    a.re := by simp [hb]

/-- Identity under the stated parameter and domain assumptions: `(a - I * b).re = a.re`. -/
private lemma re_sub_I_mul_of_im_eq_zero {a b : ℂ} (hb : b.im = 0) : (a - I * b).re =
    a.re := by simp [hb]

/-- Differentiability throughout the specified domain: `DifferentiableOn ℂ (fun k => h k ^ c)
jacobiModulusDomain`. -/
private lemma differentiableOn_cpow_of_mem_slitPlane {h : ℂ → ℂ} (c : ℂ)
    (hd : ∀ k ∈ jacobiModulusDomain, DifferentiableAt ℂ h k)
    (hs : ∀ k ∈ jacobiModulusDomain, h k ∈ slitPlane) :
    DifferentiableOn ℂ (fun k => h k ^ c) jacobiModulusDomain := fun k hk =>
  ((hd k hk).cpow_const (hs k hk)).differentiableWithinAt

/-- Formula under the stated hypotheses: `1 - k ∈ slitPlane`. -/
private lemma one_sub_mem_slitPlane {k : ℂ} (hk : k ∈ jacobiModulusDomain) : 1 - k ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : k.im = 0
  · left; simp only [sub_re, one_re]; linarith [hk.2 h]
  · right; simpa using h

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = (K + iK')/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfKKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSn ((completeEllipticK k + I * completeEllipticKPrime k) / 2) k =
        ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiCn ((completeEllipticK k + I * completeEllipticKPrime k) / 2) k = (1 - I) *
          jacobiComodulus k ^
          (1 / 2 : ℂ) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiDn ((completeEllipticK k + I * completeEllipticKPrime k) / 2) k = (1 - I) / 2 *
          jacobiComodulus k ^
          (1 / 2 : ℂ) * ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) := by
  obtain ⟨e1, e2, e3⟩ := jacobi_completeEllipticK_add_I_mul_completeEllipticKPrime_div_two hk
  rw [e1, e2, e3]
  have Dom := jacobiModulusDomain
  -- differentiability of the building blocks
  have dκ : ∀ k ∈ jacobiModulusDomain, DifferentiableAt ℂ jacobiComodulus k :=
    fun k hk => differentiableAt_jacobiComodulus hk
  have slit_re : ∀ {w : ℂ}, 0 < w.re → w ∈ slitPlane := fun h => Or.inl h
  have re1κ : ∀ k ∈ jacobiModulusDomain, 0 < (1 + jacobiComodulus k).re := fun k hk => by
    simp only [add_re, one_re]; linarith [re_jacobiComodulus_pos hk]
  have re1k : ∀ k ∈ jacobiModulusDomain, 0 < (1 + k).re := fun k hk => by
    simp only [add_re, one_re]; linarith [hk.1]
  have re2k : ∀ k ∈ jacobiModulusDomain, 0 < (2 * k).re := fun k hk => by
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith [hk.1]
  have dS := differentiableOn_cpow_of_mem_slitPlane
      (h := fun k => 1 + jacobiComodulus k) (-(1 / 2))
    (fun k hk => (dκ k hk).const_add 1) fun k hk => slit_re (re1κ k hk)
  have dQ := differentiableOn_cpow_of_mem_slitPlane (h := fun k => k) (-(1 / 2))
    (fun k _ => differentiableAt_id) fun k hk => slit_re hk.1
  have dA := differentiableOn_cpow_of_mem_slitPlane (h := fun k => 1 + k) (1 / 2)
    (fun k _ => differentiableAt_id.const_add 1) fun k hk => slit_re (re1k k hk)
  have dD := differentiableOn_cpow_of_mem_slitPlane (h := jacobiComodulus) (1 / 2) dκ
    fun k hk => slit_re (re_jacobiComodulus_pos hk)
  have dB := differentiableOn_cpow_of_mem_slitPlane (h := fun k => 1 - k) (1 / 2)
    (fun k _ => (differentiableAt_const _).sub differentiableAt_id) fun k hk =>
        one_sub_mem_slitPlane hk
  have dC := differentiableOn_cpow_of_mem_slitPlane (h := fun k => 2 * k) (1 / 2)
    (fun k _ => differentiableAt_id.const_mul 2) fun k hk => slit_re (re2k k hk)
  have dK : DifferentiableOn ℂ jacobiComodulus jacobiModulusDomain :=
    fun k hk => (dκ k hk).differentiableWithinAt
  have dId : DifferentiableOn ℂ (fun k : ℂ => k) jacobiModulusDomain := differentiableOn_id
  have dN : DifferentiableOn ℂ (fun k => 1 + k + jacobiComodulus k) jacobiModulusDomain :=
    (dId.const_add 1).add dK
  have hN := fun k (hk : k ∈ jacobiModulusDomain) => one_add_add_jacobiComodulus_ne_zero hk
  have hC0 : ∀ k ∈ jacobiModulusDomain, (2 * k) ^ (1 / 2 : ℂ) ≠ 0 := fun k hk h => by
    have := re_cpow_one_half_pos (re2k k hk); rw [h] at this; simp at this
  refine ⟨?_, ?_, ?_⟩
  · refine eqOn_of_sq_eq_of_re_pos
      (f := fun k => (1 + jacobiComodulus k) ^ (-(1 / 2) : ℂ) * k ^ (-(1 / 2) : ℂ) * (1 + k) *
        (1 + jacobiComodulus k) / (1 + k + jacobiComodulus k) +
        I * ((1 + jacobiComodulus k) ^ (-(1 / 2) : ℂ) * k ^ (-(1 / 2) : ℂ) * jacobiComodulus k *
        (1 + jacobiComodulus k) / (1 + k + jacobiComodulus k)))
      (g := fun k => ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) / (2 * k) ^ (1 / 2 : ℂ))
      ?_ ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · exact ((((dS.mul dQ).mul (dId.const_add 1)).mul (dK.const_add 1)).div dN hN).add
        (((((dS.mul dQ).mul dK).mul (dK.const_add 1)).div dN hN).const_mul I)
    · exact (dA.add (dB.const_mul I)).div dC hC0
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := isPosReal_half_period_data h0 h1
      have hN0 := hN x (ofReal_mem_jacobiModulusDomain h0 h1)
      have hC00 := hC0 x (ofReal_mem_jacobiModulusDomain h0 h1)
      have hSS : ((1 + jacobiComodulus x) ^ (-(1 / 2) : ℂ)) ^ 2 *
          (1 + jacobiComodulus x) = 1 := by
        rw [cpow_neg_one_half_sq]; exact inv_mul_cancel₀ (fun h => by
          have := (isPosReal_add isPosReal_one hκ).2; rw [h] at this; simp at this)
      have hQQ : ((x : ℂ) ^ (-(1 / 2) : ℂ)) ^ 2 * x = 1 := by
        rw [cpow_neg_one_half_sq]; exact inv_mul_cancel₀ (by exact_mod_cast h0.ne')
      have hBB := Carlson.cpow_half_sq (1 - (x : ℂ))
      have hCC := Carlson.cpow_half_sq (2 * (x : ℂ))
      have hAA := Carlson.cpow_half_sq (1 + (x : ℂ))
      have hκκ := jacobiComodulus_sq (x : ℂ)
      have hI : I ^ 2 = -1 := I_sq
      generalize (1 + jacobiComodulus x) ^ (-(1 / 2) : ℂ) = S at *
      generalize (x : ℂ) ^ (-(1 / 2) : ℂ) = Q at *
      generalize (1 + (x : ℂ)) ^ (1 / 2 : ℂ) = A at *
      generalize (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = B at *
      generalize (2 * (x : ℂ)) ^ (1 / 2 : ℂ) = C at *
      generalize jacobiComodulus x = κ at *
      generalize (x : ℂ) = k at *
      field_simp
      linear_combination (-4*k^3*I+4*κ*k^2+4*κ*k*I-4*k^2*I+4*κ*k+4*k^2+4*κ*I+4*k*I+4*k+4*I) * hSS +
          (4*S^2*κ^3*k*I-2*S^2*κ^4+2*S^2*κ^2*k^2+4*S^2*κ^3*I+8*S^2*κ^2*k*I-4*S^2*κ^3+4*S^2*κ^2*k
            +4*S^2*κ*k^2+8*S^2*κ^2*I+4*S^2*κ*k*I+8*S^2*κ*k+2*S^2*k^2+4*S^2*κ*I+4*S^2*κ+4*S^2*k
              +2*S^2) * hQQ +
          (-2*κ*k-2*κ-2*k-2) * hAA +
          (2*κ*k+2*κ+2*k+2) * hBB +
          (2*S^2*Q^2*κ^3*k*I-S^2*Q^2*κ^4+S^2*Q^2*κ^2*k^2+2*S^2*Q^2*κ^3*I+4*S^2*Q^2*κ^2*k*I
            -2*S^2*Q^2*κ^3+2*S^2*Q^2*κ^2*k+2*S^2*Q^2*κ*k^2+4*S^2*Q^2*κ^2*I+2*S^2*Q^2*κ*k*I
              +4*S^2*Q^2*κ*k+S^2*Q^2*k^2+2*S^2*Q^2*κ*I+2*S^2*Q^2*κ+2*S^2*Q^2*k+S^2*Q^2) * hCC +
          (4*S^2*κ*k*I-2*S^2*κ^2+4*S^2*κ*I+4*S^2*k*I-4*S^2*κ+4*S^2*I-2*S^2-A^2+B^2-2*κ*I-4*k*I
            -4*I) * hκκ +
          (S^2*Q^2*C^2*κ^4+2*S^2*Q^2*C^2*κ^3+S^2*Q^2*C^2*κ^2-B^2*κ^2-2*B^2*κ*k-B^2*k^2-2*B^2*κ
            -2*B^2*k-B^2) * hI +
          (-2*κ^2*I-4*κ*k*I-2*k^2*I-4*κ*I-4*k*I-2*I) * hAB
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := isPosReal_half_period_data h0 h1
      rw [re_add_I_mul_of_im_eq_zero
          (isPosReal_div (isPosReal_mul (isPosReal_mul (isPosReal_mul hS hQ) hκ)
        (isPosReal_add isPosReal_one hκ)) (isPosReal_add (isPosReal_add isPosReal_one hx) hκ)).1]
      exact (isPosReal_div (isPosReal_mul (isPosReal_mul (isPosReal_mul hS hQ)
        (isPosReal_add isPosReal_one hx)) (isPosReal_add isPosReal_one hκ))
        (isPosReal_add (isPosReal_add isPosReal_one hx) hκ)).2
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := isPosReal_half_period_data h0 h1
      rw [add_div, mul_div_assoc, re_add_I_mul_of_im_eq_zero (isPosReal_div hB hC).1]
      exact (isPosReal_div hA hC).2
  · refine eqOn_of_sq_eq_of_re_pos
      (f := fun k => (1 + jacobiComodulus k) ^ (-(1 / 2) : ℂ) * jacobiComodulus k ^ (1 / 2 : ℂ) *
        (1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ) * (1 + jacobiComodulus k) /
        (1 + k + jacobiComodulus k) - I * ((1 + jacobiComodulus k) ^ (-(1 / 2) : ℂ) *
        jacobiComodulus k ^ (1 / 2 : ℂ) * (1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ) *
        (1 + jacobiComodulus k) / (1 + k + jacobiComodulus k)))
      (g := fun k => (1 - I) * jacobiComodulus k ^ (1 / 2 : ℂ) / (2 * k) ^ (1 / 2 : ℂ))
      ?_ ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · have h := (((((dS.mul dD).mul dA).mul dQ).mul (dK.const_add 1)).div dN hN)
      exact h.sub (h.const_mul I)
    · exact (dD.const_mul (1 - I)).div dC hC0
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := isPosReal_half_period_data h0 h1
      have hN0 := hN x (ofReal_mem_jacobiModulusDomain h0 h1)
      have hC00 := hC0 x (ofReal_mem_jacobiModulusDomain h0 h1)
      have hSS : ((1 + jacobiComodulus x) ^ (-(1 / 2) : ℂ)) ^ 2 *
          (1 + jacobiComodulus x) = 1 := by
        rw [cpow_neg_one_half_sq]; exact inv_mul_cancel₀ (fun h => by
          have := (isPosReal_add isPosReal_one hκ).2; rw [h] at this; simp at this)
      have hQQ : ((x : ℂ) ^ (-(1 / 2) : ℂ)) ^ 2 * x = 1 := by
        rw [cpow_neg_one_half_sq]; exact inv_mul_cancel₀ (by exact_mod_cast h0.ne')
      have hBB := Carlson.cpow_half_sq (1 - (x : ℂ))
      have hCC := Carlson.cpow_half_sq (2 * (x : ℂ))
      have hAA := Carlson.cpow_half_sq (1 + (x : ℂ))
      have hDD := Carlson.cpow_half_sq (jacobiComodulus x)
      have hκκ := jacobiComodulus_sq (x : ℂ)
      have hI : I ^ 2 = -1 := I_sq
      generalize (1 + jacobiComodulus x) ^ (-(1 / 2) : ℂ) = S at *
      generalize (x : ℂ) ^ (-(1 / 2) : ℂ) = Q at *
      generalize (1 + (x : ℂ)) ^ (1 / 2 : ℂ) = A at *
      generalize (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = B at *
      generalize (2 * (x : ℂ)) ^ (1 / 2 : ℂ) = C at *
      generalize jacobiComodulus x ^ (1 / 2 : ℂ) = D at *
      generalize jacobiComodulus x = κ at *
      generalize (x : ℂ) = k at *
      field_simp
      linear_combination (4*k^3*I-4*κ*k*I+4*k^2*I-4*κ*I-4*k*I-4*I) * hSS +
          (-4*S^2*A^2*κ^3*I-8*S^2*A^2*κ^2*I-4*S^2*A^2*κ*I) * hQQ +
          (4*S^2*κ*k^2*I+8*S^2*k^2*I-8*S^2*κ*I-8*S^2*I) * hAA +
          (-2*S^2*Q^2*A^2*κ^3*I-4*S^2*Q^2*A^2*κ^2*I-2*S^2*Q^2*A^2*κ*I) * hCC +
          (-2*S^2*Q^2*A^2*C^2*κ^2*I-4*S^2*Q^2*A^2*C^2*κ*I-2*S^2*Q^2*A^2*C^2*I+2*κ^2*I+4*κ*k*I
            +2*k^2*I+4*κ*I+4*k*I+2*I) * hDD +
          (-4*S^2*A^2*κ*I-8*S^2*A^2*I+4*S^2*k*I+4*S^2*I+2*κ*I+4*k*I+4*I) * hκκ +
          (S^2*Q^2*A^2*C^2*D^2*κ^2+2*S^2*Q^2*A^2*C^2*D^2*κ+S^2*Q^2*A^2*C^2*D^2-D^2*κ^2-2*D^2*κ*k
            -D^2*k^2-2*D^2*κ-2*D^2*k-D^2) * hI
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := isPosReal_half_period_data h0 h1
      have h := isPosReal_div
          (isPosReal_mul (isPosReal_mul (isPosReal_mul (isPosReal_mul hS hD) hA) hQ)
        (isPosReal_add isPosReal_one hκ)) (isPosReal_add (isPosReal_add isPosReal_one hx) hκ)
      rw [re_sub_I_mul_of_im_eq_zero h.1]; exact h.2
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := isPosReal_half_period_data h0 h1
      rw [show ∀ a b : ℂ, (1 - I) * a / b = a / b - I * (a / b) from fun a b => by ring,
        re_sub_I_mul_of_im_eq_zero (isPosReal_div hD hC).1]
      exact (isPosReal_div hD hC).2
  · refine eqOn_of_sq_eq_of_re_pos
      (f := fun k => jacobiComodulus k ^ (1 / 2 : ℂ) * (1 + k) ^ (1 / 2 : ℂ) *
        (1 + jacobiComodulus k) / (1 + k + jacobiComodulus k) -
        I * (jacobiComodulus k ^ (1 / 2 : ℂ) * (1 + k) ^ (1 / 2 : ℂ) * k /
        (1 + k + jacobiComodulus k)))
      (g := fun k => (1 - I) / 2 * jacobiComodulus k ^ (1 / 2 : ℂ) *
        ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)))
      ?_ ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · exact ((((dD.mul dA).mul (dK.const_add 1)).div dN hN)).sub
        ((((dD.mul dA).mul dId).div dN hN).const_mul I)
    · exact (dD.const_mul ((1 - I) / 2)).mul (dA.add (dB.const_mul I))
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := isPosReal_half_period_data h0 h1
      have hN0 := hN x (ofReal_mem_jacobiModulusDomain h0 h1)
      have hC00 := hC0 x (ofReal_mem_jacobiModulusDomain h0 h1)
      have hSS : ((1 + jacobiComodulus x) ^ (-(1 / 2) : ℂ)) ^ 2 *
          (1 + jacobiComodulus x) = 1 := by
        rw [cpow_neg_one_half_sq]; exact inv_mul_cancel₀ (fun h => by
          have := (isPosReal_add isPosReal_one hκ).2; rw [h] at this; simp at this)
      have hQQ : ((x : ℂ) ^ (-(1 / 2) : ℂ)) ^ 2 * x = 1 := by
        rw [cpow_neg_one_half_sq]; exact inv_mul_cancel₀ (by exact_mod_cast h0.ne')
      have hBB := Carlson.cpow_half_sq (1 - (x : ℂ))
      have hCC := Carlson.cpow_half_sq (2 * (x : ℂ))
      have hAA := Carlson.cpow_half_sq (1 + (x : ℂ))
      have hDD := Carlson.cpow_half_sq (jacobiComodulus x)
      have hκκ := jacobiComodulus_sq (x : ℂ)
      have hI : I ^ 2 = -1 := I_sq
      generalize (1 + jacobiComodulus x) ^ (-(1 / 2) : ℂ) = S at *
      generalize (x : ℂ) ^ (-(1 / 2) : ℂ) = Q at *
      generalize (1 + (x : ℂ)) ^ (1 / 2 : ℂ) = A at *
      generalize (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = B at *
      generalize (2 * (x : ℂ)) ^ (1 / 2 : ℂ) = C at *
      generalize jacobiComodulus x ^ (1 / 2 : ℂ) = D at *
      generalize jacobiComodulus x = κ at *
      generalize (x : ℂ) = k at *
      field_simp
      linear_combination (4*k^3*I-8*κ*k^2-4*κ*k*I-4*k^2*I-8*k^2+4*κ*I-4*k*I+8*κ+4*I+8) * hAA +
          (4*k^3*I-4*κ*k*I+4*k^2*I-4*κ*I-4*k*I-4*I) * hBB +
          (2*A^2*κ^2*I-2*B^2*κ^2*I-4*A^2*κ*k*I-4*B^2*κ*k*I+2*A^2*k^2*I-2*B^2*k^2*I+4*A^2*κ^2
            -4*A*B*κ^2-8*A*B*κ*k-4*A^2*k^2-4*A*B*k^2+4*A^2*κ*I-4*B^2*κ*I-4*A^2*k*I-4*B^2*k*I
              +8*A^2*κ-8*A*B*κ-8*A*B*k+2*A^2*I-2*B^2*I+4*A^2-4*A*B) * hDD +
          (2*A^2*κ*I-2*B^2*κ*I-4*A^2*k*I-4*B^2*k*I+4*A^2*κ+4*A^2*I-4*B^2*I+8*A^2-4*κ^2-8*κ*k-8*κ
            -8*k-8) * hκκ +
          (-B^2*D^2*κ^2*I^2-2*B^2*D^2*κ*k*I^2-B^2*D^2*k^2*I^2-2*A*B*D^2*κ^2*I+2*B^2*D^2*κ^2*I
            -4*A*B*D^2*κ*k*I+4*B^2*D^2*κ*k*I-2*A*B*D^2*k^2*I+2*B^2*D^2*k^2*I-2*B^2*D^2*κ*I^2
              -2*B^2*D^2*k*I^2-A^2*D^2*κ^2+4*A*B*D^2*κ^2-2*A^2*D^2*κ*k+8*A*B*D^2*κ*k+3*A^2*D^2*k^2
                +4*A*B*D^2*k^2-4*A*B*D^2*κ*I+4*B^2*D^2*κ*I-4*A*B*D^2*k*I+4*B^2*D^2*k*I-B^2*D^2*I^2
                  -2*A^2*D^2*κ+8*A*B*D^2*κ-2*A^2*D^2*k+8*A*B*D^2*k-2*A*B*D^2*I+2*B^2*D^2*I-A^2*D^2
                    +4*A*B*D^2) * hI +
          (-4*κ^3-8*κ^2*k-4*κ*k^2-8*κ^2-8*κ*k-4*κ) * hAB
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := isPosReal_half_period_data h0 h1
      have h := isPosReal_div (isPosReal_mul (isPosReal_mul hD hA) (isPosReal_add isPosReal_one hκ))
        (isPosReal_add (isPosReal_add isPosReal_one hx) hκ)
      have h' := isPosReal_div (isPosReal_mul (isPosReal_mul hD hA) hx)
        (isPosReal_add (isPosReal_add isPosReal_one hx) hκ)
      rw [re_sub_I_mul_of_im_eq_zero h'.1]; exact h.2
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := isPosReal_half_period_data h0 h1
      have e : ∀ D A B : ℂ, (1 - I) / 2 * D * (A + I * B) = D * (A + B) / 2 + I *
          (D * (B - A) / 2) :=
        fun D A B => by linear_combination (-(D * B) / 2) * I_sq
      have h2 : IsPosReal (2 : ℂ) := ⟨by simp, by norm_num⟩
      rw [e, re_add_I_mul_of_im_eq_zero
          (by simp only [div_ofNat_im, mul_im, sub_im, sub_re, hD.1, hA.1, hB.1]; ring)]
      exact (isPosReal_div (isPosReal_mul hD (isPosReal_add hA hB)) h2).2

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = 3(K + iK')/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfKKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSn (3 * (completeEllipticK k + I * completeEllipticKPrime k) / 2) k =
        ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiCn (3 * (completeEllipticK k + I * completeEllipticKPrime k) / 2) k = (1 - I) *
          jacobiComodulus k ^
          (1 / 2 : ℂ) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiDn (3 * (completeEllipticK k + I * completeEllipticKPrime k) / 2) k = (I - 1) / 2 *
          jacobiComodulus
          k ^ (1 / 2 : ℂ) * ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := jacobi_specialValues_HalfKKp hk
  have e : 3 * (completeEllipticK k + I * completeEllipticKPrime k) / 2 =
      -((completeEllipticK k + I * completeEllipticKPrime k) / 2) + 2 * completeEllipticK k +
        2 * (I * completeEllipticKPrime k) := by ring
  rw [e, (jacobiSn_shift hk _).2.2.2.2.1, (jacobiCn_shift hk _).2.2.2.2.1,
    (jacobiDn_shift hk _).2.2.2.2.1, jacobiSn, jacobiCn, jacobiDn, jacobiPQ_neg,
    jacobiPQ_neg, jacobiPQ_neg, ← jacobiSn, ← jacobiCn, ← jacobiDn, h1, h2, h3]
  refine ⟨by simp, by simp, ?_⟩
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false, ↓reduceIte]
  ring

/-- §22.5(ii): `K(k) → π/2` as real `k → 0+`. -/
@[dlmf 22.5.ii]
theorem tendsto_completeEllipticK_zero :
    Tendsto (fun k : ℝ => completeEllipticK k) (𝓝[>] 0) (𝓝 (π / 2)) := by
  have hc : ContinuousAt (fun k : ℝ => (Real.completeEllipticKOfParameter (k ^ 2) : ℂ)) 0 := by
    refine Complex.continuous_ofReal.continuousAt.comp ?_
    have h1 : ContinuousAt Real.completeEllipticKOfParameter ((0 : ℝ) ^ 2) :=
      Real.continuousAt_completeEllipticKOfParameter (by norm_num)
    exact h1.comp (f := fun k : ℝ => k ^ 2) (continuous_pow 2).continuousAt
  have h := hc.tendsto
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Real.completeEllipticKOfParameter_zero,
    ofReal_div, ofReal_ofNat] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
  rw [completeEllipticK_ofReal (by nlinarith [hk.1, hk.2])]

/-- §22.5(ii): `K'(k) → π/2` as real `k → 1-`. -/
@[dlmf 22.5.ii]
theorem tendsto_completeEllipticKPrime_one :
    Tendsto (fun k : ℝ => completeEllipticKPrime k) (𝓝[<] 1) (𝓝 (π / 2)) := by
  have hc : ContinuousAt (fun k : ℝ => (Real.completeEllipticKOfParameter (1 - k ^ 2) : ℂ)) 1 := by
    refine Complex.continuous_ofReal.continuousAt.comp ?_
    have h1 : ContinuousAt Real.completeEllipticKOfParameter (1 - (1 : ℝ) ^ 2) :=
      Real.continuousAt_completeEllipticKOfParameter (by norm_num)
    exact h1.comp (f := fun k : ℝ => 1 - k ^ 2)
        (continuous_const.sub (continuous_pow 2)).continuousAt
  have h := hc.tendsto
  simp only [one_pow, sub_self, Real.completeEllipticKOfParameter_zero, ofReal_div,
      ofReal_ofNat] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
  rw [completeEllipticKPrime_ofReal (by nlinarith [hk.1, hk.2])]

/-- Logarithmic lower bound `K(1 - δ²) ≥ log(π/(2δ))/√2` for `0 < δ < π/2`. -/
lemma log_div_sqrt_two_le_completeEllipticKOfParameter {δ : ℝ} (h0 : 0 < δ) (h1 : δ < π / 2) :
    Real.log (π / 2 / δ) / √2 ≤ Real.completeEllipticKOfParameter (1 - δ ^ 2) := by
  have hm : 1 - δ ^ 2 < 1 := by nlinarith
  set f : ℝ → ℝ := fun θ => (1 - (1 - δ ^ 2) * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ) with hf
  have hfc : Continuous f := continuous_one_sub_mul_sin_sq_rpow hm _
  have hfpos : ∀ θ, 0 ≤ f θ := fun θ => Real.rpow_nonneg (one_sub_mul_sin_sq_pos hm θ).le _
  have hs2 : 0 < √2 := by positivity
  -- restrict to `[0, π/2 - δ]`
  have hsub : ∫ θ in (0 : ℝ)..(π / 2 - δ), f θ ≤ Real.completeEllipticKOfParameter (1 - δ ^ 2) := by
    rw [Real.completeEllipticKOfParameter]
    have := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hfc.intervalIntegrable 0 (π / 2 - δ)) (hfc.intervalIntegrable (π / 2 - δ) (π / 2))
    rw [← this]
    have : 0 ≤ ∫ θ in (π / 2 - δ)..(π / 2), f θ :=
      intervalIntegral.integral_nonneg (by linarith) fun θ _ => hfpos θ
    linarith
  have hlow : ∫ θ in (0 : ℝ)..(π / 2 - δ), 1 / (√2 * (π / 2 - θ)) ≤
      ∫ θ in (0 : ℝ)..(π / 2 - δ), f θ := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ (hfc.intervalIntegrable _ _) ?_
    · refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.div (by fun_prop) fun θ hθ => ?_
      rw [Set.uIcc_of_le (by linarith)] at hθ
      have : 0 < π / 2 - θ := by linarith [hθ.2]
      positivity
    · intro θ hθ
      have hx : δ ≤ π / 2 - θ := by linarith [hθ.2]
      have hxpos : 0 < π / 2 - θ := by linarith
      have hc : Real.cos θ ≤ π / 2 - θ := by
        rw [← Real.sin_pi_div_two_sub]; exact Real.sin_le hxpos.le
      have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2]⟩
      have hp := one_sub_mul_sin_sq_pos hm θ
      have hle : 1 - (1 - δ ^ 2) * Real.sin θ ^ 2 ≤ 2 * (π / 2 - θ) ^ 2 := by
        have h := Real.sin_sq_add_cos_sq θ
        have : Real.cos θ ^ 2 ≤ (π / 2 - θ) ^ 2 := pow_le_pow_left₀ hc0 hc 2
        have : δ ^ 2 ≤ (π / 2 - θ) ^ 2 := pow_le_pow_left₀ h0.le hx 2
        nlinarith [Real.sin_sq_le_one θ, sq_nonneg δ]
      simp only [hf]
      rw [Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow, one_div]
      apply inv_anti₀ (Real.sqrt_pos.mpr hp)
      calc √(1 - (1 - δ ^ 2) * Real.sin θ ^ 2) ≤ √(2 * (π / 2 - θ) ^ 2) := Real.sqrt_le_sqrt hle
        _ = √2 * (π / 2 - θ) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hxpos.le]
  have hcalc : ∫ θ in (0 : ℝ)..(π / 2 - δ), 1 / (√2 * (π / 2 - θ)) = Real.log (π / 2 / δ) / √2 := by
    have : ∀ θ, 1 / (√2 * (π / 2 - θ)) = (1 / √2) * (π / 2 - θ)⁻¹ := fun θ => by
      field_simp
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left
      (fun x => x⁻¹) (π / 2)]
    rw [show π / 2 - (π / 2 - δ) = δ by ring, sub_zero, integral_inv_of_pos h0 (by positivity)]
    ring
  linarith

/-- `log(π/(2δ))/√2 → ∞` as `δ → 0+`. -/
lemma tendsto_log_pi_div_two_div_div_sqrt_two :
    Tendsto (fun δ : ℝ => Real.log (π / 2 / δ) / √2) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun δ : ℝ => π / 2 / δ) (𝓝[>] 0) atTop := by
    simp_rw [div_eq_mul_inv (π / 2)]
    exact tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
  exact (Real.tendsto_log_atTop.comp h1).atTop_div_const (by positivity)

/-- §22.5(ii): `K'(k) → ∞` as real `k → 0+`. -/
@[dlmf 22.5.ii]
theorem tendsto_norm_completeEllipticKPrime_zero :
    Tendsto (fun k : ℝ => ‖completeEllipticKPrime k‖) (𝓝[>] 0) Filter.atTop := by
  refine tendsto_atTop_mono' _ ?_ tendsto_log_pi_div_two_div_div_sqrt_two
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
  have hk2 : 0 < k ^ 2 := by nlinarith [hk.1]
  rw [completeEllipticKPrime_ofReal hk2, Complex.norm_real, Real.norm_eq_abs]
  exact (log_div_sqrt_two_le_completeEllipticKOfParameter hk.1
      (by linarith [hk.2, Real.pi_gt_three])).trans
      (le_abs_self _)

/-- §22.5(ii): `K(k) → ∞` as real `k → 1-`. -/
@[dlmf 22.5.ii]
theorem tendsto_norm_completeEllipticK_one :
    Tendsto (fun k : ℝ => ‖completeEllipticK k‖) (𝓝[<] 1) Filter.atTop := by
  have hδ : Tendsto (fun k : ℝ => √(1 - k ^ 2)) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun k : ℝ => √(1 - k ^ 2)) (𝓝 1) (𝓝 (√(1 - 1 ^ 2))) :=
        ((continuous_const.sub (continuous_pow 2)).sqrt).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
      exact Real.sqrt_pos.mpr (by nlinarith [hk.1, hk.2])
  refine tendsto_atTop_mono' _ ?_ (tendsto_log_pi_div_two_div_div_sqrt_two.comp hδ)
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  have hpos : 0 < 1 - k ^ 2 := by linarith
  have hd0 : 0 < √(1 - k ^ 2) := Real.sqrt_pos.mpr hpos
  have hd1 : √(1 - k ^ 2) < π / 2 := by
    have : √(1 - k ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
    linarith [Real.pi_gt_three]
  have h := log_div_sqrt_two_le_completeEllipticKOfParameter hd0 hd1
  rw [Real.sq_sqrt hpos.le, show 1 - (1 - k ^ 2) = k ^ 2 by ring] at h
  rw [completeEllipticK_ofReal hk2, Complex.norm_real, Real.norm_eq_abs]
  exact h.trans (le_abs_self _)

end DLMF.JacobiElliptic
end
end
