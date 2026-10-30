/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.SpecialValues.DerivativesAndResidues

/-!
# Real Jacobian functions and half-period values

ODE uniqueness identifies the real amplitude functions with the complex theta quotients and
determines half-period values.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.SpecialValues`.
-/

@[expose] public section

open Complex DLMF.Elliptic Filter

open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

macro "je22a_value_tac " hk:term:max : tactic => `(tactic|
  (simp only [jacobiSnk_zero $hk, jacobiCnk_zero $hk, jacobiDnk_zero $hk, jacobiCdk_zero $hk,
    jacobiSdk_zero $hk, jacobiNdk_zero $hk, jacobiDck_zero $hk, jacobiNck_zero $hk,
    jacobiSck_zero $hk, mul_one, mul_zero, neg_zero] <;> try ring))

/-! ### Real bridges (DLMF 22.2.4–22.2.6 on the real line)

For `0 < k < 1` and real `u`, the theta-quotient `sn, cn, dn` agree with the amplitude-based
`Real.jacobiSnm, Real.jacobiCnm, Real.jacobiDnm` of parameter `m = k²`: both triples solve
`s' = cd, c' = -sd, d' = -k²sc` with `(s, c, d)(0) = (0, 1, 1)`, so they agree by ODE
uniqueness (`ODE_solution_unique_of_mem_Ioo`). (Moved here from `Basic`.) -/

/-- For real `0 < k < 1`, the complex `sn, cn, dn` have no pole on the real line. -/
theorem p22R1_reg_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiLetterTheta .n (jacobiZetak u k) (jacobiTauk k) ≠ 0 := by
  have hk := p22R1_ofReal_mem hk0 hk1
  have hτ := jacobiTauk_im_pos hk
  have hK := compEllIntKk_ofReal (k := k) (by nlinarith)
  have hKpos : 0 < Real.compEllIntKm (k ^ 2) := Real.compEllIntKm_pos (by nlinarith)
  have hz : jacobiZetak u k = ((u / (2 * Real.compEllIntKm (k ^ 2)) : ℝ) : ℂ) * π := by
    rw [jacobiZetak, hK]; push_cast; field_simp
  rw [hz, jacobiLetterTheta]
  exact div_ne_zero (p22R1_theta_real_ne hτ _).1 (by simpa using (p22R1_theta_real_ne hτ 0).1)

open Set in
/-- Joint real-line identification of the complex and real `sn, cn, dn` (ODE uniqueness). -/
lemma p22R1_ofReal_all {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiSnk u k = (Real.jacobiSnm u (k ^ 2) : ℂ) ∧
      jacobiCnk u k = (Real.jacobiCnm u (k ^ 2) : ℂ) ∧
      jacobiDnk u k = (Real.jacobiDnm u (k ^ 2) : ℂ) := by
  have hk := p22R1_ofReal_mem hk0 hk1
  have hm : k ^ 2 < 1 := by nlinarith
  set f : ℝ → ℂ × ℂ × ℂ := fun t => (jacobiSnk t k, jacobiCnk t k, jacobiDnk t k) with hf
  set g : ℝ → ℂ × ℂ × ℂ := fun t =>
    ((Real.jacobiSnm t (k ^ 2) : ℂ), (Real.jacobiCnm t (k ^ 2) : ℂ),
      (Real.jacobiDnm t (k ^ 2) : ℂ)) with hg
  set v : ℝ → ℂ × ℂ × ℂ → ℂ × ℂ × ℂ := fun _ x =>
    (x.2.1 * x.2.2, -(x.1 * x.2.2), -((k : ℂ) ^ 2 * x.1 * x.2.1)) with hv
  have hf' : ∀ t : ℝ, HasDerivAt f (v t (f t)) t := fun t => by
    have hz := p22R1_reg_real hk0 hk1 t
    exact ((hasDerivAt_jacobiSnk hk hz).comp_ofReal).prodMk
      (((hasDerivAt_jacobiCnk hk hz).comp_ofReal).prodMk
        ((hasDerivAt_jacobiDnk hk hz).comp_ofReal))
  have hg' : ∀ t : ℝ, HasDerivAt g (v t (g t)) t := fun t => by
    have h1 := (Real.hasDerivAt_jacobiSnm hm t).ofReal_comp
    have h2 := (Real.hasDerivAt_jacobiCnm hm t).ofReal_comp
    have h3 := (Real.hasDerivAt_jacobiDnm hm t).ofReal_comp
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
  obtain ⟨L, hL⟩ := (hvL.locallyLipschitzOn (s := Metric.closedBall 0 R)).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall 0 R)
  have h0 : f 0 = g 0 := by
    simp only [hf, hg, ofReal_zero, jacobiSnk_zero hk, jacobiCnk_zero hk, jacobiDnk_zero hk,
      Real.jacobiSnm, Real.jacobiCnm, Real.jacobiDnm, Real.jacobiAmm_zero hm]
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
for `0 < k < 1` and real `u`, `sn(u, k) = Real.jacobiSnm u (k²)`. -/
@[dlmf 22.2.E4 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiSnk_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiSnk u k = (Real.jacobiSnm u (k ^ 2) : ℂ) :=
  (p22R1_ofReal_all hk0 hk1 u).1

/-- Bridge to the real-variable `cn`: for `0 < k < 1` and real `u`,
`cn(u, k) = Real.jacobiCnm u (k²)`. -/
@[dlmf 22.2.E5 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiCnk_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiCnk u k = (Real.jacobiCnm u (k ^ 2) : ℂ) :=
  (p22R1_ofReal_all hk0 hk1 u).2.1

/-- Bridge to the real-variable `dn`: for `0 < k < 1` and real `u`,
`dn(u, k) = Real.jacobiDnm u (k²)`. -/
@[dlmf 22.2.E6 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiDnk_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiDnk u k = (Real.jacobiDnm u (k ^ 2) : ℂ) :=
  (p22R1_ofReal_all hk0 hk1 u).2.2

/-- Estimate under the stated parameter and domain assumptions: `0 < (w ^ (1 / 2 : ℂ)).re`. -/
lemma p22R1_re_cpow_half_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w ^ (1 / 2 : ℂ)).re :=
  p22R1_re_sqrt_pos (Or.inl hw)

/-- Estimate under the stated parameter and domain assumptions: `0 < (w ^ (-(1 / 2) : ℂ)).re`. -/
lemma p22R1_re_cpow_neg_half_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w ^ (-(1 / 2) : ℂ)).re := by
  rw [cpow_neg, inv_re]
  have h := p22R1_re_cpow_half_pos hw
  exact div_pos h (normSq_pos.mpr fun h0 => by rw [h0] at h; simp at h)

/-- Estimate under the stated parameter and domain assumptions: `0 < (a / (1 + a)).re`. -/
lemma p22R1_re_div_one_add_pos {a : ℂ} (ha : 0 < a.re) : 0 < (a / (1 + a)).re := by
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
lemma p22R1_cpow_neg_half_sq (w : ℂ) : (w ^ (-(1 / 2) : ℂ)) ^ 2 = w⁻¹ := by
  rw [cpow_neg, inv_pow, p22R1_sqrt_sq]

/-- Estimate under the stated parameter and domain assumptions: `0 < (jacobiComodulusk k).re`. -/
lemma p22R1_comodulus_re_pos {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    0 < (jacobiComodulusk k).re := (p22R1_comodulus_mem hk).1

/-- Differentiability at the specified argument: `DifferentiableAt ℂ jacobiComodulusk k`. -/
lemma p22R1_differentiableAt_comodulus {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    DifferentiableAt ℂ jacobiComodulusk k := by
  have hk' := hk
  rw [p22R1_domain_eq] at hk'
  exact (by fun_prop : DifferentiableAt ℂ (fun k : ℂ => 1 - k ^ 2) k).cpow_const hk'.2

/-- Square-root branch selection by the identity theorem. -/
lemma p22R1_branch {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f jacobiModulusDomain)
    (hg : DifferentiableOn ℂ g jacobiModulusDomain)
    (hsq : ∀ x : ℝ, 0 < x → x < 1 → f x ^ 2 = g x ^ 2)
    (hfr : ∀ x : ℝ, 0 < x → x < 1 → 0 < (f x).re)
    (hgr : ∀ x : ℝ, 0 < x → x < 1 → 0 < (g x).re) : Set.EqOn f g jacobiModulusDomain := by
  refine p22R1_eqOn_of_real hf hg fun x h0 h1 => ?_
  have h : (f x - g x) * (f x + g x) = 0 := by linear_combination hsq x h0 h1
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg re h
    simp only [add_re, zero_re] at this
    linarith [hfr x h0 h1, hgr x h0 h1]

/-- Composition of Glaisher's quotient at a constant real theta argument with `τ(k)`. -/
lemma p22R1_differentiableOn_glaisher_const (p q : JacobiLetter) (c : ℂ)
    (hq : ∀ τ : ℂ, 0 < τ.im → jacobiLetterTheta q c τ ≠ 0) :
    DifferentiableOn ℂ (fun k => jacobiGlaisher p q c (jacobiTauk k)) jacobiModulusDomain := by
  refine p22R1_differentiableOn_comp fun τ hτ => ?_
  have hl : ∀ r : JacobiLetter, DifferentiableAt ℂ (fun σ => jacobiLetterTheta r c σ) τ :=
    fun r => (p22R1_differentiableAt_letterTheta r (x := (c, τ)) hτ).comp τ
      (f := fun σ : ℂ => (c, σ)) (by fun_prop)
  unfold jacobiGlaisher
  by_cases hpq : p = q
  · simp only [hpq, ↓reduceIte]; exact differentiableAt_const _
  · simp only [hpq, ↓reduceIte]; exact (hl p).div (hl q) (hq τ hτ)

/-- Identity under the stated parameter and domain assumptions: `jacobiZetak (compEllIntKk k / 2)
k = ((1 / 4 : ℝ) : ℂ) * π`. -/
lemma p22R1_zeta_halfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiZetak (compEllIntKk k / 2) k = ((1 / 4 : ℝ) : ℂ) * π := by
  have := compEllIntKk_ne_zero hk
  rw [jacobiZetak]; push_cast; field_simp; ring

/-- Nonvanishing under the stated hypotheses: `jacobiLetterTheta r (((1 / 4 : ℝ) : ℂ) * π) τ ≠ 0`. -/
lemma p22R1_theta_quarter_ne {τ : ℂ} (hτ : 0 < τ.im) (r : JacobiLetter) :
    jacobiLetterTheta r (((1 / 4 : ℝ) : ℂ) * π) τ ≠ 0 := by
  obtain ⟨h4, h3, h1⟩ := p22R1_theta_real_ne hτ (1 / 4)
  have n2 := je22a_thetaTwo_zero_ne_zero hτ
  have n3 := je22a_thetaThree_zero_ne_zero hτ
  have n4 := je22a_thetaFour_zero_ne_zero hτ
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
    have h := (p22R1_theta_real_ne hτ (-(1 / 4))).2.2 hnz'
    have e : jacobiThetaOneTau (((-(1 / 4) : ℝ) : ℂ) * π) τ =
        -jacobiThetaTwoTau (((1 / 4 : ℝ) : ℂ) * π) τ := by
      rw [jacobiThetaOneTau]; congr 2; push_cast; ring
    rw [e] at h; exact fun h' => h (by rw [h', neg_zero])
  · exact div_ne_zero h3 n3
  · exact div_ne_zero h4 n4

/-- Identity under the stated parameter and domain assumptions: `StrictMono fun u =>
Real.jacobiAmm u m`. -/
theorem p22R1_amm_strictMono {m : ℝ} (hm : m < 1) : StrictMono fun u => Real.jacobiAmm u m := by
  simp only [Real.jacobiAmm, hm, ↓reduceDIte]
  exact (Real.incEllIntFmOrderIso hm).symm.strictMono

/-- The values at `K/2` up to the choice of square roots. -/
lemma p22R1_halfK_alg {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiDnk (compEllIntKk k / 2) k ^ 2 = jacobiComodulusk k ∧
      jacobiSnk (compEllIntKk k / 2) k ^ 2 * (1 + jacobiComodulusk k) = 1 ∧
      jacobiCnk (compEllIntKk k / 2) k =
        jacobiSnk (compEllIntKk k / 2) k * jacobiDnk (compEllIntKk k / 2) k := by
  have hτ := jacobiTauk_im_pos hk
  set u := compEllIntKk k / 2 with hu
  have hreg : ∀ r, JacobiRegulark r u k := fun r => by
    unfold JacobiRegulark; rw [hu, p22R1_zeta_halfK hk]; exact p22R1_theta_quarter_ne hτ r
  have hd : jacobiDnk u k ≠ 0 := jacobiPQk_ne_zero (by decide) (hreg .d) (hreg .n)
  have hm : -u + compEllIntKk k = u := by rw [hu]; ring
  have e1 := (jacobiSnk_shift hk (-u)).1
  have e3 := (jacobiDnk_shift hk (-u)).1
  rw [hm] at e1 e3
  rw [jacobiCdk, jacobiPQk_neg, ← jacobiCdk] at e1
  rw [jacobiNdk, jacobiPQk_neg, ← jacobiNdk] at e3
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, decide_true, not_true_eq_false,
    ↓reduceIte, Bool.not_eq_true, eq_self_iff_true] at e1 e3
  obtain ⟨-, -, -, -, -, -, hsd, hcd, hnd⟩ := je22a_glaisher_via_n (hreg .n)
  rw [hcd] at e1; rw [hnd] at e3
  obtain ⟨hsc, -⟩ := jacobi_sq_sum hk (hreg .n)
  have hdd : jacobiDnk u k ^ 2 = jacobiComodulusk k := by
    field_simp at e3; linear_combination e3
  refine ⟨hdd, ?_, ?_⟩
  · field_simp at e1
    have hc : jacobiCnk u k = jacobiSnk u k * jacobiDnk u k := by linear_combination -e1
    rw [hc] at hsc
    linear_combination hsc - jacobiSnk u k ^ 2 * hdd
  · field_simp at e1; linear_combination -e1

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = K/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (compEllIntKk k / 2) k = (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) ∧
      jacobiCnk (compEllIntKk k / 2) k = (jacobiComodulusk k / (1 + jacobiComodulusk k)) ^
          (1 / 2 : ℂ) ∧
      jacobiDnk (compEllIntKk k / 2) k = jacobiComodulusk k ^ (1 / 2 : ℂ) := by
  -- holomorphy of the three left-hand sides
  have hL : ∀ p q : JacobiLetter, q ≠ .s → DifferentiableOn ℂ
      (fun k => jacobiPQk p q (compEllIntKk k / 2) k) jacobiModulusDomain := by
    intro p q _
    refine (p22R1_differentiableOn_glaisher_const p q _
      fun τ hτ => p22R1_theta_quarter_ne hτ q).congr fun k hk => ?_
    simp only [jacobiPQk, p22R1_zeta_halfK hk]
  have hkd : DifferentiableOn ℂ jacobiComodulusk jacobiModulusDomain := fun k hk =>
    (p22R1_differentiableAt_comodulus hk).differentiableWithinAt
  have hslit : ∀ {w : ℂ}, 0 < w.re → w ∈ slitPlane := fun h => Or.inl h
  have h1re : ∀ k ∈ jacobiModulusDomain, 0 < (1 + jacobiComodulusk k).re := fun k hk => by
    simp only [add_re, one_re]; linarith [p22R1_comodulus_re_pos hk]
  -- real positivity of the left-hand sides
  have hreal : ∀ x : ℝ, 0 < x → x < 1 → ∀ p : JacobiLetter, p ≠ .s → ∀ q : JacobiLetter,
      jacobiPQk q .n (compEllIntKk x / 2) x = jacobiPQk q .n
        ((Real.compEllIntKm (x ^ 2) / 2 : ℝ) : ℂ) x := by
    intro x h0 h1 _ _ q
    rw [compEllIntKk_ofReal (by nlinarith)]; push_cast; rfl
  have hm : ∀ x : ℝ, 0 < x → x < 1 → x ^ 2 < 1 := fun x h0 h1 => by nlinarith
  have hamm : ∀ x : ℝ, 0 < x → x < 1 →
      0 < Real.jacobiAmm (Real.compEllIntKm (x ^ 2) / 2) (x ^ 2) ∧
        Real.jacobiAmm (Real.compEllIntKm (x ^ 2) / 2) (x ^ 2) < π / 2 := by
    intro x h0 h1
    have hK := Real.compEllIntKm_pos (hm x h0 h1)
    have a := p22R1_amm_strictMono (hm x h0 h1) (show 0 < Real.compEllIntKm (x ^ 2) / 2 by
      positivity)
    have b := p22R1_amm_strictMono (hm x h0 h1)
      (show Real.compEllIntKm (x ^ 2) / 2 < Real.compEllIntKm (x ^ 2) by linarith)
    simp only [Real.jacobiAmm_zero (hm x h0 h1), Real.jacobiAmm_compEllIntKm (hm x h0 h1)] at a b
    exact ⟨a, b⟩
  refine ⟨?_, ?_, ?_⟩
  · refine p22R1_branch (f := fun k => jacobiSnk (compEllIntKk k / 2) k)
      (g := fun k => (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ)) (hL .s .n (by decide))
      ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · intro k hk
      exact ((hkd k hk).const_add 1).cpow_const (hslit (h1re k hk))
        |>.differentiableAt (p22R1_isOpen_domain.mem_nhds hk) |>.differentiableWithinAt
    · have h := (p22R1_halfK_alg (p22R1_ofReal_mem h0 h1)).2.1
      have hne : (1 + jacobiComodulusk x) ≠ 0 := fun h' => by
        have := h1re x (p22R1_ofReal_mem h0 h1); rw [h'] at this; simp at this
      rw [p22R1_cpow_neg_half_sq]
      field_simp
      linear_combination h
    · simp only [jacobiSnk]
      rw [hreal x h0 h1 .c (by decide) .s, ← jacobiSnk, jacobiSnk_ofReal h0 h1, ofReal_re,
        Real.jacobiSnm]
      exact Real.sin_pos_of_pos_of_lt_pi (hamm x h0 h1).1 (by linarith [(hamm x h0 h1).2,
        Real.pi_pos])
    · exact p22R1_re_cpow_neg_half_pos (h1re x (p22R1_ofReal_mem h0 h1))
  · have hne : ∀ k ∈ jacobiModulusDomain, (1 + jacobiComodulusk k) ≠ 0 := fun k hk h' => by
      have := h1re k hk; rw [h'] at this; simp at this
    refine p22R1_branch (f := fun k => jacobiCnk (compEllIntKk k / 2) k)
      (g := fun k => (jacobiComodulusk k / (1 + jacobiComodulusk k)) ^ (1 / 2 : ℂ))
      (hL .c .n (by decide)) ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · intro k hk
      exact ((hkd k hk).div ((hkd k hk).const_add 1) (hne k hk)).cpow_const
        (hslit (p22R1_re_div_one_add_pos (p22R1_comodulus_re_pos hk)))
        |>.differentiableAt (p22R1_isOpen_domain.mem_nhds hk) |>.differentiableWithinAt
    · obtain ⟨hd, hs, hc⟩ := p22R1_halfK_alg (p22R1_ofReal_mem h0 h1)
      have hn := hne x (p22R1_ofReal_mem h0 h1)
      rw [p22R1_sqrt_sq, hc, mul_pow, hd]
      field_simp
      linear_combination jacobiComodulusk x * hs
    · simp only [jacobiCnk]
      rw [hreal x h0 h1 .c (by decide) .c, ← jacobiCnk, jacobiCnk_ofReal h0 h1, ofReal_re,
        Real.jacobiCnm]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [(hamm x h0 h1).1, Real.pi_pos],
        (hamm x h0 h1).2⟩
    · exact p22R1_re_cpow_half_pos (p22R1_re_div_one_add_pos
        (p22R1_comodulus_re_pos (p22R1_ofReal_mem h0 h1)))
  · refine p22R1_branch (f := fun k => jacobiDnk (compEllIntKk k / 2) k)
      (g := fun k => jacobiComodulusk k ^ (1 / 2 : ℂ))
      (hL .d .n (by decide)) ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · intro k hk
      exact (hkd k hk).cpow_const (hslit (p22R1_comodulus_re_pos hk))
        |>.differentiableAt (p22R1_isOpen_domain.mem_nhds hk) |>.differentiableWithinAt
    · rw [p22R1_sqrt_sq]; exact (p22R1_halfK_alg (p22R1_ofReal_mem h0 h1)).1
    · simp only [jacobiDnk]
      rw [hreal x h0 h1 .c (by decide) .d, ← jacobiDnk, jacobiDnk_ofReal h0 h1, ofReal_re]
      exact Real.jacobiDnm_pos (hm x h0 h1) _
    · exact p22R1_re_cpow_half_pos (p22R1_comodulus_re_pos (p22R1_ofReal_mem h0 h1))

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = 3K/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (3 * compEllIntKk k / 2) k = (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) ∧
      jacobiCnk (3 * compEllIntKk k / 2) k = -(jacobiComodulusk k / (1 + jacobiComodulusk k)) ^
          (1 / 2 : ℂ) ∧
      jacobiDnk (3 * compEllIntKk k / 2) k = jacobiComodulusk k ^ (1 / 2 : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := jacobi_specialValues_HalfK hk
  have e : 3 * compEllIntKk k / 2 = -(compEllIntKk k / 2) + 2 * compEllIntKk k := by ring
  rw [e, (jacobiSnk_shift hk _).2.2.2.1, (jacobiCnk_shift hk _).2.2.2.1,
    (jacobiDnk_shift hk _).2.2.2.1, jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk_neg,
    jacobiPQk_neg, jacobiPQk_neg, ← jacobiSnk, ← jacobiCnk, ← jacobiDnk, h1, h2, h3]
  simp

/-- `|Im a| < Re a` (argument in `(-π/4, π/4)`). -/
def P22R1Good (a : ℂ) : Prop := |a.im| < a.re

/-- The stated relation follows from the given hypotheses: `P22R1Good (w ^ (1 / 2 : ℂ))`. -/
lemma p22R1_good_sqrt {w : ℂ} (hw : 0 < w.re) : P22R1Good (w ^ (1 / 2 : ℂ)) := by
  have h := p22R1_sqrt_sq w
  have hr := p22R1_re_cpow_half_pos hw
  set a := w ^ (1 / 2 : ℂ)
  have : w.re = a.re ^ 2 - a.im ^ 2 := by rw [← h]; simp [pow_two]
  unfold P22R1Good
  rw [abs_lt]; constructor <;> nlinarith

/-- The stated relation follows from the given hypotheses: `P22R1Good a⁻¹`. -/
lemma p22R1_good_inv {a : ℂ} (ha : P22R1Good a) : P22R1Good a⁻¹ := by
  unfold P22R1Good at *
  have h0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hn := normSq_pos.mpr h0
  rw [inv_re, inv_im, neg_div, abs_neg, abs_div, abs_of_pos hn]
  exact div_lt_div_of_pos_right ha hn

/-- Estimate under the stated parameter and domain assumptions: `0 < a.re`. -/
lemma p22R1_good_re {a : ℂ} (ha : P22R1Good a) : 0 < a.re :=
  lt_of_le_of_lt (abs_nonneg _) ha

/-- Estimate under the stated parameter and domain assumptions: `0 < (a * b).re`. -/
lemma p22R1_good_mul_re {a b : ℂ} (ha : P22R1Good a) (hb : P22R1Good b) : 0 < (a * b).re := by
  unfold P22R1Good at ha hb
  rw [mul_re]
  have := abs_mul a.im b.im
  have h1 : a.im * b.im ≤ |a.im| * |b.im| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : |a.im| * |b.im| < a.re * b.re := mul_lt_mul'' ha hb (abs_nonneg _) (abs_nonneg _)
  linarith

/-- Uniqueness of a square root with positive real part. -/
lemma p22R1_sq_eq_of_re {a b : ℂ} (h : a ^ 2 = b ^ 2) (ha : 0 < a.re) (hb : 0 < b.re) :
    a = b := by
  have h' : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h' | h'
  · exact sub_eq_zero.mp h'
  · have := congrArg re h'; simp only [add_re, zero_re] at this; linarith

/-- Identity under the stated parameter and domain assumptions: `jacobiComodulusk
(jacobiComodulusk k) = k`. -/
lemma p22R1_comodulus_comodulus {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiComodulusk (jacobiComodulusk k) = k := by
  have hsl : k ^ 2 ∈ slitPlane := by
    rcases p22R1_sq_of_mem_domain hk with h | ⟨-, h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  rw [jacobiComodulusk, jacobiComodulusk_sq, sub_sub_cancel]
  exact p22R1_sq_eq_of_re (p22R1_sqrt_sq _) (p22R1_re_sqrt_pos hsl) hk.1

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = iK'/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (I * compEllIntKpk k / 2) k = I * k ^ (-(1 / 2) : ℂ) ∧
      jacobiCnk (I * compEllIntKpk k / 2) k = (1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ) ∧
      jacobiDnk (I * compEllIntKpk k / 2) k = (1 + k) ^ (1 / 2 : ℂ) := by
  have hk' := p22R1_comodulus_mem hk
  have hkk := p22R1_comodulus_comodulus hk
  obtain ⟨s1, c1, d1⟩ := jacobi_specialValues_HalfK hk'
  rw [hkk] at s1 c1 d1
  have hτ' := jacobiTauk_im_pos hk'
  have hreg : JacobiRegulark .n (compEllIntKk (jacobiComodulusk k) / 2) (jacobiComodulusk k) := by
    unfold JacobiRegulark; rw [p22R1_zeta_halfK hk']; exact p22R1_theta_quarter_ne hτ' _
  obtain ⟨-, -, -, hsc, hdc, hnc, -, -, -⟩ := je22a_glaisher_via_n hreg
  obtain ⟨t1, t2, t3, -⟩ := jacobi_imaginary_transformation hk
    (compEllIntKk (jacobiComodulusk k) / 2)
  have e : I * compEllIntKpk k / 2 = I * (compEllIntKk (jacobiComodulusk k) / 2) := by
    rw [p22R1_K_comodulus]; ring
  rw [e, t1, t2, t3, hsc, hdc, hnc, s1, c1, d1]
  have hk0 : k ≠ 0 := fun h => by have := hk.1; rw [h] at this; simp at this
  have hre1 : 0 < (1 + k).re := by simp only [add_re, one_re]; linarith [hk.1]
  have h1k : 1 + k ≠ 0 := fun h => by rw [h] at hre1; simp at hre1
  have hq := p22R1_re_div_one_add_pos hk.1
  have gS : P22R1Good ((1 + k) ^ (-(1 / 2) : ℂ)) := by
    rw [cpow_neg]; exact p22R1_good_inv (p22R1_good_sqrt hre1)
  have gC := p22R1_good_sqrt hq
  have gCi := p22R1_good_inv gC
  have gK : P22R1Good (k ^ (-(1 / 2) : ℂ)) := by
    rw [cpow_neg]; exact p22R1_good_inv (p22R1_good_sqrt hk.1)
  refine ⟨?_, ?_, ?_⟩
  · congr 1
    refine p22R1_sq_eq_of_re ?_ (by rw [div_eq_mul_inv]; exact p22R1_good_mul_re gS gCi)
      (p22R1_good_re gK)
    rw [div_pow, p22R1_cpow_neg_half_sq, p22R1_sqrt_sq, p22R1_cpow_neg_half_sq]
    field_simp
  · refine p22R1_sq_eq_of_re ?_ (by rw [one_div]; exact p22R1_good_re gCi)
      (p22R1_good_mul_re (p22R1_good_sqrt hre1) gK)
    rw [div_pow, mul_pow, p22R1_cpow_neg_half_sq, p22R1_sqrt_sq, p22R1_sqrt_sq]
    field_simp
  · have hr : 0 < (k ^ (1 / 2 : ℂ) / (k / (1 + k)) ^ (1 / 2 : ℂ)).re := by
      rw [div_eq_mul_inv]; exact p22R1_good_mul_re (p22R1_good_sqrt hk.1) gCi
    refine p22R1_sq_eq_of_re ?_ hr (p22R1_re_cpow_half_pos hre1)
    rw [div_pow, p22R1_sqrt_sq, p22R1_sqrt_sq, p22R1_sqrt_sq]
    field_simp

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = 3iK'/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (3 * (I * compEllIntKpk k) / 2) k = -(I * k ^ (-(1 / 2) : ℂ)) ∧
      jacobiCnk (3 * (I * compEllIntKpk k) / 2) k = -((1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ)) ∧
      jacobiDnk (3 * (I * compEllIntKpk k) / 2) k = -(1 + k) ^ (1 / 2 : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := jacobi_specialValues_HalfKp hk
  have e : 3 * (I * compEllIntKpk k) / 2 = -(I * compEllIntKpk k / 2) +
      2 * (I * compEllIntKpk k) := by ring
  rw [e, (jacobiSnk_shift hk _).2.2.2.2.2, (jacobiCnk_shift hk _).2.2.2.2.2,
    (jacobiDnk_shift hk _).2.2.2.2.2, jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk_neg,
    jacobiPQk_neg, jacobiPQk_neg, ← jacobiSnk, ← jacobiCnk, ← jacobiDnk, h1, h2, h3]
  simp

/-- Nonvanishing under the stated hypotheses: `jacobiThetaFourTau (((a : ℂ) + b * τ) * π) τ ≠ 0`. -/
lemma p22R1_theta4_ne {τ : ℂ} (hτ : 0 < τ.im) (a b : ℝ) (hb : ∀ n : ℤ, b ≠ n + 1 / 2) :
    jacobiThetaFourTau (((a : ℂ) + b * τ) * π) τ ≠ 0 := by
  rw [Ne, (DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ _).2.2.2]
  rintro ⟨m, n, h⟩
  have h' : ((a - m : ℝ) : ℂ) + ((b - (n + 1 / 2) : ℝ) : ℂ) * τ = 0 := by
    have := mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) h
    push_cast; linear_combination this
  have := DLMF.Theta.th20_lattice_eq_zero hτ (a := a - m) (b := b - (n + 1 / 2))
    (by rw [h', zero_mul])
  exact hb n (by linarith [this.2])

/-- The stated relation follows from the given hypotheses: `JacobiRegulark .n (I * compEllIntKpk k
/ 2) k`. -/
lemma p22R1_reg_halfKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    JacobiRegulark .n (I * compEllIntKpk k / 2) k := by
  have hτ := jacobiTauk_im_pos hk
  have hK := compEllIntKk_ne_zero hk
  unfold JacobiRegulark
  have hz : jacobiZetak (I * compEllIntKpk k / 2) k =
      (((0 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * jacobiTauk k) * π := by
    rw [jacobiZetak, jacobiTauk]; push_cast; field_simp; ring
  rw [hz, jacobiLetterTheta]
  refine div_ne_zero (p22R1_theta4_ne hτ 0 (1 / 4) fun n h => ?_)
    (je22a_thetaFour_zero_ne_zero hτ)
  have h1 : (4 * n + 1 : ℝ) = 0 := by linarith
  have h2 : (4 * n + 1 : ℤ) = 0 := by exact_mod_cast h1
  omega

/-- The stated relation follows from the given hypotheses: `JacobiRegulark r (compEllIntKk k / 2)
k`. -/
lemma p22R1_reg_halfK {k : ℂ} (hk : k ∈ jacobiModulusDomain) (r : JacobiLetter) :
    JacobiRegulark r (compEllIntKk k / 2) k := by
  unfold JacobiRegulark; rw [p22R1_zeta_halfK hk]
  exact p22R1_theta_quarter_ne (jacobiTauk_im_pos hk) r

/-- `k + k' ≠ -1`, so `1 + k + k' ≠ 0`. -/
lemma p22R1_one_add_add_ne {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    1 + k + jacobiComodulusk k ≠ 0 := fun h => by
  have := congrArg re h
  simp only [add_re, one_re, zero_re] at this
  linarith [hk.1, p22R1_comodulus_re_pos hk]

/-- Positive reals. -/
def P22R1PR (a : ℂ) : Prop := a.im = 0 ∧ 0 < a.re

/-- The stated relation follows from the given hypotheses: `P22R1PR (a * b)`. -/
lemma p22R1_PR_mul {a b : ℂ} (ha : P22R1PR a) (hb : P22R1PR b) : P22R1PR (a * b) := by
  unfold P22R1PR at *; simp [mul_re, mul_im, ha.1, hb.1, mul_pos ha.2 hb.2]

/-- The stated relation follows from the given hypotheses: `P22R1PR (a + b)`. -/
lemma p22R1_PR_add {a b : ℂ} (ha : P22R1PR a) (hb : P22R1PR b) : P22R1PR (a + b) := by
  unfold P22R1PR at *; simp [ha.1, hb.1]; linarith [ha.2, hb.2]

/-- The stated relation follows from the given hypotheses: `P22R1PR a⁻¹`. -/
lemma p22R1_PR_inv {a : ℂ} (ha : P22R1PR a) : P22R1PR a⁻¹ := by
  unfold P22R1PR at *
  have h0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  refine ⟨by simp [inv_im, ha.1], ?_⟩
  rw [inv_re]; exact div_pos ha.2 (normSq_pos.mpr h0)

/-- The stated relation follows from the given hypotheses: `P22R1PR (a / b)`. -/
lemma p22R1_PR_div {a b : ℂ} (ha : P22R1PR a) (hb : P22R1PR b) : P22R1PR (a / b) := by
  rw [div_eq_mul_inv]; exact p22R1_PR_mul ha (p22R1_PR_inv hb)

/-- The stated relation follows from the given hypotheses: `P22R1PR (a ^ (c : ℂ))`. -/
lemma p22R1_PR_cpow {a : ℂ} (ha : P22R1PR a) (c : ℝ) : P22R1PR (a ^ (c : ℂ)) := by
  have e : a = (a.re : ℂ) := by apply Complex.ext <;> simp [ha.1]
  rw [e, ← ofReal_cpow ha.2.le]
  exact ⟨ofReal_im _, by rw [ofReal_re]; exact Real.rpow_pos_of_pos ha.2 _⟩

/-- The stated relation follows from the given hypotheses: `P22R1PR 1`. -/
lemma p22R1_PR_one : P22R1PR 1 := ⟨by simp, by simp⟩

/-- The stated relation follows from the given hypotheses: `P22R1PR (x : ℂ)`. -/
lemma p22R1_PR_ofReal {x : ℝ} (hx : 0 < x) : P22R1PR (x : ℂ) := ⟨ofReal_im _, by simpa⟩

/-- The stated relation follows from the given hypotheses: `P22R1PR (jacobiComodulusk x)`. -/
lemma p22R1_PR_comodulus {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    P22R1PR (jacobiComodulusk x) := by
  have : (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [jacobiComodulusk, this, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
  exact p22R1_PR_cpow (p22R1_PR_ofReal (by nlinarith)) _

/-- Identity under the stated parameter and domain assumptions: `(a + I * b).re = a.re`. -/
lemma p22R1_PR_re_add_I_mul {a b : ℂ} (hb : P22R1PR b) :
    (a + I * b).re = a.re := by
  simp [hb.1]

/-- The values at `(K + iK')/2` from the addition theorem, in terms of the half-period values. -/
lemma p22R1_halfKKp_add {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    let κ := jacobiComodulusk k
    let S := (1 + κ) ^ (-(1 / 2) : ℂ)
    let Q := k ^ (-(1 / 2) : ℂ)
    let A := (1 + k) ^ (1 / 2 : ℂ)
    let D := κ ^ (1 / 2 : ℂ)
    jacobiSnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k =
        S * Q * (1 + k) * (1 + κ) / (1 + k + κ) + I * (S * Q * κ * (1 + κ) / (1 + k + κ)) ∧
      jacobiCnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k =
        S * D * A * Q * (1 + κ) / (1 + k + κ) - I * (S * D * A * Q * (1 + κ) / (1 + k + κ)) ∧
      jacobiDnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k =
        D * A * (1 + κ) / (1 + k + κ) - I * (D * A * k / (1 + k + κ)) := by
  intro κ S Q A D
  obtain ⟨s1, -, d1⟩ := jacobi_specialValues_HalfK hk
  obtain ⟨-, -, hc1⟩ := p22R1_halfK_alg hk
  obtain ⟨s2, c2, d2⟩ := jacobi_specialValues_HalfKp hk
  have hu := p22R1_reg_halfK hk .n
  have hv := p22R1_reg_halfKp hk
  have e : (compEllIntKk k + I * compEllIntKpk k) / 2 =
      compEllIntKk k / 2 + I * compEllIntKpk k / 2 := by ring
  have hk0 : k ≠ 0 := fun h => by have := hk.1; rw [h] at this; simp at this
  have hre1 : 0 < (1 + κ).re := by simp only [add_re, one_re]; linarith [p22R1_comodulus_re_pos hk]
  have h1κ : 1 + κ ≠ 0 := fun h => by rw [h] at hre1; simp at hre1
  have hSS : S ^ 2 * (1 + κ) = 1 := by
    simp only [S]; rw [p22R1_cpow_neg_half_sq]; field_simp
  have hQQ : Q ^ 2 * k = 1 := by simp only [Q]; rw [p22R1_cpow_neg_half_sq]; field_simp
  have hAA : A ^ 2 = 1 + k := p22R1_sqrt_sq _
  have hDD : D ^ 2 = κ := p22R1_sqrt_sq _
  have hκκ : κ ^ 2 = 1 - k ^ 2 := jacobiComodulusk_sq k
  have hI : I ^ 2 = -1 := I_sq
  have h3 := p22R1_one_add_add_ne hk
  have s1' : jacobiSnk (compEllIntKk k / 2) k = S := s1
  have d1' : jacobiDnk (compEllIntKk k / 2) k = D := d1
  have s2' : jacobiSnk (I * compEllIntKpk k / 2) k = I * Q := s2
  have c2' : jacobiCnk (I * compEllIntKpk k / 2) k = A * Q := c2
  have d2' : jacobiDnk (I * compEllIntKpk k / 2) k = A := d2
  rw [s1', d1'] at hc1
  have hden0 : (1 - k ^ 2 * S ^ 2 * (I * Q) ^ 2) * (1 + κ) = 1 + k + κ := by
    linear_combination (-k ^ 2 * Q ^ 2 * I ^ 2) * hSS - k ^ 2 * Q ^ 2 * hI + k * hQQ
  have hden : 1 - k ^ 2 * jacobiSnk (compEllIntKk k / 2) k ^ 2 *
      jacobiSnk (I * compEllIntKpk k / 2) k ^ 2 ≠ 0 := by
    rw [s1', s2']; intro h; rw [h, zero_mul] at hden0; exact h3 hden0.symm
  rw [e, jacobiSnk_add hk hu hv hden, jacobiCnk_add hk hu hv hden, jacobiDnk_add hk hu hv hden,
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

/-- The stated relation follows from the given hypotheses: `P22R1PR (a ^ (1 / 2 : ℂ)) ∧ P22R1PR
(a ^ (-(1 / 2) : ℂ))`. -/
lemma p22R1_PR_half {a : ℂ} (ha : P22R1PR a) :
    P22R1PR (a ^ (1 / 2 : ℂ)) ∧ P22R1PR (a ^ (-(1 / 2) : ℂ)) := by
  constructor
  · rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]; exact p22R1_PR_cpow ha _
  · rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring]; exact p22R1_PR_cpow ha _

/-- Real data at a real modulus `0 < x < 1`. -/
lemma p22R1_real_atoms {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    let κ := jacobiComodulusk x
    P22R1PR (x : ℂ) ∧ P22R1PR κ ∧ P22R1PR ((1 + κ) ^ (-(1 / 2) : ℂ)) ∧
      P22R1PR ((x : ℂ) ^ (-(1 / 2) : ℂ)) ∧ P22R1PR ((1 + (x : ℂ)) ^ (1 / 2 : ℂ)) ∧
      P22R1PR (κ ^ (1 / 2 : ℂ)) ∧ P22R1PR ((1 - (x : ℂ)) ^ (1 / 2 : ℂ)) ∧
      P22R1PR ((2 * (x : ℂ)) ^ (1 / 2 : ℂ)) ∧
      (1 + (x : ℂ)) ^ (1 / 2 : ℂ) * (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = κ := by
  intro κ
  have hx := p22R1_PR_ofReal h0
  have hκ := p22R1_PR_comodulus h0 h1
  have h1x : P22R1PR (1 + (x : ℂ)) := p22R1_PR_add p22R1_PR_one hx
  have h1mx : P22R1PR (1 - (x : ℂ)) := by
    rw [show (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
    exact p22R1_PR_ofReal (by linarith)
  have h2x : P22R1PR (2 * (x : ℂ)) := by
    rw [show (2 * (x : ℂ)) = ((2 * x : ℝ) : ℂ) by push_cast; ring]
    exact p22R1_PR_ofReal (by linarith)
  refine ⟨hx, hκ, (p22R1_PR_half (p22R1_PR_add p22R1_PR_one hκ)).2, (p22R1_PR_half hx).2,
    (p22R1_PR_half h1x).1, (p22R1_PR_half hκ).1, (p22R1_PR_half h1mx).1,
    (p22R1_PR_half h2x).1, ?_⟩
  refine p22R1_sq_eq_of_re ?_ (p22R1_PR_mul (p22R1_PR_half h1x).1 (p22R1_PR_half h1mx).1).2 hκ.2
  rw [mul_pow, p22R1_sqrt_sq, p22R1_sqrt_sq, jacobiComodulusk_sq]; ring

/-- Identity under the stated parameter and domain assumptions: `(a + I * b).re = a.re`. -/
lemma p22R1_re_add_I_mul' {a b : ℂ} (hb : b.im = 0) : (a + I * b).re = a.re := by simp [hb]

/-- Identity under the stated parameter and domain assumptions: `(a - I * b).re = a.re`. -/
lemma p22R1_re_sub_I_mul' {a b : ℂ} (hb : b.im = 0) : (a - I * b).re = a.re := by simp [hb]

/-- Differentiability throughout the specified domain: `DifferentiableOn ℂ (fun k => h k ^ c)
jacobiModulusDomain`. -/
lemma p22R1_diffOn_cpow {h : ℂ → ℂ} (c : ℂ)
    (hd : ∀ k ∈ jacobiModulusDomain, DifferentiableAt ℂ h k)
    (hs : ∀ k ∈ jacobiModulusDomain, h k ∈ slitPlane) :
    DifferentiableOn ℂ (fun k => h k ^ c) jacobiModulusDomain := fun k hk =>
  ((hd k hk).cpow_const (hs k hk)).differentiableWithinAt

/-- Formula under the stated hypotheses: `1 - k ∈ slitPlane`. -/
lemma p22R1_one_sub_slit {k : ℂ} (hk : k ∈ jacobiModulusDomain) : 1 - k ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : k.im = 0
  · left; simp only [sub_re, one_re]; linarith [hk.2 h]
  · right; simpa using h

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = (K + iK')/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_HalfKKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k =
        ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiCnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k = (1 - I) * jacobiComodulusk k ^
          (1 / 2 : ℂ) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiDnk ((compEllIntKk k + I * compEllIntKpk k) / 2) k = (1 - I) / 2 * jacobiComodulusk k ^
          (1 / 2 : ℂ) * ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) := by
  obtain ⟨e1, e2, e3⟩ := p22R1_halfKKp_add hk
  rw [e1, e2, e3]
  have Dom := jacobiModulusDomain
  -- differentiability of the building blocks
  have dκ : ∀ k ∈ jacobiModulusDomain, DifferentiableAt ℂ jacobiComodulusk k :=
    fun k hk => p22R1_differentiableAt_comodulus hk
  have slit_re : ∀ {w : ℂ}, 0 < w.re → w ∈ slitPlane := fun h => Or.inl h
  have re1κ : ∀ k ∈ jacobiModulusDomain, 0 < (1 + jacobiComodulusk k).re := fun k hk => by
    simp only [add_re, one_re]; linarith [p22R1_comodulus_re_pos hk]
  have re1k : ∀ k ∈ jacobiModulusDomain, 0 < (1 + k).re := fun k hk => by
    simp only [add_re, one_re]; linarith [hk.1]
  have re2k : ∀ k ∈ jacobiModulusDomain, 0 < (2 * k).re := fun k hk => by
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith [hk.1]
  have dS := p22R1_diffOn_cpow (h := fun k => 1 + jacobiComodulusk k) (-(1 / 2))
    (fun k hk => (dκ k hk).const_add 1) fun k hk => slit_re (re1κ k hk)
  have dQ := p22R1_diffOn_cpow (h := fun k => k) (-(1 / 2))
    (fun k _ => differentiableAt_id) fun k hk => slit_re hk.1
  have dA := p22R1_diffOn_cpow (h := fun k => 1 + k) (1 / 2)
    (fun k _ => differentiableAt_id.const_add 1) fun k hk => slit_re (re1k k hk)
  have dD := p22R1_diffOn_cpow (h := jacobiComodulusk) (1 / 2) dκ
    fun k hk => slit_re (p22R1_comodulus_re_pos hk)
  have dB := p22R1_diffOn_cpow (h := fun k => 1 - k) (1 / 2)
    (fun k _ => (differentiableAt_const _).sub differentiableAt_id) fun k hk => p22R1_one_sub_slit hk
  have dC := p22R1_diffOn_cpow (h := fun k => 2 * k) (1 / 2)
    (fun k _ => differentiableAt_id.const_mul 2) fun k hk => slit_re (re2k k hk)
  have dK : DifferentiableOn ℂ jacobiComodulusk jacobiModulusDomain :=
    fun k hk => (dκ k hk).differentiableWithinAt
  have dId : DifferentiableOn ℂ (fun k : ℂ => k) jacobiModulusDomain := differentiableOn_id
  have dN : DifferentiableOn ℂ (fun k => 1 + k + jacobiComodulusk k) jacobiModulusDomain :=
    (dId.const_add 1).add dK
  have hN := fun k (hk : k ∈ jacobiModulusDomain) => p22R1_one_add_add_ne hk
  have hC0 : ∀ k ∈ jacobiModulusDomain, (2 * k) ^ (1 / 2 : ℂ) ≠ 0 := fun k hk h => by
    have := p22R1_re_cpow_half_pos (re2k k hk); rw [h] at this; simp at this
  refine ⟨?_, ?_, ?_⟩
  · refine p22R1_branch
      (f := fun k => (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) * k ^ (-(1 / 2) : ℂ) * (1 + k) *
        (1 + jacobiComodulusk k) / (1 + k + jacobiComodulusk k) +
        I * ((1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) * k ^ (-(1 / 2) : ℂ) * jacobiComodulusk k *
        (1 + jacobiComodulusk k) / (1 + k + jacobiComodulusk k)))
      (g := fun k => ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) / (2 * k) ^ (1 / 2 : ℂ))
      ?_ ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · exact ((((dS.mul dQ).mul (dId.const_add 1)).mul (dK.const_add 1)).div dN hN).add
        (((((dS.mul dQ).mul dK).mul (dK.const_add 1)).div dN hN).const_mul I)
    · exact (dA.add (dB.const_mul I)).div dC hC0
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have hN0 := hN x (p22R1_ofReal_mem h0 h1)
      have hC00 := hC0 x (p22R1_ofReal_mem h0 h1)
      have hSS : ((1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ)) ^ 2 * (1 + jacobiComodulusk x) = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (fun h => by
          have := (p22R1_PR_add p22R1_PR_one hκ).2; rw [h] at this; simp at this)
      have hQQ : ((x : ℂ) ^ (-(1 / 2) : ℂ)) ^ 2 * x = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (by exact_mod_cast h0.ne')
      have hBB := p22R1_sqrt_sq (1 - (x : ℂ))
      have hCC := p22R1_sqrt_sq (2 * (x : ℂ))
      have hAA := p22R1_sqrt_sq (1 + (x : ℂ))
      have hκκ := jacobiComodulusk_sq (x : ℂ)
      have hI : I ^ 2 = -1 := I_sq
      generalize (1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ) = S at *
      generalize (x : ℂ) ^ (-(1 / 2) : ℂ) = Q at *
      generalize (1 + (x : ℂ)) ^ (1 / 2 : ℂ) = A at *
      generalize (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = B at *
      generalize (2 * (x : ℂ)) ^ (1 / 2 : ℂ) = C at *
      generalize jacobiComodulusk x = κ at *
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
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      rw [p22R1_re_add_I_mul' (p22R1_PR_div (p22R1_PR_mul (p22R1_PR_mul (p22R1_PR_mul hS hQ) hκ)
        (p22R1_PR_add p22R1_PR_one hκ)) (p22R1_PR_add (p22R1_PR_add p22R1_PR_one hx) hκ)).1]
      exact (p22R1_PR_div (p22R1_PR_mul (p22R1_PR_mul (p22R1_PR_mul hS hQ)
        (p22R1_PR_add p22R1_PR_one hx)) (p22R1_PR_add p22R1_PR_one hκ))
        (p22R1_PR_add (p22R1_PR_add p22R1_PR_one hx) hκ)).2
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      rw [add_div, mul_div_assoc, p22R1_re_add_I_mul' (p22R1_PR_div hB hC).1]
      exact (p22R1_PR_div hA hC).2
  · refine p22R1_branch
      (f := fun k => (1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) * jacobiComodulusk k ^ (1 / 2 : ℂ) *
        (1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ) * (1 + jacobiComodulusk k) /
        (1 + k + jacobiComodulusk k) - I * ((1 + jacobiComodulusk k) ^ (-(1 / 2) : ℂ) *
        jacobiComodulusk k ^ (1 / 2 : ℂ) * (1 + k) ^ (1 / 2 : ℂ) * k ^ (-(1 / 2) : ℂ) *
        (1 + jacobiComodulusk k) / (1 + k + jacobiComodulusk k)))
      (g := fun k => (1 - I) * jacobiComodulusk k ^ (1 / 2 : ℂ) / (2 * k) ^ (1 / 2 : ℂ))
      ?_ ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · have h := (((((dS.mul dD).mul dA).mul dQ).mul (dK.const_add 1)).div dN hN)
      exact h.sub (h.const_mul I)
    · exact (dD.const_mul (1 - I)).div dC hC0
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have hN0 := hN x (p22R1_ofReal_mem h0 h1)
      have hC00 := hC0 x (p22R1_ofReal_mem h0 h1)
      have hSS : ((1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ)) ^ 2 * (1 + jacobiComodulusk x) = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (fun h => by
          have := (p22R1_PR_add p22R1_PR_one hκ).2; rw [h] at this; simp at this)
      have hQQ : ((x : ℂ) ^ (-(1 / 2) : ℂ)) ^ 2 * x = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (by exact_mod_cast h0.ne')
      have hBB := p22R1_sqrt_sq (1 - (x : ℂ))
      have hCC := p22R1_sqrt_sq (2 * (x : ℂ))
      have hAA := p22R1_sqrt_sq (1 + (x : ℂ))
      have hDD := p22R1_sqrt_sq (jacobiComodulusk x)
      have hκκ := jacobiComodulusk_sq (x : ℂ)
      have hI : I ^ 2 = -1 := I_sq
      generalize (1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ) = S at *
      generalize (x : ℂ) ^ (-(1 / 2) : ℂ) = Q at *
      generalize (1 + (x : ℂ)) ^ (1 / 2 : ℂ) = A at *
      generalize (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = B at *
      generalize (2 * (x : ℂ)) ^ (1 / 2 : ℂ) = C at *
      generalize jacobiComodulusk x ^ (1 / 2 : ℂ) = D at *
      generalize jacobiComodulusk x = κ at *
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
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have h := p22R1_PR_div (p22R1_PR_mul (p22R1_PR_mul (p22R1_PR_mul (p22R1_PR_mul hS hD) hA) hQ)
        (p22R1_PR_add p22R1_PR_one hκ)) (p22R1_PR_add (p22R1_PR_add p22R1_PR_one hx) hκ)
      rw [p22R1_re_sub_I_mul' h.1]; exact h.2
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      rw [show ∀ a b : ℂ, (1 - I) * a / b = a / b - I * (a / b) from fun a b => by ring,
        p22R1_re_sub_I_mul' (p22R1_PR_div hD hC).1]
      exact (p22R1_PR_div hD hC).2
  · refine p22R1_branch
      (f := fun k => jacobiComodulusk k ^ (1 / 2 : ℂ) * (1 + k) ^ (1 / 2 : ℂ) *
        (1 + jacobiComodulusk k) / (1 + k + jacobiComodulusk k) -
        I * (jacobiComodulusk k ^ (1 / 2 : ℂ) * (1 + k) ^ (1 / 2 : ℂ) * k /
        (1 + k + jacobiComodulusk k)))
      (g := fun k => (1 - I) / 2 * jacobiComodulusk k ^ (1 / 2 : ℂ) *
        ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)))
      ?_ ?_ (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) (fun x h0 h1 => ?_) hk
    · exact ((((dD.mul dA).mul (dK.const_add 1)).div dN hN)).sub
        ((((dD.mul dA).mul dId).div dN hN).const_mul I)
    · exact (dD.const_mul ((1 - I) / 2)).mul (dA.add (dB.const_mul I))
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have hN0 := hN x (p22R1_ofReal_mem h0 h1)
      have hC00 := hC0 x (p22R1_ofReal_mem h0 h1)
      have hSS : ((1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ)) ^ 2 * (1 + jacobiComodulusk x) = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (fun h => by
          have := (p22R1_PR_add p22R1_PR_one hκ).2; rw [h] at this; simp at this)
      have hQQ : ((x : ℂ) ^ (-(1 / 2) : ℂ)) ^ 2 * x = 1 := by
        rw [p22R1_cpow_neg_half_sq]; exact inv_mul_cancel₀ (by exact_mod_cast h0.ne')
      have hBB := p22R1_sqrt_sq (1 - (x : ℂ))
      have hCC := p22R1_sqrt_sq (2 * (x : ℂ))
      have hAA := p22R1_sqrt_sq (1 + (x : ℂ))
      have hDD := p22R1_sqrt_sq (jacobiComodulusk x)
      have hκκ := jacobiComodulusk_sq (x : ℂ)
      have hI : I ^ 2 = -1 := I_sq
      generalize (1 + jacobiComodulusk x) ^ (-(1 / 2) : ℂ) = S at *
      generalize (x : ℂ) ^ (-(1 / 2) : ℂ) = Q at *
      generalize (1 + (x : ℂ)) ^ (1 / 2 : ℂ) = A at *
      generalize (1 - (x : ℂ)) ^ (1 / 2 : ℂ) = B at *
      generalize (2 * (x : ℂ)) ^ (1 / 2 : ℂ) = C at *
      generalize jacobiComodulusk x ^ (1 / 2 : ℂ) = D at *
      generalize jacobiComodulusk x = κ at *
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
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have h := p22R1_PR_div (p22R1_PR_mul (p22R1_PR_mul hD hA) (p22R1_PR_add p22R1_PR_one hκ))
        (p22R1_PR_add (p22R1_PR_add p22R1_PR_one hx) hκ)
      have h' := p22R1_PR_div (p22R1_PR_mul (p22R1_PR_mul hD hA) hx)
        (p22R1_PR_add (p22R1_PR_add p22R1_PR_one hx) hκ)
      rw [p22R1_re_sub_I_mul' h'.1]; exact h.2
    · obtain ⟨hx, hκ, hS, hQ, hA, hD, hB, hC, hAB⟩ := p22R1_real_atoms h0 h1
      have e : ∀ D A B : ℂ, (1 - I) / 2 * D * (A + I * B) = D * (A + B) / 2 + I * (D * (B - A) / 2) :=
        fun D A B => by linear_combination (-(D * B) / 2) * I_sq
      have h2 : P22R1PR (2 : ℂ) := ⟨by simp, by norm_num⟩
      rw [e, p22R1_re_add_I_mul' (by simp only [div_ofNat_im, mul_im, sub_im, sub_re, hD.1, hA.1, hB.1]; ring)]
      exact (p22R1_PR_div (p22R1_PR_mul hD (p22R1_PR_add hA hB)) h2).2

/-- Table 22.5.2: `sn`, `cn`, `dn` at `z = 3(K + iK')/2` (principal powers). -/
@[dlmf 22.5.T2]
theorem jacobi_specialValues_ThreeHalfKKp {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiSnk (3 * (compEllIntKk k + I * compEllIntKpk k) / 2) k =
        ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiCnk (3 * (compEllIntKk k + I * compEllIntKpk k) / 2) k = (1 - I) * jacobiComodulusk k ^
          (1 / 2 : ℂ) / (2 * k) ^ (1 / 2 : ℂ) ∧
      jacobiDnk (3 * (compEllIntKk k + I * compEllIntKpk k) / 2) k = (I - 1) / 2 * jacobiComodulusk
          k ^ (1 / 2 : ℂ) * ((1 + k) ^ (1 / 2 : ℂ) + I * (1 - k) ^ (1 / 2 : ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := jacobi_specialValues_HalfKKp hk
  have e : 3 * (compEllIntKk k + I * compEllIntKpk k) / 2 =
      -((compEllIntKk k + I * compEllIntKpk k) / 2) + 2 * compEllIntKk k +
        2 * (I * compEllIntKpk k) := by ring
  rw [e, (jacobiSnk_shift hk _).2.2.2.2.1, (jacobiCnk_shift hk _).2.2.2.2.1,
    (jacobiDnk_shift hk _).2.2.2.2.1, jacobiSnk, jacobiCnk, jacobiDnk, jacobiPQk_neg,
    jacobiPQk_neg, jacobiPQk_neg, ← jacobiSnk, ← jacobiCnk, ← jacobiDnk, h1, h2, h3]
  refine ⟨by simp, by simp, ?_⟩
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false, ↓reduceIte]
  ring

/-- §22.5(ii): `K(k) → π/2` as real `k → 0+`. -/
@[dlmf 22.5.ii]
theorem tendsto_compEllIntKk_zero :
    Tendsto (fun k : ℝ => compEllIntKk k) (𝓝[>] 0) (𝓝 (π / 2)) := by
  have hc : ContinuousAt (fun k : ℝ => (Real.compEllIntKm (k ^ 2) : ℂ)) 0 := by
    refine Complex.continuous_ofReal.continuousAt.comp ?_
    have h1 : ContinuousAt Real.compEllIntKm ((0 : ℝ) ^ 2) :=
      Real.continuousAt_compEllIntKm (by norm_num)
    exact h1.comp (f := fun k : ℝ => k ^ 2) (continuous_pow 2).continuousAt
  have h := hc.tendsto
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Real.compEllIntKm_zero,
    ofReal_div, ofReal_ofNat] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
  rw [compEllIntKk_ofReal (by nlinarith [hk.1, hk.2])]

/-- §22.5(ii): `K'(k) → π/2` as real `k → 1-`. -/
@[dlmf 22.5.ii]
theorem tendsto_compEllIntKpk_one :
    Tendsto (fun k : ℝ => compEllIntKpk k) (𝓝[<] 1) (𝓝 (π / 2)) := by
  have hc : ContinuousAt (fun k : ℝ => (Real.compEllIntKm (1 - k ^ 2) : ℂ)) 1 := by
    refine Complex.continuous_ofReal.continuousAt.comp ?_
    have h1 : ContinuousAt Real.compEllIntKm (1 - (1 : ℝ) ^ 2) :=
      Real.continuousAt_compEllIntKm (by norm_num)
    exact h1.comp (f := fun k : ℝ => 1 - k ^ 2)
        (continuous_const.sub (continuous_pow 2)).continuousAt
  have h := hc.tendsto
  simp only [one_pow, sub_self, Real.compEllIntKm_zero, ofReal_div, ofReal_ofNat] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
  rw [compEllIntKpk_ofReal (by nlinarith [hk.1, hk.2])]

/-- Logarithmic lower bound `K(1 - δ²) ≥ log(π/(2δ))/√2` for `0 < δ < π/2`. -/
lemma p22R1_K_ge {δ : ℝ} (h0 : 0 < δ) (h1 : δ < π / 2) :
    Real.log (π / 2 / δ) / √2 ≤ Real.compEllIntKm (1 - δ ^ 2) := by
  have hm : 1 - δ ^ 2 < 1 := by nlinarith
  set f : ℝ → ℝ := fun θ => (1 - (1 - δ ^ 2) * Real.sin θ ^ 2) ^ (-(1 / 2) : ℝ) with hf
  have hfc : Continuous f := continuous_one_sub_mul_sin_sq_rpow hm _
  have hfpos : ∀ θ, 0 ≤ f θ := fun θ => Real.rpow_nonneg (one_sub_mul_sin_sq_pos hm θ).le _
  have hs2 : 0 < √2 := by positivity
  -- restrict to `[0, π/2 - δ]`
  have hsub : ∫ θ in (0 : ℝ)..(π / 2 - δ), f θ ≤ Real.compEllIntKm (1 - δ ^ 2) := by
    rw [Real.compEllIntKm]
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
lemma p22R1_log_tendsto :
    Tendsto (fun δ : ℝ => Real.log (π / 2 / δ) / √2) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun δ : ℝ => π / 2 / δ) (𝓝[>] 0) atTop := by
    simp_rw [div_eq_mul_inv (π / 2)]
    exact tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
  exact (Real.tendsto_log_atTop.comp h1).atTop_div_const (by positivity)

/-- §22.5(ii): `K'(k) → ∞` as real `k → 0+`. -/
@[dlmf 22.5.ii]
theorem tendsto_norm_compEllIntKpk_zero :
    Tendsto (fun k : ℝ => ‖compEllIntKpk k‖) (𝓝[>] 0) Filter.atTop := by
  refine tendsto_atTop_mono' _ ?_ p22R1_log_tendsto
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
  have hk2 : 0 < k ^ 2 := by nlinarith [hk.1]
  rw [compEllIntKpk_ofReal hk2, Complex.norm_real, Real.norm_eq_abs]
  exact (p22R1_K_ge hk.1 (by linarith [hk.2, Real.pi_gt_three])).trans (le_abs_self _)

/-- §22.5(ii): `K(k) → ∞` as real `k → 1-`. -/
@[dlmf 22.5.ii]
theorem tendsto_norm_compEllIntKk_one :
    Tendsto (fun k : ℝ => ‖compEllIntKk k‖) (𝓝[<] 1) Filter.atTop := by
  have hδ : Tendsto (fun k : ℝ => √(1 - k ^ 2)) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun k : ℝ => √(1 - k ^ 2)) (𝓝 1) (𝓝 (√(1 - 1 ^ 2))) :=
        ((continuous_const.sub (continuous_pow 2)).sqrt).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
      exact Real.sqrt_pos.mpr (by nlinarith [hk.1, hk.2])
  refine tendsto_atTop_mono' _ ?_ (p22R1_log_tendsto.comp hδ)
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with k hk
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  have hpos : 0 < 1 - k ^ 2 := by linarith
  have hd0 : 0 < √(1 - k ^ 2) := Real.sqrt_pos.mpr hpos
  have hd1 : √(1 - k ^ 2) < π / 2 := by
    have : √(1 - k ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
    linarith [Real.pi_gt_three]
  have h := p22R1_K_ge hd0 hd1
  rw [Real.sq_sqrt hpos.le, show 1 - (1 - k ^ 2) = k ^ 2 by ring] at h
  rw [compEllIntKk_ofReal hk2, Complex.norm_real, Real.norm_eq_abs]
  exact h.trans (le_abs_self _)

end DLMF.JacobiElliptic
end
end
