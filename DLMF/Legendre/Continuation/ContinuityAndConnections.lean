/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Continuation.Monodromy

/-!
# Continuity of continued Legendre connection formulas

Continuity and linear connection arguments complete the logarithmic-plane continuation
identities.

Source references and common attribution are retained in
`DLMF.Legendre.Continuation`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat ComplexConjugate

namespace DLMF.Legendre

/-! ### Helpers for DLMF 14.24.1 and 14.24.4: continuity and linearity of the transport (prefix `legTr_`) -/

/-- Gronwall step for `legTr_transport_tendsto`: the second component of the difference system. -/
theorem legTr_diff_bound {g γ q α β α0 β0 ux vx u v : ℂ} {G Γ0 Qi A B U : ℝ}
    (hg : ‖g‖ ≤ G) (hγ : ‖γ‖ ≤ Γ0) (hq : ‖q⁻¹‖ ≤ Qi) (hα : ‖α‖ ≤ A) (hβ : ‖β‖ ≤ B) (hu : ‖u‖ ≤ U)
    (hG : 0 ≤ G) (hQi : 0 ≤ Qi) (hΓ : 0 ≤ Γ0) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ‖g*(2*γ*vx-(α-β/q)*ux)/q - g*(2*γ*v-(α0-β0/q)*u)/q‖ ≤
      G*Qi*(2*Γ0 + A + B*Qi) * max ‖ux-u‖ ‖vx-v‖ + G*Qi*(‖α-α0‖+‖β-β0‖*Qi)*U := by
  have e : g*(2*γ*vx-(α-β/q)*ux)/q - g*(2*γ*v-(α0-β0/q)*u)/q =
      g*q⁻¹*(2*γ*(vx-v) - (α - β*q⁻¹)*(ux-u) - ((α-α0) - (β-β0)*q⁻¹)*u) := by ring
  rw [e, norm_mul, norm_mul]
  set M := max ‖ux-u‖ ‖vx-v‖
  have h1 : ‖ux-u‖ ≤ M := le_max_left _ _
  have h2 : ‖vx-v‖ ≤ M := le_max_right _ _
  have hM : 0 ≤ M := le_trans (norm_nonneg _) h1
  have hin : ‖2*γ*(vx-v) - (α - β*q⁻¹)*(ux-u) - ((α-α0) - (β-β0)*q⁻¹)*u‖ ≤
      (2*Γ0 + A + B*Qi)*M + (‖α-α0‖+‖β-β0‖*Qi)*U := by
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
    have t1 : ‖2*γ*(vx-v)‖ ≤ 2*Γ0*M := by
      rw [norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
      exact mul_le_mul (by linarith) h2 (norm_nonneg _) (by linarith)
    have t2 : ‖(α - β*q⁻¹)*(ux-u)‖ ≤ (A + B*Qi)*M := by
      rw [norm_mul]
      refine mul_le_mul ((norm_sub_le _ _).trans ?_) h1 (norm_nonneg _) (by positivity)
      rw [norm_mul]; exact add_le_add hα (mul_le_mul hβ hq (norm_nonneg _) hB)
    have t3 : ‖((α-α0) - (β-β0)*q⁻¹)*u‖ ≤ (‖α-α0‖+‖β-β0‖*Qi)*U := by
      rw [norm_mul]
      refine mul_le_mul ((norm_sub_le _ _).trans ?_) hu (norm_nonneg _) (by positivity)
      rw [norm_mul]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hq (norm_nonneg _))
    nlinarith
  calc ‖g‖ * ‖q⁻¹‖ * ‖2*γ*(vx-v) - (α - β*q⁻¹)*(ux-u) - ((α-α0) - (β-β0)*q⁻¹)*u‖
      ≤ G * Qi * ((2*Γ0 + A + B*Qi)*M + (‖α-α0‖+‖β-β0‖*Qi)*U) := by
        gcongr
    _ = _ := by ring

/-- Continuous dependence of the Legendre transport on the degree, the order and the initial
data (Gronwall). -/
theorem legTr_transport_tendsto {X : Type*} {l : Filter X} {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hreg : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 1 ∧ γ t ≠ -1) {νf μf af bf : X → ℂ} {ν μ a b : ℂ}
    (hν : Tendsto νf l (𝓝 ν)) (hμ : Tendsto μf l (𝓝 μ)) (ha : Tendsto af l (𝓝 a))
    (hb : Tendsto bf l (𝓝 b)) :
    Tendsto (fun x => legendreTransport (νf x) (μf x) γ (af x) (bf x)) l
      (𝓝 (legendreTransport ν μ γ a b)) := by
  have hne : ∀ t ∈ Icc (0:ℝ) 1, 1 - γ t ^ 2 ≠ 0 := fun t ht h0 => by
    have : (1 - γ t) * (1 + γ t) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact (hreg t ht).1 (by linear_combination -h)
    · exact (hreg t ht).2 (by linear_combination h)
  have hγc : Continuous γ := hγ.continuous
  have hγ'c : Continuous (deriv γ) := hγ.continuous_deriv le_rfl
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn (hγ'c.continuousOn (s := Icc (0:ℝ) 1))
  obtain ⟨Γ0, hΓ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hγc.continuousOn (s := Icc (0:ℝ) 1))
  obtain ⟨Qi, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((continuous_const.sub (hγc.pow 2)).continuousOn (s := Icc (0:ℝ) 1)).inv₀ hne)
  have hQ' : ∀ t ∈ Icc (0:ℝ) 1, ‖(1-(γ t)^2)⁻¹‖ ≤ Qi := fun t ht => hQ t ht
  have hG' : ∀ t ∈ Icc (0:ℝ) 1, ‖deriv γ t‖ ≤ G := fun t ht => hG t ht
  have hΓ' : ∀ t ∈ Icc (0:ℝ) 1, ‖γ t‖ ≤ Γ0 := fun t ht => hΓ t ht
  clear hQ hG hΓ
  obtain ⟨u, v, huv⟩ := legendreTransport_exists ν μ a b γ hγ hreg
  obtain ⟨U, hU⟩ := isCompact_Icc.exists_bound_of_continuousOn huv.2.2.1
  have h0I : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG' 0 h0I)
  have hΓ0 : 0 ≤ Γ0 := (norm_nonneg _).trans (hΓ' 0 h0I)
  have hQ0 : 0 ≤ Qi := (norm_nonneg _).trans (hQ' 0 h0I)
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0 h0I)
  choose ux vx hx using fun x => legendreTransport_exists (νf x) (μf x) (af x) (bf x) γ hγ hreg
  rw [legendreTransport_unique ν μ a b γ hγ hreg huv]
  have hT : ∀ x, legendreTransport (νf x) (μf x) γ (af x) (bf x) = ux x 1 :=
    fun x => legendreTransport_unique _ _ _ _ γ hγ hreg (hx x)
  simp only [hT]
  have hα : Tendsto (fun x => νf x*(νf x+1)) l (𝓝 (ν*(ν+1))) := hν.mul (hν.add_const 1)
  have hβ : Tendsto (fun x => μf x^2) l (𝓝 (μ^2)) := hμ.pow 2
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = ‖ν*(ν+1)‖+1 := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = ‖μ^2‖+1 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAd]; positivity
  have hB0 : 0 ≤ B := by rw [hBd]; positivity
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = G + G*Qi*(2*Γ0 + A + B*Qi) + 1 := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKd]; positivity
  have hK1 : G ≤ K := by rw [hKd]; have : 0 ≤ G*Qi*(2*Γ0 + A + B*Qi) := by positivity
                         linarith
  have hK2 : G*Qi*(2*Γ0 + A + B*Qi) ≤ K := by rw [hKd]; linarith
  have hε : Tendsto (fun x => G*Qi*(‖νf x*(νf x+1)-ν*(ν+1)‖+‖μf x^2-μ^2‖*Qi)*U) l (𝓝 0) := by
    have h1 := (hα.sub_const (ν*(ν+1))).norm
    have h2 := (hβ.sub_const (μ^2)).norm
    simp only [sub_self, norm_zero] at h1 h2
    have := ((tendsto_const_nhds (x := G*Qi)).mul (h1.add (h2.mul_const Qi))).mul_const U
    simpa using this
  have hδ : Tendsto (fun x => max ‖af x - a‖ ‖bf x - b‖) l (𝓝 0) := by
    have h := ((ha.sub_const a).prodMk_nhds (hb.sub_const b)).norm
    simpa using h
  have hbound : ∀ᶠ x in l, ‖ux x 1 - u 1‖ ≤ max ‖af x - a‖ ‖bf x - b‖ * Real.exp K +
      G*Qi*(‖νf x*(νf x+1)-ν*(ν+1)‖+‖μf x^2-μ^2‖*Qi)*U / K * (Real.exp K - 1) := by
    have hA : ∀ᶠ x in l, ‖νf x*(νf x+1)‖ ≤ A := by
      filter_upwards [hα.norm.eventually (gt_mem_nhds (lt_add_one ‖ν*(ν+1)‖))] with x hx
      rw [hAd]; exact hx.le
    have hB : ∀ᶠ x in l, ‖μf x^2‖ ≤ B := by
      filter_upwards [hβ.norm.eventually (gt_mem_nhds (lt_add_one ‖μ^2‖))] with x hx
      rw [hBd]; exact hx.le
    filter_upwards [hA, hB] with x hAx hBx
    obtain ⟨hu0', hv0', hcu, hcv, hd⟩ := hx x
    obtain ⟨hu0, hv0, hcu0, hcv0, hd0⟩ := huv
    obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = G*Qi*(‖νf x*(νf x+1)-ν*(ν+1)‖+‖μf x^2-μ^2‖*Qi)*U := ⟨_, rfl⟩
    have hε0 : 0 ≤ ε := by rw [hεd]; positivity
    rw [← hεd]
    have hfc : ContinuousOn (fun t => (ux x t - u t, vx x t - v t)) (Icc 0 1) :=
      (hcu.sub hcu0).prodMk (hcv.sub hcv0)
    have hfd : ∀ t ∈ Ico (0:ℝ) 1, HasDerivWithinAt (fun t => (ux x t - u t, vx x t - v t))
        ((deriv γ t*vx x t - deriv γ t*v t,
          deriv γ t*(2*γ t*vx x t-(νf x*(νf x+1)-μf x^2/(1-(γ t)^2))*ux x t)/(1-(γ t)^2) -
          deriv γ t*(2*γ t*v t-(ν*(ν+1)-μ^2/(1-(γ t)^2))*u t)/(1-(γ t)^2)) : ℂ × ℂ) (Ici t) t := by
      intro t ht
      have htI : t ∈ Icc (0:ℝ) 1 := Ico_subset_Icc_self ht
      have hm := Icc_mem_nhdsGE_of_mem ht
      exact ((((hd t htI).1.sub (hd0 t htI).1)).prodMk ((hd t htI).2.sub (hd0 t htI).2)).mono_of_mem_nhdsWithin hm
    have hf0 : ‖((ux x 0 - u 0, vx x 0 - v 0) : ℂ × ℂ)‖ ≤ max ‖af x - a‖ ‖bf x - b‖ := by
      rw [hu0, hv0, hu0', hv0', Prod.norm_def]
    have hfb : ∀ t ∈ Ico (0:ℝ) 1, ‖((deriv γ t*vx x t - deriv γ t*v t,
          deriv γ t*(2*γ t*vx x t-(νf x*(νf x+1)-μf x^2/(1-(γ t)^2))*ux x t)/(1-(γ t)^2) -
          deriv γ t*(2*γ t*v t-(ν*(ν+1)-μ^2/(1-(γ t)^2))*u t)/(1-(γ t)^2)) : ℂ × ℂ)‖ ≤
        K * ‖((ux x t - u t, vx x t - v t) : ℂ × ℂ)‖ + ε := by
      intro t ht
      have htI : t ∈ Icc (0:ℝ) 1 := Ico_subset_Icc_self ht
      rw [Prod.norm_def, Prod.norm_def]
      simp only
      have hM : 0 ≤ max ‖ux x t - u t‖ ‖vx x t - v t‖ :=
        le_trans (norm_nonneg _) (le_max_left _ _)
      refine max_le ?_ ?_
      · rw [← mul_sub, norm_mul]
        have h2 : ‖vx x t - v t‖ ≤ max ‖ux x t - u t‖ ‖vx x t - v t‖ := le_max_right _ _
        have h3 := hG' t htI
        calc ‖deriv γ t‖ * ‖vx x t - v t‖ ≤ G * max ‖ux x t - u t‖ ‖vx x t - v t‖ :=
              mul_le_mul h3 h2 (norm_nonneg _) hG0
          _ ≤ K * max ‖ux x t - u t‖ ‖vx x t - v t‖ := mul_le_mul_of_nonneg_right hK1 hM
          _ ≤ _ := le_add_of_nonneg_right hε0
      · have h := legTr_diff_bound (g := deriv γ t) (γ := γ t) (q := 1-(γ t)^2)
          (α := νf x*(νf x+1)) (β := μf x^2) (α0 := ν*(ν+1)) (β0 := μ^2)
          (ux := ux x t) (vx := vx x t) (u := u t) (v := v t)
          (hG' t htI) (hΓ' t htI) (hQ' t htI) hAx hBx (hU t htI) hG0 hQ0 hΓ0 hA0 hB0
        rw [← hεd] at h
        refine h.trans (add_le_add_left (mul_le_mul_of_nonneg_right hK2 hM) ε |>.trans_eq' ?_ |>.trans_eq ?_)
        · ring
        · ring
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le hfc hfd hf0 hfb 1 ⟨zero_le_one, le_rfl⟩
    rw [gronwallBound_of_K_ne_0 hK.ne', sub_zero] at hgr
    simp only [mul_one] at hgr
    have : ‖ux x 1 - u 1‖ ≤ ‖((ux x 1 - u 1, vx x 1 - v 1) : ℂ × ℂ)‖ := by
      rw [Prod.norm_def]; exact le_max_left _ _
    exact this.trans hgr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hbound ?_
  have := (hδ.mul_const (Real.exp K)).add ((hε.div_const K).mul_const (Real.exp K - 1))
  simpa using this

/-- The transport depends on the order only through `μ²`. -/
theorem legTr_transport_neg_order (ν μ : ℂ) (γ : ℝ → ℂ) (a b : ℂ) :
    legendreTransport ν (-μ) γ a b = legendreTransport ν μ γ a b := by
  simp only [legendreTransport, IsLegendreTransport, neg_sq]

/-- The transport is linear in the initial data. -/
theorem legTr_transport_linear (ν μ : ℂ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hreg : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 1 ∧ γ t ≠ -1) (c₁ c₂ a₁ b₁ a₂ b₂ : ℂ) :
    legendreTransport ν μ γ (c₁*a₁ + c₂*a₂) (c₁*b₁ + c₂*b₂) =
      c₁*legendreTransport ν μ γ a₁ b₁ + c₂*legendreTransport ν μ γ a₂ b₂ := by
  obtain ⟨u₁, v₁, h₁⟩ := legendreTransport_exists ν μ a₁ b₁ γ hγ hreg
  obtain ⟨u₂, v₂, h₂⟩ := legendreTransport_exists ν μ a₂ b₂ γ hγ hreg
  rw [legendreTransport_unique _ _ _ _ γ hγ hreg h₁, legendreTransport_unique _ _ _ _ γ hγ hreg h₂]
  obtain ⟨hu₁, hv₁, hcu₁, hcv₁, hd₁⟩ := h₁
  obtain ⟨hu₂, hv₂, hcu₂, hcv₂, hd₂⟩ := h₂
  have h : IsLegendreTransport ν μ γ (c₁*a₁ + c₂*a₂) (c₁*b₁ + c₂*b₂)
      (fun t => c₁*u₁ t + c₂*u₂ t) (fun t => c₁*v₁ t + c₂*v₂ t) := by
    refine ⟨by simp [hu₁, hu₂], by simp [hv₁, hv₂],
      (continuousOn_const.mul hcu₁).add (continuousOn_const.mul hcu₂),
      (continuousOn_const.mul hcv₁).add (continuousOn_const.mul hcv₂), fun t ht => ⟨?_, ?_⟩⟩
    · exact (((hd₁ t ht).1.const_mul c₁).add ((hd₂ t ht).1.const_mul c₂)).congr_deriv (by ring)
    · exact (((hd₁ t ht).2.const_mul c₁).add ((hd₂ t ht).2.const_mul c₂)).congr_deriv (by ring)
  exact legendreTransport_unique _ _ _ _ γ hγ hreg h

/-- `legendreOneLoop` avoids `±1`. -/
theorem legTr_loop_reg {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    ∀ t ∈ Icc (0:ℝ) 1, legendreOneLoop z s t ≠ 1 ∧ legendreOneLoop z s t ≠ -1 := by
  intro t ht
  rcases legTr_loop_dom hz s ht with h | h
  · refine ⟨fun h1 => slitPlane_ne_zero h (by rw [h1]; ring), fun h1 => ?_⟩
    rw [h1] at h; norm_num [mem_slitPlane_iff] at h
  · have hn : ‖legendreOneLoop z s t‖ < 1 := by simpa using h
    refine ⟨fun h1 => by rw [h1] at hn; simp at hn, fun h1 => by rw [h1] at hn; simp at hn⟩

/-- DLMF 14.24.4 for non-integer order, from 14.24.3 for `P^{±μ}_ν` and the connection formula. -/
theorem legTr_one_olverQ_nonint (ν m : ℂ) (hm : ∀ n : ℤ, m ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    legendreOneContinued (olverQ ν m) ν m z s = exp (-s*m*π*I)*olverQ ν m z-
      π*I*sin (s*m*π)/(sin (m*π)*Gamma (ν-m+1))*associatedP ν (-m) z := by
  have hγ := legTr_contDiff_loop z s
  have hreg := legTr_loop_reg hz s
  have hP : legendreTransport ν m (legendreOneLoop z s) (associatedP ν m z) (deriv (associatedP ν m) z) =
      exp (-s*m*π*I) * associatedP ν m z := by
    have h := associatedP_one_continuation ν (-m) hz s
    rw [neg_neg] at h
    unfold legendreOneContinued at h
    rw [legTr_transport_neg_order] at h
    rw [h]; congr 1; ring_nf
  have hM : legendreTransport ν m (legendreOneLoop z s) (associatedP ν (-m) z)
      (deriv (associatedP ν (-m)) z) = exp (s*m*π*I) * associatedP ν (-m) z :=
    associatedP_one_continuation ν m hz s
  unfold legendreOneContinued
  rw [olverQ_eq_nonint ν m hm hz, deriv_olverQ_nonint ν m hm hz]
  set C := π/(2*sin (m*π))
  set g1 := (Gamma (ν+m+1))⁻¹
  set g2 := (Gamma (ν-m+1))⁻¹ with hg2
  have e1 : C*(associatedP ν m z*g1 - associatedP ν (-m) z*g2) =
      (C*g1)*associatedP ν m z + (-(C*g2))*associatedP ν (-m) z := by ring
  have e2 : C*(deriv (associatedP ν m) z*g1 - deriv (associatedP ν (-m)) z*g2) =
      (C*g1)*deriv (associatedP ν m) z + (-(C*g2))*deriv (associatedP ν (-m)) z := by ring
  rw [e1, e2, legTr_transport_linear ν m hγ hreg, hP, hM]
  have hsin := legendre_sin_ne_zero hm
  have hs : sin (s*m*π) = (exp (-s*m*π*I) - exp (s*m*π*I))*I/2 := by
    rw [Complex.sin]; ring_nf
  rw [hs]
  simp only [C, div_eq_mul_inv, mul_inv]
  rw [← hg2]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The transport depends on the degree only through `ν(ν+1)`. -/
theorem legTr_transport_degree_eq {ν ν' : ℂ} (h : ν'*(ν'+1) = ν*(ν+1)) (μ : ℂ) (γ : ℝ → ℂ) (a b : ℂ) :
    legendreTransport ν' μ γ a b = legendreTransport ν μ γ a b := by
  simp only [legendreTransport, IsLegendreTransport, h]

/-- The ellipse path is `C¹`. -/
theorem legTr_contDiff_ellipse (z : ℂ) (s : ℤ) : ContDiff ℝ 1 (legendreEllipsePath z s) := by
  have he : legendreEllipsePath z s = fun t : ℝ =>
      ((z + exp ((log (z-1) + log (z+1))/2)) * exp ((s:ℂ)*π*I * ofRealCLM t) +
        (z + exp ((log (z-1) + log (z+1))/2))⁻¹ * exp ((-(s:ℂ))*π*I * ofRealCLM t))/2 := by
    funext t; simp only [legendreEllipsePath, ofRealCLM_apply]
  rw [he]
  have h1 : ContDiff ℝ 1 (fun t : ℝ => ofRealCLM t) := ofRealCLM.contDiff
  fun_prop

/-- `ν ↦ ∂_z P^{-μ}_ν(z)` is continuous. -/
theorem legTr_continuous_deriv_associatedP_degree (μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Continuous fun ν => deriv (associatedP ν (-μ)) z := by
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have e := funext fun ν => deriv_associatedP ν (-μ) hz
  rw [e]
  have hP := (associatedP_entire_degree (-μ) z hz).continuous
  have hG := (differentiable_regularizedGaussHG_comp (A := fun ν : ℂ => ν+1+1) (B := fun ν : ℂ => -ν+1)
    (C := fun _ : ℂ => 1-(-μ)+1) (by fun_prop) (by fun_prop) (by fun_prop) hw).continuous
  exact (continuous_const.mul hP).sub ((by fun_prop : Continuous fun ν : ℂ => (ν+1)*(-ν)/2).mul
    (continuous_const.mul hG))

/-- DLMF 14.24.1 off the zeros of `cos νπ`, from 14.24.2 for `𝑸^μ_ν`, `𝑸^μ_{-ν-1}` and 14.9.12. -/
theorem legTr_ellipse_associatedP_generic (ν μ : ℂ) (hc : cos (ν*π) ≠ 0) {z : ℂ} (hz : z-1 ∈ slitPlane)
    (s : ℤ) :
    legendreEllipseContinued (associatedP ν (-μ)) ν μ z s = exp (s*ν*π*I)*associatedP ν (-μ) z+
      2*I*sin ((ν+1/2)*s*π)*exp (-s*π*I/2)/(cos (ν*π)*Gamma (μ-ν))*olverQ ν μ z := by
  have hγ := legTr_contDiff_ellipse z s
  have hreg : ∀ t ∈ Icc (0:ℝ) 1, legendreEllipsePath z s t ≠ 1 ∧ legendreEllipsePath z s t ≠ -1 :=
    fun t _ => legInt_path_ne hz s t
  set g1 := (Gamma (μ-ν))⁻¹ with hg1
  set g2 := (Gamma (ν+μ+1))⁻¹ with hg2
  set c := (cos (ν*π))⁻¹ with hcdef
  have hconn : ∀ w : ℂ, w-1 ∈ slitPlane →
      associatedP ν (-μ) w = (-c*g1)*olverQ ν μ w + (c*g2)*olverQ (-ν-1) μ w := by
    intro w hw
    have h := associated_connection_12 ν μ hw
    simp only [div_eq_mul_inv] at h
    rw [hcdef]; field_simp; linear_combination h
  have hev : associatedP ν (-μ) =ᶠ[𝓝 z] fun w => (-c*g1)*olverQ ν μ w + (c*g2)*olverQ (-ν-1) μ w := by
    filter_upwards [isOpen_sub_one_mem_slitPlane.mem_nhds hz] with w hw using hconn w hw
  have hd : deriv (associatedP ν (-μ)) z =
      (-c*g1)*deriv (olverQ ν μ) z + (c*g2)*deriv (olverQ (-ν-1) μ) z := by
    rw [hev.deriv_eq]
    have h1 := (olverQ_analytic ν μ z hz).differentiableAt.hasDerivAt
    have h2 := (olverQ_analytic (-ν-1) μ z hz).differentiableAt.hasDerivAt
    exact ((h1.const_mul (-c*g1)).add (h2.const_mul (c*g2))).deriv
  have hQ1 := olverQ_ellipse_continuation ν μ hz s
  have hQ2 := olverQ_ellipse_continuation (-ν-1) μ hz s
  unfold legendreEllipseContinued at hQ1 hQ2 ⊢
  rw [legTr_transport_degree_eq (ν := ν) (by ring)] at hQ2
  rw [hconn z hz, hd, legTr_transport_linear ν μ hγ hreg, hQ1, hQ2]
  have hs : sin ((ν+1/2)*s*π) = (exp (-((ν+1/2)*s*π)*I) - exp (((ν+1/2)*s*π)*I))*I/2 := by
    rw [Complex.sin]
  have hcos : cos (ν*π) * c = 1 := mul_inv_cancel₀ hc
  have hconnz := associated_connection_12 ν μ hz
  simp only [div_eq_mul_inv] at hconnz
  rw [← hg1, ← hg2] at hconnz
  rw [hs]
  have hE1 : exp (-((ν+1/2)*s*π)*I) * exp (-s*π*I/2) = (-1:ℂ)^s * exp (-s*ν*π*I) := by
    rw [← exp_add, show -((ν+1/2)*s*π)*I + -s*π*I/2 = (s:ℂ)*(-(π*I)) + -s*ν*π*I by ring,
      exp_add, exp_int_mul, exp_neg, exp_pi_mul_I]; norm_num
  have hE2 : exp (((ν+1/2)*s*π)*I) * exp (-s*π*I/2) = exp (s*ν*π*I) := by
    rw [← exp_add]; congr 1; ring
  have hE3 : (-1:ℂ)^s * exp (-s*(-ν-1)*π*I) = exp (s*ν*π*I) := by
    rw [show -s*(-ν-1)*π*I = (s:ℂ)*(π*I) + s*ν*π*I by ring, exp_add, exp_int_mul, exp_pi_mul_I,
      ← mul_assoc, ← mul_zpow]; norm_num
  rw [div_eq_mul_inv _ (cos (ν*π)*Gamma (μ-ν)), mul_inv, ← hcdef, ← hg1]
  linear_combination (c*g1*olverQ ν μ z)*hE1 - (c*g1*olverQ ν μ z)*hE2 +
    (c*g2*olverQ (-ν-1) μ z)*hE3 -
    ((exp (-((ν+1/2)*s*π)*I)*exp (-s*π*I/2) - exp (((ν+1/2)*s*π)*I)*exp (-s*π*I/2))*c*g1*
      olverQ ν μ z)*I_sq

/-- The parameter limit retains odd half-integral degrees.

Moved within this file (round 13) below DLMF 14.24.2–14.24.3: off the zeros of `cos νπ` the
identity follows from 14.24.2 for `𝑸^μ_ν`, `𝑸^μ_{-ν-1}` and 14.9.12
(`legTr_ellipse_associatedP_generic`); the limit uses the continuity of the transport in the
degree (`legTr_transport_tendsto`). -/
@[dlmf 14.24.E1]
theorem associatedP_ellipse_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    Tendsto (fun v : ℂ => exp (s*v*π*I)*associatedP v (-μ) z+2*I*sin ((v+1/2)*s*π)*exp (-s*π*I/2)/(cos (v*π)*Gamma (μ-v))*olverQ v μ z) (𝓝[≠] ν) (𝓝 (legendreEllipseContinued (associatedP ν (-μ)) ν μ z s)) := by

  have hγ := legTr_contDiff_ellipse z s
  have hreg : ∀ t ∈ Icc (0:ℝ) 1, legendreEllipsePath z s t ≠ 1 ∧ legendreEllipsePath z s t ≠ -1 :=
    fun t _ => legInt_path_ne hz s t
  have hcont : Tendsto (fun v => legendreEllipseContinued (associatedP v (-μ)) v μ z s) (𝓝[≠] ν)
      (𝓝 (legendreEllipseContinued (associatedP ν (-μ)) ν μ z s)) :=
    legTr_transport_tendsto (l := 𝓝[≠] ν) hγ hreg (νf := id) (μf := fun _ => μ)
      (af := fun v => associatedP v (-μ) z) (bf := fun v => deriv (associatedP v (-μ)) z)
      (tendsto_id.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
      (((associatedP_entire_degree (-μ) z hz).continuous.tendsto ν).mono_left nhdsWithin_le_nhds)
      (((legTr_continuous_deriv_associatedP_degree μ hz).tendsto ν).mono_left nhdsWithin_le_nhds)
  refine hcont.congr' ?_
  have hf : AnalyticOnNhd ℂ (fun v : ℂ => cos (v*π)) univ := fun v _ =>
    ((Complex.differentiable_cos.comp (differentiable_id.mul_const _)).analyticAt v)
  have hnz : ∀ᶠ v in 𝓝[≠] ν, cos (v*π) ≠ 0 := by
    rcases (hf ν (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ ν) h
        (mem_univ 0)
      simp at this
    · exact h
  filter_upwards [hnz] with v hv
  rw [legTr_ellipse_associatedP_generic v μ hv hz s]

/-- Integer orders use the removable parameter limit of the complete expression.

For non-integer order the identity follows from 14.24.3 for `P^{±μ}_ν` and the connection formula
(`legTr_one_olverQ_nonint`); the limit uses the continuity of the transport in the order
(`legTr_transport_tendsto`). -/
@[dlmf 14.24.E4]
theorem olverQ_one_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    Tendsto (fun m : ℂ => exp (-s*m*π*I)*olverQ ν m z-π*I*sin (s*m*π)/(sin (m*π)*Gamma (ν-m+1))*associatedP ν (-m) z) (𝓝[≠] μ) (𝓝 (legendreOneContinued (olverQ ν μ) ν μ z s)) := by

  have hγ := legTr_contDiff_loop z s
  have hreg := legTr_loop_reg hz s
  have hcont : Tendsto (fun m => legendreOneContinued (olverQ ν m) ν m z s) (𝓝[≠] μ)
      (𝓝 (legendreOneContinued (olverQ ν μ) ν μ z s)) :=
    legTr_transport_tendsto (l := 𝓝[≠] μ) hγ hreg (νf := fun _ => ν) (μf := id)
      (af := fun m => olverQ ν m z) (bf := fun m => deriv (olverQ ν m) z) tendsto_const_nhds
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (((olverQ_entire_order ν z hz).continuous.tendsto μ).mono_left nhdsWithin_le_nhds)
      (((continuous_deriv_olverQ_order ν hz).tendsto μ).mono_left nhdsWithin_le_nhds)
  refine hcont.congr' ?_
  have hf : AnalyticOnNhd ℂ (fun m : ℂ => sin (m*π)) univ := fun m _ =>
    ((Complex.differentiable_sin.comp (differentiable_id.mul_const _)).analyticAt m)
  have hnint : ∀ᶠ m in 𝓝[≠] μ, ∀ n : ℤ, (m:ℂ) ≠ (n:ℂ) := by
    rcases (hf μ (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ μ) h
        (mem_univ (1/2))
      simp only [Pi.zero_apply] at this
      rw [show (1/2:ℂ)*π = (π/2:ℝ) by push_cast; ring, ← ofReal_sin, Real.sin_pi_div_two] at this
      norm_num at this
    · filter_upwards [h] with m hm n hn
      apply hm; rw [hn]; exact Complex.sin_int_mul_pi n
  filter_upwards [hnint] with m hm
  exact legTr_one_olverQ_nonint ν m hm hz s

end DLMF.Legendre

end
