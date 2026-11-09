/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Mellin.SmallParameter
public import DLMF.AsymptoticApproximations.Mellin.VerticalBounds
public import DLMFMathlib.Analysis.Complex.VerticalResidues

/-!
# Exact residue expansion of a Laplace transform at a small parameter

The finite-subtraction continuation of the high tail supplies the vertical bounds
needed for DLMF 2.5.43. The two contour shifts are expressed with Tau Ceti residues.
The inversion lines avoid poles; a line through a pole does not define an absolutely
convergent remainder integral.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology Real

namespace DLMF.AsymptoticApproximations

open DLMF.AlgebraicAnalytic (laplaceTransform)

/-- Exact form of DLMF 2.5.43 with an intermediate line `1 < ρ < 2` and a final pole-free
line `L > ρ`. Finite-subtraction holomorphy and the asymptotic expansion imply the required
vertical decay and absolute convergence. Residues have the Tau Ceti normalization. -/
@[dlmf 2.5.E43]
theorem laplace_expansion_residues_of_asymptoticExpansion
    {h : ℝ → ℂ} {b β : ℕ → ℂ} {H : ℂ → ℂ} {c p ρ L ζ : ℝ}
    (P₂ P : Finset ℂ) (hc : -1 < c) (hp : p < 1) (hpβ : p < (β 0).re)
    (hρ : 1 < ρ) (hρ2 : ρ < 2) (hρL : ρ < L) (hζ : 0 < ζ)
    (hL : ∀ n : ℕ, 1 - L ≠ -n)
    (hhc : LocallyIntegrableOn h (Ioi 0)) (h0 : h =O[𝓝[>] 0] fun t => t ^ c)
    (hβ : StrictMono fun s => (β s).re)
    (hβinf : Tendsto (fun s => (β s).re) atTop atTop)
    (hh : HasAsymptoticExpansion atTop (fun s (t : ℝ) => (t : ℂ) ^ (-β s)) b h)
    (hH : ∀ z : ℂ, z.re < (β 0).re → H z = mellin (mellinTruncHigh h) z)
    (hHd : ∀ N : ℕ, DifferentiableOn ℂ (fun z => H z + ∑ s ∈ range N, b s / (z - β s))
      {z : ℂ | z.re < (β N).re})
    (hP₂ : ∀ q ∈ P₂, p < q.re ∧ q.re ≤ 1)
    (hP : ∀ q ∈ P, ρ < q.re ∧ q.re < L)
    (hG₂ : DifferentiableOn ℂ (fun z => Gamma (1 - z) * H z)
      ({z : ℂ | p ≤ z.re ∧ z.re ≤ ρ} \ (P₂ : Set ℂ)))
    (hG : DifferentiableOn ℂ (fun z => Gamma (1 - z) *
      (mellin (mellinTruncLow h) z + H z))
      ({z : ℂ | ρ ≤ z.re ∧ z.re ≤ L} \ (P : Set ℂ))) :
    laplaceTransform h ζ = mellin (mellinTruncLow h) 1 +
      ∑ q ∈ P₂, TauCeti.Contour.residue
        (fun z => -((ζ : ℂ) ^ (z - 1) * Gamma (1 - z) * H z)) q +
      ∑ q ∈ P, TauCeti.Contour.residue
        (fun z => -((ζ : ℂ) ^ (z - 1) * Gamma (1 - z) *
          (mellin (mellinTruncLow h) z + H z))) q +
      (ζ : ℂ)⁻¹ * mellinInv L (fun z => Gamma (1 - z) *
        (mellin (mellinTruncLow h) z + H z)) ζ⁻¹ := by
  let A : ℂ → ℂ := mellin (mellinTruncLow h)
  let G₂ : ℂ → ℂ := fun z => Gamma (1 - z) * H z
  let G₁ : ℂ → ℂ := fun z => Gamma (1 - z) * A z
  let G : ℂ → ℂ := fun z => Gamma (1 - z) * (A z + H z)
  have hpρ : p < ρ := hp.trans hρ
  have hx : 0 < ζ⁻¹ := inv_pos.mpr hζ
  have hpolep (n : ℕ) : 1 - p ≠ -(n : ℝ) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hpolerho (n : ℕ) : 1 - ρ ≠ -(n : ℝ) := by
    cases n with
    | zero => simp only [Nat.cast_zero, neg_zero]; linarith
    | succ n => have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
                push_cast
                linarith
  have hmh : Meromorphic H := meromorphic_mellin_truncHigh_continuation hβinf hHd
  have hmΓ (z : ℂ) : MeromorphicAt (fun w : ℂ => Gamma (1 - w)) z :=
    (Meromorphic.Gamma (1 - z)).comp_analyticAt (analyticAt_const.sub analyticAt_id)
  have hmG₂ (z : ℂ) : MeromorphicAt G₂ z := (hmΓ z).mul (hmh z)
  have hAc (z : ℂ) (hz : -c < z.re) : DifferentiableAt ℂ A z :=
    mellin_truncLow_differentiableAt hhc h0 hz
  have hAa : AnalyticOnNhd ℂ A {z : ℂ | -c < z.re} :=
    (show DifferentiableOn ℂ A {z : ℂ | -c < z.re} from fun z hz =>
      (hAc z hz).differentiableWithinAt).analyticOnNhd (isOpen_lt continuous_const continuous_re)
  have hmG (q : ℂ) (hq : q ∈ P) : MeromorphicAt G q :=
    (hmΓ q).mul ((hAa q (show -c < q.re by linarith [(hP q hq).1])).meromorphicAt.add (hmh q))
  obtain ⟨B, Y, hB, hY, hbound⟩ := exists_bound_mellin_truncHigh_continuation
    hhc hβ hβinf hh hH hHd L
  have hconvlow : MellinConvergent (mellinTruncLow h) 1 :=
    mellinConvergent_truncLow hhc h0 (by simp; linarith)
  let M : ℝ := ∫ t in Ioi 0, ‖mellinTruncLow h t‖
  have hM : 0 ≤ M := integral_nonneg fun t => norm_nonneg _
  have hAbound {z : ℂ} (hz : 1 ≤ z.re) : ‖A z‖ ≤ M := by
    simpa only [A, sub_self, Real.rpow_zero, one_mul] using norm_mellin_truncLow_le hconvlow hz
  have hboundG : ∀ z : ℂ, z.re ∈ Icc ρ L → Y ≤ |z.im| → ‖A z + H z‖ ≤ M + B := by
    intro z hz hy
    exact (norm_add_le _ _).trans (add_le_add (hAbound (hρ.le.trans hz.1))
      (hbound z hz.2 hy))
  have hcont₂ (σ : ℝ) (hσ : σ ∈ Icc p ρ) (hoff : ∀ q ∈ P₂, σ ≠ q.re) :
      Continuous fun y : ℝ => G₂ (σ + y * I) :=
    hG₂.continuousOn.comp_continuous (by fun_prop) fun y => by
      refine ⟨by simpa using hσ, fun hq => hoff _ hq ?_⟩
      simp
  have hcont₂p := hcont₂ p ⟨le_rfl, hpρ.le⟩ (fun q hq => (hP₂ q hq).1.ne)
  have hcont₂rho := hcont₂ ρ ⟨hpρ.le, le_rfl⟩ (fun q hq => by linarith [(hP₂ q hq).2])
  have hcontL : Continuous fun y : ℝ => G (L + y * I) :=
    hG.continuousOn.comp_continuous (by fun_prop) fun y => by
      refine ⟨by simpa using hρL.le, fun hq => ?_⟩
      have hqL := (hP _ hq).2
      simpa using hqL
  have hi₂p : VerticalIntegrable G₂ p :=
    DLMF.Gamma.verticalIntegrable_Gamma_one_sub_mul (F := H) (B := B) (Y := Y) hpolep
    (DLMF.Gamma.continuous_vertical_of_Gamma_one_sub_mul hpolep hcont₂p)
    (fun y hy => hbound _ (by simp; linarith) (by simpa using hy))
  have hi₂rho : VerticalIntegrable G₂ ρ :=
    DLMF.Gamma.verticalIntegrable_Gamma_one_sub_mul (F := H) (B := B) (Y := Y) hpolerho
      (DLMF.Gamma.continuous_vertical_of_Gamma_one_sub_mul hpolerho hcont₂rho)
      (fun y hy => hbound _ (by simp; linarith) (by simpa using hy))
  have hi₁rho : VerticalIntegrable G₁ ρ :=
    DLMF.Gamma.verticalIntegrable_Gamma_one_sub_mul (F := A) (B := M) (Y := 0) hpolerho
      (continuous_iff_continuousAt.mpr fun y => ContinuousAt.comp (g := A)
        (f := fun y : ℝ => (ρ : ℂ) + y * I) (hAc _ (by simp; linarith)).continuousAt
        (by fun_prop)) (fun y _ => hAbound (by simp; linarith))
  have hiL : VerticalIntegrable G L :=
    DLMF.Gamma.verticalIntegrable_Gamma_one_sub_mul
      (F := fun z => A z + H z) (B := M + B) (Y := Y) hL
      (DLMF.Gamma.continuous_vertical_of_Gamma_one_sub_mul
        (F := fun z => A z + H z) hL hcontL)
      (fun y hy => hboundG _ (by simp; exact hρL.le) (by simpa using hy))
  have hirho : VerticalIntegrable G ρ := by
    unfold VerticalIntegrable at hi₁rho hi₂rho ⊢
    refine (hi₁rho.add hi₂rho).congr (Eventually.of_forall fun y => ?_)
    simp only [G, G₁, G₂, Pi.add_apply]
    ring
  have hdec₂ : Tendsto (fun y : ℝ => ⨆ σ : Icc p ρ, ‖G₂ (σ + y * I)‖)
      (cocompact ℝ) (𝓝 0) := DLMF.Gamma.tendsto_iSup_norm_Gamma_one_sub_mul hpρ.le hB
        (fun z hz hy => hbound z (hz.2.trans hρL.le) hy)
  have hdec : Tendsto (fun y : ℝ => ⨆ σ : Icc ρ L, ‖G (σ + y * I)‖)
      (cocompact ℝ) (𝓝 0) :=
    DLMF.Gamma.tendsto_iSup_norm_Gamma_one_sub_mul hρL.le (add_nonneg hM hB) hboundG
  have hconvp : MellinConvergent (mellinTruncHigh h) p := by
    simpa only [Finset.range_zero, sum_empty, sub_zero] using
      mellinConvergent_truncHigh_sub_sum hhc hh 0 (by simpa using hpβ)
  have hgm : AEStronglyMeasurable (mellinTruncHigh h) (volume.restrict (Ioi 0)) := by
    rw [mellinTruncHigh_eq_indicator]
    exact hhc.aestronglyMeasurable.indicator measurableSet_Ioi
  have hsupport (t : ℝ) (ht : t ≤ 1) : mellinTruncHigh h t = 0 := by
    simp [mellinTruncHigh_eq_indicator, not_lt.mpr ht]
  have hcont := continuousAt_integral_exp_neg_mul_dilate_of_mellinConvergent
    hx hsupport hgm hconvp
  have hHp (z : ℂ) (hz : z.re = p) : H z = mellin (mellinTruncHigh h) z :=
    hH z (hz.trans_lt hpβ)
  have hHp' (y : ℝ) : H (p + y * I) = mellin (mellinTruncHigh h) (p + y * I) :=
    hHp _ (by simp)
  have htail : (∫ t in Ioi 0, (Real.exp (-t) : ℂ) * mellinTruncHigh h (ζ⁻¹ * t)) =
      mellinInv p G₂ ζ⁻¹ := by
    have hconv : ∀ z : ℂ, z.re = p → MellinConvergent (mellinTruncHigh h) z :=
      fun z hz => hconvp.of_re_eq (by simpa using hz)
    have hi : VerticalIntegrable (fun z => Gamma (1 - z) * mellin (mellinTruncHigh h) z) p := by
      unfold VerticalIntegrable at hi₂p ⊢
      simpa only [G₂, hHp'] using hi₂p
    rw [laplace_trunc_eq_mellinInv hp hx hconv hi hcont]
    unfold mellinInv
    simp only [G₂, hHp']
  have hshift₂ := Complex.mellinInv_eq_sum_residue_add_of_iSup_norm hpρ hx P₂
    (fun q hq => ⟨(hP₂ q hq).1, by linarith [(hP₂ q hq).2]⟩)
    hG₂ (fun q _ => hmG₂ q) hi₂p hi₂rho hdec₂
  have hshift := Complex.mellinInv_eq_sum_residue_add_of_iSup_norm hρL hx P hP
    hG hmG hirho hiL hdec
  have hlow := laplace_truncLow_shift hc hρ hρ2 hx hhc h0
  have hsum : mellinInv ρ G₁ ζ⁻¹ + mellinInv ρ G₂ ζ⁻¹ = mellinInv ρ G ζ⁻¹ := by
    rw [← mellinInv_add hi₁rho hi₂rho hx]
    congr 1
    funext z
    dsimp [G, G₁, G₂]
    ring
  have hilow : IntegrableOn (mellinTruncLow h) (Ioi 0) := by
    simpa only [MellinConvergent, sub_self, cpow_zero, one_smul] using hconvlow
  have hilowscale : IntegrableOn (fun t => mellinTruncLow h (ζ⁻¹ * t)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff _ 0 hx).mpr (by simpa using hilow)
  have hi₁ : IntegrableOn (fun t => (Real.exp (-t) : ℂ) * mellinTruncLow h (ζ⁻¹ * t))
      (Ioi 0) := by
    refine hilowscale.norm.mono'
      ((by fun_prop : Continuous fun t : ℝ => (Real.exp (-t) : ℂ)).aestronglyMeasurable.mul
        hilowscale.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_of_lt (show 0 < t from ht))))
  have hi₂ : IntegrableOn (fun t => (Real.exp (-t) : ℂ) * mellinTruncHigh h (ζ⁻¹ * t))
      (Ioi 0) := by
    have hi := integrableOn_exp_neg_mul_of_mellinConvergent hsupport hgm hconvp hζ
    have hs := (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => (Real.exp (-ζ * t) : ℂ) * mellinTruncHigh h t) 0 hx).mpr
        (by simpa using hi)
    convert hs using 1
    funext t
    congr 2
    field_simp
  have he := laplace_eq_trunc_add hζ hi₁ hi₂
  rw [hlow, htail, hshift₂] at he
  have hefull : (ζ : ℂ) * laplaceTransform h ζ =
      A 1 * ((ζ⁻¹ : ℝ) : ℂ)⁻¹ +
        ∑ q ∈ P₂, TauCeti.Contour.residue
          (fun z => -(((ζ⁻¹ : ℝ) : ℂ) ^ (-z) * G₂ z)) q +
        ∑ q ∈ P, TauCeti.Contour.residue
          (fun z => -(((ζ⁻¹ : ℝ) : ℂ) ^ (-z) * G z)) q + mellinInv L G ζ⁻¹ := by
    calc (ζ : ℂ) * laplaceTransform h ζ =
        (A 1 * ((ζ⁻¹ : ℝ) : ℂ)⁻¹ +
          ∑ q ∈ P₂, TauCeti.Contour.residue
            (fun z => -(((ζ⁻¹ : ℝ) : ℂ) ^ (-z) * G₂ z)) q) +
          (mellinInv ρ G₁ ζ⁻¹ + mellinInv ρ G₂ ζ⁻¹) := by linear_combination he
      _ = _ := by rw [hsum, hshift]; ring
  have hζc : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hζ.ne'
  have hpower (z : ℂ) : (ζ : ℂ)⁻¹ * ((ζ⁻¹ : ℝ) : ℂ) ^ (-z) = (ζ : ℂ) ^ (z - 1) := by
    rw [ofReal_inv, inv_cpow_ofReal_nonneg hζ.le, cpow_neg, inv_inv,
      cpow_sub _ _ hζc, cpow_one]
    ring
  have hres (F : ℂ → ℂ) (q : ℂ) : (ζ : ℂ)⁻¹ *
      TauCeti.Contour.residue (fun z => -(((ζ⁻¹ : ℝ) : ℂ) ^ (-z) * F z)) q =
      TauCeti.Contour.residue (fun z => -((ζ : ℂ) ^ (z - 1) * F z)) q := by
    rw [← TauCeti.Contour.residue_const_mul]
    congr 1
    funext z
    rw [← hpower]
    ring
  have hresSum (F : ℂ → ℂ) (S : Finset ℂ) : (ζ : ℂ)⁻¹ *
      (∑ q ∈ S, TauCeti.Contour.residue
        (fun z => -(((ζ⁻¹ : ℝ) : ℂ) ^ (-z) * F z)) q) =
      ∑ q ∈ S, TauCeti.Contour.residue
        (fun z => -((ζ : ℂ) ^ (z - 1) * F z)) q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => hres F q
  have he' := congrArg (fun w : ℂ => (ζ : ℂ)⁻¹ * w) hefull
  rw [mul_add, mul_add, mul_add, hresSum G₂ P₂, hresSum G P] at he'
  have hterm : (ζ : ℂ)⁻¹ * (A 1 * ((ζ⁻¹ : ℝ) : ℂ)⁻¹) = A 1 := by
    rw [ofReal_inv, inv_inv]
    field_simp
  rw [hterm, ← mul_assoc, inv_mul_cancel₀ hζc, one_mul] at he'
  simpa only [G₂, G, A, mul_assoc] using he'

/-- DLMF 2.5.43 at a pole-free line `L > 1`, with all poles at or below one in `P₂` and
all poles between one and `L` in `P`. The intermediate line is chosen from the finite
pole data. The actual asymptotic expansion supplies all vertical estimates. -/
@[dlmf 2.5.E43]
theorem laplace_expansion_residues_of_asymptoticExpansion_atLine
    {h : ℝ → ℂ} {b β : ℕ → ℂ} {H : ℂ → ℂ} {c p L ζ : ℝ}
    (P₂ P : Finset ℂ) (hc : -1 < c) (hp : p < 1) (hpβ : p < (β 0).re)
    (hL1 : 1 < L) (hζ : 0 < ζ)
    (hL : ∀ n : ℕ, 1 - L ≠ -n)
    (hhc : LocallyIntegrableOn h (Ioi 0)) (h0 : h =O[𝓝[>] 0] fun t => t ^ c)
    (hβ : StrictMono fun s => (β s).re)
    (hβinf : Tendsto (fun s => (β s).re) atTop atTop)
    (hh : HasAsymptoticExpansion atTop (fun s (t : ℝ) => (t : ℂ) ^ (-β s)) b h)
    (hH : ∀ z : ℂ, z.re < (β 0).re → H z = mellin (mellinTruncHigh h) z)
    (hHd : ∀ N : ℕ, DifferentiableOn ℂ (fun z => H z + ∑ s ∈ range N, b s / (z - β s))
      {z : ℂ | z.re < (β N).re})
    (hP₂ : ∀ q ∈ P₂, p < q.re ∧ q.re ≤ 1)
    (hP : ∀ q ∈ P, 1 < q.re ∧ q.re < L)
    (hG₂ : DifferentiableOn ℂ (fun z => Gamma (1 - z) * H z)
      ({z : ℂ | p ≤ z.re ∧ z.re ≤ L} \ ((P₂ : Set ℂ) ∪ P)))
    (hG : DifferentiableOn ℂ (fun z => Gamma (1 - z) *
      (mellin (mellinTruncLow h) z + H z))
      ({z : ℂ | 1 < z.re ∧ z.re ≤ L} \ (P : Set ℂ))) :
    laplaceTransform h ζ = mellin (mellinTruncLow h) 1 +
      ∑ q ∈ P₂, TauCeti.Contour.residue
        (fun z => -((ζ : ℂ) ^ (z - 1) * Gamma (1 - z) * H z)) q +
      ∑ q ∈ P, TauCeti.Contour.residue
        (fun z => -((ζ : ℂ) ^ (z - 1) * Gamma (1 - z) *
          (mellin (mellinTruncLow h) z + H z))) q +
      (ζ : ℂ)⁻¹ * mellinInv L (fun z => Gamma (1 - z) *
        (mellin (mellinTruncLow h) z + H z)) ζ⁻¹ := by
  have hsmall : ∀ᶠ ρ : ℝ in 𝓝[>] (1 : ℝ), ρ < 2 ∧ ρ < L ∧ ∀ q ∈ P, ρ < q.re := by
    have h₂ : ∀ᶠ ρ : ℝ in 𝓝[>] (1 : ℝ), ρ < 2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
    have hL' : ∀ᶠ ρ : ℝ in 𝓝[>] (1 : ℝ), ρ < L :=
      nhdsWithin_le_nhds (Iio_mem_nhds hL1)
    have hP' : ∀ᶠ ρ : ℝ in 𝓝[>] (1 : ℝ), ∀ q ∈ P, ρ < q.re :=
      (eventually_all_finset P).mpr fun q hq =>
        nhdsWithin_le_nhds (Iio_mem_nhds (hP q hq).1)
    exact h₂.and (hL'.and hP')
  have hright : ∀ᶠ ρ : ℝ in 𝓝[>] (1 : ℝ), 1 < ρ := self_mem_nhdsWithin
  obtain ⟨ρ, hρ, hρ2, hρL, hPρ⟩ := (hright.and hsmall).exists
  apply laplace_expansion_residues_of_asymptoticExpansion P₂ P hc hp hpβ hρ hρ2 hρL hζ hL
    hhc h0 hβ hβinf hh hH hHd hP₂ (fun q hq => ⟨hPρ q hq, (hP q hq).2⟩)
  · apply hG₂.mono
    intro z hz
    refine ⟨⟨hz.1.1, hz.1.2.trans hρL.le⟩, fun hq => ?_⟩
    rcases hq with hq | hq
    · exact hz.2 hq
    · exact (not_lt.mpr hz.1.2) (hPρ z hq)
  · exact hG.mono fun z hz => ⟨⟨hρ.trans_le hz.1.1, hz.1.2⟩, hz.2⟩

/-- DLMF 2.5.43 with the pole locations supplied by the asymptotic data. The continuation
regular parts imply holomorphy off those locations; no separate holomorphy, decay or
vertical convergence hypothesis is required. The final line avoids all poles. -/
@[dlmf 2.5.E43]
theorem laplace_expansion_residues_of_asymptoticExpansion_of_pole_locations
    {h : ℝ → ℂ} {b β : ℕ → ℂ} {H : ℂ → ℂ} {c p L ζ : ℝ}
    (P₂ P : Finset ℂ) (hc : -1 < c) (hp : p < 1) (hpβ : p < (β 0).re)
    (hL1 : 1 < L) (hζ : 0 < ζ)
    (hL : ∀ n : ℕ, 1 - L ≠ -n)
    (hhc : LocallyIntegrableOn h (Ioi 0)) (h0 : h =O[𝓝[>] 0] fun t => t ^ c)
    (hβ : StrictMono fun s => (β s).re)
    (hβinf : Tendsto (fun s => (β s).re) atTop atTop)
    (hh : HasAsymptoticExpansion atTop (fun s (t : ℝ) => (t : ℂ) ^ (-β s)) b h)
    (hH : ∀ z : ℂ, z.re < (β 0).re → H z = mellin (mellinTruncHigh h) z)
    (hHd : ∀ N : ℕ, DifferentiableOn ℂ (fun z => H z + ∑ s ∈ range N, b s / (z - β s))
      {z : ℂ | z.re < (β N).re})
    (hP₂ : ∀ q ∈ P₂, p < q.re ∧ q.re ≤ 1)
    (hP : ∀ q ∈ P, 1 < q.re ∧ q.re < L)
    (h1 : (1 : ℂ) ∈ P₂)
    (hP₂β : ∀ k, (β k).re ≤ 1 → β k ∈ P₂)
    (hPβ : ∀ k, 1 < (β k).re → (β k).re < L → β k ∈ P)
    (hPnat : ∀ n : ℕ, 1 < (n : ℝ) + 1 → (n : ℝ) + 1 < L → (n : ℂ) + 1 ∈ P)
    (hβL : ∀ k, (β k).re ≠ L) :
    laplaceTransform h ζ = mellin (mellinTruncLow h) 1 +
      ∑ q ∈ P₂, TauCeti.Contour.residue
        (fun z => -((ζ : ℂ) ^ (z - 1) * Gamma (1 - z) * H z)) q +
      ∑ q ∈ P, TauCeti.Contour.residue
        (fun z => -((ζ : ℂ) ^ (z - 1) * Gamma (1 - z) *
          (mellin (mellinTruncLow h) z + H z))) q +
      (ζ : ℂ)⁻¹ * mellinInv L (fun z => Gamma (1 - z) *
        (mellin (mellinTruncLow h) z + H z)) ζ⁻¹ := by
  have hd (z : ℂ) (hz : p ≤ z.re ∧ z.re ≤ L) (hnp : z ∉ (P₂ : Set ℂ) ∪ P) :
      DifferentiableAt ℂ H z ∧ DifferentiableAt ℂ (fun w => Gamma (1 - w)) z := by
    have hβz : ∀ k, z ≠ β k := by
      intro k hk
      apply hnp
      have hkL : (β k).re < L := by
        have hle : (β k).re ≤ L := by simpa only [hk] using hz.2
        rcases eq_or_lt_of_le hle with h | h
        · exact (hβL k h).elim
        · exact h
      rw [hk]
      by_cases hkle : (β k).re ≤ 1
      · exact Or.inl (hP₂β k hkle)
      · exact Or.inr (hPβ k (lt_of_not_ge hkle) hkL)
    have hΓz : ∀ n : ℕ, 1 - z ≠ -(n : ℂ) := by
      intro n hn
      have he : z = (n : ℂ) + 1 := by linear_combination -hn
      have hre : z.re = (n : ℝ) + 1 := by simp only [he, add_re, natCast_re, one_re]
      have hlt : (n : ℝ) + 1 < L := by
        have hle : (n : ℝ) + 1 ≤ L := by linarith [hz.2]
        rcases eq_or_lt_of_le hle with h | h
        · exact (hL n (by linarith)).elim
        · exact h
      apply hnp
      rw [he]
      by_cases hn0 : n = 0
      · left
        simpa only [hn0, Nat.cast_zero, zero_add, Finset.mem_coe] using h1
      · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        exact Or.inr (hPnat n (by linarith) hlt)
    exact ⟨differentiableAt_mellin_truncHigh_continuation hβinf hHd hβz,
      (Complex.differentiableAt_Gamma (1 - z) hΓz).comp z
        ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)⟩
  apply laplace_expansion_residues_of_asymptoticExpansion_atLine P₂ P hc hp hpβ hL1 hζ hL
    hhc h0 hβ hβinf hh hH hHd hP₂ hP
  · intro z hz
    exact ((hd z hz.1 hz.2).2.mul (hd z hz.1 hz.2).1).differentiableWithinAt
  · intro z hz
    have hnp : z ∉ (P₂ : Set ℂ) ∪ P := by
      rintro (hq | hq)
      · have hle := (hP₂ z hq).2
        linarith [hz.1.1]
      · exact hz.2 hq
    have hdz := hd z ⟨hp.le.trans hz.1.1.le, hz.1.2⟩ hnp
    exact (hdz.2.mul ((mellin_truncLow_differentiableAt hhc h0
      (by linarith [hz.1.1])).add hdz.1)).differentiableWithinAt

end DLMF.AsymptoticApproximations
