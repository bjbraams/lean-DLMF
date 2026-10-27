/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated

/-!
# Elementary tests of the DLMF left-cut zero rule

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- Terminating hypergeometric case used to inspect the source claim in DLMF 14.27. -/
theorem associatedP_one_neg_half {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP 1 (-1/2) z=exp (-(log (z+1)-log (z-1))/4)*(2*z+1)/(3*Gamma (3/2)) := by
  have hc : ∀ k : ℕ, (3/2:ℂ) ≠ -k := by
    intro k hk
    have h:=congrArg Complex.re hk
    norm_num at h
    linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have H : EqOn (regularizedGaussHG (-1) 2 (3/2))
      (fun u : ℂ => (1-4/3*u)/Gamma (3/2)) cutPlane := by
    apply eqOn_cutPlane_of_eqOn_disk (analyticOnNhd_regularizedGaussHG _ _ _)
      (by intro u hu; fun_prop)
    intro u hu
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hu,
      regularizedGaussHGFun_eq_div_Gamma hc]
    have hh:=ordinaryHypergeometric_eq_sum_neg_nat 1 2 (3/2) u
    norm_num [Finset.sum_range_succ, gaussHGCoeff, poch_one, poch_zero] at hh
    rw [hh]
    ring
  have hz' : 1+z ∈ slitPlane := by
    rw [mem_slitPlane_iff] at hz ⊢
    rcases hz with h | h
    · left; simp at h ⊢; linarith
    · right; simpa using h
  have hu:=mem_cutPlane_of_one_add hz'
  unfold associatedP
  norm_num only
  rw [regularizedGaussHG_symm 2 (-1) (3/2) hu, H hu]
  rw [show -(1/4:ℂ)*(log (z+1)-log (z-1))=-(log (z+1)-log (z-1))/4 by ring]
  ring

/-- The n=1, order=-1/2 example cannot have a zero on either side of the left cut. -/
theorem dlmf_14_27_no_boundary_zero {s : ℝ} (hs : s=1 ∨ s=-1) {x : ℝ} (hx : x < -1) :
    ¬Tendsto (fun ε : ℝ => associatedP 1 (-1/2) (x+s*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  intro hz0
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hp : (x:ℂ)+1 ≠ 0 := by
    intro h; have h' := congrArg Complex.re h; norm_num at h'; linarith
  have hm : (x:ℂ)-1 ≠ 0 := by
    intro h; have h' := congrArg Complex.re h; norm_num at h'; linarith
  have hnum : 2*(x:ℂ)+1 ≠ 0 := by
    intro h; have h' := congrArg Complex.re h; norm_num at h'; linarith
  have hg : Gamma (3/2:ℂ) ≠ 0 := Gamma_ne_zero (by
    intro k hk; have h' := congrArg Complex.re hk; norm_num at h';
    linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
  have hden : (3:ℂ)*Gamma (3/2) ≠ 0 := mul_ne_zero (by norm_num) hg
  let M : ℝ → ℝ := fun ε =>
    Real.exp (-(Real.log ‖(x+s*I*ε:ℂ)+1‖-Real.log ‖(x+s*I*ε:ℂ)-1‖)/4)*
      ‖2*(x+s*I*ε:ℂ)+1‖/‖(3:ℂ)*Gamma (3/2)‖
  have heq : (fun ε : ℝ => ‖associatedP 1 (-1/2) (x+s*I*ε)‖) =ᶠ[𝓝[>] (0:ℝ)] M := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    have hz : (x+s*I*ε:ℂ)-1 ∈ slitPlane := by
      apply Or.inr
      simpa using mul_ne_zero hs0 hε0.ne'
    rw [associatedP_one_neg_half hz, norm_div, norm_mul, Complex.norm_exp]
    have hre : (-(log ((x+s*I*ε:ℂ)+1)-log ((x+s*I*ε:ℂ)-1))/4).re =
        -(Real.log ‖(x+s*I*ε:ℂ)+1‖-Real.log ‖(x+s*I*ε:ℂ)-1‖)/4 := by
      norm_num [Complex.div_re, Complex.log_re] <;> ring
    rw [hre]
  have hcont : ContinuousAt M 0 := by
    dsimp [M]
    fun_prop (disch := simp [hp,hm,hden])
  have hpos : 0 < M 0 := by
    dsimp [M]
    simp only [Complex.ofReal_zero,mul_zero,add_zero]
    exact div_pos (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hnum)) (norm_pos_iff.mpr hden)
  have ht0 : Tendsto M (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hz0.norm
    simp only [norm_zero] at h
    exact h.congr' heq
  have htM : Tendsto M (𝓝[>] (0:ℝ)) (𝓝 (M 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have he := tendsto_nhds_unique htM ht0
  exact hpos.ne' he

end DLMF.Legendre
