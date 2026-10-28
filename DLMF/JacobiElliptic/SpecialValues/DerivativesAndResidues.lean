/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.SpecialValues.ThetaValues

/-!
# Jacobian elliptic derivatives and residues at special points

Derivatives and residues at the special lattice points for the twelve Jacobian functions.

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

/-! ### Derivatives and residues at the special points (helpers) -/

/-- At `p`, the function `f` has derivative `(c * g')`. -/
lemma p22R1_hasDerivAt_shift {f g : ℂ → ℂ} {c p g' : ℂ} (hfg : ∀ z, f (z + p) = c * g z)
    (hg : HasDerivAt g g' 0) : HasDerivAt f (c * g') p := by
  have hf : f = fun w => c * g (w - p) := funext fun w => by rw [← hfg, sub_add_cancel]
  rw [hf]
  have hg' : HasDerivAt g g' (p - p) := by rwa [sub_self]
  exact (hg'.comp_sub_const p p).const_mul c

/-- The map `(fun w => (w - p) * f w)` tends to `(𝓝 c)` along `(𝓝[≠] p)`. -/
lemma p22R1_residue_shift {f s : ℂ → ℂ} {c p : ℂ} (hfs : ∀ z, f (z + p) = c * (1 / s z))
    (hs : HasDerivAt s 1 0) (hs0 : s 0 = 0) :
    Tendsto (fun w => (w - p) * f w) (𝓝[≠] p) (𝓝 c) := by
  have h1 := hs.tendsto_slope_zero
  simp only [zero_add, hs0, sub_zero, smul_eq_mul] at h1
  have h2 : Tendsto (fun t => t * (1 / s t)) (𝓝[≠] 0) (𝓝 1) := by
    have := h1.inv₀ one_ne_zero
    simp only [inv_one] at this
    refine this.congr fun t => ?_
    rw [mul_inv, inv_inv, one_div]
  have h3 : Tendsto (fun w => w - p) (𝓝[≠] p) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_sub_right p).tendsto p)
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw using sub_ne_zero.mpr hw
  have h4 := (h2.comp h3).const_mul c
  rw [mul_one] at h4
  refine h4.congr fun w => ?_
  have := hfs (w - p)
  rw [sub_add_cancel] at this
  simp only [Function.comp_apply, this]
  ring

/-- Nonvanishing under the stated hypotheses: `jacobiLetterTheta q (jacobiZetak 0 k) (jacobiTauk
k) ≠ 0`. -/
theorem p22R1_reg0 {k : ℂ} (hk : k ∈ jacobiModulusDomain) {q : JacobiLetter} (hq : q ≠ .s) :
    jacobiLetterTheta q (jacobiZetak 0 k) (jacobiTauk k) ≠ 0 := by
  have : jacobiZetak 0 k = 0 := by simp [jacobiZetak]
  rw [this, je22a_letterTheta_zero (jacobiTauk_im_pos hk)]
  simp [hq]

/-- Table 22.5.1, row `sn`: the `z`-derivative of `sn(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiSnk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiSnk w k) (1) (0) ∧
    HasDerivAt (fun w => jacobiSnk w k) (0) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiSnk w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (I * compEllIntKpk k)) * jacobiSnk w k) (𝓝[≠] (I * compEllIntKpk k))
        (𝓝 (k⁻¹)) ∧
    HasDerivAt (fun w => jacobiSnk w k) (-1) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiSnk w k) (-1) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiSnk w k) (1) (2 * (I * compEllIntKpk k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiSnk (z + (0)) k = 1 * jacobiSnk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiSnk (z + (compEllIntKk k)) k = 1 * jacobiCdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiSnk_shift hk z).1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiSnk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        ((k)⁻¹) * jacobiDck z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiSnk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiSnk (z + (I * compEllIntKpk k)) k = ((k)⁻¹) * jacobiNsk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiSnk_shift hk z).2.2.1]
    have hfs : ∀ z, jacobiSnk (z + (I * compEllIntKpk k)) k = ((k)⁻¹) * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiSnk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiSnk (z + (2 * compEllIntKk k)) k = -1 * jacobiSnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiSnk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiSnk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiSnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiSnk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiSnk (z + (2 * (I * compEllIntKpk k))) k = 1 * jacobiSnk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiSnk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSnk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])

/-- Table 22.5.1, row `cn`: the `z`-derivative of `cn(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiCnk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiCnk w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiCnk w k) (-jacobiComodulusk k) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiCnk w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (I * compEllIntKpk k)) * jacobiCnk w k) (𝓝[≠] (I * compEllIntKpk k))
        (𝓝 (-I / k)) ∧
    HasDerivAt (fun w => jacobiCnk w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiCnk w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiCnk w k) (0) (2 * (I * compEllIntKpk k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiCnk (z + (0)) k = 1 * jacobiCnk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiCnk (z + (compEllIntKk k)) k = (-jacobiComodulusk k) * jacobiSdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiCnk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiCnk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I * jacobiComodulusk k / k)) * jacobiNck z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiCnk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiCnk (z + (I * compEllIntKpk k)) k = (-(I / k)) * jacobiDsk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiCnk_shift hk z).2.2.1]
    have hfs : ∀ z, jacobiCnk (z + (I * compEllIntKpk k)) k = (-(I / k)) * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCnk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiCnk (z + (2 * compEllIntKk k)) k = -1 * jacobiCnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiCnk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiCnk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        1 * jacobiCnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiCnk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiCnk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiCnk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiCnk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCnk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])

/-- Table 22.5.1, row `dn`: the `z`-derivative of `dn(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiDnk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiDnk w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiDnk w k) (0) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiDnk w k) (I * jacobiComodulusk k)
        (compEllIntKk k + I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (I * compEllIntKpk k)) * jacobiDnk w k) (𝓝[≠] (I * compEllIntKpk k))
        (𝓝 (-I)) ∧
    HasDerivAt (fun w => jacobiDnk w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiDnk w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiDnk w k) (0) (2 * (I * compEllIntKpk k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiDnk (z + (0)) k = 1 * jacobiDnk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiDnk (z + (compEllIntKk k)) k = (jacobiComodulusk k) * jacobiNdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiDnk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiDnk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (I * jacobiComodulusk k) * jacobiSck z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiDnk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiDnk (z + (I * compEllIntKpk k)) k = (-I) * jacobiCsk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiDnk_shift hk z).2.2.1]
    have hfs : ∀ z, jacobiDnk (z + (I * compEllIntKpk k)) k = (-I) * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDnk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDnk (z + (2 * compEllIntKk k)) k = 1 * jacobiDnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiDnk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiDnk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiDnk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiDnk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiDnk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiDnk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiDnk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDnk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])

/-- Table 22.5.1, row `cd`: the `z`-derivative of `cd(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiCdk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiCdk w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiCdk w k) (-1) (compEllIntKk k) ∧
    Tendsto (fun w => (w - (compEllIntKk k + I * compEllIntKpk k)) * jacobiCdk w k)
        (𝓝[≠] (compEllIntKk k + I * compEllIntKpk k))
        (𝓝 (-k⁻¹)) ∧
    HasDerivAt (fun w => jacobiCdk w k) (0) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiCdk w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiCdk w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiCdk w k) (0) (2 * (I * compEllIntKpk k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiCdk (z + (0)) k = 1 * jacobiCdk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiCdk (z + (compEllIntKk k)) k = -1 * jacobiSnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiCdk_shift hk z).1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiCdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(k)⁻¹) * jacobiNsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiCdk_shift hk z).2.1]
    have hfs : ∀ z, jacobiCdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(k)⁻¹) * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCdk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCdk (z + (I * compEllIntKpk k)) k = ((k)⁻¹) * jacobiDck z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiCdk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiCdk (z + (2 * compEllIntKk k)) k = -1 * jacobiCdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiCdk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiCdk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiCdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiCdk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiCdk (z + (2 * (I * compEllIntKpk k))) k = 1 * jacobiCdk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiCdk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCdk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])

/-- Table 22.5.1, row `sd`: the `z`-derivative of `sd(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiSdk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiSdk w k) (1) (0) ∧
    HasDerivAt (fun w => jacobiSdk w k) (0) (compEllIntKk k) ∧
    Tendsto (fun w => (w - (compEllIntKk k + I * compEllIntKpk k)) * jacobiSdk w k)
        (𝓝[≠] (compEllIntKk k + I * compEllIntKpk k))
        (𝓝 (-I / (k * jacobiComodulusk k))) ∧
    HasDerivAt (fun w => jacobiSdk w k) (0) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiSdk w k) (-1) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiSdk w k) (1) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiSdk w k) (-1) (2 * (I * compEllIntKpk k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiSdk (z + (0)) k = 1 * jacobiSdk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiSdk (z + (compEllIntKk k)) k = ((jacobiComodulusk k)⁻¹) * jacobiCnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiSdk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiSdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I / (k * jacobiComodulusk k))) * jacobiDsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiSdk_shift hk z).2.1]
    have hfs : ∀ z, jacobiSdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I / (k * jacobiComodulusk k))) * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiSdk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiSdk (z + (I * compEllIntKpk k)) k = ((I / k)) * jacobiNck z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiSdk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiSdk (z + (2 * compEllIntKk k)) k = -1 * jacobiSdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiSdk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiSdk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        1 * jacobiSdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiSdk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiSdk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiSdk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiSdk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSdk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])

/-- Table 22.5.1, row `nd`: the `z`-derivative of `nd(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiNdk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiNdk w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiNdk w k) (0) (compEllIntKk k) ∧
    Tendsto (fun w => (w - (compEllIntKk k + I * compEllIntKpk k)) * jacobiNdk w k)
        (𝓝[≠] (compEllIntKk k + I * compEllIntKpk k))
        (𝓝 (-I / jacobiComodulusk k)) ∧
    HasDerivAt (fun w => jacobiNdk w k) (I) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiNdk w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiNdk w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiNdk w k) (0) (2 * (I * compEllIntKpk k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiNdk (z + (0)) k = 1 * jacobiNdk z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiNdk (z + (compEllIntKk k)) k = ((jacobiComodulusk k)⁻¹) * jacobiDnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiNdk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiNdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I / jacobiComodulusk k)) * jacobiCsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiNdk_shift hk z).2.1]
    have hfs : ∀ z, jacobiNdk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I / jacobiComodulusk k)) * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNdk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiNdk (z + (I * compEllIntKpk k)) k = (I) * jacobiSck z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiNdk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiNdk (z + (2 * compEllIntKk k)) k = 1 * jacobiNdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiNdk_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiNdk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiNdk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiNdk_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiNdk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiNdk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiNdk_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNdk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])

/-- Table 22.5.1, row `dc`: the `z`-derivative of `dc(z, k)` at the regular
special points and the residue at the poles (proved). Corrected from the printed DLMF formula: the
printed derivative `k` of `dc` at `K + iK'` has the wrong sign; it is `-k` (numerical
differentiation and `dc' = (1 - k²) sc nc`, see the ledger). -/
@[dlmf 22.5.T1 "corrected: d dc/dz = -k at K + iK'"]
theorem jacobiDck_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiDck w k) (0) (0) ∧
    Tendsto (fun w => (w - (compEllIntKk k)) * jacobiDck w k) (𝓝[≠] (compEllIntKk k))
        (𝓝 (-1)) ∧
    HasDerivAt (fun w => jacobiDck w k) (-k) (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiDck w k) (0) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiDck w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiDck w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiDck w k) (0) (2 * (I * compEllIntKpk k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiDck (z + (0)) k = 1 * jacobiDck z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiDck (z + (compEllIntKk k)) k = -1 * jacobiNsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiDck_shift hk z).1]
        try ring
    have hfs : ∀ z, jacobiDck (z + (compEllIntKk k)) k = -1 * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDck w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDck (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-k) * jacobiSnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiDck_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiDck (z + (I * compEllIntKpk k)) k = (k) * jacobiCdk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiDck_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiDck (z + (2 * compEllIntKk k)) k = -1 * jacobiDck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiDck_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiDck (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiDck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiDck_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiDck (z + (2 * (I * compEllIntKpk k))) k = 1 * jacobiDck z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiDck_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDck w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])

/-- Table 22.5.1, row `nc`: the `z`-derivative of `nc(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiNck_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiNck w k) (0) (0) ∧
    Tendsto (fun w => (w - (compEllIntKk k)) * jacobiNck w k) (𝓝[≠] (compEllIntKk k))
        (𝓝 (-1 / jacobiComodulusk k)) ∧
    HasDerivAt (fun w => jacobiNck w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiNck w k) (I * k) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiNck w k) (0) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiNck w k) (0) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiNck w k) (0) (2 * (I * compEllIntKpk k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiNck (z + (0)) k = 1 * jacobiNck z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiNck (z + (compEllIntKk k)) k =
        (-(jacobiComodulusk k)⁻¹) * jacobiDsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiNck_shift hk z).1]
    have hfs : ∀ z, jacobiNck (z + (compEllIntKk k)) k =
        (-(jacobiComodulusk k)⁻¹) * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNck w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiNck (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        ((I * k / jacobiComodulusk k)) * jacobiCnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiNck_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiNck (z + (I * compEllIntKpk k)) k = (I * k) * jacobiSdk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiNck_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiNck (z + (2 * compEllIntKk k)) k = -1 * jacobiNck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiNck_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiNck (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        1 * jacobiNck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiNck_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiNck (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiNck z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiNck_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNck w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])

/-- Table 22.5.1, row `sc`: the `z`-derivative of `sc(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiSck_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiSck w k) (1) (0) ∧
    Tendsto (fun w => (w - (compEllIntKk k)) * jacobiSck w k) (𝓝[≠] (compEllIntKk k))
        (𝓝 (-1 / jacobiComodulusk k)) ∧
    HasDerivAt (fun w => jacobiSck w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiSck w k) (0) (I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiSck w k) (1) (2 * compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiSck w k) (-1) (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) ∧
    HasDerivAt (fun w => jacobiSck w k) (-1) (2 * (I * compEllIntKpk k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiSck (z + (0)) k = 1 * jacobiSck z k :=
      fun z => by rw [add_zero, one_mul]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiSck (z + (compEllIntKk k)) k =
        (-(jacobiComodulusk k)⁻¹) * jacobiCsk z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiSck_shift hk z).1]
    have hfs : ∀ z, jacobiSck (z + (compEllIntKk k)) k =
        (-(jacobiComodulusk k)⁻¹) * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiSck w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiSck (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        ((I / jacobiComodulusk k)) * jacobiDnk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiSck_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiSck (z + (I * compEllIntKpk k)) k = (I) * jacobiNdk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiSck_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiSck (z + (2 * compEllIntKk k)) k = 1 * jacobiSck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiSck_shift hk z).2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiSck (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiSck z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiSck_shift hk z).2.2.2.2.1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiSck (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiSck z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiSck_shift hk z).2.2.2.2.2]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiSck w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])

/-- Table 22.5.1, row `ns`: the `z`-derivative of `ns(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiNsk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    Tendsto (fun w => (w - (0)) * jacobiNsk w k) (𝓝[≠] (0))
        (𝓝 (1)) ∧
    HasDerivAt (fun w => jacobiNsk w k) (0) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiNsk w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiNsk w k) (k) (I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k)) * jacobiNsk w k) (𝓝[≠] (2 * compEllIntKk k))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) * jacobiNsk w k)
        (𝓝[≠] (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * (I * compEllIntKpk k))) * jacobiNsk w k)
        (𝓝[≠] (2 * (I * compEllIntKpk k)))
        (𝓝 (1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiNsk (z + (0)) k = 1 * jacobiNsk z k :=
      fun z => by rw [add_zero, one_mul]
    have hfs : ∀ z, jacobiNsk (z + (0)) k = 1 * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNsk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiNsk (z + (compEllIntKk k)) k = 1 * jacobiDck z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiNsk_shift hk z).1]
        try ring
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNsk w k) hfg
      (hasDerivAt_jacobiDck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiNck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiNsk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (k) * jacobiCdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiNsk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNsk w k) hfg
      (hasDerivAt_jacobiCdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiNsk (z + (I * compEllIntKpk k)) k = (k) * jacobiSnk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiNsk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiNsk w k) hfg
      (hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiNsk (z + (2 * compEllIntKk k)) k = -1 * jacobiNsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiNsk_shift hk z).2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiNsk (z + (2 * compEllIntKk k)) k = -1 * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNsk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiNsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiNsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiNsk_shift hk z).2.2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiNsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNsk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiNsk (z + (2 * (I * compEllIntKpk k))) k = 1 * jacobiNsk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiNsk_shift hk z).2.2.2.2.2]
        try ring
    have hfs : ∀ z, jacobiNsk (z + (2 * (I * compEllIntKpk k))) k = 1 * (1 / jacobiSnk z k) := by
      intro z; rw [hfg, jacobiNsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiNsk w k) hfs
      ((hasDerivAt_jacobiSnk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCnk_zero hk, jacobiDnk_zero hk]))
      (by simp [jacobiSnk_zero hk])
    convert h using 2

/-- Table 22.5.1, row `ds`: the `z`-derivative of `ds(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiDsk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    Tendsto (fun w => (w - (0)) * jacobiDsk w k) (𝓝[≠] (0))
        (𝓝 (1)) ∧
    HasDerivAt (fun w => jacobiDsk w k) (0) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiDsk w k) (I * k * jacobiComodulusk k)
        (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiDsk w k) (0) (I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k)) * jacobiDsk w k) (𝓝[≠] (2 * compEllIntKk k))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) * jacobiDsk w k)
        (𝓝[≠] (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)))
        (𝓝 (1)) ∧
    Tendsto (fun w => (w - (2 * (I * compEllIntKpk k))) * jacobiDsk w k)
        (𝓝[≠] (2 * (I * compEllIntKpk k)))
        (𝓝 (-1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiDsk (z + (0)) k = 1 * jacobiDsk z k :=
      fun z => by rw [add_zero, one_mul]
    have hfs : ∀ z, jacobiDsk (z + (0)) k = 1 * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDsk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDsk (z + (compEllIntKk k)) k = (jacobiComodulusk k) * jacobiNck z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiDsk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDsk w k) hfg
      (hasDerivAt_jacobiNck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiSck_zero hk])
  · have hfg : ∀ z, jacobiDsk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (I * k * jacobiComodulusk k) * jacobiSdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiDsk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDsk w k) hfg
      (hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk])
  · have hfg : ∀ z, jacobiDsk (z + (I * compEllIntKpk k)) k = (-(I * k)) * jacobiCnk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiDsk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiDsk w k) hfg
      (hasDerivAt_jacobiCnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiDnk_zero hk])
  · have hfg : ∀ z, jacobiDsk (z + (2 * compEllIntKk k)) k = -1 * jacobiDsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiDsk_shift hk z).2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiDsk (z + (2 * compEllIntKk k)) k = -1 * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDsk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        1 * jacobiDsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiDsk_shift hk z).2.2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiDsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        1 * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDsk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDsk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiDsk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiDsk_shift hk z).2.2.2.2.2]
        try ring
    have hfs : ∀ z, jacobiDsk (z + (2 * (I * compEllIntKpk k))) k = -1 * (1 / jacobiSdk z k) := by
      intro z; rw [hfg, jacobiDsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiDsk w k) hfs
      ((hasDerivAt_jacobiSdk hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiNdk_zero hk]))
      (by simp [jacobiSdk_zero hk])
    convert h using 2

/-- Table 22.5.1, row `cs`: the `z`-derivative of `cs(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiCsk_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    Tendsto (fun w => (w - (0)) * jacobiCsk w k) (𝓝[≠] (0))
        (𝓝 (1)) ∧
    HasDerivAt (fun w => jacobiCsk w k) (-jacobiComodulusk k) (compEllIntKk k) ∧
    HasDerivAt (fun w => jacobiCsk w k) (0) (compEllIntKk k + I * compEllIntKpk k) ∧
    HasDerivAt (fun w => jacobiCsk w k) (0) (I * compEllIntKpk k) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k)) * jacobiCsk w k) (𝓝[≠] (2 * compEllIntKk k))
        (𝓝 (1)) ∧
    Tendsto (fun w => (w - (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) * jacobiCsk w k)
        (𝓝[≠] (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * (I * compEllIntKpk k))) * jacobiCsk w k)
        (𝓝[≠] (2 * (I * compEllIntKpk k)))
        (𝓝 (-1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiCsk (z + (0)) k = 1 * jacobiCsk z k :=
      fun z => by rw [add_zero, one_mul]
    have hfs : ∀ z, jacobiCsk (z + (0)) k = 1 * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCsk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCsk (z + (compEllIntKk k)) k = (-jacobiComodulusk k) * jacobiSck z k :=
      fun z => by
        rw [show z + (compEllIntKk k) = z + compEllIntKk k by ring, (jacobiCsk_shift hk z).1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCsk w k) hfg
      (hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk])
  · have hfg : ∀ z, jacobiCsk (z + (compEllIntKk k + I * compEllIntKpk k)) k =
        (-(I * jacobiComodulusk k)) * jacobiNdk z k :=
      fun z => by
        rw [show z + (compEllIntKk k + I * compEllIntKpk k) =
            z + compEllIntKk k + I * compEllIntKpk k by ring, (jacobiCsk_shift hk z).2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCsk w k) hfg
      (hasDerivAt_jacobiNdk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiCdk_zero hk, jacobiSdk_zero hk])
  · have hfg : ∀ z, jacobiCsk (z + (I * compEllIntKpk k)) k = (-I) * jacobiDnk z k :=
      fun z => by
        rw [show z + (I * compEllIntKpk k) = z + I * compEllIntKpk k by ring,
            (jacobiCsk_shift hk z).2.2.1]
    exact (p22R1_hasDerivAt_shift (f := fun w => jacobiCsk w k) hfg
      (hasDerivAt_jacobiDnk hk (p22R1_reg0 hk (by decide)))).congr_deriv
          (by simp [jacobiSnk_zero hk, jacobiCnk_zero hk])
  · have hfg : ∀ z, jacobiCsk (z + (2 * compEllIntKk k)) k = 1 * jacobiCsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k) = z + 2 * compEllIntKk k by ring,
            (jacobiCsk_shift hk z).2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiCsk (z + (2 * compEllIntKk k)) k = 1 * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCsk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * jacobiCsk z k :=
      fun z => by
        rw [show z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k)) =
            z + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring,
                (jacobiCsk_shift hk z).2.2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiCsk (z + (2 * compEllIntKk k + 2 * (I * compEllIntKpk k))) k =
        -1 * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCsk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCsk (z + (2 * (I * compEllIntKpk k))) k = -1 * jacobiCsk z k :=
      fun z => by
        rw [show z + (2 * (I * compEllIntKpk k)) = z + 2 * (I * compEllIntKpk k) by ring,
            (jacobiCsk_shift hk z).2.2.2.2.2]
        try ring
    have hfs : ∀ z, jacobiCsk (z + (2 * (I * compEllIntKpk k))) k = -1 * (1 / jacobiSck z k) := by
      intro z; rw [hfg, jacobiCsk, jacobiPQk_eq_one_div]; rfl
    have h := p22R1_residue_shift (f := fun w => jacobiCsk w k) hfs
      ((hasDerivAt_jacobiSck hk (p22R1_reg0 hk (by decide))).congr_deriv
          (by simp [jacobiDck_zero hk, jacobiNck_zero hk]))
      (by simp [jacobiSck_zero hk])
    convert h using 2

end DLMF.JacobiElliptic
end
end
