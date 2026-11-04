/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.SpecialValues.ThetaValues

/-!
# Jacobian elliptic derivatives and residues at special points

The derivatives and residues of Table 22.5.1: for each of the twelve Jacobian elliptic
functions, the `z`-derivative at the regular special points and the residue at the poles among
`z = 0, K, K + iK', iK'`, for `k ∈ jacobiModulusDomain`.

## Main results

* `jacobiSn_specialDerivs`, `jacobiCn_specialDerivs`, `jacobiDn_specialDerivs`: Table 22.5.1,
  rows `sn, cn, dn`.
* `jacobiCd_specialDerivs`, `jacobiSd_specialDerivs`, `jacobiNd_specialDerivs`,
  `jacobiDc_specialDerivs`, `jacobiNc_specialDerivs`, `jacobiSc_specialDerivs`,
  `jacobiNs_specialDerivs`, `jacobiDs_specialDerivs`, `jacobiCs_specialDerivs`: the
  remaining rows.

## Implementation notes

The entries are proved from the derivatives of Table 22.13.1 at `z = 0` and the shift
Table 22.4.3.

**Correction.** Table 22.5.1 prints `0, k` for `dc` at `z = K + iK'`; the derivative is `-k`
(from `dc(z) = ns(z + K)`, `ns(z + 2K) = -ns z` and `ns'(iK') = k`, and numerically), which is
the form stated in `jacobiDc_specialDerivs`.
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

/-! ### Derivatives and residues at the special points (helpers) -/

/-- At `p`, the function `f` has derivative `(c * g')`. -/
private lemma hasDerivAt_of_add_eq_mul {f g : ℂ → ℂ} {c p g' : ℂ} (hfg : ∀ z, f (z + p) = c * g z)
    (hg : HasDerivAt g g' 0) : HasDerivAt f (c * g') p := by
  have hf : f = fun w => c * g (w - p) := funext fun w => by rw [← hfg, sub_add_cancel]
  rw [hf]
  have hg' : HasDerivAt g g' (p - p) := by rwa [sub_self]
  exact (hg'.comp_sub_const p p).const_mul c

/-- The map `(fun w => (w - p) * f w)` tends to `(𝓝 c)` along `(𝓝[≠] p)`. -/
private lemma tendsto_sub_mul_of_add_eq_mul_inv {f s : ℂ → ℂ} {c p : ℂ}
    (hfs : ∀ z, f (z + p) = c * (1 / s z))
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

/-- Nonvanishing under the stated hypotheses:
`jacobiLetterTheta q (jacobiThetaArgument 0 k) (jacobiTau k) ≠ 0`. -/
theorem jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    {q : JacobiLetter} (hq : q ≠ .s) :
    jacobiLetterTheta q (jacobiThetaArgument 0 k) (jacobiTau k) ≠ 0 := by
  have : jacobiThetaArgument 0 k = 0 := by simp [jacobiThetaArgument]
  rw [this, jacobiLetterTheta_zero (jacobiTau_im_pos hk)]
  simp [hq]

/-- Table 22.5.1, row `sn`: the `z`-derivative of `sn(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiSn_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiSn w k) (1) (0) ∧
    HasDerivAt (fun w => jacobiSn w k) (0) (completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiSn w k) (0) (completeEllipticK k + I * completeEllipticKPrime k) ∧
    Tendsto (fun w => (w - (I * completeEllipticKPrime k)) * jacobiSn w k)
        (𝓝[≠] (I * completeEllipticKPrime k))
        (𝓝 (k⁻¹)) ∧
    HasDerivAt (fun w => jacobiSn w k) (-1) (2 * completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiSn w k) (-1)
        (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) ∧
    HasDerivAt (fun w => jacobiSn w k) (1) (2 * (I * completeEllipticKPrime k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiSn (z + (0)) k = 1 * jacobiSn z k :=
      fun z => by rw [add_zero, one_mul]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSn w k) hfg
      (hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiSn (z + (completeEllipticK k)) k = 1 * jacobiCd z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiSn_shift hk z).1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSn w k) hfg
      (hasDerivAt_jacobiCd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiSn (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        ((k)⁻¹) * jacobiDc z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiSn_shift hk z).2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSn w k) hfg
      (hasDerivAt_jacobiDc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiNc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiSn (z + (I * completeEllipticKPrime k)) k = ((k)⁻¹) * jacobiNs z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiSn_shift hk z).2.2.1]
    have hfs : ∀ z, jacobiSn (z + (I * completeEllipticKPrime k)) k = ((k)⁻¹) *
        (1 / jacobiSn z k) := by
      intro z; rw [hfg, jacobiNs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiSn w k) hfs
      ((hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk]))
      (by simp [jacobiSn_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiSn (z + (2 * completeEllipticK k)) k = -1 * jacobiSn z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiSn_shift hk z).2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSn w k) hfg
      (hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiSn
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        -1 * jacobiSn z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiSn_shift hk z).2.2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSn w k) hfg
      (hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiSn (z + (2 * (I * completeEllipticKPrime k))) k = 1 * jacobiSn z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiSn_shift hk z).2.2.2.2.2]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSn w k) hfg
      (hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk])

/-- Table 22.5.1, row `cn`: the `z`-derivative of `cn(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiCn_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiCn w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiCn w k) (-jacobiComodulus k) (completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiCn w k) (0) (completeEllipticK k + I * completeEllipticKPrime k) ∧
    Tendsto (fun w => (w - (I * completeEllipticKPrime k)) * jacobiCn w k)
        (𝓝[≠] (I * completeEllipticKPrime k))
        (𝓝 (-I / k)) ∧
    HasDerivAt (fun w => jacobiCn w k) (0) (2 * completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiCn w k) (0)
        (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) ∧
    HasDerivAt (fun w => jacobiCn w k) (0) (2 * (I * completeEllipticKPrime k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiCn (z + (0)) k = 1 * jacobiCn z k :=
      fun z => by rw [add_zero, one_mul]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCn w k) hfg
      (hasDerivAt_jacobiCn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiCn (z + (completeEllipticK k)) k = (-jacobiComodulus k) * jacobiSd z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiCn_shift hk z).1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCn w k) hfg
      (hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiCn (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (-(I * jacobiComodulus k / k)) * jacobiNc z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiCn_shift hk z).2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCn w k) hfg
      (hasDerivAt_jacobiNc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiCn (z + (I * completeEllipticKPrime k)) k = (-(I / k)) * jacobiDs z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiCn_shift hk z).2.2.1]
    have hfs : ∀ z, jacobiCn (z + (I * completeEllipticKPrime k)) k = (-(I / k)) *
        (1 / jacobiSd z k) := by
      intro z; rw [hfg, jacobiDs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiCn w k) hfs
      ((hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk]))
      (by simp [jacobiSd_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiCn (z + (2 * completeEllipticK k)) k = -1 * jacobiCn z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiCn_shift hk z).2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCn w k) hfg
      (hasDerivAt_jacobiCn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiCn
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        1 * jacobiCn z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiCn_shift hk z).2.2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCn w k) hfg
      (hasDerivAt_jacobiCn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiCn (z + (2 * (I * completeEllipticKPrime k))) k = -1 * jacobiCn z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiCn_shift hk z).2.2.2.2.2]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCn w k) hfg
      (hasDerivAt_jacobiCn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiDn_zero hk])

/-- Table 22.5.1, row `dn`: the `z`-derivative of `dn(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiDn_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiDn w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiDn w k) (0) (completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiDn w k) (I * jacobiComodulus k)
        (completeEllipticK k + I * completeEllipticKPrime k) ∧
    Tendsto (fun w => (w - (I * completeEllipticKPrime k)) * jacobiDn w k)
        (𝓝[≠] (I * completeEllipticKPrime k))
        (𝓝 (-I)) ∧
    HasDerivAt (fun w => jacobiDn w k) (0) (2 * completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiDn w k) (0)
        (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) ∧
    HasDerivAt (fun w => jacobiDn w k) (0) (2 * (I * completeEllipticKPrime k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiDn (z + (0)) k = 1 * jacobiDn z k :=
      fun z => by rw [add_zero, one_mul]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDn w k) hfg
      (hasDerivAt_jacobiDn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiCn_zero hk])
  · have hfg : ∀ z, jacobiDn (z + (completeEllipticK k)) k = (jacobiComodulus k) * jacobiNd z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiDn_shift hk z).1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDn w k) hfg
      (hasDerivAt_jacobiNd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiSd_zero hk])
  · have hfg : ∀ z, jacobiDn (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (I * jacobiComodulus k) * jacobiSc z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiDn_shift hk z).2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDn w k) hfg
      (hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk])
  · have hfg : ∀ z, jacobiDn (z + (I * completeEllipticKPrime k)) k = (-I) * jacobiCs z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiDn_shift hk z).2.2.1]
    have hfs : ∀ z, jacobiDn (z + (I * completeEllipticKPrime k)) k = (-I) *
        (1 / jacobiSc z k) := by
      intro z; rw [hfg, jacobiCs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiDn w k) hfs
      ((hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk]))
      (by simp [jacobiSc_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDn (z + (2 * completeEllipticK k)) k = 1 * jacobiDn z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiDn_shift hk z).2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDn w k) hfg
      (hasDerivAt_jacobiDn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiCn_zero hk])
  · have hfg : ∀ z, jacobiDn
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        -1 * jacobiDn z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiDn_shift hk z).2.2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDn w k) hfg
      (hasDerivAt_jacobiDn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiCn_zero hk])
  · have hfg : ∀ z, jacobiDn (z + (2 * (I * completeEllipticKPrime k))) k = -1 * jacobiDn z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiDn_shift hk z).2.2.2.2.2]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDn w k) hfg
      (hasDerivAt_jacobiDn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiCn_zero hk])

/-- Table 22.5.1, row `cd`: the `z`-derivative of `cd(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiCd_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiCd w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiCd w k) (-1) (completeEllipticK k) ∧
    Tendsto (fun w => (w - (completeEllipticK k + I * completeEllipticKPrime k)) * jacobiCd w k)
        (𝓝[≠] (completeEllipticK k + I * completeEllipticKPrime k))
        (𝓝 (-k⁻¹)) ∧
    HasDerivAt (fun w => jacobiCd w k) (0) (I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiCd w k) (0) (2 * completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiCd w k) (0)
        (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) ∧
    HasDerivAt (fun w => jacobiCd w k) (0) (2 * (I * completeEllipticKPrime k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiCd (z + (0)) k = 1 * jacobiCd z k :=
      fun z => by rw [add_zero, one_mul]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCd w k) hfg
      (hasDerivAt_jacobiCd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiCd (z + (completeEllipticK k)) k = -1 * jacobiSn z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiCd_shift hk z).1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCd w k) hfg
      (hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiCd (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (-(k)⁻¹) * jacobiNs z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiCd_shift hk z).2.1]
    have hfs : ∀ z, jacobiCd (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (-(k)⁻¹) * (1 / jacobiSn z k) := by
      intro z; rw [hfg, jacobiNs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiCd w k) hfs
      ((hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk]))
      (by simp [jacobiSn_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCd (z + (I * completeEllipticKPrime k)) k = ((k)⁻¹) * jacobiDc z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiCd_shift hk z).2.2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCd w k) hfg
      (hasDerivAt_jacobiDc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiNc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiCd (z + (2 * completeEllipticK k)) k = -1 * jacobiCd z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiCd_shift hk z).2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCd w k) hfg
      (hasDerivAt_jacobiCd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiCd
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        -1 * jacobiCd z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiCd_shift hk z).2.2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCd w k) hfg
      (hasDerivAt_jacobiCd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiCd (z + (2 * (I * completeEllipticKPrime k))) k = 1 * jacobiCd z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiCd_shift hk z).2.2.2.2.2]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCd w k) hfg
      (hasDerivAt_jacobiCd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSd_zero hk, jacobiNd_zero hk])

/-- Table 22.5.1, row `sd`: the `z`-derivative of `sd(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiSd_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiSd w k) (1) (0) ∧
    HasDerivAt (fun w => jacobiSd w k) (0) (completeEllipticK k) ∧
    Tendsto (fun w => (w - (completeEllipticK k + I * completeEllipticKPrime k)) * jacobiSd w k)
        (𝓝[≠] (completeEllipticK k + I * completeEllipticKPrime k))
        (𝓝 (-I / (k * jacobiComodulus k))) ∧
    HasDerivAt (fun w => jacobiSd w k) (0) (I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiSd w k) (-1) (2 * completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiSd w k) (1)
        (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) ∧
    HasDerivAt (fun w => jacobiSd w k) (-1) (2 * (I * completeEllipticKPrime k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiSd (z + (0)) k = 1 * jacobiSd z k :=
      fun z => by rw [add_zero, one_mul]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSd w k) hfg
      (hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiSd (z + (completeEllipticK k)) k = ((jacobiComodulus k)⁻¹) *
        jacobiCn z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiSd_shift hk z).1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSd w k) hfg
      (hasDerivAt_jacobiCn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiSd (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (-(I / (k * jacobiComodulus k))) * jacobiDs z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiSd_shift hk z).2.1]
    have hfs : ∀ z, jacobiSd (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (-(I / (k * jacobiComodulus k))) * (1 / jacobiSd z k) := by
      intro z; rw [hfg, jacobiDs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiSd w k) hfs
      ((hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk]))
      (by simp [jacobiSd_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiSd (z + (I * completeEllipticKPrime k)) k = ((I / k)) * jacobiNc z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiSd_shift hk z).2.2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSd w k) hfg
      (hasDerivAt_jacobiNc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiSd (z + (2 * completeEllipticK k)) k = -1 * jacobiSd z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiSd_shift hk z).2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSd w k) hfg
      (hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiSd
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        1 * jacobiSd z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiSd_shift hk z).2.2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSd w k) hfg
      (hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiSd (z + (2 * (I * completeEllipticKPrime k))) k = -1 * jacobiSd z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiSd_shift hk z).2.2.2.2.2]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSd w k) hfg
      (hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk])

/-- Table 22.5.1, row `nd`: the `z`-derivative of `nd(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiNd_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiNd w k) (0) (0) ∧
    HasDerivAt (fun w => jacobiNd w k) (0) (completeEllipticK k) ∧
    Tendsto (fun w => (w - (completeEllipticK k + I * completeEllipticKPrime k)) * jacobiNd w k)
        (𝓝[≠] (completeEllipticK k + I * completeEllipticKPrime k))
        (𝓝 (-I / jacobiComodulus k)) ∧
    HasDerivAt (fun w => jacobiNd w k) (I) (I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiNd w k) (0) (2 * completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiNd w k) (0)
        (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) ∧
    HasDerivAt (fun w => jacobiNd w k) (0) (2 * (I * completeEllipticKPrime k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiNd (z + (0)) k = 1 * jacobiNd z k :=
      fun z => by rw [add_zero, one_mul]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNd w k) hfg
      (hasDerivAt_jacobiNd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiSd_zero hk])
  · have hfg : ∀ z, jacobiNd (z + (completeEllipticK k)) k = ((jacobiComodulus k)⁻¹) *
        jacobiDn z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiNd_shift hk z).1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNd w k) hfg
      (hasDerivAt_jacobiDn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiCn_zero hk])
  · have hfg : ∀ z, jacobiNd (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (-(I / jacobiComodulus k)) * jacobiCs z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiNd_shift hk z).2.1]
    have hfs : ∀ z, jacobiNd (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (-(I / jacobiComodulus k)) * (1 / jacobiSc z k) := by
      intro z; rw [hfg, jacobiCs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiNd w k) hfs
      ((hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk]))
      (by simp [jacobiSc_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiNd (z + (I * completeEllipticKPrime k)) k = (I) * jacobiSc z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiNd_shift hk z).2.2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNd w k) hfg
      (hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk])
  · have hfg : ∀ z, jacobiNd (z + (2 * completeEllipticK k)) k = 1 * jacobiNd z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiNd_shift hk z).2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNd w k) hfg
      (hasDerivAt_jacobiNd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiSd_zero hk])
  · have hfg : ∀ z, jacobiNd
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        -1 * jacobiNd z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiNd_shift hk z).2.2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNd w k) hfg
      (hasDerivAt_jacobiNd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiSd_zero hk])
  · have hfg : ∀ z, jacobiNd (z + (2 * (I * completeEllipticKPrime k))) k = -1 * jacobiNd z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiNd_shift hk z).2.2.2.2.2]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNd w k) hfg
      (hasDerivAt_jacobiNd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiSd_zero hk])

/-- Table 22.5.1, row `dc`: the `z`-derivative of `dc(z, k)` at the regular
special points and the residue at the poles (proved). Corrected from the printed DLMF formula: the
printed derivative `k` of `dc` at `K + iK'` has the wrong sign; it is `-k` (numerical
differentiation and `dc' = (1 - k²) sc nc`, see the ledger). -/
@[dlmf 22.5.T1 "corrected: d dc/dz = -k at K + iK'"]
theorem jacobiDc_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiDc w k) (0) (0) ∧
    Tendsto (fun w => (w - (completeEllipticK k)) * jacobiDc w k) (𝓝[≠] (completeEllipticK k))
        (𝓝 (-1)) ∧
    HasDerivAt (fun w => jacobiDc w k) (-k) (completeEllipticK k + I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiDc w k) (0) (I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiDc w k) (0) (2 * completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiDc w k) (0)
        (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) ∧
    HasDerivAt (fun w => jacobiDc w k) (0) (2 * (I * completeEllipticKPrime k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiDc (z + (0)) k = 1 * jacobiDc z k :=
      fun z => by rw [add_zero, one_mul]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDc w k) hfg
      (hasDerivAt_jacobiDc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiNc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiDc (z + (completeEllipticK k)) k = -1 * jacobiNs z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiDc_shift hk z).1]
        try ring
    have hfs : ∀ z, jacobiDc (z + (completeEllipticK k)) k = -1 * (1 / jacobiSn z k) := by
      intro z; rw [hfg, jacobiNs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiDc w k) hfs
      ((hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk]))
      (by simp [jacobiSn_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDc (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (-k) * jacobiSn z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiDc_shift hk z).2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDc w k) hfg
      (hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiDc (z + (I * completeEllipticKPrime k)) k = (k) * jacobiCd z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiDc_shift hk z).2.2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDc w k) hfg
      (hasDerivAt_jacobiCd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiDc (z + (2 * completeEllipticK k)) k = -1 * jacobiDc z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiDc_shift hk z).2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDc w k) hfg
      (hasDerivAt_jacobiDc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiNc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiDc
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        -1 * jacobiDc z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiDc_shift hk z).2.2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDc w k) hfg
      (hasDerivAt_jacobiDc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiNc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiDc (z + (2 * (I * completeEllipticKPrime k))) k = 1 * jacobiDc z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiDc_shift hk z).2.2.2.2.2]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDc w k) hfg
      (hasDerivAt_jacobiDc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiNc_zero hk, jacobiSc_zero hk])

/-- Table 22.5.1, row `nc`: the `z`-derivative of `nc(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiNc_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiNc w k) (0) (0) ∧
    Tendsto (fun w => (w - (completeEllipticK k)) * jacobiNc w k) (𝓝[≠] (completeEllipticK k))
        (𝓝 (-1 / jacobiComodulus k)) ∧
    HasDerivAt (fun w => jacobiNc w k) (0) (completeEllipticK k + I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiNc w k) (I * k) (I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiNc w k) (0) (2 * completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiNc w k) (0)
        (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) ∧
    HasDerivAt (fun w => jacobiNc w k) (0) (2 * (I * completeEllipticKPrime k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiNc (z + (0)) k = 1 * jacobiNc z k :=
      fun z => by rw [add_zero, one_mul]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNc w k) hfg
      (hasDerivAt_jacobiNc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiNc (z + (completeEllipticK k)) k =
        (-(jacobiComodulus k)⁻¹) * jacobiDs z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiNc_shift hk z).1]
    have hfs : ∀ z, jacobiNc (z + (completeEllipticK k)) k =
        (-(jacobiComodulus k)⁻¹) * (1 / jacobiSd z k) := by
      intro z; rw [hfg, jacobiDs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiNc w k) hfs
      ((hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk]))
      (by simp [jacobiSd_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiNc (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        ((I * k / jacobiComodulus k)) * jacobiCn z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiNc_shift hk z).2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNc w k) hfg
      (hasDerivAt_jacobiCn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiNc (z + (I * completeEllipticKPrime k)) k = (I * k) * jacobiSd z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiNc_shift hk z).2.2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNc w k) hfg
      (hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiNc (z + (2 * completeEllipticK k)) k = -1 * jacobiNc z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiNc_shift hk z).2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNc w k) hfg
      (hasDerivAt_jacobiNc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiNc
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        1 * jacobiNc z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiNc_shift hk z).2.2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNc w k) hfg
      (hasDerivAt_jacobiNc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiNc (z + (2 * (I * completeEllipticKPrime k))) k = -1 * jacobiNc z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiNc_shift hk z).2.2.2.2.2]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNc w k) hfg
      (hasDerivAt_jacobiNc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiSc_zero hk])

/-- Table 22.5.1, row `sc`: the `z`-derivative of `sc(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiSc_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    HasDerivAt (fun w => jacobiSc w k) (1) (0) ∧
    Tendsto (fun w => (w - (completeEllipticK k)) * jacobiSc w k) (𝓝[≠] (completeEllipticK k))
        (𝓝 (-1 / jacobiComodulus k)) ∧
    HasDerivAt (fun w => jacobiSc w k) (0) (completeEllipticK k + I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiSc w k) (0) (I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiSc w k) (1) (2 * completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiSc w k) (-1)
        (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) ∧
    HasDerivAt (fun w => jacobiSc w k) (-1) (2 * (I * completeEllipticKPrime k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiSc (z + (0)) k = 1 * jacobiSc z k :=
      fun z => by rw [add_zero, one_mul]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSc w k) hfg
      (hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk])
  · have hfg : ∀ z, jacobiSc (z + (completeEllipticK k)) k =
        (-(jacobiComodulus k)⁻¹) * jacobiCs z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiSc_shift hk z).1]
    have hfs : ∀ z, jacobiSc (z + (completeEllipticK k)) k =
        (-(jacobiComodulus k)⁻¹) * (1 / jacobiSc z k) := by
      intro z; rw [hfg, jacobiCs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiSc w k) hfs
      ((hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk]))
      (by simp [jacobiSc_zero hk])
    convert h using 2
    ring
  · have hfg : ∀ z, jacobiSc (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        ((I / jacobiComodulus k)) * jacobiDn z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiSc_shift hk z).2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSc w k) hfg
      (hasDerivAt_jacobiDn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiCn_zero hk])
  · have hfg : ∀ z, jacobiSc (z + (I * completeEllipticKPrime k)) k = (I) * jacobiNd z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiSc_shift hk z).2.2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSc w k) hfg
      (hasDerivAt_jacobiNd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiSd_zero hk])
  · have hfg : ∀ z, jacobiSc (z + (2 * completeEllipticK k)) k = 1 * jacobiSc z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiSc_shift hk z).2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSc w k) hfg
      (hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk])
  · have hfg : ∀ z, jacobiSc
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        -1 * jacobiSc z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiSc_shift hk z).2.2.2.2.1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSc w k) hfg
      (hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk])
  · have hfg : ∀ z, jacobiSc (z + (2 * (I * completeEllipticKPrime k))) k = -1 * jacobiSc z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiSc_shift hk z).2.2.2.2.2]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiSc w k) hfg
      (hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk])

/-- Table 22.5.1, row `ns`: the `z`-derivative of `ns(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiNs_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    Tendsto (fun w => (w - (0)) * jacobiNs w k) (𝓝[≠] (0))
        (𝓝 (1)) ∧
    HasDerivAt (fun w => jacobiNs w k) (0) (completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiNs w k) (0) (completeEllipticK k + I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiNs w k) (k) (I * completeEllipticKPrime k) ∧
    Tendsto (fun w => (w - (2 * completeEllipticK k)) * jacobiNs w k)
        (𝓝[≠] (2 * completeEllipticK k))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)))
        * jacobiNs w k)
        (𝓝[≠] (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * (I * completeEllipticKPrime k))) * jacobiNs w k)
        (𝓝[≠] (2 * (I * completeEllipticKPrime k)))
        (𝓝 (1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiNs (z + (0)) k = 1 * jacobiNs z k :=
      fun z => by rw [add_zero, one_mul]
    have hfs : ∀ z, jacobiNs (z + (0)) k = 1 * (1 / jacobiSn z k) := by
      intro z; rw [hfg, jacobiNs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiNs w k) hfs
      ((hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk]))
      (by simp [jacobiSn_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiNs (z + (completeEllipticK k)) k = 1 * jacobiDc z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiNs_shift hk z).1]
        try ring
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNs w k) hfg
      (hasDerivAt_jacobiDc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiNc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiNs (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (k) * jacobiCd z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiNs_shift hk z).2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNs w k) hfg
      (hasDerivAt_jacobiCd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiNs (z + (I * completeEllipticKPrime k)) k = (k) * jacobiSn z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiNs_shift hk z).2.2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiNs w k) hfg
      (hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiNs (z + (2 * completeEllipticK k)) k = -1 * jacobiNs z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiNs_shift hk z).2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiNs (z + (2 * completeEllipticK k)) k = -1 * (1 / jacobiSn z k) := by
      intro z; rw [hfg, jacobiNs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiNs w k) hfs
      ((hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk]))
      (by simp [jacobiSn_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiNs
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        -1 * jacobiNs z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiNs_shift hk z).2.2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiNs
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        -1 * (1 / jacobiSn z k) := by
      intro z; rw [hfg, jacobiNs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiNs w k) hfs
      ((hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk]))
      (by simp [jacobiSn_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiNs (z + (2 * (I * completeEllipticKPrime k))) k = 1 * jacobiNs z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiNs_shift hk z).2.2.2.2.2]
        try ring
    have hfs : ∀ z, jacobiNs (z + (2 * (I * completeEllipticKPrime k))) k = 1 *
        (1 / jacobiSn z k) := by
      intro z; rw [hfg, jacobiNs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiNs w k) hfs
      ((hasDerivAt_jacobiSn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCn_zero hk, jacobiDn_zero hk]))
      (by simp [jacobiSn_zero hk])
    convert h using 2

/-- Table 22.5.1, row `ds`: the `z`-derivative of `ds(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiDs_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    Tendsto (fun w => (w - (0)) * jacobiDs w k) (𝓝[≠] (0))
        (𝓝 (1)) ∧
    HasDerivAt (fun w => jacobiDs w k) (0) (completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiDs w k) (I * k * jacobiComodulus k)
        (completeEllipticK k + I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiDs w k) (0) (I * completeEllipticKPrime k) ∧
    Tendsto (fun w => (w - (2 * completeEllipticK k)) * jacobiDs w k)
        (𝓝[≠] (2 * completeEllipticK k))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)))
        * jacobiDs w k)
        (𝓝[≠] (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)))
        (𝓝 (1)) ∧
    Tendsto (fun w => (w - (2 * (I * completeEllipticKPrime k))) * jacobiDs w k)
        (𝓝[≠] (2 * (I * completeEllipticKPrime k)))
        (𝓝 (-1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiDs (z + (0)) k = 1 * jacobiDs z k :=
      fun z => by rw [add_zero, one_mul]
    have hfs : ∀ z, jacobiDs (z + (0)) k = 1 * (1 / jacobiSd z k) := by
      intro z; rw [hfg, jacobiDs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiDs w k) hfs
      ((hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk]))
      (by simp [jacobiSd_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDs (z + (completeEllipticK k)) k = (jacobiComodulus k) * jacobiNc z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiDs_shift hk z).1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDs w k) hfg
      (hasDerivAt_jacobiNc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiSc_zero hk])
  · have hfg : ∀ z, jacobiDs (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (I * k * jacobiComodulus k) * jacobiSd z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiDs_shift hk z).2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDs w k) hfg
      (hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk])
  · have hfg : ∀ z, jacobiDs (z + (I * completeEllipticKPrime k)) k = (-(I * k)) * jacobiCn z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiDs_shift hk z).2.2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiDs w k) hfg
      (hasDerivAt_jacobiCn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiDn_zero hk])
  · have hfg : ∀ z, jacobiDs (z + (2 * completeEllipticK k)) k = -1 * jacobiDs z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiDs_shift hk z).2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiDs (z + (2 * completeEllipticK k)) k = -1 * (1 / jacobiSd z k) := by
      intro z; rw [hfg, jacobiDs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiDs w k) hfs
      ((hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk]))
      (by simp [jacobiSd_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDs
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        1 * jacobiDs z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiDs_shift hk z).2.2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiDs
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        1 * (1 / jacobiSd z k) := by
      intro z; rw [hfg, jacobiDs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiDs w k) hfs
      ((hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk]))
      (by simp [jacobiSd_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiDs (z + (2 * (I * completeEllipticKPrime k))) k = -1 * jacobiDs z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiDs_shift hk z).2.2.2.2.2]
        try ring
    have hfs : ∀ z, jacobiDs (z + (2 * (I * completeEllipticKPrime k))) k = -1 *
        (1 / jacobiSd z k) := by
      intro z; rw [hfg, jacobiDs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiDs w k) hfs
      ((hasDerivAt_jacobiSd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiNd_zero hk]))
      (by simp [jacobiSd_zero hk])
    convert h using 2

/-- Table 22.5.1, row `cs`: the `z`-derivative of `cs(z, k)` at the regular
special points and the residue at the poles (from Table 22.13.1 and the shifts of Table 22.4.3). -/
@[dlmf 22.5.T1]
theorem jacobiCs_specialDerivs {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    Tendsto (fun w => (w - (0)) * jacobiCs w k) (𝓝[≠] (0))
        (𝓝 (1)) ∧
    HasDerivAt (fun w => jacobiCs w k) (-jacobiComodulus k) (completeEllipticK k) ∧
    HasDerivAt (fun w => jacobiCs w k) (0) (completeEllipticK k + I * completeEllipticKPrime k) ∧
    HasDerivAt (fun w => jacobiCs w k) (0) (I * completeEllipticKPrime k) ∧
    Tendsto (fun w => (w - (2 * completeEllipticK k)) * jacobiCs w k)
        (𝓝[≠] (2 * completeEllipticK k))
        (𝓝 (1)) ∧
    Tendsto (fun w => (w - (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)))
        * jacobiCs w k)
        (𝓝[≠] (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)))
        (𝓝 (-1)) ∧
    Tendsto (fun w => (w - (2 * (I * completeEllipticKPrime k))) * jacobiCs w k)
        (𝓝[≠] (2 * (I * completeEllipticKPrime k)))
        (𝓝 (-1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfg : ∀ z, jacobiCs (z + (0)) k = 1 * jacobiCs z k :=
      fun z => by rw [add_zero, one_mul]
    have hfs : ∀ z, jacobiCs (z + (0)) k = 1 * (1 / jacobiSc z k) := by
      intro z; rw [hfg, jacobiCs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiCs w k) hfs
      ((hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk]))
      (by simp [jacobiSc_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCs (z + (completeEllipticK k)) k = (-jacobiComodulus k) * jacobiSc z k :=
      fun z => by
        rw [show z + (completeEllipticK k) = z + completeEllipticK k by ring,
                                                                          (jacobiCs_shift hk z).1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCs w k) hfg
      (hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk])
  · have hfg : ∀ z, jacobiCs (z + (completeEllipticK k + I * completeEllipticKPrime k)) k =
        (-(I * jacobiComodulus k)) * jacobiNd z k :=
      fun z => by
        rw [show z + (completeEllipticK k + I * completeEllipticKPrime k) =
            z + completeEllipticK k + I * completeEllipticKPrime k by ring,
                                                                        (jacobiCs_shift hk z).2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCs w k) hfg
      (hasDerivAt_jacobiNd hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiCd_zero hk, jacobiSd_zero hk])
  · have hfg : ∀ z, jacobiCs (z + (I * completeEllipticKPrime k)) k = (-I) * jacobiDn z k :=
      fun z => by
        rw [show z + (I * completeEllipticKPrime k) = z + I * completeEllipticKPrime k by ring,
            (jacobiCs_shift hk z).2.2.1]
    exact (hasDerivAt_of_add_eq_mul (f := fun w => jacobiCs w k) hfg
      (hasDerivAt_jacobiDn hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide)))).congr_deriv
          (by simp [jacobiSn_zero hk, jacobiCn_zero hk])
  · have hfg : ∀ z, jacobiCs (z + (2 * completeEllipticK k)) k = 1 * jacobiCs z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k) = z + 2 * completeEllipticK k by ring,
            (jacobiCs_shift hk z).2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiCs (z + (2 * completeEllipticK k)) k = 1 * (1 / jacobiSc z k) := by
      intro z; rw [hfg, jacobiCs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiCs w k) hfs
      ((hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk]))
      (by simp [jacobiSc_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCs
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        -1 * jacobiCs z k :=
      fun z => by
        rw [show z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k)) =
            z + 2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k) by ring,
                (jacobiCs_shift hk z).2.2.2.2.1]
        try ring
    have hfs : ∀ z, jacobiCs
        (z + (2 * completeEllipticK k + 2 * (I * completeEllipticKPrime k))) k =
        -1 * (1 / jacobiSc z k) := by
      intro z; rw [hfg, jacobiCs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiCs w k) hfs
      ((hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk]))
      (by simp [jacobiSc_zero hk])
    convert h using 2
  · have hfg : ∀ z, jacobiCs (z + (2 * (I * completeEllipticKPrime k))) k = -1 * jacobiCs z k :=
      fun z => by
        rw [show z + (2 * (I * completeEllipticKPrime k)) = z + 2 *
            (I * completeEllipticKPrime k) by ring,
            (jacobiCs_shift hk z).2.2.2.2.2]
        try ring
    have hfs : ∀ z, jacobiCs (z + (2 * (I * completeEllipticKPrime k))) k = -1 *
        (1 / jacobiSc z k) := by
      intro z; rw [hfg, jacobiCs, jacobiPQ_eq_one_div]; rfl
    have h := tendsto_sub_mul_of_add_eq_mul_inv (f := fun w => jacobiCs w k) hfs
      ((hasDerivAt_jacobiSc hk
          (jacobiLetterTheta_jacobiThetaArgument_zero_ne_zero hk (by decide))).congr_deriv
          (by simp [jacobiDc_zero hk, jacobiNc_zero hk]))
      (by simp [jacobiSc_zero hk])
    convert h using 2

end DLMF.JacobiElliptic
end
end
