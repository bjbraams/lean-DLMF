/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.SpecialValues
public import DLMF.Lame.Polynomials.P2pODE
public import DLMF.Weierstrass.Relations

/-!
# Lamé's equation in Weierstrass form (DLMF 29.2.6–29.2.9, 29.2.12)

For real `e₁ > e₂ > e₃` with `e₁ + e₂ + e₃ = 0` and `(e₂ - e₃)/(e₁ - e₃) = k²`, a solution `w`
of Lamé's equation 29.2.1 gives the solution `η ↦ w(aη + iK')`, `a = √(e₁ - e₃)`, of the
Weierstrass form 29.2.9 with `g = (e₁ - e₃)h + ν(ν+1)e₃` (`p3l_weierstrass`).

The lattice is `ω₁ = K/a`, `ω₃ = iK'/a` (`p3lHP`), with `τ = iK'/K`; by Jacobi's inversion
22.2.2 its modulus is `k` and its quarter period is `K`, so 23.6.16 and 23.6.17 identify its roots
with `e₁, e₂, e₃` and its invariants with `g₂, g₃`, and 23.6.26 gives
`℘(η) - e₃ = (e₁ - e₃) k² sn²(aη + iK')` off the lattice. At lattice points (the poles of
`sn(aη + iK')`) both equations reduce to the same one because `ν(ν+1) w = 0` there
(`p3l_pole_zero`: near a pole `ν(ν+1) w = (w'' + h w) sn²(z - z₀)`).
-/

@[expose] public noncomputable section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set
open scoped Topology Real

namespace DLMF.Lame

variable {k : ℝ}

/-- `sn²` has the periods `2K` and `2iK'` (all integer combinations). -/
lemma p3l_sn_sq_lattice (hk0 : 0 < k) (hk1 : k < 1) (z : ℂ) (m n : ℤ) :
    jacobiSnk (z + m * (2 * (Real.compEllIntKm (k ^ 2) : ℂ)) +
      n * (2 * (I * Real.compEllIntKm (1 - k ^ 2)))) k ^ 2 = jacobiSnk z k ^ 2 := by
  obtain ⟨⟨s1, -, -⟩, ⟨s2, -, -⟩, -⟩ := p1l_shifts hk0 hk1 z
  have p1 : Function.Periodic (fun z => jacobiSnk z k ^ 2) (2 * (Real.compEllIntKm (k ^ 2) : ℂ)) :=
    fun z => by
      obtain ⟨⟨s1, -, -⟩, -⟩ := p1l_shifts hk0 hk1 z
      simp only [s1, neg_sq]
  have p2 : Function.Periodic (fun z => jacobiSnk z k ^ 2)
      (2 * (I * Real.compEllIntKm (1 - k ^ 2))) := fun z => by
    obtain ⟨-, ⟨s2, -, -⟩, -⟩ := p1l_shifts hk0 hk1 z
    simp only [← mul_assoc, s2]
  have := (p2.int_mul n) (z + m * (2 * (Real.compEllIntKm (k ^ 2) : ℂ)))
  rw [this]
  exact (p1.int_mul m) z

/-- At the poles `z₀ = 2mK + (2n+1)iK'` of `sn`: `sn²(z₀ + u) = 1/(k² sn²(u))` for all `u`
(both sides are Lean's `0` where `sn(u) = 0`). -/
lemma p3l_sn_sq_pole (hk0 : 0 < k) (hk1 : k < 1) (m n : ℤ) (u : ℂ) :
    jacobiSnk (m * (2 * (Real.compEllIntKm (k ^ 2) : ℂ)) +
      n * (2 * (I * Real.compEllIntKm (1 - k ^ 2))) + I * Real.compEllIntKm (1 - k ^ 2) + u) k ^ 2 =
      ((k : ℂ) ^ 2 * jacobiSnk u k ^ 2)⁻¹ := by
  have hkD := p22R1_ofReal_mem hk0 hk1
  have hK' : compEllIntKpk (k : ℂ) = Real.compEllIntKm (1 - k ^ 2) :=
    compEllIntKpk_ofReal (by positivity)
  have e := p3l_sn_sq_lattice hk0 hk1 (u + I * Real.compEllIntKm (1 - k ^ 2)) m n
  rw [show (m : ℂ) * (2 * (Real.compEllIntKm (k ^ 2) : ℂ)) +
      n * (2 * (I * Real.compEllIntKm (1 - k ^ 2))) + I * Real.compEllIntKm (1 - k ^ 2) + u =
      u + I * Real.compEllIntKm (1 - k ^ 2) + m * (2 * (Real.compEllIntKm (k ^ 2) : ℂ)) +
      n * (2 * (I * Real.compEllIntKm (1 - k ^ 2))) by ring, e]
  have s := (jacobiSnk_shift hkD u).2.2.1
  rw [hK'] at s
  rw [s, jacobiNsk, jacobiPQk_eq_one_div, ← jacobiSnk]
  rw [mul_pow, inv_pow, div_pow, one_pow, mul_inv, one_div]

/-- **At a pole of `sn`, a solution of Lamé's equation satisfies `ν(ν+1) w(z₀) = 0`**: near
`z₀` the equation reads `ν(ν+1) w = (w'' + h w) sn²(z - z₀)` and both sides are continuous. -/
lemma p3l_pole_zero (hk0 : 0 < k) (hk1 : k < 1) {h ν : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hw : IsLameSolutionOn h ν k w U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hpole : ∀ u, jacobiSnk (z₀ + u) k ^ 2 = ((k : ℂ) ^ 2 * jacobiSnk u k ^ 2)⁻¹) :
    ν * (ν + 1) * w z₀ = 0 := by
  have hkD := p22R1_ofReal_mem hk0 hk1
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hA : AnalyticAt ℂ w z₀ := DifferentiableOn.analyticAt
    (fun z hz => (hw.differentiableAt z hz).differentiableWithinAt) (hU.mem_nhds hz₀)
  have hA2 : AnalyticAt ℂ (deriv w) z₀ := DifferentiableOn.analyticAt
    (fun z hz => (hw.hasDerivAt_deriv z hz).differentiableAt.differentiableWithinAt)
    (hU.mem_nhds hz₀)
  have hsn : HasDerivAt (fun u => jacobiSnk u k) 1 0 := by
    have := hasDerivAt_jacobiSnk hkD
      (by have := p2p_regular_real hk0 hk1 0; simpa [JacobiRegulark] using this)
    simpa [jacobiCnk_zero hkD, jacobiDnk_zero hkD] using this
  set F : ℂ → ℂ := fun u => ν * (ν + 1) * w (z₀ + u)
  set G : ℂ → ℂ := fun u => (deriv (deriv w) (z₀ + u) + h * w (z₀ + u)) * jacobiSnk u k ^ 2
  have hcF : ContinuousAt F 0 := by
    have : ContinuousAt (fun u : ℂ => w (z₀ + u)) 0 :=
      (by simpa using hA.continuousAt : ContinuousAt w (z₀ + 0)).comp
        (continuous_const.add continuous_id).continuousAt
    exact continuousAt_const.mul this
  have hcG : ContinuousAt G 0 := by
    have c1 : ContinuousAt (fun u : ℂ => w (z₀ + u)) 0 :=
      (by simpa using hA.continuousAt : ContinuousAt w (z₀ + 0)).comp
        (continuous_const.add continuous_id).continuousAt
    have c2 : ContinuousAt (fun u : ℂ => deriv (deriv w) (z₀ + u)) 0 :=
      (by simpa using hA2.deriv.continuousAt : ContinuousAt (deriv (deriv w)) (z₀ + 0)).comp
        (continuous_const.add continuous_id).continuousAt
    exact (c2.add (continuousAt_const.mul c1)).mul (hsn.continuousAt.pow 2)
  have hev : F =ᶠ[𝓝[≠] 0] G := by
    have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), jacobiSnk u k ≠ 0 := by
      have := hsn.eventually_ne (c := 0) one_ne_zero
      simpa [jacobiSnk_zero hkD] using this
    have h2 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), z₀ + u ∈ U := by
      refine nhdsWithin_le_nhds ?_
      have : Tendsto (fun u : ℂ => z₀ + u) (𝓝 0) (𝓝 z₀) := by
        simpa using (tendsto_const_nhds (x := z₀)).add (tendsto_id (x := 𝓝 (0 : ℂ)))
      exact this (hU.mem_nhds hz₀)
    filter_upwards [h1, h2] with u hu hU'
    have hd := (hw.hasDerivAt_deriv _ hU').deriv
    have hp := hpole u
    have hs : (k : ℂ) ^ 2 * jacobiSnk u k ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hk) (pow_ne_zero _ hu)
    have hq : (k : ℂ) ^ 2 * jacobiSnk (z₀ + u) k ^ 2 * jacobiSnk u k ^ 2 = 1 := by
      rw [hp]; field_simp
    simp only [F, G]
    rw [hd]
    linear_combination (-(ν * (ν + 1) * w (z₀ + u))) * hq
  have t1 : Tendsto F (𝓝[≠] 0) (𝓝 (F 0)) := hcF.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto F (𝓝[≠] 0) (𝓝 (G 0)) :=
    (hcG.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  have := tendsto_nhds_unique t1 t2
  simpa [F, G, jacobiSnk_zero hkD] using this

/-- The Weierstrass half-periods `ω₁ = K/a`, `ω₃ = iK'/a` attached to a real modulus and a
scale `a > 0`. -/
def p3lHP (hk0 : 0 < k) (hk1 : k < 1) {a : ℝ} (ha : 0 < a) : Weierstrass.HalfPeriods where
  ω₁ := ((Real.compEllIntKm (k ^ 2) / a : ℝ) : ℂ)
  ω₃ := I * ((Real.compEllIntKm (1 - k ^ 2) / a : ℝ) : ℂ)
  ω₁_ne_zero := by
    have := Real.compEllIntKm_pos (show k ^ 2 < 1 by nlinarith)
    exact_mod_cast (div_pos this ha).ne'
  im_div_pos := by
    have h1 := Real.compEllIntKm_pos (show k ^ 2 < 1 by nlinarith)
    have h2 := Real.compEllIntKm_pos (show 1 - k ^ 2 < 1 by nlinarith)
    rw [show I * ((Real.compEllIntKm (1 - k ^ 2) / a : ℝ) : ℂ) /
        ((Real.compEllIntKm (k ^ 2) / a : ℝ) : ℂ) =
        I * (((Real.compEllIntKm (1 - k ^ 2) / a) / (Real.compEllIntKm (k ^ 2) / a) : ℝ) : ℂ) by
      push_cast; ring]
    simp only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add]
    positivity

/-- The lattice parameter of `p3lHP` is `τ = iK'/K`. -/
lemma p3lHP_tau (hk0 : 0 < k) (hk1 : k < 1) {a : ℝ} (ha : 0 < a) :
    (p3lHP hk0 hk1 ha).tau = jacobiTauk k := by
  have h1 := Real.compEllIntKm_pos (show k ^ 2 < 1 by nlinarith)
  have hK : compEllIntKk (k : ℂ) = Real.compEllIntKm (k ^ 2) := compEllIntKk_ofReal (by nlinarith)
  have hK' : compEllIntKpk (k : ℂ) = Real.compEllIntKm (1 - k ^ 2) :=
    compEllIntKpk_ofReal (by positivity)
  have h1' : (Real.compEllIntKm (k ^ 2) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [Weierstrass.HalfPeriods.tau, jacobiTauk, hK, hK']
  simp only [p3lHP]
  push_cast
  field_simp

/-- **Lamé's equation in Weierstrass form** (DLMF 29.2.6–29.2.9, 29.2.12): with `a = √(e₁-e₃)`,
`v(η) = w(aη + iK')` solves `v'' = -(g - ν(ν+1)℘(η; g₂, g₃)) v`. -/
theorem p3l_weierstrass {h ν : ℝ} (hk0 : 0 < k) (hk1 : k < 1)
    {e₁ e₂ e₃ : ℝ} (h12 : e₂ < e₁) (h23 : e₃ < e₂) (hsum : e₁ + e₂ + e₃ = 0)
    (hk2 : (e₂ - e₃) / (e₁ - e₃) = k ^ 2) {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hw : IsLameSolutionOn h ν k w U) :
    IsLameWeierstrassSolutionOn ((e₁ - e₃) * h + ν * (ν + 1) * e₃) ν
      (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂)) (4 * e₁ * e₂ * e₃)
      (fun η => w (Real.sqrt (e₁ - e₃) * η + I * Real.compEllIntKm (1 - k ^ 2)))
      {η | (Real.sqrt (e₁ - e₃) : ℂ) * η + I * Real.compEllIntKm (1 - k ^ 2) ∈ U} := by
  have hkD := p22R1_ofReal_mem hk0 hk1
  have h13 : 0 < e₁ - e₃ := by linarith
  set a : ℝ := Real.sqrt (e₁ - e₃)
  have ha : 0 < a := Real.sqrt_pos.2 h13
  have ha2 : (a : ℂ) ^ 2 = ((e₁ - e₃ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt h13.le]
  set K := Real.compEllIntKm (k ^ 2)
  set K' := Real.compEllIntKm (1 - k ^ 2)
  have hKpos : 0 < K := Real.compEllIntKm_pos (by nlinarith)
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hKpos.ne'
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set H := p3lHP hk0 hk1 ha
  have hτ := p3lHP_tau hk0 hk1 ha
  obtain ⟨hmodk, -, hKt⟩ := jacobi_inversion_k hkD
  have hKk : compEllIntKk (k : ℂ) = K := compEllIntKk_ofReal (by nlinarith)
  have hQ : H.quarterK = K := by
    rw [Weierstrass.HalfPeriods.quarterK, hτ, hKt, hKk]
  have hmod : H.modulus = k := by rw [Weierstrass.HalfPeriods.modulus, hτ, hmodk]
  have hω₁ : H.ω₁ = K / a := by show ((K / a : ℝ) : ℂ) = _; push_cast; rfl
  have hω₃ : H.ω₃ = I * (K' / a) := by show I * ((K' / a : ℝ) : ℂ) = _; push_cast; rfl
  -- the roots `e_j` of the lattice are the given ones
  have hd13 : H.e 1 - H.e 3 = ((e₁ - e₃ : ℝ) : ℂ) := by
    have := H.quarterK_sq_eq.1
    rw [hQ, hω₁] at this
    rw [← ha2]
    field_simp at this
    linear_combination -this
  have hd23 : H.e 2 - H.e 3 = ((e₂ - e₃ : ℝ) : ℂ) := by
    have := H.modulus_sq_eq.1
    rw [hmod, hd13] at this
    have hk2' : ((e₂ - e₃ : ℝ) : ℂ) = (k : ℂ) ^ 2 * ((e₁ - e₃ : ℝ) : ℂ) := by
      have hkc : (k : ℂ) ^ 2 = (((e₂ - e₃) / (e₁ - e₃) : ℝ) : ℂ) := by rw [hk2]; push_cast; ring
      have hne : ((e₁ - e₃ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h13.ne'
      rw [hkc]; push_cast at hne ⊢; field_simp
    have hne : ((e₁ - e₃ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h13.ne'
    rw [hk2', this]; field_simp
  have hs := H.e_sum
  have he3 : H.e 3 = e₃ := by
    push_cast at hd13 hd23
    have : (e₁ : ℂ) + e₂ + e₃ = 0 := by exact_mod_cast hsum
    linear_combination (hs - hd13 - hd23 - this) / 3
  have he1 : H.e 1 = e₁ := by push_cast at hd13; linear_combination hd13 + he3
  have he2 : H.e 2 = e₂ := by push_cast at hd23; linear_combination hd23 + he3
  have hg₂ : H.g₂ = -4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂) := by rw [H.g₂_eq_e.2, he1, he2, he3]
  have hg₃ : H.g₃ = 4 * e₁ * e₂ * e₃ := by rw [H.g₃_eq_e.1, he1, he2, he3]
  have hP : ∀ η, Weierstrass.weierstrassPInvariants (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂))
      (4 * e₁ * e₂ * e₃) η = H.weierstrassP η := fun η => by
    rw [← hg₂, ← hg₃]; exact Weierstrass.weierstrassPInvariants_eq H.periodPair η
  -- the key identity, or `ν(ν+1) w = 0` at the poles
  have key : ∀ η : ℂ, (a : ℂ) * η + I * K' ∈ U →
      (H.weierstrassP η - e₃ = (a : ℂ) ^ 2 * k ^ 2 * jacobiSnk ((a : ℂ) * η + I * K') k ^ 2) ∨
        (ν : ℂ) * (ν + 1) * w ((a : ℂ) * η + I * K') = 0 := by
    intro η hη
    by_cases hL : η ∈ H.lattice
    · right
      obtain ⟨m, n, rfl⟩ := H.mem_lattice_iff.1 hL
      refine p3l_pole_zero hk0 hk1 hU hw hη fun u => ?_
      have := p3l_sn_sq_pole hk0 hk1 m n u
      rw [hω₁, hω₃] at *
      rw [← this]
      congr 2
      field_simp
      ring
    · left
      have hz : η - H.ω₃ + H.ω₃ ∉ H.lattice := by simpa using hL
      have := H.weierstrassP_add_ω₃_sub_e_three_eq_sn hz
      rw [sub_add_cancel, he3, hQ, hmod, hτ, jacobiSnTau,
        ← jacobiPQk_eq_jacobiPQTau hkD, ← jacobiSnk] at this
      rw [this]
      have e1 : (K : ℂ) * (η - H.ω₃) / H.ω₁ = (a : ℂ) * η + I * K' + ((0 : ℤ) : ℂ) * (2 * (K : ℂ)) +
          ((-1 : ℤ) : ℂ) * (2 * (I * K')) := by
        rw [hω₁, hω₃]; field_simp; push_cast; ring
      rw [e1, p3l_sn_sq_lattice hk0 hk1 _ 0 (-1), hω₁]
      field_simp
  -- the equation
  have hγ : ∀ η : ℂ, HasDerivAt (fun η => (a : ℂ) * η + I * K') (a : ℂ) η := fun η => by
    simpa using ((hasDerivAt_id η).const_mul (a : ℂ)).add_const (I * (K' : ℂ))
  have hU' : IsOpen {η : ℂ | (a : ℂ) * η + I * K' ∈ U} :=
    hU.preimage (by fun_prop)
  refine ⟨fun η hη => ((hw.differentiableAt _ hη).hasDerivAt.comp η (hγ η)).differentiableAt,
    fun η hη => ?_⟩
  have hev : deriv (fun η => w ((a : ℂ) * η + I * K')) =ᶠ[𝓝 η]
      fun η => deriv w ((a : ℂ) * η + I * K') * a := by
    filter_upwards [hU'.mem_nhds hη] with ζ hζ
    exact ((hw.differentiableAt _ hζ).hasDerivAt.comp ζ (hγ ζ)).deriv
  have d2 := ((hw.hasDerivAt_deriv _ hη).comp η (hγ η)).mul_const (a : ℂ)
  refine (d2.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [hP]
  have ha2' : (a : ℂ) ^ 2 = (e₁ : ℂ) - e₃ := by rw [ha2]; push_cast; ring
  rcases key η hη with hk | hk
  · rw [show H.weierstrassP η = e₃ + (a : ℂ) ^ 2 * k ^ 2 *
      jacobiSnk ((a : ℂ) * η + I * K') k ^ 2 by linear_combination hk]
    linear_combination (-((h : ℂ) * w ((a : ℂ) * η + I * K'))) * ha2'
  · linear_combination (-((h : ℂ) * w ((a : ℂ) * η + I * K'))) * ha2' +
      ((a : ℂ) ^ 2 * k ^ 2 * jacobiSnk ((a : ℂ) * η + I * K') k ^ 2 + e₃ - H.weierstrassP η) * hk

end DLMF.Lame
