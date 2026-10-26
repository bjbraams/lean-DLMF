/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Defs

/-!
# Hamiltonian structure: DLMF §32.6

For each Hamiltonian of §32.6 we prove that the Hamiltonian system 32.6.1 is the explicit
first-order system printed by DLMF, that its first component solves the corresponding
Painlevé equation, and that the function `σ` built from the Hamiltonian solves the
second-order second-degree `σ`-equation. The converse statements (from `σ` back to `(q, p)`)
need a nondegeneracy hypothesis that DLMF omits (`σ'' ≠ 0` for `PI`; see the docstrings).

Corrections of the printed text (verified symbolically along the Hamiltonian flows):
* 32.6.26 prints `θ₁`; the Hamiltonian 32.6.24 gives `θ∞`.
* 32.6.30–32.6.31: from 32.6.24 and 32.6.28, `p = (2σ' + η₀η∞)/(2η₀)` (DLMF prints
  `η₀η∞ζ`) and `q = η₀(2ζσ'' - 2θ₀σ' + η₀η∞θ∞)/(η₀²η∞² - 4σ'²)` (DLMF prints `ζσ''`).
* 32.6.37: the term `-4κ₀κ∞(θ+1)θ∞zσ'` contains a stray `θ∞` (which does not occur in
  32.6.32); the correct term is `-4κ₀κ∞(θ+1)zσ'`.
* 32.6.38–32.6.39: from 32.6.32 and 32.6.36, `σ' = -2κ₀p`, so `p = -σ'/(2κ₀)` and
  `q = κ₀(zσ'' + θσ' + 2κ₀κ∞z)/σ'²` (DLMF prints `p = σ'/(2κ₀)` and `-θσ'`).
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace DLMF.Painleve

/-! ## Helpers -/

/-- A Hamiltonian system with explicitly known partial derivatives along the solution. -/
lemma a32_hamiltonian_iff {H : ℂ → ℂ → ℂ → ℂ} {q p : ℂ → ℂ} {U : Set ℂ} {Hp Hq : ℂ → ℂ}
    (hHp : ∀ z ∈ U, HasDerivAt (fun p' => H (q z) p' z) (Hp z) (p z))
    (hHq : ∀ z ∈ U, HasDerivAt (fun q' => H q' (p z) z) (Hq z) (q z)) :
    IsHamiltonianSystemOn H q p U ↔
      ∀ z ∈ U, HasDerivAt q (Hp z) z ∧ HasDerivAt p (-Hq z) z := by
  constructor
  · intro h z hz
    exact ⟨(hHp z hz).deriv ▸ h.hasDerivAt_q z hz, (hHq z hz).deriv ▸ h.hasDerivAt_p z hz⟩
  · intro h
    exact ⟨fun z hz => (hHp z hz).deriv ▸ (h z hz).1,
      fun z hz => (hHq z hz).deriv ▸ (h z hz).2⟩

/-- The second derivative of `f` from an explicit first derivative on an open set. -/
lemma a32_deriv_deriv {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ z ∈ U, HasDerivAt f (g z) z) {z g' : ℂ} (hz : z ∈ U) (hg : HasDerivAt g g' z) :
    deriv (deriv f) z = g' := by
  have he : deriv f =ᶠ[𝓝 z] g := by
    filter_upwards [hU.mem_nhds hz] with y hy using (hf y hy).deriv
  rw [he.deriv_eq, hg.deriv]

/-- A function vanishing on an open set has zero derivative there. -/
lemma a32_hasDerivAt_eq_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ z ∈ U, f z = 0) {z f' : ℂ} (hz : z ∈ U) (hd : HasDerivAt f f' z) : f' = 0 := by
  have he : f =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hz] with y hy using hf y hy
  exact hd.unique ((hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq he)

/-! ## `PI` (§32.6(ii)) -/

/-- DLMF 32.6.2–32.6.4: the Hamiltonian system of `H_I` is `q' = p`, `p' = 6q² + z`. -/
@[dlmf 32.6.E3, dlmf 32.6.E4]
theorem isHamiltonianSystemOn_painleveHamiltonianI_iff {q p : ℂ → ℂ} {U : Set ℂ} :
    IsHamiltonianSystemOn painleveHamiltonianI q p U ↔
      ∀ z ∈ U, HasDerivAt q (p z) z ∧ HasDerivAt p (6 * q z ^ 2 + z) z := by
  rw [a32_hamiltonian_iff (Hp := p) (Hq := fun z => -(6 * q z ^ 2 + z))]
  · simp only [neg_neg]
  · intro z _
    simpa [painleveHamiltonianI] using
      ((hasDerivAt_pow 2 (p z)).div_const 2).sub_const (2 * q z ^ 3 + z * q z) |>.congr_deriv
        (by ring)
  · intro z _
    have := (((hasDerivAt_pow 3 (q z)).const_mul 2).add ((hasDerivAt_id (q z)).const_mul z))
    refine (this.const_sub (p z ^ 2 / 2)).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp [painleveHamiltonianI]; try ring
    · simp; try ring

/-- DLMF §32.6(ii): along a solution of the Hamiltonian system of `H_I`, `q = w` solves
`PI`. -/
@[dlmf 32.6.ii]
theorem IsHamiltonianSystemOn.isPainleveIOn {q p : ℂ → ℂ} {U : Set ℂ}
    (h : IsHamiltonianSystemOn painleveHamiltonianI q p U) (hU : IsOpen U) :
    IsPainleveIOn q U := by
  rw [isHamiltonianSystemOn_painleveHamiltonianI_iff] at h
  exact isODE2SolutionOn_of_hasDerivAt hU (fun z hz => (h z hz).1)
    (fun z hz => (h z hz).2.congr_deriv (by simp [painleveIRhs]))

/-- DLMF 32.6.5–32.6.6: `σ = H_I(q, p, z)` along a solution of the Hamiltonian system
satisfies `(σ'')² + 4(σ')³ + 2zσ' - 2σ = 0` (with `σ' = -q`, `σ'' = -p`). -/
@[dlmf 32.6.E5, dlmf 32.6.E6]
theorem IsHamiltonianSystemOn.sigma_painleveI {q p : ℂ → ℂ} {U : Set ℂ}
    (h : IsHamiltonianSystemOn painleveHamiltonianI q p U) (hU : IsOpen U) {z : ℂ}
    (hz : z ∈ U) :
    let σ := fun z => painleveHamiltonianI (q z) (p z) z
    deriv (deriv σ) z ^ 2 + 4 * deriv σ z ^ 3 + 2 * z * deriv σ z - 2 * σ z = 0 := by
  intro σ
  rw [isHamiltonianSystemOn_painleveHamiltonianI_iff] at h
  have hσ (y : ℂ) (hy : y ∈ U) : HasDerivAt σ (-q y) y := by
    have hq := (h y hy).1
    have hp := (h y hy).2
    exact (((hp.pow 2).div_const 2).sub ((hq.pow 3).const_mul 2) |>.sub
      ((hasDerivAt_id y).mul hq)).congr_deriv (by simp; ring)
  rw [(hσ z hz).deriv, a32_deriv_deriv hU hσ hz (h z hz).1.neg]
  simp only [σ, painleveHamiltonianI]
  ring

/-- DLMF 32.6.7–32.6.8, converse: if `σ` (three times differentiable on the open set `U`)
solves `(σ'')² + 4(σ')³ + 2zσ' - 2σ = 0` and `σ'' ≠ 0` on `U`, then `q = -σ'`, `p = -σ''`
solve 32.6.3–32.6.4. The hypothesis `σ'' ≠ 0` is added: the linear solutions
`σ = 2c³ + cz` of the `σ`-equation give `p = 0`, which violates 32.6.4. -/
@[dlmf 32.6.E7, dlmf 32.6.E8]
theorem painleveI_of_sigma {σ σ₁ σ₂ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h₀ : ∀ z ∈ U, HasDerivAt σ (σ₁ z) z) (h₁ : ∀ z ∈ U, HasDerivAt σ₁ (σ₂ z) z)
    (h₂ : ∀ z ∈ U, DifferentiableAt ℂ σ₂ z)
    (hσ : ∀ z ∈ U, σ₂ z ^ 2 + 4 * σ₁ z ^ 3 + 2 * z * σ₁ z - 2 * σ z = 0)
    (hσ₂ : ∀ z ∈ U, σ₂ z ≠ 0) :
    ∀ z ∈ U, HasDerivAt (fun z => -σ₁ z) (-σ₂ z) z ∧
      HasDerivAt (fun z => -σ₂ z) (6 * (-σ₁ z) ^ 2 + z) z := by
  intro z hz
  refine ⟨(h₁ z hz).neg, ?_⟩
  have h3 := (h₂ z hz).hasDerivAt
  have hE := (((h3.pow 2).add (((h₁ z hz).pow 3).const_mul 4)).add
    (((hasDerivAt_id z).const_mul 2).mul (h₁ z hz))).sub ((h₀ z hz).const_mul 2)
  have h0 := a32_hasDerivAt_eq_zero hU (fun y hy => by simpa using hσ y hy) hz hE
  have hne := hσ₂ z hz
  have key : deriv σ₂ z = -6 * σ₁ z ^ 2 - z := by
    have : σ₂ z * (2 * deriv σ₂ z + 12 * σ₁ z ^ 2 + 2 * z) = 0 := by
      simp only [id] at h0; linear_combination h0
    have := (mul_eq_zero.mp this).resolve_left hne
    linear_combination this / 2
  exact h3.neg.congr_deriv (by rw [key]; ring)

/-! ## `PII` (§32.6(iii)) -/

/-- DLMF 32.6.9–32.6.11: the Hamiltonian system of `H_II` is `q' = p - q² - z/2`,
`p' = 2qp + α + 1/2`. -/
@[dlmf 32.6.E10, dlmf 32.6.E11]
theorem isHamiltonianSystemOn_painleveHamiltonianII_iff {α : ℂ} {q p : ℂ → ℂ} {U : Set ℂ} :
    IsHamiltonianSystemOn (painleveHamiltonianII α) q p U ↔
      ∀ z ∈ U, HasDerivAt q (p z - q z ^ 2 - z / 2) z ∧
        HasDerivAt p (2 * q z * p z + α + 1 / 2) z := by
  rw [a32_hamiltonian_iff (Hp := fun z => p z - q z ^ 2 - z / 2)
    (Hq := fun z => -(2 * q z * p z + α + 1 / 2))]
  · simp only [neg_neg]
  · intro z _
    have := (((hasDerivAt_pow 2 (p z)).div_const 2).sub
      ((hasDerivAt_id (p z)).const_mul (q z ^ 2 + z / 2))).sub_const ((α + 1 / 2) * q z)
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp [painleveHamiltonianII]
    · simp; try ring
  · intro z _
    have := ((((hasDerivAt_pow 2 (q z)).add_const (z / 2)).mul_const (p z)).add
      ((hasDerivAt_id (q z)).const_mul (α + 1 / 2))).const_sub (p z ^ 2 / 2)
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp [painleveHamiltonianII]; try ring
    · simp; try ring

/-- DLMF §32.6(iii): along a solution of the Hamiltonian system of `H_II`, `q = w` solves
`PII`. -/
@[dlmf 32.6.iii]
theorem IsHamiltonianSystemOn.isPainleveIIOn {α : ℂ} {q p : ℂ → ℂ} {U : Set ℂ}
    (h : IsHamiltonianSystemOn (painleveHamiltonianII α) q p U) (hU : IsOpen U) :
    IsPainleveIIOn α q U := by
  rw [isHamiltonianSystemOn_painleveHamiltonianII_iff] at h
  refine isODE2SolutionOn_of_hasDerivAt hU (fun z hz => (h z hz).1) (fun z hz => ?_)
  have hq := (h z hz).1
  have hp := (h z hz).2
  refine ((hp.sub (hq.pow 2)).sub ((hasDerivAt_id z).div_const 2)).congr_deriv ?_
  simp only [painleveIIRhs, id]
  ring

/-- DLMF 32.6.12: the momentum `p` of the `PII` Hamiltonian system satisfies
`pp'' = (p')²/2 + 2p³ - zp² - (α + 1/2)²/2`. -/
@[dlmf 32.6.E12]
theorem IsHamiltonianSystemOn.momentum_painleveII {α : ℂ} {q p : ℂ → ℂ} {U : Set ℂ}
    (h : IsHamiltonianSystemOn (painleveHamiltonianII α) q p U) (hU : IsOpen U) {z : ℂ}
    (hz : z ∈ U) :
    p z * deriv (deriv p) z =
      deriv p z ^ 2 / 2 + 2 * p z ^ 3 - z * p z ^ 2 - (α + 1 / 2) ^ 2 / 2 := by
  rw [isHamiltonianSystemOn_painleveHamiltonianII_iff] at h
  have hp2 : HasDerivAt (fun z => 2 * q z * p z + α + 1 / 2)
      (2 * (p z - q z ^ 2 - z / 2) * p z + 2 * q z * (2 * q z * p z + α + 1 / 2)) z :=
    ((((h z hz).1.const_mul 2).mul (h z hz).2).add_const α |>.add_const (1 / 2)).congr_deriv
      (by ring)
  rw [a32_deriv_deriv hU (fun y hy => (h y hy).2) hz hp2, (h z hz).2.deriv]
  ring

/-- DLMF 32.6.13: `σ(z) = H_II(q, p, z)` along a solution of the Hamiltonian system satisfies
`(σ'')² + 4(σ')³ + 2σ'(zσ' - σ) = (α + 1/2)²/4` (with `σ' = -p/2`). -/
@[dlmf 32.6.E13]
theorem IsHamiltonianSystemOn.sigma_painleveII {α : ℂ} {q p : ℂ → ℂ} {U : Set ℂ}
    (h : IsHamiltonianSystemOn (painleveHamiltonianII α) q p U) (hU : IsOpen U) {z : ℂ}
    (hz : z ∈ U) :
    let σ := fun z => painleveHamiltonianII α (q z) (p z) z
    deriv (deriv σ) z ^ 2 + 4 * deriv σ z ^ 3 + 2 * deriv σ z * (z * deriv σ z - σ z) =
      (α + 1 / 2) ^ 2 / 4 := by
  intro σ
  rw [isHamiltonianSystemOn_painleveHamiltonianII_iff] at h
  have hσ (y : ℂ) (hy : y ∈ U) : HasDerivAt σ (-p y / 2) y := by
    have hq := (h y hy).1
    have hp := (h y hy).2
    exact (((hp.pow 2).div_const 2).sub (((hq.pow 2).add ((hasDerivAt_id y).div_const 2)).mul
      hp) |>.sub (hq.const_mul (α + 1 / 2))).congr_deriv (by simp; ring)
  rw [(hσ z hz).deriv, a32_deriv_deriv hU hσ hz ((h z hz).2.neg.div_const 2)]
  simp only [σ, painleveHamiltonianII]
  ring

/-- DLMF 32.6.14–32.6.15, converse: if `σ` (three times differentiable on the open set `U`)
solves 32.6.13 with `σ' ≠ 0` and `σ'' ≠ 0` on `U`, then `q = (4σ'' + 2α + 1)/(8σ')`,
`p = -2σ'` solve 32.6.10–32.6.11. The hypothesis `σ'' ≠ 0` is added (it is used to
differentiate the `σ`-equation; DLMF states no condition). -/
@[dlmf 32.6.E14, dlmf 32.6.E15]
theorem painleveII_of_sigma {α : ℂ} {σ σ₁ σ₂ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h₀ : ∀ z ∈ U, HasDerivAt σ (σ₁ z) z) (h₁ : ∀ z ∈ U, HasDerivAt σ₁ (σ₂ z) z)
    (h₂ : ∀ z ∈ U, DifferentiableAt ℂ σ₂ z)
    (hσ : ∀ z ∈ U, σ₂ z ^ 2 + 4 * σ₁ z ^ 3 + 2 * σ₁ z * (z * σ₁ z - σ z) -
      (α + 1 / 2) ^ 2 / 4 = 0)
    (hσ₁ : ∀ z ∈ U, σ₁ z ≠ 0) (hσ₂ : ∀ z ∈ U, σ₂ z ≠ 0) :
    ∀ z ∈ U,
      HasDerivAt (fun z => (4 * σ₂ z + 2 * α + 1) / (8 * σ₁ z))
        (-2 * σ₁ z - ((4 * σ₂ z + 2 * α + 1) / (8 * σ₁ z)) ^ 2 - z / 2) z ∧
      HasDerivAt (fun z => -2 * σ₁ z)
        (2 * ((4 * σ₂ z + 2 * α + 1) / (8 * σ₁ z)) * (-2 * σ₁ z) + α + 1 / 2) z := by
  intro z hz
  have h3 := (h₂ z hz).hasDerivAt
  have hne1 := hσ₁ z hz
  have hne2 := hσ₂ z hz
  have hE := ((((h3.pow 2).add (((h₁ z hz).pow 3).const_mul 4)).add
    (((h₁ z hz).const_mul 2).mul (((hasDerivAt_id z).mul (h₁ z hz)).sub (h₀ z hz)))).sub_const
    ((α + 1 / 2) ^ 2 / 4))
  have h0 := a32_hasDerivAt_eq_zero hU (fun y hy => by simpa using hσ y hy) hz hE
  have key : deriv σ₂ z = -6 * σ₁ z ^ 2 - 2 * z * σ₁ z + σ z := by
    have : σ₂ z * (2 * deriv σ₂ z + 12 * σ₁ z ^ 2 + 4 * z * σ₁ z - 2 * σ z) = 0 := by
      simp only [Pi.mul_apply, Pi.sub_apply, id] at h0; linear_combination h0
    have := (mul_eq_zero.mp this).resolve_left hne2
    linear_combination this / 2
  refine ⟨?_, ?_⟩
  · refine ((((h3.const_mul 4).add_const (2 * α)).add_const 1).div ((h₁ z hz).const_mul 8)
      (mul_ne_zero (by norm_num) hne1)).congr_deriv ?_
    rw [key]
    have hs := hσ z hz
    field_simp
    linear_combination (-32 : ℂ) * hs
  · refine ((h₁ z hz).const_mul (-2)).congr_deriv ?_
    field_simp
    ring

/-! ## `PIII` (§32.6(iv)) -/

/-- DLMF 32.6.16–32.6.18: the Hamiltonian system of `H_III` is
`zq' = 2q²p - κ∞zq² - (2θ₀+1)q + κ₀z`,
`zp' = -2qp² + 2κ∞zqp + (2θ₀+1)p - κ∞(θ₀+θ∞)z`. -/
@[dlmf 32.6.E17, dlmf 32.6.E18]
theorem isHamiltonianSystemOn_painleveHamiltonianIII_iff {κ₀ κinf θ₀ θinf : ℂ}
    {q p : ℂ → ℂ} {U : Set ℂ} :
    IsHamiltonianSystemOn (painleveHamiltonianIII κ₀ κinf θ₀ θinf) q p U ↔
      ∀ z ∈ U, HasDerivAt q ((2 * q z ^ 2 * p z - κinf * z * q z ^ 2 - (2 * θ₀ + 1) * q z +
          κ₀ * z) / z) z ∧
        HasDerivAt p ((-2 * q z * p z ^ 2 + 2 * κinf * z * q z * p z + (2 * θ₀ + 1) * p z -
          κinf * (θ₀ + θinf) * z) / z) z := by
  rw [a32_hamiltonian_iff
    (Hp := fun z => (2 * q z ^ 2 * p z - κinf * z * q z ^ 2 - (2 * θ₀ + 1) * q z + κ₀ * z) / z)
    (Hq := fun z => -((-2 * q z * p z ^ 2 + 2 * κinf * z * q z * p z + (2 * θ₀ + 1) * p z -
      κinf * (θ₀ + θinf) * z) / z))]
  · simp only [neg_neg]
  · intro z _
    have := (((((hasDerivAt_pow 2 (p z)).const_mul (q z ^ 2)).sub
      ((hasDerivAt_id (p z)).const_mul (κinf * z * q z ^ 2 + (2 * θ₀ + 1) * q z - κ₀ * z))).add_const
      (κinf * (θ₀ + θinf) * z * q z)).div_const z)
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp [painleveHamiltonianIII]
    · simp; try ring
  · intro z _
    have := (((((hasDerivAt_pow 2 (q z)).mul_const (p z ^ 2)).sub
      (((((hasDerivAt_pow 2 (q z)).const_mul (κinf * z)).add
        ((hasDerivAt_id (q z)).const_mul (2 * θ₀ + 1))).sub_const (κ₀ * z)).mul_const (p z))).add
      ((hasDerivAt_id (q z)).const_mul (κinf * (θ₀ + θinf) * z))).div_const z)
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp [painleveHamiltonianIII]; try ring
    · simp; try ring

/-- DLMF 32.6.19: along a solution of the Hamiltonian system of `H_III` on an open set
avoiding `z = 0` and the zeros of `q`, `q = w` solves `PIII` with
`(α, β, γ, δ) = (-2κ∞θ∞, 2κ₀(θ₀+1), κ∞², -κ₀²)`. -/
@[dlmf 32.6.E19]
theorem IsHamiltonianSystemOn.isPainleveIIIOn {κ₀ κinf θ₀ θinf : ℂ} {q p : ℂ → ℂ} {U : Set ℂ}
    (h : IsHamiltonianSystemOn (painleveHamiltonianIII κ₀ κinf θ₀ θinf) q p U) (hU : IsOpen U)
    (hz : ∀ z ∈ U, z ≠ 0) (hq : ∀ z ∈ U, q z ≠ 0) :
    IsPainleveIIIOn (-2 * κinf * θinf) (2 * κ₀ * (θ₀ + 1)) (κinf ^ 2) (-κ₀ ^ 2) q U := by
  rw [isHamiltonianSystemOn_painleveHamiltonianIII_iff] at h
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (fun z hz => (h z hz).1) (fun z hz' => ?_), hz, hq⟩
  have hq' := (h z hz').1
  have hp' := (h z hz').2
  have hid := hasDerivAt_id z
  have hz0 := hz z hz'
  have hq0 := hq z hz'
  have hd := (((((hq'.pow 2).mul hp').const_mul 2).sub ((hid.mul (hq'.pow 2)).const_mul κinf)).sub
    (hq'.const_mul (2 * θ₀ + 1)) |>.add (hid.const_mul κ₀)).div hid hz0
  convert hd using 1
  · funext x
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    try ring
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    simp only [painleveIIIRhs]
    field_simp
    ring

/-- DLMF 32.6.20–32.6.21: `σ = zH_III + pq + θ₀² - κ₀κ∞z²/2` along a solution of the
Hamiltonian system (on an open set avoiding `z = 0`) satisfies
`(zσ'' - σ')² + 2((σ')² - κ₀²κ∞²z²)(zσ' - 2σ) + 8κ₀κ∞θ₀θ∞zσ' = 4κ₀²κ∞²(θ₀² + θ∞²)z²`. -/
@[dlmf 32.6.E20, dlmf 32.6.E21]
theorem IsHamiltonianSystemOn.sigma_painleveIII {κ₀ κinf θ₀ θinf : ℂ} {q p : ℂ → ℂ}
    {U : Set ℂ} (h : IsHamiltonianSystemOn (painleveHamiltonianIII κ₀ κinf θ₀ θinf) q p U)
    (hU : IsOpen U) (hz : ∀ z ∈ U, z ≠ 0) {z : ℂ} (hzU : z ∈ U) :
    let σ := fun z => z * painleveHamiltonianIII κ₀ κinf θ₀ θinf (q z) (p z) z + p z * q z +
      θ₀ ^ 2 - κ₀ * κinf * z ^ 2 / 2
    (z * deriv (deriv σ) z - deriv σ z) ^ 2 +
        2 * (deriv σ z ^ 2 - κ₀ ^ 2 * κinf ^ 2 * z ^ 2) * (z * deriv σ z - 2 * σ z) +
        8 * κ₀ * κinf * θ₀ * θinf * z * deriv σ z =
      4 * κ₀ ^ 2 * κinf ^ 2 * (θ₀ ^ 2 + θinf ^ 2) * z ^ 2 := by
  intro σ
  rw [isHamiltonianSystemOn_painleveHamiltonianIII_iff] at h
  have hσ (y : ℂ) (hy : y ∈ U) : HasDerivAt σ (2 * κ₀ * p y - κ₀ * κinf * y) y := by
    have hq' := (h y hy).1
    have hp' := (h y hy).2
    have hid := hasDerivAt_id y
    have hy0 := hz y hy
    have hX := (hq'.pow 2).mul (hp'.pow 2)
    have hY := ((((hid.mul (hq'.pow 2)).const_mul κinf).add (hq'.const_mul (2 * θ₀ + 1))).sub
      (hid.const_mul κ₀)).mul hp'
    have hZ := (hid.mul hq').const_mul (κinf * (θ₀ + θinf))
    have hP := ((hX.sub hY).add hZ).div hid hy0
    have hd := (((hid.mul hP).add (hp'.mul hq')).add_const (θ₀ ^ 2)).sub
      ((hid.pow 2).const_mul (κ₀ * κinf / 2))
    convert hd using 1
    · funext x
      simp only [σ, painleveHamiltonianIII, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
        Pi.pow_apply, Pi.div_apply, id]
      ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      field_simp
      ring
  have hσ2 : HasDerivAt (fun y => 2 * κ₀ * p y - κ₀ * κinf * y)
      (2 * κ₀ * ((-2 * q z * p z ^ 2 + 2 * κinf * z * q z * p z + (2 * θ₀ + 1) * p z -
        κinf * (θ₀ + θinf) * z) / z) - κ₀ * κinf) z := by
    simpa using ((h z hzU).2.const_mul (2 * κ₀)).sub ((hasDerivAt_id z).const_mul (κ₀ * κinf))
  rw [(hσ z hzU).deriv, a32_deriv_deriv hU hσ hzU hσ2]
  have hz0 := hz z hzU
  simp only [σ, painleveHamiltonianIII]
  field_simp
  ring

/-- DLMF 32.6.22–32.6.23, converse: if `σ` solves 32.6.21 on the open set `U` (three times
differentiable), then `q = κ₀(zσ'' - (2θ₀+1)σ' + 2κ₀κ∞θ∞z)/(κ₀²κ∞²z² - (σ')²)` and
`p = (σ' + κ₀κ∞z)/(2κ₀)` solve 32.6.17–32.6.18. Nondegeneracy hypotheses added (DLMF states
none): `κ₀ ≠ 0`, `z ≠ 0`, the denominator of `q` and `zσ'' - σ'` do not vanish on `U` (the
latter is needed to differentiate the `σ`-equation). -/
@[dlmf 32.6.E22, dlmf 32.6.E23]
theorem painleveIII_of_sigma {κ₀ κinf θ₀ θinf : ℂ} {σ σ₁ σ₂ : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hκ : κ₀ ≠ 0) (hz : ∀ z ∈ U, z ≠ 0)
    (h₀ : ∀ z ∈ U, HasDerivAt σ (σ₁ z) z) (h₁ : ∀ z ∈ U, HasDerivAt σ₁ (σ₂ z) z)
    (h₂ : ∀ z ∈ U, DifferentiableAt ℂ σ₂ z)
    (hσ : ∀ z ∈ U, (z * σ₂ z - σ₁ z) ^ 2 +
        2 * (σ₁ z ^ 2 - κ₀ ^ 2 * κinf ^ 2 * z ^ 2) * (z * σ₁ z - 2 * σ z) +
        8 * κ₀ * κinf * θ₀ * θinf * z * σ₁ z =
      4 * κ₀ ^ 2 * κinf ^ 2 * (θ₀ ^ 2 + θinf ^ 2) * z ^ 2)
    (hden : ∀ z ∈ U, κ₀ ^ 2 * κinf ^ 2 * z ^ 2 - σ₁ z ^ 2 ≠ 0)
    (hnd : ∀ z ∈ U, z * σ₂ z - σ₁ z ≠ 0) :
    let q := fun z => κ₀ * (z * σ₂ z - (2 * θ₀ + 1) * σ₁ z + 2 * κ₀ * κinf * θinf * z) /
      (κ₀ ^ 2 * κinf ^ 2 * z ^ 2 - σ₁ z ^ 2)
    let p := fun z => (σ₁ z + κ₀ * κinf * z) / (2 * κ₀)
    ∀ z ∈ U, HasDerivAt q ((2 * q z ^ 2 * p z - κinf * z * q z ^ 2 - (2 * θ₀ + 1) * q z +
          κ₀ * z) / z) z ∧
        HasDerivAt p ((-2 * q z * p z ^ 2 + 2 * κinf * z * q z * p z + (2 * θ₀ + 1) * p z -
          κinf * (θ₀ + θinf) * z) / z) z := by
  sorry

/-! ### `P'III` -/

/-- DLMF 32.6.24–32.6.26, as corrected: the Hamiltonian system of the `P'III` Hamiltonian is
`ζq' = 2q²p - η∞q² - θ₀q + η₀ζ` (32.6.25) and
`ζp' = -2qp² + 2η∞qp + θ₀p - η∞(θ₀ + θ∞)/2`; DLMF's 32.6.26 prints `θ₁` in place of `θ∞`
(the derivative of 32.6.24 gives `θ∞`). -/
@[dlmf 32.6.E25, dlmf 32.6.E26]
theorem isHamiltonianSystemOn_painleveHamiltonianIIIPrime_iff {η₀ ηinf θ₀ θinf : ℂ}
    {q p : ℂ → ℂ} {U : Set ℂ} :
    IsHamiltonianSystemOn (painleveHamiltonianIIIPrime η₀ ηinf θ₀ θinf) q p U ↔
      ∀ z ∈ U, HasDerivAt q ((2 * q z ^ 2 * p z - ηinf * q z ^ 2 - θ₀ * q z + η₀ * z) / z) z ∧
        HasDerivAt p ((-2 * q z * p z ^ 2 + 2 * ηinf * q z * p z + θ₀ * p z -
          ηinf * (θ₀ + θinf) / 2) / z) z := by
  rw [a32_hamiltonian_iff
    (Hp := fun z => (2 * q z ^ 2 * p z - ηinf * q z ^ 2 - θ₀ * q z + η₀ * z) / z)
    (Hq := fun z => -((-2 * q z * p z ^ 2 + 2 * ηinf * q z * p z + θ₀ * p z -
      ηinf * (θ₀ + θinf) / 2) / z))]
  · simp only [neg_neg]
  · intro z _
    have := (((((hasDerivAt_pow 2 (p z)).const_mul (q z ^ 2)).sub
      ((hasDerivAt_id (p z)).const_mul (ηinf * q z ^ 2 + θ₀ * q z - η₀ * z))).add_const
      (ηinf * (θ₀ + θinf) * q z / 2)).div_const z)
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp [painleveHamiltonianIIIPrime]
    · simp; try ring
  · intro z _
    have := (((((hasDerivAt_pow 2 (q z)).mul_const (p z ^ 2)).sub
      (((((hasDerivAt_pow 2 (q z)).const_mul ηinf).add
        ((hasDerivAt_id (q z)).const_mul θ₀)).sub_const (η₀ * z)).mul_const (p z))).add
      (((hasDerivAt_id (q z)).const_mul (ηinf * (θ₀ + θinf))).div_const 2)).div_const z)
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp [painleveHamiltonianIIIPrime]; try ring
    · simp; try ring

/-- DLMF 32.6.27: along a solution of the `P'III` Hamiltonian system (on an open set
avoiding `ζ = 0` and the zeros of `q`), `q = u` solves `P'III` with
`(α, β, γ, δ) = (-4η∞θ∞, 4η₀(θ₀+1), 4η∞², -4η₀²)`. -/
@[dlmf 32.6.E27]
theorem IsHamiltonianSystemOn.isPainleveIIIPrimeOn {η₀ ηinf θ₀ θinf : ℂ} {q p : ℂ → ℂ}
    {U : Set ℂ} (h : IsHamiltonianSystemOn (painleveHamiltonianIIIPrime η₀ ηinf θ₀ θinf) q p U)
    (hU : IsOpen U) (hz : ∀ z ∈ U, z ≠ 0) (hq : ∀ z ∈ U, q z ≠ 0) :
    IsPainleveIIIPrimeOn (-4 * ηinf * θinf) (4 * η₀ * (θ₀ + 1)) (4 * ηinf ^ 2) (-4 * η₀ ^ 2)
      q U := by
  rw [isHamiltonianSystemOn_painleveHamiltonianIIIPrime_iff] at h
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (fun z hz => (h z hz).1) (fun z hz' => ?_), hz, hq⟩
  have hq' := (h z hz').1
  have hp' := (h z hz').2
  have hid := hasDerivAt_id z
  have hz0 := hz z hz'
  have hq0 := hq z hz'
  have hd := (((((hq'.pow 2).mul hp').const_mul 2).sub ((hq'.pow 2).const_mul ηinf)).sub
    (hq'.const_mul θ₀) |>.add (hid.const_mul η₀)).div hid hz0
  convert hd using 1
  · funext x
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    try ring
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    simp only [painleveIIIPrimeRhs]
    field_simp
    ring

/-- DLMF 32.6.28–32.6.29: `σ = ζH + θ₀²/4 - η₀η∞ζ/2` along a solution of the `P'III`
Hamiltonian system (on an open set avoiding `ζ = 0`) satisfies
`ζ²(σ'')² + (4(σ')² - η₀²η∞²)(ζσ' - σ) + η₀η∞θ₀θ∞σ' = η₀²η∞²(θ₀² + θ∞²)/4`. -/
@[dlmf 32.6.E28, dlmf 32.6.E29]
theorem IsHamiltonianSystemOn.sigma_painleveIIIPrime {η₀ ηinf θ₀ θinf : ℂ} {q p : ℂ → ℂ}
    {U : Set ℂ} (h : IsHamiltonianSystemOn (painleveHamiltonianIIIPrime η₀ ηinf θ₀ θinf) q p U)
    (hU : IsOpen U) (hz : ∀ z ∈ U, z ≠ 0) {z : ℂ} (hzU : z ∈ U) :
    let σ := fun z => z * painleveHamiltonianIIIPrime η₀ ηinf θ₀ θinf (q z) (p z) z +
      θ₀ ^ 2 / 4 - η₀ * ηinf * z / 2
    z ^ 2 * deriv (deriv σ) z ^ 2 + (4 * deriv σ z ^ 2 - η₀ ^ 2 * ηinf ^ 2) *
        (z * deriv σ z - σ z) + η₀ * ηinf * θ₀ * θinf * deriv σ z =
      η₀ ^ 2 * ηinf ^ 2 * (θ₀ ^ 2 + θinf ^ 2) / 4 := by
  intro σ
  rw [isHamiltonianSystemOn_painleveHamiltonianIIIPrime_iff] at h
  have hσ (y : ℂ) (hy : y ∈ U) : HasDerivAt σ (η₀ * p y - η₀ * ηinf / 2) y := by
    have hq' := (h y hy).1
    have hp' := (h y hy).2
    have hid := hasDerivAt_id y
    have hy0 := hz y hy
    have hX := (hq'.pow 2).mul (hp'.pow 2)
    have hY := ((((hq'.pow 2).const_mul ηinf).add (hq'.const_mul θ₀)).sub
      (hid.const_mul η₀)).mul hp'
    have hZ := (hq'.const_mul (ηinf * (θ₀ + θinf))).div_const 2
    have hP := ((hX.sub hY).add hZ).div hid hy0
    have hd := (((hid.mul hP).add_const (θ₀ ^ 2 / 4)).sub ((hid.const_mul (η₀ * ηinf)).div_const 2))
    convert hd using 1
    · funext x
      simp only [σ, painleveHamiltonianIIIPrime, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
        Pi.pow_apply, Pi.div_apply, id]
      ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      field_simp
      ring
  have hσ2 : HasDerivAt (fun y => η₀ * p y - η₀ * ηinf / 2)
      (η₀ * ((-2 * q z * p z ^ 2 + 2 * ηinf * q z * p z + θ₀ * p z -
        ηinf * (θ₀ + θinf) / 2) / z)) z := by
    simpa using ((h z hzU).2.const_mul η₀).sub_const (η₀ * ηinf / 2)
  rw [(hσ z hzU).deriv, a32_deriv_deriv hU hσ hzU hσ2]
  have hz0 := hz z hzU
  simp only [σ, painleveHamiltonianIIIPrime]
  field_simp
  ring

/-- DLMF 32.6.30–32.6.31, converse, **as corrected**: if `σ` solves 32.6.29 then
`q = η₀(2ζσ'' - 2θ₀σ' + η₀η∞θ∞)/(η₀²η∞² - 4(σ')²)` and `p = (2σ' + η₀η∞)/(2η₀)` solve the
system 32.6.25–32.6.26. DLMF prints `ζσ''` in place of `2ζσ''` and `η₀η∞ζ` in place of
`η₀η∞`; the printed formulas do not recover `(q, p)` from 32.6.28 (symbolic check).
Nondegeneracy hypotheses added: `η₀ ≠ 0`, `ζ ≠ 0`, nonvanishing denominator and `σ'' ≠ 0`
on `U` (to differentiate the `σ`-equation). -/
@[dlmf 32.6.E30, dlmf 32.6.E31]
theorem painleveIIIPrime_of_sigma {η₀ ηinf θ₀ θinf : ℂ} {σ σ₁ σ₂ : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hη : η₀ ≠ 0) (hz : ∀ z ∈ U, z ≠ 0)
    (h₀ : ∀ z ∈ U, HasDerivAt σ (σ₁ z) z) (h₁ : ∀ z ∈ U, HasDerivAt σ₁ (σ₂ z) z)
    (h₂ : ∀ z ∈ U, DifferentiableAt ℂ σ₂ z)
    (hσ : ∀ z ∈ U, z ^ 2 * σ₂ z ^ 2 + (4 * σ₁ z ^ 2 - η₀ ^ 2 * ηinf ^ 2) * (z * σ₁ z - σ z) +
        η₀ * ηinf * θ₀ * θinf * σ₁ z = η₀ ^ 2 * ηinf ^ 2 * (θ₀ ^ 2 + θinf ^ 2) / 4)
    (hden : ∀ z ∈ U, η₀ ^ 2 * ηinf ^ 2 - 4 * σ₁ z ^ 2 ≠ 0) (hnd : ∀ z ∈ U, σ₂ z ≠ 0) :
    let q := fun z => η₀ * (2 * z * σ₂ z - 2 * θ₀ * σ₁ z + η₀ * ηinf * θinf) /
      (η₀ ^ 2 * ηinf ^ 2 - 4 * σ₁ z ^ 2)
    let p := fun z => (2 * σ₁ z + η₀ * ηinf) / (2 * η₀)
    ∀ z ∈ U, HasDerivAt q ((2 * q z ^ 2 * p z - ηinf * q z ^ 2 - θ₀ * q z + η₀ * z) / z) z ∧
        HasDerivAt p ((-2 * q z * p z ^ 2 + 2 * ηinf * q z * p z + θ₀ * p z -
          ηinf * (θ₀ + θinf) / 2) / z) z := by
  sorry

/-! ### `PIII` with `γ = 0` -/

/-- DLMF 32.6.32–32.6.34: the Hamiltonian system of the `PIII` Hamiltonian with `γ = 0` is
`zq' = 2q²p + θq - κ₀z`, `zp' = -2qp² - θp + κ∞z`. -/
@[dlmf 32.6.E33, dlmf 32.6.E34]
theorem isHamiltonianSystemOn_painleveHamiltonianIIIGammaZero_iff {κ₀ κinf θ : ℂ}
    {q p : ℂ → ℂ} {U : Set ℂ} :
    IsHamiltonianSystemOn (painleveHamiltonianIIIGammaZero κ₀ κinf θ) q p U ↔
      ∀ z ∈ U, HasDerivAt q ((2 * q z ^ 2 * p z + θ * q z - κ₀ * z) / z) z ∧
        HasDerivAt p ((-2 * q z * p z ^ 2 - θ * p z + κinf * z) / z) z := by
  rw [a32_hamiltonian_iff (Hp := fun z => (2 * q z ^ 2 * p z + θ * q z - κ₀ * z) / z)
    (Hq := fun z => -((-2 * q z * p z ^ 2 - θ * p z + κinf * z) / z))]
  · simp only [neg_neg]
  · intro z _
    have := (((((hasDerivAt_pow 2 (p z)).const_mul (q z ^ 2)).add
      ((hasDerivAt_id (p z)).const_mul (θ * q z - κ₀ * z))).sub_const
      (κinf * z * q z)).div_const z)
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp [painleveHamiltonianIIIGammaZero]
    · simp; try ring
  · intro z _
    have := (((((hasDerivAt_pow 2 (q z)).mul_const (p z ^ 2)).add
      ((((hasDerivAt_id (q z)).const_mul θ).sub_const (κ₀ * z)).mul_const (p z))).sub
      ((hasDerivAt_id (q z)).const_mul (κinf * z))).div_const z)
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp [painleveHamiltonianIIIGammaZero]; try ring
    · simp; try ring

/-- DLMF 32.6.35: along a solution of the Hamiltonian system with `γ = 0` (on an open set
avoiding `z = 0` and the zeros of `q`), `q = w` solves `PIII` with
`(α, β, γ, δ) = (2κ∞, κ₀(θ - 1), 0, -κ₀²)`. -/
@[dlmf 32.6.E35]
theorem IsHamiltonianSystemOn.isPainleveIIIOn_gammaZero {κ₀ κinf θ : ℂ} {q p : ℂ → ℂ}
    {U : Set ℂ} (h : IsHamiltonianSystemOn (painleveHamiltonianIIIGammaZero κ₀ κinf θ) q p U)
    (hU : IsOpen U) (hz : ∀ z ∈ U, z ≠ 0) (hq : ∀ z ∈ U, q z ≠ 0) :
    IsPainleveIIIOn (2 * κinf) (κ₀ * (θ - 1)) 0 (-κ₀ ^ 2) q U := by
  rw [isHamiltonianSystemOn_painleveHamiltonianIIIGammaZero_iff] at h
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU (fun z hz => (h z hz).1) (fun z hz' => ?_), hz, hq⟩
  have hq' := (h z hz').1
  have hp' := (h z hz').2
  have hid := hasDerivAt_id z
  have hz0 := hz z hz'
  have hq0 := hq z hz'
  have hd := (((((hq'.pow 2).mul hp').const_mul 2).add (hq'.const_mul θ)).sub
    (hid.const_mul κ₀)).div hid hz0
  convert hd using 1
  · funext x
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    try ring
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    simp only [painleveIIIRhs]
    field_simp
    ring

/-- DLMF 32.6.36–32.6.37, **as corrected**: `σ = zH + pq + (θ+1)²/4` along a solution of the
Hamiltonian system with `γ = 0` (on an open set avoiding `z = 0`) satisfies
`(zσ'' - σ')² + 2(σ')²(zσ' - 2σ) - 4κ₀κ∞(θ+1)zσ' = 4κ₀²κ∞²z²`. DLMF's 32.6.37 has an extra
factor `θ∞` in the third term (a symbol that does not occur in 32.6.32); as printed the
equation fails unless `θ∞ = 1`. -/
@[dlmf 32.6.E36, dlmf 32.6.E37]
theorem IsHamiltonianSystemOn.sigma_painleveIII_gammaZero {κ₀ κinf θ : ℂ} {q p : ℂ → ℂ}
    {U : Set ℂ} (h : IsHamiltonianSystemOn (painleveHamiltonianIIIGammaZero κ₀ κinf θ) q p U)
    (hU : IsOpen U) (hz : ∀ z ∈ U, z ≠ 0) {z : ℂ} (hzU : z ∈ U) :
    let σ := fun z => z * painleveHamiltonianIIIGammaZero κ₀ κinf θ (q z) (p z) z +
      p z * q z + (θ + 1) ^ 2 / 4
    (z * deriv (deriv σ) z - deriv σ z) ^ 2 + 2 * deriv σ z ^ 2 * (z * deriv σ z - 2 * σ z) -
        4 * κ₀ * κinf * (θ + 1) * z * deriv σ z =
      4 * κ₀ ^ 2 * κinf ^ 2 * z ^ 2 := by
  intro σ
  rw [isHamiltonianSystemOn_painleveHamiltonianIIIGammaZero_iff] at h
  have hσ (y : ℂ) (hy : y ∈ U) : HasDerivAt σ (-2 * κ₀ * p y) y := by
    have hq' := (h y hy).1
    have hp' := (h y hy).2
    have hid := hasDerivAt_id y
    have hy0 := hz y hy
    have hP := ((((hq'.pow 2).mul (hp'.pow 2)).add (((hq'.const_mul θ).sub
      (hid.const_mul κ₀)).mul hp')).sub ((hid.mul hq').const_mul κinf)).div hid hy0
    have hd := ((hid.mul hP).add (hp'.mul hq')).add_const ((θ + 1) ^ 2 / 4)
    convert hd using 1
    · funext x
      simp only [σ, painleveHamiltonianIIIGammaZero, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
        Pi.pow_apply, Pi.div_apply, id]
      ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      field_simp
      ring
  have hσ2 : HasDerivAt (fun y => -2 * κ₀ * p y)
      (-2 * κ₀ * ((-2 * q z * p z ^ 2 - θ * p z + κinf * z) / z)) z :=
    (h z hzU).2.const_mul (-2 * κ₀)
  rw [(hσ z hzU).deriv, a32_deriv_deriv hU hσ hzU hσ2]
  have hz0 := hz z hzU
  simp only [σ, painleveHamiltonianIIIGammaZero]
  field_simp
  ring

/-- DLMF 32.6.38–32.6.39, converse, **as corrected**: if `σ` solves the corrected
32.6.37, then `q = κ₀(zσ'' + θσ' + 2κ₀κ∞z)/(σ')²` and `p = -σ'/(2κ₀)` solve 32.6.33–32.6.34.
DLMF prints `-θσ'` and `p = σ'/(2κ₀)`; along the flow of 32.6.32, `σ' = -2κ₀p` (symbolic
check). Nondegeneracy hypotheses added: `κ₀ ≠ 0`, `z ≠ 0`, `σ' ≠ 0`, `zσ'' - σ' ≠ 0`. -/
@[dlmf 32.6.E38, dlmf 32.6.E39]
theorem painleveIIIGammaZero_of_sigma {κ₀ κinf θ : ℂ} {σ σ₁ σ₂ : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hκ : κ₀ ≠ 0) (hz : ∀ z ∈ U, z ≠ 0)
    (h₀ : ∀ z ∈ U, HasDerivAt σ (σ₁ z) z) (h₁ : ∀ z ∈ U, HasDerivAt σ₁ (σ₂ z) z)
    (h₂ : ∀ z ∈ U, DifferentiableAt ℂ σ₂ z)
    (hσ : ∀ z ∈ U, (z * σ₂ z - σ₁ z) ^ 2 + 2 * σ₁ z ^ 2 * (z * σ₁ z - 2 * σ z) -
        4 * κ₀ * κinf * (θ + 1) * z * σ₁ z = 4 * κ₀ ^ 2 * κinf ^ 2 * z ^ 2)
    (hσ₁ : ∀ z ∈ U, σ₁ z ≠ 0) (hnd : ∀ z ∈ U, z * σ₂ z - σ₁ z ≠ 0) :
    let q := fun z => κ₀ * (z * σ₂ z + θ * σ₁ z + 2 * κ₀ * κinf * z) / σ₁ z ^ 2
    let p := fun z => -σ₁ z / (2 * κ₀)
    ∀ z ∈ U, HasDerivAt q ((2 * q z ^ 2 * p z + θ * q z - κ₀ * z) / z) z ∧
        HasDerivAt p ((-2 * q z * p z ^ 2 - θ * p z + κinf * z) / z) z := by
  sorry

end DLMF.Painleve
