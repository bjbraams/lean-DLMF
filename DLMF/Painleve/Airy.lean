/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Backlund
public import DLMF.Airy.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Airy solutions of Painlevé II at half-integral parameters

Beals–Wong Proposition 15.4.6 starts from the Riccati reduction at `c = 1/2`.
The Airy scale must satisfy `k³ = -1/2`. The printed scale `i 2^(-1/2)` on
page 407 does not satisfy that identity; it is corrected here. Logarithmic
quotients are asserted only where their Airy denominator is nonzero.
-/

@[expose] public noncomputable section

open Set Filter Complex
open scoped Topology
open DLMF.Airy

namespace DLMF.Painleve

/-- The Riccati reduction `u' = -u² - x/2` gives `PII(1/2)`. -/
theorem isPIIOn_of_riccati {𝕜 : Type*} [RCLike 𝕜] {u : 𝕜 → 𝕜} {s : Set 𝕜}
    (hs : IsOpen s) (hu : ∀ x ∈ s, HasDerivAt u (-u x ^ 2 - x / 2) x) :
    IsPIIOn (1 / 2) u s := by
  apply isPIIOn_of_hasDerivAt hs hu
  intro x hx
  exact (((hu x hx).pow 2).neg.sub ((hasDerivAt_id x).div_const 2)).congr_deriv
    (by ring)

/-- A linear combination of scaled Airy functions used to construct a Painlevé seed. -/
def airySeed (k a b : ℂ) (z : ℂ) : ℂ := a * airyAi (k * z) + b * airyBi (k * z)

/-- The explicit derivative of the scaled Airy seed. -/
def airySeedDeriv (k a b : ℂ) (z : ℂ) : ℂ :=
  a * k * airyAiDeriv (k * z) + b * k * airyBiDeriv (k * z)

/-- Differentiation of the Airy seed. -/
theorem hasDerivAt_airySeed (k a b z : ℂ) :
    HasDerivAt (airySeed k a b) (airySeedDeriv k a b z) z := by
  have hk : HasDerivAt (fun z : ℂ => k * z) k z := by simpa using (hasDerivAt_id z).const_mul k
  exact (((hasDerivAt_airyAi (k * z)).comp z hk).const_mul a |>.add
    (((hasDerivAt_airyBi (k * z)).comp z hk).const_mul b)).congr_deriv (by
      dsimp only [airySeedDeriv]; ring)

/-- The correctly scaled Airy seed solves `φ'' = -(z/2)φ`. -/
theorem hasDerivAt_airySeedDeriv {k : ℂ} (hk : k ^ 3 = -1 / 2) (a b z : ℂ) :
    HasDerivAt (airySeedDeriv k a b) (-(z / 2) * airySeed k a b z) z := by
  have hd : HasDerivAt (fun z : ℂ => k * z) k z := by simpa using (hasDerivAt_id z).const_mul k
  refine ((((hasDerivAt_airyAiDeriv (k * z)).comp z hd).const_mul (a * k)).add
    (((hasDerivAt_airyBiDeriv (k * z)).comp z hd).const_mul (b * k))).congr_deriv ?_
  dsimp only [airySeed]
  linear_combination (z * (a * airyAi (k * z) + b * airyBi (k * z))) * hk

/-- The Airy logarithmic derivative which solves `PII(1/2)`. -/
def airyPII (k a b : ℂ) (z : ℂ) : ℂ := airySeedDeriv k a b z / airySeed k a b z

/-- The Airy logarithmic derivative satisfies the Riccati equation off its poles. -/
theorem hasDerivAt_airyPII {k : ℂ} (hk : k ^ 3 = -1 / 2) (a b : ℂ) {z : ℂ}
    (hz : airySeed k a b z ≠ 0) :
    HasDerivAt (airyPII k a b) (-airyPII k a b z ^ 2 - z / 2) z := by
  refine ((hasDerivAt_airySeedDeriv hk a b z).div (hasDerivAt_airySeed k a b z) hz).congr_deriv ?_
  dsimp only [airyPII]
  field_simp
  ring

/-- An Airy-based solution of `PII(1/2)` on its full regular set, with the corrected
cube-root scale. Negation supplies `PII(-1/2)`. -/
theorem isPIIOn_airyPII {k : ℂ} (hk : k ^ 3 = -1 / 2) (a b : ℂ) :
    IsPIIOn (1 / 2) (airyPII k a b) {z | airySeed k a b z ≠ 0} := by
  have hc : Continuous (airySeed k a b) :=
    continuous_iff_continuousAt.mpr fun z => (hasDerivAt_airySeed k a b z).continuousAt
  exact isPIIOn_of_riccati (isOpen_ne_fun hc continuous_const)
    (fun _ hz => hasDerivAt_airyPII hk a b hz)

/-- A valid complex Airy scale exists; it is a cube root of `-1/2`. -/
theorem exists_airy_scale : ∃ k : ℂ, k ^ 3 = -1 / 2 :=
  IsAlgClosed.exists_pow_nat_eq (-1 / 2) (by norm_num)

/-- The `Ai` seed has a nonzero value at the origin, so its regular set is nonempty. -/
theorem airySeed_one_zero_ne_zero (k : ℂ) : airySeed k 1 0 0 ≠ 0 := by
  simp only [airySeed, mul_zero, zero_mul, one_mul, add_zero]
  rw [airyAi_zero]
  apply div_ne_zero one_ne_zero
  apply mul_ne_zero
  · exact ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
  · exact Gamma_ne_zero_of_re_pos (by norm_num)

/-- An explicit rational jet recurrence in the Airy seed, using only arithmetic in
`z`, the Airy functions, and their first derivatives. This realizes the positive
half-integer family in Beals–Wong Proposition 15.4.6. -/
def airyPIIJet (k a b : ℂ) : ℕ → ℂ → ℂ × ℂ
  | 0, z => (airyPII k a b z, -airyPII k a b z ^ 2 - z / 2)
  | n + 1, z => backlundUpJet ((n : ℂ) + 1 / 2) z
      (airyPIIJet k a b n z).1 (airyPIIJet k a b n z).2

/-- The Airy logarithmic quotient is meromorphic on the complex plane. -/
theorem meromorphic_airyPII {k : ℂ} (hk : k ^ 3 = -1 / 2) (a b : ℂ) :
    Meromorphic (airyPII k a b) := by
  have hF : Differentiable ℂ (airySeed k a b) := fun z => (hasDerivAt_airySeed k a b z).differentiableAt
  have hG : Differentiable ℂ (airySeedDeriv k a b) :=
    fun z => (hasDerivAt_airySeedDeriv hk a b z).differentiableAt
  intro z
  exact (hG.analyticAt z).meromorphicAt.div (hF.analyticAt z).meromorphicAt

/-- Both components of each rational Airy jet are meromorphic on the plane. -/
theorem meromorphic_airyPIIJet {k : ℂ} (hk : k ^ 3 = -1 / 2) (a b : ℂ) (n : ℕ) :
    Meromorphic (fun z => (airyPIIJet k a b n z).1) ∧
      Meromorphic (fun z => (airyPIIJet k a b n z).2) := by
  induction n with
  | zero =>
    refine ⟨meromorphic_airyPII hk a b, ?_⟩
    intro z
    have h := meromorphic_airyPII hk a b z
    dsimp only [airyPIIJet]
    fun_prop
  | succ n ih =>
    obtain ⟨hU, hV⟩ := ih
    constructor <;> intro z
    all_goals
      have hu := hU z
      have hv := hV z
      dsimp only [airyPIIJet, backlundUpJet]
      fun_prop

/-- Every nonnegative half-integer Airy jet solves PII on a nonempty open regular set,
provided the starting Airy seed has a nonempty regular set. The recurrence is rational
and its second component is proved to be the derivative of the first. -/
theorem exists_open_isPIIOn_airyPIIJet {k a b : ℂ} (hk : k ^ 3 = -1 / 2)
    (hne : ({z | airySeed k a b z ≠ 0} : Set ℂ).Nonempty) (n : ℕ) :
    ∃ s : Set ℂ, IsOpen s ∧ s.Nonempty ∧
      IsPIIOn ((n : ℂ) + 1 / 2) (fun z => (airyPIIJet k a b n z).1) s ∧
        ∀ z ∈ s, deriv (fun z => (airyPIIJet k a b n z).1) z = (airyPIIJet k a b n z).2 := by
  induction n with
  | zero =>
    refine ⟨{z | airySeed k a b z ≠ 0}, ?_, hne, ?_, ?_⟩
    · exact isOpen_ne_fun
        (continuous_iff_continuousAt.mpr fun z => (hasDerivAt_airySeed k a b z).continuousAt) continuous_const
    · simpa only [airyPIIJet, Nat.cast_zero, zero_add] using isPIIOn_airyPII hk a b
    · intro z hz
      exact (hasDerivAt_airyPII hk a b hz).deriv
  | succ n ih =>
    obtain ⟨s, hs, hne, hsol, hderiv⟩ := ih
    let u (z : ℂ) := (airyPIIJet k a b n z).1
    let S : Set ℂ := s ∩ (backlundDenom (fun z => -u z)) ⁻¹' {z | z ≠ 0}
    have hct : ContinuousOn (backlundDenom (fun z => -u z)) s :=
      fun z hz => (hsol.neg.hasDerivAt_backlundDenom hz).continuousAt.continuousWithinAt
    have hS : IsOpen S := hct.isOpen_inter_preimage hs isOpen_ne
    have hc : 1 - 2 * (-((n : ℂ) + 1 / 2)) ≠ 0 := by
      have he : (1 - 2 * (-((n : ℂ) + 1 / 2))) = ((2 * (n : ℝ) + 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [he]
      exact ofReal_ne_zero.mpr (by positivity)
    obtain ⟨z, hz, hDz⟩ := hsol.neg.exists_backlundDenom_ne_zero hs hne hc
    have hnonempty : S.Nonempty := ⟨z, hz, hDz⟩
    have hD : ∀ z ∈ S, backlundDenom (fun z => -u z) z ≠ 0 := fun _ hz => hz.2
    have hu := (hsol.mono (show S ⊆ s from inter_subset_left)).shiftUp hS hD
    have he : EqOn (backlundUp ((n : ℂ) + 1 / 2) u)
        (fun z => (airyPIIJet k a b (n + 1) z).1) S := by
      intro z hz
      rw [backlundUp_eq]
      dsimp only [airyPIIJet, backlundUpJet]
      rw [hderiv z hz.1]
    refine ⟨S, hS, hnonempty, ?_, ?_⟩
    · convert hu.congr hS he using 1
      push_cast
      ring
    · intro z hz
      have hd := hsol.hasDerivAt_backlundUp hz.1 hz.2
      have hnear : (fun z => (airyPIIJet k a b (n + 1) z).1) =ᶠ[𝓝 z]
          backlundUp ((n : ℂ) + 1 / 2) u := by
        filter_upwards [hS.mem_nhds hz] with t ht using (he ht).symm
      have hval : (backlundUpJet ((n : ℂ) + 1 / 2) z (u z) (deriv u z)).2 =
          (airyPIIJet k a b (n + 1) z).2 := by
        rw [hderiv z hz.1]
        rfl
      exact ((hd.congr_of_eventuallyEq hnear).congr_deriv hval).deriv

/-- The integer-indexed Airy hierarchy: negative indices are obtained by parameter reflection. -/
def airyPIIHierarchy (k a b : ℂ) (n : ℤ) (z : ℂ) : ℂ :=
  if 0 ≤ n then (airyPIIJet k a b n.toNat z).1 else -(airyPIIJet k a b (-n - 1).toNat z).1

/-- The explicitly constructed half-integer Airy hierarchy is globally meromorphic.
This concerns these particular solutions, not the Painlevé property for arbitrary data. -/
theorem meromorphic_airyPIIHierarchy {k : ℂ} (hk : k ^ 3 = -1 / 2) (a b : ℂ) (n : ℤ) :
    Meromorphic (airyPIIHierarchy k a b n) := by
  change Meromorphic (fun z => if 0 ≤ n then _ else _)
  by_cases hn : 0 ≤ n
  · simpa only [hn, ite_true] using (meromorphic_airyPIIJet hk a b n.toNat).1
  · simpa only [hn, ite_false, Pi.neg_def] using
      (meromorphic_airyPIIJet hk a b (-n - 1).toNat).1.neg

/-- Every PII parameter `n+1/2`, `n ∈ ℤ`, has an Airy-based solution on a nonempty open set.
The displayed hierarchy is a finite rational expression in Airy functions and their
first derivatives, rather than a definition by an admitted solution-selection principle. -/
theorem exists_open_isPIIOn_airyPIIHierarchy {k : ℂ} (hk : k ^ 3 = -1 / 2) (n : ℤ) :
    ∃ s : Set ℂ, IsOpen s ∧ s.Nonempty ∧
      IsPIIOn ((n : ℂ) + 1 / 2) (airyPIIHierarchy k 1 0 n) s := by
  have hne : ({z | airySeed k 1 0 z ≠ 0} : Set ℂ).Nonempty := ⟨0, airySeed_one_zero_ne_zero k⟩
  cases n with
  | ofNat n =>
    obtain ⟨s, hs, hne, hsol, _⟩ := exists_open_isPIIOn_airyPIIJet hk hne n
    refine ⟨s, hs, hne, ?_⟩
    rw [Int.ofNat_eq_natCast]
    change IsPIIOn _ (fun z => if 0 ≤ (n : ℤ) then _ else _) s
    simpa only [Int.natCast_nonneg, ite_true, Int.toNat_natCast, Int.cast_natCast] using hsol
  | negSucc n =>
    obtain ⟨s, hs, hne, hsol, _⟩ := exists_open_isPIIOn_airyPIIJet hk hne n
    refine ⟨s, hs, hne, ?_⟩
    have hidx : (-Int.negSucc n - 1).toNat = n := by omega
    have hnot : ¬(0 : ℤ) ≤ Int.negSucc n := by omega
    change IsPIIOn _ (fun z => if 0 ≤ Int.negSucc n then _ else _) s
    simp only [hnot, ite_false, hidx]
    convert hsol.neg using 1
    push_cast
    ring

end DLMF.Painleve
