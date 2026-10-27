/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.Basic
public import DLMF.Spheroidal.P3lParity

/-!
# Spheroidal eigenvalues and eigenfunctions: existence (DLMF §30.3(i), §30.4(i))

Existence of the eigenvalues `λ^m_n(γ²)` (`exists_spheroidalEigenvalue`), existence, uniqueness
and parity of the normalized entire factor (`existsUnique_isSpheroidalPsFactor`), and the
defining properties of the choice definitions `spheroidalEigenvalue` and `spheroidalPsFactor` of
`DLMF.Spheroidal.Basic`. Moved out of the definitions file so that it imports only definitions
files; the proofs rest on `DLMF.Spheroidal.P3lSpectrum` and `DLMF.Spheroidal.P3lParity`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real Classical

namespace DLMF.Spheroidal

/-- `dif_pos` without the deprecation. -/
private lemma s30e_dif_pos {c : Prop} [Decidable c] (h : c) {α : Sort*} {t : c → α}
    {e : ¬c → α} : dite c t e = t h := by simp [h]

/-- The factor equation in the form `DLMF.Spheroidal.p3lSol` used in
`DLMF.Spheroidal.P3lSpectrum`. -/
theorem isSpheroidalFactor_iff {m : ℕ} {γ2 lam : ℝ} {g : ℂ → ℂ} :
    IsSpheroidalFactor m γ2 lam g ↔
      Differentiable ℂ g ∧ p3lSol m (γ2 : ℂ) (p3lC m lam) univ g := by
  constructor
  · intro hg
    refine ⟨hg.differentiable, fun z _ => ?_⟩
    have := hg.ode z
    simp only [p3lC]; push_cast
    linear_combination this
  · rintro ⟨hd, hs⟩
    refine ⟨hd, fun z => ?_⟩
    have := hs z trivial
    simp only [p3lC] at this; push_cast at this
    linear_combination this

/-- The spectrum agrees with `DLMF.Spheroidal.p3lSpec`. -/
theorem spheroidalSpectrum_eq_p3lSpec (m : ℕ) (γ2 : ℝ) :
    spheroidalSpectrum m γ2 = p3lSpec m γ2 := by
  ext lam
  constructor
  · rintro ⟨g, hg, hne⟩
    obtain ⟨hd, hs⟩ := isSpheroidalFactor_iff.1 hg
    exact ⟨g, hd, hs, hne⟩
  · rintro ⟨g, hd, hs, hne⟩
    exact ⟨g, isSpheroidalFactor_iff.2 ⟨hd, hs⟩, hne⟩

/-- **Existence of the eigenvalues** (DLMF §30.3(i)): for `m ≤ n` the spectrum has an element with
exactly `n - m` smaller elements. Flagged existence theorem, proved: the spectrum is infinite and
meets every `(-∞, x)` in a finite set (`p3lSpec_infinite`, `p3lSpec_Iio_finite`). -/
@[dlmf 30.3.i]
theorem exists_spheroidalEigenvalue {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃ lam ∈ spheroidalSpectrum m γ2,
      (spheroidalSpectrum m γ2 ∩ Iio lam).encard = ((n - m : ℕ) : ℕ∞) := by
  have _ := hmn
  rw [spheroidalSpectrum_eq_p3lSpec]
  exact ODE.p2s_exists_encard_eq (p3lSpec_infinite m γ2) (p3lSpec_Iio_finite m γ2) (n - m)

/-- The defining property of `λ^m_n(γ²)` (DLMF §30.3(i)), from `exists_spheroidalEigenvalue`. -/
theorem spheroidalEigenvalue_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    spheroidalEigenvalue n m γ2 ∈ spheroidalSpectrum m γ2 ∧
      (spheroidalSpectrum m γ2 ∩ Iio (spheroidalEigenvalue n m γ2)).encard =
        ((n - m : ℕ) : ℕ∞) := by
  have h := exists_spheroidalEigenvalue hmn γ2
  simp only [spheroidalEigenvalue, s30e_dif_pos h]
  exact h.choose_spec


/-- **Existence and uniqueness of the normalized eigenfunction** (DLMF §30.4(i)). Flagged
existence theorem, proved in `DLMF.Spheroidal.P3lParity`: the eigenvalues are simple, the
eigenfunction can be taken real, and the eigenfunction belonging to `λ^m_n(γ²)` is even (odd)
with `g(0) ≠ 0` (`g'(0) ≠ 0`) for `n - m` even (odd) (`p3l_parity`). -/
@[dlmf 30.4.i]
theorem existsUnique_isSpheroidalPsFactor {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃! g, IsSpheroidalPsFactor n m γ2 g := by
  obtain ⟨hmem, hcard⟩ := spheroidalEigenvalue_spec hmn γ2
  set lam := spheroidalEigenvalue n m γ2
  rw [spheroidalSpectrum_eq_p3lSpec] at hmem hcard
  have hpar := p3l_parity m γ2 (n - m) lam hmem hcard
  have t2 : ∀ k : ℕ, ((-1 : ℝ) ^ k) ^ 2 = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  have key : ∀ h₁ h₂, IsSpheroidalPsFactor n m γ2 h₁ → IsSpheroidalPsFactor n m γ2 h₂ →
      h₁ = h₂ := by
    intro h₁ h₂ H₁ H₂
    obtain ⟨d₁, s₁⟩ := isSpheroidalFactor_iff.1 H₁.factor
    obtain ⟨d₂, s₂⟩ := isSpheroidalFactor_iff.1 H₂.factor
    have P₁ := p3l_data_of_parity hmem d₁ s₁
    have P₂ := p3l_data_of_parity hmem d₂ s₂
    refine p3l_unique d₁ s₁ d₂ s₂ H₁.real H₂.real ?_ (H₁.normalized.trans H₂.normalized.symm) ?_
    · by_cases hq : p3lyR' m γ2 lam 0 = 0
      · rw [P₁.1 hq, P₂.1 hq]; ring
      · rw [P₁.2 hq, P₂.2 hq]; ring
    · by_cases he : Even (n - m)
      · left
        have a := H₁.sign_even he
        have b := H₂.sign_even he
        have e : (-1 : ℝ) ^ ((n + m) / 2) * (h₁ 0).re * ((-1 : ℝ) ^ ((n + m) / 2) * (h₂ 0).re) =
            (h₁ 0).re * (h₂ 0).re := by linear_combination (h₁ 0).re * (h₂ 0).re * t2 _
        rw [← e]; exact mul_pos a b
      · right
        have ho : Odd (n - m) := Nat.not_even_iff_odd.1 he
        have a := H₁.sign_odd ho
        have b := H₂.sign_odd ho
        have e : (-1 : ℝ) ^ ((n + m - 1) / 2) * (deriv h₁ 0).re *
            ((-1 : ℝ) ^ ((n + m - 1) / 2) * (deriv h₂ 0).re) =
            (deriv h₁ 0).re * (deriv h₂ 0).re := by
          linear_combination (deriv h₁ 0).re * (deriv h₂ 0).re * t2 _
        rw [← e]; exact mul_pos a b
  set N : ℝ := 2 / (2 * n + 1) * (((n + m).factorial : ℝ) / (n - m).factorial)
  have hN : 0 < N := by positivity
  set s : ℝ := if Even (n - m) then (-1) ^ ((n + m) / 2) else (-1) ^ ((n + m - 1) / 2)
  have hs2 : s ^ 2 = 1 := by simp only [s]; split_ifs <;> exact t2 _
  obtain ⟨g₁, hd₁, hs₁, hr₁, hev, hod⟩ := p3l_exists_unit hmem
  have hnd : (g₁ 0).re ≠ 0 ∨ (deriv g₁ 0).re ≠ 0 := by
    by_cases hq : p3lyR' m γ2 lam 0 = 0
    · left; rw [(hev hq).1]; simp
    · right; rw [(hod hq).2]; simp
  set I := ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (g₁ x).re ^ 2
  have hI : 0 < I := p3l_norm_pos m hd₁ hnd
  have hsq : Real.sqrt (N / I) ^ 2 = N / I := Real.sq_sqrt (by positivity)
  have hsqp : 0 < Real.sqrt (N / I) := Real.sqrt_pos.2 (by positivity)
  set κ : ℝ := s * Real.sqrt (N / I)
  obtain ⟨gd, gs, ge⟩ := p3lSol_lincomb hd₁ hd₁ hs₁ hs₁ (κ : ℂ) 0
  set g : ℂ → ℂ := fun z => (κ : ℂ) * g₁ z + 0 * g₁ z
  have hgre : ∀ x : ℂ, (g x).re = κ * (g₁ x).re := fun x => by simp [g]
  have hgd0 : (deriv g 0).re = κ * (deriv g₁ 0).re := by rw [ge]; simp
  have Hg : IsSpheroidalPsFactor n m γ2 g := by
    refine ⟨isSpheroidalFactor_iff.2 ⟨gd, gs⟩, fun x => by simp [g, hr₁ x], ?_, ?_, ?_⟩
    · have hint : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (g x).re ^ 2 = κ ^ 2 * I := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp only [hgre]; ring
      rw [hint]
      simp only [κ]
      rw [mul_pow, hsq, hs2, one_mul, div_mul_cancel₀ _ hI.ne']
    · intro he
      have hq := hpar.2 he
      rw [hgre, (hev hq).1]
      simp only [κ, s, he, ↓reduceIte, Complex.one_re, mul_one]
      have e : (-1 : ℝ) ^ ((n + m) / 2) * ((-1) ^ ((n + m) / 2) * Real.sqrt (N / I)) =
          Real.sqrt (N / I) := by linear_combination Real.sqrt (N / I) * t2 _
      rw [e]; exact hsqp
    · intro ho
      have hne : ¬Even (n - m) := Nat.not_even_iff_odd.2 ho
      have hq : p3lyR' m γ2 lam 0 ≠ 0 := fun h => hne (hpar.1 h)
      rw [hgd0, (hod hq).2]
      simp only [κ, s, hne, ↓reduceIte, Complex.one_re, mul_one]
      have e : (-1 : ℝ) ^ ((n + m - 1) / 2) * ((-1) ^ ((n + m - 1) / 2) * Real.sqrt (N / I)) =
          Real.sqrt (N / I) := by linear_combination Real.sqrt (N / I) * t2 _
      rw [e]; exact hsqp
  exact ⟨g, Hg, fun y hy => key y g hy Hg⟩

/-- The defining property of `spheroidalPsFactor`, from `existsUnique_isSpheroidalPsFactor`. -/
theorem spheroidalPsFactor_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    IsSpheroidalPsFactor n m γ2 (spheroidalPsFactor n m γ2) := by
  have h := (existsUnique_isSpheroidalPsFactor hmn γ2).exists
  simp only [spheroidalPsFactor, s30e_dif_pos h]
  exact h.choose_spec

end DLMF.Spheroidal
