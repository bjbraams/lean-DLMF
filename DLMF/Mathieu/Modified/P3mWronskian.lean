/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Modified.BesselSeries
public import DLMF.Bessel.Asymptotics

/-!
# The Wronskian of `M^{(1)}_ν` and `M^{(2)}_ν` (toward DLMF 28.20.21)

The Wronskian `𝒲{M^{(1)}_ν, M^{(2)}_ν}` is constant in `z`. Along the real axis `x → +∞` the
cross-product series 28.24.1 is dominated by its term with `J_0(h e^{-x})`; the other terms are
bounded by `h e^{-x}` times the size of the cylinder functions at `h e^x`, which tend to `0`
(DLMF 10.7.8 and Hankel's expansion 10.17.5). The Wronskian of the dominant terms is
`J_0(h e^{-x})² 𝒲{J_μ(h e^x), Y_μ(h e^x)} = (2/π) J_0(h e^{-x})² → 2/π` (DLMF 10.5.2).

* `p3m_tendsto_besselJ`, `p3m_tendsto_besselY`: `J_λ(x), Y_λ(x) → 0` as `x → +∞`, real `λ`.
* `p3m_F_tail`, `p3m_wronskian_alg`, `p3m_assemble`: the tail estimates.
* `p3m_tendsto_WF`: the Wronskian of the shifted series tends to `(2/π) c_n²`.
* `p3m_wronskian_one_two`: `𝒲{M^{(1)}_ν, M^{(2)}_ν} = 2/π` (DLMF 28.20.21).
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real Nat

namespace DLMF.Mathieu

/-! ### Admissibility and nonvanishing of the coefficients for real parameters -/

/-- `h²` is normal along the segment for real `ν ∉ ℤ` and real `h` (from 28.12(i)). -/
theorem p1c_normal_real {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) (h : ℝ) :
    MathieuNormalSegment ν ((h : ℂ) ^ 2) := by
  have := (mathieuNormalSegment_real (ν := ν) (q := h ^ 2) (p1c_not_int_cast hν)).1
  simpa using this

/-- Real `ν ∉ ℤ` and real `h` are admissible. -/
theorem p1c_admissible_real {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) (h : ℝ) :
    ModMathieuAdmissible ν h := by
  refine Or.inl ⟨p1c_not_int_cast hν, ?_⟩
  have := (mathieuNormalSegment_real (ν := ν) (q := h ^ 2) (p1c_not_int_cast hν)).1
  simpa using this

/-- The normalizing coefficient `c^ν_{2n}(h²)`, `n = modMathieuIndex ν h`, is nonzero for real
`ν ∉ ℤ` and real `h` (the coefficients are not all zero by 28.14.5). -/
theorem p1c_coeff_index_ne_zero {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) (h : ℝ) :
    mathieuMeCoeff ν ((h : ℂ) ^ 2) (modMathieuIndex ν h) ≠ 0 := by
  have hex : ∃ n : ℤ, mathieuMeCoeff ν ((h : ℂ) ^ 2) n ≠ 0 := by
    by_contra hc
    push Not at hc
    have := hasSum_mathieuMeCoeff_sq (p1c_not_int_cast hν) (p1c_normal_real hν h)
    have e : (fun m : ℤ => mathieuMeCoeff ν ((h : ℂ) ^ 2) m ^ 2) = fun _ => 0 :=
      funext fun m => by rw [hc m]; ring
    rw [e] at this
    exact one_ne_zero (this.unique hasSum_zero)
  rw [modMathieuIndex, dite_eq_left hex]
  exact hex.choose_spec

/-- `-ν ∉ ℤ` when `ν ∉ ℤ`. -/
theorem p1c_neg_not_int {ν : ℝ} (hν : ∀ m : ℤ, (m : ℝ) ≠ ν) : ∀ m : ℤ, (m : ℝ) ≠ -ν := by
  intro m hm; exact hν (-m) (by push_cast; linarith)

/-- Every real `ν` with real `h` is admissible. -/
theorem p1c_admissible_real' (ν h : ℝ) : ModMathieuAdmissible ν h := by
  by_cases hν : ∀ m : ℤ, (m : ℝ) ≠ ν
  · exact p1c_admissible_real hν h
  · push Not at hν
    obtain ⟨m, hm⟩ := hν
    exact Or.inr ⟨⟨m, by rw [← hm]; push_cast; rfl⟩, by
      rw [show (h : ℂ) ^ 2 = ((h ^ 2 : ℝ) : ℂ) by push_cast; ring]; exact ofReal_im _⟩

/-- Two naturals have the same parity, or `(-1)^N (-1)^m = -1`. -/
lemma p3m_parity (N m : ℕ) :
    (∃ K : ℤ, (m : ℤ) = N + 2 * K) ∨ (-1 : ℂ) ^ N * (-1 : ℂ) ^ (m : ℤ) = -1 := by
  rcases Int.even_or_odd ((m : ℤ) - N) with ⟨K, hK⟩ | ⟨K, hK⟩
  · exact Or.inl ⟨K, by omega⟩
  · right
    rw [show (m : ℤ) = N + (2 * K + 1) by omega, zpow_add₀ (by norm_num), zpow_natCast,
      zpow_add_one₀ (by norm_num), zpow_mul]
    have e : ((-1 : ℂ) ^ (2 : ℤ)) = 1 := by norm_num
    rw [e, one_zpow, one_mul, mul_neg_one, mul_neg, ← mul_pow]; simp

/-- Not all coefficients `c^ν_{2n}(h²)` vanish, for real `ν` and real `h`. -/
lemma p3m_exists_coeff_ne_zero (ν h : ℝ) : ∃ n : ℤ, mathieuMeCoeff ν ((h : ℂ) ^ 2) n ≠ 0 := by
  by_cases hν : ∀ m : ℤ, (m : ℝ) ≠ ν
  · exact ⟨_, p1c_coeff_index_ne_zero hν h⟩
  push Not at hν
  obtain ⟨k, rfl⟩ := hν
  by_contra hall
  push Not at hall
  have hq2 : (h : ℂ) ^ 2 = ((h ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hq2] at hall
  set q : ℝ := h ^ 2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := by positivity
    exact_mod_cast this.ne'
  rcases Int.eq_nat_or_neg k with ⟨N, rfl | rfl⟩
  · have hI : ∀ K : ℤ, ∫ x in (0 : ℝ)..2 * π,
        mathieuCe N x q * Complex.cos (((N + 2 * K : ℤ) : ℂ) * x) = 0 := by
      intro K
      have h1 := hall K
      have h2 := p2m_mathieuMeCoeff_ce N q K
      push_cast at h1 h2
      rw [h2] at h1
      rcases mul_eq_zero.mp h1 with h3 | h3
      · exfalso; exact div_ne_zero hs2 (mul_ne_zero two_ne_zero hπ) h3
      · push_cast; exact h3
    have hA : ∀ m : ℕ, mathieuFourierA N m q = 0 := by
      intro m
      rcases p3m_parity N m with ⟨K, hK⟩ | hp
      · rw [mathieuFourierA, show ((m : ℕ) : ℂ) = ((N + 2 * K : ℤ) : ℂ) by
          rw [← hK]; push_cast; ring, hI K, mul_zero]
      · refine p1a2_fourierA_eq_zero fun x => ?_
        have hc := p2m_cos_add_int_mul_pi (m : ℤ) x
        push_cast at hc
        rw [p2m_mathieuCe_add_pi, hc]
        linear_combination (mathieuCe N x q * Complex.cos (m * x)) * hp
    have hs := p1a2_hasSum_mathieuCe N q 0
    simp only [hA, zero_mul] at hs
    have h0 := hs.unique hasSum_zero
    rw [mathieuCe_zero] at h0
    exact (mathieuCeZero_pos N q).ne' (by exact_mod_cast h0)
  · rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have hI : ∀ K : ℤ, ∫ x in (0 : ℝ)..2 * π,
          mathieuCe 0 x q * Complex.cos ((((0 : ℕ) : ℤ) + 2 * K : ℤ) * x) = 0 := by
        intro K
        have h1 := hall K
        have h2 := p2m_mathieuMeCoeff_ce 0 q K
        push_cast at h1 h2
        rw [h2] at h1
        rcases mul_eq_zero.mp h1 with h3 | h3
        · exfalso; exact div_ne_zero hs2 (mul_ne_zero two_ne_zero hπ) h3
        · push_cast; exact h3
      have hA : ∀ m : ℕ, mathieuFourierA 0 m q = 0 := by
        intro m
        rcases p3m_parity 0 m with ⟨K, hK⟩ | hp
        · rw [mathieuFourierA, show ((m : ℕ) : ℂ) = ((((0 : ℕ) : ℤ) + 2 * K : ℤ) : ℂ) by
            rw [← hK]; push_cast; ring, hI K, mul_zero]
        · refine p1a2_fourierA_eq_zero fun x => ?_
          have hc := p2m_cos_add_int_mul_pi (m : ℤ) x
          push_cast at hc
          rw [p2m_mathieuCe_add_pi, hc]
          linear_combination (mathieuCe 0 x q * Complex.cos (m * x)) * hp
      have hs := p1a2_hasSum_mathieuCe 0 q 0
      simp only [hA, zero_mul] at hs
      have h0 := hs.unique hasSum_zero
      rw [mathieuCe_zero] at h0
      exact (mathieuCeZero_pos 0 q).ne' (by exact_mod_cast h0)
    have hN0 : N ≠ 0 := hN.ne'
    have hI : ∀ K : ℤ, ∫ x in (0 : ℝ)..2 * π,
        mathieuSe N x q * Complex.sin (((-(N : ℤ) + 2 * K : ℤ) : ℂ) * x) = 0 := by
      intro K
      have h1 := hall K
      have h2 := p2m_mathieuMeCoeff_se hN0 q K
      push_cast at h1 h2
      rw [h2] at h1
      rcases mul_eq_zero.mp h1 with h3 | h3
      · exfalso; exact neg_ne_zero.mpr (div_ne_zero hs2 (mul_ne_zero two_ne_zero hπ)) h3
      · push_cast; exact h3
    have hB : ∀ m : ℕ, mathieuFourierB N m q = 0 := by
      intro m
      rcases p3m_parity N m with ⟨K, hK⟩ | hp
      · rw [mathieuFourierB, show ((m : ℕ) : ℂ) = ((-(N : ℤ) + 2 * (K + N) : ℤ) : ℂ) by
          rw [show -(N : ℤ) + 2 * (K + N) = N + 2 * K by ring, ← hK]; push_cast; ring,
          hI (K + N), mul_zero]
      · refine p1a2_fourierB_eq_zero fun x => ?_
        have hc := p2m_sin_add_int_mul_pi (m : ℤ) x
        push_cast at hc
        rw [p2m_mathieuSe_add_pi hN0, hc]
        linear_combination (mathieuSe N x q * Complex.sin (m * x)) * hp
    have hzero : (fun z => mathieuSe N z q) = fun _ => 0 := by
      funext z
      have hs := p1a2_hasSum_mathieuSe hN0 q z
      simp only [hB, zero_mul] at hs
      exact hs.unique hasSum_zero
    have hd := deriv_mathieuSe_zero N q
    rw [hzero, deriv_const] at hd
    exact (mathieuSeDerivZero_pos N q).ne' (by exact_mod_cast hd.symm)

/-- `J_λ(x) → 0` as `x → +∞` (real `λ`; DLMF 10.7.8). -/
lemma p3m_tendsto_besselJ (l : ℝ) :
    Tendsto (fun x : ℝ => besselJ (l : ℂ) (x : ℂ)) atTop (𝓝 0) := by
  have h1 := (DLMF.Bessel.besselJ_sub_cos_isBigO (l : ℂ)).trans_tendsto
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2))
  have h2 : Tendsto (fun x : ℝ => (Real.sqrt (2 / (π * x)) : ℂ) *
      Complex.cos (x - (l : ℂ) * π / 2 - π / 4)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hs : Tendsto (fun x : ℝ => Real.sqrt (2 / (π * x))) atTop (𝓝 0) := by
      have : Tendsto (fun x : ℝ => 2 / (π * x)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (Tendsto.const_mul_atTop Real.pi_pos tendsto_id)
      simpa using this.sqrt
    refine squeeze_zero (fun x => norm_nonneg _) (fun x => ?_) hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      show (x : ℂ) - (l : ℂ) * π / 2 - π / 4 = ((x - l * π / 2 - π / 4 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_cos_le_one _)
  simpa using h1.add h2

/-- `H^{(1)}_λ(x) → 0` as `x → +∞` (Hankel's expansion, DLMF 10.17.5). -/
lemma p3m_tendsto_hankelH1 (l : ℂ) :
    Tendsto (fun x : ℝ => DLMF.Bessel.hankelH1 l (x : ℂ)) atTop (𝓝 0) := by
  have h0 := DLMF.Bessel.hasAsymptoticExpansion_hankelH1 l 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, Nat.cast_zero, zero_add] at h0
  have hg : Tendsto (fun x : ℝ => (2 * (-I * x)) ^ (-(1 / 2 : ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : Tendsto (fun x : ℝ => (2 * x) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp
        (Tendsto.const_mul_atTop (by norm_num) tendsto_id)
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hne : (2 * (-I * x) : ℂ) ≠ 0 := by
      simp [hx.ne']
    rw [Complex.norm_cpow_of_ne_zero hne]
    simp [abs_of_pos hx]
  have h1 := h0.trans_tendsto hg
  rw [tendsto_zero_iff_norm_tendsto_zero] at h1 ⊢
  refine h1.congr fun x => ?_
  rw [norm_mul, show -I * (x : ℂ) = ((-x : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `Y_λ(x) → 0` as `x → +∞` (real `λ`). -/
lemma p3m_tendsto_besselY (l : ℝ) :
    Tendsto (fun x : ℝ => DLMF.Bessel.besselY (l : ℂ) (x : ℂ)) atTop (𝓝 0) := by
  have h := ((p3m_tendsto_hankelH1 l).sub (p3m_tendsto_besselJ l)).mul_const (-I)
  simp only [sub_zero, zero_mul] at h
  refine h.congr fun x => ?_
  simp only [DLMF.Bessel.hankelH1]
  ring_nf
  rw [I_sq]; ring

/-- The continued cylinder functions `𝒞^{(j)}_λ(h e^x)`, `j = 1, 2`, tend to `0` as `x → +∞`
(real `λ`, `h > 0`). -/
lemma p3m_tendsto_mathieuCylExp {j : ℕ} (hj : j = 1 ∨ j = 2) (l : ℝ) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun x : ℝ => mathieuCylExp j l h x) atTop (𝓝 0) := by
  have he : ∀ x : ℝ, mathieuCylExp j l h x = mathieuCyl j l ((h * Real.exp x : ℝ) : ℂ) := by
    intro x
    rw [mathieuCylExp_eq_mathieuCyl j l hh (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
    push_cast; rfl
  simp only [he]
  have ht : Tendsto (fun x : ℝ => h * Real.exp x) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hh
  rcases hj with rfl | rfl
  · exact (p3m_tendsto_besselJ l).comp ht
  · exact (p3m_tendsto_besselY l).comp ht

/-- The constant of the tail bounds `p3m_F_tail`. -/
def p3m_L (Cc K C : ℝ) (β : ℤ) : ℝ :=
  Cc * Real.exp 1 * (2 * C) * (2 * (4 * C)) ^ β.natAbs * (β.natAbs ! : ℝ) *
    ∑' ℓ : ℤ, (2 * K * 1 * (4 * C)) ^ ℓ.natAbs / (ℓ.natAbs ! : ℝ)

/-- **Tail bounds** for the shifted cross-product series at real `x`: with `u = h e^{-x} ≤ 2`,
`|F_{α,β}(x)| ≤ L U` and `|F_{α,β}(x) - (term ℓ = -α)| ≤ L U u/2`, where `U` bounds
`|𝒞_{ν-1}|, |𝒞_ν|, |𝒞_{ν+1}|` at `h e^x`. -/
lemma p3m_F_tail (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (ν : ℂ) {h : ℝ} (hh : 0 < h)
    {c : ℤ → ℂ} {Cc K : ℝ} (hCc : 0 ≤ Cc) (hK : 0 ≤ K)
    (hc : ∀ m : ℤ, ‖c m‖ * (m.natAbs ! : ℝ) ^ 2 ≤ Cc * K ^ m.natAbs) {C : ℝ} (hC : 1 ≤ C)
    (α β : ℤ) {x : ℝ} (hu : h * Real.exp (-x) ≤ 2)
    (hCw : 2 * (‖ν‖ + 1) / (h * Real.exp x) ≤ C) {U : ℝ}
    (hU1 : ‖mathieuCylExp j (ν + ((-1 : ℤ) : ℂ)) h x‖ ≤ U)
    (hU0 : ‖mathieuCylExp j (ν + ((0 : ℤ) : ℂ)) h x‖ ≤ U)
    (hU2 : ‖mathieuCylExp j (ν + ((1 : ℤ) : ℂ)) h x‖ ≤ U) :
    ‖p2m_F j ν h c α β x‖ ≤ p3m_L Cc K C β * U ∧
      ‖p2m_F j ν h c α β x - p2m_fam c (p2m_Jz h x) (p2m_Cz j ν h x) α β (-α)‖ ≤
        p3m_L Cc K C β * U * (h * Real.exp (-x) / 2) := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set u := h * Real.exp (-x) with hudef
  have hu0 : 0 ≤ u := by positivity
  have hnorm : ‖(h : ℂ) * Complex.exp (-(x : ℂ))‖ = u := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, ← Complex.ofReal_neg,
      Complex.norm_exp_ofReal]
  have hE : Real.exp (u ^ 2 / 4) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by nlinarith)
  have hJ : ∀ k : ℤ, ‖p2m_Jz h x k‖ ≤ Real.exp 1 * 1 ^ k.natAbs := by
    intro k
    simp only [p2m_Jz, one_pow, mul_one]
    rw [p1c_besselJExp_intCast]
    refine (Complex.norm_besselJ_intCast_le k _).trans ?_
    rw [hnorm]
    refine (mul_le_mul hE ?_ (by positivity) (by positivity)).trans (le_of_eq (mul_one _))
    calc (u / 2) ^ k.natAbs / (k.natAbs ! : ℝ) ≤ (u / 2) ^ k.natAbs :=
          div_le_self (by positivity) (Nat.one_le_cast.mpr (Nat.factorial_pos _))
      _ ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  have hJ' : ∀ k : ℤ,
      ‖Function.update (p2m_Jz h x) 0 0 k‖ ≤ (Real.exp 1 * (u / 2)) * 1 ^ k.natAbs := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp; positivity
    rw [Function.update_of_ne hk, one_pow, mul_one]
    simp only [p2m_Jz]
    rw [p1c_besselJExp_intCast]
    refine (Complex.norm_besselJ_intCast_le k _).trans ?_
    rw [hnorm]
    refine mul_le_mul hE ?_ (by positivity) (by positivity)
    have hk1 : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk
    calc (u / 2) ^ k.natAbs / (k.natAbs ! : ℝ) ≤ (u / 2) ^ k.natAbs :=
          div_le_self (by positivity) (Nat.one_le_cast.mpr (Nat.factorial_pos _))
      _ ≤ (u / 2) ^ 1 := pow_le_pow_of_le_one (by positivity) (by linarith) hk1
      _ = u / 2 := pow_one _
  have hy : (h : ℂ) * Complex.exp (x : ℂ) ≠ 0 := mul_ne_zero hh' (Complex.exp_ne_zero _)
  have hynorm : ‖(h : ℂ) * Complex.exp (x : ℂ)‖ = h * Real.exp x := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, Complex.norm_exp_ofReal]
  have hCb : ∀ k : ℤ, ‖p2m_Cz j ν h x k‖ ≤ U * (2 * C) * (4 * C) ^ k.natAbs * (k.natAbs ! : ℝ) := by
    intro k
    refine p2m_growth_int_unif (ν := ν) hy hC (by rw [hynorm]; exact hCw) ?_ ?_ ?_ ?_ k
    · simpa only [p2m_Cz] using hU1
    · simpa only [p2m_Cz] using hU0
    · simpa only [p2m_Cz] using hU2
    · intro k
      have := p2m_mathieuCylExp_rec j hj₁ hj₄ (ν + k) hh' x
      simp only [p2m_Cz]
      push_cast
      rw [← add_sub_assoc, ← add_assoc]
      exact this
  have hU : 0 ≤ U := (norm_nonneg _).trans hU0
  have hEC : 0 ≤ U * (2 * C) := by positivity
  have hA : 1 ≤ 4 * C := by linarith
  constructor
  · have hF := p2m_hasSum_F j hj₁ hj₄ ν hh' hCc hK hc α β x
    rw [← hF.tsum_eq]
    refine (p2m_fam_tsum_le hCc hK (Real.exp_pos 1).le le_rfl hEC hA hc hJ hCb α β).trans
      (le_of_eq ?_)
    simp only [p3m_L, one_pow]; ring
  · have hF := p2m_hasSum_F j hj₁ hj₄ ν hh' hCc hK hc α β x
    have hupd : p2m_fam c (Function.update (p2m_Jz h x) 0 0) (p2m_Cz j ν h x) α β =
        Function.update (p2m_fam c (p2m_Jz h x) (p2m_Cz j ν h x) α β) (-α) 0 := by
      funext ℓ
      by_cases hl : ℓ = -α
      · subst hl; simp [p2m_fam]
      · rw [Function.update_of_ne hl]
        have : ℓ + α ≠ 0 := fun h0 => hl (by omega)
        simp only [p2m_fam, Function.update_of_ne this]
    have hT := hF.update (-α) 0
    rw [← hupd] at hT
    rw [show p2m_F j ν h c α β x - p2m_fam c (p2m_Jz h x) (p2m_Cz j ν h x) α β (-α) =
      0 - p2m_fam c (p2m_Jz h x) (p2m_Cz j ν h x) α β (-α) + p2m_F j ν h c α β x by ring,
      ← hT.tsum_eq]
    have hEJ : 0 ≤ Real.exp 1 * (u / 2) := by positivity
    refine (p2m_fam_tsum_le hCc hK hEJ le_rfl hEC hA hc hJ' hCb α β).trans (le_of_eq ?_)
    simp only [p3m_L, one_pow]; ring

/-- `J_0(h e^{-x}) → 1` as `x → +∞`. -/
lemma p3m_tendsto_besselJExp_zero (h : ℂ) :
    Tendsto (fun x : ℝ => besselJExp 0 h (-(x : ℂ))) atTop (𝓝 1) := by
  have e : ∀ x : ℝ, besselJExp 0 h (-(x : ℂ)) =
      regularizedHGFun (∅ : Multiset ℂ) {(0 : ℂ) + 1}
        (-((h * ((Real.exp (-x) : ℝ) : ℂ)) ^ 2 / 4)) := by
    intro x; simp [besselJExp]
  simp only [e]
  have h1 : regularizedHGFun (∅ : Multiset ℂ) {1} 0 = 1 := by
    have := DLMF.Bessel.besselJ_eq_regularized 0 0
    rw [DLMF.Bessel.besselJ_zero_zero] at this
    simpa using this.symm
  have hc := DLMF.Bessel.continuous_regularized0F1.comp
    (continuous_const.prodMk (((continuous_const.mul Complex.continuous_ofReal).pow 2).div_const
      4).neg : Continuous fun t : ℝ => ((0 : ℂ) + 1, -((h * (t : ℂ)) ^ 2 / 4)))
  have := (hc.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
  simp only [Function.comp_def] at this
  convert this using 2
  rw [show (-((h * ((0 : ℝ) : ℂ)) ^ 2 / 4)) = 0 by simp, zero_add]; exact h1.symm

/-- The cross product of the continued `J` and `Y` at real `x`:
`J_μ (Y_{μ-1} - Y_{μ+1}) - (J_{μ-1} - J_{μ+1}) Y_μ = 4/(π h e^x)`. -/
lemma p3m_cyl_bracket (μ : ℂ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    mathieuCylExp 1 μ h x * (mathieuCylExp 2 (μ - 1) h x - mathieuCylExp 2 (μ + 1) h x) -
      (mathieuCylExp 1 (μ - 1) h x - mathieuCylExp 1 (μ + 1) h x) * mathieuCylExp 2 μ h x =
        4 / (π * ((h : ℂ) * Complex.exp x)) := by
  have hz₁ : -π < (x : ℂ).im := by simp [Real.pi_pos]
  have hz₂ : (x : ℂ).im ≤ π := by simp [Real.pi_pos.le]
  simp only [mathieuCylExp_eq_mathieuCyl _ _ hh hz₁ hz₂, mathieuCyl]
  set w : ℂ := (h : ℂ) * Complex.exp x
  have hw : w ∈ slitPlane := by
    have : w = ((h * Real.exp x : ℝ) : ℂ) := by simp [w]
    rw [this, ofReal_mem_slitPlane]; positivity
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have eJ := DLMF.Bessel.besselJ_add_sub (ν := μ) hw0
  have eY := DLMF.Bessel.besselY_add_sub μ hw
  have eW := DLMF.Bessel.besselJ_succ_mul_besselY_sub μ hw
  linear_combination (-besselJ μ w) * eY + DLMF.Bessel.besselY μ w * eJ + 2 * eW

/-- The algebraic error estimate for the Wronskian of the cross-product series. -/
lemma p3m_wronskian_alg {F1 F2 P1 P2 R1 R2 m1 m2 q1 q2 : ℂ} {u v h2 B : ℝ} (hu : 0 ≤ u)
    (hu2 : u ≤ 2) (hv : 0 ≤ v) (huv : u * v = h2) (hB : 0 ≤ B) (hF1 : ‖F1‖ ≤ B)
    (hF2 : ‖F2‖ ≤ B) (hm1 : ‖F1 - m1‖ ≤ B * u) (hm2 : ‖F2 - m2‖ ≤ B * u)
    (hP1 : ‖P1 - q1‖ ≤ B * u) (hP2 : ‖P2 - q2‖ ≤ B * u) (hq1 : ‖q1‖ ≤ B) (hq2 : ‖q2‖ ≤ B)
    (hR1 : ‖R1‖ ≤ B) (hR2 : ‖R2‖ ≤ B) :
    ‖F1 * (-((u : ℂ) / 2) * R2 + (v : ℂ) / 2 * P2) - (-((u : ℂ) / 2) * R1 + (v : ℂ) / 2 * P1) * F2 -
        (v : ℂ) / 2 * (m1 * q2 - q1 * m2)‖ ≤ (2 * h2 + 2) * B ^ 2 := by
  set X := F1 * (P2 - q2) + (F1 - m1) * q2 - (P1 - q1) * F2 - q1 * (F2 - m2)
  set Y := F1 * R2 - R1 * F2
  have e : F1 * (-((u : ℂ) / 2) * R2 + (v : ℂ) / 2 * P2) -
      (-((u : ℂ) / 2) * R1 + (v : ℂ) / 2 * P1) * F2 - (v : ℂ) / 2 * (m1 * q2 - q1 * m2) =
      (v : ℂ) / 2 * X - (u : ℂ) / 2 * Y := by simp only [X, Y]; ring
  have hX : ‖X‖ ≤ 4 * (B * (B * u)) := by
    have e1 := norm_sub_le (F1 * (P2 - q2) + (F1 - m1) * q2 - (P1 - q1) * F2) (q1 * (F2 - m2))
    have e2 := norm_sub_le (F1 * (P2 - q2) + (F1 - m1) * q2) ((P1 - q1) * F2)
    have e3 := norm_add_le (F1 * (P2 - q2)) ((F1 - m1) * q2)
    simp only [norm_mul] at e1 e2 e3
    have a1 := mul_le_mul hF1 hP2 (norm_nonneg _) hB
    have a2 := mul_le_mul hm1 hq2 (norm_nonneg _) (by positivity)
    have a3 := mul_le_mul hP1 hF2 (norm_nonneg _) (by positivity)
    have a4 := mul_le_mul hq1 hm2 (norm_nonneg _) hB
    nlinarith
  have hY : ‖Y‖ ≤ 2 * (B * B) := by
    have e1 := norm_sub_le (F1 * R2) (R1 * F2)
    simp only [norm_mul] at e1
    have a1 := mul_le_mul hF1 hR2 (norm_nonneg _) hB
    have a2 := mul_le_mul hR1 hF2 (norm_nonneg _) hB
    simp only [Y]; linarith
  rw [e]
  have nv : ‖(v : ℂ) / 2‖ = v / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]; norm_num
  have nu : ‖(u : ℂ) / 2‖ = u / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]; norm_num
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, nv, nu]
  have b1 := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ v / 2)
  have b2 := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ u / 2)
  have : v / 2 * (4 * (B * (B * u))) = 2 * h2 * B ^ 2 := by rw [← huv]; ring
  nlinarith [sq_nonneg B, mul_nonneg hu (sq_nonneg B)]

lemma p3m_main_bound {F m : ℂ} {b u : ℝ} (hb : 0 ≤ b) (hu2 : u ≤ 2) (hF : ‖F‖ ≤ b)
    (hFm : ‖F - m‖ ≤ b * (u / 2)) : ‖m‖ ≤ 2 * b := by
  have := norm_sub_le F (F - m)
  rw [sub_sub_cancel] at this
  nlinarith [mul_le_mul_of_nonneg_left hu2 hb]

/-- Assembly of the tail bounds into the Wronskian estimate. -/
lemma p3m_assemble {F1 F2 G1a G1c G2a G2c H1a H1c H2a H2c m1 m2 m1a m1c m2a m2c : ℂ}
    {u v h2 a b c : ℝ} (hu : 0 ≤ u) (hu2 : u ≤ 2) (hv : 0 ≤ v) (huv : u * v = h2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (f1 : ‖F1‖ ≤ b) (g1 : ‖F1 - m1‖ ≤ b * (u / 2)) (f2 : ‖F2‖ ≤ b) (g2 : ‖F2 - m2‖ ≤ b * (u / 2))
    (f1a : ‖G1a‖ ≤ a) (g1a : ‖G1a - m1a‖ ≤ a * (u / 2))
    (f1c : ‖G1c‖ ≤ c) (g1c : ‖G1c - m1c‖ ≤ c * (u / 2))
    (f2a : ‖G2a‖ ≤ a) (g2a : ‖G2a - m2a‖ ≤ a * (u / 2))
    (f2c : ‖G2c‖ ≤ c) (g2c : ‖G2c - m2c‖ ≤ c * (u / 2))
    (r1a : ‖H1a‖ ≤ b) (r1c : ‖H1c‖ ≤ b) (r2a : ‖H2a‖ ≤ b) (r2c : ‖H2c‖ ≤ b) :
    ‖F1 * (-((u : ℂ) / 2) * (H2a - H2c) + (v : ℂ) / 2 * (G2a - G2c)) -
        (-((u : ℂ) / 2) * (H1a - H1c) + (v : ℂ) / 2 * (G1a - G1c)) * F2 -
        (v : ℂ) / 2 * (m1 * (m2a - m2c) - (m1a - m1c) * m2)‖ ≤
      (2 * h2 + 2) * (2 * (a + b + c)) ^ 2 := by
  have hB : 0 ≤ 2 * (a + b + c) := by positivity
  have hau := mul_nonneg ha hu
  have hbu := mul_nonneg hb hu
  have hcu := mul_nonneg hc hu
  have sub_b : ∀ {X Y : ℂ} {p r : ℝ}, ‖X‖ ≤ p → ‖Y‖ ≤ r → ‖X - Y‖ ≤ p + r := fun hX hY =>
    (norm_sub_le _ _).trans (add_le_add hX hY)
  refine p3m_wronskian_alg hu hu2 hv huv hB ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · linarith
  · linarith
  · linarith
  · linarith
  · have := sub_b g1a g1c
    rw [show G1a - G1c - (m1a - m1c) = (G1a - m1a) - (G1c - m1c) by ring]; nlinarith
  · have := sub_b g2a g2c
    rw [show G2a - G2c - (m2a - m2c) = (G2a - m2a) - (G2c - m2c) by ring]; nlinarith
  · have := sub_b (p3m_main_bound ha hu2 f1a g1a) (p3m_main_bound hc hu2 f1c g1c); linarith
  · have := sub_b (p3m_main_bound ha hu2 f2a g2a) (p3m_main_bound hc hu2 f2c g2c); linarith
  · have := sub_b r1a r1c; linarith
  · have := sub_b r2a r2c; linarith

lemma p3m_L_nonneg {Cc K C : ℝ} (hCc : 0 ≤ Cc) (hK : 0 ≤ K) (hC : 0 ≤ C) (β : ℤ) :
    0 ≤ p3m_L Cc K C β := by
  unfold p3m_L
  have : 0 ≤ ∑' ℓ : ℤ, (2 * K * 1 * (4 * C)) ^ ℓ.natAbs / (ℓ.natAbs ! : ℝ) :=
    tsum_nonneg fun ℓ => by positivity
  positivity

/-- The derivative of the shifted cross-product series `F_{-n,n}` (from `p2m_hasDerivAt_F`). -/
def p3m_D (j : ℕ) (ν h : ℂ) (c : ℤ → ℂ) (n : ℤ) (z : ℂ) : ℂ :=
  -(h * Complex.exp (-z) / 2) * (p2m_F j ν h c (-n - 1) n z - p2m_F j ν h c (-n + 1) n z) +
    h * Complex.exp z / 2 * (p2m_F j ν h c (-n) (n - 1) z - p2m_F j ν h c (-n) (n + 1) z)

/-- The Wronskian of `F^{(1)}_{-n,n}` and `F^{(2)}_{-n,n}`. -/
def p3m_WF (ν h : ℂ) (c : ℤ → ℂ) (n : ℤ) (z : ℂ) : ℂ :=
  p2m_F 1 ν h c (-n) n z * p3m_D 2 ν h c n z - p3m_D 1 ν h c n z * p2m_F 2 ν h c (-n) n z

/-- The Wronskian of the dominant terms. -/
lemma p3m_main_term (ν : ℂ) {h : ℝ} (hh : 0 < h) (c : ℤ → ℂ) (n : ℤ) (x : ℝ) :
    ((h * Real.exp x : ℝ) : ℂ) / 2 *
      (p2m_fam c (p2m_Jz h x) (p2m_Cz 1 ν h x) (-n) n (-(-n)) *
          (p2m_fam c (p2m_Jz h x) (p2m_Cz 2 ν h x) (-n) (n - 1) (-(-n)) -
            p2m_fam c (p2m_Jz h x) (p2m_Cz 2 ν h x) (-n) (n + 1) (-(-n))) -
        (p2m_fam c (p2m_Jz h x) (p2m_Cz 1 ν h x) (-n) (n - 1) (-(-n)) -
            p2m_fam c (p2m_Jz h x) (p2m_Cz 1 ν h x) (-n) (n + 1) (-(-n))) *
          p2m_fam c (p2m_Jz h x) (p2m_Cz 2 ν h x) (-n) n (-(-n))) =
      2 / π * ((-1 : ℂ) ^ n * c n * p2m_Jz h x 0) ^ 2 := by
  simp only [p2m_fam, neg_neg, add_neg_cancel, p2m_Cz]
  have e1 : ν + ((n - 1 + n : ℤ) : ℂ) = (ν + ((n + n : ℤ) : ℂ)) - 1 := by push_cast; ring
  have e2 : ν + ((n + 1 + n : ℤ) : ℂ) = (ν + ((n + n : ℤ) : ℂ)) + 1 := by push_cast; ring
  rw [e1, e2]
  have hb := p3m_cyl_bracket (ν + ((n + n : ℤ) : ℂ)) hh x
  have hw : ((h * Real.exp x : ℝ) : ℂ) = (h : ℂ) * Complex.exp x := by push_cast; rfl
  have hw0 : (h : ℂ) * Complex.exp x ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hh.ne') (Complex.exp_ne_zero _)
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hw]
  set μ := ν + ((n + n : ℤ) : ℂ)
  have hb' : (h : ℂ) * Complex.exp x *
      (mathieuCylExp 1 μ h x * (mathieuCylExp 2 (μ - 1) h x - mathieuCylExp 2 (μ + 1) h x) -
      (mathieuCylExp 1 (μ - 1) h x - mathieuCylExp 1 (μ + 1) h x) * mathieuCylExp 2 μ h x) =
        4 / π := by
    have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    rw [hb]; field_simp
  linear_combination ((((-1 : ℂ) ^ n * c n * p2m_Jz h x 0) ^ 2) / 2) * hb'

lemma p3m_negOnePow_zpow_sq (n : ℤ) : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; norm_num

/-- Along the real axis the Wronskian of `F^{(1)}_{-n,n}` and `F^{(2)}_{-n,n}` tends to
`(2/π) c_n²`. -/
lemma p3m_tendsto_WF {ν h : ℝ} (hh : 0 < h) (n : ℤ) :
    Tendsto (fun x : ℝ => p3m_WF ν h (mathieuMeCoeff ν ((h : ℂ) ^ 2)) n x) atTop
      (𝓝 (2 / π * mathieuMeCoeff ν ((h : ℂ) ^ 2) n ^ 2)) := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  obtain ⟨Cc, K, hCc, hK, hc⟩ := p2m_coeff_decay (p1c_admissible_real' ν h) hh'
  set c := mathieuMeCoeff (ν : ℂ) ((h : ℂ) ^ 2) with hcdef
  set C := max 1 (2 * (‖(ν : ℂ)‖ + 1) / h) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := by linarith
  set La := p3m_L Cc K C (n - 1)
  set Lb := p3m_L Cc K C n
  set Lc := p3m_L Cc K C (n + 1)
  have hLa : 0 ≤ La := p3m_L_nonneg hCc hK hC0 _
  have hLb : 0 ≤ Lb := p3m_L_nonneg hCc hK hC0 _
  have hLc : 0 ≤ Lc := p3m_L_nonneg hCc hK hC0 _
  set Λ := La + Lb + Lc
  let N : ℕ → ℤ → ℝ → ℝ := fun j k x => ‖mathieuCylExp j ((ν : ℂ) + ((k : ℤ) : ℂ)) h x‖
  let U : ℝ → ℝ := fun x => N 1 (-1) x + N 1 0 x + N 1 1 x + N 2 (-1) x + N 2 0 x + N 2 1 x
  let main : ℝ → ℂ := fun x => 2 / π * ((-1 : ℂ) ^ n * c n * p2m_Jz h x 0) ^ 2
  -- the dominant part tends to `(2/π) c_n²`
  have T1 : Tendsto main atTop (𝓝 (2 / π * c n ^ 2)) := by
    have hJ : Tendsto (fun x : ℝ => p2m_Jz h x 0) atTop (𝓝 1) := by
      simpa [p2m_Jz] using p3m_tendsto_besselJExp_zero (h : ℂ)
    have := ((hJ.const_mul ((-1 : ℂ) ^ n * c n)).pow 2).const_mul (2 / π : ℂ)
    convert this using 2
    rw [mul_one, mul_pow, p3m_negOnePow_zpow_sq, one_mul]
  -- the size of the cylinder functions tends to `0`
  have hN : ∀ j, (j = 1 ∨ j = 2) → ∀ k : ℤ, Tendsto (N j k) atTop (𝓝 0) := by
    intro j hj k
    have := (p3m_tendsto_mathieuCylExp hj (ν + k) hh).norm
    simpa [N] using this
  have TU : Tendsto U atTop (𝓝 0) := by
    have := (((((hN 1 (Or.inl rfl) (-1)).add (hN 1 (Or.inl rfl) 0)).add
      (hN 1 (Or.inl rfl) 1)).add (hN 2 (Or.inr rfl) (-1))).add (hN 2 (Or.inr rfl) 0)).add
      (hN 2 (Or.inr rfl) 1)
    simpa using this
  have T2 : Tendsto (fun x => (2 * h ^ 2 + 2) * (2 * Λ * U x) ^ 2) atTop (𝓝 0) := by
    have := ((TU.const_mul (2 * Λ)).pow 2).const_mul (2 * h ^ 2 + 2)
    simpa using this
  -- the estimate
  have hev : ∀ᶠ x in atTop, 0 ≤ x ∧ h * Real.exp (-x) ≤ 2 := by
    have ht : Tendsto (fun x : ℝ => h * Real.exp (-x)) atTop (𝓝 (h * 0)) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.const_mul h
    filter_upwards [eventually_ge_atTop 0,
      ht.eventually (gt_mem_nhds (by norm_num : h * 0 < 2))] with x hx hx'
    exact ⟨hx, hx'.le⟩
  have hbound : ∀ᶠ x : ℝ in atTop, ‖p3m_WF ν h c n (x : ℂ) - main x‖ ≤
      (2 * h ^ 2 + 2) * (2 * Λ * U x) ^ 2 := by
    filter_upwards [hev] with x ⟨hx0, hu⟩
    set u := h * Real.exp (-x) with hudef
    set v := h * Real.exp x with hvdef
    have hu0 : 0 ≤ u := by positivity
    have hv0 : 0 ≤ v := by positivity
    have huv : u * v = h ^ 2 := by
      rw [hudef, hvdef, mul_mul_mul_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero]; ring
    have hCw : 2 * (‖(ν : ℂ)‖ + 1) / (h * Real.exp x) ≤ C := by
      refine le_trans ?_ (le_max_right _ _)
      refine div_le_div_of_nonneg_left (by positivity) hh ?_
      exact le_mul_of_one_le_right hh.le (Real.one_le_exp hx0)
    have hU0 : 0 ≤ U x := by simp only [U, N]; positivity
    have b1 : ∀ k : ℤ, k = -1 ∨ k = 0 ∨ k = 1 → N 1 k x ≤ U x := by
      rintro k (rfl | rfl | rfl) <;> simp only [U] <;>
        linarith [norm_nonneg (mathieuCylExp 1 ((ν : ℂ) + ((-1 : ℤ) : ℂ)) h x),
          norm_nonneg (mathieuCylExp 1 ((ν : ℂ) + ((0 : ℤ) : ℂ)) h x),
          norm_nonneg (mathieuCylExp 1 ((ν : ℂ) + ((1 : ℤ) : ℂ)) h x),
          norm_nonneg (mathieuCylExp 2 ((ν : ℂ) + ((-1 : ℤ) : ℂ)) h x),
          norm_nonneg (mathieuCylExp 2 ((ν : ℂ) + ((0 : ℤ) : ℂ)) h x),
          norm_nonneg (mathieuCylExp 2 ((ν : ℂ) + ((1 : ℤ) : ℂ)) h x)]
    have b2 : ∀ k : ℤ, k = -1 ∨ k = 0 ∨ k = 1 → N 2 k x ≤ U x := by
      rintro k (rfl | rfl | rfl) <;> simp only [U] <;>
        linarith [norm_nonneg (mathieuCylExp 1 ((ν : ℂ) + ((-1 : ℤ) : ℂ)) h x),
          norm_nonneg (mathieuCylExp 1 ((ν : ℂ) + ((0 : ℤ) : ℂ)) h x),
          norm_nonneg (mathieuCylExp 1 ((ν : ℂ) + ((1 : ℤ) : ℂ)) h x),
          norm_nonneg (mathieuCylExp 2 ((ν : ℂ) + ((-1 : ℤ) : ℂ)) h x),
          norm_nonneg (mathieuCylExp 2 ((ν : ℂ) + ((0 : ℤ) : ℂ)) h x),
          norm_nonneg (mathieuCylExp 2 ((ν : ℂ) + ((1 : ℤ) : ℂ)) h x)]
    have t1 := fun α β => p3m_F_tail 1 le_rfl (by norm_num) ν hh hCc hK hc hC1 α β hu hCw
      (b1 (-1) (Or.inl rfl)) (b1 0 (Or.inr (Or.inl rfl))) (b1 1 (Or.inr (Or.inr rfl)))
    have t2 := fun α β => p3m_F_tail 2 (by norm_num) (by norm_num) ν hh hCc hK hc hC1 α β hu
      hCw (b2 (-1) (Or.inl rfl)) (b2 0 (Or.inr (Or.inl rfl))) (b2 1 (Or.inr (Or.inr rfl)))
    have hux : (h : ℂ) * Complex.exp (-(x : ℂ)) = (u : ℂ) := by simp [hudef, Complex.ofReal_exp]
    have hvx : (h : ℂ) * Complex.exp (x : ℂ) = (v : ℂ) := by simp [hvdef, Complex.ofReal_exp]
    have hmain : main x = (v : ℂ) / 2 *
      (p2m_fam c (p2m_Jz h x) (p2m_Cz 1 ν h x) (-n) n (-(-n)) *
          (p2m_fam c (p2m_Jz h x) (p2m_Cz 2 ν h x) (-n) (n - 1) (-(-n)) -
            p2m_fam c (p2m_Jz h x) (p2m_Cz 2 ν h x) (-n) (n + 1) (-(-n))) -
        (p2m_fam c (p2m_Jz h x) (p2m_Cz 1 ν h x) (-n) (n - 1) (-(-n)) -
            p2m_fam c (p2m_Jz h x) (p2m_Cz 1 ν h x) (-n) (n + 1) (-(-n))) *
          p2m_fam c (p2m_Jz h x) (p2m_Cz 2 ν h x) (-n) n (-(-n))) :=
      (p3m_main_term ν hh c n x).symm
    simp only [p3m_WF, p3m_D, hux, hvx, hmain]
    set UU := U x
    obtain ⟨f1, g1⟩ := t1 (-n) n
    obtain ⟨f2, g2⟩ := t2 (-n) n
    obtain ⟨f1a, g1a⟩ := t1 (-n) (n - 1)
    obtain ⟨f1c, g1c⟩ := t1 (-n) (n + 1)
    obtain ⟨f2a, g2a⟩ := t2 (-n) (n - 1)
    obtain ⟨f2c, g2c⟩ := t2 (-n) (n + 1)
    have r1a := (t1 (-n - 1) n).1
    have r1c := (t1 (-n + 1) n).1
    have r2a := (t2 (-n - 1) n).1
    have r2c := (t2 (-n + 1) n).1
    have hB : 0 ≤ 2 * Λ * UU := by positivity
    have pa : 0 ≤ La * UU := by positivity
    have pb : 0 ≤ Lb * UU := by positivity
    have pc : 0 ≤ Lc * UU := by positivity
    have pau : 0 ≤ La * UU * u := by positivity
    have pbu : 0 ≤ Lb * UU * u := by positivity
    have pcu : 0 ≤ Lc * UU * u := by positivity
    have := p3m_assemble hu0 hu hv0 huv pa pb pc f1 g1 f2 g2 f1a g1a f1c g1c f2a g2a f2c g2c
      r1a r1c r2a r2c
    convert this using 2; ring
  have T3 : Tendsto (fun x : ℝ => p3m_WF ν h c n x - main x) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hbound T2
  simpa using T3.add T1

/-- **DLMF 28.20.21** (first identity): `𝒲{M^{(1)}_ν, M^{(2)}_ν} = 2/π`, real `ν`, `h > 0`. -/
theorem p3m_wronskian_one_two {ν h : ℝ} (hh : 0 < h) (z : ℂ) :
    m28c_wronskian (fun z => modMathieuM 1 ν z h) (fun z => modMathieuM 2 ν z h) z = 2 / π := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hadm := p1c_admissible_real' ν h
  obtain ⟨Cc, K, hCc, hK, hc⟩ := p2m_coeff_decay hadm hh'
  set c := mathieuMeCoeff (ν : ℂ) ((h : ℂ) ^ 2) with hcdef
  set n := modMathieuIndex (ν : ℂ) (h : ℂ) with hndef
  have hcn : c n ≠ 0 := by
    have hex := p3m_exists_coeff_ne_zero ν h
    have : n = hex.choose := by simp only [hndef, modMathieuIndex, hex, ↓reduceDIte]
    rw [this]; exact hex.choose_spec
  have hM : ∀ j, (fun z => modMathieuM j ν z h) = fun z => (c n)⁻¹ * p2m_F j ν h c (-n) n z :=
    fun j => p2m_modMathieuM_eq_F j ν h
  have hD : ∀ j, 1 ≤ j → j ≤ 4 → ∀ w,
      HasDerivAt (fun z => modMathieuM j ν z h) ((c n)⁻¹ * p3m_D j ν h c n w) w := by
    intro j hj₁ hj₄ w
    rw [hM j]
    exact (p2m_hasDerivAt_F j hj₁ hj₄ ν hh' hCc hK hc (-n) n w).const_mul _
  have hW : ∀ w, m28c_wronskian (fun z => modMathieuM 1 ν z h) (fun z => modMathieuM 2 ν z h) w =
      (c n)⁻¹ ^ 2 * p3m_WF ν h c n w := by
    intro w
    simp only [m28c_wronskian, (hD 1 le_rfl (by norm_num) w).deriv,
      (hD 2 (by norm_num) (by norm_num) w).deriv, p3m_WF]
    rw [congrFun (hM 1) w, congrFun (hM 2) w]
    ring
  have hs1 := p2m_isModMathieuSolution_modMathieuM 1 le_rfl (by norm_num) hadm hh'
  have hs2 := p2m_isModMathieuSolution_modMathieuM 2 (by norm_num) (by norm_num) hadm hh'
  have hconst : ∀ w, m28c_wronskian (fun z => modMathieuM 1 ν z h)
      (fun z => modMathieuM 2 ν z h) z =
      m28c_wronskian (fun z => modMathieuM 1 ν z h) (fun z => modMathieuM 2 ν z h) w := by
    have hd : ∀ w, HasDerivAt (m28c_wronskian (fun z => modMathieuM 1 ν z h)
        (fun z => modMathieuM 2 ν z h)) 0 w := by
      intro w
      have e : m28c_wronskian (fun z => modMathieuM 1 ν z h) (fun z => modMathieuM 2 ν z h) =
          fun w => modMathieuM 1 ν w h * deriv (fun z => modMathieuM 2 ν z h) w -
            deriv (fun z => modMathieuM 1 ν z h) w * modMathieuM 2 ν w h := rfl
      rw [e]
      have := ((hs1.differentiable w).hasDerivAt.mul (hs2.hasDerivAt_deriv w)).sub
        ((hs1.hasDerivAt_deriv w).mul (hs2.differentiable w).hasDerivAt)
      convert this using 1; ring
    exact fun w => is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
      (fun w => (hd w).deriv) z w
  have hci : (c n)⁻¹ ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero hcn)
  have hWF : ∀ x : ℝ, p3m_WF ν h c n x = p3m_WF ν h c n z := by
    intro x
    have := hconst x
    rw [hW, hW] at this
    exact (mul_left_cancel₀ hci this).symm
  have hlim := p3m_tendsto_WF (ν := ν) hh n
  have hlim' : Tendsto (fun x : ℝ => p3m_WF ν h c n x) atTop (𝓝 (p3m_WF ν h c n z)) :=
    tendsto_const_nhds.congr fun x => (hWF x).symm
  have heq := tendsto_nhds_unique hlim' hlim
  rw [hW, heq, ← hcdef]
  field_simp

end DLMF.Mathieu
