/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.ZeroCounts
public import DLMF.Legendre.Connections
public import DLMF.Legendre.IntegerTheory

/-!
# Real Legendre zero counts and interlacing

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; since 2026-10-22 every statement in this
file is proved (the 14.16 zero counts via the Sturm separation tools of
`DLMF.Legendre.ZeroCounts`). See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

attribute [local instance] Classical.propDecidable

/-- legendreIntegerPart. -/
@[dlmf 14.16.E1]
def legendreIntegerPart (μ : ℝ) : ℤ :=
  ⌊μ⌋

/-- legendreFractionalPart. -/
@[dlmf 14.16.E1]
def legendreFractionalPart (μ : ℝ) : ℝ :=
  μ-⌊μ⌋

/-- ferrersZeroSet. -/
def ferrersZeroSet (second : Bool) (ν μ : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Ioo (-1:ℝ) 1 ∧ (if second then ferrersQ ν μ x else ferrersP ν μ x)=0}

/-- Extra-zero cases in DLMF 14.16(ii), away from integer parameters. DLMF prints the first case
as `n > m, δν ≤ δμ`; together with its count case `n ≥ m, δν > δμ` this omits `n = m, δν ≤ δμ`,
where 𝖯^μ_ν has the extra zero (e.g. (ν, μ) = (1/4, 3/4), (1.2, 1.7), (0.3, 0.3): one zero each).
Corrected 2026-10-22 to `n ≥ m` (DLMF erratum). -/
def ferrersPExtraZero (ν μ : ℝ) : Bool :=
  decide (0 < μ ∧ ((⌊μ⌋ ≤ ⌊ν⌋ ∧ legendreFractionalPart ν ≤ legendreFractionalPart μ) ∨ (⌊ν⌋ < ⌊μ⌋ ∧ Even (⌊μ⌋-⌊ν⌋))))

/-- The zero set of `𝖯^μ_ν` in `(-1, 1)` through the real part. -/
theorem lzero_zeroSet_P (ν μ : ℝ) : ferrersZeroSet false ν μ =
    {x | x ∈ Ioo (-1:ℝ) 1 ∧ (ferrersP ν μ x).re = 0} := by
  ext x
  simp only [ferrersZeroSet, Bool.false_eq_true, ite_false, mem_ofPred_eq]
  refine and_congr_right fun hx => ⟨fun h => by rw [h, zero_re], fun h => ?_⟩
  rw [(lzt_ferrersP_real_data ν μ hx).1, h, ofReal_zero]

/-- The nonpositive-order case, including integral parameters. -/
theorem ferrersP_nonpositive_order_zero_count {ν μ : ℝ} (hν : -1/2 ≤ ν) (hμ : μ ≤ 0) :
    Set.Finite (ferrersZeroSet false ν μ) ∧ (ferrersZeroSet false ν μ).ncard=(max (⌈ν-|μ|⌉:ℤ) 0).toNat := by
  have h := lzt_ferrersP_neg_order_zero_count (ν := ν) (m := -μ) (by linarith) hν
  simp only [neg_neg] at h
  rw [lzero_zeroSet_P, abs_of_nonpos hμ, sub_neg_eq_add]
  rw [sub_neg_eq_add] at h
  exact h

/-- `𝖯^m_j ≡ 0` on `(-1, 1)` for integers `0 ≤ j < m`. -/
theorem lzero_ferrersP_nat_lt {j m : ℕ} (hjm : j < m) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP (j : ℂ) (m : ℂ) x = 0 := by
  have htn : ‖((1:ℂ) - x) / 2‖ < 1 := by
    rw [show ((1:ℂ) - x) / 2 = (((1 - x) / 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_lt hjm
  unfold ferrersP
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ htn,
    show (1:ℂ) - ((j + N + 1 : ℕ) : ℂ) = -((j + N : ℕ) : ℂ) by push_cast; ring,
    regularized_at_neg_nat _ _ _ htn, poch_neg_nat_eq_zero (by omega)]
  simp


/-- The integral-order zero count, reduced to the order `-m` by DLMF 14.9.3. -/
theorem lzero_posInt_zero_count {ν : ℝ} (hν : -1/2 ≤ ν) (m : ℕ) (hnondeg : ∃ x ∈ Ioo (-1:ℝ) 1, ferrersP ν m x ≠ 0) :
    Set.Finite (ferrersZeroSet false ν m) ∧ (ferrersZeroSet false ν m).ncard=(max (⌈ν-m⌉:ℤ) 0).toNat := by
  by_cases h : ∀ n : ℕ, (ν:ℂ) - m + 1 ≠ -n
  · have hG1 : Gamma ((ν:ℂ) - m + 1) ≠ 0 := Complex.Gamma_ne_zero h
    have hG2 : Gamma ((ν:ℂ) + m + 1) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
    have hset : ferrersZeroSet false ν m = ferrersZeroSet false ν (-(m:ℝ)) := by
      ext x
      simp only [ferrersZeroSet, Bool.false_eq_true, ite_false, mem_ofPred_eq]
      refine and_congr_right fun hx => ?_
      rw [show (((-(m:ℝ)):ℝ):ℂ) = -((m:ℕ):ℂ) by push_cast; ring,
        ferrersP_negative_integer_order (ν:ℂ) m h hx, Complex.ofReal_natCast]
      have hc : (-1:ℂ) ^ m * Gamma ((ν:ℂ) - m + 1) / Gamma ((ν:ℂ) + m + 1) ≠ 0 :=
        div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hG1) hG2
      rw [mul_eq_zero, or_iff_right hc]
    rw [hset]
    have := ferrersP_nonpositive_order_zero_count hν (show -(m:ℝ) ≤ 0 by simp)
    rwa [abs_neg, Nat.abs_cast] at this
  · push Not at h
    obtain ⟨n, hn⟩ := h
    have hre : ν = m - 1 - n := by
      have := congrArg Complex.re hn; simp at this; linarith
    have hmn : n + 1 ≤ m := by
      have : (n:ℝ) < m := by linarith
      exact_mod_cast this
    obtain ⟨x, hx, hne⟩ := hnondeg
    exfalso
    apply hne
    have hj : (ν:ℂ) = ((m - 1 - n : ℕ) : ℂ) := by
      rw [hre]; push_cast [Nat.cast_sub (show n ≤ m - 1 by omega), Nat.cast_sub (show 1 ≤ m by omega)]
      ring
    rw [hj]
    exact lzero_ferrersP_nat_lt (by omega) hx



/-- Integer-degree case excludes the identically zero solution when integral order exceeds degree. -/
theorem ferrersP_nat_degree_zero_count (n : ℕ) (μ : ℝ) (hnondeg : ∃ x ∈ Ioo (-1:ℝ) 1, ferrersP n μ x ≠ 0) :
    Set.Finite (ferrersZeroSet false n μ) ∧ (ferrersZeroSet false n μ).ncard=(max (⌈(n:ℝ)-|μ|⌉:ℤ) 0).toNat := by
  have hn : (-1/2 : ℝ) ≤ n := by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  rcases le_or_gt μ 0 with hμ | hμ
  · exact ferrersP_nonpositive_order_zero_count hn hμ
  rw [abs_of_pos hμ]
  by_cases hint : ∃ m : ℕ, μ = m
  · obtain ⟨m, rfl⟩ := hint
    refine lzero_posInt_zero_count hn m ?_
    obtain ⟨x, hx, hne⟩ := hnondeg
    exact ⟨x, hx, by simpa [Complex.ofReal_natCast] using hne⟩
  push Not at hint
  have hnint : ∀ k : ℤ, μ ≠ k := fun k hk => by
    have hk0 : 0 ≤ k := by
      by_contra h; push Not at h
      have : (k:ℝ) < 0 := by exact_mod_cast h
      linarith
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    exact hint m (by simpa using hk)
  have hplus : LegendreQRegular ((n:ℝ):ℂ) (μ:ℂ) := fun k hk => by
    have := congrArg Complex.re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hminus : LegendreQRegular ((n:ℝ):ℂ) (-(μ:ℂ)) := fun k hk => by
    have := congrArg Complex.re hk; simp at this
    exact hnint (n + k + 1) (by push_cast; linarith)
  have hA : Complex.sin ((((n:ℝ):ℂ) - μ) * π) / Gamma (((n:ℝ):ℂ) + μ + 1) ≠ 0 := by
    refine div_ne_zero (fun h0 => ?_) (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h0
    have hk' : (((n:ℝ) - μ : ℝ) : ℂ) = (k : ℂ) := by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast
      exact mul_right_cancel₀ hπ hk
    have : (n:ℝ) - μ = k := by exact_mod_cast hk'
    exact hnint (n - k) (by push_cast; linarith)
  have hB : Complex.sin ((μ:ℂ) * π) / Gamma (((n:ℝ):ℂ) - μ + 1) ≠ 0 := by
    refine div_ne_zero (fun h0 => ?_) (Complex.Gamma_ne_zero fun k hk => ?_)
    · obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h0
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have : (μ : ℂ) = k := mul_right_cancel₀ hπ hk
      exact hnint k (by exact_mod_cast this)
    · have := congrArg Complex.re hk; simp at this
      exact hnint (n + k + 1) (by push_cast; linarith)
  have hiff : ∀ x ∈ Ioo (-1:ℝ) 1, ferrersP ((n:ℝ):ℂ) (μ:ℂ) x = 0 ↔
      ferrersP ((n:ℝ):ℂ) ((-μ:ℝ):ℂ) (-x) = 0 := by
    intro x hx
    have h7 := ferrers_connection_7 ((n:ℝ):ℂ) (μ:ℂ) hplus hminus hx
    rw [show ((n:ℝ):ℂ) * π = (n:ℂ) * π by push_cast; ring, Complex.sin_nat_mul_pi, zero_div,
      zero_mul, zero_sub] at h7
    rw [show ((-μ:ℝ):ℂ) = -(μ:ℂ) by push_cast; ring]
    constructor
    · intro h0
      rw [h0, mul_zero, eq_comm, neg_eq_zero] at h7
      exact (mul_eq_zero.mp h7).resolve_left hB
    · intro h0
      rw [h0, mul_zero, neg_zero] at h7
      exact (mul_eq_zero.mp h7).resolve_left hA
  have hset : ferrersZeroSet false n μ = (fun x => -x) '' ferrersZeroSet false n (-μ) := by
    ext x
    simp only [ferrersZeroSet, Bool.false_eq_true, ite_false, mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨hx, h0⟩
      refine ⟨-x, ⟨⟨by linarith [hx.2], by linarith [hx.1]⟩, (hiff x hx).1 h0⟩, neg_neg x⟩
    · rintro ⟨y, ⟨hy, h0⟩, rfl⟩
      have hy' : -y ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
      refine ⟨hy', (hiff (-y) hy').2 ?_⟩
      rwa [neg_neg]
  have h := ferrersP_nonpositive_order_zero_count hn (show -μ ≤ 0 by linarith)
  rw [abs_neg, abs_of_pos hμ] at h
  rw [hset, ncard_image_of_injective _ neg_injective]
  exact ⟨h.1.image _, h.2⟩


/-- Real form of a Wronskian identity `W{F, G} = c/(1-x²)` for real-valued `F`, `G`. -/
theorem lzero_real_wronskian {F G : ℝ → ℂ} {f f' g g' : ℝ → ℝ} {x c : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) (hF : F x = f x) (hF' : deriv F x = f' x) (hG : G x = g x)
    (hG' : deriv G x = g' x) (hW : ferrersWronskian F G x = (c : ℂ) / (1 - (x : ℂ) ^ 2)) :
    (1 - x ^ 2) * (f x * g' x - g x * f' x) = c := by
  unfold ferrersWronskian at hW
  rw [hF, hF', hG, hG', show (1 - (x:ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring] at hW
  have h : f x * g' x - g x * f' x = c / (1 - x ^ 2) := by exact_mod_cast hW
  have hne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [h]; field_simp

/-- The real data of `x ↦ 𝖯^{-μ}_ν(-x)`. -/
theorem lzero_reflect_data (ν μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (fun t => ferrersP ν (-μ:ℝ) (-t)) x = ((ferrersP ν (-μ:ℝ) (-x)).re : ℂ) ∧
      deriv (fun t => ferrersP ν (-μ:ℝ) (-t)) x =
        ((-(deriv (ferrersP ν (-μ:ℝ)) (-x)).re : ℝ) : ℂ) := by
  have hx' : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  obtain ⟨e0, e1⟩ := lzt_ferrersP_real_data ν (-μ) hx'
  refine ⟨e0, ?_⟩
  rw [deriv_comp_neg, e1]; simp

/-- The sign of `sin(xπ)` for nonintegral `x` is `(-1)^⌊x⌋`. -/
theorem lzero_sin_sign {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : 0 < (-1:ℝ) ^ ⌊x⌋ * Real.sin (x * π) := by
  have hd : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (fun h => hx ⌊x⌋ (by
    rw [Int.fract] at h; linarith))
  have hd1 : Int.fract x < 1 := Int.fract_lt_one x
  have e : x * π = Int.fract x * π + ⌊x⌋ * π := by rw [Int.fract]; ring
  rw [e, Real.sin_add_int_mul_pi, ← mul_assoc, ← zpow_add₀ (by norm_num : (-1:ℝ) ≠ 0),
    ← two_mul, zpow_mul]
  norm_num
  exact Real.sin_pos_of_pos_of_lt_pi (mul_pos hd Real.pi_pos) (by nlinarith [Real.pi_pos])

/-- The extra-zero rule of DLMF 14.16(ii) as a parity condition. -/
theorem lzero_extra_iff {ν μ : ℝ} (hνn : ∀ n : ℤ, ν ≠ n) (hμn : ∀ n : ℤ, μ ≠ n) (hμ : 0 < μ) :
    ferrersPExtraZero ν μ = true ↔ Even (max ⌈ν - μ⌉ 0 + ⌊μ⌋ + ⌊ν⌋) := by
  have ha0 : 0 < ν - ⌊ν⌋ := lt_of_le_of_ne (by linarith [Int.floor_le ν])
    (fun h => hνn ⌊ν⌋ (by linarith))
  have ha1 : ν - ⌊ν⌋ < 1 := by linarith [Int.lt_floor_add_one ν]
  have hb0 : 0 < μ - ⌊μ⌋ := lt_of_le_of_ne (by linarith [Int.floor_le μ])
    (fun h => hμn ⌊μ⌋ (by linarith))
  have hb1 : μ - ⌊μ⌋ < 1 := by linarith [Int.lt_floor_add_one μ]
  simp only [ferrersPExtraZero, legendreFractionalPart, decide_eq_true_eq, hμ, true_and]
  generalize ⌊ν⌋ = n at *
  generalize ⌊μ⌋ = m at *
  rcases le_or_gt m n with hmn | hnm
  · by_cases hab : ν - n ≤ μ - m
    · have hc : ⌈ν - μ⌉ = n - m := by
        rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
      rw [hc, max_eq_left (by omega)]
      simp only [hmn, hab, and_self, true_or, true_iff, Int.even_iff]
      omega
    · push Not at hab
      have hc : ⌈ν - μ⌉ = n - m + 1 := by
        rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
      rw [hc, max_eq_left (by omega)]
      have : ¬ (n < m) := not_lt.mpr hmn
      simp only [not_le.mpr hab, and_false, this, false_and, or_false, false_iff, Int.even_iff]
      omega
  · have hneg : ν - μ < 0 := by
      have h1 : (n:ℝ) + 1 ≤ m := by exact_mod_cast hnm
      linarith
    have hc : ⌈ν - μ⌉ ≤ 0 := Int.ceil_le.mpr (by push_cast; linarith)
    rw [max_eq_right hc]
    simp only [not_le.mpr hnm, false_and, false_or, hnm, true_and, Int.even_iff]
    omega

/-- Nonintegral parameter zero count from DLMF 14.16(ii). -/
theorem ferrersP_zero_count {ν μ : ℝ} (hν : -1/2 ≤ ν) (hνn : ∀ n : ℤ, ν ≠ n) (hμn : ∀ n : ℤ, μ ≠ n) (hnondeg : ∃ x ∈ Ioo (-1:ℝ) 1, ferrersP ν μ x ≠ 0) :
    Set.Finite (ferrersZeroSet false ν μ) ∧ (ferrersZeroSet false ν μ).ncard=(max (⌈ν-|μ|⌉:ℤ) 0).toNat+(if ferrersPExtraZero ν μ then 1 else 0) := by
  rcases le_or_gt μ 0 with hμ | hμ
  · have h := ferrersP_nonpositive_order_zero_count hν hμ
    have : ferrersPExtraZero ν μ = false := by simp [ferrersPExtraZero, not_lt.mpr hμ]
    rw [this]; simpa using h
  rw [abs_of_pos hμ, lzero_zeroSet_P]
  set y : ℝ → ℝ := fun x => (ferrersP ν μ x).re with hy
  set yd : ℝ → ℝ := fun x => (deriv (ferrersP ν μ) x).re with hyd
  set u : ℝ → ℝ := fun x => (ferrersP ν (-μ:ℝ) x).re
  set u' : ℝ → ℝ := fun x => (deriv (ferrersP ν (-μ:ℝ)) x).re
  have hsμ := lzero_sin_sign hμn
  have hsν := lzero_sin_sign hνn
  have hsμ0 : Real.sin (μ * π) ≠ 0 := fun h => by rw [h, mul_zero] at hsμ; exact lt_irrefl _ hsμ
  have hsν0 : Real.sin (ν * π) ≠ 0 := fun h => by rw [h, mul_zero] at hsν; exact lt_irrefl _ hsν
  have hc₁ : 2 * Real.sin (μ * π) / π ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hsμ0) Real.pi_ne_zero
  have hc₂ : 2 * Real.sin (ν * π) / π ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hsν0) Real.pi_ne_zero
  have hW₁ : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * (u x * yd x - y x * u' x) =
      2 * Real.sin (μ * π) / π := fun x hx => by
    refine lzero_real_wronskian hx (lzt_ferrersP_real_data ν (-μ) hx).1
      (lzt_ferrersP_real_data ν (-μ) hx).2 (lzt_ferrersP_real_data ν μ hx).1 (lzt_ferrersP_real_data ν μ hx).2 ?_
    have h := ferrers_wronskian_7 (ν:ℂ) (μ:ℂ) hx
    rw [show -(μ:ℂ) = ((-μ:ℝ):ℂ) by push_cast; ring] at h
    rw [h]; push_cast; rw [div_div]
  have hW₂ : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * (u (-x) * yd x -
      y x * -u' (-x)) = 2 * Real.sin (ν * π) / π := fun x hx => by
    refine lzero_real_wronskian (f := fun t => u (-t)) (f' := fun t => -u' (-t)) hx
      (lzero_reflect_data ν μ hx).1 (lzero_reflect_data ν μ hx).2
      (lzt_ferrersP_real_data ν μ hx).1 (lzt_ferrersP_real_data ν μ hx).2 ?_
    have h := lzc_wronskian_reflect_P (ν:ℂ) (μ:ℂ) hx
    rw [show -(μ:ℂ) = ((-μ:ℝ):ℂ) by push_cast; ring] at h
    rw [h]; push_cast; rw [div_div]
  have hfd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt y (yd x) x :=
    fun x hx => (lzt_ferrersP_sol ν μ hx).1
  have hsimp : ∀ x ∈ Ioo (-1:ℝ) 1, y x = 0 → yd x ≠ 0 := fun x hx h0 h1 => by
    have := hW₁ x hx; rw [h0, h1] at this; simp at this; exact hc₁ this.symm
  obtain ⟨hfin, hlo, hhi⟩ := lzc_ferrers_count_bounds hμ.le hν hfd hc₁ hW₁
  have hpar := lzc_ferrers_parity hμ.le hfd hsimp hfin hc₁ hc₂ hW₁ hW₂
  refine ⟨hfin, ?_⟩
  set n := {x | x ∈ Ioo (-1:ℝ) 1 ∧ y x = 0}.ncard
  have hN : ((max ⌈ν - μ⌉ 0).toNat : ℤ) = max ⌈ν - μ⌉ 0 := Int.toNat_of_nonneg (le_max_right _ _)
  set N := (max ⌈ν - μ⌉ 0).toNat
  -- the parity: `n + ⌊μ⌋ + ⌊ν⌋` is odd
  have hodd : Odd ((n : ℤ) + ⌊μ⌋ + ⌊ν⌋) := by
    rcases Int.even_or_odd ((n : ℤ) + ⌊μ⌋ + ⌊ν⌋) with he | ho
    · exfalso
      have h1 := he.neg_one_zpow (α := ℝ)
      rw [zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_natCast] at h1
      have hπ : 0 < π := Real.pi_pos
      have hX : 0 < -(Real.sin (μ * π) * Real.sin (ν * π) * (-1) ^ n) := by
        have e : -(2 * Real.sin (μ * π) / π * (2 * Real.sin (ν * π) / π)) * (-1) ^ n =
            4 / π ^ 2 * -(Real.sin (μ * π) * Real.sin (ν * π) * (-1) ^ n) := by
          field_simp; ring
        rw [e] at hpar
        exact pos_of_mul_pos_right hpar (by positivity)
      have hsq : ((-1:ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have key : (-1:ℝ) ^ n * (-1) ^ ⌊μ⌋ * (-1) ^ ⌊ν⌋ *
          -(Real.sin (μ * π) * Real.sin (ν * π) * (-1) ^ n) =
          -(((-1) ^ ⌊μ⌋ * Real.sin (μ * π)) * ((-1) ^ ⌊ν⌋ * Real.sin (ν * π))) * ((-1:ℝ) ^ n) ^ 2 := by
        ring
      rw [hsq, mul_one, h1, one_mul] at key
      have := mul_pos hsμ hsν
      linarith
    · exact ho
  have hE := lzero_extra_iff hνn hμn hμ
  by_cases hx : ferrersPExtraZero ν μ = true
  · simp only [hx, ↓reduceIte]
    change n = N + 1
    have he := hE.mp hx
    rw [← hN] at he
    rw [Int.even_iff] at he
    rw [Int.odd_iff] at hodd
    omega
  · simp only [Bool.not_eq_true] at hx
    simp only [hx, Bool.false_eq_true, ↓reduceIte]
    change n = N + 0
    have he : ¬ Even ((N : ℤ) + ⌊μ⌋ + ⌊ν⌋) := by
      rw [hN]; exact fun h => by have := hE.mpr h; rw [hx] at this; exact Bool.false_ne_true this
    rw [Int.even_iff] at he
    rw [Int.odd_iff] at hodd
    omega


/-! ### Real Ferrers solutions, their Wronskian, and the zeros of `𝖰_n`

On `(-1, 1)` the Ferrers functions of real parameters are real. Their Wronskian
`Γ(ν+μ+1)/(Γ(ν-μ+1)(1-x²))` (DLMF 14.2.4) has constant sign, which gives the interlacing of
zeros (`ODE.sturmCount_existsUnique_zero_between`). For `𝖰_n` the ratio `𝖰_n/𝖯_n` has
derivative at least `1/(2(1∓x))` because `|𝖯_n| ≤ 1`, so it is unbounded near `±1`, which
produces one zero next to each end.
-/

theorem lzero_isSol_P (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersP ν μ) :=
  ((ferrersEven_isFerrersSolution ν μ).add_smul (ferrersOdd_isFerrersSolution ν μ) _ _).congr
    (ferrersP_eqOn_even_odd ν μ).symm

theorem lzero_isSol_Q (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersQ ν μ) :=
  ((ferrersEven_isFerrersSolution ν μ).add_smul (ferrersOdd_isFerrersSolution ν μ) _ _).congr
    (ferrersQ_eqOn_even_odd ν μ).symm

/-- A real-valued function `f : ℝ → ℂ` on an open set has real derivative there. -/
theorem lzero_hasDerivAt_re {f : ℝ → ℂ} {x : ℝ} (hd : DifferentiableAt ℝ f x)
    (hreal : ∀ᶠ y in 𝓝 x, (f y).im = 0) :
    HasDerivAt (fun y => (f y).re) (deriv f x).re x ∧ (deriv f x).im = 0 ∧
      f x = ((f x).re : ℂ) ∧ deriv f x = ((deriv f x).re : ℂ) := by
  have h := hd.hasDerivAt
  have hre : HasDerivAt (fun y => (f y).re) (deriv f x).re x := by
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
    simp only [Function.comp_def, Complex.reCLM_apply] at h1
    exact h1
  have him : HasDerivAt (fun y => (f y).im) (deriv f x).im x := by
    have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h
    simp only [Function.comp_def, Complex.imCLM_apply] at h1
    exact h1
  have him0 : HasDerivAt (fun y => (f y).im) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq (hreal.mono fun y hy => hy)
  have h0 : (deriv f x).im = 0 := him.unique him0
  refine ⟨hre, h0, Complex.ext (by simp) (by simpa using hreal.self_of_nhds), Complex.ext (by simp) (by simp [h0])⟩

/-- The real part of `𝖯^μ_ν` on `(-1, 1)`. -/
def lzero_p (ν μ : ℝ) (x : ℝ) : ℝ := (ferrersP ν μ x).re
/-- The real part of the derivative of `𝖯^μ_ν`. -/
def lzero_p' (ν μ : ℝ) (x : ℝ) : ℝ := (deriv (ferrersP ν μ) x).re
/-- The real part of `𝖰^μ_ν` on `(-1, 1)`. -/
def lzero_q (ν μ : ℝ) (x : ℝ) : ℝ := (ferrersQ ν μ x).re
/-- The real part of the derivative of `𝖰^μ_ν`. -/
def lzero_q' (ν μ : ℝ) (x : ℝ) : ℝ := (deriv (ferrersQ ν μ) x).re

theorem lzero_evIoo {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : ∀ᶠ y in 𝓝 x, y ∈ Ioo (-1:ℝ) 1 :=
  Ioo_mem_nhds hx.1 hx.2

theorem lzero_P_data (ν μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (lzero_p ν μ) (lzero_p' ν μ x) x ∧
      ferrersP ν μ x = (lzero_p ν μ x : ℂ) ∧ deriv (ferrersP ν μ) x = (lzero_p' ν μ x : ℂ) := by
  obtain ⟨h1, -, h3, h4⟩ := lzero_hasDerivAt_re ((lzero_isSol_P ν μ x hx).1)
    ((lzero_evIoo hx).mono fun y hy => ferrersP_real ν μ hy)
  exact ⟨h1, h3, h4⟩

theorem lzero_Q_data {ν μ : ℝ} (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (lzero_q ν μ) (lzero_q' ν μ x) x ∧
      ferrersQ ν μ x = (lzero_q ν μ x : ℂ) ∧ deriv (ferrersQ ν μ) x = (lzero_q' ν μ x : ℂ) := by
  obtain ⟨h1, -, h3, h4⟩ := lzero_hasDerivAt_re ((lzero_isSol_Q ν μ x hx).1)
    ((lzero_evIoo hx).mono fun y hy => ferrersQ_real ν μ hy hr)
  exact ⟨h1, h3, h4⟩

/-- The real Wronskian of `𝖯^μ_ν` and `𝖰^μ_ν` (DLMF 14.2.4). -/
theorem lzero_wronskian {ν μ : ℝ} (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    lzero_p ν μ x * lzero_q' ν μ x - lzero_q ν μ x * lzero_p' ν μ x =
      Real.Gamma (ν + μ + 1) / Real.Gamma (ν - μ + 1) / (1 - x ^ 2) := by
  have hW := ferrers_wronskian_4 ν μ hr hx
  unfold ferrersWronskian at hW
  rw [(lzero_P_data ν μ hx).2.1, (lzero_P_data ν μ hx).2.2, (lzero_Q_data hr hx).2.1,
    (lzero_Q_data hr hx).2.2,
    show (ν : ℂ) + μ + 1 = ((ν + μ + 1 : ℝ) : ℂ) by push_cast; ring,
    show (ν : ℂ) - μ + 1 = ((ν - μ + 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    show (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring] at hW
  rw [div_div]
  exact_mod_cast hW

section NatDegree

variable (n : ℕ)

theorem lzero_nat_regular : LegendreQRegular ((n : ℝ) : ℂ) ((0 : ℝ) : ℂ) := fun k h => by
  have := congrArg re h
  simp at this
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- The Wronskian of `P_n` and `Q_n` is `1/(1-x²)`. -/
theorem lzero_nat_wronskian {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    lzero_p n 0 x * lzero_q' n 0 x - lzero_q n 0 x * lzero_p' n 0 x = 1 / (1 - x ^ 2) := by
  rw [lzero_wronskian (lzero_nat_regular n) hx, add_zero, sub_zero,
    div_self (Real.Gamma_pos_of_pos (by positivity)).ne']

theorem lzero_nat_p_eq {t : ℝ} (ht : t ∈ Ioo (-1:ℝ) 1) :
    (lzero_p n 0 t : ℂ) = DLMF.OrthogonalPolynomials.legendrePolyP n t := by
  rw [← (lzero_P_data n 0 ht).2.1, ← ferrersP_nat_polynomial n ht]
  push_cast; rfl

theorem lzero_nat_p_abs_le {t : ℝ} (ht : t ∈ Ioo (-1:ℝ) 1) : |lzero_p n 0 t| ≤ 1 := by
  have h := DLMF.OrthogonalPolynomials.norm_legendrePolyP_le_one n
    (x := t) (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
  rwa [← lzero_nat_p_eq n ht, norm_real, Real.norm_eq_abs] at h

/-- The derivative of `Q_n / P_n` and its lower bounds near `±1`. -/
theorem lzero_nat_ratio {y : ℝ} (hy : y ∈ Ioo (-1:ℝ) 1) (hp : lzero_p n 0 y ≠ 0) :
    HasDerivAt (fun t => lzero_q n 0 t / lzero_p n 0 t)
      ((lzero_q' n 0 y * lzero_p n 0 y - lzero_q n 0 y * lzero_p' n 0 y) / lzero_p n 0 y ^ 2) y ∧
    1 / 2 / (1 - y) ≤
      (lzero_q' n 0 y * lzero_p n 0 y - lzero_q n 0 y * lzero_p' n 0 y) / lzero_p n 0 y ^ 2 ∧
    1 / 2 / (y - -1) ≤
      (lzero_q' n 0 y * lzero_p n 0 y - lzero_q n 0 y * lzero_p' n 0 y) / lzero_p n 0 y ^ 2 := by
  refine ⟨HasDerivAt.fun_div (lzero_Q_data (lzero_nat_regular n) hy).1 (lzero_P_data n 0 hy).1 hp,
    ?_⟩
  have hW := lzero_nat_wronskian n hy
  have e : lzero_q' n 0 y * lzero_p n 0 y - lzero_q n 0 y * lzero_p' n 0 y = 1 / (1 - y ^ 2) := by
    rw [← hW]; ring
  rw [e]
  have h1 : 0 < 1 - y := by linarith [hy.2]
  have h2 : 0 < 1 + y := by linarith [hy.1]
  have hp2 : 0 < lzero_p n 0 y ^ 2 := by positivity
  have hp1 : lzero_p n 0 y ^ 2 ≤ 1 := by
    have := lzero_nat_p_abs_le n hy
    nlinarith [abs_nonneg (lzero_p n 0 y), sq_abs (lzero_p n 0 y)]
  have hden : 0 < 1 - y ^ 2 := by nlinarith
  rw [div_div, div_div, show y - -1 = 1 + y by ring]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem lzero_nat_pos_right {c : ℝ} (hc : c ∈ Ioo (-1:ℝ) 1)
    (hne : ∀ t ∈ Ioo c 1, lzero_p n 0 t ≠ 0) :
    ∃ y ∈ Ioo c 1, 0 < lzero_q n 0 y / lzero_p n 0 y := by
  have hy₀ : (c + 1) / 2 < 1 := by linarith [hc.2]
  have hsub : ∀ y ∈ Ico ((c + 1) / 2) 1, y ∈ Ioo c 1 := fun y hy =>
    ⟨by linarith [hy.1, hc.2], hy.2⟩
  have hsub' : ∀ y ∈ Ico ((c + 1) / 2) 1, y ∈ Ioo (-1:ℝ) 1 := fun y hy =>
    ⟨by linarith [hy.1, hc.1, hc.2], hy.2⟩
  obtain ⟨y, hy, hy0⟩ := ODE.sturmCount_exists_pos_of_deriv_ge hy₀ (by norm_num : (0:ℝ) < 1 / 2)
    (fun y hy => (lzero_nat_ratio n (hsub' y hy) (hne y (hsub y hy))).1)
    (fun y hy => (lzero_nat_ratio n (hsub' y hy) (hne y (hsub y hy))).2.1)
  exact ⟨y, ⟨by linarith [hy.1, hc.2], hy.2⟩, hy0⟩

theorem lzero_nat_neg_left {d : ℝ} (hd : d ∈ Ioo (-1:ℝ) 1)
    (hne : ∀ t ∈ Ioo (-1) d, lzero_p n 0 t ≠ 0) :
    ∃ y ∈ Ioo (-1) d, lzero_q n 0 y / lzero_p n 0 y < 0 := by
  have hy₀ : -1 < (d - 1) / 2 := by linarith [hd.1]
  have hsub : ∀ y ∈ Ioc (-1) ((d - 1) / 2), y ∈ Ioo (-1) d := fun y hy =>
    ⟨hy.1, by linarith [hy.2, hd.1]⟩
  have hsub' : ∀ y ∈ Ioc (-1) ((d - 1) / 2), y ∈ Ioo (-1:ℝ) 1 := fun y hy =>
    ⟨hy.1, by linarith [hy.2, hd.1, hd.2]⟩
  obtain ⟨y, hy, hy0⟩ := ODE.sturmCount_exists_neg_of_deriv_ge hy₀ (by norm_num : (0:ℝ) < 1 / 2)
    (fun y hy => (lzero_nat_ratio n (hsub' y hy) (hne y (hsub y hy))).1)
    (fun y hy => (lzero_nat_ratio n (hsub' y hy) (hne y (hsub y hy))).2.2)
  exact ⟨y, ⟨hy.1, by linarith [hy.2, hd.1]⟩, hy0⟩

end NatDegree

/-- DLMF 14.16(ii): the n+1 zeros of Q_n. -/
theorem ferrersQ_nat_zero_count (n : ℕ) :
    Set.Finite (ferrersZeroSet true n 0) ∧ (ferrersZeroSet true n 0).ncard=n+1 := by
  obtain ⟨x, hxm, hxI, hxz⟩ := DLMF.OrthogonalPolynomials.legendrePolyP_zeros_Ioo n
  have hr := lzero_nat_regular n
  have hpz : ∀ t ∈ Ioo (-1:ℝ) 1, lzero_p n 0 t = 0 ↔ ∃ i, t = x i := by
    intro t ht
    rw [← ofReal_eq_zero, lzero_nat_p_eq n ht, hxz]
    simp only [ofReal_inj]
  have hW : ∀ t ∈ Ioo (-1:ℝ) 1,
      0 < lzero_p n 0 t * lzero_q' n 0 t - lzero_q n 0 t * lzero_p' n 0 t := fun t ht => by
    rw [lzero_nat_wronskian n ht]; exact one_div_pos.mpr (by nlinarith [ht.1, ht.2])
  have hqx : ∀ i, lzero_q n 0 (x i) ≠ 0 := by
    intro i h
    have := hW (x i) (hxI i)
    rw [(hpz _ (hxI i)).mpr ⟨i, rfl⟩, h] at this
    simp at this
  have hP : ∀ t ∈ Ioo (-1:ℝ) 1, HasDerivAt (lzero_p n 0) (lzero_p' n 0 t) t :=
    fun t ht => (lzero_P_data n 0 ht).1
  have hQ : ∀ t ∈ Ioo (-1:ℝ) 1, HasDerivAt (lzero_q n 0) (lzero_q' n 0 t) t :=
    fun t ht => (lzero_Q_data hr ht).1
  -- `p ≠ 0` between consecutive zeros
  have hgap : ∀ {a b : ℝ}, -1 ≤ a → b ≤ 1 → (∀ i, x i ∉ Ioo a b) →
      ∀ t ∈ Ioo a b, lzero_p n 0 t ≠ 0 := by
    intro a b ha hb hx t ht h0
    obtain ⟨i, rfl⟩ := (hpz t ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩).mp h0
    exact hx i ht
  let E : ℕ → ℝ := fun k => if k = 0 then -1 else if h : k - 1 < n then x ⟨k - 1, h⟩ else 1
  have E0 : E 0 = -1 := by simp [E]
  have Em : E (n + 1) = 1 := by simp [E]
  have Ek : ∀ k (hk : k < n), E (k + 1) = x ⟨k, hk⟩ := by intro k hk; simp [E, hk]
  have hset : ferrersZeroSet true n 0 =
      {y | y ∈ Ioo (E 0) (E (n + 1)) ∧ lzero_q n 0 y = 0} := by
    rw [E0, Em]
    ext y
    simp only [ferrersZeroSet, ite_true, mem_ofPred_eq]
    refine and_congr_right fun hy => ?_
    rw [(lzero_Q_data hr hy).2.1, ofReal_eq_zero]
  rw [hset]
  refine ODE.sturmCount_ncard_of_partition (P := fun y => lzero_q n 0 y = 0) ?_ ?_ ?_
  · intro k hk
    rcases k with _ | j
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [E0, Em]; norm_num
      · rw [E0, Ek 0 hn]; exact (hxI _).1
    · rw [Ek j (by omega)]
      rcases Nat.lt_or_ge (j + 1) n with h | h
      · rw [Ek (j + 1) h]; exact hxm (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j))
      · rw [show j + 1 + 1 = n + 1 by omega, Em]; exact (hxI _).2
  · intro k hk
    rcases k with _ | j
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [E0, show (0:ℕ) + 1 = 0 + 1 from rfl, Em]
        have hne := hgap le_rfl le_rfl fun i => i.elim0
        exact ODE.sturmCount_existsUnique_zero_of_signs hP hQ hW hne
          (by
            obtain ⟨y, hy, h⟩ := lzero_nat_neg_left 0 (d := 0) (by norm_num)
              fun t ht => hne t ⟨ht.1, ht.2.trans (by norm_num)⟩
            exact ⟨y, ⟨hy.1, hy.2.trans (by norm_num)⟩, h⟩)
          (by
            obtain ⟨y, hy, h⟩ := lzero_nat_pos_right 0 (c := 0) (by norm_num)
              fun t ht => hne t ⟨(by norm_num : (-1:ℝ) < 0).trans ht.1, ht.2⟩
            exact ⟨y, ⟨(by norm_num : (-1:ℝ) < 0).trans hy.1, hy.2⟩, h⟩)
      · rw [E0, Ek 0 hn]
        have hx0 := hxI ⟨0, hn⟩
        have hsub : Ioc (-1) (x ⟨0, hn⟩) ⊆ Ioo (-1:ℝ) 1 := fun t ht => ⟨ht.1, ht.2.trans_lt hx0.2⟩
        have hne := hgap le_rfl hx0.2.le fun i hi =>
          absurd (hxm.monotone (show (⟨0, hn⟩ : Fin n) ≤ i from Fin.le_def.mpr (Nat.zero_le _)))
            (not_le.mpr hi.2)
        exact ODE.sturmCount_existsUnique_zero_left (fun t ht => hP t (hsub ht))
          (fun t ht => hQ t (hsub ht)) (fun t ht => hW t (hsub ht))
          ((hpz _ hx0).mpr ⟨_, rfl⟩) hne (lzero_nat_neg_left n hx0 hne)
    · have hj : j < n := by omega
      rw [Ek j hj]
      have hxj := hxI ⟨j, hj⟩
      rcases Nat.lt_or_ge (j + 1) n with h | h
      · rw [Ek (j + 1) h]
        have hxj1 := hxI ⟨j + 1, h⟩
        have hlt : x ⟨j, hj⟩ < x ⟨j + 1, h⟩ := hxm (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j))
        have hsub : Icc (x ⟨j, hj⟩) (x ⟨j + 1, h⟩) ⊆ Ioo (-1:ℝ) 1 :=
          Icc_subset_Ioo hxj.1 hxj1.2
        refine ODE.sturmCount_existsUnique_zero_between hlt (fun t ht => hP t (hsub ht))
          (fun t ht => hQ t (hsub ht)) (fun t ht => hW t (hsub ht)) ((hpz _ hxj).mpr ⟨_, rfl⟩)
          ((hpz _ hxj1).mpr ⟨_, rfl⟩) (hgap hxj.1.le hxj1.2.le fun i hi => ?_)
        have h1 := hxm.lt_iff_lt.mp hi.1
        have h2 := hxm.lt_iff_lt.mp hi.2
        rw [Fin.lt_def] at h1 h2
        simp only at h1 h2
        omega
      · rw [show j + 1 + 1 = n + 1 by omega, Em]
        have hsub : Ico (x ⟨j, hj⟩) 1 ⊆ Ioo (-1:ℝ) 1 := fun t ht => ⟨hxj.1.trans_le ht.1, ht.2⟩
        have hne := hgap hxj.1.le le_rfl fun i hi => by
          have h1 := hxm.lt_iff_lt.mp hi.1
          rw [Fin.lt_def] at h1
          simp only at h1
          omega
        exact ODE.sturmCount_existsUnique_zero_right (fun t ht => hP t (hsub ht))
          (fun t ht => hQ t (hsub ht)) (fun t ht => hW t (hsub ht))
          ((hpz _ hxj).mpr ⟨_, rfl⟩) hne (lzero_nat_pos_right n hxj hne)
  · intro k hk0 hkm
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Ek j (by omega)]
    exact hqx _

/-- Separation of successive distinct zeros in both directions. -/
def InterlacesZeros (S T : Set ℝ) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, a < b → (¬∃ c ∈ S, a < c ∧ c < b) → ∃! c : ℝ, c ∈ T ∧ a < c ∧ c < b) ∧ (∀ a ∈ T, ∀ b ∈ T, a < b → (¬∃ c ∈ T, a < c ∧ c < b) → ∃! c : ℝ, c ∈ S ∧ a < c ∧ c < b)

/-- Interlacing on `(-1, 1)` from a positive Wronskian. -/
theorem lzero_interlace_of_wronskian {p p' q q' : ℝ → ℝ}
    (hp : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt p (p' x) x) (hq : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt q (q' x) x)
    (hw : ∀ x ∈ Ioo (-1:ℝ) 1, 0 < p x * q' x - q x * p' x) {S T : Set ℝ}
    (hS : ∀ x, x ∈ S ↔ x ∈ Ioo (-1:ℝ) 1 ∧ p x = 0) (hT : ∀ x, x ∈ T ↔ x ∈ Ioo (-1:ℝ) 1 ∧ q x = 0) :
    InterlacesZeros S T := by
  have step : ∀ {f f' g g' : ℝ → ℝ} {A B : Set ℝ},
      (∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt f (f' x) x) → (∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt g (g' x) x) →
      (∀ x ∈ Ioo (-1:ℝ) 1, 0 < f x * g' x - g x * f' x) →
      (∀ x, x ∈ A ↔ x ∈ Ioo (-1:ℝ) 1 ∧ f x = 0) → (∀ x, x ∈ B ↔ x ∈ Ioo (-1:ℝ) 1 ∧ g x = 0) →
      ∀ a ∈ A, ∀ b ∈ A, a < b → (¬∃ c ∈ A, a < c ∧ c < b) → ∃! c : ℝ, c ∈ B ∧ a < c ∧ c < b := by
    intro f f' g g' A B hf hg hfg hA hB a ha b hb hab hgap
    have ha' := (hA a).mp ha
    have hb' := (hA b).mp hb
    have hsub : Icc a b ⊆ Ioo (-1:ℝ) 1 := Icc_subset_Ioo ha'.1.1 hb'.1.2
    obtain ⟨e, ⟨he, he0⟩, huniq⟩ := ODE.sturmCount_existsUnique_zero_between hab
      (fun x hx => hf x (hsub hx)) (fun x hx => hg x (hsub hx)) (fun x hx => hfg x (hsub hx))
      ha'.2 hb'.2 (fun x hx h0 => hgap ⟨x, (hA x).mpr ⟨hsub (Ioo_subset_Icc_self hx), h0⟩,
        hx.1, hx.2⟩)
    refine ⟨e, ⟨(hB e).mpr ⟨hsub (Ioo_subset_Icc_self he), he0⟩, he.1, he.2⟩, ?_⟩
    rintro y ⟨hy, hy1, hy2⟩
    exact huniq y ⟨⟨hy1, hy2⟩, ((hB y).mp hy).2⟩
  refine ⟨step hp hq hw hS hT, step (f := q) (g := fun x => -p x) (g' := fun x => -p' x) hq
    (fun x hx => (hp x hx).neg) (fun x hx => by have := hw x hx; linarith) hT
    (fun x => by rw [hS x, neg_eq_zero])⟩

/-- The Wronskian must be nonzero; degenerate proportional solutions do not interlace. -/
theorem ferrersPQ_interlace {ν μ : ℝ} (hν : -1/2 ≤ ν) (hr : LegendreQRegular ν μ) (hind : Gamma (ν+μ+1)/Gamma (ν-μ+1) ≠ 0) :
    InterlacesZeros (ferrersZeroSet false ν μ) (ferrersZeroSet true ν μ) := by
  set G := Real.Gamma (ν + μ + 1) / Real.Gamma (ν - μ + 1)
  have hG : G ≠ 0 := by
    intro h
    apply hind
    rw [show (ν : ℂ) + μ + 1 = ((ν + μ + 1 : ℝ) : ℂ) by push_cast; ring,
      show (ν : ℂ) - μ + 1 = ((ν - μ + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← ofReal_div]
    exact_mod_cast h
  have hS : ∀ x, x ∈ ferrersZeroSet false ν μ ↔ x ∈ Ioo (-1:ℝ) 1 ∧ lzero_p ν μ x = 0 := by
    intro x
    simp only [ferrersZeroSet, Bool.false_eq_true, ite_false, mem_ofPred_eq]
    refine and_congr_right fun hx => ?_
    rw [(lzero_P_data ν μ hx).2.1, ofReal_eq_zero]
  have hT : ∀ x, x ∈ ferrersZeroSet true ν μ ↔ x ∈ Ioo (-1:ℝ) 1 ∧ lzero_q ν μ x = 0 := by
    intro x
    simp only [ferrersZeroSet, ite_true, mem_ofPred_eq]
    refine and_congr_right fun hx => ?_
    rw [(lzero_Q_data hr hx).2.1, ofReal_eq_zero]
  have hden : ∀ x ∈ Ioo (-1:ℝ) 1, 0 < 1 - x ^ 2 := fun x hx => by nlinarith [hx.1, hx.2]
  rcases hG.lt_or_gt with hneg | hpos
  · refine lzero_interlace_of_wronskian (q := fun x => -lzero_q ν μ x) (q' := fun x => -lzero_q' ν μ x)
      (fun x hx => (lzero_P_data ν μ hx).1) (fun x hx => (lzero_Q_data hr hx).1.neg)
      (fun x hx => ?_) hS (fun x => by rw [hT x, neg_eq_zero])
    have := lzero_wronskian hr hx
    have : G / (1 - x ^ 2) < 0 := div_neg_of_neg_of_pos hneg (hden x hx)
    linarith
  · refine lzero_interlace_of_wronskian (fun x hx => (lzero_P_data ν μ hx).1)
      (fun x hx => (lzero_Q_data hr hx).1) (fun x hx => ?_) hS hT
    rw [lzero_wronskian hr hx]
    exact div_pos hpos (hden x hx)

/-- Count range and parity in DLMF 14.16(ii), on the nondegenerate domain. The parity statement
fails for `μ < 0` (at ν = −0.369, μ = −0.206 both cosines are positive but 𝖰^μ_ν > 0 on (−1, 1)),
so it is asserted for `0 ≤ μ` only (corrected 2026-10-22; DLMF erratum). -/
theorem ferrersQ_zero_count_range {ν μ : ℝ} (hν : -1/2 ≤ ν) (hr : LegendreQRegular ν μ) (hind : Gamma (ν+μ+1)/Gamma (ν-μ+1) ≠ 0) :
    Set.Finite (ferrersZeroSet true ν μ) ∧ ∃ k : ℤ, k ∈ Finset.Icc (-1) 2 ∧ ((ferrersZeroSet true ν μ).ncard:ℤ)=max (⌈ν-|μ|⌉:ℤ) 0+k ∧ (0 ≤ μ → Real.cos (ν*π)*Real.cos (μ*π) < 0 → Even ((ferrersZeroSet true ν μ).ncard:ℤ)) ∧ (0 ≤ μ → 0 < Real.cos (ν*π)*Real.cos (μ*π) → Odd ((ferrersZeroSet true ν μ).ncard:ℤ)) := by
  set G := Real.Gamma (ν + μ + 1) / Real.Gamma (ν - μ + 1)
  have hG : G ≠ 0 := by
    intro h
    apply hind
    rw [show (ν : ℂ) + μ + 1 = ((ν + μ + 1 : ℝ) : ℂ) by push_cast; ring,
      show (ν : ℂ) - μ + 1 = ((ν - μ + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← ofReal_div]
    exact_mod_cast h
  have hden : ∀ x ∈ Ioo (-1:ℝ) 1, 0 < 1 - x ^ 2 := fun x hx => by nlinarith [hx.1, hx.2]
  have hW : ∀ x ∈ Ioo (-1:ℝ) 1, lzero_p ν μ x * lzero_q' ν μ x - lzero_q ν μ x * lzero_p' ν μ x ≠ 0 :=
    fun x hx => by rw [lzero_wronskian hr hx]; exact div_ne_zero hG (hden x hx).ne'
  have hZq : ferrersZeroSet true ν μ = {x | x ∈ Ioo (-1:ℝ) 1 ∧ lzero_q ν μ x = 0} := by
    ext x
    simp only [ferrersZeroSet, ite_true, mem_ofPred_eq]
    refine and_congr_right fun hx => ?_
    rw [(lzero_Q_data hr hx).2.1, ofReal_eq_zero]
  have hZp : ferrersZeroSet false ν μ = {x | x ∈ Ioo (-1:ℝ) 1 ∧ lzero_p ν μ x = 0} :=
    lzero_zeroSet_P ν μ
  have hsubI : ∀ {a b : ℝ}, a ∈ Ioo (-1:ℝ) 1 → b ∈ Ioo (-1:ℝ) 1 → Icc a b ⊆ Ioo (-1:ℝ) 1 :=
    fun ha hb => Icc_subset_Ioo ha.1 hb.2
  -- the zeros of `𝖯^μ_ν`
  have hP : (ferrersZeroSet false ν μ).Finite ∧
      (max ⌈ν - |μ|⌉ 0).toNat ≤ (ferrersZeroSet false ν μ).ncard ∧
      (ferrersZeroSet false ν μ).ncard ≤ (max ⌈ν - |μ|⌉ 0).toNat + 1 := by
    rcases le_or_gt μ 0 with hμ | hμ
    · obtain ⟨h1, h2⟩ := ferrersP_nonpositive_order_zero_count hν hμ
      exact ⟨h1, h2.ge, h2.le.trans (Nat.le_succ _)⟩
    by_cases hint : ∃ m : ℕ, μ = m
    · obtain ⟨m, rfl⟩ := hint
      have hnd : ∃ x ∈ Ioo (-1:ℝ) 1, ferrersP ν m x ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have h0 : (0:ℝ) ∈ Ioo (-1:ℝ) 1 := ⟨by norm_num, by norm_num⟩
        have hp0 : ∀ x ∈ Ioo (-1:ℝ) 1, lzero_p ν m x = 0 := fun x hx => by
          simp [lzero_p, hcon x hx]
        have hd0 : HasDerivAt (lzero_p ν m) 0 0 :=
          (hasDerivAt_const (0:ℝ) (0:ℝ)).congr_of_eventuallyEq
            (Filter.eventually_of_mem (Ioo_mem_nhds h0.1 h0.2) fun x hx => hp0 x hx)
        have := hW 0 h0
        rw [hp0 0 h0, (lzero_P_data ν m h0).1.unique hd0] at this
        simp at this
      have := lzero_posInt_zero_count hν m hnd
      rw [abs_of_pos hμ]
      exact ⟨this.1, this.2.ge, this.2.le.trans (Nat.le_succ _)⟩
    · push Not at hint
      have hsμ0 : Real.sin (μ * π) ≠ 0 := fun h => by
        obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
        have hk' : (k:ℝ) = μ := mul_right_cancel₀ Real.pi_ne_zero hk
        have hk0 : 0 ≤ k := by
          by_contra h'; push Not at h'
          have : (k:ℝ) < 0 := by exact_mod_cast h'
          linarith
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
        exact hint m (by rw [← hk']; push_cast; ring)
      have hc₁ : 2 * Real.sin (μ * π) / π ≠ 0 :=
        div_ne_zero (mul_ne_zero two_ne_zero hsμ0) Real.pi_ne_zero
      have hW₁ : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * ((ferrersP ν (-μ:ℝ) x).re * lzero_p' ν μ x -
          lzero_p ν μ x * (deriv (ferrersP ν (-μ:ℝ)) x).re) = 2 * Real.sin (μ * π) / π :=
        fun x hx => by
          refine lzero_real_wronskian (f := fun t => (ferrersP ν (-μ:ℝ) t).re)
            (f' := fun t => (deriv (ferrersP ν (-μ:ℝ)) t).re) hx (lzt_ferrersP_real_data ν (-μ) hx).1
            (lzt_ferrersP_real_data ν (-μ) hx).2 (lzero_P_data ν μ hx).2.1
            (lzero_P_data ν μ hx).2.2 ?_
          have h := ferrers_wronskian_7 (ν:ℂ) (μ:ℂ) hx
          rw [show -(μ:ℂ) = ((-μ:ℝ):ℂ) by push_cast; ring] at h
          rw [h]; push_cast; rw [div_div]
      have := lzc_ferrers_count_bounds hμ.le hν (fun x hx => (lzero_P_data ν μ hx).1) hc₁ hW₁
      rw [hZp, abs_of_pos hμ]
      exact this
  set N := (max ⌈ν - |μ|⌉ 0).toNat
  have hN : (N : ℤ) = max ⌈ν - |μ|⌉ 0 := Int.toNat_of_nonneg (le_max_right _ _)
  obtain ⟨hPfin, hPlo, hPhi⟩ := hP
  rw [hZp] at hPfin hPlo hPhi
  -- the zeros of `𝖰^μ_ν` are separated by those of `𝖯^μ_ν` and conversely
  obtain ⟨hQfin, hQhi⟩ := lzc_ncard_le_succ hPfin
    (T := {x | x ∈ Ioo (-1:ℝ) 1 ∧ lzero_q ν μ x = 0}) fun a ha b hb hab => by
      obtain ⟨e, he, he0⟩ := lzc_exists_zero_between (p := lzero_p ν μ) (q := lzero_q ν μ) hab
        (fun x hx => (lzero_P_data ν μ (hsubI ha.1 hb.1 hx)).1)
        (fun x hx => (lzero_Q_data hr (hsubI ha.1 hb.1 hx)).1)
        (fun x hx => hW x (hsubI ha.1 hb.1 hx)) ha.2 hb.2
      exact ⟨e, ⟨hsubI ha.1 hb.1 (Ioo_subset_Icc_self he), he0⟩, he.1, he.2⟩
  obtain ⟨-, hQlo⟩ := lzc_ncard_le_succ hQfin
    (T := {x | x ∈ Ioo (-1:ℝ) 1 ∧ lzero_p ν μ x = 0}) fun a ha b hb hab => by
      obtain ⟨e, he, he0⟩ := lzc_exists_zero_between (p := lzero_q ν μ) (q := lzero_p ν μ) hab
        (fun x hx => (lzero_Q_data hr (hsubI ha.1 hb.1 hx)).1)
        (fun x hx => (lzero_P_data ν μ (hsubI ha.1 hb.1 hx)).1)
        (fun x hx h0 => hW x (hsubI ha.1 hb.1 hx) (by linarith)) ha.2 hb.2
      exact ⟨e, ⟨hsubI ha.1 hb.1 (Ioo_subset_Icc_self he), he0⟩, he.1, he.2⟩
  rw [hZq]
  set n := {x | x ∈ Ioo (-1:ℝ) 1 ∧ lzero_q ν μ x = 0}.ncard
  refine ⟨hQfin, (n : ℤ) - N, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by rw [← hN]; ring, ?_⟩
  -- the parity, for `μ ≥ 0`
  have hpar : 0 ≤ μ → Real.cos (ν * π) * Real.cos (μ * π) ≠ 0 →
      0 < -(Real.cos (μ * π) * Real.cos (ν * π)) * (-1) ^ n := by
    intro hμ hcc
    have hc₁ : Real.cos (μ * π) ≠ 0 := right_ne_zero_of_mul hcc
    have hc₂ : Real.cos (ν * π) ≠ 0 := left_ne_zero_of_mul hcc
    have hW₁ : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * ((ferrersP ν (-μ:ℝ) x).re * lzero_q' ν μ x -
        lzero_q ν μ x * (deriv (ferrersP ν (-μ:ℝ)) x).re) = Real.cos (μ * π) := fun x hx => by
      refine lzero_real_wronskian (f := fun t => (ferrersP ν (-μ:ℝ) t).re)
        (f' := fun t => (deriv (ferrersP ν (-μ:ℝ)) t).re) hx (lzt_ferrersP_real_data ν (-μ) hx).1
        (lzt_ferrersP_real_data ν (-μ) hx).2 (lzero_Q_data hr hx).2.1 (lzero_Q_data hr hx).2.2 ?_
      have h := ferrers_wronskian_6 (ν:ℂ) (μ:ℂ) hr hx
      rw [show -(μ:ℂ) = ((-μ:ℝ):ℂ) by push_cast; ring] at h
      rw [h]; push_cast; rfl
    have hW₂ : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) * ((ferrersP ν (-μ:ℝ) (-x)).re * lzero_q' ν μ x -
        lzero_q ν μ x * -(deriv (ferrersP ν (-μ:ℝ)) (-x)).re) = Real.cos (ν * π) := fun x hx => by
      refine lzero_real_wronskian (f := fun t => (ferrersP ν (-μ:ℝ) (-t)).re)
        (f' := fun t => -(deriv (ferrersP ν (-μ:ℝ)) (-t)).re) hx
        (lzero_reflect_data ν μ hx).1 (lzero_reflect_data ν μ hx).2
        (lzero_Q_data hr hx).2.1 (lzero_Q_data hr hx).2.2 ?_
      have h := lzc_wronskian_reflect_Q (ν:ℂ) (μ:ℂ) hr hx
      rw [show -(μ:ℂ) = ((-μ:ℝ):ℂ) by push_cast; ring] at h
      rw [h]; push_cast; rfl
    exact lzc_ferrers_parity hμ (fun x hx => (lzero_Q_data hr hx).1)
      (fun x hx h0 h1 => hW x hx (by rw [h0, h1]; ring)) hQfin hc₁ hc₂ hW₁ hW₂
  refine ⟨fun hμ hneg => ?_, fun hμ hpos => ?_⟩
  · have h := hpar hμ hneg.ne
    rcases Nat.even_or_odd n with he | ho
    · exact_mod_cast he.natCast
    · rw [ho.neg_one_pow] at h; nlinarith
  · have h := hpar hμ hpos.ne'
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow] at h; nlinarith
    · exact_mod_cast ho.natCast

/-- associatedPOneZero. DLMF 14.16(iii) case (b) (`μ ≤ ν`, μ non-integer, ⌊μ⌋ odd) needs `μ > 0`:
for `μ < 0`, P^μ_ν > 0 on (1, ∞) (both the behaviour at `x = 1`, with factor `1/Γ(1−μ) > 0`, and the
leading term at ∞ are positive), e.g. at ν = 0.184, μ = −0.088 (corrected 2026-10-22; DLMF erratum). -/
def associatedPOneZero (ν μ : ℝ) : Prop :=
  (0 < μ ∧ ν < μ ∧ (∀ n : ℤ, μ ≠ n) ∧ Real.sin ((μ-ν)*π)*Real.sin (μ*π) < 0) ∨ (0 < μ ∧ μ ≤ ν ∧ (∀ n : ℤ, μ ≠ n) ∧ Odd (⌊μ⌋:ℤ))

/-- A complex sum of nonnegative real terms with positive leading term is nonzero. -/
theorem lzero_ne_zero_of_hasSum {f : ℕ → ℝ} {S : ℂ} (h : HasSum (fun k => (f k : ℂ)) S)
    (hf : ∀ k, 0 ≤ f k) (h0 : 0 < f 0) : S ≠ 0 := by
  have hr : HasSum f S.re := by simpa using Complex.reCLM.hasSum h
  intro hS
  rw [hS, zero_re] at hr
  have := le_hasSum hr 0 fun j _ => hf j
  linarith

/-- The regularized Gauss series is positive for positive parameters on `(0, 1)`. -/
theorem lzero_regularizedGaussHG_ne_zero {a b c w : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hw0 : 0 ≤ w) (hw1 : w < 1) : regularizedGaussHG a b c w ≠ 0 := by
  have hw : ‖(w : ℂ)‖ < 1 := by rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]; exact hw1
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw]
  have hG : ∀ n : ℕ, 0 < Real.Gamma (c + n) := fun n => Real.Gamma_pos_of_pos (by positivity)
  refine lzero_ne_zero_of_hasSum (f := fun n => (ascPochhammer ℝ n).eval a *
    (ascPochhammer ℝ n).eval b * w ^ n / n.factorial * (Real.Gamma (c + n))⁻¹)
    ((hasSum_regularizedGaussHGFun _ _ _ hw).congr_fun fun n => ?_) (fun n => ?_) ?_
  · rw [ascPochhammer_eval_ofReal, ascPochhammer_eval_ofReal,
      show (c : ℂ) + n = ((c + n : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  · have := ascPochhammer_pos n a ha
    have := ascPochhammer_pos n b hb
    have := hG n
    positivity
  · have := hG 0
    simp only [ascPochhammer_zero, Polynomial.eval_one, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, one_mul, Nat.cast_zero, add_zero]
    positivity

theorem lzero_olverQ_ne_zero_of_nonneg {ν μ : ℝ} (hν : -1 < ν) (hμ : 0 ≤ μ) {x : ℝ} (hx : 1 < x) :
    olverQ ν μ x ≠ 0 := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith)
  unfold olverQ legendreBranchPower
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2 : (2 : ℂ) ^ ((ν : ℂ) + 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hxp : (x : ℂ) ^ ((ν : ℂ) + μ + 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hw : (1 : ℂ) / (x : ℂ) ^ 2 = ((1 / x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hF := lzero_regularizedGaussHG_ne_zero (a := (ν + μ + 2) / 2) (b := (ν + μ + 1) / 2)
    (c := ν + 3 / 2) (w := 1 / x ^ 2) (by linarith) (by linarith) (by linarith) (by positivity)
    (by rw [div_lt_one (by positivity)]; nlinarith)
  push_cast at hF
  rw [hw]
  push_cast
  exact mul_ne_zero (div_ne_zero (mul_ne_zero hπ (exp_ne_zero _)) (mul_ne_zero h2 hxp)) hF

/-- DLMF 14.16(iii): no exterior zeros for degree greater than minus one. -/
theorem olverQ_no_exterior_zero {ν μ : ℝ} (hν : -1 < ν) {x : ℝ} (hx : 1 < x) :
    olverQ ν μ x ≠ 0 := by
  rcases le_or_gt 0 μ with hμ | hμ
  · exact lzero_olverQ_ne_zero_of_nonneg hν hμ hx
  · have hs : (x : ℂ) - 1 ∈ slitPlane := by
      rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_mem_slitPlane.mpr (by linarith)
    have h := associated_connection_14 ν (-μ : ℝ) hs
    rw [show -((-μ : ℝ) : ℂ) = (μ : ℂ) by push_cast; ring] at h
    rw [h]
    exact lzero_olverQ_ne_zero_of_nonneg hν (by linarith) hx

/-- A `C²` function on `[a, b]` vanishing at both ends, whose second derivative is positive at
any positive critical point, is nonpositive on `[a, b]`. -/
theorem lzero_nonpos_of_ode {g g' g'' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Icc a b, HasDerivAt g' (g'' x) x)
    (hode : ∀ x ∈ Icc a b, 0 < g x → g' x = 0 → 0 < g'' x) (ha : g a = 0) (hb : g b = 0) :
    ∀ x ∈ Icc a b, g x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, hgy⟩ := hcon
  have hc : ContinuousOn g (Icc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le) hc
  have hpos : 0 < g x0 := hgy.trans_le (hmax hy)
  have hxa : a < x0 := lt_of_le_of_ne hx0.1 (fun h => by rw [← h, ha] at hpos; exact lt_irrefl _ hpos)
  have hxb : x0 < b := lt_of_le_of_ne hx0.2 (fun h => by rw [h, hb] at hpos; exact lt_irrefl _ hpos)
  have hloc : IsLocalMax g x0 := hmax.isLocalMax (Icc_mem_nhds hxa hxb)
  have hd0 : g' x0 = 0 := hloc.hasDerivAt_eq_zero (hg x0 hx0)
  have hdd := hode x0 hx0 hpos hd0
  -- `g'` is positive just to the right of `x0`
  have hsl := hasDerivAt_iff_tendsto_slope.mp (hg' x0 hx0)
  have hev : ∀ᶠ x in 𝓝[>] x0, 0 < g' x := by
    have h1 : ∀ᶠ x in 𝓝[≠] x0, 0 < slope g' x0 x := hsl.eventually (lt_mem_nhds hdd)
    filter_upwards [nhdsWithin_mono _ (fun x (hx : x ∈ Ioi x0) => ne_of_gt hx) h1,
      self_mem_nhdsWithin] with x hx hx'
    rw [slope_def_field, hd0, sub_zero] at hx
    exact (div_pos_iff_of_pos_right (sub_pos.mpr hx')).mp hx
  obtain ⟨c, hc0, hcsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  set x := min ((x0 + c) / 2) ((x0 + b) / 2)
  have hx1 : x0 < x := lt_min (by linarith [hc0.out]) (by linarith)
  have hx2 : x < c := (min_le_left _ _).trans_lt (by linarith [hc0.out])
  have hx3 : x < b := (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' hx1
    (fun t ht => (hg t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt)
    (fun t ht => hg t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hgξ : 0 < g' ξ := hcsub ⟨hξ.1, hξ.2.trans hx2⟩
  rw [hξeq] at hgξ
  have : g x0 < g x := by
    have := (div_pos_iff_of_pos_right (sub_pos.mpr hx1)).mp hgξ; linarith
  exact absurd (hmax ⟨by linarith, hx3.le⟩) (not_le.mpr this)

theorem lzero_mem {x : ℝ} (hx : 1 < x) : (x : ℂ) ∈ {z : ℂ | z - 1 ∈ slitPlane} := by
  show (x : ℂ) - 1 ∈ slitPlane
  rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring]
  exact ofReal_mem_slitPlane.mpr (by linarith)

/-- The real ODE of `x ↦ Re 𝑸(x)` on `(1, ∞)`. -/
theorem lzero_real_ode (ν μ : ℝ) {x : ℝ} (hx : 1 < x) :
    let Q := olverQ ν μ
    HasDerivAt (fun t : ℝ => (Q t).re) (deriv Q x).re x ∧
      HasDerivAt (fun t : ℝ => (deriv Q t).re) (deriv (deriv Q) x).re x ∧
      (1 - x ^ 2) * (deriv (deriv Q) x).re - 2 * x * (deriv Q x).re +
        (ν * (ν + 1) - μ ^ 2 / (1 - x ^ 2)) * (Q x).re = 0 := by
  intro Q
  have hA := olverQ_analytic ν μ (x : ℂ) (lzero_mem hx)
  refine ⟨hA.differentiableAt.hasDerivAt.real_of_complex,
    hA.deriv.differentiableAt.hasDerivAt.real_of_complex, ?_⟩
  have h := olverQ_ode ν μ (z := (x : ℂ)) (lzero_mem hx)
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  have h' := congrArg re h
  rw [show (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show 2 * (x : ℂ) = ((2 * x : ℝ) : ℂ) by push_cast; ring,
    show ((ν : ℂ) * (ν + 1) - (μ : ℂ) ^ 2 / ((1 - x ^ 2 : ℝ) : ℂ)) =
      ((ν * (ν + 1) - μ ^ 2 / (1 - x ^ 2) : ℝ) : ℂ) by push_cast; ring] at h'
  simpa only [add_re, sub_re, re_ofReal_mul, zero_re] using h'

/-- At most one exterior zero; the identically zero regularized solution is excluded. -/
theorem olverQ_at_most_one_exterior_zero {ν μ : ℝ} (hν : ν < -1) (hnondeg : ∃ x : ℝ, 1 < x ∧ olverQ ν μ x ≠ 0) :
    ∀ x y : ℝ, 1 < x → 1 < y → olverQ ν μ x=0 → olverQ ν μ y=0 → x=y := by
  set Q := olverQ ν μ
  have hνν : 0 < ν * (ν + 1) := by nlinarith
  -- two zeros `a < b` force `Q = 0` on `[a, b]`
  have key : ∀ a b : ℝ, 1 < a → a < b → Q a = 0 → Q b = 0 → ∀ t ∈ Icc a b, Q t = 0 := by
    intro a b ha hab hQa hQb t ht
    have hI : ∀ s ∈ Icc a b, 1 < s := fun s hs => ha.trans_le hs.1
    have hode : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 → ∀ s ∈ Icc a b, 0 < σ * (Q s).re →
        σ * (deriv Q s).re = 0 → 0 < σ * (deriv (deriv Q) s).re := by
      intro σ hσ s hs hpos hd
      obtain ⟨-, -, he⟩ := lzero_real_ode ν μ (hI s hs)
      have hs1 : 1 - s ^ 2 < 0 := by nlinarith [hI s hs]
      have hq : 0 < ν * (ν + 1) - μ ^ 2 / (1 - s ^ 2) := by
        have : μ ^ 2 / (1 - s ^ 2) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hs1.le
        linarith
      have he' : (1 - s ^ 2) * (σ * (deriv (deriv Q) s).re) =
          2 * s * (σ * (deriv Q s).re) - (ν * (ν + 1) - μ ^ 2 / (1 - s ^ 2)) * (σ * (Q s).re) := by
        linear_combination σ * he
      rw [hd, mul_zero, zero_sub] at he'
      have : (1 - s ^ 2) * (σ * (deriv (deriv Q) s).re) < 0 := by
        rw [he']; exact neg_neg_of_pos (mul_pos hq hpos)
      by_contra hle
      push Not at hle
      nlinarith
    have hσ : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → σ * (Q t).re ≤ 0 := by
      intro σ hσs
      refine lzero_nonpos_of_ode (g := fun s => σ * (Q s).re) (g' := fun s => σ * (deriv Q s).re)
        (g'' := fun s => σ * (deriv (deriv Q) s).re) hab
        (fun s hs => (lzero_real_ode ν μ (hI s hs)).1.const_mul σ)
        (fun s hs => (lzero_real_ode ν μ (hI s hs)).2.1.const_mul σ)
        (hode σ hσs) (by simp [hQa]) (by simp [hQb]) t ht
    have h1 := hσ 1 (Or.inl rfl)
    have h2 := hσ (-1) (Or.inr rfl)
    have hre : (Q t).re = 0 := by linarith
    have him : (Q t).im = 0 := olverQ_real ν μ (hI t ht)
    exact Complex.ext hre him
  intro x y hx hy hQx hQy
  by_contra hxy
  wlog hlt : x < y generalizing x y
  · exact this y x hy hx hQy hQx (Ne.symm hxy) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hxy))
  obtain ⟨w, hw, hQw⟩ := hnondeg
  -- identity theorem on the slit domain
  set U := {z : ℂ | z - 1 ∈ slitPlane}
  have hU : IsPreconnected U := isPreconnected_sub_one_mem_slitPlane
  have hfreq : ∃ᶠ z in 𝓝[≠] (x : ℂ), Q z = 0 := by
    have ht : Tendsto (fun n : ℕ => ((x + (y - x) / (n + 2) : ℝ) : ℂ)) atTop (𝓝[≠] (x : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have : Tendsto (fun n : ℕ => x + (y - x) / ((n : ℝ) + 2)) atTop (𝓝 (x + 0)) :=
          tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
        rw [add_zero] at this
        exact (continuous_ofReal.tendsto _).comp this
      · simp only [mem_compl_iff, mem_singleton_iff, ofReal_inj]
        have : 0 < (y - x) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
        linarith
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    have hn : (y - x) / ((n : ℝ) + 2) ≤ y - x := div_le_self (by linarith) (by linarith)
    have hn0 : 0 < (y - x) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
    exact key x y hx hlt hQx hQy _ ⟨by linarith, by linarith⟩
  have hzero := (olverQ_analytic ν μ).eqOn_zero_of_preconnected_of_frequently_eq_zero hU
    (lzero_mem hx) hfreq
  exact hQw (hzero (lzero_mem hw))

/-! ### Exterior zeros of `P^μ_ν` (DLMF 14.16(iii)) -/

/-- A function with zero derivative on an interval is constant there. -/
theorem lzero_const_of_deriv_zero {r r' : ℝ → ℝ} {s : Set ℝ} (hs : s.OrdConnected)
    (hd : ∀ x ∈ s, HasDerivAt r (r' x) x) (h0 : ∀ x ∈ s, r' x = 0) {x y : ℝ} (hx : x ∈ s)
    (hy : y ∈ s) : r x = r y := by
  wlog hxy : x < y generalizing x y
  · rcases eq_or_lt_of_le (not_lt.mp hxy) with h | h
    · rw [h]
    · exact (this hy hx h).symm
  have hsub : Icc x y ⊆ s := hs.out hx hy
  obtain ⟨ξ, hξ, he⟩ := exists_hasDerivAt_eq_slope r r' hxy
    (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => hd t (hsub (Ioo_subset_Icc_self ht)))
  rw [h0 ξ (hsub (Ioo_subset_Icc_self hξ)), eq_comm, div_eq_zero_iff] at he
  rcases he with h | h
  · linarith
  · linarith

/-- On `(1, ∞)`: a function with `(x²-1)(v f' - f v') = c > 0` against a positive solution `v`
with `(x²-1)v² = O(x-1)` is negative near `1`. -/
theorem lzero_ext_neg_near_one {f f' v v' : ℝ → ℝ} {s K c : ℝ} (hs : 1 < s) (hK : 0 < K)
    (hc : 0 < c) (hfd : ∀ x ∈ Ioc 1 s, HasDerivAt f (f' x) x)
    (hvd : ∀ x ∈ Ioc 1 s, HasDerivAt v (v' x) x) (hv : ∀ x ∈ Ioc 1 s, 0 < v x)
    (hb : ∀ x ∈ Ioc 1 s, (x ^ 2 - 1) * v x ^ 2 ≤ K * (x - 1))
    (hW : ∀ x ∈ Ioc 1 s, (x ^ 2 - 1) * (v x * f' x - f x * v' x) = c) :
    ∃ t ∈ Ioo 1 s, ∀ x ∈ Ioo 1 t, f x < 0 := by
  have hp : ∀ x ∈ Ioc 1 s, 0 < x ^ 2 - 1 := fun x hx => by nlinarith [hx.1]
  have hD : ∀ x ∈ Ioc 1 s, 0 < v x * f' x - f x * v' x := fun x hx =>
    (mul_pos_iff_of_pos_left (hp x hx)).mp (by rw [hW x hx]; exact hc)
  have hder : ∀ x ∈ Ioc 1 s, HasDerivAt (fun t => f t / v t)
      ((f' x * v x - f x * v' x) / v x ^ 2) x := fun x hx =>
    (hfd x hx).fun_div (hvd x hx) (hv x hx).ne'
  obtain ⟨x0, hx0, h0⟩ := ODE.sturmCount_exists_neg_of_deriv_ge (r := fun t => f t / v t)
    (r' := fun x => (f' x * v x - f x * v' x) / v x ^ 2) (c := c / K) hs (div_pos hc hK) hder
    (fun x hx => by
      have hv2 := pow_pos (hv x hx) 2
      have h1x : 0 < x - 1 := by linarith [hx.1]
      rw [div_div, div_le_div_iff₀ (mul_pos hK h1x) hv2]
      have e : f' x * v x - f x * v' x = v x * f' x - f x * v' x := by ring
      rw [e]
      have := hb x hx
      have hWx := hW x hx
      nlinarith [mul_le_mul_of_nonneg_left this (hD x hx).le])
  refine ⟨x0, hx0, fun x hx => ?_⟩
  have hmono : StrictMonoOn (fun t => f t / v t) (Ioc 1 s) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc 1 s)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      have htI : t ∈ Ioc 1 s := Ioo_subset_Ioc_self ht
      rw [(hder t htI).deriv]
      exact div_pos (by linarith [hD t htI]) (pow_pos (hv t htI) 2)
  have hxI : x ∈ Ioc 1 s := ⟨hx.1, hx.2.le.trans hx0.2.le⟩
  have := hmono hxI ⟨hx0.1, hx0.2.le⟩ hx.2
  have h2 : f x / v x < 0 := lt_trans this h0
  have h3 := mul_neg_of_neg_of_pos h2 (hv x hxI)
  rwa [div_mul_cancel₀ _ (hv x hxI).ne'] at h3

/-- On `(1, ∞)`: a function with `(x²-1)(u f' - f u') = c > 0` against a positive solution `u`
with `(x²-1)u² = O(x)` is eventually positive. -/
theorem lzero_ext_pos_atTop {f f' u u' : ℝ → ℝ} {X K c : ℝ} (hX : 1 < X) (hK : 0 < K)
    (hc : 0 < c) (hfd : ∀ x ∈ Ici X, HasDerivAt f (f' x) x)
    (hud : ∀ x ∈ Ici X, HasDerivAt u (u' x) x) (hu : ∀ x ∈ Ici X, 0 < u x)
    (hb : ∀ x ∈ Ici X, (x ^ 2 - 1) * u x ^ 2 ≤ K * x)
    (hW : ∀ x ∈ Ici X, (x ^ 2 - 1) * (u x * f' x - f x * u' x) = c) :
    ∃ T, ∀ x, T < x → 0 < f x := by
  have hX0 : 0 < X := by linarith
  have hp : ∀ x ∈ Ici X, 0 < x ^ 2 - 1 := fun x hx => by
    have : X ≤ x := hx; nlinarith
  have hD : ∀ x ∈ Ici X, 0 < u x * f' x - f x * u' x := fun x hx =>
    (mul_pos_iff_of_pos_left (hp x hx)).mp (by rw [hW x hx]; exact hc)
  set r : ℝ → ℝ := fun t => f t / u t - c / K * Real.log t
  have hder : ∀ x ∈ Ici X, HasDerivAt r
      ((f' x * u x - f x * u' x) / u x ^ 2 - c / K * x⁻¹) x := fun x hx => by
    have : (0:ℝ) < x := lt_of_lt_of_le hX0 hx
    exact ((hfd x hx).fun_div (hud x hx) (hu x hx).ne').sub
      ((Real.hasDerivAt_log this.ne').const_mul _)
  have hge : ∀ x ∈ Ici X, 0 ≤ (f' x * u x - f x * u' x) / u x ^ 2 - c / K * x⁻¹ := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hX0 hx
    have hu2 := pow_pos (hu x hx) 2
    rw [sub_nonneg, show c / K * x⁻¹ = c / (K * x) by field_simp, div_le_div_iff₀
      (mul_pos hK hx0) hu2]
    have e : f' x * u x - f x * u' x = u x * f' x - f x * u' x := by ring
    rw [e]
    have := hb x hx
    have hWx := hW x hx
    nlinarith [mul_le_mul_of_nonneg_left this (hD x hx).le]
  have hmono : MonotoneOn r (Ici X) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici X)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hder t (interior_subset ht)).deriv]
      exact hge t (interior_subset ht)
  set A := |r X| + 1 with hA
  refine ⟨max X (Real.exp (A * K / c)), fun x hx => ?_⟩
  have hxX : X ≤ x := (le_max_left _ _).trans hx.le
  have hx0 : 0 < x := lt_of_lt_of_le hX0 hxX
  have hxe : Real.exp (A * K / c) < x := (le_max_right _ _).trans_lt hx
  have hlog : A * K / c < Real.log x := by
    rw [Real.lt_log_iff_exp_lt hx0]; exact hxe
  have h1 := hmono self_mem_Ici (show x ∈ Ici X from hxX) hxX
  simp only [r] at h1
  have h2 : A < c / K * Real.log x := by
    rw [div_lt_iff₀ hc] at hlog
    have : A * K < Real.log x * c := hlog
    rw [div_mul_eq_mul_div, lt_div_iff₀ hK]; linarith
  have h3 : 0 < f x / u x := by
    have h4 := neg_abs_le (r X)
    simp only [r] at h4 hA
    linarith
  exact (div_pos_iff_of_pos_right (hu x hxX)).mp h3

/-- A function with zero derivative on an interval is constant there. -/
theorem lzero_ext_count {f f' Q Q' : ℝ → ℝ} {c t₁ T σ₁ σ₂ : ℝ} (ht₁ : 1 < t₁)
    (hfd : ∀ x, 1 < x → HasDerivAt f (f' x) x) (hQd : ∀ x, 1 < x → HasDerivAt Q (Q' x) x)
    (hQ : ∀ x, 1 < x → 0 < Q x) (hc : c ≠ 0)
    (hW : ∀ x, 1 < x → (x ^ 2 - 1) * (Q x * f' x - f x * Q' x) = c)
    (hl : ∀ x ∈ Ioo 1 t₁, 0 < σ₁ * f x) (hr : ∀ x, T < x → 0 < σ₂ * f x) :
    {x | 1 < x ∧ f x = 0}.Finite ∧
      {x | 1 < x ∧ f x = 0}.ncard = if σ₁ * σ₂ < 0 then 1 else 0 := by
  set g : ℝ → ℝ := fun x => c * (f x / Q x)
  have hder : ∀ x, 1 < x → HasDerivAt g (c * ((f' x * Q x - f x * Q' x) / Q x ^ 2)) x :=
    fun x hx => ((hfd x hx).fun_div (hQd x hx) (hQ x hx).ne').const_mul c
  have hmono : StrictMonoOn g (Ioi 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 1)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      rw [(hder t ht).deriv]
      have hp : 0 < t ^ 2 - 1 := by have : (1:ℝ) < t := ht; nlinarith
      have hWt := hW t ht
      have e : c * ((f' t * Q t - f t * Q' t) / Q t ^ 2) =
          c * ((t ^ 2 - 1) * (Q t * f' t - f t * Q' t)) / ((t ^ 2 - 1) * Q t ^ 2) := by
        field_simp
      rw [e, hWt]
      exact div_pos (mul_self_pos.mpr hc) (mul_pos hp (pow_pos (hQ t ht) 2))
  have hg0 : ∀ x, 1 < x → (g x = 0 ↔ f x = 0) := fun x hx => by
    simp only [g, mul_eq_zero, hc, false_or, div_eq_zero_iff, (hQ x hx).ne', or_false]
  have huniq : ∀ a b, 1 < a → 1 < b → f a = 0 → f b = 0 → a = b := by
    intro a b ha hb h1 h2
    exact hmono.injOn ha hb (by rw [(hg0 a ha).2 h1, (hg0 b hb).2 h2])
  have hcont : ContinuousOn f (Ioi 1) := fun x hx => (hfd x hx).continuousAt.continuousWithinAt
  by_cases hσ : σ₁ * σ₂ < 0
  · simp only [hσ, ↓reduceIte]
    set x1 := (1 + t₁) / 2
    have hx1 : x1 ∈ Ioo 1 t₁ := ⟨by simp only [x1]; linarith, by simp only [x1]; linarith⟩
    set x2 := max T x1 + 1
    have hx2T : T < x2 := by have := le_max_left T x1; simp only [x2]; linarith
    have hx12 : x1 < x2 := by have := le_max_right T x1; simp only [x2]; linarith
    have h1 := hl x1 hx1
    have h2 := hr x2 hx2T
    have hprod : f x1 * f x2 < 0 := by nlinarith
    have hsub : Icc x1 x2 ⊆ Ioi 1 := fun x hx => lt_of_lt_of_le hx1.1 hx.1
    obtain ⟨z, hz, hz0⟩ : ∃ z ∈ Icc x1 x2, f z = 0 := by
      rcases lt_or_gt_of_ne (show f x1 ≠ 0 by intro h; rw [h] at hprod; simp at hprod) with
        hn | hp
      · have : 0 < f x2 := by nlinarith
        exact intermediate_value_Icc hx12.le (hcont.mono hsub) ⟨hn.le, this.le⟩
      · have : f x2 < 0 := by nlinarith
        exact intermediate_value_Icc' hx12.le (hcont.mono hsub) ⟨this.le, hp.le⟩
    have hz1 : 1 < z := hsub hz
    have hZ : {x | 1 < x ∧ f x = 0} = {z} := by
      ext x
      simp only [mem_ofPred_eq, mem_singleton_iff]
      exact ⟨fun ⟨hx, h0⟩ => huniq x z hx hz1 h0 hz0, fun h => h ▸ ⟨hz1, hz0⟩⟩
    rw [hZ]; exact ⟨finite_singleton z, ncard_singleton z⟩
  · simp only [hσ, ↓reduceIte]
    have hZ : {x | 1 < x ∧ f x = 0} = ∅ := by
      ext z
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hz1 hz0
      set x1 := min ((1 + t₁) / 2) ((1 + z) / 2)
      have a1 := min_le_left ((1 + t₁) / 2) ((1 + z) / 2)
      have a2 := min_le_right ((1 + t₁) / 2) ((1 + z) / 2)
      have hx1 : x1 ∈ Ioo 1 t₁ := ⟨lt_min (by linarith) (by linarith), by linarith⟩
      have hx1z : x1 < z := by linarith
      set x2 := max T z + 1
      have hx2T : T < x2 := by have := le_max_left T z; simp only [x2]; linarith
      have hzx2 : z < x2 := by have := le_max_right T z; simp only [x2]; linarith
      have hgz : g z = 0 := (hg0 z hz1).2 hz0
      have g1 := hmono hx1.1 hz1 hx1z
      have g2 := hmono hz1 (show (1:ℝ) < x2 by linarith) hzx2
      rw [hgz] at g1 g2
      simp only [g] at g1 g2
      have q1 := hQ x1 hx1.1
      have q2 := hQ x2 (by linarith)
      have k1 : c * f x1 < 0 := by
        have : c * f x1 = c * (f x1 / Q x1) * Q x1 := by field_simp
        rw [this]; exact mul_neg_of_neg_of_pos g1 q1
      have k2 : 0 < c * f x2 := by
        have : c * f x2 = c * (f x2 / Q x2) * Q x2 := by field_simp
        rw [this]; exact mul_pos g2 q2
      have h1 := hl x1 hx1
      have h2 := hr x2 hx2T
      have hprod : f x1 * f x2 < 0 := by
        have : (c * f x1) * (c * f x2) < 0 := mul_neg_of_neg_of_pos k1 k2
        have hc2 : 0 < c ^ 2 := by positivity
        nlinarith
      apply hσ
      nlinarith [mul_pos h1 h2]
    rw [hZ]; exact ⟨finite_empty, ncard_empty ℝ⟩

/-- The rule of DLMF 14.16(iii) (as corrected) through the sign of `sin(μπ)/Γ(ν-μ+1)`. -/
theorem lzero_oneZero_iff {ν μ : ℝ} : associatedPOneZero ν μ ↔
    0 < μ ∧ (∀ n : ℤ, μ ≠ n) ∧ Real.sin (μ * π) * (Real.Gamma (ν - μ + 1))⁻¹ < 0 := by
  have hinv : ν < μ → (Real.Gamma (ν - μ + 1))⁻¹ =
      Real.sin ((μ - ν) * π) * Real.Gamma (μ - ν) / π := by
    intro hlt
    have hG : 0 < Real.Gamma (μ - ν) := Real.Gamma_pos_of_pos (by linarith)
    have h := Real.Gamma_mul_Gamma_one_sub (ν - μ + 1)
    rw [show 1 - (ν - μ + 1) = μ - ν by ring] at h
    have hs : Real.sin (π * (ν - μ + 1)) = Real.sin ((μ - ν) * π) := by
      rw [show π * (ν - μ + 1) = -((μ - ν) * π) + π by ring, Real.sin_add_pi, Real.sin_neg, neg_neg]
    rw [hs] at h
    by_cases h0 : Real.sin ((μ - ν) * π) = 0
    · rw [h0, div_zero, mul_eq_zero, or_iff_left hG.ne'] at h
      rw [h, h0, inv_zero, zero_mul, zero_div]
    · have hπ := Real.pi_pos
      have hGs : Real.Gamma (ν - μ + 1) = π / (Real.sin ((μ - ν) * π) * Real.Gamma (μ - ν)) := by
        have h' := h
        field_simp at h'
        rw [eq_div_iff (mul_ne_zero h0 hG.ne')]
        linear_combination h'
      rw [hGs, inv_div]
  unfold associatedPOneZero
  constructor
  · rintro (⟨h0, hlt, hn, hs⟩ | ⟨h0, hle, hn, hodd⟩)
    · refine ⟨h0, hn, ?_⟩
      rw [hinv hlt]
      have hG : 0 < Real.Gamma (μ - ν) := Real.Gamma_pos_of_pos (by linarith)
      have : Real.sin (μ * π) * (Real.sin ((μ - ν) * π) * Real.Gamma (μ - ν) / π) =
          Real.sin ((μ - ν) * π) * Real.sin (μ * π) * (Real.Gamma (μ - ν) / π) := by ring
      rw [this]
      exact mul_neg_of_neg_of_pos hs (div_pos hG Real.pi_pos)
    · refine ⟨h0, hn, ?_⟩
      have hG : 0 < Real.Gamma (ν - μ + 1) := Real.Gamma_pos_of_pos (by linarith)
      have hss := lzero_sin_sign hn
      rw [hodd.neg_one_zpow] at hss
      exact mul_neg_of_neg_of_pos (by linarith) (inv_pos.mpr hG)
  · rintro ⟨h0, hn, hneg⟩
    rcases lt_or_ge ν μ with hlt | hle
    · refine Or.inl ⟨h0, hlt, hn, ?_⟩
      rw [hinv hlt] at hneg
      have hG : 0 < Real.Gamma (μ - ν) / π := div_pos (Real.Gamma_pos_of_pos (by linarith))
        Real.pi_pos
      have : Real.sin (μ * π) * (Real.sin ((μ - ν) * π) * Real.Gamma (μ - ν) / π) =
          Real.sin ((μ - ν) * π) * Real.sin (μ * π) * (Real.Gamma (μ - ν) / π) := by ring
      rw [this] at hneg
      rcases mul_neg_iff.mp hneg with ⟨_, h⟩ | ⟨h, _⟩
      · linarith
      · exact h
    · refine Or.inr ⟨h0, hle, hn, ?_⟩
      have hG : 0 < Real.Gamma (ν - μ + 1) := Real.Gamma_pos_of_pos (by linarith)
      have hs : Real.sin (μ * π) < 0 := by
        rcases mul_neg_iff.mp hneg with ⟨_, h⟩ | ⟨h, _⟩
        · linarith [inv_pos.mpr hG]
        · exact h
      have hss := lzero_sin_sign hn
      rcases Int.even_or_odd ⌊μ⌋ with he | ho
      · rw [he.neg_one_zpow, one_mul] at hss; linarith
      · exact ho

/-- For positive parameters the regularized Gauss series on `[0, 1)` is real, positive and
increasing. -/
theorem lzero_regGauss_pos_mono {a b c w w' : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hw0 : 0 ≤ w) (hww : w ≤ w') (hw1 : w' < 1) :
    0 < (regularizedGaussHG a b c w).re ∧ (regularizedGaussHG a b c w).im = 0 ∧
      (regularizedGaussHG a b c w).re ≤ (regularizedGaussHG a b c w').re := by
  have hG : ∀ n : ℕ, 0 < Real.Gamma (c + n) := fun n => Real.Gamma_pos_of_pos (by positivity)
  let f : ℝ → ℕ → ℝ := fun w n => (ascPochhammer ℝ n).eval a *
    (ascPochhammer ℝ n).eval b * w ^ n / n.factorial * (Real.Gamma (c + n))⁻¹
  have hsum : ∀ w : ℝ, 0 ≤ w → w < 1 → HasSum (fun n => (f w n : ℂ)) (regularizedGaussHG a b c w) := by
    intro w hw0 hw1
    have hw : ‖(w : ℂ)‖ < 1 := by rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]; exact hw1
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw]
    refine (hasSum_regularizedGaussHGFun _ _ _ hw).congr_fun fun n => ?_
    simp only [f]
    rw [ascPochhammer_eval_ofReal, ascPochhammer_eval_ofReal,
      show (c : ℂ) + n = ((c + n : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  have hf0 : ∀ w : ℝ, 0 ≤ w → ∀ n, 0 ≤ f w n := fun w hw n => by
    have := ascPochhammer_pos n a ha
    have := ascPochhammer_pos n b hb
    have := hG n
    simp only [f]; positivity
  have h1 := hsum w hw0 (hww.trans_lt hw1)
  have h2 := hsum w' (hw0.trans hww) hw1
  have hr1 : HasSum (f w) (regularizedGaussHG a b c w).re := by
    simpa using Complex.reCLM.hasSum h1
  have hr2 : HasSum (f w') (regularizedGaussHG a b c w').re := by
    simpa using Complex.reCLM.hasSum h2
  have hi1 : HasSum (fun _ : ℕ => (0:ℝ)) (regularizedGaussHG a b c w).im := by
    simpa using Complex.imCLM.hasSum h1
  refine ⟨?_, (hi1.unique hasSum_zero), hasSum_le (fun n => ?_) hr1 hr2⟩
  · have := le_hasSum hr1 0 fun j _ => hf0 w hw0 j
    have h00 : 0 < f w 0 := by
      have := hG 0
      simp only [f, ascPochhammer_zero, Polynomial.eval_one, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, one_mul, Nat.cast_zero, add_zero]
      positivity
    linarith
  · simp only [f]
    have := ascPochhammer_pos n a ha
    have := ascPochhammer_pos n b hb
    have := hG n
    have hp : w ^ n ≤ w' ^ n := pow_le_pow_left₀ hw0 hww n
    have hk : 0 ≤ (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b := by positivity
    have hk2 : 0 ≤ (n.factorial : ℝ)⁻¹ * (Real.Gamma (c + n))⁻¹ := by positivity
    calc (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b * w ^ n / n.factorial *
          (Real.Gamma (c + n))⁻¹
        = ((ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b) * w ^ n *
          ((n.factorial : ℝ)⁻¹ * (Real.Gamma (c + n))⁻¹) := by ring
      _ ≤ ((ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b) * w' ^ n *
          ((n.factorial : ℝ)⁻¹ * (Real.Gamma (c + n))⁻¹) := by gcongr
      _ = _ := by ring

/-- Positivity of `𝑸^μ_ν` on `(1, ∞)` (`ν > -1`) and the bound `(x²-1)(𝑸^μ_ν)² = O(x)` at
infinity (`ν ≥ -1/2`). -/
theorem lzero_olverQ_pos_bound {ν : ℝ} (hν : -1/2 ≤ ν) (μ : ℝ) :
    (∀ x : ℝ, 1 < x → 0 < (olverQ ν μ x).re) ∧
      ∃ K > 0, ∀ x : ℝ, 2 ≤ x → (x ^ 2 - 1) * (olverQ ν μ x).re ^ 2 ≤ K * x := by
  -- reduce to `μ ≥ 0`
  have hred : ∀ x : ℝ, 1 < x → olverQ ν μ x = olverQ ν (|μ| : ℝ) x := by
    intro x hx
    rcases le_or_gt 0 μ with h | h
    · rw [abs_of_nonneg h]
    · have := associated_connection_14 (ν:ℂ) ((|μ|:ℝ):ℂ) (z := (x:ℂ)) (lzero_mem hx)
      rw [← this, abs_of_neg h]; push_cast; ring_nf
  set m := |μ| with hm
  have hm0 : 0 ≤ m := abs_nonneg μ
  set a := (ν + m + 2) / 2
  set b := (ν + m + 1) / 2
  set c := ν + 3 / 2
  have ha : 0 < a := by simp only [a]; linarith
  have hb : 0 < b := by simp only [b]; linarith
  have hc : 0 < c := by simp only [c]; linarith
  -- the real form
  set R : ℝ → ℝ := fun x => Real.sqrt π * Real.exp (m / 2 * (Real.log (x - 1) + Real.log (x + 1))) /
    ((2:ℝ) ^ (ν + 1) * x ^ (ν + m + 1)) with hR
  have hrep : ∀ x : ℝ, 1 < x → olverQ ν m x = (R x : ℂ) * regularizedGaussHG a b c (1 / x ^ 2) := by
    intro x hx
    unfold olverQ legendreBranchPower
    have h1 : (x:ℂ) - 1 = ((x - 1 : ℝ) : ℂ) := by push_cast; ring
    have h2 : (x:ℂ) + 1 = ((x + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, ← ofReal_log (by linarith), ← ofReal_log (by linarith)]
    have e1 : (2:ℂ) ^ ((ν:ℂ) + 1) = (((2:ℝ) ^ (ν + 1) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by norm_num)]; push_cast; ring_nf
    have e2 : (x:ℂ) ^ ((ν:ℂ) + (m:ℂ) + 1) = ((x ^ (ν + m + 1) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by linarith)]; push_cast; ring_nf
    rw [e1, e2]
    simp only [hR, a, b, c]
    push_cast
    ring_nf
  have hdata : ∀ x : ℝ, 1 < x → 0 < R x ∧ (olverQ ν m x).re =
      R x * (regularizedGaussHG a b c ((1 / x ^ 2 : ℝ) : ℂ)).re := by
    intro x hx
    refine ⟨by
      simp only [hR]
      have : 0 < (2:ℝ) ^ (ν + 1) := Real.rpow_pos_of_pos (by norm_num) _
      have : 0 < x ^ (ν + m + 1) := Real.rpow_pos_of_pos (by linarith) _
      have : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
      positivity, ?_⟩
    rw [hrep x hx, show (1:ℂ) / (x:ℂ) ^ 2 = ((1 / x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      re_ofReal_mul]
  have hw : ∀ x : ℝ, 1 < x → 0 ≤ 1 / x ^ 2 ∧ 1 / x ^ 2 < 1 := fun x hx =>
    ⟨by positivity, by rw [div_lt_one (by positivity)]; nlinarith⟩
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [hred x hx]
    obtain ⟨hR0, hre⟩ := hdata x hx
    rw [hre]
    exact mul_pos hR0 (lzero_regGauss_pos_mono ha hb hc (hw x hx).1 le_rfl (hw x hx).2).1
  · set S := (regularizedGaussHG a b c ((1 / 4 : ℝ) : ℂ)).re
    refine ⟨π * S ^ 2 + 1, by positivity, fun x hx => ?_⟩
    have hx1 : 1 < x := by linarith
    have hx0 : 0 < x := by linarith
    rw [hred x hx1]
    obtain ⟨hR0, hre⟩ := hdata x hx1
    rw [hre]
    obtain ⟨hF0, -, hFle⟩ := lzero_regGauss_pos_mono ha hb hc (hw x hx1).1
      (show 1 / x ^ 2 ≤ 1 / 4 by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith) (by norm_num)
    set F := (regularizedGaussHG a b c ((1 / x ^ 2 : ℝ) : ℂ)).re
    -- `(x²-1) R² ≤ π x`
    obtain ⟨t, ht⟩ : ∃ t, Real.log x = t := ⟨_, rfl⟩
    obtain ⟨L, hLd⟩ : ∃ L, Real.log (x - 1) + Real.log (x + 1) = L := ⟨_, rfl⟩
    have hL : L = Real.log (x ^ 2 - 1) := by
      rw [← hLd, ← Real.log_mul (by linarith) (by linarith)]; ring_nf
    have hLt : L ≤ 2 * t := by
      have h := Real.log_le_log (by nlinarith) (show x ^ 2 - 1 ≤ x ^ 2 by linarith)
      rw [Real.log_pow] at h
      push_cast at h
      rw [hL, ← ht]; linarith
    have hexpL : Real.exp L = x ^ 2 - 1 := by rw [hL, Real.exp_log (by nlinarith)]
    have ht0 : 0 ≤ t := by rw [← ht]; exact Real.log_nonneg (by linarith)
    have hxt : x = Real.exp t := by rw [← ht, Real.exp_log hx0]
    have h2p : 1 ≤ (2:ℝ) ^ (ν + 1) := Real.one_le_rpow (by norm_num) (by linarith)
    have hxp : x ^ (ν + m + 1) = Real.exp ((ν + m + 1) * t) := by
      rw [Real.rpow_def_of_pos hx0, ht]; ring_nf
    have hRsq : (x ^ 2 - 1) * R x ^ 2 ≤ π * x := by
      simp only [hR]
      rw [hLd, div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, mul_pow]
      have e1 : Real.exp (m / 2 * L) ^ 2 = Real.exp (m * L) := by
        rw [← Real.exp_nat_mul]; ring_nf
      have e2 : (x ^ (ν + m + 1)) ^ 2 = Real.exp (2 * (ν + m + 1) * t) := by
        rw [hxp, ← Real.exp_nat_mul]; ring_nf
      rw [e1, e2, ← hexpL]
      have hd : 0 < ((2:ℝ) ^ (ν + 1)) ^ 2 * Real.exp (2 * (ν + m + 1) * t) := by positivity
      rw [mul_div_assoc', div_le_iff₀ hd]
      have hk0 : Real.exp L * Real.exp (m * L) ≤ Real.exp (2 * (ν + m + 1) * t) * Real.exp t := by
        rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
      have hk : Real.exp L * (π * Real.exp (m * L)) ≤
          π * (Real.exp (2 * (ν + m + 1) * t) * x) := by
        rw [hxt]
        nlinarith [Real.pi_pos]
      have h2sq : 1 ≤ ((2:ℝ) ^ (ν + 1)) ^ 2 := one_le_pow₀ h2p
      have hE : 0 ≤ π * (Real.exp (2 * (ν + m + 1) * t) * x) := by positivity
      nlinarith
    have hF2 : F ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hF0.le hFle 2
    have hp : 0 ≤ x ^ 2 - 1 := by nlinarith
    calc (x ^ 2 - 1) * (R x * F) ^ 2 = ((x ^ 2 - 1) * R x ^ 2) * F ^ 2 := by ring
      _ ≤ (π * x) * S ^ 2 := mul_le_mul hRsq hF2 (sq_nonneg _) (by positivity)
      _ ≤ (π * S ^ 2 + 1) * x := by nlinarith

/-- Real form of a Wronskian identity on `(1, ∞)` for functions real there. -/
theorem lzero_ext_wr {F G : ℂ → ℂ} {x c : ℝ} (hx : 1 < x) (hF : (F x).im = 0)
    (hG : (G x).im = 0) (h : LegendreWronskian F G x = (c : ℂ) / ((x : ℂ) ^ 2 - 1)) :
    (x ^ 2 - 1) * ((F x).re * (deriv G x).re - (G x).re * (deriv F x).re) = c := by
  have hp : x ^ 2 - 1 ≠ 0 := by nlinarith
  rw [show (c : ℂ) / ((x : ℂ) ^ 2 - 1) = ((c / (x ^ 2 - 1) : ℝ) : ℂ) by push_cast; ring] at h
  have h' := congrArg re h
  simp only [LegendreWronskian, sub_re, mul_re, hF, hG, zero_mul, sub_zero, ofReal_re] at h'
  rw [h']
  field_simp

/-- Near `x = 1⁺`, `P^{-m}_ν` (`m ≥ 0`) is positive and `O((x - 1)^{1/2}(x+1)^{-1/2})`. -/
theorem lzero_assocP_near_one (ν : ℝ) {m : ℝ} (hm : 0 ≤ m) :
    ∃ s : ℝ, 1 < s ∧ ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, x ∈ Ioc 1 s → 0 < (associatedP ν (-m : ℝ) x).re ∧
      (x ^ 2 - 1) * (associatedP ν (-m : ℝ) x).re ^ 2 ≤ K * (x - 1) := by
  set g : ℝ → ℂ := fun x => regularizedGaussHG ((ν:ℂ) + 1) (-(ν:ℂ)) (1 - ((-m:ℝ):ℂ))
    ((1 - (x:ℂ)) / 2) with hg
  have h0c : (0:ℂ) ∈ cutPlane := mem_cutPlane_of_norm_lt_one (by simp)
  have hcont : ContinuousAt g 1 := by
    have h1 : ContinuousAt (fun x : ℝ => (1 - (x:ℂ)) / 2) 1 := by fun_prop
    have h2 : ((1:ℂ) - ((1:ℝ):ℂ)) / 2 = 0 := by simp
    have h3 := (analyticOnNhd_regularizedGaussHG ((ν:ℂ) + 1) (-(ν:ℂ)) (1 - ((-m:ℝ):ℂ)) 0
      h0c).continuousAt
    exact h3.comp_of_eq h1 h2
  have hc : ∀ k : ℕ, (1:ℂ) - ((-m:ℝ):ℂ) ≠ -(k:ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hg1 : g 1 = ((Real.Gamma (1 + m))⁻¹ : ℝ) := by
    simp only [hg, ofReal_one, sub_self, zero_div]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by simp),
      regularizedGaussHGFun_eq_div_Gamma hc, ordinaryHypergeometric_zero,
      show (1:ℂ) - ((-m:ℝ):ℂ) = ((1 + m : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  have hG := Real.Gamma_pos_of_pos (show 0 < 1 + m by linarith)
  have hre1 : 0 < (g 1).re := by rw [hg1, ofReal_re]; positivity
  have hev : ∀ᶠ x in 𝓝 (1:ℝ), 0 < (g x).re ∧ ‖g x‖ < ‖g 1‖ + 1 := by
    have t1 := (Complex.continuous_re.continuousAt.comp hcont).eventually (lt_mem_nhds
      (show (g 1).re / 2 < (g 1).re by linarith))
    have t2 := (continuous_norm.continuousAt.comp hcont).eventually (gt_mem_nhds
      (show ‖g 1‖ < ‖g 1‖ + 1 by linarith))
    filter_upwards [t1, t2] with x h1 h2
    exact ⟨by simp only [Function.comp] at h1; linarith, h2⟩
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (nhdsWithin_le_nhds hev)
  have hu1 : (1:ℝ) < u := hu
  set M := ‖g 1‖ + 1 with hM
  have hM1 : 1 ≤ M := by have := norm_nonneg (g 1); linarith
  refine ⟨(1 + u) / 2, by linarith, ((1 + u) / 2 + 1) * M ^ 2, mul_pos (by linarith) (pow_pos (by linarith) 2), fun x hx => ?_⟩
  have hx1 : 1 < x := hx.1
  obtain ⟨hgr, hgn⟩ := hsub ⟨hx1, by linarith [hx.2]⟩
  set E := Real.exp ((-m) / 2 * (Real.log (x + 1) - Real.log (x - 1))) with hE
  have hrep : (associatedP ν (-m : ℝ) x).re = E * (g x).re := by
    simp only [associatedP, hg, hE]
    rw [show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring,
      show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith),
      show ((-m : ℝ) : ℂ) / 2 * ((Real.log (x + 1) : ℂ) - (Real.log (x - 1) : ℂ)) =
        (((-m) / 2 * (Real.log (x + 1) - Real.log (x - 1)) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_exp, re_ofReal_mul]
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    have : Real.log (x - 1) ≤ Real.log (x + 1) := Real.log_le_log (by linarith) (by linarith)
    nlinarith
  refine ⟨by rw [hrep]; exact mul_pos hE0 hgr, ?_⟩
  rw [hrep]
  have hgb : (g x).re ^ 2 ≤ M ^ 2 := by
    have h1 := Complex.abs_re_le_norm (g x)
    have h2 : |(g x).re| ≤ M := h1.trans hgn.le
    nlinarith [abs_nonneg (g x).re, sq_abs (g x).re]
  have hE2 : E ^ 2 ≤ 1 := by nlinarith
  have hx2 : x + 1 ≤ (1 + u) / 2 + 1 := by linarith [hx.2]
  calc (x ^ 2 - 1) * (E * (g x).re) ^ 2 = (x - 1) * ((x + 1) * (E ^ 2 * (g x).re ^ 2)) := by ring
    _ ≤ (x - 1) * (((1 + u) / 2 + 1) * (1 * M ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply mul_le_mul hx2 (mul_le_mul hE2 hgb (sq_nonneg _) zero_le_one)
          (by positivity) (by positivity)
    _ = ((1 + u) / 2 + 1) * M ^ 2 * (x - 1) := by ring

/-- Exactly one or no exterior zeros, excluding an identically zero solution. -/
theorem associatedP_zero_count {ν μ : ℝ} (hν : -1/2 ≤ ν) (hnondeg : ∃ x : ℝ, 1 < x ∧ associatedP ν μ x ≠ 0) :
    Set.Finite {x : ℝ | 1 < x ∧ associatedP ν μ x=0} ∧ ({x : ℝ | 1 < x ∧ associatedP ν μ x=0}:Set ℝ).ncard=if associatedPOneZero ν μ then 1 else 0 := by
  set P : ℂ → ℂ := associatedP (ν : ℂ) (μ : ℂ) with hP
  set Qc : ℂ → ℂ := olverQ (ν : ℂ) (μ : ℂ) with hQc
  set f : ℝ → ℝ := fun x => (P x).re with hf
  set f' : ℝ → ℝ := fun x => (deriv P x).re with hf'
  set q : ℝ → ℝ := fun x => (Qc x).re with hq
  set q' : ℝ → ℝ := fun x => (deriv Qc x).re with hq'
  have hfd : ∀ x, 1 < x → HasDerivAt f (f' x) x := fun x hx =>
    (associatedP_analytic (ν : ℂ) μ x (lzero_mem hx)).differentiableAt.hasDerivAt.real_of_complex
  have hqd : ∀ x, 1 < x → HasDerivAt q (q' x) x := fun x hx =>
    (olverQ_analytic (ν : ℂ) μ x (lzero_mem hx)).differentiableAt.hasDerivAt.real_of_complex
  obtain ⟨hQpos, K, hK, hQb⟩ := lzero_olverQ_pos_bound hν μ
  set cA : ℝ := (Real.Gamma (ν - μ + 1))⁻¹ with hcA
  have hWA : ∀ x, 1 < x → (x ^ 2 - 1) * (q x * f' x - f x * q' x) = cA := by
    intro x hx
    have h := olverQ_wronskian_pos (ν : ℂ) μ (z := x) (lzero_mem hx)
    have h2 : LegendreWronskian Qc P x = (cA : ℂ) / ((x : ℂ) ^ 2 - 1) := by
      rw [show LegendreWronskian Qc P x = -LegendreWronskian P Qc x by
        simp only [LegendreWronskian]; ring, h,
        show (ν : ℂ) - μ + 1 = ((ν - μ + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
        hcA]
      push_cast; ring
    exact lzero_ext_wr hx (olverQ_real ν μ hx) (associatedP_real ν μ hx) h2
  have hset : {x : ℝ | 1 < x ∧ associatedP ν μ x = 0} = {x | 1 < x ∧ f x = 0} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨hx, by simp only [hf, hP, h, zero_re]⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, Complex.ext h (associatedP_real ν μ hx)⟩
  rw [hset]
  by_cases hA : cA = 0
  · -- `P` is a multiple of `𝑸`, hence zero-free
    have hr : ∀ x, 1 < x → f x / q x = f 2 / q 2 := by
      intro x hx
      refine lzero_const_of_deriv_zero (s := Ioi 1) ordConnected_Ioi
        (fun y hy => (hfd y hy).div (hqd y hy) (hQpos y hy).ne') (fun y hy => ?_) hx
        (show (1:ℝ) < 2 by norm_num)
      have h := hWA y hy
      rw [hA] at h
      have hp : y ^ 2 - 1 ≠ 0 := by have : (1:ℝ) < y := hy; nlinarith
      have h' : q y * f' y - f y * q' y = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h hp
        · exact h
      rw [show f' y * q y - f y * q' y = 0 by linarith, zero_div]
    obtain ⟨w, hw, hPw⟩ := hnondeg
    have hfw : f w ≠ 0 := fun h => hPw (Complex.ext h (associatedP_real ν μ hw))
    have hZ : {x | 1 < x ∧ f x = 0} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx h0
      have h1 := hr x hx
      have h2 := hr w hw
      rw [h0, zero_div] at h1
      rw [← h1, div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · exact hfw h2
      · exact (hQpos w hw).ne' h2
    have hno : ¬ associatedPOneZero ν μ := by
      rw [lzero_oneZero_iff, ← hcA, hA, mul_zero]
      exact fun h => lt_irrefl _ h.2.2
    rw [hZ]
    simp [hno]
  -- sign at infinity
  have hcA2 : 0 < cA ^ 2 := by positivity
  obtain ⟨T, hT⟩ := lzero_ext_pos_atTop (f := fun x => cA * f x) (f' := fun x => cA * f' x)
    (u := q) (u' := q') (X := 2) (K := K) (c := cA ^ 2) (by norm_num) hK hcA2
    (fun x hx => (hfd x (by have : (2:ℝ) ≤ x := hx; linarith)).const_mul cA)
    (fun x hx => hqd x (by have : (2:ℝ) ≤ x := hx; linarith))
    (fun x hx => hQpos x (by have : (2:ℝ) ≤ x := hx; linarith))
    (fun x hx => hQb x hx)
    (fun x hx => by
      have h := hWA x (by have : (2:ℝ) ≤ x := hx; linarith)
      linear_combination cA * h)
  -- sign near one
  have hnear : ∃ σ₁ t₁ : ℝ, 1 < t₁ ∧ (∀ x ∈ Ioo 1 t₁, 0 < σ₁ * f x) ∧
      (σ₁ * cA < 0 ↔ associatedPOneZero ν μ) := by
    rcases le_or_gt μ 0 with hμ | hμ
    · obtain ⟨s, hs, K1, hK1, hv⟩ := lzero_assocP_near_one ν (m := -μ) (by linarith)
      have hcA0 : 0 < cA := inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))
      refine ⟨1, s, hs, fun x hx => ?_, ?_⟩
      · have := (hv x (Ioo_subset_Ioc_self hx)).1
        simp only [neg_neg] at this
        simpa [hf, hP] using this
      · rw [lzero_oneZero_iff]
        constructor
        · intro h; linarith
        · intro h; exact absurd h.1 (not_lt.mpr hμ)
    · obtain ⟨s, hs, K1, hK1, hv⟩ := lzero_assocP_near_one ν (m := μ) hμ.le
      set V : ℂ → ℂ := associatedP (ν : ℂ) (-(μ : ℂ)) with hV
      set v : ℝ → ℝ := fun x => (V x).re with hv_def
      set v' : ℝ → ℝ := fun x => (deriv V x).re with hv'_def
      have hvd : ∀ x, 1 < x → HasDerivAt v (v' x) x := fun x hx =>
        (associatedP_analytic (ν : ℂ) (-(μ : ℂ)) x
          (lzero_mem hx)).differentiableAt.hasDerivAt.real_of_complex
      have hVreal : ∀ x : ℝ, 1 < x → (V x).im = 0 := fun x hx => by
        have := associatedP_real ν (-μ) hx
        simpa [hV] using this
      have hv1 : ∀ x ∈ Ioc 1 s, 0 < v x ∧ (x ^ 2 - 1) * v x ^ 2 ≤ K1 * (x - 1) := by
        intro x hx
        have := hv x hx
        simpa [hv_def, hV] using this
      set cB : ℝ := -2 * Real.sin (μ * π) / π with hcB
      have hWB : ∀ x, 1 < x → (x ^ 2 - 1) * (v x * f' x - f x * v' x) = cB := by
        intro x hx
        have h := associated_wronskian_7 (ν : ℂ) μ (z := x) (lzero_mem hx)
        have h2 : LegendreWronskian V P x = (cB : ℂ) / ((x : ℂ) ^ 2 - 1) := by
          rw [h, hcB, show (μ : ℂ) * π = ((μ * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin]
          have hp : (x : ℂ) ^ 2 - 1 ≠ 0 := by
            rw [show (x : ℂ) ^ 2 - 1 = ((x ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring]
            exact ofReal_ne_zero.mpr (by nlinarith)
          have hp' : (1 : ℂ) - (x : ℂ) ^ 2 ≠ 0 := by
            rw [show (1 : ℂ) - (x : ℂ) ^ 2 = -((x : ℂ) ^ 2 - 1) by ring]; exact neg_ne_zero.mpr hp
          have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
          push_cast
          field_simp
          ring
        exact lzero_ext_wr hx (hVreal x hx) (associatedP_real ν μ hx) h2
      by_cases hint : ∀ n : ℤ, μ ≠ n
      · -- nonintegral `μ`
        have hsin : Real.sin (μ * π) ≠ 0 := by
          have := lzero_sin_sign hint
          intro h; rw [h, mul_zero] at this; exact lt_irrefl _ this
        have hcB0 : cB ≠ 0 := by
          rw [hcB]; exact div_ne_zero (by simpa using hsin) Real.pi_pos.ne'
        obtain ⟨t, ht, hneg⟩ := lzero_ext_neg_near_one (f := fun x => cB * f x)
          (f' := fun x => cB * f' x) (v := v) (v' := v') (s := s) (K := K1) (c := cB ^ 2) hs hK1
          (by positivity) (fun x hx => (hfd x hx.1).const_mul cB) (fun x hx => hvd x hx.1)
          (fun x hx => (hv1 x hx).1) (fun x hx => (hv1 x hx).2)
          (fun x hx => by linear_combination cB * hWB x hx.1)
        refine ⟨-cB, t, ht.1, fun x hx => by have : cB * f x < 0 := hneg x hx; linarith, ?_⟩
        rw [lzero_oneZero_iff, hcB, ← hcA]
        have hπ := Real.pi_pos
        constructor
        · intro h
          refine ⟨hμ, hint, ?_⟩
          have : -(-2 * Real.sin (μ * π) / π) * cA = (2 / π) * (Real.sin (μ * π) * cA) := by ring
          rw [this] at h
          rcases mul_neg_iff.mp h with h | h
          · exact h.2
          · exact absurd h.1 (not_lt.mpr (by positivity))
        · rintro ⟨-, -, h⟩
          have : -(-2 * Real.sin (μ * π) / π) * cA = (2 / π) * (Real.sin (μ * π) * cA) := by ring
          rw [this]
          exact mul_neg_of_pos_of_neg (by positivity) h
      · -- integral `μ`: `P` is a multiple of `P^{-μ}` near `1`
        push Not at hint
        obtain ⟨n, hn⟩ := hint
        have hcB0 : cB = 0 := by
          rw [hcB, hn, Real.sin_int_mul_pi, mul_zero, zero_div]
        set cC : ℝ := (Real.Gamma (ν + μ + 1))⁻¹ with hcC
        have hcC0 : 0 < cC := inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))
        have hWC : ∀ x, 1 < x → (x ^ 2 - 1) * (q x * v' x - v x * q' x) = cC := by
          intro x hx
          have h := associated_wronskian_8 (ν : ℂ) μ (z := x) (lzero_mem hx)
          have h2 : LegendreWronskian Qc V x = (cC : ℂ) / ((x : ℂ) ^ 2 - 1) := by
            rw [show LegendreWronskian Qc V x = -LegendreWronskian V Qc x by
              simp only [LegendreWronskian]; ring, h,
              show (ν : ℂ) + μ + 1 = ((ν + μ + 1 : ℝ) : ℂ) by push_cast; ring,
              Complex.Gamma_ofReal, hcC]
            push_cast
            simp only [div_eq_mul_inv, mul_inv]
            ring
          exact lzero_ext_wr hx (olverQ_real ν μ hx) (hVreal x hx) h2
        set s' : ℝ := (1 + s) / 2 with hs'
        have hs'1 : 1 < s' := by linarith
        have hs's : s' < s := by linarith
        have hlam : ∀ x ∈ Ioo 1 s, f x / v x = f s' / v s' := by
          intro x hx
          refine lzero_const_of_deriv_zero (s := Ioo 1 s) ordConnected_Ioo
            (fun y hy => (hfd y hy.1).div (hvd y hy.1) (hv1 y (Ioo_subset_Ioc_self hy)).1.ne')
            (fun y hy => ?_) hx ⟨hs'1, hs's⟩
          have h := hWB y hy.1
          rw [hcB0] at h
          have hp : y ^ 2 - 1 ≠ 0 := by nlinarith [hy.1]
          have h' : v y * f' y - f y * v' y = 0 := by
            rcases mul_eq_zero.mp h with h | h
            · exact absurd h hp
            · exact h
          rw [show f' y * v y - f y * v' y = 0 by linarith, zero_div]
        set lam : ℝ := f s' / v s' with hlam_def
        have hfeq : ∀ x ∈ Ioo 1 s, f x = lam * v x := fun x hx => by
          have := hlam x hx
          have hv0 := (hv1 x (Ioo_subset_Ioc_self hx)).1
          rw [← this]; field_simp
        -- compare Wronskians at `s'`
        have hderiv : f' s' = lam * v' s' := by
          have h1 : HasDerivAt f (lam * v' s') s' := by
            refine ((hvd s' hs'1).const_mul lam).congr_of_eventuallyEq ?_
            filter_upwards [Ioo_mem_nhds hs'1 hs's] with y hy using hfeq y hy
          exact (hfd s' hs'1).unique h1
        have hrel : cA = lam * cC := by
          rw [← hWA s' hs'1, ← hWC s' hs'1, hderiv, hfeq s' ⟨hs'1, hs's⟩]; ring
        have hpos : 0 < cA * lam := by
          have h : cA * lam * cC = cA ^ 2 := by rw [hrel]; ring
          have : 0 < cA * lam * cC := by rw [h]; exact hcA2
          exact pos_of_mul_pos_left this hcC0.le
        refine ⟨cA, s, hs, fun x hx => ?_, ?_⟩
        · rw [hfeq x hx, ← mul_assoc]
          exact mul_pos hpos (hv1 x (Ioo_subset_Ioc_self hx)).1
        · rw [lzero_oneZero_iff]
          constructor
          · intro h; nlinarith
          · rintro ⟨-, h, -⟩; exact absurd hn (h n)
  obtain ⟨σ₁, t₁, ht₁, hl, hiff⟩ := hnear
  have hcount := lzero_ext_count (σ₂ := cA) ht₁ hfd hqd hQpos hA hWA hl
    (fun x hx => hT x hx)
  rw [hcount.2]
  refine ⟨hcount.1, ?_⟩
  exact if_congr hiff rfl rfl

end DLMF.Legendre
